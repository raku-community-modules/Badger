no precompilation;
use MONKEY-SEE-NO-EVAL;

my module AST {

}

my role AST::Typed {
    has Str $.type-name;
    has @.used-modules;

    method type {
        if $!type-name {
            if @!used-modules {
                EVAL @!used-modules.map({ "use $_;\n" }).join ~ "::('$!type-name')"
            }
            else {
                ::($!type-name)
            }
        }
        else {
            Any
        }
    }
}

my class AST::Param does AST::Typed {
    has Str $.sigil;
    has Str $.name;
    has Bool $.named;
    has Bool $.mandatory;

    submethod BUILD(:$!sigil, :$!name, :$!named, :$!type-name, :$quantifier) {
      # It's mandatory if it's a positional parameter OR has a bang
      $!mandatory = !$!named || $quantifier eq '!';
    }

    method Str {
        $.sigil ~ $.name
    }
}

my class AST::Return is repr('Uninstantiable') {

}
my class AST::Return::SingleHash is AST::Return {

}
my class AST::Return::MultiHash is AST::Return {

}
my class AST::Return::Scalar is AST::Return {

}
my class AST::Return::Count is AST::Return {

}
my class AST::Return::Typed is AST::Return does AST::Typed {

}
my class AST::Return::MultiTyped is AST::Return does AST::Typed {

}

my class AST::Sig {
    has AST::Param:D @.by-name is required;
    has AST::Param:D @.by-pos is required;
    has AST::Param:D @.param is required;
    has AST::Return:D $.return is required;

    submethod BUILD(:$!return, :@param) {
        # Sort by-name so that we can deal with incoming parameters more easily later on
        @!by-name = @param.grep(*.named).sort(*.name);
        @!by-pos = @param.grep(!*.named);

        @!param = |@!by-pos, |@!by-name;
    }
}

my class AST::Module {
    has Str $.name;
    has Str $.content;
    has AST::Sig:D $.sig is required handles <param return by-name by-pos>;
}

my class ParseFail is Exception {
    has Str $.reason is required;
    has Cursor $.cursor is required;

    method message() {
        "SQL parse failed: $!reason at line $.line near '$.near'"
    }

    method line() {
        $!cursor.orig.substr(0, $!cursor.pos).split(/\n/).elems
    }

    method near() {
        $!cursor.orig.substr($!cursor.pos, 40)
    }
}

#use Grammar::Tracer;
my grammar FileGrammar {
    token TOP { <.ws> <use>* <.ws> <module>+ }

    token use {
        '--' <.ws>
        'use' <.ws>
        [
        || <module-name=.qualified-name> \n+
        || <.panic: 'Malformed use'>
        ]
    }

    token module {
        :my @*param-names;
        :my $*param-has-named = False;
        <header>
        <content>
    }

    token header {
        '--' <.ws>
        'sub' <.ws>
        <name>
        [ '(' ~ ')' <sig> \n
        || <.panic: "No signature found for routine $<name>"> ]
    }

    rule sig {
        <param>* % [ ',' ]
        ['-->' <return>]?
    }

    token named {
        [ ':' { $*param-has-named = True; }
        || <?{ $*param-has-named }> <.panic: "Cannot have a positional parameter after a named one"> ]?
    }

    token param {
        [ $<type>=<.qualified-name> \s+ ]?
        <named> $<sigil>=<[ $ @ % ]> <name> $<quantifier>=<[ ! ]>?
        [ <?{ ~$<name> (elem) @*param-names }> <.panic: "Duplicate parameter name: $<name>">
        || { @*param-names.push: ~$<name> } ]
    }

    proto token return { * }

    multi token return:count { '+' '@'? }

    multi token return:sigil { (<[ $ @ % ]>) }

    multi token return:typed-sigil {
        $<type>=<.qualified-name> <|b> \s*
        [  $<sigil>=<[ $ @ ]>
        || '%' <.panic: "Hash return cannot have a type ascription">
        || <.panic: "Expected sigil after return type ascription">
        ]
    }

    token content {
        [ ^^ <!before '--' <.ws> 'sub' <.ws>> \N* $$ ]+%% \n
    }

    token qualified-name { <name>+ % '::' }

    token name { <[- \w]>+ }

    token ws { \h* }

    method panic($reason) {
        die ParseFail.new(:$reason, :cursor(self));
    }
}

my class FileActions {
    my @used-modules;

    method TOP($/) {
        make $<module>>>.made
    }

    method use($/) {
        push @used-modules, ~$<module-name>;
    }

    method module($/) {
        make AST::Module.new(
            :name(~$<header><name>),
            :sig($<header><sig>.made),
            :content(~$<content>),
        )
    }

    method sig($/) {
        make AST::Sig.new(
            :param($<param>>>.made),
            :return($<return> ?? $<return>.made !! AST::Return::Count.new) # default to +
        )
    }

    method return:count ($/) {
        make AST::Return::Count.new
    }
    method return:sigil ($/) {
        given ~$0 {
            when '@' { make AST::Return::MultiHash.new }
            when '%' { make AST::Return::SingleHash.new }
            when '$' { make AST::Return::Scalar.new }
            default { die "Unrecognized sigil" }
        }
    }
    method return:typed-sigil ($/) {
        given ~$<sigil> {
            when '@' { make AST::Return::MultiTyped.new(type-name => ~$<type>, :@used-modules) }
            when '$' { make AST::Return::Typed.new(type-name => ~$<type>, :@used-modules) }
            default { die "Unrecognized sigil" }
        }
    }

    method named ($/) {
        make $/ eq ":"
    }

    method param ($/) {
        make AST::Param.new(
            sigil => ~$<sigil>,
            name => ~$<name>,
            type-name => $<type> ?? ~$<type> !! Nil,
            named => $<named>.made,
            quantifier => $<quantifier>
        )
    }
}

my subset File of Str where *.IO.e;

my class PopulateClass {
    has Code $.fn;
    method populate($obj) {
        $!fn($obj)
    }
}

multi sub build-return-class($, AST::Return::Count) {
    PopulateClass.new(fn => *.rows)
}

multi sub build-return-class($, AST::Return::SingleHash) {
    PopulateClass.new(fn => { my \r = .hash; r ?? r !! %() })
}

multi sub build-return-class($, AST::Return::MultiHash) {
    PopulateClass.new(fn => *.hashes)
}
multi sub build-return-class($, AST::Return::Scalar) {
    PopulateClass.new(fn => *.value)
}

multi sub build-return-class($, AST::Return::Typed $typed) {
    PopulateClass.new(fn => { $typed.type.new(|.hash) })
}

multi sub build-return-class($, AST::Return::MultiTyped $typed) {
    PopulateClass.new(fn => {
        my $type = $typed.type;
        .hashes.map({
            $type.new(|$_)
        })
    })
}

multi sub build-return-class($name, AST::Return:D $return) {
    die "NYI, AST::Return::Create and AST::Return::MultiCreate";
    my $return-class = Metamodel::ClassHOW.new_type(:name("ReturnType-$name"));
    for $return.attributes -> $attr {
        $return-class.^add_attribute(Attribute.new(
            :name($attr.sigil ~ '!' ~ $attr.name),
            :type($attr.type),
            :has_accessor(1),
            :package($return-class),
            :required
        ));
    }
    # TODO "Int $.affected-rows is required;"?
    $return-class.^add_method("populate", method ($obj) {
        # $.affected-rows = $obj.rows;
        $obj.hashes.map({ $return-class.new(|$_) })
    });
    $return-class.^compose;
}

# Automatically adds an annotation for the type in case we know it in advance
sub type-to-ascription(AST::Param $param) {
    my $sql-type = do given $param.type {
        when Int { "int" }
        when Rat { "float" }
        when Str { "text" }
        default { return Nil }
    }

    given $param.sigil {
        when "@" { $sql-type ~ '[]' }
        default { $sql-type }
    }
}

my role SignatureOverload[$sig] {
  # Enable this to see the optimizer fail
  #method signature {
  #  $sig
  #}
}

# Replaces $a, $b, ... with $1 or $2 in the SQL query.
# Uses C<type-to-ascription> to optionally ascribe them in the SQL.
sub interpolate-sql($module) {
    my @arg-names = $module.param.map({ .sigil ~ .name });
    $module.content.trim.subst(/<[$@%]> (<[- \w]>+)/, {
        with @arg-names.first(~$/, :k) -> $i {
            with type-to-ascription($module.param[$i]) {
                '($' ~ 1 + $i ~ "::$_)"
            } else {
                '$' ~ 1 + $i
            }
        } else {
            if $module.param.grep({ $0.fc eq .name.fc }) -> @vars {
                die "Unknown parameter $/, do you mean $(@vars.join: " or ")?";
            } else {
                die "Unknown parameter: $/";
            }
        }
    }, :g)
}

sub gen-sql-sub(AST::Module:D $module) {
    my $name = $module.name;
    my $return-class = build-return-class($name, $module.return);

    my $params := Array.new(Parameter.new(:name('$connection'), :mandatory, :type(Any)));
    for $module.param -> $param {
        $params.push: Parameter.new(:name($param.name), :mandatory($param.mandatory), :type($param.type), :named($param.named));
    }
    my @named-names = $module.by-name.map(*.name);

    my $sql = interpolate-sql($module);

    my $sig = Signature.new(:returns($return-class), :count(1.Num), :params($params.List));

    my $sub = (sub ($connection, *@params, *%named-params) {
        unless @params == $module.by-pos {
            die "SQL query $name takes $module.by-pos.elems() positional SQL arguments, got @params.elems().";
        }
        if %named-params.keys (-) $module.by-name.map(*.name) -> $extra {
            die "Extra named parameters for SQL query $name: $($extra.keys.sort.join: ", "). Named parameters: $($module.by-name.map(*.name).join: ", ").";
        }
        if $module.by-name.grep(*.mandatory).map(*.name) (-) %named-params.keys -> $missing {
            die "Missing required named parameters for SQL query $name: $($missing.keys.sort.join: ", ").";
        }
        my %by-name-params = %(@named-names X=> Nil), %named-params;

        my $query = $connection.query($sql, |@params, |%by-name-params.sort(*.key).map(*.value));
        # NOTE DB::Pg returns an Int for non-SELECT queries. We should probably abstract all this in some adapter class.
        # TODO Maybe make sure that we have a AST::Return::Count in that case?
        return $query ~~ Int ?? $query !! $return-class.populate($query);
    } does SignatureOverload.^parameterize($sig));
    $sub.set_name($name);
    return "&$name" => $sub,
            "ReturnType-$name" => $return-class;
}

sub EXPORT(File $file) {
    my $content = $file.IO.slurp;
    my $ast = FileGrammar.parse($content, :actions(FileActions.new));
    with $ast {
        my @h = $ast.made.map(&gen-sql-sub).flat;
        return @h.hash;
    } else {
        return Map.new;
    }
}

=begin pod

=head1 NAME

Badger - expose SQL queries as Raku subroutines

=head1 WHAT'S BADGER?

C<Badger> is a SQL library that allows you to invoke SQL snippets as
function as if it was Raku code. This way you can keep writing your
SQL queries by hand for performance and tweakability, and your tools
still recognize the C<.sql> files to help you work with them.

=head2 What does a Badger SQL file look like?

A badger-compatible SQL file is just a normal SQL file, with
signature headers.  These signatures are intended to look like Raku
signatures.

The most basic example:

=begin code :lang<sql>

-- sub my-query()
SELECT;

=end code

=head2 How do I feed Badger my SQL?

You have to pass the .sql file(s) to the C<use Badger> statement:

=begin code :lang<raku>

use Badger <sql/my-query.sql>; # The file in the previous code block

=end code

This will generate this function Raku-side:

=begin code :lang<raku>

sub my-query(Database $db --> Int) { ... }

=end code

Which you can call just like any other Raku subroutine, by passing
any object that has an interface similar to C<DB::Pg> (for now at
least) as the connection.

For parameters and return values, see below.

=head1 Parameters

A Badger SQL sub can have arguments that you can use in the SQL body.
Interpolation works for sigilled variables:

=begin code :lang<sql>

-- sub query-with-params($a, $b)
SELECT $a + $b, @c

=end code

This will generate a prepared query with C<$a> and C<$b> replaced C<$1>, C<$2>
(or with C<?>s depending on the RDBMS).

=head2 Parameter Sigils

The Raku allowed sigils are C<$> and C<@>. 

=head2 Parameter typing

You can put type annotations on the parameters:

=begin code :lang<sql>

-- sub query-with-params(Int $x, Int @xs)
SELECT $x = ANY(@xs)

=end code

If a parameter is typed, Badger will try to help you by inserting coercions in the generated SQL.
This is what the executed SQL looks like:

=begin code :lang<sql>

SELECT ($1::int) = ANY(($2::int[]))

=end code

=head2 Named Parameters

Parameters can be named, just like in Raku:

=begin code :lang<sql>

-- sub query-nameds(Int :$a, :$b)
SELECT $a + $b

=end code

Just like in Raku, you can't have a positional parameter after a named one.

=head2 Mandatory Named Parameters 

Also just like in Raku, named parameters can be marked mandatory:

=begin code :lang<sql>

-- sub query-nameds(:$mandatory!)
SELECT $a * 2

=end code

=head1 Return Sigils

=head2 + (default)

The default one -- in you don't specify a return sigil, you get this.
Returns the number of affected rows (as an C<Int>).

=begin code :lang<sql>

-- sub count-unnests(--> +)
-- ... or ...
-- sub count-unnests()
UPDATE products
   SET price = 999
   WHERE price IS NULL

=end code

=head2 $

Returns a single value. C<Nil> is returned otherwise:

=begin code :lang<sql>

-- sub get-username(Str $token --> $)
SELECT username
FROM users
WHERE token = $token

=end code

=head2 Typed $

Calls C<.new> on the given type with all the data returned from the SQL query:

=begin code :lang<sql>

-- sub get-user(Int $id --> MyApp::Models::User)
SELECT 1 AS id, 'steve' AS username

=end code

You'll usually need to import type module that provides the type, by placing
a C<use> at the top of the SQL file:

=begin code :lang<sql>

-- use MyApp::Models;

=end code

=begin code :lang<raku>

class MyApp::Models::User {
  has Int $.id;
  has Str $.username;
}
...
my MyApp::Models::User $user = get-user(db, 1);
# Result: MyApp::Models::User.new(id => 1, :username<steve>);

=end code

=head2 %

Returns a hash.

=begin code :lang<sql>

-- sub get-hash(--> %)
SELECT 'comment' as type, 'Hello world!' as txt

=end code

=begin code :lang<raku>

my %h = get-hash($db);
# Result: %(type => "comment", txt => "Hello world!")

=end code

If the database doesn't return anything, Badger gives you an empty hash back.

=head2 @

Returns an array of hashes.

=begin code :lang<sql>

-- sub get-hashes(--> @)
SELECT 'comment' as type, txt
FROM unnest(array['Hello', 'world!']) txt

=end code

=begin code :lang<raku>

my @hashes = get-hashes($db);
# Result: %(type => "comment", txt => "Hello"), %(type => "comment", txt => "world!")

=end code

=head2 Typed @

Calls C<.new> on the given type on each row of the data returned from the SQL query:

=begin code :lang<sql>

-- sub get-data(--> Datum @)
SELECT row_number() OVER () as id
     , unnest(ARRAY['a','b']) as value

=end code

=begin code :lang<raku>

class Datum {
  has Int $.id;
  has Str $.value;                                                                                                                                                    
}
...
my Datum @data = get-data($db);
# Result: Datum.new(id => 1, :value<a>), Datum.new(id => 2, :value<b>)

=end code

=head1 DESCRIPTION

=head1 AUTHORS

=item vedethiel
=item Jonathan Worthington

Source can be located at: https://github.com/raku-community-modules/Badger .
Comments and Pull Requests are welcome.

=head1 COPYRIGHT AND LICENSE

Copyright 2020 Edument AB

Copyright 2024 The Raku Community

This library is free software; you can redistribute it and/or modify it under the Artistic License 2.0.

=end pod

# vim: expandtab shiftwidth=4
