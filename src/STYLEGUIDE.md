# Style guide and design principles

This guide provides a set of design principles and guidelines for the `sHoTT`
project.

Our style and design principles borrows heavily from
[`agda-unimath`](https://github.com/UniMath/agda-unimath).

## The structure of code

We enforce strict formatting rules. This formatting allows the type of the
defined term to be easily readable, and aids in understanding the structure of
the definition.

The general format of a definition is as follows:

```rzk
#def concat
  ( p : x = y)
  ( q : y = z)
  : (x = z)
  :=
    ind-path A y (\ z' q' → (x = z')) p z q
```

- We start with the name, and place every assumption on a new line.

- The conclusion of the definition is placed on its own line, which starts with
  a colon (`:`).

- Then, on the next line, the walrus separator (`:=`) is placed, and after it
  follows the actual construction of the definition. If the construction does
  not fit on a single line, we immediately insert a new line after the walrus
  separator and indent the code an extra level (2 spaces).

In the Rzk language, every construction is structured like a tree, where each
operation can be seen as a branching point. We use indentation levels and
parentheses to highlight this structure, which makes the code more organized and
readable. For example, when part of a definition extends beyond a single line,
we introduce line breaks at the earliest branching point, clearly displaying the
tree structure of the definition. This allows the reader to follow the branches
of the tree, and to visually grasp the scope of each operation and argument.
Consider the following example about Segal types:

```rzk
#def is-segal-is-local-horn-inclusion
  ( A : U)
  ( is-local-horn-inclusion-A : is-local-horn-inclusion A)
  : is-segal A
  :=
    \ x y z f g →
    contractible-fibers-is-equiv-projection
      ( Λ → A)
      ( \ k →
        Σ ( h : hom A (k (0₂ , 0₂)) (k (1₂ , 1₂))) ,
          ( hom2 A
            ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
            ( \ t → k (t , 0₂))
            ( \ t → k (1₂ , t))
            ( h)))
      ( second
        ( equiv-comp
          ( Σ ( k : Λ → A) ,
            Σ ( h : hom A (k (0₂ , 0₂)) (k (1₂ , 1₂))) ,
              ( hom2 A
                ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
                ( \ t → k (t , 0₂))
                ( \ t → k (1₂ , t))
                ( h)))
          ( Δ² → A)
          ( Λ  → A)
          ( inv-equiv
            ( Δ² → A)
            ( Σ ( k : Λ → A) ,
              Σ ( h : hom A (k (0₂ , 0₂)) (k (1₂ , 1₂))) ,
                ( hom2 A
                  ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
                  ( \ t → k (t , 0₂))
                  ( \ t → k (1₂ , t))
                  ( h)))
            ( equiv-horn-restriction A))
          ( horn-restriction A , is-local-horn-inclusion-A)))
      ( horn A x y z f g)
```

The root here is the function `projection-equiv-contractible-fibers`. It takes
four arguments, each starting on a fresh line and is indented an extra level
from the root. The first argument fits neatly on one line, but the second one is
too large. In these cases, we add a line break right after the `→`-symbol
following the lambda-abstraction, which we consider the earliest branching point
in this case. The next node is again `Σ`, with two arguments. The first one fits
on a line, but the second does not, so we add a line break between them. This
process is continued until the definition is complete.

Note also that we use parentheses to mark the branches. The extra space after
the opening parentheses marking a branch is there to visually emphasize the tree
structure of the definition, and synergizes with our convention to have
two-space indentation level increases.

## Naming conventions

Adhering to a good naming convention is essential for keeping the library
navigable and maintainable, and helps you make progress with your formalization
goals. Good names provide concise descriptions of an entry's purpose, and help
making the code in the library readable.

- Entry names aim to concisely describe their mathematical concept, using
  well-known mathematical vocabulary.
- While an entry's name reflects its concept, it avoids relying on the details
  of its formalization. This way, a user is not required to know how something
  is formalized in order to reference an entry.
- Even with only minimal knowledge of the conventions, readers should be able to
  intuitively grasp an entry's purpose from its name.
- The naming conventions should apply regardless of topic or subfield.
- For many common kinds of entries, our naming conventions should offer a
  predictable suggestion of what its name should be.
- Ultimately, our goal is for these conventions to support clear and
  maintainable code.

> - Add example
> - prepending assumptions and then conclusion. General format of names
>
> > The naming conventions are aimed at improving the readability of the code,
> > not to ensure the shortest possible names, nor to minimize the amount of
> > typing by the implementers of the library.

> - We mainly use lower case names with words separated by hyphens.

- Capitalized names are reserved for subuniverses and similar "namespaces". When
  a construction is made internally to such a collection, we _append_ its name.
  For instance, the subuniverse of Segal types is called `Segal`, and the
  function type formation in that subuniverse , called `function-type-Segal,`
  has the following signature:

  ```rzk
  #def function-type-Segal
    ( A B : Segal)
    : Segal
  ```

- Use meaningful names that accurately represent the concepts applied. For
  example, if a concept is known best by a special name, that name should
  probably be used.

- For technical lemmas or definitions, where the chance they will be reused is
  very low, the specific names do not matter as much. In these cases, one may
  resort to a simplified naming scheme, like enumeration. Please keep in mind,
  however, that if you find yourself appealing to this convention frequently,
  that is a sign that your code should be refactored.

- We use Unicode symbols in names very sparingly and only when they align with
  established mathematical practice.

## Use of Unicode characters

In defined names we use Unicode symbols sparingly and only when they align with
established mathematical practice. For the builtin syntactic features of `rzk`,
however, we prefer the following Unicode symbols:

- `→` should be used instead of `->` (`\to`)
- `↦` should be used instead of`|->` (`\mapsto`)
- `≡` should be used instead of `===` (`\equiv`)
- `≤` should be used instead of `<=` (`\<=`)
- `∧` should be used instead of `/\` (`\and`)
- `∨` should be used instead of `\/` (`\or`)
- `0₂` should be used instead of `0_2` (`0\2`)
- `1₂` should be used instead of `1_2` (`1\2`)
- `I × J` should be used instead of `I * J` (`\x` or `\times`)

!!! info

    For `first`, `second`, `TOP` and `BOT`, we prefer the ASCII versions as
    opposed to `π₁`, `π₂`, `⊤` and `⊥`, as we find the latter don't read too
    well in the code. Please also note that we usually prefer the use of
    named projections for special Sigma-types when these are defined.

## Use of comments

Since we are using literate file formats, the need for comments in the code
should be heavily limited. If you feel the need to comment your code, then
please consider the following:

- Descriptive names for definitions should make their use self-documenting. If
  you are finding that you want to explain an application of a definition,
  consider giving it a better name, or creating an intermediate definition with
  a name that better describes your current aplication.

  In particular, if a particular family of Sigma types is given a name, we
  prefer to also create and use named projections instead of `first` and
  `second`. In many cases, their meaning is not immediately obvious, and so one
  could be tempted to annotate the code with their meaning using comments.

  For instance, instead of writing `first (second is-invertible-f)`, we define a
  named projection `is-section-is-invertible`. This may then be used as
  `is-section-is-invertible A B f is-invertible-f` elsewhere. This way, the code
  becomes self-documenting, and much easier to read.

  However, we recognize that in `rzk`, since we do not have the luxury of
  implicit arguments, this may sometimes cause unnecessarily verbose code. In
  such cases, you may revert to using `first` and `second`.

- Can your code be structured in a way that makes it more readable? Are you
  structuring it according to our conventions, or can our conventions be
  improved to make it more readable?

- Can the comments naturally be converted to prose that can be placed outside of
  the coding environment in the literate file?

## Literary conventions

- We write in US English.
- Headers are written using sentence casing, as opposed to title casing.

## Adapting and evolving the style guide

This style guide should evolve as Rzk develops and grows. If new features are
added to the language or if there is made changes to the syntax of the language,
their use should be incorporated into this style guide.

Remember, the goal is at all times is to have code that is easy to read,
navigate and maintain, even for those who are not the original authors.
