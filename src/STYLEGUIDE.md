# Style guide and design principles

The `sHoTT` project is an evolving community effort, and your participation is
most welcomed! However, to make the library as useful as possible for everyone,
we ask that everyone comply to a common set of style guidelines.

Good style conventions don't just serve to homogenize code and make things look
pretty, but they serve to

- Elucidate the structure of proofs and definitions through proper formatting.
- Effectively summarize definitions and arguments through good naming
  conventions.
- Make the formalization base easier to navigate.
- Help us maintain the repository.
- Provide techniques and habits that help you in the formalization process.

Please note that these conventions will and should change as the project and
language develops. We acknowledge that our code is not always consistent with
our conventions, and appreciate your help keeping the library compliant and
clean.

## The structure of code

We enforce strict formatting rules. These rules facilitate better readability of
the code and aids in understanding the structure of every. The general format of
a definition is as follows:

```rzk
#def concat
  ( p : x = y)
  ( q : y = z)
  : (x = z)
  := ind-path A y (\ z' q' → (x = z')) p z q
```

- We start with the name, and place every assumption on a new line.

- The conclusion of the definition is placed on its own line, which starts with
  a colon (`:`).

- On the next line, the walrus separator (`:=`) is placed, and after it follows
  the actual construction of the definition. If the construction does not fit on
  a single line, by which we mean fit within our stipulated 80-character limit,
  we immediately insert a new line after the walrus separator. Note, in
  particular, to avoid excessive indentation we do not indent the code an extra
  level in this particular case.

### The tree structure of constructions

In the Rzk language, every construction is structured like a tree, where each
operation can be seen as a branching point. We use indentation and
parenthization conventions to highlight this structure, which makes the code
more organized and readable. For example, when part of a definition extends
beyond a single line, we introduce line breaks at the earliest sensible
branching point, clearly displaying the tree structure of the definition. This
allows the reader to follow the branches of the tree, and to visually grasp the
scope of each operation and argument. Consider the following example about Segal
types:

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
    Σ ( h : hom A (k (0₂ , 0₂)) (k (1₂ , 1₂)))
    , ( hom2 A
        ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
        ( \ t → k (t , 0₂))
        ( \ t → k (1₂ , t))
        ( h)))
  ( second
    ( equiv-comp
      ( Σ ( k : Λ → A)
        , Σ ( h : hom A (k (0₂ , 0₂)) (k (1₂ , 1₂)))
          , ( hom2 A
              ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
              ( \ t → k (t , 0₂))
              ( \ t → k (1₂ , t))
              ( h)))
      ( Δ² → A)
      ( Λ  → A)
      ( inv-equiv
        ( Δ² → A)
        ( Σ ( k : Λ → A)
          , Σ ( h : hom A (k (0₂ , 0₂)) (k (1₂ , 1₂)))
            , ( hom2 A
                ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
                ( \ t → k (t , 0₂))
                ( \ t → k (1₂ , t))
                ( h)))
        ( equiv-horn-restriction A))
      ( horn-restriction A , is-local-horn-inclusion-A)))
  ( horn A x y z f g)
```

The root in this instance is the function
`projection-equiv-contractible-fibers`. It takes four arguments, each starting
on a fresh line and is parenthesized. Note that its parentheses are indented at
the same level as its parent node. The first argument fits neatly on one line,
but the second one is too large. In this case, we add a line break right after
the `→`-symbol following the lambda-abstraction, which we consider the earliest
branching point in this case. The next node is again `Σ`, with two arguments.
The first one fits on a line, but the second does not, so we add a line break
between them since `Σ` is only one character. This process is continued until
the definition is complete.

Observe also that we use indentation to highlight the branches. The extra space
after the opening parentheses marking a branch is there to visually emphasize
the tree structure of the definition, and synergizes with our convention to have
two-space indentation level increases.

What is generally considered the "earliest _sensible_ branching point" will
depend on context, and we ask that contributors practice common sense when
determining this. For instance, it may be sensible to group some arguments
together on a line. Already in our example above we wrote

```rzk
  hom2 A
  ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
  ( \ t → k (t , 0₂))
  ( \ t → k (1₂ , t))
  ( h)
```

visually grouping together `hom2` and `A`, and again the next three arguments,
emphasizing their connection to eachother. When in doubt, it is generally better
to break lines sooner rather than later.

## Other code conventions

- We employ an 80-character line length limit. This means that lines of code
  generally should not be longer than 80 characters. If they exceed this limit,
  they should be reformatted to fit within the limit by inserting appropriate
  line breaks.

  !!! info

      Names can be longer than the line character limit.

- We place binary operators/separators at the beginning of a line rather than
  the end. When they are a single character wide, this aligns very well with our
  parenthization and indentation rules. Consider for instance the following
  sample code:

  ```rzk
  ( moderately-long-name-of-a-function-A
    ( a-very-complicated-term-with-a-very-long-name-or-description-B
    , another-long-and-complicated-expression-for-another-term-C))
  ```

  Our indentation convention has the beautiful feature that we can determine the
  structure of the code simply by scanning the left edge of the code block. The
  placement of the comma separator in the example above complements this neatly,
  since we can immediately see that `function-A` is applied to the pair
  `(term-B , term-C)` by scanning the left edge of the code.

  Similarly, consider also

  ```rzk
  ( ( a-long-and-complicated-arithmetic-expression-involving-many-operations)
  * ( another-complicated-and-long-expression-with-symbols-and-numbers))
  ```

  By having the multiplication symbol on the start of the line we can
  immediately see that we are multiplying the two long expressions together, as
  opposed to performing some other operation.

  Similarly, we also place function type formation arrows at the start of the
  next line. E.g.

  ```rzk
  #def function
    ( parameter-1 : type-1)
    ( parameter-2 : type-2)
    : type-with-a-name-3
    → type-with-a-longer-name-4
    → short-type-5
    := undefined
  ```

  !!! warning

      This should not be confused with the convention for placement of arrows
      for lambda abstractions, which should be placed at the end of the line
      instead.

  When the binary operator/separator is more than a single character wide, e.g.
  for the walrus separator (`:=`) and identity type formation with explicitly
  passed underlying type (`=_{...}`), we insert a new line directly after the
  operator as well. I.e.

  ```rzk
  ( ( a-term-of-a-type)
  =_{ the-name-of-the-type}
    ( another-term-of-that-type))
  ```

- The `uses`-keyword and the accompanying list of variables is placed on their
  own lines.

  In the base case, write

  ```rzk
  #define my-name
    uses (my-variable-1 my-variable-2 ...)
    ( A : U)
    ...
  ```

  If the variable list (`(my-variable-1 my-variable-2 ...)`) does not fit on the
  first line together with `uses`, insert a line break directly after `uses` and
  write:

  ```rzk
  #define my-name
    uses
      ( my-variable-1 my-variable-2 ...)
    ( A : U)
    ...
  ```

  If the list still does not fit on a single line, start insert line breaks
  between variables. Here, there is some room for common sense in where the line
  breaks should be inserted, allowing for certain variable names to be grouped
  together:

  ```rzk
  #define my-name
    uses
      ( my-variable-1
        my-variable-2
        ...)
    ( A : U)
    ...
  ```

- If you find that the separation between the type signature of a definition and
  its construction is not visually clear, we permit the insertion of an
  additional line break after the walrus separator (`:=`).

## Naming conventions

Adhering to a good naming convention is essential for keeping the library
navigable and maintainable, and helps you make progress with your formalization
goals. Good names provide concise descriptions of an entry's purpose, and help
making the code in the library readable. The intent of our conventions can be
summarized as follows:

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
- In this way, our conventions should help generate names for definitions.
- Ultimately, our goal is for these conventions to support clear and
  maintainable code.

### A general naming scheme

With the basic purpose in mind, we present an adapted possible general naming
scheme originally due to Egbert Rijke.

The general pattern looks as follows:

```text
  [descriptor]-[output-type]-[input-types]-[Namespace]
```

Every part of the pattern is optional. However, their order is fixed. The
general naming pattern is broken into the following parts:

- **\[descriptor\]:** A custom descriptive name part for the entry.
- **\[output-type\]:** Refers to the concluding type of the entry.
- **\[input-types\]:** Consists of references to noteworthy input types.
- **\[Namespace\]:** Refers to an overarching concept, a subuniverse which the
  construction takes place in, or a general category the entry is about.

In particular, since Rzk does not currently have a suitable namespace mechanism,
the `[Namespace]` field serves as a reasonable substitute.

Now, let us consider some examples:

- ```rzk
  #def function-type-Segal
    ( A B : Segal)
    : Segal
  ```

  This definition uses the pattern `[output-type]-[Namespace]`.

- `is-segal-is-local-horn-inclusion` uses the pattern
  `[output-type]-[input-types]`.
- `is-equiv-identity` uses the pattern `[output-type]`.

The descriptor pattern is by far the most versatile one. Its purpose is to give
special meaningful descriptions that accurately represent some aspect, or
precisely the concept in question. For instance, if a concept is known best by a
special name, that name should probably be used.

- As an example, the canonical function with type signature

  ```rzk
  (A → B → C) → (A × B → C)
  ```

  should be called `uncurry`, using the `descriptor`-pattern. It should not, for
  instance, be called `map-from-product-map-of-maps`.

- Another example is `compute-hom-eq-extension-type-is-discrete`. This uses the
  pattern `[descriptor]-[output-type]-[input-types]`
  (`(compute)-(hom)-(eq-extension-type-is-discrete)`).

### Conclusions first!

The most noteworthy aspect of our general naming scheme is that conclusions
always end up at the start of the name. This has the benefit that the most
important aspect of a definition is what is mentioned first in its name.
Although it can take a little while to get used to this scheme as everything is
written in the opposite order you may be used to, it offers the following
central benefit: the name summarizes the entry's meaning efficiently, even if
only part of it is read. This means that when a reader is scanning the
application of a definition in a larger proof, they can get an overview by only
scanning the first few words at each branching point/line.

Hence, if you are at a loss for naming a definition, we offer you the following
simplified naming scheme: start with the first important assumption in your
definition statement, and to it, _prepend_ every subsequent important assumption
that is made. Finally, prepend the concluding type.

- For example, consider an entry with the following signature

  ```rzk
  #def ?????
    ( A B : U)
    ( is-prop-A : is-prop A)
    ( is-prop-B : is-prop B)
    ( (f , g) : iff A B)
    : is-equiv A B f
    := ...
  ```

  applying the scheme we get

  1. `is-prop`, noting the assumption that `A` is a proposition. We do not
     include variable names in the entry's name.
  2. `is-prop-is-prop`, noting the assumption that `B` is a proposition.
  3. `iff-is-prop-is-prop`, noting the assumption that we have a logical
     equivalence between `A` and `B`.
  4. `is-equiv-iff-is-prop-is-prop`, finally prepending the concluding type.

  Hence our final definition will be

  ```rzk
  #def is-equiv-iff-is-prop-is-prop
    ( A B : U)
    ( is-prop-A : is-prop A)
    ( is-prop-B : is-prop B)
    ( (f , g) : iff A B)
    : is-equiv A B f
    := ...
  ```

  Observe how it is immediately clear what the elements that go into the entry
  are, in which order they go, and what you get out if applying it!

### Table of common descriptors

To give a sense of the kind of general descriptors we use, we list some common
descriptors with examples in the table below.

| Descriptor           | Purpose                                                                                                             | Example                                 |
| -------------------- | ------------------------------------------------------------------------------------------------------------------- | --------------------------------------- |
| `coherence`          | Used for proofs of coherence.                                                                                       | `coherence-is-half-adjoint-equiv`       |
| `compute`            | Used for proofs of computation, which may be an identification or an element of any other identity system.          | `compute-postwhisker-homotopy-is-segal` |
| `Eq`                 | Used for identity systems on types where `htpy` or `equiv` is not an appropriate descriptor of the identity system. | `Eq-Σ`                                  |
| `eq`                 | Used as a descriptor for the identity type.                                                                         | `eq-htpy`                               |
| `equiv`              | Used for equivalences, and also for names of identity systems of universe-like types.                               | `equiv-ap-is-equiv`                     |
| `extensionality`     | Used for computations of identity types.                                                                            | `extensionality-Σ`                      |
| `homotopy` or `htpy` | Used for constructions of homotopies, and also for names of identity systems of function-like types.                | `homotopy-section-retraction-is-equiv`  |
| `is-property`        | Used when `is-prop` is unavailable.                                                                                 | `is-property-is-contr`                  |
| `map`                | Used in two ways: as the functorial action of a type constructor, but also as the underlying map of a morphism.     | `map-inverse-has-inverse`               |
| `type`               | Used for the underlying type of an object.                                                                          | `type-Segal`                            |
| `statement`          | Used for definitions which are statements of things.                                                                | `statement-homotopy-interchange-law`    |

### Exceptions and naming practices to avoid

- We use Unicode symbols in names very sparingly and only when they align with
  established mathematical practice. See the next section for more elaboration.

- We never refer to variables in definition names. The only instance we allow
  this is when that variable is available at every possible invoking site. For
  instance, we can name the argument of `is-segal-is-local-horn-inclusion` of
  type `is-local-horn-inclusion A` as `is-local-horn-inclusion-A`, since
  anywhere it can be invoked, the name `A` is also in scope. However, we would
  never name `is-segal-is-local-horn-inclusion` as
  `is-segal-A-is-local-horn-inclusion`.

- For technical lemmas or definitions, where the chance they will be reused is
  very low, the specific names do not matter as much. In these cases, you may
  resort to a simplified naming scheme, like enumeration. Please keep in mind,
  however, that if you find yourself appealing to this convention frequently,
  that is a sign that your code should be refactored.

In closing, we note that the naming conventions are aimed at improving the
readability of the code, not to ensure the shortest possible names, nor to
minimize the amount of typing by the implementers of the library.

## Use of Unicode characters

Although using Unicode characters in definition names is entirely permissible,
we recommend practicing restraint to maintain readability. For instance,
although products of shapes can be formed with the `×` binary operator, we
prefer to refer to it as `product` in names.

When it comes to using builtin syntactic features of `rzk`, however, we use the
following symbols:

- `→` should be used over `->` (`\to`)
- `↦` should be used over `|->` (`\mapsto`)
- `≡` should be used over `===` (`\equiv`)
- `≤` should be used over `<=` (`\<=`)
- `∧` should be used over `/\` (`\and`)
- `∨` should be used over `\/` (`\or`)
- `0₂` should be used over `0_2` (`0\2`)
- `1₂` should be used over `1_2` (`1\2`)
- `I × J` should be used over `I * J` (`\x` or `\times`)

!!! info

    For `first`, `second`, `TOP` and `BOT`, we prefer the ASCII versions as
    opposed to `π₁`, `π₂`, `⊤` and `⊥`, as we find the latter don't read too
    well in the code. Please also note that we usually prefer the use of
    named projections for special `Σ`-types when these are defined.

## Use of comments

Since we are using literate file formats, the need for comments in the code
should be heavily limited. If you feel the need to comment your code, then
please consider the following:

- Descriptive names for definitions should make their use self-documenting. If
  you are finding that you want to explain an application of a definition,
  consider giving it a better name, or creating an intermediate definition with
  a name that better describes your current aplication.

  In particular, if some family of `Σ`-types is given a name, we prefer to also
  define and use named projections for it instead of `first` and `second`. In
  many cases, their meaning is not immediately obvious, and so one could be
  tempted to annotate the code using comments to explain them.

  For example, instead of writing `first (second is-invertible-f)`, we define a
  named projection `is-section-is-invertible`. This may then be used as
  `is-section-is-invertible A B f is-invertible-f` elsewhere. This way, the code
  becomes self-documenting.

  However, we recognize that in Rzk, since we do not have the luxury of implicit
  arguments, this may sometimes cause overly verbose code. In such cases, you
  may revert to using `first` and `second`.

- Can your code be structured in a way that makes it more readable? Are you
  structuring it according to our conventions, or can our conventions be
  improved to make it more readable?

- Can the comments naturally be converted to prose that can be placed outside of
  the coding environment in the literate file?

## Literary conventions

- For consistency, we prefer to write in US English.

- Headers are written using sentence casing, as opposed to title casing.

- If the contents of a code block in some sense captures a section of an
  external source, the `title`-field may be used to reference that section.

  For example:

  ````md
  ```rzk title="RS17, Definition 10.6"
  #def is-rezk
    ( A : U)
    : U
    :=
    Σ ( is-segal-A : is-segal A)
    , ( (x : A)
      → (y : A)
      → is-equiv (x = y) (Iso A is-segal-A x y) (iso-eq A is-segal-A x y))
  ```
  ````

  The `title`-field may also be used to give descriptive headers to sections of
  your code.

- We use the autoformatting tool [Prettier](https://prettier.io/) to format
  markdown code, and we recommend that you install it or an alternative for use
  with your editor. Be aware that the formatting rules automated by Prettier are
  enforced by our CI workflow, so pull requests cannot be merged without the
  proper markdown formatting.

## Adapting and evolving the style guide

As mentioned in the introduction, we reiterate that this style guide will
necessarily evolve as we learn to use Rzk in new and better ways, and as the
language itself develops. Remember, the goal is at all times is to have code
that is easy to read, navigate and maintain, even for those who are not the
original authors.

## References

Our style guide and design principles borrow heavily from
[`agda-unimath`](https://github.com/UniMath/agda-unimath). If you are looking
for more inspiration, have a look at:

- [The design philosophy of `agda-unimath`](https://unimath.github.io/agda-unimath/DESIGN-PRINCIPLES.html#design-philosophy-of-agda-unimath)
- [The `agda-unimath` library style guide](https://unimath.github.io/agda-unimath/CODINGSTYLE.html)
- [Naming conventions for `agda-unimath`](https://unimath.github.io/agda-unimath/NAMING-CONVENTIONS.html)
