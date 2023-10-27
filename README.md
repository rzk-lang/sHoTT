# Simplicial HoTT and synthetic ∞-categories

[![Typecheck with latest Rzk](https://github.com/rzk-lang/sHoTT/actions/workflows/rzk.yml/badge.svg)](https://github.com/rzk-lang/sHoTT/actions/workflows/rzk.yml)
[![MkDocs to GitHub Pages](https://github.com/rzk-lang/sHoTT/actions/workflows/mkdocs.yml/badge.svg)](https://github.com/rzk-lang/sHoTT/actions/workflows/mkdocs.yml)

> :information_source: This project originated as a fork of
> https://github.com/emilyriehl/yoneda.

This is a formalization library for simplicial Homotopy Type Theory (sHoTT) with
the aim of proving resulting in synthetic ∞-category theory, starting with the
results from the following papers:

- "[A type theory for synthetic ∞-categories](https://higher-structures.math.cas.cz/api/files/issues/Vol1Iss1/RiehlShulman)"
  [1]
- "[Synthetic fibered (∞,1)-category theory](https://doi.org/10.21136/HS.2023.04)"
  [2]
- "[Limits and colimits of synthetic ∞-categories](https://arxiv.org/abs/2202.12386)"
  [3]

This formalization project follows the philosophy laid out in the article
"[Could ∞-category theory be taught to undergraduates?](https://www.ams.org/journals/notices/202305/noti2692/noti2692.html)"
[4].

The formalizations are implemented using
[`rzk`](https://github.com/rzk-lang/rzk), an experimental proof assistant for a
variant of type theory with shapes. See the list of contributors at
[`src/CONTRIBUTORS.md`](src/CONTRIBUTORS.md).

The formalizations can be viewed as markdown files rendered at
[rzk-lang.github.io/sHoTT/](https://rzk-lang.github.io/sHoTT/) using syntax
highlighting supplied by
[MkDocs plugin for Rzk](https://github.com/rzk-lang/mkdocs-plugin-rzk).

## Checking the formalisations locally

Install the
[`rzk`](https://rzk-lang.github.io/rzk/latest/getting-started/install/) proof
assistant. Then run the following command from the root of this repository:

```sh
rzk typecheck
```

Please also have a look at our [style guide](src/STYLEGUIDE.md) before
submitting your pull request.

# References

1. Emily Riehl & Michael Shulman. A type theory for synthetic ∞-categories.
   Higher Structures 1(1), 147-224. 2017. https://arxiv.org/abs/1705.07442

2. Ulrik Buchholtz and Jonathan Weinberger. 2023. Synthetic fibered (∞,
   1)-category theory. Higher Structures 7 (2023), 74–165. Issue 1.
   https://doi.org/10.21136/HS.2023.04

3. César Bardomiano Martínez. Limits and colimits of synthetic ∞-categories.
   1-33, 2022. https://arxiv.org/abs/2202.12386

4. Emily Riehl. Could ∞-category theory be taught to undergraduates? Notices of
   the AMS. May 2023.
   https://www.ams.org/journals/notices/202305/noti2692/noti2692.html
