# Simplicial HoTT and synthetic ∞-categories

!!! info

    This project originated as a fork of [:material-github: emilyriehl/yoneda](https://github.com/emilyriehl/yoneda).

This is a formalization library for simplicial Homotopy Type Theory (sHoTT) with
the aim of proving resulting in synthetic ∞-category theory, starting with the
results from the following papers:

- "[A type theory for synthetic ∞-categories](https://higher-structures.math.cas.cz/api/files/issues/Vol1Iss1/RiehlShulman)"
  [^1]
- "[Synthetic fibered (∞,1)-category theory](https://doi.org/10.21136/HS.2023.04)"
  [^2]
- "[Limits and colimits of synthetic ∞-categories](https://arxiv.org/abs/2202.12386)"
  [^3]

This formalization project follows the philosophy laid out in the article
"[Could ∞-category theory be taught to undergraduates?](https://www.ams.org/journals/notices/202305/noti2692/noti2692.html)"
[^4].

The formalizations are implemented using
[`rzk`](https://github.com/rzk-lang/rzk), an experimental proof assistant for a
variant of type theory with shapes.

See the list of contributors to this formalisation project at
[`CONTRIBUTORS.md`](CONTRIBUTORS.md).

## Checking the formalisations locally

It is recommended to use
[VS Code extension for Rzk](https://rzk-lang.github.io/rzk/v0.6.2/getting-started/install/)
(available in
[Visual Studio Marketplace](https://marketplace.visualstudio.com/items?itemName=NikolaiKudasovfizruk.rzk-1-experimental-highlighting),
as well as in
[Open VSX](https://open-vsx.org/extension/NikolaiKudasovfizruk/rzk-1-experimental-highlighting)).
The extension should then manage an `rzk` executable and provide some feedback
directly in VS Code, without users having to use the command line.

Otherwise, install the
[`rzk`](https://rzk-lang.github.io/rzk/latest/getting-started/install/) proof
assistant
[from sources](https://rzk-lang.github.io/rzk/v0.6.2/getting-started/install/#install-from-sources).
Then run the following command from the root of this repository:

```sh
rzk typecheck src/hott/* src/simplicial-hott/*
```

[^1]:
    Emily Riehl & Michael Shulman. A type theory for synthetic ∞-categories.
    Higher Structures 1(1), 147-224. 2017. <https://arxiv.org/abs/1705.07442>

[^2]:
    Ulrik Buchholtz and Jonathan Weinberger. Synthetic fibered (∞, 1)-category
    theory. Higher Structures 7 (2023), 74–165. Issue 1.
    <https://doi.org/10.21136/HS.2023.04>

[^3]:
    César Bardomiano Martínez. Limits and colimits of synthetic ∞-categories.
    1-33, 2022. <https://arxiv.org/abs/2202.12386>

[^4]:
    Emily Riehl. Could ∞-category theory be taught to undergraduates? Notices of
    the AMS. May 2023.
    <https://www.ams.org/journals/notices/202305/noti2692/noti2692.html>
