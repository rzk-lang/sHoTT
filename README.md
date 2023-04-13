# sHoTT

[![MkDocs](https://shields.io/badge/MkDocs-documentation-informational)](https://fizruk.github.io/rzk/split.html)

This is a formalisation library for simplicial Homotopy Type Theory (sHoTT).

You can browse the rendered formalisations at https://fizruk.github.io/sHoTT/

The formalisations are implemented using [`rzk`](https://github.com/fizruk/rzk), an experimental proof assistant for a variant of type theory with shapes strongly based on Riehl and Shulman's type theory for synthetic ∞-categories [1].

## Checking the Formalisations Locally

Install [`rzk`](https://github.com/fizruk/rzk) proof assistant. Then run the following command from the root of this repository:

```sh
rzk typecheck src/hott/* src/simplicial-hott/*
```

## Building the Documentation Locally

First, you need to install [MkDocs](https://www.mkdocs.org/getting-started/) and `mdx_math` Markdown extension (to enable LaTeX):

```sh
pip install python-markdown-math
```

Now, you can build and serve the documentation locally by running

```sh
mkdocs serve --config-file docs/mkdocs.yml
```

The (locally built) documentation should be available at http://127.0.0.1:8000

The pages of the documentation are the `*.md` files in [docs/docs](docs/docs) directory and its subdirectories.
To add a new page, you can create a new `*.md` file and add it to the navigation by modifying [docs/mkdocs.yml](docs/mkdocs.yml).

# References

1. Emily Riehl, & Michael Shulman. (2017). A type theory for synthetic ∞-categories. https://arxiv.org/abs/1705.07442
