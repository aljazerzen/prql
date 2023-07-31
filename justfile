choose-recipe:
    @just --choose

pull-request: fmt prqlc-test

fmt:
    @echo '--- remove trailing whitespace ---'
    @rg '\s+$' --files-with-matches --glob '!*.rs' . \
        | xargs -I _ sh -c "echo _ && sd '[\t ]+$' '' _"

    @echo '--- no-dbg ---'
    @! rg 'dbg!' --glob '*.rs' . --no-heading

    @echo '--- cargo fmt ---'
    @cargo fmt --all

    @echo '--- prettier ---'
    @prettier --write . \
            --config=.config/prettier.yaml \
            --ignore-path=.config/prettierignore \
            --ignore-unknown \
            --log-level=warn


    @echo '--- nixpkgs-fmt ---'
    @nixpkgs-fmt flake.nix


prqlc-lint:
    @echo '--- clippy ---'
    @cargo clippy --all --fix --allow-staged


target := 'x86_64-unknown-linux-gnu'

# Test prqlc
prqlc-test:
    @echo "Testing prqlc…"

    cargo clippy --all-targets --target={{ target }} -- -D warnings

    @# Note that `--all-targets` doesn't refer to targets like
    @# `wasm32-unknown-unknown`; it refers to lib / bin / tests etc.
    @#
    @# Autoformatting does not make this clear to read, but this tertiary
    @# expression states to run:
    @# - External DB integration tests — `--features=test-dbs-external`
    @#   on Linux
    @# - No features on Windows
    @# - Internal DB integration tests — `--features=test-dbs` otherwise
    @#
    @# Below, we also add:
    @# - Unreferenced snapshots - `--unreferenced=auto` on Linux
    @#
    @# We'd like to reenable on Windows, ref https://github.com/wangfenjin/duckdb-rs/issues/179.

    cargo test --no-run --locked --target={{ target }}

    cargo insta test --target={{ target }}



# Build & serve the website & playground.
web-run:
    # Note that this only live-reloads the static website; and requires
    # rerunning to pick up playground & book changes.

    just web-build

    cd web/website && hugo server --renderToDisk

# Build the website, including the book & playground.
web-build:
    just web-site-build

    just web-book-build

    just web-playground-build

web-clean:
    rm -rf web/build

web-site-build:
    cd web/website && hugo --minify

web-book-run:
    cd web/book && mdbook serve

web-book-build:
    cd web/book && mdbook build

web-playground-build:
    @# Must set `install-links=false` in the playground's `npm install` to
    @# install prql-js as the regular dependency, instead of creating a
    @# symlink. Refer to https://github.com/PRQL/prql/pull/1296.
    cd web/playground && npm install --install-links=false
    cd web/playground && npm run build

    # We place the playground app in a nested path, because we want to use
    # prql-lang.org/playground with an iframe containing the playground.
    # Possibly there's a more elegant way of doing this...
    rsync -ai --checksum --delete web/playground/build/ web/build/playground/playground/

# Build & serve the playground.
web-playground-run:
    cd web/playground && npm install --install-links=false
    cd web/playground && npm start

web-check-links:
    just web-clean

    just web-site-build
    just web-book-build
    
    @ # we do not build playground here, as it is slow and does not contain much links
    @ # so we have to fake that it exists
    @mkdir web/build/playground/playground
    @touch web/build/playground/playground/index.html

    hyperlink web/build/



python_bindings := 'target/bindings/python'

prqlc-python-build mode='debug':
    #!/usr/bin/env bash
    if [ '{{mode}}' = 'release' ]; then
        release='--release'
    else
        release=''
    fi

    maturin build $release \
       -o {{python_bindings}} \
       -m prqlc/bindings/python/Cargo.toml

prqlc-python-test:
    #!/usr/bin/env bash
    just python-build
    python -m venv target/venv
    source target/venv/bin/activate
    pip install {{python_bindings}}/prql_python-*.whl
    pip install -r prqlc/bindings/python/requirements.txt
    pytest
