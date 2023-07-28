pull-request: fmt test-rust


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


target := 'x86_64-unknown-linux-gnu'

# Test prqlc
test-rust:
    @echo "Testing prqlc…"

    cargo clippy --all-targets --target={{ target }} -- -D warnings

    @# Note that `--all-targets` doesn't refer to targets like
    @# `wasm32-unknown-unknown`; it refers to lib / bin / tests etc.
    @#
    @# Autoformatting doesn't make this clear to read, but this tertiary
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

# Build the website, including the book & playground.
build-web:
    mkdir -p web/website/public

    # Build website
    cd web/website && hugo --minify

    # Build book
    cd web/book && mdbook build
    @# Copy the book into the website path, using rsync so it only copies new files
    @rsync -ai --checksum --delete web/book/book/ web/website/public/book/

    just build-web-playground

build-web-playground:
    @# Must set `install-links=false` in the playground's `npm install` to
    @# install prql-js as the regular dependency, instead of creating a
    @# symlink. Refer to https://github.com/PRQL/prql/pull/1296.
    cd web/playground && npm install --install-links=false
    cd web/playground && npm run build

    # We place the playground app in a nested path, because we want to use
    # prql-lang.org/playground with an iframe containing the playground.
    # Possibly there's a more elegant way of doing this...
    rsync -ai --checksum --delete web/playground/build/ web/website/public/playground/playground/

run-web-site:
    cd web/website && hugo --minify

run-web-book:
    cd web/book && mdbook serve

# Build & serve the playground.
run-web-playground:
    cd web/playground && npm install --install-links=false
    cd web/playground && npm start

# Build & serve the website & playground.
run-web:
    # Note that this only live-reloads the static website; and requires
    # rerunning to pick up playground & book changes.

    just build-web

    cd web/website && hugo server --renderToDisk


python_bindings := 'target/bindings/python'

build-python mode='debug':
    #!/usr/bin/env bash
    if [ '{{mode}}' = 'release' ]; then
        release='--release'
    else
        release=''
    fi

    maturin build $release \
       -o {{python_bindings}} \
       -m prqlc/bindings/python/Cargo.toml


test-python:
    #!/usr/bin/env bash
    just build-python
    python -m venv target/venv
    source target/venv/bin/activate
    pip install {{python_bindings}}/prql_python-*.whl
    pip install -r prqlc/bindings/python/requirements.txt
    pytest
