set quiet

rust_nightly_version := `cat rust-toolchain-nightly`

# Call `fmt`, `lint`, `test`, and `check-readme`.
@default: fmt lint test check-readme

# Format all Rust code.
fmt:
    cargo '+{{rust_nightly_version}}' fmt --all

# Lint all code.
lint:
    cargo '+{{rust_nightly_version}}' fmt -- --check
    cargo clippy \
        --workspace \
        --tests \
        --benches \
        --all-targets \
        --all-features \
        --quiet
    cargo doc --all --no-deps --document-private-items --all-features --quiet

# Run all tests.
test:
    cargo test --workspace --all-features

# Install the nightly version needed for `fmt` and `lint`.
install-nightly:
    rustup toolchain install '{{rust_nightly_version}}'

install-cargo-rdme:
    cargo install cargo-rdme

update-readme:
    cargo rdme

check-readme:
    cargo rdme --check