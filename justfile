set quiet

rust_nightly_version := `cat rust-toolchain-nightly`

@default: fmt lint test

fmt:
    cargo '+{{rust_nightly_version}}' fmt --all

lint strict="":
    cargo '+{{rust_nightly_version}}' fmt -- --check
    cargo clippy \
        --workspace \
        --tests \
        --benches \
        --all-targets \
        --all-features \
        --quiet \
        -- {{ if strict != "" { "-D warnings" } else { "" } }}
    cargo doc --all --no-deps --document-private-items --all-features --quiet

test:
    cargo test --workspace --all-features