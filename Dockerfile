FROM rust:1.89-alpine

COPY . .

RUN cargo test --workspace
