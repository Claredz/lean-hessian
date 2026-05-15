# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Commands

- `lake build` — build the `Hessian` Lean library. This currently succeeds with a warning because `second_order_necessary_condition_gradient` uses `sorry`.
- `lake env lean Hessian/Basic.lean` — check the main source file directly; use this as the closest equivalent to running a single test/file check.
- `lake env lean Hessian.lean` — check the root module and its imports.
- There is no dedicated test suite or test target in this repository at present.
- There is no configured lint executable; `lake exe lint Hessian` is not available. CI currently relies on `leanprover/lean-action@v1`.

## Project structure

This is a Lean 4 project named `hessian`, using Lean `v4.29.1` and mathlib `v4.29.1` as pinned in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

The Lake configuration defines a single Lean library:

- `Hessian.lean` is the root module. It imports modules that should be built as part of the library.
- `Hessian/Basic.lean` contains the current formalization work.

`Hessian/Basic.lean` sets up a real inner product space context and defines:

- `LocalMinimumAt` for local minima of functions `E → ℝ`.
- `HessianOp` as the Fréchet derivative of the gradient, `D(∇f)(x)`.
- `PosSemidefOp` and `HessianPosSemidefAt` for positive semidefinite continuous linear operators and Hessians.
- `second_order_necessary_condition_gradient`, the main second-order necessary condition theorem, currently left as `sorry`.
- Basic closure/examples for positive semidefinite operators: zero, addition, nonnegative scalar multiplication, constant-function Hessian.
- A finite-dimensional matrix representation section using `EuclideanSpace ℝ (Fin n)`.

When adding new Lean files under `Hessian/`, import them from `Hessian.lean` if they should be included in `lake build`.

## CI

`.github/workflows/lean_action_ci.yml` runs on pushes, pull requests, and manual dispatch. It checks out the repository and runs `leanprover/lean-action@v1` on Ubuntu.
