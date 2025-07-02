# Finite Geometry in Lean 4

A little project in which I'm formalizing Leandro Caniglia's notes on Finite Geometry in Lean 4, using LLMs as much as possible.
Currently, it only contains the basics of Latin squares and [Mutually Orthogonal Latin Squares (MOLS)](https://en.wikipedia.org/wiki/Mutually_orthogonal_Latin_squares), which I learned because of their application in statistics, specifically in incomplete U-statistics.
> Blom, G. (1976). Some Properties of Incomplete U-Statistics. *Biometrika*, 63(3), 573–580. [Oxford University Press](https://doi.org/10.2307/2335635).

## Overview

This project formalizes key concepts from finite geometry, specifically:

- **Latin Squares**: Square arrays where each symbol appears exactly once in each row and column
- **Mutually Orthogonal Latin Squares (MOLS)**: Pairs of Latin squares with the orthogonality property
- **Bounds on MOLS**: Upper bounds on the maximum number of pairwise orthogonal Latin squares

## Key Features

### Latin Squares

- Formal definition of Latin squares using `Fin n → Fin n → Fin n`
- Condition that rows and columns are injective functions
- Support for matrix-style notation `A[(i,j)]`
- Equivalences between rows/columns and bijective functions

### Orthogonality

- Definition of orthogonal Latin squares using pair mappings
- Equivalence between injectivity and bijectivity for finite sets
- Pairwise orthogonality for collections of Latin squares

### MOLS Construction over Finite Fields

- Construction of Latin squares `L_m` over finite fields `K`
- Formula: `L_m(i,j) = i + m·j` (where `m ≠ 0`)
- Proof of orthogonality: `L_m₁ ⊥ L_m₂` when `m₁ ≠ m₂`
- Complete family of `|K| - 1` MOLS for any finite field `K`

### Bounds

- At most `n - 1` pairwise orthogonal Latin squares of order `n ≥ 2`
- Constructive proof using counting arguments and the pigeonhole principle

## 🧮 Mathematical Background

### Latin Squares

A **Latin square** of order `n` is an `n × n` array filled with `n` different symbols, each occurring exactly once in each row and exactly once in each column.

### Orthogonality

Two Latin squares `A` and `B` are **orthogonal** if the ordered pairs `(A[i,j], B[i,j])` are all distinct as `(i,j)` ranges over all positions.

### Key Theorem

For any finite field `K` with `n` elements, there exists a complete set of `n - 1` mutually orthogonal Latin squares of order `n`.

## 🚀 Getting Started

### Prerequisites
- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html)
- [Mathlib](https://github.com/leanprover-community/mathlib4)

### Building
```bash
# Clone the repository
git clone [your-repo-url]
cd finite_geometry

# Build the project
lake build

# Check for errors
lake exe cache get
```

### Usage
```lean
import FiniteGeometry.MOLS

-- Define a Latin square over a finite field
variable {K : Type*} [Field K] [Fintype K]

-- Create MOLS for different parameters
noncomputable def myMOLS (m : K) (h : (0 : K) ≠ m) : LatinSquare (Fintype.card K) :=
  L_square h

-- Verify orthogonality
example (m₁ m₂ : K) (h₁ : (0 : K) ≠ m₁) (h₂ : (0 : K) ≠ m₂) (h : m₁ ≠ m₂) :
    (L_square h₁) ⊥ (L_square h₂) :=
  L_square_orth h₁ h₂ h
```

## 📚 Main Results

1. **Construction Theorem**: For any finite field `K`, the squares `L_m` (where `m ≠ 0`) form a family of mutually orthogonal Latin squares.

2. **Orthogonality Theorem**: If `m₁ ≠ m₂` (both non-zero), then `L_m₁ ⊥ L_m₂`.

3. **Cardinality Bound**: Any collection of pairwise orthogonal Latin squares of order `n ≥ 2` has at most `n - 1` elements.

4. **Optimality**: The construction over finite fields achieves this bound: for prime powers `q`, we get exactly `q - 1` MOLS of order `q`.
