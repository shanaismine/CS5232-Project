# Formal Verification of the Futurama Theorem

**CS5232 — Specification and Verification of Systems (Spring 2026)**
**Author:** Yilun Li (A0182429Y)

## Overview

A machine-checked formalisation of the **Futurama Theorem** (Keeler's Theorem) in Lean 4 using Mathlib. The theorem states that any permutation on a finite set can be undone by a sequence of distinct transpositions, each involving one of two auxiliary elements.

| Theorem | Status | Description |
|---------|--------|-------------|
| `keeler_identity` | ✅ Proven | Keeler sequence correctly cancels any single cycle |
| `keelerSeq_uses_auxiliary` | ✅ Proven | Every transposition involves auxiliary x or y |
| `keelerSeq_nodup` | ✅ Proven | No transposition is repeated |
| `keeler_theorem` | 📝 Sorry | Full theorem for arbitrary permutations (proof sketch in comments) |

## Building

```bash
git clone <repo-url>
cd <repo>/Lean
elan override set leanprover/lean4:v4.23.0
lake build
```

## Verifying

Open `Project/futurama.lean` in VS Code with the Lean 4 extension. All theorems except `keeler_theorem` are fully verified.

## Evaluation

A computational sanity check is included at the end of the file:

```lean
#eval evalCycle [5, 1, 2, 3, 4] 6 7
-- Expected: [0, 1, 2, 3, 4, 5, 7, 6]
```

This applies the Keeler sequence for the 5-cycle `(5 1 2 3 4)` with helpers `x=6, y=7`. The output `[0, 1, 2, 3, 4, 5, 7, 6]` confirms that all cycle elements are restored to their original positions, with only `x` and `y` swapped.

## File Structure

```
Lean/
├── Project/
│   └── futurama.lean       # Main formalisation
├── Project.lean             # Root import
├── lakefile.toml
└── lean-toolchain
```