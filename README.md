<div align="center">

# Light Keeps the Ledger — Lean proofs

**Machine-checked finite algebra behind the paper: boundary elimination, the transition census, optical response as a reweighted metric, and the scope counterexamples that keep each statement honest.**

[![Lean proof check](https://github.com/dicipler-pixel/light-ledger-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/light-ledger-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.33.0-blue)
![Theorems](https://img.shields.io/badge/theorems-122-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.22123115-blue)](https://doi.org/10.5281/zenodo.22123115)

Jeromie Beasley

</div>

---

## Start here

| If you want to… | Open |
| :--- | :--- |
| Know exactly what is **not** proved | [`LIMITATIONS.md`](LIMITATIONS.md) |
| Check where every file came from | [`PROVENANCE.md`](PROVENANCE.md) |
| See the statements that must be rejected | [`FalseControls/`](FalseControls/) |

## What the library contains

The files keep their original module names and bytes, so their hashes match the verified
sources exactly. Several file headers still carry the note "NOT COMPILED" from the day they
were written, before they were first checked, and some point to `STATUS.json` or
`evidence/report.json`, which are not part of this repository; the check below is the current
evidence.

| Subject | File | Theorems |
| :--- | :--- | :-: |
| **Algebraic bridges**: universal identities used by the manuscript | [`LightBridges/Algebra`](LightBridges/Algebra.lean) | 6 |
| **Gram positivity**: every finite Gram form is positive semidefinite; purity is not a hypothesis | [`LightBridges/Gram`](LightBridges/Gram.lean) | 8 |
| **Transition-window census**: a division-free lower bound on the weight of a transition window | [`LightBridges/Census`](LightBridges/Census.lean) | 9 |
| **Coherence**: covariant squares, triangle holonomy, flatness as a composition law, the compression associator | [`LightBridges/Coherence`](LightBridges/Coherence.lean) | 5 |
| **Boundary elimination**: the Schur lift and the matrix Smith transform, every inverse stated as an equation | [`LightBridges/Boundary`](LightBridges/Boundary.lean) | 9 |
| **Ledger**: transpose symmetry and the exact finite determinant | [`LightBridges/Ledger`](LightBridges/Ledger.lean) | 7 |
| **Scalar optics**: the Smith loss identity and real/imaginary response algebra | [`LightBridges/ScalarOptics`](LightBridges/ScalarOptics.lean) | 8 |
| **Scope counterexamples**: oblique idempotents and the other exact examples that stop over-reaching claims | [`LightBridges/Examples`](LightBridges/Examples.lean) | 10 |
| **Optical response as a weighted metric**: positive weights, matching null directions, lower and upper bounds, and the peel: reducing channel weights cannot raise the response, and a null direction persists | [`OpticalMetric`](OpticalMetric.lean) | 16 |
| **Rigidity**: the regularized singular-value response and its positivity | [`Rigidity`](Rigidity.lean) | 8 |
| **Completion steps**: equal metric with unequal static response, the unique lossless two-pole zero between the poles, the calibration obstruction, equal weighted-Gram kernels | [`LightCompletion`](LightCompletion.lean) | 9 |
| **Edition 7.2** (§4.9e, §4.10a, §5.2): for a finite spectrum above a gap `a > 0` (weights `w ≥ 0`, readings `0 ≤ y, y₁, y₂ < a²`), `B/β(a) ≤ g` (Corollary 4.7), `2ag ≤ α₀`, `α₀² ≤ 2FB` and `α₀ ≤ R(y) ≤ α₀/(1 − y/a²)`; Theorem 4.9 on a finite grid of gaps `0 < t₀ < t₁ < …`: under upward redistribution with conserved total the metric change is nonnegative and, for a reading `y < t₀²`, vanishes exactly when the response change does; the confined oscillator reproduces `g = q²/(2mħΩ³)`, `α(ω) = q²/(m(Ω² − ω²))` and `F = q²ħ²/(2m)`, satisfies `α₀³ = 8g²F` (the equality case of the upper bound `α₀ ≤ 2(g²F)^{1/3}`, which is not itself formalized here), and gives the exact table; the identification target `R_η = c r ⇔ σ² = 1/(c r) − η`; no single constant calibrates the field-derivative candidate in the oscillator | [`LightSpectral`](LightSpectral.lean) | 27 |
| | **Total** | **122** |

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml) on GitHub:

1. **Build**: every module compiles against Lean v4.33.0 and Mathlib `v4.33.0`.
2. **Independent replay**: every module is re-checked by Lean's separate kernel checker.
3. **Axiom audit**: every named theorem depends only on `propext`, `Classical.choice` and
   `Quot.sound`. No `sorry`, no project axioms, no `native_decide`.
4. **False controls**: six deliberately false statements must fail to compile, for a
   mathematical reason: an oblique trace bound, a zero regulator, perfect absorption by a
   sheet, a tune-out that kills the metric, a reversed static bound, and the identification
   target without its regulator. The last two are written as explicit numeric instances, not
   through the library's definitions.

```bash
lake exe cache get
lake build
python3 scripts/verify.py
```

## The paper

*Light Keeps the Ledger*, Jeromie Beasley. DOI
[10.5281/zenodo.22123115](https://doi.org/10.5281/zenodo.22123115).

## Citation, licence and AI use

Citation metadata is in [`CITATION.cff`](CITATION.cff). The Lean code and scripts are released under the [MIT License](LICENSE) and the written text under [CC BY 4.0](LICENSE-CC-BY-4.0.md); see [`LICENSING.md`](LICENSING.md). How AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
