# Light 7.2: paper and formalization scope

Jeromie Beasley · repository documentation updated 16 October 2026

## Description

*Light Keeps the Ledger* constructs its metric and ledger registers in explicit finite models. The ledger construction requires an admissible resolvent contour and an analytic branch rather than a local pairing. Its integer rank/winding content can survive metric degeneration while the required admissibility conditions remain valid; the ledger value itself is even, not generally constant.

Light as the carrier and matter as the source of the relevant constraints is the paper's organizing interpretation **[H]**, a hypothesis rather than a consequence of the finite algebra.

Edition 7.2 includes gapped spectral-measure bounds on the metric from subgap optical readings, the conserved-strength redistribution theorem, and an exactly solved confined oscillator realizing that redistribution. The formal coverage below is narrower than the full written results.

AI-assisted research and exposition; Jeromie Beasley is responsible for the claims and their interpretation. See [AI_USE.md](AI_USE.md).

## What Lean covers

The repository contains **122 named theorems**, including **27 in LightSpectral**. Earlier paper counts of 91 or 95 describe older inventories; they must not be presented as the current repository total.

| Paper result | Named Lean statements in LightSpectral | Scope |
| --- | --- | --- |
| Corollary 4.7, lower bound from two readings | `kernelRatio_antitone`, `kernelRatio_pos`, `secant_le_kernelRatio_metric`, `secant_div_le_metric` | Finite nonnegative spectrum above a positive gap; subgap readings. Does not certify every bound in the written corollary. |
| Corollary 4.8 | `static_lower`, `static_sq_le`, `moment3_le_secant`, `static_sq_le_budget_secant`, `response_bracket` | Finite-spectrum inequalities under the hypotheses in each declaration. |
| Theorem 4.9 | `sum_by_parts`, `redistribution_sum`, `redistribution_nonneg`, `redistribution_zero_iff`, `metric_kernel_strictAnti`, `response_kernel_strictAnti`, `metric_response_common_kernel` | Conserved strength on a finite ordered grid, one polarization at a time. The change is initial minus final. |
| Confined oscillator, §4.10a | `oscillator_metric`, `oscillator_response`, `oscillator_budget`, `oscillator_attains_static_bound`, `oscillator_table` | Algebra of the stated formulas and the exact table; not a formal derivation of the Gaussian ground state or Heisenberg response. |
| Identification and exclusion, §5.2 | `identification_target`, `identification_target_bound`, `oscillator_metric_strictAnti`, `oscillator_index_strictAnti`, `no_common_constant`, `oscillator_excludes_field_derivative` | The stated scalar target and specific oscillator calibration obstruction. |

The general spectral-measure/matrix versions of Theorem 4.9, Corollary 4.10, analytic contour integrals, and the physical interpretation are **not** Lean-certified here. The oscillator identity `α₀³ = 8g²F` does not by itself prove the general upper bound `α₀ ≤ 2(g²F)^{1/3}`. See [LIMITATIONS.md](LIMITATIONS.md).

## Verified public evidence

The public [proof-check run 37550909831](https://github.com/dicipler-pixel/light-ledger-lean/actions/runs/37550909831), for commit `10cb5dacd0fa8ab01dfa705102846a87d2620c02`, completed successfully on 7 October 2026. Its job log records:

> OK: 122 theorems, axioms used: ['Classical.choice', 'Quot.sound', 'propext'], 6 false controls rejected

The build and independent kernel replay also passed. This is an inspected existing run, not a new local compilation. It does not independently verify the older private operator-first workflow runs cited by the manuscript.

## Wording for a subsequent manuscript revision

“The earlier edition archived an older Lean inventory. The companion repository subsequently formalized finite-spectrum and finite-grid counterparts of selected results, including 27 declarations in LightSpectral, bringing its inventory to 122 named theorems. This formal coverage does not extend to the general spectral-measure or matrix-valued results, the full oscillator derivation, or the physical interpretation.”

This repository note is not a publication of edition 7.3. Removing boxed equations and inserting the AI-assisted disclosure above the abstract are manuscript edits, not changes to the Lean proofs.
