# Provenance

Every Lean file is a byte-identical copy of a verified source in the private
`operator-first` repository.

| Files | Source | Verified at |
| :--- | :--- | :--- |
| `LightBridges.lean`, `LightBridges/*.lean`, `Rigidity.lean`, `LightCompletion.lean` | PR #7, "Light ledger: verify 82 supplement theorems and add 9 finite completion steps" | commit `41d9523a53ad`, Actions run 34015381110 |
| `OpticalMetric.lean` | PR #11, `proofs/peel_constitutive/OpticalMetric.lean`: the original 12 declarations plus 4 peel results | commit `4675da5baf7c` |
| `FalseControls/*.lean` | PR #7, `verification/light/false_*.lean` | commit `41d9523a53ad` |
| `LightSpectral.lean`, `FalseControls/false_static_bound_reversed.lean`, `FalseControls/false_target_without_regulator.lean` | Written for this repository from Edition 7.2 (Sections 4.9e, 4.10a and 5.2, package `Light_Research_Edition_7_2_Proofs_and_Code`) | checked on every push |

The same PR #7 sources are archived, with matching hashes, in the Edition 7.2 package
`Light_Research_Edition_7_2_Proofs_and_Code` (`archive/original_supplement/`), and the PR #11
file in its `archive/peel_archived/`. The SHA-256 of every checked file is written to
`verification/report.json` on each run.
