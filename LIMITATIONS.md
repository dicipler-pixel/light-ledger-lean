# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

The declarations do not formalize spectral differentiation, density-matrix dynamics, Maxwell
boundary conditions, homogenization, analytic contour integrals, entropy functional calculus,
continuum optical capacity, Kakeya or local smoothing, or a physical transport-to-permittivity
identification.

* The census is formalized as scalar and count algebra plus a projector-block identity; the full
  singular-value spectral mapping remains a written argument.
* Rigidity starts from a specified scalar singular value; it does not construct the
  singular-value operator or identify rigidity with `n²`.
* The calibration obstruction in `LightCompletion` assumes that the squared transport singular
  value equals the field metric, a fixed positive regularizer, and optical coefficient `1 + k g`
  with `k > 0`. It excludes that particular identification only.
* Edition 7.2 (`LightSpectral`): the bounds of Corollary 4.8 are proved for a finite spectrum
  (finitely many gaps with nonnegative weights), not for a general spectral measure; the
  spectral theorem, the perturbative derivation of the integrals (4.M2), and the matrix-valued, continuous-measure form of Theorem 4.9 and Corollary 4.10 are not
  formalized; Theorem 4.9 is proved for strength on a finite grid of gaps, one polarization at
  a time. For the oscillator, the Gaussian ground state and the Heisenberg-equation
  response are not formalized; the Lean file checks that the stated formulas agree with each
  other and gives the exact table.

Formalization is evidence for the mathematics, not for the physical interpretation.
