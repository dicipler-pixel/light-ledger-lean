import LightSpectral
-- Dropping the regulator from the identification target: at σ = 0, η = 1 the regularized
-- rigidity is 1 = c r with c r = 1, yet σ² = 0 ≠ 1/(c r) = 1.
example : (0:ℝ) ^ 2 = 1 / (1 * 1) := by norm_num
