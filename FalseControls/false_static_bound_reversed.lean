import LightSpectral
-- One level at gap 2 with weight 1 above the floor a = 1: α₀ = 2·1/2 = 1 but 2 a g = 1/2.
-- The static response is bounded BELOW by 2 a g, not above.
example : (2:ℝ) * 1 / 2 ≤ 2 * 1 * (1 / 2 ^ 2) := by norm_num
