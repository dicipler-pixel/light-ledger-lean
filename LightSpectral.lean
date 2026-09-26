import Mathlib
import Rigidity

/-!
# Edition 7.2: spectral bounds, the confined oscillator and the identification target

Finite forms of Sections 4.9e, 4.10a and 5.2 of *The Light Keeps the Ledger*
(Jeromie Beasley, DOI 10.5281/zenodo.22124938).

A dipole-active spectrum is a finite list of excitation gaps `t i ≥ a > 0` with
oscillator weights `w i ≥ 0`. From it:

* field metric `g = Σ w/t²`, oscillator budget `F = Σ t w`, static response
  `α₀ = Σ 2w/t`, subgap response `R(y) = Σ 2tw/(t² − y)` and the two-reading secant
  `B = Σ 2tw/((t² − y₁)(t² − y₂))`.

Proved here (Corollary 4.8 for a finite spectrum, with `0 ≤ y, y₁, y₂ < a²`):
`2 a g ≤ α₀`, `α₀² ≤ 2 F B`, and `α₀ ≤ R(y) ≤ α₀ / (1 − y/a²)`.

For the confined oscillator of Section 4.10a (`Δ = ħΩ`, `w = q²ħ/(2mΩ)`): the spectral
formulas reproduce `g = q²/(2mħΩ³)` and `α(ω) = q²/(m(Ω² − ω²))`, the budget is
`F = q²ħ²/(2m)`, the static bound is attained (`α₀³ = 8 g² F`), and the exact table of
Section 4.10a holds.

For Section 5.2: the scalar identification target `R_η = c r ⇔ σ² = 1/(c r) − η`, and the
exclusion of the field-derivative candidate `σ² = g` in the oscillator realization.

The spectral theorem, infinite spectra and the physical derivations are not formalized;
see `LIMITATIONS.md`.
-/

set_option autoImplicit false
noncomputable section
namespace LightSpectral

open Finset

variable {ι : Type*}

/-! ## Finite spectral data -/

/-- Field metric `g = Σ w/t²`. -/
def metric (s : Finset ι) (t w : ι → ℝ) : ℝ := ∑ i ∈ s, w i / t i ^ 2

/-- Oscillator budget `F = Σ t w`. -/
def budget (s : Finset ι) (t w : ι → ℝ) : ℝ := ∑ i ∈ s, t i * w i

/-- Static response `α₀ = Σ 2w/t`. -/
def static (s : Finset ι) (t w : ι → ℝ) : ℝ := ∑ i ∈ s, 2 * w i / t i

/-- The moment `Σ w/t³`. -/
def moment3 (s : Finset ι) (t w : ι → ℝ) : ℝ := ∑ i ∈ s, w i / t i ^ 3

/-- Subgap response `R(y) = Σ 2tw/(t² − y)`. -/
def response (s : Finset ι) (t w : ι → ℝ) (y : ℝ) : ℝ := ∑ i ∈ s, 2 * t i * w i / (t i ^ 2 - y)

/-- Two-reading secant `B = Σ 2tw/((t² − y₁)(t² − y₂))`. -/
def secant (s : Finset ι) (t w : ι → ℝ) (y₁ y₂ : ℝ) : ℝ :=
  ∑ i ∈ s, 2 * t i * w i / ((t i ^ 2 - y₁) * (t i ^ 2 - y₂))

variable (s : Finset ι) (t w : ι → ℝ) (a : ℝ)

/-- **Corollary 4.8, static lower bound**: `2 a g ≤ α₀`. -/
theorem static_lower (ha : 0 < a) (hta : ∀ i ∈ s, a ≤ t i) (hw : ∀ i ∈ s, 0 ≤ w i) :
    2 * a * metric s t w ≤ static s t w := by
  unfold metric static
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have ht : 0 < t i := lt_of_lt_of_le ha (hta i hi)
  have key : 2 * w i / t i = 2 * a * (w i / t i ^ 2) + 2 * w i * (t i - a) / t i ^ 2 := by
    field_simp <;> ring
  rw [key]
  have : 0 ≤ 2 * w i * (t i - a) / t i ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hw i hi)) (sub_nonneg.mpr (hta i hi)))
      (by positivity)
  linarith

/-- Cauchy–Schwarz: `α₀² ≤ 4 F Σ w/t³`. -/
theorem static_sq_le (ha : 0 < a) (hta : ∀ i ∈ s, a ≤ t i) (hw : ∀ i ∈ s, 0 ≤ w i) :
    static s t w ^ 2 ≤ 4 * budget s t w * moment3 s t w := by
  have hs : static s t w = 2 * ∑ i ∈ s, w i / t i := by
    unfold static
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  have hcs : (∑ i ∈ s, w i / t i) ^ 2 ≤ budget s t w * moment3 s t w := by
    unfold budget moment3
    apply sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro i hi
      exact mul_nonneg (le_trans ha.le (hta i hi)) (hw i hi)
    · intro i hi
      have ht : 0 < t i := lt_of_lt_of_le ha (hta i hi)
      exact div_nonneg (hw i hi) (by positivity)
    · intro i hi
      have ht : 0 < t i := lt_of_lt_of_le ha (hta i hi)
      field_simp <;> ring
  rw [hs]
  nlinarith [hcs]

/-- The secant dominates twice the third inverse moment. -/
theorem moment3_le_secant (y₁ y₂ : ℝ) (ha : 0 < a) (hta : ∀ i ∈ s, a ≤ t i)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (h₁ : y₁ < a ^ 2)
    (h₂ : y₂ < a ^ 2) :
    2 * moment3 s t w ≤ secant s t w y₁ y₂ := by
  unfold moment3 secant
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have ht : 0 < t i := lt_of_lt_of_le ha (hta i hi)
  have hsq : a ^ 2 ≤ t i ^ 2 := by nlinarith [hta i hi]
  have d1 : 0 < t i ^ 2 - y₁ := by linarith
  have d2 : 0 < t i ^ 2 - y₂ := by linarith
  have hD : (t i ^ 2 - y₁) * (t i ^ 2 - y₂) ≤ t i ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right (le_of_lt (lt_of_lt_of_le h₁ hsq)) hy₂,
      mul_nonneg hy₁ (sq_nonneg (t i))]
  have hnum : 0 ≤ 2 * t i * w i := by have := hw i hi; positivity
  calc 2 * (w i / t i ^ 3) = 2 * t i * w i / t i ^ 4 := by field_simp <;> ring
    _ ≤ 2 * t i * w i / ((t i ^ 2 - y₁) * (t i ^ 2 - y₂)) :=
        div_le_div_of_nonneg_left hnum (mul_pos d1 d2) hD

/-- **Corollary 4.8, two-reading bound**: `α₀² ≤ 2 F B`. -/
theorem static_sq_le_budget_secant (y₁ y₂ : ℝ) (ha : 0 < a) (hta : ∀ i ∈ s, a ≤ t i)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (h₁ : y₁ < a ^ 2)
    (h₂ : y₂ < a ^ 2) :
    static s t w ^ 2 ≤ 2 * budget s t w * secant s t w y₁ y₂ := by
  have hF : 0 ≤ budget s t w :=
    sum_nonneg fun i hi => mul_nonneg (le_trans ha.le (hta i hi)) (hw i hi)
  have h1 := static_sq_le s t w a ha hta hw
  have h2 := moment3_le_secant s t w a y₁ y₂ ha hta hw hy₁ hy₂ h₁ h₂
  nlinarith [mul_le_mul_of_nonneg_left h2 hF]

/-- **Corollary 4.8, subgap bracket**: `α₀ ≤ R(y) ≤ α₀ / (1 − y/a²)`. -/
theorem response_bracket (y : ℝ) (ha : 0 < a) (hta : ∀ i ∈ s, a ≤ t i)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hy : 0 ≤ y) (hya : y < a ^ 2) :
    static s t w ≤ response s t w y ∧ response s t w y ≤ static s t w / (1 - y / a ^ 2) := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hq : 0 < 1 - y / a ^ 2 := by
    rw [sub_pos, div_lt_one ha2]
    exact hya
  constructor
  · unfold static response
    apply sum_le_sum
    intro i hi
    have ht : 0 < t i := lt_of_lt_of_le ha (hta i hi)
    have hsq : a ^ 2 ≤ t i ^ 2 := by nlinarith [hta i hi]
    have d : 0 < t i ^ 2 - y := by linarith
    have hnum : 0 ≤ 2 * t i * w i := by have := hw i hi; positivity
    calc 2 * w i / t i = 2 * t i * w i / t i ^ 2 := by field_simp <;> ring
      _ ≤ 2 * t i * w i / (t i ^ 2 - y) :=
          div_le_div_of_nonneg_left hnum d (by linarith)
  · unfold static response
    rw [sum_div]
    apply sum_le_sum
    intro i hi
    have ht : 0 < t i := lt_of_lt_of_le ha (hta i hi)
    have hsq : a ^ 2 ≤ t i ^ 2 := by nlinarith [hta i hi]
    have d : 0 < t i ^ 2 - y := by linarith
    have hwi := hw i hi
    have hay : 0 < a ^ 2 - y := by linarith
    have e : 2 * w i / t i / (1 - y / a ^ 2) = 2 * w i * a ^ 2 / (t i * (a ^ 2 - y)) := by
      field_simp <;> ring
    rw [e, div_le_div_iff₀ d (mul_pos ht hay)]
    nlinarith [mul_nonneg (mul_nonneg hwi hy) (sub_nonneg.mpr hsq)]

/-! ## The confined oscillator (Section 4.10a) -/

/-- The oscillator's single transition reproduces the field metric `q²/(2mħΩ³)`. -/
theorem oscillator_metric (q m ħ Ω : ℝ) (hm : m ≠ 0) (hħ : ħ ≠ 0) (hΩ : Ω ≠ 0) :
    (q ^ 2 * ħ / (2 * m * Ω)) / (ħ * Ω) ^ 2 = q ^ 2 / (2 * m * ħ * Ω ^ 3) := by
  field_simp <;> ring

/-- … and the lossless polarizability `q²/(m(Ω² − ω²))`. -/
theorem oscillator_response (q m ħ Ω ω : ℝ) (hm : m ≠ 0) (hħ : ħ ≠ 0) (hΩ : Ω ≠ 0)
    (hω : Ω ^ 2 - ω ^ 2 ≠ 0) :
    2 * (ħ * Ω) * (q ^ 2 * ħ / (2 * m * Ω)) / ((ħ * Ω) ^ 2 - (ħ * ω) ^ 2) =
      q ^ 2 / (m * (Ω ^ 2 - ω ^ 2)) := by
  have h2 : (ħ * Ω) ^ 2 - (ħ * ω) ^ 2 = ħ ^ 2 * (Ω ^ 2 - ω ^ 2) := by ring
  rw [h2]
  field_simp <;> ring

/-- The oscillator budget is the Thomas–Reiche–Kuhn value `q²ħ²/(2m)`. -/
theorem oscillator_budget (q m ħ Ω : ℝ) (hm : m ≠ 0) (hΩ : Ω ≠ 0) :
    (ħ * Ω) * (q ^ 2 * ħ / (2 * m * Ω)) = q ^ 2 * ħ ^ 2 / (2 * m) := by
  field_simp <;> ring

/-- The static upper bound `α₀ ≤ 2 (g² F)^{1/3}` is attained: `α₀³ = 8 g² F`. -/
theorem oscillator_attains_static_bound (q m ħ Ω : ℝ) (hm : m ≠ 0) (hħ : ħ ≠ 0)
    (hΩ : Ω ≠ 0) :
    (q ^ 2 / (m * Ω ^ 2)) ^ 3 =
      8 * (q ^ 2 / (2 * m * ħ * Ω ^ 3)) ^ 2 * (q ^ 2 * ħ ^ 2 / (2 * m)) := by
  field_simp <;> ring

/-- The exact table of Section 4.10a (`q = m = ħ = 1`, `N/ε₀ = 1/100`, `ω = 1/2`,
`Ω : 1 → 2`): metric, response, secant and squared index before and after. -/
theorem oscillator_table :
    (1 : ℝ) / (2 * 1 ^ 3) = 1 / 2 ∧ (1 : ℝ) / (2 * 2 ^ 3) = 1 / 16 ∧
    (1 : ℝ) / (1 ^ 2 - (1 / 2) ^ 2) = 4 / 3 ∧ (1 : ℝ) / (2 ^ 2 - (1 / 2) ^ 2) = 4 / 15 ∧
    ((1 : ℝ) / (1 ^ 2 - 1 / 4) - 1 / 1 ^ 2) / (1 / 4) = 4 / 3 ∧
    ((1 : ℝ) / (2 ^ 2 - 1 / 4) - 1 / 2 ^ 2) / (1 / 4) = 1 / 15 ∧
    1 + (1 : ℝ) / 100 * (4 / 3) = 76 / 75 ∧ 1 + (1 : ℝ) / 100 * (4 / 15) = 376 / 375 ∧
    ((76 : ℝ) / 75) / (376 / 375) = 95 / 94 ∧
    (1 : ℝ) / 2 - 1 / 16 = 7 / 16 ∧ (4 : ℝ) / 3 - 1 / 15 = 19 / 15 := by
  norm_num

/-! ## The identification target (Section 5.2) -/

/-- **Proposition 5.4a**: `R_η(σ) = c r ⇔ σ² = 1/(c r) − η`. -/
theorem identification_target (σ η c r : ℝ) :
    LightRigidity.regularized σ η = c * r ↔ σ ^ 2 = 1 / (c * r) - η := by
  rw [LightRigidity.regularized, one_div, inv_eq_iff_eq_inv, one_div]
  constructor <;> intro h <;> linarith

/-- The target forces `c η r ≤ 1`. -/
theorem identification_target_bound (σ η c r : ℝ) (hcr : 0 < c * r)
    (h : LightRigidity.regularized σ η = c * r) : c * r * η ≤ 1 := by
  have h1 := (identification_target σ η c r).1 h
  have h2 : η ≤ 1 / (c * r) := by nlinarith [sq_nonneg σ]
  rw [le_div_iff₀ hcr] at h2
  linarith

/-- The oscillator field metric strictly decreases with the confinement. -/
theorem oscillator_metric_strictAnti (q m ħ Ω₁ Ω₂ : ℝ) (hq : q ≠ 0) (hm : 0 < m)
    (hħ : 0 < ħ) (h₁ : 0 < Ω₁) (h₁₂ : Ω₁ < Ω₂) :
    q ^ 2 / (2 * m * ħ * Ω₂ ^ 3) < q ^ 2 / (2 * m * ħ * Ω₁ ^ 3) := by
  have hq2 : 0 < q ^ 2 := lt_of_le_of_ne (sq_nonneg q) (Ne.symm (pow_ne_zero 2 hq))
  have hΩ₂ : 0 < Ω₂ := by linarith
  apply div_lt_div_of_pos_left hq2 (by positivity)
  have h3 : Ω₁ ^ 3 < Ω₂ ^ 3 := by
    have := mul_pos (sub_pos.mpr h₁₂)
      (add_pos (add_pos (pow_pos hΩ₂ 2) (mul_pos hΩ₂ h₁)) (pow_pos h₁ 2))
    nlinarith
  have hc : 0 < 2 * m * ħ := by positivity
  exact mul_lt_mul_of_pos_left h3 hc

/-- The oscillator squared index strictly decreases with the confinement. -/
theorem oscillator_index_strictAnti (C q m Ω₁ Ω₂ ω : ℝ) (hC : 0 < C) (hq : q ≠ 0)
    (hm : 0 < m) (hω : ω ^ 2 < Ω₁ ^ 2) (h₁ : 0 < Ω₁) (h₁₂ : Ω₁ < Ω₂) :
    1 + C * (q ^ 2 / (m * (Ω₂ ^ 2 - ω ^ 2))) < 1 + C * (q ^ 2 / (m * (Ω₁ ^ 2 - ω ^ 2))) := by
  have hq2 : 0 < q ^ 2 := lt_of_le_of_ne (sq_nonneg q) (Ne.symm (pow_ne_zero 2 hq))
  have d1 : 0 < Ω₁ ^ 2 - ω ^ 2 := by linarith
  have hΩ₂ : 0 < Ω₂ := by linarith
  have hsq : Ω₁ ^ 2 < Ω₂ ^ 2 := by nlinarith [mul_pos (sub_pos.mpr h₁₂) (add_pos hΩ₂ h₁)]
  have d2 : 0 < Ω₂ ^ 2 - ω ^ 2 := by linarith
  have hlt : q ^ 2 / (m * (Ω₂ ^ 2 - ω ^ 2)) < q ^ 2 / (m * (Ω₁ ^ 2 - ω ^ 2)) := by
    apply div_lt_div_of_pos_left hq2 (mul_pos hm d1)
    nlinarith [mul_pos hm (sub_pos.mpr hsq)]
  linarith [mul_lt_mul_of_pos_left hlt hC]

/-- Two strictly ordered positive products cannot share one calibration constant. -/
theorem no_common_constant (g₁ g₂ r₁ r₂ η c : ℝ) (hg : g₂ < g₁) (hr : r₂ < r₁)
    (hg₂ : 0 ≤ g₂) (hr₂ : 0 < r₂) (hη : 0 < η)
    (e₁ : 1 / (g₁ + η) = c * r₁) (e₂ : 1 / (g₂ + η) = c * r₂) : False := by
  have p1 : 0 < g₁ + η := by linarith
  have p2 : 0 < g₂ + η := by linarith
  have k1 := (div_eq_iff p1.ne').1 e₁
  have k2 := (div_eq_iff p2.ne').1 e₂
  have hlt : (g₂ + η) * r₂ < (g₁ + η) * r₁ :=
    mul_lt_mul'' (by linarith) hr (by linarith) hr₂.le
  have hc : c ≠ 0 := by
    rintro rfl
    simp at k1
  have heq : c * ((g₁ + η) * r₁) = c * ((g₂ + η) * r₂) := by linear_combination k2 - k1
  exact (ne_of_lt hlt) (mul_left_cancel₀ hc heq).symm

/-- **Section 5.2 exclusion**: in the oscillator realization, no single constant `c`
identifies the regularized field-derivative rigidity `1/(g + η)` with `c r` at two distinct
confinements. -/
theorem oscillator_excludes_field_derivative (C q m ħ Ω₁ Ω₂ ω η c : ℝ) (hC : 0 < C)
    (hq : q ≠ 0) (hm : 0 < m) (hħ : 0 < ħ) (hη : 0 < η) (hω : ω ^ 2 < Ω₁ ^ 2)
    (h₁ : 0 < Ω₁) (h₁₂ : Ω₁ < Ω₂)
    (e₁ : 1 / (q ^ 2 / (2 * m * ħ * Ω₁ ^ 3) + η) =
      c * (1 + C * (q ^ 2 / (m * (Ω₁ ^ 2 - ω ^ 2)))))
    (e₂ : 1 / (q ^ 2 / (2 * m * ħ * Ω₂ ^ 3) + η) =
      c * (1 + C * (q ^ 2 / (m * (Ω₂ ^ 2 - ω ^ 2))))) : False := by
  have hΩ₂ : 0 < Ω₂ := by linarith
  have d : 0 < Ω₂ ^ 2 - ω ^ 2 := by nlinarith [mul_pos (sub_pos.mpr h₁₂) (add_pos hΩ₂ h₁)]
  have hr₂ : 0 < 1 + C * (q ^ 2 / (m * (Ω₂ ^ 2 - ω ^ 2))) := by
    have := mul_nonneg hC.le (div_nonneg (sq_nonneg q) (mul_nonneg hm.le d.le))
    linarith
  exact no_common_constant _ _ _ _ η c
    (oscillator_metric_strictAnti q m ħ Ω₁ Ω₂ hq hm hħ h₁ h₁₂)
    (oscillator_index_strictAnti C q m Ω₁ Ω₂ ω hC hq hm hω h₁ h₁₂)
    (div_nonneg (sq_nonneg q) (by positivity)) hr₂ hη e₁ e₂

end LightSpectral
