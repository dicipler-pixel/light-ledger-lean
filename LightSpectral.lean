import Mathlib
import Rigidity

/-!
# Edition 7.2: spectral bounds, the confined oscillator and the identification target

Finite forms of Sections 4.9e, 4.10a and 5.2 of *The Light Keeps the Ledger*
(Jeromie Beasley, DOI 10.5281/zenodo.22123115).

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


/-! ## Corollary 4.7: the lower bound from two readings -/

/-- The kernel ratio `β(t) = 2t³/((t² − y₁)(t² − y₂))`. -/
def kernelRatio (y₁ y₂ t : ℝ) : ℝ := 2 * t ^ 3 / ((t ^ 2 - y₁) * (t ^ 2 - y₂))

/-- `β` falls as the gap grows: for `a ≤ t` and subgap readings, `β(t) ≤ β(a)`. -/
theorem kernelRatio_antitone (y₁ y₂ a t : ℝ) (ha : 0 < a) (hat : a ≤ t) (hy₁ : 0 ≤ y₁)
    (hy₂ : 0 ≤ y₂) (h₁ : y₁ < a ^ 2) (h₂ : y₂ < a ^ 2) :
    kernelRatio y₁ y₂ t ≤ kernelRatio y₁ y₂ a := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  have hsq : a ^ 2 ≤ t ^ 2 := by nlinarith
  have form : ∀ x : ℝ, 0 < x → x ^ 2 - y₁ ≠ 0 → x ^ 2 - y₂ ≠ 0 →
      kernelRatio y₁ y₂ x = 2 / ((x - y₁ / x) * (1 - y₂ / x ^ 2)) := by
    intro x hx d1 d2
    unfold kernelRatio
    have hx0 : x ≠ 0 := hx.ne'
    rw [show x - y₁ / x = (x ^ 2 - y₁) / x by field_simp <;> ring,
      show 1 - y₂ / x ^ 2 = (x ^ 2 - y₂) / x ^ 2 by field_simp <;> ring]
    field_simp <;> ring
  have da1 : 0 < a ^ 2 - y₁ := by linarith
  have da2 : 0 < a ^ 2 - y₂ := by linarith
  rw [form t ht (by linarith) (by linarith), form a ha da1.ne' da2.ne']
  have p1 : 0 < a - y₁ / a := by
    rw [show a - y₁ / a = (a ^ 2 - y₁) / a by field_simp <;> ring]
    exact div_pos da1 ha
  have p2 : 0 < 1 - y₂ / a ^ 2 := by
    rw [show 1 - y₂ / a ^ 2 = (a ^ 2 - y₂) / a ^ 2 by field_simp <;> ring]
    exact div_pos da2 (by positivity)
  have q1 : a - y₁ / a ≤ t - y₁ / t := by
    have : y₁ / t ≤ y₁ / a := div_le_div_of_nonneg_left hy₁ ha hat
    linarith
  have q2 : 1 - y₂ / a ^ 2 ≤ 1 - y₂ / t ^ 2 := by
    have : y₂ / t ^ 2 ≤ y₂ / a ^ 2 := div_le_div_of_nonneg_left hy₂ (by positivity) hsq
    linarith
  have hprod : (a - y₁ / a) * (1 - y₂ / a ^ 2) ≤ (t - y₁ / t) * (1 - y₂ / t ^ 2) :=
    mul_le_mul q1 q2 p2.le (le_trans p1.le q1)
  exact div_le_div_of_nonneg_left (by norm_num) (mul_pos p1 p2) hprod

theorem kernelRatio_pos (y₁ y₂ a : ℝ) (ha : 0 < a) (h₁ : y₁ < a ^ 2) (h₂ : y₂ < a ^ 2) :
    0 < kernelRatio y₁ y₂ a := by
  unfold kernelRatio
  have d1 : 0 < a ^ 2 - y₁ := by linarith
  have d2 : 0 < a ^ 2 - y₂ := by linarith
  exact div_pos (by positivity) (mul_pos d1 d2)

/-- **Corollary 4.7, lower bound**: `B ≤ β(a) g`, i.e. `B / β(a) ≤ g`. -/
theorem secant_le_kernelRatio_metric (y₁ y₂ : ℝ) (ha : 0 < a) (hta : ∀ i ∈ s, a ≤ t i)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (h₁ : y₁ < a ^ 2)
    (h₂ : y₂ < a ^ 2) :
    secant s t w y₁ y₂ ≤ kernelRatio y₁ y₂ a * metric s t w := by
  unfold secant metric
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have ht : 0 < t i := lt_of_lt_of_le ha (hta i hi)
  have hsq : a ^ 2 ≤ t i ^ 2 := by nlinarith [hta i hi]
  have d1 : t i ^ 2 - y₁ ≠ 0 := by
    have : 0 < t i ^ 2 - y₁ := by linarith
    exact this.ne'
  have d2 : t i ^ 2 - y₂ ≠ 0 := by
    have : 0 < t i ^ 2 - y₂ := by linarith
    exact this.ne'
  have split : 2 * t i * w i / ((t i ^ 2 - y₁) * (t i ^ 2 - y₂)) =
      kernelRatio y₁ y₂ (t i) * (w i / t i ^ 2) := by
    unfold kernelRatio
    field_simp <;> ring
  rw [split]
  exact mul_le_mul_of_nonneg_right
    (kernelRatio_antitone y₁ y₂ a (t i) ha (hta i hi) hy₁ hy₂ h₁ h₂)
    (div_nonneg (hw i hi) (by positivity))

theorem secant_div_le_metric (y₁ y₂ : ℝ) (ha : 0 < a) (hta : ∀ i ∈ s, a ≤ t i)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (h₁ : y₁ < a ^ 2)
    (h₂ : y₂ < a ^ 2) :
    secant s t w y₁ y₂ / kernelRatio y₁ y₂ a ≤ metric s t w := by
  rw [div_le_iff₀ (kernelRatio_pos y₁ y₂ a ha h₁ h₂), mul_comm]
  exact secant_le_kernelRatio_metric s t w a y₁ y₂ ha hta hw hy₁ hy₂ h₁ h₂


/-! ## Theorem 4.9: conserved strength and upward redistribution (finite form)

Oscillator strength sits on an increasing grid of gaps `t 0 < t 1 < … < t n`. The change
between two stages is `d k = m₀ k − m₁ k`; its cumulative sum `S j = Σ_{k ≤ j} d k` is
nonnegative (no low-energy interval gains strength) and vanishes at the top (the total is
conserved). -/

/-- Cumulative change `S j = Σ_{k ≤ j} d k`. -/
def cumulative (d : ℕ → ℝ) (j : ℕ) : ℝ := ∑ k ∈ range (j + 1), d k

/-- Summation by parts. -/
theorem sum_by_parts (F d : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ range (n + 1), F k * d k =
      ∑ j ∈ range n, (F j - F (j + 1)) * cumulative d j + F n * cumulative d n := by
  induction n with
  | zero => simp [cumulative]
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun j => (F j - F (j + 1)) * cumulative d j)]
    have h : cumulative d (n + 1) = cumulative d n + d (n + 1) := by
      simp only [cumulative]
      rw [sum_range_succ]
    rw [h]
    ring

/-- With the total conserved, a kernel reads the change through the cumulative order. -/
theorem redistribution_sum (F d : ℕ → ℝ) (n : ℕ) (htot : cumulative d n = 0) :
    ∑ k ∈ range (n + 1), F k * d k = ∑ j ∈ range n, (F j - F (j + 1)) * cumulative d j := by
  rw [sum_by_parts, htot, mul_zero, add_zero]

/-- **Theorem 4.9, order.** A decreasing kernel sees a nonnegative change. -/
theorem redistribution_nonneg (F d : ℕ → ℝ) (n : ℕ) (hF : ∀ j < n, F (j + 1) < F j)
    (hS : ∀ j < n, 0 ≤ cumulative d j) (htot : cumulative d n = 0) :
    0 ≤ ∑ k ∈ range (n + 1), F k * d k := by
  rw [redistribution_sum F d n htot]
  exact sum_nonneg fun j hj =>
    mul_nonneg (sub_nonneg.mpr (hF j (mem_range.mp hj)).le) (hS j (mem_range.mp hj))

/-- **Theorem 4.9, kernel.** A strictly decreasing kernel sees no change exactly when no
cumulative change occurs anywhere. -/
theorem redistribution_zero_iff (F d : ℕ → ℝ) (n : ℕ) (hF : ∀ j < n, F (j + 1) < F j)
    (hS : ∀ j < n, 0 ≤ cumulative d j) (htot : cumulative d n = 0) :
    ∑ k ∈ range (n + 1), F k * d k = 0 ↔ ∀ j < n, cumulative d j = 0 := by
  rw [redistribution_sum F d n htot, sum_eq_zero_iff_of_nonneg fun j hj =>
    mul_nonneg (sub_nonneg.mpr (hF j (mem_range.mp hj)).le) (hS j (mem_range.mp hj))]
  constructor
  · intro h j hj
    rcases mul_eq_zero.mp (h j (mem_range.mpr hj)) with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) (ne_of_gt (hF j hj))
    · exact h1
  · intro h j hj
    rw [h j (mem_range.mp hj), mul_zero]

/-- The metric kernel `t⁻³` falls along an increasing positive grid. -/
theorem metric_kernel_strictAnti (t : ℕ → ℝ) (ht : StrictMono t) (h0 : 0 < t 0) (j : ℕ) :
    1 / t (j + 1) ^ 3 < 1 / t j ^ 3 := by
  have hj : 0 < t j := lt_of_lt_of_le h0 (ht.monotone (Nat.zero_le j))
  have hlt : t j < t (j + 1) := ht (Nat.lt_succ_self j)
  apply one_div_lt_one_div_of_lt (by positivity)
  exact pow_lt_pow_left₀ hlt hj.le (by norm_num)

/-- The response kernel `2/(t² − y)` falls along the grid for a subgap reading `y < t₀²`. -/
theorem response_kernel_strictAnti (t : ℕ → ℝ) (ht : StrictMono t) (h0 : 0 < t 0) (y : ℝ)
    (hy : y < t 0 ^ 2) (j : ℕ) :
    2 / (t (j + 1) ^ 2 - y) < 2 / (t j ^ 2 - y) := by
  have hj : 0 < t j := lt_of_lt_of_le h0 (ht.monotone (Nat.zero_le j))
  have hmono : t 0 ≤ t j := ht.monotone (Nat.zero_le j)
  have hlt : t j < t (j + 1) := ht (Nat.lt_succ_self j)
  have hsq0 : t 0 ^ 2 ≤ t j ^ 2 := by nlinarith
  have hsq : t j ^ 2 < t (j + 1) ^ 2 := by nlinarith
  exact div_lt_div_of_pos_left (by norm_num) (by linarith) (by linarith)

/-- **Theorem 4.9, common kernel (finite form).** Under upward redistribution with conserved
total, the metric change `L = Σ t⁻³ d` vanishes exactly when the response change
`T(y) = Σ 2/(t² − y) d` does, and both vanish exactly when the cumulative change vanishes. -/
theorem metric_response_common_kernel (t d : ℕ → ℝ) (n : ℕ) (ht : StrictMono t)
    (h0 : 0 < t 0) (y : ℝ) (hy : y < t 0 ^ 2) (hS : ∀ j < n, 0 ≤ cumulative d j)
    (htot : cumulative d n = 0) :
    (∑ k ∈ range (n + 1), 1 / t k ^ 3 * d k = 0 ↔ ∀ j < n, cumulative d j = 0) ∧
    (∑ k ∈ range (n + 1), 2 / (t k ^ 2 - y) * d k = 0 ↔ ∀ j < n, cumulative d j = 0) :=
  ⟨redistribution_zero_iff (fun k => 1 / t k ^ 3) d n
      (fun j _ => metric_kernel_strictAnti t ht h0 j) hS htot,
    redistribution_zero_iff (fun k => 2 / (t k ^ 2 - y)) d n
      (fun j _ => response_kernel_strictAnti t ht h0 y hy j) hS htot⟩

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
