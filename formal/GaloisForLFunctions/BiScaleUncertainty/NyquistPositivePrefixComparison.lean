import GaloisForLFunctions.BiScaleUncertainty.NyquistPositiveTailComparison

/-! # Transfer of coefficient ratios to divergent positive prefixes -/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

private theorem prefix_lower {a b : ℕ → ℝ} {c : ℝ} {L M : ℕ}
    (hLM : L ≤ M) (h : ∀ n, L ≤ n → c * b n ≤ a n) :
    c * (∑ n ∈ Finset.range M, b n) +
        ((∑ n ∈ Finset.range L, a n) - c * (∑ n ∈ Finset.range L, b n)) ≤
      ∑ n ∈ Finset.range M, a n := by
  have ha := Finset.sum_range_add a L (M - L)
  have hb := Finset.sum_range_add b L (M - L)
  rw [Nat.add_sub_of_le hLM] at ha hb
  have ht : ∑ n ∈ Finset.range (M - L), c * b (L + n) ≤
      ∑ n ∈ Finset.range (M - L), a (L + n) :=
    Finset.sum_le_sum (fun n _ => h (L + n) (by omega))
  rw [← Finset.mul_sum] at ht
  rw [ha, hb]
  nlinarith

theorem tendsto_nyquist_positive_prefix_ratio {a b : ℕ → ℝ}
    (hbpos : ∀ n, 0 < b n)
    (hB : Tendsto (fun M => ∑ n ∈ Finset.range M, b n) atTop atTop) {c : ℝ}
    (hlim : Tendsto (fun n => a n / b n) atTop (𝓝 c)) :
    Tendsto (fun M => (∑ n ∈ Finset.range M, a n) /
      (∑ n ∈ Finset.range M, b n)) atTop (𝓝 c) := by
  rw [Metric.tendsto_atTop] at hlim ⊢
  intro ε hε
  obtain ⟨L, hL⟩ := hlim (ε / 2) (by linarith)
  let B : ℕ → ℝ := fun M => ∑ n ∈ Finset.range M, b n
  let A : ℕ → ℝ := fun M => ∑ n ∈ Finset.range M, a n
  let CLower : ℝ := A L - (c - ε / 2) * B L
  let CUpper : ℝ := A L - (c + ε / 2) * B L
  have hlow (M : ℕ) (hLM : L ≤ M) : (c - ε / 2) * B M + CLower ≤ A M := by
    apply prefix_lower hLM
    intro n hn
    have hd := hL n hn
    rw [Real.dist_eq] at hd
    apply (le_div_iff₀ (hbpos n)).mp
    linarith [(abs_lt.mp hd).1]
  have hupp (M : ℕ) (hLM : L ≤ M) : A M ≤ (c + ε / 2) * B M + CUpper := by
    have h := prefix_lower (a := fun n => -a n) (b := b)
      (c := -(c + ε / 2)) hLM (fun n hn => ?_)
    · simp only [Finset.sum_neg_distrib] at h
      change -(c + ε / 2) * B M + (-A L - -(c + ε / 2) * B L) ≤ -A M at h
      dsimp [CUpper]
      linarith
    · have hd := hL n hn
      rw [Real.dist_eq] at hd
      have ht : a n / b n ≤ c + ε / 2 := by linarith [(abs_lt.mp hd).2]
      have hm := (div_le_iff₀ (hbpos n)).mp ht
      linarith
  have hlo : Tendsto (fun M => c - ε / 2 + CLower / B M) atTop (𝓝 (c - ε / 2)) := by
    simpa using tendsto_const_nhds.add (hB.const_div_atTop CLower)
  have hup : Tendsto (fun M => c + ε / 2 + CUpper / B M) atTop (𝓝 (c + ε / 2)) := by
    simpa using tendsto_const_nhds.add (hB.const_div_atTop CUpper)
  have hgood : ∀ᶠ M : ℕ in atTop, dist (A M / B M) c < ε := by
    filter_upwards [eventually_ge_atTop L,
      hB.eventually (eventually_gt_atTop 0),
      hlo.eventually_const_lt (by linarith : c - ε < c - ε / 2),
      hup.eventually_lt_const (by linarith : c + ε / 2 < c + ε)] with M hLM hBM hl hu
    have hlow' : c - ε / 2 + CLower / B M ≤ A M / B M := by
      apply (le_div_iff₀ hBM).mpr
      calc
        (c - ε / 2 + CLower / B M) * B M = (c - ε / 2) * B M + CLower := by
          field_simp [show B M ≠ 0 from hBM.ne'] <;> ring
        _ ≤ A M := hlow M hLM
    have hupp' : A M / B M ≤ c + ε / 2 + CUpper / B M := by
      apply (div_le_iff₀ hBM).mpr
      calc
        A M ≤ (c + ε / 2) * B M + CUpper := hupp M hLM
        _ = (c + ε / 2 + CUpper / B M) * B M := by
          field_simp [show B M ≠ 0 from hBM.ne'] <;> ring
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor <;> linarith
  exact eventually_atTop.mp hgood

end
end GaloisForLFunctions.BiScaleUncertainty
