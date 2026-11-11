import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheCorrectedPolynomialJetsConverge
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform parameter bounds for corrected polynomial jets

Compact uniform Möbius-profile bounds control every retained harmonic
row. Summing the Cauchy coefficient bounds against the absolute pair
mass controls all corrected jets on a compact shift interval. The exact
derivative recurrence then gives one Lipschitz constant in the coupled
parameter, independent of the cutoff.
-/

open Filter Polynomial Set Topology

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- One row bound works for all compact shifts, retained dilations, and logarithmic powers. -/
theorem exists_uniform_coupledPolynomialRow_bound (P Q : ℝ[X])
    (hP : P.eval 0 = 0) (hQ : Q.eval 0 = 0) {V : ℝ} (hV : 0 ≤ V) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop, ∀ v ∈ Icc (-V) V, ∀ a b k : ℕ,
      0 < a → 0 < b → a ≤ N → b ≤ N →
      |shiftedProfileHarmonicRow P.eval Q.eval N a b (-2 * v) v k| ≤ B := by
  obtain ⟨B, hB, hPB⟩ := (normalizedShiftedMobiusProfile_compact_uniform P.hasDerivAt
    P.derivative.hasDerivAt P.derivative.derivative.continuous hP hV).1
  obtain ⟨D, hD, hQD⟩ := (normalizedShiftedMobiusProfile_compact_uniform Q.hasDerivAt
    Q.derivative.hasDerivAt Q.derivative.derivative.continuous hQ hV).1
  have hmass : ∀ᶠ N : ℕ in atTop, normalizedHarmonicLogMoment 0 1 N ≤ 2 := by
    have hh := (tendsto_normalizedHarmonicLogMoment 0 (by omega : 0 < 1)).eventually_lt_const
      (show (1 : ℝ) / ((0 : ℕ) + 1) < 2 by norm_num)
    exact hh.mono (fun _ h => h.le)
  refine ⟨Real.exp (2 * V) * (B * D * 2), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 2, hmass] with N hN hm
  intro v hv a b k ha hb haN hbN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hrow := abs_shiftedProfileHarmonicRow_coupled_le k (by omega : 1 < N)
    ha hb haN hbN hV hv hB hD
    (fun u hu => hPB _ hlog u hu _ hv) (fun u hu => hQD _ hlog u hu _ hv)
  exact hrow.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hm (mul_nonneg hB hD)) (Real.exp_nonneg _))

/-- Every corrected jet has a common compact-shift envelope with the Cauchy factorial. -/
theorem exists_uniform_correctedProfileJetSum_bound (P Q : ℝ[X])
    (hP : P.eval 0 = 0) (hQ : Q.eval 0 = 0) {V : ℝ} (hV : 0 ≤ V) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop, ∀ v ∈ Icc (-V) V, ∀ k j : ℕ,
      |correctedProfileJetSum P.eval Q.eval N (-2 * v) v k j| ≤
        B * (j.factorial : ℝ) * Real.exp (4 * (2 * V + 1)) := by
  obtain ⟨B, hB, hrows⟩ := exists_uniform_coupledPolynomialRow_bound P Q hP hQ hV
  let A : ℝ := ∑' x : ℕ × ℕ, absoluteSelbergCorrectionCoeff x.1 x.2
  have hA : 0 ≤ A := tsum_nonneg (fun x => absoluteSelbergCorrectionCoeff_nonneg x.1 x.2)
  have hsum (N : ℕ) : (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
      absoluteSelbergCorrectionCoeff a b) ≤ A := by
    have hh := summable_absoluteSelbergCorrectionCoeff.sum_le_tsum
      ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N))
      (fun x _ => absoluteSelbergCorrectionCoeff_nonneg x.1 x.2)
    simpa only [Finset.sum_product, A] using hh
  refine ⟨B * A, mul_nonneg hB hA, ?_⟩
  filter_upwards [eventually_ge_atTop 2, hrows] with N hN hrow
  intro v hv k j
  let E : ℝ := (j.factorial : ℝ) * Real.exp (4 * (2 * V + 1))
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hcentre : |-2 * v| ≤ 2 * V := by
    rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr hv) (by norm_num)
  have hterm (a : ℕ) (ha : a ∈ Finset.Icc 1 N) (b : ℕ) (hb : b ∈ Finset.Icc 1 N) :
      |realNormalizedCorrectionCoeffJet N a b j (-2 * v) *
        shiftedProfileHarmonicRow P.eval Q.eval N a b (-2 * v) v k| ≤
          B * E * absoluteSelbergCorrectionCoeff a b := by
    have ha' := Finset.mem_Icc.mp ha
    have hb' := Finset.mem_Icc.mp hb
    have hc : |realNormalizedCorrectionCoeffJet N a b j (-2 * v)| ≤
        E * absoluteSelbergCorrectionCoeff a b := by
      refine (abs_realNormalizedCorrectionCoeffJet_le (by omega : 1 < N) (-2 * v) j ha'.2 hb'.2).trans ?_
      apply mul_le_mul_of_nonneg_right _ (absoluteSelbergCorrectionCoeff_nonneg _ _)
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Real.exp_le_exp.mpr
      linarith only [hcentre]
    rw [abs_mul]
    have hh := mul_le_mul hc (hrow v hv a b k ha'.1 hb'.1 ha'.2 hb'.2)
      (abs_nonneg _) (mul_nonneg hE (absoluteSelbergCorrectionCoeff_nonneg _ _))
    exact hh.trans_eq (by ring)
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        |realNormalizedCorrectionCoeffJet N a b j (-2 * v) *
          shiftedProfileHarmonicRow P.eval Q.eval N a b (-2 * v) v k| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        B * E * absoluteSelbergCorrectionCoeff a b :=
      Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hterm a ha b hb
    _ = B * E * (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        absoluteSelbergCorrectionCoeff a b) := by simp only [Finset.mul_sum]
    _ ≤ B * E * A := mul_le_mul_of_nonneg_left (hsum N) (mul_nonneg hB hE)
    _ = _ := by dsimp only [E]; ring

private theorem abs_four_derivative_terms_le (a b c d : ℝ) :
    |(-2) * a + (-2) * b + c + d| ≤ 2 * |a| + 2 * |b| + |c| + |d| := by
  calc
    _ ≤ |(-2) * a + (-2) * b + c| + |d| := abs_add_le _ _
    _ ≤ (|(-2) * a + (-2) * b| + |c|) + |d| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ ((|(-2) * a| + |(-2) * b|) + |c|) + |d| :=
      add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
    _ = _ := by norm_num [abs_mul]

/-- Corrected jets are eventually Lipschitz in the coupled parameter on every compact interval. -/
theorem exists_uniform_correctedProfileJetSum_lipschitz (P Q : ℝ[X])
    (hP : P.eval 0 = 0) (hQ : Q.eval 0 = 0) {V : ℝ} (hV : 0 ≤ V) (k j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop, ∀ x ∈ Icc (-V) V, ∀ y ∈ Icc (-V) V,
      |correctedProfileJetSum P.eval Q.eval N (-2 * x) x k j -
        correctedProfileJetSum P.eval Q.eval N (-2 * y) y k j| ≤ K * |x - y| := by
  obtain ⟨B, hB, hb⟩ := exists_uniform_correctedProfileJetSum_bound P Q hP hQ hV
  obtain ⟨D, hD, hd⟩ := exists_uniform_correctedProfileJetSum_bound (complementPolynomial P) Q
    (complementPolynomial_eval_zero P hP) hQ hV
  obtain ⟨E, hE, he⟩ := exists_uniform_correctedProfileJetSum_bound P (complementPolynomial Q)
    hP (complementPolynomial_eval_zero Q hQ) hV
  let K : ℝ := (2 * B * ((j + 1).factorial : ℝ) +
    2 * B * (j.factorial : ℝ) + D * (j.factorial : ℝ) + E * (j.factorial : ℝ)) *
      Real.exp (4 * (2 * V + 1))
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  filter_upwards [hb, hd, he] with N hbN hdN heN
  have hdiff (v : ℝ) : HasDerivAt
      (fun u => correctedProfileJetSum P.eval Q.eval N (-2 * u) u k j)
      ((-2) * correctedProfileJetSum P.eval Q.eval N (-2 * v) v k (j + 1) +
        (-2) * correctedProfileJetSum P.eval Q.eval N (-2 * v) v (k + 1) j +
        correctedProfileJetSum (logComplementProfile P.eval) Q.eval N (-2 * v) v k j +
        correctedProfileJetSum P.eval (logComplementProfile Q.eval) N (-2 * v) v k j) v := by
    simpa only [zero_add, one_mul] using
      hasDerivAt_correctedProfileJetSum_direction P.eval Q.eval N k j 0 0 (-2) 1 v
  have hbound (v : ℝ) (hv : v ∈ Icc (-V) V) :
      ‖deriv (fun u => correctedProfileJetSum P.eval Q.eval N (-2 * u) u k j) v‖ ≤ K := by
    have h0 := hbN v hv k (j + 1)
    have h1 := hbN v hv (k + 1) j
    have h2 := hdN v hv k j
    have h3 := heN v hv k j
    rw [complementPolynomial_eval] at h2 h3
    rw [(hdiff v).deriv, Real.norm_eq_abs]
    refine (abs_four_derivative_terms_le _ _ _ _).trans ?_
    dsimp only [K]
    linarith only [h0, h1, h2, h3]
  intro x hx y hy
  have hh := (convex_Icc (-V) V).norm_image_sub_le_of_norm_deriv_le
    (fun v _ => (hdiff v).differentiableAt) hbound hy hx
  simpa only [Real.norm_eq_abs] using hh

end GaloisForLFunctions.MultiscaleMollifiedZetaField
