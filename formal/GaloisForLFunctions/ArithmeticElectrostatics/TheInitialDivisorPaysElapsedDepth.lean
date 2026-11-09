import GaloisForLFunctions.ArithmeticElectrostatics.ThePolynomialHeatDivisorPaysElapsedDepth
import GaloisForLFunctions.ArithmeticElectrostatics.TheHeatDivisorPaysElapsedDepth
import GaloisForLFunctions.RHTower.DeBruijnNewmanEnergyTransition

/-!
# The initial divisor pays every surviving heat pair

For every positive depth exponent, the elapsed moment of the Riemann heat
divisor is bounded by its initial multiplicity-exact depth sum. The initial
sum takes values in `ENNReal`; no summability input is assumed.

Continuous minorants vanishing on the real axis transfer the polynomial
inequality through locally uniform convergence. A short initial heat step
lies below the Gaussian growth horizon; positive-time monotonicity reaches
every later time. Reflection identifies the full and upper-half budgets.
-/

open Polynomial Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.ArithmeticElectrostatics
noncomputable section

/-- Canonical polynomial approximants retain the exact initial multiplicity copies. -/
theorem sum_root_depth_powers_xiRealApprox (n : ℕ) (q : ℝ) :
    (((xiRealApprox n).map ofRealHom).roots.map (fun z => (z.im ^ 2) ^ q)).sum =
      ∑ ρ ∈ xiPairedCopyFinset (xiConjClosedFinset n), ((xiSpectralPoint ρ).im ^ 2) ^ q := by
  rw [map_xiRealApprox, roots_C_mul _ XiC_zero_ne_zero, roots_xiZeroPoly,
    Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

/-- Polynomial budgets pass to the heat divisor below the convergence horizon. -/
theorem heat_elapsed_moment_le_initial_bound_small {q t K : ℝ}
    (hq : 0 < q) (ht : 0 < t) (htS : 8 * xiApproxGrowth * t < 1)
    (hK : ∀ T : Finset XiZeroCopy, ∑ ρ ∈ T, ((xiSpectralPoint ρ).im ^ 2) ^ q ≤ K) :
    heatElapsedDepthMoment q t ≤ K := by
  classical
  let S := (riemannHeat_nonreal_zeros_finite ht).toFinset
  have hS (z : ℂ) (hz : z ∈ S) : z.im ≠ 0 :=
    ((Set.Finite.mem_toFinset _).mp hz).2
  obtain ⟨Ψ, hΨ, hΨ0, hΨreal, hΨle, hΨeq⟩ := exists_elapsedDepth_cutoff S hS
    hq.le (mul_nonneg zero_le_two ht.le)
  have hpoly (n : ℕ) :
      ((((polyHeat t (xiRealApprox n)).map ofRealHom).roots).map Ψ).sum ≤ K := by
    have h := (sum_roots_real_vanishing_weight_le_elapsedMoment
      (xiRealApprox n) q t Ψ hΨreal hΨle).trans
        (polynomial_elapsed_moment_le_initial (xiRealApprox_ne_zero n) hq ht.le)
    rw [sum_root_depth_powers_xiRealApprox] at h
    exact h.trans (hK _)
  have h := sum_zeroMult_mul_le_of_tendstoLocallyUniformly
    (differentiable_riemannHeat ht.le) ⟨0, RHTower.DeBruijn.riemannHeat_zero_ne ht.le⟩ S
    (tendstoLocallyUniformly_polyHeat_xiRealApprox ht htS)
    hΨ hΨ0 (Filter.Eventually.of_forall hpoly)
  have heq : (∑ z ∈ S, (zeroMult (riemannHeat t) z : ℝ) * Ψ z) =
      heatElapsedDepthMoment q t := by
    rw [heatElapsedDepthMoment_eq_sum q ht]
    apply Finset.sum_congr rfl
    intro z hz
    rw [hΨeq z hz]
  rwa [heq] at h

/-- A bound on every finite initial packet controls every positive heat time. -/
theorem heat_elapsed_moment_le_initial_bound {q t K : ℝ}
    (hq : 0 < q) (ht : 0 < t)
    (hK : ∀ T : Finset XiZeroCopy, ∑ ρ ∈ T, ((xiSpectralPoint ρ).im ^ 2) ^ q ≤ K) :
    heatElapsedDepthMoment q t ≤ K := by
  let a := min t (1 / (16 * (xiApproxGrowth + 1)))
  have hS := xiApproxGrowth_nonneg
  have ha : 0 < a := lt_min ht (by positivity)
  have hat : a ≤ t := min_le_left _ _
  have hsmall : 8 * xiApproxGrowth * a < 1 := by
    calc
      8 * xiApproxGrowth * a ≤
          8 * xiApproxGrowth * (1 / (16 * (xiApproxGrowth + 1))) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (mul_nonneg (by norm_num) hS)
      _ < 1 := by
        rw [← mul_div_assoc, mul_one, div_lt_iff₀ (by positivity)]
        nlinarith only [hS]
  exact (antitoneOn_heatElapsedDepthMoment hq.le ha ht hat).trans
    (heat_elapsed_moment_le_initial_bound_small hq ha hsmall hK)

/-- The full initial depth moment, allowing infinite mass. -/
def initialDepthMoment (q : ℝ) : ENNReal :=
  ∑' ρ : XiZeroCopy, ENNReal.ofReal (((xiSpectralPoint ρ).im ^ 2) ^ q)

/-- Every positive elapsed-depth moment is paid by the initial divisor. -/
theorem heat_elapsed_moment_le_initial {q t : ℝ} (hq : 0 < q) (ht : 0 < t) :
    ENNReal.ofReal (heatElapsedDepthMoment q t) ≤ initialDepthMoment q := by
  by_cases htop : initialDepthMoment q = ⊤
  · rw [htop]
    exact le_top
  have hK (T : Finset XiZeroCopy) :
      (∑ ρ ∈ T, ((xiSpectralPoint ρ).im ^ 2) ^ q) ≤ (initialDepthMoment q).toReal := by
    have hnonneg (ρ : XiZeroCopy) : 0 ≤ ((xiSpectralPoint ρ).im ^ 2) ^ q :=
      Real.rpow_nonneg (sq_nonneg _) q
    have hsum : ENNReal.ofReal (∑ ρ ∈ T, ((xiSpectralPoint ρ).im ^ 2) ^ q) ≤
        initialDepthMoment q := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun ρ _ => hnonneg ρ)]
      exact ENNReal.sum_le_tsum T
    have h := ENNReal.toReal_mono htop hsum
    rwa [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun ρ _ => hnonneg ρ))] at h
  calc
    ENNReal.ofReal (heatElapsedDepthMoment q t) ≤
        ENNReal.ofReal (initialDepthMoment q).toReal :=
      ENNReal.ofReal_le_ofReal (heat_elapsed_moment_le_initial_bound hq ht hK)
    _ = initialDepthMoment q := ENNReal.ofReal_toReal htop

/-- Each surviving nonreal multiplicity copy consumes at least `(2t)^q`. -/
theorem nonrealCount_elapsed_power_le_initial {q t : ℝ} (hq : 0 < q) (ht : 0 < t) :
    ENNReal.ofReal ((2 * t) ^ q * (nonrealZeroCount t : ℝ)) ≤ initialDepthMoment q := by
  have h : (2 * t) ^ q * (nonrealZeroCount t : ℝ) ≤ heatElapsedDepthMoment q t :=
    le_add_of_nonneg_left (heatElapsedDepthAction_nonneg hq.le ht.le)
  exact (ENNReal.ofReal_le_ofReal h).trans (heat_elapsed_moment_le_initial hq ht)

/-- The initial upper-half depth moment, with exact analytic multiplicities. -/
def initialUpperDepthMoment (q : ℝ) : ENNReal :=
  ∑' ρ : XiZeroCopy, ENNReal.ofReal (((max (xiSpectralPoint ρ).im 0) ^ 2) ^ q)

/-- The upper-half elapsed moment; its support is finite at positive time. -/
def heatUpperElapsedDepthMoment (q t : ℝ) : ℝ :=
  heatWeightedZeroSum (fun z => if 0 < z.im then (z.im ^ 2 + 2 * t) ^ q else 0) t

/-- Functional-equation reflection splits the initial budget into equal halves. -/
theorem initialDepthMoment_eq_twice_upper {q : ℝ} (hq : 0 < q) :
    initialDepthMoment q = 2 * initialUpperDepthMoment q := by
  have hp (y : ℝ) : ENNReal.ofReal ((y ^ 2) ^ q) =
      ENNReal.ofReal (((max y 0) ^ 2) ^ q) +
        ENNReal.ofReal (((max (-y) 0) ^ 2) ^ q) := by
    rcases le_total 0 y with hy | hy
    · simp only [max_eq_left hy, max_eq_right (neg_nonpos.mpr hy), zero_pow two_ne_zero,
        Real.zero_rpow hq.ne', ENNReal.ofReal_zero, add_zero]
    · simp only [max_eq_right hy, max_eq_left (neg_nonneg.mpr hy), neg_sq,
        zero_pow two_ne_zero, Real.zero_rpow hq.ne', ENNReal.ofReal_zero, zero_add]
  have hreindex :
      (∑' ρ : XiZeroCopy, ENNReal.ofReal (((max (-(xiSpectralPoint ρ).im) 0) ^ 2) ^ q)) =
      ∑' ρ : XiZeroCopy, ENNReal.ofReal (((max (xiSpectralPoint ρ).im 0) ^ 2) ^ q) := by
    simpa only [xiSpectralPoint_reflect, Complex.neg_im] using
      xiZeroCopyReflectEquiv.tsum_eq
        (fun ρ => ENNReal.ofReal (((max (xiSpectralPoint ρ).im 0) ^ 2) ^ q))
  rw [show initialDepthMoment q =
    ∑' ρ : XiZeroCopy, (ENNReal.ofReal (((max (xiSpectralPoint ρ).im 0) ^ 2) ^ q) +
      ENNReal.ofReal (((max (-(xiSpectralPoint ρ).im) 0) ^ 2) ^ q)) from
    tsum_congr (fun ρ => hp (xiSpectralPoint ρ).im)]
  rw [ENNReal.tsum_add, hreindex, ← two_mul]
  rfl

/-- Conjugation splits the finite heat moment into equal upper and lower halves. -/
theorem heatElapsedDepthMoment_eq_twice_upper {q t : ℝ} (ht : 0 < t) :
    heatElapsedDepthMoment q t = 2 * heatUpperElapsedDepthMoment q t := by
  classical
  let S := (riemannHeat_nonreal_zeros_finite ht).toFinset
  let f : ℂ → ℝ := fun z => (zeroMult (riemannHeat t) z : ℝ) * (z.im ^ 2 + 2 * t) ^ q
  have hS (z : ℂ) (hz : z ∈ S) := (Set.Finite.mem_toFinset _).mp hz
  have hconj (z : ℂ) (hz : z ∈ S) : starRingEnd ℂ z ∈ S := by
    apply (Set.Finite.mem_toFinset _).mpr
    constructor
    · rw [riemannHeat_conj ht.le, (hS z hz).1, map_zero]
    · simpa only [Complex.conj_im, neg_ne_zero] using (hS z hz).2
  have hpair := congrArg Complex.re (sum_conjugate_packet S
    (fun z hz => (hS z hz).2) hconj (fun z => (f z : ℂ)))
  have heven (z : ℂ) : f (starRingEnd ℂ z) = f z := by
    simp only [f, zeroMult_riemannHeat_conj ht.le, Complex.conj_im, neg_sq]
  simp only [Complex.re_sum, Complex.add_re, Complex.ofReal_re, heven] at hpair
  have hupper : heatUpperElapsedDepthMoment q t = ∑ z ∈ S.filter (fun z => 0 < z.im), f z := by
    unfold heatUpperElapsedDepthMoment heatWeightedZeroSum
    rw [show (∑' z : ℂ, (zeroMult (riemannHeat t) z : ℝ) *
        (if 0 < z.im then (z.im ^ 2 + 2 * t) ^ q else 0)) =
        ∑ z ∈ S, (zeroMult (riemannHeat t) z : ℝ) *
        (if 0 < z.im then (z.im ^ 2 + 2 * t) ^ q else 0) from by
      apply tsum_eq_sum
      intro z hz
      by_cases hf : riemannHeat t z = 0
      · have hi : z.im = 0 := by
          by_contra hi
          exact hz ((Set.Finite.mem_toFinset _).mpr ⟨hf, hi⟩)
        simp only [hi, lt_self_iff_false, if_false, mul_zero]
      · rw [zeroMult_riemannHeat_eq_zero ht.le hf, Nat.cast_zero, zero_mul]]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    split_ifs <;> simp only [f, mul_zero]
  rw [heatElapsedDepthMoment_eq_sum q ht, hupper]
  change (∑ z ∈ S, f z) = 2 * ∑ z ∈ S.filter (fun z => 0 < z.im), f z
  rw [hpair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- The upper heat divisor obeys the same sharp initial budget as finite polynomials. -/
theorem heat_upper_elapsed_moment_le_initial {q t : ℝ} (hq : 0 < q) (ht : 0 < t) :
    ENNReal.ofReal (heatUpperElapsedDepthMoment q t) ≤ initialUpperDepthMoment q := by
  have h := heat_elapsed_moment_le_initial hq ht
  rw [heatElapsedDepthMoment_eq_twice_upper ht, initialDepthMoment_eq_twice_upper hq,
    ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num), ENNReal.ofReal_ofNat,
    mul_comm 2 (ENNReal.ofReal _), mul_comm 2 (initialUpperDepthMoment q)] at h
  exact (ENNReal.mul_le_mul_iff_left (by norm_num : (2 : ENNReal) ≠ 0) (by simp)).mp h

/-- The full surviving count is charged to twice the initial upper-half moment. -/
theorem nonrealCount_elapsed_power_le_twice_initial_upper {q t : ℝ}
    (hq : 0 < q) (ht : 0 < t) :
    ENNReal.ofReal ((2 * t) ^ q * (nonrealZeroCount t : ℝ)) ≤
      2 * initialUpperDepthMoment q := by
  rw [← initialDepthMoment_eq_twice_upper hq]
  exact nonrealCount_elapsed_power_le_initial hq ht

#print axioms heat_elapsed_moment_le_initial_bound
#print axioms heat_elapsed_moment_le_initial
#print axioms nonrealCount_elapsed_power_le_initial
#print axioms heat_upper_elapsed_moment_le_initial
#print axioms nonrealCount_elapsed_power_le_twice_initial_upper

end
end GaloisForLFunctions.ArithmeticElectrostatics
