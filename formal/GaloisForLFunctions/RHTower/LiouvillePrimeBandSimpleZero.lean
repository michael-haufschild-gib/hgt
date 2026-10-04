import GaloisForLFunctions.RHTower.LiouvillePrimeBandDecomposition
import GaloisForLFunctions.RHTower.LiouvilleTwistedPrimeCapacity
import GaloisForLFunctions.RHTower.LiouvilleTwistedDensityCenter
import GaloisForLFunctions.HTGeometry.HurwitzClosedZeroLocus

/-!
# Simple zeros of the complete exponential arithmetic weight

Two actual prime bands supply a strict capacity surplus. Full cofactor errors and the
original nonlinear tail transfer that surplus to the exact center. The full real-scale
logarithmic center limit then pays the entire error budget. Aligning
the actual cofactor responses produces a zero in a moving disc strictly inside the
unit disc; the full derivative bound proves that this zero is simple.

The final existence theorem has no cancellation, summability, or zero hypotheses.
It concerns the complete prime-phase evaluation of the exponential harmonic weight,
not a zero of zeta. The RH-critical Liouville lower bound remains a separate problem.
-/

open Filter Finset
open scoped Topology BigOperators Classical

namespace RHTower.LiouvillePrimeBand
noncomputable section
open RHTower.LiouvilleTwistedDensity

private def align (w : ℂ) : ℂ := if w = 0 then 1 else (starRingEnd ℂ) w / (‖w‖ : ℂ)

private theorem norm_align (w : ℂ) : ‖align w‖ = 1 := by
  by_cases hw : w = 0
  · simp [align, hw]
  · simp [align, hw, Complex.norm_real, norm_ne_zero_iff.mpr hw]

private theorem align_mul (w : ℂ) : align w * w = (‖w‖ : ℂ) := by
  by_cases hw : w = 0
  · simp [align, hw]
  · rw [align, if_neg hw, div_mul_eq_mul_div, mul_comm ((starRingEnd ℂ) w),
      Complex.mul_conj, ← Complex.sq_norm]
    have hn : (‖w‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw)
    push_cast
    field_simp

private theorem affine_simple_zero {C : ℂ} {S b : ℝ} {R : ℂ → ℂ}
    (hb : 0 ≤ b) (hgap : 6 * b < S - ‖C‖)
    (hR : ∀ z : ℂ, ‖z‖ ≤ 1 → HasDerivAt R (deriv R z) z)
    (hval : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖R z‖ ≤ b)
    (hder : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖deriv R z‖ ≤ b) :
    ∃ z : ℂ, ‖z‖ < 1 ∧ C + (S : ℂ) * z + R z = 0 ∧
      deriv (fun w => C + (S : ℂ) * w + R w) z ≠ 0 := by
  have hS : 0 < S := by linarith [norm_nonneg C]
  have hSC : ‖C‖ < S := by linarith
  have hbS : b < S := by linarith [norm_nonneg C]
  have hSne : (S : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS.ne'
  let z₀ : ℂ := -C / S
  let r : ℝ := (S - ‖C‖) / (2 * S)
  let A : ℂ → ℂ := fun z => C + (S : ℂ) * z
  have hr : 0 < r := div_pos (sub_pos.mpr hSC) (by positivity)
  have hz₀ : ‖z₀‖ = ‖C‖ / S := by
    dsimp [z₀]
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
  have hin : r + ‖z₀‖ < 1 := by
    rw [hz₀]
    calc
      _ = (S + ‖C‖) / (2 * S) := by dsimp [r]; field_simp; ring
      _ < 1 := (div_lt_one (by positivity : 0 < 2 * S)).mpr (by linarith)
  have hball : ∀ z ∈ Metric.closedBall z₀ r, ‖z‖ < 1 := by
    intro z hz
    have hdist : ‖z - z₀‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    calc
      ‖z‖ = ‖(z-z₀)+z₀‖ := by congr 1; ring
      _ ≤ ‖z-z₀‖ + ‖z₀‖ := norm_add_le _ _
      _ ≤ r + ‖z₀‖ := add_le_add hdist le_rfl
      _ < 1 := hin
  have hA : ∀ z : ℂ, HasDerivAt A (S : ℂ) z := by
    intro z
    simpa [A] using ((hasDerivAt_id z).const_mul (S : ℂ)).const_add C
  have hA₀ : A z₀ = 0 := by dsimp [A, z₀]; field_simp [hSne]; ring
  have hRc : DiffContOnCl ℂ R (Metric.ball z₀ r) := by
    constructor
    · intro z hz
      exact (hR z (hball z (Metric.ball_subset_closedBall hz)).le).differentiableAt.differentiableWithinAt
    · rw [closure_ball _ hr.ne']
      intro z hz
      exact (hR z (hball z hz).le).continuousAt.continuousWithinAt
  have hAc : DiffContOnCl ℂ A (Metric.ball z₀ r) := by
    constructor
    · intro z _
      exact (hA z).differentiableAt.differentiableWithinAt
    · intro z _
      exact (hA z).continuousAt.continuousWithinAt
  have hdom : ∀ z ∈ Metric.sphere z₀ r, 3 * ‖R z‖ ≤ ‖A z‖ := by
    intro z hz
    have hdist : ‖z-z₀‖ = r := by simpa only [Metric.mem_sphere, dist_eq_norm] using hz
    have hrepr : A z = (S : ℂ) * (z-z₀) := by dsimp [A, z₀]; field_simp [hSne]; ring
    have hnorm : ‖A z‖ = (S - ‖C‖) / 2 := by
      rw [hrepr, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS, hdist]
      dsimp [r]
      field_simp
    have hv := hval z (hball z (Metric.sphere_subset_closedBall hz)).le
    rw [hnorm]
    linarith
  have hzero : ∃ z ∈ Metric.closedBall z₀ r, A z + R z = 0 := by
    by_cases hc : R z₀ = 0
    · exact ⟨z₀, Metric.mem_closedBall_self hr.le, by rw [hA₀, hc, add_zero]⟩
    · obtain ⟨z, hz, he⟩ := GaloisForLFunctions.HTGeometry.exists_zero_of_sphere_domination
        hr hRc hAc hA₀ hc hdom
      exact ⟨z, hz, by simpa only [add_comm] using he⟩
  obtain ⟨z, hz, he⟩ := hzero
  have hz1 := hball z hz
  have hd := (hA z).add (hR z hz1.le)
  refine ⟨z, hz1, he, ?_⟩
  change deriv (A + R) z ≠ 0
  rw [hd.deriv]
  intro hf
  have heq : deriv R z = -(S : ℂ) := by linear_combination hf
  have hn : ‖deriv R z‖ = S := by
    rw [heq, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
  have hdv := hder z hz1.le
  linarith

private theorem selected_mem {a b c d T : ℝ} (ha : 1 < a) (hab : a < b)
    (hbc : b < c) (hcd : c < d) (hT : 0 < T) {p : ℕ}
    (hp : p ∈ selectedPrimes a b c d T) : p.Prime ∧ T < (p : ℝ) ∧ (p : ℝ) ≤ d * T := by
  have hwin : ∀ u v : ℝ, 1 < u → u < v → v ≤ d → p ∈ primeWindow u v T →
      p.Prime ∧ T < (p : ℝ) ∧ (p : ℝ) ≤ d*T := by
    intro u v hu huv hv hpv
    obtain ⟨hpp, hlo, hhi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hpv
    have hpl : u*T < (p : ℝ) := Nat.lt_of_floor_lt hlo
    have hpu : (p : ℝ) ≤ v*T := (by exact_mod_cast hhi : (p : ℝ) ≤ (⌊v*T⌋₊ : ℝ)).trans
      (Nat.floor_le (mul_nonneg (by linarith : 0 ≤ v) hT.le))
    exact ⟨hpp, (by nlinarith), hpu.trans (mul_le_mul_of_nonneg_right hv hT.le)⟩
  rcases Finset.mem_union.mp hp with hp | hp
  · exact hwin a b ha hab (by linarith) hp
  · exact hwin c d (by linarith) hcd le_rfl hp

private theorem selected_mass_le {a b c d T : ℝ} (ha : 1 < a) (hab : a < b)
    (hbc : b < c) (hcd : c < d) (hT : 0 < T) :
    (∑ p ∈ selectedPrimes a b c d T, 1 / (p : ℝ)) ≤ d := by
  let P := selectedPrimes a b c d T
  have hsub : P ⊆ Finset.Icc 1 ⌊d*T⌋₊ := by
    intro p hp
    obtain ⟨hpp, _, hpu⟩ := selected_mem ha hab hbc hcd hT hp
    exact Finset.mem_Icc.mpr ⟨hpp.one_lt.le, Nat.le_floor hpu⟩
  have hcard : (P.card : ℝ) ≤ d*T := by
    have hc : P.card ≤ ⌊d*T⌋₊ := by simpa using Finset.card_le_card hsub
    exact (by exact_mod_cast hc : (P.card : ℝ) ≤ (⌊d*T⌋₊ : ℝ)).trans (Nat.floor_le (mul_nonneg (by linarith : 0 ≤ d) hT.le))
  calc
    _ ≤ ∑ p ∈ P, 1 / T := Finset.sum_le_sum fun p hp =>
      one_div_le_one_div_of_le hT (selected_mem ha hab hbc hcd hT hp).2.1.le
    _ = (P.card : ℝ) / T := by simp [div_eq_mul_inv]
    _ ≤ d := (div_le_iff₀ hT).mpr hcard

private theorem actual_gap_lower {a b c d T : ℝ} (ha : 1 < a) (hab : a < b)
    (hbc : b < c) (hcd : c < d) (hT : 2 < T) :
    idealCapacity a b c d T - ‖idealCenter a b c d T‖ -
      (2 * (d * Real.exp (-T) / (1-Real.exp (-1))) + ‖exponentialDensity (1/T)‖ +
        (T+1)*Real.exp (-T)) ≤
      (∑ p ∈ selectedPrimes a b c d T, ‖cofactorResponse (selectedPrimes a b c d T) (1/T) p‖) -
      ‖cofactorDensity (selectedPrimes a b c d T) (1/T)‖ := by
  let P := selectedPrimes a b c d T
  let A := cofactorResponse P (1/T)
  let B := idealCoefficient T
  let E : ℝ := ∑ p ∈ P, ‖A p - B p‖
  have hT0 : 0 < T := by linarith
  have hp := fun p (hp : p ∈ P) => selected_mem ha hab hbc hcd hT0 hp
  have hPprime : ∀ p ∈ P, p.Prime := fun p hm => (hp p hm).1
  have hPgt : ∀ p ∈ P, T < (p : ℝ) := fun p hm => (hp p hm).2.1
  have h2 : 2 ∉ P := by intro h; have := hPgt 2 h; norm_num at this; linarith
  have hE : E ≤ d * Real.exp (-T) / (1-Real.exp (-1)) := by
    have he := cofactorResponse_total_error hT0.le hPgt (t := 1/T)
      (fun p hm => by
        rw [one_div, ← div_eq_mul_inv]
        exact (le_div_iff₀ hT0).mpr (by simpa using (hPgt p hm).le))
    have heq : ∀ p : ℕ, exponentialDensity ((p : ℝ) * (1/T)) / (p : ℂ) = B p := by
      intro p
      dsimp [B, idealCoefficient]
      push_cast
      have hpt : (p : ℝ) * (1/T) = (p : ℝ) / T := by ring
      rw [hpt]
      ring
    simp only [heq] at he
    apply he.trans
    have hh := selected_mass_le ha hab hbc hcd hT0
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hh
      (div_nonneg (Real.exp_pos _).le (by have := Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0); linarith))
  have hcap : idealCapacity a b c d T ≤ (∑ p ∈ P, ‖A p‖) + E := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p _
    have h := norm_sub_norm_le (B p) (A p)
    rw [norm_sub_rev] at h
    linarith
  have hsum : ‖∑ p ∈ P, A p‖ ≤ ‖idealCenter a b c d T‖ + E := by
    have hh : ‖(∑ p ∈ P, A p) - ∑ p ∈ P, B p‖ ≤ E := by
      rw [← Finset.sum_sub_distrib]
      exact norm_sum_le _ _
    have hn := norm_sub_norm_le (∑ p ∈ P, A p) (∑ p ∈ P, B p)
    change ‖(∑ p ∈ P, A p)‖ - ‖idealCenter a b c d T‖ ≤ _ at hn
    linarith
  have hbase := baseline_decomposition hPprime h2 (one_div_pos.mpr hT0)
  have hrem := (nonlinearRemainder_bounds_exp (P := P) (β := fun _ => -1)
    (by intro p hm; simp) hT0 hPgt (z := 1) (by simp)).1
  have hcenter : ‖cofactorDensity P (1/T)‖ ≤
      ‖exponentialDensity (1/T)‖ + ‖∑ p ∈ P, A p‖ + (T+1)*Real.exp (-T) := by
    have he : cofactorDensity P (1/T) = exponentialDensity (1/T) + (∑ p ∈ P, A p) -
        nonlinearRemainder P (fun _ => -1) (1/T) 1 := by rw [hbase]; dsimp [A]; ring
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) hrem)
  change _ ≤ (∑ p ∈ P, ‖A p‖) - ‖cofactorDensity P (1/T)‖
  linarith

private theorem source_simple_zero_of_gap {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {T : ℝ} (hT : 0 < T) (hPgt : ∀ p ∈ P, T < (p : ℝ))
    (hgap : 6 * ((T+1)*Real.exp (-T)) <
      (∑ p ∈ P, ‖cofactorResponse P (1/T) p‖) - ‖cofactorDensity P (1/T)‖) :
    ∃ β : ℕ → ℂ, (∀ p, ‖β p‖ = 1) ∧ ∃ z : ℂ,
      ‖z‖ < 1 ∧ source P β (1/T) z = 0 ∧ deriv (source P β (1/T)) z ≠ 0 := by
  let β : ℕ → ℂ := fun p => align (cofactorResponse P (1/T) p)
  let C := cofactorDensity P (1/T)
  let S : ℝ := ∑ p ∈ P, ‖cofactorResponse P (1/T) p‖
  let R := nonlinearRemainder P β (1/T)
  have hβ : ∀ p, ‖β p‖ = 1 := fun p => norm_align _
  have hβP : ∀ p ∈ P, ‖β p‖ = 1 := fun p _ => hβ p
  have ht : 0 < 1/T := one_div_pos.mpr hT
  have hslope : (∑ p ∈ P, β p * cofactorResponse P (1/T) p) = (S : ℂ) := by
    calc
      _ = ∑ p ∈ P, (‖cofactorResponse P (1/T) p‖ : ℂ) :=
        Finset.sum_congr rfl fun p _ => align_mul _
      _ = _ := by dsimp [S]; push_cast; rfl
  have he : ∀ z : ℂ, ‖z‖ ≤ 1 → source P β (1/T) z = C + (S : ℂ) * z + R z := by
    intro z hz
    rw [source_decomposition hP hβP ht hz, hslope]
    dsimp [C, R]
    ring
  have hR : ∀ z : ℂ, ‖z‖ ≤ 1 → HasDerivAt R (deriv R z) z := by
    intro z hz
    exact (hasDerivAt_degreeSlice hβP ht (Set.Ici 2) hz).differentiableAt.hasDerivAt
  have hb := fun z (hz : ‖z‖ ≤ 1) => nonlinearRemainder_bounds_exp hβP hT hPgt hz
  obtain ⟨z, hz, hzero, hsimple⟩ := affine_simple_zero (C := C) (S := S) (R := R)
    (by positivity : 0 ≤ (T+1)*Real.exp (-T)) hgap hR
    (fun z hz => (hb z hz).1) (fun z hz => (hb z hz).2)
  refine ⟨β, hβ, z, hz, by rw [he z hz.le]; exact hzero, ?_⟩
  have hevent : source P β (1/T) =ᶠ[𝓝 z] (fun w => C + (S : ℂ) * w + R w) := by
    have hnear : ∀ᶠ w : ℂ in 𝓝 z, ‖w‖ < 1 :=
      continuous_norm.continuousAt.tendsto.eventually (isOpen_Iio.mem_nhds hz)
    filter_upwards [hnear] with w hw
    exact he w hw.le
  rw [hevent.deriv_eq]
  exact hsimple

private theorem log_poly_exp_decay (m : ℕ) :
    Tendsto (fun T : ℝ => Real.log T * (T ^ m * Real.exp (-T))) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => T ^ (m+1) * Real.exp (-T)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, neg_one_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((m+1 : ℕ) : ℝ) 1 zero_lt_one
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact mul_nonneg (Real.log_nonneg hT) (by positivity)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    calc
      _ ≤ T * (T ^ m * Real.exp (-T)) := mul_le_mul_of_nonneg_right
        (Real.log_le_self (by linarith)) (by positivity)
      _ = _ := by rw [pow_succ]; ring

private theorem square_scale_tendsto :
    Tendsto (fun N : ℕ => ((N : ℝ)+1)^2) atTop atTop :=
  (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

private theorem total_error_tendsto (d : ℝ) :
    Tendsto (fun T : ℝ => Real.log T *
      (2 * (d * Real.exp (-T) / (1-Real.exp (-1))) +
        ‖exponentialDensity (1/T)‖ + 7*((T+1)*Real.exp (-T)))) atTop (𝓝 0) := by
  have h0 : Tendsto (fun T : ℝ => Real.log T * Real.exp (-T)) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul] using log_poly_exp_decay 0
  have h1 : Tendsto (fun T : ℝ => Real.log T * (T * Real.exp (-T))) atTop (𝓝 0) := by
    simpa only [pow_one] using log_poly_exp_decay 1
  have hc : Tendsto (fun T : ℝ => Real.log T * ‖exponentialDensity (1/T)‖) atTop (𝓝 0) := by
    have hh := tendsto_log_mul_exponentialDensity_reciprocal_zero.norm
    simp only [norm_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hT)]
  have h := ((h0.const_mul (2*d/(1-Real.exp (-1)))).add hc).add ((h1.add h0).const_mul 7)
  simp only [mul_zero, add_zero] at h
  convert h using 1
  funext T
  ring

/-- Every sufficiently large real scale has a simple zero of the complete prime-phase source.
No cancellation, density, or zero-existence hypothesis is supplied. -/
theorem exists_eventually_simple_prime_phase_zero :
    ∃ a b c d : ℝ, 1 < a ∧ a < b ∧ b < c ∧ c < d ∧
      ∀ᶠ T : ℝ in atTop,
        ∃ β : ℕ → ℂ, (∀ p, ‖β p‖ = 1) ∧ ∃ z : ℂ,
          ‖z‖ < 1 ∧ source (selectedPrimes a b c d T) β (1/T) z = 0 ∧
            deriv (source (selectedPrimes a b c d T) β (1/T)) z ≠ 0 := by
  obtain ⟨a,b,c,d,κ,ha,hab,hbc,hcd,hκ,hcap⟩ := exists_prime_phase_capacity_gap
  have hsmall := (total_error_tendsto d).eventually (isOpen_Iio.mem_nhds hκ)
  refine ⟨a,b,c,d,ha,hab,hbc,hcd,?_⟩
  filter_upwards [hsmall, hcap, eventually_gt_atTop (2 : ℝ)] with T hs hc hT
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have hb : 2 * (d * Real.exp (-T) / (1-Real.exp (-1))) +
      ‖exponentialDensity (1/T)‖ + 7*((T+1)*Real.exp (-T)) <
      idealCapacity a b c d T - ‖idealCenter a b c d T‖ := by
    by_contra h
    have hh := mul_le_mul_of_nonneg_left (le_of_not_gt h) hL.le
    exact (not_lt_of_ge hh) (hs.trans_le hc)
  have hg := actual_gap_lower ha hab hbc hcd hT
  have hgap : 6*((T+1)*Real.exp (-T)) <
      (∑ p ∈ selectedPrimes a b c d T, ‖cofactorResponse (selectedPrimes a b c d T) (1/T) p‖) -
      ‖cofactorDensity (selectedPrimes a b c d T) (1/T)‖ := by linarith
  exact source_simple_zero_of_gap
    (fun p hp => (selected_mem ha hab hbc hcd (by linarith : 0 < T) hp).1)
    (by linarith : 0 < T)
    (fun p hp => (selected_mem ha hab hbc hcd (by linarith : 0 < T) hp).2.1) hgap

/-- In particular, the square-scale subfamily has simple zeros. -/
theorem exists_cofinal_simple_prime_phase_zero :
    ∃ a b c d : ℝ, 1 < a ∧ a < b ∧ b < c ∧ c < d ∧
      ∀ᶠ N : ℕ in atTop,
        let T := ((N : ℝ)+1)^2
        ∃ β : ℕ → ℂ, (∀ p, ‖β p‖ = 1) ∧ ∃ z : ℂ,
          ‖z‖ < 1 ∧ source (selectedPrimes a b c d T) β (1/T) z = 0 ∧
            deriv (source (selectedPrimes a b c d T) β (1/T)) z ≠ 0 := by
  obtain ⟨a,b,c,d,ha,hab,hbc,hcd,h⟩ := exists_eventually_simple_prime_phase_zero
  exact ⟨a,b,c,d,ha,hab,hbc,hcd,square_scale_tendsto.eventually h⟩

end
end RHTower.LiouvillePrimeBand
