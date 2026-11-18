import GaloisForLFunctions.CountingHolography.Sections.ExponentialMomentsForcePositiveWeilEnergy
import GaloisForLFunctions.CountingHolography.Sections.PrimeTraceWindows
import GaloisForLFunctions.BiScaleUncertainty.SplineProbeFiniteShiftBounds
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Small sections on the kernel of integer power sums

On a conductor interval of bounded multiplicative width, a fixed number of
integer moment equations suffices for positive degree on every nonzero ray.
The number of equations is independent of the number of conductors.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology MeasureTheory ArithmeticScatteringHolography ArithmeticCastelnuovoSeveri
open BiScaleUncertainty.ChebyshevGauge SpacingScaleHarmonicAnalysis

private def centeredSource {N : ℕ} (D : ℝ) (a : Fin N → ℤ) (u : ℝ) : ℝ :=
  ∑ i, (a i : ℝ) * cubicSpline (u - (Real.log ((i : ℝ)+1) - D))

private theorem centered_smooth {N : ℕ} (D : ℝ) (a : Fin N → ℤ) :
    ContDiff ℝ 2 (centeredSource D a) :=
  ContDiff.sum fun _ _ => contDiff_const.mul (contDiff_cubicSpline.comp (contDiff_id.sub contDiff_const))

private theorem centered_weil {N : ℕ} (D : ℝ) (a : Fin N → ℤ) :
    weilQuad (centeredSource D a) = integerProbe N a := by
  have he : centeredSource D a = fun u => splineSource a (u - (-D)) := by
    funext u
    unfold centeredSource splineSource
    apply sum_congr rfl
    intro i _
    rw [show u - (Real.log ((i : ℝ)+1) - D) = u - (-D) - Real.log ((i : ℝ)+1) by ring]
  rw [he, weilQuad_comp_sub]
  exact (integerProbe_eq_source a).symm

private def splineMoment (j : ℕ) : ℝ := ∫ u : ℝ, cubicSpline u * (Real.exp u)^j

private theorem splineMoment_pos (j : ℕ) : 0 < splineMoment j := by
  have hunit : (∫ u, cubicSpline u) = 1 := _root_.RHTower.WeilDeletion.integral_upow one_pos 3
  obtain ⟨x, hx⟩ : ∃ x, cubicSpline x ≠ 0 := by
    by_contra! h
    simp_rw [h, integral_zero] at hunit
    exact zero_ne_one hunit
  exact (contDiff_cubicSpline.continuous.mul (Real.continuous_exp.pow j)).integral_pos_of_hasCompactSupport_nonneg_nonzero
    hasCompactSupport_cubicSpline.mul_right (fun u => mul_nonneg (cubicSpline_nonneg u) (pow_nonneg (Real.exp_pos u).le j))
    (mul_ne_zero hx (pow_ne_zero _ (Real.exp_ne_zero _)))

private theorem translated_moment (d : ℝ) (j : ℕ) :
    (∫ u : ℝ, cubicSpline (u-d) * (Real.exp u)^j) = splineMoment j * (Real.exp d)^j := by
  rw [← integral_add_right_eq_self (fun u => cubicSpline (u-d) * (Real.exp u)^j) d]
  simp_rw [add_sub_cancel_right, Real.exp_add, mul_pow, ← mul_assoc]
  exact integral_mul_const _ _

/-- Translating the probe identifies its exponential moments with ordinary power sums. -/
private theorem centered_moment {N : ℕ} (a : Fin N → ℤ) (D : ℝ) (j : ℕ) :
    (∫ u : ℝ, centeredSource D a u * (Real.exp u)^j) =
      (splineMoment j / (Real.exp D)^j) * ∑ i : Fin N, ((i : ℝ)+1)^j * (a i : ℝ) := by
  let d (i : Fin N) := Real.log ((i : ℝ)+1) - D
  have hi (i : Fin N) : Integrable fun u => (a i : ℝ) * (cubicSpline (u-d i) * (Real.exp u)^j) :=
    (((contDiff_cubicSpline.continuous.comp (continuous_id.sub continuous_const)).mul
      (Real.continuous_exp.pow j)).integrable_of_hasCompactSupport
      (hasCompactSupport_cubicSpline.comp_homeomorph (Homeomorph.subRight (d i))).mul_right).const_mul _
  simp_rw [centeredSource, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ fun i _ => hi i, Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  rw [integral_const_mul, translated_moment, Real.exp_sub, Real.exp_log (by positivity), div_pow]
  ring

private theorem centered_ne_zero {N : ℕ} {a : Fin N → ℤ} (ha : a ≠ 0) (D : ℝ) :
    centeredSource D a ≠ 0 := by
  intro h
  have hzero (j : ℕ) : ∑ i : Fin N, ((i : ℝ)+1)^j * (a i : ℝ) = 0 := by
    have he := centered_moment a D j
    rw [h] at he
    simp only [Pi.zero_apply, zero_mul, integral_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (div_pos (splineMoment_pos _) (by positivity)).ne'
  have hv : (fun i => (a i : ℝ)) = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero (M := (Matrix.vandermonde (fun i : Fin N => (i : ℝ)+1)).transpose)
    · rw [Matrix.det_transpose, Matrix.det_vandermonde_ne_zero_iff]
      intro i j hij
      apply Fin.ext
      exact_mod_cast (add_right_cancel hij : (i.val : ℝ) = j.val)
    · funext j
      exact hzero j.val
  apply ha
  funext i
  change a i = 0
  have hi : (a i : ℝ) = 0 := congrFun hv i
  exact_mod_cast hi

private theorem centered_window {N B : ℕ} (hB : 0 < B) {a : Fin N → ℤ}
    (hh : ∀ i : Fin N, i.val < N / B → a i = 0) :
    ∀ u, u ∉ Set.Icc (-(Real.log B + 8)) 0 →
      centeredSource (Real.log (N+1 : ℝ)+4) a u = 0 := by
  intro u hu
  unfold centeredSource
  apply sum_eq_zero
  intro i _
  by_cases hi : i.val < N / B
  · rw [hh i hi, Int.cast_zero, zero_mul]
  apply mul_eq_zero_of_right
  apply cubicSpline_eq_zero
  have hm : N+1 ≤ B*(i.val+1) := by
    rw [Nat.mul_comm]
    exact (Nat.div_lt_iff_lt_mul hB).mp (Nat.lt_succ_of_le (le_of_not_gt hi))
  have hr : Real.log (N+1 : ℝ) ≤ Real.log B + Real.log ((i : ℝ)+1) := by
    rw [← Real.log_mul (by exact_mod_cast hB.ne') (by positivity)]
    apply Real.log_le_log (by positivity)
    exact_mod_cast hm
  have hl : Real.log ((i : ℝ)+1) ≤ Real.log (N+1 : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right i.isLt.le 1)
  rcases lt_or_ge u (-(Real.log B + 8)) with h | h
  · linarith only [h, hr, neg_le_abs (u - (Real.log ((i : ℝ)+1) - (Real.log (N+1 : ℝ)+4)))]
  · have hp : 0 < u := lt_of_not_ge (fun hn => hu ⟨h,hn⟩)
    linarith only [hp, hl, le_abs_self (u - (Real.log ((i : ℝ)+1) - (Real.log (N+1 : ℝ)+4)))]

/-- Each bounded-ratio conductor window has a fixed integer moment kernel of strictly
positive degree, uniform in the conductor and the coefficients. -/
theorem positive_integer_window_moments (B : ℕ) (hB : 0 < B) :
    ∃ k : ℕ, ∀ (N : ℕ) (a : Fin N → ℤ), a ≠ 0 →
      (∀ i : Fin N, i.val < N / B → a i = 0) →
      (∀ j < k, ∑ i : Fin N, ((i : ℝ)+1)^j * (a i : ℝ) = 0) → 0 < integerProbe N a := by
  have hlog : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB)
  obtain ⟨k, hk⟩ := unit_weil_energy_of_vanishing_moments (A := Real.log B+8) (by linarith) 0
  refine ⟨k, fun N a ha hh hm => ?_⟩
  let D := Real.log (N+1 : ℝ)+4
  let f := centeredSource D a
  have hf : ContDiff ℝ 2 f := centered_smooth D a
  have hs : ∀ u, u ∉ Set.Icc (-(Real.log B+8)) 0 → f u = 0 := centered_window hB hh
  obtain ⟨x,hx⟩ : ∃ x, f x ≠ 0 := by simpa [funext_iff,f] using centered_ne_zero ha D
  let M := ∫ u, f u^2
  have hM : 0 < M := (hf.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.intro (K := Set.Icc (-(Real.log B+8)) 0) isCompact_Icc (fun u hu => by simp [hs u hu]))
    (fun u => sq_nonneg _) (pow_ne_zero _ hx)
  let c := (Real.sqrt M)⁻¹
  have hnorm : (∫ u, (c * f u)^2) = 1 := by
    simp_rw [mul_pow]
    rw [integral_const_mul]
    change (Real.sqrt M)⁻¹ ^ 2 * M = 1
    rw [inv_pow, Real.sq_sqrt hM.le, inv_mul_cancel₀ hM.ne']
  have hz : vanishingExpMoments k (fun u => c*f u) := by
    intro j hj
    simp only [mul_assoc, integral_const_mul, f, centered_moment, hm j hj, mul_zero]
  have hp := hk _ (contDiff_const.mul hf) (fun u hu => by rw [hs u hu, mul_zero]) hnorm hz
  rw [CohomologyOfWindowsOfSpecZ.weilQuad_const_mul] at hp
  have hg := pos_of_mul_pos_right hp (sq_nonneg c)
  rwa [show weilQuad f = integerProbe N a from centered_weil D a] at hg

private def windowReadings (N B k : ℕ) : (Fin N → ℚ) →ₗ[ℚ] ((Fin (N/B) → ℚ) × (Fin k → ℚ)) where
  toFun v := (fun i => v (Fin.castLE (Nat.div_le_self N B) i),
    fun j => ∑ i : Fin N, ((i : ℚ)+1)^j.val * v i)
  map_add' v w := by
    apply Prod.ext
    · rfl
    funext j
    change ∑ i : Fin N, ((i : ℚ)+1)^j.val * (v i+w i) =
      (∑ i : Fin N, ((i : ℚ)+1)^j.val*v i) + ∑ i : Fin N, ((i : ℚ)+1)^j.val*w i
    simp only [mul_add, sum_add_distrib]
  map_smul' c v := by
    apply Prod.ext
    · rfl
    funext j
    change ∑ i : Fin N, ((i : ℚ)+1)^j.val * (c*v i) = c*∑ i : Fin N, ((i : ℚ)+1)^j.val*v i
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring

/-- Rational equations cutting out vectors supported past the initial N/B conductors
whose first k integer power sums vanish. -/
def windowMomentKernel (N B k : ℕ) : Submodule ℚ (Fin N → ℚ) := (windowReadings N B k).ker

theorem windowMomentKernel_rank (N B k : ℕ) :
    N ≤ Module.finrank ℚ (windowMomentKernel N B k) + N/B + k := by
  let T := windowReadings N B k
  have he := T.finrank_range_add_finrank_ker
  have hl := Submodule.finrank_le (LinearMap.range T)
  simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at he hl
  change N ≤ Module.finrank ℚ T.ker + N/B + k
  omega

private theorem windowMomentKernel_integer {N B k : ℕ} {a : Fin N → ℤ}
    (hv : (fun i => (a i : ℚ)) ∈ windowMomentKernel N B k) :
    (∀ i : Fin N, i.val < N/B → a i = 0) ∧
      ∀ j < k, ∑ i : Fin N, ((i : ℝ)+1)^j * (a i : ℝ) = 0 := by
  have he : windowReadings N B k (fun i => (a i : ℚ)) = 0 := hv
  constructor
  · intro i hi
    have h := congrFun (congrArg Prod.fst he) ⟨i.val, hi⟩
    change (a i : ℚ) = 0 at h
    exact_mod_cast h
  · intro j hj
    have h := congrFun (congrArg Prod.snd he) ⟨j,hj⟩
    change ∑ i : Fin N, ((i : ℚ)+1)^j * (a i : ℚ) = 0 at h
    exact_mod_cast h

/-- On every nonzero integral ray in this kernel the ordinary section count recovers
the full signed degree and the original radius admits nonzero small sections. -/
theorem windowMomentKernel_smallSections (B : ℕ) (hB : 0 < B) :
    ∃ k : ℕ, ∀ (N : ℕ) (a : Fin N → ℤ), a ≠ 0 →
      (fun i => (a i : ℚ)) ∈ windowMomentKernel N B k →
      Tendsto (fun m : ℕ => (splineCount (m • a) : ℝ) / (m : ℝ)^2)
        atTop (𝓝 (integerProbe N a)) ∧
      ∀ᶠ m : ℕ in atTop, ∃ z ∈ smallSections (generator (m • a) : ℝ) (radius (m • a)), z ≠ 0 := by
  obtain ⟨k,hk⟩ := positive_integer_window_moments B hB
  refine ⟨k, fun N a ha hv => ?_⟩
  obtain ⟨hh,hm⟩ := windowMomentKernel_integer hv
  have hp := hk N a ha hh hm
  refine ⟨?_, ?_⟩
  · simpa only [max_eq_left hp.le] using splineCount_tateLimit a
  filter_upwards [eventually_log_generator_lt_radius hp] with m h
  exact (exists_nonzero_smallSection (by exact_mod_cast contactGenerator_pos _ _ _)).mpr h.le

/-- At all sufficiently large horizons a rational subspace of relative dimension
at least 1−ε has a section-carrying integral multiple of every nonzero rational vector. -/
theorem smallSections_on_subspaces_of_density_one (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ V : Submodule ℚ (Fin N → ℚ),
      (1-ε)*(N : ℝ) ≤ Module.finrank ℚ V ∧
      ∀ v ∈ V, v ≠ 0 → ∃ (D : ℕ) (a : Fin N → ℤ), 0 < D ∧
        (fun i => (a i : ℚ)) = (D : ℚ) • v ∧
        ∀ᶠ m : ℕ in atTop, ∃ z ∈ smallSections (generator (m • a) : ℝ) (radius (m • a)), z ≠ 0 := by
  obtain ⟨B,hB⟩ := exists_nat_gt (2/ε)
  have hBr : 0 < (B : ℝ) := (div_pos (by norm_num) hε).trans hB
  obtain ⟨k,hk⟩ := windowMomentKernel_smallSections B (by exact_mod_cast hBr)
  obtain ⟨L,hL⟩ := exists_nat_gt (2*(k : ℝ)/ε)
  filter_upwards [eventually_ge_atTop L] with N hN
  refine ⟨windowMomentKernel N B k, ?_, fun v hv hv0 => ?_⟩
  · have hr := windowMomentKernel_rank N B k
    have hr' : (N : ℝ) ≤ Module.finrank ℚ (windowMomentKernel N B k) + ((N/B : ℕ) : ℝ) + (k : ℝ) := by exact_mod_cast hr
    have hdiv : ((N/B : ℕ) : ℝ)*(B : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.div_mul_le_self N B
    have hc := (div_lt_iff₀ hε).mp hB
    have ht := (div_lt_iff₀ hε).mp (hL.trans_le (by exact_mod_cast hN : (L : ℝ) ≤ N))
    have hhalf : 2*((N/B : ℕ) : ℝ) ≤ (N : ℝ)*ε :=
      calc 2*((N/B : ℕ) : ℝ) ≤ ((B : ℝ)*ε)*((N/B : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_right hc.le (by positivity)
           _ = (((N/B : ℕ) : ℝ)*B)*ε := by ring
           _ ≤ _ := mul_le_mul_of_nonneg_right hdiv hε.le
    linarith only [hr', ht, hhalf]
  · obtain ⟨D,a,hD,hd⟩ := ArithmeticScatteringHolography.exists_common_denominator v
    have he : (fun i => (a i : ℚ)) = (D : ℚ) • v := by
      funext i
      change (a i : ℚ) = (D : ℚ)*v i
      rw [mul_comm]
      exact_mod_cast (hd i).symm
    have ha : a ≠ 0 := by
      intro h
      apply hv0
      funext i
      have hi : (a i : ℚ) = (D : ℚ)*v i := congrFun he i
      rw [h, Pi.zero_apply, Int.cast_zero] at hi
      exact (mul_eq_zero.mp hi.symm).resolve_left (Nat.cast_ne_zero.mpr hD.ne')
    have hmem : (fun i => (a i : ℚ)) ∈ windowMomentKernel N B k := by
      rw [he]
      exact (windowMomentKernel N B k).smul_mem _ hv
    exact ⟨D, a, hD, he, (hk N a ha hmem).2⟩

#print axioms positive_integer_window_moments
#print axioms windowMomentKernel_rank
#print axioms windowMomentKernel_smallSections
#print axioms smallSections_on_subspaces_of_density_one

end GaloisForLFunctions.CountingHolography.Sections
