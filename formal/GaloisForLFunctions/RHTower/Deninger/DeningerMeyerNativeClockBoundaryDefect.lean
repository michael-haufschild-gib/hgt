import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerBoundaryJetTransgression
import GaloisForLFunctions.RHTower.CCM.CCMConnesConsaniZetaCycles
import GaloisForLFunctions.RHTower.PrimeAlgebraicTranslationWeylPhase
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerXiSpectralInclusion

/-!
# The native clock exposes every full finite Xi jet from literal boundaries

One fixed actual cap test and its finite negative Euler orbits produce every
finite jet packet after a sufficiently small rational-imaginary translation.
The clock denominator is chosen from isolated zeros of its entire boundary
transform and works for every jet depth. No interpolation or source-lift
premise is imposed on the actual Xi specialization.

This is a relative boundary defect. It does not assert that translation
descends to Meyer cohomology or that the defect is a projective K-class.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

def deningerMeyerFixedBoundaryMellin : ℂ → ℂ :=
  deningerMeyerBoundaryMellin meyerPoissonTestSource

theorem deningerMeyerFixedBoundaryMellin_analytic :
    AnalyticOnNhd ℂ deningerMeyerFixedBoundaryMellin Set.univ :=
  analyticOnNhd_deningerMeyerStrongLogMellin
    (deningerMeyerStrongLogSumLM meyerPoissonTestSource).property

theorem deningerMeyerFixedBoundaryMellin_two_ne_zero :
    deningerMeyerFixedBoundaryMellin 2 ≠ 0 := by
  change deningerMeyerStrongLogMellin (deningerMeyerStrongLogSumLM meyerPoissonTestSource) 2 ≠ 0
  rw [deningerMeyerStrongLogMellin_boundary_eq_zeta_mul_mellin
    meyerPoissonTestSource (by norm_num : 1 < (2 : ℂ).re)]
  exact mul_ne_zero (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
    (mellin_meyerPoissonTestSource_ne_zero (by norm_num) (by norm_num))

theorem deningerMeyerFixedBoundaryMellin_isolated (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, deningerMeyerFixedBoundaryMellin w ≠ 0 := by
  apply (deningerMeyerFixedBoundaryMellin_analytic z (Set.mem_univ z)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
  intro h
  have hz := deningerMeyerFixedBoundaryMellin_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ z) h
  exact deningerMeyerFixedBoundaryMellin_two_ne_zero (hz (Set.mem_univ 2))

/-- A single native denominator avoids all zeros at the chosen finite nodes. -/
theorem deningerMeyerFixedBoundaryMellin_exists_nativeClock {K : ℕ} (x : Fin K → ℂ) :
    ∃ q : ℕ, 0 < q ∧ ∀ i,
      deningerMeyerFixedBoundaryMellin (x i + primeAlgebraicClockStep q) ≠ 0 := by
  have hi : ∀ i, ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 →
      deningerMeyerFixedBoundaryMellin (x i + t) ≠ 0 := by
    intro i
    have h := deningerMeyerFixedBoundaryMellin_isolated (x i)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
    obtain ⟨e, he, h⟩ := h
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨e, he, fun t ht ht0 => ?_⟩
    exact h (by simpa [dist_eq_norm] using ht) (by simpa using ht0)
  have hall := Filter.eventually_all.mpr hi
  obtain ⟨e, he, h⟩ := Metric.eventually_nhds_iff.mp hall
  obtain ⟨q, hq, hqe⟩ := exists_primeAlgebraicClockStep_norm_lt he
  refine ⟨q, hq, fun i => h (by simpa [dist_eq_norm] using hqe) i ?_⟩
  simp [primeAlgebraicClockStep, Nat.ne_of_gt hq]

theorem primeAlgebraicClockStep_re (q : ℕ) : (primeAlgebraicClockStep q).re = 0 := by
  simp [primeAlgebraicClockStep]

/-- The fixed actual cap source supplies every finite jet depth at the same clock. -/
theorem deningerMeyerBoundary_exists_nativeClock_allJets {K : ℕ}
    (x : Fin K → ℂ) (hx : Function.Injective x) (hxre : ∀ i, 0 < (x i).re) :
    ∃ q : ℕ, 0 < q ∧ ∀ m : ℕ,
      Function.Bijective (deningerMeyerBoundaryEulerJetLM meyerPoissonTestSource
        (fun i => x i + primeAlgebraicClockStep q) m) := by
  obtain ⟨q, hq, hB⟩ := deningerMeyerFixedBoundaryMellin_exists_nativeClock x
  refine ⟨q, hq, fun m => deningerMeyerBoundaryEulerJetLM_bijective _ _ m ?_ ?_ hB⟩
  · intro i j h
    exact hx (add_right_cancel h)
  · intro i h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, primeAlgebraicClockStep_re, add_zero, Complex.zero_re] at hr
    exact (ne_of_gt (hxre i)) hr

/-- All multiplicity slots of a finite array of genuine Xi points. -/
abbrev DeningerMeyerClockXiSlot {K : ℕ} (rho : Fin K → XiDivisorSupport) :=
  (i : Fin K) × Fin (xiSupportMultiplicity (rho i))

def deningerMeyerClockXiBoundaryDefectLM {K : ℕ}
    (rho : Fin K → XiDivisorSupport) (q : ℕ) :
    DeningerMeyerCap →ₗ[ℂ] (DeningerMeyerClockXiSlot rho → ℂ) :=
  LinearMap.pi fun i => (deningerMeyerStrongLogMellinJetLM i.2.val
    ((rho i.1 : ℂ) + primeAlgebraicClockStep q)).comp deningerMeyerStrongLogSumLM

/-- Actual Xi specialization: every full finite multiplicity packet is a clock
defect of a literal Poisson boundary. -/
theorem deningerMeyerClockXiBoundaryDefectLM_exists_surjective {K : ℕ}
    (rho : Fin K → XiDivisorSupport) (hrho : Function.Injective rho) :
    ∃ q : ℕ, 0 < q ∧ Function.Surjective (deningerMeyerClockXiBoundaryDefectLM rho q) := by
  classical
  have hx : Function.Injective (fun i => (rho i : ℂ)) := fun _ _ h => hrho (Subtype.ext h)
  obtain ⟨q, hq, hjet⟩ := deningerMeyerBoundary_exists_nativeClock_allJets
    (fun i => (rho i : ℂ)) hx (fun i => (xi_divisor_support_re_mem_open_unit (rho i)).1)
  refine ⟨q, hq, fun y => ?_⟩
  let m := ∑ i, xiSupportMultiplicity (rho i)
  have hm : ∀ i, xiSupportMultiplicity (rho i) ≤ m := by
    intro i
    change xiSupportMultiplicity (rho i) ≤ ∑ j, xiSupportMultiplicity (rho j)
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (xiSupportMultiplicity (rho j)))
      (Finset.mem_univ i)
  let Y : Fin K × Fin m → ℂ := fun i =>
    if h : i.2.val < xiSupportMultiplicity (rho i.1) then y ⟨i.1, ⟨i.2.val, h⟩⟩ else 0
  obtain ⟨c, hc⟩ := (hjet m).2 Y
  refine ⟨deningerMeyerBoundaryPolynomialSource meyerPoissonTestSource (K*m) c, ?_⟩
  funext i
  have h := congrFun hc (i.1, ⟨i.2.val, lt_of_lt_of_le i.2.isLt (hm i.1)⟩)
  change deningerMeyerStrongLogMellinJetLM i.2.val
    ((rho i.1 : ℂ) + primeAlgebraicClockStep q)
    (deningerMeyerStrongLogSumLM
      (deningerMeyerBoundaryPolynomialSource meyerPoissonTestSource (K*m) c)) = _ at h
  have hi : (⟨i.1, ⟨i.2.val, i.2.isLt⟩⟩ : DeningerMeyerClockXiSlot rho) = i := by
    cases i
    rfl
  change deningerMeyerStrongLogMellinJetLM i.2.val
    ((rho i.1 : ℂ) + primeAlgebraicClockStep q)
    (deningerMeyerStrongLogSumLM
      (deningerMeyerBoundaryPolynomialSource meyerPoissonTestSource (K*m) c)) = y i
  simpa only [Y, dif_pos i.2.isLt, hi] using h

/-- Before the clock translation, the same literal boundary has zero full Xi jets. -/
theorem deningerMeyerClockXiBoundaryDefectLM_zero {K : ℕ}
    (rho : Fin K → XiDivisorSupport) : deningerMeyerClockXiBoundaryDefectLM rho 0 = 0 := by
  ext f i
  change deningerMeyerStrongLogMellinJetLM i.2.val
    ((rho i.1 : ℂ) + primeAlgebraicClockStep 0) (deningerMeyerStrongLogSumLM f) = 0
  simp only [primeAlgebraicClockStep, Nat.cast_zero, div_zero, zero_mul, add_zero]
  rw [deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv,
    deningerMeyerStrongLogMellin_boundary_iteratedDeriv_zero f
      (xi_divisor_support_re_mem_open_unit (rho i.1)).1
      (xiDivisorSupport_ne_one (rho i.1)) i.2.val]
  intro j hj
  exact iteratedDeriv_riemannZeta_eq_zero_of_lt_xiSupportMultiplicity
    (rho i.1) (lt_of_le_of_lt hj i.2.isLt)

/-- The physical clock on logarithmic profiles. -/
def deningerMeyerLogClockModulation (a : ℂ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun t => Complex.exp (a * (t : ℂ)) * g t

theorem deningerMeyerLogClockModulation_mellin (a : ℂ) (g : ℝ → ℂ) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerMeyerLogClockModulation a g) s =
      deningerMeyerStrongLogMellin g (s + a) := by
  unfold deningerMeyerStrongLogMellin
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  simp only [deningerMeyerStrongLogMellinJet, deningerMeyerLogClockModulation,
    pow_zero, one_mul, add_mul, Complex.exp_add]
  ring

theorem deningerMeyerLogClockModulation_mellin_jet
    (a : ℂ) (g : ℝ → ℂ) (k : ℕ) (s : ℂ) :
    iteratedDeriv k (deningerMeyerStrongLogMellin (deningerMeyerLogClockModulation a g)) s =
      iteratedDeriv k (deningerMeyerStrongLogMellin g) (s + a) := by
  rw [show deningerMeyerStrongLogMellin (deningerMeyerLogClockModulation a g) =
      fun z => deningerMeyerStrongLogMellin g (z+a) from
    funext (deningerMeyerLogClockModulation_mellin a g)]
  exact congrFun (iteratedDeriv_comp_add_const k (deningerMeyerStrongLogMellin g) a) s

/-- A nonzero full clock defect forbids an actual Poisson boundary preimage. -/
theorem deningerMeyerClockXiBoundaryDefect_not_boundary {K : ℕ}
    (rho : Fin K → XiDivisorSupport) (q : ℕ) (f : DeningerMeyerCap)
    (hf : deningerMeyerClockXiBoundaryDefectLM rho q f ≠ 0) :
    ¬ ∃ h : DeningerMeyerCap,
      deningerMeyerLogClockModulation (primeAlgebraicClockStep q)
        (deningerMeyerStrongLogSumLM f) = (deningerMeyerStrongLogSumLM h : ℝ → ℂ) := by
  rintro ⟨h, hh⟩
  apply hf
  funext i
  change deningerMeyerStrongLogMellinJetLM i.2.val
    ((rho i.1 : ℂ) + primeAlgebraicClockStep q) (deningerMeyerStrongLogSumLM f) = 0
  rw [deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv,
    ← deningerMeyerLogClockModulation_mellin_jet, hh,
    deningerMeyerStrongLogMellin_boundary_iteratedDeriv_zero h
      (xi_divisor_support_re_mem_open_unit (rho i.1)).1
      (xiDivisorSupport_ne_one (rho i.1)) i.2.val]
  intro j hj
  exact iteratedDeriv_riemannZeta_eq_zero_of_lt_xiSupportMultiplicity
    (rho i.1) (lt_of_le_of_lt hj i.2.isLt)

/-- At every actual Xi point some native physical clock takes a literal
Poisson boundary outside the literal Poisson range. -/
theorem deningerMeyerNativeClock_not_boundary_invariant (rho : XiDivisorSupport) :
    ∃ q : ℕ, 0 < q ∧ ∃ f : DeningerMeyerCap,
      ¬ ∃ h : DeningerMeyerCap,
        deningerMeyerLogClockModulation (primeAlgebraicClockStep q)
          (deningerMeyerStrongLogSumLM f) = (deningerMeyerStrongLogSumLM h : ℝ → ℂ) := by
  let r : Fin 1 → XiDivisorSupport := fun _ => rho
  obtain ⟨q, hq, hsurj⟩ := deningerMeyerClockXiBoundaryDefectLM_exists_surjective
    r (fun _ _ _ => Subsingleton.elim _ _)
  obtain ⟨f, hf⟩ := hsurj (fun _ => 1)
  refine ⟨q, hq, f, deningerMeyerClockXiBoundaryDefect_not_boundary r q f ?_⟩
  intro hz
  have h := congrFun (hf.symm.trans hz)
    (⟨0, ⟨0, xiSupportMultiplicity_pos rho⟩⟩ : DeningerMeyerClockXiSlot r)
  exact one_ne_zero h

end
end RHTower
