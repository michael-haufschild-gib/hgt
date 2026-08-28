import GaloisForLFunctions.RHTower.SoninAllPrimeMomentApertureContinuity
import GaloisForLFunctions.RHTower.SoninAllPrimeMomentWeldApertureFloor

/-!
# Exact positive aperture for the all-prime Sonin zeroth moment

Positive-aperture Hilbert--Schmidt continuity, the quadratic small-aperture ceiling, and
large-aperture escape force the intrinsic all-prime zeroth trace moment through every positive
real target.  In particular, it hits the normalized prime--archimedean zeroth moment exactly at
some finite positive aperture.

No Xi zero, RH premise, numerical computation, or unproved asymptotic is used.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Every intrinsic all-prime trace moment is continuous at each positive aperture. -/
theorem continuousAt_soninAllPrimeEnergyMoment
    (a : ℝ) (ha : 0 < a) (r : ℕ) :
    ContinuousAt (fun b : ℝ => soninAllPrimeEnergyMoment b r) a := by
  change Tendsto (fun b : ℝ => soninAllPrimeEnergyMoment b r) (𝓝 a)
    (𝓝 (soninAllPrimeEnergyMoment a r))
  rw [tendsto_nhds_iff_seq_tendsto]
  intro u hu
  have huPosEventually : ∀ᶠ n in atTop, 0 < u n :=
    hu.eventually (Ioi_mem_nhds ha)
  obtain ⟨N, hN⟩ := eventually_atTop.1 huPosEventually
  let v : ℕ → ℝ := fun n => if N ≤ n then u n else a
  have hvPos : ∀ n, 0 < v n := by
    intro n
    dsimp only [v]
    split_ifs with hn
    · exact hN n hn
    · exact ha
  have huv : u =ᶠ[atTop] v := by
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [v, hn]
  have hv : Tendsto v atTop (𝓝 a) := hu.congr' huv
  have hmoment := tendsto_soninAllPrimeEnergyMoment_of_tendsto hvPos ha hv r
  have heqMoment :
      (fun n => soninAllPrimeEnergyMoment (v n) r) =ᶠ[atTop]
        (fun n => soninAllPrimeEnergyMoment (u n) r) := by
    filter_upwards [huv] with n hn
    rw [hn]
  simpa only [Function.comp_def] using Filter.Tendsto.congr' heqMoment hmoment

/-- Every intrinsic all-prime trace moment is continuous on positive apertures. -/
theorem continuousOn_soninAllPrimeEnergyMoment (r : ℕ) :
    ContinuousOn (fun a : ℝ => soninAllPrimeEnergyMoment a r) (Set.Ioi 0) := by
  intro a ha
  exact (continuousAt_soninAllPrimeEnergyMoment a ha r).continuousWithinAt

/-- The real zeroth intrinsic all-prime trace is continuous on positive apertures. -/
theorem continuousOn_re_soninAllPrimeEnergyMoment_zero :
    ContinuousOn (fun a : ℝ => (soninAllPrimeEnergyMoment a 0).re) (Set.Ioi 0) :=
  Complex.continuous_re.comp_continuousOn
    (continuousOn_soninAllPrimeEnergyMoment 0)

/-- The intrinsic all-prime zeroth trace hits every positive real target at a finite positive
aperture. -/
theorem exists_positive_aperture_soninAllPrimeEnergyMoment_zero_eq
    (T : ℝ) (hT : 0 < T) :
    ∃ a : ℝ, 0 < a ∧
      soninAllPrimeEnergyMoment a 0 = (T : ℂ) := by
  let M : ℝ := soninAllPrimeColumnWeightSqMass
  let R : ℝ := 128 * M
  let a₀ : ℝ := Real.sqrt (T / (2 * R))
  have hM : 0 < M := by
    simpa only [M] using soninAllPrimeColumnWeightSqMass_pos
  have hR : 0 < R := by
    dsimp only [R]
    positivity
  have hratio : 0 < T / (2 * R) := by positivity
  have ha₀ : 0 < a₀ := Real.sqrt_pos.2 hratio
  have ha₀sq : a₀ ^ 2 = T / (2 * R) := by
    dsimp only [a₀]
    exact Real.sq_sqrt hratio.le
  let f : ℝ → ℝ := fun a => (soninAllPrimeEnergyMoment a 0).re
  have hsmall : f a₀ < T := by
    have harea := re_soninAllPrimeEnergyMoment_zero_le_area a₀ ha₀
    have heq : (128 * a₀ ^ 2) * soninAllPrimeColumnWeightSqMass = T / 2 := by
      dsimp only [R, M] at hR ha₀sq
      rw [ha₀sq]
      field_simp [soninAllPrimeColumnWeightSqMass_pos.ne']
    dsimp only [f]
    rw [heq] at harea
    linarith
  have hlargeEventually : ∀ᶠ A : ℝ in atTop, T < f A := by
    simpa only [f] using
      tendsto_re_soninAllPrimeEnergyMoment_zero_atTop.eventually_gt_atTop T
  obtain ⟨A, hlarge, hA⟩ :=
    (hlargeEventually.and (eventually_gt_atTop a₀)).exists
  have hcont : ContinuousOn f (Set.Icc a₀ A) := by
    intro x hx
    change ContinuousWithinAt
      (fun a : ℝ => (soninAllPrimeEnergyMoment a 0).re) (Set.Icc a₀ A) x
    exact (continuousOn_re_soninAllPrimeEnergyMoment_zero x
      (ha₀.trans_le hx.1)).mono (fun y hy => ha₀.trans_le hy.1)
  have htarget : T ∈ Set.Icc (f a₀) (f A) :=
    ⟨hsmall.le, hlarge.le⟩
  obtain ⟨a, haIcc, haeq⟩ :=
    (intermediate_value_Icc hA.le hcont) htarget
  refine ⟨a, ha₀.trans_le haIcc.1, ?_⟩
  have haPos : 0 < a := ha₀.trans_le haIcc.1
  have haeq' : HilbertSchmidt.hsNormSq (soninAllPrimeResidualKernel a) = T := by
    simpa only [f, soninAllPrimeEnergyMoment, HilbertSchmidt.hsPow,
      trace_soninAllPrimeResidualEnergyKernel a haPos, Complex.ofReal_re] using haeq
  rw [soninAllPrimeEnergyMoment, HilbertSchmidt.hsPow,
    trace_soninAllPrimeResidualEnergyKernel a haPos]
  exact congrArg (fun x : ℝ => (x : ℂ)) haeq'

/-- The normalized prime--archimedean zeroth moment occurs at an exact positive aperture. -/
theorem exists_positive_aperture_soninAllPrimeEnergyMoment_zero_eq_normalizedPrimeArchMoment :
    ∃ a : ℝ, 0 < a ∧
      soninAllPrimeEnergyMoment a 0 = (normalizedPrimeArchMoment 0 : ℂ) := by
  exact exists_positive_aperture_soninAllPrimeEnergyMoment_zero_eq
    (normalizedPrimeArchMoment 0) normalizedPrimeArchMoment_zero_pos

end

end RHTower
