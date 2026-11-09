import GaloisForLFunctions.ArithmeticPositiveDuality.TwoPrimePhaseHull
import GaloisForLFunctions.ArithmeticPositiveDuality.SymmetricPhaseConvexity

/-!
# Parity detects the antipodal point of a simultaneous phase hull

The all-minus-one point belongs to the monomial phase hull exactly when every
integer relation among the ordinates has even coefficient sum. Translation by
that point makes the hull centrally symmetric, giving exact finite convex
representations of its strict radial contractions.
-/

noncomputable section
set_option autoImplicit false

open Set Topology
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

variable {ι : Type*}

/-- Every integer relation among the ordinates has even total coefficient. -/
def EvenOrdinateRelations (γ : ι → ℝ) : Prop :=
  ∀ n : ι →₀ ℤ, infiniteTorusCharacterDetuning n γ = 0 → Even (n.sum fun _ k => k)

/-- Nonconstant two-prime monomial phases, evaluated simultaneously. -/
def monomialPhaseSet (γ : ι → ℝ) : Set (ι → ℂ) :=
  {z | ∃ d : Fin 2 →₀ ℕ, d ≠ 0 ∧ (fun i => monomialPhase (γ i) d) = z}

private def circleCoordinates (x : ι → UnitAddCircle) : ι → ℂ :=
  fun i => fourier 1 (x i)

private theorem continuous_circleCoordinates : Continuous (circleCoordinates (ι := ι)) := by
  apply continuous_pi
  intro i
  exact (fourier 1).continuous.comp (continuous_apply i)

private theorem circleCoordinates_injective : Function.Injective (circleCoordinates (ι := ι)) := by
  intro x y h
  funext i
  apply AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)
  apply Subtype.ext
  simpa only [circleCoordinates, fourier_one] using congrFun h i

private theorem circleCoordinates_twoPrimePhase (γ : ι → ℝ) (d : Fin 2 →₀ ℕ) :
    circleCoordinates (twoPrimePhase (fun i => -γ i) d) = fun i => monomialPhase (γ i) d := by
  funext i
  have h := infiniteTorusFourier_screwPhase (Finsupp.single i 1)
    (fun i => -γ i) (monomialLog d)
  simp only [infiniteTorusFourier_single, infiniteTorusCharacterDetuning,
    Finsupp.sum_single_index, Int.cast_one, one_mul, Int.cast_zero, zero_mul] at h
  change fourier 1 (screwPhase (fun i => -γ i) (monomialLog d) i) = _
  rw [h]
  unfold monomialPhase
  congr 1
  push_cast
  ring

private def halfPeriodPoint : ι → UnitAddCircle := fun _ => ((1 / 2 : ℝ) : UnitAddCircle)

private theorem fourier_halfPeriod (n : ℤ) :
    fourier n ((1 / 2 : ℝ) : UnitAddCircle) = (-1 : ℂ) ^ n := by
  rw [fourier_coe_apply]
  have he : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((1 / 2 : ℝ) : ℂ) / (1 : ℝ)) =
      (n : ℂ) * ((Real.pi : ℂ) * Complex.I) := by push_cast; ring
  rw [he, Complex.exp_int_mul, Complex.exp_pi_mul_I]

private theorem infiniteTorusFourier_halfPeriod (n : ι →₀ ℤ) :
    infiniteTorusFourier n (halfPeriodPoint (ι := ι)) = (-1 : ℂ) ^ (n.sum fun _ k => k) := by
  classical
  simp only [infiniteTorusFourier, ContinuousMap.coe_mk, Finsupp.prod,
    halfPeriodPoint, fourier_halfPeriod, Finsupp.sum]
  rw [← Complex.exp_pi_mul_I]
  simp_rw [← Complex.exp_int_mul]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]

private theorem circleCoordinates_halfPeriod :
    circleCoordinates (halfPeriodPoint (ι := ι)) = fun _ => (-1 : ℂ) := by
  funext i
  exact (fourier_halfPeriod 1).trans (zpow_one _)

private theorem detuning_neg_ordinates (n : ι →₀ ℤ) (γ : ι → ℝ) :
    infiniteTorusCharacterDetuning n (fun i => -γ i) = -infiniteTorusCharacterDetuning n γ := by
  simp only [infiniteTorusCharacterDetuning, Finsupp.sum, mul_neg, Finset.sum_neg_distrib]

variable [Fintype ι]

/-- The simultaneous complex phase hull is the image of the additive relation hull. -/
theorem closure_monomialPhaseSet (γ : ι → ℝ) :
    closure (monomialPhaseSet γ) = circleCoordinates '' screwHull (fun i => -γ i) := by
  let D : Set (ι → UnitAddCircle) :=
    {x | ∃ d : Fin 2 →₀ ℕ, d ≠ 0 ∧ twoPrimePhase (fun i => -γ i) d = x}
  have himage : circleCoordinates '' D = monomialPhaseSet γ := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, ⟨d, hd, rfl⟩, rfl⟩
      exact ⟨d, hd, (circleCoordinates_twoPrimePhase γ d).symm⟩
    · rintro _ ⟨d, hd, rfl⟩
      exact ⟨twoPrimePhase (fun i => -γ i) d, ⟨d, hd, rfl⟩,
        circleCoordinates_twoPrimePhase γ d⟩
  have hD : closure D = screwHull (fun i => -γ i) := closure_nonconstant_twoPrimePhase _
  rw [← himage, ← hD]
  apply Set.Subset.antisymm
  · apply closure_minimal (image_mono subset_closure)
    rw [hD]
    exact ((isCompact_screwHull (fun i => -γ i)).image continuous_circleCoordinates).isClosed
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_closure_image continuous_circleCoordinates.continuousAt hx

/-- The all-minus-one phase is accessible precisely when no odd integer relation obstructs it. -/
theorem neg_one_mem_phaseHull_iff (γ : ι → ℝ) :
    (fun _ : ι => (-1 : ℂ)) ∈ closure (monomialPhaseSet γ) ↔ EvenOrdinateRelations γ := by
  rw [closure_monomialPhaseSet, ← circleCoordinates_halfPeriod]
  have himem : circleCoordinates halfPeriodPoint ∈
      circleCoordinates '' screwHull (fun i => -γ i) ↔
      halfPeriodPoint ∈ screwHull (fun i => -γ i) := by
    constructor
    · rintro ⟨x, hx, he⟩
      exact circleCoordinates_injective he ▸ hx
    · intro hx
      exact ⟨halfPeriodPoint, hx, rfl⟩
  rw [himem]
  rw [screwHull_eq_screwAnnihilator]
  change (∀ n : ι →₀ ℤ, infiniteTorusCharacterDetuning n (fun i => -γ i) = 0 →
    infiniteTorusFourier n halfPeriodPoint = 1) ↔ _
  simp only [detuning_neg_ordinates, neg_eq_zero, infiniteTorusFourier_halfPeriod]
  constructor
  · intro h n hn
    rcases Int.even_or_odd (n.sum fun _ k => k) with he | ho
    · exact he
    · have hc := h n hn
      rw [ho.neg_one_zpow] at hc
      norm_num at hc
  · intro h n hn
    exact (h n hn).neg_one_zpow

/-- Under the parity condition, the simultaneous phase hull is centrally symmetric. -/
theorem phaseHull_neg_mem (γ : ι → ℝ) (hγ : EvenOrdinateRelations γ)
    {z : ι → ℂ} (hz : z ∈ closure (monomialPhaseSet γ)) :
    -z ∈ closure (monomialPhaseSet γ) := by
  have hhalf := (neg_one_mem_phaseHull_iff γ).mpr hγ
  rw [closure_monomialPhaseSet] at hz hhalf ⊢
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨y, hy, he⟩ := hhalf
  refine ⟨x + y, add_mem_screwHull hx hy, ?_⟩
  funext i
  have hi := congrFun he i
  change fourier 1 (y i) = -1 at hi
  change fourier 1 (x i + y i) = -fourier 1 (x i)
  have hm := infiniteTorusFourier_add_point (Finsupp.single i 1) x y
  simp only [infiniteTorusFourier_single, Pi.add_apply] at hm
  rw [hm, hi]
  simp

/-- Every strict radial contraction of the antipodal phase has an exact finite
representation using nonconstant two-prime monomials. -/
theorem neg_smul_one_mem_phaseConvexHull (γ : ι → ℝ) (hγ : EvenOrdinateRelations γ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (fun _ : ι => (-(r : ℂ))) ∈ convexHull ℝ (monomialPhaseSet γ) := by
  have hne : (monomialPhaseSet γ).Nonempty := by
    refine ⟨fun i => monomialPhase (γ i) (Finsupp.single 0 1), Finsupp.single 0 1, ?_, rfl⟩
    simp
  have h := smul_mem_convexHull_of_symmetric_closure hne
    (fun _ hz => phaseHull_neg_mem γ hγ hz) ((neg_one_mem_phaseHull_iff γ).mpr hγ) hr0 hr1
  have he : r • (fun _ : ι => (-1 : ℂ)) = (fun _ : ι => -(r : ℂ)) := by
    funext i
    simp only [Pi.smul_apply, Complex.real_smul, mul_neg, mul_one]
  rwa [he] at h

#print axioms neg_one_mem_phaseHull_iff
#print axioms neg_smul_one_mem_phaseConvexHull

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
