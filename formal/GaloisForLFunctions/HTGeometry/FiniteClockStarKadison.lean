import GaloisForLFunctions.HTGeometry.FiniteClockResolutionVariance

/-!
# Star-Kadison observability for arbitrary finite-clock operators

The usual finite-clock defect in this corpus is written with `X * X` and therefore yields a
positive observability energy only when `X` is self-adjoint.  Quantum channels and conditional
expectations instead use the star-Kadison defect

`Phi(X† X) - Phi(X)† Phi(X)`.

For a finite-period isometric clock and a stationary state, its value is exactly the squared norm
of the observable vector erased by the stationary projection.  Thus self-adjointness of `X` is not
part of the observability structure.  The result applies equally to transition operators and is
static: no temporal evolution is introduced.
-/

namespace HTGeometry

noncomputable section

open scoped BigOperators

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The star-Kadison defect of the finite cyclic observable twirl.  Unlike the earlier squared
defect, this is the correct conditional variance for an arbitrary, not necessarily self-adjoint,
operator. -/
def finiteCyclicObservableTwirlStarKadisonDefect
    (U X : E →L[𝕜] E) (N : ℕ) : E →L[𝕜] E :=
  finiteCyclicObservableTwirl U (X.adjoint * X) N -
    (finiteCyclicObservableTwirl U X N).adjoint *
      finiteCyclicObservableTwirl U X N

/-- On self-adjoint observables the star-Kadison defect is exactly the existing finite-clock
defect, so the new interface strictly extends rather than duplicates the old one. -/
theorem finiteCyclicObservableTwirlStarKadisonDefect_eq_of_isSelfAdjoint
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    (hX : IsSelfAdjoint X) :
    finiteCyclicObservableTwirlStarKadisonDefect U X N =
      finiteCyclicObservableTwirlKadisonDefect U X N := by
  have hXadj : X.adjoint = X := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using hX.star_eq
  have hPhiAdj :
      (finiteCyclicObservableTwirl U X N).adjoint =
        finiteCyclicObservableTwirl U X N := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (finiteCyclicObservableTwirl_isSelfAdjoint
        U X N hN hadjoint_mul hperiod hX).star_eq
  rw [finiteCyclicObservableTwirlStarKadisonDefect,
    finiteCyclicObservableTwirlKadisonDefect, hXadj, hPhiAdj]

/-- **Arbitrary-operator finite-clock erased-information law.**  On a stationary state, the
star-Kadison value is the exact squared norm rejected by the clock's stationary projection.  No
self-adjointness premise on `X` is needed. -/
theorem re_inner_finiteCyclicObservableTwirlStarKadisonDefect_eq_erasedNormSq
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    {ψ : E} (hψ : U ψ = ψ) :
    RCLike.re
        (inner 𝕜 ψ
          (finiteCyclicObservableTwirlStarKadisonDefect U X N ψ)) =
      ‖(1 - finiteCyclicGaugeAverage U N) (X ψ)‖ ^ 2 := by
  let Phi : E →L[𝕜] E := finiteCyclicObservableTwirl U X N
  have hUadj := adjoint_eq_pow_pred_of_periodic_isometry
    U N hN hadjoint_mul hperiod
  have hpowfix : ∀ k : ℕ, (U ^ k) ψ = ψ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, mul_apply_eq_comp, hψ, ih]
  have hψleft : U.adjoint ψ = ψ := by
    rw [hUadj, hpowfix]
  have hfirst := inner_finiteCyclicObservableTwirl_of_fixed
    U (X.adjoint * X) N hN hψleft hψ
  have hXnorm :
      RCLike.re (inner 𝕜 ψ ((X.adjoint * X) ψ)) = ‖X ψ‖ ^ 2 := by
    simpa only [mul_apply_eq_comp] using
      (X.apply_norm_sq_eq_inner_adjoint_right ψ).symm
  have hPhinorm :
      RCLike.re (inner 𝕜 ψ ((Phi.adjoint * Phi) ψ)) = ‖Phi ψ‖ ^ 2 := by
    simpa only [mul_apply_eq_comp] using
      (Phi.apply_norm_sq_eq_inner_adjoint_right ψ).symm
  have hPhiApply :
      Phi ψ = finiteCyclicGaugeAverage U N (X ψ) := by
    exact finiteCyclicObservableTwirl_apply_of_fixed U X N hψ
  have hsplit :=
    norm_finiteCyclicGaugeAverage_sq_add_complement_sq_of_periodic_isometry
      U N hN hadjoint_mul hperiod (X ψ)
  have hsplit' :
      ‖finiteCyclicGaugeAverage U N (X ψ)‖ ^ 2 +
          ‖X ψ - finiteCyclicGaugeAverage U N (X ψ)‖ ^ 2 =
        ‖X ψ‖ ^ 2 := by
    simpa only [_root_.sub_apply, one_apply_eq_self] using hsplit
  rw [finiteCyclicObservableTwirlStarKadisonDefect]
  change RCLike.re
      (inner 𝕜 ψ
        ((finiteCyclicObservableTwirl U (X.adjoint * X) N -
          Phi.adjoint * Phi) ψ)) = _
  simp only [_root_.sub_apply, one_apply_eq_self,
    inner_sub_right, map_sub]
  rw [hfirst, hXnorm, hPhinorm, hPhiApply]
  linarith [hsplit']

/-- The retained finite-clock value and the arbitrary-operator star-Kadison loss form an exact
energy partition. -/
theorem finiteClock_starObservableValue_energy_partition
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    {ψ : E} (hψ : U ψ = ψ) :
    ‖finiteCyclicObservableTwirl U X N ψ‖ ^ 2 +
        RCLike.re
          (inner 𝕜 ψ
            (finiteCyclicObservableTwirlStarKadisonDefect U X N ψ)) =
      ‖X ψ‖ ^ 2 := by
  have hsplit :=
    norm_finiteCyclicGaugeAverage_sq_add_complement_sq_of_periodic_isometry
      U N hN hadjoint_mul hperiod (X ψ)
  rw [← finiteCyclicObservableTwirl_apply_of_fixed U X N hψ,
    ← re_inner_finiteCyclicObservableTwirlStarKadisonDefect_eq_erasedNormSq
      U X N hN hadjoint_mul hperiod hψ] at hsplit
  exact hsplit

/-- The star-Kadison observability value is nonnegative for every operator. -/
theorem re_inner_finiteCyclicObservableTwirlStarKadisonDefect_nonneg
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    {ψ : E} (hψ : U ψ = ψ) :
    0 ≤ RCLike.re
      (inner 𝕜 ψ
        (finiteCyclicObservableTwirlStarKadisonDefect U X N ψ)) := by
  rw [re_inner_finiteCyclicObservableTwirlStarKadisonDefect_eq_erasedNormSq
    U X N hN hadjoint_mul hperiod hψ]
  positivity

/-- Zero star-Kadison loss is equivalent to exact retention of the observed vector. -/
theorem re_inner_finiteCyclicObservableTwirlStarKadisonDefect_eq_zero_iff_twirl_fixed
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    {ψ : E} (hψ : U ψ = ψ) :
    RCLike.re
        (inner 𝕜 ψ
          (finiteCyclicObservableTwirlStarKadisonDefect U X N ψ)) = 0 ↔
      finiteCyclicObservableTwirl U X N ψ = X ψ := by
  rw [re_inner_finiteCyclicObservableTwirlStarKadisonDefect_eq_erasedNormSq
    U X N hN hadjoint_mul hperiod hψ]
  constructor
  · intro hz
    have hresidual : (1 - finiteCyclicGaugeAverage U N) (X ψ) = 0 := by
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
    rw [finiteCyclicObservableTwirl_apply_of_fixed U X N hψ]
    have hxP : X ψ = finiteCyclicGaugeAverage U N (X ψ) := by
      apply sub_eq_zero.mp
      simpa only [_root_.sub_apply, one_apply_eq_self] using hresidual
    exact hxP.symm
  · intro hfixed
    rw [finiteCyclicObservableTwirl_apply_of_fixed U X N hψ] at hfixed
    simp [hfixed]

/-- Zero star-Kadison loss discharges, and is characterized by, physicality of the observed
vector for the finite clock constraint. -/
theorem re_inner_finiteCyclicObservableTwirlStarKadisonDefect_eq_zero_iff_physical
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    {ψ : E} (hψ : U ψ = ψ) :
    RCLike.re
        (inner 𝕜 ψ
          (finiteCyclicObservableTwirlStarKadisonDefect U X N ψ)) = 0 ↔
      GaloisForLFunctions.PhysicalState (U - 1).toLinearMap (X ψ) := by
  rw [re_inner_finiteCyclicObservableTwirlStarKadisonDefect_eq_zero_iff_twirl_fixed
      U X N hN hadjoint_mul hperiod hψ,
    finiteCyclicObservableTwirl_apply_of_fixed U X N hψ]
  exact (physicalState_iff_finiteCyclicGaugeAverage_fixed
    U N hN hperiod (X ψ)).symm

/-- Zero star-Kadison loss is equivalent to the clock-observable commutator annihilating the
stationary state, for arbitrary `X`. -/
theorem re_inner_finiteCyclicObservableTwirlStarKadisonDefect_eq_zero_iff_commutator
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    {ψ : E} (hψ : U ψ = ψ) :
    RCLike.re
        (inner 𝕜 ψ
          (finiteCyclicObservableTwirlStarKadisonDefect U X N ψ)) = 0 ↔
      (U * X - X * U) ψ = 0 := by
  rw [re_inner_finiteCyclicObservableTwirlStarKadisonDefect_eq_zero_iff_physical
    U X N hN hadjoint_mul hperiod hψ]
  rw [GaloisForLFunctions.PhysicalState]
  change (U - 1) (X ψ) = 0 ↔ (U * X - X * U) ψ = 0
  simp only [_root_.sub_apply, mul_apply_eq_comp,
    one_apply_eq_self, hψ]

/-- **Arbitrary-operator law of total finite-clock observability variance.**  Refining a power
subclock to the full clock adds exactly the squared norm of the newly erased resolution layer.
The self-adjointness hypothesis required by the earlier squared-defect theorem is absent. -/
theorem finiteClockResolution_starObservabilityVariance
    (U X : E →L[𝕜] E) (d M : ℕ) (hd : d ≠ 0) (hM : M ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ (d * M) = 1)
    {ψ : E} (hψ : U ψ = ψ) :
    RCLike.re
        (inner 𝕜 ψ
          (finiteCyclicObservableTwirlStarKadisonDefect U X (d * M) ψ)) =
      RCLike.re
          (inner 𝕜 ψ
            (finiteCyclicObservableTwirlStarKadisonDefect (U ^ d) X M ψ)) +
        ‖(finiteCyclicGaugeAverage (U ^ d) M -
          finiteCyclicGaugeAverage U (d * M)) (X ψ)‖ ^ 2 := by
  have hfullN : d * M ≠ 0 := Nat.mul_ne_zero hd hM
  have hsubadjoint : (U ^ d).adjoint * U ^ d = 1 :=
    adjoint_pow_mul_pow_eq_one_of_adjoint_mul_self U d hadjoint_mul
  have hsubperiod : (U ^ d) ^ M = 1 := by
    rw [← pow_mul]
    exact hperiod
  have hsubψ : (U ^ d) ψ = ψ :=
    pow_apply_eq_self_of_apply_eq_self U hψ d
  rw [re_inner_finiteCyclicObservableTwirlStarKadisonDefect_eq_erasedNormSq
      U X (d * M) hfullN hadjoint_mul hperiod hψ,
    re_inner_finiteCyclicObservableTwirlStarKadisonDefect_eq_erasedNormSq
      (U ^ d) X M hM hsubadjoint hsubperiod hsubψ]
  exact finiteClockResolution_energy_partition
    U d M hM hadjoint_mul hperiod (X ψ)

section FiniteFamily

variable {ι : Type*} [Fintype ι]

/-- Total star-Kadison observability loss for a finite family of clocks.  The observed operator
may be non-self-adjoint. -/
def finiteClockFamilyStarObservabilityEnergy
    (U : ι → E →L[𝕜] E) (X : E →L[𝕜] E) (N : ι → ℕ) (ψ : E) : ℝ :=
  ∑ i, RCLike.re
    (inner 𝕜 ψ
      (finiteCyclicObservableTwirlStarKadisonDefect (U i) X (N i) ψ))

/-- The family star energy is exactly the sum of the vector energies erased by its clocks. -/
theorem finiteClockFamilyStarObservabilityEnergy_eq_sum_erasedNormSq
    (U : ι → E →L[𝕜] E) (X : E →L[𝕜] E) (N : ι → ℕ)
    (hN : ∀ i, N i ≠ 0)
    (hadjoint_mul : ∀ i, (U i).adjoint * U i = 1)
    (hperiod : ∀ i, U i ^ N i = 1)
    {ψ : E} (hψ : ∀ i, U i ψ = ψ) :
    finiteClockFamilyStarObservabilityEnergy U X N ψ =
      ∑ i, ‖(1 - finiteCyclicGaugeAverage (U i) (N i)) (X ψ)‖ ^ 2 := by
  unfold finiteClockFamilyStarObservabilityEnergy
  apply Finset.sum_congr rfl
  intro i hi
  exact re_inner_finiteCyclicObservableTwirlStarKadisonDefect_eq_erasedNormSq
    (U i) X (N i) (hN i) (hadjoint_mul i) (hperiod i) (hψ i)

/-- Total star-Kadison observability loss is nonnegative without self-adjointness of `X`. -/
theorem finiteClockFamilyStarObservabilityEnergy_nonneg
    (U : ι → E →L[𝕜] E) (X : E →L[𝕜] E) (N : ι → ℕ)
    (hN : ∀ i, N i ≠ 0)
    (hadjoint_mul : ∀ i, (U i).adjoint * U i = 1)
    (hperiod : ∀ i, U i ^ N i = 1)
    {ψ : E} (hψ : ∀ i, U i ψ = ψ) :
    0 ≤ finiteClockFamilyStarObservabilityEnergy U X N ψ := by
  unfold finiteClockFamilyStarObservabilityEnergy
  exact Finset.sum_nonneg fun i hi =>
    re_inner_finiteCyclicObservableTwirlStarKadisonDefect_nonneg
      (U i) X (N i) (hN i) (hadjoint_mul i) (hperiod i) (hψ i)

/-- Zero family star energy is equivalent to physicality of the observed vector for every clock
constraint. -/
theorem finiteClockFamilyStarObservabilityEnergy_eq_zero_iff_forall_physical
    (U : ι → E →L[𝕜] E) (X : E →L[𝕜] E) (N : ι → ℕ)
    (hN : ∀ i, N i ≠ 0)
    (hadjoint_mul : ∀ i, (U i).adjoint * U i = 1)
    (hperiod : ∀ i, U i ^ N i = 1)
    {ψ : E} (hψ : ∀ i, U i ψ = ψ) :
    finiteClockFamilyStarObservabilityEnergy U X N ψ = 0 ↔
      ∀ i, GaloisForLFunctions.PhysicalState (U i - 1).toLinearMap (X ψ) := by
  unfold finiteClockFamilyStarObservabilityEnergy
  have hterm : ∀ i,
      0 ≤ RCLike.re
        (inner 𝕜 ψ
          (finiteCyclicObservableTwirlStarKadisonDefect (U i) X (N i) ψ)) :=
    fun i => re_inner_finiteCyclicObservableTwirlStarKadisonDefect_nonneg
      (U i) X (N i) (hN i) (hadjoint_mul i) (hperiod i) (hψ i)
  constructor
  · intro hzero i
    have hi : RCLike.re
        (inner 𝕜 ψ
          (finiteCyclicObservableTwirlStarKadisonDefect (U i) X (N i) ψ)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm j)).mp
        hzero i (Finset.mem_univ i)
    exact
      (re_inner_finiteCyclicObservableTwirlStarKadisonDefect_eq_zero_iff_physical
        (U i) X (N i) (hN i) (hadjoint_mul i) (hperiod i) (hψ i)).mp hi
  · intro hphysical
    apply Finset.sum_eq_zero
    intro i hi
    exact
      (re_inner_finiteCyclicObservableTwirlStarKadisonDefect_eq_zero_iff_physical
        (U i) X (N i) (hN i) (hadjoint_mul i) (hperiod i) (hψ i)).mpr
          (hphysical i)

/-- The zero set of arbitrary-operator clock-family loss is exactly the physical kernel of the
existing finite quantum master constraint. -/
theorem finiteClockFamilyStarObservabilityEnergy_eq_zero_iff_masterPhysical
    (U : ι → E →L[𝕜] E) (X : E →L[𝕜] E) (N : ι → ℕ)
    (hN : ∀ i, N i ≠ 0)
    (hadjoint_mul : ∀ i, (U i).adjoint * U i = 1)
    (hperiod : ∀ i, U i ^ N i = 1)
    {ψ : E} (hψ : ∀ i, U i ψ = ψ) :
    finiteClockFamilyStarObservabilityEnergy U X N ψ = 0 ↔
      GaloisForLFunctions.PhysicalState
        (finiteQuantumMasterConstraint (fun i => U i - 1)).toLinearMap (X ψ) := by
  rw [finiteClockFamilyStarObservabilityEnergy_eq_zero_iff_forall_physical
    U X N hN hadjoint_mul hperiod hψ]
  exact (physicalState_finiteQuantumMasterConstraint_iff
    (fun i => U i - 1) (X ψ)).symm

/-- Zero arbitrary-operator family loss supplies the physicality premise required by the master
constraint Ward-value theorem. -/
theorem finiteClockFamilyStar_zeroEnergy_WardValue_eq_zero
    (U : ι → E →L[𝕜] E) (X A : E →L[𝕜] E) (N : ι → ℕ)
    (hN : ∀ i, N i ≠ 0)
    (hadjoint_mul : ∀ i, (U i).adjoint * U i = 1)
    (hperiod : ∀ i, U i ^ N i = 1)
    {ψ : E} (hψ : ∀ i, U i ψ = ψ)
    (hzero : finiteClockFamilyStarObservabilityEnergy U X N ψ = 0) :
    inner 𝕜 (X ψ)
      (finiteQuantumMasterConstraint (fun i => U i - 1) (A (X ψ))) = 0 := by
  apply finiteQuantumMasterConstraint_WardValue_eq_zero (fun i => U i - 1) A
  exact (finiteClockFamilyStarObservabilityEnergy_eq_zero_iff_forall_physical
    U X N hN hadjoint_mul hperiod hψ).mp hzero

end FiniteFamily

end

end HTGeometry
