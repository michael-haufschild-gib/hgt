import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelCountableL2Dominance

/-!
# Phase-fiber rigidity for physical theta--Abel apertures

Finite distinct exponential profiles are coefficient-faithful in compact-aperture `L²`. Therefore
collisions of their discrete height phases cannot cancel a maximal spectral fiber. Combined with
countable `L²` dominance, this removes the phase-injectivity escape completely.
-/

open Complex Filter Topology MeasureTheory Set
open scoped BigOperators ENNReal NNReal

attribute [local instance] Measure.Subtype.measureSpace

namespace RHTower

noncomputable section

def gammaJetSlotNodeOneEquiv (r : ℕ) :
    Fin (∑ _i : Fin r, 1) ≃ Fin r := by
  let node := GaloisForLFunctions.gammaJetSlotNode (fun _i : Fin r => 1)
  apply Equiv.ofBijective node
  exact (Fintype.bijective_iff_injective_and_card node).2
    ⟨gammaJetSlotNode_one_injective, by simp⟩

@[simp] theorem gammaJetSlotNodeOneEquiv_apply {r : ℕ}
    (k : Fin (∑ _i : Fin r, 1)) :
    gammaJetSlotNodeOneEquiv r k =
      GaloisForLFunctions.gammaJetSlotNode (fun _i : Fin r => 1) k := rfl

/-- Coordinate observability for a plain finite family of distinct exponential profiles. -/
theorem exists_plainExponentialInterval_coordinate_observability
    {r : ℕ} {z : Fin r → ℂ} (hzinj : Function.Injective z)
    {A : ℝ} (hA : 0 < A) (j : Fin r) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Fin r → ℂ,
      ‖x j‖ ^ 2 ≤ C * ∫ u : ℝ in Set.Icc 0 A,
        ‖∑ i, x i * Complex.exp (-z i * (u : ℂ))‖ ^ 2 := by
  let e := gammaJetSlotNodeOneEquiv r
  let jslot := e.symm j
  have hneginj : Function.Injective (fun i => -z i) :=
    fun i q h => hzinj (neg_injective h)
  obtain ⟨C, hC, hobs⟩ :=
    exists_exponentialPolynomialInterval_coordinate_observability
      hneginj (fun _i : Fin r => 1) hA jslot
  refine ⟨C, hC, fun x => ?_⟩
  let xslot : Fin (∑ _i : Fin r, 1) → ℂ := fun k => x (e k)
  have h := hobs xslot
  have hxj : xslot jslot = x j := by simp [xslot, jslot]
  rw [hxj] at h
  apply h.trans_eq
  congr 1
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    apply congrArg (fun w : ℂ => ‖w‖ ^ 2)
    rw [exponentialPolynomialIntervalCombination]
    simp only [xslot, exponentialPolynomialRealFeature, exponentialPolynomialMode,
      gammaJetSlotOrder_one, pow_zero, one_mul]
    exact Equiv.sum_comp e (fun i => x i * Complex.exp (-z i * (u : ℂ)))

/-- A finite distinct exponential profile packet is coefficient-faithful in aperture `L²`. -/
theorem plainExponentialApertureL2_relation_coefficients_zero
    {r : ℕ} {z : Fin r → ℂ} (hzinj : Function.Injective z)
    {A : ℝ} (hA : 0 < A) (x : Fin r → ℂ)
    (hrel : ∑ i, x i • xiPhysicalThetaAbelModeApertureL2 A (z i) = 0) :
    x = 0 := by
  let F : C(ClosedInterval 0 A, ℂ) :=
    ∑ i, x i • xiPhysicalThetaAbelModeApertureContinuous A (z i)
  have hmap : ContinuousMap.toLp 2 (volume : Measure (ClosedInterval 0 A)) ℂ F =
      ∑ i, x i • xiPhysicalThetaAbelModeApertureL2 A (z i) := by
    simp only [F, map_sum, map_smul, xiPhysicalThetaAbelModeApertureL2]
  have hzeroLp : ContinuousMap.toLp 2
      (volume : Measure (ClosedInterval 0 A)) ℂ F = 0 := hmap.trans hrel
  have hcoe := ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
    (μ := (volume : Measure (ClosedInterval 0 A))) F
  have hzeroCoe :
      ((ContinuousMap.toLp 2 (volume : Measure (ClosedInterval 0 A)) ℂ F :
        Lp ℂ 2 (volume : Measure (ClosedInterval 0 A))) :
          ClosedInterval 0 A → ℂ) =ᵐ[volume] fun _ => 0 := by
    rw [hzeroLp]
    exact Lp.coeFn_zero ℂ 2 (volume : Measure (ClosedInterval 0 A))
  have hcombo : ∀ᵐ u : ClosedInterval 0 A ∂volume,
      (∑ i, x i * Complex.exp (-z i * ((u : ℝ) : ℂ))) = 0 := by
    filter_upwards [hcoe, hzeroCoe] with u hu hzero
    rw [hu] at hzero
    simpa [F, xiPhysicalThetaAbelModeApertureContinuous, Pi.smul_apply,
      smul_eq_mul] using hzero
  have henergySubtype :
      (∫ u : ClosedInterval 0 A,
        ‖∑ i, x i * Complex.exp (-z i * (((u : ℝ) : ℂ)))‖ ^ 2 ∂volume) = 0 := by
    calc
      (∫ u : ClosedInterval 0 A,
          ‖∑ i, x i * Complex.exp (-z i * (((u : ℝ) : ℂ)))‖ ^ 2 ∂volume) =
          ∫ _u : ClosedInterval 0 A, (0 : ℝ) ∂volume := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [hcombo] with u hu
            rw [hu]
            simp
      _ = 0 := by simp
  have henergy :
      (∫ u : ℝ in Set.Icc 0 A,
        ‖∑ i, x i * Complex.exp (-z i * (u : ℂ))‖ ^ 2) = 0 := by
    rw [← MeasureTheory.integral_subtype measurableSet_Icc]
    exact henergySubtype
  funext j
  obtain ⟨C, hC, hobs⟩ :=
    exists_plainExponentialInterval_coordinate_observability hzinj hA j
  have hj := hobs x
  rw [henergy, mul_zero] at hj
  have hsquare : ‖x j‖ ^ 2 = 0 := le_antisymm hj (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsquare)

/-- Coefficient faithfulness transported to an arbitrary finite index type. -/
theorem finiteType_plainExponentialApertureL2_relation_coefficients_zero
    {ι : Type*} [Fintype ι] {z : ι → ℂ} (hzinj : Function.Injective z)
    {A : ℝ} (hA : 0 < A) (x : ι → ℂ)
    (hrel : ∑ i, x i • xiPhysicalThetaAbelModeApertureL2 A (z i) = 0) :
    x = 0 := by
  let e := Fintype.equivFin ι
  let zFin : Fin (Fintype.card ι) → ℂ := fun q => z (e.symm q)
  let xFin : Fin (Fintype.card ι) → ℂ := fun q => x (e.symm q)
  have hzinjFin : Function.Injective zFin := fun q₁ q₂ h => by
    apply e.symm.injective
    exact hzinj h
  have hrelFin :
      ∑ q, xFin q • xiPhysicalThetaAbelModeApertureL2 A (zFin q) = 0 := by
    have hsum := Fintype.sum_equiv e
      (fun i => x i • xiPhysicalThetaAbelModeApertureL2 A (z i))
      (fun q => xFin q • xiPhysicalThetaAbelModeApertureL2 A (zFin q))
      (fun i => by simp [xFin, zFin, e])
    exact hsum.symm.trans hrel
  have hzeroFin := plainExponentialApertureL2_relation_coefficients_zero
    hzinjFin hA xFin hrelFin
  funext i
  have hi := congrFun hzeroFin (e i)
  simpa [xFin, e] using hi

/-- Distinct aperture exponents prevent cancellation inside every finite phase fiber, even when
several discrete height phases collide. -/
theorem finiteExponentialVectorFiberCoefficient_thetaAbel_ne_zero
    {ι : Type*} (D : Finset ι) (z coeff : ι → ℂ) (phase : ι → ℂ)
    {A : ℝ} (hA : 0 < A) (hzinj : Set.InjOn z D)
    {u : ℂ} {j : ι} (hj : j ∈ D) (hphasej : phase j = u)
    (hcoeff : coeff j ≠ 0) :
    finiteExponentialVectorFiberCoefficient D
      (fun i => coeff i • xiPhysicalThetaAbelModeApertureL2 A (z i)) phase u ≠ 0 := by
  classical
  let S := D.filter (fun i => phase i = u)
  have hjS : j ∈ S := by simp [S, hj, hphasej]
  let zS : (↥S) → ℂ := fun i => z i
  let coeffS : (↥S) → ℂ := fun i => coeff i
  have hzinjS : Function.Injective zS := by
    intro i q hiq
    apply Subtype.ext
    exact hzinj (Finset.mem_filter.mp i.2).1 (Finset.mem_filter.mp q.2).1 hiq
  intro hzero
  have hrel :
      ∑ i : ↥S, coeffS i • xiPhysicalThetaAbelModeApertureL2 A (zS i) = 0 := by
    simp only [coeffS, zS]
    rw [Finset.univ_eq_attach,
      Finset.sum_attach S
        (fun i => coeff i • xiPhysicalThetaAbelModeApertureL2 A (z i))]
    simpa [S, finiteExponentialVectorFiberCoefficient,
      Finset.sum_filter] using hzero
  have hcoeffZero := finiteType_plainExponentialApertureL2_relation_coefficients_zero
    hzinjS hA coeffS hrel
  have hjzero := congrFun hcoeffZero (⟨j, hjS⟩ : ↥S)
  exact hcoeff (by simpa [coeffS] using hjzero)

/-- Distinct dominant exponents make every maximal phase-fiber cancellation impossible. A selected
nonzero supercritical theta--Abel mode therefore survives every norm-summable strictly
subdominant countable tail without any phase-injectivity premise. -/
theorem not_tendsto_xiPhysicalThetaAbelCountableL2PhysicalScale_zero_of_distinctModes
    {ι : Type*} (A c beta : ℝ) (z a : ι → ℂ)
    (hA : 0 < A) (hc : 0 < c)
    (hsum : Summable (fun i => ‖xiPhysicalThetaAbelCountableModeVector A c z a i‖))
    (D : Finset ι)
    (hdom : ∀ i ∈ D, (z i).re = beta)
    (hsub : ∀ i ∉ D, (z i).re < beta)
    (hzinj : Set.InjOn z D)
    (j : ι) (hj : j ∈ D) (ha : a j ≠ 0) (hznegOne : z j ≠ -1)
    (hbeta0 : beta < 0) (hwall : -(1 / 2 : ℝ) < beta) :
    ¬ Tendsto
      (fun n : ℕ =>
        Complex.exp ((beta + 1 / 2 : ℝ) : ℂ) ^ n •
          xiPhysicalThetaAbelCountableNormalizedL2Response A c beta z a n)
      atTop (nhds 0) := by
  let phase : ι → ℂ :=
    fun i => Complex.exp (z i) / (Real.exp beta : ℂ)
  let coeff : ι → ℂ := fun i =>
    a i * xiPhysicalLogWindowModeMultiplier c (z i) * ((z i + 1) / z i)
  have hzjre : (z j).re < 0 := by rw [hdom j hj]; exact hbeta0
  have hzj : z j ≠ 0 := by
    intro h
    rw [h] at hzjre
    simp at hzjre
  have hnum : z j + 1 ≠ 0 := by
    intro h
    apply hznegOne
    calc
      z j = (z j + 1) - 1 := by ring
      _ = -1 := by rw [h]; ring
  have hcoeff : coeff j ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero ha
      (xiPhysicalLogWindowModeMultiplier_ne_zero hc hzjre)) (div_ne_zero hnum hzj)
  have hjfiber := finiteExponentialVectorFiberCoefficient_thetaAbel_ne_zero
    D z coeff phase hA hzinj hj rfl hcoeff
  have hfiber : ∃ u ∈ D.image phase,
      finiteExponentialVectorFiberCoefficient D
        (xiPhysicalThetaAbelCountableModeVector A c z a) phase u ≠ 0 := by
    refine ⟨phase j, Finset.mem_image_of_mem phase hj, ?_⟩
    change finiteExponentialVectorFiberCoefficient D
      (fun i => (a i * xiPhysicalLogWindowModeMultiplier c (z i) *
        ((z i + 1) / z i)) • xiPhysicalThetaAbelModeApertureL2 A (z i))
      phase (phase j) ≠ 0
    exact hjfiber
  exact not_tendsto_xiPhysicalThetaAbelCountableL2PhysicalScale_zero_of_dominantFinset
    A c beta z a hsum D hdom hsub hfiber hwall

end

end RHTower
