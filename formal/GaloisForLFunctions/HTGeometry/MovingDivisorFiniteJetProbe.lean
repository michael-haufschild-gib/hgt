import GaloisForLFunctions.HTGeometry.MovingDivisorFiniteJetSubmersion
import GaloisForLFunctions.HTGeometry.MovingCanonicalFiniteJetProbe

/-!
# The universal finite parameter probe of a moving divisor

The initial block of parameters of a moving divisor spans every finite complex jet packet, and the
actual differential-jet terms of the carrier have the corresponding finite chart derivative.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology Filter
open scoped ENNReal

noncomputable section
set_option maxHeartbeats 2000000

namespace MovingDivisor

/-- Exact location-jet control by the initial finite block of the moving canonical divisor. -/
def finiteLocationJetLinearMap (Dv : MovingDivisor)
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (n : ι → ℕ) (θ : BoundedRealSequence) :
    (Fin (movingCanonicalLocationProbeCard n) → ℝ) →ₗ[ℝ]
      ((Σ i, Fin (n i)) → ℂ) :=
  (movingPoleLocationJetRealLinearCombination x n
      (fun a : Fin (movingCanonicalLocationProbeCard n) =>
        Dv.zeroAt θ a.1)).comp
    (Finsupp.linearEquivFunOnFinite ℝ ℝ
      (Fin (movingCanonicalLocationProbeCard n))).symm.toLinearMap

/-- The explicit initial finite canonical block spans every finite complex location-jet packet. -/
theorem finiteLocationJetLinearMap_surjective (Dv : MovingDivisor)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence) :
    Function.Surjective
      (Dv.finiteLocationJetLinearMap x n θ) := by
  let t : Fin (movingCanonicalLocationProbeCard n) → ℝ :=
    fun a => Dv.zeroAt θ a.1
  have hloc : Function.Surjective
      (movingPoleLocationJetRealLinearCombination x n t) := by
    have ht : Function.Injective t :=
      (Dv.injective (θ : ℕ → ℝ)).comp Fin.val_injective
    have ht0 : ∀ a, t a ≠ 0 :=
      fun a => ne_of_gt (Dv.zeroAt_pos θ a.1)
    have hcard : inverseSquareCauchyProbeCard (fun i => n i + 1) ≤
        Fintype.card (Fin (movingCanonicalLocationProbeCard n)) := by
      rw [Fintype.card_fin, movingCanonicalLocationProbeCard]
    exact movingPoleLocationJetRealLinearCombination_surjective_of_card
      x hx hupper n t ht ht0 hcard
  have hequiv : Function.Surjective
      (Finsupp.linearEquivFunOnFinite ℝ ℝ
        (Fin (movingCanonicalLocationProbeCard n))).symm :=
    (Finsupp.linearEquivFunOnFinite ℝ ℝ
      (Fin (movingCanonicalLocationProbeCard n))).symm.surjective
  change Function.Surjective
    ((movingPoleLocationJetRealLinearCombination x n t).comp
      (Finsupp.linearEquivFunOnFinite ℝ ℝ
        (Fin (movingCanonicalLocationProbeCard n))).symm.toLinearMap)
  exact hloc.comp hequiv

/-- Positive diagonal speed map on the universal initial finite canonical probe. -/
def finiteSpeedLinearMap (Dv : MovingDivisor)
    {ι : Type*} [Fintype ι] (n : ι → ℕ)
    (θ : BoundedRealSequence) :
    (Fin (movingCanonicalLocationProbeCard n) → ℝ) →ₗ[ℝ]
      (Fin (movingCanonicalLocationProbeCard n) → ℝ) where
  toFun p a := Dv.coordinateSpeed a.1 (θ a.1) * p a
  map_add' p q := by
    funext a
    simp only [Pi.add_apply]
    ring
  map_smul' r p := by
    funext a
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

theorem finiteSpeedLinearMap_surjective (Dv : MovingDivisor)
    {ι : Type*} [Fintype ι] (n : ι → ℕ)
    (θ : BoundedRealSequence) :
    Function.Surjective (Dv.finiteSpeedLinearMap n θ) := by
  intro y
  refine ⟨fun a => y a / Dv.coordinateSpeed a.1 (θ a.1), ?_⟩
  funext a
  simp only [finiteSpeedLinearMap, LinearMap.coe_mk,
    AddHom.coe_mk]
  exact mul_div_cancel₀ (y a)
    (ne_of_gt (Dv.coordinate_speed_pos a.1 (θ a.1)))

/-- Exact finite derivative of the canonical parameter chart on the universal initial probe. -/
def finiteParameterJetLinearMap (Dv : MovingDivisor)
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (n : ι → ℕ) (θ : BoundedRealSequence) :
    (Fin (movingCanonicalLocationProbeCard n) → ℝ) →ₗ[ℝ]
      ((Σ i, Fin (n i)) → ℂ) :=
  (Dv.finiteLocationJetLinearMap x n θ).comp
    (Dv.finiteSpeedLinearMap n θ)

theorem finiteParameterJetLinearMap_surjective (Dv : MovingDivisor)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence) :
    Function.Surjective
      (Dv.finiteParameterJetLinearMap x n θ) :=
  (Dv.finiteLocationJetLinearMap_surjective x hx hupper n θ).comp
    (Dv.finiteSpeedLinearMap_surjective n θ)


def differentialJetTerm (Dv : MovingDivisor)
    (θ : BoundedRealSequence) (k : ℕ) (a : ℕ) (z : ℂ) : ℂ :=
  if k = 0 then Dv.regularizedTerm θ a z
  else (k.factorial : ℂ) *
    (((Dv.zeroAt θ a : ℂ) - z)⁻¹) ^ (k + 1)

def regularizedPoleDifferentialJetTerm
    (k : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  if k = 0 then
    (((t : ℂ) - z)⁻¹ - (t : ℂ)⁻¹)
  else (k.factorial : ℂ) * (((t : ℂ) - z)⁻¹) ^ (k + 1)

theorem differentialJetTerm_eq (Dv : MovingDivisor)
    (θ : BoundedRealSequence) (k a : ℕ) (z : ℂ) :
    Dv.differentialJetTerm θ k a z =
      regularizedPoleDifferentialJetTerm k (Dv.zeroAt θ a) z :=
  rfl

theorem regularizedPoleDifferentialJetTerm_zero_hasDerivAt
    (t : ℝ) (ht : t ≠ 0) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (fun s : ℝ => (((s : ℂ) - z)⁻¹ - (s : ℂ)⁻¹))
      (-1 / (((t : ℂ) - z) ^ 2) - (-1 / ((t : ℂ) ^ 2))) t := by
  have htZ : (t : ℂ) - z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact (ne_of_gt hz) him
  have hofReal : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    exact (hasDerivAt_id t).ofReal_comp
  exact ((hofReal.sub_const z).inv htZ).sub
    (hofReal.inv (Complex.ofReal_ne_zero.mpr ht))

theorem regularizedPoleDifferentialJetTerm_succ_hasDerivAt
    (k : ℕ) (t : ℝ) {z : ℂ} (hz : 0 < z.im) :
    @HasDerivAt ℝ inferInstance ℂ
      instCommCStarAlgebraComplex.toCStarAlgebra.toAddCommGroup inferInstance
      inferInstance inferInstance
      (fun s : ℝ =>
        (k.factorial : ℂ) * (((s : ℂ) - z)⁻¹) ^ (k + 1))
      (-((Nat.factorial (k + 1) : ℂ) *
        (((t : ℂ) - z)⁻¹) ^ (k + 2))) t := by
  have htZ : (t : ℂ) - z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact (ne_of_gt hz) him
  have hofReal : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    exact (hasDerivAt_id t).ofReal_comp
  have hbase : HasDerivAt (fun s : ℝ => ((s : ℂ) - z)⁻¹)
      (-(((t : ℂ) - z)⁻¹) ^ 2) t := by
    exact (hofReal.sub_const z).inv htZ |>.congr_deriv (by
      field_simp)
  have hpow := hbase.pow (k + 1)
  have hmul := hpow.const_mul (k.factorial : ℂ)
  convert hmul using 1
  · funext s
    rfl
  · rw [Nat.factorial_succ]
    push_cast
    rw [pow_add]
    ring

theorem finiteParameterJetLinearMap_apply (Dv : MovingDivisor)
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard n) → ℝ)
    (s : Σ i, Fin (n i)) :
    Dv.finiteParameterJetLinearMap x n θ p s =
      ∑ a : Fin (movingCanonicalLocationProbeCard n),
        p a • (Dv.coordinateSpeed a.1 (θ a.1) •
          movingCanonicalDifferentialJetCoefficient
            s.2.1 (Dv.zeroAt θ a.1) (x s.1)) := by
  let D := movingCanonicalLocationProbeCard n
  let r : Fin D → ℝ := fun a => Dv.coordinateSpeed a.1 (θ a.1) * p a
  have hr : (Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin D)).symm r =
      ∑ a : Fin D, Finsupp.single a (r a) := by
    ext a
    rw [congrFun
      (Finsupp.linearEquivFunOnFinite_symm_apply ℝ ℝ (Fin D) r) a]
    exact (congrFun (Finsupp.coe_univ_sum_single r) a).symm
  change movingPoleLocationJetRealLinearCombination x n
      (fun a : Fin D => Dv.zeroAt θ a.1)
      ((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin D)).symm r) s = _
  rw [hr, map_sum]
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a ha
  have hsingle : Finsupp.single a (r a) =
      r a • Finsupp.single a (1 : ℝ) := by
    ext b
    by_cases hba : b = a <;> simp [hba]
  rw [hsingle, map_smul]
  rw [Pi.smul_apply]
  rw [movingCanonicalDifferentialJetCoefficient_eq_location_single
    (κ := Fin D) x n
      (fun b : Fin D => Dv.zeroAt θ b.1) a s]
  simp only [r, smul_smul]
  ring

theorem differentialJetTerm_finiteChart_hasFDerivAt (Dv : MovingDivisor)
    (D : ℕ) (θ : BoundedRealSequence) (p : Fin D → ℝ)
    (k : ℕ) (a : Fin D) {z : ℂ} (hz : 0 < z.im) :
    HasNormedFDerivAt
      (fun q : Fin D → ℝ =>
        Dv.differentialJetTerm (movingCanonicalFiniteChart D θ q) k a.1 z)
      ((ContinuousLinearMap.proj a : (Fin D → ℝ) →L[ℝ] ℝ).smulRight
        (Dv.coordinateSpeed a.1 (θ a.1 + p a) •
          movingCanonicalDifferentialJetCoefficient k
            (Dv.zeroAt (movingCanonicalFiniteChart D θ p) a.1) z)) p := by
  let t := Dv.zeroAt (movingCanonicalFiniteChart D θ p) a.1
  have ht : t ≠ 0 :=
    ne_of_gt (Dv.zeroAt_pos (movingCanonicalFiniteChart D θ p) a.1)
  have hzero := Dv.zeroAt_finiteChart_hasFDerivAt D θ p a
  by_cases hk : k = 0
  · subst k
    have hout :=
      (regularizedPoleDifferentialJetTerm_zero_hasDerivAt t ht hz).hasFDerivAt
    have hcomp := hout.comp p hzero
    convert hcomp using 1
    · funext q
      simp [Function.comp_apply, MovingDivisor.differentialJetTerm,
        MovingDivisor.regularizedTerm]
    · ext v
      simp only [FunLike.coe_smul, Pi.smul_apply,
        smul_eq_mul, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply]
      dsimp only [movingCanonicalDifferentialJetCoefficient]
      simp only [if_pos, Nat.zero_add, Nat.factorial_one, Nat.cast_one,
        one_mul, Complex.real_smul]
      dsimp only [t] at ht ⊢
      push_cast
      field_simp [ht]
      ring
  · have hout :=
      (regularizedPoleDifferentialJetTerm_succ_hasDerivAt
        k t hz).hasFDerivAt
    have hcomp := hout.comp p hzero
    convert hcomp using 1
    · funext q
      simp [Function.comp_apply, MovingDivisor.differentialJetTerm, hk]
    · ext v
      simp only [FunLike.coe_smul, Pi.smul_apply,
        smul_eq_mul, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply]
      dsimp only [movingCanonicalDifferentialJetCoefficient]
      rw [if_neg hk]
      simp only [Complex.real_smul]
      norm_num
      ring


end MovingDivisor

end

end GaloisForLFunctions.HTGeometry
