import GaloisForLFunctions.HTGeometry.MovingDivisorFiniteJetSubmersion
import GaloisForLFunctions.HTGeometry.MovingCanonicalFiniteJetProbe

/-!
# The universal finite parameter probe of a moving divisor

The initial block of parameters of a moving divisor spans every finite complex jet packet, the
actual differential jets of the carrier depend smoothly on those parameters, and the derivative of
the actual jet family is exactly the finite parameter jet map — hence surjective.
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
  simp only [MovingDivisor.finiteSpeedLinearMap, LinearMap.coe_mk,
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
  (Dv.finiteLocationJetLinearMap_surjective
    x hx hupper n θ).comp
      (Dv.finiteSpeedLinearMap_surjective n θ)


def differentialJetTerm (Dv : MovingDivisor)
    (θ : BoundedRealSequence) (k : ℕ) (a : ℕ) (z : ℂ) : ℂ :=
  if k = 0 then Dv.regularizedTerm θ a z
  else (k.factorial : ℂ) *
    (((Dv.zeroAt θ a : ℂ) - z)⁻¹) ^ (k + 1)

theorem differentialJetTerm_eq (Dv : MovingDivisor)
    (θ : BoundedRealSequence) (k a : ℕ) (z : ℂ) :
    Dv.differentialJetTerm θ k a z =
      regularizedPoleDifferentialJetTerm k (Dv.zeroAt θ a) z :=
  rfl

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
        Dv.differentialJetTerm
          (movingCanonicalFiniteChart D θ q) k a.1 z)
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

theorem iteratedDeriv_regularizedTerm (Dv : MovingDivisor)
    (θ : BoundedRealSequence) (a k : ℕ) {z : ℂ} (hz : 0 < z.im) :
    iteratedDeriv k (Dv.regularizedTerm θ a) z =
      Dv.differentialJetTerm θ k a z := by
  by_cases hk : k = 0
  · subst k
    simp [MovingDivisor.differentialJetTerm, MovingDivisor.regularizedTerm, iteratedDeriv_zero]
  · have hkernel : ContDiffAt ℂ (k : ℕ∞)
        (fun w : ℂ => ((Dv.zeroAt θ a : ℂ) - w)⁻¹) z := by
      have hne : (Dv.zeroAt θ a : ℂ) - z ≠ 0 := by
        intro h
        have him := congrArg Complex.im h
        simp at him
        exact (ne_of_gt hz) him
      fun_prop
    have hconst : ContDiffAt ℂ (k : ℕ∞)
        (fun _ : ℂ => (Dv.zeroAt θ a : ℂ)⁻¹) z :=
      contDiffAt_const
    change iteratedDeriv k
      ((fun w : ℂ => ((Dv.zeroAt θ a : ℂ) - w)⁻¹) -
        fun _ : ℂ => (Dv.zeroAt θ a : ℂ)⁻¹) z = _
    rw [iteratedDeriv_sub hkernel hconst,
      iteratedDeriv_realCauchyKernel (Dv.zeroAt θ a) k z hz,
      iteratedDeriv_const]
    simp [MovingDivisor.differentialJetTerm, hk]

/-- Finite-coordinate canonical perturbation changes every actual node jet by the exact finite
sum of the corresponding pole contributions. -/
theorem iteratedDeriv_logDerivative_finiteChart (Dv : MovingDivisor)
    (D : ℕ) (θ : BoundedRealSequence) (p : Fin D → ℝ)
    (k : ℕ) {z : ℂ} (hz : 0 < z.im) :
    iteratedDeriv k
        (Dv.logDerivative ((movingCanonicalFiniteChart D θ p : BoundedRealSequence) : ℕ → ℝ)) z =
      iteratedDeriv k (Dv.logDerivative (θ : ℕ → ℝ)) z +
        ∑ a : Fin D,
          (Dv.differentialJetTerm
              (movingCanonicalFiniteChart D θ p) k a.1 z -
            Dv.differentialJetTerm θ k a.1 z) := by
  have heq : Dv.logDerivative ((movingCanonicalFiniteChart D θ p : BoundedRealSequence) : ℕ → ℝ) =ᶠ[nhds z]
      fun w => Dv.logDerivative (θ : ℕ → ℝ) w +
        ∑ a : Fin D,
          (Dv.regularizedTerm
              (movingCanonicalFiniteChart D θ p) a.1 w -
            Dv.regularizedTerm θ a.1 w) := by
    filter_upwards [isOpen_upperHalfPlane.mem_nhds hz] with w hw
    simpa [MovingDivisor.normalizedJetTerm, MovingDivisor.regularizedTerm] using
      Dv.normalizedJet_finiteChart D θ p 0 hw
  rw [heq.iteratedDeriv_eq k]
  have hbase : ContDiffAt ℂ (k : ℕ∞)
      (Dv.logDerivative (θ : ℕ → ℝ)) z :=
    (Dv.analyticAt_logDerivative θ hz).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_rfl)
  have hterm : ∀ a : Fin D,
      ContDiffAt ℂ (k : ℕ∞)
          (Dv.regularizedTerm
            (movingCanonicalFiniteChart D θ p) a.1) z ∧
        ContDiffAt ℂ (k : ℕ∞)
          (Dv.regularizedTerm θ a.1) z := by
    intro a
    have hneNew :
        (Dv.zeroAt (movingCanonicalFiniteChart D θ p) a.1 : ℂ) - z ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      exact (ne_of_gt hz) him
    have hneOld : (Dv.zeroAt θ a.1 : ℂ) - z ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      exact (ne_of_gt hz) him
    constructor <;> unfold MovingDivisor.regularizedTerm <;> fun_prop
  have hsum : ContDiffAt ℂ (k : ℕ∞)
      (fun w => ∑ a : Fin D,
        (Dv.regularizedTerm
            (movingCanonicalFiniteChart D θ p) a.1 w -
          Dv.regularizedTerm θ a.1 w)) z :=
    ContDiffAt.sum (s := Finset.univ)
      (fun a _ => (hterm a).1.sub (hterm a).2)
  change iteratedDeriv k
      (Dv.logDerivative (θ : ℕ → ℝ) +
        fun w => ∑ a : Fin D,
          (Dv.regularizedTerm
              (movingCanonicalFiniteChart D θ p) a.1 w -
            Dv.regularizedTerm θ a.1 w)) z = _
  rw [iteratedDeriv_add hbase hsum]
  have hsumDeriv :
      iteratedDeriv k
          (fun w => ∑ a : Fin D,
            (Dv.regularizedTerm
                (movingCanonicalFiniteChart D θ p) a.1 w -
              Dv.regularizedTerm θ a.1 w)) z =
        ∑ a : Fin D, iteratedDeriv k
          (fun w =>
            Dv.regularizedTerm
                (movingCanonicalFiniteChart D θ p) a.1 w -
              Dv.regularizedTerm θ a.1 w) z := by
    have hfun :
        (fun w => ∑ a : Fin D,
          (Dv.regularizedTerm
              (movingCanonicalFiniteChart D θ p) a.1 w -
            Dv.regularizedTerm θ a.1 w)) =
          ∑ a : Fin D,
            (Dv.regularizedTerm
                (movingCanonicalFiniteChart D θ p) a.1 -
              Dv.regularizedTerm θ a.1) := by
      funext w
      simp
    rw [hfun]
    exact iteratedDeriv_sum
      (I := Finset.univ)
      (fun a _ => (hterm a).1.sub (hterm a).2)
  rw [hsumDeriv]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro a ha
  change iteratedDeriv k
      (Dv.regularizedTerm
          (movingCanonicalFiniteChart D θ p) a.1 -
        Dv.regularizedTerm θ a.1) z = _
  rw [iteratedDeriv_sub]
  · rw [Dv.iteratedDeriv_regularizedTerm
      (movingCanonicalFiniteChart D θ p) a.1 k hz,
      Dv.iteratedDeriv_regularizedTerm θ a.1 k hz]
  · exact (hterm a).1
  · exact (hterm a).2

def finiteActualJetFamily (Dv : MovingDivisor)
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard n) → ℝ) :
    (Σ i, Fin (n i)) → ℂ :=
  fun s => iteratedDeriv s.2.1
    (Dv.logDerivative ((movingCanonicalFiniteChart (movingCanonicalLocationProbeCard n) θ p : BoundedRealSequence) : ℕ → ℝ)) (x s.1)

theorem finiteActualJetFamily_coordinate_hasFDerivAt (Dv : MovingDivisor)
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard n) → ℝ)
    (s : Σ i, Fin (n i)) :
    HasNormedFDerivAt
      (fun q => Dv.finiteActualJetFamily x n θ q s)
      (∑ a : Fin (movingCanonicalLocationProbeCard n),
        (ContinuousLinearMap.proj a :
          (Fin (movingCanonicalLocationProbeCard n) → ℝ) →L[ℝ] ℝ).smulRight
          (Dv.coordinateSpeed a.1 (θ a.1 + p a) •
            movingCanonicalDifferentialJetCoefficient s.2.1
              (Dv.zeroAt (movingCanonicalFiniteChart (movingCanonicalLocationProbeCard n) θ p) a.1)
              (x s.1))) p := by
  let D := movingCanonicalLocationProbeCard n
  have hterm : ∀ a : Fin D, HasNormedFDerivAt
      (fun q : Fin D → ℝ =>
        Dv.differentialJetTerm
            (movingCanonicalFiniteChart D θ q) s.2.1 a.1 (x s.1) -
          Dv.differentialJetTerm θ s.2.1 a.1 (x s.1))
      ((ContinuousLinearMap.proj a : (Fin D → ℝ) →L[ℝ] ℝ).smulRight
        (Dv.coordinateSpeed a.1 (θ a.1 + p a) •
          movingCanonicalDifferentialJetCoefficient s.2.1
            (Dv.zeroAt (movingCanonicalFiniteChart D θ p) a.1) (x s.1))) p := by
    intro a
    have hnew :=
      Dv.differentialJetTerm_finiteChart_hasFDerivAt
        D θ p s.2.1 a (hupper s.1)
    have hadjusted := hnew.add_const
      (-Dv.differentialJetTerm θ s.2.1 a.1 (x s.1))
    convert hadjusted using 1
    funext q
    simp only [sub_eq_add_neg]
  have hsum := HasFDerivAt.sum
    (u := (Finset.univ : Finset (Fin D)))
    (fun a _ => hterm a)
  have hfull := hsum.const_add
    (iteratedDeriv s.2.1 (Dv.logDerivative (θ : ℕ → ℝ)) (x s.1))
  convert hfull using 1
  funext q
  dsimp only [MovingDivisor.finiteActualJetFamily]
  rw [Finset.sum_apply]
  exact Dv.iteratedDeriv_logDerivative_finiteChart
    D θ q s.2.1 (hupper s.1)

def finiteParameterJetCLM (Dv : MovingDivisor)
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (n : ι → ℕ) (θ : BoundedRealSequence) :
    (Fin (movingCanonicalLocationProbeCard n) → ℝ) →L[ℝ]
      ((Σ i, Fin (n i)) → ℂ) :=
  LinearMap.toContinuousLinearMap
    (Dv.finiteParameterJetLinearMap x n θ)

theorem finiteActualJetFamily_hasFDerivAt (Dv : MovingDivisor)
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard n) → ℝ) :
    HasNormedFDerivAt
      (Dv.finiteActualJetFamily x n θ)
      (Dv.finiteParameterJetCLM x n
        (movingCanonicalFiniteChart
          (movingCanonicalLocationProbeCard n) θ p)) p := by
  let D := movingCanonicalLocationProbeCard n
  let derivative : (Σ i, Fin (n i)) →
      (Fin D → ℝ) →L[ℝ] ℂ := fun s =>
    ∑ a : Fin D,
      (ContinuousLinearMap.proj a : (Fin D → ℝ) →L[ℝ] ℝ).smulRight
        (Dv.coordinateSpeed a.1 (θ a.1 + p a) •
          movingCanonicalDifferentialJetCoefficient s.2.1
            (Dv.zeroAt (movingCanonicalFiniteChart D θ p) a.1) (x s.1))
  have hpi : HasNormedFDerivAt
      (Dv.finiteActualJetFamily x n θ)
      (ContinuousLinearMap.pi derivative) p := by
    apply (hasFDerivAt_pi).2
    intro s
    exact Dv.finiteActualJetFamily_coordinate_hasFDerivAt
      x hupper n θ p s
  convert hpi using 1
  ext v s
  rw [MovingDivisor.finiteParameterJetCLM]
  change Dv.finiteParameterJetLinearMap x n
      (movingCanonicalFiniteChart D θ p) v s = derivative s v
  rw [Dv.finiteParameterJetLinearMap_apply]
  simp only [derivative, sum_apply,
    ContinuousLinearMap.smulRight_apply]
  apply Finset.sum_congr rfl
  intro a ha
  rw [movingCanonicalFiniteChart_apply, dif_pos a.2]
  change
    v a • Dv.coordinateSpeed a.1 (θ a.1 + p a) •
        movingCanonicalDifferentialJetCoefficient s.2.1
          (Dv.zeroAt (movingCanonicalFiniteChart D θ p) a.1)
          (x s.1) =
      v a • Dv.coordinateSpeed a.1 (θ a.1 + p a) •
        movingCanonicalDifferentialJetCoefficient s.2.1
          (Dv.zeroAt (movingCanonicalFiniteChart D θ p) a.1)
          (x s.1)
  rfl

theorem contDiff_zeroAt_finiteChart (Dv : MovingDivisor)
    (D : ℕ) (θ : BoundedRealSequence) (a : Fin D) :
    ContDiff ℝ ⊤
      (fun p : Fin D → ℝ =>
        Dv.zeroAt (movingCanonicalFiniteChart D θ p) a.1) := by
  have hcoord : ContDiff ℝ ⊤
      (fun p : Fin D → ℝ => θ a.1 + p a) :=
    contDiff_const.add
      (ContinuousLinearMap.proj a :
        (Fin D → ℝ) →L[ℝ] ℝ).contDiff
  have hcomp := contDiff_real_tanh.comp hcoord
  unfold MovingDivisor.zeroAt MovingDivisor.zero
  simp only [movingCanonicalFiniteChart_apply, dif_pos a.2]
  exact contDiff_const.add (contDiff_const.mul hcomp)

theorem contDiff_zeroAt_finiteChart_ofReal (Dv : MovingDivisor)
    (D : ℕ) (θ : BoundedRealSequence) (a : Fin D) :
    ContDiff ℝ ⊤
      (fun p : Fin D → ℝ =>
        (Dv.zeroAt (movingCanonicalFiniteChart D θ p) a.1 : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp
    (Dv.contDiff_zeroAt_finiteChart D θ a)

theorem contDiff_differentialJetTerm_finiteChart (Dv : MovingDivisor)
    (D : ℕ) (θ : BoundedRealSequence)
    (k : ℕ) (a : Fin D) {z : ℂ} (hz : 0 < z.im) :
    ContDiff ℝ ⊤
      (fun p : Fin D → ℝ =>
        Dv.differentialJetTerm
          (movingCanonicalFiniteChart D θ p) k a.1 z) := by
  have htanh : ContDiff ℝ ⊤ Real.tanh := by
    have hneg : ContDiff ℝ ⊤ (fun x : ℝ => -x) := contDiff_id.neg
    have hexpNeg : ContDiff ℝ ⊤ (fun x : ℝ => Real.exp (-x)) :=
      Real.contDiff_exp.comp hneg
    have hquot : ContDiff ℝ ⊤
        (fun x : ℝ =>
          (Real.exp x - Real.exp (-x)) /
            (Real.exp x + Real.exp (-x))) :=
      (Real.contDiff_exp.sub hexpNeg).div
        (Real.contDiff_exp.add hexpNeg)
        (fun x => ne_of_gt (add_pos (Real.exp_pos x) (Real.exp_pos (-x))))
    convert hquot using 1
    funext x
    exact Real.tanh_eq x
  have hzero : ContDiff ℝ ⊤
      (fun p : Fin D → ℝ =>
        Dv.zeroAt (movingCanonicalFiniteChart D θ p) a.1) := by
    have hcoord : ContDiff ℝ ⊤
        (fun p : Fin D → ℝ => θ a.1 + p a) :=
      contDiff_const.add
        (ContinuousLinearMap.proj a :
          (Fin D → ℝ) →L[ℝ] ℝ).contDiff
    have hcomp := htanh.comp hcoord
    unfold MovingDivisor.zeroAt MovingDivisor.zero
    simp only [movingCanonicalFiniteChart_apply, dif_pos a.2]
    exact contDiff_const.add (contDiff_const.mul hcomp)
  have hzeroC : ContDiff ℝ ⊤
      (fun p : Fin D → ℝ =>
        (Dv.zeroAt (movingCanonicalFiniteChart D θ p) a.1 : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp hzero
  have hsep : ∀ p : Fin D → ℝ,
      (Dv.zeroAt (movingCanonicalFiniteChart D θ p) a.1 : ℂ) - z ≠ 0 := by
    intro p h
    have him := congrArg Complex.im h
    simp at him
    exact (ne_of_gt hz) him
  have hne : ∀ p : Fin D → ℝ,
      (Dv.zeroAt (movingCanonicalFiniteChart D θ p) a.1 : ℂ) ≠ 0 := by
    intro p
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Dv.zeroAt_pos (movingCanonicalFiniteChart D θ p) a.1))
  by_cases hk : k = 0
  · subst k
    simp only [MovingDivisor.differentialJetTerm, if_pos,
      MovingDivisor.regularizedTerm]
    fun_prop
  · simp only [MovingDivisor.differentialJetTerm, if_neg hk]
    fun_prop

theorem contDiff_finiteActualJetFamily (Dv : MovingDivisor)
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence) :
    ContDiff ℝ ⊤ (Dv.finiteActualJetFamily x n θ) := by
  rw [contDiff_pi]
  intro s
  let D := movingCanonicalLocationProbeCard n
  have hfun :
      (fun p : Fin D → ℝ =>
        Dv.finiteActualJetFamily x n θ p s) =
        fun p =>
          iteratedDeriv s.2.1
              (Dv.logDerivative (θ : ℕ → ℝ)) (x s.1) +
            ∑ a : Fin D,
              (Dv.differentialJetTerm
                  (movingCanonicalFiniteChart D θ p)
                  s.2.1 a.1 (x s.1) -
                Dv.differentialJetTerm
                  θ s.2.1 a.1 (x s.1)) := by
    funext p
    exact Dv.iteratedDeriv_logDerivative_finiteChart
      D θ p s.2.1 (hupper s.1)
  rw [hfun]
  apply contDiff_const.add
  simpa only [Finset.sum_const_zero, add_zero] using
    (ContDiff.sum (s := (Finset.univ : Finset (Fin D)))
      (fun a _ =>
        (Dv.contDiff_differentialJetTerm_finiteChart
          D θ s.2.1 a (hupper s.1)).sub contDiff_const))

theorem fderiv_finiteActualJetFamily (Dv : MovingDivisor)
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard n) → ℝ) :
    fderiv ℝ (Dv.finiteActualJetFamily x n θ) p =
      Dv.finiteParameterJetCLM x n
        (movingCanonicalFiniteChart
          (movingCanonicalLocationProbeCard n) θ p) :=
  (Dv.finiteActualJetFamily_hasFDerivAt
    x hupper n θ p).fderiv

theorem finiteParameterJetCLM_surjective (Dv : MovingDivisor)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hx : Function.Injective x)
    (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence) :
    Function.Surjective
      (Dv.finiteParameterJetCLM x n θ) := by
  intro y
  obtain ⟨p, hp⟩ :=
    Dv.finiteParameterJetLinearMap_surjective
      x hx hupper n θ y
  refine ⟨p, ?_⟩
  exact hp

theorem fderiv_finiteActualJetFamily_surjective (Dv : MovingDivisor)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hx : Function.Injective x)
    (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard n) → ℝ) :
    Function.Surjective
      (fderiv ℝ (Dv.finiteActualJetFamily x n θ) p) := by
  rw [Dv.fderiv_finiteActualJetFamily x hupper n θ p]
  exact Dv.finiteParameterJetCLM_surjective
    x hx hupper n
      (movingCanonicalFiniteChart
        (movingCanonicalLocationProbeCard n) θ p)

end MovingDivisor

end

end GaloisForLFunctions.HTGeometry
