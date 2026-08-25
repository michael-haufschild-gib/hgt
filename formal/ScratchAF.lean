import GaloisForLFunctions.HTGeometry.ColorGramSpecialUnitaryOrbit
import Mathlib.Analysis.InnerProductSpace.PiL2

open Matrix Finset
open scoped ComplexConjugate

namespace ScratchAF

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

def e (a0 : α) : α → ℂ := fun i => if i = a0 then 1 else 0

def a (a0 : α) (x : α → ℂ) : α → ℂ := e a0 + x

def c (a0 : α) (x : α → ℂ) : ℂ := 1 + star (x a0)

def Q (a0 : α) (x : α → ℂ) : Matrix α α ℂ :=
  Matrix.vecMulVec ((c a0 x)⁻¹ • a a0 x) (star (a a0 x))

def completion (a0 : α) (x : α → ℂ) : Matrix α α ℂ := -1 + Q a0 x

lemma star_e_dot_x (a0 : α) (x : α → ℂ) :
    star (e a0) ⬝ᵥ x = x a0 := by
  simp [e, dotProduct]

lemma star_x_dot_e (a0 : α) (x : α → ℂ) :
    star x ⬝ᵥ e a0 = star (x a0) := by
  simp [e, dotProduct]

lemma star_e_dot_e (a0 : α) :
    star (e a0) ⬝ᵥ e a0 = 1 := by
  simp [e, dotProduct]

lemma rootNorm_a (a0 : α) (x : α → ℂ)
    (hx : star x ⬝ᵥ x = 1) :
    GaloisForLFunctions.HTGeometry.rootHermitianNormSq (a a0 x) =
      c a0 x + star (c a0 x) := by
  simp only [GaloisForLFunctions.HTGeometry.rootHermitianNormSq, a]
  rw [show star (e a0 + x) = star (e a0) + star x by
    ext i
    simp]
  rw [add_dotProduct, dotProduct_add, dotProduct_add]
  rw [star_e_dot_e, star_e_dot_x, star_x_dot_e, hx]
  simp [c]
  ring

lemma c_ne_zero (a0 : α) (x : α → ℂ)
    (hx : star x ⬝ᵥ x = 1) (hne : x ≠ -e a0) : c a0 x ≠ 0 := by
  intro hc
  have haNorm : GaloisForLFunctions.HTGeometry.rootHermitianNormSq (a a0 x) = 0 := by
    rw [rootNorm_a a0 x hx, hc, star_zero, add_zero]
  have ha : a a0 x = 0 := by
    have hsum : ((∑ i, Complex.normSq (a a0 x i) : ℝ) : ℂ) = 0 := by
      calc
        ((∑ i, Complex.normSq (a a0 x i) : ℝ) : ℂ) =
            star (a a0 x) ⬝ᵥ a a0 x := by
          push_cast
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Complex.normSq_eq_conj_mul_self]
          rfl
        _ = 0 := haNorm
    have hsumR : (∑ i, Complex.normSq (a a0 x i) : ℝ) = 0 := by
      exact_mod_cast hsum
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (a a0 x j))).mp hsumR i (Finset.mem_univ i)
    exact Complex.normSq_eq_zero.mp hi
  apply hne
  funext i
  have hi := congrFun ha i
  simp [a, e] at hi ⊢
  apply eq_neg_of_add_eq_zero_left
  simpa [add_comm] using hi

lemma Q_conjTranspose (a0 : α) (x : α → ℂ) :
    (Q a0 x)ᴴ =
      Matrix.vecMulVec ((star (c a0 x))⁻¹ • a a0 x) (star (a a0 x)) := by
  ext i j
  simp [Q, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply]
  ring

lemma Qstar_mul_Q (a0 : α) (x : α → ℂ)
    (hx : star x ⬝ᵥ x = 1) (hc : c a0 x ≠ 0) :
    (Q a0 x)ᴴ * Q a0 x = (Q a0 x)ᴴ + Q a0 x := by
  rw [Q_conjTranspose]
  simp only [Q, Matrix.vecMulVec_mul_vecMulVec]
  ext i j
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [show star (a a0 x) ⬝ᵥ (c a0 x)⁻¹ • a a0 x =
      (c a0 x)⁻¹ * (c a0 x + star (c a0 x)) by
    rw [dotProduct_smul]
    have hr := rootNorm_a a0 x hx
    change star (a a0 x) ⬝ᵥ a a0 x = c a0 x + star (c a0 x) at hr
    rw [hr]
    rfl]
  have hsc : star (c a0 x) ≠ 0 := star_ne_zero.mpr hc
  field_simp

theorem completion_unitary (a0 : α) (x : α → ℂ)
    (hx : star x ⬝ᵥ x = 1) (hne : x ≠ -e a0) :
    (completion a0 x)ᴴ * completion a0 x = 1 := by
  have hc := c_ne_zero a0 x hx hne
  rw [completion, Matrix.conjTranspose_add, Matrix.conjTranspose_neg,
    Matrix.conjTranspose_one]
  calc
    (-1 + (Q a0 x)ᴴ) * (-1 + Q a0 x) =
        1 - (Q a0 x)ᴴ - Q a0 x + (Q a0 x)ᴴ * Q a0 x := by
      noncomm_ring
    _ = 1 := by rw [Qstar_mul_Q a0 x hx hc]; noncomm_ring

theorem completion_mulVec_e (a0 : α) (x : α → ℂ)
    (hx : star x ⬝ᵥ x = 1) (hne : x ≠ -e a0) :
    completion a0 x *ᵥ e a0 = x := by
  have hc := c_ne_zero a0 x hx hne
  funext i
  have hstar : star (a a0 x a0) = c a0 x := by simp [a, e, c]
  simp only [completion, Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec,
    Q, Matrix.vecMulVec_mulVec]
  rw [show star (a a0 x) ⬝ᵥ e a0 = star (a a0 x a0) by
    exact star_x_dot_e a0 (a a0 x), hstar]
  simp [hc, a]

abbrev UnitSphere (α : Type*) [Fintype α] :=
  Metric.sphere (0 : EuclideanSpace ℂ α) 1

def raw (x : EuclideanSpace ℂ α) : α → ℂ := x.ofLp

lemma star_raw_dot_raw_of_mem_sphere (x : UnitSphere α) :
    star (raw x.1) ⬝ᵥ raw x.1 = 1 := by
  have hnorm : ‖x.1‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using x.2
  have hsq := congrArg (fun r : ℝ => r ^ 2) hnorm
  rw [PiLp.norm_sq_eq_of_L2] at hsq
  have hsum : (∑ i, Complex.normSq (raw x.1 i)) = 1 := by
    simpa [raw, Complex.sq_norm] using hsq
  calc
    star (raw x.1) ⬝ᵥ raw x.1 =
        ((∑ i, Complex.normSq (raw x.1 i) : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.normSq_eq_conj_mul_self]
      rfl
    _ = 1 := by rw [hsum]; norm_num

lemma star_mulVec_dot_mulVec_of_unitary (a0 : α)
    (U : Matrix.unitaryGroup α ℂ) :
    star ((U : Matrix α α ℂ) *ᵥ e a0) ⬝ᵥ
        ((U : Matrix α α ℂ) *ᵥ e a0) = 1 := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec]
  have hU := (Unitary.mem_iff.mp U.2).1
  change (U : Matrix α α ℂ)ᴴ * U = 1 at hU
  rw [hU, Matrix.one_mulVec, star_e_dot_e]

def unitaryFirstColumn (a0 : α) (U : Matrix.unitaryGroup α ℂ) : UnitSphere α := by
  let y : α → ℂ := (U : Matrix α α ℂ) *ᵥ e a0
  refine ⟨WithLp.toLp 2 y, ?_⟩
  rw [mem_sphere_zero_iff_norm]
  have hdot := star_mulVec_dot_mulVec_of_unitary a0 U
  have hsum : ∑ i, Complex.normSq (y i) = 1 := by
    have hcast : ((∑ i, Complex.normSq (y i) : ℝ) : ℂ) = 1 := by
      calc
        ((∑ i, Complex.normSq (y i) : ℝ) : ℂ) = star y ⬝ᵥ y := by
          push_cast
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Complex.normSq_eq_conj_mul_self]
          rfl
        _ = 1 := hdot
    exact_mod_cast hcast
  rw [PiLp.norm_eq_of_L2]
  simp [y, Complex.sq_norm, hsum]

lemma raw_unitaryFirstColumn (a0 : α) (U : Matrix.unitaryGroup α ℂ) :
    raw (unitaryFirstColumn a0 U).1 = (U : Matrix α α ℂ) *ᵥ e a0 := rfl

theorem continuous_unitaryFirstColumn (a0 : α) :
    Continuous (unitaryFirstColumn a0 : Matrix.unitaryGroup α ℂ → UnitSphere α) := by
  apply continuous_induced_rng.2
  exact (PiLp.lipschitzWith_toLp 2 (fun _ : α => ℂ)).continuous.comp (by fun_prop)

def unitarySphereAction (U : Matrix.unitaryGroup α ℂ) (x : UnitSphere α) :
    UnitSphere α := by
  let y : α → ℂ := (U : Matrix α α ℂ) *ᵥ raw x.1
  refine ⟨WithLp.toLp 2 y, ?_⟩
  rw [mem_sphere_zero_iff_norm]
  have hdot : star y ⬝ᵥ y = 1 := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec]
    have hU := (Unitary.mem_iff.mp U.2).1
    change (U : Matrix α α ℂ)ᴴ * U = 1 at hU
    rw [hU, Matrix.one_mulVec, star_raw_dot_raw_of_mem_sphere]
  have hsum : ∑ i, Complex.normSq (y i) = 1 := by
    have hcast : ((∑ i, Complex.normSq (y i) : ℝ) : ℂ) = 1 := by
      calc
        ((∑ i, Complex.normSq (y i) : ℝ) : ℂ) = star y ⬝ᵥ y := by
          push_cast
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Complex.normSq_eq_conj_mul_self]
          rfl
        _ = 1 := hdot
    exact_mod_cast hcast
  rw [PiLp.norm_eq_of_L2]
  simp [y, Complex.sq_norm, hsum]

@[simp] lemma raw_unitarySphereAction (U : Matrix.unitaryGroup α ℂ)
    (x : UnitSphere α) :
    raw (unitarySphereAction U x).1 = (U : Matrix α α ℂ) *ᵥ raw x.1 := rfl

theorem continuous_unitarySphereAction (U : Matrix.unitaryGroup α ℂ) :
    Continuous (unitarySphereAction U : UnitSphere α → UnitSphere α) := by
  apply continuous_induced_rng.2
  exact (PiLp.lipschitzWith_toLp 2 (fun _ : α => ℂ)).continuous.comp (by fun_prop)

@[simp] theorem unitarySphereAction_one (x : UnitSphere α) :
    unitarySphereAction (1 : Matrix.unitaryGroup α ℂ) x = x := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  change ((1 : Matrix α α ℂ) *ᵥ raw x.1) i = raw x.1 i
  rw [Matrix.one_mulVec]

theorem unitarySphereAction_mul (U V : Matrix.unitaryGroup α ℂ) (x : UnitSphere α) :
    unitarySphereAction (U * V) x = unitarySphereAction U (unitarySphereAction V x) := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  change ((((U : Matrix α α ℂ) * (V : Matrix α α ℂ)) *ᵥ raw x.1) i) =
    ((U : Matrix α α ℂ) *ᵥ ((V : Matrix α α ℂ) *ᵥ raw x.1)) i
  rw [Matrix.mulVec_mulVec]

def sphereNeg (x : UnitSphere α) : UnitSphere α :=
  ⟨-x.1, by
    rw [mem_sphere_zero_iff_norm, norm_neg]
    exact mem_sphere_zero_iff_norm.mp x.2⟩

@[simp] theorem raw_sphereNeg (x : UnitSphere α) :
    raw (sphereNeg x).1 = -raw x.1 := rfl

theorem unitarySphereAction_neg (U : Matrix.unitaryGroup α ℂ) (x : UnitSphere α) :
    unitarySphereAction U (sphereNeg x) = sphereNeg (unitarySphereAction U x) := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  change ((U : Matrix α α ℂ) *ᵥ -raw x.1) i =
    (-((U : Matrix α α ℂ) *ᵥ raw x.1)) i
  rw [Matrix.mulVec_neg]

def basisSphere (a0 : α) : UnitSphere α :=
  unitaryFirstColumn a0 1

@[simp] theorem raw_basisSphere (a0 : α) : raw (basisSphere a0).1 = e a0 := by
  rw [basisSphere, raw_unitaryFirstColumn]
  change (1 : Matrix α α ℂ) *ᵥ e a0 = e a0
  rw [Matrix.one_mulVec]

lemma unitaryFirstColumn_eq_action (a0 : α) (U : Matrix.unitaryGroup α ℂ) :
    unitaryFirstColumn a0 U =
      unitarySphereAction U (basisSphere a0) := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  change ((U : Matrix α α ℂ) *ᵥ e a0) i =
    ((U : Matrix α α ℂ) *ᵥ raw (basisSphere a0).1) i
  rw [raw_basisSphere]

abbrev SphereChart (a0 : α) (R : Matrix.unitaryGroup α ℂ) :=
  {x : UnitSphere α // x ≠ sphereNeg (unitaryFirstColumn a0 R)}

lemma rotated_raw_ne (a0 : α) (R : Matrix.unitaryGroup α ℂ)
    (x : SphereChart a0 R) :
    raw (unitarySphereAction R⁻¹ x.1).1 ≠ -e a0 := by
  intro hy
  apply x.2
  have hact : unitarySphereAction R (unitarySphereAction R⁻¹ x.1) = x.1 := by
    calc
      unitarySphereAction R (unitarySphereAction R⁻¹ x.1) =
          unitarySphereAction (R * R⁻¹) x.1 :=
        (unitarySphereAction_mul R R⁻¹ x.1).symm
      _ = x.1 := by simp
  rw [← hact, show unitarySphereAction R⁻¹ x.1 = sphereNeg (basisSphere a0) by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    change raw (unitarySphereAction R⁻¹ x.1).1 i =
      raw (sphereNeg (basisSphere a0)).1 i
    simpa using congrFun hy i]
  rw [unitarySphereAction_neg, ← unitaryFirstColumn_eq_action]

def rotatedCompletion (a0 : α) (R : Matrix.unitaryGroup α ℂ)
    (x : SphereChart a0 R) : Matrix.unitaryGroup α ℂ := by
  let y : UnitSphere α := unitarySphereAction R⁻¹ x.1
  have hyne : raw y.1 ≠ -e a0 := rotated_raw_ne a0 R x
  let S : Matrix.unitaryGroup α ℂ :=
    ⟨completion a0 (raw y.1),
      Matrix.mem_unitaryGroup_iff.mpr
        (mul_eq_one_comm.mp
          (completion_unitary a0 (raw y.1) (star_raw_dot_raw_of_mem_sphere y) hyne))⟩
  exact R * S

noncomputable def matrixVecLinearEquiv :
    Matrix α α ℂ ≃ₗ[ℂ] ((α × α) → ℂ) :=
  LinearEquiv.ofBijective
    { toFun := Matrix.vec
      map_add' := Matrix.vec_add
      map_smul' := Matrix.vec_smul }
    Matrix.vec_bijective

theorem continuous_rotatedCompletion (a0 : α) (R : Matrix.unitaryGroup α ℂ) :
    Continuous (rotatedCompletion a0 R : SphereChart a0 R → Matrix.unitaryGroup α ℂ) := by
  apply continuous_induced_rng.2
  apply continuous_iff_continuousAt.2
  intro x
  have hc := c_ne_zero a0 (raw (unitarySphereAction R⁻¹ x.1).1)
    (star_raw_dot_raw_of_mem_sphere _) (rotated_raw_ne a0 R x)
  have hcomp : ContinuousAt (completion a0)
      (raw (unitarySphereAction R⁻¹ x.1).1) := by
    let E := matrixVecLinearEquiv (α := α)
    have hvec : ContinuousAt (fun z : α → ℂ => E (completion a0 z))
        (raw (unitarySphereAction R⁻¹ x.1).1) := by
      rw [continuousAt_pi]
      intro ij
      change ContinuousAt (fun z : α → ℂ =>
        -(if ij.2 = ij.1 then 1 else 0) +
          ((1 + star (z a0))⁻¹ * ((if ij.2 = a0 then 1 else 0) + z ij.2)) *
            star ((if ij.1 = a0 then 1 else 0) + z ij.1))
        (raw (unitarySphereAction R⁻¹ x.1).1)
      have hi : ContinuousAt (fun z : α → ℂ => z ij.2) _ :=
        continuousAt_apply ij.2 (raw (unitarySphereAction R⁻¹ x.1).1)
      have hj : ContinuousAt (fun z : α → ℂ => z ij.1) _ :=
        continuousAt_apply ij.1 (raw (unitarySphereAction R⁻¹ x.1).1)
      have hden : ContinuousAt (fun z : α → ℂ => 1 + star (z a0))
          (raw (unitarySphereAction R⁻¹ x.1).1) := by
        exact continuousAt_const.add
          (continuousAt_apply a0 (raw (unitarySphereAction R⁻¹ x.1).1)).star
      have hc' : 1 + star (raw (unitarySphereAction R⁻¹ x.1).1 a0) ≠ 0 := hc
      exact continuousAt_const.neg.add
        (((hden.inv₀ hc').mul (continuousAt_const.add hi)).mul
          (continuousAt_const.add hj).star)
    have hback := E.toContinuousLinearEquiv.symm.continuousAt.comp hvec
    have heq : (E.toContinuousLinearEquiv.symm ∘
        fun z : α → ℂ => E (completion a0 z)) = completion a0 := by
      funext z
      change E.symm (E (completion a0 z)) = completion a0 z
      exact E.symm_apply_apply _
    rw [heq] at hback
    exact hback
  have haction : Continuous (fun x : SphereChart a0 R =>
      unitarySphereAction R⁻¹ x.1) := by
    change Continuous (unitarySphereAction R⁻¹ ∘ Subtype.val)
    exact (continuous_unitarySphereAction R⁻¹).comp continuous_subtype_val
  have hact : Continuous (fun x : SphereChart a0 R =>
      (unitarySphereAction R⁻¹ x.1).1) :=
    continuous_subtype_val.comp haction
  have hraw : ContinuousAt (fun x : SphereChart a0 R =>
      raw (unitarySphereAction R⁻¹ x.1).1) x := by
    rw [continuousAt_pi]
    intro i
    change ContinuousAt (fun x : SphereChart a0 R =>
      (unitarySphereAction R⁻¹ x.1).1 i) x
    let ev : EuclideanSpace ℂ α →L[ℂ] ℂ :=
      LinearMap.mkContinuous (PiLp.projₗ 2 (fun _ : α => ℂ) i) 1 (fun z => by
        simpa using PiLp.norm_apply_le z i)
    exact (ev.continuous.comp hact).continuousAt
  change ContinuousAt (fun x : SphereChart a0 R =>
    (R : Matrix α α ℂ) * completion a0
      (raw (unitarySphereAction R⁻¹ x.1).1)) x
  apply continuousAt_const.mul
  change ContinuousAt (completion a0 ∘ fun x : SphereChart a0 R =>
    raw (unitarySphereAction R⁻¹ x.1).1) x
  exact hcomp.comp (f := fun x : SphereChart a0 R =>
    raw (unitarySphereAction R⁻¹ x.1).1) hraw

theorem rotatedCompletion_firstColumn (a0 : α) (R : Matrix.unitaryGroup α ℂ)
    (x : SphereChart a0 R) :
    unitaryFirstColumn a0 (rotatedCompletion a0 R x) = x.1 := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  change (((R : Matrix α α ℂ) *
      completion a0 (raw (unitarySphereAction R⁻¹ x.1).1)) *ᵥ e a0) i = raw x.1 i
  rw [← Matrix.mulVec_mulVec, completion_mulVec_e a0]
  · have hact : unitarySphereAction R (unitarySphereAction R⁻¹ x.1) = x.1 := by
      calc
        unitarySphereAction R (unitarySphereAction R⁻¹ x.1) =
            unitarySphereAction (R * R⁻¹) x.1 :=
          (unitarySphereAction_mul R R⁻¹ x.1).symm
        _ = x.1 := by simp
    have h := congrArg Subtype.val hact
    exact congrFun (congrArg WithLp.ofLp h) i
  · exact star_raw_dot_raw_of_mem_sphere _
  · intro hy
    apply x.2
    have hact : unitarySphereAction R (unitarySphereAction R⁻¹ x.1) = x.1 := by
      calc
        unitarySphereAction R (unitarySphereAction R⁻¹ x.1) =
            unitarySphereAction (R * R⁻¹) x.1 :=
          (unitarySphereAction_mul R R⁻¹ x.1).symm
        _ = x.1 := by simp
    rw [← hact]
    have hy' : unitarySphereAction R⁻¹ x.1 = sphereNeg (basisSphere a0) := by
      apply Subtype.ext
      apply PiLp.ext
      intro j
      change raw (unitarySphereAction R⁻¹ x.1).1 j =
        raw (sphereNeg (basisSphere a0)).1 j
      simpa using congrFun hy j
    rw [hy', unitarySphereAction_neg, ← unitaryFirstColumn_eq_action]

end

end ScratchAF
