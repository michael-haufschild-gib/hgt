import GaloisForLFunctions.HTGeometry.ColorGramSpecialUnitaryOrbit
import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryPathConnected
import GaloisForLFunctions.HTGeometry.FundamentalGroupTopologicalGroup
import GaloisForLFunctions.HTGeometry.FiniteUnitaryHaarMeasureLaw
import GaloisForLFunctions.HTGeometry.LoopOpenCoverDecomposition
import GaloisForLFunctions.HTGeometry.SphereSimplyConnected
import GaloisForLFunctions.HTGeometry.SchurTriangulation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Normed.Module.Connected

open Matrix Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

namespace FiniteUnitaryStabilization

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
  have hsq := congrArg (fun r : ℝ => r ^ (2 : ℕ)) hnorm
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

@[simp] theorem raw_unitaryFirstColumn_apply (a0 : α)
    (U : Matrix.unitaryGroup α ℂ) (i : α) :
    raw (unitaryFirstColumn a0 U).1 i = (U : Matrix α α ℂ) i a0 := by
  rw [raw_unitaryFirstColumn]
  simp [Matrix.mulVec, dotProduct, e]

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

omit [DecidableEq α] in
theorem unitSphere_compl_singleton_contractible (v : UnitSphere α) :
    ContractibleSpace ({v}ᶜ : Set (UnitSphere α)) :=
  sphereComplementPoint_contractible v

theorem unitSphere_isPathConnected_compl_singleton (v : UnitSphere α) :
    IsPathConnected ({v}ᶜ : Set (UnitSphere α)) := by
  rw [isPathConnected_iff_pathConnectedSpace]
  letI : ContractibleSpace ({v}ᶜ : Set (UnitSphere α)) :=
    unitSphere_compl_singleton_contractible v
  infer_instance

theorem PartialEquiv.symm_image_target_minus_singleton_eq_local
    {A B : Type*} (f : PartialEquiv A B) {b : B} (hb : b ∈ f.target) :
    f.symm '' (f.target \ {b}) = f.source \ {f.symm b} := by
  rw [Set.image_sdiff_of_injOn, f.symm_image_target_eq_source, Set.image_singleton]
  · exact f.symm.injOn
  · exact Set.singleton_subset_iff.mpr hb

theorem unitSphere_isPathConnected_compl_antipodes (v : UnitSphere α)
    (hrank : 1 < Module.rank ℝ ((ℝ ∙ (v : EuclideanSpace ℂ α))ᗮ)) :
    IsPathConnected ({v}ᶜ ∩ {sphereNeg v}ᶜ : Set (UnitSphere α)) := by
  let proj := stereographic (norm_eq_of_mem_sphere v)
  have himage : proj.toPartialEquiv.symm '' (proj.target \ {0}) =
      {v}ᶜ ∩ {sphereNeg v}ᶜ := by
    rw [PartialEquiv.symm_image_target_minus_singleton_eq_local]
    · rw [stereographic_source]
      congr 2
      calc
        proj.toPartialEquiv.symm 0 =
            proj.toPartialEquiv.symm (proj (-v)) := by
          rw [stereographic_apply_neg]
        _ = -v := proj.left_inv (by
          rw [stereographic_source]
          exact (ne_neg_of_mem_unit_sphere ℝ v).symm)
        _ = sphereNeg v := by rfl
    · rw [stereographic_target]
      exact Set.mem_univ 0
  rw [← himage]
  apply IsPathConnected.image'
  · rw [stereographic_target]
    have hset : (Set.univ \ {0} : Set ((ℝ ∙ (v : EuclideanSpace ℂ α))ᗮ)) = {0}ᶜ := by
      ext x
      simp
    rw [hset]
    exact isPathConnected_compl_singleton_of_one_lt_rank hrank 0
  · exact ContinuousOn.mono proj.continuousOn_invFun Set.sdiff_subset

theorem one_lt_rank_real_orthogonal_unitSphere_fin (n : ℕ)
    (v : UnitSphere (Fin (n + 2))) :
    1 < Module.rank ℝ
      ((ℝ ∙ (v : EuclideanSpace ℂ (Fin (n + 2))))ᗮ) := by
  let E := EuclideanSpace ℂ (Fin (n + 2))
  have htotal : Module.finrank ℝ E = 2 * (n + 2) := by
    calc
      Module.finrank ℝ E =
          Module.finrank ℝ ℂ * Module.finrank ℂ E :=
        (Module.finrank_mul_finrank ℝ ℂ E).symm
      _ = 2 * (n + 2) := by rw [Complex.finrank_real_complex, finrank_euclideanSpace_fin]
  have hv0 : (v : E) ≠ 0 := ne_zero_of_mem_unit_sphere v
  have hspan : Module.finrank ℝ (ℝ ∙ (v : E)) = 1 := by
    rw [finrank_span_singleton hv0]
  have hadd := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ (v : E))
  rw [hspan, htotal] at hadd
  have hfin : 1 < Module.finrank ℝ ((ℝ ∙ (v : E))ᗮ) := by omega
  rw [← Module.finrank_eq_rank]
  exact_mod_cast hfin

def unitaryEmbedSucc (n : ℕ) :
    Matrix.unitaryGroup (Fin n) ℂ →* Matrix.unitaryGroup (Fin (n + 1)) ℂ where
  toFun V := ⟨embedSucc V, Matrix.mem_unitaryGroup_iff.mpr
    (embedSucc_mul_conjTranspose_self (Matrix.UnitaryGroup.star_mul_self V))⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    induction i using Fin.cases with
    | zero =>
        induction j using Fin.cases with
        | zero => simp [Matrix.one_apply]
        | succ j =>
            have hne : (0 : Fin (n + 1)) ≠ j.succ := by
              intro h
              simpa using congrArg Fin.val h
            simp [Matrix.one_apply, hne]
    | succ i => induction j using Fin.cases <;> simp [Matrix.one_apply]
  map_mul' V W := by
    apply Subtype.ext
    ext i j
    induction i using Fin.cases <;> induction j using Fin.cases <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem unitaryEmbedSucc_coe (n : ℕ)
    (V : Matrix.unitaryGroup (Fin n) ℂ) :
    (unitaryEmbedSucc n V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = embedSucc V := rfl

theorem continuous_unitaryEmbedSucc (n : ℕ) : Continuous (unitaryEmbedSucc n) := by
  apply continuous_induced_rng.2
  change Continuous (fun V : Matrix.unitaryGroup (Fin n) ℂ =>
    embedSucc (V : Matrix (Fin n) (Fin n) ℂ))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  induction i using Fin.cases with
  | zero => induction j using Fin.cases <;> simp <;> fun_prop
  | succ i =>
      induction j using Fin.cases with
      | zero => exact continuous_const
      | succ j => simpa using continuous_finiteUnitaryEntry i j

@[simp] theorem unitaryFirstColumn_unitaryEmbedSucc (n : ℕ)
    (V : Matrix.unitaryGroup (Fin n) ℂ) :
    unitaryFirstColumn 0 (unitaryEmbedSucc n V) = basisSphere 0 := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  change ((embedSucc (V : Matrix (Fin n) (Fin n) ℂ)) *ᵥ e 0) i = raw (basisSphere 0).1 i
  rw [raw_basisSphere]
  induction i using Fin.cases <;> simp [Matrix.mulVec, dotProduct, e]

abbrev FirstColumnStabilizer (n : ℕ) :=
  {U : Matrix.unitaryGroup (Fin (n + 1)) ℂ //
    unitaryFirstColumn 0 U = basisSphere 0}

def stabilizerTail (n : ℕ) (U : FirstColumnStabilizer n) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => U.1 i.succ j.succ

theorem stabilizer_zero_succ (n : ℕ) (U : FirstColumnStabilizer n) (j : Fin n) :
    (U.1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 j.succ = 0 := by
  have hstar := Matrix.UnitaryGroup.star_mul_self U.1
  have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => M 0 j.succ) hstar
  have hcol : ∀ k : Fin (n + 1),
      (U.1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) k 0 = if k = 0 then 1 else 0 := by
    intro k
    have h' := congrArg (fun x : UnitSphere (Fin (n + 1)) => raw x.1 k) U.2
    rw [raw_unitaryFirstColumn_apply, raw_basisSphere] at h'
    exact h'
  have h' : (U.1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 j.succ =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 j.succ := by
    simpa [Matrix.mul_apply, Matrix.star_apply, hcol, Fin.sum_univ_succ] using h
  have hne : (0 : Fin (n + 1)) ≠ j.succ := by
    intro hzero
    simpa using congrArg Fin.val hzero
  simpa [Matrix.one_apply, hne] using h'

theorem stabilizerTail_star_mul_self (n : ℕ) (U : FirstColumnStabilizer n) :
    (stabilizerTail n U)ᴴ * stabilizerTail n U = 1 := by
  have hstar := Matrix.UnitaryGroup.star_mul_self U.1
  ext i j
  have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => M i.succ j.succ) hstar
  simp only [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_succ] at h
  rw [stabilizer_zero_succ n U i] at h
  simpa [stabilizerTail, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_succ,
    Matrix.one_apply] using h

def stabilizerTailUnitary (n : ℕ) (U : FirstColumnStabilizer n) :
    Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨stabilizerTail n U, Matrix.mem_unitaryGroup_iff.mpr
    (mul_eq_one_comm.mp (stabilizerTail_star_mul_self n U))⟩

theorem unitaryEmbedSucc_stabilizerTail (n : ℕ) (U : FirstColumnStabilizer n) :
    unitaryEmbedSucc n (stabilizerTailUnitary n U) = U.1 := by
  apply Subtype.ext
  ext i j
  induction i using Fin.cases with
  | zero =>
      induction j using Fin.cases with
      | zero =>
          have h := congrArg (fun x : UnitSphere (Fin (n + 1)) => raw x.1 0) U.2
          rw [raw_unitaryFirstColumn_apply, raw_basisSphere] at h
          exact h.symm
      | succ j => simpa using (stabilizer_zero_succ n U j).symm
  | succ i =>
      induction j using Fin.cases with
      | zero =>
          have h := congrArg (fun x : UnitSphere (Fin (n + 1)) => raw x.1 i.succ) U.2
          rw [raw_unitaryFirstColumn_apply, raw_basisSphere] at h
          exact h.symm
      | succ j => simp [unitaryEmbedSucc, stabilizerTailUnitary, stabilizerTail]

@[simp] theorem stabilizerTailUnitary_unitaryEmbedSucc (n : ℕ)
    (V : Matrix.unitaryGroup (Fin n) ℂ) :
    stabilizerTailUnitary n
      ⟨unitaryEmbedSucc n V, unitaryFirstColumn_unitaryEmbedSucc n V⟩ = V := by
  apply Subtype.ext
  ext i j
  simp [stabilizerTailUnitary, stabilizerTail, unitaryEmbedSucc]

def unitaryEmbedSuccStabilizer (n : ℕ)
    (V : Matrix.unitaryGroup (Fin n) ℂ) : FirstColumnStabilizer n :=
  ⟨unitaryEmbedSucc n V, unitaryFirstColumn_unitaryEmbedSucc n V⟩

theorem continuous_unitaryEmbedSuccStabilizer (n : ℕ) :
    Continuous (unitaryEmbedSuccStabilizer n) := by
  apply continuous_induced_rng.2
  exact continuous_unitaryEmbedSucc n

theorem continuous_stabilizerTailUnitary (n : ℕ) :
    Continuous (stabilizerTailUnitary n) := by
  apply continuous_induced_rng.2
  change Continuous (fun U : FirstColumnStabilizer n => stabilizerTail n U)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_finiteUnitaryEntry i.succ j.succ).comp
    continuous_subtype_val

noncomputable def unitaryStabilizerHomeomorph (n : ℕ) :
    Matrix.unitaryGroup (Fin n) ℂ ≃ₜ FirstColumnStabilizer n where
  toFun := unitaryEmbedSuccStabilizer n
  invFun := stabilizerTailUnitary n
  left_inv := stabilizerTailUnitary_unitaryEmbedSucc n
  right_inv U := Subtype.ext (unitaryEmbedSucc_stabilizerTail n U)
  continuous_toFun := continuous_unitaryEmbedSuccStabilizer n
  continuous_invFun := continuous_stabilizerTailUnitary n

theorem isPathConnected_univ_firstColumnStabilizer (n : ℕ) :
    IsPathConnected (Set.univ : Set (FirstColumnStabilizer n)) := by
  rw [← (unitaryStabilizerHomeomorph n).surjective.range_eq]
  simpa only [Set.image_univ] using
    isPathConnected_univ.image (unitaryStabilizerHomeomorph n).continuous

noncomputable def unitaryWithFirstColumn (m : ℕ)
    (x : UnitSphere (Fin (m + 1))) : Matrix.unitaryGroup (Fin (m + 1)) ℂ := by
  let h := exists_unitary_firstColumn (raw x.1) (norm_eq_of_mem_sphere x)
  exact ⟨Classical.choose h, Matrix.mem_unitaryGroup_iff.mpr
    (Classical.choose_spec h).2.1⟩

@[simp] theorem unitaryFirstColumn_unitaryWithFirstColumn (m : ℕ)
    (x : UnitSphere (Fin (m + 1))) :
    unitaryFirstColumn 0 (unitaryWithFirstColumn m x) = x := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  change raw (unitaryFirstColumn 0 (unitaryWithFirstColumn m x)).1 i = raw x.1 i
  rw [raw_unitaryFirstColumn_apply]
  exact (Classical.choose_spec
    (exists_unitary_firstColumn (raw x.1) (norm_eq_of_mem_sphere x))).2.2 i

def transverseIndex (n : ℕ) : Fin (n + 2) := ⟨1, by omega⟩

def transverseSphere (n : ℕ) : UnitSphere (Fin (n + 2)) := basisSphere (transverseIndex n)

noncomputable def transverseUnitary (n : ℕ) :
    Matrix.unitaryGroup (Fin (n + 2)) ℂ :=
  unitaryWithFirstColumn (n + 1) (transverseSphere n)

noncomputable def negativeTransverseUnitary (n : ℕ) :
    Matrix.unitaryGroup (Fin (n + 2)) ℂ :=
  unitaryWithFirstColumn (n + 1) (sphereNeg (transverseSphere n))

@[simp] theorem transverseUnitary_firstColumn (n : ℕ) :
    unitaryFirstColumn 0 (transverseUnitary n) = transverseSphere n :=
  unitaryFirstColumn_unitaryWithFirstColumn _ _

@[simp] theorem negativeTransverseUnitary_firstColumn (n : ℕ) :
    unitaryFirstColumn 0 (negativeTransverseUnitary n) = sphereNeg (transverseSphere n) :=
  unitaryFirstColumn_unitaryWithFirstColumn _ _

theorem unitaryFirstColumn_mul_of_right_stabilizes (a0 : α)
    (U V : Matrix.unitaryGroup α ℂ)
    (hV : unitaryFirstColumn a0 V = basisSphere a0) :
    unitaryFirstColumn a0 (U * V) = unitaryFirstColumn a0 U := by
  rw [unitaryFirstColumn_eq_action, unitarySphereAction_mul,
    ← unitaryFirstColumn_eq_action, hV, ← unitaryFirstColumn_eq_action]

theorem unitaryFirstColumn_inv_of_stabilizes (a0 : α)
    (U : Matrix.unitaryGroup α ℂ)
    (hU : unitaryFirstColumn a0 U = basisSphere a0) :
    unitaryFirstColumn a0 U⁻¹ = basisSphere a0 := by
  have hmul := unitaryFirstColumn_mul_of_right_stabilizes a0 U⁻¹ U hU
  change unitaryFirstColumn a0 U⁻¹ = unitaryFirstColumn a0 1
  simpa using hmul.symm

def chartBase (a0 : α) (R : Matrix.unitaryGroup α ℂ)
    (hbase : basisSphere a0 ≠ sphereNeg (unitaryFirstColumn a0 R)) :
    SphereChart a0 R := ⟨basisSphere a0, hbase⟩

def normalizedRotatedCompletion (a0 : α) (R : Matrix.unitaryGroup α ℂ)
    (hbase : basisSphere a0 ≠ sphereNeg (unitaryFirstColumn a0 R))
    (x : SphereChart a0 R) : Matrix.unitaryGroup α ℂ :=
  rotatedCompletion a0 R x * (rotatedCompletion a0 R (chartBase a0 R hbase))⁻¹

theorem continuous_normalizedRotatedCompletion (a0 : α)
    (R : Matrix.unitaryGroup α ℂ)
    (hbase : basisSphere a0 ≠ sphereNeg (unitaryFirstColumn a0 R)) :
    Continuous (normalizedRotatedCompletion a0 R hbase) := by
  exact (continuous_rotatedCompletion a0 R).mul continuous_const

@[simp] theorem normalizedRotatedCompletion_base (a0 : α)
    (R : Matrix.unitaryGroup α ℂ)
    (hbase : basisSphere a0 ≠ sphereNeg (unitaryFirstColumn a0 R)) :
    normalizedRotatedCompletion a0 R hbase (chartBase a0 R hbase) = 1 := by
  simp [normalizedRotatedCompletion]

@[simp] theorem normalizedRotatedCompletion_firstColumn (a0 : α)
    (R : Matrix.unitaryGroup α ℂ)
    (hbase : basisSphere a0 ≠ sphereNeg (unitaryFirstColumn a0 R))
    (x : SphereChart a0 R) :
    unitaryFirstColumn a0 (normalizedRotatedCompletion a0 R hbase x) = x.1 := by
  apply (unitaryFirstColumn_mul_of_right_stabilizes a0 _ _ ?_).trans
  · exact rotatedCompletion_firstColumn a0 R x
  · apply unitaryFirstColumn_inv_of_stabilizes
    exact rotatedCompletion_firstColumn a0 R (chartBase a0 R hbase)

theorem basisSphere_zero_ne_transverseSphere (n : ℕ) :
    basisSphere (0 : Fin (n + 2)) ≠ transverseSphere n := by
  intro h
  have h0 := congrArg (fun x : UnitSphere (Fin (n + 2)) => raw x.1 0) h
  simpa [transverseSphere, transverseIndex, e] using h0

theorem basisSphere_zero_ne_neg_transverseSphere (n : ℕ) :
    basisSphere (0 : Fin (n + 2)) ≠ sphereNeg (transverseSphere n) := by
  intro h
  have h0 := congrArg (fun x : UnitSphere (Fin (n + 2)) => raw x.1 0) h
  simpa [transverseSphere, transverseIndex, e] using h0

theorem transverseSphere_ne_neg (n : ℕ) :
    transverseSphere n ≠ sphereNeg (transverseSphere n) := by
  exact ne_neg_of_mem_unit_sphere ℝ (transverseSphere n)

noncomputable instance firstColumnStabilizerPathConnectedSpace (n : ℕ) :
    PathConnectedSpace (FirstColumnStabilizer n) where
  nonempty := ⟨unitaryEmbedSuccStabilizer n 1⟩
  joined U V := by
    let p := PathConnectedSpace.somePath
      ((unitaryStabilizerHomeomorph n).symm U)
      ((unitaryStabilizerHomeomorph n).symm V)
    exact ⟨by simpa using p.map (unitaryStabilizerHomeomorph n).continuous⟩

theorem unitaryFirstColumn_mul (a0 : α)
    (U V : Matrix.unitaryGroup α ℂ) :
    unitaryFirstColumn a0 (U * V) =
      unitarySphereAction U (unitaryFirstColumn a0 V) := by
  rw [unitaryFirstColumn_eq_action, unitarySphereAction_mul,
    ← unitaryFirstColumn_eq_action]

theorem unitaryFirstColumn_inv_mul_eq_basis (a0 : α)
    (S U : Matrix.unitaryGroup α ℂ) (x : UnitSphere α)
    (hS : unitaryFirstColumn a0 S = x)
    (hU : unitaryFirstColumn a0 U = x) :
    unitaryFirstColumn a0 (S⁻¹ * U) = basisSphere a0 := by
  calc
    unitaryFirstColumn a0 (S⁻¹ * U) =
        unitarySphereAction S⁻¹ (unitaryFirstColumn a0 U) :=
      unitaryFirstColumn_mul a0 S⁻¹ U
    _ = unitarySphereAction S⁻¹ (unitaryFirstColumn a0 S) := by rw [hU, hS]
    _ = unitaryFirstColumn a0 (S⁻¹ * S) :=
      (unitaryFirstColumn_mul a0 S⁻¹ S).symm
    _ = basisSphere a0 := by simp [basisSphere]

def chartParam (n : ℕ) (R : Matrix.unitaryGroup (Fin (n + 2)) ℂ)
    (s : Set (UnitSphere (Fin (n + 2))))
    (hsub : s ⊆ {sphereNeg (unitaryFirstColumn 0 R)}ᶜ)
    (z : s × FirstColumnStabilizer (n + 1)) :
    Matrix.unitaryGroup (Fin (n + 2)) ℂ :=
  rotatedCompletion 0 R ⟨z.1.1, hsub z.1.2⟩ * z.2.1

theorem continuous_chartParam (n : ℕ)
    (R : Matrix.unitaryGroup (Fin (n + 2)) ℂ)
    (s : Set (UnitSphere (Fin (n + 2))))
    (hsub : s ⊆ {sphereNeg (unitaryFirstColumn 0 R)}ᶜ) :
    Continuous (chartParam n R s hsub) := by
  apply Continuous.mul
  · apply (continuous_rotatedCompletion 0 R).comp
    exact Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_fst) _
  · exact continuous_subtype_val.comp continuous_snd

def chartParamToPreimage (n : ℕ)
    (R : Matrix.unitaryGroup (Fin (n + 2)) ℂ)
    (s : Set (UnitSphere (Fin (n + 2))))
    (hsub : s ⊆ {sphereNeg (unitaryFirstColumn 0 R)}ᶜ)
    (z : s × FirstColumnStabilizer (n + 1)) :
    (unitaryFirstColumn 0 ⁻¹' s : Set (Matrix.unitaryGroup (Fin (n + 2)) ℂ)) := by
  refine ⟨chartParam n R s hsub z, ?_⟩
  change unitaryFirstColumn 0 (chartParam n R s hsub z) ∈ s
  rw [chartParam, unitaryFirstColumn_mul_of_right_stabilizes 0 _ _ z.2.2,
    rotatedCompletion_firstColumn]
  exact z.1.2

theorem continuous_chartParamToPreimage (n : ℕ)
    (R : Matrix.unitaryGroup (Fin (n + 2)) ℂ)
    (s : Set (UnitSphere (Fin (n + 2))))
    (hsub : s ⊆ {sphereNeg (unitaryFirstColumn 0 R)}ᶜ) :
    Continuous (chartParamToPreimage n R s hsub) := by
  apply continuous_induced_rng.2
  exact continuous_chartParam n R s hsub

theorem surjective_chartParam (n : ℕ)
    (R : Matrix.unitaryGroup (Fin (n + 2)) ℂ)
    (s : Set (UnitSphere (Fin (n + 2))))
    (hsub : s ⊆ {sphereNeg (unitaryFirstColumn 0 R)}ᶜ) :
    Function.Surjective
      (chartParamToPreimage n R s hsub) := by
  intro U
  let x : s := ⟨unitaryFirstColumn 0 U.1, U.2⟩
  let S : Matrix.unitaryGroup (Fin (n + 2)) ℂ :=
    rotatedCompletion 0 R ⟨x.1, hsub x.2⟩
  have hS : unitaryFirstColumn 0 S = x.1 :=
    rotatedCompletion_firstColumn 0 R ⟨x.1, hsub x.2⟩
  let F : FirstColumnStabilizer (n + 1) :=
    ⟨S⁻¹ * U.1,
      unitaryFirstColumn_inv_mul_eq_basis 0 S U.1 x.1 hS rfl⟩
  refine ⟨(x, F), Subtype.ext ?_⟩
  change S * (S⁻¹ * U.1) = U.1
  simp

theorem unitaryFirstColumn_preimage_isPathConnected (n : ℕ)
    (R : Matrix.unitaryGroup (Fin (n + 2)) ℂ)
    (s : Set (UnitSphere (Fin (n + 2))))
    (hs : IsPathConnected s)
    (hsub : s ⊆ {sphereNeg (unitaryFirstColumn 0 R)}ᶜ) :
    IsPathConnected (unitaryFirstColumn 0 ⁻¹' s) := by
  have hsSpace : PathConnectedSpace s := by
    rw [← isPathConnected_iff_pathConnectedSpace]
    exact hs
  letI := hsSpace
  have hrange : Set.range (chartParam n R s hsub) = unitaryFirstColumn 0 ⁻¹' s := by
    ext U
    constructor
    · rintro ⟨z, rfl⟩
      exact (chartParamToPreimage n R s hsub z).2
    · intro hU
      obtain ⟨z, hz⟩ := surjective_chartParam n R s hsub ⟨U, hU⟩
      exact ⟨z, congrArg Subtype.val hz⟩
  rw [← hrange]
  simpa only [Set.image_univ] using
    isPathConnected_univ.image (continuous_chartParam n R s hsub)

@[simp] theorem sphereNeg_sphereNeg (x : UnitSphere α) :
    sphereNeg (sphereNeg x) = x := by
  apply Subtype.ext
  simp [sphereNeg]

noncomputable def twoChartUnitary (n : ℕ) :
    Bool → Matrix.unitaryGroup (Fin (n + 2)) ℂ
  | false => transverseUnitary n
  | true => negativeTransverseUnitary n

def twoChartSet (n : ℕ) (b : Bool) :
    Set (Matrix.unitaryGroup (Fin (n + 2)) ℂ) :=
  unitaryFirstColumn 0 ⁻¹'
    {sphereNeg (unitaryFirstColumn 0 (twoChartUnitary n b))}ᶜ

theorem isOpen_twoChartSet (n : ℕ) (b : Bool) : IsOpen (twoChartSet n b) := by
  exact isClosed_singleton.isOpen_compl.preimage (continuous_unitaryFirstColumn 0)

theorem one_mem_twoChartSet (n : ℕ) (b : Bool) :
    (1 : Matrix.unitaryGroup (Fin (n + 2)) ℂ) ∈ twoChartSet n b := by
  cases b with
  | false =>
      change basisSphere 0 ≠ sphereNeg (unitaryFirstColumn 0 (transverseUnitary n))
      simpa using basisSphere_zero_ne_neg_transverseSphere n
  | true =>
      change basisSphere 0 ≠ sphereNeg
        (unitaryFirstColumn 0 (negativeTransverseUnitary n))
      simpa using basisSphere_zero_ne_transverseSphere n

theorem twoChartSet_cover (n : ℕ) :
    Set.univ ⊆ ⋃ b : Bool, twoChartSet n b := by
  intro U _
  let x := unitaryFirstColumn 0 U
  by_cases hneg : x ≠ sphereNeg (transverseSphere n)
  · apply Set.mem_iUnion.2
    refine ⟨false, ?_⟩
    simpa [twoChartSet, twoChartUnitary, x] using hneg
  · have hx : x = sphereNeg (transverseSphere n) := Classical.not_not.mp hneg
    have hpos : x ≠ transverseSphere n := by
      rw [hx]
      exact (transverseSphere_ne_neg n).symm
    apply Set.mem_iUnion.2
    refine ⟨true, ?_⟩
    simpa [twoChartSet, twoChartUnitary, x] using hpos

theorem twoChartSet_inter_isPathConnected (n : ℕ) (b c : Bool) :
    IsPathConnected (twoChartSet n b ∩ twoChartSet n c) := by
  have hrank := one_lt_rank_real_orthogonal_unitSphere_fin n (transverseSphere n)
  cases b <;> cases c
  · have h := unitaryFirstColumn_preimage_isPathConnected n (transverseUnitary n)
      ({sphereNeg (transverseSphere n)}ᶜ)
      (unitSphere_isPathConnected_compl_singleton (sphereNeg (transverseSphere n)))
      (by simpa)
    simpa [twoChartSet, twoChartUnitary] using h

  · have hbase : IsPathConnected
        ({sphereNeg (transverseSphere n)}ᶜ ∩ {transverseSphere n}ᶜ :
          Set (UnitSphere (Fin (n + 2)))) := by
      simpa [Set.inter_comm] using
        unitSphere_isPathConnected_compl_antipodes (transverseSphere n) hrank
    have h := unitaryFirstColumn_preimage_isPathConnected n (transverseUnitary n)
      ({sphereNeg (transverseSphere n)}ᶜ ∩ {transverseSphere n}ᶜ)
      hbase (by intro x hx; simpa using hx.1)
    simpa [twoChartSet, twoChartUnitary, Set.preimage_inter] using h
  · have hbase := unitSphere_isPathConnected_compl_antipodes
      (transverseSphere n) hrank
    have h := unitaryFirstColumn_preimage_isPathConnected n (negativeTransverseUnitary n)
      ({transverseSphere n}ᶜ ∩ {sphereNeg (transverseSphere n)}ᶜ)
      hbase (by intro x hx; simpa using hx.1)
    simpa [twoChartSet, twoChartUnitary, Set.preimage_inter] using h
  · have h := unitaryFirstColumn_preimage_isPathConnected n
      (negativeTransverseUnitary n) ({transverseSphere n}ᶜ)
      (unitSphere_isPathConnected_compl_singleton (transverseSphere n)) (by simpa)
    simpa [twoChartSet, twoChartUnitary] using h

theorem twoChartBaseProof (n : ℕ) (b : Bool) :
    basisSphere (0 : Fin (n + 2)) ≠
      sphereNeg (unitaryFirstColumn 0 (twoChartUnitary n b)) := by
  have h := one_mem_twoChartSet n b
  change unitaryFirstColumn 0 (1 : Matrix.unitaryGroup (Fin (n + 2)) ℂ) ≠
    sphereNeg (unitaryFirstColumn 0 (twoChartUnitary n b)) at h
  exact h

noncomputable def firstColumnChartPath (n : ℕ) (b : Bool)
    (D : Path (1 : Matrix.unitaryGroup (Fin (n + 2)) ℂ) 1)
    (hD : Set.range D ⊆ twoChartSet n b) :
    Path (chartBase 0 (twoChartUnitary n b) (twoChartBaseProof n b))
      (chartBase 0 (twoChartUnitary n b) (twoChartBaseProof n b)) where
  toFun t := ⟨unitaryFirstColumn 0 (D t), hD (Set.mem_range_self t)⟩
  continuous_toFun := Continuous.subtype_mk
    ((continuous_unitaryFirstColumn 0).comp D.continuous) _
  source' := by
    apply Subtype.ext
    change unitaryFirstColumn 0 (D 0) = basisSphere 0
    rw [D.source]
    rfl
  target' := by
    apply Subtype.ext
    change unitaryFirstColumn 0 (D 1) = basisSphere 0
    rw [D.target]
    rfl

noncomputable def chartSectionLoop (n : ℕ) (b : Bool)
    (D : Path (1 : Matrix.unitaryGroup (Fin (n + 2)) ℂ) 1)
    (hD : Set.range D ⊆ twoChartSet n b) :
    Path (1 : Matrix.unitaryGroup (Fin (n + 2)) ℂ) 1 where
  toFun t := normalizedRotatedCompletion 0 (twoChartUnitary n b)
    (twoChartBaseProof n b) (firstColumnChartPath n b D hD t)
  continuous_toFun := (continuous_normalizedRotatedCompletion 0 (twoChartUnitary n b)
    (twoChartBaseProof n b)).comp (firstColumnChartPath n b D hD).continuous
  source' := by simp
  target' := by simp

noncomputable def chartFiberLoop (n : ℕ) (b : Bool)
    (D : Path (1 : Matrix.unitaryGroup (Fin (n + 2)) ℂ) 1)
    (hD : Set.range D ⊆ twoChartSet n b) :
    Path (1 : Matrix.unitaryGroup (Fin (n + 2)) ℂ) 1 where
  toFun t := (chartSectionLoop n b D hD t)⁻¹ * D t
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

theorem chartFiberLoop_stabilizes (n : ℕ) (b : Bool)
    (D : Path (1 : Matrix.unitaryGroup (Fin (n + 2)) ℂ) 1)
    (hD : Set.range D ⊆ twoChartSet n b) (t : unitInterval) :
    unitaryFirstColumn 0 (chartFiberLoop n b D hD t) = basisSphere 0 := by
  apply unitaryFirstColumn_inv_mul_eq_basis 0
    (chartSectionLoop n b D hD t) (D t) (unitaryFirstColumn 0 (D t))
  · change unitaryFirstColumn 0
      (normalizedRotatedCompletion 0 (twoChartUnitary n b)
        (twoChartBaseProof n b) (firstColumnChartPath n b D hD t)) = _
    exact normalizedRotatedCompletion_firstColumn 0 (twoChartUnitary n b)
      (twoChartBaseProof n b) (firstColumnChartPath n b D hD t)
  · rfl

noncomputable def chartStabilizerLoop (n : ℕ) (b : Bool)
    (D : Path (1 : Matrix.unitaryGroup (Fin (n + 2)) ℂ) 1)
    (hD : Set.range D ⊆ twoChartSet n b) :
    Path (unitaryEmbedSuccStabilizer (n + 1) 1)
      (unitaryEmbedSuccStabilizer (n + 1) 1) := by
  let p : Path (unitaryEmbedSuccStabilizer (n + 1) 1)
      (unitaryEmbedSuccStabilizer (n + 1) 1) :=
    { toFun := fun t =>
        ⟨chartFiberLoop n b D hD t, chartFiberLoop_stabilizes n b D hD t⟩
      continuous_toFun := Continuous.subtype_mk (chartFiberLoop n b D hD).continuous _
      source' := by
        apply Subtype.ext
        change chartFiberLoop n b D hD 0 = unitaryEmbedSucc (n + 1) 1
        simp
      target' := by
        apply Subtype.ext
        change chartFiberLoop n b D hD 1 = unitaryEmbedSucc (n + 1) 1
        simp }
  exact p

noncomputable def chartLowerLoop (n : ℕ) (b : Bool)
    (D : Path (1 : Matrix.unitaryGroup (Fin (n + 2)) ℂ) 1)
    (hD : Set.range D ⊆ twoChartSet n b) :
    Path (1 : Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1 := by
  let p := (chartStabilizerLoop n b D hD).map
    (continuous_stabilizerTailUnitary (n + 1))
  have hbase : stabilizerTailUnitary (n + 1)
      (unitaryEmbedSuccStabilizer (n + 1) 1) = 1 :=
    stabilizerTailUnitary_unitaryEmbedSucc (n + 1) 1
  exact p.cast hbase hbase

noncomputable def embeddedChartLowerLoop (n : ℕ) (b : Bool)
    (D : Path (1 : Matrix.unitaryGroup (Fin (n + 2)) ℂ) 1)
    (hD : Set.range D ⊆ twoChartSet n b) :
    Path (1 : Matrix.unitaryGroup (Fin (n + 2)) ℂ) 1 where
  toFun t := unitaryEmbedSucc (n + 1) (chartLowerLoop n b D hD t)
  continuous_toFun := (continuous_unitaryEmbedSucc (n + 1)).comp
    (chartLowerLoop n b D hD).continuous
  source' := by simp
  target' := by simp

theorem embeddedChartLowerLoop_eq_chartFiberLoop (n : ℕ) (b : Bool)
    (D : Path (1 : Matrix.unitaryGroup (Fin (n + 2)) ℂ) 1)
    (hD : Set.range D ⊆ twoChartSet n b) :
    embeddedChartLowerLoop n b D hD = chartFiberLoop n b D hD := by
  ext t i j
  change ((unitaryEmbedSucc (n + 1)
      (stabilizerTailUnitary (n + 1)
        ⟨chartFiberLoop n b D hD t, chartFiberLoop_stabilizes n b D hD t⟩) :
      Matrix.unitaryGroup (Fin (n + 2)) ℂ) :
      Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) i j =
    (chartFiberLoop n b D hD t : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) i j
  have h := congrArg Subtype.val (unitaryEmbedSucc_stabilizerTail (n + 1)
    ⟨chartFiberLoop n b D hD t, chartFiberLoop_stabilizes n b D hD t⟩)
  exact congrFun (congrFun h i) j

theorem chartSectionLoop_nullhomotopic (n : ℕ) (b : Bool)
    (D : Path (1 : Matrix.unitaryGroup (Fin (n + 2)) ℂ) 1)
    (hD : Set.range D ⊆ twoChartSet n b) :
    (chartSectionLoop n b D hD).Homotopic (Path.refl 1) := by
  let R := twoChartUnitary n b
  let p := sphereNeg (unitaryFirstColumn 0 R)
  letI : ContractibleSpace (SphereChart 0 R) := by
    letI := unitSphere_compl_singleton_contractible p
    have hset : {x : UnitSphere (Fin (n + 2)) | x ≠ p} = {p}ᶜ := by
      ext x
      simp
    exact Homeomorph.contractibleSpace (Homeomorph.setCongr hset)
  letI : SimplyConnectedSpace (SphereChart 0 R) :=
    SimplyConnectedSpace.ofContractible _
  have hsimple : IsSimplyConnected (Set.univ : Set (SphereChart 0 R)) := by
    rw [IsSimplyConnected]
    exact (Homeomorph.Set.univ (SphereChart 0 R)).toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨H, -⟩ :=
    (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hsimple).2
      (chartBase 0 R (twoChartBaseProof n b))
      (firstColumnChartPath n b D hD) (by simp)
  let f : C(SphereChart 0 R, Matrix.unitaryGroup (Fin (n + 2)) ℂ) :=
    ⟨normalizedRotatedCompletion 0 R (twoChartBaseProof n b),
      continuous_normalizedRotatedCompletion 0 R (twoChartBaseProof n b)⟩
  let Kmap : C(unitInterval × unitInterval,
      Matrix.unitaryGroup (Fin (n + 2)) ℂ) :=
    ⟨fun st => f (H.toFun st), f.continuous.comp H.continuous⟩
  let K : (chartSectionLoop n b D hD).toContinuousMap.Homotopy
      (Path.refl 1).toContinuousMap :=
    { toContinuousMap := Kmap
      map_zero_left := by
        intro t
        exact congrArg f (H.map_zero_left t)
      map_one_left := by
        intro t
        calc
          f (H.toFun (1, t)) = f (chartBase 0 R (twoChartBaseProof n b)) :=
            congrArg f (H.map_one_left t)
          _ = 1 := normalizedRotatedCompletion_base 0 R (twoChartBaseProof n b)
          _ = Path.refl 1 t := rfl }
  refine ⟨K, ?_⟩
  intro t z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · calc
      f (H.toFun (t, 0)) = f (firstColumnChartPath n b D hD 0) :=
        congrArg f (H.prop' t 0 (by simp))
      _ = f (chartBase 0 R (twoChartBaseProof n b)) :=
        congrArg f (firstColumnChartPath n b D hD).source
      _ = 1 := normalizedRotatedCompletion_base 0 R (twoChartBaseProof n b)
      _ = chartSectionLoop n b D hD 0 := (chartSectionLoop n b D hD).source.symm
  · calc
      f (H.toFun (t, 1)) = f (firstColumnChartPath n b D hD 1) :=
        congrArg f (H.prop' t 1 (by simp))
      _ = f (chartBase 0 R (twoChartBaseProof n b)) :=
        congrArg f (firstColumnChartPath n b D hD).target
      _ = 1 := normalizedRotatedCompletion_base 0 R (twoChartBaseProof n b)
      _ = chartSectionLoop n b D hD 1 := (chartSectionLoop n b D hD).target.symm

noncomputable local instance finiteUnitaryFundamentalGroupCommGroup (m : ℕ) :
    CommGroup (FundamentalGroup (Matrix.unitaryGroup (Fin m) ℂ) 1) :=
  fundamentalGroupCommGroup

theorem chartLoop_class_eq_embeddedLower (n : ℕ) (b : Bool)
    (D : Path (1 : Matrix.unitaryGroup (Fin (n + 2)) ℂ) 1)
    (hD : Set.range D ⊆ twoChartSet n b) :
    Path.Homotopic.Quotient.mk D =
      Path.Homotopic.Quotient.mk (embeddedChartLowerLoop n b D hD) := by
  let S := chartSectionLoop n b D hD
  let F := chartFiberLoop n b D hD
  have hfactor : D = loopPointwiseMulPath S F := by
    ext t i j
    simp [S, F, loopPointwiseMulPath, chartFiberLoop]
  rcases chartSectionLoop_nullhomotopic n b D hD with ⟨HS⟩
  have hprod : (loopPointwiseMulPath S F).Homotopic
      (loopPointwiseMulPath
        (Path.refl (1 : Matrix.unitaryGroup (Fin (n + 2)) ℂ)) F) :=
    ⟨loopPointwiseMulHomotopy HS (Path.Homotopy.refl F)⟩
  have hunit : loopPointwiseMulPath
      (Path.refl (1 : Matrix.unitaryGroup (Fin (n + 2)) ℂ)) F = F := by
    ext t i j
    simp [loopPointwiseMulPath]
  exact (congrArg Path.Homotopic.Quotient.mk hfactor).trans
    ((Path.Homotopic.Quotient.eq.mpr hprod).trans
      ((congrArg Path.Homotopic.Quotient.mk hunit).trans
        (congrArg Path.Homotopic.Quotient.mk
          (embeddedChartLowerLoop_eq_chartFiberLoop n b D hD).symm)))

def unitaryEmbedSuccPath (n : ℕ)
    (p : Path (1 : Matrix.unitaryGroup (Fin n) ℂ) 1) :
    Path (1 : Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1 where
  toFun t := unitaryEmbedSucc n (p t)
  continuous_toFun := (continuous_unitaryEmbedSucc n).comp p.continuous
  source' := by simp
  target' := by simp

theorem unitaryEmbedSuccPath_homotopic (n : ℕ)
    {p q : Path (1 : Matrix.unitaryGroup (Fin n) ℂ) 1}
    (hpq : p.Homotopic q) :
    (unitaryEmbedSuccPath n p).Homotopic (unitaryEmbedSuccPath n q) := by
  rcases hpq with ⟨H⟩
  refine ⟨{
    toFun := fun z => unitaryEmbedSucc n (H z)
    continuous_toFun := (continuous_unitaryEmbedSucc n).comp H.continuous
    map_zero_left := fun t => congrArg (unitaryEmbedSucc n) (H.map_zero_left t)
    map_one_left := fun t => congrArg (unitaryEmbedSucc n) (H.map_one_left t)
    prop' := fun t z hz => congrArg (unitaryEmbedSucc n) (H.prop' t z hz) }⟩

noncomputable def unitaryEmbedSuccFundamentalGroupMap (n : ℕ) :
    FundamentalGroup (Matrix.unitaryGroup (Fin n) ℂ) 1 →
      FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1 :=
  Quotient.map (unitaryEmbedSuccPath n)
    (fun _ _ h => unitaryEmbedSuccPath_homotopic n h)

theorem unitaryEmbedSuccPath_trans (n : ℕ)
    (p q : Path (1 : Matrix.unitaryGroup (Fin n) ℂ) 1) :
    unitaryEmbedSuccPath n (p.trans q) =
      (unitaryEmbedSuccPath n p).trans (unitaryEmbedSuccPath n q) := by
  ext t i j
  simp only [unitaryEmbedSuccPath, Path.trans_apply, Path.coe_mk_mk]
  split_ifs <;> rfl

theorem unitaryEmbedSuccFundamentalGroupMap_range_trans (n : ℕ)
    {x y : FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1}
    (hx : x ∈ Set.range (unitaryEmbedSuccFundamentalGroupMap n))
    (hy : y ∈ Set.range (unitaryEmbedSuccFundamentalGroupMap n)) :
    x.trans y ∈ Set.range (unitaryEmbedSuccFundamentalGroupMap n) := by
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hy
  induction x', y' using Path.Homotopic.Quotient.ind₂ with
  | mk p q =>
      refine ⟨Path.Homotopic.Quotient.mk (p.trans q), ?_⟩
      change Path.Homotopic.Quotient.mk (unitaryEmbedSuccPath n (p.trans q)) =
        (Path.Homotopic.Quotient.mk (unitaryEmbedSuccPath n p)).trans
          (Path.Homotopic.Quotient.mk (unitaryEmbedSuccPath n q))
      rw [unitaryEmbedSuccPath_trans, Path.Homotopic.Quotient.mk_trans]

theorem chartLoop_class_mem_unitaryEmbedSucc_range (n : ℕ) (b : Bool)
    (D : Path (1 : Matrix.unitaryGroup (Fin (n + 2)) ℂ) 1)
    (hD : Set.range D ⊆ twoChartSet n b) :
    Path.Homotopic.Quotient.mk D ∈
      Set.range (unitaryEmbedSuccFundamentalGroupMap (n + 1)) := by
  refine ⟨Path.Homotopic.Quotient.mk (chartLowerLoop n b D hD), ?_⟩
  change Path.Homotopic.Quotient.mk (unitaryEmbedSuccPath (n + 1)
      (chartLowerLoop n b D hD)) = Path.Homotopic.Quotient.mk D
  have hpath : unitaryEmbedSuccPath (n + 1) (chartLowerLoop n b D hD) =
      embeddedChartLowerLoop n b D hD := by
    ext t i j
    rfl
  rw [hpath]
  exact (chartLoop_class_eq_embeddedLower n b D hD).symm

theorem concat_loop_classes_mem_unitaryEmbedSucc_range (n : ℕ) :
    ∀ (m : ℕ)
      (D : Fin (m + 1) → Path (1 : Matrix.unitaryGroup (Fin (n + 2)) ℂ) 1),
      (∀ k, Path.Homotopic.Quotient.mk (D k) ∈
        Set.range (unitaryEmbedSuccFundamentalGroupMap (n + 1))) →
      Path.Homotopic.Quotient.mk (Path.concat (fun _ => 1) D) ∈
        Set.range (unitaryEmbedSuccFundamentalGroupMap (n + 1)) := by
  intro m
  induction m with
  | zero =>
      intro D hD
      have hbase := hD 0
      have heq : Path.Homotopic.Quotient.mk (Path.concat (fun _ => 1) D) =
          Path.Homotopic.Quotient.mk (D 0) := by
        apply Path.Homotopic.Quotient.eq.mpr
        simp only [Path.concat_succ, Path.concat_zero]
        exact ⟨Path.Homotopy.reflTrans _⟩
      rw [heq]
      exact hbase
  | succ m ih =>
      intro D hD
      rw [Path.concat_succ]
      change (Path.Homotopic.Quotient.mk
          ((Path.concat (fun _ => 1) (fun k => D k.castSucc)).trans
            (D (Fin.last (m + 1)))) :
        FundamentalGroup (Matrix.unitaryGroup (Fin (n + 2)) ℂ) 1) ∈
          Set.range (unitaryEmbedSuccFundamentalGroupMap (n + 1))
      rw [Path.Homotopic.Quotient.mk_trans]
      apply unitaryEmbedSuccFundamentalGroupMap_range_trans (n + 1)
      · apply ih
        intro k
        exact hD k.castSucc
      · exact hD (Fin.last (m + 1))

theorem unitaryEmbedSuccFundamentalGroupMap_surjective (n : ℕ) :
    Function.Surjective (unitaryEmbedSuccFundamentalGroupMap (n + 1)) := by
  intro q
  induction q using Path.Homotopic.Quotient.ind with
  | mk γ =>
      obtain ⟨m, D, hD, hRange⟩ := exists_loops_homotopic_concat_of_open_cover
        (isOpen_twoChartSet n) (twoChartSet_cover n)
        (twoChartSet_inter_isPathConnected n) (one_mem_twoChartSet n) γ
      choose b hb using hRange
      have hconcat := concat_loop_classes_mem_unitaryEmbedSucc_range n m D
        (fun k => chartLoop_class_mem_unitaryEmbedSucc_range n (b k) (D k) (hb k))
      have heq : Path.Homotopic.Quotient.mk (Path.concat (fun _ => 1) D) =
          Path.Homotopic.Quotient.mk γ := Path.Homotopic.Quotient.eq.mpr hD
      rw [heq] at hconcat
      exact hconcat

@[simp] theorem det_embedSucc (n : ℕ) (V : Matrix (Fin n) (Fin n) ℂ) :
    (embedSucc V).det = V.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hzero : ∀ j : Fin n,
      (-1 : ℂ) ^ ((j.succ : Fin (n + 1)) : ℕ) * (embedSucc V) 0 j.succ *
        ((embedSucc V).submatrix Fin.succ (Fin.succAbove j.succ)).det = 0 := by
    intro j
    rw [embedSucc_zero_succ, mul_zero, zero_mul]
  rw [Finset.sum_congr rfl fun j _ => hzero j, Finset.sum_const_zero, add_zero,
    Fin.succAbove_zero]
  norm_num [embedSucc_zero_zero]
  apply congrArg Matrix.det
  ext i j
  rfl

end

end FiniteUnitaryStabilization

end GaloisForLFunctions.HTGeometry
