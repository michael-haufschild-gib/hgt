import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicGradedCoefficient

/-!
# Actual homogeneous defect classes and their attained physical norm

Residuals are quotiented by equality of the missing coefficient. This relation
is proved equivalent to their difference being available in the cusp algebra,
so it is exactly the homogeneous observation quotient. Its norm is defined as
the infimum of physical capacities of representatives. Every class attains that
infimum, which equals the positive recovery gap times its absolute coefficient.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial


/-- Residuals modulo equality of their missing coefficient. -/
def cubicGradedDefect (k : ℕ) : Type := Quotient (Setoid.ker (cubicGradedCoefficient k))

def cubicGradedDefectMk (k : ℕ) (P : cubicHomogeneousSpace (k+1)) : cubicGradedDefect k :=
  Quotient.mk (Setoid.ker (cubicGradedCoefficient k)) P

def cubicGradedDefectCoordinate (k : ℕ) : cubicGradedDefect k → ℝ :=
  Quotient.lift (fun P : cubicHomogeneousSpace (k+1) => cubicGradedCoefficient k P) (fun _ _ h => h)

theorem cubicGradedDefectCoordinate_mk (k : ℕ) (P : cubicHomogeneousSpace (k+1)) :
    cubicGradedDefectCoordinate k (cubicGradedDefectMk k P)=cubicGradedCoefficient k P := rfl

theorem cubicGradedDefectMk_eq (k : ℕ) (P Q : cubicHomogeneousSpace (k+1)) :
    cubicGradedDefectMk k P=cubicGradedDefectMk k Q ↔ P.val-Q.val ∈ cubicCuspAlgebra := by
  have hsub : cubicGradedCoefficient k (P-Q)=cubicGradedCoefficient k P-cubicGradedCoefficient k Q := by
    change (((P.val-Q.val).coeff (k+1-k)).coeff k)=
      (P.val.coeff (k+1-k)).coeff k-(Q.val.coeff (k+1-k)).coeff k
    rw [Polynomial.coeff_sub,Polynomial.coeff_sub]
  constructor
  · intro h
    have hc := congrArg (cubicGradedDefectCoordinate k) h
    rw [cubicGradedDefectCoordinate_mk,cubicGradedDefectCoordinate_mk] at hc
    have hz : cubicGradedCoefficient k (P-Q)=0 := by rw [hsub,hc,sub_self]
    exact (cubicGradedAvailable_mem k (P-Q)).mp hz
  · intro h
    have hz : cubicGradedCoefficient k (P-Q)=0 := (cubicGradedAvailable_mem k (P-Q)).mpr h
    rw [hsub] at hz
    exact Quotient.sound (sub_eq_zero.mp hz)

def cubicGradedDefectEquiv (k : ℕ) : cubicGradedDefect k ≃ ℝ where
  toFun := cubicGradedDefectCoordinate k
  invFun r := cubicGradedDefectMk k (r • cubicHomogeneousMissing k)
  left_inv x := by
    refine Quotient.inductionOn x ?_
    intro P
    apply Quotient.sound
    change cubicGradedCoefficient k (cubicGradedCoefficient k P • cubicHomogeneousMissing k)=cubicGradedCoefficient k P
    rw [map_smul,cubicGradedCoefficient_missing,smul_eq_mul,mul_one]
  right_inv r := by
    change cubicGradedCoefficient k (r • cubicHomogeneousMissing k)=r
    rw [map_smul,cubicGradedCoefficient_missing,smul_eq_mul,mul_one]

def cubicGradedRepresentativeValues (k : ℕ) (x : cubicGradedDefect k) : Set ℝ :=
  cubicHomogeneousCapacity (k+1) '' {P : cubicHomogeneousSpace (k+1) | cubicGradedDefectMk k P=x}

def cubicGradedDefectNorm (k : ℕ) (x : cubicGradedDefect k) : ℝ :=
  sInf (cubicGradedRepresentativeValues k x)

theorem cubicGradedRepresentativeValues_isLeast (k : ℕ) (x : cubicGradedDefect k) :
    IsLeast (cubicGradedRepresentativeValues k x)
      (|cubicGradedDefectCoordinate k x| * cubicGradedRecoveryGap k) := by
  obtain ⟨P,hP,hcap⟩ := cubicGradedCoefficient_sharpAttainment k (cubicGradedDefectCoordinate k x)
  constructor
  · refine ⟨P,?_,hcap⟩
    apply (cubicGradedDefectEquiv k).injective
    exact hP
  · rintro y ⟨Q,hQ,rfl⟩
    have he := congrArg (cubicGradedDefectCoordinate k) hQ
    rw [cubicGradedDefectCoordinate_mk] at he
    have hb := cubicGradedCoefficient_sharpBound k Q
    rw [he] at hb
    exact hb

theorem cubicGradedDefectNorm_eq (k : ℕ) (x : cubicGradedDefect k) :
    cubicGradedDefectNorm k x=|cubicGradedDefectCoordinate k x| * cubicGradedRecoveryGap k :=
  (cubicGradedRepresentativeValues_isLeast k x).csInf_eq

theorem cubicGradedDefectNorm_attained (k : ℕ) (x : cubicGradedDefect k) :
    ∃ P : cubicHomogeneousSpace (k+1), cubicGradedDefectMk k P=x ∧
      cubicHomogeneousCapacity (k+1) P=cubicGradedDefectNorm k x := by
  have h := (cubicGradedRepresentativeValues_isLeast k x).1
  rw [← cubicGradedDefectNorm_eq] at h
  exact h

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
