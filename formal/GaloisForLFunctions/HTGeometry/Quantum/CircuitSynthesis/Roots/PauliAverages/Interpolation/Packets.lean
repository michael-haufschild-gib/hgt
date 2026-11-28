import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension
import GaloisForLFunctions.HTGeometry.TorsionPolygonRecurrenceShadowing
import GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
import Mathlib.Tactic

/-! # Spectral phase packets in a fixed unitary basis -/

open Matrix Complex
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Interpolation
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

def phaseValue (t : ℝ) : ℂ := Complex.exp ((t:ℂ)*Complex.I)

def inBasis (V : unitary (Mat I)) (A : Mat I) := V.val*A*star V.val

def packet (V : unitary (Mat I)) (θ : I → ℝ) := inBasis V (diagonal fun i => phaseValue (θ i))

theorem inBasis_mul (V : unitary (Mat I)) (X Y : Mat I) :
    inBasis V X*inBasis V Y=inBasis V (X*Y) := by
  simp only [inBasis,mul_assoc,←mul_assoc (star V.val) V.val,(Unitary.mem_iff.mp V.2).1,one_mul]

theorem inBasis_trace (V : unitary (Mat I)) (X : Mat I) : (inBasis V X).trace=X.trace := by
  rw [inBasis,Matrix.trace_mul_cycle,←Matrix.mul_assoc,(Unitary.mem_iff.mp V.2).1,Matrix.one_mul]

theorem inBasis_star (V : unitary (Mat I)) (X : Mat I) : star (inBasis V X)=inBasis V (star X) := by
  simp only [inBasis,star_mul,star_star,mul_assoc]

theorem inBasis_smul (V : unitary (Mat I)) (c : ℂ) (X : Mat I) :
    c • inBasis V X=inBasis V (c • X) := by simp only [inBasis,Matrix.smul_mul,Matrix.mul_smul]

theorem inBasis_sub (V : unitary (Mat I)) (X Y : Mat I) :
    inBasis V X-inBasis V Y=inBasis V (X-Y) := by simp only [inBasis,mul_sub,sub_mul]

theorem packet_add (V : unitary (Mat I)) (θ φ : I → ℝ) :
    packet V θ*packet V φ=packet V (fun i => θ i+φ i) := by
  simp only [packet,inBasis_mul,Matrix.diagonal_mul_diagonal,phaseValue,Complex.ofReal_add,add_mul,
    Complex.exp_add]

theorem packet_unitary (V : unitary (Mat I)) (θ : I → ℝ) : packet V θ∈unitary (Mat I) :=
  mul_mem (mul_mem V.2 (StaticLocalLaboratoryComplexityGrowthLaw.mem_unitaryGroup_diagonal_general _
    (fun i => Complex.norm_exp_ofReal_mul_I (θ i)))) (V⁻¹).2

theorem packet_star (V : unitary (Mat I)) (θ : I → ℝ) :
    star (packet V θ)=packet V (fun i => -θ i) := by
  rw [packet,inBasis_star,packet]
  congr 1
  ext i j
  by_cases h : i=j
  · subst j
    simp [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,phaseValue,
      Complex.star_def,←Complex.exp_conj]
  · simp [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,h,Ne.symm h]

theorem packet_shift (V : unitary (Mat I)) (θ : I → ℝ) (a : ℝ) :
    packet V (fun i => a+θ i)=phaseValue a • packet V θ := by
  rw [packet,packet,inBasis_smul]
  congr 1
  ext i j
  by_cases h : i=j
  · subst j
    simp [Matrix.smul_apply,phaseValue,add_mul,Complex.exp_add]
  · simp [Matrix.smul_apply,h]

theorem packet_pow (V : unitary (Mat I)) (θ : I → ℝ) (l : ℕ) :
    (packet V θ)^l=packet V (fun i => l*θ i) := by
  induction l with
  | zero => simp [packet,inBasis,phaseValue,(Unitary.mem_iff.mp V.2).2]
  | succ l ih => simp only [pow_succ,ih,packet_add,Nat.cast_succ,add_mul,one_mul]

/-- In a common basis, uniform error in the real eigenangles bounds
operator distance without a factor depending on dimension. -/
theorem packet_distance (V : unitary (Mat I)) (θ φ : I → ℝ) {e : ℝ} (he : 0 ≤ e)
    (h : ∀ i, |θ i-φ i|≤e) : ‖packet V θ-packet V φ‖ ≤ e := by
  rw [packet,packet,inBasis_sub,inBasis,CStarRing.norm_mul_mem_unitary _ (V⁻¹).2,
    CStarRing.norm_mem_unitary_mul _ V.2,←Matrix.diagonal_sub,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg he).2
  intro i
  change ‖phaseValue (θ i)-phaseValue (φ i)‖ ≤ e
  exact (norm_exp_ofReal_mul_I_sub_le (θ i) (φ i)).trans (h i)

end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Interpolation
