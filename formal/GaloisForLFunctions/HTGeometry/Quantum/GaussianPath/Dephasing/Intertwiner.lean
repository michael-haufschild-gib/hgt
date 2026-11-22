import GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw
import Mathlib.Analysis.Calculus.MeanValue

/-! # Evolution under approximately intertwined Hamiltonians -/
open NormedSpace
namespace GaloisForLFunctions.HTGeometry.Dephasing
noncomputable section
variable {A : Type*} [CStarAlgebra A]

/-- Transport of an arbitrary operator B between two unitary evolutions
costs at most time times its generator intertwining defect. -/
theorem intertwiner_bound (a b B : A) (ha : a∈skewAdjoint A) (hb : b∈skewAdjoint A) (t : ℝ) :
    ‖exp (t • a)*B-B*exp (t • b)‖ ≤ |t| * ‖a*B-B*b‖ := by
  letI : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  let f (s : ℝ) := exp (s • (-a))*B*exp (s • b)
  let d := B*b-a*B
  let g (s : ℝ) := exp (s • (-a))*d*exp (s • b)
  have hd (s : ℝ) : HasDerivAt f (g s) s := by
    have h := ((hasDerivAt_exp_smul_const (-a) s).mul_const B).fun_mul (hasDerivAt_exp_smul_const' b s)
    convert h using 1
    dsimp only [g,d]
    noncomm_ring
  have hu (x : A) (hx : x∈skewAdjoint A) (s : ℝ) : exp (s • x)∈unitary A :=
    exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem s hx)
  have hg (s : ℝ) : ‖g s‖=‖d‖ := by
    dsimp only [g]
    rw [CStarRing.norm_mul_mem_unitary _ (hu b hb s),
      CStarRing.norm_mem_unitary_mul _ (hu (-a) ((skewAdjoint A).neg_mem ha) s)]
  have hL : LipschitzWith ‖d‖₊ f := lipschitzWith_of_nnnorm_deriv_le
    (fun s => (hd s).differentiableAt) (fun s => by exact_mod_cast (by rw [(hd s).deriv,hg] : ‖deriv f s‖≤‖d‖))
  have hcancel : exp (t • a)*exp (t • (-a))=(1:A) := by
    rw [smul_neg,←exp_add_of_commute (Commute.refl (t • a)).neg_right]
    simp
  have hmul : exp (t • a)*(f t-f 0)=B*exp (t • b)-exp (t • a)*B := by
    simp only [f,zero_smul,exp_zero,one_mul,mul_one,mul_sub,←mul_assoc,hcancel]
  calc
    ‖exp (t • a)*B-B*exp (t • b)‖ = ‖B*exp (t • b)-exp (t • a)*B‖ := norm_sub_rev _ _
    _ = ‖f t-f 0‖ := by rw [←hmul,CStarRing.norm_mem_unitary_mul _ (hu a ha t)]
    _ ≤ ‖d‖*|t| := by simpa only [dist_eq_norm,Real.norm_eq_abs,sub_zero,coe_nnnorm] using hL.dist_le_mul t 0
    _ = |t| * ‖a*B-B*b‖ := by dsimp only [d]; rw [mul_comm,norm_sub_rev]

/-- Conjugating the generators by the scalar −i translates the bound
to physical self-adjoint Hamiltonians with the same operator norm. -/
theorem hamiltonian_intertwiner_bound (H K B : A) (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) (t : ℝ) :
    ‖exp (t • ((-Complex.I) • H))*B-B*exp (t • ((-Complex.I) • K))‖≤|t| * ‖H*B-B*K‖ := by
  have hsk (C : A) (hc : IsSelfAdjoint C) : (-Complex.I) • C ∈ skewAdjoint A := by
    rw [skewAdjoint.mem_iff,star_smul,hc.star_eq]
    simp
  simpa only [smul_mul_assoc,mul_smul_comm,←smul_sub,norm_smul,norm_neg,Complex.norm_I,one_mul] using
    intertwiner_bound _ _ B (hsk H hH) (hsk K hK) t

#print axioms hamiltonian_intertwiner_bound
end
end GaloisForLFunctions.HTGeometry.Dephasing
