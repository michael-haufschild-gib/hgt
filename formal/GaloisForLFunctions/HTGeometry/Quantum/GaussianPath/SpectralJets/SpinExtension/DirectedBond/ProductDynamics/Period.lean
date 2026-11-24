import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.ProductDynamics.Factorization
import GaloisForLFunctions.HTGeometry.ScalarSquareExponential

/-! # Projective return at π for each integral tilted product background -/
open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

private theorem rotation_pi (b : ℕ) :
    unitaryEvolution (height b • tiltedAxis) π=(-1:ℂ)^(b+1) • (1:Matrix Bool Bool ℂ) := by
  let r : ℝ := (b+1:ℕ)*π
  let M := (-Complex.I*(r:ℂ)) • tiltedAxis
  have hsq : M*M=(-((r:ℂ)^2)) • (1:Matrix Bool Bool ℂ) := by
    rw [show M*M=((-Complex.I*(r:ℂ))*(-Complex.I*(r:ℂ))) • (tiltedAxis*tiltedAxis) by
      rw [M,smul_mul_smul_comm],tiltedAxis_square]
    congr 1
    calc _ = (Complex.I*Complex.I)*(r:ℂ)^2 := by ring
         _ = _ := by rw [Complex.I_mul_I]; ring
  have hgen : π • ((-Complex.I) • (height b • tiltedAxis))=M := by
    rw [←Complex.coe_smul,smul_smul,smul_smul]
    change _ = (-Complex.I*(r:ℂ)) • tiltedAxis
    congr 1
    simp only [height,r,Complex.ofReal_mul,Complex.ofReal_natCast,Nat.cast_add,Nat.cast_one]
    ring
  have hr : r≠0 := by dsimp [r]; positivity
  have hsin : sin r=0 := sin_nat_mul_pi (b+1)
  have hcos : cos r=(-1:ℝ)^(b+1) := cos_nat_mul_pi (b+1)
  rw [unitaryEvolution,hgen,_root_.HTGeometry.exp_of_mul_self_eq_neg_sq_smul_one M r hsq,hcos,
    sinc_of_ne_zero hr,hsin,zero_div,Complex.ofReal_zero,zero_smul,add_zero]
  push_cast
  rfl

/-- The same projective return time works for every length and every choice
of the positive integral onsite fields, including the full-rank witnesses. -/
theorem product_return_pi (n : ℕ) (B : Fin (n+1)→ℕ) :
    unitaryEvolution (chain B 0) π=(∏ s, (-1:ℂ)^(B s+1)) • (1:Register (n+1)) := by
  rw [chain,map_zero,Prod.fst_zero,Prod.snd_zero,zero_smul,add_zero]
  ext i j
  rw [product_evolution]
  simp only [rotation_pi,Matrix.smul_apply,smul_eq_mul,Finset.prod_mul_distrib]
  by_cases he : i=j
  · subst j
    simp [Matrix.one_apply]
  · obtain ⟨s,hs⟩ : ∃ s, i s≠j s := by
      by_contra! h
      exact he (funext h)
    have hz : (∏ s, (1:Matrix Bool Bool ℂ) (i s) (j s))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ s) (by simp [Matrix.one_apply,hs])
    simp only [hz,Matrix.one_apply,if_neg he,mul_zero]

#print axioms product_return_pi
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
