import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.OddInverse

/-! # Quadratic time error from a transverse field at a gapped spin -/

open NormedSpace
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin
noncomputable section
variable {A : Type*} [CStarAlgebra A]

/-- Transverse perturbations of size δ across a gapped spin introduce
a uniform error of order δ plus |t|δ² in the actual propagator. -/
theorem transverse_evolution (Z W V : A) (hz : IsSelfAdjoint Z)
    (hw : IsSelfAdjoint W) (hv : IsSelfAdjoint V) (hZ : Z*Z=1) (hn : ‖Z‖≤1)
    (hW : Z*W=W*Z) (hV : Z*V=-(V*Z)) {h : ℝ} (hg : ‖W‖<h) (t : ℝ) :
    let H := h • Z+W
    ‖exp (t • ((-Complex.I) • (H+V)))-exp (t • ((-Complex.I) • H))‖ ≤
      (2+|t| * ‖V‖)*(‖V‖/(2*(h-‖W‖))) := by
  intro H
  obtain ⟨X,hX,hb⟩ := odd_commutator_inverse Z W V hZ hn hW hV hg
  have hH : IsSelfAdjoint H := by
    change star (h • Z+W)=h • Z+W
    rw [star_add,star_smul,hz.star_eq,hw.star_eq,star_trivial]
  have he := field_evolution_bound H V 0 X hH hv (IsSelfAdjoint.zero _)
    (by simpa only [sub_zero] using hX) 1 t
  simp only [one_smul,add_zero,abs_one,mul_one,one_pow,mul_zero,zero_sub,norm_neg] at he
  have hmul := mul_le_mul_of_nonneg_left (norm_mul_le V X) (abs_nonneg t)
  have hf : 2*‖X‖+|t| * (‖V‖*‖X‖)=(2+|t| * ‖V‖)*‖X‖ := by ring
  exact he.trans ((add_le_add le_rfl hmul).trans (hf.le.trans
    (mul_le_mul_of_nonneg_left hb (by positivity))))

#print axioms transverse_evolution
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin
