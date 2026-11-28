import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.PauliAverages.Interpolation.Chords.Scalar

/-! # Chord motion and skew error in physical operator norm -/

open Matrix Complex
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Interpolation.Chords
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

def affine (A B : Mat I) (u : ℝ) := ((1-u:ℝ):ℂ) • A+(u:ℂ) • B

private theorem basis_norm (V : unitary (Mat I)) (X : Mat I) : ‖inBasis V X‖=‖X‖ := by
  rw [inBasis,CStarRing.norm_mul_mem_unitary _ (V⁻¹).2,CStarRing.norm_mem_unitary_mul _ V.2]

private theorem basis_one (V : unitary (Mat I)) : inBasis V 1=1 := by
  simp only [inBasis,mul_one,(Unitary.mem_iff.mp V.2).2]

/-- In the intermediate unitary frame, the chord is diagonal with
the scalar interpolation factors as entries. -/
theorem frame_chord (A V : unitary (Mat I)) (θ : I → ℝ) (u : ℝ) :
    star (A.val*packet V (fun i => u*θ i))*affine A.val (A.val*packet V θ) u=
      inBasis V (diagonal fun i => chord u (θ i)) := by
  have htop : star (A.val*packet V (fun i => u*θ i))*A.val=star (packet V (fun i => u*θ i)) := by
    rw [star_mul,mul_assoc,(Unitary.mem_iff.mp A.2).1,mul_one]
  rw [affine,mul_add,Matrix.mul_smul,Matrix.mul_smul,←mul_assoc _ A.val,htop,packet_star,packet_add]
  simp only [packet,inBasis_smul,inBasis,←add_mul,←mul_add]
  congr 2
  ext i j
  by_cases h : i=j
  · subst j
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply_eq,chord]
    congr 2 <;> unfold phaseValue <;> congr 2 <;> push_cast <;> ring
  · simp [Matrix.smul_apply,h]

theorem operator_chord (A V : unitary (Mat I)) (θ : I → ℝ) {u r : ℝ}
    (hu : 0 ≤ u) (hu' : u ≤ 1) (hr : 0 ≤ r) (hw : ∀ i, |θ i| ≤ r) :
    let X := star (A.val*packet V (fun i => u*θ i))*affine A.val (A.val*packet V θ) u
    ‖X-1‖ ≤ r^2/8+r^3/48 ∧ ‖star X-X‖ ≤ r^3/24 := by
  intro X
  have he : X=inBasis V (diagonal fun i => chord u (θ i)) := frame_chord A V θ u
  have hh (i : I) := chord_components hu hu' (θ i)
  have hq (i : I) : (θ i)^2 ≤ r^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hw i) 2
  have hc (i : I) : |θ i|^3 ≤ r^3 := pow_le_pow_left₀ (abs_nonneg _) (hw i) 3
  constructor
  · rw [he,←basis_one V, inBasis_sub,basis_norm,←Matrix.diagonal_one,←Matrix.diagonal_sub,
      Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    have h := Complex.norm_le_abs_re_add_abs_im (chord u (θ i)-1)
    rw [Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,sub_zero,
      abs_of_nonpos (by linarith only [(hh i).1])] at h
    exact h.trans (by linarith only [(hh i).2.1,(hh i).2.2,hq i,hc i])
  · rw [he,inBasis_star,inBasis_sub,basis_norm,Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose,←Matrix.diagonal_sub,Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    let z := chord u (θ i)
    change ‖conj z-z‖ ≤ _
    have hid : conj z-z=(-(2*z.im):ℂ)*Complex.I := by
      apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring
    rw [hid,norm_mul,Complex.norm_I,mul_one,norm_neg,norm_mul,Complex.norm_ofNat,
      Complex.norm_real,Real.norm_eq_abs]
    change 2*|(chord u (θ i)).im| ≤ _
    linarith only [(hh i).2.2,hc i]

end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Interpolation.Chords
