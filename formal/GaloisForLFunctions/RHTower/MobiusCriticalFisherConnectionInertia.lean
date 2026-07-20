import GaloisForLFunctions.HTGeometry.PointedFisherConnectionInertia
import GaloisForLFunctions.RHTower.MobiusCriticalFisherTangentHilbertLift

/-!
# Exact mixed signature of the squarefree Möbius Fisher connection

The squarefree Möbius source state has unit norm and is orthogonal to its centered Fisher tangent,
but those facts alone do not discharge two-channel independence: the tangent must also be nonzero.
This module closes that Prop interface from the actual arithmetic source.

Every squarefree coordinate has strictly positive probability and hence nonzero signed weight.
If the centered logarithmic tangent vanished, its coordinates at `n=1` and `n=2` would force the
same centering value to equal both `log 1` and `log 2`, contradicting `log 2 > 0`.  The state and
tangent are therefore independent for every `sigma > 1`.  The general pointed-Fisher law then
makes the actual arithmetic compression Hermitian, nonsingular, and of mixed sign, unconditionally.
-/

open Complex
open scoped ComplexOrder InnerProductSpace Matrix

namespace RHTower

noncomputable section

/-- Every squarefree coordinate has strictly positive normalized Möbius mass. -/
theorem squarefreeMobiusProbability_pos_of_squarefree
    {sigma : ℝ} (hsigma : 1 < sigma) {n : ℕ} (hn : Squarefree n) :
    0 < squarefreeMobiusProbability sigma n := by
  have hn0 : n ≠ 0 := by
    intro hzero
    subst n
    exact not_squarefree_zero hn
  rw [squarefreeMobiusProbability, squarefreeMobiusMass, if_pos hn]
  exact div_pos (by positivity) (squarefreeMobiusTotal_pos hsigma)

/-- The signed Möbius source weight is nonzero on every squarefree coordinate. -/
theorem infiniteMobiusSignedWeight_ne_zero_of_squarefree
    {sigma : ℝ} (hsigma : 1 < sigma) {n : ℕ} (hn : Squarefree n) :
    infiniteMobiusSignedWeight sigma n ≠ 0 := by
  intro hzero
  have hnorm := norm_infiniteMobiusSignedWeight_sq hsigma n
  rw [hzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hnorm
  linarith [squarefreeMobiusProbability_pos_of_squarefree hsigma hn]

/-- The completed centered Fisher tangent is nonzero for every `sigma > 1`. -/
theorem infiniteMobiusCriticalFisherTangentLp_ne_zero
    {sigma : ℝ} (hsigma : 1 < sigma) :
    infiniteMobiusCriticalFisherTangentLp sigma hsigma ≠ 0 := by
  intro hzero
  have h1 := congrArg (fun f : lp (fun _ : ℕ => ℂ) 2 => f 1) hzero
  have h2 := congrArg (fun f : lp (fun _ : ℕ => ℂ) 2 => f 2) hzero
  simp only [infiniteMobiusCriticalFisherTangentLp] at h1 h2
  rw [infiniteMobiusCriticalFisherTangentWeight] at h1 h2
  have hs1' :=
    (mul_eq_zero.mp h1).resolve_right
      (infiniteMobiusSignedWeight_ne_zero_of_squarefree hsigma (by norm_num))
  have hs2' :=
    (mul_eq_zero.mp h2).resolve_right
      (infiniteMobiusSignedWeight_ne_zero_of_squarefree hsigma
        Nat.prime_two.squarefree)
  have hs1 :
      ((-2 * (sigma - 1) *
        (Real.log 1 - squarefreeMobiusLogMoment 1 sigma) : ℝ) : ℂ) = 0 := by
    simpa using hs1'
  have hs2 :
      ((-2 * (sigma - 1) *
        (Real.log 2 - squarefreeMobiusLogMoment 1 sigma) : ℝ) : ℂ) = 0 := by
    simpa using hs2'
  have hs1r : -2 * (sigma - 1) *
      (Real.log 1 - squarefreeMobiusLogMoment 1 sigma) = 0 := by
    exact_mod_cast hs1
  have hs2r : -2 * (sigma - 1) *
      (Real.log 2 - squarefreeMobiusLogMoment 1 sigma) = 0 := by
    exact_mod_cast hs2
  have hpref : -2 * (sigma - 1) ≠ 0 :=
    mul_ne_zero (by norm_num) (sub_ne_zero.mpr (ne_of_gt hsigma))
  have hc1 := (mul_eq_zero.mp hs1r).resolve_left hpref
  have hc2 := (mul_eq_zero.mp hs2r).resolve_left hpref
  norm_num at hc1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-- Unit norm, centering orthogonality, and source nondegeneracy discharge pair independence. -/
theorem squarefreeMobiusCritical_state_tangent_linearIndependent
    {sigma : ℝ} (hsigma : 1 < sigma) :
    LinearIndependent ℂ
      ![infiniteMobiusSignedWeightLp sigma hsigma,
        infiniteMobiusCriticalFisherTangentLp sigma hsigma] := by
  rw [LinearIndependent.pair_iff]
  intro s t hrel
  have hinner := congrArg
    (inner ℂ (infiniteMobiusSignedWeightLp sigma hsigma)) hrel
  simp only [inner_add_right, inner_smul_right, inner_zero_right,
    inner_infiniteMobiusSignedWeightLp_fisherTangent_eq_zero hsigma,
    mul_zero, add_zero] at hinner
  rw [inner_self_eq_norm_sq_to_K,
    norm_infiniteMobiusSignedWeightLp hsigma] at hinner
  norm_num at hinner
  subst s
  simp only [zero_smul, zero_add] at hrel
  exact ⟨rfl, (smul_eq_zero.mp hrel).resolve_right
    (infiniteMobiusCriticalFisherTangentLp_ne_zero hsigma)⟩

/-- The actual squarefree Möbius pointed Fisher compression has exact mixed signature. -/
theorem squarefreeMobiusCritical_pointedFisherConnectionCompression_exact_mixed_signature
    {sigma : ℝ} (hsigma : 1 < sigma) :
    let M := GaloisForLFunctions.HTGeometry.pointedFisherConnectionCompression
      (infiniteMobiusSignedWeightLp sigma hsigma)
      (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
    M.IsHermitian ∧ M.det ≠ 0 ∧
      ¬ M.PosSemidef ∧ ¬ (-M).PosSemidef := by
  exact
    GaloisForLFunctions.HTGeometry.pointedFisherConnectionCompression_exact_mixed_signature
      (squarefreeMobiusCritical_state_tangent_linearIndependent hsigma)

end

end RHTower
