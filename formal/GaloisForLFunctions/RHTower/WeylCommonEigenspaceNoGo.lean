import GaloisForLFunctions.RHTower.WeldWeylMultiplicity

/-!
# Nontrivial Weyl pairs preserve no common character line

A finite Hurwitz residue packet carries the standard clock--shift action, but the scalar zeta
component is one character line inside that packet.  Projecting to that line cannot retain the
nontrivial Weyl action.

This module proves the underlying algebraic obstruction.  If `U V = zeta V U` and a nonzero vector
is an eigenvector of both `U` and `V` with nonzero eigenvalues, then `zeta=1`.  Hence a positive-depth
dyadic Weyl pair has no common character line.  Any arithmetic isolation compatible with both
generators must retain a full nontrivial orbit rather than the trivial-character component alone.

The theorem is standard Weyl-pair representation theory and is used as a bridge/no-go, not as new
scientific knowledge.
-/

open Complex Matrix

noncomputable section

namespace RHTower

/-- A projective Weyl pair with a common nonzero eigendirection and nonzero eigenvalues has trivial
phase. -/
theorem phase_eq_one_of_weyl_common_eigenvector {d : ℕ}
    {zeta a b : ℂ} (U V : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ)
    (hx : x ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hU : U *ᵥ x = a • x) (hV : V *ᵥ x = b • x)
    (hweyl : U * V = zeta • (V * U)) :
    zeta = 1 := by
  have haction := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M *ᵥ x) hweyl
  change (U * V) *ᵥ x = (zeta • (V * U)) *ᵥ x at haction
  have hleft : (U * V) *ᵥ x = (a * b) • x := by
    rw [← Matrix.mulVec_mulVec, hV, Matrix.mulVec_smul, hU, smul_smul]
    congr 1
    ring
  have hright : (zeta • (V * U)) *ᵥ x = (zeta * (a * b)) • x := by
    rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hU, Matrix.mulVec_smul, hV,
      smul_smul, smul_smul]
    congr 1
    ring
  have hscalar : (a * b) • x = (zeta * (a * b)) • x := by
    rw [← hleft, haction, hright]
  have hex : ∃ i, x i ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hx
    funext i
    exact hnone i
  obtain ⟨i, hi⟩ := hex
  have hiEq := congrFun hscalar i
  change (a * b) * x i = (zeta * (a * b)) * x i at hiEq
  have habx : (a * b) * x i ≠ 0 := mul_ne_zero (mul_ne_zero ha hb) hi
  apply mul_left_cancel₀ habx
  calc
    (a * b) * x i * zeta = (zeta * (a * b)) * x i := by ring
    _ = (a * b) * x i := hiEq.symm
    _ = (a * b) * x i * 1 := by ring

/-- At every positive dyadic depth there is no common nonzero eigendirection on which both
generators have nonzero eigenvalues. -/
theorem no_dyadicWeyl_common_eigenvector {d k : ℕ} (hk : 0 < k)
    (U V : Matrix (Fin d) (Fin d) ℂ)
    (hweyl : U * V = Bottcher.dyadicRoot k • (V * U)) :
    ¬ ∃ (x : Fin d → ℂ) (a b : ℂ),
      x ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧ U *ᵥ x = a • x ∧ V *ᵥ x = b • x := by
  rintro ⟨x, a, b, hx, ha, hb, hU, hV⟩
  have hphase := phase_eq_one_of_weyl_common_eigenvector U V x hx ha hb hU hV hweyl
  have horder : 1 < 2 ^ k := one_lt_pow₀ (by omega) hk.ne'
  exact (dyadicWeylPhase_isPrimitiveRoot k).ne_one horder hphase

end RHTower
