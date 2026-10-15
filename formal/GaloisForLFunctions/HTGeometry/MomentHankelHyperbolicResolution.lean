import GaloisForLFunctions.HTGeometry.MomentHankelNormalKernel

/-!
# A hyperbolic plane across every genuine Hankel gap

The first and last admission multiples have Gram matrix `[[0, δ], [δ, b]]`
with `δ ≠ 0`. Subtracting `b/(2δ)` times the first from the last makes both
isotropic. Their normalized sum and difference have exact Gram matrix
`diag(2,-2)`, and remain orthogonal to the preceding regular head.
-/

open Polynomial Matrix
namespace HTGeometry.MomentNormalBlock
noncomputable section

/-- A genuine singular gap resolves into an explicit hyperbolic plane orthogonal to the old head.
The normalizations `2` and `-2` are exact. -/
theorem exists_hyperbolic_plane {s : ℕ → ℝ} {n d : ℕ}
    (h : MomentNormalBlock s n d) (hd : 1 < d) :
    ∃ U V : ℝ[X], U.natDegree < n + d ∧ V.natDegree < n + d ∧
      momentInner s U U = 2 ∧ momentInner s V V = -2 ∧ momentInner s U V = 0 ∧
      ∀ i : Fin n, momentInner s (X ^ (i : ℕ)) U = 0 ∧
        momentInner s (X ^ (i : ℕ)) V = 0 := by
  let P := monicMomentAdmissionPolynomial s n
  let Q : ℝ[X] := X ^ (d - 1) * P
  let δ := momentFunctional s (X ^ (n + d - 1) * P)
  have hδ : δ ≠ 0 := h.coupling_ne_zero
  have hPP : momentInner s P P = 0 := by
    simpa only [gram, pow_zero, one_mul] using
      h.gram_before_antidiagonal ⟨0, by omega⟩ ⟨0, by omega⟩ (by
        change 0 + 0 < d - 1
        omega)
  have hPQ : momentInner s P Q = δ := by
    simpa only [gram, pow_zero, one_mul, Nat.zero_add] using
      h.gram_antidiagonal ⟨0, by omega⟩ ⟨d - 1, by omega⟩ (by
        change 0 + (d - 1) = d - 1
        omega)
  have hQP : momentInner s Q P = δ := (momentInner_comm s Q P).trans hPQ
  let R := Q + (-(momentInner s Q Q / (2 * δ))) • P
  have hPR : momentInner s P R = δ := by
    simp only [R, momentInner_add_right, momentInner_smul_right, hPQ, hPP, mul_zero,
      add_zero]
  have hRP : momentInner s R P = δ := (momentInner_comm s R P).trans hPR
  have hRR : momentInner s R R = 0 := by
    simp only [R, momentInner_add_left, momentInner_add_right, momentInner_smul_left,
      momentInner_smul_right, hPP, hPQ, hQP]
    field_simp [hδ]
    ring
  let U := P + δ⁻¹ • R
  let V := P + (-δ⁻¹) • R
  have hPdeg : P.natDegree < n + d := by
    rw [monicMomentAdmissionPolynomial_natDegree]
    omega
  have hQdeg : Q.natDegree < n + d := by
    dsimp only [Q]
    rw [(monic_X_pow (d - 1)).natDegree_mul (monicMomentAdmissionPolynomial_monic s n),
      natDegree_X_pow, monicMomentAdmissionPolynomial_natDegree]
    omega
  have hdegadd (p q : ℝ[X]) (c : ℝ) (hp : p.natDegree < n + d)
      (hq : q.natDegree < n + d) : (p + c • q).natDegree < n + d :=
    (natDegree_add_le _ _).trans_lt (max_lt hp ((natDegree_smul_le _ _).trans_lt hq))
  have hRdeg : R.natDegree < n + d := hdegadd _ _ _ hQdeg hPdeg
  refine ⟨U, V, hdegadd _ _ _ hPdeg hRdeg, hdegadd _ _ _ hPdeg hRdeg, ?_, ?_, ?_, ?_⟩
  · simp only [U, momentInner_add_left, momentInner_add_right, momentInner_smul_left,
      momentInner_smul_right, hPP, hPR, hRP, hRR]
    field_simp [hδ]
    ring
  · simp only [V, momentInner_add_left, momentInner_add_right, momentInner_smul_left,
      momentInner_smul_right, hPP, hPR, hRP, hRR]
    field_simp [hδ]
    ring
  · simp only [U, V, momentInner_add_left, momentInner_add_right, momentInner_smul_left,
      momentInner_smul_right, hPP, hPR, hRP, hRR]
    ring
  · intro i
    have hiP : momentInner s (X ^ (i : ℕ)) P = 0 := by
      simpa only [pow_zero, one_mul] using h.orthogonal_to_head i ⟨0, by omega⟩
    have hiQ : momentInner s (X ^ (i : ℕ)) Q = 0 :=
      h.orthogonal_to_head i ⟨d - 1, by omega⟩
    simp only [U, V, R, momentInner_add_right, momentInner_smul_right, hiP, hiQ,
      mul_zero, add_zero, and_self]

end
end HTGeometry.MomentNormalBlock
