import GaloisForLFunctions.HTGeometry.InfinitePathBoundedProjectiveSelection

/-!
# A nested-centered thermodynamic path field

Expand the compatible inverse-square matching and inverse-fourth bridge `P11` background into
onsite `Z`, edge `ZZ`, and scalar coordinates.  Around its nonidentity path coefficients, choose
radius `10⁻⁶ n⁻²` at every onsite and edge Pauli coordinate.  Bounded simultaneous generic
selection gives one countable field inside these boxes whose every finite path prefix is maximally
projective.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Weight of the physical path bond with zero-based left endpoint `e`: inverse-square on matching
bonds and inverse-fourth on inter-pair bridge bonds. -/
def nestedInfiniteEdgeWeight (e : ℕ) : ℝ :=
  if Even e then 1 / (((e / 2 + 1 : ℕ) : ℝ) ^ (2 : ℕ))
  else 1 / (((e / 2 + 2 : ℕ) : ℝ) ^ (4 : ℕ))

/-- Nonidentity Pauli coefficients of the compatible nested `P11` background. -/
def nestedInfinitePathCenter : InfinitePathLabel → ℝ
  | Sum.inl sq =>
      if sq.2 = 2 then
        -(nestedInfiniteEdgeWeight sq.1 +
          if sq.1 = 0 then 0 else nestedInfiniteEdgeWeight (sq.1 - 1)) / 4
      else 0
  | Sum.inr eab =>
      if eab.2 = ((2 : Fin 3), (2 : Fin 3)) then
        nestedInfiniteEdgeWeight eab.1 / 4
      else 0

/-- Coordinatewise perturbation envelope around the nested background. -/
def infinitePathRadius : InfinitePathLabel → ℝ
  | Sum.inl sq => 1 / (1000000 * (((sq.1 + 1 : ℕ) : ℝ) ^ (2 : ℕ)))
  | Sum.inr eab => 1 / (1000000 * (((eab.1 + 1 : ℕ) : ℝ) ^ (2 : ℕ)))

theorem infinitePathRadius_pos (i : InfinitePathLabel) : 0 < infinitePathRadius i := by
  rcases i with i | i <;> simp [infinitePathRadius] <;> positivity

/-- **Nested-centered all-prefix selection law.** -/
theorem exists_nestedCentered_allPrefixes_projective :
    ∃ p : InfinitePathLabel → ℝ,
      (∀ i, |p i - nestedInfinitePathCenter i| < infinitePathRadius i) ∧
      ∀ k, coefficientRestrict (numberedPathToInfinite k) p ∈ chainProjectiveGood k := by
  exact exists_bounded_infinitePath_allPrefixes_projective
    nestedInfinitePathCenter infinitePathRadius infinitePathRadius_pos

/-- Literal finite path-shell restriction of one infinite path field. -/
def infinitePathPrefixShell (k : ℕ) (p : InfinitePathLabel → ℝ) : PathShell (k + 1) :=
  WithLp.toLp 2 fun l => p (pathLabelToInfinite k l)

theorem pathChainCoeff_infinitePathPrefixShell (k : ℕ) (p : InfinitePathLabel → ℝ) :
    pathChainCoeff k (WithLp.ofLp (infinitePathPrefixShell k p)) =
      coefficientRestrict (numberedPathToInfinite k) p := by
  rfl

/-- Every literal finite restriction selected by the one-field law has maximally projective
eigenvalues. -/
theorem infinitePathPrefixShell_maximallyProjective
    {p : InfinitePathLabel → ℝ}
    (hp : ∀ k, coefficientRestrict (numberedPathToInfinite k) p ∈ chainProjectiveGood k)
    (k : ℕ) :
    MaximallyProjectiveEnergy (pathEigenValues k (infinitePathPrefixShell k p)) := by
  have hgood := hp k
  rw [chainProjectiveGood] at hgood
  have hmax := (mem_genericSet_iff_maximallyProjective
    (chainPauliFin_isHermitian (k + 3))
    (coefficientRestrict (numberedPathToInfinite k) p)).mp hgood
  rw [← pathChainCoeff_infinitePathPrefixShell k p] at hmax
  exact hmax.comp_equiv_relabel (qubitConfigFin (k + 3))

/-- The same finite restriction carries an explicit orthonormal eigenbasis and a maximally
projective eigenvalue packet. -/
theorem infinitePathPrefixShell_orthoEigenBasis_maximal
    {p : InfinitePathLabel → ℝ}
    (hp : ∀ k, coefficientRestrict (numberedPathToInfinite k) p ∈ chainProjectiveGood k)
    (k : ℕ) :
    ∃ (e : FiniteQubitConfiguration (Fin (k + 3)) →
          FiniteQubitConfiguration (Fin (k + 3)) → ℂ)
      (lam : FiniteQubitConfiguration (Fin (k + 3)) → ℝ),
      IsOrthoEigenBasis (pathHamiltonian (infinitePathPrefixShell k p)) e lam ∧
        MaximallyProjectiveEnergy lam := by
  exact ⟨pathEigenBasis k (infinitePathPrefixShell k p),
    pathEigenValues k (infinitePathPrefixShell k p),
    isOrthoEigenBasis_pathEigenBasis k (infinitePathPrefixShell k p),
    infinitePathPrefixShell_maximallyProjective hp k⟩

end

end GaloisForLFunctions.HTGeometry
