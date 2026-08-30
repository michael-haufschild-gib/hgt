import GaloisForLFunctions.HTGeometry.MahlerCoefficientFieldConfinement
import GaloisForLFunctions.HTGeometry.GeneratedFieldRank

/-!
# Infinitely many independent Taylor coefficients force hypertranscendence

Mahler's integer normalization and the forward coefficient recursion confine the coefficients of a
formal solution of a nonzero algebraic differential equation to the field generated over `ℚ` by
finitely many of them.  Such a field has finite transcendence degree, so a power series with
infinitely many algebraically independent coefficients satisfies no nonzero algebraic differential
equation — whatever its coefficient magnitudes are.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Coefficient confinement.**  A formal solution of a nonzero algebraic differential relation has
all of its coefficients in the field generated over `ℚ` by finitely many of them. -/
theorem coefficients_mem_adjoin_of_formalRelation {F : PowerSeries ℂ} {r : ℕ}
    {P : MvPolynomial (Fin (r + 2)) ℂ} (hP0 : P ≠ 0)
    (hrel : MvPolynomial.aeval (GaloisForLFunctions.formalJets r F) P = 0) :
    ∃ N : ℕ, ∀ n : ℕ, PowerSeries.coeff n F
      ∈ IntermediateField.adjoin ℚ ((fun k => PowerSeries.coeff k F) '' Set.Iic N) := by
  obtain ⟨m, Q, hQ0, hQint, hQsol⟩ :=
    GaloisForLFunctions.exists_integer_jet_relation_of_formalRelation hP0 hrel
  obtain ⟨N, hN⟩ := exists_forall_coefficientsIn_of_integer_ordinaryADE Q hQ0 hQint hQsol
  refine ⟨N, ?_⟩
  refine hN (IntermediateField.adjoin ℚ ((fun k => PowerSeries.coeff k F) '' Set.Iic N)) ?_
  intro n hn
  exact IntermediateField.subset_adjoin ℚ _ ⟨n, hn, rfl⟩

/-- **Independent coefficients survive every algebraic differential equation.** -/
theorem aeval_formalJets_ne_zero_of_infinite_independent {a : ℕ → ℂ} {S : Set ℕ}
    (hS : S.Infinite)
    (hind : ∀ T : Finset ℕ, (↑T : Set ℕ) ⊆ S → AlgebraicIndepOn ℚ a (↑T : Set ℕ))
    {r : ℕ} {P : MvPolynomial (Fin (r + 2)) ℂ} (hP0 : P ≠ 0) :
    MvPolynomial.aeval (GaloisForLFunctions.formalJets r (PowerSeries.mk a)) P ≠ 0 := by
  classical
  intro hrel
  obtain ⟨N, hN⟩ := coefficients_mem_adjoin_of_formalRelation hP0 hrel
  set K : IntermediateField ℚ ℂ :=
    IntermediateField.adjoin ℚ
      ((fun k => PowerSeries.coeff k (PowerSeries.mk a)) '' Set.Iic N) with hK
  -- the generated field has transcendence degree at most `N + 1`
  have hle : Algebra.trdeg ℚ ↥K
      ≤ Cardinal.mk ((fun k => PowerSeries.coeff k (PowerSeries.mk a)) '' Set.Iic N) :=
    trdeg_intermediateFieldAdjoin_le _
  have hIic : Cardinal.mk (Set.Iic N : Set ℕ) = ((N + 1 : ℕ) : Cardinal) := by
    rw [show (Set.Iic N : Set ℕ) = ↑(Finset.Iic N) by ext x; simp]
    simp
  have hbound : Algebra.trdeg ℚ ↥K ≤ ((N + 1 : ℕ) : Cardinal) := by
    refine hle.trans ?_
    refine le_trans (Cardinal.mk_image_le) ?_
    rw [hIic]
  -- a subfamily of `N + 2` independent coefficients
  obtain ⟨T, hTS, hTcard⟩ := hS.exists_subset_card_eq (N + 2)
  have hmemK : ∀ n : ℕ, a n ∈ K := by
    intro n
    have := hN n
    rwa [PowerSeries.coeff_mk] at this
  set b : (↑T : Set ℕ) → ↥K := fun i => ⟨a (i : ℕ), hmemK (i : ℕ)⟩ with hb
  have hincl : AlgebraicIndependent ℚ (fun i : (↑T : Set ℕ) => a (i : ℕ)) := hind T hTS
  have hbind : AlgebraicIndependent ℚ b := by
    refine AlgebraicIndependent.of_comp (IntermediateField.val K) ?_
    exact hincl
  have hcard := hbind.cardinalMk_le_trdeg
  have hcardT : Cardinal.mk (↑T : Set ℕ) = ((N + 2 : ℕ) : Cardinal) := by
    simp [hTcard]
  rw [hcardT] at hcard
  have hcontra : ((N + 2 : ℕ) : Cardinal) ≤ ((N + 1 : ℕ) : Cardinal) := hcard.trans hbound
  rw [Nat.cast_le] at hcontra
  omega

end

end GaloisForLFunctions.HTGeometry
