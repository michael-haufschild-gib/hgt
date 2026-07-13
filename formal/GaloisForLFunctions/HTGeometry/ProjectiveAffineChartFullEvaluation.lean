import GaloisForLFunctions.HTGeometry.ProjectiveAffineChartActiveEvaluation
import GaloisForLFunctions.HTGeometry.ProjectiveAffineChartFullIncidenceDimension

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Evaluation of the all-row disjoint-block ambient algebra in the genuine
coefficient-localized global incidence quotient. Active block coordinates are evaluated by the
nested active-block map; inactive variables are sent to their corresponding global packet
coordinates. -/
def projectiveChartFullAmbientEvaluation
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime] :
    projectiveChartFullIncidenceAmbient q n z j exponent p →ₐ[Localization.AtPrime p]
      projectiveChartBaseChangedGlobalIncidenceRing q n z j exponent p := by
  let E := projectiveChartActiveBlockEvaluation q n z j exponent p
  let f : projectiveChartFullIncidenceAmbient q n z j exponent p →+*
      projectiveChartBaseChangedGlobalIncidenceRing q n z j exponent p :=
    MvPolynomial.eval₂Hom E.toRingHom
      (fun bk => projectiveChartBaseChangedQuotientMap q n z j exponent p
        (MvPolynomial.X (bk.1.1, bk.2)))
  exact { f with
    commutes' := by
      intro a
      change f (MvPolynomial.C (algebraMap (Localization.AtPrime p)
        (projectiveChartActiveBlockRing q n z j exponent p) a)) = _
      dsimp [f]
      rw [MvPolynomial.eval₂_C]
      exact E.commutes a }

/-- The full ambient evaluation restricts on its coefficient algebra to the active-block
evaluation. -/
@[simp] theorem projectiveChartFullAmbientEvaluation_C
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime]
    (x : projectiveChartActiveBlockRing q n z j exponent p) :
    projectiveChartFullAmbientEvaluation q n z j exponent p (MvPolynomial.C x) =
      projectiveChartActiveBlockEvaluation q n z j exponent p x := by
  change MvPolynomial.eval₂ _ _ (MvPolynomial.C x) = _
  rw [MvPolynomial.eval₂_C]
  rfl

/-- Every inactive-row defining equation vanishes under the full ambient evaluation. -/
@[simp] theorem projectiveChartFullAmbientEvaluation_inactiveBlockPolynomial
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime]
    (b : projectiveChartInactiveRow q z j p) :
    projectiveChartFullAmbientEvaluation q n z j exponent p
        (projectiveChartInactiveBlockPolynomial q n z j exponent p b) = 0 := by
  let Q := projectiveChartBaseChangedQuotientMap q n z j exponent p
  let E := projectiveChartActiveBlockEvaluation q n z j exponent p
  let P := localizedCoefficientRowPolynomial q n z
    (projectiveChartCoefficient j) exponent p b.1
  change MvPolynomial.eval₂ E.toRingHom
      (fun bk => Q (MvPolynomial.X (bk.1.1, bk.2)))
      (MvPolynomial.rename (Prod.mk b)
        (MvPolynomial.map (algebraMap (Localization.AtPrime p)
          (projectiveChartActiveBlockRing q n z j exponent p)) P)) = 0
  rw [MvPolynomial.eval₂_rename_prod_mk]
  rw [MvPolynomial.eval₂_map]
  have hE : E.toRingHom.comp
      (algebraMap (Localization.AtPrime p)
        (projectiveChartActiveBlockRing q n z j exponent p)) =
      algebraMap (Localization.AtPrime p)
        (projectiveChartBaseChangedGlobalIncidenceRing q n z j exponent p) :=
    E.comp_algebraMap
  rw [hE]
  change MvPolynomial.eval₂
      (algebraMap (Localization.AtPrime p)
        (projectiveChartBaseChangedGlobalIncidenceRing q n z j exponent p))
      (fun k => Q (MvPolynomial.X (b.1, k))) P = 0
  rw [← MvPolynomial.eval₂_rename_prod_mk
    (f := algebraMap (Localization.AtPrime p)
      (projectiveChartBaseChangedGlobalIncidenceRing q n z j exponent p))
    (g := fun bk : row × Fin n => Q (MvPolynomial.X bk))]
  have hQ : MvPolynomial.eval₂AlgHom (Localization.AtPrime p)
      (fun bk : row × Fin n => Q (MvPolynomial.X bk)) = Q := by
    ext bk
    simp [Q, projectiveChartBaseChangedQuotientMap]
  change (MvPolynomial.eval₂AlgHom (Localization.AtPrime p)
      (fun bk : row × Fin n => Q (MvPolynomial.X bk)))
      (projectiveChartBaseChangedRowPolynomial q n z j exponent p b.1) = 0
  rw [hQ]
  change Ideal.Quotient.mk _
      (projectiveChartBaseChangedRowPolynomial q n z j exponent p b.1) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  have hmem : projectiveChartBaseChangedRowPolynomial q n z j exponent p b.1 ∈
      projectiveChartBaseChangedIncidenceIdeal q n z j exponent p :=
    Ideal.subset_span (Set.mem_range_self b.1)
  rwa [← projectiveChartGlobalIncidenceIdeal_map_localization] at hmem

/-- The full ambient evaluation descends through every inactive-row relation. -/
def projectiveChartFullEvaluation
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime] :
    projectiveChartFullIncidenceRing q n z j exponent p →ₐ[Localization.AtPrime p]
      projectiveChartBaseChangedGlobalIncidenceRing q n z j exponent p :=
  Ideal.Quotient.liftₐ (projectiveChartFullIncidenceIdeal q n z j exponent p)
    (projectiveChartFullAmbientEvaluation q n z j exponent p) (by
      intro P hP
      apply (show projectiveChartFullIncidenceIdeal q n z j exponent p ≤
        RingHom.ker (projectiveChartFullAmbientEvaluation q n z j exponent p) from ?_) hP
      unfold projectiveChartFullIncidenceIdeal
      rw [Ideal.span_le]
      intro Q hQ
      rcases hQ with ⟨b, rfl⟩
      exact projectiveChartFullAmbientEvaluation_inactiveBlockPolynomial
        q n z j exponent p b)

/-- An inactive packet coordinate maps to the corresponding global coordinate class. -/
@[simp] theorem projectiveChartFullEvaluation_inactive_X
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime]
    (b : projectiveChartInactiveRow q z j p) (k : Fin n) :
    projectiveChartFullEvaluation q n z j exponent p
        (Ideal.Quotient.mk _ (MvPolynomial.X (b, k))) =
      projectiveChartBaseChangedQuotientMap q n z j exponent p
        (MvPolynomial.X (b.1, k)) := by
  change Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ _) = _
  rw [Ideal.Quotient.lift_mk]
  change MvPolynomial.eval₂ _ _ (MvPolynomial.X (b, k)) = _
  rw [MvPolynomial.eval₂_X]

/-- Every global packet variable has a preimage in the full disjoint-block quotient, according as
its row is active or inactive at the coefficient prime. -/
theorem projectiveChartFullEvaluation_exists_preimage_X
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime]
    (bk : row × Fin n) :
    ∃ x : projectiveChartFullIncidenceRing q n z j exponent p,
      projectiveChartFullEvaluation q n z j exponent p x =
        projectiveChartBaseChangedQuotientMap q n z j exponent p
          (MvPolynomial.X bk) := by
  classical
  by_cases h : ∃ a,
      rowCoefficientPolynomialOf q z (projectiveChartCoefficient j) bk.1 a ∉ p
  · let b : projectiveChartGoodRow q z j p := ⟨bk.1, h⟩
    let e := Finite.equivFin (projectiveChartGoodRow q z j p)
    let i : Fin (Nat.card (projectiveChartGoodRow q z j p)) := e b
    obtain ⟨x, hx⟩ :=
      projectiveChartActiveBlockEvaluation_exists_preimage q n z j exponent p i bk.2
    refine ⟨Ideal.Quotient.mk _ (MvPolynomial.C x), ?_⟩
    change Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ _) = _
    rw [Ideal.Quotient.lift_mk]
    have hi : e.symm i = b := e.symm_apply_apply b
    have hrow : ((Finite.equivFin (projectiveChartGoodRow q z j p)).symm i).1 = bk.1 := by
      simpa [e] using congrArg Subtype.val hi
    calc
      _ = projectiveChartActiveBlockEvaluation q n z j exponent p x :=
        projectiveChartFullAmbientEvaluation_C q n z j exponent p x
      _ = projectiveChartBaseChangedQuotientMap q n z j exponent p
          (MvPolynomial.X
            (((Finite.equivFin (projectiveChartGoodRow q z j p)).symm i).1, bk.2)) := hx
      _ = projectiveChartBaseChangedQuotientMap q n z j exponent p
          (MvPolynomial.X bk) := by rw [hrow]
  · let b : projectiveChartInactiveRow q z j p := ⟨bk.1, h⟩
    refine ⟨Ideal.Quotient.mk _ (MvPolynomial.X (b, bk.2)), ?_⟩
    simp [b]

/-- The disjoint all-row local presentation maps onto the genuine coefficient-localized global
incidence quotient. -/
theorem projectiveChartFullEvaluation_surjective
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime] :
    Function.Surjective (projectiveChartFullEvaluation q n z j exponent p) := by
  classical
  let F := projectiveChartFullEvaluation q n z j exponent p
  let Q := projectiveChartBaseChangedQuotientMap q n z j exponent p
  have hpoly : ∀ P : MvPolynomial (row × Fin n) (Localization.AtPrime p),
      ∃ x : projectiveChartFullIncidenceRing q n z j exponent p,
        F x = Q P := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a =>
        refine ⟨algebraMap (Localization.AtPrime p)
          (projectiveChartFullIncidenceRing q n z j exponent p) a, ?_⟩
        exact F.commutes a |>.trans (Q.commutes a).symm
    | add P R hP hR =>
        obtain ⟨x, hx⟩ := hP
        obtain ⟨y, hy⟩ := hR
        refine ⟨x + y, ?_⟩
        rw [map_add, hx, hy, map_add]
    | mul_X P bk hP =>
        obtain ⟨x, hx⟩ := hP
        obtain ⟨y, hy⟩ :=
          projectiveChartFullEvaluation_exists_preimage_X q n z j exponent p bk
        refine ⟨x * y, ?_⟩
        rw [map_mul, hx, hy, map_mul]
  intro y
  induction y using Quotient.inductionOn with
  | _ P => exact hpoly P

/-- The exact evaluation-codimension threshold holds for the genuine coefficient-localized global
incidence quotient, not only for the disjoint-block presentation resolving it. -/
theorem projectiveChartBaseChangedGlobalIncidenceRing_evaluationCodimension
    {row κ : Type} [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ)) (hexponent : Function.Injective exponent)
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime]
    (hrows : Fintype.card (κ × Fin (q + 1)) + q < Fintype.card row) :
    ringKrullDim
        (projectiveChartBaseChangedGlobalIncidenceRing q n z j exponent p) +
        ((Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1 : ℕ) :
          WithBot ℕ∞) ≤
      (Fintype.card row * n : ℕ) := by
  have hdim : ringKrullDim
      (projectiveChartBaseChangedGlobalIncidenceRing q n z j exponent p) ≤
      ringKrullDim (projectiveChartFullIncidenceRing q n z j exponent p) :=
    ringKrullDim_le_of_surjective
      (projectiveChartFullEvaluation q n z j exponent p).toRingHom
      (projectiveChartFullEvaluation_surjective q n z j exponent p)
  calc
    _ ≤ ringKrullDim (projectiveChartFullIncidenceRing q n z j exponent p) +
        ((Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1 : ℕ) :
          WithBot ℕ∞) := by
      simpa [add_comm] using add_le_add_right hdim
        ((Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1 : ℕ) :
          WithBot ℕ∞)
    _ ≤ _ := projectiveChartFullIncidenceRing_evaluationCodimension
      q n z hz j exponent hexponent p hrows

end
end GaloisForLFunctions.HTGeometry
