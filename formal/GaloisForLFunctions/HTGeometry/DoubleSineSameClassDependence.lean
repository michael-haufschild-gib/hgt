import GaloisForLFunctions.HTGeometry.DoubleSineLatticeShiftDefect

/-!
# Translates in the same class are differentially dependent

The sharp complement of the orbit independence theorem.  If two members of a family differ by an
element of the base field, the family is not differentially independent: the two zeroth jets
already satisfy a nontrivial algebraic relation over the base.

For the double-sine orbit that happens exactly when the two shifts differ by a period-lattice
element, because the defect of a lattice shift lies in the base field.  Together with the
independence theorem this is the two-sided form of the coset count.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

/-! ### A base-field difference destroys independence -/

theorem not_differentialIndependent_of_sub_eq_algebraMap {K L : Type*} [Field K] [Field L]
    [Algebra K L] [Differential L] {κ : Type*} [DecidableEq κ] (x : κ → L) {i j : κ}
    (hij : i ≠ j) {y : K} (hdiff : x i - x j = algebraMap K L y) :
    ¬ DifferentialIndependent K x := by
  classical
  intro hind
  set P : MvPolynomial (κ × ℕ) K :=
    MvPolynomial.X (i, 0) - MvPolynomial.X (j, 0) - MvPolynomial.C y with hPdef
  have hzero : (MvPolynomial.aeval (R := K) (S₁ := L)
        fun p : κ × ℕ => differentialJet p.2 (x p.1)) P
      = (MvPolynomial.aeval (R := K) (S₁ := L)
        fun p : κ × ℕ => differentialJet p.2 (x p.1)) 0 := by
    rw [hPdef, map_sub, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, map_zero, differentialJet_zero, differentialJet_zero, hdiff,
      sub_self]
  have hinj : Function.Injective
      (MvPolynomial.aeval (R := K) fun p : κ × ℕ => differentialJet p.2 (x p.1)) := hind
  have hP0 : P = 0 := hinj hzero
  have hev := congrArg
    (MvPolynomial.eval (fun p : κ × ℕ => if p = (i, 0) then y + 1 else 0)) hP0
  rw [hPdef] at hev
  have hne : ((j, 0) : κ × ℕ) ≠ (i, 0) := by
    intro h
    exact hij (congrArg Prod.fst h).symm
  simp only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, map_zero, if_neg hne] at hev
  simp at hev

/-! ### The double-sine orbit -/

variable {l : Fin 2 → ℂ}

local instance dscDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance dscMeroDifferential : Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- **Two translates whose shifts differ by a lattice element differ by a base-field element.** -/
theorem translate_sub_translate_eq_embed (hl : LinearIndependent ℚ l)
    (M : meroField (Set.univ : Set ℂ)) {ω : Fin 2 → ℂ}
    (h0 : BaseDefectShift hl M (ω 0)) (h1 : BaseDefectShift hl M (ω 1))
    (hi hj : ℂ) (m n : ℤ) (hclass : hi - hj = (m : ℂ) * ω 0 + (n : ℂ) * ω 1) :
    ∃ y : RatFunc (RatFunc ℂ),
      addTranslationMeroEquiv hi M - addTranslationMeroEquiv hj M
        = twoCylinderEmbed hl y := by
  obtain ⟨y, hy⟩ := baseDefectShift_lattice hl M h0 h1 m n
  refine ⟨twoCylTranslate (q0 := Complex.exp (l 0 * hj)) (q1 := Complex.exp (l 1 * hj))
    (Complex.exp_ne_zero _) (Complex.exp_ne_zero _) y, ?_⟩
  rw [← addTranslationMeroEquiv_twoCylinderEmbed_general hl hj y, ← hy,
    (addTranslationMeroEquiv hj).map_sub, addTranslationMeroEquiv_add]
  have harg : hj + ((m : ℂ) * ω 0 + (n : ℂ) * ω 1) = hi := by
    linear_combination -hclass
  rw [harg]

end

end GaloisForLFunctions.HTGeometry
