import GaloisForLFunctions.HTGeometry.DifferentialOperatorMatroid
import GaloisForLFunctions.HTGeometry.StanleyReisnerLaurentRows

/-!
# Rank of localized Stanley--Reisner differential matroids

The existing Laurent-row theorem proves independence for one complete finite family.  To obtain a
genuine matroid and numerical ranks, the statement must hold uniformly on every subfamily while
using the common finite coordinate packet of the original family.  This file proves that restricted
finite-support expansion preserves row independence, constructs the resulting Stanley--Reisner
row matroid, and identifies it with the genuine differential-family matroid of the operator outputs.

Thus arbitrary dependent packets, not only full-row-rank packets, have differential rank equal to
the fraction-field dimension of their localized Laurent coefficient-row span.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial Set
open scoped Classical Differential

noncomputable section

universe u

/-- Restricting a finite-support operator family to any subset of its rows preserves and reflects
linear independence while retaining the common coordinate packet of the full family. -/
theorem linearIndependent_restrict_finiteFinsuppOperatorRows_iff
    {P ι σ G : Type u} [Ring P] [Fintype ι] [Fintype σ]
    [DecidableEq ι] [DecidableEq σ] [DecidableEq G]
    (Q : ι → σ → G →₀ P) (I : Set ι) :
    LinearIndependent P
        (fun i : I => finiteFinsuppOperatorRows Q i) ↔
      LinearIndependent P (fun i : I => Q i) := by
  classical
  rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
  constructor
  · intro h A hrel i
    apply h A
    funext q
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.zero_apply, finiteFinsuppOperatorRows]
    have hs := congrArg
      (fun f : σ → G →₀ P => f q.1.1 q.1.2) hrel
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
      Finsupp.zero_apply] at hs
    change (Finsupp.lapply (R := P) q.1.2)
      (∑ x, A x • Q x q.1.1) = 0 at hs
    rw [map_sum] at hs
    simpa only [map_smul, finiteFinsuppOperatorRows] using hs
  · intro h A hrel i
    apply h A
    funext s
    apply Finsupp.ext
    intro g
    by_cases hzero : ∀ j : I, Q j s g = 0
    · simp [hzero]
    · push Not at hzero
      obtain ⟨j, hj⟩ := hzero
      let q : FiniteFinsuppRowIndex Q :=
        ⟨(s, g), mem_finiteFinsuppRowSupport_of_ne Q hj⟩
      have hq := congrArg
        (fun f : FiniteFinsuppRowIndex Q → P => f q) hrel
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
        finiteFinsuppOperatorRows, q] at hq
      rw [Finset.sum_apply]
      simp only [Pi.zero_apply, Finsupp.zero_apply]
      change (Finsupp.lapply (R := P) g) (∑ x, A x • Q x s) = 0
      rw [map_sum]
      simpa only [map_smul] using hq

/-- The localized linear row matroid of one finite family of facetwise finitely supported
polynomial operators. -/
def finiteFinsuppRowMatroid
    {C ι σ G : Type u} [Field C] [Fintype ι] [Fintype σ]
    [DecidableEq ι] [DecidableEq σ] [DecidableEq G]
    (Q : ι → σ → G →₀ Polynomial C) : Matroid ι :=
  differentialOperatorRowMatroid (finiteFinsuppOperatorRows Q)

@[simp]
theorem finiteFinsuppRowMatroid_ground
    {C ι σ G : Type u} [Field C] [Fintype ι] [Fintype σ]
    [DecidableEq ι] [DecidableEq σ] [DecidableEq G]
    (Q : ι → σ → G →₀ Polynomial C) :
    (finiteFinsuppRowMatroid Q).E = Set.univ := by
  simp [finiteFinsuppRowMatroid]

/-- Independent sets of the finite-support row matroid are precisely the polynomially independent
subfamilies of the original nested rows. -/
theorem finiteFinsuppRowMatroid_indep_iff
    {C ι σ G : Type u} [Field C] [Fintype ι] [Fintype σ]
    [DecidableEq ι] [DecidableEq σ] [DecidableEq G]
    (Q : ι → σ → G →₀ Polynomial C) (I : Set ι) :
    (finiteFinsuppRowMatroid Q).Indep I ↔
      LinearIndependent (Polynomial C) (fun i : I => Q i) := by
  rw [finiteFinsuppRowMatroid, differentialOperatorRowMatroid_indep_iff,
    linearIndependent_restrict_finiteFinsuppOperatorRows_iff]

/-- The complete localized Stanley--Reisner row matroid of a finite numerator family. -/
def stanleyReisnerLaurentMatroid
    {C α ι : Type u} [Field C] [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι]
    (d : translationSubmonoid (Polynomial C) α)
    (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial C) ⧸
      stanleyReisnerIdeal (Polynomial C) facets) : Matroid ι :=
  finiteFinsuppRowMatroid (stanleyReisnerLaurentRows d facets N)

@[simp]
theorem stanleyReisnerLaurentMatroid_ground
    {C α ι : Type u} [Field C] [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι]
    (d : translationSubmonoid (Polynomial C) α)
    (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial C) ⧸
      stanleyReisnerIdeal (Polynomial C) facets) :
    (stanleyReisnerLaurentMatroid d facets N).E = Set.univ := by
  simp [stanleyReisnerLaurentMatroid]

/-- The localized Stanley--Reisner matroid has exactly the independent subsets of numerator
classes in the quotient; denominator clearing and finite coordinate expansion lose no circuits. -/
theorem stanleyReisnerLaurentMatroid_indep_iff
    {C α ι : Type u} [Field C] [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι]
    (d : translationSubmonoid (Polynomial C) α)
    (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial C) ⧸
      stanleyReisnerIdeal (Polynomial C) facets)
    (I : Set ι) :
    (stanleyReisnerLaurentMatroid d facets N).Indep I ↔
      LinearIndependent (Polynomial C) (fun i : I => N i) := by
  rw [stanleyReisnerLaurentMatroid, finiteFinsuppRowMatroid_indep_iff]
  change LinearIndependent (Polynomial C)
      (stanleyReisnerLaurentRows d facets (fun i : I => N i)) ↔
    LinearIndependent (Polynomial C) (fun i : I => N i)
  exact linearIndependent_stanleyReisnerLaurentRows_iff
    d facets (fun i : I => N i)

/-- **Exact localized Stanley--Reisner differential matroid.**  On an independent source packet,
the genuine differential-family matroid of the Laurent structural outputs equals the complete
Stanley--Reisner quotient-class matroid. -/
theorem differentialFamilyMatroid_stanleyReisnerLaurentRows_eq
    {C K α ι : Type u}
    [Field C] [Field K] [Algebra C K]
    [Differential C] [Differential K] [DifferentialAlgebra C K] [CharZero K]
    [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (d : translationSubmonoid (Polynomial C) α)
    (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial C) ⧸
      stanleyReisnerIdeal (Polynomial C) facets)
    (x : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) → K)
    (hx : DifferentialIndependent C x) :
    differentialFamilyMatroid (F := C)
        (differentialOperatorRowApply
          (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) x) =
      stanleyReisnerLaurentMatroid d facets N := by
  rw [stanleyReisnerLaurentMatroid, finiteFinsuppRowMatroid]
  exact differentialFamilyMatroid_differentialOperatorRows_eq
    hconst (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) x hx

/-- Numerical form: every finite localized Stanley--Reisner output packet has rank equal to the
fraction-field dimension of its Laurent coefficient-row span. -/
theorem differentialOperatorRows_stanleyReisnerLaurent_eRk_eq_finrank_span
    {C K α ι : Type u}
    [Field C] [Field K] [Algebra C K]
    [Differential C] [Differential K] [DifferentialAlgebra C K] [CharZero K]
    [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (d : translationSubmonoid (Polynomial C) α)
    (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial C) ⧸
      stanleyReisnerIdeal (Polynomial C) facets)
    (x : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) → K)
    (hx : DifferentialIndependent C x) (I : Finset ι) :
    (differentialFamilyMatroid (F := C)
        (differentialOperatorRowApply
          (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) x)).eRk
        (↑I : Set ι) =
      (Module.finrank (FractionRing (Polynomial C))
        (Submodule.span (FractionRing (Polynomial C))
          ((fun i => localizeOperatorRow
            (finiteFinsuppOperatorRows
              (stanleyReisnerLaurentRows d facets N) i)) '' (↑I : Set ι))) : ℕ∞) := by
  exact differentialOperatorRows_eRk_eq_finrank_span hconst
    (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) x hx I

end

end GaloisForLFunctions.HTGeometry
