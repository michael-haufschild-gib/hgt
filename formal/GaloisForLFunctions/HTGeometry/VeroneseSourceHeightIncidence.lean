import GaloisForLFunctions.HTGeometry.PhysicalArcCriticalCompletion

/-!
# Source height, physical contact order and incidence level agree

The source height of an augmented constraint ideal is the least total degree of a nonzero element.
For the squarefree degree-`r` annihilator it is exactly `r`: monomial width bounds total degree
from below, and a coface generator attains the bound.

That integer is the same as the two physical ones already computed for the same ideal.  Along an
arc with no vanishing period the contact order is `r`, and for a nondiscrete period source the
level of the powered period-incidence filtration at which the arc image is detected is `r`.  So the
filtered source algebra, the arc geometry and the bounded incidence space return one integer.
-/

open scoped BigOperators

namespace GaloisForLFunctions.VeroneseIdeal

open MvPolynomial

variable {R σ : Type*} [CommRing R] [DecidableEq σ]

/-! ## Monomial width bounds total degree -/

omit [DecidableEq σ] in
theorem card_support_le_sum (d : σ →₀ ℕ) : d.support.card ≤ d.sum fun _ e => e := by
  classical
  rw [Finsupp.sum, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)

omit [DecidableEq σ] in
/-- **Lower bound on the source height.**  A nonzero monomial-wide polynomial of width `r` has
total degree at least `r`. -/
theorem le_totalDegree_of_monoWide {r : ℕ} {P : MvPolynomial σ R} (hP : MonoWide r P)
    (hP0 : P ≠ 0) : r ≤ P.totalDegree := by
  classical
  obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr
    (fun h => hP0 (MvPolynomial.support_eq_empty.mp h))
  calc r ≤ d.support.card := hP d (MvPolynomial.mem_support_iff.mp hd)
    _ ≤ d.sum fun _ e => e := card_support_le_sum d
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hd

/-- The total degree of a squarefree monomial is the number of its variables. -/
theorem totalDegree_prod_X [Nontrivial R] (J : Finset σ) :
    (∏ j ∈ J, (X j : MvPolynomial σ R)).totalDegree = J.card := by
  classical
  rw [prod_X_eq_monomial, MvPolynomial.totalDegree_monomial _ (one_ne_zero (α := R)), Finsupp.sum,
    support_sum_single]
  refine (Finset.sum_congr rfl fun i hi => ?_).trans (by rw [Finset.card_eq_sum_ones])
  rw [sum_single_apply, if_pos hi]

theorem prod_X_ne_zero [Nontrivial R] (J : Finset σ) :
    (∏ j ∈ J, (X j : MvPolynomial σ R)) ≠ 0 := by
  rw [prod_X_eq_monomial]
  simp

/-! ## The source height of the squarefree annihilator -/

/-- The augmentation degrees realized by the nonzero elements of the squarefree annihilator. -/
def sourceDegrees (R σ : Type*) [CommRing R] [DecidableEq σ] (r : ℕ) : Set ℕ :=
  {n | ∃ P ∈ veroneseIdeal R σ r, P ≠ 0 ∧ P.totalDegree = n}

/-- **The source height is exactly `r`.**  Every nonzero element of the squarefree degree-`r`
annihilator has total degree at least `r`, and a coface generator has total degree exactly `r`. -/
theorem isLeast_sourceDegrees [Nontrivial R] {r : ℕ} {J : Finset σ} (hJ : J.card = r) :
    IsLeast (sourceDegrees R σ r) r := by
  constructor
  · exact ⟨∏ j ∈ J, X j, Ideal.subset_span ⟨J, hJ, rfl⟩, prod_X_ne_zero J,
      (totalDegree_prod_X J).trans hJ⟩
  · rintro n ⟨P, hP, hP0, rfl⟩
    exact le_totalDegree_of_monoWide (monoWide_of_mem_ideal hP) hP0

end GaloisForLFunctions.VeroneseIdeal

namespace GaloisForLFunctions

noncomputable section

/-- **One integer, three realizations.**  For a nondiscrete period source and an arc with no
vanishing period, the source height of the squarefree degree-`r` annihilator, its physical contact
order along the arc, and the level of the powered period-incidence filtration at which its arc
image is detected are all equal to `r`. -/
theorem veroneseIdeal_sourceHeight_eq_contact_eq_incidenceLevel
    {ι : Type*} [DecidableEq ι] (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L)
    (τ : ι → ℂ) (hτ : ∀ j, τ j ≠ 0) {r : ℕ} {S : Finset ι} (hS : S.card = r) :
    IsLeast (VeroneseIdeal.sourceDegrees ℂ ι r) r ∧
      ((∀ P ∈ VeroneseIdeal.veroneseIdeal ℂ ι r,
          (Polynomial.X : Polynomial ℂ) ^ r ∣ VeroneseIdeal.physicalArcPullback τ P) ∧
        ¬ (Polynomial.X : Polynomial ℂ) ^ (r + 1) ∣
          VeroneseIdeal.physicalArcPullback τ (∏ j ∈ S, MvPolynomial.X j)) ∧
      ((∀ P ∈ VeroneseIdeal.veroneseIdeal ℂ ι r,
          arcEvalVector L (VeroneseIdeal.physicalArcPullback τ P) ∈
            Set.range (poweredPeriodIncidenceMultiplier L r)) ∧
        arcEvalVector L (VeroneseIdeal.physicalArcPullback τ (∏ j ∈ S, MvPolynomial.X j)) ∉
          Set.range (poweredPeriodIncidenceMultiplier L (r + 1))) :=
  ⟨VeroneseIdeal.isLeast_sourceDegrees hS,
    ⟨fun _ hP => VeroneseIdeal.pow_dvd_physicalArcPullback_of_mem_veroneseIdeal τ hP,
      (VeroneseIdeal.physicalArcPullback_generator_ne_zero τ hτ hS).2⟩,
    veroneseIdeal_arcEval_poweredRange_exact L hL τ hτ hS⟩

end

end GaloisForLFunctions
