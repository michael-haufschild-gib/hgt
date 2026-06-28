/-
# Eventual period selection for the connected repelling input

The active `c₂` input should not have to hand-pick a period and prove a
`strongFixedPointRoots` cardinality inequality directly.  This file turns the
natural asymptotic data into the concrete period required by
`ConnectedRepellingPeriodicAvoidance`:

* fixed-point fibres are eventually separable;
* all roots outside a finite exceptional set are eventually strong;
* the squarefree bad-locus budget is eventually dominated by `2^p`.

Lean then chooses one large period and feeds the existing strong-root-card
interface.
-/
import GaloisForLFunctions.Bottcher.ConnectedRepellingPeriodicAvoidance

open Polynomial Finset Filter Topology

namespace Bottcher

/-- **Eventual exceptional-set data creates a strong-root-card period.**

For a denominator family `e p`, if for all sufficiently large periods the fixed-point polynomial is
separable, all period-`p` roots outside a finite exceptional set `E` are strong, and the bad-locus
budget plus `E.card` is less than `2^p`, then some period has enough strong roots to beat the budget.
This is the finite-count bridge used by the asymptotic `c₂` input below. -/
theorem exists_period_of_eventually_exceptional_strong_roots
    (c : ℂ) (P : Polynomial (Polynomial ℂ)) (e : ℕ → Polynomial ℂ) (E : Finset ℂ)
    (hsep : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ (fixedPointPoly c p).Separable)
    (hstrong : ∀ᶠ p : ℕ in atTop,
      ∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∉ E →
        (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖)
    (hbound : ∀ᶠ p : ℕ in atTop,
      squarefreeBadDegreeBudget P (e p) ∅ + E.card < 2 ^ p) :
    ∃ p : ℕ, squarefreeBadDegreeBudget P (e p) ∅ < (strongFixedPointRoots c p).card := by
  obtain ⟨p, ⟨⟨hp, hsep_p⟩, hstrong_p, hbound_p⟩⟩ :=
    (hsep.and (hstrong.and hbound)).exists
  have hnonStrong :
      squarefreeBadDegreeBudget P (e p) ∅ + (nonStrongFixedPointRoots c p).card < 2 ^ p :=
    squarefreeBadDegreeBudget_add_nonStrong_card_lt_of_exceptional
      c P (e p) ∅ E hstrong_p hbound_p
  exact ⟨p,
    squarefreeBadDegreeBudget_lt_strongFixedPointRoots_card_of_add_nonStrong_lt
      c hp hsep_p P (e p) ∅ hnonStrong⟩

/-- If a finite exceptional set eventually contains all non-strong roots, then roots outside that set
are eventually strong.  This converts the natural finite-exceptional-set statement into the pointwise
strong-off-exceptional callback used by `exists_period_of_eventually_exceptional_strong_roots`. -/
theorem eventually_strong_roots_off_of_eventually_nonStrong_subset
    (c : ℂ) (E : Finset ℂ)
    (hE : ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    ∀ᶠ p : ℕ in atTop,
      ∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∉ E →
        (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖ := by
  filter_upwards [hE] with p hEp z hzroot hzE
  by_contra hnot
  exact hzE (hEp ((mem_nonStrongFixedPointRoots).mpr ⟨hzroot, hnot⟩))

/-- **Eventual non-strong-root containment creates a strong-root-card period.**

This is the same period-selection bridge as
`exists_period_of_eventually_exceptional_strong_roots`, but the dynamical input is the sharper and more
natural statement that the finite exceptional set eventually contains every non-strong fixed root. -/
theorem exists_period_of_eventually_exceptional_nonStrong_subset
    (c : ℂ) (P : Polynomial (Polynomial ℂ)) (e : ℕ → Polynomial ℂ) (E : Finset ℂ)
    (hsep : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ (fixedPointPoly c p).Separable)
    (hE : ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E)
    (hbound : ∀ᶠ p : ℕ in atTop,
      squarefreeBadDegreeBudget P (e p) ∅ + E.card < 2 ^ p) :
    ∃ p : ℕ, squarefreeBadDegreeBudget P (e p) ∅ < (strongFixedPointRoots c p).card :=
  exists_period_of_eventually_exceptional_strong_roots c P e E hsep
    (eventually_strong_roots_off_of_eventually_nonStrong_subset c E hE) hbound

/-- An eventually bounded squarefree budget is eventually dominated by the exponential root count. -/
theorem eventually_budget_add_card_lt_two_pow_of_eventually_le
    (P : Polynomial (Polynomial ℂ)) (e : ℕ → Polynomial ℂ) (E : Finset ℂ) (M : ℕ)
    (hbudget : ∀ᶠ p : ℕ in atTop, squarefreeBadDegreeBudget P (e p) ∅ ≤ M) :
    ∀ᶠ p : ℕ in atTop, squarefreeBadDegreeBudget P (e p) ∅ + E.card < 2 ^ p := by
  have htwo : Tendsto (fun p : ℕ => 2 ^ p) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (show 1 < (2 : ℕ) by norm_num)
  filter_upwards [hbudget, htwo.eventually_gt_atTop (M + E.card)] with p hle hbig
  omega

/-- **Bounded-budget version of the eventual non-strong-containment period selector.**

Instead of asking directly for eventual domination by `2^p`, this version only asks that the internally
chosen squarefree budget is eventually bounded by a finite number `M`; exponential growth supplies the
domination against `2^p`. -/
theorem exists_period_of_eventually_exceptional_nonStrong_subset_of_bounded_budget
    (c : ℂ) (P : Polynomial (Polynomial ℂ)) (e : ℕ → Polynomial ℂ) (E : Finset ℂ) (M : ℕ)
    (hsep : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ (fixedPointPoly c p).Separable)
    (hE : ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E)
    (hbudget : ∀ᶠ p : ℕ in atTop, squarefreeBadDegreeBudget P (e p) ∅ ≤ M) :
    ∃ p : ℕ, squarefreeBadDegreeBudget P (e p) ∅ < (strongFixedPointRoots c p).card :=
  exists_period_of_eventually_exceptional_nonStrong_subset c P e E hsep hE
    (eventually_budget_add_card_lt_two_pow_of_eventually_le P e E M hbudget)

/-- The part of the standard squarefree budget independent of the chosen denominator. -/
noncomputable def squarefreeStaticDegreeBudget (P : Polynomial (Polynomial ℂ)) : ℕ :=
  P.leadingCoeff.natDegree +
    (Polynomial.derivative P).leadingCoeff.natDegree +
    (Polynomial.resultant P (Polynomial.derivative P)).natDegree +
    (P.coeff 0).natDegree

/-- With no extra bad polynomials, the squarefree budget is bounded by the denominator degree plus the
static `P`-dependent budget. -/
theorem squarefreeBadDegreeBudget_empty_le_natDegree_add_static
    (P : Polynomial (Polynomial ℂ)) (e : Polynomial ℂ) :
    squarefreeBadDegreeBudget P e ∅ ≤ e.natDegree + squarefreeStaticDegreeBudget P := by
  rw [squarefreeBadDegreeBudget_empty]
  unfold squarefreeStaticDegreeBudget
  omega

/-- A bound on the denominator degree gives an eventual bound on the whole no-extra squarefree budget. -/
theorem eventually_budget_le_of_eventually_denominator_natDegree_le
    (P : Polynomial (Polynomial ℂ)) (e : ℕ → Polynomial ℂ) (M : ℕ)
    (hdenom : ∀ᶠ p : ℕ in atTop, (e p).natDegree ≤ M) :
    ∀ᶠ p : ℕ in atTop,
      squarefreeBadDegreeBudget P (e p) ∅ ≤ M + squarefreeStaticDegreeBudget P := by
  filter_upwards [hdenom] with p hp
  exact le_trans (squarefreeBadDegreeBudget_empty_le_natDegree_add_static P (e p))
    (Nat.add_le_add_right hp (squarefreeStaticDegreeBudget P))

/-- **Denominator-degree version of the eventual non-strong-containment period selector.**

The only varying part of the no-extra squarefree budget is the chosen denominator degree.  Once that
degree is eventually bounded, the bounded-budget selector supplies the period. -/
theorem exists_period_of_eventually_exceptional_nonStrong_subset_of_bounded_denominator_degree
    (c : ℂ) (P : Polynomial (Polynomial ℂ)) (e : ℕ → Polynomial ℂ) (E : Finset ℂ) (M : ℕ)
    (hsep : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ (fixedPointPoly c p).Separable)
    (hE : ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E)
    (hdenom : ∀ᶠ p : ℕ in atTop, (e p).natDegree ≤ M) :
    ∃ p : ℕ, squarefreeBadDegreeBudget P (e p) ∅ < (strongFixedPointRoots c p).card :=
  exists_period_of_eventually_exceptional_nonStrong_subset_of_bounded_budget c P e E
    (M + squarefreeStaticDegreeBudget P) hsep hE
    (eventually_budget_le_of_eventually_denominator_natDegree_le P e M hdenom)

/-- **Asymptotic exceptional-set input for the active cleared-denominator `c₂` interface.**

This removes the terminal obligation to choose a period with
`squarefreeBadDegreeBudget ... < (strongFixedPointRoots c p).card`.  The callback instead supplies a
finite exceptional set and three eventual statements for the internally constructed denominator
`chosenCompRelDenom ... p`; Lean chooses a single large period and routes it through the existing
strong-root-card interface. -/
theorem phiMero_transcendental_of_repelling_eventually_exceptionalSet_clearedDenominator_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
        (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ E : Finset ℂ,
          (∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ (fixedPointPoly c p).Separable) ∧
          (∀ᶠ p : ℕ in atTop,
            ∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∉ E →
              (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖) ∧
          (∀ᶠ p : ℕ in atTop,
            squarefreeBadDegreeBudget P
                (chosenCompRelDenom hUo hUne c hU P hP0 hPrel hPmin p) ∅ + E.card < 2 ^ p)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_clearedDenominator_noExtra_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨E, hsep, hstrong, hbound⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  exact exists_period_of_eventually_exceptional_strong_roots c P
    (fun p => chosenCompRelDenom hUo hUne c hU P hP0 hPrel hPmin p) E
    hsep hstrong hbound

/-- **Asymptotic non-strong-containment input for the active cleared-denominator `c₂` interface.**

This is the sharpest finite-exceptional-set form in this module: for each minimal relation, the caller
provides a finite set `E` which eventually contains all non-strong period roots, plus eventual
separability and budget domination.  Lean converts containment of `nonStrongFixedPointRoots` into
pointwise strong behavior off `E`, chooses the period, and routes through the strong-root-card
interface. -/
theorem phiMero_transcendental_of_repelling_eventually_nonStrongSubset_clearedDenominator_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
        (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ E : Finset ℂ,
          (∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ (fixedPointPoly c p).Separable) ∧
          (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) ∧
          (∀ᶠ p : ℕ in atTop,
            squarefreeBadDegreeBudget P
                (chosenCompRelDenom hUo hUne c hU P hP0 hPrel hPmin p) ∅ + E.card < 2 ^ p)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_clearedDenominator_noExtra_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨E, hsep, hE, hbound⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  exact exists_period_of_eventually_exceptional_nonStrong_subset c P
    (fun p => chosenCompRelDenom hUo hUne c hU P hP0 hPrel hPmin p) E
    hsep hE hbound

/-- **Bounded-budget non-strong-containment input for the active cleared-denominator `c₂` interface.**

This removes the explicit eventual exponential inequality from the asymptotic `c₂` interface.  The
caller supplies a finite exceptional set `E`, a finite budget bound `M`, eventual separability,
eventual containment of all non-strong roots in `E`, and eventual boundedness of the internally chosen
squarefree budget by `M`; Lean supplies the domination by `2^p`, chooses a period, and routes through
the strong-root-card interface. -/
theorem phiMero_transcendental_of_repelling_eventually_boundedBudget_clearedDenominator_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
        (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (E : Finset ℂ) (M : ℕ),
          (∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ (fixedPointPoly c p).Separable) ∧
          (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) ∧
          (∀ᶠ p : ℕ in atTop,
            squarefreeBadDegreeBudget P
              (chosenCompRelDenom hUo hUne c hU P hP0 hPrel hPmin p) ∅ ≤ M)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_clearedDenominator_noExtra_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨E, M, hsep, hE, hbudget⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  exact exists_period_of_eventually_exceptional_nonStrong_subset_of_bounded_budget c P
    (fun p => chosenCompRelDenom hUo hUne c hU P hP0 hPrel hPmin p) E M hsep hE hbudget

/-- **Denominator-degree-bounded input for the active cleared-denominator `c₂` interface.**

This is the sharpest purely counting interface in this module: the caller supplies a finite exceptional
set `E`, a finite degree bound `M`, eventual separability, eventual containment of all non-strong roots
in `E`, and eventual boundedness of the chosen denominator degree by `M`.  Lean expands the fixed
squarefree budget, supplies the exponential domination, chooses a period, and routes through the
strong-root-card interface. -/
theorem phiMero_transcendental_of_repelling_eventually_denominatorDegreeBound_clearedDenominator_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
        (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (E : Finset ℂ) (M : ℕ),
          (∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ (fixedPointPoly c p).Separable) ∧
          (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) ∧
          (∀ᶠ p : ℕ in atTop,
            (chosenCompRelDenom hUo hUne c hU P hP0 hPrel hPmin p).natDegree ≤ M)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_clearedDenominator_noExtra_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨E, M, hsep, hE, hdenom⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  exact exists_period_of_eventually_exceptional_nonStrong_subset_of_bounded_denominator_degree c P
    (fun p => chosenCompRelDenom hUo hUne c hU P hP0 hPrel hPmin p) E M hsep hE hdenom

/-- **Explicit-denominator version of the eventual non-strong-containment period selector.**

This is the constructible counterpart of
`exists_period_of_eventually_exceptional_nonStrong_subset_of_bounded_denominator_degree`: instead of
bounding the arbitrary `chosenCompRelDenom`, the caller eventually supplies one clearing denominator
witness `e,S` whose degree is bounded by `M`.  Lean chooses a large period and returns the actual
denominator identity required by the chosen-denominator repelling interface. -/
theorem exists_period_denominator_of_eventually_exceptional_nonStrong_subset_of_bounded_denominator_witness
    (c : ℂ) (P : Polynomial (Polynomial ℂ)) (E : Finset ℂ) (M : ℕ)
    (hsep : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ (fixedPointPoly c p).Separable)
    (hE : ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E)
    (hdenom : ∀ᶠ p : ℕ in atTop,
      ∃ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
        e ≠ 0 ∧ (Polynomial.C e) * (compRelPoly c p P) = P * S ∧ e.natDegree ≤ M) :
    ∃ (p : ℕ) (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
      1 ≤ p ∧ (fixedPointPoly c p).Separable ∧ e ≠ 0 ∧
      (Polynomial.C e) * (compRelPoly c p P) = P * S ∧
      squarefreeBadDegreeBudget P e ∅ + (nonStrongFixedPointRoots c p).card < 2 ^ p := by
  have htwo : Tendsto (fun p : ℕ => 2 ^ p) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (show 1 < (2 : ℕ) by norm_num)
  obtain ⟨p, hpsep, hEsub, hdenp, hbig⟩ :=
    (hsep.and (hE.and (hdenom.and
      (htwo.eventually_gt_atTop ((M + squarefreeStaticDegreeBudget P) + E.card))))).exists
  obtain ⟨e, S, he0, hPS, hdeg⟩ := hdenp
  refine ⟨p, e, S, hpsep.1, hpsep.2, he0, hPS, ?_⟩
  have hbudget : squarefreeBadDegreeBudget P e ∅ ≤ M + squarefreeStaticDegreeBudget P :=
    le_trans (squarefreeBadDegreeBudget_empty_le_natDegree_add_static P e)
      (Nat.add_le_add_right hdeg (squarefreeStaticDegreeBudget P))
  have hcard : (nonStrongFixedPointRoots c p).card ≤ E.card := Finset.card_le_card hEsub
  omega

/-- **Constructible explicit-denominator input for the active `c₂` interface.**

This is the sharpest hRigid counting interface in this file.  For each minimal relation, the caller
does not have to prove a fact about the arbitrary denominator selected by `Classical.choose`; it
eventually produces a clearing identity `(C e) * compRelPoly c p P = P * S` with `e.natDegree ≤ M`,
plus eventual separability and eventual containment of the non-strong roots in a finite set.  Lean
then proves the squarefree budget bound, chooses a large period, and routes through the explicit
chosen-denominator repelling interface. -/
theorem phiMero_transcendental_of_repelling_eventually_denominatorWitnessBound_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ (P : Polynomial (Polynomial ℂ)) (_hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (_hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
        (_hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (E : Finset ℂ) (M : ℕ),
          (∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ (fixedPointPoly c p).Separable) ∧
          (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) ∧
          (∀ᶠ p : ℕ in atTop,
            ∃ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
              e ≠ 0 ∧ (Polynomial.C e) * (compRelPoly c p P) = P * S ∧ e.natDegree ≤ M)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_standard_squarefree_budget_nonStrong_chosenDenominator_noExtra_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨E, M, hsep, hE, hdenom⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  exact exists_period_denominator_of_eventually_exceptional_nonStrong_subset_of_bounded_denominator_witness
    c P E M hsep hE hdenom

/-- **Frequent-separability explicit-denominator period selector.**

The denominator/non-strong data are still eventual, but separability only has to occur frequently.  This
is the useful form when finitely or arithmetically many bad periods may remain: any frequently
separable period set meets the eventual large-period region where the denominator degree and non-strong
containment bounds hold. -/
theorem exists_period_denominator_of_frequently_separable_eventually_nonStrong_subset_of_bounded_denominator_witness
    (c : ℂ) (P : Polynomial (Polynomial ℂ)) (E : Finset ℂ) (M : ℕ)
    (hsep : ∃ᶠ p : ℕ in atTop, 1 ≤ p ∧ (fixedPointPoly c p).Separable)
    (hE : ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E)
    (hdenom : ∀ᶠ p : ℕ in atTop,
      ∃ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
        e ≠ 0 ∧ (Polynomial.C e) * (compRelPoly c p P) = P * S ∧ e.natDegree ≤ M) :
    ∃ (p : ℕ) (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
      1 ≤ p ∧ (fixedPointPoly c p).Separable ∧ e ≠ 0 ∧
      (Polynomial.C e) * (compRelPoly c p P) = P * S ∧
      squarefreeBadDegreeBudget P e ∅ + (nonStrongFixedPointRoots c p).card < 2 ^ p := by
  have htwo : Tendsto (fun p : ℕ => 2 ^ p) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (show 1 < (2 : ℕ) by norm_num)
  have hev : ∀ᶠ p : ℕ in atTop,
      nonStrongFixedPointRoots c p ⊆ E ∧
      (∃ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
        e ≠ 0 ∧ (Polynomial.C e) * (compRelPoly c p P) = P * S ∧ e.natDegree ≤ M) ∧
      ((M + squarefreeStaticDegreeBudget P) + E.card < 2 ^ p) := by
    filter_upwards [hE, hdenom,
      htwo.eventually_gt_atTop ((M + squarefreeStaticDegreeBudget P) + E.card)] with
      p hEp hdenp hbig
    exact ⟨hEp, hdenp, hbig⟩
  obtain ⟨p, hpsep, hEsub, hdenp, hbig⟩ := (hsep.and_eventually hev).exists
  obtain ⟨e, S, he0, hPS, hdeg⟩ := hdenp
  refine ⟨p, e, S, hpsep.1, hpsep.2, he0, hPS, ?_⟩
  have hbudget : squarefreeBadDegreeBudget P e ∅ ≤ M + squarefreeStaticDegreeBudget P :=
    le_trans (squarefreeBadDegreeBudget_empty_le_natDegree_add_static P e)
      (Nat.add_le_add_right hdeg (squarefreeStaticDegreeBudget P))
  have hcard : (nonStrongFixedPointRoots c p).card ≤ E.card := Finset.card_le_card hEsub
  omega

/-- **Constructible explicit-denominator input with only frequent fixed-point separability.**

This is the current weakest counting form in this module: for each minimal relation, separability of
`fixedPointPoly c p` is required only frequently, while the non-strong containment and explicit bounded
denominator-clearing witnesses are eventual.  Lean intersects the frequent set with the eventual
large-period region and routes through the chosen-denominator repelling interface. -/
theorem phiMero_transcendental_of_repelling_frequently_separable_denominatorWitnessBound_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ (P : Polynomial (Polynomial ℂ)) (_hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (_hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
        (_hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (E : Finset ℂ) (M : ℕ),
          (∃ᶠ p : ℕ in atTop, 1 ≤ p ∧ (fixedPointPoly c p).Separable) ∧
          (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) ∧
          (∀ᶠ p : ℕ in atTop,
            ∃ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
              e ≠ 0 ∧ (Polynomial.C e) * (compRelPoly c p P) = P * S ∧ e.natDegree ≤ M)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_standard_squarefree_budget_nonStrong_chosenDenominator_noExtra_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨E, M, hsep, hE, hdenom⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  exact
    exists_period_denominator_of_frequently_separable_eventually_nonStrong_subset_of_bounded_denominator_witness
      c P E M hsep hE hdenom

end Bottcher
