/-
# Connected repelling event route with bounded fixed-root deficit

The no-multiplier-one route recovers separability of `fixedPointPoly c p`, hence the exact distinct
root count `2^p`.  That is too narrow near parabolic parameters.  This file replaces separability by
a bounded distinct-root deficit: it is enough that the number of distinct fixed roots is at least
`2^p - D` eventually, because every other contribution to the squarefree budget is bounded while
`2^p` grows.
-/
import GaloisForLFunctions.Bottcher.DenominatorContent

open Polynomial Finset Filter Topology

namespace Bottcher

/-- Period-`p` fixed roots whose period-`p` multiplier is exactly `1`. -/
noncomputable def multiplierOneFixedPointRoots (c : ℂ) (p : ℕ) : Finset ℂ := by
  classical
  exact (fixedPointPoly c p).roots.toFinset.filter fun z =>
    (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) = (1 : ℂ)

theorem mem_multiplierOneFixedPointRoots {c z : ℂ} {p : ℕ} :
    z ∈ multiplierOneFixedPointRoots c p ↔
      z ∈ (fixedPointPoly c p).roots.toFinset ∧
        (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) = (1 : ℂ) := by
  classical
  simp [multiplierOneFixedPointRoots]

/-- Multiple roots of the fixed-point polynomial are exactly in the multiplier-one locus needed for
the root-defect route.  This is the local algebraic bridge from repeated fixed roots to parabolic
period-`p` multiplier behavior. -/
theorem mem_multiplierOneFixedPointRoots_of_one_lt_roots_count
    (c : ℂ) {p : ℕ} (hp : 1 ≤ p) {z : ℂ}
    (hcount : 1 < (fixedPointPoly c p).roots.count z) :
    z ∈ multiplierOneFixedPointRoots c p := by
  have hrootMult :
      1 < (fixedPointPoly c p).rootMultiplicity z := by
    simpa [Polynomial.count_roots] using hcount
  have hboth :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot (fixedPointPoly_ne_zero c hp)).mp hrootMult
  have hzroot : z ∈ (fixedPointPoly c p).roots.toFinset := by
    exact Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (by omega))
  have hprod : (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) = (1 : ℂ) := by
    have hder := hboth.2
    rw [Polynomial.IsRoot.def, eval_deriv_fixedPointPoly] at hder
    exact sub_eq_zero.mp hder
  exact (mem_multiplierOneFixedPointRoots).mpr ⟨hzroot, hprod⟩

/-- A multiset's cardinality is its number of distinct elements plus the total duplicate excess. -/
theorem multiset_card_eq_toFinset_card_add_count_excess {α : Type*} [DecidableEq α]
    (s : Multiset α) :
    s.card = s.toFinset.card + ∑ x ∈ s.toFinset, (s.count x - 1) := by
  rw [← Multiset.toFinset_sum_count_eq s, Finset.card_eq_sum_ones,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have hpos : 0 < s.count x := by
    rw [Multiset.count_pos]
    exact Multiset.mem_toFinset.mp hx
  omega

/-- If all duplicate elements of a multiset lie in `E`, and each duplicate excess on `E` is at most
`L`, then the total duplicate excess is at most `E.card * L`. -/
theorem multiset_count_excess_le_card_mul_of_multiple_support {α : Type*} [DecidableEq α]
    (s : Multiset α) (E : Finset α) (L : ℕ)
    (hsimple_off : ∀ x ∈ s.toFinset, x ∉ E → s.count x ≤ 1)
    (hexcess_on : ∀ x ∈ s.toFinset, x ∈ E → s.count x - 1 ≤ L) :
    (∑ x ∈ s.toFinset, (s.count x - 1)) ≤ E.card * L := by
  classical
  let T : Finset α := s.toFinset.filter fun x => x ∈ E
  have hsplit :
      (∑ x ∈ s.toFinset, (s.count x - 1)) =
        (∑ x ∈ T, (s.count x - 1)) := by
    rw [← Finset.sum_filter_add_sum_filter_not s.toFinset (fun x => x ∈ E)]
    have hzero : (∑ x ∈ s.toFinset.filter (fun x => ¬x ∈ E), (s.count x - 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hxroot : x ∈ s.toFinset := (Finset.mem_filter.mp hx).1
      have hxE : x ∉ E := (Finset.mem_filter.mp hx).2
      have hle := hsimple_off x hxroot hxE
      omega
    simp [T, hzero]
  rw [hsplit]
  have hsum_le : (∑ x ∈ T, (s.count x - 1)) ≤ T.card * L := by
    simpa [nsmul_eq_mul] using
      Finset.sum_le_card_nsmul T (fun x => s.count x - 1) L (by
        intro x hx
        exact hexcess_on x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2)
  exact hsum_le.trans (Nat.mul_le_mul_right L (Finset.card_le_card (by
    intro x hx
    exact (Finset.mem_filter.mp hx).2)))

/-- A bound on duplicate excess gives a lower bound on the number of distinct roots. -/
theorem fixedPointPoly_rootDefect_bound_of_roots_count_excess_le
    (c : ℂ) {p D : ℕ} (hp : 1 ≤ p)
    (hD : (∑ z ∈ (fixedPointPoly c p).roots.toFinset,
      ((fixedPointPoly c p).roots.count z - 1)) ≤ D) :
    2 ^ p ≤ (fixedPointPoly c p).roots.toFinset.card + D := by
  have hroots_card : (fixedPointPoly c p).roots.card = 2 ^ p := by
    rw [IsAlgClosed.card_roots_eq_natDegree, fixedPointPoly_natDegree c hp]
  rw [← hroots_card]
  calc
    (fixedPointPoly c p).roots.card =
        (fixedPointPoly c p).roots.toFinset.card +
          ∑ z ∈ (fixedPointPoly c p).roots.toFinset,
            ((fixedPointPoly c p).roots.count z - 1) :=
      multiset_card_eq_toFinset_card_add_count_excess _
    _ ≤ (fixedPointPoly c p).roots.toFinset.card + D :=
      Nat.add_le_add_left hD _

/-- Eventual duplicate-excess bounds supply the eventual root-defect input consumed by the active
root-defect hRigid route. -/
theorem eventually_fixedPointPoly_rootDefect_bound_of_eventually_roots_count_excess_le
    (c : ℂ) (D : ℕ)
    (hD : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧
      (∑ z ∈ (fixedPointPoly c p).roots.toFinset,
        ((fixedPointPoly c p).roots.count z - 1)) ≤ D) :
    ∀ᶠ p : ℕ in atTop,
      2 ^ p ≤ (fixedPointPoly c p).roots.toFinset.card + D :=
  hD.mono fun _ hp =>
    fixedPointPoly_rootDefect_bound_of_roots_count_excess_le c hp.1 hp.2

/-- A finite set containing all multiple fixed roots, with bounded local duplicate excess, supplies a
root-defect bound. -/
theorem fixedPointPoly_rootDefect_bound_of_multiple_roots_subset
    (c : ℂ) {p L : ℕ} (hp : 1 ≤ p) (E : Finset ℂ)
    (hsimple_off : ∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∉ E →
      (fixedPointPoly c p).roots.count z ≤ 1)
    (hexcess_on : ∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ E →
      (fixedPointPoly c p).roots.count z - 1 ≤ L) :
    2 ^ p ≤ (fixedPointPoly c p).roots.toFinset.card + E.card * L :=
  fixedPointPoly_rootDefect_bound_of_roots_count_excess_le c hp
    (multiset_count_excess_le_card_mul_of_multiple_support
      (fixedPointPoly c p).roots E L hsimple_off hexcess_on)

/-- If a finite set contains the multiplier-one fixed roots, then it contains all multiple fixed roots.
Together with a local duplicate-excess bound on that finite set, this supplies root defect. -/
theorem fixedPointPoly_rootDefect_bound_of_multiplierOne_subset
    (c : ℂ) {p L : ℕ} (hp : 1 ≤ p) (E : Finset ℂ)
    (hE : multiplierOneFixedPointRoots c p ⊆ E)
    (hexcess_on : ∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ E →
      (fixedPointPoly c p).roots.count z - 1 ≤ L) :
    2 ^ p ≤ (fixedPointPoly c p).roots.toFinset.card + E.card * L :=
  fixedPointPoly_rootDefect_bound_of_multiple_roots_subset c hp E
    (by
      intro z _hzroot hzE
      by_contra hle
      exact hzE (hE (mem_multiplierOneFixedPointRoots_of_one_lt_roots_count c hp (not_le.mp hle))))
    hexcess_on

/-- Eventual finite support for multiple fixed roots supplies the eventual root-defect input consumed
by the active hRigid route. -/
theorem eventually_fixedPointPoly_rootDefect_bound_of_eventually_multiple_roots_subset
    (c : ℂ) (E : Finset ℂ) (L : ℕ)
    (hmultiple : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧
      (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∉ E →
        (fixedPointPoly c p).roots.count z ≤ 1) ∧
      (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ E →
        (fixedPointPoly c p).roots.count z - 1 ≤ L)) :
    ∀ᶠ p : ℕ in atTop,
      2 ^ p ≤ (fixedPointPoly c p).roots.toFinset.card + E.card * L :=
  hmultiple.mono fun _ hp =>
    fixedPointPoly_rootDefect_bound_of_multiple_roots_subset c hp.1 E hp.2.1 hp.2.2

/-- Eventual finite support for multiplier-one fixed roots supplies the eventual root-defect input
consumed by the active hRigid route. -/
theorem eventually_fixedPointPoly_rootDefect_bound_of_eventually_multiplierOne_subset
    (c : ℂ) (E : Finset ℂ) (L : ℕ)
    (hmultiplierOne : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧
      multiplierOneFixedPointRoots c p ⊆ E ∧
      (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ E →
        (fixedPointPoly c p).roots.count z - 1 ≤ L)) :
    ∀ᶠ p : ℕ in atTop,
      2 ^ p ≤ (fixedPointPoly c p).roots.toFinset.card + E.card * L :=
  hmultiplierOne.mono fun _ hp =>
    fixedPointPoly_rootDefect_bound_of_multiplierOne_subset c hp.1 E hp.2.1 hp.2.2

/-- If the no-extra budget plus the non-strong root count is below the number of distinct fixed roots,
then the strong-root pool beats the budget.  This is the separability-free replacement for
`squarefreeBadDegreeBudget_lt_strongFixedPointRoots_card_of_add_nonStrong_lt`. -/
theorem squarefreeBadDegreeBudget_lt_strongFixedPointRoots_card_of_add_nonStrong_lt_roots
    (c : ℂ) (p : ℕ) (P : Polynomial (Polynomial ℂ)) (e : Polynomial ℂ)
    (B : Finset (Polynomial ℂ))
    (hbound :
      squarefreeBadDegreeBudget P e B + (nonStrongFixedPointRoots c p).card <
        (fixedPointPoly c p).roots.toFinset.card) :
    squarefreeBadDegreeBudget P e B < (strongFixedPointRoots c p).card := by
  have hsplit :=
    strongFixedPointRoots_card_add_nonStrongFixedPointRoots_card_eq_roots_card c p
  omega

/-- **Bounded-root-defect period selector with explicit denominator witnesses.**

Assume the distinct fixed-root deficit is eventually bounded by `D`, all non-strong roots are
eventually contained in a finite set `E`, and an explicit denominator witness has eventually bounded
degree.  Then some large period has enough strong distinct roots to beat the squarefree budget. -/
theorem exists_period_denominator_of_eventually_nonStrong_subset_of_bounded_rootDefect_denominator_witness
    (c : ℂ) (P : Polynomial (Polynomial ℂ)) (E : Finset ℂ) (D M : ℕ)
    (hrootDefect : ∀ᶠ p : ℕ in atTop,
      2 ^ p ≤ (fixedPointPoly c p).roots.toFinset.card + D)
    (hE : ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E)
    (hdenom : ∀ᶠ p : ℕ in atTop,
      ∃ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
        e ≠ 0 ∧ (Polynomial.C e) * (compRelPoly c p P) = P * S ∧ e.natDegree ≤ M) :
    ∃ (p : ℕ) (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
      e ≠ 0 ∧ (Polynomial.C e) * (compRelPoly c p P) = P * S ∧
      squarefreeBadDegreeBudget P e ∅ < (strongFixedPointRoots c p).card := by
  have htwo : Tendsto (fun p : ℕ => 2 ^ p) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (show 1 < (2 : ℕ) by norm_num)
  obtain ⟨p, hdef, hEsub, hdenp, hbig⟩ :=
    (hrootDefect.and (hE.and (hdenom.and
      (htwo.eventually_gt_atTop ((M + squarefreeStaticDegreeBudget P) + E.card + D))))).exists
  obtain ⟨e, S, he0, hPS, hdeg⟩ := hdenp
  refine ⟨p, e, S, he0, hPS, ?_⟩
  have hbudget : squarefreeBadDegreeBudget P e ∅ ≤ M + squarefreeStaticDegreeBudget P :=
    le_trans (squarefreeBadDegreeBudget_empty_le_natDegree_add_static P e)
      (Nat.add_le_add_right hdeg (squarefreeStaticDegreeBudget P))
  have hcard : (nonStrongFixedPointRoots c p).card ≤ E.card := Finset.card_le_card hEsub
  have hlt_roots :
      squarefreeBadDegreeBudget P e ∅ + (nonStrongFixedPointRoots c p).card <
        (fixedPointPoly c p).roots.toFinset.card := by
    have hlt_with_defect :
        squarefreeBadDegreeBudget P e ∅ + (nonStrongFixedPointRoots c p).card + D <
          (fixedPointPoly c p).roots.toFinset.card + D := by
      omega
    omega
  exact
    squarefreeBadDegreeBudget_lt_strongFixedPointRoots_card_of_add_nonStrong_lt_roots
      c p P e ∅ hlt_roots

/-- **Explicit-denominator strong-root-card input for absolute connected `φ_c` transcendence.**

This is the strong-root analogue of the chosen-denominator no-extra interface, but the denominator is
supplied explicitly together with the period.  It does not require fixed-point separability. -/
theorem phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_denominatorWitness_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ (P : Polynomial (Polynomial ℂ)) (_hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (_hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
        (_hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support,
            (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (p : ℕ) (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
          e ≠ 0 ∧ (Polynomial.C e) * (compRelPoly c p P) = P * S ∧
          squarefreeBadDegreeBudget P e ∅ < (strongFixedPointRoots c p).card) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_chosen_denominator_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, e, S, he0, hPS, hcard⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨hlead, hderivLead, hres, hconst⟩ :=
    minimal_relation_squarefree_bad_polys_ne_zero
      hUo hUc c hU P hP0 hdeg hPrel hPmin hconst_poly
  have hA0 : ∀ q ∈ squarefreeBadFamily P e ∅, q ≠ 0 :=
    squarefreeBadFamily_ne_zero he0 hlead hderivLead hres hconst (by simp)
  obtain ⟨z₀, hzroot, havoid, hnorm⟩ :=
    exists_strong_fixedPoint_avoiding_squarefreeBadFamily_of_budget_card c p P e ∅ hA0 hcard
  have hp : 1 ≤ p := by
    cases p with
    | zero =>
      have hzero : (strongFixedPointRoots c 0).card = 0 := by
        simp [strongFixedPointRoots]
      rw [hzero] at hcard
      omega
    | succ k => omega
  have hFz : (quadratic c)^[p] z₀ = z₀ := by
    rw [← fixedPointPoly_isRoot_iff]
    exact (mem_roots (fixedPointPoly_ne_zero c hp)).mp (Multiset.mem_toFinset.mp hzroot)
  refine ⟨p, e, S, ∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z₀, z₀,
    he0, hPS, hFz, hasDerivAt_quadratic_iterate c z₀ p, hnorm,
    havoid e (mem_squarefreeBadFamily_denominator P e ∅),
    ?_,
    havoid P.leadingCoeff (mem_squarefreeBadFamily_leadingCoeff P e ∅),
    havoid (P.coeff 0) (mem_squarefreeBadFamily_constCoeff P e ∅)⟩
  exact separable_specialization_of_avoids_squarefree_bad_locus P
    (mem_squarefreeBadFamily_leadingCoeff P e ∅)
    (mem_squarefreeBadFamily_derivative_leadingCoeff P e ∅)
    (mem_squarefreeBadFamily_resultant P e ∅)
    havoid

/-- **Bounded-root-defect content-denominator input for absolute connected `φ_c` transcendence.**

For each minimal relation, the caller supplies only a finite eventual exceptional set for non-strong
roots and an eventual bound on the distinct fixed-root deficit.  The denominator is created
internally from `P.content`, and separability/no-multiplier-one is not required. -/
theorem phiMero_transcendental_of_repelling_eventually_rootDefect_contentDenominator_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ (P : Polynomial (Polynomial ℂ)) (_hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (_hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
        (_hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support,
            (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (E : Finset ℂ) (D : ℕ),
          (∀ᶠ p : ℕ in atTop,
            2 ^ p ≤ (fixedPointPoly c p).roots.toFinset.card + D) ∧
          (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply
    phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_denominatorWitness_noExtra_input
      hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨E, D, hrootDefect, hE⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  exact
    exists_period_denominator_of_eventually_nonStrong_subset_of_bounded_rootDefect_denominator_witness
      c P E D P.content.natDegree hrootDefect hE
      (eventually_content_compRelPoly_denominatorWitness_of_minimal
        hUo hUne c hU P hP0 hPrel hPmin)

/-- **Multiplier-one content-denominator input for absolute connected `φ_c` transcendence.**

This is the active hRigid surface: instead of asking for an abstract fixed-root deficit bound, the
caller supplies a finite eventual support for multiplier-one fixed roots and a uniform local bound
for duplicate root excess on that support.  Lean proves that all multiple fixed roots lie in the
multiplier-one locus and converts the input to the root-defect inequality internally. -/
theorem phiMero_transcendental_of_repelling_eventually_multiplierOne_contentDenominator_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ (P : Polynomial (Polynomial ℂ)) (_hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (_hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
        (_hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support,
            (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (E F : Finset ℂ) (L : ℕ),
          (∀ᶠ p : ℕ in atTop,
            1 ≤ p ∧
            multiplierOneFixedPointRoots c p ⊆ F ∧
            (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ F →
              (fixedPointPoly c p).roots.count z - 1 ≤ L)) ∧
          (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_eventually_rootDefect_contentDenominator_noExtra_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨E, F, L, hmultiplierOne, hE⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  exact ⟨E, F.card * L,
    eventually_fixedPointPoly_rootDefect_bound_of_eventually_multiplierOne_subset
      c F L hmultiplierOne,
    hE⟩

end Bottcher
