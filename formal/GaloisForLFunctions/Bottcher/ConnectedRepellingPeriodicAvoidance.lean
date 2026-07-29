/-
# Absolute connected transcendence from finite periodic-point avoidance

This is the finite-count replacement for the stale fixed-period accumulation interface.  After the
denominator-clearing step selects a period and denominator, it is enough to give a finite bad set
strictly smaller than the separable fixed-point set and prove that every remaining fixed point has the
local repelling/fibre data required by `ConnectedRepellingFibreInput`.
-/
import GaloisForLFunctions.Bottcher.ConnectedRepellingFibreInput
import GaloisForLFunctions.Bottcher.PeriodicPointAvoidance

open Polynomial Filter Topology Set

namespace Bottcher

variable {U : Set ℂ}

/-- **Absolute connected `φ_c`-transcendence from finite fixed-point avoidance.**

For each minimal relation, the callback chooses one period `p` with separable fixed-point polynomial.
For every selected denominator identity it then supplies a finite bad set `B` of cardinality `< 2^p`;
the theorem chooses a period-`p` fixed point outside `B` and passes its local data to the existing
selected-denominator reduction. -/
theorem phiMero_transcendental_of_repelling_fixedPoint_avoidance_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ p : ℕ, 1 ≤ p ∧ (fixedPointPoly c p).Separable ∧
          ∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
            (Polynomial.C e) * (compRelPoly c p P) = P * S →
            ∃ B : Finset ℂ, B.card < 2 ^ p ∧
              ∀ z₀ ∈ (fixedPointPoly c p).roots.toFinset, z₀ ∉ B →
                ∃ lam : ℂ,
                  HasDerivAt ((quadratic c)^[p]) lam z₀ ∧
                  (2 ^ p : ℝ) < ‖lam‖ ∧
                  e.eval z₀ ≠ 0 ∧
                  (P.map (Polynomial.evalRingHom z₀)).Separable ∧
                  (P.coeff P.natDegree).eval z₀ ≠ 0 ∧
                  (P.coeff 0).eval z₀ ≠ 0) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_selected_denominator_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, hp, hsep, hpinput⟩ := hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  refine ⟨p, ?_⟩
  intro e S he0 hPS
  obtain ⟨B, hBcard, hgood⟩ := hpinput e S he0 hPS
  obtain ⟨z₀, hzroot, hzB⟩ := exists_fixedPointPoly_root_notMem_finset c hp hsep B hBcard
  have hFz : (quadratic c)^[p] z₀ = z₀ := by
    rw [← fixedPointPoly_isRoot_iff]
    exact (mem_roots (fixedPointPoly_ne_zero c hp)).mp (Multiset.mem_toFinset.mp hzroot)
  obtain ⟨lam, hlam, hnorm, hez, hsepz, hlead, hconst⟩ := hgood z₀ hzroot hzB
  exact ⟨lam, z₀, hFz, hlam, hnorm, hez, hsepz, hlead, hconst⟩

/-- **Absolute connected `φ_c`-transcendence from a finite polynomial bad locus.**

This packages the finite bad set in
`phiMero_transcendental_of_repelling_fixedPoint_avoidance_input` as the union of zero loci of a finite
family `A` of nonzero polynomials.  The theorem supplies denominator, leading-coefficient and
constant-coefficient avoidance automatically from membership of those polynomials in `A`; the callback
only has to prove the dynamical repulsion and fibre separability at fixed points avoiding every
polynomial in `A`. -/
theorem phiMero_transcendental_of_repelling_polynomial_bad_locus_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ p : ℕ, 1 ≤ p ∧ (fixedPointPoly c p).Separable ∧
          ∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
            (Polynomial.C e) * (compRelPoly c p P) = P * S →
            ∃ A : Finset (Polynomial ℂ),
              e ∈ A ∧ P.coeff P.natDegree ∈ A ∧ P.coeff 0 ∈ A ∧
              (∀ q ∈ A, q ≠ 0) ∧
              (∑ q ∈ A, q.natDegree) < 2 ^ p ∧
              ∀ z₀ ∈ (fixedPointPoly c p).roots.toFinset,
                (∀ q ∈ A, q.eval z₀ ≠ 0) →
                ∃ lam : ℂ,
                  HasDerivAt ((quadratic c)^[p]) lam z₀ ∧
                  (2 ^ p : ℝ) < ‖lam‖ ∧
                  (P.map (Polynomial.evalRingHom z₀)).Separable) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_fixedPoint_avoidance_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, hp, hsep, hpinput⟩ := hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  refine ⟨p, hp, hsep, ?_⟩
  intro e S he0 hPS
  obtain ⟨A, heA, hleadA, hconstA, hA0, hdegA, hgood⟩ := hpinput e S he0 hPS
  let B : Finset ℂ := A.biUnion fun q => q.roots.toFinset
  have hBcard : B.card < 2 ^ p := lt_of_le_of_lt (roots_biUnion_card_le_sum_natDegree A) hdegA
  refine ⟨B, hBcard, ?_⟩
  intro z₀ hzroot hzB
  have havoid : ∀ q ∈ A, q.eval z₀ ≠ 0 := by
    intro q hqA
    exact eval_ne_zero_of_notMem_roots_biUnion hqA (hA0 q hqA) hzB
  obtain ⟨lam, hlam, hnorm, hsepz⟩ := hgood z₀ hzroot havoid
  exact ⟨lam, hlam, hnorm, havoid e heA, hsepz,
    havoid (P.coeff P.natDegree) hleadA, havoid (P.coeff 0) hconstA⟩

/-- Avoiding the leading, derivative-leading, and resultant bad polynomials makes the fibre separable. -/
theorem separable_specialization_of_avoids_squarefree_bad_locus
    (P : Polynomial (Polynomial ℂ)) {A : Finset (Polynomial ℂ)} {z₀ : ℂ}
    (hleadA : P.leadingCoeff ∈ A)
    (hderivLeadA : (Polynomial.derivative P).leadingCoeff ∈ A)
    (hresA : Polynomial.resultant P (Polynomial.derivative P) ∈ A)
    (havoid : ∀ q ∈ A, q.eval z₀ ≠ 0) :
    (P.map (Polynomial.evalRingHom z₀)).Separable := by
  exact HolomorphicIFT.separable_specialize z₀
    (havoid P.leadingCoeff hleadA)
    (havoid (Polynomial.derivative P).leadingCoeff hderivLeadA)
    (havoid (Polynomial.resultant P (Polynomial.derivative P)) hresA)

/-- Positive degree makes the `Y`-derivative's leading coefficient nonzero. -/
theorem derivative_leadingCoeff_ne_zero_of_natDegree_pos (P : Polynomial (Polynomial ℂ))
    (hdeg : 1 ≤ P.natDegree) :
    (Polynomial.derivative P).leadingCoeff ≠ 0 := by
  have hderiv : Polynomial.derivative P ≠ 0 := by
    intro h
    have := Polynomial.derivative_eq_zero.mp h
    omega
  exact Polynomial.leadingCoeff_ne_zero.mpr hderiv

/-- The standard squarefree bad-locus polynomials for a minimal relation are nonzero. -/
theorem minimal_relation_squarefree_bad_polys_ne_zero {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0) (hdeg : 1 ≤ P.natDegree)
    (hPrel : ∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
        (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        P.natDegree ≤ R.natDegree)
    (hconst : P.coeff 0 ≠ 0) :
    P.leadingCoeff ≠ 0 ∧
      (Polynomial.derivative P).leadingCoeff ≠ 0 ∧
      Polynomial.resultant P (Polynomial.derivative P) ≠ 0 ∧
      P.coeff 0 ≠ 0 := by
  have hsepFrac :
      (P.map (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))).Separable :=
    minimal_relation_fraction_field_separable hUo hUc c hU P hP0 hdeg hPrel hPmin
  exact ⟨Polynomial.leadingCoeff_ne_zero.mpr hP0,
    derivative_leadingCoeff_ne_zero_of_natDegree_pos P hdeg,
    HolomorphicIFT.resultant_ne_zero_of_separable P hsepFrac,
    hconst⟩

/-- The standard squarefree bad-locus family, plus caller-supplied extra bad polynomials. -/
noncomputable def squarefreeBadFamily (P : Polynomial (Polynomial ℂ)) (e : Polynomial ℂ)
    (B : Finset (Polynomial ℂ)) : Finset (Polynomial ℂ) := by
  classical
  exact insert e <|
    insert P.leadingCoeff <|
    insert (Polynomial.derivative P).leadingCoeff <|
    insert (Polynomial.resultant P (Polynomial.derivative P)) <|
    insert (P.coeff 0) B

theorem mem_squarefreeBadFamily_denominator (P : Polynomial (Polynomial ℂ)) (e : Polynomial ℂ)
    (B : Finset (Polynomial ℂ)) :
    e ∈ squarefreeBadFamily P e B := by
  classical
  simp [squarefreeBadFamily]

theorem mem_squarefreeBadFamily_leadingCoeff (P : Polynomial (Polynomial ℂ)) (e : Polynomial ℂ)
    (B : Finset (Polynomial ℂ)) :
    P.leadingCoeff ∈ squarefreeBadFamily P e B := by
  classical
  simp [squarefreeBadFamily]

theorem mem_squarefreeBadFamily_derivative_leadingCoeff (P : Polynomial (Polynomial ℂ))
    (e : Polynomial ℂ) (B : Finset (Polynomial ℂ)) :
    (Polynomial.derivative P).leadingCoeff ∈ squarefreeBadFamily P e B := by
  classical
  simp [squarefreeBadFamily]

theorem mem_squarefreeBadFamily_resultant (P : Polynomial (Polynomial ℂ)) (e : Polynomial ℂ)
    (B : Finset (Polynomial ℂ)) :
    Polynomial.resultant P (Polynomial.derivative P) ∈ squarefreeBadFamily P e B := by
  classical
  simp [squarefreeBadFamily]

theorem mem_squarefreeBadFamily_constCoeff (P : Polynomial (Polynomial ℂ)) (e : Polynomial ℂ)
    (B : Finset (Polynomial ℂ)) :
    P.coeff 0 ∈ squarefreeBadFamily P e B := by
  classical
  simp [squarefreeBadFamily]

/-- Nonvanishing of the standard squarefree bad-locus family reduces to the extra family. -/
theorem squarefreeBadFamily_ne_zero {P : Polynomial (Polynomial ℂ)} {e : Polynomial ℂ}
    {B : Finset (Polynomial ℂ)}
    (he : e ≠ 0) (hlead : P.leadingCoeff ≠ 0)
    (hderivLead : (Polynomial.derivative P).leadingCoeff ≠ 0)
    (hres : Polynomial.resultant P (Polynomial.derivative P) ≠ 0)
    (hconst : P.coeff 0 ≠ 0) (hB : ∀ q ∈ B, q ≠ 0) :
    ∀ q ∈ squarefreeBadFamily P e B, q ≠ 0 := by
  classical
  intro q hq
  simp [squarefreeBadFamily] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | hqB
  · exact he
  · exact hlead
  · exact hderivLead
  · exact hres
  · exact hconst
  · exact hB q hqB

theorem sum_insert_natDegree_le_add (q : Polynomial ℂ) (B : Finset (Polynomial ℂ)) :
    (∑ r ∈ insert q B, r.natDegree) ≤ q.natDegree + ∑ r ∈ B, r.natDegree := by
  classical
  by_cases hq : q ∈ B
  · rw [Finset.insert_eq_of_mem hq]
    exact Nat.le_add_left _ _
  · rw [Finset.sum_insert hq]

/-- Explicit degree budget for the standard squarefree bad-locus family plus extras. -/
noncomputable def squarefreeBadDegreeBudget (P : Polynomial (Polynomial ℂ)) (e : Polynomial ℂ)
    (B : Finset (Polynomial ℂ)) : ℕ :=
  e.natDegree + P.leadingCoeff.natDegree +
    (Polynomial.derivative P).leadingCoeff.natDegree +
    (Polynomial.resultant P (Polynomial.derivative P)).natDegree +
    (P.coeff 0).natDegree +
    ∑ q ∈ B, q.natDegree

/-- The actual finite-family degree sum is bounded by the explicit standard budget. -/
theorem squarefreeBadFamily_sum_natDegree_le_budget
    (P : Polynomial (Polynomial ℂ)) (e : Polynomial ℂ) (B : Finset (Polynomial ℂ)) :
    (∑ q ∈ squarefreeBadFamily P e B, q.natDegree) ≤
      squarefreeBadDegreeBudget P e B := by
  classical
  unfold squarefreeBadDegreeBudget
  rw [squarefreeBadFamily]
  have h0 := sum_insert_natDegree_le_add (P.coeff 0) B
  have h1 := sum_insert_natDegree_le_add
    (Polynomial.resultant P (Polynomial.derivative P)) (insert (P.coeff 0) B)
  have h2 := sum_insert_natDegree_le_add
    (Polynomial.derivative P).leadingCoeff
      (insert (Polynomial.resultant P (Polynomial.derivative P)) (insert (P.coeff 0) B))
  have h3 := sum_insert_natDegree_le_add P.leadingCoeff
    (insert (Polynomial.derivative P).leadingCoeff
      (insert (Polynomial.resultant P (Polynomial.derivative P)) (insert (P.coeff 0) B)))
  have h4 := sum_insert_natDegree_le_add e
    (insert P.leadingCoeff
      (insert (Polynomial.derivative P).leadingCoeff
        (insert (Polynomial.resultant P (Polynomial.derivative P)) (insert (P.coeff 0) B))))
  omega

/-- The explicit squarefree budget produces a fixed point avoiding the whole standard bad family. -/
theorem exists_fixedPointPoly_root_avoiding_squarefreeBadFamily_of_budget (c : ℂ) {p : ℕ}
    (hp : 1 ≤ p) (hsep : (fixedPointPoly c p).Separable)
    (P : Polynomial (Polynomial ℂ)) (e : Polynomial ℂ) (B : Finset (Polynomial ℂ))
    (hA0 : ∀ q ∈ squarefreeBadFamily P e B, q ≠ 0)
    (hbudget : squarefreeBadDegreeBudget P e B < 2 ^ p) :
    ∃ z₀, z₀ ∈ (fixedPointPoly c p).roots.toFinset ∧
      (quadratic c)^[p] z₀ = z₀ ∧
      ∀ q ∈ squarefreeBadFamily P e B, q.eval z₀ ≠ 0 := by
  exact exists_fixedPointPoly_root_avoiding_polys_of_sum_natDegree_lt c hp hsep
    (squarefreeBadFamily P e B) hA0
    (lt_of_le_of_lt (squarefreeBadFamily_sum_natDegree_le_budget P e B) hbudget)

/-- Period-`p` fixed roots satisfying the explicit strong orbit-product inequality. -/
noncomputable def strongFixedPointRoots (c : ℂ) (p : ℕ) : Finset ℂ := by
  classical
  exact (fixedPointPoly c p).roots.toFinset.filter fun z =>
    (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖

/-- Period-`p` fixed roots not satisfying the explicit strong orbit-product inequality. -/
noncomputable def nonStrongFixedPointRoots (c : ℂ) (p : ℕ) : Finset ℂ := by
  classical
  exact (fixedPointPoly c p).roots.toFinset.filter fun z =>
    ¬ (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖

theorem mem_strongFixedPointRoots {c z : ℂ} {p : ℕ} :
    z ∈ strongFixedPointRoots c p ↔
      z ∈ (fixedPointPoly c p).roots.toFinset ∧
        (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖ := by
  classical
  simp [strongFixedPointRoots]

theorem mem_nonStrongFixedPointRoots {c z : ℂ} {p : ℕ} :
    z ∈ nonStrongFixedPointRoots c p ↔
      z ∈ (fixedPointPoly c p).roots.toFinset ∧
        ¬ (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖ := by
  classical
  simp [nonStrongFixedPointRoots]

/-- At a fixed point of `f_c`, the period-`p` orbit product is `(2z)^p`. -/
theorem strongFixedPointRoots_orbitProduct_at_fixed {c z : ℂ} (hfix : quadratic c z = z)
    (p : ℕ) :
    (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) = ((2 : ℂ) * z) ^ p := by
  rw [Finset.prod_congr rfl (fun k _ => by rw [Function.iterate_fixed hfix k]),
    Finset.prod_const, Finset.card_range]

/-- A fixed point whose period-`p` multiplier norm is stronger than `2^p` is a strong root. -/
theorem mem_strongFixedPointRoots_of_fixed_pow_norm {c z : ℂ} {p : ℕ}
    (hp : 1 ≤ p) (hfix : quadratic c z = z)
    (hstrong : (2 ^ p : ℝ) < ‖(2 : ℂ) * z‖ ^ p) :
    z ∈ strongFixedPointRoots c p := by
  rw [mem_strongFixedPointRoots]
  refine ⟨fixed_mem_fixedPointPoly_roots hp hfix, ?_⟩
  rw [strongFixedPointRoots_orbitProduct_at_fixed hfix p, norm_pow]
  exact hstrong

/-- A fixed point with multiplier norm above `2` is strong at every positive period. -/
theorem mem_strongFixedPointRoots_of_fixed_norm_gt_two {c z : ℂ} {p : ℕ}
    (hp : 1 ≤ p) (hfix : quadratic c z = z)
    (hgt : (2 : ℝ) < ‖(2 : ℂ) * z‖) :
    z ∈ strongFixedPointRoots c p := by
  apply mem_strongFixedPointRoots_of_fixed_pow_norm hp hfix
  have hp0 : p ≠ 0 := by omega
  have hpow : (2 : ℝ) ^ p < ‖(2 : ℂ) * z‖ ^ p :=
    pow_lt_pow_left₀ hgt (by norm_num) hp0
  simpa using hpow

/-- A fixed point with multiplier norm above `2` makes the strong-root pool nonempty. -/
theorem strongFixedPointRoots_card_pos_of_fixed_norm_gt_two {c z : ℂ} {p : ℕ}
    (hp : 1 ≤ p) (hfix : quadratic c z = z)
    (hgt : (2 : ℝ) < ‖(2 : ℂ) * z‖) :
    0 < (strongFixedPointRoots c p).card := by
  exact Finset.card_pos.mpr
    ⟨z, mem_strongFixedPointRoots_of_fixed_norm_gt_two hp hfix hgt⟩

/-- A finite set of fixed points with multiplier norm above `2` embeds in the strong-root pool. -/
theorem fixedNormGtTwo_finset_subset_strongFixedPointRoots {c : ℂ} {p : ℕ}
    (hp : 1 ≤ p) (E : Finset ℂ)
    (hfix : ∀ z ∈ E, quadratic c z = z)
    (hgt : ∀ z ∈ E, (2 : ℝ) < ‖(2 : ℂ) * z‖) :
    E ⊆ strongFixedPointRoots c p := by
  intro z hz
  exact mem_strongFixedPointRoots_of_fixed_norm_gt_two hp (hfix z hz) (hgt z hz)

/-- Strong fixed points with multiplier norm above `2` give a cardinality lower bound. -/
theorem fixedNormGtTwo_finset_card_le_strongFixedPointRoots_card {c : ℂ} {p : ℕ}
    (hp : 1 ≤ p) (E : Finset ℂ)
    (hfix : ∀ z ∈ E, quadratic c z = z)
    (hgt : ∀ z ∈ E, (2 : ℝ) < ‖(2 : ℂ) * z‖) :
    E.card ≤ (strongFixedPointRoots c p).card :=
  Finset.card_le_card (fixedNormGtTwo_finset_subset_strongFixedPointRoots hp E hfix hgt)

/-- A finite set of fixed points with multiplier norm above `2` can discharge the strong-root budget. -/
theorem squarefreeBadDegreeBudget_lt_strongFixedPointRoots_card_of_fixedNormGtTwo_finset
    {c : ℂ} {p : ℕ} (hp : 1 ≤ p) (P : Polynomial (Polynomial ℂ))
    (e : Polynomial ℂ) (B : Finset (Polynomial ℂ)) (E : Finset ℂ)
    (hfix : ∀ z ∈ E, quadratic c z = z)
    (hgt : ∀ z ∈ E, (2 : ℝ) < ‖(2 : ℂ) * z‖)
    (hbudget : squarefreeBadDegreeBudget P e B < E.card) :
    squarefreeBadDegreeBudget P e B < (strongFixedPointRoots c p).card :=
  lt_of_lt_of_le hbudget
    (fixedNormGtTwo_finset_card_le_strongFixedPointRoots_card hp E hfix hgt)

theorem strongFixedPointRoots_subset_roots (c : ℂ) (p : ℕ) :
    strongFixedPointRoots c p ⊆ (fixedPointPoly c p).roots.toFinset := by
  intro z hz
  exact (mem_strongFixedPointRoots.mp hz).1

theorem nonStrongFixedPointRoots_subset_roots (c : ℂ) (p : ℕ) :
    nonStrongFixedPointRoots c p ⊆ (fixedPointPoly c p).roots.toFinset := by
  intro z hz
  exact (mem_nonStrongFixedPointRoots.mp hz).1

theorem strongFixedPointRoots_card_le_roots (c : ℂ) (p : ℕ) :
    (strongFixedPointRoots c p).card ≤ (fixedPointPoly c p).roots.toFinset.card := by
  exact Finset.card_le_card (strongFixedPointRoots_subset_roots c p)

/-- Strong and non-strong roots partition the fixed-root finset. -/
theorem strongFixedPointRoots_card_add_nonStrongFixedPointRoots_card_eq_roots_card
    (c : ℂ) (p : ℕ) :
    (strongFixedPointRoots c p).card + (nonStrongFixedPointRoots c p).card =
      (fixedPointPoly c p).roots.toFinset.card := by
  classical
  exact Finset.card_filter_add_card_filter_not
    (fun z => (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖)

/-- A budget plus non-strong-root count below `2^p` implies the strong-root pool beats the budget. -/
theorem squarefreeBadDegreeBudget_lt_strongFixedPointRoots_card_of_add_nonStrong_lt
    (c : ℂ) {p : ℕ} (hp : 1 ≤ p) (hsep : (fixedPointPoly c p).Separable)
    (P : Polynomial (Polynomial ℂ)) (e : Polynomial ℂ) (B : Finset (Polynomial ℂ))
    (hbound :
      squarefreeBadDegreeBudget P e B + (nonStrongFixedPointRoots c p).card < 2 ^ p) :
    squarefreeBadDegreeBudget P e B < (strongFixedPointRoots c p).card := by
  have hsplit := strongFixedPointRoots_card_add_nonStrongFixedPointRoots_card_eq_roots_card c p
  rw [fixedPointPoly_roots_card c hp hsep] at hsplit
  rw [← hsplit] at hbound
  exact Nat.lt_of_add_lt_add_right hbound

/-- If every fixed root outside `E` is strong, then every non-strong fixed root lies in `E`. -/
theorem nonStrongFixedPointRoots_subset_of_strong_off_exceptional (c : ℂ) (p : ℕ)
    (E : Finset ℂ)
    (hstrong : ∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∉ E →
      (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖) :
    nonStrongFixedPointRoots c p ⊆ E := by
  intro z hz
  by_contra hzE
  exact (mem_nonStrongFixedPointRoots.mp hz).2
    (hstrong z (mem_nonStrongFixedPointRoots.mp hz).1 hzE)

/-- A finite exceptional set containing all non-strong fixed roots bounds the non-strong count. -/
theorem squarefreeBadDegreeBudget_add_nonStrong_card_lt_of_exceptional
    (c : ℂ) {p : ℕ} (P : Polynomial (Polynomial ℂ)) (e : Polynomial ℂ)
    (B : Finset (Polynomial ℂ)) (E : Finset ℂ)
    (hstrong : ∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∉ E →
      (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖)
    (hbound : squarefreeBadDegreeBudget P e B + E.card < 2 ^ p) :
    squarefreeBadDegreeBudget P e B + (nonStrongFixedPointRoots c p).card < 2 ^ p := by
  have hcard : (nonStrongFixedPointRoots c p).card ≤ E.card :=
    Finset.card_le_card (nonStrongFixedPointRoots_subset_of_strong_off_exceptional c p E hstrong)
  exact lt_of_le_of_lt
    (Nat.add_le_add_left hcard (squarefreeBadDegreeBudget P e B)) hbound

/-- A point outside the root finset of a nonzero polynomial has nonzero evaluation. -/
theorem eval_ne_zero_of_notMem_roots {q : Polynomial ℂ} (hq0 : q ≠ 0) {z : ℂ}
    (hz : z ∉ q.roots.toFinset) :
    q.eval z ≠ 0 := by
  intro hqz
  exact hz (Multiset.mem_toFinset.mpr ((mem_roots hq0).mpr hqz))

/-- The polynomial exceptional locus attached to a finite exceptional point set. -/
noncomputable def exceptionalPoly (E : Finset ℂ) : Polynomial ℂ :=
  ∏ a ∈ E, (X - C a)

/-- The finite-set exceptional polynomial is nonzero. -/
theorem exceptionalPoly_ne_zero (E : Finset ℂ) : exceptionalPoly E ≠ 0 := by
  classical
  unfold exceptionalPoly
  rw [Finset.prod_ne_zero_iff]
  intro a ha
  exact Polynomial.X_sub_C_ne_zero a

/-- The finite-set exceptional polynomial has degree exactly the size of the set. -/
theorem exceptionalPoly_natDegree (E : Finset ℂ) :
    (exceptionalPoly E).natDegree = E.card := by
  classical
  unfold exceptionalPoly
  rw [Polynomial.natDegree_prod]
  · simp
  · intro a ha
    exact Polynomial.X_sub_C_ne_zero a

/-- The finite-set exceptional polynomial vanishes on the exceptional set. -/
theorem exceptionalPoly_eval_eq_zero_of_mem {E : Finset ℂ} {z : ℂ} (hz : z ∈ E) :
    (exceptionalPoly E).eval z = 0 := by
  classical
  unfold exceptionalPoly
  rw [Polynomial.eval_prod]
  rw [Finset.prod_eq_zero_iff]
  exact ⟨z, hz, by simp⟩

/-- The explicit standard budget when no extra bad polynomials are supplied. -/
theorem squarefreeBadDegreeBudget_empty (P : Polynomial (Polynomial ℂ)) (e : Polynomial ℂ) :
    squarefreeBadDegreeBudget P e ∅ =
      e.natDegree + P.leadingCoeff.natDegree +
        (Polynomial.derivative P).leadingCoeff.natDegree +
        (Polynomial.resultant P (Polynomial.derivative P)).natDegree +
        (P.coeff 0).natDegree := by
  simp [squarefreeBadDegreeBudget]

/-- A polynomial exceptional locus bounds the non-strong fixed roots by its degree. -/
theorem squarefreeBadDegreeBudget_add_nonStrong_card_lt_of_exceptional_poly
    (c : ℂ) {p : ℕ} (P : Polynomial (Polynomial ℂ)) (e : Polynomial ℂ)
    (B : Finset (Polynomial ℂ)) (H : Polynomial ℂ) (hH0 : H ≠ 0)
    (hstrong : ∀ z ∈ (fixedPointPoly c p).roots.toFinset, H.eval z ≠ 0 →
      (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖)
    (hbound : squarefreeBadDegreeBudget P e B + H.natDegree < 2 ^ p) :
    squarefreeBadDegreeBudget P e B + (nonStrongFixedPointRoots c p).card < 2 ^ p := by
  have hroots_card : H.roots.toFinset.card ≤ H.natDegree := by
    exact le_trans (Multiset.toFinset_card_le _) (card_roots' H)
  refine squarefreeBadDegreeBudget_add_nonStrong_card_lt_of_exceptional
    c P e B H.roots.toFinset ?_ ?_
  · intro z hzroot hzH
    exact hstrong z hzroot (eval_ne_zero_of_notMem_roots hH0 hzH)
  · exact lt_of_le_of_lt
      (Nat.add_le_add_left hroots_card (squarefreeBadDegreeBudget P e B)) hbound

/-- If the strong fixed-root pool is larger than the squarefree bad-locus budget, one strong fixed root
avoids the whole standard bad family. -/
theorem exists_strong_fixedPoint_avoiding_squarefreeBadFamily_of_budget_card (c : ℂ) (p : ℕ)
    (P : Polynomial (Polynomial ℂ)) (e : Polynomial ℂ) (B : Finset (Polynomial ℂ))
    (hA0 : ∀ q ∈ squarefreeBadFamily P e B, q ≠ 0)
    (hcard : squarefreeBadDegreeBudget P e B < (strongFixedPointRoots c p).card) :
    ∃ z₀, z₀ ∈ (fixedPointPoly c p).roots.toFinset ∧
      (∀ q ∈ squarefreeBadFamily P e B, q.eval z₀ ≠ 0) ∧
      (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z₀‖ := by
  obtain ⟨z₀, hzstrong, havoid⟩ :=
    exists_mem_finset_avoiding_polys_of_sum_natDegree_lt
      (strongFixedPointRoots c p) (squarefreeBadFamily P e B) hA0
      (lt_of_le_of_lt (squarefreeBadFamily_sum_natDegree_le_budget P e B) hcard)
  exact ⟨z₀, (mem_strongFixedPointRoots.mp hzstrong).1, havoid,
    (mem_strongFixedPointRoots.mp hzstrong).2⟩

/-- **Absolute connected `φ_c`-transcendence from a squarefree polynomial bad locus.**

This removes pointwise fibre separability from the active finite-count callback.  The finite family
`A` now has to contain the selected denominator, the constant coefficient, and the standard
squarefree-specialization bad polynomials `P.leadingCoeff`, `(derivative P).leadingCoeff`, and
`resultant P (derivative P)`.  Avoiding `A` gives the leading/constant denominator conditions and
fibre separability; the callback only proves strong repulsion at the remaining period-`p` fixed
points. -/
theorem phiMero_transcendental_of_repelling_squarefree_bad_locus_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ p : ℕ, 1 ≤ p ∧ (fixedPointPoly c p).Separable ∧
          ∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
            (Polynomial.C e) * (compRelPoly c p P) = P * S →
            ∃ A : Finset (Polynomial ℂ),
              e ∈ A ∧ P.leadingCoeff ∈ A ∧ (Polynomial.derivative P).leadingCoeff ∈ A ∧
              Polynomial.resultant P (Polynomial.derivative P) ∈ A ∧ P.coeff 0 ∈ A ∧
              (∀ q ∈ A, q ≠ 0) ∧
              (∑ q ∈ A, q.natDegree) < 2 ^ p ∧
              ∀ z₀ ∈ (fixedPointPoly c p).roots.toFinset,
                (∀ q ∈ A, q.eval z₀ ≠ 0) →
                ∃ lam : ℂ,
                  HasDerivAt ((quadratic c)^[p]) lam z₀ ∧
                  (2 ^ p : ℝ) < ‖lam‖) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_polynomial_bad_locus_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, hp, hsep, hpinput⟩ := hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  refine ⟨p, hp, hsep, ?_⟩
  intro e S he0 hPS
  obtain ⟨A, heA, hleadA, hderivLeadA, hresA, hconstA, hA0, hdegA, hrep⟩ :=
    hpinput e S he0 hPS
  refine ⟨A, heA, ?_, hconstA, hA0, hdegA, ?_⟩
  · exact hleadA
  · intro z₀ hzroot havoid
    obtain ⟨lam, hlam, hnorm⟩ := hrep z₀ hzroot havoid
    exact ⟨lam, hlam, hnorm,
      separable_specialization_of_avoids_squarefree_bad_locus P hleadA hderivLeadA hresA havoid⟩

/-- **Absolute connected `φ_c`-transcendence from a squarefree bad locus and orbit-product repulsion.**

This removes the derivative witness from
`phiMero_transcendental_of_repelling_squarefree_bad_locus_input`: the multiplier of `f_c^[p]` at a
period-`p` point is the orbit product `∏ k<p, 2·f_c^[k](z₀)`, with derivative proof supplied by
`hasDerivAt_quadratic_iterate`.  The remaining dynamical callback only proves the strong norm
inequality for that explicit multiplier. -/
theorem phiMero_transcendental_of_repelling_squarefree_bad_locus_orbitNorm_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ p : ℕ, 1 ≤ p ∧ (fixedPointPoly c p).Separable ∧
          ∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
            (Polynomial.C e) * (compRelPoly c p P) = P * S →
            ∃ A : Finset (Polynomial ℂ),
              e ∈ A ∧ P.leadingCoeff ∈ A ∧ (Polynomial.derivative P).leadingCoeff ∈ A ∧
              Polynomial.resultant P (Polynomial.derivative P) ∈ A ∧ P.coeff 0 ∈ A ∧
              (∀ q ∈ A, q ≠ 0) ∧
              (∑ q ∈ A, q.natDegree) < 2 ^ p ∧
              ∀ z₀ ∈ (fixedPointPoly c p).roots.toFinset,
                (∀ q ∈ A, q.eval z₀ ≠ 0) →
                  (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z₀‖) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_squarefree_bad_locus_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, hp, hsep, hpinput⟩ := hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  refine ⟨p, hp, hsep, ?_⟩
  intro e S he0 hPS
  obtain ⟨A, heA, hleadA, hderivLeadA, hresA, hconstA, hA0, hdegA, hnorm⟩ :=
    hpinput e S he0 hPS
  refine ⟨A, heA, hleadA, hderivLeadA, hresA, hconstA, hA0, hdegA, ?_⟩
  intro z₀ hzroot havoid
  exact ⟨∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z₀,
    hasDerivAt_quadratic_iterate c z₀ p, hnorm z₀ hzroot havoid⟩

/-- **Absolute connected `φ_c`-transcendence from the standard squarefree bad locus and orbit norm.**

This is the active finite-count `c₂` interface.  The caller supplies only an extra finite family `B`;
the denominator, leading coefficient, derivative-leading coefficient, resultant, and constant coefficient
are inserted internally by `squarefreeBadFamily`, and their nonvanishing is proved from the selected
denominator plus minimal-relation facts. -/
theorem phiMero_transcendental_of_repelling_standard_squarefree_bad_locus_orbitNorm_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ p : ℕ, 1 ≤ p ∧ (fixedPointPoly c p).Separable ∧
          ∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
            (Polynomial.C e) * (compRelPoly c p P) = P * S →
            ∃ B : Finset (Polynomial ℂ),
              (∀ q ∈ B, q ≠ 0) ∧
              (∑ q ∈ squarefreeBadFamily P e B, q.natDegree) < 2 ^ p ∧
              ∀ z₀ ∈ (fixedPointPoly c p).roots.toFinset,
                (∀ q ∈ squarefreeBadFamily P e B, q.eval z₀ ≠ 0) →
                  (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z₀‖) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_squarefree_bad_locus_orbitNorm_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, hp, hsep, hpinput⟩ := hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  refine ⟨p, hp, hsep, ?_⟩
  intro e S he0 hPS
  obtain ⟨B, hB0, hdegB, hnorm⟩ := hpinput e S he0 hPS
  obtain ⟨hlead, hderivLead, hres, hconst⟩ :=
    minimal_relation_squarefree_bad_polys_ne_zero
      hUo hUc c hU P hP0 hdeg hPrel hPmin hconst_poly
  refine ⟨squarefreeBadFamily P e B,
    mem_squarefreeBadFamily_denominator P e B,
    mem_squarefreeBadFamily_leadingCoeff P e B,
    mem_squarefreeBadFamily_derivative_leadingCoeff P e B,
    mem_squarefreeBadFamily_resultant P e B,
    mem_squarefreeBadFamily_constCoeff P e B,
    squarefreeBadFamily_ne_zero he0 hlead hderivLead hres hconst hB0,
    hdegB,
    ?_⟩
  intro z₀ hzroot havoid
  exact hnorm z₀ hzroot havoid

/-- **Budget form with an explicitly selected avoiding fixed point.**

The finite-count budget is kept in the interface, but the dynamical part only has to produce one
fixed point avoiding the standard bad family and satisfying the orbit-product repulsion bound. -/
theorem phiMero_transcendental_of_repelling_standard_squarefree_budget_target_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ p : ℕ, 1 ≤ p ∧ (fixedPointPoly c p).Separable ∧
          ∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
            (Polynomial.C e) * (compRelPoly c p P) = P * S →
            ∃ B : Finset (Polynomial ℂ),
              (∀ q ∈ B, q ≠ 0) ∧
              squarefreeBadDegreeBudget P e B < 2 ^ p ∧
              ∃ z₀, z₀ ∈ (fixedPointPoly c p).roots.toFinset ∧
                (∀ q ∈ squarefreeBadFamily P e B, q.eval z₀ ≠ 0) ∧
                (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z₀‖) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_selected_denominator_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, hp, _hsep, hpinput⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  refine ⟨p, ?_⟩
  intro e S he0 hPS
  obtain ⟨B, _hB0, _hbudget, z₀, hzroot, havoid, hnorm⟩ := hpinput e S he0 hPS
  have hFz : (quadratic c)^[p] z₀ = z₀ := by
    rw [← fixedPointPoly_isRoot_iff]
    exact (mem_roots (fixedPointPoly_ne_zero c hp)).mp (Multiset.mem_toFinset.mp hzroot)
  refine ⟨∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z₀, z₀,
    hFz, hasDerivAt_quadratic_iterate c z₀ p, hnorm,
    havoid e (mem_squarefreeBadFamily_denominator P e B),
    ?_,
    havoid P.leadingCoeff (mem_squarefreeBadFamily_leadingCoeff P e B),
    havoid (P.coeff 0) (mem_squarefreeBadFamily_constCoeff P e B)⟩
  exact separable_specialization_of_avoids_squarefree_bad_locus P
    (mem_squarefreeBadFamily_leadingCoeff P e B)
    (mem_squarefreeBadFamily_derivative_leadingCoeff P e B)
    (mem_squarefreeBadFamily_resultant P e B)
    havoid

/-- **Budget form from a lower bound on strongly repelling fixed roots.**

This finite-count `c₂` interface asks only that the explicit squarefree bad-locus budget be smaller
than the number of strong period-`p` fixed roots.  The avoiding strong target is selected internally. -/
theorem phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ p : ℕ, 1 ≤ p ∧ (fixedPointPoly c p).Separable ∧
          ∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
            (Polynomial.C e) * (compRelPoly c p P) = P * S →
            ∃ B : Finset (Polynomial ℂ),
              (∀ q ∈ B, q ≠ 0) ∧
              squarefreeBadDegreeBudget P e B < (strongFixedPointRoots c p).card) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_standard_squarefree_budget_target_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, hp, hsep, hpinput⟩ := hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  refine ⟨p, hp, hsep, ?_⟩
  intro e S he0 hPS
  obtain ⟨B, hB0, hcard⟩ := hpinput e S he0 hPS
  obtain ⟨hlead, hderivLead, hres, hconst⟩ :=
    minimal_relation_squarefree_bad_polys_ne_zero
      hUo hUc c hU P hP0 hdeg hPrel hPmin hconst_poly
  have hA0 : ∀ q ∈ squarefreeBadFamily P e B, q ≠ 0 :=
    squarefreeBadFamily_ne_zero he0 hlead hderivLead hres hconst hB0
  have hstrong_card_le : (strongFixedPointRoots c p).card ≤ 2 ^ p := by
    simpa [fixedPointPoly_roots_card c hp hsep] using
      strongFixedPointRoots_card_le_roots c p
  have hbudget : squarefreeBadDegreeBudget P e B < 2 ^ p :=
    lt_of_lt_of_le hcard hstrong_card_le
  obtain ⟨z₀, hzroot, havoid, hnorm⟩ :=
    exists_strong_fixedPoint_avoiding_squarefreeBadFamily_of_budget_card
      c p P e B hA0 hcard
  exact ⟨B, hB0, hbudget, z₀, hzroot, havoid, hnorm⟩

/-- **Budget form from a bound on the non-strong fixed-root exceptional set.**

This is the counting form closest to the remaining dynamics: after the bad polynomials are chosen, it
is enough to prove that their degree budget plus the number of non-strong period-`p` fixed roots is
strictly smaller than the full separable fixed-root count `2^p`. -/
theorem phiMero_transcendental_of_repelling_standard_squarefree_budget_nonStrong_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ p : ℕ, 1 ≤ p ∧ (fixedPointPoly c p).Separable ∧
          ∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
            (Polynomial.C e) * (compRelPoly c p P) = P * S →
            ∃ B : Finset (Polynomial ℂ),
              (∀ q ∈ B, q ≠ 0) ∧
              squarefreeBadDegreeBudget P e B + (nonStrongFixedPointRoots c p).card < 2 ^ p) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, hp, hsep, hpinput⟩ := hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  refine ⟨p, hp, hsep, ?_⟩
  intro e S he0 hPS
  obtain ⟨B, hB0, hbound⟩ := hpinput e S he0 hPS
  exact ⟨B, hB0,
    squarefreeBadDegreeBudget_lt_strongFixedPointRoots_card_of_add_nonStrong_lt
      c hp hsep P e B hbound⟩

/-- **Budget form from a finite exceptional set of non-strong fixed roots.**

The caller supplies an exceptional finite set `E` and proves that every period-`p` fixed root outside
`E` is strong.  The remaining numeric obligation is the concrete bound
`squarefreeBadDegreeBudget P e B + E.card < 2^p`. -/
theorem phiMero_transcendental_of_repelling_standard_squarefree_budget_exceptional_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ p : ℕ, 1 ≤ p ∧ (fixedPointPoly c p).Separable ∧
          ∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
            (Polynomial.C e) * (compRelPoly c p P) = P * S →
            ∃ (B : Finset (Polynomial ℂ)) (E : Finset ℂ),
              (∀ q ∈ B, q ≠ 0) ∧
              (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∉ E →
                (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖) ∧
              squarefreeBadDegreeBudget P e B + E.card < 2 ^ p) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_standard_squarefree_budget_nonStrong_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, hp, hsep, hpinput⟩ := hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  refine ⟨p, hp, hsep, ?_⟩
  intro e S he0 hPS
  obtain ⟨B, E, hB0, hstrong, hbound⟩ := hpinput e S he0 hPS
  exact ⟨B, hB0,
    squarefreeBadDegreeBudget_add_nonStrong_card_lt_of_exceptional c P e B E hstrong hbound⟩

/-- **Budget form from a polynomial exceptional locus for non-strong fixed roots.**

The caller supplies a nonzero polynomial `H`.  Fixed roots outside `H = 0` must be strongly repelling,
and the numeric budget pays only `H.natDegree`. -/
theorem phiMero_transcendental_of_repelling_standard_squarefree_budget_exceptionalPoly_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ p : ℕ, 1 ≤ p ∧ (fixedPointPoly c p).Separable ∧
          ∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
            (Polynomial.C e) * (compRelPoly c p P) = P * S →
            ∃ (B : Finset (Polynomial ℂ)) (H : Polynomial ℂ),
              H ≠ 0 ∧
              (∀ q ∈ B, q ≠ 0) ∧
              (∀ z ∈ (fixedPointPoly c p).roots.toFinset, H.eval z ≠ 0 →
                (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖) ∧
              squarefreeBadDegreeBudget P e B + H.natDegree < 2 ^ p) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_standard_squarefree_budget_exceptional_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, hp, hsep, hpinput⟩ := hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  refine ⟨p, hp, hsep, ?_⟩
  intro e S he0 hPS
  obtain ⟨B, H, hH0, hB0, hstrong, hbound⟩ := hpinput e S he0 hPS
  refine ⟨B, H.roots.toFinset, hB0, ?_, ?_⟩
  · intro z hzroot hzH
    exact hstrong z hzroot (eval_ne_zero_of_notMem_roots hH0 hzH)
  · have hroots_card : H.roots.toFinset.card ≤ H.natDegree := by
      exact le_trans (Multiset.toFinset_card_le _) (card_roots' H)
    exact lt_of_le_of_lt
      (Nat.add_le_add_left hroots_card (squarefreeBadDegreeBudget P e B)) hbound

/-- **Finite-set exceptional input, with the polynomial locus constructed internally.**

This is the creator bridge for the polynomial exceptional-locus interface: a caller may provide a
finite exceptional set `E`; Lean constructs `∏ a ∈ E, (X - C a)`, proves it is nonzero, proves its
degree is `E.card`, and routes the complement condition through nonvanishing of that polynomial. -/
theorem phiMero_transcendental_of_repelling_standard_squarefree_budget_exceptionalSet_asPoly_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ p : ℕ, 1 ≤ p ∧ (fixedPointPoly c p).Separable ∧
          ∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
            (Polynomial.C e) * (compRelPoly c p P) = P * S →
            ∃ (B : Finset (Polynomial ℂ)) (E : Finset ℂ),
              (∀ q ∈ B, q ≠ 0) ∧
              (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∉ E →
                (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖) ∧
              squarefreeBadDegreeBudget P e B + E.card < 2 ^ p) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_standard_squarefree_budget_exceptionalPoly_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, hp, hsep, hpinput⟩ := hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  refine ⟨p, hp, hsep, ?_⟩
  intro e S he0 hPS
  obtain ⟨B, E, hB0, hstrong, hbound⟩ := hpinput e S he0 hPS
  refine ⟨B, exceptionalPoly E, exceptionalPoly_ne_zero E, hB0, ?_, ?_⟩
  · intro z hzroot hHz
    exact hstrong z hzroot (fun hzE => hHz (exceptionalPoly_eval_eq_zero_of_mem hzE))
  · simpa [exceptionalPoly_natDegree E] using hbound

/-- **No-extra-family finite exceptional input.**

This removes the terminal construction of the auxiliary polynomial family `B` from the active `c₂`
interface.  The standard bad family already inserts the selected denominator, leading coefficient,
derivative-leading coefficient, resultant, and constant coefficient; this bridge chooses the extra
family to be empty and routes the remaining finite exceptional set through `exceptionalPoly`. -/
theorem phiMero_transcendental_of_repelling_standard_squarefree_budget_exceptionalSet_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ p : ℕ, 1 ≤ p ∧ (fixedPointPoly c p).Separable ∧
          ∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
            (Polynomial.C e) * (compRelPoly c p P) = P * S →
            ∃ E : Finset ℂ,
              (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∉ E →
                (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖) ∧
              squarefreeBadDegreeBudget P e ∅ + E.card < 2 ^ p) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_standard_squarefree_budget_exceptionalSet_asPoly_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, hp, hsep, hpinput⟩ := hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  refine ⟨p, hp, hsep, ?_⟩
  intro e S he0 hPS
  obtain ⟨E, hstrong, hbound⟩ := hpinput e S he0 hPS
  refine ⟨∅, E, ?_, hstrong, ?_⟩
  · simp
  · simpa using hbound

/-- **No-extra-family non-strong-root count input.**

This removes the terminal construction of the finite exceptional set from the active `c₂` interface:
Lean chooses `nonStrongFixedPointRoots c p` as the exceptional set.  Outside that set, fixed roots are
strong by definition, so the only remaining dynamical count is the no-extra budget plus the number of
non-strong fixed roots. -/
theorem phiMero_transcendental_of_repelling_standard_squarefree_budget_nonStrong_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ p : ℕ, 1 ≤ p ∧ (fixedPointPoly c p).Separable ∧
          ∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
            (Polynomial.C e) * (compRelPoly c p P) = P * S →
              squarefreeBadDegreeBudget P e ∅ + (nonStrongFixedPointRoots c p).card < 2 ^ p) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_standard_squarefree_budget_exceptionalSet_noExtra_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, hp, hsep, hpinput⟩ := hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  refine ⟨p, hp, hsep, ?_⟩
  intro e S he0 hPS
  refine ⟨nonStrongFixedPointRoots c p, ?_, hpinput e S he0 hPS⟩
  intro z hzroot hzNonStrong
  by_contra hnot
  exact hzNonStrong ((mem_nonStrongFixedPointRoots).mpr ⟨hzroot, hnot⟩)

/-- **No-extra non-strong count with one chosen denominator identity.**

This is the finite-count form aligned with the actual denominator-clearing proof.  The period, the
chosen denominator identity, and the non-strong count bound are supplied together.  Lean then chooses a
strong period-`p` fixed root avoiding the standard squarefree bad family and feeds the resulting data to
`phiMero_transcendental_of_repelling_chosen_denominator_input`. -/
theorem phiMero_transcendental_of_repelling_standard_squarefree_budget_nonStrong_chosenDenominator_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ (p : ℕ) (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
          1 ≤ p ∧ (fixedPointPoly c p).Separable ∧
          e ≠ 0 ∧
          (Polynomial.C e) * (compRelPoly c p P) = P * S ∧
          squarefreeBadDegreeBudget P e ∅ + (nonStrongFixedPointRoots c p).card < 2 ^ p) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_chosen_denominator_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, e, S, hp, hsep, he0, hPS, hbound⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨hlead, hderivLead, hres, hconst⟩ :=
    minimal_relation_squarefree_bad_polys_ne_zero
      hUo hUc c hU P hP0 hdeg hPrel hPmin hconst_poly
  have hA0 : ∀ q ∈ squarefreeBadFamily P e ∅, q ≠ 0 :=
    squarefreeBadFamily_ne_zero he0 hlead hderivLead hres hconst (by simp)
  have hcard : squarefreeBadDegreeBudget P e ∅ < (strongFixedPointRoots c p).card :=
    squarefreeBadDegreeBudget_lt_strongFixedPointRoots_card_of_add_nonStrong_lt
      c hp hsep P e ∅ hbound
  obtain ⟨z₀, hzroot, havoid, hnorm⟩ :=
    exists_strong_fixedPoint_avoiding_squarefreeBadFamily_of_budget_card
      c p P e ∅ hA0 hcard
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

/-- **No-extra non-strong count for the internally cleared denominator.**

This is the active finite-count `c₂` shape after denominator clearing has been created in Lean.  For
each period `p`, `chosenCompRelDenom` and `chosenCompRelQuot` provide the identity
`(C e) * compRelPoly c p P = P * S`; the callback only chooses `p`, proves fixed-point separability,
and bounds the standard squarefree budget for that constructed denominator plus the non-strong root
count. -/
theorem phiMero_transcendental_of_repelling_standard_squarefree_budget_nonStrong_clearedDenominator_noExtra_input
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
        ∃ p : ℕ, 1 ≤ p ∧ (fixedPointPoly c p).Separable ∧
          squarefreeBadDegreeBudget P
              (chosenCompRelDenom hUo hUne c hU P hP0 hPrel hPmin p) ∅ +
              (nonStrongFixedPointRoots c p).card < 2 ^ p) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_standard_squarefree_budget_nonStrong_chosenDenominator_noExtra_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, hp, hsep, hbound⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  have hspec := chosenCompRelDenom_spec hUo hUne c hU P hP0 hPrel hPmin p
  exact ⟨p,
    chosenCompRelDenom hUo hUne c hU P hP0 hPrel hPmin p,
    chosenCompRelQuot hUo hUne c hU P hP0 hPrel hPmin p,
    hp, hsep, hspec.1, hspec.2, hbound⟩

/-- **No-extra strong-root count for the internally cleared denominator.**

This is the leanest finite-count `c₂` interface in this file: denominator clearing is constructed by
`chosenCompRelDenom`, the extra bad-family is empty, and the callback only proves that the strong
period-`p` fixed-root pool is larger than the explicit squarefree bad-locus budget.  Unlike the
non-strong-count route, this does not require separability of `fixedPointPoly c p`; a selected strong
root is already an actual root of `fixedPointPoly c p`, and its orbit-product inequality supplies the
repelling multiplier. -/
theorem phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_clearedDenominator_noExtra_input
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
        ∃ p : ℕ,
          squarefreeBadDegreeBudget P
              (chosenCompRelDenom hUo hUne c hU P hP0 hPrel hPmin p) ∅ <
            (strongFixedPointRoots c p).card) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_chosen_denominator_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, hcard_raw⟩ := hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  let e : Polynomial ℂ := chosenCompRelDenom hUo hUne c hU P hP0 hPrel hPmin p
  let S : Polynomial (Polynomial ℂ) := chosenCompRelQuot hUo hUne c hU P hP0 hPrel hPmin p
  have hcard : squarefreeBadDegreeBudget P e ∅ < (strongFixedPointRoots c p).card := by
    simpa [e] using hcard_raw
  have hspec : e ≠ 0 ∧ (Polynomial.C e) * (compRelPoly c p P) = P * S := by
    simpa [e, S] using chosenCompRelDenom_spec hUo hUne c hU P hP0 hPrel hPmin p
  obtain ⟨hlead, hderivLead, hres, hconst⟩ :=
    minimal_relation_squarefree_bad_polys_ne_zero
      hUo hUc c hU P hP0 hdeg hPrel hPmin hconst_poly
  have hA0 : ∀ q ∈ squarefreeBadFamily P e ∅, q ≠ 0 :=
    squarefreeBadFamily_ne_zero hspec.1 hlead hderivLead hres hconst (by simp)
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
    hspec.1, hspec.2, hFz, hasDerivAt_quadratic_iterate c z₀ p, hnorm,
    havoid e (mem_squarefreeBadFamily_denominator P e ∅),
    ?_,
    havoid P.leadingCoeff (mem_squarefreeBadFamily_leadingCoeff P e ∅),
    havoid (P.coeff 0) (mem_squarefreeBadFamily_constCoeff P e ∅)⟩
  exact separable_specialization_of_avoids_squarefree_bad_locus P
    (mem_squarefreeBadFamily_leadingCoeff P e ∅)
    (mem_squarefreeBadFamily_derivative_leadingCoeff P e ∅)
    (mem_squarefreeBadFamily_resultant P e ∅)
    havoid

/-- **Fixed-point finite-set lower bound for the active no-extra `c₂` interface.**

This creates the strong-root-card callback from a concrete finite set of ordinary fixed points whose
multiplier norm is already above `2`.  The caller no longer has to mention `strongFixedPointRoots`: it
exhibits enough fixed points to beat the squarefree budget for the internally chosen denominator, and Lean
promotes that finite set into the period-`p` strong-root pool. -/
theorem phiMero_transcendental_of_repelling_standard_squarefree_budget_fixedNormGtTwo_clearedDenominator_noExtra_input
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
        ∃ (p : ℕ) (E : Finset ℂ),
          1 ≤ p ∧
          (∀ z ∈ E, quadratic c z = z) ∧
          (∀ z ∈ E, (2 : ℝ) < ‖(2 : ℂ) * z‖) ∧
          squarefreeBadDegreeBudget P
              (chosenCompRelDenom hUo hUne c hU P hP0 hPrel hPmin p) ∅ < E.card) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_clearedDenominator_noExtra_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, E, hp, hfix, hgt, hbudget⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  refine ⟨p, ?_⟩
  exact squarefreeBadDegreeBudget_lt_strongFixedPointRoots_card_of_fixedNormGtTwo_finset
    (c := c) hp P (chosenCompRelDenom hUo hUne c hU P hP0 hPrel hPmin p) ∅ E
    hfix hgt hbudget

/-- **Budget form of the standard squarefree bad-locus/orbit-norm interface.**

This replaces the actual sum over `squarefreeBadFamily P e B` by the explicit upper bound
`squarefreeBadDegreeBudget P e B`. -/
theorem phiMero_transcendental_of_repelling_standard_squarefree_budget_orbitNorm_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ p : ℕ, 1 ≤ p ∧ (fixedPointPoly c p).Separable ∧
          ∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
            (Polynomial.C e) * (compRelPoly c p P) = P * S →
            ∃ B : Finset (Polynomial ℂ),
              (∀ q ∈ B, q ≠ 0) ∧
              squarefreeBadDegreeBudget P e B < 2 ^ p ∧
              ∀ z₀ ∈ (fixedPointPoly c p).roots.toFinset,
                (∀ q ∈ squarefreeBadFamily P e B, q.eval z₀ ≠ 0) →
                  (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z₀‖) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
    apply phiMero_transcendental_of_repelling_standard_squarefree_budget_target_input
      hUo hUc hUne hUinf c hU
    intro P hP0 hdeg hPrel hPmin hcount hconst_poly
    obtain ⟨p, hp, hsep, hpinput⟩ := hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
    refine ⟨p, hp, hsep, ?_⟩
    intro e S he0 hPS
    obtain ⟨B, hB0, hbudget, hnorm⟩ := hpinput e S he0 hPS
    obtain ⟨hlead, hderivLead, hres, hconst⟩ :=
      minimal_relation_squarefree_bad_polys_ne_zero
        hUo hUc c hU P hP0 hdeg hPrel hPmin hconst_poly
    have hA0 : ∀ q ∈ squarefreeBadFamily P e B, q ≠ 0 :=
      squarefreeBadFamily_ne_zero he0 hlead hderivLead hres hconst hB0
    obtain ⟨z₀, hzroot, _hFz, havoid⟩ :=
      exists_fixedPointPoly_root_avoiding_squarefreeBadFamily_of_budget
        c hp hsep P e B hA0 hbudget
    exact ⟨B, hB0, hbudget, z₀, hzroot, havoid, hnorm z₀ hzroot havoid⟩

end Bottcher
