import GaloisForLFunctions.HTGeometry.OstrowskiRelationCarrier
import GaloisForLFunctions.HTGeometry.PaddedOrderTuple
import GaloisForLFunctions.HTGeometry.JetRelationPropagation
import GaloisForLFunctions.HTGeometry.DigammaGammaLocalHypertranscendence

/-!
# An exponential carrier with independent frequencies is hypertranscendental

A differential relation is a finite sum of monomials, each one a power of the variable times a
product of jets.  Sorting the monomials by the power of the variable and by the total degree of the
jet part puts the relation in the graded form the frequency argument reads, with the jet part of a
monomial listed as a tuple of orders padded to its degree.

The frequency argument then forces every coefficient to vanish, so a relation satisfied by the
carrier is the zero relation: the carrier satisfies no algebraic differential equation.  Since the
carrier is entire, a relation holding on any nonempty open set already holds on the real line, so the
conclusion is local.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- **A vanishing differential relation of an exponential carrier has vanishing coefficients.**
The monomials are sorted by the power of the variable and by the total degree of the jet part; the
jet part is listed as a padded tuple of orders, which is faithful in each degree. -/
theorem eq_zero_of_jetMonomialCombination_vanishing {a : ι → ℂ} {omega : ι → ℝ}
    (hom : RationallyIndependentSequence omega) (ha : ExpSeriesNormallySummable a omega)
    (hinf : {i : ι | a i ≠ 0}.Infinite) {n : ℕ} {S : Finset (Fin (n + 2) →₀ ℕ)}
    (co : (Fin (n + 2) →₀ ℕ) → ℂ)
    (hzero : ∀ t : ℝ, ∑ m ∈ S, co m * ((t : ℂ) ^ m 0 *
      ∏ j : Fin (n + 1), iteratedDeriv (j : ℕ) (cexpSeriesCarrier a omega) (t : ℂ) ^ m j.succ)
      = 0) :
    ∀ m ∈ S, co m = 0 := by
  classical
  obtain ⟨D, hD⟩ : ∃ D : ℕ, ∀ m ∈ S, m 0 ≤ D :=
    ⟨S.sup fun m => m 0, fun _ hm => Finset.le_sup (f := fun m : Fin (n + 2) →₀ ℕ => m 0) hm⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ m ∈ S, (∑ j : Fin (n + 1), m j.succ) ≤ N :=
    ⟨S.sup fun m => ∑ j : Fin (n + 1), m j.succ,
      fun _ hm => Finset.le_sup (f := fun m : Fin (n + 2) →₀ ℕ => ∑ j : Fin (n + 1), m j.succ) hm⟩
  set L : (Fin (n + 2) →₀ ℕ) → Fin (N + 1) :=
    fun m => ⟨min (∑ j : Fin (n + 1), m j.succ) N, Nat.lt_succ_of_le (min_le_right _ _)⟩ with hLdef
  have hLval : ∀ m ∈ S, ((L m : ℕ)) = ∑ j : Fin (n + 1), m j.succ := by
    intro m hm
    show min (∑ j : Fin (n + 1), m j.succ) N = _
    exact min_eq_left (hN m hm)
  set pad : ∀ M : ℕ, (Fin (n + 2) →₀ ℕ) → (Fin M → ℕ) :=
    fun M m => padOrderTuple (fun j : Fin (n + 1) => m j.succ) M with hpaddef
  set fib : ℕ × Fin (N + 1) → Finset (Fin (n + 2) →₀ ℕ) :=
    fun p => S.filter fun m => (m 0, L m) = p with hfibdef
  set K : ∀ M : Fin (N + 1), Finset (Fin (M : ℕ) → ℕ) :=
    fun M => (S.filter fun m => L m = M).image (pad (M : ℕ)) with hKdef
  set c : ℕ → ∀ M : Fin (N + 1), (Fin (M : ℕ) → ℕ) → ℂ :=
    fun d M s => ∑ m ∈ (fib (d, M)).filter fun m => pad (M : ℕ) m = s, co m with hcdef
  -- the padded tuple of a monomial of the right degree lies in the family of that degree
  have hmaps : ∀ (d : ℕ) (M : Fin (N + 1)), ∀ m ∈ fib (d, M), pad (M : ℕ) m ∈ K M := by
    intro d M m hm
    rw [hfibdef, Finset.mem_filter] at hm
    refine Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hm.1, ?_⟩)
    exact (Prod.ext_iff.1 hm.2).2
  -- padding is faithful in each degree
  have hdistinct : ∀ M : Fin (N + 1), ∀ s ∈ K M, ∀ s' ∈ K M,
      tupleCount s = tupleCount s' → s = s' := by
    intro M s hs s' hs' hcount
    rw [hKdef] at hs hs'
    simp only [Finset.mem_image, Finset.mem_filter] at hs hs'
    obtain ⟨m, ⟨hmS, hmL⟩, rfl⟩ := hs
    obtain ⟨m', ⟨hm'S, hm'L⟩, rfl⟩ := hs'
    have h1 : (∑ j : Fin (n + 1), m j.succ) = (M : ℕ) := by rw [← hLval m hmS, hmL]
    have h2 : (∑ j : Fin (n + 1), m' j.succ) = (M : ℕ) := by rw [← hLval m' hm'S, hm'L]
    exact congrArg (fun mj => padOrderTuple mj (M : ℕ)) (padOrderTuple_injOn h1 h2 hcount)
  have hkey : ∀ d ≤ D, ∀ M : Fin (N + 1), ∀ s ∈ K M, c d M s = 0 := by
    refine eq_zero_of_gradedPolynomialCombination_vanishing hom ha hinf K hdistinct D c ?_
    intro t
    refine Eq.trans ?_ (hzero t)
    -- one degree at a time: the coefficients of a degree repackage its monomials
    have hstep : ∀ (d : ℕ) (M : Fin (N + 1)),
        (∑ s ∈ K M, c d M s * ∏ l, iteratedDeriv (s l) (cexpSeriesCarrier a omega) (t : ℂ))
          = ∑ m ∈ fib (d, M), co m *
            ∏ j : Fin (n + 1),
              iteratedDeriv (j : ℕ) (cexpSeriesCarrier a omega) (t : ℂ) ^ m j.succ := by
      intro d M
      rw [← Finset.sum_fiberwise_of_maps_to (hmaps d M)
        (fun m => co m * ∏ j : Fin (n + 1),
          iteratedDeriv (j : ℕ) (cexpSeriesCarrier a omega) (t : ℂ) ^ m j.succ)]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hcdef]
      simp only
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.mem_filter] at hm
      have hmS : m ∈ S := by
        rw [hfibdef, Finset.mem_filter] at hm
        exact hm.1.1
      have hML : (∑ j : Fin (n + 1), m j.succ) = (M : ℕ) := by
        rw [← hLval m hmS]
        rw [hfibdef, Finset.mem_filter] at hm
        exact congrArg (fun p : ℕ × Fin (N + 1) => ((p.2 : ℕ))) hm.1.2
      rw [← hm.2, hpaddef]
      simp only
      rw [prod_padOrderTuple hML fun k => iteratedDeriv k (cexpSeriesCarrier a omega) (t : ℂ)]
    -- the degrees repackage the whole relation
    have hexpand : ∀ d ∈ Finset.range (D + 1),
        ((t : ℂ) ^ d * ∑ M : Fin (N + 1), ∑ s ∈ K M,
            c d M s * ∏ l, iteratedDeriv (s l) (cexpSeriesCarrier a omega) (t : ℂ))
          = ∑ M : Fin (N + 1), ∑ m ∈ fib (d, M), co m * ((t : ℂ) ^ m 0 *
            ∏ j : Fin (n + 1),
              iteratedDeriv (j : ℕ) (cexpSeriesCarrier a omega) (t : ℂ) ^ m j.succ) := by
      intro d _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun M _ => ?_
      rw [hstep d M, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hd : m 0 = d := by
        rw [hfibdef, Finset.mem_filter] at hm
        exact (Prod.ext_iff.1 hm.2).1
      rw [hd]
      ring
    rw [Finset.sum_congr rfl hexpand, ← Finset.sum_product']
    refine Finset.sum_fiberwise_of_maps_to (t := Finset.range (D + 1) ×ˢ Finset.univ)
      (fun m hm => ?_) _
    exact Finset.mem_product.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (hD m hm)), Finset.mem_univ _⟩
  -- each monomial is alone in its cell
  intro m hm
  have hmem : pad ((L m : ℕ)) m ∈ K (L m) := by
    rw [hKdef]
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hm, rfl⟩)
  have hc0 := hkey (m 0) (hD m hm) (L m) (pad ((L m : ℕ)) m) hmem
  have hsingle : (fib (m 0, L m)).filter (fun m' => pad ((L m : ℕ)) m' = pad ((L m : ℕ)) m)
      = {m} := by
    refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩
    · rw [hfibdef]
      exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hm, rfl⟩, rfl⟩
    · intro m' hm'
      rw [Finset.mem_filter, hfibdef, Finset.mem_filter] at hm'
      obtain ⟨⟨hm'S, hpair⟩, hpadeq⟩ := hm'
      have h0 : m' 0 = m 0 := (Prod.ext_iff.1 hpair).1
      have hL' : L m' = L m := (Prod.ext_iff.1 hpair).2
      have hlen' : (∑ j : Fin (n + 1), m' j.succ) = ((L m : ℕ)) := by
        rw [← hLval m' hm'S, hL']
      have hlen : (∑ j : Fin (n + 1), m j.succ) = ((L m : ℕ)) := (hLval m hm).symm
      have hj : (fun j : Fin (n + 1) => m' j.succ) = fun j : Fin (n + 1) => m j.succ := by
        refine padOrderTuple_injOn hlen' hlen ?_
        rw [hpaddef] at hpadeq
        simp only at hpadeq
        rw [hpadeq]
      refine Finsupp.ext fun v => ?_
      induction v using Fin.cases with
      | zero => exact h0
      | succ j => exact congrFun hj j
  rw [hcdef] at hc0
  simp only at hc0
  rw [hsingle, Finset.sum_singleton] at hc0
  exact hc0

/-- **An exponential carrier with rationally independent frequencies and infinitely many nonzero
amplitudes satisfies no algebraic differential equation on any nonempty open set.** -/
theorem not_differentiallyAlgebraicOn_cexpSeriesCarrier {a : ι → ℂ} {omega : ι → ℝ}
    (hom : RationallyIndependentSequence omega) (ha : ExpSeriesNormallySummable a omega)
    (hinf : {i : ι | a i ≠ 0}.Infinite) {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) :
    ¬ DifferentiallyAlgebraicOn (cexpSeriesCarrier a omega) U := by
  classical
  rintro ⟨n, P, hPne, hrel⟩
  have hall := jetRelation_eq_zero_of_isOpen (analyticAt_cexpSeriesCarrier ha) hU hUne hrel
  have hco : ∀ m ∈ P.support, MvPolynomial.coeff m P = 0 := by
    refine eq_zero_of_jetMonomialCombination_vanishing hom ha hinf _ fun t => ?_
    refine Eq.trans ?_ (hall (t : ℂ))
    rw [MvPolynomial.eval_eq']
    refine Finset.sum_congr rfl fun m _ => ?_
    conv_rhs => rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  refine hPne (MvPolynomial.ext P 0 fun m => ?_)
  by_cases hmem : m ∈ P.support
  · rw [hco m hmem, MvPolynomial.coeff_zero]
  · rw [MvPolynomial.notMem_support_iff.1 hmem, MvPolynomial.coeff_zero]

/-- **A unimodular twist of an exponential carrier satisfies no algebraic differential equation
either.**  Rotating the amplitudes changes neither their sizes nor their support. -/
theorem not_differentiallyAlgebraicOn_cexpSeriesCarrier_twist {a : ι → ℂ} {omega : ι → ℝ}
    {lam : ι → ℂ} (hom : RationallyIndependentSequence omega)
    (ha : ExpSeriesNormallySummable a omega) (hinf : {i : ι | a i ≠ 0}.Infinite)
    (hlam : ∀ i, ‖lam i‖ = 1) {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) :
    ¬ DifferentiallyAlgebraicOn (cexpSeriesCarrier (fun i => a i * lam i) omega) U := by
  have hlamne : ∀ i, lam i ≠ 0 := by
    intro i hi
    have h := hlam i
    rw [hi, norm_zero] at h
    exact zero_ne_one h
  refine not_differentiallyAlgebraicOn_cexpSeriesCarrier hom (fun R => ?_) ?_ hU hUne
  · refine (ha R).congr fun i => ?_
    rw [norm_mul, hlam i, mul_one]
  · have hset : {i : ι | a i * lam i ≠ 0} = {i : ι | a i ≠ 0} := by
      ext i
      simp only [Set.mem_setOf_eq, ne_eq, mul_eq_zero, not_or]
      exact ⟨fun h => h.1, fun h => ⟨h, hlamne i⟩⟩
    rw [hset]
    exact hinf

end

end GaloisForLFunctions.HTGeometry
