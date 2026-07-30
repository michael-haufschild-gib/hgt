import GaloisForLFunctions.RHTower.BakerWeldIndependence

/-!
# Minimal-support relations for the Baker proof

This file packages a hypothetical nontrivial algebraic-coefficient relation among distinct prime
logarithms after deleting its zero coefficients.  The formalized two-prime Gelfond--Schneider
fragment then forces every such reduced relation to have arity at least three.
-/

open scoped Classical

namespace GaloisForLFunctions.RHTower.BakerProof

/-- A nontrivial algebraic-coefficient relation among logarithms of distinct primes, with its support
already reduced so every coefficient is nonzero. -/
structure Relation where
  n : ℕ
  p : Fin n → ℕ
  coeff : Fin n → ℂ
  p_injective : Function.Injective p
  p_prime : ∀ i, (p i).Prime
  coeff_algebraic : ∀ i, IsAlgebraic ℤ (coeff i)
  coeff_ne_zero : ∀ i, coeff i ≠ 0
  vanishes : ∑ i, coeff i * ((Real.log (p i) : ℝ) : ℂ) = 0

/-- Every nontrivial algebraic-coefficient relation on the same prime family has full support.  This
is the global minimal-arity property needed by the terminal zero lemma. -/
def Relation.SupportMinimal (R : Relation) : Prop :=
  ∀ γ : Fin R.n → ℂ,
    (∀ i, IsAlgebraic ℤ (γ i)) →
    (∑ i, γ i * ((Real.log (R.p i) : ℝ) : ℂ)) = 0 →
    (∃ i, γ i ≠ 0) →
    ∀ i, γ i ≠ 0

/-- Any counterexample to the Baker interface restricts to a reduced relation of arity at least
three.  Arity zero and one are elementary; arity two is the unconditional complex
Gelfond--Schneider fragment. -/
theorem exists_reduced_relation_of_counterexample
    (n : ℕ) (p : Fin n → ℕ) (β : Fin n → ℂ)
    (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (hβ : ∀ i, IsAlgebraic ℤ (β i))
    (hrel : ∑ i, β i * ((Real.log (p i) : ℝ) : ℂ) = 0)
    (hnontrivial : ∃ i, β i ≠ 0) :
    ∃ R : Relation, 3 ≤ R.n ∧
      R.n = (Finset.univ.filter fun i => β i ≠ 0).card := by
  let term : Fin n → ℂ := fun i => β i * ((Real.log (p i) : ℝ) : ℂ)
  let s : Finset (Fin n) := Finset.univ.filter fun i => β i ≠ 0
  let e : Fin s.card ≃ s := (s.orderIsoOfFin rfl).toEquiv
  have hsum_s : ∑ i ∈ s, term i = 0 := by
    calc
      ∑ i ∈ s, term i = ∑ i, term i := by
        apply Finset.sum_subset (by simp [s])
        intro i hi hiS
        have hβi : β i = 0 := by
          by_contra hne
          exact hiS (by simp [s, hne])
        simp [term, hβi]
      _ = 0 := hrel
  have hsum_subtype : ∑ i : s, term i = 0 := by
    calc
      ∑ i : s, term i = ∑ i ∈ s, term i := by
        rw [Finset.univ_eq_attach, Finset.sum_attach]
      _ = 0 := hsum_s
  have hsum_fin : ∑ j : Fin s.card, term (e j) = 0 :=
    (e.sum_comp fun i : s => term i).trans hsum_subtype
  let R : Relation :=
    { n := s.card
      p := fun j => p (e j)
      coeff := fun j => β (e j)
      p_injective := by
        intro i j hij
        apply e.injective
        apply Subtype.ext
        exact hp hij
      p_prime := fun j => hprime (e j)
      coeff_algebraic := fun j => hβ (e j)
      coeff_ne_zero := by
        intro j
        exact (Finset.mem_filter.mp (e j).property).2
      vanishes := by
        simpa [term] using hsum_fin }
  refine ⟨R, ?_, rfl⟩
  by_contra hlt
  change ¬3 ≤ s.card at hlt
  have hcard : s.card ≤ 2 := by omega
  have hall := bakerLinearIndependence_of_card_le_two R.n (by simpa [R] using hcard)
    R.p R.coeff R.p_injective R.p_prime R.coeff_algebraic R.vanishes
  obtain ⟨i, hi⟩ := hnontrivial
  have hiS : i ∈ s := by simp [s, hi]
  let j : Fin s.card := e.symm ⟨i, hiS⟩
  exact R.coeff_ne_zero j (hall j)

/-- Any counterexample admits a support-minimal reduced relation of arity at least three. -/
theorem exists_supportMinimal_relation_of_counterexample
    (n : ℕ) (p : Fin n → ℕ) (β : Fin n → ℂ)
    (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (hβ : ∀ i, IsAlgebraic ℤ (β i))
    (hrel : ∑ i, β i * ((Real.log (p i) : ℝ) : ℂ) = 0)
    (hnontrivial : ∃ i, β i ≠ 0) :
    ∃ R : Relation, 3 ≤ R.n ∧ R.SupportMinimal := by
  let P : ℕ → Prop := fun k => ∃ R : Relation, 3 ≤ R.n ∧ R.n = k
  have hP : ∃ k, P k := by
    obtain ⟨R, hn, _⟩ := exists_reduced_relation_of_counterexample
      n p β hp hprime hβ hrel hnontrivial
    exact ⟨R.n, R, hn, rfl⟩
  let k := Nat.find hP
  obtain ⟨R, hn, hRk⟩ := Nat.find_spec hP
  refine ⟨R, hn, ?_⟩
  intro γ hγ hγrel hγnonzero i
  by_contra hi
  obtain ⟨R', hn', hcard'⟩ := exists_reduced_relation_of_counterexample
    R.n R.p γ R.p_injective R.p_prime hγ hγrel hγnonzero
  have hsProper : (Finset.univ.filter fun j => γ j ≠ 0) ≠ Finset.univ := by
    intro hall
    have : i ∈ Finset.univ.filter fun j => γ j ≠ 0 := hall.symm ▸ Finset.mem_univ i
    exact (Finset.mem_filter.mp this).2 hi
  have hsCard : (Finset.univ.filter fun j => γ j ≠ 0).card < R.n := by
    simpa using Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.filter_subset _ _, hsProper⟩)
  have hR'lt : R'.n < k := by
    calc
      R'.n = (Finset.univ.filter fun j => γ j ≠ 0).card := hcard'
      _ < R.n := hsCard
      _ = k := by simpa [k] using hRk
  have hk_le : k ≤ R'.n :=
    Nat.find_min' hP ⟨R', hn', rfl⟩
  omega

/-- In a globally support-minimal counterexample, every coefficient ratio is fixed by complex
conjugation.  Otherwise the difference between the normalized relation and its conjugate would be a
nontrivial algebraic relation whose pivot coefficient is zero. -/
theorem Relation.coeff_div_coeff_conj_eq_of_supportMinimal
    (R : Relation) (hmin : R.SupportMinimal) (pivot i : Fin R.n) :
    starRingEnd ℂ (R.coeff i / R.coeff pivot) = R.coeff i / R.coeff pivot := by
  let logp : Fin R.n → ℂ := fun j => ((Real.log (R.p j) : ℝ) : ℂ)
  let ratio : Fin R.n → ℂ := fun j => R.coeff j / R.coeff pivot
  have hnorm : ∑ j, ratio j * logp j = 0 := by
    calc
      ∑ j, ratio j * logp j =
          (R.coeff pivot)⁻¹ * ∑ j, R.coeff j * logp j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp only [ratio]
        field_simp
      _ = 0 := by
        rw [show (∑ j, R.coeff j * logp j) = 0 from R.vanishes, mul_zero]
  have hconj : ∑ j, starRingEnd ℂ (ratio j) * logp j = 0 := by
    have h := congrArg (starRingEnd ℂ) hnorm
    rw [map_sum] at h
    simp only [map_mul, map_zero] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [show starRingEnd ℂ (logp j) = logp j by
      exact Complex.conj_ofReal (Real.log (R.p j))]
  have hdiff : ∑ j, (ratio j - starRingEnd ℂ (ratio j)) * logp j = 0 := by
    calc
      _ = (∑ j, ratio j * logp j) -
          ∑ j, starRingEnd ℂ (ratio j) * logp j := by
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [hnorm, hconj, sub_zero]
  let γ : Fin R.n → ℂ := fun j => ratio j - starRingEnd ℂ (ratio j)
  have hγalg : ∀ j, IsAlgebraic ℤ (γ j) := by
    intro j
    have hjQ : IsAlgebraic ℚ (ratio j) := by
      have hj : IsAlgebraic ℚ (R.coeff j) :=
        (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp (R.coeff_algebraic j)
      have hp : IsAlgebraic ℚ (R.coeff pivot) :=
        (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp (R.coeff_algebraic pivot)
      simpa [div_eq_mul_inv] using! hj.mul hp.inv
    have hconjQ : IsAlgebraic ℚ (starRingEnd ℂ (ratio j)) := by
      have := hjQ.algHom (Complex.conjAe.restrictScalars ℚ).toAlgHom
      simpa [Complex.conjAe_coe] using this
    exact (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr (hjQ.sub hconjQ)
  by_contra hne
  have hγi : γ i ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm hne)
  have hall := hmin γ hγalg (by simpa [γ, logp] using hdiff) ⟨i, hγi⟩
  have hpivot : γ pivot = 0 := by
    simp [γ, ratio, R.coeff_ne_zero pivot]
  exact (hall pivot) hpivot

end GaloisForLFunctions.RHTower.BakerProof
