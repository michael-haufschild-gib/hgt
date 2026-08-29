import GaloisForLFunctions.HTGeometry.FormalHypertranscendence
import GaloisForLFunctions.HTGeometry.FormalJetPrefixShift

/-!
# Hypertranscendence from an eventual gap condition

The gap criterion for a lacunary series asks for a growth condition tied to the degree data of the
relation being excluded.  A single series cannot satisfy the condition for every relation on its
whole support, because the degree data of a relation is unbounded.  It can satisfy the condition
eventually, and that suffices: for a given relation the offending prefix is a polynomial, and
adding a polynomial is an invertible triangular change of the jet coordinates that raises the
degree data of the relation only linearly in the degree of the prefix, whereas the gaps grow
faster than any linear rate.  Choosing the truncation after the relation is known therefore breaks
the apparent circularity.

* `aeval_survives_of_eventualGap` — the formal statement;
* `hypertranscendental_of_eventualGap` — the analytic capstone.
-/

open MvPolynomial PowerSeries Filter Finset

namespace GaloisForLFunctions.HTGeometry

/-- The prefix polynomial collecting the first `K + 1` terms of a series supported on `b`. -/
noncomputable def gapPrefix (F : ℂ⟦X⟧) (b : ℕ → ℕ) (K : ℕ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range (K + 1), Polynomial.monomial (b i) (PowerSeries.coeff (b i) F)

theorem natDegree_gapPrefix_le {F : ℂ⟦X⟧} {b : ℕ → ℕ} (hmono : Monotone b) (K : ℕ) :
    (gapPrefix F b K).natDegree ≤ b K := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  exact le_trans (Polynomial.natDegree_monomial_le _)
    (hmono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))

theorem coeff_gapPrefix {F : ℂ⟦X⟧} {b : ℕ → ℕ} (hinj : Function.Injective b) (K k : ℕ) :
    (gapPrefix F b K).coeff k
      = if ∃ i ∈ Finset.range (K + 1), b i = k then PowerSeries.coeff k F else 0 := by
  classical
  rw [gapPrefix, Polynomial.finsetSum_coeff]
  by_cases h : ∃ i ∈ Finset.range (K + 1), b i = k
  · obtain ⟨i, hi, hbi⟩ := h
    rw [if_pos ⟨i, hi, hbi⟩,
      Finset.sum_eq_single i (fun j hj hji => ?_) (fun hni => absurd hi hni)]
    · rw [Polynomial.coeff_monomial, if_pos hbi, hbi]
    · rw [Polynomial.coeff_monomial, if_neg (fun hc => hji (hinj (hc.trans hbi.symm)))]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Polynomial.coeff_monomial, if_neg (fun hc => h ⟨j, hj, hc⟩)]

/-- **Eventual-gap formal survival.**  A power series supported on a strictly increasing sequence
whose successive ratios exceed every fixed multiplier from some point on, and with infinitely many
nonzero coefficients, satisfies no nonzero formal algebraic differential relation. -/
theorem aeval_survives_of_eventualGap {n : ℕ} {F : ℂ⟦X⟧} {b : ℕ → ℕ}
    (hstrict : StrictMono b)
    (hgap : ∀ C : ℕ, ∀ᶠ k in atTop, C * b k < b (k + 1))
    (hsupp : ∀ k, PowerSeries.coeff k F ≠ 0 → ∃ i, k = b i)
    (hinf : {i : ℕ | PowerSeries.coeff (b i) F ≠ 0}.Infinite)
    {Q : MvPolynomial (Fin (n + 2)) ℂ} (hQ : Q ≠ 0) :
    aeval (formalJets n F) Q ≠ 0 := by
  classical
  intro hzero
  set r : ℕ := Q.support.sup (fun m => ∑ j : Fin (n + 1), m j.succ) with hr
  set V : ℕ := Q.support.sup (fun m => m 0 + ∑ j : Fin (n + 1), (j : ℕ) * m j.succ) with hV
  have hQbd : JetBd n r V Q := by
    constructor
    · intro m hm; rw [hr]; exact Finset.le_sup (f := fun m => ∑ j : Fin (n + 1), m j.succ) hm
    · intro m hm; rw [hV]
      exact Finset.le_sup (f := fun m => m 0 + ∑ j : Fin (n + 1), (j : ℕ) * m j.succ) hm
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 (hgap (3 * r + 2 * V + 2))
  set K : ℕ := K₀ + 1 with hKdef
  have hKge : K₀ ≤ K := by omega
  have hbKpos : 0 < b K := lt_of_le_of_lt (Nat.zero_le _) (hstrict (by omega : 0 < K))
  have hCk : ∀ k, K ≤ k → (3 * r + 2 * V + 2) * b k < b (k + 1) := fun k hk =>
    hK₀ k (le_trans hKge hk)
  -- the prefix polynomial and the remaining tail
  set p : Polynomial ℂ := gapPrefix F b K with hp
  have hpdeg : p.natDegree ≤ b K := natDegree_gapPrefix_le hstrict.monotone K
  set F' : ℂ⟦X⟧ := F - (p : ℂ⟦X⟧) with hF'
  have hFsplit : F' + (p : ℂ⟦X⟧) = F := by rw [hF']; ring
  set b' : ℕ → ℕ := fun j => b (K + 1 + j) with hb'
  -- the transported relation
  set Q' : MvPolynomial (Fin (n + 2)) ℂ := bind₁ (jetPolynomialAdd n p) Q with hQ'
  have hQ'ne : Q' ≠ 0 := bind₁_jetPolynomialAdd_ne_zero p hQ
  set V' : ℕ := V + b K * r with hV'
  have hQ'bd : JetBd n r V' Q' :=
    (jetBd_bind₁_jetPolynomialAdd hQbd p).mono le_rfl (by
      have : p.natDegree * r ≤ b K * r := Nat.mul_le_mul_right _ hpdeg
      omega)
  -- the tail is supported on the shifted sequence
  have hcoeffF' : ∀ k, PowerSeries.coeff k F'
      = if ∃ i ∈ Finset.range (K + 1), b i = k then 0 else PowerSeries.coeff k F := by
    intro k
    rw [hF', map_sub, Polynomial.coeff_coe, coeff_gapPrefix hstrict.injective]
    by_cases h : ∃ i ∈ Finset.range (K + 1), b i = k
    · rw [if_pos h, if_pos h, sub_self]
    · rw [if_neg h, if_neg h, sub_zero]
  have hsupp' : ∀ k, PowerSeries.coeff k F' ≠ 0 → ∃ j, k = b' j := by
    intro k hk
    rw [hcoeffF'] at hk
    by_cases h : ∃ i ∈ Finset.range (K + 1), b i = k
    · exact absurd (by rw [if_pos h]) hk
    · rw [if_neg h] at hk
      obtain ⟨i, rfl⟩ := hsupp k hk
      have hiK : K < i := by
        by_contra hc
        exact h ⟨i, Finset.mem_range.2 (by omega), rfl⟩
      exact ⟨i - (K + 1), by rw [hb']; congr 1; omega⟩
  have hcoeffb' : ∀ j, PowerSeries.coeff (b' j) F' = PowerSeries.coeff (b' j) F := by
    intro j
    rw [hcoeffF', if_neg]
    rintro ⟨i, hi, hbi⟩
    have := hstrict.injective hbi
    have : i < K + 1 := Finset.mem_range.1 hi
    omega
  have hinf' : {j : ℕ | PowerSeries.coeff (b' j) F' ≠ 0}.Infinite := by
    have hsub : {i : ℕ | PowerSeries.coeff (b i) F ≠ 0}
        ⊆ Set.Iic K ∪ (fun j => K + 1 + j) '' {j : ℕ | PowerSeries.coeff (b' j) F' ≠ 0} := by
      intro i hi
      rcases le_or_gt i K with h | h
      · exact Or.inl h
      · refine Or.inr ⟨i - (K + 1), ?_, by show K + 1 + (i - (K + 1)) = i; omega⟩
        show PowerSeries.coeff (b' (i - (K + 1))) F' ≠ 0
        rw [hcoeffb']
        simpa [hb', show K + 1 + (i - (K + 1)) = i by omega] using hi
    have hu := hinf.mono hsub
    rcases Set.infinite_union.1 hu with h | h
    · exact absurd h (Set.finite_Iic K).not_infinite
    · exact Set.Infinite.of_image _ h
  -- the gap conditions for the shifted sequence
  have hb'mono : Monotone b' := fun i j hij => hstrict.monotone (by omega)
  have hb'0 : 0 < b' 0 := lt_of_le_of_lt (Nat.zero_le _) (hstrict (by omega : 0 < K + 1 + 0))
  have hb'top : Tendsto b' atTop atTop := by
    refine tendsto_atTop_atTop.2 fun c => ?_
    obtain ⟨N, hN⟩ := tendsto_atTop_atTop.1 hstrict.tendsto_atTop c
    exact ⟨N, fun j hj => hN (K + 1 + j) (by omega)⟩
  have hWb : 2 * V' < b' 0 := by
    have h1 := hCk K le_rfl
    have h2 : 2 * V ≤ 2 * V * b K := Nat.le_mul_of_pos_right _ hbKpos
    have h3 : (2 * V + 2 * r) * b K ≤ (3 * r + 2 * V + 2) * b K := by
      exact Nat.mul_le_mul_right _ (by omega)
    have h4 : 2 * V' = 2 * V + 2 * (b K * r) := by rw [hV']; ring
    have h5 : 2 * (b K * r) = 2 * r * b K := by ring
    have h6 : (2 * V + 2 * r) * b K = 2 * V * b K + 2 * r * b K := by ring
    show 2 * V' < b (K + 1 + 0)
    rw [show K + 1 + 0 = K + 1 by omega]
    omega
  have hWgap : ∀ j, r * b' j + 2 * V' < b' (j + 1) := by
    intro j
    have hkge : K ≤ K + 1 + j := by omega
    have h1 := hCk (K + 1 + j) hkge
    have hble : b K ≤ b (K + 1 + j) := hstrict.monotone (by omega)
    have hbpos : 0 < b (K + 1 + j) := lt_of_lt_of_le hbKpos hble
    have h2 : 2 * V ≤ 2 * V * b (K + 1 + j) := Nat.le_mul_of_pos_right _ hbpos
    have h3 : 2 * (b K * r) ≤ 2 * r * b (K + 1 + j) := by
      have : b K * r ≤ b (K + 1 + j) * r := Nat.mul_le_mul_right _ hble
      nlinarith
    have h4 : (r + 2 * V + 2 * r) * b (K + 1 + j) ≤ (3 * r + 2 * V + 2) * b (K + 1 + j) :=
      Nat.mul_le_mul_right _ (by omega)
    have h5 : (r + 2 * V + 2 * r) * b (K + 1 + j)
        = r * b (K + 1 + j) + 2 * V * b (K + 1 + j) + 2 * r * b (K + 1 + j) := by ring
    have h6 : 2 * V' = 2 * V + 2 * (b K * r) := by rw [hV']; ring
    show r * b (K + 1 + j) + 2 * V' < b (K + 1 + (j + 1))
    rw [show K + 1 + (j + 1) = (K + 1 + j) + 1 by omega]
    omega
  -- apply the global-gap survival theorem to the tail
  have hkey := aeval_survives (n := n) (F := F') (bnat := b') (r := r) (W := V')
    hb'mono hb'0 hWb hWgap
    (fun i j hij => by
      have : K + 1 + i = K + 1 + j := hstrict.injective hij
      omega)
    hb'top
    hsupp' hinf' hQ'ne
    (fun m hm => hQ'bd.deg m hm)
    (fun m hm => by have := hQ'bd.wt m hm; omega)
    (fun m hm => by have := hQ'bd.wt m hm; omega)
  apply hkey
  rw [hQ', aeval_formalJets_bind₁_jetPolynomialAdd, hFsplit, hzero]

/-- **Eventual-gap hypertranscendence.**  A smooth function whose Taylor series is supported on a
strictly increasing sequence with eventually superlinear gaps, and which has infinitely many
nonzero coefficients on that sequence, satisfies no algebraic differential equation. -/
theorem hypertranscendental_of_eventualGap {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℕ} (hstrict : StrictMono b)
    (hgap : ∀ C : ℕ, ∀ᶠ k in atTop, C * b k < b (k + 1))
    (hsupp : ∀ k, PowerSeries.coeff k (taylorPS f) ≠ 0 → ∃ i, k = b i)
    (hinf : {i : ℕ | PowerSeries.coeff (b i) (taylorPS f) ≠ 0}.Infinite) :
    Hypertranscendental f :=
  hypertranscendental_of_aeval_survives hf fun _ _ hQ =>
    aeval_survives_of_eventualGap hstrict hgap hsupp hinf hQ

end GaloisForLFunctions.HTGeometry
