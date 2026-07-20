import GaloisForLFunctions.HilbertMetric.TransverseCollisionGraph
import GaloisForLFunctions.HilbertMetric.CoherentCollisionJet

/-!
# Degree-five coherent-collision graph jet

Distinct unisolvent nodes and their exact dual moment coefficients are combined with the explicit
top-degree transverse vectors.  For every pair of top symmetric channels, this module proves the
order-ten value, first-derivative, and second-derivative jets of the recombined coherent Gram entry.

After dividing by the positive monomial weight, the three limiting entries are respectively
`1 + lam²`, `5 + lam²`, and `20`: the literal two-jet at scale one of
`t ^ 5 + lam² * t`.  No interpolation matrix, collision limit, or asymptotic coefficient is
assumed among the hypotheses.
-/

open Filter Asymptotics
open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

abbrev DegreeFiveIndex (d : ℕ) := GradedMultiIndex d 5
abbrev DegreeFiveTopIndex (d : ℕ) := HomogeneousMultiIndex d 5

def degreeFiveTopGradedIndex {d : ℕ} (a : DegreeFiveTopIndex d) : DegreeFiveIndex d :=
  gradedIndex (topDegreeIndex 5) a

def collisionBaseGramEntry {d : ℕ} (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (i j : DegreeFiveIndex d) : ℝ :=
  ∑ l, nodes i l * nodes j l

theorem recombined_innerPower_top_five {d : ℕ}
    (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (a b : DegreeFiveTopIndex d) (n : Fin 6) :
    ∑ i, ∑ j,
      c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
        collisionBaseGramEntry nodes i j ^ (n : ℕ) =
      if a = b ∧ n = topDegreeIndex 5 then
        (Nat.multinomial Finset.univ a.1 : ℝ) else 0 := by
  by_cases hab : a = b
  · subst b
    by_cases hn : n = topDegreeIndex 5
    · subst n
      rw [if_pos ⟨rfl, rfl⟩]
      exact recombined_innerPower_self_degree nodes c hdelta (degreeFiveTopGradedIndex a)
    · rw [if_neg (fun h => hn h.2)]
      exact recombined_innerPower_eq_zero_of_degree_ne nodes c hdelta
        (degreeFiveTopGradedIndex a) (degreeFiveTopGradedIndex a) n (by
          simpa [degreeFiveTopGradedIndex] using (fun h => hn h.symm))
  · rw [if_neg (fun h => hab h.1)]
    apply recombined_innerPower_eq_zero_of_ne nodes c hdelta
    intro h
    apply hab
    exact eq_of_heq (Sigma.ext_iff.mp h).2

theorem recombined_valuePolynomial_top_five {d : ℕ}
    (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (a b : DegreeFiveTopIndex d) (e : ℝ) :
    ∑ i, ∑ j,
      c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
        (∑ n ∈ Finset.range 6,
          e ^ (2 * n) * collisionBaseGramEntry nodes i j ^ n / (n.factorial : ℝ)) =
      e ^ 10 * (if a = b then fockMonomialWeight a else 0) := by
  calc
    ∑ i, ∑ j,
      c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
        (∑ n ∈ Finset.range 6,
          e ^ (2 * n) * collisionBaseGramEntry nodes i j ^ n / (n.factorial : ℝ)) =
      ∑ i, ∑ n ∈ Finset.range 6, ∑ j,
        e ^ (2 * n) / (n.factorial : ℝ) *
          (c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
            collisionBaseGramEntry nodes i j ^ n) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ n ∈ Finset.range 6, e ^ (2 * n) / (n.factorial : ℝ) *
        (∑ i, ∑ j,
          c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
            collisionBaseGramEntry nodes i j ^ n) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = ∑ n ∈ Finset.range 6, e ^ (2 * n) / (n.factorial : ℝ) *
        (if a = b ∧ n = 5 then
          (Nat.multinomial Finset.univ a.1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [recombined_innerPower_top_five nodes c hdelta a b
        ⟨n, Finset.mem_range.mp hn⟩]
      simp [topDegreeIndex, Fin.ext_iff]
    _ = e ^ 10 * (if a = b then fockMonomialWeight a else 0) := by
      by_cases hab : a = b
      · subst b
        rw [if_pos rfl]
        simp only [true_and]
        calc
          (∑ n ∈ Finset.range 6, e ^ (2 * n) / (n.factorial : ℝ) *
            (if n = 5 then (Nat.multinomial Finset.univ a.1 : ℝ) else 0)) =
              e ^ (2 * 5) / (Nat.factorial 5 : ℝ) *
                (if 5 = 5 then (Nat.multinomial Finset.univ a.1 : ℝ) else 0) := by
              apply Finset.sum_eq_single 5
              · intro n hn hn5
                simp [hn5]
              · simp
          _ = _ := by simp [fockMonomialWeight]; ring
      · rw [if_neg hab]
        simp [hab]

theorem recombined_firstPolynomial_top_five {d : ℕ}
    (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (a b : DegreeFiveTopIndex d) (e : ℝ) :
    ∑ i, ∑ j,
      c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
        (∑ k ∈ Finset.range 5,
          e ^ (2 * (k + 1)) * collisionBaseGramEntry nodes i j ^ (k + 1) /
            (k.factorial : ℝ)) =
      e ^ 10 * (if a = b then 5 * fockMonomialWeight a else 0) := by
  calc
    ∑ i, ∑ j,
      c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
        (∑ k ∈ Finset.range 5,
          e ^ (2 * (k + 1)) * collisionBaseGramEntry nodes i j ^ (k + 1) /
            (k.factorial : ℝ)) =
      ∑ i, ∑ k ∈ Finset.range 5, ∑ j,
        e ^ (2 * (k + 1)) / (k.factorial : ℝ) *
          (c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
            collisionBaseGramEntry nodes i j ^ (k + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ k ∈ Finset.range 5, e ^ (2 * (k + 1)) / (k.factorial : ℝ) *
        (∑ i, ∑ j,
          c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
            collisionBaseGramEntry nodes i j ^ (k + 1)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = ∑ k ∈ Finset.range 5, e ^ (2 * (k + 1)) / (k.factorial : ℝ) *
        (if a = b ∧ k = 4 then (Nat.multinomial Finset.univ a.1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [recombined_innerPower_top_five nodes c hdelta a b
        ⟨k + 1, by have hklt := Finset.mem_range.mp hk; omega⟩]
      simp [topDegreeIndex, Fin.ext_iff]
    _ = e ^ 10 * (if a = b then 5 * fockMonomialWeight a else 0) := by
      by_cases hab : a = b
      · subst b
        rw [if_pos rfl]
        simp only [true_and]
        calc
          (∑ k ∈ Finset.range 5, e ^ (2 * (k + 1)) / (k.factorial : ℝ) *
            (if k = 4 then (Nat.multinomial Finset.univ a.1 : ℝ) else 0)) =
              e ^ (2 * (4 + 1)) / (Nat.factorial 4 : ℝ) *
                (if 4 = 4 then (Nat.multinomial Finset.univ a.1 : ℝ) else 0) := by
              apply Finset.sum_eq_single 4
              · intro k hk hk4
                simp [hk4]
              · simp
          _ = _ := by simp [fockMonomialWeight]; ring
      · rw [if_neg hab]
        simp [hab]

theorem recombined_secondPolynomial_top_five {d : ℕ}
    (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (a b : DegreeFiveTopIndex d) (e : ℝ) :
    ∑ i, ∑ j,
      c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
        (∑ k ∈ Finset.range 4,
          e ^ (2 * (k + 2)) * collisionBaseGramEntry nodes i j ^ (k + 2) /
            (k.factorial : ℝ)) =
      e ^ 10 * (if a = b then 20 * fockMonomialWeight a else 0) := by
  calc
    ∑ i, ∑ j,
      c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
        (∑ k ∈ Finset.range 4,
          e ^ (2 * (k + 2)) * collisionBaseGramEntry nodes i j ^ (k + 2) /
            (k.factorial : ℝ)) =
      ∑ i, ∑ k ∈ Finset.range 4, ∑ j,
        e ^ (2 * (k + 2)) / (k.factorial : ℝ) *
          (c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
            collisionBaseGramEntry nodes i j ^ (k + 2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ k ∈ Finset.range 4, e ^ (2 * (k + 2)) / (k.factorial : ℝ) *
        (∑ i, ∑ j,
          c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
            collisionBaseGramEntry nodes i j ^ (k + 2)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = ∑ k ∈ Finset.range 4, e ^ (2 * (k + 2)) / (k.factorial : ℝ) *
        (if a = b ∧ k = 3 then (Nat.multinomial Finset.univ a.1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [recombined_innerPower_top_five nodes c hdelta a b
        ⟨k + 2, by have hklt := Finset.mem_range.mp hk; omega⟩]
      simp [topDegreeIndex, Fin.ext_iff]
    _ = e ^ 10 * (if a = b then 20 * fockMonomialWeight a else 0) := by
      by_cases hab : a = b
      · subst b
        rw [if_pos rfl]
        simp only [true_and]
        calc
          (∑ k ∈ Finset.range 4, e ^ (2 * (k + 2)) / (k.factorial : ℝ) *
            (if k = 3 then (Nat.multinomial Finset.univ a.1 : ℝ) else 0)) =
              e ^ (2 * (3 + 2)) / (Nat.factorial 3 : ℝ) *
                (if 3 = 3 then (Nat.multinomial Finset.univ a.1 : ℝ) else 0) := by
              apply Finset.sum_eq_single 3
              · intro k hk hk3
                simp [hk3]
              · simp
          _ = _ := by simp [fockMonomialWeight]; ring
      · rw [if_neg hab]
        simp [hab]

theorem degreeFiveTop_valueJet {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (a b : DegreeFiveTopIndex d) :
    (fun e =>
      (∑ i, ∑ j,
        c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
          Real.exp (coherentCollisionExponent (collisionBaseGramEntry nodes i j)
            (transverseCollisionGramEntry lam nodes i j) e)) -
        e ^ 10 *
          (if a = b then fockMonomialWeight a * (1 + lam ^ 2) else 0))
      =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  have hjet := coherentCollision_valueJet_finset
    (Finset.univ : Finset (DegreeFiveIndex d × DegreeFiveIndex d))
    (fun p => c (degreeFiveTopGradedIndex a) p.1 *
      c (degreeFiveTopGradedIndex b) p.2)
    (fun p => collisionBaseGramEntry nodes p.1 p.2)
    (fun p => transverseCollisionGramEntry lam nodes p.1 p.2)
  simp only [Fintype.sum_prod_type] at hjet
  have htransScaled (e : ℝ) :
      ∑ i, ∑ j,
        c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
          (e ^ 10 * transverseCollisionGramEntry lam nodes i j) =
        e ^ 10 * (if a = b then lam ^ 2 * fockMonomialWeight a else 0) := by
    calc
      _ = e ^ 10 *
          (∑ i, ∑ j,
            c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
              transverseCollisionGramEntry lam nodes i j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        congr 1
        simpa [degreeFiveTopGradedIndex] using
          recombined_transverseCollisionGramEntry_top lam nodes c hdelta a b
  convert hjet using 1
  funext e
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [recombined_valuePolynomial_top_five nodes c hdelta a b e,
    htransScaled e]
  by_cases hab : a = b
  · simp [hab]
    ring
  · simp [hab]

theorem degreeFiveTop_firstJet {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (a b : DegreeFiveTopIndex d) :
    (fun e =>
      (∑ i, ∑ j,
        c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
          (coherentCollisionExponent (collisionBaseGramEntry nodes i j)
              (transverseCollisionGramEntry lam nodes i j) e *
            Real.exp (coherentCollisionExponent (collisionBaseGramEntry nodes i j)
              (transverseCollisionGramEntry lam nodes i j) e))) -
        e ^ 10 *
          (if a = b then fockMonomialWeight a * (5 + lam ^ 2) else 0))
      =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  have hjet := coherentCollision_firstJet_finset
    (Finset.univ : Finset (DegreeFiveIndex d × DegreeFiveIndex d))
    (fun p => c (degreeFiveTopGradedIndex a) p.1 *
      c (degreeFiveTopGradedIndex b) p.2)
    (fun p => collisionBaseGramEntry nodes p.1 p.2)
    (fun p => transverseCollisionGramEntry lam nodes p.1 p.2)
  simp only [Fintype.sum_prod_type] at hjet
  have htransScaled (e : ℝ) :
      ∑ i, ∑ j,
        c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
          (e ^ 10 * transverseCollisionGramEntry lam nodes i j) =
        e ^ 10 * (if a = b then lam ^ 2 * fockMonomialWeight a else 0) := by
    calc
      _ = e ^ 10 *
          (∑ i, ∑ j,
            c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
              transverseCollisionGramEntry lam nodes i j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        congr 1
        simpa [degreeFiveTopGradedIndex] using
          recombined_transverseCollisionGramEntry_top lam nodes c hdelta a b
  convert hjet using 1
  funext e
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [recombined_firstPolynomial_top_five nodes c hdelta a b e, htransScaled e]
  by_cases hab : a = b
  · simp [hab]
    ring
  · simp [hab]

theorem degreeFiveTop_secondJet {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (a b : DegreeFiveTopIndex d) :
    (fun e =>
      (∑ i, ∑ j,
        c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
          (coherentCollisionExponent (collisionBaseGramEntry nodes i j)
              (transverseCollisionGramEntry lam nodes i j) e ^ 2 *
            Real.exp (coherentCollisionExponent (collisionBaseGramEntry nodes i j)
              (transverseCollisionGramEntry lam nodes i j) e))) -
        e ^ 10 * (if a = b then 20 * fockMonomialWeight a else 0))
      =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  have hjet := coherentCollision_secondJet_finset
    (Finset.univ : Finset (DegreeFiveIndex d × DegreeFiveIndex d))
    (fun p => c (degreeFiveTopGradedIndex a) p.1 *
      c (degreeFiveTopGradedIndex b) p.2)
    (fun p => collisionBaseGramEntry nodes p.1 p.2)
    (fun p => transverseCollisionGramEntry lam nodes p.1 p.2)
  simp only [Fintype.sum_prod_type] at hjet
  convert hjet using 1
  funext e
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [recombined_secondPolynomial_top_five nodes c hdelta a b e]

def degreeFiveCollisionPoint {d : ℕ} (lam : ℝ)
    (nodes : DegreeFiveIndex d → (Fin d → ℝ)) (e : ℝ) (i : DegreeFiveIndex d) :
    Fin d ⊕ DegreeFiveTopIndex d → ℝ
  | Sum.inl l => e * nodes i l
  | Sum.inr a => e ^ 5 * transverseCollisionVector lam nodes i a

theorem degreeFiveCollisionPoint_inner {d : ℕ} (lam : ℝ)
    (nodes : DegreeFiveIndex d → (Fin d → ℝ)) (e : ℝ) (i j : DegreeFiveIndex d) :
    ∑ x, degreeFiveCollisionPoint lam nodes e i x * degreeFiveCollisionPoint lam nodes e j x =
      coherentCollisionExponent (collisionBaseGramEntry nodes i j)
        (transverseCollisionGramEntry lam nodes i j) e := by
  simp only [Fintype.sum_sum_type, degreeFiveCollisionPoint]
  unfold coherentCollisionExponent collisionBaseGramEntry transverseCollisionGramEntry
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring

theorem degreeFiveCollisionPoint_injective {d : ℕ} (lam : ℝ)
    (nodes : DegreeFiveIndex d → (Fin d → ℝ)) (hnodes : Function.Injective nodes)
    {e : ℝ} (he : e ≠ 0) : Function.Injective (degreeFiveCollisionPoint lam nodes e) := by
  intro i j h
  apply hnodes
  funext l
  have hl := congrFun h (Sum.inl l)
  simp only [degreeFiveCollisionPoint] at hl
  exact mul_left_cancel₀ he hl

def gaussianCollisionGramEntry {d : ℕ} (lam : ℝ)
    (nodes : DegreeFiveIndex d → (Fin d → ℝ)) (e : ℝ)
    (i j : DegreeFiveIndex d) : ℝ :=
  Real.exp (∑ x,
    degreeFiveCollisionPoint lam nodes e i x * degreeFiveCollisionPoint lam nodes e j x)

def gaussianCollisionGramFirstEntry {d : ℕ} (lam : ℝ)
    (nodes : DegreeFiveIndex d → (Fin d → ℝ)) (e : ℝ)
    (i j : DegreeFiveIndex d) : ℝ :=
  (∑ x, degreeFiveCollisionPoint lam nodes e i x * degreeFiveCollisionPoint lam nodes e j x) *
    gaussianCollisionGramEntry lam nodes e i j

def gaussianCollisionGramSecondEntry {d : ℕ} (lam : ℝ)
    (nodes : DegreeFiveIndex d → (Fin d → ℝ)) (e : ℝ)
    (i j : DegreeFiveIndex d) : ℝ :=
  (∑ x, degreeFiveCollisionPoint lam nodes e i x * degreeFiveCollisionPoint lam nodes e j x) ^ 2 *
    gaussianCollisionGramEntry lam nodes e i j

theorem degreeFiveTop_gaussianValueJet {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (a b : DegreeFiveTopIndex d) :
    (fun e =>
      (∑ i, ∑ j, c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
        gaussianCollisionGramEntry lam nodes e i j) -
      e ^ 10 * (if a = b then fockMonomialWeight a * (1 + lam ^ 2) else 0))
      =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  unfold gaussianCollisionGramEntry
  simp_rw [degreeFiveCollisionPoint_inner]
  exact degreeFiveTop_valueJet lam nodes c hdelta a b

theorem degreeFiveTop_gaussianFirstJet {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (a b : DegreeFiveTopIndex d) :
    (fun e =>
      (∑ i, ∑ j, c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
        gaussianCollisionGramFirstEntry lam nodes e i j) -
      e ^ 10 * (if a = b then fockMonomialWeight a * (5 + lam ^ 2) else 0))
      =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  unfold gaussianCollisionGramFirstEntry gaussianCollisionGramEntry
  simp_rw [degreeFiveCollisionPoint_inner]
  exact degreeFiveTop_firstJet lam nodes c hdelta a b

theorem degreeFiveTop_gaussianSecondJet {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (a b : DegreeFiveTopIndex d) :
    (fun e =>
      (∑ i, ∑ j, c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
        gaussianCollisionGramSecondEntry lam nodes e i j) -
      e ^ 10 * (if a = b then 20 * fockMonomialWeight a else 0))
      =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  unfold gaussianCollisionGramSecondEntry gaussianCollisionGramEntry
  simp_rw [degreeFiveCollisionPoint_inner]
  exact degreeFiveTop_secondJet lam nodes c hdelta a b

theorem exists_distinct_degreeFiveGaussianGraphJets (d : ℕ) (lam : ℝ) :
    ∃ (nodes : DegreeFiveIndex d → (Fin d → ℝ))
      (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ),
      Function.Injective nodes ∧
      (∀ e, e ≠ 0 → Function.Injective (degreeFiveCollisionPoint lam nodes e)) ∧
      (∀ a b : DegreeFiveTopIndex d,
        (fun e =>
          (∑ i, ∑ j, c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
            gaussianCollisionGramEntry lam nodes e i j) -
          e ^ 10 * (if a = b then fockMonomialWeight a * (1 + lam ^ 2) else 0))
          =o[nhds 0] (fun e : ℝ => e ^ 10)) ∧
      (∀ a b : DegreeFiveTopIndex d,
        (fun e =>
          (∑ i, ∑ j, c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
            gaussianCollisionGramFirstEntry lam nodes e i j) -
          e ^ 10 * (if a = b then fockMonomialWeight a * (5 + lam ^ 2) else 0))
          =o[nhds 0] (fun e : ℝ => e ^ 10)) ∧
      (∀ a b : DegreeFiveTopIndex d,
        (fun e =>
          (∑ i, ∑ j, c (degreeFiveTopGradedIndex a) i * c (degreeFiveTopGradedIndex b) j *
            gaussianCollisionGramSecondEntry lam nodes e i j) -
          e ^ 10 * (if a = b then 20 * fockMonomialWeight a else 0))
          =o[nhds 0] (fun e : ℝ => e ^ 10)) := by
  obtain ⟨nodes, c, hnodes, hdelta⟩ := exists_gradedMonomial_unisolvent_delta d 5
  refine ⟨nodes, c, hnodes, ?_, ?_, ?_, ?_⟩
  · intro e he
    exact degreeFiveCollisionPoint_injective lam nodes hnodes he
  · intro a b
    exact degreeFiveTop_gaussianValueJet lam nodes c hdelta a b
  · intro a b
    exact degreeFiveTop_gaussianFirstJet lam nodes c hdelta a b
  · intro a b
    exact degreeFiveTop_gaussianSecondJet lam nodes c hdelta a b

end
end GaloisForLFunctions.HilbertMetric
