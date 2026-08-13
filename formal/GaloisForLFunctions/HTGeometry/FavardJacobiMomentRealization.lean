import GaloisForLFunctions.HTGeometry.AdaptiveOrthogonalSourceJacobiEnergy

/-!
# Favard realization of prescribed Jacobi data

Given a diagonal sequence `α` and a lower sequence `β` that is strictly positive from index one
on, the monic three-term recurrence polynomials

`P₀ = 1, P₁ = X - α₀, Pₙ₊₂ = (X - αₙ₊₁) Pₙ₊₁ - βₙ₊₁ Pₙ`

admit a moment sequence whose functional annihilates every positive-degree member.  The induced
moment form is positive definite, its Gram--Schmidt family is exactly the recurrence family, and
its monic Jacobi coordinates are the prescribed data.  This is the constructive, measure-free
direction of Favard's theorem: every strictly positive Jacobi shape is realized by a positive
Hamburger moment geometry, with `Xᵏ`-against-`Pₖ` pairing equal to `β₁ ⋯ βₖ`.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

noncomputable section

/-- Monic three-term recurrence polynomials attached to prescribed Jacobi data. -/
def favardPoly (α β : ℕ → ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.X - Polynomial.C (α 0)
  | n + 2 => (Polynomial.X - Polynomial.C (α (n + 1))) * favardPoly α β (n + 1) -
      Polynomial.C (β (n + 1)) * favardPoly α β n

@[simp] theorem favardPoly_zero (α β : ℕ → ℝ) : favardPoly α β 0 = 1 := rfl

@[simp] theorem favardPoly_one (α β : ℕ → ℝ) :
    favardPoly α β 1 = Polynomial.X - Polynomial.C (α 0) := rfl

theorem favardPoly_succ_succ (α β : ℕ → ℝ) (n : ℕ) :
    favardPoly α β (n + 2) =
      (Polynomial.X - Polynomial.C (α (n + 1))) * favardPoly α β (n + 1) -
        Polynomial.C (β (n + 1)) * favardPoly α β n := rfl

/-- Monicity and exact degree of the recurrence family. -/
theorem favardPoly_monic_degree (α β : ℕ → ℝ) :
    ∀ n : ℕ, (favardPoly α β n).Monic ∧ (favardPoly α β n).degree = (n : WithBot ℕ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact ⟨monic_one, by simp⟩
    | 1 => exact ⟨monic_X_sub_C (α 0), degree_X_sub_C (α 0)⟩
    | n + 2 =>
      obtain ⟨hm1, hd1⟩ := ih (n + 1) (by omega)
      obtain ⟨hm0, hd0⟩ := ih n (by omega)
      have hmA : ((Polynomial.X - Polynomial.C (α (n + 1))) * favardPoly α β (n + 1)).Monic :=
        (monic_X_sub_C (α (n + 1))).mul hm1
      have hdA : ((Polynomial.X - Polynomial.C (α (n + 1))) * favardPoly α β (n + 1)).degree =
          ((n + 2 : ℕ) : WithBot ℕ) := by
        rw [degree_mul, degree_X_sub_C, hd1]
        exact_mod_cast (by omega : (1 + (n + 1) : ℕ) = n + 2)
      have hdB : (Polynomial.C (β (n + 1)) * favardPoly α β n).degree <
          ((n + 2 : ℕ) : WithBot ℕ) := by
        refine lt_of_le_of_lt (degree_mul_le _ _) ?_
        refine lt_of_le_of_lt (add_le_add degree_C_le le_rfl) ?_
        rw [zero_add, hd0]
        exact_mod_cast Nat.lt_succ_of_lt (Nat.lt_succ_self n)
      constructor
      · rw [favardPoly_succ_succ, sub_eq_add_neg]
        exact hmA.add_of_left (by rwa [degree_neg, hdA])
      · rw [favardPoly_succ_succ, sub_eq_add_neg,
          degree_add_eq_left_of_degree_lt (by rwa [degree_neg, hdA]), hdA]

theorem favardPoly_monic (α β : ℕ → ℝ) (n : ℕ) : (favardPoly α β n).Monic :=
  (favardPoly_monic_degree α β n).1

theorem favardPoly_degree (α β : ℕ → ℝ) (n : ℕ) :
    (favardPoly α β n).degree = (n : WithBot ℕ) :=
  (favardPoly_monic_degree α β n).2

theorem favardPoly_natDegree (α β : ℕ → ℝ) (n : ℕ) :
    (favardPoly α β n).natDegree = n := by
  have hd := favardPoly_degree α β n
  rw [Polynomial.degree_eq_natDegree (favardPoly_monic α β n).ne_zero] at hd
  exact_mod_cast hd

theorem favardPoly_ne_zero (α β : ℕ → ℝ) (n : ℕ) : favardPoly α β n ≠ 0 :=
  (favardPoly_monic α β n).ne_zero

/-- Uniform three-term shift: multiplying by the coordinate moves one recurrence step up. -/
theorem X_mul_favardPoly (α β : ℕ → ℝ) (n : ℕ) :
    Polynomial.X * favardPoly α β (n + 1) =
      favardPoly α β (n + 2) + Polynomial.C (α (n + 1)) * favardPoly α β (n + 1) +
        Polynomial.C (β (n + 1)) * favardPoly α β n := by
  rw [favardPoly_succ_succ]
  ring

theorem X_mul_favardPoly_zero (α β : ℕ → ℝ) :
    Polynomial.X * favardPoly α β 0 =
      favardPoly α β 1 + Polynomial.C (α 0) * favardPoly α β 0 := by
  simp only [favardPoly_zero, favardPoly_one, mul_one]
  ring

/-- The Favard moment sequence: the unique normalization annihilating every positive-degree
recurrence polynomial. -/
def favardMoment (α β : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 1
  else -∑ i : Fin n, (favardPoly α β n).coeff i.1 * favardMoment α β i.1
termination_by n
decreasing_by exact i.isLt

theorem favardMoment_eq (α β : ℕ → ℝ) (n : ℕ) :
    favardMoment α β n =
      if n = 0 then 1
      else -∑ i : Fin n, (favardPoly α β n).coeff i.1 * favardMoment α β i.1 := by
  rw [favardMoment]

@[simp] theorem favardMoment_zero (α β : ℕ → ℝ) : favardMoment α β 0 = 1 := by
  rw [favardMoment_eq]
  simp

theorem favardMoment_succ (α β : ℕ → ℝ) (n : ℕ) :
    favardMoment α β (n + 1) =
      -∑ i ∈ Finset.range (n + 1),
        (favardPoly α β (n + 1)).coeff i * favardMoment α β i := by
  rw [favardMoment_eq]
  simp only [Nat.succ_ne_zero, if_false]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (favardPoly α β (n + 1)).coeff i * favardMoment α β i)]

/-- Scalars pass through the moment functional. -/
theorem momentFunctional_C_mul (s : ℕ → ℝ) (c : ℝ) (p : Polynomial ℝ) :
    momentFunctional s (Polynomial.C c * p) = c * momentFunctional s p := by
  rw [← Polynomial.smul_eq_C_mul, momentFunctional_smul]

/-- Constants evaluate to multiples of the zeroth moment. -/
theorem momentFunctional_C (s : ℕ → ℝ) (c : ℝ) :
    momentFunctional s (Polynomial.C c) = c * s 0 := by
  rw [← Polynomial.monomial_zero_left, momentFunctional_monomial]

/-- The functional of the constant one is the zeroth moment. -/
theorem momentFunctional_one (s : ℕ → ℝ) : momentFunctional s 1 = s 0 := by
  rw [← Polynomial.C_1, momentFunctional_C, one_mul]

/-- The Favard functional annihilates every positive-degree recurrence polynomial. -/
theorem momentFunctional_favardPoly (α β : ℕ → ℝ) (n : ℕ) :
    momentFunctional (favardMoment α β) (favardPoly α β (n + 1)) = 0 := by
  set s := favardMoment α β with hs
  set p := favardPoly α β (n + 1) with hp
  have hdeg : p.natDegree = n + 1 := favardPoly_natDegree α β (n + 1)
  have hsum : momentFunctional s p =
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * s i := by
    rw [momentFunctional_eq_support_sum]
    exact Finset.sum_subset p.supp_subset_range_natDegree_succ
      (fun i _ hi => by rw [Polynomial.notMem_support_iff.mp hi, zero_mul])
  rw [hsum, hdeg, Finset.sum_range_succ]
  have hlead : p.coeff (n + 1) = 1 := by
    have hcn := (favardPoly_monic α β (n + 1)).coeff_natDegree
    rwa [hdeg] at hcn
  rw [hlead, one_mul, hs, favardMoment_succ]
  simp [hp]

/-- Orthogonality against every strictly lower monomial. -/
theorem momentFunctional_X_pow_mul_favardPoly (α β : ℕ → ℝ) :
    ∀ m k : ℕ, m < k →
      momentFunctional (favardMoment α β) (Polynomial.X ^ m * favardPoly α β k) = 0 := by
  intro m
  induction m with
  | zero =>
      intro k hk
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [pow_zero, one_mul]
      exact momentFunctional_favardPoly α β j
  | succ m ih =>
      intro k hk
      obtain ⟨i, rfl⟩ : ∃ i, k = i + 2 := ⟨k - 2, by omega⟩
      have hsplit : Polynomial.X ^ (m + 1) * favardPoly α β (i + 2) =
          Polynomial.X ^ m * favardPoly α β (i + 3) +
            Polynomial.C (α (i + 2)) * (Polynomial.X ^ m * favardPoly α β (i + 2)) +
            Polynomial.C (β (i + 2)) * (Polynomial.X ^ m * favardPoly α β (i + 1)) := by
        calc Polynomial.X ^ (m + 1) * favardPoly α β (i + 2) =
            Polynomial.X ^ m * (Polynomial.X * favardPoly α β (i + 2)) := by ring
          _ = Polynomial.X ^ m * (favardPoly α β (i + 3) +
              Polynomial.C (α (i + 2)) * favardPoly α β (i + 2) +
              Polynomial.C (β (i + 2)) * favardPoly α β (i + 1)) := by
                rw [X_mul_favardPoly α β (i + 1)]
          _ = _ := by ring
      rw [hsplit, momentFunctional_add, momentFunctional_add,
        momentFunctional_C_mul, momentFunctional_C_mul,
        ih (i + 3) (by omega), ih (i + 2) (by omega), ih (i + 1) (by omega)]
      ring

/-- Exact diagonal pairing: `L(Xᵏ Pₖ) = β₁ ⋯ βₖ`. -/
theorem momentFunctional_X_pow_mul_favardPoly_self (α β : ℕ → ℝ) :
    ∀ k : ℕ, momentFunctional (favardMoment α β) (Polynomial.X ^ k * favardPoly α β k) =
      ∏ j ∈ Finset.range k, β (j + 1) := by
  intro k
  induction k with
  | zero =>
      rw [pow_zero, favardPoly_zero, one_mul, momentFunctional_one, favardMoment_zero]
      simp
  | succ k ih =>
      have hsplit : Polynomial.X ^ (k + 1) * favardPoly α β (k + 1) =
          Polynomial.X ^ k * favardPoly α β (k + 2) +
            Polynomial.C (α (k + 1)) * (Polynomial.X ^ k * favardPoly α β (k + 1)) +
            Polynomial.C (β (k + 1)) * (Polynomial.X ^ k * favardPoly α β k) := by
        calc Polynomial.X ^ (k + 1) * favardPoly α β (k + 1) =
            Polynomial.X ^ k * (Polynomial.X * favardPoly α β (k + 1)) := by ring
          _ = Polynomial.X ^ k * (favardPoly α β (k + 2) +
              Polynomial.C (α (k + 1)) * favardPoly α β (k + 1) +
              Polynomial.C (β (k + 1)) * favardPoly α β k) := by
                rw [X_mul_favardPoly α β k]
          _ = _ := by ring
      rw [hsplit, momentFunctional_add, momentFunctional_add,
        momentFunctional_C_mul, momentFunctional_C_mul,
        momentFunctional_X_pow_mul_favardPoly α β k (k + 2) (by omega),
        momentFunctional_X_pow_mul_favardPoly α β k (k + 1) (by omega),
        ih, Finset.prod_range_succ]
      ring

/-- Orthogonality against every polynomial of strictly lower degree. -/
theorem momentFunctional_mul_favardPoly_eq_zero (α β : ℕ → ℝ) {q : Polynomial ℝ} {k : ℕ}
    (hq : q.degree < (k : WithBot ℕ)) :
    momentFunctional (favardMoment α β) (q * favardPoly α β k) = 0 := by
  have hexp : q * favardPoly α β k =
      ∑ i ∈ q.support, Polynomial.monomial i (q.coeff i) * favardPoly α β k := by
    rw [← Finset.sum_mul, ← Polynomial.as_sum_support]
  rw [hexp, momentFunctional_finset_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hik : i < k := by
    have hle : (i : WithBot ℕ) ≤ q.degree :=
      Polynomial.le_degree_of_ne_zero (Polynomial.mem_support_iff.mp hi)
    have hlt := lt_of_le_of_lt hle hq
    exact_mod_cast hlt
  rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc, momentFunctional_C_mul,
    momentFunctional_X_pow_mul_favardPoly α β i k hik, mul_zero]

/-- Exact diagonal norm: `L(Pₖ Pₖ) = β₁ ⋯ βₖ`. -/
theorem momentFunctional_favardPoly_mul_self (α β : ℕ → ℝ) (k : ℕ) :
    momentFunctional (favardMoment α β) (favardPoly α β k * favardPoly α β k) =
      ∏ j ∈ Finset.range k, β (j + 1) := by
  have hdecomp : favardPoly α β k * favardPoly α β k =
      (favardPoly α β k - Polynomial.X ^ k) * favardPoly α β k +
        Polynomial.X ^ k * favardPoly α β k := by ring
  have hdeg : (favardPoly α β k - Polynomial.X ^ k).degree < (k : WithBot ℕ) := by
    have hd : (favardPoly α β k).degree = (Polynomial.X ^ k : Polynomial ℝ).degree := by
      rw [favardPoly_degree α β k, Polynomial.degree_X_pow]
    have hlc : (favardPoly α β k).leadingCoeff =
        (Polynomial.X ^ k : Polynomial ℝ).leadingCoeff := by
      rw [(favardPoly_monic α β k).leadingCoeff,
        ((Polynomial.monic_X_pow (n := k) (R := ℝ))).leadingCoeff]
    have hlt := Polynomial.degree_sub_lt hd (favardPoly_ne_zero α β k) hlc
    rwa [favardPoly_degree α β k] at hlt
  rw [hdecomp, momentFunctional_add,
    momentFunctional_mul_favardPoly_eq_zero α β hdeg,
    momentFunctional_X_pow_mul_favardPoly_self α β k, zero_add]

/-- Square positivity of the Favard functional under strictly positive lower data. -/
theorem momentFunctional_mul_self_pos (α β : ℕ → ℝ) (hβ : ∀ n : ℕ, 0 < β (n + 1)) :
    ∀ d : ℕ, ∀ p : Polynomial ℝ, p.natDegree ≤ d →
      0 ≤ momentFunctional (favardMoment α β) (p * p) ∧
        (p ≠ 0 → 0 < momentFunctional (favardMoment α β) (p * p)) := by
  intro d
  induction d with
  | zero =>
      intro p hp
      have hpc := Polynomial.eq_C_of_natDegree_le_zero hp
      constructor
      · rw [hpc, ← Polynomial.C_mul, momentFunctional_C, favardMoment_zero, mul_one]
        exact mul_self_nonneg _
      · intro hne
        have hc : p.coeff 0 ≠ 0 := fun h0 => hne (by rw [hpc, h0, Polynomial.C_0])
        rw [hpc, ← Polynomial.C_mul, momentFunctional_C, favardMoment_zero, mul_one]
        exact mul_self_pos.mpr hc
  | succ d ih =>
      intro p hp
      rcases hp.lt_or_eq with hlt | heq
      · exact ih p (by omega)
      · have hp0 : p ≠ 0 := fun h => by simp [h] at heq
        set c := p.leadingCoeff with hc
        have hcne : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
        set P := favardPoly α β (d + 1) with hP
        set r := p - Polynomial.C c * P with hr
        have hdegCP : (Polynomial.C c * P).degree = ((d + 1 : ℕ) : WithBot ℕ) := by
          rw [Polynomial.degree_C_mul hcne, hP, favardPoly_degree]
        have hdegp : p.degree = ((d + 1 : ℕ) : WithBot ℕ) := by
          rw [Polynomial.degree_eq_natDegree hp0, heq]
        have hrdeg : r.degree < ((d + 1 : ℕ) : WithBot ℕ) := by
          have hd' : p.degree = (Polynomial.C c * P).degree := by rw [hdegp, hdegCP]
          have hlc' : p.leadingCoeff = (Polynomial.C c * P).leadingCoeff := by
            rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hP,
              (favardPoly_monic α β (d + 1)).leadingCoeff, mul_one]
          have hlt := Polynomial.degree_sub_lt hd' hp0 hlc'
          rwa [hdegp] at hlt
        have hrnat : r.natDegree ≤ d := by
          rcases eq_or_ne r 0 with hr0 | hr0
          · simp [hr0]
          · have hnd := (Polynomial.natDegree_lt_iff_degree_lt hr0).mpr hrdeg
            omega
        have hprod : p * p = Polynomial.C c * (Polynomial.C c * (P * P)) +
            (Polynomial.C c * (r * P) + (Polynomial.C c * (r * P) + r * r)) := by
          rw [show p = Polynomial.C c * P + r by rw [hr]; ring]
          ring
        have hPP := momentFunctional_favardPoly_mul_self α β (d + 1)
        have hrP := momentFunctional_mul_favardPoly_eq_zero α β (q := r) (k := d + 1) hrdeg
        have hprodpos : 0 < ∏ j ∈ Finset.range (d + 1), β (j + 1) :=
          Finset.prod_pos fun j _ => hβ j
        have hrr := (ih r hrnat).1
        have hexpand : momentFunctional (favardMoment α β) (p * p) =
            c * (c * (∏ j ∈ Finset.range (d + 1), β (j + 1))) +
              momentFunctional (favardMoment α β) (r * r) := by
          rw [hprod, momentFunctional_add, momentFunctional_add, momentFunctional_add,
            momentFunctional_C_mul, momentFunctional_C_mul, momentFunctional_C_mul,
            hPP, hrP]
          ring
        constructor
        · rw [hexpand]
          have hnn : 0 ≤ c * (c * (∏ j ∈ Finset.range (d + 1), β (j + 1))) := by
            have hcc : 0 ≤ c * c := mul_self_nonneg c
            nlinarith
          linarith
        · intro _
          rw [hexpand]
          have hcc : 0 < c * c := mul_self_pos.mpr hcne
          have hpos : 0 < c * (c * (∏ j ∈ Finset.range (d + 1), β (j + 1))) := by
            nlinarith
          linarith

/-- The Favard moment sequence carries a positive definite moment form. -/
theorem favard_positiveMomentForm (α β : ℕ → ℝ) (hβ : ∀ n : ℕ, 0 < β (n + 1)) :
    PositiveMomentForm (favardMoment α β) := by
  refine ⟨fun p hp => ?_⟩
  rw [momentInner_def, ← pow_two, sq]
  exact (momentFunctional_mul_self_pos α β hβ p.natDegree p le_rfl).2 hp

/-- Gram--Schmidt on the Favard moments returns exactly the recurrence family. -/
theorem monicOrtho_favardMoment (α β : ℕ → ℝ) (hβ : ∀ n : ℕ, 0 < β (n + 1)) (n : ℕ) :
    monicOrtho (favardMoment α β) n = favardPoly α β n := by
  set s := favardMoment α β with hs
  have hform := favard_positiveMomentForm α β hβ
  set D := monicOrtho s n - favardPoly α β n with hD
  rcases eq_or_ne D 0 with hD0 | hD0
  · exact sub_eq_zero.mp hD0
  · exfalso
    have hDdeg : D.degree < (n : WithBot ℕ) := by
      have hd' : (monicOrtho s n).degree = (favardPoly α β n).degree := by
        rw [monicOrtho_degree s n, favardPoly_degree α β n]
      have hlc' : (monicOrtho s n).leadingCoeff = (favardPoly α β n).leadingCoeff := by
        rw [(monicOrtho_monic s n).leadingCoeff, (favardPoly_monic α β n).leadingCoeff]
      have hlt := Polynomial.degree_sub_lt hd' (monicOrtho_ne_zero s n) hlc'
      rwa [monicOrtho_degree s n] at hlt
    have hDP : momentFunctional s (D * favardPoly α β n) = 0 :=
      momentFunctional_mul_favardPoly_eq_zero α β hDdeg
    have hDmo : momentInner s D (monicOrtho s n) = 0 := by
      rw [momentInner_comm]
      exact monicOrtho_inner_eq_zero_of_degree_lt hform n n le_rfl D hDdeg
    have hDD : momentInner s D D = 0 := by
      have hsum2 : momentFunctional s (D * monicOrtho s n) =
          momentFunctional s (D * D) + momentFunctional s (D * favardPoly α β n) := by
        rw [← momentFunctional_add]
        congr 1
        rw [hD]
        ring
      have hDmo' : momentFunctional s (D * monicOrtho s n) = 0 := hDmo
      rw [momentInner_def]
      have := hsum2
      rw [hDmo', hDP, add_zero] at this
      exact this.symm
    exact hD0 (hform.eq_zero_of_self_eq_zero hDD)

/-- The Favard norms are the running products of the lower data. -/
theorem monicOrthoNormSq_favardMoment (α β : ℕ → ℝ) (hβ : ∀ n : ℕ, 0 < β (n + 1)) (n : ℕ) :
    monicOrthoNormSq (favardMoment α β) n = ∏ j ∈ Finset.range n, β (j + 1) := by
  rw [monicOrthoNormSq, monicOrtho_favardMoment α β hβ n, momentInner_def,
    momentFunctional_favardPoly_mul_self]

/-- The Favard lower Jacobi coordinates are the prescribed data. -/
theorem monicOrthoBeta_favardMoment (α β : ℕ → ℝ) (hβ : ∀ n : ℕ, 0 < β (n + 1))
    {n : ℕ} (hn : 0 < n) :
    monicOrthoBeta (favardMoment α β) n = β n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hprodpos : 0 < ∏ j ∈ Finset.range m, β (j + 1) :=
    Finset.prod_pos fun j _ => hβ j
  show monicOrthoNormSq (favardMoment α β) (m + 1) / monicOrthoNormSq (favardMoment α β) m = _
  rw [monicOrthoNormSq_favardMoment α β hβ, monicOrthoNormSq_favardMoment α β hβ,
    Finset.prod_range_succ]
  field_simp

/-- The Favard diagonal Jacobi coordinates are the prescribed data. -/
theorem monicOrthoAlpha_favardMoment (α β : ℕ → ℝ) (hβ : ∀ n : ℕ, 0 < β (n + 1)) (n : ℕ) :
    monicOrthoAlpha (favardMoment α β) n = α n := by
  have hform := favard_positiveMomentForm α β hβ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- direct evaluation: `α'₀ = L(X)/L(1) = s₁ = α₀`
    have h1 : momentInner (favardMoment α β)
        (Polynomial.X * monicOrtho (favardMoment α β) 0)
        (monicOrtho (favardMoment α β) 0) = favardMoment α β 1 := by
      simp only [monicOrtho_zero, mul_one]
      rw [momentInner_def, mul_one, ← pow_one Polynomial.X, momentFunctional_X_pow]
    have h2 : monicOrthoNormSq (favardMoment α β) 0 = 1 := by
      rw [monicOrthoNormSq]
      simp only [monicOrtho_zero]
      rw [momentInner_def, mul_one, momentFunctional_one, favardMoment_zero]
    have h3 : favardMoment α β 1 = α 0 := by
      rw [favardMoment_succ]
      simp [Polynomial.coeff_sub]
    rw [monicOrthoAlpha, h1, h2, h3, div_one]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have hrec := X_mul_monicOrtho hform (m + 1)
    rw [monicOrtho_favardMoment α β hβ, monicOrtho_favardMoment α β hβ,
      monicOrtho_favardMoment α β hβ] at hrec
    rw [show m + 1 - 1 = m from rfl] at hrec
    rw [monicOrthoBeta_favardMoment α β hβ (by omega : 0 < m + 1)] at hrec
    rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul] at hrec
    have hours := X_mul_favardPoly α β m
    have hstep : Polynomial.C (monicOrthoAlpha (favardMoment α β) (m + 1)) *
        favardPoly α β (m + 1) =
        Polynomial.C (α (m + 1)) * favardPoly α β (m + 1) := by
      linear_combination (norm := ring_nf) hours - hrec
    have hCeq := mul_right_cancel₀ (favardPoly_ne_zero α β (m + 1)) hstep
    exact Polynomial.C_injective hCeq

/-- **Favard realization.**  Every diagonal sequence together with a strictly positive lower
sequence is the exact Jacobi data of a positive definite Hamburger moment geometry. -/
theorem exists_positiveMomentForm_of_jacobiData (α β : ℕ → ℝ)
    (hβ : ∀ n : ℕ, 0 < β (n + 1)) :
    ∃ s : ℕ → ℝ, PositiveMomentForm s ∧
      (∀ n : ℕ, monicOrthoAlpha s n = α n) ∧
      (∀ n : ℕ, 0 < n → monicOrthoBeta s n = β n) :=
  ⟨favardMoment α β, favard_positiveMomentForm α β hβ,
    monicOrthoAlpha_favardMoment α β hβ,
    fun _ hn => monicOrthoBeta_favardMoment α β hβ hn⟩

end

end HTGeometry
