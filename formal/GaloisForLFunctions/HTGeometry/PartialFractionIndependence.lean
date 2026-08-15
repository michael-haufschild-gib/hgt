import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.LinearCombination

/-!
# Independence of the divided principal parts at distinct roots

For distinct points `r i` with multiplicities `m i`, the divided principal parts of
`∏ (X - r i)^(m i)` are the polynomials

`B i p = (X - r i)^(m i - p) · ∏_{l ≠ i} (X - r l)^(m l)`,  `1 ≤ p ≤ m i`,

that is, `A/(X - r i)^p` written without division.  They are linearly independent: at the root
`r i` the term of largest divided order has the lowest order of vanishing, and every other term
vanishes to one order more, so its coefficient is forced to zero.

This is the algebraic content of "the rational principal parts are independent", which converts one
null state with repeated roots into a lower bound on the dimension of a radical.
-/

open Polynomial

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {k : ℕ}

/-- The divided principal part of order `p` at the root `r i`, written without division. -/
def dividedPart (r : Fin k → ℝ) (m : Fin k → ℕ) (i : Fin k) (p : ℕ) : Polynomial ℝ :=
  (Polynomial.X - Polynomial.C (r i)) ^ (m i - p) *
    ∏ l ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (r l)) ^ (m l)

/-- Every other divided part vanishes at `r i₀` to order at least `m i₀ - p₀ + 1`. -/
theorem pow_dvd_dividedPart_of_ne (r : Fin k → ℝ) (m : Fin k → ℕ) {i₀ : Fin k} {p₀ : ℕ}
    (hp₀ : 1 ≤ p₀) (hp₀le : p₀ ≤ m i₀) {i : Fin k} {p : ℕ}
    (h : i ≠ i₀ ∨ (i = i₀ ∧ p < p₀)) :
    ((Polynomial.X - Polynomial.C (r i₀)) ^ (m i₀ - p₀ + 1)) ∣ dividedPart r m i p := by
  classical
  rcases h with hne | ⟨hi, hlt⟩
  · refine Dvd.dvd.mul_left ?_ _
    have hmem : i₀ ∈ Finset.univ.erase i :=
      Finset.mem_erase.2 ⟨fun h => hne h.symm, Finset.mem_univ i₀⟩
    refine dvd_trans (pow_dvd_pow (Polynomial.X - Polynomial.C (r i₀))
      (show m i₀ - p₀ + 1 ≤ m i₀ by omega)) (Finset.dvd_prod_of_mem _ hmem)
  · subst hi
    exact Dvd.dvd.mul_right (pow_dvd_pow (Polynomial.X - Polynomial.C (r i))
      (show m i - p₀ + 1 ≤ m i - p by omega)) _

/-- The product over the other roots does not vanish at `r i₀`. -/
theorem eval_prod_erase_ne_zero {r : Fin k → ℝ} (hr : Function.Injective r) (m : Fin k → ℕ)
    (i₀ : Fin k) :
    (∏ l ∈ Finset.univ.erase i₀, (Polynomial.X - Polynomial.C (r l)) ^ (m l)).eval (r i₀)
      ≠ 0 := by
  classical
  rw [Polynomial.eval_prod]
  refine Finset.prod_ne_zero_iff.2 fun l hl => ?_
  have hne : l ≠ i₀ := (Finset.mem_erase.1 hl).1
  have hval : (r i₀ - r l) ≠ 0 := sub_ne_zero.2 fun h => hne (hr h.symm)
  simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact pow_ne_zero _ hval

/-- **Independence of the divided principal parts.** -/
theorem dividedPart_eq_zero_of_sum_eq_zero {r : Fin k → ℝ} (hr : Function.Injective r)
    (m : Fin k → ℕ) (c : Fin k → ℕ → ℝ)
    (hsum : ∑ i : Fin k, ∑ p ∈ Finset.Icc 1 (m i),
      Polynomial.C (c i p) * dividedPart r m i p = 0) :
    ∀ (i : Fin k), ∀ p ∈ Finset.Icc 1 (m i), c i p = 0 := by
  classical
  by_contra hcon
  obtain ⟨i₀, hi₀⟩ := not_forall.1 hcon
  obtain ⟨p₀, hp₀⟩ := not_forall.1 hi₀
  obtain ⟨hp₀mem, hp₀ne⟩ := Classical.not_imp.1 hp₀
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ,
      S = (Finset.Icc 1 (m i₀)).filter fun p => c i₀ p ≠ 0 := ⟨_, rfl⟩
  have hSne : S.Nonempty := ⟨p₀, by rw [hS]; exact Finset.mem_filter.2 ⟨hp₀mem, hp₀ne⟩⟩
  obtain ⟨q, hqS, hqmax⟩ : ∃ q ∈ S, ∀ p ∈ S, p ≤ q :=
    ⟨S.max' hSne, S.max'_mem hSne, fun p hp => S.le_max' p hp⟩
  have hqmem : q ∈ Finset.Icc 1 (m i₀) := by
    rw [hS] at hqS
    exact (Finset.mem_filter.1 hqS).1
  have hqne : c i₀ q ≠ 0 := by
    rw [hS] at hqS
    exact (Finset.mem_filter.1 hqS).2
  have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hqmem).1
  have hqle : q ≤ m i₀ := (Finset.mem_Icc.1 hqmem).2
  obtain ⟨g, hg⟩ : ∃ g : ((_ : Fin k) × ℕ) → Polynomial ℝ,
      g = fun x => Polynomial.C (c x.1 x.2) * dividedPart r m x.1 x.2 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Finset ((_ : Fin k) × ℕ),
      T = Finset.univ.sigma fun i => Finset.Icc 1 (m i) := ⟨_, rfl⟩
  have hsumT : ∑ x ∈ T, g x = 0 := by
    rw [hT, Finset.sum_sigma, hg]
    exact hsum
  have hx₀ : (⟨i₀, q⟩ : (_ : Fin k) × ℕ) ∈ T := by
    rw [hT]
    exact Finset.mem_sigma.2 ⟨Finset.mem_univ _, hqmem⟩
  have hsplit : g ⟨i₀, q⟩ + ∑ x ∈ T.erase ⟨i₀, q⟩, g x = 0 := by
    rw [Finset.add_sum_erase T g hx₀]
    exact hsumT
  have hrest : ((Polynomial.X - Polynomial.C (r i₀)) ^ (m i₀ - q + 1))
      ∣ ∑ x ∈ T.erase ⟨i₀, q⟩, g x := by
    refine Finset.dvd_sum fun x hx => ?_
    have hxne : x ≠ (⟨i₀, q⟩ : (_ : Fin k) × ℕ) := (Finset.mem_erase.1 hx).1
    have hxmem : x ∈ T := (Finset.mem_erase.1 hx).2
    have hxIcc : x.2 ∈ Finset.Icc 1 (m x.1) := by
      rw [hT] at hxmem
      exact (Finset.mem_sigma.1 hxmem).2
    simp only [hg]
    by_cases hi : x.1 = i₀
    · by_cases hlt : x.2 < q
      · exact Dvd.dvd.mul_left (pow_dvd_dividedPart_of_ne r m hq1 hqle (Or.inr ⟨hi, hlt⟩)) _
      · have hczero : c x.1 x.2 = 0 := by
          by_contra hc
          have hmemS : x.2 ∈ S := by
            rw [hS, ← hi]
            exact Finset.mem_filter.2 ⟨hxIcc, hc⟩
          have hle := hqmax x.2 hmemS
          have hpq : x.2 = q := by omega
          exact hxne (Sigma.ext hi (by rw [hpq]))
        rw [hczero, map_zero, zero_mul]
        exact dvd_zero _
    · exact Dvd.dvd.mul_left (pow_dvd_dividedPart_of_ne r m hq1 hqle (Or.inl hi)) _
  have hmain : ((Polynomial.X - Polynomial.C (r i₀)) ^ (m i₀ - q + 1)) ∣ g ⟨i₀, q⟩ := by
    have heq : g ⟨i₀, q⟩ = -∑ x ∈ T.erase ⟨i₀, q⟩, g x :=
      eq_neg_of_add_eq_zero_left hsplit
    rw [heq]
    exact hrest.neg_right
  simp only [hg] at hmain
  obtain ⟨Pi0, hPi0⟩ : ∃ Pi0 : Polynomial ℝ,
      Pi0 = ∏ l ∈ Finset.univ.erase i₀, (Polynomial.X - Polynomial.C (r l)) ^ (m l) := ⟨_, rfl⟩
  have hform : Polynomial.C (c i₀ q) * dividedPart r m i₀ q
      = (Polynomial.X - Polynomial.C (r i₀)) ^ (m i₀ - q) * (Polynomial.C (c i₀ q) * Pi0) := by
    rw [dividedPart, hPi0]
    ring
  rw [hform, pow_succ] at hmain
  have hXne : ((Polynomial.X - Polynomial.C (r i₀)) ^ (m i₀ - q) : Polynomial ℝ) ≠ 0 :=
    pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (r i₀))
  have hcancel : (Polynomial.X - Polynomial.C (r i₀)) ∣ (Polynomial.C (c i₀ q) * Pi0) :=
    (mul_dvd_mul_iff_left hXne).1 hmain
  have hroot : (Polynomial.C (c i₀ q) * Pi0).eval (r i₀) = 0 :=
    Polynomial.dvd_iff_isRoot.1 hcancel
  rw [Polynomial.eval_mul, Polynomial.eval_C] at hroot
  have hPi0ne : Pi0.eval (r i₀) ≠ 0 := by
    rw [hPi0]
    exact eval_prod_erase_ne_zero hr m i₀
  exact hqne ((mul_eq_zero.1 hroot).resolve_right hPi0ne)

/-! ## The state itself, and the degree separation -/

/-- The product of all root factors: the state divided by its regular part. -/
def rootProduct (r : Fin k → ℝ) (m : Fin k → ℕ) : Polynomial ℝ :=
  ∏ l : Fin k, (Polynomial.X - Polynomial.C (r l)) ^ (m l)

theorem monic_rootProduct (r : Fin k → ℝ) (m : Fin k → ℕ) : (rootProduct r m).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun l _ => (Polynomial.monic_X_sub_C (r l)).pow _

theorem natDegree_rootProduct (r : Fin k → ℝ) (m : Fin k → ℕ) :
    (rootProduct r m).natDegree = ∑ l : Fin k, m l := by
  rw [rootProduct, Polynomial.natDegree_prod _ _
    fun l _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (r l))]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]

theorem monic_dividedPart (r : Fin k → ℝ) (m : Fin k → ℕ) (i : Fin k) (p : ℕ) :
    (dividedPart r m i p).Monic := by
  classical
  exact ((Polynomial.monic_X_sub_C (r i)).pow _).mul
    (Polynomial.monic_prod_of_monic _ _ fun l _ => (Polynomial.monic_X_sub_C (r l)).pow _)

theorem natDegree_dividedPart (r : Fin k → ℝ) (m : Fin k → ℕ) (i : Fin k) {p : ℕ}
    (hp : p ≤ m i) : (dividedPart r m i p).natDegree = (∑ l : Fin k, m l) - p := by
  classical
  rw [dividedPart, Polynomial.Monic.natDegree_mul ((Polynomial.monic_X_sub_C (r i)).pow _)
      (Polynomial.monic_prod_of_monic _ _ fun l _ => (Polynomial.monic_X_sub_C (r l)).pow _),
    Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one,
    Polynomial.natDegree_prod _ _ fun l _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (r l))]
  have hterms : ∑ l ∈ Finset.univ.erase i,
      ((Polynomial.X - Polynomial.C (r l)) ^ (m l)).natDegree
        = ∑ l ∈ Finset.univ.erase i, m l :=
    Finset.sum_congr rfl fun l _ => by
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  have hsplit : ∑ l : Fin k, m l = m i + ∑ l ∈ Finset.univ.erase i, m l :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  rw [hterms, hsplit]
  omega

/-- **Independence of the state and its divided principal parts.**  The state has degree
`∑ m l`, every divided part has strictly smaller degree, so the coefficient of the state is read
off from the top coefficient and the remaining independence is the previous theorem. -/
theorem base_and_dividedPart_eq_zero_of_sum_eq_zero {r : Fin k → ℝ} (hr : Function.Injective r)
    (m : Fin k → ℕ) (c₀ : ℝ) (c : Fin k → ℕ → ℝ)
    (hsum : Polynomial.C c₀ * rootProduct r m
      + ∑ i : Fin k, ∑ p ∈ Finset.Icc 1 (m i),
          Polynomial.C (c i p) * dividedPart r m i p = 0) :
    c₀ = 0 ∧ ∀ (i : Fin k), ∀ p ∈ Finset.Icc 1 (m i), c i p = 0 := by
  classical
  have hc₀ : c₀ = 0 := by
    have hco := congrArg (fun P : Polynomial ℝ => P.coeff (∑ l : Fin k, m l)) hsum
    simp only [Polynomial.coeff_add, Polynomial.coeff_zero] at hco
    have hbase : (Polynomial.C c₀ * rootProduct r m).coeff (∑ l : Fin k, m l) = c₀ := by
      rw [Polynomial.coeff_C_mul, ← natDegree_rootProduct r m,
        (monic_rootProduct r m).coeff_natDegree, mul_one]
    have hrest : (∑ i : Fin k, ∑ p ∈ Finset.Icc 1 (m i),
        Polynomial.C (c i p) * dividedPart r m i p).coeff (∑ l : Fin k, m l) = 0 := by
      rw [Polynomial.finsetSum_coeff]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Polynomial.finsetSum_coeff]
      refine Finset.sum_eq_zero fun p hp => ?_
      obtain ⟨hp1, hpm⟩ := Finset.mem_Icc.1 hp
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      refine lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) ?_
      rw [natDegree_dividedPart r m i hpm]
      have hle : m i ≤ ∑ l : Fin k, m l :=
        Finset.single_le_sum (fun l _ => Nat.zero_le (m l)) (Finset.mem_univ i)
      omega
    rw [hbase, hrest, add_zero] at hco
    exact hco
  refine ⟨hc₀, dividedPart_eq_zero_of_sum_eq_zero hr m c ?_⟩
  rw [hc₀] at hsum
  simpa using hsum

/-! ## The divided principal parts as functions -/

/-- The part of the state regular at the root `r i`. -/
def multiRegular (r : Fin k → ℝ) (m : Fin k → ℕ) (G : ℝ → ℝ) (i : Fin k) : ℝ → ℝ :=
  fun u => (∏ l ∈ Finset.univ.erase i, (u - r l) ^ (m l)) * G u

/-- The divided principal part of order `p` at the root `r i`, written without division. -/
def multiJetDescendant (r : Fin k → ℝ) (m : Fin k → ℕ) (G : ℝ → ℝ) (i : Fin k) (p : ℕ) :
    ℝ → ℝ :=
  fun u => (u - r i) ^ (m i - p) * multiRegular r m G i u

/-- The state with prescribed roots and regular part. -/
def multiJetBase (r : Fin k → ℝ) (m : Fin k → ℕ) (G : ℝ → ℝ) : ℝ → ℝ :=
  fun u => (∏ l : Fin k, (u - r l) ^ (m l)) * G u

theorem multiJetDescendant_zero (r : Fin k → ℝ) (m : Fin k → ℕ) (G : ℝ → ℝ) (i : Fin k) :
    multiJetDescendant r m G i 0 = multiJetBase r m G := by
  classical
  funext u
  rw [multiJetDescendant, multiRegular, multiJetBase, Nat.sub_zero, ← mul_assoc,
    Finset.mul_prod_erase _ (fun l => (u - r l) ^ (m l)) (Finset.mem_univ i)]

theorem eval_dividedPart (r : Fin k → ℝ) (m : Fin k → ℕ) (i : Fin k) (p : ℕ) (G : ℝ → ℝ)
    (u : ℝ) : (dividedPart r m i p).eval u * G u = multiJetDescendant r m G i p u := by
  classical
  rw [dividedPart, multiJetDescendant, multiRegular]
  simp only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  ring

theorem eval_rootProduct (r : Fin k → ℝ) (m : Fin k → ℕ) (G : ℝ → ℝ) (u : ℝ) :
    (rootProduct r m).eval u * G u = multiJetBase r m G u := by
  rw [rootProduct, multiJetBase]
  simp only [Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]

/-- **Independence of the state and its divided principal parts, as functions.**  A vanishing
combination on an infinite set where the regular part does not vanish forces the corresponding
polynomial combination to have infinitely many roots. -/
theorem multiJet_eq_zero_of_sum_eq_zero {r : Fin k → ℝ} (hr : Function.Injective r)
    (m : Fin k → ℕ) (G : ℝ → ℝ) {S : Set ℝ} (hS : S.Infinite) (hG : ∀ u ∈ S, G u ≠ 0)
    (c₀ : ℝ) (c : Fin k → ℕ → ℝ)
    (hsum : ∀ u : ℝ, c₀ * multiJetBase r m G u
      + ∑ i : Fin k, ∑ p ∈ Finset.Icc 1 (m i), c i p * multiJetDescendant r m G i p u = 0) :
    c₀ = 0 ∧ ∀ (i : Fin k), ∀ p ∈ Finset.Icc 1 (m i), c i p = 0 := by
  classical
  obtain ⟨P, hP⟩ : ∃ P : Polynomial ℝ,
      P = Polynomial.C c₀ * rootProduct r m
        + ∑ i : Fin k, ∑ p ∈ Finset.Icc 1 (m i),
            Polynomial.C (c i p) * dividedPart r m i p := ⟨_, rfl⟩
  have heval : ∀ u ∈ S, P.eval u = 0 := by
    intro u hu
    have hGu : G u ≠ 0 := hG u hu
    have hmul : P.eval u * G u = 0 := by
      rw [hP]
      simp only [Polynomial.eval_add, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C]
      rw [add_mul, Finset.sum_mul]
      have h1 : (c₀ * (rootProduct r m).eval u) * G u = c₀ * multiJetBase r m G u := by
        rw [mul_assoc, eval_rootProduct]
      have h2 : ∀ i : Fin k,
          (∑ p ∈ Finset.Icc 1 (m i), c i p * (dividedPart r m i p).eval u) * G u
            = ∑ p ∈ Finset.Icc 1 (m i), c i p * multiJetDescendant r m G i p u := by
        intro i
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [mul_assoc, eval_dividedPart]
      rw [h1]
      have h3 : ∑ i : Fin k,
          (∑ p ∈ Finset.Icc 1 (m i), c i p * (dividedPart r m i p).eval u) * G u
            = ∑ i : Fin k, ∑ p ∈ Finset.Icc 1 (m i), c i p * multiJetDescendant r m G i p u :=
        Finset.sum_congr rfl fun i _ => h2 i
      rw [h3]
      exact hsum u
    exact (mul_eq_zero.1 hmul).resolve_right hGu
  have hsub : S ⊆ {x : ℝ | P.IsRoot x} := fun u hu => heval u hu
  have hzero : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P (hS.mono hsub)
  rw [hP] at hzero
  exact base_and_dividedPart_eq_zero_of_sum_eq_zero hr m c₀ c hzero

/-! ## The independent family of nonterminal directions -/

theorem sum_Icc_one_eq_sum_fin {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ p ∈ Finset.Icc 1 n, f p = ∑ j : Fin n, f ((j : ℕ) + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  rw [Fin.sum_univ_eq_sum_range (fun j => f (j + 1)) n]
  exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm]

/-- The state together with all its nonterminal divided principal parts. -/
def multiJetEvenFamily (r : Fin k → ℝ) (m : Fin k → ℕ) (G : ℝ → ℝ) :
    Unit ⊕ ((i : Fin k) × Fin (m i - 1)) → (ℝ → ℝ) :=
  Sum.elim (fun _ => multiJetBase r m G)
    (fun x => multiJetDescendant r m G x.1 ((x.2 : ℕ) + 1))

/-- **The state and its nonterminal divided principal parts are linearly independent.** -/
theorem linearIndependent_multiJetEvenFamily {r : Fin k → ℝ} (hr : Function.Injective r)
    (m : Fin k → ℕ) (G : ℝ → ℝ) {S : Set ℝ} (hS : S.Infinite) (hG : ∀ u ∈ S, G u ≠ 0) :
    LinearIndependent ℝ (multiJetEvenFamily r m G) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  obtain ⟨c, hc⟩ : ∃ c : Fin k → ℕ → ℝ,
      c = fun i p => ∑ j : Fin (m i - 1),
        if (j : ℕ) + 1 = p then g (Sum.inr ⟨i, j⟩) else 0 := ⟨_, rfl⟩
  have hcval : ∀ (i : Fin k) (j : Fin (m i - 1)), c i ((j : ℕ) + 1) = g (Sum.inr ⟨i, j⟩) := by
    intro i j
    simp only [hc]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]
    · intro b _ hb
      exact if_neg fun h => hb (Fin.ext (by omega))
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hczero : ∀ (i : Fin k), ∀ p ∈ Finset.Icc 1 (m i), p ∉ Finset.Icc 1 (m i - 1) →
      c i p = 0 := by
    intro i p hp hpn
    obtain ⟨hp1, hpm⟩ := Finset.mem_Icc.1 hp
    have hgt : ¬ (p ≤ m i - 1) := fun h => hpn (Finset.mem_Icc.2 ⟨hp1, h⟩)
    simp only [hc]
    refine Finset.sum_eq_zero fun j _ => if_neg fun h => ?_
    have hjlt := j.isLt
    exact hgt (by omega)
  have hsum : ∀ u : ℝ, g (Sum.inl ()) * multiJetBase r m G u
      + ∑ i : Fin k, ∑ p ∈ Finset.Icc 1 (m i), c i p * multiJetDescendant r m G i p u = 0 := by
    intro u
    have hpt := congrFun hg u
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hpt
    rw [Fintype.sum_sum_type] at hpt
    simp only [multiJetEvenFamily, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
      Finset.sum_singleton] at hpt
    have hblocks : ∀ i : Fin k, ∑ p ∈ Finset.Icc 1 (m i), c i p * multiJetDescendant r m G i p u
        = ∑ j : Fin (m i - 1),
            g (Sum.inr ⟨i, j⟩) * multiJetDescendant r m G i ((j : ℕ) + 1) u := by
      intro i
      rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.sub_le (m i) 1))
        (fun p hp hpn => by rw [hczero i p hp hpn, zero_mul])]
      rw [sum_Icc_one_eq_sum_fin (m i - 1)
        (fun p => c i p * multiJetDescendant r m G i p u)]
      exact Finset.sum_congr rfl fun j _ => by rw [hcval i j]
    have hsigma : ∑ x : ((i : Fin k) × Fin (m i - 1)),
        g (Sum.inr x) * multiJetDescendant r m G x.1 ((x.2 : ℕ) + 1) u
          = ∑ i : Fin k, ∑ j : Fin (m i - 1),
              g (Sum.inr ⟨i, j⟩) * multiJetDescendant r m G i ((j : ℕ) + 1) u := by
      rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hblocks i, ← hsigma]
    exact hpt
  obtain ⟨hzero, hrest⟩ := multiJet_eq_zero_of_sum_eq_zero hr m G hS hG _ c hsum
  rintro (⟨⟩ | ⟨i, j⟩)
  · exact hzero
  · rw [← hcval i j]
    refine hrest i ((j : ℕ) + 1) (Finset.mem_Icc.2 ⟨by omega, ?_⟩)
    have := j.isLt
    omega

/-! ## Arbitrary selections of divided orders -/

/-- The state together with a selected set `A i` of divided orders at each root. -/
def multiJetSubfamily (r : Fin k → ℝ) (m : Fin k → ℕ) (G : ℝ → ℝ) (A : Fin k → Finset ℕ) :
    Unit ⊕ ((i : Fin k) × {p // p ∈ A i}) → (ℝ → ℝ) :=
  Sum.elim (fun _ => multiJetBase r m G)
    (fun x => multiJetDescendant r m G x.1 (x.2 : ℕ))

/-- **The state and any selection of its divided principal parts are linearly independent.** -/
theorem linearIndependent_multiJetSubfamily {r : Fin k → ℝ} (hr : Function.Injective r)
    (m : Fin k → ℕ) (G : ℝ → ℝ) (A : Fin k → Finset ℕ)
    (hA : ∀ i, A i ⊆ Finset.Icc 1 (m i))
    {S : Set ℝ} (hS : S.Infinite) (hG : ∀ u ∈ S, G u ≠ 0) :
    LinearIndependent ℝ (multiJetSubfamily r m G A) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  obtain ⟨c, hc⟩ : ∃ c : Fin k → ℕ → ℝ,
      c = fun i p => ∑ q ∈ (A i).attach, if (q : ℕ) = p then g (Sum.inr ⟨i, q⟩) else 0 :=
    ⟨_, rfl⟩
  have hcval : ∀ (i : Fin k) (q : {p // p ∈ A i}), c i (q : ℕ) = g (Sum.inr ⟨i, q⟩) := by
    intro i q
    simp only [hc]
    rw [Finset.sum_eq_single q]
    · rw [if_pos rfl]
    · intro b _ hb
      exact if_neg fun h => hb (Subtype.ext h)
    · intro hq
      exact absurd (Finset.mem_attach _ q) hq
  have hczero : ∀ (i : Fin k) (p : ℕ), p ∉ A i → c i p = 0 := by
    intro i p hp
    simp only [hc]
    refine Finset.sum_eq_zero fun q _ => if_neg fun h => ?_
    exact hp (h ▸ q.2)
  have hsum : ∀ u : ℝ, g (Sum.inl ()) * multiJetBase r m G u
      + ∑ i : Fin k, ∑ p ∈ Finset.Icc 1 (m i), c i p * multiJetDescendant r m G i p u = 0 := by
    intro u
    have hpt := congrFun hg u
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hpt
    rw [Fintype.sum_sum_type] at hpt
    simp only [multiJetSubfamily, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
      Finset.sum_singleton] at hpt
    have hblocks : ∀ i : Fin k,
        ∑ p ∈ Finset.Icc 1 (m i), c i p * multiJetDescendant r m G i p u
          = ∑ q ∈ (A i).attach,
              g (Sum.inr ⟨i, q⟩) * multiJetDescendant r m G i (q : ℕ) u := by
      intro i
      rw [← Finset.sum_subset (hA i) (fun p _ hpn => by rw [hczero i p hpn, zero_mul])]
      rw [← Finset.sum_attach (A i) (fun p => c i p * multiJetDescendant r m G i p u)]
      exact Finset.sum_congr rfl fun q _ => by rw [hcval i q]
    have hsigma : ∑ x : ((i : Fin k) × {p // p ∈ A i}),
        g (Sum.inr x) * multiJetDescendant r m G x.1 (x.2 : ℕ) u
          = ∑ i : Fin k, ∑ q ∈ (A i).attach,
              g (Sum.inr ⟨i, q⟩) * multiJetDescendant r m G i (q : ℕ) u := by
      rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.univ_eq_attach]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hblocks i, ← hsigma]
    exact hpt
  obtain ⟨hzero, hrest⟩ := multiJet_eq_zero_of_sum_eq_zero hr m G hS hG _ c hsum
  rintro (⟨⟩ | ⟨i, q⟩)
  · exact hzero
  · rw [← hcval i q]
    exact hrest i (q : ℕ) (hA i q.2)

end GaloisForLFunctions.HTGeometry

end
