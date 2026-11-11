import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.MonicPowerSums
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitSelection

/-!
# Power sums over monic polynomials as sums over digit chains

For `q = |𝔽_q|` the power sums `S_d(N) = ∑_{a monic, deg a = d} a ^ N` obey
`S_{d+1}(N) = −∑ binom(N, j) T ^ (N − j) S_d(N − j)`, the sum over `0 < j ≤ N` with
`(q − 1) ∣ j`. This recursion has integer coefficients, so it defines `gossPoly R q d N`
over every commutative ring (`monicPowerSum_eq_gossPoly`, `map_gossPoly`).

In characteristic `p`, with `q = p ^ s`, Lucas's theorem turns the binomial coefficients into
digit selections. Unrolling the recursion indexes the terms by **digit chains**: `d` disjoint
nonempty subsets of the base-`p` digits of `N` with values divisible by `q − 1`, the rest
forming the remainder. A chain with parts `T₁, …, T_d` and remainder `R` contributes the
exponent `∑ i · val Tᵢ + (d + 1) · val R − N`.

* Every exponent in the support is the exponent of a chain
  (`exists_chain_of_coeff_gossPoly_ne_zero`).
* If all chains of largest exponent have the same part values, the coefficient at that exponent
  is nonzero (`coeff_gossPoly_ne_zero_of_unique_top`): the remaining terms of the recursion
  would produce a top chain with a different first part.
-/

open Finset Polynomial

namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

/-! ### The power-sum recursion -/

/-- The recursion of the monic power sums, with integer coefficients. -/
noncomputable def gossPoly (R : Type*) [CommRing R] (q : ℕ) : ℕ → ℕ → R[X]
  | 0, _ => 1
  | d + 1, N => -∑ j ∈ (range (N + 1)).filter (fun j => 0 < j ∧ (q - 1) ∣ j),
      C (N.choose j : R) * X ^ (N - j) * gossPoly R q d (N - j)

theorem gossPoly_zero (R : Type*) [CommRing R] (q N : ℕ) : gossPoly R q 0 N = 1 := rfl

theorem gossPoly_succ (R : Type*) [CommRing R] (q d N : ℕ) :
    gossPoly R q (d + 1) N = -∑ j ∈ (range (N + 1)).filter (fun j => 0 < j ∧ (q - 1) ∣ j),
      C (N.choose j : R) * X ^ (N - j) * gossPoly R q d (N - j) := rfl

theorem map_gossPoly {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (q d N : ℕ) :
    (gossPoly R q d N).map f = gossPoly S q d N := by
  induction d generalizing N with
  | zero => simp only [gossPoly_zero, Polynomial.map_one]
  | succ d ih =>
    rw [gossPoly_succ, gossPoly_succ, Polynomial.map_neg, Polynomial.map_sum]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, map_natCast,
      Polynomial.map_pow, Polynomial.map_X, ih]

/-- **The actual power sums.** Over a finite field the monic power sums are the recursion with
`q = |K|`. -/
theorem monicPowerSum_eq_gossPoly (K : Type*) [Field K] [Fintype K] [DecidableEq K] (d N : ℕ) :
    monicPowerSum K d N = gossPoly K (Fintype.card K) d N := by
  induction d generalizing N with
  | zero => rw [monicPowerSum_zero, gossPoly_zero]
  | succ d ih =>
    rw [monicPowerSum_succ, gossPoly_succ, sum_filter, ← sum_neg_distrib]
    apply sum_congr rfl
    intro j _
    rw [ih, coefficientMoment]
    by_cases hj : j = 0
    · simp only [hj, if_true, mul_zero, map_zero, zero_mul, lt_irrefl, false_and, if_false,
        neg_zero]
    · have hj' : 0 < j := Nat.pos_of_ne_zero hj
      by_cases hd : Fintype.card K - 1 ∣ j
      · simp only [hj, hd, hj', if_false, if_true, and_self, mul_neg, mul_one, map_neg,
          neg_mul]
      · simp only [hj, hd, hj', if_false, true_and, mul_zero, map_zero, zero_mul, neg_zero]

/-! ### Digit chains -/

variable {p : ℕ}

/-- A chain of length `d` in a digit collection `S`: pairwise disjoint nonempty parts of `S`
whose values are divisible by `p ^ s − 1`. The rest of `S` is the remainder, possibly empty. -/
structure DigitChain (p s d : ℕ) (S : Finset (Digit p)) where
  parts : Fin d → Finset (Digit p)
  subset : ∀ i, parts i ⊆ S
  disjoint : Pairwise fun i j => Disjoint (parts i) (parts j)
  nonempty : ∀ i, (parts i).Nonempty
  divisible : ∀ i, ((p : ℤ) ^ s - 1) ∣ digitValue p (parts i)

namespace DigitChain

variable {s d : ℕ} {S : Finset (Digit p)}

theorem ext_parts {c c' : DigitChain p s d S} (h : c.parts = c'.parts) : c = c' := by
  cases c
  cases c'
  cases h
  rfl

instance : Finite (DigitChain p s d S) := by
  apply Finite.of_injective
    (fun c : DigitChain p s d S => fun i =>
      (⟨c.parts i, mem_powerset.mpr (c.subset i)⟩ : ↥S.powerset))
  intro c c' h
  apply ext_parts
  funext i
  exact congrArg Subtype.val (congrFun h i)

/-- The digits of `S` outside every part. -/
def remainder (c : DigitChain p s d S) : Finset (Digit p) := S \ univ.biUnion c.parts

/-- The part values. -/
def values (c : DigitChain p s d S) (i : Fin d) : ℕ := digitValueNat p (c.parts i)

/-- Weighted part values, the remainder counted as part `d + 1`. -/
def weight (c : DigitChain p s d S) : ℕ :=
  ∑ i, (i.val + 1) * c.values i + (d + 1) * digitValueNat p c.remainder

/-- The exponent of `T` contributed by the chain. -/
def expo (c : DigitChain p s d S) : ℕ := c.weight - digitValueNat p S

theorem biUnion_subset (c : DigitChain p s d S) : univ.biUnion c.parts ⊆ S :=
  Finset.biUnion_subset.mpr fun i _ => c.subset i

/-- The part values and the remainder add up to the value of `S`. -/
theorem sum_values_add_remainder (c : DigitChain p s d S) :
    ∑ i, c.values i + digitValueNat p c.remainder = digitValueNat p S := by
  have hd : Set.PairwiseDisjoint (↑(univ : Finset (Fin d))) c.parts :=
    fun _ _ _ _ hij => c.disjoint hij
  have hu : digitValueNat p (univ.biUnion c.parts) = ∑ i, c.values i := by
    unfold digitValueNat values
    rw [sum_biUnion hd]
    rfl
  rw [← hu, remainder, digitValueNat, digitValueNat, digitValueNat, add_comm,
    sum_sdiff c.biUnion_subset]

theorem le_weight (c : DigitChain p s d S) : digitValueNat p S ≤ c.weight := by
  rw [← c.sum_values_add_remainder, weight]
  refine add_le_add (sum_le_sum fun i _ => ?_) ?_
  · exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  · exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

/-! ### Adding and removing the first part -/

theorem pairwise_disjoint_cons {α : Type*} {T : Finset α} {f : Fin d → Finset α}
    (hT : ∀ i, Disjoint T (f i)) (hf : Pairwise fun i j => Disjoint (f i) (f j)) :
    Pairwise fun i j : Fin (d + 1) =>
      Disjoint ((Fin.cons T f : Fin (d + 1) → Finset α) i)
        ((Fin.cons T f : Fin (d + 1) → Finset α) j) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact absurd rfl hij
    | succ j => simpa only [Fin.cons_zero, Fin.cons_succ] using hT j
  | succ i =>
    induction j using Fin.cases with
    | zero => simpa only [Fin.cons_zero, Fin.cons_succ] using (hT i).symm
    | succ j =>
      simp only [Fin.cons_succ]
      exact hf fun h => hij (congrArg Fin.succ h)

/-- Prepend a part `T ⊆ S` to a chain in `S \ T`. -/
def cons (T : Finset (Digit p)) (hT : T ⊆ S) (hne : T.Nonempty)
    (hdiv : ((p : ℤ) ^ s - 1) ∣ digitValue p T) (c : DigitChain p s d (S \ T)) :
    DigitChain p s (d + 1) S where
  parts := Fin.cons T c.parts
  subset i := by
    induction i using Fin.cases with
    | zero => simpa only [Fin.cons_zero] using hT
    | succ i => simpa only [Fin.cons_succ] using (c.subset i).trans sdiff_subset
  disjoint := pairwise_disjoint_cons
    (fun i => disjoint_of_subset_right (c.subset i) disjoint_sdiff) c.disjoint
  nonempty i := by
    induction i using Fin.cases with
    | zero => simpa only [Fin.cons_zero] using hne
    | succ i => simpa only [Fin.cons_succ] using c.nonempty i
  divisible i := by
    induction i using Fin.cases with
    | zero => simpa only [Fin.cons_zero] using hdiv
    | succ i => simpa only [Fin.cons_succ] using c.divisible i

/-- The chain of the parts after the first, in `S` minus the first part. -/
def tail (c : DigitChain p s (d + 1) S) : DigitChain p s d (S \ c.parts 0) where
  parts i := c.parts i.succ
  subset i := subset_sdiff.mpr ⟨c.subset i.succ, c.disjoint (Fin.succ_ne_zero i)⟩
  disjoint _ _ hij := c.disjoint fun h => hij (Fin.succ_injective _ h)
  nonempty i := c.nonempty i.succ
  divisible i := c.divisible i.succ

theorem biUnion_cons_parts (T : Finset (Digit p)) (f : Fin d → Finset (Digit p)) :
    univ.biUnion (Fin.cons T f : Fin (d + 1) → Finset (Digit p)) = T ∪ univ.biUnion f := by
  ext x
  simp only [mem_biUnion, mem_univ, true_and, mem_union, Fin.exists_fin_succ, Fin.cons_zero,
    Fin.cons_succ]

theorem cons_values (T : Finset (Digit p)) (hT : T ⊆ S) (hne : T.Nonempty)
    (hdiv : ((p : ℤ) ^ s - 1) ∣ digitValue p T) (c : DigitChain p s d (S \ T)) :
    (cons T hT hne hdiv c).values = Fin.cons (digitValueNat p T) c.values := by
  funext i
  induction i using Fin.cases with
  | zero => simp only [values, cons, Fin.cons_zero]
  | succ i => simp only [values, cons, Fin.cons_succ]

theorem cons_remainder (T : Finset (Digit p)) (hT : T ⊆ S) (hne : T.Nonempty)
    (hdiv : ((p : ℤ) ^ s - 1) ∣ digitValue p T) (c : DigitChain p s d (S \ T)) :
    (cons T hT hne hdiv c).remainder = c.remainder := by
  simp only [remainder, cons, biUnion_cons_parts]
  ext x
  simp only [mem_sdiff, mem_union]
  tauto

theorem digitValueNat_sdiff {T : Finset (Digit p)} (hT : T ⊆ S) :
    digitValueNat p (S \ T) = digitValueNat p S - digitValueNat p T := by
  unfold digitValueNat
  rw [← sum_sdiff hT]
  omega

/-- **The exponent of a prepended part.** The new exponent adds the value left after
removing that part, as in the recursion. -/
theorem expo_cons (T : Finset (Digit p)) (hT : T ⊆ S) (hne : T.Nonempty)
    (hdiv : ((p : ℤ) ^ s - 1) ∣ digitValue p T) (c : DigitChain p s d (S \ T)) :
    (cons T hT hne hdiv c).expo = digitValueNat p (S \ T) + c.expo := by
  have hsum := c.sum_values_add_remainder
  have hle := c.le_weight
  have hS : digitValueNat p S = digitValueNat p T + digitValueNat p (S \ T) := by
    rw [digitValueNat_sdiff hT]
    have : digitValueNat p T ≤ digitValueNat p S := by
      unfold digitValueNat
      exact sum_le_sum_of_subset hT
    omega
  have hw : (cons T hT hne hdiv c).weight = c.weight + digitValueNat p S := by
    simp only [weight, cons_values, cons_remainder, Fin.sum_univ_succ, Fin.cons_zero,
      Fin.cons_succ, Fin.val_zero, Fin.val_succ]
    rw [hS, ← hsum]
    simp only [add_mul, one_mul, sum_add_distrib, zero_add]
    ring
  rw [expo, hw, expo]
  omega

theorem cons_tail_parts (c : DigitChain p s (d + 1) S) :
    (Fin.cons (c.parts 0) c.tail.parts : Fin (d + 1) → Finset (Digit p)) = c.parts := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ i => rfl

theorem expo_eq_tail (c : DigitChain p s (d + 1) S) :
    c.expo = digitValueNat p (S \ c.parts 0) + c.tail.expo := by
  have h := expo_cons (c.parts 0) (c.subset 0) (c.nonempty 0) (c.divisible 0) c.tail
  rwa [show cons (c.parts 0) (c.subset 0) (c.nonempty 0) (c.divisible 0) c.tail = c from
    ext_parts (cons_tail_parts c)] at h

theorem values_zero (c : DigitChain p s (d + 1) S) : c.values 0 = digitValueNat p (c.parts 0) :=
  rfl

theorem tail_values (c : DigitChain p s (d + 1) S) (i : Fin d) :
    c.tail.values i = c.values i.succ := rfl

end DigitChain

/-! ### The support and the top coefficient -/

theorem dvd_iff_int_dvd {s j : ℕ} (hp1 : 1 ≤ p) :
    (p ^ s - 1) ∣ j ↔ ((p : ℤ) ^ s - 1) ∣ (j : ℤ) := by
  have h1 : 1 ≤ p ^ s := Nat.one_le_pow _ _ hp1
  rw [← Int.natCast_dvd_natCast, Nat.cast_sub h1]
  push_cast
  rfl

theorem coeff_gossPoly_succ {F : Type*} [Field F] {s : ℕ} (d N n : ℕ) :
    (gossPoly F (p ^ s) (d + 1) N).coeff n =
      -∑ j ∈ (range (N + 1)).filter (fun j => 0 < j ∧ (p ^ s - 1) ∣ j),
        (N.choose j : F) * (if N - j ≤ n then (gossPoly F (p ^ s) d (N - j)).coeff (n - (N - j))
          else 0) := by
  rw [gossPoly_succ, coeff_neg, finsetSum_coeff]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']

section CharP

variable [hp : Fact p.Prime] {F : Type*} [Field F] [CharP F p] {s : ℕ}

/-- **The support.** Every exponent with a nonzero coefficient is the exponent of a chain. -/
theorem exists_chain_of_coeff_gossPoly_ne_zero (d : ℕ) (S : Finset (Digit p)) (n : ℕ)
    (h : (gossPoly F (p ^ s) d (digitValueNat p S)).coeff n ≠ 0) :
    ∃ c : DigitChain p s d S, c.expo = n := by
  induction d generalizing S n with
  | zero =>
    rw [gossPoly_zero, coeff_one] at h
    have hn : n = 0 := by by_contra hn; exact h (if_neg hn)
    refine ⟨⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0⟩, ?_⟩
    simp only [DigitChain.expo, DigitChain.weight, univ_eq_empty, sum_empty, zero_add, one_mul,
      DigitChain.remainder, biUnion_empty, sdiff_empty, Nat.sub_self, hn]
  | succ d ih =>
    rw [coeff_gossPoly_succ] at h
    obtain ⟨j, hj, hne⟩ := exists_ne_zero_of_sum_ne_zero (neg_ne_zero.mp h)
    simp only [mem_filter, mem_range] at hj
    have hchoose : ((digitValueNat p S).choose j : F) ≠ 0 := left_ne_zero_of_mul hne
    have hcoeff := right_ne_zero_of_mul hne
    by_cases hle : digitValueNat p S - j ≤ n
    · rw [if_pos hle] at hcoeff
      obtain ⟨T, hTS, hTv⟩ := (cast_choose_ne_zero_iff_subset F S j).mp hchoose
      have hval : digitValueNat p (S \ T) = digitValueNat p S - j := by
        rw [DigitChain.digitValueNat_sdiff hTS, hTv]
      rw [← hval] at hcoeff hle
      obtain ⟨c, hc⟩ := ih (S \ T) _ hcoeff
      have hTne : T.Nonempty := by
        rw [nonempty_iff_ne_empty]
        rintro rfl
        simp only [digitValueNat, sum_empty] at hTv
        omega
      have hTdiv : ((p : ℤ) ^ s - 1) ∣ digitValue p T := by
        rw [← natCast_digitValueNat, hTv]
        exact (dvd_iff_int_dvd hp.out.one_lt.le).mp hj.2.2
      refine ⟨DigitChain.cons T hTS hTne hTdiv c, ?_⟩
      rw [DigitChain.expo_cons, hc]
      omega
    · exact absurd (if_neg hle) hcoeff

/-- **The top coefficient.** If all chains of largest exponent have the same part values, the
coefficient of that exponent is nonzero. -/
theorem coeff_gossPoly_ne_zero_of_unique_top (d : ℕ) (S : Finset (Digit p))
    (c₀ : DigitChain p s d S) (hmax : ∀ c : DigitChain p s d S, c.expo ≤ c₀.expo)
    (huniq : ∀ c : DigitChain p s d S, c.expo = c₀.expo → c.values = c₀.values) :
    (gossPoly F (p ^ s) d (digitValueNat p S)).coeff c₀.expo ≠ 0 := by
  induction d generalizing S with
  | zero =>
    have h0 : c₀.expo = 0 := by
      simp only [DigitChain.expo, DigitChain.weight, univ_eq_empty, sum_empty, zero_add,
        one_mul, DigitChain.remainder, biUnion_empty, sdiff_empty, Nat.sub_self]
    rw [h0, gossPoly_zero, coeff_one_zero]
    exact one_ne_zero
  | succ d ih =>
    set T := c₀.parts 0 with hTdef
    set N := digitValueNat p S
    set j₀ := digitValueNat p T
    have hTS : T ⊆ S := c₀.subset 0
    have hj₀N : j₀ ≤ N := sum_le_sum_of_subset hTS
    have hval : digitValueNat p (S \ T) = N - j₀ := DigitChain.digitValueNat_sdiff hTS
    have hexpo : c₀.expo = (N - j₀) + c₀.tail.expo := by rw [c₀.expo_eq_tail, hval]
    -- the tail is a top chain of `S \ T` with unique values
    have htail : (gossPoly F (p ^ s) d (digitValueNat p (S \ T))).coeff c₀.tail.expo ≠ 0 := by
      refine ih (S \ T) c₀.tail (fun c => ?_) (fun c hc => ?_)
      · have h := hmax (DigitChain.cons T hTS (c₀.nonempty 0) (c₀.divisible 0) c)
        rw [DigitChain.expo_cons, hval, hexpo] at h
        omega
      · have h := huniq (DigitChain.cons T hTS (c₀.nonempty 0) (c₀.divisible 0) c)
          (by rw [DigitChain.expo_cons, hval, hexpo, hc])
        funext i
        have hi := congrFun h i.succ
        rw [DigitChain.cons_values, Fin.cons_succ] at hi
        rw [hi, DigitChain.tail_values]
    rw [hval] at htail
    rw [coeff_gossPoly_succ, sum_eq_single j₀]
    · rw [if_pos (by omega), show c₀.expo - (N - j₀) = c₀.tail.expo by omega, neg_ne_zero]
      refine mul_ne_zero ?_ htail
      exact (cast_choose_ne_zero_iff_subset F S j₀).mpr ⟨T, hTS, rfl⟩
    · intro j hj hjne
      simp only [mem_filter, mem_range] at hj
      by_contra hne
      have hchoose : (N.choose j : F) ≠ 0 := left_ne_zero_of_mul hne
      have hcoeff := right_ne_zero_of_mul hne
      by_cases hle : N - j ≤ c₀.expo
      · rw [if_pos hle] at hcoeff
        obtain ⟨U, hUS, hUv⟩ := (cast_choose_ne_zero_iff_subset F S j).mp hchoose
        have hvalU : digitValueNat p (S \ U) = N - j := by
          rw [DigitChain.digitValueNat_sdiff hUS, hUv]
        rw [← hvalU] at hcoeff
        obtain ⟨c, hc⟩ := exists_chain_of_coeff_gossPoly_ne_zero d (S \ U) _ hcoeff
        have hUne : U.Nonempty := by
          rw [nonempty_iff_ne_empty]
          rintro rfl
          simp only [digitValueNat, sum_empty] at hUv
          omega
        have hUdiv : ((p : ℤ) ^ s - 1) ∣ digitValue p U := by
          rw [← natCast_digitValueNat, hUv]
          exact (dvd_iff_int_dvd hp.out.one_lt.le).mp hj.2.2
        have h := huniq (DigitChain.cons U hUS hUne hUdiv c)
          (by rw [DigitChain.expo_cons, hc, hvalU]; omega)
        have h0 := congrFun h 0
        rw [DigitChain.cons_values, Fin.cons_zero, DigitChain.values_zero, hUv] at h0
        exact hjne h0
      · exact hcoeff (if_neg hle)
    · intro hj₀
      exfalso
      apply hj₀
      simp only [mem_filter, mem_range]
      refine ⟨by omega, ?_, ?_⟩
      · have hpos : 0 < digitValueNat p T := by
          obtain ⟨x, hx⟩ := c₀.nonempty 0
          exact lt_of_lt_of_le (pow_pos hp.out.pos x.1)
            (single_le_sum (f := fun y : Digit p => p ^ y.1) (fun _ _ => Nat.zero_le _) hx)
        exact hpos
      · have h := c₀.divisible 0
        rw [← natCast_digitValueNat] at h
        exact (dvd_iff_int_dvd hp.out.one_lt.le).mpr h

end CharP

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
