import GaloisForLFunctions.PrimeTorusTheory.IteratedDifferencesOfTheLogarithm

/-!
# Tarry–Escott words

A **word** of length `M` is a nonzero `c : ℕ → ℤ` with values in `{−1, 0, 1}`, supported on `[0, M]`. Its binomial moments
are `β_j = Σ_a c(a) C(a, j)`, the Taylor coefficients at `1` of `P(z) = Σ_a c(a) z^a`.

* **Existence** (`exists_word`). By pigeonhole on subsets of `[0, M]`, if `Π_{j ≤ k} (C(M+1, j+1) + 1) < 2^{M+1}`, some word
  has `β_0 = … = β_k = 0`. So `M ≈ k² log k` suffices.
* **Newton series** (`sum_word_shift_eq`). For any `f`, `Σ_a c(a) f(x + a) = Σ_j β_j Δ^j f(x)`.
* **The multiplicity bound** (`sum_primes_le_of_moments_vanish`). If `β_j = 0` for `j < e`, every prime `p ≤ e` with
  `p² > M + 1 + p` has vanishing residue-class sums of `c`, because `C(a, j) ≡ C(a mod p, j)` modulo `p` and class sums are
  smaller than `p`. So `P` vanishes at all primitive `p`-th roots of unity, whence `Σ (p − 1) ≤ M` over those primes. The first
  nonzero moment of a word of length `M` therefore has index `≲ √(M log M)`.
-/

open Finset

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- The binomial moment `β_j = Σ_{a ≤ M} c(a) C(a, j)`. -/
def binomMoment (M : ℕ) (c : ℕ → ℤ) (j : ℕ) : ℤ := ∑ a ∈ range (M + 1), c a * (a.choose j : ℤ)

/-- A word of length `M`. -/
structure IsWord (M : ℕ) (c : ℕ → ℤ) : Prop where
  bound : ∀ a, |c a| ≤ 1
  support : ∀ a, M < a → c a = 0
  ne_zero : ∃ a, c a ≠ 0

theorem sum_range_choose_eq (M j : ℕ) :
    ∑ a ∈ range (M + 1), a.choose j = (M + 1).choose (j + 1) := by
  induction M with
  | zero =>
    cases j with
    | zero => simp
    | succ n => simp [Nat.choose_eq_zero_of_lt]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ' (M + 1) j]
    ring

theorem abs_binomMoment_le {M : ℕ} {c : ℕ → ℤ} (hc : IsWord M c) (j : ℕ) :
    |binomMoment M c j| ≤ ((M + 1).choose (j + 1) : ℤ) := by
  unfold binomMoment
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [← sum_range_choose_eq]
  push_cast
  refine Finset.sum_le_sum fun a _ => ?_
  rw [abs_mul, Nat.abs_cast]
  have := hc.bound a
  have h0 : (0 : ℤ) ≤ (a.choose j : ℤ) := by positivity
  nlinarith

/-- **Existence of words with vanishing low moments**, by pigeonhole on subsets. -/
theorem exists_word {M k : ℕ}
    (h : ∏ j ∈ range (k + 1), ((M + 1).choose (j + 1) + 1) < 2 ^ (M + 1)) :
    ∃ c, IsWord M c ∧ ∀ j ≤ k, binomMoment M c j = 0 := by
  classical
  set U := (range (M + 1)).powerset with hU
  set V := Finset.pi (range (k + 1)) (fun j => range ((M + 1).choose (j + 1) + 1)) with hV
  have hcardU : U.card = 2 ^ (M + 1) := by simp [hU]
  have hcardV : V.card = ∏ j ∈ range (k + 1), ((M + 1).choose (j + 1) + 1) := by
    simp [hV, Finset.card_pi]
  let F : Finset ℕ → (∀ j ∈ range (k + 1), ℕ) := fun S j _ => ∑ a ∈ S, a.choose j
  have hF : ∀ S ∈ U, F S ∈ V := by
    intro S hS
    refine Finset.mem_pi.mpr fun j _ => Finset.mem_range.mpr (Nat.lt_succ_of_le ?_)
    rw [← sum_range_choose_eq]
    exact Finset.sum_le_sum_of_subset (Finset.mem_powerset.mp hS)
  obtain ⟨S, hS, T, hT, hne, hST⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := U) (t := V) (f := F)
      (by rw [hcardU, hcardV]; exact h) hF
  have hSM := Finset.mem_powerset.mp hS
  have hTM := Finset.mem_powerset.mp hT
  refine ⟨fun a => (if a ∈ S then 1 else 0) - (if a ∈ T then 1 else 0), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a
    by_cases h1 : a ∈ S <;> by_cases h2 : a ∈ T <;> simp [h1, h2]
  · intro a ha
    have h1 : a ∉ S := fun h => by
      have := Finset.mem_range.mp (hSM h); omega
    have h2 : a ∉ T := fun h => by
      have := Finset.mem_range.mp (hTM h); omega
    simp [h1, h2]
  · by_contra hall
    push Not at hall
    apply hne
    ext a
    have := hall a
    by_cases h1 : a ∈ S <;> by_cases h2 : a ∈ T <;> simp_all
  · intro j hj
    have hj' : j ∈ range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
    have e := congrFun (congrFun hST j) hj'
    simp only [F] at e
    unfold binomMoment
    have hS' : ∑ a ∈ range (M + 1), (if a ∈ S then 1 else 0 : ℤ) * (a.choose j : ℤ) =
        ∑ a ∈ S, (a.choose j : ℤ) := by
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hSM]
    have hT' : ∑ a ∈ range (M + 1), (if a ∈ T then 1 else 0 : ℤ) * (a.choose j : ℤ) =
        ∑ a ∈ T, (a.choose j : ℤ) := by
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hTM]
    simp only [sub_mul, Finset.sum_sub_distrib, hS', hT']
    have e' : (∑ a ∈ S, (a.choose j : ℤ)) = ∑ a ∈ T, (a.choose j : ℤ) := by exact_mod_cast e
    rw [e', sub_self]

open scoped fwdDiff

/-- **Newton series of a word.** -/
theorem sum_word_shift_eq (M : ℕ) (c : ℕ → ℤ) (f : ℝ → ℝ) (x : ℝ) :
    ∑ a ∈ range (M + 1), (c a : ℝ) * f (x + a) =
      ∑ j ∈ range (M + 1), (binomMoment M c j : ℝ) * (fwdDiff (1 : ℝ))^[j] f x := by
  have hN : ∀ a ∈ range (M + 1), f (x + a) =
      ∑ j ∈ range (M + 1), (a.choose j : ℝ) * (fwdDiff (1 : ℝ))^[j] f x := by
    intro a ha
    have h := shift_eq_sum_fwdDiff_iter (h := (1 : ℝ)) f a x
    simp only [nsmul_eq_mul, mul_one] at h
    rw [h]
    have hsub : range (a + 1) ⊆ range (M + 1) := by
      intro j hj
      have := Finset.mem_range.mp hj
      have := Finset.mem_range.mp ha
      exact Finset.mem_range.mpr (by omega)
    refine Finset.sum_subset hsub fun j _ hj => ?_
    have hja : a < j := by
      have : ¬ j < a + 1 := fun h => hj (Finset.mem_range.mpr h)
      omega
    rw [Nat.choose_eq_zero_of_lt hja]
    simp
  rw [Finset.sum_congr rfl fun a ha => by rw [hN a ha]]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold binomMoment
  push_cast
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

/-! ### Class sums modulo a prime -/

/-- The sum of `c` over a residue class modulo `p`. -/
def classSum (M : ℕ) (c : ℕ → ℤ) (p r : ℕ) : ℤ :=
  ∑ a ∈ (range (M + 1)).filter (fun a => a % p = r), c a

/-- The binomial moment below a prime reads the class sums modulo that prime. -/
theorem binomMoment_modEq {M p j : ℕ} [Fact p.Prime] (hj : j < p) (c : ℕ → ℤ) :
    binomMoment M c j ≡ ∑ r ∈ range p, classSum M c p r * (r.choose j : ℤ) [ZMOD p] := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hL : ∀ a : ℕ, (a.choose j : ℤ) ≡ ((a % p).choose j : ℤ) [ZMOD p] := by
    intro a
    have := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := a) (k := j)
    rw [Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj, Nat.choose_zero_right, mul_one] at this
    exact_mod_cast (Int.natCast_modEq_iff.mpr this)
  have hsplit : ∑ r ∈ range p, classSum M c p r * (r.choose j : ℤ) =
      ∑ a ∈ range (M + 1), c a * ((a % p).choose j : ℤ) := by
    unfold classSum
    simp only [Finset.sum_mul]
    rw [← Finset.sum_fiberwise_of_maps_to (s := range (M + 1)) (t := range p) (g := fun a => a % p)
      (fun a _ => Finset.mem_range.mpr (Nat.mod_lt a hp))]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.mp ha).2]
  rw [hsplit]
  unfold binomMoment
  exact Int.ModEq.sum fun a _ => (Int.ModEq.refl _).mul (hL a)

/-- If the moments below `p` vanish, the class sums are divisible by `p`: the system is triangular, read from the top class down. -/
theorem classSum_modEq_zero {M p : ℕ} [Fact p.Prime] {c : ℕ → ℤ}
    (h : ∀ j < p, binomMoment M c j = 0) {r : ℕ} (hr : r < p) :
    classSum M c p r ≡ 0 [ZMOD p] := by
  classical
  have key : ∀ d r : ℕ, r < p → p - 1 - r = d → classSum M c p r ≡ 0 [ZMOD p] := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro r hr hd
      have h1 := binomMoment_modEq (M := M) (p := p) (j := r) hr c
      rw [h r hr] at h1
      have hsplit : ∑ q ∈ range p, classSum M c p q * (q.choose r : ℤ) =
          classSum M c p r + ∑ q ∈ (range p).erase r, classSum M c p q * (q.choose r : ℤ) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hr)]
        simp
      have h2 : ∑ q ∈ (range p).erase r, classSum M c p q * (q.choose r : ℤ) ≡ 0 [ZMOD p] := by
        have h3 : ∑ q ∈ (range p).erase r, classSum M c p q * (q.choose r : ℤ) ≡
            ∑ q ∈ (range p).erase r, (0 : ℤ) [ZMOD p] := by
          refine Int.ModEq.sum fun q hq => ?_
          have hne := (Finset.mem_erase.mp hq).1
          have hqp := Finset.mem_range.mp (Finset.mem_erase.mp hq).2
          rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
          · rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, mul_zero]
          · have := (ih (p - 1 - q) (by omega) q hqp rfl).mul_right (q.choose r : ℤ)
            simpa using this
        simpa using h3
      rw [hsplit] at h1
      have h5 := h1.symm.sub h2
      simpa using h5
  exact key _ r hr rfl

/-- The number of integers `≤ M` in a residue class. -/
theorem card_filter_mod_le (M p r : ℕ) (hp : 0 < p) :
    ((range (M + 1)).filter (fun a => a % p = r)).card ≤ (M + 1) / p + 1 := by
  classical
  by_cases hr : r < p
  · have hcount := Nat.count_modEq_card (b := M + 1) hp r
    have heq : ((range (M + 1)).filter (fun a => a % p = r)).card =
        ((range (M + 1)).filter (fun a => a ≡ r [MOD p])).card := by
      refine congrArg _ (Finset.filter_congr fun a _ => ?_)
      unfold Nat.ModEq
      rw [Nat.mod_eq_of_lt hr]
    rw [heq, ← Nat.count_eq_card_filter_range]
    rw [hcount]
    split_ifs <;> omega
  · have : (range (M + 1)).filter (fun a => a % p = r) = ∅ := by
      refine Finset.filter_false_of_mem fun a _ h => hr ?_
      rw [← h]
      exact Nat.mod_lt a hp
    rw [this]
    simp

/-- A class sum of a word is smaller than `p` once `p² > M + 1 + p`; so it vanishes when divisible by `p`. -/
theorem classSum_eq_zero {M p : ℕ} [Fact p.Prime] {c : ℕ → ℤ} (hc : IsWord M c)
    (h : ∀ j < p, binomMoment M c j = 0) (hpM : M + 1 + p < p * p) {r : ℕ} (hr : r < p) :
    classSum M c p r = 0 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hdvd : (p : ℤ) ∣ classSum M c p r := by
    have := classSum_modEq_zero h hr
    exact Int.modEq_zero_iff_dvd.mp this
  have hcard := card_filter_mod_le M p r hp
  have hsmall : (M + 1) / p + 1 < p := by
    have : (M + 1) / p < p - 1 + 1 - 1 + 1 - 1 := by
      have h1 : (M + 1) / p * p ≤ M + 1 := Nat.div_mul_le_self _ _
      by_contra hcon
      push Not at hcon
      have h2 : p - 1 ≤ (M + 1) / p := by omega
      have h3 : (p - 1) * p ≤ (M + 1) / p * p := Nat.mul_le_mul_right _ h2
      have h4 : (p - 1) * p = p * p - p := by
        rw [Nat.sub_mul, one_mul]
      omega
    omega
  have habs : |classSum M c p r| < p := by
    unfold classSum
    refine lt_of_le_of_lt (Finset.abs_sum_le_sum_abs _ _) ?_
    have hle : ∑ a ∈ (range (M + 1)).filter (fun a => a % p = r), |c a| ≤
        ((range (M + 1)).filter (fun a => a % p = r)).card := by
      have := Finset.sum_le_card_nsmul _ _ (1 : ℤ) fun a (_ : a ∈ (range (M + 1)).filter
        (fun a => a % p = r)) => hc.bound a
      simpa using this
    have hlt : (((range (M + 1)).filter (fun a => a % p = r)).card : ℤ) < p := by
      exact_mod_cast lt_of_le_of_lt hcard hsmall
    linarith
  exact Int.eq_zero_of_abs_lt_dvd hdvd habs

/-- The polynomial of a word. -/
def wordPoly (M : ℕ) (c : ℕ → ℤ) : Polynomial ℂ :=
  ∑ a ∈ range (M + 1), Polynomial.monomial a ((c a : ℤ) : ℂ)

theorem wordPoly_natDegree_le (M : ℕ) (c : ℕ → ℤ) : (wordPoly M c).natDegree ≤ M := by
  unfold wordPoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun a ha => ?_
  refine (Polynomial.natDegree_monomial_le _).trans ?_
  have := Finset.mem_range.mp ha
  omega

theorem wordPoly_coeff {M : ℕ} {c : ℕ → ℤ} (hc : IsWord M c) (a : ℕ) :
    (wordPoly M c).coeff a = (c a : ℂ) := by
  classical
  unfold wordPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases ha : a ∈ range (M + 1)
  · rw [Finset.sum_ite_eq' (range (M + 1)) a]
    simp [ha]
  · have hgt : M < a := by
      by_contra h
      exact ha (Finset.mem_range.mpr (by omega))
    rw [hc.support a hgt]
    simp only [Int.cast_zero]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [if_neg]
    rintro rfl
    exact ha hb

theorem wordPoly_ne_zero {M : ℕ} {c : ℕ → ℤ} (hc : IsWord M c) : wordPoly M c ≠ 0 := by
  obtain ⟨a, ha⟩ := hc.ne_zero
  intro h
  have := wordPoly_coeff hc a
  rw [h, Polynomial.coeff_zero] at this
  exact ha (by exact_mod_cast this.symm)

/-- A word whose class sums modulo `p` vanish has every `p`-th root of unity as a root. -/
theorem wordPoly_eval_eq_zero {M p : ℕ} (hp : 0 < p) {c : ℕ → ℤ}
    (h : ∀ r < p, classSum M c p r = 0) {ω : ℂ} (hω : ω ^ p = 1) :
    (wordPoly M c).eval ω = 0 := by
  classical
  unfold wordPoly
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  rw [← Finset.sum_fiberwise_of_maps_to (s := range (M + 1)) (t := range p) (g := fun a => a % p)
    (fun a _ => Finset.mem_range.mpr (Nat.mod_lt a hp))]
  refine Finset.sum_eq_zero fun r hr => ?_
  have hω' : ∀ a ∈ (range (M + 1)).filter (fun a => a % p = r),
      ((c a : ℤ) : ℂ) * ω ^ a = ((c a : ℤ) : ℂ) * ω ^ r := by
    intro a ha
    have har := (Finset.mem_filter.mp ha).2
    congr 1
    rw [← har]
    conv_lhs => rw [← Nat.div_add_mod a p, pow_add, pow_mul, hω, one_pow, one_mul]
  rw [Finset.sum_congr rfl hω', ← Finset.sum_mul]
  have := h r (Finset.mem_range.mp hr)
  unfold classSum at this
  have h2 : (∑ a ∈ (range (M + 1)).filter (fun a => a % p = r), ((c a : ℤ) : ℂ)) = 0 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) this
  rw [h2, zero_mul]

/-- **The multiplicity bound for a word.** If the moments below `e` vanish, then the primes `p ≤ e` with `p² > M + 1 + p` satisfy
`Σ (p − 1) ≤ M`. -/
theorem sum_primes_le_of_moments_vanish {M e : ℕ} {c : ℕ → ℤ} (hc : IsWord M c)
    (h : ∀ j < e, binomMoment M c j = 0) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hSe : ∀ p ∈ S, p ≤ e) (hSM : ∀ p ∈ S, M + 1 + p < p * p) :
    ∑ p ∈ S, (p - 1) ≤ M := by
  classical
  set R := S.biUnion fun p => primitiveRoots p ℂ with hR
  have hcardR : R.card = ∑ p ∈ S, (p - 1) := by
    rw [hR, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun p hp => ?_
      have hp' := hS p hp
      haveI : NeZero p := ⟨hp'.ne_zero⟩
      have hprim := Complex.isPrimitiveRoot_exp p hp'.ne_zero
      rw [hprim.card_primitiveRoots, Nat.totient_prime hp']
    · intro p hp q hq hpq
      refine Finset.disjoint_left.mpr fun ω h1 h2 => hpq ?_
      have hp' := hS p hp
      have hq' := hS q hq
      have h1' := (mem_primitiveRoots hp'.pos).mp h1
      have h2' := (mem_primitiveRoots hq'.pos).mp h2
      exact h1'.unique h2'
  have hroots : R ⊆ (wordPoly M c).roots.toFinset := by
    intro ω hω
    obtain ⟨p, hp, hωp⟩ := Finset.mem_biUnion.mp hω
    have hp' := hS p hp
    have hprim := (mem_primitiveRoots hp'.pos).mp hωp
    haveI : Fact p.Prime := ⟨hp'⟩
    have hcl : ∀ r < p, classSum M c p r = 0 := fun r hr =>
      classSum_eq_zero hc (fun j hj => h j (lt_of_lt_of_le hj (hSe p hp))) (hSM p hp) hr
    have hev := wordPoly_eval_eq_zero hp'.pos hcl hprim.pow_eq_one
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (wordPoly_ne_zero hc)).mpr hev)
  calc ∑ p ∈ S, (p - 1) = R.card := hcardR.symm
    _ ≤ (wordPoly M c).roots.toFinset.card := Finset.card_le_card hroots
    _ ≤ Multiset.card (wordPoly M c).roots := Multiset.toFinset_card_le _
    _ ≤ (wordPoly M c).natDegree := Polynomial.card_roots' _
    _ ≤ M := wordPoly_natDegree_le M c

/-- A word has a first nonzero moment: otherwise the Taylor expansion at `1` of its polynomial would vanish. -/
theorem exists_binomMoment_ne_zero {M : ℕ} {c : ℕ → ℤ} (hc : IsWord M c) :
    ∃ j, binomMoment M c j ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨a, ha⟩ := hc.ne_zero
  have haM : a ≤ M := by
    by_contra h
    exact ha (hc.support a (by omega))
  -- Downward induction: the top coefficient is the top moment.
  have key : ∀ d, ∀ b, b + d = M → c b = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro b hb
      have h0 := hall b
      unfold binomMoment at h0
      have hb' : b ∈ range (M + 1) := Finset.mem_range.mpr (by omega)
      rw [← Finset.add_sum_erase _ _ hb'] at h0
      have hrest : ∑ x ∈ (range (M + 1)).erase b, c x * (x.choose b : ℤ) = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        have hne := (Finset.mem_erase.mp hx).1
        have hxM := Finset.mem_range.mp (Finset.mem_erase.mp hx).2
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · rw [Nat.choose_eq_zero_of_lt hlt]; simp
        · rw [ih (M - x) (by omega) x (by omega)]; simp
      rw [hrest, add_zero, Nat.choose_self] at h0
      simpa using h0
  exact ha (key (M - a) a (by omega))

end

end GaloisForLFunctions.PrimeTorusTheory
