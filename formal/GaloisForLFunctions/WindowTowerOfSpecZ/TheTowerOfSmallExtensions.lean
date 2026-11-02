import GaloisForLFunctions.WindowTowerOfSpecZ.TheWindowDirichletAlgebra

/-!
# The tower of small extensions

The window algebra of length `A` is the ring of arithmetic functions modulo the **truncation ideal**
`I_N = {f : f(n) = 0 for 1 ≤ n ≤ N}`, `N = ⌊e^A⌋` (`ker_windowRep`). As the window grows the
algebras form an inverse system `D_1 ← D_2 ← D_3 ← ⋯` of local Artinian rings with maximal ideal
`m = I_1 = {f : f(1) = 0}`. Its control theory is exact:

* **One new fold per stage** (`sub_single_mem_truncIdeal_succ`): `I_N / I_{N+1}` is spanned by the
  basis function `δ_{N+1}` of the integer that enters.
* **The socle law** (`mul_mem_truncIdeal`): `I_M · m ⊆ I_{2M+1}`. In particular each transition
  `D_{N+1} → D_N` is a small extension: its kernel is killed by the maximal ideal. On a window
  shorter than `log 2n` the new fold `T_n` composes to zero with every element of `m`
  (`windowRep_single_mul_eq_zero`).
* **Loewy length** (`pow_truncIdeal_one_le`, `windowRep_kills_pow_iff`): `m^k ⊆ I_{2^k − 1}`, and
  `ρ_A` kills `m^k` exactly when `⌊e^A⌋ < 2^k`: any `k` folds compose to zero on windows shorter
  than `k log 2`, and `T₂^{k−1}` survives on longer ones.
* **The cotangent space is the primes** (`mem_sq_sup_truncIdeal_iff`): `f ∈ m` lies in `m² + I_N`
  iff `f` vanishes at every prime `p ≤ N`. The primes `≤ e^A` are a basis of `m/(m² + I_N)`: they
  generate the window algebra, and prime powers and composites are products.
* **The inverse limit is the Dirichlet ring** (`iInf_truncIdeal`, `existsUnique_limit`): the tower
  separates points, and every compatible family of window classes comes from a unique arithmetic
  function.
-/

noncomputable section

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ

variable {R : Type*} [CommRing R]

/-! ### Truncation ideals and basis functions -/

theorem sub_apply' (f g : ArithmeticFunction R) (n : ℕ) : (f - g) n = f n - g n := by
  rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply, ← sub_eq_add_neg]

/-- The **truncation ideal** `I_N`: arithmetic functions vanishing on `[1, N]`. -/
def truncIdeal (N : ℕ) : Ideal (ArithmeticFunction R) where
  carrier := {f | ∀ n, 1 ≤ n → n ≤ N → f n = 0}
  add_mem' {f g} hf hg n h1 hN := by
    rw [ArithmeticFunction.add_apply, hf n h1 hN, hg n h1 hN, add_zero]
  zero_mem' _ _ _ := rfl
  smul_mem' c f hf n h1 hN := by
    rw [smul_eq_mul, ArithmeticFunction.mul_apply]
    refine Finset.sum_eq_zero fun x hx => ?_
    obtain ⟨hxn, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have h2 : 1 ≤ x.2 := Nat.pos_of_ne_zero fun h => hn0 (by rw [← hxn, h, mul_zero])
    have h3 : x.2 ≤ n := Nat.le_of_dvd (by omega) ⟨x.1, by rw [← hxn, mul_comm]⟩
    rw [hf x.2 h2 (h3.trans hN), mul_zero]

theorem mem_truncIdeal {N : ℕ} {f : ArithmeticFunction R} :
    f ∈ truncIdeal N ↔ ∀ n, 1 ≤ n → n ≤ N → f n = 0 := Iff.rfl

/-- The maximal ideal of the window algebra is `I_1 = {f : f(1) = 0}`. -/
theorem mem_truncIdeal_one {f : ArithmeticFunction R} : f ∈ truncIdeal 1 ↔ f 1 = 0 :=
  ⟨fun h => h 1 le_rfl le_rfl, fun h n h1 hn => by rw [show n = 1 by omega, h]⟩

theorem truncIdeal_anti {M N : ℕ} (h : M ≤ N) :
    (truncIdeal N : Ideal (ArithmeticFunction R)) ≤ truncIdeal M :=
  fun _ hf n h1 hn => hf n h1 (hn.trans h)

/-- The basis function `c·δ_n`. -/
def single (n : ℕ) (c : R) : ArithmeticFunction R :=
  ⟨fun k => if k = n ∧ k ≠ 0 then c else 0, by simp⟩

theorem single_apply (n : ℕ) (c : R) (k : ℕ) :
    single n c k = if k = n ∧ k ≠ 0 then c else 0 := rfl

theorem single_apply_self {n : ℕ} (hn : n ≠ 0) (c : R) : single n c n = c := by
  rw [single_apply, if_pos ⟨rfl, hn⟩]

/-- `δ_a · δ_b = δ_{ab}`: the basis functions multiply like the integers. -/
theorem single_mul_single {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (c d : R) :
    single a c * single b d = single (a * b) (c * d) := by
  ext k
  rw [ArithmeticFunction.mul_apply, single_apply]
  by_cases hk : k = a * b ∧ k ≠ 0
  · rw [if_pos hk, Finset.sum_eq_single (a, b)]
    · rw [single_apply_self ha, single_apply_self hb]
    · intro x _ hx
      rw [single_apply, single_apply]
      by_cases h1 : x.1 = a ∧ x.1 ≠ 0
      · rw [if_pos h1, if_neg fun h2 => hx (Prod.ext h1.1 h2.1), mul_zero]
      · rw [if_neg h1, zero_mul]
    · intro h
      exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨hk.1.symm, hk.2⟩) h
  · rw [if_neg hk]
    refine Finset.sum_eq_zero fun x hx => ?_
    obtain ⟨hxk, hk0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    rw [single_apply, single_apply]
    by_cases h1 : x.1 = a ∧ x.1 ≠ 0
    · by_cases h2 : x.2 = b ∧ x.2 ≠ 0
      · exact absurd ⟨by rw [← hxk, h1.1, h2.1], hk0⟩ hk
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

theorem single_mem_truncIdeal {n : ℕ} (c : R) : single n c ∈ truncIdeal (n - 1) :=
  fun k h1 hk => by rw [single_apply, if_neg fun h => by omega]

/-! ### The kernel of the window representation -/

/-- **The window algebra is the truncated Dirichlet ring**: `ker ρ_A = I_{⌊e^A⌋}`. -/
theorem ker_windowRep (A : ℝ) : RingHom.ker (windowRep A) = truncIdeal (windowLevel A) := by
  ext f
  rw [RingHom.mem_ker, windowRep_eq_zero_iff, mem_truncIdeal]
  exact ⟨fun h n h1 hn => h n (Finset.mem_Icc.mpr ⟨h1, hn⟩),
    fun h n hn => h n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2⟩

theorem windowRep_eq_zero_of_mem {A : ℝ} {f : ArithmeticFunction ℝ}
    (hf : f ∈ truncIdeal (windowLevel A)) : windowRep A f = 0 := by
  rw [← RingHom.mem_ker, ker_windowRep]; exact hf

/-! ### One new fold per stage -/

/-- **The kernel of a transition is one-dimensional**: `f ∈ I_N` is `f(N+1)·δ_{N+1}` modulo
`I_{N+1}`. -/
theorem sub_single_mem_truncIdeal_succ {N : ℕ} {f : ArithmeticFunction R} (hf : f ∈ truncIdeal N) :
    f - single (N + 1) (f (N + 1)) ∈ truncIdeal (N + 1) := by
  intro n h1 hn
  rw [sub_apply', single_apply]
  rcases Nat.lt_or_ge n (N + 1) with h | h
  · rw [hf n h1 (by omega), if_neg fun h' => by omega, sub_zero]
  · rw [show n = N + 1 by omega, if_pos ⟨rfl, by omega⟩, sub_self]

/-- **The socle law**: `I_M · m ⊆ I_{2M+1}`. -/
theorem mul_mem_truncIdeal {M : ℕ} {f g : ArithmeticFunction R} (hf : f ∈ truncIdeal M)
    (hg : g ∈ truncIdeal 1) : f * g ∈ truncIdeal (2 * M + 1) := by
  intro n h1 hn
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero fun x hx => ?_
  obtain ⟨hxn, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have ha : 1 ≤ x.1 := Nat.pos_of_ne_zero fun h => hn0 (by rw [← hxn, h, zero_mul])
  have hb : 1 ≤ x.2 := Nat.pos_of_ne_zero fun h => hn0 (by rw [← hxn, h, mul_zero])
  rcases Nat.lt_or_ge x.2 2 with hb2 | hb2
  · rw [show x.2 = 1 by omega, mem_truncIdeal_one.mp hg, mul_zero]
  · rcases Nat.lt_or_ge M x.1 with ha' | ha'
    · have hprod : (M + 1) * 2 ≤ x.1 * x.2 := Nat.mul_le_mul ha' hb2
      rw [hxn] at hprod
      omega
    · rw [hf x.1 ha ha', zero_mul]

/-- **Each transition is a small extension**: the kernel `I_N/I_{N+1}` is killed by `m`. -/
theorem mul_mem_truncIdeal_succ {N : ℕ} {f g : ArithmeticFunction R} (hf : f ∈ truncIdeal N)
    (hg : g ∈ truncIdeal 1) : f * g ∈ truncIdeal (N + 1) :=
  truncIdeal_anti (by omega) (mul_mem_truncIdeal hf hg)

/-- **The new fold is a socle element**: on windows shorter than `log 2n` the fold `δ_n` composes
to zero with every element of the maximal ideal. -/
theorem windowRep_single_mul_eq_zero {A : ℝ} {n : ℕ} (hA : windowLevel A < 2 * n) (c : ℝ)
    {g : ArithmeticFunction ℝ} (hg : g ∈ truncIdeal 1) :
    windowRep A (single n c) * windowRep A g = 0 := by
  rw [← map_mul]
  refine windowRep_eq_zero_of_mem (truncIdeal_anti ?_ (mul_mem_truncIdeal
    (single_mem_truncIdeal (n := n) c) hg))
  omega

/-! ### Loewy length -/

/-- **Loewy law**: `m^{k+1} ⊆ I_{2^{k+1} − 1}`. -/
theorem pow_truncIdeal_one_le (k : ℕ) :
    (truncIdeal 1 : Ideal (ArithmeticFunction R)) ^ (k + 1) ≤ truncIdeal (2 ^ (k + 1) - 1) := by
  induction k with
  | zero => rw [zero_add, pow_one, pow_one]
  | succ k ih =>
    rw [pow_succ _ (k + 1)]
    refine Ideal.mul_le.mpr fun f hf g hg => ?_
    have h := mul_mem_truncIdeal (ih hf) hg
    have hk := Nat.one_le_two_pow (n := k + 1)
    have e : 2 * (2 ^ (k + 1) - 1) + 1 = 2 ^ (k + 1 + 1) - 1 := by rw [pow_succ 2 (k + 1)]; omega
    rwa [e] at h

/-- `δ_2^k = δ_{2^k}`. -/
theorem single_two_pow (k : ℕ) : single 2 (1 : R) ^ k = single (2 ^ k) 1 := by
  induction k with
  | zero =>
    ext n
    rw [pow_zero, ArithmeticFunction.one_apply, single_apply, pow_zero]
    by_cases h : n = 1 <;> simp [h]
  | succ k ih =>
    rw [pow_succ, ih, single_mul_single (by positivity) (by norm_num), mul_one, ← pow_succ]

/-- **The Loewy length is sharp**: `ρ_A` kills `m^k` (`k ≥ 1`) exactly when `⌊e^A⌋ < 2^k`. -/
theorem windowRep_kills_pow_iff {A : ℝ} {k : ℕ} (hk : 1 ≤ k) :
    (truncIdeal 1 : Ideal (ArithmeticFunction ℝ)) ^ k ≤ RingHom.ker (windowRep A) ↔
      windowLevel A < 2 ^ k := by
  rw [ker_windowRep]
  constructor
  · intro h
    by_contra hle
    have hmem : single 2 (1 : ℝ) ^ k ∈ (truncIdeal 1 : Ideal (ArithmeticFunction ℝ)) ^ k :=
      Ideal.pow_mem_pow (mem_truncIdeal_one.mpr (by rw [single_apply]; simp)) k
    have h0 := h hmem (2 ^ k) Nat.one_le_two_pow (not_lt.mp hle)
    rw [single_two_pow, single_apply_self (by positivity)] at h0
    exact one_ne_zero h0
  · intro h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact (pow_truncIdeal_one_le j).trans (truncIdeal_anti (by omega))

/-! ### The cotangent space is spanned by the primes -/

/-- Functions vanishing at `1` and at every prime form an ideal containing `m²`. -/
def primeVanishing : Ideal (ArithmeticFunction R) where
  carrier := {f | f 1 = 0 ∧ ∀ p : ℕ, p.Prime → f p = 0}
  add_mem' {f g} hf hg := ⟨by rw [ArithmeticFunction.add_apply, hf.1, hg.1, add_zero],
    fun p hp => by rw [ArithmeticFunction.add_apply, hf.2 p hp, hg.2 p hp, add_zero]⟩
  zero_mem' := ⟨rfl, fun _ _ => rfl⟩
  smul_mem' c f hf := by
    have hterm : ∀ n : ℕ, (n = 1 ∨ n.Prime) → (c * f) n = 0 := fun n hn => by
      rw [ArithmeticFunction.mul_apply]
      refine Finset.sum_eq_zero fun x hx => ?_
      obtain ⟨hxn, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
      have hdvd : x.2 ∣ n := ⟨x.1, by rw [← hxn, mul_comm]⟩
      rcases hn with rfl | hp
      · rw [Nat.eq_one_of_dvd_one hdvd, hf.1, mul_zero]
      · rcases hp.eq_one_or_self_of_dvd x.2 hdvd with h | h
        · rw [h, hf.1, mul_zero]
        · rw [h, hf.2 n hp, mul_zero]
    exact ⟨hterm 1 (Or.inl rfl), fun p hp => hterm p (Or.inr hp)⟩

theorem sq_truncIdeal_one_le_primeVanishing :
    (truncIdeal 1 : Ideal (ArithmeticFunction R)) ^ 2 ≤ primeVanishing := by
  rw [pow_two]
  refine Ideal.mul_le.mpr fun f hf g hg => ?_
  have hterm : ∀ n : ℕ, (n = 1 ∨ n.Prime) → (f * g) n = 0 := fun n hn => by
    rw [ArithmeticFunction.mul_apply]
    refine Finset.sum_eq_zero fun x hx => ?_
    obtain ⟨hxn, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have hdvd : x.1 ∣ n := ⟨x.2, hxn.symm⟩
    rcases hn with rfl | hp
    · rw [Nat.eq_one_of_dvd_one hdvd, mem_truncIdeal_one.mp hf, zero_mul]
    · rcases hp.eq_one_or_self_of_dvd x.1 hdvd with h | h
      · rw [h, mem_truncIdeal_one.mp hf, zero_mul]
      · have h2 : x.2 = 1 := by
          rw [h] at hxn
          exact (Nat.mul_eq_left hp.ne_zero).mp hxn
        rw [h2, mem_truncIdeal_one.mp hg, mul_zero]
  exact ⟨hterm 1 (Or.inl rfl), fun p hp => hterm p (Or.inr hp)⟩

/-- The restriction of `f` to a finite set of positive integers. -/
def restrictTo (C : Finset ℕ) (f : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun k => if k ∈ C ∧ k ≠ 0 then f k else 0, by simp⟩

theorem restrictTo_apply (C : Finset ℕ) (f : ArithmeticFunction R) (k : ℕ) :
    restrictTo C f k = if k ∈ C ∧ k ≠ 0 then f k else 0 := rfl

/-- A composite number `n ≥ 2` is a product of two integers `≥ 2`. -/
theorem exists_mul_of_not_prime {n : ℕ} (h2 : 2 ≤ n) (hn : ¬ n.Prime) :
    ∃ a b, 2 ≤ a ∧ 2 ≤ b ∧ a * b = n := by
  obtain ⟨a, b, ha, hb, hab⟩ := (Nat.not_prime_iff_exists_mul_eq h2).mp hn
  refine ⟨a, b, ?_, ?_, hab⟩
  · by_contra h
    interval_cases a <;> omega
  · by_contra h
    interval_cases b <;> omega

/-- Functions supported on composite numbers lie in `m²`. -/
theorem restrictTo_mem_sq {C : Finset ℕ} (hC : ∀ n ∈ C, 2 ≤ n ∧ ¬ n.Prime)
    (f : ArithmeticFunction R) : restrictTo C f ∈ (truncIdeal 1 : Ideal (ArithmeticFunction R)) ^ 2 := by
  induction C using Finset.induction_on with
  | empty =>
    have : restrictTo (∅ : Finset ℕ) f = 0 := by ext k; simp [restrictTo_apply]
    rw [this]; exact Submodule.zero_mem _
  | insert n C hnC ih =>
    have hn := hC n (Finset.mem_insert_self n C)
    have hsplit : restrictTo (insert n C) f = single n (f n) + restrictTo C f := by
      ext k
      rw [ArithmeticFunction.add_apply, restrictTo_apply, restrictTo_apply, single_apply]
      by_cases hk : k = n
      · subst hk
        simp [hnC, show k ≠ 0 by omega]
      · simp [hk]
    rw [hsplit]
    refine Submodule.add_mem _ ?_ (ih fun m hm => hC m (Finset.mem_insert_of_mem hm))
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_mul_of_not_prime hn.1 hn.2
    rw [← mul_one (f (a * b)), ← single_mul_single (by omega) (by omega), pow_two]
    refine Ideal.mul_mem_mul (mem_truncIdeal_one.mpr ?_) (mem_truncIdeal_one.mpr ?_) <;>
      rw [single_apply, if_neg fun h => by omega]

/-- **The cotangent space of the window algebra is spanned by the primes**: for `f ∈ m`,
`f ∈ m² + I_N` iff `f` vanishes at every prime `p ≤ N`. -/
theorem mem_sq_sup_truncIdeal_iff {N : ℕ} {f : ArithmeticFunction R} (hf1 : f 1 = 0) :
    f ∈ (truncIdeal 1 : Ideal (ArithmeticFunction R)) ^ 2 ⊔ truncIdeal N ↔
      ∀ p : ℕ, p.Prime → p ≤ N → f p = 0 := by
  constructor
  · intro h p hp hpN
    obtain ⟨g, hg, k, hk, rfl⟩ := Submodule.mem_sup.mp h
    rw [ArithmeticFunction.add_apply, (sq_truncIdeal_one_le_primeVanishing hg).2 p hp,
      hk p hp.one_lt.le hpN, add_zero]
  · intro h
    set C := (Finset.Icc 2 N).filter fun n => ¬ n.Prime
    have hC : ∀ n ∈ C, 2 ≤ n ∧ ¬ n.Prime := fun n hn => by
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      exact ⟨hn.1.1, hn.2⟩
    refine Submodule.mem_sup.mpr ⟨restrictTo C f, restrictTo_mem_sq hC f, f - restrictTo C f,
      fun n h1 hn => ?_, add_sub_cancel _ _⟩
    rw [sub_apply', restrictTo_apply]
    by_cases hnC : n ∈ C
    · rw [if_pos ⟨hnC, by omega⟩, sub_self]
    · rw [if_neg fun h' => hnC h'.1, sub_zero]
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · rw [show n = 1 by omega, hf1]
      · have hp : n.Prime := by
          by_contra hp
          exact hnC (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h2, hn⟩, hp⟩)
        exact h n hp hn

/-- The primes `≤ N` are independent in the cotangent space: a combination `Σ c_p δ_p` lies in
`m² + I_N` only if every coefficient vanishes. -/
theorem single_prime_not_mem {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N) {c : R} (hc : c ≠ 0) :
    single p c ∉ (truncIdeal 1 : Ideal (ArithmeticFunction R)) ^ 2 ⊔ truncIdeal N := by
  intro h
  have := (mem_sq_sup_truncIdeal_iff (by rw [single_apply, if_neg fun h => hp.one_lt.ne h.1])).mp
    h p hp hpN
  rw [single_apply_self hp.ne_zero] at this
  exact hc this

/-! ### The inverse limit -/

/-- **The tower separates points**: `⋂_N I_N = 0`. -/
theorem iInf_truncIdeal : ⨅ N, (truncIdeal N : Ideal (ArithmeticFunction R)) = ⊥ := by
  refine eq_bot_iff.mpr fun f hf => ?_
  rw [Submodule.mem_iInf] at hf
  rw [Submodule.mem_bot]
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact hf n n hn le_rfl

theorem sub_mem_truncIdeal_of_compatible (F : ℕ → ArithmeticFunction R)
    (hF : ∀ N, F (N + 1) - F N ∈ truncIdeal N) {n N : ℕ} (h : n ≤ N) :
    F N - F n ∈ truncIdeal n := by
  induction N, h using Nat.le_induction with
  | base => rw [sub_self]; exact Submodule.zero_mem _
  | succ N hnN ih =>
    have := Submodule.add_mem _ (truncIdeal_anti hnN (hF N)) ih
    rwa [sub_add_sub_cancel] at this

/-- **The inverse limit of the window algebras is the Dirichlet ring**: a compatible family of
classes `F_N mod I_N` has a unique arithmetic function as limit. -/
theorem existsUnique_limit (F : ℕ → ArithmeticFunction R)
    (hF : ∀ N, F (N + 1) - F N ∈ truncIdeal N) :
    ∃! f : ArithmeticFunction R, ∀ N, f - F N ∈ truncIdeal N := by
  refine ⟨⟨fun n => F n n, by simp⟩, fun N n h1 hn => ?_, fun g hg => ?_⟩
  · rw [sub_apply']
    change F n n - F N n = 0
    have := sub_mem_truncIdeal_of_compatible F hF hn n h1 le_rfl
    rw [sub_apply'] at this
    exact sub_eq_zero.mpr (sub_eq_zero.mp this).symm
  · ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h1 := hg n n hn le_rfl
      rw [sub_apply', sub_eq_zero] at h1
      exact h1
