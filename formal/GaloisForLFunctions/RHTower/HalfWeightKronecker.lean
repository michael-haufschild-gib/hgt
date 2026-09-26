import GaloisForLFunctions.RHTower.HalfWeightSquareRoots

/-!
# The Kronecker character and the Euler decomposition of the coefficient function

For `n ≠ 0` and `M ≥ 1`:

* `kronChar`: `d ↦ (n/d)` (Jacobi symbol) as a Dirichlet character modulo `4|n|M`; well defined by
  `jacobiSym.mod_right` (quadratic reciprocity), multiplicative by `jacobiSym.mul_right`.
  `kronChar_prime`: at odd primes `p ∤ nM` it is the Legendre symbol `(n/p)`;
  `kronChar_prime_of_dvd`: it vanishes at the primes of `T = primes(4|n|M)`.
* `fN = μ * N(n)` is multiplicative (`isMultiplicative_fN`, via `rootCard_mul`), with
  `fN_apply`: `fN n c = Σ_{e|c} μ(e) N_{c/e}(n)`.
* `fN_eq_mul`: **`μ * N(n) = (μ² χ) ⍟ e_T`**, where `e_T` is the restriction of `μ * N(n)` to
  `T`-factored numbers. Checked on prime powers: for `p ∈ T` only `e_T` contributes; for `p ∉ T`,
  `N_{p^a}(n) = 1 + (n/p)` gives `(μ * N)(p) = (n/p) = χ(p)` and `(μ * N)(p^a) = 0` for `a ≥ 2`.

Consequently `Σ_{4M|c} (μ*N(n))(c) c^{-s} = L(s,χ)/L(2s,χ²) · Σ_{c T-factored, 4M|c} e_T(c) c^{-s}`
(the second factor converges for `Re s > 0`).
-/

open Complex

namespace GaloisForLFunctions.RHTower.HalfWeight

/-! ### The Kronecker character `d ↦ (n/d)` modulo `4|n|M` -/

section Kronecker

variable (n : ℤ) (M : ℕ)

/-- The modulus `4|n|M`. -/
abbrev kmod : ℕ := 4 * n.natAbs * M

variable {n M}

theorem kmod_pos (hn : n ≠ 0) (hM : 0 < M) : 0 < kmod n M := by
  unfold kmod; positivity

theorem two_dvd_kmod : 2 ∣ kmod n M :=
  dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by norm_num) _) _

theorem four_natAbs_dvd_kmod : 4 * n.natAbs ∣ kmod n M := dvd_mul_right _ _

theorem odd_val_of_isUnit (hn : n ≠ 0) (hM : 0 < M) {x : ZMod (kmod n M)} (hx : IsUnit x) :
    Odd x.val := by
  haveI : NeZero (kmod n M) := ⟨(kmod_pos hn hM).ne'⟩
  have hc : x.val.Coprime (kmod n M) := by
    rw [← ZMod.natCast_zmod_val x] at hx
    exact (ZMod.isUnit_iff_coprime _ _).1 hx
  rw [Nat.odd_iff]
  have h2 : ¬ 2 ∣ x.val := fun h2 =>
    Nat.not_coprime_of_dvd_of_dvd (by norm_num) h2 two_dvd_kmod hc
  omega

theorem jac_periodic {b b' : ℕ} (hb : Odd b) (hb' : Odd b') (h : b % kmod n M = b' % kmod n M) :
    jacobiSym n b = jacobiSym n b' := by
  rw [jacobiSym.mod_right n hb, jacobiSym.mod_right n hb']
  congr 1
  rw [← Nat.mod_mod_of_dvd b four_natAbs_dvd_kmod, h, Nat.mod_mod_of_dvd b' four_natAbs_dvd_kmod]

open Classical in
/-- **The Kronecker character** `d ↦ (n/d)` as a Dirichlet character modulo `4|n|M`. -/
noncomputable def kronChar (hn : n ≠ 0) (hM : 0 < M) : DirichletCharacter ℂ (kmod n M) where
  toFun x := if IsUnit x then (jacobiSym n x.val : ℂ) else 0
  map_one' := by
    haveI : Fact (1 < kmod n M) := ⟨by unfold kmod; have := Int.natAbs_pos.2 hn; nlinarith⟩
    simp [ZMod.val_one, jacobiSym.one_right]
  map_mul' x y := by
    haveI : NeZero (kmod n M) := ⟨(kmod_pos hn hM).ne'⟩
    by_cases hx : IsUnit x
    · by_cases hy : IsUnit y
      · have hxy : IsUnit (x * y) := hx.mul hy
        simp only [hx, hy, hxy, if_true]
        have ox := odd_val_of_isUnit hn hM hx
        have oy := odd_val_of_isUnit hn hM hy
        have oxy := odd_val_of_isUnit hn hM hxy
        haveI : NeZero x.val := ⟨ox.pos.ne'⟩
        haveI : NeZero y.val := ⟨oy.pos.ne'⟩
        rw [← Int.cast_mul, ← jacobiSym.mul_right]
        congr 1
        apply jac_periodic oxy (ox.mul oy)
        rw [ZMod.val_mul, Nat.mod_mod]
      · have hxy : ¬ IsUnit (x * y) := fun h => hy (isUnit_of_mul_isUnit_right h)
        simp [hx, hy, hxy]
    · have hxy : ¬ IsUnit (x * y) := fun h => hx (isUnit_of_mul_isUnit_left h)
      simp [hx, hxy]
  map_nonunit' x hx := by simp [hx]

open Classical in
theorem kronChar_apply (hn : n ≠ 0) (hM : 0 < M) (x : ZMod (kmod n M)) :
    kronChar hn hM x = if IsUnit x then (jacobiSym n x.val : ℂ) else 0 := rfl

/-- At an odd prime `p ∤ nM`, the Kronecker character is the Legendre symbol `(n/p)`. -/
theorem kronChar_prime (hn : n ≠ 0) (hM : 0 < M) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hpn : ¬ (p : ℤ) ∣ n) (hpM : ¬ p ∣ M) :
    kronChar hn hM (p : ZMod (kmod n M)) = (legendreSym p n : ℂ) := by
  haveI : NeZero (kmod n M) := ⟨(kmod_pos hn hM).ne'⟩
  have hcop : p.Coprime (kmod n M) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp.out]
    intro h
    unfold kmod at h
    rcases (Nat.Prime.dvd_mul hp.out).1 h with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp.out).1 h1 with h2 | h2
      · have : p ∣ 2 ^ 2 := by norm_num at h2 ⊢; exact h2
        have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow this)
        exact hp2 this
      · exact hpn (Int.natCast_dvd.2 h2)
    · exact hpM h1
  have hu : IsUnit (p : ZMod (kmod n M)) := (ZMod.isUnit_iff_coprime _ _).2 hcop
  rw [kronChar_apply, if_pos hu, ZMod.val_natCast, jacobiSym.legendreSym.to_jacobiSym]
  have hpo : Odd p := hp.out.odd_of_ne_two hp2
  congr 1
  exact (jac_periodic (hpo.mod_even (by
    have := (two_dvd_kmod (n := n) (M := M)); exact even_iff_two_dvd.2 this)) hpo (Nat.mod_mod _ _))

/-- The Kronecker character vanishes at primes dividing `2nM`. -/
theorem kronChar_prime_of_dvd (hn : n ≠ 0) (hM : 0 < M) {p : ℕ} [hp : Fact p.Prime]
    (hpd : p ∣ kmod n M) : kronChar hn hM (p : ZMod (kmod n M)) = 0 := by
  haveI : NeZero (kmod n M) := ⟨(kmod_pos hn hM).ne'⟩
  have hnu : ¬ IsUnit (p : ZMod (kmod n M)) := by
    rw [ZMod.isUnit_iff_coprime]
    intro h
    exact hp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h hpd)
  rw [kronChar_apply, if_neg hnu]

end Kronecker

/-! ### The coefficient function as a Dirichlet convolution -/

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

section Decomposition

/-- `N(n)` as an arithmetic function. -/
noncomputable def Nfun (n : ℤ) : ArithmeticFunction ℂ := ⟨fun c => sqCount n c, by simp [sqCount]⟩

theorem Nfun_apply (n : ℤ) (c : ℕ) : Nfun n c = sqCount n c := rfl

theorem sqCount_one (n : ℤ) : sqCount n 1 = 1 := by simp [sqCount]

theorem isMultiplicative_Nfun (n : ℤ) : (Nfun n).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by rw [Nfun_apply, sqCount_one], fun {a b} ha hb hab => ?_⟩
  haveI : NeZero a := ⟨ha⟩
  haveI : NeZero b := ⟨hb⟩
  haveI : NeZero (a * b) := ⟨mul_ne_zero ha hb⟩
  simp only [Nfun_apply, sqCount_eq_rootCard]
  rw [rootCard_mul hab]
  push_cast; ring

/-- `f = μ * N(n)`, the coefficient function of `Dser_one`. -/
noncomputable def fN (n : ℤ) : ArithmeticFunction ℂ := (μ : ArithmeticFunction ℂ) * Nfun n

theorem isMultiplicative_fN (n : ℤ) : (fN n).IsMultiplicative :=
  isMultiplicative_moebius.intCast.mul (isMultiplicative_Nfun n)

theorem fN_apply (n : ℤ) (c : ℕ) : fN n c = muN n c := by
  unfold fN muN
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => (μ : ArithmeticFunction ℂ) a * Nfun n b)]
  simp [intCoe_apply, Nfun_apply]

/-- `(μ * g)(p^i) = g(p^i) - g(p^{i-1})` for `i ≥ 1`. -/
theorem moebius_mul_prime_pow (g : ArithmeticFunction ℂ) {p : ℕ} (hp : p.Prime) {i : ℕ}
    (hi : 1 ≤ i) : ((μ : ArithmeticFunction ℂ) * g) (p ^ i) = g (p ^ i) - g (p ^ (i - 1)) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => (μ : ArithmeticFunction ℂ) a * g b),
    Nat.sum_divisors_prime_pow hp]
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : ∀ j ∈ Finset.range k, (μ : ArithmeticFunction ℂ) (p ^ (j + 1 + 1)) *
      g (p ^ (k + 1) / p ^ (j + 1 + 1)) = 0 := by
    intro j _
    rw [intCoe_apply, moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp
  rw [Finset.sum_eq_zero hz]
  simp only [intCoe_apply, pow_zero, pow_one, moebius_apply_one, moebius_apply_prime hp,
    Int.cast_one, Int.cast_neg, one_mul, neg_one_mul, zero_add, Nat.div_one]
  rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
  simp only [Nat.add_sub_cancel]
  ring

end Decomposition

section Decomposition2

variable {n : ℤ} {M : ℕ} (hn : n ≠ 0) (hM : 0 < M)

/-- The Kronecker character as an arithmetic function. -/
noncomputable def chiA : ArithmeticFunction ℂ :=
  ⟨fun c => if c = 0 then 0 else kronChar hn hM (c : ZMod (kmod n M)), by simp⟩

theorem chiA_apply {c : ℕ} (hc : c ≠ 0) : chiA hn hM c = kronChar hn hM (c : ZMod (kmod n M)) := by
  simp [chiA, hc]

theorem isMultiplicative_chiA : (chiA hn hM).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by rw [chiA_apply hn hM one_ne_zero]; simp, fun {a b} ha hb _ => ?_⟩
  rw [chiA_apply hn hM (mul_ne_zero ha hb), chiA_apply hn hM ha, chiA_apply hn hM hb, Nat.cast_mul,
    map_mul]

/-- `μ² χ`, supported on square-free numbers coprime to `2nM`. -/
noncomputable def sqfChi : ArithmeticFunction ℂ :=
  ((μ : ArithmeticFunction ℂ).pmul (μ : ArithmeticFunction ℂ)).pmul (chiA hn hM)

theorem isMultiplicative_sqfChi : (sqfChi hn hM).IsMultiplicative :=
  (isMultiplicative_moebius.intCast.pmul isMultiplicative_moebius.intCast).pmul
    (isMultiplicative_chiA hn hM)

/-- The primes dividing `4|n|M`. -/
noncomputable def Tset : Finset ℕ := (kmod n M).primeFactors

/-- The `T`-factored part of `f = μ * N(n)`. -/
noncomputable def eT : ArithmeticFunction ℂ :=
  ⟨fun c => if c ∈ Nat.factoredNumbers (Tset (n := n) (M := M)) then fN n c else 0, by
    simp [Nat.mem_factoredNumbers]⟩

theorem eT_apply (c : ℕ) :
    eT (n := n) (M := M) c = if c ∈ Nat.factoredNumbers (Tset (n := n) (M := M)) then fN n c else 0 :=
  rfl

theorem isMultiplicative_eT : (eT (n := n) (M := M)).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  have h1 : 1 ∈ Nat.factoredNumbers (Tset (n := n) (M := M)) := by
    simp [Nat.mem_factoredNumbers]
  refine ⟨by rw [eT_apply, if_pos h1, (isMultiplicative_fN n).map_one], fun {a b} ha hb hab => ?_⟩
  rw [eT_apply, eT_apply, eT_apply]
  by_cases hA : a ∈ Nat.factoredNumbers (Tset (n := n) (M := M))
  · by_cases hB : b ∈ Nat.factoredNumbers (Tset (n := n) (M := M))
    · rw [if_pos (Nat.mul_mem_factoredNumbers hA hB), if_pos hA, if_pos hB,
        (isMultiplicative_fN n).map_mul_of_coprime hab]
    · rw [if_neg (fun h => hB (Nat.mem_factoredNumbers_of_dvd h (dvd_mul_left b a))), if_neg hB,
        mul_zero]
  · rw [if_neg (fun h => hA (Nat.mem_factoredNumbers_of_dvd h (dvd_mul_right a b))), if_neg hA,
      zero_mul]

theorem prime_pow_mem_factoredNumbers_iff {p : ℕ} (hp : p.Prime) {i : ℕ} (hi : 1 ≤ i) :
    p ^ i ∈ Nat.factoredNumbers (Tset (n := n) (M := M)) ↔ p ∈ Tset (n := n) (M := M) := by
  rw [Nat.mem_factoredNumbers']
  constructor
  · intro h; exact h p hp (dvd_pow_self p (by omega))
  · intro h q hq hqd
    rw [(Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hqd)]
    exact h

end Decomposition2

section Decomposition3

variable {n : ℤ} {M : ℕ} (hn : n ≠ 0) (hM : 0 < M)

theorem sqfChi_apply (c : ℕ) :
    sqfChi hn hM c = ((μ c : ℤ) : ℂ) ^ 2 * chiA hn hM c := by
  simp [sqfChi, pmul_apply, intCoe_apply, pow_two]

include hn hM in
theorem mem_Tset_iff {p : ℕ} (hp : p.Prime) :
    p ∈ Tset (n := n) (M := M) ↔ p ∣ kmod n M := by
  rw [Tset, Nat.mem_primeFactors]
  exact ⟨fun h => h.2.1, fun h => ⟨hp, h, (kmod_pos hn hM).ne'⟩⟩

theorem sqfChi_prime_pow_of_mem {p : ℕ} (hp : p.Prime) (hpT : p ∈ Tset (n := n) (M := M)) {j : ℕ}
    (hj : 1 ≤ j) : sqfChi hn hM (p ^ j) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hk : kronChar hn hM ((p ^ j : ℕ) : ZMod (kmod n M)) = 0 := by
    rw [Nat.cast_pow, map_pow, kronChar_prime_of_dvd hn hM ((mem_Tset_iff hn hM hp).1 hpT),
      zero_pow (by omega)]
  rw [sqfChi_apply, chiA_apply hn hM (pow_ne_zero _ hp.ne_zero), hk, mul_zero]

/-- **The Euler decomposition**: `μ * N(n) = (μ² χ) ⍟ e_T`. -/
theorem fN_eq_mul : fN n = sqfChi hn hM * eT (n := n) (M := M) := by
  have hmul := (isMultiplicative_sqfChi hn hM).mul (isMultiplicative_eT (n := n) (M := M))
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers (fN n) (isMultiplicative_fN n) _ hmul).2 ?_
  intro p i hp
  haveI : Fact p.Prime := ⟨hp⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [pow_zero, (isMultiplicative_fN n).map_one, hmul.map_one]
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => sqfChi hn hM a * eT (n := n) (M := M) b),
    Nat.sum_divisors_prime_pow hp]
  by_cases hpT : p ∈ Tset (n := n) (M := M)
  · rw [Finset.sum_range_succ']
    have hz : ∀ j ∈ Finset.range i, sqfChi hn hM (p ^ (j + 1)) *
        eT (n := n) (M := M) (p ^ i / p ^ (j + 1)) = 0 := by
      intro j _; rw [sqfChi_prime_pow_of_mem hn hM hp hpT (by omega), zero_mul]
    rw [Finset.sum_eq_zero hz, zero_add, pow_zero, (isMultiplicative_sqfChi hn hM).map_one, one_mul,
      Nat.div_one, eT_apply, if_pos ((prime_pow_mem_factoredNumbers_iff hp hi).2 hpT)]
  · rw [Finset.sum_range_succ]
    have hz : ∀ j ∈ Finset.range i, sqfChi hn hM (p ^ j) *
        eT (n := n) (M := M) (p ^ i / p ^ j) = 0 := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [Nat.pow_div hj.le hp.pos, eT_apply,
        if_neg (fun h => hpT ((prime_pow_mem_factoredNumbers_iff hp (by omega)).1 h)), mul_zero]
    rw [Finset.sum_eq_zero hz, zero_add, Nat.div_self (pow_pos hp.pos i),
      (isMultiplicative_eT (n := n) (M := M)).map_one, mul_one]
    -- the prime `p` is odd and prime to `nM`
    have hpk : ¬ p ∣ kmod n M := fun h => hpT ((mem_Tset_iff hn hM hp).2 h)
    have hp2 : p ≠ 2 := by rintro rfl; exact hpk two_dvd_kmod
    have hpn : ¬ (p : ℤ) ∣ n := by
      intro h; apply hpk
      have : p ∣ n.natAbs := Int.natCast_dvd.1 h
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right this 4) M
    have hpM : ¬ p ∣ M := fun h => hpk (dvd_mul_of_dvd_right h _)
    have hN : ∀ a : ℕ, 1 ≤ a → sqCount n (p ^ a) = (legendreSym p n : ℂ) + 1 := by
      intro a ha
      haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
      rw [sqCount_eq_rootCard]
      have := rootCard_prime_pow hp2 ha hpn
      exact_mod_cast this
    have hk : kronChar hn hM ((p ^ i : ℕ) : ZMod (kmod n M)) = (legendreSym p n : ℂ) ^ i := by
      rw [Nat.cast_pow, map_pow, kronChar_prime hn hM hp2 hpn hpM]
    rw [fN, moebius_mul_prime_pow _ hp hi, Nfun_apply, Nfun_apply, sqfChi_apply,
      chiA_apply hn hM (pow_ne_zero _ hp.ne_zero), hk]
    rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · obtain rfl : i = 1 := by omega
      rw [hN 1 le_rfl, pow_zero, sqCount_one, pow_one, pow_one,
        ArithmeticFunction.moebius_apply_prime hp]
      push_cast; ring
    · rw [hN i hi, hN (i - 1) (by omega), ArithmeticFunction.moebius_apply_prime_pow hp (by omega),
        if_neg (by omega)]
      push_cast; ring

end Decomposition3

end GaloisForLFunctions.RHTower.HalfWeight
