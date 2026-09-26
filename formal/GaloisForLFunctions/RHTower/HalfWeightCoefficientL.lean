import GaloisForLFunctions.RHTower.HalfWeightKronecker

/-!
# The Fourier coefficients of the weight-½ Eisenstein series as `L`-function quotients

For `n ≠ 0` (trivial nebentypus, level `4M`), with `χ = kronChar` (`d ↦ (n/d)` mod `4|n|M`):

* `gL_eq_mul`: the restriction of `μ * N(n)` to multiples of `4M` is `(μ²χ) ⍟ e_L`, with `e_L` the
  `T`-factored part restricted to multiples of `4M` (where `μ²χ(a) ≠ 0`, `a` is prime to `4M`).
* `chiA_eq_mul`: `χ = (μ²χ) ⍟ (χ on squares)` (multiplicativity of `IsSquare` on coprime pairs,
  `isSquare_mul_of_coprime`; `IsSquare (p^k) ↔ Even k`); hence
  `LSeries_sqfChi`: `Σ μ(c)²χ(c) c^{-s} = L(s,χ)/L(2s,χ²)` for `Re s > 1`.
* `summable_eMaj`, `lseriesSummable_eL`: the `T`-factored part converges for `Re s > 0`
  (Euler product over `T`-factored numbers, local bound `‖e_T(p^a)‖ ≤ 16|n|` from `rootCard_le`).
* `LSeries_gL`: `Σ_{4M|c} (μ*N(n))(c) c^{-s} = L(s,χ)/L(2s,χ²) · Σ e_L(c) c^{-s}` for `Re s > 1`.
* `Dser_one_eq_LSeries`: `D_n(w) = i^{1/2}/√2 · LSeries g_L (2w - 1/2)` for every `w`.

The right-hand side of `LSeries_gL` continues to `Re s > 0` away from the zeros of `L(2s, χ²)`
(a principal character: `χ² = 1`), with a pole at `s = 1` only when `χ` is principal.
-/

open Complex ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RHTower.HalfWeight

section Constraint

variable {n : ℤ} {M : ℕ} (hn : n ≠ 0) (hM : 0 < M)

/-- The coefficient function restricted to multiples of `4M`. -/
noncomputable def gL : ArithmeticFunction ℂ :=
  ⟨fun c => if 4 * M ∣ c then fN n c else 0, by simp⟩

/-- `e_T` restricted to multiples of `4M`. -/
noncomputable def eL : ArithmeticFunction ℂ :=
  ⟨fun c => if 4 * M ∣ c then eT (n := n) (M := M) c else 0, by simp⟩

theorem gL_apply (c : ℕ) : gL (n := n) (M := M) c = if 4 * M ∣ c then fN n c else 0 := rfl

theorem eL_apply (c : ℕ) :
    eL (n := n) (M := M) c = if 4 * M ∣ c then eT (n := n) (M := M) c else 0 := rfl

theorem coprime_of_sqfChi_ne_zero {a : ℕ} (ha : sqfChi hn hM a ≠ 0) : a.Coprime (4 * M) := by
  haveI : NeZero (kmod n M) := ⟨(kmod_pos hn hM).ne'⟩
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  rw [sqfChi_apply, chiA_apply hn hM ha0] at ha
  have hk : kronChar hn hM (a : ZMod (kmod n M)) ≠ 0 := fun h => ha (by rw [h, mul_zero])
  have hu : IsUnit (a : ZMod (kmod n M)) := by
    by_contra hnu
    exact hk (by rw [kronChar_apply, if_neg hnu])
  have hc : a.Coprime (kmod n M) := (ZMod.isUnit_iff_coprime _ _).1 hu
  exact Nat.Coprime.coprime_dvd_right
    (by unfold kmod; exact ⟨n.natAbs, by ring⟩) hc

/-- **The constraint `4M ∣ c` passes to the `T`-factored part**: `g_L = (μ² χ) ⍟ e_L`. -/
theorem gL_eq_mul : gL (n := n) (M := M) = sqfChi hn hM * eL (n := n) (M := M) := by
  ext c
  rw [gL_apply, fN_eq_mul hn hM, mul_apply, mul_apply]
  rw [ite_eq_iff']
  constructor
  · intro hc
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [eL_apply]
    have hxc : x.1 * x.2 = c := (Nat.mem_divisorsAntidiagonal.1 hx).1
    by_cases hs : sqfChi hn hM x.1 = 0
    · simp [hs]
    · have hcop := coprime_of_sqfChi_ne_zero hn hM hs
      have hdvd : 4 * M ∣ x.2 := by
        rw [← hxc] at hc
        exact (Nat.Coprime.dvd_mul_left hcop.symm).1 hc
      rw [if_pos hdvd]
  · intro hc
    symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [eL_apply]
    have hxc : x.1 * x.2 = c := (Nat.mem_divisorsAntidiagonal.1 hx).1
    by_cases hdvd : 4 * M ∣ x.2
    · exact absurd (hxc ▸ dvd_mul_of_dvd_right hdvd x.1) hc
    · rw [if_neg hdvd, mul_zero]

end Constraint

/-! ### Squares -/

theorem isSquare_mul_of_coprime {a b : ℕ} (hab : a.Coprime b) :
    IsSquare (a * b) ↔ IsSquare a ∧ IsSquare b := by
  constructor
  · rintro ⟨m, hm⟩
    have hu : IsUnit (gcd a b) := by
      rw [show gcd a b = Nat.gcd a b from rfl, hab.gcd_eq_one]; exact isUnit_one
    have hu' : IsUnit (gcd b a) := by
      rw [show gcd b a = Nat.gcd b a from rfl, hab.symm.gcd_eq_one]; exact isUnit_one
    obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow hu (k := 2) (by rw [hm, pow_two])
    obtain ⟨e, he⟩ := exists_eq_pow_of_mul_eq_pow hu' (k := 2) (by rw [mul_comm, hm, pow_two])
    exact ⟨⟨d, by rw [hd, pow_two]⟩, ⟨e, by rw [he, pow_two]⟩⟩
  · rintro ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
    exact ⟨x * y, by ring⟩

theorem isSquare_prime_pow_iff {p : ℕ} (hp : p.Prime) (k : ℕ) : IsSquare (p ^ k) ↔ Even k := by
  constructor
  · rintro ⟨m, hm⟩
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hp.ne_zero hm.1
    have h := congrArg (fun t => t.factorization p) hm
    simp only [Nat.factorization_pow, Nat.factorization_mul hm0 hm0, Finsupp.smul_apply,
      Finsupp.add_apply, hp.factorization_self, smul_eq_mul, mul_one] at h
    exact ⟨m.factorization p, h⟩
  · rintro ⟨j, rfl⟩
    exact ⟨p ^ j, by ring⟩

section SquarePart

variable {n : ℤ} {M : ℕ} (hn : n ≠ 0) (hM : 0 < M)

open Classical in
/-- The character restricted to squares. -/
noncomputable def sqPart : ArithmeticFunction ℂ :=
  ⟨fun c => if IsSquare c then chiA hn hM c else 0, by simp [chiA]⟩

open Classical in
theorem sqPart_apply (c : ℕ) : sqPart hn hM c = if IsSquare c then chiA hn hM c else 0 := rfl

theorem isMultiplicative_sqPart : (sqPart hn hM).IsMultiplicative := by
  classical
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by rw [sqPart_apply, if_pos ⟨1, rfl⟩, (isMultiplicative_chiA hn hM).map_one],
    fun {a b} ha hb hab => ?_⟩
  rw [sqPart_apply, sqPart_apply, sqPart_apply]
  by_cases hA : IsSquare a
  · by_cases hB : IsSquare b
    · have hAB : IsSquare (a * b) := (isSquare_mul_of_coprime hab).2 ⟨hA, hB⟩
      simp only [hA, hB, hAB, if_true]
      exact (isMultiplicative_chiA hn hM).map_mul_of_coprime hab
    · have hAB : ¬ IsSquare (a * b) := fun h => hB ((isSquare_mul_of_coprime hab).1 h).2
      simp only [hAB, hB, if_false, mul_zero]
  · have hAB : ¬ IsSquare (a * b) := fun h => hA ((isSquare_mul_of_coprime hab).1 h).1
    simp only [hAB, hA, if_false, zero_mul]

theorem chiA_prime_pow {p : ℕ} (hp : p.Prime) (j : ℕ) :
    chiA hn hM (p ^ j) = (chiA hn hM p) ^ j := by
  rw [chiA_apply hn hM (pow_ne_zero _ hp.ne_zero), chiA_apply hn hM hp.ne_zero, Nat.cast_pow, map_pow]

/-- **`χ = (μ² χ) ⍟ (χ on squares)`**. -/
theorem chiA_eq_mul : chiA hn hM = sqfChi hn hM * sqPart hn hM := by
  classical
  have hmul := (isMultiplicative_sqfChi hn hM).mul (isMultiplicative_sqPart hn hM)
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (isMultiplicative_chiA hn hM) _ hmul).2 ?_
  intro p i hp
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [pow_zero, (isMultiplicative_chiA hn hM).map_one, hmul.map_one]
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => sqfChi hn hM a * sqPart hn hM b),
    Nat.sum_divisors_prime_pow hp]
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : ∀ j ∈ Finset.range k, sqfChi hn hM (p ^ (j + 1 + 1)) *
      sqPart hn hM (p ^ (k + 1) / p ^ (j + 1 + 1)) = 0 := by
    intro j _
    rw [sqfChi_apply, ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp
  rw [Finset.sum_eq_zero hz, zero_add]
  have hdiv : p ^ (k + 1) / p ^ (0 + 1) = p ^ k := by
    rw [zero_add, pow_one, pow_succ, Nat.mul_div_cancel _ hp.pos]
  rw [hdiv, pow_zero, Nat.div_one, (isMultiplicative_sqfChi hn hM).map_one, one_mul, zero_add,
    pow_one, sqfChi_apply, ArithmeticFunction.moebius_apply_prime hp, sqPart_apply, sqPart_apply,
    chiA_prime_pow hn hM hp, chiA_prime_pow hn hM hp]
  rcases Nat.even_or_odd k with he | ho
  · have h1 : IsSquare (p ^ k) := (isSquare_prime_pow_iff hp k).2 he
    have h2 : ¬ IsSquare (p ^ (k + 1)) := fun h =>
      Nat.not_even_iff_odd.2 he.add_one ((isSquare_prime_pow_iff hp _).1 h)
    simp only [h1, h2, if_true, if_false]
    push_cast; ring
  · have h1 : ¬ IsSquare (p ^ k) := fun h =>
      Nat.not_even_iff_odd.2 ho ((isSquare_prime_pow_iff hp _).1 h)
    have h2 : IsSquare (p ^ (k + 1)) := (isSquare_prime_pow_iff hp _).2 ho.add_one
    simp only [h1, h2, if_true, if_false]
    ring

end SquarePart

/-! ### The L-series of `μ² χ` -/

section LSeriesPart

variable {n : ℤ} {M : ℕ} (hn : n ≠ 0) (hM : 0 < M) [NeZero (kmod n M)]

omit [NeZero (kmod n M)] in
theorem norm_chiA_le (c : ℕ) : ‖chiA hn hM c‖ ≤ 1 := by
  by_cases hc : c = 0
  · simp [chiA, hc]
  · rw [chiA_apply hn hM hc]; exact DirichletCharacter.norm_le_one _ _

omit [NeZero (kmod n M)] in
theorem norm_sqfChi_le (c : ℕ) : ‖sqfChi hn hM c‖ ≤ 1 := by
  rw [sqfChi_apply, norm_mul, norm_pow]
  have h1 : ‖((μ c : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have h2 := norm_chiA_le hn hM c
  have h3 : ‖((μ c : ℤ) : ℂ)‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) h1
  nlinarith [norm_nonneg (chiA hn hM c), sq_nonneg ‖((μ c : ℤ) : ℂ)‖]

omit [NeZero (kmod n M)] in
theorem norm_sqPart_le (c : ℕ) : ‖sqPart hn hM c‖ ≤ 1 := by
  classical
  rw [sqPart_apply]
  split_ifs
  · exact norm_chiA_le hn hM c
  · simp

theorem lseriesSummable_of_norm_le_one {f : ℕ → ℂ} (hf : ∀ c, ‖f c‖ ≤ 1) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable f s :=
  LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨1, fun c _ => by simpa using hf c⟩

theorem LSeries_chiA {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun c => chiA hn hM c) s = DirichletCharacter.LFunction (kronChar hn hM) s := by
  rw [DirichletCharacter.LFunction_eq_LSeries _ hs]
  exact LSeries_congr (fun {c} hc => chiA_apply hn hM hc) s

theorem LSeries_sqPart {s : ℂ} (hs : 1 / 2 < s.re) :
    LSeries (fun c => sqPart hn hM c) s =
      DirichletCharacter.LFunction (kronChar hn hM ^ 2) (2 * s) := by
  classical
  rw [DirichletCharacter.LFunction_eq_LSeries _ (by simp; linarith)]
  unfold LSeries
  have hinj : Function.Injective (fun k : ℕ => k ^ 2) := Nat.pow_left_injective two_ne_zero
  have hsupp : Function.support (LSeries.term (fun c => sqPart hn hM c) s) ⊆
      Set.range (fun k : ℕ => k ^ 2) := by
    intro c hc
    rw [Function.mem_support, LSeries.term_def] at hc
    split_ifs at hc with hc0
    · exact absurd rfl hc
    · rw [sqPart_apply] at hc
      split_ifs at hc with hsq
      · obtain ⟨k, rfl⟩ := hsq; exact ⟨k, by ring⟩
      · simp at hc
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [LSeries.term_def]
  have hk0 : k ≠ 0 := hk.ne'
  rw [LSeries.term_of_ne_zero (pow_ne_zero 2 hk0), LSeries.term_of_ne_zero hk0, sqPart_apply,
    if_pos ⟨k, by ring⟩, chiA_apply hn hM (pow_ne_zero 2 hk0), MulChar.pow_apply' _ two_ne_zero,
    Nat.cast_pow, map_pow]
  congr 1
  rw [show (2 * s) = ((2 : ℕ) : ℂ) * s by norm_num, Complex.natCast_cpow_natCast_mul]
  push_cast; ring_nf

/-- **`Σ μ(c)² χ(c) c^{-s} = L(s, χ) / L(2s, χ²)`** for `Re s > 1`. -/
theorem LSeries_sqfChi {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun c => sqfChi hn hM c) s = DirichletCharacter.LFunction (kronChar hn hM) s /
      DirichletCharacter.LFunction (kronChar hn hM ^ 2) (2 * s) := by
  have h1 := lseriesSummable_of_norm_le_one (norm_sqfChi_le hn hM) hs
  have h2 := lseriesSummable_of_norm_le_one (norm_sqPart_le hn hM) hs
  have hmul := LSeries_mul' h1 h2
  rw [← chiA_eq_mul, LSeries_chiA hn hM hs, LSeries_sqPart hn hM (by linarith)] at hmul
  have hne : DirichletCharacter.LFunction (kronChar hn hM ^ 2) (2 * s) ≠ 0 := by
    apply DirichletCharacter.LFunction_ne_zero_of_one_le_re
    · right; intro h; have := congrArg Complex.re h; simp at this; linarith
    · simp; linarith
  rw [hmul, mul_div_assoc, div_self hne, mul_one]

end LSeriesPart

/-! ### The `T`-factored part converges for `Re s > 0` -/

section FactoredPart

variable {n : ℤ} {M : ℕ} (hn : n ≠ 0)

include hn in
theorem norm_sqCount_prime_pow_le {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ‖sqCount n (p ^ a)‖ ≤ 8 * n.natAbs := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [sqCount_eq_rootCard, Complex.norm_natCast]
  exact_mod_cast rootCard_le hn a

include hn in
theorem one_le_natAbs : (1 : ℝ) ≤ n.natAbs := by
  exact_mod_cast Int.natAbs_pos.2 hn

include hn in
theorem norm_eT_prime_pow_le {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ‖eT (n := n) (M := M) (p ^ a)‖ ≤ 16 * n.natAbs := by
  have h1 := one_le_natAbs hn
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [pow_zero, (isMultiplicative_eT (n := n) (M := M)).map_one, norm_one]; linarith
  rw [eT_apply]
  split_ifs
  · rw [fN, moebius_mul_prime_pow _ hp ha, Nfun_apply, Nfun_apply]
    refine (norm_sub_le _ _).trans ?_
    have := norm_sqCount_prime_pow_le hn hp a
    have := norm_sqCount_prime_pow_le hn hp (a - 1)
    linarith
  · simp

/-- The real multiplicative majorant `‖e_T(c)‖ c^{-σ}`. -/
noncomputable def eMaj (σ : ℝ) (c : ℕ) : ℝ := ‖eT (n := n) (M := M) c‖ * (c : ℝ) ^ (-σ)

include hn in
theorem summable_eMaj {σ : ℝ} (hσ : 0 < σ) : Summable (eMaj (n := n) (M := M) σ) := by
  have hmulT := isMultiplicative_eT (n := n) (M := M)
  have h1 : eMaj (n := n) (M := M) σ 1 = 1 := by
    simp [eMaj, hmulT.map_one]
  have hmul : ∀ {a b : ℕ}, a.Coprime b →
      eMaj (n := n) (M := M) σ (a * b) = eMaj (n := n) (M := M) σ a * eMaj (n := n) (M := M) σ b := by
    intro a b hab
    simp only [eMaj, hmulT.map_mul_of_coprime hab, norm_mul, Nat.cast_mul]
    rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  have hsum : ∀ {p : ℕ}, p.Prime → Summable fun a : ℕ => ‖eMaj (n := n) (M := M) σ (p ^ a)‖ := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    set r : ℝ := (p : ℝ) ^ (-σ)
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    refine Summable.of_nonneg_of_le (fun a => norm_nonneg _) (fun a => ?_)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left (16 * (n.natAbs : ℝ)))
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold eMaj; positivity), eMaj, Nat.cast_pow,
      ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm (a : ℝ) (-σ),
      Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_right (norm_eT_prime_pow_le hn hp a) (by positivity)
  have hfact := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum h1 hmul
    hsum (Tset (n := n) (M := M))).1
  have hsupp : ∀ c ∉ Nat.factoredNumbers (Tset (n := n) (M := M)), eMaj (n := n) (M := M) σ c = 0 := by
    intro c hc; simp [eMaj, eT_apply, hc]
  have h2 : Summable ((Nat.factoredNumbers (Tset (n := n) (M := M))).indicator
      (eMaj (n := n) (M := M) σ)) := by
    rw [← summable_subtype_iff_indicator]
    refine hfact.congr fun m => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold eMaj; positivity)]
    rfl
  refine h2.congr fun c => ?_
  by_cases hc : c ∈ Nat.factoredNumbers (Tset (n := n) (M := M))
  · rw [Set.indicator_of_mem hc]
  · rw [Set.indicator_of_notMem hc, hsupp c hc]

include hn in
theorem lseriesSummable_eL {s : ℂ} (hs : 0 < s.re) :
    LSeriesSummable (fun c => eL (n := n) (M := M) c) s := by
  have hm := summable_eMaj (n := n) (M := M) hn hs
  refine Summable.of_norm_bounded hm (fun c => ?_)
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp [LSeries.term_def, eMaj]
  rw [LSeries.term_of_ne_zero hc.ne', norm_div, Complex.norm_natCast_cpow_of_pos hc, eMaj,
    Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [eL_apply]
  split_ifs
  · exact le_rfl
  · simp

end FactoredPart

/-! ### The coefficient series as an `L`-function quotient -/

section Assembly

variable {n : ℤ} {M : ℕ} (hn : n ≠ 0) (hM : 0 < M) [NeZero (kmod n M)]

/-- **`Σ_{4M|c} (μ*N(n))(c) c^{-s} = L(s,χ)/L(2s,χ²) · Σ_{4M|c} e_T(c) c^{-s}`** for `Re s > 1`. -/
theorem LSeries_gL {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun c => gL (n := n) (M := M) c) s =
      DirichletCharacter.LFunction (kronChar hn hM) s /
        DirichletCharacter.LFunction (kronChar hn hM ^ 2) (2 * s) *
          LSeries (fun c => eL (n := n) (M := M) c) s := by
  rw [gL_eq_mul hn hM, LSeries_mul' (lseriesSummable_of_norm_le_one (norm_sqfChi_le hn hM) hs)
    (lseriesSummable_eL hn (by linarith)), LSeries_sqfChi hn hM hs]

omit [NeZero (kmod n M)] in
/-- The coefficient series of `Dser_one` is the `L`-series of `g_L` at `s = 2w - 1/2`. -/
theorem Dser_one_eq_LSeries [NeZero M] (w : ℂ) :
    Dser M (1 : DirichletCharacter ℂ (4 * M)) n w = I ^ (1 / 2 : ℂ) / Real.sqrt 2 *
      LSeries (fun c => gL (n := n) (M := M) c) (2 * w - 1 / 2) := by
  rw [Dser_one]
  congr 1
  unfold LSeries
  have hinj : Function.Injective (fun k : ℕ => k + 1) := fun a b h => by simpa using h
  have hsupp : Function.support (LSeries.term (fun c => gL (n := n) (M := M) c) (2 * w - 1 / 2)) ⊆
      Set.range (fun k : ℕ => k + 1) := by
    intro c hc
    rw [Function.mem_support, LSeries.term_def] at hc
    split_ifs at hc with hc0
    · exact absurd rfl hc
    · exact ⟨c - 1, by simp only; omega⟩
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr fun k => ?_
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero k), gL_apply, ← fN_apply]
  split_ifs with h4
  · have hk0 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    rw [show (1 / 2 - 2 * w : ℂ) = -(2 * w - 1 / 2) by ring, Complex.cpow_neg, div_eq_mul_inv]
    push_cast; ring
  · simp

end Assembly

end GaloisForLFunctions.RHTower.HalfWeight
