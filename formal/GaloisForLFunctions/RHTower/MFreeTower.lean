import GaloisForLFunctions.RHTower.MFreeLadder

/-!
# The telescoping m-free tower

The rungs of the `m`-free ladder compose.  The `m`-th power dilations form a multiplicative
semigroup (`mPart a ∘ mPart b = mPart (a*b)`), and the `m`-free indicators telescope
against their dilations: the Dirichlet convolution
`∏_{k<K} mPart (m^k) [·, m-free] = [·, m^K-free]` is the arithmetic statement that every
exponent has a unique base-`m` digit expansion with `K` digits exactly when it is below
`m^K`.  On L-series this telescopes `ζ(s)/ζ(ms) · ζ(ms)/ζ(m²s) ⋯ = ζ(s)/ζ(m^K s)`, and on
carriers it gives one `ζ(m^k z)⁻¹` limit on each nested half-plane `re z > 1/m^k`.

* `RHTower.mPart_mPart` — composition of dilations: `mPart a (mPart b f) = mPart (a*b) f`;
  `RHTower.mPart_one` is the identity rung.
* `RHTower.prod_mPart_mFreeIndicator` — the arithmetic telescope
  `∏_{k<K} mPart (m^k) [·, m-free] = [·, m^K-free]` (Dirichlet convolution product):
  base-`m` digit uniqueness at every prime power.
* `RHTower.prod_LSeries_mFreeIndicator_telescope` — the L-series telescope
  `∏_{k<K} L([·, m-free], m^k s) = ζ(s)/ζ(m^K s)` on `re s > 1`.
* `RHTower.tendsto_dpoly2_mPartMoebiusCoeff_pow` — the carrier tower: on the nested
  half-plane `re z > 1/m^k` the dilated Möbius carrier converges to `ζ(m^k z)⁻¹`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction LSeries Complex Filter
open scoped LSeries.notation Moebius ArithmeticFunction.zeta

/-! ## Composition of dilations -/

theorem mPart_one {R : Type*} [AddCommMonoid R] (f : ArithmeticFunction R) :
    mPart 1 f = f := by
  ext n
  conv_lhs => rw [show n = n ^ 1 from (pow_one n).symm]
  rw [mPart_apply_pow one_ne_zero]

/-- **Dilations compose:** the `a`-th power dilation of the `b`-th power dilation is the
`a·b`-th power dilation. -/
theorem mPart_mPart {R : Type*} [AddCommMonoid R] {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (f : ArithmeticFunction R) : mPart a (mPart b f) = mPart (a * b) f := by
  ext n
  by_cases h : ∃ j, j ^ (a * b) = n
  · obtain ⟨j, rfl⟩ := h
    rw [mPart_apply_pow (mul_ne_zero ha hb), show j ^ (a * b) = (j ^ b) ^ a by
      rw [← pow_mul, mul_comm], mPart_apply_pow ha, mPart_apply_pow hb]
  · rw [mPart_apply_of_forall_pow_ne _ _ (fun j hj => h ⟨j, hj⟩)]
    by_cases hc : ∃ c, c ^ a = n
    · obtain ⟨c, rfl⟩ := hc
      rw [mPart_apply_pow ha, mPart_apply_of_forall_pow_ne]
      intro d hd
      exact h ⟨d, by rw [show a * b = b * a from mul_comm a b, pow_mul, hd]⟩
    · rw [mPart_apply_of_forall_pow_ne _ _ (fun c hc' => hc ⟨c, hc'⟩)]

/-- The successor rung of the power tower: `mPart (m^(k+1)) = mPart (m^k) ∘ mPart m`. -/
theorem mPart_pow_succ {R : Type*} [AddCommMonoid R] {m : ℕ} (hm : m ≠ 0) (k : ℕ)
    (f : ArithmeticFunction R) :
    mPart (m ^ (k + 1)) f = mPart (m ^ k) (mPart m f) := by
  rw [mPart_mPart (pow_ne_zero k hm) hm, ← pow_succ]

/-! ## The arithmetic telescope -/

theorem mFreeIndicator_one : mFreeIndicator 1 = 1 := by
  ext n
  rw [mFreeIndicator_apply, ArithmeticFunction.one_apply]
  by_cases hn : n = 1
  · rw [if_pos (hn ▸ mFree_one one_ne_zero), if_pos hn]
  · rw [if_neg ?_, if_neg hn]
    intro hfree
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn
    exact hfree p hp (by rwa [pow_one])

/-- No `M`-th power hits a prime power whose exponent `M` does not divide. -/
theorem forall_pow_ne_prime_pow_of_not_dvd {p M l : ℕ} (hM : M ≠ 0) (hp : p.Prime)
    (h : ¬ M ∣ l) : ∀ k : ℕ, k ^ M ≠ p ^ l := by
  intro k hk
  have hkdvd : k ∣ p ^ l := hk ▸ dvd_pow_self k hM
  obtain ⟨t, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hkdvd
  rw [← pow_mul] at hk
  exact h ⟨t, (Nat.pow_right_injective hp.two_le hk).symm.trans (mul_comm t M)⟩

/-- The dilated `m`-free indicator at prime powers: value `1` exactly on exponents
`l = M·t` with digit `t < m`. -/
theorem mPart_mFreeIndicator_apply_prime_pow {M m p : ℕ} (hM : M ≠ 0) (hm : m ≠ 0)
    (hp : p.Prime) (l : ℕ) :
    mPart M (mFreeIndicator m) (p ^ l) = if M ∣ l ∧ l / M < m then 1 else 0 := by
  by_cases hdvd : M ∣ l
  · obtain ⟨t, rfl⟩ := hdvd
    rw [show p ^ (M * t) = (p ^ t) ^ M by rw [← pow_mul, mul_comm], mPart_apply_pow hM,
      mFreeIndicator_apply_prime_pow hm hp]
    have h1 : M ∣ M * t := ⟨t, rfl⟩
    have h2 : M * t / M = t := Nat.mul_div_cancel_left t (Nat.pos_of_ne_zero hM)
    simp [h1, h2]
  · rw [mPart_apply_of_forall_pow_ne _ _ (forall_pow_ne_prime_pow_of_not_dvd hM hp hdvd),
      if_neg fun hc => hdvd hc.1]

/-- One telescoping step: convolving the `m^K`-free indicator with the `m^K`-dilated
`m`-free indicator produces the `m^(K+1)`-free indicator.  At a prime power `p^i` this is
base-`m^K` division with remainder: `i = j + m^K·t` with `j < m^K` and digit `t < m`
exists (uniquely) exactly when `i < m^(K+1)`. -/
theorem mFreeIndicator_mul_mPart_mFreeIndicator {m : ℕ} (hm : m ≠ 0) (K : ℕ) :
    mFreeIndicator (m ^ K) * mPart (m ^ K) (mFreeIndicator m)
      = mFreeIndicator (m ^ (K + 1)) := by
  have hE : m ^ K ≠ 0 := pow_ne_zero K hm
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((isMultiplicative_mFreeIndicator hE).mul
      (isMultiplicative_mPart hE (isMultiplicative_mFreeIndicator hm)))
    _ (isMultiplicative_mFreeIndicator (pow_ne_zero (K + 1) hm))).mpr fun p i hp => ?_
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun d e => mFreeIndicator (m ^ K) d * mPart (m ^ K) (mFreeIndicator m) e),
    Nat.sum_divisors_prime_pow hp, mFreeIndicator_apply_prime_pow (pow_ne_zero (K + 1) hm) hp]
  have hEpos : 0 < m ^ K := Nat.pos_of_ne_zero hE
  have hpow : ∀ j ∈ Finset.range (i + 1),
      mFreeIndicator (m ^ K) (p ^ j) * mPart (m ^ K) (mFreeIndicator m) (p ^ i / p ^ j)
        = (if j < m ^ K then 1 else 0)
            * (if m ^ K ∣ (i - j) ∧ (i - j) / m ^ K < m then 1 else 0) := by
    intro j hj
    have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Nat.pow_div hji hp.pos, mFreeIndicator_apply_prime_pow hE hp,
      mPart_mFreeIndicator_apply_prime_pow hE hm hp]
  rw [Finset.sum_congr rfl hpow]
  rcases Nat.lt_or_ge i (m ^ (K + 1)) with hi | hi
  · rw [if_pos hi]
    have hdm := Nat.div_add_mod i (m ^ K)
    have hj₀i : i % m ^ K ≤ i := Nat.mod_le _ _
    have hdig : m ^ K ∣ i - i % m ^ K ∧ (i - i % m ^ K) / m ^ K < m := by
      have hsub : i - i % m ^ K = m ^ K * (i / m ^ K) := by omega
      refine ⟨⟨i / m ^ K, hsub⟩, ?_⟩
      rw [hsub, Nat.mul_div_cancel_left _ hEpos]
      rw [pow_succ] at hi
      exact (Nat.div_lt_iff_lt_mul hEpos).mpr (by rw [mul_comm]; exact hi)
    rw [Finset.sum_eq_single_of_mem (i % m ^ K)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj₀i)) (fun j hj hjne => ?_),
      if_pos (Nat.mod_lt _ hEpos), if_pos hdig, one_mul]
    have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    by_cases hjE : j < m ^ K
    · rw [if_pos hjE, one_mul, if_neg]
      rintro ⟨⟨t, ht⟩, -⟩
      refine hjne ?_
      have hit : i = j + m ^ K * t := by omega
      rw [hit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hjE]
    · rw [if_neg hjE, zero_mul]
  · rw [if_neg (by omega)]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    by_cases hjE : j < m ^ K
    · rw [if_pos hjE, one_mul, if_neg]
      rintro ⟨⟨t, ht⟩, htm⟩
      rw [ht, Nat.mul_div_cancel_left _ hEpos] at htm
      have hit : i = j + m ^ K * t := by omega
      have htm' : t + 1 ≤ m := htm
      have hmul : m ^ K * (t + 1) ≤ m ^ K * m := Nat.mul_le_mul_left _ htm'
      rw [Nat.mul_succ] at hmul
      rw [pow_succ] at hi
      omega
    · rw [if_neg hjE, zero_mul]

/-- **The arithmetic telescope.**  The Dirichlet convolution of the dilated `m`-free
indicators along the power tower is the `m^K`-free indicator:
`∏_{k<K} mPart (m^k) [·, m-free] = [·, m^K-free]` — unique base-`m` digit expansion of
every exponent below `m^K`. -/
theorem prod_mPart_mFreeIndicator {m : ℕ} (hm : m ≠ 0) (K : ℕ) :
    ∏ k ∈ Finset.range K, mPart (m ^ k) (mFreeIndicator m) = mFreeIndicator (m ^ K) := by
  induction K with
  | zero => simp [mFreeIndicator_one]
  | succ K ih =>
    rw [Finset.prod_range_succ, ih, mFreeIndicator_mul_mPart_mFreeIndicator hm K]

/-! ## The L-series telescope -/

/-- **The L-series telescope.**  The rungs of the `m`-free ladder multiply out over the
power tower: `∏_{k<K} L([·, m-free], m^k·s) = ζ(s)/ζ(m^K·s)` on `re s > 1`. -/
theorem prod_LSeries_mFreeIndicator_telescope {m : ℕ} (hm : m ≠ 0) {s : ℂ}
    (hs : 1 < s.re) (K : ℕ) :
    ∏ k ∈ Finset.range K, L ↗(mFreeIndicator m) (((m ^ k : ℕ) : ℂ) * s)
      = riemannZeta s / riemannZeta (((m ^ K : ℕ) : ℂ) * s) := by
  induction K with
  | zero =>
    rw [Finset.prod_range_zero, pow_zero]
    rw [show (((1 : ℕ) : ℂ)) * s = s by norm_num,
      div_self (riemannZeta_ne_zero_of_one_lt_re hs)]
  | succ K ih =>
    have hres : 1 < (((m ^ K : ℕ) : ℂ) * s).re :=
      one_lt_natCast_mul_re (pow_ne_zero K hm) (one_div_natCast_lt_re (pow_ne_zero K hm) hs)
    have hcast : (m : ℂ) * (((m ^ K : ℕ) : ℂ) * s) = ((m ^ (K + 1) : ℕ) : ℂ) * s := by
      push_cast [pow_succ]
      ring
    rw [Finset.prod_range_succ, ih, LSeries_mFree_eq_riemannZeta_div hm hres, hcast,
      div_mul_div_comm]
    rw [div_eq_div_iff (mul_ne_zero (riemannZeta_ne_zero_of_one_lt_re hres)
      (riemannZeta_ne_zero_of_one_lt_re ?_)) ?_]
    · ring
    · rw [show ((m ^ (K + 1) : ℕ) : ℂ) * s = (m : ℂ) * (((m ^ K : ℕ) : ℂ) * s) from
        hcast.symm]
      exact one_lt_natCast_mul_re hm (one_div_natCast_lt_re hm hres)
    · refine riemannZeta_ne_zero_of_one_lt_re ?_
      rw [show ((m ^ (K + 1) : ℕ) : ℂ) * s = (m : ℂ) * (((m ^ K : ℕ) : ℂ) * s) from
        hcast.symm]
      exact one_lt_natCast_mul_re hm (one_div_natCast_lt_re hm hres)

/-! ## The carrier tower on nested half-planes -/

/-- **The carrier tower.**  On the nested half-plane `re z > 1/m^k`, the `m^k`-dilated
Möbius carrier polynomials converge to `ζ(m^k·z)⁻¹` — one carrier limit per rung of the
tower. -/
theorem tendsto_dpoly2_mPartMoebiusCoeff_pow {m : ℕ} (hm : m ≠ 0) (k : ℕ) {z : ℂ}
    (hz : 1 / ((m ^ k : ℕ) : ℝ) < z.re) :
    Tendsto (fun N => dpoly2 (mPartMoebiusCoeff (m ^ k)) (Finset.Icc 1 N) z) atTop
      (nhds ((riemannZeta (((m ^ k : ℕ) : ℂ) * z))⁻¹)) :=
  tendsto_dpoly2_mPartMoebiusCoeff (pow_ne_zero k hm) hz

end RHTower
