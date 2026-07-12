import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import GaloisForLFunctions.RHTower.Mollifier
import GaloisForLFunctions.RHTower.DpolyOffline

/-!
# The m-free Möbius ladder and the off-line carrier bridge

The square dilation of `SquarefreeMoebiusNormalization` is the `m = 2` rung of a full
ladder.  The `m`-th power dilation `mPart m f` (value `f k` at `n = k^m`, zero off `m`-th
powers) satisfies the same reindexing law `L(mPart m f, s) = L(f, ms)`, and normalizes the
`m`-free indicator against the zeta function:

* `RHTower.mPart` — the `m`-th power dilation; `RHTower.mPart_two_eq_sqrtPart` identifies
  the `m = 2` rung with the square dilation.  Dilation preserves multiplicativity
  (`RHTower.isMultiplicative_mPart`), because coprime factors of an `m`-th power are
  `m`-th powers.
* `RHTower.mPart_moebius_mul_zeta` — the arithmetic normalization
  `mPart m μ ⍟ ζ = [·, m-free]`, equivalently `∑_{d^m ∣ n} μ(d) = [n is m-free]`
  (`RHTower.sum_divisors_mPart_moebius`), where `RHTower.MFree m n` means no `m`-th prime
  power divides `n`.
* `RHTower.LSeries_mPart` — the dilation law `L(mPart m f, s) = L(f, ms)`, with two-way
  summability transfer `RHTower.LSeriesSummable_mPart_iff`.  The dilated Möbius series
  converges on `re s > 1/m` and represents `ζ(ms)⁻¹` there
  (`RHTower.LSeries_mPart_moebius`).
* `RHTower.tsum_mFree_cpow` — the ladder `∑' n, [n is m-free]/n^s = ζ(s)/ζ(ms)` on
  `re s > 1`, with product form `RHTower.LSeries_mFree_mul_riemannZeta` and quotient form
  `RHTower.LSeries_mFree_eq_riemannZeta_div`.

The final section makes these limits native to the carrier machinery: for any real
coefficient sequence with a summable L-series, the off-line carrier polynomials
`dpoly2 a (Icc 1 N) z` converge to the L-series value
(`RHTower.tendsto_dpoly2_Icc_of_LSeriesSummable`).  Instantiated:

* `RHTower.tendsto_dpoly2_moebiusCoeff` — the Möbius mollifier coefficients converge to
  `ζ(z)⁻¹` on `re z > 1`;
* `RHTower.tendsto_dpoly2_sqrtMoebiusCoeff` — the square-dilated Möbius coefficients
  converge to `ζ(2z)⁻¹` on the half-plane `re z > 1/2`, exhibiting `ζ(2z)⁻¹` as a
  critical-strip-adjacent limit of carrier polynomials with mollifier-grade coefficients
  (`RHTower.abs_sqrtMoebiusCoeff_le_one`), whose second moment is a Montgomery–Vaughan
  mean value (`RHTower.sqrtMollifier_secondMoment`);
* `RHTower.tendsto_dpoly2_mPartMoebiusCoeff` — the general rung: `ζ(mz)⁻¹` on
  `re z > 1/m`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction LSeries Complex Filter
open scoped LSeries.notation Moebius ArithmeticFunction.zeta

/-! ## The m-th power dilation of an arithmetic function -/

/-- The `m`-th power dilation of an arithmetic function: `mPart m f` takes the value `f k`
at `n = k^m` and vanishes off `m`-th powers.  On Dirichlet series this multiplies the
variable by `m`: `L(mPart m f, s) = L(f, ms)`.  For `m = 2` this is the square dilation
`sqrtPart`. -/
def mPart {R : Type*} [AddCommMonoid R] (m : ℕ) (f : ArithmeticFunction R) :
    ArithmeticFunction R :=
  ⟨fun n => ∑ k ∈ Finset.range (n + 1), if k ^ m = n ∧ k ≠ 0 then f k else 0, by simp⟩

theorem mPart_apply {R : Type*} [AddCommMonoid R] (m : ℕ) (f : ArithmeticFunction R)
    (n : ℕ) :
    mPart m f n = ∑ k ∈ Finset.range (n + 1), if k ^ m = n ∧ k ≠ 0 then f k else 0 := rfl

@[simp] theorem mPart_apply_pow {R : Type*} [AddCommMonoid R] {m : ℕ} (hm : m ≠ 0)
    (f : ArithmeticFunction R) (k : ℕ) : mPart m f (k ^ m) = f k := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [zero_pow hm]
    show (∑ j ∈ Finset.range (0 + 1), if j ^ m = 0 ∧ j ≠ 0 then f j else 0) = f 0
    simp [ArithmeticFunction.map_zero]
  · show (∑ j ∈ Finset.range (k ^ m + 1), if j ^ m = k ^ m ∧ j ≠ 0 then f j else 0) = f k
    rw [Finset.sum_eq_single_of_mem k
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_self_pow hm k)))]
    · rw [if_pos ⟨rfl, hk⟩]
    · intro b _ hbk
      rw [if_neg]
      rintro ⟨hb, -⟩
      exact hbk (Nat.pow_left_injective hm hb)

theorem mPart_apply_of_forall_pow_ne {R : Type*} [AddCommMonoid R] (m : ℕ)
    (f : ArithmeticFunction R) {n : ℕ} (h : ∀ k, k ^ m ≠ n) : mPart m f n = 0 := by
  rw [mPart_apply]
  exact Finset.sum_eq_zero fun k _ => if_neg fun hk => h k hk.1

/-- The `m = 2` rung of the dilation ladder is the square dilation. -/
theorem mPart_two_eq_sqrtPart {R : Type*} [AddCommMonoid R] (f : ArithmeticFunction R) :
    mPart 2 f = sqrtPart f := by
  ext n
  by_cases h : IsSquare n
  · obtain ⟨r, rfl⟩ := h
    rw [show r * r = r ^ 2 by rw [pow_two], mPart_apply_pow two_ne_zero,
      sqrtPart_apply_sq]
  · rw [sqrtPart_apply_of_not_isSquare f h, mPart_apply_of_forall_pow_ne]
    intro k hk
    exact h ⟨k, by rw [← hk, pow_two]⟩

/-- Coprime factors of an `m`-th power are `m`-th powers. -/
theorem exists_pow_and_pow_of_coprime_mul_pow {a b c m : ℕ} (hab : Nat.Coprime a b)
    (h : a * b = c ^ m) : (∃ d, d ^ m = a) ∧ (∃ e, e ^ m = b) := by
  obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hab) h
  obtain ⟨e, he⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hab.symm)
    (mul_comm a b ▸ h)
  exact ⟨⟨d, hd.symm⟩, ⟨e, he.symm⟩⟩

/-- The `m`-th power dilation preserves multiplicativity. -/
theorem isMultiplicative_mPart {R : Type*} [CommSemiring R] {m : ℕ} (hm : m ≠ 0)
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative) : (mPart m f).IsMultiplicative := by
  refine ⟨?_, fun {a b} hab => ?_⟩
  · rw [show (1 : ℕ) = 1 ^ m by rw [one_pow], mPart_apply_pow hm]
    exact hf.map_one
  · by_cases ha : ∃ d : ℕ, d ^ m = a
    · by_cases hb : ∃ e : ℕ, e ^ m = b
      · obtain ⟨d, rfl⟩ := ha
        obtain ⟨e, rfl⟩ := hb
        have hde : Nat.Coprime d e :=
          (hab.coprime_dvd_left (dvd_pow_self d hm)).coprime_dvd_right (dvd_pow_self e hm)
        rw [← mul_pow, mPart_apply_pow hm, mPart_apply_pow hm, mPart_apply_pow hm]
        exact hf.map_mul_of_coprime hde
      · rw [mPart_apply_of_forall_pow_ne m f (fun k hk => hb ⟨k, hk⟩), mul_zero,
          mPart_apply_of_forall_pow_ne]
        intro c hc
        exact hb (exists_pow_and_pow_of_coprime_mul_pow hab hc.symm).2
    · rw [mPart_apply_of_forall_pow_ne m f (fun k hk => ha ⟨k, hk⟩), zero_mul,
        mPart_apply_of_forall_pow_ne]
      intro c hc
      exact ha (exists_pow_and_pow_of_coprime_mul_pow hab hc.symm).1

/-- The `m`-th power dilation commutes with coefficient casting from `ℤ`. -/
theorem mPart_intCoe (m : ℕ) (f : ArithmeticFunction ℤ) :
    ((mPart m f : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) =
      mPart m (f : ArithmeticFunction ℂ) := by
  ext n
  simp only [intCoe_apply, mPart_apply, Int.cast_sum, apply_ite (Int.cast : ℤ → ℂ),
    Int.cast_zero]

/-! ## The m-free indicator and the arithmetic normalization law -/

/-- `n` is `m`-free if no `m`-th power of a prime divides it.  For `m = 2` this is
squarefreeness. -/
def MFree (m n : ℕ) : Prop := ∀ p : ℕ, p.Prime → ¬ p ^ m ∣ n

theorem not_mFree_zero (m : ℕ) : ¬ MFree m 0 :=
  fun h => h 2 Nat.prime_two (dvd_zero _)

theorem mFree_one {m : ℕ} (hm : m ≠ 0) : MFree m 1 := by
  intro p hp hdvd
  exact hp.ne_one (Nat.dvd_one.mp (dvd_trans (dvd_pow_self p hm) hdvd))

theorem mFree_two_iff_squarefree (n : ℕ) : MFree 2 n ↔ Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  constructor
  · intro h x hx hdvd
    exact h x hx (by rwa [pow_two])
  · intro h p hp hdvd
    exact h p hp (by rwa [← pow_two])

/-- On coprime factors, `m`-freeness splits. -/
theorem mFree_mul_iff {m a b : ℕ} (hab : Nat.Coprime a b) :
    MFree m (a * b) ↔ MFree m a ∧ MFree m b := by
  constructor
  · intro h
    exact ⟨fun p hp hdvd => h p hp (hdvd.mul_right b),
      fun p hp hdvd => h p hp (hdvd.mul_left a)⟩
  · rintro ⟨ha, hb⟩ p hp hdvd
    by_cases hpa : p ∣ a
    · have hpb : ¬ p ∣ b := fun hpb =>
        hp.ne_one ((hab.coprime_dvd_left hpa).eq_one_of_dvd hpb)
      exact ha p hp (hp.prime.pow_dvd_of_dvd_mul_right m hpb hdvd)
    · exact hb p hp (hp.prime.pow_dvd_of_dvd_mul_left m hpa hdvd)

open scoped Classical in
/-- The `m`-free indicator as an arithmetic function. -/
noncomputable def mFreeIndicator (m : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if MFree m n then 1 else 0, if_neg (not_mFree_zero m)⟩

open scoped Classical in
theorem mFreeIndicator_apply (m n : ℕ) :
    mFreeIndicator m n = if MFree m n then 1 else 0 := rfl

/-- For `m = 2` the `m`-free indicator is the pointwise Möbius square. -/
theorem mFreeIndicator_two : mFreeIndicator 2 = pmul (μ : ArithmeticFunction ℤ) μ := by
  ext n
  rw [mFreeIndicator_apply, pmul_apply, ← pow_two, moebius_sq]
  simp only [mFree_two_iff_squarefree]

theorem isMultiplicative_mFreeIndicator {m : ℕ} (hm : m ≠ 0) :
    (mFreeIndicator m).IsMultiplicative := by
  refine ⟨?_, fun {a b} hab => ?_⟩
  · rw [mFreeIndicator_apply, if_pos (mFree_one hm)]
  · rw [mFreeIndicator_apply, mFreeIndicator_apply, mFreeIndicator_apply]
    by_cases ha : MFree m a
    · by_cases hb : MFree m b
      · rw [if_pos ha, if_pos hb, if_pos ((mFree_mul_iff hab).mpr ⟨ha, hb⟩), one_mul]
      · rw [if_neg hb, mul_zero, if_neg fun h => hb ((mFree_mul_iff hab).mp h).2]
    · rw [if_neg ha, zero_mul, if_neg fun h => ha ((mFree_mul_iff hab).mp h).1]

/-- The dilated Möbius function at prime powers: `1` at `p⁰`, `-1` at `p^m`, `0`
elsewhere. -/
theorem mPart_moebius_apply_prime_pow {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime) (j : ℕ) :
    mPart m (μ : ArithmeticFunction ℤ) (p ^ j) =
      if j = 0 then 1 else if j = m then -1 else 0 := by
  by_cases hdvd : m ∣ j
  · obtain ⟨t, rfl⟩ := hdvd
    rw [show p ^ (m * t) = (p ^ t) ^ m by rw [← pow_mul, mul_comm], mPart_apply_pow hm]
    match t with
    | 0 => simp
    | 1 => rw [pow_one, moebius_apply_prime hp, mul_one, if_neg hm, if_pos rfl]
    | (v + 2) =>
      rw [moebius_apply_prime_pow hp (by omega), if_neg (by omega),
        if_neg (mul_ne_zero hm (by omega)), if_neg]
      intro hmm
      have := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm)
        (hmm.trans (mul_one m).symm)
      omega
  · have hnp : ∀ k : ℕ, k ^ m ≠ p ^ j := by
      intro k hk
      have hkdvd : k ∣ p ^ j := hk ▸ dvd_pow_self k hm
      obtain ⟨t, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hkdvd
      rw [← pow_mul] at hk
      exact hdvd ⟨t, (Nat.pow_right_injective hp.two_le hk).symm.trans (mul_comm t m)⟩
    rw [mPart_apply_of_forall_pow_ne _ _ hnp,
      if_neg (show ¬ j = 0 from fun hj0 => hdvd (by rw [hj0]; exact dvd_zero m)),
      if_neg (show ¬ j = m from fun hjm => hdvd (by rw [hjm]))]

/-- The `m`-free indicator at prime powers: `1` below the `m`-th power, `0` from it on. -/
theorem mFreeIndicator_apply_prime_pow {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime) (i : ℕ) :
    mFreeIndicator m (p ^ i) = if i < m then 1 else 0 := by
  rw [mFreeIndicator_apply]
  by_cases him : i < m
  · rw [if_pos him, if_pos]
    intro q hq hdvd
    have hqp : q = p :=
      (Nat.prime_dvd_prime_iff_eq hq hp).mp
        (hq.dvd_of_dvd_pow (dvd_trans (dvd_pow_self q hm) hdvd))
    subst hqp
    rw [Nat.pow_dvd_pow_iff_le_right hq.one_lt] at hdvd
    omega
  · rw [if_neg him, if_neg]
    intro hfree
    exact hfree p hp (pow_dvd_pow p (by omega))

/-- **The m-free Möbius normalization, arithmetic form.**  The Dirichlet convolution of the
`m`-th-power-dilated Möbius function with `ζ` is the `m`-free indicator:
`∑_{d^m ∣ n} μ(d) = [n is m-free]`. -/
theorem mPart_moebius_mul_zeta {m : ℕ} (hm : m ≠ 0) :
    mPart m (μ : ArithmeticFunction ℤ) * (ζ : ArithmeticFunction ℤ) = mFreeIndicator m := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((isMultiplicative_mPart hm isMultiplicative_moebius).mul isMultiplicative_zeta.natCast)
    _ (isMultiplicative_mFreeIndicator hm)).mpr fun p i hp => ?_
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp,
    mFreeIndicator_apply_prime_pow hm hp]
  rcases Nat.lt_or_ge i m with hi | hi
  · rw [if_pos hi]
    have hsum : ∑ j ∈ Finset.range (i + 1), mPart m (μ : ArithmeticFunction ℤ) (p ^ j)
        = ∑ j ∈ ({0} : Finset ℕ), mPart m (μ : ArithmeticFunction ℤ) (p ^ j) := by
      symm
      refine Finset.sum_subset ?_ fun x hx hxne => ?_
      · intro x hx
        simp only [Finset.mem_singleton] at hx
        simp [hx]
      · simp only [Finset.mem_singleton] at hxne
        have hxi := Finset.mem_range.mp hx
        rw [mPart_moebius_apply_prime_pow hm hp x, if_neg hxne, if_neg (by omega)]
    rw [hsum, Finset.sum_singleton, mPart_moebius_apply_prime_pow hm hp 0, if_pos rfl]
  · rw [if_neg (by omega)]
    have hsum : ∑ j ∈ Finset.range (i + 1), mPart m (μ : ArithmeticFunction ℤ) (p ^ j)
        = ∑ j ∈ ({0, m} : Finset ℕ), mPart m (μ : ArithmeticFunction ℤ) (p ^ j) := by
      symm
      refine Finset.sum_subset ?_ fun x hx hxne => ?_
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_range]
        omega
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxne
        rw [mPart_moebius_apply_prime_pow hm hp x, if_neg hxne.1, if_neg hxne.2]
    rw [hsum, Finset.sum_pair (Ne.symm hm), mPart_moebius_apply_prime_pow hm hp 0,
      mPart_moebius_apply_prime_pow hm hp m, if_pos rfl, if_neg hm, if_pos rfl]
    norm_num

/-- The divisor-sum face: `∑_{d ∣ n} (mPart m μ)(d) = [n is m-free]`, the sum extending
only over `m`-th power divisors. -/
theorem sum_divisors_mPart_moebius {m : ℕ} (hm : m ≠ 0) (n : ℕ) :
    ∑ d ∈ n.divisors, mPart m (μ : ArithmeticFunction ℤ) d = mFreeIndicator m n := by
  have h : (mPart m (μ : ArithmeticFunction ℤ) * (ζ : ArithmeticFunction ℤ)) n
      = mFreeIndicator m n := by rw [mPart_moebius_mul_zeta hm]
  rwa [coe_mul_zeta_apply] at h

/-! ## The analytic dilation law: `L(mPart m f, s) = L(f, ms)` -/

/-- Casting an `m`-th power of a natural into `ℂ` and raising to `s` is the `m`-th power of
the base raised to `s`. -/
theorem natCast_pow_cpow (k m : ℕ) (s : ℂ) :
    ((k ^ m : ℕ) : ℂ) ^ s = (((k : ℕ) : ℂ) ^ s) ^ m := by
  induction m with
  | zero => simp
  | succ t ih => rw [pow_succ, natCast_mul_cpow, ih, pow_succ]

theorem term_mPart_pow {m : ℕ} (hm : m ≠ 0) (f : ArithmeticFunction ℂ) (s : ℂ) (k : ℕ) :
    term (⇑(mPart m f)) s (k ^ m) = term (⇑f) ((m : ℂ) * s) k := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [zero_pow hm]; simp
  · rw [term_of_ne_zero (pow_ne_zero m hk), term_of_ne_zero hk, mPart_apply_pow hm,
      natCast_pow_cpow, Complex.cpow_nat_mul]

private theorem term_mPart_vanish (m : ℕ) (f : ArithmeticFunction ℂ) (s : ℂ) :
    ∀ x ∉ Set.range (fun k : ℕ => k ^ m), term (⇑(mPart m f)) s x = 0 := by
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · rw [term_of_ne_zero hx0, mPart_apply_of_forall_pow_ne m f (fun k hk => hx ⟨k, hk⟩),
      zero_div]

/-- Summability transfer for the `m`-th power dilation: `L(mPart m f)` converges at `s`
exactly when `L f` converges at `ms`. -/
theorem LSeriesSummable_mPart_iff {m : ℕ} (hm : m ≠ 0) (f : ArithmeticFunction ℂ) (s : ℂ) :
    LSeriesSummable (⇑(mPart m f)) s ↔ LSeriesSummable (⇑f) ((m : ℂ) * s) := by
  have hterm : (term (⇑(mPart m f)) s) ∘ (fun k : ℕ => k ^ m) = term (⇑f) ((m : ℂ) * s) :=
    funext fun k => term_mPart_pow hm f s k
  unfold LSeriesSummable
  rw [← (Nat.pow_left_injective hm).summable_iff (term_mPart_vanish m f s), hterm]

/-- **The dilation ladder.**  The L-series of the `m`-th power dilation is the original
L-series at the `m`-fold variable: `L(mPart m f, s) = L(f, ms)`.  The square dilation law
is the rung `m = 2`. -/
theorem LSeries_mPart {m : ℕ} (hm : m ≠ 0) (f : ArithmeticFunction ℂ) (s : ℂ) :
    LSeries (⇑(mPart m f)) s = LSeries (⇑f) ((m : ℂ) * s) := by
  unfold LSeries
  rw [← (Nat.pow_left_injective hm).tsum_eq
    (Function.support_subset_iff'.mpr (term_mPart_vanish m f s))]
  exact tsum_congr fun k => term_mPart_pow hm f s k

/-! ## The Möbius rungs: `ζ(ms)⁻¹` on `re s > 1/m` and the m-free ladder on `re s > 1` -/

private theorem coe_mPart_moebius_intCoe (m : ℕ) :
    ⇑(mPart m ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)) =
      ↗(mPart m (μ : ArithmeticFunction ℤ)) := by
  rw [← mPart_intCoe]
  funext n
  simp [intCoe_apply]

private theorem coe_intCoe_moebius' :
    ⇑((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) = ↗μ := by
  funext n; simp [intCoe_apply]

private theorem coe_natCoe_zeta' :
    ⇑((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) = ↗ζ := by
  funext n; simp [natCoe_apply]

theorem one_lt_natCast_mul_re {m : ℕ} (hm : m ≠ 0) {s : ℂ}
    (hs : 1 / (m : ℝ) < s.re) : 1 < ((m : ℂ) * s).re := by
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have hre : ((m : ℂ) * s).re = (m : ℝ) * s.re := by simp [Complex.mul_re]
  rw [hre]
  rw [div_lt_iff₀ hm0] at hs
  calc (1 : ℝ) < s.re * m := hs
    _ = m * s.re := mul_comm _ _

/-- The dilated Möbius series converges on the half-plane `re s > 1/m`. -/
theorem LSeriesSummable_mPart_moebius {m : ℕ} (hm : m ≠ 0) {s : ℂ}
    (hs : 1 / (m : ℝ) < s.re) :
    LSeriesSummable ↗(mPart m (μ : ArithmeticFunction ℤ)) s := by
  rw [← coe_mPart_moebius_intCoe, LSeriesSummable_mPart_iff hm, coe_intCoe_moebius']
  exact LSeriesSummable_moebius_iff.mpr (one_lt_natCast_mul_re hm hs)

/-- On `re s > 1/m` the dilated Möbius series represents `ζ(ms)⁻¹`. -/
theorem LSeries_mPart_moebius {m : ℕ} (hm : m ≠ 0) {s : ℂ}
    (hs : 1 / (m : ℝ) < s.re) :
    L ↗(mPart m (μ : ArithmeticFunction ℤ)) s = (riemannZeta ((m : ℂ) * s))⁻¹ := by
  rw [← coe_mPart_moebius_intCoe, LSeries_mPart hm, coe_intCoe_moebius',
    LSeries_moebius_eq_inv_riemannZeta (one_lt_natCast_mul_re hm hs)]

theorem one_div_natCast_lt_re {m : ℕ} (hm : m ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    1 / (m : ℝ) < s.re := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hm)
  have : 1 / (m : ℝ) ≤ 1 :=
    (div_le_one (by linarith)).mpr hm1
  linarith

/-- **The m-free Möbius ladder, product form.**
`L([·, m-free], s) · ζ(ms) = ζ(s)` on `re s > 1`. -/
theorem LSeries_mFree_mul_riemannZeta {m : ℕ} (hm : m ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    L ↗(mFreeIndicator m) s * riemannZeta ((m : ℂ) * s) = riemannZeta s := by
  have hsm : 1 / (m : ℝ) < s.re := one_div_natCast_lt_re hm hs
  have h2 : 1 < ((m : ℂ) * s).re := one_lt_natCast_mul_re hm hsm
  have hzsum : LSeriesSummable ⇑((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) s := by
    rw [coe_natCoe_zeta']
    exact LSeriesSummable_zeta_iff.mpr hs
  have hmusum : LSeriesSummable
      ⇑(mPart m ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)) s := by
    rw [coe_mPart_moebius_intCoe]
    exact LSeriesSummable_mPart_moebius hm hsm
  have hfun : ↗(mFreeIndicator m) =
      ⇑((mFreeIndicator m : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) := by
    funext n; simp [intCoe_apply]
  have hAF : ((mFreeIndicator m : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) =
      mPart m ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) *
        (ζ : ArithmeticFunction ℂ) := by
    rw [← mPart_moebius_mul_zeta hm, intCoe_mul, mPart_intCoe, intCoe_natCoe]
  have hz : L ⇑((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) s = riemannZeta s := by
    rw [coe_natCoe_zeta']
    exact LSeries_zeta_eq_riemannZeta hs
  rw [hfun, hAF, LSeries_mul' hmusum hzsum, hz, coe_mPart_moebius_intCoe,
    LSeries_mPart_moebius hm hsm]
  field_simp [riemannZeta_ne_zero_of_one_lt_re h2]

/-- **The m-free Möbius ladder, quotient form.**
`L([·, m-free], s) = ζ(s)/ζ(ms)` on `re s > 1`. -/
theorem LSeries_mFree_eq_riemannZeta_div {m : ℕ} (hm : m ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    L ↗(mFreeIndicator m) s = riemannZeta s / riemannZeta ((m : ℂ) * s) := by
  have h2 : 1 < ((m : ℂ) * s).re :=
    one_lt_natCast_mul_re hm (one_div_natCast_lt_re hm hs)
  rw [eq_div_iff (riemannZeta_ne_zero_of_one_lt_re h2)]
  exact LSeries_mFree_mul_riemannZeta hm hs

open scoped Classical in
/-- **The m-free Möbius ladder, explicit series form.**
`∑' n, [n is m-free]/n^s = ζ(s)/ζ(ms)` on `re s > 1`. -/
theorem tsum_mFree_cpow {m : ℕ} (hm : m ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, (if MFree m n then 1 / (n : ℂ) ^ s else 0) =
      riemannZeta s / riemannZeta ((m : ℂ) * s) := by
  rw [← LSeries_mFree_eq_riemannZeta_div hm hs]
  unfold LSeries
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [not_mFree_zero]
  · rw [term_of_ne_zero hn, mFreeIndicator_apply]
    split_ifs with h
    · push_cast
      rw [one_div]
    · push_cast
      rw [zero_div]

/-! ## The off-line carrier bridge: `dpoly2` truncations converge to the L-series -/

/-- The off-line carrier polynomial on `[1, N]` is the range-`(N+1)` partial sum of the
L-series terms: the `0`-term vanishes and the remaining terms are the carrier summands. -/
theorem dpoly2_Icc_eq_sum_range_term (a : ℕ → ℝ) (z : ℂ) (N : ℕ) :
    dpoly2 a (Finset.Icc 1 N) z
      = ∑ i ∈ Finset.range (N + 1), term (fun n => (a n : ℂ)) z i := by
  symm
  rw [dpoly2, ← Finset.sum_subset (fun i hi => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.mem_Icc.mp hi).2))
    (fun x hxmem hx => ?_)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi1 : i ≠ 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hi).1
    rw [term_of_ne_zero hi1, Complex.cpow_neg, div_eq_mul_inv]
  · have hx0 : x = 0 := by
      by_contra hxne
      exact hx (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hxne,
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hxmem)⟩)
    subst hx0
    exact LSeries.term_zero _ _

/-- **Truncation-convergence bridge.**  For any real coefficient sequence whose L-series
converges at `z`, the off-line carrier polynomials `dpoly2 a (Icc 1 N) z` converge to the
L-series value as the cutoff grows.  This is what turns an L-series identity on a
half-plane into a statement about the finite Dirichlet carriers of the mollifier/carrier
machinery. -/
theorem tendsto_dpoly2_Icc_of_LSeriesSummable {a : ℕ → ℝ} {z : ℂ}
    (h : LSeriesSummable (fun n => (a n : ℂ)) z) :
    Tendsto (fun N => dpoly2 a (Finset.Icc 1 N) z) atTop
      (nhds (LSeries (fun n => (a n : ℂ)) z)) := by
  have h1 := h.hasSum.tendsto_sum_nat
  have hcomp := h1.comp (tendsto_add_atTop_nat 1)
  exact hcomp.congr fun N => (dpoly2_Icc_eq_sum_range_term a z N).symm

/-- The Möbius mollifier coefficients (`Mollifier.moebiusCoeff`), read as complex values,
are the Möbius L-series coefficients. -/
theorem moebiusCoeff_complex (n : ℕ) : ((moebiusCoeff n : ℝ) : ℂ) = ↗μ n := by
  simp [moebiusCoeff]

/-- **The mollifier converges to `ζ(z)⁻¹` off the line.**  The off-line carriers built from
the Möbius mollifier coefficients converge to `ζ(z)⁻¹` on `re z > 1`. -/
theorem tendsto_dpoly2_moebiusCoeff {z : ℂ} (hz : 1 < z.re) :
    Tendsto (fun N => dpoly2 moebiusCoeff (Finset.Icc 1 N) z) atTop
      (nhds ((riemannZeta z)⁻¹)) := by
  have hfun : (fun n => ((moebiusCoeff n : ℝ) : ℂ)) = ↗μ := funext moebiusCoeff_complex
  have hsum : LSeriesSummable (fun n => ((moebiusCoeff n : ℝ) : ℂ)) z := by
    rw [hfun]; exact LSeriesSummable_moebius_iff.mpr hz
  have h := tendsto_dpoly2_Icc_of_LSeriesSummable hsum
  rwa [hfun, LSeries_moebius_eq_inv_riemannZeta hz] at h

/-- The `ζ(mz)⁻¹` carrier coefficients: the `m`-th-power-dilated Möbius sequence, as
reals. -/
noncomputable def mPartMoebiusCoeff (m n : ℕ) : ℝ :=
  ((mPart m (μ : ArithmeticFunction ℤ) n : ℤ) : ℝ)

theorem mPartMoebiusCoeff_complex (m n : ℕ) :
    ((mPartMoebiusCoeff m n : ℝ) : ℂ) = ↗(mPart m (μ : ArithmeticFunction ℤ)) n := by
  simp [mPartMoebiusCoeff]

/-- The dilated Möbius coefficients are mollifier-grade: bounded by `1`. -/
theorem abs_mPartMoebiusCoeff_le_one {m : ℕ} (hm : m ≠ 0) (n : ℕ) :
    |mPartMoebiusCoeff m n| ≤ 1 := by
  rw [mPartMoebiusCoeff, ← Int.cast_abs]
  have hint : |mPart m (μ : ArithmeticFunction ℤ) n| ≤ 1 := by
    by_cases h : ∃ k, k ^ m = n
    · obtain ⟨k, rfl⟩ := h
      rw [mPart_apply_pow hm]
      exact abs_moebius_le_one
    · rw [mPart_apply_of_forall_pow_ne m _ (fun k hk => h ⟨k, hk⟩)]
      norm_num
  exact_mod_cast hint

/-- **The general rung.**  The off-line carriers of the `m`-th-power-dilated Möbius
coefficients converge to `ζ(mz)⁻¹` on the half-plane `re z > 1/m`. -/
theorem tendsto_dpoly2_mPartMoebiusCoeff {m : ℕ} (hm : m ≠ 0) {z : ℂ}
    (hz : 1 / (m : ℝ) < z.re) :
    Tendsto (fun N => dpoly2 (mPartMoebiusCoeff m) (Finset.Icc 1 N) z) atTop
      (nhds ((riemannZeta ((m : ℂ) * z))⁻¹)) := by
  have hfun : (fun n => ((mPartMoebiusCoeff m n : ℝ) : ℂ)) =
      ↗(mPart m (μ : ArithmeticFunction ℤ)) := funext (mPartMoebiusCoeff_complex m)
  have hsum : LSeriesSummable (fun n => ((mPartMoebiusCoeff m n : ℝ) : ℂ)) z := by
    rw [hfun]; exact LSeriesSummable_mPart_moebius hm hz
  have h := tendsto_dpoly2_Icc_of_LSeriesSummable hsum
  rwa [hfun, LSeries_mPart_moebius hm hz] at h

/-- The `ζ(2z)⁻¹` carrier coefficients: the square-dilated Möbius sequence, as reals. -/
noncomputable def sqrtMoebiusCoeff (n : ℕ) : ℝ :=
  ((sqrtPart (μ : ArithmeticFunction ℤ) n : ℤ) : ℝ)

theorem sqrtMoebiusCoeff_eq_mPart : sqrtMoebiusCoeff = mPartMoebiusCoeff 2 := by
  funext n
  rw [sqrtMoebiusCoeff, mPartMoebiusCoeff, mPart_two_eq_sqrtPart]

/-- The square-dilated Möbius coefficients are mollifier-grade: bounded by `1`. -/
theorem abs_sqrtMoebiusCoeff_le_one (n : ℕ) : |sqrtMoebiusCoeff n| ≤ 1 := by
  rw [sqrtMoebiusCoeff_eq_mPart]
  exact abs_mPartMoebiusCoeff_le_one two_ne_zero n

/-- **`ζ(2z)⁻¹` is a native critical-strip-adjacent carrier limit.**  The off-line carriers
of the square-dilated Möbius coefficients converge to `ζ(2z)⁻¹` on the half-plane
`re z > 1/2`. -/
theorem tendsto_dpoly2_sqrtMoebiusCoeff {z : ℂ} (hz : 1 / 2 < z.re) :
    Tendsto (fun N => dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) z) atTop
      (nhds ((riemannZeta (2 * z))⁻¹)) := by
  have h := tendsto_dpoly2_mPartMoebiusCoeff two_ne_zero (z := z) (by simpa using hz)
  rw [sqrtMoebiusCoeff_eq_mPart]
  have h2 : ((2 : ℕ) : ℂ) = (2 : ℂ) := by norm_num
  rwa [h2] at h

/-- **The square-dilated Möbius mollifier's second moment** over a window `[T, T+U]` is the
Montgomery–Vaughan mean value with diagonal `∑_{m≤y} sqrtMoebiusCoeff(m)²` plus the explicit
off-diagonal remainder — the same machinery the Möbius mollifier feeds. -/
theorem sqrtMollifier_secondMoment (y : ℕ) (T U : ℝ) :
    (∫ t in T..T + U, ‖dpoly sqrtMoebiusCoeff (Finset.Icc 1 y) t‖ ^ 2)
      = U * (∑ m ∈ Finset.Icc 1 y, (sqrtMoebiusCoeff m) ^ 2)
        + ∑ m ∈ Finset.Icc 1 y, ∑ n ∈ (Finset.Icc 1 y).erase m,
            sqrtMoebiusCoeff m * sqrtMoebiusCoeff n * cosInt (Real.log n - Real.log m) T U :=
  secondMoment_meanValue sqrtMoebiusCoeff (Finset.Icc 1 y) T U

end RHTower
