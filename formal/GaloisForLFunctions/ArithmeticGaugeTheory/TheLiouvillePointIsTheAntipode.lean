import GaloisForLFunctions.ArithmeticGaugeTheory.TheDivisorCollapse
import GaloisForLFunctions.ArithmeticGaugeTheory.TheGaugeExponentIsATailInvariant
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# The Liouville point is the antipode of the trivial point

Read the prime source at a gauge point: `S_N(y) = Σ_{n ≤ N} Λ(n) χ_y(n)`. At the trivial point this is
`ψ(N)`, the pole. At a Liouville point (`χ_y(p) = −1` for every prime) the prime powers `p^k` carry the
sign `(−1)^k`.

* **The antipode identity** (`primeGaugeSum_liouville_add_trivial`).
  `S_N(ℓ) + S_N(0) = 2 Σ_{m ≤ √N} Λ(m) = 2ψ(√N)`: only the even prime powers survive, and they are
  the squares of the prime powers up to `√N` (`vonMangoldt_mul_one_add_twist`).
* **Pole and anti-pole** (`tendsto_primeGaugeSum_trivial`, `tendsto_primeGaugeSum_liouville`). By the
  prime number theorem `S_N(0)/N → 1` and `S_N(ℓ)/N → −1`.
* **The boundary separates the twins** (`eventually_re_primeGaugeSum_liouville_neg`). For large `N` the
  real part is positive at the trivial point and negative at the Liouville point.

Both points have coherent prime sums of size `N`, so no size statement (an exponent, a modulus, a
norm bound) separates them, and coherence `|S_N(y)| ≤ S_N(0)` is attained at both. What separates them
is the sign of the boundary term: the pole is `+1` at the trivial point and `−1` at its parity twin.
A positivity principle whose boundary is the pole sees the twin with the opposite sign.
-/

open Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-- The prime source read at a gauge point. -/
def primeGaugeSum (N : ℕ) (y : GaugeTorus) : ℂ :=
  ∑ n ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) * twist y n

/-- At the trivial point the prime source is `ψ(N)`. -/
theorem primeGaugeSum_trivial (N : ℕ) :
    primeGaugeSum N 0 = ((∑ n ∈ Iic N, ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) := by
  have hI : Iic N = insert 0 (Icc 1 N) := by
    ext n
    simp only [mem_Iic, mem_insert, mem_Icc]
    omega
  rw [hI, sum_insert (by simp), ArithmeticFunction.map_zero, zero_add, primeGaugeSum]
  push_cast
  simp [twist_trivialPoint]

/-- A prime power is a square iff its exponent is even. -/
theorem exists_sq_eq_prime_pow_iff {p k : ℕ} (hp : p.Prime) : (∃ m, m ^ 2 = p ^ k) ↔ Even k := by
  constructor
  · rintro ⟨m, hm⟩
    have hdvd : m ∣ p ^ k := ⟨m, by rw [← hm, sq]⟩
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rw [← pow_mul] at hm
    have := Nat.pow_right_injective hp.two_le hm
    exact ⟨j, by omega⟩
  · rintro ⟨j, rfl⟩
    exact ⟨p ^ j, by ring⟩

open Classical in
/-- At a Liouville point `Λ(n)(1 + χ(n))` keeps exactly the even prime powers, doubled. -/
theorem vonMangoldt_mul_one_add_twist {y : GaugeTorus} (hy : ∀ p, p.Prime → twist y p = -1)
    (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℂ) * (1 + twist y n) =
      if ∃ m, m ^ 2 = n then 2 * (ArithmeticFunction.vonMangoldt n : ℂ) else 0 := by
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp [hΛ]
  · obtain ⟨p, k, hp, -, rfl⟩ :=
      (isPrimePow_nat_iff _).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
    rw [twist_pow y hp.ne_zero, hy p hp]
    by_cases he : Even k
    · rw [if_pos ((exists_sq_eq_prime_pow_iff hp).mpr he), he.neg_one_pow]
      ring
    · rw [if_neg fun h => he ((exists_sq_eq_prime_pow_iff hp).mp h),
        (Nat.not_even_iff_odd.mp he).neg_one_pow]
      ring

open Classical in
/-- **The antipode identity.** `S_N(ℓ) + S_N(0) = 2 Σ_{m ≤ √N} Λ(m)`. -/
theorem primeGaugeSum_liouville_add_trivial {y : GaugeTorus}
    (hy : ∀ p, p.Prime → twist y p = -1) (N : ℕ) :
    primeGaugeSum N y + primeGaugeSum N 0 =
      2 * ((∑ m ∈ Icc 1 (Nat.sqrt N), ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) := by
  rw [primeGaugeSum, primeGaugeSum, ← sum_add_distrib]
  have hterm : ∀ n, (ArithmeticFunction.vonMangoldt n : ℂ) * twist y n +
      (ArithmeticFunction.vonMangoldt n : ℂ) * twist 0 n =
      (ArithmeticFunction.vonMangoldt n : ℂ) * (1 + twist y n) := by
    intro n
    rw [twist_trivialPoint]
    ring
  simp_rw [hterm, vonMangoldt_mul_one_add_twist hy]
  -- The squares in `[1, N]` are the squares of `[1, √N]`.
  have himg : (Icc 1 N).filter (fun n => ∃ m, m ^ 2 = n) =
      (Icc 1 (Nat.sqrt N)).image (fun m => m ^ 2) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h1, hN⟩, m, rfl⟩
      refine ⟨m, ⟨Nat.pos_of_ne_zero ?_, Nat.le_sqrt'.mpr hN⟩, rfl⟩
      rintro rfl
      simp at h1
    · rintro ⟨m, ⟨h1, hm⟩, rfl⟩
      exact ⟨⟨Nat.one_le_pow _ _ h1, Nat.le_sqrt'.mp hm⟩, m, rfl⟩
  have hR : 2 * ((∑ m ∈ Icc 1 (Nat.sqrt N), ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) =
      ∑ n ∈ (Icc 1 N).filter (fun n => ∃ m, m ^ 2 = n),
        2 * (ArithmeticFunction.vonMangoldt n : ℂ) := by
    rw [himg, sum_image fun a _ b _ h => Nat.pow_left_injective two_ne_zero h]
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [ArithmeticFunction.vonMangoldt_apply_pow two_ne_zero]
  rw [hR, sum_filter]
  -- The two `if`s differ only in their decidability instances.
  refine sum_congr rfl fun n _ => ?_
  congr

/-- The square-root term is negligible: `Σ_{m ≤ √N} Λ(m) / N → 0`. -/
theorem tendsto_sum_vonMangoldt_sqrt_div :
    Tendsto (fun N : ℕ => (∑ m ∈ Icc 1 (Nat.sqrt N), ArithmeticFunction.vonMangoldt m) / (N : ℝ))
      atTop (𝓝 0) := by
  have hsqrt : Tendsto Nat.sqrt atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b * b, fun n hn => Nat.le_sqrt.mpr hn⟩
  have hpnt := WeakPNT'.comp hsqrt
  -- `√N / N ≤ 1/√N → 0`.
  have hratio : Tendsto (fun N : ℕ => (Nat.sqrt N : ℝ) / N) atTop (𝓝 0) := by
    have hinv : Tendsto (fun N : ℕ => 1 / Real.sqrt N) atTop (𝓝 0) := by
      refine (tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).congr fun N => ?_
      simp only [Function.comp_apply, one_div]
    refine squeeze_zero (fun N => by positivity) (fun N => ?_) hinv
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have hs : (Nat.sqrt N : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
      have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNr.le
      have hsp : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
      rw [div_le_div_iff₀ hNr hsp]
      nlinarith
  have hprod := hpnt.mul hratio
  rw [one_mul] at hprod
  refine hprod.congr fun N => ?_
  have hIic : ∑ m ∈ Iic (Nat.sqrt N), ArithmeticFunction.vonMangoldt m =
      ∑ m ∈ Icc 1 (Nat.sqrt N), ArithmeticFunction.vonMangoldt m := by
    have hI : Iic (Nat.sqrt N) = insert 0 (Icc 1 (Nat.sqrt N)) := by
      ext n
      simp only [mem_Iic, mem_insert, mem_Icc]
      omega
    rw [hI, sum_insert (by simp), ArithmeticFunction.map_zero, zero_add]
  simp only [Function.comp_apply, hIic]
  rcases Nat.eq_zero_or_pos (Nat.sqrt N) with h0 | hpos
  · rw [h0]
    simp
  · have : (Nat.sqrt N : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp

/-- **The pole at the trivial point.** -/
theorem tendsto_primeGaugeSum_trivial :
    Tendsto (fun N : ℕ => primeGaugeSum N 0 / N) atTop (𝓝 1) := by
  have h := (Complex.continuous_ofReal.tendsto 1).comp WeakPNT'
  rw [Complex.ofReal_one] at h
  refine h.congr fun N => ?_
  simp only [Function.comp_apply, primeGaugeSum_trivial]
  push_cast
  rfl

/-- **The anti-pole at the Liouville point.** -/
theorem tendsto_primeGaugeSum_liouville {y : GaugeTorus} (hy : ∀ p, p.Prime → twist y p = -1) :
    Tendsto (fun N : ℕ => primeGaugeSum N y / N) atTop (𝓝 (-1)) := by
  have hsq := (Complex.continuous_ofReal.tendsto 0).comp tendsto_sum_vonMangoldt_sqrt_div
  rw [Complex.ofReal_zero] at hsq
  have h := (hsq.const_mul 2).sub tendsto_primeGaugeSum_trivial
  rw [mul_zero, zero_sub] at h
  refine h.congr fun N => ?_
  simp only [Function.comp_apply]
  have hid := primeGaugeSum_liouville_add_trivial hy N
  push_cast at hid ⊢
  rw [eq_sub_of_add_eq hid]
  ring

/-- **The boundary separates the twins.** For large `N` the prime source has positive real part at
the trivial point and negative real part at the Liouville point. -/
theorem eventually_re_primeGaugeSum_liouville_neg {y : GaugeTorus}
    (hy : ∀ p, p.Prime → twist y p = -1) :
    ∀ᶠ N : ℕ in atTop, (primeGaugeSum N y).re < 0 ∧ 0 < (primeGaugeSum N 0).re := by
  have hℓ := (Complex.continuous_re.tendsto _).comp (tendsto_primeGaugeSum_liouville hy)
  have h0 := (Complex.continuous_re.tendsto _).comp tendsto_primeGaugeSum_trivial
  simp only [Complex.neg_re, Complex.one_re] at hℓ h0
  filter_upwards [hℓ.eventually (gt_mem_nhds (show (-1 : ℝ) < 0 by norm_num)),
    h0.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)), eventually_gt_atTop 0]
    with N hN1 hN2 hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Function.comp_apply, Complex.div_natCast_re] at hN1 hN2
  exact ⟨(div_neg_iff.mp hN1).elim (fun h => absurd h.2 (not_lt.mpr hNr.le)) (fun h => h.1),
    (div_pos_iff.mp hN2).elim (fun h => h.1) (fun h => absurd h.2 (not_lt.mpr hNr.le))⟩

end GaloisForLFunctions.ArithmeticGaugeTheory
