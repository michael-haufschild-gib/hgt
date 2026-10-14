import GaloisForLFunctions.RHTower.ArchimedeanMellinFourier
import GaloisForLFunctions.HTGeometry.SchwartzDilateSummability
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Integer blindness is a Möbius law for primitive Farey sums

Let `f` be an even Schwartz function with Fourier transform `F = 𝓕 f`
(`F(ξ) = ∫ f(x) e^{−2πixξ} dx`).  For `q ≥ 1` let

`P_f(q) = Σ_{a ≥ 1, gcd(a, q) = 1} F(a/q)`   (`primitiveFareySum`)

be the sum of `F` over the positive reduced fractions with denominator `q`.

**Theorem** (`primitiveFareySum_eq_moebius_mul`).  If `f(0) = 0` and `f(n) = 0` for every integer
`n ≥ 2` (so the only integer values allowed are `f(±1)`), then for every `q ≥ 2`

`P_f(q) = μ(q) · f(1)`.

For a Weil test the function `g(y) = G(log |y|)` (with `G` the autocorrelation) is even, vanishes
near `0`, and vanishes at every integer `n ≥ 2` exactly when `G` is prime-blind at `log n`; so
prime blindness is the statement that the primitive Farey sums of `ĝ` are the Möbius function.

Proof.
* Dilated Poisson summation at scale `m` (`even_poisson_summation_dilate`):
  `f(0) + 2 Σ_{n≥1} f(mn) = m⁻¹ (F(0) + 2 Σ_{k≥1} F(k/m))`.  Blindness makes the left side `0`
  for `m ≥ 2` and `2f(1)` for `m = 1`, so `V(m) := Σ_{k≥1} F(k/m)` equals `−F(0)/2` for `m ≥ 2` and
  `f(1) − F(0)/2` for `m = 1`.
* Grouping `k ≥ 1` by `g = gcd(k, m)` (`k = g a`, `gcd(a, m/g) = 1`) gives
  `V(m) = Σ_{q ∣ m} P_f(q)` (`tsum_fareyDilate_eq_sum_divisors`).
* Möbius inversion: `P_f(q) = Σ_{de = q} μ(d) V(e) = −(F(0)/2) Σ_{d∣q} μ(d) + μ(q) f(1) = μ(q) f(1)`.

**Converse** (`blind_of_primitiveFareySum`, `blind_iff_primitiveFareySum`).  If `f` vanishes for
`|x| > N`, the Möbius law for every `q ≥ 2` gives back `f(0) = 0` and `f(n) = 0` for `n ≥ 2`.  The
Möbius law makes `V(m) = P_f(1) − f(1)` for every `m ≥ 2`, so Poisson summation reads
`f(0) + 2 Σ_{n≥1} f(mn) = C/m`.  For `m > N` the left side is `f(0)`, and comparing `m = N + 2` with
`m = 2N + 4` gives `C = 0` and `f(0) = 0`.  Every multiple sum `Σ_{n≥1} f(mn)` then vanishes, and
downward induction over multiples (`eq_zero_of_multiple_sums`) gives `f(m) = 0`.
-/

open Complex Real Filter Topology Set
open scoped FourierTransform ArithmeticFunction.Moebius

namespace RHTower

noncomputable section

/-- The primitive Farey sum `Σ_{a ≥ 1, gcd(a, q) = 1} F(a/q)` of `F = 𝓕 f`. -/
def primitiveFareySum (f : SchwartzMap ℝ ℂ) (q : ℕ) : ℂ :=
  ∑' a : ℕ, if Nat.Coprime (a + 1) q then (𝓕 (f : ℝ → ℂ)) (((a : ℝ) + 1) / q) else 0

/-- The dilated Fourier sum `Σ_{k ≥ 1} F(k/m)`. -/
def fareyDilateSum (f : SchwartzMap ℝ ℂ) (m : ℕ) : ℂ :=
  ∑' k : ℕ, (𝓕 (f : ℝ → ℂ)) (((k : ℝ) + 1) / m)

theorem summable_fourier_dilate (f : SchwartzMap ℝ ℂ) {m : ℕ} (hm : 0 < m) :
    Summable fun k : ℕ => (𝓕 (f : ℝ → ℂ)) (((k : ℝ) + 1) / m) := by
  have hu : (0 : ℝ) < 1 / m := by positivity
  refine (HTGeometry.summable_schwartzDilate (𝓕 f) hu).congr fun k => ?_
  rw [SchwartzMap.fourier_coe]
  exact congrArg _ (by ring)

theorem summable_norm_fourier_dilate (f : SchwartzMap ℝ ℂ) {m : ℕ} (hm : 0 < m) :
    Summable fun k : ℕ => ‖(𝓕 (f : ℝ → ℂ)) (((k : ℝ) + 1) / m)‖ := by
  have hu : (0 : ℝ) < 1 / m := by positivity
  refine (HTGeometry.summable_norm_schwartzDilate (𝓕 f) hu).congr fun k => ?_
  rw [SchwartzMap.fourier_coe]
  exact congrArg _ (congrArg _ (by ring))

/-- The gcd class `g` of the dilated sum is the primitive Farey sum at `m / g`. -/
theorem tsum_gcd_class_eq_primitiveFareySum (f : SchwartzMap ℝ ℂ) {m g : ℕ} (hm : 0 < m)
    (hg : g ∈ m.divisors) :
    (∑' k : ℕ, if Nat.gcd (k + 1) m = g then (𝓕 (f : ℝ → ℂ)) (((k : ℝ) + 1) / m) else 0) =
      primitiveFareySum f (m / g) := by
  have hgm : g ∣ m := Nat.dvd_of_mem_divisors hg
  have hg0 : 0 < g := Nat.pos_of_mem_divisors hg
  set φ : ℕ → ℕ := fun a => g * (a + 1) - 1 with hφ
  have hφ1 : ∀ a, φ a + 1 = g * (a + 1) := fun a => by
    simp only [hφ]
    have : 1 ≤ g * (a + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 := hφ1 a
    have h2 := hφ1 b
    rw [hab] at h1
    have : g * (a + 1) = g * (b + 1) := by omega
    have := Nat.eq_of_mul_eq_mul_left hg0 this
    omega
  have hsupp : (Function.support fun k : ℕ =>
      if Nat.gcd (k + 1) m = g then (𝓕 (f : ℝ → ℂ)) (((k : ℝ) + 1) / m) else 0) ⊆
      Set.range φ := by
    intro k hk
    have hk' : Nat.gcd (k + 1) m = g := by
      by_contra h
      exact hk (by simp [h])
    have hdvd : g ∣ k + 1 := hk' ▸ Nat.gcd_dvd_left (k + 1) m
    obtain ⟨b, hb⟩ := hdvd
    have hb0 : 0 < b := by
      rcases Nat.eq_zero_or_pos b with h | h
      · rw [h, mul_zero] at hb; omega
      · exact h
    refine ⟨b - 1, ?_⟩
    have := hφ1 (b - 1)
    rw [Nat.sub_add_cancel hb0] at this
    omega
  rw [← hinj.tsum_eq hsupp]
  unfold primitiveFareySum
  refine tsum_congr fun a => ?_
  have hk1 : φ a + 1 = g * (a + 1) := hφ1 a
  have hm' : m = g * (m / g) := (Nat.mul_div_cancel' hgm).symm
  have hgcd : Nat.gcd (φ a + 1) m = g * Nat.gcd (a + 1) (m / g) := by
    rw [hk1]
    conv_lhs => rw [hm']
    exact Nat.gcd_mul_left g (a + 1) (m / g)
  have hiff : Nat.gcd (φ a + 1) m = g ↔ Nat.Coprime (a + 1) (m / g) := by
    rw [hgcd, Nat.Coprime]
    constructor
    · intro h
      have := Nat.eq_of_mul_eq_mul_left hg0 (h.trans (mul_one g).symm)
      exact this
    · intro h
      rw [h, mul_one]
  have hval : (((φ a : ℕ) : ℝ) + 1) / m = (((a : ℕ) : ℝ) + 1) / ((m / g : ℕ) : ℝ) := by
    have hcast : ((φ a : ℕ) : ℝ) + 1 = (g : ℝ) * ((a : ℝ) + 1) := by
      exact_mod_cast hk1
    rw [hcast, Nat.cast_div hgm (by exact_mod_cast hg0.ne')]
    have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg0.ne'
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  by_cases h : Nat.Coprime (a + 1) (m / g)
  · rw [if_pos (hiff.mpr h), if_pos h, hval]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

/-- **Grouping by gcd.**  `Σ_{k≥1} F(k/m) = Σ_{q ∣ m} P_f(q)`. -/
theorem tsum_fareyDilate_eq_sum_divisors (f : SchwartzMap ℝ ℂ) {m : ℕ} (hm : 0 < m) :
    ∑ q ∈ m.divisors, primitiveFareySum f q = fareyDilateSum f m := by
  classical
  have hpt : ∀ k : ℕ, (𝓕 (f : ℝ → ℂ)) (((k : ℝ) + 1) / m) =
      ∑ g ∈ m.divisors,
        (if Nat.gcd (k + 1) m = g then (𝓕 (f : ℝ → ℂ)) (((k : ℝ) + 1) / m) else 0) := by
    intro k
    rw [Finset.sum_ite_eq]
    rw [if_pos (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hm.ne'⟩)]
  have hsum : ∀ g ∈ m.divisors, Summable fun k : ℕ =>
      (if Nat.gcd (k + 1) m = g then (𝓕 (f : ℝ → ℂ)) (((k : ℝ) + 1) / m) else 0) := by
    intro g _
    refine Summable.of_norm_bounded (summable_norm_fourier_dilate f hm) fun k => ?_
    split_ifs
    · exact le_rfl
    · simp
  unfold fareyDilateSum
  rw [tsum_congr hpt, Summable.tsum_finsetSum hsum]
  rw [← Nat.sum_div_divisors m (primitiveFareySum f)]
  exact Finset.sum_congr rfl fun g hg => (tsum_gcd_class_eq_primitiveFareySum f hm hg).symm

/-- **Dilated Poisson summation for an integer-blind function.** -/
theorem fareyDilateSum_of_blind {f : SchwartzMap ℝ ℂ} (heven : ∀ x : ℝ, f (-x) = f x)
    (h0 : f 0 = 0) (hblind : ∀ n : ℕ, 2 ≤ n → f n = 0) {m : ℕ} (hm : 0 < m) :
    fareyDilateSum f m =
      (if m = 1 then f 1 else 0) - (𝓕 (f : ℝ → ℂ)) 0 / 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsum : Summable fun n : ℕ => f ((m : ℝ) * ((n : ℝ) + 1)) :=
    HTGeometry.summable_schwartzDilate f hmR
  have hsumF : Summable fun n : ℕ => (𝓕 (f : ℝ → ℂ)) (((n : ℝ) + 1) / m) :=
    summable_fourier_dilate f hm
  have hP := even_poisson_summation_dilate f heven hmR hsum hsumF
  have hL : (∑' n : ℕ, f ((m : ℝ) * ((n : ℝ) + 1))) = if m = 1 then f 1 else 0 := by
    have hval : ∀ n : ℕ, f ((m : ℝ) * ((n : ℝ) + 1)) =
        if n = 0 ∧ m = 1 then f 1 else 0 := by
      intro n
      have hcast : (m : ℝ) * ((n : ℝ) + 1) = ((m * (n + 1) : ℕ) : ℝ) := by push_cast; ring
      by_cases h : n = 0 ∧ m = 1
      · obtain ⟨rfl, rfl⟩ := h
        simp
      · rw [if_neg h, hcast]
        apply hblind
        rcases Nat.lt_or_ge 1 m with h1 | h1
        · nlinarith
        · have hm1 : m = 1 := by omega
          have hn : n ≠ 0 := fun hn => h ⟨hn, hm1⟩
          subst hm1
          omega
    rw [tsum_congr hval]
    by_cases hm1 : m = 1
    · rw [if_pos hm1, tsum_eq_single 0 (fun n hn => by simp [hn])]
      simp [hm1]
    · simp [hm1]
  rw [h0, hL, zero_add] at hP
  unfold fareyDilateSum
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hm1 : (if m = 1 then f 1 else 0) * (m : ℂ) = (if m = 1 then f 1 else 0) := by
    by_cases h : m = 1
    · simp [h]
    · simp [h]
  rw [Complex.ofReal_natCast] at hP
  set X := (𝓕 (f : ℝ → ℂ)) 0 + 2 * ∑' n : ℕ, (𝓕 (f : ℝ → ℂ)) (((n : ℝ) + 1) / m) with hXdef
  have hX : X = 2 * (if m = 1 then f 1 else 0) := by
    calc X = (m : ℂ) * ((m : ℂ)⁻¹ * X) := by field_simp
      _ = (m : ℂ) * (2 * (if m = 1 then f 1 else 0)) := by rw [← hP]
      _ = 2 * ((if m = 1 then f 1 else 0) * (m : ℂ)) := by ring
      _ = 2 * (if m = 1 then f 1 else 0) := by rw [hm1]
  rw [hXdef] at hX
  linear_combination hX / 2

theorem sum_divisorsAntidiagonal_moebius_eq_zero {q : ℕ} (hq : 2 ≤ q) :
    ∑ x ∈ q.divisorsAntidiagonal, (μ x.1 : ℂ) = 0 := by
  have h := congrArg (fun F : ArithmeticFunction ℤ => F q) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply, ArithmeticFunction.one_apply] at h
  have hne : q ≠ 1 := by omega
  rw [if_neg hne] at h
  have h' : ∑ x ∈ q.divisorsAntidiagonal, (μ x.1 : ℤ) = 0 := by
    rw [← h]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx2 : x.2 ≠ 0 := by
      have := Nat.mem_divisorsAntidiagonal.mp hx
      intro h0
      rw [h0, mul_zero] at this
      omega
    simp [hx2]
  exact_mod_cast h'

/-- **Integer blindness gives the Möbius law for primitive Farey sums.** -/
theorem primitiveFareySum_eq_moebius_mul {f : SchwartzMap ℝ ℂ} (heven : ∀ x : ℝ, f (-x) = f x)
    (h0 : f 0 = 0) (hblind : ∀ n : ℕ, 2 ≤ n → f n = 0) {q : ℕ} (hq : 2 ≤ q) :
    primitiveFareySum f q = (μ q : ℂ) * f 1 := by
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
    (f := primitiveFareySum f) (g := fareyDilateSum f)).mp
    (fun n hn => tsum_fareyDilate_eq_sum_divisors f hn) q (by omega)
  rw [← hinv]
  have hV : ∀ x ∈ q.divisorsAntidiagonal, μ x.1 • fareyDilateSum f x.2 =
      (μ x.1 : ℂ) * (-((𝓕 (f : ℝ → ℂ)) 0 / 2)) + (if x.2 = 1 then (μ x.1 : ℂ) * f 1 else 0) := by
    intro x hx
    have hx2 : 0 < x.2 := by
      have := Nat.mem_divisorsAntidiagonal.mp hx
      rcases Nat.eq_zero_or_pos x.2 with h | h
      · rw [h, mul_zero] at this; omega
      · exact h
    rw [fareyDilateSum_of_blind heven h0 hblind hx2, zsmul_eq_mul]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hV, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_divisorsAntidiagonal_moebius_eq_zero hq, zero_mul, zero_add]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hfilter : (q.divisorsAntidiagonal.filter fun x : ℕ × ℕ => x.2 = 1) = {(q, 1)} := by
    ext x
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hx, -⟩, h1⟩
      rw [h1, mul_one] at hx
      exact Prod.ext hx h1
    · rintro rfl
      exact ⟨⟨mul_one q, by omega⟩, rfl⟩
  rw [hfilter, Finset.sum_singleton]

/-- **Blind tests carry the Mertens function in their Farey sums.**  For an integer-blind even
Schwartz `f` and every `Q ≥ 1`, the cumulative primitive Farey sums of `𝓕 f` are
`P_f(1) + f(1) · (M(Q) − 1)`, with `M(Q) = Σ_{q ≤ Q} μ(q)` the Mertens function. -/
theorem sum_primitiveFareySum_eq_mertens {f : SchwartzMap ℝ ℂ} (heven : ∀ x : ℝ, f (-x) = f x)
    (h0 : f 0 = 0) (hblind : ∀ n : ℕ, 2 ≤ n → f n = 0) (Q : ℕ) :
    ∑ q ∈ Finset.Icc 1 (Q + 1), primitiveFareySum f q =
      primitiveFareySum f 1 + f 1 * ((∑ q ∈ Finset.Icc 1 (Q + 1), (μ q : ℂ)) - 1) := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ Q + 1 + 1 by omega) (fun q => primitiveFareySum f q),
      Finset.sum_Icc_succ_top (show 1 ≤ Q + 1 + 1 by omega) (fun q => (μ q : ℂ)), ih,
      primitiveFareySum_eq_moebius_mul heven h0 hblind (by omega : 2 ≤ Q + 1 + 1)]
    ring

/-! ### The converse for compactly supported functions -/

/-- Dilated Poisson summation in general form. -/
theorem fareyDilate_poisson {f : SchwartzMap ℝ ℂ} (heven : ∀ x : ℝ, f (-x) = f x) {m : ℕ}
    (hm : 0 < m) :
    f 0 + 2 * ∑' n : ℕ, f ((m : ℝ) * ((n : ℝ) + 1)) =
      (m : ℂ)⁻¹ * ((𝓕 (f : ℝ → ℂ)) 0 + 2 * fareyDilateSum f m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hP := even_poisson_summation_dilate f heven hmR
    (HTGeometry.summable_schwartzDilate f hmR) (summable_fourier_dilate f hm)
  rw [Complex.ofReal_natCast] at hP
  exact hP

theorem sum_divisors_moebius_eq_zero {m : ℕ} (hm : 2 ≤ m) : ∑ q ∈ m.divisors, (μ q : ℂ) = 0 := by
  rw [← Nat.sum_divisorsAntidiagonal (fun a _ => (μ a : ℂ))]
  exact sum_divisorsAntidiagonal_moebius_eq_zero hm

/-- Under the Möbius law the dilated Fourier sums are constant for `m ≥ 2`. -/
theorem fareyDilateSum_of_moebius {f : SchwartzMap ℝ ℂ}
    (hF : ∀ q : ℕ, 2 ≤ q → primitiveFareySum f q = (μ q : ℂ) * f 1) {m : ℕ} (hm : 2 ≤ m) :
    fareyDilateSum f m = primitiveFareySum f 1 - f 1 := by
  have h1 : 1 ∈ m.divisors := Nat.one_mem_divisors.mpr (by omega)
  rw [← tsum_fareyDilate_eq_sum_divisors f (by omega), ← Finset.add_sum_erase _ _ h1]
  have hrest : ∑ q ∈ m.divisors.erase 1, primitiveFareySum f q =
      ∑ q ∈ m.divisors.erase 1, (μ q : ℂ) * f 1 := by
    refine Finset.sum_congr rfl fun q hq => hF q ?_
    have hq1 : q ≠ 1 := Finset.ne_of_mem_erase hq
    have hq0 : 0 < q := Nat.pos_of_mem_divisors (Finset.mem_of_mem_erase hq)
    omega
  rw [hrest, ← Finset.sum_mul]
  have hsum := sum_divisors_moebius_eq_zero hm
  rw [← Finset.add_sum_erase _ _ h1] at hsum
  simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one] at hsum
  have hneg : ∑ q ∈ m.divisors.erase 1, (μ q : ℂ) = -1 := by linear_combination hsum
  rw [hneg]
  ring

/-- **Downward induction over multiples.**  For a finitely supported sequence, vanishing of every
multiple sum `Σ_{n ≥ 1} a(mn)`, `m ≥ 2`, forces `a(m) = 0` for `m ≥ 2`. -/
theorem eq_zero_of_multiple_sums {a : ℕ → ℂ} {N : ℕ} (hsupp : ∀ k, N < k → a k = 0)
    (hH : ∀ m, 2 ≤ m → ∑' n : ℕ, a (m * (n + 1)) = 0) : ∀ m, 2 ≤ m → a m = 0 := by
  have key : ∀ j m, N + 1 - m = j → 2 ≤ m → a m = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro m hj hm
      by_cases hmN : N < m
      · exact hsupp m hmN
      · have hsum : Summable fun n : ℕ => a (m * (n + 1)) := by
          refine summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => ?_
          apply hsupp
          simp only [Finset.mem_range, not_lt] at hn
          nlinarith
        have hsplit := hsum.tsum_eq_zero_add
        rw [hH m hm] at hsplit
        have hrest : ∑' n : ℕ, a (m * (n + 1 + 1)) = 0 := by
          refine (tsum_congr fun n => ?_).trans tsum_zero
          by_cases hbig : N < m * (n + 1 + 1)
          · exact hsupp _ hbig
          · exact ih (N + 1 - m * (n + 1 + 1)) (by
              have : m < m * (n + 1 + 1) := by nlinarith
              omega) _ rfl (by nlinarith)
        simp only [zero_add, mul_one] at hsplit
        rw [hrest, add_zero] at hsplit
        exact hsplit.symm
  exact fun m hm => key _ m rfl hm

/-- **The Möbius law gives integer blindness** for compactly supported even Schwartz functions. -/
theorem blind_of_primitiveFareySum {f : SchwartzMap ℝ ℂ} (heven : ∀ x : ℝ, f (-x) = f x)
    {N : ℕ} (hsupp : ∀ x : ℝ, (N : ℝ) < |x| → f x = 0)
    (hF : ∀ q : ℕ, 2 ≤ q → primitiveFareySum f q = (μ q : ℂ) * f 1) :
    f 0 = 0 ∧ ∀ n : ℕ, 2 ≤ n → f n = 0 := by
  set C : ℂ := (𝓕 (f : ℝ → ℂ)) 0 + 2 * (primitiveFareySum f 1 - f 1) with hC
  clear_value C
  have hP : ∀ m : ℕ, 2 ≤ m →
      f 0 + 2 * ∑' n : ℕ, f ((m : ℝ) * ((n : ℝ) + 1)) = (m : ℂ)⁻¹ * C := by
    intro m hm
    rw [fareyDilate_poisson heven (by omega), fareyDilateSum_of_moebius hF hm, hC]
  have hbig : ∀ m : ℕ, N < m → ∑' n : ℕ, f ((m : ℝ) * ((n : ℝ) + 1)) = 0 := by
    intro m hm
    refine (tsum_congr fun n => hsupp _ ?_).trans tsum_zero
    have hmR : (N : ℝ) < m := by exact_mod_cast hm
    have h1 : (m : ℝ) ≤ (m : ℝ) * ((n : ℝ) + 1) := by
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hA := hP (N + 2) (by omega)
  have hB := hP (2 * N + 4) (by omega)
  rw [hbig _ (by omega), mul_zero, add_zero] at hA hB
  have hC0 : C = 0 := by
    have hN2 : ((N + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : N + 2 ≠ 0)
    have hN4 : ((2 * N + 4 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * N + 4 ≠ 0)
    have hA' : f 0 * ((N + 2 : ℕ) : ℂ) = C := by
      rw [hA, mul_comm, ← mul_assoc, mul_inv_cancel₀ hN2, one_mul]
    have hB' : f 0 * ((2 * N + 4 : ℕ) : ℂ) = C := by
      rw [hB, mul_comm, ← mul_assoc, mul_inv_cancel₀ hN4, one_mul]
    have h2 : ((2 * N + 4 : ℕ) : ℂ) = 2 * ((N + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [h2] at hB'
    linear_combination hB' - 2 * hA'
  have hf0 : f 0 = 0 := by rw [hA, hC0, mul_zero]
  refine ⟨hf0, ?_⟩
  have hH : ∀ m : ℕ, 2 ≤ m → ∑' n : ℕ, (fun k : ℕ => f k) (m * (n + 1)) = 0 := by
    intro m hm
    have := hP m hm
    rw [hf0, hC0, mul_zero, zero_add] at this
    have h2 : ∑' n : ℕ, f ((m : ℝ) * ((n : ℝ) + 1)) = 0 := by
      have := congrArg (· / 2) this
      simpa using this
    refine (tsum_congr fun n => ?_).trans h2
    simp only
    congr 1
    push_cast
    ring
  have hsuppN : ∀ k : ℕ, N < k → (fun k : ℕ => f k) k = 0 := by
    intro k hk
    apply hsupp
    have : (N : ℝ) < k := by exact_mod_cast hk
    rw [abs_of_nonneg (by positivity)]
    exact this
  exact eq_zero_of_multiple_sums hsuppN hH

/-- **Integer blindness ⟺ the Möbius law for primitive Farey sums**, for compactly supported even
Schwartz functions. -/
theorem blind_iff_primitiveFareySum {f : SchwartzMap ℝ ℂ} (heven : ∀ x : ℝ, f (-x) = f x)
    {N : ℕ} (hsupp : ∀ x : ℝ, (N : ℝ) < |x| → f x = 0) :
    (f 0 = 0 ∧ ∀ n : ℕ, 2 ≤ n → f n = 0) ↔
      ∀ q : ℕ, 2 ≤ q → primitiveFareySum f q = (μ q : ℂ) * f 1 :=
  ⟨fun h _ hq => primitiveFareySum_eq_moebius_mul heven h.1 h.2 hq,
    blind_of_primitiveFareySum heven hsupp⟩

/-! ### The pole term through Poisson summation -/

/-- **The pole term through Poisson summation.**  For an even Schwartz `f` with `f(0) = 0`,
`F(0) = 2f(1) − 2F(1) + 2Σ_{n≥2} f(n) − 2Σ_{k≥2} F(k)`, `F = 𝓕 f`.  For a Weil test `F(0)` is the
pole term. -/
theorem fourier_zero_eq_poisson {f : SchwartzMap ℝ ℂ} (heven : ∀ x : ℝ, f (-x) = f x)
    (h0 : f 0 = 0) :
    (𝓕 (f : ℝ → ℂ)) 0 = 2 * f 1 - 2 * (𝓕 (f : ℝ → ℂ)) 1 +
      2 * ∑' n : ℕ, f ((n : ℝ) + 2) - 2 * ∑' k : ℕ, (𝓕 (f : ℝ → ℂ)) ((k : ℝ) + 2) := by
  have hsum : Summable fun n : ℕ => f ((n : ℝ) + 1) := by
    simpa using HTGeometry.summable_schwartzDilate f (by norm_num : (0 : ℝ) < 1)
  have hsumF : Summable fun n : ℕ => (𝓕 (f : ℝ → ℂ)) ((n : ℝ) + 1) := by
    simpa using summable_fourier_dilate f (by norm_num : 0 < 1)
  have hP := even_poisson_summation f heven hsum hsumF
  rw [hsum.tsum_eq_zero_add, hsumF.tsum_eq_zero_add, h0] at hP
  have e1 : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := fun n => by push_cast; ring
  simp only [e1, Nat.cast_zero, zero_add] at hP
  linear_combination -hP

/-- For an integer-blind test the pole term is `2f(1) − 2Σ_{k≥1} F(k)`. -/
theorem fourier_zero_eq_of_blind {f : SchwartzMap ℝ ℂ} (heven : ∀ x : ℝ, f (-x) = f x)
    (h0 : f 0 = 0) (hblind : ∀ n : ℕ, 2 ≤ n → f n = 0) :
    (𝓕 (f : ℝ → ℂ)) 0 = 2 * f 1 - 2 * (𝓕 (f : ℝ → ℂ)) 1 -
      2 * ∑' k : ℕ, (𝓕 (f : ℝ → ℂ)) ((k : ℝ) + 2) := by
  have hz : ∑' n : ℕ, f ((n : ℝ) + 2) = 0 := by
    refine (tsum_congr fun n => ?_).trans tsum_zero
    have := hblind (n + 2) (by omega)
    simpa using this
  rw [fourier_zero_eq_poisson heven h0, hz]
  ring

/-- **Doubly blind tests.**  If `f(n) = 0` and `F(n) = 0` for every integer `n ≥ 2`, the pole term is
`F(0) = 2f(1) − 2F(1)`. -/
theorem fourier_zero_eq_of_doublyBlind {f : SchwartzMap ℝ ℂ} (heven : ∀ x : ℝ, f (-x) = f x)
    (h0 : f 0 = 0) (hblind : ∀ n : ℕ, 2 ≤ n → f n = 0)
    (hFblind : ∀ k : ℕ, 2 ≤ k → (𝓕 (f : ℝ → ℂ)) k = 0) :
    (𝓕 (f : ℝ → ℂ)) 0 = 2 * f 1 - 2 * (𝓕 (f : ℝ → ℂ)) 1 := by
  have hz : ∑' k : ℕ, (𝓕 (f : ℝ → ℂ)) ((k : ℝ) + 2) = 0 := by
    refine (tsum_congr fun k => ?_).trans tsum_zero
    have := hFblind (k + 2) (by omega)
    simpa using this
  rw [fourier_zero_eq_of_blind heven h0 hblind, hz]
  ring

end

end RHTower
