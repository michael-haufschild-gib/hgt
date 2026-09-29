import GaloisForLFunctions.RHTower.MobiusCubicSourceExponentLaw
import GaloisForLFunctions.RHTower.MobiusDecayZeroObstruction
import GaloisForLFunctions.RHTower.MobiusLaplaceAdditiveTriangle

/-!
# Absolute moments of the Mertens function

Let `M(k) = Σ_{n≤k} μ(n)` and `Θ = sup Re ρ`. For `p ≥ 1` and `c ≥ 1` with `c ≠ pΘ + 1`,

```text
Σ_{k≤X} |M(k)|^p = O(X^c)    ⟺    pΘ + 1 < c .
```

At `p = 1` the left side is the one-dimensional transport cost `Σ_k |F⁺(k) − F⁻(k)|` between the
positive and negative parts of `μ`, the cost of any sign-matching argument. These moments, like the
quadratic ones, are receivers with the zero abscissa as threshold.

Mechanism.
* Lower direction: Hölder reduces to `p = 1`. Two Abel summations give
  `|Σ μ(n) e^{-nx}| ≤ (1 − e^{-x})² Σ_N (Σ_{k≤N} |M(k)|) e^{-Nx} ≪ x^{1−c}`, and a zeta zero with
  `Re ρ > c − 1` obstructs this decay of the Möbius–Laplace source.
* Upper direction: Littlewood's bound `M(k) = O(k^{Θ+ε})`.
-/

noncomputable section

open Finset Complex

namespace RHTower

theorem norm_mobiusMertensPartialSum_le (N : ℕ) :
    ‖mobiusMertensPartialSum N‖ ≤ (N : ℝ) + 1 := by
  rw [mobiusMertensPartialSum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n ∈ range (N + 1), ‖mobiusComplexCoefficient n‖
      ≤ ∑ _n ∈ range (N + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => norm_mobiusCoeff_le_one n
    _ = (N : ℝ) + 1 := by simp

/-- **Transport cost controls the Möbius–Laplace source.** If `Σ_{k≤X} |M(k)| ≤ C (X+1)^c` with
`c ≥ 1`, then `|Σ μ(n) e^{-nx}| ≪ x^{-(c-1)}` as `x → 0⁺`. -/
theorem mobiusDiscreteLaplaceDecay_of_sum_norm_mertens_le {C c : ℝ} (hc : 1 ≤ c)
    (hS : ∀ X : ℕ, ∑ k ∈ range (X + 1), ‖mobiusMertensPartialSum k‖ ≤ C * ((X : ℝ) + 1) ^ c) :
    MobiusDiscreteLaplaceDecay (c - 1) := by
  have hC : 0 ≤ C := by
    have hnn : 0 ≤ ∑ k ∈ range (0 + 1), ‖mobiusMertensPartialSum k‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have := hnn.trans (hS 0)
    simpa using this
  have hc0 : 0 ≤ c := by linarith
  refine ⟨4 * C * Real.exp 1 * ((2 * c) ^ c * Real.exp (-c)), 1, by positivity, one_pos,
    fun x hx hx1 => ?_⟩
  set r : ℝ := Real.exp (-x) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h1r : 1 - r ≤ x := by
    have := Real.add_one_le_exp (-x)
    rw [← hr] at this
    linarith
  have h1r0 : 0 ≤ 1 - r := by linarith
  set B : ℝ := (2 * c / x) ^ c * Real.exp (-c) * (4 / x) with hB
  have hrn : ∀ n : ℕ, r ^ n = Real.exp x * Real.exp (-(((n : ℝ) + 1) * x)) := by
    intro n
    rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  set g : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ c * r ^ n with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by positivity
  have hgpartial : ∀ m : ℕ, ∑ n ∈ range m, g n ≤ Real.exp x * B := by
    intro m
    have hfin := CubicGamma.sum_rpow_mul_exp_neg_le hc0 hx hx1.le m
    calc ∑ n ∈ range m, g n
        = Real.exp x * ∑ n ∈ range m, ((n : ℝ) + 1) ^ c * Real.exp (-(((n : ℝ) + 1) * x)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [hg]
          simp only
          rw [hrn n]
          ring
      _ ≤ Real.exp x * B := mul_le_mul_of_nonneg_left hfin (Real.exp_pos x).le
  have hgsum : Summable g := summable_of_sum_range_le hg0 hgpartial
  have hgtsum : ∑' n, g n ≤ Real.exp x * B := Real.tsum_le_of_sum_range_le hg0 hgpartial
  set M : ℕ → ℂ := mobiusMertensPartialSum with hM
  have hMle : ∀ N : ℕ, ‖M N‖ * r ^ N ≤ g N := by
    intro N
    have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
    have hpow : (N : ℝ) + 1 ≤ ((N : ℝ) + 1) ^ c := by
      simpa using Real.rpow_le_rpow_of_exponent_le hN1 hc
    exact mul_le_mul_of_nonneg_right ((norm_mobiusMertensPartialSum_le N).trans hpow)
      (by positivity)
  set S : ℕ → ℝ := fun N => ∑ k ∈ range (N + 1), ‖M k‖ with hSdef
  have hSle : ∀ N : ℕ, S N * r ^ N ≤ C * g N := by
    intro N
    have := mul_le_mul_of_nonneg_right (hS N) (pow_nonneg hr0.le N)
    calc S N * r ^ N ≤ C * ((N : ℝ) + 1) ^ c * r ^ N := this
      _ = C * g N := by rw [hg]; ring
  -- summability of the three series
  have hnormM : Summable (fun N : ℕ => ‖M N‖ * r ^ N) :=
    Summable.of_nonneg_of_le (fun N => by positivity) hMle hgsum
  have hSsum : Summable (fun N : ℕ => S N * r ^ N) :=
    Summable.of_nonneg_of_le
      (fun N => mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (by positivity))
      hSle (hgsum.mul_left C)
  have hnormr : ‖((r : ℝ) : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hcsum : Summable (fun n : ℕ => mobiusCoeff n * ((r : ℝ) : ℂ) ^ n) :=
    (summable_norm_mobiusCoeff_mul_pow hx).of_norm
  have hTnorm : ∀ N : ℕ,
      ‖(∑ k ∈ range (N + 1), mobiusCoeff k) * ((r : ℝ) : ℂ) ^ N‖ = ‖M N‖ * r ^ N := by
    intro N
    rw [norm_mul, norm_pow, hnormr]
    rfl
  have hTsum : Summable (fun N : ℕ => (∑ k ∈ range (N + 1), mobiusCoeff k) * ((r : ℝ) : ℂ) ^ N) :=
    Summable.of_norm (by simpa only [hTnorm] using hnormM)
  -- first Abel summation, complex
  have habel1 := tsum_mul_pow_eq_one_sub_mul_tsum_partialSums mobiusCoeff ((r : ℝ) : ℂ)
    hcsum hTsum
  -- second Abel summation, real
  have hcsum' : Summable (fun N : ℕ => ‖M N‖ * r ^ N) := hnormM
  have habel2 := tsum_mul_pow_eq_one_sub_mul_tsum_partialSums (K := ℝ) (fun N => ‖M N‖) r
    hcsum' hSsum
  have hstep1 : ‖mobiusDiscreteLaplaceTransform x‖ ≤ (1 - r) * ∑' N : ℕ, ‖M N‖ * r ^ N := by
    rw [mobiusDiscreteLaplaceTransform_eq_tsum, ← hr, habel1, norm_mul]
    have h1 : ‖(1 : ℂ) - ((r : ℝ) : ℂ)‖ = 1 - r := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg h1r0]
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ h1r0
    refine (norm_tsum_le_tsum_norm (by simpa only [hTnorm] using hnormM)).trans (le_of_eq ?_)
    exact tsum_congr hTnorm
  have hstep2 : ∑' N : ℕ, ‖M N‖ * r ^ N ≤ (1 - r) * (C * (Real.exp x * B)) := by
    rw [habel2]
    refine mul_le_mul_of_nonneg_left ?_ h1r0
    calc ∑' N : ℕ, (∑ k ∈ range (N + 1), ‖M k‖) * r ^ N
        ≤ ∑' N : ℕ, C * g N := Summable.tsum_le_tsum hSle hSsum (hgsum.mul_left C)
      _ = C * ∑' N : ℕ, g N := tsum_mul_left
      _ ≤ C * (Real.exp x * B) := mul_le_mul_of_nonneg_left hgtsum hC
  have hexp : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hx1.le
  have hB0 : 0 ≤ B := by positivity
  have hxc : (2 * c / x) ^ c = (2 * c) ^ c * x ^ (-c) := by
    rw [Real.div_rpow (by positivity) hx.le, Real.rpow_neg hx.le, div_eq_mul_inv]
  calc ‖mobiusDiscreteLaplaceTransform x‖
      ≤ (1 - r) * ((1 - r) * (C * (Real.exp x * B))) :=
        hstep1.trans (mul_le_mul_of_nonneg_left hstep2 h1r0)
    _ ≤ x * (x * (C * (Real.exp 1 * B))) := by
        gcongr
    _ = 4 * C * Real.exp 1 * ((2 * c) ^ c * Real.exp (-c)) * (x * x ^ (-c)) := by
        rw [hB, hxc]
        field_simp
    _ = 4 * C * Real.exp 1 * ((2 * c) ^ c * Real.exp (-c)) * x ^ (-(c - 1)) := by
        congr 1
        rw [show -(c - 1) = 1 + -c by ring, Real.rpow_add hx, Real.rpow_one]

/-- **Transport-cost exponent bound.** `Σ_{k≤X} |M(k)| = O(X^c)` with `c ≥ 1` forces `Θ ≤ c − 1`. -/
theorem zetaZeroAbscissa_le_of_sum_norm_mertens_le {C c : ℝ} (hc : 1 ≤ c)
    (hS : ∀ X : ℕ, ∑ k ∈ range (X + 1), ‖mobiusMertensPartialSum k‖ ≤ C * ((X : ℝ) + 1) ^ c) :
    zetaZeroAbscissa ≤ c - 1 := by
  by_contra h
  rw [not_le] at h
  obtain ⟨ρ, hzero, hρ1, hρre⟩ := exists_zetaZero_mem_openStrip_lt_re h
  refine not_mobiusDiscreteLaplaceDecay_of_riemannZeta_eq_zero (by linarith) hρre ?_ hzero
    (mobiusDiscreteLaplaceDecay_of_sum_norm_mertens_le hc hS)
  intro h1
  rw [h1, Complex.one_re] at hρ1
  exact lt_irrefl 1 hρ1

/-- Hölder for a finite sum against the constant weight: `Σ z ≤ n^{1−1/p} (Σ z^p)^{1/p}`. -/
theorem sum_le_card_rpow_mul_sum_rpow {s : Finset ℕ} {z : ℕ → ℝ} (hz : ∀ i ∈ s, 0 ≤ z i)
    {p : ℝ} (hp : 1 ≤ p) :
    ∑ i ∈ s, z i ≤ (s.card : ℝ) ^ (1 - p⁻¹) * (∑ i ∈ s, z i ^ p) ^ p⁻¹ := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp only [Finset.sum_empty, Finset.card_empty]
    have hp0 : p⁻¹ ≠ 0 := inv_ne_zero (by linarith)
    rw [Real.zero_rpow hp0, mul_zero]
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hp0 : 0 < p := by linarith
  set n : ℝ := (s.card : ℝ) with hn_def
  have hw : ∑ i ∈ s, (fun _ : ℕ => n⁻¹) i = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← hn_def]
    field_simp
  have hpm := Real.rpow_arith_mean_le_arith_mean_rpow s (fun _ => n⁻¹) z
    (fun _ _ => inv_nonneg.mpr hn.le) hw hz hp
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hpm
  have hsum0 : 0 ≤ ∑ i ∈ s, z i := Finset.sum_nonneg hz
  have hsump0 : 0 ≤ ∑ i ∈ s, z i ^ p :=
    Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hz i hi) p
  have hroot := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) p) hpm
    (inv_nonneg.mpr hp0.le)
  rw [Real.rpow_rpow_inv (by positivity) hp0.ne', Real.mul_rpow (by positivity) hsump0] at hroot
  have hn1 : n * (n⁻¹) ^ p⁻¹ = n ^ (1 - p⁻¹) := by
    rw [Real.inv_rpow hn.le, Real.rpow_sub hn, Real.rpow_one, div_eq_mul_inv]
  calc ∑ i ∈ s, z i = n * (n⁻¹ * ∑ i ∈ s, z i) := by field_simp
    _ ≤ n * ((n⁻¹) ^ p⁻¹ * (∑ i ∈ s, z i ^ p) ^ p⁻¹) :=
        mul_le_mul_of_nonneg_left hroot hn.le
    _ = n ^ (1 - p⁻¹) * (∑ i ∈ s, z i ^ p) ^ p⁻¹ := by rw [← mul_assoc, hn1]

/-- **Absolute-moment exponent bound.** `Σ_{k≤X} |M(k)|^p = O(X^c)` with `p ≥ 1`, `c ≥ 1` forces
`pΘ + 1 ≤ c`. -/
theorem zetaZeroAbscissa_le_of_sum_norm_mertens_rpow_le {C c p : ℝ} (hp : 1 ≤ p) (hc : 1 ≤ c)
    (hS : ∀ X : ℕ,
      ∑ k ∈ range (X + 1), ‖mobiusMertensPartialSum k‖ ^ p ≤ C * ((X : ℝ) + 1) ^ c) :
    p * zetaZeroAbscissa + 1 ≤ c := by
  have hp0 : 0 < p := by linarith
  have hC : 0 ≤ C := by
    have hnn : 0 ≤ ∑ k ∈ range (0 + 1), ‖mobiusMertensPartialSum k‖ ^ p :=
      Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) p
    have := hnn.trans (hS 0)
    simpa using this
  set c₁ : ℝ := 1 - p⁻¹ + c * p⁻¹ with hc₁
  have hc₁1 : 1 ≤ c₁ := by
    have : 0 ≤ (c - 1) * p⁻¹ := mul_nonneg (by linarith) (inv_nonneg.mpr hp0.le)
    rw [hc₁]; nlinarith
  have hL1 : ∀ X : ℕ, ∑ k ∈ range (X + 1), ‖mobiusMertensPartialSum k‖ ≤
      C ^ p⁻¹ * ((X : ℝ) + 1) ^ c₁ := by
    intro X
    have hX : (0 : ℝ) < (X : ℝ) + 1 := by positivity
    have hH := sum_le_card_rpow_mul_sum_rpow (s := range (X + 1))
      (z := fun k => ‖mobiusMertensPartialSum k‖) (fun _ _ => norm_nonneg _) hp
    rw [Finset.card_range] at hH
    push_cast at hH
    have hroot : (∑ k ∈ range (X + 1), ‖mobiusMertensPartialSum k‖ ^ p) ^ p⁻¹ ≤
        (C * ((X : ℝ) + 1) ^ c) ^ p⁻¹ :=
      Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) p) (hS X)
        (inv_nonneg.mpr hp0.le)
    rw [Real.mul_rpow hC (by positivity), ← Real.rpow_mul hX.le] at hroot
    calc ∑ k ∈ range (X + 1), ‖mobiusMertensPartialSum k‖
        ≤ ((X : ℝ) + 1) ^ (1 - p⁻¹) *
            (∑ k ∈ range (X + 1), ‖mobiusMertensPartialSum k‖ ^ p) ^ p⁻¹ := hH
      _ ≤ ((X : ℝ) + 1) ^ (1 - p⁻¹) * (C ^ p⁻¹ * ((X : ℝ) + 1) ^ (c * p⁻¹)) :=
          mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = C ^ p⁻¹ * ((X : ℝ) + 1) ^ c₁ := by
          rw [hc₁, Real.rpow_add hX]
          ring
  have h := zetaZeroAbscissa_le_of_sum_norm_mertens_le hc₁1 hL1
  rw [hc₁] at h
  have h2 : p * zetaZeroAbscissa ≤ p * ((c - 1) * p⁻¹) := by
    apply mul_le_mul_of_nonneg_left _ hp0.le
    linarith
  rw [show p * ((c - 1) * p⁻¹) = c - 1 by field_simp] at h2
  linarith

/-- **Upper direction.** Right of the threshold, Littlewood's bound gives the moment bound. -/
theorem exists_sum_norm_mertens_rpow_le_of_lt {c p : ℝ} (hp : 1 ≤ p)
    (hlt : p * zetaZeroAbscissa + 1 < c) :
    ∃ C : ℝ, ∀ X : ℕ,
      ∑ k ∈ range (X + 1), ‖mobiusMertensPartialSum k‖ ^ p ≤ C * ((X : ℝ) + 1) ^ c := by
  have hp0 : 0 < p := by linarith
  set ε : ℝ := (c - 1 - p * zetaZeroAbscissa) / (2 * p) with hε
  have hε0 : 0 < ε := by rw [hε]; apply div_pos <;> linarith
  obtain ⟨C₀, hC₀, hbound⟩ := mobiusMertens_subpower_zetaZeroAbscissa ε hε0
  have hΘ := half_le_zetaZeroAbscissa
  have ha0 : 0 ≤ p * (zetaZeroAbscissa + ε) := by positivity
  have hexp : p * (zetaZeroAbscissa + ε) + 1 ≤ c := by
    have : p * ε = (c - 1 - p * zetaZeroAbscissa) / 2 := by rw [hε]; field_simp
    nlinarith
  refine ⟨C₀ ^ p, fun X => ?_⟩
  have hX1 : (1 : ℝ) ≤ (X : ℝ) + 1 := by have : (0 : ℝ) ≤ X := Nat.cast_nonneg X; linarith
  have hterm : ∀ k ∈ range (X + 1), ‖mobiusMertensPartialSum k‖ ^ p ≤
      C₀ ^ p * ((X : ℝ) + 1) ^ (p * (zetaZeroAbscissa + ε)) := by
    intro k hk
    have hk : (k : ℝ) + 1 ≤ (X : ℝ) + 1 := by
      have := Finset.mem_range.mp hk
      have : (k : ℝ) ≤ X := by exact_mod_cast Nat.lt_succ_iff.mp this
      linarith
    calc ‖mobiusMertensPartialSum k‖ ^ p
        ≤ (C₀ * ((k : ℝ) + 1) ^ (zetaZeroAbscissa + ε)) ^ p :=
          Real.rpow_le_rpow (norm_nonneg _) (hbound k) hp0.le
      _ = C₀ ^ p * ((k : ℝ) + 1) ^ (p * (zetaZeroAbscissa + ε)) := by
          rw [Real.mul_rpow hC₀ (by positivity), ← Real.rpow_mul (by positivity), mul_comm p]
      _ ≤ C₀ ^ p * ((X : ℝ) + 1) ^ (p * (zetaZeroAbscissa + ε)) := by
          gcongr
  calc ∑ k ∈ range (X + 1), ‖mobiusMertensPartialSum k‖ ^ p
      ≤ ∑ _k ∈ range (X + 1), C₀ ^ p * ((X : ℝ) + 1) ^ (p * (zetaZeroAbscissa + ε)) :=
        Finset.sum_le_sum hterm
    _ = C₀ ^ p * ((X : ℝ) + 1) ^ (p * (zetaZeroAbscissa + ε) + 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          Real.rpow_add (by positivity), Real.rpow_one]
        push_cast
        ring
    _ ≤ C₀ ^ p * ((X : ℝ) + 1) ^ c := by
        gcongr

/-- **Absolute-moment exponent law for the Mertens function.** For `p ≥ 1` and `c ≥ 1` with
`c ≠ pΘ + 1`: `Σ_{k≤X} |M(k)|^p = O(X^c)` iff `pΘ + 1 < c`. At `p = 1` this is the transport cost
between the positive and negative parts of `μ`, so sign-matching carriers are receivers with the
same threshold as the quadratic ones. -/
theorem exists_sum_norm_mertens_rpow_le_iff {c p : ℝ} (hp : 1 ≤ p) (hc : 1 ≤ c)
    (hne : c ≠ p * zetaZeroAbscissa + 1) :
    (∃ C : ℝ, ∀ X : ℕ,
      ∑ k ∈ range (X + 1), ‖mobiusMertensPartialSum k‖ ^ p ≤ C * ((X : ℝ) + 1) ^ c) ↔
      p * zetaZeroAbscissa + 1 < c := by
  constructor
  · rintro ⟨C, hS⟩
    exact lt_of_le_of_ne (zetaZeroAbscissa_le_of_sum_norm_mertens_rpow_le hp hc hS)
      (fun h => hne h.symm)
  · exact exists_sum_norm_mertens_rpow_le_of_lt hp

end RHTower
