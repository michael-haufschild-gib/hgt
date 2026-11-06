import GaloisForLFunctions.ArithmeticProduction.ImpureEulerFactorsPassEveryUpperBound
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheWidthIsReadInOneWindow

/-!
# Barriers on prime sums are blind to purity

A barrier event constrains the prime walk `Σ_{p ∈ P} a(p) p^{−σ} cos(t log p)` of a weight `a` (`primeWalk`, `barrierEvent`). This module shows that such an
event by itself cannot decide window occupancy.

**The mimic.** For `A > 0` and large `V`, take a prime `p₀` just above `V^{1/A}` and `c = p₀^{½ + A/log V}`. The Euler factor `1 − c p₀^{−s}` has zeros on the line
`Re s = ½ + A/log V`, spaced by `2π/log p₀ < 1`, so **every** unit window of `[V, 2V]` holds a zero of depth `A/log V` (`exists_mimic_factor`). Yet `ζ(s)(1 − c p₀^{−s})` has
the same prime coefficients as `ζ` except at the single prime `p₀`, where they differ by `c`, and `c p₀^{−½} ≤ 8` uniformly in `A` and `V`. So its prime walk stays within `8`
of that of `ζ`, at every height and on every set of primes (`abs_primeWalk_mimicWeight_sub_le`), and barrier events transfer with a buffer of `8`
(`barrierEvent_subset_mimicWeight`).

**The pure field.** A finite Euler product with unimodular phases never vanishes on `Re s > 0` (`prod_one_sub_ne_zero`). Its partial prime sums obey every barrier the actual
walk obeys, and it has no zero at all.

So the same barrier data is carried by a field with no zero and by a field with a zero in every window. Any proof of `D_win` must use an input that sees the size of the
Euler factor at each prime. Examples are the sharp constant of a second moment (`impure_second_moment_floor`, APR) and the zero count, as opposed to an upper bound up to
constants.
-/

noncomputable section

open Complex MeasureTheory Filter Set

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

open GaloisForLFunctions.ArithmeticProduction

/-- The prime walk of a weight: `Re Σ_{p ∈ P} a(p) p^{−σ−it}`. -/
def primeWalk (a : ℕ → ℝ) (P : Finset ℕ) (σ t : ℝ) : ℝ :=
  ∑ p ∈ P, a p * (p : ℝ) ^ (-σ) * Real.cos (t * Real.log p)

/-- A barrier event: the walk along the prime sets `P k` stays under the curve `B k` for `k < K`. -/
def barrierEvent (a : ℕ → ℝ) (P : ℕ → Finset ℕ) (σ : ℝ) (B : ℕ → ℝ) (K : ℕ) : Set ℝ :=
  {t | ∀ k < K, primeWalk a (P k) σ t ≤ B k}

/-- The prime coefficients of `log ζ`: the constant `1`. -/
def pureWeight : ℕ → ℝ := fun _ => 1

/-- The prime coefficients of `log (ζ(s) (1 − c p₀^{−s}))`. -/
def mimicWeight (p₀ : ℕ) (c : ℝ) : ℕ → ℝ := fun n => 1 - if n = p₀ then c else 0

/-- **The mimic walk stays within `c p₀^{−σ}` of the pure walk**, at every height and on every set of primes. -/
theorem abs_primeWalk_mimicWeight_sub_le {p₀ : ℕ} {c : ℝ} (hc : 0 ≤ c) (P : Finset ℕ) (σ t : ℝ) :
    |primeWalk (mimicWeight p₀ c) P σ t - primeWalk pureWeight P σ t| ≤ c * (p₀ : ℝ) ^ (-σ) := by
  have hdiff : primeWalk (mimicWeight p₀ c) P σ t - primeWalk pureWeight P σ t =
      -∑ p ∈ P, (if p = p₀ then c else 0) * (p : ℝ) ^ (-σ) * Real.cos (t * Real.log p) := by
    unfold primeWalk
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [mimicWeight, pureWeight]
    ring
  rw [hdiff, abs_neg]
  have hsingle : ∑ p ∈ P, (if p = p₀ then c else 0) * (p : ℝ) ^ (-σ) * Real.cos (t * Real.log p) =
      if p₀ ∈ P then c * (p₀ : ℝ) ^ (-σ) * Real.cos (t * Real.log p₀) else 0 := by
    split_ifs with hmem
    · rw [Finset.sum_eq_single_of_mem p₀ hmem]
      · simp
      · intro q _ hq
        simp [hq]
    · refine Finset.sum_eq_zero fun q hq => ?_
      have hne : q ≠ p₀ := fun h => hmem (h ▸ hq)
      simp [hne]
  rw [hsingle]
  have hpow : 0 ≤ (p₀ : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  split_ifs
  · rw [abs_mul, abs_of_nonneg (mul_nonneg hc hpow)]
    exact mul_le_of_le_one_right (mul_nonneg hc hpow) (Real.abs_cos_le_one _)
  · simpa using mul_nonneg hc hpow

/-- **Barrier events transfer with a bounded buffer.** A barrier for the pure walk at the curve `B − e` is a barrier for the mimic walk at `B`, with `e = c p₀^{−σ}`. -/
theorem barrierEvent_subset_mimicWeight {p₀ : ℕ} {c : ℝ} (hc : 0 ≤ c) (P : ℕ → Finset ℕ) (σ : ℝ)
    (B : ℕ → ℝ) (K : ℕ) :
    barrierEvent pureWeight P σ (fun k => B k - c * (p₀ : ℝ) ^ (-σ)) K ⊆
      barrierEvent (mimicWeight p₀ c) P σ B K := by
  intro t ht k hk
  have h1 := ht k hk
  have h2 := abs_primeWalk_mimicWeight_sub_le (p₀ := p₀) hc (P k) σ t
  have h3 := (abs_le.mp h2).2
  simp only at h1
  linarith

/-- The converse transfer: a barrier for the mimic at `B − e` is a barrier for the pure walk at `B`. -/
theorem barrierEvent_mimicWeight_subset {p₀ : ℕ} {c : ℝ} (hc : 0 ≤ c) (P : ℕ → Finset ℕ) (σ : ℝ)
    (B : ℕ → ℝ) (K : ℕ) :
    barrierEvent (mimicWeight p₀ c) P σ (fun k => B k - c * (p₀ : ℝ) ^ (-σ)) K ⊆
      barrierEvent pureWeight P σ B K := by
  intro t ht k hk
  have h1 := ht k hk
  have h2 := abs_primeWalk_mimicWeight_sub_le (p₀ := p₀) hc (P k) σ t
  have h3 := (abs_le.mp h2).1
  simp only at h1
  linarith

/-- **The mimic of depth `A/log V`.** For `A > 0` and large `V` there are a prime `p₀` and `c > 0` with `c p₀^{−½} ≤ 8` such that `1 − c p₀^{−s}` has a zero on
`Re s = ½ + A/log V` in every unit window `(m, m + 1)`, for all `m ≥ 0`. -/
theorem exists_mimic_factor {A : ℝ} (hA : 0 < A) :
    ∀ᶠ V : ℝ in atTop, ∃ (p₀ : ℕ) (c : ℝ), p₀.Prime ∧ 0 < c ∧ c * (p₀ : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 8 ∧
      ∀ m : ℝ, ∃ s : ℂ, s.re = 1 / 2 + A / Real.log V ∧ m < s.im ∧ s.im < m + 1 ∧
        impureFactor p₀ c s = 0 := by
  have hlogV : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (Real.exp (A * (2 * Real.pi + 1)) + 2),
    eventually_ge_atTop (Real.exp 1),
    hlogV.eventually_ge_atTop (A * Real.log 4 + 1)] with V hV1 hV2 hV3
  have hexp0 := Real.exp_pos (A * (2 * Real.pi + 1))
  have hV0 : 0 < V := by linarith
  have hL : 0 < Real.log V := by
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have : 0 ≤ A * Real.log 4 := mul_nonneg hA.le h4
    linarith
  set Y : ℝ := V ^ (1 / A) with hY
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hV0 _
  have hlogY : Real.log Y = Real.log V / A := by
    rw [hY, Real.log_rpow hV0]
    ring
  have hLA : (2 * Real.pi + 1) ≤ Real.log V / A := by
    rw [le_div_iff₀ hA]
    have h1 := Real.log_le_log hexp0 (by linarith : Real.exp (A * (2 * Real.pi + 1)) ≤ V)
    rw [Real.log_exp] at h1
    linarith
  have hY1 : 1 ≤ Y := by
    rw [hY]
    exact Real.one_le_rpow (by linarith [Real.add_one_le_exp (A * (2 * Real.pi + 1))])
      (by positivity)
  obtain ⟨p₀, hp, hlow, hup⟩ := Nat.exists_prime_lt_and_le_two_mul (Nat.ceil Y)
    (by
      have : 0 < Nat.ceil Y := Nat.ceil_pos.mpr hY0
      omega)
  have hceil1 : (Nat.ceil Y : ℝ) < Y + 1 := Nat.ceil_lt_add_one hY0.le
  have hceil2 : Y ≤ Nat.ceil Y := Nat.le_ceil Y
  have hp1 : 1 < p₀ := hp.one_lt
  have hp0R : (0 : ℝ) < p₀ := by exact_mod_cast hp.pos
  have hlowR : Y < p₀ := by
    have : ((Nat.ceil Y : ℕ) : ℝ) < p₀ := by exact_mod_cast hlow
    linarith
  have hupR : (p₀ : ℝ) ≤ 4 * Y := by
    have : (p₀ : ℝ) ≤ 2 * (Nat.ceil Y : ℝ) := by exact_mod_cast hup
    linarith
  have hlogp_low : Real.log V / A ≤ Real.log p₀ := by
    rw [← hlogY]
    exact Real.log_le_log hY0 hlowR.le
  have hlogp_up : Real.log p₀ ≤ Real.log 4 + Real.log V / A := by
    have h := Real.log_le_log hp0R hupR
    rwa [Real.log_mul (by norm_num) hY0.ne', hlogY] at h
  have hlogp_pos : 0 < Real.log p₀ := by
    have : 0 < Real.log V / A := div_pos hL hA
    linarith
  set η : ℝ := 1 / 2 + A / Real.log V with hη
  refine ⟨p₀, (p₀ : ℝ) ^ η, hp, Real.rpow_pos_of_pos hp0R _, ?_, fun m => ?_⟩
  · -- the size of the factor on the critical line
    rw [← Real.rpow_add hp0R]
    have hexpo : η + -(1 / 2 : ℝ) = A / Real.log V := by rw [hη]; ring
    rw [hexpo, Real.rpow_def_of_pos hp0R]
    have hexp : Real.log p₀ * (A / Real.log V) ≤ 2 := by
      have h1 : Real.log p₀ * (A / Real.log V) ≤
          (Real.log 4 + Real.log V / A) * (A / Real.log V) :=
        mul_le_mul_of_nonneg_right hlogp_up (by positivity)
      have h2 : (Real.log 4 + Real.log V / A) * (A / Real.log V) =
          A * Real.log 4 / Real.log V + 1 := by
        field_simp
      have h3 : A * Real.log 4 / Real.log V ≤ 1 := by
        rw [div_le_one hL]
        linarith
      linarith
    calc Real.exp (Real.log p₀ * (A / Real.log V)) ≤ Real.exp 2 := Real.exp_le_exp.mpr hexp
      _ ≤ 8 := by
        have h1 := Real.exp_one_lt_d9
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        have h3 := Real.exp_pos 1
        rw [h2]
        nlinarith
  · -- the lattice of zeros
    obtain ⟨k, hk⟩ := exists_lattice_zero_near hp1 (m + 1 / 2)
    have hπ := Real.pi_pos
    have hspacing : Real.pi / Real.log p₀ < 1 / 2 := by
      rw [div_lt_iff₀ hlogp_pos]
      have : 2 * Real.pi + 1 ≤ Real.log p₀ := hLA.trans hlogp_low
      linarith
    have habs := abs_lt.mp (hk.trans_lt hspacing)
    have hreval : ((η : ℂ) + ((2 * Real.pi * k / Real.log p₀ : ℝ) : ℂ) * I).re = η := by
      rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    refine ⟨(η : ℂ) + ((2 * Real.pi * k / Real.log p₀ : ℝ) : ℂ) * I, hreval, ?_, ?_,
      impureFactor_rpow_eq_zero hp1 η k⟩
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
      linarith [habs.1]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
      linarith [habs.2]

/-- **Barrier data does not decide occupancy.** For `A > 0` and large `V` there is a weight whose prime walk stays within `8` of the pure walk at every height, on every set of
primes and on every line `Re s = σ ≥ ½`, and whose Euler factor has a zero of depth `A/log V` in every unit window. -/
theorem barrier_data_does_not_decide_occupancy {A : ℝ} (hA : 0 < A) :
    ∀ᶠ V : ℝ in atTop, ∃ (p₀ : ℕ) (c : ℝ), p₀.Prime ∧ 0 < c ∧
      (∀ (P : Finset ℕ) (σ t : ℝ), 1 / 2 ≤ σ →
        |primeWalk (mimicWeight p₀ c) P σ t - primeWalk pureWeight P σ t| ≤ 8) ∧
      ∀ m : ℝ, ∃ s : ℂ, s.re = 1 / 2 + A / Real.log V ∧ m < s.im ∧ s.im < m + 1 ∧
        riemannZeta s * impureFactor p₀ c s = 0 := by
  filter_upwards [exists_mimic_factor hA] with V ⟨p₀, c, hp, hc, hbound, hzero⟩
  refine ⟨p₀, c, hp, hc, fun P σ t hσ => ?_, fun m => ?_⟩
  · have h1 := abs_primeWalk_mimicWeight_sub_le (p₀ := p₀) hc.le P σ t
    have hp1 : (1 : ℝ) ≤ p₀ := by exact_mod_cast hp.one_le
    have h2 : (p₀ : ℝ) ^ (-σ) ≤ (p₀ : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    have h3 := mul_le_mul_of_nonneg_left h2 hc.le
    linarith
  · obtain ⟨s, h1, h2, h3, h4⟩ := hzero m
    exact ⟨s, h1, h2, h3, by rw [h4, mul_zero]⟩

/-- **The pure field has no zero.** A finite Euler product with phases of modulus at most one does not vanish on `Re s > 0`. -/
theorem prod_one_sub_ne_zero {P : Finset ℕ} (hP : ∀ p ∈ P, 1 < p) {z : ℕ → ℂ} (hz : ∀ p, ‖z p‖ ≤ 1)
    {s : ℂ} (hs : 0 < s.re) :
    ∏ p ∈ P, (1 - z p * (p : ℂ) ^ (-s)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun p hp hzero => ?_
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hP p hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hnorm : ‖z p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hp0)]
    have h1 : (p : ℝ) ^ (-s).re < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hp1 (by simpa using hs)
    have h2 := mul_le_mul_of_nonneg_right (hz p) (Real.rpow_nonneg hp0.le (-s).re)
    linarith
  have heq : z p * (p : ℂ) ^ (-s) = 1 := by
    linear_combination -hzero
  rw [heq, norm_one] at hnorm
  exact lt_irrefl _ hnorm

end GaloisForLFunctions.MultiscaleMollifiedZetaField
