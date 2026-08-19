import Mathlib
import GaloisForLFunctions.RHTower.RegularizedDivisorHarmonicLimit
import GaloisForLFunctions.RHTower.GeometricMomentRational

/-!
# The γ-affine structure of the single-prime Stieltjes lanes at every order

For a prime `p` and an order `β ≥ 1` the generalized Stieltjes structure constant of the
single-prime multi-index `β·e_p` is the regularized limit

```text
A_{β,p} = reg-lim_{N → ∞} ( ∑_{k ≤ N} v_p(k)^β / k − D_{β,p} · log N ).
```

The prime-power ladder writes `v_p(k)^β` as a divisor sum: with `c_i = i^β − (i−1)^β` supported on
`i ≥ 1`,

```text
v_p(k)^β = ∑_{i ≤ v_p(k)} c_i = ∑_{d ∣ k} a_d,   a_{p^i} = c_i,  a_d = 0 otherwise.
```

Feeding this coefficient field to `RegularizedDivisorHarmonic.tendsto_regularizedDivisorHarmonic`
gives the limit, with

```text
D_{β,p} = ∑_{i ≥ 1} c_i p^{-i},        A_{β,p} = γ·D_{β,p} − (log p)·∑_{i ≥ 1} i c_i p^{-i}.
```

Both coefficients are therefore visible as explicit convergent prime-power series; the γ-lane and
the `log p`-lane are exactly separated.  This is the single-prime instance of the card's γ-affine
structure theorem at arbitrary order.
-/

open Finset Filter Topology

namespace RHTower
namespace StieltjesGammaAffine

open RegularizedDivisorHarmonic

noncomputable section

/-! ### The ladder increments -/

/-- The order-`β` ladder increment `c_i = i^β − (i−1)^β`. -/
def ladderCoeff (β i : ℕ) : ℝ := (i : ℝ) ^ β - ((i - 1 : ℕ) : ℝ) ^ β

@[simp] theorem ladderCoeff_zero (β : ℕ) : ladderCoeff β 0 = 0 := by simp [ladderCoeff]

theorem ladderCoeff_nonneg (β i : ℕ) : 0 ≤ ladderCoeff β i := by
  rw [ladderCoeff, sub_nonneg]
  have h : ((i - 1 : ℕ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast Nat.sub_le i 1
  have h0 : (0 : ℝ) ≤ ((i - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  gcongr

/-- **Telescoping.**  The ladder increments sum to the power. -/
theorem sum_ladderCoeff {β : ℕ} (hβ : 1 ≤ β) (a : ℕ) :
    ∑ i ∈ Finset.Icc 1 a, ladderCoeff β i = (a : ℝ) ^ β := by
  induction a with
  | zero =>
    simp only [Nat.cast_zero]
    rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) by decide]
    simp [zero_pow (by omega : β ≠ 0)]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, ladderCoeff]
    simp

/-! ### The single-prime divisor coefficient field -/

/-- The single-prime order-`β` divisor coefficient: `a_{p^i} = c_i`, and `0` off the powers
of `p`. -/
def primePowerLadder (p β : ℕ) (d : ℕ) : ℝ :=
  if p ^ (padicValNat p d) = d ∧ d ≠ 0 then ladderCoeff β (padicValNat p d) else 0

theorem primePowerLadder_zero (p β : ℕ) : primePowerLadder p β 0 = 0 := by
  rw [primePowerLadder, if_neg]
  rintro ⟨-, h⟩
  exact h rfl

theorem primePowerLadder_nonneg (p β d : ℕ) : 0 ≤ primePowerLadder p β d := by
  rw [primePowerLadder]
  split_ifs
  · exact ladderCoeff_nonneg _ _
  · exact le_rfl

theorem primePowerLadder_pow {p : ℕ} (hp : p.Prime) (β i : ℕ) :
    primePowerLadder p β (p ^ i) = ladderCoeff β i := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hval : padicValNat p (p ^ i) = i := padicValNat.prime_pow i
  have hne : p ^ i ≠ 0 := pow_ne_zero i hp.pos.ne'
  rw [primePowerLadder, if_pos ⟨by rw [hval], hne⟩, hval]

/-- **The prime-power ladder is a divisor transform of the valuation power.** -/
theorem sum_divisors_primePowerLadder {p : ℕ} (hp : p.Prime) {β : ℕ} (hβ : 1 ≤ β)
    {k : ℕ} (hk : k ≠ 0) :
    ∑ d ∈ k.divisors, primePowerLadder p β d = ((padicValNat p k : ℕ) : ℝ) ^ β := by
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  set v := padicValNat p k with hv
  have hmemiff : ∀ i : ℕ, i ∈ Finset.Icc 0 v ↔ p ^ i ∈ k.divisors := by
    intro i
    simp only [Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨-, hi⟩
      refine ⟨?_, hk⟩
      rw [hp.pow_dvd_iff_le_factorization hk, Nat.factorization_def _ hp]
      exact hi
    · rintro ⟨hdvd, -⟩
      refine ⟨Nat.zero_le _, ?_⟩
      rw [hp.pow_dvd_iff_le_factorization hk, Nat.factorization_def _ hp] at hdvd
      exact hdvd
  have hsub : (Finset.Icc 0 v).image (fun i => p ^ i) ⊆ k.divisors := by
    intro d hd
    simp only [Finset.mem_image] at hd
    obtain ⟨i, hi, rfl⟩ := hd
    exact (hmemiff i).mp hi
  have hzero : ∀ d ∈ k.divisors, d ∉ (Finset.Icc 0 v).image (fun i => p ^ i) →
      primePowerLadder p β d = 0 := by
    intro d hd hnot
    rw [primePowerLadder]
    refine if_neg ?_
    rintro ⟨hpow, hdne⟩
    refine hnot ?_
    simp only [Finset.mem_image]
    refine ⟨padicValNat p d, ?_, hpow⟩
    exact (hmemiff (padicValNat p d)).mpr (by rw [hpow]; exact hd)
  rw [← Finset.sum_subset hsub hzero]
  rw [Finset.sum_image (fun i _ j _ h => Nat.pow_right_injective hp.two_le h)]
  have hstep : ∀ i ∈ Finset.Icc 0 v, primePowerLadder p β (p ^ i) = ladderCoeff β i :=
    fun i _ => primePowerLadder_pow hp β i
  rw [Finset.sum_congr rfl hstep]
  rw [show Finset.Icc 0 v = insert 0 (Finset.Icc 1 v) by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega]
  rw [Finset.sum_insert (by simp), ladderCoeff_zero, zero_add, sum_ladderCoeff hβ]

/-! ### Support and reindexing -/

theorem primePowerLadder_support {p : ℕ} (_hp : p.Prime) (β : ℕ) :
    Function.support (primePowerLadder p β) ⊆ Set.range (fun i : ℕ => p ^ i) := by
  intro d hd
  simp only [Function.mem_support, primePowerLadder] at hd
  by_cases h : p ^ (padicValNat p d) = d ∧ d ≠ 0
  · exact ⟨padicValNat p d, h.1⟩
  · rw [if_neg h] at hd
    exact absurd rfl hd

theorem primePowerLadder_injective {p : ℕ} (hp : p.Prime) :
    Function.Injective (fun i : ℕ => p ^ i) := Nat.pow_right_injective hp.two_le

/-- The prime-power ladder mass up to a cutoff is the telescoped power of the ladder height. -/
theorem sum_Icc_primePowerLadder {p : ℕ} (hp : p.Prime) {β : ℕ} (hβ : 1 ≤ β) {N : ℕ}
    (hN : 1 ≤ N) :
    ∑ d ∈ Finset.Icc 1 N, primePowerLadder p β d = ((Nat.log p N : ℕ) : ℝ) ^ β := by
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  set I := Nat.log p N with hI
  have hmemiff : ∀ i : ℕ, i ∈ Finset.Icc 0 I ↔ p ^ i ∈ Finset.Icc 1 N := by
    intro i
    simp only [Finset.mem_Icc]
    constructor
    · rintro ⟨-, hi⟩
      refine ⟨Nat.one_le_pow _ _ hp.pos, ?_⟩
      calc p ^ i ≤ p ^ I := Nat.pow_le_pow_right hp.pos hi
        _ ≤ N := Nat.pow_log_le_self p (by omega)
    · rintro ⟨-, hle⟩
      refine ⟨Nat.zero_le _, ?_⟩
      exact Nat.le_log_of_pow_le hp.one_lt hle
  have hsub : (Finset.Icc 0 I).image (fun i => p ^ i) ⊆ Finset.Icc 1 N := by
    intro d hd
    simp only [Finset.mem_image] at hd
    obtain ⟨i, hi, rfl⟩ := hd
    exact (hmemiff i).mp hi
  have hzero : ∀ d ∈ Finset.Icc 1 N, d ∉ (Finset.Icc 0 I).image (fun i => p ^ i) →
      primePowerLadder p β d = 0 := by
    intro d hd hnot
    rw [primePowerLadder]
    refine if_neg ?_
    rintro ⟨hpow, hdne⟩
    refine hnot ?_
    simp only [Finset.mem_image]
    refine ⟨padicValNat p d, ?_, hpow⟩
    exact (hmemiff (padicValNat p d)).mpr (by rw [hpow]; exact hd)
  rw [← Finset.sum_subset hsub hzero]
  rw [Finset.sum_image (fun i _ j _ h => primePowerLadder_injective hp h)]
  rw [Finset.sum_congr rfl (fun i _ => primePowerLadder_pow hp β i)]
  rw [show Finset.Icc 0 I = insert 0 (Finset.Icc 1 I) by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega]
  rw [Finset.sum_insert (by simp), ladderCoeff_zero, zero_add, sum_ladderCoeff hβ]

/-! ### The two hypotheses of the regularization device -/

theorem ladderCoeff_le_pow (β i : ℕ) : ladderCoeff β i ≤ (i : ℝ) ^ β := by
  rw [ladderCoeff]
  have : (0 : ℝ) ≤ ((i - 1 : ℕ) : ℝ) ^ β := by positivity
  linarith

theorem summable_logWeight_primePowerLadder {p : ℕ} (hp : p.Prime) (β : ℕ) :
    Summable (logWeight (primePowerLadder p β)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hr : ‖((p : ℝ)⁻¹)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [inv_lt_one_iff₀]
    right; linarith
  have hzero : ∀ x ∉ Set.range (fun i : ℕ => p ^ i), logWeight (primePowerLadder p β) x = 0 := by
    intro x hx
    have h0 : primePowerLadder p β x = 0 := by
      by_contra hne
      exact hx (primePowerLadder_support hp β (by simpa using hne))
    rw [logWeight, h0]
    simp
  rw [← Function.Injective.summable_iff (primePowerLadder_injective hp) hzero]
  have hval : ∀ i : ℕ, (logWeight (primePowerLadder p β) ∘ fun i : ℕ => p ^ i) i
      = ladderCoeff β i * (1 + (i : ℝ) * Real.log p) * ((p : ℝ)⁻¹) ^ i := by
    intro i
    simp only [Function.comp_apply, logWeight, primePowerLadder_pow hp β i]
    rw [abs_of_nonneg (ladderCoeff_nonneg β i)]
    have hcast : (((p ^ i : ℕ)) : ℝ) = (p : ℝ) ^ i := by push_cast; ring
    rw [hcast, Real.log_pow, inv_pow]
    field_simp
  rw [show (logWeight (primePowerLadder p β) ∘ fun i : ℕ => p ^ i)
      = fun i : ℕ => ladderCoeff β i * (1 + (i : ℝ) * Real.log p) * ((p : ℝ)⁻¹) ^ i
    from funext hval]
  have hmaj : Summable (fun i : ℕ =>
      ((i : ℝ) ^ β * ((p : ℝ)⁻¹) ^ i + Real.log p * ((i : ℝ) ^ (β + 1) * ((p : ℝ)⁻¹) ^ i))) :=
    (summable_pow_mul_geometric_of_norm_lt_one β hr).add
      ((summable_pow_mul_geometric_of_norm_lt_one (β + 1) hr).mul_left _)
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hmaj
  · have h1 : (0 : ℝ) ≤ ladderCoeff β i := ladderCoeff_nonneg β i
    have h2 : (0 : ℝ) ≤ 1 + (i : ℝ) * Real.log p := by
      have : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
      positivity
    positivity
  · have h1 : (0 : ℝ) ≤ ladderCoeff β i := ladderCoeff_nonneg β i
    have hle := ladderCoeff_le_pow β i
    have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
    have hgeo : (0 : ℝ) ≤ ((p : ℝ)⁻¹) ^ i := by positivity
    have hexp : (i : ℝ) ^ (β + 1) = (i : ℝ) ^ β * (i : ℝ) := by ring
    calc ladderCoeff β i * (1 + (i : ℝ) * Real.log p) * ((p : ℝ)⁻¹) ^ i
        ≤ (i : ℝ) ^ β * (1 + (i : ℝ) * Real.log p) * ((p : ℝ)⁻¹) ^ i := by
          have hfac : (0 : ℝ) ≤ (1 + (i : ℝ) * Real.log p) * ((p : ℝ)⁻¹) ^ i := by positivity
          nlinarith
      _ = (i : ℝ) ^ β * ((p : ℝ)⁻¹) ^ i + Real.log p * ((i : ℝ) ^ (β + 1) * ((p : ℝ)⁻¹) ^ i) := by
          rw [hexp]; ring

theorem tendsto_log_pow_div_atTop (β : ℕ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ β / x) atTop (nhds 0) := by
  rcases Nat.eq_zero_or_pos β with rfl | hβ
  · simp only [pow_zero]
    simpa [one_div] using tendsto_inv_atTop_zero
  · have hβR : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ
    have hmaj : Tendsto (fun x : ℝ => ((2 * (β : ℝ)) ^ β) * x ^ (-(1 / 2) : ℝ))
        atTop (nhds 0) := by
      have h := tendsto_rpow_neg_atTop (y := (1 / 2 : ℝ)) (by norm_num)
      simpa using h.const_mul ((2 * (β : ℝ)) ^ β)
    refine squeeze_zero' ?_ ?_ hmaj
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
      positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx0 : (0 : ℝ) < x := by linarith
      have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
      have hε : (0 : ℝ) < 1 / (2 * (β : ℝ)) := by positivity
      have hbound : Real.log x ≤ (2 * (β : ℝ)) * x ^ (1 / (2 * (β : ℝ))) := by
        calc Real.log x ≤ x ^ (1 / (2 * (β : ℝ))) / (1 / (2 * (β : ℝ))) := by
              exact Real.log_le_rpow_div hx0.le hε
          _ = (2 * (β : ℝ)) * x ^ (1 / (2 * (β : ℝ))) := by
              field_simp
      have hpow : (Real.log x) ^ β ≤ ((2 * (β : ℝ)) * x ^ (1 / (2 * (β : ℝ)))) ^ β := by
        gcongr
      have hsimp : ((2 * (β : ℝ)) * x ^ (1 / (2 * (β : ℝ)))) ^ β
          = (2 * (β : ℝ)) ^ β * x ^ ((1 : ℝ) / 2) := by
        rw [mul_pow, ← Real.rpow_natCast (x ^ (1 / (2 * (β : ℝ)))) β, ← Real.rpow_mul hx0.le]
        congr 2
        field_simp
      have hdiv : x ^ ((1 : ℝ) / 2) / x = x ^ (-(1 / 2) : ℝ) := by
        have hsplit := Real.rpow_add hx0 (-(1 / 2)) 1
        rw [Real.rpow_one, show (-(1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) by norm_num] at hsplit
        rw [hsplit]
        field_simp
      calc (Real.log x) ^ β / x ≤ ((2 * (β : ℝ)) * x ^ (1 / (2 * (β : ℝ)))) ^ β / x := by
            gcongr
        _ = (2 * (β : ℝ)) ^ β * (x ^ ((1 : ℝ) / 2) / x) := by rw [hsimp]; ring
        _ = (2 * (β : ℝ)) ^ β * x ^ (-(1 / 2) : ℝ) := by rw [hdiv]

theorem tendsto_primePowerLadder_mass_div {p : ℕ} (hp : p.Prime) {β : ℕ} (hβ : 1 ≤ β) :
    Tendsto (fun N : ℕ => (∑ d ∈ Finset.Icc 1 N, |primePowerLadder p β d|) / N)
      atTop (nhds 0) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hmaj : Tendsto (fun N : ℕ => (1 / Real.log p) ^ β * ((Real.log N) ^ β / N))
      atTop (nhds 0) := by
    have h := (tendsto_log_pow_div_atTop β).comp tendsto_natCast_atTop_atTop
    simpa using h.const_mul ((1 / Real.log p) ^ β)
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have : (0 : ℕ) < N := hN
      exact_mod_cast this
    have : (0 : ℝ) ≤ ∑ d ∈ Finset.Icc 1 N, |primePowerLadder p β d| :=
      Finset.sum_nonneg fun d _ => abs_nonneg _
    positivity
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have : (0 : ℕ) < N := hN
      exact_mod_cast this
    have habs : ∀ d, |primePowerLadder p β d| = primePowerLadder p β d :=
      fun d => abs_of_nonneg (primePowerLadder_nonneg p β d)
    simp only [habs]
    rw [sum_Icc_primePowerLadder hp hβ hN]
    have hlogle : ((Nat.log p N : ℕ) : ℝ) ≤ Real.log N / Real.log p := by
      rw [le_div_iff₀ hlogp]
      have hpow : p ^ (Nat.log p N) ≤ N := Nat.pow_log_le_self p (by omega)
      have h1 : Real.log (((p ^ (Nat.log p N) : ℕ)) : ℝ) ≤ Real.log N := by
        refine Real.log_le_log ?_ (by exact_mod_cast hpow)
        have : (0 : ℕ) < p ^ (Nat.log p N) := Nat.one_le_pow _ _ hp.pos
        exact_mod_cast this
      rw [show (((p ^ (Nat.log p N) : ℕ)) : ℝ) = (p : ℝ) ^ (Nat.log p N) from by push_cast; ring,
        Real.log_pow] at h1
      exact h1
    have hlognn : (0 : ℝ) ≤ ((Nat.log p N : ℕ) : ℝ) := Nat.cast_nonneg _
    have hpowle : ((Nat.log p N : ℕ) : ℝ) ^ β ≤ (Real.log N / Real.log p) ^ β := by gcongr
    calc ((Nat.log p N : ℕ) : ℝ) ^ β / N ≤ (Real.log N / Real.log p) ^ β / N := by gcongr
      _ = (1 / Real.log p) ^ β * ((Real.log N) ^ β / N) := by
          rw [div_pow, one_div]
          ring

/-! ### The regularized single-prime lane -/

/-- The `γ`-lane density `D_{β,p} = ∑_{i ≥ 1} c_i p^{-i}`. -/
def stieltjesSinglePrimeDensity (p β : ℕ) : ℝ :=
  ∑' i : ℕ, ladderCoeff β i * ((p : ℝ)⁻¹) ^ i

/-- The `log p`-lane mass `L_{β,p} = ∑_{i ≥ 1} i c_i p^{-i}`. -/
def stieltjesSinglePrimeLogMass (p β : ℕ) : ℝ :=
  ∑' i : ℕ, (i : ℝ) * (ladderCoeff β i * ((p : ℝ)⁻¹) ^ i)

theorem coeffDensity_primePowerLadder {p : ℕ} (hp : p.Prime) (β : ℕ) :
    coeffDensity (primePowerLadder p β) = stieltjesSinglePrimeDensity p β := by
  rw [coeffDensity, stieltjesSinglePrimeDensity]
  have hsupp : Function.support (fun d : ℕ => primePowerLadder p β d / d)
      ⊆ Set.range (fun i : ℕ => p ^ i) := by
    intro d hd
    refine primePowerLadder_support hp β ?_
    simp only [Function.mem_support] at hd ⊢
    intro h
    rw [h, zero_div] at hd
    exact hd rfl
  rw [← Function.Injective.tsum_eq (primePowerLadder_injective hp) hsupp]
  refine tsum_congr fun i => ?_
  rw [primePowerLadder_pow hp β i]
  have hcast : (((p ^ i : ℕ)) : ℝ) = (p : ℝ) ^ i := by push_cast; ring
  rw [hcast, inv_pow]
  ring

theorem coeffLogMass_primePowerLadder {p : ℕ} (hp : p.Prime) (β : ℕ) :
    coeffLogMass (primePowerLadder p β) = Real.log p * stieltjesSinglePrimeLogMass p β := by
  rw [coeffLogMass, stieltjesSinglePrimeLogMass, ← tsum_mul_left]
  have hsupp : Function.support (fun d : ℕ => primePowerLadder p β d / d * Real.log d)
      ⊆ Set.range (fun i : ℕ => p ^ i) := by
    intro d hd
    refine primePowerLadder_support hp β ?_
    simp only [Function.mem_support] at hd ⊢
    intro h
    rw [h, zero_div, zero_mul] at hd
    exact hd rfl
  rw [← Function.Injective.tsum_eq (primePowerLadder_injective hp) hsupp]
  refine tsum_congr fun i => ?_
  rw [primePowerLadder_pow hp β i]
  have hcast : (((p ^ i : ℕ)) : ℝ) = (p : ℝ) ^ i := by push_cast; ring
  rw [hcast, Real.log_pow, inv_pow]
  ring

/-- **The γ-affine structure of the single-prime Stieltjes lane at every order.**
The regularized limit exists and splits exactly into a `γ`-lane and a `log p`-lane. -/
theorem tendsto_stieltjesSinglePrimeCutoff {p : ℕ} (hp : p.Prime) {β : ℕ} (hβ : 1 ≤ β) :
    Tendsto (fun N : ℕ =>
        (∑ k ∈ Finset.Icc 1 N, ((padicValNat p k : ℕ) : ℝ) ^ β / k)
          - stieltjesSinglePrimeDensity p β * Real.log N)
      atTop (nhds (stieltjesSinglePrimeDensity p β * Real.eulerMascheroniConstant
        - Real.log p * stieltjesSinglePrimeLogMass p β)) := by
  have hdev := tendsto_regularizedDivisorHarmonic
    (a := primePowerLadder p β) (summable_logWeight_primePowerLadder hp β)
    (tendsto_primePowerLadder_mass_div hp hβ)
  rw [coeffDensity_primePowerLadder hp β, coeffLogMass_primePowerLadder hp β] at hdev
  refine hdev.congr fun N => ?_
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  rw [sum_divisors_primePowerLadder hp hβ (by omega : k ≠ 0)]

/-! ### Rationality of the two lane coefficients -/

theorem primeRatio_abs_lt_one {p : ℕ} (hp : p.Prime) : |((p : ℝ)⁻¹)| < 1 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  rw [abs_of_nonneg (by positivity)]
  rw [inv_lt_one_iff₀]
  right; linarith

theorem summable_shiftedLadderTerm {p : ℕ} (hp : p.Prime) (β : ℕ) :
    Summable (fun i : ℕ => (((i - 1 : ℕ)) : ℝ) ^ β * ((p : ℝ)⁻¹) ^ i) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    (summable_geomMomentTerm (primeRatio_abs_lt_one hp) β)
  have h : (((i - 1 : ℕ)) : ℝ) ≤ (i : ℝ) := by exact_mod_cast Nat.sub_le i 1
  have h0 : (0 : ℝ) ≤ (((i - 1 : ℕ)) : ℝ) := Nat.cast_nonneg _
  have hgeo : (0 : ℝ) ≤ ((p : ℝ)⁻¹) ^ i := by positivity
  gcongr

theorem summable_ladderCoeff_geom {p : ℕ} (hp : p.Prime) (β : ℕ) :
    Summable (fun i : ℕ => ladderCoeff β i * ((p : ℝ)⁻¹) ^ i) := by
  have hrep : ∀ i : ℕ, ladderCoeff β i * ((p : ℝ)⁻¹) ^ i
      = (i : ℝ) ^ β * ((p : ℝ)⁻¹) ^ i - (((i - 1 : ℕ)) : ℝ) ^ β * ((p : ℝ)⁻¹) ^ i := by
    intro i; rw [ladderCoeff]; ring
  rw [show (fun i : ℕ => ladderCoeff β i * ((p : ℝ)⁻¹) ^ i)
      = fun i : ℕ => (i : ℝ) ^ β * ((p : ℝ)⁻¹) ^ i
        - (((i - 1 : ℕ)) : ℝ) ^ β * ((p : ℝ)⁻¹) ^ i from funext hrep]
  exact (summable_geomMomentTerm (primeRatio_abs_lt_one hp) β).sub
    (summable_shiftedLadderTerm hp β)

/-- The `γ`-lane density is `(1 − 1/p)·R_β(1/p)`. -/
theorem stieltjesSinglePrimeDensity_eq {p : ℕ} (hp : p.Prime) {β : ℕ} (hβ : 1 ≤ β) :
    stieltjesSinglePrimeDensity p β
      = (1 - (p : ℝ)⁻¹) * geomMoment ((p : ℝ)⁻¹) β := by
  have hr := primeRatio_abs_lt_one hp
  have hshift : (∑' i : ℕ, (((i - 1 : ℕ)) : ℝ) ^ β * ((p : ℝ)⁻¹) ^ i)
      = (p : ℝ)⁻¹ * geomMoment ((p : ℝ)⁻¹) β := by
    rw [(summable_shiftedLadderTerm hp β).tsum_eq_zero_add]
    have hz : (((0 - 1 : ℕ)) : ℝ) ^ β = 0 := by
      simp only [Nat.zero_sub, Nat.cast_zero]
      exact zero_pow (by omega)
    rw [hz, zero_mul, zero_add, geomMoment, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [Nat.add_sub_cancel]
    rw [pow_succ]
    ring
  have hrep : ∀ i : ℕ, ladderCoeff β i * ((p : ℝ)⁻¹) ^ i
      = (i : ℝ) ^ β * ((p : ℝ)⁻¹) ^ i - (((i - 1 : ℕ)) : ℝ) ^ β * ((p : ℝ)⁻¹) ^ i := by
    intro i; rw [ladderCoeff]; ring
  rw [stieltjesSinglePrimeDensity]
  rw [show (fun i : ℕ => ladderCoeff β i * ((p : ℝ)⁻¹) ^ i)
      = fun i : ℕ => (i : ℝ) ^ β * ((p : ℝ)⁻¹) ^ i
        - (((i - 1 : ℕ)) : ℝ) ^ β * ((p : ℝ)⁻¹) ^ i from funext hrep]
  rw [Summable.tsum_sub (summable_geomMomentTerm hr β) (summable_shiftedLadderTerm hp β),
    hshift, ← geomMoment]
  ring

/-- The `log p`-lane mass is `R_{β+1}(1/p) − (1/p)(R_{β+1}(1/p) + R_β(1/p))`. -/
theorem stieltjesSinglePrimeLogMass_eq {p : ℕ} (hp : p.Prime) {β : ℕ} (_hβ : 1 ≤ β) :
    stieltjesSinglePrimeLogMass p β
      = geomMoment ((p : ℝ)⁻¹) (β + 1)
        - (p : ℝ)⁻¹ * (geomMoment ((p : ℝ)⁻¹) (β + 1) + geomMoment ((p : ℝ)⁻¹) β) := by
  have hr := primeRatio_abs_lt_one hp
  have hsum2 : Summable (fun i : ℕ => (i : ℝ) * ((((i - 1 : ℕ)) : ℝ) ^ β * ((p : ℝ)⁻¹) ^ i)) := by
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      (summable_geomMomentTerm hr (β + 1))
    have h : (((i - 1 : ℕ)) : ℝ) ≤ (i : ℝ) := by exact_mod_cast Nat.sub_le i 1
    have h0 : (0 : ℝ) ≤ (((i - 1 : ℕ)) : ℝ) := Nat.cast_nonneg _
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
    have hgeo : (0 : ℝ) ≤ ((p : ℝ)⁻¹) ^ i := by positivity
    have hpow : (((i - 1 : ℕ)) : ℝ) ^ β ≤ (i : ℝ) ^ β := by gcongr
    calc (i : ℝ) * ((((i - 1 : ℕ)) : ℝ) ^ β * ((p : ℝ)⁻¹) ^ i)
        ≤ (i : ℝ) * ((i : ℝ) ^ β * ((p : ℝ)⁻¹) ^ i) := by
          have : (0 : ℝ) ≤ ((p : ℝ)⁻¹) ^ i := hgeo
          nlinarith [mul_nonneg hi0 hgeo]
      _ = (i : ℝ) ^ (β + 1) * ((p : ℝ)⁻¹) ^ i := by ring
  have hshift : (∑' i : ℕ, (i : ℝ) * ((((i - 1 : ℕ)) : ℝ) ^ β * ((p : ℝ)⁻¹) ^ i))
      = (p : ℝ)⁻¹ * (geomMoment ((p : ℝ)⁻¹) (β + 1) + geomMoment ((p : ℝ)⁻¹) β) := by
    rw [hsum2.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_mul, zero_add]
    rw [geomMoment, geomMoment, ← Summable.tsum_add (summable_geomMomentTerm hr (β + 1))
      (summable_geomMomentTerm hr β), ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [Nat.add_sub_cancel]
    push_cast
    rw [pow_succ]
    ring
  have hrep : ∀ i : ℕ, (i : ℝ) * (ladderCoeff β i * ((p : ℝ)⁻¹) ^ i)
      = (i : ℝ) ^ (β + 1) * ((p : ℝ)⁻¹) ^ i
        - (i : ℝ) * ((((i - 1 : ℕ)) : ℝ) ^ β * ((p : ℝ)⁻¹) ^ i) := by
    intro i; rw [ladderCoeff]; ring
  rw [stieltjesSinglePrimeLogMass]
  rw [show (fun i : ℕ => (i : ℝ) * (ladderCoeff β i * ((p : ℝ)⁻¹) ^ i))
      = fun i : ℕ => (i : ℝ) ^ (β + 1) * ((p : ℝ)⁻¹) ^ i
        - (i : ℝ) * ((((i - 1 : ℕ)) : ℝ) ^ β * ((p : ℝ)⁻¹) ^ i) from funext hrep]
  rw [Summable.tsum_sub (summable_geomMomentTerm hr (β + 1)) hsum2, hshift, ← geomMoment]

theorem primeRatio_eq_ratCast {p : ℕ} (_hp : p.Prime) :
    ((p : ℝ)⁻¹) = (((1 / p : ℚ)) : ℝ) := by
  push_cast
  ring

/-- **The single-prime lane coefficients are rational.** -/
theorem exists_rat_stieltjesSinglePrime {p : ℕ} (hp : p.Prime) {β : ℕ} (hβ : 1 ≤ β) :
    ∃ d l : ℚ, stieltjesSinglePrimeDensity p β = (d : ℝ)
      ∧ stieltjesSinglePrimeLogMass p β = (l : ℝ) := by
  have hcast := primeRatio_eq_ratCast hp
  have hr : |(((1 / p : ℚ)) : ℝ)| < 1 := by
    rw [← hcast]
    exact primeRatio_abs_lt_one hp
  obtain ⟨a, ha⟩ := exists_rat_geomMoment hr β
  obtain ⟨b, hb⟩ := exists_rat_geomMoment hr (β + 1)
  rw [← hcast] at ha hb
  refine ⟨(1 - 1 / p) * a, b - (1 / p) * (b + a), ?_, ?_⟩
  · rw [stieltjesSinglePrimeDensity_eq hp hβ, ha, hcast]
    push_cast
    ring
  · rw [stieltjesSinglePrimeLogMass_eq hp hβ, ha, hb, hcast]
    push_cast
    ring

/-- **γ-affine structure with rational coefficients, single prime, every order.**
`A_{β,p} = q₁·γ + q₂·log p` with `q₁, q₂ ∈ ℚ`. -/
theorem tendsto_stieltjesSinglePrimeCutoff_rat {p : ℕ} (hp : p.Prime) {β : ℕ} (hβ : 1 ≤ β) :
    ∃ d l : ℚ,
      Tendsto (fun N : ℕ =>
          (∑ k ∈ Finset.Icc 1 N, ((padicValNat p k : ℕ) : ℝ) ^ β / k) - (d : ℝ) * Real.log N)
        atTop (nhds ((d : ℝ) * Real.eulerMascheroniConstant - Real.log p * (l : ℝ))) := by
  obtain ⟨d, l, hd, hl⟩ := exists_rat_stieltjesSinglePrime hp hβ
  refine ⟨d, l, ?_⟩
  have h := tendsto_stieltjesSinglePrimeCutoff hp hβ
  rw [hd, hl] at h
  exact h

end

end StieltjesGammaAffine
end RHTower
