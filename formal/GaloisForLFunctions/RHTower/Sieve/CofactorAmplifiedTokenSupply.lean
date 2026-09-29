import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenBandTokens
import GaloisForLFunctions.RHTower.Sieve.CoprimeE3BlockReplacement
import GaloisForLFunctions.RHTower.RouteECofactorBandMass
import GaloisForLFunctions.RHTower.Sieve.GeomBlockPrimesRange

/-!
# Cofactor-amplified `E₃` token supply

Assume the Deshouillers--Iwaniec and Watt bounds `(E1)`, `(E2)` and let `0 < η < 1/6`.  For a
squarefree source `u ∈ [U, 2U]` the replacement family `Q(u)` consists of the products `q = t·m`
where `t ≤ ⌊U^{2η}⌋` is a squarefree cofactor of Möbius sign `μ(u)` avoiding the prime band
`(⌊(log U)^{1.09}⌋, ⌊2(log U)^{1.1}⌋]`, and `m = p₁p₂n` is an `E₃` number in the natural window
`(u/t, u/t + √(u/t) (log(u/t))^{31/20}]` whose small prime `p₁` lies in that band and whose two
large primes exceed `⌊U^{2η}⌋`.

* The band makes `t` and `m` coprime and makes `t` recoverable from `q` (`cofactor_mul_inj`), so
  `μ(q) = -μ(u)` and `0 < q - u ≤ 8 U^{1/2+η} (log U)^{31/20}`.
* The row supply of the band tokens and the parity-class estimate `Σ t^{-1/2} ≫ √T` give
  `#Q(u) ≫ U^{1/2+η}/(log U)^{9/20}`.
* Sources of sign `-1` in every interval of length `√x (log x)^{31/20}` (the all-interval `E₃`
  theorem) are placed on a grid of spacing `4√(Ut) (log 2U)^{31/20}`; the windows are disjoint and
  `Σ 1/t ≫ η log U` gives a physical union of size `≫ η U/log U`.

The main statement is `eventually_cofactor_amplified_supply`.
-/

namespace RHTower.Sieve

open Finset Filter

noncomputable section

/-- The band-avoiding cofactors of Möbius sign `σ` up to `Tn`, band `(z₀, z]`. -/
abbrev bandCofactors (z₀ z : ℕ) (σ : ℤ) (Tn : ℕ) : Finset ℕ :=
  CofactorParity.parityClass (fun p => p ∈ Sieve.primesRange z₀ z) σ Tn

/-- A band token of the window `(y, y+H]` lies in it. -/
theorem bandTokens_mem_bounds {z₀ z T m : ℕ} {y H : ℝ} (hm : m ∈ bandTokens z₀ z T y H) :
    y < (m : ℝ) ∧ (m : ℝ) ≤ y + H := by
  classical
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.1 (Finset.mem_filter.1 hm).1
  refine ⟨Nat.lt_of_floor_lt hlo, ?_⟩
  have hyH : 0 ≤ y + H := by
    by_contra hc; push Not at hc
    have : ⌊y + H⌋₊ = 0 := Nat.floor_eq_zero.2 (by linarith)
    omega
  exact (Nat.cast_le.2 hhi).trans (Nat.floor_le hyH)

/-- **A cofactor and a band token are coprime, and their product reverses the sign.**  The token's
small prime lies in the band avoided by `t`, and its large primes exceed `Tn ≥ t`. -/
theorem cofactor_bandToken_facts {z₀ z Tn t m : ℕ} {σ : ℤ} {y H : ℝ} (hzT : z < Tn)
    (hσ : σ = 1 ∨ σ = -1) (ht : t ∈ bandCofactors z₀ z σ Tn) (hm : m ∈ bandTokens (z₀ + 1) z Tn y H) :
    Nat.Coprime t m ∧ Squarefree (t * m) ∧
      ArithmeticFunction.moebius (t * m) = -σ ∧ y < (m : ℝ) ∧ (m : ℝ) ≤ y + H := by
  classical
  obtain ⟨htI, hμ, hband⟩ := Finset.mem_filter.1 ht
  obtain ⟨ht1, htT⟩ := Finset.mem_Icc.1 htI
  have hb := bandTokens_mem_bounds hm
  unfold bandTokens at hm
  obtain ⟨-, p₁, p₂, n, h₁, h₂, h₃, hne, hz₀, hz, hT₂, hTn, rfl⟩ := Finset.mem_filter.1 hm
  have hnd : ∀ p : ℕ, p.Prime → Tn < p → ¬ p ∣ t := fun p _ hp hd =>
    absurd (Nat.le_of_dvd (by omega) hd) (by omega)
  have hc₁ : Nat.Coprime t p₁ := by
    refine (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd h₁).2 fun hd => ?_))
    have hmem : p₁ ∈ t.primeFactors := Nat.mem_primeFactors.2 ⟨h₁, hd, by omega⟩
    exact hband p₁ hmem (Sieve.mem_primesRange.2 ⟨h₁, by omega, hz⟩)
  have hc₂ : Nat.Coprime t p₂ := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd h₂).2
    (hnd p₂ h₂ hT₂))
  have hc₃ : Nat.Coprime t n := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd h₃).2
    (hnd n h₃ hTn))
  have hcop : Nat.Coprime t (p₁ * p₂ * n) := Nat.Coprime.mul_right (Nat.Coprime.mul_right hc₁ hc₂) hc₃
  have h12 : p₁ ≠ p₂ := by omega
  have h13 : p₁ ≠ n := by omega
  have hsqm := squarefree_mul_three_primes h₁ h₂ h₃ h12 h13 hne
  have hσ0 : ArithmeticFunction.moebius t ≠ 0 := by
    rw [hμ]; rcases hσ with h | h <;> rw [h] <;> norm_num
  have hsqt : Squarefree t := ArithmeticFunction.moebius_ne_zero_iff_squarefree.1 hσ0
  refine ⟨hcop, Nat.squarefree_mul_iff.2 ⟨hcop, hsqt, hsqm⟩, ?_, hb.1, hb.2⟩
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop.gcd_eq_one, hμ,
    moebius_mul_three_distinct_primes h₁ h₂ h₃ h12 h13 hne]
  ring

/-- **Decoding.**  A product `t·m` of a band-avoiding cofactor and a band token determines both:
`t` divides `t'm'` and is coprime to `m'`. -/
theorem cofactor_mul_inj {z₀ z Tn t t' m m' : ℕ} {σ σ' : ℤ} {y y' H H' : ℝ} (hzT : z < Tn)
    (hσ : σ = 1 ∨ σ = -1) (hσ' : σ' = 1 ∨ σ' = -1)
    (ht : t ∈ bandCofactors z₀ z σ Tn) (ht' : t' ∈ bandCofactors z₀ z σ' Tn)
    (hm : m ∈ bandTokens (z₀ + 1) z Tn y H) (hm' : m' ∈ bandTokens (z₀ + 1) z Tn y' H')
    (h : t * m = t' * m') : t = t' ∧ m = m' := by
  have c1 := (cofactor_bandToken_facts hzT hσ ht hm').1
  have c2 := (cofactor_bandToken_facts hzT hσ' ht' hm).1
  have d1 : t ∣ t' := c1.dvd_of_dvd_mul_right (h ▸ dvd_mul_right t m)
  have d2 : t' ∣ t := c2.dvd_of_dvd_mul_right (h.symm ▸ dvd_mul_right t' m')
  have e : t = t' := Nat.dvd_antisymm d1 d2
  refine ⟨e, ?_⟩
  subst e
  have ht0 : 0 < t := (Finset.mem_Icc.1 (Finset.mem_filter.1 ht).1).1
  exact Nat.eq_of_mul_eq_mul_left ht0 h

/-- The natural interval `H(y) = √y (log y)^{31/20}`. -/
def naturalWidth (y : ℝ) : ℝ := Real.sqrt y * Real.log y ^ (31 / 20 : ℝ)

/-- **The replacement family of a source `u`**: the products `t·m` of the band-avoiding cofactors
`t ≤ Tn` of sign `μ(u)` with the band tokens `m ∈ (u/t, u/t + H(u/t)]`. -/
def cofactorFamily (z₀ z Tn u : ℕ) : Finset ℕ :=
  (bandCofactors z₀ z (ArithmeticFunction.moebius u) Tn).biUnion fun t =>
    (bandTokens (z₀ + 1) z Tn ((u : ℝ) / t) (naturalWidth ((u : ℝ) / t))).image (t * ·)

/-- **The size of the family.**  Distinct cofactors give disjoint pieces. -/
theorem card_cofactorFamily {z₀ z Tn u : ℕ} (hzT : z < Tn)
    (hσ : ArithmeticFunction.moebius u = 1 ∨ ArithmeticFunction.moebius u = -1) :
    ((cofactorFamily z₀ z Tn u).card : ℝ) =
      ∑ t ∈ bandCofactors z₀ z (ArithmeticFunction.moebius u) Tn,
        ((bandTokens (z₀ + 1) z Tn ((u : ℝ) / t) (naturalWidth ((u : ℝ) / t))).card : ℝ) := by
  classical
  unfold cofactorFamily
  rw [Finset.card_biUnion]
  · push_cast
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht0 : 0 < t := (Finset.mem_Icc.1 (Finset.mem_filter.1 ht).1).1
    rw [Finset.card_image_of_injective _ (fun a b hab => Nat.eq_of_mul_eq_mul_left ht0 hab)]
  · intro t ht t' ht' htt
    rw [Function.onFun, Finset.disjoint_left]
    intro q hq hq'
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨m', hm', he⟩ := Finset.mem_image.1 hq'
    exact htt (cofactor_mul_inj hzT hσ hσ ht ht' hm hm' he.symm).1

/-- Lower end of the excluded band: `⌊(log U)^{109/100}⌋`. -/
def cofactorBandLow (U : ℝ) : ℕ := ⌊Real.log U ^ (109 / 100 : ℝ)⌋₊

/-- Upper end of the excluded band: `⌊2 (log U)^{11/10}⌋`. -/
def cofactorBandHigh (U : ℝ) : ℕ := ⌊2 * Real.log U ^ (11 / 10 : ℝ)⌋₊

/-- The cofactor height `⌊U^{2η}⌋`. -/
def cofactorHeight (η U : ℝ) : ℕ := ⌊U ^ (2 * η)⌋₊

/-- `(log U)^ε → ∞`: eventually `C ≤ (log U)^ε`. -/
theorem eventually_le_log_rpow {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ∀ᶠ U : ℝ in atTop, C ≤ Real.log U ^ ε :=
  ((tendsto_rpow_atTop hε).comp Real.tendsto_log_atTop).eventually_ge_atTop C

/-- **The band facts.**  For large `U`, with `L = log U`, the band `(⌊L^{1.09}⌋, ⌊2L^{1.1}⌋]` has
`2 ≤` its lower end, lies between `L^{1.08}` and `2L^{1.1}`, its lower end plus one is below
`((2/3)L)^{1.0999}`, and its upper end exceeds `(log 2U)^{1.1}/2`. -/
theorem eventually_cofactor_band_facts :
    ∀ᶠ U : ℝ in atTop, 1 ≤ Real.log U ∧ 2 ≤ cofactorBandLow U ∧
      cofactorBandLow U ≤ cofactorBandHigh U ∧
      Real.log U ^ (108 / 100 : ℝ) ≤ cofactorBandLow U ∧
      (cofactorBandHigh U : ℝ) ≤ 2 * Real.log U ^ (11 / 10 : ℝ) ∧
      ((cofactorBandLow U + 1 : ℕ) : ℝ) ≤ (2 / 3 * Real.log U) ^ (10999 / 10000 : ℝ) ∧
      Real.log (2 * U) ^ (11 / 10 : ℝ) / 2 ≤ cofactorBandHigh U := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 2, eventually_gt_atTop (0 : ℝ),
    eventually_le_log_rpow (ε := 1 / 100) (by norm_num) 2,
    eventually_le_log_rpow (ε := 99 / 10000) (by norm_num) 10] with U hL hU0 h1 h2
  set L := Real.log U with hLdef
  have hL0 : 0 < L := by linarith
  have hsplit : ∀ a b : ℝ, L ^ (a + b) = L ^ a * L ^ b := fun a b => Real.rpow_add hL0 a b
  have hge1 : ∀ a : ℝ, 0 ≤ a → 1 ≤ L ^ a := fun a ha => Real.one_le_rpow (by linarith) ha
  have h108 := hge1 (108 / 100) (by norm_num)
  have h109 := hge1 (109 / 100) (by norm_num)
  have h110 := hge1 (11 / 10) (by norm_num)
  have e109 : L ^ (109 / 100 : ℝ) = L ^ (108 / 100 : ℝ) * L ^ (1 / 100 : ℝ) := by
    rw [← hsplit]; norm_num
  have e10999 : L ^ (10999 / 10000 : ℝ) = L ^ (109 / 100 : ℝ) * L ^ (99 / 10000 : ℝ) := by
    rw [← hsplit]; norm_num
  have h109le : L ^ (109 / 100 : ℝ) ≤ L ^ (11 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hfl := Nat.sub_one_lt_floor (L ^ (109 / 100 : ℝ))
  have hfh := Nat.sub_one_lt_floor (2 * L ^ (11 / 10 : ℝ))
  refine ⟨by linarith, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_floor (by push_cast; nlinarith)
  · exact Nat.floor_le_floor (by linarith)
  · unfold cofactorBandLow; nlinarith
  · exact Nat.floor_le (by positivity)
  · have hc : (4 / 9 : ℝ) ≤ (2 / 3 : ℝ) ^ (10999 / 10000 : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_ge (x := (2 / 3 : ℝ)) (by norm_num) (by norm_num)
        (show (10999 / 10000 : ℝ) ≤ 2 by norm_num)
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
      norm_num at this ⊢; linarith
    rw [Real.mul_rpow (by norm_num) hL0.le, e10999]
    have hfl' : ((cofactorBandLow U : ℕ) : ℝ) ≤ L ^ (109 / 100 : ℝ) := Nat.floor_le (by positivity)
    push_cast
    have hA : 0 ≤ L ^ (109 / 100 : ℝ) := by positivity
    have hB : 10 * L ^ (109 / 100 : ℝ) ≤ L ^ (109 / 100 : ℝ) * L ^ (99 / 10000 : ℝ) := by
      nlinarith
    have hC : 4 / 9 * (L ^ (109 / 100 : ℝ) * L ^ (99 / 10000 : ℝ)) ≤
        (2 / 3 : ℝ) ^ (10999 / 10000 : ℝ) * (L ^ (109 / 100 : ℝ) * L ^ (99 / 10000 : ℝ)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    linarith
  · have hl2 : Real.log (2 * U) ≤ 2 * L := by
      rw [Real.log_mul (by norm_num) hU0.ne']
      linarith [Real.log_two_lt_d9]
    have hl2' : 0 ≤ Real.log (2 * U) := by
      rw [Real.log_mul (by norm_num) hU0.ne']; linarith [Real.log_two_gt_d9]
    have hp : Real.log (2 * U) ^ (11 / 10 : ℝ) ≤ 3 * L ^ (11 / 10 : ℝ) := by
      calc Real.log (2 * U) ^ (11 / 10 : ℝ) ≤ (2 * L) ^ (11 / 10 : ℝ) :=
            Real.rpow_le_rpow hl2' hl2 (by norm_num)
        _ = 2 ^ (11 / 10 : ℝ) * L ^ (11 / 10 : ℝ) := Real.mul_rpow (by norm_num) hL0.le
        _ ≤ 3 * L ^ (11 / 10 : ℝ) :=
            mul_le_mul_of_nonneg_right two_rpow_eleven_tenths_le_three (by positivity)
    have hL11 : L ≤ L ^ (11 / 10 : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_le (x := L) (by linarith)
        (show (1 : ℝ) ≤ 11 / 10 by norm_num)
      rwa [Real.rpow_one] at this
    unfold cofactorBandHigh
    linarith

/-- **The height facts.**  For `0 < η < 1/6` and large `U`: `U^{1-2η}` exceeds `2` and any fixed
`y₀`; `2(log U)^{1.1} + 1 ≤ U^{2η}`; `U^{2η} (log 2U)² ≤ U^{1/2-η}`;
`16 U^η (log 2U)^{31/20} ≤ √U`; `9 ≤ η log U`; `32 ≤ U^η`. -/
theorem eventually_cofactor_height_facts {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 6) (y₀ : ℝ) :
    ∀ᶠ U : ℝ in atTop, y₀ ≤ U ^ (1 - 2 * η) ∧ 2 ≤ U ^ (1 - 2 * η) ∧
      2 * Real.log U ^ (11 / 10 : ℝ) + 1 ≤ U ^ (2 * η) ∧
      U ^ (2 * η) * Real.log (2 * U) ^ 2 ≤ U ^ (1 / 2 - η) ∧
      16 * U ^ η * Real.log (2 * U) ^ (31 / 20 : ℝ) ≤ Real.sqrt U ∧
      9 ≤ η * Real.log U ∧ 32 ≤ U ^ η := by
  have hpoly : ∀ {C κ : ℝ}, 0 ≤ C → 0 < κ →
      ∀ᶠ U : ℝ in atTop, C * Real.log U ^ 2 ≤ U ^ κ := by
    intro C κ hC hκ
    filter_upwards [eventually_polylog_le_rpow 2 hC hκ, eventually_ge_atTop (1 : ℝ)] with U h hU
    have hL : 0 ≤ Real.log U := Real.log_nonneg hU
    have h24 : Real.log U ≤ 1 + Real.log (24 * U) := by
      rw [Real.log_mul (by norm_num) (by linarith)]
      have : 0 < Real.log 24 := Real.log_pos (by norm_num)
      linarith
    have : Real.log U ^ 2 ≤ (1 + Real.log (24 * U)) ^ 2 := pow_le_pow_left₀ hL h24 2
    nlinarith
  filter_upwards [(tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - 2 * η)).eventually_ge_atTop
      (max y₀ 2),
    hpoly (C := 3) (by norm_num) (by linarith : (0 : ℝ) < 2 * η),
    hpoly (C := 4) (by norm_num) (by linarith : (0 : ℝ) < 1 / 2 - 3 * η),
    hpoly (C := 64) (by norm_num) (by linarith : (0 : ℝ) < 1 / 2 - η),
    Real.tendsto_log_atTop.eventually_ge_atTop (9 / η),
    (tendsto_rpow_atTop hη0).eventually_ge_atTop 32,
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_gt_atTop (0 : ℝ)]
    with U hy h3 h4 h64 h9 h32 hL1 hU0
  set L := Real.log U with hLdef
  have hl2 : Real.log (2 * U) ≤ 2 * L := by
    rw [Real.log_mul (by norm_num) hU0.ne']; linarith [Real.log_two_lt_d9]
  have hl2' : 1 ≤ Real.log (2 * U) := by
    rw [Real.log_mul (by norm_num) hU0.ne']; linarith [Real.log_two_gt_d9]
  have hsq : Real.log (2 * U) ^ 2 ≤ 4 * L ^ 2 := by nlinarith
  refine ⟨(le_max_left _ _).trans hy, (le_max_right _ _).trans hy, ?_, ?_, ?_, ?_, h32⟩
  · have : L ^ (11 / 10 : ℝ) ≤ L ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    rw [Real.rpow_two] at this
    nlinarith
  · have hmul : U ^ (2 * η) * U ^ (1 / 2 - 3 * η) = U ^ (1 / 2 - η) := by
      rw [← Real.rpow_add hU0]; congr 1; ring
    have hpos : 0 ≤ U ^ (2 * η) := by positivity
    calc U ^ (2 * η) * Real.log (2 * U) ^ 2 ≤ U ^ (2 * η) * (4 * L ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hpos
      _ ≤ U ^ (2 * η) * U ^ (1 / 2 - 3 * η) := mul_le_mul_of_nonneg_left h4 hpos
      _ = U ^ (1 / 2 - η) := hmul
  · have hp : Real.log (2 * U) ^ (31 / 20 : ℝ) ≤ Real.log (2 * U) ^ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le hl2' (show (31 / 20 : ℝ) ≤ 2 by norm_num)
      rwa [Real.rpow_two] at this
    have hmul : U ^ η * U ^ (1 / 2 - η) = Real.sqrt U := by
      rw [← Real.rpow_add hU0, Real.sqrt_eq_rpow]; congr 1; ring
    have hpos : 0 ≤ U ^ η := by positivity
    calc 16 * U ^ η * Real.log (2 * U) ^ (31 / 20 : ℝ) ≤ 16 * U ^ η * (4 * L ^ 2) :=
          mul_le_mul_of_nonneg_left (hp.trans hsq) (by positivity)
      _ = U ^ η * (64 * L ^ 2) := by ring
      _ ≤ U ^ η * U ^ (1 / 2 - η) := mul_le_mul_of_nonneg_left h64 hpos
      _ = Real.sqrt U := hmul
  · rw [div_le_iff₀ hη0] at h9; linarith

/-- `(log 2U)^a ≤ 2^a (log U)^a` once `log U ≥ 1`. -/
theorem log_two_mul_rpow_le {U a : ℝ} (hU0 : 0 < U) (hL1 : 1 ≤ Real.log U) (ha : 0 ≤ a) :
    Real.log (2 * U) ^ a ≤ 2 ^ a * Real.log U ^ a := by
  have hl2 : Real.log (2 * U) ≤ 2 * Real.log U := by
    rw [Real.log_mul (by norm_num) hU0.ne']; linarith [Real.log_two_lt_d9]
  have hl2' : 0 ≤ Real.log (2 * U) := by
    rw [Real.log_mul (by norm_num) hU0.ne']; linarith [Real.log_two_gt_d9]
  rw [← Real.mul_rpow (by norm_num) (by linarith)]
  exact Real.rpow_le_rpow hl2' hl2 ha

/-- **The admissible windows.**  For `1 ≤ t ≤ ⌊U^{2η}⌋` and `U ≤ u ≤ 2U`, the scale `y = u/t` lies in
`(1, 2U]` above `y₀`, and the band and the cofactor height satisfy the hypotheses of the band token
count at `y`. -/
theorem cofactor_window_admissible {η U y₀ : ℝ} (hη1 : η < 1 / 6) (hU0 : 0 < U)
    (hy₀ : y₀ ≤ U ^ (1 - 2 * η)) (h2 : 2 ≤ U ^ (1 - 2 * η)) (hL1 : 1 ≤ Real.log U)
    (hlow : ((cofactorBandLow U + 1 : ℕ) : ℝ) ≤ (2 / 3 * Real.log U) ^ (10999 / 10000 : ℝ))
    (hhigh : Real.log (2 * U) ^ (11 / 10 : ℝ) / 2 ≤ cofactorBandHigh U)
    (hT : U ^ (2 * η) * Real.log (2 * U) ^ 2 ≤ U ^ (1 / 2 - η))
    {t : ℕ} (ht1 : 1 ≤ t) (htT : t ≤ cofactorHeight η U) {u : ℝ} (hUu : U ≤ u) (hu2 : u ≤ 2 * U) :
    y₀ ≤ u / t ∧ 1 < u / t ∧ u / t ≤ 2 * U ∧
      ((cofactorBandLow U + 1 : ℕ) : ℝ) ≤ Real.log (2 * (u / t)) ^ (10999 / 10000 : ℝ) ∧
      Real.log (u / t) ^ (11 / 10 : ℝ) / 2 ≤ cofactorBandHigh U ∧
      (cofactorHeight η U : ℝ) ≤ Real.sqrt (u / t) / Real.log (u / t) ^ 2 := by
  have hTn : (cofactorHeight η U : ℝ) ≤ U ^ (2 * η) := Nat.floor_le (by positivity)
  have ht0 : (0 : ℝ) < t := Nat.cast_pos.2 (by omega)
  have ht1' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have htle : (t : ℝ) ≤ U ^ (2 * η) := (Nat.cast_le.2 htT).trans hTn
  have hsplitU : U ^ (1 - 2 * η) = U / U ^ (2 * η) := by rw [Real.rpow_sub hU0, Real.rpow_one]
  have hylow : U ^ (1 - 2 * η) ≤ u / t := by
    rw [hsplitU]; exact div_le_div₀ (by linarith) hUu ht0 htle
  have hyhigh : u / t ≤ 2 * U := (div_le_self (by linarith) ht1').trans hu2
  have hy1 : 1 < u / t := by linarith
  have hy0 : 0 < u / t := by linarith
  have hlogy : (1 - 2 * η) * Real.log U ≤ Real.log (u / t) := by
    rw [← Real.log_rpow hU0]; exact Real.log_le_log (by positivity) hylow
  have hlog23 : 2 / 3 * Real.log U ≤ Real.log (u / t) := by nlinarith
  have hlogpos : 0 < Real.log (u / t) := Real.log_pos hy1
  have hlog2 : Real.log (u / t) ≤ Real.log (2 * (u / t)) := Real.log_le_log hy0 (by linarith)
  have hlogU : Real.log (u / t) ≤ Real.log (2 * U) := Real.log_le_log hy0 hyhigh
  refine ⟨hy₀.trans hylow, hy1, hyhigh, ?_, ?_, ?_⟩
  · exact hlow.trans (Real.rpow_le_rpow (by positivity) (hlog23.trans hlog2) (by norm_num))
  · have := Real.rpow_le_rpow hlogpos.le hlogU (show (0 : ℝ) ≤ 11 / 10 by norm_num)
    linarith
  · have hsqrt : U ^ (1 / 2 - η) ≤ Real.sqrt (u / t) := by
      have e : Real.sqrt (U ^ (1 - 2 * η)) = U ^ (1 / 2 - η) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hU0.le]; congr 1; ring
      rw [← e]; exact Real.sqrt_le_sqrt hylow
    have hl2 : 0 < Real.log (2 * U) ^ 2 := by
      have : 0 < Real.log (2 * U) := hlogpos.trans_le hlogU
      positivity
    have hA : U ^ (2 * η) ≤ U ^ (1 / 2 - η) / Real.log (2 * U) ^ 2 := by
      rw [le_div_iff₀ hl2]; exact hT
    have hB : U ^ (1 / 2 - η) / Real.log (2 * U) ^ 2 ≤ Real.sqrt (u / t) / Real.log (2 * U) ^ 2 :=
      div_le_div_of_nonneg_right hsqrt hl2.le
    have hC : Real.sqrt (u / t) / Real.log (2 * U) ^ 2 ≤ Real.sqrt (u / t) / Real.log (u / t) ^ 2 :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
        (pow_le_pow_left₀ hlogpos.le hlogU 2)
    exact hTn.trans (hA.trans (hB.trans hC))

/-- **Trading the logarithm for the top scale.**  For `1 < y ≤ Y`,
`√y/(6·10⁹ (log Y)^{9/20}) ≤ √y (log y)^{31/20} / (6·10⁹ (log y)²)`. -/
theorem sqrt_div_logpow_le {y Y : ℝ} (hy : 1 < y) (hyY : y ≤ Y) :
    Real.sqrt y / (6 * 10 ^ 9 * Real.log Y ^ (9 / 20 : ℝ)) ≤
      Real.sqrt y * Real.log y ^ (31 / 20 : ℝ) / (6 * 10 ^ 9 * Real.log y ^ 2) := by
  have hl : 0 < Real.log y := Real.log_pos hy
  have hlY : Real.log y ≤ Real.log Y := Real.log_le_log (by linarith) hyY
  have hsplit : Real.log y ^ 2 = Real.log y ^ (31 / 20 : ℝ) * Real.log y ^ (9 / 20 : ℝ) := by
    rw [← Real.rpow_add hl, ← Real.rpow_two]; norm_num
  have hmono : Real.log y ^ (9 / 20 : ℝ) ≤ Real.log Y ^ (9 / 20 : ℝ) :=
    Real.rpow_le_rpow hl.le hlY (by norm_num)
  have hY : 0 < Real.log Y ^ (9 / 20 : ℝ) := Real.rpow_pos_of_pos (hl.trans_le hlY) _
  rw [div_le_div_iff₀ (by positivity) (by positivity), hsplit]
  have hs : 0 ≤ Real.sqrt y * (6 * 10 ^ 9) * Real.log y ^ (31 / 20 : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left hmono hs
  linarith

/-- **Half the cofactor height.**  If `4 ≤ U^{2η}` then `U^{2η}/4 ≤ ⌊U^{2η}⌋/2` and `1 ≤ ⌊U^{2η}⌋/2`. -/
theorem cofactorHeight_half_ge {η U : ℝ} (h4 : 4 ≤ U ^ (2 * η)) :
    U ^ (2 * η) / 4 ≤ ((cofactorHeight η U / 2 : ℕ) : ℝ) ∧ 1 ≤ cofactorHeight η U / 2 := by
  have hfl := Nat.sub_one_lt_floor (U ^ (2 * η))
  unfold cofactorHeight
  set T := ⌊U ^ (2 * η)⌋₊ with hTdef
  have hT3 : 3 < (T : ℝ) := by linarith
  have hT4 : 4 ≤ T := by
    by_contra hc; push Not at hc
    have : (T : ℝ) ≤ 3 := by exact_mod_cast (show T ≤ 3 by omega)
    linarith
  have hdiv : T ≤ 2 * (T / 2) + 1 := by omega
  have hdiv' : (T : ℝ) ≤ 2 * ((T / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hdiv
  exact ⟨by linarith, by omega⟩

/-- `√(U^{2η}/4) = U^η/2`. -/
theorem sqrt_rpow_two_mul_div_four {η U : ℝ} (hU0 : 0 < U) :
    Real.sqrt (U ^ (2 * η) / 4) = U ^ η / 2 := by
  have e : U ^ (2 * η) / 4 = (U ^ η / 2) ^ 2 := by
    rw [div_pow, ← Real.rpow_two, ← Real.rpow_mul hU0.le, mul_comm η 2]; norm_num
  rw [e, Real.sqrt_sq (by positivity)]

/-- `t √(u/t) = √(ut)`. -/
theorem mul_sqrt_div_eq {u t : ℝ} (hu : 0 ≤ u) (ht : 0 < t) :
    t * Real.sqrt (u / t) = Real.sqrt (u * t) := by
  have h1 : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have h2 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  rw [Real.sqrt_div' u ht.le, Real.sqrt_mul hu, mul_div_assoc', div_eq_iff h2.ne', mul_assoc, h1,
    mul_comm]

/-- **The amplified width.**  For `1 ≤ t`, `1 < s/t` and `s ≤ 2U`:
`t H(s/t) ≤ 2 √(Ut) (log 2U)^{31/20}`. -/
theorem mul_naturalWidth_le {U s t : ℝ} (ht : 1 ≤ t) (hst : 1 < s / t) (hs2 : s ≤ 2 * U) :
    t * naturalWidth (s / t) ≤ 2 * Real.sqrt (U * t) * Real.log (2 * U) ^ (31 / 20 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < s := by
    have := (one_lt_div ht0).1 hst; linarith
  have hU0 : 0 < U := by linarith
  unfold naturalWidth
  rw [← mul_assoc, mul_sqrt_div_eq hs0.le ht0]
  have hsq : Real.sqrt (s * t) ≤ 2 * Real.sqrt (U * t) := by
    have h : s * t ≤ 2 ^ 2 * (U * t) := by nlinarith
    have := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_mul (show (0 : ℝ) ≤ 2 ^ 2 by norm_num),
      Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)] at this
  have hl0 : 0 ≤ Real.log (s / t) := (Real.log_pos hst).le
  have hlog : Real.log (s / t) ^ (31 / 20 : ℝ) ≤ Real.log (2 * U) ^ (31 / 20 : ℝ) :=
    Real.rpow_le_rpow hl0 (Real.log_le_log (by positivity)
      ((div_le_self hs0.le ht).trans hs2)) (by norm_num)
  exact mul_le_mul hsq hlog (Real.rpow_nonneg hl0 _) (by positivity)

/-- **The source half-width.**  For `1 ≤ x ≤ 2U` and `1 ≤ t`:
`√x (log x)^{31/20} ≤ 2 √(Ut) (log 2U)^{31/20}`. -/
theorem sqrt_logpow_le_two_mul {U x t : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2 * U) (ht : 1 ≤ t) :
    Real.sqrt x * Real.log x ^ (31 / 20 : ℝ) ≤
      2 * Real.sqrt (U * t) * Real.log (2 * U) ^ (31 / 20 : ℝ) := by
  have hU0 : 0 < U := by linarith
  have hsq : Real.sqrt x ≤ 2 * Real.sqrt (U * t) := by
    have h : x ≤ 2 ^ 2 * (U * t) := by nlinarith
    have := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_mul (show (0 : ℝ) ≤ 2 ^ 2 by norm_num),
      Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)] at this
  have hlog : Real.log x ^ (31 / 20 : ℝ) ≤ Real.log (2 * U) ^ (31 / 20 : ℝ) :=
    Real.rpow_le_rpow (Real.log_nonneg hx1) (Real.log_le_log (by linarith) hx2) (by norm_num)
  exact mul_le_mul hsq hlog (Real.rpow_nonneg (Real.log_nonneg hx1) _) (by positivity)

/-- **The displacement of the family.**  Every member `q` of the replacement family of a
squarefree source `u ∈ [U, 2U]` is squarefree with `μ(q) = -μ(u)` and
`u < q ≤ u + 8 U^{1/2+η} (log U)^{31/20}`. -/
theorem cofactorFamily_mem_facts {η U : ℝ} (hU0 : 0 < U) (hL1 : 1 ≤ Real.log U)
    (hzT : cofactorBandHigh U < cofactorHeight η U)
    (hadm : ∀ t : ℕ, 1 ≤ t → t ≤ cofactorHeight η U → ∀ u : ℝ, U ≤ u → u ≤ 2 * U → 1 < u / t)
    {u : ℕ} (hUu : U ≤ u) (hu2 : (u : ℝ) ≤ 2 * U) (hμ : ArithmeticFunction.moebius u ≠ 0) {q : ℕ}
    (hq : q ∈ cofactorFamily (cofactorBandLow U) (cofactorBandHigh U) (cofactorHeight η U) u) :
    Squarefree q ∧ ArithmeticFunction.moebius q = -ArithmeticFunction.moebius u ∧ u < q ∧
      (q : ℝ) ≤ u + 8 * U ^ (1 / 2 + η) * Real.log U ^ (31 / 20 : ℝ) := by
  have hσ := CofactorParity.moebius_eq_one_or_neg_one
    (ArithmeticFunction.moebius_ne_zero_iff_squarefree.1 hμ)
  unfold cofactorFamily at hq
  obtain ⟨t, ht, hq⟩ := Finset.mem_biUnion.1 hq
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hq
  obtain ⟨-, hsq, hμq, hlo, hhi⟩ := cofactor_bandToken_facts hzT hσ ht hm
  obtain ⟨ht1, htT⟩ := Finset.mem_Icc.1 (Finset.mem_filter.1 ht).1
  have hy1 := hadm t ht1 htT u hUu hu2
  have ht0 : (0 : ℝ) < t := Nat.cast_pos.2 (by omega)
  have ht1' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  refine ⟨hsq, hμq, ?_, ?_⟩
  · have h : (u : ℝ) < t * m := by
      rw [div_lt_iff₀ ht0] at hlo; linarith
    exact_mod_cast h
  · have hw := mul_naturalWidth_le ht1' hy1 hu2
    have htm : ((t * m : ℕ) : ℝ) ≤ u + t * naturalWidth ((u : ℝ) / t) := by
      push_cast
      have := mul_le_mul_of_nonneg_left hhi ht0.le
      rw [mul_add, mul_div_cancel₀ _ ht0.ne'] at this
      exact this
    have hTn : (cofactorHeight η U : ℝ) ≤ U ^ (2 * η) := Nat.floor_le (by positivity)
    have htle : (t : ℝ) ≤ U ^ (2 * η) := (Nat.cast_le.2 htT).trans hTn
    have hsqrt : Real.sqrt (U * t) ≤ U ^ (1 / 2 + η) := by
      have e : (U ^ (1 / 2 + η)) ^ 2 = U * U ^ (2 * η) := by
        rw [← Real.rpow_two, ← Real.rpow_mul hU0.le, show (1 / 2 + η) * 2 = 1 + 2 * η by ring,
          Real.rpow_add hU0, Real.rpow_one]
      rw [Real.sqrt_le_left (by positivity), e]
      exact mul_le_mul_of_nonneg_left htle hU0.le
    have hlog := log_two_mul_rpow_le (a := 31 / 20) hU0 hL1 (by norm_num)
    have h4 : (2 : ℝ) ^ (31 / 20 : ℝ) ≤ 4 := by
      have := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
        (show (31 / 20 : ℝ) ≤ 2 by norm_num)
      rw [Real.rpow_two] at this; linarith
    have hlog4 : Real.log (2 * U) ^ (31 / 20 : ℝ) ≤ 4 * Real.log U ^ (31 / 20 : ℝ) :=
      hlog.trans (mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg (by linarith) _))
    have hfin : 2 * Real.sqrt (U * t) * Real.log (2 * U) ^ (31 / 20 : ℝ) ≤
        8 * U ^ (1 / 2 + η) * Real.log U ^ (31 / 20 : ℝ) := by
      calc 2 * Real.sqrt (U * t) * Real.log (2 * U) ^ (31 / 20 : ℝ)
          ≤ 2 * U ^ (1 / 2 + η) * (4 * Real.log U ^ (31 / 20 : ℝ)) :=
            mul_le_mul (by linarith) hlog4
              (Real.rpow_nonneg (by linarith [Real.log_le_log hU0 (by linarith : U ≤ 2 * U)]) _)
              (by positivity)
        _ = 8 * U ^ (1 / 2 + η) * Real.log U ^ (31 / 20 : ℝ) := by ring
    linarith

/-- **The size of the family.**  If every admissible window `(u/t, u/t + H(u/t)]` carries at least
`√(u/t)/(6·10⁹ (log 2U)^{9/20})` band tokens and the band-avoiding cofactors of sign `μ(u)` have
`Σ t^{-1/2} ≥ (1/8)√(T/2) - 1`, then the family has at least `(η/10¹³) U^{1/2+η}/(log U)^{9/20}`
members. -/
theorem cofactorFamily_card_ge {η U : ℝ} (hη1 : η < 1 / 6) (hU0 : 0 < U) (hL1 : 1 ≤ Real.log U)
    (hzT : cofactorBandHigh U < cofactorHeight η U) (h32 : 32 ≤ U ^ η)
    {u : ℕ} (hUu : U ≤ u) (hσ : ArithmeticFunction.moebius u = 1 ∨ ArithmeticFunction.moebius u = -1)
    (hwin : ∀ t ∈ bandCofactors (cofactorBandLow U) (cofactorBandHigh U)
        (ArithmeticFunction.moebius u) (cofactorHeight η U),
      Real.sqrt ((u : ℝ) / t) / (6 * 10 ^ 9 * Real.log (2 * U) ^ (9 / 20 : ℝ)) ≤
        ((bandTokens (cofactorBandLow U + 1) (cofactorBandHigh U) (cofactorHeight η U) ((u : ℝ) / t)
          (naturalWidth ((u : ℝ) / t))).card : ℝ))
    (hsum : (1 / 8 : ℝ) * Real.sqrt ((cofactorHeight η U / 2 : ℕ) : ℝ) - 1 ≤
      ∑ t ∈ bandCofactors (cofactorBandLow U) (cofactorBandHigh U) (ArithmeticFunction.moebius u)
        (cofactorHeight η U), 1 / Real.sqrt (t : ℝ)) :
    η / 10 ^ 13 * U ^ (1 / 2 + η) / Real.log U ^ (9 / 20 : ℝ) ≤
      ((cofactorFamily (cofactorBandLow U) (cofactorBandHigh U) (cofactorHeight η U) u).card : ℝ) := by
  rw [card_cofactorFamily hzT hσ]
  set Λ := Real.log (2 * U) ^ (9 / 20 : ℝ) with hΛdef
  set ℓ := Real.log U ^ (9 / 20 : ℝ) with hℓdef
  have hℓ : 0 < ℓ := Real.rpow_pos_of_pos (by linarith) _
  have hΛℓ : Λ ≤ 2 * ℓ := by
    have h := log_two_mul_rpow_le (a := 9 / 20) hU0 hL1 (by norm_num)
    have h2 : (2 : ℝ) ^ (9 / 20 : ℝ) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
        (show (9 / 20 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    exact h.trans (mul_le_mul_of_nonneg_right h2 hℓ.le)
  have hΛ : 0 < Λ := by
    have : 1 ≤ Real.log (2 * U) := by
      rw [Real.log_mul (by norm_num) hU0.ne']; linarith [Real.log_two_gt_d9]
    exact Real.rpow_pos_of_pos (by linarith) _
  -- the cofactor height side
  have h4 : 4 ≤ U ^ (2 * η) := by
    have e : U ^ (2 * η) = U ^ η * U ^ η := by rw [← Real.rpow_add hU0]; ring_nf
    rw [e]; nlinarith
  have hsqrtT : U ^ η / 2 ≤ Real.sqrt ((cofactorHeight η U / 2 : ℕ) : ℝ) := by
    rw [← sqrt_rpow_two_mul_div_four hU0]
    exact Real.sqrt_le_sqrt (cofactorHeight_half_ge h4).1
  have hS : U ^ η / 32 ≤ ∑ t ∈ bandCofactors (cofactorBandLow U) (cofactorBandHigh U)
      (ArithmeticFunction.moebius u) (cofactorHeight η U), 1 / Real.sqrt (t : ℝ) := by
    linarith
  set c := Real.sqrt U / (6 * 10 ^ 9 * Λ) with hcdef
  have hc : 0 ≤ c := by positivity
  have hterm : ∀ t ∈ bandCofactors (cofactorBandLow U) (cofactorBandHigh U)
      (ArithmeticFunction.moebius u) (cofactorHeight η U),
      c * (1 / Real.sqrt (t : ℝ)) ≤
        ((bandTokens (cofactorBandLow U + 1) (cofactorBandHigh U) (cofactorHeight η U)
          ((u : ℝ) / t) (naturalWidth ((u : ℝ) / t))).card : ℝ) := by
    intro t ht
    refine le_trans ?_ (hwin t ht)
    have hsq : Real.sqrt U * (1 / Real.sqrt (t : ℝ)) ≤ Real.sqrt ((u : ℝ) / t) := by
      rw [Real.sqrt_div' _ (Nat.cast_nonneg t), mul_one_div]
      exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hUu) (Real.sqrt_nonneg _)
    rw [hcdef, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hsq (by positivity)
  have hmain : c * (U ^ η / 32) ≤ ∑ t ∈ bandCofactors (cofactorBandLow U) (cofactorBandHigh U)
      (ArithmeticFunction.moebius u) (cofactorHeight η U),
        ((bandTokens (cofactorBandLow U + 1) (cofactorBandHigh U) (cofactorHeight η U)
          ((u : ℝ) / t) (naturalWidth ((u : ℝ) / t))).card : ℝ) :=
    (mul_le_mul_of_nonneg_left hS hc).trans ((Finset.mul_sum _ _ _).trans_le
      (Finset.sum_le_sum hterm))
  refine le_trans ?_ hmain
  have hP : U ^ (1 / 2 + η) = Real.sqrt U * U ^ η := by
    rw [Real.rpow_add hU0, Real.sqrt_eq_rpow]
  have hPnn : 0 ≤ Real.sqrt U * U ^ η := by positivity
  have e : c * (U ^ η / 32) = Real.sqrt U * U ^ η / (192 * 10 ^ 9 * Λ) := by
    rw [hcdef]; field_simp; ring
  rw [e, hP]
  have h1 : Real.sqrt U * U ^ η / (384 * 10 ^ 9 * ℓ) ≤ Real.sqrt U * U ^ η / (192 * 10 ^ 9 * Λ) :=
    div_le_div_of_nonneg_left hPnn (by positivity) (by linarith)
  have h2 : η / 10 ^ 13 * (Real.sqrt U * U ^ η) / ℓ ≤ Real.sqrt U * U ^ η / (384 * 10 ^ 9 * ℓ) := by
    rw [div_le_div_iff₀ hℓ (by positivity)]
    have hηc : η * (384 * 10 ^ 9) / 10 ^ 13 ≤ 1 := by
      rw [div_le_one (by norm_num)]; linarith
    have := mul_le_mul_of_nonneg_right hηc (mul_nonneg hPnn hℓ.le)
    nlinarith [this]
  exact h2.trans h1

/-- **One grid source.**  Let `4D ≤ U`, `2√(Ut)(log 2U)^{31/20} ≤ D/2` and `k < ⌊U/(2D)⌋`.  The
source `s` chosen in `(x, x + √x (log x)^{31/20}]`, `x = U + kD`, lies in `[U, 2U]` with `μ(s) = -1`,
and every band token `m` of the window `(s/t, s/t + H(s/t)]` has `U + kD < tm ≤ U + (k+1)D`. -/
theorem cofactor_grid_facts {U x₀ D : ℝ} {src : ℝ → ℕ}
    (hsrc : ∀ x, x₀ ≤ x → x < src x ∧
      (src x : ℝ) ≤ x + Real.sqrt x * Real.log x ^ (31 / 20 : ℝ) ∧
      ArithmeticFunction.moebius (src x) = -1)
    (hx₀ : x₀ ≤ U) (hU1 : 1 ≤ U) {t : ℕ} (ht1 : 1 ≤ t) (hD0 : 0 < D)
    (hDw : 2 * Real.sqrt (U * t) * Real.log (2 * U) ^ (31 / 20 : ℝ) ≤ D / 2) (hDU : 4 * D ≤ U)
    (hwin1 : ∀ u : ℝ, U ≤ u → u ≤ 2 * U → 1 < u / t) {k : ℕ} (hk : k < ⌊U / (2 * D)⌋₊)
    {z₀ z T : ℕ} :
    (U ≤ (src (U + k * D) : ℝ) ∧ (src (U + k * D) : ℝ) ≤ 2 * U ∧
      ArithmeticFunction.moebius (src (U + k * D)) = -1) ∧
    ∀ m ∈ bandTokens z₀ z T ((src (U + k * D) : ℝ) / t) (naturalWidth ((src (U + k * D) : ℝ) / t)),
      U + k * D < (t : ℝ) * m ∧ (t : ℝ) * m ≤ U + (k + 1) * D := by
  have hkD : (k : ℝ) * D ≤ U / 2 := by
    have h := Nat.lt_of_lt_floor hk
    rw [lt_div_iff₀ (by positivity)] at h
    nlinarith
  have hk0 : (0 : ℝ) ≤ k * D := by positivity
  obtain ⟨hxs, hs, hμ⟩ := hsrc (U + k * D) (by linarith)
  have ht1' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have ht0 : (0 : ℝ) < t := by linarith
  have hw := sqrt_logpow_le_two_mul (U := U) (x := U + k * D) (t := t) (by linarith) (by linarith)
    ht1'
  have hs2 : (src (U + k * D) : ℝ) ≤ 2 * U := by linarith
  have hsU : U ≤ (src (U + k * D) : ℝ) := by linarith
  refine ⟨⟨hsU, hs2, hμ⟩, fun m hm => ?_⟩
  obtain ⟨hlo, hhi⟩ := bandTokens_mem_bounds hm
  have hst := hwin1 _ hsU hs2
  have hW := mul_naturalWidth_le ht1' hst hs2
  have h1 : (src (U + k * D) : ℝ) < t * m := by
    rw [div_lt_iff₀ ht0] at hlo; linarith
  have h2 : (t : ℝ) * m ≤ src (U + k * D) + t * naturalWidth ((src (U + k * D) : ℝ) / t) := by
    have := mul_le_mul_of_nonneg_left hhi ht0.le
    rwa [mul_add, mul_div_cancel₀ _ ht0.ne'] at this
  constructor <;> linarith

/-- The grid of targets: products `t·m` over the band-avoiding cofactors `t` of sign `-1`, the grid
positions `k < K(t)`, and the band tokens `m` of the window of the source `srcs t k`. -/
def cofactorGrid (z₀ z Tn : ℕ) (K : ℕ → ℕ) (srcs : ℕ → ℕ → ℕ) : Finset ℕ :=
  (bandCofactors z₀ z (-1) Tn).biUnion fun t => (Finset.range (K t)).biUnion fun k =>
    (bandTokens (z₀ + 1) z Tn ((srcs t k : ℝ) / t) (naturalWidth ((srcs t k : ℝ) / t))).image (t * ·)

/-- **The grid is counted without overlap.**  Distinct cofactors are decoded, and distinct grid
positions `k` put `t·m` in the disjoint intervals `(a + k d, a + (k+1) d]`. -/
theorem card_cofactorGrid {z₀ z Tn : ℕ} {K : ℕ → ℕ} {srcs : ℕ → ℕ → ℕ} {a : ℝ} {d : ℕ → ℝ}
    (hzT : z < Tn) (hd : ∀ t ∈ bandCofactors z₀ z (-1) Tn, 0 < d t)
    (hsep : ∀ t ∈ bandCofactors z₀ z (-1) Tn, ∀ k < K t,
      ∀ m ∈ bandTokens (z₀ + 1) z Tn ((srcs t k : ℝ) / t) (naturalWidth ((srcs t k : ℝ) / t)),
        a + k * d t < (t : ℝ) * m ∧ (t : ℝ) * m ≤ a + (k + 1) * d t) :
    ((cofactorGrid z₀ z Tn K srcs).card : ℝ) =
      ∑ t ∈ bandCofactors z₀ z (-1) Tn, ∑ k ∈ Finset.range (K t),
        ((bandTokens (z₀ + 1) z Tn ((srcs t k : ℝ) / t)
          (naturalWidth ((srcs t k : ℝ) / t))).card : ℝ) := by
  classical
  unfold cofactorGrid
  rw [Finset.card_biUnion]
  · push_cast
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht0 : 0 < t := (Finset.mem_Icc.1 (Finset.mem_filter.1 ht).1).1
    rw [Finset.card_biUnion]
    · push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.card_image_of_injective _ (fun a b hab => Nat.eq_of_mul_eq_mul_left ht0 hab)]
    · intro k hk k' hk' hkk
      rw [Function.onFun, Finset.disjoint_left]
      intro q hq hq'
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hq
      obtain ⟨m', hm', he⟩ := Finset.mem_image.1 hq'
      have hmm : m' = m := Nat.eq_of_mul_eq_mul_left ht0 he
      subst hmm
      have h1 := hsep t ht k (Finset.mem_range.1 hk) m' hm
      have h2 := hsep t ht k' (Finset.mem_range.1 hk') m' hm'
      have hd0 := hd t ht
      apply hkk
      have a1 : (k : ℝ) * d t < (k' + 1) * d t := by linarith [h1.1, h2.2]
      have a2 : (k' : ℝ) * d t < (k + 1) * d t := by linarith [h2.1, h1.2]
      have b1 : (k : ℝ) < k' + 1 := lt_of_mul_lt_mul_right a1 hd0.le
      have b2 : (k' : ℝ) < k + 1 := lt_of_mul_lt_mul_right a2 hd0.le
      have c1 : k < k' + 1 := by exact_mod_cast b1
      have c2 : k' < k + 1 := by exact_mod_cast b2
      omega
  · intro t ht t' ht' htt
    rw [Function.onFun, Finset.disjoint_left]
    intro q hq hq'
    obtain ⟨k, -, hq⟩ := Finset.mem_biUnion.1 hq
    obtain ⟨k', -, hq'⟩ := Finset.mem_biUnion.1 hq'
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨m', hm', he⟩ := Finset.mem_image.1 hq'
    exact htt (cofactor_mul_inj hzT (Or.inr rfl) (Or.inr rfl) ht ht' hm hm' he.symm).1

/-- **The grid lies in the physical union.**  Each grid target belongs to the family of its source,
a squarefree integer of sign `-1` in `[U, 2U]`. -/
theorem cofactorGrid_subset {U : ℝ} {z₀ z Tn : ℕ} {K : ℕ → ℕ} {srcs : ℕ → ℕ → ℕ}
    (hs : ∀ t ∈ bandCofactors z₀ z (-1) Tn, ∀ k < K t, U ≤ (srcs t k : ℝ) ∧
      (srcs t k : ℝ) ≤ 2 * U ∧ ArithmeticFunction.moebius (srcs t k) = -1) :
    cofactorGrid z₀ z Tn K srcs ⊆
      ((Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊).filter fun u => ArithmeticFunction.moebius u ≠ 0).biUnion
        (cofactorFamily z₀ z Tn) := by
  intro q hq
  unfold cofactorGrid at hq
  obtain ⟨t, ht, hq⟩ := Finset.mem_biUnion.1 hq
  obtain ⟨k, hk, hq⟩ := Finset.mem_biUnion.1 hq
  obtain ⟨hU, h2U, hμ⟩ := hs t ht k (Finset.mem_range.1 hk)
  refine Finset.mem_biUnion.2 ⟨srcs t k, Finset.mem_filter.2
    ⟨Finset.mem_Icc.2 ⟨Nat.ceil_le.2 hU, Nat.le_floor h2U⟩, by rw [hμ]; norm_num⟩, ?_⟩
  unfold cofactorFamily
  rw [hμ]
  exact Finset.mem_biUnion.2 ⟨t, ht, hq⟩

/-- **Per-cofactor count.**  With `K ≥ U/(4D)`, `D = 4√(Ut) Λ^{31/20}`, the `K` windows of
`√U/(6·10⁹ Λ^{9/20}) · t^{-1/2}` tokens each give at least `U/(96·10⁹ t Λ²)`. -/
theorem per_cofactor_bound {U t Lg K : ℝ} (hU0 : 0 < U) (ht : 1 ≤ t) (hLg : 0 < Lg)
    (hK : U / (4 * (4 * Real.sqrt (U * t) * Lg ^ (31 / 20 : ℝ))) ≤ K) :
    U / (96 * 10 ^ 9 * t * Lg ^ 2) ≤
      K * (Real.sqrt U / (6 * 10 ^ 9 * Lg ^ (9 / 20 : ℝ)) * (1 / Real.sqrt t)) := by
  have ht0 : 0 < t := by linarith
  have hs := Real.sqrt_pos.2 hU0
  have hr := Real.sqrt_pos.2 ht0
  have hsplit : Lg ^ 2 = Lg ^ (31 / 20 : ℝ) * Lg ^ (9 / 20 : ℝ) := by
    rw [← Real.rpow_add hLg, ← Real.rpow_two]; norm_num
  have ha := Real.rpow_pos_of_pos hLg (31 / 20)
  have hb := Real.rpow_pos_of_pos hLg (9 / 20)
  have hc : 0 ≤ Real.sqrt U / (6 * 10 ^ 9 * Lg ^ (9 / 20 : ℝ)) * (1 / Real.sqrt t) := by positivity
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right hK hc)
  have hss : Real.sqrt U * Real.sqrt U = U := Real.mul_self_sqrt hU0.le
  have hrr : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  rw [Real.sqrt_mul hU0.le, hsplit]
  generalize Real.sqrt U = s at *
  generalize Real.sqrt t = r at *
  subst hss hrr
  field_simp
  ring

/-- **The physical union.**  Given sources of sign `-1` in every interval
`(x, x + √x (log x)^{31/20}]`, `x ≥ x₀`, admissible windows carrying
`√(u/t)/(6·10⁹ (log 2U)^{9/20})` band tokens, and `Σ_{t, μ(t) = -1} 1/t ≥ η log U/16`, the union of
the families of the squarefree `u ∈ [U, 2U]` has at least `(η/10¹³) U/log U` members. -/
theorem card_union_cofactorFamily_ge {η U x₀ : ℝ} {src : ℝ → ℕ}
    (hsrc : ∀ x, x₀ ≤ x → x < src x ∧
      (src x : ℝ) ≤ x + Real.sqrt x * Real.log x ^ (31 / 20 : ℝ) ∧
      ArithmeticFunction.moebius (src x) = -1)
    (hη0 : 0 < η) (hx₀ : x₀ ≤ U) (hU0 : 0 < U) (hL1 : 1 ≤ Real.log U)
    (hzT : cofactorBandHigh U < cofactorHeight η U)
    (hD : 16 * U ^ η * Real.log (2 * U) ^ (31 / 20 : ℝ) ≤ Real.sqrt U)
    (hwin : ∀ t : ℕ, 1 ≤ t → t ≤ cofactorHeight η U → ∀ u : ℝ, U ≤ u → u ≤ 2 * U →
      1 < u / t ∧ Real.sqrt (u / t) / (6 * 10 ^ 9 * Real.log (2 * U) ^ (9 / 20 : ℝ)) ≤
        ((bandTokens (cofactorBandLow U + 1) (cofactorBandHigh U) (cofactorHeight η U) (u / t)
          (naturalWidth (u / t))).card : ℝ))
    (hsum : η * Real.log U / 16 ≤ ∑ t ∈ bandCofactors (cofactorBandLow U) (cofactorBandHigh U) (-1)
        (cofactorHeight η U), 1 / (t : ℝ)) :
    η / 10 ^ 13 * U / Real.log U ≤
      ((((Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊).filter fun u => ArithmeticFunction.moebius u ≠ 0).biUnion
        (cofactorFamily (cofactorBandLow U) (cofactorBandHigh U) (cofactorHeight η U))).card : ℝ) := by
  set Lg := Real.log (2 * U) with hLgdef
  set z₀ := cofactorBandLow U
  set z := cofactorBandHigh U
  set Tn := cofactorHeight η U with hTndef
  have hLg1 : 1 ≤ Lg := by
    rw [hLgdef, Real.log_mul (by norm_num) hU0.ne']; linarith [Real.log_two_gt_d9]
  have hLg0 : 0 < Lg := by linarith
  have hU1 : 1 ≤ U := by linarith [Real.log_le_sub_one_of_pos hU0]
  set D : ℕ → ℝ := fun t => 4 * Real.sqrt (U * t) * Lg ^ (31 / 20 : ℝ) with hDdef
  set K : ℕ → ℕ := fun t => ⌊U / (2 * D t)⌋₊ with hKdef
  set srcs : ℕ → ℕ → ℕ := fun t k => src (U + k * D t) with hsrcsdef
  have hTn : (Tn : ℝ) ≤ U ^ (2 * η) := Nat.floor_le (by positivity)
  have hmemt : ∀ t ∈ bandCofactors z₀ z (-1) Tn, 1 ≤ t ∧ t ≤ Tn := fun t ht =>
    Finset.mem_Icc.1 (Finset.mem_filter.1 ht).1
  have hDpos : ∀ t : ℕ, 1 ≤ t → 0 < D t := by
    intro t ht
    have : (0 : ℝ) < t := Nat.cast_pos.2 (by omega)
    simp only [hDdef]; positivity
  have hDU : ∀ t : ℕ, t ≤ Tn → 4 * D t ≤ U := by
    intro t htT
    have htle : (t : ℝ) ≤ U ^ (2 * η) := (Nat.cast_le.2 htT).trans hTn
    have hsqt : Real.sqrt t ≤ U ^ η := by
      rw [Real.sqrt_le_left (by positivity), ← Real.rpow_two, ← Real.rpow_mul hU0.le, mul_comm]
      exact htle
    have hsU : Real.sqrt U * Real.sqrt U = U := Real.mul_self_sqrt hU0.le
    have hLgp : 0 ≤ Lg ^ (31 / 20 : ℝ) := Real.rpow_nonneg hLg0.le _
    simp only [hDdef]
    rw [Real.sqrt_mul hU0.le]
    calc 4 * (4 * (Real.sqrt U * Real.sqrt t) * Lg ^ (31 / 20 : ℝ))
        = Real.sqrt U * (16 * Real.sqrt t * Lg ^ (31 / 20 : ℝ)) := by ring
      _ ≤ Real.sqrt U * (16 * U ^ η * Lg ^ (31 / 20 : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hLgp)
            (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt U * Real.sqrt U := mul_le_mul_of_nonneg_left hD (Real.sqrt_nonneg _)
      _ = U := hsU
  have hgrid : ∀ t ∈ bandCofactors z₀ z (-1) Tn, ∀ k < K t,
      (U ≤ (srcs t k : ℝ) ∧ (srcs t k : ℝ) ≤ 2 * U ∧ ArithmeticFunction.moebius (srcs t k) = -1) ∧
      ∀ m ∈ bandTokens (z₀ + 1) z Tn ((srcs t k : ℝ) / t) (naturalWidth ((srcs t k : ℝ) / t)),
        U + k * D t < (t : ℝ) * m ∧ (t : ℝ) * m ≤ U + (k + 1) * D t := by
    intro t ht k hk
    obtain ⟨ht1, htT⟩ := hmemt t ht
    exact cofactor_grid_facts hsrc hx₀ hU1 ht1 (hDpos t ht1) (by simp only [hDdef]; linarith)
      (hDU t htT) (fun u hUu hu2 => (hwin t ht1 htT u hUu hu2).1) hk
  have hsub := cofactorGrid_subset (U := U) (z₀ := z₀) (z := z) (Tn := Tn) (K := K) (srcs := srcs)
    (fun t ht k hk => (hgrid t ht k hk).1)
  have hcard := card_cofactorGrid (a := U) (d := D) (K := K) (srcs := srcs) hzT
    (fun t ht => hDpos t (hmemt t ht).1) (fun t ht k hk m hm => (hgrid t ht k hk).2 m hm)
  refine le_trans ?_ (Nat.cast_le.2 (Finset.card_le_card hsub))
  rw [hcard]
  have hper : ∀ t ∈ bandCofactors z₀ z (-1) Tn, U / (96 * 10 ^ 9 * Lg ^ 2) * (1 / (t : ℝ)) ≤
      ∑ k ∈ Finset.range (K t), ((bandTokens (z₀ + 1) z Tn ((srcs t k : ℝ) / t)
        (naturalWidth ((srcs t k : ℝ) / t))).card : ℝ) := by
    intro t ht
    obtain ⟨ht1, htT⟩ := hmemt t ht
    have ht1' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
    have hterm : ∀ k ∈ Finset.range (K t),
        Real.sqrt U / (6 * 10 ^ 9 * Lg ^ (9 / 20 : ℝ)) * (1 / Real.sqrt t) ≤
          ((bandTokens (z₀ + 1) z Tn ((srcs t k : ℝ) / t)
            (naturalWidth ((srcs t k : ℝ) / t))).card : ℝ) := by
      intro k hk
      obtain ⟨⟨hU, h2U, -⟩, -⟩ := hgrid t ht k (Finset.mem_range.1 hk)
      refine le_trans ?_ (hwin t ht1 htT _ hU h2U).2
      have hsq : Real.sqrt U * (1 / Real.sqrt t) ≤ Real.sqrt ((srcs t k : ℝ) / t) := by
        rw [Real.sqrt_div' _ (Nat.cast_nonneg t), mul_one_div]
        exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hU) (Real.sqrt_nonneg _)
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hsq (by positivity)
    have hsumk := Finset.card_nsmul_le_sum _ _ _ hterm
    rw [Finset.card_range, nsmul_eq_mul] at hsumk
    have hK : U / (4 * D t) ≤ (K t : ℝ) := by
      have hfl := Nat.sub_one_lt_floor (U / (2 * D t))
      have hDt := hDpos t ht1
      have h1 : 1 ≤ U / (4 * D t) := by
        rw [le_div_iff₀ (by linarith)]; linarith [hDU t htT]
      have e : U / (2 * D t) = 2 * (U / (4 * D t)) := by field_simp; ring
      simp only [hKdef]; linarith
    have hb := per_cofactor_bound hU0 ht1' hLg0 (K := (K t : ℝ)) hK
    have e : U / (96 * 10 ^ 9 * Lg ^ 2) * (1 / (t : ℝ)) = U / (96 * 10 ^ 9 * t * Lg ^ 2) := by
      field_simp
    rw [e]
    exact hb.trans hsumk
  have hL0 : 0 < Real.log U := by linarith
  have hcoef : 0 ≤ U / (96 * 10 ^ 9 * Lg ^ 2) := by positivity
  have hmain : U / (96 * 10 ^ 9 * Lg ^ 2) * (η * Real.log U / 16) ≤
      ∑ t ∈ bandCofactors z₀ z (-1) Tn, ∑ k ∈ Finset.range (K t),
        ((bandTokens (z₀ + 1) z Tn ((srcs t k : ℝ) / t)
          (naturalWidth ((srcs t k : ℝ) / t))).card : ℝ) :=
    (mul_le_mul_of_nonneg_left hsum hcoef).trans
      ((Finset.mul_sum _ _ _).trans_le (Finset.sum_le_sum hper))
  refine le_trans ?_ hmain
  have hLg2 : Lg ^ 2 ≤ 4 * Real.log U ^ 2 := by
    have : Lg ≤ 2 * Real.log U := by
      rw [hLgdef, Real.log_mul (by norm_num) hU0.ne']; linarith [Real.log_two_lt_d9]
    nlinarith
  have e1 : U / (96 * 10 ^ 9 * Lg ^ 2) * (η * Real.log U / 16) =
      η * U * Real.log U / (1536 * 10 ^ 9 * Lg ^ 2) := by
    field_simp; ring
  have hnum : 0 ≤ η * U * Real.log U := by positivity
  have h1 : η * U * Real.log U / (1536 * 10 ^ 9 * (4 * Real.log U ^ 2)) ≤
      η * U * Real.log U / (1536 * 10 ^ 9 * Lg ^ 2) :=
    div_le_div_of_nonneg_left hnum (by positivity) (by linarith)
  have e2 : η * U * Real.log U / (1536 * 10 ^ 9 * (4 * Real.log U ^ 2)) =
      η / (6144 * 10 ^ 9) * U / Real.log U := by
    field_simp; ring
  have h2 : η / 10 ^ 13 * U / Real.log U ≤ η / (6144 * 10 ^ 9) * U / Real.log U := by
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hU0.le) hL0.le
    exact div_le_div_of_nonneg_left hη0.le (by norm_num) (by norm_num)
  rw [e1]
  exact h2.trans (e2 ▸ h1)

/-- **Sources of sign `-1` in every short interval.**  Assume `(E1)` and `(E2)`.  For large `x`,
the interval `(x, x + √x (log x)^{31/20}]` contains an `E₃` number, of Möbius sign `-1`. -/
theorem exists_moebius_neg_one_short (hDI : MTDeshouillersIwaniecBound) (hW : MTWattBound) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∃ u : ℕ, x < u ∧
      (u : ℝ) ≤ x + Real.sqrt x * Real.log x ^ (31 / 20 : ℝ) ∧
      ArithmeticFunction.moebius u = -1 := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (eventually_exists_coprime_threePrime hDI hW one_pos)
  refine ⟨max x₀ 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  obtain ⟨p₁, p₂, p₃, h₁, h₂, h₃, h12, h13, h23, -, -, -, -, -, -, -, -, hlo, hhi⟩ :=
    hx₀ x ((le_max_left _ _).trans hx) 1 le_rfl (by rw [Real.rpow_one]; exact_mod_cast hx1)
  refine ⟨p₁ * p₂ * p₃, hlo, hhi.trans ?_,
    moebius_mul_three_distinct_primes h₁ h₂ h₃ h12 h13 h23⟩
  have h := amplified_window_le (u := x) (ℓ := 1) le_rfl hx1
  simp only [div_one, one_mul, mul_one] at h
  linarith

/-- **Cofactor-amplified `E₃` token supply.**  Assume `(E1)` and `(E2)`, and let `0 < η < 1/6`.  For
large `U`, with the band `(⌊(log U)^{1.09}⌋, ⌊2 (log U)^{1.1}⌋]` and cofactor height `⌊U^{2η}⌋`, the
source-fixed families `Q(u) = {t·m}` satisfy, for every squarefree `u ∈ [U, 2U]`:

* every `q ∈ Q(u)` is squarefree, `μ(q) = -μ(u)` and `0 < q - u ≤ 8 U^{1/2+η} (log U)^{31/20}`;
* `#Q(u) ≥ (η/10¹³) U^{1/2+η} / (log U)^{9/20}`;

and the physical union of the `Q(u)` over the squarefree `u ∈ [U, 2U]` has at least
`(η/10¹³) U / log U` members. -/
theorem eventually_cofactor_amplified_supply (hDI : MTDeshouillersIwaniecBound)
    (hW : MTWattBound) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 6) :
    ∀ᶠ U : ℝ in atTop,
      (∀ u : ℕ, U ≤ u → (u : ℝ) ≤ 2 * U → ArithmeticFunction.moebius u ≠ 0 →
        ∀ q ∈ cofactorFamily (cofactorBandLow U) (cofactorBandHigh U) (cofactorHeight η U) u,
          Squarefree q ∧ ArithmeticFunction.moebius q = -ArithmeticFunction.moebius u ∧ u < q ∧
            (q : ℝ) ≤ u + 8 * U ^ (1 / 2 + η) * Real.log U ^ (31 / 20 : ℝ)) ∧
      (∀ u : ℕ, U ≤ u → (u : ℝ) ≤ 2 * U → ArithmeticFunction.moebius u ≠ 0 →
        η / 10 ^ 13 * U ^ (1 / 2 + η) / Real.log U ^ (9 / 20 : ℝ) ≤
          ((cofactorFamily (cofactorBandLow U) (cofactorBandHigh U) (cofactorHeight η U) u).card :
            ℝ)) ∧
      η / 10 ^ 13 * U / Real.log U ≤
        ((((Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊).filter fun u => ArithmeticFunction.moebius u ≠ 0).biUnion
          (cofactorFamily (cofactorBandLow U) (cofactorBandHigh U) (cofactorHeight η U))).card :
            ℝ) := by
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.1 (eventually_card_bandTokens_ge hDI hW)
  obtain ⟨x₀, hx₀⟩ := exists_moebius_neg_one_short hDI hW
  choose! src hsrc using hx₀
  have hsqb := Real.tendsto_log_atTop.eventually
    (eventually_sum_inv_sqrt_parityClass_band_ge (a₀ := 108 / 100) (a₁ := 11 / 10) (by norm_num)
      (by norm_num))
  have hinvb := Real.tendsto_log_atTop.eventually
    (eventually_sum_inv_parityClass_band_ge (a₀ := 108 / 100) (a₁ := 11 / 10) (by norm_num)
      (by norm_num))
  filter_upwards [eventually_cofactor_band_facts, eventually_cofactor_height_facts hη0 hη1 y₀,
    hsqb, hinvb, eventually_ge_atTop x₀, eventually_gt_atTop (0 : ℝ)]
    with U hband hheight hsq hinv hUx₀ hU0
  obtain ⟨hL1, h2low, hlowhigh, hlow108, hhigh2, hlow, hhigh⟩ := hband
  obtain ⟨hyU, h2U, hTheight, hT, hD, h9, h32⟩ := hheight
  have hzT : cofactorBandHigh U < cofactorHeight η U := by
    have hfl := Nat.sub_one_lt_floor (U ^ (2 * η))
    have : (cofactorBandHigh U : ℝ) < cofactorHeight η U := by unfold cofactorHeight; linarith
    exact_mod_cast this
  have hwin : ∀ t : ℕ, 1 ≤ t → t ≤ cofactorHeight η U → ∀ u : ℝ, U ≤ u → u ≤ 2 * U →
      1 < u / t ∧ Real.sqrt (u / t) / (6 * 10 ^ 9 * Real.log (2 * U) ^ (9 / 20 : ℝ)) ≤
        ((bandTokens (cofactorBandLow U + 1) (cofactorBandHigh U) (cofactorHeight η U) (u / t)
          (naturalWidth (u / t))).card : ℝ) := by
    intro t ht1 htT u hUu hu2
    obtain ⟨hy₀', hy1, hy2, hz₀, hz, hTy⟩ :=
      cofactor_window_admissible hη1 hU0 hyU h2U hL1 hlow hhigh hT ht1 htT hUu hu2
    exact ⟨hy1, (sqrt_div_logpow_le hy1 hy2).trans
      (hy₀ (u / t) hy₀' (cofactorBandLow U + 1) (cofactorBandHigh U) (cofactorHeight η U) hz₀ hz
        hTy)⟩
  have h4 : 4 ≤ U ^ (2 * η) := by
    have e : U ^ (2 * η) = U ^ η * U ^ η := by rw [← Real.rpow_add hU0]; ring_nf
    rw [e]; nlinarith
  refine ⟨fun u hUu hu2 hμ q hq => cofactorFamily_mem_facts hU0 hL1 hzT
    (fun t ht1 htT u hUu hu2 => (hwin t ht1 htT u hUu hu2).1) hUu hu2 hμ hq,
    fun u hUu hu2 hμ => ?_, ?_⟩
  · have hσ := CofactorParity.moebius_eq_one_or_neg_one
      (ArithmeticFunction.moebius_ne_zero_iff_squarefree.1 hμ)
    refine cofactorFamily_card_ge hη1 hU0 hL1 hzT h32 hUu hσ (fun t ht => ?_)
      (hsq _ _ h2low hlowhigh hlow108 hhigh2 _ hσ _)
    obtain ⟨ht1, htT⟩ := Finset.mem_Icc.1 (Finset.mem_filter.1 ht).1
    exact (hwin t ht1 htT u hUu hu2).2
  · obtain ⟨hTlow, hT1⟩ := cofactorHeight_half_ge h4
    have hlogsum := hinv _ _ h2low hlowhigh hlow108 hhigh2 (-1) (Or.inr rfl) _ hT1
    have hlogT : 2 * η * Real.log U - 2 ≤ Real.log ((cofactorHeight η U / 2 : ℕ) : ℝ) := by
      have hpos : 0 < U ^ (2 * η) / 4 := by positivity
      have h := Real.log_le_log hpos hTlow
      rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hU0] at h
      have hl4 : Real.log 4 < 2 := by
        have e : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        rw [e]; linarith [Real.log_two_lt_d9]
      linarith
    exact card_union_cofactorFamily_ge hsrc hη0 hUx₀ hU0 hL1 hzT hD hwin (by linarith)

end

end RHTower.Sieve
