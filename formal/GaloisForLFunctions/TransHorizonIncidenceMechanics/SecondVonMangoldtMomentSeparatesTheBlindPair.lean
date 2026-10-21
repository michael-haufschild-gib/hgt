import GaloisForLFunctions.TransHorizonIncidenceMechanics.FirstMomentBlindParityPairOfTheNegatedMoebiusWeight

/-!
# The second von Mangoldt moment separates the first-moment-blind pair

For a nonnegative arithmetic weight `a` with divisor sums `Σ_{e|d} a(e) = g(d)`, regrouping the
products `d = ek` gives the **divisor pairing** `Σ_d c(d) g(d)/d = Σ_e a(e) W_c(e)`. With `a = Λ`,
`g = log` this is the first-moment law; with the second von Mangoldt function
`Λ₂ = Λ·log + Λ ⋆ Λ`, `g = log²` (from `Λ ⋆ 1 = log` and `log(ab) = log a + log b`). Since
`Σ_d c(d) log² d / d = −M(c·log)`, the **first pronic moment of the logarithmic weight** reads
`Σ_e Λ₂(e) W_c(e)`, and `Λ₂` lives on the moduli with at most two prime factors.

For the first-moment-blind pair `c_b = 2ρδ₁ − μd^{-ε}` and `c'_ε`,
`W_{c_b}(e) − W_{c'}(e) = −ρ_ε (μ(e) + μ(e)²)/D_ε(e)` for `e ≥ 2`, which vanishes on prime powers and
is `−2ρ_ε/D_ε(pq)` on `e = pq`. Hence
`M(c_b·log) − M(c'·log) = Σ_e Λ₂(e) ρ_ε (μ(e) + μ(e)²)/D_ε(e) > 0`:
**the logarithmic first moment separates the pair, through the moduli `pq` alone.**
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- **The divisor pairing.** For `a ≥ 0` with `Σ_{e|d} a(e) = g(d)`:
`Σ_d c(d) g(d)/d = Σ_e a(e) W_c(e)`. -/
theorem tsum_divisorPairing {c g a : ℕ → ℝ} (ha : ∀ e, 0 ≤ a e)
    (hdiv : ∀ d : ℕ, d ≠ 0 → ∑ e ∈ d.divisors, a e = g d)
    (hs : Summable (fun d : ℕ => c d / d))
    (hg : Summable (fun d : ℕ => |c d| * g d / d)) :
    ∑' d : ℕ, c d * g d / d = ∑' e : ℕ, a e * weightRamanujanCoeff c e := by
  have hg0 : ∀ d : ℕ, d ≠ 0 → 0 ≤ g d := fun d hd => by
    rw [← hdiv d hd]; exact sum_nonneg fun e _ => ha e
  set H : ℕ × ℕ → ℝ := fun p => a p.1 * (c (p.1 * p.2) / ((p.1 * p.2 : ℕ) : ℝ))
  have hfiber : ∀ d : ℕ, d ≠ 0 → ∀ (f : ℝ → ℝ),
      ∑ p ∈ d.divisorsAntidiagonal, a p.1 * f (c (p.1 * p.2) / ((p.1 * p.2 : ℕ) : ℝ)) =
        g d * f (c d / d) := by
    intro d hd f
    rw [Nat.sum_divisorsAntidiagonal (fun x y => a x * f (c (x * y) / ((x * y : ℕ) : ℝ))),
      ← hdiv d hd, sum_mul]
    exact sum_congr rfl fun e he => by rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he)]
  have hH0 : ∀ p : ℕ × ℕ, p.1 * p.2 = 0 → H p = 0 := fun p hp => by
    simp only [H, hp, Nat.cast_zero, div_zero, mul_zero]
  have hHabs : Summable (fun p => |H p|) := by
    refine summable_of_sum_le (c := ∑' d : ℕ, |c d| * g d / d) (fun p => abs_nonneg _)
      fun u => ?_
    have hmaps : ∀ p ∈ u, p.1 * p.2 ∈ u.image (fun p : ℕ × ℕ => p.1 * p.2) :=
      fun p hp => mem_image_of_mem _ hp
    rw [← sum_fiberwise_of_maps_to hmaps]
    refine (sum_le_sum fun d _ => ?_).trans (hg.sum_le_tsum _ fun d _ => by
      rcases eq_or_ne d 0 with rfl | hd
      · simp
      · have := hg0 d hd; positivity)
    rcases eq_or_ne d 0 with rfl | hd
    · rw [sum_eq_zero fun p hp => by rw [hH0 p (mem_filter.mp hp).2, abs_zero]]
      simp
    · calc ∑ p ∈ u with p.1 * p.2 = d, |H p| ≤ ∑ p ∈ d.divisorsAntidiagonal, |H p| :=
            sum_le_sum_of_subset_of_nonneg (fun p hp => by
              rw [mem_filter] at hp; exact Nat.mem_divisorsAntidiagonal.mpr ⟨hp.2, hd⟩)
              fun _ _ _ => abs_nonneg _
        _ = g d * |c d / d| := by
            have := hfiber d hd (fun x => |x|)
            rw [← this]
            exact sum_congr rfl fun p _ => by
              simp only [H]; rw [abs_mul, abs_of_nonneg (ha _)]
        _ = |c d| * g d / d := by
            rw [abs_div, Nat.abs_cast]; ring
  have hH : Summable H := hHabs.of_abs
  have hprod : ∑' p, H p = ∑' d : ℕ, c d * g d / d := by
    refine (hH.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)).tsum_eq.symm.trans ?_
    refine tsum_congr fun d => ?_
    rcases eq_or_ne d 0 with rfl | hd
    · have h0 : ∑' p : ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0}), H p = 0 := by
        rw [tsum_congr (fun p : ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0}) => hH0 p.1 p.2),
          tsum_zero]
      rw [h0]; simp
    · rw [show (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {d} = d.divisorsAntidiagonal by ext; simp [hd],
        Finset.tsum_subtype' d.divisorsAntidiagonal H]
      have := hfiber d hd id
      simp only [id] at this
      rw [this]; ring
  have hrow : ∀ e : ℕ, HasSum (fun k => H (e, k)) (a e * weightRamanujanCoeff c e) := by
    intro e
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp [H, weightRamanujanCoeff]
    · have hinj : Function.Injective (fun k : ℕ => e * k) := fun x y h =>
        Nat.eq_of_mul_eq_mul_left he h
      have hk := (hs.comp_injective hinj).hasSum.mul_left (a e)
      rw [weightRamanujanCoeff]
      exact hk
  rw [← hprod]
  exact (hH.hasSum.prod_fiberwise hrow).tsum_eq.symm

/-! ### The second von Mangoldt function -/

/-- `Λ₂ = Λ·log + Λ ⋆ Λ`. -/
def secondVonMangoldt : ArithmeticFunction ℝ :=
  ArithmeticFunction.vonMangoldt.pmul ArithmeticFunction.log + Λ * Λ

theorem secondVonMangoldt_nonneg (n : ℕ) : 0 ≤ secondVonMangoldt n := by
  rw [secondVonMangoldt, ArithmeticFunction.add_apply, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.mul_apply, ArithmeticFunction.log_apply]
  exact add_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg n))
    (sum_nonneg fun _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      ArithmeticFunction.vonMangoldt_nonneg)

/-- `Σ_{e | d} Λ₂(e) = log² d`. -/
theorem sum_divisors_secondVonMangoldt {d : ℕ} (hd : d ≠ 0) :
    ∑ e ∈ d.divisors, secondVonMangoldt e = Real.log d * Real.log d := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply, secondVonMangoldt, add_mul, mul_assoc,
    ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.add_apply,
    ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.mul_apply]
  simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.log_apply]
  rw [← Nat.sum_divisorsAntidiagonal (fun a _ => Λ a * Real.log a), ← sum_add_distrib]
  have h : ∀ p ∈ d.divisorsAntidiagonal, Λ p.1 * Real.log p.1 + Λ p.1 * Real.log p.2 =
      Λ p.1 * Real.log d := fun p hp => by
    obtain ⟨hpd, -⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have h1 : (p.1 : ℝ) ≠ 0 := by
      have : p.1 ≠ 0 := fun h => hd (by rw [← hpd, h, zero_mul])
      exact_mod_cast this
    have h2 : (p.2 : ℝ) ≠ 0 := by
      have : p.2 ≠ 0 := fun h => hd (by rw [← hpd, h, mul_zero])
      exact_mod_cast this
    rw [← mul_add, ← Real.log_mul h1 h2, ← Nat.cast_mul, hpd]
  rw [sum_congr rfl h, ← sum_mul, Nat.sum_divisorsAntidiagonal (fun a _ => Λ a),
    ArithmeticFunction.vonMangoldt_sum]

theorem secondVonMangoldt_le (n : ℕ) : secondVonMangoldt n ≤ Real.log n * Real.log n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [secondVonMangoldt]
  · rw [← sum_divisors_secondVonMangoldt hn]
    exact single_le_sum (fun e _ => secondVonMangoldt_nonneg e) (Nat.mem_divisors_self n hn)

/-- `Λ₂(6) ≥ Λ(2)Λ(3) > 0`: the second function sees the modulus `2·3`. -/
theorem secondVonMangoldt_six_pos : 0 < secondVonMangoldt 6 := by
  have h : Λ 2 * Λ 3 ≤ (Λ * Λ) 6 := by
    rw [ArithmeticFunction.mul_apply]
    have hmem : ((2, 3) : ℕ × ℕ) ∈ (6 : ℕ).divisorsAntidiagonal := by
      rw [Nat.mem_divisorsAntidiagonal]; norm_num
    exact single_le_sum (f := fun p : ℕ × ℕ => Λ p.1 * Λ p.2) (fun p _ =>
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg) hmem
  have h2 : 0 < Λ 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]; exact Real.log_pos (by norm_num)
  have h3 : 0 < Λ 3 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]; exact Real.log_pos (by norm_num)
  rw [secondVonMangoldt, ArithmeticFunction.add_apply, ArithmeticFunction.pmul_apply]
  have := mul_pos h2 h3
  have hnn : 0 ≤ Λ 6 * ArithmeticFunction.log 6 := by
    rw [ArithmeticFunction.log_apply]
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg 6)
  linarith

/-! ### The logarithmic first moment -/

/-- The logarithmic weight `c(d) log d`. -/
def logWeight (c : ℕ → ℝ) (d : ℕ) : ℝ := c d * Real.log d

theorem logWeight_mem_dampedClass {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ} (hc : DampedClass K ε c) :
    DampedClass (K * (2 / ε)) (ε / 2) (logWeight c) := fun d => by
  have hK := nonneg_of_dampedClass hc
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [logWeight, Real.zero_rpow (show -(ε / 2) ≠ 0 by linarith)]
  · have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hlog := Real.log_le_rpow_div (x := d) hd0.le (by linarith : 0 < ε / 2)
    have hlog0 := Real.log_natCast_nonneg d
    rw [logWeight, abs_mul, abs_of_nonneg hlog0]
    calc |c d| * Real.log d ≤ K * (d : ℝ) ^ (-ε) * ((d : ℝ) ^ (ε / 2) / (ε / 2)) :=
          mul_le_mul (hc d) hlog hlog0 (by positivity)
      _ = K * (2 / ε) * (d : ℝ) ^ (-(ε / 2)) := by
          rw [show -(ε / 2) = -ε + ε / 2 by ring, Real.rpow_add hd0]
          field_simp

theorem summable_secondVonMangoldt_mul_weightRamanujanCoeff {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) :
    Summable (fun e : ℕ => secondVonMangoldt e * weightRamanujanCoeff c e) := by
  have hK := nonneg_of_dampedClass hc
  set Z := ∑' k : ℕ, dampedSignWeight unitSign ε k / k
  have hZ := (unitDampedMass_pos hε).le
  have hu : DampedClass 1 ε (dampedSignWeight unitSign ε) := fun d => by
    rw [dampedSignWeight, unitSign, one_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  have hlog2 := summable_abs_mul_log_div_of_dampedClass (by linarith : 0 < ε / 2)
    (logWeight_mem_dampedClass hε hu)
  refine (hlog2.mul_left (K * Z)).of_norm_bounded fun e => ?_
  have hW := abs_weightRamanujanCoeff_le_of_dampedClass hε hc e
  have hΛ2 := secondVonMangoldt_le e
  have hl := Real.log_natCast_nonneg e
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (secondVonMangoldt_nonneg e), logWeight,
    dampedSignWeight, unitSign, one_mul, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg e) _), abs_of_nonneg hl]
  have hp : 0 ≤ K * Z * ((e : ℝ) ^ (-ε) / e) := by positivity
  calc secondVonMangoldt e * |weightRamanujanCoeff c e| ≤
        (Real.log e * Real.log e) * (K * Z * ((e : ℝ) ^ (-ε) / e)) :=
        mul_le_mul hΛ2 hW (abs_nonneg _) (mul_nonneg hl hl)
    _ = K * Z * ((e : ℝ) ^ (-ε) * Real.log e * Real.log e / e) := by ring

/-- **The logarithmic first moment.** On the damped class,
`M(c·log) = −Σ_d c(d) log² d / d = −Σ_e Λ₂(e) W_c(e)`. -/
theorem firstPronicMoment_logWeight {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ} (hc : DampedClass K ε c) :
    firstPronicMoment (logWeight c) = -∑' e : ℕ, secondVonMangoldt e * weightRamanujanCoeff c e := by
  have hcl := logWeight_mem_dampedClass hε hc
  have hε2 : 0 < ε / 2 := by linarith
  unfold firstPronicMoment
  rw [(hasSum_weightCenteredPrefix_div_pronic (summable_div_of_dampedClass hε2 hcl)
    (summable_abs_mul_log_div_of_dampedClass hε2 hcl)).tsum_eq]
  congr 1
  have hsq : ∀ d : ℕ, logWeight c d * Real.log d / d = c d * (Real.log d * Real.log d) / d :=
    fun d => by rw [logWeight]; ring
  rw [tsum_congr hsq]
  refine tsum_divisorPairing secondVonMangoldt_nonneg (fun d hd => sum_divisors_secondVonMangoldt hd)
    (summable_div_of_dampedClass hε hc) ?_
  refine (summable_abs_mul_log_div_of_dampedClass hε2 hcl).congr fun d => ?_
  rw [logWeight, abs_mul, abs_of_nonneg (Real.log_natCast_nonneg d)]; ring

/-- **The second moment separates the first-moment-blind pair.** For `0 < ε`:
`M(c_b·log) − M(c'·log) = Σ_e Λ₂(e) ρ_ε (μ(e) + μ(e)²)/D_ε(e) > 0`, a sum over the moduli `pq`. -/
theorem logMoment_separates_firstMomentBlind {ε : ℝ} (hε : 0 < ε) :
    firstPronicMoment (logWeight (negatedMoebiusWeight ε)) -
        firstPronicMoment (logWeight (parityTwinWeight ε)) =
      ∑' e : ℕ, secondVonMangoldt e * (dampedDensity ε *
        (((ArithmeticFunction.moebius e : ℤ) : ℝ) + ((ArithmeticFunction.moebius e : ℤ) : ℝ) ^ 2) /
          RHTower.pmPowerDampedRamanujanDenominator ε e) ∧
    0 < firstPronicMoment (logWeight (negatedMoebiusWeight ε)) -
        firstPronicMoment (logWeight (parityTwinWeight ε)) := by
  obtain ⟨K, hK⟩ := parityTwinWeight_mem_dampedClass hε
  have hb := negatedMoebiusWeight_mem_dampedClass hε
  have hε2 : 0 < ε / 2 := by linarith
  have hρ : 0 < dampedDensity ε := RHTower.pmPowerDampedDivisorDensity_re_pos hε
  have hsb := summable_secondVonMangoldt_mul_weightRamanujanCoeff hε hb
  have hsp := summable_secondVonMangoldt_mul_weightRamanujanCoeff hε2 hK
  -- termwise gap
  have hterm : ∀ e : ℕ, secondVonMangoldt e * weightRamanujanCoeff (parityTwinWeight ε) e -
      secondVonMangoldt e * weightRamanujanCoeff (negatedMoebiusWeight ε) e =
      secondVonMangoldt e * (dampedDensity ε *
        (((ArithmeticFunction.moebius e : ℤ) : ℝ) + ((ArithmeticFunction.moebius e : ℤ) : ℝ) ^ 2) /
          RHTower.pmPowerDampedRamanujanDenominator ε e) := fun e => by
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp [secondVonMangoldt]
    rcases eq_or_ne e 1 with rfl | he1
    · simp [secondVonMangoldt]
    rw [← mul_sub, weightRamanujanCoeff_parityTwin hε, weightRamanujanCoeff_negatedMoebius hε he,
      if_neg he1, dampedRamanujanCoeff_eq_closed hε]
    congr 1
    ring
  have hgap : firstPronicMoment (logWeight (negatedMoebiusWeight ε)) -
      firstPronicMoment (logWeight (parityTwinWeight ε)) =
      ∑' e : ℕ, secondVonMangoldt e * (dampedDensity ε *
        (((ArithmeticFunction.moebius e : ℤ) : ℝ) + ((ArithmeticFunction.moebius e : ℤ) : ℝ) ^ 2) /
          RHTower.pmPowerDampedRamanujanDenominator ε e) := by
    rw [firstPronicMoment_logWeight hε hb, firstPronicMoment_logWeight hε2 hK, neg_sub_neg,
      ← hsp.tsum_sub hsb]
    exact tsum_congr hterm
  refine ⟨hgap, ?_⟩
  rw [hgap]
  have hnn : ∀ e : ℕ, 0 ≤ secondVonMangoldt e * (dampedDensity ε *
      (((ArithmeticFunction.moebius e : ℤ) : ℝ) + ((ArithmeticFunction.moebius e : ℤ) : ℝ) ^ 2) /
        RHTower.pmPowerDampedRamanujanDenominator ε e) := fun e => by
    have hD := RHTower.pmPowerDampedRamanujanDenominator_pos hε e
    have hμ : 0 ≤ ((ArithmeticFunction.moebius e : ℤ) : ℝ) + ((ArithmeticFunction.moebius e : ℤ) : ℝ) ^ 2 := by
      rcases ArithmeticFunction.moebius_eq_or e with h | h | h <;> simp [h]
    exact mul_nonneg (secondVonMangoldt_nonneg e) (div_nonneg (mul_nonneg hρ.le hμ) hD.le)
  refine ((hsp.sub hsb).congr hterm).tsum_pos hnn 6 ?_
  have hD := RHTower.pmPowerDampedRamanujanDenominator_pos hε 6
  have hμ6 : ((ArithmeticFunction.moebius 6 : ℤ) : ℝ) = 1 := by
    have hcop : Nat.gcd 2 3 = 1 := by norm_num
    rw [show (6 : ℕ) = 2 * 3 by norm_num,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two,
      ArithmeticFunction.moebius_apply_prime Nat.prime_three]
    norm_num
  rw [hμ6]
  have := secondVonMangoldt_six_pos
  positivity

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
