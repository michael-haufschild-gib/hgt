import GaloisForLFunctions.RHTower.MontgomeryPhaseSeriesProducts
import GaloisForLFunctions.RHTower.MontgomeryPrimePowerPairs
import GaloisForLFunctions.RHTower.MontgomeryLeadingOrderLimits
import GaloisForLFunctions.RHTower.LorentzianZeroMass
import Mathlib.Analysis.MeanInequalities

/-!
# The 3-level form factor of ζ zeros vanishes below threshold

For the Lorentzian zero sum `S(x, t) = Σ_ρ x^{ρ−1/2}/(1 + (t + i(ρ − 1/2))²)` over all zeros of
`ξ` (no hypothesis on their real parts), Montgomery's lemma writes `Z = −2√x S = P + E` with the
prime side `P = e^{it log x} K_x`, `K_x(t) = Σ_n d_x(n) e^{−it log n}`, `d_x = primeAmp x`.

* **Theorem** (`tendsto_tripleFormFactor`): for `α, β > 0` with `α + β < 1`,
  `∫_0^T S(T^α, t) S(T^β, t) conj S(T^{α+β}, t) dt = o(T log T)`,
  while the pair forms `∫_0^T |S(T^α, t)|² dt` are of exact order `T log T`.

Proof. `S₁S₂S̄₃ = −Z₁Z₂Z̄₃/(8x₁x₂)` (`triple_S_eq`) and the phases of the prime sides cancel
(`primeSide_triple_eq`), so the main term is `∫ K₁K₂ conj K₃ = ∫ K[d₁ ⍟ d₂] conj K[d₃]`. By the
bilinear mean value theorem it is `T Σ (d₁ ⍟ d₂) d₃ + O(x₁²x₂² log²)`, and a product of two prime
powers is a prime power only for powers of one prime: the diagonal is at most `c₀ x₁x₂ T`,
`c₀ = Σ_m Λ(m)(Λ ⍟ Λ)(m)/m` (`norm_integral_primeConjSum_triple_le`) — `O(T)`, not `T log T`.
The remainder `E₁Z₂Z̄₃ + P₁E₂Z̄₃ + P₁P₂Ē₃` splits into the polar part `4x/(1+t²)`, against the
pointwise bounds `|Z| ≤ 256xΛ`, `|P| ≤ 261xΛ`, and the part `Λ/√x`, against the energies
`∫|Z|² ≤ 7Tx log T`, `∫|P|² ≤ 3Tx log T` (`norm_integral_triple_le`, `eventually_energy_bounds`).
-/

open Complex MeasureTheory Filter Topology
open ArithmeticFunction (vonMangoldt)
open scoped ComplexConjugate LSeries.notation

noncomputable section

namespace RHTower

open PhaseSeries PrimePowerPairs

/-! ### Prime amplitudes as prime-power sequences -/

theorem ppBound_primeAmp_half {x : ℝ} (hx : 1 ≤ x) : PPBound (primeAmp x) (Real.sqrt x) (1 / 2) := by
  intro n
  refine ⟨primeAmp_nonneg (by linarith) n, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [primeAmp]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have hy : 0 < x / n := by positivity
  have hfac : Real.sqrt x / (n : ℝ) ^ (1 / 2 : ℝ) = (x / n) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.div_rpow hx0.le hn'.le]
  rw [show Real.sqrt x * vonMangoldt n / (n : ℝ) ^ (1 / 2 : ℝ) =
    vonMangoldt n * (Real.sqrt x / (n : ℝ) ^ (1 / 2 : ℝ)) by ring, hfac]
  unfold primeAmp
  refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
  split_ifs with h
  · exact Real.rpow_le_rpow_of_exponent_le ((one_le_div hn').mpr h) (by norm_num)
  · exact Real.rpow_le_rpow_of_exponent_ge hy ((div_le_one hn').mpr (le_of_lt (not_le.mp h)))
      (by norm_num)

theorem ppBound_primeAmp_threeHalves {x : ℝ} (hx : 1 ≤ x) :
    PPBound (primeAmp x) (x ^ (3 / 2 : ℝ)) (3 / 2) := by
  intro n
  refine ⟨primeAmp_nonneg (by linarith) n, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [primeAmp]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have hfac : x ^ (3 / 2 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) = (x / n) ^ (3 / 2 : ℝ) := by
    rw [Real.div_rpow hx0.le hn'.le]
  rw [show x ^ (3 / 2 : ℝ) * vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ) =
    vonMangoldt n * (x ^ (3 / 2 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)) by ring, hfac]
  unfold primeAmp
  refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
  split_ifs with h
  · exact Real.rpow_le_rpow_of_exponent_le ((one_le_div hn').mpr h) (by norm_num)
  · exact le_rfl

/-- Cauchy–Schwarz for series: `(Σ uv)² ≤ Σ u² Σ v²`. -/
theorem sq_tsum_mul_le {u v : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (hu2 : Summable fun n => u n ^ 2) (hv2 : Summable fun n => v n ^ 2) :
    (∑' n, u n * v n) ^ 2 ≤ (∑' n, u n ^ 2) * ∑' n, v n ^ 2 := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have e : ∀ w : ℕ → ℝ, (fun n => w n ^ (2 : ℝ)) = fun n => w n ^ 2 := fun w => by
    funext n; exact Real.rpow_two _
  have h := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hu hv (by rw [e]; exact hu2)
    (by rw [e]; exact hv2)
  rw [e, e] at h
  have hA : 0 ≤ ∑' n, u n ^ 2 := tsum_nonneg fun n => sq_nonneg _
  have hB : 0 ≤ ∑' n, v n ^ 2 := tsum_nonneg fun n => sq_nonneg _
  have hS : 0 ≤ ∑' n, u n * v n := tsum_nonneg fun n => mul_nonneg (hu n) (hv n)
  calc (∑' n, u n * v n) ^ 2 ≤ ((∑' n, u n ^ 2) ^ (1 / 2 : ℝ) * (∑' n, v n ^ 2) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hS h 2
    _ = (∑' n, u n ^ 2) * ∑' n, v n ^ 2 := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hA, Real.sq_sqrt hB]

/-! ### The prime-side triple -/

/-- The prime amplitudes as complex coefficients. -/
def ampC (x : ℝ) : ℕ → ℂ := fun n => (primeAmp x n : ℂ)

theorem primeConjSum_eq_phaseSeries (x t : ℝ) : primeConjSum x t = phaseSeries (ampC x) t := by
  rw [phaseSeries_eq_tsum (by simp [ampC, primeAmp_zero])]; rfl

theorem ampC_conv (x₁ x₂ : ℝ) (n : ℕ) :
    (ampC x₁ ⍟ ampC x₂) n = ((primeAmp x₁ ⍟ primeAmp x₂) n : ℂ) := by
  rw [congrFun (LSeries.convolution_def _ _) n, congrFun (LSeries.convolution_def _ _) n]
  push_cast; rfl

/-- **The prime-side triple is small**: with `c₀ = Σ_m Λ(m)L(m)/m` and `c₁ = Σ_{pp} L(m)²/m`,
`‖∫_0^T K₁ K₂ conj K₃‖ ≤ c₀ T x₁x₂ + 208 (2 A₁A₂ + c₁ x₁²x₂² + A₃)`, `A_i = Σ n d_{x_i}(n)²`,
`x₃ = x₁x₂`. Only pairs of powers of one prime meet a prime power. -/
theorem norm_integral_primeConjSum_triple_le {x₁ x₂ : ℝ} (hx₁ : 1 ≤ x₁) (hx₂ : 1 ≤ x₂) {T : ℝ}
    (hT : 0 ≤ T) :
    ‖∫ t in (0 : ℝ)..T, primeConjSum x₁ t * primeConjSum x₂ t * conj (primeConjSum (x₁ * x₂) t)‖
      ≤ T * (x₁ * x₂) * (∑' m : ℕ, vonMangoldt m * LL m / m) +
        208 * (2 * (∑' n : ℕ, (n : ℝ) * primeAmp x₁ n ^ 2) * (∑' n : ℕ, (n : ℝ) * primeAmp x₂ n ^ 2)
          + x₁ ^ 2 * x₂ ^ 2 * (∑' m, ppWeight m) + ∑' n : ℕ, (n : ℝ) * primeAmp (x₁ * x₂) n ^ 2) := by
  have hx₃ : 1 ≤ x₁ * x₂ := one_le_mul_of_one_le_of_one_le hx₁ hx₂
  have h1 := ppBound_primeAmp_half hx₁
  have h2 := ppBound_primeAmp_half hx₂
  have h3 := ppBound_primeAmp_half hx₃
  have h1' := ppBound_primeAmp_threeHalves hx₁
  have h2' := ppBound_primeAmp_threeHalves hx₂
  have hd1 := fun n => primeAmp_nonneg (x := x₁) (by linarith) n
  have hd2 := fun n => primeAmp_nonneg (x := x₂) (by linarith) n
  have hd3 := fun n => primeAmp_nonneg (x := x₁ * x₂) (by linarith) n
  set c : ℕ → ℝ := primeAmp x₁ ⍟ primeAmp x₂ with hc
  have hc0 : ∀ n, 0 ≤ c n := conv_nonneg hd1 hd2
  -- summability of the convolution and its weighted energy
  have hcs : Summable c := (hasSum_conv hd1 hd2 (primeAmp_zero _) (primeAmp_zero _)
    (summable_primeAmp hx₁) (summable_primeAmp hx₂)).summable
  have hn12 : Summable fun n : ℕ => (n : ℝ) * (primeAmp x₁ n * primeAmp x₂ n) := by
    refine ((summable_mul_primeAmp_sq hx₁).add (summable_mul_primeAmp_sq hx₂)).of_nonneg_of_le
      (fun n => mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (hd1 n) (hd2 n))) fun n => ?_
    have := Nat.cast_nonneg (α := ℝ) n
    nlinarith [sq_nonneg (primeAmp x₁ n - primeAmp x₂ n), mul_nonneg this
      (sq_nonneg (primeAmp x₁ n - primeAmp x₂ n))]
  obtain ⟨hnc, hncle⟩ := sum_mul_sq_conv h1 h2 h1' h2' (summable_mul_primeAmp_sq hx₁)
    (summable_mul_primeAmp_sq hx₂) hn12
  obtain ⟨-, htri⟩ := conv_mul_le h1 h2 h3
  -- Cauchy–Schwarz for the weighted cross term
  have hcs2 : (∑' n : ℕ, (n : ℝ) * (primeAmp x₁ n * primeAmp x₂ n)) ^ 2 ≤
      (∑' n : ℕ, (n : ℝ) * primeAmp x₁ n ^ 2) * ∑' n : ℕ, (n : ℝ) * primeAmp x₂ n ^ 2 := by
    have := sq_tsum_mul_le (u := fun n => Real.sqrt n * primeAmp x₁ n)
      (v := fun n => Real.sqrt n * primeAmp x₂ n)
      (fun n => mul_nonneg (Real.sqrt_nonneg _) (hd1 n))
      (fun n => mul_nonneg (Real.sqrt_nonneg _) (hd2 n))
      (by simpa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] using summable_mul_primeAmp_sq hx₁)
      (by simpa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] using summable_mul_primeAmp_sq hx₂)
    have e1 : ∀ n : ℕ, Real.sqrt n * primeAmp x₁ n * (Real.sqrt n * primeAmp x₂ n) =
        (n : ℝ) * (primeAmp x₁ n * primeAmp x₂ n) := fun n => by
      rw [show Real.sqrt n * primeAmp x₁ n * (Real.sqrt n * primeAmp x₂ n) =
        (Real.sqrt n * Real.sqrt n) * (primeAmp x₁ n * primeAmp x₂ n) by ring,
        Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp_rw [e1, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at this
    exact this
  -- the bilinear mean value theorem for `K[c]` against `K[d₃]`
  have hcC0 : (fun n => (c n : ℂ)) 0 = 0 := by simp [hc, LSeries.convolution_map_zero]
  have hcCs : Summable fun n => ‖(fun n => (c n : ℂ)) n‖ := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 _)] using hcs
  have hcCn : Summable fun n : ℕ => (n : ℝ) * ‖(fun n => (c n : ℂ)) n‖ ^ 2 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 _), sq_abs] using hnc
  have hd3C : Summable fun n => ‖ampC (x₁ * x₂) n‖ := by
    simpa [ampC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd3 _)] using
      summable_primeAmp hx₃
  have hd3Cn : Summable fun n : ℕ => (n : ℝ) * ‖ampC (x₁ * x₂) n‖ ^ 2 := by
    simpa [ampC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd3 _), sq_abs] using
      summable_mul_primeAmp_sq hx₃
  have hmv := norm_integral_phaseSeries_mul_conj_sub_le hcC0 (by simp [ampC, primeAmp_zero])
    hcCs hd3C hcCn hd3Cn hT
  have hprod : ∀ t, primeConjSum x₁ t * primeConjSum x₂ t * conj (primeConjSum (x₁ * x₂) t) =
      phaseSeries (fun n => (c n : ℂ)) t * conj (phaseSeries (ampC (x₁ * x₂)) t) := fun t => by
    rw [primeConjSum_eq_phaseSeries, primeConjSum_eq_phaseSeries, primeConjSum_eq_phaseSeries,
      phaseSeries_mul (by simp [ampC, primeAmp_zero]) (by simp [ampC, primeAmp_zero])
        (by simpa [ampC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd1 _)] using
          summable_primeAmp hx₁)
        (by simpa [ampC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd2 _)] using
          summable_primeAmp hx₂)]
    congr 2
    funext n; rw [ampC_conv]
  simp_rw [hprod]
  -- the diagonal `Σ c(n) d₃(n)`
  have hdiag : T * ∑' n, (fun n => (c n : ℂ)) n * conj (ampC (x₁ * x₂) n) =
      ((T * ∑' n, c n * primeAmp (x₁ * x₂) n : ℝ) : ℂ) := by
    push_cast
    congr 1
    refine tsum_congr fun n => ?_
    simp [ampC, Complex.conj_ofReal]
  have hdiag_le : ‖((T * ∑' n, c n * primeAmp (x₁ * x₂) n : ℝ) : ℂ)‖ ≤
      T * (x₁ * x₂) * ∑' m : ℕ, vonMangoldt m * LL m / m := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hT
      (tsum_nonneg fun n => mul_nonneg (hc0 n) (hd3 n)))]
    have hsq : Real.sqrt x₁ * Real.sqrt x₂ * Real.sqrt (x₁ * x₂) = x₁ * x₂ := by
      rw [Real.sqrt_mul (by linarith), show Real.sqrt x₁ * Real.sqrt x₂ * (Real.sqrt x₁ *
        Real.sqrt x₂) = (Real.sqrt x₁ * Real.sqrt x₁) * (Real.sqrt x₂ * Real.sqrt x₂) by ring,
        Real.mul_self_sqrt (by linarith), Real.mul_self_sqrt (by linarith)]
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hT
    rw [hsq] at htri; exact htri
  have hnorm_c : ∑' n : ℕ, (n : ℝ) * ‖(fun n => (c n : ℂ)) n‖ ^ 2 = ∑' m : ℕ, (m : ℝ) * c m ^ 2 := by
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hnorm_d : ∑' n : ℕ, (n : ℝ) * ‖ampC (x₁ * x₂) n‖ ^ 2 =
      ∑' n : ℕ, (n : ℝ) * primeAmp (x₁ * x₂) n ^ 2 := by
    simp [ampC, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hdiag, hnorm_c, hnorm_d] at hmv
  have hab : Real.sqrt x₁ * Real.sqrt x₂ * x₁ ^ (3 / 2 : ℝ) * x₂ ^ (3 / 2 : ℝ) = x₁ ^ 2 * x₂ ^ 2 := by
    have e : ∀ y : ℝ, 0 ≤ y → Real.sqrt y * y ^ (3 / 2 : ℝ) = y ^ 2 := fun y hy => by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add' hy (by norm_num)]; norm_num
    rw [show Real.sqrt x₁ * Real.sqrt x₂ * x₁ ^ (3 / 2 : ℝ) * x₂ ^ (3 / 2 : ℝ) =
      (Real.sqrt x₁ * x₁ ^ (3 / 2 : ℝ)) * (Real.sqrt x₂ * x₂ ^ (3 / 2 : ℝ)) by ring,
      e x₁ (by linarith), e x₂ (by linarith)]
  rw [hab] at hncle
  calc ‖∫ t in (0 : ℝ)..T, phaseSeries (fun n => (c n : ℂ)) t * conj (phaseSeries (ampC (x₁ * x₂)) t)‖
      ≤ ‖((T * ∑' n, c n * primeAmp (x₁ * x₂) n : ℝ) : ℂ)‖ +
        208 * (∑' m : ℕ, (m : ℝ) * c m ^ 2 + ∑' n : ℕ, (n : ℝ) * primeAmp (x₁ * x₂) n ^ 2) := by
        have := norm_sub_norm_le (∫ t in (0 : ℝ)..T, phaseSeries (fun n => (c n : ℂ)) t *
          conj (phaseSeries (ampC (x₁ * x₂)) t)) ((T * ∑' n, c n * primeAmp (x₁ * x₂) n : ℝ) : ℂ)
        linarith
    _ ≤ _ := by
        have hA1 : 0 ≤ ∑' n : ℕ, (n : ℝ) * primeAmp x₁ n ^ 2 := tsum_nonneg fun n => by positivity
        have hA2 : 0 ≤ ∑' n : ℕ, (n : ℝ) * primeAmp x₂ n ^ 2 := tsum_nonneg fun n => by positivity
        nlinarith [hdiag_le, hncle, hcs2]

/-! ### The zero side and the remainder -/

/-- The zero side `Z = P + E = −2√x S` of Montgomery's lemma. -/
def zSide (x t : ℝ) : ℂ := primeSide x t + montgomeryRemainder x t

theorem zSide_eq {x : ℝ} (hx : 1 < x) (t : ℝ) :
    zSide x t = -2 * (Real.sqrt x : ℂ) * lorentzZeroSumAll x t := by
  have h := montgomeryRemainder_eq hx t
  have hc : (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) = (Real.sqrt x : ℂ) := by
    rw [← Complex.ofReal_cpow (by linarith), Real.sqrt_eq_rpow]
  rw [zSide, h, hc]; ring

/-- `S₁ S₂ conj S₃ = −Z₁ Z₂ conj Z₃ / (8 x₁ x₂)` for `x₃ = x₁ x₂`. -/
theorem triple_S_eq {x₁ x₂ : ℝ} (hx₁ : 1 < x₁) (hx₂ : 1 < x₂) (t : ℝ) :
    lorentzZeroSumAll x₁ t * lorentzZeroSumAll x₂ t * conj (lorentzZeroSumAll (x₁ * x₂) t) =
      -(1 / (8 * x₁ * x₂)) * (zSide x₁ t * zSide x₂ t * conj (zSide (x₁ * x₂) t)) := by
  have hx₃ : 1 < x₁ * x₂ := one_lt_mul_of_lt_of_le hx₁ hx₂.le
  rw [zSide_eq hx₁, zSide_eq hx₂, zSide_eq hx₃, map_mul, map_mul, Complex.conj_ofReal,
    map_neg, map_ofNat, Real.sqrt_mul (by linarith)]
  have h1 : (Real.sqrt x₁ : ℂ) * Real.sqrt x₁ = x₁ := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have h2 : (Real.sqrt x₂ : ℂ) * Real.sqrt x₂ = x₂ := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have hx0 : (x₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hx0' : (x₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  push_cast
  rw [show -(1 / (8 * (x₁ : ℂ) * x₂)) * (-2 * (Real.sqrt x₁ : ℂ) * lorentzZeroSumAll x₁ t *
      (-2 * (Real.sqrt x₂ : ℂ) * lorentzZeroSumAll x₂ t) *
      (-2 * ((Real.sqrt x₁ : ℂ) * Real.sqrt x₂) * conj (lorentzZeroSumAll (x₁ * x₂) t))) =
      ((Real.sqrt x₁ : ℂ) * Real.sqrt x₁) * ((Real.sqrt x₂ : ℂ) * Real.sqrt x₂) / (x₁ * x₂) *
      (lorentzZeroSumAll x₁ t * lorentzZeroSumAll x₂ t * conj (lorentzZeroSumAll (x₁ * x₂) t))
      by field_simp; ring, h1, h2, div_self (mul_ne_zero hx0 hx0'), one_mul]

/-- The phases of the prime sides cancel: `P₁ P₂ conj P₃ = K₁ K₂ conj K₃`. -/
theorem primeSide_triple_eq {x₁ x₂ : ℝ} (hx₁ : 1 ≤ x₁) (hx₂ : 1 ≤ x₂) (t : ℝ) :
    primeSide x₁ t * primeSide x₂ t * conj (primeSide (x₁ * x₂) t) =
      primeConjSum x₁ t * primeConjSum x₂ t * conj (primeConjSum (x₁ * x₂) t) := by
  rw [primeSide_eq_conjSum hx₁, primeSide_eq_conjSum hx₂,
    primeSide_eq_conjSum (one_le_mul_of_one_le_of_one_le hx₁ hx₂), map_mul, ← Complex.exp_conj,
    map_mul, Complex.conj_ofReal, Complex.conj_I,
    Real.log_mul (by linarith) (by linarith)]
  have hphase : Complex.exp (((t * Real.log x₁ : ℝ) : ℂ) * I) *
      Complex.exp (((t * Real.log x₂ : ℝ) : ℂ) * I) *
      Complex.exp (((t * (Real.log x₁ + Real.log x₂) : ℝ) : ℂ) * -I) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_zero]
    congr 1; push_cast; ring
  calc _ = (Complex.exp (((t * Real.log x₁ : ℝ) : ℂ) * I) *
        Complex.exp (((t * Real.log x₂ : ℝ) : ℂ) * I) *
        Complex.exp (((t * (Real.log x₁ + Real.log x₂) : ℝ) : ℂ) * -I)) *
        (primeConjSum x₁ t * primeConjSum x₂ t * conj (primeConjSum (x₁ * x₂) t)) := by ring
    _ = _ := by rw [hphase, one_mul]

/-- On `[0, T]`: `‖E‖ ≤ 4x/(1+t²) + Λ/√x` with `Λ ≥ C + log(T+4) + 16`. -/
theorem norm_montgomeryRemainder_le_window {x : ℝ} (hx : 1 < x) {T t Λ : ℝ} (ht : t ∈ Set.Icc 0 T)
    (hΛ : xbBlockConstant + Real.log (T + 4) + 16 ≤ Λ) :
    ‖montgomeryRemainder x t‖ ≤ 4 * x / (1 + t ^ 2) + Λ / Real.sqrt x := by
  have h := norm_montgomeryRemainder_le hx t
  have hx0 : 0 < x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hrpow : x ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt x := by
    rw [Real.rpow_neg hx0.le, Real.sqrt_eq_rpow, inv_eq_one_div]
  have hlog : Real.log (|t| + 4) ≤ Real.log (T + 4) := by
    rw [abs_of_nonneg ht.1]
    exact Real.log_le_log (by linarith [ht.1]) (by linarith [ht.2])
  have h16 : 16 * (x ^ 2)⁻¹ / (1 + |t|) ≤ 16 / Real.sqrt x := by
    have h1 : 16 * (x ^ 2)⁻¹ / (1 + |t|) ≤ 16 * (x ^ 2)⁻¹ :=
      div_le_self (by positivity) (by linarith [abs_nonneg t])
    refine h1.trans ?_
    rw [div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left (inv_anti₀ hs ?_) (by norm_num)
    calc Real.sqrt x ≤ x := by
          rw [Real.sqrt_le_left (by linarith)]; nlinarith
      _ ≤ x ^ 2 := by nlinarith
  have hb := xbBlockConstant_nonneg
  rw [hrpow] at h
  calc ‖montgomeryRemainder x t‖ ≤ 4 * x / (1 + t ^ 2) +
        1 / Real.sqrt x * (xbBlockConstant + Real.log (|t| + 4)) + 16 * (x ^ 2)⁻¹ / (1 + |t|) := h
    _ ≤ 4 * x / (1 + t ^ 2) + 1 / Real.sqrt x * (xbBlockConstant + Real.log (T + 4)) +
        16 / Real.sqrt x := by gcongr
    _ ≤ 4 * x / (1 + t ^ 2) + Λ / Real.sqrt x := by
        have e : (xbBlockConstant + Real.log (T + 4)) / Real.sqrt x + 16 / Real.sqrt x =
            (xbBlockConstant + Real.log (T + 4) + 16) / Real.sqrt x := by ring
        rw [one_div_mul_eq_div, add_assoc, e]
        gcongr

/-- On `[0, T]`: `‖Z‖ = 2√x ‖S‖ ≤ 256 x Λ`. -/
theorem norm_zSide_le_window {x : ℝ} (hx : 1 < x) {T t Λ : ℝ} (ht : t ∈ Set.Icc 0 T)
    (hΛ : xiLineTwoLogDerivConstant + Real.log (T + 4) ≤ Λ) :
    ‖zSide x t‖ ≤ 256 * x * Λ := by
  have hx0 : 0 ≤ x := by linarith
  rw [zSide_eq hx, norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg x)]
  have hS : ‖lorentzZeroSumAll x t‖ ≤ 16 * Real.sqrt x * lorentzMass t := by
    refine (norm_tsum_le_tsum_norm (summable_norm_zeroSumTerm hx.le t)).trans ?_
    rw [lorentzMass, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (norm_zeroSumTerm_le hx.le t) (summable_norm_zeroSumTerm hx.le t)
      ((summable_lorentzMassTerm t).mul_left _)
  have hM := lorentzMass_le_log t
  have hlog : Real.log (|t| + 4) ≤ Real.log (T + 4) := by
    rw [abs_of_nonneg ht.1]
    exact Real.log_le_log (by linarith [ht.1]) (by linarith [ht.2])
  have hM0 : 0 ≤ lorentzMass t := tsum_nonneg fun q => lorentzMassTerm_nonneg t q
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  calc 2 * Real.sqrt x * ‖lorentzZeroSumAll x t‖ ≤ 2 * Real.sqrt x * (16 * Real.sqrt x * lorentzMass t) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = 32 * (Real.sqrt x * Real.sqrt x) * lorentzMass t := by ring
    _ ≤ 32 * x * (8 * Λ) := by
        rw [hss]
        gcongr
        linarith
    _ = 256 * x * Λ := by ring

theorem continuousOn_zSide {x : ℝ} (hx : 1 < x) (T : ℝ) : ContinuousOn (zSide x) (Set.Icc 0 T) :=
  (continuous_primeSide hx.le).continuousOn.add (continuousOn_montgomeryRemainder hx T)

theorem mul_le_half_sq_add_sq (a b : ℝ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- `e u v ≤ q x U V + Λ r u v` from `e ≤ qx + Λr`, `u ≤ U`, `v ≤ V`. -/
theorem triple_term_le {e u v q x Λ r U V : ℝ} (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (hq : 0 ≤ q) (hx : 0 ≤ x) (he : e ≤ q * x + Λ * r) (hu : u ≤ U) (hv : v ≤ V) :
    e * u * v ≤ q * (x * U * V) + Λ * (r * u * v) := by
  have huv : u * v ≤ U * V := mul_le_mul hu hv hv0 (hu0.trans hu)
  have h1 : e * u * v ≤ (q * x + Λ * r) * u * v := by
    have := mul_le_mul_of_nonneg_right he (mul_nonneg hu0 hv0)
    nlinarith [this]
  have h2 : q * x * (u * v) ≤ q * x * (U * V) := mul_le_mul_of_nonneg_left huv (mul_nonneg hq hx)
  nlinarith [h1, h2]

theorem amgm_div_sqrt {u v x : ℝ} (hx : 0 < x) :
    1 / Real.sqrt x * u * v ≤ (u ^ 2 + v ^ 2 / x) / 2 := by
  have h := mul_le_half_sq_add_sq u (v / Real.sqrt x)
  rw [div_pow, Real.sq_sqrt hx.le] at h
  calc 1 / Real.sqrt x * u * v = u * (v / Real.sqrt x) := by ring
    _ ≤ _ := h

theorem amgm_div_sqrt_mul {u v x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    1 / (Real.sqrt x * Real.sqrt y) * u * v ≤ (u ^ 2 / x + v ^ 2 / y) / 2 := by
  have h := mul_le_half_sq_add_sq (u / Real.sqrt x) (v / Real.sqrt y)
  rw [div_pow, div_pow, Real.sq_sqrt hx.le, Real.sq_sqrt hy.le] at h
  calc 1 / (Real.sqrt x * Real.sqrt y) * u * v = u / Real.sqrt x * (v / Real.sqrt y) := by
        field_simp
    _ ≤ _ := h

/-- The real inequality behind the remainder majorant. -/
theorem remainder_combo_le {a b c Z₂ Z₃ P₁ P₂ q x₁ x₂ Λ : ℝ} (hZ₂0 : 0 ≤ Z₂) (hZ₃0 : 0 ≤ Z₃) (hP₁0 : 0 ≤ P₁) (hP₂0 : 0 ≤ P₂) (hq : 0 ≤ q)
    (hΛ : 0 ≤ Λ) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (ha : a ≤ q * x₁ + Λ * (1 / Real.sqrt x₁)) (hb : b ≤ q * x₂ + Λ * (1 / Real.sqrt x₂))
    (hc : c ≤ q * (x₁ * x₂) + Λ * (1 / (Real.sqrt x₁ * Real.sqrt x₂)))
    (hZ₂ : Z₂ ≤ 256 * x₂ * Λ) (hZ₃ : Z₃ ≤ 256 * (x₁ * x₂) * Λ) (hP₁ : P₁ ≤ 261 * x₁ * Λ)
    (hP₂ : P₂ ≤ 261 * x₂ * Λ) :
    a * Z₂ * Z₃ + P₁ * b * Z₃ + P₁ * P₂ * c ≤
      q * ((x₁ * (256 * x₂) * (256 * (x₁ * x₂)) + x₂ * (261 * x₁) * (256 * (x₁ * x₂)) +
        (x₁ * x₂) * (261 * x₁) * (261 * x₂)) * Λ ^ 2) +
      Λ / 2 * (Z₂ ^ 2 + Z₃ ^ 2 / x₁ + P₁ ^ 2 + Z₃ ^ 2 / x₂ + P₁ ^ 2 / x₁ + P₂ ^ 2 / x₂) := by
  have k₁ := triple_term_le hZ₂0 hZ₃0 hq hx₁.le ha hZ₂ hZ₃
  have k₂ := triple_term_le hP₁0 hZ₃0 hq hx₂.le hb hP₁ hZ₃
  have k₃ := triple_term_le hP₁0 hP₂0 hq (by positivity) hc hP₁ hP₂
  have m₁ := amgm_div_sqrt (u := Z₂) (v := Z₃) hx₁
  have m₂ := amgm_div_sqrt (u := P₁) (v := Z₃) hx₂
  have m₃ := amgm_div_sqrt_mul (u := P₁) (v := P₂) hx₁ hx₂
  have e₂ : P₁ * b * Z₃ = b * P₁ * Z₃ := by ring
  have e₃ : P₁ * P₂ * c = c * P₁ * P₂ := by ring
  rw [e₂, e₃]
  have l₁ := mul_le_mul_of_nonneg_left m₁ hΛ
  have l₂ := mul_le_mul_of_nonneg_left m₂ hΛ
  have l₃ := mul_le_mul_of_nonneg_left m₃ hΛ
  have hsum : q * (x₁ * (256 * x₂ * Λ) * (256 * (x₁ * x₂) * Λ)) +
      q * (x₂ * (261 * x₁ * Λ) * (256 * (x₁ * x₂) * Λ)) +
      q * (x₁ * x₂ * (261 * x₁ * Λ) * (261 * x₂ * Λ)) =
      q * ((x₁ * (256 * x₂) * (256 * (x₁ * x₂)) + x₂ * (261 * x₁) * (256 * (x₁ * x₂)) +
        (x₁ * x₂) * (261 * x₁) * (261 * x₂)) * Λ ^ 2) := by ring
  have hsum' : Λ * ((Z₂ ^ 2 + Z₃ ^ 2 / x₁) / 2) + Λ * ((P₁ ^ 2 + Z₃ ^ 2 / x₂) / 2) +
      Λ * ((P₁ ^ 2 / x₁ + P₂ ^ 2 / x₂) / 2) =
      Λ / 2 * (Z₂ ^ 2 + Z₃ ^ 2 / x₁ + P₁ ^ 2 + Z₃ ^ 2 / x₂ + P₁ ^ 2 / x₁ + P₂ ^ 2 / x₂) := by
    ring
  linarith

/-- **The triple assembly.** With `W(x) = ∫_0^T ‖Z‖²`, `W'(x) = ∫_0^T ‖P‖²`, `x₃ = x₁x₂` and
`Λ ≥ C + log(T+4)`:
`8x₁x₂ ‖∫ S₁S₂ conj S₃‖ ≤ ‖∫ K₁K₂ conj K₃‖ + 8Λ²(polar) + (Λ/2)(W₂ + W₃/x₁ + W'₁ + W₃/x₂ +
W'₁/x₁ + W'₂/x₂)`. The remainder `Z₁Z₂Z̄₃ − P₁P₂P̄₃ = E₁Z₂Z̄₃ + P₁E₂Z̄₃ + P₁P₂Ē₃` is split into
the polar part `4x/(1+t²)` (bounded by the sup of the other factors) and the part `Λ/√x`
(paired by `ab ≤ (a² + b²)/2`). -/
theorem norm_integral_triple_le {x₁ x₂ : ℝ} (hx₁ : 1 < x₁) (hx₂ : 1 < x₂) {T Λ : ℝ} (hT : 0 ≤ T)
    (hΛ : xbBlockConstant + xiLineTwoLogDerivConstant + 16 + Real.log (T + 4) ≤ Λ) :
    8 * x₁ * x₂ * ‖∫ t in (0 : ℝ)..T, lorentzZeroSumAll x₁ t * lorentzZeroSumAll x₂ t *
        conj (lorentzZeroSumAll (x₁ * x₂) t)‖ ≤
      ‖∫ t in (0 : ℝ)..T, primeConjSum x₁ t * primeConjSum x₂ t * conj (primeConjSum (x₁ * x₂) t)‖
      + 8 * Λ ^ 2 * (x₁ * (256 * x₂) * (256 * (x₁ * x₂)) + x₂ * (261 * x₁) * (256 * (x₁ * x₂)) +
          (x₁ * x₂) * (261 * x₁) * (261 * x₂))
      + Λ / 2 * ((∫ t in (0 : ℝ)..T, ‖zSide x₂ t‖ ^ 2) +
          (∫ t in (0 : ℝ)..T, ‖zSide (x₁ * x₂) t‖ ^ 2) / x₁ +
          (∫ t in (0 : ℝ)..T, ‖primeSide x₁ t‖ ^ 2) +
          (∫ t in (0 : ℝ)..T, ‖zSide (x₁ * x₂) t‖ ^ 2) / x₂ +
          (∫ t in (0 : ℝ)..T, ‖primeSide x₁ t‖ ^ 2) / x₁ +
          (∫ t in (0 : ℝ)..T, ‖primeSide x₂ t‖ ^ 2) / x₂) := by
  set x₃ := x₁ * x₂ with hx₃def
  have hx₃ : 1 < x₃ := one_lt_mul_of_lt_of_le hx₁ hx₂.le
  have hb := xbBlockConstant_nonneg
  have hξ := xiLineTwoLogDerivConstant_nonneg
  have hlog4 : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
  have hΛ1 : 1 ≤ Λ := by linarith
  have hΛE : xbBlockConstant + Real.log (T + 4) + 16 ≤ Λ := by linarith
  have hΛZ : xiLineTwoLogDerivConstant + Real.log (T + 4) ≤ Λ := by linarith
  have hs₁ : 0 < Real.sqrt x₁ := Real.sqrt_pos.mpr (by linarith)
  have hs₂ : 0 < Real.sqrt x₂ := Real.sqrt_pos.mpr (by linarith)
  have hsq₁ : Real.sqrt x₁ ^ 2 = x₁ := Real.sq_sqrt (by linarith)
  have hsq₂ : Real.sqrt x₂ ^ 2 = x₂ := Real.sq_sqrt (by linarith)
  have hs₃ : Real.sqrt x₃ = Real.sqrt x₁ * Real.sqrt x₂ := Real.sqrt_mul (by linarith) _
  -- pointwise bounds on the window
  have hP : ∀ x : ℝ, 1 < x → ∀ t ∈ Set.Icc 0 T, ‖primeSide x t‖ ≤ 261 * x * Λ := by
    intro x hx t ht
    have hZ := norm_zSide_le_window hx ht hΛZ
    have hE := norm_montgomeryRemainder_le_window hx ht hΛE
    have hPe : primeSide x t = zSide x t - montgomeryRemainder x t := by rw [zSide]; ring
    have hsx : 1 ≤ Real.sqrt x := by rw [Real.one_le_sqrt]; linarith
    have hpol : 4 * x / (1 + t ^ 2) ≤ 4 * x := div_le_self (by linarith) (by nlinarith)
    have hΛx : Λ / Real.sqrt x ≤ x * Λ := by
      rw [div_le_iff₀ (by linarith)]
      have h1 : 1 ≤ x * Real.sqrt x := one_le_mul_of_one_le_of_one_le hx.le hsx
      nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ Λ)]
    calc ‖primeSide x t‖ ≤ ‖zSide x t‖ + ‖montgomeryRemainder x t‖ := by
          rw [hPe]; exact norm_sub_le _ _
      _ ≤ 256 * x * Λ + (4 * x + x * Λ) := add_le_add hZ (hE.trans (add_le_add hpol hΛx))
      _ ≤ 261 * x * Λ := by nlinarith
  -- the decomposition of the integrand
  have hdec : ∀ t, lorentzZeroSumAll x₁ t * lorentzZeroSumAll x₂ t *
      conj (lorentzZeroSumAll x₃ t) = -(1 / (8 * x₁ * x₂)) *
      (primeConjSum x₁ t * primeConjSum x₂ t * conj (primeConjSum x₃ t) +
        (montgomeryRemainder x₁ t * zSide x₂ t * conj (zSide x₃ t) +
          primeSide x₁ t * montgomeryRemainder x₂ t * conj (zSide x₃ t) +
          primeSide x₁ t * primeSide x₂ t * conj (montgomeryRemainder x₃ t))) := by
    intro t
    rw [triple_S_eq hx₁ hx₂, ← primeSide_triple_eq hx₁.le hx₂.le]
    simp only [zSide, map_add]
    ring
  -- integrability on the window
  have hcZ₂ := continuousOn_zSide hx₂ T
  have hcZ₃ := continuousOn_zSide hx₃ T
  have hcE₁ := continuousOn_montgomeryRemainder hx₁ T
  have hcE₂ := continuousOn_montgomeryRemainder hx₂ T
  have hcE₃ := continuousOn_montgomeryRemainder hx₃ T
  have hcP₁ := (continuous_primeSide hx₁.le).continuousOn (s := Set.Icc 0 T)
  have hcP₂ := (continuous_primeSide hx₂.le).continuousOn (s := Set.Icc 0 T)
  have hcP₃ := (continuous_primeSide hx₃.le).continuousOn (s := Set.Icc 0 T)
  have huIcc : Set.uIcc 0 T = Set.Icc 0 T := Set.uIcc_of_le hT
  have hint : ∀ {f : ℝ → ℂ}, ContinuousOn f (Set.Icc 0 T) → IntervalIntegrable f volume 0 T :=
    fun hf => (huIcc ▸ hf).intervalIntegrable
  have hintR : ∀ {f : ℝ → ℝ}, ContinuousOn f (Set.Icc 0 T) → IntervalIntegrable f volume 0 T :=
    fun hf => (huIcc ▸ hf).intervalIntegrable
  have hcK : ContinuousOn (fun t => primeConjSum x₁ t * primeConjSum x₂ t *
      conj (primeConjSum x₃ t)) (Set.Icc 0 T) := by
    refine ((hcP₁.mul hcP₂).mul (Complex.continuous_conj.comp_continuousOn hcP₃)).congr ?_
    intro t _; exact (primeSide_triple_eq hx₁.le hx₂.le t).symm
  have hcR : ContinuousOn (fun t => montgomeryRemainder x₁ t * zSide x₂ t * conj (zSide x₃ t) +
      primeSide x₁ t * montgomeryRemainder x₂ t * conj (zSide x₃ t) +
      primeSide x₁ t * primeSide x₂ t * conj (montgomeryRemainder x₃ t)) (Set.Icc 0 T) :=
    (((hcE₁.mul hcZ₂).mul (Complex.continuous_conj.comp_continuousOn hcZ₃)).add
      ((hcP₁.mul hcE₂).mul (Complex.continuous_conj.comp_continuousOn hcZ₃))).add
      ((hcP₁.mul hcP₂).mul (Complex.continuous_conj.comp_continuousOn hcE₃))
  have hI : ∫ t in (0 : ℝ)..T, lorentzZeroSumAll x₁ t * lorentzZeroSumAll x₂ t *
      conj (lorentzZeroSumAll x₃ t) = -(1 / (8 * x₁ * x₂)) *
      ((∫ t in (0 : ℝ)..T, primeConjSum x₁ t * primeConjSum x₂ t * conj (primeConjSum x₃ t)) +
        ∫ t in (0 : ℝ)..T, (montgomeryRemainder x₁ t * zSide x₂ t * conj (zSide x₃ t) +
          primeSide x₁ t * montgomeryRemainder x₂ t * conj (zSide x₃ t) +
          primeSide x₁ t * primeSide x₂ t * conj (montgomeryRemainder x₃ t))) := by
    simp_rw [hdec]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hint hcK) (hint hcR)]
  -- the pointwise majorant of the remainder
  set M : ℝ := x₁ * (256 * x₂) * (256 * x₃) + x₂ * (261 * x₁) * (256 * x₃) +
    x₃ * (261 * x₁) * (261 * x₂)
  set g : ℝ → ℝ := fun t => 4 / (1 + t ^ 2) * (M * Λ ^ 2) + Λ / 2 * (‖zSide x₂ t‖ ^ 2 +
    ‖zSide x₃ t‖ ^ 2 / x₁ + ‖primeSide x₁ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₂ +
    ‖primeSide x₁ t‖ ^ 2 / x₁ + ‖primeSide x₂ t‖ ^ 2 / x₂)
  have hRle : ∀ t ∈ Set.Icc 0 T, ‖montgomeryRemainder x₁ t * zSide x₂ t * conj (zSide x₃ t) +
      primeSide x₁ t * montgomeryRemainder x₂ t * conj (zSide x₃ t) +
      primeSide x₁ t * primeSide x₂ t * conj (montgomeryRemainder x₃ t)‖ ≤ g t := by
    intro t ht
    have e₁ := norm_montgomeryRemainder_le_window hx₁ ht hΛE
    have e₂ := norm_montgomeryRemainder_le_window hx₂ ht hΛE
    have e₃ := norm_montgomeryRemainder_le_window hx₃ ht hΛE
    have hpol : ∀ x : ℝ, 4 * x / (1 + t ^ 2) + Λ / Real.sqrt x =
        4 / (1 + t ^ 2) * x + Λ * (1 / Real.sqrt x) := fun x => by ring
    rw [hpol] at e₁ e₂ e₃
    rw [hs₃] at e₃
    have hcombo := remainder_combo_le
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (by positivity : (0 : ℝ) ≤ 4 / (1 + t ^ 2)) (by linarith) (by linarith) (by linarith)
      e₁ e₂ e₃ (norm_zSide_le_window hx₂ ht hΛZ) (norm_zSide_le_window hx₃ ht hΛZ)
      (hP x₁ hx₁ t ht) (hP x₂ hx₂ t ht)
    calc ‖montgomeryRemainder x₁ t * zSide x₂ t * conj (zSide x₃ t) +
          primeSide x₁ t * montgomeryRemainder x₂ t * conj (zSide x₃ t) +
          primeSide x₁ t * primeSide x₂ t * conj (montgomeryRemainder x₃ t)‖
        ≤ ‖montgomeryRemainder x₁ t‖ * ‖zSide x₂ t‖ * ‖zSide x₃ t‖ +
          ‖primeSide x₁ t‖ * ‖montgomeryRemainder x₂ t‖ * ‖zSide x₃ t‖ +
          ‖primeSide x₁ t‖ * ‖primeSide x₂ t‖ * ‖montgomeryRemainder x₃ t‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
            (le_of_eq ?_) (le_of_eq ?_))) (le_of_eq ?_)) <;>
          simp only [norm_mul, RCLike.norm_conj]
      _ ≤ g t := by
          refine hcombo.trans (le_of_eq ?_)
          simp only [g, M]; ring

  -- integrate the majorant
  have hcpol : Continuous fun t : ℝ => 4 / (1 + t ^ 2) * (M * Λ ^ 2) :=
    (continuous_const.div (by fun_prop) fun t => by positivity).mul continuous_const
  have hcg : ContinuousOn g (Set.Icc 0 T) := by
    refine ContinuousOn.add hcpol.continuousOn (continuousOn_const.mul ?_)
    exact (((((hcZ₂.norm.pow 2).add ((hcZ₃.norm.pow 2).div_const _)).add (hcP₁.norm.pow 2)).add
      ((hcZ₃.norm.pow 2).div_const _)).add ((hcP₁.norm.pow 2).div_const _)).add
      ((hcP₂.norm.pow 2).div_const _)
  have hRint : ∫ t in (0 : ℝ)..T, ‖montgomeryRemainder x₁ t * zSide x₂ t * conj (zSide x₃ t) +
      primeSide x₁ t * montgomeryRemainder x₂ t * conj (zSide x₃ t) +
      primeSide x₁ t * primeSide x₂ t * conj (montgomeryRemainder x₃ t)‖ ≤ ∫ t in (0 : ℝ)..T, g t :=
    intervalIntegral.integral_mono_on hT (hintR hcR.norm) (hintR hcg) hRle
  have hg : ∫ t in (0 : ℝ)..T, g t ≤ 8 * Λ ^ 2 * M + Λ / 2 *
      ((∫ t in (0 : ℝ)..T, ‖zSide x₂ t‖ ^ 2) + (∫ t in (0 : ℝ)..T, ‖zSide x₃ t‖ ^ 2) / x₁ +
        (∫ t in (0 : ℝ)..T, ‖primeSide x₁ t‖ ^ 2) + (∫ t in (0 : ℝ)..T, ‖zSide x₃ t‖ ^ 2) / x₂ +
        (∫ t in (0 : ℝ)..T, ‖primeSide x₁ t‖ ^ 2) / x₁ +
        (∫ t in (0 : ℝ)..T, ‖primeSide x₂ t‖ ^ 2) / x₂) := by
    have i1 : IntervalIntegrable (fun t : ℝ => 4 / (1 + t ^ 2) * (M * Λ ^ 2)) volume 0 T :=
      hcpol.continuousOn.intervalIntegrable
    have iA := hintR (hcZ₂.norm.pow 2)
    have iB : IntervalIntegrable (fun t => ‖zSide x₃ t‖ ^ 2 / x₁) volume 0 T :=
      (hintR (hcZ₃.norm.pow 2)).div_const _
    have iC := hintR (hcP₁.norm.pow 2)
    have iD : IntervalIntegrable (fun t => ‖zSide x₃ t‖ ^ 2 / x₂) volume 0 T :=
      (hintR (hcZ₃.norm.pow 2)).div_const _
    have iE : IntervalIntegrable (fun t => ‖primeSide x₁ t‖ ^ 2 / x₁) volume 0 T :=
      (hintR (hcP₁.norm.pow 2)).div_const _
    have iF : IntervalIntegrable (fun t => ‖primeSide x₂ t‖ ^ 2 / x₂) volume 0 T :=
      (hintR (hcP₂.norm.pow 2)).div_const _
    have j2 : IntervalIntegrable (fun t => ‖zSide x₂ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₁) volume 0 T :=
      iA.add iB
    have j3 : IntervalIntegrable (fun t => ‖zSide x₂ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₁ +
        ‖primeSide x₁ t‖ ^ 2) volume 0 T := j2.add iC
    have j4 : IntervalIntegrable (fun t => ‖zSide x₂ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₁ +
        ‖primeSide x₁ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₂) volume 0 T := j3.add iD
    have j5 : IntervalIntegrable (fun t => ‖zSide x₂ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₁ +
        ‖primeSide x₁ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₂ + ‖primeSide x₁ t‖ ^ 2 / x₁) volume 0 T :=
      j4.add iE
    have j6 : IntervalIntegrable (fun t => ‖zSide x₂ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₁ +
        ‖primeSide x₁ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₂ + ‖primeSide x₁ t‖ ^ 2 / x₁ +
        ‖primeSide x₂ t‖ ^ 2 / x₂) volume 0 T := j5.add iF
    have j7 : IntervalIntegrable (fun t => Λ / 2 * (‖zSide x₂ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₁ +
        ‖primeSide x₁ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₂ + ‖primeSide x₁ t‖ ^ 2 / x₁ +
        ‖primeSide x₂ t‖ ^ 2 / x₂)) volume 0 T := j6.const_mul _
    have hpolar : ∫ t in (0 : ℝ)..T, 4 / (1 + t ^ 2) * (M * Λ ^ 2) ≤ 8 * (M * Λ ^ 2) := by
      rw [intervalIntegral.integral_mul_const, show (fun t : ℝ => 4 / (1 + t ^ 2)) =
        fun t => 4 * (1 / (1 + t ^ 2)) from funext fun t => by ring,
        intervalIntegral.integral_const_mul]
      have hM : 0 ≤ M * Λ ^ 2 := by positivity
      nlinarith [integral_inv_one_add_sq_le T]
    have s1 : ∫ t in (0 : ℝ)..T, (‖zSide x₂ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₁ +
        ‖primeSide x₁ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₂ + ‖primeSide x₁ t‖ ^ 2 / x₁ +
        ‖primeSide x₂ t‖ ^ 2 / x₂) =
        (∫ t in (0 : ℝ)..T, (‖zSide x₂ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₁ +
          ‖primeSide x₁ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₂ + ‖primeSide x₁ t‖ ^ 2 / x₁)) +
        ∫ t in (0 : ℝ)..T, ‖primeSide x₂ t‖ ^ 2 / x₂ := intervalIntegral.integral_add j5 iF
    have s2 : ∫ t in (0 : ℝ)..T, (‖zSide x₂ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₁ +
        ‖primeSide x₁ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₂ + ‖primeSide x₁ t‖ ^ 2 / x₁) =
        (∫ t in (0 : ℝ)..T, (‖zSide x₂ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₁ +
          ‖primeSide x₁ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₂)) +
        ∫ t in (0 : ℝ)..T, ‖primeSide x₁ t‖ ^ 2 / x₁ := intervalIntegral.integral_add j4 iE
    have s3 : ∫ t in (0 : ℝ)..T, (‖zSide x₂ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₁ +
        ‖primeSide x₁ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₂) =
        (∫ t in (0 : ℝ)..T, (‖zSide x₂ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₁ + ‖primeSide x₁ t‖ ^ 2)) +
        ∫ t in (0 : ℝ)..T, ‖zSide x₃ t‖ ^ 2 / x₂ := intervalIntegral.integral_add j3 iD
    have s4 : ∫ t in (0 : ℝ)..T, (‖zSide x₂ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₁ + ‖primeSide x₁ t‖ ^ 2) =
        (∫ t in (0 : ℝ)..T, (‖zSide x₂ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₁)) +
        ∫ t in (0 : ℝ)..T, ‖primeSide x₁ t‖ ^ 2 := intervalIntegral.integral_add j2 iC
    have s5 : ∫ t in (0 : ℝ)..T, (‖zSide x₂ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₁) =
        (∫ t in (0 : ℝ)..T, ‖zSide x₂ t‖ ^ 2) + ∫ t in (0 : ℝ)..T, ‖zSide x₃ t‖ ^ 2 / x₁ :=
      intervalIntegral.integral_add iA iB
    have s0 : ∫ t in (0 : ℝ)..T, g t = (∫ t in (0 : ℝ)..T, 4 / (1 + t ^ 2) * (M * Λ ^ 2)) +
        Λ / 2 * ∫ t in (0 : ℝ)..T, (‖zSide x₂ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₁ +
          ‖primeSide x₁ t‖ ^ 2 + ‖zSide x₃ t‖ ^ 2 / x₂ + ‖primeSide x₁ t‖ ^ 2 / x₁ +
          ‖primeSide x₂ t‖ ^ 2 / x₂) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_add i1 j7
    rw [s0, s1, s2, s3, s4, s5, intervalIntegral.integral_div, intervalIntegral.integral_div,
      intervalIntegral.integral_div, intervalIntegral.integral_div]
    nlinarith [hpolar]
  -- combine
  have hx12 : 0 < 8 * x₁ * x₂ := by positivity
  have hn : ‖(-(1 / (8 * (x₁ : ℂ) * (x₂ : ℂ))) : ℂ)‖ = 1 / (8 * x₁ * x₂) := by
    rw [show (8 * (x₁ : ℂ) * x₂) = ((8 * x₁ * x₂ : ℝ) : ℂ) by push_cast; ring, norm_neg,
      norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx12]
  rw [hI, norm_mul, hn, ← mul_assoc, mul_one_div_cancel hx12.ne', one_mul]
  calc ‖(∫ t in (0 : ℝ)..T, primeConjSum x₁ t * primeConjSum x₂ t * conj (primeConjSum x₃ t)) +
        ∫ t in (0 : ℝ)..T, (montgomeryRemainder x₁ t * zSide x₂ t * conj (zSide x₃ t) +
          primeSide x₁ t * montgomeryRemainder x₂ t * conj (zSide x₃ t) +
          primeSide x₁ t * primeSide x₂ t * conj (montgomeryRemainder x₃ t))‖
      ≤ ‖∫ t in (0 : ℝ)..T, primeConjSum x₁ t * primeConjSum x₂ t * conj (primeConjSum x₃ t)‖ +
        ∫ t in (0 : ℝ)..T, ‖montgomeryRemainder x₁ t * zSide x₂ t * conj (zSide x₃ t) +
          primeSide x₁ t * montgomeryRemainder x₂ t * conj (zSide x₃ t) +
          primeSide x₁ t * primeSide x₂ t * conj (montgomeryRemainder x₃ t)‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl
          (intervalIntegral.norm_integral_le_integral_norm hT))
    _ ≤ _ := by simp only [M] at hg; linarith

/-! ### Energies at `x = T^γ` -/

theorem integral_normSq_zSide_le {x : ℝ} (hx : 1 < x) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, ‖zSide x t‖ ^ 2 ≤ 2 * (∫ t in (0 : ℝ)..T, ‖primeSide x t‖ ^ 2) +
      2 * ∫ t in (0 : ℝ)..T, ‖montgomeryRemainder x t‖ ^ 2 := by
  have huIcc : Set.uIcc 0 T = Set.Icc 0 T := Set.uIcc_of_le hT
  have hP : IntervalIntegrable (fun t => ‖primeSide x t‖ ^ 2) volume 0 T :=
    ((continuous_primeSide hx.le).norm.pow 2).intervalIntegrable _ _
  have hE : IntervalIntegrable (fun t => ‖montgomeryRemainder x t‖ ^ 2) volume 0 T :=
    (huIcc ▸ ((continuousOn_montgomeryRemainder hx T).norm.pow 2)).intervalIntegrable
  have hZ : IntervalIntegrable (fun t => ‖zSide x t‖ ^ 2) volume 0 T :=
    (huIcc ▸ ((continuousOn_zSide hx T).norm.pow 2)).intervalIntegrable
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (hP.const_mul 2) (hE.const_mul 2)]
  refine intervalIntegral.integral_mono_on hT hZ ((hP.const_mul 2).add (hE.const_mul 2))
    fun t _ => ?_
  have h := norm_add_le (primeSide x t) (montgomeryRemainder x t)
  have h0 := norm_nonneg (primeSide x t + montgomeryRemainder x t)
  simp only [zSide]
  nlinarith [sq_nonneg (‖primeSide x t‖ - ‖montgomeryRemainder x t‖), norm_nonneg (primeSide x t),
    norm_nonneg (montgomeryRemainder x t)]

/-- Eventually, at `x = T^γ` (`0 < γ < 1`), with `ℓ = log T`:
`Σ n d_x² ≤ 3x²ℓ`, `∫_0^T ‖P‖² ≤ 3Txℓ`, `∫_0^T ‖Z‖² ≤ 7Txℓ`. -/
theorem eventually_energy_bounds {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∀ᶠ T : ℝ in atTop,
      ∑' n : ℕ, (n : ℝ) * primeAmp (T ^ γ) n ^ 2 ≤ 3 * (T ^ γ) ^ 2 * Real.log T ∧
      ∫ t in (0 : ℝ)..T, ‖primeSide (T ^ γ) t‖ ^ 2 ≤ 3 * T * T ^ γ * Real.log T ∧
      ∫ t in (0 : ℝ)..T, ‖zSide (T ^ γ) t‖ ^ 2 ≤ 7 * T * T ^ γ * Real.log T := by
  have hx := tendsto_rpow_atTop hγ0
  have hA := hx.eventually eventually_tsum_mul_primeAmp_sq_le
  have hB := hx.eventually (tendsto_tsum_primeAmp_sq_div.eventually
    (eventually_le_nhds (by norm_num : (1 : ℝ) < 2)))
  have hgt := hx.eventually (eventually_gt_atTop (1 : ℝ))
  -- `x/T → 0`, `ℓ/x² → 0`, `1/(Txℓ) → 0`
  have h1 : Tendsto (fun T : ℝ => T ^ γ / T) atTop (𝓝 0) := tendsto_rpow_div_self hγ1
  have h2 : Tendsto (fun T : ℝ => Real.log T ^ 1 / T ^ (2 * γ)) atTop (𝓝 0) :=
    tendsto_log_pow_div_rpow 1 (by linarith)
  have h3 : Tendsto (fun T : ℝ => Real.log T ^ 2 / T ^ (2 * γ)) atTop (𝓝 0) :=
    tendsto_log_pow_div_rpow 2 (by linarith)
  have e1 := h1.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 1000))
  have e2 := h3.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 1000))
  filter_upwards [hA, hB, hgt, e1, e2, eventually_log_bounds, eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop
      (xbBlockConstant + xiLineTwoLogDerivConstant + 16)] with T hA hB hgt e1 e2 hlb hT2 hlC
  obtain ⟨hl1, -, -, hl4⟩ := hlb
  set x := T ^ γ with hxdef
  have hT0 : 0 < T := by linarith
  have hx1 : 1 < x := hgt
  have hx0 : 0 < x := by linarith
  have hl : Real.log x ≤ Real.log T := by
    rw [hxdef, Real.log_rpow hT0]; nlinarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)]
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hxT : x ≤ T / 1000 := by
    have := e1; rw [div_le_iff₀ hT0] at this; linarith
  have hA' : ∑' n : ℕ, (n : ℝ) * primeAmp x n ^ 2 ≤ 3 * x ^ 2 * Real.log T := by
    refine hA.trans ?_
    have := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ 3 * x ^ 2)
    linarith
  have hB' : ∑' n : ℕ, primeAmp x n ^ 2 ≤ 2 * x * Real.log T := by
    rw [div_le_iff₀ (by positivity)] at hB
    nlinarith
  -- the prime side
  have hP := integral_normSq_primeSide_sub_le hx1.le hT0.le
  have hW' : ∫ t in (0 : ℝ)..T, ‖primeSide x t‖ ^ 2 ≤ 3 * T * x * Real.log T := by
    have h0 := (abs_le.mp hP).2
    have hx2 : 312 * x * (x * Real.log T) ≤ T * (x * Real.log T) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hTB := mul_le_mul_of_nonneg_left hB' hT0.le
    have hAA := mul_le_mul_of_nonneg_left hA' (by norm_num : (0 : ℝ) ≤ 104)
    nlinarith
  refine ⟨hA', hW', ?_⟩
  -- the remainder
  have hE := integral_normSq_montgomeryRemainder_le hx1 hT0.le
  have hCl : xbBlockConstant + Real.log (T + 4) ≤ 3 * Real.log T := by
    have := xiLineTwoLogDerivConstant_nonneg; linarith
  have hb0 := xbBlockConstant_nonneg
  have hsq : (xbBlockConstant + Real.log (T + 4)) ^ 2 ≤ 9 * Real.log T ^ 2 := by
    have h0 : 0 ≤ xbBlockConstant + Real.log (T + 4) :=
      add_nonneg hb0 (Real.log_nonneg (by linarith))
    nlinarith
  have hx4 : 1536 / x ^ 4 ≤ 1536 := div_le_self (by norm_num) (one_le_pow₀ hx1.le)
  have hlx2 : Real.log T ^ 2 ≤ x ^ 2 / 1000 := by
    have := e2
    rw [div_le_iff₀ (by positivity), show T ^ (2 * γ) = x ^ 2 by
      rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; ring_nf] at this
    linarith
  have hrem : 3 * T * (xbBlockConstant + Real.log (T + 4)) ^ 2 / x ≤ T * x * Real.log T / 10 := by
    rw [div_le_iff₀ hx0]
    have : 27 * T * Real.log T ^ 2 ≤ T * x ^ 2 * Real.log T / 10 := by
      have h1 := mul_le_mul_of_nonneg_left hlx2 (by positivity : (0 : ℝ) ≤ 27 * T)
      have h2 : 27 * T * (x ^ 2 / 1000) ≤ T * x ^ 2 * Real.log T / 10 := by
        nlinarith [mul_le_mul_of_nonneg_left hl1 (by positivity : (0 : ℝ) ≤ T * x ^ 2)]
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 3 * T)]
  have hsmall : 96 * x ^ 2 + 1536 ≤ T * x * Real.log T / 5 := by
    have : 96 * x ≤ T / 10 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right this hx0.le]
  have hZ := integral_normSq_zSide_le hx1 hT0.le
  have hpos : 0 ≤ T * x * Real.log T := by positivity
  linarith

/-! ### The limit -/

/-- The arithmetic of the final estimate. -/
theorem triple_final_le {I K x₁ x₂ T ℓ Λ A₁ A₂ A₃ W₂ W₃ V₁ V₂ c₀ c₁ : ℝ}
    (hx₁ : 1 ≤ x₁) (hx₂ : 1 ≤ x₂) (hT : 0 < T) (hℓ : 1 ≤ ℓ) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ 3 * ℓ)
    (hc₁ : 0 ≤ c₁) (hA₂0 : 0 ≤ A₂)
    (h1 : 8 * x₁ * x₂ * I ≤ K + 8 * Λ ^ 2 * (x₁ * (256 * x₂) * (256 * (x₁ * x₂)) +
      x₂ * (261 * x₁) * (256 * (x₁ * x₂)) + (x₁ * x₂) * (261 * x₁) * (261 * x₂)) +
      Λ / 2 * (W₂ + W₃ / x₁ + V₁ + W₃ / x₂ + V₁ / x₁ + V₂ / x₂))
    (h2 : K ≤ T * (x₁ * x₂) * c₀ + 208 * (2 * A₁ * A₂ + x₁ ^ 2 * x₂ ^ 2 * c₁ + A₃))
    (hA₁ : A₁ ≤ 3 * x₁ ^ 2 * ℓ) (hA₂ : A₂ ≤ 3 * x₂ ^ 2 * ℓ) (hA₃ : A₃ ≤ 3 * (x₁ * x₂) ^ 2 * ℓ)
    (hV₁ : V₁ ≤ 3 * T * x₁ * ℓ) (hV₂ : V₂ ≤ 3 * T * x₂ * ℓ) (hW₂ : W₂ ≤ 7 * T * x₂ * ℓ)
    (hW₃ : W₃ ≤ 7 * T * (x₁ * x₂) * ℓ) :
    I ≤ T * ℓ * (c₀ / (8 * ℓ) + (2000000 + 26 * c₁) * (x₁ * x₂ * ℓ / T) +
      4 * (ℓ / x₁ + ℓ / x₂)) := by
  have hx₁0 : 0 < x₁ := by linarith
  have hx₂0 : 0 < x₂ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hX0 : 0 ≤ x₁ ^ 2 * x₂ ^ 2 := by positivity
  have hℓℓ : ℓ ≤ ℓ ^ 2 := by nlinarith
  have hℓ1 : 1 ≤ ℓ ^ 2 := by nlinarith
  -- the prime-side triple
  have hAA : A₁ * A₂ ≤ 9 * (x₁ ^ 2 * x₂ ^ 2) * ℓ ^ 2 := by
    have h := mul_le_mul hA₁ hA₂ hA₂0 (by positivity)
    have e : 3 * x₁ ^ 2 * ℓ * (3 * x₂ ^ 2 * ℓ) = 9 * (x₁ ^ 2 * x₂ ^ 2) * ℓ ^ 2 := by ring
    rw [e] at h; exact h
  have hA₃' : A₃ ≤ 3 * (x₁ ^ 2 * x₂ ^ 2) * ℓ ^ 2 := by
    have e : 3 * (x₁ * x₂) ^ 2 * ℓ = 3 * (x₁ ^ 2 * x₂ ^ 2) * ℓ := by ring
    rw [e] at hA₃
    exact hA₃.trans (mul_le_mul_of_nonneg_left hℓℓ (by positivity))
  have hc₁X : x₁ ^ 2 * x₂ ^ 2 * c₁ ≤ x₁ ^ 2 * x₂ ^ 2 * (c₁ * ℓ ^ 2) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hc₁ hℓ1) hX0
  have hK : K ≤ T * (x₁ * x₂) * c₀ + 208 * (18 * (x₁ ^ 2 * x₂ ^ 2) * ℓ ^ 2 +
      x₁ ^ 2 * x₂ ^ 2 * (c₁ * ℓ ^ 2) + 3 * (x₁ ^ 2 * x₂ ^ 2) * ℓ ^ 2) := by
    linarith
  -- the polar part
  have hM : x₁ * (256 * x₂) * (256 * (x₁ * x₂)) + x₂ * (261 * x₁) * (256 * (x₁ * x₂)) +
      (x₁ * x₂) * (261 * x₁) * (261 * x₂) = 200473 * (x₁ ^ 2 * x₂ ^ 2) := by ring
  have hΛ2 : Λ ^ 2 ≤ 9 * ℓ ^ 2 := by nlinarith
  have hpol : 8 * Λ ^ 2 * (200473 * (x₁ ^ 2 * x₂ ^ 2)) ≤
      (8 * 200473 * (x₁ ^ 2 * x₂ ^ 2)) * (9 * ℓ ^ 2) := by
    rw [show 8 * Λ ^ 2 * (200473 * (x₁ ^ 2 * x₂ ^ 2)) = (8 * 200473 * (x₁ ^ 2 * x₂ ^ 2)) * Λ ^ 2
      by ring]
    exact mul_le_mul_of_nonneg_left hΛ2 (by positivity)
  -- the energies
  have q₁ : W₃ / x₁ ≤ 7 * T * x₂ * ℓ := by
    rw [div_le_iff₀ hx₁0, show 7 * T * x₂ * ℓ * x₁ = 7 * T * (x₁ * x₂) * ℓ by ring]; exact hW₃
  have q₂ : W₃ / x₂ ≤ 7 * T * x₁ * ℓ := by
    rw [div_le_iff₀ hx₂0, show 7 * T * x₁ * ℓ * x₂ = 7 * T * (x₁ * x₂) * ℓ by ring]; exact hW₃
  have q₃ : V₁ / x₁ ≤ 3 * T * ℓ := by
    rw [div_le_iff₀ hx₁0, show 3 * T * ℓ * x₁ = 3 * T * x₁ * ℓ by ring]; exact hV₁
  have q₄ : V₂ / x₂ ≤ 3 * T * ℓ := by
    rw [div_le_iff₀ hx₂0, show 3 * T * ℓ * x₂ = 3 * T * x₂ * ℓ by ring]; exact hV₂
  have hsum : W₂ + W₃ / x₁ + V₁ + W₃ / x₂ + V₁ / x₁ + V₂ / x₂ ≤
      7 * T * x₂ * ℓ + 7 * T * x₂ * ℓ + 3 * T * x₁ * ℓ + 7 * T * x₁ * ℓ + 3 * T * ℓ + 3 * T * ℓ := by
    linarith
  have hB : Λ / 2 * (W₂ + W₃ / x₁ + V₁ + W₃ / x₂ + V₁ / x₁ + V₂ / x₂) ≤
      3 * ℓ / 2 * (7 * T * x₂ * ℓ + 7 * T * x₂ * ℓ + 3 * T * x₁ * ℓ + 7 * T * x₁ * ℓ +
        3 * T * ℓ + 3 * T * ℓ) := by
    have hs0 : 0 ≤ 7 * T * x₂ * ℓ + 7 * T * x₂ * ℓ + 3 * T * x₁ * ℓ + 7 * T * x₁ * ℓ +
        3 * T * ℓ + 3 * T * ℓ := by positivity
    exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans
      (mul_le_mul_of_nonneg_right (by linarith) hs0)
  -- assemble
  rw [hM] at h1
  have hbig : 208 * (18 * (x₁ ^ 2 * x₂ ^ 2) * ℓ ^ 2 + x₁ ^ 2 * x₂ ^ 2 * (c₁ * ℓ ^ 2) +
      3 * (x₁ ^ 2 * x₂ ^ 2) * ℓ ^ 2) + (8 * 200473 * (x₁ ^ 2 * x₂ ^ 2)) * (9 * ℓ ^ 2) ≤
      8 * (2000000 + 26 * c₁) * (x₁ ^ 2 * x₂ ^ 2) * ℓ ^ 2 := by
    have h0 : 0 ≤ x₁ ^ 2 * x₂ ^ 2 * ℓ ^ 2 := by positivity
    have e1 : 208 * (18 * (x₁ ^ 2 * x₂ ^ 2) * ℓ ^ 2 + x₁ ^ 2 * x₂ ^ 2 * (c₁ * ℓ ^ 2) +
      3 * (x₁ ^ 2 * x₂ ^ 2) * ℓ ^ 2) + (8 * 200473 * (x₁ ^ 2 * x₂ ^ 2)) * (9 * ℓ ^ 2) =
      (14438424 + 208 * c₁) * (x₁ ^ 2 * x₂ ^ 2 * ℓ ^ 2) := by ring
    have e2 : 8 * (2000000 + 26 * c₁) * (x₁ ^ 2 * x₂ ^ 2) * ℓ ^ 2 =
      (16000000 + 208 * c₁) * (x₁ ^ 2 * x₂ ^ 2 * ℓ ^ 2) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (by linarith) h0
  have hT9 : 3 * ℓ / 2 * (7 * T * x₂ * ℓ + 7 * T * x₂ * ℓ + 3 * T * x₁ * ℓ + 7 * T * x₁ * ℓ +
      3 * T * ℓ + 3 * T * ℓ) ≤ 32 * T * ℓ ^ 2 * (x₂ + x₁) := by
    have h0 : 0 ≤ T * ℓ ^ 2 := by positivity
    have e1 : 3 * ℓ / 2 * (7 * T * x₂ * ℓ + 7 * T * x₂ * ℓ + 3 * T * x₁ * ℓ + 7 * T * x₁ * ℓ +
      3 * T * ℓ + 3 * T * ℓ) = (T * ℓ ^ 2) * (21 * x₂ + 15 * x₁ + 9) := by ring
    rw [e1, show 32 * T * ℓ ^ 2 * (x₂ + x₁) = (T * ℓ ^ 2) * (32 * (x₂ + x₁)) by ring]
    exact mul_le_mul_of_nonneg_left (by linarith) h0
  have hmain : 8 * x₁ * x₂ * I ≤ T * (x₁ * x₂) * c₀ +
      8 * (2000000 + 26 * c₁) * (x₁ ^ 2 * x₂ ^ 2) * ℓ ^ 2 + 32 * T * ℓ ^ 2 * (x₂ + x₁) := by
    linarith
  have e : T * (x₁ * x₂) * c₀ + 8 * (2000000 + 26 * c₁) * (x₁ ^ 2 * x₂ ^ 2) * ℓ ^ 2 +
      32 * T * ℓ ^ 2 * (x₂ + x₁) = 8 * x₁ * x₂ * (T * ℓ * (c₀ / (8 * ℓ) +
        (2000000 + 26 * c₁) * (x₁ * x₂ * ℓ / T) + 4 * (ℓ / x₁ + ℓ / x₂))) := by
    have p1 : 8 * x₁ * x₂ * (T * ℓ * (c₀ / (8 * ℓ))) = T * (x₁ * x₂) * c₀ := by
      field_simp
    have p2 : 8 * x₁ * x₂ * (T * ℓ * ((2000000 + 26 * c₁) * (x₁ * x₂ * ℓ / T))) =
        8 * (2000000 + 26 * c₁) * (x₁ ^ 2 * x₂ ^ 2) * ℓ ^ 2 := by
      field_simp
    have p3 : 8 * x₁ * x₂ * (T * ℓ * (4 * (ℓ / x₁ + ℓ / x₂))) = 32 * T * ℓ ^ 2 * (x₂ + x₁) := by
      field_simp; ring
    linear_combination -p1 - p2 - p3
  rw [e] at hmain
  exact le_of_mul_le_mul_left hmain (by positivity)

/-- **The 3-level form factor of the zeros of `ζ` vanishes below threshold.** Unconditionally,
with complex ordinates, for `α, β > 0` with `α + β < 1`,
`∫_0^T S(T^α, t) S(T^β, t) conj S(T^{α+β}, t) dt = o(T log T)`,
where `S(x, t) = Σ_ρ x^{ρ−1/2}/(1 + (t + i(ρ − 1/2))²)` is the Lorentzian zero sum of Montgomery's
method (its mean square is the pair form `~ (T/4) log x`). -/
theorem tendsto_tripleFormFactor {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β < 1) :
    Tendsto (fun T : ℝ => ‖∫ t in (0 : ℝ)..T, lorentzZeroSumAll (T ^ α) t *
        lorentzZeroSumAll (T ^ β) t * conj (lorentzZeroSumAll (T ^ (α + β)) t)‖ /
        (T * Real.log T)) atTop (𝓝 0) := by
  set c₀ := ∑' m : ℕ, vonMangoldt m * LL m / m
  set c₁ := ∑' m, ppWeight m
  have hc₁ : 0 ≤ c₁ := tsum_nonneg ppWeight_nonneg
  set C := xbBlockConstant + xiLineTwoLogDerivConstant + 16
  set ε : ℝ → ℝ := fun T => c₀ / (8 * Real.log T) +
    (2000000 + 26 * c₁) * (T ^ (α + β) * Real.log T / T) +
    4 * (Real.log T / T ^ α + Real.log T / T ^ β)
  have hε : Tendsto ε atTop (𝓝 0) := by
    have t1 : Tendsto (fun T => c₀ / (8 * Real.log T)) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.comp ((Real.tendsto_log_atTop).const_mul_atTop
        (by norm_num : (0 : ℝ) < 8))).const_mul c₀
      simpa [div_eq_mul_inv] using this
    have t2 : Tendsto (fun T : ℝ => T ^ (α + β) * Real.log T / T) atTop (𝓝 0) := by
      refine (tendsto_log_pow_div_rpow 1 (by linarith : (0 : ℝ) < 1 - (α + β))).congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      rw [pow_one, Real.rpow_sub hT, Real.rpow_one]; field_simp
    have t3 : Tendsto (fun T : ℝ => Real.log T / T ^ α) atTop (𝓝 0) := by
      simpa using tendsto_log_pow_div_rpow 1 hα
    have t4 : Tendsto (fun T : ℝ => Real.log T / T ^ β) atTop (𝓝 0) := by
      simpa using tendsto_log_pow_div_rpow 1 hβ
    have := (t1.add (t2.const_mul (2000000 + 26 * c₁))).add ((t3.add t4).const_mul 4)
    simpa [ε] using this
  refine squeeze_zero' ((eventually_ge_atTop (1 : ℝ)).mono fun T hT =>
    div_nonneg (norm_nonneg _) (mul_nonneg (by linarith) (Real.log_nonneg hT))) ?_ hε
  have hlC := Real.tendsto_log_atTop.eventually_ge_atTop C
  filter_upwards [eventually_energy_bounds hα (by linarith),
    eventually_energy_bounds hβ (by linarith), eventually_energy_bounds (by linarith : 0 < α + β) hαβ,
    eventually_log_bounds, eventually_gt_atTop (1 : ℝ), hlC] with T h₁ h₂ h₃ hlb hT1 hlC
  obtain ⟨hl1, -, -, hl4⟩ := hlb
  have hT0 : 0 < T := by linarith
  have hx₁ : 1 < T ^ α := Real.one_lt_rpow hT1 hα
  have hx₂ : 1 < T ^ β := Real.one_lt_rpow hT1 hβ
  have hx₃ : T ^ (α + β) = T ^ α * T ^ β := Real.rpow_add hT0 α β
  rw [hx₃] at h₃ ⊢
  set Λ := C + Real.log (T + 4)
  have hΛ : xbBlockConstant + xiLineTwoLogDerivConstant + 16 + Real.log (T + 4) ≤ Λ := le_rfl
  have hΛ0 : 0 ≤ Λ := by
    have := xbBlockConstant_nonneg; have := xiLineTwoLogDerivConstant_nonneg
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 4)
    simp only [Λ, C]; linarith
  have hΛ3 : Λ ≤ 3 * Real.log T := by simp only [Λ]; linarith
  have hA := norm_integral_triple_le hx₁ hx₂ hT0.le hΛ
  have hK := norm_integral_primeConjSum_triple_le hx₁.le hx₂.le hT0.le
  have hfin := triple_final_le hx₁.le hx₂.le hT0 hl1 hΛ0 hΛ3 hc₁
    (tsum_nonneg fun n => by positivity) hA hK
    h₁.1 h₂.1 h₃.1 h₁.2.1 h₂.2.1 h₂.2.2 h₃.2.2
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ _ := hfin
    _ = ε T * (T * Real.log T) := by simp only [ε, hx₃]; ring

end RHTower
