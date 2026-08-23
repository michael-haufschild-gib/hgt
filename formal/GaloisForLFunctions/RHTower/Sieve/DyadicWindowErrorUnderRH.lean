import GaloisForLFunctions.RHTower.Sieve.ChebyshevErrorPowerBound
import GaloisForLFunctions.RHTower.DyadicVonMangoldtSqrtAsymptotic

/-!
# The dyadic weighted prime window under the Riemann hypothesis

Abel summation writes the dyadic mass as two endpoint terms and one integral of `ψ`; replacing
`ψ(t)` by `t` in each produces the constant `2(√2 − 1)√X`, and every remainder is the Chebyshev
error divided by `√t`, hence `O(X^a)` for every positive `a` once RH supplies
`|ψ(t) − t| ≪ t^{1/2+a}`.
-/

namespace RHTower.Sieve

open Filter MeasureTheory Set ArithmeticFunction

noncomputable section

/-- The integral half of the Abel identity, with a power-law error. -/
theorem abs_integral_psiWeight_sub_le_power {X : ℝ} (hX : 1 ≤ X) {C a : ℝ} (hC : 0 ≤ C)
    (ha : 0 < a) (ha1 : a ≤ 1)
    (hpsi : ∀ t ∈ Ioc X (2 * X), |chebyshevPsiReal t - t| ≤ C * t ^ (1 / 2 + a)) :
    |(∫ t in Ioc X (2 * X), chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)))
        - (Real.sqrt (2 * X) - Real.sqrt X)| ≤ C * X ^ a := by
  have hX0 : (0 : ℝ) < X := by linarith
  have h2X : (0 : ℝ) < 2 * X := by linarith
  have hdiffint : IntegrableOn
      (fun t : ℝ => chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)) - 1 / (2 * Real.sqrt t))
      (Ioc X (2 * X)) volume := (integrableOn_psiWeight hX0).sub (integrableOn_sqrtWeight hX0)
  have hsplit : (∫ t in Ioc X (2 * X), chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)))
      - (Real.sqrt (2 * X) - Real.sqrt X)
      = ∫ t in Ioc X (2 * X),
          (chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)) - 1 / (2 * Real.sqrt t)) := by
    rw [integral_sub (integrableOn_psiWeight hX0) (integrableOn_sqrtWeight hX0),
      integral_sqrtWeight hX0]
  rw [hsplit, ← Real.norm_eq_abs]
  have hconstint : IntegrableOn (fun _ : ℝ => C * (2 * X) ^ a / (2 * X))
      (Ioc X (2 * X)) volume :=
    MeasureTheory.integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hmono : ‖∫ t in Ioc X (2 * X),
      (chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)) - 1 / (2 * Real.sqrt t))‖
      ≤ ∫ _t in Ioc X (2 * X), C * (2 * X) ^ a / (2 * X) := by
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    refine setIntegral_mono_on hdiffint.norm hconstint measurableSet_Ioc fun t ht => ?_
    have ht0 : (0 : ℝ) < t := lt_trans hX0 ht.1
    have hsq : Real.sqrt t = t ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow t
    have hsq0 : (0 : ℝ) < t ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos ht0 _
    have hval : chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)) - 1 / (2 * Real.sqrt t)
        = (chebyshevPsiReal t - t) * (1 / (2 * t * Real.sqrt t)) := by
      have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
      field_simp
    rw [Real.norm_eq_abs, hval, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * t * Real.sqrt t))]
    have hb := hpsi t ht
    have hstep : |chebyshevPsiReal t - t| * (1 / (2 * t * Real.sqrt t))
        ≤ (C * t ^ ((1 : ℝ) / 2 + a)) * (1 / (2 * t * Real.sqrt t)) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    refine hstep.trans ?_
    have hid : (C * t ^ ((1 : ℝ) / 2 + a)) * (1 / (2 * t * Real.sqrt t))
        = C * t ^ a / (2 * t) := by
      rw [Real.rpow_add ht0, hsq]
      field_simp
    rw [hid]
    have h1 : t ^ a ≤ (2 * X) ^ a := Real.rpow_le_rpow ht0.le ht.2 ha.le
    have hta : (0 : ℝ) ≤ t ^ a := Real.rpow_nonneg ht0.le a
    have h2a : (0 : ℝ) ≤ (2 * X) ^ a := Real.rpow_nonneg h2X.le a
    rw [div_le_div_iff₀ (by linarith) h2X]
    have hs1 : C * t ^ a * (2 * X) ≤ C * (2 * X) ^ a * (2 * X) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC) (by linarith)
    have hs2 : C * (2 * X) ^ a * (2 * X) ≤ C * (2 * X) ^ a * (2 * t) :=
      mul_le_mul_of_nonneg_left (by linarith [ht.1.le]) (mul_nonneg hC h2a)
    linarith
  rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 2 * X - X), smul_eq_mul] at hmono
  refine hmono.trans ?_
  have hpow : (2 * X) ^ a = 2 ^ a * X ^ a := Real.mul_rpow (by norm_num) hX0.le
  have h2le : (2 : ℝ) ^ a ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) ha1
    simpa using this
  have hXa : (0 : ℝ) ≤ X ^ a := Real.rpow_nonneg hX0.le a
  have hid : (2 * X - X) * (C * (2 * X) ^ a / (2 * X)) = C * (2 ^ a * X ^ a) / 2 := by
    rw [hpow]
    field_simp
    ring
  rw [hid, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  nlinarith [mul_le_mul_of_nonneg_left h2le (mul_nonneg hC hXa)]

/-- **The dyadic weighted prime mass under RH.**  For every `a > 0` the mass differs from
`2(√2 − 1)√X` by at most `C X^a`. -/
theorem exists_dyadicSqrtVonMangoldtMass_error_bound (hRH : RiemannHypothesis) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      |dyadicSqrtVonMangoldtMass X - 2 * (Real.sqrt 2 - 1) * Real.sqrt X| ≤ C * X ^ a := by
  obtain ⟨C, hC0, hC⟩ := exists_chebyshevPsiReal_error_power_bound hRH ha
  refine ⟨4 * C, by positivity, ?_⟩
  intro X hX
  have hX0 : (0 : ℝ) < X := by linarith
  have h2X : (0 : ℝ) < 2 * X := by linarith
  have h2X1 : (1 : ℝ) ≤ 2 * X := by linarith
  have hXa : (0 : ℝ) ≤ X ^ a := Real.rpow_nonneg hX0.le a
  have habel := dyadicSqrtVonMangoldtMass_abel hX0
  have hsqX : Real.sqrt X = X ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow X
  have hsq2X : Real.sqrt (2 * X) = (2 * X) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (2 * X)
  have hsqXpos : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.2 hX0
  have hsq2Xpos : (0 : ℝ) < Real.sqrt (2 * X) := Real.sqrt_pos.2 h2X
  -- the two endpoint terms
  have hend2 : |chebyshevPsiReal (2 * X) * invSqrt (2 * X) - Real.sqrt (2 * X)|
      ≤ 2 * C * X ^ a := by
    have hid : chebyshevPsiReal (2 * X) * invSqrt (2 * X) - Real.sqrt (2 * X)
        = (chebyshevPsiReal (2 * X) - 2 * X) * invSqrt (2 * X) := by
      rw [invSqrt]
      have hsq : Real.sqrt (2 * X) * Real.sqrt (2 * X) = 2 * X :=
        Real.mul_self_sqrt h2X.le
      field_simp
      linarith [hsq]
    rw [hid, abs_mul, invSqrt, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt (2*X))⁻¹)]
    have hb := hC (2 * X) h2X1
    have hstep : |chebyshevPsiReal (2 * X) - 2 * X| * (Real.sqrt (2 * X))⁻¹
        ≤ (C * (2 * X) ^ ((1:ℝ) / 2 + a)) * (Real.sqrt (2 * X))⁻¹ :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    refine hstep.trans ?_
    have hid2 : (C * (2 * X) ^ ((1:ℝ) / 2 + a)) * (Real.sqrt (2 * X))⁻¹ = C * (2 * X) ^ a := by
      rw [Real.rpow_add h2X, hsq2X]
      have : (0:ℝ) < (2 * X) ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos h2X _
      field_simp
    rw [hid2]
    have hpow : (2 * X) ^ a = 2 ^ a * X ^ a := Real.mul_rpow (by norm_num) hX0.le
    have h2le : (2 : ℝ) ^ a ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) ha1
      simpa using this
    rw [hpow]
    nlinarith [mul_le_mul_of_nonneg_left h2le (mul_nonneg hC0.le hXa)]
  have hend1 : |chebyshevPsiReal X * invSqrt X - Real.sqrt X| ≤ C * X ^ a := by
    have hid : chebyshevPsiReal X * invSqrt X - Real.sqrt X
        = (chebyshevPsiReal X - X) * invSqrt X := by
      rw [invSqrt]
      have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
      field_simp
      linarith [hsq]
    rw [hid, abs_mul, invSqrt, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt X)⁻¹)]
    have hb := hC X hX
    have hstep : |chebyshevPsiReal X - X| * (Real.sqrt X)⁻¹
        ≤ (C * X ^ ((1:ℝ) / 2 + a)) * (Real.sqrt X)⁻¹ :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    refine hstep.trans (le_of_eq ?_)
    rw [Real.rpow_add hX0, hsqX]
    have : (0:ℝ) < X ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hX0 _
    field_simp
  have hint : |(∫ t in Ioc X (2 * X), chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)))
        - (Real.sqrt (2 * X) - Real.sqrt X)| ≤ C * X ^ a := by
    refine abs_integral_psiWeight_sub_le_power hX hC0.le ha ha1 fun t ht => ?_
    exact hC t (le_trans hX ht.1.le)
  -- assemble
  have hmain : 2 * (Real.sqrt 2 - 1) * Real.sqrt X = 2 * (Real.sqrt (2 * X) - Real.sqrt X) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) X]
    ring
  rw [habel, hmain]
  have hdecomp : chebyshevPsiReal (2 * X) * invSqrt (2 * X) - chebyshevPsiReal X * invSqrt X
        + (∫ t in Ioc X (2 * X), chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)))
        - 2 * (Real.sqrt (2 * X) - Real.sqrt X)
      = (chebyshevPsiReal (2 * X) * invSqrt (2 * X) - Real.sqrt (2 * X))
        - (chebyshevPsiReal X * invSqrt X - Real.sqrt X)
        + ((∫ t in Ioc X (2 * X), chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)))
            - (Real.sqrt (2 * X) - Real.sqrt X)) := by ring
  rw [hdecomp]
  refine le_trans (abs_add_le _ _) ?_
  refine le_trans (add_le_add (abs_sub _ _) hint) ?_
  linarith [hend2, hend1, hint]

end

end RHTower.Sieve
