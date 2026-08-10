import GaloisForLFunctions.RHTower.DeningerMomentMajorant
import GaloisForLFunctions.RHTower.DeningerHigherMajorant
import GaloisForLFunctions.RHTower.DeningerHigherPreimageMass

/-!
# The weighted moments of the preimage are bounded by a single Meyer seminorm

Every constant in the `(11)` chain except one depends only on the order: the coefficient series
`∑_i |M(i)|(i^{-(r+1)} - (i+1)^{-(r+1)})/(r+1)` and the mass of the majorant
`min(u^{2r+2}, u^{-2})`.  The only source-dependent factor is the Meyer seminorm `q_{r+2,1}(h)`.

So `(11)` upgrades from a finiteness statement to the *linear* estimate

`∫_0^∞ x^r |f_h(x)| dx ≤ K_r · q_{r+2,1}(h)`,

which is exactly the continuity assertion `(13)`.

* `deningerBracket_le_invSq` : the order-`r` bracket at every order, including `r = 0`.
* `deningerCoefficientSum` : the order-`r` coefficient series.
* `deningerHigherMomentMass_le_seminorm` : the weighted moment against one seminorm.
* `deningerPreimageMoment_le_seminorm` : **`(13)`: the `L¹` estimate is a seminorm bound.**
-/

namespace RHTower

open MeasureTheory SchwartzMap ENNReal ArithmeticFunction

noncomputable section

/-! ## The coefficient series at every order -/

/-- **The order-`r` bracket is nonnegative and dominated by an inverse square**, at every order,
including `r = 0` where it is exactly `1/(i(i+1))`. -/
theorem deningerBracket_le_invSq {i : ℕ} (hi : 0 < i) (r : ℕ) :
    0 ≤ 1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1) ∧
      1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1) ≤ 1 / (i : ℝ) ^ 2 := by
  have hir : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hipos : (0 : ℝ) < (i : ℝ) := lt_of_lt_of_le zero_lt_one hir
  have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by linarith
  have hmono : (i : ℝ) ^ (r + 1) ≤ ((i : ℝ) + 1) ^ (r + 1) :=
    pow_le_pow_left₀ hipos.le (by linarith) _
  have hnn : 1 / ((i : ℝ) + 1) ^ (r + 1) ≤ 1 / (i : ℝ) ^ (r + 1) :=
    one_div_le_one_div_of_le (by positivity) hmono
  refine ⟨by linarith, ?_⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hsimp : 1 / (i : ℝ) ^ (0 + 1) - 1 / ((i : ℝ) + 1) ^ (0 + 1)
        = 1 / ((i : ℝ) * ((i : ℝ) + 1)) := by
      field_simp
      ring
    rw [hsimp]
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith
  · have hsq : (i : ℝ) ^ 2 ≤ (i : ℝ) ^ (r + 1) := pow_le_pow_right₀ hir (by omega)
    have hle : 1 / (i : ℝ) ^ (r + 1) ≤ 1 / (i : ℝ) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) hsq
    have hpos : 0 ≤ 1 / ((i : ℝ) + 1) ^ (r + 1) := by positivity
    linarith

/-- The order-`r` Abel coefficients, in the normalisation the mass bound produces. -/
def deningerCoefficientTerm (r i : ℕ) : ℝ :=
  |Sieve.mertensM i| * ((1 / ((r : ℝ) + 1)) *
    (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1)))

theorem deningerCoefficientTerm_nonneg (r i : ℕ) : 0 ≤ deningerCoefficientTerm r i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have hz : Sieve.mertensM 0 = 0 := by
      rw [Sieve.mertensM]
      simp
    rw [deningerCoefficientTerm, hz]
    simp
  · exact mul_nonneg (abs_nonneg _)
      (mul_nonneg (by positivity) (deningerBracket_le_invSq hi r).1)

theorem deningerCoefficientTerm_summable (r : ℕ) : Summable (deningerCoefficientTerm r) := by
  refine Summable.of_nonneg_of_le (deningerCoefficientTerm_nonneg r) (fun i => ?_)
    deningerMertensM_invSq_summable
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have hz : Sieve.mertensM 0 = 0 := by
      rw [Sieve.mertensM]
      simp
    rw [deningerCoefficientTerm, hz]
    simp
  · have hb := deningerBracket_le_invSq hi r
    have hrone : (1 : ℝ) / ((r : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      linarith
    have hstep : (1 / ((r : ℝ) + 1)) *
        (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1)) ≤ 1 / (i : ℝ) ^ 2 := by
      calc (1 / ((r : ℝ) + 1)) *
            (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1))
          ≤ 1 * (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1)) :=
            mul_le_mul_of_nonneg_right hrone hb.1
        _ = 1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1) := one_mul _
        _ ≤ 1 / (i : ℝ) ^ 2 := hb.2
    rw [deningerCoefficientTerm]
    calc |Sieve.mertensM i| * ((1 / ((r : ℝ) + 1)) *
          (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1)))
        ≤ |Sieve.mertensM i| * (1 / (i : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hstep (abs_nonneg _)
      _ = |Sieve.mertensM i| / (i : ℝ) ^ 2 := by rw [mul_one_div]

/-- The order-`r` coefficient series. -/
def deningerCoefficientSum (r : ℕ) : ℝ := ∑' i : ℕ, deningerCoefficientTerm r i

theorem deningerCoefficientSum_nonneg (r : ℕ) : 0 ≤ deningerCoefficientSum r :=
  tsum_nonneg fun i => deningerCoefficientTerm_nonneg r i

/-! ## The weighted moment against one seminorm -/

/-- **The weighted moment is bounded by one Meyer seminorm**, with a constant depending only on
the order. -/
theorem deningerHigherMomentMass_le_seminorm (r : ℕ) (h : DeningerExpSchwartz) :
    deningerHigherMomentMass (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) r
      ≤ ENNReal.ofReal
        (deningerMeyerSeminormFun ((r : ℝ) + 2) 1 h * deningerMomentMajorantMass r) := by
  set q : ℝ := deningerMeyerSeminormFun ((r : ℝ) + 2) 1 h with hq
  have hqnn : 0 ≤ q := deningerMeyerSeminormFun_nonneg _ _ _
  have hstep : (∫⁻ u in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (u ^ (r + 1) *
        ‖deningerLogPullDeriv (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) u‖))
      ≤ ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (q * deningerMomentMajorant r u) := by
    refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
    exact ENNReal.ofReal_le_ofReal
      (deningerLogPullDeriv_weightedPow_le_seminorm r h hu)
  have hmass : (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (q * deningerMomentMajorant r u))
      = ENNReal.ofReal (q * deningerMomentMajorantMass r) := by
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun u : ℝ => q * deningerMomentMajorant r u := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact mul_nonneg hqnn (deningerMomentMajorant_nonneg r hu)
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((deningerMomentMajorant_integrableOn r).const_mul q) hnn,
      integral_const_mul, deningerMomentMajorantMass]
  rw [deningerHigherMomentMass]
  exact le_trans hstep (le_of_eq hmass)

end

end RHTower

/-! ## The `L¹` estimate as a seminorm bound -/

namespace RHTower

open MeasureTheory SchwartzMap ENNReal ArithmeticFunction

noncomputable section

/-- The weighted mass of the preimage is the coefficient series times the weighted moment. -/
theorem deningerPreimageMomentMass_le (r : ℕ) (h : DeningerExpSchwartz) :
    (∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x ^ r) *
        ‖deningerMobiusPreimage (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) x‖ₑ)
      ≤ ENNReal.ofReal (deningerCoefficientSum r) *
        deningerHigherMomentMass (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) r := by
  set g : 𝓢(ℝ, ℂ) := ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) with hg
  have hstep0 : (∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x ^ r) *
      ‖deningerMobiusPreimage g x‖ₑ)
      ≤ ∫⁻ x in Set.Ioi (0 : ℝ), deningerHigherMajorant g r x := by
    refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
    exact deningerMobiusPreimage_higherEnorm_le h.2 r hx
  have hswap : (∫⁻ x in Set.Ioi (0 : ℝ), deningerHigherMajorant g r x)
      = ∑' i : ℕ, ENNReal.ofReal |Sieve.mertensM i| *
        ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x ^ r) *
          ‖deningerLogPull g (((i : ℝ) + 1) * x) - deningerLogPull g ((i : ℝ) * x)‖ₑ := by
    have hpt : ∀ x : ℝ, deningerHigherMajorant g r x
        = ∑' i : ℕ, ENNReal.ofReal |Sieve.mertensM i| *
          (ENNReal.ofReal (x ^ r) *
            ‖deningerLogPull g (((i : ℝ) + 1) * x) - deningerLogPull g ((i : ℝ) * x)‖ₑ) := by
      intro x
      rw [deningerHigherMajorant, deningerAbelMajorant, ← ENNReal.tsum_mul_left]
      exact tsum_congr fun i => by ring
    rw [lintegral_congr hpt,
      lintegral_tsum fun i =>
        ((deningerAbelDifferencePow_measurable g i r).const_mul _).aemeasurable]
    exact tsum_congr fun i => lintegral_const_mul' _ _ ofReal_ne_top
  have hterm : ∀ i : ℕ, ENNReal.ofReal |Sieve.mertensM i| *
      (∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x ^ r) *
        ‖deningerLogPull g (((i : ℝ) + 1) * x) - deningerLogPull g ((i : ℝ) * x)‖ₑ)
        ≤ ENNReal.ofReal (deningerCoefficientTerm r i) * deningerHigherMomentMass g r := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have hzero : Sieve.mertensM 0 = 0 := by
        rw [Sieve.mertensM]
        simp
      rw [hzero]
      simp
    · have hstep : ENNReal.ofReal |Sieve.mertensM i| *
          (∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x ^ r) *
            ‖deningerLogPull g (((i : ℝ) + 1) * x) - deningerLogPull g ((i : ℝ) * x)‖ₑ)
          ≤ ENNReal.ofReal |Sieve.mertensM i| *
            (ENNReal.ofReal ((1 / ((r : ℝ) + 1)) *
                (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1))) *
              deningerHigherMomentMass g r) := by
        rw [deningerHigherMomentMass]
        gcongr
        exact deningerAbelDifferencePow_mass_le g hi r
      refine le_trans hstep (le_of_eq ?_)
      rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), deningerCoefficientTerm]
  refine le_trans hstep0 ?_
  rw [hswap]
  refine le_trans (ENNReal.tsum_le_tsum hterm) (le_of_eq ?_)
  rw [ENNReal.tsum_mul_right, deningerCoefficientSum,
    ← ENNReal.ofReal_tsum_of_nonneg (deningerCoefficientTerm_nonneg r)
      (deningerCoefficientTerm_summable r)]

/-- **`(13)`: the `L¹` estimate of `(11)` is a bound by a single Meyer seminorm**, with a constant
depending only on the order.  This is the continuity of `h ↦ x^r f_h` into `L¹(0,∞)`. -/
theorem deningerPreimageMoment_le_seminorm (r : ℕ) (h : DeningerExpSchwartz) :
    (∫ x in Set.Ioi (0 : ℝ),
        ‖((x ^ r : ℝ) : ℂ) * deningerMobiusPreimage (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) x‖)
      ≤ (deningerCoefficientSum r * deningerMomentMajorantMass r) *
        deningerMeyerSeminormFun ((r : ℝ) + 2) 1 h := by
  set g : 𝓢(ℝ, ℂ) := ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) with hg
  set q : ℝ := deningerMeyerSeminormFun ((r : ℝ) + 2) 1 h with hq
  have hqnn : 0 ≤ q := deningerMeyerSeminormFun_nonneg _ _ _
  have hint := deningerMobiusPreimage_moment_integrable h.2 r
  have hnorm : (∫ x in Set.Ioi (0 : ℝ), ‖((x ^ r : ℝ) : ℂ) * deningerMobiusPreimage g x‖)
      = (∫⁻ x in Set.Ioi (0 : ℝ), ‖((x ^ r : ℝ) : ℂ) * deningerMobiusPreimage g x‖ₑ).toReal :=
    integral_norm_eq_lintegral_enorm hint.aestronglyMeasurable
  have hcongr : (∫⁻ x in Set.Ioi (0 : ℝ), ‖((x ^ r : ℝ) : ℂ) * deningerMobiusPreimage g x‖ₑ)
      = ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x ^ r) * ‖deningerMobiusPreimage g x‖ₑ := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    rw [enorm_mul, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hx0.le r)]
  have hbound : (∫⁻ x in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (x ^ r) * ‖deningerMobiusPreimage g x‖ₑ)
      ≤ ENNReal.ofReal ((deningerCoefficientSum r * deningerMomentMajorantMass r) * q) := by
    refine le_trans (deningerPreimageMomentMass_le r h) ?_
    refine le_trans (mul_le_mul_right (deningerHigherMomentMass_le_seminorm r h) _)
      (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (deningerCoefficientSum_nonneg r)]
    congr 1
    ring
  rw [hnorm, hcongr]
  refine ENNReal.toReal_le_of_le_ofReal ?_ hbound
  exact mul_nonneg (mul_nonneg (deningerCoefficientSum_nonneg r)
    (deningerMomentMajorantMass_nonneg r)) hqnn

end

end RHTower
