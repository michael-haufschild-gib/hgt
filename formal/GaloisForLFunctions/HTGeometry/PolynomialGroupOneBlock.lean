import GaloisForLFunctions.HTGeometry.PolynomialTransportRemainder

/-!
# The operator-valued polynomial-group one-block estimate

A transport family with slow exponent `p = 1/2 + σ` and polynomial degree `κ` carries three data:
the propagated lower endpoint, the resolvent boundary term left by the integrations by parts, and
the transported third remainder.  The first has majorant `x^{κ-p}`, the third splits at half the
frequency into `x^{κ-p}` and `x^{κ-2}`, and the second is square-integrable by Plancherel.  The two
exact squared-tail tests are `κ < σ` and `κ + 3/2 < 3`, and the block profile is square integrable
exactly when both hold.
-/

open MeasureTheory Set intervalIntegral
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem enn_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  rcases le_total a b with h | h
  · calc (a + b) ^ 2 ≤ (b + b) ^ 2 := by gcongr
      _ = 4 * b ^ 2 := by ring
      _ ≤ 4 * (a ^ 2 + b ^ 2) := by gcongr; exact le_add_self
  · calc (a + b) ^ 2 ≤ (a + a) ^ 2 := by gcongr
      _ = 4 * a ^ 2 := by ring
      _ ≤ 4 * (a ^ 2 + b ^ 2) := by gcongr; exact le_self_add

/-- The two-power majorant of a polynomially transported block profile. -/
def polynomialBlockMajorant (A A' κ p x : ℝ) : ℝ := A * x ^ (κ - p) + A' * x ^ (κ - 2)

theorem polynomialBlockMajorant_nonneg {A A' κ p x : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hx : 0 < x) : 0 ≤ polynomialBlockMajorant A A' κ p x := by
  rw [polynomialBlockMajorant]
  positivity

/-- **`(19)`--`(20)`: the two-power majorant is square integrable exactly in the stated window.** -/
theorem integrableOn_sq_polynomialBlockMajorant {A A' κ σ X₀ : ℝ} (hκσ : κ < σ) (hκ2 : κ < 3 / 2)
    (hX₀ : 0 < X₀) :
    IntegrableOn (fun x : ℝ => 2 * (A ^ 2 * x ^ (2 * (κ - (1 / 2 + σ)))
      + A' ^ 2 * x ^ (2 * (κ - 2)))) (Ioi X₀) := by
  have h1 : IntegrableOn (fun x : ℝ => x ^ (2 * (κ - (1 / 2 + σ)))) (Ioi X₀) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hX₀
  have h2 : IntegrableOn (fun x : ℝ => x ^ (2 * (κ - 2))) (Ioi X₀) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hX₀
  exact ((h1.const_mul (A ^ 2)).add (h2.const_mul (A' ^ 2))).const_mul 2

theorem lintegral_sq_ofReal_polynomialBlockMajorant_ne_top {A A' κ σ X₀ : ℝ}
    (hA : 0 ≤ A) (hA' : 0 ≤ A') (hκσ : κ < σ) (hκ2 : κ < 3 / 2) (hX₀ : 0 < X₀) :
    (∫⁻ x in Ioi X₀,
        ENNReal.ofReal (polynomialBlockMajorant A A' κ (1 / 2 + σ) x) ^ 2) ≠ ⊤ := by
  set h : ℝ → ℝ := fun x : ℝ => 2 * (A ^ 2 * x ^ (2 * (κ - (1 / 2 + σ)))
    + A' ^ 2 * x ^ (2 * (κ - 2))) with hhdef
  have hint : IntegrableOn h (Ioi X₀) := integrableOn_sq_polynomialBlockMajorant hκσ hκ2 hX₀
  have hnn : ∀ᵐ x ∂(volume.restrict (Ioi X₀)), 0 ≤ h x := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := X₀))] with x hx
    have hx0 : (0 : ℝ) < x := lt_trans hX₀ hx
    rw [hhdef]
    positivity
  have hfin : (∫⁻ x in Ioi X₀, ENNReal.ofReal (h x)) ≠ ⊤ := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn]
    exact ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top hfin ?_
  refine MeasureTheory.lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := X₀))] with x hx
  have hx0 : (0 : ℝ) < x := lt_trans hX₀ hx
  have hle : polynomialBlockMajorant A A' κ (1 / 2 + σ) x ^ 2 ≤ h x := by
    rw [polynomialBlockMajorant, hhdef]
    have e1 : (x ^ (κ - (1 / 2 + σ))) ^ 2 = x ^ (2 * (κ - (1 / 2 + σ))) := by
      rw [← Real.rpow_natCast (x ^ (κ - (1 / 2 + σ))) 2, ← Real.rpow_mul hx0.le]
      congr 1
      push_cast
      ring
    have e2 : (x ^ (κ - 2)) ^ 2 = x ^ (2 * (κ - 2)) := by
      rw [← Real.rpow_natCast (x ^ (κ - 2)) 2, ← Real.rpow_mul hx0.le]
      congr 1
      push_cast
      ring
    have hu : (0 : ℝ) ≤ A * x ^ (κ - (1 / 2 + σ)) := by positivity
    have hv : (0 : ℝ) ≤ A' * x ^ (κ - 2) := by positivity
    nlinarith [sq_nonneg (A * x ^ (κ - (1 / 2 + σ)) - A' * x ^ (κ - 2)), e1, e2, hu, hv]
  calc ENNReal.ofReal (polynomialBlockMajorant A A' κ (1 / 2 + σ) x) ^ 2
      = ENNReal.ofReal (polynomialBlockMajorant A A' κ (1 / 2 + σ) x ^ 2) := by
        rw [← ENNReal.ofReal_pow (polynomialBlockMajorant_nonneg
          (by positivity) (by positivity) hx0)]
    _ ≤ ENNReal.ofReal (h x) := ENNReal.ofReal_le_ofReal hle


variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- **`(15)`: the propagated lower endpoint carries the slow majorant.** -/
theorem norm_transport_lowerEndpoint_le {Φ : ℝ → ℝ → (X →L[ℂ] X)} {v : X} {κ σ K X₀ x : ℝ}
    (hκ : 0 ≤ κ) (hK : 0 ≤ K) (hX₀ : 1 ≤ X₀) (hx : 2 * X₀ ≤ x)
    (htrans : ‖Φ x X₀‖ ≤ K * ((X₀ / x) ^ (1 / 2 + σ) * (1 + x - X₀) ^ κ)) :
    ‖Φ x X₀ v‖ ≤ (K * ‖v‖ * X₀ ^ (1 / 2 + σ) * 2 ^ κ) * x ^ (κ - (1 / 2 + σ)) := by
  have hX0 : (0 : ℝ) < X₀ := lt_of_lt_of_le zero_lt_one hX₀
  have hx0 : (0 : ℝ) < x := by linarith
  have hx2 : (2 : ℝ) ≤ x := by linarith
  set p : ℝ := 1 / 2 + σ with hpdef
  have hdiv : (X₀ / x) ^ p = X₀ ^ p * x ^ (-p) := by
    rw [Real.div_rpow hX0.le hx0.le, Real.rpow_neg hx0.le, div_eq_mul_inv]
  have hpoly : (1 + x - X₀) ^ κ ≤ 2 ^ κ * x ^ κ := by
    refine le_trans (Real.rpow_le_rpow (by linarith) (by linarith : 1 + x - X₀ ≤ 2 * x) hκ) ?_
    exact le_of_eq (Real.mul_rpow (by norm_num) hx0.le)
  have hxp : x ^ (-p) * x ^ κ = x ^ (κ - p) := by
    rw [← Real.rpow_add hx0, show -p + κ = κ - p by ring]
  have hop : ‖Φ x X₀ v‖ ≤ ‖Φ x X₀‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
  have hXp : (0 : ℝ) < X₀ ^ p := Real.rpow_pos_of_pos hX0 _
  have hxpn : (0 : ℝ) < x ^ (-p) := Real.rpow_pos_of_pos hx0 _
  have hstep : ‖Φ x X₀‖ ≤ K * (X₀ ^ p * x ^ (-p) * (2 ^ κ * x ^ κ)) := by
    refine le_trans htrans ?_
    refine mul_le_mul_of_nonneg_left ?_ hK
    rw [hdiv]
    exact mul_le_mul_of_nonneg_left hpoly (by positivity)
  have hval : K * (X₀ ^ p * x ^ (-p) * (2 ^ κ * x ^ κ)) * ‖v‖
      = (K * ‖v‖ * X₀ ^ p * 2 ^ κ) * x ^ (κ - p) := by
    rw [← hxp]
    ring
  calc ‖Φ x X₀ v‖ ≤ ‖Φ x X₀‖ * ‖v‖ := hop
    _ ≤ K * (X₀ ^ p * x ^ (-p) * (2 ^ κ * x ^ κ)) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
    _ = (K * ‖v‖ * X₀ ^ p * 2 ^ κ) * x ^ (κ - p) := hval

set_option maxHeartbeats 1000000 in
/-- **`(14)`--`(18)`: the transported third remainder carries the two-power majorant.** -/
theorem norm_transport_remainder_le {Φ : ℝ → ℝ → (X →L[ℂ] X)} {r : ℝ → X} {κ σ K K' X₀ x : ℝ}
    (hκ : 0 ≤ κ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (hX₀ : 1 ≤ X₀) (hx : 2 * X₀ ≤ x)
    (htrans : ∀ t : ℝ, X₀ ≤ t → t ≤ x → ‖Φ x t‖ ≤ K * ((t / x) ^ (1 / 2 + σ) * (1 + x - t) ^ κ))
    (hr : ∀ t : ℝ, X₀ ≤ t → ‖r t‖ ≤ K' * t ^ (-(3 : ℝ)))
    (hrint : IntervalIntegrable (fun t => Φ x t (r t)) volume X₀ x) :
    ‖∫ t in X₀..x, Φ x t (r t)‖
      ≤ (K * K' * (2 * 2 ^ κ)) * x ^ (κ - (1 / 2 + σ)) + (K * K' * 4) * x ^ (κ - 2) := by
  have hX0 : (0 : ℝ) < X₀ := lt_of_lt_of_le zero_lt_one hX₀
  have hx0 : (0 : ℝ) < x := by linarith
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hXx : X₀ ≤ x := by linarith
  set p : ℝ := 1 / 2 + σ with hpdef
  have hp0 : (0 : ℝ) < p := by rw [hpdef]; linarith
  have hp32 : p ≤ 3 / 2 := by rw [hpdef]; linarith
  have hpt : ∀ t ∈ Icc X₀ x,
      ‖Φ x t (r t)‖ ≤ K * K' * polynomialTransportIntegrand p κ x t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hX0 ht.1
    have h1 : ‖Φ x t (r t)‖ ≤ ‖Φ x t‖ * ‖r t‖ := ContinuousLinearMap.le_opNorm _ _
    have h2 : ‖Φ x t‖ * ‖r t‖
        ≤ (K * ((t / x) ^ p * (1 + x - t) ^ κ)) * (K' * t ^ (-(3 : ℝ))) := by
      refine mul_le_mul (htrans t ht.1 ht.2) (hr t ht.1) (norm_nonneg _) ?_
      have : (0 : ℝ) ≤ (t / x) ^ p * (1 + x - t) ^ κ := by
        refine mul_nonneg (Real.rpow_nonneg (by positivity) _)
          (Real.rpow_nonneg (by linarith [ht.2]) _)
      positivity
    refine le_trans h1 (le_trans h2 (le_of_eq ?_))
    rw [polynomialTransportIntegrand]
    ring
  have hmajint : IntervalIntegrable
      (fun t : ℝ => K * K' * polynomialTransportIntegrand p κ x t) volume X₀ x :=
    (intervalIntegrable_polynomialTransportIntegrand hκ hX0 hXx hx0).const_mul _
  have hstep : ‖∫ t in X₀..x, Φ x t (r t)‖
      ≤ ∫ t in X₀..x, K * K' * polynomialTransportIntegrand p κ x t := by
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm hXx) ?_
    exact intervalIntegral.integral_mono_on hXx hrint.norm hmajint hpt
  refine le_trans hstep ?_
  rw [intervalIntegral.integral_const_mul]
  have hbase := integral_polynomialTransportIntegrand_le (p := p) (κ := κ) (X₀ := X₀) (x := x)
    hp0 hp32 hκ hX₀ hx hx2
  have hKK : (0 : ℝ) ≤ K * K' := mul_nonneg hK hK'
  nlinarith [hbase, hKK]

set_option maxHeartbeats 1000000 in
/-- **`(21)`: the polynomial-group one-block estimate.**  A block profile assembled from the
propagated lower endpoint, a Plancherel boundary term, and the transported third remainder is
square integrable on the ray, exactly under the two tail tests `κ < σ` and `κ + 3/2 < 3`. -/
theorem lintegral_sq_polynomialTransportProfile_ne_top
    {Φ : ℝ → ℝ → (X →L[ℂ] X)} {f B r : ℝ → X} {v : X} {κ σ K K' X₀ : ℝ}
    (hκ0 : 0 ≤ κ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hκσ : κ < σ)
    (hX₀ : 1 ≤ X₀) (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (htrans : ∀ x t : ℝ, X₀ ≤ t → t ≤ x →
      ‖Φ x t‖ ≤ K * ((t / x) ^ (1 / 2 + σ) * (1 + x - t) ^ κ))
    (hr : ∀ t : ℝ, X₀ ≤ t → ‖r t‖ ≤ K' * t ^ (-(3 : ℝ)))
    (hrint : ∀ x : ℝ, X₀ ≤ x → IntervalIntegrable (fun t => Φ x t (r t)) volume X₀ x)
    (hB : (∫⁻ x in Ioi (2 * X₀), ‖B x‖ₑ ^ 2) ≠ ⊤)
    (hf : ∀ x : ℝ, 2 * X₀ ≤ x → f x = Φ x X₀ v + B x + ∫ t in X₀..x, Φ x t (r t)) :
    (∫⁻ x in Ioi (2 * X₀), ‖f x‖ₑ ^ 2) ≠ ⊤ := by
  have hX0 : (0 : ℝ) < X₀ := lt_of_lt_of_le zero_lt_one hX₀
  set p : ℝ := 1 / 2 + σ with hpdef
  set A : ℝ := K * ‖v‖ * X₀ ^ p * 2 ^ κ + K * K' * (2 * 2 ^ κ) with hAdef
  set A' : ℝ := K * K' * 4 with hA'def
  have hA : (0 : ℝ) ≤ A := by
    rw [hAdef]
    have h1 : (0 : ℝ) ≤ K * ‖v‖ * X₀ ^ p * 2 ^ κ := by positivity
    have h2 : (0 : ℝ) ≤ K * K' * (2 * 2 ^ κ) := by positivity
    linarith
  have hA' : (0 : ℝ) ≤ A' := by rw [hA'def]; positivity
  have hpoint : ∀ x : ℝ, 2 * X₀ ≤ x →
      ‖f x‖ₑ ≤ ENNReal.ofReal (polynomialBlockMajorant A A' κ p x) + ‖B x‖ₑ := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have h1 := norm_transport_lowerEndpoint_le (Φ := Φ) (v := v) (κ := κ) (σ := σ)
      hκ0 hK hX₀ hx (htrans x X₀ le_rfl (by linarith))
    have h2 := norm_transport_remainder_le (Φ := Φ) (r := r) hκ0 hσ0 hσ1 hK hK' hX₀ hx
      (fun t ht1 ht2 => htrans x t ht1 ht2) hr (hrint x (by linarith))
    have hnorm : ‖f x‖ ≤ polynomialBlockMajorant A A' κ p x + ‖B x‖ := by
      rw [hf x hx, polynomialBlockMajorant, hAdef, hA'def]
      calc ‖Φ x X₀ v + B x + ∫ t in X₀..x, Φ x t (r t)‖
          ≤ ‖Φ x X₀ v + B x‖ + ‖∫ t in X₀..x, Φ x t (r t)‖ := norm_add_le _ _
        _ ≤ ‖Φ x X₀ v‖ + ‖B x‖ + ‖∫ t in X₀..x, Φ x t (r t)‖ := by
            gcongr
            exact norm_add_le _ _
        _ ≤ (K * ‖v‖ * X₀ ^ p * 2 ^ κ) * x ^ (κ - p) + ‖B x‖
              + ((K * K' * (2 * 2 ^ κ)) * x ^ (κ - p) + (K * K' * 4) * x ^ (κ - 2)) := by
            exact add_le_add (add_le_add h1 le_rfl) h2
        _ = (K * ‖v‖ * X₀ ^ p * 2 ^ κ + K * K' * (2 * 2 ^ κ)) * x ^ (κ - p)
              + K * K' * 4 * x ^ (κ - 2) + ‖B x‖ := by ring
    calc ‖f x‖ₑ = ENNReal.ofReal ‖f x‖ := by rw [ofReal_norm]
      _ ≤ ENNReal.ofReal (polynomialBlockMajorant A A' κ p x + ‖B x‖) :=
          ENNReal.ofReal_le_ofReal hnorm
      _ = ENNReal.ofReal (polynomialBlockMajorant A A' κ p x) + ENNReal.ofReal ‖B x‖ :=
          ENNReal.ofReal_add (polynomialBlockMajorant_nonneg hA hA' hx0) (norm_nonneg _)
      _ = ENNReal.ofReal (polynomialBlockMajorant A A' κ p x) + ‖B x‖ₑ := by
          rw [ofReal_norm]
  have hmaj : (∫⁻ x in Ioi (2 * X₀),
      ENNReal.ofReal (polynomialBlockMajorant A A' κ p x) ^ 2) ≠ ⊤ :=
    lintegral_sq_ofReal_polynomialBlockMajorant_ne_top hA hA' hκσ (by linarith) (by linarith)
  have hsum : (∫⁻ x in Ioi (2 * X₀),
      (ENNReal.ofReal (polynomialBlockMajorant A A' κ p x) + ‖B x‖ₑ) ^ 2) ≠ ⊤ := by
    have hle : (∫⁻ x in Ioi (2 * X₀),
        (ENNReal.ofReal (polynomialBlockMajorant A A' κ p x) + ‖B x‖ₑ) ^ 2)
        ≤ 4 * ((∫⁻ x in Ioi (2 * X₀), ENNReal.ofReal (polynomialBlockMajorant A A' κ p x) ^ 2)
          + ∫⁻ x in Ioi (2 * X₀), ‖B x‖ₑ ^ 2) := by
      have hmeas : AEMeasurable
          (fun x : ℝ => ENNReal.ofReal (polynomialBlockMajorant A A' κ p x) ^ 2)
          (volume.restrict (Ioi (2 * X₀))) := by
        refine Measurable.aemeasurable ?_
        refine Measurable.pow_const ?_ 2
        refine ENNReal.measurable_ofReal.comp ?_
        unfold polynomialBlockMajorant
        fun_prop
      rw [← MeasureTheory.lintegral_add_left' hmeas,
        ← MeasureTheory.lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
      refine MeasureTheory.lintegral_mono fun x => ?_
      exact enn_add_sq_le _ _
    refine ne_top_of_le_ne_top ?_ hle
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.mpr ⟨hmaj, hB⟩)
  refine ne_top_of_le_ne_top hsum ?_
  refine MeasureTheory.lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := 2 * X₀))] with x hx
  exact pow_le_pow_left' (hpoint x (le_of_lt hx)) 2

end GaloisForLFunctions.HTGeometry
