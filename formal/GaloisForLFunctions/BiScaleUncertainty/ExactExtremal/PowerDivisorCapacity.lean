import GaloisForLFunctions.RHTower.ThetaTailDivisorCapacity

/-!
# Multiplicity and double-exponential Fourier capacity

The divisor of `Ξ^k` contributes `k/π` to the leading disc-count coefficient.
A source bounded by `C exp(-a exp(b|x|))` has angular capacity `2/(πb)`.
Consequently a nonzero source whose transform contains that divisor satisfies `kb ≤ 2`.
For a full spectral square the necessary exponent is `b ≤ 1`.
-/

open MeasureTheory Set Filter Topology Complex Metric

namespace GaloisForLFunctions.BiScaleUncertainty.ExactExtremal

open _root_.RHTower

noncomputable section

/-- Raising Xi to a power multiplies its exact disc divisor mass. -/
theorem finsum_divisor_XiC_pow (k : ℕ) (c : ℂ) (r : ℝ) :
    (∑ᶠ z, MeromorphicOn.divisor (fun z => XiC z ^ k) (closedBall c r) z) =
      (k : ℤ) * ∑ᶠ z, MeromorphicOn.divisor XiC (closedBall c r) z := by
  have hA : AnalyticOnNhd ℂ XiC (closedBall c r) := fun z _ => XiC_differentiable.analyticAt z
  calc
    (∑ᶠ z, MeromorphicOn.divisor (fun z => XiC z ^ k) (closedBall c r) z) =
        ∑ᶠ z, (k : ℤ) * MeromorphicOn.divisor XiC (closedBall c r) z := by
      apply finsum_congr
      intro z
      rw [MeromorphicOn.divisor_fun_pow hA.meromorphicOn]
      change k • (MeromorphicOn.divisor XiC (closedBall c r) z) = _
      simp only [nsmul_eq_mul]
    _ = _ := by
      simpa only [smul_eq_mul, mul_comm] using
        (finsum_smul (R := ℤ) (M := ℤ)
          (fun z => MeromorphicOn.divisor XiC (closedBall c r) z) (k : ℤ)).symm

/-- Full divisor containment preserves the finite-height Xi mass with its multiplicity. -/
theorem mul_xiSymmetricMass_le_divisor {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hH0 : ∃ z, H z ≠ 0) (k : ℕ)
    (hdiv : ∀ z, analyticOrderAt (fun z => XiC z ^ k) z ≤ analyticOrderAt H z)
    (c : ℂ) {T r : ℝ} (hT : 0 ≤ T) (hTr : T + 3 / 2 + ‖c‖ ≤ r) :
    (k : ℝ) * (xiSymmetricMass T : ℝ) ≤
      ∑ᶠ z, (MeromorphicOn.divisor H (closedBall c r) z : ℝ) := by
  have hmass := xiSymmetricMass_le_finsum_divisor_XiC c hT hTr
  have hpow := finsum_divisor_le_of_order_le (f := fun z => XiC z ^ k)
    (XiC_differentiable.pow k) hH hH0 hdiv c r
  rw [finsum_divisor_XiC_pow] at hpow
  have hlow := (mul_le_mul_of_nonneg_left hmass (Int.natCast_nonneg k)).trans hpow
  rw [← cast_finsum_divisor]
  exact_mod_cast hlow

/-- Above the multiplicity capacity `kb = 2`, every source carrying `Ξ^k` is zero. -/
theorem ae_eq_zero_of_doubleExp_XiC_pow_divisor {u : ℝ → ℂ} {a b C : ℝ} {k : ℕ}
    (hu : AEStronglyMeasurable u) (ha : 0 < a) (hb : 0 < b) (hkb : 2 < (k : ℝ) * b)
    (hC : ∀ x, ‖u x‖ ≤ C * Real.exp (-a * Real.exp (b * |x|)))
    (hdiv : ∀ z, analyticOrderAt (fun z => XiC z ^ k) z ≤
      analyticOrderAt (sourceTransform u) z) :
    u =ᵐ[volume] 0 := by
  have hms := measurableMomentSource_of_doubleExp hu ha hb hC
  have hHd := hms.differentiable_sourceTransform
  have hint : Integrable u := (hms.moment 0).mono' hu
    (Eventually.of_forall fun x => by simp)
  by_cases hH : ∀ z, sourceTransform u z = 0
  · exact ae_eq_zero_of_sourceTransform_eq_zero hint hH
  exfalso
  push Not at hH
  obtain ⟨c, hc⟩ := hH
  have hk : (0 : ℝ) < k := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hπ := Real.pi_pos
  have hgap : 2 / (Real.pi * b) < (k : ℝ) / Real.pi := by
    rw [div_lt_div_iff₀ (by positivity) hπ]
    nlinarith [mul_pos hπ (sub_pos.mpr hkb)]
  let ε := ((k : ℝ) / Real.pi - 2 / (Real.pi * b)) / (2 * k)
  have hε : 0 < ε := div_pos (sub_pos.mpr hgap) (by positivity)
  have heq : (k : ℝ) * ε = ((k : ℝ) / Real.pi - 2 / (Real.pi * b)) / 2 := by
    dsimp only [ε]
    field_simp
  have hκ : 2 / (Real.pi * b) < (k : ℝ) * (1 / Real.pi - ε) := by
    have hsplit : (k : ℝ) * (1 / Real.pi - ε) = (k : ℝ) / Real.pi - k * ε := by ring
    rw [hsplit, heq]
    linarith
  obtain ⟨T₀, hT₀, hmass⟩ := exists_xiSymmetricMass_close ε hε
  refine false_of_capacity hu ha hb hC hc (κ := (k : ℝ) * (1 / Real.pi - ε))
    (K := 3 / 2 + ‖c‖) (T₀ := T₀) (by positivity) hκ (by linarith) ?_
  intro T hT
  have hlow : (1 / Real.pi - ε) * (T * Real.log T) ≤ (xiSymmetricMass T : ℝ) := by
    have := (abs_le.mp (hmass T hT)).1
    linarith
  have hcount := mul_xiSymmetricMass_le_divisor hHd ⟨c, hc⟩ k hdiv c
    (T := T) (r := T + (3 / 2 + ‖c‖)) (by linarith) (by linarith)
  calc
    (k : ℝ) * (1 / Real.pi - ε) * (T * Real.log T) =
        k * ((1 / Real.pi - ε) * (T * Real.log T)) := by ring
    _ ≤ k * (xiSymmetricMass T : ℝ) := mul_le_mul_of_nonneg_left hlow hk.le
    _ ≤ _ := hcount

/-- The nonzero full-divisor class has the multiplicity budget `kb ≤ 2`. -/
theorem mul_exponent_le_two {u : ℝ → ℂ} {a b C : ℝ} {k : ℕ}
    (hu : AEStronglyMeasurable u) (hne : ¬ u =ᵐ[volume] 0)
    (ha : 0 < a) (hb : 0 < b)
    (hC : ∀ x, ‖u x‖ ≤ C * Real.exp (-a * Real.exp (b * |x|)))
    (hdiv : ∀ z, analyticOrderAt (fun z => XiC z ^ k) z ≤
      analyticOrderAt (sourceTransform u) z) :
    (k : ℝ) * b ≤ 2 := by
  by_contra h
  exact hne (ae_eq_zero_of_doubleExp_XiC_pow_divisor hu ha hb (lt_of_not_ge h) hC hdiv)

end

end GaloisForLFunctions.BiScaleUncertainty.ExactExtremal

