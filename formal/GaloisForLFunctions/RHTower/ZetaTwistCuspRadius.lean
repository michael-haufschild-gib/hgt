import GaloisForLFunctions.RHTower.ZetaTwistShiftDecomposition
import GaloisForLFunctions.RHTower.ZetaCuspRadiusConstant

/-!
# The cusp radius law at a real shift

The Hurwitz-formula decomposition of the shifted standard twist leaves, after the
geometric factor `(2π)^{-k}` and the Gamma quotient, a bracket of two terms whose
moduli grow like `A^{-k}` and `B^{-k}`, with `A` and `B` the smallest exponents of
the two Hurwitz series at the shifts `α` and `-α`.

If the two rates differ the faster term dominates and the bracket grows exactly at
that rate.  If they agree the two Hurwitz values coincide and the bracket is a
quarter-turn periodic factor times a single Hurwitz value, and a periodic factor
is invisible to the root.  Either way the root growth of the bracket is
`1/min(A,B)`, so the growth functional of the factorially normalized shifted
twists is `1/(2π min(A,B))`: the cusp radius law at the real base point `α`, with
cusp gap `min(A,B)`.
-/

open Complex HurwitzZeta Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped ENNReal NNReal

namespace RHTower

section TwistTerms

/-- The normalized Hurwitz value along the shift lattice. -/
noncomputable def twistP (β : ℝ) (s₀ : ℂ) (k : ℕ) : ℂ :=
  ((twistFirst β : ℝ) : ℂ) ^ (1 - s₀ + (k : ℂ))
    * hurwitzZeta ((β : ℝ) : UnitAddCircle) (1 - s₀ + (k : ℂ))

theorem tendsto_twistP (β : ℝ) (s₀ : ℂ) :
    Tendsto (fun k : ℕ => twistP β s₀ k) atTop (𝓝 1) :=
  tendsto_normalizedTwist β (1 - s₀)

theorem tendsto_norm_twistP (β : ℝ) (s₀ : ℂ) :
    Tendsto (fun k : ℕ => ‖twistP β s₀ k‖) atTop (𝓝 1) := by
  simpa using (tendsto_twistP β s₀).norm

theorem exists_bound_norm_twistP (β : ℝ) (s₀ : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ‖twistP β s₀ k‖ ≤ C := by
  obtain ⟨C, hC⟩ := (tendsto_norm_twistP β s₀).bddAbove_range
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun k => ?_⟩
  exact le_trans (hC ⟨k, rfl⟩) (le_max_left _ _)

/-- The constant prefactor of one half of the bracket. -/
noncomputable def twistLead (β : ℝ) (ε s₀ : ℂ) : ℂ :=
  Complex.exp (ε * (Real.pi : ℂ) * Complex.I * (1 - s₀) / 2)
    * ((twistFirst β : ℝ) : ℂ) ^ (-(1 - s₀))

theorem twistFirst_ne_zero (β : ℝ) : ((twistFirst β : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (twistFirst_pos β).ne'

theorem twistLead_ne_zero (β : ℝ) (ε s₀ : ℂ) : twistLead β ε s₀ ≠ 0 := by
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (twistFirst_ne_zero β))

/-- One half of the bracket, with the cusp-gap geometric factor extracted. -/
noncomputable def twistTerm (α β : ℝ) (ε s₀ : ℂ) (k : ℕ) : ℂ :=
  twistLead β ε s₀
    * (ε * Complex.I * ((twistGap α / twistFirst β : ℝ) : ℂ)) ^ k
    * twistP β s₀ k

/-- **The extracted term is the original one up to the geometric factor.** -/
theorem twistTerm_eq (α β : ℝ) {ε : ℂ}
    (hε : Complex.exp (ε * (Real.pi : ℂ) * Complex.I / 2) = ε * Complex.I)
    (s₀ : ℂ) (k : ℕ) :
    twistTerm α β ε s₀ k
      = ((twistGap α : ℝ) : ℂ) ^ k
        * (Complex.exp (ε * (Real.pi : ℂ) * Complex.I * (1 - s₀ + (k : ℂ)) / 2)
            * hurwitzZeta ((β : ℝ) : UnitAddCircle) (1 - s₀ + (k : ℂ))) := by
  have hAC : ((twistFirst β : ℝ) : ℂ) ≠ 0 := twistFirst_ne_zero β
  have hratio : ((twistGap α / twistFirst β : ℝ) : ℂ)
      = ((twistGap α : ℝ) : ℂ) / ((twistFirst β : ℝ) : ℂ) := by push_cast; ring
  have hexp : Complex.exp (ε * (Real.pi : ℂ) * Complex.I * (1 - s₀) / 2)
      * (ε * Complex.I) ^ k
      = Complex.exp (ε * (Real.pi : ℂ) * Complex.I * (1 - s₀ + (k : ℂ)) / 2) := by
    rw [← hε, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    ring
  have hcancel : ((twistFirst β : ℝ) : ℂ) ^ (-(1 - s₀))
      * (((twistFirst β : ℝ) : ℂ) ^ (k : ℕ))⁻¹
      * ((twistFirst β : ℝ) : ℂ) ^ (1 - s₀ + (k : ℂ)) = 1 := by
    rw [← Complex.cpow_natCast ((twistFirst β : ℝ) : ℂ) k, ← Complex.cpow_neg,
      ← Complex.cpow_add _ _ hAC, ← Complex.cpow_add _ _ hAC,
      show -(1 - s₀) + -(k : ℂ) + (1 - s₀ + (k : ℂ)) = 0 from by ring,
      Complex.cpow_zero]
  rw [twistTerm, twistLead, twistP, hratio]
  have key : Complex.exp (ε * (Real.pi : ℂ) * Complex.I * (1 - s₀) / 2)
        * ((twistFirst β : ℝ) : ℂ) ^ (-(1 - s₀))
        * (ε * Complex.I * (((twistGap α : ℝ) : ℂ) / ((twistFirst β : ℝ) : ℂ))) ^ k
        * (((twistFirst β : ℝ) : ℂ) ^ (1 - s₀ + (k : ℂ))
            * hurwitzZeta ((β : ℝ) : UnitAddCircle) (1 - s₀ + (k : ℂ)))
      = (Complex.exp (ε * (Real.pi : ℂ) * Complex.I * (1 - s₀) / 2) * (ε * Complex.I) ^ k)
        * ((twistGap α : ℝ) : ℂ) ^ k
        * (((twistFirst β : ℝ) : ℂ) ^ (-(1 - s₀))
            * (((twistFirst β : ℝ) : ℂ) ^ (k : ℕ))⁻¹
            * ((twistFirst β : ℝ) : ℂ) ^ (1 - s₀ + (k : ℂ)))
        * hurwitzZeta ((β : ℝ) : UnitAddCircle) (1 - s₀ + (k : ℂ)) := by
    ring
  rw [key, hcancel, hexp]
  ring

theorem norm_twistTerm (α β : ℝ) {ε : ℂ} (hε1 : ‖ε‖ = 1) (s₀ : ℂ) (k : ℕ) :
    ‖twistTerm α β ε s₀ k‖
      = ‖twistLead β ε s₀‖ * (twistGap α / twistFirst β) ^ k * ‖twistP β s₀ k‖ := by
  have hnn : (0 : ℝ) ≤ twistGap α / twistFirst β :=
    div_nonneg (twistGap_pos α).le (twistFirst_pos β).le
  rw [twistTerm, norm_mul, norm_mul, norm_pow, norm_mul, norm_mul, hε1, Complex.norm_I,
    one_mul, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]

/-- If the shift realises the cusp gap its half of the bracket has constant
modulus in the limit. -/
theorem tendsto_norm_twistTerm_of_eq (α β : ℝ) {ε : ℂ} (hε1 : ‖ε‖ = 1) (s₀ : ℂ)
    (hβ : twistFirst β = twistGap α) :
    Tendsto (fun k : ℕ => ‖twistTerm α β ε s₀ k‖) atTop (𝓝 ‖twistLead β ε s₀‖) := by
  have hone : twistGap α / twistFirst β = 1 := by
    rw [hβ, div_self (twistGap_pos α).ne']
  have hlim := (tendsto_norm_twistP β s₀).const_mul ‖twistLead β ε s₀‖
  rw [mul_one] at hlim
  refine hlim.congr fun k => ?_
  rw [norm_twistTerm α β hε1 s₀ k, hone, one_pow, mul_one]

/-- If the shift does not realise the cusp gap its half of the bracket is
geometrically negligible. -/
theorem tendsto_norm_twistTerm_of_lt (α β : ℝ) {ε : ℂ} (hε1 : ‖ε‖ = 1) (s₀ : ℂ)
    (hβ : twistGap α < twistFirst β) :
    Tendsto (fun k : ℕ => ‖twistTerm α β ε s₀ k‖) atTop (𝓝 0) := by
  have hr0 : (0 : ℝ) ≤ twistGap α / twistFirst β :=
    div_nonneg (twistGap_pos α).le (twistFirst_pos β).le
  have hr1 : twistGap α / twistFirst β < 1 := by
    rw [div_lt_one (twistFirst_pos β)]
    exact hβ
  have hpow : Tendsto (fun k : ℕ => (twistGap α / twistFirst β) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hprod := (hpow.const_mul ‖twistLead β ε s₀‖).mul (tendsto_norm_twistP β s₀)
  rw [mul_zero, zero_mul] at hprod
  refine hprod.congr fun k => ?_
  rw [norm_twistTerm α β hε1 s₀ k]

end TwistTerms

section QuarterTurn

theorem exp_quarter_turn : Complex.exp ((Real.pi : ℂ) * Complex.I / 2) = Complex.I := by
  rw [Complex.exp_eq_exp_re_mul_sin_add_cos]
  simp

theorem exp_pos_quarter :
    Complex.exp ((1 : ℂ) * (Real.pi : ℂ) * Complex.I / 2) = (1 : ℂ) * Complex.I := by
  rw [one_mul, one_mul, exp_quarter_turn]

theorem exp_neg_quarter :
    Complex.exp ((-1 : ℂ) * (Real.pi : ℂ) * Complex.I / 2) = (-1 : ℂ) * Complex.I := by
  rw [show ((-1 : ℂ) * (Real.pi : ℂ) * Complex.I / 2)
      = -((Real.pi : ℂ) * Complex.I / 2) from by ring, Complex.exp_neg, exp_quarter_turn,
    Complex.inv_I]
  ring

end QuarterTurn

section Bracket

/-- The bracket of the Hurwitz-formula decomposition. -/
noncomputable def twistBracket (α : ℝ) (s₀ : ℂ) (k : ℕ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - s₀ + (k : ℂ)) / 2)
      * hurwitzZeta ((α : ℝ) : UnitAddCircle) (1 - s₀ + (k : ℂ))
    + Complex.exp (-(Real.pi : ℂ) * Complex.I * (1 - s₀ + (k : ℂ)) / 2)
      * hurwitzZeta (((-α : ℝ)) : UnitAddCircle) (1 - s₀ + (k : ℂ))

/-- The sum of the two extracted halves. -/
noncomputable def twistSum (α : ℝ) (s₀ : ℂ) (k : ℕ) : ℂ :=
  twistTerm α α 1 s₀ k + twistTerm α (-α) (-1) s₀ k

theorem twistBracket_eq (α : ℝ) (s₀ : ℂ) (k : ℕ) :
    twistBracket α s₀ k
      = (((twistGap α)⁻¹ : ℝ) : ℂ) ^ k * twistSum α s₀ k := by
  have hinv : (((twistGap α)⁻¹ : ℝ) : ℂ) * ((twistGap α : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (twistGap_pos α).ne', Complex.ofReal_one]
  rw [twistSum, twistTerm_eq α α exp_pos_quarter, twistTerm_eq α (-α) exp_neg_quarter,
    twistBracket,
    show ((1 : ℂ) * (Real.pi : ℂ) * Complex.I * (1 - s₀ + (k : ℂ)) / 2)
      = (Real.pi : ℂ) * Complex.I * (1 - s₀ + (k : ℂ)) / 2 from by ring,
    show ((-1 : ℂ) * (Real.pi : ℂ) * Complex.I * (1 - s₀ + (k : ℂ)) / 2)
      = -(Real.pi : ℂ) * Complex.I * (1 - s₀ + (k : ℂ)) / 2 from by ring]
  set X := Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - s₀ + (k : ℂ)) / 2)
      * hurwitzZeta ((α : ℝ) : UnitAddCircle) (1 - s₀ + (k : ℂ)) with hXdef
  set Y := Complex.exp (-(Real.pi : ℂ) * Complex.I * (1 - s₀ + (k : ℂ)) / 2)
      * hurwitzZeta (((-α : ℝ)) : UnitAddCircle) (1 - s₀ + (k : ℂ)) with hYdef
  set M := ((twistGap α : ℝ) : ℂ) with hMdef
  set N := (((twistGap α)⁻¹ : ℝ) : ℂ) with hNdef
  calc X + Y = (N * M) ^ k * (X + Y) := by rw [hinv, one_pow, one_mul]
    _ = N ^ k * (M ^ k * X + M ^ k * Y) := by ring

end Bracket

section Bounds

/-- The sum of the two halves is bounded. -/
theorem exists_bound_norm_twistSum (α : ℝ) (s₀ : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ‖twistSum α s₀ k‖ ≤ C := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := exists_bound_norm_twistP α s₀
  obtain ⟨C₂, hC₂pos, hC₂⟩ := exists_bound_norm_twistP (-α) s₀
  refine ⟨‖twistLead α 1 s₀‖ * C₁ + ‖twistLead (-α) (-1) s₀‖ * C₂ + 1, ?_, fun k => ?_⟩
  · have h1 : 0 ≤ ‖twistLead α 1 s₀‖ * C₁ := mul_nonneg (norm_nonneg _) hC₁pos.le
    have h2 : 0 ≤ ‖twistLead (-α) (-1) s₀‖ * C₂ := mul_nonneg (norm_nonneg _) hC₂pos.le
    linarith
  · have hr1 : (twistGap α / twistFirst α) ^ k ≤ 1 := by
      refine pow_le_one₀ (div_nonneg (twistGap_pos α).le (twistFirst_pos α).le) ?_
      rw [div_le_one (twistFirst_pos α)]
      exact min_le_left _ _
    have hr2 : (twistGap α / twistFirst (-α)) ^ k ≤ 1 := by
      refine pow_le_one₀ (div_nonneg (twistGap_pos α).le (twistFirst_pos (-α)).le) ?_
      rw [div_le_one (twistFirst_pos (-α))]
      exact min_le_right _ _
    have hb1 : ‖twistTerm α α 1 s₀ k‖ ≤ ‖twistLead α 1 s₀‖ * C₁ := by
      rw [norm_twistTerm α α norm_one s₀ k]
      have hnn : (0 : ℝ) ≤ ‖twistLead α 1 s₀‖ := norm_nonneg _
      have hpk : (0 : ℝ) ≤ ‖twistP α s₀ k‖ := norm_nonneg _
      have hmul := mul_le_mul hr1 (hC₁ k) hpk zero_le_one
      calc ‖twistLead α 1 s₀‖ * (twistGap α / twistFirst α) ^ k * ‖twistP α s₀ k‖
          = ‖twistLead α 1 s₀‖ * ((twistGap α / twistFirst α) ^ k * ‖twistP α s₀ k‖) := by
            ring
        _ ≤ ‖twistLead α 1 s₀‖ * (1 * C₁) := mul_le_mul_of_nonneg_left hmul hnn
        _ = ‖twistLead α 1 s₀‖ * C₁ := by ring
    have hb2 : ‖twistTerm α (-α) (-1) s₀ k‖ ≤ ‖twistLead (-α) (-1) s₀‖ * C₂ := by
      have hone : ‖(-1 : ℂ)‖ = 1 := by simp
      rw [norm_twistTerm α (-α) hone s₀ k]
      have hnn : (0 : ℝ) ≤ ‖twistLead (-α) (-1) s₀‖ := norm_nonneg _
      have hpk : (0 : ℝ) ≤ ‖twistP (-α) s₀ k‖ := norm_nonneg _
      have hmul := mul_le_mul hr2 (hC₂ k) hpk zero_le_one
      calc ‖twistLead (-α) (-1) s₀‖ * (twistGap α / twistFirst (-α)) ^ k
              * ‖twistP (-α) s₀ k‖
          = ‖twistLead (-α) (-1) s₀‖
              * ((twistGap α / twistFirst (-α)) ^ k * ‖twistP (-α) s₀ k‖) := by ring
        _ ≤ ‖twistLead (-α) (-1) s₀‖ * (1 * C₂) := mul_le_mul_of_nonneg_left hmul hnn
        _ = ‖twistLead (-α) (-1) s₀‖ * C₂ := by ring
    have := norm_add_le (twistTerm α α 1 s₀ k) (twistTerm α (-α) (-1) s₀ k)
    rw [twistSum]
    linarith

/-- If one of the two shifts strictly dominates, the sum is eventually bounded
below by half the dominant modulus. -/
theorem eventually_norm_add_ge {f g : ℕ → ℂ} {c : ℝ} (hc : 0 < c)
    (hf : Tendsto (fun k => ‖f k‖) atTop (𝓝 c))
    (hg : Tendsto (fun k => ‖g k‖) atTop (𝓝 0)) :
    ∀ᶠ k in atTop, c / 2 ≤ ‖f k + g k‖ := by
  filter_upwards [hf.eventually_const_lt (by linarith : (3 : ℝ) * c / 4 < c),
    hg.eventually_lt_const (by linarith : (0 : ℝ) < c / 4)] with k h1 h2
  have h3 : ‖f k‖ ≤ ‖f k + g k‖ + ‖g k‖ := by
    have hsub := norm_sub_le (f k + g k) (g k)
    simpa using hsub
  linarith

end Bounds

section Symmetric

/-- If the two Hurwitz exponents agree, the two shifts are the same point of the
circle. -/
theorem coe_neg_eq_of_twistFirst_eq {α : ℝ} (h : twistFirst α = twistFirst (-α)) :
    (((-α : ℝ)) : UnitAddCircle) = ((α : ℝ) : UnitAddCircle) := by
  by_cases h0 : Int.fract α = 0
  · have hn : Int.fract (-α) = 0 := Int.fract_neg_eq_zero.mpr h0
    rw [← coe_fract_unitAddCircle (-α), ← coe_fract_unitAddCircle α, h0, hn]
  · have hn0 : Int.fract (-α) ≠ 0 := fun hc => h0 (Int.fract_neg_eq_zero.mp hc)
    rw [twistFirst, twistFirst, if_neg h0, if_neg hn0] at h
    rw [← coe_fract_unitAddCircle (-α), ← coe_fract_unitAddCircle α, ← h]

theorem twistP_neg_eq {α : ℝ} (h : twistFirst α = twistFirst (-α)) (s₀ : ℂ) (k : ℕ) :
    twistP (-α) s₀ k = twistP α s₀ k := by
  rw [twistP, twistP, ← h, coe_neg_eq_of_twistFirst_eq h]

/-- The periodic factor appearing when the two exponents agree. -/
noncomputable def twistWave (α : ℝ) (s₀ : ℂ) (k : ℕ) : ℂ :=
  twistLead α 1 s₀ * Complex.I ^ k + twistLead (-α) (-1) s₀ * (-Complex.I) ^ k

theorem twistWave_periodic (α : ℝ) (s₀ : ℂ) (k : ℕ) :
    twistWave α s₀ (k + 4) = twistWave α s₀ k := by
  have h1 : (Complex.I) ^ (k + 4) = Complex.I ^ k := by
    rw [pow_add]
    norm_num [Complex.I_pow_four]
  have h2 : (-Complex.I) ^ (k + 4) = (-Complex.I) ^ k := by
    rw [pow_add]
    have : (-Complex.I) ^ 4 = 1 := by
      rw [show (-Complex.I) ^ 4 = (Complex.I) ^ 4 from by ring, Complex.I_pow_four]
    rw [this, mul_one]
  rw [twistWave, twistWave, h1, h2]

theorem exists_norm_twistWave_pos (α : ℝ) (s₀ : ℂ) :
    0 < ‖twistWave α s₀ 0‖ ∨ 0 < ‖twistWave α s₀ 1‖ := by
  by_contra hcon
  rw [not_or, not_lt, not_lt] at hcon
  obtain ⟨h0, h1⟩ := hcon
  have hz0 : twistWave α s₀ 0 = 0 := norm_le_zero_iff.mp h0
  have hz1 : twistWave α s₀ 1 = 0 := norm_le_zero_iff.mp h1
  rw [twistWave, pow_zero, pow_zero, mul_one, mul_one] at hz0
  rw [twistWave, pow_one, pow_one] at hz1
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hsub : twistLead α 1 s₀ * Complex.I - twistLead (-α) (-1) s₀ * Complex.I = 0 := by
    have : twistLead α 1 s₀ * Complex.I + twistLead (-α) (-1) s₀ * (-Complex.I) = 0 := hz1
    linear_combination this
  have hdiff : twistLead α 1 s₀ = twistLead (-α) (-1) s₀ := by
    have := sub_eq_zero.mp hsub
    exact mul_right_cancel₀ hI this
  rw [hdiff] at hz0
  have : twistLead (-α) (-1) s₀ = 0 := by linear_combination hz0 / 2
  exact twistLead_ne_zero (-α) (-1) s₀ this

theorem twistSum_eq_wave {α : ℝ} (h : twistFirst α = twistFirst (-α)) (s₀ : ℂ) (k : ℕ) :
    twistSum α s₀ k = twistP α s₀ k * twistWave α s₀ k := by
  have hgapα : twistGap α / twistFirst α = 1 := by
    rw [twistGap, ← h, min_self, div_self (twistFirst_pos α).ne']
  have hgapβ : twistGap α / twistFirst (-α) = 1 := by
    rw [twistGap, ← h, min_self, h, div_self (twistFirst_pos (-α)).ne']
  rw [twistSum, twistTerm, twistTerm, hgapα, hgapβ, twistP_neg_eq h s₀ k, twistWave]
  push_cast
  ring

end Symmetric

section RootGrowth

variable {s₀ : ℂ}

/-- **The root growth of the bracket sum is one.** -/
theorem limsup_norm_twistSum_eq_one (α : ℝ) (s₀ : ℂ) :
    limsup (fun k : ℕ => ‖twistSum α s₀ k‖ ^ (1 / (k : ℝ))) atTop = 1 := by
  obtain ⟨C, hCpos, hC⟩ := exists_bound_norm_twistSum α s₀
  have hnn : ∀ k : ℕ, (0 : ℝ) ≤ ‖twistSum α s₀ k‖ := fun k => norm_nonneg _
  have hone : ‖(-1 : ℂ)‖ = 1 := by simp
  have hlb : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ᶠ k in atTop, c₀ ≤ ‖twistSum α s₀ k‖ := by
    rcases lt_trichotomy (twistFirst α) (twistFirst (-α)) with hlt | heq | hgt
    · have hgap : twistGap α = twistFirst α := min_eq_left hlt.le
      have hd : Tendsto (fun k : ℕ => ‖twistTerm α α 1 s₀ k‖) atTop
          (𝓝 ‖twistLead α 1 s₀‖) :=
        tendsto_norm_twistTerm_of_eq α α norm_one s₀ hgap.symm
      have hs : Tendsto (fun k : ℕ => ‖twistTerm α (-α) (-1) s₀ k‖) atTop (𝓝 0) :=
        tendsto_norm_twistTerm_of_lt α (-α) hone s₀ (by rw [hgap]; exact hlt)
      have hpos : 0 < ‖twistLead α 1 s₀‖ :=
        norm_pos_iff.mpr (twistLead_ne_zero α 1 s₀)
      refine ⟨‖twistLead α 1 s₀‖ / 2, by linarith, ?_⟩
      exact (eventually_norm_add_ge hpos hd hs).frequently
    · refine ?_
      have hP : Tendsto (fun k : ℕ => ‖twistP α s₀ k‖) atTop (𝓝 1) :=
        tendsto_norm_twistP α s₀
      obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, 0 < ‖twistWave α s₀ k₀‖ := by
        rcases exists_norm_twistWave_pos α s₀ with h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
      refine ⟨‖twistWave α s₀ k₀‖ / 2, by linarith, ?_⟩
      have hfreq := GaloisForLFunctions.HTGeometry.frequently_le_of_periodic
        (f := fun k : ℕ => ‖twistWave α s₀ k‖) (p := 4) (by norm_num)
        (fun k => by rw [twistWave_periodic α s₀ k]) k₀
      have hev : ∀ᶠ k in atTop, (1 : ℝ) / 2 ≤ ‖twistP α s₀ k‖ := by
        filter_upwards [hP.eventually_const_lt (by norm_num : (1 : ℝ) / 2 < 1)] with k hk
        exact hk.le
      refine (hfreq.and_eventually hev).mono fun k hk => ?_
      obtain ⟨hw, hp⟩ := hk
      rw [twistSum_eq_wave heq s₀ k, norm_mul]
      have h1 : (0 : ℝ) ≤ ‖twistWave α s₀ k₀‖ := norm_nonneg _
      nlinarith
    · have hgap : twistGap α = twistFirst (-α) := min_eq_right hgt.le
      have hd : Tendsto (fun k : ℕ => ‖twistTerm α (-α) (-1) s₀ k‖) atTop
          (𝓝 ‖twistLead (-α) (-1) s₀‖) :=
        tendsto_norm_twistTerm_of_eq α (-α) hone s₀ hgap.symm
      have hs : Tendsto (fun k : ℕ => ‖twistTerm α α 1 s₀ k‖) atTop (𝓝 0) :=
        tendsto_norm_twistTerm_of_lt α α norm_one s₀ (by rw [hgap]; exact hgt)
      have hpos : 0 < ‖twistLead (-α) (-1) s₀‖ :=
        norm_pos_iff.mpr (twistLead_ne_zero (-α) (-1) s₀)
      refine ⟨‖twistLead (-α) (-1) s₀‖ / 2, by linarith, ?_⟩
      have := (eventually_norm_add_ge hpos hd hs).frequently
      refine this.mono fun k hk => ?_
      rw [twistSum, add_comm]
      exact hk
  obtain ⟨c₀, hc₀, hfreq⟩ := hlb
  exact GaloisForLFunctions.HTGeometry.limsup_rpow_inv_eq_one hCpos hc₀ hnn hC hfreq

/-- The remainder with the cusp-gap geometric factor extracted. -/
noncomputable def twistT (α : ℝ) (s₀ : ℂ) (k : ℕ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ (-(1 - s₀))
    * (Complex.Gamma (1 - s₀ + (k : ℂ)) / Complex.Gamma (1 + (k : ℂ)))
    * twistSum α s₀ k

theorem twistRemainder_eq (α : ℝ) (s₀ : ℂ) (k : ℕ) :
    twistRemainder α s₀ k = (((twistGap α)⁻¹ : ℝ) : ℂ) ^ k * twistT α s₀ k := by
  have hdef : twistRemainder α s₀ k
      = (2 * (Real.pi : ℂ)) ^ (-(1 - s₀))
        * (Complex.Gamma (1 - s₀ + (k : ℂ)) / Complex.Gamma (1 + (k : ℂ)))
        * twistBracket α s₀ k := rfl
  rw [hdef, twistBracket_eq, twistT]
  ring

/-- **The extracted remainder has growth functional one.** -/
theorem hadamardLimsup_twistT (α : ℝ) (hs : ∀ m : ℕ, s₀ ≠ (m : ℂ)) :
    hadamardLimsup (twistT α s₀) = 1 := by
  set Cst : ℝ := ‖(2 * (Real.pi : ℂ)) ^ (-(1 - s₀))‖ with hCst
  have hCpos : 0 < Cst := by
    rw [hCst, norm_pos_iff]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl two_pi_ne_zero)
  obtain ⟨C, hCpos', hC⟩ := exists_bound_norm_twistSum α s₀
  have hsplit : ∀ k : ℕ, ‖twistT α s₀ k‖
      = (Cst * ‖Complex.Gamma (1 - s₀ + (k : ℂ)) / Complex.Gamma (1 + (k : ℂ))‖)
        * ‖twistSum α s₀ k‖ := by
    intro k
    rw [twistT, norm_mul, norm_mul, hCst]
  have hconv : Tendsto (fun k : ℕ =>
      (Cst * ‖Complex.Gamma (1 - s₀ + (k : ℂ)) / Complex.Gamma (1 + (k : ℂ))‖)
        ^ (1 / (k : ℝ))) atTop (𝓝 1) := by
    have hprod := (tendsto_const_rpow_inv_nat hCpos).mul (tendsto_gammaQuotient hs)
    rw [one_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards with k
    rw [← Real.mul_rpow hCpos.le (norm_nonneg _)]
  have hnn : ∀ k : ℕ, (0 : ℝ) ≤ ‖twistSum α s₀ k‖ := fun k => norm_nonneg _
  have hbbdd : IsBoundedUnder (· ≤ ·) atTop
      (fun k : ℕ => ‖twistSum α s₀ k‖ ^ (1 / (k : ℝ))) :=
    GaloisForLFunctions.HTGeometry.isBoundedUnder_rpow_inv hCpos' hnn hC
  have hbnn : ∀ k : ℕ, 0 ≤ ‖twistSum α s₀ k‖ ^ (1 / (k : ℝ)) := fun k =>
    Real.rpow_nonneg (hnn k) _
  have hcongr : ∀ k : ℕ, ‖twistT α s₀ k‖ ^ (1 / (k : ℝ))
      = (Cst * ‖Complex.Gamma (1 - s₀ + (k : ℂ)) / Complex.Gamma (1 + (k : ℂ))‖)
          ^ (1 / (k : ℝ))
        * ‖twistSum α s₀ k‖ ^ (1 / (k : ℝ)) := by
    intro k
    rw [hsplit k, Real.mul_rpow (by positivity) (hnn k)]
  have hbdd : IsBoundedUnder (· ≤ ·) atTop
      (fun k : ℕ => ‖twistT α s₀ k‖ ^ (1 / (k : ℝ))) := by
    obtain ⟨B, hB⟩ := id hbbdd
    rw [Filter.eventually_map] at hB
    refine ⟨2 * max B 0, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [hconv.eventually_lt_const (by norm_num : (1 : ℝ) < 2), hB]
      with k h2 hBk
    rw [hcongr k]
    exact mul_le_mul h2.le (le_trans hBk (le_max_left _ _)) (hbnn k) (by norm_num)
  have hlim : limsup (fun k : ℕ => ‖twistT α s₀ k‖ ^ (1 / (k : ℝ))) atTop = 1 := by
    rw [limsup_congr (Filter.Eventually.of_forall hcongr)]
    exact GaloisForLFunctions.HTGeometry.limsup_mul_eq_one_of_tendsto_one hconv hbnn
      hbbdd (limsup_norm_twistSum_eq_one α s₀)
  exact GaloisForLFunctions.HTGeometry.hadamardLimsup_eq_one_of_limsup_eq_one hbdd hlim

end RootGrowth

section CuspLaw

variable {s₀ : ℂ}

/-- **The cusp radius law at a real shift.**  The factorially normalized shifted
standard twists of the zeta function grow exactly like `1/(2π Δ(α))`, where
`Δ(α)` is the cusp gap at `α`. -/
theorem hadamardLimsup_zetaTwistShift (α : ℝ) (hs : ∀ m : ℕ, s₀ ≠ (m : ℂ)) :
    hadamardLimsup (fun k : ℕ =>
        expZeta ((α : ℝ) : UnitAddCircle) (s₀ - (k : ℂ)) / (Nat.factorial k : ℂ))
      = ENNReal.ofReal (1 / (2 * Real.pi * twistGap α)) := by
  have hfun : (fun k : ℕ =>
      expZeta ((α : ℝ) : UnitAddCircle) (s₀ - (k : ℂ)) / (Nat.factorial k : ℂ))
      = fun k : ℕ => ((2 * (Real.pi : ℂ))⁻¹) ^ k * twistRemainder α s₀ k :=
    funext fun k => zetaTwist_decomposition α hs k
  have hrem : twistRemainder α s₀
      = fun k : ℕ => (((twistGap α)⁻¹ : ℝ) : ℂ) ^ k * twistT α s₀ k :=
    funext fun k => twistRemainder_eq α s₀ k
  rw [hfun, hadamardLimsup_geometric, hrem, hadamardLimsup_geometric,
    hadamardLimsup_twistT α hs, mul_one]
  have hnorm1 : ‖((2 * (Real.pi : ℂ))⁻¹)‖ = 1 / (2 * Real.pi) := by
    rw [norm_inv, one_div]
    congr 1
    simp [abs_of_pos Real.pi_pos]
  have hnorm2 : ‖((((twistGap α)⁻¹ : ℝ)) : ℂ)‖ = 1 / twistGap α := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (twistGap_pos α)),
      one_div]
  have hcoe1 : ((‖((2 * (Real.pi : ℂ))⁻¹)‖₊ : ℝ≥0∞))
      = ENNReal.ofReal ‖((2 * (Real.pi : ℂ))⁻¹)‖ := by
    rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
    rfl
  have hcoe2 : ((‖((((twistGap α)⁻¹ : ℝ)) : ℂ)‖₊ : ℝ≥0∞))
      = ENNReal.ofReal ‖((((twistGap α)⁻¹ : ℝ)) : ℂ)‖ := by
    rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
    rfl
  rw [hcoe1, hcoe2, hnorm1, hnorm2, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

end CuspLaw

end RHTower
