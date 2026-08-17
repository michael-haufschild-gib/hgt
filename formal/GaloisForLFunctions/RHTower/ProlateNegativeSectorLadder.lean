import GaloisForLFunctions.RHTower.ProlateSignedLadderEnvelope
import GaloisForLFunctions.RHTower.ConstrainedProlateParityExactTransfer

/-!
# The negative Fourier-parity sector of the constrained prolate ladder

The even prolate index splits into two sublattices: `2j`, whose Hermite limits are the modes
`h_{4j}`, and `2j+1`, whose Hermite limits are `h_{4j+2}`.  The first is the positive Fourier sector
of the constrained problem, the second the negative one.

Everything the positive sector consumed is index-generic.  The coordinate limit holds at an
arbitrary even prolate index with the Hermite shape ratio of the doubled index as its value, and the
shape ratio of `h_{2k}` is `2 sqrt(pi) · binom(2k,k)/4^k` in closed form.  On the negative
sublattice `k = 2j+1`, and the first two values are exactly the CCM negative-sector weights
`2^{-1/4}` and `sqrt 5 · 2^{-7/4}`.

The leakage ladder is likewise index-generic: one step of the negative sublattice again moves the
corpus index by two, hence the separation constant by `8`, so the same two-sided estimate separates
it.  The negative-sector floors `8/13` and `5/13` therefore hold for the true prolate family with no
hypothesis.
-/

noncomputable section

open Set MeasureTheory Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

/-! ## The coordinate limit at an arbitrary even prolate index -/

/-- **The constrained coordinate limit, at an arbitrary index.**  The squared coordinate converges
to the Hermite shape ratio of the doubled index, normalized by `sqrt(2 pi)`. -/
theorem tendsto_norm_sq_evenProlateConstraintCoord_index (n : ℕ) :
    Tendsto (fun a : GaloisForLFunctions.RHTower.ProlatePositiveAperture =>
        ‖evenProlateConstraintCoord (a : ℝ) n‖ ^ 2)
      atTop (𝓝 (hermiteShapeRatio (2 * n) / Real.sqrt (2 * Real.pi))) := by
  have hbase := GaloisForLFunctions.RHTower.tendsto_indexedRung_coordinateLimit n
  have hpi : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hne : ∀ᶠ a : GaloisForLFunctions.RHTower.ProlatePositiveAperture in atTop,
      evenProlateSignedValue (a : ℝ) n ≠ 0 :=
    GaloisForLFunctions.RHTower.tendsto_prolatePositiveAperture_val_atTop.eventually
      (eventually_evenProlateSignedValue_ne_zero n)
  have hev : ∀ᶠ a : GaloisForLFunctions.RHTower.ProlatePositiveAperture in atTop,
      Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a) *
          ((∫ u in (-1 : ℝ)..1, (signedModeRadialData (a : ℝ) n).R u) ^ 2
            / ∫ u in (-1 : ℝ)..1, ((signedModeRadialData (a : ℝ) n).R u) ^ 2)
        = Real.sqrt (2 * Real.pi) * ‖evenProlateConstraintCoord (a : ℝ) n‖ ^ 2 := by
    filter_upwards [hne] with a hva
    have ha : (0 : ℝ) < (a : ℝ) := a.property
    have hband : GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a
        = 2 * Real.pi * (a : ℝ) ^ 2 := rfl
    have hsqrt : Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a)
        = (a : ℝ) * Real.sqrt (2 * Real.pi) := by
      rw [hband, mul_comm (2 * Real.pi) ((a : ℝ) ^ 2),
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (a : ℝ) ^ 2), Real.sqrt_sq ha.le]
    rw [hsqrt, shapeRatio_radialR_eq_radialPhi ha n hva,
      norm_sq_evenProlateConstraintCoord_eq ha n hva]
    ring
  have hlim : Tendsto (fun a : GaloisForLFunctions.RHTower.ProlatePositiveAperture =>
      Real.sqrt (2 * Real.pi) * ‖evenProlateConstraintCoord (a : ℝ) n‖ ^ 2)
      atTop (𝓝 (hermiteShapeRatio (2 * n))) := by
    refine hbase.congr' hev
  have hdiv := hlim.div_const (Real.sqrt (2 * Real.pi))
  refine hdiv.congr fun a => ?_
  rw [mul_div_cancel_left₀ _ hpi.ne']

/-! ## The negative-sector Hermite coordinates -/

/-- The negative-sector squared Hermite weight `binom(4j+2, 2j+1)/4^{2j+1}`. -/
def constrainedProlateNegativeWeight (j : ℕ) : ℝ :=
  (Nat.centralBinom (2 * j + 1) : ℝ) / 4 ^ (2 * j + 1)

theorem constrainedProlateNegativeWeight_pos (j : ℕ) :
    0 < constrainedProlateNegativeWeight j := by
  have h : 0 < (Nat.centralBinom (2 * j + 1) : ℝ) := by
    exact_mod_cast Nat.centralBinom_pos (2 * j + 1)
  rw [constrainedProlateNegativeWeight]
  positivity

/-- The negative-sector Hermite coordinate. -/
def constrainedProlateNegativeCoordinate (j : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt 2 * constrainedProlateNegativeWeight j)

theorem constrainedProlateNegativeCoordinate_pos (j : ℕ) :
    0 < constrainedProlateNegativeCoordinate j := by
  have h := constrainedProlateNegativeWeight_pos j
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [constrainedProlateNegativeCoordinate]
  exact Real.sqrt_pos.2 (by positivity)

theorem constrainedProlateNegativeCoordinate_sq (j : ℕ) :
    constrainedProlateNegativeCoordinate j ^ 2
      = Real.sqrt 2 * constrainedProlateNegativeWeight j := by
  have h := constrainedProlateNegativeWeight_pos j
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [constrainedProlateNegativeCoordinate, Real.sq_sqrt (by positivity)]

/-- The Hermite shape ratio at a negative-sector index. -/
theorem hermiteShapeRatio_negativeSector (j : ℕ) :
    hermiteShapeRatio (2 * (2 * j + 1))
      = Real.sqrt (2 * Real.pi) * constrainedProlateNegativeCoordinate j ^ 2 := by
  rw [hermiteShapeRatio_two_mul, constrainedProlateNegativeCoordinate_sq,
    constrainedProlateNegativeWeight]
  have hsplit : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
    Real.sqrt_mul (by norm_num) _
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [hsplit]
  field_simp
  ring_nf
  nlinarith [h2, Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg Real.pi]

/-- **The negative-sector coordinate limit on the aperture axis.** -/
theorem tendsto_norm_evenProlateConstraintCoord_negative_atTop (j : ℕ) :
    Tendsto (fun lam : ℝ => ‖evenProlateConstraintCoord lam (2 * j + 1)‖) atTop
      (𝓝 (constrainedProlateNegativeCoordinate j)) := by
  have hpi : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsq := tendsto_norm_sq_evenProlateConstraintCoord_index (2 * j + 1)
  rw [hermiteShapeRatio_negativeSector j,
    mul_div_cancel_left₀ _ hpi.ne'] at hsq
  have h := hsq.sqrt
  have hpos := constrainedProlateNegativeCoordinate_pos j
  rw [Real.sqrt_sq hpos.le] at h
  have h' : Tendsto (fun a : GaloisForLFunctions.RHTower.ProlatePositiveAperture =>
      ‖evenProlateConstraintCoord (a : ℝ) (2 * j + 1)‖) atTop
      (𝓝 (constrainedProlateNegativeCoordinate j)) := by
    refine h.congr fun a => ?_
    exact Real.sqrt_sq (norm_nonneg _)
  have hmap : Filter.map (Subtype.val :
      GaloisForLFunctions.RHTower.ProlatePositiveAperture → ℝ) atTop = atTop := by
    refine Filter.map_val_atTop_of_Ici_subset (a := (1 : ℝ)) (s := {x : ℝ | 0 < x}) ?_
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := hx
    exact lt_of_lt_of_le zero_lt_one hx1
  rw [← hmap, Filter.tendsto_map'_iff]
  exact h'

/-! ## The first two negative-sector values -/

theorem constrainedProlateNegativeWeight_zero : constrainedProlateNegativeWeight 0 = 1 / 2 := by
  rw [constrainedProlateNegativeWeight]
  norm_num [Nat.centralBinom]

theorem constrainedProlateNegativeWeight_one : constrainedProlateNegativeWeight 1 = 5 / 16 := by
  rw [constrainedProlateNegativeWeight]
  norm_num [Nat.centralBinom, show Nat.choose 6 3 = 20 from rfl]

theorem constrainedProlateNegativeCoordinate_zero :
    constrainedProlateNegativeCoordinate 0 = (2 : ℝ) ^ (-(1 : ℝ) / 4) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hL : ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 = (2 : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(1 : ℝ) / 4)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h12 : (2 : ℝ) ^ (-(1 : ℝ) / 2) = (Real.sqrt 2)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsq : ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2
      = Real.sqrt 2 * constrainedProlateNegativeWeight 0 := by
    rw [hL, h12, constrainedProlateNegativeWeight_zero]
    field_simp
    linarith [h2]
  rw [constrainedProlateNegativeCoordinate, ← hsq, Real.sqrt_sq hpos.le]

theorem constrainedProlateNegativeCoordinate_one :
    constrainedProlateNegativeCoordinate 1 = Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4) := by
  have hden : (0 : ℝ) < (2 : ℝ) ^ ((7 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hpos : (0 : ℝ) ≤ Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4) := by positivity
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h72 : (2 : ℝ) ^ ((7 : ℝ) / 2) = 8 * Real.sqrt 2 := by
    rw [show (7 : ℝ) / 2 = 3 + 1 / 2 by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.sqrt_eq_rpow,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hL : (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)) ^ 2 = 5 / (8 * Real.sqrt 2) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5),
      ← Real.rpow_natCast ((2 : ℝ) ^ ((7 : ℝ) / 4)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [h72]
  have hsq : (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)) ^ 2
      = Real.sqrt 2 * constrainedProlateNegativeWeight 1 := by
    rw [hL, constrainedProlateNegativeWeight_one]
    field_simp
    linarith [h2]
  rw [constrainedProlateNegativeCoordinate, ← hsq, Real.sqrt_sq hpos]

/-! ## The negative-sector ladder -/

theorem injective_two_mul_add_one : Function.Injective (fun j : ℕ => 2 * j + 1) := by
  intro i j hij
  simpa using hij

/-- **One negative-sector ladder step separates the leakages.** -/
theorem tendsto_evenProlateSignedLeakage_negative_step_ratio (j : ℕ) :
    Tendsto (fun a : ℝ =>
      evenProlateSignedLeakage a (2 * j + 1) / evenProlateSignedLeakage a (2 * j + 3))
      atTop (𝓝 0) := by
  have hn : 1 ≤ 2 * j + 3 := by omega
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hK : (2 : ℝ) ≤ 8 * (j : ℝ) + 7 := by linarith
  have haux := ladder_gap_aux (Q := 8 * (j : ℝ) + 7) hK
  have hr0 : (0 : ℝ) < Real.sqrt (1 - 1 / (8 * (j : ℝ) + 7) ^ 2) := by
    refine Real.sqrt_pos.2 ?_
    have h : 1 / (8 * (j : ℝ) + 7) ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
      nlinarith
    linarith
  have hmono : (8 * (j : ℝ) + 5) / Real.sqrt (1 - 1 / (8 * (j : ℝ) + 7) ^ 2)
      ≤ (8 * (j : ℝ) + 7 - 1) / Real.sqrt (1 - 1 / (8 * (j : ℝ) + 7) ^ 2) := by
    rw [← sub_nonneg, ← sub_div]
    exact div_nonneg (by linarith) hr0.le
  have hgap : (0 : ℝ) + 3 + (4 * ((2 * j + 1 : ℕ) : ℝ) + 1)
        / (2 * Real.sqrt (1 - 1 / (8 * (j : ℝ) + 7) ^ 2))
      - (4 * ((2 * j + 3 : ℕ) : ℝ) + 1) / 2 < 0 := by
    push_cast
    have hsplit : (4 * (2 * (j : ℝ) + 1) + 1)
          / (2 * Real.sqrt (1 - 1 / (8 * (j : ℝ) + 7) ^ 2))
        = (8 * (j : ℝ) + 5) / Real.sqrt (1 - 1 / (8 * (j : ℝ) + 7) ^ 2) / 2 := by
      rw [div_div]
      congr 1
      · ring
      · ring
    rw [hsplit]
    linarith [hmono, haux]
  have h := tendsto_signedLeakage_ratio_pow (2 * j + 1) (2 * j + 3) hn 0
    (8 * (j : ℝ) + 7) hK hgap
  simpa [Real.rpow_zero] using h

/-- **The aperture-weighted negative-sector leakage is negligible against the next gap.** -/
theorem tendsto_evenProlateSignedLeakage_negative_step_tail (j : ℕ) :
    Tendsto (fun a : ℝ => a * evenProlateSignedLeakage a (2 * j + 3)
      / (evenProlateSignedLeakage a (2 * j + 5) - evenProlateSignedLeakage a (2 * j + 3)))
      atTop (𝓝 0) := by
  have hn : 1 ≤ 2 * j + 5 := by omega
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hK : (2 : ℝ) ≤ 8 * (j : ℝ) + 14 := by linarith
  have haux := ladder_gap_aux (Q := 8 * (j : ℝ) + 14) hK
  have hgap : (1 : ℝ) / 2 + 3 + (4 * ((2 * j + 3 : ℕ) : ℝ) + 1)
        / (2 * Real.sqrt (1 - 1 / (8 * (j : ℝ) + 14) ^ 2))
      - (4 * ((2 * j + 5 : ℕ) : ℝ) + 1) / 2 < 0 := by
    push_cast
    have hsplit : (4 * (2 * (j : ℝ) + 3) + 1)
          / (2 * Real.sqrt (1 - 1 / (8 * (j : ℝ) + 14) ^ 2))
        = (8 * (j : ℝ) + 14 - 1) / Real.sqrt (1 - 1 / (8 * (j : ℝ) + 14) ^ 2) / 2 := by
      rw [div_div]
      congr 1
      · ring
      · ring
    rw [hsplit]
    linarith [haux]
  have hmain := tendsto_signedLeakage_ratio_pow (2 * j + 3) (2 * j + 5) hn (1 / 2)
    (8 * (j : ℝ) + 14) hK hgap
  have hmaj : Tendsto (fun a : ℝ => 2 * (signedModeRadialBandwidth a ^ ((1 : ℝ) / 2)
      * (evenProlateSignedLeakage a (2 * j + 3) / evenProlateSignedLeakage a (2 * j + 5))))
      atTop (𝓝 0) := by
    simpa using hmain.const_mul (2 : ℝ)
  have hratio := tendsto_evenProlateSignedLeakage_negative_step_ratio (j + 1)
  simp only [show 2 * (j + 1) + 1 = 2 * j + 3 from by ring,
    show 2 * (j + 1) + 3 = 2 * j + 5 from by ring] at hratio
  have hhalf : ∀ᶠ a : ℝ in atTop,
      evenProlateSignedLeakage a (2 * j + 3) / evenProlateSignedLeakage a (2 * j + 5) < 1 / 2 :=
    hratio.eventually (eventually_lt_nhds (by norm_num))
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [hhalf, eventually_evenProlateSignedLeakage_pos (2 * j + 5) hn,
      eventually_ge_atTop (0 : ℝ)] with a hlt hpos ha0
    have hstep : evenProlateSignedLeakage a (2 * j + 3)
        < 1 / 2 * evenProlateSignedLeakage a (2 * j + 5) := by
      rw [div_lt_iff₀ hpos] at hlt
      linarith
    have hden : (0 : ℝ) < evenProlateSignedLeakage a (2 * j + 5)
        - evenProlateSignedLeakage a (2 * j + 3) := by linarith
    exact div_nonneg (mul_nonneg ha0 (evenProlateSignedLeakage_nonneg a (2 * j + 3))) hden.le
  · filter_upwards [hhalf, eventually_evenProlateSignedLeakage_pos (2 * j + 5) hn,
      eventually_ge_atTop (1 : ℝ)] with a hlt hpos ha1
    have ha0 : (0 : ℝ) ≤ a := by linarith
    have hstep : evenProlateSignedLeakage a (2 * j + 3)
        < 1 / 2 * evenProlateSignedLeakage a (2 * j + 5) := by
      rw [div_lt_iff₀ hpos] at hlt
      linarith
    have hden : (0 : ℝ) < evenProlateSignedLeakage a (2 * j + 5)
        - evenProlateSignedLeakage a (2 * j + 3) := by linarith
    have hbig : evenProlateSignedLeakage a (2 * j + 5) / 2
        ≤ evenProlateSignedLeakage a (2 * j + 5) - evenProlateSignedLeakage a (2 * j + 3) := by
      linarith
    have hc : signedModeRadialBandwidth a = 2 * Real.pi * a ^ 2 := rfl
    have hcpos : (0 : ℝ) < signedModeRadialBandwidth a := by
      rw [hc]
      have := Real.pi_pos
      positivity
    have hasq : a ^ 2 ≤ signedModeRadialBandwidth a := by
      rw [hc]
      nlinarith [Real.pi_gt_three, sq_nonneg a, ha1]
    have hale : a ≤ signedModeRadialBandwidth a ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow]
      exact (Real.le_sqrt ha0 hcpos.le).mpr hasq
    have hnumnn : (0 : ℝ) ≤ evenProlateSignedLeakage a (2 * j + 3) :=
      evenProlateSignedLeakage_nonneg a (2 * j + 3)
    calc a * evenProlateSignedLeakage a (2 * j + 3)
          / (evenProlateSignedLeakage a (2 * j + 5) - evenProlateSignedLeakage a (2 * j + 3))
        ≤ signedModeRadialBandwidth a ^ ((1 : ℝ) / 2)
            * evenProlateSignedLeakage a (2 * j + 3)
            / (evenProlateSignedLeakage a (2 * j + 5) / 2) := by
          apply div_le_div₀ (by positivity) (by nlinarith [hale, hnumnn])
            (by linarith) hbig
      _ = 2 * (signedModeRadialBandwidth a ^ ((1 : ℝ) / 2)
            * (evenProlateSignedLeakage a (2 * j + 3)
              / evenProlateSignedLeakage a (2 * j + 5))) := by
          field_simp

/-- **The negative-sector signed prolate leakage ladder is a ladder envelope.** -/
theorem ladderEnvelope_evenProlateSignedLeakage_negative :
    LadderEnvelope (fun a j => evenProlateSignedLeakage a (2 * j + 1)) where
  nonneg := fun a j => evenProlateSignedLeakage_nonneg a (2 * j + 1)
  mono := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha i j hij
    exact evenProlateSignedLeakage_monotone a ha (by omega)
  lt_succ := by
    intro j
    have hratio := tendsto_evenProlateSignedLeakage_negative_step_ratio j
    have hhalf : ∀ᶠ a : ℝ in atTop,
        evenProlateSignedLeakage a (2 * j + 1)
          / evenProlateSignedLeakage a (2 * j + 3) < 1 / 2 :=
      hratio.eventually (eventually_lt_nhds (by norm_num))
    filter_upwards [hhalf,
      eventually_evenProlateSignedLeakage_pos (2 * j + 3) (by omega)] with a hlt hpos
    rw [show 2 * (j + 1) + 1 = 2 * j + 3 from by ring]
    rw [div_lt_iff₀ hpos] at hlt
    linarith
  ratio_tendsto_zero := by
    intro j
    have h := tendsto_evenProlateSignedLeakage_negative_step_ratio j
    rw [show 2 * (j + 1) + 1 = 2 * j + 3 from by ring]
    exact h
  tail_tendsto_zero := by
    intro j
    have h := tendsto_evenProlateSignedLeakage_negative_step_tail j
    rw [show 2 * (j + 1) + 1 = 2 * j + 3 from by ring,
      show 2 * (j + 2) + 1 = 2 * j + 5 from by ring]
    exact h

/-! ## The negative-sector floors, unconditionally -/

theorem negativeSector_sum :
    ∀ᶠ lam : ℝ in atTop,
      Summable fun j : ℕ => ‖evenProlateConstraintCoord lam (2 * j + 1)‖ ^ 2 :=
  Eventually.of_forall fun lam =>
    (summable_evenProlateConstraintCoord_sq lam).comp_injective injective_two_mul_add_one

theorem negativeSector_bessel :
    ∀ᶠ lam : ℝ in atTop,
      (∑' j : ℕ, ‖evenProlateConstraintCoord lam (2 * j + 1)‖ ^ 2) ≤ 2 * lam := by
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with lam hlam
  exact tsum_evenProlateConstraintCoord_comp_sq_le hlam injective_two_mul_add_one

/-- **The negative-sector `8/13` floor, unconditionally.** -/
theorem constrainedProlateNegative_ground_ratio_tendsto :
    let D : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j + 1)
    let ℓ : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖
    Tendsto (fun lam : ℝ => infiniteSecularRoot (D lam) (ℓ lam) / D lam 1)
      atTop (𝓝 (8 / 13)) := by
  refine ladderEnvelope_evenProlateSignedLeakage_negative.ccm_negativeSector_ratio_tendsto
    negativeSector_sum negativeSector_bessel ?_ ?_
  · have h := tendsto_norm_evenProlateConstraintCoord_negative_atTop 0
    rwa [constrainedProlateNegativeCoordinate_zero] at h
  · have h := tendsto_norm_evenProlateConstraintCoord_negative_atTop 1
    rwa [constrainedProlateNegativeCoordinate_one] at h

/-- **The negative-sector `5/13` gap floor, unconditionally.** -/
theorem constrainedProlateNegative_gap_ratio_tendsto :
    let D : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j + 1)
    let ℓ : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖
    Tendsto (fun lam : ℝ =>
        (D lam 1 - infiniteSecularRoot (D lam) (ℓ lam)) / D lam 1)
      atTop (𝓝 (5 / 13)) := by
  refine ladderEnvelope_evenProlateSignedLeakage_negative.ccm_negativeSector_gap_ratio_tendsto
    negativeSector_sum negativeSector_bessel ?_ ?_
  · have h := tendsto_norm_evenProlateConstraintCoord_negative_atTop 0
    rwa [constrainedProlateNegativeCoordinate_zero] at h
  · have h := tendsto_norm_evenProlateConstraintCoord_negative_atTop 1
    rwa [constrainedProlateNegativeCoordinate_one] at h

/-! ## The positive-sector floors, and the leakage-normalized parity collapse -/

theorem constrainedProlateHermiteCoordinate_zero_eq :
    constrainedProlateHermiteCoordinate 0 = (2 : ℝ) ^ ((1 : ℝ) / 4) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hL : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = (2 : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 4)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsq : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2
      = Real.sqrt 2 * constrainedProlateHermiteWeight 0 := by
    rw [hL, constrainedProlateHermiteWeight_zero, Real.sqrt_eq_rpow]
    ring
  have hcoord : constrainedProlateHermiteCoordinate 0
      = Real.sqrt (Real.sqrt 2 * constrainedProlateHermiteWeight 0) := rfl
  rw [hcoord, ← hsq, Real.sqrt_sq hpos.le]

theorem constrainedProlateHermiteCoordinate_one_eq :
    constrainedProlateHermiteCoordinate 1 = Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4) := by
  have hden : (0 : ℝ) < (2 : ℝ) ^ ((5 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hpos : (0 : ℝ) ≤ Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4) := by positivity
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h52 : (2 : ℝ) ^ ((5 : ℝ) / 2) = 4 * Real.sqrt 2 := by
    rw [show (5 : ℝ) / 2 = 2 + 1 / 2 by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.sqrt_eq_rpow,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hL : (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) ^ 2 = 3 / (4 * Real.sqrt 2) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_natCast ((2 : ℝ) ^ ((5 : ℝ) / 4)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [h52]
  have hsq : (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) ^ 2
      = Real.sqrt 2 * constrainedProlateHermiteWeight 1 := by
    rw [hL, constrainedProlateHermiteWeight_one]
    field_simp
    linarith [h2]
  have hcoord : constrainedProlateHermiteCoordinate 1
      = Real.sqrt (Real.sqrt 2 * constrainedProlateHermiteWeight 1) := rfl
  rw [hcoord, ← hsq, Real.sqrt_sq hpos]

/-- **The positive-sector `8/11` floor, unconditionally.** -/
theorem constrainedProlatePositive_ground_ratio_tendsto :
    let D : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j)
    let ℓ : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j)‖
    Tendsto (fun lam : ℝ => infiniteSecularRoot (D lam) (ℓ lam) / D lam 1)
      atTop (𝓝 (8 / 11)) := by
  refine ladderEnvelope_evenProlateSignedLeakage.ccm_ground_ratio_tendsto
    evenProlateLadder_sum evenProlateLadder_bessel ?_ ?_
  · have h := tendsto_norm_evenProlateConstraintCoord_atTop 0
    rwa [constrainedProlateHermiteCoordinate_zero_eq] at h
  · have h := tendsto_norm_evenProlateConstraintCoord_atTop 1
    rwa [constrainedProlateHermiteCoordinate_one_eq] at h

/-- **The positive-sector `3/11` gap floor, unconditionally.** -/
theorem constrainedProlatePositive_gap_ratio_tendsto :
    let D : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j)
    let ℓ : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j)‖
    Tendsto (fun lam : ℝ =>
        (D lam 1 - infiniteSecularRoot (D lam) (ℓ lam)) / D lam 1)
      atTop (𝓝 (3 / 11)) := by
  refine ladderEnvelope_evenProlateSignedLeakage.ccm_gap_ratio_tendsto
    evenProlateLadder_sum evenProlateLadder_bessel ?_ ?_
  · have h := tendsto_norm_evenProlateConstraintCoord_atTop 0
    rwa [constrainedProlateHermiteCoordinate_zero_eq] at h
  · have h := tendsto_norm_evenProlateConstraintCoord_atTop 1
    rwa [constrainedProlateHermiteCoordinate_one_eq] at h

/-- **The parity collapse, in leakage-normalized form, unconditionally.**  The positive and
negative Fourier-sector constrained floors, each normalized by its own dominant leakage, separate
by exactly `13/11`. -/
theorem constrainedProlateParity_normalized_ratio_tendsto :
    let Dp : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j)
    let ℓp : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j)‖
    let Dn : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j + 1)
    let ℓn : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖
    Tendsto (fun lam : ℝ =>
        infiniteSecularRoot (Dp lam) (ℓp lam) / Dp lam 1
          / (infiniteSecularRoot (Dn lam) (ℓn lam) / Dn lam 1))
      atTop (𝓝 (13 / 11)) := by
  intro Dp ℓp Dn ℓn
  have hp := constrainedProlatePositive_ground_ratio_tendsto
  have hn := constrainedProlateNegative_ground_ratio_tendsto
  have h := hp.div hn (by norm_num : (8 : ℝ) / 13 ≠ 0)
  have hval : (8 : ℝ) / 11 / ((8 : ℝ) / 13) = 13 / 11 := by norm_num
  rw [hval] at h
  exact Tendsto.congr (fun _ => rfl) h

/-- **The quantified constrained spectral gap `(7)`, unconditionally.**  For every constant below
`3/11`, every other constrained eigenvalue eventually exceeds the ground one by that multiple of
the dominant leakage. -/
theorem constrainedProlatePositive_spectralGap_eventually {cst : ℝ} (hc : cst < 3 / 11) :
    let D : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j)
    let ℓ : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j)‖
    ∀ᶠ lam : ℝ in atTop, ∀ μ' : ℝ, infiniteSecular (D lam) (ℓ lam) μ' = 0 →
      μ' ≠ infiniteSecularRoot (D lam) (ℓ lam) →
      cst * D lam 1 ≤ μ' - infiniteSecularRoot (D lam) (ℓ lam) := by
  refine ladderEnvelope_evenProlateSignedLeakage.ccm_spectralGap_eventually
    evenProlateLadder_sum evenProlateLadder_bessel ?_ ?_ hc
  · have h := tendsto_norm_evenProlateConstraintCoord_atTop 0
    rwa [constrainedProlateHermiteCoordinate_zero_eq] at h
  · have h := tendsto_norm_evenProlateConstraintCoord_atTop 1
    rwa [constrainedProlateHermiteCoordinate_one_eq] at h

end RHTower

end
