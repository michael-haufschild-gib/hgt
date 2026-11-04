import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.CoreHeckeBoundaryCharge
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.LewisPeriodReflectionPositivity

/-!
# The retained Hecke channel reads the quarter line

At every upper Mayer resonance the raw `T₂` image of the core leaves whole-Haar `L²`, and exactly
one boundary coefficient `c = core_s(2)` restores it (`hecke_mayerPeriodCore_boundary_charge_iff`);
`c ≠ 0` (`mayerPeriodCore_two_ne_zero`). The retained channel is `u_s = c·1_{(0,1)}`.

The co-isometry defect `D_s(ψ) = ‖ψ‖²_LP − ‖I_{½−s̄} ψ‖²_LP` of the full resonant period is `≤ 0` on
both sides of `Re s = ¼` and vanishes only on it (`resonantLewisPeriod_coIsometryDefect_*`): it does not
see which side a resonance lies on. On the retained channel it is signed:

* **Exact value** (`lewisCoIsometryDefect_heckeBoundaryChannel`).
  `D_s(u_s) = |c|² Φ(Re s)`, `Φ(σ) = ∫₀¹ (1 − b^{1−4σ}) w(b) db`, with `w` the critical weight. The
  inversion `I_{½−s̄}` moves the lower cusp to the upper one with the weight `a^{4σ−2}`; inverting back
  costs the Jacobian `w(1/b) b^{−2} = w(b)/b`.
* **The sign law** (`retainedHeckeChannel_defect_sign`). `D_s(u_s) > 0 ⟺ Re s < ¼`,
  `D_s(u_s) = 0 ⟺ Re s = ¼`, `D_s(u_s) < 0 ⟺ Re s > ¼`.
* **Reflected pairs** (`retainedHeckeChannel_defect_reflect`). The reflected resonance `½ − s̄` has
  the opposite sign.

The sign is read off the retained channel of `T₂` alone: arithmetic enters only through `c ≠ 0`, the
fact that the first Hecke step retains the channel at every resonance; the side of `¼` is the
exponent of the inversion. The law is unconditional and holds at every resonance, so it carries the
position of a resonance relative to the line, not a constraint forcing it onto the line.
-/

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- The retained boundary channel of `T₂`: the constant `c` on the lower cusp `(0, 1)`. -/
def heckeBoundaryChannel (c : ℂ) : ℝ → ℂ := (Ioo (0 : ℝ) 1).indicator fun _ => c

/-- The channel profile `Φ(σ) = ∫₀¹ (1 − b^{1−4σ}) w(b) db`. -/
def channelProfile (σ : ℝ) : ℝ :=
  ∫ b in Ioo (0 : ℝ) 1, (1 - b ^ (1 - 4 * σ)) * lewisCriticalWeight b

/-! ### The critical weight on the lower cusp -/

/-- Inversion of the critical weight: `w(1/b) = b w(b)`. -/
theorem lewisCriticalWeight_inv {b : ℝ} (hb : 0 < b) :
    lewisCriticalWeight b⁻¹ = b * lewisCriticalWeight b := by
  unfold lewisCriticalWeight
  rw [inv_inv, add_comm b⁻¹ b, Real.inv_rpow hb.le, ← Real.rpow_neg hb.le, neg_neg]
  have h : b * b ^ (-(1 / 2 : ℝ)) = b ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_one_add' hb.le (by norm_num)]; norm_num
  rw [← h]; ring

/-- On `(0, 1)`, `w(b) ≤ b^{11/2}`. -/
theorem lewisCriticalWeight_le {b : ℝ} (hb : 0 < b) :
    lewisCriticalWeight b ≤ b ^ (11 / 2 : ℝ) := by
  unfold lewisCriticalWeight
  have hle : b⁻¹ ≤ b + b⁻¹ := by linarith
  have h6 : (b + b⁻¹) ^ (-6 : ℝ) ≤ (b⁻¹) ^ (-6 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hb) hle (by norm_num)
  have hinv : (b⁻¹) ^ (-6 : ℝ) = b ^ (6 : ℝ) := by
    rw [Real.inv_rpow hb.le, ← Real.rpow_neg hb.le, neg_neg]
  have hsplit : b ^ (11 / 2 : ℝ) = b ^ (6 : ℝ) * b ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hb]; norm_num
  rw [hsplit, ← hinv]
  exact mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg hb.le _)

theorem measurable_lewisCriticalWeight : Measurable lewisCriticalWeight := by
  unfold lewisCriticalWeight
  fun_prop

/-- `b^e w(b)` is integrable on `(0, 1)` for `e ≥ −11/2`. -/
theorem integrableOn_rpow_mul_weight {e : ℝ} (he : -(11 / 2) ≤ e) :
    IntegrableOn (fun b => b ^ e * lewisCriticalWeight b) (Ioo (0 : ℝ) 1) := by
  refine Measure.integrableOn_of_bounded (M := 1) (by simp) ?_ ?_
  · exact ((measurable_id.pow_const e).mul measurable_lewisCriticalWeight).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun b hb => ?_)
    obtain ⟨hb0, hb1⟩ := hb
    have hw0 := (lewisCriticalWeight_pos hb0).le
    have hbe : 0 ≤ b ^ e := Real.rpow_nonneg hb0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hbe hw0)]
    calc b ^ e * lewisCriticalWeight b ≤ b ^ e * b ^ (11 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left (lewisCriticalWeight_le hb0) hbe
      _ = b ^ (e + 11 / 2) := by rw [Real.rpow_add hb0]
      _ ≤ 1 := Real.rpow_le_one hb0.le hb1.le (by linarith)

theorem integrableOn_weight : IntegrableOn lewisCriticalWeight (Ioo (0 : ℝ) 1) := by
  have h := integrableOn_rpow_mul_weight (e := 0) (by norm_num)
  refine h.congr_fun (fun b hb => ?_) measurableSet_Ioo
  simp only [Real.rpow_zero, one_mul]

/-! ### The defect of the retained channel -/

theorem lewisCriticalNormSq_heckeBoundaryChannel (c : ℂ) :
    lewisCriticalNormSq (heckeBoundaryChannel c) =
      ‖c‖ ^ 2 * ∫ b in Ioo (0 : ℝ) 1, lewisCriticalWeight b := by
  unfold lewisCriticalNormSq
  have hpt : (fun a => ‖heckeBoundaryChannel c a‖ ^ 2 * lewisCriticalWeight a) =
      (Ioo (0 : ℝ) 1).indicator fun a => ‖c‖ ^ 2 * lewisCriticalWeight a := by
    funext a
    by_cases ha : a ∈ Ioo (0 : ℝ) 1
    · simp [heckeBoundaryChannel, indicator_of_mem ha]
    · simp [heckeBoundaryChannel, indicator_of_notMem ha]
  rw [hpt, setIntegral_indicator measurableSet_Ioo,
    show Ioi (0 : ℝ) ∩ Ioo 0 1 = Ioo 0 1 from inter_eq_right.mpr Ioo_subset_Ioi_self,
    integral_const_mul]

theorem lewisCriticalNormSq_inversion_heckeBoundaryChannel (s c : ℂ) :
    lewisCriticalNormSq (lewisModularInversion (riemannMayerReflect s) (heckeBoundaryChannel c)) =
      ‖c‖ ^ 2 * ∫ b in Ioo (0 : ℝ) 1, b ^ (1 - 4 * s.re) * lewisCriticalWeight b := by
  unfold lewisCriticalNormSq
  rw [integral_Ioi_zero_inv_subst]
  have hre : (-(2 * riemannMayerReflect s)).re = 2 * s.re - 1 := by
    simp [riemannMayerReflect]; ring
  have hpt : ∀ b ∈ Ioi (0 : ℝ), b ^ (-2 : ℝ) • (‖lewisModularInversion (riemannMayerReflect s)
        (heckeBoundaryChannel c) b⁻¹‖ ^ 2 * lewisCriticalWeight b⁻¹) =
      (Ioo (0 : ℝ) 1).indicator (fun b => ‖c‖ ^ 2 * (b ^ (1 - 4 * s.re) *
        lewisCriticalWeight b)) b := by
    intro b hb
    have hb0 : 0 < b := hb
    have hnorm : ‖((b⁻¹ : ℝ) : ℂ) ^ (-(2 * riemannMayerReflect s))‖ ^ 2 = b ^ (2 - 4 * s.re) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr hb0), hre, Real.inv_rpow hb0.le,
        ← Real.rpow_neg hb0.le, ← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
      norm_num; ring_nf
    rw [smul_eq_mul, lewisModularInversion, inv_inv, norm_mul, mul_pow, hnorm,
      lewisCriticalWeight_inv hb0]
    by_cases hbI : b ∈ Ioo (0 : ℝ) 1
    · rw [heckeBoundaryChannel, indicator_of_mem hbI, indicator_of_mem hbI]
      have h : b ^ (-2 : ℝ) * (b ^ (2 - 4 * s.re) * ‖c‖ ^ 2 * (b * lewisCriticalWeight b)) =
          ‖c‖ ^ 2 * ((b ^ (-2 : ℝ) * b ^ (2 - 4 * s.re) * b) * lewisCriticalWeight b) := by ring
      rw [h, ← Real.rpow_add hb0, ← Real.rpow_add_one hb0.ne']
      congr 3; ring
    · rw [heckeBoundaryChannel, indicator_of_notMem hbI, indicator_of_notMem hbI]
      simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, setIntegral_indicator measurableSet_Ioo,
    show Ioi (0 : ℝ) ∩ Ioo 0 1 = Ioo 0 1 from inter_eq_right.mpr Ioo_subset_Ioi_self,
    integral_const_mul]

/-- **Exact value.** `D_s(c·1_{(0,1)}) = |c|² Φ(Re s)`. -/
theorem lewisCoIsometryDefect_heckeBoundaryChannel {s : ℂ} (hs : s.re ≤ 13 / 8) (c : ℂ) :
    lewisCoIsometryDefect s (heckeBoundaryChannel c) = ‖c‖ ^ 2 * channelProfile s.re := by
  rw [lewisCoIsometryDefect, lewisCriticalNormSq_heckeBoundaryChannel,
    lewisCriticalNormSq_inversion_heckeBoundaryChannel, ← mul_sub, channelProfile,
    ← integral_sub integrableOn_weight
      (integrableOn_rpow_mul_weight (e := 1 - 4 * s.re) (by linarith))]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo fun b _ => ?_
  ring

/-! ### The sign of the profile -/

theorem integrableOn_channelIntegrand {σ : ℝ} (hσ : σ ≤ 13 / 8) :
    IntegrableOn (fun b => (1 - b ^ (1 - 4 * σ)) * lewisCriticalWeight b) (Ioo (0 : ℝ) 1) := by
  refine (integrableOn_weight.sub (integrableOn_rpow_mul_weight (e := 1 - 4 * σ)
    (by linarith))).congr_fun (fun b _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioo

/-- A strictly positive integrand on `(0, 1)` has positive integral. -/
theorem setIntegral_Ioo_pos {f : ℝ → ℝ} (hf : IntegrableOn f (Ioo (0 : ℝ) 1))
    (hpos : ∀ b ∈ Ioo (0 : ℝ) 1, 0 < f b) : 0 < ∫ b in Ioo (0 : ℝ) 1, f b := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ hpos zero_lt_one
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
    integrableOn_Ioc_iff_integrableOn_Ioo]
  exact hf

theorem channelProfile_pos {σ : ℝ} (hσ : σ < 1 / 4) : 0 < channelProfile σ :=
  setIntegral_Ioo_pos (integrableOn_channelIntegrand (by linarith)) fun b ⟨hb0, hb1⟩ =>
    mul_pos (sub_pos.mpr (Real.rpow_lt_one hb0.le hb1 (by linarith)))
      (lewisCriticalWeight_pos hb0)

theorem channelProfile_neg {σ : ℝ} (h1 : 1 / 4 < σ) (h2 : σ ≤ 13 / 8) : channelProfile σ < 0 := by
  have h := setIntegral_Ioo_pos (f := fun b => -((1 - b ^ (1 - 4 * σ)) * lewisCriticalWeight b))
    (integrableOn_channelIntegrand h2).neg fun b ⟨hb0, hb1⟩ => by
      have : 1 < b ^ (1 - 4 * σ) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hb0 hb1 (by linarith)
      have := lewisCriticalWeight_pos hb0
      nlinarith
  rw [integral_neg] at h
  unfold channelProfile
  linarith

theorem channelProfile_quarter : channelProfile (1 / 4) = 0 := by
  unfold channelProfile
  norm_num

/-- `Φ` has the sign of `¼ − σ`. -/
theorem channelProfile_sign {σ : ℝ} (hσ : σ ≤ 13 / 8) :
    (0 < channelProfile σ ↔ σ < 1 / 4) ∧ (channelProfile σ = 0 ↔ σ = 1 / 4) ∧
      (channelProfile σ < 0 ↔ 1 / 4 < σ) := by
  rcases lt_trichotomy σ (1 / 4) with h | h | h
  · have := channelProfile_pos h
    exact ⟨⟨fun _ => h, fun _ => this⟩, ⟨fun h0 => by linarith, fun h0 => by linarith⟩,
      ⟨fun h0 => by linarith, fun h0 => by linarith⟩⟩
  · subst h
    rw [channelProfile_quarter]
    exact ⟨⟨fun h0 => absurd h0 (lt_irrefl 0), fun h0 => absurd h0 (lt_irrefl _)⟩,
      ⟨fun _ => rfl, fun _ => rfl⟩, ⟨fun h0 => absurd h0 (lt_irrefl 0),
        fun h0 => absurd h0 (lt_irrefl _)⟩⟩
  · have := channelProfile_neg h hσ
    exact ⟨⟨fun h0 => by linarith, fun h0 => by linarith⟩, ⟨fun h0 => by linarith,
      fun h0 => by linarith⟩, ⟨fun _ => h, fun _ => this⟩⟩

/-! ### The sign law at the resonances -/

/-- **The retained `T₂` channel reads the quarter line.** At every upper Mayer resonance the
co-isometry defect of the retained boundary channel `core_s(2)·1_{(0,1)}` equals
`|core_s(2)|² Φ(Re s)`, is positive exactly left of `Re s = ¼`, zero exactly on it and negative
exactly right of it. -/
theorem retainedHeckeChannel_defect_sign (s : upperMayerResonances) :
    lewisCoIsometryDefect s.1 (heckeBoundaryChannel (mayerPeriodCore s.1 2)) =
        ‖mayerPeriodCore s.1 2‖ ^ 2 * channelProfile s.1.re ∧
      (0 < lewisCoIsometryDefect s.1 (heckeBoundaryChannel (mayerPeriodCore s.1 2)) ↔
        s.1.re < 1 / 4) ∧
      (lewisCoIsometryDefect s.1 (heckeBoundaryChannel (mayerPeriodCore s.1 2)) = 0 ↔
        s.1.re = 1 / 4) ∧
      (lewisCoIsometryDefect s.1 (heckeBoundaryChannel (mayerPeriodCore s.1 2)) < 0 ↔
        1 / 4 < s.1.re) := by
  have hσ : s.1.re ≤ 13 / 8 := by linarith [s.2.2.2.1]
  have hc : 0 < ‖mayerPeriodCore s.1 2‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (mayerPeriodCore_two_ne_zero s.2)) 2
  have hD := lewisCoIsometryDefect_heckeBoundaryChannel hσ (mayerPeriodCore s.1 2)
  obtain ⟨h1, h2, h3⟩ := channelProfile_sign hσ
  refine ⟨hD, ?_, ?_, ?_⟩ <;> rw [hD]
  · rw [mul_pos_iff_of_pos_left hc]; exact h1
  · rw [mul_eq_zero, or_iff_right (ne_of_gt hc)]; exact h2
  · exact ⟨fun h => h3.mp (neg_of_mul_neg_right h hc.le),
      fun h => mul_neg_of_pos_of_neg hc (h3.mpr h)⟩

/-- The retained channel is the unique `T₂` boundary coefficient: the defining property. -/
theorem retainedHeckeChannel_unique (s : upperMayerResonances) (c : ℂ) :
    IntegrableOn (fun a : ℝ => ‖lewisHeckeT2 s.1 (mayerPeriodCore s.1) a -
        heckeBoundaryChannel c a‖ ^ 2 / a) (Ioi 0) ↔ c = mayerPeriodCore s.1 2 :=
  hecke_mayerPeriodCore_boundary_charge_iff s c

/-- **Reflected resonances carry opposite signs.** -/
theorem retainedHeckeChannel_defect_reflect (s : upperMayerResonances) :
    0 < lewisCoIsometryDefect s.1 (heckeBoundaryChannel (mayerPeriodCore s.1 2)) ↔
      lewisCoIsometryDefect (reflectUpperResonance s).1
        (heckeBoundaryChannel (mayerPeriodCore (reflectUpperResonance s).1 2)) < 0 := by
  rw [(retainedHeckeChannel_defect_sign s).2.1, (retainedHeckeChannel_defect_sign _).2.2.2]
  have hre : (reflectUpperResonance s).1.re = 1 / 2 - s.1.re := by
    simp [reflectUpperResonance, riemannMayerReflect]
  rw [hre]
  constructor <;> intro h <;> linarith

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
