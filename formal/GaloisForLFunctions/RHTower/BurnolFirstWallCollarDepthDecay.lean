import GaloisForLFunctions.RHTower.BurnolBocksteinLimit
import GaloisForLFunctions.RHTower.BurnolCollarKernelSeries
import GaloisForLFunctions.RHTower.BurnolFirstWallTailMass

/-!
# The completed collar pairing is three geometric orders below the depth weight

The normalised collar reading `∫ κ(r) q^{-n} W_G(nL + r) dr` tends to zero because the limit
profile `R e^{-r/2}` lies in the kernel of the completed collar.  Subtracting that null profile
turns the reading into a pairing against the **error** of the depth profile, and for a source whose
exterior mass decays quadratically that error is `O(4^{-n} e^{-5r/2})` on the half where the shifted
lag is positive.

On the other half the error is only `O(e^{-r/2})`, but there the lag constraint `r ≤ -nL` supplies
the missing factor: `e^{2r} ≤ 4^{-n}` exactly on that region, so the majorant
`4^{-n} |κ(r)| e^{-5r/2}` works there as well.  One integrable majorant therefore controls the whole
reading, and the pairing is `O(4^{-n})`.

The weight `e^{-5r/2}` is integrable against the collar kernel because the kernel against the stable
mode decays like `e^{-3|r|}`: on the right the polynomial factor `z(2z²-7z+3)` contributes an extra
`e^{-2r}`, and on the left `z ≥ π` grows like `e^{-2r}` while the Gamma tail `e^{-z}` beats every
power of it.

Restoring the depth weight `q^n = 2^{-n/2}` on both sides puts the raw depth pairing at
`q^{6n} = 8^{-n}`.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-! ## A cubic majorant for the collar kernel -/

/-- **The collar kernel against the stable mode decays like `e^{-3|u|}`.** -/
theorem abs_burnolCollarKernel_mul_mode_le_cubic (u : ℝ) :
    |burnolCollarKernel 0 u * Real.exp (-u / 2)| ≤ 4000 * Real.exp (-3 * |u|) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hπ4 : (3 : ℝ) < π := by linarith [Real.pi_gt_three]
  have hπ32 : π ≤ 4 := Real.pi_le_four
  set z : ℝ := burnolCollarZ 0 u with hz
  have hzpos : 0 < z := burnolCollarZ_pos 0 u
  have hzval : z = π * Real.exp (-2 * u) := by
    rw [hz, burnolCollarZ]
    norm_num
  have hep : (0 : ℝ) < Real.exp (-z) := Real.exp_pos _
  have hzexp : Real.exp (-burnolCollarZ 0 u) = Real.exp (-z) := by rw [hz]
  rw [burnolCollarKernel_mul_mode_eq u, ← hz, hzexp, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_pos (Real.exp_pos (-u)),
    abs_of_pos hep]
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
    have hexp2pos : (0 : ℝ) < Real.exp (-2 * u) := Real.exp_pos _
    have hexp1 : Real.exp (-z) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hz4 : z ≤ 4 * Real.exp (-2 * u) := by
      rw [hzval]
      nlinarith [hexp2pos, hπ32]
    have hzle4 : z ≤ 4 := by
      have h1 : Real.exp (-2 * u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith [hz4]
    have hsplit : |z * (2 * z ^ 2 - 7 * z + 3)| ≤ 63 * z := by
      rw [abs_le]
      constructor <;>
        nlinarith [hzpos, hzle4, sq_nonneg z, mul_nonneg hzpos.le (sub_nonneg.mpr hzle4),
          mul_nonneg (mul_nonneg hzpos.le hzpos.le) (sub_nonneg.mpr hzle4)]
    have hprod : Real.exp (-u) * Real.exp (-2 * u) = Real.exp (-3 * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hmid : Real.exp (-z) * |z * (2 * z ^ 2 - 7 * z + 3)| ≤ 252 * Real.exp (-2 * u) := by
      calc Real.exp (-z) * |z * (2 * z ^ 2 - 7 * z + 3)|
          ≤ 1 * (63 * (4 * Real.exp (-2 * u))) :=
            mul_le_mul hexp1 (le_trans hsplit (by linarith)) (abs_nonneg _) zero_le_one
        _ = 252 * Real.exp (-2 * u) := by ring
    have hstep : 4 * Real.exp (-u) * (Real.exp (-z) * |z * (2 * z ^ 2 - 7 * z + 3)|) ≤
        4 * Real.exp (-u) * (252 * Real.exp (-2 * u)) :=
      mul_le_mul_of_nonneg_left hmid (by positivity)
    have hval : 4 * Real.exp (-u) * (252 * Real.exp (-2 * u)) = 1008 * Real.exp (-3 * u) := by
      rw [← hprod]
      ring
    rw [hval] at hstep
    linarith [hstep, Real.exp_pos (-3 * u)]
  · rw [abs_of_neg hu, show -3 * -u = 3 * u by ring]
    have hz2 : Real.exp (-2 * u) = z / π := by
      rw [hzval]
      field_simp
    have h4 : Real.exp (-4 * u) = z ^ 2 / π ^ 2 := by
      rw [show (-4 : ℝ) * u = -2 * u + -2 * u by ring, Real.exp_add, hz2]
      ring
    have hsplit3 : Real.exp (-u) = Real.exp (-4 * u) * Real.exp (3 * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hsplit : |z * (2 * z ^ 2 - 7 * z + 3)| ≤ 2 * z ^ 3 + 7 * z ^ 2 + 3 * z := by
      rw [abs_le]
      constructor <;> nlinarith [hzpos, sq_nonneg z, pow_pos hzpos 3]
    have hquint : (2 * z ^ 5 + 7 * z ^ 4 + 3 * z ^ 3) * Real.exp (-z) ≤ 8123 := by
      nlinarith [burnolPow5ExpBound hzpos.le, burnolPow4ExpBound hzpos.le,
        burnolPow3ExpBound hzpos.le, hep]
    have hbb : z ^ 2 * (Real.exp (-z) * |z * (2 * z ^ 2 - 7 * z + 3)|) ≤ 8123 := by
      calc z ^ 2 * (Real.exp (-z) * |z * (2 * z ^ 2 - 7 * z + 3)|)
          ≤ z ^ 2 * (Real.exp (-z) * (2 * z ^ 3 + 7 * z ^ 2 + 3 * z)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsplit hep.le) (by positivity)
        _ = (2 * z ^ 5 + 7 * z ^ 4 + 3 * z ^ 3) * Real.exp (-z) := by ring
        _ ≤ 8123 := hquint
    have hexp3pos : (0 : ℝ) < Real.exp (3 * u) := Real.exp_pos _
    have hmain : 4 * Real.exp (-u) * (Real.exp (-z) * |z * (2 * z ^ 2 - 7 * z + 3)|) =
        4 / π ^ 2 * Real.exp (3 * u) *
          (z ^ 2 * (Real.exp (-z) * |z * (2 * z ^ 2 - 7 * z + 3)|)) := by
      rw [hsplit3, h4]
      ring
    rw [hmain]
    have hstep := mul_le_mul_of_nonneg_left hbb
      (by positivity : (0 : ℝ) ≤ 4 / π ^ 2 * Real.exp (3 * u))
    have hcoef2 : 4 / π ^ 2 * 8123 ≤ 4000 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [hπ4, hπ]
    have hfin : 4 / π ^ 2 * Real.exp (3 * u) * 8123 ≤ 4000 * Real.exp (3 * u) := by
      nlinarith [hcoef2, hexp3pos]
    linarith [hstep, hfin]

/-! ## The five-halves mode mass of the collar kernel -/

theorem burnolCollarModeFive_nonneg (r : ℝ) :
    0 ≤ |burnolCollarKernel 0 r| * Real.exp (-5 * r / 2) := by positivity

theorem burnolCollarModeFive_le (r : ℝ) :
    |burnolCollarKernel 0 r| * Real.exp (-5 * r / 2) ≤ 4000 * Real.exp (-|r|) := by
  have hcubic := abs_burnolCollarKernel_mul_mode_le_cubic r
  rw [abs_mul, abs_of_pos (Real.exp_pos (-r / 2))] at hcubic
  have hfac : |burnolCollarKernel 0 r| * Real.exp (-5 * r / 2) =
      |burnolCollarKernel 0 r| * Real.exp (-r / 2) * Real.exp (-2 * r) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hstep : |burnolCollarKernel 0 r| * Real.exp (-r / 2) * Real.exp (-2 * r) ≤
      4000 * Real.exp (-3 * |r|) * Real.exp (-2 * r) :=
    mul_le_mul_of_nonneg_right hcubic (Real.exp_pos _).le
  have hexp : (4000 : ℝ) * Real.exp (-3 * |r|) * Real.exp (-2 * r) ≤ 4000 * Real.exp (-|r|) := by
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    linarith [neg_abs_le r]
  rw [hfac]
  linarith [hstep, hexp]

theorem burnolIntegrable_collarModeFive :
    Integrable (fun r : ℝ => |burnolCollarKernel 0 r| * Real.exp (-5 * r / 2)) := by
  have hcont : Continuous fun r : ℝ => |burnolCollarKernel 0 r| * Real.exp (-5 * r / 2) := by
    unfold burnolCollarKernel burnolCollarZ
    fun_prop
  refine MeasureTheory.Integrable.mono' (g := fun r : ℝ => 4000 * Real.exp (-|r|))
    (burnolIntegrable_exp_neg_abs.const_mul 4000) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (burnolCollarModeFive_nonneg r)]
  exact burnolCollarModeFive_le r

/-- The total mass of the collar kernel against the `5/2` mode. -/
def burnolCollarModeFiveMass : ℝ := ∫ r : ℝ, |burnolCollarKernel 0 r| * Real.exp (-5 * r / 2)

theorem burnolCollarModeFiveMass_nonneg : 0 ≤ burnolCollarModeFiveMass :=
  MeasureTheory.integral_nonneg fun r => burnolCollarModeFive_nonneg r

/-! ## Two dyadic exponentials -/

theorem burnolExpTwoLogTwo (n : ℕ) : Real.exp (2 * (n : ℝ) * Real.log 2) = (4 : ℝ) ^ n := by
  rw [show 2 * (n : ℝ) * Real.log 2 = Real.log 4 * (n : ℝ) by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring,
    ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), Real.rpow_natCast]

theorem burnolExpNegTwoLogTwo (n : ℕ) :
    Real.exp (-(2 * (n : ℝ) * Real.log 2)) = 1 / (4 : ℝ) ^ n := by
  rw [Real.exp_neg, burnolExpTwoLogTwo, one_div]

theorem burnolExpQuadraticCut (s : ℝ) : (Real.exp s / 2) ^ (-2 : ℝ) = 4 * Real.exp (-2 * s) := by
  have hpos : (0 : ℝ) < Real.exp s / 2 := by positivity
  have hne : Real.exp (2 * s) ≠ 0 := (Real.exp_pos _).ne'
  have hneg2 : (Real.exp s / 2) ^ (-2 : ℝ) = ((Real.exp s / 2) ^ (2 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hpos.le, ← Real.rpow_natCast (Real.exp s / 2) 2]
    norm_num
  have hsq : (Real.exp s / 2) ^ (2 : ℕ) = Real.exp (2 * s) / 4 := by
    rw [div_pow, pow_two, ← Real.exp_add, show s + s = 2 * s by ring]
    norm_num
  have hexp : Real.exp (-2 * s) = (Real.exp (2 * s))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hneg2, hsq, hexp]
  field_simp

/-! ## The residue error of the crossing correlation -/

/-- **The error of the depth profile is the exterior mass beyond the moving cut.** -/
theorem burnolCrossingCorrelation_residue_error {g : ℝ → ℂ} {c : ℂ}
    (hhead : BurnolApertureHead g c) (hIoi : IntegrableOn g (Ioi (1 / 2 : ℝ)))
    {s : ℝ} (hs : 0 < s) :
    ((Real.exp (s / 2) : ℝ) : ℂ) * burnolCrossingCorrelationW g s -
        -c * (starRingEnd ℂ) (∫ t in Ioi (1 / 2 : ℝ), g t) =
      c * (starRingEnd ℂ) (∫ t in Ioi (Real.exp s / 2), g t) := by
  have hX : (1 / 2 : ℝ) ≤ Real.exp s / 2 := by
    have h := Real.one_le_exp hs.le
    linarith
  have hdisj : Disjoint (Ioc (1 / 2 : ℝ) (Real.exp s / 2)) (Ioi (Real.exp s / 2)) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx1⟩ hx2
    exact absurd (mem_Ioi.mp hx2) (not_lt.mpr hx1)
  have hunion : Ioc (1 / 2 : ℝ) (Real.exp s / 2) ∪ Ioi (Real.exp s / 2) = Ioi (1 / 2 : ℝ) :=
    Ioc_union_Ioi_eq_Ioi hX
  have hsplit := setIntegral_union hdisj measurableSet_Ioi
    (hIoi.mono_set fun x hx => mem_Ioi.mpr hx.1)
    (hIoi.mono_set fun x hx => mem_Ioi.mpr (lt_of_le_of_lt hX (mem_Ioi.mp hx)))
  rw [hunion] at hsplit
  have hS := congrArg (starRingEnd ℂ) hsplit
  rw [map_add] at hS
  have hcancel : ((Real.exp (s / 2) : ℝ) : ℂ) * ((Real.exp (-s / 2) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, show s / 2 + -s / 2 = 0 by ring, Real.exp_zero]
    norm_num
  rw [burnolCrossingCorrelationW_eq_of_head hhead hs, integral_conj, hS]
  linear_combination
    (-c * (starRingEnd ℂ) (∫ t in Ioc (1 / 2 : ℝ) (Real.exp s / 2), g t)) * hcancel

/-! ## The quartic decay of the normalised collar reading -/

/-- A positive-ray source has **quadratic exterior mass** when the mass beyond every cut past the
aperture is `O(X^{-2})`. -/
def BurnolQuadraticExteriorMass (g : ℝ → ℂ) (C : ℝ) : Prop :=
  ∀ X : ℝ, 1 / 2 ≤ X → ‖∫ t in Ioi X, g t‖ ≤ C * X ^ (-2 : ℝ)

/-- **The error of the normalised depth profile is uniformly `O(4^{-n} e^{-5r/2})`.**  Past the lag
the exterior mass supplies the two extra powers; before it the lag constraint does. -/
theorem norm_burnolDepthProfileError_le {g : ℝ → ℂ} {c : ℂ} {C : ℝ}
    (hhead : BurnolApertureHead g c) (hIoi : IntegrableOn g (Ioi (1 / 2 : ℝ)))
    (hC0 : 0 ≤ C) (hC : BurnolQuadraticExteriorMass g C) (n : ℕ) (r : ℝ) :
    ‖((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
          burnolCrossingCorrelationW g ((n : ℝ) * Real.log 2 + r) -
        -c * (starRingEnd ℂ) (∫ t in Ioi (1 / 2 : ℝ), g t) * ((Real.exp (-r / 2) : ℝ) : ℂ)‖ ≤
      (4 * ‖c‖ * C + ‖c‖ * (∫ t in Ioi (1 / 2 : ℝ), ‖g t‖) +
          ‖c‖ * ‖∫ t in Ioi (1 / 2 : ℝ), g t‖) / (4 : ℝ) ^ n * Real.exp (-5 * r / 2) := by
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have hmode : (0 : ℝ) < Real.exp (-5 * r / 2) := Real.exp_pos _
  have hM0 : (0 : ℝ) ≤ ∫ t in Ioi (1 / 2 : ℝ), ‖g t‖ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun t _ => norm_nonneg _
  have hHead : (0 : ℝ) ≤ 4 * ‖c‖ * C := mul_nonneg (by positivity) hC0
  have hRest : (0 : ℝ) ≤ ‖c‖ * (∫ t in Ioi (1 / 2 : ℝ), ‖g t‖) +
      ‖c‖ * ‖∫ t in Ioi (1 / 2 : ℝ), g t‖ := by
    have h2 : (0 : ℝ) ≤ ‖c‖ * ∫ t in Ioi (1 / 2 : ℝ), ‖g t‖ := mul_nonneg (norm_nonneg _) hM0
    have h3 : (0 : ℝ) ≤ ‖c‖ * ‖∫ t in Ioi (1 / 2 : ℝ), g t‖ := by positivity
    linarith
  rcases le_or_gt ((n : ℝ) * Real.log 2 + r) 0 with hs | hs
  · -- shallow lag: the constraint `r ≤ -n log 2` supplies the missing factor
    have hW := norm_burnolCrossingCorrelationW_le hhead hIoi ((n : ℝ) * Real.log 2 + r)
    have hfac : Real.exp ((n : ℝ) * Real.log 2 / 2) *
        Real.exp (-((n : ℝ) * Real.log 2 + r) / 2) = Real.exp (-r / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h1 : ‖((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
        burnolCrossingCorrelationW g ((n : ℝ) * Real.log 2 + r)‖ ≤
        ‖c‖ * (∫ t in Ioi (1 / 2 : ℝ), ‖g t‖) * Real.exp (-r / 2) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc Real.exp ((n : ℝ) * Real.log 2 / 2) *
            ‖burnolCrossingCorrelationW g ((n : ℝ) * Real.log 2 + r)‖
          ≤ Real.exp ((n : ℝ) * Real.log 2 / 2) *
              (‖c‖ * (∫ t in Ioi (1 / 2 : ℝ), ‖g t‖) *
                Real.exp (-((n : ℝ) * Real.log 2 + r) / 2)) :=
            mul_le_mul_of_nonneg_left hW (le_of_lt (Real.exp_pos _))
        _ = ‖c‖ * (∫ t in Ioi (1 / 2 : ℝ), ‖g t‖) * Real.exp (-r / 2) := by
            rw [show Real.exp ((n : ℝ) * Real.log 2 / 2) *
                (‖c‖ * (∫ t in Ioi (1 / 2 : ℝ), ‖g t‖) *
                  Real.exp (-((n : ℝ) * Real.log 2 + r) / 2)) =
                ‖c‖ * (∫ t in Ioi (1 / 2 : ℝ), ‖g t‖) *
                  (Real.exp ((n : ℝ) * Real.log 2 / 2) *
                    Real.exp (-((n : ℝ) * Real.log 2 + r) / 2)) by ring, hfac]
    have h2 : ‖-c * (starRingEnd ℂ) (∫ t in Ioi (1 / 2 : ℝ), g t) *
        ((Real.exp (-r / 2) : ℝ) : ℂ)‖ =
        ‖c‖ * ‖∫ t in Ioi (1 / 2 : ℝ), g t‖ * Real.exp (-r / 2) := by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_conj, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hD : ‖((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
        burnolCrossingCorrelationW g ((n : ℝ) * Real.log 2 + r) -
        -c * (starRingEnd ℂ) (∫ t in Ioi (1 / 2 : ℝ), g t) *
          ((Real.exp (-r / 2) : ℝ) : ℂ)‖ ≤
        (‖c‖ * (∫ t in Ioi (1 / 2 : ℝ), ‖g t‖) + ‖c‖ * ‖∫ t in Ioi (1 / 2 : ℝ), g t‖) *
          Real.exp (-r / 2) := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [h2]
      nlinarith [h1]
    have hshift : Real.exp (-r / 2) = Real.exp (-5 * r / 2) * Real.exp (2 * r) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hlag : Real.exp (2 * r) * (4 : ℝ) ^ n ≤ 1 := by
      have hle : Real.exp (2 * r) ≤ 1 / (4 : ℝ) ^ n := by
        rw [← burnolExpNegTwoLogTwo n]
        exact Real.exp_le_exp.mpr (by linarith)
      exact (le_div_iff₀ h4pos).mp hle
    refine le_trans hD ?_
    rw [hshift, div_mul_eq_mul_div, le_div_iff₀ h4pos]
    nlinarith [mul_nonneg (mul_nonneg hRest hmode.le) (sub_nonneg.mpr hlag),
      mul_nonneg hHead hmode.le]
  · -- deep lag: the quadratic exterior mass supplies the two extra powers
    have hXge : (1 / 2 : ℝ) ≤ Real.exp ((n : ℝ) * Real.log 2 + r) / 2 := by
      have h := Real.one_le_exp hs.le
      linarith
    have herr := burnolCrossingCorrelation_residue_error hhead hIoi hs
    have hE : Real.exp ((n : ℝ) * Real.log 2 / 2) =
        Real.exp (-r / 2) * Real.exp (((n : ℝ) * Real.log 2 + r) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hDeq : ((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
        burnolCrossingCorrelationW g ((n : ℝ) * Real.log 2 + r) -
        -c * (starRingEnd ℂ) (∫ t in Ioi (1 / 2 : ℝ), g t) * ((Real.exp (-r / 2) : ℝ) : ℂ) =
        ((Real.exp (-r / 2) : ℝ) : ℂ) *
          (c * (starRingEnd ℂ) (∫ t in Ioi (Real.exp ((n : ℝ) * Real.log 2 + r) / 2), g t)) := by
      rw [hE, Complex.ofReal_mul]
      linear_combination ((Real.exp (-r / 2) : ℝ) : ℂ) * herr
    rw [hDeq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      norm_mul, Complex.norm_conj]
    have hmass := hC (Real.exp ((n : ℝ) * Real.log 2 + r) / 2) hXge
    rw [burnolExpQuadraticCut] at hmass
    have hstep : Real.exp (-r / 2) *
        (‖c‖ * ‖∫ t in Ioi (Real.exp ((n : ℝ) * Real.log 2 + r) / 2), g t‖) ≤
        Real.exp (-r / 2) *
          (‖c‖ * (C * (4 * Real.exp (-2 * ((n : ℝ) * Real.log 2 + r))))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass (norm_nonneg _))
        (Real.exp_pos _).le
    have hcomb : Real.exp (-r / 2) * Real.exp (-2 * ((n : ℝ) * Real.log 2 + r)) =
        1 / (4 : ℝ) ^ n * Real.exp (-5 * r / 2) := by
      rw [← Real.exp_add,
        show -r / 2 + -2 * ((n : ℝ) * Real.log 2 + r) = -(2 * (n : ℝ) * Real.log 2) + -5 * r / 2 by
          ring,
        Real.exp_add, burnolExpNegTwoLogTwo]
    have heq : Real.exp (-r / 2) * (‖c‖ * (C * (4 * Real.exp (-2 * ((n : ℝ) * Real.log 2 + r))))) =
        4 * ‖c‖ * C * (1 / (4 : ℝ) ^ n) * Real.exp (-5 * r / 2) := by
      rw [show Real.exp (-r / 2) * (‖c‖ * (C * (4 * Real.exp (-2 * ((n : ℝ) * Real.log 2 + r))))) =
          4 * ‖c‖ * C *
            (Real.exp (-r / 2) * Real.exp (-2 * ((n : ℝ) * Real.log 2 + r))) by ring, hcomb]
      ring
    have hfin : 4 * ‖c‖ * C * (1 / (4 : ℝ) ^ n) * Real.exp (-5 * r / 2) ≤
        (4 * ‖c‖ * C + ‖c‖ * (∫ t in Ioi (1 / 2 : ℝ), ‖g t‖) +
          ‖c‖ * ‖∫ t in Ioi (1 / 2 : ℝ), g t‖) / (4 : ℝ) ^ n * Real.exp (-5 * r / 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ h4pos]
      have hcancel : 4 * ‖c‖ * C * (1 / (4 : ℝ) ^ n) * Real.exp (-5 * r / 2) * (4 : ℝ) ^ n =
          4 * ‖c‖ * C * Real.exp (-5 * r / 2) := by
        field_simp
      rw [hcancel]
      nlinarith [mul_nonneg hRest hmode.le]
    linarith [hstep, heq, hfin]

/-- The constant in the quartic decay of the normalised collar reading. -/
def burnolCollarDepthConstant (g : ℝ → ℂ) (c : ℂ) (C : ℝ) : ℝ :=
  (4 * ‖c‖ * C + ‖c‖ * (∫ t in Ioi (1 / 2 : ℝ), ‖g t‖) +
      ‖c‖ * ‖∫ t in Ioi (1 / 2 : ℝ), g t‖) * burnolCollarModeFiveMass

/-- **The normalised collar reading of a quadratic-tail source is `O(4^{-n})`.** -/
theorem norm_burnolCollarDepthReading_le {g : ℝ → ℂ} {c : ℂ} {C : ℝ}
    (hhead : BurnolApertureHead g c) (hIoi : IntegrableOn g (Ioi (1 / 2 : ℝ)))
    (hC0 : 0 ≤ C) (hC : BurnolQuadraticExteriorMass g C) (n : ℕ) :
    ‖burnolCollarDepthReading g n‖ ≤ burnolCollarDepthConstant g c C / (4 : ℝ) ^ n := by
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have hkcont : Continuous fun r : ℝ => ((burnolCollarKernel 0 r : ℝ) : ℂ) := by
    refine Complex.continuous_ofReal.comp ?_
    unfold burnolCollarKernel burnolCollarZ
    fun_prop
  have hWcont : Continuous (burnolCrossingCorrelationW g) :=
    continuous_burnolCrossingCorrelationW hhead hIoi
  have hFint : Integrable (fun r : ℝ => ((burnolCollarKernel 0 r : ℝ) : ℂ) *
      (((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
        burnolCrossingCorrelationW g ((n : ℝ) * Real.log 2 + r))) := by
    refine MeasureTheory.Integrable.mono'
      (g := fun r : ℝ => ‖c‖ * (∫ t in Ioi (1 / 2 : ℝ), ‖g t‖) *
        |burnolCollarKernel 0 r * Real.exp (-r / 2)|) ?_ ?_ ?_
    · have h := burnolIntegrable_collarKernel_mul_mode.norm
      simpa only [Real.norm_eq_abs] using h.const_mul (‖c‖ * ∫ t in Ioi (1 / 2 : ℝ), ‖g t‖)
    · exact (hkcont.mul (continuous_const.mul
        (hWcont.comp (continuous_const.add continuous_id)))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun r => norm_burnolCollarDepthProfile_le hhead hIoi n r
  have hGcongr : (fun r : ℝ => ((burnolCollarKernel 0 r : ℝ) : ℂ) *
      (-c * (starRingEnd ℂ) (∫ t in Ioi (1 / 2 : ℝ), g t) *
        ((Real.exp (-r / 2) : ℝ) : ℂ))) =
      fun r : ℝ => -c * (starRingEnd ℂ) (∫ t in Ioi (1 / 2 : ℝ), g t) *
        ((burnolCollarKernel 0 r * Real.exp (-r / 2) : ℝ) : ℂ) := by
    funext r
    push_cast
    ring
  have hGint : Integrable (fun r : ℝ => ((burnolCollarKernel 0 r : ℝ) : ℂ) *
      (-c * (starRingEnd ℂ) (∫ t in Ioi (1 / 2 : ℝ), g t) *
        ((Real.exp (-r / 2) : ℝ) : ℂ))) := by
    rw [hGcongr]
    exact (burnolIntegrable_collarKernel_mul_mode.ofReal).const_mul _
  have hGzero : (∫ r : ℝ, ((burnolCollarKernel 0 r : ℝ) : ℂ) *
      (-c * (starRingEnd ℂ) (∫ t in Ioi (1 / 2 : ℝ), g t) *
        ((Real.exp (-r / 2) : ℝ) : ℂ))) = 0 := by
    rw [hGcongr, MeasureTheory.integral_const_mul, integral_complex_ofReal,
      integral_burnolCollarKernel_mul_mode]
    norm_num
  have hdiff : burnolCollarDepthReading g n =
      ∫ r : ℝ, (((burnolCollarKernel 0 r : ℝ) : ℂ) *
          (((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
            burnolCrossingCorrelationW g ((n : ℝ) * Real.log 2 + r)) -
        ((burnolCollarKernel 0 r : ℝ) : ℂ) *
          (-c * (starRingEnd ℂ) (∫ t in Ioi (1 / 2 : ℝ), g t) *
            ((Real.exp (-r / 2) : ℝ) : ℂ))) := by
    rw [MeasureTheory.integral_sub hFint hGint, hGzero, sub_zero, burnolCollarDepthReading]
  have hpt : ∀ r : ℝ, ‖((burnolCollarKernel 0 r : ℝ) : ℂ) *
      (((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
        burnolCrossingCorrelationW g ((n : ℝ) * Real.log 2 + r)) -
      ((burnolCollarKernel 0 r : ℝ) : ℂ) *
        (-c * (starRingEnd ℂ) (∫ t in Ioi (1 / 2 : ℝ), g t) *
          ((Real.exp (-r / 2) : ℝ) : ℂ))‖ ≤
      (4 * ‖c‖ * C + ‖c‖ * (∫ t in Ioi (1 / 2 : ℝ), ‖g t‖) +
          ‖c‖ * ‖∫ t in Ioi (1 / 2 : ℝ), g t‖) / (4 : ℝ) ^ n *
        (|burnolCollarKernel 0 r| * Real.exp (-5 * r / 2)) := by
    intro r
    have hfactor : ((burnolCollarKernel 0 r : ℝ) : ℂ) *
        (((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
          burnolCrossingCorrelationW g ((n : ℝ) * Real.log 2 + r)) -
        ((burnolCollarKernel 0 r : ℝ) : ℂ) *
          (-c * (starRingEnd ℂ) (∫ t in Ioi (1 / 2 : ℝ), g t) *
            ((Real.exp (-r / 2) : ℝ) : ℂ)) =
        ((burnolCollarKernel 0 r : ℝ) : ℂ) *
          (((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
              burnolCrossingCorrelationW g ((n : ℝ) * Real.log 2 + r) -
            -c * (starRingEnd ℂ) (∫ t in Ioi (1 / 2 : ℝ), g t) *
              ((Real.exp (-r / 2) : ℝ) : ℂ)) := by ring
    rw [hfactor, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |burnolCollarKernel 0 r| *
          ‖((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
              burnolCrossingCorrelationW g ((n : ℝ) * Real.log 2 + r) -
            -c * (starRingEnd ℂ) (∫ t in Ioi (1 / 2 : ℝ), g t) *
              ((Real.exp (-r / 2) : ℝ) : ℂ)‖
        ≤ |burnolCollarKernel 0 r| *
            ((4 * ‖c‖ * C + ‖c‖ * (∫ t in Ioi (1 / 2 : ℝ), ‖g t‖) +
                ‖c‖ * ‖∫ t in Ioi (1 / 2 : ℝ), g t‖) / (4 : ℝ) ^ n *
              Real.exp (-5 * r / 2)) :=
          mul_le_mul_of_nonneg_left
            (norm_burnolDepthProfileError_le hhead hIoi hC0 hC n r) (abs_nonneg _)
      _ = (4 * ‖c‖ * C + ‖c‖ * (∫ t in Ioi (1 / 2 : ℝ), ‖g t‖) +
              ‖c‖ * ‖∫ t in Ioi (1 / 2 : ℝ), g t‖) / (4 : ℝ) ^ n *
            (|burnolCollarKernel 0 r| * Real.exp (-5 * r / 2)) := by ring
  have hmaj : Integrable (fun r : ℝ =>
      (4 * ‖c‖ * C + ‖c‖ * (∫ t in Ioi (1 / 2 : ℝ), ‖g t‖) +
          ‖c‖ * ‖∫ t in Ioi (1 / 2 : ℝ), g t‖) / (4 : ℝ) ^ n *
        (|burnolCollarKernel 0 r| * Real.exp (-5 * r / 2))) :=
    burnolIntegrable_collarModeFive.const_mul _
  have hcmp := MeasureTheory.norm_integral_le_of_norm_le hmaj
    (Filter.Eventually.of_forall hpt)
  rw [MeasureTheory.integral_const_mul, ← burnolCollarModeFiveMass] at hcmp
  rw [hdiff]
  refine le_trans hcmp (le_of_eq ?_)
  rw [burnolCollarDepthConstant]
  ring

/-! ## The raw depth pairing -/

theorem burnolCollarDepthReading_eq (g : ℝ → ℂ) (n : ℕ) :
    burnolCollarDepthReading g n = ((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
      ∫ r : ℝ, ((burnolCollarKernel 0 r : ℝ) : ℂ) *
        burnolCrossingCorrelationW g ((n : ℝ) * Real.log 2 + r) := by
  rw [burnolCollarDepthReading, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with r
  ring

/-- **The raw collar depth pairing is `O(8^{-n})`.**  Both the normalisation of the reading and the
depth weight of the kernel contribute a factor `2^{-n/2}`. -/
theorem norm_burnolDepthPairing_le {g : ℝ → ℂ} {c : ℂ} {C : ℝ}
    (hhead : BurnolApertureHead g c) (hIoi : IntegrableOn g (Ioi (1 / 2 : ℝ)))
    (hC0 : 0 ≤ C) (hC : BurnolQuadraticExteriorMass g C) (n : ℕ) :
    ‖∫ s : ℝ, ((burnolCollarKernel n s : ℝ) : ℂ) * burnolCrossingCorrelationW g s‖ ≤
      burnolCollarDepthConstant g c C / (8 : ℝ) ^ n := by
  have hexp : Real.exp ((n : ℝ) * Real.log 2 / 2) = (2 : ℝ) ^ ((n : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hpow : (2 : ℝ) ^ (-(n : ℝ) / 2) * (2 : ℝ) ^ ((n : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), show -(n : ℝ) / 2 + (n : ℝ) / 2 = 0 by ring,
      Real.rpow_zero]
  have hpowC : (((2 : ℝ) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) * (((2 : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hpow, Complex.ofReal_one]
  have hsq : (2 : ℝ) ^ (-(n : ℝ) / 2) * (2 : ℝ) ^ (-(n : ℝ) / 2) = 1 / (2 : ℝ) ^ n := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      show -(n : ℝ) / 2 + -(n : ℝ) / 2 = -(n : ℝ) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, one_div]
  have hkey : (∫ s : ℝ, ((burnolCollarKernel n s : ℝ) : ℂ) * burnolCrossingCorrelationW g s) =
      (((2 : ℝ) ^ (-(n : ℝ) / 2) * (2 : ℝ) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
        burnolCollarDepthReading g n := by
    rw [burnolDepthPairing_translate, burnolCollarDepthReading_eq, hexp, Complex.ofReal_mul]
    linear_combination (-((((2 : ℝ) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
      ∫ r : ℝ, ((burnolCollarKernel 0 r : ℝ) : ℂ) *
        burnolCrossingCorrelationW g ((n : ℝ) * Real.log 2 + r))) * hpowC
  rw [hkey, norm_mul, Complex.norm_real, Real.norm_eq_abs, hsq,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 : ℝ) ^ n)]
  calc 1 / (2 : ℝ) ^ n * ‖burnolCollarDepthReading g n‖
      ≤ 1 / (2 : ℝ) ^ n * (burnolCollarDepthConstant g c C / (4 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left (norm_burnolCollarDepthReading_le hhead hIoi hC0 hC n)
          (by positivity)
    _ = burnolCollarDepthConstant g c C / (8 : ℝ) ^ n := by
        rw [show (8 : ℝ) ^ n = (2 : ℝ) ^ n * (4 : ℝ) ^ n by rw [← mul_pow]; norm_num]
        field_simp

/-! ## The zero-divided source -/

theorem xiDivisor_burnolQuadraticExteriorMass {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    BurnolQuadraticExteriorMass (burnolZeroDividedSource ρ) (burnolTailMassConstant ρ) :=
  fun _ hX => norm_integral_burnolZeroDividedSource_Ioi_le hρ0 hρ1 (by linarith)

/-- **The normalised collar reading of the zero-divided source is `O(4^{-n})`.** -/
theorem xiDivisor_norm_burnolCollarDepthReading_le {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) (n : ℕ) :
    ‖burnolCollarDepthReading (burnolZeroDividedSource ρ) n‖ ≤
      burnolCollarDepthConstant (burnolZeroDividedSource ρ) (burnolFirstWallHead ρ)
        (burnolTailMassConstant ρ) / (4 : ℝ) ^ n :=
  norm_burnolCollarDepthReading_le
    (xiDivisor_burnolZeroDividedSource_apertureHead hρ0 hρ1 hxi)
    (integrableOn_burnolZeroDividedSource_Ioi hρ0 hρ1 (by norm_num))
    (burnolTailMassConstant_nonneg (by linarith))
    (xiDivisor_burnolQuadraticExteriorMass hρ0 hρ1) n

/-- **The completed collar depth pairing of the zero-divided source is `O(8^{-n})`** — three
geometric orders below the raw depth weight. -/
theorem xiDivisor_norm_burnolDepthPairing_le {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) (n : ℕ) :
    ‖∫ s : ℝ, ((burnolCollarKernel n s : ℝ) : ℂ) *
        burnolCrossingCorrelationW (burnolZeroDividedSource ρ) s‖ ≤
      burnolCollarDepthConstant (burnolZeroDividedSource ρ) (burnolFirstWallHead ρ)
        (burnolTailMassConstant ρ) / (8 : ℝ) ^ n :=
  norm_burnolDepthPairing_le
    (xiDivisor_burnolZeroDividedSource_apertureHead hρ0 hρ1 hxi)
    (integrableOn_burnolZeroDividedSource_Ioi hρ0 hρ1 (by norm_num))
    (burnolTailMassConstant_nonneg (by linarith))
    (xiDivisor_burnolQuadraticExteriorMass hρ0 hρ1) n

end RHTower
