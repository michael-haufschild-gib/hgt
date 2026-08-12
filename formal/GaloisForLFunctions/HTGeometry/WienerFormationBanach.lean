import GaloisForLFunctions.HTGeometry.WienerFormationScale

/-!
# The Wiener receiver as a unital Banach algebra

For a positive radius `R` the admitted packets form a commutative unital `ℂ`-algebra `W_R`.  The
Wiener norm makes it a normed algebra with submultiplicative norm, and the weight isometry
`f ↦ (a_n R^n)` identifies it with `ℓ¹(ℕ)` as a metric space, so `W_R` is complete.
-/

namespace HTGeometry

open PowerSeries

/-- The Wiener receiver algebra `W_R` of positive radius `R`. -/
def WienerAlgebra (R : ℝ) [hR : Fact (0 < R)] : Type :=
  ↥(wienerScaleAlgebra hR.out.le)

namespace WienerAlgebra

variable {R : ℝ} [hR : Fact (0 < R)]

instance : CommRing (WienerAlgebra R) :=
  inferInstanceAs (CommRing ↥(wienerScaleAlgebra hR.out.le))

instance : Algebra ℂ (WienerAlgebra R) :=
  inferInstanceAs (Algebra ℂ ↥(wienerScaleAlgebra hR.out.le))

/-- The underlying formal packet of a Wiener element. -/
def toSeries (f : WienerAlgebra R) : PowerSeries ℂ := f.1

theorem admissible (f : WienerAlgebra R) : WienerScaleAdmissible R f.toSeries := f.2

theorem toSeries_injective : Function.Injective (toSeries (R := R)) := fun _ _ h => Subtype.ext h

theorem toSeries_zero : (0 : WienerAlgebra R).toSeries = 0 := rfl

theorem toSeries_one : (1 : WienerAlgebra R).toSeries = 1 := rfl

theorem toSeries_add (f g : WienerAlgebra R) : (f + g).toSeries = f.toSeries + g.toSeries := rfl

theorem toSeries_neg (f : WienerAlgebra R) : (-f).toSeries = -f.toSeries := rfl

theorem toSeries_sub (f g : WienerAlgebra R) : (f - g).toSeries = f.toSeries - g.toSeries := rfl

theorem toSeries_mul (f g : WienerAlgebra R) : (f * g).toSeries = f.toSeries * g.toSeries := rfl

theorem toSeries_smul (c : ℂ) (f : WienerAlgebra R) : (c • f).toSeries = c • f.toSeries := rfl

/-! ## The Wiener norm -/

/-- The Wiener norm as an additive group norm on `W_R`. -/
noncomputable def groupNorm (R : ℝ) [hR : Fact (0 < R)] : AddGroupNorm (WienerAlgebra R) where
  toFun f := wienerScaleNorm R f.toSeries
  map_zero' := by
    show wienerScaleNorm R (0 : WienerAlgebra R).toSeries = 0
    rw [toSeries_zero, wienerScaleNorm_zero]
  add_le' f g := by
    show wienerScaleNorm R (f + g).toSeries ≤ wienerScaleNorm R f.toSeries
      + wienerScaleNorm R g.toSeries
    rw [toSeries_add]
    exact wienerScaleNorm_add_le hR.out.le f.admissible g.admissible
  neg' f := by
    show wienerScaleNorm R (-f).toSeries = wienerScaleNorm R f.toSeries
    rw [toSeries_neg, wienerScaleNorm_neg]
  eq_zero_of_map_eq_zero' f h := by
    have hzero : ∀ n, wienerScaleWeight R f.toSeries n = 0 := by
      intro n
      have hle : wienerScaleWeight R f.toSeries n ≤ wienerScaleNorm R f.toSeries :=
        f.admissible.le_tsum n fun j _ => wienerScaleWeight_nonneg hR.out.le _ j
      have hge : 0 ≤ wienerScaleWeight R f.toSeries n :=
        wienerScaleWeight_nonneg hR.out.le _ n
      have : wienerScaleWeight R f.toSeries n ≤ 0 := by
        rw [← h]
        exact hle
      linarith
    refine toSeries_injective ?_
    rw [toSeries_zero]
    ext n
    have hn := hzero n
    rw [wienerScaleWeight, mul_eq_zero] at hn
    rcases hn with hn | hn
    · rw [norm_eq_zero] at hn
      simp [hn]
    · exact absurd hn (pow_ne_zero n hR.out.ne')

noncomputable instance : NormedAddCommGroup (WienerAlgebra R) :=
  (groupNorm R).toNormedAddCommGroup

theorem norm_def (f : WienerAlgebra R) : ‖f‖ = wienerScaleNorm R f.toSeries := rfl

noncomputable instance : NormedCommRing (WienerAlgebra R) :=
  { (inferInstance : CommRing (WienerAlgebra R)),
    (inferInstance : NormedAddCommGroup (WienerAlgebra R)) with
    norm_mul_le := fun f g => by
      rw [norm_def, norm_def, norm_def, toSeries_mul]
      exact wienerScaleNorm_mul_le hR.out.le f.admissible g.admissible }

noncomputable instance : NormedAlgebra ℂ (WienerAlgebra R) :=
  { (inferInstance : Algebra ℂ (WienerAlgebra R)) with
    norm_smul_le := fun c f => by
      rw [norm_def, toSeries_smul, wienerScaleNorm_smul, norm_def] }

/-- The unit of `W_R` has norm one. -/
theorem norm_one_eq : ‖(1 : WienerAlgebra R)‖ = 1 := by
  rw [norm_def, toSeries_one, wienerScaleNorm_one]

/-! ## Completeness through the weight isometry -/

/-- The weight coordinates of an admitted packet. -/
noncomputable def weightCoord (f : WienerAlgebra R) (n : ℕ) : ℂ :=
  (PowerSeries.coeff n) f.toSeries * (R : ℂ) ^ n

theorem norm_weightCoord (f : WienerAlgebra R) (n : ℕ) :
    ‖weightCoord f n‖ = wienerScaleWeight R f.toSeries n := by
  rw [weightCoord, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hR.out, wienerScaleWeight]

theorem memLp_weightCoord (f : WienerAlgebra R) : Memℓp (weightCoord f) 1 := by
  rw [memℓp_gen_iff (by norm_num)]
  have h : (fun n => ‖weightCoord f n‖ ^ (1 : ℝ≥0∞).toReal)
      = wienerScaleWeight R f.toSeries := by
    funext n
    rw [norm_weightCoord]
    simp
  rw [h]
  exact f.admissible

/-- The weight isometry into `ℓ¹`. -/
noncomputable def toLp (f : WienerAlgebra R) : lp (fun _ : ℕ => ℂ) 1 :=
  ⟨weightCoord f, memLp_weightCoord f⟩

theorem coe_toLp (f : WienerAlgebra R) : ((toLp f : lp (fun _ : ℕ => ℂ) 1) : ℕ → ℂ)
    = weightCoord f := rfl

theorem norm_toLp (f : WienerAlgebra R) : ‖toLp f‖ = ‖f‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), norm_def, wienerScaleNorm]
  have h : (fun n => ‖((toLp f : lp (fun _ : ℕ => ℂ) 1) : ℕ → ℂ) n‖ ^ (1 : ℝ≥0∞).toReal)
      = wienerScaleWeight R f.toSeries := by
    funext n
    rw [coe_toLp, norm_weightCoord]
    simp
  rw [h]
  simp

theorem toLp_sub (f g : WienerAlgebra R) : toLp (f - g) = toLp f - toLp g := by
  refine lp.ext ?_
  funext n
  rw [lp.coeFn_sub]
  simp only [Pi.sub_apply, coe_toLp, weightCoord, toSeries_sub, map_sub]
  ring

/-- The inverse of the weight isometry. -/
noncomputable def ofLpSeries (g : lp (fun _ : ℕ => ℂ) 1) : PowerSeries ℂ :=
  PowerSeries.mk fun n => (g : ℕ → ℂ) n / (R : ℂ) ^ n

theorem admissible_ofLpSeries (g : lp (fun _ : ℕ => ℂ) 1) :
    WienerScaleAdmissible R (ofLpSeries (R := R) g) := by
  have hRne : ((R : ℂ)) ^ 0 ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr hR.out.ne')
  have hsum : Summable fun n => ‖(g : ℕ → ℂ) n‖ ^ (1 : ℝ≥0∞).toReal :=
    (memℓp_gen_iff (by norm_num)).mp g.2
  have h : wienerScaleWeight R (ofLpSeries (R := R) g) = fun n => ‖(g : ℕ → ℂ) n‖ := by
    funext n
    have hpow : ((R : ℂ)) ^ n ≠ 0 := pow_ne_zero n (Complex.ofReal_ne_zero.mpr hR.out.ne')
    rw [wienerScaleWeight, ofLpSeries, PowerSeries.coeff_mk, norm_div, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR.out, div_mul_cancel₀]
    exact pow_ne_zero n hR.out.ne'
  rw [WienerScaleAdmissible, h]
  simpa using hsum

/-- The inverse of the weight isometry as a Wiener element. -/
noncomputable def ofLp (g : lp (fun _ : ℕ => ℂ) 1) : WienerAlgebra R :=
  ⟨ofLpSeries (R := R) g, admissible_ofLpSeries g⟩

theorem toSeries_ofLp (g : lp (fun _ : ℕ => ℂ) 1) :
    (ofLp (R := R) g).toSeries = ofLpSeries (R := R) g := rfl

theorem ofLp_toLp (f : WienerAlgebra R) : ofLp (toLp f) = f := by
  refine toSeries_injective ?_
  rw [toSeries_ofLp]
  ext n
  rw [ofLpSeries, PowerSeries.coeff_mk, coe_toLp, weightCoord,
    mul_div_cancel_right₀]
  exact pow_ne_zero n (Complex.ofReal_ne_zero.mpr hR.out.ne')

theorem toLp_ofLp (g : lp (fun _ : ℕ => ℂ) 1) : toLp (ofLp (R := R) g) = g := by
  refine lp.ext ?_
  funext n
  rw [coe_toLp, weightCoord, toSeries_ofLp, ofLpSeries, PowerSeries.coeff_mk,
    div_mul_cancel₀]
  exact pow_ne_zero n (Complex.ofReal_ne_zero.mpr hR.out.ne')

/-- **The weight isometry.**  `W_R` and `ℓ¹(ℕ)` are isometric. -/
noncomputable def isometryLp (R : ℝ) [hR : Fact (0 < R)] :
    WienerAlgebra R ≃ᵢ lp (fun _ : ℕ => ℂ) 1 where
  toFun := toLp
  invFun := ofLp
  left_inv := ofLp_toLp
  right_inv := toLp_ofLp
  isometry_toFun := by
    refine Isometry.of_dist_eq fun f g => ?_
    rw [dist_eq_norm, dist_eq_norm, toLp_sub, norm_toLp]

/-- **`W_R` is a Banach algebra.** -/
instance : CompleteSpace (WienerAlgebra R) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_refl _⟩
  exact (isometryLp R).completeSpace_iff.mpr inferInstance

end WienerAlgebra

end HTGeometry
