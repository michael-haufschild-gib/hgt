import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspWignerPairLogScaleWeight

/-!
# The centre-weighted theta Wigner pair current

The exponential chart is an integrability equivalence as well as an identity, so both the
exponentially weighted and the log-scale-weighted pair currents converge.  Since
`log (2π n m e^(2u)) = log (2π n m) + 2u`, the linear centre weight `u` is half the difference of
the two, and the centre-weighted current is

```text
∫ u e^((2σ-1)u) Φ_n(u+t) Φ_m(u-t) du
  = (4 (2πnm)^σ)⁻¹ (cosh w)^(-(σ+2)) (LogWeight σ (cosh w) - log(2πnm) Γ(σ+2) Q σ (cosh w)) ,
```

`w = 2t + log n - log m`.  The coefficient `log (2π n m)` is the only place where the indices
occur outside a Dirichlet factor, so this is the first weight whose sum over `n` and `m` cannot
factor through a single Dirichlet series.
-/

open Real MeasureTheory Set

namespace RHTower

noncomputable section

theorem integrableOn_rpow_mul_iff_integrable_exp_chart {σ P : ℝ} (hP : 0 < P) (F : ℝ → ℝ) :
    IntegrableOn (fun z : ℝ => z ^ (σ - 1) * F z) (Ioi 0) ↔
      Integrable (fun u : ℝ => Real.exp (2 * σ * u) * F (P * Real.exp (2 * u))) := by
  have hPs : Real.exp (σ * Real.log P) = P ^ σ := by
    rw [Real.rpow_def_of_pos hP, mul_comm]
  have hPpow : (P : ℝ) ^ σ ≠ 0 := (Real.rpow_pos_of_pos hP σ).ne'
  -- the exponential chart
  have hchart := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (f := Real.exp) (f' := Real.exp) (s := (univ : Set ℝ)) MeasurableSet.univ
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    (Real.exp_injective.injOn) (fun z : ℝ => z ^ (σ - 1) * F z)
  rw [Set.image_univ, Real.range_exp, MeasureTheory.integrableOn_univ] at hchart
  have hfun : (fun t : ℝ => |Real.exp t| • ((Real.exp t) ^ (σ - 1) * F (Real.exp t)))
      = fun t : ℝ => Real.exp (σ * t) * F (Real.exp t) := by
    funext t
    rw [smul_eq_mul, abs_of_pos (Real.exp_pos t), ← mul_assoc,
      Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp, ← Real.exp_add,
      show t + t * (σ - 1) = σ * t by ring]
  rw [hfun] at hchart
  rw [hchart]
  -- translate by log P
  have htrans : Integrable (fun t : ℝ => Real.exp (σ * t) * F (Real.exp t)) ↔
      Integrable (fun s : ℝ => Real.exp (σ * (s + Real.log P)) * F (Real.exp (s + Real.log P))) := by
    refine ((measurePreserving_add_right (volume : Measure ℝ) (Real.log P)).integrable_comp_emb
      (measurableEmbedding_addRight (Real.log P))).symm
  rw [htrans]
  have hpt : (fun s : ℝ => Real.exp (σ * (s + Real.log P)) * F (Real.exp (s + Real.log P)))
      = fun s : ℝ => P ^ σ * (Real.exp (σ * s) * F (P * Real.exp s)) := by
    funext s
    have h1 : Real.exp (s + Real.log P) = P * Real.exp s := by
      rw [Real.exp_add, Real.exp_log hP, mul_comm]
    have h2 : Real.exp (σ * (s + Real.log P)) = P ^ σ * Real.exp (σ * s) := by
      rw [mul_add, Real.exp_add, hPs, mul_comm]
    rw [h1, h2]; ring
  rw [hpt, integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hPpow)]
  -- rescale by two
  have hscale := MeasureTheory.integrable_comp_mul_left_iff
    (fun s : ℝ => Real.exp (σ * s) * F (P * Real.exp s)) (R := (2 : ℝ)) (by norm_num)
  rw [← hscale]
  constructor <;> intro h <;>
    · refine h.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only []
      rw [show σ * (2 * u) = 2 * σ * u by ring]

/-! ## Integrability of the two pair currents -/

theorem integrableOn_rpow_mul_thetaCuspWignerRadialProfile {σ : ℝ} (hσ : 0 < σ) (v : ℝ) :
    IntegrableOn (fun s : ℝ => s ^ (σ - 1) * thetaCuspWignerRadialProfile s v) (Ioi 0) := by
  set C : ℝ := Real.cosh (2 * v) with hCdef
  have hC : (0 : ℝ) < C := Real.cosh_pos _
  have i4 : IntegrableOn (fun s : ℝ => s ^ (σ + 3) * Real.exp (-(C * s))) (Ioi 0) :=
    GaloisForLFunctions.HTGeometry.integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) hC
  have i3 : IntegrableOn (fun s : ℝ => s ^ (σ + 2) * Real.exp (-(C * s))) (Ioi 0) :=
    GaloisForLFunctions.HTGeometry.integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) hC
  have i2 : IntegrableOn (fun s : ℝ => s ^ (σ + 1) * Real.exp (-(C * s))) (Ioi 0) :=
    GaloisForLFunctions.HTGeometry.integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) hC
  refine ((i4.sub (i3.const_mul (6 * C))).add (i2.const_mul 9)).congr_fun
    (fun s hs => ?_) measurableSet_Ioi
  have hs0 : (0 : ℝ) < s := hs
  have e4 : s ^ (σ - 1) * (s ^ (4 : ℕ)) = s ^ (σ + 3) := by
    rw [← Real.rpow_natCast s 4, ← Real.rpow_add hs0]; congr 1; norm_num; ring
  have e3 : s ^ (σ - 1) * (s ^ (3 : ℕ)) = s ^ (σ + 2) := by
    rw [← Real.rpow_natCast s 3, ← Real.rpow_add hs0]; congr 1; norm_num; ring
  have e2 : s ^ (σ - 1) * (s ^ (2 : ℕ)) = s ^ (σ + 1) := by
    rw [← Real.rpow_natCast s 2, ← Real.rpow_add hs0]; congr 1; norm_num; ring
  show s ^ (σ + 3) * Real.exp (-(C * s)) - 6 * C * (s ^ (σ + 2) * Real.exp (-(C * s))) +
      9 * (s ^ (σ + 1) * Real.exp (-(C * s))) =
    s ^ (σ - 1) * thetaCuspWignerRadialProfile s v
  unfold thetaCuspWignerRadialProfile
  rw [← hCdef, show -s * C = -(C * s) by ring]
  linear_combination (-(Real.exp (-(C * s)))) * e4 + 6 * C * (Real.exp (-(C * s))) * e3 -
    9 * (Real.exp (-(C * s))) * e2

theorem integrableOn_rpow_mul_log_mul_thetaCuspWignerRadialProfile {σ : ℝ} (hσ : 0 < σ) (v : ℝ) :
    IntegrableOn
      (fun s : ℝ => s ^ (σ - 1) * (Real.log s * thetaCuspWignerRadialProfile s v)) (Ioi 0) := by
  set C : ℝ := Real.cosh (2 * v) with hCdef
  have hC : (0 : ℝ) < C := Real.cosh_pos _
  have i4 := integrableOn_rpow_mul_log_mul_exp_neg_mul_Ioi (a := σ + 4) (by linarith) hC
  have i3 := integrableOn_rpow_mul_log_mul_exp_neg_mul_Ioi (a := σ + 3) (by linarith) hC
  have i2 := integrableOn_rpow_mul_log_mul_exp_neg_mul_Ioi (a := σ + 2) (by linarith) hC
  refine ((i4.sub (i3.const_mul (6 * C))).add (i2.const_mul 9)).congr_fun
    (fun s hs => ?_) measurableSet_Ioi
  have hs0 : (0 : ℝ) < s := hs
  have e4 : s ^ (σ - 1) * (s ^ (4 : ℕ)) = s ^ (σ + 4 - 1) := by
    rw [← Real.rpow_natCast s 4, ← Real.rpow_add hs0]; congr 1; norm_num; ring
  have e3 : s ^ (σ - 1) * (s ^ (3 : ℕ)) = s ^ (σ + 3 - 1) := by
    rw [← Real.rpow_natCast s 3, ← Real.rpow_add hs0]; congr 1; norm_num; ring
  have e2 : s ^ (σ - 1) * (s ^ (2 : ℕ)) = s ^ (σ + 2 - 1) := by
    rw [← Real.rpow_natCast s 2, ← Real.rpow_add hs0]; congr 1; norm_num; ring
  show s ^ (σ + 4 - 1) * Real.log s * Real.exp (-(C * s)) -
      6 * C * (s ^ (σ + 3 - 1) * Real.log s * Real.exp (-(C * s))) +
      9 * (s ^ (σ + 2 - 1) * Real.log s * Real.exp (-(C * s))) =
    s ^ (σ - 1) * (Real.log s * thetaCuspWignerRadialProfile s v)
  unfold thetaCuspWignerRadialProfile
  rw [← hCdef, show -s * C = -(C * s) by ring]
  linear_combination (-(Real.log s * Real.exp (-(C * s)))) * e4 +
    6 * C * (Real.log s * Real.exp (-(C * s))) * e3 -
      9 * (Real.log s * Real.exp (-(C * s))) * e2

/-! ## The two pair currents are integrable -/

theorem integrable_exp_mul_thetaCuspSourceTerm_pair {σ : ℝ} (hσ : 0 < σ)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (t : ℝ) :
    Integrable (fun u : ℝ => Real.exp ((2 * σ - 1) * u) *
      (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hP : (0 : ℝ) < 2 * Real.pi * n * m := by positivity
  set w : ℝ := thetaCuspWignerAtomCenteredCoordinate n m t with hw
  have h := (integrableOn_rpow_mul_iff_integrable_exp_chart (σ := σ) hP
    (fun z => thetaCuspWignerRadialProfile z w)).mp
    (integrableOn_rpow_mul_thetaCuspWignerRadialProfile hσ w)
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  show Real.exp (2 * σ * u) *
      thetaCuspWignerRadialProfile (2 * Real.pi * n * m * Real.exp (2 * u)) w =
    Real.exp ((2 * σ - 1) * u) *
      (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)
  rw [thetaCuspSourceTerm_mul_reflect_eq_wignerRadialProfile hn hm u t,
    thetaCuspWignerAtomScale, ← hw, ← mul_assoc, ← Real.exp_add,
    show (2 * σ - 1) * u + u = 2 * σ * u by ring]

theorem log_thetaCuspWignerAtomScale {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (u : ℝ) :
    Real.log (thetaCuspWignerAtomScale n m u) =
      Real.log (2 * Real.pi * n * m) + 2 * u := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hP : (0 : ℝ) < 2 * Real.pi * n * m := by positivity
  rw [thetaCuspWignerAtomScale, Real.log_mul hP.ne' (Real.exp_ne_zero _), Real.log_exp]

theorem integrable_log_scale_mul_exp_mul_thetaCuspSourceTerm_pair {σ : ℝ} (hσ : 0 < σ)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (t : ℝ) :
    Integrable (fun u : ℝ =>
      Real.log (thetaCuspWignerAtomScale n m u) * Real.exp ((2 * σ - 1) * u) *
        (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hP : (0 : ℝ) < 2 * Real.pi * n * m := by positivity
  set w : ℝ := thetaCuspWignerAtomCenteredCoordinate n m t with hw
  have h := (integrableOn_rpow_mul_iff_integrable_exp_chart (σ := σ) hP
    (fun z => Real.log z * thetaCuspWignerRadialProfile z w)).mp
    (integrableOn_rpow_mul_log_mul_thetaCuspWignerRadialProfile hσ w)
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  show Real.exp (2 * σ * u) *
      (Real.log (2 * Real.pi * n * m * Real.exp (2 * u)) *
        thetaCuspWignerRadialProfile (2 * Real.pi * n * m * Real.exp (2 * u)) w) =
    Real.log (thetaCuspWignerAtomScale n m u) * Real.exp ((2 * σ - 1) * u) *
      (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)
  rw [thetaCuspSourceTerm_mul_reflect_eq_wignerRadialProfile hn hm u t,
    thetaCuspWignerAtomScale, ← hw]
  rw [show Real.log (2 * Real.pi * n * m * Real.exp (2 * u)) * Real.exp ((2 * σ - 1) * u) *
      (Real.exp u * thetaCuspWignerRadialProfile (2 * Real.pi * n * m * Real.exp (2 * u)) w) =
    (Real.exp ((2 * σ - 1) * u) * Real.exp u) *
      (Real.log (2 * Real.pi * n * m * Real.exp (2 * u)) *
        thetaCuspWignerRadialProfile (2 * Real.pi * n * m * Real.exp (2 * u)) w) by ring,
    ← Real.exp_add, show (2 * σ - 1) * u + u = 2 * σ * u by ring]

/-! ## The centre-weighted pair current -/

/-- **Exact centre-weighted center integral of an ordered theta source pair.**  The linear centre
weight splits the log-scale weight from a multiple of the exponential weight; the multiple is
`log (2π n m)`, which is the only place where the indices appear outside a Dirichlet factor. -/
theorem integral_center_mul_exp_mul_thetaCuspSourceTerm_pair {σ : ℝ} (hσ : 0 < σ)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (t : ℝ) :
    (∫ u : ℝ, u * Real.exp ((2 * σ - 1) * u) *
        (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) =
      1 / (4 * (2 * Real.pi * n * m) ^ σ) *
        ((1 / Real.cosh (2 * t + Real.log n - Real.log m)) ^ (σ + 2) *
          (thetaCuspWignerRadialLogWeight σ
              (Real.cosh (2 * t + Real.log n - Real.log m)) -
            Real.log (2 * Real.pi * n * m) * Real.Gamma (σ + 2) *
              thetaCuspWignerRadialQ σ
                (Real.cosh (2 * t + Real.log n - Real.log m)))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hP : (0 : ℝ) < 2 * Real.pi * n * m := by positivity
  have hPpow : (0 : ℝ) < (2 * Real.pi * n * m) ^ σ := Real.rpow_pos_of_pos hP _
  have hI1 := integrable_log_scale_mul_exp_mul_thetaCuspSourceTerm_pair hσ hn hm t
  have hI2 := integrable_exp_mul_thetaCuspSourceTerm_pair hσ hn hm t
  have hpt : ∀ u : ℝ, u * Real.exp ((2 * σ - 1) * u) *
      (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m) =
      (1 / 2) * (Real.log (thetaCuspWignerAtomScale n m u) * Real.exp ((2 * σ - 1) * u) *
          (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) -
        (Real.log (2 * Real.pi * n * m) / 2) * (Real.exp ((2 * σ - 1) * u) *
          (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) := by
    intro u
    rw [log_thetaCuspWignerAtomScale hn hm u]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_sub (hI1.const_mul _) (hI2.const_mul _), integral_const_mul, integral_const_mul,
    integral_log_scale_mul_exp_mul_thetaCuspSourceTerm_pair hσ hn hm t,
    integral_exp_mul_thetaCuspSourceTerm_pair hσ hn hm t]
  field_simp
  ring

end

end RHTower
