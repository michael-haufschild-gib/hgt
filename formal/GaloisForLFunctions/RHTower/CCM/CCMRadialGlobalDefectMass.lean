import GaloisForLFunctions.RHTower.RadialLeakageMassNormalization

/-!
# The global radial defect mass and the escape from the outer coordinate

The corpus already owns the arcsine leakage measure, the Scheffé transfer with its total mass
discharged from evenness and the normalized exterior ratio, and the profile side of the card.  What
was still missing are the card's own equations `(15)`, `(16)`, `(18)` and `(20)`: the exact change
of variables `y = λx` in the leakage norm, the resulting universal total mass, and the fact that the
former outer coordinate `r = λ²(x − 1)` carries no mass in the limit.

All four are proved here, with the card's `(13)` — the exact constrained leakage ratio and the
endpoint-response height — as named inputs, exactly as the surrounding response-constant layer
states its own limit inferences.
-/

open MeasureTheory Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

variable {lam : ℝ} {q : ℝ → ℂ}

/-- **Equation (3), squared.**  The squared normalized global radial profile `|R_λ(x)|²`. -/
def radialProfileSq (lam : ℝ) (q : ℝ → ℂ) (x : ℝ) : ℝ := ‖q (lam * x)‖ ^ (2 : ℕ) / ‖q lam‖ ^ (2 : ℕ)

/-- **Equation (19).**  The former outer coordinate `r = λ²(x − 1)`. -/
def outerProfileSq (lam : ℝ) (q : ℝ → ℂ) (r : ℝ) : ℝ :=
  radialProfileSq lam q (r / lam ^ (2 : ℕ) + 1)

theorem radialProfileSq_nonneg (lam : ℝ) (q : ℝ → ℂ) (x : ℝ) : 0 ≤ radialProfileSq lam q x := by
  unfold radialProfileSq
  positivity

theorem radialProfileSq_eq_nuLambda {d : ℝ} (hlam : lam ≠ 0) (hd : d ≠ 0)
    (hqlam : ‖q lam‖ ≠ 0) (x : ℝ) :
    radialProfileSq lam q x = d / (lam * ‖q lam‖ ^ (2 : ℕ)) * nuLambdaDensity lam d q x := by
  unfold radialProfileSq nuLambdaDensity
  have h2 : ‖q lam‖ ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hqlam
  field_simp

/-- **Equation (15).**  The exact change of variables `y = λx` in the leakage norm. -/
theorem integral_Ioi_radialProfileSq {delta : ℝ} (hlam : 0 < lam)
    (hqeven : Function.Even q) (hqlam : ‖q lam‖ ≠ 0)
    (hexterior : (∫ y in Iic (-lam), ‖q y‖ ^ (2 : ℕ)) + ∫ y in Ioi lam, ‖q y‖ ^ (2 : ℕ) = delta) :
    ∫ x in Ioi (1 : ℝ), radialProfileSq lam q x = delta / (2 * (lam * ‖q lam‖ ^ (2 : ℕ))) := by
  have hmass := integral_Ioi_nuLambdaDensity_eq_half_exterior (lam := lam) (d := 1)
    (delta := delta) hlam one_ne_zero hqeven hexterior
  have hcongr : ∫ x in Ioi (1 : ℝ), radialProfileSq lam q x
      = ∫ x in Ioi (1 : ℝ), 1 / (lam * ‖q lam‖ ^ (2 : ℕ)) * nuLambdaDensity lam 1 q x :=
    setIntegral_congr_fun measurableSet_Ioi fun x _ =>
      radialProfileSq_eq_nuLambda hlam.ne' one_ne_zero hqlam x
  rw [hcongr, integral_const_mul, hmass]
  have h2 : ‖q lam‖ ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hqlam
  field_simp

/-- **Equation (16).**  The aperture-normalized global radial mass is universal. -/
theorem tendsto_aperture_mul_integral_radialProfileSq
    {ι : Type*} {l : Filter ι} {lamf df deltaf : ι → ℝ} {qf : ι → ℝ → ℂ}
    (hparam : ∀ᶠ i in l, 0 < lamf i ∧ df i ≠ 0 ∧ ‖qf i (lamf i)‖ ≠ 0)
    (hqeven : ∀ i, Function.Even (qf i))
    (hexterior : ∀ i,
      (∫ y in Iic (-lamf i), ‖qf i y‖ ^ (2 : ℕ)) + ∫ y in Ioi (lamf i), ‖qf i y‖ ^ (2 : ℕ) = deltaf i)
    (hratio : Tendsto (fun i => deltaf i / df i) l (nhds (8 / 11)))
    (hheight : Tendsto (fun i => ‖qf i (lamf i)‖ ^ (2 : ℕ) / (lamf i * df i)) l
      (nhds (16 * Real.pi / 11))) :
    Tendsto (fun i => 2 * Real.pi * lamf i ^ (2 : ℕ)
        * ∫ x in Ioi (1 : ℝ), radialProfileSq (lamf i) (qf i) x) l (nhds (1 / 2)) := by
  have hne : (16 * Real.pi / 11 : ℝ) ≠ 0 := by positivity
  have hlim := (hratio.const_mul Real.pi).div hheight hne
  have hval : Real.pi * (8 / 11) / (16 * Real.pi / 11) = 1 / 2 := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [hparam] with i hi
  rw [integral_Ioi_radialProfileSq hi.1 (hqeven i) hi.2.2 (hexterior i)]
  simp only [Pi.div_apply]
  have h2 : ‖qf i (lamf i)‖ ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hi.2.2
  have hd : df i ≠ 0 := hi.2.1
  have hl : lamf i ≠ 0 := hi.1.ne'
  field_simp

/-- **Equation (18), mass form.**  In the CCM normalization the total global radial mass is
`1/(4π)`. -/
theorem tendsto_sq_mul_integral_radialProfileSq
    {ι : Type*} {l : Filter ι} {lamf df deltaf : ι → ℝ} {qf : ι → ℝ → ℂ}
    (hparam : ∀ᶠ i in l, 0 < lamf i ∧ df i ≠ 0 ∧ ‖qf i (lamf i)‖ ≠ 0)
    (hqeven : ∀ i, Function.Even (qf i))
    (hexterior : ∀ i,
      (∫ y in Iic (-lamf i), ‖qf i y‖ ^ (2 : ℕ)) + ∫ y in Ioi (lamf i), ‖qf i y‖ ^ (2 : ℕ) = deltaf i)
    (hratio : Tendsto (fun i => deltaf i / df i) l (nhds (8 / 11)))
    (hheight : Tendsto (fun i => ‖qf i (lamf i)‖ ^ (2 : ℕ) / (lamf i * df i)) l
      (nhds (16 * Real.pi / 11))) :
    Tendsto (fun i => lamf i ^ (2 : ℕ) * ∫ x in Ioi (1 : ℝ), radialProfileSq (lamf i) (qf i) x) l
      (nhds (1 / (4 * Real.pi))) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hmain := tendsto_aperture_mul_integral_radialProfileSq hparam hqeven hexterior hratio
    hheight
  have hscaled := hmain.const_mul (1 / (2 * Real.pi))
  have hval : 1 / (2 * Real.pi) * (1 / 2 : ℝ) = 1 / (4 * Real.pi) := by
    field_simp
    ring
  rw [hval] at hscaled
  refine hscaled.congr fun i => ?_
  field_simp

/-! ## The escape from the outer coordinate -/

/-- **Equation (19), change of variables.**  The outer-coordinate mass on `[0, A]` is the global
mass of the shrinking band `[1, 1 + A/λ²]`, in the `(18)` normalization. -/
theorem integral_outerProfileSq_eq (hlam : 0 < lam) (q : ℝ → ℂ) (A : ℝ) :
    (∫ r in (0 : ℝ)..A, outerProfileSq lam q r)
      = lam ^ (2 : ℕ) * ∫ x in (1 : ℝ)..(A / lam ^ (2 : ℕ) + 1), radialProfileSq lam q x := by
  have hne : (lam ^ (2 : ℕ) : ℝ) ≠ 0 := by positivity
  have h := intervalIntegral.integral_comp_div_add (a := (0 : ℝ)) (b := A)
    (c := lam ^ (2 : ℕ)) (radialProfileSq lam q) hne 1
  simp only [smul_eq_mul, zero_div, zero_add] at h
  exact h

/-- The limiting density's mass on a band at the edge. -/
theorem integral_Ioc_nuInfinityDensity {b : ℝ} (hb : 1 ≤ b) :
    ∫ x in Ioc (1 : ℝ) b, nuInfinityDensity x
      = 8 / (11 * Real.pi) * (Real.pi / 2 - Real.arcsin (1 / b)) := by
  have hsplit : Ioi (1 : ℝ) = Ioc 1 b ∪ Ioi b := (Ioc_union_Ioi_eq_Ioi hb).symm
  have hdisj : Disjoint (Ioc (1 : ℝ) b) (Ioi b) := Ioc_disjoint_Ioi le_rfl
  have hint1 : IntegrableOn nuInfinityDensity (Ioc (1 : ℝ) b) volume :=
    integrableOn_Ioi_one_nuInfinityDensity.mono_set Ioc_subset_Ioi_self
  have hint2 : IntegrableOn nuInfinityDensity (Ioi b) volume :=
    integrableOn_Ioi_one_nuInfinityDensity.mono_set (Ioi_subset_Ioi hb)
  have hunion : ∫ x in Ioi (1 : ℝ), nuInfinityDensity x
      = (∫ x in Ioc (1 : ℝ) b, nuInfinityDensity x) + ∫ x in Ioi b, nuInfinityDensity x := by
    rw [hsplit, setIntegral_union hdisj measurableSet_Ioi hint1 hint2]
  have htail : ∫ x in Ioi b, nuInfinityDensity x
      = 8 / (11 * Real.pi) * Real.arcsin (1 / b) := by
    unfold nuInfinityDensity
    rw [integral_const_mul, integral_Ioi_radialLeakageDensity hb]
  have htotal : ∫ x in Ioi (1 : ℝ), nuInfinityDensity x = 4 / 11 :=
    integral_Ioi_one_nuInfinityDensity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hgoal : (8 : ℝ) / (11 * Real.pi) * (Real.pi / 2 - Real.arcsin (1 / b))
      = 4 / 11 - 8 / (11 * Real.pi) * Real.arcsin (1 / b) := by
    field_simp
    ring
  rw [hgoal, ← htotal, hunion, htail]
  ring

/-- The band mass of a finite density is controlled by the limiting band mass and the `L¹`
distance. -/
theorem integral_Ioc_le_of_L1 {f g : ℝ → ℝ} {b : ℝ} (_hb : 1 ≤ b)
    (hfint : IntegrableOn f (Ioi (1 : ℝ)) volume)
    (hgint : IntegrableOn g (Ioi (1 : ℝ)) volume) :
    ∫ x in Ioc (1 : ℝ) b, f x
      ≤ (∫ x in Ioc (1 : ℝ) b, g x) + ∫ x in Ioi (1 : ℝ), |f x - g x| := by
  have hsub : Ioc (1 : ℝ) b ⊆ Ioi (1 : ℝ) := Ioc_subset_Ioi_self
  have hfb : IntegrableOn f (Ioc (1 : ℝ) b) volume := hfint.mono_set hsub
  have hgb : IntegrableOn g (Ioc (1 : ℝ) b) volume := hgint.mono_set hsub
  have hdiff : IntegrableOn (fun x => f x - g x) (Ioi (1 : ℝ)) volume := hfint.sub hgint
  have habs : IntegrableOn (fun x => |f x - g x|) (Ioi (1 : ℝ)) volume := hdiff.abs
  have hstep1 : (∫ x in Ioc (1 : ℝ) b, f x) - ∫ x in Ioc (1 : ℝ) b, g x
      = ∫ x in Ioc (1 : ℝ) b, (f x - g x) := (integral_sub hfb hgb).symm
  have hstep2 : (∫ x in Ioc (1 : ℝ) b, (f x - g x)) ≤ ∫ x in Ioc (1 : ℝ) b, |f x - g x| := by
    refine setIntegral_mono_on (hfb.sub hgb) (habs.mono_set hsub) measurableSet_Ioc
      fun x _ => le_abs_self _
  have hstep3 : (∫ x in Ioc (1 : ℝ) b, |f x - g x|) ≤ ∫ x in Ioi (1 : ℝ), |f x - g x| := by
    refine setIntegral_mono_set habs ?_ ?_
    · filter_upwards with x using abs_nonneg _
    · exact Filter.Eventually.of_forall fun x hx => hsub hx
  linarith [hstep1, hstep2, hstep3]

/-- **Equation (20).**  All the normalized mass escapes the former outer coordinate: for every
fixed window `[0, A]` the outer-coordinate mass tends to zero. -/
theorem tendsto_integral_outerProfileSq
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {lamf df deltaf : ι → ℝ} {qf : ι → ℝ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hparam : ∀ᶠ i in l, 0 < lamf i ∧ 0 < df i ∧ ‖qf i (lamf i)‖ ≠ 0)
    (hlamTop : Tendsto lamf l atTop)
    (hqeven : ∀ i, Function.Even (qf i))
    (hexterior : ∀ i,
      (∫ y in Iic (-lamf i), ‖qf i y‖ ^ (2 : ℕ)) + ∫ y in Ioi (lamf i), ‖qf i y‖ ^ (2 : ℕ) = deltaf i)
    (hratio : Tendsto (fun i => deltaf i / df i) l (nhds (8 / 11)))
    (hheight : Tendsto (fun i => ‖qf i (lamf i)‖ ^ (2 : ℕ) / (lamf i * df i)) l
      (nhds (16 * Real.pi / 11)))
    (hqint : ∀ᶠ i in l, IntegrableOn (fun y : ℝ => ‖qf i y‖ ^ (2 : ℕ)) (Ioi (lamf i)))
    (hae : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))),
      Tendsto (fun i => nuLambdaDensity (lamf i) (df i) (qf i) x) l
        (nhds (nuInfinityDensity x))) :
    Tendsto (fun i => ∫ r in (0 : ℝ)..A, outerProfileSq (lamf i) (qf i) r) l (nhds 0) := by
  have hne : (16 * Real.pi / 11 : ℝ) ≠ 0 := by positivity
  -- the reciprocal height
  have hrecip : Tendsto (fun i => lamf i * df i / ‖qf i (lamf i)‖ ^ (2 : ℕ)) l
      (nhds (11 / (16 * Real.pi))) := by
    have hinv := hheight.inv₀ hne
    have hval : (16 * Real.pi / 11 : ℝ)⁻¹ = 11 / (16 * Real.pi) := by
      rw [inv_div]
    rw [hval] at hinv
    refine hinv.congr' ?_
    filter_upwards [hparam] with i hi
    rw [inv_div]
  -- the L¹ convergence of the finite densities
  have hL1 := nuLambdaDensity_tendsto_L1_of_exterior_ratio
    (hparam.mono fun _ hi => ⟨hi.1, hi.2.1⟩) hqeven hexterior hratio hqint hae
  -- the shrinking band
  have hbandTop : Tendsto (fun i => A / lamf i ^ (2 : ℕ) + 1) l (nhds 1) := by
    have hsq : Tendsto (fun i => lamf i ^ (2 : ℕ)) l atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hlamTop
    have hdiv : Tendsto (fun i => A / lamf i ^ (2 : ℕ)) l (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds hsq
    simpa using hdiv.add_const (1 : ℝ)
  have hedge : Tendsto (fun i => 8 / (11 * Real.pi)
      * (Real.pi / 2 - Real.arcsin (1 / (A / lamf i ^ (2 : ℕ) + 1)))) l (nhds 0) := by
    have hone : Tendsto (fun i => (1 : ℝ) / (A / lamf i ^ (2 : ℕ) + 1)) l (nhds 1) := by
      have h : Tendsto (fun i => (1 : ℝ) / (A / lamf i ^ (2 : ℕ) + 1)) l (nhds ((1 : ℝ) / 1)) :=
        tendsto_const_nhds.div hbandTop one_ne_zero
      rwa [div_one] at h
    have harc : Tendsto (fun i => Real.arcsin (1 / (A / lamf i ^ (2 : ℕ) + 1))) l
        (nhds (Real.pi / 2)) := by
      have := (Real.continuous_arcsin.tendsto (1 : ℝ)).comp hone
      rwa [Real.arcsin_one] at this
    have hsub : Tendsto (fun i => Real.pi / 2 - Real.arcsin (1 / (A / lamf i ^ (2 : ℕ) + 1))) l
        (nhds 0) := by
      have h : Tendsto (fun i => Real.pi / 2 - Real.arcsin (1 / (A / lamf i ^ (2 : ℕ) + 1))) l
          (nhds (Real.pi / 2 - Real.pi / 2)) := tendsto_const_nhds.sub harc
      rwa [sub_self] at h
    simpa using hsub.const_mul (8 / (11 * Real.pi))
  -- the upper envelope
  have hupper : Tendsto (fun i => lamf i * df i / ‖qf i (lamf i)‖ ^ (2 : ℕ)
      * ((8 / (11 * Real.pi) * (Real.pi / 2 - Real.arcsin (1 / (A / lamf i ^ (2 : ℕ) + 1))))
        + ∫ x in Ioi (1 : ℝ),
            |nuLambdaDensity (lamf i) (df i) (qf i) x - nuInfinityDensity x|)) l (nhds 0) := by
    have hsum := hedge.add hL1
    rw [add_zero] at hsum
    have := hrecip.mul hsum
    rwa [mul_zero] at this
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [hparam] with i hi
    rw [integral_outerProfileSq_eq hi.1]
    have hband : (1 : ℝ) ≤ A / lamf i ^ (2 : ℕ) + 1 := by
      have : (0 : ℝ) ≤ A / lamf i ^ (2 : ℕ) := by positivity
      linarith
    have hnn : (0 : ℝ) ≤ ∫ x in (1 : ℝ)..(A / lamf i ^ (2 : ℕ) + 1), radialProfileSq (lamf i) (qf i) x :=
      intervalIntegral.integral_nonneg hband fun x _ => radialProfileSq_nonneg _ _ _
    positivity
  · filter_upwards [hparam, hqint] with i hi hqi
    have hband : (1 : ℝ) ≤ A / lamf i ^ (2 : ℕ) + 1 := by
      have : (0 : ℝ) ≤ A / lamf i ^ (2 : ℕ) := by positivity
      linarith
    have hlam0 : (0 : ℝ) < lamf i := hi.1
    have hd0 : (0 : ℝ) < df i := hi.2.1
    have hq0 : ‖qf i (lamf i)‖ ≠ 0 := hi.2.2
    have hq2 : ‖qf i (lamf i)‖ ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hq0
    have hnuint : IntegrableOn (nuLambdaDensity (lamf i) (df i) (qf i)) (Ioi (1 : ℝ)) volume :=
      integrableOn_Ioi_nuLambdaDensity hlam0 (qf i) hqi
    -- rewrite the interval integral as an `Ioc` integral of the finite density
    have hrewrite : (∫ x in (1 : ℝ)..(A / lamf i ^ (2 : ℕ) + 1), radialProfileSq (lamf i) (qf i) x)
        = df i / (lamf i * ‖qf i (lamf i)‖ ^ (2 : ℕ))
          * ∫ x in Ioc (1 : ℝ) (A / lamf i ^ (2 : ℕ) + 1), nuLambdaDensity (lamf i) (df i) (qf i) x := by
      rw [intervalIntegral.integral_of_le hband, ← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioc fun x _ =>
        radialProfileSq_eq_nuLambda hlam0.ne' hd0.ne' hq0 x
    rw [integral_outerProfileSq_eq hlam0, hrewrite]
    have hband_le := integral_Ioc_le_of_L1 (f := nuLambdaDensity (lamf i) (df i) (qf i))
      (g := nuInfinityDensity) hband hnuint integrableOn_Ioi_one_nuInfinityDensity
    rw [integral_Ioc_nuInfinityDensity hband] at hband_le
    have hcoeff : lamf i ^ (2 : ℕ) * (df i / (lamf i * ‖qf i (lamf i)‖ ^ (2 : ℕ)))
        = lamf i * df i / ‖qf i (lamf i)‖ ^ (2 : ℕ) := by
      field_simp
    calc lamf i ^ (2 : ℕ) * (df i / (lamf i * ‖qf i (lamf i)‖ ^ (2 : ℕ))
          * ∫ x in Ioc (1 : ℝ) (A / lamf i ^ (2 : ℕ) + 1), nuLambdaDensity (lamf i) (df i) (qf i) x)
        = lamf i * df i / ‖qf i (lamf i)‖ ^ (2 : ℕ)
          * ∫ x in Ioc (1 : ℝ) (A / lamf i ^ (2 : ℕ) + 1),
              nuLambdaDensity (lamf i) (df i) (qf i) x := by
          rw [← hcoeff]; ring
      _ ≤ lamf i * df i / ‖qf i (lamf i)‖ ^ (2 : ℕ)
          * ((8 / (11 * Real.pi) * (Real.pi / 2 - Real.arcsin (1 / (A / lamf i ^ (2 : ℕ) + 1))))
            + ∫ x in Ioi (1 : ℝ),
                |nuLambdaDensity (lamf i) (df i) (qf i) x - nuInfinityDensity x|) := by
          refine mul_le_mul_of_nonneg_left hband_le ?_
          positivity

end GaloisForLFunctions.RHTower

end
