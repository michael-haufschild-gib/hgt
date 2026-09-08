import GaloisForLFunctions.HTGeometry.FokasLenellsSmallScattering
import GaloisForLFunctions.HTGeometry.HermiteOrthogonality

/-!
# Spectral-independent uniformized transport and endpoint estimates

Equations (2.8) and (3.6)–(3.13) of Yan–Zhang–Zhu, arXiv:2607.19649v1,
separate an integrable effective potential from the free spectral oscillation.
The existing Schwartz-product construction from `HermiteOrthogonality` makes
all four effective entries Schwartz. The corpus's variable-coefficient
Gronwall theorem and integrable-derivative limit theorem then give both
endpoint states with bounds independent of every real uniformized parameter.

All coefficient profiles are arbitrary Schwartz functions. Existence,
integrability, endpoint convergence and displacement estimates are proved;
no asymptotic or smallness hypothesis is imposed. A Boolean orientation runs
the same argument on both half-lines without doubling the coefficient mass.
-/

open Complex Matrix MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- Schwartz entries of the effective potential (2.8), independent of the spectral variable. -/
def effectiveSchwartzEntries (f g h : SchwartzMap ℝ ℂ) :
    Matrix (Fin 2) (Fin 2) (SchwartzMap ℝ ℂ) :=
  !![(I/2) • (mulS f g), (-I/2) • g;
    h+(I/2) • (mulS (mulS f f) g), (-I/2) • (mulS f g)]

theorem effectiveSchwartzEntries_apply (f g h : SchwartzMap ℝ ℂ) (x : ℝ) :
    (effectiveSchwartzEntries f g h).map (fun e => e x) = effectivePotential (f x) (g x) (h x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [effectiveSchwartzEntries, effectivePotential] <;> ring

/-- An integrable majorant with no spectral parameter. -/
def effectiveDensity (f g h : SchwartzMap ℝ ℂ) (x : ℝ) : ℝ :=
  ‖effectiveSchwartzEntries f g h 0 0 x‖+‖effectiveSchwartzEntries f g h 0 1 x‖+
    ‖effectiveSchwartzEntries f g h 1 0 x‖+‖effectiveSchwartzEntries f g h 1 1 x‖

theorem effectiveDensity_nonneg (f g h : SchwartzMap ℝ ℂ) (x : ℝ) :
    0 ≤ effectiveDensity f g h x := by unfold effectiveDensity; positivity

theorem effectiveDensity_continuous (f g h : SchwartzMap ℝ ℂ) : Continuous (effectiveDensity f g h) := by
  unfold effectiveDensity
  fun_prop

theorem effectiveDensity_integrable (f g h : SchwartzMap ℝ ℂ) : Integrable (effectiveDensity f g h) :=
  ((((effectiveSchwartzEntries f g h 0 0).integrable.norm.add
    (effectiveSchwartzEntries f g h 0 1).integrable.norm).add
    (effectiveSchwartzEntries f g h 1 0).integrable.norm).add
    (effectiveSchwartzEntries f g h 1 1).integrable.norm)

def effectiveMass (f g h : SchwartzMap ℝ ℂ) : ℝ := ∫ x, effectiveDensity f g h x

theorem effectiveMass_nonneg (f g h : SchwartzMap ℝ ℂ) : 0 ≤ effectiveMass f g h :=
  integral_nonneg (effectiveDensity_nonneg f g h)

def effectiveOperator (f g h : SchwartzMap ℝ ℂ) (x : ℝ) : SpectralVector →L[ℝ] SpectralVector :=
  pairOperator (effectiveSchwartzEntries f g h 0 0 x) (effectiveSchwartzEntries f g h 0 1 x)
    (effectiveSchwartzEntries f g h 1 0 x) (effectiveSchwartzEntries f g h 1 1 x)

theorem effectiveOperator_bound (f g h : SchwartzMap ℝ ℂ) (x : ℝ) (v : SpectralVector) :
    ‖effectiveOperator f g h x v‖ ≤ effectiveDensity f g h x*‖v‖ := by
  exact ((effectiveOperator f g h x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (pairOperator_bound _ _ _ _) (norm_nonneg v))

def uniformizedInteractionRate (f g h : SchwartzMap ℝ ℂ) (z x : ℝ) (v : SpectralVector) : SpectralVector :=
  rotatingFrame z x (effectiveOperator f g h x (rotatingFrame (-z) x v))

theorem uniformizedInteractionRate_bound (f g h : SchwartzMap ℝ ℂ) (z x : ℝ) (v : SpectralVector) :
    ‖uniformizedInteractionRate f g h z x v‖ ≤ effectiveDensity f g h x*‖v‖ := by
  rw [uniformizedInteractionRate, rotatingFrame_norm]
  exact (effectiveOperator_bound _ _ _ _ _).trans_eq (by rw [rotatingFrame_norm])

def uniformizedInteractionSolution (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (v : SpectralVector) (x : ℝ) :
    SpectralVector := rotatingFrame z x (spectralSolution f g h (z:ℂ) v x)

/-- Cancellation of the free oscillation leaves precisely the integrable effective potential. -/
theorem uniformizedInteractionSolution_hasDerivAt (f g h : SchwartzMap ℝ ℂ) (z : ℝ)
    (v : SpectralVector) (x : ℝ) :
    HasDerivAt (uniformizedInteractionSolution f g h z v)
      (uniformizedInteractionRate f g h z x (uniformizedInteractionSolution f g h z v x)) x := by
  have hd := spectralSolution_hasDerivAt f g h (z:ℂ) v x
  have h1 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x hd
  have h2 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x hd
  have hpair := ((FDNLS.hasDerivAt_staggerPhase z x).fun_mul h1).prodMk
    ((FDNLS.hasDerivAt_staggerPhase (-z) x).fun_mul h2)
  refine hpair.congr_deriv ?_
  change _ = rotatingFrame z x (effectiveOperator f g h x
    (rotatingFrame (-z) x (rotatingFrame z x (spectralSolution f g h (z:ℂ) v x))))
  rw [rotatingFrame_neg_inverse]
  apply Prod.ext <;>
    simp [rotatingFrame, effectiveOperator, effectiveSchwartzEntries, spectralKernel,
      spectralEntries, pairOperator] <;> ring

theorem uniformizedInteractionSolution_initial (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (v : SpectralVector) :
    uniformizedInteractionSolution f g h z v 0 = v := by
  simp [uniformizedInteractionSolution, spectralSolution_initial, rotatingFrame, FDNLS.staggerPhase]

theorem uniformizedInteractionSolution_continuous (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (v : SpectralVector) :
    Continuous (uniformizedInteractionSolution f g h z v) :=
  (show Differentiable ℝ (uniformizedInteractionSolution f g h z v) from
    fun x => (uniformizedInteractionSolution_hasDerivAt f g h z v x).differentiableAt).continuous


theorem uniformizedInteractionRate_continuous (f g h : SchwartzMap ℝ ℂ) (z : ℝ) :
    Continuous (fun p : ℝ × SpectralVector => uniformizedInteractionRate f g h z p.1 p.2) := by
  unfold uniformizedInteractionRate rotatingFrame effectiveOperator pairOperator
  change Continuous fun p : ℝ × SpectralVector =>
    (FDNLS.staggerPhase z p.1 *
      (effectiveSchwartzEntries f g h 0 0 p.1*(FDNLS.staggerPhase (-z) p.1*p.2.1)+
       effectiveSchwartzEntries f g h 0 1 p.1*(FDNLS.staggerPhase (-(-z)) p.1*p.2.2)),
     FDNLS.staggerPhase (-z) p.1 *
      (effectiveSchwartzEntries f g h 1 0 p.1*(FDNLS.staggerPhase (-z) p.1*p.2.1)+
       effectiveSchwartzEntries f g h 1 1 p.1*(FDNLS.staggerPhase (-(-z)) p.1*p.2.2)))
  unfold FDNLS.staggerPhase
  fun_prop

/-- Orientation packages both half-lines in the same quantitative argument. -/
def uniformizedOrbit (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (v : SpectralVector) (b : Bool) (x : ℝ) :
    SpectralVector := uniformizedInteractionSolution f g h z v (if b then -x else x)

def uniformizedOrbitDerivative (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (v : SpectralVector)
    (b : Bool) (x : ℝ) : SpectralVector :=
  if b then -(uniformizedInteractionRate f g h z (-x) (uniformizedInteractionSolution f g h z v (-x)))
    else uniformizedInteractionRate f g h z x (uniformizedInteractionSolution f g h z v x)

def orientedEffectiveDensity (f g h : SchwartzMap ℝ ℂ) (b : Bool) (x : ℝ) : ℝ :=
  effectiveDensity f g h (if b then -x else x)

theorem uniformizedOrbit_hasDerivAt (f g h : SchwartzMap ℝ ℂ) (z : ℝ)
    (v : SpectralVector) (b : Bool) (x : ℝ) :
    HasDerivAt (uniformizedOrbit f g h z v b) (uniformizedOrbitDerivative f g h z v b x) x := by
  cases b
  · exact uniformizedInteractionSolution_hasDerivAt f g h z v x
  · have hd := (uniformizedInteractionSolution_hasDerivAt f g h z v (-x)).scomp x
      (hasDerivAt_id x).neg
    change HasDerivAt (fun y => uniformizedInteractionSolution f g h z v (-y))
      (-uniformizedInteractionRate f g h z (-x) (uniformizedInteractionSolution f g h z v (-x))) x
    simpa only [Function.comp_def, neg_one_smul] using hd

theorem uniformizedOrbit_initial (f g h : SchwartzMap ℝ ℂ) (z : ℝ)
    (v : SpectralVector) (b : Bool) : uniformizedOrbit f g h z v b 0 = v := by
  cases b <;> simpa [uniformizedOrbit] using uniformizedInteractionSolution_initial f g h z v

theorem uniformizedOrbit_continuous (f g h : SchwartzMap ℝ ℂ) (z : ℝ)
    (v : SpectralVector) (b : Bool) : Continuous (uniformizedOrbit f g h z v b) :=
  (show Differentiable ℝ (uniformizedOrbit f g h z v b) from
    fun x => (uniformizedOrbit_hasDerivAt f g h z v b x).differentiableAt).continuous

theorem uniformizedOrbitDerivative_continuous (f g h : SchwartzMap ℝ ℂ) (z : ℝ)
    (v : SpectralVector) (b : Bool) : Continuous (uniformizedOrbitDerivative f g h z v b) := by
  have hc := (uniformizedInteractionRate_continuous f g h z).comp
    (f := fun x : ℝ => (x, uniformizedInteractionSolution f g h z v x))
    (continuous_id.prodMk (uniformizedInteractionSolution_continuous f g h z v))
  cases b
  · exact hc
  · exact (hc.comp (f := fun x : ℝ => -x) continuous_neg).neg

theorem uniformizedOrbitDerivative_bound (f g h : SchwartzMap ℝ ℂ) (z : ℝ)
    (v : SpectralVector) (b : Bool) (x : ℝ) :
    ‖uniformizedOrbitDerivative f g h z v b x‖ ≤
      orientedEffectiveDensity f g h b x*‖uniformizedOrbit f g h z v b x‖ := by
  cases b
  · exact uniformizedInteractionRate_bound f g h z x _
  · simpa only [uniformizedOrbitDerivative, uniformizedOrbit, orientedEffectiveDensity,
      Bool.true_eq, ↓reduceIte, norm_neg] using uniformizedInteractionRate_bound f g h z (-x) _

theorem orientedEffectiveDensity_nonneg (f g h : SchwartzMap ℝ ℂ) (b : Bool) (x : ℝ) :
    0 ≤ orientedEffectiveDensity f g h b x := effectiveDensity_nonneg f g h _

theorem orientedEffectiveDensity_continuous (f g h : SchwartzMap ℝ ℂ) (b : Bool) :
    Continuous (orientedEffectiveDensity f g h b) := by
  cases b
  · exact effectiveDensity_continuous f g h
  · exact (effectiveDensity_continuous f g h).comp (f := fun x : ℝ => -x) continuous_neg

theorem orientedEffectiveDensity_integrable (f g h : SchwartzMap ℝ ℂ) (b : Bool) :
    Integrable (orientedEffectiveDensity f g h b) := by
  cases b
  · exact effectiveDensity_integrable f g h
  · exact (effectiveDensity_integrable f g h).comp_neg

theorem orientedEffectiveDensity_integral (f g h : SchwartzMap ℝ ℂ) (b : Bool) :
    ∫ x, orientedEffectiveDensity f g h b x = effectiveMass f g h := by
  cases b
  · rfl
  · exact integral_neg_eq_self (effectiveDensity f g h) volume

theorem uniformizedOrbit_integral (f g h : SchwartzMap ℝ ℂ) (z : ℝ)
    (v : SpectralVector) (b : Bool) (x : ℝ) :
    uniformizedOrbit f g h z v b x = v+∫ y in (0:ℝ)..x, uniformizedOrbitDerivative f g h z v b y := by
  have hdint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => uniformizedOrbit_hasDerivAt f g h z v b y)
    ((uniformizedOrbitDerivative_continuous f g h z v b).intervalIntegrable 0 x)
  rw [uniformizedOrbit_initial] at hdint
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp hdint.symm)

/-- A bound uniform in both position on either half-line and the real spectral variable. -/
theorem uniformizedOrbit_bound (f g h : SchwartzMap ℝ ℂ) (z : ℝ)
    (v : SpectralVector) (b : Bool) (x : ℝ) :
    ‖uniformizedOrbit f g h z v b |x|‖ ≤ ‖v‖*Real.exp (effectiveMass f g h) := by
  have hS := (uniformizedOrbit_continuous f g h z v b).norm
  have hk := orientedEffectiveDensity_continuous f g h b
  have hD := (uniformizedOrbitDerivative_continuous f g h z v b).norm
  apply le_mul_exp_of_le_add_integral_of_mass_le (A := 0) (B := |x|)
    (S := fun y => ‖uniformizedOrbit f g h z v b y‖) (k := orientedEffectiveDensity f g h b)
    (abs_nonneg x) hS.continuousOn hk.continuousOn
    (fun y _ => orientedEffectiveDensity_nonneg f g h b y) (norm_nonneg v)
  · intro y hy
    calc
      ‖uniformizedOrbit f g h z v b y‖ =
          ‖v+∫ s in (0:ℝ)..y, uniformizedOrbitDerivative f g h z v b s‖ := by
        rw [uniformizedOrbit_integral]
      _ ≤ ‖v‖+‖∫ s in (0:ℝ)..y, uniformizedOrbitDerivative f g h z v b s‖ := norm_add_le _ _
      _ ≤ ‖v‖+∫ s in (0:ℝ)..y, ‖uniformizedOrbitDerivative f g h z v b s‖ :=
        add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm hy.1)
      _ ≤ ‖v‖+∫ s in (0:ℝ)..y,
          orientedEffectiveDensity f g h b s*‖uniformizedOrbit f g h z v b s‖ := by
        apply add_le_add le_rfl
        exact intervalIntegral.integral_mono_on hy.1 (hD.intervalIntegrable 0 y)
          ((hk.mul hS).intervalIntegrable 0 y)
          (fun s _ => uniformizedOrbitDerivative_bound f g h z v b s)
  · intro y hy
    rw [intervalIntegral.integral_of_le hy.1, ← orientedEffectiveDensity_integral f g h b]
    exact setIntegral_le_integral (orientedEffectiveDensity_integrable f g h b)
      (Eventually.of_forall (orientedEffectiveDensity_nonneg f g h b))
  · exact ⟨abs_nonneg x, le_rfl⟩

theorem uniformizedOrbitDerivative_integrableOn_Ioi (f g h : SchwartzMap ℝ ℂ) (z : ℝ)
    (v : SpectralVector) (b : Bool) :
    IntegrableOn (uniformizedOrbitDerivative f g h z v b) (Set.Ioi 0) := by
  have hmajor := ((orientedEffectiveDensity_integrable f g h b).const_mul
    (‖v‖*Real.exp (effectiveMass f g h))).integrableOn (s := Set.Ioi 0)
  apply hmajor.mono' (uniformizedOrbitDerivative_continuous f g h z v b).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hb := uniformizedOrbit_bound f g h z v b x
  rw [abs_of_pos hx] at hb
  calc
    ‖uniformizedOrbitDerivative f g h z v b x‖ ≤
        orientedEffectiveDensity f g h b x*‖uniformizedOrbit f g h z v b x‖ :=
      uniformizedOrbitDerivative_bound _ _ _ _ _ _ _
    _ ≤ orientedEffectiveDensity f g h b x*(‖v‖*Real.exp (effectiveMass f g h)) :=
      mul_le_mul_of_nonneg_left hb (orientedEffectiveDensity_nonneg f g h b x)
    _ = _ := mul_comm _ _

def uniformizedAsymptoticVector (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (v : SpectralVector)
    (b : Bool) : SpectralVector := v+∫ x in Set.Ioi (0:ℝ), uniformizedOrbitDerivative f g h z v b x

theorem uniformizedOrbit_tendsto (f g h : SchwartzMap ℝ ℂ) (z : ℝ)
    (v : SpectralVector) (b : Bool) :
    Tendsto (uniformizedOrbit f g h z v b) atTop (𝓝 (uniformizedAsymptoticVector f g h z v b)) := by
  have hd := tendsto_of_hasDerivAt_of_integrableOn_Ioi
    (a := 0) (fun x _ => uniformizedOrbit_hasDerivAt f g h z v b x)
    (uniformizedOrbitDerivative_integrableOn_Ioi f g h z v b)
  simpa only [uniformizedOrbit_initial, uniformizedAsymptoticVector] using hd

/-- Both endpoint states have a spectral-independent displacement bound. -/
theorem uniformizedAsymptoticVector_displacement (f g h : SchwartzMap ℝ ℂ) (z : ℝ)
    (v : SpectralVector) (b : Bool) :
    ‖uniformizedAsymptoticVector f g h z v b-v‖ ≤
      ‖v‖*(Real.exp (effectiveMass f g h)*effectiveMass f g h) := by
  rw [uniformizedAsymptoticVector, add_sub_cancel_left]
  have hc : 0 ≤ ‖v‖*Real.exp (effectiveMass f g h) := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  calc
    ‖∫ x in Set.Ioi (0:ℝ), uniformizedOrbitDerivative f g h z v b x‖ ≤
        ∫ x in Set.Ioi (0:ℝ), (‖v‖*Real.exp (effectiveMass f g h))*orientedEffectiveDensity f g h b x := by
      apply norm_integral_le_of_norm_le
        (((orientedEffectiveDensity_integrable f g h b).const_mul _).integrableOn)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hb := uniformizedOrbit_bound f g h z v b x
      rw [abs_of_pos hx] at hb
      calc
        ‖uniformizedOrbitDerivative f g h z v b x‖ ≤
            orientedEffectiveDensity f g h b x*‖uniformizedOrbit f g h z v b x‖ :=
          uniformizedOrbitDerivative_bound _ _ _ _ _ _ _
        _ ≤ orientedEffectiveDensity f g h b x*(‖v‖*Real.exp (effectiveMass f g h)) :=
          mul_le_mul_of_nonneg_left hb (orientedEffectiveDensity_nonneg f g h b x)
        _ = _ := mul_comm _ _
    _ = (‖v‖*Real.exp (effectiveMass f g h))*∫ x in Set.Ioi (0:ℝ), orientedEffectiveDensity f g h b x :=
      integral_const_mul _ _
    _ ≤ (‖v‖*Real.exp (effectiveMass f g h))*effectiveMass f g h := by
      apply mul_le_mul_of_nonneg_left _ hc
      rw [← orientedEffectiveDensity_integral f g h b]
      exact setIntegral_le_integral (orientedEffectiveDensity_integrable f g h b)
        (Eventually.of_forall (orientedEffectiveDensity_nonneg f g h b))
    _ = _ := by ring

end
end GaloisForLFunctions.HTGeometry.FokasLenells
