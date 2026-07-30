import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationBounds
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailArithmeticPhaseSeam

/-!
# The exact potential jet behind the arithmetic phase seam

The first differentiated Gaussian density atom is literally four times the second source
derivative of the first raw theta atom.  Two integrations by parts therefore split every
positive-half-line phase tail into its two endpoint jets and one `z^2`-weighted potential tail.
This retains the boundary data block by block, before any current polarization.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

/-- Positive-half-line phase transform of four times the first raw theta potential atom. -/
def thetaCuspTailPotentialAtomOnePhaseTail (a : ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ in Ioi a,
    ((4 * thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 0) 1 u : ℝ) : ℂ) *
      spectralTranslationPhase u z

lemma hasDerivAt_spectralTranslationPhase_source (z : ℂ) (x : ℝ) :
    HasDerivAt (fun u : ℝ => spectralTranslationPhase u z)
      (I * z * spectralTranslationPhase x z) x := by
  have hraw :=
    (Complex.hasDerivAt_exp (((x : ℂ) * I) * z)).comp x
      ((Complex.ofRealCLM.hasDerivAt.mul_const I).mul_const z)
  have hraw' := hraw.congr_deriv
    (g' := I * z * Complex.exp (((x : ℂ) * I) * z)) (by
      simpa [Complex.ofRealCLM_apply] using
        (mul_comm (Complex.exp (((x : ℂ) * I) * z)) (I * z)))
  simpa only [spectralTranslationPhase, Complex.ofRealCLM_apply,
    Function.comp_apply] using! hraw'

lemma hasDerivAt_spectralTranslationPhase_sourceDerivative (z : ℂ) (x : ℝ) :
    HasDerivAt (fun u : ℝ => I * z * spectralTranslationPhase u z)
      (-(z ^ 2) * spectralTranslationPhase x z) x := by
  have h := (hasDerivAt_spectralTranslationPhase_source z x).const_mul (I * z)
  apply h.congr_deriv
  rw [show I * z * (I * z * spectralTranslationPhase x z) =
      I * I * z ^ 2 * spectralTranslationPhase x z by ring, I_mul_I]
  ring

lemma integrableOn_four_thetaCuspTailDerivativeAtom_one_mul_phase
    (m : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    IntegrableOn (fun u : ℝ =>
      ((4 * thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial m) 1 u : ℝ) : ℂ) *
        spectralTranslationPhase u z) (Ioi 0) := by
  have hbase : IntegrableOn (fun u : ℝ =>
      ((4 * thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial m) 1 u : ℝ) : ℂ))
      (Ioi 0) := by
    exact ((integrableOn_thetaCuspPolynomialAtom_Ioi_of_pos
      (thetaCuspTailDerivativePolynomial m) (by omega : 0 < 1)).const_mul 4).ofReal
  change Integrable (fun u : ℝ =>
    ((4 * thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial m) 1 u : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) at hbase
  change Integrable (fun u : ℝ =>
    ((4 * thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial m) 1 u : ℝ) : ℂ) *
      spectralTranslationPhase u z) (volume.restrict (Ioi 0))
  apply hbase.mono
  · have hphase : Continuous (fun u : ℝ => spectralTranslationPhase u z) := by
      unfold spectralTranslationPhase
      fun_prop
    exact hbase.aestronglyMeasurable.mul hphase.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hp := norm_spectralTranslationPhase_le_one hu.le hz
    simpa only [norm_mul, mul_one] using
      mul_le_mul_of_nonneg_left hp
        (norm_nonneg (((4 * thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial m) 1 u : ℝ) : ℂ)))

lemma tendsto_four_thetaCuspTailDerivativeAtom_one_mul_phase_atTop_zero
    (m : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    Tendsto (fun u : ℝ =>
      spectralTranslationPhase u z *
        ((4 * thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial m) 1 u : ℝ) : ℂ))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbaseReal := thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
    (thetaCuspTailDerivativePolynomial m) (by omega : 0 < 1)
  have hbase : Tendsto (fun u : ℝ =>
      4 * ‖(thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial m) 1 u : ℂ)‖)
      atTop (nhds 0) := by
    simpa using (hbaseReal.ofReal.norm.const_mul 4)
  apply squeeze_zero' (Eventually.of_forall fun u => norm_nonneg _) ?_ hbase
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  have hp := norm_spectralTranslationPhase_le_one hu hz
  rw [norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  have hnon : 0 ≤ 4 *
      |thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial m) 1 u| :=
    mul_nonneg (by norm_num) (abs_nonneg _)
  nlinarith

/-- Exact blockwise source identity.  The density phase tail is the endpoint first jet minus the
endpoint zeroth jet, followed by the `z^2`-weighted raw potential tail. -/
theorem thetaCuspTailSecondDensityAtomOnePhaseTail_eq_boundary_sub_sq_potential
    {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : 0 ≤ z.im) :
    thetaCuspTailSecondDensityAtomOnePhaseTail a z =
      -spectralTranslationPhase a z *
          ((4 * thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 1) 1 a : ℝ) : ℂ) +
        I * z * spectralTranslationPhase a z *
          ((4 * thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 0) 1 a : ℝ) : ℂ) -
        z ^ 2 * thetaCuspTailPotentialAtomOnePhaseTail a z := by
  let f : ℝ → ℂ := fun u =>
    ((4 * thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 0) 1 u : ℝ) : ℂ)
  let f' : ℝ → ℂ := fun u =>
    ((4 * thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 1) 1 u : ℝ) : ℂ)
  let f'' : ℝ → ℂ := fun u => (thetaCuspTailSecondDensityAtom 1 u : ℂ)
  let g : ℝ → ℂ := fun u => spectralTranslationPhase u z
  let g' : ℝ → ℂ := fun u => I * z * spectralTranslationPhase u z
  let g'' : ℝ → ℂ := fun u => -(z ^ 2) * spectralTranslationPhase u z
  have hf (u : ℝ) : HasDerivAt f (f' u) u := by
    dsimp [f, f']
    simpa only [thetaCuspTailDerivativePolynomial] using
      ((hasDerivAt_thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial 0) 1 u).const_mul 4).ofReal_comp
  have hf' (u : ℝ) : HasDerivAt f' (f'' u) u := by
    dsimp [f', f'']
    simpa only [thetaCuspTailSecondDensityAtom, thetaCuspTailDerivativePolynomial] using
      ((hasDerivAt_thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial 1) 1 u).const_mul 4).ofReal_comp
  have hg (u : ℝ) : HasDerivAt g (g' u) u := by
    exact hasDerivAt_spectralTranslationPhase_source z u
  have hg' (u : ℝ) : HasDerivAt g' (g'' u) u := by
    exact hasDerivAt_spectralTranslationPhase_sourceDerivative z u
  have hgf'' : IntegrableOn (g * f'') (Ioi a) := by
    have h := (integrableOn_thetaCuspTailSecondDensityAtom_one_mul_phase hz).mono_set
      (Ioi_subset_Ioi ha)
    convert h using 1
    funext u
    dsimp [g, f'']
    ring
  have hg'f' : IntegrableOn (g' * f') (Ioi a) := by
    have h := (integrableOn_four_thetaCuspTailDerivativeAtom_one_mul_phase 1 hz).mono_set
      (Ioi_subset_Ioi ha)
    rw [show g' * f' = fun u =>
        (I * z) * (((4 * thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial 1) 1 u : ℝ) : ℂ) *
            spectralTranslationPhase u z) by
      funext u
      dsimp [g', f']
      ring]
    exact h.const_mul (I * z)
  have hg''f : IntegrableOn (g'' * f) (Ioi a) := by
    have h := (integrableOn_four_thetaCuspTailDerivativeAtom_one_mul_phase 0 hz).mono_set
      (Ioi_subset_Ioi ha)
    rw [show g'' * f = fun u =>
        (-(z ^ 2)) * (((4 * thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial 0) 1 u : ℝ) : ℂ) *
            spectralTranslationPhase u z) by
      funext u
      dsimp [g'', f]
      ring]
    exact h.const_mul (-(z ^ 2))
  have hzero1 : Tendsto (g * f') (𝓝[>] a) (nhds (g a * f' a)) := by
    exact ((hg a).continuousAt.mul (hf' a).continuousAt).tendsto.mono_left inf_le_left
  have hzero2 : Tendsto (g' * f) (𝓝[>] a) (nhds (g' a * f a)) := by
    exact ((hg' a).continuousAt.mul (hf a).continuousAt).tendsto.mono_left inf_le_left
  have hinfty1 : Tendsto (g * f') atTop (nhds 0) := by
    apply
      (tendsto_four_thetaCuspTailDerivativeAtom_one_mul_phase_atTop_zero
        1 hz).congr'
    exact Eventually.of_forall fun _ => rfl
  have hinfty2 : Tendsto (g' * f) atTop (nhds 0) := by
    have h :=
      (tendsto_four_thetaCuspTailDerivativeAtom_one_mul_phase_atTop_zero 0 hz).const_mul
        (I * z)
    have h0 : Tendsto (fun x => (I * z) *
        (spectralTranslationPhase x z *
          ((4 * thetaCuspPolynomialAtom
            (thetaCuspTailDerivativePolynomial 0) 1 x : ℝ) : ℂ)))
        atTop (nhds 0) := by simpa only [mul_zero] using h
    apply h0.congr'
    filter_upwards with u
    dsimp [g', f]
    ring
  have h := integral_Ioi_secondDerivative_mul_eq_boundary_add
    (a := a) (f := f) (f' := f') (f'' := f'')
    (g := g) (g' := g') (g'' := g'')
    (A₁ := g a * f' a) (B₁ := 0) (A₂ := g' a * f a) (B₂ := 0)
    (fun u _ => hf u) (fun u _ => hf' u) (fun u _ => hg u) (fun u _ => hg' u)
    hgf'' hg'f' hg''f hzero1 hinfty1 hzero2 hinfty2
  dsimp [f, f', f'', g, g', g'', thetaCuspTailSecondDensityAtomOnePhaseTail,
    thetaCuspTailPotentialAtomOnePhaseTail] at h ⊢
  rw [show (fun x : ℝ =>
      ((4 * thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 0) 1 x : ℝ) : ℂ) *
        (-(z ^ 2) * spectralTranslationPhase x z)) =
      fun x : ℝ => (-(z ^ 2)) *
        (((4 * thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial 0) 1 x : ℝ) : ℂ) *
            spectralTranslationPhase x z) by funext x; ring,
    integral_const_mul] at h
  (convert h using 1; ring)

end
end RHTower

namespace RHTower
noncomputable section

/-- The raw potential phase tail after the critical half-density normalization. -/
def thetaCuspTailPotentialAtomNormalizedPhaseTail (a : ℝ) (z : ℂ) : ℂ :=
  (Real.exp (-a / 2) : ℂ) * spectralTranslationPhase (-a) z *
    thetaCuspTailPotentialAtomOnePhaseTail a z

lemma exp_neg_half_mul_thetaCuspTailPotentialAtom_zero (a : ℝ) :
    Real.exp (-a / 2) *
        (4 * thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial 0) 1 a) =
      4 * Real.exp (-Real.pi * Real.exp (2 * a)) := by
  simp [thetaCuspPolynomialAtom, thetaCuspTailDerivativePolynomial]
  rw [show Real.exp a ^ 2 = Real.exp (2 * a) by
    rw [pow_two, ← Real.exp_add]; congr 1; ring]
  rw [show Real.exp (-a / 2) *
      (4 * (Real.exp (a / 2) * Real.exp (-(Real.pi * Real.exp (2 * a))))) =
      4 * (Real.exp (-a / 2) * Real.exp (a / 2)) *
        Real.exp (-(Real.pi * Real.exp (2 * a))) by ring,
    ← Real.exp_add]
  simp
  ring

lemma exp_neg_half_mul_thetaCuspTailPotentialAtom_one (a : ℝ) :
    Real.exp (-a / 2) *
        (4 * thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial 1) 1 a) =
      (2 - 8 * Real.pi * Real.exp (2 * a)) *
        Real.exp (-Real.pi * Real.exp (2 * a)) := by
  simp [thetaCuspPolynomialAtom, thetaCuspTailDerivativePolynomial,
    thetaCuspLogDerivativeStep]
  rw [show Real.exp a ^ 2 = Real.exp (2 * a) by
    rw [pow_two, ← Real.exp_add]; congr 1; ring]
  rw [show Real.exp (-a / 2) *
      (4 * (Real.exp (a / 2) * ((2 : ℝ)⁻¹ - 2 * Real.pi * Real.exp (2 * a)) *
        Real.exp (-(Real.pi * Real.exp (2 * a))))) =
      4 * ((2 : ℝ)⁻¹ - 2 * Real.pi * Real.exp (2 * a)) *
        (Real.exp (-a / 2) * Real.exp (a / 2)) *
          Real.exp (-(Real.pi * Real.exp (2 * a))) by ring,
    ← Real.exp_add]
  simp
  rw [show -a / 2 + a / 2 = 0 by ring, Real.exp_zero]
  ring

/-- After critical normalization, both source endpoint jets collapse to one explicit affine
spectral factor times the Gaussian `exp (-pi exp (2a))`.  All non-endpoint content carries the
common factor `-z^2`. -/
theorem criticalNormalized_densityPhaseTail_eq_endpoint_sub_sq_potential
    {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : 0 ≤ z.im) :
    (Real.exp (-a / 2) : ℂ) * spectralTranslationPhase (-a) z *
        thetaCuspTailSecondDensityAtomOnePhaseTail a z =
      (((8 * Real.pi * Real.exp (2 * a) - 2) *
          Real.exp (-Real.pi * Real.exp (2 * a)) : ℝ) : ℂ) +
        (4 : ℂ) * I * z *
          (Real.exp (-Real.pi * Real.exp (2 * a)) : ℂ) -
        z ^ 2 * thetaCuspTailPotentialAtomNormalizedPhaseTail a z := by
  rw [thetaCuspTailSecondDensityAtomOnePhaseTail_eq_boundary_sub_sq_potential ha hz]
  have hphase : spectralTranslationPhase (-a) z * spectralTranslationPhase a z = 1 := by
    have h := spectralTranslationPhase_sub a a z
    simpa [spectralTranslationPhase] using h.symm
  rw [show (Real.exp (-a / 2) : ℂ) * spectralTranslationPhase (-a) z *
      (-spectralTranslationPhase a z *
        ((4 * thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial 1) 1 a : ℝ) : ℂ) +
       I * z * spectralTranslationPhase a z *
        ((4 * thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial 0) 1 a : ℝ) : ℂ) -
       z ^ 2 * thetaCuspTailPotentialAtomOnePhaseTail a z) =
      -(spectralTranslationPhase (-a) z * spectralTranslationPhase a z) *
          ((Real.exp (-a / 2) : ℂ) *
            ((4 * thetaCuspPolynomialAtom
              (thetaCuspTailDerivativePolynomial 1) 1 a : ℝ) : ℂ)) +
        I * z * (spectralTranslationPhase (-a) z * spectralTranslationPhase a z) *
          ((Real.exp (-a / 2) : ℂ) *
            ((4 * thetaCuspPolynomialAtom
              (thetaCuspTailDerivativePolynomial 0) 1 a : ℝ) : ℂ)) -
        z ^ 2 * thetaCuspTailPotentialAtomNormalizedPhaseTail a z by
      unfold thetaCuspTailPotentialAtomNormalizedPhaseTail
      ring]
  rw [hphase]
  norm_num only [neg_mul, one_mul]
  rw [show (Real.exp (-a / 2) : ℂ) *
        ((4 * thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial 0) 1 a : ℝ) : ℂ) =
      ((Real.exp (-a / 2) * (4 * thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial 0) 1 a) : ℝ) : ℂ) by push_cast; rfl,
    show (Real.exp (-a / 2) : ℂ) *
        ((4 * thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial 1) 1 a : ℝ) : ℂ) =
      ((Real.exp (-a / 2) * (4 * thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial 1) 1 a) : ℝ) : ℂ) by push_cast; rfl,
    exp_neg_half_mul_thetaCuspTailPotentialAtom_zero,
    exp_neg_half_mul_thetaCuspTailPotentialAtom_one]
  push_cast
  ring_nf

end
end RHTower
