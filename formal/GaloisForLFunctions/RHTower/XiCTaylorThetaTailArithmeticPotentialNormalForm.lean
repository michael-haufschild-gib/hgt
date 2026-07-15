import GaloisForLFunctions.RHTower.XiCTaylorThetaTailMonotonePacketCurrent

/-!
# Arithmetic potential normal form of one theta-density atom

Two integrations by parts identify the exact endpoint jet and the completion-potential remainder
of every critically normalized arithmetic density atom.  The value and spectral-derivative
relations are kept together; no term is estimated or assigned a sign.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Spectral derivative of the critically normalized raw-potential tail.  The displacement
`u - a` includes the derivative of the normalizing phase at the moving endpoint. -/
def thetaCuspTailPotentialAtomNormalizedPhaseTailDerivative
    (a : ℝ) (z : ℂ) : ℂ :=
  (Real.exp (-a / 2) : ℂ) * spectralTranslationPhase (-a) z *
    ∫ u : ℝ in Ioi a,
      ((4 * thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial 0) 1 u : ℝ) : ℂ) *
        (((u - a : ℝ) : ℂ) * I * spectralTranslationPhase u z)

private theorem integrableOn_pow_four_thetaCuspTailDerivativeAtom_one_mul_phase
    (k m : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    IntegrableOn (fun u : ℝ =>
      ((u ^ k * (4 * thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial m) 1 u) : ℝ) : ℂ) *
          spectralTranslationPhase u z) (Ioi 0) := by
  have hreal : IntegrableOn (fun u : ℝ =>
      u ^ k * (4 * thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial m) 1 u)) (Ioi 0) := by
    have h : IntegrableOn (fun u : ℝ =>
        4 * (u ^ k * thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial m) 1 u)) (Ioi 0) :=
      (integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
        k (thetaCuspTailDerivativePolynomial m) (by omega : 0 < 1)).const_mul 4
    refine h.congr (Eventually.of_forall fun u => ?_)
    ring
  exact integrableOn_ofReal_mul_spectralTranslationPhase hreal hz

private theorem tendsto_pow_four_thetaCuspTailDerivativeAtom_one_mul_phase_atTop_zero
    (k m : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    Tendsto (fun u : ℝ =>
      spectralTranslationPhase u z *
        ((u ^ k * (4 * thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial m) 1 u) : ℝ) : ℂ))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbaseReal :=
    pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
      k (thetaCuspTailDerivativePolynomial m) (by omega : 0 < 1)
  have hbase : Tendsto (fun u : ℝ =>
      4 * ‖((u ^ k * thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial m) 1 u : ℝ) : ℂ)‖)
      atTop (nhds 0) := by
    simpa using (hbaseReal.ofReal.norm.const_mul 4)
  apply squeeze_zero' (Eventually.of_forall fun u => norm_nonneg _) ?_ hbase
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  have hp := norm_spectralTranslationPhase_le_one hu hz
  calc
    ‖spectralTranslationPhase u z *
        ((u ^ k * (4 * thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial m) 1 u) : ℝ) : ℂ)‖ =
      ‖spectralTranslationPhase u z‖ *
        ‖((u ^ k * (4 * thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial m) 1 u) : ℝ) : ℂ)‖ := norm_mul _ _
    _ ≤ 1 * ‖((u ^ k * (4 * thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial m) 1 u) : ℝ) : ℂ)‖ := by
      gcongr
    _ = 4 * ‖((u ^ k * thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial m) 1 u : ℝ) : ℂ)‖ := by
      simp only [Complex.norm_real, Real.norm_eq_abs]
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      rw [abs_mul]
      ring

/-- Derivative-level companion of the normalized potential-jet identity. -/
theorem criticalNormalized_densityPhaseTailDerivative_eq_endpoint_sub_sq_potential
    {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : 0 ≤ z.im) :
    (Real.exp (-a / 2) : ℂ) * spectralTranslationPhase (-a) z *
        (thetaCuspTailSecondDensityAtomOnePhaseTailDerivative a z -
          ((a : ℂ) * I) * thetaCuspTailSecondDensityAtomOnePhaseTail a z) =
      (4 : ℂ) * I *
          (Real.exp (-Real.pi * Real.exp (2 * a)) : ℂ) -
        2 * z * thetaCuspTailPotentialAtomNormalizedPhaseTail a z -
        z ^ 2 * thetaCuspTailPotentialAtomNormalizedPhaseTailDerivative a z := by
  let f : ℝ → ℂ := fun u =>
    ((4 * thetaCuspPolynomialAtom
      (thetaCuspTailDerivativePolynomial 0) 1 u : ℝ) : ℂ)
  let f' : ℝ → ℂ := fun u =>
    ((4 * thetaCuspPolynomialAtom
      (thetaCuspTailDerivativePolynomial 1) 1 u : ℝ) : ℂ)
  let f'' : ℝ → ℂ := fun u =>
    (thetaCuspTailSecondDensityAtom 1 u : ℂ)
  let g : ℝ → ℂ := fun u =>
    ((u - a : ℝ) : ℂ) * I * spectralTranslationPhase u z
  let g' : ℝ → ℂ := fun u =>
    I * spectralTranslationPhase u z -
      ((u - a : ℝ) : ℂ) * z * spectralTranslationPhase u z
  let g'' : ℝ → ℂ := fun u =>
    -2 * z * spectralTranslationPhase u z -
      ((u - a : ℝ) : ℂ) * I * z ^ 2 * spectralTranslationPhase u z
  have hf (u : ℝ) : HasDerivAt f (f' u) u := by
    dsimp [f, f']
    simpa only [thetaCuspTailDerivativePolynomial] using
      ((hasDerivAt_thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial 0) 1 u).const_mul 4).ofReal_comp
  have hf' (u : ℝ) : HasDerivAt f' (f'' u) u := by
    dsimp [f', f'']
    simpa only [thetaCuspTailSecondDensityAtom,
      thetaCuspTailDerivativePolynomial] using
      ((hasDerivAt_thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial 1) 1 u).const_mul 4).ofReal_comp
  have hg (u : ℝ) : HasDerivAt g (g' u) u := by
    have hlinear : HasDerivAt (fun v : ℝ => (((v - a : ℝ) : ℂ) * I)) I u := by
      convert (((Complex.ofRealCLM.hasDerivAt (x := u)).sub_const (a : ℂ)).mul_const I)
        using 1 <;>
        simp [Complex.ofRealCLM_apply]
    convert hlinear.mul (hasDerivAt_spectralTranslationPhase_source z u) using 1
    dsimp [g, g']
    ring_nf
    rw [I_sq]
    ring
  have hg' (u : ℝ) : HasDerivAt g' (g'' u) u := by
    have hp := hasDerivAt_spectralTranslationPhase_source z u
    have hlinear : HasDerivAt
        (fun v : ℝ => (((v - a : ℝ) : ℂ) * z)) z u := by
      convert (((Complex.ofRealCLM.hasDerivAt (x := u)).sub_const (a : ℂ)).mul_const z)
        using 1 <;>
        simp [Complex.ofRealCLM_apply]
    convert (hp.const_mul I).sub (hlinear.mul hp) using 1
    dsimp [g', g'']
    ring_nf
    rw [I_sq]
    ring
  have hmoment (m k : ℕ) : IntegrableOn (fun u : ℝ =>
      ((u ^ k * (4 * thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial m) 1 u) : ℝ) : ℂ) *
          spectralTranslationPhase u z) (Ioi a) :=
    (integrableOn_pow_four_thetaCuspTailDerivativeAtom_one_mul_phase k m hz).mono_set
      (Ioi_subset_Ioi ha)
  have hgf'' : IntegrableOn (g * f'') (Ioi a) := by
    have h1 := (hmoment 2 1).const_mul I
    have h0 := (hmoment 2 0).const_mul ((a : ℂ) * I)
    refine (h1.sub h0).congr (Eventually.of_forall fun u => ?_)
    dsimp [g, f'', thetaCuspTailSecondDensityAtom]
    push_cast
    simp only [pow_one, Pi.mul_apply]
    ring
  have hg'f' : IntegrableOn (g' * f') (Ioi a) := by
    have h0i := (hmoment 1 0).const_mul I
    have h1z := (hmoment 1 1).const_mul z
    have h0az := (hmoment 1 0).const_mul ((a : ℂ) * z)
    refine ((h0i.sub h1z).add h0az).congr (Eventually.of_forall fun u => ?_)
    dsimp [g', f']
    push_cast
    simp only [pow_one, Pi.mul_apply]
    ring
  have hg''f : IntegrableOn (g'' * f) (Ioi a) := by
    have h0z := (hmoment 0 0).const_mul (-2 * z)
    have h1z := (hmoment 0 1).const_mul (-(I * z ^ 2))
    have h0az := (hmoment 0 0).const_mul ((a : ℂ) * I * z ^ 2)
    refine ((h0z.add h1z).add h0az).congr (Eventually.of_forall fun u => ?_)
    dsimp [g'', f]
    push_cast
    simp only [pow_one, Pi.mul_apply]
    ring
  have hzero1 : Tendsto (g * f') (nhdsWithin a (Ioi a)) (nhds 0) := by
    have h := (hg a).continuousAt.mul (hf' a).continuousAt
    simpa [g] using h.tendsto.mono_left inf_le_left
  have hzero2 : Tendsto (g' * f) (nhdsWithin a (Ioi a))
      (nhds (I * spectralTranslationPhase a z * f a)) := by
    have h := (hg' a).continuousAt.mul (hf a).continuousAt
    simpa [g'] using h.tendsto.mono_left inf_le_left
  have htail (m k : ℕ) : Tendsto (fun u : ℝ =>
      spectralTranslationPhase u z *
        ((u ^ k * (4 * thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial m) 1 u) : ℝ) : ℂ))
      atTop (nhds 0) :=
    tendsto_pow_four_thetaCuspTailDerivativeAtom_one_mul_phase_atTop_zero k m hz
  have hinfty1 : Tendsto (g * f') atTop (nhds 0) := by
    have h1 := (htail 1 1).const_mul I
    have h0 := (htail 1 0).const_mul ((a : ℂ) * I)
    convert h1.sub h0 using 1
    · funext u
      dsimp [g, f']
      push_cast
      simp only [pow_one, Pi.mul_apply]
      ring
    · simp
  have hinfty2 : Tendsto (g' * f) atTop (nhds 0) := by
    have h0i := (htail 0 0).const_mul I
    have h1z := (htail 0 1).const_mul z
    have h0az := (htail 0 0).const_mul ((a : ℂ) * z)
    convert (h0i.sub h1z).add h0az using 1
    · funext u
      dsimp [g', f]
      push_cast
      simp only [pow_one, Pi.mul_apply]
      ring
    · simp
  have hibp := integral_Ioi_secondDerivative_mul_eq_boundary_add
    (a := a) (f := f) (f' := f') (f'' := f'')
    (g := g) (g' := g') (g'' := g'')
    (A₁ := 0) (B₁ := 0)
    (A₂ := I * spectralTranslationPhase a z * f a) (B₂ := 0)
    (fun u _hu => hf u) (fun u _hu => hf' u)
    (fun u _hu => hg u) (fun u _hu => hg' u)
    hgf'' hg'f' hg''f hzero1 hinfty1 hzero2 hinfty2
  have hpotential : IntegrableOn (fun u : ℝ =>
      f u * spectralTranslationPhase u z) (Ioi a) := by
    convert hmoment 0 0 using 1
    funext u
    simp [f]
  have hpotentialD : IntegrableOn (fun u : ℝ =>
      f u * (((u - a : ℝ) : ℂ) * I * spectralTranslationPhase u z))
      (Ioi a) := by
    have h1 := (hmoment 0 1).const_mul I
    have h0 := (hmoment 0 0).const_mul ((a : ℂ) * I)
    refine (h1.sub h0).congr (Eventually.of_forall fun u => ?_)
    dsimp [f]
    push_cast
    simp only [pow_one]
    ring
  have hremainder : (∫ u : ℝ in Ioi a, f u * g'' u) =
      -2 * z * (∫ u : ℝ in Ioi a,
        f u * spectralTranslationPhase u z) -
      z ^ 2 * (∫ u : ℝ in Ioi a,
        f u * (((u - a : ℝ) : ℂ) * I * spectralTranslationPhase u z)) := by
    rw [show (fun u : ℝ => f u * g'' u) = fun u : ℝ =>
        (-2 * z) * (f u * spectralTranslationPhase u z) -
          z ^ 2 * (f u * (((u - a : ℝ) : ℂ) * I *
            spectralTranslationPhase u z)) by
      funext u
      dsimp [g'']
      ring,
      integral_sub (hpotential.const_mul (-2 * z))
        (hpotentialD.const_mul (z ^ 2)),
      integral_const_mul, integral_const_mul]
  rw [hremainder] at hibp
  have hleft :
      thetaCuspTailSecondDensityAtomOnePhaseTailDerivative a z -
          ((a : ℂ) * I) * thetaCuspTailSecondDensityAtomOnePhaseTail a z =
        ∫ u : ℝ in Ioi a, f'' u * g u := by
    unfold thetaCuspTailSecondDensityAtomOnePhaseTailDerivative
      thetaCuspTailSecondDensityAtomOnePhaseTail
    rw [← integral_const_mul]
    rw [← integral_sub]
    · apply integral_congr_ae
      filter_upwards [] with u
      dsimp [f'', g]
      push_cast
      ring
    · exact (integrableOn_thetaCuspTailSecondDensityAtom_one_mul_phaseDerivative hz).mono_set
        (Ioi_subset_Ioi ha)
    · exact ((integrableOn_thetaCuspTailSecondDensityAtom_one_mul_phase hz).mono_set
        (Ioi_subset_Ioi ha)).const_mul ((a : ℂ) * I)
  rw [hleft, hibp]
  have hphase : spectralTranslationPhase (-a) z * spectralTranslationPhase a z = 1 := by
    have h := spectralTranslationPhase_sub a a z
    simpa [spectralTranslationPhase] using h.symm
  unfold thetaCuspTailPotentialAtomNormalizedPhaseTail
    thetaCuspTailPotentialAtomNormalizedPhaseTailDerivative
    thetaCuspTailPotentialAtomOnePhaseTail
  dsimp only [f]
  simp only [sub_zero, zero_sub, neg_neg, zero_add]
  have hendpoint :
      (Real.exp (-a / 2) : ℂ) * spectralTranslationPhase (-a) z *
          (I * spectralTranslationPhase a z *
            ((4 * thetaCuspPolynomialAtom
              (thetaCuspTailDerivativePolynomial 0) 1 a : ℝ) : ℂ)) =
        (4 : ℂ) * I *
          (Real.exp (-Real.pi * Real.exp (2 * a)) : ℂ) := by
    rw [show (Real.exp (-a / 2) : ℂ) * spectralTranslationPhase (-a) z *
        (I * spectralTranslationPhase a z *
          ((4 * thetaCuspPolynomialAtom
            (thetaCuspTailDerivativePolynomial 0) 1 a : ℝ) : ℂ)) =
      I * (spectralTranslationPhase (-a) z * spectralTranslationPhase a z) *
        ((Real.exp (-a / 2) : ℂ) *
          ((4 * thetaCuspPolynomialAtom
            (thetaCuspTailDerivativePolynomial 0) 1 a : ℝ) : ℂ)) by ring,
      hphase]
    norm_num only [one_mul]
    rw [show (Real.exp (-a / 2) : ℂ) *
        ((4 * thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial 0) 1 a : ℝ) : ℂ) =
      ((Real.exp (-a / 2) * (4 * thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial 0) 1 a) : ℝ) : ℂ) by push_cast; rfl,
    exp_neg_half_mul_thetaCuspTailPotentialAtom_zero]
    push_cast
    ring
  rw [show (Real.exp (-a / 2) : ℂ) * spectralTranslationPhase (-a) z *
      (I * spectralTranslationPhase a z *
          ((4 * thetaCuspPolynomialAtom
            (thetaCuspTailDerivativePolynomial 0) 1 a : ℝ) : ℂ) +
        ((-2 * z * (∫ u : ℝ in Ioi a,
          ((4 * thetaCuspPolynomialAtom
            (thetaCuspTailDerivativePolynomial 0) 1 u : ℝ) : ℂ) *
              spectralTranslationPhase u z)) -
        z ^ 2 * (∫ u : ℝ in Ioi a,
          ((4 * thetaCuspPolynomialAtom
            (thetaCuspTailDerivativePolynomial 0) 1 u : ℝ) : ℂ) *
              (((u - a : ℝ) : ℂ) * I * spectralTranslationPhase u z)))) =
      ((Real.exp (-a / 2) : ℂ) * spectralTranslationPhase (-a) z *
        (I * spectralTranslationPhase a z *
          ((4 * thetaCuspPolynomialAtom
            (thetaCuspTailDerivativePolynomial 0) 1 a : ℝ) : ℂ))) -
        2 * z * ((Real.exp (-a / 2) : ℂ) * spectralTranslationPhase (-a) z *
          (∫ u : ℝ in Ioi a,
            ((4 * thetaCuspPolynomialAtom
              (thetaCuspTailDerivativePolynomial 0) 1 u : ℝ) : ℂ) *
                spectralTranslationPhase u z)) -
        z ^ 2 * ((Real.exp (-a / 2) : ℂ) * spectralTranslationPhase (-a) z *
          (∫ u : ℝ in Ioi a,
            ((4 * thetaCuspPolynomialAtom
              (thetaCuspTailDerivativePolynomial 0) 1 u : ℝ) : ℂ) *
                (((u - a : ℝ) : ℂ) * I * spectralTranslationPhase u z))) by ring,
    hendpoint]
  ring

/-- The critically normalized phase transform of the `n`-th arithmetic atom has an explicit
affine endpoint jet and one `z^2`-weighted potential tail. -/
theorem thetaCuspTailSecondDensityAtomPhase_eq_arithmeticEndpoint_sub_sq_potential
    {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : 0 ≤ z.im) :
    thetaCuspTailSecondDensityAtomPhase n z =
      (((8 * Real.pi * ((n : ℝ) ^ 2) - 2) *
          Real.exp (-Real.pi * ((n : ℝ) ^ 2)) : ℝ) : ℂ) +
        (4 : ℂ) * I * z *
          (Real.exp (-Real.pi * ((n : ℝ) ^ 2)) : ℂ) -
        z ^ 2 * thetaCuspTailPotentialAtomNormalizedPhaseTail (Real.log n) z := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrpow : (n : ℝ) ^ (-(1 / 2 : ℝ)) = Real.exp (-Real.log n / 2) := by
    rw [Real.rpow_def_of_pos hnR]
    congr 1
    ring
  have hexp : Real.exp (2 * Real.log (n : ℝ)) = (n : ℝ) ^ 2 := by
    rw [show 2 * Real.log (n : ℝ) =
        Real.log (n : ℝ) + Real.log (n : ℝ) by ring,
      Real.exp_add, Real.exp_log hnR]
    ring
  rw [thetaCuspTailSecondDensityAtomPhase_eq_centeredTail hn, hrpow]
  rw [criticalNormalized_densityPhaseTail_eq_endpoint_sub_sq_potential
    (Real.log_nonneg (by exact_mod_cast hn)) hz, hexp]

/-- Spectral-derivative companion of the arithmetic potential normal form. -/
theorem thetaCuspTailSecondDensityAtomPhaseDerivative_eq_arithmeticEndpoint_sub_sq_potential
    {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : 0 ≤ z.im) :
    thetaCuspTailSecondDensityAtomPhaseDerivative n z =
      (4 : ℂ) * I *
          (Real.exp (-Real.pi * ((n : ℝ) ^ 2)) : ℂ) -
        2 * z * thetaCuspTailPotentialAtomNormalizedPhaseTail (Real.log n) z -
        z ^ 2 *
          thetaCuspTailPotentialAtomNormalizedPhaseTailDerivative (Real.log n) z := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrpow : (n : ℝ) ^ (-(1 / 2 : ℝ)) = Real.exp (-Real.log n / 2) := by
    rw [Real.rpow_def_of_pos hnR]
    congr 1
    ring
  have hexp : Real.exp (2 * Real.log (n : ℝ)) = (n : ℝ) ^ 2 := by
    rw [show 2 * Real.log (n : ℝ) =
        Real.log (n : ℝ) + Real.log (n : ℝ) by ring,
      Real.exp_add, Real.exp_log hnR]
    ring
  rw [thetaCuspTailSecondDensityAtomPhaseDerivative_eq_centeredTail hn z hz, hrpow]
  rw [criticalNormalized_densityPhaseTailDerivative_eq_endpoint_sub_sq_potential
    (Real.log_nonneg (by exact_mod_cast hn)) hz, hexp]

end

end RHTower
