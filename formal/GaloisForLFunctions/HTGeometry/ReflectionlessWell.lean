import GaloisForLFunctions.HTGeometry.ChargedWaveFlux
import GaloisForLFunctions.HTGeometry.QLadderTransmission
import GaloisForLFunctions.HTGeometry.NoncommutativeQubitResponsePolarization

/-!
# A negative-well scattering wave realizing the ladder transmission factor

Applies the neutral no-superradiance result and Wronskian interpretation of
arXiv:2608.21406v1 to an explicitly constructed smooth Pöschl--Teller well.
The Darboux amplitude uses the existing dark-soliton profiles. Its wave solves
the actual second-order radial equation; the potential is strictly negative;
and its Noether current is exactly the positive incident momentum everywhere.

The qubit-response tanh limit proves both asymptotic channels. Field and first
derivative have a unit incident coefficient and a pure transmitted coefficient
of modulus one. That coefficient is identified with the existing geometric
ladder's one-shell factor. Thus this realizes one transmission factor by an
actual scattering solution; no infinite-ladder potential construction is
asserted. No wave-equation or scattering-boundary hypotheses are assumed.
-/

noncomputable section
open Complex Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open DispersivePDE

def reflectionlessWellPotential (l x : ℝ) : ℝ := -2 * Real.exp l ^ 2 * solitonQ (Real.exp l * x)

def reflectionlessWellAmplitude (k l x : ℝ) : ℂ :=
  (I * (Real.exp k : ℂ) - (Real.exp l : ℂ) * (solitonT (Real.exp l * x) : ℂ)) / (I * (Real.exp k : ℂ) + (Real.exp l : ℂ))

def reflectionlessWellAmplitude1 (k l x : ℝ) : ℂ :=
  (-(Real.exp l : ℂ) ^ 2 * (solitonQ (Real.exp l * x) : ℂ)) / (I * (Real.exp k : ℂ) + (Real.exp l : ℂ))

def reflectionlessWellAmplitude2 (k l x : ℝ) : ℂ :=
  (-(Real.exp l : ℂ) ^ 3 * (solitonQ1 (Real.exp l * x) : ℂ)) / (I * (Real.exp k : ℂ) + (Real.exp l : ℂ))

def reflectionlessWellWave (k l x : ℝ) : ℂ :=
  reflectionlessWellAmplitude k l x * FDNLS.staggerPhase (-Real.exp k) x

def reflectionlessWellWave1 (k l x : ℝ) : ℂ :=
  (reflectionlessWellAmplitude1 k l x + I * (Real.exp k : ℂ) * reflectionlessWellAmplitude k l x) *
    FDNLS.staggerPhase (-Real.exp k) x

theorem reflectionlessWellPotential_neg (l x : ℝ) : reflectionlessWellPotential l x < 0 := by
  rw [reflectionlessWellPotential, solitonQ_eq_inv_cosh_sq]
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos (exp_pos l)))
    (one_div_pos.mpr (sq_pos_of_pos (cosh_pos _)))

theorem reflectionlessWell_denominator_ne_zero (k l : ℝ) :
    I * (Real.exp k : ℂ) + (Real.exp l : ℂ) ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, zero_mul, mul_zero, sub_zero, zero_add, zero_re] at hr
  exact (Real.exp_ne_zero l) hr

theorem reflectionlessWellAmplitude_derivative (k l x : ℝ) :
    HasDerivAt (reflectionlessWellAmplitude k l) (reflectionlessWellAmplitude1 k l x) x := by
  have h := (((((hasDerivAt_solitonT (Real.exp l * x)).comp x
    ((hasDerivAt_id x).const_mul (Real.exp l))).ofReal_comp).const_mul (Real.exp l : ℂ)).const_sub
      (I * (Real.exp k : ℂ))).div_const (I * (Real.exp k : ℂ) + (Real.exp l : ℂ))
  apply h.congr_deriv
  dsimp [reflectionlessWellAmplitude1]
  push_cast
  ring

theorem reflectionlessWellAmplitude1_derivative (k l x : ℝ) :
    HasDerivAt (reflectionlessWellAmplitude1 k l) (reflectionlessWellAmplitude2 k l x) x := by
  have h := ((((hasDerivAt_solitonQ (Real.exp l * x)).comp x
    ((hasDerivAt_id x).const_mul (Real.exp l))).ofReal_comp).const_mul (-(Real.exp l : ℂ) ^ 2)).div_const
      (I * (Real.exp k : ℂ) + (Real.exp l : ℂ))
  apply h.congr_deriv
  dsimp [reflectionlessWellAmplitude2]
  push_cast
  ring

/-- Exact Darboux amplitude identity over the corpus's dark-soliton profile. -/
theorem reflectionlessWellAmplitude_darboux (k l x : ℝ) :
    reflectionlessWellAmplitude2 k l x +
      2 * I * (Real.exp k : ℂ) * reflectionlessWellAmplitude1 k l x +
        2 * (Real.exp l : ℂ) ^ 2 * (solitonQ (Real.exp l * x) : ℂ) * reflectionlessWellAmplitude k l x = 0 := by
  unfold reflectionlessWellAmplitude2 reflectionlessWellAmplitude1 reflectionlessWellAmplitude solitonQ1
  push_cast
  ring

theorem reflectionlessWellWave_derivative (k l x : ℝ) :
    HasDerivAt (reflectionlessWellWave k l) (reflectionlessWellWave1 k l x) x := by
  have h := (reflectionlessWellAmplitude_derivative k l x).mul (FDNLS.hasDerivAt_staggerPhase (-Real.exp k) x)
  apply h.congr_deriv
  simp only [reflectionlessWellWave1, Complex.ofReal_neg]
  ring

theorem reflectionlessWellWave1_derivative (k l x : ℝ) :
    HasDerivAt (reflectionlessWellWave1 k l)
      (-((Real.exp k : ℂ) ^ 2 - (reflectionlessWellPotential l x : ℂ)) * reflectionlessWellWave k l x) x := by
  have h := ((reflectionlessWellAmplitude1_derivative k l x).add
    ((reflectionlessWellAmplitude_derivative k l x).const_mul (I * (Real.exp k : ℂ)))).mul
      (FDNLS.hasDerivAt_staggerPhase (-Real.exp k) x)
  apply h.congr_deriv
  simp only [Complex.ofReal_neg, reflectionlessWellWave, reflectionlessWellPotential, Pi.add_apply,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
  have hd := reflectionlessWellAmplitude_darboux k l x
  linear_combination FDNLS.staggerPhase (-Real.exp k) x * hd +
    ((Real.exp k : ℂ) ^ 2 * reflectionlessWellAmplitude k l x * FDNLS.staggerPhase (-Real.exp k) x) * I_sq

/-- A genuine smooth scattering wave solves the negative-well radial equation. -/
theorem reflectionlessWellWave_equation (k l x : ℝ) :
    deriv (deriv (reflectionlessWellWave k l)) x +
      ((Real.exp k : ℂ) ^ 2 - (reflectionlessWellPotential l x : ℂ)) * reflectionlessWellWave k l x = 0 := by
  have he : deriv (reflectionlessWellWave k l) = reflectionlessWellWave1 k l :=
    funext (fun y => (reflectionlessWellWave_derivative k l y).deriv)
  rw [he, (reflectionlessWellWave1_derivative k l x).deriv]
  ring

/-- Exact current of the Darboux amplitude, including its spatial derivative. -/
theorem reflectionlessWellAmplitude_flux (k l x : ℝ) :
    ((starRingEnd ℂ) (reflectionlessWellAmplitude k l x) *
      (reflectionlessWellAmplitude1 k l x + I * (Real.exp k : ℂ) * reflectionlessWellAmplitude k l x)).im = Real.exp k := by
  simp only [reflectionlessWellAmplitude, reflectionlessWellAmplitude1, solitonQ, pow_two,
    Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, zero_sub,
    add_zero, zero_add, one_mul, neg_zero]
  have hn : Real.exp l * Real.exp l + Real.exp k * Real.exp k ≠ 0 := by positivity
  field_simp
  ring

/-- The actual flux stays equal to incident momentum throughout the negative well. -/
theorem reflectionlessWellWave_flux (k l x : ℝ) :
    complexRadialFlux (reflectionlessWellWave k l) x = Real.exp k := by
  rw [complexRadialFlux, (reflectionlessWellWave_derivative k l x).deriv,
    reflectionlessWellWave, reflectionlessWellWave1, map_mul]
  have he : (starRingEnd ℂ) (reflectionlessWellAmplitude k l x) *
      (starRingEnd ℂ) (FDNLS.staggerPhase (-Real.exp k) x) *
      ((reflectionlessWellAmplitude1 k l x + I * (Real.exp k : ℂ) * reflectionlessWellAmplitude k l x) *
        FDNLS.staggerPhase (-Real.exp k) x) =
      ((starRingEnd ℂ) (reflectionlessWellAmplitude k l x) *
        (reflectionlessWellAmplitude1 k l x + I * (Real.exp k : ℂ) * reflectionlessWellAmplitude k l x)) *
      ((starRingEnd ℂ) (FDNLS.staggerPhase (-Real.exp k) x) * FDNLS.staggerPhase (-Real.exp k) x) := by ring
  rw [he, FDNLS.staggerPhase_conj_mul, mul_one, reflectionlessWellAmplitude_flux]

theorem reflectionlessWellWave_flux_conserved (k l x : ℝ) :
    HasDerivAt (complexRadialFlux (reflectionlessWellWave k l)) 0 x := by
  simp only [funext (reflectionlessWellWave_flux k l)]
  exact hasDerivAt_const x _

def reflectionlessWellTransmission (k l : ℝ) : ℂ :=
  (I * (Real.exp k : ℂ) - (Real.exp l : ℂ)) / (I * (Real.exp k : ℂ) + (Real.exp l : ℂ))

/-- The transmitted amplitude has unit modulus, independently of well depth. -/
theorem reflectionlessWellTransmission_norm (k l : ℝ) : ‖reflectionlessWellTransmission k l‖ = 1 := by
  have he : I * (Real.exp k : ℂ) - (Real.exp l : ℂ) =
      -(starRingEnd ℂ) (I * (Real.exp k : ℂ) + (Real.exp l : ℂ)) := by
    simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [reflectionlessWellTransmission, norm_div, he]
  simp only [norm_neg, Complex.norm_conj]
  exact div_self (norm_ne_zero_iff.mpr (reflectionlessWell_denominator_ne_zero k l))

/-- The existing ladder factor is realized by an actual smooth scattering wave. -/
theorem reflectionlessWellTransmission_ladder_factor (k l : ℝ) (q : ℂ) :
    reflectionlessWellTransmission k l =
      qLadderFactor q (I * (Real.exp l : ℂ) / (Real.exp k : ℂ)) 0 := by
  have hk : (Real.exp k : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero k
  have hd : (Real.exp k : ℂ) - I * (Real.exp l : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    exact Real.exp_ne_zero k hr
  rw [← qLadderFactor_momentum (q := q) (kappa := (Real.exp l : ℂ)) (k := (Real.exp k : ℂ)) hk 0]
  simp only [pow_zero, mul_one]
  unfold reflectionlessWellTransmission
  have hn := reflectionlessWell_denominator_ne_zero k l
  field_simp
  linear_combination -2 * (Real.exp k : ℂ) * (Real.exp l : ℂ) * I_sq

private theorem reflectionlessWell_tanh_atTop (l : ℝ) :
    Tendsto (fun x => solitonT (Real.exp l * x)) atTop (𝓝 1) := by
  simpa only [solitonT, Function.comp_def, id_eq] using
    tendsto_tanh_atTop_one.comp (tendsto_id.const_mul_atTop (Real.exp_pos l))

private theorem reflectionlessWell_tanh_atBot (l : ℝ) :
    Tendsto (fun x => solitonT (Real.exp l * x)) atBot (𝓝 (-1)) := by
  have h := (reflectionlessWell_tanh_atTop l).neg.comp tendsto_neg_atBot_atTop
  simpa only [Function.comp_def, solitonT, mul_neg, Real.tanh_neg, neg_neg] using h

/-- The incident amplitude is exactly one on the left end. -/
theorem reflectionlessWellAmplitude_atBot (k l : ℝ) :
    Tendsto (reflectionlessWellAmplitude k l) atBot (𝓝 1) := by
  have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp (reflectionlessWell_tanh_atBot l)
  have h := ((tendsto_const_nhds (x := I * (Real.exp k : ℂ))).sub (ht.const_mul (Real.exp l : ℂ))).div_const
    (I * (Real.exp k : ℂ) + (Real.exp l : ℂ))
  have hv : (I * (Real.exp k : ℂ) - (Real.exp l : ℂ) * ((-1 : ℝ) : ℂ)) /
      (I * (Real.exp k : ℂ) + (Real.exp l : ℂ)) = 1 := by
    simp only [Complex.ofReal_neg, Complex.ofReal_one, mul_neg_one, sub_neg_eq_add]
    exact div_self (reflectionlessWell_denominator_ne_zero k l)
  unfold reflectionlessWellAmplitude
  simpa only [Function.comp_def, hv] using h

/-- The right-end coefficient is the unimodular transmission factor. -/
theorem reflectionlessWellAmplitude_atTop (k l : ℝ) :
    Tendsto (reflectionlessWellAmplitude k l) atTop (𝓝 (reflectionlessWellTransmission k l)) := by
  have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp (reflectionlessWell_tanh_atTop l)
  have h := ((tendsto_const_nhds (x := I * (Real.exp k : ℂ))).sub (ht.const_mul (Real.exp l : ℂ))).div_const
    (I * (Real.exp k : ℂ) + (Real.exp l : ℂ))
  unfold reflectionlessWellAmplitude reflectionlessWellTransmission
  simpa only [Function.comp_def, Complex.ofReal_one, mul_one] using h

theorem reflectionlessWellWave_demodulation (k l x : ℝ) :
    reflectionlessWellWave k l x * FDNLS.staggerPhase (Real.exp k) x = reflectionlessWellAmplitude k l x := by
  have hp : FDNLS.staggerPhase (-Real.exp k) x * FDNLS.staggerPhase (Real.exp k) x = 1 := by
    simp [FDNLS.staggerPhase, ← Complex.exp_add]
  rw [reflectionlessWellWave, mul_assoc, hp, mul_one]

/-- Actual left scattering asymptote: no reflected channel is present. -/
theorem reflectionlessWellWave_incident_limit (k l : ℝ) :
    Tendsto (fun x => reflectionlessWellWave k l x * FDNLS.staggerPhase (Real.exp k) x) atBot (𝓝 1) := by
  simp only [reflectionlessWellWave_demodulation]
  exact reflectionlessWellAmplitude_atBot k l

/-- Actual right scattering asymptote of the constructed negative-well solution. -/
theorem reflectionlessWellWave_transmitted_limit (k l : ℝ) :
    Tendsto (fun x => reflectionlessWellWave k l x * FDNLS.staggerPhase (Real.exp k) x) atTop
      (𝓝 (reflectionlessWellTransmission k l)) := by
  simp only [reflectionlessWellWave_demodulation]
  exact reflectionlessWellAmplitude_atTop k l

private theorem reflectionlessWellAmplitude1_atTop (k l : ℝ) :
    Tendsto (reflectionlessWellAmplitude1 k l) atTop (𝓝 0) := by
  have hq := (tendsto_const_nhds (x := (1 : ℝ))).sub ((reflectionlessWell_tanh_atTop l).pow 2)
  simp only [one_pow, sub_self] at hq
  have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp hq
  have h := (ht.const_mul (-(Real.exp l : ℂ) ^ 2)).div_const (I * (Real.exp k : ℂ) + (Real.exp l : ℂ))
  unfold reflectionlessWellAmplitude1 solitonQ
  simpa only [Function.comp_def, Complex.ofReal_zero, mul_zero, zero_div] using h

private theorem reflectionlessWellAmplitude1_atBot (k l : ℝ) :
    Tendsto (reflectionlessWellAmplitude1 k l) atBot (𝓝 0) := by
  have hq := (tendsto_const_nhds (x := (1 : ℝ))).sub ((reflectionlessWell_tanh_atBot l).pow 2)
  simp only [neg_sq, one_pow, sub_self] at hq
  have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp hq
  have h := (ht.const_mul (-(Real.exp l : ℂ) ^ 2)).div_const (I * (Real.exp k : ℂ) + (Real.exp l : ℂ))
  unfold reflectionlessWellAmplitude1 solitonQ
  simpa only [Function.comp_def, Complex.ofReal_zero, mul_zero, zero_div] using h

theorem reflectionlessWellWave_derivative_demodulation (k l x : ℝ) :
    deriv (reflectionlessWellWave k l) x * FDNLS.staggerPhase (Real.exp k) x =
      reflectionlessWellAmplitude1 k l x + I * (Real.exp k : ℂ) * reflectionlessWellAmplitude k l x := by
  have hp : FDNLS.staggerPhase (-Real.exp k) x * FDNLS.staggerPhase (Real.exp k) x = 1 := by
    simp [FDNLS.staggerPhase, ← Complex.exp_add]
  rw [(reflectionlessWellWave_derivative k l x).deriv, reflectionlessWellWave1, mul_assoc, hp, mul_one]

/-- Both field and derivative have the pure incident asymptote. -/
theorem reflectionlessWellWave_incident_jet_limit (k l : ℝ) :
    Tendsto (fun x => reflectionlessWellWave k l x * FDNLS.staggerPhase (Real.exp k) x) atBot (𝓝 1) ∧
      Tendsto (fun x => deriv (reflectionlessWellWave k l) x * FDNLS.staggerPhase (Real.exp k) x) atBot
        (𝓝 (I * (Real.exp k : ℂ))) := by
  refine ⟨reflectionlessWellWave_incident_limit k l, ?_⟩
  simp only [reflectionlessWellWave_derivative_demodulation]
  simpa only [mul_one, zero_add] using (reflectionlessWellAmplitude1_atBot k l).add
    ((reflectionlessWellAmplitude_atBot k l).const_mul (I * (Real.exp k : ℂ)))

/-- Both field and derivative have the pure transmitted asymptote. -/
theorem reflectionlessWellWave_transmitted_jet_limit (k l : ℝ) :
    Tendsto (fun x => reflectionlessWellWave k l x * FDNLS.staggerPhase (Real.exp k) x) atTop
      (𝓝 (reflectionlessWellTransmission k l)) ∧
      Tendsto (fun x => deriv (reflectionlessWellWave k l) x * FDNLS.staggerPhase (Real.exp k) x) atTop
        (𝓝 (I * (Real.exp k : ℂ) * reflectionlessWellTransmission k l)) := by
  refine ⟨reflectionlessWellWave_transmitted_limit k l, ?_⟩
  simp only [reflectionlessWellWave_derivative_demodulation]
  simpa only [zero_add] using (reflectionlessWellAmplitude1_atTop k l).add
    ((reflectionlessWellAmplitude_atTop k l).const_mul (I * (Real.exp k : ℂ)))

end GaloisForLFunctions.HTGeometry
