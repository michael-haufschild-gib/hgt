import GaloisForLFunctions.RHTower.GammaVerticalPolar
import GaloisForLFunctions.RHTower.KapustinGaugeSmirnovCollision
import GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTAdaptiveOnShellOccurrenceNoGo

/-!
# FZZ balanced external-Gamma phase-recurrence no-go

At physical level `k = 4`, product of Halder--Jafferis opposite-winding external-leg Gamma
normalizations is a pure phase.  Exact Gamma recurrence reduces its unwrapped phase to

`4 * (gammaVerticalPhase (1/2) y + arctan (2y) + arctan (2y/3))`.

Corpus Gamma-phase asymptotics make this lift continuous and cofinal.  It therefore crosses
arbitrarily large integer multiples of `2π`, so complete complex amplitude returns exactly to its
wall value `1` at arbitrarily large nonzero radial momenta.  Since linear replica-area passivity
holds exactly at zero momentum, no pointwise predicate of this full amplitude can supply missing
FZZ-P passivity premise.

Positive survivor: unwrapped phase/history data or integrated Ward coupling, neither pointwise
complex amplitude nor its modulus.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

def fzzHJBalancedExternalGammaPhaseLift (y : ℝ) : ℝ :=
  4 * (gammaVerticalPhase (1 / 2) y +
    Real.arctan (2 * y) + Real.arctan (2 * y / 3))

theorem continuous_fzzHJBalancedExternalGammaPhaseLift :
    Continuous fzzHJBalancedExternalGammaPhaseLift := by
  unfold fzzHJBalancedExternalGammaPhaseLift
  have hphase : Continuous (gammaVerticalPhase (1 / 2)) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (hasDerivAt_gammaVerticalPhase (by norm_num) y).continuousAt
  fun_prop

theorem gammaVerticalPhase_half_tendsto_atTop :
    Tendsto (gammaVerticalPhase (1 / 2)) atTop atTop := by
  have hratio := tendsto_gammaVerticalPhase_ratio (by norm_num : (0 : ℝ) < 1 / 2)
  have hlogtop : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hscale : Tendsto (fun y : ℝ => y * Real.log y) atTop atTop :=
    Filter.Tendsto.atTop_mul_atTop₀ tendsto_id hlogtop
  have hprod := hratio.pos_mul_atTop (by norm_num : (0 : ℝ) < 1) hscale
  exact hprod.congr' <| by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
    have hy0 : y ≠ 0 := ne_of_gt (by linarith)
    have hlog0 : Real.log y ≠ 0 := (Real.log_pos hy).ne'
    field_simp

theorem fzzHJBalancedExternalGammaPhaseLift_tendsto_atTop :
    Tendsto fzzHJBalancedExternalGammaPhaseLift atTop atTop := by
  change Tendsto
    (fun y : ℝ => 4 * (gammaVerticalPhase (1 / 2) y +
      Real.arctan (2 * y) + Real.arctan (2 * y / 3))) atTop atTop
  have htwo : Tendsto (fun y : ℝ => 2 * y) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have htwoThirds : Tendsto (fun y : ℝ => 2 * y / 3) atTop atTop :=
    (tendsto_id.const_mul_atTop (by norm_num)).atTop_div_const (by norm_num)
  have hatan : Tendsto Real.arctan atTop (nhds (Real.pi / 2)) :=
    Real.tendsto_arctan_atTop.mono_right inf_le_left
  have hangle : Tendsto
      (fun y : ℝ => Real.arctan (2 * y) + Real.arctan (2 * y / 3))
      atTop (nhds (Real.pi / 2 + Real.pi / 2)) :=
    (hatan.comp htwo).add (hatan.comp htwoThirds)
  have hsum := gammaVerticalPhase_half_tendsto_atTop.atTop_add hangle
  have hmul := hsum.const_mul_atTop (by norm_num : (0 : ℝ) < 4)
  simpa only [add_assoc] using hmul

theorem fzzHJBalancedExternalGammaPhaseLift_cofinal_period
    (M : ℝ) :
    ∃ y : ℝ, M < y ∧ ∃ n : ℕ,
      fzzHJBalancedExternalGammaPhaseLift y = (n : ℝ) * (2 * Real.pi) := by
  obtain ⟨n, hn⟩ := exists_nat_gt
    (fzzHJBalancedExternalGammaPhaseLift M / (2 * Real.pi))
  let L : ℝ := (n : ℝ) * (2 * Real.pi)
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hML : fzzHJBalancedExternalGammaPhaseLift M < L := by
    dsimp [L]
    exact (div_lt_iff₀ hpi).mp hn
  have hev : ∀ᶠ T : ℝ in atTop,
      M < T ∧ L < fzzHJBalancedExternalGammaPhaseLift T :=
    (eventually_gt_atTop M).and
      (fzzHJBalancedExternalGammaPhaseLift_tendsto_atTop.eventually
        (eventually_gt_atTop L))
  obtain ⟨T, hMT, hLT⟩ := hev.exists
  have hcont : ContinuousOn fzzHJBalancedExternalGammaPhaseLift (Set.Icc M T) :=
    continuous_fzzHJBalancedExternalGammaPhaseLift.continuousOn
  have hmem : L ∈ Set.Icc
      (fzzHJBalancedExternalGammaPhaseLift M)
      (fzzHJBalancedExternalGammaPhaseLift T) := ⟨hML.le, hLT.le⟩
  obtain ⟨y, hy, hyL⟩ := (intermediate_value_Icc hMT.le hcont) hmem
  refine ⟨y, ?_, n, hyL⟩
  exact lt_of_le_of_ne hy.1 fun hEq => by
    subst y
    exact hML.ne hyL

def fzzHJBalancedExternalGammaAmplitude (P : ℝ) : ℂ :=
  fzzHJExternalGammaPlusNormalization 4 P *
    fzzHJExternalGammaMinusNormalization 4 P

theorem fzzHJBalancedExternalGammaAmplitude_eq_shiftProduct_div_conj (P : ℝ) :
    fzzHJBalancedExternalGammaAmplitude P =
      let z : ℂ := (1 / 2 : ℂ) + ((Real.sqrt 2 * P : ℝ) : ℂ) * I
      (Complex.Gamma (z + 2) * Complex.Gamma (z - 2)) /
        (starRingEnd ℂ) (Complex.Gamma (z + 2) * Complex.Gamma (z - 2)) := by
  simp only [fzzHJBalancedExternalGammaAmplitude,
    fzzHJExternalGammaPlusNormalization,
    fzzHJExternalGammaMinusNormalization,
    fzzHJExternalGammaPlusNumeratorArgument,
    fzzHJExternalGammaPlusDenominatorArgument,
    fzzHJExternalGammaMinusNumeratorArgument,
    fzzHJExternalGammaMinusDenominatorArgument,
    fzzHJPhysicalRadialLabel]
  have hplus :
      Complex.Gamma (((5 / 2 : ℝ) : ℂ) - (Real.sqrt 2 : ℂ) * (P : ℂ) * I) =
        (starRingEnd ℂ) (Complex.Gamma
          (((5 / 2 : ℝ) : ℂ) + (Real.sqrt 2 : ℂ) * (P : ℂ) * I)) := by
    rw [← Complex.Gamma_conj]
    congr 1
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hminus :
      Complex.Gamma (((-3 / 2 : ℝ) : ℂ) - (Real.sqrt 2 : ℂ) * (P : ℂ) * I) =
        (starRingEnd ℂ) (Complex.Gamma
          (((-3 / 2 : ℝ) : ℂ) + (Real.sqrt 2 : ℂ) * (P : ℂ) * I)) := by
    rw [← Complex.Gamma_conj]
    congr 1
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  push_cast at hplus hminus
  norm_num at ⊢
  ring_nf at ⊢
  rw [hplus, hminus]
  ring

theorem fzzHJGammaShiftProduct_eq_base_mul_rational (y : ℝ) :
    let z : ℂ := (1 / 2 : ℂ) + (y : ℂ) * I
    Complex.Gamma (z + 2) * Complex.Gamma (z - 2) =
      gammaVerticalValue (1 / 2) y ^ (2 : ℕ) *
        (z * (z + 1) / ((z - 1) * (z - 2))) := by
  let z : ℂ := (1 / 2 : ℂ) + (y : ℂ) * I
  change Complex.Gamma (z + 2) * Complex.Gamma (z - 2) =
    gammaVerticalValue (1 / 2) y ^ (2 : ℕ) *
      (z * (z + 1) / ((z - 1) * (z - 2)))
  have hz : z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [z, Complex.mul_re] at hre
  have hzp1 : z + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [z, Complex.mul_re] at hre
  have hzm1 : z - 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [z, Complex.mul_re] at hre
  have hzm2 : z - 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [z, Complex.mul_re] at hre
  have hplus : Complex.Gamma (z + 2) =
      (z + 1) * z * Complex.Gamma z := by
    calc
      Complex.Gamma (z + 2) = Complex.Gamma ((z + 1) + 1) := by congr 1 <;> ring
      _ = (z + 1) * Complex.Gamma (z + 1) :=
        Complex.Gamma_add_one (z + 1) hzp1
      _ = (z + 1) * (z * Complex.Gamma z) := by
        rw [Complex.Gamma_add_one z hz]
      _ = _ := by ring
  have hminus : Complex.Gamma (z - 2) =
      Complex.Gamma z / ((z - 1) * (z - 2)) := by
    apply (eq_div_iff (mul_ne_zero hzm1 hzm2)).2
    have hstep1 : Complex.Gamma z = (z - 1) * Complex.Gamma (z - 1) := by
      convert Complex.Gamma_add_one (z - 1) hzm1 using 1 <;> ring
    have hstep2 : Complex.Gamma (z - 1) =
        (z - 2) * Complex.Gamma (z - 2) := by
      convert Complex.Gamma_add_one (z - 2) hzm2 using 1 <;> ring
    rw [hstep1, hstep2]
    ring
  rw [hplus, hminus]
  have hbase : gammaVerticalValue (1 / 2) y = Complex.Gamma z := by
    unfold gammaVerticalValue
    congr 1
    dsimp [z]
    push_cast
    ring
  rw [hbase]
  field_simp [hzm1, hzm2]

theorem fzzHJRationalShiftFactor_eq_cayleyProduct (y : ℝ) :
    let z : ℂ := (1 / 2 : ℂ) + (y : ℂ) * I
    z * (z + 1) / ((z - 1) * (z - 2)) =
      GaloisForLFunctions.HTGeometry.realCayley (2 * y) *
        GaloisForLFunctions.HTGeometry.realCayley (2 * y / 3) := by
  let z : ℂ := (1 / 2 : ℂ) + (y : ℂ) * I
  change z * (z + 1) / ((z - 1) * (z - 2)) = _
  have hzm1 : z - 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [z, Complex.mul_re] at hre
  have hzm2 : z - 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [z, Complex.mul_re] at hre
  have hcayley (x : ℝ) : (x : ℂ) + I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  have hfactor : z * (z + 1) / ((z - 1) * (z - 2)) =
      (z / (z - 1)) * ((z + 1) / (z - 2)) := by
    field_simp [hzm1, hzm2]
  have hfirst : z / (z - 1) =
      GaloisForLFunctions.HTGeometry.realCayley (2 * y) := by
    unfold GaloisForLFunctions.HTGeometry.realCayley
    apply (div_eq_div_iff hzm1 (hcayley (2 * y))).2
    dsimp [z]
    push_cast
    ring_nf
    simp
  have hsecond : (z + 1) / (z - 2) =
      GaloisForLFunctions.HTGeometry.realCayley (2 * y / 3) := by
    unfold GaloisForLFunctions.HTGeometry.realCayley
    apply (div_eq_div_iff hzm2 (hcayley (2 * y / 3))).2
    dsimp [z]
    push_cast
    ring_nf
    simp
  rw [hfactor, hfirst, hsecond]

theorem fzzHJRationalShiftFactor_eq_exp_phase (y : ℝ) :
    let z : ℂ := (1 / 2 : ℂ) + (y : ℂ) * I
    z * (z + 1) / ((z - 1) * (z - 2)) =
      Complex.exp (I * (((2 * (Real.arctan (2 * y) +
        Real.arctan (2 * y / 3))) : ℝ) : ℂ)) := by
  change ((1 / 2 : ℂ) + (y : ℂ) * I) *
      ((1 / 2 : ℂ) + (y : ℂ) * I + 1) /
        ((((1 / 2 : ℂ) + (y : ℂ) * I) - 1) *
          (((1 / 2 : ℂ) + (y : ℂ) * I) - 2)) = _
  rw [fzzHJRationalShiftFactor_eq_cayleyProduct,
    realCayley_eq_neg_exp_two_mul_I_arctan,
    realCayley_eq_neg_exp_two_mul_I_arctan]
  simp only [neg_mul_neg]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem fzzHJGammaShiftProduct_eq_normSq_mul_exp_halfPhase (y : ℝ) :
    let z : ℂ := (1 / 2 : ℂ) + (y : ℂ) * I
    Complex.Gamma (z + 2) * Complex.Gamma (z - 2) =
      ((‖gammaVerticalValue (1 / 2) y‖ ^ (2 : ℕ) : ℝ) : ℂ) *
        Complex.exp (I * (((2 * (gammaVerticalPhase (1 / 2) y +
          Real.arctan (2 * y) + Real.arctan (2 * y / 3))) : ℝ) : ℂ)) := by
  change Complex.Gamma ((1 / 2 : ℂ) + (y : ℂ) * I + 2) *
      Complex.Gamma ((1 / 2 : ℂ) + (y : ℂ) * I - 2) = _
  rw [fzzHJGammaShiftProduct_eq_base_mul_rational]
  nth_rewrite 1 [gammaVerticalValue_eq_norm_mul_exp_phase
    (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [fzzHJRationalShiftFactor_eq_exp_phase]
  rw [mul_pow]
  calc
    ((‖gammaVerticalValue (1 / 2) y‖ : ℂ) ^ (2 : ℕ) *
          Complex.exp (I * (gammaVerticalPhase (1 / 2) y : ℂ)) ^ (2 : ℕ)) *
        Complex.exp (I * (((2 * (Real.arctan (2 * y) +
          Real.arctan (2 * y / 3))) : ℝ) : ℂ)) =
      ((‖gammaVerticalValue (1 / 2) y‖ ^ (2 : ℕ) : ℝ) : ℂ) *
        (Complex.exp (I * (gammaVerticalPhase (1 / 2) y : ℂ)) ^ (2 : ℕ) *
          Complex.exp (I * (((2 * (Real.arctan (2 * y) +
            Real.arctan (2 * y / 3))) : ℝ) : ℂ))) := by
        push_cast
        ring
    _ = _ := by
      simp only [pow_two]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring

theorem fzzHJGammaShiftProduct_div_conj_eq_exp_phase (y : ℝ) :
    let z : ℂ := (1 / 2 : ℂ) + (y : ℂ) * I
    let F : ℂ := Complex.Gamma (z + 2) * Complex.Gamma (z - 2)
    F / (starRingEnd ℂ) F =
      Complex.exp (I * (fzzHJBalancedExternalGammaPhaseLift y : ℂ)) := by
  let z : ℂ := (1 / 2 : ℂ) + (y : ℂ) * I
  let F : ℂ := Complex.Gamma (z + 2) * Complex.Gamma (z - 2)
  change F / (starRingEnd ℂ) F = _
  have hF : F =
      ((‖gammaVerticalValue (1 / 2) y‖ ^ (2 : ℕ) : ℝ) : ℂ) *
        Complex.exp (I * (((2 * (gammaVerticalPhase (1 / 2) y +
          Real.arctan (2 * y) + Real.arctan (2 * y / 3))) : ℝ) : ℂ)) := by
    dsimp [F, z]
    exact fzzHJGammaShiftProduct_eq_normSq_mul_exp_halfPhase y
  rw [hF]
  let r : ℝ := ‖gammaVerticalValue (1 / 2) y‖ ^ (2 : ℕ)
  let beta : ℝ := 2 * (gammaVerticalPhase (1 / 2) y +
    Real.arctan (2 * y) + Real.arctan (2 * y / 3))
  have hr : (r : ℂ) ≠ 0 := by
    exact_mod_cast (sq_pos_of_pos
      (norm_pos_iff.mpr (gammaVerticalValue_ne_zero (by norm_num) y))).ne'
  change (r : ℂ) * Complex.exp (I * (beta : ℂ)) /
      (starRingEnd ℂ) ((r : ℂ) * Complex.exp (I * (beta : ℂ))) = _
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
  field_simp [hr]
  rw [← Complex.exp_add]
  congr 1
  unfold fzzHJBalancedExternalGammaPhaseLift
  dsimp [beta]
  push_cast
  ring

theorem fzzHJBalancedExternalGammaAmplitude_eq_exp_phase (P : ℝ) :
    fzzHJBalancedExternalGammaAmplitude P =
      Complex.exp (I *
        (fzzHJBalancedExternalGammaPhaseLift (Real.sqrt 2 * P) : ℂ)) := by
  rw [fzzHJBalancedExternalGammaAmplitude_eq_shiftProduct_div_conj]
  exact fzzHJGammaShiftProduct_div_conj_eq_exp_phase (Real.sqrt 2 * P)

@[simp] theorem fzzHJBalancedExternalGammaAmplitude_zero :
    fzzHJBalancedExternalGammaAmplitude 0 = 1 := by
  rw [fzzHJBalancedExternalGammaAmplitude_eq_exp_phase]
  simp [fzzHJBalancedExternalGammaPhaseLift, gammaVerticalPhase]

theorem fzzHJBalancedExternalGammaAmplitude_cofinal_recurrence
    (M : ℝ) :
    ∃ P : ℝ, M < P ∧ fzzHJBalancedExternalGammaAmplitude P = 1 := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  obtain ⟨y, hy, n, hn⟩ :=
    fzzHJBalancedExternalGammaPhaseLift_cofinal_period (Real.sqrt 2 * M)
  refine ⟨y / Real.sqrt 2, ?_, ?_⟩
  · apply (lt_div_iff₀ hsqrt).2
    nlinarith
  · rw [fzzHJBalancedExternalGammaAmplitude_eq_exp_phase]
    have hyarg : Real.sqrt 2 * (y / Real.sqrt 2) = y := by
      field_simp [hsqrt.ne']
    rw [hyarg, hn]
    convert Complex.exp_nat_mul_two_pi_mul_I n using 1 <;> push_cast <;> ring

/-- Closed route class: no pointwise predicate of the complete balanced external-leg amplitude
can characterize linear replica-area passivity. -/
def FZZHJBalancedExternalGammaAmplitudeRouteKilled : Prop :=
  (∀ M : ℝ, ∃ P : ℝ, M < P ∧
      fzzHJBalancedExternalGammaAmplitude P =
        fzzHJBalancedExternalGammaAmplitude 0) ∧
    ¬ ∃ S : ℂ → Prop, ∀ P : ℝ,
      S (fzzHJBalancedExternalGammaAmplitude P) ↔
        fzzLinearReplicaAreaNormalizedResponse 1 P ≤ 1

/-- The complete balanced Halder--Jafferis external Gamma amplitude returns exactly to its wall
value at arbitrarily large nonzero radial momenta.  Hence its pointwise value cannot be the
missing passivity producer in the FZZ-P proof chain. -/
theorem fzzHJBalancedExternalGammaAmplitudeRouteKilled :
    FZZHJBalancedExternalGammaAmplitudeRouteKilled := by
  constructor
  · intro M
    obtain ⟨P, hMP, hP⟩ := fzzHJBalancedExternalGammaAmplitude_cofinal_recurrence M
    exact ⟨P, hMP, by simpa using hP⟩
  · rintro ⟨S, hS⟩
    have hpassive0 : fzzLinearReplicaAreaNormalizedResponse 1 0 ≤ 1 :=
      (fzzLinearReplicaAreaNormalizedResponse_le_one_iff
        (n := 1) (by norm_num) 0).2 rfl
    have hSone : S 1 := by
      simpa using (hS 0).2 hpassive0
    obtain ⟨P, hPpos, hPamp⟩ :=
      fzzHJBalancedExternalGammaAmplitude_cofinal_recurrence 0
    have hpassiveP : fzzLinearReplicaAreaNormalizedResponse 1 P ≤ 1 := by
      exact (hS P).1 (by simpa [hPamp] using hSone)
    exact (not_fzzLinearReplicaAreaNormalizedResponse_passive_of_ne_zero
      (ne_of_gt hPpos)) hpassiveP

end

end RHTower
