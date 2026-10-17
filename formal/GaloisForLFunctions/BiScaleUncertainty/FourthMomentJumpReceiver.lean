import GaloisForLFunctions.BiScaleUncertainty.DyadicHyperbolicMomentControl

/-!
# Fourth-moment variational transfer of hyperbolic jumps

Actual second and fourth hyperbolic moments replace the source-support envelope.
Signed variational controls transfer the resulting bound through the full multiplier
Gram and source-data frame envelope into the original secant/plastic functional.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.FourthMomentJump
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open CenteredHyperbolicGram ProjectedHyperbolicGram ArithmeticMultiplierCollisions
open DyadicMultiplierFrame DyadicHyperbolicMoment
noncomputable section
variable {ι : Type*}

/-- Energy of the twice sine-multiplied actual source. -/
def fourthEnergy (f : C_c(ℝ, ℝ)) (α : ℝ) : ℝ :=
  autocorr (sinhCompact α (sinhCompact α f)) 0

theorem fourthEnergy_nonneg (f : C_c(ℝ, ℝ)) (α : ℝ) : 0 ≤ fourthEnergy f α :=
  autocorr_zero_nonneg _

theorem fourthEnergy_eq_integral (f : C_c(ℝ, ℝ)) (α : ℝ) :
    fourthEnergy f α = ∫ u, Real.sinh (α * u) ^ 4 * f u ^ 2 := by
  unfold fourthEnergy
  rw [← integral_sq_eq_autocorr_zero]
  apply integral_congr_ae
  filter_upwards [] with u
  change (Real.sinh (α * u) * (Real.sinh (α * u) * f u)) ^ 2 = _
  ring

private theorem secondEnergy_eq_integral (f : C_c(ℝ, ℝ)) (α : ℝ) :
    autocorr (sinhCompact α f) 0 = ∫ u, Real.sinh (α * u) ^ 2 * f u ^ 2 := by
  rw [← integral_sq_eq_autocorr_zero]
  apply integral_congr_ae
  filter_upwards [] with u
  change (Real.sinh (α * u) * f u) ^ 2 = _
  ring

/-- The quadratic endpoint moment contains no source-support radius. -/
def fourthEnvelope (f : C_c(ℝ, ℝ)) (α x : ℝ) : ℝ :=
  fourthEnergy f α * Real.cosh (α * x) ^ 2 +
    (fourthEnergy f α + autocorr (sinhCompact α f) 0) * Real.sinh (α * x) ^ 2

theorem fourthEnvelope_nonneg (f : C_c(ℝ, ℝ)) (α x : ℝ) : 0 ≤ fourthEnvelope f α x := by
  unfold fourthEnvelope
  exact add_nonneg (mul_nonneg (fourthEnergy_nonneg f α) (sq_nonneg _))
    (mul_nonneg (add_nonneg (fourthEnergy_nonneg f α) (autocorr_zero_nonneg _)) (sq_nonneg _))

theorem continuous_fourthEnvelope (f : C_c(ℝ, ℝ)) (α : ℝ) : Continuous (fourthEnvelope f α) := by
  unfold fourthEnvelope
  fun_prop

private theorem integrable_weighted_square (f : C_c(ℝ, ℝ)) (w : ℝ → ℝ) (hw : Continuous w) :
    Integrable (fun u => w u * f u ^ 2) := by
  have hs : HasCompactSupport (fun u : ℝ => f u ^ 2) := by
    have h : HasCompactSupport (fun u : ℝ => f u * f u) := f.hasCompactSupport.mul_left
    simpa only [sq] using h
  exact (hw.mul (f.continuous.pow 2)).integrable_of_hasCompactSupport hs.mul_left

private theorem doubleCosh_eq (u : ℝ) : Real.cosh (2 * u) = 1 + 2 * Real.sinh u ^ 2 := by
  rw [Real.cosh_two_mul]
  nlinarith only [Real.cosh_sq_sub_sinh_sq u]

private theorem coshMass_eq_second (f : C_c(ℝ, ℝ)) (α : ℝ) :
    coshMass f α = autocorr f 0 + 2 * autocorr (sinhCompact α f) 0 := by
  have hF := integrable_sq (g := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport
  have hS := integrable_weighted_square f (fun u => Real.sinh (α * u) ^ 2) (by fun_prop)
  have he : (fun u => Real.cosh (2 * α * u) * f u ^ 2) =
      fun u => f u ^ 2 + 2 * (Real.sinh (α * u) ^ 2 * f u ^ 2) := by
    funext u
    rw [show 2 * α * u = 2 * (α * u) by ring, doubleCosh_eq]
    ring
  unfold coshMass
  rw [he, integral_add hF (hS.const_mul 2), integral_const_mul,
    integral_sq_eq_autocorr_zero, ← secondEnergy_eq_integral]

private theorem coshSquareMass_eq_fourth (f : C_c(ℝ, ℝ)) (α : ℝ) :
    coshSquareMass f α = autocorr f 0 + 4 * autocorr (sinhCompact α f) 0 +
      4 * fourthEnergy f α := by
  have hF := integrable_sq (g := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport
  have hS := integrable_weighted_square f (fun u => Real.sinh (α * u) ^ 2) (by fun_prop)
  have hT := integrable_weighted_square f (fun u => Real.sinh (α * u) ^ 4) (by fun_prop)
  have hA : Integrable (fun u => f u ^ 2 + 4 * (Real.sinh (α * u) ^ 2 * f u ^ 2)) :=
    hF.add (hS.const_mul 4)
  have he : (fun u => coshCompact (2 * α) f u ^ 2) = fun u =>
      f u ^ 2 + 4 * (Real.sinh (α * u) ^ 2 * f u ^ 2) +
        4 * (Real.sinh (α * u) ^ 4 * f u ^ 2) := by
    funext u
    change (Real.cosh (2 * α * u) * f u) ^ 2 = _
    rw [show 2 * α * u = 2 * (α * u) by ring, doubleCosh_eq]
    ring
  unfold coshSquareMass
  rw [← integral_sq_eq_autocorr_zero, he, integral_add hA (hT.const_mul 4),
    integral_add hF (hS.const_mul 4), integral_const_mul, integral_const_mul,
    integral_sq_eq_autocorr_zero, ← secondEnergy_eq_integral, ← fourthEnergy_eq_integral]

/-- Fourth-moment cost is exactly determined by the existing source energies and variance. -/
theorem fourthEnergy_variance_identity (f : C_c(ℝ, ℝ)) (α : ℝ) :
    4 * autocorr f 0 * fourthEnergy f α =
      sourceVariance f α + 4 * autocorr (sinhCompact α f) 0 ^ 2 := by
  unfold sourceVariance
  rw [coshMass_eq_second, coshSquareMass_eq_fourth]
  ring

private theorem integrable_weighted_shift_square (f : C_c(ℝ, ℝ)) (w : ℝ → ℝ)
    (hw : Continuous w) (x : ℝ) : Integrable (fun u => w u * f (u + x) ^ 2) := by
  have hs : HasCompactSupport (fun u : ℝ => f (u + x) ^ 2) := by
    have h : HasCompactSupport (fun u : ℝ => f (u + x) * f (u + x)) :=
      (hasCompactSupport_comp_add f.hasCompactSupport x).mul_left
    simpa only [sq] using h
  exact (hw.mul ((f.continuous.comp (continuous_add_const x)).pow 2)).integrable_of_hasCompactSupport
    hs.mul_left

private theorem integrable_weighted_jump (f : C_c(ℝ, ℝ)) (w : ℝ → ℝ)
    (hw : Continuous w) (x : ℝ) : Integrable (fun u => w u * (f u - f (u + x)) ^ 2) := by
  have hc : Continuous (fun u => (f u - f (u + x)) ^ 2) :=
    (f.continuous.sub (f.continuous.comp (continuous_add_const x))).pow 2
  have hs : HasCompactSupport (fun u => (f u - f (u + x)) ^ 2) := by
    have hj : HasCompactSupport (fun u : ℝ => f u - f (u + x)) :=
      f.hasCompactSupport.sub (hasCompactSupport_comp_add f.hasCompactSupport x)
    have h : HasCompactSupport (fun u : ℝ => (f u - f (u + x)) * (f u - f (u + x))) :=
      hj.mul_left
    simpa only [sq] using h
  exact (hw.mul hc).integrable_of_hasCompactSupport hs.mul_left

private theorem endpoint_weight_identity (α x u : ℝ) :
    (Real.sinh (α * u) * Real.sinh (α * (u + x))) ^ 2 +
      (Real.sinh (α * (u - x)) * Real.sinh (α * u)) ^ 2 =
        2 * (Real.sinh (α * u) ^ 4 * Real.cosh (α * x) ^ 2 +
          (Real.sinh (α * u) ^ 4 + Real.sinh (α * u) ^ 2) * Real.sinh (α * x) ^ 2) := by
  rw [mul_add, mul_sub, Real.sinh_add, Real.sinh_sub]
  linear_combination 2 * Real.sinh (α * u) ^ 2 * Real.sinh (α * x) ^ 2 *
    (Real.cosh_sq_sub_sinh_sq (α * u))

/-- The squared hyperbolic jump weight is controlled by actual fourth moments. -/
theorem weighted_jump_square_le_fourth (f : C_c(ℝ, ℝ)) (α x : ℝ) :
    (∫ u, (Real.sinh (α * u) * Real.sinh (α * (u + x))) ^ 2 *
      (f u - f (u + x)) ^ 2) ≤ 4 * fourthEnvelope f α x := by
  let w := fun u : ℝ => (Real.sinh (α * u) * Real.sinh (α * (u + x))) ^ 2
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hi := integrable_weighted_jump f w hw x
  have hL := integrable_weighted_square f w hw
  have hR := integrable_weighted_shift_square f w hw x
  have hUpper : Integrable (fun u => 2 * (w u * f u ^ 2 + w u * f (u + x) ^ 2)) :=
    (hL.add hR).const_mul 2
  have hmono : (∫ u, w u * (f u - f (u + x)) ^ 2) ≤
      ∫ u, 2 * (w u * f u ^ 2 + w u * f (u + x) ^ 2) := integral_mono hi hUpper (fun u => by
    change w u * (f u - f (u + x)) ^ 2 ≤ 2 * (w u * f u ^ 2 + w u * f (u + x) ^ 2)
    have hsq : (f u - f (u + x)) ^ 2 ≤ 2 * (f u ^ 2 + f (u + x) ^ 2) := by
      nlinarith only [sq_nonneg (f u + f (u + x))]
    have h := mul_le_mul_of_nonneg_left hsq (sq_nonneg (Real.sinh (α * u) * Real.sinh (α * (u + x))))
    change w u * (f u - f (u + x)) ^ 2 ≤ w u * (2 * (f u ^ 2 + f (u + x) ^ 2)) at h
    nlinarith only [h])
  have hshift : (∫ u, w u * f (u + x) ^ 2) = ∫ u, w (u - x) * f u ^ 2 := by
    have h := integral_add_right_eq_self (μ := volume) (fun u => w (u - x) * f u ^ 2) x
    simpa only [add_sub_cancel_right] using h
  have hR' := integrable_weighted_square f (fun u => w (u - x)) (by fun_prop)
  have he : (fun u => w u * f u ^ 2 + w (u - x) * f u ^ 2) = fun u =>
      2 * (Real.cosh (α * x) ^ 2 * (Real.sinh (α * u) ^ 4 * f u ^ 2) +
        Real.sinh (α * x) ^ 2 *
          (Real.sinh (α * u) ^ 4 * f u ^ 2 + Real.sinh (α * u) ^ 2 * f u ^ 2)) := by
    funext u
    have h := congrArg (fun z : ℝ => z * f u ^ 2) (endpoint_weight_identity α x u)
    dsimp [w]
    rw [sub_add_cancel]
    nlinarith only [h]
  have hT := integrable_weighted_square f (fun u => Real.sinh (α * u) ^ 4) (by fun_prop)
  have hS := integrable_weighted_square f (fun u => Real.sinh (α * u) ^ 2) (by fun_prop)
  have hTS : Integrable (fun u => Real.sinh (α * u) ^ 4 * f u ^ 2 +
      Real.sinh (α * u) ^ 2 * f u ^ 2) := hT.add hS
  rw [integral_const_mul, integral_add hL hR, hshift, ← integral_add hL hR', he,
    integral_const_mul, integral_add (hT.const_mul _) (hTS.const_mul _),
    integral_const_mul, integral_const_mul, integral_add hT hS,
    ← fourthEnergy_eq_integral, ← secondEnergy_eq_integral] at hmono
  change _ ≤ 4 * fourthEnvelope f α x
  unfold fourthEnvelope
  nlinarith only [hmono]

/-- Signed variational transfer, with no support radius or positivity assumption on the control. -/
theorem source_increment_ge_variational (f : C_c(ℝ, ℝ)) (α x a : ℝ) :
    2 * a * (Real.cosh (α * x) * autocorr (sinhCompact α f) 0 -
      autocorr (sinhCompact α f) x) - 2 * a ^ 2 * fourthEnvelope f α x ≤
        autocorr f 0 - autocorr f x := by
  let w := fun u : ℝ => Real.sinh (α * u) * Real.sinh (α * (u + x))
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hJ : Integrable (fun u => (f u - f (u + x)) ^ 2) := by
    simpa only [one_mul] using integrable_weighted_jump f (fun _ => 1) continuous_const x
  have hW := integrable_weighted_jump f w hw x
  have hW2 := integrable_weighted_jump f (fun u => w u ^ 2) (hw.pow 2) x
  have hA : Integrable (fun u => (f u - f (u + x)) ^ 2 -
      (2 * a) * (w u * (f u - f (u + x)) ^ 2)) := hJ.sub (hW.const_mul (2 * a))
  have hB : Integrable (fun u => a ^ 2 * (w u ^ 2 * (f u - f (u + x)) ^ 2)) :=
    hW2.const_mul (a ^ 2)
  have hn : 0 ≤ ∫ u, (f u - f (u + x)) ^ 2 -
      (2 * a) * (w u * (f u - f (u + x)) ^ 2) +
        a ^ 2 * (w u ^ 2 * (f u - f (u + x)) ^ 2) :=
    integral_nonneg fun u => by
      change 0 ≤ (f u - f (u + x)) ^ 2 - (2 * a) * (w u * (f u - f (u + x)) ^ 2) +
        a ^ 2 * (w u ^ 2 * (f u - f (u + x)) ^ 2)
      nlinarith only [sq_nonneg ((f u - f (u + x)) - a * w u * (f u - f (u + x)))]
  rw [integral_add hA hB,
    integral_sub hJ (hW.const_mul (2 * a)), integral_const_mul, integral_const_mul,
    integral_sub_shift_sq (f := (f : ℝ → ℝ)) f.hasCompactSupport f.continuous x] at hn
  have hid := sinh_weighted_jump_identity f α x
  change (∫ u, w u * (f u - f (u + x)) ^ 2) = _ at hid
  rw [hid] at hn
  have hcost := mul_le_mul_of_nonneg_left (weighted_jump_square_le_fourth f α x) (sq_nonneg a)
  change a ^ 2 * (∫ u, w u ^ 2 * (f u - f (u + x)) ^ 2) ≤ _ at hcost
  nlinarith only [hn, hcost]

/-- Signed collar weights supplied by arbitrary real variational controls. -/
def variationalWeights (b t a : ι → ℝ) (y : ℝ) (i : ι) : ℝ :=
  2 * b i ^ 2 * archSechHalfWeight (t i - y) * a i

def fourthCost (f : C_c(ℝ, ℝ)) (s : Finset ι) (b t a : ι → ℝ) (y : ℝ) : ℝ :=
  ∑ i ∈ s, 2 * b i ^ 2 * archSechHalfWeight (t i - y) *
    fourthEnvelope f (1 / 2) (t i - y) * a i ^ 2

/-- Full multiplier Gram lower bound with a fourth-moment control cost. -/
def fourthGramBound (f : C_c(ℝ, ℝ)) (s : Finset ι) (b t a : ι → ℝ) (y : ℝ) : ℝ :=
  autocorr (sinhCompact (1 / 2) f) 0 *
      (∑ i ∈ s, variationalWeights b t a y i * Real.cosh ((t i - y) / 2)) -
    Real.sqrt (autocorr (sinhCompact (1 / 2) f) 0 *
      translationGramEnergy (sinhCompact (1 / 2) f) s (variationalWeights b t a y) t) -
    fourthCost f s b t a y

/-- Unconditional multi-node transfer without a source-support envelope. -/
theorem secantJumpCollar_ge_fourthGram (f : C_c(ℝ, ℝ))
    (s : Finset ι) (b t a : ι → ℝ) (y : ℝ) :
    fourthGramBound f s b t a y ≤ secantJumpCollar f s b t y := by
  have hpair := translationPacket_correlation_le (sinhCompact (1 / 2) f) s
    (variationalWeights b t a y) t y
  have hnode (i : ι) : variationalWeights b t a y i *
      (Real.cosh ((t i - y) / 2) * autocorr (sinhCompact (1 / 2) f) 0 -
        autocorr (sinhCompact (1 / 2) f) (t i - y)) -
      2 * b i ^ 2 * archSechHalfWeight (t i - y) *
        fourthEnvelope f (1 / 2) (t i - y) * a i ^ 2 ≤
      b i ^ 2 * ((autocorr f 0 - autocorr f (t i - y)) * archSechHalfWeight (t i - y)) := by
    have h := mul_le_mul_of_nonneg_left
      (source_increment_ge_variational f (1 / 2) (t i - y) (a i))
      (mul_nonneg (sq_nonneg (b i)) (archSechHalfWeight_pos (t i - y)).le)
    rw [show (1 / 2 : ℝ) * (t i - y) = (t i - y) / 2 by ring] at h
    unfold variationalWeights
    nlinarith only [h]
  unfold fourthGramBound fourthCost secantJumpCollar
  calc
    _ ≤ autocorr (sinhCompact (1 / 2) f) 0 *
        (∑ i ∈ s, variationalWeights b t a y i * Real.cosh ((t i - y) / 2)) -
      (∑ i ∈ s, variationalWeights b t a y i * autocorr (sinhCompact (1 / 2) f) (t i - y)) -
      ∑ i ∈ s, 2 * b i ^ 2 * archSechHalfWeight (t i - y) *
        fourthEnvelope f (1 / 2) (t i - y) * a i ^ 2 := by linarith only [hpair]
    _ = ∑ i ∈ s, (variationalWeights b t a y i *
        (Real.cosh ((t i - y) / 2) * autocorr (sinhCompact (1 / 2) f) 0 -
          autocorr (sinhCompact (1 / 2) f) (t i - y)) -
        2 * b i ^ 2 * archSechHalfWeight (t i - y) *
          fourthEnvelope f (1 / 2) (t i - y) * a i ^ 2) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => hnode i

private theorem continuous_sech_translate (t : ℝ) :
    Continuous (fun y => archSechHalfWeight (t - y)) := by
  unfold archSechHalfWeight
  exact continuous_const.div (Real.continuous_cosh.comp (by fun_prop))
    (fun y => (Real.cosh_pos ((t - y) / 2)).ne')

theorem continuous_variationalWeights (b t a : ι → ℝ) (i : ι) :
    Continuous (fun y => variationalWeights b t a y i) :=
  (continuous_const.mul (continuous_sech_translate (t i))).mul continuous_const

theorem continuous_fourthCost (f : C_c(ℝ, ℝ)) (s : Finset ι) (b t a : ι → ℝ) :
    Continuous (fourthCost f s b t a) := by
  unfold fourthCost
  exact continuous_finsetSum _ fun i _ =>
    (((continuous_const.mul (continuous_sech_translate (t i))).mul
      ((continuous_fourthEnvelope f (1 / 2)).comp (by fun_prop))).mul continuous_const)

/-- Radius-free dyadic receiver with all off-diagonal source errors retained. -/
def fourthFrameBound (f : C_c(ℝ, ℝ)) (N : ℕ) (a : ℕ → ℝ) (y : ℝ) : ℝ :=
  autocorr (sinhCompact (1 / 2) f) 0 *
      (∑ i ∈ Finset.range (N + 1), variationalWeights (fun _ => 1) (chainNode (Real.log 2)) a y i *
        Real.cosh ((chainNode (Real.log 2) i - y) / 2)) -
    Real.sqrt (autocorr (sinhCompact (1 / 2) f) 0 *
      max (frameGramUpper f N (variationalWeights (fun _ => 1) (chainNode (Real.log 2)) a y)) 0) -
    fourthCost f (Finset.range (N + 1)) (fun _ => 1) (chainNode (Real.log 2)) a y

theorem odd_fourthFrameBound_le_gram (f : C_c(ℝ, ℝ)) (N : ℕ) (a : ℕ → ℝ) (y : ℝ) :
    fourthFrameBound (oddCompactSource f) N a y ≤
      fourthGramBound (oddCompactSource f) (Finset.range (N + 1))
        (fun _ => 1) (chainNode (Real.log 2)) a y := by
  have h := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
    ((odd_sinhGram_le_frameGramUpper f N
      (variationalWeights (fun _ => 1) (chainNode (Real.log 2)) a y)).trans (le_max_left _ 0))
    (autocorr_zero_nonneg (sinhCompact (1 / 2) (oddCompactSource f))))
  unfold fourthFrameBound fourthGramBound
  linarith only [h]

theorem odd_secantJumpCollar_ge_fourthFrame (f : C_c(ℝ, ℝ)) (N : ℕ) (a : ℕ → ℝ) (y : ℝ) :
    fourthFrameBound (oddCompactSource f) N a y ≤
      secantJumpCollar (oddCompactSource f) (Finset.range (N + 1))
        (fun _ => 1) (chainNode (Real.log 2)) y :=
  (odd_fourthFrameBound_le_gram f N a y).trans (secantJumpCollar_ge_fourthGram _ _ _ _ _ _)

theorem continuous_frameGramUpper_of_weights (f : C_c(ℝ, ℝ)) (N : ℕ) (v : ℝ → ℕ → ℝ)
    (hv : ∀ i, Continuous (fun y => v y i)) : Continuous (fun y => frameGramUpper f N (v y)) := by
  have ha (r : ℕ) : Continuous (fun y => lagAmplitude N (1 / 2) (Real.log 2) (v y) r) := by
    unfold lagAmplitude differenceWeight
    exact continuous_finsetSum _ fun p _ => ((hv p.1).mul (hv p.2)).div_const _
  have he : Continuous (fun y => lagCorrection f N (1 / 2) (sourceMean f (1 / 2))
      (Real.log 2) (v y)) := by
    unfold lagCorrection
    exact continuous_finsetSum _ fun r _ => ((ha r).mul continuous_const).mul continuous_const
  have hz : Continuous (fun y => crossLagError f N (1 / 2) (Real.log 2) (v y)) := by
    unfold crossLagError
    exact continuous_finsetSum _ fun p _ => ((ha p.1).mul (ha p.2)).mul continuous_const
  have hw : Continuous (fun y => weightEnergy N (v y)) :=
    continuous_finsetSum _ fun i _ => (hv i).pow 2
  unfold frameGramUpper frameSourceError
  exact (continuous_const.mul hw).add (he.add
    (Real.continuous_sqrt.comp (continuous_const.mul (hz.max continuous_const))))

theorem continuous_fourthFrameBound (f : C_c(ℝ, ℝ)) (N : ℕ) (a : ℕ → ℝ) :
    Continuous (fourthFrameBound f N a) := by
  have hv := continuous_variationalWeights (fun _ => (1 : ℝ)) (chainNode (Real.log 2)) a
  have hu := continuous_frameGramUpper_of_weights f N _ hv
  unfold fourthFrameBound
  exact ((continuous_const.mul (continuous_finsetSum _ fun i _ =>
    (hv i).mul (by fun_prop))).sub
      (Real.continuous_sqrt.comp (continuous_const.mul (hu.max continuous_const)))).sub
        (continuous_fourthCost _ _ _ _ _)

private theorem integral_secantCollar_le_energy (f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, secantJumpCollar f (Finset.range (N + 1))
      (fun _ => 1) (chainNode (Real.log 2)) (-y)) ≤ biScaleSecantEnergy f := by
  have hd : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have htile := intervalIntegral_periodic_collar_sum_eq (continuous_secantJumpIntegrand f)
    0 (Real.log 2) (N + 1)
  simp only [zero_add] at htile
  have hcollar : (fun y => secantJumpCollar f (Finset.range (N + 1))
      (fun _ => 1) (chainNode (Real.log 2)) (-y)) = fun y =>
      ∑ k ∈ Finset.range (N + 1), (autocorr f 0 - autocorr f ((k : ℝ) * Real.log 2 + y)) *
        archSechHalfWeight ((k : ℝ) * Real.log 2 + y) := by
    funext y
    simp [secantJumpCollar, chainNode, sub_neg_eq_add]
  rw [hcollar, ← htile]
  unfold biScaleSecantEnergy
  rw [intervalIntegral.integral_of_le (mul_nonneg (Nat.cast_nonneg (N + 1)) hd)]
  refine setIntegral_mono_set (integrableOn_secantJumpIntegrand_compact f) ?_ ?_
  · filter_upwards [] with x
    exact mul_nonneg (autocorr_sub_nonneg f.hasCompactSupport f.continuous x)
      (archSechHalfWeight_pos x).le
  · exact Filter.Eventually.of_forall fun x hx => hx.1

/-- Full original secant energy receives the support-radius-free fourth-moment bound. -/
theorem odd_secantEnergy_ge_fourthFrame (f : C_c(ℝ, ℝ)) (N : ℕ) (a : ℕ → ℝ) :
    (∫ y in (0 : ℝ)..Real.log 2, fourthFrameBound (oddCompactSource f) N a (-y)) ≤
      biScaleSecantEnergy (oddCompactSource f) := by
  refine le_trans ?_ (integral_secantCollar_le_energy (oddCompactSource f) N)
  exact intervalIntegral.integral_mono_on (μ := volume)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    (((continuous_fourthFrameBound _ _ _).comp continuous_neg).intervalIntegrable _ _)
    (((continuous_secantJumpCollar _ _ _ _).comp continuous_neg).intervalIntegrable _ _)
    (fun y _ => odd_secantJumpCollar_ge_fourthFrame f N a (-y))

/-- Unconditional actual plastic receiver with fourth-moment control cost. -/
theorem odd_plasticCrossover_ge_fourthFrame (f : C_c(ℝ, ℝ)) (N : ℕ) (a : ℕ → ℝ) :
    (∫ y in (0 : ℝ)..Real.log 2, fourthFrameBound (oddCompactSource f) N a (-y)) +
      plasticRemainderEnergy (oddCompactSource f) -
        2 * (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 ≤
      plasticCrossover (oddCompactSource f) := by
  have h := odd_secantEnergy_ge_fourthFrame f N a
  rw [plasticCrossover_eq_secant_add_remainder_add_moment, hyperbolicMomentEnergy_oddSource]
  linarith

theorem odd_plasticCrossover_ge_fourthFrame_momentBudget (f : C_c(ℝ, ℝ))
    (N M : ℕ) (a : ℕ → ℝ) :
    (∫ y in (0 : ℝ)..Real.log 2, fourthFrameBound (oddCompactSource f) N a (-y)) +
      plasticRemainderEnergy (oddCompactSource f) - 2 * momentBudget (oddCompactSource f) M ≤
        plasticCrossover (oddCompactSource f) := by
  have hp := odd_plasticCrossover_ge_fourthFrame f N a
  have hm := odd_moment_sq_le_budget f M
  linarith

/-- On the full source logarithmic grid, neither collar nor moment cost uses a support radius. -/
theorem odd_logGrid_plasticCrossover_ge_fourthFrame (f : C_c(ℝ, ℝ)) (N : ℕ) (a : ℕ → ℝ)
    (hz : ∀ n : ℕ, 2 ≤ n → autocorr (oddCompactSource f) (Real.log (n : ℝ)) = 0) :
    (∫ y in (0 : ℝ)..Real.log 2, fourthFrameBound (oddCompactSource f) N a (-y)) +
      plasticRemainderEnergy (oddCompactSource f) -
        2 * Real.log 2 * (autocorr (sinhCompact (1 / 2) (oddCompactSource f)) 0 +
          frameRadius (oddCompactSource f)) ≤ plasticCrossover (oddCompactSource f) := by
  have hp := odd_plasticCrossover_ge_fourthFrame f N a
  have hm := odd_logGrid_moment_sq_le_frame f hz
  nlinarith only [hp, hm]

end
end GaloisForLFunctions.BiScaleUncertainty.FourthMomentJump
