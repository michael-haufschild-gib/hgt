import GaloisForLFunctions.RHTower.FZZCigarParityTorusHolonomyFourierResonanceNoGo
import GaloisForLFunctions.RHTower.FZZCigarParityDelaySourceContinuation

/-!
# FZZ linear replica-area holonomy selector

Halder--Jafferis' fractional-winding area operator differentiates a neutral pair at replica
parameter zero.  Its compact-holonomy derivative is the sawtooth character

`2π i n s (χ_{-n}(s) - χ_n(s))`.

The radial derivative is retained as two arbitrary coefficients of `χ_n` and `χ_{-n}`.  This file
proves that neither coefficient affects the three frequencies seen by the squared odd FZZ
holonomy: the Fourier data are exactly `c₀ = -2` and `c_{±2n} = 2/3` for every `n ≠ 0`.

The corpus weighted-resonance theorem then gives the exact normalized rectangular-torus response

`R_n(s₁) = 3/4 + (exp(-4πns₁) + exp(4πns₁))/8`.

It satisfies `R_n ≥ 1`, with passivity `R_n ≤ 1` exactly when `s₁ = 0`.  At the canonical
parity-Mellin twist, universal passivity on source divisor modes is therefore equivalent to FZZ
Mellin completeness and to RH.  The remaining producer is precisely that source-dynamical
divisor-mode passivity law; this module does not assume or prove it.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry.FZZCigar

private theorem intervalIntegral_id_mul_fzzTorusHolonomyCharacter
    {k : ℤ} (hk : k ≠ 0) :
    (∫ s in (0 : ℝ)..1, (s : ℂ) * fzzTorusHolonomyCharacter k s) =
      (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I)⁻¹ := by
  let c : ℂ := ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hc : c ≠ 0 := by
    apply mul_ne_zero
    · exact Complex.ofReal_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hkR)
    · exact Complex.I_ne_zero
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ =>
        ((s : ℂ) / c) * Complex.exp (c * (s : ℂ)) -
          Complex.exp (c * (s : ℂ)) / c ^ 2)
      ((t : ℂ) * Complex.exp (c * (t : ℂ))) t := by
    intro t
    have hlin : HasDerivAt (fun s : ℝ => c * (s : ℂ)) c t := by
      simpa only [mul_one] using (Complex.hasDerivAt_ofReal t).const_mul c
    have hexp : HasDerivAt (fun s : ℝ => Complex.exp (c * (s : ℂ)))
        (c * Complex.exp (c * (t : ℂ))) t := by
      simpa [mul_comm] using hlin.cexp
    have hraw := ((Complex.hasDerivAt_ofReal t).div_const c).mul hexp |>.sub
      (hexp.div_const (c ^ 2))
    convert hraw using 1 <;> try rfl
    field_simp [hc]
    ring
  have hint : IntervalIntegrable
      (fun s : ℝ => (s : ℂ) * fzzTorusHolonomyCharacter k s) volume 0 1 := by
    refine Continuous.intervalIntegrable ?_ 0 1
    exact Complex.continuous_ofReal.mul (continuous_fzzTorusHolonomyCharacter k)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t _ => hderiv t) hint
  have hperiod : Complex.exp (c * (1 : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    refine ⟨k, ?_⟩
    dsimp [c]
    push_cast
    ring
  change (∫ s in (0 : ℝ)..1, (s : ℂ) * Complex.exp (c * (s : ℂ))) = c⁻¹
  rw [hFTC]
  have hperiod_one : Complex.exp (c * ((1 : ℝ) : ℂ)) = 1 := by
    simpa using hperiod
  rw [hperiod_one]
  simp

/-- Compact-holonomy derivative of the fractional-winding pair at replica parameter zero. -/
def fzzLinearReplicaAreaBranchTangent (n : ℤ) (s : ℝ) : ℂ :=
  (((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I) * (s : ℂ) *
    (fzzTorusHolonomyCharacter (-n) s - fzzTorusHolonomyCharacter n s)

/-- Full tangent; constants retain arbitrary radial derivatives of the two winding branches. -/
def fzzLinearReplicaAreaHolonomyTangent
    (n : ℤ) (radialPlus radialMinus : ℂ) (s : ℝ) : ℂ :=
  fzzLinearReplicaAreaBranchTangent n s +
    radialPlus * fzzTorusHolonomyCharacter n s +
    radialMinus * fzzTorusHolonomyCharacter (-n) s

theorem continuous_fzzLinearReplicaAreaHolonomyTangent
    (n : ℤ) (radialPlus radialMinus : ℂ) :
    Continuous (fzzLinearReplicaAreaHolonomyTangent n radialPlus radialMinus) := by
  unfold fzzLinearReplicaAreaHolonomyTangent fzzLinearReplicaAreaBranchTangent
  exact (((continuous_const.mul Complex.continuous_ofReal).mul
      ((continuous_fzzTorusHolonomyCharacter (-n)).sub
        (continuous_fzzTorusHolonomyCharacter n))).add
      (continuous_const.mul (continuous_fzzTorusHolonomyCharacter n))).add
    (continuous_const.mul (continuous_fzzTorusHolonomyCharacter (-n)))

private theorem fzzAreaFourierCoefficient_add
    (m : ℤ) (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    fzzTorusHolonomyFourierCoefficient m (fun s => f s + g s) =
      fzzTorusHolonomyFourierCoefficient m f +
        fzzTorusHolonomyFourierCoefficient m g := by
  unfold fzzTorusHolonomyFourierCoefficient
  rw [show (fun s => fzzTorusHolonomyCharacter (-m) s * (f s + g s)) =
      (fun s => fzzTorusHolonomyCharacter (-m) s * f s +
        fzzTorusHolonomyCharacter (-m) s * g s) by funext s; ring]
  exact intervalIntegral.integral_add
    (((continuous_fzzTorusHolonomyCharacter (-m)).mul hf).intervalIntegrable 0 1)
    (((continuous_fzzTorusHolonomyCharacter (-m)).mul hg).intervalIntegrable 0 1)

private theorem fzzAreaFourierCoefficient_sub
    (m : ℤ) (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    fzzTorusHolonomyFourierCoefficient m (fun s => f s - g s) =
      fzzTorusHolonomyFourierCoefficient m f -
        fzzTorusHolonomyFourierCoefficient m g := by
  unfold fzzTorusHolonomyFourierCoefficient
  rw [show (fun s => fzzTorusHolonomyCharacter (-m) s * (f s - g s)) =
      (fun s => fzzTorusHolonomyCharacter (-m) s * f s -
        fzzTorusHolonomyCharacter (-m) s * g s) by funext s; ring]
  exact intervalIntegral.integral_sub
    (((continuous_fzzTorusHolonomyCharacter (-m)).mul hf).intervalIntegrable 0 1)
    (((continuous_fzzTorusHolonomyCharacter (-m)).mul hg).intervalIntegrable 0 1)

private theorem fzzAreaFourierCoefficient_const_mul
    (m : ℤ) (c : ℂ) (f : ℝ → ℂ) :
    fzzTorusHolonomyFourierCoefficient m (fun s => c * f s) =
      c * fzzTorusHolonomyFourierCoefficient m f := by
  unfold fzzTorusHolonomyFourierCoefficient
  rw [show (fun s => fzzTorusHolonomyCharacter (-m) s * (c * f s)) =
      (fun s => c * (fzzTorusHolonomyCharacter (-m) s * f s)) by
      funext s; ring]
  rw [intervalIntegral.integral_const_mul]

private theorem fzzAreaFourierCoefficient_id_mul_character
    (m k : ℤ) (hfreq : k - m ≠ 0) :
    fzzTorusHolonomyFourierCoefficient m
        (fun s => (s : ℂ) * fzzTorusHolonomyCharacter k s) =
      (((2 * Real.pi * ((k - m : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I)⁻¹ := by
  unfold fzzTorusHolonomyFourierCoefficient
  calc
    (∫ s in (0 : ℝ)..1, fzzTorusHolonomyCharacter (-m) s *
        ((s : ℂ) * fzzTorusHolonomyCharacter k s)) =
        ∫ s in (0 : ℝ)..1,
          (s : ℂ) * fzzTorusHolonomyCharacter (k - m) s := by
            apply intervalIntegral.integral_congr
            intro s _
            calc
              fzzTorusHolonomyCharacter (-m) s *
                    ((s : ℂ) * fzzTorusHolonomyCharacter k s) =
                  (s : ℂ) * (fzzTorusHolonomyCharacter (-m) s *
                    fzzTorusHolonomyCharacter k s) := by ring
              _ = (s : ℂ) * fzzTorusHolonomyCharacter (-m + k) s := by
                    rw [fzzTorusHolonomyCharacter_mul]
              _ = (s : ℂ) * fzzTorusHolonomyCharacter (k - m) s := by
                    rw [show -m + k = k - m by omega]
    _ = (((2 * Real.pi * ((k - m : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I)⁻¹ :=
      intervalIntegral_id_mul_fzzTorusHolonomyCharacter hfreq

private theorem fzzAreaFourierCoefficient_const_mul_character_eq_zero
    (m k : ℤ) (c : ℂ) (hkm : k ≠ m) :
    fzzTorusHolonomyFourierCoefficient m
        (fun s => c * fzzTorusHolonomyCharacter k s) = 0 := by
  unfold fzzTorusHolonomyFourierCoefficient
  calc
    (∫ s in (0 : ℝ)..1, fzzTorusHolonomyCharacter (-m) s *
        (c * fzzTorusHolonomyCharacter k s)) =
        ∫ s in (0 : ℝ)..1, c *
          fzzTorusHolonomyCharacter (k - m) s := by
            apply intervalIntegral.integral_congr
            intro s _
            calc
              fzzTorusHolonomyCharacter (-m) s *
                    (c * fzzTorusHolonomyCharacter k s) =
                  c * (fzzTorusHolonomyCharacter (-m) s *
                    fzzTorusHolonomyCharacter k s) := by ring
              _ = c * fzzTorusHolonomyCharacter (-m + k) s := by
                    rw [fzzTorusHolonomyCharacter_mul]
              _ = c * fzzTorusHolonomyCharacter (k - m) s := by
                    rw [show -m + k = k - m by omega]
    _ = c * ∫ s in (0 : ℝ)..1,
          fzzTorusHolonomyCharacter (k - m) s := by
            rw [intervalIntegral.integral_const_mul]
    _ = 0 := by
      rw [intervalIntegral_fzzTorusHolonomyCharacter]
      have hfreq : k - m ≠ 0 := by omega
      simp [hfreq]

private theorem fzzLinearReplicaAreaHolonomyTangent_fourierCoefficient_decomposition
    (n m : ℤ) (radialPlus radialMinus : ℂ) :
    fzzTorusHolonomyFourierCoefficient m
        (fzzLinearReplicaAreaHolonomyTangent n radialPlus radialMinus) =
      (((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I) *
          (fzzTorusHolonomyFourierCoefficient m
              (fun s => (s : ℂ) * fzzTorusHolonomyCharacter (-n) s) -
            fzzTorusHolonomyFourierCoefficient m
              (fun s => (s : ℂ) * fzzTorusHolonomyCharacter n s)) +
        radialPlus * fzzTorusHolonomyFourierCoefficient m
          (fzzTorusHolonomyCharacter n) +
        radialMinus * fzzTorusHolonomyFourierCoefficient m
          (fzzTorusHolonomyCharacter (-n)) := by
  let c : ℂ := ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I
  let fn : ℝ → ℂ := fun s => (s : ℂ) * fzzTorusHolonomyCharacter (-n) s
  let fp : ℝ → ℂ := fun s => (s : ℂ) * fzzTorusHolonomyCharacter n s
  have hfn : Continuous fn :=
    Complex.continuous_ofReal.mul (continuous_fzzTorusHolonomyCharacter (-n))
  have hfp : Continuous fp :=
    Complex.continuous_ofReal.mul (continuous_fzzTorusHolonomyCharacter n)
  have hbranch : Continuous (fun s => c * (fn s - fp s)) :=
    continuous_const.mul (hfn.sub hfp)
  have hrp : Continuous
      (fun s => radialPlus * fzzTorusHolonomyCharacter n s) :=
    continuous_const.mul (continuous_fzzTorusHolonomyCharacter n)
  have hrm : Continuous
      (fun s => radialMinus * fzzTorusHolonomyCharacter (-n) s) :=
    continuous_const.mul (continuous_fzzTorusHolonomyCharacter (-n))
  rw [show fzzLinearReplicaAreaHolonomyTangent n radialPlus radialMinus =
      (fun s => c * (fn s - fp s) +
        radialPlus * fzzTorusHolonomyCharacter n s +
        radialMinus * fzzTorusHolonomyCharacter (-n) s) by
      funext s
      simp only [fzzLinearReplicaAreaHolonomyTangent,
        fzzLinearReplicaAreaBranchTangent]
      dsimp [c, fn, fp]
      ring]
  rw [fzzAreaFourierCoefficient_add m
      (fun s => c * (fn s - fp s) +
        radialPlus * fzzTorusHolonomyCharacter n s)
      (fun s => radialMinus * fzzTorusHolonomyCharacter (-n) s)
      (hbranch.add hrp) hrm]
  rw [fzzAreaFourierCoefficient_add m
      (fun s => c * (fn s - fp s))
      (fun s => radialPlus * fzzTorusHolonomyCharacter n s)
      hbranch hrp]
  rw [fzzAreaFourierCoefficient_const_mul,
    fzzAreaFourierCoefficient_sub m fn fp hfn hfp,
    fzzAreaFourierCoefficient_const_mul,
    fzzAreaFourierCoefficient_const_mul]

/-- Replica-area tangent has fixed zero-mode `-2`, independent of radial dressing. -/
theorem fzzLinearReplicaAreaHolonomyTangent_fourierCoefficient_zero
    {n : ℤ} (hn : n ≠ 0) (radialPlus radialMinus : ℂ) :
    fzzTorusHolonomyFourierCoefficient 0
        (fzzLinearReplicaAreaHolonomyTangent n radialPlus radialMinus) = -2 := by
  rw [fzzLinearReplicaAreaHolonomyTangent_fourierCoefficient_decomposition]
  rw [fzzAreaFourierCoefficient_id_mul_character 0 (-n) (by omega),
    fzzAreaFourierCoefficient_id_mul_character 0 n (by omega)]
  rw [show fzzTorusHolonomyFourierCoefficient 0 (fzzTorusHolonomyCharacter n) = 0 by
      simpa only [one_mul] using
        fzzAreaFourierCoefficient_const_mul_character_eq_zero 0 n 1 (by omega)]
  rw [show fzzTorusHolonomyFourierCoefficient 0 (fzzTorusHolonomyCharacter (-n)) = 0 by
      simpa only [one_mul] using
        fzzAreaFourierCoefficient_const_mul_character_eq_zero 0 (-n) 1 (by omega)]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp [hnR, hnC, Real.pi_ne_zero, Complex.I_ne_zero]
  ring_nf

/-- Positive marked resonance is fixed at `2/3`, independent of radial dressing. -/
theorem fzzLinearReplicaAreaHolonomyTangent_fourierCoefficient_two_mul
    {n : ℤ} (hn : n ≠ 0) (radialPlus radialMinus : ℂ) :
    fzzTorusHolonomyFourierCoefficient (2 * n)
        (fzzLinearReplicaAreaHolonomyTangent n radialPlus radialMinus) =
      (2 / 3 : ℂ) := by
  rw [fzzLinearReplicaAreaHolonomyTangent_fourierCoefficient_decomposition]
  rw [fzzAreaFourierCoefficient_id_mul_character (2 * n) (-n) (by omega),
    fzzAreaFourierCoefficient_id_mul_character (2 * n) n (by omega)]
  rw [show fzzTorusHolonomyFourierCoefficient (2 * n)
        (fzzTorusHolonomyCharacter n) = 0 by
      simpa only [one_mul] using
        fzzAreaFourierCoefficient_const_mul_character_eq_zero
          (2 * n) n 1 (by omega)]
  rw [show fzzTorusHolonomyFourierCoefficient (2 * n)
        (fzzTorusHolonomyCharacter (-n)) = 0 by
      simpa only [one_mul] using
        fzzAreaFourierCoefficient_const_mul_character_eq_zero
          (2 * n) (-n) 1 (by omega)]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp [hnR, hnC, Real.pi_ne_zero, Complex.I_ne_zero]
  ring_nf

/-- Negative marked resonance is fixed at `2/3`, independent of radial dressing. -/
theorem fzzLinearReplicaAreaHolonomyTangent_fourierCoefficient_neg_two_mul
    {n : ℤ} (hn : n ≠ 0) (radialPlus radialMinus : ℂ) :
    fzzTorusHolonomyFourierCoefficient (-2 * n)
        (fzzLinearReplicaAreaHolonomyTangent n radialPlus radialMinus) =
      (2 / 3 : ℂ) := by
  rw [fzzLinearReplicaAreaHolonomyTangent_fourierCoefficient_decomposition]
  rw [fzzAreaFourierCoefficient_id_mul_character (-2 * n) (-n) (by omega),
    fzzAreaFourierCoefficient_id_mul_character (-2 * n) n (by omega)]
  rw [show fzzTorusHolonomyFourierCoefficient (-2 * n)
        (fzzTorusHolonomyCharacter n) = 0 by
      simpa only [one_mul] using
        fzzAreaFourierCoefficient_const_mul_character_eq_zero
          (-2 * n) n 1 (by omega)]
  rw [show fzzTorusHolonomyFourierCoefficient (-2 * n)
        (fzzTorusHolonomyCharacter (-n)) = 0 by
      simpa only [one_mul] using
        fzzAreaFourierCoefficient_const_mul_character_eq_zero
          (-2 * n) (-n) 1 (by omega)]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp [hnR, hnC, Real.pi_ne_zero, Complex.I_ne_zero]
  ring_nf

/-- Exact torus response of linear replica-area tangent against odd holonomy square. -/
theorem fzzLinearReplicaAreaHolonomyTangent_weightedResponse
    {n : ℤ} (hn : n ≠ 0) (s₁ : ℝ) (τ : ℂ)
    (radialPlus radialMinus : ℂ) :
    (∫ s₂ in (0 : ℝ)..1,
      fzzLinearReplicaAreaHolonomyTangent n radialPlus radialMinus s₂ *
        fzzHigherGenusOddHolonomy n (torusJacobianTwist s₁ s₂ τ) ^ 2) =
      1 + (fzzHigherGenusBetaRadialSquare n s₁ τ +
        fzzHigherGenusGammaRadialSquare n s₁ τ) / 6 := by
  rw [fzzHigherGenusOddHolonomy_sq_weightedAverage_resonance n s₁ τ
    (fzzLinearReplicaAreaHolonomyTangent n radialPlus radialMinus)
    (continuous_fzzLinearReplicaAreaHolonomyTangent n radialPlus radialMinus)]
  rw [fzzLinearReplicaAreaHolonomyTangent_fourierCoefficient_neg_two_mul hn,
    fzzLinearReplicaAreaHolonomyTangent_fourierCoefficient_two_mul hn,
    fzzLinearReplicaAreaHolonomyTangent_fourierCoefficient_zero hn]
  ring

theorem fzzHigherGenusBetaRadialSquare_I
    (n : ℤ) (s₁ : ℝ) :
    fzzHigherGenusBetaRadialSquare n s₁ Complex.I =
      (Real.exp (-4 * Real.pi * (n : ℝ) * s₁) : ℂ) := by
  unfold fzzHigherGenusBetaRadialSquare higherGenusBetaTwistMultiplier
    torusJacobianTwist
  simp only [ofReal_zero, add_zero]
  rw [pow_two, ← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem fzzHigherGenusGammaRadialSquare_I
    (n : ℤ) (s₁ : ℝ) :
    fzzHigherGenusGammaRadialSquare n s₁ Complex.I =
      (Real.exp (4 * Real.pi * (n : ℝ) * s₁) : ℂ) := by
  unfold fzzHigherGenusGammaRadialSquare higherGenusGammaTwistMultiplier
    torusJacobianTwist
  simp only [ofReal_zero, add_zero]
  rw [pow_two, ← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Closed scalar form of normalized rectangular-torus replica-area response. -/
def fzzLinearReplicaAreaNormalizedResponse
    (n : ℤ) (s₁ : ℝ) : ℝ :=
  3 / 4 +
    (Real.exp (-4 * Real.pi * (n : ℝ) * s₁) +
      Real.exp (4 * Real.pi * (n : ℝ) * s₁)) / 8

theorem fzzLinearReplicaAreaNormalizedResponse_closedForm
    (n : ℤ) (s₁ : ℝ) :
    fzzLinearReplicaAreaNormalizedResponse n s₁ =
      3 / 4 +
        (Real.exp (-4 * Real.pi * (n : ℝ) * s₁) +
          Real.exp (4 * Real.pi * (n : ℝ) * s₁)) / 8 := by
  rfl

/-- Closed scalar is exactly the normalized literal holonomy integral. -/
theorem fzzLinearReplicaAreaNormalizedResponse_ofReal_eq_integral
    {n : ℤ} (hn : n ≠ 0) (s₁ : ℝ) (radialPlus radialMinus : ℂ) :
    (fzzLinearReplicaAreaNormalizedResponse n s₁ : ℂ) =
      (3 / 4 : ℂ) *
        (∫ s₂ in (0 : ℝ)..1,
          fzzLinearReplicaAreaHolonomyTangent n radialPlus radialMinus s₂ *
            fzzHigherGenusOddHolonomy n
              (torusJacobianTwist s₁ s₂ Complex.I) ^ 2) := by
  have hcomplex :
      (3 / 4 : ℂ) *
          (∫ s₂ in (0 : ℝ)..1,
            fzzLinearReplicaAreaHolonomyTangent n radialPlus radialMinus s₂ *
              fzzHigherGenusOddHolonomy n
                (torusJacobianTwist s₁ s₂ Complex.I) ^ 2) =
        ((3 / 4 +
          (Real.exp (-4 * Real.pi * (n : ℝ) * s₁) +
            Real.exp (4 * Real.pi * (n : ℝ) * s₁)) / 8 : ℝ) : ℂ) := by
    rw [fzzLinearReplicaAreaHolonomyTangent_weightedResponse hn,
      fzzHigherGenusBetaRadialSquare_I,
      fzzHigherGenusGammaRadialSquare_I]
    push_cast
    ring
  exact hcomplex.symm

theorem one_le_fzzLinearReplicaAreaNormalizedResponse
    (n : ℤ) (s₁ : ℝ) :
    1 ≤ fzzLinearReplicaAreaNormalizedResponse n s₁ := by
  let x : ℝ := 4 * Real.pi * (n : ℝ) * s₁
  have hypos : 0 < Real.exp x := Real.exp_pos x
  have hyne : Real.exp x ≠ 0 := ne_of_gt hypos
  have hprod : Real.exp x * (Real.exp x)⁻¹ = 1 := by
    exact mul_inv_cancel₀ hyne
  have hsum : 2 ≤ Real.exp (-x) + Real.exp x := by
    rw [Real.exp_neg]
    nlinarith [sq_nonneg (Real.exp x - 1)]
  rw [fzzLinearReplicaAreaNormalizedResponse_closedForm]
  have hnegarg : -4 * Real.pi * (n : ℝ) * s₁ = -x := by
    dsimp [x]
    ring
  rw [hnegarg]
  change 1 ≤ 3 / 4 + (Real.exp (-x) + Real.exp x) / 8
  linarith

theorem fzzLinearReplicaAreaNormalizedResponse_eq_one_iff
    {n : ℤ} (hn : n ≠ 0) (s₁ : ℝ) :
    fzzLinearReplicaAreaNormalizedResponse n s₁ = 1 ↔
      s₁ = 0 := by
  let x : ℝ := 4 * Real.pi * (n : ℝ) * s₁
  constructor
  · intro hresponse
    rw [fzzLinearReplicaAreaNormalizedResponse_closedForm] at hresponse
    have hnegarg : -4 * Real.pi * (n : ℝ) * s₁ = -x := by
      dsimp [x]
      ring
    rw [hnegarg] at hresponse
    change 3 / 4 + (Real.exp (-x) + Real.exp x) / 8 = 1 at hresponse
    have hsum : Real.exp (-x) + Real.exp x = 2 := by
      linarith
    have hypos : 0 < Real.exp x := Real.exp_pos x
    have hyne : Real.exp x ≠ 0 := ne_of_gt hypos
    have hprod : Real.exp x * (Real.exp x)⁻¹ = 1 := by
      exact mul_inv_cancel₀ hyne
    rw [Real.exp_neg] at hsum
    have hyone : Real.exp x = 1 := by
      nlinarith [sq_nonneg (Real.exp x - 1)]
    have hx : x = 0 := (Real.exp_eq_one_iff x).mp hyone
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hcoef : 4 * Real.pi * (n : ℝ) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hnR
    exact (mul_eq_zero.mp (by simpa [x, mul_assoc] using hx)).resolve_left hcoef
  · rintro rfl
    rw [fzzLinearReplicaAreaNormalizedResponse_closedForm]
    norm_num

/-- Passivity is possible exactly on zero-radial-monodromy wall. -/
theorem fzzLinearReplicaAreaNormalizedResponse_le_one_iff
    {n : ℤ} (hn : n ≠ 0) (s₁ : ℝ) :
    fzzLinearReplicaAreaNormalizedResponse n s₁ ≤ 1 ↔
      s₁ = 0 := by
  constructor
  · intro hle
    apply (fzzLinearReplicaAreaNormalizedResponse_eq_one_iff hn s₁).mp
    exact le_antisymm hle
      (one_le_fzzLinearReplicaAreaNormalizedResponse n s₁)
  · intro hs
    exact le_of_eq
      ((fzzLinearReplicaAreaNormalizedResponse_eq_one_iff hn s₁).mpr hs)

/-- On canonical parity-Mellin twists, area-response passivity is exactly critical-line
placement, pointwise and without a divisor hypothesis. -/
theorem fzzLinearReplicaAreaNormalizedResponse_mellinTorusTwist_le_one_iff
    (rho : ℂ) :
    fzzLinearReplicaAreaNormalizedResponse 1
        (fzzCigarParityMellinTorusTwist rho).im ≤ 1 ↔
      rho.re = 1 / 2 := by
  rw [fzzLinearReplicaAreaNormalizedResponse_le_one_iff (n := 1) (by norm_num),
    fzzCigarParityMellinTorusTwist_im_eq_zero_iff]

/-- Remaining source-side premise: every open-strip parity-Mellin divisor mode has passive
normalized linear replica-area response. -/
def FZZLinearReplicaAreaDivisorPassive : Prop :=
  ∀ rho : ℂ, 0 < rho.re → rho.re < 1 → FZZCigarParityMellinMode rho →
    fzzLinearReplicaAreaNormalizedResponse 1
      (fzzCigarParityMellinTorusTwist rho).im ≤ 1

theorem fzzLinearReplicaAreaDivisorPassive_iff_mellinComplete :
    FZZLinearReplicaAreaDivisorPassive ↔ FZZCigarParityMellinComplete := by
  constructor
  · intro hpassive rho h0 h1 hmode
    have hle := hpassive rho h0 h1 hmode
    have hre : rho.re = 1 / 2 :=
      (fzzLinearReplicaAreaNormalizedResponse_mellinTorusTwist_le_one_iff rho).mp hle
    refine ⟨rho.im, ?_⟩
    apply Complex.ext
    · rw [fzzPunctureHorizonDilationSpectralParameter_re, hre]
    · rw [fzzPunctureHorizonDilationSpectralParameter_im]
  · intro hcomplete rho h0 h1 hmode
    obtain ⟨E, hE⟩ := hcomplete rho h0 h1 hmode
    have hre : rho.re = 1 / 2 := by
      rw [hE, fzzPunctureHorizonDilationSpectralParameter_re]
    exact (fzzLinearReplicaAreaNormalizedResponse_mellinTorusTwist_le_one_iff rho).mpr hre

/-- Exact FZZ-P chain reduction: divisor-mode passivity of literal linear replica-area holonomy
response is equivalent to RH. -/
theorem fzzLinearReplicaAreaDivisorPassive_iff_riemannHypothesis :
    FZZLinearReplicaAreaDivisorPassive ↔ RiemannHypothesis :=
  fzzLinearReplicaAreaDivisorPassive_iff_mellinComplete.trans
    fzzCigarParityMellinComplete_iff_riemannHypothesis

end

end RHTower
