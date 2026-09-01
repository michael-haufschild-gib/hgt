import GaloisForLFunctions.RHTower.FZZCigarParityHigherGenusMellinCycleSelector
import GaloisForLFunctions.PNTPlus.Auxiliary

/-!
# FZZ torus holonomy Fourier-resonance no-go

The same-cigar cycle selector is pointwise in the higher-genus twist.  Physical cigar correlators,
however, integrate the flat gauge twist.  This file determines exactly what survives integration
over the compact Jacobian coordinate `s₂` in `twist = s₁ τ + s₂`.

For nonzero cycle `n`, the squared odd beta/gamma holonomy has only three Fourier charges:

`0, 2n, -2n`.

The zero coefficient is always `-1/2`, independent of radial monodromy.  Consequently the
unweighted averaged cycle-`n,2n` reality/passivity chamber holds even at an explicit nonzero
radial twist.  Haar averaging the bare squared holonomy therefore cannot be the missing FZZ-P Ward
producer.

The positive survivor is sharp.  The normalized `2n` and `-2n` coefficients are exactly the
squares of the reciprocal beta and gamma radial holonomies, their product is one, and unit norm of
the positive marked coefficient is equivalent to zero radial monodromy.  More generally, an
arbitrary continuous torus background couples to the squared odd holonomy only through its Fourier
coefficients at `0, -2n, 2n`.  Thus a surviving torus area law must carry a matching marked Fourier
mode (or leave this continuous-background class through the known nonlocal/branch-cut sector).

## RH-chain no-go

`literal parity-Mellin Gamma-zeta divisor mode`
→ `canonical torus twist`
→ `unmarked Haar-averaged squared holonomy Ward law`
→ `cycle-(1,2) chamber`
→ `critical line`
→ `RH`

fails at the averaged-to-pointwise arrow.  The marked-mode survivor identifies the exact
replacement premise instead of merely negating the route.

Physics sources:

* Hikida--Schomerus, arXiv:0805.3931, eqs. (4.14)--(4.15), (A.4)--(A.6): higher-genus cigar
  correlators integrate the complex twist holonomies.
* Halder--Jafferis, arXiv:2402.00932v3, sec. 3.2.3: the torus one-point of the nonlocal replica-area
  operator is left open and is expected to contain branch-cut information.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry.FZZCigar

/-- Unit-period additive character of integer charge `m`. -/
def fzzTorusHolonomyCharacter (m : ℤ) (s : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I * (s : ℂ))

@[simp] theorem fzzTorusHolonomyCharacter_zero (s : ℝ) :
    fzzTorusHolonomyCharacter 0 s = 1 := by
  simp [fzzTorusHolonomyCharacter]

/-- Torus characters add their integer charges under multiplication. -/
theorem fzzTorusHolonomyCharacter_mul (m k : ℤ) (s : ℝ) :
    fzzTorusHolonomyCharacter m s * fzzTorusHolonomyCharacter k s =
      fzzTorusHolonomyCharacter (m + k) s := by
  rw [fzzTorusHolonomyCharacter, fzzTorusHolonomyCharacter,
    fzzTorusHolonomyCharacter, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Reversing charge inverts the unit-period character. -/
theorem fzzTorusHolonomyCharacter_neg (m : ℤ) (s : ℝ) :
    fzzTorusHolonomyCharacter (-m) s =
      (fzzTorusHolonomyCharacter m s)⁻¹ := by
  rw [fzzTorusHolonomyCharacter, fzzTorusHolonomyCharacter, ← Complex.exp_neg]
  congr 2
  push_cast
  ring

/-- Exact integer-character orthogonality on one compact holonomy period. -/
theorem intervalIntegral_fzzTorusHolonomyCharacter (m : ℤ) :
    (∫ s in (0 : ℝ)..1, fzzTorusHolonomyCharacter m s) =
      if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [fzzTorusHolonomyCharacter]
  · rw [if_neg hm]
    let c : ℂ := ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hc : c ≠ 0 := by
      apply mul_ne_zero
      · exact Complex.ofReal_ne_zero.mpr
          (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hmR)
      · exact Complex.I_ne_zero
    have hderiv : ∀ t : ℝ, HasDerivAt
        (fun s : ℝ => Complex.exp (c * (s : ℂ)) / c)
        (Complex.exp (c * (t : ℂ))) t := by
      intro t
      have hlin : HasDerivAt (fun s : ℝ => c * (s : ℂ)) c t := by
        simpa only [mul_one] using (Complex.hasDerivAt_ofReal t).const_mul c
      have hd := hlin.cexp.div_const c
      have hval : Complex.exp (c * (t : ℂ)) * c / c =
          Complex.exp (c * (t : ℂ)) := by
        field_simp
      rw [hval] at hd
      exact hd
    have hint : IntervalIntegrable
        (fun s : ℝ => Complex.exp (c * (s : ℂ))) volume 0 1 := by
      refine Continuous.intervalIntegrable ?_ 0 1
      fun_prop
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := 1) (fun t _ => hderiv t) hint
    have hperiod : Complex.exp (c * (1 : ℂ)) = 1 := by
      rw [Complex.exp_eq_one_iff]
      refine ⟨m, ?_⟩
      dsimp [c]
      push_cast
      ring
    have hperiodReal : Complex.exp (c * ((1 : ℝ) : ℂ)) = 1 := by
      simp only [ofReal_one]
      exact hperiod
    have hzeroReal : Complex.exp (c * ((0 : ℝ) : ℂ)) = 1 := by
      simp
    change (∫ s in (0 : ℝ)..1, Complex.exp (c * (s : ℂ))) = 0
    rw [hFTC, hperiodReal, hzeroReal]
    ring

/-- `m`-th Fourier coefficient in the compact holonomy coordinate. -/
def fzzTorusHolonomyFourierCoefficient (m : ℤ) (f : ℝ → ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..1, fzzTorusHolonomyCharacter (-m) s * f s

/-- Square of the beta holonomy at the radial representative `s₂=0`. -/
def fzzHigherGenusBetaRadialSquare (n : ℤ) (s₁ : ℝ) (τ : ℂ) : ℂ :=
  higherGenusBetaTwistMultiplier n (torusJacobianTwist s₁ 0 τ) ^ 2

/-- Square of the reciprocal gamma holonomy at the radial representative `s₂=0`. -/
def fzzHigherGenusGammaRadialSquare (n : ℤ) (s₁ : ℝ) (τ : ℂ) : ℂ :=
  higherGenusGammaTwistMultiplier n (torusJacobianTwist s₁ 0 τ) ^ 2

/-- Beta holonomy separates into radial and compact-character factors after squaring. -/
theorem higherGenusBetaTwistMultiplier_sq_torusJacobian
    (n : ℤ) (s₁ s₂ : ℝ) (τ : ℂ) :
    higherGenusBetaTwistMultiplier n (torusJacobianTwist s₁ s₂ τ) ^ 2 =
      fzzHigherGenusBetaRadialSquare n s₁ τ *
        fzzTorusHolonomyCharacter (2 * n) s₂ := by
  have hsplit :
      higherGenusBetaTwistMultiplier n (torusJacobianTwist s₁ s₂ τ) =
        higherGenusBetaTwistMultiplier n (torusJacobianTwist s₁ 0 τ) *
          fzzTorusHolonomyCharacter n s₂ := by
    rw [higherGenusBetaTwistMultiplier, torusJacobianTwist,
      higherGenusBetaTwistMultiplier, torusJacobianTwist,
      fzzTorusHolonomyCharacter]
    simp only [ofReal_zero, add_zero]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hchar : fzzTorusHolonomyCharacter n s₂ ^ 2 =
      fzzTorusHolonomyCharacter (2 * n) s₂ := by
    rw [pow_two, fzzTorusHolonomyCharacter_mul]
    congr 2
    ring
  rw [hsplit, fzzHigherGenusBetaRadialSquare, mul_pow, hchar]

/-- Gamma holonomy separates into the opposite compact character after squaring. -/
theorem higherGenusGammaTwistMultiplier_sq_torusJacobian
    (n : ℤ) (s₁ s₂ : ℝ) (τ : ℂ) :
    higherGenusGammaTwistMultiplier n (torusJacobianTwist s₁ s₂ τ) ^ 2 =
      fzzHigherGenusGammaRadialSquare n s₁ τ *
        fzzTorusHolonomyCharacter (-2 * n) s₂ := by
  have hsplit :
      higherGenusGammaTwistMultiplier n (torusJacobianTwist s₁ s₂ τ) =
        higherGenusGammaTwistMultiplier n (torusJacobianTwist s₁ 0 τ) *
          fzzTorusHolonomyCharacter (-n) s₂ := by
    rw [higherGenusGammaTwistMultiplier, torusJacobianTwist,
      higherGenusGammaTwistMultiplier, torusJacobianTwist,
      fzzTorusHolonomyCharacter]
    simp only [ofReal_zero, add_zero]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hchar : fzzTorusHolonomyCharacter (-n) s₂ ^ 2 =
      fzzTorusHolonomyCharacter (-2 * n) s₂ := by
    rw [pow_two, fzzTorusHolonomyCharacter_mul]
    congr 2
    ring
  rw [hsplit, fzzHigherGenusGammaRadialSquare, mul_pow, hchar]

/-- Squared odd holonomy is the reciprocal pair minus its neutral cross term. -/
theorem fzzHigherGenusOddHolonomy_sq (n : ℤ) (twist : ℂ) :
    fzzHigherGenusOddHolonomy n twist ^ 2 =
      (higherGenusBetaTwistMultiplier n twist ^ 2 +
        higherGenusGammaTwistMultiplier n twist ^ 2 - 2) / 4 := by
  rw [fzzHigherGenusOddHolonomy]
  have hrecip := higherGenusBetaTwist_mul_gammaTwist n twist
  rw [show ((higherGenusBetaTwistMultiplier n twist -
      higherGenusGammaTwistMultiplier n twist) / 2) ^ 2 =
      (higherGenusBetaTwistMultiplier n twist ^ 2 +
        higherGenusGammaTwistMultiplier n twist ^ 2 -
        2 * (higherGenusBetaTwistMultiplier n twist *
          higherGenusGammaTwistMultiplier n twist)) / 4 by ring]
  rw [hrecip]
  ring

/-- **Three-frequency law.** The squared odd holonomy has only charges `0, 2n, -2n`. -/
theorem fzzHigherGenusOddHolonomy_sq_torusJacobian_threeFrequency
    (n : ℤ) (s₁ s₂ : ℝ) (τ : ℂ) :
    fzzHigherGenusOddHolonomy n (torusJacobianTwist s₁ s₂ τ) ^ 2 =
      (fzzHigherGenusBetaRadialSquare n s₁ τ *
          fzzTorusHolonomyCharacter (2 * n) s₂ +
        fzzHigherGenusGammaRadialSquare n s₁ τ *
          fzzTorusHolonomyCharacter (-2 * n) s₂ - 2) / 4 := by
  rw [fzzHigherGenusOddHolonomy_sq,
    higherGenusBetaTwistMultiplier_sq_torusJacobian,
    higherGenusGammaTwistMultiplier_sq_torusJacobian]

theorem continuous_fzzTorusHolonomyCharacter (m : ℤ) :
    Continuous (fzzTorusHolonomyCharacter m) := by
  unfold fzzTorusHolonomyCharacter
  fun_prop

private theorem fzzTorusHolonomyFourierCoefficient_add
    (m : ℤ) (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    fzzTorusHolonomyFourierCoefficient m (fun s => f s + g s) =
      fzzTorusHolonomyFourierCoefficient m f +
        fzzTorusHolonomyFourierCoefficient m g := by
  rw [fzzTorusHolonomyFourierCoefficient,
    fzzTorusHolonomyFourierCoefficient,
    fzzTorusHolonomyFourierCoefficient]
  have hcf : IntervalIntegrable
      (fun s => fzzTorusHolonomyCharacter (-m) s * f s) volume 0 1 :=
    ((continuous_fzzTorusHolonomyCharacter (-m)).mul hf).intervalIntegrable 0 1
  have hcg : IntervalIntegrable
      (fun s => fzzTorusHolonomyCharacter (-m) s * g s) volume 0 1 :=
    ((continuous_fzzTorusHolonomyCharacter (-m)).mul hg).intervalIntegrable 0 1
  rw [show (fun s => fzzTorusHolonomyCharacter (-m) s * (f s + g s)) =
      (fun s => fzzTorusHolonomyCharacter (-m) s * f s +
        fzzTorusHolonomyCharacter (-m) s * g s) by funext s; ring,
    intervalIntegral.integral_add hcf hcg]

private theorem fzzTorusHolonomyFourierCoefficient_const_mul_character
    (m k : ℤ) (c : ℂ) :
    fzzTorusHolonomyFourierCoefficient m
        (fun s => c * fzzTorusHolonomyCharacter k s) =
      c * if k = m then 1 else 0 := by
  rw [fzzTorusHolonomyFourierCoefficient]
  calc
    (∫ s in (0 : ℝ)..1,
        fzzTorusHolonomyCharacter (-m) s *
          (c * fzzTorusHolonomyCharacter k s)) =
        ∫ s in (0 : ℝ)..1,
          c * fzzTorusHolonomyCharacter (-m + k) s := by
            apply intervalIntegral.integral_congr
            intro s _
            calc
              fzzTorusHolonomyCharacter (-m) s *
                    (c * fzzTorusHolonomyCharacter k s) =
                  c * (fzzTorusHolonomyCharacter (-m) s *
                    fzzTorusHolonomyCharacter k s) := by ring
              _ = c * fzzTorusHolonomyCharacter (-m + k) s := by
                    rw [fzzTorusHolonomyCharacter_mul]
    _ = c * ∫ s in (0 : ℝ)..1,
          fzzTorusHolonomyCharacter (-m + k) s := by
            rw [intervalIntegral.integral_const_mul]
    _ = c * if k = m then 1 else 0 := by
            rw [intervalIntegral_fzzTorusHolonomyCharacter]
            by_cases hkm : k = m
            · subst k
              simp
            · have hfreq : -m + k ≠ 0 := by omega
              simp [hfreq, hkm]

/-- **Complete Fourier classification.** This sum-of-Kronecker-deltas form remains valid at
`n=0`, where the three frequencies collide and cancel. -/
theorem fzzHigherGenusOddHolonomy_sq_fourierCoefficient
    (n m : ℤ) (s₁ : ℝ) (τ : ℂ) :
    fzzTorusHolonomyFourierCoefficient m
        (fun s₂ => fzzHigherGenusOddHolonomy n
          (torusJacobianTwist s₁ s₂ τ) ^ 2) =
      fzzHigherGenusBetaRadialSquare n s₁ τ / 4 *
          (if 2 * n = m then 1 else 0) +
        fzzHigherGenusGammaRadialSquare n s₁ τ / 4 *
          (if -2 * n = m then 1 else 0) +
        (-1 / 2 : ℂ) * (if (0 : ℤ) = m then 1 else 0) := by
  rw [show (fun s₂ => fzzHigherGenusOddHolonomy n
      (torusJacobianTwist s₁ s₂ τ) ^ 2) =
      (fun s₂ =>
        fzzHigherGenusBetaRadialSquare n s₁ τ / 4 *
            fzzTorusHolonomyCharacter (2 * n) s₂ +
          fzzHigherGenusGammaRadialSquare n s₁ τ / 4 *
            fzzTorusHolonomyCharacter (-2 * n) s₂ +
          (-1 / 2 : ℂ) * fzzTorusHolonomyCharacter 0 s₂) by
      funext s₂
      rw [fzzHigherGenusOddHolonomy_sq_torusJacobian_threeFrequency,
        fzzTorusHolonomyCharacter_zero]
      ring]
  rw [fzzTorusHolonomyFourierCoefficient_add]
  · rw [fzzTorusHolonomyFourierCoefficient_add]
    · rw [fzzTorusHolonomyFourierCoefficient_const_mul_character,
        fzzTorusHolonomyFourierCoefficient_const_mul_character,
        fzzTorusHolonomyFourierCoefficient_const_mul_character]
    · exact continuous_const.mul
        (continuous_fzzTorusHolonomyCharacter (2 * n))
    · exact continuous_const.mul
        (continuous_fzzTorusHolonomyCharacter (-2 * n))
  · exact (continuous_const.mul
      (continuous_fzzTorusHolonomyCharacter (2 * n))).add
        (continuous_const.mul
          (continuous_fzzTorusHolonomyCharacter (-2 * n)))
  · exact continuous_const.mul (continuous_fzzTorusHolonomyCharacter 0)

/-- Every nonresonant Fourier coefficient vanishes exactly. -/
theorem fzzHigherGenusOddHolonomy_sq_fourierCoefficient_eq_zero_of_offResonance
    (n m : ℤ) (s₁ : ℝ) (τ : ℂ)
    (hpos : m ≠ 2 * n) (hneg : m ≠ -2 * n) (hzero : m ≠ 0) :
    fzzTorusHolonomyFourierCoefficient m
        (fun s₂ => fzzHigherGenusOddHolonomy n
          (torusJacobianTwist s₁ s₂ τ) ^ 2) = 0 := by
  rw [fzzHigherGenusOddHolonomy_sq_fourierCoefficient]
  have hpos' : 2 * n ≠ m := Ne.symm hpos
  have hneg' : -(2 * n) ≠ m := by
    intro h
    apply hneg
    omega
  have hzero' : (0 : ℤ) ≠ m := Ne.symm hzero
  simp [hpos', hneg', hzero']

/-- Haar zero mode is `0` at the trivial cycle and `-1/2` at every nontrivial cycle. -/
theorem fzzHigherGenusOddHolonomy_sq_zeroCoefficient
    (n : ℤ) (s₁ : ℝ) (τ : ℂ) :
    fzzTorusHolonomyFourierCoefficient 0
        (fun s₂ => fzzHigherGenusOddHolonomy n
          (torusJacobianTwist s₁ s₂ τ) ^ 2) =
      if n = 0 then 0 else (-1 / 2 : ℂ) := by
  rw [fzzHigherGenusOddHolonomy_sq_fourierCoefficient]
  by_cases hn : n = 0
  · subst n
    simp [fzzHigherGenusBetaRadialSquare, fzzHigherGenusGammaRadialSquare,
      higherGenusBetaTwistMultiplier, higherGenusGammaTwistMultiplier]
    ring
  · have htwo : 2 * n ≠ 0 := by omega
    simp [hn, htwo]

/-- Positive marked mode recovers one quarter of the beta radial square. -/
theorem fzzHigherGenusOddHolonomy_sq_markedPositiveCoefficient
    {n : ℤ} (hn : n ≠ 0) (s₁ : ℝ) (τ : ℂ) :
    fzzTorusHolonomyFourierCoefficient (2 * n)
        (fun s₂ => fzzHigherGenusOddHolonomy n
          (torusJacobianTwist s₁ s₂ τ) ^ 2) =
      fzzHigherGenusBetaRadialSquare n s₁ τ / 4 := by
  rw [fzzHigherGenusOddHolonomy_sq_fourierCoefficient]
  have hopp : -(2 * n) ≠ 2 * n := by omega
  have hzero : (0 : ℤ) ≠ 2 * n := by omega
  simp [hopp, hzero]

/-- Negative marked mode recovers one quarter of the reciprocal gamma radial square. -/
theorem fzzHigherGenusOddHolonomy_sq_markedNegativeCoefficient
    {n : ℤ} (hn : n ≠ 0) (s₁ : ℝ) (τ : ℂ) :
    fzzTorusHolonomyFourierCoefficient (-2 * n)
        (fun s₂ => fzzHigherGenusOddHolonomy n
          (torusJacobianTwist s₁ s₂ τ) ^ 2) =
      fzzHigherGenusGammaRadialSquare n s₁ τ / 4 := by
  rw [fzzHigherGenusOddHolonomy_sq_fourierCoefficient]
  have hopp : 2 * n ≠ -(2 * n) := by omega
  have hzero : (0 : ℤ) ≠ -(2 * n) := by omega
  simp [hopp, hzero]

/-- Normalized positive marked Fourier coefficient. -/
def fzzHigherGenusMarkedPositiveHolonomyCoefficient
    (n : ℤ) (s₁ : ℝ) (τ : ℂ) : ℂ :=
  4 * fzzTorusHolonomyFourierCoefficient (2 * n)
    (fun s₂ => fzzHigherGenusOddHolonomy n
      (torusJacobianTwist s₁ s₂ τ) ^ 2)

/-- Normalized negative marked Fourier coefficient. -/
def fzzHigherGenusMarkedNegativeHolonomyCoefficient
    (n : ℤ) (s₁ : ℝ) (τ : ℂ) : ℂ :=
  4 * fzzTorusHolonomyFourierCoefficient (-2 * n)
    (fun s₂ => fzzHigherGenusOddHolonomy n
      (torusJacobianTwist s₁ s₂ τ) ^ 2)

theorem fzzHigherGenusMarkedPositiveHolonomyCoefficient_eq_betaSquare
    {n : ℤ} (hn : n ≠ 0) (s₁ : ℝ) (τ : ℂ) :
    fzzHigherGenusMarkedPositiveHolonomyCoefficient n s₁ τ =
      fzzHigherGenusBetaRadialSquare n s₁ τ := by
  rw [fzzHigherGenusMarkedPositiveHolonomyCoefficient,
    fzzHigherGenusOddHolonomy_sq_markedPositiveCoefficient hn]
  ring

theorem fzzHigherGenusMarkedNegativeHolonomyCoefficient_eq_gammaSquare
    {n : ℤ} (hn : n ≠ 0) (s₁ : ℝ) (τ : ℂ) :
    fzzHigherGenusMarkedNegativeHolonomyCoefficient n s₁ τ =
      fzzHigherGenusGammaRadialSquare n s₁ τ := by
  rw [fzzHigherGenusMarkedNegativeHolonomyCoefficient,
    fzzHigherGenusOddHolonomy_sq_markedNegativeCoefficient hn]
  ring

/-- The two surviving marked modes retain the exact reciprocal holonomy law. -/
theorem fzzHigherGenusMarkedHolonomyCoefficients_mul_eq_one
    {n : ℤ} (hn : n ≠ 0) (s₁ : ℝ) (τ : ℂ) :
    fzzHigherGenusMarkedPositiveHolonomyCoefficient n s₁ τ *
      fzzHigherGenusMarkedNegativeHolonomyCoefficient n s₁ τ = 1 := by
  rw [fzzHigherGenusMarkedPositiveHolonomyCoefficient_eq_betaSquare hn,
    fzzHigherGenusMarkedNegativeHolonomyCoefficient_eq_gammaSquare hn,
    fzzHigherGenusBetaRadialSquare, fzzHigherGenusGammaRadialSquare,
    ← mul_pow, higherGenusBetaTwist_mul_gammaTwist]
  simp

/-- **Marked survivor selector.** Unit norm of the surviving positive Fourier mode is equivalent
to zero radial black-hole monodromy. -/
theorem norm_fzzHigherGenusMarkedPositiveHolonomyCoefficient_eq_one_iff
    {b : ℝ} (hb : 0 < b) {n : ℤ} (hn : n ≠ 0) (s₁ : ℝ) (τ : ℂ) :
    ‖fzzHigherGenusMarkedPositiveHolonomyCoefficient n s₁ τ‖ = 1 ↔
      higherGenusRadialMonodromy b n (torusJacobianTwist s₁ 0 τ) = 0 := by
  rw [fzzHigherGenusMarkedPositiveHolonomyCoefficient_eq_betaSquare hn,
    fzzHigherGenusBetaRadialSquare, norm_pow]
  have hbase := norm_higherGenusBetaTwistMultiplier_eq_one_iff
    hb n (torusJacobianTwist s₁ 0 τ)
  constructor
  · intro hsq
    apply hbase.mp
    have hnonneg : 0 ≤ ‖higherGenusBetaTwistMultiplier n
        (torusJacobianTwist s₁ 0 τ)‖ := norm_nonneg _
    nlinarith
  · intro hradial
    rw [hbase.mpr hradial]
    simp

/-- Cycle-pair chamber formed after compact-holonomy zero-mode projection. -/
def FZZAveragedHigherGenusCyclePairKreinSign
    (n : ℤ) (s₁ : ℝ) (τ : ℂ) : Prop :=
  (fzzTorusHolonomyFourierCoefficient 0
      (fun s₂ => fzzHigherGenusOddHolonomy n
        (torusJacobianTwist s₁ s₂ τ) ^ 2)).im = 0 ∧
    (fzzTorusHolonomyFourierCoefficient 0
      (fun s₂ => fzzHigherGenusOddHolonomy (2 * n)
        (torusJacobianTwist s₁ s₂ τ) ^ 2)).re ≤ 0

/-- The averaged reality/passivity chamber is automatic at every twist and every cycle. -/
theorem fzzAveragedHigherGenusCyclePairKreinSign_all
    (n : ℤ) (s₁ : ℝ) (τ : ℂ) :
    FZZAveragedHigherGenusCyclePairKreinSign n s₁ τ := by
  rw [FZZAveragedHigherGenusCyclePairKreinSign,
    fzzHigherGenusOddHolonomy_sq_zeroCoefficient,
    fzzHigherGenusOddHolonomy_sq_zeroCoefficient]
  by_cases hn : n = 0
  · subst n
    simp
  · have htwo : 2 * n ≠ 0 := by omega
    simp [hn, htwo]
    norm_num

/-- **Averaged-selector no-go.** The averaged chamber holds at an explicit nonzero radial
monodromy, so it cannot imply the pointwise selector chamber. -/
theorem fzzAveragedHigherGenusCyclePairKreinSign_off_radialWall :
    FZZAveragedHigherGenusCyclePairKreinSign 1 1 Complex.I ∧
      higherGenusRadialMonodromy 1 1
        (torusJacobianTwist 1 0 Complex.I) ≠ 0 := by
  refine ⟨fzzAveragedHigherGenusCyclePairKreinSign_all 1 1 Complex.I, ?_⟩
  rw [higherGenusRadialMonodromy_torusJacobian]
  norm_num [Real.pi_ne_zero]

private theorem intervalIntegral_fzzTorusHolonomyCharacter_mul_eq_coefficient
    (k : ℤ) (A : ℝ → ℂ) :
    (∫ s in (0 : ℝ)..1, fzzTorusHolonomyCharacter k s * A s) =
      fzzTorusHolonomyFourierCoefficient (-k) A := by
  rw [fzzTorusHolonomyFourierCoefficient]
  congr 1
  funext s
  congr 1
  ring

/-- **Weighted resonance law.** Any continuous torus background couples to the squared odd
holonomy only through its Fourier coefficients at charges `0, -2n, 2n`. -/
theorem fzzHigherGenusOddHolonomy_sq_weightedAverage_resonance
    (n : ℤ) (s₁ : ℝ) (τ : ℂ) (A : ℝ → ℂ) (hA : Continuous A) :
    (∫ s₂ in (0 : ℝ)..1,
      A s₂ * fzzHigherGenusOddHolonomy n
        (torusJacobianTwist s₁ s₂ τ) ^ 2) =
      fzzHigherGenusBetaRadialSquare n s₁ τ / 4 *
          fzzTorusHolonomyFourierCoefficient (-2 * n) A +
        fzzHigherGenusGammaRadialSquare n s₁ τ / 4 *
          fzzTorusHolonomyFourierCoefficient (2 * n) A +
        (-1 / 2 : ℂ) * fzzTorusHolonomyFourierCoefficient 0 A := by
  rw [show (fun s₂ => A s₂ * fzzHigherGenusOddHolonomy n
      (torusJacobianTwist s₁ s₂ τ) ^ 2) =
      (fun s₂ =>
        fzzHigherGenusBetaRadialSquare n s₁ τ / 4 *
            (fzzTorusHolonomyCharacter (2 * n) s₂ * A s₂) +
          fzzHigherGenusGammaRadialSquare n s₁ τ / 4 *
            (fzzTorusHolonomyCharacter (-2 * n) s₂ * A s₂) +
          (-1 / 2 : ℂ) * (fzzTorusHolonomyCharacter 0 s₂ * A s₂)) by
      funext s₂
      rw [fzzHigherGenusOddHolonomy_sq_torusJacobian_threeFrequency,
        fzzTorusHolonomyCharacter_zero]
      ring]
  have hfirst : Continuous (fun s₂ =>
      fzzHigherGenusBetaRadialSquare n s₁ τ / 4 *
        (fzzTorusHolonomyCharacter (2 * n) s₂ * A s₂)) :=
    continuous_const.mul
      ((continuous_fzzTorusHolonomyCharacter (2 * n)).mul hA)
  have hsecond : Continuous (fun s₂ =>
      fzzHigherGenusGammaRadialSquare n s₁ τ / 4 *
        (fzzTorusHolonomyCharacter (-2 * n) s₂ * A s₂)) :=
    continuous_const.mul
      ((continuous_fzzTorusHolonomyCharacter (-2 * n)).mul hA)
  have hzero : Continuous (fun s₂ =>
      (-1 / 2 : ℂ) * (fzzTorusHolonomyCharacter 0 s₂ * A s₂)) :=
    continuous_const.mul ((continuous_fzzTorusHolonomyCharacter 0).mul hA)
  calc
    (∫ s₂ in (0 : ℝ)..1,
        fzzHigherGenusBetaRadialSquare n s₁ τ / 4 *
              (fzzTorusHolonomyCharacter (2 * n) s₂ * A s₂) +
            fzzHigherGenusGammaRadialSquare n s₁ τ / 4 *
              (fzzTorusHolonomyCharacter (-2 * n) s₂ * A s₂) +
          (-1 / 2 : ℂ) * (fzzTorusHolonomyCharacter 0 s₂ * A s₂)) =
        (∫ s₂ in (0 : ℝ)..1,
          fzzHigherGenusBetaRadialSquare n s₁ τ / 4 *
              (fzzTorusHolonomyCharacter (2 * n) s₂ * A s₂) +
            fzzHigherGenusGammaRadialSquare n s₁ τ / 4 *
              (fzzTorusHolonomyCharacter (-2 * n) s₂ * A s₂)) +
        (∫ s₂ in (0 : ℝ)..1,
          (-1 / 2 : ℂ) * (fzzTorusHolonomyCharacter 0 s₂ * A s₂)) := by
            exact intervalIntegral.integral_add
              ((hfirst.add hsecond).intervalIntegrable 0 1)
              (hzero.intervalIntegrable 0 1)
    _ = (∫ s₂ in (0 : ℝ)..1,
          fzzHigherGenusBetaRadialSquare n s₁ τ / 4 *
            (fzzTorusHolonomyCharacter (2 * n) s₂ * A s₂)) +
        (∫ s₂ in (0 : ℝ)..1,
          fzzHigherGenusGammaRadialSquare n s₁ τ / 4 *
            (fzzTorusHolonomyCharacter (-2 * n) s₂ * A s₂)) +
        (∫ s₂ in (0 : ℝ)..1,
          (-1 / 2 : ℂ) * (fzzTorusHolonomyCharacter 0 s₂ * A s₂)) := by
            rw [intervalIntegral.integral_add
              (hfirst.intervalIntegrable 0 1)
              (hsecond.intervalIntegrable 0 1)]
    _ = fzzHigherGenusBetaRadialSquare n s₁ τ / 4 *
          fzzTorusHolonomyFourierCoefficient (-2 * n) A +
        fzzHigherGenusGammaRadialSquare n s₁ τ / 4 *
          fzzTorusHolonomyFourierCoefficient (2 * n) A +
        (-1 / 2 : ℂ) * fzzTorusHolonomyFourierCoefficient 0 A := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const_mul,
            intervalIntegral_fzzTorusHolonomyCharacter_mul_eq_coefficient,
            intervalIntegral_fzzTorusHolonomyCharacter_mul_eq_coefficient,
            intervalIntegral_fzzTorusHolonomyCharacter_mul_eq_coefficient]
          ring

/-- Backgrounds with a gap at both resonant charges retain only the blind zero mode. -/
theorem fzzHigherGenusOddHolonomy_sq_weightedAverage_eq_zeroMode_of_resonanceGap
    (n : ℤ) (s₁ : ℝ) (τ : ℂ) (A : ℝ → ℂ) (hA : Continuous A)
    (hneg : fzzTorusHolonomyFourierCoefficient (-2 * n) A = 0)
    (hpos : fzzTorusHolonomyFourierCoefficient (2 * n) A = 0) :
    (∫ s₂ in (0 : ℝ)..1,
      A s₂ * fzzHigherGenusOddHolonomy n
        (torusJacobianTwist s₁ s₂ τ) ^ 2) =
      (-1 / 2 : ℂ) * fzzTorusHolonomyFourierCoefficient 0 A := by
  rw [fzzHigherGenusOddHolonomy_sq_weightedAverage_resonance
    n s₁ τ A hA, hneg, hpos]
  ring

end

end RHTower
