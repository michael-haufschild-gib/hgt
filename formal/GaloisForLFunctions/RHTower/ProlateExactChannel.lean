import GaloisForLFunctions.RHTower.ProlateChannelBranch
import GaloisForLFunctions.RHTower.ProlateChannelSum
import GaloisForLFunctions.RHTower.ProlateDilatedLeftEndpoint
import GaloisForLFunctions.RHTower.ProlateFullPrimitive
import GaloisForLFunctions.RHTower.ProlateLiouvilleOscillator

/-!
# The exact radial mode in two-branch form

The oscillator `w = h u` recovers the mode by `R = w/(h √(x²-1))`, and `w` is exactly
`A cos φ + B sin φ`.  So the mode itself has a two-branch representation with no error term:

```text
R(x) = envelope(x) · (A(x) cos φ(x) + B(x) sin φ(x)),   envelope = 1/(h √(x²-1)).
```

The envelope decays like `1/(√c x)` and its derivative like `1/(√c x²)`, which is what the
exterior estimate needs after the `√x` normalization.
-/

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

/-- The envelope of the exterior representation. -/
def prolateEnvelope (s c x : ℝ) : ℝ := 1 / (lgSpeedAmp s c x * Real.sqrt (x ^ (2 : ℕ) - 1))

/-- Its derivative. -/
def prolateEnvelopeDeriv (s c x : ℝ) : ℝ :=
  -(lgSpeedAmpDeriv s c x * Real.sqrt (x ^ (2 : ℕ) - 1)
      + lgSpeedAmp s c x * (x / Real.sqrt (x ^ (2 : ℕ) - 1)))
    / (lgSpeedAmp s c x * Real.sqrt (x ^ (2 : ℕ) - 1)) ^ (2 : ℕ)

theorem sqrt_c_le_lgSpeedAmp {s c x : ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hx : 1 < x) :
    Real.sqrt c ≤ lgSpeedAmp s c x := by
  have hsp1 : (1 : ℝ) ≤ xiSpeed s x := one_le_xiSpeed (by linarith) hx
  rw [lgSpeedAmp, prolatePhaseSpeed]
  refine Real.sqrt_le_sqrt ?_
  nlinarith [hc.le]

theorem lgSpeedAmp_le_sqrt_two_c {s c x : ℝ} (hs0 : 0 ≤ s) (hc : 0 < c) (hx : 2 ≤ x) :
    lgSpeedAmp s c x ≤ Real.sqrt (2 * c) := by
  have hsp2 : xiSpeed s x ≤ 2 := xiSpeed_le_two hs0 hx
  rw [lgSpeedAmp, prolatePhaseSpeed]
  refine Real.sqrt_le_sqrt ?_
  nlinarith [hc.le]

theorem hasDerivAt_prolateEnvelope {s c x : ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hx : 1 < x) :
    HasDerivAt (prolateEnvelope s c) (prolateEnvelopeDeriv s c x) x := by
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hsd : (0 : ℝ) < Real.sqrt (x ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr hd
  have hh : 0 < lgSpeedAmp s c x := lgSpeedAmp_pos hs1 hc hx
  have hnf : HasDerivAt (fun t : ℝ => Real.sqrt (t ^ (2 : ℕ) - 1))
      (x / Real.sqrt (x ^ (2 : ℕ) - 1)) x := by
    have h := hasDerivAt_nfWeight hx
    have hfun : nfWeight = fun t : ℝ => Real.sqrt (t ^ (2 : ℕ) - 1) := by
      funext t
      rw [nfWeight]
    rw [hfun, nfWeightDeriv] at h
    exact h
  have hden : HasDerivAt (fun t : ℝ => lgSpeedAmp s c t * Real.sqrt (t ^ (2 : ℕ) - 1))
      (lgSpeedAmpDeriv s c x * Real.sqrt (x ^ (2 : ℕ) - 1)
        + lgSpeedAmp s c x * (x / Real.sqrt (x ^ (2 : ℕ) - 1))) x :=
    (hasDerivAt_lgSpeedAmp hs1 hc hx).fun_mul hnf
  have hne : lgSpeedAmp s c x * Real.sqrt (x ^ (2 : ℕ) - 1) ≠ 0 := by positivity
  have h := (hasDerivAt_const x (1 : ℝ)).fun_div hden hne
  have hfun : prolateEnvelope s c
      = fun t : ℝ => 1 / (lgSpeedAmp s c t * Real.sqrt (t ^ (2 : ℕ) - 1)) := by
    funext t
    rw [prolateEnvelope]
  have hval : (0 * (lgSpeedAmp s c x * Real.sqrt (x ^ (2 : ℕ) - 1))
        - 1 * (lgSpeedAmpDeriv s c x * Real.sqrt (x ^ (2 : ℕ) - 1)
          + lgSpeedAmp s c x * (x / Real.sqrt (x ^ (2 : ℕ) - 1))))
      / (lgSpeedAmp s c x * Real.sqrt (x ^ (2 : ℕ) - 1)) ^ (2 : ℕ)
      = prolateEnvelopeDeriv s c x := by
    rw [prolateEnvelopeDeriv]
    ring
  rw [hfun, ← hval]
  exact h

/-- **The exact mode in two-branch form.**  An identity: the oscillator representation is exact and
the rescaling is invertible. -/
theorem radialProlate_eq_branches {s c x : ℝ} {R DR : ℝ → ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hx : 1 < x) :
    R x = prolateEnvelope s c x
      * (phaseCosCoeff (prolateOsc s c R) (prolateOscD s c R DR) (prolatePhase s c) x
          * Real.cos (prolatePhase s c x)
        + phaseSinCoeff (prolateOsc s c R) (prolateOscD s c R DR) (prolatePhase s c) x
          * Real.sin (prolatePhase s c x)) := by
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hsd : (0 : ℝ) < Real.sqrt (x ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr hd
  have hh : 0 < lgSpeedAmp s c x := lgSpeedAmp_pos hs1 hc hx
  have hrep := phase_eq_coeff (prolateOsc s c R) (prolateOscD s c R DR) (prolatePhase s c) x
  have hw : prolateOsc s c R x = lgSpeedAmp s c x * (Real.sqrt (x ^ (2 : ℕ) - 1) * R x) := by
    rw [prolateOsc, prolateNormalFormSol, nfWeight]
  rw [prolateEnvelope, ← hrep, hw]
  field_simp

theorem abs_lgSpeedAmpDeriv_le {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hx : 2 ≤ x) : |lgSpeedAmpDeriv s c x| ≤ Real.sqrt c / x ^ (3 : ℕ) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hss : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  have hh : Real.sqrt c ≤ lgSpeedAmp s c x := sqrt_c_le_lgSpeedAmp hs1 hc hx1
  have hh0 : 0 < lgSpeedAmp s c x := lgSpeedAmp_pos hs1 hc hx1
  have hdd := abs_xiSpeedDeriv_le_two_div hs0 hs1 hx
  have hnum : |prolatePhaseAccel s c x| ≤ 2 * c / x ^ (3 : ℕ) := by
    rw [prolatePhaseAccel, abs_mul, abs_of_pos hc]
    have := mul_le_mul_of_nonneg_left hdd hc.le
    calc c * |xiSpeedDeriv s x| ≤ c * (2 / x ^ (3 : ℕ)) := this
      _ = 2 * c / x ^ (3 : ℕ) := by ring
  rw [lgSpeedAmpDeriv, abs_div,
    abs_of_pos (by rw [← lgSpeedAmp]; positivity : (0 : ℝ) < 2 * Real.sqrt (prolatePhaseSpeed s c x)),
    div_le_div_iff₀ (by rw [← lgSpeedAmp]; positivity) (by positivity)]
  have hamp : (2 : ℝ) * Real.sqrt c ≤ 2 * Real.sqrt (prolatePhaseSpeed s c x) := by
    have : lgSpeedAmp s c x = Real.sqrt (prolatePhaseSpeed s c x) := rfl
    linarith [hh, this ▸ hh]
  calc |prolatePhaseAccel s c x| * x ^ (3 : ℕ) ≤ 2 * c / x ^ (3 : ℕ) * x ^ (3 : ℕ) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = 2 * c := by field_simp
    _ = Real.sqrt c * (2 * Real.sqrt c) := by
        rw [show Real.sqrt c * (2 * Real.sqrt c) = 2 * (Real.sqrt c * Real.sqrt c) by ring, hss]
    _ ≤ Real.sqrt c * (2 * Real.sqrt (prolatePhaseSpeed s c x)) :=
        mul_le_mul_of_nonneg_left hamp hsc.le

theorem prolateEnvelope_le {s c x : ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hx : 2 ≤ x) :
    prolateEnvelope s c x ≤ 2 / (Real.sqrt c * x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hh : Real.sqrt c ≤ lgSpeedAmp s c x := sqrt_c_le_lgSpeedAmp hs1 hc hx1
  have hh0 : 0 < lgSpeedAmp s c x := lgSpeedAmp_pos hs1 hc hx1
  have hsd : (0 : ℝ) < Real.sqrt (x ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr hd
  have hlow : x / 2 ≤ Real.sqrt (x ^ (2 : ℕ) - 1) := by
    have h1 : (x / 2) ^ (2 : ℕ) ≤ x ^ (2 : ℕ) - 1 := by nlinarith
    have h2 : Real.sqrt ((x / 2) ^ (2 : ℕ)) ≤ Real.sqrt (x ^ (2 : ℕ) - 1) := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity)] at h2
  rw [prolateEnvelope, div_le_div_iff₀ (by positivity) (by positivity)]
  have hprod : Real.sqrt c * (x / 2) ≤ lgSpeedAmp s c x * Real.sqrt (x ^ (2 : ℕ) - 1) :=
    mul_le_mul hh hlow (by positivity) hh0.le
  linarith [hprod]

theorem abs_prolateEnvelopeDeriv_le {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hx : 2 ≤ x) : |prolateEnvelopeDeriv s c x| ≤ 16 / (Real.sqrt c * x ^ (2 : ℕ)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hss : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  have hh : Real.sqrt c ≤ lgSpeedAmp s c x := sqrt_c_le_lgSpeedAmp hs1 hc hx1
  have hh2 : lgSpeedAmp s c x ≤ Real.sqrt (2 * c) := lgSpeedAmp_le_sqrt_two_c hs0 hc hx
  have hh0 : 0 < lgSpeedAmp s c x := lgSpeedAmp_pos hs1 hc hx1
  have hsd : (0 : ℝ) < Real.sqrt (x ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr hd
  have hsdle : Real.sqrt (x ^ (2 : ℕ) - 1) ≤ x := by
    have h1 : Real.sqrt (x ^ (2 : ℕ) - 1) ≤ Real.sqrt (x ^ (2 : ℕ)) := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_sq hx0.le] at h1
  have hlow : x / 2 ≤ Real.sqrt (x ^ (2 : ℕ) - 1) := by
    have h1 : (x / 2) ^ (2 : ℕ) ≤ x ^ (2 : ℕ) - 1 := by nlinarith
    have h2 : Real.sqrt ((x / 2) ^ (2 : ℕ)) ≤ Real.sqrt (x ^ (2 : ℕ) - 1) := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity)] at h2
  have hdd := abs_lgSpeedAmpDeriv_le hs0 hs1 hc hx
  have h2c : Real.sqrt (2 * c) ≤ 3 / 2 * Real.sqrt c := by
    have h1 : Real.sqrt (2 * c) ≤ Real.sqrt ((3 / 2) ^ (2 : ℕ) * c) :=
      Real.sqrt_le_sqrt (by nlinarith [hc.le])
    have h2 : Real.sqrt ((3 / 2 : ℝ) ^ (2 : ℕ) * c) = 3 / 2 * Real.sqrt c := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    linarith [h1, h2]
  rw [prolateEnvelopeDeriv, abs_div, abs_neg,
    abs_of_pos (by positivity : (0 : ℝ) < (lgSpeedAmp s c x * Real.sqrt (x ^ (2 : ℕ) - 1)) ^ (2 : ℕ)),
    div_le_div_iff₀ (by positivity) (by positivity)]
  -- numerator
  have hnum : |lgSpeedAmpDeriv s c x * Real.sqrt (x ^ (2 : ℕ) - 1)
      + lgSpeedAmp s c x * (x / Real.sqrt (x ^ (2 : ℕ) - 1))| ≤ 4 * Real.sqrt c := by
    refine le_trans (abs_add_le _ _) ?_
    have h1 : |lgSpeedAmpDeriv s c x * Real.sqrt (x ^ (2 : ℕ) - 1)| ≤ Real.sqrt c := by
      rw [abs_mul, abs_of_pos hsd]
      calc |lgSpeedAmpDeriv s c x| * Real.sqrt (x ^ (2 : ℕ) - 1)
          ≤ Real.sqrt c / x ^ (3 : ℕ) * x := mul_le_mul hdd hsdle hsd.le (by positivity)
        _ ≤ Real.sqrt c := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith [mul_nonneg hsc.le (mul_nonneg hx0.le hd.le)]
    have h2 : |lgSpeedAmp s c x * (x / Real.sqrt (x ^ (2 : ℕ) - 1))| ≤ 3 * Real.sqrt c := by
      rw [abs_mul, abs_of_pos hh0, abs_of_pos (by positivity)]
      have hratio : x / Real.sqrt (x ^ (2 : ℕ) - 1) ≤ 2 := by
        rw [div_le_iff₀ hsd]
        linarith [hlow]
      calc lgSpeedAmp s c x * (x / Real.sqrt (x ^ (2 : ℕ) - 1))
          ≤ 3 / 2 * Real.sqrt c * 2 := mul_le_mul (le_trans hh2 h2c) hratio (by positivity)
            (by positivity)
        _ ≤ 3 * Real.sqrt c := by nlinarith [hsc.le]
    linarith
  have hden : Real.sqrt c * Real.sqrt c * (x / 2) ^ (2 : ℕ)
      ≤ (lgSpeedAmp s c x * Real.sqrt (x ^ (2 : ℕ) - 1)) ^ (2 : ℕ) := by
    have hprod : Real.sqrt c * (x / 2) ≤ lgSpeedAmp s c x * Real.sqrt (x ^ (2 : ℕ) - 1) :=
      mul_le_mul hh hlow (by positivity) hh0.le
    have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ Real.sqrt c * (x / 2)) hprod
    calc Real.sqrt c * Real.sqrt c * (x / 2) ^ (2 : ℕ)
        = Real.sqrt c * (x / 2) * (Real.sqrt c * (x / 2)) := by ring
      _ ≤ lgSpeedAmp s c x * Real.sqrt (x ^ (2 : ℕ) - 1)
          * (lgSpeedAmp s c x * Real.sqrt (x ^ (2 : ℕ) - 1)) := hsq
      _ = (lgSpeedAmp s c x * Real.sqrt (x ^ (2 : ℕ) - 1)) ^ (2 : ℕ) := by ring
  calc |lgSpeedAmpDeriv s c x * Real.sqrt (x ^ (2 : ℕ) - 1)
        + lgSpeedAmp s c x * (x / Real.sqrt (x ^ (2 : ℕ) - 1))| * (Real.sqrt c * x ^ (2 : ℕ))
      ≤ 4 * Real.sqrt c * (Real.sqrt c * x ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = 4 * c * x ^ (2 : ℕ) := by
        rw [show 4 * Real.sqrt c * (Real.sqrt c * x ^ (2 : ℕ))
          = 4 * (Real.sqrt c * Real.sqrt c) * x ^ (2 : ℕ) by ring, hss]
    _ ≤ 16 * (lgSpeedAmp s c x * Real.sqrt (x ^ (2 : ℕ) - 1)) ^ (2 : ℕ) := by
        have hq : Real.sqrt c * Real.sqrt c * (x / 2) ^ (2 : ℕ) = c * x ^ (2 : ℕ) / 4 := by
          rw [show Real.sqrt c * Real.sqrt c * (x / 2) ^ (2 : ℕ)
            = (Real.sqrt c * Real.sqrt c) * (x / 2) ^ (2 : ℕ) by ring, hss]
          ring
        rw [hq] at hden
        linarith [hden]


/-- The dilated channel amplitude of the exact mode, for an arbitrary branch coefficient. -/
def exactAmplitude (s c k : ℝ) (A : ℝ → ℝ) (x : ℝ) : ℝ :=
  prolateEnvelope s c (k * x) * A (k * x)

/-- Its derivative. -/
def exactAmplitudeDeriv (s c k : ℝ) (A A' : ℝ → ℝ) (x : ℝ) : ℝ :=
  k * prolateEnvelopeDeriv s c (k * x) * A (k * x)
    + prolateEnvelope s c (k * x) * (k * A' (k * x))

/-- The amplitude in the exterior estimate's normalization. -/
def exactAmp (s c k : ℝ) (A : ℝ → ℝ) (x : ℝ) : ℝ := Real.sqrt x * exactAmplitude s c k A x

/-- Its derivative. -/
def exactAmpDeriv (s c k : ℝ) (A A' : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 / (2 * Real.sqrt x) * exactAmplitude s c k A x
    + Real.sqrt x * exactAmplitudeDeriv s c k A A' x

theorem hasDerivAt_exactAmplitude {s c k x : ℝ} {A A' : ℝ → ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hkx : 1 < k * x) (hA : ∀ y : ℝ, 1 < y → HasDerivAt A (A' y) y) :
    HasDerivAt (exactAmplitude s c k A) (exactAmplitudeDeriv s c k A A' x) x := by
  have hlin : HasDerivAt (fun t : ℝ => k * t) k x := by
    simpa using (hasDerivAt_id x).const_mul k
  have henv : HasDerivAt (fun t : ℝ => prolateEnvelope s c (k * t))
      (k * prolateEnvelopeDeriv s c (k * x)) x := by
    have h := (hasDerivAt_prolateEnvelope hs1 hc hkx).comp x hlin
    have hv : prolateEnvelopeDeriv s c (k * x) * k
        = k * prolateEnvelopeDeriv s c (k * x) := by ring
    rwa [hv] at h
  have hcoeff : HasDerivAt (fun t : ℝ => A (k * t)) (k * A' (k * x)) x := by
    have h := (hA _ hkx).comp x hlin
    have hv : A' (k * x) * k = k * A' (k * x) := by ring
    rwa [hv] at h
  exact henv.mul hcoeff

theorem hasDerivAt_exactAmp {s c k x : ℝ} {A A' : ℝ → ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hx0 : 0 < x) (hkx : 1 < k * x) (hA : ∀ y : ℝ, 1 < y → HasDerivAt A (A' y) y) :
    HasDerivAt (exactAmp s c k A) (exactAmpDeriv s c k A A' x) x := by
  have hsq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x :=
    Real.hasDerivAt_sqrt (ne_of_gt hx0)
  exact hsq.mul (hasDerivAt_exactAmplitude hs1 hc hkx hA)

/-- **The exact channel amplitude carries `1/(√c k)`.** -/
theorem abs_exactAmp_le {s c k x M : ℝ} {A : ℝ → ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hk : 1 ≤ k) (hx : 1 ≤ x) (hkx2 : 2 ≤ k * x) (hM : 0 ≤ M) (hAb : |A (k * x)| ≤ M) :
    |exactAmp s c k A x| ≤ 300 * M / (Real.sqrt c * k) / Real.sqrt x := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hx0 : (0 : ℝ) < x := by linarith
  have hkx : (1 : ℝ) < k * x := by linarith
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have henv := prolateEnvelope_le (s := s) (c := c) hs1 hc hkx2
  have henv0 : (0 : ℝ) < prolateEnvelope s c (k * x) := by
    rw [prolateEnvelope]
    have h1 : 0 < lgSpeedAmp s c (k * x) := lgSpeedAmp_pos hs1 hc hkx
    have h2 : (0 : ℝ) < (k * x) ^ (2 : ℕ) - 1 := by nlinarith
    have h3 : (0 : ℝ) < Real.sqrt ((k * x) ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr h2
    positivity
  rw [exactAmp, exactAmplitude, abs_mul, abs_of_pos hsx, abs_mul, abs_of_pos henv0]
  have hstep : Real.sqrt x * (prolateEnvelope s c (k * x) * |A (k * x)|)
      ≤ Real.sqrt x * (2 / (Real.sqrt c * (k * x)) * M) :=
    mul_le_mul_of_nonneg_left (mul_le_mul henv hAb (abs_nonneg _) (by positivity)) hsx.le
  refine le_trans hstep ?_
  have hval : Real.sqrt x * (2 / (Real.sqrt c * (k * x)) * M)
      = 2 * M / (Real.sqrt c * k) / Real.sqrt x := by
    field_simp
    linear_combination M * hss
  rw [hval]
  have hnn : (0 : ℝ) ≤ Real.sqrt c * k := by positivity
  rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hM, hnn, hsx.le, mul_nonneg (mul_nonneg hM hnn) hsx.le]


/-- **The exact channel amplitude's derivative carries the same constant.** -/
theorem abs_exactAmpDeriv_le {s c k x M : ℝ} {A A' : ℝ → ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 1 ≤ c) (hk : 1 ≤ k) (hx : 1 ≤ x) (hkx2 : 2 ≤ k * x) (hM : 0 ≤ M)
    (hAb : |A (k * x)| ≤ M) (hA'b : |A' (k * x)| ≤ 280 * M / (c * (k * x) ^ (2 : ℕ))) :
    |exactAmpDeriv s c k A A' x| ≤ 300 * M / (Real.sqrt c * k) / (x * Real.sqrt x) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hx0 : (0 : ℝ) < x := by linarith
  have hkx : (1 : ℝ) < k * x := by linarith
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have henv := prolateEnvelope_le (s := s) (c := c) hs1 hc0 hkx2
  have henvd := abs_prolateEnvelopeDeriv_le (s := s) (c := c) hs0 hs1 hc0 hkx2
  have henv0 : (0 : ℝ) < prolateEnvelope s c (k * x) := by
    rw [prolateEnvelope]
    have h1 : 0 < lgSpeedAmp s c (k * x) := lgSpeedAmp_pos hs1 hc0 hkx
    have h2 : (0 : ℝ) < (k * x) ^ (2 : ℕ) - 1 := by nlinarith
    have h3 : (0 : ℝ) < Real.sqrt ((k * x) ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr h2
    positivity
  set T : ℝ := M / (Real.sqrt c * k) / (x * Real.sqrt x) with hTdef
  have hT0 : (0 : ℝ) ≤ T := by rw [hTdef]; positivity
  rw [exactAmpDeriv, exactAmplitude, exactAmplitudeDeriv]
  refine le_trans (abs_add_le _ _) ?_
  -- the square-root factor
  have hT1 : |1 / (2 * Real.sqrt x) * (prolateEnvelope s c (k * x) * A (k * x))| ≤ T := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.sqrt x)), abs_mul,
      abs_of_pos henv0]
    have hstep : 1 / (2 * Real.sqrt x) * (prolateEnvelope s c (k * x) * |A (k * x)|)
        ≤ 1 / (2 * Real.sqrt x) * (2 / (Real.sqrt c * (k * x)) * M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul henv hAb (abs_nonneg _) (by positivity))
        (by positivity)
    refine le_trans hstep (le_of_eq ?_)
    rw [hTdef]
    field_simp
  -- the envelope-derivative term
  have hT2 : |k * prolateEnvelopeDeriv s c (k * x) * A (k * x)| * Real.sqrt x ≤ 16 * T := by
    rw [abs_mul, abs_mul, abs_of_pos hk0]
    have hstep : k * |prolateEnvelopeDeriv s c (k * x)| * |A (k * x)| * Real.sqrt x
        ≤ k * (16 / (Real.sqrt c * (k * x) ^ (2 : ℕ))) * M * Real.sqrt x := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul
        (mul_le_mul_of_nonneg_left henvd hk0.le) hAb (abs_nonneg _) (by positivity)) hsx.le
    refine le_trans hstep (le_of_eq ?_)
    rw [hTdef]
    field_simp
    linear_combination M * hss
  -- the coefficient-drift term
  have hT3 : prolateEnvelope s c (k * x) * |k * A' (k * x)| * Real.sqrt x ≤ 280 * T := by
    rw [abs_mul, abs_of_pos hk0]
    have hstep : prolateEnvelope s c (k * x) * (k * |A' (k * x)|) * Real.sqrt x
        ≤ 2 / (Real.sqrt c * (k * x)) * (k * (280 * M / (c * (k * x) ^ (2 : ℕ)))) * Real.sqrt x := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul henv
        (mul_le_mul_of_nonneg_left hA'b hk0.le) (by positivity) (by positivity)) hsx.le
    refine le_trans hstep ?_
    have hval : 2 / (Real.sqrt c * (k * x)) * (k * (280 * M / (c * (k * x) ^ (2 : ℕ))))
        * Real.sqrt x = 560 * T / (c * k * x) := by
      rw [hTdef]
      field_simp
      linear_combination (560 * M) * hss
    rw [hval]
    have hckx : (2 : ℝ) ≤ c * k * x := by nlinarith [hc, hkx2, hk0, hx0]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hT0, hckx]
  -- combine
  have habs2 : |Real.sqrt x * (k * prolateEnvelopeDeriv s c (k * x) * A (k * x)
      + prolateEnvelope s c (k * x) * (k * A' (k * x)))|
      ≤ 16 * T + 280 * T := by
    rw [abs_mul, abs_of_pos hsx]
    have hinner : |k * prolateEnvelopeDeriv s c (k * x) * A (k * x)
        + prolateEnvelope s c (k * x) * (k * A' (k * x))|
        ≤ 16 * T / Real.sqrt x + 280 * T / Real.sqrt x := by
      refine le_trans (abs_add_le _ _) ?_
      have h2 : |k * prolateEnvelopeDeriv s c (k * x) * A (k * x)| ≤ 16 * T / Real.sqrt x := by
        rw [le_div_iff₀ hsx]
        exact hT2
      have h3 : |prolateEnvelope s c (k * x) * (k * A' (k * x))| ≤ 280 * T / Real.sqrt x := by
        rw [le_div_iff₀ hsx, abs_mul, abs_of_pos henv0]
        exact hT3
      linarith
    calc Real.sqrt x * |k * prolateEnvelopeDeriv s c (k * x) * A (k * x)
          + prolateEnvelope s c (k * x) * (k * A' (k * x))|
        ≤ Real.sqrt x * (16 * T / Real.sqrt x + 280 * T / Real.sqrt x) :=
          mul_le_mul_of_nonneg_left hinner hsx.le
      _ = 16 * T + 280 * T := by field_simp
  have hfin : T + (16 * T + 280 * T) ≤ 300 * M / (Real.sqrt c * k) / (x * Real.sqrt x) := by
    rw [hTdef]
    have hval : 300 * M / (Real.sqrt c * k) / (x * Real.sqrt x)
        = 300 * (M / (Real.sqrt c * k) / (x * Real.sqrt x)) := by ring
    rw [hval]
    have := hT0
    rw [hTdef] at this
    linarith
  linarith [hT1, habs2, hfin]


/-- **The abstract drift bound, in the form the channel amplitude consumes.**  The phase speed is
at most `2c` and the phase at least `c y/2`, so `φ' κ/φ² ≤ 4κ/(c y²)`. -/
theorem prolate_drift_le {s c y M : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hy : 2 ≤ y) (hM : 0 ≤ M) :
    prolatePhaseSpeed s c y * (35 / prolatePhase s c y ^ (2 : ℕ)) * M ≤ 280 * M / (c * y ^ (2 : ℕ)) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hy1 : (1 : ℝ) < y := by linarith
  have hsp2 : xiSpeed s y ≤ 2 := xiSpeed_le_two hs0 hy
  have hphase : c * y / 2 ≤ prolatePhase s c y := by
    have h := half_mul_le_xiEndpointPhase hs0 hs1 hy
    rw [prolatePhase]
    have := mul_le_mul_of_nonneg_left h hc.le
    linarith [this]
  have hp0 : (0 : ℝ) < c * y / 2 := by positivity
  have hspd : prolatePhaseSpeed s c y ≤ 2 * c := by
    rw [prolatePhaseSpeed]
    nlinarith [hsp2, hc.le]
  have hspd0 : (0 : ℝ) ≤ prolatePhaseSpeed s c y := (prolatePhaseSpeed_pos hs1 hc hy1).le
  have hsq : (c * y / 2) ^ (2 : ℕ) ≤ prolatePhase s c y ^ (2 : ℕ) := by
    nlinarith [hphase, hp0.le]
  have hfrac : 35 / prolatePhase s c y ^ (2 : ℕ) ≤ 35 / (c * y / 2) ^ (2 : ℕ) := by
    refine div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
  calc prolatePhaseSpeed s c y * (35 / prolatePhase s c y ^ (2 : ℕ)) * M
      ≤ 2 * c * (35 / (c * y / 2) ^ (2 : ℕ)) * M := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul hspd hfrac (by positivity)
          (by positivity)) hM
    _ = 280 * M / (c * y ^ (2 : ℕ)) := by
        field_simp
        ring


/-- The cosine branch coefficient of the exact mode. -/
def exactCosCoeff (s c : ℝ) (R DR : ℝ → ℝ) : ℝ → ℝ :=
  phaseCosCoeff (prolateOsc s c R) (prolateOscD s c R DR) (prolatePhase s c)

/-- The sine branch coefficient. -/
def exactSinCoeff (s c : ℝ) (R DR : ℝ → ℝ) : ℝ → ℝ :=
  phaseSinCoeff (prolateOsc s c R) (prolateOscD s c R DR) (prolatePhase s c)

/-- The cosine coefficient's derivative. -/
def exactCosCoeffDeriv (s c : ℝ) (R : ℝ → ℝ) (y : ℝ) : ℝ :=
  prolatePhaseSpeed s c y * prolateOscPotential s c y * prolateOsc s c R y
    * Real.sin (prolatePhase s c y)

/-- The sine coefficient's derivative. -/
def exactSinCoeffDeriv (s c : ℝ) (R : ℝ → ℝ) (y : ℝ) : ℝ :=
  -(prolatePhaseSpeed s c y * prolateOscPotential s c y * prolateOsc s c R y
    * Real.cos (prolatePhase s c y))

/-- The energy budget of the exact mode measured at a base point. -/
def exactEnergyBudget (s c : ℝ) (R DR : ℝ → ℝ) (a : ℝ) : ℝ :=
  Real.sqrt (phaseEnergy (prolateOsc s c R) (prolateOscD s c R DR) a
    * Real.exp (35 / prolatePhase s c a))

theorem hasDerivAt_exactCosCoeff {s c y : ℝ} {R DR DDR : ℝ → ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hy : 1 < y)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    HasDerivAt (exactCosCoeff s c R DR) (exactCosCoeffDeriv s c R y) y :=
  hasDerivAt_phaseCosCoeff (DDw := prolateOscDD s c R DR DDR) (q := prolateOscPotential s c)
    (hasDerivAt_prolatePhase hs0 hy)
    (hasDerivAt_prolateOsc hs1 hc hy (hR y))
    (hasDerivAt_prolateOscD hs1 hc hy (hR y) (hDR y))
    (prolateOsc_ode hs1 hc hy (hode y))

theorem hasDerivAt_exactSinCoeff {s c y : ℝ} {R DR DDR : ℝ → ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hy : 1 < y)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    HasDerivAt (exactSinCoeff s c R DR) (exactSinCoeffDeriv s c R y) y :=
  hasDerivAt_phaseSinCoeff (DDw := prolateOscDD s c R DR DDR) (q := prolateOscPotential s c)
    (hasDerivAt_prolatePhase hs0 hy)
    (hasDerivAt_prolateOsc hs1 hc hy (hR y))
    (hasDerivAt_prolateOscD hs1 hc hy (hR y) (hDR y))
    (prolateOsc_ode hs1 hc hy (hode y))

/-- **The exact mode's coefficients are bounded by the energy budget.** -/
theorem abs_exactCoeff_le {s c a y : ℝ} {R DR DDR : ℝ → ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (ha : 2 ≤ a) (hay : a ≤ y)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    |exactCosCoeff s c R DR y| ≤ exactEnergyBudget s c R DR a
      ∧ |exactSinCoeff s c R DR y| ≤ exactEnergyBudget s c R DR a :=
  abs_prolateOscCoeff_le (DDR := DDR) hs0 hs1 hc ha hay hR hDR hode

/-- **The exact mode's coefficient drift.** -/
theorem abs_exactCoeffDeriv_le {s c a y : ℝ} {R DR DDR : ℝ → ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (ha : 2 ≤ a) (hay : a ≤ y)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    |exactCosCoeffDeriv s c R y| ≤ 280 * exactEnergyBudget s c R DR a / (c * y ^ (2 : ℕ))
      ∧ |exactSinCoeffDeriv s c R y| ≤ 280 * exactEnergyBudget s c R DR a / (c * y ^ (2 : ℕ)) := by
  have hy2 : (2 : ℝ) ≤ y := le_trans ha hay
  have hM : (0 : ℝ) ≤ exactEnergyBudget s c R DR a := Real.sqrt_nonneg _
  obtain ⟨hφd, hφpos, hDφ, hw, hDw, hodew, hq⟩ :=
    prolate_isPhaseOscillator (a := a) hs0 hs1 hc ha hR hDR hode
  obtain ⟨h1, h2⟩ := abs_deriv_phaseCoeff_le_base (w := prolateOsc s c R)
    (Dw := prolateOscD s c R DR) (DDw := prolateOscDD s c R DR DDR)
    (q := prolateOscPotential s c) (φ := prolatePhase s c) (Dφ := prolatePhaseSpeed s c)
    (κ := 35) hay (by norm_num) hφd hφpos hDφ hw hDw hodew hq
  have hbridge := prolate_drift_le (s := s) (c := c) (y := y)
    (M := exactEnergyBudget s c R DR a) hs0 hs1 hc hy2 hM
  exact ⟨le_trans h1 hbridge, le_trans h2 hbridge⟩

/-- **The dilated exact mode in two real branches.** -/
theorem sqrt_mul_radialProlate_dilate_eq {s c k x : ℝ} {R DR : ℝ → ℝ} (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hkx : 1 < k * x) :
    Real.sqrt x * R (k * x)
      = exactAmp s c k (exactCosCoeff s c R DR) x * Real.cos (prolatePhase s c (k * x))
        + exactAmp s c k (exactSinCoeff s c R DR) x * Real.sin (prolatePhase s c (k * x)) := by
  rw [radialProlate_eq_branches (R := R) (DR := DR) hs1 hc hkx, exactAmp, exactAmp,
    exactAmplitude, exactAmplitude, exactCosCoeff, exactSinCoeff]
  ring


theorem continuousOn_xiSpeedSecondDeriv {s : ℝ} (hs1 : s ≤ 1 / 2) :
    ContinuousOn (xiSpeedSecondDeriv s) (Set.Ioi (1 : ℝ)) := by
  have hsp : ContinuousOn (xiSpeed s) (Set.Ioi (1 : ℝ)) := continuousOn_xiSpeed s
  have hspd : ContinuousOn (xiSpeedDeriv s) (Set.Ioi (1 : ℝ)) :=
    continuousOn_xiSpeedDeriv (by linarith)
  have hden : ContinuousOn (fun t : ℝ => ((t ^ (2 : ℕ) - 1) ^ (2 : ℕ) * xiSpeed s t) ^ (2 : ℕ))
      (Set.Ioi (1 : ℝ)) := (((continuousOn_id.pow 2).sub continuousOn_const).pow 2).mul hsp
      |>.pow 2
  rw [show xiSpeedSecondDeriv s = fun t : ℝ =>
      ((s - 1) * ((t ^ (2 : ℕ) - 1) ^ (2 : ℕ) * xiSpeed s t)
        - t * (s - 1) * (4 * t * (t ^ (2 : ℕ) - 1) * xiSpeed s t
          + (t ^ (2 : ℕ) - 1) ^ (2 : ℕ) * xiSpeedDeriv s t))
      / ((t ^ (2 : ℕ) - 1) ^ (2 : ℕ) * xiSpeed s t) ^ (2 : ℕ) from rfl]
  refine ContinuousOn.div ?_ hden ?_
  · refine (continuousOn_const.mul (((continuousOn_id.pow 2).sub continuousOn_const).pow 2
      |>.mul hsp)).sub ?_
    refine (continuousOn_id.mul continuousOn_const).mul ?_
    exact ((continuousOn_const.mul continuousOn_id).mul
      ((continuousOn_id.pow 2).sub continuousOn_const) |>.mul hsp).add
      ((((continuousOn_id.pow 2).sub continuousOn_const).pow 2).mul hspd)
  · intro t ht
    have ht1 : (1 : ℝ) < t := ht
    have hd : (0 : ℝ) < t ^ (2 : ℕ) - 1 := by nlinarith
    have hs : 0 < xiSpeed s t := xiSpeed_pos hs1 ht1
    positivity

theorem continuousOn_prolateOscPotential {s c : ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c) :
    ContinuousOn (prolateOscPotential s c) (Set.Ioi (1 : ℝ)) := by
  have hsp : ContinuousOn (xiSpeed s) (Set.Ioi (1 : ℝ)) := continuousOn_xiSpeed s
  have hspd : ContinuousOn (xiSpeedDeriv s) (Set.Ioi (1 : ℝ)) :=
    continuousOn_xiSpeedDeriv (by linarith)
  have hspdd : ContinuousOn (xiSpeedSecondDeriv s) (Set.Ioi (1 : ℝ)) :=
    continuousOn_xiSpeedSecondDeriv hs1
  have hcongr : Set.EqOn (prolateOscPotential s c)
      (fun x : ℝ => 1 / (c ^ (2 : ℕ) * xiSpeed s x ^ (2 : ℕ) * (x ^ (2 : ℕ) - 1) ^ (2 : ℕ))
        + (3 * xiSpeedDeriv s x ^ (2 : ℕ) - 2 * xiSpeedSecondDeriv s x * xiSpeed s x)
          / (4 * c ^ (2 : ℕ) * xiSpeed s x ^ (4 : ℕ))) (Set.Ioi (1 : ℝ)) := by
    intro x hx
    exact prolateOscPotential_eq hs1 hc hx
  refine ContinuousOn.congr ?_ hcongr
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_const.div ((continuousOn_const.mul (hsp.pow 2)).mul
      (((continuousOn_id.pow 2).sub continuousOn_const).pow 2)) ?_
    intro x hx
    have hx1 : (1 : ℝ) < x := hx
    have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
    have hs : 0 < xiSpeed s x := xiSpeed_pos hs1 hx1
    positivity
  · refine ContinuousOn.div ((continuousOn_const.mul (hspd.pow 2)).sub
      ((continuousOn_const.mul hspdd).mul hsp)) (continuousOn_const.mul (hsp.pow 4)) ?_
    intro x hx
    have hx1 : (1 : ℝ) < x := hx
    have hs : 0 < xiSpeed s x := xiSpeed_pos hs1 hx1
    positivity


theorem continuousOn_lgSpeedAmp {s c : ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c) :
    ContinuousOn (lgSpeedAmp s c) (Set.Ioi (1 : ℝ)) :=
  fun _ hy => ((hasDerivAt_lgSpeedAmp hs1 hc hy).continuousAt).continuousWithinAt

theorem continuousOn_lgSpeedAmpDeriv {s c : ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c) :
    ContinuousOn (lgSpeedAmpDeriv s c) (Set.Ioi (1 : ℝ)) :=
  fun _ hy => ((hasDerivAt_lgSpeedAmpDeriv hs1 hc hy).continuousAt).continuousWithinAt

theorem continuousOn_prolateEnvelope {s c : ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c) :
    ContinuousOn (prolateEnvelope s c) (Set.Ioi (1 : ℝ)) :=
  fun _ hy => ((hasDerivAt_prolateEnvelope hs1 hc hy).continuousAt).continuousWithinAt

theorem continuousOn_prolateEnvelopeDeriv {s c : ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c) :
    ContinuousOn (prolateEnvelopeDeriv s c) (Set.Ioi (1 : ℝ)) := by
  have hsd : ContinuousOn (fun t : ℝ => Real.sqrt (t ^ (2 : ℕ) - 1)) (Set.Ioi (1 : ℝ)) :=
    Real.continuous_sqrt.comp_continuousOn ((continuousOn_id.pow 2).sub continuousOn_const)
  have hsdne : ∀ t ∈ Set.Ioi (1 : ℝ), Real.sqrt (t ^ (2 : ℕ) - 1) ≠ 0 := by
    intro t ht
    have ht1 : (1 : ℝ) < t := ht
    have hd : (0 : ℝ) < t ^ (2 : ℕ) - 1 := by nlinarith
    exact ne_of_gt (Real.sqrt_pos.mpr hd)
  have hden : ContinuousOn (fun t : ℝ => (lgSpeedAmp s c t * Real.sqrt (t ^ (2 : ℕ) - 1)) ^ (2 : ℕ))
      (Set.Ioi (1 : ℝ)) := (((continuousOn_lgSpeedAmp hs1 hc).mul hsd).pow 2)
  rw [show prolateEnvelopeDeriv s c = fun t : ℝ =>
      -(lgSpeedAmpDeriv s c t * Real.sqrt (t ^ (2 : ℕ) - 1)
        + lgSpeedAmp s c t * (t / Real.sqrt (t ^ (2 : ℕ) - 1)))
      / (lgSpeedAmp s c t * Real.sqrt (t ^ (2 : ℕ) - 1)) ^ (2 : ℕ) from rfl]
  refine ContinuousOn.div (((continuousOn_lgSpeedAmpDeriv hs1 hc).mul hsd).add
    ((continuousOn_lgSpeedAmp hs1 hc).mul (continuousOn_id.div hsd hsdne))).neg hden ?_
  intro t ht
  have ht1 : (1 : ℝ) < t := ht
  have h1 : 0 < lgSpeedAmp s c t := lgSpeedAmp_pos hs1 hc ht1
  have hd : (0 : ℝ) < t ^ (2 : ℕ) - 1 := by nlinarith
  have h2 : (0 : ℝ) < Real.sqrt (t ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr hd
  positivity

theorem continuousOn_exactCosCoeffDeriv {s c : ℝ} {R DR : ℝ → ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) :
    ContinuousOn (exactCosCoeffDeriv s c R) (Set.Ioi (1 : ℝ)) := by
  have hRc : Continuous R := continuous_iff_continuousAt.mpr fun t => (hR t).continuousAt
  have hsd : ContinuousOn (fun t : ℝ => Real.sqrt (t ^ (2 : ℕ) - 1)) (Set.Ioi (1 : ℝ)) :=
    Real.continuous_sqrt.comp_continuousOn ((continuousOn_id.pow 2).sub continuousOn_const)
  have hosc : ContinuousOn (prolateOsc s c R) (Set.Ioi (1 : ℝ)) := by
    rw [show prolateOsc s c R = fun t : ℝ =>
        lgSpeedAmp s c t * (Real.sqrt (t ^ (2 : ℕ) - 1) * R t) from rfl]
    exact (continuousOn_lgSpeedAmp hs1 hc).mul (hsd.mul hRc.continuousOn)
  have hspd : ContinuousOn (prolatePhaseSpeed s c) (Set.Ioi (1 : ℝ)) :=
    continuousOn_const.mul (continuousOn_xiSpeed s)
  have hph : ContinuousOn (prolatePhase s c) (Set.Ioi (1 : ℝ)) :=
    continuousOn_const.mul (continuousOn_xiEndpointPhase hs0)
  rw [show exactCosCoeffDeriv s c R = fun t : ℝ =>
      prolatePhaseSpeed s c t * prolateOscPotential s c t * prolateOsc s c R t
        * Real.sin (prolatePhase s c t) from rfl]
  exact ((hspd.mul (continuousOn_prolateOscPotential hs1 hc)).mul hosc).mul
    (Real.continuous_sin.comp_continuousOn hph)

theorem continuousOn_exactSinCoeffDeriv {s c : ℝ} {R DR : ℝ → ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) :
    ContinuousOn (exactSinCoeffDeriv s c R) (Set.Ioi (1 : ℝ)) := by
  have hRc : Continuous R := continuous_iff_continuousAt.mpr fun t => (hR t).continuousAt
  have hsd : ContinuousOn (fun t : ℝ => Real.sqrt (t ^ (2 : ℕ) - 1)) (Set.Ioi (1 : ℝ)) :=
    Real.continuous_sqrt.comp_continuousOn ((continuousOn_id.pow 2).sub continuousOn_const)
  have hosc : ContinuousOn (prolateOsc s c R) (Set.Ioi (1 : ℝ)) := by
    rw [show prolateOsc s c R = fun t : ℝ =>
        lgSpeedAmp s c t * (Real.sqrt (t ^ (2 : ℕ) - 1) * R t) from rfl]
    exact (continuousOn_lgSpeedAmp hs1 hc).mul (hsd.mul hRc.continuousOn)
  have hspd : ContinuousOn (prolatePhaseSpeed s c) (Set.Ioi (1 : ℝ)) :=
    continuousOn_const.mul (continuousOn_xiSpeed s)
  have hph : ContinuousOn (prolatePhase s c) (Set.Ioi (1 : ℝ)) :=
    continuousOn_const.mul (continuousOn_xiEndpointPhase hs0)
  rw [show exactSinCoeffDeriv s c R = fun t : ℝ =>
      -(prolatePhaseSpeed s c t * prolateOscPotential s c t * prolateOsc s c R t
        * Real.cos (prolatePhase s c t)) from rfl]
  exact (((hspd.mul (continuousOn_prolateOscPotential hs1 hc)).mul hosc).mul
    (Real.continuous_cos.comp_continuousOn hph)).neg


theorem continuousOn_exactAmpDeriv {s c k X : ℝ} {A A' : ℝ → ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hk : 1 ≤ k) (hX : 2 ≤ X) (hAc : ContinuousOn A (Set.Ioi (1 : ℝ)))
    (hA'c : ContinuousOn A' (Set.Ioi (1 : ℝ))) :
    ContinuousOn (exactAmpDeriv s c k A A') (Set.uIcc (2 : ℝ) X) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hx2 : ∀ x ∈ Set.uIcc (2 : ℝ) X, (2 : ℝ) ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hX] at hx
    exact hx.1
  have hkx : ∀ x ∈ Set.uIcc (2 : ℝ) X, (1 : ℝ) < k * x := by
    intro x hx
    nlinarith [hx2 x hx, hk]
  have hlin : ContinuousOn (fun t : ℝ => k * t) (Set.uIcc (2 : ℝ) X) :=
    continuousOn_const.mul continuousOn_id
  have hmaps : Set.MapsTo (fun t : ℝ => k * t) (Set.uIcc (2 : ℝ) X) (Set.Ioi 1) :=
    fun x hx => hkx x hx
  have henv : ContinuousOn (fun x : ℝ => prolateEnvelope s c (k * x)) (Set.uIcc (2 : ℝ) X) :=
    (continuousOn_prolateEnvelope hs1 hc).comp hlin hmaps
  have henvd : ContinuousOn (fun x : ℝ => prolateEnvelopeDeriv s c (k * x))
      (Set.uIcc (2 : ℝ) X) := (continuousOn_prolateEnvelopeDeriv hs1 hc).comp hlin hmaps
  have hA : ContinuousOn (fun x : ℝ => A (k * x)) (Set.uIcc (2 : ℝ) X) := hAc.comp hlin hmaps
  have hA' : ContinuousOn (fun x : ℝ => A' (k * x)) (Set.uIcc (2 : ℝ) X) := hA'c.comp hlin hmaps
  have hsqc : ContinuousOn (fun x : ℝ => 1 / (2 * Real.sqrt x)) (Set.uIcc (2 : ℝ) X) := by
    refine continuousOn_const.div (continuousOn_const.mul Real.continuous_sqrt.continuousOn) ?_
    intro x hx
    have h := hx2 x hx
    have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    positivity
  rw [show exactAmpDeriv s c k A A' = fun x : ℝ =>
      1 / (2 * Real.sqrt x) * (prolateEnvelope s c (k * x) * A (k * x))
      + Real.sqrt x * (k * prolateEnvelopeDeriv s c (k * x) * A (k * x)
        + prolateEnvelope s c (k * x) * (k * A' (k * x))) from rfl]
  exact (hsqc.mul (henv.mul hA)).add (Real.continuous_sqrt.continuousOn.mul
    (((continuousOn_const.mul henvd).mul hA).add (henv.mul (continuousOn_const.mul hA'))))

/-- The complex amplitude of one exponential branch of the exact mode. -/
def exactBranchAmp (s c k eps : ℝ) (R DR : ℝ → ℝ) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * (((exactAmp s c k (exactCosCoeff s c R DR) x : ℝ) : ℂ)
    - (eps : ℂ) * Complex.I * ((exactAmp s c k (exactSinCoeff s c R DR) x : ℝ) : ℂ))

/-- Its derivative. -/
def exactBranchAmpDeriv (s c k eps : ℝ) (R DR : ℝ → ℝ) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * (((exactAmpDeriv s c k (exactCosCoeff s c R DR)
        (exactCosCoeffDeriv s c R) x : ℝ) : ℂ)
    - (eps : ℂ) * Complex.I * ((exactAmpDeriv s c k (exactSinCoeff s c R DR)
        (exactSinCoeffDeriv s c R) x : ℝ) : ℂ))

theorem hasDerivAt_exactBranchAmp {s c k eps x : ℝ} {R DR DDR : ℝ → ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hx0 : 0 < x) (hkx : 1 < k * x)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    HasDerivAt (exactBranchAmp s c k eps R DR) (exactBranchAmpDeriv s c k eps R DR x) x := by
  have hcos := (hasDerivAt_exactAmp (A := exactCosCoeff s c R DR)
    (A' := exactCosCoeffDeriv s c R) hs1 hc hx0 hkx
    (fun y hy => hasDerivAt_exactCosCoeff hs0 hs1 hc hy hR hDR hode)).ofReal_comp
  have hsin := (hasDerivAt_exactAmp (A := exactSinCoeff s c R DR)
    (A' := exactSinCoeffDeriv s c R) hs1 hc hx0 hkx
    (fun y hy => hasDerivAt_exactSinCoeff hs0 hs1 hc hy hR hDR hode)).ofReal_comp
  exact (hcos.sub (hsin.const_mul ((eps : ℂ) * Complex.I))).const_mul (1 / 2 : ℂ)

/-- **The dilated exact mode as two complex exponential branches.** -/
theorem sqrt_mul_radialProlate_dilate_eq_branches {s c k x : ℝ} {R DR : ℝ → ℝ} (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hk : 1 ≤ k) (hkx : 1 < k * x) :
    ((Real.sqrt x * R (k * x) : ℝ) : ℂ)
      = exactBranchAmp s c k 1 R DR x
          * Complex.exp (Complex.I * ((1 * (c * k) * dilatedPhase s k x : ℝ) : ℂ))
        + exactBranchAmp s c k (-1) R DR x
          * Complex.exp (Complex.I * ((-1 * (c * k) * dilatedPhase s k x : ℝ) : ℂ)) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hphase : (1 : ℝ) * (c * k) * dilatedPhase s k x = prolatePhase s c (k * x) := by
    rw [dilatedPhase, prolatePhase]
    field_simp
  have hphase' : (-1 : ℝ) * (c * k) * dilatedPhase s k x = -(prolatePhase s c (k * x)) := by
    rw [dilatedPhase, prolatePhase]
    field_simp
  rw [hphase, hphase', sqrt_mul_radialProlate_dilate_eq (R := R) (DR := DR) hs1 hc hkx,
    two_branch_euler, exactBranchAmp, exactBranchAmp]
  push_cast
  ring


theorem abs_exactBranchAmp_le {s c k eps x : ℝ} {R DR DDR : ℝ → ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 1 ≤ k) (hx : 1 ≤ x) (hkx2 : 2 ≤ k * x)
    (heps : |eps| = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    ‖exactBranchAmp s c k eps R DR x‖
      ≤ 300 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * k) / Real.sqrt x := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  set M : ℝ := exactEnergyBudget s c R DR 2 with hMdef
  have hM : (0 : ℝ) ≤ M := Real.sqrt_nonneg _
  obtain ⟨hA, hB⟩ := abs_exactCoeff_le (DDR := DDR) hs0 hs1 hc le_rfl hkx2 hR hDR hode
  have hcos := abs_exactAmp_le (A := exactCosCoeff s c R DR) hs1 hc hk (by linarith) hkx2 hM hA
  have hsin := abs_exactAmp_le (A := exactSinCoeff s c R DR) hs1 hc hk (by linarith) hkx2 hM hB
  rw [exactBranchAmp, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  have hsplit : ‖((exactAmp s c k (exactCosCoeff s c R DR) x : ℝ) : ℂ)
      - (eps : ℂ) * Complex.I * ((exactAmp s c k (exactSinCoeff s c R DR) x : ℝ) : ℂ)‖
      ≤ 300 * M / (Real.sqrt c * k) / Real.sqrt x
        + 300 * M / (Real.sqrt c * k) / Real.sqrt x := by
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖((exactAmp s c k (exactCosCoeff s c R DR) x : ℝ) : ℂ)‖
        ≤ 300 * M / (Real.sqrt c * k) / Real.sqrt x := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hcos
    have h2 : ‖(eps : ℂ) * Complex.I * ((exactAmp s c k (exactSinCoeff s c R DR) x : ℝ) : ℂ)‖
        ≤ 300 * M / (Real.sqrt c * k) / Real.sqrt x := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, Complex.norm_I, heps, one_mul, one_mul]
      exact hsin
    linarith
  calc 1 / 2 * ‖((exactAmp s c k (exactCosCoeff s c R DR) x : ℝ) : ℂ)
        - (eps : ℂ) * Complex.I * ((exactAmp s c k (exactSinCoeff s c R DR) x : ℝ) : ℂ)‖
      ≤ 1 / 2 * (300 * M / (Real.sqrt c * k) / Real.sqrt x
          + 300 * M / (Real.sqrt c * k) / Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hsplit (by norm_num)
    _ = 300 * M / (Real.sqrt c * k) / Real.sqrt x := by ring

theorem abs_exactBranchAmpDeriv_le {s c k eps x : ℝ} {R DR DDR : ℝ → ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1 / 2) (hc : 1 ≤ c) (hk : 1 ≤ k) (hx : 1 ≤ x) (hkx2 : 2 ≤ k * x)
    (heps : |eps| = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    ‖exactBranchAmpDeriv s c k eps R DR x‖
      ≤ 300 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * k) / (x * Real.sqrt x) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  set M : ℝ := exactEnergyBudget s c R DR 2 with hMdef
  have hM : (0 : ℝ) ≤ M := Real.sqrt_nonneg _
  obtain ⟨hA, hB⟩ := abs_exactCoeff_le (DDR := DDR) hs0 hs1 hc0 le_rfl hkx2 hR hDR hode
  obtain ⟨hA', hB'⟩ := abs_exactCoeffDeriv_le (DDR := DDR) hs0 hs1 hc0 le_rfl hkx2 hR hDR hode
  have hcos := abs_exactAmpDeriv_le (A := exactCosCoeff s c R DR)
    (A' := exactCosCoeffDeriv s c R) hs0 hs1 hc hk (by linarith) hkx2 hM hA hA'
  have hsin := abs_exactAmpDeriv_le (A := exactSinCoeff s c R DR)
    (A' := exactSinCoeffDeriv s c R) hs0 hs1 hc hk (by linarith) hkx2 hM hB hB'
  rw [exactBranchAmpDeriv, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  have hsplit : ‖((exactAmpDeriv s c k (exactCosCoeff s c R DR)
        (exactCosCoeffDeriv s c R) x : ℝ) : ℂ)
      - (eps : ℂ) * Complex.I * ((exactAmpDeriv s c k (exactSinCoeff s c R DR)
        (exactSinCoeffDeriv s c R) x : ℝ) : ℂ)‖
      ≤ 300 * M / (Real.sqrt c * k) / (x * Real.sqrt x)
        + 300 * M / (Real.sqrt c * k) / (x * Real.sqrt x) := by
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖((exactAmpDeriv s c k (exactCosCoeff s c R DR)
        (exactCosCoeffDeriv s c R) x : ℝ) : ℂ)‖
        ≤ 300 * M / (Real.sqrt c * k) / (x * Real.sqrt x) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hcos
    have h2 : ‖(eps : ℂ) * Complex.I * ((exactAmpDeriv s c k (exactSinCoeff s c R DR)
        (exactSinCoeffDeriv s c R) x : ℝ) : ℂ)‖
        ≤ 300 * M / (Real.sqrt c * k) / (x * Real.sqrt x) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, Complex.norm_I, heps, one_mul, one_mul]
      exact hsin
    linarith
  calc 1 / 2 * ‖((exactAmpDeriv s c k (exactCosCoeff s c R DR)
        (exactCosCoeffDeriv s c R) x : ℝ) : ℂ)
      - (eps : ℂ) * Complex.I * ((exactAmpDeriv s c k (exactSinCoeff s c R DR)
        (exactSinCoeffDeriv s c R) x : ℝ) : ℂ)‖
      ≤ 1 / 2 * (300 * M / (Real.sqrt c * k) / (x * Real.sqrt x)
          + 300 * M / (Real.sqrt c * k) / (x * Real.sqrt x)) :=
        mul_le_mul_of_nonneg_left hsplit (by norm_num)
    _ = 300 * M / (Real.sqrt c * k) / (x * Real.sqrt x) := by ring


theorem continuousOn_exactBranchAmp {s c k eps X : ℝ} {R DR DDR : ℝ → ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 1 ≤ k) (hX : 2 ≤ X)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    ContinuousOn (exactBranchAmp s c k eps R DR) (Set.uIcc (2 : ℝ) X) := by
  intro x hx
  rw [Set.uIcc_of_le hX] at hx
  have hkx : (1 : ℝ) < k * x := by nlinarith [hx.1, hk]
  exact ((hasDerivAt_exactBranchAmp (DDR := DDR) hs0 hs1 hc (by linarith [hx.1]) hkx hR hDR
    hode).continuousAt).continuousWithinAt

theorem continuousOn_exactBranchAmpDeriv {s c k eps X : ℝ} {R DR DDR : ℝ → ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 1 ≤ k) (hX : 2 ≤ X)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    ContinuousOn (exactBranchAmpDeriv s c k eps R DR) (Set.uIcc (2 : ℝ) X) := by
  have hAc : ContinuousOn (exactCosCoeff s c R DR) (Set.Ioi (1 : ℝ)) :=
    fun _ hy => ((hasDerivAt_exactCosCoeff hs0 hs1 hc hy hR hDR hode).continuousAt
      ).continuousWithinAt
  have hBc : ContinuousOn (exactSinCoeff s c R DR) (Set.Ioi (1 : ℝ)) :=
    fun _ hy => ((hasDerivAt_exactSinCoeff hs0 hs1 hc hy hR hDR hode).continuousAt
      ).continuousWithinAt
  have hcos : ContinuousOn (fun x : ℝ => ((exactAmpDeriv s c k (exactCosCoeff s c R DR)
      (exactCosCoeffDeriv s c R) x : ℝ) : ℂ)) (Set.uIcc (2 : ℝ) X) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_exactAmpDeriv hs1 hc hk hX hAc
      (continuousOn_exactCosCoeffDeriv (DR := DR) hs0 hs1 hc hR))
  have hsin : ContinuousOn (fun x : ℝ => ((exactAmpDeriv s c k (exactSinCoeff s c R DR)
      (exactSinCoeffDeriv s c R) x : ℝ) : ℂ)) (Set.uIcc (2 : ℝ) X) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_exactAmpDeriv hs1 hc hk hX hBc
      (continuousOn_exactSinCoeffDeriv (DR := DR) hs0 hs1 hc hR))
  exact continuousOn_const.mul (hcos.sub (continuousOn_const.mul hsin))

/-- The dilated exact mode in the exterior estimate's integrand shape. -/
theorem radialProlate_dilate_eq_branch_integrand {s c k t : ℝ} {R DR : ℝ → ℝ} (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hk : 1 ≤ k) (ht0 : 0 < t) (hkt : 1 < k * t) :
    ((R (k * t) : ℝ) : ℂ)
      = (exactBranchAmp s c k 1 R DR t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
          * Complex.exp (Complex.I * ((1 * (c * k) * dilatedPhase s k t : ℝ) : ℂ))
        + (exactBranchAmp s c k (-1) R DR t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
          * Complex.exp (Complex.I * ((-1 * (c * k) * dilatedPhase s k t : ℝ) : ℂ)) := by
  have hst : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hne : ((Real.sqrt t : ℝ) : ℂ) ≠ 0 := by simpa using (ne_of_gt hst)
  have hid := sqrt_mul_radialProlate_dilate_eq_branches (R := R) (DR := DR) hs1 hc hk hkt
  have hmul : ((Real.sqrt t : ℝ) : ℂ) * ((R (k * t) : ℝ) : ℂ)
      = exactBranchAmp s c k 1 R DR t
          * Complex.exp (Complex.I * ((1 * (c * k) * dilatedPhase s k t : ℝ) : ℂ))
        + exactBranchAmp s c k (-1) R DR t
          * Complex.exp (Complex.I * ((-1 * (c * k) * dilatedPhase s k t : ℝ) : ℂ)) := by
    rw [← hid]
    push_cast
    ring
  have hinv : (((Real.sqrt t)⁻¹ : ℝ) : ℂ) = (((Real.sqrt t : ℝ) : ℂ))⁻¹ := by push_cast; ring
  rw [hinv]
  have hsplit : ((R (k * t) : ℝ) : ℂ)
      = (((Real.sqrt t : ℝ) : ℂ))⁻¹ * (((Real.sqrt t : ℝ) : ℂ) * ((R (k * t) : ℝ) : ℂ)) := by
    field_simp
  rw [hsplit, hmul]
  ring


theorem continuousOn_exactBranchIntegrand {s c k eps X : ℝ} {R DR DDR : ℝ → ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 1 ≤ k) (hX : 2 ≤ X)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    ContinuousOn (fun t : ℝ => (exactBranchAmp s c k eps R DR t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
      * Complex.exp (Complex.I * ((eps * (c * k) * dilatedPhase s k t : ℝ) : ℂ)))
      (Set.uIcc (2 : ℝ) X) := by
  have hx2 : ∀ x ∈ Set.uIcc (2 : ℝ) X, (2 : ℝ) ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hX] at hx
    exact hx.1
  have hinv : ContinuousOn (fun t : ℝ => (((Real.sqrt t)⁻¹ : ℝ) : ℂ)) (Set.uIcc (2 : ℝ) X) := by
    refine Complex.continuous_ofReal.comp_continuousOn (ContinuousOn.inv₀
      Real.continuous_sqrt.continuousOn ?_)
    intro x hx
    exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx2 x hx]))
  have hexp : ContinuousOn
      (fun t : ℝ => Complex.exp (Complex.I * ((eps * (c * k) * dilatedPhase s k t : ℝ) : ℂ)))
      (Set.uIcc (2 : ℝ) X) :=
    Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_const.mul (continuousOn_dilatedPhase hs0 hk hX))))
  exact ((continuousOn_exactBranchAmp (DDR := DDR) hs0 hs1 hc hk hX hR hDR hode).mul hinv).mul hexp

/-- **`(16)` for the exact radial mode.**  The `k`-th channel primitive of the exact prolate mode
is `O(1/(c^{3/2} k²))`, uniformly in the endpoint of integration, with a constant free of `k`.
After the `√c` normalization this is the card's `(16)`: no model, no transfer, no error term. -/
theorem norm_integral_radialProlate_dilate_le {s c k X : ℝ} {R DR DDR : ℝ → ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1 / 2) (hc : 1 ≤ c) (hk : 1 ≤ k) (hX : 2 ≤ X)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    ‖∫ t in (2 : ℝ)..X, ((R (k * t) : ℝ) : ℂ)‖
      ≤ 1800 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * (c * k ^ (2 : ℕ))) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  set M : ℝ := exactEnergyBudget s c R DR 2 with hMdef
  have hM : (0 : ℝ) ≤ M := Real.sqrt_nonneg _
  have hCa : (0 : ℝ) ≤ 300 * M / (Real.sqrt c * k) := by positivity
  have hx2 : ∀ x ∈ Set.uIcc (2 : ℝ) X, (2 : ℝ) ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hX] at hx
    exact hx.1
  have hbranch : ∀ eps : ℝ, |eps| = 1 →
      ‖∫ t in (2 : ℝ)..X, (exactBranchAmp s c k eps R DR t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
          * Complex.exp (Complex.I * ((eps * (c * k) * dilatedPhase s k t : ℝ) : ℂ))‖
        ≤ 3 * (300 * M / (Real.sqrt c * k)) / (c * k) := by
    intro eps heps
    exact norm_integral_exterior_dilated_sharp_le (Ca := 300 * M / (Real.sqrt c * k))
      (a := exactBranchAmp s c k eps R DR) (a' := exactBranchAmpDeriv s c k eps R DR)
      hX hCa hc0 hk heps hs0 hs1
      (fun x hx => hasDerivAt_exactBranchAmp (DDR := DDR) hs0 hs1 hc0
        (by linarith [hx2 x hx]) (by nlinarith [hx2 x hx, hk, hk0]) hR hDR hode)
      (continuousOn_exactBranchAmp (DDR := DDR) hs0 hs1 hc0 hk hX hR hDR hode)
      (continuousOn_exactBranchAmpDeriv (DDR := DDR) hs0 hs1 hc0 hk hX hR hDR hode)
      (fun x hx => abs_exactBranchAmp_le (DDR := DDR) hs0 hs1 hc0 hk (by linarith [hx2 x hx])
        (by nlinarith [hx2 x hx, hk, hk0]) heps hR hDR hode)
      (fun x hx => abs_exactBranchAmpDeriv_le (DDR := DDR) hs0 hs1 hc hk
        (by linarith [hx2 x hx]) (by nlinarith [hx2 x hx, hk, hk0]) heps hR hDR hode)
  have hcongr : (∫ t in (2 : ℝ)..X, ((R (k * t) : ℝ) : ℂ))
      = (∫ t in (2 : ℝ)..X, (exactBranchAmp s c k 1 R DR t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
            * Complex.exp (Complex.I * ((1 * (c * k) * dilatedPhase s k t : ℝ) : ℂ)))
        + ∫ t in (2 : ℝ)..X, (exactBranchAmp s c k (-1) R DR t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
            * Complex.exp (Complex.I * ((-1 * (c * k) * dilatedPhase s k t : ℝ) : ℂ)) := by
    rw [← intervalIntegral.integral_add
      ((continuousOn_exactBranchIntegrand (DDR := DDR) hs0 hs1 hc0 hk hX hR hDR
        hode).intervalIntegrable)
      ((continuousOn_exactBranchIntegrand (DDR := DDR) hs0 hs1 hc0 hk hX hR hDR
        hode).intervalIntegrable)]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    have hxx := hx2 x hx
    have hkxx : (1 : ℝ) < k * x := by nlinarith [hk0, hxx, hk]
    exact radialProlate_dilate_eq_branch_integrand hs1 hc0 hk (by linarith) hkxx
  rw [hcongr]
  refine le_trans (norm_add_le _ _) ?_
  have h1 := hbranch 1 (by norm_num)
  have h2 := hbranch (-1) (by norm_num)
  have hsum : 3 * (300 * M / (Real.sqrt c * k)) / (c * k)
      + 3 * (300 * M / (Real.sqrt c * k)) / (c * k)
      = 1800 * M / (Real.sqrt c * (c * k ^ (2 : ℕ))) := by
    field_simp
    ring
  linarith [h1, h2, hsum]


/-- **The exterior channels of the exact mode sum.**  Because the constant is free of `k`, the
`1/k²` decay of `(16)` makes the whole radial object's exterior primitive bounded by a single
constant, uniformly in the endpoint of integration. -/
theorem tsum_norm_integral_radialProlate_channels_le {s c X : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 1 ≤ c) (hX : 2 ≤ X)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    ∑' k : ℕ, ‖∫ t in (2 : ℝ)..X, ((R (((k : ℝ) + 1) * t) : ℝ) : ℂ)‖
      ≤ 2 * (1800 * exactEnergyBudget s c R DR 2 / Real.sqrt c) / c := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  set M : ℝ := exactEnergyBudget s c R DR 2 with hMdef
  have hM : (0 : ℝ) ≤ M := Real.sqrt_nonneg _
  set B : ℝ := 1800 * M / Real.sqrt c with hBdef
  have hB : (0 : ℝ) ≤ B := by rw [hBdef]; positivity
  have hterm : ∀ k : ℕ, ‖∫ t in (2 : ℝ)..X, ((R (((k : ℝ) + 1) * t) : ℝ) : ℂ)‖
      ≤ channelMajorant B c k := by
    intro k
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h := norm_integral_radialProlate_dilate_le (DDR := DDR) (k := (k : ℝ) + 1)
      hs0 hs1 hc hk hX hR hDR hode
    refine le_trans h (le_of_eq ?_)
    rw [channelMajorant, hBdef, ← hMdef]
    have hne : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  have hnn : ∀ k : ℕ, (0 : ℝ) ≤ ‖∫ t in (2 : ℝ)..X, ((R (((k : ℝ) + 1) * t) : ℝ) : ℂ)‖ :=
    fun k => norm_nonneg _
  have hsummable : Summable fun k : ℕ =>
      ‖∫ t in (2 : ℝ)..X, ((R (((k : ℝ) + 1) * t) : ℝ) : ℂ)‖ :=
    (summable_channelMajorant (c := c) B).of_nonneg_of_le hnn hterm
  calc ∑' k : ℕ, ‖∫ t in (2 : ℝ)..X, ((R (((k : ℝ) + 1) * t) : ℝ) : ℂ)‖
      ≤ ∑' k : ℕ, channelMajorant B c k :=
        hsummable.tsum_le_tsum hterm (summable_channelMajorant (c := c) B)
    _ ≤ 2 * B / c := tsum_channelMajorant_le hB hc0


theorem continuousOn_dilatedPhase_left {s k L X : ℝ} (hs0 : 0 ≤ s) (hk : 1 ≤ k) (hL : 1 ≤ L)
    (hkL : 2 ≤ k * L) (hLX : L ≤ X) : ContinuousOn (dilatedPhase s k) (Set.uIcc L X) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  intro x hx
  rw [Set.uIcc_of_le hLX] at hx
  have hkx : (1 : ℝ) < k * x := by nlinarith [hx.1, hkL, hk0]
  exact ((hasDerivAt_dilatedPhase hs0 hk hkx).continuousAt).continuousWithinAt

theorem continuousOn_exactAmpDeriv_left {s c k L X : ℝ} {A A' : ℝ → ℝ} (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hk : 1 ≤ k) (hL : 1 ≤ L) (hkL : 2 ≤ k * L) (hLX : L ≤ X)
    (hAc : ContinuousOn A (Set.Ioi (1 : ℝ))) (hA'c : ContinuousOn A' (Set.Ioi (1 : ℝ))) :
    ContinuousOn (exactAmpDeriv s c k A A') (Set.uIcc L X) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hxL : ∀ x ∈ Set.uIcc L X, L ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hLX] at hx
    exact hx.1
  have hx1 : ∀ x ∈ Set.uIcc L X, (1 : ℝ) ≤ x := fun x hx => le_trans hL (hxL x hx)
  have hkx : ∀ x ∈ Set.uIcc L X, (1 : ℝ) < k * x := by
    intro x hx
    nlinarith [hxL x hx, hkL, hk0]
  have hlin : ContinuousOn (fun t : ℝ => k * t) (Set.uIcc L X) :=
    continuousOn_const.mul continuousOn_id
  have hmaps : Set.MapsTo (fun t : ℝ => k * t) (Set.uIcc L X) (Set.Ioi 1) := fun x hx => hkx x hx
  have henv : ContinuousOn (fun x : ℝ => prolateEnvelope s c (k * x)) (Set.uIcc L X) :=
    (continuousOn_prolateEnvelope hs1 hc).comp hlin hmaps
  have henvd : ContinuousOn (fun x : ℝ => prolateEnvelopeDeriv s c (k * x)) (Set.uIcc L X) :=
    (continuousOn_prolateEnvelopeDeriv hs1 hc).comp hlin hmaps
  have hA : ContinuousOn (fun x : ℝ => A (k * x)) (Set.uIcc L X) := hAc.comp hlin hmaps
  have hA' : ContinuousOn (fun x : ℝ => A' (k * x)) (Set.uIcc L X) := hA'c.comp hlin hmaps
  have hsqc : ContinuousOn (fun x : ℝ => 1 / (2 * Real.sqrt x)) (Set.uIcc L X) := by
    refine continuousOn_const.div (continuousOn_const.mul Real.continuous_sqrt.continuousOn) ?_
    intro x hx
    have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr (by linarith [hx1 x hx])
    positivity
  rw [show exactAmpDeriv s c k A A' = fun x : ℝ =>
      1 / (2 * Real.sqrt x) * (prolateEnvelope s c (k * x) * A (k * x))
      + Real.sqrt x * (k * prolateEnvelopeDeriv s c (k * x) * A (k * x)
        + prolateEnvelope s c (k * x) * (k * A' (k * x))) from rfl]
  exact (hsqc.mul (henv.mul hA)).add (Real.continuous_sqrt.continuousOn.mul
    (((continuousOn_const.mul henvd).mul hA).add (henv.mul (continuousOn_const.mul hA'))))

theorem continuousOn_exactBranchAmp_left {s c k eps L X : ℝ} {R DR DDR : ℝ → ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 1 ≤ k) (hL : 1 ≤ L) (hkL : 2 ≤ k * L) (hLX : L ≤ X)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    ContinuousOn (exactBranchAmp s c k eps R DR) (Set.uIcc L X) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  intro x hx
  rw [Set.uIcc_of_le hLX] at hx
  have hkx : (1 : ℝ) < k * x := by nlinarith [hx.1, hkL, hk0]
  exact ((hasDerivAt_exactBranchAmp (DDR := DDR) hs0 hs1 hc (by linarith [hx.1, hL]) hkx
    hR hDR hode).continuousAt).continuousWithinAt

theorem continuousOn_exactBranchAmpDeriv_left {s c k eps L X : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 1 ≤ k) (hL : 1 ≤ L) (hkL : 2 ≤ k * L)
    (hLX : L ≤ X)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    ContinuousOn (exactBranchAmpDeriv s c k eps R DR) (Set.uIcc L X) := by
  have hAc : ContinuousOn (exactCosCoeff s c R DR) (Set.Ioi (1 : ℝ)) :=
    fun _ hy => ((hasDerivAt_exactCosCoeff hs0 hs1 hc hy hR hDR hode).continuousAt
      ).continuousWithinAt
  have hBc : ContinuousOn (exactSinCoeff s c R DR) (Set.Ioi (1 : ℝ)) :=
    fun _ hy => ((hasDerivAt_exactSinCoeff hs0 hs1 hc hy hR hDR hode).continuousAt
      ).continuousWithinAt
  have hcos : ContinuousOn (fun x : ℝ => ((exactAmpDeriv s c k (exactCosCoeff s c R DR)
      (exactCosCoeffDeriv s c R) x : ℝ) : ℂ)) (Set.uIcc L X) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_exactAmpDeriv_left hs1 hc hk hL
      hkL hLX hAc (continuousOn_exactCosCoeffDeriv (DR := DR) hs0 hs1 hc hR))
  have hsin : ContinuousOn (fun x : ℝ => ((exactAmpDeriv s c k (exactSinCoeff s c R DR)
      (exactSinCoeffDeriv s c R) x : ℝ) : ℂ)) (Set.uIcc L X) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_exactAmpDeriv_left hs1 hc hk hL
      hkL hLX hBc (continuousOn_exactSinCoeffDeriv (DR := DR) hs0 hs1 hc hR))
  exact continuousOn_const.mul (hcos.sub (continuousOn_const.mul hsin))

theorem continuousOn_exactBranchIntegrand_left {s c k eps L X : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 1 ≤ k) (hL : 1 ≤ L) (hkL : 2 ≤ k * L)
    (hLX : L ≤ X)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    ContinuousOn (fun t : ℝ => (exactBranchAmp s c k eps R DR t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
      * Complex.exp (Complex.I * ((eps * (c * k) * dilatedPhase s k t : ℝ) : ℂ)))
      (Set.uIcc L X) := by
  have hx1 : ∀ x ∈ Set.uIcc L X, (1 : ℝ) ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hLX] at hx
    linarith [hx.1, hL]
  have hinv : ContinuousOn (fun t : ℝ => (((Real.sqrt t)⁻¹ : ℝ) : ℂ)) (Set.uIcc L X) := by
    refine Complex.continuous_ofReal.comp_continuousOn (ContinuousOn.inv₀
      Real.continuous_sqrt.continuousOn ?_)
    intro x hx
    exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx1 x hx]))
  have hexp : ContinuousOn
      (fun t : ℝ => Complex.exp (Complex.I * ((eps * (c * k) * dilatedPhase s k t : ℝ) : ℂ)))
      (Set.uIcc L X) :=
    Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_const.mul (continuousOn_dilatedPhase_left hs0 hk hL hkL hLX))))
  exact ((continuousOn_exactBranchAmp_left (DDR := DDR) hs0 hs1 hc hk hL hkL hLX hR hDR
    hode).mul hinv).mul hexp


/-- **`(16)` for the exact radial mode over the full channel range `[L, X]`.**  With `L = 1` and
`k >= 2` this covers the whole channel in one estimate: the gain is `1/(L c k)` from the endpoint
and a further `1/k` is already inside the amplitude constant. -/
theorem norm_integral_radialProlate_dilate_left_le {s c k L X : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 1 ≤ c) (hk : 1 ≤ k) (hL : 1 ≤ L) (hkL : 2 ≤ k * L)
    (hLX : L ≤ X)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    ‖∫ t in L..X, ((R (k * t) : ℝ) : ℂ)‖
      ≤ 4500 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * (c * k ^ (2 : ℕ)) * L) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  set M : ℝ := exactEnergyBudget s c R DR 2 with hMdef
  have hM : (0 : ℝ) ≤ M := Real.sqrt_nonneg _
  have hCa : (0 : ℝ) ≤ 300 * M / (Real.sqrt c * k) := by positivity
  have hxL : ∀ x ∈ Set.uIcc L X, L ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hLX] at hx
    exact hx.1
  have hx1 : ∀ x ∈ Set.uIcc L X, (1 : ℝ) ≤ x := fun x hx => le_trans hL (hxL x hx)
  have hkx2 : ∀ x ∈ Set.uIcc L X, (2 : ℝ) ≤ k * x := by
    intro x hx
    nlinarith [hxL x hx, hkL, hk0]
  have hbranch : ∀ eps : ℝ, |eps| = 1 →
      ‖∫ t in L..X, (exactBranchAmp s c k eps R DR t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
          * Complex.exp (Complex.I * ((eps * (c * k) * dilatedPhase s k t : ℝ) : ℂ))‖
        ≤ 15 * (300 * M / (Real.sqrt c * k)) / (2 * (L * (c * k))) := by
    intro eps heps
    exact norm_integral_exterior_dilated_left (Ca := 300 * M / (Real.sqrt c * k))
      (a := exactBranchAmp s c k eps R DR) (a' := exactBranchAmpDeriv s c k eps R DR)
      hL hLX hkL hCa hc0 hk heps hs0 hs1
      (fun x hx => hasDerivAt_exactBranchAmp (DDR := DDR) hs0 hs1 hc0
        (by linarith [hx1 x hx]) (by linarith [hkx2 x hx]) hR hDR hode)
      (continuousOn_exactBranchAmp_left (DDR := DDR) hs0 hs1 hc0 hk hL hkL hLX hR hDR hode)
      (continuousOn_exactBranchAmpDeriv_left (DDR := DDR) hs0 hs1 hc0 hk hL hkL hLX hR hDR hode)
      (fun x hx => abs_exactBranchAmp_le (DDR := DDR) hs0 hs1 hc0 hk (hx1 x hx) (hkx2 x hx)
        heps hR hDR hode)
      (fun x hx => abs_exactBranchAmpDeriv_le (DDR := DDR) hs0 hs1 hc hk (hx1 x hx)
        (hkx2 x hx) heps hR hDR hode)
  have hcongr : (∫ t in L..X, ((R (k * t) : ℝ) : ℂ))
      = (∫ t in L..X, (exactBranchAmp s c k 1 R DR t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
            * Complex.exp (Complex.I * ((1 * (c * k) * dilatedPhase s k t : ℝ) : ℂ)))
        + ∫ t in L..X, (exactBranchAmp s c k (-1) R DR t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
            * Complex.exp (Complex.I * ((-1 * (c * k) * dilatedPhase s k t : ℝ) : ℂ)) := by
    rw [← intervalIntegral.integral_add
      ((continuousOn_exactBranchIntegrand_left (DDR := DDR) hs0 hs1 hc0 hk hL hkL hLX hR hDR
        hode).intervalIntegrable)
      ((continuousOn_exactBranchIntegrand_left (DDR := DDR) hs0 hs1 hc0 hk hL hkL hLX hR hDR
        hode).intervalIntegrable)]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    exact radialProlate_dilate_eq_branch_integrand hs1 hc0 hk
      (by linarith [hx1 x hx]) (by linarith [hkx2 x hx])
  rw [hcongr]
  refine le_trans (norm_add_le _ _) ?_
  have h1 := hbranch 1 (by norm_num)
  have h2 := hbranch (-1) (by norm_num)
  have hsum : 15 * (300 * M / (Real.sqrt c * k)) / (2 * (L * (c * k)))
      + 15 * (300 * M / (Real.sqrt c * k)) / (2 * (L * (c * k)))
      = 4500 * M / (Real.sqrt c * (c * k ^ (2 : ℕ)) * L) := by
    field_simp
    ring
  linarith [h1, h2, hsum]


/-- **The full-range channels `k >= 2` sum.**  Each contributes `O(1/(c^{3/2} k^(2 : ℕ)))` over the whole
range `[1, X]`, and the constant is free of `k`, so the sum is a single constant. -/
theorem tsum_norm_integral_radialProlate_full_channels_le {s c X : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 1 ≤ c) (hX : 1 ≤ X)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    ∑' j : ℕ, ‖∫ t in (1 : ℝ)..X, ((R ((2 + (j : ℝ)) * t) : ℝ) : ℂ)‖
      ≤ 4500 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * c) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  set M : ℝ := exactEnergyBudget s c R DR 2 with hMdef
  have hM : (0 : ℝ) ≤ M := Real.sqrt_nonneg _
  set B : ℝ := 4500 * M / (Real.sqrt c * c) with hBdef
  have hB : (0 : ℝ) ≤ B := by rw [hBdef]; positivity
  have hterm : ∀ j : ℕ, ‖∫ t in (1 : ℝ)..X, ((R ((2 + (j : ℝ)) * t) : ℝ) : ℂ)‖
      ≤ B * (1 / (2 + (j : ℝ)) ^ (2 : ℕ)) := by
    intro j
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hk : (1 : ℝ) ≤ 2 + (j : ℝ) := by linarith
    have hkL : (2 : ℝ) ≤ (2 + (j : ℝ)) * 1 := by linarith
    have h := norm_integral_radialProlate_dilate_left_le (DDR := DDR) (k := 2 + (j : ℝ))
      (L := 1) hs0 hs1 hc hk le_rfl hkL hX hR hDR hode
    refine le_trans h (le_of_eq ?_)
    rw [hBdef, ← hMdef]
    have hne : (2 + (j : ℝ)) ≠ 0 := by positivity
    field_simp
  have hnn : ∀ j : ℕ, (0 : ℝ) ≤ ‖∫ t in (1 : ℝ)..X, ((R ((2 + (j : ℝ)) * t) : ℝ) : ℂ)‖ :=
    fun j => norm_nonneg _
  have hmaj : Summable fun j : ℕ => B * (1 / (2 + (j : ℝ)) ^ (2 : ℕ)) :=
    (GaloisForLFunctions.HTGeometry.summable_inv_sq_shift (σ := 2) (by norm_num)).mul_left B
  have hsummable : Summable fun j : ℕ =>
      ‖∫ t in (1 : ℝ)..X, ((R ((2 + (j : ℝ)) * t) : ℝ) : ℂ)‖ :=
    hmaj.of_nonneg_of_le hnn hterm
  calc ∑' j : ℕ, ‖∫ t in (1 : ℝ)..X, ((R ((2 + (j : ℝ)) * t) : ℝ) : ℂ)‖
      ≤ ∑' j : ℕ, B * (1 / (2 + (j : ℝ)) ^ (2 : ℕ)) := hsummable.tsum_le_tsum hterm hmaj
    _ = B * ∑' j : ℕ, 1 / (2 + (j : ℝ)) ^ (2 : ℕ) := tsum_mul_left
    _ ≤ B * 1 := mul_le_mul_of_nonneg_left
        GaloisForLFunctions.HTGeometry.tsum_inv_sq_shift_two_le_one hB
    _ = 4500 * M / (Real.sqrt c * c) := by rw [hBdef]; ring


/-- The endpoint constant of `(17)`. -/
def prolateEndpointConstant : ℝ :=
  9 / 4 + (8 * radialProlateUniformTransferConstant * lgBesselCommonEnvelopeConstant / 3
    + 2 * (648 * 64))

theorem prolateEndpointConstant_nonneg : 0 ≤ prolateEndpointConstant := by
  have hK : 0 ≤ radialProlateUniformTransferConstant := radialProlateUniformTransferConstant_nonneg
  have hC : 0 ≤ lgBesselCommonEnvelopeConstant := lgBesselCommonEnvelopeConstant_nonneg
  unfold prolateEndpointConstant
  positivity

/-- **The first channel.**  `k = 1` is the one channel whose range is not entirely exterior: it
splits at the Dunster crossing, with `(17)` on `[1,2]` and the exterior estimate beyond. -/
theorem norm_integral_radialProlate_first_channel_le {s c X : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c) (hR1 : R 1 = 1) (hX1 : 1 ≤ X)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    ‖∫ t in (1 : ℝ)..X, ((R t : ℝ) : ℂ)‖
      ≤ prolateEndpointConstant / (c * Real.sqrt c)
        + 2250 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * c) := by
  have hc1 : (1 : ℝ) ≤ c := by linarith
  have hc0 : (0 : ℝ) < c := by linarith
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  set M : ℝ := exactEnergyBudget s c R DR 2 with hMdef
  have hM : (0 : ℝ) ≤ M := Real.sqrt_nonneg _
  have htail0 : (0 : ℝ) ≤ 2250 * M / (Real.sqrt c * c) := by positivity
  have hRc : Continuous R := continuous_iff_continuousAt.mpr fun t => (hR t).continuousAt
  have hend : ∀ Y : ℝ, 1 ≤ Y → Y ≤ 2 →
      |∫ t in (1 : ℝ)..Y, R t| ≤ prolateEndpointConstant / (c * Real.sqrt c) := by
    intro Y hY1 hY2
    have h := abs_integral_sqrt_mul_radialProlate_full_le hs0 hs1 hc hR1 hR hDR hode hY1 hY2
    have hpull : (∫ t in (1 : ℝ)..Y, Real.sqrt c * R t)
        = Real.sqrt c * ∫ t in (1 : ℝ)..Y, R t := intervalIntegral.integral_const_mul _ _
    rw [hpull, abs_mul, abs_of_pos hsc, le_div_iff₀ hc0] at h
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < c * Real.sqrt c)]
    calc |∫ t in (1 : ℝ)..Y, R t| * (c * Real.sqrt c)
        = Real.sqrt c * |∫ t in (1 : ℝ)..Y, R t| * c := by ring
      _ ≤ prolateEndpointConstant := h
  rw [intervalIntegral.integral_ofReal, Complex.norm_real, Real.norm_eq_abs]
  rcases le_or_gt X 2 with hX2 | hX2
  · linarith [hend X hX1 hX2, htail0]
  · have hint1 : IntervalIntegrable R MeasureTheory.volume 1 2 := hRc.intervalIntegrable 1 2
    have hint2 : IntervalIntegrable R MeasureTheory.volume 2 X := hRc.intervalIntegrable 2 X
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
    have hfar : |∫ t in (2 : ℝ)..X, R t| ≤ 2250 * M / (Real.sqrt c * c) := by
      have hcongr : (∫ t in (2 : ℝ)..X, ((R ((1 : ℝ) * t) : ℝ) : ℂ))
          = ((∫ t in (2 : ℝ)..X, R t : ℝ) : ℂ) := by
        rw [← intervalIntegral.integral_ofReal]
        refine intervalIntegral.integral_congr (fun x _ => ?_)
        rw [one_mul]
      have h := norm_integral_radialProlate_dilate_left_le (DDR := DDR) (k := 1) (L := 2)
        (X := X) hs0 hs1 hc1 le_rfl (by norm_num) (by norm_num) (by linarith) hR hDR hode
      rw [hcongr, Complex.norm_real, Real.norm_eq_abs, ← hMdef] at h
      refine le_trans h (le_of_eq ?_)
      field_simp
      ring
    have heq : (∫ t in (1 : ℝ)..X, R t)
        = (∫ t in (1 : ℝ)..2, R t) + ∫ t in (2 : ℝ)..X, R t := by linarith [hsplit]
    rw [heq]
    refine le_trans (abs_add_le _ _) ?_
    linarith [hend 2 (by norm_num) le_rfl, hfar]


/-- **`(11)` for the exact radial mode.**  Every channel's primitive, summed, is bounded by one
constant, uniformly in the endpoint of integration.  The first channel contributes the endpoint
term `O(c^{-3/2})` and the exterior term; the channels `k >= 2` contribute a convergent series. -/
theorem tsum_norm_integral_radialProlate_all_channels_le {s c X : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c) (hR1 : R 1 = 1) (hX1 : 1 ≤ X)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    ‖∫ t in (1 : ℝ)..X, ((R t : ℝ) : ℂ)‖
        + ∑' j : ℕ, ‖∫ t in (1 : ℝ)..X, ((R ((2 + (j : ℝ)) * t) : ℝ) : ℂ)‖
      ≤ prolateEndpointConstant / (c * Real.sqrt c)
        + 6750 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * c) := by
  have hc1 : (1 : ℝ) ≤ c := by linarith
  have hc0 : (0 : ℝ) < c := by linarith
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  set M : ℝ := exactEnergyBudget s c R DR 2 with hMdef
  have h1 := norm_integral_radialProlate_first_channel_le (DDR := DDR) hs0 hs1 hc hR1 hX1
    hR hDR hode
  have h2 := tsum_norm_integral_radialProlate_full_channels_le (DDR := DDR) hs0 hs1 hc1 hX1
    hR hDR hode
  rw [← hMdef] at h1 h2
  have hsum : 2250 * M / (Real.sqrt c * c) + 4500 * M / (Real.sqrt c * c)
      = 6750 * M / (Real.sqrt c * c) := by ring
  linarith [h1, h2, hsum]


end GaloisForLFunctions.RHTower
