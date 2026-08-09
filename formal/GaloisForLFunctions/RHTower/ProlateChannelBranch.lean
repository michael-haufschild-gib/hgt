import GaloisForLFunctions.RHTower.ProlateTwoBranch

/-!
# The channel branch amplitude for an arbitrary slowly varying coefficient

Both coefficients of the exact two-branch representation of the Bessel normal form obey the same
two bounds: they are bounded by the energy, and their derivatives are bounded by the energy times
`1/(4u²)`.  Everything the exterior estimate needs about a channel amplitude follows from those
two bounds alone, so the amplitude layer is built once for an arbitrary coefficient and
instantiated at both.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

/-- The channel amplitude built from a coefficient `A` transported along the dilated phase. -/
def branchAmplitude (s c k : ℝ) (A : ℝ → ℝ) (x : ℝ) : ℝ :=
  ampFourth s (k * x) * A (c * xiEndpointPhase s (k * x))

/-- Its derivative, in terms of the coefficient's derivative. -/
def branchAmplitudeDeriv (s c k : ℝ) (A A' : ℝ → ℝ) (x : ℝ) : ℝ :=
  k * (-(2 * (k * x) * (2 * (k * x) ^ 2 - s - 1))
      / (4 * (((k * x) ^ 2 - 1) * ((k * x) ^ 2 - s))) * ampFourth s (k * x))
    * A (c * xiEndpointPhase s (k * x))
  + ampFourth s (k * x)
    * (A' (c * xiEndpointPhase s (k * x)) * (c * (k * xiSpeed s (k * x))))

theorem hasDerivAt_branchAmplitude {s c k x : ℝ} {A A' : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 1 ≤ k) (hx : 2 ≤ x)
    (hA : ∀ u : ℝ, 0 < u → HasDerivAt A (A' u) u) :
    HasDerivAt (branchAmplitude s c k A) (branchAmplitudeDeriv s c k A A' x) x := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hkx : (1 : ℝ) < k * x := by nlinarith [hk, hx]
  have hph : 0 < xiEndpointPhase s (k * x) := xiEndpointPhase_pos hs0 hs1 hkx
  have hu : 0 < c * xiEndpointPhase s (k * x) := by positivity
  have hlin : HasDerivAt (fun u : ℝ => k * u) k x := by
    simpa using (hasDerivAt_id x).const_mul k
  have hamp : HasDerivAt (fun u : ℝ => ampFourth s (k * u))
      (k * (-(2 * (k * x) * (2 * (k * x) ^ 2 - s - 1))
        / (4 * (((k * x) ^ 2 - 1) * ((k * x) ^ 2 - s))) * ampFourth s (k * x))) x := by
    have h := (hasDerivAt_ampFourth hs1 hkx).comp x hlin
    have hv : -(2 * (k * x) * (2 * (k * x) ^ 2 - s - 1))
        / (4 * (((k * x) ^ 2 - 1) * ((k * x) ^ 2 - s))) * ampFourth s (k * x) * k
        = k * (-(2 * (k * x) * (2 * (k * x) ^ 2 - s - 1))
          / (4 * (((k * x) ^ 2 - 1) * ((k * x) ^ 2 - s))) * ampFourth s (k * x)) := by ring
    rwa [hv] at h
  exact hamp.mul ((hA _ hu).comp x (hasDerivAt_scaled_dilated_phase hs0 hkx))

/-- **The branch amplitude carries the `1/k`.** -/
theorem abs_branchAmplitude_le {s c k x M : ℝ} {A : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 ≤ k) (hx : 2 ≤ x)
    (hAb : |A (c * xiEndpointPhase s (k * x))| ≤ M) :
    |branchAmplitude s c k A x| ≤ 2 * M / k / x := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hx0 : (0 : ℝ) < x := by linarith
  have hkx : (1 : ℝ) < k * x := by nlinarith [hk, hx]
  have hamp := ampFourth_dilate_le hs0 hs1 hk hx
  have hamp0 : (0 : ℝ) < ampFourth s (k * x) := ampFourth_pos hs1 hkx
  rw [branchAmplitude, abs_mul, abs_of_pos hamp0]
  have hstep : ampFourth s (k * x) * |A (c * xiEndpointPhase s (k * x))|
      ≤ 2 / (k * x) * M := mul_le_mul hamp hAb (abs_nonneg _) (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  field_simp

/-- **The coefficient's drift along the dilated phase is `O(1/(c k x²))`.** -/
theorem abs_branch_drift_le {s c k x M : ℝ} {A' : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 1 ≤ k) (hx : 2 ≤ x) (hM : 0 ≤ M)
    (hA'b : |A' (c * xiEndpointPhase s (k * x))|
      ≤ 1 / (4 * (c * xiEndpointPhase s (k * x)) ^ 2) * M) :
    |A' (c * xiEndpointPhase s (k * x)) * (c * (k * xiSpeed s (k * x)))|
      ≤ 2 * M / (c * k * x ^ 2) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hx0 : (0 : ℝ) < x := by linarith
  have hkx2 : (2 : ℝ) ≤ k * x := by nlinarith [hk, hx]
  have hkx : (1 : ℝ) < k * x := by linarith
  have hph : 0 < xiEndpointPhase s (k * x) := xiEndpointPhase_pos hs0 hs1 hkx
  set u : ℝ := c * xiEndpointPhase s (k * x) with hudef
  have hu : 0 < u := by rw [hudef]; positivity
  have hspeed : xiSpeed s (k * x) ≤ 2 := xiSpeed_le_two hs0 hkx2
  have hspeed0 : (0 : ℝ) ≤ xiSpeed s (k * x) :=
    le_trans zero_le_one (one_le_xiSpeed (by linarith) hkx)
  have hphase : k * x / 2 ≤ xiEndpointPhase s (k * x) :=
    half_mul_le_xiEndpointPhase hs0 hs1 hkx2
  have hulow : c * (k * x) / 2 ≤ u := by
    rw [hudef]
    have := mul_le_mul_of_nonneg_left hphase hc.le
    linarith [this]
  have hulow0 : (0 : ℝ) < c * (k * x) / 2 := by positivity
  rw [abs_mul]
  have hfac : |c * (k * xiSpeed s (k * x))| ≤ c * (k * 2) := by
    rw [abs_of_nonneg (mul_nonneg hc.le (mul_nonneg hk0.le hspeed0))]
    have := mul_le_mul_of_nonneg_left hspeed hk0.le
    nlinarith [this, hc.le]
  have hstep : |A' u| * |c * (k * xiSpeed s (k * x))|
      ≤ (1 / (4 * u ^ 2) * M) * (c * (k * 2)) :=
    mul_le_mul hA'b hfac (abs_nonneg _) (by positivity)
  refine le_trans hstep ?_
  have hq : 1 / (4 * u ^ 2) ≤ 1 / (c ^ 2 * (k * x) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hulow, hulow0, hu]
  have hfin : 1 / (c ^ 2 * (k * x) ^ 2) * M * (c * (k * 2))
      = 2 * M / (c * k * x ^ 2) := by field_simp
  calc 1 / (4 * u ^ 2) * M * (c * (k * 2))
      ≤ 1 / (c ^ 2 * (k * x) ^ 2) * M * (c * (k * 2)) := by gcongr
    _ = 2 * M / (c * k * x ^ 2) := hfin

/-- **The branch amplitude's derivative also carries the `1/k`.** -/
theorem abs_branchAmplitudeDeriv_le {s c k x M : ℝ} {A A' : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 1 ≤ c) (hk : 1 ≤ k) (hx : 2 ≤ x) (hM : 0 ≤ M)
    (hAb : |A (c * xiEndpointPhase s (k * x))| ≤ M)
    (hA'b : |A' (c * xiEndpointPhase s (k * x))|
      ≤ 1 / (4 * (c * xiEndpointPhase s (k * x)) ^ 2) * M) :
    |branchAmplitudeDeriv s c k A A' x| ≤ 36 * M / k / x ^ 2 := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hx0 : (0 : ℝ) < x := by linarith
  have hkx : (1 : ℝ) < k * x := by nlinarith [hk, hx]
  have hamp0 : (0 : ℝ) < ampFourth s (k * x) := ampFourth_pos hs1 hkx
  have hampd := abs_deriv_ampFourth_dilate_le hs0 hs1 hk hx
  have hampb := ampFourth_dilate_le hs0 hs1 hk hx
  have hdrift := abs_branch_drift_le hs0 hs1 hc0 hk hx hM hA'b
  rw [branchAmplitudeDeriv]
  refine le_trans (abs_add_le _ _) ?_
  have h1 : |k * (-(2 * (k * x) * (2 * (k * x) ^ 2 - s - 1))
        / (4 * (((k * x) ^ 2 - 1) * ((k * x) ^ 2 - s))) * ampFourth s (k * x))
      * A (c * xiEndpointPhase s (k * x))|
      ≤ 32 * M / (k * x ^ 2) := by
    rw [abs_mul]
    calc |k * (-(2 * (k * x) * (2 * (k * x) ^ 2 - s - 1))
            / (4 * (((k * x) ^ 2 - 1) * ((k * x) ^ 2 - s))) * ampFourth s (k * x))|
          * |A (c * xiEndpointPhase s (k * x))|
        ≤ 32 / (k * x ^ 2) * M := mul_le_mul hampd hAb (abs_nonneg _) (by positivity)
      _ = 32 * M / (k * x ^ 2) := by ring
  have h2 : |ampFourth s (k * x)
      * (A' (c * xiEndpointPhase s (k * x)) * (c * (k * xiSpeed s (k * x))))|
      ≤ 4 * M / (k * x ^ 2) := by
    rw [abs_mul, abs_of_pos hamp0]
    have hstep : ampFourth s (k * x)
        * |A' (c * xiEndpointPhase s (k * x)) * (c * (k * xiSpeed s (k * x)))|
        ≤ 2 / (k * x) * (2 * M / (c * k * x ^ 2)) :=
      mul_le_mul hampb hdrift (abs_nonneg _) (by positivity)
    refine le_trans hstep ?_
    have hval : 2 / (k * x) * (2 * M / (c * k * x ^ 2)) = 4 * M / (c * k ^ 2 * x ^ 3) := by
      field_simp
      ring
    rw [hval, div_le_div_iff₀ (by positivity) (by positivity)]
    have hckx : (1 : ℝ) ≤ c * k * x := by nlinarith [hc, hk, hx]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * M) hk0.le)
      (sq_nonneg x)) (by linarith : (0 : ℝ) ≤ c * k * x - 1)]
  have hsum : 32 * M / (k * x ^ 2) + 4 * M / (k * x ^ 2) = 36 * M / k / x ^ 2 := by
    field_simp
    ring
  linarith [h1, h2, hsum]

/-- The branch amplitude in the exterior estimate's normalization. -/
def branchAmp (s c k : ℝ) (A : ℝ → ℝ) (x : ℝ) : ℝ := Real.sqrt x * branchAmplitude s c k A x

/-- Its derivative. -/
def branchAmpDeriv (s c k : ℝ) (A A' : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 / (2 * Real.sqrt x) * branchAmplitude s c k A x
    + Real.sqrt x * branchAmplitudeDeriv s c k A A' x

theorem hasDerivAt_branchAmp {s c k x : ℝ} {A A' : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 1 ≤ k) (hx : 2 ≤ x)
    (hA : ∀ u : ℝ, 0 < u → HasDerivAt A (A' u) u) :
    HasDerivAt (branchAmp s c k A) (branchAmpDeriv s c k A A' x) x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x :=
    Real.hasDerivAt_sqrt (ne_of_gt hx0)
  exact hsq.mul (hasDerivAt_branchAmplitude hs0 hs1 hc hk hx hA)

theorem abs_branchAmp_le {s c k x M : ℝ} {A : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 ≤ k) (hx : 2 ≤ x)
    (hAb : |A (c * xiEndpointPhase s (k * x))| ≤ M) :
    |branchAmp s c k A x| ≤ 2 * M / k / Real.sqrt x := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hbase := abs_branchAmplitude_le hs0 hs1 hk hx hAb
  rw [branchAmp, abs_mul, abs_of_pos hsx]
  have hval : Real.sqrt x * (2 * M / k / x) = 2 * M / k / Real.sqrt x := by
    field_simp
    linear_combination M * hss
  calc Real.sqrt x * |branchAmplitude s c k A x| ≤ Real.sqrt x * (2 * M / k / x) :=
        mul_le_mul_of_nonneg_left hbase hsx.le
    _ = 2 * M / k / Real.sqrt x := hval

theorem abs_branchAmpDeriv_le {s c k x M : ℝ} {A A' : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 1 ≤ c) (hk : 1 ≤ k) (hx : 2 ≤ x) (hM : 0 ≤ M)
    (hAb : |A (c * xiEndpointPhase s (k * x))| ≤ M)
    (hA'b : |A' (c * xiEndpointPhase s (k * x))|
      ≤ 1 / (4 * (c * xiEndpointPhase s (k * x)) ^ 2) * M) :
    |branchAmpDeriv s c k A A' x| ≤ 37 * M / k / (x * Real.sqrt x) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hsq2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  have hb := abs_branchAmplitude_le hs0 hs1 hk hx hAb
  have hd := abs_branchAmplitudeDeriv_le hs0 hs1 hc hk hx hM hAb hA'b
  rw [branchAmpDeriv]
  refine le_trans (abs_add_le _ _) ?_
  have h1 : |1 / (2 * Real.sqrt x) * branchAmplitude s c k A x|
      ≤ M / k / (x * Real.sqrt x) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.sqrt x))]
    have hstep : 1 / (2 * Real.sqrt x) * |branchAmplitude s c k A x|
        ≤ 1 / (2 * Real.sqrt x) * (2 * M / k / x) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  have h2 : |Real.sqrt x * branchAmplitudeDeriv s c k A A' x|
      ≤ 36 * M / k / (x * Real.sqrt x) := by
    rw [abs_mul, abs_of_pos hsx]
    have hstep : Real.sqrt x * |branchAmplitudeDeriv s c k A A' x|
        ≤ Real.sqrt x * (36 * M / k / x ^ 2) :=
      mul_le_mul_of_nonneg_left hd hsx.le
    refine le_trans hstep (le_of_eq ?_)
    field_simp
    linear_combination M * hsq2
  have hsum : M / k / (x * Real.sqrt x) + 36 * M / k / (x * Real.sqrt x)
      = 37 * M / k / (x * Real.sqrt x) := by ring
  linarith [h1, h2, hsum]

theorem continuousOn_branchAmplitudeDeriv {s c k X : ℝ} {A A' : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 1 ≤ k) (hX : 2 ≤ X)
    (hAc : ContinuousOn A (Set.Ioi 0)) (hA'c : ContinuousOn A' (Set.Ioi 0)) :
    ContinuousOn (branchAmplitudeDeriv s c k A A') (Set.uIcc (2 : ℝ) X) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hx2 : ∀ x ∈ Set.uIcc (2 : ℝ) X, (2 : ℝ) ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hX] at hx
    exact hx.1
  have hkx : ∀ x ∈ Set.uIcc (2 : ℝ) X, (1 : ℝ) < k * x := by
    intro x hx
    nlinarith [hx2 x hx, hk]
  have hphpos : ∀ x ∈ Set.uIcc (2 : ℝ) X, 0 < c * xiEndpointPhase s (k * x) := by
    intro x hx
    have := xiEndpointPhase_pos hs0 hs1 (hkx x hx)
    positivity
  have hlin : ContinuousOn (fun t : ℝ => k * t) (Set.uIcc (2 : ℝ) X) :=
    continuousOn_const.mul continuousOn_id
  have hmaps : Set.MapsTo (fun t : ℝ => k * t) (Set.uIcc (2 : ℝ) X) (Set.Ioi 1) :=
    fun x hx => hkx x hx
  have hampc : ContinuousOn (fun x : ℝ => ampFourth s (k * x)) (Set.uIcc (2 : ℝ) X) :=
    (continuousOn_ampFourth_Ioi hs1).comp hlin hmaps
  have hphc : ContinuousOn (fun x : ℝ => c * xiEndpointPhase s (k * x)) (Set.uIcc (2 : ℝ) X) :=
    continuousOn_const.mul (((continuousOn_xiEndpointPhase hs0).comp hlin hmaps))
  have hphmaps : Set.MapsTo (fun x : ℝ => c * xiEndpointPhase s (k * x))
      (Set.uIcc (2 : ℝ) X) (Set.Ioi 0) := fun x hx => hphpos x hx
  have hA'comp : ContinuousOn (fun x : ℝ => A' (c * xiEndpointPhase s (k * x)))
      (Set.uIcc (2 : ℝ) X) := hA'c.comp hphc hphmaps
  have hspc : ContinuousOn (fun x : ℝ => xiSpeed s (k * x)) (Set.uIcc (2 : ℝ) X) :=
    (continuousOn_xiSpeed s).comp hlin hmaps
  have hratc : ContinuousOn (fun x : ℝ => -(2 * (k * x) * (2 * (k * x) ^ 2 - s - 1))
      / (4 * (((k * x) ^ 2 - 1) * ((k * x) ^ 2 - s)))) (Set.uIcc (2 : ℝ) X) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro x hx
    have h1 : (1 : ℝ) < k * x := hkx x hx
    have hd : (0 : ℝ) < (k * x) ^ 2 - 1 := by nlinarith
    have hn : (0 : ℝ) < (k * x) ^ 2 - s := by nlinarith
    positivity
  have hAcomp : ContinuousOn (fun x : ℝ => A (c * xiEndpointPhase s (k * x)))
      (Set.uIcc (2 : ℝ) X) := hAc.comp hphc hphmaps
  rw [show branchAmplitudeDeriv s c k A A' = fun x : ℝ =>
      k * (-(2 * (k * x) * (2 * (k * x) ^ 2 - s - 1))
        / (4 * (((k * x) ^ 2 - 1) * ((k * x) ^ 2 - s))) * ampFourth s (k * x))
      * A (c * xiEndpointPhase s (k * x))
    + ampFourth s (k * x)
      * (A' (c * xiEndpointPhase s (k * x)) * (c * (k * xiSpeed s (k * x)))) from rfl]
  exact ((continuousOn_const.mul (hratc.mul hampc)).mul hAcomp).add
    (hampc.mul (hA'comp.mul (continuousOn_const.mul (continuousOn_const.mul hspc))))

theorem continuousOn_branchAmpDeriv {s c k X : ℝ} {A A' : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 1 ≤ k) (hX : 2 ≤ X)
    (hA : ∀ u : ℝ, 0 < u → HasDerivAt A (A' u) u)
    (hAc : ContinuousOn A (Set.Ioi 0)) (hA'c : ContinuousOn A' (Set.Ioi 0)) :
    ContinuousOn (branchAmpDeriv s c k A A') (Set.uIcc (2 : ℝ) X) := by
  have hx2 : ∀ x ∈ Set.uIcc (2 : ℝ) X, (2 : ℝ) ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hX] at hx
    exact hx.1
  have hampc : ContinuousOn (branchAmplitude s c k A) (Set.uIcc (2 : ℝ) X) :=
    fun x hx => ((hasDerivAt_branchAmplitude hs0 hs1 hc hk (hx2 x hx) hA).continuousAt
      ).continuousWithinAt
  have hsqc : ContinuousOn (fun x : ℝ => 1 / (2 * Real.sqrt x)) (Set.uIcc (2 : ℝ) X) := by
    refine continuousOn_const.div (continuousOn_const.mul Real.continuous_sqrt.continuousOn) ?_
    intro x hx
    have h := hx2 x hx
    have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    positivity
  rw [show branchAmpDeriv s c k A A' = fun x : ℝ =>
      1 / (2 * Real.sqrt x) * branchAmplitude s c k A x
        + Real.sqrt x * branchAmplitudeDeriv s c k A A' x from rfl]
  exact (hsqc.mul hampc).add (Real.continuous_sqrt.continuousOn.mul
    (continuousOn_branchAmplitudeDeriv hs0 hs1 hc hk hX hAc hA'c))

/-- The derivative of the cosine coefficient, named for reuse. -/
def besselCosCoeffDeriv (u : ℝ) : ℝ := 1 / (4 * u ^ 2) * besselNormalForm u * Real.sin u

/-- The derivative of the sine coefficient. -/
def besselSinCoeffDeriv (u : ℝ) : ℝ := -(1 / (4 * u ^ 2) * besselNormalForm u * Real.cos u)

theorem hasDerivAt_besselCosCoeff' {u : ℝ} (hu : 0 < u) :
    HasDerivAt besselCosCoeff (besselCosCoeffDeriv u) u := hasDerivAt_besselCosCoeff hu

theorem hasDerivAt_besselSinCoeff' {u : ℝ} (hu : 0 < u) :
    HasDerivAt besselSinCoeff (besselSinCoeffDeriv u) u := hasDerivAt_besselSinCoeff hu

theorem continuousOn_besselCosCoeff : ContinuousOn besselCosCoeff (Set.Ioi (0 : ℝ)) :=
  fun _ hu => ((hasDerivAt_besselCosCoeff hu).continuousAt).continuousWithinAt

theorem continuousOn_besselSinCoeff : ContinuousOn besselSinCoeff (Set.Ioi (0 : ℝ)) :=
  fun _ hu => ((hasDerivAt_besselSinCoeff hu).continuousAt).continuousWithinAt

theorem continuousOn_besselNormalForm : ContinuousOn besselNormalForm (Set.Ioi (0 : ℝ)) :=
  fun _ hu => ((hasDerivAt_besselNormalForm hu).continuousAt).continuousWithinAt

theorem continuousOn_besselCosCoeffDeriv : ContinuousOn besselCosCoeffDeriv (Set.Ioi (0 : ℝ)) := by
  refine ContinuousOn.mul (ContinuousOn.mul ?_ continuousOn_besselNormalForm)
    Real.continuous_sin.continuousOn
  refine continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 2)) ?_
  intro u hu
  have : (0 : ℝ) < u := hu
  positivity

theorem continuousOn_besselSinCoeffDeriv : ContinuousOn besselSinCoeffDeriv (Set.Ioi (0 : ℝ)) := by
  refine ContinuousOn.neg (ContinuousOn.mul (ContinuousOn.mul ?_ continuousOn_besselNormalForm)
    Real.continuous_cos.continuousOn)
  refine continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 2)) ?_
  intro u hu
  have : (0 : ℝ) < u := hu
  positivity

/-- **The complex amplitude of one exponential branch.**  The exact two-branch representation
`A cos u + B sin u = ½(A - iB) e^{iu} + ½(A + iB) e^{-iu}` puts both real coefficients into a
single complex amplitude per branch. -/
def channelBranchAmp (s c k eps : ℝ) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * (((branchAmp s c k besselCosCoeff x : ℝ) : ℂ)
    - (eps : ℂ) * Complex.I * ((branchAmp s c k besselSinCoeff x : ℝ) : ℂ))

/-- Its derivative. -/
def channelBranchAmpDeriv (s c k eps : ℝ) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * (((branchAmpDeriv s c k besselCosCoeff besselCosCoeffDeriv x : ℝ) : ℂ)
    - (eps : ℂ) * Complex.I
      * ((branchAmpDeriv s c k besselSinCoeff besselSinCoeffDeriv x : ℝ) : ℂ))

theorem hasDerivAt_channelBranchAmp {s c k eps x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hk : 1 ≤ k) (hx : 2 ≤ x) :
    HasDerivAt (channelBranchAmp s c k eps) (channelBranchAmpDeriv s c k eps x) x := by
  have hcos := (hasDerivAt_branchAmp (A := besselCosCoeff) (A' := besselCosCoeffDeriv)
    hs0 hs1 hc hk hx (fun _ hu => hasDerivAt_besselCosCoeff' hu)).ofReal_comp
  have hsin := (hasDerivAt_branchAmp (A := besselSinCoeff) (A' := besselSinCoeffDeriv)
    hs0 hs1 hc hk hx (fun _ hu => hasDerivAt_besselSinCoeff' hu)).ofReal_comp
  exact (hcos.sub (hsin.const_mul ((eps : ℂ) * Complex.I))).const_mul (1 / 2 : ℂ)

theorem continuousOn_channelBranchAmpDeriv {s c k eps X : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hk : 1 ≤ k) (hX : 2 ≤ X) :
    ContinuousOn (channelBranchAmpDeriv s c k eps) (Set.uIcc (2 : ℝ) X) := by
  have hcos : ContinuousOn (fun x : ℝ =>
      ((branchAmpDeriv s c k besselCosCoeff besselCosCoeffDeriv x : ℝ) : ℂ))
      (Set.uIcc (2 : ℝ) X) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_branchAmpDeriv hs0 hs1 hc hk hX (fun _ hu => hasDerivAt_besselCosCoeff' hu)
        continuousOn_besselCosCoeff continuousOn_besselCosCoeffDeriv)
  have hsin : ContinuousOn (fun x : ℝ =>
      ((branchAmpDeriv s c k besselSinCoeff besselSinCoeffDeriv x : ℝ) : ℂ))
      (Set.uIcc (2 : ℝ) X) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_branchAmpDeriv hs0 hs1 hc hk hX (fun _ hu => hasDerivAt_besselSinCoeff' hu)
        continuousOn_besselSinCoeff continuousOn_besselSinCoeffDeriv)
  exact continuousOn_const.mul (hcos.sub (continuousOn_const.mul hsin))

theorem abs_channelBranchAmp_le {s c k eps x a : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hk : 1 ≤ k) (hx : 2 ≤ x) (heps : |eps| = 1) (ha : 0 < a)
    (hau : a ≤ c * xiEndpointPhase s (k * x)) :
    ‖channelBranchAmp s c k eps x‖
      ≤ 2 * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) / k / Real.sqrt x := by
  obtain ⟨hA, hB⟩ := abs_besselCoeff_le_base ha hau
  have hcos := abs_branchAmp_le (A := besselCosCoeff) hs0 hs1 hk hx hA
  have hsin := abs_branchAmp_le (A := besselSinCoeff) hs0 hs1 hk hx hB
  set M : ℝ := Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) with hMdef
  rw [channelBranchAmp, norm_mul]
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hhalf]
  have hsplit : ‖((branchAmp s c k besselCosCoeff x : ℝ) : ℂ)
      - (eps : ℂ) * Complex.I * ((branchAmp s c k besselSinCoeff x : ℝ) : ℂ)‖
      ≤ 2 * M / k / Real.sqrt x + 2 * M / k / Real.sqrt x := by
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖((branchAmp s c k besselCosCoeff x : ℝ) : ℂ)‖ ≤ 2 * M / k / Real.sqrt x := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hcos
    have h2 : ‖(eps : ℂ) * Complex.I * ((branchAmp s c k besselSinCoeff x : ℝ) : ℂ)‖
        ≤ 2 * M / k / Real.sqrt x := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, Complex.norm_I, heps, one_mul, one_mul]
      exact hsin
    linarith
  calc 1 / 2 * ‖((branchAmp s c k besselCosCoeff x : ℝ) : ℂ)
        - (eps : ℂ) * Complex.I * ((branchAmp s c k besselSinCoeff x : ℝ) : ℂ)‖
      ≤ 1 / 2 * (2 * M / k / Real.sqrt x + 2 * M / k / Real.sqrt x) := by
        exact mul_le_mul_of_nonneg_left hsplit (by norm_num)
    _ = 2 * M / k / Real.sqrt x := by ring

theorem abs_channelBranchAmpDeriv_le {s c k eps x a : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 1 ≤ c) (hk : 1 ≤ k) (hx : 2 ≤ x) (heps : |eps| = 1) (ha : 0 < a)
    (hau : a ≤ c * xiEndpointPhase s (k * x)) :
    ‖channelBranchAmpDeriv s c k eps x‖
      ≤ 37 * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) / k
        / (x * Real.sqrt x) := by
  obtain ⟨hA, hB⟩ := abs_besselCoeff_le_base ha hau
  obtain ⟨hA', hB'⟩ := abs_deriv_besselCoeff_le_base ha hau
  set M : ℝ := Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) with hMdef
  have hM : (0 : ℝ) ≤ M := Real.sqrt_nonneg _
  have hcos := abs_branchAmpDeriv_le (A := besselCosCoeff) (A' := besselCosCoeffDeriv)
    hs0 hs1 hc hk hx hM hA hA'
  have hsin := abs_branchAmpDeriv_le (A := besselSinCoeff) (A' := besselSinCoeffDeriv)
    hs0 hs1 hc hk hx hM hB hB'
  rw [channelBranchAmpDeriv, norm_mul]
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hhalf]
  have hsplit : ‖((branchAmpDeriv s c k besselCosCoeff besselCosCoeffDeriv x : ℝ) : ℂ)
      - (eps : ℂ) * Complex.I
        * ((branchAmpDeriv s c k besselSinCoeff besselSinCoeffDeriv x : ℝ) : ℂ)‖
      ≤ 37 * M / k / (x * Real.sqrt x) + 37 * M / k / (x * Real.sqrt x) := by
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖((branchAmpDeriv s c k besselCosCoeff besselCosCoeffDeriv x : ℝ) : ℂ)‖
        ≤ 37 * M / k / (x * Real.sqrt x) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hcos
    have h2 : ‖(eps : ℂ) * Complex.I
        * ((branchAmpDeriv s c k besselSinCoeff besselSinCoeffDeriv x : ℝ) : ℂ)‖
        ≤ 37 * M / k / (x * Real.sqrt x) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, Complex.norm_I, heps, one_mul, one_mul]
      exact hsin
    linarith
  calc 1 / 2 * ‖((branchAmpDeriv s c k besselCosCoeff besselCosCoeffDeriv x : ℝ) : ℂ)
        - (eps : ℂ) * Complex.I
          * ((branchAmpDeriv s c k besselSinCoeff besselSinCoeffDeriv x : ℝ) : ℂ)‖
      ≤ 1 / 2 * (37 * M / k / (x * Real.sqrt x) + 37 * M / k / (x * Real.sqrt x)) :=
        mul_le_mul_of_nonneg_left hsplit (by norm_num)
    _ = 37 * M / k / (x * Real.sqrt x) := by ring

/-- **Euler's identity in two-branch form.**  A real cosine/sine combination is a sum of two
complex exponential branches with conjugate amplitudes. -/
theorem two_branch_euler (P Q u : ℝ) :
    ((P * Real.cos u + Q * Real.sin u : ℝ) : ℂ)
      = (1 / 2 : ℂ) * ((P : ℂ) - (1 : ℂ) * Complex.I * (Q : ℂ))
          * Complex.exp (Complex.I * ((u : ℝ) : ℂ))
        + (1 / 2 : ℂ) * ((P : ℂ) - (-1 : ℂ) * Complex.I * (Q : ℂ))
          * Complex.exp (Complex.I * ((-u : ℝ) : ℂ)) := by
  have h1 : Complex.I * ((u : ℝ) : ℂ) = ((u : ℝ) : ℂ) * Complex.I := mul_comm _ _
  have h2 : Complex.I * ((-u : ℝ) : ℂ) = ((-u : ℝ) : ℂ) * Complex.I := mul_comm _ _
  rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The exact two-branch decomposition of the dilated profile.**  No approximation: the
coefficients are exact and the identity is Euler's. -/
theorem sqrt_mul_radialProlateBesselProfile_eq_branches {s c k x : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 1 ≤ k) (hx : 2 ≤ x) :
    ((Real.sqrt x * radialProlateBesselProfile s c (k * x) : ℝ) : ℂ)
      = channelBranchAmp s c k 1 x
          * Complex.exp (Complex.I * ((1 * (c * k) * dilatedPhase s k x : ℝ) : ℂ))
        + channelBranchAmp s c k (-1) x
          * Complex.exp (Complex.I * ((-1 * (c * k) * dilatedPhase s k x : ℝ) : ℂ)) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hkx : (1 : ℝ) < k * x := by nlinarith [hk, hx]
  have hphase : (1 : ℝ) * (c * k) * dilatedPhase s k x = c * xiEndpointPhase s (k * x) := by
    rw [dilatedPhase]
    field_simp
  have hphase' : (-1 : ℝ) * (c * k) * dilatedPhase s k x
      = -(c * xiEndpointPhase s (k * x)) := by
    rw [dilatedPhase]
    field_simp
  rw [hphase, hphase', radialProlateBesselProfile_eq_twoBranch hs0 hs1 hc hkx]
  have hval : Real.sqrt x * (ampFourth s (k * x)
      * (besselCosCoeff (c * xiEndpointPhase s (k * x))
          * Real.cos (c * xiEndpointPhase s (k * x))
        + besselSinCoeff (c * xiEndpointPhase s (k * x))
          * Real.sin (c * xiEndpointPhase s (k * x))))
      = branchAmp s c k besselCosCoeff x * Real.cos (c * xiEndpointPhase s (k * x))
        + branchAmp s c k besselSinCoeff x * Real.sin (c * xiEndpointPhase s (k * x)) := by
    rw [branchAmp, branchAmp, branchAmplitude, branchAmplitude]
    ring
  rw [hval, two_branch_euler]
  rw [channelBranchAmp, channelBranchAmp]
  push_cast
  ring

theorem continuousOn_channelBranchAmp {s c k eps X : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hk : 1 ≤ k) (hX : 2 ≤ X) :
    ContinuousOn (channelBranchAmp s c k eps) (Set.uIcc (2 : ℝ) X) := by
  intro x hx
  rw [Set.uIcc_of_le hX] at hx
  exact ((hasDerivAt_channelBranchAmp hs0 hs1 hc hk hx.1).continuousAt).continuousWithinAt

theorem continuousOn_dilatedPhase {s k X : ℝ} (hs0 : 0 ≤ s) (hk : 1 ≤ k) (hX : 2 ≤ X) :
    ContinuousOn (dilatedPhase s k) (Set.uIcc (2 : ℝ) X) := by
  intro x hx
  rw [Set.uIcc_of_le hX] at hx
  have hkx : (1 : ℝ) < k * x := by nlinarith [hk, hx.1]
  exact ((hasDerivAt_dilatedPhase hs0 hk hkx).continuousAt).continuousWithinAt

theorem continuousOn_branchIntegrand {s c k eps X : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hk : 1 ≤ k) (hX : 2 ≤ X) :
    ContinuousOn (fun t : ℝ => (channelBranchAmp s c k eps t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
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
  exact ((continuousOn_channelBranchAmp hs0 hs1 hc hk hX).mul hinv).mul hexp

/-- The dilated profile written as the two exponential branches, in the exact form the exterior
estimate consumes. -/
theorem profile_eq_branch_integrand {s c k t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hk : 1 ≤ k) (ht : 2 ≤ t) :
    ((radialProlateBesselProfile s c (k * t) : ℝ) : ℂ)
      = (channelBranchAmp s c k 1 t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
          * Complex.exp (Complex.I * ((1 * (c * k) * dilatedPhase s k t : ℝ) : ℂ))
        + (channelBranchAmp s c k (-1) t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
          * Complex.exp (Complex.I * ((-1 * (c * k) * dilatedPhase s k t : ℝ) : ℂ)) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hst : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hne : ((Real.sqrt t : ℝ) : ℂ) ≠ 0 := by
    simpa using (ne_of_gt hst)
  have hid := sqrt_mul_radialProlateBesselProfile_eq_branches hs0 hs1 hc hk ht
  have hmul : ((Real.sqrt t : ℝ) : ℂ) * ((radialProlateBesselProfile s c (k * t) : ℝ) : ℂ)
      = channelBranchAmp s c k 1 t
          * Complex.exp (Complex.I * ((1 * (c * k) * dilatedPhase s k t : ℝ) : ℂ))
        + channelBranchAmp s c k (-1) t
          * Complex.exp (Complex.I * ((-1 * (c * k) * dilatedPhase s k t : ℝ) : ℂ)) := by
    rw [← hid]
    push_cast
    ring
  have hinv : (((Real.sqrt t)⁻¹ : ℝ) : ℂ) = (((Real.sqrt t : ℝ) : ℂ))⁻¹ := by push_cast; ring
  rw [hinv]
  have hsplit : ((radialProlateBesselProfile s c (k * t) : ℝ) : ℂ)
      = (((Real.sqrt t : ℝ) : ℂ))⁻¹ * (((Real.sqrt t : ℝ) : ℂ)
        * ((radialProlateBesselProfile s c (k * t) : ℝ) : ℂ)) := by
    field_simp
  rw [hsplit, hmul]
  ring

/-- **The `k`-th channel primitive of the dilated Bessel profile is `O(1/(c k²))`,** uniformly in
the endpoint of integration and with a constant free of `k`.  This is the card's `(16)` for the
full profile: both branches of the exact two-branch representation, not a leading term. -/
theorem norm_integral_dilated_profile_le {s c k X : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 1 ≤ c) (hk : 1 ≤ k) (hX : 2 ≤ X) :
    ‖∫ t in (2 : ℝ)..X, ((radialProlateBesselProfile s c (k * t) : ℝ) : ℂ)‖
      ≤ 222 * channelEnergyConstant s c / (c * k ^ 2) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hbpos : 0 < channelBase s c k := channelBase_pos hs0 hs1 hc0 hk
  set M : ℝ := Real.sqrt (besselEnergy (channelBase s c k)
    * Real.exp (1 / (4 * channelBase s c k))) with hMdef
  have hM : (0 : ℝ) ≤ M := Real.sqrt_nonneg _
  have hCa : (0 : ℝ) ≤ 37 * M / k := by positivity
  have hx2 : ∀ x ∈ Set.uIcc (2 : ℝ) X, (2 : ℝ) ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hX] at hx
    exact hx.1
  -- each exponential branch obeys the exterior estimate with the same amplitude constant
  have hbranch : ∀ eps : ℝ, |eps| = 1 →
      ‖∫ t in (2 : ℝ)..X, (channelBranchAmp s c k eps t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
          * Complex.exp (Complex.I * ((eps * (c * k) * dilatedPhase s k t : ℝ) : ℂ))‖
        ≤ 3 * (37 * M / k) / (c * k) := by
    intro eps heps
    refine norm_integral_exterior_dilated_sharp_le (Ca := 37 * M / k)
      (a := channelBranchAmp s c k eps) (a' := channelBranchAmpDeriv s c k eps)
      hX hCa hc0 hk heps hs0 hs1
      (fun x hx => hasDerivAt_channelBranchAmp hs0 hs1 hc0 hk (hx2 x hx))
      (continuousOn_channelBranchAmp hs0 hs1 hc0 hk hX)
      (continuousOn_channelBranchAmpDeriv hs0 hs1 hc0 hk hX)
      (fun x hx => ?_) (fun x hx => ?_)
    · have h := abs_channelBranchAmp_le hs0 hs1 hk (hx2 x hx) heps hbpos
        (channelBase_le hs0 hs1 hc0 hk (hx2 x hx))
      rw [← hMdef] at h
      refine le_trans h ?_
      have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr (by linarith [hx2 x hx])
      rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg hM hk0.le) hsx.le]
    · have h := abs_channelBranchAmpDeriv_le hs0 hs1 hc hk (hx2 x hx) heps hbpos
        (channelBase_le hs0 hs1 hc0 hk (hx2 x hx))
      rw [← hMdef] at h
      exact h
  -- the profile is the sum of the two branches
  have hcongr : (∫ t in (2 : ℝ)..X, ((radialProlateBesselProfile s c (k * t) : ℝ) : ℂ))
      = (∫ t in (2 : ℝ)..X, (channelBranchAmp s c k 1 t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
            * Complex.exp (Complex.I * ((1 * (c * k) * dilatedPhase s k t : ℝ) : ℂ)))
        + ∫ t in (2 : ℝ)..X, (channelBranchAmp s c k (-1) t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
            * Complex.exp (Complex.I * ((-1 * (c * k) * dilatedPhase s k t : ℝ) : ℂ)) := by
    rw [← intervalIntegral.integral_add
      ((continuousOn_branchIntegrand hs0 hs1 hc0 hk hX).intervalIntegrable)
      ((continuousOn_branchIntegrand hs0 hs1 hc0 hk hX).intervalIntegrable)]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    exact profile_eq_branch_integrand hs0 hs1 hc0 hk (hx2 x hx)
  rw [hcongr]
  refine le_trans (norm_add_le _ _) ?_
  have h1 := hbranch 1 (by norm_num)
  have h2 := hbranch (-1) (by norm_num)
  have hsum : 3 * (37 * M / k) / (c * k) + 3 * (37 * M / k) / (c * k)
      = 222 * M / (c * k ^ 2) := by
    field_simp
    ring
  have hEle : M ≤ channelEnergyConstant s c := channelEnergy_le hs0 hs1 hc0 hk
  have hden : (0 : ℝ) < c * k ^ 2 := by positivity
  have hfin : 222 * M / (c * k ^ 2) ≤ 222 * channelEnergyConstant s c / (c * k ^ 2) := by
    gcongr
  linarith [h1, h2, hsum, hfin]

end GaloisForLFunctions.RHTower
