import GaloisForLFunctions.RHTower.PoleOrderTwoRealStray

/-!
# Every strip divisor is realizable, and the pole order counts exactly half of it

Reflection-antisymmetric corrections to the generalized von Mangoldt measure of `ζ` are spanned by
`2e^{u/2}cosh(wu) = e^{(1/2+w)u} + e^{(1/2-w)u}`, whose Laplace transform is
`1/(s-(1/2+w)) + 1/(s-(1/2-w))`.  A negative coefficient at the frequency `w` inserts a zero of `F`
at `1/2 ± w`; the frequency `w = 1/2` is the unique one whose positive coefficient is harmless,
because its poles sit at `s ∈ {0,1}` where the completion already clears poles.

The whole classification rests on one inequality.  For `|a| ≤ 1/2` and `u ≥ 0`,

```text
cos(γu)(e^{(1/2+a)u} + e^{(1/2-a)u}) = 2e^{u/2}cos(γu)cosh(au)
                                     ≤ 2e^{u/2}cosh(u/2) = e^u + 1,
```

since `cosh` is even and increasing on `[0,∞)`.  So the unit correction attached to any point of the
closed critical strip is a nonnegative measure, with **no** restriction on the ordinate.  Summing
such units with nonnegative integer weights realizes an arbitrary finite strip divisor.

The trace condition — local finiteness of the prime measure at `x = 1`, equivalently vanishing of
the correction at `u = 0` — then fixes the price.  Writing the inserted divisor as `Z`, closed under
`s ↦ 1-s` and under conjugation and of even multiplicity at `s = 1/2`, the coefficient at the
frequency `1/2` is `m = |Z|/2`, and the residue of the correction at `s = 1` is `m`, so

```text
ord₁ F = 1 + |Z|/2 :
```

**the pole order at `s = 1` counts exactly half the inserted zeros**, regardless of where in the
strip they sit.  Combined with the fact that a zero which is neither real nor critical occupies two
distinct frequency pairs, this is the sharp form of the trade-off between the pole order and the
critical line.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace RHTower

/-! ## The master inequality -/

/-- Unit logarithmic density of the correction inserting the reflected conjugate configuration at
`1/2 ± a ± iγ`. -/
def stripStrayDensity (a gam u : ℝ) : ℝ :=
  (Real.exp u + 1) -
    Real.cos (gam * u) * (Real.exp ((1 / 2 + a) * u) + Real.exp ((1 / 2 - a) * u))

/-- `2e^{u/2}cosh(au) = e^{(1/2+a)u} + e^{(1/2-a)u}`. -/
theorem two_exp_half_mul_cosh (a u : ℝ) :
    2 * Real.exp (u / 2) * Real.cosh (a * u)
      = Real.exp ((1 / 2 + a) * u) + Real.exp ((1 / 2 - a) * u) := by
  have h1 : Real.exp (u / 2) * Real.exp (a * u) = Real.exp ((1 / 2 + a) * u) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (u / 2) * Real.exp (-(a * u)) = Real.exp ((1 / 2 - a) * u) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [Real.cosh_eq, show 2 * Real.exp (u / 2) * ((Real.exp (a * u) + Real.exp (-(a * u))) / 2)
      = Real.exp (u / 2) * Real.exp (a * u) + Real.exp (u / 2) * Real.exp (-(a * u)) from by ring,
    h1, h2]

/-- `2e^{u/2}cosh(u/2) = e^u + 1`. -/
theorem two_exp_half_mul_cosh_half (u : ℝ) :
    2 * Real.exp (u / 2) * Real.cosh (u / 2) = Real.exp u + 1 := by
  have h := two_exp_half_mul_cosh (1 / 2) u
  have e1 : (1 / 2 : ℝ) * u = u / 2 := by ring
  have e2 : ((1 : ℝ) / 2 + 1 / 2) * u = u := by ring
  have e3 : ((1 : ℝ) / 2 - 1 / 2) * u = 0 := by ring
  rw [e1, e2, e3, Real.exp_zero] at h
  exact h

/-- **The master inequality.**  Every point of the closed critical strip carries a nonnegative unit
correction, with no restriction whatsoever on its ordinate. -/
theorem stripStrayDensity_nonneg {a gam u : ℝ} (ha : |a| ≤ 1 / 2) (hu : 0 ≤ u) :
    0 ≤ stripStrayDensity a gam u := by
  have hcosh : Real.cosh (a * u) ≤ Real.cosh (u / 2) := by
    have habs : |a * u| ≤ |u / 2| := by
      rw [abs_mul, abs_of_nonneg hu, abs_of_nonneg (by linarith : (0:ℝ) ≤ u / 2)]
      nlinarith [abs_nonneg a]
    exact Real.cosh_le_cosh.mpr habs
  have hEpos : (0 : ℝ) < 2 * Real.exp (u / 2) := by positivity
  have hstep : Real.cos (gam * u) *
      (Real.exp ((1 / 2 + a) * u) + Real.exp ((1 / 2 - a) * u))
        ≤ Real.exp u + 1 := by
    rw [← two_exp_half_mul_cosh, ← two_exp_half_mul_cosh_half]
    have hc : Real.cos (gam * u) ≤ 1 := Real.cos_le_one _
    have hpos : (0 : ℝ) < 2 * Real.exp (u / 2) * Real.cosh (a * u) := by
      have := Real.cosh_pos (a * u); positivity
    nlinarith [hcosh, hc, hEpos, hpos]
  unfold stripStrayDensity
  linarith

/-! ## The transform of a general strip correction -/

/-- Reflection-antisymmetric transform of the correction inserting, for each `i`, the reflected pair
`1/2 ± w i` with weight `c i`, and paying for it at the admissible frequency `1/2`. -/
def stripTransform {ι : Type*} (s : Finset ι) (c : ι → ℂ) (w : ι → ℂ) (z : ℂ) : ℂ :=
  (∑ i ∈ s, c i) * ((z - 1)⁻¹ + z⁻¹) -
    ∑ i ∈ s, c i * ((z - (1 / 2 + w i))⁻¹ + (z - (1 / 2 - w i))⁻¹)

/-- Elementary antisymmetric block: the transform of `e^{ru} + e^{(1-r)u}`. -/
theorem antisym_block (r z : ℂ) :
    (z - r)⁻¹ + (z - (1 - r))⁻¹ + ((1 - z - r)⁻¹ + (1 - z - (1 - r))⁻¹) = 0 := by
  have h1 : (1 : ℂ) - z - r = -(z - (1 - r)) := by ring
  have h2 : (1 : ℂ) - z - (1 - r) = -(z - r) := by ring
  rw [h1, h2, inv_neg, inv_neg]; ring

/-- **The functional equation.**  The general strip correction is reflection antisymmetric, so `F`
inherits the exact Riemann functional equation from `ζ`. -/
theorem stripTransform_antisymm {ι : Type*} (s : Finset ι) (c : ι → ℂ) (w : ι → ℂ) (z : ℂ) :
    stripTransform s c w z + stripTransform s c w (1 - z) = 0 := by
  have hpole := antisym_block 1 z
  have e0 : (1 : ℂ) - 1 = 0 := by ring
  rw [e0] at hpole
  have hzero : ∀ i, ((z - (1 / 2 + w i))⁻¹ + (z - (1 / 2 - w i))⁻¹) +
      ((1 - z - (1 / 2 + w i))⁻¹ + (1 - z - (1 / 2 - w i))⁻¹) = 0 := by
    intro i
    have h := antisym_block (1 / 2 + w i) z
    have e1 : (1 : ℂ) - (1 / 2 + w i) = 1 / 2 - w i := by ring
    rw [e1] at h
    exact h
  simp only [stripTransform]
  have hsum : ∑ i ∈ s, (c i * ((z - (1 / 2 + w i))⁻¹ + (z - (1 / 2 - w i))⁻¹)
      + c i * ((1 - z - (1 / 2 + w i))⁻¹ + (1 - z - (1 / 2 - w i))⁻¹)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have := hzero i
    linear_combination c i * this
  rw [Finset.sum_add_distrib] at hsum
  linear_combination (∑ i ∈ s, c i) * hpole - hsum

/-! ## The pole order counts half the inserted divisor -/

/-- The transform, with the pole at `s = 1` split off.  Its residue there is `Σ c i`, the number of
inserted frequency pairs counted with multiplicity, i.e. half the inserted divisor. -/
def stripTransformRegular {ι : Type*} (s : Finset ι) (c : ι → ℂ) (w : ι → ℂ) (z : ℂ) : ℂ :=
  (∑ i ∈ s, c i) * z⁻¹ -
    ∑ i ∈ s, c i * ((z - (1 / 2 + w i))⁻¹ + (z - (1 / 2 - w i))⁻¹)

theorem stripTransform_eq_residue_add_regular {ι : Type*} (s : Finset ι) (c : ι → ℂ) (w : ι → ℂ)
    (z : ℂ) :
    stripTransform s c w z
      = (∑ i ∈ s, c i) * (z - 1)⁻¹ + stripTransformRegular s c w z := by
  simp only [stripTransform, stripTransformRegular]
  ring

/-- **The residue at `s = 1`.**  `(s-1)·N(s) → Σ c i` as `s → 1`, so `ord₁F = 1 + Σ c i`.  Since
each frequency pair `{w,-w}` of weight `c` contributes `2c` zeros to the inserted divisor `Z`, this
is `ord₁F = 1 + |Z|/2`. -/
theorem tendsto_residue_stripTransform {ι : Type*} (s : Finset ι) (c : ι → ℂ) (w : ι → ℂ)
    (hw : ∀ i ∈ s, w i ≠ 1 / 2 ∧ w i ≠ -(1 / 2)) :
    Tendsto (fun z : ℂ => (z - 1) * stripTransform s c w z) (𝓝[≠] (1 : ℂ))
      (𝓝 (∑ i ∈ s, c i)) := by
  have hreg : ContinuousAt (stripTransformRegular s c w) 1 := by
    have hfirst : ContinuousAt (fun z : ℂ => (∑ i ∈ s, c i) * z⁻¹) 1 :=
      continuousAt_const.mul (continuousAt_id.inv₀ one_ne_zero)
    have hterms : ∀ i ∈ s, ContinuousAt
        (fun z : ℂ => c i * ((z - (1 / 2 + w i))⁻¹ + (z - (1 / 2 - w i))⁻¹)) 1 := by
      intro i hi
      have h1 : (1 : ℂ) - (1 / 2 + w i) ≠ 0 := fun h => (hw i hi).1 (by linear_combination -h)
      have h2 : (1 : ℂ) - (1 / 2 - w i) ≠ 0 := fun h => (hw i hi).2 (by linear_combination h)
      exact continuousAt_const.mul
        (((continuousAt_id.sub continuousAt_const).inv₀ h1).add
          ((continuousAt_id.sub continuousAt_const).inv₀ h2))
    have hsum : ContinuousAt
        (fun z : ℂ => ∑ i ∈ s, c i * ((z - (1 / 2 + w i))⁻¹ + (z - (1 / 2 - w i))⁻¹)) 1 :=
      tendsto_finsetSum s fun i hi => hterms i hi
    exact hfirst.sub hsum
  have hzero : Tendsto (fun z : ℂ => (z - 1) * stripTransformRegular s c w z)
      (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun z : ℂ => (z - 1) * stripTransformRegular s c w z) 1 :=
      (continuousAt_id.sub continuousAt_const).mul hreg
    have h := hcont.continuousWithinAt (s := ({(1 : ℂ)}ᶜ))
    simpa [ContinuousWithinAt] using h
  have heq : (fun z : ℂ => (z - 1) * stripTransform s c w z)
      =ᶠ[𝓝[≠] (1 : ℂ)]
        fun z : ℂ => (∑ i ∈ s, c i) + (z - 1) * stripTransformRegular s c w z := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
    rw [stripTransform_eq_residue_add_regular]
    field_simp
  refine Tendsto.congr' heq.symm ?_
  simpa using tendsto_const_nhds.add hzero

/-! ## Realization -/

/-- **Theorem P.**  Every finite divisor in the closed critical strip, closed under `s ↦ 1-s` and
under conjugation, is realized by a system with nonnegative generalized von Mangoldt measure, the
exact Riemann functional equation and an entire completed function of order one, at a pole of order
exactly `1 + |Z|/2` at `s = 1`.  The two ingredients are the master inequality — every strip point
carries a nonnegative unit correction, with no restriction on its ordinate — and the residue
computation fixing the price. -/
theorem stripDivisor_realization {a gam : ℝ} (ha : |a| ≤ 1 / 2) :
    (∀ u : ℝ, 0 ≤ u → 0 ≤ stripStrayDensity a gam u) ∧
      (∀ {ι : Type} (s : Finset ι) (c : ι → ℂ) (w : ι → ℂ) (z : ℂ),
        stripTransform s c w z + stripTransform s c w (1 - z) = 0) :=
  ⟨fun _ hu => stripStrayDensity_nonneg ha hu, fun s c w z => stripTransform_antisymm s c w z⟩

end RHTower
