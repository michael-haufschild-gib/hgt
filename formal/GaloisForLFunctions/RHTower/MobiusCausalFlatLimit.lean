import GaloisForLFunctions.RHTower.ZetaDerivResidue

/-!
# The critical (flat) limit of the parameter derivative

Letting `ω → 0+` in the parameter derivative of the coupled causal multiplier, the two
`ζ`-pole contributions of the subtracted term collapse to a single `-2/z`:

```text
∂_ω M_ω(z) → -1/(1+z)² - 2 ζ'(1+z)/[(1+z) ζ(1+z)] - 2/z      (ω → 0+),
```

which is the card's `(4)`.  The `-2/z` is exactly the `(s-1)²ζ'(s) → -1` derivative residue
of `RHTower.tendsto_sub_one_sq_mul_deriv_riemannZeta` beating against the simple pole
`(s-1)ζ(s) → 1`.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The critical parameter direction along which the multiplier is differentiated. -/
theorem tendsto_one_add_two_mul_ne :
    Tendsto (fun ω : ℝ => (1 : ℂ) + 2 * (ω : ℂ)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hc : Continuous fun ω : ℝ => 1 + 2 * (ω : ℂ) := by fun_prop
    have h0 : (1 : ℂ) + 2 * ((0 : ℝ) : ℂ) = 1 := by push_cast; ring
    have h := hc.tendsto (0 : ℝ)
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ω hω
    have hωpos : (0 : ℝ) < ω := hω
    intro hmem
    rw [Set.mem_singleton_iff] at hmem
    have hre : ((1 : ℂ) + 2 * (ω : ℂ)).re = 1 := by rw [hmem]; simp
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero] at hre
    linarith

/-- The derivative residue in the critical parameter. -/
theorem tendsto_sq_mul_deriv_riemannZeta_one_add_two_mul :
    Tendsto (fun ω : ℝ => (2 * (ω : ℂ)) ^ (2 : ℕ) * deriv riemannZeta (1 + 2 * (ω : ℂ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (-1)) := by
  have h := tendsto_sub_one_sq_mul_deriv_riemannZeta.comp tendsto_one_add_two_mul_ne
  refine h.congr fun ω => ?_
  simp only [Function.comp_apply]
  ring_nf

/-- **The pole factor of the subtracted term tends to `-2`.** -/
theorem tendsto_mobiusCausalPoleFactor :
    Tendsto (fun ω : ℝ => (riemannZeta (1 + 2 * (ω : ℂ)) +
        2 * (1 + (ω : ℂ)) * deriv riemannZeta (1 + 2 * (ω : ℂ))) /
      ((1 + (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ))) ^ (2 : ℕ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (-2)) := by
  have hP := tendsto_two_mul_riemannZeta_one_add_two_mul
  have hQ := tendsto_sq_mul_deriv_riemannZeta_one_add_two_mul
  have hω : Tendsto (fun ω : ℝ => ((ω : ℝ) : ℂ)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hc : Continuous fun ω : ℝ => ((ω : ℝ) : ℂ) := Complex.continuous_ofReal
    have h := hc.tendsto (0 : ℝ)
    rw [Complex.ofReal_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlin : Tendsto (fun ω : ℝ => (1 : ℂ) + (ω : ℂ)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds 1) := by
    have := (tendsto_const_nhds (x := (1 : ℂ)) (f := nhdsWithin (0 : ℝ) (Set.Ioi 0))).add hω
    simpa using this
  have hnum : Tendsto (fun ω : ℝ => (2 * (ω : ℂ)) * ((2 * (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ)))
      + 2 * (1 + (ω : ℂ)) * ((2 * (ω : ℂ)) ^ (2 : ℕ) * deriv riemannZeta (1 + 2 * (ω : ℂ))))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (-2)) := by
    have h2ω : Tendsto (fun ω : ℝ => 2 * ((ω : ℝ) : ℂ)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds 0) := by simpa using hω.const_mul (2 : ℂ)
    have ha := h2ω.mul hP
    have hb := ((tendsto_const_nhds (x := (2 : ℂ))
      (f := nhdsWithin (0 : ℝ) (Set.Ioi 0))).mul hlin).mul hQ
    have := ha.add hb
    simpa using this
  have hden : Tendsto (fun ω : ℝ => (1 + (ω : ℂ)) ^ (2 : ℕ) *
      ((2 * (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ))) ^ (2 : ℕ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
    have := (hlin.pow 2).mul (hP.pow 2)
    simpa using this
  have hdiv := hnum.div hden (by norm_num)
  rw [show ((-2 : ℂ) / 1) = -2 by norm_num] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ω hω0
  have hωpos : (0 : ℝ) < ω := hω0
  have hωne : ((ω : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hωpos
  have hζ : riemannZeta (1 + 2 * (ω : ℂ)) ≠ 0 := riemannZeta_one_add_two_mul_ne_zero hωpos
  have hω1 : (1 : ℂ) + (ω : ℂ) ≠ 0 := by
    intro h
    have hre : ((1 : ℂ) + (ω : ℂ)).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re] at hre
    linarith
  simp only [Pi.div_apply]
  field_simp

/-- The card's `(4)`: the flat (critical) parameter derivative. -/
def mobiusCausalFlatDeriv (z : ℂ) : ℂ :=
  -(1 / (1 + z) ^ (2 : ℕ)) - 2 * deriv riemannZeta (1 + z) / ((1 + z) * riemannZeta (1 + z)) - 2 / z

theorem one_add_ne_one {z : ℂ} (hz0 : z ≠ 0) : (1 : ℂ) + z ≠ 1 := by
  intro h
  exact hz0 (by linear_combination h)

theorem one_add_ne_zero {z : ℂ} (hz : 0 ≤ z.re) : (1 : ℂ) + z ≠ 0 := by
  intro h
  have hre : ((1 : ℂ) + z).re = 0 := by rw [h]; simp
  simp only [Complex.add_re, Complex.one_re] at hre
  linarith

theorem riemannZeta_one_add_ne_zero {z : ℂ} (hz : 0 ≤ z.re) : riemannZeta (1 + z) ≠ 0 := by
  refine riemannZeta_ne_zero_of_one_le_re ?_
  simp only [Complex.add_re, Complex.one_re]
  linarith

/-- **The card's `(4)`.**  The parameter derivative of the coupled causal multiplier converges,
as `ω → 0+`, to the flat derivative; the two `ζ`-pole contributions collapse to `-2/z`. -/
theorem tendsto_mobiusCausalMultiplierDeriv {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    Tendsto (fun ω : ℝ => mobiusCausalMultiplierDeriv ω z) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (mobiusCausalFlatDeriv z)) := by
  have h1z : (1 : ℂ) + z ≠ 1 := one_add_ne_one hz0
  have h1z0 : (1 : ℂ) + z ≠ 0 := one_add_ne_zero hz
  have hζ0 : riemannZeta (1 + z) ≠ 0 := riemannZeta_one_add_ne_zero hz
  have hdiffOn : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ : Set ℂ) := by
    intro s hs
    exact (differentiableAt_riemannZeta (by simpa using hs)).differentiableWithinAt
  have hana : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ : Set ℂ) :=
    hdiffOn.analyticOnNhd isOpen_compl_singleton
  have hmem : (1 : ℂ) + z ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using h1z
  have hζcont : ContinuousAt riemannZeta (1 + z) :=
    (differentiableAt_riemannZeta h1z).continuousAt
  have hζ'cont : ContinuousAt (deriv riemannZeta) (1 + z) := (hana _ hmem).deriv.continuousAt
  have hshift : Tendsto (fun ω : ℝ => (1 : ℂ) + 2 * (ω : ℂ) + z)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 + z)) := by
    have hc : Continuous fun ω : ℝ => (1 : ℂ) + 2 * (ω : ℂ) + z := by fun_prop
    have h0 : (1 : ℂ) + 2 * ((0 : ℝ) : ℂ) + z = 1 + z := by push_cast; ring
    have h := hc.tendsto (0 : ℝ)
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlin : Tendsto (fun ω : ℝ => (1 : ℂ) + (ω : ℂ) + z)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 + z)) := by
    have hc : Continuous fun ω : ℝ => (1 : ℂ) + (ω : ℂ) + z := by fun_prop
    have h0 : (1 : ℂ) + ((0 : ℝ) : ℂ) + z = 1 + z := by push_cast; ring
    have h := hc.tendsto (0 : ℝ)
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hζs : Tendsto (fun ω : ℝ => riemannZeta (1 + 2 * (ω : ℂ) + z))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (riemannZeta (1 + z))) := hζcont.tendsto.comp hshift
  have hζ's : Tendsto (fun ω : ℝ => deriv riemannZeta (1 + 2 * (ω : ℂ) + z))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (deriv riemannZeta (1 + z))) :=
    hζ'cont.tendsto.comp hshift
  have hprodne : (1 + z) * riemannZeta (1 + z) ≠ 0 := mul_ne_zero h1z0 hζ0
  have hA : Tendsto (fun ω : ℝ =>
      riemannZeta (1 + z) / ((1 + (ω : ℂ) + z) * riemannZeta (1 + 2 * (ω : ℂ) + z)) *
        (-(1 / (1 + (ω : ℂ) + z)) -
          2 * deriv riemannZeta (1 + 2 * (ω : ℂ) + z) / riemannZeta (1 + 2 * (ω : ℂ) + z)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (riemannZeta (1 + z) / ((1 + z) * riemannZeta (1 + z)) *
        (-(1 / (1 + z)) - 2 * deriv riemannZeta (1 + z) / riemannZeta (1 + z)))) :=
    (tendsto_const_nhds.div (hlin.mul hζs) hprodne).mul
      (((tendsto_const_nhds.div hlin h1z0).neg).sub
        ((tendsto_const_nhds.mul hζ's).div hζs hζ0))
  have hB : Tendsto (fun ω : ℝ => 1 / z * ((riemannZeta (1 + 2 * (ω : ℂ)) +
        2 * (1 + (ω : ℂ)) * deriv riemannZeta (1 + 2 * (ω : ℂ))) /
      ((1 + (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ))) ^ (2 : ℕ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 / z * (-2))) :=
    tendsto_const_nhds.mul tendsto_mobiusCausalPoleFactor
  have hsum := hA.add hB
  have hval : riemannZeta (1 + z) / ((1 + z) * riemannZeta (1 + z)) *
      (-(1 / (1 + z)) - 2 * deriv riemannZeta (1 + z) / riemannZeta (1 + z)) + 1 / z * (-2)
      = mobiusCausalFlatDeriv z := by
    rw [mobiusCausalFlatDeriv]
    field_simp
    ring
  rw [hval] at hsum
  exact hsum

end

end RHTower
