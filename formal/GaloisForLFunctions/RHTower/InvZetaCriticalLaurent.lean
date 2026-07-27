import GaloisForLFunctions.RHTower.SquarefreePartitionPole

/-!
# The critical Laurent behaviour of the reciprocal zeta factor

The reciprocal factor of the coupled causal multiplier is `r(ω) = 1/ζ(1+2ω)`.  The simple pole of
`ζ` at `1` makes it vanish linearly:

```text
r(ω)/ω → 2       (ω → 0+),
```

which is the first Laurent coefficient used when the causal multiplier is differentiated at the
critical parameter.
-/

open Filter Topology

namespace RHTower

noncomputable section

theorem tendsto_two_mul_riemannZeta_one_add_two_mul :
    Tendsto (fun ω : ℝ => (2 * (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
  have hmap : Tendsto (fun ω : ℝ => 1 + 2 * (ω : ℂ)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
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
  have hcomp := riemannZeta_residue_one.comp hmap
  refine hcomp.congr fun ω => ?_
  simp only [Function.comp_apply]
  ring_nf

/-- **The reciprocal zeta factor vanishes linearly at the critical parameter.** -/
theorem tendsto_inv_riemannZeta_one_add_two_mul_div :
    Tendsto (fun ω : ℝ => (riemannZeta (1 + 2 * (ω : ℂ)))⁻¹ / (ω : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 2) := by
  have hbase := tendsto_two_mul_riemannZeta_one_add_two_mul
  have hinv := hbase.inv₀ (by norm_num)
  rw [inv_one] at hinv
  have hmul := hinv.const_mul (2 : ℂ)
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ω hω
  have hωpos : (0 : ℝ) < ω := hω
  have hωne : ((ω : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hωpos
  have hζ : riemannZeta (1 + 2 * (ω : ℂ)) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero]
    linarith
  field_simp

end

end RHTower
