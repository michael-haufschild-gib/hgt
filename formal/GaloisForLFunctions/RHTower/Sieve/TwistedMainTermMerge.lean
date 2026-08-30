import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The removable singularity of the twisted main term

The main term of the twisted second moment `∫ |ζ(1/2+it)|² (h/k)^{-it} dt` is built from a
shifted diagonal series together with its functional-equation reflection.  Writing
`h' = h/(h,k)`, `k' = k/(h,k)` and `c = h'k'`, the shifted pair is

```text
c^{-w/2} ζ(1+w) + X^{-w} c^{w/2} ζ(1-w),
```

with `X` the archimedean scale.  Each summand has a simple pole at `w = 0`; the two residues are
`+1` and `-1`, so the pair extends continuously across `w = 0`.  Its value there is

```text
log X - log c + 2γ  =  log (X (h,k)² / (hk)) + 2γ,
```

the logarithmic weight of the twisted second moment.  The pole cancellation is proved by
splitting off `w⁻¹` times the difference of the two exponential factors and recognizing the
remaining quotient as a difference quotient at `w = 0`.
-/

open Filter Topology Complex

namespace RHTower.Sieve

noncomputable section

/-- The shifted diagonal series together with its functional-equation reflection. -/
def bchbMergeCore (X c : ℝ) (w : ℂ) : ℂ :=
  (c : ℂ) ^ (-w / 2) * riemannZeta (1 + w)
    + (X : ℂ) ^ (-w) * ((c : ℂ) ^ (w / 2) * riemannZeta (1 - w))

/-- The polar part of the shifted pair: the difference of the two exponential factors. -/
def bchbMergeGap (X c : ℝ) (w : ℂ) : ℂ :=
  (c : ℂ) ^ (-w / 2) - (X : ℂ) ^ (-w) * (c : ℂ) ^ (w / 2)

/-- The regular part of the shifted pair, built from the pole-free completion `riemannZeta₀`. -/
def bchbMergeReg (X c : ℝ) (w : ℂ) : ℂ :=
  (c : ℂ) ^ (-w / 2) * riemannZeta₀ (1 + w)
    + (X : ℂ) ^ (-w) * ((c : ℂ) ^ (w / 2) * riemannZeta₀ (1 - w))

/-- Splitting the shifted pair into its polar and regular parts. -/
theorem bchbMergeCore_eq (X c : ℝ) {w : ℂ} (hw : w ≠ 0) :
    bchbMergeCore X c w = w⁻¹ * bchbMergeGap X c w + bchbMergeReg X c w := by
  have h1 : (1 : ℂ) + w ≠ 1 := by
    intro h
    exact hw (by linear_combination h)
  have h2 : (1 : ℂ) - w ≠ 1 := by
    intro h
    exact hw (by linear_combination -h)
  have e1 : (1 : ℂ) + w - 1 = w := by ring
  have e2 : (1 : ℂ) - w - 1 = -w := by ring
  rw [bchbMergeCore, bchbMergeGap, bchbMergeReg,
    riemannZeta_eq_inv_sub_add h1, riemannZeta_eq_inv_sub_add h2, e1, e2, inv_neg]
  field_simp
  ring

/-- The polar part vanishes at `w = 0`. -/
@[simp] theorem bchbMergeGap_zero (X c : ℝ) : bchbMergeGap X c 0 = 0 := by
  simp [bchbMergeGap]

/-- The derivative of the polar part at `w = 0` is the logarithmic weight `log X - log c`. -/
theorem hasDerivAt_bchbMergeGap {X c : ℝ} (hX : 0 < X) (hc : 0 < c) :
    HasDerivAt (bchbMergeGap X c) ((Real.log X - Real.log c : ℝ) : ℂ) 0 := by
  have hcne : ((c : ℂ)) ≠ 0 := by
    simpa using hc.ne'
  have hXne : ((X : ℂ)) ≠ 0 := by
    simpa using hX.ne'
  have hlogc : Complex.log (c : ℂ) = ((Real.log c : ℝ) : ℂ) := by
    rw [Complex.ofReal_log hc.le]
  have hlogX : Complex.log (X : ℂ) = ((Real.log X : ℝ) : ℂ) := by
    rw [Complex.ofReal_log hX.le]
  -- the three elementary exponential factors
  have hA : HasDerivAt (fun w : ℂ => -w / 2) (-1 / 2 : ℂ) 0 :=
    (hasDerivAt_neg (0 : ℂ)).div_const 2
  have hB : HasDerivAt (fun w : ℂ => -w) (-1 : ℂ) 0 := hasDerivAt_neg (0 : ℂ)
  have hC : HasDerivAt (fun w : ℂ => w / 2) ((1 : ℂ) / 2) 0 :=
    (hasDerivAt_id' (x := (0 : ℂ))).div_const 2
  have h1 : HasDerivAt (fun w : ℂ => (c : ℂ) ^ (-w / 2))
      (-(((Real.log c : ℝ) : ℂ) / 2)) 0 := by
    have h := hA.const_cpow (c := (c : ℂ)) (Or.inl hcne)
    rw [hlogc] at h
    refine h.congr_deriv ?_
    norm_num [div_eq_mul_inv]
  have h2 : HasDerivAt (fun w : ℂ => (X : ℂ) ^ (-w)) (-((Real.log X : ℝ) : ℂ)) 0 := by
    have h := hB.const_cpow (c := (X : ℂ)) (Or.inl hXne)
    rw [hlogX] at h
    refine h.congr_deriv ?_
    norm_num [div_eq_mul_inv]
  have h3 : HasDerivAt (fun w : ℂ => (c : ℂ) ^ (w / 2)) (((Real.log c : ℝ) : ℂ) / 2) 0 := by
    have h := hC.const_cpow (c := (c : ℂ)) (Or.inl hcne)
    rw [hlogc] at h
    refine h.congr_deriv ?_
    norm_num [div_eq_mul_inv]
  have h5 := h1.sub (h2.mul h3)
  simp only [Pi.sub_def, Pi.mul_def] at h5
  refine h5.congr_deriv ?_
  push_cast
  norm_num
  ring

/-- The polar part contributes exactly `log X - log c` in the limit. -/
theorem tendsto_bchbMergeGap_div {X c : ℝ} (hX : 0 < X) (hc : 0 < c) :
    Tendsto (fun w : ℂ => w⁻¹ * bchbMergeGap X c w) (𝓝[≠] 0)
      (𝓝 ((Real.log X - Real.log c : ℝ) : ℂ)) := by
  have h := hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_bchbMergeGap hX hc)
  refine h.congr ?_
  intro w
  simp [slope, bchbMergeGap_zero]

/-- The regular part is continuous at `w = 0` with value `2γ`. -/
theorem tendsto_bchbMergeReg {X c : ℝ} (hX : 0 < X) (hc : 0 < c) :
    Tendsto (bchbMergeReg X c) (𝓝 0)
      (𝓝 ((2 * Real.eulerMascheroniConstant : ℝ) : ℂ)) := by
  have hcne : ((c : ℂ)) ≠ 0 := by simpa using hc.ne'
  have hXne : ((X : ℂ)) ≠ 0 := by simpa using hX.ne'
  have hz : Continuous riemannZeta₀ := differentiable_riemannZeta₀.continuous
  have hcont : Continuous (bchbMergeReg X c) := by
    unfold bchbMergeReg
    have c1 : Continuous fun w : ℂ => (c : ℂ) ^ (-w / 2) :=
      Continuous.const_cpow (by fun_prop) (Or.inl hcne)
    have c2 : Continuous fun w : ℂ => (X : ℂ) ^ (-w) :=
      Continuous.const_cpow (by fun_prop) (Or.inl hXne)
    have c3 : Continuous fun w : ℂ => (c : ℂ) ^ (w / 2) :=
      Continuous.const_cpow (by fun_prop) (Or.inl hcne)
    exact (c1.mul (hz.comp (by fun_prop))).add
      (c2.mul (c3.mul (hz.comp (by fun_prop))))
  have hval : bchbMergeReg X c 0 = ((2 * Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    simp [bchbMergeReg]
    ring
  have h := hcont.tendsto 0
  rwa [hval] at h

/-- **The shifted pair has a removable singularity at `w = 0`.**  Its value there is the
logarithmic weight `log X - log c + 2γ`. -/
theorem tendsto_bchbMergeCore {X c : ℝ} (hX : 0 < X) (hc : 0 < c) :
    Tendsto (bchbMergeCore X c) (𝓝[≠] 0)
      (𝓝 ((Real.log X - Real.log c + 2 * Real.eulerMascheroniConstant : ℝ) : ℂ)) := by
  have hsum :
      Tendsto (fun w : ℂ => w⁻¹ * bchbMergeGap X c w + bchbMergeReg X c w) (𝓝[≠] 0)
        (𝓝 (((Real.log X - Real.log c : ℝ) : ℂ)
          + ((2 * Real.eulerMascheroniConstant : ℝ) : ℂ))) :=
    (tendsto_bchbMergeGap_div hX hc).add
      ((tendsto_bchbMergeReg hX hc).mono_left nhdsWithin_le_nhds)
  have heq : ∀ᶠ w : ℂ in 𝓝[≠] 0,
      w⁻¹ * bchbMergeGap X c w + bchbMergeReg X c w = bchbMergeCore X c w := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (bchbMergeCore_eq X c hw).symm
  have h := hsum.congr' heq
  refine h.mono_right (le_of_eq ?_)
  congr 1
  push_cast
  ring

/-! ### The reduced ray -/

/-- Clearing the greatest common divisor: `h' k' (h,k)² = hk`. -/
theorem reducedProduct_mul_gcd_sq (h k : ℕ) :
    h / Nat.gcd h k * (k / Nat.gcd h k) * Nat.gcd h k ^ 2 = h * k := by
  have e : h / Nat.gcd h k * (k / Nat.gcd h k) * Nat.gcd h k ^ 2
      = h / Nat.gcd h k * Nat.gcd h k * (k / Nat.gcd h k * Nat.gcd h k) := by ring
  rw [e, Nat.div_mul_cancel (Nat.gcd_dvd_left h k), Nat.div_mul_cancel (Nat.gcd_dvd_right h k)]

/-- The same identity over the reals. -/
theorem reducedProduct_mul_gcd_sq_real (h k : ℕ) :
    ((h / Nat.gcd h k * (k / Nat.gcd h k) : ℕ) : ℝ) * (Nat.gcd h k : ℝ) ^ 2
      = (h : ℝ) * (k : ℝ) := by
  exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (reducedProduct_mul_gcd_sq h k)

/-- The reduced product is positive. -/
theorem reducedProduct_pos {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    0 < ((h / Nat.gcd h k * (k / Nat.gcd h k) : ℕ) : ℝ) := by
  have hg : 0 < Nat.gcd h k := Nat.gcd_pos_of_pos_left k hh
  have h1 : 0 < h / Nat.gcd h k :=
    Nat.div_pos (Nat.le_of_dvd hh (Nat.gcd_dvd_left h k)) hg
  have h2 : 0 < k / Nat.gcd h k :=
    Nat.div_pos (Nat.le_of_dvd hk (Nat.gcd_dvd_right h k)) hg
  exact_mod_cast Nat.mul_pos h1 h2

/-- **The Balasubramanian--Conrey--Heath-Brown normalization.**  The reduced ray carries the
critical-line weight `(h,k)/√(hk)`. -/
theorem sqrt_reducedProduct_mul_gcd (h k : ℕ) :
    Real.sqrt ((h / Nat.gcd h k * (k / Nat.gcd h k) : ℕ) : ℝ) * (Nat.gcd h k : ℝ)
      = Real.sqrt ((h : ℝ) * (k : ℝ)) := by
  have hg : (0 : ℝ) ≤ (Nat.gcd h k : ℝ) := by positivity
  have hc : (0 : ℝ) ≤ ((h / Nat.gcd h k * (k / Nat.gcd h k) : ℕ) : ℝ) := by positivity
  rw [← Real.sqrt_sq hg, ← Real.sqrt_mul hc, reducedProduct_mul_gcd_sq_real h k]

/-- The reduced-ray normalization in reciprocal form. -/
theorem inv_sqrt_reducedProduct {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    (Real.sqrt ((h / Nat.gcd h k * (k / Nat.gcd h k) : ℕ) : ℝ))⁻¹
      = (Nat.gcd h k : ℝ) / Real.sqrt ((h : ℝ) * (k : ℝ)) := by
  have hcpos := reducedProduct_pos hh hk
  have hs : 0 < Real.sqrt ((h / Nat.gcd h k * (k / Nat.gcd h k) : ℕ) : ℝ) :=
    Real.sqrt_pos.mpr hcpos
  have hgpos : (0 : ℝ) < (Nat.gcd h k : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left k hh
  rw [← sqrt_reducedProduct_mul_gcd h k]
  field_simp

/-! ### The packaged main term -/

/-- The main term of the twisted second moment of `ζ` on the critical line at scale `X`. -/
def bchbTwistedMainTerm (X : ℝ) (h k : ℕ) : ℝ :=
  (Nat.gcd h k : ℝ) / Real.sqrt ((h : ℝ) * (k : ℝ)) *
    (Real.log (X * (Nat.gcd h k : ℝ) ^ 2 / ((h : ℝ) * (k : ℝ)))
      + 2 * Real.eulerMascheroniConstant)

/-- The merged logarithm on the reduced ray. -/
theorem log_reducedProduct_merge {X : ℝ} (hX : 0 < X) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    Real.log X - Real.log ((h / Nat.gcd h k * (k / Nat.gcd h k) : ℕ) : ℝ)
      = Real.log (X * (Nat.gcd h k : ℝ) ^ 2 / ((h : ℝ) * (k : ℝ))) := by
  have hcpos := reducedProduct_pos hh hk
  have hgpos : (0 : ℝ) < (Nat.gcd h k : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left k hh
  have hprod := reducedProduct_mul_gcd_sq_real h k
  have hrw : X * (Nat.gcd h k : ℝ) ^ 2 / ((h : ℝ) * (k : ℝ))
      = X / ((h / Nat.gcd h k * (k / Nat.gcd h k) : ℕ) : ℝ) := by
    rw [← hprod]
    field_simp
  rw [hrw, Real.log_div hX.ne' hcpos.ne']

/-- **The twisted main term is the value of the shifted pair at the removed singularity.**
The logarithmic weight `log (X (h,k)²/(hk)) + 2γ` is exactly the limit of
`c^{-w/2} ζ(1+w) + X^{-w} c^{w/2} ζ(1-w)` at `w = 0`, with `c = h'k'` the reduced product. -/
theorem tendsto_bchbMergeCore_reduced {X : ℝ} (hX : 0 < X) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    Tendsto (bchbMergeCore X ((h / Nat.gcd h k * (k / Nat.gcd h k) : ℕ) : ℝ)) (𝓝[≠] 0)
      (𝓝 ((Real.log (X * (Nat.gcd h k : ℝ) ^ 2 / ((h : ℝ) * (k : ℝ)))
        + 2 * Real.eulerMascheroniConstant : ℝ) : ℂ)) := by
  have hcpos := reducedProduct_pos hh hk
  have h := tendsto_bchbMergeCore hX hcpos
  rwa [log_reducedProduct_merge hX hh hk] at h

/-- The packaged main term factors as reduced-ray normalization times the merged logarithm. -/
theorem bchbTwistedMainTerm_eq {X : ℝ} (hX : 0 < X) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    bchbTwistedMainTerm X h k
      = (Real.sqrt ((h / Nat.gcd h k * (k / Nat.gcd h k) : ℕ) : ℝ))⁻¹ *
        (Real.log X - Real.log ((h / Nat.gcd h k * (k / Nat.gcd h k) : ℕ) : ℝ)
          + 2 * Real.eulerMascheroniConstant) := by
  rw [bchbTwistedMainTerm, inv_sqrt_reducedProduct hh hk, log_reducedProduct_merge hX hh hk]

end

end RHTower.Sieve
