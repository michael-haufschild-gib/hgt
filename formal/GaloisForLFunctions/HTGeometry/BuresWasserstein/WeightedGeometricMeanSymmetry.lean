import GaloisForLFunctions.HTGeometry.BuresWasserstein.OperatorGeometricMean
import GaloisForLFunctions.HTGeometry.DisjointSpectrumIntertwiner

/-!
# Symmetry of the weighted geometric mean

With `z := a^{-1/2} b^{1/2}` one has `z z^* = a^{-1/2} b a^{-1/2}`, the middle of `a #_t b`, and
`z^* z = (b^{-1/2} a b^{-1/2})^{-1}`, the inverse of the middle of `b #_{1-t} a`.  The algebraic
intertwining `(z z^*) z = z (z^* z)` passes to the continuous functional calculus, so both means
collapse to `b^{1/2}(b^{-1/2} a b^{-1/2})^{1-t}b^{1/2}` and

`a #_t b = b #_{1-t} a`.

Monotonicity in the first argument and homogeneity in a left scalar follow.
-/

open scoped NNReal Ring

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {a b : A}

/-- The continuous functional calculus intertwines `z z^*` and `z^* z`. -/
theorem rpow_mul_star_intertwine (z : A) {t : ℝ} (ht : 0 ≤ t) :
    ((z * star z) ^ t : A) * z = z * (star z * z) ^ t := by
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · exact Subsingleton.elim _ _
  have hsa1 : IsSelfAdjoint (z * star z) := by
    show star (z * star z) = z * star z
    rw [star_mul, star_star]
  have hsa2 : IsSelfAdjoint (star z * z) := by
    show star (star z * z) = star z * z
    rw [star_mul, star_star]
  have hnn1 : (0 : A) ≤ z * star z := mul_star_self_nonneg z
  have hnn2 : (0 : A) ≤ star z * z := star_mul_self_nonneg z
  have hg : Continuous (fun x : ℝ => ((x.toNNReal ^ t : ℝ≥0) : ℝ)) := by
    have heq : (fun x : ℝ => ((x.toNNReal ^ t : ℝ≥0) : ℝ)) = fun x : ℝ => (max x 0) ^ t := by
      funext x
      rw [NNReal.coe_rpow, Real.coe_toNNReal']
    rw [heq]
    exact (Real.continuous_rpow_const ht).comp (continuous_id.max continuous_const)
  have h := cfc_mul_eq_mul_cfc_of_intertwine hsa1 hsa2
    (by rw [mul_assoc] : (z * star z) * z = z * (star z * z)) hg
  rw [CFC.rpow_def (a := z * star z) (y := t), CFC.rpow_def (a := star z * z) (y := t),
    cfc_nnreal_eq_real (fun x : ℝ≥0 => x ^ t) (z * star z) hnn1,
    cfc_nnreal_eq_real (fun x : ℝ≥0 => x ^ t) (star z * z) hnn2]
  exact h

/-- **Symmetry of the weighted geometric mean**: `a #_t b = b #_{1-t} a`. -/
theorem wgm_symm {t : ℝ} (ht : 0 ≤ t) (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    wgm t a b = wgm (1 - t) b a := by
  have han : IsStrictlyPositive (a ^ (-(1/2) : ℝ) : A) := ha.rpow a _
  have hah : IsStrictlyPositive (a ^ (1/2 : ℝ) : A) := ha.rpow a _
  have hbh : IsStrictlyPositive (b ^ (1/2 : ℝ) : A) := hb.rpow b _
  have hbn : IsStrictlyPositive (b ^ (-(1/2) : ℝ) : A) := hb.rpow b _
  obtain ⟨z, hzdef⟩ : ∃ x : A, x = (a ^ (-(1/2) : ℝ) : A) * b ^ (1/2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨zi, hzidef⟩ : ∃ x : A, x = (b ^ (-(1/2) : ℝ) : A) * a ^ (1/2 : ℝ) := ⟨_, rfl⟩
  have hzstar : star z = (b ^ (1/2 : ℝ) : A) * a ^ (-(1/2) : ℝ) := by
    rw [hzdef, star_mul, (isSelfAdjoint_rpow a _).star_eq, (isSelfAdjoint_rpow b _).star_eq]
  have hzistar : star zi = (a ^ (1/2 : ℝ) : A) * b ^ (-(1/2) : ℝ) := by
    rw [hzidef, star_mul, (isSelfAdjoint_rpow a _).star_eq, (isSelfAdjoint_rpow b _).star_eq]
  have hzzi : z * zi = 1 := by
    rw [hzdef, hzidef,
      show (a ^ (-(1/2) : ℝ) : A) * b ^ (1/2 : ℝ) * ((b ^ (-(1/2) : ℝ) : A) * a ^ (1/2 : ℝ))
        = (a ^ (-(1/2) : ℝ) : A) * ((b ^ (1/2 : ℝ) : A) * b ^ (-(1/2) : ℝ)) * a ^ (1/2 : ℝ) by
        noncomm_ring,
      rpow_half_mul_rpow_neg_half hb, mul_one, rpow_neg_half_mul_rpow_half ha]
  have hziz : zi * z = 1 := by
    rw [hzdef, hzidef,
      show (b ^ (-(1/2) : ℝ) : A) * a ^ (1/2 : ℝ) * ((a ^ (-(1/2) : ℝ) : A) * b ^ (1/2 : ℝ))
        = (b ^ (-(1/2) : ℝ) : A) * ((a ^ (1/2 : ℝ) : A) * a ^ (-(1/2) : ℝ)) * b ^ (1/2 : ℝ) by
        noncomm_ring,
      rpow_half_mul_rpow_neg_half ha, mul_one, rpow_neg_half_mul_rpow_half hb]
  -- the two middles
  have hzz : z * star z = (a ^ (-(1/2) : ℝ) : A) * b * a ^ (-(1/2) : ℝ) := by
    rw [hzstar, hzdef,
      show (a ^ (-(1/2) : ℝ) : A) * b ^ (1/2 : ℝ) * ((b ^ (1/2 : ℝ) : A) * a ^ (-(1/2) : ℝ))
        = (a ^ (-(1/2) : ℝ) : A) * ((b ^ (1/2 : ℝ) : A) * b ^ (1/2 : ℝ)) * a ^ (-(1/2) : ℝ) by
        noncomm_ring,
      rpow_half_mul_rpow_half hb]
  have hzizi : zi * star zi = (b ^ (-(1/2) : ℝ) : A) * a * b ^ (-(1/2) : ℝ) := by
    rw [hzistar, hzidef,
      show (b ^ (-(1/2) : ℝ) : A) * a ^ (1/2 : ℝ) * ((a ^ (1/2 : ℝ) : A) * b ^ (-(1/2) : ℝ))
        = (b ^ (-(1/2) : ℝ) : A) * ((a ^ (1/2 : ℝ) : A) * a ^ (1/2 : ℝ)) * b ^ (-(1/2) : ℝ) by
        noncomm_ring,
      rpow_half_mul_rpow_half ha]
  -- `star z * z` is the inverse of the middle of the other mean
  have hc : IsStrictlyPositive ((b ^ (-(1/2) : ℝ) : A) * a * b ^ (-(1/2) : ℝ)) :=
    conj_strictlyPositive hb ha
  have hsz : star z * z = ((b ^ (-(1/2) : ℝ) : A) * a * b ^ (-(1/2) : ℝ))⁻¹ʳ := by
    have hprod : ((b ^ (-(1/2) : ℝ) : A) * a * b ^ (-(1/2) : ℝ)) * (star z * z) = 1 := by
      rw [hzstar, hzdef, ← hzizi, hzistar, hzidef]
      have hexp : ((b ^ (-(1/2) : ℝ) : A) * a ^ (1/2 : ℝ)) * ((a ^ (1/2 : ℝ) : A)
            * b ^ (-(1/2) : ℝ))
          * ((b ^ (1/2 : ℝ) : A) * a ^ (-(1/2) : ℝ) * ((a ^ (-(1/2) : ℝ) : A) * b ^ (1/2 : ℝ)))
          = ((b ^ (-(1/2) : ℝ) : A) * a ^ (1/2 : ℝ))
            * ((a ^ (1/2 : ℝ) : A) * ((b ^ (-(1/2) : ℝ) : A) * b ^ (1/2 : ℝ))
              * ((a ^ (-(1/2) : ℝ) : A) * a ^ (-(1/2) : ℝ)) * b ^ (1/2 : ℝ)) := by
        noncomm_ring
      rw [hexp, rpow_neg_half_mul_rpow_half hb, mul_one,
        rpow_neg_half_mul_rpow_neg_half ha]
      have hexp2 : ((b ^ (-(1/2) : ℝ) : A) * a ^ (1/2 : ℝ))
          * ((a ^ (1/2 : ℝ) : A) * a⁻¹ʳ * b ^ (1/2 : ℝ))
          = (b ^ (-(1/2) : ℝ) : A) * ((a ^ (1/2 : ℝ) : A) * a ^ (1/2 : ℝ) * a⁻¹ʳ)
            * b ^ (1/2 : ℝ) := by noncomm_ring
      rw [hexp2, rpow_half_mul_rpow_half ha, Ring.mul_inverse_cancel _ ha.isUnit, mul_one,
        rpow_neg_half_mul_rpow_half hb]
    calc (star z * z)
        = ((b ^ (-(1/2) : ℝ) : A) * a * b ^ (-(1/2) : ℝ))⁻¹ʳ
          * (((b ^ (-(1/2) : ℝ) : A) * a * b ^ (-(1/2) : ℝ)) * (star z * z)) := by
          rw [← mul_assoc, Ring.inverse_mul_cancel _ hc.isUnit, one_mul]
      _ = ((b ^ (-(1/2) : ℝ) : A) * a * b ^ (-(1/2) : ℝ))⁻¹ʳ := by rw [hprod, mul_one]
  -- the intertwining, transported to `zi`
  have hinter : (zi : A) * (z * star z) ^ t = ((star z * z) ^ t : A) * zi := by
    have h := rpow_mul_star_intertwine z ht
    have h1 := congrArg (fun x : A => zi * x * zi) h
    have hl : (zi : A) * (((z * star z) ^ t : A) * z) * zi
        = (zi : A) * ((z * star z) ^ t : A) * (z * zi) := by noncomm_ring
    have hr : (zi : A) * (z * ((star z * z) ^ t : A)) * zi
        = ((zi : A) * z) * (((star z * z) ^ t : A) * zi) := by noncomm_ring
    rw [hl, hr, hzzi, hziz, mul_one, one_mul] at h1
    exact h1
  -- rewrite `a^{1/2}` through `zi`
  have hleft : (a ^ (1/2 : ℝ) : A) = (b ^ (1/2 : ℝ) : A) * zi := by
    rw [hzidef, ← mul_assoc, rpow_half_mul_rpow_neg_half hb, one_mul]
  have hright : (a ^ (1/2 : ℝ) : A) = star zi * b ^ (1/2 : ℝ) := by
    rw [hzistar, mul_assoc, rpow_neg_half_mul_rpow_half hb, mul_one]
  -- the negative power
  have hcneg : (((b ^ (-(1/2) : ℝ) : A) * a * b ^ (-(1/2) : ℝ))⁻¹ʳ ^ t : A)
      = ((b ^ (-(1/2) : ℝ) : A) * a * b ^ (-(1/2) : ℝ)) ^ (-t) := by
    have hu := hc.isUnit
    have h := CFC.rpow_neg hu.unit t (by rw [hu.unit_spec]; exact hc.nonneg)
    rw [hu.unit_spec] at h
    rw [h, ← Ring.inverse_unit hu.unit, hu.unit_spec]
  -- assemble
  rw [wgm_def, wgm_def, ← hzz]
  nth_rewrite 1 [hleft]
  rw [hright]
  have hstep : (b ^ (1/2 : ℝ) : A) * zi * ((z * star z) ^ t : A) * (star zi * b ^ (1/2 : ℝ))
      = (b ^ (1/2 : ℝ) : A) * (((star z * z) ^ t : A) * (zi * star zi)) * b ^ (1/2 : ℝ) := by
    rw [show (b ^ (1/2 : ℝ) : A) * zi * ((z * star z) ^ t : A) * (star zi * b ^ (1/2 : ℝ))
        = (b ^ (1/2 : ℝ) : A) * ((zi : A) * ((z * star z) ^ t : A)) * star zi
          * b ^ (1/2 : ℝ) by noncomm_ring, hinter]
    noncomm_ring
  rw [hstep, hzizi, hsz, hcneg]
  have hadd : (((b ^ (-(1/2) : ℝ) : A) * a * b ^ (-(1/2) : ℝ)) ^ (-t) : A)
        * ((b ^ (-(1/2) : ℝ) : A) * a * b ^ (-(1/2) : ℝ))
      = ((b ^ (-(1/2) : ℝ) : A) * a * b ^ (-(1/2) : ℝ)) ^ (1 - t) := by
    have h1 : (((b ^ (-(1/2) : ℝ) : A) * a * b ^ (-(1/2) : ℝ)) ^ (-t + 1) : A)
        = ((b ^ (-(1/2) : ℝ) : A) * a * b ^ (-(1/2) : ℝ)) ^ (-t)
          * ((b ^ (-(1/2) : ℝ) : A) * a * b ^ (-(1/2) : ℝ)) ^ (1 : ℝ) :=
      CFC.rpow_add hc.isUnit
    rw [CFC.rpow_one _ hc.nonneg] at h1
    rw [← h1]
    congr 1
    ring
  rw [hadd]

/-- **Monotonicity of the weighted geometric mean in the first argument.** -/
theorem wgm_mono_left {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {c : A} (ha : IsStrictlyPositive a)
    (hc : IsStrictlyPositive c) (hb : IsStrictlyPositive b) (h : a ≤ c) :
    wgm t a b ≤ wgm t c b := by
  rw [wgm_symm ht.1 ha hb, wgm_symm ht.1 hc hb]
  exact wgm_mono_right ⟨by linarith [ht.2], by linarith [ht.1]⟩ b h

/-- **Joint monotonicity of the weighted geometric mean.** -/
theorem wgm_mono {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {c d : A} (ha : IsStrictlyPositive a)
    (hc : IsStrictlyPositive c) (hd : IsStrictlyPositive d)
    (hac : a ≤ c) (hbd : b ≤ d) :
    wgm t a b ≤ wgm t c d :=
  le_trans (wgm_mono_right ht a hbd) (wgm_mono_left ht ha hc hd hac)

/-! ### Homogeneity -/

/-- **Homogeneity of the real power**: `(r • a)^t = r^t • a^t`. -/
theorem rpow_smul_of_nonneg {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) {x : A} (hx : 0 ≤ x) :
    ((r • x) ^ t : A) = (r ^ t) • (x ^ t) := by
  have hrx : (0 : A) ≤ r • x := smul_nonneg hr hx
  have hg : Continuous (fun y : ℝ => ((y.toNNReal ^ t : ℝ≥0) : ℝ)) := by
    have heq : (fun y : ℝ => ((y.toNNReal ^ t : ℝ≥0) : ℝ)) = fun y : ℝ => (max y 0) ^ t := by
      funext y
      rw [NNReal.coe_rpow, Real.coe_toNNReal']
    rw [heq]
    exact (Real.continuous_rpow_const ht).comp (continuous_id.max continuous_const)
  have hfun : (fun y : ℝ => (((r • y).toNNReal ^ t : ℝ≥0) : ℝ))
      = fun y : ℝ => r ^ t * ((y.toNNReal ^ t : ℝ≥0) : ℝ) := by
    funext y
    rw [smul_eq_mul, Real.toNNReal_mul hr, NNReal.mul_rpow, NNReal.coe_mul, NNReal.coe_rpow,
      Real.coe_toNNReal r hr]
  rw [CFC.rpow_def (a := r • x) (y := t), CFC.rpow_def (a := x) (y := t),
    cfc_nnreal_eq_real (fun y : ℝ≥0 => y ^ t) (r • x) hrx,
    cfc_nnreal_eq_real (fun y : ℝ≥0 => y ^ t) x hx,
    ← cfc_comp_smul r (fun y : ℝ => ((y.toNNReal ^ t : ℝ≥0) : ℝ)) x hg.continuousOn, hfun,
    cfc_const_mul (r ^ t) (fun y : ℝ => ((y.toNNReal ^ t : ℝ≥0) : ℝ)) x hg.continuousOn]

/-- **Left homogeneity of the weighted geometric mean**: `(r • a) #_t b = r^{1-t} (a #_t b)`. -/
theorem wgm_smul_left {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    wgm t (r • a) b = (r ^ (1 - t)) • wgm t a b := by
  rw [wgm_symm ht (IsStrictlyPositive.smul hr ha) hb, wgm_symm ht ha hb, wgm_def, wgm_def]
  have hmid : (b ^ (-(1/2) : ℝ) : A) * (r • a) * b ^ (-(1/2) : ℝ)
      = r • ((b ^ (-(1/2) : ℝ) : A) * a * b ^ (-(1/2) : ℝ)) := by
    rw [mul_smul_comm, smul_mul_assoc]
  rw [hmid, rpow_smul_of_nonneg hr.le (by linarith : (0:ℝ) ≤ 1 - t)
    (conj_strictlyPositive hb ha).nonneg]
  rw [mul_smul_comm, smul_mul_assoc]

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
