import GaloisForLFunctions.RHTower.Suzuki.SuzukiLagariasMeromorphicInner
import GaloisForLFunctions.RHTower.XiResolventMassBudget
import GaloisForLFunctions.RHTower.ScrewCurvatureSumOfSquares
import GaloisForLFunctions.HTGeometry.RealRootedCoefficientLimit
import GaloisForLFunctions.HTGeometry.LaguerrePolyaClass

/-!
# The cosine shifts of Ξ are Laguerre–Pólya

For `h > 0` put `A_h(z) = (Ξ(z + ih) + Ξ(z − ih))/2 = cos(hD)Ξ(z)`.  If every zero `γ` of `Ξ`
(centred spectral coordinate) satisfies `Im γ > −h`, then `A_h` lies in the Laguerre–Pólya class
(`laguerrePolya_cosineShiftXi_of_im_gt`).  Hence `A_h` is Laguerre–Pólya for every `h ≥ ½`
unconditionally (`laguerrePolya_cosineShiftXi`), and for every `h > 0` under RH
(`laguerrePolya_cosineShiftXi_of_rh`).

Proof.  Truncate the multiplicity-exact Hadamard product `Ξ = Ξ(0)·∏ E₁(z/γ)` to the zeros with
`|γ| ≤ m`.  This set is closed under `γ ↦ −γ`, so the exponential factors cancel and the truncation
is the polynomial `∏(1 − z/γ)`; it is closed under `γ ↦ γ̄`, so
`R_m(z) = Ξ(0)/2·(∏(1 − (z+ih)/γ) + ∏(1 − (z−ih)/γ))` has real coefficients.  For `Im z < 0`,
pairing `γ` with `γ̄` gives `|z + ih − γ̄| < |z − ih − γ|` factor by factor (Lagarias–Suzuki), so the
two products have different moduli and `R_m(z) ≠ 0`; conjugation excludes `Im z > 0`.  Thus each
`R_m` is real-rooted, and `R_m → A_h` locally uniformly.
-/

open Complex Polynomial Filter Topology Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## The ball truncation of the Xi divisor -/

theorem xiZeroBall_finite (m : ℕ) :
    {q : XiZeroCopy | ‖xiSpectralPoint q‖ ≤ m}.Finite := by
  have hev : ∀ᶠ q in cofinite, 1 / ‖xiSpectralPoint q‖ ^ 2 < 1 / ((m : ℝ) + 1) ^ 2 :=
    xiSpectralPoint_inv_sq_summable.tendsto_cofinite_zero.eventually
      (gt_mem_nhds (by positivity))
  rw [Filter.eventually_cofinite] at hev
  refine hev.subset fun q hq => ?_
  simp only [mem_setOf_eq, not_lt]
  have hpos : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hle : ‖xiSpectralPoint q‖ ≤ (m : ℝ) + 1 := by
    have : ‖xiSpectralPoint q‖ ≤ m := hq
    linarith
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hpos.le hle 2)

/-- The zeros of `Ξ` with `|γ| ≤ m`, with multiplicity. -/
def xiZeroBall (m : ℕ) : Finset XiZeroCopy := (xiZeroBall_finite m).toFinset

theorem mem_xiZeroBall {m : ℕ} {q : XiZeroCopy} :
    q ∈ xiZeroBall m ↔ ‖xiSpectralPoint q‖ ≤ m := by
  simp [xiZeroBall]

theorem xiSpectralPoint_reflect_symm (q : XiZeroCopy) :
    xiSpectralPoint (xiZeroCopyReflectEquiv.symm q) = -xiSpectralPoint q := by
  have h := xiSpectralPoint_reflect (xiZeroCopyReflectEquiv.symm q)
  rw [Equiv.apply_symm_apply] at h
  rw [h, neg_neg]

theorem xiSpectralPoint_lineConj_symm (q : XiZeroCopy) :
    xiSpectralPoint (xiZeroCopyLineConjEquiv.symm q) = (starRingEnd ℂ) (xiSpectralPoint q) := by
  have h := xiSpectralPoint_lineConj (xiZeroCopyLineConjEquiv.symm q)
  rw [Equiv.apply_symm_apply] at h
  rw [h, Complex.conj_conj]

/-- The ball is closed under `γ ↦ −γ`, so the reciprocal zeros sum to `0`. -/
theorem sum_inv_xiZeroBall (m : ℕ) :
    ∑ q ∈ xiZeroBall m, (xiSpectralPoint q)⁻¹ = 0 := by
  have h : ∑ q ∈ xiZeroBall m, -(xiSpectralPoint q)⁻¹ =
      ∑ q ∈ xiZeroBall m, (xiSpectralPoint q)⁻¹ := by
    refine Finset.sum_nbij' xiZeroCopyReflectEquiv xiZeroCopyReflectEquiv.symm
      (fun q hq => ?_) (fun q hq => ?_) (fun q _ => by simp) (fun q _ => by simp)
      (fun q _ => by rw [xiSpectralPoint_reflect, inv_neg])
    · rw [mem_xiZeroBall, xiSpectralPoint_reflect, norm_neg]; exact mem_xiZeroBall.mp hq
    · rw [mem_xiZeroBall, xiSpectralPoint_reflect_symm, norm_neg]; exact mem_xiZeroBall.mp hq
  rw [Finset.sum_neg_distrib] at h
  linear_combination -h / 2

/-- On the ball, the genus-one product is the polynomial `∏(1 − z/γ)`. -/
theorem prod_weierstrassE1_xiZeroBall (m : ℕ) (z : ℂ) :
    ∏ q ∈ xiZeroBall m, weierstrassE1 (z / xiSpectralPoint q) =
      ∏ q ∈ xiZeroBall m, (1 - z / xiSpectralPoint q) := by
  simp only [weierstrassE1, Finset.prod_mul_distrib]
  rw [← Complex.exp_sum]
  have hsum : ∑ q ∈ xiZeroBall m, z / xiSpectralPoint q =
      z * ∑ q ∈ xiZeroBall m, (xiSpectralPoint q)⁻¹ := by
    rw [Finset.mul_sum]; simp only [div_eq_mul_inv]
  rw [hsum, sum_inv_xiZeroBall, mul_zero, Complex.exp_zero, mul_one]

theorem tendstoLocallyUniformly_prod_xiZeroBall :
    TendstoLocallyUniformly (fun (m : ℕ) (z : ℂ) => ∏ q ∈ xiZeroBall m, (1 - z / xiSpectralPoint q))
      xiCanonicalProduct atTop := by
  have hmono : Monotone xiZeroBall := fun a b hab q hq =>
    mem_xiZeroBall.mpr ((mem_xiZeroBall.mp hq).trans (by exact_mod_cast hab))
  have hcov : ∀ q, ∃ m, q ∈ xiZeroBall m := fun q =>
    ⟨⌈‖xiSpectralPoint q‖⌉₊, mem_xiZeroBall.mpr (Nat.le_ceil _)⟩
  have ht := tendsto_atTop_finset_of_monotone hmono hcov
  have h2 : TendstoLocallyUniformly
      (fun (s : Finset XiZeroCopy) (z : ℂ) => ∏ q ∈ s, weierstrassE1 (z / xiSpectralPoint q))
      xiCanonicalProduct atTop := by
    rw [← tendstoLocallyUniformlyOn_univ]
    exact xiCanonicalProduct_hasProdLocallyUniformlyOn
  have h3 : TendstoLocallyUniformly
      (fun (m : ℕ) (z : ℂ) => ∏ q ∈ xiZeroBall m, weierstrassE1 (z / xiSpectralPoint q))
      xiCanonicalProduct atTop := by
    intro u hu x
    obtain ⟨t, ht', hev⟩ := h2 u hu x
    exact ⟨t, ht', ht.eventually hev⟩
  exact h3.congr fun m z => prod_weierstrassE1_xiZeroBall m z

/-! ## The real-rooted truncations -/

/-- `Ξ(0)/2·(∏(1 − (X+ih)/γ) + ∏(1 − (X−ih)/γ))` over the ball. -/
def cosineShiftPolyC (h : ℝ) (m : ℕ) : ℂ[X] :=
  C (XiC 0 / 2) *
    (∏ q ∈ xiZeroBall m, (1 - C (xiSpectralPoint q)⁻¹ * (X + C ((h : ℂ) * I))) +
      ∏ q ∈ xiZeroBall m, (1 - C (xiSpectralPoint q)⁻¹ * (X - C ((h : ℂ) * I))))

theorem eval_cosineShiftPolyC (h : ℝ) (m : ℕ) (z : ℂ) :
    (cosineShiftPolyC h m).eval z =
      XiC 0 / 2 * (∏ q ∈ xiZeroBall m, (1 - (z + h * I) / xiSpectralPoint q) +
        ∏ q ∈ xiZeroBall m, (1 - (z - h * I) / xiSpectralPoint q)) := by
  simp only [cosineShiftPolyC, eval_mul, eval_C, eval_add, eval_prod, eval_sub, eval_one,
    eval_X]
  congr 2 <;> refine Finset.prod_congr rfl fun q _ => ?_ <;> ring

theorem conj_XiC_zero : (starRingEnd ℂ) (XiC 0) = XiC 0 := by
  have h := XiC_ofReal 0
  rw [Complex.ofReal_zero] at h
  rw [h, Complex.conj_ofReal]

theorem prod_lineConj_xiZeroBall (m : ℕ) (P : ℂ → ℂ[X]) :
    ∏ q ∈ xiZeroBall m, P ((starRingEnd ℂ) (xiSpectralPoint q)) =
      ∏ q ∈ xiZeroBall m, P (xiSpectralPoint q) := by
  refine Finset.prod_nbij' xiZeroCopyLineConjEquiv xiZeroCopyLineConjEquiv.symm
    (fun q hq => ?_) (fun q hq => ?_) (fun q _ => by simp) (fun q _ => by simp)
    (fun q _ => by rw [xiSpectralPoint_lineConj])
  · rw [mem_xiZeroBall, xiSpectralPoint_lineConj, Complex.norm_conj]
    exact mem_xiZeroBall.mp hq
  · rw [mem_xiZeroBall, xiSpectralPoint_lineConj_symm, Complex.norm_conj]
    exact mem_xiZeroBall.mp hq

/-- The truncation has real coefficients. -/
theorem map_conj_cosineShiftPolyC (h : ℝ) (m : ℕ) :
    (cosineShiftPolyC h m).map (starRingEnd ℂ) = cosineShiftPolyC h m := by
  have hI : (starRingEnd ℂ) ((h : ℂ) * I) = -((h : ℂ) * I) := by
    simp [Complex.conj_ofReal, Complex.conj_I]
  have h1 := prod_lineConj_xiZeroBall m (fun γ => 1 - C γ⁻¹ * (X - C ((h : ℂ) * I)))
  have h2 := prod_lineConj_xiZeroBall m (fun γ => 1 - C γ⁻¹ * (X - -C ((h : ℂ) * I)))
  simp only [cosineShiftPolyC, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_prod,
    Polynomial.map_sub, Polynomial.map_one, Polynomial.map_C, Polynomial.map_X, map_div₀,
    conj_XiC_zero, map_inv₀, hI, map_ofNat, C_neg, ← sub_eq_add_neg]
  rw [h1, h2, sub_neg_eq_add, add_comm]

theorem exists_real_cosineShiftPoly (h : ℝ) (m : ℕ) :
    ∃ p : ℝ[X], p.map (algebraMap ℝ ℂ) = cosineShiftPolyC h m := by
  have hmem : cosineShiftPolyC h m ∈ Polynomial.lifts (algebraMap ℝ ℂ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    have hc : (starRingEnd ℂ) ((cosineShiftPolyC h m).coeff n) = (cosineShiftPolyC h m).coeff n := by
      conv_rhs => rw [← map_conj_cosineShiftPolyC h m]
      rw [Polynomial.coeff_map]
    exact ⟨((cosineShiftPolyC h m).coeff n).re, Complex.conj_eq_iff_re.mp hc⟩
  exact Polynomial.mem_lifts _ |>.mp hmem

/-! ## No zeros off the real axis -/

theorem norm_prod_shift_lt {h : ℝ} (hz : ∀ q, -h < (xiSpectralPoint q).im) {m : ℕ}
    (hne : (xiZeroBall m).Nonempty) {z : ℂ} (hzim : z.im < 0) :
    ‖∏ q ∈ xiZeroBall m, (1 - (z + h * I) / xiSpectralPoint q)‖ <
      ‖∏ q ∈ xiZeroBall m, (1 - (z - h * I) / xiSpectralPoint q)‖ := by
  rw [norm_prod, norm_prod]
  have hre : ∏ q ∈ xiZeroBall m, ‖1 - (z + h * I) / xiSpectralPoint q‖ =
      ∏ q ∈ xiZeroBall m, ‖1 - (z + h * I) / (starRingEnd ℂ) (xiSpectralPoint q)‖ := by
    symm
    refine Finset.prod_nbij' xiZeroCopyLineConjEquiv xiZeroCopyLineConjEquiv.symm
      (fun q hq => ?_) (fun q hq => ?_) (fun q _ => by simp) (fun q _ => by simp)
      (fun q _ => by rw [xiSpectralPoint_lineConj])
    · rw [mem_xiZeroBall, xiSpectralPoint_lineConj, Complex.norm_conj]
      exact mem_xiZeroBall.mp hq
    · rw [mem_xiZeroBall, xiSpectralPoint_lineConj_symm, Complex.norm_conj]
      exact mem_xiZeroBall.mp hq
  rw [hre]
  have hfac : ∀ q ∈ xiZeroBall m,
      ‖1 - (z + h * I) / (starRingEnd ℂ) (xiSpectralPoint q)‖ <
        ‖1 - (z - h * I) / xiSpectralPoint q‖ := by
    intro q _
    have hγ := xiSpectralPoint_ne_zero q
    have hγc : (starRingEnd ℂ) (xiSpectralPoint q) ≠ 0 := by
      rwa [_root_.map_ne_zero]
    have hn : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr hγ
    have e1 : 1 - (z + h * I) / (starRingEnd ℂ) (xiSpectralPoint q) =
        -((z + h * I) - (starRingEnd ℂ) (xiSpectralPoint q)) / (starRingEnd ℂ) (xiSpectralPoint q) := by
      field_simp; ring
    have e2 : 1 - (z - h * I) / xiSpectralPoint q =
        -((z - h * I) - xiSpectralPoint q) / xiSpectralPoint q := by
      field_simp; ring
    rw [e1, e2, norm_div, norm_div, norm_neg, norm_neg, Complex.norm_conj]
    exact div_lt_div_of_pos_right
      (norm_sub_lt_norm_sub_vertical_shift z (xiSpectralPoint q) h hzim (hz q)) hn
  by_cases h0 : ∏ q ∈ xiZeroBall m, ‖1 - (z + h * I) / (starRingEnd ℂ) (xiSpectralPoint q)‖ = 0
  · rw [h0]
    refine Finset.prod_pos fun q hq => ?_
    exact lt_of_le_of_lt (norm_nonneg _) (hfac q hq)
  · refine Finset.prod_lt_prod_of_nonempty (fun q hq => ?_) hfac hne
    rcases (norm_nonneg (1 - (z + h * I) / (starRingEnd ℂ) (xiSpectralPoint q))).lt_or_eq with
      hlt | heq
    · exact hlt
    · exact absurd (Finset.prod_eq_zero hq heq.symm) h0

theorem eval_cosineShiftPolyC_ne_zero {h : ℝ} (hz : ∀ q, -h < (xiSpectralPoint q).im) (m : ℕ)
    {z : ℂ} (hzim : z.im < 0) : (cosineShiftPolyC h m).eval z ≠ 0 := by
  rw [eval_cosineShiftPolyC]
  have hc : XiC 0 / 2 ≠ 0 := div_ne_zero XiC_zero_ne two_ne_zero
  refine mul_ne_zero hc fun hsum => ?_
  rcases (xiZeroBall m).eq_empty_or_nonempty with he | hne
  · simp [he] at hsum
  · have hlt := norm_prod_shift_lt hz hne hzim
    rw [add_eq_zero_iff_eq_neg.mp hsum, norm_neg] at hlt
    exact lt_irrefl _ hlt

theorem im_eq_zero_of_eval_cosineShiftPolyC {h : ℝ} (hz : ∀ q, -h < (xiSpectralPoint q).im)
    (m : ℕ) {z : ℂ} (h0 : (cosineShiftPolyC h m).eval z = 0) : z.im = 0 := by
  rcases lt_trichotomy z.im 0 with hlt | heq | hgt
  · exact absurd h0 (eval_cosineShiftPolyC_ne_zero hz m hlt)
  · exact heq
  · exfalso
    have hconj : (cosineShiftPolyC h m).eval ((starRingEnd ℂ) z) = 0 := by
      rw [← map_conj_cosineShiftPolyC h m, Polynomial.eval_map, Polynomial.eval₂_hom, h0,
        map_zero]
    exact eval_cosineShiftPolyC_ne_zero hz m (by simp; linarith) hconj

/-! ## Laguerre–Pólya membership -/

/-- **Cosine shifts of Ξ are Laguerre–Pólya.**  If every zero of `Ξ` has `Im γ > −h`, then
`z ↦ (Ξ(z + ih) + Ξ(z − ih))/2` is a locally uniform limit of real-rooted real polynomials. -/
theorem laguerrePolya_cosineShiftXi_of_im_gt {h : ℝ} (hz : ∀ q, -h < (xiSpectralPoint q).im) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya (fun z => (XiC (z + h * I) + XiC (z - h * I)) / 2) := by
  choose p hp using exists_real_cosineShiftPoly h
  have hev : ∀ m, polyEvalC (p m) = fun z => XiC 0 / 2 *
      (∏ q ∈ xiZeroBall m, (1 - (z + h * I) / xiSpectralPoint q) +
        ∏ q ∈ xiZeroBall m, (1 - (z - h * I) / xiSpectralPoint q)) := by
    intro m
    funext z
    rw [polyEvalC_eq_eval_map, hp, eval_cosineShiftPolyC]
  refine ⟨p, fun m => ?_, ?_⟩
  · refine splits_of_forall_complex_root_real (p m).natDegree (p m) le_rfl fun z hz0 => ?_
    have : (cosineShiftPolyC h m).eval z = 0 := by
      rw [← hp, Polynomial.eval_map, ← Polynomial.aeval_def]; exact hz0
    exact im_eq_zero_of_eval_cosineShiftPolyC hz m this
  · have hP := tendstoLocallyUniformly_prod_xiZeroBall
    have hplus := hP.comp (fun z : ℂ => z + h * I) (continuous_add_const _)
    have hminus := hP.comp (fun z : ℂ => z - h * I) (continuous_sub_right _)
    have hscaled := (uniformContinuous_const_smul (XiC 0 / 2)).comp_tendstoLocallyUniformly
      (hplus.add hminus)
    have hX : ∀ w, XiC w = XiC 0 * xiCanonicalProduct w := fun w => by
      simpa using congrFun XiC_eq_constant_mul_canonicalProduct w
    convert hscaled using 1
    · funext m z
      rw [hev m]
      simp only [Function.comp_apply, Pi.add_apply, smul_eq_mul]
    · funext z
      simp only [Function.comp_apply, Pi.add_apply, smul_eq_mul]
      rw [hX (z + h * I), hX (z - h * I)]
      ring

/-- **Unconditional:** `cos(hD)Ξ` is Laguerre–Pólya for every `h ≥ ½`. -/
theorem laguerrePolya_cosineShiftXi {h : ℝ} (hh : 1 / 2 ≤ h) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya (fun z => (XiC (z + h * I) + XiC (z - h * I)) / 2) := by
  refine laguerrePolya_cosineShiftXi_of_im_gt fun q => ?_
  have hsq := xiSpectralPoint_im_sq_lt_quarter q
  have : -(1 / 2 : ℝ) < (xiSpectralPoint q).im := by
    nlinarith [sq_nonneg ((xiSpectralPoint q).im + 1 / 2)]
  linarith

/-- **Under RH:** `cos(hD)Ξ` is Laguerre–Pólya for every `h > 0`. -/
theorem laguerrePolya_cosineShiftXi_of_rh (hRH : RiemannHypothesis) {h : ℝ} (hh : 0 < h) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya (fun z => (XiC (z + h * I) + XiC (z - h * I)) / 2) := by
  refine laguerrePolya_cosineShiftXi_of_im_gt fun q => ?_
  rw [xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH q]
  linarith

end RHTower
