import GaloisForLFunctions.RHTower.XiSliceGaussianFiniteHead

/-!
# Lossless Taylor-positivity transfer from the retained finite head to the full Xi slice

At every height `t ∈ ℝ` and cutoff radius `R ≥ 0`, `xiSliceProduct_eq_gaussianFiniteHead_mul_tail`
factors the horizontal slice as

  `xiSliceProduct t z = xiSliceGaussianFiniteHead t R z * xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) z`.

While Gaussian approximation of the infinite tail introduces a fourth-moment remainder, the exact
complementary tail `xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R)` needs no Gaussian
approximation to preserve Taylor-coefficient positivity at `z = 0`:

1. **Reflection invariance and automatic cone condition outside `R ≥ 1/√2`.**  The spectral-radius
   head `xiSliceGaussianRadiusHead t R` is invariant under the Hermitian reflection `lagPartner`.
   Every zero copy `q ∉ xiSliceGaussianRadiusHead t R` satisfies `‖z_q − t‖ > R` and
   `(Im z_q)² < 1/4`, hence `(Re z_q − t)² − (Im z_q)² > R² − 1/2`.  For `R² ≥ 1/2` every tail
   zero copy therefore lies outside the `π/4` cone at `t`.
2. **Unconditional Taylor positivity of the exact infinite tail**
   (`nonnegTaylorAtZero_xiSliceGaussianTail_radius`).  Grouping the complementary canonical product
   into `lagPartner`-orbits shows that `xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R)` is
   an entire function with all Taylor coefficients at `0` real and nonnegative whenever `R ≥ 0` and
   `1/2 ≤ R²`.
3. **Lossless finite-head reduction of RH**
   (`riemannHypothesis_iff_forall_nonnegTaylorAtZero_xiSliceGaussianFiniteHead`).  By the Leibniz
   product rule (`NonnegTaylorAtZero.mul`), Taylor positivity of the retained finite-head polynomial
   `xiSliceGaussianFiniteHead t R` implies Taylor positivity of the full slice `xiSliceProduct t`
   without any tail error.  Conversely, if every zero in `xiSliceGaussianRadiusHead t R` lies
   outside the `π/4` cone (and in particular under RH), the finite head has nonnegative Taylor
   coefficients at `0`.  Thus for any fixed `R ≥ 0` with `1/2 ≤ R²`, the Riemann hypothesis is
   equivalent to `∀ t : ℝ, NonnegTaylorAtZero (xiSliceGaussianFiniteHead t R)`.
4. **Unconditional real-axis positivity of the finite head and full-slice Gaussian bracket**
   (`xiSliceGaussianFiniteHead_ofReal_nonneg`, `xiSliceProduct_real_gaussian_bracket`).  On the real
   axis `z = x ∈ ℝ`, reflection pairing makes `xiSliceGaussianFiniteHead t R x` real and nonnegative
   for every `t, R, x ∈ ℝ`, yielding the two-sided Gaussian bracket for the real slice on all of `ℝ`
   when `R ≥ 4`.
-/

open Complex Filter Topology
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- The spectral-radius head `xiSliceGaussianRadiusHead t R` is invariant under `lagPartner`. -/
theorem mem_xiSliceGaussianRadiusHead_lagPartner_iff (t R : ℝ) (q : XiZeroCopy) :
    lagPartner q ∈ xiSliceGaussianRadiusHead t R ↔ q ∈ xiSliceGaussianRadiusHead t R := by
  rw [mem_xiSliceGaussianRadiusHead, mem_xiSliceGaussianRadiusHead, xiSpectralPoint_lagPartner]
  have hc : (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := by simp
  rw [← hc, ← map_sub, Complex.norm_conj, hc]

/-- Every zero copy outside `xiSliceGaussianRadiusHead t R` (`R ≥ 0`) satisfies
`R² − 1/2 ≤ (Re z_q − t)² − (Im z_q)²`. -/
theorem xiSliceGaussianRadiusHead_compl_re_sq_sub_im_sq {t R : ℝ} (hR : 0 ≤ R) {q : XiZeroCopy}
    (hq : q ∉ xiSliceGaussianRadiusHead t R) :
    R ^ 2 - 1 / 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 - (xiSpectralPoint q).im ^ 2 := by
  have hd : R < ‖xiSpectralPoint q - (t : ℂ)‖ :=
    lt_of_not_ge fun h => hq ((mem_xiSliceGaussianRadiusHead t R q).mpr h)
  have hsq : R ^ 2 ≤ ‖xiSpectralPoint q - (t : ℂ)‖ ^ 2 :=
    pow_le_pow_left₀ hR hd.le 2
  have hnorm : ‖xiSpectralPoint q - (t : ℂ)‖ ^ 2 =
      ((xiSpectralPoint q).re - t) ^ 2 + (xiSpectralPoint q).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    ring
  have him := xiSpectralPoint_im_sq_lt_quarter q
  linarith

/-- For `R ≥ 0` and `1/2 ≤ R² + M`, every zero copy outside `xiSliceGaussianRadiusHead t R`
satisfies the shifted cone inequality `(Im z_q)² ≤ (Re z_q − t)² + M`. -/
theorem xiSliceGaussianRadiusHead_compl_heatedCone {t R M : ℝ} (hR : 0 ≤ R)
    (hRM : 1 / 2 ≤ R ^ 2 + M) {q : XiZeroCopy} (hq : q ∉ xiSliceGaussianRadiusHead t R) :
    (xiSpectralPoint q).im ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 + M := by
  have h := xiSliceGaussianRadiusHead_compl_re_sq_sub_im_sq hR hq
  linarith

/-- For `R ≥ 0` with `1/2 ≤ R²`, every zero copy outside `xiSliceGaussianRadiusHead t R` lies
outside the `π/4` cone at `t`. -/
theorem xiSliceGaussianRadiusHead_compl_cone {t R : ℝ} (hR : 0 ≤ R) (hR2 : 1 / 2 ≤ R ^ 2)
    {q : XiZeroCopy} (hq : q ∉ xiSliceGaussianRadiusHead t R) :
    (xiSpectralPoint q).im ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 := by
  simpa using xiSliceGaussianRadiusHead_compl_heatedCone hR (M := 0) (by linarith) hq

/-- In `ρ`-coordinates, every zero copy outside `xiSliceGaussianRadiusHead t R` (`R ≥ 0`,
`1/2 ≤ R²`) satisfies `|Re ρ − ½| ≤ |Im ρ − t|`. -/
theorem xiSliceGaussianRadiusHead_compl_abs_re_sub_half_le {t R : ℝ} (hR : 0 ≤ R)
    (hR2 : 1 / 2 ≤ R ^ 2) {q : XiZeroCopy} (hq : q ∉ xiSliceGaussianRadiusHead t R) :
    |(q.1 : ℂ).re - 1 / 2| ≤ |(q.1 : ℂ).im - t| := by
  have hcone := xiSliceGaussianRadiusHead_compl_cone hR hR2 hq
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
  have him : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by simp [xiSpectralPoint]
  rw [hre, him, ← sq_abs (1 / 2 - (q.1 : ℂ).re), abs_sub_comm (1 / 2) (q.1 : ℂ).re,
    ← sq_abs ((q.1 : ℂ).im - t)] at hcone
  nlinarith [abs_nonneg ((q.1 : ℂ).re - 1 / 2), abs_nonneg ((q.1 : ℂ).im - t)]

/-- The reflection involution on the complement `XiZeroCopyOff (xiSliceGaussianRadiusHead t R)`. -/
def xiZeroCopyOffLagPartner (t R : ℝ)
    (q : XiZeroCopyOff (xiSliceGaussianRadiusHead t R)) :
    XiZeroCopyOff (xiSliceGaussianRadiusHead t R) :=
  ⟨lagPartner q.1, fun h => q.2 ((mem_xiSliceGaussianRadiusHead_lagPartner_iff t R q.1).mp h)⟩

theorem xiZeroCopyOffLagPartner_involutive (t R : ℝ)
    (q : XiZeroCopyOff (xiSliceGaussianRadiusHead t R)) :
    xiZeroCopyOffLagPartner t R (xiZeroCopyOffLagPartner t R q) = q :=
  Subtype.ext (lagPartner_lagPartner q.1)

/-- For any finite set `K` closed under `lagPartner` and any real `t`, the complementary canonical
product `xiCanonicalProductOff K` has nonnegative square at `t`. -/
theorem xiCanonicalProductOff_sq_nonneg_of_closed {K : Finset XiZeroCopy}
    (hK : ∀ q ∈ K, lagPartner q ∈ K) (t : ℝ) :
    0 ≤ xiCanonicalProductOff K t ^ 2 := by
  classical
  let σ : XiZeroCopyOff K → XiZeroCopyOff K := fun q =>
    ⟨lagPartner q.1, fun h => q.2 (by
      have := hK (lagPartner q.1) h
      rwa [lagPartner_lagPartner] at this)⟩
  have hσ : ∀ q, σ (σ q) = q := fun q => Subtype.ext (lagPartner_lagPartner q.1)
  have hP : TendstoLocallyUniformlyOn
      (fun (F : Finset (XiZeroCopyOff K)) w => ∏ q ∈ F, weierstrassE1 (w / xiSpectralPoint q.1))
      (xiCanonicalProductOff K) atTop Set.univ :=
    canonicalProductE1Indexed_hasProdLocallyUniformlyOn
      (fun q : XiZeroCopyOff K => xiSpectralPoint q.1) (fun q => xiSpectralPoint_ne_zero q.1)
      (xiCanonicalProductOff_inv_sq_summable K)
  have hpt := (hP.tendsto_at (Set.mem_univ (t : ℂ))).pow 2
  let c : Finset (XiZeroCopyOff K) → Finset (XiZeroCopyOff K) := fun S => S ∪ S.image σ
  have hc : Tendsto c atTop atTop :=
    tendsto_atTop_mono (fun S => Finset.subset_union_left) tendsto_id
  have hclosed : ∀ S, ∀ a ∈ c S, σ a ∈ c S := by
    intro S a ha
    simp only [c, Finset.mem_union, Finset.mem_image] at ha ⊢
    rcases ha with ha | ⟨b, hb, rfl⟩
    · exact Or.inr ⟨a, ha, rfl⟩
    · exact Or.inl (by rw [hσ]; exact hb)
  have hlim := hpt.comp hc
  set f : XiZeroCopyOff K → ℂ → ℂ := fun q _ => weierstrassE1 ((t : ℂ) / xiSpectralPoint q.1) ^ 2
    with hf
  have hfix : ∀ q, σ q = q → NonnegTaylorAtZero (f q) := by
    intro q hq
    have hre : (q.1.1 : ℂ).re = 1 / 2 :=
      (lagPartner_fst_eq_iff q.1).mp (congrArg (fun r : XiZeroCopyOff K => (r.1.1 : ℂ)) hq)
    have hz : xiSpectralPoint q.1 = (((q.1.1 : ℂ).im : ℝ) : ℂ) := by
      rw [xiSpectralPoint_eq_re_im, hre]; simp
    have hγ : (q.1.1 : ℂ).im ≠ 0 := by
      intro h0
      apply xiSpectralPoint_ne_zero q.1
      rw [hz, h0, Complex.ofReal_zero]
    have h0 := weierstrassE1_slice_pair (t := t) hγ 0
    simp only [mul_zero, sub_zero, add_zero, ← sq] at h0
    refine nonnegTaylorAtZero_const ?_
    rw [hf, hz, h0]
    exact Complex.zero_le_real.mpr (by positivity)
  have hpair : ∀ q, σ q ≠ q → NonnegTaylorAtZero (f q * f (σ q)) := by
    intro q _
    set a : ℝ := (q.1.1 : ℂ).im with ha
    set cc : ℝ := 1 / 2 - (q.1.1 : ℂ).re with hcc
    have hz : xiSpectralPoint q.1 = (a : ℂ) + cc * I := xiSpectralPoint_eq_re_im q.1
    have hz0 : (a : ℂ) + cc * I ≠ 0 := by rw [← hz]; exact xiSpectralPoint_ne_zero q.1
    have hzσ : xiSpectralPoint (σ q).1 = starRingEnd ℂ ((a : ℂ) + cc * I) := by
      change xiSpectralPoint (lagPartner q.1) = _
      rw [xiSpectralPoint_lagPartner, hz]
    have h0 := weierstrassE1_slice_reflectionPair (t := t) hz0 0
    simp only [mul_zero, sub_zero, add_zero, zero_pow (by decide : 4 ≠ 0),
      zero_pow (by decide : 2 ≠ 0), ← sq] at h0
    refine nonnegTaylorAtZero_const ?_
    change 0 ≤ weierstrassE1 ((t : ℂ) / xiSpectralPoint q.1) ^ 2 *
      weierstrassE1 ((t : ℂ) / xiSpectralPoint (σ q).1) ^ 2
    rw [hz, hzσ, h0, ← Complex.ofReal_mul]
    exact Complex.zero_le_real.mpr (by positivity)
  refine ge_of_tendsto' hlim fun S => ?_
  have hNT := nonnegTaylorAtZero_prod_of_involution σ hσ f hfix hpair (c S) (hclosed S)
  have h0 := hNT.2 0
  simp only [iteratedDeriv_zero, hf, ← Finset.prod_pow] at h0
  exact h0

/-- For every `t, R ∈ ℝ`, `xiCanonicalProductOff (xiSliceGaussianRadiusHead t R) t ^ 2 ≥ 0`. -/
theorem xiCanonicalProductOff_radius_sq_nonneg (t R : ℝ) :
    0 ≤ xiCanonicalProductOff (xiSliceGaussianRadiusHead t R) t ^ 2 :=
  xiCanonicalProductOff_sq_nonneg_of_closed
    (fun q hq => (mem_xiSliceGaussianRadiusHead_lagPartner_iff t R q).mpr hq) t

/-- For every `t, R ∈ ℝ`, the finite-head scalar `xiSliceGaussianFiniteHeadScalar t R` is real and
nonnegative. -/
theorem xiSliceGaussianFiniteHeadScalar_nonneg (t R : ℝ) :
    0 ≤ xiSliceGaussianFiniteHeadScalar t R := by
  classical
  unfold xiSliceGaussianFiniteHeadScalar
  refine mul_nonneg (mul_nonneg (by rw [sq]; exact zero_le_XiC_zero_mul_self)
    (xiCanonicalProductOff_radius_sq_nonneg t R)) ?_
  set H := xiSliceGaussianRadiusHead t R
  set f : XiZeroCopy → ℂ → ℂ := fun q _ =>
    Complex.exp (2 * (t : ℂ) / xiSpectralPoint q) / xiSpectralPoint q ^ 2 with hf
  have hclosed : ∀ q ∈ H, lagPartner q ∈ H := fun q hq =>
    (mem_xiSliceGaussianRadiusHead_lagPartner_iff t R q).mpr hq
  have hfix : ∀ q, lagPartner q = q → NonnegTaylorAtZero (f q) := by
    intro q hq
    have hre : (q.1 : ℂ).re = 1 / 2 :=
      (lagPartner_fst_eq_iff q).mp (congrArg (fun r => (r.1 : ℂ)) hq)
    have hz : xiSpectralPoint q = (((q.1 : ℂ).im : ℝ) : ℂ) := by
      rw [xiSpectralPoint_eq_re_im, hre]; simp
    refine nonnegTaylorAtZero_const ?_
    rw [hf, hz]
    have e : Complex.exp (2 * (t : ℂ) / (((q.1 : ℂ).im : ℝ) : ℂ)) /
        (((q.1 : ℂ).im : ℝ) : ℂ) ^ 2 =
        ((Real.exp (2 * t / (q.1 : ℂ).im) / (q.1 : ℂ).im ^ 2 : ℝ) : ℂ) := by
      push_cast; rfl
    rw [e]
    exact Complex.zero_le_real.mpr (by positivity)
  have hpair : ∀ q, lagPartner q ≠ q → NonnegTaylorAtZero (f q * f (lagPartner q)) := by
    intro q _
    set a : ℝ := (q.1 : ℂ).im with ha
    set cc : ℝ := 1 / 2 - (q.1 : ℂ).re with hcc
    have hz : xiSpectralPoint q = (a : ℂ) + cc * I := xiSpectralPoint_eq_re_im q
    have hz0 : (a : ℂ) + cc * I ≠ 0 := by rw [← hz]; exact xiSpectralPoint_ne_zero q
    have hconj : starRingEnd ℂ ((a : ℂ) + cc * I) = (a : ℂ) - cc * I := by
      simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    have hzσ : xiSpectralPoint (lagPartner q) = (a : ℂ) - cc * I := by
      rw [xiSpectralPoint_lagPartner, hz, hconj]
    have hprod : ((a : ℂ) + cc * I) * ((a : ℂ) - cc * I) = (a : ℂ) ^ 2 + (cc : ℂ) ^ 2 := by
      linear_combination (-(cc : ℂ) ^ 2) * Complex.I_sq
    have hexp : cexp (2 * t / ((a : ℂ) + cc * I)) * cexp (2 * t / ((a : ℂ) - cc * I)) =
        ((Real.exp (4 * t * a / (a ^ 2 + cc ^ 2)) : ℝ) : ℂ) := by
      rw [← Complex.exp_add, Complex.ofReal_exp]
      congr 1
      push_cast
      field_simp [hz0, (show (a : ℂ) - cc * I ≠ 0 by rw [← hconj]; exact (map_ne_zero _).mpr hz0)]
      linear_combination (4 * (t : ℂ) * a) * hprod +
        (8 * (t : ℂ) * a * (cc : ℂ) ^ 2) * Complex.I_sq
    refine nonnegTaylorAtZero_const ?_
    change 0 ≤ f q 0 * f (lagPartner q) 0
    simp only [hf, hz, hzσ]
    have e : cexp (2 * (t : ℂ) / ((a : ℂ) + cc * I)) / ((a : ℂ) + cc * I) ^ 2 *
        (cexp (2 * (t : ℂ) / ((a : ℂ) - cc * I)) / ((a : ℂ) - cc * I) ^ 2) =
        (cexp (2 * (t : ℂ) / ((a : ℂ) + cc * I)) * cexp (2 * (t : ℂ) / ((a : ℂ) - cc * I))) /
          (((a : ℂ) + cc * I) * ((a : ℂ) - cc * I)) ^ 2 := by ring
    rw [e, hexp, hprod]
    have e2 : ((Real.exp (4 * t * a / (a ^ 2 + cc ^ 2)) : ℝ) : ℂ) /
        ((a : ℂ) ^ 2 + (cc : ℂ) ^ 2) ^ 2 =
        ((Real.exp (4 * t * a / (a ^ 2 + cc ^ 2)) / (a ^ 2 + cc ^ 2) ^ 2 : ℝ) : ℂ) := by
      push_cast; rfl
    rw [e2]
    exact Complex.zero_le_real.mpr (by positivity)
  have hNT := nonnegTaylorAtZero_prod_of_involution lagPartner lagPartner_lagPartner f hfix hpair
    H hclosed
  simpa [iteratedDeriv_zero, hf] using hNT.2 0

/-- For every `t ∈ ℝ` and `R ≥ 0`, `xiSliceGaussianFiniteHeadScalar t R` has strictly positive real
part and zero imaginary part. -/
theorem xiSliceGaussianFiniteHeadScalar_re_pos (t : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    0 < (xiSliceGaussianFiniteHeadScalar t R).re := by
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp (xiSliceGaussianFiniteHeadScalar_nonneg t R)
  refine lt_of_le_of_ne hre fun h0 => xiSliceGaussianFiniteHeadScalar_ne_zero t hR ?_
  exact Complex.ext h0.symm him

theorem xiSliceGaussianFiniteHeadScalar_im_eq_zero (t R : ℝ) :
    (xiSliceGaussianFiniteHeadScalar t R).im = 0 :=
  (Complex.nonneg_iff.mp (xiSliceGaussianFiniteHeadScalar_nonneg t R)).2

/-- On the real axis `z = x ∈ ℝ`, the finite head `xiSliceGaussianFiniteHead t R x` is real and
nonnegative for all `t, R, x ∈ ℝ`. -/
theorem xiSliceGaussianFiniteHead_ofReal_nonneg (t R x : ℝ) :
    0 ≤ xiSliceGaussianFiniteHead t R (x : ℂ) := by
  classical
  unfold xiSliceGaussianFiniteHead
  refine mul_nonneg (xiSliceGaussianFiniteHeadScalar_nonneg t R) ?_
  set H := xiSliceGaussianRadiusHead t R
  set f : XiZeroCopy → ℂ → ℂ := fun q _ => (x : ℂ) ^ 2 + (xiSpectralPoint q - t) ^ 2 with hf
  have hclosed : ∀ q ∈ H, lagPartner q ∈ H := fun q hq =>
    (mem_xiSliceGaussianRadiusHead_lagPartner_iff t R q).mpr hq
  have hfix : ∀ q, lagPartner q = q → NonnegTaylorAtZero (f q) := by
    intro q hq
    have hre : (q.1 : ℂ).re = 1 / 2 :=
      (lagPartner_fst_eq_iff q).mp (congrArg (fun r => (r.1 : ℂ)) hq)
    have hz : xiSpectralPoint q = (((q.1 : ℂ).im : ℝ) : ℂ) := by
      rw [xiSpectralPoint_eq_re_im, hre]; simp
    refine nonnegTaylorAtZero_const ?_
    rw [hf, hz]
    have e : (x : ℂ) ^ 2 + ((((q.1 : ℂ).im : ℝ) : ℂ) - (t : ℂ)) ^ 2 =
        ((x ^ 2 + ((q.1 : ℂ).im - t) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e]
    exact Complex.zero_le_real.mpr (by positivity)
  have hpair : ∀ q, lagPartner q ≠ q → NonnegTaylorAtZero (f q * f (lagPartner q)) := by
    intro q _
    refine nonnegTaylorAtZero_const ?_
    change 0 ≤ f q 0 * f (lagPartner q) 0
    simp only [hf]
    have hconj : (x : ℂ) ^ 2 + (xiSpectralPoint (lagPartner q) - (t : ℂ)) ^ 2 =
        starRingEnd ℂ ((x : ℂ) ^ 2 + (xiSpectralPoint q - (t : ℂ)) ^ 2) := by
      rw [xiSpectralPoint_lagPartner]
      simp [map_add, map_pow, map_sub, Complex.conj_ofReal]
    rw [hconj, Complex.mul_conj]
    exact Complex.zero_le_real.mpr (Complex.normSq_nonneg _)
  have hNT := nonnegTaylorAtZero_prod_of_involution lagPartner lagPartner_lagPartner f hfix hpair
    H hclosed
  simpa [iteratedDeriv_zero, hf] using hNT.2 0

theorem xiSliceGaussianFiniteHead_ofReal_im_eq_zero (t R x : ℝ) :
    (xiSliceGaussianFiniteHead t R (x : ℂ)).im = 0 :=
  (Complex.nonneg_iff.mp (xiSliceGaussianFiniteHead_ofReal_nonneg t R x)).2

theorem xiSliceGaussianFiniteHead_ofReal_re_nonneg (t R x : ℝ) :
    0 ≤ (xiSliceGaussianFiniteHead t R (x : ℂ)).re :=
  (Complex.nonneg_iff.mp (xiSliceGaussianFiniteHead_ofReal_nonneg t R x)).1

theorem xiSliceGaussianFiniteHead_ofReal_eq_re (t R x : ℝ) :
    xiSliceGaussianFiniteHead t R (x : ℂ) = ((xiSliceGaussianFiniteHead t R (x : ℂ)).re : ℂ) :=
  Complex.ext rfl (xiSliceGaussianFiniteHead_ofReal_im_eq_zero t R x)

theorem norm_xiSliceGaussianFiniteHead_ofReal (t R x : ℝ) :
    ‖xiSliceGaussianFiniteHead t R (x : ℂ)‖ = (xiSliceGaussianFiniteHead t R (x : ℂ)).re := by
  rw [xiSliceGaussianFiniteHead_ofReal_eq_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (xiSliceGaussianFiniteHead_ofReal_re_nonneg t R x)]

/-- **Unconditional two-sided Gaussian bracket for the full Xi slice on the real axis.**
For `R ≥ 4` and all `t, x ∈ ℝ`, the product of the real nonnegative finite head
`Q(x) = (xiSliceGaussianFiniteHead t R x).re` and the Gaussian tail background `exp(a x²)`
brackets `(xiSliceProduct t x).re` from above with relative error at most `B x⁴`. -/
theorem xiSliceProduct_real_gaussian_bracket (t : ℝ) {R : ℝ} (hR : 4 ≤ R) (x : ℝ) :
    let a := (xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R)).re
    let B := xiSliceGaussianTailFourth t (xiSliceGaussianRadiusHead t R)
    let Q := (xiSliceGaussianFiniteHead t R (x : ℂ)).re
    0 ≤ Q * Real.exp (a * x ^ 2) - (xiSliceProduct t (x : ℂ)).re ∧
      Q * Real.exp (a * x ^ 2) - (xiSliceProduct t (x : ℂ)).re ≤
        B * x ^ 4 * (Q * Real.exp (a * x ^ 2)) := by
  dsimp only
  set H := xiSliceGaussianRadiusHead t R
  set a := (xiSliceGaussianTailQuadratic t H).re
  set B := xiSliceGaussianTailFourth t H
  set Q := (xiSliceGaussianFiniteHead t R (x : ℂ)).re
  have hQ0 : 0 ≤ Q := xiSliceGaussianFiniteHead_ofReal_re_nonneg t R x
  have hT := xiSliceGaussianTail_real_eq_norm t hR x
  have hb := norm_xiSliceGaussianTail_real_bounds t hR x
  change Real.exp (x ^ 2 * a - x ^ 4 * B) ≤ ‖xiSliceGaussianTail t H (x : ℂ)‖ ∧
    ‖xiSliceGaussianTail t H (x : ℂ)‖ ≤ Real.exp (x ^ 2 * a) at hb
  rw [mul_comm (x ^ 2) a, mul_comm (x ^ 4) B] at hb
  have hprod : (xiSliceProduct t (x : ℂ)).re = Q * ‖xiSliceGaussianTail t H (x : ℂ)‖ := by
    rw [xiSliceProduct_eq_gaussianFiniteHead_mul_tail t (by linarith : 0 ≤ R) (x : ℂ),
      xiSliceGaussianFiniteHead_ofReal_eq_re, hT, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hprod]
  refine ⟨?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left hb.2 hQ0
    linarith
  · have hlow : Real.exp (a * x ^ 2) * (1 - B * x ^ 4) ≤ ‖xiSliceGaussianTail t H (x : ℂ)‖ := by
      calc Real.exp (a * x ^ 2) * (1 - B * x ^ 4)
          ≤ Real.exp (a * x ^ 2) * Real.exp (-(B * x ^ 4)) :=
            mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (-(B * x ^ 4))])
              (Real.exp_pos _).le
        _ = Real.exp (a * x ^ 2 - B * x ^ 4) := (Real.exp_add _ _).symm
        _ ≤ _ := hb.1
    have := mul_le_mul_of_nonneg_left hlow hQ0
    nlinarith

/-- **Taylor positivity of the complementary canonical product outside `R ≥ 1/√2`.**
Whenever `0 ≤ R` and `1/2 ≤ R²`, the off-head slice
`z ↦ xiCanonicalProductOff H (t − iz) * xiCanonicalProductOff H (t + iz)` has all Taylor
coefficients at `0` real and nonnegative. -/
theorem nonnegTaylorAtZero_xiCanonicalProductOff_radius (t : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hR2 : 1 / 2 ≤ R ^ 2) :
    NonnegTaylorAtZero (fun z =>
      xiCanonicalProductOff (xiSliceGaussianRadiusHead t R) ((t : ℂ) - I * z) *
        xiCanonicalProductOff (xiSliceGaussianRadiusHead t R) ((t : ℂ) + I * z)) := by
  classical
  set H := xiSliceGaussianRadiusHead t R
  set φm : ℂ → ℂ := fun x => (t : ℂ) - I * x with hφm
  set φp : ℂ → ℂ := fun x => (t : ℂ) + I * x with hφp
  have hcm : Continuous φm := by rw [hφm]; fun_prop
  have hcp : Continuous φp := by rw [hφp]; fun_prop
  have hP : TendstoLocallyUniformlyOn
      (fun (S : Finset (XiZeroCopyOff H)) x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q.1))
      (xiCanonicalProductOff H) atTop Set.univ :=
    canonicalProductE1Indexed_hasProdLocallyUniformlyOn
      (fun q : XiZeroCopyOff H => xiSpectralPoint q.1) (fun q => xiSpectralPoint_ne_zero q.1)
      (xiCanonicalProductOff_inv_sq_summable H)
  have hPdiff : Differentiable ℂ (xiCanonicalProductOff H) :=
    differentiable_xiCanonicalProductOff H
  have hPcont : Continuous (xiCanonicalProductOff H) := hPdiff.continuous
  have hm := TendstoLocallyUniformlyOn.comp hP φm (Set.mapsTo_univ φm Set.univ) hcm.continuousOn
  have hp := TendstoLocallyUniformlyOn.comp hP φp (Set.mapsTo_univ φp Set.univ) hcp.continuousOn
  have hmul := hm.mul₀ hp (hPcont.comp hcm).continuousOn (hPcont.comp hcp).continuousOn
  let σ := xiZeroCopyOffLagPartner t R
  have hσ : ∀ q, σ (σ q) = q := xiZeroCopyOffLagPartner_involutive t R
  let c : Finset (XiZeroCopyOff H) → Finset (XiZeroCopyOff H) := fun S => S ∪ S.image σ
  have hc : Tendsto c atTop atTop :=
    tendsto_atTop_mono (fun S => Finset.subset_union_left) tendsto_id
  have hclosed : ∀ S, ∀ a ∈ c S, σ a ∈ c S := by
    intro S a ha
    simp only [c, Finset.mem_union, Finset.mem_image] at ha ⊢
    rcases ha with ha | ⟨b, hb, rfl⟩
    · exact Or.inr ⟨a, ha, rfl⟩
    · exact Or.inl (by rw [hσ]; exact hb)
  have hmul' := tendstoLocallyUniformlyOn_comp_index hmul hc
  set f : XiZeroCopyOff H → ℂ → ℂ := fun q x =>
    weierstrassE1 (φm x / xiSpectralPoint q.1) * weierstrassE1 (φp x / xiSpectralPoint q.1) with hf
  have hfix : ∀ q, σ q = q → NonnegTaylorAtZero (f q) := by
    intro q hq
    have hre : (q.1.1 : ℂ).re = 1 / 2 :=
      (lagPartner_fst_eq_iff q.1).mp (congrArg (fun r : XiZeroCopyOff H => (r.1.1 : ℂ)) hq)
    have hz : xiSpectralPoint q.1 = (((q.1.1 : ℂ).im : ℝ) : ℂ) := by
      rw [xiSpectralPoint_eq_re_im, hre]; simp
    have hγ : (q.1.1 : ℂ).im ≠ 0 := by
      intro h0
      apply xiSpectralPoint_ne_zero q.1
      rw [hz, h0, Complex.ofReal_zero]
    simp only [hf, hz, hφm, hφp]
    exact nonnegTaylorAtZero_slice_pair hγ
  have hpair : ∀ q, σ q ≠ q → NonnegTaylorAtZero (f q * f (σ q)) := by
    intro q _
    set a : ℝ := (q.1.1 : ℂ).im with ha
    set cc : ℝ := 1 / 2 - (q.1.1 : ℂ).re with hcc
    have hz : xiSpectralPoint q.1 = (a : ℂ) + cc * I := xiSpectralPoint_eq_re_im q.1
    have hz0 : (a : ℂ) + cc * I ≠ 0 := by rw [← hz]; exact xiSpectralPoint_ne_zero q.1
    have hzσ : xiSpectralPoint (σ q).1 = starRingEnd ℂ ((a : ℂ) + cc * I) := by
      change xiSpectralPoint (lagPartner q.1) = _
      rw [xiSpectralPoint_lagPartner, hz]
    have e : f q * f (σ q) = fun x =>
        ((Real.exp (4 * t * a / (a ^ 2 + cc ^ 2)) / (a ^ 2 + cc ^ 2) ^ 2 : ℝ) : ℂ) *
          (x ^ 4 + ((2 * ((a - t) ^ 2 - cc ^ 2) : ℝ) : ℂ) * x ^ 2 +
            ((((a - t) ^ 2 + cc ^ 2) ^ 2 : ℝ) : ℂ)) := by
      funext x
      simp only [Pi.mul_apply, hf, hz, hzσ, hφm, hφp]
      exact weierstrassE1_slice_reflectionPair hz0 x
    rw [e]
    have hcone := xiSliceGaussianRadiusHead_compl_cone hR hR2 q.2
    have hre' : (xiSpectralPoint q.1).re = a := by simp [xiSpectralPoint, ha]
    have him' : (xiSpectralPoint q.1).im = cc := by simp [xiSpectralPoint, hcc]
    rw [hre', him'] at hcone
    exact nonnegTaylorAtZero_quartic (by positivity) (by linarith) (by positivity)
  have hfin : ∀ S : Finset (XiZeroCopyOff H), NonnegTaylorAtZero
      (((fun (S : Finset (XiZeroCopyOff H)) x =>
          ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q.1)) (c S) ∘ φm) *
        ((fun (S : Finset (XiZeroCopyOff H)) x =>
          ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q.1)) (c S) ∘ φp)) := by
    intro S
    have e : (((fun (S : Finset (XiZeroCopyOff H)) x =>
          ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q.1)) (c S) ∘ φm) *
        ((fun (S : Finset (XiZeroCopyOff H)) x =>
          ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q.1)) (c S) ∘ φp)) =
        fun x => ∏ q ∈ c S, f q x := by
      funext x
      simp only [Pi.mul_apply, Function.comp_apply, hf]
      rw [Finset.prod_mul_distrib]
    rw [e]
    exact nonnegTaylorAtZero_prod_of_involution σ hσ f hfix hpair (c S) (hclosed S)
  exact NonnegTaylorAtZero.of_tendstoLocallyUniformlyOn hfin
    ((hPdiff.comp (by rw [hφm]; fun_prop)).mul (hPdiff.comp (by rw [hφp]; fun_prop))) hmul'

/-- **Unconditional Taylor-coefficient positivity of the exact infinite tail.**
For every height `t ∈ ℝ` and cutoff radius `R ≥ 0` with `1/2 ≤ R²` (in particular `R ≥ 1/√2`,
`R ≥ 1`, `R ≥ 4`), `xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R)` is entire and all of
its Taylor coefficients at `0` are real and nonnegative. -/
theorem nonnegTaylorAtZero_xiSliceGaussianTail_radius (t : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hR2 : 1 / 2 ≤ R ^ 2) :
    NonnegTaylorAtZero (xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R)) := by
  set H := xiSliceGaussianRadiusHead t R
  have hcen : ∀ q : XiZeroCopy, xiSpectralPoint q = t → q ∈ H := by
    intro q hq
    rw [mem_xiSliceGaussianRadiusHead, hq, sub_self, norm_zero]
    exact hR
  have hPne : xiCanonicalProductOff H t ^ 2 ≠ 0 :=
    pow_ne_zero 2 (xiCanonicalProductOff_ne_zero hcen)
  have hP0 : 0 ≤ xiCanonicalProductOff H t ^ 2 := xiCanonicalProductOff_radius_sq_nonneg t R
  have hPinv : 0 ≤ (xiCanonicalProductOff H t ^ 2)⁻¹ := by
    obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hP0
    have hre_pos : 0 < (xiCanonicalProductOff H t ^ 2).re :=
      lt_of_le_of_ne hre fun h0 => hPne (Complex.ext h0.symm him)
    rw [Complex.nonneg_iff, Complex.inv_re, Complex.inv_im, ← him, neg_zero, zero_div]
    exact ⟨div_nonneg hre.le (Complex.normSq_nonneg _), rfl⟩
  have heq : xiSliceGaussianTail t H =
      (fun _ => (xiCanonicalProductOff H t ^ 2)⁻¹) *
        fun z => xiCanonicalProductOff H ((t : ℂ) - I * z) *
          xiCanonicalProductOff H ((t : ℂ) + I * z) := by
    funext z
    let e : {q : XiZeroCopy // q ∉ H} ≃ XiZeroCopyOff H :=
      { toFun := fun q => ⟨q.val, q.property⟩
        invFun := fun q => ⟨q.val, q.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hlim : HasProd (fun q : XiZeroCopyOff H => 1 + z ^ 2 * xiSliceGaussianReciprocal t q)
        (xiCanonicalProductOff H ((t : ℂ) - I * z) * xiCanonicalProductOff H ((t : ℂ) + I * z) /
          xiCanonicalProductOff H t ^ 2) := by
      simpa only [HasProd, SummationFilter.unconditional, H,
        xiSliceGaussianReciprocal, div_eq_mul_inv] using
        tendsto_prod_off_one_add_sq_div hcen z
    have htprod : xiSliceGaussianTail t H z =
        xiCanonicalProductOff H ((t : ℂ) - I * z) * xiCanonicalProductOff H ((t : ℂ) + I * z) /
          xiCanonicalProductOff H t ^ 2 :=
      (e.tprod_eq (fun q : XiZeroCopyOff H => 1 + z ^ 2 * xiSliceGaussianReciprocal t q)).trans
        hlim.tprod_eq
    simp only [Pi.mul_apply, htprod, div_eq_inv_mul]
  rw [heq]
  exact (nonnegTaylorAtZero_const hPinv).mul (nonnegTaylorAtZero_xiCanonicalProductOff_radius t hR hR2)

/-- **Lossless transfer of Taylor positivity from the finite head to the full Xi slice.**
For `R ≥ 0` with `1/2 ≤ R²`, if the retained finite-head polynomial `xiSliceGaussianFiniteHead t R`
has nonnegative Taylor coefficients at `0`, then so does the full slice `xiSliceProduct t`. -/
theorem nonnegTaylorAtZero_xiSliceProduct_of_finiteHead {t R : ℝ} (hR : 0 ≤ R)
    (hR2 : 1 / 2 ≤ R ^ 2) (hhead : NonnegTaylorAtZero (xiSliceGaussianFiniteHead t R)) :
    NonnegTaylorAtZero (xiSliceProduct t) := by
  have heq : xiSliceProduct t =
      xiSliceGaussianFiniteHead t R * xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) :=
    funext (xiSliceProduct_eq_gaussianFiniteHead_mul_tail t hR)
  rw [heq]
  exact hhead.mul (nonnegTaylorAtZero_xiSliceGaussianTail_radius t hR hR2)

/-- If the retained finite head at cutoff `R ≥ 1/√2` is Taylor-nonnegative at `0`, every Taylor
coefficient `xiSliceCoeff t n` of the full slice at height `t` is nonnegative. -/
theorem xiSliceCoeff_nonneg_of_finiteHead {t R : ℝ} (hR : 0 ≤ R) (hR2 : 1 / 2 ≤ R ^ 2)
    (hhead : NonnegTaylorAtZero (xiSliceGaussianFiniteHead t R)) (n : ℕ) :
    0 ≤ xiSliceCoeff t n := by
  unfold xiSliceCoeff
  have hfac : ((n.factorial : ℂ))⁻¹ = (((n.factorial : ℝ))⁻¹ : ℝ) := by push_cast; rfl
  rw [hfac]
  exact mul_nonneg (Complex.zero_le_real.mpr (by positivity))
    ((nonnegTaylorAtZero_xiSliceProduct_of_finiteHead hR hR2 hhead).2 n)

/-- **Local cone criterion for the retained finite head.**
If every zero copy `q ∈ xiSliceGaussianRadiusHead t R` in the retained head satisfies
`|Re ρ − ½| ≤ |Im ρ − t|`, then `xiSliceGaussianFiniteHead t R` has nonnegative Taylor coefficients
at `0`. -/
theorem nonnegTaylorAtZero_xiSliceGaussianFiniteHead_of_local_cone {t R : ℝ}
    (hcone : ∀ q ∈ xiSliceGaussianRadiusHead t R,
      |(q.1 : ℂ).re - 1 / 2| ≤ |(q.1 : ℂ).im - t|) :
    NonnegTaylorAtZero (xiSliceGaussianFiniteHead t R) := by
  classical
  set H := xiSliceGaussianRadiusHead t R
  have hclosed : ∀ q ∈ H, lagPartner q ∈ H := fun q hq =>
    (mem_xiSliceGaussianRadiusHead_lagPartner_iff t R q).mpr hq
  let σ : ↥H → ↥H := fun q => ⟨lagPartner q.1, hclosed q.1 q.2⟩
  have hσ : ∀ q : ↥H, σ (σ q) = q := fun q => Subtype.ext (lagPartner_lagPartner q.1)
  set f : ↥H → ℂ → ℂ := fun q z => z ^ 2 + (xiSpectralPoint q.1 - t) ^ 2 with hf
  have hfix : ∀ q : ↥H, σ q = q → NonnegTaylorAtZero (f q) := by
    intro q hq
    have hre : (q.1.1 : ℂ).re = 1 / 2 :=
      (lagPartner_fst_eq_iff q.1).mp (congrArg (fun r : ↥H => (r.1.1 : ℂ)) hq)
    have hz : xiSpectralPoint q.1 = (((q.1.1 : ℂ).im : ℝ) : ℂ) := by
      rw [xiSpectralPoint_eq_re_im, hre]; simp
    have e : f q = (fun x : ℂ => x) * (fun x : ℂ => x) +
        fun _ => ((((q.1.1 : ℂ).im - t) ^ 2 : ℝ) : ℂ) := by
      funext z
      simp only [hf, hz, Pi.add_apply, Pi.mul_apply]
      push_cast
      ring
    rw [e]
    exact (nonnegTaylorAtZero_id.mul nonnegTaylorAtZero_id).add
      (nonnegTaylorAtZero_const (Complex.zero_le_real.mpr (sq_nonneg _)))
  have hpair : ∀ q : ↥H, σ q ≠ q → NonnegTaylorAtZero (f q * f (σ q)) := by
    intro q _
    set a : ℝ := (q.1.1 : ℂ).im with ha
    set cc : ℝ := 1 / 2 - (q.1.1 : ℂ).re with hcc
    have hz : xiSpectralPoint q.1 = (a : ℂ) + cc * I := xiSpectralPoint_eq_re_im q.1
    have hconj : starRingEnd ℂ ((a : ℂ) + cc * I) = (a : ℂ) - cc * I := by
      simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    have hzσ : xiSpectralPoint (σ q).1 = (a : ℂ) - cc * I := by
      change xiSpectralPoint (lagPartner q.1) = _
      rw [xiSpectralPoint_lagPartner, hz, hconj]
    have e : f q * f (σ q) = fun z =>
        ((1 : ℝ) : ℂ) * (z ^ 4 + ((2 * ((a - t) ^ 2 - cc ^ 2) : ℝ) : ℂ) * z ^ 2 +
          ((((a - t) ^ 2 + cc ^ 2) ^ 2 : ℝ) : ℂ)) := by
      funext z
      simp only [Pi.mul_apply, hf, hz, hzσ, Complex.ofReal_one, one_mul]
      have hpoly := slice_reflectionPair_poly a cc t z
      linear_combination hpoly
    rw [e]
    have hsq : cc ^ 2 ≤ (a - t) ^ 2 := by
      have h := hcone q.1 q.2
      have h' : |cc| ≤ |a - t| := by
        rw [hcc, ha, abs_sub_comm]
        simpa using h
      exact sq_le_sq.mpr h'
    exact nonnegTaylorAtZero_quartic zero_le_one (by linarith) (by positivity)
  have hprod := nonnegTaylorAtZero_prod_of_involution σ hσ f hfix hpair Finset.univ
    (fun q _ => Finset.mem_univ (σ q))
  have heq : xiSliceGaussianFiniteHead t R =
      (fun _ => xiSliceGaussianFiniteHeadScalar t R) * fun z => ∏ q : ↥H, f q z := by
    funext z
    simp only [xiSliceGaussianFiniteHead, Pi.mul_apply, hf]
    rw [Finset.prod_coe_sort H (fun q => z ^ 2 + (xiSpectralPoint q - (t : ℂ)) ^ 2)]
  rw [heq]
  exact (nonnegTaylorAtZero_const (xiSliceGaussianFiniteHeadScalar_nonneg t R)).mul hprod

/-- **Under the Riemann hypothesis, the retained finite head has nonnegative Taylor coefficients at
every height `t` and every radius `R`.** -/
theorem nonnegTaylorAtZero_xiSliceGaussianFiniteHead_of_riemannHypothesis
    (hRH : RiemannHypothesis) (t R : ℝ) :
    NonnegTaylorAtZero (xiSliceGaussianFiniteHead t R) := by
  refine nonnegTaylorAtZero_xiSliceGaussianFiniteHead_of_local_cone fun q _ => ?_
  obtain ⟨γ, hγ⟩ := xiSpectralPoint_real_of_rh hRH q
  have him : (xiSpectralPoint q).im = 0 := by rw [hγ, Complex.ofReal_im]
  have hre : (q.1 : ℂ).re - 1 / 2 = 0 := by
    simp only [xiSpectralPoint, Complex.mul_im, Complex.sub_re, Complex.div_ofNat_re,
      Complex.one_re, Complex.neg_im, Complex.I_im, Complex.sub_im, Complex.div_ofNat_im,
      Complex.one_im, Complex.neg_re, Complex.I_re] at him
    linarith
  rw [hre, abs_zero]
  exact abs_nonneg _

/-- **Finite-head characterization of the Riemann hypothesis.**
For any fixed cutoff radius `R ≥ 0` with `1/2 ≤ R²` (for example `R = 1/√2`, `R = 1`, or `R = 4`),
the Riemann hypothesis holds if and only if the retained finite-head polynomial
`xiSliceGaussianFiniteHead t R` has nonnegative Taylor coefficients at `0` at every height `t ∈ ℝ`. -/
theorem riemannHypothesis_iff_forall_nonnegTaylorAtZero_xiSliceGaussianFiniteHead {R : ℝ}
    (hR : 0 ≤ R) (hR2 : 1 / 2 ≤ R ^ 2) :
    RiemannHypothesis ↔ ∀ t : ℝ, NonnegTaylorAtZero (xiSliceGaussianFiniteHead t R) :=
  ⟨fun hRH t => nonnegTaylorAtZero_xiSliceGaussianFiniteHead_of_riemannHypothesis hRH t R,
    fun h => riemannHypothesis_iff_xiSliceCoeff_nonneg.mpr fun t n =>
      xiSliceCoeff_nonneg_of_finiteHead hR hR2 (h t) n⟩

end

end RHTower
