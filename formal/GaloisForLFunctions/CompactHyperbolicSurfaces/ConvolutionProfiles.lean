import GaloisForLFunctions.CompactHyperbolicSurfaces.ResolventKernels

/-!
# Convolutions of point-pair profiles and Abel inversion

* `SL(2, ℝ)` preserves `(k ⋆ k')(z, w) = ∫ k(u(z, ξ)) k'(u(ξ, w)) dμ(ξ)` (`convK_smul`), and the
  rotations `[[α, β], [−β, α]]` fixing `i` move `iy` to every point at the same distance from `i`
  (`exists_rotSL_smul`).  Hence `k ⋆ k'` is a point-pair profile: `(k ⋆ k')(z, w) = κ(u(z, w))`
  (`convK_eq_convProfile`), and `𝒜κ = 𝒜k ∗ 𝒜k'` (`abelL_convProfile`).
* **Abel inversion.**  `∫_{c>v} Q(c) (c − v)^{−½} dc = 2π ∫_{u>v} κ(u) du` for the horocycle integrals
  `Q(c) = ∫ κ(η²/4 + c) dη` (`lintegral_tail_abel`).  So profiles with equal Abel transforms and
  finite tails agree almost everywhere on `(0, ∞)` (`ae_eq_of_abelL_eq`).
* `w ↦ u(z, w)` maps `μ` to a measure without null-set mass: `μ{w : u(z, w) ∈ N} = 0` for
  Lebesgue-null `N` (`volume_pairU_preimage_eq_zero`).
-/

open MeasureTheory Set Filter UpperHalfPlane
open scoped ENNReal MatrixGroups

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Invariance and radiality -/

theorem convK_smul (k k' : ℝ → ℝ≥0∞) (g : SL(2, ℝ)) (z w : ℍ) :
    convK k k' (g • z) (g • w) = convK k k' z w := by
  unfold convK
  have hmp := measurePreserving_smul ((g : GL (Fin 2) ℝ)) (volume : Measure ℍ)
  have e : ∀ ξ : ℍ, ((g : GL (Fin 2) ℝ)) • ξ = g • ξ := fun ξ => rfl
  rw [← hmp.lintegral_comp_emb (measurableEmbedding_const_smul _)]
  simp only [e, pairU_smul]

/-- The rotation `[[α, β], [−β, α]]` with `α² + β² = 1`. -/
def rotSL (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1) : SL(2, ℝ) :=
  ⟨!![α, β; -β, α], by rw [Matrix.det_fin_two_of]; linarith⟩

theorem coe_rotSL_smul {α β : ℝ} (h : α ^ 2 + β ^ 2 = 1) (z : ℍ) :
    ((rotSL α β h • z : ℍ) : ℂ) = (α * z + β) / (-β * z + α) := by
  rw [coe_specialLinearGroup_apply]
  simp [rotSL]

theorem rotSL_den_ne_zero {α β : ℝ} (h : α ^ 2 + β ^ 2 = 1) (z : ℍ) :
    (-β * (z : ℂ) + α) ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp only [Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, Complex.zero_im, Complex.add_re, Complex.mul_re, Complex.zero_re] at him hre
  have hz := z.im_pos
  have hβ : β = 0 := by
    have : -β * z.im = 0 := by simpa using him
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · exact absurd h1 hz.ne'
  subst hβ
  have : α = 0 := by simpa using hre
  subst this
  norm_num at h

theorem rotSL_smul_I {α β : ℝ} (h : α ^ 2 + β ^ 2 = 1) : rotSL α β h • I = I := by
  apply UpperHalfPlane.ext
  rw [coe_rotSL_smul, div_eq_iff (rotSL_den_ne_zero h I), UpperHalfPlane.coe_I]
  have : (α : ℂ) ^ 2 + (β : ℂ) ^ 2 = 1 := by exact_mod_cast h
  linear_combination (-(Complex.I) * β + α - α) * 0 + 0 * this + β * Complex.I_sq

/-- **Rotations act transitively on hyperbolic circles about `i`.** -/
theorem exists_rotSL_smul {y : ℝ} (hy : 0 < y) (w : ℍ)
    (hw : pairU I w = pairU I (hpt 0 hy)) : ∃ g : SL(2, ℝ), g • I = I ∧ g • hpt 0 hy = w := by
  have hv := w.im_pos
  -- the distance condition `y (1 + |w|²) = Im w (1 + y²)`
  have hkey : y * (1 + (w.re ^ 2 + w.im ^ 2)) = w.im * (1 + y ^ 2) := by
    rw [pairU_I_eq, pairU_I_eq] at hw
    simp only [hpt_re, hpt_im] at hw
    rw [div_eq_div_iff (by positivity) (by positivity)] at hw
    nlinarith [hw]
  set W : ℂ := w
  set ζ : ℂ := 1 + Complex.I * y * W
  set η : ℂ := W - Complex.I * y
  by_cases hζ : ζ = 0
  · refine ⟨rotSL 0 1 (by norm_num), rotSL_smul_I _, ?_⟩
    apply UpperHalfPlane.ext
    rw [coe_rotSL_smul, div_eq_iff (rotSL_den_ne_zero _ _)]
    show ((0 : ℝ) * ((⟨0, y⟩ : ℂ)) + ((1 : ℝ) : ℂ)) = W * (-((1 : ℝ) : ℂ) * (⟨0, y⟩ : ℂ) + ((0 : ℝ) : ℂ))
    have hpt : (⟨0, y⟩ : ℂ) = Complex.I * y := by apply Complex.ext <;> simp
    rw [hpt]
    push_cast
    linear_combination hζ
  · -- `η/ζ` is real
    set q : ℂ := η / ζ
    have hqim : q.im = 0 := by
      have hη : η * (starRingEnd ℂ) ζ = ⟨W.re * (1 - y * W.im) + (W.im - y) * y * W.re, 0⟩ := by
        apply Complex.ext
        · simp [η, ζ, W, Complex.mul_re, Complex.mul_im]; ring
        · simp [η, ζ, W, Complex.mul_re, Complex.mul_im]
          have : W.re = w.re := rfl
          have : W.im = w.im := rfl
          nlinarith [hkey]
      have : q = η * (starRingEnd ℂ) ζ / ((Complex.normSq ζ : ℝ) : ℂ) := by
        rw [Complex.normSq_eq_conj_mul_self, show q = η / ζ from rfl]
        field_simp
        push_cast
        ring
      rw [this, hη, Complex.div_ofReal_im]
      simp
    set r : ℝ := q.re
    have hq : q = r := Complex.ext (by simp [r]) (by simp [hqim])
    have hηr : η = r * ζ := by rw [← hq]; field_simp [q]
    set n : ℝ := Real.sqrt (1 + r ^ 2)
    have hn : 0 < n := Real.sqrt_pos.mpr (by positivity)
    have hn2 : n ^ 2 = 1 + r ^ 2 := Real.sq_sqrt (by positivity)
    have hαβ : (1 / n) ^ 2 + (r / n) ^ 2 = 1 := by
      rw [div_pow, div_pow, ← add_div, one_pow, hn2]; field_simp
    refine ⟨rotSL (1 / n) (r / n) hαβ, rotSL_smul_I _, ?_⟩
    apply UpperHalfPlane.ext
    rw [coe_rotSL_smul, div_eq_iff (rotSL_den_ne_zero _ _)]
    have hpt : ((hpt 0 hy : ℍ) : ℂ) = Complex.I * y := by
      show (⟨0, y⟩ : ℂ) = _; apply Complex.ext <;> simp
    rw [hpt]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp
    simp only [η, ζ] at hηr
    linear_combination hηr

/-- The height `Y(u) = 1 + 2u + 2√(u(u + 1))` (with `u⁺`) of the point `iY` at `u`-distance `u` from `i`. -/
def axisY (u : ℝ) : ℝ := 1 + 2 * max u 0 + 2 * Real.sqrt (max u 0 * (max u 0 + 1))

theorem axisY_pos (u : ℝ) : 0 < axisY u := by
  unfold axisY; have := le_max_right u 0; positivity

theorem continuous_axisY : Continuous axisY := by unfold axisY; fun_prop

theorem pairU_I_axisY {u : ℝ} (hu : 0 ≤ u) : pairU I (hpt 0 (axisY_pos u)) = u := by
  rw [pairU_I_eq]
  simp only [hpt_re, hpt_im]
  have hY := axisY_pos u
  rw [div_eq_iff (by positivity)]
  have hm : max u 0 = u := max_eq_left hu
  have hS := Real.sq_sqrt (show 0 ≤ u * (u + 1) by positivity)
  simp only [axisY, hm]
  nlinarith [hS]

/-- The profile of `k ⋆ k'`: its value at the pair `(i, iY(u))`. -/
def convProfile (k k' : ℝ → ℝ≥0∞) (u : ℝ) : ℝ≥0∞ := convK k k' I (hpt 0 (axisY_pos u))

/-- **The convolution is a point-pair profile.** -/
theorem convK_eq_convProfile (k k' : ℝ → ℝ≥0∞) (z w : ℍ) :
    convK k k' z w = convProfile k k' (pairU z w) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, ℝ) z I
  rw [← convK_smul k k' g, hg]
  have hu : pairU I (g • w) = pairU z w := by rw [← hg, pairU_smul]
  have hu0 : 0 ≤ pairU z w := pairU_nonneg z w
  obtain ⟨r, hrI, hrp⟩ := exists_rotSL_smul (axisY_pos (pairU z w)) (g • w)
    (by rw [hu, pairU_I_axisY hu0])
  rw [← hrp, ← convK_smul k k' r⁻¹, ← hrI]
  simp only [inv_smul_smul]
  rw [hrI]
  rfl

theorem measurable_convProfile {k k' : ℝ → ℝ≥0∞} (hk : Measurable k) (hk' : Measurable k') :
    Measurable (convProfile k k') := by
  have hc : Continuous fun u : ℝ => hpt 0 (axisY_pos u) := by
    have : (fun u : ℝ => ((hpt 0 (axisY_pos u) : ℍ) : ℂ)) = fun u => Complex.I * (axisY u : ℂ) := by
      funext u; show (⟨0, axisY u⟩ : ℂ) = _; apply Complex.ext <;> simp
    refine UpperHalfPlane.isOpenEmbedding_coe.isInducing.continuous_iff.mpr ?_
    show Continuous fun u : ℝ => ((hpt 0 (axisY_pos u) : ℍ) : ℂ)
    rw [this]; fun_prop
  have hj : Measurable fun p : ℝ × ℍ => k (pairU I p.2) * k' (pairU p.2 (hpt 0 (axisY_pos p.1))) :=
    (hk.comp (continuous_pairU.comp (continuous_const.prodMk continuous_snd)).measurable).mul
      (hk'.comp (continuous_pairU.comp (continuous_snd.prodMk (hc.comp continuous_fst))).measurable)
  exact hj.lintegral_prod_right'

/-- **Abel transforms of convolutions.**  `𝒜(k ⋆ k') = 𝒜k ∗ 𝒜k'`. -/
theorem abelL_convProfile {k k' : ℝ → ℝ≥0∞} (hk : Measurable k) (hk' : Measurable k') (τ : ℝ) :
    abelL (convProfile k k') τ = ∫⁻ σ : ℝ, abelL k σ * abelL k' (τ - σ) := by
  have hy : 0 < Real.exp τ := Real.exp_pos τ
  have h1 := lintegral_pairU_slice (convProfile k k') I hy
  have h2 := lintegral_convK_slice hk hk' hy
  simp_rw [← convK_eq_convProfile] at h1
  rw [h1] at h2
  simp only [UpperHalfPlane.I_im, one_mul, Real.log_one, sub_zero, Real.log_exp] at h2
  have hs0 : ENNReal.ofReal (Real.sqrt (Real.exp τ)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr hy)
  exact (ENNReal.mul_right_inj hs0 ENNReal.ofReal_ne_top).mp h2

/-! ### Abel inversion -/

/-- **The tail identity.**  `∫_{c>v} Q(c)(c − v)^{−½} dc = 2π ∫_{u>v} κ(u) du`,
`Q(c) = ∫ κ(η²/4 + c) dη`. -/
theorem lintegral_tail_abel {κ : ℝ → ℝ≥0∞} (hκ : Measurable κ) (v : ℝ) :
    ∫⁻ c in Ioi v, (∫⁻ η : ℝ, κ (η ^ 2 / 4 + c)) * ENNReal.ofReal (Real.sqrt (c - v))⁻¹ =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ u in Ioi v, κ u := by
  set m : ℝ → ℝ≥0∞ := fun c => ENNReal.ofReal (Real.sqrt (c - v))⁻¹
  have hm : Measurable m := by fun_prop
  -- step 1: the double integral over `(c, η)`
  have hJ : Measurable fun p : ℝ × ℝ =>
      (Ioi v).indicator (fun c => κ (p.2 ^ 2 / 4 + c) * m c) p.1 := by
    have : (fun p : ℝ × ℝ => (Ioi v).indicator (fun c => κ (p.2 ^ 2 / 4 + c) * m c) p.1) =
        {p : ℝ × ℝ | v < p.1}.indicator (fun p => κ (p.2 ^ 2 / 4 + p.1) * m p.1) := by
      funext p; simp only [indicator_apply, mem_Ioi, mem_setOf_eq]
    rw [this]
    exact ((hκ.comp (by fun_prop)).mul (hm.comp measurable_fst)).indicator
      (measurableSet_lt measurable_const measurable_fst)
  have e1 : ∫⁻ c in Ioi v, (∫⁻ η : ℝ, κ (η ^ 2 / 4 + c)) * m c =
      ∫⁻ c : ℝ, ∫⁻ η : ℝ, (Ioi v).indicator (fun c => κ (η ^ 2 / 4 + c) * m c) c := by
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun c => ?_
    by_cases hc : v < c
    · simp only [indicator_of_mem (show c ∈ Ioi v from hc)]
      exact (lintegral_mul_const _ (hκ.comp (by fun_prop))).symm
    · simp only [indicator_of_notMem (show c ∉ Ioi v from hc), lintegral_zero]
  rw [e1, lintegral_lintegral_swap hJ.aemeasurable]
  -- step 2: translate `c = u − η²/4`
  have e2 : ∀ η : ℝ, ∫⁻ c : ℝ, (Ioi v).indicator (fun c => κ (η ^ 2 / 4 + c) * m c) c =
      ∫⁻ u : ℝ, (Ioi (v + η ^ 2 / 4)).indicator
        (fun u => κ u * ENNReal.ofReal (Real.sqrt (u - v - η ^ 2 / 4))⁻¹) u := by
    intro η
    rw [← lintegral_add_right_eq_self _ (η ^ 2 / 4)]
    refine lintegral_congr fun u => ?_
    simp only [indicator_apply, mem_Ioi, m]
    by_cases hu : v < u - η ^ 2 / 4
    · rw [if_pos hu, if_pos (by linarith)]
      congr 2
      · ring_nf
      · ring_nf
    · rw [if_neg hu, if_neg (by intro h; exact hu (by linarith))]
  simp_rw [e2]
  have hK : Measurable fun p : ℝ × ℝ => (Ioi (v + p.1 ^ 2 / 4)).indicator
      (fun u => κ u * ENNReal.ofReal (Real.sqrt (u - v - p.1 ^ 2 / 4))⁻¹) p.2 := by
    have : (fun p : ℝ × ℝ => (Ioi (v + p.1 ^ 2 / 4)).indicator
        (fun u => κ u * ENNReal.ofReal (Real.sqrt (u - v - p.1 ^ 2 / 4))⁻¹) p.2) =
        {p : ℝ × ℝ | v + p.1 ^ 2 / 4 < p.2}.indicator
          (fun p => κ p.2 * ENNReal.ofReal (Real.sqrt (p.2 - v - p.1 ^ 2 / 4))⁻¹) := by
      funext p; simp only [indicator_apply, mem_Ioi, mem_setOf_eq]
    rw [this]
    exact ((hκ.comp measurable_snd).mul (by fun_prop)).indicator
      (measurableSet_lt (by fun_prop) measurable_snd)
  rw [lintegral_lintegral_swap hK.aemeasurable, ← lintegral_indicator measurableSet_Ioi,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- step 3: the arcsine integral in `η`
  refine lintegral_congr fun u => ?_
  by_cases hu : v < u
  · rw [indicator_of_mem (show u ∈ Ioi v from hu)]
    have hA : 0 < u - v := by linarith
    have hmeas : Measurable fun η : ℝ => (Ioo (-(2 * Real.sqrt (u - v))) (2 * Real.sqrt (u - v))).indicator
        (fun η => ENNReal.ofReal (Real.sqrt (u - v - η ^ 2 / 4))⁻¹) η :=
      (by fun_prop : Measurable fun η : ℝ => ENNReal.ofReal (Real.sqrt (u - v - η ^ 2 / 4))⁻¹).indicator
        measurableSet_Ioo
    rw [mul_comm, ← lintegral_arcsine hA, ← lintegral_const_mul _ hmeas]
    refine lintegral_congr fun η => ?_
    simp only [indicator_apply, mem_Ioi, mem_Ioo]
    by_cases hη : η ^ 2 / 4 < u - v
    · have h1 : v + η ^ 2 / 4 < u := by linarith
      have h2 : -(2 * Real.sqrt (u - v)) < η ∧ η < 2 * Real.sqrt (u - v) := by
        have h3 : η ^ 2 < (2 * Real.sqrt (u - v)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hA.le]; linarith
        exact abs_lt.mp (abs_lt_of_sq_lt_sq h3 (by positivity))
      rw [if_pos h1, if_pos h2]
    · have h1 : ¬ v + η ^ 2 / 4 < u := by intro h; exact hη (by linarith)
      have h2 : ¬ (-(2 * Real.sqrt (u - v)) < η ∧ η < 2 * Real.sqrt (u - v)) := by
        rintro ⟨h4, h5⟩
        have h6 : |η| < 2 * Real.sqrt (u - v) := abs_lt.mpr ⟨h4, h5⟩
        have h7 : η ^ 2 < (2 * Real.sqrt (u - v)) ^ 2 := by
          rw [← sq_abs]; exact pow_lt_pow_left₀ h6 (abs_nonneg _) two_ne_zero
        rw [mul_pow, Real.sq_sqrt hA.le] at h7
        exact hη (by linarith)
      rw [if_neg h1, if_neg h2, mul_zero]
  · rw [indicator_of_notMem (show u ∉ Ioi v from hu), mul_zero]
    refine lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun η => ?_)
    have : ¬ v + η ^ 2 / 4 < u := by intro h; exact hu (by nlinarith [sq_nonneg η])
    simp only [indicator_apply, mem_Ioi, this, if_false, Pi.zero_apply]

/-- **Abel inversion.**  Profiles with equal Abel transforms and finite tails agree a.e. on
`(0, ∞)`. -/
theorem ae_eq_of_abelL_eq {κ κ' : ℝ → ℝ≥0∞} (hκ : Measurable κ) (hκ' : Measurable κ')
    (h : ∀ τ, abelL κ τ = abelL κ' τ) (hfin : ∀ v : ℝ, 0 < v → ∫⁻ u in Ioi v, κ' u < ∞) :
    κ =ᵐ[volume.restrict (Ioi 0)] κ' := by
  have hQ : ∀ c : ℝ, 0 ≤ c → ∫⁻ η : ℝ, κ (η ^ 2 / 4 + c) = ∫⁻ η : ℝ, κ' (η ^ 2 / 4 + c) := by
    intro c hc
    have hτ : Real.sinh (2 * Real.arsinh (Real.sqrt c) / 2) ^ 2 = c := by
      rw [mul_div_cancel_left₀ _ two_ne_zero, Real.sinh_arsinh, Real.sq_sqrt hc]
    have := h (2 * Real.arsinh (Real.sqrt c))
    simp only [abelL, hτ] at this
    exact this
  have htail : ∀ v : ℝ, 0 ≤ v → ∫⁻ u in Ioi v, κ u = ∫⁻ u in Ioi v, κ' u := by
    intro v hv
    have h1 := lintegral_tail_abel hκ v
    have h2 := lintegral_tail_abel hκ' v
    have h3 : ∫⁻ c in Ioi v, (∫⁻ η : ℝ, κ (η ^ 2 / 4 + c)) * ENNReal.ofReal (Real.sqrt (c - v))⁻¹ =
        ∫⁻ c in Ioi v, (∫⁻ η : ℝ, κ' (η ^ 2 / 4 + c)) * ENNReal.ofReal (Real.sqrt (c - v))⁻¹ :=
      setLIntegral_congr_fun measurableSet_Ioi fun c hc => by
        rw [hQ c (le_trans hv (le_of_lt hc))]
    rw [h1, h2] at h3
    have h0 : ENNReal.ofReal (2 * Real.pi) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
    exact (ENNReal.mul_right_inj h0 ENNReal.ofReal_ne_top).mp h3
  have hloc : ∀ n : ℕ, κ =ᵐ[volume.restrict (Ioi (1 / ((n : ℝ) + 1)))] κ' := by
    intro n
    set v₀ : ℝ := 1 / ((n : ℝ) + 1)
    have hv₀ : 0 < v₀ := by positivity
    set μ := volume.restrict (Ioi v₀)
    have hfin' : ∫⁻ u in Ioi v₀, κ u < ∞ := (htail v₀ hv₀.le) ▸ hfin v₀ hv₀
    haveI : IsFiniteMeasure (μ.withDensity κ) := by
      refine ⟨?_⟩
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact hfin'
    have hext : μ.withDensity κ = μ.withDensity κ' := by
      refine Measure.ext_of_generate_finite (range Ioi)
        (BorelSpace.measurable_eq.trans borel_eq_generateFrom_Ioi) isPiSystem_Ioi ?_ ?_
      · rintro _ ⟨v, rfl⟩
        rw [withDensity_apply _ measurableSet_Ioi, withDensity_apply _ measurableSet_Ioi,
          Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi]
        exact htail _ (le_trans hv₀.le (le_sup_right))
      · rw [withDensity_apply _ MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
          Measure.restrict_univ, Measure.restrict_univ]
        exact htail v₀ hv₀.le
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hκ hκ' fun t ht _ => ?_
    rw [← withDensity_apply _ ht, ← withDensity_apply _ ht, hext]
  have hU : Ioi (0 : ℝ) = ⋃ n : ℕ, Ioi (1 / ((n : ℝ) + 1)) := by
    ext u
    simp only [mem_Ioi, mem_iUnion]
    constructor
    · intro hu
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hu
      exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩
      exact lt_trans (by positivity) hn
  rw [hU, EventuallyEq, ae_restrict_iUnion_iff]
  exact hloc

/-! ### Null sets -/

/-- `{η : η²/4 + c ∈ N}` is null when `N` is. -/
theorem volume_setOf_sq_add_mem (c : ℝ) {N : Set ℝ} (hN : MeasurableSet N) (h0 : volume N = 0) :
    volume {η : ℝ | η ^ 2 / 4 + c ∈ N} = 0 := by
  set φ : ℝ → ℝ := fun η => η ^ 2 / 4 + c
  set S := {η : ℝ | η ^ 2 / 4 + c ∈ N}
  have hSm : MeasurableSet S := hN.preimage (by fun_prop)
  have hpos : volume (S ∩ Ioi 0) = 0 := by
    have hd : ∀ η ∈ Ioi (0 : ℝ), HasDerivWithinAt φ (η / 2) (Ioi 0) η := by
      intro η _
      have := ((hasDerivAt_pow 2 η).div_const 4).add_const c
      exact (this.congr_deriv (by push_cast; ring)).hasDerivWithinAt
    have hinj : InjOn φ (Ioi 0) := by
      intro a ha b hb hab
      have ha' : (0:ℝ) < a := ha
      have hb' : (0:ℝ) < b := hb
      simp only [φ] at hab
      nlinarith [hab]
    have h1 := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hd hinj
      (N.indicator (1 : ℝ → ℝ≥0∞))
    have h2 : ∫⁻ x in φ '' Ioi 0, N.indicator (1 : ℝ → ℝ≥0∞) x = 0 := by
      refine le_antisymm ((setLIntegral_le_lintegral _ _).trans ?_) (zero_le _)
      rw [lintegral_indicator_one hN, h0]
    rw [h2] at h1
    have h3 : ∀ᵐ η ∂(volume.restrict (Ioi (0 : ℝ))),
        ENNReal.ofReal |η / 2| * N.indicator (1 : ℝ → ℝ≥0∞) (φ η) = 0 :=
      (lintegral_eq_zero_iff (by fun_prop)).mp h1.symm
    rw [inter_comm, ← Measure.restrict_apply hSm, ← lintegral_indicator_one hSm]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [h3, ae_restrict_mem measurableSet_Ioi] with η hη hη0
    have hη0' : (0:ℝ) < η := hη0
    rcases mul_eq_zero.mp hη with h | h
    · exfalso
      rw [ENNReal.ofReal_eq_zero, abs_of_pos (by linarith)] at h
      linarith
    · simp only [indicator_apply, Pi.one_apply, Pi.zero_apply] at h ⊢
      by_cases hS : η ∈ S
      · exact absurd h (by simp [φ, show η ^ 2 / 4 + c ∈ N from hS])
      · simp [hS]
  have hneg : S ∩ Iio 0 = (fun η => -1 * η) ⁻¹' (S ∩ Ioi 0) := by
    ext η
    simp only [mem_inter_iff, mem_preimage, mem_Iio, mem_Ioi, S, mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by rwa [show (-1 * η) ^ 2 = η ^ 2 by ring], by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by rwa [show (-1 * η) ^ 2 = η ^ 2 by ring] at h1, by linarith⟩
  have hneg0 : volume (S ∩ Iio 0) = 0 := by
    rw [hneg, Real.volume_preimage_mul_left (by norm_num), hpos, mul_zero]
  have hsub : S ⊆ (S ∩ Ioi 0) ∪ (S ∩ Iio 0) ∪ {0} := by
    intro η hη
    rcases lt_trichotomy η 0 with h | h | h
    · exact Or.inl (Or.inr ⟨hη, h⟩)
    · exact Or.inr h
    · exact Or.inl (Or.inl ⟨hη, h⟩)
  refine le_antisymm ((measure_mono hsub).trans ?_) (zero_le _)
  refine (measure_union_le _ _).trans ?_
  rw [Real.volume_singleton, add_zero]
  exact (measure_union_le _ _).trans (by rw [hpos, hneg0, add_zero])

theorem measurableSet_pairU_mem (z : ℍ) {N : Set ℝ} (hN : MeasurableSet N) :
    MeasurableSet {w : ℍ | pairU z w ∈ N} :=
  hN.preimage (continuous_pairU.comp (continuous_const.prodMk continuous_id)).measurable

/-- **No null-set mass.**  `μ{w : u(z, w) ∈ N} = 0` for every Lebesgue-null measurable `N`. -/
theorem volume_pairU_preimage_eq_zero (z : ℍ) {N : Set ℝ} (hN : MeasurableSet N)
    (h0 : volume N = 0) : volume {w : ℍ | pairU z w ∈ N} = 0 := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, ℝ) I z
  have hset : {w : ℍ | pairU z w ∈ N} = (fun w => g⁻¹ • w) ⁻¹' {w : ℍ | pairU I w ∈ N} := by
    ext w
    simp only [mem_setOf_eq, mem_preimage]
    rw [← hg, ← pairU_smul g⁻¹, inv_smul_smul]
  have hmp := measurePreserving_smul (((g⁻¹ : SL(2, ℝ)) : GL (Fin 2) ℝ)) (volume : Measure ℍ)
  rw [hset, show (fun w : ℍ => g⁻¹ • w) = fun w => ((g⁻¹ : SL(2, ℝ)) : GL (Fin 2) ℝ) • w from rfl,
    hmp.measure_preimage (measurableSet_pairU_mem I hN).nullMeasurableSet]
  have hk : Measurable (N.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hN
  rw [← lintegral_indicator_one (measurableSet_pairU_mem I hN)]
  have : (fun w : ℍ => {w : ℍ | pairU I w ∈ N}.indicator 1 w) =
      fun w => N.indicator (1 : ℝ → ℝ≥0∞) (pairU I w) := by
    funext w; simp only [indicator_apply, mem_setOf_eq, Pi.one_apply]
  rw [this, lintegral_pairU_I hk]
  refine lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun τ => ?_)
  have habel : abelL (N.indicator (1 : ℝ → ℝ≥0∞)) τ = 0 := by
    have hm : MeasurableSet {η : ℝ | η ^ 2 / 4 + Real.sinh (τ / 2) ^ 2 ∈ N} :=
      hN.preimage (by fun_prop)
    rw [abelL, ← volume_setOf_sq_add_mem (Real.sinh (τ / 2) ^ 2) hN h0,
      ← lintegral_indicator_one hm]
    refine lintegral_congr fun η => ?_
    simp only [indicator_apply, mem_setOf_eq, Pi.one_apply]
  simp only [habel, mul_zero, Pi.zero_apply]

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
end

end GaloisForLFunctions.CompactHyperbolicSurfaces
