import GaloisForLFunctions.RHTower.HyperbolicPointPairFormHorocyclicFibreDecomposition
import GaloisForLFunctions.RHTower.HyperbolicPointPairPositiveDefiniteNecessity

/-!
# The Mehler–Fock dictionary for point-pair kernels

For a continuous point-pair kernel `k` of compact support on `ℍ`, with Selberg transform `h_k` and
Abel transform `𝒜k`, the following are equivalent:

1. `k` is positive definite: `Re ∫∫ k(u(z, w)) g(z) ḡ(w) ≥ 0` for every continuous compactly
   supported `g` on `ℍ`;
2. `Re h_k(½ + iτ) ≥ 0` for every real `τ`;
3. `𝒜k` lies in the Bochner cone of positive definite functions on `ℝ`.

(1) ⇒ (3) is `isBochnerPositive_abelTransform` (horocyclic packets) and (3) ⇒ (2) is
`h_k(½ + iτ) = ∫ 𝒜k(v) cos(τv) dv`.  Here (2) ⇒ (1) is completed: for tests with smooth zero
extension it is `re_pointPairForm_nonneg_of_contDiff` (horocyclic Fourier analysis plus
Kontorovich–Lebedev inversion on every fibre); a general test is a uniform limit of such tests
vanishing off one compact set (`exists_contDiff_approximation`), along which the form is continuous
(`tendsto_pointPairForm`).
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane Metric
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate ContDiff

noncomputable section

namespace GaloisForLFunctions.RHTower.MehlerFock

open DeckPointPair

/-! ### Smooth approximation of tests -/

/-- **Smooth approximation.**  A continuous compactly supported `g` on `ℍ` is the uniform limit,
at rate `1/(n + 1)`, of continuous tests `G n` with smooth zero extensions, all vanishing off one
compact set `K` off which `g` vanishes too. -/
theorem exists_contDiff_approximation {g : ℍ → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    ∃ K : Set ℍ, IsCompact K ∧ (∀ z ∉ K, g z = 0) ∧ ∃ G : ℕ → ℍ → ℂ,
      (∀ n, Continuous (G n)) ∧ (∀ n, HasCompactSupport (G n)) ∧
      (∀ n, ContDiff ℝ ∞ (zeroExtendC (G n))) ∧ (∀ n, ∀ z ∉ K, G n z = 0) ∧
      ∀ n z, ‖G n z - g z‖ ≤ 1 / (n + 1) := by
  obtain ⟨a, b, X, ha, hX, hbox⟩ := exists_support_box_zeroExtendC hgc
  have hF : Continuous (zeroExtendC g) := continuous_zeroExtendC hg hgc
  have hFu : UniformContinuous (zeroExtendC g) :=
    (hasCompactSupport_zeroExtendC hgc).uniformContinuous_of_continuous hF
  -- the compact box `C ⊂ {Im > 0}` and its image `K ⊂ ℍ`
  set C : Set ℂ := Icc (-(X + 1)) (X + 1) ×ℂ Icc (a / 2) (b + 1) with hCdef
  have hC : IsCompact C := isCompact_Icc.reProdIm isCompact_Icc
  have hCpos : C ⊆ {w : ℂ | 0 < w.im} := fun w hw => by
    have := hw.2.1
    simp only [mem_setOf_eq]
    linarith
  have hK : IsCompact (ofComplex '' C) :=
    hC.image_of_continuousOn (continuousOn_ofComplex_of_im_pos.mono hCpos)
  have hmemK : ∀ z : ℍ, (z : ℂ) ∈ C → z ∈ ofComplex '' C := fun z hz =>
    ⟨z, hz, by rw [ofComplex_apply_of_im_pos z.im_pos]⟩
  -- the box contains every point at distance `< min(a/2, 1)` from the support
  have hnear : ∀ {w x : ℂ}, dist x w < min (a / 2) 1 → zeroExtendC g x ≠ 0 → w ∈ C := by
    intro w x hxw hx
    obtain ⟨h1, h2, h3⟩ := hbox x hx
    have hre : |x.re - w.re| < min (a / 2) 1 :=
      lt_of_le_of_lt (by rw [← Complex.sub_re, dist_eq_norm]; exact Complex.abs_re_le_norm _) hxw
    have him : |x.im - w.im| < min (a / 2) 1 :=
      lt_of_le_of_lt (by rw [← Complex.sub_im, dist_eq_norm]; exact Complex.abs_im_le_norm _) hxw
    have hm1 := min_le_left (a / 2) 1
    have hm2 := min_le_right (a / 2) 1
    rw [abs_lt] at hre him
    rw [abs_le] at h3
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hgK : ∀ z ∉ ofComplex '' C, g z = 0 := fun z hz => by
    by_contra h
    exact hz (hmemK z (hnear (dist_self (z : ℂ) ▸ lt_min (by positivity) one_pos)
      (by rwa [zeroExtendC_apply])))
  -- smooth approximants on `ℂ`
  have hstep : ∀ n : ℕ, ∃ Gc : ℂ → ℂ, ContDiff ℝ ∞ Gc ∧
      (∀ w, ‖Gc w - zeroExtendC g w‖ ≤ 1 / (n + 1)) ∧ ∀ w ∉ C, Gc w = 0 := by
    intro n
    obtain ⟨δ, hδ, hδF⟩ := Metric.uniformContinuous_iff.mp hFu (1 / (n + 1)) (by positivity)
    have hε : 0 < min δ (min (a / 2) 1) := lt_min hδ (lt_min (by positivity) one_pos)
    obtain ⟨Gc, hGs, hGc⟩ := hF.exists_contDiff_dist_le_of_forall_mem_ball_dist_le hε
    refine ⟨Gc, hGs, fun w => ?_, fun w hw => ?_⟩
    · rw [← dist_eq_norm]
      exact hGc w _ fun x hx => (hδF (lt_of_lt_of_le (mem_ball.mp hx) (min_le_left _ _))).le
    · have hzero : ∀ x ∈ ball w (min δ (min (a / 2) 1)), zeroExtendC g x = 0 := fun x hx => by
        by_contra h
        exact hw (hnear (lt_of_lt_of_le (mem_ball.mp hx) (min_le_right _ _)) h)
      have h0 := hGc w 0 fun x hx => by
        rw [hzero x hx, hzero w (mem_ball_self hε), dist_self]
      rw [dist_le_zero.mp h0, hzero w (mem_ball_self hε)]
  choose Gc hGs hGb hG0 using hstep
  refine ⟨ofComplex '' C, hK, hgK, fun n z => Gc n z, fun n => (hGs n).continuous.comp
    continuous_coe, fun n => HasCompactSupport.intro hK fun z hz =>
      hG0 n z fun h => hz (hmemK z h), fun n => ?_, fun n z hz => hG0 n z fun h => hz (hmemK z h),
    fun n z => by simpa only [zeroExtendC_apply] using hGb n z⟩
  have hext : zeroExtendC (fun z : ℍ => Gc n z) = Gc n := funext fun w => by
    by_cases hw : 0 < w.im
    · rw [zeroExtendC_of_im_pos _ hw, ofComplex_apply_of_im_pos hw]
    · rw [zeroExtendC_of_im_nonpos _ (not_lt.mp hw), hG0 n w fun h => hw (hCpos h)]
  rw [hext]
  exact hGs n

/-! ### Continuity of the form -/

section Continuity

variable {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k) (hkR : KernelSupport k R)
include hkc hkR

/-- **Continuity of the form** under uniform convergence of tests vanishing off a fixed compact
set: `|Q_k(G_n) − Q_k(g)| ≤ μ(K)² M (2C + 1) / (n + 1)`. -/
theorem tendsto_pointPairForm {g : ℍ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {K : Set ℍ} (hK : IsCompact K) (hgK : ∀ z ∉ K, g z = 0) {G : ℕ → ℍ → ℂ}
    (hG : ∀ n, Continuous (G n)) (hGc : ∀ n, HasCompactSupport (G n))
    (hGK : ∀ n, ∀ z ∉ K, G n z = 0) (hGg : ∀ n z, ‖G n z - g z‖ ≤ 1 / (n + 1)) :
    Tendsto (fun n => pointPairForm k (G n)) atTop (𝓝 (pointPairForm k g)) := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_kernelSupport hkc hkR
  obtain ⟨Cg, hCg0, hCg⟩ := exists_norm_le_of_compactSupport hg hgc
  have hKm : MeasurableSet K := hK.measurableSet
  have hind : ∀ c : ℝ, Integrable (K.indicator fun _ => c) := fun c =>
    (integrable_indicator_iff hKm).mpr (integrableOn_const hK.measure_lt_top.ne (by simp))
  have hintI : ∀ c : ℝ, ∫ z, K.indicator (fun _ => c) z = (volume : Measure ℍ).real K * c :=
    fun c => by rw [integral_indicator_const _ hKm, smul_eq_mul]
  set m := (volume : Measure ℍ).real K
  -- `Q(f) = ∫ f(z) H_f(z)` with `H_f(z) = ∫ k(u(z, w)) f̄(w)`
  have hQ : ∀ f : ℍ → ℂ, pointPairForm k f =
      ∫ z, f z * ∫ w, ((k (pairU z w) : ℝ) : ℂ) * conj (f w) := fun f => by
    rw [pointPairForm]
    congr 1 with z
    rw [← integral_const_mul]
    congr 1 with w
    ring
  have hHb : ∀ (f : ℍ → ℂ) (c : ℝ), (∀ w, ‖f w‖ ≤ c) → (∀ w ∉ K, f w = 0) → ∀ z,
      ‖∫ w, ((k (pairU z w) : ℝ) : ℂ) * conj (f w)‖ ≤ m * (M * c) := by
    intro f c hfc hfK z
    refine (norm_integral_le_of_norm_le (hind (M * c)) (Eventually.of_forall fun w => ?_)).trans_eq
      (hintI _)
    by_cases hw : w ∈ K
    · rw [indicator_of_mem hw, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hM _ (pairU_nonneg z w)) (hfc w) (norm_nonneg _) hM0
    · rw [indicator_of_notMem hw, hfK w hw, map_zero, mul_zero, norm_zero]
  have hdiff : ∀ n : ℕ, ‖pointPairForm k (G n) - pointPairForm k g‖ ≤
      m * (m * (M * (2 * Cg + 1))) * (1 / (n + 1)) := by
    intro n
    have hε0 : (0 : ℝ) ≤ 1 / (n + 1) := by positivity
    have hε1 : (1 : ℝ) / (n + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [n.cast_nonneg (α := ℝ)]
    have hGb : ∀ w, ‖G n w‖ ≤ Cg + 1 := fun w =>
      calc ‖G n w‖ = ‖(G n w - g w) + g w‖ := by rw [sub_add_cancel]
        _ ≤ ‖G n w - g w‖ + ‖g w‖ := norm_add_le _ _
        _ ≤ 1 + Cg := add_le_add ((hGg n w).trans hε1) (hCg w)
        _ = Cg + 1 := by ring
    have hHd : ∀ z, (∫ w, ((k (pairU z w) : ℝ) : ℂ) * conj (G n w)) -
        ∫ w, ((k (pairU z w) : ℝ) : ℂ) * conj (g w) =
          ∫ w, ((k (pairU z w) : ℝ) : ℂ) * conj (G n w - g w) := fun z => by
      rw [← integral_sub (integrable_pairKernel_conj hkc hkR (hG n) z)
        (integrable_pairKernel_conj hkc hkR hg z)]
      congr 1 with w
      rw [map_sub]
      ring
    rw [hQ, hQ, ← integral_sub (integrable_mul_innerIntegral hkc hkR (hG n) (hGc n))
      (integrable_mul_innerIntegral hkc hkR hg hgc)]
    refine (norm_integral_le_of_norm_le (hind (m * (M * (2 * Cg + 1)) * (1 / (n + 1))))
      (Eventually.of_forall fun z => ?_)).trans_eq (by rw [hintI]; ring)
    by_cases hz : z ∈ K
    · rw [indicator_of_mem hz]
      have h1 := hHb (G n) (Cg + 1) hGb (hGK n) z
      have h2 := hHb (fun w => G n w - g w) (1 / (n + 1)) (hGg n)
        (fun w hw => by simp [hGK n w hw, hgK w hw]) z
      have hsplit : G n z * (∫ w, ((k (pairU z w) : ℝ) : ℂ) * conj (G n w)) -
          g z * ∫ w, ((k (pairU z w) : ℝ) : ℂ) * conj (g w) =
          (G n z - g z) * (∫ w, ((k (pairU z w) : ℝ) : ℂ) * conj (G n w)) +
            g z * ∫ w, ((k (pairU z w) : ℝ) : ℂ) * conj (G n w - g w) := by
        rw [← hHd]
        ring
      rw [hsplit]
      calc _ ≤ ‖(G n z - g z) * ∫ w, ((k (pairU z w) : ℝ) : ℂ) * conj (G n w)‖ +
            ‖g z * ∫ w, ((k (pairU z w) : ℝ) : ℂ) * conj (G n w - g w)‖ := norm_add_le _ _
        _ ≤ 1 / (n + 1) * (m * (M * (Cg + 1))) + Cg * (m * (M * (1 / (n + 1)))) := by
            rw [norm_mul, norm_mul]
            gcongr
            · exact hGg n z
            · exact hCg z
        _ = m * (M * (2 * Cg + 1)) * (1 / (n + 1)) := by ring
    · rw [indicator_of_notMem hz, hGK n z hz, hgK z hz]
      simp
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) hdiff ?_
  simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (m * (m * (M * (2 * Cg + 1))))

/-! ### The dictionary -/

/-- **Sufficiency.**  A kernel whose Selberg transform has nonnegative real part on the critical
line is positive definite. -/
theorem isPositiveDefinitePointPair_of_re_selbergTransform_nonneg
    (hh : ∀ τ : ℝ, 0 ≤ (selbergTransform k (1 / 2 + τ * Complex.I)).re) :
    IsPositiveDefinitePointPair k := by
  intro g hg hgc
  obtain ⟨K, hK, hgK, G, hG, hGc, hGs, hGK, hGg⟩ := exists_contDiff_approximation hg hgc
  exact ge_of_tendsto ((Complex.continuous_re.tendsto _).comp
    (tendsto_pointPairForm hkc hkR hg hgc hK hgK hG hGc hGK hGg))
    (Eventually.of_forall fun n => re_pointPairForm_nonneg_of_contDiff hkc hkR (hG n) (hGc n)
      (hGs n) hh)

/-- **The Mehler–Fock dictionary, spectral form.**  `k` is positive definite iff
`Re h_k(½ + iτ) ≥ 0` for every real `τ`. -/
theorem isPositiveDefinitePointPair_iff_re_selbergTransform_nonneg :
    IsPositiveDefinitePointPair k ↔
      ∀ τ : ℝ, 0 ≤ (selbergTransform k (1 / 2 + τ * Complex.I)).re :=
  ⟨fun hpd => selbergTransform_critical_re_nonneg hkc hkR hpd,
    isPositiveDefinitePointPair_of_re_selbergTransform_nonneg hkc hkR⟩

/-- **The Mehler–Fock dictionary, Abel form.**  `k` is positive definite iff its Abel transform
lies in the Bochner cone. -/
theorem isPositiveDefinitePointPair_iff_isBochnerPositive :
    IsPositiveDefinitePointPair k ↔ IsBochnerPositive (abelTransform k) :=
  ⟨isBochnerPositive_abelTransform hkc hkR, fun hB =>
    isPositiveDefinitePointPair_of_re_selbergTransform_nonneg hkc hkR fun τ => by
      rw [selbergTransform_critical_eq_ofReal hkc hkR, Complex.ofReal_re]
      exact integral_mul_cos_nonneg_of_isBochnerPositive (continuous_abelTransform hkc hkR)
        (hasCompactSupport_abelTransform hkR) hB τ⟩

end Continuity

end GaloisForLFunctions.RHTower.MehlerFock
