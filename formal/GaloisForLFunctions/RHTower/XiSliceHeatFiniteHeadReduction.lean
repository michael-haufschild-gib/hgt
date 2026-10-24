import GaloisForLFunctions.RHTower.XiSliceGaussianFiniteHeadPositivity
import GaloisForLFunctions.RHTower.XiSliceHeatPerPairPositivity
import GaloisForLFunctions.RHTower.XiSliceAbscissaProfile
import GaloisForLFunctions.RHTower.XiSliceKKLScaleOffLineDetection

/-!
# Finite-head reduction of heated-slice positivity and sharp height-by-height heat profiles

This file establishes the exact decoupling of the retained finite zero block
`xiSliceGaussianRadiusHead t R` from the complementary tail in the heated-slice coefficients
`xiSliceHeatTransfer lam r t n`, removes the nonvanishing hypothesis `XiC t ≠ 0` from the heated
hyperbola and heated cone criteria, sharpens the height-by-height heat profile by a factor of `300`
over `xiSliceHeatTransfer_nonneg_of_absMono`, and reduces zero-free strips at the Ki–Kim–Lee scale
`κ₀(δ₀) / log t` to polynomial heat-positivity of the retained finite head alone.

## Main results

1. **Exact multiplicative splitting of `sliceTruncPoly` (`sliceTruncPoly_eq_head_mul_sdiff`) and
   unconditional heat positivity of the tail (`coeffNonneg_taylor_forwardPolyHeat_sliceTruncPoly_sdiff`).**
   For `H ⊆ S`, `sliceTruncPoly t S = sliceTruncPoly t H * sliceTruncPoly t (S \ H)`.  Whenever
   `R ≥ 0`, `r ≥ 0`, `s ≥ 0` and `1/2 ≤ R² + r² + 6s`, every zero copy outside
   `xiSliceGaussianRadiusHead t R` satisfies the heated hyperbola inequality, so the complementary
   factor `sliceTruncPoly t (S \ xiSliceGaussianRadiusHead t R)` is unconditionally
   coefficient-nonnegative after `e^{s ∂_x²}` and Taylor shift by `r`.
2. **Lossless finite-head transfer of heated-slice positivity
   (`xiSliceHeatTransfer_nonneg_of_finiteHead_poly`).**  At any height `t` with `Ξ(t) ≠ 0`, heat
   `λ ≥ 0`, shift `r ≥ 0`, and cutoff `R ≥ 0` with `1/2 ≤ R² + 3λ`, if the single finite-head
   polynomial `forwardPolyHeat (λ/2) (expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t R)))`
   has nonnegative coefficients, then `0 ≤ xiSliceHeatTransfer lam r t n` for every order `n : ℕ`.
3. **Unconditional removal of `Ξ(t) ≠ 0` (`xiSliceHeatTransfer_nonneg_of_heatedHyperbola_all`,
   `xiSliceHeatTransfer_nonneg_of_heatedCone_all`, `xiSliceHeatTransfer_nonneg_of_local_heatedCone`).**
   Via dominated joint continuity (`continuousOn_xiSliceHeatTransfer_comp`) along the coupled
   perturbation `(t', λ + min(|t' − t|, 1)) → (t, λ)` through `𝓝[≠] t`, the heated hyperbola and
   heated cone criteria hold at every real height `t ∈ ℝ`, including real zeros of `Ξ`.
4. **Sharp height-by-height heat threshold profile (`xiSliceHeatTransfer_nonneg_of_band`,
   `xiSliceHeatTransfer_nonneg_zero_free`, `exists_xiSliceHeatTransfer_nonneg_vinogradovKorobov`).**
   Whereas `xiSliceHeatTransfer_nonneg_of_absMono` requires `λ ≥ 100 x₀(t)²` for even orders,
   the local heated cone criterion gives `0 ≤ xiSliceHeatTransfer lam 0 t n` for all `n` at
   `λ ≥ x₀(t)² / 3`:
   * `λ = 0` on the low-height band `(|t| + 1/2)² ≤ 431/2`;
   * `λ ≥ (1/2 − 1/(100 log(t + 1/2)))² / 3 < 1/12` for all `t ≥ 9/2`;
   * `λ ≥ (1/2 − w(t + 1/2))² / 3 < 1/12` for all large `t` with the Vinogradov–Korobov width `w`.
5. **Finite-head criterion for a vertical zero-free strip at the KKL scale
   (`re_lt_of_finiteHead_heat_rate_nonneg`).**  For `δ₀ ∈ (0, 1/2]`, `0 < κ ≤ κ₀(δ₀)`, and `R ≥ 0`
   with `1/2 ≤ R²`, if the finite-head polynomial at cutoff `R` is heat-nonnegative at heat
   `κ / (2 log t)` for all `t ≥ t₀` with `Ξ(t) ≠ 0`, then every zero of `ξ` above `max(t₀, t₁)`
   satisfies `Re ρ < 1/2 + δ₀`.
-/

open Complex Filter Topology Metric Polynomial MeasureTheory Set
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry
open RHTower.XiAtlasFinitePart

namespace RHTower.DeBruijn

noncomputable section

/-! ## Exact head–tail factorization of the symmetric truncation polynomials -/

/-- For disjoint finite sets `A` and `B`, `sliceTruncCrit (A ∪ B) = sliceTruncCrit A ∪ sliceTruncCrit B`
disjointly, and similarly for `sliceTruncUp`, so `sliceTruncPoly t (A ∪ B)` factors as
`sliceTruncPoly t A * sliceTruncPoly t B`. -/
theorem sliceTruncPoly_union_disjoint (t : ℝ) {A B : Finset XiZeroCopy} (hAB : Disjoint A B) :
    sliceTruncPoly t (A ∪ B) = sliceTruncPoly t A * sliceTruncPoly t B := by
  classical
  have hcrit_eq : sliceTruncCrit (A ∪ B) = sliceTruncCrit A ∪ sliceTruncCrit B := by
    ext q
    simp only [mem_sliceTruncCrit, Finset.mem_union, or_and_right]
  have hup_eq : sliceTruncUp (A ∪ B) = sliceTruncUp A ∪ sliceTruncUp B := by
    ext q
    simp only [mem_sliceTruncUp, Finset.mem_union, or_and_right]
  have hcrit_disj : Disjoint (sliceTruncCrit A) (sliceTruncCrit B) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    exact Finset.disjoint_left.mp hAB (mem_sliceTruncCrit.mp h1).1 (mem_sliceTruncCrit.mp h2).1
  have hup_disj : Disjoint (sliceTruncUp A) (sliceTruncUp B) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    exact Finset.disjoint_left.mp hAB (mem_sliceTruncUp.mp h1).1 (mem_sliceTruncUp.mp h2).1
  unfold sliceTruncPoly
  rw [hcrit_eq, hup_eq, Finset.prod_union hcrit_disj, Finset.prod_union hup_disj]
  ring

/-- For any finite subset `H ⊆ S`, `sliceTruncPoly t S` factors into the retained head polynomial
`sliceTruncPoly t H` and the complementary polynomial `sliceTruncPoly t (S \ H)`. -/
theorem sliceTruncPoly_eq_head_mul_sdiff (t : ℝ) {H S : Finset XiZeroCopy} (hHS : H ⊆ S) :
    sliceTruncPoly t S = sliceTruncPoly t H * sliceTruncPoly t (S \ H) := by
  classical
  conv_lhs => rw [← Finset.union_sdiff_of_subset hHS]
  exact sliceTruncPoly_union_disjoint t Finset.disjoint_sdiff

/-- Whenever `0 ≤ R`, `0 ≤ r`, `0 ≤ s` and `1/2 ≤ R² + r² + 6s`, the complementary truncation
`sliceTruncPoly t (S \ xiSliceGaussianRadiusHead t R)` is unconditionally coefficient-nonnegative
after forward heat `s` and Taylor shift by `r`. -/
theorem coeffNonneg_taylor_forwardPolyHeat_sliceTruncPoly_sdiff {t s r R : ℝ} (ht : XiC t ≠ 0)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hR : 0 ≤ R) (hRrs : 1 / 2 ≤ R ^ 2 + r ^ 2 + 6 * s)
    (S : Finset XiZeroCopy) :
    CoeffNonneg (taylor r (forwardPolyHeat s
      (expand ℝ 2 (sliceTruncPoly t (S \ xiSliceGaussianRadiusHead t R))))) := by
  classical
  unfold sliceTruncPoly
  rw [map_mul, map_prod, map_prod]
  refine coeffNonneg_taylor_forwardPolyHeat_mul hs r
    (coeffNonneg_taylor_forwardPolyHeat_prod hs r _ fun q _ => ?_)
    (coeffNonneg_taylor_forwardPolyHeat_prod hs r _ fun q hq => ?_)
  · exact coeffNonneg_taylor_forwardPolyHeat_sliceLin hs (by unfold sliceAtom; positivity) hr
  · have hnotMem : q ∉ xiSliceGaussianRadiusHead t R :=
      (Finset.mem_sdiff.mp (mem_sliceTruncUp.mp hq).1).2
    have hcone := xiSliceGaussianRadiusHead_compl_heatedCone hR
      (M := r ^ 2 + 6 * s) (by linarith) hnotMem
    exact coeffNonneg_taylor_forwardPolyHeat_slicePair hs hr (xiSpectralPoint_ne_ofReal ht q)
      (by linarith)

/-- At `r = 0`, whenever `0 ≤ R`, `0 ≤ s` and `1/2 ≤ R² + 6s`, the complementary truncation
`sliceTruncPoly t (S \ xiSliceGaussianRadiusHead t R)` is unconditionally coefficient-nonnegative
after forward heat `s`. -/
theorem coeffNonneg_forwardPolyHeat_sliceTruncPoly_sdiff {t s R : ℝ} (ht : XiC t ≠ 0)
    (hs : 0 ≤ s) (hR : 0 ≤ R) (hRs : 1 / 2 ≤ R ^ 2 + 6 * s)
    (S : Finset XiZeroCopy) :
    CoeffNonneg (forwardPolyHeat s
      (expand ℝ 2 (sliceTruncPoly t (S \ xiSliceGaussianRadiusHead t R)))) := by
  classical
  unfold sliceTruncPoly
  rw [map_mul, map_prod, map_prod]
  refine coeffNonneg_forwardPolyHeat_mul hs
    (coeffNonneg_forwardPolyHeat_prod hs _ fun q _ => ?_)
    (coeffNonneg_forwardPolyHeat_prod hs _ fun q hq => ?_)
  · exact coeffNonneg_forwardPolyHeat_sliceLin hs (by unfold sliceAtom; positivity)
  · have hnotMem : q ∉ xiSliceGaussianRadiusHead t R :=
      (Finset.mem_sdiff.mp (mem_sliceTruncUp.mp hq).1).2
    have hcone := xiSliceGaussianRadiusHead_compl_heatedCone hR
      (M := 6 * s) (by linarith) hnotMem
    exact coeffNonneg_forwardPolyHeat_slicePair hs (xiSpectralPoint_ne_ofReal ht q) hcone

/-- **Lossless finite-head transfer of heated-slice positivity.**
Let `Ξ(t) ≠ 0`, `λ ≥ 0`, `r ≥ 0`, and `R ≥ 0` with `1/2 ≤ R² + 3λ`.  If the retained finite-head
polynomial `sliceTruncPoly t (xiSliceGaussianRadiusHead t R)` has nonnegative coefficients after
forward heat `λ/2`, then `0 ≤ xiSliceHeatTransfer lam r t n` for every order `n : ℕ`. -/
theorem xiSliceHeatTransfer_nonneg_of_finiteHead_poly {lam r t R : ℝ} (hlam : 0 ≤ lam)
    (hr : 0 ≤ r) (ht : XiC t ≠ 0) (hR : 0 ≤ R) (hRlam : 1 / 2 ≤ R ^ 2 + 3 * lam)
    (hhead : CoeffNonneg (forwardPolyHeat (lam / 2)
      (expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t R)))))
    (n : ℕ) :
    0 ≤ xiSliceHeatTransfer lam r t n := by
  classical
  have hzero : ∀ m : ℕ, 0 ≤ xiSliceHeatTransfer lam 0 t m := by
    intro m
    obtain ⟨l, rfl | rfl⟩ := Nat.even_or_odd' m
    · set s := lam / 2 with hs_def
      have hs : 0 ≤ s := by positivity
      have hRs : 1 / 2 ≤ R ^ 2 + 6 * s := by rw [hs_def]; linarith
      set H := xiSliceGaussianRadiusHead t R
      have hev : ∀ᶠ S : Finset XiZeroCopy in atTop,
          0 ≤ (((forwardPolyHeat s (expand ℝ 2 (sliceTruncPoly t S))).coeff (2 * l) : ℝ) : ℂ) := by
        filter_upwards [eventually_ge_atTop H] with S hHS
        rw [sliceTruncPoly_eq_head_mul_sdiff t hHS, map_mul]
        exact Complex.zero_le_real.mpr
          ((coeffNonneg_forwardPolyHeat_mul hs hhead
            (coeffNonneg_forwardPolyHeat_sliceTruncPoly_sdiff ht hs hR hRs S)) (2 * l))
      have hq : 0 ≤ xiSliceHeatTransfer lam 0 t (2 * l) / xiHorizontalPair t 0 :=
        ge_of_tendsto (tendsto_coeff_forwardPolyHeat_sliceTruncPoly hlam ht l) hev
      rw [← mul_div_cancel₀ (xiSliceHeatTransfer lam 0 t (2 * l)) (xiHorizontalPair_zero_ne ht)]
      refine mul_nonneg ?_ hq
      rw [xiHorizontalPair_zero_eq_ofReal]
      exact Complex.zero_le_real.mpr (sq_nonneg _)
    · rw [xiSliceHeatTransfer_odd_eq_zero hlam]
  refine (hasSum_xiSliceHeatTransfer_center hlam r t n).nonneg fun j => ?_
  exact mul_nonneg (Complex.zero_le_real.mpr (by positivity)) (hzero (n + j))

/-! ## Dominated joint continuity and removal of `Ξ(t) ≠ 0` -/

/-- **Dominated continuity of `xiSliceHeatTransfer` along continuous heat and height paths.**
If `lam : ℝ → ℝ` and `t : ℝ → ℝ` are continuous on `s` with `lam x ≤ L` on `s`, then
`x ↦ xiSliceHeatTransfer (lam x) x₀ (t x) n` is continuous on `s`. -/
theorem continuousOn_xiSliceHeatTransfer_comp {L : ℝ} (hL : 0 ≤ L) {lam t : ℝ → ℝ} {s : Set ℝ}
    (hlam_cont : ContinuousOn lam s) (ht_cont : ContinuousOn t s)
    (hlamL : ∀ x ∈ s, lam x ≤ L) (x₀ : ℝ) (n : ℕ) :
    ContinuousOn (fun x => xiSliceHeatTransfer (lam x) x₀ (t x) n) s := by
  set Φ := riemannKernelReal with hΦ
  have hΦ0 : ∀ u, 0 ≤ Φ u := riemannKernel_superExp.nonneg
  set D : ℝ × ℝ → ℝ := fun p =>
    Φ p.1 * Real.exp (L * p.1 ^ 2) * Real.exp ((|x₀| + 1) * |p.1|) *
      (Φ p.2 * Real.exp (L * p.2 ^ 2) * Real.exp ((|x₀| + 1) * |p.2|)) with hD
  have hDi : Integrable D :=
    integrable_prod_majorant (riemannKernel_superExp.mul_exp_sq hL) (|x₀| + 1)
  set G : ℝ → ℝ × ℝ → ℂ := fun x p =>
    ((Φ p.1 * Φ p.2 * Real.exp (lam x * (p.1 - p.2) ^ 2 / 2) *
      Real.exp (x₀ * (p.1 - p.2)) * ((p.1 - p.2) ^ n / n.factorial) : ℝ) : ℂ) *
        cexp (I * (t x : ℂ) * ((p.1 : ℂ) + (p.2 : ℂ))) with hG
  have hmeas : ∀ x ∈ s, AEStronglyMeasurable (G x) volume := by
    intro x _
    have := continuous_riemannKernelReal
    refine Continuous.aestronglyMeasurable ?_
    simp only [hG, hΦ]
    fun_prop
  have hbound : ∀ x ∈ s, ∀ᵐ p : ℝ × ℝ ∂volume, ‖G x p‖ ≤ D p := by
    intro x hx
    refine Eventually.of_forall fun p => ?_
    dsimp only [G]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_I_mul_ofReal_add, mul_one]
    have hexpsq : Real.exp (lam x * (p.1 - p.2) ^ 2 / 2) ≤
        Real.exp (L * p.1 ^ 2) * Real.exp (L * p.2 ^ 2) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h1 : lam x * (p.1 - p.2) ^ 2 / 2 ≤ L * (p.1 - p.2) ^ 2 / 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hlamL x hx) (sq_nonneg _))
          zero_le_two
      nlinarith [sq_nonneg (p.1 + p.2)]
    have h2 := abs_sub_pow_div_mul_exp_le x₀ p.1 p.2 n
    have habs : |Φ p.1 * Φ p.2 * Real.exp (lam x * (p.1 - p.2) ^ 2 / 2) *
        Real.exp (x₀ * (p.1 - p.2)) * ((p.1 - p.2) ^ n / n.factorial)| =
        Φ p.1 * Φ p.2 * Real.exp (lam x * (p.1 - p.2) ^ 2 / 2) *
          (|p.1 - p.2| ^ n / n.factorial * Real.exp (x₀ * (p.1 - p.2))) := by
      simp only [abs_mul, abs_div, abs_pow, Nat.abs_cast, abs_of_nonneg (hΦ0 _),
        abs_of_pos (Real.exp_pos _)]
      ring
    rw [habs]
    calc Φ p.1 * Φ p.2 * Real.exp (lam x * (p.1 - p.2) ^ 2 / 2) *
          (|p.1 - p.2| ^ n / n.factorial * Real.exp (x₀ * (p.1 - p.2)))
        ≤ Φ p.1 * Φ p.2 * (Real.exp (L * p.1 ^ 2) * Real.exp (L * p.2 ^ 2)) *
            (Real.exp ((|x₀| + 1) * |p.1|) * Real.exp ((|x₀| + 1) * |p.2|)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexpsq (mul_nonneg (hΦ0 _) (hΦ0 _))) h2
            (by positivity) (by have := hΦ0 p.1; have := hΦ0 p.2; positivity)
      _ = D p := by simp only [hD]; ring
  have hcont_p : ∀ᵐ p : ℝ × ℝ ∂volume, ContinuousOn (fun x => G x p) s := by
    refine Eventually.of_forall fun p => ?_
    simp only [hG]
    refine ContinuousOn.mul ?_ ?_
    · refine Complex.continuous_ofReal.comp_continuousOn ?_
      refine ContinuousOn.mul (ContinuousOn.mul (ContinuousOn.mul continuousOn_const ?_)
        continuousOn_const) continuousOn_const
      exact Real.continuous_exp.comp_continuousOn
        ((hlam_cont.mul continuousOn_const).div_const 2)
    · refine Complex.continuous_exp.comp_continuousOn ?_
      exact (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn ht_cont)).mul
        continuousOn_const
  exact continuousOn_of_dominated hmeas hbound hDi hcont_p

/-- **The heated hyperbola criterion at every real height (removing `Ξ(t) ≠ 0`).**
For every `t ∈ ℝ`, `λ ≥ 0`, and `r ≥ 0`, if every zero `z` of `Ξ` satisfies
`(Im z)² ≤ (Re z − t)² + r² + 3λ`, then `0 ≤ xiSliceHeatTransfer lam r t n` for every `n : ℕ`. -/
theorem xiSliceHeatTransfer_nonneg_of_heatedHyperbola_all {lam r t : ℝ} (hlam : 0 ≤ lam)
    (hr : 0 ≤ r)
    (hcone : ∀ q : XiZeroCopy,
      (xiSpectralPoint q).im ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 + r ^ 2 + 3 * lam)
    (n : ℕ) :
    0 ≤ xiSliceHeatTransfer lam r t n := by
  by_cases ht : XiC (t : ℂ) ≠ 0
  · exact xiSliceHeatTransfer_nonneg_of_heatedHyperbola hlam hr ht hcone n
  · set lamPath : ℝ → ℝ := fun t' => lam + min |t' - t| 1 with hlamPath
    have hcontOn : ContinuousOn (fun t' => xiSliceHeatTransfer (lamPath t') r t' n) univ := by
      refine continuousOn_xiSliceHeatTransfer_comp (L := lam + 1) (by linarith) ?_ continuousOn_id
        (fun t' _ => by simp only [hlamPath]; linarith [min_le_right |t' - t| 1]) r n
      simp only [hlamPath]
      exact continuousOn_const.add ((continuous_abs.comp (continuous_id.sub continuous_const)).min
        continuous_const).continuousOn
    have htend : Tendsto (fun t' => xiSliceHeatTransfer (lamPath t') r t' n) (𝓝[≠] t)
        (𝓝 (xiSliceHeatTransfer lam r t n)) := by
      have h0 : lamPath t = lam := by simp [hlamPath]
      rw [← h0]
      exact ((continuousOn_univ.mp hcontOn).tendsto t).mono_left nhdsWithin_le_nhds
    have hnear : ∀ᶠ t' : ℝ in 𝓝[≠] t, |t' - t| < 1 / 2 := by
      have : ∀ᶠ t' : ℝ in 𝓝 t, |t' - t| < 1 / 2 := by
        have hc : Continuous fun t' : ℝ => |t' - t| := by fun_prop
        have h := hc.tendsto t
        rw [sub_self, abs_zero] at h
        exact h.eventually (gt_mem_nhds (by norm_num))
      exact this.filter_mono nhdsWithin_le_nhds
    refine ge_of_tendsto htend ((hnear.and (eventually_XiC_ofReal_ne_zero t)).mono fun t' h => ?_)
    have hdist : |t' - t| < 1 / 2 := h.1
    have hmin : min |t' - t| 1 = |t' - t| := min_eq_left (by linarith)
    have hlam' : 0 ≤ lamPath t' := by simp only [hlamPath]; positivity
    refine xiSliceHeatTransfer_nonneg_of_heatedHyperbola hlam' hr h.2 (fun q => ?_) n
    simp only [hlamPath, hmin]
    have h4 := xiSpectralPoint_im_sq_lt_quarter q
    by_cases hfar : 1 / 2 ≤ |(xiSpectralPoint q).re - t'|
    · have hsq : (1 / 2 : ℝ) ^ 2 ≤ ((xiSpectralPoint q).re - t') ^ 2 := by
        rw [← sq_abs ((xiSpectralPoint q).re - t')]
        exact pow_le_pow_left₀ (by norm_num) hfar 2
      have : 0 ≤ r ^ 2 + 3 * (lam + |t' - t|) := by positivity
      linarith
    · push Not at hfar
      set d := (xiSpectralPoint q).re - t
      set d' := (xiSpectralPoint q).re - t'
      have hd_sub : d - d' = t' - t := by simp [d, d']
      have hd'_lt := abs_lt.mp hfar
      have hdt_lt := abs_lt.mp hdist
      have hsum_abs : |d + d'| ≤ 3 := by
        rw [abs_le]
        constructor <;> linarith [hd'_lt.1, hd'_lt.2, hdt_lt.1, hdt_lt.2, hd_sub]
      have hdiff_sq : d ^ 2 - d' ^ 2 ≤ 3 * |t' - t| := by
        calc d ^ 2 - d' ^ 2 = (d + d') * (d - d') := by ring
          _ ≤ |(d + d') * (d - d')| := le_abs_self _
          _ = |d + d'| * |t' - t| := by rw [abs_mul, hd_sub]
          _ ≤ 3 * |t' - t| := mul_le_mul_of_nonneg_right hsum_abs (abs_nonneg _)
      have hcq := hcone q
      change (xiSpectralPoint q).im ^ 2 ≤ d ^ 2 + r ^ 2 + 3 * lam at hcq
      change (xiSpectralPoint q).im ^ 2 ≤ d' ^ 2 + r ^ 2 + 3 * (lam + |t' - t|)
      linarith

/-- **The heated cone criterion at every real height (removing `Ξ(t) ≠ 0`).**
For every `t ∈ ℝ` and `λ ≥ 0`, if every zero `z` of `Ξ` satisfies `(Im z)² ≤ (Re z − t)² + 3λ`,
then `0 ≤ xiSliceHeatTransfer lam 0 t n` for every `n : ℕ`. -/
theorem xiSliceHeatTransfer_nonneg_of_heatedCone_all {lam t : ℝ} (hlam : 0 ≤ lam)
    (hcone : ∀ q : XiZeroCopy,
      (xiSpectralPoint q).im ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 + 3 * lam)
    (n : ℕ) :
    0 ≤ xiSliceHeatTransfer lam 0 t n :=
  xiSliceHeatTransfer_nonneg_of_heatedHyperbola_all hlam le_rfl (fun q => by
    simpa using hcone q) n

/-- **Local heated hyperbola criterion on `xiSliceGaussianRadiusHead t R`.**
For every `t ∈ ℝ`, `λ ≥ 0`, `r ≥ 0`, and `R ≥ 0` with `1/2 ≤ R² + r² + 3λ`, if every zero copy in
the finite head `q ∈ xiSliceGaussianRadiusHead t R` satisfies
`(Im z_q)² ≤ (Re z_q − t)² + r² + 3λ`, then `0 ≤ xiSliceHeatTransfer lam r t n` for all `n : ℕ`. -/
theorem xiSliceHeatTransfer_nonneg_of_local_heatedHyperbola {lam r t R : ℝ} (hlam : 0 ≤ lam)
    (hr : 0 ≤ r) (hR : 0 ≤ R) (hRrs : 1 / 2 ≤ R ^ 2 + r ^ 2 + 3 * lam)
    (hlocal : ∀ q ∈ xiSliceGaussianRadiusHead t R,
      (xiSpectralPoint q).im ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 + r ^ 2 + 3 * lam)
    (n : ℕ) :
    0 ≤ xiSliceHeatTransfer lam r t n := by
  refine xiSliceHeatTransfer_nonneg_of_heatedHyperbola_all hlam hr (fun q => ?_) n
  by_cases hq : q ∈ xiSliceGaussianRadiusHead t R
  · exact hlocal q hq
  · have := xiSliceGaussianRadiusHead_compl_heatedCone hR (M := r ^ 2 + 3 * lam) (by linarith) hq
    linarith

/-- **Local heated cone criterion on `xiSliceGaussianRadiusHead t R`.**
For every `t ∈ ℝ`, `λ ≥ 0`, and `R ≥ 0` with `1/2 ≤ R² + 3λ`, if every zero copy in the finite head
`q ∈ xiSliceGaussianRadiusHead t R` satisfies `(Im z_q)² ≤ (Re z_q − t)² + 3λ`, then
`0 ≤ xiSliceHeatTransfer lam 0 t n` for all `n : ℕ`. -/
theorem xiSliceHeatTransfer_nonneg_of_local_heatedCone {lam t R : ℝ} (hlam : 0 ≤ lam)
    (hR : 0 ≤ R) (hRlam : 1 / 2 ≤ R ^ 2 + 3 * lam)
    (hlocal : ∀ q ∈ xiSliceGaussianRadiusHead t R,
      (xiSpectralPoint q).im ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 + 3 * lam)
    (n : ℕ) :
    0 ≤ xiSliceHeatTransfer lam 0 t n :=
  xiSliceHeatTransfer_nonneg_of_local_heatedHyperbola hlam le_rfl hR (by linarith)
    (fun q hq => by simpa using hlocal q hq) n

/-! ## Sharp height-by-height heat threshold profile (`λ ≥ x₀(t)² / 3`) -/

/-- **All-order heated-slice positivity on the low-height band.**
For `(|t| + 1/2)² ≤ 431/2` (`|t| ≤ 14.18…`), `0 ≤ xiSliceHeatTransfer lam 0 t n` holds for every
heat `λ ≥ 0` and every order `n : ℕ`. -/
theorem xiSliceHeatTransfer_nonneg_of_band {lam t : ℝ} (hlam : 0 ≤ lam)
    (ht : (|t| + 1 / 2) ^ 2 ≤ 431 / 2) (n : ℕ) :
    0 ≤ xiSliceHeatTransfer lam 0 t n := by
  refine xiSliceHeatTransfer_nonneg_of_heatedCone_all hlam (fun q => ?_) n
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
  have him : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by simp [xiSpectralPoint]
  rw [hre, him]
  set β := (q.1 : ℂ).re with hβ
  set γ := (q.1 : ℂ).im with hγ
  have hquarter : (1 / 2 - β) ^ 2 < 1 / 4 := by
    have := xi_divisor_support_centered_re_sq_lt_quarter q.1
    rw [← hβ] at this
    linarith [show (1 / 2 - β) ^ 2 = (β - 1 / 2) ^ 2 by ring]
  by_cases hfar : 1 / 2 ≤ |γ - t|
  · have : (1 / 2 : ℝ) ^ 2 ≤ (γ - t) ^ 2 := by
      rw [← sq_abs (γ - t)]; exact pow_le_pow_left₀ (by norm_num) hfar 2
    linarith
  · have hnear : |γ - t| < 1 / 2 := lt_of_not_ge hfar
    have hγabs : |γ| < |t| + 1 / 2 := by
      have := abs_sub_abs_le_abs_sub γ t
      linarith
    have hγsq : γ ^ (2 : ℕ) < 431 / 2 := by
      have h1 : |γ| ^ 2 < (|t| + 1 / 2) ^ 2 :=
        pow_lt_pow_left₀ hγabs (abs_nonneg _) two_ne_zero
      rw [sq_abs] at h1
      linarith
    have hline := xiZeroCopy_re_eq_half_of_im_sq_lt_fourHundredThirtyOne_halves q hγsq
    rw [← hβ] at hline
    rw [hline, sub_self]
    nlinarith [sq_nonneg (γ - t)]

/-- **Heated-slice positivity from the de la Vallée Poussin zero-free region (`λ < 1/12`).**
For every height `t ≥ 9/2` and every heat `λ ≥ 0` satisfying
`(1/2 − 1/(100 log(t + 1/2)))² ≤ 3λ`, `0 ≤ xiSliceHeatTransfer lam 0 t n` holds for all `n : ℕ`. -/
theorem xiSliceHeatTransfer_nonneg_zero_free {lam t : ℝ} (ht : 9 / 2 ≤ t) (hlam : 0 ≤ lam)
    (hbound : (1 / 2 - 1 / 100 / Real.log (t + 1 / 2)) ^ 2 ≤ 3 * lam) (n : ℕ) :
    0 ≤ xiSliceHeatTransfer lam 0 t n := by
  have hlog5 : 1 < Real.log (t + 1 / 2) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  set x₀ := 1 / 2 - 1 / 100 / Real.log (t + 1 / 2) with hx₀def
  have hsmall : 1 / 100 / Real.log (t + 1 / 2) < 1 / 2 := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  have hx₀ : 0 ≤ x₀ := by rw [hx₀def]; linarith
  refine xiSliceHeatTransfer_nonneg_of_heatedCone_all hlam (fun q => ?_) n
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
  have him : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by simp [xiSpectralPoint]
  rw [hre, him]
  set β := (q.1 : ℂ).re with hβ
  set γ := (q.1 : ℂ).im with hγ
  have hquarter : (1 / 2 - β) ^ 2 < 1 / 4 := by
    have := xi_divisor_support_centered_re_sq_lt_quarter q.1
    rw [← hβ] at this
    linarith [show (1 / 2 - β) ^ 2 = (β - 1 / 2) ^ 2 by ring]
  by_cases hfar : 1 / 2 ≤ |γ - t|
  · have : (1 / 2 : ℝ) ^ 2 ≤ (γ - t) ^ 2 := by
      rw [← sq_abs (γ - t)]; exact pow_le_pow_left₀ (by norm_num) hfar 2
    linarith
  · have hnear : |γ - t| < 1 / 2 := lt_of_not_ge hfar
    have hγ4 : 4 ≤ γ := by have := (abs_lt.mp hnear).1; linarith
    have hγt : γ < t + 1 / 2 := by have := (abs_lt.mp hnear).2; linarith
    have hup := xiZeroCopy_zero_free_from_four (q := q) hγ4
    have hpart : 4 ≤ ((lagPartner q).1 : ℂ).im := by
      rw [lagPartner_coe]; simpa [hγ] using hγ4
    have hlow := xiZeroCopy_zero_free_from_four (q := lagPartner q) hpart
    rw [lagPartner_coe] at hlow
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.sub_im, Complex.one_im,
      Complex.conj_im, zero_sub, neg_neg] at hlow
    rw [← hβ, ← hγ] at hup hlow
    have hlogγ : 0 < Real.log γ := Real.log_pos (by linarith)
    have hlogle : Real.log γ ≤ Real.log (t + 1 / 2) := Real.log_le_log (by linarith) hγt.le
    have hcmp : 1 / 100 / Real.log (t + 1 / 2) ≤ 1 / 100 / Real.log γ :=
      div_le_div_of_nonneg_left (by norm_num) hlogγ hlogle
    have habs : |1 / 2 - β| ≤ x₀ := by
      rw [abs_le, hx₀def]; constructor <;> linarith
    have hsq : (1 / 2 - β) ^ 2 ≤ x₀ ^ 2 := by
      rw [← sq_abs (1 / 2 - β)]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    nlinarith [sq_nonneg (γ - t)]

/-- **Heated-slice positivity from the Vinogradov–Korobov zero-free region (`λ < 1/12`).**
There is `T₀` such that for every `t ≥ T₀` and every `λ ≥ 0` with
`(1/2 − w(t + 1/2))² ≤ 3λ`, where `w(T) = (log T)^{−2/3} (log log T)^{−5/3}/10⁸`,
`0 ≤ xiSliceHeatTransfer lam 0 t n` holds for all `n : ℕ`. -/
theorem exists_xiSliceHeatTransfer_nonneg_vinogradovKorobov :
    ∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t → ∀ lam : ℝ, 0 ≤ lam →
      (1 / 2 - vinogradovKorobovGaussianWidth (t + 1 / 2)) ^ 2 ≤ 3 * lam →
      ∀ n : ℕ, 0 ≤ xiSliceHeatTransfer lam 0 t n := by
  obtain ⟨t₀, ht₀2, ht₀e, hvk⟩ := exists_xiZero_re_le_vinogradovKorobov
  refine ⟨t₀ + 1 / 2, fun t ht lam hlam hbound n => ?_⟩
  set w := vinogradovKorobovGaussianWidth (t + 1 / 2) with hw
  have hT : Real.exp (Real.exp 1) ≤ t + 1 / 2 := by linarith
  have hpos : 0 < t + 1 / 2 := lt_of_lt_of_le (Real.exp_pos _) hT
  have hl : Real.exp 1 ≤ Real.log (t + 1 / 2) := (Real.le_log_iff_exp_le hpos).mpr hT
  have hl1 : 1 ≤ Real.log (t + 1 / 2) := le_trans (Real.one_le_exp (by norm_num)) hl
  have hll : 1 ≤ Real.log (Real.log (t + 1 / 2)) :=
    (Real.le_log_iff_exp_le (by linarith)).mpr hl
  have hw1 : w ≤ 1 / 2 := by
    have ha : Real.log (t + 1 / 2) ^ (-(2 : ℝ) / 3) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hl1 (by norm_num)
    have hb : Real.log (Real.log (t + 1 / 2)) ^ (-(5 : ℝ) / 3) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hll (by norm_num)
    have ha0 : 0 ≤ Real.log (t + 1 / 2) ^ (-(2 : ℝ) / 3) := by positivity
    rw [hw]; unfold vinogradovKorobovGaussianWidth
    rw [div_le_iff₀ (by norm_num)]
    nlinarith [mul_le_one₀ ha (by positivity) hb]
  refine xiSliceHeatTransfer_nonneg_of_heatedCone_all hlam (fun q => ?_) n
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
  have him : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by simp [xiSpectralPoint]
  rw [hre, him]
  set β := (q.1 : ℂ).re with hβ
  set γ := (q.1 : ℂ).im with hγ
  have hquarter : (1 / 2 - β) ^ 2 < 1 / 4 := by
    have := xi_divisor_support_centered_re_sq_lt_quarter q.1
    rw [← hβ] at this
    linarith [show (1 / 2 - β) ^ 2 = (β - 1 / 2) ^ 2 by ring]
  by_cases hfar : 1 / 2 ≤ |γ - t|
  · have : (1 / 2 : ℝ) ^ 2 ≤ (γ - t) ^ 2 := by
      rw [← sq_abs (γ - t)]; exact pow_le_pow_left₀ (by norm_num) hfar 2
    linarith
  · have hnear : |γ - t| < 1 / 2 := lt_of_not_ge hfar
    have hγ0 : t₀ ≤ γ := by have := (abs_lt.mp hnear).1; linarith
    have hγt : γ < t + 1 / 2 := by have := (abs_lt.mp hnear).2; linarith
    have hγabs : |γ| = γ := abs_of_nonneg (by linarith)
    have hup := hvk q (by simp only [xiZero, ← hγ, hγabs]; exact hγ0)
    have hpart := hvk (lagPartner q) (by
      simp only [xiZero, lagPartner_coe, Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub,
        neg_neg, ← hγ, hγabs]; exact hγ0)
    simp only [xiZero, ← hβ, ← hγ, hγabs] at hup
    simp only [xiZero, lagPartner_coe, Complex.sub_re, Complex.one_re, Complex.conj_re,
      Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub, neg_neg, ← hβ, ← hγ,
      hγabs] at hpart
    have hanti := vinogradovKorobovGaussianWidth_anti (le_trans ht₀e hγ0) hγt.le
    rw [← hw] at hanti
    have habs : |1 / 2 - β| ≤ 1 / 2 - w := by
      rw [abs_le]; constructor <;> linarith
    have hsq : (1 / 2 - β) ^ 2 ≤ (1 / 2 - w) ^ 2 := by
      rw [← sq_abs (1 / 2 - β)]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    nlinarith [sq_nonneg (γ - t)]

/-! ## Finite-head criterion for a vertical zero-free strip at the Ki–Kim–Lee scale -/

/-- **Finite-head heat-rate criterion for a zero-free strip at the KKL scale.**
For `δ₀ ∈ (0, 1/2]` there is `t₁ ≥ 16` such that for any `0 < κ ≤ κ₀(δ₀)`, `t₀ ∈ ℝ`, and cutoff
`R ≥ 0` with `1/2 ≤ R²`: if at every height `t ≥ t₀` with `Ξ(t) ≠ 0` the retained finite-head
polynomial `sliceTruncPoly t (xiSliceGaussianRadiusHead t R)` is coefficient-nonnegative after
forward heat `κ / (2 log t)`, then every zero `ρ` of `ξ` with `Im ρ ≥ max(t₀, t₁)` satisfies
`Re ρ < 1/2 + δ₀`. -/
theorem re_lt_of_finiteHead_heat_rate_nonneg {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hδ₀2 : δ₀ ≤ 1 / 2) :
    ∃ t₁ : ℝ, 16 ≤ t₁ ∧ ∀ κ t₀ R : ℝ, 0 < κ → κ ≤ kklDetectionRate δ₀ →
      0 ≤ R → 1 / 2 ≤ R ^ 2 →
      (∀ t : ℝ, t₀ ≤ t → XiC (t : ℂ) ≠ 0 →
        CoeffNonneg (forwardPolyHeat (κ / (2 * Real.log t))
          (expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t R))))) →
      ∀ ρ : ℂ, xi ρ = 0 → max t₀ t₁ ≤ ρ.im → ρ.re < 1 / 2 + δ₀ := by
  obtain ⟨t₁, ht₁, hdet⟩ := exists_re_xiSliceHeatTransfer_neg_of_slice_zero hδ₀ hδ₀2
  refine ⟨t₁, ht₁, fun κ t₀ R hκ hκ₀ hR hR2 hhead ρ hρ hγ => ?_⟩
  by_contra hre
  push Not at hre
  have hγ₁ : t₁ ≤ ρ.im := le_trans (le_max_right _ _) hγ
  have hγ₀ : t₀ ≤ ρ.im := le_trans (le_max_left _ _) hγ
  obtain ⟨n, hn⟩ := hdet ρ.im hγ₁ (ρ.re - 1 / 2) (by linarith) (xiSliceReal_offset_eq_zero hρ) κ hκ
    hκ₀
  have hgood : ∀ t' : ℝ, max t₀ 8 ≤ t' → XiC (t' : ℂ) ≠ 0 →
      0 ≤ xiSliceHeatTransfer (κ / Real.log t') 0 t' n := by
    intro t' ht' hX
    have ht'0 : t₀ ≤ t' := le_trans (le_max_left _ _) ht'
    have ht'8 : 8 ≤ t' := le_trans (le_max_right _ _) ht'
    have hlog : 0 < Real.log t' := Real.log_pos (by linarith)
    have hlam0 : 0 ≤ κ / Real.log t' := div_nonneg hκ.le hlog.le
    have hhalf : κ / Real.log t' / 2 = κ / (2 * Real.log t') := by ring
    refine xiSliceHeatTransfer_nonneg_of_finiteHead_poly hlam0 le_rfl hX hR
      (by linarith) ?_ n
    rw [hhalf]
    exact hhead t' ht'0 hX
  have hpos_at_im : 0 ≤ xiSliceHeatTransfer (κ / Real.log ρ.im) 0 ρ.im n := by
    have him8 : 8 ≤ ρ.im := by linarith
    have him_max : max t₀ 8 ≤ ρ.im := max_le hγ₀ him8
    by_cases hX : XiC (ρ.im : ℂ) ≠ 0
    · exact hgood ρ.im him_max hX
    · have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hcontOn : ContinuousOn (fun t' : ℝ => xiSliceHeatTransfer (κ / Real.log t') 0 t' n)
          (Ici 2) := by
        refine continuousOn_xiSliceHeatTransfer_comp (L := κ / Real.log 2) (by positivity) ?_
          continuousOn_id
          (fun t' ht' => div_le_div_of_nonneg_left hκ.le hl2
            (Real.log_le_log (by norm_num) (mem_Ici.mp ht'))) 0 n
        exact continuousOn_const.div (Real.continuousOn_log.mono fun x hx =>
          ne_of_gt (by linarith [mem_Ici.mp hx])) fun x hx =>
            ne_of_gt (Real.log_pos (by linarith [mem_Ici.mp hx]))
      have htend : Tendsto (fun t' : ℝ => xiSliceHeatTransfer (κ / Real.log t') 0 t' n)
          (𝓝[>] ρ.im) (𝓝 (xiSliceHeatTransfer (κ / Real.log ρ.im) 0 ρ.im n)) :=
        ((hcontOn.continuousAt (Ici_mem_nhds (by linarith))).tendsto).mono_left nhdsWithin_le_nhds
      have hX_ev : ∀ᶠ t' : ℝ in 𝓝[>] ρ.im, XiC (t' : ℂ) ≠ 0 :=
        (eventually_XiC_ofReal_ne_zero ρ.im).filter_mono
          (nhdsWithin_mono ρ.im fun _ hx => ne_of_gt hx)
      have hgt_ev : ∀ᶠ t' : ℝ in 𝓝[>] ρ.im, ρ.im < t' := self_mem_nhdsWithin
      exact ge_of_tendsto htend ((hgt_ev.and hX_ev).mono fun t' h =>
        hgood t' (him_max.trans h.1.le) h.2)
  have := (Complex.nonneg_iff.mp hpos_at_im).1
  linarith

end

end RHTower.DeBruijn
