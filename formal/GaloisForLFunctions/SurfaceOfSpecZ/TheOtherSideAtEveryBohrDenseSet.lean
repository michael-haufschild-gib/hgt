import GaloisForLFunctions.SurfaceOfSpecZ.BohrDenseSetsSampleEveryAttainedTop
import GaloisForLFunctions.SurfaceOfSpecZ.TheOtherSideSeesEveryZero

/-!
# The other side at every Bohr-dense set

`BohrDenseSetsSampleEveryAttainedTop` decides attained tops from below on every Bohr-dense set,
for configurations without real zeros: a real zero masks the shallower ones. From above nothing is
masked: an upper bound `2 Re S(u) ≤ K` on a set `T` that is Bohr-dense at `+∞` puts every zero of a
tempered configuration on the line as soon as the maximal real part is attained, real zeros allowed
(`onLine_of_bddAbove_of_isBohrDenseAtTop`); in particular on any set with arbitrarily long
intervals (`onLine_of_bddAbove_long_intervals_of_max`).

**Mechanism.** The top layer `F_top` is real, almost periodic and, by the bound and Bohr density,
`≤ 0` on `ℝ` (`topTrace_nonpos_of_isBohrDenseAtTop`). Its mean is its coefficient `e_b` at the real
exponent `b` (`bohrCoefficient_topTraceC`), which is `0` or, for a real top zero, positive
(`evenCoeff_spline_pos_of_real`). So `e_b − F_top ≥ 0` has mean zero and vanishes: `F_top = e_b ≥ 0`,
hence `F_top = 0`, against the coefficient `e_{ρ₀ − ½} ≠ 0`.
-/

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- **The Bohr coefficients of the top layer** at its own exponents: `e_{z₁}` at `Im z₁` if
`Re z₁ = b`. -/
theorem bohrCoefficient_topTraceC {Z : ZeroConfig} (hZ : TemperedConfig Z) {b : ℝ} {z₁ : ℂ}
    (hz₁ : z₁.re = b) :
    bohrCoefficient (topTraceC Z b) z₁.im = evenCoeff Z (boxSpline 1 3) z₁ := by
  have hgc := continuous_topTraceC (b := b) hZ
  have hga := isBohrAlmostPeriodic_topTraceC (b := b) hZ
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨S₀, hS₀⟩ := exists_finset_topTraceC_approx (b := b) hZ hε
  classical
  have hS := hS₀ (insert z₁ S₀) (Finset.subset_insert _ _)
  have hcoefP : bohrCoefficient (fun t => ∑ z ∈ insert z₁ S₀, topTerm Z b z t) z₁.im =
      evenCoeff Z (boxSpline 1 3) z₁ := by
    rw [bohrCoefficient_finset_sum _ (fun z => continuous_topTerm z)
      (fun z => isBohrAlmostPeriodic_topTerm z)]
    rw [Finset.sum_eq_single z₁]
    · rw [bohrCoefficient_topTerm, if_pos ⟨hz₁, rfl⟩]
    · intro z _ hne
      rw [bohrCoefficient_topTerm, if_neg]
      rintro ⟨h1, h2⟩
      exact hne (Complex.ext (by rw [h1, hz₁]) h2.symm)
    · intro hn; exact absurd (Finset.mem_insert_self _ _) hn
  have hd := norm_bohrCoefficient_sub_le hgc hga (continuous_topTerm_sum _)
    (isBohrAlmostPeriodic_topTerm_sum _) (fun t => hS t) z₁.im
  rw [hcoefP] at hd
  rw [dist_eq_norm]; exact hd

/-- **The top layer is nonpositive** under an upper bound on a Bohr-dense set. -/
theorem topTrace_nonpos_of_isBohrDenseAtTop {Z : ZeroConfig} (hZ : TemperedConfig Z) {b : ℝ}
    (h : TopDepth Z b) (hb0 : 0 < b) {T : Set ℝ} (hT : IsBohrDenseAtTop T) {K : ℝ}
    (hK : ∀ u ∈ T, 2 * (lagStructure Z (boxSpline 1 3) u).re ≤ K) (v : ℝ) :
    topTrace Z b v ≤ 0 := by
  have hE := summable_norm_evenCoeff_spline hZ
  set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ with hEdef
  have hE0 : 0 ≤ E := tsum_nonneg fun _ => norm_nonneg _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := ε / 5 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨S, hS⟩ := exists_finset_topTraceC_approx (b := b) hZ hδ
  have h1 := (tendsto_normTrace_sub_topTrace hZ h).eventually
    (Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ)
  have hlim : Tendsto (fun u : ℝ => |K| * Real.exp (-(b * u))) atTop (𝓝 0) := by
    have h0 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hb0)).const_mul |K|
    simpa [Function.comp_def] using h0
  have h2 := hlim.eventually (gt_mem_nhds hδ)
  obtain ⟨U, hU⟩ := eventually_atTop.mp (h1.and h2)
  obtain ⟨u, huT, hUu, hph⟩ := hT (S.image Complex.im) v (δ / (E + 1)) U (by positivity)
  obtain ⟨hu1, hu2⟩ := hU u hUu
  have hn : normTrace Z b u ≤ δ := by
    have hk := hK u huT
    unfold normTrace
    have h3 : 2 * (lagStructure Z (boxSpline 1 3) u).re * Real.exp (-(b * u)) ≤
        |K| * Real.exp (-(b * u)) :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) (Real.exp_pos _).le
    linarith
  have htu : topTrace Z b u ≤ 2 * δ := by linarith [hu1.1]
  have hPP : ‖∑ z ∈ S, topTerm Z b z u - ∑ z ∈ S, topTerm Z b z v‖ ≤ δ := by
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ z ∈ S, (topTerm Z b z u - topTerm Z b z v)‖
        ≤ ∑ z ∈ S, ‖topTerm Z b z u - topTerm Z b z v‖ := norm_sum_le _ _
      _ ≤ ∑ z ∈ S, ‖evenCoeff Z (boxSpline 1 3) z‖ * (δ / (E + 1)) := by
          refine Finset.sum_le_sum fun z hz => ?_
          unfold topTerm
          split_ifs with hzb
          · rw [← mul_sub, norm_mul]
            exact mul_le_mul_of_nonneg_left (hph z.im (Finset.mem_image_of_mem _ hz)).le
              (norm_nonneg _)
          · simp only [sub_self, norm_zero]; positivity
      _ = (∑ z ∈ S, ‖evenCoeff Z (boxSpline 1 3) z‖) * (δ / (E + 1)) := by rw [Finset.sum_mul]
      _ ≤ E * (δ / (E + 1)) :=
          mul_le_mul_of_nonneg_right (hE.sum_le_tsum S fun _ _ => norm_nonneg _) (by positivity)
      _ ≤ δ := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have hdiff : ‖topTraceC Z b u - topTraceC Z b v‖ ≤ 3 * δ := by
    have hPu := hS S le_rfl u
    have hPv := hS S le_rfl v
    have e : topTraceC Z b u - topTraceC Z b v =
        (topTraceC Z b u - ∑ z ∈ S, topTerm Z b z u) +
          (∑ z ∈ S, topTerm Z b z u - ∑ z ∈ S, topTerm Z b z v) -
            (topTraceC Z b v - ∑ z ∈ S, topTerm Z b z v) := by ring
    rw [e]
    calc ‖(topTraceC Z b u - ∑ z ∈ S, topTerm Z b z u) +
          (∑ z ∈ S, topTerm Z b z u - ∑ z ∈ S, topTerm Z b z v) -
            (topTraceC Z b v - ∑ z ∈ S, topTerm Z b z v)‖
        ≤ ‖(topTraceC Z b u - ∑ z ∈ S, topTerm Z b z u) +
          (∑ z ∈ S, topTerm Z b z u - ∑ z ∈ S, topTerm Z b z v)‖ +
            ‖topTraceC Z b v - ∑ z ∈ S, topTerm Z b z v‖ := norm_sub_le _ _
      _ ≤ (δ + δ) + δ := add_le_add ((norm_add_le _ _).trans (add_le_add hPu hPP)) hPv
      _ = 3 * δ := by ring
  have hre : topTrace Z b v - topTrace Z b u ≤ 3 * δ := by
    rw [topTrace_eq_re, topTrace_eq_re, ← Complex.sub_re]
    exact (Complex.re_le_norm _).trans (by rw [norm_sub_rev]; exact hdiff)
  linarith

/-- **The other side at every Bohr-dense set.** An upper bound `2 Re S(u) ≤ K` on a set that is
Bohr-dense at `+∞` puts every zero of a tempered configuration on the line, provided the maximal
real part is attained; real zeros are not excluded. -/
theorem onLine_of_bddAbove_of_isBohrDenseAtTop {T : Set ℝ} (hT : IsBohrDenseAtTop T)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier)
    (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) {K : ℝ}
    (hK : ∀ u ∈ T, 2 * (lagStructure Z (boxSpline 1 3) u).re ≤ K) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  rcases (half_le_of_max hρ₀ hmax).eq_or_lt with h | h
  · exact onLine_of_max_eq_half hmax h.symm
  exfalso
  have hb3 := contDiff_boxSpline (r := 1) one_pos 2
  have hbc := hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos 3)
  set b : ℝ := ρ₀.re - 1 / 2 with hbdef
  have hb0 : 0 < b := by rw [hbdef]; linarith
  have htop : TopDepth Z b := by
    intro z hz
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · have h1 := hmax _ h; simp at h1; rw [hbdef]; linarith
    · have h1 := hmax _ h; simp at h1; rw [hbdef]; linarith
  have hz₀ : evenCoeff Z (boxSpline 1 3) (ρ₀ - 1 / 2) ≠ 0 :=
    evenCoeff_sub_half_ne_zero_of_conj_symm Z hb3.continuous hbc
      (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ₀
      (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero (by linarith)))
  set g := topTraceC Z b with hgdef
  have hgc := continuous_topTraceC (b := b) hZ
  have hga := isBohrAlmostPeriodic_topTraceC (b := b) hZ
  -- the real coefficient `c = e_b`, real and nonnegative
  set c : ℂ := evenCoeff Z (boxSpline 1 3) (b : ℂ) with hcdef
  have hcim : c.im = 0 := by
    have h1 := evenCoeff_conj Z (b : ℂ)
    rw [Complex.conj_ofReal] at h1
    have h2 := congrArg Complex.im h1
    simp only [Complex.conj_im] at h2
    rw [hcdef]; linarith
  have hcre : 0 ≤ c.re := by
    by_cases hc0 : c = 0
    · rw [hc0]; simp
    · have hmem := mem_of_evenCoeff_ne_zero hc0
      have hx : (1 / 2 + (b : ℂ)) ∈ Z.carrier := by
        rcases hmem with h' | h'
        · exact h'
        · rwa [Complex.conj_ofReal] at h'
      exact (evenCoeff_spline_pos_of_real Z hx (by simp; exact hb0) (by simp)).le
  -- the mean of `F_top` is `c`
  have hmean : bohrMean g = c := by
    have h0 := bohrCoefficient_topTraceC (b := b) hZ (z₁ := (b : ℂ)) (by simp)
    rw [Complex.ofReal_im] at h0
    rw [← h0]
    unfold bohrCoefficient
    congr 1
    funext t
    simp [bohrChar]
  -- `c − F_top ≥ 0` has mean zero, so `F_top = c`
  have hgim : ∀ t, (g t).im = 0 := fun t => topTraceC_im t
  have hgre : ∀ t, (g t).re ≤ 0 := fun t => by
    rw [← topTrace_eq_re]
    exact topTrace_nonpos_of_isBohrDenseAtTop hZ htop hb0 hT hK t
  have hhc : Continuous fun t => c - g t := continuous_const.sub hgc
  have hha : _root_.HTGeometry.IsBohrAlmostPeriodic fun t => c - g t :=
    isBohrAlmostPeriodic_sub continuous_const (isBohrAlmostPeriodic_const _) hgc hga
  have hhmean : bohrMean (fun t => c - g t) = 0 := by
    rw [bohrMean_sub continuous_const (isBohrAlmostPeriodic_const _) hgc hga, hmean]
    have : bohrMean (fun _ : ℝ => c) = c := by
      have h1 := bohrMean_const_mul c continuous_const (isBohrAlmostPeriodic_const (1 : ℂ))
      have h2 := bohrMean_bohrChar 0
      have e1 : bohrChar 0 = fun _ : ℝ => (1 : ℂ) := by funext t; simp [bohrChar]
      rw [e1, if_pos rfl] at h2
      simpa [h2] using h1
    rw [this, sub_self]
  have hzero := eq_zero_of_bohrMean_eq_zero_of_nonneg hhc hha
    (fun t => by simp only [Complex.sub_re]; linarith [hgre t])
    (fun t => by simp only [Complex.sub_im]; rw [hcim, hgim t]; ring) hhmean
  have hgc' : ∀ t, g t = c := fun t => by have := hzero t; rw [sub_eq_zero] at this; exact this.symm
  have hc0 : c = 0 := by
    have h1 := hgre 0
    rw [hgc' 0] at h1
    exact Complex.ext (by linarith) hcim
  -- then `F_top = 0`, against the top coefficient
  have hz₀re : (ρ₀ - 1 / 2).re = b := by simp [hbdef]
  have hcoef := bohrCoefficient_topTraceC (b := b) hZ hz₀re
  have hg0 : g = fun _ => 0 := funext fun t => by rw [hgc' t, hc0]
  rw [← hgdef, hg0] at hcoef
  unfold bohrCoefficient at hcoef
  simp only [zero_mul] at hcoef
  rw [bohrMean_zero] at hcoef
  exact hz₀ hcoef.symm

/-- **Long runs see every attained top from above.** -/
theorem onLine_of_bddAbove_long_intervals_of_max {T : Set ℝ}
    (hT : ∀ L U : ℝ, ∃ a, U ≤ a ∧ Set.Icc a (a + L) ⊆ T)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ Z.carrier) (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) {K : ℝ}
    (hK : ∀ u ∈ T, 2 * (lagStructure Z (boxSpline 1 3) u).re ≤ K) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 :=
  onLine_of_bddAbove_of_isBohrDenseAtTop (isBohrDenseAtTop_of_long_intervals hT) Z hZ hρ₀ hmax hK

end GaloisForLFunctions.SurfaceOfSpecZ
