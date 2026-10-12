import GaloisForLFunctions.RHTower.XiCosineShiftDeepZeroBudget
import GaloisForLFunctions.RHTower.XiWindowNonrealBudget

/-!
# The off-line zero count of `Ξ` is the defect count of `cos(hD)Ξ` at small depth

For `h ∈ ℝ` let `A_h = cos(hD)Ξ = (Ξ(z + ih) + Ξ(z − ih))/2`.

**Theorem** (`eventually_sum_zeroMult_cosShiftXi_eq`). If `Ξ` has finitely many nonreal zeros,
`N` of them counted with multiplicity, then for every sufficiently small `h > 0` the nonreal zeros
of `A_h` are finite in number and have total multiplicity exactly `N`.

**Theorem** (`riemannHypothesis_iff_eventually_cosShiftXi_real`). RH holds iff `A_h` has only real
zeros for all sufficiently small `h > 0`.

**Proof.** Upper bound: the nonreal zeros of `A_h` count at most the zeros of `ξ` deeper than `h`
(`CosineDefectBudget.finite_nonreal_zeros_cosShiftXi`). For `h` below the smallest off-line depth
these are all off-line zeros on one side of the line, i.e. `N/2` of them, and the bound is `N`.
Lower bound: `A_h → Ξ` locally uniformly as `h → 0`. Hurwitz's theorem on discs isolating the
nonreal zeros of `Ξ` and avoiding the real axis gives, for small `h`, nonreal zeros of `A_h` of
total multiplicity at least `N`.
-/

open Complex Filter Topology Set Metric

namespace RHTower.CosineDefectLimit

open GaloisForLFunctions.HTGeometry RHTower.CosineDefectBudget

noncomputable section

/-- `cos(hD)Ξ → Ξ` locally uniformly as `h → 0`. -/
theorem tendstoLocallyUniformly_cosShiftXi :
    TendstoLocallyUniformly (fun h : ℝ => cosShiftXi h) XiC (𝓝 0) := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  have hK1 : IsCompact (cthickening 1 K) := hK.cthickening
  have hU := hK1.uniformContinuousOn_of_continuous differentiable_XiC'.continuous.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hU
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδU⟩ := hU ε hε
  have hball : ball (0 : ℝ) (min δ 1) ∈ 𝓝 (0 : ℝ) := ball_mem_nhds _ (lt_min hδ one_pos)
  filter_upwards [hball] with h hh z hz
  rw [mem_ball, Real.dist_eq, sub_zero] at hh
  have hhδ : |h| < δ := hh.trans_le (min_le_left _ _)
  have hh1 : |h| < 1 := hh.trans_le (min_le_right _ _)
  have hzK : z ∈ cthickening 1 K := self_subset_cthickening K hz
  have hnorm : ‖(h : ℂ) * I‖ = |h| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hmem : ∀ w : ℂ, ‖w - z‖ ≤ |h| → w ∈ cthickening 1 K := by
    intro w hw
    refine mem_cthickening_of_dist_le w z 1 K hz ?_
    rw [dist_eq_norm]; linarith
  have h1 : dist (XiC z) (XiC (z + h * I)) < ε :=
    hδU z hzK _ (hmem _ (by rw [add_sub_cancel_left, hnorm])) (by
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg, hnorm]; exact hhδ)
  have h2 : dist (XiC z) (XiC (z - h * I)) < ε :=
    hδU z hzK _ (hmem _ (by rw [sub_sub_cancel_left, norm_neg, hnorm])) (by
      rw [dist_eq_norm, sub_sub_cancel, hnorm]; exact hhδ)
  rw [dist_eq_norm] at h1 h2 ⊢
  unfold cosShiftXi
  have e : XiC z - (XiC (z + h * I) + XiC (z - h * I)) / 2 =
      ((XiC z - XiC (z + h * I)) + (XiC z - XiC (z - h * I))) / 2 := by ring
  rw [e, norm_div, Complex.norm_ofNat]
  linarith [norm_add_le (XiC z - XiC (z + h * I)) (XiC z - XiC (z - h * I))]

/-- **Hurwitz lower bound.** For a finite set `E` of nonreal points, for all small `h` the shift
`cos(hD)Ξ` has nonreal zeros of total multiplicity at least `Σ_{e∈E} ord_e Ξ`. -/
theorem eventually_exists_nonreal_zeros_ge (E : Finset ℂ) (hE : ∀ e ∈ E, e.im ≠ 0) :
    ∀ᶠ h in 𝓝 (0 : ℝ), ∃ F : Finset ℂ, (∀ z ∈ F, cosShiftXi h z = 0 ∧ z.im ≠ 0) ∧
      ∑ e ∈ E, zeroMult XiC e ≤ ∑ z ∈ F, zeroMult (cosShiftXi h) z := by
  classical
  choose ρ₀ hρ₀ hρ₀prop using fun e => exists_radius_zeroSumBall_eq_zeroMult differentiable_XiC'
    WindowNonrealBudget.analyticOrderAt_XiC_ne_top e
  obtain ⟨d, hd, hdsep⟩ := DeBruijn.exists_pos_sep E
  set r : ℂ → ℝ := fun e => min (ρ₀ e) (min (|e.im| / 2) (d / 3)) with hrdef
  have hrpos : ∀ e ∈ E, 0 < r e := fun e he =>
    lt_min (hρ₀ e) (lt_min (by have := abs_pos.mpr (hE e he); linarith) (by linarith))
  have havoid : ∀ e ∈ E, ∀ w ∈ ball e (r e), w.im ≠ 0 := by
    intro e he w hw hw0
    have h1 : |(w - e).im| ≤ ‖w - e‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, hw0, zero_sub, abs_neg] at h1
    rw [mem_ball, dist_eq_norm] at hw
    have hr2 : r e ≤ |e.im| / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hpos := abs_pos.mpr (hE e he)
    linarith
  have hdisj : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → Disjoint (ball e (r e)) (ball e' (r e')) := by
    intro e he e' he' hne
    refine Set.disjoint_left.mpr fun w hw hw' => ?_
    have h1 := hdsep e he e' he' hne
    have h2 : dist e e' ≤ dist e w + dist w e' := dist_triangle _ _ _
    rw [mem_ball] at hw hw'
    rw [dist_comm] at hw
    have h3 : r e ≤ d / 3 := (min_le_right _ _).trans (min_le_right _ _)
    have h4 : r e' ≤ d / 3 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hconv := tendstoLocallyUniformly_cosShiftXi
  have hev : ∀ e ∈ E, ∀ᶠ h in 𝓝 (0 : ℝ),
      zeroSumBall (cosShiftXi h) e (r e) = (zeroMult XiC e : ℂ) ∧
        ∀ w ∈ sphere e (r e), cosShiftXi h w ≠ 0 := by
    intro e he
    obtain ⟨hsph, hcount⟩ := hρ₀prop e (r e) (hrpos e he) (min_le_left _ _)
    have h1 := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly
      (fun h => differentiable_cosShiftXi h) differentiable_XiC' hconv (hrpos e he)
      (by linarith [hrpos e he] : r e < 2 * r e) hsph
    have h2 := eventually_ne_zero_on_sphere differentiable_XiC'.continuous hconv
      (hrpos e he).le hsph
    filter_upwards [h1, h2] with h hh1 hh2
    exact ⟨by rw [hh1, hcount], hh2⟩
  filter_upwards [(Filter.eventually_all_finset E).mpr hev] with h hh
  have hZ : ∀ e ∈ E, ∃ Z : Finset ℂ, (∀ z ∈ Z, z ∈ ball e (r e)) ∧
      (∀ z ∈ ball e (r e), cosShiftXi h z = 0 ↔ z ∈ Z) ∧
      zeroSumBall (cosShiftXi h) e (r e) = ∑ z ∈ Z, (zeroMult (cosShiftXi h) z : ℂ) := by
    intro e he
    exact exists_zeroSet_zeroSumBall (hrpos e he) (by linarith [hrpos e he] : r e < 2 * r e)
      isOpen_univ (subset_univ _) (differentiable_cosShiftXi h).differentiableOn (hh e he).2
  choose! Z hZball hZzero hZsum using hZ
  refine ⟨E.biUnion Z, fun z hz => ?_, ?_⟩
  · obtain ⟨e, he, hze⟩ := Finset.mem_biUnion.mp hz
    exact ⟨(hZzero e he z (hZball e he z hze)).mpr hze, havoid e he z (hZball e he z hze)⟩
  · rw [Finset.sum_biUnion]
    · refine Finset.sum_le_sum fun e he => ?_
      have h1 := (hh e he).1
      rw [hZsum e he] at h1
      have h2 : ((∑ z ∈ Z e, zeroMult (cosShiftXi h) z : ℕ) : ℂ) = (zeroMult XiC e : ℂ) := by
        push_cast; exact h1
      exact (Nat.cast_injective h2).ge
    · intro e he e' he' hne
      refine Finset.disjoint_left.mpr fun z hz hz' => ?_
      exact Set.disjoint_left.mp (hdisj e he e' he' hne) (hZball e he z hz) (hZball e' he' z hz')

/-! ## The exact law -/

theorem im_xiSpectralPoint_lineConj (q : XiZeroCopy) :
    (xiSpectralPoint (xiZeroCopyLineConjEquiv q)).im = -(xiSpectralPoint q).im := by
  rw [xiSpectralPoint_lineConj, Complex.conj_im]

/-- Off-line copies come in pairs: as many lie above the real axis as below it. -/
theorem card_nonrealCopies_eq_two_mul (hfin : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite) :
    hfin.toFinset.card = 2 * (hfin.toFinset.filter fun q => 0 < (xiSpectralPoint q).im).card := by
  classical
  set T := hfin.toFinset
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := T) (fun q : XiZeroCopy => 0 < (xiSpectralPoint q).im)
  have hneg : (T.filter fun q => ¬ 0 < (xiSpectralPoint q).im).card =
      (T.filter fun q => 0 < (xiSpectralPoint q).im).card := by
    refine Finset.card_nbij' (fun q => xiZeroCopyLineConjEquiv.symm q)
      (fun q => xiZeroCopyLineConjEquiv q) ?_ ?_ ?_ ?_
    · intro q hq
      simp only [Finset.coe_filter, Set.mem_setOf_eq, T, Set.Finite.mem_toFinset] at hq ⊢
      have him : (xiSpectralPoint (xiZeroCopyLineConjEquiv.symm q)).im =
          -(xiSpectralPoint q).im := by
        have := im_xiSpectralPoint_lineConj (xiZeroCopyLineConjEquiv.symm q)
        rw [Equiv.apply_symm_apply] at this
        linarith
      rw [him]
      refine ⟨neg_ne_zero.mpr hq.1, ?_⟩
      have := lt_of_le_of_ne (not_lt.mp hq.2) hq.1
      linarith
    · intro q hq
      simp only [Finset.coe_filter, Set.mem_setOf_eq, T, Set.Finite.mem_toFinset] at hq ⊢
      rw [im_xiSpectralPoint_lineConj]
      exact ⟨neg_ne_zero.mpr hq.1, by linarith [hq.2]⟩
    · intro q _; simp
    · intro q _; simp
  omega

/-- **The defect count of `cos(hD)Ξ` at small depth is the off-line zero count.** -/
theorem eventually_sum_zeroMult_cosShiftXi_eq
    (hfin : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), ∃ hZ : {z : ℂ | cosShiftXi h z = 0 ∧ z.im ≠ 0}.Finite,
      ∑ z ∈ hZ.toFinset, zeroMult (cosShiftXi h) z = hfin.toFinset.card := by
  classical
  set T := hfin.toFinset
  set P := T.filter fun q => 0 < (xiSpectralPoint q).im with hPdef
  -- below every positive depth, the deep copies are exactly `P`
  have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ q ∈ P, h < (xiSpectralPoint q).im := by
    refine (Filter.eventually_all_finset P).mpr fun q hq => ?_
    have hq' := (Finset.mem_filter.mp hq).2
    exact nhdsWithin_le_nhds (eventually_lt_nhds hq')
  have hEim : ∀ e ∈ T.image xiSpectralPoint, e.im ≠ 0 := by
    intro e he
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
    exact (hfin.mem_toFinset.mp hq)
  have hlow : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∃ F : Finset ℂ,
      (∀ z ∈ F, cosShiftXi h z = 0 ∧ z.im ≠ 0) ∧
      ∑ e ∈ T.image xiSpectralPoint, zeroMult XiC e ≤ ∑ z ∈ F, zeroMult (cosShiftXi h) z :=
    nhdsWithin_le_nhds (eventually_exists_nonreal_zeros_ge _ hEim)
  filter_upwards [hsmall, hlow, self_mem_nhdsWithin] with h hh hF hpos
  have hpos : 0 < h := hpos
  have hdeep : deepCopies h = (P : Set XiZeroCopy) := by
    ext q
    simp only [deepCopies, Set.mem_setOf_eq, Finset.coe_filter, hPdef, T, Set.Finite.mem_toFinset]
    constructor
    · intro hq; exact ⟨(lt_trans hpos hq).ne', lt_trans hpos hq⟩
    · intro hq; exact hh q (Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hq.1, hq.2⟩)
  have hS : (deepCopies h).Finite := by rw [hdeep]; exact P.finite_toSet
  have hScard : hS.toFinset.card = P.card := by
    congr 1; ext q; simp [hdeep]
  obtain ⟨hZ, hup⟩ := finite_nonreal_zeros_cosShiftXi hS
  refine ⟨hZ, le_antisymm ?_ ?_⟩
  · rw [hScard, ← card_nonrealCopies_eq_two_mul hfin] at hup
    exact hup
  · obtain ⟨F, hFz, hFge⟩ := hF
    rw [DeBruijn.card_nonrealCopies_eq_sum_zeroMult hfin, DeBruijn.riemannHeat_zero_eq_XiC]
    refine hFge.trans (Finset.sum_le_sum_of_subset fun z hz => ?_)
    exact hZ.mem_toFinset.mpr (hFz z hz)

/-- **RH ⟺ the cosine producer is lossless at every small depth.** -/
theorem riemannHypothesis_iff_eventually_cosShiftXi_real :
    RiemannHypothesis ↔ ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ z, cosShiftXi h z = 0 → z.im = 0 := by
  classical
  constructor
  · intro hRH
    have hreal := (riemannHypothesis_iff_XiC_zeros_real.mp hRH)
    have hno : ∀ h : ℝ, 0 ≤ h → deepCopies h = ∅ := by
      intro h hh
      ext q
      simp only [deepCopies, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [hreal _ (XiC_xiSpectralPoint_eq_zero q)]
      exact hh
    filter_upwards [self_mem_nhdsWithin] with h hh z hz
    exact cosShiftXi_zero_im_eq_zero_of_no_deep (hno h (le_of_lt hh)) hz
  · intro hev
    by_contra hRH
    rw [riemannHypothesis_iff_XiC_zeros_real] at hRH
    push Not at hRH
    obtain ⟨e, he0, heim⟩ := hRH
    have hlow : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∃ F : Finset ℂ,
        (∀ z ∈ F, cosShiftXi h z = 0 ∧ z.im ≠ 0) ∧
        ∑ e' ∈ ({e} : Finset ℂ), zeroMult XiC e' ≤ ∑ z ∈ F, zeroMult (cosShiftXi h) z :=
      nhdsWithin_le_nhds (eventually_exists_nonreal_zeros_ge {e} (by simpa using heim))
    obtain ⟨h, hreal, F, hFz, hFge⟩ := (hev.and hlow).exists
    have h1 : 1 ≤ zeroMult XiC e := one_le_zeroMult_of_eq_zero differentiable_XiC'
      WindowNonrealBudget.analyticOrderAt_XiC_ne_top he0
    rw [Finset.sum_singleton] at hFge
    obtain ⟨z, hz⟩ : F.Nonempty := by
      by_contra hF
      rw [Finset.not_nonempty_iff_eq_empty] at hF
      rw [hF, Finset.sum_empty] at hFge
      omega
    exact (hFz z hz).2 (hreal z (hFz z hz).1)

end

end RHTower.CosineDefectLimit
