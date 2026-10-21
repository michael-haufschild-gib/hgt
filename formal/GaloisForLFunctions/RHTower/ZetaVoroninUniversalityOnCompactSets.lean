import GaloisForLFunctions.RHTower.ZetaStrongRecurrenceOnCompactSets
import GaloisForLFunctions.RHTower.ZetaTypicalHeightApproximationExcludesZeroTargets

/-!
# Voronin universality of `ζ` on compact sets of the strip, for targets analytic on a disc

Let `K` be a compact subset of the open strip `1/2 < Re s < 1` and let `g` be analytic and
nonvanishing on an open disc `ball c₀ R₀` containing `K` (the disc may leave the strip; `K` may
be tall).  Then for every `ε > 0` the shifts `τ` with `sup_K |ζ(s + iτ) − g(s)| < ε` have positive
lower density (`exists_pos_density_zetaTargetReturnSet_of_isCompact`).  This is unconditional.

The mechanism is the joint-phase machinery of the Bagchi criterion with `ζ` replaced by `g`: on a
finite cover of `K` by discs whose enlarged discs lie in the strip and in `ball c₀ R₀`, the tuple
of an analytic logarithm of `g` lies in the closed span of the prime tuples, the finite Euler
products with joint phases approximate `g` on all the discs with cutoff-uniform positive density
(`exists_uniform_pos_density_eulerTargetReturnSet_exp_union`), and the Euler tail is small on all
discs outside a set of heights of small density.  Special cases: nonzero constants, nonvanishing
entire functions, and polynomials without zeros on a disc containing `K`.
-/

open Complex Filter Topology Finset Metric MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open scoped ENNReal

noncomputable section

namespace RHTower

variable {ι : Type*} [Fintype ι]

/-! ## Return heights to a target on a finite union of discs -/

omit [Fintype ι] in
/-- Euler-target heights at which the tail is small on every disc are target-return heights of
`ζ` on the union. -/
theorem eulerTargetReturnSet_diff_iUnion_eulerDiscTailBadSet_subset_zetaTargetReturnSet (y : ℕ)
    (g : ℂ → ℂ) (z : ι → ℂ) (ρ : ι → ℝ) (r₁ ε ε' : ℝ) :
    eulerTargetReturnSet y g (⋃ i, closedBall (z i) (ρ i * r₁)) ε
        \ (⋃ i, eulerDiscTailBadSet y (z i) (ρ i * r₁) ε')
      ⊆ zetaTargetReturnSet g (⋃ i, closedBall (z i) (ρ i * r₁)) (ε' + ε) := by
  rintro τ ⟨htarget, hgood⟩ s hs
  obtain ⟨i, hsi⟩ := mem_iUnion.mp hs
  have htail : ‖eulerTailFun y (s + τ * I)‖ < ε' := by
    by_contra hcon
    exact hgood (mem_iUnion.mpr ⟨i, s, hsi, not_lt.mp hcon⟩)
  have hh := htarget s hs
  have hid : riemannZeta (s + τ * I) - g s =
      eulerTailFun y (s + τ * I) + (eulerPhaseProduct y 1 (s + τ * I) - g s) := by
    unfold eulerTailFun
    ring
  rw [hid]
  exact (norm_add_le _ _).trans_lt (add_lt_add htail hh)

/-- Target-return heights pass to subsets of `K`. -/
theorem zetaTargetReturnSet_mono (g : ℂ → ℂ) {K K' : Set ℂ} (h : K' ⊆ K) (ε : ℝ) :
    zetaTargetReturnSet g K ε ⊆ zetaTargetReturnSet g K' ε :=
  fun _ hτ s hs => hτ s (h hs)

/-- **Positive lower density of the target-return heights on a finite union of discs**, for a
target `g` continuous on the union whose logarithm tuple lies in `primeSpan`; the enlarged discs
`closedBall (z i) (ρ i R₂)` lie in the strip. -/
theorem exists_pos_density_zetaTargetReturnSet_iUnion_closedBall (z : ι → ℂ) {ρ : ι → ℝ}
    (hρ : ∀ i, 0 < ρ i) {σ₁ : ℝ} (hσ₁ : 1 / 2 < σ₁) (hσ₁le : ∀ i, σ₁ ≤ (z i).re - ρ i)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1)
    {R₂ : ℝ} (hR₂ : 1 < R₂) (hhalf : ∀ i, 1 / 2 < (z i).re - ρ i * R₂)
    (hR₂1 : ∀ i, (z i).re + ρ i * R₂ < 1)
    {L : DiscTuple ι} (hL : L ∈ primeSpan z (fun i => (hρ i).le)) {g : ℂ → ℂ}
    (hexpL : ∀ i, ∀ q : ℂ, ‖q‖ < 1 → Complex.exp (hardyFun (L i) q) = g (z i + ρ i * q))
    {r₁ : ℝ} (hr₁0 : 0 ≤ r₁) (hr₁ : r₁ < 1)
    (hg : ContinuousOn g (⋃ i, closedBall (z i) (ρ i * r₁))) {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ᶠ T in atTop, ENNReal.ofReal (c * T) ≤
      volume (zetaTargetReturnSet g (⋃ i, closedBall (z i) (ρ i * r₁)) ε ∩ Icc 0 T) := by
  have hρR₂ : ∀ i, ρ i * R₂ < (z i).re := fun i => by linarith [hhalf i]
  obtain ⟨κ, hκ, y₁, hy₁⟩ := exists_uniform_pos_density_eulerTargetReturnSet_exp_union z hρ hσ₁
    hσ₁le hb hb1 hR₂ hρR₂ hL hexpL hr₁0 hr₁ hg (half_pos hε)
  have hbad := eventually_eventually_volume_iUnion_eulerDiscTailBadSet_le z hρ hhalf hR₂1
    (by linarith : r₁ < R₂) (half_pos hε) (half_pos hκ)
  obtain ⟨y, hy, hyb⟩ := ((eventually_ge_atTop y₁).and hbad).exists
  refine ⟨κ / 2, half_pos hκ, ?_⟩
  filter_upwards [hy₁ y hy, hyb, eventually_ge_atTop (0 : ℝ)] with T hT1 hT2 hT0
  have hsub' := eulerTargetReturnSet_diff_iUnion_eulerDiscTailBadSet_subset_zetaTargetReturnSet y
    g z ρ r₁ (ε / 2) (ε / 2)
  rw [add_halves] at hsub'
  exact (ofReal_half_le_volume_diff_inter hκ hT0 hT1 hT2).trans
    (measure_mono (inter_subset_inter_left _ hsub'))

/-- **Universality on a finite union of discs for a target analytic and nonvanishing on a disc
containing the enlarged discs.** -/
theorem exists_pos_density_zetaTargetReturnSet_iUnion_closedBall_of_analyticOnNhd (z : ι → ℂ)
    {ρ : ι → ℝ} (hρ : ∀ i, 0 < ρ i) {σ₁ : ℝ} (hσ₁ : 1 / 2 < σ₁)
    (hσ₁le : ∀ i, σ₁ ≤ (z i).re - ρ i) {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1)
    {R₂ : ℝ} (hR₂ : 1 < R₂) (hhalf : ∀ i, 1 / 2 < (z i).re - ρ i * R₂)
    (hR₂1 : ∀ i, (z i).re + ρ i * R₂ < 1) {c₀ : ℂ} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hsub : ∀ i, ‖z i - c₀‖ + ρ i * R₂ < R₀) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball c₀ R₀)) (hg0 : ∀ s ∈ ball c₀ R₀, g s ≠ 0)
    {r₁ : ℝ} (hr₁0 : 0 ≤ r₁) (hr₁ : r₁ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ᶠ T in atTop, ENNReal.ofReal (c * T) ≤
      volume (zetaTargetReturnSet g (⋃ i, closedBall (z i) (ρ i * r₁)) ε ∩ Icc 0 T) := by
  have hρ' : ∀ i, 0 ≤ ρ i := fun i => (hρ i).le
  obtain ⟨F, hF, hexpF⟩ := exists_analyticOnNhd_exp_eq_ball hR₀ hg hg0
  obtain ⟨L, hL, hLfun⟩ :=
    exists_mem_primeSpan_of_differentiableOn_ball z hρ' hb hb1 hR₂ hsub hF.differentiableOn
  have hexpL : ∀ i, ∀ q : ℂ, ‖q‖ < 1 → Complex.exp (hardyFun (L i) q) = g (z i + ρ i * q) := by
    intro i q hq
    have hqR : q ∈ closedBall (0 : ℂ) R₂ := by
      rw [mem_closedBall, dist_zero_right]
      linarith
    rw [hLfun i q hq, hexpF _ (mapsTo_disc_coordinate z hρ' hsub i hqR)]
  have hKsub : (⋃ i, closedBall (z i) (ρ i * r₁)) ⊆ ball c₀ R₀ := by
    intro s hs
    obtain ⟨i, hsi⟩ := mem_iUnion.mp hs
    rw [mem_closedBall, dist_eq_norm] at hsi
    rw [mem_ball, dist_eq_norm]
    have h1 : ρ i * r₁ ≤ ρ i * R₂ := mul_le_mul_of_nonneg_left (by linarith) (hρ' i)
    calc ‖s - c₀‖ = ‖(s - z i) + (z i - c₀)‖ := by congr 1; ring
      _ ≤ ‖s - z i‖ + ‖z i - c₀‖ := norm_add_le _ _
      _ < R₀ := by linarith [hsub i]
  exact exists_pos_density_zetaTargetReturnSet_iUnion_closedBall z hρ hσ₁ hσ₁le hb hb1 hR₂ hhalf
    hR₂1 hL hexpL hr₁0 hr₁ (hg.continuousOn.mono hKsub) hε

/-! ## Compact sets of the strip -/

/-- **Voronin universality of `ζ` on compact sets of the strip.**  For `K` compact in
`1/2 < Re s < 1`, contained in an open disc `ball c₀ R₀` on which `g` is analytic and nonvanishing,
and every `ε > 0`, the shifts `τ` with `sup_K |ζ(s + iτ) − g(s)| < ε` have positive lower
density. -/
theorem exists_pos_density_zetaTargetReturnSet_of_isCompact {K : Set ℂ} (hK : IsCompact K)
    (hstrip : ∀ s ∈ K, 1 / 2 < s.re ∧ s.re < 1) {c₀ : ℂ} {R₀ : ℝ} (hKsub : K ⊆ ball c₀ R₀)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (ball c₀ R₀)) (hg0 : ∀ s ∈ ball c₀ R₀, g s ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ᶠ T in atTop, ENNReal.ofReal (c * T) ≤
      volume (zetaTargetReturnSet g K ε ∩ Icc 0 T) := by
  rcases K.eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, Filter.Eventually.of_forall fun T => ?_⟩
    have huniv : zetaTargetReturnSet g K ε = univ := by
      ext τ
      simp [zetaTargetReturnSet, hemp]
    rw [huniv, Set.univ_inter, Real.volume_Icc, one_mul, sub_zero]
  obtain ⟨a, b', ha, hb', hab⟩ := exists_strip_bounds_of_isCompact hK hne hstrip
  -- the margin to the boundary of the disc
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne (f := fun s : ℂ => ‖s - c₀‖) (by fun_prop)
  have hxR : ‖x - c₀‖ < R₀ := by
    have := hKsub hx
    rwa [mem_ball, dist_eq_norm] at this
  set η : ℝ := R₀ - ‖x - c₀‖ with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  have hKR : ∀ s ∈ K, ‖s - c₀‖ ≤ R₀ - η := fun s hs => by
    have := isMaxOn_iff.mp hmax s hs
    beta_reduce at this
    rw [hη]
    linarith
  -- the common radius and the finite cover
  set ρ₀ : ℝ := min (min (a - 1 / 2) (1 - b')) η / 4 with hρ₀
  have hmin : 0 < min (min (a - 1 / 2) (1 - b')) η := lt_min (lt_min (by linarith) (by linarith)) hηpos
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀]; positivity
  have hρ₀a : ρ₀ ≤ (a - 1 / 2) / 4 := by
    rw [hρ₀]
    exact div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) (by norm_num)
  have hρ₀b : ρ₀ ≤ (1 - b') / 4 := by
    rw [hρ₀]
    exact div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _)) (by norm_num)
  have hρ₀η : ρ₀ ≤ η / 4 := by
    rw [hρ₀]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun s => ball s (ρ₀ / 2))
    fun s _ => ball_mem_nhds s (by positivity)
  -- the disc family indexed by the centres
  let z : t → ℂ := fun i => (i : ℂ)
  let ρ : t → ℝ := fun _ => ρ₀
  have hρ : ∀ i, 0 < ρ i := fun _ => hρ₀pos
  have hreK : ∀ i : t, a ≤ (z i).re ∧ (z i).re ≤ b' := fun i => hab _ (htK _ i.2)
  have hσ₁ : 1 / 2 < a - ρ₀ := by linarith
  have hσ₁le : ∀ i, a - ρ₀ ≤ (z i).re - ρ i := fun i => by
    have := (hreK i).1
    simp only [ρ]
    linarith
  have hb : ∀ i, (z i).re + ρ i ≤ b' + ρ₀ := fun i => by
    have := (hreK i).2
    simp only [ρ]
    linarith
  have hb1 : b' + ρ₀ < 1 := by linarith
  have hhalf : ∀ i, 1 / 2 < (z i).re - ρ i * 2 := fun i => by
    have := (hreK i).1
    simp only [ρ]
    linarith
  have hR₂1 : ∀ i, (z i).re + ρ i * 2 < 1 := fun i => by
    have := (hreK i).2
    simp only [ρ]
    linarith
  have hsub : ∀ i, ‖z i - c₀‖ + ρ i * 2 < R₀ := fun i => by
    have := hKR _ (htK _ i.2)
    simp only [ρ]
    linarith
  have hR₀ : 0 < R₀ := by
    obtain ⟨s₀, hs₀⟩ := hne
    have := hKsub hs₀
    rw [mem_ball] at this
    linarith [dist_nonneg (x := s₀) (y := c₀)]
  obtain ⟨c, hc, hT⟩ := exists_pos_density_zetaTargetReturnSet_iUnion_closedBall_of_analyticOnNhd
    z hρ hσ₁ hσ₁le hb hb1 (by norm_num : (1 : ℝ) < 2) hhalf hR₂1 hR₀ hsub hg hg0
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hε
  refine ⟨c, hc, hT.mono fun T hT => hT.trans (measure_mono (inter_subset_inter_left _ ?_))⟩
  refine zetaTargetReturnSet_mono g ?_ ε
  intro s hs
  obtain ⟨x', hx', hsx⟩ := Set.mem_iUnion₂.mp (hcov hs)
  refine Set.mem_iUnion.mpr ⟨⟨x', hx'⟩, ?_⟩
  rw [mem_ball] at hsx
  rw [mem_closedBall]
  show dist s x' ≤ ρ₀ * (1 / 2)
  linarith

/-! ## Special cases -/

/-- **Nonzero constants** are approximated by `ζ` uniformly on every compact set of the strip at
positive lower density. -/
theorem exists_pos_density_zetaTargetReturnSet_const_of_isCompact {K : Set ℂ} (hK : IsCompact K)
    (hstrip : ∀ s ∈ K, 1 / 2 < s.re ∧ s.re < 1) {w : ℂ} (hw : w ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ᶠ T in atTop, ENNReal.ofReal (c * T) ≤
      volume (zetaTargetReturnSet (fun _ => w) K ε ∩ Icc 0 T) := by
  obtain ⟨R₀, hKsub⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).mp hK.isBounded
  exact exists_pos_density_zetaTargetReturnSet_of_isCompact hK hstrip hKsub analyticOnNhd_const
    (fun _ _ => hw) hε

/-- **Nonvanishing entire functions** are approximated by `ζ` uniformly on every compact set of
the strip at positive lower density. -/
theorem exists_pos_density_zetaTargetReturnSet_of_differentiable_of_isCompact {K : Set ℂ}
    (hK : IsCompact K) (hstrip : ∀ s ∈ K, 1 / 2 < s.re ∧ s.re < 1) {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hg0 : ∀ s, g s ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ᶠ T in atTop, ENNReal.ofReal (c * T) ≤
      volume (zetaTargetReturnSet g K ε ∩ Icc 0 T) := by
  obtain ⟨R₀, hKsub⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).mp hK.isBounded
  exact exists_pos_density_zetaTargetReturnSet_of_isCompact hK hstrip hKsub
    (hg.differentiableOn.analyticOnNhd isOpen_ball) (fun s _ => hg0 s) hε

end RHTower
