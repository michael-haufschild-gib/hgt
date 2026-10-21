import GaloisForLFunctions.RHTower.UniformEulerTargetDensityOnDiscUnions
import GaloisForLFunctions.RHTower.ZetaDiscRecurrenceOnEveryClosedDiscOfTheStrip

/-!
# Bagchi's criterion: the Riemann hypothesis is the strong recurrence of `ζ` on compact sets

`ZetaStronglyRecurrent` asks that for every compact `K` of the open strip `1/2 < Re s < 1` and
every `ε > 0` the shifts `τ` with `sup_K |ζ(s + iτ) − ζ(s)| < ε` have positive lower density.
The direction `ZetaStronglyRecurrent → RiemannHypothesis` is
`riemannHypothesis_of_zetaStronglyRecurrent`.  Here the converse is proved.

Under the Riemann hypothesis, a compact `K` of the strip has real parts in `[a, b']` with
`1/2 < a`, `b' < 1`; it is covered by finitely many discs `closedBall (z i) (ρ₀/2)` centred in
`K`, with `ρ₀ = min(a − 1/2, 1 − b')/4`, and the doubled discs `closedBall (z i) (2ρ₀)` lie in a
disc of the half plane `Re s > 1/2`, on which `ζ` has no zero.  The Euler-target heights for `ζ`
on the union of the discs have positive lower density uniformly in the cutoff
(`exists_uniform_pos_density_eulerTargetReturnSet_zeta_union`), and the Euler tail is small on
every disc at once except on a set of heights of small density
(`eventually_eventually_volume_iUnion_eulerDiscTailBadSet_le`, a union bound over the per-disc tail
law), so `ζ` is strongly recurrent on the union, hence on `K`
(`zetaDiscStronglyRecurrentOn_of_riemannHypothesis_of_isCompact`).

Main theorem: `riemannHypothesis_iff_zetaStronglyRecurrent`.
-/

open Complex Filter Topology Finset Metric MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace RHTower

variable {ι : Type*} [Fintype ι]

/-! ## The Euler tail on a finite union of discs -/

/-- **Union bound for the Euler tail.**  On finitely many discs `closedBall (z i) (ρ i r₁)` with
`closedBall (z i) (ρ i R₂)` in the strip and `r₁ < R₂`, the heights at which the Euler tail is
large on some disc have density at most `δ`, for all large cutoffs. -/
theorem eventually_eventually_volume_iUnion_eulerDiscTailBadSet_le (z : ι → ℂ) {ρ : ι → ℝ}
    (hρ : ∀ i, 0 < ρ i) {R₂ : ℝ} (hhalf : ∀ i, 1 / 2 < (z i).re - ρ i * R₂)
    (hR₂1 : ∀ i, (z i).re + ρ i * R₂ < 1) {r₁ : ℝ} (hr₁ : r₁ < R₂) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) :
    ∀ᶠ y : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
      volume ((⋃ i, eulerDiscTailBadSet y (z i) (ρ i * r₁) ε) ∩ Icc 0 T)
        ≤ ENNReal.ofReal (δ * T) := by
  set δ' : ℝ := δ / (Fintype.card ι + 1) with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hsmall : ∀ i, ∀ᶠ y : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
      volume (eulerDiscTailBadSet y (z i) (ρ i * r₁) ε ∩ Icc 0 T) ≤ ENNReal.ofReal (δ' * T) :=
    fun i => eventually_eventually_volume_eulerDiscTailBadSet_le_of_lt
      (mul_lt_mul_of_pos_left hr₁ (hρ i)) (hhalf i) (hR₂1 i) hε hδ'0
  filter_upwards [Filter.eventually_all.mpr hsmall] with y hy
  have hcard : (Fintype.card ι : ℝ) * δ' ≤ δ := card_mul_div_card_add_one_le hδ.le _
  have hU : (⋃ i, eulerDiscTailBadSet y (z i) (ρ i * r₁) ε)
      = ⋃ i ∈ (Finset.univ : Finset ι), eulerDiscTailBadSet y (z i) (ρ i * r₁) ε := by simp
  filter_upwards [eventually_volume_biUnion_inter_Icc_le (Finset.univ : Finset ι)
    (fun i => eulerDiscTailBadSet y (z i) (ρ i * r₁) ε) (fun i _ => hy i),
    eventually_ge_atTop (0 : ℝ)] with T hT hT0
  rw [hU]
  calc volume ((⋃ i ∈ (Finset.univ : Finset ι), eulerDiscTailBadSet y (z i) (ρ i * r₁) ε)
        ∩ Icc 0 T)
      ≤ ENNReal.ofReal ((Finset.univ : Finset ι).card * δ' * T) := hT
    _ ≤ ENNReal.ofReal (δ * T) := by
        rw [Finset.card_univ]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hT0)

omit [Fintype ι] in
/-- Euler-target heights at which the tail is small on every disc are return heights of `ζ` on the
union. -/
theorem eulerTargetReturnSet_diff_iUnion_eulerDiscTailBadSet_subset_zetaReturnSet (y : ℕ)
    (z : ι → ℂ) (ρ : ι → ℝ) (r₁ ε ε' : ℝ) :
    eulerTargetReturnSet y riemannZeta (⋃ i, closedBall (z i) (ρ i * r₁)) ε
        \ (⋃ i, eulerDiscTailBadSet y (z i) (ρ i * r₁) ε')
      ⊆ zetaReturnSet (⋃ i, closedBall (z i) (ρ i * r₁)) (ε' + ε) := by
  rintro τ ⟨htarget, hgood⟩ s hs
  obtain ⟨i, hsi⟩ := mem_iUnion.mp hs
  have htail : ‖eulerTailFun y (s + τ * I)‖ < ε' := by
    by_contra hcon
    exact hgood (mem_iUnion.mpr ⟨i, s, hsi, not_lt.mp hcon⟩)
  have hh := htarget s hs
  have hid : riemannZeta (s + τ * I) - riemannZeta s =
      eulerTailFun y (s + τ * I) + (eulerPhaseProduct y 1 (s + τ * I) - riemannZeta s) := by
    unfold eulerTailFun
    ring
  rw [hid]
  exact (norm_add_le _ _).trans_lt (add_lt_add htail hh)

/-! ## Strong recurrence on a finite union of discs -/

/-- **Strong recurrence of `ζ` on a finite union of discs of a zero-free region.**  With the
common floor `σ₁` and ceiling `b`, the discs `closedBall (z i) (ρ i R₂)` in the strip, `R₂ > 1`,
contained in a zero-free disc `ball c₀ R₀`, and `r₁ < 1`: `ζ` is strongly recurrent on
`⋃_i closedBall (z i) (ρ i r₁)`. -/
theorem zetaDiscStronglyRecurrentOn_iUnion_closedBall_of_zeroFree (z : ι → ℂ) {ρ : ι → ℝ}
    (hρ : ∀ i, 0 < ρ i) {σ₁ : ℝ} (hσ₁ : 1 / 2 < σ₁) (hσ₁le : ∀ i, σ₁ ≤ (z i).re - ρ i)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1)
    {R₂ : ℝ} (hR₂ : 1 < R₂) (hhalf : ∀ i, 1 / 2 < (z i).re - ρ i * R₂)
    (hR₂1 : ∀ i, (z i).re + ρ i * R₂ < 1) {c₀ : ℂ} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hsub : ∀ i, ‖z i - c₀‖ + ρ i * R₂ < R₀) (hζ : ∀ s ∈ ball c₀ R₀, riemannZeta s ≠ 0)
    {r₁ : ℝ} (hr₁0 : 0 ≤ r₁) (hr₁ : r₁ < 1) :
    ZetaDiscStronglyRecurrentOn (⋃ i, closedBall (z i) (ρ i * r₁)) := by
  have hρR₂ : ∀ i, ρ i * R₂ < (z i).re := fun i => by linarith [hhalf i]
  intro ε hε
  obtain ⟨κ, hκ, y₁, hy₁⟩ := exists_uniform_pos_density_eulerTargetReturnSet_zeta_union z hρ hσ₁
    hσ₁le hb hb1 hR₂ hρR₂ hR₂1 hR₀ hsub hζ hr₁0 hr₁ (half_pos hε)
  have hbad := eventually_eventually_volume_iUnion_eulerDiscTailBadSet_le z hρ hhalf hR₂1
    (by linarith : r₁ < R₂) (half_pos hε) (half_pos hκ)
  obtain ⟨y, hy, hyb⟩ := ((eventually_ge_atTop y₁).and hbad).exists
  refine ⟨κ / 2, half_pos hκ, ?_⟩
  filter_upwards [hy₁ y hy, hyb, eventually_ge_atTop (0 : ℝ)] with T hT1 hT2 hT0
  have hsub' := eulerTargetReturnSet_diff_iUnion_eulerDiscTailBadSet_subset_zetaReturnSet y z ρ
    r₁ (ε / 2) (ε / 2)
  rw [add_halves] at hsub'
  exact (ofReal_half_le_volume_diff_inter hκ hT0 hT1 hT2).trans
    (measure_mono (inter_subset_inter_left _ hsub'))

/-! ## Compact sets of the strip -/

/-- A nonempty compact set of the open strip has its real parts in a closed interval `[a, b']`
of the strip. -/
theorem exists_strip_bounds_of_isCompact {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (hstrip : ∀ s ∈ K, 1 / 2 < s.re ∧ s.re < 1) :
    ∃ a b' : ℝ, 1 / 2 < a ∧ b' < 1 ∧ ∀ s ∈ K, a ≤ s.re ∧ s.re ≤ b' := by
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hne Complex.continuous_re.continuousOn
  exact ⟨x.re, y.re, (hstrip x hx).1, (hstrip y hy).2,
    fun s hs => ⟨isMinOn_iff.mp hmin s hs, isMaxOn_iff.mp hmax s hs⟩⟩

/-- **Under RH, `ζ` is strongly recurrent on every compact set of the open strip.** -/
theorem zetaDiscStronglyRecurrentOn_of_riemannHypothesis_of_isCompact (hRH : RiemannHypothesis)
    {K : Set ℂ} (hK : IsCompact K) (hstrip : ∀ s ∈ K, 1 / 2 < s.re ∧ s.re < 1) :
    ZetaDiscStronglyRecurrentOn K := by
  rcases K.eq_empty_or_nonempty with hemp | hne
  · rw [hemp]
    refine zetaDiscStronglyRecurrentOn_mono (Set.empty_subset _)
      (zetaDiscStronglyRecurrentOn_of_riemannHypothesis_of_closedBall hRH
        (c := ((3 / 4 : ℝ) : ℂ)) (r := 1 / 8) (by norm_num) ?_ ?_)
    · rw [Complex.ofReal_re]
      norm_num
    · rw [Complex.ofReal_re]
      norm_num
  obtain ⟨a, b', ha, hb', hab⟩ := exists_strip_bounds_of_isCompact hK hne hstrip
  -- the common radius and the finite cover
  set ρ₀ : ℝ := min (a - 1 / 2) (1 - b') / 4 with hρ₀
  have hmin : 0 < min (a - 1 / 2) (1 - b') := lt_min (by linarith) (by linarith)
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀]; positivity
  have hρ₀a : ρ₀ ≤ (a - 1 / 2) / 4 := by
    rw [hρ₀]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hρ₀b : ρ₀ ≤ (1 - b') / 4 := by
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
  -- the zero-free disc containing the doubled discs
  obtain ⟨c₀, R₀, hsub, hre⟩ :=
    exists_ball_re_gt_of_forall_lt z (r := fun i => ρ i * 2) (α := 1 / 2) hhalf
  obtain ⟨s₀, hs₀⟩ := hne
  obtain ⟨x₀, hx₀, -⟩ := Set.mem_iUnion₂.mp (hcov hs₀)
  have hR₀ : 0 < R₀ := by
    have h1 := hsub ⟨x₀, hx₀⟩
    have h2 : 0 ≤ ‖z ⟨x₀, hx₀⟩ - c₀‖ + ρ ⟨x₀, hx₀⟩ * 2 := by
      have := hρ ⟨x₀, hx₀⟩
      positivity
    linarith
  have hζ : ∀ s ∈ ball c₀ R₀, riemannZeta s ≠ 0 := fun s hs =>
    riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.mp hRH s
      (hre s (ball_subset_closedBall hs))
  -- strong recurrence on the union of the discs, hence on `K`
  have hrec := zetaDiscStronglyRecurrentOn_iUnion_closedBall_of_zeroFree z hρ hσ₁ hσ₁le hb hb1
    (by norm_num : (1 : ℝ) < 2) hhalf hR₂1 hR₀ hsub hζ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine zetaDiscStronglyRecurrentOn_mono ?_ hrec
  intro s hs
  obtain ⟨x, hx, hsx⟩ := Set.mem_iUnion₂.mp (hcov hs)
  refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
  rw [mem_ball] at hsx
  rw [mem_closedBall]
  show dist s x ≤ ρ₀ * (1 / 2)
  linarith

/-! ## Bagchi's criterion -/

/-- **The Riemann hypothesis implies Bagchi's strong recurrence of `ζ`.** -/
theorem zetaStronglyRecurrent_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ZetaStronglyRecurrent :=
  fun _ hK hstrip => zetaDiscStronglyRecurrentOn_of_riemannHypothesis_of_isCompact hRH hK hstrip

/-- **Bagchi's criterion.**  The Riemann hypothesis holds if and only if `ζ` is strongly
recurrent: for every compact `K` in `1/2 < Re s < 1` and every `ε > 0`, the shifts `τ` with
`sup_K |ζ(s + iτ) − ζ(s)| < ε` have positive lower density. -/
theorem riemannHypothesis_iff_zetaStronglyRecurrent :
    RiemannHypothesis ↔ ZetaStronglyRecurrent :=
  ⟨zetaStronglyRecurrent_of_riemannHypothesis, riemannHypothesis_of_zetaStronglyRecurrent⟩

end RHTower
