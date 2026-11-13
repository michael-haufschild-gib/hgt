import GaloisForLFunctions.GaloisTheoryOfZeros.TheSheetsOfACollisionAreAllItsZeros

/-!
# A zero continues along a path of times until it escapes

The heat cover is not proper over the plane of times: it has infinitely many sheets. This file
determines what the local theory gives for the continuation of a zero along a path of times
`γ : [0, 1] → ℂ` that avoids the branch times.

* **Charts.** Near a simple zero `(τ₀, z₀)` the cover is the graph of a continuous function of the
  time: there are discs `U ∋ τ₀`, `V ∋ z₀` and `ζ : U → V` such that for `τ ∈ U` the only zero of
  `H_τ` in `V` is `ζ(τ)` (`exists_zero_chart`).
* **Uniqueness.** Two lifts of `γ` that start at the same zero agree (`IsZeroLift.eqOn`), and two
  lifts that meet at one parameter start at the same zero (`IsZeroLift.eq_zero_of_eq`). So the
  transport of zeros along `γ` is an injective partial map from the fibre over `γ(0)` to the fibre
  over `γ(1)`.
* **The alternative.** A zero `z₀` of `H_{γ(0)}` either lifts along the whole path, or it escapes
  (`EscapesAlong`): it lifts on a half-open interval `[0, b)` and its modulus tends to infinity as
  the parameter tends to `b` (`exists_isZeroLift_or_escape`). There is no third case: a lift that
  stays bounded along a sequence of parameters converges to a simple zero and enters its chart.
  The two cases exclude each other (`IsZeroLift.not_escapesAlong`). The relative form
  (`exists_isZeroLift_or_escape_of_mem`) needs simple zeros only in a closed set of places in
  which the lifts of `z₀` stay; its path may cross branch times.

The transport along a loop is therefore a permutation of exactly those zeros that do not escape
along the loop or along its inverse. The monodromy group of the heat cover over a set of times is
defined as soon as no zero escapes over that set.
-/

open Complex Filter Topology Set Metric
open RHTower RHTower.DeBruijn GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## The chart of a simple zero -/

private theorem fderiv_complexHeat_ne_zero {τ₀ z₀ : ℂ} (h1 : deriv (complexHeat τ₀) z₀ ≠ 0) :
    (fderiv ℂ (fun p : ℂ × ℂ => complexHeat p.1 p.2) (τ₀, z₀)) (0, 1) ≠ 0 := by
  have hd := (analyticAt_complexHeat (τ₀, z₀)).differentiableAt.hasFDerivAt
  have hline : HasDerivAt (fun z : ℂ => (τ₀, z)) ((0 : ℂ), (1 : ℂ)) z₀ :=
    (hasDerivAt_const z₀ τ₀).prodMk (hasDerivAt_id z₀)
  have h2 := hd.comp_hasDerivAt z₀ hline
  have h3 : ((fun p : ℂ × ℂ => complexHeat p.1 p.2) ∘ fun z : ℂ => (τ₀, z)) = complexHeat τ₀ :=
    rfl
  rw [h3] at h2
  rwa [h2.deriv] at h1

/-- **The chart of a simple zero.** Near a simple zero `(τ₀, z₀)` the zeros of the family form the
graph of a continuous function `ζ` of the time: for `τ` in a disc around `τ₀` the point `ζ(τ)` is
the only zero of `H_τ` in a fixed disc around `z₀`. -/
theorem exists_zero_chart {τ₀ z₀ : ℂ} (h0 : complexHeat τ₀ z₀ = 0)
    (h1 : deriv (complexHeat τ₀) z₀ ≠ 0) :
    ∃ δ > 0, ∃ ρ > 0, ∃ ζ : ℂ → ℂ, ContinuousOn ζ (ball τ₀ δ) ∧ ζ τ₀ = z₀ ∧
      ∀ τ ∈ ball τ₀ δ, ζ τ ∈ ball z₀ ρ ∧ complexHeat τ (ζ τ) = 0 ∧
        ∀ z ∈ ball z₀ ρ, complexHeat τ z = 0 → z = ζ τ := by
  have hc : IsCollision τ₀ z₀ 1 := by
    refine ⟨fun i hi => ?_, by rwa [iteratedDeriv_one]⟩
    obtain rfl : i = 0 := by omega
    rwa [iteratedDeriv_zero]
  obtain ⟨ρ, hρ, huniq, hev⟩ := exists_ball_simple_zeros hc
  obtain ⟨ζ, hζan, hζ0, hζzero, -⟩ := parametric_holo_implicit_unique
    (f := fun p : ℂ × ℂ => complexHeat p.1 p.2) (analyticAt_complexHeat (τ₀, z₀)) h0
    (fderiv_complexHeat_ne_zero h1)
  have hball : ∀ᶠ τ in 𝓝 τ₀, ζ τ ∈ ball z₀ ρ := by
    have h := hζan.continuousAt.tendsto
    rw [hζ0] at h
    exact h.eventually_mem (ball_mem_nhds z₀ hρ)
  have hcount : ∀ᶠ τ in 𝓝 τ₀, τ ≠ τ₀ →
      {z | z ∈ ball z₀ ρ ∧ complexHeat τ z = 0}.ncard = 1 := by
    filter_upwards [eventually_nhdsWithin_iff.1 hev] with τ hτ hne
    exact (hτ hne).2
  obtain ⟨δ, hδ, hsub⟩ := Metric.eventually_nhds_iff.1
    (((hζzero.and hball).and hζan.eventually_analyticAt).and hcount)
  refine ⟨δ, hδ, ρ, hρ, ζ, fun τ hτ => (hsub hτ).1.2.continuousAt.continuousWithinAt, hζ0,
    fun τ hτ => ?_⟩
  obtain ⟨⟨⟨hz, hb⟩, -⟩, hcnt⟩ := hsub hτ
  refine ⟨hb, hz, fun z hzb hzz => ?_⟩
  by_cases hne : τ = τ₀
  · rw [hne] at hzz ⊢
    rw [hζ0]
    exact huniq z hzb hzz
  · obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 (hcnt hne)
    have h1' : z ∈ {z | z ∈ ball z₀ ρ ∧ complexHeat τ z = 0} := ⟨hzb, hzz⟩
    have h2' : ζ τ ∈ {z | z ∈ ball z₀ ρ ∧ complexHeat τ z = 0} := ⟨hb, hz⟩
    rw [ha] at h1' h2'
    exact (mem_singleton_iff.1 h1').trans (mem_singleton_iff.1 h2').symm

/-! ## Lifts of a path of times -/

private theorem tendsto_nhdsGT_of_continuousOn {f : ℝ → ℂ} {a b x : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hx : x ∈ Ico a b) : Tendsto f (𝓝[>] x) (𝓝 (f x)) :=
  (hf x ⟨hx.1, hx.2.le⟩).tendsto.mono_left (nhdsWithin_le_of_mem
    (mem_of_superset (Ioc_mem_nhdsGT hx.2) fun _ hs => ⟨hx.1.trans hs.1.le, hs.2⟩))

private theorem continuousOn_glue {f g : ℝ → ℂ} {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hf : ContinuousOn f (Icc a c)) (hg : ContinuousOn g (Icc c b)) (hfg : f c = g c) :
    ContinuousOn (fun s => if s ≤ c then f s else g s) (Icc a b) := by
  rw [← Icc_union_Icc_eq_Icc hac hcb]
  refine ContinuousOn.union_of_isClosed (hf.congr fun _ hs => if_pos hs.2)
    (hg.congr fun s hs => ?_) isClosed_Icc isClosed_Icc
  rcases eq_or_lt_of_le hs.1 with h | h
  · show (if s ≤ c then f s else g s) = g s
    rw [if_pos h.ge, ← h, hfg]
  · exact if_neg (not_le.2 h)

/-- **A lift that enters a chart stays on its branch.** While the time stays in the disc of a
chart, a continuous family of zeros that starts in the disc of zeros is the branch of the chart. -/
theorem eqOn_chart {γ w : ℝ → ℂ} {a c : ℝ} {τ₀ z₀ : ℂ} {δ ρ : ℝ} {ζ : ℂ → ℂ}
    (hζc : ContinuousOn ζ (ball τ₀ δ))
    (hchart : ∀ τ ∈ ball τ₀ δ, ζ τ ∈ ball z₀ ρ ∧ complexHeat τ (ζ τ) = 0 ∧
      ∀ z ∈ ball z₀ ρ, complexHeat τ z = 0 → z = ζ τ)
    (hγ : ContinuousOn γ (Icc a c)) (hγU : ∀ s ∈ Icc a c, γ s ∈ ball τ₀ δ)
    (hw : ContinuousOn w (Icc a c)) (hzero : ∀ s ∈ Icc a c, complexHeat (γ s) (w s) = 0)
    (ha : w a ∈ ball z₀ ρ) : ∀ s ∈ Icc a c, w s = ζ (γ s) := by
  rcases lt_or_ge c a with hac | hac
  · exact fun s hs => absurd (hs.1.trans hs.2) (not_le.2 hac)
  have hζγ : ContinuousOn (fun s => ζ (γ s)) (Icc a c) := hζc.comp hγ hγU
  have hclosed : IsClosed ({s | w s = ζ (γ s)} ∩ Icc a c) := by
    have h := (hw.sub hζγ).preimage_isClosed_of_isClosed isClosed_Icc
      (isClosed_singleton (x := (0 : ℂ)))
    have hset : {s | w s = ζ (γ s)} ∩ Icc a c =
        Icc a c ∩ (fun s => w s - ζ (γ s)) ⁻¹' {0} := by
      ext s
      simp only [mem_inter_iff, mem_setOf_eq, mem_preimage, mem_singleton_iff, sub_eq_zero]
      exact and_comm
    rw [hset]
    exact h
  have haI : a ∈ Icc a c := ⟨le_rfl, hac⟩
  refine hclosed.Icc_subset_of_forall_mem_nhdsWithin
    ((hchart (γ a) (hγU a haI)).2.2 (w a) ha (hzero a haI)) fun x hx => ?_
  obtain ⟨hxeq, hxI⟩ := hx
  have hxI' : x ∈ Icc a c := ⟨hxI.1, hxI.2.le⟩
  have hwx : w x ∈ ball z₀ ρ := by
    rw [show w x = ζ (γ x) from hxeq]
    exact (hchart (γ x) (hγU x hxI')).1
  have e1 := (tendsto_nhdsGT_of_continuousOn hw hxI).eventually_mem (isOpen_ball.mem_nhds hwx)
  have e2 : ∀ᶠ s in 𝓝[>] x, s ∈ Icc a c :=
    mem_of_superset (Ioc_mem_nhdsGT hxI.2) fun s hs => ⟨hxI.1.trans hs.1.le, hs.2⟩
  filter_upwards [e1, e2] with s hs1 hs2
  exact (hchart (γ s) (hγU s hs2)).2.2 (w s) hs1 (hzero s hs2)

/-- A lift of the path of times `γ` on `[0, b]`: a continuous choice of a zero of `H_{γ(s)}`. -/
structure IsZeroLift (γ : ℝ → ℂ) (b : ℝ) (z : ℝ → ℂ) : Prop where
  continuousOn : ContinuousOn z (Icc 0 b)
  zero : ∀ s ∈ Icc (0 : ℝ) b, complexHeat (γ s) (z s) = 0

variable {γ : ℝ → ℂ}

theorem IsZeroLift.mono {b b' : ℝ} {z : ℝ → ℂ} (h : IsZeroLift γ b z) (hb : b' ≤ b) :
    IsZeroLift γ b' z :=
  ⟨h.continuousOn.mono (Icc_subset_Icc_right hb), fun s hs =>
    h.zero s (Icc_subset_Icc_right hb hs)⟩

/-- **Uniqueness of lifts.** Two lifts through simple zeros that start at the same zero agree. -/
theorem IsZeroLift.eqOn {b : ℝ} {z₁ z₂ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 b))
    (h₁ : IsZeroLift γ b z₁) (h₂ : IsZeroLift γ b z₂) (h0 : z₁ 0 = z₂ 0)
    (hsimple : ∀ s ∈ Icc (0 : ℝ) b, deriv (complexHeat (γ s)) (z₁ s) ≠ 0) :
    EqOn z₁ z₂ (Icc 0 b) := by
  have hclosed : IsClosed ({s | z₁ s = z₂ s} ∩ Icc 0 b) := by
    have h := (h₁.continuousOn.sub h₂.continuousOn).preimage_isClosed_of_isClosed isClosed_Icc
      (isClosed_singleton (x := (0 : ℂ)))
    have hset : {s | z₁ s = z₂ s} ∩ Icc 0 b = Icc 0 b ∩ (fun s => z₁ s - z₂ s) ⁻¹' {0} := by
      ext s
      simp only [mem_inter_iff, mem_setOf_eq, mem_preimage, mem_singleton_iff, sub_eq_zero]
      exact and_comm
    rw [hset]
    exact h
  refine hclosed.Icc_subset_of_forall_mem_nhdsWithin h0 fun x hx => ?_
  obtain ⟨hxeq, hxI⟩ := hx
  have hxI' : x ∈ Icc (0 : ℝ) b := ⟨hxI.1, hxI.2.le⟩
  obtain ⟨δ, hδ, ρ, hρ, ζ, hζc, -, hchart⟩ :=
    exists_zero_chart (h₁.zero x hxI') (hsimple x hxI')
  obtain ⟨ε, hε, hεball⟩ := Metric.continuousWithinAt_iff.1 (hγ x hxI') δ hδ
  have hxc : x < min b (x + ε / 2) := lt_min hxI.2 (by linarith)
  have hsub : Icc x (min b (x + ε / 2)) ⊆ Icc 0 b := fun s hs =>
    ⟨hxI.1.trans hs.1, hs.2.trans (min_le_left _ _)⟩
  have hγU : ∀ s ∈ Icc x (min b (x + ε / 2)), γ s ∈ ball (γ x) δ := fun s hs => by
    refine hεball (hsub hs) ?_
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hs.1)]
    have := hs.2.trans (min_le_right b (x + ε / 2))
    linarith
  have e₁ := eqOn_chart hζc hchart (hγ.mono hsub) hγU (h₁.continuousOn.mono hsub)
    (fun s hs => h₁.zero s (hsub hs)) (mem_ball_self hρ)
  have e₂ := eqOn_chart hζc hchart (hγ.mono hsub) hγU (h₂.continuousOn.mono hsub)
    (fun s hs => h₂.zero s (hsub hs))
    (by rw [← show z₁ x = z₂ x from hxeq]; exact mem_ball_self hρ)
  refine mem_of_superset (Ioc_mem_nhdsGT hxc) fun s hs => ?_
  have hs' : s ∈ Icc x (min b (x + ε / 2)) := ⟨hs.1.le, hs.2⟩
  exact (e₁ s hs').trans (e₂ s hs').symm

private theorem mapsTo_reverse (b : ℝ) : MapsTo (fun s : ℝ => b - s) (Icc 0 b) (Icc 0 b) :=
  fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩

/-- The reversed lift is a lift of the reversed path. -/
theorem IsZeroLift.reverse {b : ℝ} {z : ℝ → ℂ} (h : IsZeroLift γ b z) :
    IsZeroLift (fun s => γ (b - s)) b fun s => z (b - s) :=
  ⟨h.continuousOn.comp (continuous_const.sub continuous_id).continuousOn (mapsTo_reverse b),
    fun s hs => h.zero (b - s) (mapsTo_reverse b hs)⟩

/-- **Lifts that meet agree from the start.** Two lifts along a path that avoids the branch times
and that take the same value at one parameter start at the same zero. -/
theorem IsZeroLift.eq_zero_of_eq {b s₁ : ℝ} {z₁ z₂ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 b))
    (hsimple : ∀ s ∈ Icc (0 : ℝ) b, γ s ∉ branchTimes)
    (h₁ : IsZeroLift γ b z₁) (h₂ : IsZeroLift γ b z₂) (hs₁ : s₁ ∈ Icc (0 : ℝ) b)
    (h : z₁ s₁ = z₂ s₁) : z₁ 0 = z₂ 0 := by
  have hsub : Icc (0 : ℝ) s₁ ⊆ Icc 0 b := Icc_subset_Icc_right hs₁.2
  have hγr : ContinuousOn (fun s => γ (s₁ - s)) (Icc 0 s₁) :=
    (hγ.mono hsub).comp (continuous_const.sub continuous_id).continuousOn (mapsTo_reverse s₁)
  have he := IsZeroLift.eqOn hγr (h₁.mono hs₁.2).reverse (h₂.mono hs₁.2).reverse
    (by simpa using h)
    (fun s hs => deriv_complexHeat_ne_zero_of_not_mem_branchTimes
      (hsimple _ (hsub (mapsTo_reverse s₁ hs))) (h₁.zero (s₁ - s) (hsub (mapsTo_reverse s₁ hs))))
    (show s₁ ∈ Icc (0 : ℝ) s₁ from ⟨hs₁.1, le_rfl⟩)
  simpa using he

/-- **Transport is injective.** Two lifts along a path that avoids the branch times and that end
at the same zero start at the same zero. -/
theorem IsZeroLift.eq_zero_of_eq_one {z₁ z₂ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1))
    (hsimple : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∉ branchTimes)
    (h₁ : IsZeroLift γ 1 z₁) (h₂ : IsZeroLift γ 1 z₂) (h1 : z₁ 1 = z₂ 1) : z₁ 0 = z₂ 0 :=
  h₁.eq_zero_of_eq hγ hsimple h₂ ⟨zero_le_one, le_rfl⟩ h1

/-- A lift through a simple zero extends beyond its endpoint. -/
theorem IsZeroLift.exists_extension {b : ℝ} {z : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1))
    (hb0 : 0 ≤ b) (hb1 : b < 1) (h : IsZeroLift γ b z)
    (hsimple : deriv (complexHeat (γ b)) (z b) ≠ 0) :
    ∃ b' ∈ Ioc b 1, ∃ z', IsZeroLift γ b' z' ∧ z' 0 = z 0 := by
  have hbI : b ∈ Icc (0 : ℝ) b := ⟨hb0, le_rfl⟩
  obtain ⟨δ, hδ, ρ, hρ, ζ, hζc, hζb, hchart⟩ := exists_zero_chart (h.zero b hbI) hsimple
  obtain ⟨ε, hε, hεball⟩ := Metric.continuousWithinAt_iff.1 (hγ b ⟨hb0, hb1.le⟩) δ hδ
  have hbc : b < min 1 (b + ε / 2) := lt_min hb1 (by linarith)
  have hc1 : min 1 (b + ε / 2) ≤ 1 := min_le_left _ _
  have hγU : ∀ s ∈ Icc b (min 1 (b + ε / 2)), γ s ∈ ball (γ b) δ := fun s hs => by
    refine hεball ⟨hb0.trans hs.1, hs.2.trans hc1⟩ ?_
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hs.1)]
    have := hs.2.trans (min_le_right 1 (b + ε / 2))
    linarith
  have hζγ : ContinuousOn (fun s => ζ (γ s)) (Icc b (min 1 (b + ε / 2))) :=
    hζc.comp (hγ.mono fun s hs => ⟨hb0.trans hs.1, hs.2.trans hc1⟩) hγU
  refine ⟨min 1 (b + ε / 2), ⟨hbc, hc1⟩, fun s => if s ≤ b then z s else ζ (γ s),
    ⟨continuousOn_glue hb0 hbc.le h.continuousOn hζγ hζb.symm, fun s hs => ?_⟩, ?_⟩
  · show complexHeat (γ s) (if s ≤ b then z s else ζ (γ s)) = 0
    by_cases hsb : s ≤ b
    · rw [if_pos hsb]
      exact h.zero s ⟨hs.1, hsb⟩
    · rw [if_neg hsb]
      exact (hchart (γ s) (hγU s ⟨(not_le.1 hsb).le, hs.2⟩)).2.1
  · show (if (0 : ℝ) ≤ b then z 0 else ζ (γ 0)) = z 0
    rw [if_pos hb0]

/-! ## The alternative -/

/-- The zero `z₀` of `H_{γ(0)}` escapes along `γ`: it continues as a continuous family of zeros on
a half-open interval `[0, b)`, `b ≤ 1`, and the modulus of the family tends to infinity at `b`. -/
def EscapesAlong (γ : ℝ → ℂ) (z₀ : ℂ) : Prop :=
  ∃ b ∈ Ioc (0 : ℝ) 1, ∃ z : ℝ → ℂ, ContinuousOn z (Ico 0 b) ∧ z 0 = z₀ ∧
    (∀ s ∈ Ico (0 : ℝ) b, complexHeat (γ s) (z s) = 0) ∧
    Tendsto (fun s => ‖z s‖) (𝓝[<] b) atTop

/-- **A zero that lifts does not escape.** Along a path that avoids the branch times the two cases
of the alternative exclude each other. -/
theorem IsZeroLift.not_escapesAlong {z : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1))
    (hsimple : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∉ branchTimes) (h : IsZeroLift γ 1 z) :
    ¬ EscapesAlong γ (z 0) := by
  rintro ⟨b, hb, w, hwc, hw0, hwz, htend⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn h.continuousOn
  have hIco : ∀ᶠ s in 𝓝[<] b, s ∈ Ico (0 : ℝ) b := Ico_mem_nhdsLT hb.1
  obtain ⟨s, hsM, hsI⟩ := ((htend.eventually_ge_atTop (M + 1)).and hIco).exists
  have hs1 : s ≤ 1 := hsI.2.le.trans hb.2
  have hw : IsZeroLift γ s w :=
    ⟨hwc.mono fun x hx => ⟨hx.1, hx.2.trans_lt hsI.2⟩,
      fun x hx => hwz x ⟨hx.1, hx.2.trans_lt hsI.2⟩⟩
  have he := IsZeroLift.eqOn (hγ.mono (Icc_subset_Icc_right hs1)) (h.mono hs1) hw hw0.symm
    (fun x hx => deriv_complexHeat_ne_zero_of_not_mem_branchTimes
      (hsimple x ⟨hx.1, hx.2.trans hs1⟩) (h.zero x ⟨hx.1, hx.2.trans hs1⟩))
    (show s ∈ Icc (0 : ℝ) s from ⟨hsI.1, le_rfl⟩)
  have := hM s ⟨hsI.1, hs1⟩
  rw [he] at this
  linarith

/-- **A zero continues along a path of times until it escapes: the relative form.** Let `K` be
a closed set of places such that the zeros of the family along `γ` that lie in `K` are simple and
every continuous family of zeros that starts at `z₀` stays in `K`. Either `z₀` lifts along the
whole path, or it lifts on a half-open interval `[0, b)` and the modulus of the lift tends to
infinity at `b`. The path may cross branch times. -/
theorem exists_isZeroLift_or_escape_of_mem (hγ : ContinuousOn γ (Icc 0 1)) {K : Set ℂ}
    (hK : IsClosed K)
    (hsimple : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ K, complexHeat (γ s) z = 0 →
      deriv (complexHeat (γ s)) z ≠ 0) {z₀ : ℂ}
    (hstay : ∀ b ∈ Icc (0 : ℝ) 1, ∀ z, IsZeroLift γ b z → z 0 = z₀ →
      ∀ s ∈ Icc (0 : ℝ) b, z s ∈ K)
    (h0 : complexHeat (γ 0) z₀ = 0) :
    (∃ z, IsZeroLift γ 1 z ∧ z 0 = z₀) ∨ EscapesAlong γ z₀ := by
  by_cases h1 : ∃ z, IsZeroLift γ 1 z ∧ z 0 = z₀
  · exact Or.inl h1
  right
  -- the parameters up to which the zero lifts
  obtain ⟨S, hSdef⟩ : ∃ S : Set ℝ, ∀ b, b ∈ S ↔
      (b ∈ Icc (0 : ℝ) 1 ∧ ∃ z, IsZeroLift γ b z ∧ z 0 = z₀) :=
    ⟨{b | b ∈ Icc (0 : ℝ) 1 ∧ ∃ z, IsZeroLift γ b z ∧ z 0 = z₀}, fun b => Iff.rfl⟩
  have hS0 : (0 : ℝ) ∈ S := (hSdef 0).2 ⟨⟨le_rfl, zero_le_one⟩, fun _ => z₀,
    ⟨continuousOn_const, fun s hs => by
      obtain rfl : s = 0 := le_antisymm hs.2 hs.1
      exact h0⟩, rfl⟩
  have hSbdd : BddAbove S := ⟨1, fun b hb => ((hSdef b).1 hb).1.2⟩
  have hb01 : sSup S ∈ Icc (0 : ℝ) 1 :=
    ⟨le_csSup hSbdd hS0, csSup_le ⟨0, hS0⟩ fun x hx => ((hSdef x).1 hx).1.2⟩
  have hsim : ∀ {b₁ : ℝ} {z : ℝ → ℂ}, 0 ≤ b₁ → b₁ ≤ 1 → IsZeroLift γ b₁ z → z 0 = z₀ →
      ∀ s ∈ Icc (0 : ℝ) b₁, deriv (complexHeat (γ s)) (z s) ≠ 0 := fun hb₀ hb₁ hz hz0 s hs =>
    hsimple s ⟨hs.1, hs.2.trans hb₁⟩ _ (hstay _ ⟨hb₀, hb₁⟩ _ hz hz0 s hs) (hz.zero s hs)
  -- the supremum is not attained
  have hbS : sSup S ∉ S := by
    intro hbS
    obtain ⟨-, z, hz, hz0⟩ := (hSdef _).1 hbS
    rcases eq_or_lt_of_le hb01.2 with hb1 | hb1
    · exact h1 ⟨z, hb1 ▸ hz, hz0⟩
    · obtain ⟨b', hb', z', hz', hz'0⟩ := hz.exists_extension hγ hb01.1 hb1
        (hsim hb01.1 hb01.2 hz hz0 _ ⟨hb01.1, le_rfl⟩)
      have hb'S : b' ∈ S := (hSdef b').2
        ⟨⟨hb01.1.trans hb'.1.le, hb'.2⟩, z', hz', hz'0.trans hz0⟩
      exact absurd (le_csSup hSbdd hb'S) (not_le.2 hb'.1)
  have hbpos : 0 < sSup S := lt_of_le_of_ne hb01.1 fun h => hbS (h ▸ hS0)
  -- every earlier parameter carries a lift
  have hlt : ∀ s, 0 ≤ s → s < sSup S → ∃ z, IsZeroLift γ s z ∧ z 0 = z₀ := by
    intro s hs0 hsb
    obtain ⟨b₁, hb₁, hsb₁⟩ := exists_lt_of_lt_csSup ⟨0, hS0⟩ hsb
    obtain ⟨-, z, hz, hz0⟩ := (hSdef b₁).1 hb₁
    exact ⟨z, hz.mono hsb₁.le, hz0⟩
  -- the lifts glue to one lift on `[0, sup S)`
  classical
  let Z : ℝ → ℂ := fun s => if h : 0 ≤ s ∧ s < sSup S then (hlt s h.1 h.2).choose s else z₀
  have hZ : ∀ {b₁ : ℝ} {w : ℝ → ℂ}, b₁ < sSup S → IsZeroLift γ b₁ w → w 0 = z₀ →
      EqOn Z w (Icc 0 b₁) := by
    intro b₁ w hb₁ hw hw0 s hs
    have hsb : 0 ≤ s ∧ s < sSup S := ⟨hs.1, hs.2.trans_lt hb₁⟩
    obtain ⟨hc, hc0⟩ := (hlt s hsb.1 hsb.2).choose_spec
    have hs1 : s ≤ 1 := hsb.2.le.trans hb01.2
    have hZs : Z s = (hlt s hsb.1 hsb.2).choose s := dif_pos hsb
    rw [hZs]
    exact IsZeroLift.eqOn (hγ.mono (Icc_subset_Icc_right hs1)) hc (hw.mono hs.2)
      (hc0.trans hw0.symm) (hsim hs.1 hs1 hc hc0) ⟨hs.1, le_rfl⟩
  have hZc : ContinuousOn Z (Ico 0 (sSup S)) := by
    intro s hs
    obtain ⟨b₁, hsb₁, hb₁b⟩ := exists_between hs.2
    obtain ⟨w, hw, hw0⟩ := hlt b₁ (hs.1.trans hsb₁.le) hb₁b
    have hcw : ContinuousWithinAt Z (Icc 0 b₁) s :=
      (hw.continuousOn s ⟨hs.1, hsb₁.le⟩).congr (fun x hx => hZ hb₁b hw hw0 hx)
        (hZ hb₁b hw hw0 ⟨hs.1, hsb₁.le⟩)
    exact hcw.mono_of_mem_nhdsWithin (mem_of_superset
      (inter_mem_nhdsWithin _ (Iio_mem_nhds hsb₁)) fun x hx => ⟨hx.1.1, hx.2.le⟩)
  have hZ0 : Z 0 = z₀ := by
    obtain ⟨w, hw, hw0⟩ := hlt 0 le_rfl hbpos
    exact (hZ hbpos hw hw0 ⟨le_rfl, le_rfl⟩).trans hw0
  have hZzero : ∀ s ∈ Ico (0 : ℝ) (sSup S), complexHeat (γ s) (Z s) = 0 := by
    intro s hs
    obtain ⟨w, hw, hw0⟩ := hlt s hs.1 hs.2
    rw [hZ hs.2 hw hw0 ⟨hs.1, le_rfl⟩]
    exact hw.zero s ⟨hs.1, le_rfl⟩
  refine ⟨sSup S, ⟨hbpos, hb01.2⟩, Z, hZc, hZ0, hZzero, ?_⟩
  -- a lift that does not escape has a cluster point, a simple zero, and enters its chart
  by_contra hne
  rw [Filter.tendsto_atTop] at hne
  obtain ⟨M, hM⟩ := not_forall.1 hne
  have hfreq : ∃ᶠ s in 𝓝[<] sSup S, Z s ∈ closedBall (0 : ℂ) M :=
    (not_eventually.1 hM).mono fun s hs => mem_closedBall_zero_iff.2 (not_le.1 hs).le
  obtain ⟨zs, -, hcl⟩ := (isCompact_closedBall (0 : ℂ) M).exists_mapClusterPt_of_frequently hfreq
  rw [mapClusterPt_iff_frequently] at hcl
  have hIco : ∀ᶠ s in 𝓝[<] sSup S, s ∈ Ico (0 : ℝ) (sSup S) := Ico_mem_nhdsLT hbpos
  have hγb : Tendsto γ (𝓝[<] sSup S) (𝓝 (γ (sSup S))) :=
    (hγ _ hb01).tendsto.mono_left (nhdsWithin_le_of_mem
      (mem_of_superset (Ico_mem_nhdsLT hbpos) fun s hs => ⟨hs.1, hs.2.le.trans hb01.2⟩))
  have hzs : complexHeat (γ (sSup S)) zs = 0 := by
    by_contra hzs
    have hne' : ∀ᶠ p in 𝓝 (γ (sSup S), zs), complexHeat p.1 p.2 ≠ 0 :=
      continuous_complexHeat.continuousAt.eventually_ne hzs
    rw [nhds_prod_eq] at hne'
    obtain ⟨pa, hpa, pb, hpb, hprod⟩ := eventually_prod_iff.1 hne'
    obtain ⟨s, hsb, hsa, hsI⟩ :=
      ((hcl _ hpb).and_eventually ((hγb.eventually hpa).and hIco)).exists
    exact hprod hsa hsb (hZzero s hsI)
  -- the cluster point lies in `K`, since the lift stays there
  have hzsK : zs ∈ K := by
    by_contra hnot
    obtain ⟨s, hsK, hsI⟩ := ((hcl _ (hK.isOpen_compl.mem_nhds hnot)).and_eventually hIco).exists
    obtain ⟨w, hw, hw0⟩ := hlt s hsI.1 hsI.2
    have hws := hstay s ⟨hsI.1, hsI.2.le.trans hb01.2⟩ w hw hw0 s ⟨hsI.1, le_rfl⟩
    rw [← hZ hsI.2 hw hw0 ⟨hsI.1, le_rfl⟩] at hws
    exact hsK hws
  obtain ⟨δ, hδ, ρ, hρ, ζ, hζc, -, hchart⟩ := exists_zero_chart hzs
    (hsimple _ hb01 zs hzsK hzs)
  obtain ⟨ε, hε, hεball⟩ := Metric.continuousWithinAt_iff.1 (hγ _ hb01) δ hδ
  have hIoo : ∀ᶠ s in 𝓝[<] sSup S, s ∈ Ioo (max 0 (sSup S - ε)) (sSup S) :=
    Ioo_mem_nhdsLT (max_lt hbpos (by linarith))
  obtain ⟨s₁, hs₁V, hs₁I⟩ := ((hcl _ (ball_mem_nhds zs hρ)).and_eventually hIoo).exists
  have hs₁0 : 0 < s₁ := lt_of_le_of_lt (le_max_left _ _) hs₁I.1
  have hs₁ε : sSup S - ε < s₁ := lt_of_le_of_lt (le_max_right _ _) hs₁I.1
  have hγU : ∀ s ∈ Icc s₁ (sSup S), γ s ∈ ball (γ (sSup S)) δ := fun s hs => by
    refine hεball ⟨hs₁0.le.trans hs.1, hs.2.trans hb01.2⟩ ?_
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hs.2)]
    linarith [hs.1]
  have hfollow : ∀ s ∈ Ico s₁ (sSup S), Z s = ζ (γ s) := fun s hs => by
    have hsub : Icc s₁ s ⊆ Ico (0 : ℝ) (sSup S) := fun x hx =>
      ⟨hs₁0.le.trans hx.1, hx.2.trans_lt hs.2⟩
    exact eqOn_chart hζc hchart
      (hγ.mono fun x hx => ⟨(hsub hx).1, (hsub hx).2.le.trans hb01.2⟩)
      (fun x hx => hγU x (Icc_subset_Icc_right hs.2.le hx)) (hZc.mono hsub)
      (fun x hx => hZzero x (hsub hx)) hs₁V s ⟨hs.1, le_rfl⟩
  have hlift : IsZeroLift γ (sSup S) fun s => if s ≤ s₁ then Z s else ζ (γ s) := by
    refine ⟨continuousOn_glue hs₁0.le hs₁I.2.le
      (hZc.mono fun x hx => ⟨hx.1, hx.2.trans_lt hs₁I.2⟩)
      (hζc.comp (hγ.mono fun x hx => ⟨hs₁0.le.trans hx.1, hx.2.trans hb01.2⟩) hγU)
      (hfollow s₁ ⟨le_rfl, hs₁I.2⟩), fun s hs => ?_⟩
    show complexHeat (γ s) (if s ≤ s₁ then Z s else ζ (γ s)) = 0
    by_cases hss : s ≤ s₁
    · rw [if_pos hss]
      exact hZzero s ⟨hs.1, hss.trans_lt hs₁I.2⟩
    · rw [if_neg hss]
      exact (hchart (γ s) (hγU s ⟨(not_le.1 hss).le, hs.2⟩)).2.1
  refine hbS ((hSdef _).2 ⟨hb01, _, hlift, ?_⟩)
  show (if (0 : ℝ) ≤ s₁ then Z 0 else ζ (γ 0)) = z₀
  rw [if_pos hs₁0.le, hZ0]

/-- **A zero continues along a path of times until it escapes.** Let `γ` be a path of times that
avoids the branch times and `z₀` a zero of `H_{γ(0)}`. Either `z₀` lifts along the whole path, or
it lifts on a half-open interval `[0, b)` and the modulus of the lift tends to infinity at `b`. -/
theorem exists_isZeroLift_or_escape (hγ : ContinuousOn γ (Icc 0 1))
    (hsimple : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∉ branchTimes) {z₀ : ℂ}
    (h0 : complexHeat (γ 0) z₀ = 0) :
    (∃ z, IsZeroLift γ 1 z ∧ z 0 = z₀) ∨ EscapesAlong γ z₀ :=
  exists_isZeroLift_or_escape_of_mem hγ isClosed_univ
    (fun s hs _ _ hz => deriv_complexHeat_ne_zero_of_not_mem_branchTimes (hsimple s hs) hz)
    (fun _ _ _ _ _ _ _ => mem_univ _) h0

end

end GaloisForLFunctions.GaloisTheoryOfZeros
