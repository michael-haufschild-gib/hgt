/-
# The hole-free-tip interface and its discharge from a collar (OP4, answered)

The single named datum the both-connected pair chain consumes (open problem 04, ANSWERED in
`docs/open-problems/04-answer.md` for the class `−3/4 < c₂ < c₁ < 0`): a Julia point `z₀` of
`K_{c₁}` with a `K_{c₂}`-free ball on which **every** basin point reaches `∞` inside
`ℂ ∖ (K₁ ∪ K₂)` — the W-approach form, which avoids formalizing "holes" altogether.

This file (i) defines the Prop `HoleFreeTip`; (ii) proves the **imaginary escape ray** above the
tip is an unbounded preconnected subset of the joint complement; (iii) discharges `HoleFreeTip`
at `imagTip c₁` from ONE remaining input, the Schoenflies exterior collar of the 04-answer
(`U ∖ K₁` preconnected at arbitrarily small scales) — carried as an explicit hypothesis until the
collar epic lands; (iv) provides the frontier-approach consumer the pigeonhole chain reads.
Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.ImaginaryAxisTip

open Set Metric Bornology Filter Topology

namespace Bottcher

/-- **The hole-free-tip datum** (open problem 04, W-approach form): `z₀` is a Julia point of
`K_{c₁}`, the `r`-ball at `z₀` misses `K_{c₂}`, and every basin point of the ball lies in an
unbounded preconnected subset of `ℂ ∖ (K₁ ∪ K₂)` — hence in the unbounded component `W`, so no
hole of the union meets the ball. -/
def HoleFreeTip (c₁ c₂ z₀ : ℂ) (r : ℝ) : Prop :=
  0 < r ∧ z₀ ∈ frontier (filledJulia c₁) ∧
  Metric.ball z₀ r ∩ filledJulia c₂ = ∅ ∧
  ∀ q ∈ Metric.ball z₀ r, q ∉ filledJulia c₁ →
    ∃ V : Set ℂ, q ∈ V ∧ IsPreconnected V ∧ ¬ IsBounded V ∧
      V ⊆ (filledJulia c₁ ∪ filledJulia c₂)ᶜ

/-- The imaginary escape ray `{iy : y ≥ y₀}` above the tip height. -/
def imagRay (y₀ : ℝ) : Set ℂ := (fun y : ℝ => (y : ℂ) * Complex.I) '' Set.Ici y₀

theorem imagRay_preconnected (y₀ : ℝ) : IsPreconnected (imagRay y₀) :=
  isPreconnected_Ici.image _ (by fun_prop : Continuous fun y : ℝ => (y : ℂ) * Complex.I).continuousOn

theorem imagRay_not_isBounded (y₀ : ℝ) : ¬ IsBounded (imagRay y₀) := by
  intro hbd
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbd
  set y : ℝ := max y₀ (C + 1) with hydef
  have hy : ((y : ℂ) * Complex.I) ∈ imagRay y₀ := ⟨y, Set.mem_Ici.mpr (le_max_left _ _), rfl⟩
  have h1 := hC _ hy
  rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one] at h1
  have h2 : C + 1 ≤ y := le_max_right _ _
  have h3 : y ≤ |y| := le_abs_self y
  linarith

/-- **The ray escapes both filled Julia sets**: for a real pair `c₂ < c₁ ≤ 0` and any height
`y₀ > t₁`, the ray `{iy : y ≥ y₀}` lies in the joint complement. -/
theorem imagRay_subset_pair_compl {c₁ c₂ : ℝ} (h2 : -2 ≤ c₂) (hlt : c₂ < c₁) (h1 : c₁ ≤ 0)
    {y₀ : ℝ} (hy₀ : tipHeight c₁ < y₀) :
    imagRay y₀ ⊆ (filledJulia (c₁ : ℂ) ∪ filledJulia (c₂ : ℂ))ᶜ := by
  rintro _ ⟨y, hy, rfl⟩ hmem
  have hyt : tipHeight c₁ < y := lt_of_lt_of_le hy₀ hy
  have hynn : 0 ≤ y := le_trans (tipHeight_nonneg c₁) hyt.le
  rcases hmem with hmem | hmem
  · rw [imag_mem_filledJulia_iff (by linarith) (by linarith), abs_of_nonneg hynn] at hmem
    linarith
  · rw [imag_mem_filledJulia_iff h2 (by linarith), abs_of_nonneg hynn] at hmem
    have := tipHeight_lt h2 hlt h1
    linarith

/-- **`HoleFreeTip` from the Schoenflies collar** (the 04-answer, formalized modulo its one
topological input).  Given the exterior collar — arbitrarily small open `U ∋ imagTip c₁` with
`U ∖ K₁` preconnected (from `J₁` Jordan + Schoenflies on paper; the collar epic in Lean) — the
tip package `exists_real_pair_tip` upgrades to the full hole-free-tip datum: every basin point of
a small ball joins the collar, crosses to the near-tip ray anchor, and escapes to `∞` along the
imaginary ray. -/
theorem holeFreeTip_of_collar {c₁ c₂ : ℝ} (h2 : -2 ≤ c₂) (hlt : c₂ < c₁) (h1 : c₁ ≤ 0)
    (hcollar : ∀ ρ > 0, ∃ U : Set ℂ, IsOpen U ∧ imagTip c₁ ∈ U ∧
      U ⊆ Metric.ball (imagTip c₁) ρ ∧ IsPreconnected (U \ filledJulia (c₁ : ℂ))) :
    ∃ r : ℝ, HoleFreeTip (c₁ : ℂ) (c₂ : ℂ) (imagTip c₁) r := by
  obtain ⟨d, hd, hfront, _hnot, hdisj⟩ := exists_real_pair_tip h2 hlt h1
  obtain ⟨U, hUo, hUmem, hUsub, hUconn⟩ := hcollar d hd
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hUo _ hUmem
  -- the ray anchor just above the tip, inside the r-ball
  set ε : ℝ := min (r / 2) 1 with hεdef
  have hε : 0 < ε := lt_min (by linarith) one_pos
  set p : ℂ := ((tipHeight c₁ + ε : ℝ) : ℂ) * Complex.I with hpdef
  have hpball : p ∈ Metric.ball (imagTip c₁) r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hcalc : p - imagTip c₁ = ((ε : ℝ) : ℂ) * Complex.I := by
      rw [hpdef, imagTip]
      push_cast
      ring
    rw [hcalc, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one,
      abs_of_pos hε]
    calc ε ≤ r / 2 := min_le_left _ _
      _ < r := by linarith
  have hpK₁ : p ∉ filledJulia (c₁ : ℂ) := by
    rw [hpdef, imag_mem_filledJulia_iff (by linarith) (by linarith),
      abs_of_nonneg (by linarith [tipHeight_nonneg c₁])]
    linarith
  have hpU : p ∈ U \ filledJulia (c₁ : ℂ) := ⟨hrU hpball, hpK₁⟩
  have hpray : p ∈ imagRay (tipHeight c₁ + ε) := ⟨tipHeight c₁ + ε, Set.mem_Ici.mpr (le_refl _), rfl⟩
  -- the collar avoids K₂ outright (it sits inside the d-ball)
  have hUK₂ : ∀ z ∈ U, z ∉ filledJulia (c₂ : ℂ) := by
    intro z hz hzK₂
    have : z ∈ Metric.ball (imagTip c₁) d ∩ filledJulia (c₂ : ℂ) := ⟨hUsub hz, hzK₂⟩
    rw [hdisj] at this
    exact this
  -- the escape carrier: collar ∪ ray
  set V : Set ℂ := (U \ filledJulia (c₁ : ℂ)) ∪ imagRay (tipHeight c₁ + ε) with hVdef
  have hVconn : IsPreconnected V :=
    IsPreconnected.union p hpU hpray hUconn (imagRay_preconnected _)
  have hVunbd : ¬ IsBounded V := by
    intro hbd
    exact imagRay_not_isBounded (tipHeight c₁ + ε) (hbd.subset subset_union_right)
  have hVcompl : V ⊆ (filledJulia (c₁ : ℂ) ∪ filledJulia (c₂ : ℂ))ᶜ := by
    rintro z (⟨hzU, hzK₁⟩ | hzray)
    · rintro (h | h)
      · exact hzK₁ h
      · exact hUK₂ z hzU h
    · exact imagRay_subset_pair_compl h2 hlt h1 (by linarith) hzray
  refine ⟨r, hr, hfront, ?_, ?_⟩
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz1, hz2⟩
    exact hUK₂ z (hrU hz1) hz2
  · intro q hq hqK₁
    exact ⟨V, Or.inl ⟨hrU hq, hqK₁⟩, hVconn, hVunbd, hVcompl⟩

/-- **The frontier-approach consumer**: at a hole-free tip, every Julia point of the ball is
approached, at every scale, by basin points that carry an unbounded preconnected escape set in
the joint complement — the exact supply of relation-carrying approach points for the root-limit
pigeonhole chain. -/
theorem holeFreeTip_frontier_approach {c₁ c₂ z₀ : ℂ} {r : ℝ}
    (h : HoleFreeTip c₁ c₂ z₀ r) {w : ℂ} (hw : w ∈ frontier (filledJulia c₁))
    (hwball : w ∈ Metric.ball z₀ r) :
    ∀ ε > 0, ∃ q, q ∈ Metric.ball w ε ∧ q ∈ Metric.ball z₀ r ∧ q ∉ filledJulia c₁ ∧
      ∃ V : Set ℂ, q ∈ V ∧ IsPreconnected V ∧ ¬ IsBounded V ∧
        V ⊆ (filledJulia c₁ ∪ filledJulia c₂)ᶜ := by
  intro ε hε
  obtain ⟨_, _, _, happ⟩ := h
  have hwcl : w ∈ closure (filledJulia c₁)ᶜ := by
    rw [frontier_eq_closure_inter_closure] at hw
    exact hw.2
  have hopen : IsOpen (Metric.ball w ε ∩ Metric.ball z₀ r) :=
    Metric.isOpen_ball.inter Metric.isOpen_ball
  have hwmem : w ∈ Metric.ball w ε ∩ Metric.ball z₀ r :=
    ⟨Metric.mem_ball_self hε, hwball⟩
  obtain ⟨q, ⟨hq1, hq2⟩, hq3⟩ := mem_closure_iff.mp hwcl _ hopen hwmem
  obtain ⟨V, hV⟩ := happ q hq2 hq3
  exact ⟨q, hq1, hq2, hq3, V, hV⟩

end Bottcher
