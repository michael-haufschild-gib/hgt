/-
# Smooth paths in open connected planar sets, and chains of small sets

* **Smooth paths.**  Any two points of an open preconnected `U ⊆ ℂ` are joined by a `C¹` path
  `γ : ℝ → ℂ` that is constant on `(-∞, 0]` and on `[1, ∞)` and stays in `U`.  Segments are
  reparametrised by the smooth transition function, and two such paths with `γ₁ 1 = γ₂ 0`
  concatenate to `t ↦ γ₁ (2t) + γ₂ (2t - 1) - γ₂ 0`: each summand is constant where the other
  moves, so the sum is the concatenation and is `C¹` with no gluing argument.
* **Chains.**  If a preconnected `Z` is covered by finitely many open sets `Uᵢ` on each of which
  `F` varies by at most `δ`, then `F` varies by at most `(number of sets)·δ` on `Z`.  The sets
  meeting the `kδ`-ball of `F` around a base value grow with `k`; once they stop growing they cover
  `Z` by connectedness, and they can grow at most `(number of sets)` times.
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex

open Set Metric

namespace Bottcher

/-- A `C¹` path from `a` to `b` parametrised by `ℝ`, equal to `a` on `(-∞, 0]` and to `b` on
`[1, ∞)`. -/
structure PlanarPath (a b : ℂ) where
  γ : ℝ → ℂ
  smooth : ContDiff ℝ 1 γ
  left : ∀ t ≤ 0, γ t = a
  right : ∀ t, 1 ≤ t → γ t = b

namespace PlanarPath

theorem apply_zero {a b : ℂ} (p : PlanarPath a b) : p.γ 0 = a := p.left 0 le_rfl

theorem apply_one {a b : ℂ} (p : PlanarPath a b) : p.γ 1 = b := p.right 1 le_rfl

/-- The smoothly reparametrised segment from `a` to `b`. -/
noncomputable def segment (a b : ℂ) : PlanarPath a b where
  γ t := a + Real.smoothTransition t • (b - a)
  smooth := contDiff_const.add (Real.smoothTransition.contDiff.smul contDiff_const)
  left t ht := by simp [Real.smoothTransition.zero_of_nonpos ht]
  right t ht := by simp [Real.smoothTransition.one_of_one_le ht]

theorem segment_mem {a b : ℂ} {s : Set ℂ} (hs : Convex ℝ s) (ha : a ∈ s) (hb : b ∈ s) (t : ℝ) :
    (segment a b).γ t ∈ s :=
  hs.add_smul_sub_mem ha hb ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩

/-- Concatenation of paths. -/
noncomputable def trans {a b d : ℂ} (p : PlanarPath a b) (q : PlanarPath b d) : PlanarPath a d where
  γ t := p.γ (2 * t) + q.γ (2 * t - 1) - q.γ 0
  smooth := by
    have h1 : ContDiff ℝ 1 fun t : ℝ => p.γ (2 * t) :=
      p.smooth.comp (contDiff_const.mul contDiff_id)
    have h2 : ContDiff ℝ 1 fun t : ℝ => q.γ (2 * t - 1) :=
      q.smooth.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
    exact (h1.add h2).sub contDiff_const
  left t ht := by
    rw [p.left (2 * t) (by linarith), q.left (2 * t - 1) (by linarith), q.apply_zero]
    ring
  right t ht := by
    rw [p.right (2 * t) (by linarith), q.right (2 * t - 1) (by linarith), q.apply_zero]
    ring

theorem trans_mem {a b d : ℂ} (p : PlanarPath a b) (q : PlanarPath b d) {s : Set ℂ}
    (hp : ∀ t, p.γ t ∈ s) (hq : ∀ t, q.γ t ∈ s) (t : ℝ) : (p.trans q).γ t ∈ s := by
  change p.γ (2 * t) + q.γ (2 * t - 1) - q.γ 0 ∈ s
  rcases le_total t (1 / 2) with ht | ht
  · rw [q.left (2 * t - 1) (by linarith), q.apply_zero, add_sub_cancel_right]
    exact hp _
  · rw [p.right (2 * t) (by linarith), q.apply_zero, add_sub_cancel_left]
    exact hq _

end PlanarPath

/-- **Open connected planar sets are connected by `C¹` paths.** -/
theorem exists_planarPath_of_isPreconnected {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) : ∃ p : PlanarPath a b, ∀ t, p.γ t ∈ U := by
  set S := {z : ℂ | ∃ p : PlanarPath a z, ∀ t, p.γ t ∈ U} with hSdef
  have hSU : S ⊆ U := fun z ⟨p, hp⟩ => p.apply_one ▸ hp 1
  have hstep : ∀ z ∈ S, ∀ r > 0, ball z r ⊆ U → ball z r ⊆ S := by
    rintro z ⟨p, hp⟩ r hr hrU z' hz'
    refine ⟨p.trans (PlanarPath.segment z z'), PlanarPath.trans_mem _ _ hp fun t => hrU ?_⟩
    exact PlanarPath.segment_mem (convex_ball z r) (mem_ball_self hr) hz' t
  have hSo : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro z hz
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hUo z (hSU hz)
    exact ⟨r, hr, hstep z hz r hr hrU⟩
  have hclosed : ∀ z ∈ U, z ∈ closure S → z ∈ S := by
    intro z hzU hzcl
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hUo z hzU
    obtain ⟨z', hz'S, hz'z⟩ := Metric.mem_closure_iff.mp hzcl r hr
    obtain ⟨p, hp⟩ := hz'S
    have hz'B : z' ∈ ball z r := by rw [mem_ball, dist_comm]; exact hz'z
    refine ⟨p.trans (PlanarPath.segment z' z), PlanarPath.trans_mem _ _ hp fun t => hrU ?_⟩
    exact PlanarPath.segment_mem (convex_ball z r) hz'B (mem_ball_self hr) t
  have haS : a ∈ S := ⟨⟨fun _ => a, contDiff_const, fun _ _ => rfl, fun _ _ => rfl⟩,
    fun _ => ha⟩
  have hsub : U ⊆ S ∪ (closure S)ᶜ := fun z hz => by
    by_cases h : z ∈ closure S
    · exact Or.inl (hclosed z hz h)
    · exact Or.inr h
  have hdisj : Disjoint S (closure S)ᶜ :=
    (disjoint_compl_right (a := closure S)).mono_left subset_closure
  exact hUc.subset_left_of_subset_union hSo isClosed_closure.isOpen_compl hdisj hsub
    ⟨a, ha, haS⟩ hb

/-- **Chains of small sets.**  If a preconnected `Z` is covered by the open sets `U i` (`i ∈ I`) and
`F` varies by at most `δ` on each `U i ∩ Z`, then `F` varies by at most `I.card * δ` on `Z`. -/
theorem dist_le_card_mul_of_cover {ι : Type*} (I : Finset ι) {Z : Set ℂ} (hZ : IsPreconnected Z)
    {U : ι → Set ℂ} (hUo : ∀ i ∈ I, IsOpen (U i)) (hcov : Z ⊆ ⋃ i ∈ I, U i) {F : ℂ → ℂ} {δ : ℝ}
    (hδ : ∀ i ∈ I, ∀ x ∈ U i ∩ Z, ∀ y ∈ U i ∩ Z, dist (F x) (F y) ≤ δ)
    {x y : ℂ} (hx : x ∈ Z) (hy : y ∈ Z) : dist (F x) (F y) ≤ I.card * δ := by
  classical
  obtain ⟨i₀, hi₀I, hxi₀⟩ : ∃ i ∈ I, x ∈ U i := by simpa using hcov hx
  have hδ0 : 0 ≤ δ := by
    have := hδ i₀ hi₀I x ⟨hxi₀, hx⟩ x ⟨hxi₀, hx⟩
    rwa [dist_self] at this
  set B : ℕ → Set ℂ := fun k => {z | z ∈ Z ∧ dist (F x) (F z) ≤ k * δ} with hBdef
  set N : ℕ → Finset ι := fun k => I.filter fun i => (U i ∩ B k).Nonempty with hNdef
  have hBmono : ∀ k, B k ⊆ B (k + 1) := fun k z ⟨hz, hzk⟩ =>
    ⟨hz, hzk.trans (by push_cast; nlinarith)⟩
  have hNmono : ∀ k, N k ⊆ N (k + 1) := by
    intro k i hi
    simp only [hNdef, Finset.mem_filter] at hi ⊢
    obtain ⟨hiI, z, hzU, hzB⟩ := hi
    exact ⟨hiI, z, hzU, hBmono k hzB⟩
  have hgrow : ∀ k, ∀ i ∈ N k, ∀ z ∈ U i ∩ Z, z ∈ B (k + 1) := by
    intro k i hi z hz
    simp only [hNdef, Finset.mem_filter] at hi
    obtain ⟨hiI, w, hwU, hwZ, hwB⟩ := hi
    refine ⟨hz.2, ?_⟩
    calc dist (F x) (F z) ≤ dist (F x) (F w) + dist (F w) (F z) := dist_triangle _ _ _
      _ ≤ k * δ + δ := add_le_add hwB (hδ i hiI w ⟨hwU, hwZ⟩ z hz)
      _ = (k + 1 : ℕ) * δ := by push_cast; ring
  have hi₀N : ∀ k, i₀ ∈ N k := fun k => by
    simp only [hNdef, Finset.mem_filter]
    exact ⟨hi₀I, x, hxi₀, hx, by rw [dist_self]; positivity⟩
  -- once the index sets stop growing, they cover `Z`
  have hstop : ∀ k, N k = N (k + 1) → Z ⊆ B (k + 1) := by
    intro k hk z hz
    set O₁ := ⋃ i ∈ N k, U i
    set O₂ := ⋃ i ∈ I \ N k, U i
    have hO₁ : IsOpen O₁ := isOpen_biUnion fun i hi =>
      hUo i (Finset.mem_filter.mp hi).1
    have hO₂ : IsOpen O₂ := isOpen_biUnion fun i hi => hUo i (Finset.mem_sdiff.mp hi).1
    have hZO : Z ⊆ O₁ ∪ O₂ := by
      intro w hw
      obtain ⟨i, hiI, hwi⟩ : ∃ i ∈ I, w ∈ U i := by simpa using hcov hw
      by_cases hiN : i ∈ N k
      · exact Or.inl (mem_biUnion hiN hwi)
      · exact Or.inr (mem_biUnion (Finset.mem_sdiff.mpr ⟨hiI, hiN⟩) hwi)
    have hZ₂ : ¬ (Z ∩ O₂).Nonempty := by
      intro h₂
      obtain ⟨w, hwZ, hw₁, hw₂⟩ := hZ O₁ O₂ hO₁ hO₂ hZO ⟨x, hx, mem_biUnion (hi₀N k) hxi₀⟩ h₂
      obtain ⟨i, hi, hwi⟩ := mem_iUnion₂.mp hw₁
      obtain ⟨j, hj, hwj⟩ := mem_iUnion₂.mp hw₂
      have hwB := hgrow k i hi w ⟨hwi, hwZ⟩
      have hjN : j ∈ N (k + 1) := by
        simp only [hNdef, Finset.mem_filter]
        exact ⟨(Finset.mem_sdiff.mp hj).1, w, hwj, hwB⟩
      rw [← hk] at hjN
      exact (Finset.mem_sdiff.mp hj).2 hjN
    rcases hZO hz with hz₁ | hz₂
    · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz₁
      exact hgrow k i hi z ⟨hzi, hz⟩
    · exact absurd ⟨z, hz, hz₂⟩ hZ₂
  -- the index sets can grow at most `I.card` times
  obtain ⟨k, hk, hkeq⟩ : ∃ k < I.card, N k = N (k + 1) := by
    by_contra hcon
    push Not at hcon
    have hcard : ∀ k ≤ I.card, k + 1 ≤ (N k).card := by
      intro k
      induction k with
      | zero =>
        intro _
        exact Finset.card_pos.mpr ⟨i₀, hi₀N 0⟩
      | succ k ih =>
        intro hk
        have hlt : (N k).card < (N (k + 1)).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hNmono k, hcon k (by omega)⟩)
        have := ih (by omega)
        omega
    have h1 := hcard I.card le_rfl
    have h2 : (N I.card).card ≤ I.card := Finset.card_le_card (Finset.filter_subset _ _)
    omega
  have hyB := (hstop k hkeq hy).2
  calc dist (F x) (F y) ≤ (k + 1 : ℕ) * δ := hyB
    _ ≤ I.card * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ0
      exact_mod_cast hk

end Bottcher
