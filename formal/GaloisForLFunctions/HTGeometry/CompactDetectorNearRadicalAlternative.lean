import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Compact detector / near-radical alternative

This file isolates the topological engine used by remote-divisor detector no-go theorems.

* pointwise vanishing becomes uniform on a compact parameter family when evaluation is uniformly
  Lipschitz in the parameter;
* a product of two uniformly vanishing complex channels gives the real fourfold quartet defect;
* a continuous strictly positive form has a positive margin on a nonempty compact family;
* a compact detector sequence for a uniformly vanishing defect must approach the radical;
* without a fixed compact carrier, the exact alternative is compact escape or radical approach.

All results are filter-level and require no Xi, divisor, or RH premise.
-/

open Filter Metric
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

/-- Uniform convergence to zero on `K`, expressed without choosing a supremum. -/
def UniformlyVanishesAlong {Y X E : Type*} [Norm E]
    (l : Filter Y) (K : Set X) (F : Y → X → E) : Prop :=
  ∀ ε > 0, ∀ᶠ y in l, ∀ x ∈ K, ‖F y x‖ < ε

/-- **Compact-uniform vanishing.** If every parameter section tends to zero and every evaluation is
`1`-Lipschitz in the parameter, convergence is uniform on each compact parameter set. -/
theorem compact_uniformVanishesAlong_of_lipschitz
    {X Y E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
    {l : Filter Y} {K : Set X} (hK : IsCompact K) (F : X → Y → E)
    (hpoint : ∀ x, Tendsto (F x) l (𝓝 0))
    (hLip : ∀ x y t, ‖F x t - F y t‖ ≤ dist x y) :
    UniformlyVanishesAlong l K (fun t x => F x t) := by
  classical
  intro ε hε
  have hr : 0 < ε / 4 := by positivity
  obtain ⟨s, hscover⟩ := hK.elim_finite_subcover
    (fun x : X => Metric.ball x (ε / 4))
    (fun _ => Metric.isOpen_ball)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, Metric.mem_ball_self hr⟩)
  have hcenter (c : X) : ∀ᶠ t in l, ‖F c t‖ < ε / 2 := by
    have hmem := (hpoint c) (Metric.ball_mem_nhds (0 : E) (by positivity : 0 < ε / 2))
    filter_upwards [hmem] with t ht
    change F c t ∈ Metric.ball (0 : E) (ε / 2) at ht
    simpa only [Metric.mem_ball, dist_zero_right] using ht
  have hsEvent : ∀ᶠ t in l, ∀ c ∈ s, ‖F c t‖ < ε / 2 := by
    exact (Finset.eventually_all s).2 fun c _ => hcenter c
  filter_upwards [hsEvent] with t ht
  intro x hx
  have hxcov := hscover hx
  simp only [Set.mem_iUnion] at hxcov
  obtain ⟨c, hc, hxc⟩ := hxcov
  have hdist : dist x c < ε / 4 := Metric.mem_ball.mp hxc
  calc
    ‖F x t‖ ≤ ‖F x t - F c t‖ + ‖F c t‖ := by
      simpa only [sub_add_cancel] using norm_add_le (F x t - F c t) (F c t)
    _ < ε := by linarith [hLip x c t, ht c hc]

/-- Two uniformly vanishing complex channels make the real fourfold quartet defect vanish
uniformly as well. -/
theorem UniformlyVanishesAlong.quartetDefect
    {Y X : Type*} {l : Filter Y} {K : Set X} {F G : Y → X → ℂ}
    (hF : UniformlyVanishesAlong l K F)
    (hG : UniformlyVanishesAlong l K G) :
    UniformlyVanishesAlong l K
      (fun y x => (4 * ((F y x) * (G y x)).re : ℝ)) := by
  intro ε hε
  have hquarter : 0 < ε / 4 := by positivity
  filter_upwards [hF (ε / 4) hquarter, hG 1 zero_lt_one] with y hyF hyG
  intro x hx
  have hprod : ‖F y x‖ * ‖G y x‖ < ε / 4 := by
    calc
      ‖F y x‖ * ‖G y x‖ ≤ (ε / 4) * ‖G y x‖ :=
        mul_le_mul_of_nonneg_right (le_of_lt (hyF x hx)) (norm_nonneg _)
      _ < (ε / 4) * 1 := mul_lt_mul_of_pos_left (hyG x hx) hquarter
      _ = ε / 4 := mul_one _
  calc
    ‖(4 * ((F y x) * (G y x)).re : ℝ)‖ = 4 * |((F y x) * (G y x)).re| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    _ ≤ 4 * ‖(F y x) * (G y x)‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    _ = 4 * (‖F y x‖ * ‖G y x‖) := by rw [norm_mul]
    _ < ε := by nlinarith

/-- A continuous function strictly positive on a nonempty compact set has a positive uniform
margin there. -/
theorem exists_pos_compactMargin
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (hKne : K.Nonempty) {W : X → ℝ} (hWcont : ContinuousOn W K)
    (hWpos : ∀ x ∈ K, 0 < W x) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, m ≤ W x := by
  obtain ⟨x, hx, hxmin⟩ := hK.exists_isMinOn hKne hWcont
  exact ⟨W x, hWpos x hx, fun y hy => hxmin hy⟩

/-- A compact family separated from the radical remains strictly positive after every sufficiently
remote uniformly vanishing defect. -/
theorem eventually_strictPositive_of_compactMargin
    {X Y : Type*} [TopologicalSpace X] {l : Filter Y} {K : Set X}
    (hK : IsCompact K) (hKne : K.Nonempty)
    {W : X → ℝ} (hWcont : ContinuousOn W K) (hWpos : ∀ x ∈ K, 0 < W x)
    {Δ : Y → X → ℝ} (hΔ : UniformlyVanishesAlong l K Δ) :
    ∀ᶠ y in l, ∀ x ∈ K, 0 < W x + Δ y x := by
  obtain ⟨m, hm, hmW⟩ := exists_pos_compactMargin hK hKne hWcont hWpos
  filter_upwards [hΔ m hm] with y hy
  intro x hx
  have habs := hy x hx
  have hneg : -m < Δ y x := neg_lt_of_abs_lt habs
  linarith [hmW x hx]

/-- **Near-radical law.** A detecting sequence constrained to one compact family has background
energy tending to zero whenever the remote defect vanishes uniformly on that family. -/
theorem tendsto_nearRadical_of_detecting
    {X Y Z : Type*} [TopologicalSpace X] [PseudoMetricSpace Z]
    {l : Filter Y} {lz : Filter Z} {K : Set X}
    {W : X → ℝ} (hWnonneg : ∀ x ∈ K, 0 ≤ W x)
    {Δ : Y → X → ℝ} (hΔ : UniformlyVanishesAlong l K Δ)
    {t : Z → Y} (ht : Tendsto t lz l) {x : Z → X}
    (hxK : ∀ᶠ z in lz, x z ∈ K)
    (hdetect : ∀ᶠ z in lz, W (x z) + Δ (t z) (x z) ≤ 0) :
    Tendsto (fun z => W (x z)) lz (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsmall := ht.eventually (hΔ ε hε)
  filter_upwards [hsmall, hxK, hdetect] with z hz hx hzdet
  have hnonneg := hWnonneg (x z) hx
  have hupper : W (x z) ≤ |Δ (t z) (x z)| := by
    calc
      W (x z) ≤ -Δ (t z) (x z) := by linarith
      _ ≤ |Δ (t z) (x z)| := neg_le_abs _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact lt_of_le_of_lt hupper (hz (x z) hx)

/-- **Compact escape / near-radical alternative.** For a defect vanishing uniformly on every compact
set, every detecting sequence either is not eventually contained in any compact set, or its
background energy tends to zero. -/
theorem compactEscape_or_tendsto_nearRadical
    {X Y Z : Type*} [TopologicalSpace X] [PseudoMetricSpace Z]
    {l : Filter Y} {lz : Filter Z} {W : X → ℝ}
    (hWnonneg : ∀ x, 0 ≤ W x) {Δ : Y → X → ℝ}
    (hΔ : ∀ K : Set X, IsCompact K → UniformlyVanishesAlong l K Δ)
    {t : Z → Y} (ht : Tendsto t lz l) {x : Z → X}
    (hdetect : ∀ᶠ z in lz, W (x z) + Δ (t z) (x z) ≤ 0) :
    (∀ K : Set X, IsCompact K → ¬ ∀ᶠ z in lz, x z ∈ K) ∨
      Tendsto (fun z => W (x z)) lz (𝓝 0) := by
  classical
  by_cases hescape : ∀ K : Set X, IsCompact K → ¬ ∀ᶠ z in lz, x z ∈ K
  · exact Or.inl hescape
  · right
    push Not at hescape
    obtain ⟨K, hK, hxK⟩ := hescape
    exact tendsto_nearRadical_of_detecting
      (fun y _ => hWnonneg y) (hΔ K hK) ht hxK hdetect

end GaloisForLFunctions.HTGeometry
