import GaloisForLFunctions.HTGeometry.BohrAlmostPeriodic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Bohr's criterion and Bochner's criterion agree

A continuous function on `ℝ` is *Bohr* almost periodic when its `ε`-almost periods are relatively
dense, and *Bochner* almost periodic when its translation orbit is relatively compact for the uniform
metric.  Mathlib has neither notion; this file proves that the two agree, in an elementary form that
avoids bundling the orbit into a function space:

`HasTotallyBoundedOrbit f` says that for every `ε` finitely many sample times approximate every
translate uniformly to within `ε`.  In a complete function space that is exactly relative
compactness of the orbit.

Both directions are needed downstream.  Bochner's form is what makes almost periodicity stable under
pairing — two functions acquire *common* almost periods — and Bohr's form is what the mean-value and
block arguments consume.  Along the way the file proves that a continuous almost-periodic function is
uniformly continuous, which is the ingredient that turns a compact parameter interval into a finite
sample set.
-/

open Filter Topology Metric

namespace GaloisForLFunctions

open HTGeometry

variable {E : Type*} [NormedAddCommGroup E]

/-- **Uniform continuity from almost periodicity.**  A continuous Bohr almost-periodic function is
uniformly continuous: every point can be transported by an almost period into the fixed compact
window `[-1, L+1]`, on which continuity is already uniform. -/
theorem exists_delta_of_isBohrAlmostPeriodic {f : ℝ → E} (hcont : Continuous f)
    (hap : IsBohrAlmostPeriodic f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : ℝ, |x - y| < δ → ‖f x - f y‖ ≤ ε := by
  obtain ⟨L, hL, hdense⟩ := hap (ε / 3) (by linarith)
  have hK : IsCompact (Set.Icc (-1 : ℝ) (L + 1)) := isCompact_Icc
  obtain ⟨δ₀, hδ₀, hunif⟩ :=
    (Metric.uniformContinuousOn_iff.mp
      (IsCompact.uniformContinuousOn_of_continuous hK hcont.continuousOn)) (ε / 3) (by linarith)
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, fun x y hxy => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hdense (-x)
  have hxτ : x + τ ∈ Set.Icc (-1 : ℝ) (L + 1) := by
    constructor
    · linarith [hτmem.1]
    · linarith [hτmem.2]
  have hlt1 : |x - y| < 1 := lt_of_lt_of_le hxy (min_le_right _ _)
  have habs : -1 < x - y ∧ x - y < 1 := abs_lt.mp hlt1
  have hyτ : y + τ ∈ Set.Icc (-1 : ℝ) (L + 1) := by
    constructor
    · linarith [hτmem.1, habs.2]
    · linarith [hτmem.2, habs.1]
  have hdist : dist (x + τ) (y + τ) < δ₀ := by
    rw [Real.dist_eq]
    have : |x + τ - (y + τ)| = |x - y| := by congr 1; ring
    rw [this]
    exact lt_of_lt_of_le hxy (min_le_left _ _)
  have hmid : ‖f (x + τ) - f (y + τ)‖ ≤ ε / 3 := by
    have := hunif _ hxτ _ hyτ hdist
    rw [dist_eq_norm] at this
    exact this.le
  have hx : ‖f x - f (x + τ)‖ ≤ ε / 3 := by
    rw [← norm_neg]
    simpa using hτ x
  have hy : ‖f (y + τ) - f y‖ ≤ ε / 3 := hτ y
  calc ‖f x - f y‖
      = ‖(f x - f (x + τ)) + (f (x + τ) - f (y + τ)) + (f (y + τ) - f y)‖ := by congr 1; abel
    _ ≤ ‖f x - f (x + τ)‖ + ‖f (x + τ) - f (y + τ)‖ + ‖f (y + τ) - f y‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ ε / 3 + ε / 3 + ε / 3 := add_le_add (add_le_add hx hmid) hy
    _ = ε := by ring

/-- A continuous Bohr almost-periodic function is uniformly continuous. -/
theorem uniformContinuous_of_isBohrAlmostPeriodic {f : ℝ → E} (hcont : Continuous f)
    (hap : IsBohrAlmostPeriodic f) : UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := exists_delta_of_isBohrAlmostPeriodic hcont hap (ε := ε / 2) (by linarith)
  refine ⟨δ, hδ, fun a b hab => ?_⟩
  rw [dist_eq_norm]
  rw [Real.dist_eq] at hab
  exact lt_of_le_of_lt (h a b hab) (by linarith)

/-- **Bochner's criterion, elementary form.**  The translation orbit of `f` is totally bounded for
the uniform metric: for every `ε` there is a finite set of sample times such that every translate of
`f` is uniformly within `ε` of the translate by one of them. -/
def HasTotallyBoundedOrbit (f : ℝ → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ S : Finset ℝ, S.Nonempty ∧
    ∀ a : ℝ, ∃ s ∈ S, ∀ x : ℝ, ‖f (x + a) - f (x + s)‖ ≤ ε

/-- **Bohr implies Bochner.**  Every translate is an almost period away from a translate by a time in
the compact window `[0, L]`, and uniform continuity replaces that window by a finite grid. -/
theorem hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic {f : ℝ → E} (hcont : Continuous f)
    (hap : IsBohrAlmostPeriodic f) : HasTotallyBoundedOrbit f := by
  intro ε hε
  obtain ⟨L, hL, hdense⟩ := hap (ε / 2) (by linarith)
  obtain ⟨δ, hδ, hunif⟩ := exists_delta_of_isBohrAlmostPeriodic hcont hap (ε := ε / 2) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt (L / δ)
  have hNpos : 0 < (N : ℝ) := lt_of_le_of_lt (by positivity) hN
  refine ⟨(Finset.range (N + 1)).image (fun j : ℕ => (j : ℝ) * L / N), ⟨0, ?_⟩, ?_⟩
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos N), by simp⟩
  intro a
  obtain ⟨τ, hτmem, hτ⟩ := hdense (a - L)
  set s : ℝ := a - τ with hsdef
  have hs0 : 0 ≤ s := by
    have : τ ≤ a := by linarith [hτmem.2]
    linarith
  have hsL : s ≤ L := by
    have : a - L ≤ τ := hτmem.1
    linarith
  -- the grid index
  set j : ℕ := ⌊s * N / L⌋₊ with hjdef
  have hjle : (j : ℝ) ≤ s * N / L := Nat.floor_le (by positivity)
  have hjlt : s * N / L < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hjrange : j ∈ Finset.range (N + 1) := by
    refine Finset.mem_range.mpr ?_
    have hle : (j : ℝ) ≤ (N : ℝ) := by
      refine hjle.trans ?_
      rw [div_le_iff₀ hL]
      nlinarith
    exact Nat.lt_succ_of_le (by exact_mod_cast hle)
  set g : ℝ := (j : ℝ) * L / N with hgdef
  have hclose : |s - g| < δ := by
    have hjL : (j : ℝ) * L ≤ s * N := (le_div_iff₀ hL).mp hjle
    have hsN : s * N < ((j : ℝ) + 1) * L := (div_lt_iff₀ hL).mp hjlt
    have hgN : g * N = (j : ℝ) * L := by rw [hgdef]; field_simp
    have h1 : g ≤ s := by
      rw [hgdef, div_le_iff₀ hNpos]
      linarith
    have h2 : s - g < L / N := by
      rw [lt_div_iff₀ hNpos]
      nlinarith
    have hLd : L < (N : ℝ) * δ := by
      rw [div_lt_iff₀ hδ] at hN
      linarith
    have h3 : L / N < δ := by
      rw [div_lt_iff₀ hNpos]
      linarith
    rw [abs_of_nonneg (by linarith)]
    linarith
  refine ⟨g, Finset.mem_image.mpr ⟨j, hjrange, rfl⟩, fun x => ?_⟩
  have hstep1 : ‖f (x + a) - f (x + s)‖ ≤ ε / 2 := by
    have hxa : x + a = (x + s) + τ := by rw [hsdef]; ring
    rw [hxa]
    exact hτ (x + s)
  have hstep2 : ‖f (x + s) - f (x + g)‖ ≤ ε / 2 := by
    refine hunif _ _ ?_
    have : |x + s - (x + g)| = |s - g| := by congr 1; ring
    rw [this]
    exact hclose
  calc ‖f (x + a) - f (x + g)‖
      = ‖(f (x + a) - f (x + s)) + (f (x + s) - f (x + g))‖ := by congr 1; abel
    _ ≤ ‖f (x + a) - f (x + s)‖ + ‖f (x + s) - f (x + g)‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hstep1 hstep2
    _ = ε := by ring

/-- **Bochner implies Bohr.**  If finitely many sample times approximate every translate, then the
differences `a - s` between a shifted parameter and its approximating sample are almost periods, and
they are relatively dense with inclusion length the diameter of the sample set. -/
theorem isBohrAlmostPeriodic_of_hasTotallyBoundedOrbit {f : ℝ → E}
    (htb : HasTotallyBoundedOrbit f) : IsBohrAlmostPeriodic f := by
  intro ε hε
  obtain ⟨S, hSne, hS⟩ := htb ε hε
  refine ⟨max 1 (S.max' hSne - S.min' hSne), lt_of_lt_of_le one_pos (le_max_left _ _), fun a => ?_⟩
  obtain ⟨s, hsS, hs⟩ := hS (a + S.max' hSne)
  refine ⟨a + S.max' hSne - s, ⟨?_, ?_⟩, fun x => ?_⟩
  · have : s ≤ S.max' hSne := S.le_max' s hsS
    linarith
  · have : S.min' hSne ≤ s := S.min'_le s hsS
    have hdiam : S.max' hSne - s ≤ S.max' hSne - S.min' hSne := by linarith
    have hle : S.max' hSne - S.min' hSne ≤ max 1 (S.max' hSne - S.min' hSne) := le_max_right _ _
    linarith
  · have hxeq : x + (a + S.max' hSne - s) = (x - s) + (a + S.max' hSne) := by ring
    have hxeq2 : x = (x - s) + s := by ring
    rw [hxeq]
    nth_rewrite 2 [hxeq2]
    exact hs (x - s)

/-- The two criteria agree for continuous functions. -/
theorem isBohrAlmostPeriodic_iff_hasTotallyBoundedOrbit {f : ℝ → E} (hcont : Continuous f) :
    IsBohrAlmostPeriodic f ↔ HasTotallyBoundedOrbit f :=
  ⟨hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hcont,
    isBohrAlmostPeriodic_of_hasTotallyBoundedOrbit⟩

end GaloisForLFunctions
