import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic

/-!
# Small certificates for enclosing balls

Helly's theorem reduces finite enclosing-ball feasibility in dimension `d`
to subsets of at most `d+1` points. Compactness attains the minimum radius;
taking the largest minimum among these small subsets gives a support set
for the full minimum. In the plane, three points suffice.

This is the finite support mechanism of Lemma 5.4 of
Kittipassorn--Phetmak--Sriamorn, extended to arbitrary finite-dimensional
real normed spaces.
-/

noncomputable section
namespace GaloisForLFunctions.HilbertMetric

open Metric Set

variable {ι E : Type*} [NormedAddCommGroup E]

/-- A finite indexed configuration fits inside one closed ball. -/
def FitsBall (p : ι → E) (s : Finset ι) (r : ℝ) : Prop :=
  ∃ c : E, ∀ i ∈ s, dist (p i) c ≤ r

/-- Enclosing-ball feasibility has certificates of size at most dimension plus one. -/
theorem fitsBall_iff_small_subsets [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (p : ι → E) (s : Finset ι) (r : ℝ) :
    FitsBall p s r ↔ ∀ t ⊆ s, t.card ≤ Module.finrank ℝ E + 1 → FitsBall p t r := by
  constructor
  · rintro ⟨c, hc⟩ t hts _
    exact ⟨c, fun i hi => hc i (hts hi)⟩
  · intro h
    have hsmall : ∀ t ⊆ s, t.card ≤ Module.finrank ℝ E + 1 →
        (⋂ i ∈ t, closedBall (p i) r).Nonempty := by
      intro t hts hcard
      obtain ⟨c, hc⟩ := h t hts hcard
      refine ⟨c, mem_iInter.mpr fun i => mem_iInter.mpr fun hi => ?_⟩
      simpa only [mem_closedBall, dist_comm] using hc i hi
    obtain ⟨c, hc⟩ := Convex.helly_theorem'
      (fun i (_ : i ∈ s) => convex_closedBall (p i) r) hsmall
    refine ⟨c, fun i hi => ?_⟩
    have hci := mem_iInter.mp (mem_iInter.mp hc i) hi
    simpa only [mem_closedBall, dist_comm] using hci

/-- Enlarging a ball preserves feasibility. -/
theorem FitsBall.mono_radius {p : ι → E} {s : Finset ι} {r q : ℝ}
    (h : FitsBall p s r) (hrq : r ≤ q) : FitsBall p s q := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun i hi => (hc i hi).trans hrq⟩

/-- Every finite configuration in a proper normed space has a minimum enclosing radius. -/
theorem exists_minimum_enclosing_radius [ProperSpace E] (p : ι → E) (s : Finset ι) :
    ∃ r : ℝ, 0 ≤ r ∧ FitsBall p s r ∧
      ∀ q : ℝ, 0 ≤ q → FitsBall p s q → r ≤ q := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hs
    have hs : s.Nonempty := ⟨i₀, hi₀⟩
    let R : E → ℝ := fun c => s.sup' hs (fun i => dist (p i) c)
    have hRcont : Continuous R := by
      have heq : R = s.sup' hs (fun i c => dist (p i) c) := by
        funext c
        exact (Finset.sup'_apply hs (fun i c => dist (p i) c) c).symm
      rw [heq]
      exact Continuous.finset_sup' hs (fun _ _ => continuous_const.dist continuous_id)
    have hRnonneg (c : E) : 0 ≤ R c :=
      dist_nonneg.trans (Finset.le_sup' (fun i => dist (p i) c) hi₀)
    have hzero : (0 : E) ∈ closedBall (p i₀) (R 0) := by
      rw [mem_closedBall, dist_comm]
      exact Finset.le_sup' (fun i => dist (p i) 0) hi₀
    obtain ⟨c, _, hmin⟩ := (isCompact_closedBall (p i₀) (R 0)).exists_isMinOn
      ⟨0, hzero⟩ hRcont.continuousOn
    refine ⟨R c, hRnonneg c, ⟨c, fun i hi => Finset.le_sup' (fun j => dist (p j) c) hi⟩, ?_⟩
    rintro q _ ⟨c', hc'⟩
    have hbase : R c ≤ R 0 := hmin hzero
    by_cases hc'ball : c' ∈ closedBall (p i₀) (R 0)
    · exact (hmin hc'ball).trans (Finset.sup'_le hs _ hc')
    · have hfar : R 0 < dist (p i₀) c' := by
        simpa only [mem_closedBall, not_le, dist_comm] using hc'ball
      exact hbase.trans ((hfar.le).trans (hc' i₀ hi₀))
  · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    exact ⟨0, le_rfl, ⟨0, by simp⟩, fun _ hq _ => hq⟩

/-- The attained nonnegative minimum enclosing radius. -/
def enclosingRadius [ProperSpace E] (p : ι → E) (s : Finset ι) : ℝ :=
  Classical.choose (exists_minimum_enclosing_radius p s)

theorem enclosingRadius_nonneg [ProperSpace E] (p : ι → E) (s : Finset ι) :
    0 ≤ enclosingRadius p s :=
  (Classical.choose_spec (exists_minimum_enclosing_radius p s)).1

theorem fitsBall_enclosingRadius [ProperSpace E] (p : ι → E) (s : Finset ι) :
    FitsBall p s (enclosingRadius p s) :=
  (Classical.choose_spec (exists_minimum_enclosing_radius p s)).2.1

/-- A candidate radius works exactly when it is no smaller than the minimum. -/
theorem fitsBall_iff_enclosingRadius_le [ProperSpace E] (p : ι → E) (s : Finset ι)
    {r : ℝ} (hr : 0 ≤ r) : FitsBall p s r ↔ enclosingRadius p s ≤ r := by
  constructor
  · exact (Classical.choose_spec (exists_minimum_enclosing_radius p s)).2.2 r hr
  · exact (fitsBall_enclosingRadius p s).mono_radius

/-- Adding points cannot decrease the minimum radius. -/
theorem enclosingRadius_mono [ProperSpace E] (p : ι → E) {s t : Finset ι} (hst : s ⊆ t) :
    enclosingRadius p s ≤ enclosingRadius p t := by
  apply (fitsBall_iff_enclosingRadius_le p s (enclosingRadius_nonneg p t)).mp
  obtain ⟨c, hc⟩ := fitsBall_enclosingRadius p t
  exact ⟨c, fun i hi => hc i (hst hi)⟩

/-- At most dimension plus one points determine the exact minimum radius. -/
theorem exists_small_support_enclosingRadius [NormedSpace ℝ E] [ProperSpace E]
    [FiniteDimensional ℝ E]
    (p : ι → E) (s : Finset ι) :
    ∃ t ⊆ s, t.card ≤ Module.finrank ℝ E + 1 ∧ enclosingRadius p s = enclosingRadius p t := by
  classical
  let P := s.powerset.filter (fun t => t.card ≤ Module.finrank ℝ E + 1)
  have hP : P.Nonempty := ⟨∅, by simp [P]⟩
  obtain ⟨t, ht, hmax⟩ := P.exists_max_image (enclosingRadius p) hP
  have ht' := Finset.mem_filter.mp ht
  have hts : t ⊆ s := Finset.mem_powerset.mp ht'.1
  have hfits : FitsBall p s (enclosingRadius p t) := by
    apply (fitsBall_iff_small_subsets p s _).mpr
    intro u hus hucard
    apply (fitsBall_iff_enclosingRadius_le p u (enclosingRadius_nonneg p t)).mpr
    exact hmax u (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hus, hucard⟩)
  exact ⟨t, hts, ht'.2, le_antisymm
    ((fitsBall_iff_enclosingRadius_le p s (enclosingRadius_nonneg p t)).mp hfits)
    (enclosingRadius_mono p hts)⟩

/-- Three-point subsets determine every finite enclosing-disk feasibility question. -/
theorem fitsDisk_iff_triples (p : ι → ℂ) (s : Finset ι) (r : ℝ) :
    FitsBall p s r ↔ ∀ t ⊆ s, t.card ≤ 3 → FitsBall p t r := by
  simpa only [Complex.finrank_real_complex] using fitsBall_iff_small_subsets p s r

/-- Every finite planar configuration has a support of at most three points at its minimum radius. -/
theorem exists_three_point_support (p : ι → ℂ) (s : Finset ι) :
    ∃ t ⊆ s, t.card ≤ 3 ∧ enclosingRadius p s = enclosingRadius p t := by
  simpa only [Complex.finrank_real_complex] using exists_small_support_enclosingRadius p s

/-- A nonempty finite planar configuration has a unique centre at its minimum radius. -/
theorem minimum_enclosing_centre_unique (p : ι → ℂ) (s : Finset ι) (hs : s.Nonempty)
    {c d : ℂ}
    (hc : ∀ i ∈ s, dist (p i) c ≤ enclosingRadius p s)
    (hd : ∀ i ∈ s, dist (p i) d ≤ enclosingRadius p s) : c = d := by
  classical
  let R := enclosingRadius p s
  let m : ℂ := (1 / 2 : ℝ) • (c + d)
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image (fun i => dist (p i) m) hs
  have hm : R ≤ ‖p i - m‖ := by
    have h := (fitsBall_iff_enclosingRadius_le p s (dist_nonneg : 0 ≤ dist (p i) m)).mp
      ⟨m, hmax⟩
    simpa only [dist_eq_norm] using h
  have hR : 0 ≤ R := enclosingRadius_nonneg p s
  have hc' : ‖p i - c‖ ≤ R := by simpa only [dist_eq_norm] using hc i hi
  have hd' : ‖p i - d‖ ≤ R := by simpa only [dist_eq_norm] using hd i hi
  have hcSq : Complex.normSq (p i - c) ≤ R ^ 2 := by
    simp only [Complex.normSq_eq_norm_sq, pow_two]
    exact mul_le_mul hc' hc' (norm_nonneg _) hR
  have hdSq : Complex.normSq (p i - d) ≤ R ^ 2 := by
    simp only [Complex.normSq_eq_norm_sq, pow_two]
    exact mul_le_mul hd' hd' (norm_nonneg _) hR
  have hmSq : R ^ 2 ≤ Complex.normSq (p i - m) := by
    simp only [Complex.normSq_eq_norm_sq, pow_two]
    exact mul_le_mul hm hm hR (norm_nonneg _)
  have hpar : 4 * Complex.normSq (p i - m) + Complex.normSq (c - d) =
      2 * Complex.normSq (p i - c) + 2 * Complex.normSq (p i - d) := by
    simp only [m, Complex.real_smul, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    ring
  have hz : Complex.normSq (c - d) = 0 := by
    apply le_antisymm
    · linarith only [hpar, hcSq, hdSq, hmSq]
    · rw [Complex.normSq_eq_norm_sq]
      exact sq_nonneg _
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp hz)

end GaloisForLFunctions.HilbertMetric

#print axioms GaloisForLFunctions.HilbertMetric.fitsBall_iff_small_subsets
#print axioms GaloisForLFunctions.HilbertMetric.exists_minimum_enclosing_radius
#print axioms GaloisForLFunctions.HilbertMetric.exists_three_point_support
#print axioms GaloisForLFunctions.HilbertMetric.minimum_enclosing_centre_unique
