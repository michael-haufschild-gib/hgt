import GaloisForLFunctions.HTGeometry.ChronometricBundleMetricRigidity

/-!
# Proper time alone determines the chronometric field

Squared clock intervals are directly measured only on timelike directions: a clock carried along a
worldline reports `g_x(v,v)` for `v` in the timelike cone, and the spacelike part of the signed
quadratic germ was left to a separate radar protocol.

That bridge is not needed. A symmetric bilinear form whose diagonal vanishes on *any* nonempty open
set vanishes identically: restricting a quadratic function to a line through an interior point
gives a degree-two real polynomial vanishing on an interval, so all of its coefficients vanish, and
its leading coefficient is the diagonal value at an arbitrary vector.

Consequently two chronometric fields agreeing on their timelike cones agree everywhere, and the
branch-safe rigidity theorem holds with proper-time data alone.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

open scoped BigOperators

section OpenDetermination

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [ContinuousAdd V] [ContinuousSMul ℝ V]

/-- **A symmetric bilinear form whose diagonal vanishes on a nonempty open set has vanishing
diagonal everywhere.** The line `t ↦ v₀ + t • w` meets the open set in an interval, on which the
diagonal is a degree-two polynomial in `t`; its leading coefficient is `D w w`. -/
theorem bilin_diag_eq_zero_of_diag_eqOn_open
    {D : LinearMap.BilinForm ℝ V} (hsymm : ∀ u v, D u v = D v u)
    {U : Set V} (hU : IsOpen U) {v₀ : V} (hv₀ : v₀ ∈ U)
    (hzero : ∀ v ∈ U, D v v = 0) (w : V) : D w w = 0 := by
  have hline : Continuous fun t : ℝ => v₀ + t • w :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hopen : IsOpen ((fun t : ℝ => v₀ + t • w) ⁻¹' U) := hU.preimage hline
  have hmem : (0 : ℝ) ∈ (fun t : ℝ => v₀ + t • w) ⁻¹' U := by
    simpa using hv₀
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.mp hopen 0 hmem
  have hzero₀ : D v₀ v₀ = 0 := hzero v₀ hv₀
  have hexpand : ∀ t : ℝ,
      D (v₀ + t • w) (v₀ + t • w) =
        D v₀ v₀ + t * D v₀ w + t * D w v₀ + (t * t) * D w w := by
    intro t
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hkey : ∀ t : ℝ, |t| < e → t ≠ 0 → 2 * D v₀ w + t * D w w = 0 := by
    intro t ht htne
    have hmemU : v₀ + t • w ∈ U := by
      refine hball ?_
      simpa [Real.dist_eq] using ht
    have hvanish := hzero _ hmemU
    rw [hexpand t, hzero₀, hsymm w v₀] at hvanish
    have hfactor : t * (2 * D v₀ w + t * D w w) = 0 := by linarith
    rcases mul_eq_zero.mp hfactor with h | h
    · exact absurd h htne
    · exact h
  have habs₁ : |e / 2| < e := by
    rw [abs_of_pos (by linarith)]
    linarith
  have habs₂ : |e / 4| < e := by
    rw [abs_of_pos (by linarith)]
    linarith
  have h₁ := hkey (e / 2) habs₁ (by positivity)
  have h₂ := hkey (e / 4) habs₂ (by positivity)
  have hprod : e * D w w = 0 := by linarith
  rcases mul_eq_zero.mp hprod with h | h
  · exact absurd h (ne_of_gt he)
  · exact h

/-- **Two symmetric bilinear forms agreeing on the diagonal over a nonempty open set are equal.** -/
theorem bilinForm_eq_of_diagonal_eqOn_open
    {B C : LinearMap.BilinForm ℝ V}
    (hB : ∀ u v, B u v = B v u) (hC : ∀ u v, C u v = C v u)
    {U : Set V} (hU : IsOpen U) (hne : U.Nonempty)
    (hdiag : ∀ v ∈ U, B v v = C v v) : B = C := by
  obtain ⟨v₀, hv₀⟩ := hne
  have hsymm : ∀ u v, (B - C) u v = (B - C) v u := by
    intro u v
    simp only [LinearMap.sub_apply]
    rw [hB u v, hC u v]
  have hzero : ∀ v ∈ U, (B - C) v v = 0 := by
    intro v hv
    simp only [LinearMap.sub_apply]
    rw [hdiag v hv, sub_self]
  have hall : ∀ w, (B - C) w w = 0 :=
    fun w => bilin_diag_eq_zero_of_diag_eqOn_open hsymm hU hv₀ hzero w
  refine bilinForm_eq_of_diagonal_eq hB hC fun w => ?_
  have := hall w
  simp only [LinearMap.sub_apply] at this
  linarith

end OpenDetermination

/-! ## Bundle fields determined by an open cone of directions -/

namespace BundleChronometricMetric

variable {Event : Type u} {Fiber : Event → Type v}
  [∀ x, AddCommGroup (Fiber x)] [∀ x, Module ℝ (Fiber x)]
  [∀ x, TopologicalSpace (Fiber x)] [∀ x, ContinuousAdd (Fiber x)]
  [∀ x, ContinuousSMul ℝ (Fiber x)]

/-- **Squared clock intervals on any fiberwise nonempty open family of directions determine the
complete bundle metric field.** -/
theorem eq_of_squaredInterval_eqOn_open
    {g h : BundleChronometricMetric Event Fiber}
    {U : ∀ x, Set (Fiber x)} (hU : ∀ x, IsOpen (U x)) (hne : ∀ x, (U x).Nonempty)
    (heq : ∀ x, ∀ v ∈ U x, g.squaredInterval x v = h.squaredInterval x v) : g = h := by
  refine ext ?_
  funext x
  exact bilinForm_eq_of_diagonal_eqOn_open (g.symmetric x) (h.symmetric x) (hU x) (hne x)
    (heq x)

end BundleChronometricMetric

/-! ## Charts: proper time alone -/

namespace SmoothPseudoMetric

variable {d : ℕ}

theorem continuous_squaredInterval (g : SmoothPseudoMetric d) (x : Fin d → ℝ) :
    Continuous fun v : Fin d → ℝ => g.squaredInterval x v := by
  simp only [squaredInterval]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (continuous_const.mul (continuous_apply i)).mul (continuous_apply j)

/-- The timelike cone at an event: directions of negative squared interval, i.e. the directions a
clock can be carried along. -/
def timelikeCone (g : SmoothPseudoMetric d) (x : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {v | g.squaredInterval x v < 0}

theorem isOpen_timelikeCone (g : SmoothPseudoMetric d) (x : Fin d → ℝ) :
    IsOpen (g.timelikeCone x) :=
  isOpen_lt (g.continuous_squaredInterval x) continuous_const

theorem mem_timelikeCone_iff (g : SmoothPseudoMetric d) (x v : Fin d → ℝ) :
    v ∈ g.timelikeCone x ↔ g.squaredInterval x v < 0 := Iff.rfl

/-- Chart metrics are symmetric bilinear forms, in the form required by the open-cone theorem. -/
theorem toBilin'_diag_eq_squaredInterval (g : SmoothPseudoMetric d) (x v : Fin d → ℝ) :
    Matrix.toBilin' (g.metric x) v v = g.squaredInterval x v :=
  (g.squaredInterval_eq_toBilin' x v).symm

/-- **Proper time alone determines a smooth chart metric field.**

If at every event some direction is timelike, and two chart metrics report the same squared
interval on every timelike direction of the first, then the two metrics are equal. No radar
reconstruction of spacelike separations is needed. -/
theorem eq_of_properTime_eq {g h : SmoothPseudoMetric d}
    (htimelike : ∀ x, (g.timelikeCone x).Nonempty)
    (heq : ∀ x, ∀ v ∈ g.timelikeCone x, g.squaredInterval x v = h.squaredInterval x v) :
    g = h := by
  refine ext' ?_
  funext x
  have hbilin : Matrix.toBilin' (g.metric x) = Matrix.toBilin' (h.metric x) := by
    refine bilinForm_eq_of_diagonal_eqOn_open (g.toBilin'_symm x) (h.toBilin'_symm x)
      (g.isOpen_timelikeCone x) (htimelike x) ?_
    intro v hv
    rw [g.toBilin'_diag_eq_squaredInterval, h.toBilin'_diag_eq_squaredInterval]
    exact heq x v hv
  exact (Matrix.toBilin' (R₁ := ℝ) (n := Fin d)).injective hbilin

/-- Proper-time observation of a chart metric field: the squared interval restricted to the
timelike cone, together with the cone itself. -/
noncomputable def properTimeObservation (g : SmoothPseudoMetric d) :
    ((Fin d → ℝ) → Set (Fin d → ℝ)) × ((Fin d → ℝ) → (Fin d → ℝ) → ℝ) :=
  (g.timelikeCone, fun x => (g.timelikeCone x).indicator (g.squaredInterval x))

/-- **Proper-time data alone are injective on chart metric fields with a timelike direction at
every event.** -/
theorem properTimeObservation_injOn
    {g h : SmoothPseudoMetric d} (hg : ∀ x, (g.timelikeCone x).Nonempty)
    (hdata : g.properTimeObservation = h.properTimeObservation) : g = h := by
  have hcone : g.timelikeCone = h.timelikeCone := congrArg Prod.fst hdata
  have hvalue : ∀ x v, (g.timelikeCone x).indicator (g.squaredInterval x) v =
      (h.timelikeCone x).indicator (h.squaredInterval x) v := by
    intro x v
    exact congrFun (congrFun (congrArg Prod.snd hdata) x) v
  refine eq_of_properTime_eq hg fun x v hv => ?_
  have hx := hvalue x v
  rw [← hcone, Set.indicator_of_mem hv, Set.indicator_of_mem hv] at hx
  exact hx

/-- **Branch-safe gravity-operator rigidity from proper time alone.**

Restricted to chart metric fields carrying a timelike direction at every event, equality of
proper-time solution graphs is equality of the nonlinear gravity operators. -/
theorem chronometricOperatorRigidity_properTime {Source : Type w}
    (law₁ law₂ : SmoothPseudoMetric d → Source)
    (hcone : ∀ g : SmoothPseudoMetric d, ∀ x, (g.timelikeCone x).Nonempty)
    (hgraph : chronometricSolutionGraph properTimeObservation law₁ =
      chronometricSolutionGraph properTimeObservation law₂) :
    law₁ = law₂ := by
  have hinj : Function.Injective (properTimeObservation (d := d)) := by
    intro g h hdata
    exact properTimeObservation_injOn (hcone g) hdata
  exact (chronometricSolutionGraph_eq_iff_of_injective hinj law₁ law₂).1 hgraph

/-! ### The proper-time hypothesis is satisfiable -/

theorem ofSignature_squaredInterval {d : ℕ} (eps : Fin d → ℝ) (heps : ∀ i, eps i ≠ 0)
    (x v : Fin d → ℝ) :
    (ofSignature eps heps).squaredInterval x v = ∑ i, eps i * v i * v i := by
  simp only [squaredInterval, ofSignature, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem minkowski_squaredInterval {d : ℕ} (x v : Fin d → ℝ) :
    (minkowski d).squaredInterval x v =
      ∑ i : Fin d, (if (i : ℕ) = 0 then (-1 : ℝ) else 1) * v i * v i :=
  ofSignature_squaredInterval _ _ x v

/-- **Minkowski space has a timelike direction at every event**, so the proper-time determination
theorem is not vacuous. -/
theorem minkowski_timelikeCone_nonempty {d : ℕ} (hd : 0 < d) (x : Fin d → ℝ) :
    ((minkowski d).timelikeCone x).Nonempty := by
  refine ⟨Pi.single (⟨0, hd⟩ : Fin d) 1, ?_⟩
  rw [mem_timelikeCone_iff, minkowski_squaredInterval,
    Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
  · norm_num
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

end SmoothPseudoMetric

end GaloisForLFunctions.HTGeometry
