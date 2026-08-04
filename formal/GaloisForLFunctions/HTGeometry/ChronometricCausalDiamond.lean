import GaloisForLFunctions.HTGeometry.ChronometricTimelikeConeDetermination

/-!
# Clock-only reconstruction inside a causal diamond

Proper time determines a chart metric field globally. A laboratory, however, carries its clocks only
through a bounded region of spacetime — the causal diamond between two events — and its readings say
nothing about the metric elsewhere.

The determination argument is pointwise in the event, so it localizes exactly: clocks that agree at
every event of a region determine the metric at every event of that region, and at no other. The
region of interest is the coordinate causal diamond, whose cone at each of its two tips is the cone
of the metric there; the timelike segment joining the tips lies inside it, so the region a clock can
actually traverse is not empty.
-/

namespace GaloisForLFunctions.HTGeometry

namespace SmoothPseudoMetric

/-! ## Clock readings on a region -/

variable {d : ℕ}

/-- **Clock-only reconstruction on a region.** Two chart metrics whose clocks report the same
squared interval on every timelike direction at every event of a region agree at every event of that
region. Nothing outside the region is claimed. -/
theorem eqOn_of_properTime_eqOn {g h : SmoothPseudoMetric d} {W : Set (Fin d → ℝ)}
    (htimelike : ∀ x ∈ W, (g.timelikeCone x).Nonempty)
    (heq : ∀ x ∈ W, ∀ v ∈ g.timelikeCone x, g.squaredInterval x v = h.squaredInterval x v) :
    ∀ x ∈ W, g.metric x = h.metric x := by
  intro x hx
  have hbilin : Matrix.toBilin' (g.metric x) = Matrix.toBilin' (h.metric x) := by
    refine bilinForm_eq_of_diagonal_eqOn_open (g.toBilin'_symm x) (h.toBilin'_symm x)
      (g.isOpen_timelikeCone x) (htimelike x hx) ?_
    intro v hv
    rw [g.toBilin'_diag_eq_squaredInterval, h.toBilin'_diag_eq_squaredInterval]
    exact heq x hx v hv
  exact (Matrix.toBilin' (R₁ := ℝ) (n := Fin d)).injective hbilin

/-! ## The coordinate causal diamond -/

/-- The causal future of an event in the cone of the metric there: displacements of nonpositive
squared interval with nondecreasing time coordinate. -/
def coneFuture (g : SmoothPseudoMetric (d + 1)) (p : Fin (d + 1) → ℝ) :
    Set (Fin (d + 1) → ℝ) :=
  {x | g.squaredInterval p (x - p) ≤ 0 ∧ p 0 ≤ x 0}

/-- The causal past of an event in the cone of the metric there. -/
def conePast (g : SmoothPseudoMetric (d + 1)) (q : Fin (d + 1) → ℝ) :
    Set (Fin (d + 1) → ℝ) :=
  {x | g.squaredInterval q (x - q) ≤ 0 ∧ x 0 ≤ q 0}

/-- The coordinate causal diamond between two events. -/
def coneDiamond (g : SmoothPseudoMetric (d + 1)) (p q : Fin (d + 1) → ℝ) :
    Set (Fin (d + 1) → ℝ) :=
  coneFuture g p ∩ conePast g q

theorem squaredInterval_zero (g : SmoothPseudoMetric d) (x : Fin d → ℝ) :
    g.squaredInterval x (0 : Fin d → ℝ) = 0 := by
  simp [squaredInterval]

theorem mem_coneFuture_self (g : SmoothPseudoMetric (d + 1)) (p : Fin (d + 1) → ℝ) :
    p ∈ coneFuture g p := by
  refine ⟨?_, le_rfl⟩
  rw [sub_self, g.squaredInterval_zero p]

theorem mem_conePast_self (g : SmoothPseudoMetric (d + 1)) (q : Fin (d + 1) → ℝ) :
    q ∈ conePast g q := by
  refine ⟨?_, le_rfl⟩
  rw [sub_self, g.squaredInterval_zero q]

/-! ## The diamond is traversed by a clock -/

/-- The future-directed time axis of the chart. -/
def timeAxis (d : ℕ) : Fin (d + 1) → ℝ := fun i => if (i : ℕ) = 0 then 1 else 0

theorem minkowski_squaredInterval_smul_timeAxis (d : ℕ) (x : Fin (d + 1) → ℝ) (t : ℝ) :
    (minkowski (d + 1)).squaredInterval x (t • timeAxis d) = -(t * t) := by
  classical
  have hval : (minkowski (d + 1)).squaredInterval x (t • timeAxis d)
      = ∑ i : Fin (d + 1),
        (if (i : ℕ) = 0 then (-1 : ℝ) else 1) * (t • timeAxis d) i * (t • timeAxis d) i := by
    exact ofSignature_squaredInterval _ _ x (t • timeAxis d)
  rw [hval, Finset.sum_eq_single (0 : Fin (d + 1))]
  · simp [timeAxis]
  · intro i _ hi
    have hival : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
    simp [timeAxis, hival]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin (d + 1))) h

theorem sub_smul_timeAxis (p : Fin (d + 1) → ℝ) (t T : ℝ) :
    (p + t • timeAxis d) - (p + T • timeAxis d) = (t - T) • timeAxis d := by
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem apply_zero_add_smul_timeAxis (p : Fin (d + 1) → ℝ) (t : ℝ) :
    (p + t • timeAxis d) 0 = p 0 + t := by
  simp [timeAxis]

/-- **The clock's own worldline lies in the diamond.** Every event of the timelike segment joining
the two tips belongs to the coordinate diamond of Minkowski space, so the region on which clock
readings are collected is not empty. -/
theorem mem_coneDiamond_segment (p : Fin (d + 1) → ℝ) {T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    p + t • timeAxis d ∈ coneDiamond (minkowski (d + 1)) p (p + T • timeAxis d) := by
  have hfuture : p + t • timeAxis d ∈ coneFuture (minkowski (d + 1)) p := by
    constructor
    · have hsub : (p + t • timeAxis d) - p = t • timeAxis d := by
        funext i
        simp
      rw [hsub, minkowski_squaredInterval_smul_timeAxis]
      nlinarith [mul_self_nonneg t]
    · rw [apply_zero_add_smul_timeAxis]
      linarith
  have hpast : p + t • timeAxis d ∈ conePast (minkowski (d + 1)) (p + T • timeAxis d) := by
    constructor
    · rw [sub_smul_timeAxis, minkowski_squaredInterval_smul_timeAxis]
      nlinarith [mul_self_nonneg (t - T)]
    · rw [apply_zero_add_smul_timeAxis, apply_zero_add_smul_timeAxis]
      linarith
  exact ⟨hfuture, hpast⟩

/-- **Clock-only reconstruction inside a causal diamond.** Clocks that agree on every timelike
direction at every event of the diamond determine the metric at every event of the diamond. -/
theorem eqOn_coneDiamond_of_properTime {g h : SmoothPseudoMetric (d + 1)}
    (p q : Fin (d + 1) → ℝ)
    (htimelike : ∀ x ∈ coneDiamond g p q, (g.timelikeCone x).Nonempty)
    (heq : ∀ x ∈ coneDiamond g p q, ∀ v ∈ g.timelikeCone x,
      g.squaredInterval x v = h.squaredInterval x v) :
    ∀ x ∈ coneDiamond g p q, g.metric x = h.metric x :=
  eqOn_of_properTime_eqOn htimelike heq

/-! ## The chronological diamond -/

/-- The chronological future of an event: strictly timelike displacements into the future. -/
def chronoFuture (g : SmoothPseudoMetric (d + 1)) (p : Fin (d + 1) → ℝ) :
    Set (Fin (d + 1) → ℝ) :=
  {x | g.squaredInterval p (x - p) < 0 ∧ p 0 < x 0}

/-- The chronological past of an event. -/
def chronoPast (g : SmoothPseudoMetric (d + 1)) (q : Fin (d + 1) → ℝ) :
    Set (Fin (d + 1) → ℝ) :=
  {x | g.squaredInterval q (x - q) < 0 ∧ x 0 < q 0}

/-- The chronological diamond between two events. It is open, so it is a laboratory region in which
probes may be posed. -/
def chronoDiamond (g : SmoothPseudoMetric (d + 1)) (p q : Fin (d + 1) → ℝ) :
    Set (Fin (d + 1) → ℝ) :=
  chronoFuture g p ∩ chronoPast g q

theorem isOpen_chronoFuture (g : SmoothPseudoMetric (d + 1)) (p : Fin (d + 1) → ℝ) :
    IsOpen (chronoFuture g p) := by
  have hcont : Continuous fun x : Fin (d + 1) → ℝ => g.squaredInterval p (x - p) :=
    (g.continuous_squaredInterval p).comp (continuous_id.sub continuous_const)
  exact (isOpen_lt hcont continuous_const).inter (isOpen_lt continuous_const (continuous_apply 0))

theorem isOpen_chronoPast (g : SmoothPseudoMetric (d + 1)) (q : Fin (d + 1) → ℝ) :
    IsOpen (chronoPast g q) := by
  have hcont : Continuous fun x : Fin (d + 1) → ℝ => g.squaredInterval q (x - q) :=
    (g.continuous_squaredInterval q).comp (continuous_id.sub continuous_const)
  exact (isOpen_lt hcont continuous_const).inter (isOpen_lt (continuous_apply 0) continuous_const)

theorem isOpen_chronoDiamond (g : SmoothPseudoMetric (d + 1)) (p q : Fin (d + 1) → ℝ) :
    IsOpen (chronoDiamond g p q) :=
  (isOpen_chronoFuture g p).inter (isOpen_chronoPast g q)

theorem chronoDiamond_subset_coneDiamond (g : SmoothPseudoMetric (d + 1))
    (p q : Fin (d + 1) → ℝ) : chronoDiamond g p q ⊆ coneDiamond g p q := by
  rintro x ⟨⟨h₁, h₂⟩, h₃, h₄⟩
  exact ⟨⟨le_of_lt h₁, le_of_lt h₂⟩, le_of_lt h₃, le_of_lt h₄⟩

/-- **The chronological diamond is not empty.** The interior of the clock's own worldline segment
lies in it. -/
theorem mem_chronoDiamond_segment (p : Fin (d + 1) → ℝ) {T t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    p + t • timeAxis d ∈ chronoDiamond (minkowski (d + 1)) p (p + T • timeAxis d) := by
  have hfuture : p + t • timeAxis d ∈ chronoFuture (minkowski (d + 1)) p := by
    constructor
    · have hsub : (p + t • timeAxis d) - p = t • timeAxis d := by
        funext i
        simp
      rw [hsub, minkowski_squaredInterval_smul_timeAxis]
      nlinarith
    · rw [apply_zero_add_smul_timeAxis]
      linarith
  have hpast : p + t • timeAxis d ∈ chronoPast (minkowski (d + 1)) (p + T • timeAxis d) := by
    constructor
    · rw [sub_smul_timeAxis, minkowski_squaredInterval_smul_timeAxis]
      nlinarith
    · rw [apply_zero_add_smul_timeAxis, apply_zero_add_smul_timeAxis]
      linarith
  exact ⟨hfuture, hpast⟩

end SmoothPseudoMetric

end GaloisForLFunctions.HTGeometry
