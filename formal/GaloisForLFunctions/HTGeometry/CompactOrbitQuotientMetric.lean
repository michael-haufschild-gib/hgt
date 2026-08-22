import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# The quotient metric of a compact group of isometries

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 7.7
(`t87`).

Let `(X, d)` be a metric space with an action of a compact group `G` by isometries such that all
orbit maps `G → X`, `σ ↦ σ • x`, are continuous.  Then

`δ (x G, y G) = min_σ d (σ • x, y)`

is a metric on the orbit space `X / G` which induces the quotient topology; in particular `X / G`
is Hausdorff.

The infimum `orbitDist G x y = ⨅ σ, d (σ • x, y)` is defined without any compactness assumption;
compactness enters through `exists_orbitDist_eq`, which turns the infimum into a minimum and is
what makes `δ` positive definite.  The identification of the two topologies is proved by the
stronger statement `orbitQuotient_isOpen_iff`: a subset of `X / G` is open for the quotient
topology exactly when it contains a `δ`-ball around each of its points.
-/

namespace HTGeometry

open MulAction Metric

variable {X : Type*} [MetricSpace X]

/-- The distance from the `G`-orbit of `x` to the point `y`; equivalently, the distance between the
orbits of `x` and of `y`. -/
noncomputable def orbitDist (G : Type*) [Group G] [MulAction G X] (x y : X) : ℝ :=
  ⨅ σ : G, dist (σ • x) y

section Basic

variable {G : Type*} [Group G] [MulAction G X]

theorem orbitDist_bddBelow (x y : X) :
    BddBelow (Set.range fun σ : G => dist (σ • x) y) :=
  ⟨0, by rintro _ ⟨σ, rfl⟩; exact dist_nonneg⟩

theorem orbitDist_nonneg (x y : X) : 0 ≤ orbitDist G x y :=
  le_ciInf fun _ => dist_nonneg

theorem orbitDist_le (σ : G) (x y : X) : orbitDist G x y ≤ dist (σ • x) y :=
  ciInf_le (orbitDist_bddBelow x y) σ

theorem orbitDist_self (x : X) : orbitDist G x x = 0 :=
  le_antisymm (by simpa using orbitDist_le (1 : G) x x) (orbitDist_nonneg x x)

theorem orbitDist_le_dist (x y : X) : orbitDist G x y ≤ dist x y := by
  simpa using orbitDist_le (1 : G) x y

theorem orbitDist_smul_left (τ : G) (x y : X) : orbitDist G (τ • x) y = orbitDist G x y := by
  have h : ∀ σ : G, dist (σ • (τ • x)) y = dist ((σ * τ) • x) y := by
    intro σ; rw [mul_smul]
  calc orbitDist G (τ • x) y = ⨅ σ : G, dist ((σ * τ) • x) y := iInf_congr h
    _ = ⨅ σ : G, dist (σ • x) y := (Equiv.mulRight τ).iInf_congr (fun _ => rfl)
    _ = orbitDist G x y := rfl

end Basic

section Isometric

variable {G : Type*} [Group G] [MulAction G X] [IsIsometricSMul G X]

theorem orbitDist_comm (x y : X) : orbitDist G x y = orbitDist G y x := by
  have h : ∀ σ : G, dist (σ • x) y = dist (σ⁻¹ • y) x := by
    intro σ
    rw [← dist_smul σ⁻¹ (σ • x) y, inv_smul_smul, dist_comm]
  calc orbitDist G x y = ⨅ σ : G, dist (σ⁻¹ • y) x := iInf_congr h
    _ = ⨅ σ : G, dist (σ • y) x := (Equiv.inv G).iInf_congr (fun _ => rfl)
    _ = orbitDist G y x := rfl

theorem orbitDist_smul_right (τ : G) (x y : X) : orbitDist G x (τ • y) = orbitDist G x y := by
  rw [orbitDist_comm, orbitDist_smul_left, orbitDist_comm]

end Isometric

/-- The distance induced on the orbit space `X / G`. -/
noncomputable def orbitQuotientDist (G : Type*) [Group G] [MulAction G X] [IsIsometricSMul G X]
    (p q : orbitRel.Quotient G X) : ℝ :=
  Quotient.liftOn₂ p q (fun x y => orbitDist G x y) <| by
    rintro x y x' y' ⟨σ, rfl⟩ ⟨τ, rfl⟩
    rw [orbitDist_smul_left, orbitDist_smul_right]

section IsometricQuotient

variable {G : Type*} [Group G] [MulAction G X] [IsIsometricSMul G X]

@[simp]
theorem orbitQuotientDist_mk (x y : X) :
    orbitQuotientDist G (Quotient.mk _ x : orbitRel.Quotient G X) (Quotient.mk _ y)
      = orbitDist G x y := rfl

/-- The quotient map does not increase distances. -/
theorem orbitQuotientDist_le_dist (x y : X) :
    orbitQuotientDist G (Quotient.mk _ x : orbitRel.Quotient G X) (Quotient.mk _ y) ≤ dist x y :=
  orbitDist_le_dist x y

end IsometricQuotient

section Compact

variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [MulAction G X]

/-- For a compact group with continuous orbit maps the infimum defining `orbitDist` is attained,
so that the source's minimum formula holds. -/
theorem exists_orbitDist_eq (hcont : ∀ x : X, Continuous fun σ : G => σ • x) (x y : X) :
    ∃ σ : G, orbitDist G x y = dist (σ • x) y := by
  have hc : Continuous fun σ : G => dist (σ • x) y := (hcont x).dist continuous_const
  obtain ⟨σ, -, hσ⟩ :=
    isCompact_univ.exists_isMinOn (Set.univ_nonempty) hc.continuousOn
  exact ⟨σ, le_antisymm (orbitDist_le σ x y) (le_ciInf fun τ => hσ (Set.mem_univ τ))⟩

theorem orbitDist_eq_zero_iff (hcont : ∀ x : X, Continuous fun σ : G => σ • x) (x y : X) :
    orbitDist G x y = 0 ↔ ∃ σ : G, σ • x = y := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := exists_orbitDist_eq hcont x y
    exact ⟨σ, dist_eq_zero.mp (by rw [← hσ, h])⟩
  · rintro ⟨σ, rfl⟩
    exact le_antisymm (by simpa using orbitDist_le σ x (σ • x)) (orbitDist_nonneg _ _)

end Compact

section CompactIsometric

variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [MulAction G X]
  [IsIsometricSMul G X]

theorem orbitDist_triangle (hcont : ∀ x : X, Continuous fun σ : G => σ • x) (x y z : X) :
    orbitDist G x z ≤ orbitDist G x y + orbitDist G y z := by
  obtain ⟨σ, hσ⟩ := exists_orbitDist_eq hcont x y
  obtain ⟨τ, hτ⟩ := exists_orbitDist_eq hcont y z
  have h1 : orbitDist G x z ≤ dist (σ • x) (τ⁻¹ • z) := by
    have h := orbitDist_le σ x (τ⁻¹ • z)
    rwa [orbitDist_smul_right] at h
  have h2 : dist y (τ⁻¹ • z) = dist (τ • y) z := by
    rw [← dist_smul τ y (τ⁻¹ • z), smul_inv_smul]
  calc orbitDist G x z ≤ dist (σ • x) (τ⁻¹ • z) := h1
    _ ≤ dist (σ • x) y + dist y (τ⁻¹ • z) := dist_triangle _ _ _
    _ = orbitDist G x y + orbitDist G y z := by rw [h2, ← hσ, ← hτ]

/-- A subset of the orbit space is open for the quotient topology exactly when it contains an
`orbitQuotientDist`-ball around each of its points. -/
theorem orbitQuotient_isOpen_iff (hcont : ∀ x : X, Continuous fun σ : G => σ • x)
    (s : Set (orbitRel.Quotient G X)) :
    IsOpen s ↔ ∀ p ∈ s, ∃ ε > 0, ∀ q, orbitQuotientDist G p q < ε → q ∈ s := by
  constructor
  · intro hs p hp
    induction p using Quotient.inductionOn with
    | h x =>
      have hx : x ∈ (Quotient.mk (orbitRel G X)) ⁻¹' s := hp
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hs.preimage continuous_quotient_mk') x hx
      refine ⟨ε, hε, ?_⟩
      intro q hq
      induction q using Quotient.inductionOn with
      | h y =>
        obtain ⟨σ, hσ⟩ := exists_orbitDist_eq hcont x y
        have hlt : dist (σ • x) y < ε := by
          have hlt' : orbitDist G x y < ε := hq
          rwa [hσ] at hlt'
        have hmem : σ⁻¹ • y ∈ Metric.ball x ε := by
          rw [Metric.mem_ball, dist_comm]
          calc dist x (σ⁻¹ • y) = dist (σ • x) y := by
                rw [← dist_smul σ x (σ⁻¹ • y), smul_inv_smul]
            _ < ε := hlt
        have hmem' : (Quotient.mk (orbitRel G X) (σ⁻¹ • y)) ∈ s := hball hmem
        have heq : (Quotient.mk (orbitRel G X) (σ⁻¹ • y)) = Quotient.mk _ y :=
          Quotient.sound ⟨σ⁻¹, rfl⟩
        exact heq ▸ hmem'
  · intro h
    rw [isOpen_coinduced, Metric.isOpen_iff]
    intro x hx
    obtain ⟨ε, hε, hball⟩ := h _ hx
    refine ⟨ε, hε, fun y hy => ?_⟩
    have hxy : dist x y < ε := by rw [dist_comm]; exact Metric.mem_ball.mp hy
    exact hball _ (lt_of_le_of_lt (orbitDist_le_dist x y) hxy)

/-- **Deninger, Proposition 7.7 (`t87`).**  For a metric space `X` carrying an action of a compact
group `G` by isometries whose orbit maps are continuous, the orbit space `X / G` carries the metric
`orbitQuotientDist`, and this metric induces the quotient topology.  In particular `X / G` is
Hausdorff. -/
@[implicit_reducible]
noncomputable def orbitQuotientMetricSpace (hcont : ∀ x : X, Continuous fun σ : G => σ • x) :
    MetricSpace (orbitRel.Quotient G X) :=
  MetricSpace.ofDistTopology (orbitQuotientDist G)
    (fun p => by
      induction p using Quotient.inductionOn with
      | h x => exact orbitDist_self x)
    (fun p q => by
      induction p using Quotient.inductionOn with
      | h x =>
        induction q using Quotient.inductionOn with
        | h y => exact orbitDist_comm x y)
    (fun p q r => by
      induction p using Quotient.inductionOn with
      | h x =>
        induction q using Quotient.inductionOn with
        | h y =>
          induction r using Quotient.inductionOn with
          | h z => exact orbitDist_triangle hcont x y z)
    (orbitQuotient_isOpen_iff hcont)
    (fun p q => by
      induction p using Quotient.inductionOn with
      | h x =>
        induction q using Quotient.inductionOn with
        | h y =>
          intro h
          obtain ⟨σ, hσ⟩ := (orbitDist_eq_zero_iff hcont x y).mp h
          have hxy : x ∈ MulAction.orbit G y := ⟨σ⁻¹, by simp [← hσ]⟩
          exact Quotient.sound hxy)

end CompactIsometric

end HTGeometry
