import GaloisForLFunctions.HTGeometry.Quantum.FermionTransport.FiniteRateComparison
import GaloisForLFunctions.HTGeometry.Quantum.FermionTransport.GraphFlow

/-!
# Small-time propagation of particles and vacancies

The incoming rate matrix and its transpose bound the Pauli-blocked
particle and vacancy equations. Their iterates enumerate the
positive-weight walks that can carry an initially present particle or
vacancy. The first such walk length gives the exact small-time power.
-/

open Set Filter
open scoped BigOperators Topology

namespace GaloisForLFunctions.HTGeometry.Quantum.FermiGraph

noncomputable section

variable {V : Type*} [Fintype V]

/-- The incoming rate from the second vertex to the first. -/
def particleRate (G : WeightedGraph V) (E : V → ℝ) (v u : V) : ℝ :=
  G.w v u * Real.exp (E u)

/-- A uniform upper bound on total arrival and departure coefficients. -/
def propagationLoss (G : WeightedGraph V) (E : V → ℝ) : ℝ :=
  ∑ v, graphRateBound G E v

omit [Fintype V] in
private theorem particleRate_nonneg (G : WeightedGraph V) (E : V → ℝ) (v u : V) :
    0 ≤ particleRate G E v u :=
  mul_nonneg (G.w_nonneg v u) (Real.exp_pos _).le

private theorem particleRate_row_bound (G : WeightedGraph V) (E : V → ℝ) (v : V) :
    (∑ u, (particleRate G E v u + particleRate G E u v)) ≤ propagationLoss G E :=
  Finset.single_le_sum (fun u _ => graphRateBound_nonneg G E u) (Finset.mem_univ v)

private def exchangeDrift (r : V → V → ℝ) (f : V → ℝ) (v : V) : ℝ :=
  ∑ u, (r v u * (f u * (1 - f v)) - r u v * (f v * (1 - f u)))

private theorem exchangeDrift_vacancy (r : V → V → ℝ) (f : V → ℝ) (v : V) :
    exchangeDrift (fun a b => r b a) (fun u => 1 - f u) v = -exchangeDrift r f v := by
  unfold exchangeDrift
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun u _ => by ring

private theorem clippedDrift_eq_exchangeDrift (G : WeightedGraph V) (E f : V → ℝ)
    (hf : ∀ v, f v ∈ Icc (0 : ℝ) 1) (v : V) :
    clippedDrift G E f v = exchangeDrift (particleRate G E) f v := by
  rw [clippedDrift_eq_of_box G E f hf v]
  unfold exchangeDrift
  exact Finset.sum_congr rfl fun u _ => by rw [particleRate, particleRate, G.w_symm u v]

private theorem exchangeDrift_bounds (r : V → V → ℝ) (hr : ∀ v u, 0 ≤ r v u) (c : ℝ)
    (f : V → ℝ) (hf : ∀ v, f v ∈ Icc (0 : ℝ) 1) (v : V)
    (hc : (∑ u, (r v u + r u v)) ≤ c) :
    rateApply r f v ≤ exchangeDrift r f v + c * f v ∧ exchangeDrift r f v ≤ rateApply r f v := by
  have he : rateApply r f v - exchangeDrift r f v =
      ∑ u, (r v u * f u + r u v * (1 - f u)) * f v := by
    unfold rateApply exchangeDrift
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  have hn : 0 ≤ ∑ u, (r v u * f u + r u v * (1 - f u)) * f v :=
    Finset.sum_nonneg fun u _ => mul_nonneg
      (add_nonneg (mul_nonneg (hr v u) (hf u).1)
        (mul_nonneg (hr u v) (sub_nonneg.mpr (hf u).2))) (hf v).1
  have hu : (∑ u, (r v u * f u + r u v * (1 - f u)) * f v) ≤ c * f v := by
    calc
      _ ≤ ∑ u, (r v u + r u v) * f v :=
        Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_right
          (add_le_add (mul_le_of_le_one_right (hr v u) (hf u).2)
            (mul_le_of_le_one_right (hr u v) (sub_le_self 1 (hf u).1))) (hf v).1
      _ = (∑ u, (r v u + r u v)) * f v := (Finset.sum_mul _ _ _).symm
      _ ≤ c * f v := mul_le_mul_of_nonneg_right hc (hf v).1
  exact ⟨by linarith only [he, hu], by linarith only [he, hn]⟩

variable {G : WeightedGraph V} {E : V → ℝ} {x : ℝ → V → ℝ}

/-- Two-sided Taylor bounds for particle occupation, with coefficients
given by the incoming-rate iterates. -/
theorem IsBoxOccupationFlow.particle_taylor_bounds (h : IsBoxOccupationFlow G E x)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (v : V) :
    Real.exp (-(propagationLoss G E * t)) * rateTaylor (particleRate G E) (x 0) n t v ≤ x t v ∧
      x t v ≤ rateTaylor (particleRate G E) (x 0) n t v +
        dividedPowerFn n t * ratePower (particleRate G E) (fun _ => 1) n v := by
  have hbounds (s : ℝ) (hs : 0 ≤ s) (u : V) :
      rateApply (particleRate G E) (x s) u ≤ clippedDrift G E (x s) u + propagationLoss G E * x s u ∧
        clippedDrift G E (x s) u ≤ rateApply (particleRate G E) (x s) u := by
    rw [clippedDrift_eq_exchangeDrift G E _ (h.in_box s hs) u]
    exact exchangeDrift_bounds (particleRate G E) (particleRate_nonneg G E)
      (propagationLoss G E) _ (h.in_box s hs) u (particleRate_row_bound G E u)
  exact rateTaylor_bounds (particleRate G E) (particleRate_nonneg G E) (propagationLoss G E)
    h.hasDerivAt_coordinate h.in_box (fun s hs u => (hbounds s hs u).1)
    (fun s hs u => (hbounds s hs u).2) n ht v

/-- The vacancy equation obeys the same Taylor bounds with transposed rates. -/
theorem IsBoxOccupationFlow.vacancy_taylor_bounds (h : IsBoxOccupationFlow G E x)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (v : V) :
    let r := fun u w => particleRate G E w u
    let f := fun u => 1 - x 0 u
    Real.exp (-(propagationLoss G E * t)) * rateTaylor r f n t v ≤ 1 - x t v ∧
      1 - x t v ≤ rateTaylor r f n t v + dividedPowerFn n t * ratePower r (fun _ => 1) n v := by
  let r (u w : V) := particleRate G E w u
  let z (s : ℝ) (u : V) := 1 - x s u
  have hz (s : ℝ) (hs : 0 ≤ s) (u : V) : z s u ∈ Icc 0 1 :=
    ⟨sub_nonneg.mpr (h.in_box s hs u).2, sub_le_self _ (h.in_box s hs u).1⟩
  have hr (u w : V) : 0 ≤ r u w := particleRate_nonneg G E w u
  have hbound (s : ℝ) (hs : 0 ≤ s) (u : V) :
      rateApply r (z s) u ≤ -clippedDrift G E (x s) u + propagationLoss G E * z s u ∧
        -clippedDrift G E (x s) u ≤ rateApply r (z s) u := by
    have he : exchangeDrift r (z s) u = -clippedDrift G E (x s) u := by
      rw [clippedDrift_eq_exchangeDrift G E _ (h.in_box s hs) u]
      exact exchangeDrift_vacancy (particleRate G E) (x s) u
    have hrow : (∑ w, (r u w + r w u)) ≤ propagationLoss G E := by
      simpa only [r, add_comm] using particleRate_row_bound G E u
    rw [← he]
    exact exchangeDrift_bounds r hr (propagationLoss G E) (z s) (hz s hs) u hrow
  exact rateTaylor_bounds r hr (propagationLoss G E)
    (fun s hs u => (h.hasDerivAt_coordinate s hs u).const_sub 1) hz
    (fun s hs u => (hbound s hs u).1) (fun s hs u => (hbound s hs u).2) n ht v

/-- A walk of prescribed length using strictly positive edge weights. -/
inductive PositiveEdgeWalk (G : WeightedGraph V) : ℕ → V → V → Prop
  | zero (v : V) : PositiveEdgeWalk G 0 v v
  | snoc {n : ℕ} {u v w : V} : PositiveEdgeWalk G n u v → 0 < G.w v w →
      PositiveEdgeWalk G (n + 1) u w

omit [Fintype V] in
/-- Positive-edge reachability is exactly the existence of a walk of finite length. -/
theorem positive_reachable_iff_exists_walk (G : WeightedGraph V) (u v : V) :
    Relation.ReflTransGen (fun a b => 0 < G.w a b) u v ↔ ∃ n, PositiveEdgeWalk G n u v := by
  constructor
  · intro hp
    induction hp with
    | refl => exact ⟨0, .zero u⟩
    | tail _ he ih =>
      obtain ⟨n, hw⟩ := ih
      exact ⟨n + 1, hw.snoc he⟩
  · rintro ⟨n, hw⟩
    induction hw with
    | zero => exact .refl
    | snoc _ he ih => exact ih.tail he

omit [Fintype V] in
/-- A reachable positive coordinate determines a shortest walk from the
support of a nonnegative field. Every shorter walk starts at zero. -/
theorem exists_shortest_walk_from_support (G : WeightedGraph V) (f : V → ℝ)
    (hf : ∀ u, 0 ≤ f u) (v : V)
    (hseed : ∃ u, Relation.ReflTransGen (fun a b => 0 < G.w a b) u v ∧ 0 < f u) :
    ∃ n, (∀ j < n, ∀ u, PositiveEdgeWalk G j u v → f u = 0) ∧
      ∃ u, PositiveEdgeWalk G n u v ∧ 0 < f u := by
  classical
  obtain ⟨u, hp, hpos⟩ := hseed
  obtain ⟨m, hw⟩ := (positive_reachable_iff_exists_walk G u v).mp hp
  have he : ∃ n, ∃ w, PositiveEdgeWalk G n w v ∧ 0 < f w := ⟨m, u, hw, hpos⟩
  refine ⟨Nat.find he, ?_, Nat.find_spec he⟩
  intro j hj w hwalk
  exact (le_of_not_gt fun hpos => Nat.find_min he hj ⟨w, hwalk, hpos⟩).antisymm (hf w)

/-- A nonnegative rate iterate is positive precisely when a walk of its
length starts at a positive initial coordinate. -/
theorem ratePower_pos_iff_walk (G : WeightedGraph V) (r : V → V → ℝ)
    (hr : ∀ v u, 0 ≤ r v u) (hedge : ∀ u v, 0 < r v u ↔ 0 < G.w u v)
    (f : V → ℝ) (hf : ∀ v, 0 ≤ f v) (n : ℕ) (v : V) :
    0 < ratePower r f n v ↔ ∃ u, PositiveEdgeWalk G n u v ∧ 0 < f u := by
  induction n generalizing v with
  | zero =>
    constructor
    · intro hp
      exact ⟨v, .zero v, hp⟩
    · rintro ⟨u, hw, hp⟩
      cases hw
      exact hp
  | succ n ih =>
    have hn (u : V) : 0 ≤ ratePower r f n u := ratePower_nonneg r hr f hf n u
    change 0 < (∑ u, r v u * ratePower r f n u) ↔ _
    constructor
    · intro hp
      have hex : ∃ u, 0 < r v u * ratePower r f n u := by
        by_contra! h
        exact (not_le_of_gt hp) (Finset.sum_nonpos fun u _ => h u)
      obtain ⟨u, hu⟩ := hex
      have hc := (hedge u v).mp (pos_of_mul_pos_left hu (hn u))
      obtain ⟨a, ha, hpos⟩ := (ih u).mp (pos_of_mul_pos_right hu (hr v u))
      exact ⟨a, ha.snoc hc, hpos⟩
    · rintro ⟨a, ha, hpos⟩
      have he : ∃ u, PositiveEdgeWalk G n a u ∧ 0 < G.w u v := by
        cases ha with
        | snoc hw hh => exact ⟨_, hw, hh⟩
      obtain ⟨u, hu, hed⟩ := he
      have hp := mul_pos ((hedge u v).mpr hed) ((ih u).mpr ⟨a, hu, hpos⟩)
      exact hp.trans_le (Finset.single_le_sum
        (fun w _ => mul_nonneg (hr v w) (hn w)) (Finset.mem_univ u))

private theorem first_walk_coefficients (G : WeightedGraph V) (r : V → V → ℝ)
    (hr : ∀ v u, 0 ≤ r v u) (hedge : ∀ u v, 0 < r v u ↔ 0 < G.w u v)
    (f : V → ℝ) (hf : ∀ v, 0 ≤ f v) (n : ℕ) (v : V)
    (hshort : ∀ j < n, ∀ u, PositiveEdgeWalk G j u v → f u = 0)
    (hseed : ∃ u, PositiveEdgeWalk G n u v ∧ 0 < f u) :
    (∀ j < n, ratePower r f j v = 0) ∧ 0 < ratePower r f n v := by
  refine ⟨?_, (ratePower_pos_iff_walk G r hr hedge f hf n v).mpr hseed⟩
  intro j hj
  apply le_antisymm _ (ratePower_nonneg r hr f hf j v)
  by_contra! hp
  obtain ⟨u, hu, hfu⟩ := (ratePower_pos_iff_walk G r hr hedge f hf j v).mp hp
  exact hfu.ne' (hshort j hj u hu)

omit [Fintype V] in
private theorem particleRate_pos_iff (G : WeightedGraph V) (E : V → ℝ) (u v : V) :
    0 < particleRate G E v u ↔ 0 < G.w u v := by
  rw [particleRate, G.w_symm v u]
  exact ⟨fun h => pos_of_mul_pos_left h (Real.exp_pos _).le, fun h => mul_pos h (Real.exp_pos _)⟩

/-- The shortest particle-carrying walk length is the exact onset order.
The leading coefficient is the corresponding incoming-rate iterate
of the initial field divided by the length factorial. -/
theorem IsBoxOccupationFlow.particle_first_arrival (h : IsBoxOccupationFlow G E x)
    (n : ℕ) (v : V) (hshort : ∀ j < n, ∀ u, PositiveEdgeWalk G j u v → x 0 u = 0)
    (hseed : ∃ u, PositiveEdgeWalk G n u v ∧ 0 < x 0 u) :
    let a := ratePower (particleRate G E) (x 0) n v / (n.factorial : ℝ)
    0 < a ∧ Tendsto (fun t : ℝ => x t v / t ^ n) (𝓝[>] 0) (𝓝 a) := by
  obtain ⟨hzero, hpos⟩ := first_walk_coefficients G (particleRate G E)
    (particleRate_nonneg G E) (particleRate_pos_iff G E) (x 0)
    (fun u => (h.in_box 0 le_rfl u).1) n v hshort hseed
  exact ⟨div_pos hpos (by positivity), tendsto_div_pow_of_rateTaylor_bounds
    (particleRate G E) (x 0) (propagationLoss G E) (fun t => x t v) n v hzero
    (fun t ht => h.particle_taylor_bounds (n + 1) ht v)⟩

/-- The shortest vacancy-carrying walk length is the exact onset order
for vacancies, with the leading coefficient given by transposed rates. -/
theorem IsBoxOccupationFlow.vacancy_first_arrival (h : IsBoxOccupationFlow G E x)
    (n : ℕ) (v : V) (hshort : ∀ j < n, ∀ u, PositiveEdgeWalk G j u v → 1 - x 0 u = 0)
    (hseed : ∃ u, PositiveEdgeWalk G n u v ∧ 0 < 1 - x 0 u) :
    let r := fun u w => particleRate G E w u
    let a := ratePower r (fun u => 1 - x 0 u) n v / (n.factorial : ℝ)
    0 < a ∧ Tendsto (fun t : ℝ => (1 - x t v) / t ^ n) (𝓝[>] 0) (𝓝 a) := by
  let r (u w : V) := particleRate G E w u
  have hedge (u w : V) : 0 < r w u ↔ 0 < G.w u w := by
    have hp := particleRate_pos_iff G E w u
    rw [G.w_symm w u] at hp
    exact hp
  obtain ⟨hzero, hpos⟩ := first_walk_coefficients G r
    (fun u w => particleRate_nonneg G E w u) hedge (fun u => 1 - x 0 u)
    (fun u => sub_nonneg.mpr (h.in_box 0 le_rfl u).2) n v hshort hseed
  exact ⟨div_pos hpos (by positivity), tendsto_div_pow_of_rateTaylor_bounds
    r (fun u => 1 - x 0 u) (propagationLoss G E) (fun t => 1 - x t v) n v hzero
    (fun t ht => h.vacancy_taylor_bounds (n + 1) ht v)⟩

/-- A component containing particles has a positive leading coefficient
at every vertex, at the least length of a walk from the initial support. -/
theorem IsBoxOccupationFlow.exists_particle_onset_order (h : IsBoxOccupationFlow G E x) (v : V)
    (hseed : ∃ u, Relation.ReflTransGen (fun a b => 0 < G.w a b) u v ∧ 0 < x 0 u) :
    ∃ n, let a := ratePower (particleRate G E) (x 0) n v / (n.factorial : ℝ)
      0 < a ∧ Tendsto (fun t : ℝ => x t v / t ^ n) (𝓝[>] 0) (𝓝 a) := by
  obtain ⟨n, hshort, hs⟩ := exists_shortest_walk_from_support G (x 0)
    (fun u => (h.in_box 0 le_rfl u).1) v hseed
  exact ⟨n, h.particle_first_arrival n v hshort hs⟩

/-- A component containing vacancies has a positive leading coefficient
for the vacancy at every vertex. -/
theorem IsBoxOccupationFlow.exists_vacancy_onset_order (h : IsBoxOccupationFlow G E x) (v : V)
    (hseed : ∃ u, Relation.ReflTransGen (fun a b => 0 < G.w a b) u v ∧ 0 < 1 - x 0 u) :
    ∃ n, let r := fun u w => particleRate G E w u
      let a := ratePower r (fun u => 1 - x 0 u) n v / (n.factorial : ℝ)
      0 < a ∧ Tendsto (fun t : ℝ => (1 - x t v) / t ^ n) (𝓝[>] 0) (𝓝 a) := by
  obtain ⟨n, hshort, hs⟩ := exists_shortest_walk_from_support G (fun u => 1 - x 0 u)
    (fun u => sub_nonneg.mpr (h.in_box 0 le_rfl u).2) v hseed
  exact ⟨n, h.vacancy_first_arrival n v hshort hs⟩

#print axioms IsBoxOccupationFlow.particle_taylor_bounds
#print axioms IsBoxOccupationFlow.vacancy_taylor_bounds
#print axioms ratePower_pos_iff_walk
#print axioms IsBoxOccupationFlow.particle_first_arrival
#print axioms IsBoxOccupationFlow.vacancy_first_arrival
#print axioms IsBoxOccupationFlow.exists_particle_onset_order
#print axioms IsBoxOccupationFlow.exists_vacancy_onset_order

end

end GaloisForLFunctions.HTGeometry.Quantum.FermiGraph
