import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.GaussianJumpReadings
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Recovering momentum labels from a sparse network of Weil measurements

For the linear and quadratic jumps it suffices to observe specified pairs.
One calibrated absolute value propagates through its connected component.
Otherwise all squared momenta in that component take at most two values;
the alternative assignment swaps those values at every vertex. Once
magnitudes are known, each connected component left after deleting zero
momenta has precisely one free common sign.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.Sparse
variable {n : ℕ}
private abbrev Probes (n : ℕ) := Fin n → {x : ℝ // 1 ≤ x}

/-- Only the two observed entries on each edge are used. -/
def «matches» (G : SimpleGraph (Fin n)) (r s : Fin n → ℝ) (p : Probes n) :=
  ∀ i j, G.Adj i j → jumpReadout 1 r p i j = jumpReadout 1 s p i j ∧
    jumpReadout 2 r p i j = jumpReadout 2 s p i j

theorem edges_exact (G : SimpleGraph (Fin n)) (r s : Fin n → ℝ) (p : Probes n) :
    «matches» G r s p ↔ ∀ i j, G.Adj i j → indistinguishablePair (r i) (r j) (s i) (s j) := by
  have he (k : ℕ) (i j : Fin n) :
      jumpReadout k r p i j = jumpReadout k s p i j ↔ powerRate k (r i) (r j)=powerRate k (s i) (s j) :=
    (reading_eq_iff _ _ _).trans (or_iff_right (safe_probeGram_entry_ne_zero p i j))
  simp only [«matches»,he,pair_two_rates_iff]

private theorem along {V : Type*} {G : SimpleGraph V} {P : V → Prop}
    (step : ∀ i j, G.Adj i j → P i → P j) {i j : V} (h : G.Reachable i j) : P i → P j := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact id
  | cons he _ ih => exact fun h => ih (step _ _ he h)

private theorem propagate {x y u v : ℝ} (he : indistinguishablePair x y u v) :
    x^2=u^2 → y^2=v^2 := by
  rcases he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
    simp_all [eq_comm]

private theorem swapped {x y u v : ℝ} (he : indistinguishablePair x y u v) (hn : x^2≠u^2) :
    (y^2=x^2 ∧ v^2=u^2 ∨ y^2=u^2 ∧ v^2=x^2) ∧ y*v=x*u := by
  rcases he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
    simp_all [mul_comm]

/-- Exact magnitude propagation, including through zero-momentum vertices. -/
theorem anchored_magnitudes (G : SimpleGraph (Fin n)) (r s : Fin n → ℝ) (p : Probes n)
    (o : Fin n) : «matches» G r s p → r o^2=s o^2 → ∀ i, G.Reachable o i → r i^2=s i^2 := by
  intro h ho i hi
  exact along (fun j k hjk => propagate ((edges_exact _ _ _ _).mp h j k hjk)) hi ho

/-- Every uncalibrated component consists of a globally exchanged pair of
squared levels. Even the signed product of old and new labels is constant. -/
theorem component_alternative (G : SimpleGraph (Fin n)) (r s : Fin n → ℝ) (p : Probes n)
    (o : Fin n) : «matches» G r s p →
    (∀ i, G.Reachable o i → r i^2=s i^2) ∨
    (r o^2≠s o^2 ∧ ∀ i, G.Reachable o i →
      (r i^2=r o^2 ∧ s i^2=s o^2 ∨ r i^2=s o^2 ∧ s i^2=r o^2) ∧ r i*s i=r o*s o) := by
  intro h
  by_cases ho : r o^2=s o^2
  · exact Or.inl (anchored_magnitudes G r s p o h ho)
  right
  refine ⟨ho,fun i hi => ?_⟩
  let P := fun i => (r i^2=r o^2 ∧ s i^2=s o^2 ∨ r i^2=s o^2 ∧ s i^2=r o^2) ∧ r i*s i=r o*s o
  have step (j k) (he : G.Adj j k) (hj : P j) : P k := by
    have hn : r j^2≠s j^2 := by
      rcases hj.1 with ⟨h1,h2⟩|⟨h1,h2⟩ <;> rw [h1,h2] <;> first | exact ho | exact Ne.symm ho
    obtain ⟨H,hm⟩ := swapped ((edges_exact _ _ _ _).mp h j k he) hn
    refine ⟨?_,hm.trans hj.2⟩
    rcases H with ⟨h1,h2⟩|⟨h1,h2⟩
    · rw [h1,h2]; exact hj.1
    · rw [h1,h2]
      rcases hj.1 with ⟨e1,e2⟩|⟨e1,e2⟩
      · exact Or.inr ⟨e2,e1⟩
      · exact Or.inl ⟨e2,e1⟩
  exact along step hi ⟨Or.inl ⟨rfl,rfl⟩,rfl⟩

/-- Once absolute momenta agree, the remaining edge information is exactly
the sign of the product. This criterion includes zero and diagonal edges. -/
theorem magnitude_and_edge_products (G : SimpleGraph (Fin n)) (r s : Fin n → ℝ) (p : Probes n) :
    (∀ i, r i^2=s i^2) → («matches» G r s p ↔ ∀ i j, G.Adj i j → r i*r j=s i*s j) := by
  intro hmag
  rw [edges_exact]
  constructor
  · intro h i j he
    have H := ((pair_two_rates_iff _ _ _ _).mpr (h i j he)).1
    simp only [powerRate,gapCost,pow_one] at H
    linear_combination -4*H+(hmag i)/2+(hmag j)/2
  · intro h i j he
    apply (pair_two_rates_iff _ _ _ _).mp
    constructor
    · simp only [powerRate,gapCost,pow_one]
      linear_combination ((hmag i)+(hmag j)-2*(h i j he))/8
    · simp only [powerRate,gapCost,hmag]

/-- Independent sign choices on selected vertices. -/
def flip (e : Fin n → Bool) (r : Fin n → ℝ) (i : Fin n) := if e i then -(r i) else r i

private def support (r : Fin n → ℝ) := {i | r i ≠ 0}

/-- The unobservable signs are exactly independent common signs on the
connected components of the nonzero induced graph. -/
theorem sign_freedom (G : SimpleGraph (Fin n)) (r : Fin n → ℝ) (p : Probes n) (e : Fin n → Bool) :
    «matches» G r (flip e r) p ↔
      ∀ i j : support r, (G.induce (support r)).Reachable i j → e i.val=e j.val := by
  have hm (i) : r i^2=flip e r i^2 := by cases h : e i <;> simp [flip,h]
  rw [magnitude_and_edge_products _ _ _ _ hm]
  constructor
  · intro hp i j hj
    have step (u v : support r) (he : (G.induce _).Adj u v) : e u.val=e v.val := by
      have H := hp u.val v.val he
      have hn : r u.val*r v.val ≠ 0 := mul_ne_zero u.property v.property
      cases hu : e u.val <;> cases hv : e v.val <;> simp_all [flip]
      all_goals exact hn (by linarith only [H])
    exact along (P := fun v : support r => e i.val=e v.val) (fun u v he hu => hu.trans (step u v he)) hj rfl
  · intro h i j he
    by_cases hi : r i=0
    · simp [flip,hi]
    by_cases hj : r j=0
    · simp [flip,hj]
    have hs : e i=e j := h ⟨i,hi⟩ ⟨j,hj⟩ (show (G.induce _).Adj ⟨i,hi⟩ ⟨j,hj⟩ from he).reachable
    cases hb : e j <;> simp [flip,hs,hb]

#print axioms edges_exact
#print axioms anchored_magnitudes
#print axioms component_alternative
#print axioms magnitude_and_edge_products
#print axioms sign_freedom
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.Sparse
