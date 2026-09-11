import GaloisForLFunctions.RHTower.RouteEIntegerWindowMass

/-!
# Literal singleton-histogram window mass

The exact anchored histogram marginal gives the Bernoulli mass of each active
subset and of every family of such subsets. Applying it to the actual slot
receiver transfers the integer-window concentration theorem to literal
histogram counts. The endpoint here assumes all nonconstant factors have the
same increasing orientation. Averaging opposite orientations remains separate.
-/

open Finset Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower.IntegerCubeAperture

/-- Components active at a specified slot. -/
def activeSet {C : Type*} [Fintype C] [DecidableEq C] (x : C → Bool) : Finset C :=
  univ.filter fun c => x c = true

theorem activeSet_eq_iff {C : Type*} [Fintype C] [DecidableEq C]
    (x : C → Bool) (s : Finset C) :
    activeSet x = s ↔ x = fun c => decide (c ∈ s) := by
  constructor
  · intro h
    funext c
    have hm : x c = true ↔ c ∈ s := by rw [← h]; simp [activeSet]
    by_cases hc : c ∈ s <;> cases hx : x c <;> simp_all
  · intro h
    subst x
    ext c
    simp [activeSet]

/-- Exact subset probability under the original uniform singleton histogram law. -/
theorem histogram_anchor_subset_mass {C : Type*} [Fintype C] [DecidableEq C]
    (m : ℕ) (k : C → Bool → ℕ)
    (hk : ∀ c, ∑ b, k c b = m+1) (hone : ∀ c, k c true = 1)
    (r : Fin (m+1)) (s : Finset C) :
    (((routeEComponentHistogramCell (fun _ : C => Bool) (m+1) k).filter
        fun h => activeSet (h r) = s).card : ℝ) /
      (routeEComponentHistogramCell (fun _ : C => Bool) (m+1) k).card =
      (1/((m+1:ℕ):ℝ))^s.card*(1-1/((m+1:ℕ):ℝ))^(Fintype.card C-s.card) := by
  simp only [activeSet_eq_iff]
  rw [routeE_componentHistogram_anchor_joint_ratio (fun _ : C => Bool) m k _ hk r]
  have hfalse (c : C) : k c false = m := by
    have h := hk c
    simp only [Fintype.sum_bool,hone c] at h
    omega
  have hm : ((m:ℕ):ℝ)/((m+1:ℕ):ℝ) = 1-1/((m+1:ℕ):ℝ) := by
    push_cast
    field_simp
    ring
  have hprod : (∏ c, (k c (decide (c ∈ s)) : ℝ)/((m+1:ℕ):ℝ)) =
      ∏ c, if c ∈ s then (1/((m+1:ℕ):ℝ)) else (1-1/((m+1:ℕ):ℝ)) := by
    apply prod_congr rfl
    intro c hc
    by_cases hs : c ∈ s
    · simp [hs,hone]
    · simpa [hs,hfalse] using hm
  rw [hprod,prod_ite]
  have h1 : univ.filter (fun c : C => c ∈ s) = s := by ext; simp
  have h2 : univ.filter (fun c : C => c ∉ s) = sᶜ := by ext; simp
  rw [h1,h2]
  simp only [prod_const,card_compl]

theorem histogram_anchor_family_mass {C : Type*} [Fintype C] [DecidableEq C]
    (m : ℕ) (k : C → Bool → ℕ)
    (hk : ∀ c, ∑ b, k c b = m+1) (hone : ∀ c, k c true = 1)
    (r : Fin (m+1)) (A : Finset (Finset C)) :
    (((routeEComponentHistogramCell (fun _ : C => Bool) (m+1) k).filter
        fun h => activeSet (h r) ∈ A).card : ℝ) /
      (routeEComponentHistogramCell (fun _ : C => Bool) (m+1) k).card =
      ∑ s ∈ A, (1/((m+1:ℕ):ℝ))^s.card*(1-1/((m+1:ℕ):ℝ))^(Fintype.card C-s.card) := by
  rw [← sum_card_fiberwise_eq_card_filter
    (routeEComponentHistogramCell (fun _ : C => Bool) (m+1) k) A (fun h => activeSet (h r))]
  push_cast
  rw [sum_div]
  apply sum_congr rfl
  intro s hs
  simpa only [Nat.cast_add,Nat.cast_one] using histogram_anchor_subset_mass m k hk hone r s

theorem slot_receiver_eq_cornerProduct {C : Type*} [Fintype C] [DecidableEq C]
    (m : ℕ) (a b : C → ℕ) (h : RouteEComponentHistory (fun _ : C => Bool) m)
    (r : Fin m) :
    routeEComponentSlotReceiver (fun _ : C => Bool)
      (fun c z => if z then (b c:ℝ) else (a c:ℝ)) h r =
      (cornerProduct a b (activeSet (h r)) : ℝ) := by
  unfold routeEComponentSlotReceiver cornerProduct
  push_cast
  apply prod_congr rfl
  intro c hc
  cases hz : h r c <;> simp [activeSet,hz]

/-- The literal physical receiver event has exactly the indicated Bernoulli mass. -/
theorem histogram_anchor_window_mass {C : Type*} [Fintype C] [DecidableEq C]
    (m : ℕ) (k : C → Bool → ℕ)
    (hk : ∀ c, ∑ b, k c b = m+1) (hone : ∀ c, k c true = 1)
    (r : Fin (m+1)) (a b : C → ℕ) (L U : ℝ) :
    (((routeEComponentHistogramCell (fun _ : C => Bool) (m+1) k).filter fun h =>
      routeEComponentSlotReceiver (fun _ : C => Bool)
        (fun c z => if z then (b c:ℝ) else (a c:ℝ)) h r ∈ Set.Icc L U).card : ℝ) /
      (routeEComponentHistogramCell (fun _ : C => Bool) (m+1) k).card =
      ∑ s ∈ (univ.filter fun s : Finset C => (cornerProduct a b s : ℝ) ∈ Set.Icc L U),
        (1/((m+1:ℕ):ℝ))^s.card*(1-1/((m+1:ℕ):ℝ))^(Fintype.card C-s.card) := by
  have h := histogram_anchor_family_mass m k hk hone r
    (univ.filter fun s : Finset C => (cornerProduct a b s : ℝ) ∈ Set.Icc L U)
  simpa only [mem_filter,mem_univ,true_and,slot_receiver_eq_cornerProduct] using h

/-- Vanishing admitted histogram fraction for increasing integer components at growing variance. -/
theorem tendsto_growing_window_histogram_mass_zero
    (d m : ℕ → ℕ) (k : ∀ n, Fin (d n) → Bool → ℕ)
    (a b : ∀ n, Fin (d n) → ℕ) (X : ℕ → ℝ) (r : ∀ n, Fin (m n+1))
    (hk : ∀ n c, ∑ z, k n c z = m n+1) (hone : ∀ n c, k n c true = 1)
    (ha : ∀ n i, 1 ≤ a n i) (hab : ∀ n i, a n i < b n i)
    (hX : Tendsto X atTop atTop)
    (hvariance : Tendsto (fun n => (d n:ℝ)*(1/((m n+1:ℕ):ℝ))*
      (1-1/((m n+1:ℕ):ℝ))) atTop atTop) :
    Tendsto (fun n =>
      (((routeEComponentHistogramCell (fun _ : Fin (d n) => Bool) (m n+1) (k n)).filter fun h =>
        routeEComponentSlotReceiver (fun _ : Fin (d n) => Bool)
          (fun c z => if z then (b n c:ℝ) else (a n c:ℝ)) h (r n) ∈
            Set.Icc (X n-Sieve.growingReciprocalMarkerWindow (X n))
              (X n+Sieve.growingReciprocalMarkerWindow (X n))).card : ℝ) /
        (routeEComponentHistogramCell (fun _ : Fin (d n) => Bool) (m n+1) (k n)).card)
      atTop (𝓝 0) := by
  have hp (n : ℕ) : 0 ≤ (1/((m n+1:ℕ):ℝ)) ∧ (1/((m n+1:ℕ):ℝ)) ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      exact_mod_cast Nat.succ_pos (m n)
  have ht := tendsto_growing_window_bernoulli_mass_zero d a b X (fun _ => 1)
    (fun n => 1/((m n+1:ℕ):ℝ)) ha hab (by intro; rfl) hp hX hvariance
  simpa only [histogram_anchor_window_mass _ _ (hk _) (hone _),
    one_mul,Fintype.card_fin] using ht

end RHTower.IntegerCubeAperture
