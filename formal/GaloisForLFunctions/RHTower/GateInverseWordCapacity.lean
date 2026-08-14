import GaloisForLFunctions.RHTower.GateCapacityDiscrepancy
import GaloisForLFunctions.RHTower.GateWordRenewalBridge
import GaloisForLFunctions.RHTower.GateWordComplexityLaws

/-!
# Inverse-word conversion and the capacity form of the circuit union

An inverse-closed gate alphabet acting by isometries turns the forward synthesis process into a
backward walk on states: the distance from a synthesized point to a target equals the distance from
the seed to the inversely transported target.  The discounted first-hit mass of the target tube,
read as a function of the target, therefore satisfies the Bellman--Dirichlet equation of the
backward walk and is its equilibrium potential.

Consequently the complete circuit union of the parent first-entrance law becomes a capacity bound:
the probability that a random target is reachable within a fixed synthesis length is controlled by
the discounted capacity of the seed tube, corrected by the directional capacity discrepancy of the
target law.
-/

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.RHTower

section InverseWord

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] [Nonempty Γ]
variable {X : Type*} [PseudoMetricSpace X]

/-- The backward gate action of an inverse-closed alphabet. -/
def backAct (act : Γ → X → X) (inv : Γ → Γ) : Γ → X → X := fun g x => act (inv g) x

/-- The closed tube of a given radius around a point. -/
def tube (ε : ℝ) (v : X) : Set X := {x : X | dist x v ≤ ε}

theorem mem_tube_comm {ε : ℝ} {x v : X} : x ∈ tube ε v ↔ v ∈ tube ε x := by
  simp only [tube, Set.mem_setOf_eq, dist_comm]

/-- **Inverse-word conversion.**  Pulling a target tube back along a gate is the tube around the
inversely transported target. -/
theorem preimage_tube (act : Γ → X → X) (inv : Γ → Γ)
    (hinv : ∀ g x, act (inv g) (act g x) = x)
    (hiso : ∀ g x y, dist (act g x) (act g y) = dist x y) (ε : ℝ) (g : Γ) (v : X) :
    {x : X | act g x ∈ tube ε v} = tube ε (backAct act inv g v) := by
  ext x
  simp only [tube, Set.mem_setOf_eq, backAct]
  rw [← hiso (inv g) (act g x) v, hinv g x]

/-- The discounted first-hit mass of the target tube, read as a function of the target. -/
noncomputable def firstHitPotential (act : Γ → X → X) (χ : X) (ε : ℝ) (a : ℝ) :
    X → ℝ := fun v => firstHitMassReal act χ (tube ε v) a

theorem firstHitPotential_of_mem (act : Γ → X → X) (χ : X) (ε : ℝ) (a : ℝ) {v : X}
    (hv : v ∈ tube ε χ) : firstHitPotential act χ ε a v = 1 := by
  rw [firstHitPotential, firstHitMassReal,
    firstHitMass_of_mem act (ENNReal.ofReal a) (mem_tube_comm.mpr hv)]
  simp

/-- **Backward Bellman equation.**  Off the seed tube the first-hit potential takes one killed
backward step. -/
theorem firstHitPotential_recursion (act : Γ → X → X) (inv : Γ → Γ)
    (hinv : ∀ g x, act (inv g) (act g x) = x)
    (hiso : ∀ g x y, dist (act g x) (act g y) = dist x y) (χ : X) (ε : ℝ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {v : X} (hv : v ∉ tube ε χ) :
    firstHitPotential act χ ε a v =
      a * ((∑ g : Γ, firstHitPotential act χ ε a (backAct act inv g v)) / Fintype.card Γ) := by
  have hχ : χ ∉ tube ε v := fun hc => hv (mem_tube_comm.mp hc)
  have haE : ENNReal.ofReal a ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ha1
  have hMtop : (Fintype.card Γ : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hrec := firstHitMass_recursion act χ (tube ε v) hχ (ENNReal.ofReal a)
  have hpull : ∀ g : Γ, {x : X | act g x ∈ tube ε v} = tube ε (backAct act inv g v) :=
    fun g => preimage_tube act inv hinv hiso ε g v
  rw [Finset.sum_congr rfl (fun g _ => by rw [hpull g])] at hrec
  have hne : ∀ g : Γ, firstHitMass act χ (tube ε (backAct act inv g v)) (ENNReal.ofReal a) ≠ ⊤ :=
    fun g => firstHitMass_ne_top act χ _ haE
  rw [firstHitPotential, firstHitMassReal, hrec, ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_ofReal ha0, ENNReal.toReal_natCast, ENNReal.toReal_sum (fun g _ => hne g)]
  simp only [firstHitPotential, firstHitMassReal]
  ring

end InverseWord

section BackwardChain

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] [Nonempty Γ]
variable {X : Type*} [Fintype X] [DecidableEq X] [PseudoMetricSpace X]

/-- The number of gates carrying a state to another under the backward action. -/
def gateCount (act : Γ → X → X) (inv : Γ → Γ) (x y : X) : ℕ :=
  (Finset.univ.filter (fun g : Γ => backAct act inv g x = y)).card

/-- A chain whose transition law counts backward gates averages functions over the alphabet. -/
theorem step_eq_of_gateCount (C : ReversibleChain X) (act : Γ → X → X) (inv : Γ → Γ)
    (hker : ∀ x y, C.kernel x y = (gateCount act inv x y : ℝ) / Fintype.card Γ)
    (f : X → ℝ) (x : X) :
    C.step f x = (∑ g : Γ, f (backAct act inv g x)) / Fintype.card Γ := by
  classical
  have hfib : (∑ y : X, (gateCount act inv x y : ℝ) * f y) =
      ∑ g : Γ, f (backAct act inv g x) := by
    have hinner : ∀ y : X, (gateCount act inv x y : ℝ) * f y =
        ∑ g ∈ Finset.univ.filter (fun g : Γ => backAct act inv g x = y),
          f (backAct act inv g x) := by
      intro y
      rw [gateCount, Finset.sum_congr rfl (fun g hg => by
        rw [(Finset.mem_filter.mp hg).2]), Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_congr rfl fun y _ => hinner y]
    exact Finset.sum_fiberwise Finset.univ (fun g : Γ => backAct act inv g x)
      (fun g => f (backAct act inv g x))
  rw [ReversibleChain.step, Finset.sum_congr rfl fun y _ => by rw [hker x y], ← hfib,
    Finset.sum_div]
  exact Finset.sum_congr rfl fun y _ => by rw [div_mul_eq_mul_div]

/-- **Equilibrium potential of the seed tube.**  The first-hit potential of the seed tube is the
equilibrium potential of the backward gate chain. -/
theorem potential_eq_firstHitPotential (C : ReversibleChain X) (act : Γ → X → X) (inv : Γ → Γ)
    (hinv : ∀ g x, act (inv g) (act g x) = x)
    (hiso : ∀ g x y, dist (act g x) (act g y) = dist x y)
    (hker : ∀ x y, C.kernel x y = (gateCount act inv x y : ℝ) / Fintype.card Γ)
    (χ : X) (ε : ℝ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    C.potential a (tube ε χ) = firstHitPotential act χ ε a := by
  classical
  set u : X → ℝ := C.potential a (tube ε χ) - firstHitPotential act χ ε a with hu
  have hbnd : ∀ x ∈ tube ε χ, u x = 0 := by
    intro x hx
    simp only [hu, Pi.sub_apply, C.potential_of_mem a hx,
      firstHitPotential_of_mem act χ ε a hx, sub_self]
  have hharm : ∀ x, x ∉ tube ε χ → C.killed a u x = 0 := by
    intro x hx
    have h1 : C.killed a (C.potential a (tube ε χ)) x = 0 :=
      C.killed_potential_of_notMem ha0 ha1.le hx
    have h2 : C.killed a (firstHitPotential act χ ε a) x = 0 := by
      rw [ReversibleChain.killed, step_eq_of_gateCount C act inv hker,
        ← firstHitPotential_recursion act inv hinv hiso χ ε ha0 ha1.le hx, sub_self]
    have hsub : C.killed a u x =
        C.killed a (C.potential a (tube ε χ)) x - C.killed a (firstHitPotential act χ ε a) x := by
      simp only [hu, ReversibleChain.killed, ReversibleChain.step, Pi.sub_apply]
      have : ∀ y : X, C.kernel x y * (C.potential a (tube ε χ) y -
          firstHitPotential act χ ε a y) =
          C.kernel x y * C.potential a (tube ε χ) y -
            C.kernel x y * firstHitPotential act χ ε a y := fun y => by ring
      rw [Finset.sum_congr rfl fun y _ => this y, Finset.sum_sub_distrib]
      ring
    rw [hsub, h1, h2, sub_zero]
  have := C.eq_zero_of_boundary_of_killed_harmonic ha0 ha1 hbnd hharm
  funext x
  have hx := congrFun this x
  simp only [hu, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hx
  exact hx

end BackwardChain

section CapacityUnion

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] [Nonempty Γ]
variable {X : Type*} [Fintype X] [DecidableEq X] [PseudoMetricSpace X]

/-- The set of targets reachable from the seed within a fixed synthesis length. -/
def reachableSet (act : Γ → X → X) (χ : X) (ε : ℝ) (s : ℕ) : Set X :=
  {v : X | ∃ w : List Γ, w.length ≤ s ∧ wordEval act w χ ∈ tube ε v}

/-- On the reachable set the first-hit potential dominates the inverse discount power. -/
theorem one_le_pow_mul_firstHitPotential (act : Γ → X → X) (χ : X) (ε : ℝ) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (s : ℕ) {v : X} (hv : v ∈ reachableSet act χ ε s) :
    1 ≤ (Fintype.card Γ / a) ^ s * firstHitPotential act χ ε a v := by
  classical
  have hM : (0 : ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos (α := Γ)
  have hM1 : (1 : ℝ) ≤ Fintype.card Γ := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero (α := Γ))
  obtain ⟨v₁, hv₁len, hv₁⟩ := hv
  obtain ⟨w₀, hw₀, hmin⟩ := exists_minimal_hitting_word act χ (tube ε v) ⟨v₁, hv₁⟩
  have hlen : w₀.length ≤ s := le_trans (hmin v₁ hv₁) hv₁len
  have hle1 : a / (Fintype.card Γ : ℝ) ≤ 1 := by
    rw [div_le_one hM]
    linarith
  have hlow : (a / Fintype.card Γ) ^ s ≤ firstHitPotential act χ ε a v := by
    refine le_trans (pow_le_pow_of_le_one (by positivity) hle1 hlen) ?_
    exact (firstHitMassReal_sandwich act χ (tube ε v) ha0 ha1 hw₀ hmin).1
  have hcancel : ((Fintype.card Γ : ℝ) / a) ^ s * (a / Fintype.card Γ) ^ s = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm ((Fintype.card Γ : ℝ)) a,
      div_self (by positivity), one_pow]
  calc (1 : ℝ) = ((Fintype.card Γ : ℝ) / a) ^ s * (a / Fintype.card Γ) ^ s := hcancel.symm
    _ ≤ ((Fintype.card Γ : ℝ) / a) ^ s * firstHitPotential act χ ε a v := by
        refine mul_le_mul_of_nonneg_left hlow ?_
        positivity

/-- **Capacity union bound.**  The mass of the reachable set under any target law is controlled by
the mean first-hit potential. -/
theorem measure_reachableSet_le (act : Γ → X → X) (χ : X) (ε : ℝ) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (s : ℕ) {ν : X → ℝ} (hν : ∀ v, 0 ≤ ν v) :
    ∑ v, Set.indicator (reachableSet act χ ε s) ν v ≤
      (Fintype.card Γ / a) ^ s * ∑ v, ν v * firstHitPotential act χ ε a v := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  by_cases hv : v ∈ reachableSet act χ ε s
  · rw [Set.indicator_of_mem hv]
    have h := one_le_pow_mul_firstHitPotential act χ ε ha0 ha1 s hv
    calc ν v = ν v * 1 := (mul_one _).symm
      _ ≤ ν v * (((Fintype.card Γ : ℝ) / a) ^ s * firstHitPotential act χ ε a v) :=
          mul_le_mul_of_nonneg_left h (hν v)
      _ = ((Fintype.card Γ : ℝ) / a) ^ s * (ν v * firstHitPotential act χ ε a v) := by ring
  · rw [Set.indicator_of_notMem hv]
    have hFnn : 0 ≤ firstHitPotential act χ ε a v := ENNReal.toReal_nonneg
    have : (0:ℝ) ≤ ((Fintype.card Γ : ℝ) / a) ^ s := by positivity
    exact mul_nonneg this (mul_nonneg (hν v) hFnn)

/-- **Stationary capacity union bound.**  Under the stationary target law the reachable mass is
controlled by the discounted capacity of the seed tube. -/
theorem stationary_capacity_union_bound (C : ReversibleChain X) (act : Γ → X → X) (inv : Γ → Γ)
    (hinv : ∀ g x, act (inv g) (act g x) = x)
    (hiso : ∀ g x y, dist (act g x) (act g y) = dist x y)
    (hker : ∀ x y, C.kernel x y = (gateCount act inv x y : ℝ) / Fintype.card Γ)
    (χ : X) (ε : ℝ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (s : ℕ) :
    ∑ v, Set.indicator (reachableSet act χ ε s) C.stat v ≤
      (Fintype.card Γ / a) ^ s * (C.capacity a (tube ε χ) / (1 - a)) := by
  have hpot := potential_eq_firstHitPotential C act inv hinv hiso hker χ ε ha0.le ha1
  have hbound := measure_reachableSet_le act χ ε ha0 ha1 s (ν := C.stat)
    (fun v => (C.stat_pos v).le)
  rw [← hpot] at hbound
  rwa [C.stationary_mean ha0.le ha1 (tube ε χ)] at hbound

/-- **Nonstationary capacity union bound.**  For an arbitrary target law the reachable mass picks
up exactly the directional capacity discrepancy. -/
theorem capacity_union_bound (C : ReversibleChain X) (act : Γ → X → X) (inv : Γ → Γ)
    (hinv : ∀ g x, act (inv g) (act g x) = x)
    (hiso : ∀ g x y, dist (act g x) (act g y) = dist x y)
    (hker : ∀ x y, C.kernel x y = (gateCount act inv x y : ℝ) / Fintype.card Γ)
    (χ : X) (ε : ℝ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (s : ℕ) {ν : X → ℝ}
    (hν : ∀ v, 0 ≤ ν v) :
    ∑ v, Set.indicator (reachableSet act χ ε s) ν v ≤
      (Fintype.card Γ / a) ^ s *
        (C.capacity a (tube ε χ) / (1 - a) + C.discrepancy a (tube ε χ) ν) := by
  have hpot := potential_eq_firstHitPotential C act inv hinv hiso hker χ ε ha0.le ha1
  have hbound := measure_reachableSet_le act χ ε ha0 ha1 s hν
  rw [← hpot] at hbound
  rwa [C.mean_potential_eq ha0.le ha1 (tube ε χ) ν] at hbound

/-- **Dual capacity union bound.**  The discrepancy correction is controlled by capacity and the
killed negative-energy square. -/
theorem capacity_union_bound_dual (C : ReversibleChain X) (act : Γ → X → X) (inv : Γ → Γ)
    (hinv : ∀ g x, act (inv g) (act g x) = x)
    (hiso : ∀ g x y, dist (act g x) (act g y) = dist x y)
    (hker : ∀ x y, C.kernel x y = (gateCount act inv x y : ℝ) / Fintype.card Γ)
    (χ : X) (ε : ℝ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (s : ℕ) {ν : X → ℝ}
    (hν : ∀ v, 0 ≤ ν v) :
    ∑ v, Set.indicator (reachableSet act χ ε s) ν v ≤
      (Fintype.card Γ / a) ^ s *
        (C.capacity a (tube ε χ) / (1 - a) +
          Real.sqrt (C.capacity a (tube ε χ)) * Real.sqrt (C.dualNormSq a ν)) := by
  refine le_trans (capacity_union_bound C act inv hinv hiso hker χ ε ha0 ha1 s hν) ?_
  have hcd := C.abs_discrepancy_le ha0.le ha1 (tube ε χ) ν
  have hpow : (0:ℝ) ≤ ((Fintype.card Γ : ℝ) / a) ^ s := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hpow
  have := le_of_abs_le hcd
  linarith

end CapacityUnion

end GaloisForLFunctions.RHTower
