/-
# The completed-phase accessibility plateau

A uniform per-word target bound on an endpoint law forces a uniform bound on its first-entrance
mass, hence a Markov bound on the accessibility potential and a complete-union bound at every
circuit depth.  The proof is the fixed-point equation iterated: the discounted occupation mass of a
law is the target mass of its pushforwards, geometrically discounted, plus a tail that vanishes.

Main results:
* `lawPush`, `lawTargetMass` — the one-step pushforward of an endpoint law and its target mass.
* `sum_lawPush` — the pushforward is mass preserving.
* `sum_occupation_expand` — the geometric expansion after `n` steps.
* `sum_occupation_le` — **`(11aq)` for the occupation potential**.
* `sum_hitting_le` — **`(11aq)`**: `∫ h_A dν ≤ B/(1-a)`.
* `measure_hitting_ge_le` — **`(11ar)`**: the Markov bound at level `θ`.
* `measure_reachable_le_of_uniform` — **`(11as)`**: the complete-union bound at depth `s`.
-/
import GaloisForLFunctions.HTGeometry.ObserverExcisedUnion
import GaloisForLFunctions.HTGeometry.RenewalOccupationPotential

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option linter.unusedSectionVars false

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- The one-step pushforward of an endpoint law along the chain. -/
def lawPush (P : Matrix X X ℝ) (nu : X → ℝ) : X → ℝ := fun y => ∑ x, nu x * P x y

/-- The target mass of an endpoint law. -/
def lawTargetMass (nu : X → ℝ) (A : Finset X) : ℝ := ∑ x ∈ A, nu x

theorem lawPush_nonneg {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y) {nu : X → ℝ}
    (hnu : ∀ x, 0 ≤ nu x) (y : X) : 0 ≤ lawPush P nu y :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hnu x) (hP x y)

theorem lawPush_iterate_nonneg {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y) {nu : X → ℝ}
    (hnu : ∀ x, 0 ≤ nu x) (n : ℕ) (y : X) : 0 ≤ (lawPush P)^[n] nu y := by
  induction n generalizing y with
  | zero => simpa using hnu y
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact lawPush_nonneg hP (fun x => ih x) y

/-- **The pushforward preserves total mass.** -/
theorem sum_lawPush {P : Matrix X X ℝ} (hrow : ∀ x, ∑ y, P x y = 1) (nu : X → ℝ) :
    ∑ y, lawPush P nu y = ∑ x, nu x := by
  classical
  show (∑ y, ∑ x, nu x * P x y) = ∑ x, nu x
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => by rw [← Finset.mul_sum, hrow x, mul_one]

theorem sum_lawPush_iterate {P : Matrix X X ℝ} (hrow : ∀ x, ∑ y, P x y = 1) (nu : X → ℝ)
    (n : ℕ) : ∑ y, (lawPush P)^[n] nu y = ∑ x, nu x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', sum_lawPush hrow, ih]

/-- The fixed-point equation, averaged against an endpoint law. -/
theorem sum_occupation_step {P : Matrix X X ℝ} {A : Finset X} {a : ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1)
    (nu : X → ℝ) :
    (∑ x, nu x * occupationPotential P A a hP hrow ha ha1 x)
      = lawTargetMass nu A
        + a * ∑ y, lawPush P nu y * occupationPotential P A a hP hrow ha ha1 y := by
  classical
  have hpt : ∀ x, nu x * occupationPotential P A a hP hrow ha ha1 x
      = (if x ∈ A then nu x else 0)
        + a * (nu x * ∑ y, P x y * occupationPotential P A a hP hrow ha ha1 y) := by
    intro x
    rw [occupationPotential_apply hP hrow ha ha1 x]
    by_cases hx : x ∈ A <;> simp [hx] <;> ring
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_add_distrib]
  congr 1
  · rw [lawTargetMass, Finset.sum_ite_mem, Finset.univ_inter]
  · rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => Finset.mul_sum
      Finset.univ (fun y => P x y * occupationPotential P A a hP hrow ha ha1 y) (nu x))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    show (∑ x, nu x * (P x y * occupationPotential P A a hP hrow ha ha1 y))
        = (∑ x, nu x * P x y) * occupationPotential P A a hP hrow ha ha1 y
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring

/-- The geometric expansion of the occupation mass after `n` steps. -/
theorem sum_occupation_expand {P : Matrix X X ℝ} {A : Finset X} {a : ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1)
    (nu : X → ℝ) (n : ℕ) :
    (∑ x, nu x * occupationPotential P A a hP hrow ha ha1 x)
      = (∑ l ∈ Finset.range n, a ^ l * lawTargetMass ((lawPush P)^[l] nu) A)
        + a ^ n * ∑ y, (lawPush P)^[n] nu y
            * occupationPotential P A a hP hrow ha ha1 y := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ih, Finset.sum_range_succ]
      rw [sum_occupation_step hP hrow ha ha1 ((lawPush P)^[n] nu)]
      rw [← Function.iterate_succ_apply' (lawPush P) n nu]
      ring

/-- **`(11aq)` for the occupation potential.**  A uniform target bound on every pushforward of a
probability endpoint law bounds its discounted occupation mass by `B/(1-a)`. -/
theorem sum_occupation_le {P : Matrix X X ℝ} {A : Finset X} {a B : ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1)
    {nu : X → ℝ} (hnu : ∀ x, 0 ≤ nu x) (hnusum : ∑ x, nu x = 1)
    (hB : ∀ n : ℕ, lawTargetMass ((lawPush P)^[n] nu) A ≤ B) :
    (∑ x, nu x * occupationPotential P A a hP hrow ha ha1 x) ≤ B / (1 - a) := by
  classical
  have hden : (0 : ℝ) < 1 - a := by linarith
  have hB0 : 0 ≤ B := by
    refine le_trans ?_ (hB 0)
    simpa [lawTargetMass] using
      Finset.sum_nonneg (fun x (_ : x ∈ A) => hnu x)
  have hstep : ∀ n : ℕ,
      (∑ x, nu x * occupationPotential P A a hP hrow ha ha1 x) ≤ B / (1 - a) + a ^ n / (1 - a) := by
    intro n
    rw [sum_occupation_expand hP hrow ha ha1 nu n]
    have hhead : (∑ l ∈ Finset.range n, a ^ l * lawTargetMass ((lawPush P)^[l] nu) A)
        ≤ B / (1 - a) := by
      calc (∑ l ∈ Finset.range n, a ^ l * lawTargetMass ((lawPush P)^[l] nu) A)
          ≤ ∑ l ∈ Finset.range n, a ^ l * B :=
            Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hB l) (pow_nonneg ha l)
        _ = (∑ l ∈ Finset.range n, a ^ l) * B := by rw [Finset.sum_mul]
        _ ≤ (1 - a)⁻¹ * B := by
            refine mul_le_mul_of_nonneg_right ?_ hB0
            have hgm := geom_sum_mul a n
            have hsum : (∑ l ∈ Finset.range n, a ^ l) * (1 - a) = 1 - a ^ n := by
              nlinarith [hgm]
            rw [inv_eq_one_div, le_div_iff₀ hden]
            nlinarith [pow_nonneg ha n, hsum]
        _ = B / (1 - a) := by rw [inv_mul_eq_div]
    have htail : a ^ n * ∑ y, (lawPush P)^[n] nu y
          * occupationPotential P A a hP hrow ha ha1 y ≤ a ^ n / (1 - a) := by
      have hbnd : (∑ y, (lawPush P)^[n] nu y * occupationPotential P A a hP hrow ha ha1 y)
          ≤ (1 - a)⁻¹ := by
        calc (∑ y, (lawPush P)^[n] nu y * occupationPotential P A a hP hrow ha ha1 y)
            ≤ ∑ y, (lawPush P)^[n] nu y * (1 - a)⁻¹ :=
              Finset.sum_le_sum fun y _ =>
                mul_le_mul_of_nonneg_left
                  (occupationPotential_bounds hP hrow ha ha1 y).2
                  (lawPush_iterate_nonneg hP hnu n y)
          _ = (1 - a)⁻¹ := by rw [← Finset.sum_mul, sum_lawPush_iterate hrow nu n, hnusum, one_mul]
      calc a ^ n * ∑ y, (lawPush P)^[n] nu y * occupationPotential P A a hP hrow ha ha1 y
          ≤ a ^ n * (1 - a)⁻¹ := mul_le_mul_of_nonneg_left hbnd (pow_nonneg ha n)
        _ = a ^ n / (1 - a) := by rw [← div_eq_mul_inv]
    linarith
  refine le_of_forall_pos_le_add fun eps heps => ?_
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a ^ n / (1 - a) < eps := by
    have hlim : Tendsto (fun n : ℕ => a ^ n / (1 - a)) atTop (nhds 0) := by
      have h0 : Tendsto (fun n : ℕ => a ^ n) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one ha ha1
      simpa using h0.div_const (1 - a)
    obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds heps)).exists
    exact ⟨n, hn⟩
  exact le_trans (hstep n) (by linarith)

/-- **`(11aq)`.**  The same bound for the discounted first-entrance potential. -/
theorem sum_hitting_le {P : Matrix X X ℝ} {A : Finset X} {a B : ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1)
    {nu : X → ℝ} (hnu : ∀ x, 0 ≤ nu x) (hnusum : ∑ x, nu x = 1)
    (hB : ∀ n : ℕ, lawTargetMass ((lawPush P)^[n] nu) A ≤ B) :
    (∑ x, nu x * hittingPotential P A a hP hrow ha ha1 x) ≤ B / (1 - a) :=
  le_trans (reporter_sandwich hP hrow ha ha1 nu hnu).2
    (sum_occupation_le hP hrow ha ha1 hnu hnusum hB)

/-- **`(11ar)`.**  Markov's inequality for the accessibility potential. -/
theorem measure_hitting_ge_le {P : Matrix X X ℝ} {A : Finset X} {a B theta : ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1)
    (htheta : 0 < theta)
    {nu : X → ℝ} (hnu : ∀ x, 0 ≤ nu x) (hnusum : ∑ x, nu x = 1)
    (hB : ∀ n : ℕ, lawTargetMass ((lawPush P)^[n] nu) A ≤ B) :
    (∑ x ∈ Finset.univ.filter
        (fun x => theta ≤ hittingPotential P A a hP hrow ha ha1 x), nu x)
      ≤ B / ((1 - a) * theta) := by
  classical
  set S := Finset.univ.filter
    (fun x => theta ≤ hittingPotential P A a hP hrow ha ha1 x) with hS
  have hSsum : theta * ∑ x ∈ S, nu x
      ≤ ∑ x, nu x * hittingPotential P A a hP hrow ha ha1 x := by
    calc theta * ∑ x ∈ S, nu x = ∑ x ∈ S, nu x * theta := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ ≤ ∑ x ∈ S, nu x * hittingPotential P A a hP hrow ha ha1 x := by
          refine Finset.sum_le_sum fun x hx => ?_
          exact mul_le_mul_of_nonneg_left (by simpa [hS] using (Finset.mem_filter.mp hx).2) (hnu x)
      _ ≤ ∑ x, nu x * hittingPotential P A a hP hrow ha ha1 x := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun x _ _ =>
            mul_nonneg (hnu x) (hittingPotential_mem_unitInterval hP hrow ha ha1 x).1
  have hmain := sum_hitting_le hP hrow ha ha1 hnu hnusum hB
  have hden : (0 : ℝ) < 1 - a := by linarith
  have hmain' : (1 - a) * (∑ x, nu x * hittingPotential P A a hP hrow ha ha1 x) ≤ B := by
    rw [mul_comm, ← le_div_iff₀ hden]
    exact hmain
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hSsum, hmain', hden]

/-- **`(11as)`.**  The complete-union bound: at circuit depth `s` the endpoint mass of the states
reachable within `s` steps is at most `(B/(1-a))·(M/a)^s`. -/
theorem measure_reachable_le_of_uniform {P : Matrix X X ℝ} {A : Finset X} {a B : ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 < a) (ha1 : a < 1)
    {M : ℝ} (hM : 1 ≤ M) {s : ℕ}
    {nu : X → ℝ} (hnu : ∀ x, 0 ≤ nu x) (hnusum : ∑ x, nu x = 1)
    (hB : ∀ n : ℕ, lawTargetMass ((lawPush P)^[n] nu) A ≤ B)
    (S : Finset X) (hS : ∀ x ∈ S, ReachableWithin P A M s x) :
    (∑ x ∈ S, nu x) ≤ B / (1 - a) * (M / a) ^ s := by
  classical
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hpow : (0 : ℝ) < (a / M) ^ s := by positivity
  have hsub : S ⊆ Finset.univ.filter
      (fun x => (a / M) ^ s ≤ hittingPotential P A a hP hrow ha.le ha1 x) := by
    intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ?_⟩
    obtain ⟨k, hks, path, hpath0, hlast, hstep⟩ := hS x hx
    have hbase := le_hittingPotential_of_path hP hrow ha.le ha1 hM k path hlast hstep
    rw [hpath0] at hbase
    have hratio1 : a / M ≤ 1 := by rw [div_le_one hM0]; linarith
    exact le_trans (pow_le_pow_of_le_one (div_nonneg ha.le hM0.le) hratio1 hks) hbase
  have hmain := measure_hitting_ge_le hP hrow ha.le ha1 hpow hnu hnusum hB
  have hmono : (∑ x ∈ S, nu x)
      ≤ ∑ x ∈ Finset.univ.filter
          (fun x => (a / M) ^ s ≤ hittingPotential P A a hP hrow ha.le ha1 x), nu x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => hnu x
  refine le_trans hmono (le_trans hmain (le_of_eq ?_))
  have hinv : ((a / M) ^ s)⁻¹ = (M / a) ^ s := by
    rw [← inv_pow, inv_div]
  rw [div_mul_eq_div_div, div_eq_mul_inv, hinv]

end

end GaloisForLFunctions.HTGeometry
