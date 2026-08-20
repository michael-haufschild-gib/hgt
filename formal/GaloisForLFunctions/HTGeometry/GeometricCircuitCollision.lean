/-
# One geometric random circuit replaces the complete union

The linear accessibility reporter is exactly the discounted Neumann series of the target masses of
the pushed-forward endpoint law, so it *is* the collision probability of one geometrically killed
uniform random gate word, up to the factor `1-a`.  At the depth-optimal fugacity `a_s = s/(s+1)` --
which is the unique minimizer of `a^{-s}/(1-a)`, and makes the geometric word have mean length `s`
-- the complete depth-`s` circuit union costs only `e(s+1)M^s` times that single collision.

Main results:
* `hasSum_occupation_neumann` — **the reporter is the discounted Neumann series**.
* `collisionProbability`, `collisionProbability_eq` — **`(11bo)`**: `p_coll = (1-a)Z_a`.
* `hitting_le_collision_div`, `collision_le_hitting` — the `(11bo)` sandwich.
* `measure_reachable_le_collision` — **`(11bp)`**.
* `collision_ge_measure` — **`(11bq)`**.
* `pow_mul_one_sub_le` — the optimal fugacity `a_s = s/(s+1)`.
* `measure_reachable_le_optimal` — **`(11ay)`/`(11br)`**.
-/
import GaloisForLFunctions.HTGeometry.CompletedPhaseAccessibilityPlateau
import GaloisForLFunctions.HTGeometry.CapacityEntropyBudget

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option linter.unusedSectionVars false

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-! ## The reporter is a discounted Neumann series -/

/-- **The linear reporter is the discounted Neumann series of the pushed target masses.** -/
theorem hasSum_occupation_neumann {P : Matrix X X ℝ} {A : Finset X} {a : ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1)
    {nu : X → ℝ} (hnu : ∀ x, 0 ≤ nu x) (hnusum : ∑ x, nu x = 1) :
    HasSum (fun l : ℕ => a ^ l * lawTargetMass ((lawPush P)^[l] nu) A)
      (∑ x, nu x * occupationPotential P A a hP hrow ha ha1 x) := by
  classical
  have hden : (0 : ℝ) < 1 - a := by linarith
  obtain ⟨S, hSdef⟩ : ∃ S, S = ∑ x, nu x * occupationPotential P A a hP hrow ha ha1 x :=
    ⟨_, rfl⟩
  have htailnonneg : ∀ n : ℕ,
      0 ≤ ∑ y, (lawPush P)^[n] nu y * occupationPotential P A a hP hrow ha ha1 y := by
    intro n
    exact Finset.sum_nonneg fun y _ =>
      mul_nonneg (lawPush_iterate_nonneg hP hnu n y)
        (occupationPotential_bounds hP hrow ha ha1 y).1
  have htailbound : ∀ n : ℕ,
      a ^ n * ∑ y, (lawPush P)^[n] nu y * occupationPotential P A a hP hrow ha ha1 y
        ≤ a ^ n / (1 - a) := by
    intro n
    have hbnd : (∑ y, (lawPush P)^[n] nu y * occupationPotential P A a hP hrow ha ha1 y)
        ≤ (1 - a)⁻¹ := by
      calc (∑ y, (lawPush P)^[n] nu y * occupationPotential P A a hP hrow ha ha1 y)
          ≤ ∑ y, (lawPush P)^[n] nu y * (1 - a)⁻¹ :=
            Finset.sum_le_sum fun y _ =>
              mul_le_mul_of_nonneg_left (occupationPotential_bounds hP hrow ha ha1 y).2
                (lawPush_iterate_nonneg hP hnu n y)
        _ = (1 - a)⁻¹ := by
            rw [← Finset.sum_mul, sum_lawPush_iterate hrow nu n, hnusum, one_mul]
    calc a ^ n * ∑ y, (lawPush P)^[n] nu y * occupationPotential P A a hP hrow ha ha1 y
        ≤ a ^ n * (1 - a)⁻¹ := mul_le_mul_of_nonneg_left hbnd (pow_nonneg ha n)
      _ = a ^ n / (1 - a) := by rw [← div_eq_mul_inv]
  have hpartial : ∀ n : ℕ,
      (∑ l ∈ Finset.range n, a ^ l * lawTargetMass ((lawPush P)^[l] nu) A)
        = S - a ^ n * ∑ y, (lawPush P)^[n] nu y
            * occupationPotential P A a hP hrow ha ha1 y := by
    intro n
    have := sum_occupation_expand (A := A) hP hrow ha ha1 nu n
    rw [← hSdef] at this
    linarith
  have hnonneg : ∀ l : ℕ, 0 ≤ a ^ l * lawTargetMass ((lawPush P)^[l] nu) A := by
    intro l
    refine mul_nonneg (pow_nonneg ha l) ?_
    exact Finset.sum_nonneg fun x _ => lawPush_iterate_nonneg hP hnu l x
  have hle : ∀ n : ℕ, (∑ l ∈ Finset.range n, a ^ l * lawTargetMass ((lawPush P)^[l] nu) A) ≤ S := by
    intro n
    rw [hpartial n]
    have := mul_nonneg (pow_nonneg ha n) (htailnonneg n)
    linarith
  have hsummable : Summable (fun l : ℕ => a ^ l * lawTargetMass ((lawPush P)^[l] nu) A) :=
    summable_of_sum_range_le hnonneg hle
  have hlim1 : Tendsto
      (fun n : ℕ => ∑ l ∈ Finset.range n, a ^ l * lawTargetMass ((lawPush P)^[l] nu) A) atTop
      (nhds (∑' l : ℕ, a ^ l * lawTargetMass ((lawPush P)^[l] nu) A)) :=
    hsummable.hasSum.tendsto_sum_nat
  have hlim2 : Tendsto
      (fun n : ℕ => ∑ l ∈ Finset.range n, a ^ l * lawTargetMass ((lawPush P)^[l] nu) A) atTop
      (nhds S) := by
    have hzero : Tendsto (fun n : ℕ =>
        a ^ n * ∑ y, (lawPush P)^[n] nu y
          * occupationPotential P A a hP hrow ha ha1 y) atTop (nhds 0) := by
      refine squeeze_zero (fun n => mul_nonneg (pow_nonneg ha n) (htailnonneg n))
        htailbound ?_
      have h0 : Tendsto (fun n : ℕ => a ^ n) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one ha ha1
      simpa using h0.div_const (1 - a)
    have := (tendsto_const_nhds (x := S) (f := atTop (α := ℕ))).sub hzero
    simpa [hpartial] using this
  have heq : (∑' l : ℕ, a ^ l * lawTargetMass ((lawPush P)^[l] nu) A) = S :=
    tendsto_nhds_unique hlim1 hlim2
  rw [hSdef] at heq
  rw [← heq]
  exact hsummable.hasSum

/-- **`(11bn)`.**  The collision probability of one geometrically killed uniform random gate word
against the target. -/
def collisionProbability (P : Matrix X X ℝ) (A : Finset X) (a : ℝ) (nu : X → ℝ) : ℝ :=
  ∑' l : ℕ, (1 - a) * a ^ l * lawTargetMass ((lawPush P)^[l] nu) A

/-- **`(11bo)`, first equality.**  `p_coll = (1-a)·Z_a(ν,A)`. -/
theorem collisionProbability_eq {P : Matrix X X ℝ} {A : Finset X} {a : ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1)
    {nu : X → ℝ} (hnu : ∀ x, 0 ≤ nu x) (hnusum : ∑ x, nu x = 1) :
    collisionProbability P A a nu
      = (1 - a) * ∑ x, nu x * occupationPotential P A a hP hrow ha ha1 x := by
  have hbase := hasSum_occupation_neumann (A := A) hP hrow ha ha1 hnu hnusum
  have hscaled := hbase.mul_left (1 - a)
  rw [collisionProbability]
  rw [show (fun l : ℕ => (1 - a) * a ^ l * lawTargetMass ((lawPush P)^[l] nu) A)
      = fun l : ℕ => (1 - a) * (a ^ l * lawTargetMass ((lawPush P)^[l] nu) A) by
    funext l; ring]
  exact hscaled.tsum_eq

/-- **`(11bo)`, right half.**  The first-entrance mass is at most the collision probability divided
by `1-a`. -/
theorem hitting_le_collision_div {P : Matrix X X ℝ} {A : Finset X} {a : ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1)
    {nu : X → ℝ} (hnu : ∀ x, 0 ≤ nu x) (hnusum : ∑ x, nu x = 1) :
    (∑ x, nu x * hittingPotential P A a hP hrow ha ha1 x)
      ≤ collisionProbability P A a nu / (1 - a) := by
  have hden : (0 : ℝ) < 1 - a := by linarith
  rw [collisionProbability_eq hP hrow ha ha1 hnu hnusum, mul_div_assoc, mul_comm,
    div_mul_eq_mul_div, mul_div_assoc, div_self (ne_of_gt hden), mul_one]
  exact (reporter_sandwich hP hrow ha ha1 nu hnu).2

/-- **`(11bo)`, left half.**  The collision probability is at most the first-entrance mass. -/
theorem collision_le_hitting {P : Matrix X X ℝ} {A : Finset X} {a : ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1)
    {nu : X → ℝ} (hnu : ∀ x, 0 ≤ nu x) (hnusum : ∑ x, nu x = 1) :
    collisionProbability P A a nu
      ≤ ∑ x, nu x * hittingPotential P A a hP hrow ha ha1 x := by
  rw [collisionProbability_eq hP hrow ha ha1 hnu hnusum]
  exact (reporter_sandwich hP hrow ha ha1 nu hnu).1

/-- **`(11bp)`.**  The complete depth-`s` circuit union is at most `(M/a)^s/(1-a)` times one
geometric-circuit collision. -/
theorem measure_reachable_le_collision {P : Matrix X X ℝ} {A : Finset X} {a : ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 < a) (ha1 : a < 1)
    {M : ℝ} (hM : 1 ≤ M) {s : ℕ}
    {nu : X → ℝ} (hnu : ∀ x, 0 ≤ nu x) (hnusum : ∑ x, nu x = 1)
    (S : Finset X) (hS : ∀ x ∈ S, ReachableWithin P A M s x) :
    (∑ x ∈ S, nu x)
      ≤ (M / a) ^ s * (collisionProbability P A a nu / (1 - a)) := by
  have hpow : (0 : ℝ) < (M / a) ^ s := by
    have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
    positivity
  have hbase := measure_reachable_inter_le hP hrow ha ha1 hM nu hnu Finset.univ S
    (Finset.subset_univ S) hS
  refine le_trans hbase (mul_le_mul_of_nonneg_left ?_ hpow.le)
  exact hitting_le_collision_div hP hrow ha.le ha1 hnu hnusum

/-- **`(11bq)`.**  Conversely the collision probability is at least `(1-a)(a/M)^s` times the
complete-union mass. -/
theorem collision_ge_measure {P : Matrix X X ℝ} {A : Finset X} {a : ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 < a) (ha1 : a < 1)
    {M : ℝ} (hM : 1 ≤ M) {s : ℕ}
    {nu : X → ℝ} (hnu : ∀ x, 0 ≤ nu x) (hnusum : ∑ x, nu x = 1)
    (S : Finset X) (hS : ∀ x ∈ S, ReachableWithin P A M s x) :
    (1 - a) * ((a / M) ^ s * ∑ x ∈ S, nu x) ≤ collisionProbability P A a nu := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hden : (0 : ℝ) < 1 - a := by linarith
  have hkey := measure_reachable_le_collision hP hrow ha ha1 hM hnu hnusum S hS
  have hinv : (a / M) ^ s * (M / a) ^ s = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm a M, div_self (by positivity), one_pow]
  have hpow : (0 : ℝ) < (a / M) ^ s := by positivity
  have hstep : (a / M) ^ s * ∑ x ∈ S, nu x
      ≤ collisionProbability P A a nu / (1 - a) := by
    have := mul_le_mul_of_nonneg_left hkey hpow.le
    calc (a / M) ^ s * ∑ x ∈ S, nu x
        ≤ (a / M) ^ s * ((M / a) ^ s * (collisionProbability P A a nu / (1 - a))) := this
      _ = collisionProbability P A a nu / (1 - a) := by
          rw [← mul_assoc, hinv, one_mul]
  rw [← le_div_iff₀' hden]
  exact hstep

/-! ## The optimal fugacity -/

/-- **`(11ax)`, optimality.**  `a ↦ a^s(1-a)` is maximized at `a = s/(s+1)`, so `a^{-s}/(1-a)` is
minimized there. -/
theorem pow_mul_one_sub_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) {s : ℕ} (hs : 1 ≤ s) :
    a ^ s * (1 - a) ≤ ((s : ℝ) / (s + 1)) ^ s * (1 / ((s : ℝ) + 1)) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (0 : ℝ) < (s : ℝ) + 1 := by linarith
  obtain ⟨u, hudef⟩ : ∃ u, u = ((s : ℝ) + 1) * a / s := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v, v = ((s : ℝ) + 1) * (1 - a) := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hudef]; positivity
  have hv0 : 0 ≤ v := by rw [hvdef]; nlinarith
  have hsum : (s : ℝ) * u + v = (s : ℝ) + 1 := by
    rw [hudef, hvdef]
    field_simp
    ring
  have hub : u ^ s ≤ Real.exp ((s : ℝ) * (u - 1)) := by
    have h1 : u ≤ Real.exp (u - 1) := by
      have := Real.add_one_le_exp (u - 1)
      linarith
    calc u ^ s ≤ (Real.exp (u - 1)) ^ s := pow_le_pow_left₀ hu0 h1 s
      _ = Real.exp ((s : ℝ) * (u - 1)) := by
          rw [← Real.exp_nat_mul]
  have hvb : v ≤ Real.exp (v - 1) := by
    have := Real.add_one_le_exp (v - 1)
    linarith
  have hprod : u ^ s * v ≤ 1 := by
    calc u ^ s * v ≤ Real.exp ((s : ℝ) * (u - 1)) * Real.exp (v - 1) :=
          mul_le_mul hub hvb hv0 (Real.exp_pos _).le
      _ = Real.exp ((s : ℝ) * (u - 1) + (v - 1)) := by rw [← Real.exp_add]
      _ = Real.exp 0 := by
          congr 1
          nlinarith [hsum]
      _ = 1 := Real.exp_zero
  have hu : u = a * (((s : ℝ) + 1) / (s : ℝ)) := by rw [hudef]; ring
  have hv : v = (1 - a) * ((s : ℝ) + 1) := by rw [hvdef]; ring
  have hcancel : ((s : ℝ) / ((s : ℝ) + 1)) * (((s : ℝ) + 1) / (s : ℝ)) = 1 := by
    field_simp
  have hexpand : ((s : ℝ) / ((s : ℝ) + 1)) ^ s * (1 / ((s : ℝ) + 1)) * (u ^ s * v)
      = a ^ s * (1 - a) := by
    rw [hu, hv, mul_pow]
    calc ((s : ℝ) / ((s : ℝ) + 1)) ^ s * (1 / ((s : ℝ) + 1)) *
          (a ^ s * ((((s : ℝ) + 1) / (s : ℝ)) ^ s) * ((1 - a) * ((s : ℝ) + 1)))
        = (((s : ℝ) / ((s : ℝ) + 1)) * ((((s : ℝ) + 1) / (s : ℝ)))) ^ s *
            ((1 / ((s : ℝ) + 1)) * ((s : ℝ) + 1)) * (a ^ s * (1 - a)) := by
          rw [mul_pow]; ring
      _ = a ^ s * (1 - a) := by
          rw [hcancel, one_pow, one_div, inv_mul_cancel₀ (ne_of_gt hs1)]
          ring
  have hC : (0 : ℝ) ≤ ((s : ℝ) / ((s : ℝ) + 1)) ^ s * (1 / ((s : ℝ) + 1)) := by positivity
  calc a ^ s * (1 - a)
      = ((s : ℝ) / ((s : ℝ) + 1)) ^ s * (1 / ((s : ℝ) + 1)) * (u ^ s * v) := hexpand.symm
    _ ≤ ((s : ℝ) / ((s : ℝ) + 1)) ^ s * (1 / ((s : ℝ) + 1)) * 1 :=
        mul_le_mul_of_nonneg_left hprod hC
    _ = ((s : ℝ) / ((s : ℝ) + 1)) ^ s * (1 / ((s : ℝ) + 1)) := by ring

/-- `(1+1/s)^s ≤ e`. -/
theorem one_add_inv_pow_le_exp_one {s : ℕ} (hs : 1 ≤ s) :
    (1 + 1 / (s : ℝ)) ^ s ≤ Real.exp 1 := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have h1 : (1 : ℝ) + 1 / (s : ℝ) ≤ Real.exp (1 / (s : ℝ)) := by
    have := Real.add_one_le_exp (1 / (s : ℝ))
    linarith
  calc (1 + 1 / (s : ℝ)) ^ s ≤ (Real.exp (1 / (s : ℝ))) ^ s :=
        pow_le_pow_left₀ (by positivity) h1 s
    _ = Real.exp ((s : ℝ) * (1 / (s : ℝ))) := by rw [← Real.exp_nat_mul]
    _ = Real.exp 1 := by rw [mul_one_div, div_self (ne_of_gt hs0)]


/-- **`(11ay)`.**  At the optimal fugacity `a_s = s/(s+1)` the complete depth-`s` circuit union
costs only `e(s+1)M^s` times the uniform per-step target bound. -/
theorem measure_reachable_le_optimal {P : Matrix X X ℝ} {A : Finset X} {B : ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    {M : ℝ} (hM : 1 ≤ M) {s : ℕ} (hs : 1 ≤ s)
    {nu : X → ℝ} (hnu : ∀ x, 0 ≤ nu x) (hnusum : ∑ x, nu x = 1)
    (hB : ∀ n : ℕ, lawTargetMass ((lawPush P)^[n] nu) A ≤ B)
    (Sfin : Finset X) (hS : ∀ x ∈ Sfin, ReachableWithin P A M s x) :
    (∑ x ∈ Sfin, nu x) ≤ Real.exp 1 * (((s : ℝ) + 1) * (M ^ s * B)) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (0 : ℝ) < (s : ℝ) + 1 := by linarith
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hB0 : 0 ≤ B := by
    refine le_trans ?_ (hB 0)
    simpa [lawTargetMass] using Finset.sum_nonneg (fun x (_ : x ∈ A) => hnu x)
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = (s : ℝ) / ((s : ℝ) + 1) := ⟨_, rfl⟩
  have hapos : 0 < a := by rw [hadef]; positivity
  have halt : a < 1 := by
    rw [hadef, div_lt_one hs1]
    linarith
  have hone : 1 - a = 1 / ((s : ℝ) + 1) := by
    rw [hadef]
    field_simp
    ring
  have hbase := measure_reachable_le_of_uniform hP hrow hapos halt hM hnu hnusum hB Sfin hS
  have hMa : M / a = M * (1 + 1 / (s : ℝ)) := by
    rw [hadef]
    field_simp
  have heq : B / (1 - a) * (M / a) ^ s
      = ((s : ℝ) + 1) * (M ^ s * ((1 + 1 / (s : ℝ)) ^ s * B)) := by
    rw [hone, hMa, mul_pow]
    field_simp
  have hpow := one_add_inv_pow_le_exp_one hs
  have hstep : ((s : ℝ) + 1) * (M ^ s * ((1 + 1 / (s : ℝ)) ^ s * B))
      ≤ Real.exp 1 * (((s : ℝ) + 1) * (M ^ s * B)) := by
    have hinner : (1 + 1 / (s : ℝ)) ^ s * B ≤ Real.exp 1 * B :=
      mul_le_mul_of_nonneg_right hpow hB0
    calc ((s : ℝ) + 1) * (M ^ s * ((1 + 1 / (s : ℝ)) ^ s * B))
        ≤ ((s : ℝ) + 1) * (M ^ s * (Real.exp 1 * B)) := by
          refine mul_le_mul_of_nonneg_left ?_ hs1.le
          exact mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = Real.exp 1 * (((s : ℝ) + 1) * (M ^ s * B)) := by ring
  calc (∑ x ∈ Sfin, nu x) ≤ B / (1 - a) * (M / a) ^ s := hbase
    _ = ((s : ℝ) + 1) * (M ^ s * ((1 + 1 / (s : ℝ)) ^ s * B)) := heq
    _ ≤ Real.exp 1 * (((s : ℝ) + 1) * (M ^ s * B)) := hstep

end

end GaloisForLFunctions.HTGeometry
