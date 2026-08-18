import GaloisForLFunctions.HTGeometry.ObserverComplementOrderParameter

/-!
# The renewal-linearised occupation potential of a finite chain

The discounted occupation operator `f ↦ 1_A + a P f` is the linear reporter attached to a target
set: it adds one unit of charge on every visit to the target rather than stopping there.  Like the
first-entrance operator it is an `a`-contraction of the sup norm, so it has a unique fixed point
`g_{A,a}`, and that fixed point is the Neumann sum `∑_ℓ a^ℓ P^ℓ 1_A` in disguise.

Comparing the two fixed points is what linearises a first-entrance estimate.  A monotone
contraction lies above each of its subsolutions and below each of its supersolutions, and both
`g_{A,a}` and `(1-a) g_{A,a}` are comparable with the first-entrance operator in that sense; the
two comparisons give the sandwich `(1-a) g_{A,a} ≤ h_A ≤ g_{A,a}` with no path space, hitting time
or renewal decomposition.  Every first-entrance bound therefore transfers to the linear reporter at
the cost of one factor `1-a`, and averaging against a law turns the transferred bound into a
two-sided estimate for the reporter `Z_a(ν,A) = ∑_x ν(x) g_{A,a}(x)`.

The reporter is linear in the target indicator, so it also diagonalises: against a stationary law
its total mass is `π(A)/(1-a)`, and against an eigenvector of a self-adjoint chain its pairing is
the source pairing divided by `1 - aλ`.
-/

open scoped BigOperators NNReal
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Comparison

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- **A subsolution of a monotone contraction lies below its fixed point.** -/
theorem le_fixedPoint_of_le_map {K : ℝ≥0} {T : (X → ℝ) → (X → ℝ)} (hT : ContractingWith K T)
    (hmono : ∀ f g : X → ℝ, (∀ x, f x ≤ g x) → ∀ x, T f x ≤ T g x)
    {f : X → ℝ} (hf : ∀ x, f x ≤ T f x) (x : X) :
    f x ≤ ContractingWith.fixedPoint T hT x := by
  have hiter : ∀ n : ℕ, ∀ y : X, f y ≤ T^[n] f y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
        intro y
        have hstep : T f y ≤ T (T^[n] f) y := hmono f (T^[n] f) ih y
        rw [Function.iterate_succ_apply']
        exact le_trans (hf y) hstep
  have htend : Tendsto (fun n : ℕ => T^[n] f) atTop (𝓝 (ContractingWith.fixedPoint T hT)) :=
    hT.tendsto_iterate_fixedPoint f
  have hpt : Tendsto (fun n : ℕ => T^[n] f x) atTop (𝓝 (ContractingWith.fixedPoint T hT x)) :=
    (tendsto_pi_nhds.mp htend) x
  exact ge_of_tendsto' hpt (fun n => hiter n x)

/-- **A supersolution of a monotone contraction lies above its fixed point.** -/
theorem fixedPoint_le_of_map_le {K : ℝ≥0} {T : (X → ℝ) → (X → ℝ)} (hT : ContractingWith K T)
    (hmono : ∀ f g : X → ℝ, (∀ x, f x ≤ g x) → ∀ x, T f x ≤ T g x)
    {f : X → ℝ} (hf : ∀ x, T f x ≤ f x) (x : X) :
    ContractingWith.fixedPoint T hT x ≤ f x := by
  have hiter : ∀ n : ℕ, ∀ y : X, T^[n] f y ≤ f y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
        intro y
        rw [Function.iterate_succ_apply']
        exact le_trans (hmono (T^[n] f) f ih y) (hf y)
  have htend : Tendsto (fun n : ℕ => T^[n] f) atTop (𝓝 (ContractingWith.fixedPoint T hT)) :=
    hT.tendsto_iterate_fixedPoint f
  have hpt : Tendsto (fun n : ℕ => T^[n] f x) atTop (𝓝 (ContractingWith.fixedPoint T hT x)) :=
    (tendsto_pi_nhds.mp htend) x
  exact le_of_tendsto' hpt (fun n => hiter n x)

/-- The first-entrance operator is monotone. -/
theorem hittingMap_mono {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y) {A : Finset X} {a : ℝ}
    (ha : 0 ≤ a) (f g : X → ℝ) (hfg : ∀ x, f x ≤ g x) (x : X) :
    hittingMap P A a f x ≤ hittingMap P A a g x := by
  simp only [hittingMap]
  split_ifs
  · exact le_rfl
  · refine mul_le_mul_of_nonneg_left ?_ ha
    exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hfg y) (hP x y)

end Comparison

section Occupation

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- **`(11bc)`.**  The discounted occupation operator of a target set: one unit of charge on every
visit to the target, discounted by `a` per step. -/
def occupationMap (P : Matrix X X ℝ) (A : Finset X) (a : ℝ) (f : X → ℝ) : X → ℝ :=
  fun x => (if x ∈ A then 1 else 0) + a * ∑ y, P x y * f y

/-- **The occupation operator is an `a`-contraction of the sup norm.** -/
theorem lipschitzWith_occupationMap {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) {A : Finset X} {a : ℝ} (ha : 0 ≤ a) :
    LipschitzWith ⟨a, ha⟩ (occupationMap P A a) := by
  refine LipschitzWith.of_dist_le_mul fun f g => ?_
  rw [dist_pi_le_iff (by positivity)]
  intro x
  simp only [occupationMap]
  rw [Real.dist_eq]
  have hEq : ((if x ∈ A then (1 : ℝ) else 0) + a * ∑ y, P x y * f y)
      - ((if x ∈ A then (1 : ℝ) else 0) + a * ∑ y, P x y * g y)
      = a * ∑ y, (P x y * f y - P x y * g y) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hEq, abs_mul, abs_of_nonneg ha]
  have hterm : ∀ y, |P x y * f y - P x y * g y| ≤ P x y * dist f g := by
    intro y
    rw [← mul_sub, abs_mul, abs_of_nonneg (hP x y)]
    refine mul_le_mul_of_nonneg_left ?_ (hP x y)
    rw [← Real.dist_eq]
    exact dist_le_pi_dist f g y
  have hbound : |∑ y, (P x y * f y - P x y * g y)| ≤ dist f g := by
    calc |∑ y, (P x y * f y - P x y * g y)| ≤ ∑ y, |P x y * f y - P x y * g y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, P x y * dist f g := Finset.sum_le_sum fun y _ => hterm y
      _ = dist f g := by rw [← Finset.sum_mul, hrow x, one_mul]
  calc a * |∑ y, (P x y * f y - P x y * g y)| ≤ a * dist f g :=
        mul_le_mul_of_nonneg_left hbound ha
    _ = ↑(⟨a, ha⟩ : ℝ≥0) * dist f g := by norm_num

/-- The occupation operator contracts. -/
theorem occupationContracting (P : Matrix X X ℝ) (A : Finset X) (a : ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1) :
    ContractingWith ⟨a, ha⟩ (occupationMap P A a) :=
  ⟨by exact_mod_cast ha1, lipschitzWith_occupationMap hP hrow ha⟩

/-- **`(11bc)`.**  The discounted occupation potential: the unique fixed point of the occupation
operator, that is the Neumann sum `∑_ℓ a^ℓ P^ℓ 1_A`. -/
def occupationPotential (P : Matrix X X ℝ) (A : Finset X) (a : ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1) : X → ℝ :=
  ContractingWith.fixedPoint (occupationMap P A a) (occupationContracting P A a hP hrow ha ha1)

theorem occupationPotential_fixed (P : Matrix X X ℝ) (A : Finset X) (a : ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1) :
    occupationMap P A a (occupationPotential P A a hP hrow ha ha1)
      = occupationPotential P A a hP hrow ha ha1 :=
  ContractingWith.fixedPoint_isFixedPt (occupationContracting P A a hP hrow ha ha1)

/-- **`(11bc)`, resolvent form.**  The occupation potential solves `(I - aP) g = 1_A`. -/
theorem occupationPotential_apply {P : Matrix X X ℝ} {A : Finset X} {a : ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1) (x : X) :
    occupationPotential P A a hP hrow ha ha1 x
      = (if x ∈ A then 1 else 0)
        + a * ∑ y, P x y * occupationPotential P A a hP hrow ha ha1 y := by
  conv_lhs => rw [← occupationPotential_fixed P A a hP hrow ha ha1]
  simp only [occupationMap]

/-- The occupation operator is monotone. -/
theorem occupationMap_mono {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y) {A : Finset X} {a : ℝ}
    (ha : 0 ≤ a) (f g : X → ℝ) (hfg : ∀ x, f x ≤ g x) (x : X) :
    occupationMap P A a f x ≤ occupationMap P A a g x := by
  simp only [occupationMap]
  have hstep : a * ∑ y, P x y * f y ≤ a * ∑ y, P x y * g y :=
    mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hfg y) (hP x y)) ha
  linarith

/-- **The occupation potential lies between zero and the geometric ceiling `(1-a)⁻¹`.** -/
theorem occupationPotential_bounds {P : Matrix X X ℝ} {A : Finset X} {a : ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1) (x : X) :
    0 ≤ occupationPotential P A a hP hrow ha ha1 x ∧
      occupationPotential P A a hP hrow ha ha1 x ≤ (1 - a)⁻¹ := by
  classical
  have hden : (0 : ℝ) < 1 - a := by linarith
  set S : Set (X → ℝ) := {f | ∀ y, 0 ≤ f y ∧ f y ≤ (1 - a)⁻¹} with hS
  have hclosed : IsClosed S := by
    have hrepr : S = ⋂ y : X, {f : X → ℝ | 0 ≤ f y} ∩ {f : X → ℝ | f y ≤ (1 - a)⁻¹} := by
      ext f
      simp [hS, Set.mem_iInter]
    rw [hrepr]
    refine isClosed_iInter fun y => IsClosed.inter ?_ ?_
    · exact isClosed_le continuous_const (continuous_apply y)
    · exact isClosed_le (continuous_apply y) continuous_const
  have hinv : ∀ f ∈ S, occupationMap P A a f ∈ S := by
    intro f hf y
    have hnn : 0 ≤ ∑ z, P y z * f z :=
      Finset.sum_nonneg fun z _ => mul_nonneg (hP y z) (hf z).1
    have hle : ∑ z, P y z * f z ≤ (1 - a)⁻¹ := by
      calc ∑ z, P y z * f z ≤ ∑ z, P y z * (1 - a)⁻¹ :=
            Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hf z).2 (hP y z)
        _ = (1 - a)⁻¹ := by rw [← Finset.sum_mul, hrow y, one_mul]
    have hind : (0 : ℝ) ≤ (if y ∈ A then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have hind1 : (if y ∈ A then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
    have hceil : 1 + a * (1 - a)⁻¹ = (1 - a)⁻¹ := by
      field_simp
      ring
    refine ⟨?_, ?_⟩
    · simp only [occupationMap]
      have : 0 ≤ a * ∑ z, P y z * f z := mul_nonneg ha hnn
      linarith
    · simp only [occupationMap]
      have hstep : a * ∑ z, P y z * f z ≤ a * (1 - a)⁻¹ :=
        mul_le_mul_of_nonneg_left hle ha
      linarith
  have hzero : (fun _ : X => (0 : ℝ)) ∈ S := fun y => ⟨le_rfl, by positivity⟩
  have hiter : ∀ n : ℕ, (occupationMap P A a)^[n] (fun _ : X => (0 : ℝ)) ∈ S := by
    intro n
    induction n with
    | zero => exact hzero
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hinv _ ih
  have htend := ContractingWith.tendsto_iterate_fixedPoint
    (occupationContracting P A a hP hrow ha ha1) (fun _ : X => (0 : ℝ))
  have hmem : occupationPotential P A a hP hrow ha ha1 ∈ S :=
    hclosed.mem_of_tendsto htend (Filter.Eventually.of_forall hiter)
  exact hmem x

end Occupation

section Sandwich

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- **`(11bd)`, upper half.**  The first-entrance potential is dominated by the occupation
potential: the occupation potential is a supersolution of the first-entrance operator. -/
theorem hittingPotential_le_occupationPotential {P : Matrix X X ℝ} {A : Finset X} {a : ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1) (x : X) :
    hittingPotential P A a hP hrow ha ha1 x ≤ occupationPotential P A a hP hrow ha ha1 x := by
  classical
  refine fixedPoint_le_of_map_le (hittingContracting P A a hP hrow ha ha1)
    (hittingMap_mono hP ha) ?_ x
  intro y
  have hval := occupationPotential_apply (A := A) hP hrow ha ha1 y
  by_cases hy : y ∈ A
  · rw [hittingMap_apply_mem _ hy, hval, if_pos hy]
    have hnn : 0 ≤ ∑ z, P y z * occupationPotential P A a hP hrow ha ha1 z :=
      Finset.sum_nonneg fun z _ =>
        mul_nonneg (hP y z) (occupationPotential_bounds (A := A) hP hrow ha ha1 z).1
    nlinarith [mul_nonneg ha hnn]
  · rw [hittingMap_apply_notMem _ hy]
    conv_rhs => rw [hval, if_neg hy]
    simp

/-- **`(11bd)`, lower half.**  Shrinking the occupation potential by the discount gap produces a
subsolution of the first-entrance operator, so `(1-a) g_{A,a} ≤ h_A`. -/
theorem one_sub_mul_occupationPotential_le_hittingPotential {P : Matrix X X ℝ} {A : Finset X}
    {a : ℝ} (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1)
    (x : X) :
    (1 - a) * occupationPotential P A a hP hrow ha ha1 x
      ≤ hittingPotential P A a hP hrow ha ha1 x := by
  classical
  have hden : (0 : ℝ) < 1 - a := by linarith
  refine le_fixedPoint_of_le_map (hittingContracting P A a hP hrow ha ha1)
    (hittingMap_mono hP ha)
    (f := fun y => (1 - a) * occupationPotential P A a hP hrow ha ha1 y) ?_ x
  intro y
  have hval := occupationPotential_apply (A := A) hP hrow ha ha1 y
  by_cases hy : y ∈ A
  · rw [hittingMap_apply_mem _ hy]
    have hup := (occupationPotential_bounds (A := A) hP hrow ha ha1 y).2
    have : (1 - a) * occupationPotential P A a hP hrow ha ha1 y ≤ (1 - a) * (1 - a)⁻¹ :=
      mul_le_mul_of_nonneg_left hup hden.le
    rwa [mul_inv_cancel₀ (ne_of_gt hden)] at this
  · rw [hittingMap_apply_notMem _ hy]
    have hfree : occupationPotential P A a hP hrow ha ha1 y
        = a * ∑ z, P y z * occupationPotential P A a hP hrow ha ha1 z := by
      rw [hval, if_neg hy, zero_add]
    rw [hfree]
    have hpull : ∑ z, P y z * ((1 - a) * occupationPotential P A a hP hrow ha ha1 z)
        = (1 - a) * ∑ z, P y z * occupationPotential P A a hP hrow ha ha1 z := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [hpull]
    ring_nf
    exact le_rfl

end Sandwich

section Transfer

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- **`(11bi)`, lower half.**  One witness word of length at most `s` charges the occupation
potential by at least `(a/M)^s`. -/
theorem le_occupationPotential_of_reach {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) {A : Finset X} {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {M : ℝ}
    (hM : 1 ≤ M) {s : ℕ} {x : X} (hx : ReachableWithin P A M s x) :
    (a / M) ^ s ≤ occupationPotential P A a hP hrow ha.le ha1 x := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hratio0 : (0 : ℝ) ≤ a / M := div_nonneg ha.le hM0.le
  have hratio1 : a / M ≤ 1 := by
    rw [div_le_one hM0]; linarith
  obtain ⟨k, hks, path, hpath0, hlast, hstep⟩ := hx
  have hbase := le_hittingPotential_of_path hP hrow ha.le ha1 hM k path hlast hstep
  rw [hpath0] at hbase
  have hmono : (a / M) ^ s ≤ (a / M) ^ k := pow_le_pow_of_le_one hratio0 hratio1 hks
  exact le_trans (le_trans hmono hbase)
    (hittingPotential_le_occupationPotential hP hrow ha.le ha1 x)

/-- **`(11bi)`, upper half.**  A state from which no successful word is shorter than `k` has
occupation potential at most `a^{k+1}/(1-a)`. -/
theorem occupationPotential_le_pow_div {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) {A : Finset X} {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (k : ℕ)
    {x : X} (hx : ¬ PositiveReach P A k x) :
    occupationPotential P A a hP hrow ha ha1 x ≤ a ^ (k + 1) / (1 - a) := by
  have hden : (0 : ℝ) < 1 - a := by linarith
  have hlow := one_sub_mul_occupationPotential_le_hittingPotential (A := A) hP hrow ha ha1 x
  have hup := hittingPotential_le_pow hP hrow ha ha1 k x hx
  rw [le_div_iff₀ hden, mul_comm]
  linarith

end Transfer

section Reporter

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- **`(11bh)`.**  Averaging the sandwich against a law bounds the first-entrance mass by the
linear reporter `Z_a(ν,A) = ∑_x ν(x) g_{A,a}(x)` from both sides. -/
theorem reporter_sandwich {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) {A : Finset X} {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (nu : X → ℝ) (hnu : ∀ x, 0 ≤ nu x) :
    (1 - a) * (∑ x, nu x * occupationPotential P A a hP hrow ha ha1 x)
        ≤ ∑ x, nu x * hittingPotential P A a hP hrow ha ha1 x ∧
      ∑ x, nu x * hittingPotential P A a hP hrow ha ha1 x
        ≤ ∑ x, nu x * occupationPotential P A a hP hrow ha ha1 x := by
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have h := one_sub_mul_occupationPotential_le_hittingPotential (A := A) hP hrow ha ha1 x
    calc (1 - a) * (nu x * occupationPotential P A a hP hrow ha ha1 x)
        = nu x * ((1 - a) * occupationPotential P A a hP hrow ha ha1 x) := by ring
      _ ≤ nu x * hittingPotential P A a hP hrow ha ha1 x :=
          mul_le_mul_of_nonneg_left h (hnu x)
  · refine Finset.sum_le_sum fun x _ => ?_
    exact mul_le_mul_of_nonneg_left
      (hittingPotential_le_occupationPotential hP hrow ha ha1 x) (hnu x)

/-- **`(11bj)`.**  The mass of the states reachable within `s` steps is at most `(M/a)^s` times the
linear reporter.  No capacity budget and no Bellman remainder appear: the reporter absorbs both. -/
theorem measure_reachable_le_reporter {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) {A : Finset X} {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {M : ℝ}
    (hM : 1 ≤ M) {s : ℕ} (nu : X → ℝ) (hnu : ∀ x, 0 ≤ nu x) (S : Finset X)
    (hS : ∀ x ∈ S, ReachableWithin P A M s x) :
    ∑ x ∈ S, nu x
      ≤ (M / a) ^ s * ∑ x, nu x * occupationPotential P A a hP hrow ha.le ha1 x := by
  classical
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hpow : (0 : ℝ) < (M / a) ^ s := by positivity
  have hinv : (M / a) ^ s * (a / M) ^ s = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm M a, div_self (by positivity), one_pow]
  have hind : ∀ x ∈ S,
      nu x ≤ (M / a) ^ s * (nu x * occupationPotential P A a hP hrow ha.le ha1 x) := by
    intro x hx
    have hbase := le_occupationPotential_of_reach hP hrow ha ha1 hM (hS x hx)
    calc nu x = nu x * ((M / a) ^ s * (a / M) ^ s) := by rw [hinv]; ring
      _ ≤ nu x * ((M / a) ^ s * occupationPotential P A a hP hrow ha.le ha1 x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbase hpow.le) (hnu x)
      _ = (M / a) ^ s * (nu x * occupationPotential P A a hP hrow ha.le ha1 x) := by ring
  have hSsum : ∑ x ∈ S, nu x
      ≤ (M / a) ^ s * ∑ x ∈ S, nu x * occupationPotential P A a hP hrow ha.le ha1 x := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hind
  refine le_trans hSsum (mul_le_mul_of_nonneg_left ?_ hpow.le)
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun x _ _ =>
    mul_nonneg (hnu x) (occupationPotential_bounds (A := A) hP hrow ha.le ha1 x).1

/-- **`(11bk)`.**  Equivalently, a reachable set of mass `p` forces the reporter to be at least
`p (a/M)^s`: a small reporter certifies that the fast-return set is thin. -/
theorem reporter_ge_of_measure {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) {A : Finset X} {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {M : ℝ}
    (hM : 1 ≤ M) {s : ℕ} (nu : X → ℝ) (hnu : ∀ x, 0 ≤ nu x) (S : Finset X)
    (hS : ∀ x ∈ S, ReachableWithin P A M s x) :
    (∑ x ∈ S, nu x) * (a / M) ^ s
      ≤ ∑ x, nu x * occupationPotential P A a hP hrow ha.le ha1 x := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hratio : (0 : ℝ) < a / M := div_pos ha hM0
  have hmain := measure_reachable_le_reporter hP hrow ha ha1 hM nu hnu S hS
  have hinv : (M / a) ^ s * (a / M) ^ s = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm M a, div_self (by positivity), one_pow]
  calc (∑ x ∈ S, nu x) * (a / M) ^ s
      ≤ ((M / a) ^ s * ∑ x, nu x * occupationPotential P A a hP hrow ha.le ha1 x)
          * (a / M) ^ s := by
        exact mul_le_mul_of_nonneg_right hmain (by positivity)
    _ = ∑ x, nu x * occupationPotential P A a hP hrow ha.le ha1 x := by
        rw [mul_comm ((M / a) ^ s), mul_assoc, hinv, mul_one]

end Reporter

section Spectral

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- **`(11bl)`, eigenvector form.**  Against an eigenvector of a chain that is self-adjoint for the
weight `pi`, the reporter pairing is the source pairing divided by `1 - aλ`. -/
theorem sum_weighted_occupationPotential_eigen {P : Matrix X X ℝ} {A : Finset X} {a : ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1)
    (pi phi : X → ℝ) {lam : ℝ}
    (hsa : ∀ f k : X → ℝ, ∑ x, pi x * (∑ y, P x y * f y) * k x
      = ∑ x, pi x * f x * (∑ y, P x y * k y))
    (heig : ∀ x, ∑ y, P x y * phi y = lam * phi x) :
    ∑ x, pi x * (if x ∈ A then (1 : ℝ) else 0) * phi x
      = (1 - a * lam) * ∑ x, pi x * occupationPotential P A a hP hrow ha ha1 x * phi x := by
  classical
  set g := occupationPotential P A a hP hrow ha ha1 with hg
  have hsource : ∀ x, (if x ∈ A then (1 : ℝ) else 0) = g x - a * ∑ y, P x y * g y := by
    intro x
    have := occupationPotential_apply (A := A) hP hrow ha ha1 x
    rw [hg]
    linarith [this]
  have hsplit : ∑ x, pi x * (if x ∈ A then (1 : ℝ) else 0) * phi x
      = (∑ x, pi x * g x * phi x) - a * ∑ x, pi x * (∑ y, P x y * g y) * phi x := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hsource x]
    ring
  have hself : ∑ x, pi x * (∑ y, P x y * g y) * phi x
      = lam * ∑ x, pi x * g x * phi x := by
    rw [hsa g phi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [heig x]
    ring
  rw [hsplit, hself]
  ring

/-- **`(11bl)`, total-mass form.**  Against a stationary law the reporter has total mass
`π(A)/(1-a)`. -/
theorem sum_stationary_occupationPotential {P : Matrix X X ℝ} {A : Finset X} {a : ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (ha : 0 ≤ a) (ha1 : a < 1)
    (pi : X → ℝ) (hstat : ∀ y, ∑ x, pi x * P x y = pi y) :
    ∑ x ∈ A, pi x = (1 - a) * ∑ x, pi x * occupationPotential P A a hP hrow ha ha1 x := by
  classical
  set g := occupationPotential P A a hP hrow ha ha1 with hg
  have hswap : ∑ x, pi x * (∑ y, P x y * g y) = ∑ y, pi y * g y := by
    have h1 : ∀ x : X, pi x * (∑ y, P x y * g y) = ∑ y, pi x * P x y * g y := by
      intro x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    have h2 : ∀ y : X, (∑ x, pi x * P x y) * g y = ∑ x, pi x * P x y * g y := by
      intro y
      rw [Finset.sum_mul]
    have hstep : ∑ x, pi x * (∑ y, P x y * g y) = ∑ y, (∑ x, pi x * P x y) * g y := by
      simp_rw [h1, h2]
      exact Finset.sum_comm
    rw [hstep]
    exact Finset.sum_congr rfl fun y _ => by rw [hstat y]
  have hsource : ∀ x, (if x ∈ A then (1 : ℝ) else 0) = g x - a * ∑ y, P x y * g y := by
    intro x
    have := occupationPotential_apply (A := A) hP hrow ha ha1 x
    rw [hg]
    linarith [this]
  have hind : ∑ x ∈ A, pi x = ∑ x, pi x * (if x ∈ A then (1 : ℝ) else 0) := by
    have hpt : ∀ x : X, pi x * (if x ∈ A then (1 : ℝ) else 0)
        = if x ∈ A then pi x else 0 := by
      intro x
      split_ifs <;> ring
    simp_rw [hpt]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hind]
  have hsplit : ∑ x, pi x * (if x ∈ A then (1 : ℝ) else 0)
      = (∑ x, pi x * g x) - a * ∑ x, pi x * (∑ y, P x y * g y) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hsource x]
    ring
  rw [hsplit, hswap]
  ring

end Spectral

end

end GaloisForLFunctions.HTGeometry
