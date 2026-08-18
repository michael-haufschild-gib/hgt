import GaloisForLFunctions.HTGeometry.DiscountedHittingPotential

/-!
# The observer-excised complete circuit union

A word of length at most `s` driving the inverse gate walk from a state into the target tube gives
that state discounted path mass at least `(a/M)^s`, so the indicator of the low-complexity event is
dominated by `(M/a)^s` times the discounted first-entrance potential.  Integrating against an
arbitrary endpoint law and splitting the potential into its observer part and the high-mode
remainder bounds the whole low-complexity mass by the target capacity term plus the positive part
of that remainder.  No total-variation, chi-square, design or Haar-mixing distance of the endpoint
law occurs anywhere.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Reach

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- A discounted path of length at most `s` from a state into the target, each step of which has
transition probability at least `1/M`. -/
def ReachableWithin (P : Matrix X X ℝ) (A : Finset X) (M : ℝ) (s : ℕ) (x : X) : Prop :=
  ∃ k ≤ s, ∃ path : ℕ → X, path 0 = x ∧ path k ∈ A ∧
    ∀ i < k, (1 : ℝ) / M ≤ P (path i) (path (i + 1))

/-- **The discounted path mass of one witness word.**  A `k`-step path into the target with steps
of probability at least `1/M` gives the potential at least `(a/M)^k`. -/
theorem le_hittingPotential_of_path
    {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    {A : Finset X} {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) {M : ℝ} (hM : 1 ≤ M) :
    ∀ (k : ℕ) (path : ℕ → X), path k ∈ A →
      (∀ i < k, (1 : ℝ) / M ≤ P (path i) (path (i + 1))) →
      (a / M) ^ k ≤ hittingPotential P A a hP hrow ha ha1 (path 0) := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hratio0 : (0 : ℝ) ≤ a / M := div_nonneg ha hM0.le
  have hratio1 : a / M ≤ 1 := by
    rw [div_le_one hM0]
    linarith
  intro k
  induction k with
  | zero =>
      intro path hlast _
      rw [pow_zero, hittingPotential_eq_one hP hrow ha ha1 hlast]
  | succ k ih =>
      intro path hlast hstep
      by_cases hx : path 0 ∈ A
      · rw [hittingPotential_eq_one hP hrow ha ha1 hx]
        exact pow_le_one₀ hratio0 hratio1
      · have hshift := ih (fun i => path (i + 1)) hlast
          (fun i hi => hstep (i + 1) (by omega))
        have hfix : hittingPotential P A a hP hrow ha ha1 (path 0)
            = a * ∑ y, P (path 0) y * hittingPotential P A a hP hrow ha ha1 y := by
          conv_lhs => rw [← hittingPotential_fixed P A a hP hrow ha ha1]
          rw [hittingMap_apply_notMem _ hx]
        have hsingle : P (path 0) (path 1) * hittingPotential P A a hP hrow ha ha1 (path 1) ≤
            ∑ y, P (path 0) y * hittingPotential P A a hP hrow ha ha1 y :=
          Finset.single_le_sum
            (f := fun y => P (path 0) y * hittingPotential P A a hP hrow ha ha1 y)
            (fun y _ => mul_nonneg (hP _ y)
              (hittingPotential_mem_unitInterval hP hrow ha ha1 y).1)
            (Finset.mem_univ (path 1))
        have hstep0 : (1 : ℝ) / M ≤ P (path 0) (path 1) := hstep 0 (by omega)
        have hlow : (1 : ℝ) / M * (a / M) ^ k ≤
            P (path 0) (path 1) * hittingPotential P A a hP hrow ha ha1 (path 1) := by
          refine mul_le_mul hstep0 hshift (pow_nonneg hratio0 k) (le_trans (by positivity) hstep0)
        rw [hfix]
        calc
          (a / M) ^ (k + 1) = a * ((1 : ℝ) / M * (a / M) ^ k) := by
            rw [pow_succ]
            field_simp
          _ ≤ a * (P (path 0) (path 1) * hittingPotential P A a hP hrow ha ha1 (path 1)) :=
            mul_le_mul_of_nonneg_left hlow ha
          _ ≤ a * ∑ y, P (path 0) y * hittingPotential P A a hP hrow ha ha1 y :=
            mul_le_mul_of_nonneg_left hsingle ha

/-- **`(9)`.**  A state reachable within `s` steps has potential at least `(a/M)^s`, so its
indicator is dominated by `(M/a)^s` times the potential. -/
theorem one_le_pow_mul_hittingPotential
    {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    {A : Finset X} {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {M : ℝ} (hM : 1 ≤ M)
    {s : ℕ} {x : X} (hx : ReachableWithin P A M s x) :
    1 ≤ (M / a) ^ s * hittingPotential P A a hP hrow ha.le ha1 x := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hratio0 : (0 : ℝ) < a / M := div_pos ha hM0
  have hratio1 : a / M ≤ 1 := by
    rw [div_le_one hM0]
    linarith
  obtain ⟨k, hks, path, hpath0, hlast, hstep⟩ := hx
  have hbase := le_hittingPotential_of_path hP hrow ha.le ha1 hM k path hlast hstep
  rw [hpath0] at hbase
  have hmono : (a / M) ^ s ≤ (a / M) ^ k := pow_le_pow_of_le_one hratio0.le hratio1 hks
  have hpos : (0 : ℝ) < (M / a) ^ s := by positivity
  have hinv : (M / a) ^ s * (a / M) ^ s = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm M a, div_self (by positivity), one_pow]
  calc
    (1 : ℝ) = (M / a) ^ s * (a / M) ^ s := hinv.symm
    _ ≤ (M / a) ^ s * hittingPotential P A a hP hrow ha.le ha1 x :=
      mul_le_mul_of_nonneg_left (le_trans hmono hbase) hpos.le

end Reach

section ObserverExcision

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- **Theorem B `(11)`, the observer-excised complete union.**  The endpoint mass of the states
reachable within `s` steps is bounded by the geometric factor times the target capacity term plus
the positive part of the high-mode Bellman remainder.  No distance of the endpoint law from any
reference appears. -/
theorem measure_reachable_le
    {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    {A : Finset X} {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {M : ℝ} (hM : 1 ≤ M) {s : ℕ}
    (nu : X → ℝ) (hnu : ∀ x, 0 ≤ nu x) (hnusum : ∑ x, nu x = 1)
    (S : Finset X) (hS : ∀ x ∈ S, ReachableWithin P A M s x)
    (proj : X → ℝ) {bound : ℝ}
    (hub : ∀ x, proj x ≤ bound) :
    ∑ x ∈ S, nu x ≤ (M / a) ^ s *
      (bound + max (∑ x, nu x * (hittingPotential P A a hP hrow ha.le ha1 x - proj x)) 0) := by
  classical
  have hpow : (0 : ℝ) < (M / a) ^ s := by
    have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
    positivity
  have hind : ∀ x ∈ S, nu x ≤ (M / a) ^ s * (nu x * hittingPotential P A a hP hrow ha.le ha1 x) := by
    intro x hx
    have h1 := one_le_pow_mul_hittingPotential hP hrow ha ha1 hM (hS x hx)
    calc
      nu x = nu x * 1 := by ring
      _ ≤ nu x * ((M / a) ^ s * hittingPotential P A a hP hrow ha.le ha1 x) :=
        mul_le_mul_of_nonneg_left h1 (hnu x)
      _ = (M / a) ^ s * (nu x * hittingPotential P A a hP hrow ha.le ha1 x) := by ring
  have hSsum : ∑ x ∈ S, nu x ≤
      (M / a) ^ s * ∑ x ∈ S, nu x * hittingPotential P A a hP hrow ha.le ha1 x := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hind
  have hall : ∑ x ∈ S, nu x * hittingPotential P A a hP hrow ha.le ha1 x ≤
      ∑ x, nu x * hittingPotential P A a hP hrow ha.le ha1 x := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun x _ _ =>
      mul_nonneg (hnu x) (hittingPotential_mem_unitInterval hP hrow ha.le ha1 x).1
  have hsplit : ∑ x, nu x * hittingPotential P A a hP hrow ha.le ha1 x =
      (∑ x, nu x * proj x) +
        ∑ x, nu x * (hittingPotential P A a hP hrow ha.le ha1 x - proj x) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hprojbound : ∑ x, nu x * proj x ≤ bound := by
    calc
      ∑ x, nu x * proj x ≤ ∑ x, nu x * bound :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hub x) (hnu x)
      _ = bound := by rw [← Finset.sum_mul, hnusum, one_mul]
  have hrem : ∑ x, nu x * (hittingPotential P A a hP hrow ha.le ha1 x - proj x) ≤
      max (∑ x, nu x * (hittingPotential P A a hP hrow ha.le ha1 x - proj x)) 0 :=
    le_max_left _ _
  calc
    ∑ x ∈ S, nu x ≤
        (M / a) ^ s * ∑ x ∈ S, nu x * hittingPotential P A a hP hrow ha.le ha1 x := hSsum
    _ ≤ (M / a) ^ s * ∑ x, nu x * hittingPotential P A a hP hrow ha.le ha1 x :=
      mul_le_mul_of_nonneg_left hall hpow.le
    _ ≤ (M / a) ^ s *
        (bound + max (∑ x, nu x * (hittingPotential P A a hP hrow ha.le ha1 x - proj x)) 0) := by
      refine mul_le_mul_of_nonneg_left ?_ hpow.le
      rw [hsplit]
      linarith

end ObserverExcision

end

end GaloisForLFunctions.HTGeometry
