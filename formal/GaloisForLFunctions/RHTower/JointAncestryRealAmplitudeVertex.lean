import GaloisForLFunctions.RHTower.JointAncestryRealAmplitudeCapstone
import GaloisForLFunctions.RHTower.JointAncestryPrimeCosineKernel

/-!
# Real-amplitude JAS positivity is decided at the vertices

For a finite set `P` of primes, a level `σ` and per-prime real amplitudes `t : P → ℝ` put
`K_{P,t}(s) = ∏_{p ∈ P} (1 + t_p p^{−σ} cosh((s − ½) log p))`.
Each factor is affine in `t_p`, so the zero aggregate `Re Σ_ρ K_{P,t}(ρ)/(ρ(1−ρ))` is multi-affine in
`t` and its minimum over a box sits at a vertex.

* **Constant amplitudes** (`re_tsum_jasRealTerm_eq_sum_powerset`).  For a constant amplitude `t`,
  `K_{P,t} = Σ_{S ⊆ P} t^{|S|} (1 − t)^{|P∖S|} K_{S,1}`: the aggregate is the Bernstein polynomial of
  the subset function `S ↦ Re Σ_ρ K_{S,1}(ρ)/(ρ(1−ρ))`.  So positivity for all `t ∈ [0,1]` is
  positivity at full amplitude `t = 1` on every subset (`jasRealPositiveAbove_iff_subset`).
* **Per-prime amplitudes** (`re_tsum_jasRealVecTerm_eq_sum_signs`).  For `|t_p| ≤ 1`,
  `1 + t c = ((1 + t)/2)(1 + c) + ((1 − t)/2)(1 − c)`, so the aggregate is a convex combination of
  the sign-pattern aggregates `ε ∈ {±1}^P` (`jasRealVecPositiveAbove_iff_sign`).
* **Levels** (`JasRealSubsetPositiveAbove.mono`).  Raising the level multiplies the amplitudes by
  `p^{−(σ'−σ)} ≤ 1`, so subset positivity at `σ` gives real-amplitude positivity at every `σ' ≥ σ`.
* Under RH every factor is `1 + t_p p^{−σ} cos(γ log p) ≥ 0` for `σ ≥ 0` and every weight
  `1/(ρ(1−ρ)) = 1/(¼ + γ²)` is positive, so sign-pattern positivity holds at every level `σ ≥ 0` above
  every `X` (`jasRealVecPositiveAbove_of_riemannHypothesis`).

**Capstones.**  RH holds iff the zeros approach the critical line and, above some `X`, either
* `Re Σ_ρ ∏_{p ∈ P} (1 + p^{−1} cosh((ρ − ½) log p))/(ρ(1−ρ)) ≥ 0` for every finite set `P` of primes
  `p > X` (no amplitude parameter), or
* `Re Σ_ρ ∏_{p ∈ P} (1 + ε_p p^{−1} cosh((ρ − ½) log p))/(ρ(1−ρ)) ≥ 0` for every such `P` and every
  sign pattern `ε ∈ {±1}^P`.

An attained off-line zero at distance `δ` is detected by a full-amplitude subset test at every level
`δ < σ < 1 + δ` (`not_jasRealSubsetPositiveAbove_of_maximal_offLine`).

The full-amplitude kernel is the prime cosine kernel `K_P` (`jasRealKernel_one_eq_jasCosineKernel`).
Positivity against all vertical translates `K_P(ρ − it)` is product positivity, which with a
half-plane bound below `½` is RH.  The subset form uses only the untranslated kernels `t = 0`, at the
price of the stronger side condition that the zeros approach the line.
-/

open Complex Filter
open scoped BigOperators

namespace RHTower

open BacklundConverse

noncomputable section

/-! ## Per-prime amplitudes -/

/-- The per-prime real-amplitude kernel `∏_{p ∈ P} (1 + t_p p^{−σ} cosh((s − ½) log p))`. -/
def jasRealVecKernel (P : Finset Nat.Primes) (σ : ℝ) (t : Nat.Primes → ℝ) (s : ℂ) : ℂ :=
  ∏ p ∈ P, jasRealFactor σ (t p) p s

/-- The per-prime JAS term `K_{P,t}(s)/(s(1−s))`. -/
def jasRealVecTerm (P : Finset Nat.Primes) (σ : ℝ) (t : Nat.Primes → ℝ) (s : ℂ) : ℂ :=
  jasRealVecKernel P σ t s / (s * (1 - s))

/-- The sign vector of `S`: `+1` on `S` and `−1` off `S`. -/
def jasSignVec (S : Finset Nat.Primes) (p : Nat.Primes) : ℝ := if p ∈ S then 1 else -1

/-- Positivity against every per-prime real amplitude `|t_p| ≤ 1` on primes `p > X`. -/
def JasRealVecPositiveAbove (X : ℕ) (σ : ℝ) : Prop :=
  ∀ P : Finset Nat.Primes, (∀ p ∈ P, X < (p : ℕ)) → ∀ t : Nat.Primes → ℝ, (∀ p ∈ P, |t p| ≤ 1) →
    0 ≤ (∑' q : XiZeroCopy, jasRealVecTerm P σ t (q.1 : ℂ)).re

/-- Positivity against every sign pattern `ε ∈ {±1}^P` on primes `p > X`. -/
def JasRealSignPositiveAbove (X : ℕ) (σ : ℝ) : Prop :=
  ∀ P : Finset Nat.Primes, (∀ p ∈ P, X < (p : ℕ)) → ∀ S ⊆ P,
    0 ≤ (∑' q : XiZeroCopy, jasRealVecTerm P σ (jasSignVec S) (q.1 : ℂ)).re

/-- Positivity at full amplitude `t = 1` on every finite set of primes `p > X`. -/
def JasRealSubsetPositiveAbove (X : ℕ) (σ : ℝ) : Prop :=
  ∀ P : Finset Nat.Primes, (∀ p ∈ P, X < (p : ℕ)) →
    0 ≤ (∑' q : XiZeroCopy, jasRealTerm P σ 1 (q.1 : ℂ)).re

/-! ## Affine structure -/

/-- The factor is affine in the amplitude. -/
theorem jasRealFactor_eq_affine (σ t : ℝ) (p : Nat.Primes) (s : ℂ) :
    jasRealFactor σ t p s = 1 + (t : ℂ) * (jasRealFactor σ 1 p s - 1) := by
  simp only [jasRealFactor, one_mul, add_sub_cancel_left]
  push_cast
  ring

/-- `1 + t c = ((1 + t)/2)(1 + c) + ((1 − t)/2)(1 − c)`. -/
theorem jasRealFactor_eq_signs (σ t : ℝ) (p : Nat.Primes) (s : ℂ) :
    jasRealFactor σ t p s = (((1 + t) / 2 : ℝ) : ℂ) * jasRealFactor σ 1 p s +
      (((1 - t) / 2 : ℝ) : ℂ) * jasRealFactor σ (-1) p s := by
  rw [jasRealFactor_eq_affine σ t, jasRealFactor_eq_affine σ (-1)]
  push_cast
  ring

/-- **Bernstein expansion.**  `K_{P,t} = Σ_{S ⊆ P} t^{|S|} (1 − t)^{|P∖S|} K_{S,1}`. -/
theorem jasRealKernel_eq_sum_powerset (P : Finset Nat.Primes) (σ t : ℝ) (s : ℂ) :
    jasRealKernel P σ t s = ∑ S ∈ P.powerset,
      ((t ^ S.card * (1 - t) ^ (P \ S).card : ℝ) : ℂ) * jasRealKernel S σ 1 s := by
  have h : ∀ p ∈ P, jasRealFactor σ t p s =
      (t : ℂ) * jasRealFactor σ 1 p s + ((1 - t : ℝ) : ℂ) := by
    intro p _
    rw [jasRealFactor_eq_affine]
    push_cast
    ring
  rw [jasRealKernel, Finset.prod_congr rfl h, Finset.prod_add]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const, jasRealKernel]
  push_cast
  ring

/-- The sign-pattern kernel splits into `+1` factors on `S` and `−1` factors on `P ∖ S`. -/
theorem jasRealVecKernel_sign {P S : Finset Nat.Primes} (hS : S ⊆ P) (σ : ℝ) (s : ℂ) :
    jasRealVecKernel P σ (jasSignVec S) s =
      (∏ p ∈ S, jasRealFactor σ 1 p s) * ∏ p ∈ P \ S, jasRealFactor σ (-1) p s := by
  rw [jasRealVecKernel, ← Finset.prod_sdiff hS, mul_comm]
  congr 1
  · refine Finset.prod_congr rfl fun p hp => ?_
    simp [jasSignVec, hp]
  · refine Finset.prod_congr rfl fun p hp => ?_
    simp [jasSignVec, (Finset.mem_sdiff.mp hp).2]

/-- **Sign expansion.**  For per-prime amplitudes,
`K_{P,t} = Σ_{S ⊆ P} ∏_{p ∈ S} (1 + t_p)/2 · ∏_{p ∉ S} (1 − t_p)/2 · K_{P,ε_S}`. -/
theorem jasRealVecKernel_eq_sum_signs (P : Finset Nat.Primes) (σ : ℝ) (t : Nat.Primes → ℝ)
    (s : ℂ) :
    jasRealVecKernel P σ t s = ∑ S ∈ P.powerset,
      (((∏ p ∈ S, (1 + t p) / 2) * ∏ p ∈ P \ S, (1 - t p) / 2 : ℝ) : ℂ) *
        jasRealVecKernel P σ (jasSignVec S) s := by
  rw [jasRealVecKernel, Finset.prod_congr rfl fun p _ => jasRealFactor_eq_signs σ (t p) p s,
    Finset.prod_add]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [jasRealVecKernel_sign (Finset.mem_powerset.mp hS), Finset.prod_mul_distrib,
    Finset.prod_mul_distrib]
  push_cast
  ring

/-! ## Summability -/

/-- At a zero, `‖1 + a p^{−σ} cosh((ρ − ½) log p)‖ ≤ 1 + |a| p^{−(σ−½)}`. -/
theorem norm_jasRealFactor_xiZero_le (σ a : ℝ) (p : Nat.Primes) (q : XiZeroCopy) :
    ‖jasRealFactor σ a p (q.1 : ℂ)‖ ≤ 1 + |a| * Real.exp (-(σ - 1 / 2) * Real.log p) := by
  rw [jasRealFactor_eq_affine]
  refine (norm_add_le _ _).trans ?_
  rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  refine (norm_jasRealFactor_sub_one_le zero_le_one p _).trans ?_
  rw [one_mul]
  refine Real.exp_le_exp.mpr ?_
  have hL := (log_two_le_log_prime p).trans' (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hq : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith [xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q]
  nlinarith

theorem norm_jasRealVecKernel_xiZero_le (P : Finset Nat.Primes) (σ : ℝ) (t : Nat.Primes → ℝ)
    (q : XiZeroCopy) :
    ‖jasRealVecKernel P σ t (q.1 : ℂ)‖ ≤
      ∏ p ∈ P, (1 + |t p| * Real.exp (-(σ - 1 / 2) * Real.log p)) := by
  rw [jasRealVecKernel, norm_prod]
  exact Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p _ =>
    norm_jasRealFactor_xiZero_le σ (t p) p q

theorem summable_jasRealVecTerm (P : Finset Nat.Primes) (σ : ℝ) (t : Nat.Primes → ℝ) :
    Summable fun q : XiZeroCopy => jasRealVecTerm P σ t (q.1 : ℂ) := by
  refine Summable.of_norm_bounded ((summable_inv_mul_one_sub.norm).mul_left
    (∏ p ∈ P, (1 + |t p| * Real.exp (-(σ - 1 / 2) * Real.log p)))) fun q => ?_
  rw [jasRealVecTerm, div_eq_mul_one_div, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_jasRealVecKernel_xiZero_le P σ t q) (norm_nonneg _)

theorem summable_jasRealTerm (P : Finset Nat.Primes) (σ t : ℝ) :
    Summable fun q : XiZeroCopy => jasRealTerm P σ t (q.1 : ℂ) :=
  summable_jasRealVecTerm P σ fun _ => t

/-! ## The aggregate at the vertices -/

/-- **The constant-amplitude aggregate is a Bernstein polynomial** of the full-amplitude subset
aggregates. -/
theorem re_tsum_jasRealTerm_eq_sum_powerset (P : Finset Nat.Primes) (σ t : ℝ) :
    (∑' q : XiZeroCopy, jasRealTerm P σ t (q.1 : ℂ)).re = ∑ S ∈ P.powerset,
      t ^ S.card * (1 - t) ^ (P \ S).card * (∑' q : XiZeroCopy, jasRealTerm S σ 1 (q.1 : ℂ)).re := by
  have e : ∀ q : XiZeroCopy, jasRealTerm P σ t (q.1 : ℂ) = ∑ S ∈ P.powerset,
      ((t ^ S.card * (1 - t) ^ (P \ S).card : ℝ) : ℂ) * jasRealTerm S σ 1 (q.1 : ℂ) := by
    intro q
    rw [jasRealTerm, jasRealKernel_eq_sum_powerset, Finset.sum_div]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [jasRealTerm, mul_div_assoc]
  simp_rw [e]
  rw [Summable.tsum_finsetSum fun S _ => (summable_jasRealTerm S σ 1).mul_left _, Complex.re_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [tsum_mul_left, Complex.re_ofReal_mul]

/-- **The per-prime aggregate is a convex combination** of the sign-pattern aggregates. -/
theorem re_tsum_jasRealVecTerm_eq_sum_signs (P : Finset Nat.Primes) (σ : ℝ)
    (t : Nat.Primes → ℝ) :
    (∑' q : XiZeroCopy, jasRealVecTerm P σ t (q.1 : ℂ)).re = ∑ S ∈ P.powerset,
      (∏ p ∈ S, (1 + t p) / 2) * (∏ p ∈ P \ S, (1 - t p) / 2) *
        (∑' q : XiZeroCopy, jasRealVecTerm P σ (jasSignVec S) (q.1 : ℂ)).re := by
  have e : ∀ q : XiZeroCopy, jasRealVecTerm P σ t (q.1 : ℂ) = ∑ S ∈ P.powerset,
      (((∏ p ∈ S, (1 + t p) / 2) * ∏ p ∈ P \ S, (1 - t p) / 2 : ℝ) : ℂ) *
        jasRealVecTerm P σ (jasSignVec S) (q.1 : ℂ) := by
    intro q
    rw [jasRealVecTerm, jasRealVecKernel_eq_sum_signs, Finset.sum_div]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [jasRealVecTerm, mul_div_assoc]
  simp_rw [e]
  rw [Summable.tsum_finsetSum fun S _ => (summable_jasRealVecTerm P σ _).mul_left _,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [tsum_mul_left, Complex.re_ofReal_mul]

/-- **Amplitude elimination.**  Positivity for every constant amplitude `t ∈ [0,1]` is positivity at
full amplitude on every subset. -/
theorem jasRealPositiveAbove_iff_subset {X : ℕ} {σ : ℝ} :
    JasRealPositiveAbove X σ ↔ JasRealSubsetPositiveAbove X σ := by
  constructor
  · intro h P hP
    exact h P hP 1 zero_le_one le_rfl
  · intro h P hP t ht0 ht1
    change 0 ≤ (∑' q : XiZeroCopy, jasRealTerm P σ t (q.1 : ℂ)).re
    rw [re_tsum_jasRealTerm_eq_sum_powerset]
    refine Finset.sum_nonneg fun S hS => mul_nonneg
      (mul_nonneg (pow_nonneg ht0 _) (pow_nonneg (by linarith) _)) ?_
    exact h S fun p hp => hP p (Finset.mem_powerset.mp hS hp)

/-- **Per-prime Bernstein expansion.**
`K_{P,t} = Σ_{S ⊆ P} ∏_{p ∈ S} t_p ∏_{p ∈ P∖S} (1 − t_p) K_{S,1}`. -/
theorem jasRealVecKernel_eq_sum_powerset (P : Finset Nat.Primes) (σ : ℝ) (t : Nat.Primes → ℝ)
    (s : ℂ) :
    jasRealVecKernel P σ t s = ∑ S ∈ P.powerset,
      (((∏ p ∈ S, t p) * ∏ p ∈ P \ S, (1 - t p) : ℝ) : ℂ) * jasRealKernel S σ 1 s := by
  have h : ∀ p ∈ P, jasRealFactor σ (t p) p s =
      (t p : ℂ) * jasRealFactor σ 1 p s + ((1 - t p : ℝ) : ℂ) := by
    intro p _
    rw [jasRealFactor_eq_affine]
    push_cast
    ring
  rw [jasRealVecKernel, Finset.prod_congr rfl h, Finset.prod_add]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_mul_distrib, jasRealKernel]
  push_cast
  ring

/-- The per-prime aggregate with amplitudes in `[0,1]` is a nonnegative combination of the
full-amplitude subset aggregates. -/
theorem re_tsum_jasRealVecTerm_eq_sum_powerset (P : Finset Nat.Primes) (σ : ℝ)
    (t : Nat.Primes → ℝ) :
    (∑' q : XiZeroCopy, jasRealVecTerm P σ t (q.1 : ℂ)).re = ∑ S ∈ P.powerset,
      (∏ p ∈ S, t p) * (∏ p ∈ P \ S, (1 - t p)) *
        (∑' q : XiZeroCopy, jasRealTerm S σ 1 (q.1 : ℂ)).re := by
  have e : ∀ q : XiZeroCopy, jasRealVecTerm P σ t (q.1 : ℂ) = ∑ S ∈ P.powerset,
      (((∏ p ∈ S, t p) * ∏ p ∈ P \ S, (1 - t p) : ℝ) : ℂ) * jasRealTerm S σ 1 (q.1 : ℂ) := by
    intro q
    rw [jasRealVecTerm, jasRealVecKernel_eq_sum_powerset, Finset.sum_div]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [jasRealTerm, mul_div_assoc]
  simp_rw [e]
  rw [Summable.tsum_finsetSum fun S _ => (summable_jasRealTerm S σ 1).mul_left _, Complex.re_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [tsum_mul_left, Complex.re_ofReal_mul]

/-- Subset positivity gives positivity for every per-prime amplitude in `[0,1]`. -/
theorem JasRealSubsetPositiveAbove.vecNonneg {X : ℕ} {σ : ℝ} (h : JasRealSubsetPositiveAbove X σ)
    {P : Finset Nat.Primes} (hP : ∀ p ∈ P, X < (p : ℕ)) {t : Nat.Primes → ℝ}
    (ht : ∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 1) :
    0 ≤ (∑' q : XiZeroCopy, jasRealVecTerm P σ t (q.1 : ℂ)).re := by
  rw [re_tsum_jasRealVecTerm_eq_sum_powerset]
  refine Finset.sum_nonneg fun S hS => mul_nonneg (mul_nonneg ?_ ?_)
    (h S fun p hp => hP p (Finset.mem_powerset.mp hS hp))
  · exact Finset.prod_nonneg fun p hp => (ht p (Finset.mem_powerset.mp hS hp)).1
  · exact Finset.prod_nonneg fun p hp => by linarith [(ht p (Finset.mem_sdiff.mp hp).1).2]

/-- Raising the level rescales the amplitudes by `p^{−(σ'−σ)} ≤ 1`. -/
theorem jasRealKernel_eq_vec_of_level (P : Finset Nat.Primes) (σ σ' t : ℝ) (s : ℂ) :
    jasRealKernel P σ' t s =
      jasRealVecKernel P σ (fun p => t * Real.exp (-(σ' - σ) * Real.log p)) s := by
  refine Finset.prod_congr rfl fun p _ => ?_
  have e : t * Real.exp (-σ' * Real.log p) =
      t * Real.exp (-(σ' - σ) * Real.log p) * Real.exp (-σ * Real.log p) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [jasRealFactor, jasRealFactor, e]

/-- **Monotonicity in the level.**  Subset positivity at level `σ` gives real-amplitude positivity
at every level `σ' ≥ σ`. -/
theorem JasRealSubsetPositiveAbove.mono {X : ℕ} {σ σ' : ℝ} (h : JasRealSubsetPositiveAbove X σ)
    (hσ : σ ≤ σ') : JasRealPositiveAbove X σ' := by
  intro P hP t ht0 ht1
  change 0 ≤ (∑' q : XiZeroCopy, jasRealTerm P σ' t (q.1 : ℂ)).re
  have e : ∀ q : XiZeroCopy, jasRealTerm P σ' t (q.1 : ℂ) =
      jasRealVecTerm P σ (fun p => t * Real.exp (-(σ' - σ) * Real.log p)) (q.1 : ℂ) := fun q => by
    rw [jasRealTerm, jasRealVecTerm, jasRealKernel_eq_vec_of_level P σ σ' t]
  simp_rw [e]
  refine h.vecNonneg hP fun p _ => ⟨mul_nonneg ht0 (Real.exp_pos _).le, ?_⟩
  have hL := (log_two_le_log_prime p).trans' (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have he : Real.exp (-(σ' - σ) * Real.log p) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  calc t * Real.exp (-(σ' - σ) * Real.log p) ≤ 1 * 1 :=
        mul_le_mul ht1 he (Real.exp_pos _).le zero_le_one
    _ = 1 := one_mul 1

/-- **Sign patterns decide per-prime positivity.** -/
theorem jasRealVecPositiveAbove_iff_sign {X : ℕ} {σ : ℝ} :
    JasRealVecPositiveAbove X σ ↔ JasRealSignPositiveAbove X σ := by
  constructor
  · intro h P hP S _
    refine h P hP _ fun p _ => ?_
    unfold jasSignVec
    split_ifs <;> simp
  · intro h P hP t ht
    rw [re_tsum_jasRealVecTerm_eq_sum_signs]
    refine Finset.sum_nonneg fun S hS => mul_nonneg (mul_nonneg ?_ ?_)
      (h P hP S (Finset.mem_powerset.mp hS))
    · refine Finset.prod_nonneg fun p hp => ?_
      have := abs_le.mp (ht p (Finset.mem_powerset.mp hS hp))
      linarith
    · refine Finset.prod_nonneg fun p hp => ?_
      have := abs_le.mp (ht p (Finset.mem_sdiff.mp hp).1)
      linarith

/-- Per-prime positivity contains constant-amplitude positivity. -/
theorem JasRealVecPositiveAbove.realPositive {X : ℕ} {σ : ℝ} (h : JasRealVecPositiveAbove X σ) :
    JasRealPositiveAbove X σ := fun P hP t ht0 ht1 =>
  h P hP (fun _ => t) fun _ _ => abs_le.mpr ⟨by linarith, ht1⟩

/-! ## The forward direction -/

/-- On the critical line the factor is the real number `1 + a p^{−σ} cos(γ log p)`. -/
theorem jasRealFactor_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) (σ a : ℝ) (p : Nat.Primes) :
    jasRealFactor σ a p s =
      ((1 + a * Real.exp (-σ * Real.log p) * Real.cos (s.im * Real.log p) : ℝ) : ℂ) := by
  have e : (s - 1 / 2) * (Real.log p : ℂ) = ((s.im * Real.log p : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hs]
  rw [jasRealFactor, e, Complex.cosh_mul_I, ← Complex.ofReal_cos]
  push_cast
  ring

/-- On the critical line `s(1 − s) = ¼ + γ²`. -/
theorem mul_one_sub_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) :
    s * (1 - s) = ((1 / 4 + s.im ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hs, pow_two] <;> ring

/-- On the critical line every per-prime term with `|t_p| ≤ 1` and `σ ≥ 0` has nonnegative real
part. -/
theorem re_jasRealVecTerm_nonneg_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) {σ : ℝ} (hσ : 0 ≤ σ)
    (P : Finset Nat.Primes) (t : Nat.Primes → ℝ) (ht : ∀ p ∈ P, |t p| ≤ 1) :
    0 ≤ (jasRealVecTerm P σ t s).re := by
  rw [jasRealVecTerm, jasRealVecKernel,
    Finset.prod_congr rfl fun p _ => jasRealFactor_of_re_eq_half hs σ (t p) p,
    ← Complex.ofReal_prod, mul_one_sub_of_re_eq_half hs, Complex.div_ofReal_re,
    Complex.ofReal_re]
  refine div_nonneg (Finset.prod_nonneg fun p hp => ?_) (by positivity)
  have hL := (log_two_le_log_prime p).trans' (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have he1 : Real.exp (-σ * Real.log p) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have he0 := Real.exp_pos (-σ * Real.log p)
  have hb : |t p * Real.exp (-σ * Real.log p) * Real.cos (s.im * Real.log p)| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_pos he0]
    calc |t p| * Real.exp (-σ * Real.log p) * |Real.cos (s.im * Real.log p)| ≤ 1 * 1 * 1 := by
          gcongr
          · exact ht p hp
          · exact Real.abs_cos_le_one _
      _ = 1 := by norm_num
  linarith [neg_abs_le (t p * Real.exp (-σ * Real.log p) * Real.cos (s.im * Real.log p))]

/-- **RH gives per-prime positivity** at every level `σ ≥ 0` above every `X`. -/
theorem jasRealVecPositiveAbove_of_riemannHypothesis (hRH : RiemannHypothesis) (X : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) : JasRealVecPositiveAbove X σ := by
  intro P _ t ht
  rw [Complex.re_tsum (summable_jasRealVecTerm P σ t)]
  exact tsum_nonneg fun q => re_jasRealVecTerm_nonneg_of_re_eq_half
    (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q) hσ P t ht

/-! ## Capstones -/

/-- The full-amplitude kernel is the prime cosine kernel. -/
theorem jasRealKernel_one_eq_jasCosineKernel (P : Finset Nat.Primes) (σ : ℝ) (s : ℂ) :
    jasRealKernel P σ 1 s = jasCosineKernel P σ s := by
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [jasRealFactor, one_mul]

/-- Subset positivity is positivity against the untranslated prime cosine kernels. -/
theorem jasRealSubsetPositiveAbove_iff_cosine {X : ℕ} {σ : ℝ} :
    JasRealSubsetPositiveAbove X σ ↔ ∀ P : Finset Nat.Primes, (∀ p ∈ P, X < (p : ℕ)) →
      0 ≤ (∑' q : XiZeroCopy, jasCosineKernel P σ (q.1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  simp only [JasRealSubsetPositiveAbove, jasRealTerm, jasRealKernel_one_eq_jasCosineKernel]

/-- Positivity against all translates contains the untranslated kernels. -/
theorem JasCosinePositiveAbove.subsetPositive {X : ℕ} {σ : ℝ} (h : JasCosinePositiveAbove X σ) :
    JasRealSubsetPositiveAbove X σ := by
  rw [jasRealSubsetPositiveAbove_iff_cosine]
  intro P hP
  simpa using h P hP 0

/-- **Detection at full amplitude.**  An attained off-line zero at distance `δ` makes some
full-amplitude subset test negative at every level `δ < σ < 1 + δ`, above every `X`. -/
theorem not_jasRealSubsetPositiveAbove_of_maximal_offLine (q₀ : XiZeroCopy)
    (hoff : (q₀.1 : ℂ).re ≠ 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) {σ : ℝ}
    (hσ0 : |(q₀.1 : ℂ).re - 1 / 2| < σ) (hσ1 : σ < 1 + |(q₀.1 : ℂ).re - 1 / 2|) (X : ℕ) :
    ¬ JasRealSubsetPositiveAbove X σ := fun h =>
  not_jasRealPositiveAbove_of_maximal_offLine q₀ hoff hmax hσ0 hσ1 X
    (jasRealPositiveAbove_iff_subset.mpr h)

/-- **Capstone, subset form.**  RH holds iff the zeros approach the critical line and, above some
`X`, `Re Σ_ρ ∏_{p ∈ P} (1 + p^{−1} cosh((ρ − ½) log p))/(ρ(1−ρ)) ≥ 0` for every finite set `P` of
primes. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_jasRealSubsetPositiveAbove :
    RiemannHypothesis ↔ ZerosApproachLine ∧ ∃ X : ℕ, JasRealSubsetPositiveAbove X 1 := by
  rw [riemannHypothesis_iff_zerosApproachLine_and_jasRealPositiveAbove]
  simp_rw [jasRealPositiveAbove_iff_subset]

/-- **Capstone, sign form.**  RH holds iff the zeros approach the critical line and, above some `X`,
`Re Σ_ρ ∏_{p ∈ P} (1 + ε_p p^{−1} cosh((ρ − ½) log p))/(ρ(1−ρ)) ≥ 0` for every finite set `P` of
primes and every sign pattern `ε ∈ {±1}^P`. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_jasRealSignPositiveAbove :
    RiemannHypothesis ↔ ZerosApproachLine ∧ ∃ X : ℕ, JasRealSignPositiveAbove X 1 := by
  constructor
  · intro hRH
    exact ⟨(riemannHypothesis_iff_zerosApproachLine_and_jasRealPositiveAbove.mp hRH).1, 0,
      jasRealVecPositiveAbove_iff_sign.mp
        (jasRealVecPositiveAbove_of_riemannHypothesis hRH 0 zero_le_one)⟩
  · rintro ⟨hZ, X, h⟩
    exact riemannHypothesis_iff_zerosApproachLine_and_jasRealPositiveAbove.mpr
      ⟨hZ, X, (jasRealVecPositiveAbove_iff_sign.mpr h).realPositive⟩

/-- **Capstone, level form.**  RH holds iff the zeros approach the critical line and subset
positivity holds above some `X` at some level `σ ≤ 1`; under RH it holds at every level `σ ≥ 0`. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_exists_level_le_one :
    RiemannHypothesis ↔ ZerosApproachLine ∧ ∃ X : ℕ, ∃ σ ≤ 1, JasRealSubsetPositiveAbove X σ := by
  constructor
  · intro hRH
    refine ⟨(riemannHypothesis_iff_zerosApproachLine_and_jasRealPositiveAbove.mp hRH).1, 0, 0,
      zero_le_one, ?_⟩
    exact jasRealPositiveAbove_iff_subset.mp
      (jasRealVecPositiveAbove_of_riemannHypothesis hRH 0 le_rfl).realPositive
  · rintro ⟨hZ, X, σ, hσ, h⟩
    exact riemannHypothesis_iff_zerosApproachLine_and_jasRealPositiveAbove.mpr ⟨hZ, X, h.mono hσ⟩

/-- **Capstone, finite subset form.** -/
theorem riemannHypothesis_iff_finiteOffLine_and_jasRealSubsetPositiveAbove :
    RiemannHypothesis ↔ FiniteOffLine ∧ ∃ X : ℕ, JasRealSubsetPositiveAbove X 1 := by
  rw [riemannHypothesis_iff_finiteOffLine_and_jasRealPositiveAbove]
  simp_rw [jasRealPositiveAbove_iff_subset]

end

end RHTower
