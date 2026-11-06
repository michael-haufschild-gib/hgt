import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheTorusWallsOfPrimeInsertion
import GaloisForLFunctions.HTGeometry.PrimeTorusKroneckerDensity

/-!
# Phase locking is torus positivity

The phases of an actual Euler product are locked: `θ_p = b log p`. By Kronecker, the locked phases fill the torus. So a torus sum
with a *fixed* amplitude is nonnegative at all locked phases iff it is nonnegative at all phases
(`torusSum_nonneg_iff_locked`). Hence:

* a fixed summable amplitude gets nothing from locking. In `S(a, b) = Σ_N τ_b(N) A(N; a, b)` locking can only act through the dependence of
  the amplitude on `b`, the correlation of the amplitude with the height, or through the failure of summability uniform in the prime set;
* the walls of the torus apply verbatim at locked phases, at a height that Kronecker does not bound.
* this is the mechanism by which incommensurability of `log p` enters: for commensurable steps the locked phases lie on a subtorus, and locked
  positivity is strictly weaker (`locked_on_commensurable_steps`).
-/

open Filter Topology Set Metric
open scoped Real

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GaloisForLFunctions.CompletedArithmeticForms (cosSum)

noncomputable section

/-! ### Characters on the circle group -/

/-- The character `U_k` on the circle group: `Σ_j Re z^{2j−k}`. -/
def chiCircle (k : ℕ) (z : Circle) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), (((z ^ ((2 * (j : ℤ)) - k) : Circle) : ℂ)).re

theorem continuous_chiCircle (k : ℕ) : Continuous (chiCircle k) := by
  unfold chiCircle
  refine continuous_finsetSum _ fun j _ => ?_
  have hc : Continuous fun z : Circle => (z : ℂ) := continuous_subtype_val
  exact Complex.continuous_re.comp (hc.comp (continuous_zpow _))

theorem abs_chiCircle_le (k : ℕ) (z : Circle) : |chiCircle k z| ≤ (k : ℝ) + 1 := by
  rw [chiCircle]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ 1 fun j _ => ?_).trans (by simp)
  refine (Complex.abs_re_le_norm _).trans ?_
  simp

/-- `U_k(cos θ)` depends only on `e^{iθ}`. -/
theorem chiCircle_exp (k : ℕ) (θ : ℝ) : chiCircle k (Circle.exp θ) = cosSum θ k := by
  rw [chiCircle, cosSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Circle.coe_zpow, Circle.coe_exp, ← Complex.exp_int_mul]
  have e : (((2 * (j : ℤ) - (k : ℤ)) : ℤ) : ℂ) * ((θ : ℂ) * Complex.I) =
      (((((2 * j : ℝ) - k) * θ : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e, Complex.exp_ofReal_mul_I_re]

variable {n : ℕ} {a : (Fin n → ℕ) → ℝ}

/-- The torus sum as a function on the compact torus. -/
def torusSumCircle (a : (Fin n → ℕ) → ℝ) (z : Fin n → Circle) : ℝ :=
  ∑' k, a k * ∏ i, chiCircle (k i) (z i)

theorem torusSumCircle_exp (a : (Fin n → ℕ) → ℝ) (θ : Fin n → ℝ) :
    torusSumCircle a (fun i => Circle.exp (θ i)) = torusSum a θ := by
  refine tsum_congr fun k => ?_
  simp only [chiCircle_exp, chiProd]

theorem continuous_torusSumCircle (ha : TraceSummable a) : Continuous (torusSumCircle a) := by
  refine continuous_tsum (fun k => continuous_const.mul
    (continuous_finsetProd _ fun i _ => (continuous_chiCircle (k i)).comp (continuous_apply i)))
    ha fun k z => ?_
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Finset.abs_prod]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => abs_chiCircle_le _ _

/-! ### Locked phases -/

/-- Steps whose locked phases fill the torus. -/
def IsKroneckerFamily (ℓ : Fin n → ℝ) : Prop :=
  ∀ (θ : Fin n → ℝ) (ε : ℝ), 0 < ε → ∃ b : ℝ, ∀ i,
    ‖Complex.exp (((b * ℓ i : ℝ) : ℂ) * Complex.I) - Complex.exp ((θ i : ℂ) * Complex.I)‖ < ε

/-- **Locking is torus positivity.** -/
theorem torusSum_nonneg_iff_locked (ha : TraceSummable a) {ℓ : Fin n → ℝ} (hℓ : IsKroneckerFamily ℓ) :
    (∀ θ, 0 ≤ torusSum a θ) ↔ ∀ b : ℝ, 0 ≤ torusSum a fun i => b * ℓ i := by
  refine ⟨fun h b => h _, fun h θ => ?_⟩
  rw [← torusSumCircle_exp]
  have hclosed : IsClosed {z : Fin n → Circle | 0 ≤ torusSumCircle a z} :=
    isClosed_le continuous_const (continuous_torusSumCircle ha)
  have hsub : {z : Fin n → Circle | ∃ b : ℝ, z = fun i => Circle.exp (b * ℓ i)} ⊆
      {z : Fin n → Circle | 0 ≤ torusSumCircle a z} := by
    rintro _ ⟨b, rfl⟩
    change 0 ≤ torusSumCircle a _
    rw [torusSumCircle_exp]
    exact h b
  refine closure_minimal hsub hclosed (Metric.mem_closure_iff.mpr fun ε hε => ?_)
  obtain ⟨b, hb⟩ := hℓ θ ε hε
  refine ⟨_, ⟨b, rfl⟩, ?_⟩
  rw [dist_pi_lt_iff hε]
  intro i
  have h1 := hb i
  rw [norm_sub_rev] at h1
  change dist ((Circle.exp (θ i) : Circle) : ℂ) ((Circle.exp (b * ℓ i) : Circle) : ℂ) < ε
  rw [Circle.coe_exp, Circle.coe_exp, dist_eq_norm]
  exact h1

/-- **The logarithms of distinct primes are a Kronecker family.** -/
theorem isKroneckerFamily_log_primes (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) : IsKroneckerFamily fun i => Real.log (p i) := by
  intro θ ε hε
  classical
  obtain ⟨N, hN⟩ : ∃ N, ∀ i, p i ≤ N := by
    obtain ⟨N, hN⟩ := (Set.finite_range p).bddAbove
    exact ⟨N, fun i => hN ⟨i, rfl⟩⟩
  let q : Fin n → GaloisForLFunctions.primesLE N := fun i =>
    ⟨⟨p i, hp i⟩, Finset.mem_map.mpr
      ⟨⟨p i, Nat.mem_primesBelow.mpr ⟨Nat.lt_succ_of_le (hN i), hp i⟩⟩, Finset.mem_attach _ _, rfl⟩⟩
  have hq : Function.Injective q := by
    intro i j hij
    apply hinj
    have := congrArg (fun x : GaloisForLFunctions.primesLE N => ((x : Nat.Primes) : ℕ)) hij
    exact this
  let θ' : GaloisForLFunctions.primesLE N → ℝ := Function.extend q θ 0
  obtain ⟨t, ht⟩ := GaloisForLFunctions.primeTorus_kronecker_dense N θ' hε
  refine ⟨t, fun i => ?_⟩
  have h := ht (q i)
  have e : θ' (q i) = θ i := hq.extend_apply θ 0 i
  rw [e] at h
  have e2 : GaloisForLFunctions.expChar
      (Real.log (((q i : GaloisForLFunctions.primesLE N) : Nat.Primes) : ℕ)) t =
      Complex.exp (((t * Real.log (p i) : ℝ) : ℂ) * Complex.I) := by
    change Complex.exp (((Real.log (p i) * t : ℝ) : ℂ) * Complex.I) = _
    rw [mul_comm (Real.log (p i)) t]
  rwa [e2] at h

/-- **Commensurable steps.** On equal steps the locked phases `(bℓ, bℓ)` form a diagonal, and the torus is not reached: a
fixed amplitude can be positive on the diagonal and negative off it. So incommensurability is what makes locking equal to the
torus. -/
theorem locked_on_commensurable_steps :
    ∃ a : (Fin 2 → ℕ) → ℝ, TraceSummable a ∧ (∀ b : ℝ, 0 ≤ torusSum a fun _ => b * 1) ∧
      ∃ θ, torusSum a θ < 0 := by
  -- the character `U₁(θ₁) U₁(θ₂)` is a square on the diagonal and negative off it
  set m : Fin 2 → ℕ := unitIdx 0 + unitIdx 1 with hm
  refine ⟨fun k => if k = m then 1 else 0, ?_, ?_⟩
  · refine summable_of_ne_finset_zero (s := {m}) fun k hk => ?_
    have : k ≠ m := by simpa using hk
    simp [this]
  have hS : ∀ θ, torusSum (fun k => if k = m then (1 : ℝ) else 0) θ = chiProd θ m := by
    intro θ
    rw [torusSum, tsum_eq_single m fun k hk => by simp [hk]]
    simp
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hval : ∀ θ, chiProd θ m = cosSum (θ 0) 1 * cosSum (θ 1) 1 := fun θ =>
    chiProd_unit_add_unit θ h01
  have hcos : ∀ t : ℝ, cosSum t 1 = 2 * Real.cos t := by
    intro t
    simp only [cosSum, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Real.cos_neg]
    ring
  refine ⟨fun b => ?_, ![0, π], ?_⟩
  · rw [hS, hval]
    exact mul_self_nonneg _
  · rw [hS, hval]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hcos, Real.cos_zero, Real.cos_pi]
    norm_num

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
