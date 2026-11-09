import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheFrobeniusOfTheTorsionIsGalois
import GaloisForLFunctions.HTGeometry.FinitelyGeneratedDivisibleSubgroup

/-!
# Prime-orbit clocks have no discontinuous freedom

A character-valued reparametrization of the prime orbit is additive by
injectivity. Its discrepancy from a linear clock lies in a cyclic period
lattice. Divisibility kills that discrepancy, without a regularity assumption.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
open InfiniteRankWeilTheory

variable {P : Finset Nat.Primes}

theorem phase_eq_expChar (n : ℕ) (t : ℝ) :
    phase n t = expChar (-Real.log n) t := by
  unfold phase expChar
  congr 1
  push_cast
  ring

theorem phase_add (n : ℕ) (s t : ℝ) :
    phase n (s + t) = phase n s * phase n t := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_sub (n : ℕ) (s t : ℝ) :
    phase n (s - t) = phase n s / phase n t := by
  unfold phase
  rw [← Complex.exp_sub]
  congr 1
  push_cast
  ring

/-- Two distinct prime coordinates identify the real orbit parameter. -/
theorem orbitPoint_injective (p q : P) (hpq : p ≠ q) :
    Function.Injective (orbitPoint P) := by
  intro s t h
  apply sub_eq_zero.mp
  apply eq_zero_of_exact_return p.val.property q.val.property
    (fun he => hpq (Subtype.ext (Subtype.ext he)))
  · rw [phase_sub, show phase (p.val : ℕ) s = phase (p.val : ℕ) t from congrFun h p]
    exact div_self (Complex.exp_ne_zero _)
  · rw [phase_sub, show phase (q.val : ℕ) s = phase (q.val : ℕ) t from congrFun h q]
    exact div_self (Complex.exp_ne_zero _)

/-- An additive real clock agreeing with a character has no hidden period-lattice term. -/
theorem additive_character_clock (f : ℝ →+ ℝ) (β γ : ℝ)
    (h : ∀ t, expChar β (f t) = expChar γ t) :
    ∀ t, β * f t = γ * t := by
  let δ : ℝ →+ ℝ :=
    { toFun := fun t => β * f t - γ * t
      map_zero' := by simp
      map_add' := by intro s t; simp only [map_add]; ring }
  have hperiod : ∀ t, δ t ∈ AddSubgroup.zmultiples (2 * Real.pi) := by
    intro t
    have he : Complex.exp (((δ t : ℝ) : ℂ) * I) = 1 := by
      change Complex.exp (((β * f t - γ * t : ℝ) : ℂ) * I) = 1
      rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub]
      change expChar β (f t) / expChar γ t = 1
      rw [h t, div_self (Complex.exp_ne_zero _)]
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp he
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨k, ?_⟩
    have him : δ t = (k : ℝ) * (2 * Real.pi) := by
      simpa using congrArg Complex.im hk
    simpa only [zsmul_eq_mul] using him.symm
  letI : AddGroup.FG (AddSubgroup.zmultiples (2 * Real.pi)) :=
    (AddGroup.fg_iff_addSubgroup_fg _).mpr
      ⟨{2 * Real.pi}, by
        rw [Finset.coe_singleton]
        exact (AddSubgroup.zmultiples_eq_closure _).symm⟩
  have hzero : δ.range = ⊥ :=
    HTGeometry.addSubgroup_eq_bot_of_le_fg_of_nsmulDivisible δ.range
      (AddSubgroup.zmultiples (2 * Real.pi))
      (by rintro x ⟨t, rfl⟩; exact hperiod t)
      (by
        intro n hn x hx
        obtain ⟨t, rfl⟩ := hx
        refine ⟨δ (t / n), ⟨t / n, rfl⟩, ?_⟩
        rw [← map_nsmul]
        congr 1
        rw [nsmul_eq_mul]
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        field_simp)
  intro t
  have ht : δ t ∈ δ.range := ⟨t, rfl⟩
  rw [hzero] at ht
  exact sub_eq_zero.mp ht

/-- Characters in each coordinate force an affine-free linear clock. -/
theorem prime_character_clock_linear (p q : P) (hpq : p ≠ q)
    (τ : ℝ → ℝ) (γ : P → ℝ)
    (h : ∀ t r, orbitPoint P (τ t) r = expChar (γ r) t) :
    ∃ a : ℝ, (∀ t, τ t = a * t) ∧
      ∀ r, γ r = -Real.log ((r : Nat.Primes) : ℕ) * a := by
  have hinj := orbitPoint_injective p q hpq
  let f : ℝ →+ ℝ :=
    { toFun := τ
      map_zero' := by
        apply hinj
        funext r
        rw [h]
        simp only [expChar, mul_zero, Complex.ofReal_zero, zero_mul,
          Complex.exp_zero, orbitPoint, phase]
        simp
      map_add' := by
        intro s t
        apply hinj
        funext r
        rw [h, orbitPoint, phase_add]
        change expChar (γ r) (s + t) =
          orbitPoint P (τ s) r * orbitPoint P (τ t) r
        rw [h, h]
        unfold expChar
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring }
  have hlinear (r : P) := additive_character_clock f
    (-Real.log ((r : Nat.Primes) : ℕ)) (γ r)
    (fun t => by rw [← phase_eq_expChar]; exact h t r)
  have hp0 : -Real.log ((p : Nat.Primes) : ℕ) ≠ 0 :=
    neg_ne_zero.mpr (ne_of_gt (Real.log_pos (by exact_mod_cast p.val.property.one_lt)))
  let a := γ p / (-Real.log ((p : Nat.Primes) : ℕ))
  have hf : ∀ t, τ t = a * t := by
    intro t
    apply (mul_left_cancel₀ hp0)
    change (-Real.log ((p : Nat.Primes) : ℕ)) * f t = _
    rw [hlinear p t]
    dsimp [a]
    field_simp
  refine ⟨a, hf, fun r => ?_⟩
  have hr := hlinear r 1
  change -Real.log ((r : Nat.Primes) : ℕ) * τ 1 = γ r * 1 at hr
  simpa only [hf 1, mul_one] using hr.symm

#print axioms prime_character_clock_linear

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
