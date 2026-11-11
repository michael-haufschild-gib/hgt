import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.OnNestedWindowsTheCombFormTendsToWeilsFormOfTheStepPacket
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.WeilsFormInTheGaugeOfTheFlatTail

/-!
# Weil's form on the comb is a quadratic form in the increments of the divisor

A real divisor `Σ_{n ≤ N} c_n γ_n` is a combination of the flat tails `T_M = Σ_{n ≤ M} γ_n` with
the increments `c_M − c_{M+1}` as coefficients. The flat tail `T_M` pairs with a degree point
`n ≤ M` through the row

`R_M(n) = M/n − ψ(M/n) + H_M − ½(H_{M−n} + H_{M+n}) + 3/(4n) − log 2π`

(continuation, `tailRow`), the remainder of the prime number theorem at the ratio `M/n`.

* **Adding a constant** (`combForm_add_const`):
  `𝔚(c + t) = 𝔚(c) + 2t ⟨T, c⟩ + t² 𝔚(T)`, `T` the flat divisor of the set.
* **Peeling the top point** (`combForm_Icc_succ`): on `[1, N + 1]`, with `t = c_{N+1}`,
  `𝔚(c) = 𝔚_{[1,N]}(c − t) + t Σ_{n ≤ N+1} (2c_n − t) R_{N+1}(n)`.
* **The expansion** (`combForm_Icc_eq_sum_increments`): if `c_{N+1} = 0`,

  `2 d₁ d₂ − D·D = Σ_{M ≤ N} (c_M − c_{M+1}) Σ_{n ≤ M} (2c_n − c_M − c_{M+1}) R_M(n)`.

So at every finite scale the form of a tail is a quadratic form in its increments whose
coefficients are partial sums of the rows `R_M`: the Laguerre tails of the Li ladder, and every
other tail, are read off the remainders of the prime number theorem at the ratios `M/n ≤ N`.
For the flat tail one increment remains and the expansion is `Σ_{n ≤ N} R_N(n)`.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HodgeTheoryOfAFixedPart (formBilin tailRow)

local notation "combW" => HodgeTheoryOfAFixedPart.combForm

variable (S : Finset ℕ)

/-- Adding a constant to the first argument of the bilinear form. -/
theorem formBilin_add_const_left (c e : ℕ → ℝ) (t : ℝ) :
    formBilin S (fun n => c n + t) e = formBilin S c e + t * formBilin S (fun _ => 1) e := by
  have h1 : formBilin S (fun n => c n + t) e =
      formBilin S c e + formBilin S (fun _ => t) e := formBilin_add_left S c (fun _ => t) e
  have h2 : formBilin S (fun _ : ℕ => t) e = t * formBilin S (fun _ => 1) e := by
    have h := formBilin_const_mul_left S t (fun _ => 1) e
    have hfun : (fun _ : ℕ => t) = fun _ : ℕ => t * (1 : ℝ) := funext fun _ => (mul_one t).symm
    rw [hfun]
    exact h
  rw [h1, h2]

/-- **Adding a constant to a divisor.** -/
theorem combForm_add_const (c : ℕ → ℝ) (t : ℝ) :
    combW S (fun n => c n + t) =
      combW S c + 2 * t * formBilin S (fun _ => 1) c + t ^ 2 * combW S (fun _ => 1) := by
  have hR : ∀ e : ℕ → ℝ, formBilin S e (fun n => c n + t) =
      formBilin S e c + t * formBilin S e (fun _ => 1) := fun e => by
    rw [formBilin_comm S e, formBilin_add_const_left, formBilin_comm S c e,
      formBilin_comm S (fun _ => 1) e]
  rw [← HodgeTheoryOfAFixedPart.formBilin_self S (fun n => c n + t), formBilin_add_const_left,
    hR c, hR (fun _ => 1), HodgeTheoryOfAFixedPart.formBilin_self,
    HodgeTheoryOfAFixedPart.formBilin_self, formBilin_comm S c (fun _ => 1)]
  ring

/-- **Peeling the top point of a tail.** -/
theorem combForm_Icc_succ (N : ℕ) (c : ℕ → ℝ) :
    combW (Icc 1 (N + 1)) c =
      combW (Icc 1 N) (fun n => c n - c (N + 1)) +
        c (N + 1) * ∑ n ∈ Icc 1 (N + 1), (2 * c n - c (N + 1)) * tailRow (N + 1) n := by
  have hc : c = fun n => (c n - c (N + 1)) + c (N + 1) := funext fun n => by ring
  have hsub : combW (Icc 1 (N + 1)) (fun n => c n - c (N + 1)) =
      combW (Icc 1 N) (fun n => c n - c (N + 1)) := by
    refine combForm_of_subset (Finset.Icc_subset_Icc_right (Nat.le_succ N)) fun n hn hnW => ?_
    have h1 := Finset.mem_Icc.mp hn
    have h2 : ¬ (1 ≤ n ∧ n ≤ N) := fun h => hnW (Finset.mem_Icc.mpr h)
    have hn' : n = N + 1 := by omega
    rw [hn', sub_self]
  have hT : combW (Icc 1 (N + 1)) (fun _ => 1) =
      ∑ n ∈ Icc 1 (N + 1), (1 : ℝ) * tailRow (N + 1) n := by
    rw [← HodgeTheoryOfAFixedPart.formBilin_self]
    exact HodgeTheoryOfAFixedPart.formBilin_flatTail (N + 1) fun _ => 1
  have hB : formBilin (Icc 1 (N + 1)) (fun _ => 1) (fun n => c n - c (N + 1)) =
      ∑ n ∈ Icc 1 (N + 1), (c n - c (N + 1)) * tailRow (N + 1) n :=
    HodgeTheoryOfAFixedPart.formBilin_flatTail (N + 1) fun n => c n - c (N + 1)
  have hexp := combForm_add_const (Icc 1 (N + 1)) (fun n => c n - c (N + 1)) (c (N + 1))
  rw [← hc] at hexp
  rw [hexp, hsub, hT, hB, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, add_assoc,
    ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **Weil's form on the comb in the increments of the divisor.** For a divisor on `[1, N]`
(`c_{N+1} = 0`):
`2 d₁ d₂ − D·D = Σ_{M ≤ N} (c_M − c_{M+1}) Σ_{n ≤ M} (2c_n − c_M − c_{M+1}) R_M(n)`. -/
theorem combForm_Icc_eq_sum_increments (N : ℕ) :
    ∀ c : ℕ → ℝ, c (N + 1) = 0 →
      combW (Icc 1 N) c = ∑ M ∈ Icc 1 N, (c M - c (M + 1)) *
        ∑ n ∈ Icc 1 M, (2 * c n - c M - c (M + 1)) * tailRow M n := by
  induction N with
  | zero =>
    intro c _
    have hempty : Icc 1 0 = (∅ : Finset ℕ) := by decide
    rw [hempty, Finset.sum_empty]
    simp [HodgeTheoryOfAFixedPart.combForm, HodgeTheoryOfAFixedPart.combPairing,
      HodgeTheoryOfAFixedPart.degOne, HodgeTheoryOfAFixedPart.degTwo]
  | succ N ih =>
    intro c hc
    have hstep := combForm_Icc_succ N c
    have hih := ih (fun n => c n - c (N + 1)) (sub_self _)
    have hR : ∑ M ∈ Icc 1 (N + 1), (c M - c (M + 1)) *
          ∑ n ∈ Icc 1 M, (2 * c n - c M - c (M + 1)) * tailRow M n =
        ∑ M ∈ Icc 1 N, (c M - c (M + 1)) *
            ∑ n ∈ Icc 1 M, (2 * c n - c M - c (M + 1)) * tailRow M n +
          (c (N + 1) - c (N + 1 + 1)) *
            ∑ n ∈ Icc 1 (N + 1), (2 * c n - c (N + 1) - c (N + 1 + 1)) * tailRow (N + 1) n :=
      Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1) _
    rw [hstep, hih, hR, hc]
    congr 1
    · refine Finset.sum_congr rfl fun M _ => ?_
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun n _ => by ring
    · rw [sub_zero]
      congr 1
      exact Finset.sum_congr rfl fun n _ => by ring

/-- The expansion for a divisor that is not cut: the values beyond `N` do not enter. -/
theorem combForm_Icc_eq_sum_increments_cut (N : ℕ) (c : ℕ → ℝ) :
    combW (Icc 1 N) c =
      ∑ M ∈ Icc 1 N, (c M - (if M < N then c (M + 1) else 0)) *
        ∑ n ∈ Icc 1 M, (2 * c n - c M - (if M < N then c (M + 1) else 0)) * tailRow M n := by
  set c' : ℕ → ℝ := fun n => if n ≤ N then c n else 0 with hc'
  have hcongr : combW (Icc 1 N) c = combW (Icc 1 N) c' :=
    combForm_congr fun n hn => by
      rw [hc']
      simp only [if_pos (Finset.mem_Icc.mp hn).2]
  have hzero : c' (N + 1) = 0 := by
    rw [hc']
    simp
  rw [hcongr, combForm_Icc_eq_sum_increments N c' hzero]
  refine Finset.sum_congr rfl fun M hM => ?_
  have hMN := (Finset.mem_Icc.mp hM).2
  have hcM : c' M = c M := by
    rw [hc']
    simp only [if_pos hMN]
  have hcM1 : c' (M + 1) = if M < N then c (M + 1) else 0 := by
    rw [hc']
    by_cases h : M < N
    · simp only [if_pos h, if_pos (Nat.succ_le_of_lt h)]
    · simp only [if_neg h, if_neg (by omega : ¬ M + 1 ≤ N)]
  rw [hcM, hcM1]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2.trans hMN
  have hcn : c' n = c n := by
    rw [hc']
    simp only [if_pos hnN]
  rw [hcn]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
