import GaloisForLFunctions.HTGeometry.JacobiSolutionConstruction
import GaloisForLFunctions.HTGeometry.JacobiLimitPointBoundedPotential
import GaloisForLFunctions.RHTower.JacobiDeficiencyRankTwoAmbiguity

/-!
# The archimedean prolate Jacobi blocks

The even and odd archimedean prolate parity blocks have Jacobi radii

`ρ_n = ¼√((4n+1)(4n+2)(4n+3)(4n+4))`,  `ρ_n = ¼√((4n+3)(4n+4)(4n+5)(4n+6))`

and diagonals `q_n = -8n²-2n-3/4+2πλ²(8n+1)`, `q_n = -8n²-10n-15/4+2πλ²(8n+5)`.  Two exact
observations drive the whole analysis.

* Each quartic under the square root is `t_n² − 1` for an explicit quadratic `t_n`
  (`t_n = 16n²+20n+5` and `t_n = 16n²+36n+19`), because consecutive outer and inner products
  differ by two.  Hence `ρ_n = t_n/4 − δ_n` with `0 < δ_n ≤ 1/(4t_n)`.
* The Sturm--Liouville potential is therefore *exact*:
  `Q_n = ρ_n + ρ_{n−1} + q_n − z = 3/4 + 2πλ²(8n+c) − z − δ_n − δ_{n−1}`.

At `λ = 0` the potential is bounded while `ρ_n ≥ 4n²`, so no two independent solutions are
square-summable and the block is in the limit-point case.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## The exact shape of the prolate Jacobi radii -/

/-- The quadratic `t_n` for which the prolate Jacobi radius is `¼√(t_n² − 1)`. -/
def prolateBase (β γ : ℝ) (n : ℕ) : ℝ := 16 * (n : ℝ) ^ 2 + β * (n : ℝ) + γ

/-- The prolate Jacobi radius. -/
noncomputable def prolateRho (β γ : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (prolateBase β γ n ^ 2 - 1) / 4

/-- The defect `t_n/4 − ρ_n`. -/
noncomputable def prolateDefect (β γ : ℝ) (n : ℕ) : ℝ :=
  prolateBase β γ n / 4 - prolateRho β γ n

variable {β γ : ℝ} {n : ℕ}

theorem prolateBase_ge (hβ : 0 ≤ β) (hγ : 2 ≤ γ) : 2 ≤ prolateBase β γ n := by
  have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold prolateBase
  nlinarith [sq_nonneg (n : ℝ)]

theorem prolateRho_eq_sub (β γ : ℝ) (n : ℕ) :
    prolateRho β γ n = prolateBase β γ n / 4 - prolateDefect β γ n := by
  unfold prolateDefect
  ring

theorem prolateDefect_mul (hβ : 0 ≤ β) (hγ : 2 ≤ γ) :
    (4 * prolateDefect β γ n) * (prolateBase β γ n
      + Real.sqrt (prolateBase β γ n ^ 2 - 1)) = 1 := by
  have hb := prolateBase_ge (β := β) (γ := γ) (n := n) hβ hγ
  have hsq : (0:ℝ) ≤ prolateBase β γ n ^ 2 - 1 := by nlinarith
  have hs : Real.sqrt (prolateBase β γ n ^ 2 - 1) ^ 2 = prolateBase β γ n ^ 2 - 1 :=
    Real.sq_sqrt hsq
  have hrw : 4 * prolateDefect β γ n
      = prolateBase β γ n - Real.sqrt (prolateBase β γ n ^ 2 - 1) := by
    unfold prolateDefect prolateRho
    ring
  rw [hrw]
  nlinarith [hs]

theorem prolateDefect_pos (hβ : 0 ≤ β) (hγ : 2 ≤ γ) : 0 < prolateDefect β γ n := by
  have hb := prolateBase_ge (β := β) (γ := γ) (n := n) hβ hγ
  have hsq : (0:ℝ) ≤ prolateBase β γ n ^ 2 - 1 := by nlinarith
  have hs0 : (0:ℝ) ≤ Real.sqrt (prolateBase β γ n ^ 2 - 1) := Real.sqrt_nonneg _
  have hm := prolateDefect_mul (β := β) (γ := γ) (n := n) hβ hγ
  have hpos : (0:ℝ) < prolateBase β γ n + Real.sqrt (prolateBase β γ n ^ 2 - 1) := by linarith
  nlinarith [hm, hpos]

theorem prolateDefect_le (hβ : 0 ≤ β) (hγ : 2 ≤ γ) :
    prolateDefect β γ n * (4 * prolateBase β γ n) ≤ 1 := by
  have hb := prolateBase_ge (β := β) (γ := γ) (n := n) hβ hγ
  have hsq : (0:ℝ) ≤ prolateBase β γ n ^ 2 - 1 := by nlinarith
  have hs0 : (0:ℝ) ≤ Real.sqrt (prolateBase β γ n ^ 2 - 1) := Real.sqrt_nonneg _
  have hd := prolateDefect_pos (β := β) (γ := γ) (n := n) hβ hγ
  have hm := prolateDefect_mul (β := β) (γ := γ) (n := n) hβ hγ
  nlinarith [hm, hd, hs0]

theorem prolateDefect_lt_quarter (hβ : 0 ≤ β) (hγ : 2 ≤ γ) : prolateDefect β γ n < 1 / 4 := by
  have hb := prolateBase_ge (β := β) (γ := γ) (n := n) hβ hγ
  have hd := prolateDefect_pos (β := β) (γ := γ) (n := n) hβ hγ
  have hle := prolateDefect_le (β := β) (γ := γ) (n := n) hβ hγ
  nlinarith

/-- **Lower bound on the prolate Jacobi radius.** -/
theorem four_sq_le_prolateRho (hβ : 0 ≤ β) (hγ : 2 ≤ γ) :
    4 * (n : ℝ) ^ 2 ≤ prolateRho β γ n := by
  have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd := prolateDefect_lt_quarter (β := β) (γ := γ) (n := n) hβ hγ
  rw [prolateRho_eq_sub]
  unfold prolateBase
  nlinarith

theorem prolateRho_pos (hβ : 0 ≤ β) (hγ : 2 ≤ γ) : 0 < prolateRho β γ n := by
  have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd := prolateDefect_lt_quarter (β := β) (γ := γ) (n := n) hβ hγ
  have hdp := prolateDefect_pos (β := β) (γ := γ) (n := n) hβ hγ
  rw [prolateRho_eq_sub]
  unfold prolateBase
  nlinarith

/-! ## The exact Sturm--Liouville potential -/

/-- The exact Sturm--Liouville potential of a prolate block. -/
noncomputable def prolatePotential (β γ c lam z : ℝ) : ℕ → ℝ
  | 0 => 1
  | (n + 1) => 3 / 4 + 2 * Real.pi * lam ^ 2 * (8 * ((n : ℝ) + 1) + c) - z
      - prolateDefect β γ (n + 1) - prolateDefect β γ n

theorem prolatePotential_succ (β γ c lam z : ℝ) (n : ℕ) :
    prolatePotential β γ c lam z (n + 1)
      = 3 / 4 + 2 * Real.pi * lam ^ 2 * (8 * ((n : ℝ) + 1) + c) - z
        - prolateDefect β γ (n + 1) - prolateDefect β γ n := rfl

variable {c lam z : ℝ} {q : ℕ → ℝ}

theorem prolatePotential_eq
    (hq : ∀ n : ℕ, (prolateBase β γ (n + 1) + prolateBase β γ n) / 4 + q (n + 1)
        = 3 / 4 + 2 * Real.pi * lam ^ 2 * (8 * ((n : ℝ) + 1) + c)) (n : ℕ) :
    prolatePotential β γ c lam z (n + 1)
      = prolateRho β γ (n + 1) + prolateRho β γ n + q (n + 1) - z := by
  rw [prolatePotential_succ, prolateRho_eq_sub, prolateRho_eq_sub]
  linarith [hq n]

/-! ## The limit-point case at zero prolate parameter -/

theorem prolate_diag_sum_bound (hβ : 0 ≤ β) (hγ : 2 ≤ γ)
    (hq : ∀ n : ℕ, (prolateBase β γ (n + 1) + prolateBase β γ n) / 4 + q (n + 1) = 3 / 4)
    (n : ℕ) :
    |prolateRho β γ (n + 1) + prolateRho β γ n + q (n + 1)| ≤ 3 / 4 := by
  have h1 := prolateDefect_pos (β := β) (γ := γ) (n := n) hβ hγ
  have h2 := prolateDefect_pos (β := β) (γ := γ) (n := n + 1) hβ hγ
  have h3 := prolateDefect_lt_quarter (β := β) (γ := γ) (n := n) hβ hγ
  have h4 := prolateDefect_lt_quarter (β := β) (γ := γ) (n := n + 1) hβ hγ
  have hval : prolateRho β γ (n + 1) + prolateRho β γ n + q (n + 1)
      = 3 / 4 - prolateDefect β γ (n + 1) - prolateDefect β γ n := by
    rw [prolateRho_eq_sub, prolateRho_eq_sub]
    linarith [hq n]
  rw [hval, abs_le]
  constructor <;> linarith

/-- **The prolate block at zero parameter is in the limit-point case.**  Its deficiency space at
every non-real spectral parameter is trivial. -/
theorem prolate_jacobiDeficiency_eq_bot (hβ : 0 ≤ β) (hγ : 2 ≤ γ)
    (hq : ∀ n : ℕ, (prolateBase β γ (n + 1) + prolateBase β γ n) / 4 + q (n + 1) = 3 / 4)
    (Z : ℂ) (hZ : (starRingEnd ℂ) Z ≠ Z) :
    jacobiDeficiency (prolateRho β γ) q Z = ⊥ := by
  classical
  have ha : ∀ n, prolateRho β γ n ≠ 0 := fun n => (prolateRho_pos hβ hγ).ne'
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [jacobiDeficiency, Submodule.mem_inf] at hx
  obtain ⟨hsol, hsum⟩ := hx
  have hjs : IsJacobiSolution (prolateRho β γ) q Z x := hsol
  have hx2 : Summable fun n => ‖x n‖ ^ 2 := (mem_sqSummable_iff x).mp hsum
  by_contra hne
  have hx0 : x 0 ≠ 0 := by
    intro h0
    exact hne (IsJacobiSolution.ext ha hjs ((jacobiSolutions (prolateRho β γ) q Z).zero_mem') h0)
  -- the two standard solutions
  set A : ℕ → ℂ := fun n => ((prolateRho β γ n : ℝ) : ℂ) with hAdef
  set B : ℕ → ℂ := fun n => ((q n : ℝ) : ℂ) with hBdef
  have hA : ∀ n, A n ≠ 0 := fun n => by
    simp only [hAdef, ne_eq, Complex.ofReal_eq_zero]
    exact ha n
  have hw1 : IsJacobiRec (prolateRho β γ) q Z (jacobiSol A B Z 1 0) := fun n =>
    jacobiSol_rec hA n
  have hw2 : IsJacobiRec (prolateRho β γ) q Z (jacobiSol A B Z 0 1) := fun n =>
    jacobiSol_rec hA n
  -- rigidity: every solution is square-summable
  have hs1 := summable_sq_of_boundary_solution (u := x) (w := jacobiSol A B Z 1 0)
    hjs.step hw1 hjs.base hZ hx0 hx2
  have hs2 := summable_sq_of_boundary_solution (u := x) (w := jacobiSol A B Z 0 1)
    hjs.step hw2 hjs.base hZ hx0 hx2
  -- but two square-summable solutions have vanishing Wronskian
  have hQb : ∀ n : ℕ, 1 ≤ n → ‖slPotential (prolateRho β γ) q Z n‖ ≤ 3 / 4 + ‖Z‖ := by
    intro n _
    have hb := prolate_diag_sum_bound hβ hγ hq n
    have hrw : slPotential (prolateRho β γ) q Z n
        = ((prolateRho β γ (n + 1) + prolateRho β γ n + q (n + 1) : ℝ) : ℂ) - Z := by
      simp only [slPotential]
      push_cast
      ring
    rw [hrw]
    calc ‖((prolateRho β γ (n + 1) + prolateRho β γ n + q (n + 1) : ℝ) : ℂ) - Z‖
        ≤ ‖((prolateRho β γ (n + 1) + prolateRho β γ n + q (n + 1) : ℝ) : ℂ)‖ + ‖Z‖ :=
          norm_sub_le _ _
      _ ≤ 3 / 4 + ‖Z‖ := by
          have hnorm : ‖((prolateRho β γ (n + 1) + prolateRho β γ n + q (n + 1) : ℝ) : ℂ)‖
              = |prolateRho β γ (n + 1) + prolateRho β γ n + q (n + 1)| := by
            rw [Complex.norm_real, Real.norm_eq_abs]
          rw [hnorm]
          linarith
  have hazero := crossWronskian_eq_zero_of_both_summable (a := prolateRho β γ) (b := q) (z := Z)
    (u := jacobiSol A B Z 1 0) (w := jacobiSol A B Z 0 1) (c₀ := 4) (Cq := 3 / 4 + ‖Z‖) (N₀ := 1)
    hw1 hw2 le_rfl (by norm_num)
    (fun n _ => four_sq_le_prolateRho hβ hγ) hQb (by positivity) hs1 hs2
  have hconst : crossWronskian (prolateRho β γ) (jacobiSol A B Z 1 0) (jacobiSol A B Z 0 1) 1
      = crossWronskian (prolateRho β γ) (jacobiSol A B Z 1 0) (jacobiSol A B Z 0 1) 0 :=
    crossWronskian_eq_zero_of_const hw1 hw2
  have hval : crossWronskian (prolateRho β γ) (jacobiSol A B Z 1 0) (jacobiSol A B Z 0 1) 0
      = -((prolateRho β γ 0 : ℝ) : ℂ) := by
    simp [crossWronskian]
  rw [hconst, hval] at hazero
  exact (ha 0) (by simpa using neg_eq_zero.mp hazero)

/-! ## The two archimedean prolate parity blocks -/

/-- The even-parity prolate diagonal. -/
noncomputable def prolateDiagEven (lam : ℝ) (n : ℕ) : ℝ :=
  -8 * (n : ℝ) ^ 2 - 2 * (n : ℝ) - 3 / 4 + 2 * Real.pi * lam ^ 2 * (8 * (n : ℝ) + 1)

/-- The odd-parity prolate diagonal. -/
noncomputable def prolateDiagOdd (lam : ℝ) (n : ℕ) : ℝ :=
  -8 * (n : ℝ) ^ 2 - 10 * (n : ℝ) - 15 / 4 + 2 * Real.pi * lam ^ 2 * (8 * (n : ℝ) + 5)

/-- **The even-parity radius is the parent paper's `ρ_n^+`.** -/
theorem prolateRho_even (n : ℕ) :
    prolateRho 20 5 n
      = Real.sqrt ((4 * (n : ℝ) + 1) * (4 * (n : ℝ) + 2) * (4 * (n : ℝ) + 3)
          * (4 * (n : ℝ) + 4)) / 4 := by
  unfold prolateRho prolateBase
  rw [show (16 * (n : ℝ) ^ 2 + 20 * (n : ℝ) + 5) ^ 2 - 1
      = (4 * (n : ℝ) + 1) * (4 * (n : ℝ) + 2) * (4 * (n : ℝ) + 3) * (4 * (n : ℝ) + 4) from by
    ring]

/-- **The odd-parity radius is the parent paper's `ρ_n^-`.** -/
theorem prolateRho_odd (n : ℕ) :
    prolateRho 36 19 n
      = Real.sqrt ((4 * (n : ℝ) + 3) * (4 * (n : ℝ) + 4) * (4 * (n : ℝ) + 5)
          * (4 * (n : ℝ) + 6)) / 4 := by
  unfold prolateRho prolateBase
  rw [show (16 * (n : ℝ) ^ 2 + 36 * (n : ℝ) + 19) ^ 2 - 1
      = (4 * (n : ℝ) + 3) * (4 * (n : ℝ) + 4) * (4 * (n : ℝ) + 5) * (4 * (n : ℝ) + 6) from by
    ring]

/-- **The exact even-parity potential identity.** -/
theorem prolateEven_key (lam : ℝ) (n : ℕ) :
    (prolateBase 20 5 (n + 1) + prolateBase 20 5 n) / 4 + prolateDiagEven lam (n + 1)
      = 3 / 4 + 2 * Real.pi * lam ^ 2 * (8 * ((n : ℝ) + 1) + 1) := by
  unfold prolateBase prolateDiagEven
  push_cast
  ring

/-- **The exact odd-parity potential identity.** -/
theorem prolateOdd_key (lam : ℝ) (n : ℕ) :
    (prolateBase 36 19 (n + 1) + prolateBase 36 19 n) / 4 + prolateDiagOdd lam (n + 1)
      = 3 / 4 + 2 * Real.pi * lam ^ 2 * (8 * ((n : ℝ) + 1) + 5) := by
  unfold prolateBase prolateDiagOdd
  push_cast
  ring

/-- **The even parity block is limit point at zero prolate parameter.** -/
theorem prolateEven_jacobiDeficiency_eq_bot (Z : ℂ) (hZ : (starRingEnd ℂ) Z ≠ Z) :
    jacobiDeficiency (prolateRho 20 5) (prolateDiagEven 0) Z = ⊥ := by
  refine prolate_jacobiDeficiency_eq_bot (by norm_num) (by norm_num) (fun n => ?_) Z hZ
  have := prolateEven_key 0 n
  simpa using this

/-- **The odd parity block is limit point at zero prolate parameter.** -/
theorem prolateOdd_jacobiDeficiency_eq_bot (Z : ℂ) (hZ : (starRingEnd ℂ) Z ≠ Z) :
    jacobiDeficiency (prolateRho 36 19) (prolateDiagOdd 0) Z = ⊥ := by
  refine prolate_jacobiDeficiency_eq_bot (by norm_num) (by norm_num) (fun n => ?_) Z hZ
  have := prolateOdd_key 0 n
  simpa using this

end RHTower
