import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicFisherDefect

/-!
# The iterated dyadic meta-constraint

`dyadic-squarefree-euler-fock-source-factorization`, §6, equations `(24)`–`(26)`.

Iterating `n = m² d` gives the unique tower decomposition

```text
n = d_0 · d_1² · … · d_{R-1}^{2^{R-1}} · m^{2^R},   every d_r squarefree,
```

realized here as an explicit equivalence `ℕ+ ≃ DyadTower R`.  Under it:

* `(24)` the decomposition is a bijection (`dyadicTowerEquiv`);
* `(25)` the pointed Euler state factorizes into the tower of signed squarefree parity states and
  one residual Euler state at `2^R σ` (`dyadicTowerUnitary_eulerPointedState`);
* `(26)` the Euler logarithmic observable becomes the additive tower constraint
  `log n = ∑_{r<R} 2^r log d_r + 2^R log m` (`towerLog_dyadicTowerEquiv`);
* the analytic shadow `ζ(σ) = ∏_{r<R} Z_sq(2^r σ) · ζ(2^R σ)` (`eulerMass_tower_telescope`).
-/

open Complex Set

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## The tower index type -/

/-- The `R`-fold dyadic tower index: `R` squarefree digits followed by one residual integer. -/
abbrev DyadTower : ℕ → Type
  | 0 => ℕ+
  | (R + 1) => SquarefreePNat × DyadTower R

/-- **Equation (24).**  The iterated squarefree-times-square decomposition is a bijection. -/
def dyadicTowerEquiv : (R : ℕ) → (ℕ+ ≃ DyadTower R)
  | 0 => Equiv.refl ℕ+
  | (R + 1) =>
      dyadicSquarefreeSquareEquiv.trans (Equiv.prodCongr (Equiv.refl SquarefreePNat)
        (dyadicTowerEquiv R))

@[simp] theorem dyadicTowerEquiv_zero (n : ℕ+) : dyadicTowerEquiv 0 n = n := rfl

@[simp] theorem dyadicTowerEquiv_succ (R : ℕ) (n : ℕ+) :
    dyadicTowerEquiv (R + 1) n
      = ((dyadicSquarefreeSquareEquiv n).1,
          dyadicTowerEquiv R (dyadicSquarefreeSquareEquiv n).2) := rfl

/-! ## The additive tower constraint `(26)` -/

/-- The tower logarithm: `log d_0 + 2(log d_1 + 2(… + 2 log m))`. -/
def towerLog : (R : ℕ) → DyadTower R → ℝ
  | 0 => fun m => Real.log ((m : ℕ+) : ℝ)
  | (R + 1) => fun p => Real.log ((p.1.1 : ℝ)) + 2 * towerLog R p.2

/-- **Equation (26).**  The Euler logarithmic observable is the additive tower constraint. -/
theorem towerLog_dyadicTowerEquiv : ∀ (R : ℕ) (n : ℕ+),
    Real.log ((n : ℕ+) : ℝ) = towerLog R (dyadicTowerEquiv R n)
  | 0, n => rfl
  | (R + 1), n => by
      have hIH := towerLog_dyadicTowerEquiv R (dyadicSquarefreeSquareEquiv n).2
      have hbase := dyadicSquarefreeSquareEquiv_log n
      show Real.log ((n : ℕ+) : ℝ)
          = Real.log (((dyadicSquarefreeSquareEquiv n).1.1 : ℝ))
            + 2 * towerLog R (dyadicTowerEquiv R (dyadicSquarefreeSquareEquiv n).2)
      rw [← hIH]
      exact hbase

/-! ## The tower state and its phase `(25)` -/

/-- The signed Möbius phase of a whole tower point. -/
def towerPhase : (R : ℕ) → DyadTower R → ℂ
  | 0 => fun _ => 1
  | (R + 1) => fun p =>
      ((ArithmeticFunction.moebius (p.1.1 : ℕ) : ℝ) : ℂ) * towerPhase R p.2

theorem norm_towerPhase : ∀ (R : ℕ) (t : DyadTower R), ‖towerPhase R t‖ = 1
  | 0, _ => by
      show ‖(1 : ℂ)‖ = 1
      simp
  | (R + 1), p => by
      show ‖((ArithmeticFunction.moebius (p.1.1 : ℕ) : ℝ) : ℂ) * towerPhase R p.2‖ = 1
      rw [norm_mul, norm_towerPhase R p.2, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_moebius_squarefree p.1.2]

/-- The tower state: the signed squarefree parity states at `σ, 2σ, …, 2^{R-1}σ` times the
residual Euler state at `2^R σ`. -/
def towerStateCoord : (R : ℕ) → (σ : ℝ) → DyadTower R → ℂ
  | 0, σ => fun m => eulerStateCoord σ m
  | (R + 1), σ => fun p =>
      squarefreeStateCoord σ p.1 * towerStateCoord R (2 * σ) p.2

/-- **Equation (25), coordinate form.**  The signed tower transport of the pointed Euler state is
the tower state. -/
theorem towerPhase_mul_eulerStateCoord : ∀ (R : ℕ) {σ : ℝ}, 1 < σ → ∀ n : ℕ+,
    towerPhase R (dyadicTowerEquiv R n) * eulerStateCoord σ n
      = towerStateCoord R σ (dyadicTowerEquiv R n)
  | 0, σ, _, n => by
      show (1 : ℂ) * eulerStateCoord σ n = eulerStateCoord σ n
      rw [one_mul]
  | (R + 1), σ, hσ, n => by
      have hσ2 : 1 < 2 * σ := by linarith
      have hbase := dyadicSquarefreeSignedUnitary_eulerPointedState hσ
        (dyadicSquarefreeSquareEquiv n)
      rw [dyadicSquarefreeSignedUnitary_apply, eulerPointedState_apply,
        Equiv.symm_apply_apply, dyadicMoebiusPhase] at hbase
      have hIH := towerPhase_mul_eulerStateCoord R hσ2 (dyadicSquarefreeSquareEquiv n).2
      show (((ArithmeticFunction.moebius ((dyadicSquarefreeSquareEquiv n).1.1 : ℕ) : ℝ) : ℂ)
            * towerPhase R (dyadicTowerEquiv R (dyadicSquarefreeSquareEquiv n).2))
          * eulerStateCoord σ n
        = squarefreeStateCoord σ (dyadicSquarefreeSquareEquiv n).1
          * towerStateCoord R (2 * σ) (dyadicTowerEquiv R (dyadicSquarefreeSquareEquiv n).2)
      rw [← hIH]
      linear_combination
        (towerPhase R (dyadicTowerEquiv R (dyadicSquarefreeSquareEquiv n).2)) * hbase

/-! ## The tower unitary -/

/-- The `R`-fold signed arithmetic unitary. -/
def dyadicTowerUnitary (R : ℕ) :
    EulerPositiveL2 ≃ₗᵢ[ℂ] lp (fun _ : DyadTower R => ℂ) 2 :=
  (lpReindexEquiv (dyadicTowerEquiv R)).trans
    (lpPhaseUnitary (towerPhase R) (norm_towerPhase R))

@[simp] theorem dyadicTowerUnitary_apply (R : ℕ) (x : EulerPositiveL2) (t : DyadTower R) :
    dyadicTowerUnitary R x t = towerPhase R t * x ((dyadicTowerEquiv R).symm t) := rfl

/-- **Equation (25).**  The `R`-fold signed unitary sends the pointed Euler state at `σ` to the
tower state, coordinate by coordinate. -/
theorem dyadicTowerUnitary_eulerPointedState (R : ℕ) {σ : ℝ} (hσ : 1 < σ)
    (t : DyadTower R) :
    dyadicTowerUnitary R (eulerPointedState hσ) t = towerStateCoord R σ t := by
  have h := towerPhase_mul_eulerStateCoord R hσ ((dyadicTowerEquiv R).symm t)
  rw [Equiv.apply_symm_apply] at h
  rw [dyadicTowerUnitary_apply, eulerPointedState_apply]
  exact h

/-! ## The analytic telescope `(27)` -/

/-- **Equation (27).**  `ζ(σ) = ∏_{r<R} Z_sq(2^r σ) · ζ(2^R σ)`. -/
theorem eulerMass_tower_telescope : ∀ (R : ℕ) {σ : ℝ}, 1 < σ →
    eulerMass σ
      = (∏ r ∈ Finset.range R, squarefreeMass (2 ^ r * σ)) * eulerMass (2 ^ R * σ)
  | 0, σ, _ => by simp
  | (R + 1), σ, hσ => by
      have hσ2 : 1 < 2 * σ := by linarith
      have hIH := eulerMass_tower_telescope R hσ2
      have hbase := squarefreeMass_mul_eulerMass_two_mul hσ
      rw [← hbase, hIH, Finset.prod_range_succ']
      have hrw : ∀ r : ℕ, (2 : ℝ) ^ r * (2 * σ) = 2 ^ (r + 1) * σ := by
        intro r; rw [pow_succ]; ring
      have hpow : (2 : ℝ) ^ R * (2 * σ) = 2 ^ (R + 1) * σ := by rw [pow_succ]; ring
      rw [Finset.prod_congr rfl (fun r _ => by rw [hrw r]), hpow, pow_zero, one_mul]
      ring

/-! ## The iterated affine joint cutoff `(35)` -/

/-- **Equation (35).**  Every sharp logarithmic Euler cutoff becomes the affine joint cutoff of
the whole tower, `∑_{r<R} 2^r log d_r + 2^R log m < T`, written in its exact recursive form. -/
theorem eulerLogCutoff_iff_towerCutoff (R : ℕ) (T : ℝ) (n : ℕ+) :
    Real.log ((n : ℕ+) : ℝ) < T ↔ towerLog R (dyadicTowerEquiv R n) < T := by
  rw [towerLog_dyadicTowerEquiv R n]

end RHTower
