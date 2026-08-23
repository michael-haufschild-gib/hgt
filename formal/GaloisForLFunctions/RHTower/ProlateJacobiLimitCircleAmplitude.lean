import GaloisForLFunctions.RHTower.ProlateJacobiLimitCircle
import GaloisForLFunctions.HTGeometry.RelativeApproximation

/-!
# The prolate Jacobi blocks at positive parameter

For `λ > 0` the Sturm--Liouville potential of a prolate block is `Q_n = A n + B − δ_n − δ_{n−1}`
with `A = 16πλ² > 0`, while the weight is `ρ_n = 4n² + O(n)`.  Hence `ρ_n Q_n = 4An³(1 + O(1/n))`
and the Liouville--Green drift is `−6/(√A √n)(1 + O(1/n))`.  Feeding this into the discrete
Sturm--Liouville bootstrap gives the amplitude `u_n² ≲ (ρ_n Q_n)^{-1/2} ≍ n^{-3/2}`, so every
solution is square-summable: the block is in the limit-circle case.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem forall_ge_succ {P : ℕ → Prop} {M : ℕ} (h : ∀ m, M ≤ m → P (m + 1)) :
    ∀ n, M + 1 ≤ n → P n := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact h m (by omega)

variable {β γ c lam z : ℝ}

theorem prolateDefect_le_sq (hβ : 0 ≤ β) (hγ : 2 ≤ γ) {n : ℕ} (hn : 1 ≤ n) :
    prolateDefect β γ n ≤ 1 / (64 * (n : ℝ) ^ 2) := by
  have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd := prolateDefect_pos (β := β) (γ := γ) (n := n) hβ hγ
  have hm := prolateDefect_le (β := β) (γ := γ) (n := n) hβ hγ
  have hb : 16 * (n : ℝ) ^ 2 ≤ prolateBase β γ n := by
    unfold prolateBase
    nlinarith
  have hpos : (0:ℝ) < 64 * (n : ℝ) ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  nlinarith [hm, hd, hb]

/-- **The prolate radius is `4n²` to relative order `1/n`.** -/
theorem relApprox_prolateRho (hβ : 0 ≤ β) (hγ : 2 ≤ γ) {n : ℕ} (hn : 1 ≤ n) :
    RelApprox (prolateRho β γ n) (4 * (n : ℝ) ^ 2) ((β + γ + 1) / (16 * (n : ℝ))) := by
  have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd := prolateDefect_pos (β := β) (γ := γ) (n := n) hβ hγ
  have hd4 := prolateDefect_lt_quarter (β := β) (γ := γ) (n := n) hβ hγ
  have hval : prolateRho β γ n - 4 * (n : ℝ) ^ 2
      = β * (n : ℝ) / 4 + γ / 4 - prolateDefect β γ n := by
    rw [prolateRho_eq_sub]
    unfold prolateBase
    ring
  have hrhs : (β + γ + 1) / (16 * (n : ℝ)) * (4 * (n : ℝ) ^ 2) = (β + γ + 1) * (n : ℝ) / 4 := by
    field_simp
    ring
  rw [RelApprox, hval, hrhs, abs_le]
  constructor <;> nlinarith [hγ, hβ]

/-- The exact `λ`-linear form of the potential. -/
theorem prolatePotential_succ_linear (β γ c lam z : ℝ) (n : ℕ) :
    prolatePotential β γ c lam z (n + 1)
      = 16 * Real.pi * lam ^ 2 * ((n : ℝ) + 1) + (3 / 4 + 2 * Real.pi * lam ^ 2 * c - z)
        - prolateDefect β γ (n + 1) - prolateDefect β γ n := by
  rw [prolatePotential_succ]
  ring

/-- **The prolate potential is `A n` to relative order `1/n`.** -/
theorem relApprox_prolatePotential (hβ : 0 ≤ β) (hγ : 2 ≤ γ)
    (hA : 0 < 16 * Real.pi * lam ^ 2) (n : ℕ) :
    RelApprox (prolatePotential β γ c lam z (n + 1))
      (16 * Real.pi * lam ^ 2 * ((n : ℝ) + 1))
      ((|3 / 4 + 2 * Real.pi * lam ^ 2 * c - z| + 1 / 2)
        / (16 * Real.pi * lam ^ 2) / ((n : ℝ) + 1)) := by
  have hd1 := prolateDefect_pos (β := β) (γ := γ) (n := n) hβ hγ
  have hd2 := prolateDefect_pos (β := β) (γ := γ) (n := n + 1) hβ hγ
  have hd3 := prolateDefect_lt_quarter (β := β) (γ := γ) (n := n) hβ hγ
  have hd4 := prolateDefect_lt_quarter (β := β) (γ := γ) (n := n + 1) hβ hγ
  have hn1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have hval : prolatePotential β γ c lam z (n + 1)
      - 16 * Real.pi * lam ^ 2 * ((n : ℝ) + 1)
      = (3 / 4 + 2 * Real.pi * lam ^ 2 * c - z)
        - prolateDefect β γ (n + 1) - prolateDefect β γ n := by
    rw [prolatePotential_succ_linear]
    ring
  have hrhs : (|3 / 4 + 2 * Real.pi * lam ^ 2 * c - z| + 1 / 2)
        / (16 * Real.pi * lam ^ 2) / ((n : ℝ) + 1)
        * (16 * Real.pi * lam ^ 2 * ((n : ℝ) + 1))
      = |3 / 4 + 2 * Real.pi * lam ^ 2 * c - z| + 1 / 2 := by
    have hD : (16 * Real.pi * lam ^ 2) ≠ 0 := ne_of_gt hA
    have hM : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hn1
    have hlam : lam ≠ 0 := by
      intro h
      rw [h] at hA
      simp at hA
    field_simp
  rw [RelApprox, hval, hrhs, abs_le]
  have habs := abs_le.mp (le_refl |3 / 4 + 2 * Real.pi * lam ^ 2 * c - z|)
  have hlb := neg_abs_le (3 / 4 + 2 * Real.pi * lam ^ 2 * c - z)
  have hub := le_abs_self (3 / 4 + 2 * Real.pi * lam ^ 2 * c - z)
  constructor <;> linarith

/-! ## A single relative-error constant -/

/-- A constant dominating every relative error of a prolate block. -/
noncomputable def prolateErr (β γ c lam z : ℝ) : ℝ :=
  (β + γ + 1) / 16 + (|3 / 4 + 2 * Real.pi * lam ^ 2 * c - z| + 1 / 2)
    / (16 * Real.pi * lam ^ 2) + 7

theorem seven_le_prolateErr (hβ : 0 ≤ β) (hγ : 2 ≤ γ) (hA : 0 < 16 * Real.pi * lam ^ 2) :
    7 ≤ prolateErr β γ c lam z := by
  unfold prolateErr
  have h1 : (0:ℝ) ≤ (β + γ + 1) / 16 := by positivity
  have h2 : (0:ℝ) ≤ (|3 / 4 + 2 * Real.pi * lam ^ 2 * c - z| + 1 / 2)
      / (16 * Real.pi * lam ^ 2) := by positivity
  linarith

theorem prolateErr_pos (hβ : 0 ≤ β) (hγ : 2 ≤ γ) (hA : 0 < 16 * Real.pi * lam ^ 2) :
    0 < prolateErr β γ c lam z := by
  have := seven_le_prolateErr (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA
  linarith

theorem relApprox_rho_err (hβ : 0 ≤ β) (hγ : 2 ≤ γ) (hA : 0 < 16 * Real.pi * lam ^ 2)
    (n : ℕ) :
    RelApprox (prolateRho β γ (n + 1)) (4 * ((n : ℝ) + 1) ^ 2)
      (prolateErr β γ c lam z / ((n : ℝ) + 1)) := by
  have h := relApprox_prolateRho (β := β) (γ := γ) (n := n + 1) hβ hγ (by omega)
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast] at h
  refine h.mono (by positivity) ?_
  have hle : (β + γ + 1) / 16 ≤ prolateErr β γ c lam z := by
    unfold prolateErr
    have h2 : (0:ℝ) ≤ (|3 / 4 + 2 * Real.pi * lam ^ 2 * c - z| + 1 / 2)
        / (16 * Real.pi * lam ^ 2) := by positivity
    linarith
  have hx : (0:ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_le_div_iff₀ (by positivity) hx]
  nlinarith [hle, hx]

theorem relApprox_Q_err (hβ : 0 ≤ β) (hγ : 2 ≤ γ) (hA : 0 < 16 * Real.pi * lam ^ 2)
    (n : ℕ) :
    RelApprox (prolatePotential β γ c lam z (n + 1)) (16 * Real.pi * lam ^ 2 * ((n : ℝ) + 1))
      (prolateErr β γ c lam z / ((n : ℝ) + 1)) := by
  have h := relApprox_prolatePotential (β := β) (γ := γ) (c := c) (lam := lam) (z := z)
    hβ hγ hA n
  refine h.mono (by positivity) ?_
  have hle : (|3 / 4 + 2 * Real.pi * lam ^ 2 * c - z| + 1 / 2) / (16 * Real.pi * lam ^ 2)
      ≤ prolateErr β γ c lam z := by
    unfold prolateErr
    have h1 : (0:ℝ) ≤ (β + γ + 1) / 16 := by positivity
    linarith
  exact div_le_div_of_nonneg_right hle (by positivity)

/-! ## Shifted references -/

theorem relApprox_shift_sq {x : ℝ} (hx : 1 ≤ x) :
    RelApprox (4 * (x + 1) ^ 2) (4 * x ^ 2) (3 / x) := by
  have hx0 : (0:ℝ) < x := by linarith
  have hval : 4 * (x + 1) ^ 2 - 4 * x ^ 2 = 8 * x + 4 := by ring
  have hrhs : 3 / x * (4 * x ^ 2) = 12 * x := by field_simp; ring
  rw [RelApprox, hval, hrhs, abs_le]
  constructor <;> linarith

theorem relApprox_shift_cube {A x : ℝ} (hA : 0 < A) (hx : 1 ≤ x) :
    RelApprox (4 * A * (x + 1) ^ 3) (4 * A * x ^ 3) (7 / x) := by
  have hx0 : (0:ℝ) < x := by linarith
  have hval : 4 * A * (x + 1) ^ 3 - 4 * A * x ^ 3 = 4 * A * (3 * x ^ 2 + 3 * x + 1) := by ring
  have hrhs : 7 / x * (4 * A * x ^ 3) = 28 * A * x ^ 2 := by field_simp; ring
  have hquad : (0:ℝ) ≤ 4 * x ^ 2 - 3 * x - 1 := by nlinarith
  rw [RelApprox, hval, hrhs, abs_le]
  constructor <;> nlinarith [mul_nonneg hA.le hquad, hA, hx0]

/-! ## The Liouville--Green weight -/

/-- The Liouville--Green weight `ρ_n Q_n` of a prolate block. -/
noncomputable def prolateWeight (β γ c lam z : ℝ) (n : ℕ) : ℝ :=
  slgWeight (prolateRho β γ) (prolatePotential β γ c lam z) n

theorem prolateWeight_eq (β γ c lam z : ℝ) (n : ℕ) :
    prolateWeight β γ c lam z n
      = prolateRho β γ n * prolatePotential β γ c lam z n := rfl

theorem prolateWeight_succ_sub (β γ c lam z : ℝ) (n : ℕ) :
    prolateWeight β γ c lam z (n + 2) - prolateWeight β γ c lam z (n + 1)
      = prolateRho β γ (n + 2)
          * (prolatePotential β γ c lam z (n + 2) - prolatePotential β γ c lam z (n + 1))
        + prolatePotential β γ c lam z (n + 1)
          * (prolateRho β γ (n + 2) - prolateRho β γ (n + 1)) := by
  simp only [prolateWeight_eq]
  ring

/-! ## Increments of the radius and the potential -/

theorem prolateRho_succ_sub_eq (β γ : ℝ) (n : ℕ) :
    prolateRho β γ (n + 2) - prolateRho β γ (n + 1)
      = 8 * (n : ℝ) + 12 + β / 4 - prolateDefect β γ (n + 2) + prolateDefect β γ (n + 1) := by
  rw [prolateRho_eq_sub, prolateRho_eq_sub]
  unfold prolateBase
  push_cast
  ring

theorem prolatePotential_succ_sub_eq (β γ c lam z : ℝ) (n : ℕ) :
    prolatePotential β γ c lam z (n + 2) - prolatePotential β γ c lam z (n + 1)
      = 16 * Real.pi * lam ^ 2 - prolateDefect β γ (n + 2) + prolateDefect β γ n := by
  rw [prolatePotential_succ_linear, prolatePotential_succ_linear]
  push_cast
  ring

theorem relApprox_drho (hβ : 0 ≤ β) (hγ : 2 ≤ γ) (hA : 0 < 16 * Real.pi * lam ^ 2) (n : ℕ) :
    RelApprox (prolateRho β γ (n + 2) - prolateRho β γ (n + 1)) (8 * ((n : ℝ) + 1))
      (prolateErr β γ c lam z / ((n : ℝ) + 1)) := by
  have hd1 := prolateDefect_pos (β := β) (γ := γ) (n := n + 1) hβ hγ
  have hd2 := prolateDefect_pos (β := β) (γ := γ) (n := n + 2) hβ hγ
  have hd3 := prolateDefect_lt_quarter (β := β) (γ := γ) (n := n + 1) hβ hγ
  have hd4 := prolateDefect_lt_quarter (β := β) (γ := γ) (n := n + 2) hβ hγ
  have hx : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have hK : 7 + β / 16 ≤ prolateErr β γ c lam z := by
    unfold prolateErr
    have h2 : (0:ℝ) ≤ (|3 / 4 + 2 * Real.pi * lam ^ 2 * c - z| + 1 / 2)
        / (16 * Real.pi * lam ^ 2) := by positivity
    have h1 : β / 16 ≤ (β + γ + 1) / 16 := by linarith
    linarith
  have hval : prolateRho β γ (n + 2) - prolateRho β γ (n + 1) - 8 * ((n : ℝ) + 1)
      = 4 + β / 4 - prolateDefect β γ (n + 2) + prolateDefect β γ (n + 1) := by
    rw [prolateRho_succ_sub_eq]
    ring
  have hrhs : prolateErr β γ c lam z / ((n : ℝ) + 1) * (8 * ((n : ℝ) + 1))
      = 8 * prolateErr β γ c lam z := by field_simp
  rw [RelApprox, hval, hrhs, abs_le]
  constructor <;> nlinarith [hK, hβ]

theorem relApprox_dQ (hβ : 0 ≤ β) (hγ : 2 ≤ γ) (hA : 0 < 16 * Real.pi * lam ^ 2)
    {n : ℕ} (hn : 1 ≤ n) :
    RelApprox (prolatePotential β γ c lam z (n + 2) - prolatePotential β γ c lam z (n + 1))
      (16 * Real.pi * lam ^ 2) (prolateErr β γ c lam z / ((n : ℝ) + 1)) := by
  have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd1 := prolateDefect_pos (β := β) (γ := γ) (n := n) hβ hγ
  have hd2 := prolateDefect_pos (β := β) (γ := γ) (n := n + 2) hβ hγ
  have hb1 := prolateDefect_le_sq (β := β) (γ := γ) (n := n) hβ hγ hn
  have hb2 := prolateDefect_le_sq (β := β) (γ := γ) (n := n + 2) hβ hγ (by omega)
  have hx : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have hK : (1 / 2) / (16 * Real.pi * lam ^ 2) ≤ prolateErr β γ c lam z := by
    unfold prolateErr
    have h1 : (0:ℝ) ≤ (β + γ + 1) / 16 := by positivity
    have h2 : (1 / 2 : ℝ) / (16 * Real.pi * lam ^ 2)
        ≤ (|3 / 4 + 2 * Real.pi * lam ^ 2 * c - z| + 1 / 2) / (16 * Real.pi * lam ^ 2) := by
      have hnum : (1 / 2 : ℝ) ≤ |3 / 4 + 2 * Real.pi * lam ^ 2 * c - z| + 1 / 2 := by
        have := abs_nonneg (3 / 4 + 2 * Real.pi * lam ^ 2 * c - z)
        linarith
      exact div_le_div_of_nonneg_right hnum hA.le
    linarith
  have hKA : 1 / 2 ≤ prolateErr β γ c lam z * (16 * Real.pi * lam ^ 2) := by
    rw [div_le_iff₀ hA] at hK
    linarith
  have hval : prolatePotential β γ c lam z (n + 2) - prolatePotential β γ c lam z (n + 1)
      - 16 * Real.pi * lam ^ 2
      = -prolateDefect β γ (n + 2) + prolateDefect β γ n := by
    rw [prolatePotential_succ_sub_eq]
    ring
  have hrhs : prolateErr β γ c lam z / ((n : ℝ) + 1) * (16 * Real.pi * lam ^ 2)
      = prolateErr β γ c lam z * (16 * Real.pi * lam ^ 2) / ((n : ℝ) + 1) := by
    field_simp
  have hsmall : prolateDefect β γ n ≤ 1 / (2 * ((n : ℝ) + 1)) := by
    have hcalc : (1:ℝ) / (64 * (n : ℝ) ^ 2) ≤ 1 / (2 * ((n : ℝ) + 1)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith
    linarith
  have hsmall2 : prolateDefect β γ (n + 2) ≤ 1 / (2 * ((n : ℝ) + 1)) := by
    have hcast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    rw [hcast] at hb2
    have hcalc : (1:ℝ) / (64 * ((n : ℝ) + 2) ^ 2) ≤ 1 / (2 * ((n : ℝ) + 1)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith
    linarith
  have hbig : 1 / (2 * ((n : ℝ) + 1))
      ≤ prolateErr β γ c lam z * (16 * Real.pi * lam ^ 2) / ((n : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) hx]
    nlinarith [hKA, hx]
  rw [RelApprox, hval, hrhs, abs_le]
  constructor <;> linarith

/-! ## The Liouville--Green drift of a prolate block -/

theorem neg_drift_form (a bb d r : ℝ) : -((a - bb) / d * r) = ((bb - a) * r) / d := by
  rw [div_mul_eq_mul_div, ← neg_div]
  congr 1
  ring

theorem sqrt_weight_ref {A x : ℝ} (hA : 0 < A) (hx : 0 < x) :
    Real.sqrt (4 * A * x ^ 3) = 2 * Real.sqrt A * x * Real.sqrt x := by
  have hsq : (2 * Real.sqrt A * x * Real.sqrt x) ^ 2 = 4 * A * x ^ 3 := by
    have h1 : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA.le
    have h2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
    calc (2 * Real.sqrt A * x * Real.sqrt x) ^ 2
        = 4 * (Real.sqrt A ^ 2) * x ^ 2 * (Real.sqrt x ^ 2) := by ring
      _ = 4 * A * x ^ 3 := by rw [h1, h2]; ring
  rw [← hsq, Real.sqrt_sq (by positivity)]

/-! ## Composed weight approximations -/

section Composed

theorem relApprox_weight_succ (hβ : 0 ≤ β) (hγ : 2 ≤ γ)
    (hA : 0 < 16 * Real.pi * lam ^ 2) {n : ℕ}
    (hbig : 100 * prolateErr β γ c lam z ≤ (n : ℝ) + 1) :
    RelApprox (prolateWeight β γ c lam z (n + 1))
      (4 * (16 * Real.pi * lam ^ 2) * ((n : ℝ) + 1) ^ 3)
      (3 * (prolateErr β γ c lam z / ((n : ℝ) + 1))) := by
  have hK7 : 7 ≤ prolateErr β γ c lam z := seven_le_prolateErr hβ hγ hA
  have hx0 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have hKpos := prolateErr_pos (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA
  have he0 : 0 ≤ prolateErr β γ c lam z / ((n : ℝ) + 1) := div_nonneg hKpos.le hx0.le
  have he1 : prolateErr β γ c lam z / ((n : ℝ) + 1) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ hx0 (by norm_num)]
    linarith
  have h := (relApprox_rho_err (c := c) (z := z) hβ hγ hA n).mul (by positivity) (by positivity)
    (by linarith) (relApprox_Q_err hβ hγ hA n)
  rw [show (4 * ((n : ℝ) + 1) ^ 2) * (16 * Real.pi * lam ^ 2 * ((n : ℝ) + 1))
      = 4 * (16 * Real.pi * lam ^ 2) * ((n : ℝ) + 1) ^ 3 from by ring] at h
  exact h.mono (by positivity) (by nlinarith)

theorem relApprox_rho_succ2 (hβ : 0 ≤ β) (hγ : 2 ≤ γ)
    (hA : 0 < 16 * Real.pi * lam ^ 2) {n : ℕ}
    (hbig : 100 * prolateErr β γ c lam z ≤ (n : ℝ) + 1) :
    RelApprox (prolateRho β γ (n + 2)) (4 * ((n : ℝ) + 1) ^ 2)
      (3 * (prolateErr β γ c lam z / ((n : ℝ) + 1))) := by
  have hK7 : 7 ≤ prolateErr β γ c lam z := seven_le_prolateErr hβ hγ hA
  have hx0 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have hx1 : (1:ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hKpos := prolateErr_pos (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA
  have he0 : 0 ≤ prolateErr β γ c lam z / ((n : ℝ) + 1) := div_nonneg hKpos.le hx0.le
  have he1 : prolateErr β γ c lam z / ((n : ℝ) + 1) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ hx0 (by norm_num)]
    linarith
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have h0 := relApprox_rho_err (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA (n + 1)
  rw [hcast] at h0
  have hstep : RelApprox (prolateRho β γ (n + 2)) (4 * (((n : ℝ) + 1) + 1) ^ 2)
      (prolateErr β γ c lam z / ((n : ℝ) + 1)) := by
    refine h0.mono (by positivity) ?_
    exact div_le_div_of_nonneg_left (by linarith) hx0 (by linarith)
  have hsh : RelApprox (4 * (((n : ℝ) + 1) + 1) ^ 2) (4 * ((n : ℝ) + 1) ^ 2)
      (prolateErr β γ c lam z / ((n : ℝ) + 1)) := by
    refine (relApprox_shift_sq (x := (n : ℝ) + 1) hx1).mono (by positivity) ?_
    exact div_le_div_of_nonneg_right (by linarith) hx0.le
  have h := hstep.trans (by positivity) (by positivity) hsh
  exact h.mono (by positivity) (by nlinarith)

theorem relApprox_weight_succ2 (hβ : 0 ≤ β) (hγ : 2 ≤ γ)
    (hA : 0 < 16 * Real.pi * lam ^ 2) {n : ℕ}
    (hbig : 100 * prolateErr β γ c lam z ≤ (n : ℝ) + 1) :
    RelApprox (prolateWeight β γ c lam z (n + 2))
      (4 * (16 * Real.pi * lam ^ 2) * ((n : ℝ) + 1) ^ 3)
      (5 * (prolateErr β γ c lam z / ((n : ℝ) + 1))) := by
  have hK7 : 7 ≤ prolateErr β γ c lam z := seven_le_prolateErr hβ hγ hA
  have hx0 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have hx1 : (1:ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hKpos := prolateErr_pos (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA
  have he0 : 0 ≤ prolateErr β γ c lam z / ((n : ℝ) + 1) := div_nonneg hKpos.le hx0.le
  have he1 : prolateErr β γ c lam z / ((n : ℝ) + 1) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ hx0 (by norm_num)]
    linarith
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hρ2 : RelApprox (prolateRho β γ (n + 2)) (4 * (((n : ℝ) + 1) + 1) ^ 2)
      (prolateErr β γ c lam z / ((n : ℝ) + 1)) := by
    have h0 := relApprox_rho_err (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA (n + 1)
    rw [hcast] at h0
    refine h0.mono (by positivity) ?_
    exact div_le_div_of_nonneg_left (by linarith) hx0 (by linarith)
  have hQ2 : RelApprox (prolatePotential β γ c lam z (n + 2))
      (16 * Real.pi * lam ^ 2 * (((n : ℝ) + 1) + 1))
      (prolateErr β γ c lam z / ((n : ℝ) + 1)) := by
    have h0 := relApprox_Q_err (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA (n + 1)
    rw [hcast] at h0
    refine h0.mono (by positivity) ?_
    exact div_le_div_of_nonneg_left (by linarith) hx0 (by linarith)
  have hprod := hρ2.mul (by positivity) (by positivity) (by linarith) hQ2
  rw [show (4 * (((n : ℝ) + 1) + 1) ^ 2) * (16 * Real.pi * lam ^ 2 * (((n : ℝ) + 1) + 1))
      = 4 * (16 * Real.pi * lam ^ 2) * (((n : ℝ) + 1) + 1) ^ 3 from by ring] at hprod
  have hsh : RelApprox (4 * (16 * Real.pi * lam ^ 2) * (((n : ℝ) + 1) + 1) ^ 3)
      (4 * (16 * Real.pi * lam ^ 2) * ((n : ℝ) + 1) ^ 3)
      (prolateErr β γ c lam z / ((n : ℝ) + 1)) := by
    refine (relApprox_shift_cube (A := 16 * Real.pi * lam ^ 2) (x := (n : ℝ) + 1)
      hA hx1).mono (by positivity) ?_
    exact div_le_div_of_nonneg_right (by linarith) hx0.le
  have hcomb := (hprod.mono (by positivity)
    (by nlinarith : prolateErr β γ c lam z / ((n : ℝ) + 1)
        + prolateErr β γ c lam z / ((n : ℝ) + 1)
        + prolateErr β γ c lam z / ((n : ℝ) + 1) * (prolateErr β γ c lam z / ((n : ℝ) + 1))
      ≤ 3 * (prolateErr β γ c lam z / ((n : ℝ) + 1)))).trans
      (by positivity) (by positivity) hsh
  exact hcomb.mono (by positivity) (by nlinarith)

theorem relApprox_sqrt_weight_succ2 (hβ : 0 ≤ β) (hγ : 2 ≤ γ)
    (hA : 0 < 16 * Real.pi * lam ^ 2) {n : ℕ}
    (hbig : 100 * prolateErr β γ c lam z ≤ (n : ℝ) + 1) :
    RelApprox (Real.sqrt (prolateWeight β γ c lam z (n + 2)))
      (2 * Real.sqrt (16 * Real.pi * lam ^ 2) * ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))
      (5 * (prolateErr β γ c lam z / ((n : ℝ) + 1))) := by
  have hK7 : 7 ≤ prolateErr β γ c lam z := seven_le_prolateErr hβ hγ hA
  have hx0 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have he1 : prolateErr β γ c lam z / ((n : ℝ) + 1) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ hx0 (by norm_num)]
    linarith
  have h := (relApprox_weight_succ2 hβ hγ hA hbig).sqrt (by positivity) (by linarith)
  rwa [sqrt_weight_ref hA hx0] at h

theorem relApprox_dW (hβ : 0 ≤ β) (hγ : 2 ≤ γ)
    (hA : 0 < 16 * Real.pi * lam ^ 2) {n : ℕ} (hn : 1 ≤ n)
    (hbig : 100 * prolateErr β γ c lam z ≤ (n : ℝ) + 1) :
    RelApprox (prolateWeight β γ c lam z (n + 2) - prolateWeight β γ c lam z (n + 1))
      (12 * (16 * Real.pi * lam ^ 2) * ((n : ℝ) + 1) ^ 2)
      (5 * (prolateErr β γ c lam z / ((n : ℝ) + 1))) := by
  have hK7 : 7 ≤ prolateErr β γ c lam z := seven_le_prolateErr hβ hγ hA
  have hx0 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have hKpos := prolateErr_pos (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA
  have he0 : 0 ≤ prolateErr β γ c lam z / ((n : ℝ) + 1) := div_nonneg hKpos.le hx0.le
  have he1 : prolateErr β γ c lam z / ((n : ℝ) + 1) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ hx0 (by norm_num)]
    linarith
  have T1 := (relApprox_rho_succ2 hβ hγ hA hbig).mul (by positivity) hA (by linarith)
    (relApprox_dQ hβ hγ hA hn)
  have T2 := (relApprox_Q_err (β := β) (γ := γ) (c := c) (lam := lam) (z := z)
    hβ hγ hA n).mul (by positivity) (by positivity) (by linarith)
    (relApprox_drho (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA n)
  have T1' := T1.mono (by positivity)
    (by nlinarith : 3 * (prolateErr β γ c lam z / ((n : ℝ) + 1))
        + prolateErr β γ c lam z / ((n : ℝ) + 1)
        + 3 * (prolateErr β γ c lam z / ((n : ℝ) + 1))
          * (prolateErr β γ c lam z / ((n : ℝ) + 1))
      ≤ 5 * (prolateErr β γ c lam z / ((n : ℝ) + 1)))
  have T2' := T2.mono (by positivity)
    (by nlinarith : prolateErr β γ c lam z / ((n : ℝ) + 1)
        + prolateErr β γ c lam z / ((n : ℝ) + 1)
        + prolateErr β γ c lam z / ((n : ℝ) + 1) * (prolateErr β γ c lam z / ((n : ℝ) + 1))
      ≤ 5 * (prolateErr β γ c lam z / ((n : ℝ) + 1)))
  have h := T1'.add (by positivity) (by positivity) T2'
  rw [show 4 * ((n : ℝ) + 1) ^ 2 * (16 * Real.pi * lam ^ 2)
      + 16 * Real.pi * lam ^ 2 * ((n : ℝ) + 1) * (8 * ((n : ℝ) + 1))
      = 12 * (16 * Real.pi * lam ^ 2) * ((n : ℝ) + 1) ^ 2 from by ring] at h
  rw [prolateWeight_succ_sub]
  simpa using h

end Composed

set_option maxHeartbeats 1000000 in
/-- **The Liouville--Green drift of a prolate block is `−6/(√A √n)` to relative order `1/n`.** -/
theorem relApprox_slgAbelDrift (hβ : 0 ≤ β) (hγ : 2 ≤ γ)
    (hA : 0 < 16 * Real.pi * lam ^ 2) {n : ℕ} (hn : 1 ≤ n)
    (hbig : 100 * prolateErr β γ c lam z ≤ (n : ℝ) + 1) :
    RelApprox (-(slgAbelDrift (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)))
      (6 / (Real.sqrt (16 * Real.pi * lam ^ 2) * Real.sqrt ((n : ℝ) + 1)))
      (20 * (prolateErr β γ c lam z / ((n : ℝ) + 1))) := by
  have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set A : ℝ := 16 * Real.pi * lam ^ 2 with hAdef
  set K : ℝ := prolateErr β γ c lam z with hKdef
  set x : ℝ := (n : ℝ) + 1 with hxdef
  have hK7 : 7 ≤ K := seven_le_prolateErr hβ hγ hA
  have hx2 : (2:ℝ) ≤ x := by rw [hxdef]; linarith
  have hx0 : (0:ℝ) < x := by linarith
  set e : ℝ := K / x with hedef
  have he0 : 0 ≤ e := by rw [hedef]; positivity
  have he1 : e ≤ 1 / 100 := by
    rw [hedef, div_le_div_iff₀ hx0 (by norm_num)]
    linarith [hbig]
  have hcast : ((n + 1 : ℕ) : ℝ) = x := by rw [hxdef]; push_cast; ring
  -- the four basic approximations
  have Rρ1 : RelApprox (prolateRho β γ (n + 1)) (4 * x ^ 2) e :=
    relApprox_rho_err (c := c) (z := z) hβ hγ hA n
  have RQ1 : RelApprox (prolatePotential β γ c lam z (n + 1)) (A * x) e :=
    relApprox_Q_err hβ hγ hA n
  have Rρ2a : RelApprox (prolateRho β γ (n + 2)) (4 * (x + 1) ^ 2) e := by
    have h := relApprox_rho_err (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA (n + 1)
    rw [hcast] at h
    refine h.mono (by positivity) ?_
    rw [hedef]
    exact div_le_div_of_nonneg_left (by linarith) hx0 (by linarith)
  have RQ2a : RelApprox (prolatePotential β γ c lam z (n + 2)) (A * (x + 1)) e := by
    have h := relApprox_Q_err (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA (n + 1)
    rw [hcast] at h
    refine h.mono (by positivity) ?_
    rw [hedef]
    exact div_le_div_of_nonneg_left (by linarith) hx0 (by linarith)
  -- weights
  have RW1 : RelApprox (prolateWeight β γ c lam z (n + 1)) (4 * A * x ^ 3) (3 * e) := by
    have h := Rρ1.mul (by positivity) (by positivity) (by linarith) RQ1
    rw [show (4 * x ^ 2) * (A * x) = 4 * A * x ^ 3 from by ring] at h
    exact h.mono (by positivity) (by nlinarith)
  have RW2a : RelApprox (prolateWeight β γ c lam z (n + 2)) (4 * A * (x + 1) ^ 3) (3 * e) := by
    have h := Rρ2a.mul (by positivity) (by positivity) (by linarith) RQ2a
    rw [show (4 * (x + 1) ^ 2) * (A * (x + 1)) = 4 * A * (x + 1) ^ 3 from by ring] at h
    exact h.mono (by positivity) (by nlinarith)
  have Rshift3 : RelApprox (4 * A * (x + 1) ^ 3) (4 * A * x ^ 3) e := by
    have h := relApprox_shift_cube (A := A) (x := x) hA (by linarith)
    refine h.mono (by positivity) ?_
    rw [hedef]
    exact div_le_div_of_nonneg_right (by linarith) hx0.le
  have RW2 : RelApprox (prolateWeight β γ c lam z (n + 2)) (4 * A * x ^ 3) (5 * e) := by
    have h := RW2a.trans (by positivity) (by positivity) Rshift3
    exact h.mono (by positivity) (by nlinarith)
  have RsqrtW2 : RelApprox (Real.sqrt (prolateWeight β γ c lam z (n + 2)))
      (2 * Real.sqrt A * x * Real.sqrt x) (5 * e) := by
    have h := RW2.sqrt (by positivity) (by linarith)
    rwa [sqrt_weight_ref hA hx0] at h
  -- increments
  have RdQ : RelApprox (prolatePotential β γ c lam z (n + 2)
      - prolatePotential β γ c lam z (n + 1)) A e := relApprox_dQ hβ hγ hA hn
  have RdRho : RelApprox (prolateRho β γ (n + 2) - prolateRho β γ (n + 1)) (8 * x) e := by
    have h := relApprox_drho (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA n
    rw [← hxdef] at h
    exact h
  have Rshift2 : RelApprox (4 * (x + 1) ^ 2) (4 * x ^ 2) e := by
    have h := relApprox_shift_sq (x := x) (by linarith)
    refine h.mono (by positivity) ?_
    rw [hedef]
    exact div_le_div_of_nonneg_right (by linarith) hx0.le
  have Rρ2 : RelApprox (prolateRho β γ (n + 2)) (4 * x ^ 2) (3 * e) := by
    have h := Rρ2a.trans (by positivity) (by positivity) Rshift2
    exact h.mono (by positivity) (by nlinarith)
  have T1 : RelApprox (prolateRho β γ (n + 2)
      * (prolatePotential β γ c lam z (n + 2) - prolatePotential β γ c lam z (n + 1)))
      (4 * x ^ 2 * A) (5 * e) := by
    have h := Rρ2.mul (by positivity) hA (by linarith) RdQ
    exact h.mono (by positivity) (by nlinarith)
  have T2 : RelApprox (prolatePotential β γ c lam z (n + 1)
      * (prolateRho β γ (n + 2) - prolateRho β γ (n + 1))) (A * x * (8 * x)) (3 * e) := by
    have h := RQ1.mul (by positivity) (by positivity) (by linarith) RdRho
    exact h.mono (by positivity) (by nlinarith)
  have RdW : RelApprox (prolateWeight β γ c lam z (n + 2)
      - prolateWeight β γ c lam z (n + 1)) (12 * A * x ^ 2) (5 * e) := by
    have h := T1.add (by positivity) (by positivity) T2
    rw [show 4 * x ^ 2 * A + A * x * (8 * x) = 12 * A * x ^ 2 from by ring] at h
    rw [prolateWeight_succ_sub]
    refine h.mono (by positivity) ?_
    rw [max_le_iff]
    constructor <;> linarith
  -- numerator and denominator
  have RNum : RelApprox ((prolateWeight β γ c lam z (n + 2)
      - prolateWeight β γ c lam z (n + 1)) * prolateRho β γ (n + 1))
      (48 * A * x ^ 4) (7 * e) := by
    have h := RdW.mul (by positivity) (by positivity) (by linarith) Rρ1
    rw [show 12 * A * x ^ 2 * (4 * x ^ 2) = 48 * A * x ^ 4 from by ring] at h
    exact h.mono (by positivity) (by nlinarith)
  have RDen : RelApprox (prolateWeight β γ c lam z (n + 1)
      * Real.sqrt (prolateWeight β γ c lam z (n + 2)))
      (8 * A * Real.sqrt A * x ^ 4 * Real.sqrt x) (9 * e) := by
    have h := RW1.mul (by positivity) (by positivity) (by linarith) RsqrtW2
    rw [show 4 * A * x ^ 3 * (2 * Real.sqrt A * x * Real.sqrt x)
        = 8 * A * Real.sqrt A * x ^ 4 * Real.sqrt x from by ring] at h
    exact h.mono (by positivity) (by nlinarith)
  -- the quotient
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have RQuot := RNum.div (by positivity) (by positivity) (by linarith) RDen
  have hrefeq : 48 * A * x ^ 4 / (8 * A * Real.sqrt A * x ^ 4 * Real.sqrt x)
      = 6 / (Real.sqrt A * Real.sqrt x) := by
    field_simp
    ring
  rw [hrefeq] at RQuot
  have hform : -(slgAbelDrift (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1))
      = (prolateWeight β γ c lam z (n + 2) - prolateWeight β γ c lam z (n + 1))
          * prolateRho β γ (n + 1)
        / (prolateWeight β γ c lam z (n + 1)
          * Real.sqrt (prolateWeight β γ c lam z (n + 2))) := by
    simp only [slgAbelDrift, slgDrift, prolateWeight]
    exact neg_drift_form _ _ _ _
  rw [hform]
  refine RQuot.mono (by positivity) ?_
  rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - 9 * e)]
  nlinarith [he0, he1]

/-! ## Two-sided bounds and the control coefficient -/

theorem relApprox_sqrt_weight_succ (hβ : 0 ≤ β) (hγ : 2 ≤ γ)
    (hA : 0 < 16 * Real.pi * lam ^ 2) {n : ℕ}
    (hbig : 100 * prolateErr β γ c lam z ≤ (n : ℝ) + 1) :
    RelApprox (Real.sqrt (prolateWeight β γ c lam z (n + 1)))
      (2 * Real.sqrt (16 * Real.pi * lam ^ 2) * ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))
      (3 * (prolateErr β γ c lam z / ((n : ℝ) + 1))) := by
  have hK7 : 7 ≤ prolateErr β γ c lam z := seven_le_prolateErr hβ hγ hA
  have hx0 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have he1 : prolateErr β γ c lam z / ((n : ℝ) + 1) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ hx0 (by norm_num)]
    linarith
  have h := (relApprox_weight_succ hβ hγ hA hbig).sqrt (by positivity) (by linarith)
  rwa [sqrt_weight_ref hA hx0] at h

set_option maxHeartbeats 2000000 in
/-- **The per-step control coefficient of a prolate block is `O(n^{-3/2})`.** -/
theorem slgControl_le (hβ : 0 ≤ β) (hγ : 2 ≤ γ)
    (hA : 0 < 16 * Real.pi * lam ^ 2) {n : ℕ} (hn : 1 ≤ n)
    (hbig : 100 * prolateErr β γ c lam z ≤ (n : ℝ) + 1) :
    slgControl (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)
      ≤ (15 + 54 * Real.sqrt (16 * Real.pi * lam ^ 2))
        / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)) := by
  have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- gather all relative approximations before abbreviating
  have hρ1 := relApprox_rho_err (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA n
  have hQ1 := relApprox_Q_err (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA n
  have hs1 := relApprox_sqrt_weight_succ hβ hγ hA hbig
  have hs2 := relApprox_sqrt_weight_succ2 hβ hγ hA hbig
  have hW1 := relApprox_weight_succ hβ hγ hA hbig
  have hW2 := relApprox_weight_succ2 hβ hγ hA hbig
  have hdW := relApprox_dW hβ hγ hA hn hbig
  have hdrho := relApprox_drho (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA n
  have hdrift := relApprox_slgAbelDrift hβ hγ hA hn hbig
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hQ2r := relApprox_Q_err (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA (n + 1)
  rw [hcast] at hQ2r
  set A : ℝ := 16 * Real.pi * lam ^ 2 with hAdef
  set x : ℝ := (n : ℝ) + 1 with hxdef
  set K : ℝ := prolateErr β γ c lam z with hKdef
  have hK7 : 7 ≤ K := seven_le_prolateErr hβ hγ hA
  have hx2 : (2:ℝ) ≤ x := by rw [hxdef]; linarith
  have hx0 : (0:ℝ) < x := by linarith
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  have hsA2 : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA.le
  have hsxx : Real.sqrt x ≤ x := by nlinarith [hsx, hsx2, hx2]
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hsxne : Real.sqrt x ≠ 0 := ne_of_gt hsx
  have hsAne : Real.sqrt A ≠ 0 := ne_of_gt hsA
  set e : ℝ := K / x with hedef
  have he0 : 0 ≤ e := by rw [hedef]; positivity
  have he1 : e ≤ 1 / 100 := by
    rw [hedef, div_le_div_iff₀ hx0 (by norm_num)]
    linarith
  have heK : K / (x + 1) ≤ e := by
    rw [hedef]
    exact div_le_div_of_nonneg_left (by linarith) hx0 (by linarith)
  -- two-sided bounds
  have hsq0 : (0:ℝ) < x ^ 2 := by positivity
  have hAx : (0:ℝ) < A * x := mul_pos hA hx0
  have hAx3 : (0:ℝ) < A * x ^ 3 := by positivity
  have hSxx : (0:ℝ) < Real.sqrt A * x * Real.sqrt x := by positivity
  have hρlo : 3 * x ^ 2 ≤ prolateRho β γ (n + 1) := by
    nlinarith [hρ1.lower, mul_nonneg hsq0.le (by linarith : (0:ℝ) ≤ 1 - 4 * e)]
  have hρpos : 0 < prolateRho β γ (n + 1) := by nlinarith [hρlo, hsq0]
  have hQlo : 0 < prolatePotential β γ c lam z (n + 1) := by
    nlinarith [hQ1.lower, mul_pos (by linarith : (0:ℝ) < 1 - e) hAx]
  have hQhi : prolatePotential β γ c lam z (n + 1) ≤ 2 * (A * x) := by
    nlinarith [hQ1.upper, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - e) hAx.le]
  have hs1lo : Real.sqrt A * x * Real.sqrt x
      ≤ Real.sqrt (prolateWeight β γ c lam z (n + 1)) := by
    nlinarith [hs1.lower, mul_nonneg hSxx.le (by linarith : (0:ℝ) ≤ 1 - 6 * e)]
  have hs1hi : Real.sqrt (prolateWeight β γ c lam z (n + 1))
      ≤ 3 * (Real.sqrt A * x * Real.sqrt x) := by
    nlinarith [hs1.upper, mul_nonneg hSxx.le (by linarith : (0:ℝ) ≤ 1 - 6 * e)]
  have hs2lo : Real.sqrt A * x * Real.sqrt x
      ≤ Real.sqrt (prolateWeight β γ c lam z (n + 2)) := by
    nlinarith [hs2.lower, mul_nonneg hSxx.le (by linarith : (0:ℝ) ≤ 1 - 10 * e)]
  have hs2hi : Real.sqrt (prolateWeight β γ c lam z (n + 2))
      ≤ 3 * (Real.sqrt A * x * Real.sqrt x) := by
    nlinarith [hs2.upper, mul_nonneg hSxx.le (by linarith : (0:ℝ) ≤ 1 - 10 * e)]
  have hW1pos : 0 < prolateWeight β γ c lam z (n + 1) := by
    nlinarith [hW1.lower, mul_pos (by linarith : (0:ℝ) < 1 - 3 * e) hAx3]
  have hW2pos : 0 < prolateWeight β γ c lam z (n + 2) := by
    nlinarith [hW2.lower, mul_pos (by linarith : (0:ℝ) < 1 - 5 * e) hAx3]
  have hdWabs : |prolateWeight β γ c lam z (n + 2) - prolateWeight β γ c lam z (n + 1)|
      ≤ 13 * (A * x ^ 2) := by
    have hp : (0:ℝ) < A * x ^ 2 := by positivity
    rw [abs_le]
    constructor <;>
      nlinarith [hdW.lower, hdW.upper, mul_nonneg hp.le (by linarith : (0:ℝ) ≤ 1 - 60 * e),
        mul_nonneg hp.le (by linarith : (0:ℝ) ≤ 1 + 60 * e)]
  have hdrhoabs : |prolateRho β γ (n + 2) - prolateRho β γ (n + 1)| ≤ 9 * x := by
    rw [abs_le]
    constructor <;>
      nlinarith [hdrho.lower, hdrho.upper, mul_nonneg hx0.le (by linarith : (0:ℝ) ≤ 1 - 8 * e)]
  have hQ2abs : |prolatePotential β γ c lam z (n + 2)| ≤ 4 * (A * x) := by
    have hup := hQ2r.upper
    have hlo := hQ2r.lower
    have hAx1 : (0:ℝ) < A * (x + 1) := by positivity
    have hkey1 : (1 + K / (x + 1)) * (A * (x + 1)) ≤ 4 * (A * x) := by
      have h1 : K / (x + 1) ≤ e := heK
      nlinarith [mul_nonneg hA.le hx0.le, hA, hx0, he1,
        mul_nonneg (mul_nonneg hA.le hx0.le) (by linarith : (0:ℝ) ≤ 1 - 100 * e)]
    have hkey2 : -(4 * (A * x)) ≤ (1 - K / (x + 1)) * (A * (x + 1)) := by
      have h1 : K / (x + 1) ≤ e := heK
      have h2 : (0:ℝ) ≤ K / (x + 1) := by positivity
      nlinarith [hAx1, hA, hx0, he1]
    rw [abs_le]
    constructor <;> linarith
  -- the drift bound
  have hdriftabs : |slgAbelDrift (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)|
      ≤ 8 / (Real.sqrt A * Real.sqrt x) := by
    have hpos : (0:ℝ) < Real.sqrt A * Real.sqrt x := by positivity
    have h6 : (0:ℝ) < 6 / (Real.sqrt A * Real.sqrt x) := by positivity
    have hconv : (8:ℝ) / (Real.sqrt A * Real.sqrt x)
        = 4 / 3 * (6 / (Real.sqrt A * Real.sqrt x)) := by ring
    rw [hconv, abs_le]
    constructor
    · nlinarith [hdrift.upper, mul_nonneg h6.le (by linarith : (0:ℝ) ≤ 1 / 3 - 20 * e)]
    · nlinarith [hdrift.lower, mul_nonneg h6.le (by linarith : (0:ℝ) ≤ 1 - 20 * e),
        mul_nonneg h6.le (by linarith : (0:ℝ) ≤ (4:ℝ) / 3)]
  have habs : |slgDrift (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)|
      ≤ 3 / (Real.sqrt A * x ^ 2 * Real.sqrt x) := by
    have hpos : (0:ℝ) < Real.sqrt A * Real.sqrt x := by positivity
    have hform : slgDrift (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)
        = slgAbelDrift (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)
          / prolateRho β γ (n + 1) := by
      simp only [slgAbelDrift]
      rw [mul_div_assoc, div_self hρpos.ne', mul_one]
    have hkey : |slgAbelDrift (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)|
        * (Real.sqrt A * Real.sqrt x) ≤ 8 := by
      rw [← le_div_iff₀ hpos]
      exact hdriftabs
    rw [hform, abs_div, abs_of_pos hρpos, div_le_div_iff₀ hρpos (by positivity)]
    nlinarith [hkey, hρlo, hsA, hsx, hx0,
      abs_nonneg (slgAbelDrift (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1))]
  -- the ratio defect
  have hdefabs : |slgRatioDefect (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)|
      ≤ 13 / (8 * x) := by
    have hsw : (0:ℝ) < Real.sqrt (prolateWeight β γ c lam z (n + 1))
        + Real.sqrt (prolateWeight β γ c lam z (n + 2)) := by
      have := Real.sqrt_pos.mpr hW1pos
      have := Real.sqrt_pos.mpr hW2pos
      linarith
    have hq1 : Real.sqrt (prolateWeight β γ c lam z (n + 1)) ^ 2
        = prolateWeight β γ c lam z (n + 1) := Real.sq_sqrt hW1pos.le
    have hq2 : Real.sqrt (prolateWeight β γ c lam z (n + 2)) ^ 2
        = prolateWeight β γ c lam z (n + 2) := Real.sq_sqrt hW2pos.le
    have hfac : (Real.sqrt (prolateWeight β γ c lam z (n + 1))
        - Real.sqrt (prolateWeight β γ c lam z (n + 2)))
        * (Real.sqrt (prolateWeight β γ c lam z (n + 1))
          + Real.sqrt (prolateWeight β γ c lam z (n + 2)))
        = prolateWeight β γ c lam z (n + 1) - prolateWeight β γ c lam z (n + 2) := by
      linear_combination hq1 - hq2
    have hdiffabs : |Real.sqrt (prolateWeight β γ c lam z (n + 1))
        - Real.sqrt (prolateWeight β γ c lam z (n + 2))|
        * (Real.sqrt (prolateWeight β γ c lam z (n + 1))
          + Real.sqrt (prolateWeight β γ c lam z (n + 2)))
        = |prolateWeight β γ c lam z (n + 2) - prolateWeight β γ c lam z (n + 1)| := by
      rw [← abs_of_pos hsw, ← abs_mul, hfac]
      exact abs_sub_comm _ _
    have hsumlo : 2 * (Real.sqrt A * x * Real.sqrt x)
        ≤ Real.sqrt (prolateWeight β γ c lam z (n + 1))
          + Real.sqrt (prolateWeight β γ c lam z (n + 2)) := by linarith
    have hdefeq : slgRatioDefect (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)
        * (2 * (Real.sqrt (prolateWeight β γ c lam z (n + 1))
          + Real.sqrt (prolateWeight β γ c lam z (n + 2))))
        = Real.sqrt (prolateWeight β γ c lam z (n + 1))
          - Real.sqrt (prolateWeight β γ c lam z (n + 2)) := by
      simp only [slgRatioDefect, prolateWeight]
      exact div_mul_cancel₀ _ (by positivity)
    have habsdef : |slgRatioDefect (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)|
        * (2 * (Real.sqrt (prolateWeight β γ c lam z (n + 1))
          + Real.sqrt (prolateWeight β γ c lam z (n + 2))))
        = |Real.sqrt (prolateWeight β γ c lam z (n + 1))
          - Real.sqrt (prolateWeight β γ c lam z (n + 2))| := by
      rw [← abs_of_pos (by positivity : (0:ℝ) < 2 * (Real.sqrt (prolateWeight β γ c lam z (n + 1))
        + Real.sqrt (prolateWeight β γ c lam z (n + 2)))), ← abs_mul, hdefeq]
    have hmain : |slgRatioDefect (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)|
        * (2 * (Real.sqrt (prolateWeight β γ c lam z (n + 1))
          + Real.sqrt (prolateWeight β γ c lam z (n + 2))) ^ 2)
        ≤ 13 * (A * x ^ 2) := by
      have hstep : |slgRatioDefect (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)|
          * (2 * (Real.sqrt (prolateWeight β γ c lam z (n + 1))
            + Real.sqrt (prolateWeight β γ c lam z (n + 2))) ^ 2)
          = |prolateWeight β γ c lam z (n + 2) - prolateWeight β γ c lam z (n + 1)| := by
        rw [← hdiffabs, ← habsdef]
        ring
      rw [hstep]
      exact hdWabs
    have hbig2 : 8 * (A * x ^ 3)
        ≤ 2 * (Real.sqrt (prolateWeight β γ c lam z (n + 1))
          + Real.sqrt (prolateWeight β γ c lam z (n + 2))) ^ 2 := by
      have hsq : (2 * (Real.sqrt A * x * Real.sqrt x)) ^ 2 = 4 * (A * x ^ 3) := by
        calc (2 * (Real.sqrt A * x * Real.sqrt x)) ^ 2
            = 4 * (Real.sqrt A ^ 2) * x ^ 2 * (Real.sqrt x ^ 2) := by ring
          _ = 4 * (A * x ^ 3) := by rw [hsA2, hsx2]; ring
      nlinarith [hsumlo, hsq, hsw, hsA, hsx, hx0]
    have hnn : (0:ℝ)
        ≤ |slgRatioDefect (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)| :=
      abs_nonneg _
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hmain, hbig2, hnn, hA, hx0]
  -- assemble
  have hT1 : |slgDrift (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)|
      * prolatePotential β γ c lam z (n + 1)
      ≤ 6 * Real.sqrt A / (x * Real.sqrt x) := by
    have hstep : |slgDrift (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)|
        * prolatePotential β γ c lam z (n + 1)
        ≤ (3 / (Real.sqrt A * x ^ 2 * Real.sqrt x)) * (2 * (A * x)) :=
      mul_le_mul habs hQhi hQlo.le (by positivity)
    refine le_trans hstep (le_of_eq ?_)
    rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (-(6 * x ^ 2 * Real.sqrt x)) * hsA2
  have hT2 : |slgDrift (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)|
      * |slgRatioDefect (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)|
      * Real.sqrt (prolateWeight β γ c lam z (n + 1))
      ≤ 15 / (x * Real.sqrt x) := by
    have hstep : |slgDrift (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)|
        * |slgRatioDefect (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)|
        * Real.sqrt (prolateWeight β γ c lam z (n + 1))
        ≤ (3 / (Real.sqrt A * x ^ 2 * Real.sqrt x)) * (13 / (8 * x))
          * (3 * (Real.sqrt A * x * Real.sqrt x)) := by
      refine mul_le_mul (mul_le_mul habs hdefabs (abs_nonneg _) (by positivity))
        hs1hi (Real.sqrt_nonneg _) (by positivity)
    refine le_trans hstep ?_
    have heq : (3 / (Real.sqrt A * x ^ 2 * Real.sqrt x)) * (13 / (8 * x))
        * (3 * (Real.sqrt A * x * Real.sqrt x)) = 117 / (8 * x ^ 2) := by
      field_simp
      ring
    rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hsxx, hx2, hsx, hx0]
  have hT3 : 4 * (|prolatePotential β γ c lam z (n + 2)|
        * |prolateRho β γ (n + 2) - prolateRho β γ (n + 1)|)
      / (prolateRho β γ (n + 1) * Real.sqrt (prolateWeight β γ c lam z (n + 2)))
      ≤ 48 * Real.sqrt A / (x * Real.sqrt x) := by
    have hnum : 4 * (|prolatePotential β γ c lam z (n + 2)|
        * |prolateRho β γ (n + 2) - prolateRho β γ (n + 1)|) ≤ 4 * (4 * (A * x) * (9 * x)) := by
      have := mul_le_mul hQ2abs hdrhoabs (abs_nonneg _) (by positivity)
      linarith
    have hden : 3 * x ^ 2 * (Real.sqrt A * x * Real.sqrt x)
        ≤ prolateRho β γ (n + 1) * Real.sqrt (prolateWeight β γ c lam z (n + 2)) :=
      mul_le_mul hρlo hs2lo (by positivity) (by positivity)
    have hdenpos : (0:ℝ) < 3 * x ^ 2 * (Real.sqrt A * x * Real.sqrt x) := by positivity
    have hnumnn : (0:ℝ) ≤ 4 * (|prolatePotential β γ c lam z (n + 2)|
        * |prolateRho β γ (n + 2) - prolateRho β γ (n + 1)|) := by positivity
    calc 4 * (|prolatePotential β γ c lam z (n + 2)|
          * |prolateRho β γ (n + 2) - prolateRho β γ (n + 1)|)
        / (prolateRho β γ (n + 1) * Real.sqrt (prolateWeight β γ c lam z (n + 2)))
        ≤ 4 * (4 * (A * x) * (9 * x)) / (3 * x ^ 2 * (Real.sqrt A * x * Real.sqrt x)) := by
          apply div_le_div₀ (by positivity) hnum hdenpos hden
      _ = 48 * Real.sqrt A / (x * Real.sqrt x) := by
          rw [div_eq_div_iff (by positivity) (by positivity)]
          linear_combination (-(144 * x ^ 3 * Real.sqrt x)) * hsA2
  rw [slgControl]
  calc |slgDrift (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)|
        * prolatePotential β γ c lam z (n + 1)
      + |slgDrift (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)|
        * |slgRatioDefect (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)|
        * Real.sqrt (slgWeight (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1))
      + 4 * (|prolatePotential β γ c lam z (n + 1 + 1)|
        * |prolateRho β γ (n + 1 + 1) - prolateRho β γ (n + 1)|)
        / (prolateRho β γ (n + 1)
          * Real.sqrt (slgWeight (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1 + 1)))
      ≤ 6 * Real.sqrt A / (x * Real.sqrt x) + 15 / (x * Real.sqrt x)
        + 48 * Real.sqrt A / (x * Real.sqrt x) := by
        have h2 := hT2
        have h3 := hT3
        simp only [prolateWeight] at h2 h3
        linarith [hT1, h2, h3]
    _ = (15 + 54 * Real.sqrt A) / (x * Real.sqrt x) := by ring

/-! ## The explicit Abel drift and its deviation -/

/-- The explicit monotone Abel drift of a prolate block. -/
noncomputable def prolateDrift (lam : ℝ) (n : ℕ) : ℝ :=
  -(6 / (Real.sqrt (16 * Real.pi * lam ^ 2) * Real.sqrt (n : ℝ)))

/-- The deviation of the true Liouville--Green drift from `prolateDrift`. -/
noncomputable def prolateDev (β γ c lam z : ℝ) (n : ℕ) : ℝ :=
  120 * prolateErr β γ c lam z
    / (Real.sqrt (16 * Real.pi * lam ^ 2) * (n : ℝ) * Real.sqrt (n : ℝ))

theorem prolateDev_nonneg (hβ : 0 ≤ β) (hγ : 2 ≤ γ) (hA : 0 < 16 * Real.pi * lam ^ 2)
    (n : ℕ) : 0 ≤ prolateDev β γ c lam z n := by
  unfold prolateDev
  have hK := prolateErr_pos (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA
  positivity

theorem prolate_dev_bound (hβ : 0 ≤ β) (hγ : 2 ≤ γ)
    (hA : 0 < 16 * Real.pi * lam ^ 2) {n : ℕ} (hn : 1 ≤ n)
    (hbig : 100 * prolateErr β γ c lam z ≤ (n : ℝ) + 1) :
    |slgAbelDrift (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)
      - prolateDrift lam (n + 1)| ≤ prolateDev β γ c lam z (n + 1) := by
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hx0 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have hsA : 0 < Real.sqrt (16 * Real.pi * lam ^ 2) := Real.sqrt_pos.mpr hA
  have hsx : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr hx0
  have h := relApprox_slgAbelDrift hβ hγ hA hn hbig
  have hval : |slgAbelDrift (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1)
      - prolateDrift lam (n + 1)|
      = |-(slgAbelDrift (prolateRho β γ) (prolatePotential β γ c lam z) (n + 1))
        - 6 / (Real.sqrt (16 * Real.pi * lam ^ 2) * Real.sqrt ((n : ℝ) + 1))| := by
    rw [prolateDrift, hcast, ← abs_neg]
    congr 1
    ring
  have hdevval : prolateDev β γ c lam z (n + 1)
      = 20 * (prolateErr β γ c lam z / ((n : ℝ) + 1))
        * (6 / (Real.sqrt (16 * Real.pi * lam ^ 2) * Real.sqrt ((n : ℝ) + 1))) := by
    rw [prolateDev, hcast]
    field_simp
    ring
  rw [hval, hdevval]
  exact h

theorem prolateDrift_bdry (hA : 0 < 16 * Real.pi * lam ^ 2) {n : ℕ}
    (hn : (96 : ℝ) / Real.sqrt (16 * Real.pi * lam ^ 2) ≤ Real.sqrt (n : ℝ)) :
    2 * |prolateDrift lam n| ≤ 1 / 8 := by
  have hsA : 0 < Real.sqrt (16 * Real.pi * lam ^ 2) := Real.sqrt_pos.mpr hA
  have hsx : (0:ℝ) < Real.sqrt (n : ℝ) := by
    have h1 : (0:ℝ) < 96 / Real.sqrt (16 * Real.pi * lam ^ 2) := by positivity
    linarith
  rw [div_le_iff₀ hsA] at hn
  rw [prolateDrift, abs_neg, abs_of_pos (by positivity),
    show (2:ℝ) * (6 / (Real.sqrt (16 * Real.pi * lam ^ 2) * Real.sqrt (n : ℝ)))
      = 12 / (Real.sqrt (16 * Real.pi * lam ^ 2) * Real.sqrt (n : ℝ)) from by ring,
    div_le_iff₀ (by positivity)]
  nlinarith [hn, hsA, hsx]

theorem prolateDrift_diff (hA : 0 < 16 * Real.pi * lam ^ 2) {k : ℕ} (hk : 1 ≤ k) :
    |prolateDrift lam (k + 1) - prolateDrift lam k|
      = 6 / Real.sqrt (16 * Real.pi * lam ^ 2)
        * (1 / Real.sqrt (k : ℝ) - 1 / Real.sqrt ((k : ℝ) + 1)) := by
  have hsA : 0 < Real.sqrt (16 * Real.pi * lam ^ 2) := Real.sqrt_pos.mpr hA
  have hk1 : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsk : (0:ℝ) < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsk1 : (0:ℝ) < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
  have hmono : Real.sqrt (k : ℝ) < Real.sqrt ((k : ℝ) + 1) :=
    Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  have hval : prolateDrift lam (k + 1) - prolateDrift lam k
      = 6 / Real.sqrt (16 * Real.pi * lam ^ 2)
        * (1 / Real.sqrt (k : ℝ) - 1 / Real.sqrt ((k : ℝ) + 1)) := by
    rw [prolateDrift, prolateDrift, hcast]
    field_simp
    ring
  rw [hval, abs_of_nonneg]
  have hinv : 1 / Real.sqrt ((k : ℝ) + 1) ≤ 1 / Real.sqrt (k : ℝ) :=
    one_div_le_one_div_of_le hsk hmono.le
  have : (0:ℝ) ≤ 6 / Real.sqrt (16 * Real.pi * lam ^ 2) := by positivity
  nlinarith [hinv]

/-! ## The summed control -/

theorem inv_succ_le_sqrt_div_sq {k : ℕ} (hk : 1 ≤ k) :
    1 / (((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1)) ≤ Real.sqrt (k : ℝ) / (k : ℝ) ^ 2 := by
  have hk1 : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsk : (0:ℝ) < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsk1 : (0:ℝ) < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
  have hsk2 : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt (by linarith)
  have hmono : Real.sqrt (k : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have heq : Real.sqrt (k : ℝ) / (k : ℝ) ^ 2 = 1 / ((k : ℝ) * Real.sqrt (k : ℝ)) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    nlinarith [hsk2]
  rw [heq]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [hsk, hsk1, hmono, hk1]

/-- The constant controlling the whole Liouville--Green sum of a prolate block. -/
noncomputable def prolateTotalConst (β γ c lam z : ℝ) : ℝ :=
  12 / Real.sqrt (16 * Real.pi * lam ^ 2)
    + 4 * (2 * (15 + 54 * Real.sqrt (16 * Real.pi * lam ^ 2))
      + 480 * prolateErr β γ c lam z / Real.sqrt (16 * Real.pi * lam ^ 2))

set_option maxHeartbeats 1000000 in
theorem prolate_sum_le (hβ : 0 ≤ β) (hγ : 2 ≤ γ) (hA : 0 < 16 * Real.pi * lam ^ 2)
    {N₀ : ℕ} (hN₀ : 1 ≤ N₀)
    (hbigall : ∀ n : ℕ, N₀ ≤ n → 100 * prolateErr β γ c lam z ≤ (n : ℝ) + 1) (K : ℕ) :
    ∑ k ∈ Finset.Ico N₀ K, (2 * |prolateDrift lam (k + 1) - prolateDrift lam k|
      + 2 * (slgControl (prolateRho β γ) (prolatePotential β γ c lam z) (k + 1)
        + 2 * prolateDev β γ c lam z (k + 1)))
      ≤ prolateTotalConst β γ c lam z / Real.sqrt (N₀ : ℝ) := by
  have hsA : 0 < Real.sqrt (16 * Real.pi * lam ^ 2) := Real.sqrt_pos.mpr hA
  have hK' := prolateErr_pos (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA
  have hN₀r : (1:ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀
  have hsN : (0:ℝ) < Real.sqrt (N₀ : ℝ) := Real.sqrt_pos.mpr (by linarith)
  set Cbig : ℝ := 2 * (15 + 54 * Real.sqrt (16 * Real.pi * lam ^ 2))
    + 480 * prolateErr β γ c lam z / Real.sqrt (16 * Real.pi * lam ^ 2) with hCbig
  have hCbig0 : 0 ≤ Cbig := by rw [hCbig]; positivity
  rcases Nat.lt_or_ge K N₀ with hKN | hNK
  · rw [Finset.Ico_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    rw [prolateTotalConst]
    positivity

  · have hsplit : ∀ k ∈ Finset.Ico N₀ K,
        2 * |prolateDrift lam (k + 1) - prolateDrift lam k|
          + 2 * (slgControl (prolateRho β γ) (prolatePotential β γ c lam z) (k + 1)
            + 2 * prolateDev β γ c lam z (k + 1))
        ≤ 12 / Real.sqrt (16 * Real.pi * lam ^ 2)
            * (1 / Real.sqrt (k : ℝ) - 1 / Real.sqrt ((k : ℝ) + 1))
          + Cbig * (Real.sqrt (k : ℝ) / (k : ℝ) ^ 2) := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hk1 : 1 ≤ k := le_trans hN₀ hk.1
      have hbig := hbigall k hk.1
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      have hd := prolateDrift_diff (lam := lam) hA hk1
      have hc := slgControl_le hβ hγ hA hk1 hbig
      have hdev : prolateDev β γ c lam z (k + 1)
          = 120 * prolateErr β γ c lam z
            / (Real.sqrt (16 * Real.pi * lam ^ 2) * ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1)) := by
        rw [prolateDev, hcast]
      have hbase := inv_succ_le_sqrt_div_sq hk1
      have hcle : slgControl (prolateRho β γ) (prolatePotential β γ c lam z) (k + 1)
          ≤ (15 + 54 * Real.sqrt (16 * Real.pi * lam ^ 2))
            * (Real.sqrt (k : ℝ) / (k : ℝ) ^ 2) := by
        refine le_trans hc ?_
        have hrw : (15 + 54 * Real.sqrt (16 * Real.pi * lam ^ 2))
            / (((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1))
            = (15 + 54 * Real.sqrt (16 * Real.pi * lam ^ 2))
              * (1 / (((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1))) := by ring
        rw [hrw]
        exact mul_le_mul_of_nonneg_left hbase (by positivity)
      have hdle : prolateDev β γ c lam z (k + 1)
          ≤ 120 * prolateErr β γ c lam z / Real.sqrt (16 * Real.pi * lam ^ 2)
            * (Real.sqrt (k : ℝ) / (k : ℝ) ^ 2) := by
        rw [hdev]
        have hrw : 120 * prolateErr β γ c lam z
            / (Real.sqrt (16 * Real.pi * lam ^ 2) * ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1))
            = 120 * prolateErr β γ c lam z / Real.sqrt (16 * Real.pi * lam ^ 2)
              * (1 / (((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1))) := by
          field_simp
        rw [hrw]
        exact mul_le_mul_of_nonneg_left hbase (by positivity)
      rw [hd, hCbig]
      have h12 : 2 * (6 / Real.sqrt (16 * Real.pi * lam ^ 2)
          * (1 / Real.sqrt (k : ℝ) - 1 / Real.sqrt ((k : ℝ) + 1)))
          = 12 / Real.sqrt (16 * Real.pi * lam ^ 2)
            * (1 / Real.sqrt (k : ℝ) - 1 / Real.sqrt ((k : ℝ) + 1)) := by ring
      rw [h12]
      have hfin : 2 * (slgControl (prolateRho β γ) (prolatePotential β γ c lam z) (k + 1)
          + 2 * prolateDev β γ c lam z (k + 1))
          ≤ (2 * (15 + 54 * Real.sqrt (16 * Real.pi * lam ^ 2))
            + 480 * prolateErr β γ c lam z / Real.sqrt (16 * Real.pi * lam ^ 2))
            * (Real.sqrt (k : ℝ) / (k : ℝ) ^ 2) := by
        have e3 : 2 * ((15 + 54 * Real.sqrt (16 * Real.pi * lam ^ 2))
              * (Real.sqrt (k : ℝ) / (k : ℝ) ^ 2))
            + 4 * (120 * prolateErr β γ c lam z / Real.sqrt (16 * Real.pi * lam ^ 2)
              * (Real.sqrt (k : ℝ) / (k : ℝ) ^ 2))
            = (2 * (15 + 54 * Real.sqrt (16 * Real.pi * lam ^ 2))
              + 480 * prolateErr β γ c lam z / Real.sqrt (16 * Real.pi * lam ^ 2))
              * (Real.sqrt (k : ℝ) / (k : ℝ) ^ 2) := by ring
        have e1 : 2 * slgControl (prolateRho β γ) (prolatePotential β γ c lam z) (k + 1)
            ≤ 2 * ((15 + 54 * Real.sqrt (16 * Real.pi * lam ^ 2))
              * (Real.sqrt (k : ℝ) / (k : ℝ) ^ 2)) := by linarith [hcle]
        have e2 : 4 * prolateDev β γ c lam z (k + 1)
            ≤ 4 * (120 * prolateErr β γ c lam z / Real.sqrt (16 * Real.pi * lam ^ 2)
              * (Real.sqrt (k : ℝ) / (k : ℝ) ^ 2)) := by linarith [hdle]
        linarith [e1, e2, e3]
      linarith
    calc ∑ k ∈ Finset.Ico N₀ K, (2 * |prolateDrift lam (k + 1) - prolateDrift lam k|
          + 2 * (slgControl (prolateRho β γ) (prolatePotential β γ c lam z) (k + 1)
            + 2 * prolateDev β γ c lam z (k + 1)))
        ≤ ∑ k ∈ Finset.Ico N₀ K, (12 / Real.sqrt (16 * Real.pi * lam ^ 2)
            * (1 / Real.sqrt (k : ℝ) - 1 / Real.sqrt ((k : ℝ) + 1))
            + Cbig * (Real.sqrt (k : ℝ) / (k : ℝ) ^ 2)) := Finset.sum_le_sum hsplit
      _ = 12 / Real.sqrt (16 * Real.pi * lam ^ 2)
            * (∑ k ∈ Finset.Ico N₀ K, (1 / Real.sqrt (k : ℝ) - 1 / Real.sqrt ((k : ℝ) + 1)))
          + Cbig * (∑ k ∈ Finset.Ico N₀ K, Real.sqrt (k : ℝ) / (k : ℝ) ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 12 / Real.sqrt (16 * Real.pi * lam ^ 2) * (1 / Real.sqrt (N₀ : ℝ))
          + Cbig * (4 / Real.sqrt (N₀ : ℝ)) := by
          have h1 := sum_Ico_sqrtinv_telescope hNK
          have h2 := sum_Ico_sqrt_div_sq_le hN₀ hNK
          have h3 : (0:ℝ) ≤ 1 / Real.sqrt (K : ℝ) := by positivity
          have h4 : (0:ℝ) ≤ 12 / Real.sqrt (16 * Real.pi * lam ^ 2) := by positivity
          nlinarith [h1, h2, h3, h4, hCbig0]
      _ = prolateTotalConst β γ c lam z / Real.sqrt (N₀ : ℝ) := by
          rw [prolateTotalConst, hCbig]
          ring

/-! ## Positivity of the prolate potential and the weight lower bound -/

theorem prolate_e_le (_hβ : 0 ≤ β) (_hγ : 2 ≤ γ) (_hA : 0 < 16 * Real.pi * lam ^ 2) {n : ℕ}
    (hbig : 100 * prolateErr β γ c lam z ≤ (n : ℝ) + 1) :
    prolateErr β γ c lam z / ((n : ℝ) + 1) ≤ 1 / 100 := by
  have hx0 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_le_div_iff₀ hx0 (by norm_num)]
  linarith

theorem prolatePotential_pos (hβ : 0 ≤ β) (hγ : 2 ≤ γ) (hA : 0 < 16 * Real.pi * lam ^ 2)
    {n : ℕ} (hbig : 100 * prolateErr β γ c lam z ≤ (n : ℝ) + 1) :
    0 < prolatePotential β γ c lam z (n + 1) := by
  have hx0 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have he1 := prolate_e_le hβ hγ hA hbig
  have hKpos := prolateErr_pos (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA
  have he0 : 0 ≤ prolateErr β γ c lam z / ((n : ℝ) + 1) := div_nonneg hKpos.le hx0.le
  have hlo := (relApprox_Q_err (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA n).lower
  nlinarith [hlo, mul_pos (by linarith : (0:ℝ) < 1 - prolateErr β γ c lam z / ((n : ℝ) + 1))
    (mul_pos hA hx0)]

theorem prolatePotential_le_rho (hβ : 0 ≤ β) (hγ : 2 ≤ γ) (hA : 0 < 16 * Real.pi * lam ^ 2)
    {n : ℕ} (hbig : 100 * prolateErr β γ c lam z ≤ (n : ℝ) + 1)
    (hAx : 16 * Real.pi * lam ^ 2 ≤ (n : ℝ) + 1) :
    prolatePotential β γ c lam z (n + 1) ≤ prolateRho β γ (n + 1) := by
  have hx0 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have he1 := prolate_e_le hβ hγ hA hbig
  have hKpos := prolateErr_pos (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA
  have he0 : 0 ≤ prolateErr β γ c lam z / ((n : ℝ) + 1) := div_nonneg hKpos.le hx0.le
  have hup := (relApprox_Q_err (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA n).upper
  have hlo := (relApprox_rho_err (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA n).lower
  have hQhi : prolatePotential β γ c lam z (n + 1) ≤ 2 * (16 * Real.pi * lam ^ 2 * ((n : ℝ) + 1)) := by
    nlinarith [hup, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - prolateErr β γ c lam z / ((n : ℝ) + 1))
      (mul_pos hA hx0).le]
  have hρlo : 3 * ((n : ℝ) + 1) ^ 2 ≤ prolateRho β γ (n + 1) := by
    nlinarith [hlo, mul_nonneg (by positivity : (0:ℝ) ≤ ((n : ℝ) + 1) ^ 2)
      (by linarith : (0:ℝ) ≤ 1 - 4 * (prolateErr β γ c lam z / ((n : ℝ) + 1)))]
  nlinarith [hQhi, hρlo, hAx, hx0]

theorem sqrt_weight_lower (hβ : 0 ≤ β) (hγ : 2 ≤ γ) (hA : 0 < 16 * Real.pi * lam ^ 2)
    {n : ℕ} (hbig : 100 * prolateErr β γ c lam z ≤ (n : ℝ) + 1) :
    Real.sqrt (16 * Real.pi * lam ^ 2) * ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)
      ≤ Real.sqrt (prolateWeight β γ c lam z (n + 1)) := by
  have hx0 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have he1 := prolate_e_le hβ hγ hA hbig
  have hKpos := prolateErr_pos (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA
  have he0 : 0 ≤ prolateErr β γ c lam z / ((n : ℝ) + 1) := div_nonneg hKpos.le hx0.le
  have hSxx : (0:ℝ) ≤ Real.sqrt (16 * Real.pi * lam ^ 2) * ((n : ℝ) + 1)
      * Real.sqrt ((n : ℝ) + 1) := by positivity
  have hlo := (relApprox_sqrt_weight_succ hβ hγ hA hbig).lower
  nlinarith [hlo, mul_nonneg hSxx
    (by linarith : (0:ℝ) ≤ 1 - 6 * (prolateErr β γ c lam z / ((n : ℝ) + 1)))]

/-! ## Every solution at positive prolate parameter is square-summable -/

set_option maxHeartbeats 1000000 in
/-- **The limit-circle half.**  For a positive prolate parameter every real solution of the block
is square-summable. -/
theorem prolate_summable_of_pos (hβ : 0 ≤ β) (hγ : 2 ≤ γ)
    (hA : 0 < 16 * Real.pi * lam ^ 2) {q : ℕ → ℝ}
    (hq : ∀ n : ℕ, (prolateBase β γ (n + 1) + prolateBase β γ n) / 4 + q (n + 1)
        = 3 / 4 + 2 * Real.pi * lam ^ 2 * (8 * ((n : ℝ) + 1) + c))
    {u : ℕ → ℝ} (hu : IsJacobiRecR (prolateRho β γ) q z u) :
    Summable fun n => u n ^ 2 := by
  have hsA : 0 < Real.sqrt (16 * Real.pi * lam ^ 2) := Real.sqrt_pos.mpr hA
  have hKpos := prolateErr_pos (β := β) (γ := γ) (c := c) (lam := lam) (z := z) hβ hγ hA
  have hslg : IsSLGSolution (prolateRho β γ) (prolatePotential β γ c lam z) u :=
    isSLGSolution_of_jacobi (fun n => prolatePotential_eq hq n) hu
  obtain ⟨M, hM⟩ := exists_nat_gt
    (max (max (100 * prolateErr β γ c lam z) ((96 / Real.sqrt (16 * Real.pi * lam ^ 2)) ^ 2))
      (max ((8 * prolateTotalConst β γ c lam z) ^ 2) (max (16 * Real.pi * lam ^ 2) 1)))
  have hM1 : (1:ℝ) < (M : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_max_right _ _))) hM
  have hMnat : 1 ≤ M := by exact_mod_cast hM1.le
  have hMK : 100 * prolateErr β γ c lam z < (M : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hMsq : (96 / Real.sqrt (16 * Real.pi * lam ^ 2)) ^ 2 < (M : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hMtot : (8 * prolateTotalConst β γ c lam z) ^ 2 < (M : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have hMA : 16 * Real.pi * lam ^ 2 < (M : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_max_right _ _))) hM
  -- the window
  have hbigsucc : ∀ m : ℕ, M ≤ m → 100 * prolateErr β γ c lam z ≤ (m : ℝ) + 1 := by
    intro m hm
    have : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hbigall : ∀ n : ℕ, M + 1 ≤ n → 100 * prolateErr β γ c lam z ≤ (n : ℝ) + 1 := by
    intro n hn
    have : (M : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hρpos : ∀ n : ℕ, M + 1 ≤ n → 0 < prolateRho β γ n := fun n _ => prolateRho_pos hβ hγ
  have hQpos : ∀ n : ℕ, M + 1 ≤ n → 0 < prolatePotential β γ c lam z n :=
    forall_ge_succ (fun m hm => prolatePotential_pos hβ hγ hA (hbigsucc m hm))
  have hQρ : ∀ n : ℕ, M + 1 ≤ n → prolatePotential β γ c lam z n ≤ prolateRho β γ n :=
    forall_ge_succ (fun m hm => prolatePotential_le_rho hβ hγ hA (hbigsucc m hm)
      (by have : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          linarith))
  have hdev : ∀ n : ℕ, M + 1 ≤ n →
      |slgAbelDrift (prolateRho β γ) (prolatePotential β γ c lam z) n
        - prolateDrift lam n| ≤ prolateDev β γ c lam z n :=
    forall_ge_succ (fun m hm => prolate_dev_bound hβ hγ hA (le_trans hMnat hm) (hbigsucc m hm))
  have hdev0 : ∀ n : ℕ, M + 1 ≤ n → 0 ≤ prolateDev β γ c lam z n :=
    fun n _ => prolateDev_nonneg hβ hγ hA n
  have hbdry : ∀ n : ℕ, M + 1 ≤ n → 2 * |prolateDrift lam n| ≤ 1 / 8 := by
    intro n hn
    refine prolateDrift_bdry hA ?_
    have hnr : (M : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : (96 / Real.sqrt (16 * Real.pi * lam ^ 2)) ^ 2 ≤ (n : ℝ) := by linarith
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity)] at h2
  have hsN : (0:ℝ) < Real.sqrt ((M + 1 : ℕ) : ℝ) := by
    refine Real.sqrt_pos.mpr ?_
    have : (0:ℝ) < (M : ℝ) + 1 := by linarith
    push_cast
    linarith
  have hsumbound : prolateTotalConst β γ c lam z / Real.sqrt ((M + 1 : ℕ) : ℝ) ≤ 1 / 8 := by
    have hCpos : (0:ℝ) < prolateTotalConst β γ c lam z := by
      rw [prolateTotalConst]; positivity
    have hnr : (8 * prolateTotalConst β γ c lam z) ^ 2 ≤ ((M + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have h2 := Real.sqrt_le_sqrt hnr
    rw [Real.sqrt_sq (by positivity)] at h2
    rw [div_le_iff₀ hsN]
    linarith
  have hsum : ∀ K : ℕ, ∑ k ∈ Finset.Ico (M + 1) K,
      (2 * |prolateDrift lam (k + 1) - prolateDrift lam k|
        + 2 * (slgControl (prolateRho β γ) (prolatePotential β γ c lam z) (k + 1)
          + 2 * prolateDev β γ c lam z (k + 1))) ≤ 1 / 8 := fun K =>
    le_trans (prolate_sum_le hβ hγ hA (by omega) hbigall K) hsumbound
  -- the amplitude bound
  have hamp := fun (m : ℕ) (hm : M + 1 ≤ m) =>
    sq_le_of_slgControl hslg hρpos hQpos hQρ hdev hdev0 hbdry hsum hm
  set C : ℝ := max (slgNormalizedEnergy (prolateRho β γ) (prolatePotential β γ c lam z) u (M + 1))
    (slgNormalizedEnergy (prolateRho β γ) (prolatePotential β γ c lam z) u (M + 1 + 1)) with hCdef
  have hC0 : 0 ≤ C := by
    refine le_trans ?_ (le_max_left _ _)
    exact slgNormalizedEnergy_nonneg (hρpos (M + 1) le_rfl) (hQpos (M + 1) le_rfl).le
      (by linarith [hQρ (M + 1) le_rfl, hρpos (M + 1) le_rfl])
  have hbound : ∀ m : ℕ, M + 1 ≤ m →
      u m ^ 2 ≤ 4 * C / Real.sqrt (16 * Real.pi * lam ^ 2) * (Real.sqrt (m : ℝ) / (m : ℝ) ^ 2) := by
    refine forall_ge_succ (fun j hj => ?_)
    have hj1 : (1:ℝ) ≤ (j : ℝ) := by exact_mod_cast le_trans hMnat hj
    have hx0 : (0:ℝ) < (j : ℝ) + 1 := by positivity
    have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    have hlow := sqrt_weight_lower hβ hγ hA (hbigsucc j hj)
    have h := hamp (j + 1) (by omega)
    have hWpos : (0:ℝ) < Real.sqrt (16 * Real.pi * lam ^ 2) * ((j : ℝ) + 1)
        * Real.sqrt ((j : ℝ) + 1) := by positivity
    have hden : 0 < Real.sqrt (slgWeight (prolateRho β γ) (prolatePotential β γ c lam z) (j + 1)) :=
      lt_of_lt_of_le hWpos hlow
    have hstep : 4 * C / Real.sqrt (slgWeight (prolateRho β γ)
        (prolatePotential β γ c lam z) (j + 1))
        ≤ 4 * C / (Real.sqrt (16 * Real.pi * lam ^ 2) * ((j : ℝ) + 1)
          * Real.sqrt ((j : ℝ) + 1)) :=
      div_le_div_of_nonneg_left (by linarith) hWpos hlow
    have hfin : 4 * C / (Real.sqrt (16 * Real.pi * lam ^ 2) * ((j : ℝ) + 1)
        * Real.sqrt ((j : ℝ) + 1))
        = 4 * C / Real.sqrt (16 * Real.pi * lam ^ 2)
          * (Real.sqrt (((j + 1 : ℕ)) : ℝ) / (((j + 1 : ℕ)) : ℝ) ^ 2) := by
      rw [hcast]
      have hsj : Real.sqrt ((j : ℝ) + 1) ^ 2 = (j : ℝ) + 1 := Real.sq_sqrt (by linarith)
      have hne1 : Real.sqrt (16 * Real.pi * lam ^ 2) * ((j : ℝ) + 1)
          * Real.sqrt ((j : ℝ) + 1) ≠ 0 := by positivity
      have hne2 : Real.sqrt (16 * Real.pi * lam ^ 2) * ((j : ℝ) + 1) ^ 2 ≠ 0 := by positivity
      rw [div_mul_div_comm, div_eq_div_iff hne1 hne2]
      linear_combination (-(4 * C * Real.sqrt (16 * Real.pi * lam ^ 2) * ((j : ℝ) + 1))) * hsj
    linarith [h, hstep, hfin.le, hfin.ge]
  -- summability
  have hsummable : Summable fun i : ℕ => u (i + (M + 1)) ^ 2 := by
    refine summable_of_sum_range_le
      (c := 4 * C / Real.sqrt (16 * Real.pi * lam ^ 2) * (4 / Real.sqrt ((M + 1 : ℕ) : ℝ)))
      (fun i => sq_nonneg _) (fun r => ?_)
    have hre : ∑ i ∈ Finset.range r, u (i + (M + 1)) ^ 2
        ≤ ∑ i ∈ Finset.range r, 4 * C / Real.sqrt (16 * Real.pi * lam ^ 2)
          * (Real.sqrt ((i + (M + 1) : ℕ) : ℝ) / ((i + (M + 1) : ℕ) : ℝ) ^ 2) := by
      refine Finset.sum_le_sum (fun i _ => hbound _ (by omega))
    have hre2 : ∑ i ∈ Finset.range r, 4 * C / Real.sqrt (16 * Real.pi * lam ^ 2)
          * (Real.sqrt ((i + (M + 1) : ℕ) : ℝ) / ((i + (M + 1) : ℕ) : ℝ) ^ 2)
        = 4 * C / Real.sqrt (16 * Real.pi * lam ^ 2)
          * ∑ k ∈ Finset.Ico (M + 1) (M + 1 + r), Real.sqrt (k : ℝ) / (k : ℝ) ^ 2 := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left, ← Finset.mul_sum]
      refine congrArg _ (Finset.sum_congr rfl (fun i _ => ?_))
      congr 2 <;> [skip; skip] <;> · congr 1; omega
    have hre3 := sum_Ico_sqrt_div_sq_le (N := M + 1) (P := M + 1 + r) (by omega) (by omega)
    have hpos : (0:ℝ) ≤ 4 * C / Real.sqrt (16 * Real.pi * lam ^ 2) := by positivity
    calc ∑ i ∈ Finset.range r, u (i + (M + 1)) ^ 2
        ≤ 4 * C / Real.sqrt (16 * Real.pi * lam ^ 2)
          * ∑ k ∈ Finset.Ico (M + 1) (M + 1 + r), Real.sqrt (k : ℝ) / (k : ℝ) ^ 2 := by
          rw [← hre2]; exact hre
      _ ≤ 4 * C / Real.sqrt (16 * Real.pi * lam ^ 2) * (4 / Real.sqrt ((M + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hre3 hpos
  exact (summable_nat_add_iff (M + 1)).mp hsummable

/-! ## The deficiency space at positive prolate parameter -/

set_option maxHeartbeats 1000000 in
/-- **The limit-circle theorem.**  For a positive prolate parameter the deficiency space of the
block is nontrivial at *every* spectral parameter. -/
theorem prolate_jacobiDeficiency_ne_bot (hβ : 0 ≤ β) (hγ : 2 ≤ γ)
    (hA : 0 < 16 * Real.pi * lam ^ 2) {q : ℕ → ℝ}
    (hq : ∀ n : ℕ, (prolateBase β γ (n + 1) + prolateBase β γ n) / 4 + q (n + 1)
        = 3 / 4 + 2 * Real.pi * lam ^ 2 * (8 * ((n : ℝ) + 1) + c))
    (Z : ℂ) :
    jacobiDeficiency (prolateRho β γ) q Z ≠ ⊥ := by
  classical
  have ha : ∀ n, prolateRho β γ n ≠ 0 := fun n => (prolateRho_pos hβ hγ).ne'
  set A : ℕ → ℂ := fun n => ((prolateRho β γ n : ℝ) : ℂ) with hAdef
  set B : ℕ → ℂ := fun n => ((q n : ℝ) : ℂ) with hBdef
  have hAne : ∀ n, A n ≠ 0 := fun n => by
    simp only [hAdef, ne_eq, Complex.ofReal_eq_zero]
    exact ha n
  -- a real fundamental system at the spectral parameter zero
  set φ : ℕ → ℝ := jacobiSol (prolateRho β γ) q (0 : ℝ) 1 0 with hφdef
  set ψ : ℕ → ℝ := jacobiSol (prolateRho β γ) q (0 : ℝ) 0 1 with hψdef
  have hφ : IsJacobiRecR (prolateRho β γ) q (0 : ℝ) φ := isJacobiRecR_jacobiSol ha 1 0
  have hψ : IsJacobiRecR (prolateRho β γ) q (0 : ℝ) ψ := isJacobiRecR_jacobiSol ha 0 1
  have hφ2 : Summable fun n => φ n ^ 2 := prolate_summable_of_pos hβ hγ hA hq hφ
  have hψ2 : Summable fun n => ψ n ^ 2 := prolate_summable_of_pos hβ hγ hA hq hψ
  have hφC : IsJacobiRec (prolateRho β γ) q (0 : ℂ) (fun n => (φ n : ℂ)) := by
    have := isJacobiRec_ofReal hφ
    simpa using this
  have hψC : IsJacobiRec (prolateRho β γ) q (0 : ℂ) (fun n => (ψ n : ℂ)) := by
    have := isJacobiRec_ofReal hψ
    simpa using this
  have hφ2C : Summable fun n => ‖(φ n : ℂ)‖ ^ 2 := by
    refine hφ2.congr (fun n => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hψ2C : Summable fun n => ‖(ψ n : ℂ)‖ ^ 2 := by
    refine hψ2.congr (fun n => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- the constant Wronskian of the fundamental system
  have hWn : ∀ n : ℕ, ((prolateRho β γ n : ℝ) : ℂ)
      * ((φ n : ℂ) * (ψ (n + 1) : ℂ) - (φ (n + 1) : ℂ) * (ψ n : ℂ))
      = ((prolateRho β γ 0 : ℝ) : ℂ) := by
    intro n
    have hcw : crossWronskian (prolateRho β γ) (fun k => (φ k : ℂ)) (fun k => (ψ k : ℂ)) n
        = crossWronskian (prolateRho β γ) (fun k => (φ k : ℂ)) (fun k => (ψ k : ℂ)) 0 :=
      crossWronskian_eq_zero_of_const hφC hψC
    have h0 : crossWronskian (prolateRho β γ) (fun k => (φ k : ℂ)) (fun k => (ψ k : ℂ)) 0
        = -((prolateRho β γ 0 : ℝ) : ℂ) := by
      simp [crossWronskian, hφdef, hψdef]
    rw [h0] at hcw
    simp only [crossWronskian] at hcw
    linear_combination -hcw
  have hWne : ((prolateRho β γ 0 : ℝ) : ℂ) ≠ 0 := hAne 0
  -- the first-kind solution at `Z`
  set x : ℕ → ℂ := jacobiSol A B Z 1 ((Z - B 0) / A 0) with hxdef
  have hxrec : IsJacobiRec (prolateRho β γ) q Z x := fun n => jacobiSol_rec hAne n
  have hxbase : (q 0 : ℂ) * x 0 + (prolateRho β γ 0 : ℂ) * x 1 = Z * x 0 := by
    have h1 : x 0 = 1 := rfl
    have h2 : x 1 = (Z - B 0) / A 0 := rfl
    have h3 : ((prolateRho β γ 0 : ℝ) : ℂ) ≠ 0 := hAne 0
    rw [h1, h2, hAdef, hBdef]
    field_simp
    ring
  have hx2 : Summable fun n => ‖x n‖ ^ 2 :=
    summable_sq_of_fundamental hφC hψC hxrec hWne hWn hφ2C hψ2C
  intro hbot
  rw [Submodule.eq_bot_iff] at hbot
  have hmem : x ∈ jacobiDeficiency (prolateRho β γ) q Z := by
    rw [jacobiDeficiency, Submodule.mem_inf]
    exact ⟨⟨hxbase, hxrec⟩, (mem_sqSummable_iff x).mpr hx2⟩
  have hzero := hbot x hmem
  exact one_ne_zero (congrFun hzero 0)

/-! ## The two archimedean parity blocks at positive parameter -/

theorem prolate_A_pos {lam : ℝ} (hlam : lam ≠ 0) : 0 < 16 * Real.pi * lam ^ 2 := by
  have h2 : 0 < lam ^ 2 := lt_of_le_of_ne (sq_nonneg lam) (Ne.symm (pow_ne_zero 2 hlam))
  have hpi := Real.pi_pos
  nlinarith

/-- **The even parity block is limit circle at every positive prolate parameter.** -/
theorem prolateEven_jacobiDeficiency_ne_bot {lam : ℝ} (hlam : lam ≠ 0) (Z : ℂ) :
    jacobiDeficiency (prolateRho 20 5) (prolateDiagEven lam) Z ≠ ⊥ :=
  prolate_jacobiDeficiency_ne_bot (c := 1) (by norm_num) (by norm_num)
    (prolate_A_pos hlam) (prolateEven_key lam) Z

/-- **The odd parity block is limit circle at every positive prolate parameter.** -/
theorem prolateOdd_jacobiDeficiency_ne_bot {lam : ℝ} (hlam : lam ≠ 0) (Z : ℂ) :
    jacobiDeficiency (prolateRho 36 19) (prolateDiagOdd lam) Z ≠ ⊥ :=
  prolate_jacobiDeficiency_ne_bot (c := 5) (by norm_num) (by norm_num)
    (prolate_A_pos hlam) (prolateOdd_key lam) Z

/-- **The archimedean prolate Jacobi limit-circle transition.**  Every positive prolate parameter
puts both parity blocks in the limit-circle case — one boundary angle on each block, hence
deficiency indices `(1,1)` and `(2,2)` for the parity-preserving direct sum — while the zero
parameter puts both blocks in the limit-point case. -/
theorem prolate_limit_circle_transition (lam : ℝ) (Z : ℂ) (hZ : (starRingEnd ℂ) Z ≠ Z) :
    (lam ≠ 0 →
        jacobiDeficiency (prolateRho 20 5) (prolateDiagEven lam) Z ≠ ⊥
          ∧ jacobiDeficiency (prolateRho 36 19) (prolateDiagOdd lam) Z ≠ ⊥)
      ∧ (lam = 0 →
        jacobiDeficiency (prolateRho 20 5) (prolateDiagEven lam) Z = ⊥
          ∧ jacobiDeficiency (prolateRho 36 19) (prolateDiagOdd lam) Z = ⊥) := by
  constructor
  · intro hlam
    exact ⟨prolateEven_jacobiDeficiency_ne_bot hlam Z,
      prolateOdd_jacobiDeficiency_ne_bot hlam Z⟩
  · intro hlam
    subst hlam
    exact ⟨prolateEven_jacobiDeficiency_eq_bot Z hZ, prolateOdd_jacobiDeficiency_eq_bot Z hZ⟩

/-! ## Deficiency indices -/

theorem rank_jacobiDeficiency_eq_one {a b : ℕ → ℝ} (ha : ∀ n, a n ≠ 0) {Z : ℂ}
    (h : jacobiDeficiency a b Z ≠ ⊥) : Module.rank ℂ (jacobiDeficiency a b Z) = 1 := by
  have hnt : Nontrivial (jacobiDeficiency a b Z) := (Submodule.nontrivial_iff_ne_bot).mpr h
  have hpos : 0 < Module.rank ℂ (jacobiDeficiency a b Z) := rank_pos
  exact le_antisymm (rank_jacobiDeficiency_le_one a b ha Z) (Cardinal.one_le_iff_pos.mpr hpos)

/-- **Deficiency indices `(1,1)` for the even parity block at positive prolate parameter.** -/
theorem prolateEven_deficiency_indices {lam : ℝ} (hlam : lam ≠ 0) :
    Module.rank ℂ (jacobiDeficiency (prolateRho 20 5) (prolateDiagEven lam) Complex.I) = 1
      ∧ Module.rank ℂ
        (jacobiDeficiency (prolateRho 20 5) (prolateDiagEven lam) (-Complex.I)) = 1 := by
  have ha : ∀ n, prolateRho 20 5 n ≠ 0 := fun n =>
    (prolateRho_pos (by norm_num) (by norm_num)).ne'
  exact ⟨rank_jacobiDeficiency_eq_one ha (prolateEven_jacobiDeficiency_ne_bot hlam _),
    rank_jacobiDeficiency_eq_one ha (prolateEven_jacobiDeficiency_ne_bot hlam _)⟩

/-- **Deficiency indices `(1,1)` for the odd parity block at positive prolate parameter.** -/
theorem prolateOdd_deficiency_indices {lam : ℝ} (hlam : lam ≠ 0) :
    Module.rank ℂ (jacobiDeficiency (prolateRho 36 19) (prolateDiagOdd lam) Complex.I) = 1
      ∧ Module.rank ℂ
        (jacobiDeficiency (prolateRho 36 19) (prolateDiagOdd lam) (-Complex.I)) = 1 := by
  have ha : ∀ n, prolateRho 36 19 n ≠ 0 := fun n =>
    (prolateRho_pos (by norm_num) (by norm_num)).ne'
  exact ⟨rank_jacobiDeficiency_eq_one ha (prolateOdd_jacobiDeficiency_ne_bot hlam _),
    rank_jacobiDeficiency_eq_one ha (prolateOdd_jacobiDeficiency_ne_bot hlam _)⟩

/-- **Deficiency indices `(0,0)` for both parity blocks at zero prolate parameter.** -/
theorem prolate_deficiency_indices_zero :
    jacobiDeficiency (prolateRho 20 5) (prolateDiagEven 0) Complex.I = ⊥
      ∧ jacobiDeficiency (prolateRho 20 5) (prolateDiagEven 0) (-Complex.I) = ⊥
      ∧ jacobiDeficiency (prolateRho 36 19) (prolateDiagOdd 0) Complex.I = ⊥
      ∧ jacobiDeficiency (prolateRho 36 19) (prolateDiagOdd 0) (-Complex.I) = ⊥ := by
  have hI : (starRingEnd ℂ) Complex.I ≠ Complex.I := by
    rw [Complex.conj_I]
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hI' : (starRingEnd ℂ) (-Complex.I) ≠ -Complex.I := by
    rw [map_neg, Complex.conj_I]
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  exact ⟨prolateEven_jacobiDeficiency_eq_bot _ hI, prolateEven_jacobiDeficiency_eq_bot _ hI',
    prolateOdd_jacobiDeficiency_eq_bot _ hI, prolateOdd_jacobiDeficiency_eq_bot _ hI'⟩

end RHTower
