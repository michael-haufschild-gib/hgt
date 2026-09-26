import GaloisForLFunctions.RHTower.ThetaPowerCoefficientMass

/-!
# Square summability of the theta-power coefficients

For `0 < a < 1/2` and `u > 1/2`, `Σ_n |b_n|² (n+α)^{-u} < ∞` (`α = a/4`).

Dyadically, `x^{-u} ≤ 2^u e^{2π} Σ_{j ≥ 0} 2^{-ju} e^{-2π x 2^{-j}}` for `x ≥ 1`, and the horizontal mass bound
`Σ_n |b_n|² e^{-2π(n+α)y} ≤ C_H² y^{-1/2}` at `y = 2^{-j}` sums to `C_H² Σ_j 2^{-j(u-1/2)} < ∞`.
-/

open Complex Real Filter Topology

namespace RHTower

noncomputable section

variable {a : ℝ}

/-- `x^{-u} ≤ 2^u e^{2π} 2^{-ju} e^{-2π x 2^{-j}}` for the dyadic `j` with `2^{j-1} < x ≤ 2^j`. -/
theorem rpow_neg_le_dyadic {x u : ℝ} (hx : 1 ≤ x) (hu : 0 < u) :
    ∃ j : ℕ, x ^ (-u) ≤ 2 ^ u * Real.exp (2 * π) *
      ((1 / 2 : ℝ) ^ j) ^ u * Real.exp (-(2 * π * x * (1 / 2 : ℝ) ^ j)) := by
  -- the least `j` with `x ≤ 2^j`
  have hex : ∃ j : ℕ, x ≤ (2 : ℝ) ^ j := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)
    exact ⟨j, hj.le⟩
  classical
  set j := Nat.find hex with hj
  have hxj : x ≤ (2 : ℝ) ^ j := Nat.find_spec hex
  have hjlow : (2 : ℝ) ^ j ≤ 2 * x := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0]; simp; linarith
    · have hmin := Nat.find_min hex (show j - 1 < j by omega)
      push Not at hmin
      have : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [this]; linarith
  refine ⟨j, ?_⟩
  have h2j : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hx0 : 0 < x := by linarith
  have hhalf : ((1 / 2 : ℝ) ^ j) = ((2 : ℝ) ^ j)⁻¹ := by rw [one_div, inv_pow]
  -- `e^{-2π x 2^{-j}} ≥ e^{-2π}`
  have he : Real.exp (-(2 * π)) ≤ Real.exp (-(2 * π * x * (1 / 2 : ℝ) ^ j)) := by
    apply Real.exp_le_exp.mpr
    rw [hhalf]
    have : x * ((2 : ℝ) ^ j)⁻¹ ≤ 1 := by rw [mul_inv_le_iff₀ h2j]; linarith
    nlinarith [Real.pi_pos]
  -- `2^{-ju} ≥ (2x)^{-u}`
  have hp : (2 * x) ^ (-u) ≤ ((1 / 2 : ℝ) ^ j) ^ u := by
    rw [hhalf, Real.inv_rpow h2j.le, ← Real.rpow_neg h2j.le]
    exact Real.rpow_le_rpow_of_nonpos h2j hjlow (by linarith)
  have hsplit : x ^ (-u) = 2 ^ u * (2 * x) ^ (-u) := by
    rw [Real.mul_rpow (by norm_num) hx0.le, ← mul_assoc, ← Real.rpow_add (by norm_num), add_neg_cancel,
      Real.rpow_zero, one_mul]
  have hE : 1 ≤ Real.exp (2 * π) * Real.exp (-(2 * π * x * (1 / 2 : ℝ) ^ j)) := by
    calc (1 : ℝ) = Real.exp (2 * π) * Real.exp (-(2 * π)) := by rw [← Real.exp_add]; simp
      _ ≤ Real.exp (2 * π) * Real.exp (-(2 * π * x * (1 / 2 : ℝ) ^ j)) := by gcongr
  rw [hsplit]
  calc 2 ^ u * (2 * x) ^ (-u) ≤ 2 ^ u * ((1 / 2 : ℝ) ^ j) ^ u := by gcongr
    _ ≤ 2 ^ u * ((1 / 2 : ℝ) ^ j) ^ u *
          (Real.exp (2 * π) * Real.exp (-(2 * π * x * (1 / 2 : ℝ) ^ j))) :=
        le_mul_of_one_le_right (by positivity) hE
    _ = _ := by ring

/-- **Square summability** `Σ |b_n|² (n+α)^{-u} < ∞` for `u > 1/2`. -/
theorem summable_thetaPowerCoeff_sq_rpow (ha0 : 0 < a) (ha1 : a < 1 / 2) {u : ℝ} (hu : 1 / 2 < u) :
    Summable fun n : ℕ => ‖thetaPowerCoeff a n‖ ^ 2 * ((n : ℝ) + a / 4) ^ (-u) := by
  set CH := thetaPowerHeckeConstant a
  set g : ℕ → ℝ := fun j => ((1 / 2 : ℝ) ^ j) ^ u * thetaPowerMass a ((1 / 2 : ℝ) ^ j) with hg
  have hmass : ∀ j : ℕ, thetaPowerMass a ((1 / 2 : ℝ) ^ j) ≤ CH ^ 2 * ((2 : ℝ) ^ j) ^ (1 / 2 : ℝ) := by
    intro j
    have h := thetaPowerMass_le ha0 ha1 (y := (1 / 2 : ℝ) ^ j) (by positivity)
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [one_div, inv_pow, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_neg]
  have hgs : Summable g := by
    have hgeo : Summable fun j : ℕ => CH ^ 2 * ((1 / 2 : ℝ) ^ (u - 1 / 2)) ^ j := by
      refine (summable_geometric_of_lt_one (by positivity) ?_).mul_left _
      exact Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hgeo
    · exact mul_nonneg (by positivity) (thetaPowerMass_nonneg _ _)
    · have hA : ((1 / 2 : ℝ) ^ j) ^ u = ((1 / 2 : ℝ) ^ u) ^ j := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
          Real.rpow_natCast]
      have hB : ((2 : ℝ) ^ j) ^ (1 / 2 : ℝ) = ((2 : ℝ) ^ (1 / 2 : ℝ)) ^ j := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
          Real.rpow_natCast]
      have hC : (1 / 2 : ℝ) ^ u * (2 : ℝ) ^ (1 / 2 : ℝ) = (1 / 2 : ℝ) ^ (u - 1 / 2) := by
        rw [Real.rpow_sub (by norm_num)]
        have : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) = ((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
          rw [one_div, Real.inv_rpow (by norm_num)]
        rw [this]
        have h2 : (0 : ℝ) < (2 : ℝ) ^ (1 / 2 : ℝ) := by positivity
        field_simp
      have h1 : ((1 / 2 : ℝ) ^ j) ^ u * (CH ^ 2 * ((2 : ℝ) ^ j) ^ (1 / 2 : ℝ)) =
          CH ^ 2 * ((1 / 2 : ℝ) ^ (u - 1 / 2)) ^ j := by
        rw [hA, hB, ← hC, mul_pow]; ring
      simp only [hg]
      rw [← h1]
      exact mul_le_mul_of_nonneg_left (hmass j) (by positivity)
  set K : ℝ := 2 ^ u * Real.exp (2 * π)
  -- shift: control the terms `n ≥ 1`
  have hterm : ∀ n : ℕ, ‖thetaPowerCoeff a (n + 1)‖ ^ 2 * (((n + 1 : ℕ) : ℝ) + a / 4) ^ (-u) ≤
      K * ∑' j, ((1 / 2 : ℝ) ^ j) ^ u * (‖thetaPowerCoeff a (n + 1)‖ ^ 2 *
        Real.exp (-(2 * π * (((n + 1 : ℕ) : ℝ) + a / 4) * (1 / 2 : ℝ) ^ j))) := by
    intro n
    have hx : 1 ≤ ((n + 1 : ℕ) : ℝ) + a / 4 := by push_cast; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
    obtain ⟨j, hj⟩ := rpow_neg_le_dyadic hx (by linarith : 0 < u)
    have hs : Summable fun j : ℕ => ((1 / 2 : ℝ) ^ j) ^ u * (‖thetaPowerCoeff a (n + 1)‖ ^ 2 *
        Real.exp (-(2 * π * (((n + 1 : ℕ) : ℝ) + a / 4) * (1 / 2 : ℝ) ^ j))) := by
      refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
        ((summable_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ (1 / 2) ^ u)
          (Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith))).mul_left
          (‖thetaPowerCoeff a (n + 1)‖ ^ 2))
      have hA : ((1 / 2 : ℝ) ^ j) ^ u = ((1 / 2 : ℝ) ^ u) ^ j := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
          Real.rpow_natCast]
      have hexp : Real.exp (-(2 * π * (((n + 1 : ℕ) : ℝ) + a / 4) * (1 / 2 : ℝ) ^ j)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by
          have : 0 ≤ 2 * π * (((n + 1 : ℕ) : ℝ) + a / 4) * (1 / 2 : ℝ) ^ j := by positivity
          linarith)
      calc ((1 / 2 : ℝ) ^ j) ^ u * (‖thetaPowerCoeff a (n + 1)‖ ^ 2 *
            Real.exp (-(2 * π * (((n + 1 : ℕ) : ℝ) + a / 4) * (1 / 2 : ℝ) ^ j)))
          ≤ ((1 / 2 : ℝ) ^ j) ^ u * (‖thetaPowerCoeff a (n + 1)‖ ^ 2 * 1) := by gcongr
        _ = ‖thetaPowerCoeff a (n + 1)‖ ^ 2 * ((1 / 2 : ℝ) ^ u) ^ j := by rw [hA]; ring
    have hsingle := hs.le_tsum j (fun i _ => by positivity)
    calc ‖thetaPowerCoeff a (n + 1)‖ ^ 2 * (((n + 1 : ℕ) : ℝ) + a / 4) ^ (-u)
        ≤ ‖thetaPowerCoeff a (n + 1)‖ ^ 2 * (K * ((1 / 2 : ℝ) ^ j) ^ u *
            Real.exp (-(2 * π * (((n + 1 : ℕ) : ℝ) + a / 4) * (1 / 2 : ℝ) ^ j))) := by gcongr
      _ = K * (((1 / 2 : ℝ) ^ j) ^ u * (‖thetaPowerCoeff a (n + 1)‖ ^ 2 *
            Real.exp (-(2 * π * (((n + 1 : ℕ) : ℝ) + a / 4) * (1 / 2 : ℝ) ^ j)))) := by ring
      _ ≤ K * ∑' j, ((1 / 2 : ℝ) ^ j) ^ u * (‖thetaPowerCoeff a (n + 1)‖ ^ 2 *
            Real.exp (-(2 * π * (((n + 1 : ℕ) : ℝ) + a / 4) * (1 / 2 : ℝ) ^ j))) := by gcongr
  -- the double series is controlled by `Σ_j g_j`
  refine (summable_nat_add_iff 1).mp ?_
  refine summable_of_sum_le (c := K * ∑' j, g j) (fun n => by positivity) (fun s => ?_)
  calc ∑ n ∈ s, ‖thetaPowerCoeff a (n + 1)‖ ^ 2 * (((n + 1 : ℕ) : ℝ) + a / 4) ^ (-u)
      ≤ ∑ n ∈ s, K * ∑' j, ((1 / 2 : ℝ) ^ j) ^ u * (‖thetaPowerCoeff a (n + 1)‖ ^ 2 *
          Real.exp (-(2 * π * (((n + 1 : ℕ) : ℝ) + a / 4) * (1 / 2 : ℝ) ^ j))) :=
        Finset.sum_le_sum fun n _ => by exact_mod_cast hterm n
    _ ≤ K * ∑' j, g j := by
        rw [← Finset.mul_sum]
        gcongr
        have hsw : ∀ n ∈ s, Summable fun j : ℕ => ((1 / 2 : ℝ) ^ j) ^ u *
            (‖thetaPowerCoeff a (n + 1)‖ ^ 2 *
              Real.exp (-(2 * π * (((n + 1 : ℕ) : ℝ) + a / 4) * (1 / 2 : ℝ) ^ j))) := by
          intro n _
          refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hgs
          simp only [hg]
          gcongr
          have hms := summable_thetaPowerMass ha0.le (y := (1 / 2 : ℝ) ^ j) (by positivity)
          exact hms.le_tsum (n + 1) (fun m _ => by positivity)
        rw [← Summable.tsum_finsetSum hsw]
        refine Summable.tsum_le_tsum (fun j => ?_) (summable_sum fun n hn => hsw n hn) hgs
        simp only [hg]
        rw [← Finset.mul_sum]
        gcongr
        have hms := summable_thetaPowerMass ha0.le (y := (1 / 2 : ℝ) ^ j) (by positivity)
        have hshift := (summable_nat_add_iff 1).mpr hms
        have h1 := hshift.sum_le_tsum s (fun m _ => by positivity)
        have h2 : ∑' m : ℕ, ‖thetaPowerCoeff a (m + 1)‖ ^ 2 *
            Real.exp (-(2 * π * (((m + 1 : ℕ) : ℝ) + a / 4) * (1 / 2 : ℝ) ^ j)) ≤ thetaPowerMass a ((1 / 2 : ℝ) ^ j) := by
          unfold thetaPowerMass
          rw [hms.tsum_eq_zero_add]
          have : 0 ≤ ‖thetaPowerCoeff a 0‖ ^ 2 * Real.exp (-(2 * π * (((0 : ℕ) : ℝ) + a / 4) * (1 / 2 : ℝ) ^ j)) := by
            positivity
          linarith
        exact h1.trans h2

end

end RHTower
