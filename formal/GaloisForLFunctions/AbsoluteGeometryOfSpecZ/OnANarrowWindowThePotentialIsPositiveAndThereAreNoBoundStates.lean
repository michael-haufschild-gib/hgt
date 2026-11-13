import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.OnANarrowWindowThePotentialIsShallowAndTheCountOfBoundStatesIsOne
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TwoCoupledWindowsAreBracketedByLoweredAndRaisedPotentialsAndGluedThroughResponseMatrices

/-!
# On a narrow window the potential is positive and there are no bound states

Refining the step enclosure of `Δ(n) = (n + 1) log(n + 1) − n log n` around the half-integer
midpoint `n + ½` (`xLogXStep_le_log_add_half`, `log_add_half_sub_le_xLogXStep`) sharpens both the
potential of a narrow window and the monotonicity of the archimedean jet:

* **Monotonicity of the jet** (`blockJet_lt_of_lt`): for `1 ≤ a₁ < a₂ < b`,
  `blockJet a₁ b < blockJet a₂ b`.
* **Positive potential and zero bound states on narrow windows**
  (`one_lt_blockPotential_of_narrow`, `hermNegIndex_neutralWindow_eq_zero_of_narrow`,
  `bilin_neutralWindow_pos_of_narrow`): when `16 J ≤ R`, every block of `(R, R + J]` has potential
  strictly above `1`, so `neutralWindow Q R J` is strictly positive definite and holds `0` bound
  states.
* **Susceptibility dichotomy on adjacent narrow windows.** When `16 (J₁ + J₂) ≤ R`, the union
  `(R, R + J₁ + J₂]` also holds `0` bound states (`hermNegIndex_neutralWindow_add_eq_zero_of_narrow`),
  and both zero-charge lowered halves are strictly positive definite:
  - Under same-sign admissible charges (`0 ≤ u_i v_j ≤ K_ij`), both lowered forms stay positive
    definite and their susceptibilities are nonnegative (`chargeOf_nonneg_of_narrow_same_sign`).
  - Under general admissible charges (`u_i v_j ≤ K_ij`), opposite-sign spike charges pushed just
    past the Schur threshold give negative susceptibilities on both halves, nonnegative lowered
    kernels, and an arbitrarily large susceptibility product
    (`exists_admissible_susceptibility_mul_ge_of_posDef`,
    `exists_narrow_admissible_susceptibility_mul_ge`).
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Midpoint enclosure of `Δ(n)` and monotonicity of the jet -/

/-- Upper midpoint bound: `Δ(n) ≤ log(n + ½) + 1` for every `n ≥ 0`. -/
theorem xLogXStep_le_log_add_half (n : ℕ) :
    xLogXStep n ≤ Real.log ((n : ℝ) + 1 / 2) + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [xLogXStep_zero, Nat.cast_zero, zero_add, one_div, Real.log_inv]
    linarith [Real.log_two_lt_d9]
  · set u : ℝ := (n : ℝ) + 1 / 2
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hu0 : 0 < u := by positivity
    have hn1 : 0 < (n : ℝ) + 1 := by positivity
    have hstep : xLogXStep n - Real.log u =
        ((n : ℝ) + 1) * Real.log (((n : ℝ) + 1) / u) + (n : ℝ) * Real.log (u / n) := by
      rw [xLogXStep, xLogX, xLogX, Real.log_div hn1.ne' hu0.ne', Real.log_div hu0.ne' hn0.ne']
      push_cast
      ring
    set x₁ : ℝ := ((n : ℝ) + 1) / u
    set x₂ : ℝ := u / n
    have hx₁ : 1 ≤ x₁ := by
      rw [le_div_iff₀ hu0]
      dsimp [u]
      linarith
    have hx₂ : 1 ≤ x₂ := by
      rw [le_div_iff₀ hn0]
      dsimp [u]
      linarith
    have hb₁ := mul_le_mul_of_nonneg_left (RHTower.log_le_geometric_cubic hx₁) hn1.le
    have hb₂ := mul_le_mul_of_nonneg_left (RHTower.log_le_geometric_cubic hx₂) hn0.le
    have h2n1 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
    have h4n1 : (0 : ℝ) < 4 * (n : ℝ) + 1 := by positivity
    have h4n3 : (0 : ℝ) < 4 * (n : ℝ) + 3 := by positivity
    have hrat : ((n : ℝ) + 1) * (2 * (x₁ - 1) / (x₁ + 1) + (x₁ - 1) ^ 3 / (6 * x₁ * (x₁ + 1))) +
        (n : ℝ) * (2 * (x₂ - 1) / (x₂ + 1) + (x₂ - 1) ^ 3 / (6 * x₂ * (x₂ + 1))) =
        1 - 2 / (3 * (4 * (n : ℝ) + 1) * (4 * (n : ℝ) + 3)) := by
      dsimp [x₁, x₂, u]
      field_simp
      ring
    have hrem : 0 ≤ 2 / (3 * (4 * (n : ℝ) + 1) * (4 * (n : ℝ) + 3)) := by positivity
    linarith

/-- Lower midpoint bound: `log(n + ½) + 1 − 1/((4n + 1)(4n + 3)) ≤ Δ(n)` for `n ≥ 1`. -/
theorem log_add_half_sub_le_xLogXStep {n : ℕ} (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 1 / 2) + 1 - 1 / ((4 * (n : ℝ) + 1) * (4 * (n : ℝ) + 3)) ≤
      xLogXStep n := by
  set u : ℝ := (n : ℝ) + 1 / 2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hu0 : 0 < u := by positivity
  have hn1 : 0 < (n : ℝ) + 1 := by positivity
  have hstep : xLogXStep n - Real.log u =
      ((n : ℝ) + 1) * Real.log (((n : ℝ) + 1) / u) + (n : ℝ) * Real.log (u / n) := by
    rw [xLogXStep, xLogX, xLogX, Real.log_div hn1.ne' hu0.ne', Real.log_div hu0.ne' hn0.ne']
    push_cast
    ring
  set z₁ : ℝ := 1 / (2 * (n : ℝ) + 1)
  set z₂ : ℝ := 1 / (2 * (n : ℝ))
  have hlo₁ := (Real.lt_log_one_add_of_pos (show 0 < z₁ by positivity)).le
  have hlo₂ := (Real.lt_log_one_add_of_pos (show 0 < z₂ by positivity)).le
  have harg₁ : 1 + z₁ = ((n : ℝ) + 1) / u := by
    dsimp [z₁, u]
    field_simp
    ring
  have harg₂ : 1 + z₂ = u / n := by
    dsimp [z₂, u]
    field_simp
  rw [harg₁] at hlo₁
  rw [harg₂] at hlo₂
  have hb₁ := mul_le_mul_of_nonneg_left hlo₁ hn1.le
  have hb₂ := mul_le_mul_of_nonneg_left hlo₂ hn0.le
  have h4n1 : (0 : ℝ) < 4 * (n : ℝ) + 1 := by positivity
  have h4n3 : (0 : ℝ) < 4 * (n : ℝ) + 3 := by positivity
  have hrat : ((n : ℝ) + 1) * (2 * z₁ / (z₁ + 2)) + (n : ℝ) * (2 * z₂ / (z₂ + 2)) =
      1 - 1 / ((4 * (n : ℝ) + 1) * (4 * (n : ℝ) + 3)) := by
    dsimp [z₁, z₂]
    field_simp
    ring
  linarith

/-- For `n ≥ 2`, the second difference of `n log n` satisfies `xLogXDiff n ≤ 2 / (2n − 1)`. -/
theorem xLogXDiff_le_two_div {n : ℕ} (hn : 2 ≤ n) :
    xLogXDiff n ≤ 2 / (2 * (n : ℝ) - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [xLogXDiff_eq_step (by omega)]
  have hhi := xLogXStep_le_log_add_half (k + 2)
  have hlo := log_add_half_sub_le_xLogXStep (n := k + 1) (by omega)
  have hsub1 : k + 2 - 1 = k + 1 := by omega
  rw [hsub1]
  set u₁ : ℝ := ((k + 2 : ℕ) : ℝ) + 1 / 2
  set u₀ : ℝ := ((k + 1 : ℕ) : ℝ) + 1 / 2
  have hu₀ : 0 < u₀ := by dsimp [u₀]; positivity
  have hu₁ : 0 < u₁ := by dsimp [u₁]; positivity
  set x : ℝ := u₁ / u₀
  have hx : 1 ≤ x := by
    rw [le_div_iff₀ hu₀]
    dsimp [u₁, u₀]
    push_cast
    linarith
  have hlog : Real.log u₁ - Real.log u₀ ≤
      2 * (x - 1) / (x + 1) + (x - 1) ^ 3 / (6 * x * (x + 1)) := by
    rw [← Real.log_div hu₁.ne' hu₀.ne']
    exact RHTower.log_le_geometric_cubic hx
  have hx_eq : x = (2 * (k : ℝ) + 5) / (2 * (k : ℝ) + 3) := by
    dsimp [x, u₁, u₀]
    push_cast
    field_simp
    ring
  have hdiff : 2 / (2 * ((k + 2 : ℕ) : ℝ) - 1) -
      (2 * (x - 1) / (x + 1) + (x - 1) ^ 3 / (6 * x * (x + 1)) +
        1 / ((4 * ((k + 1 : ℕ) : ℝ) + 1) * (4 * ((k + 1 : ℕ) : ℝ) + 3))) =
      (84 * (k : ℝ) ^ 3 + 440 * (k : ℝ) ^ 2 + 741 * (k : ℝ) + 400) /
        (3 * ((k : ℝ) + 2) * (2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 5) *
          (4 * (k : ℝ) + 5) * (4 * (k : ℝ) + 7)) := by
    rw [hx_eq]
    push_cast
    have h1 : (0 : ℝ) < 2 * (k : ℝ) + 3 := by positivity
    rw [show (2 : ℝ) * ((k : ℝ) + 2) - 1 = 2 * (k : ℝ) + 3 by ring,
      show (4 : ℝ) * ((k : ℝ) + 1) + 1 = 4 * (k : ℝ) + 5 by ring,
      show (4 : ℝ) * ((k : ℝ) + 1) + 3 = 4 * (k : ℝ) + 7 by ring]
    field_simp
    ring
  have hpos : 0 ≤ (84 * (k : ℝ) ^ 3 + 440 * (k : ℝ) ^ 2 + 741 * (k : ℝ) + 400) /
      (3 * ((k : ℝ) + 2) * (2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 5) *
        (4 * (k : ℝ) + 5) * (4 * (k : ℝ) + 7)) := by positivity
  linarith

private theorem hasDerivAt_shift_mul_log {u a : ℝ} (h : u + a ≠ 0) :
    HasDerivAt (fun x : ℝ => (x + a) * Real.log (x + a)) (Real.log (u + a) + 1) u := by
  have hb : HasDerivAt (fun x : ℝ => x + a) 1 u := (hasDerivAt_id u).add_const a
  have hl := (Real.hasDerivAt_log h).comp u hb
  have hfun : (Real.log ∘ fun x : ℝ => x + a) = fun x : ℝ => Real.log (x + a) := rfl
  rw [hfun] at hl
  exact (hb.mul hl).congr_deriv (by field_simp)

/-- The negative third difference `xLogXDiff n − xLogXDiff (n + 1)` is strictly decreasing for
`n ≥ 1`. -/
theorem xLogXDiff_sub_succ_lt {d s : ℕ} (hd : 1 ≤ d) (hds : d < s) :
    xLogXDiff s - xLogXDiff (s + 1) < xLogXDiff d - xLogXDiff (d + 1) := by
  by_cases hd1 : d = 1
  · subst hd1
    have hs2 : 2 ≤ s := by omega
    have hd1_val : xLogXDiff 1 = 2 * Real.log 2 := by
      simp [xLogXDiff, xLogX]
    have hd2_val : xLogXDiff 2 = 3 * Real.log 3 - 4 * Real.log 2 := by
      simp only [xLogXDiff, xLogX, Nat.reduceAdd, Nat.reduceSub, Nat.cast_one, Real.log_one]
      norm_num
      ring
    have hlo : (17 / 20 : ℝ) < xLogXDiff 1 - xLogXDiff 2 := by
      rw [hd1_val, hd2_val]
      linarith [Real.log_two_gt_d9, log_three_mem.2]
    have hhi_s : xLogXDiff s ≤ 2 / 3 := by
      have hs_real : (2 : ℝ) ≤ s := by exact_mod_cast hs2
      exact (xLogXDiff_le_two_div hs2).trans
        (div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith))
    have hpos_succ : 0 < xLogXDiff (s + 1) := xLogXDiff_pos (by omega)
    linarith
  · have hd2 : 2 ≤ d := by omega
    let g : ℝ → ℝ := fun u =>
      (u + (-1)) * Real.log (u + (-1)) - 3 * ((u + 0) * Real.log (u + 0)) +
        3 * ((u + 1) * Real.log (u + 1)) - (u + 2) * Real.log (u + 2)
    have hgd : ∀ {u : ℝ}, 1 < u → HasDerivAt g
        (Real.log (u - 1) - 3 * Real.log u + 3 * Real.log (u + 1) - Real.log (u + 2)) u := by
      intro u hu
      have t1 := hasDerivAt_shift_mul_log (u := u) (a := -1) (by linarith)
      have t2 := (hasDerivAt_shift_mul_log (u := u) (a := 0) (by linarith)).const_mul 3
      have t3 := (hasDerivAt_shift_mul_log (u := u) (a := 1) (by linarith)).const_mul 3
      have t4 := hasDerivAt_shift_mul_log (u := u) (a := 2) (by linarith)
      exact (((t1.sub t2).add t3).sub t4).congr_deriv (by
        rw [show u + (-1) = u - 1 by ring, add_zero]
        ring)
    have hanti : StrictAntiOn g (Set.Ici (2 : ℝ)) := by
      refine strictAntiOn_of_deriv_neg (convex_Ici 2) ?_ ?_
      · intro u hu
        exact (hgd (by linarith [Set.mem_Ici.mp hu])).continuousAt.continuousWithinAt
      · intro u hu
        have hu1 : 1 < u := by linarith [Set.mem_Ici.mp (interior_subset hu)]
        rw [(hgd hu1).deriv]
        have hu_m1 : 0 < u - 1 := by linarith
        have hu_0 : 0 < u := by linarith
        have hu_p1 : 0 < u + 1 := by linarith
        have hu_p2 : 0 < u + 2 := by linarith
        have hlogs : Real.log (u - 1) - 3 * Real.log u + 3 * Real.log (u + 1) -
            Real.log (u + 2) =
            Real.log ((u - 1) * (u + 1) ^ 3) - Real.log (u ^ 3 * (u + 2)) := by
          rw [Real.log_mul hu_m1.ne' (by positivity), Real.log_mul (by positivity) hu_p2.ne',
            Real.log_pow, Real.log_pow]
          push_cast
          ring
        rw [hlogs, sub_lt_zero]
        refine Real.log_lt_log (by positivity) ?_
        have hpoly : u ^ 3 * (u + 2) - (u - 1) * (u + 1) ^ 3 = 2 * u + 1 := by ring
        linarith
    have hgeval : ∀ {n : ℕ}, 2 ≤ n → xLogXDiff n - xLogXDiff (n + 1) = g n := by
      intro n hn
      simp only [xLogXDiff, xLogX, g]
      have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hc, show (n : ℝ) + (-1) = (n : ℝ) - 1 by ring, add_zero]
      push_cast
      rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
      ring
    rw [hgeval (by omega), hgeval hd2]
    exact hanti (show (2 : ℝ) ≤ d by exact_mod_cast hd2)
      (show (2 : ℝ) ≤ s by exact_mod_cast (by omega : 2 ≤ s))
      (by exact_mod_cast hds)

/-- **Strict monotonicity of the archimedean block jet.** Moving the lower block closer to `b`
strictly increases `blockJet`. -/
theorem blockJet_lt_of_lt {a₁ a₂ b : ℕ} (ha₁ : 1 ≤ a₁) (h12 : a₁ < a₂) (h2b : a₂ < b) :
    blockJet a₁ b < blockJet a₂ b := by
  have hstep : ∀ {a : ℕ}, 1 ≤ a → a + 1 < b → blockJet a b < blockJet (a + 1) b := by
    intro a ha hab
    simp only [blockJet]
    have hd : b - a = (b - (a + 1)) + 1 := by omega
    have hs : a + 1 + b + 1 = (a + b + 1) + 1 := by omega
    rw [hd, hs]
    have hlt := xLogXDiff_sub_succ_lt (d := b - (a + 1)) (s := a + b + 1) (by omega) (by omega)
    linarith
  obtain ⟨k, rfl⟩ : ∃ k, a₂ = a₁ + 1 + k := ⟨a₂ - a₁ - 1, by omega⟩
  induction k with
  | zero =>
    rw [add_zero]
    exact hstep ha₁ h2b
  | succ k ih =>
    have hprev := ih (by omega) (by omega)
    rw [show a₁ + 1 + (k + 1) = (a₁ + 1 + k) + 1 by omega] at h2b ⊢
    exact hprev.trans (hstep (by omega) h2b)

/-! ### Positive potential and strict positive definiteness on narrow windows -/

/-- **On a narrow window (`16 J ≤ R`) every block has potential strictly above `1`.** -/
theorem one_lt_blockPotential_of_narrow {Q R J j : ℕ} (hJ : 16 * J ≤ R) (hj : j < J) :
    1 < blockPotential Q R J j := by
  have hJ1 : 1 ≤ J := by omega
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ1
  rw [blockPotential_eq_of_window (by omega) hj]
  have hρ : blockDensity (R + j) =
      xLogXStep (R + j) - (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) := rfl
  rw [hρ]
  set a : ℕ := R + j
  set m : ℕ := R + j + R
  have ha1 : 1 ≤ a := by omega
  have hm1 : 1 ≤ m := by omega
  have hb_a := log_add_half_sub_le_xLogXStep ha1
  have hb_mJ := xLogXStep_le_log_add_half (m + J)
  have hb_m := log_add_half_sub_le_xLogXStep hm1
  have hb_j := xLogXStep_le_log_add_half j
  have hb_Jj := xLogXStep_le_log_add_half (J - 1 - j)
  -- `a + 1/2 ≥ 16 J`
  have haR : (16 : ℝ) * J ≤ (a : ℝ) + 1 / 2 := by
    have h : ((16 * J : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 16 * J ≤ a by omega)
    push_cast at h
    linarith
  have hlogA : 4 * Real.log 2 + Real.log J ≤ Real.log ((a : ℝ) + 1 / 2) := by
    have h16 : 4 * Real.log 2 + Real.log J = Real.log (16 * (J : ℝ)) := by
      rw [Real.log_mul (by norm_num) hJr.ne', log_sixteen]
    rw [h16]
    exact Real.log_le_log (by positivity) haR
  -- AM–GM on `(j + 1/2) + (J - 1 - j + 1/2) = J`
  set x : ℝ := (j : ℝ) + 1 / 2
  set y : ℝ := ((J - 1 - j : ℕ) : ℝ) + 1 / 2
  have hx : 0 < x := by positivity
  have hy : 0 < y := by positivity
  have hxy_sum : x + y = (J : ℝ) := by
    dsimp [x, y]
    have hnat : j + (J - 1 - j) + 1 = J := by omega
    have hcast : (j : ℝ) + ((J - 1 - j : ℕ) : ℝ) + 1 = (J : ℝ) := by exact_mod_cast hnat
    linarith
  have hxy_prod : x * y ≤ ((J : ℝ) / 2) ^ 2 := by
    have hsq : 0 ≤ (x - y) ^ 2 := sq_nonneg _
    have hid : ((J : ℝ) / 2) ^ 2 - x * y = (x - y) ^ 2 / 4 := by
      rw [← hxy_sum]
      ring
    linarith
  have hlog_xy : Real.log x + Real.log y ≤ 2 * (Real.log J - Real.log 2) := by
    rw [← Real.log_mul hx.ne' hy.ne']
    have hle := Real.log_le_log (mul_pos hx hy) hxy_prod
    have hrhs : Real.log (((J : ℝ) / 2) ^ 2) = 2 * (Real.log J - Real.log 2) := by
      rw [Real.log_pow, Real.log_div hJr.ne' (by norm_num)]
      push_cast
      ring
    rwa [hrhs] at hle
  -- sum-jet difference `m ≥ 32 J`
  have hmR : (32 : ℝ) * J ≤ (m : ℝ) + 1 / 2 := by
    have h : ((32 * J : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 32 * J ≤ m by omega)
    push_cast at h
    linarith
  have hmpos : (0 : ℝ) < (m : ℝ) + 1 / 2 := by positivity
  have hlogM : Real.log (((m + J : ℕ) : ℝ) + 1 / 2) - Real.log ((m : ℝ) + 1 / 2) ≤ 1 / 32 := by
    have hpos : (0 : ℝ) < ((m + J : ℕ) : ℝ) + 1 / 2 := by positivity
    rw [← Real.log_div hpos.ne' hmpos.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hpos hmpos)
    have h2 : (((m + J : ℕ) : ℝ) + 1 / 2) / ((m : ℝ) + 1 / 2) - 1 ≤ 1 / 32 := by
      rw [div_sub_one hmpos.ne', div_le_div_iff₀ hmpos (by norm_num)]
      push_cast
      linarith
    linarith
  have ha16 : (16 : ℝ) ≤ a := by exact_mod_cast (show 16 ≤ a by omega)
  have hm32 : (32 : ℝ) ≤ m := by exact_mod_cast (show 32 ≤ m by omega)
  have hrem_a : 1 / ((4 * (a : ℝ) + 1) * (4 * (a : ℝ) + 3)) ≤ 1 / (65 * 67) :=
    one_div_le_one_div_of_le (by norm_num) (mul_le_mul (by linarith) (by linarith) (by norm_num)
      (by positivity))
  have hrem_m : 1 / ((4 * (m : ℝ) + 1) * (4 * (m : ℝ) + 3)) ≤ 1 / (129 * 131) :=
    one_div_le_one_div_of_le (by norm_num) (mul_le_mul (by linarith) (by linarith) (by norm_num)
      (by positivity))
  have hγ := RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have hπ : Real.log (2 * Real.pi) < Real.log 2 + 1.1447302 := by
    rw [log_two_pi]
    linarith [log_pi_lt]
  linarith [Real.log_two_gt_d9]

theorem blockPotential_pos_of_narrow {Q R J j : ℕ} (hJ : 16 * J ≤ R) (hj : j < J) :
    0 < blockPotential Q R J j :=
  lt_trans zero_lt_one (one_lt_blockPotential_of_narrow hJ hj)

/-- **A narrow window (`16 J ≤ R`) holds no bound states.** -/
theorem hermNegIndex_neutralWindow_eq_zero_of_narrow {Q R J : ℕ} (hJ : 16 * J ≤ R) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 0 := by
  have h := hermNegIndex_neutralWindow_le_card_wells Q R J
  have h0 : Fintype.card {j : Fin J // blockPotential Q R J j < 0} = 0 :=
    Fintype.card_eq_zero_iff.mpr
      ⟨fun j => absurd j.2 (not_lt.mpr (blockPotential_pos_of_narrow hJ j.1.2).le)⟩
  rw [h0] at h
  exact Nat.eq_zero_of_le_zero h

/-- **On a narrow window (`16 J ≤ R`), `neutralWindow` dominates the Euclidean norm square.** -/
theorem sum_sq_le_bilin_neutralWindow_of_narrow {Q R J : ℕ} (hJ : 16 * J ≤ R) (x : Fin J → ℝ) :
    ∑ i, x i ^ 2 ≤ bilin (neutralWindow Q R J) x x := by
  have h := sum_div_mul_mulVec_le (neutralWindow Q R J) (fun i j => neutralBlock_comm Q _ _)
    (fun i j hij => (neutralBlock_neg (fun heq => hij (Fin.ext (Nat.add_left_cancel heq))) Q).le)
    (v := fun _ => (1 : ℝ)) (fun _ => one_pos) x
  have hge : ∑ i, x i ^ 2 ≤
      ∑ i, x i ^ 2 / (1 : ℝ) * (neutralWindow Q R J *ᵥ fun _ => (1 : ℝ)) i := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [div_one, neutralWindow_mulVec_one]
    exact le_mul_of_one_le_right (sq_nonneg _) (one_lt_blockPotential_of_narrow hJ i.2).le
  exact hge.trans h

/-- **Strict positive definiteness of `neutralWindow` on narrow windows.** -/
theorem bilin_neutralWindow_pos_of_narrow {Q R J : ℕ} (hJ : 16 * J ≤ R) {x : Fin J → ℝ}
    (hx : x ≠ 0) : 0 < bilin (neutralWindow Q R J) x x := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  have hpos : 0 < ∑ i, x i ^ 2 :=
    lt_of_lt_of_le (sq_pos_of_ne_zero hi₀)
      (Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ i₀))
  exact lt_of_lt_of_le hpos (sum_sq_le_bilin_neutralWindow_of_narrow hJ x)

/-- **The union of two narrow windows (`16 (J₁ + J₂) ≤ R`) holds no bound states.** -/
theorem hermNegIndex_neutralWindow_add_eq_zero_of_narrow {Q R J₁ J₂ : ℕ}
    (hJ : 16 * (J₁ + J₂) ≤ R) :
    hermNegIndex ((neutralWindow Q R (J₁ + J₂)).map (↑) : Matrix (Fin (J₁ + J₂)) _ ℂ) = 0 :=
  hermNegIndex_neutralWindow_eq_zero_of_narrow hJ

/-! ### Zero-charge lowered halves and the susceptibility dichotomy on narrow windows -/

/-- On a narrow union `16 (J₁ + J₂) ≤ R`, the left half lowered by all cross-couplings still
dominates the Euclidean norm square. -/
theorem sum_sq_le_bilin_lowered_left_of_narrow {Q R J₁ J₂ : ℕ} (hJ : 16 * (J₁ + J₂) ≤ R)
    (x : Fin J₁ → ℝ) :
    ∑ i, x i ^ 2 ≤
      bilin (neutralWindow Q R J₁ -
        diagonal fun i : Fin J₁ => ∑ j : Fin J₂, blockWeight Q (R + i) (R + J₁ + j)) x x := by
  set A₀ := neutralWindow Q R J₁ -
    diagonal fun i : Fin J₁ => ∑ j : Fin J₂, blockWeight Q (R + i) (R + J₁ + j)
  have hsym : ∀ i l, A₀ i l = A₀ l i := sub_diagonal_symm (fun i l => neutralBlock_comm Q _ _) _
  have hoff : ∀ i l, i ≠ l → A₀ i l ≤ 0 := fun i l hil => by
    simp only [A₀, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hil, sub_zero]
    exact (neutralBlock_neg (fun heq => hil (Fin.ext (Nat.add_left_cancel heq))) Q).le
  have hrow : ∀ i : Fin J₁, (A₀ *ᵥ fun _ => (1 : ℝ)) i = blockPotential Q R (J₁ + J₂) i := by
    intro i
    have hsub : (A₀ *ᵥ fun _ => (1 : ℝ)) i =
        (neutralWindow Q R J₁ *ᵥ fun _ => (1 : ℝ)) i -
          ∑ j : Fin J₂, blockWeight Q (R + i) (R + J₁ + j) := by
      simp only [A₀, mulVec, dotProduct, Matrix.sub_apply, mul_one, Finset.sum_sub_distrib]
      congr 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro l _ hli
        exact Matrix.diagonal_apply_ne _ (Ne.symm hli)
      · exact fun h => absurd (Finset.mem_univ i) h
    rw [hsub, neutralWindow_mulVec_one, blockPotential, blockPotential, Finset.sum_range_add,
      Fin.sum_univ_eq_sum_range (fun m => blockWeight Q (R + i) (R + J₁ + m)) J₂]
    have h2 : -∑ m ∈ range J₂, blockWeight Q (R + i) (R + J₁ + m) =
        ∑ m ∈ range J₂, neutralBlock Q (R + i) (R + (J₁ + m)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [blockWeight, neg_neg, add_assoc]
    linarith
  have h := sum_div_mul_mulVec_le A₀ hsym hoff (v := fun _ => (1 : ℝ)) (fun _ => one_pos) x
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) h
  rw [div_one, hrow]
  exact le_mul_of_one_le_right (sq_nonneg _)
    (one_lt_blockPotential_of_narrow hJ (by have := i.2; omega)).le

/-- On a narrow union `16 (J₁ + J₂) ≤ R`, the right half lowered by all cross-couplings still
dominates the Euclidean norm square. -/
theorem sum_sq_le_bilin_lowered_right_of_narrow {Q R J₁ J₂ : ℕ} (hJ : 16 * (J₁ + J₂) ≤ R)
    (y : Fin J₂ → ℝ) :
    ∑ j, y j ^ 2 ≤
      bilin (neutralWindow Q (R + J₁) J₂ -
        diagonal fun j : Fin J₂ => ∑ i : Fin J₁, blockWeight Q (R + i) (R + J₁ + j)) y y := by
  set B₀ := neutralWindow Q (R + J₁) J₂ -
    diagonal fun j : Fin J₂ => ∑ i : Fin J₁, blockWeight Q (R + i) (R + J₁ + j)
  have hsym : ∀ j m, B₀ j m = B₀ m j := sub_diagonal_symm (fun j m => neutralBlock_comm Q _ _) _
  have hoff : ∀ j m, j ≠ m → B₀ j m ≤ 0 := fun j m hjm => by
    simp only [B₀, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hjm, sub_zero]
    exact (neutralBlock_neg (fun heq => hjm (Fin.ext (Nat.add_left_cancel heq))) Q).le
  have hrow : ∀ j : Fin J₂,
      (B₀ *ᵥ fun _ => (1 : ℝ)) j = blockPotential Q R (J₁ + J₂) (J₁ + j) := by
    intro j
    have hsub : (B₀ *ᵥ fun _ => (1 : ℝ)) j =
        (neutralWindow Q (R + J₁) J₂ *ᵥ fun _ => (1 : ℝ)) j -
          ∑ i : Fin J₁, blockWeight Q (R + i) (R + J₁ + j) := by
      simp only [B₀, mulVec, dotProduct, Matrix.sub_apply, mul_one, Finset.sum_sub_distrib]
      congr 1
      rw [Finset.sum_eq_single j]
      · simp
      · intro m _ hmj
        exact Matrix.diagonal_apply_ne _ (Ne.symm hmj)
      · exact fun h => absurd (Finset.mem_univ j) h
    rw [hsub, neutralWindow_mulVec_one, blockPotential, blockPotential, Finset.sum_range_add,
      Fin.sum_univ_eq_sum_range (fun i => blockWeight Q (R + i) (R + J₁ + j)) J₁]
    have h1 : -∑ i ∈ range J₁, blockWeight Q (R + i) (R + J₁ + j) =
        ∑ i ∈ range J₁, neutralBlock Q (R + (J₁ + j)) (R + i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [blockWeight, neg_neg, neutralBlock_comm, add_assoc]
    have h2 : ∑ l ∈ range J₂, neutralBlock Q (R + J₁ + j) (R + J₁ + l) =
        ∑ l ∈ range J₂, neutralBlock Q (R + (J₁ + j)) (R + (J₁ + l)) :=
      Finset.sum_congr rfl fun l _ => by rw [add_assoc, add_assoc]
    linarith
  have h := sum_div_mul_mulVec_le B₀ hsym hoff (v := fun _ => (1 : ℝ)) (fun _ => one_pos) y
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) h
  rw [div_one, hrow]
  exact le_mul_of_one_le_right (sq_nonneg _)
    (one_lt_blockPotential_of_narrow hJ (by have := j.2; omega)).le

/-- **Same-sign admissible charges on narrow windows have nonnegative susceptibilities.** When
`16 (J₁ + J₂) ≤ R` and `0 ≤ u_i v_j ≤ K_ij`, both lowered forms remain positive semidefinite, so
neither susceptibility can be negative. -/
theorem chargeOf_nonneg_of_narrow_same_sign {Q R J₁ J₂ : ℕ} (hJ : 16 * (J₁ + J₂) ≤ R)
    {u a : Fin J₁ → ℝ} {v b : Fin J₂ → ℝ}
    (hpos_uv : ∀ i j, 0 ≤ u i * v j)
    (hAa : ∀ i, ∑ l,
      (neutralWindow Q R J₁ -
        diagonal (excessLeft
          (fun (i : Fin J₁) (j : Fin J₂) => blockWeight Q (R + i) (R + J₁ + j)) u v)) i l *
          a l = u i)
    (hBb : ∀ j, ∑ m,
      (neutralWindow Q (R + J₁) J₂ -
        diagonal (excessRight
          (fun (i : Fin J₁) (j : Fin J₂) => blockWeight Q (R + i) (R + J₁ + j)) u v)) j m *
          b m = v j) :
    0 ≤ chargeOf u a ∧ 0 ≤ chargeOf v b := by
  set K : Fin J₁ → Fin J₂ → ℝ := fun i j => blockWeight Q (R + i) (R + J₁ + j)
  constructor
  · rw [← bilin_right_eq_chargeOf hAa a, bilin_sub_diagonal]
    have hex : ∑ i, excessLeft K u v i * a i ^ 2 ≤ ∑ i, (∑ j, K i j) * a i ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
        (Finset.sum_le_sum fun j _ => sub_le_self _ (hpos_uv i j)) (sq_nonneg _)
    have hA₀ := sum_sq_le_bilin_lowered_left_of_narrow (Q := Q) hJ a
    rw [bilin_sub_diagonal] at hA₀
    have ha2 : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  · rw [← bilin_right_eq_chargeOf hBb b, bilin_sub_diagonal]
    have hex : ∑ j, excessRight K u v j * b j ^ 2 ≤ ∑ j, (∑ i, K i j) * b j ^ 2 :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
        (Finset.sum_le_sum fun i _ => sub_le_self _ (hpos_uv i j)) (sq_nonneg _)
    have hB₀ := sum_sq_le_bilin_lowered_right_of_narrow (Q := Q) hJ b
    rw [bilin_sub_diagonal] at hB₀
    have hb2 : 0 ≤ ∑ j, b j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    linarith

/-- **Arbitrarily large susceptibility product on positive-definite windows under general
admissible charges.** Whenever the zero-charge lowered forms `A − diag(K 1)` and `B − diag(Kᵀ 1)`
are strictly positive definite and `K ≥ 0`, opposite-sign spike charges `u = −p e_{i₀}` and
`v = e_{j₀}` pushed just past `max(1/c_A, 1/c_B)` are admissible (`u_i v_j ≤ 0 ≤ K_ij`), make both
lowered forms nonnegative on `ker u` and `ker v`, make both susceptibilities negative, and send
`(u · a)(v · b)` above any prescribed bound `M`. -/
theorem exists_admissible_susceptibility_mul_ge_of_posDef
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (i₀ : ι₁) (j₀ : ι₂) {A : Matrix ι₁ ι₁ ℝ} {B : Matrix ι₂ ι₂ ℝ} {K : ι₁ → ι₂ → ℝ}
    (hK0 : ∀ i j, 0 ≤ K i j)
    (hA₀ : ∀ x : ι₁ → ℝ, x ≠ 0 → 0 < bilin (A - diagonal fun i => ∑ j, K i j) x x)
    (hB₀ : ∀ y : ι₂ → ℝ, y ≠ 0 → 0 < bilin (B - diagonal fun j => ∑ i, K i j) y y)
    (M : ℝ) :
    ∃ (u a : ι₁ → ℝ) (v b : ι₂ → ℝ),
      (∀ i j, u i * v j ≤ K i j) ∧
      (∀ i, ∑ l, (A - diagonal (excessLeft K u v)) i l * a l = u i) ∧
      (∀ j, ∑ m, (B - diagonal (excessRight K u v)) j m * b m = v j) ∧
      (∀ x, chargeOf u x = 0 → 0 ≤ bilin (A - diagonal (excessLeft K u v)) x x) ∧
      (∀ y, chargeOf v y = 0 → 0 ≤ bilin (B - diagonal (excessRight K u v)) y y) ∧
      chargeOf u a < 0 ∧ chargeOf v b < 0 ∧ M ≤ chargeOf u a * chargeOf v b := by
  set A₀ : Matrix ι₁ ι₁ ℝ := A - diagonal fun i => ∑ j, K i j
  set B₀ : Matrix ι₂ ι₂ ℝ := B - diagonal fun j => ∑ i, K i j
  -- solve `A₀ φ₀ = e_{i₀}` and `B₀ ψ₀ = e_{j₀}` by injectivity on finite dimensions
  have hinjA : Function.Injective A₀.mulVecLin := by
    intro x y hxy
    by_contra hne
    have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
    have hpos := hA₀ (x - y) hsub
    have hzero : bilin A₀ (x - y) (x - y) = 0 := by
      rw [← dotProduct_mulVec_eq_bilin, Matrix.mulVec_sub,
        show A₀ *ᵥ x = A₀ *ᵥ y from hxy, sub_self, dotProduct_zero]
    linarith
  have hinjB : Function.Injective B₀.mulVecLin := by
    intro x y hxy
    by_contra hne
    have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
    have hpos := hB₀ (x - y) hsub
    have hzero : bilin B₀ (x - y) (x - y) = 0 := by
      rw [← dotProduct_mulVec_eq_bilin, Matrix.mulVec_sub,
        show B₀ *ᵥ x = B₀ *ᵥ y from hxy, sub_self, dotProduct_zero]
    linarith
  obtain ⟨φ₀, hφ₀⟩ := LinearMap.surjective_of_injective hinjA (Pi.single i₀ 1 : ι₁ → ℝ)
  obtain ⟨ψ₀, hψ₀⟩ := LinearMap.surjective_of_injective hinjB (Pi.single j₀ 1 : ι₂ → ℝ)
  have hA₀φ : ∀ i, ∑ l, A₀ i l * φ₀ l = (Pi.single i₀ 1 : ι₁ → ℝ) i := fun i => by
    have h := congrFun hφ₀ i
    simpa [Matrix.mulVec, dotProduct] using h
  have hB₀ψ : ∀ j, ∑ m, B₀ j m * ψ₀ m = (Pi.single j₀ 1 : ι₂ → ℝ) j := fun j => by
    have h := congrFun hψ₀ j
    simpa [Matrix.mulVec, dotProduct] using h
  have hφ_ne : φ₀ ≠ 0 := by
    intro h0
    have h := hA₀φ i₀
    simp [h0] at h
  have hψ_ne : ψ₀ ≠ 0 := by
    intro h0
    have h := hB₀ψ j₀
    simp [h0] at h
  set cA : ℝ := φ₀ i₀
  set cB : ℝ := ψ₀ j₀
  have hcA : 0 < cA := by
    have h1 := hA₀ φ₀ hφ_ne
    rw [bilin_right_eq_chargeOf hA₀φ φ₀, chargeOf, Finset.sum_eq_single i₀
      (fun i _ hi => by simp [hi]) (fun h => absurd (Finset.mem_univ i₀) h)] at h1
    simpa [cA] using h1
  have hcB : 0 < cB := by
    have h1 := hB₀ ψ₀ hψ_ne
    rw [bilin_right_eq_chargeOf hB₀ψ ψ₀, chargeOf, Finset.sum_eq_single j₀
      (fun j _ hj => by simp [hj]) (fun h => absurd (Finset.mem_univ j₀) h)] at h1
    simpa [cB] using h1
  -- choose `p = max (1/cA) (1/cB) + ε` just above the larger Schur threshold
  set p₀ : ℝ := max (1 / cA) (1 / cB)
  have hp₀ : 0 < p₀ := lt_max_of_lt_left (div_pos one_pos hcA)
  set C : ℝ := 2 * max cA cB
  have hC : 0 < C := mul_pos two_pos (lt_max_of_lt_left hcA)
  set M₁ : ℝ := max M 1
  have hM₁ : 0 < M₁ := lt_max_of_lt_right one_pos
  set ε : ℝ := min p₀ (1 / (C * M₁))
  have hε : 0 < ε := lt_min hp₀ (div_pos one_pos (mul_pos hC hM₁))
  have hε_p₀ : ε ≤ p₀ := min_le_left _ _
  have hε_M : ε * (C * M₁) ≤ 1 := by
    have hle : ε ≤ 1 / (C * M₁) := min_le_right _ _
    exact (le_div_iff₀ (mul_pos hC hM₁)).mp hle
  set p : ℝ := p₀ + ε
  have hp : 0 < p := add_pos hp₀ hε
  have hp_le : p ≤ 2 * p₀ := by dsimp [p]; linarith
  have hpcA_p₀ : 1 ≤ p₀ * cA := by
    have h : 1 / cA ≤ p₀ := le_max_left _ _
    exact (div_le_iff₀ hcA).mp h
  have hpcB_p₀ : 1 ≤ p₀ * cB := by
    have h : 1 / cB ≤ p₀ := le_max_right _ _
    exact (div_le_iff₀ hcB).mp h
  have hpcA : 1 < p * cA := by
    dsimp [p]
    nlinarith [mul_pos hε hcA]
  have hpcB : 1 < p * cB := by
    dsimp [p]
    nlinarith [mul_pos hε hcB]
  -- define the spike charges and Sherman–Morrison solutions
  set u : ι₁ → ℝ := Pi.single i₀ (-p)
  set v : ι₂ → ℝ := Pi.single j₀ 1
  set a : ι₁ → ℝ := fun l => (-p / (1 - p * cA)) * φ₀ l
  set b : ι₂ → ℝ := fun m => (1 / (1 - p * cB)) * ψ₀ m
  have hexL : excessLeft K u v = fun i => (∑ j, K i j) + Pi.single (M := fun _ => ℝ) i₀ p i := by
    funext i
    simp only [excessLeft, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hvsum : ∑ j, v j = 1 := by simp [v]
    rw [hvsum, mul_one]
    by_cases hi : i = i₀
    · subst hi
      simp [u]
    · simp [u, hi]
  have hexR : excessRight K u v = fun j => (∑ i, K i j) + Pi.single (M := fun _ => ℝ) j₀ p j := by
    funext j
    simp only [excessRight, Finset.sum_sub_distrib, ← Finset.sum_mul]
    have husum : ∑ i, u i = -p := by simp [u]
    rw [husum]
    by_cases hj : j = j₀
    · subst hj
      simp [v]
    · simp [v, hj]
  have hAlow_eq :
      A - diagonal (excessLeft K u v) = A₀ - diagonal (Pi.single (M := fun _ => ℝ) i₀ p) := by
    ext i l
    rw [hexL]
    by_cases hil : i = l
    · subst hil
      simp [A₀]
      ring
    · simp [A₀, Matrix.diagonal_apply_ne _ hil]
  have hBlow_eq :
      B - diagonal (excessRight K u v) = B₀ - diagonal (Pi.single (M := fun _ => ℝ) j₀ p) := by
    ext j m
    rw [hexR]
    by_cases hjm : j = m
    · subst hjm
      simp [B₀]
      ring
    · simp [B₀, Matrix.diagonal_apply_ne _ hjm]
  refine ⟨u, a, v, b, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- admissibility: `u_i v_j ≤ 0 ≤ K_ij`
    intro i j
    refine le_trans ?_ (hK0 i j)
    by_cases hi : i = i₀
    · subst hi
      by_cases hj : j = j₀
      · subst hj
        simp [u, v, hp.le]
      · simp [v, hj]
    · simp [u, hi]
  · -- `A_low a = u`
    intro i
    rw [hAlow_eq]
    have hne : 1 - p * cA ≠ 0 := by linarith
    have hdiag : ∑ l, diagonal (Pi.single (M := fun _ => ℝ) i₀ p) i l * φ₀ l =
        Pi.single (M := fun _ => ℝ) i₀ (p * cA) i := by
      rw [Finset.sum_eq_single i (fun l _ hli => by
        rw [Matrix.diagonal_apply_ne _ (Ne.symm hli), zero_mul])
        (fun h => absurd (Finset.mem_univ i) h), Matrix.diagonal_apply_eq]
      by_cases hi : i = i₀
      · subst hi
        simp [cA]
      · simp [hi]
    have hlin : ∑ l, (A₀ - diagonal (Pi.single (M := fun _ => ℝ) i₀ p)) i l * a l =
        (-p / (1 - p * cA)) *
          (∑ l, A₀ i l * φ₀ l - ∑ l, diagonal (Pi.single (M := fun _ => ℝ) i₀ p) i l * φ₀ l) := by
      simp only [a, Matrix.sub_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hlin, hA₀φ i, hdiag]
    by_cases hi : i = i₀
    · subst hi
      simp only [Pi.single_eq_same, u]
      field_simp
    · simp [hi, u]
  · -- `B_low b = v`
    intro j
    rw [hBlow_eq]
    have hne : 1 - p * cB ≠ 0 := by linarith
    have hdiag : ∑ m, diagonal (Pi.single (M := fun _ => ℝ) j₀ p) j m * ψ₀ m =
        Pi.single (M := fun _ => ℝ) j₀ (p * cB) j := by
      rw [Finset.sum_eq_single j (fun m _ hmj => by
        rw [Matrix.diagonal_apply_ne _ (Ne.symm hmj), zero_mul])
        (fun h => absurd (Finset.mem_univ j) h), Matrix.diagonal_apply_eq]
      by_cases hj : j = j₀
      · subst hj
        simp [cB]
      · simp [hj]
    have hlin : ∑ m, (B₀ - diagonal (Pi.single (M := fun _ => ℝ) j₀ p)) j m * b m =
        (1 / (1 - p * cB)) *
          (∑ m, B₀ j m * ψ₀ m - ∑ m, diagonal (Pi.single (M := fun _ => ℝ) j₀ p) j m * ψ₀ m) := by
      simp only [b, Matrix.sub_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [hlin, hB₀ψ j, hdiag]
    by_cases hj : j = j₀
    · subst hj
      simp only [Pi.single_eq_same, v]
      field_simp
    · simp [hj, v]
  · -- nonnegativity on `ker u`
    intro x hx
    rw [hAlow_eq, bilin_sub_diagonal]
    have hxi₀ : x i₀ = 0 := by
      have h1 : chargeOf u x = -p * x i₀ := by
        rw [chargeOf, Finset.sum_eq_single i₀
          (fun i _ hi => by simp [u, hi]) (fun h => absurd (Finset.mem_univ i₀) h)]
        simp [u]
      rw [h1] at hx
      exact (mul_eq_zero.mp hx).resolve_left (neg_ne_zero.mpr hp.ne')
    have hsingle : ∑ i, Pi.single (M := fun _ => ℝ) i₀ p i * x i ^ 2 = 0 := by
      rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hi])
        (fun h => absurd (Finset.mem_univ i₀) h), Pi.single_eq_same, hxi₀]
      ring
    rw [hsingle, sub_zero]
    by_cases hx0 : x = 0
    · subst hx0
      simp [bilin]
    · exact (hA₀ x hx0).le
  · -- nonnegativity on `ker v`
    intro y hy
    rw [hBlow_eq, bilin_sub_diagonal]
    have hyj₀ : y j₀ = 0 := by
      have h1 : chargeOf v y = y j₀ := by
        rw [chargeOf, Finset.sum_eq_single j₀
          (fun j _ hj => by simp [v, hj]) (fun h => absurd (Finset.mem_univ j₀) h)]
        simp [v]
      linarith
    have hsingle : ∑ j, Pi.single (M := fun _ => ℝ) j₀ p j * y j ^ 2 = 0 := by
      rw [Finset.sum_eq_single j₀ (fun j _ hj => by simp [hj])
        (fun h => absurd (Finset.mem_univ j₀) h), Pi.single_eq_same, hyj₀]
      ring
    rw [hsingle, sub_zero]
    by_cases hy0 : y = 0
    · subst hy0
      simp [bilin]
    · exact (hB₀ y hy0).le
  · -- `chargeOf u a < 0`
    have hua : chargeOf u a = -(p ^ 2 * cA / (p * cA - 1)) := by
      rw [chargeOf, Finset.sum_eq_single i₀
        (fun i _ hi => by simp [u, hi]) (fun h => absurd (Finset.mem_univ i₀) h)]
      simp only [u, a, Pi.single_eq_same]
      change -p * (-p / (1 - p * cA) * cA) = -(p ^ 2 * cA / (p * cA - 1))
      have hne1 : 1 - p * cA ≠ 0 := by linarith
      have hne2 : p * cA - 1 ≠ 0 := by linarith
      field_simp
      ring
    rw [hua, neg_lt_zero]
    exact div_pos (by positivity) (by linarith)
  · -- `chargeOf v b < 0`
    have hvb : chargeOf v b = -(cB / (p * cB - 1)) := by
      rw [chargeOf, Finset.sum_eq_single j₀
        (fun j _ hj => by simp [v, hj]) (fun h => absurd (Finset.mem_univ j₀) h)]
      simp only [v, b, Pi.single_eq_same]
      change 1 * (1 / (1 - p * cB) * cB) = -(cB / (p * cB - 1))
      have hne1 : 1 - p * cB ≠ 0 := by linarith
      have hne2 : p * cB - 1 ≠ 0 := by linarith
      field_simp
      ring
    rw [hvb, neg_lt_zero]
    exact div_pos hcB (by linarith)
  · -- `M ≤ chargeOf u a * chargeOf v b`
    have hprod : chargeOf u a * chargeOf v b =
        (p * cA) * (p * cB) / ((p * cA - 1) * (p * cB - 1)) := by
      have hua : chargeOf u a = -(p ^ 2 * cA / (p * cA - 1)) := by
        rw [chargeOf, Finset.sum_eq_single i₀
          (fun i _ hi => by simp [u, hi]) (fun h => absurd (Finset.mem_univ i₀) h)]
        simp only [u, a, Pi.single_eq_same]
        change -p * (-p / (1 - p * cA) * cA) = -(p ^ 2 * cA / (p * cA - 1))
        have hne1 : 1 - p * cA ≠ 0 := by linarith
        have hne2 : p * cA - 1 ≠ 0 := by linarith
        field_simp
        ring
      have hvb : chargeOf v b = -(cB / (p * cB - 1)) := by
        rw [chargeOf, Finset.sum_eq_single j₀
          (fun j _ hj => by simp [v, hj]) (fun h => absurd (Finset.mem_univ j₀) h)]
        simp only [v, b, Pi.single_eq_same]
        change 1 * (1 / (1 - p * cB) * cB) = -(cB / (p * cB - 1))
        have hne1 : 1 - p * cB ≠ 0 := by linarith
        have hne2 : p * cB - 1 ≠ 0 := by linarith
        field_simp
        ring
      rw [hua, hvb, neg_mul_neg, div_mul_div_comm]
      congr 1
      ring
    rw [hprod]
    have hden_pos : 0 < (p * cA - 1) * (p * cB - 1) :=
      mul_pos (by linarith) (by linarith)
    have hden_le : (p * cA - 1) * (p * cB - 1) ≤ ε * C := by
      rcases max_choice (1 / cA) (1 / cB) with hp_eq | hp_eq
      · have hp₀cA : p₀ * cA = 1 := by
          dsimp only [p₀]
          rw [hp_eq]
          exact one_div_mul_cancel hcA.ne'
        have hf1 : p * cA - 1 = ε * cA := by
          dsimp [p]
          linarith
        have hf2 : p * cB - 1 ≤ 2 * p₀ * cB := by
          have := mul_le_mul_of_nonneg_right hp_le hcB.le
          linarith
        calc (p * cA - 1) * (p * cB - 1)
            = (ε * cA) * (p * cB - 1) := by rw [hf1]
          _ ≤ (ε * cA) * (2 * p₀ * cB) :=
              mul_le_mul_of_nonneg_left hf2 (by positivity)
          _ = 2 * ε * (p₀ * cA) * cB := by ring
          _ = ε * (2 * cB) := by rw [hp₀cA]; ring
          _ ≤ ε * C := mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (le_max_right _ _) zero_le_two) hε.le
      · have hp₀cB : p₀ * cB = 1 := by
          dsimp only [p₀]
          rw [hp_eq]
          exact one_div_mul_cancel hcB.ne'
        have hf2 : p * cB - 1 = ε * cB := by
          dsimp [p]
          linarith
        have hf1 : p * cA - 1 ≤ 2 * p₀ * cA := by
          have := mul_le_mul_of_nonneg_right hp_le hcA.le
          linarith
        calc (p * cA - 1) * (p * cB - 1)
            = (p * cA - 1) * (ε * cB) := by rw [hf2]
          _ ≤ (2 * p₀ * cA) * (ε * cB) :=
              mul_le_mul_of_nonneg_right hf1 (by positivity)
          _ = 2 * ε * (p₀ * cB) * cA := by ring
          _ = ε * (2 * cA) := by rw [hp₀cB]; ring
          _ ≤ ε * C := mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (le_max_left _ _) zero_le_two) hε.le
    have hnum_ge : 1 ≤ (p * cA) * (p * cB) := by nlinarith
    have hM_le : M ≤ M₁ := le_max_left _ _
    refine le_trans hM_le ((le_div_iff₀ hden_pos).mpr ?_)
    calc M₁ * ((p * cA - 1) * (p * cB - 1))
        ≤ M₁ * (ε * C) := mul_le_mul_of_nonneg_left hden_le hM₁.le
      _ = ε * (C * M₁) := by ring
      _ ≤ 1 := hε_M
      _ ≤ (p * cA) * (p * cB) := hnum_ge

/-- **Unbounded susceptibility product on adjacent narrow windows (`16 (J₁ + J₂) ≤ R`).** For any
two nonempty adjacent narrow windows and any `M : ℝ`, there exist admissible charge vectors `u`, `v`
whose lowered halves are nonnegative on `ker u` and `ker v`, with `u · a < 0`, `v · b < 0`, and
`M ≤ (u · a)(v · b)`. -/
theorem exists_narrow_admissible_susceptibility_mul_ge {Q R J₁ J₂ : ℕ}
    (hJ : 16 * (J₁ + 1 + (J₂ + 1)) ≤ R) (M : ℝ) :
    ∃ (u a : Fin (J₁ + 1) → ℝ) (v b : Fin (J₂ + 1) → ℝ),
      (∀ i j, u i * v j ≤ blockWeight Q (R + i) (R + (J₁ + 1) + j)) ∧
      (∀ i, ∑ l,
        (neutralWindow Q R (J₁ + 1) -
          diagonal (excessLeft
            (fun (i : Fin (J₁ + 1)) (j : Fin (J₂ + 1)) =>
              blockWeight Q (R + i) (R + (J₁ + 1) + j)) u v)) i l * a l = u i) ∧
      (∀ j, ∑ m,
        (neutralWindow Q (R + (J₁ + 1)) (J₂ + 1) -
          diagonal (excessRight
            (fun (i : Fin (J₁ + 1)) (j : Fin (J₂ + 1)) =>
              blockWeight Q (R + i) (R + (J₁ + 1) + j)) u v)) j m * b m = v j) ∧
      (∀ x, chargeOf u x = 0 →
        0 ≤ bilin (neutralWindow Q R (J₁ + 1) -
          diagonal (excessLeft
            (fun (i : Fin (J₁ + 1)) (j : Fin (J₂ + 1)) =>
              blockWeight Q (R + i) (R + (J₁ + 1) + j)) u v)) x x) ∧
      (∀ y, chargeOf v y = 0 →
        0 ≤ bilin (neutralWindow Q (R + (J₁ + 1)) (J₂ + 1) -
          diagonal (excessRight
            (fun (i : Fin (J₁ + 1)) (j : Fin (J₂ + 1)) =>
              blockWeight Q (R + i) (R + (J₁ + 1) + j)) u v)) y y) ∧
      chargeOf u a < 0 ∧ chargeOf v b < 0 ∧ M ≤ chargeOf u a * chargeOf v b := by
  refine exists_admissible_susceptibility_mul_ge_of_posDef 0 0
    (fun i j => (blockWeight_pos (by have := i.2; omega) Q).le) ?_ ?_ M
  · intro x hx
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
    have hpos : 0 < ∑ i, x i ^ 2 :=
      lt_of_lt_of_le (sq_pos_of_ne_zero hi₀)
        (Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ i₀))
    exact lt_of_lt_of_le hpos (sum_sq_le_bilin_lowered_left_of_narrow hJ x)
  · intro y hy
    obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hy
    have hpos : 0 < ∑ j, y j ^ 2 :=
      lt_of_lt_of_le (sq_pos_of_ne_zero hj₀)
        (Finset.single_le_sum (fun j _ => sq_nonneg (y j)) (Finset.mem_univ j₀))
    exact lt_of_lt_of_le hpos (sum_sq_le_bilin_lowered_right_of_narrow hJ y)

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
