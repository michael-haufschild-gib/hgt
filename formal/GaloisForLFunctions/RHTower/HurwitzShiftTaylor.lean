import GaloisForLFunctions.RHTower.HurwitzZetaSmallShift

/-!
# All-order Taylor expansion of the shifted power and of the shift-difference series

The shifted power `b ↦ (x+b)^{-w}` has a Taylor expansion to every order at `b = 0`, with an
explicit remainder that is summable over `x = n+1` for every `Re w > 0`.  Summing gives the
all-order small-shift expansion of the shift-difference series, whose coefficients are the
forward zeta values `ζ(w+j)`.
-/

open Complex Filter Topology

namespace RHTower

/-- The `j`-th Taylor coefficient of `b ↦ (x+b)^{-w}`, stripped of the power of `x`. -/
noncomputable def shiftTaylorCoeff (w : ℂ) (j : ℕ) : ℂ :=
  (∏ i ∈ Finset.range j, (-w - i)) / (Nat.factorial j : ℂ)

theorem shiftTaylorCoeff_zero (w : ℂ) : shiftTaylorCoeff w 0 = 1 := by
  rw [shiftTaylorCoeff]
  simp

/-- The descent identity linking consecutive orders at consecutive exponents. -/
theorem shiftTaylorCoeff_succ_mul (w : ℂ) (j : ℕ) :
    shiftTaylorCoeff w (j + 1) * ((j : ℂ) + 1) = -w * shiftTaylorCoeff (w + 1) j := by
  have hfacne : ((Nat.factorial j : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hne : ((j : ℂ) + 1) ≠ 0 := by
    intro hcon
    have hre := congrArg Complex.re hcon
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hprod : (∏ i ∈ Finset.range (j + 1), (-w - (i : ℂ)))
      = -w * ∏ i ∈ Finset.range j, (-(w + 1) - (i : ℂ)) := by
    rw [Finset.prod_range_succ' (fun i : ℕ => (-w - (i : ℂ))) j]
    simp only [Nat.cast_zero, sub_zero]
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    push_cast
    ring
  have hfac : ((Nat.factorial (j + 1) : ℕ) : ℂ) = ((j : ℂ) + 1) * (Nat.factorial j : ℂ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [shiftTaylorCoeff, shiftTaylorCoeff, hprod, hfac]
  field_simp

/-- The `K`-th order Taylor remainder of the shifted power. -/
noncomputable def shiftRemainder (w : ℂ) (K : ℕ) (x y : ℝ) : ℂ :=
  ((x + y : ℝ) : ℂ) ^ (-w)
    - ∑ j ∈ Finset.range (K + 1),
        shiftTaylorCoeff w j * ((y : ℝ) : ℂ) ^ j * ((x : ℝ) : ℂ) ^ (-w - j)

theorem shiftRemainder_zero (w : ℂ) (K : ℕ) (x : ℝ) :
    shiftRemainder w K x 0 = 0 := by
  rw [shiftRemainder]
  have hsum : ∑ j ∈ Finset.range (K + 1),
      shiftTaylorCoeff w j * (((0 : ℝ) : ℝ) : ℂ) ^ j * ((x : ℝ) : ℂ) ^ (-w - j)
      = ((x : ℝ) : ℂ) ^ (-w) := by
    rw [Finset.sum_eq_single 0]
    · rw [shiftTaylorCoeff_zero]
      push_cast
      ring
    · intro j _ hj
      rw [Complex.ofReal_zero, zero_pow hj]
      ring
    · intro hcon
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos K)) hcon
  rw [hsum, add_zero]
  ring

/-- The derivative of the Taylor polynomial part, in descent form. -/
theorem hasDerivAt_shiftPoly (w : ℂ) (K : ℕ) {x : ℝ} (hx : 0 < x) (y : ℝ) :
    HasDerivAt
      (fun z : ℝ => ∑ j ∈ Finset.range (K + 2),
        shiftTaylorCoeff w j * ((z : ℝ) : ℂ) ^ j * ((x : ℝ) : ℂ) ^ (-w - j))
      (-w * ∑ j ∈ Finset.range (K + 1),
        shiftTaylorCoeff (w + 1) j * ((y : ℝ) : ℂ) ^ j * ((x : ℝ) : ℂ) ^ (-(w + 1) - j)) y := by
  have hbase : HasDerivAt (fun z : ℝ => ((z : ℝ) : ℂ)) 1 y := by
    simpa using ((hasDerivAt_id y).ofReal_comp)
  have hterm : ∀ j ∈ Finset.range (K + 2),
      HasDerivAt (fun z : ℝ => shiftTaylorCoeff w j * ((z : ℝ) : ℂ) ^ j * ((x : ℝ) : ℂ) ^ (-w - j))
        ((shiftTaylorCoeff w j * (j : ℂ) * ((y : ℝ) : ℂ) ^ (j - 1))
          * ((x : ℝ) : ℂ) ^ (-w - j)) y := by
    intro j _
    have hp : HasDerivAt (fun z : ℝ => ((z : ℝ) : ℂ) ^ j)
        ((j : ℂ) * ((y : ℝ) : ℂ) ^ (j - 1) * 1) y := hbase.pow j
    simpa [mul_comm, mul_assoc, mul_left_comm] using
      ((hp.const_mul (shiftTaylorCoeff w j)).mul_const (((x : ℝ) : ℂ) ^ (-w - j)))
  have hsum := HasDerivAt.sum hterm
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hval : (∑ j ∈ Finset.range (K + 2),
      (shiftTaylorCoeff w j * (j : ℂ) * ((y : ℝ) : ℂ) ^ (j - 1)) * ((x : ℝ) : ℂ) ^ (-w - j))
      = -w * ∑ j ∈ Finset.range (K + 1),
        shiftTaylorCoeff (w + 1) j * ((y : ℝ) : ℂ) ^ j * ((x : ℝ) : ℂ) ^ (-(w + 1) - j) := by
    rw [Finset.sum_range_succ' (fun j =>
      (shiftTaylorCoeff w j * (j : ℂ) * ((y : ℝ) : ℂ) ^ (j - 1)) * ((x : ℝ) : ℂ) ^ (-w - j))
      (K + 1)]
    simp only [Nat.cast_zero, mul_zero, zero_mul]
    rw [add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hstep := shiftTaylorCoeff_succ_mul w j
    have hpow : ((x : ℝ) : ℂ) ^ (-w - ((j : ℂ) + 1)) = ((x : ℝ) : ℂ) ^ (-(w + 1) - j) := by
      congr 1
      ring
    rw [Nat.add_sub_cancel]
    push_cast
    rw [hpow]
    calc shiftTaylorCoeff w (j + 1) * ((j : ℂ) + 1) * ((y : ℝ) : ℂ) ^ j
          * ((x : ℝ) : ℂ) ^ (-(w + 1) - j)
        = (shiftTaylorCoeff w (j + 1) * ((j : ℂ) + 1)) * (((y : ℝ) : ℂ) ^ j
            * ((x : ℝ) : ℂ) ^ (-(w + 1) - j)) := by ring
      _ = (-w * shiftTaylorCoeff (w + 1) j) * (((y : ℝ) : ℂ) ^ j
            * ((x : ℝ) : ℂ) ^ (-(w + 1) - j)) := by rw [hstep]
      _ = -w * (shiftTaylorCoeff (w + 1) j * ((y : ℝ) : ℂ) ^ j
            * ((x : ℝ) : ℂ) ^ (-(w + 1) - j)) := by ring
  have hfun : (fun z : ℝ => ∑ j ∈ Finset.range (K + 2),
        shiftTaylorCoeff w j * ((z : ℝ) : ℂ) ^ j * ((x : ℝ) : ℂ) ^ (-w - j))
      = ∑ j ∈ Finset.range (K + 2),
        (fun z : ℝ => shiftTaylorCoeff w j * ((z : ℝ) : ℂ) ^ j * ((x : ℝ) : ℂ) ^ (-w - j)) := by
    funext z
    simp
  rw [← hval, hfun]
  exact hsum

/-- The constant in the all-order remainder bound. -/
noncomputable def shiftTaylorConst (w : ℂ) : ℕ → ℝ
  | 0 => ‖w‖ * 2 ^ (w.re + 1)
  | (K + 1) => ‖w‖ * shiftTaylorConst (w + 1) K

theorem shiftTaylorConst_nonneg (w : ℂ) (K : ℕ) : 0 ≤ shiftTaylorConst w K := by
  induction K generalizing w with
  | zero =>
      rw [shiftTaylorConst]
      positivity
  | succ K ih =>
      rw [shiftTaylorConst]
      exact mul_nonneg (norm_nonneg _) (ih (w + 1))

/-- **The all-order Taylor bound for the shifted power.** -/
theorem norm_shiftRemainder_le : ∀ (K : ℕ) {w : ℂ}, 0 < w.re → ∀ {x b : ℝ}, 1 ≤ x → |b| ≤ 1 / 2 →
    ‖shiftRemainder w K x b‖
      ≤ shiftTaylorConst w K * x ^ (-w.re - (K : ℝ) - 1) * |b| ^ (K + 1) := by
  intro K
  induction K with
  | zero =>
      intro w hw x b hx hb
      have h := norm_cpow_shift_sub_le hx hb hw
      have hrem : shiftRemainder w 0 x b
          = ((x + b : ℝ) : ℂ) ^ (-w) - ((x : ℝ) : ℂ) ^ (-w) := by
        rw [shiftRemainder]
        simp [shiftTaylorCoeff_zero]
      rw [hrem, shiftTaylorConst]
      simpa using h
  | succ K ih =>
      intro w hw x b hx hb
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
      have hw1 : 0 < (w + 1).re := by simp; linarith
      have hwne : (-w) ≠ 0 := by
        intro hcon
        have : w = 0 := by linear_combination -hcon
        rw [this] at hw
        simp at hw
      have habs : ∀ y ∈ Set.uIcc (0 : ℝ) b, |y| ≤ |b| := by
        intro y hy
        rcases abs_cases b with ⟨hbv, hbs⟩ | ⟨hbv, hbs⟩
        · have hmem : y ∈ Set.Icc (0 : ℝ) b := by
            rwa [Set.uIcc_of_le (by linarith)] at hy
          rw [abs_of_nonneg hmem.1, hbv]
          exact hmem.2
        · have hmem : y ∈ Set.Icc b (0 : ℝ) := by
            rwa [Set.uIcc_of_ge (by linarith)] at hy
          rw [abs_of_nonpos hmem.2, hbv]
          linarith [hmem.1]
      have hxy : ∀ y ∈ Set.uIcc (0 : ℝ) b, (0 : ℝ) < x + y := by
        intro y hy
        have := habs y hy
        have h2 : |y| ≤ 1 / 2 := le_trans this hb
        have := abs_le.mp h2
        linarith
      have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) b,
          HasDerivWithinAt (fun z : ℝ => shiftRemainder w (K + 1) x z)
            (-w * shiftRemainder (w + 1) K x y) (Set.uIcc (0 : ℝ) b) y := by
        intro y hy
        have hpos := hxy y hy
        have hcpow : HasDerivAt (fun z : ℝ => ((x + z : ℝ) : ℂ) ^ (-w))
            ((-w) * ((x + y : ℝ) : ℂ) ^ (-w - 1)) y := by
          have hb0 := hasDerivAt_ofReal_cpow_const (x := x + y) hpos.ne' hwne
          exact HasDerivAt.comp_const_add x y hb0
        have hpoly := hasDerivAt_shiftPoly w K hx0 y
        have hsub := hcpow.sub hpoly
        have hval : ((-w) * ((x + y : ℝ) : ℂ) ^ (-w - 1)
            - -w * ∑ j ∈ Finset.range (K + 1),
              shiftTaylorCoeff (w + 1) j * ((y : ℝ) : ℂ) ^ j * ((x : ℝ) : ℂ) ^ (-(w + 1) - j))
            = -w * shiftRemainder (w + 1) K x y := by
          rw [shiftRemainder, show (-w - 1 : ℂ) = -(w + 1) by ring]
          ring
        rw [hval] at hsub
        exact hsub.hasDerivWithinAt
      have hbnd : ∀ y ∈ Set.uIcc (0 : ℝ) b,
          ‖-w * shiftRemainder (w + 1) K x y‖
            ≤ ‖w‖ * (shiftTaylorConst (w + 1) K * x ^ (-(w + 1).re - (K : ℝ) - 1)
              * |b| ^ (K + 1)) := by
        intro y hy
        have hy2 : |y| ≤ 1 / 2 := le_trans (habs y hy) hb
        have hin := ih hw1 hx hy2
        rw [norm_mul, norm_neg]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine hin.trans ?_
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg y) (habs y hy) _) ?_
        exact mul_nonneg (shiftTaylorConst_nonneg _ _) (Real.rpow_nonneg hx0.le _)
      have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun z : ℝ => shiftRemainder w (K + 1) x z)
        (f' := fun z : ℝ => -w * shiftRemainder (w + 1) K x z)
        hderiv hbnd (convex_uIcc _ _) Set.left_mem_uIcc Set.right_mem_uIcc
      rw [shiftRemainder_zero w (K + 1) x, sub_zero] at hmain
      have hnorm : ‖(b : ℝ) - (0 : ℝ)‖ = |b| := by
        rw [sub_zero, Real.norm_eq_abs]
      rw [hnorm] at hmain
      refine hmain.trans ?_
      have hre : (-(w + 1).re - (K : ℝ) - 1) = (-w.re - ((K : ℝ) + 1) - 1) := by
        simp
        ring
      rw [hre, shiftTaylorConst]
      push_cast
      exact le_of_eq (by ring)

/-! ## The all-order small-shift expansion of the shift-difference series -/

theorem hasSum_riemannZeta_shift_add {w : ℂ} (hw : 0 < w.re) (j : ℕ) :
    HasSum (fun n : ℕ => ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-w - ((j : ℂ) + 1)))
      (riemannZeta (w + ((j : ℂ) + 1))) := by
  have hw1 : 1 < (w + ((j : ℂ) + 1)).re := by
    simp
    linarith [Nat.cast_nonneg (α := ℝ) j]
  refine (hasSum_riemannZeta_shift hw1).congr_fun fun n => ?_
  rw [show (-w - ((j : ℂ) + 1)) = -(w + ((j : ℂ) + 1)) by ring, Complex.cpow_neg, one_div]
  congr 2
  push_cast
  ring

theorem summable_shiftMajorant_add {w : ℂ} (hw : 0 < w.re) (K : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-w.re - (K : ℝ) - 1)) := by
  have hwK : 0 < (w + (K : ℂ)).re := by
    simp
    linarith [Nat.cast_nonneg (α := ℝ) K]
  refine (summable_shiftMajorant hwK).congr fun n => ?_
  congr 1
  simp
  ring

/-- The `K`-th order Taylor polynomial of the shift-difference series, with the forward zeta
values as coefficients. -/
noncomputable def shiftZetaTaylor (b : ℝ) (w : ℂ) (K : ℕ) : ℂ :=
  ∑ j ∈ Finset.range K, shiftTaylorCoeff w (j + 1) * ((b : ℝ) : ℂ) ^ (j + 1)
    * riemannZeta (w + ((j : ℂ) + 1))

/-- The termwise reindexing of the Taylor remainder. -/
theorem shiftRemainder_eq (w : ℂ) (K : ℕ) (b : ℝ) (n : ℕ) :
    shiftRemainder w K ((n : ℝ) + 1) b
      = shiftDiffTerm b w n
        - ∑ j ∈ Finset.range K, shiftTaylorCoeff w (j + 1) * ((b : ℝ) : ℂ) ^ (j + 1)
            * ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-w - ((j : ℂ) + 1)) := by
  rw [shiftRemainder, shiftDiffTerm,
    Finset.sum_range_succ' (fun j : ℕ =>
      shiftTaylorCoeff w j * ((b : ℝ) : ℂ) ^ j * ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-w - (j : ℂ))) K]
  simp only [shiftTaylorCoeff_zero, pow_zero, Nat.cast_zero, sub_zero, one_mul]
  have hcong : ∀ j ∈ Finset.range K,
      shiftTaylorCoeff w (j + 1) * ((b : ℝ) : ℂ) ^ (j + 1)
        * ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-w - ((j + 1 : ℕ) : ℂ))
      = shiftTaylorCoeff w (j + 1) * ((b : ℝ) : ℂ) ^ (j + 1)
        * ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-w - ((j : ℂ) + 1)) := by
    intro j _
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl hcong]
  ring

/-- **The all-order small-shift expansion of the shift-difference series.** -/
theorem norm_shiftDiffSeries_sub_taylor_le (K : ℕ) {w : ℂ} (hw : 0 < w.re) {b : ℝ}
    (hb : |b| ≤ 1 / 2) :
    ‖shiftDiffSeries b w - shiftZetaTaylor b w K‖
      ≤ (shiftTaylorConst w K * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-w.re - (K : ℝ) - 1)))
        * |b| ^ (K + 1) := by
  set C : ℝ := shiftTaylorConst w K with hC
  have hCnn : 0 ≤ C := shiftTaylorConst_nonneg w K
  set F : ℕ → ℂ := fun n => shiftDiffTerm b w n
      - ∑ j ∈ Finset.range K, shiftTaylorCoeff w (j + 1) * ((b : ℝ) : ℂ) ^ (j + 1)
          * ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-w - ((j : ℂ) + 1)) with hF
  have hterm : ∀ n : ℕ, ‖F n‖ ≤ (C * |b| ^ (K + 1)) * (((n : ℝ) + 1) ^ (-w.re - (K : ℝ) - 1)) := by
    intro n
    have hx : (1 : ℝ) ≤ (n : ℝ) + 1 := by simp [Nat.cast_nonneg]
    have h := norm_shiftRemainder_le K hw hx hb
    simp only [hF]
    rw [← shiftRemainder_eq w K b n]
    refine h.trans (le_of_eq ?_)
    ring
  have hsummaj : Summable
      (fun n : ℕ => (C * |b| ^ (K + 1)) * (((n : ℝ) + 1) ^ (-w.re - (K : ℝ) - 1))) :=
    (summable_shiftMajorant_add hw K).mul_left _
  have hsum1 : Summable (fun n : ℕ => shiftDiffTerm b w n) := summable_shiftDiffTerm hb hw
  have hHS : HasSum (fun n : ℕ =>
      ∑ j ∈ Finset.range K, shiftTaylorCoeff w (j + 1) * ((b : ℝ) : ℂ) ^ (j + 1)
        * ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-w - ((j : ℂ) + 1))) (shiftZetaTaylor b w K) :=
    hasSum_sum fun j _ => (hasSum_riemannZeta_shift_add hw j).mul_left _
  have hsum2 : Summable (fun n : ℕ =>
      ∑ j ∈ Finset.range K, shiftTaylorCoeff w (j + 1) * ((b : ℝ) : ℂ) ^ (j + 1)
        * ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-w - ((j : ℂ) + 1))) := hHS.summable
  have hval : shiftDiffSeries b w - shiftZetaTaylor b w K = ∑' n : ℕ, F n := by
    simp only [hF]
    rw [hsum1.tsum_sub hsum2, shiftDiffSeries, hHS.tsum_eq]
  rw [hval]
  have hnormsum : Summable (fun n : ℕ => ‖F n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsummaj
  refine (norm_tsum_le_tsum_norm hnormsum).trans ?_
  refine (Summable.tsum_le_tsum hterm hnormsum hsummaj).trans ?_
  rw [tsum_mul_left]
  exact le_of_eq (by ring)

end RHTower
