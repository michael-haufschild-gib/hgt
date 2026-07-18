import GaloisForLFunctions.HTGeometry.ComplexChristoffelDarboux
import GaloisForLFunctions.HTGeometry.SecondKindMomentPolynomials

/-!
# The second-kind family at complex points

Complex evaluations of the second-kind polynomials, their recurrence, and the mixed
Christoffel--Darboux identity over `ℂ`.  These are the complex counterparts of the real identities
in `SecondKindMomentPolynomials`, and they are what the comparison of the orthogonal polynomials at
two *complex* points requires.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- Complex evaluation of the second-kind polynomials. -/
noncomputable def secondKindC (s : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  Polynomial.aeval z (secondKind s n)

@[simp] theorem secondKindC_zero (s : ℕ → ℝ) (z : ℂ) : secondKindC s 0 z = 0 := by
  simp [secondKindC]

@[simp] theorem secondKindC_one (s : ℕ → ℝ) (z : ℂ) : secondKindC s 1 z = 1 := by
  simp [secondKindC]

theorem secondKindC_succ_succ (s : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    secondKindC s (n + 2) z =
      (z - ((recurDiag s n : ℝ) : ℂ)) * secondKindC s (n + 1) z
        - ((recurOff s n : ℝ) : ℂ) * secondKindC s n z := by
  have hev := congrArg (Polynomial.aeval z) (secondKind_succ_succ s n)
  simpa [secondKindC] using hev

theorem monicOrthoC_succ_succ (h : PositiveMomentForm s) (n : ℕ) (z : ℂ) :
    monicOrthoC s (n + 2) z =
      (z - ((recurDiag s n : ℝ) : ℂ)) * monicOrthoC s (n + 1) z
        - ((recurOff s n : ℝ) : ℂ) * monicOrthoC s n z := by
  have hev := congrArg (Polynomial.aeval z) (monicOrtho_succ_succ h n)
  simpa [monicOrthoC] using hev

/-- **Mixed Christoffel--Darboux over `ℂ`.**  As over `ℝ`, the `n = 0` boundary term leaves the
constant `1 / h₀`. -/
theorem mixedChristoffelDarbouxC (h : PositiveMomentForm s) (n : ℕ) (z w : ℂ) :
    (z - w) * ∑ k ∈ Finset.range (n + 1),
        monicOrthoC s k z * secondKindC s k w /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)
      = (monicOrthoC s (n + 1) z * secondKindC s n w -
          monicOrthoC s n z * secondKindC s (n + 1) w) /
          ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ)
        + 1 / ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) := by
  induction n with
  | zero =>
      have h0 : ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast h.self_ne_zero (monicOrtho_ne_zero s 0)
      have hz0 : monicOrthoC s 0 z = 1 := by simp [monicOrthoC]
      simp only [Nat.zero_add, Finset.sum_range_one, secondKindC_zero, secondKindC_one, hz0,
        mul_zero, zero_div, mul_one, mul_zero, zero_sub]
      field_simp
      ring
  | succ n ih =>
      have hn : ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast h.self_ne_zero (monicOrtho_ne_zero s n)
      have hn1 : ((momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast h.self_ne_zero (monicOrtho_ne_zero s (n + 1))
      have hQ := monicOrthoC_succ_succ h n z
      have hR := secondKindC_succ_succ s n w
      simp only [recurOff] at hQ hR
      push_cast at hQ hR
      rw [Finset.sum_range_succ, mul_add, ih, hQ, hR]
      field_simp [hn, hn1]
      ring

/-! ## Duhamel comparison at complex points -/

theorem monicOrthoC_wronskian (h : PositiveMomentForm s) (n : ℕ) (z : ℂ) :
    monicOrthoC s (n + 1) z * secondKindC s n z - monicOrthoC s n z * secondKindC s (n + 1) z
      = -((momentInner s (monicOrtho s n) (monicOrtho s n) /
          momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) := by
  have hev := congrArg (Polynomial.aeval z) (momentWronskian_eq h n)
  simpa [momentWronskian, monicOrthoC, secondKindC] using hev

/-- **Duhamel comparison at complex points.**  The complex counterpart of `monicOrtho_duhamel`. -/
theorem monicOrthoC_duhamel (h : PositiveMomentForm s) (n : ℕ) (z w : ℂ) :
    monicOrthoC s n w
      = monicOrthoC s n z
        - (w - z) * ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) *
          (monicOrthoC s n z *
              (∑ j ∈ Finset.range (n + 1), monicOrthoC s j w * secondKindC s j z /
                ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))
            - secondKindC s n z *
              (∑ j ∈ Finset.range (n + 1), monicOrthoC s j w * monicOrthoC s j z /
                ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))) := by
  have h0 : ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast h.self_ne_zero (monicOrtho_ne_zero s 0)
  have hn : ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast h.self_ne_zero (monicOrtho_ne_zero s n)
  have hCD := christoffelDarbouxC h n w z
  have hMix := mixedChristoffelDarbouxC h n w z
  have hWz := monicOrthoC_wronskian h n z
  have hnum : monicOrthoC s n z *
        (monicOrthoC s (n + 1) w * secondKindC s n z -
          monicOrthoC s n w * secondKindC s (n + 1) z)
      - secondKindC s n z *
        (monicOrthoC s (n + 1) w * monicOrthoC s n z -
          monicOrthoC s n w * monicOrthoC s (n + 1) z)
      = -(monicOrthoC s n w * ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ)) := by
    have hb : monicOrthoC s n z *
          (monicOrthoC s (n + 1) w * secondKindC s n z -
            monicOrthoC s n w * secondKindC s (n + 1) z)
        - secondKindC s n z *
          (monicOrthoC s (n + 1) w * monicOrthoC s n z -
            monicOrthoC s n w * monicOrthoC s (n + 1) z)
        = monicOrthoC s n w *
          (monicOrthoC s (n + 1) z * secondKindC s n z -
            monicOrthoC s n z * secondKindC s (n + 1) z) := by
      ring
    rw [hb, hWz]
    push_cast
    ring
  have key : (w - z) * ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) *
      (monicOrthoC s n z *
          (∑ j ∈ Finset.range (n + 1), monicOrthoC s j w * secondKindC s j z /
            ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))
        - secondKindC s n z *
          (∑ j ∈ Finset.range (n + 1), monicOrthoC s j w * monicOrthoC s j z /
            ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ)))
      = monicOrthoC s n z - monicOrthoC s n w := by
    calc (w - z) * ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) *
          (monicOrthoC s n z *
              (∑ j ∈ Finset.range (n + 1), monicOrthoC s j w * secondKindC s j z /
                ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))
            - secondKindC s n z *
              (∑ j ∈ Finset.range (n + 1), monicOrthoC s j w * monicOrthoC s j z /
                ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ)))
        = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) *
            (monicOrthoC s n z *
                ((w - z) * ∑ j ∈ Finset.range (n + 1), monicOrthoC s j w * secondKindC s j z /
                  ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))
              - secondKindC s n z *
                ((w - z) * ∑ j ∈ Finset.range (n + 1), monicOrthoC s j w * monicOrthoC s j z /
                  ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))) := by
          ring
      _ = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) *
            (monicOrthoC s n z *
                ((monicOrthoC s (n + 1) w * secondKindC s n z -
                    monicOrthoC s n w * secondKindC s (n + 1) z) /
                  ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ)
                  + 1 / ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ))
              - secondKindC s n z *
                ((monicOrthoC s (n + 1) w * monicOrthoC s n z -
                    monicOrthoC s n w * monicOrthoC s (n + 1) z) /
                  ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ))) := by
          rw [hMix, hCD]
      _ = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) *
            (monicOrthoC s n z *
                (monicOrthoC s (n + 1) w * secondKindC s n z -
                  monicOrthoC s n w * secondKindC s (n + 1) z)
              - secondKindC s n z *
                (monicOrthoC s (n + 1) w * monicOrthoC s n z -
                  monicOrthoC s n w * monicOrthoC s (n + 1) z)) /
              ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ)
            + monicOrthoC s n z := by
          field_simp [h0, hn]
          ring
      _ = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) *
            (-(monicOrthoC s n w * ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) /
              ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ))) /
              ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ)
            + monicOrthoC s n z := by
          rw [hnum]
      _ = monicOrthoC s n z - monicOrthoC s n w := by
          field_simp [h0, hn]
          ring
  linear_combination key

/-! ## Weighted Cauchy--Schwarz

The Duhamel sums are inner products against the weights `1/hⱼ`.  Bounding them by the kernel sums is
the first analytic step of the convergence transfer. -/

theorem weightedSum_sq_le (h : PositiveMomentForm s) (n : ℕ) (f g : ℕ → ℂ) :
    (∑ j ∈ Finset.range (n + 1),
        ‖f j‖ * ‖g j‖ / momentInner s (monicOrtho s j) (monicOrtho s j)) ^ 2
      ≤ (∑ j ∈ Finset.range (n + 1), ‖f j‖ ^ 2 /
            momentInner s (monicOrtho s j) (monicOrtho s j)) *
        (∑ j ∈ Finset.range (n + 1), ‖g j‖ ^ 2 /
            momentInner s (monicOrtho s j) (monicOrtho s j)) := by
  have hpos : ∀ j, 0 < momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => monicOrtho_inner_self_pos h j
  have hmul : ∀ j, Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j)) *
      Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))
      = momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => Real.mul_self_sqrt (hpos j).le
  have hcs : (∑ j ∈ Finset.range (n + 1),
        (‖f j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))) *
          (‖g j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j)))) ^ 2
      ≤ (∑ j ∈ Finset.range (n + 1),
            (‖f j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))) ^ 2) *
        (∑ j ∈ Finset.range (n + 1),
            (‖g j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))) ^ 2) := by
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have e1 : ∑ j ∈ Finset.range (n + 1),
      (‖f j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))) *
        (‖g j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j)))
      = ∑ j ∈ Finset.range (n + 1),
        ‖f j‖ * ‖g j‖ / momentInner s (monicOrtho s j) (monicOrtho s j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_mul_div_comm, hmul j]
  have e2 : ∑ j ∈ Finset.range (n + 1),
      (‖f j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))) ^ 2
      = ∑ j ∈ Finset.range (n + 1),
        ‖f j‖ ^ 2 / momentInner s (monicOrtho s j) (monicOrtho s j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_pow, Real.sq_sqrt (hpos j).le]
  have e3 : ∑ j ∈ Finset.range (n + 1),
      (‖g j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))) ^ 2
      = ∑ j ∈ Finset.range (n + 1),
        ‖g j‖ ^ 2 / momentInner s (monicOrtho s j) (monicOrtho s j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_pow, Real.sq_sqrt (hpos j).le]
  rw [e1, e2, e3] at hcs
  exact hcs

/-- The root of a weighted kernel sum, the natural norm for the Duhamel estimates. -/
noncomputable def kernelRoot (s : ℕ → ℝ) (p : ℕ → ℂ) (n : ℕ) : ℝ :=
  Real.sqrt (∑ j ∈ Finset.range (n + 1),
    ‖p j‖ ^ 2 / momentInner s (monicOrtho s j) (monicOrtho s j))

theorem kernelRoot_nonneg (s : ℕ → ℝ) (p : ℕ → ℂ) (n : ℕ) : 0 ≤ kernelRoot s p n :=
  Real.sqrt_nonneg _

/-- **Cauchy--Schwarz in usable form.**  A weighted Duhamel sum is bounded by the product of the
two kernel roots. -/
theorem norm_weightedSum_le (h : PositiveMomentForm s) (n : ℕ) (f g : ℕ → ℂ) :
    ‖∑ j ∈ Finset.range (n + 1), f j * g j /
        ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ)‖
      ≤ kernelRoot s f n * kernelRoot s g n := by
  have hpos : ∀ j, 0 < momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => monicOrtho_inner_self_pos h j
  have hterm : ∀ j, ‖f j * g j /
      ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ)‖
      = ‖f j‖ * ‖g j‖ / momentInner s (monicOrtho s j) (monicOrtho s j) := by
    intro j
    rw [norm_div, norm_mul]
    congr 1
    simp [abs_of_pos (hpos j)]
  have hstep1 : ‖∑ j ∈ Finset.range (n + 1), f j * g j /
      ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ)‖
      ≤ ∑ j ∈ Finset.range (n + 1),
        ‖f j‖ * ‖g j‖ / momentInner s (monicOrtho s j) (monicOrtho s j) := by
    refine le_trans (norm_sum_le _ _) ?_
    exact le_of_eq (Finset.sum_congr rfl fun j _ => hterm j)
  have hnn : 0 ≤ ∑ j ∈ Finset.range (n + 1),
      ‖f j‖ * ‖g j‖ / momentInner s (monicOrtho s j) (monicOrtho s j) :=
    Finset.sum_nonneg fun j _ =>
      div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hpos j).le
  have hA : 0 ≤ ∑ j ∈ Finset.range (n + 1),
      ‖f j‖ ^ 2 / momentInner s (monicOrtho s j) (monicOrtho s j) :=
    Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hpos j).le
  refine le_trans hstep1 ?_
  rw [kernelRoot, kernelRoot, ← Real.sqrt_mul hA]
  have hsq := Real.sqrt_le_sqrt (weightedSum_sq_le h n f g)
  rwa [Real.sqrt_sq hnn] at hsq

end HTGeometry
