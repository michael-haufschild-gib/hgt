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
        ‖f j‖ * ‖g j‖ / momentInner s (monicOrtho s j) (monicOrtho s j)) ^ (2 : ℕ)
      ≤ (∑ j ∈ Finset.range (n + 1), ‖f j‖ ^ (2 : ℕ) /
            momentInner s (monicOrtho s j) (monicOrtho s j)) *
        (∑ j ∈ Finset.range (n + 1), ‖g j‖ ^ (2 : ℕ) /
            momentInner s (monicOrtho s j) (monicOrtho s j)) := by
  have hpos : ∀ j, 0 < momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => monicOrtho_inner_self_pos h j
  have hmul : ∀ j, Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j)) *
      Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))
      = momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => Real.mul_self_sqrt (hpos j).le
  have hcs : (∑ j ∈ Finset.range (n + 1),
        (‖f j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))) *
          (‖g j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j)))) ^ (2 : ℕ)
      ≤ (∑ j ∈ Finset.range (n + 1),
            (‖f j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))) ^ (2 : ℕ)) *
        (∑ j ∈ Finset.range (n + 1),
            (‖g j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))) ^ (2 : ℕ)) := by
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have e1 : ∑ j ∈ Finset.range (n + 1),
      (‖f j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))) *
        (‖g j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j)))
      = ∑ j ∈ Finset.range (n + 1),
        ‖f j‖ * ‖g j‖ / momentInner s (monicOrtho s j) (monicOrtho s j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_mul_div_comm, hmul j]
  have e2 : ∑ j ∈ Finset.range (n + 1),
      (‖f j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))) ^ (2 : ℕ)
      = ∑ j ∈ Finset.range (n + 1),
        ‖f j‖ ^ (2 : ℕ) / momentInner s (monicOrtho s j) (monicOrtho s j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_pow, Real.sq_sqrt (hpos j).le]
  have e3 : ∑ j ∈ Finset.range (n + 1),
      (‖g j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))) ^ (2 : ℕ)
      = ∑ j ∈ Finset.range (n + 1),
        ‖g j‖ ^ (2 : ℕ) / momentInner s (monicOrtho s j) (monicOrtho s j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_pow, Real.sq_sqrt (hpos j).le]
  rw [e1, e2, e3] at hcs
  exact hcs

/-- The root of a weighted kernel sum, the natural norm for the Duhamel estimates. -/
noncomputable def kernelRoot (s : ℕ → ℝ) (p : ℕ → ℂ) (n : ℕ) : ℝ :=
  Real.sqrt (∑ j ∈ Finset.range (n + 1),
    ‖p j‖ ^ (2 : ℕ) / momentInner s (monicOrtho s j) (monicOrtho s j))

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
      ‖f j‖ ^ (2 : ℕ) / momentInner s (monicOrtho s j) (monicOrtho s j) :=
    Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hpos j).le
  refine le_trans hstep1 ?_
  rw [kernelRoot, kernelRoot, ← Real.sqrt_mul hA]
  have hsq := Real.sqrt_le_sqrt (weightedSum_sq_le h n f g)
  rwa [Real.sqrt_sq hnn] at hsq

/-- **The pointwise Duhamel estimate.**  Combining the comparison formula with Cauchy--Schwarz: the
polynomial at `w` is controlled by its value at `z` plus `|w - z|` times the kernel root at `w`. -/
theorem norm_monicOrthoC_duhamel_le (h : PositiveMomentForm s) (n : ℕ) (z w : ℂ) :
    ‖monicOrthoC s n w‖
      ≤ ‖monicOrthoC s n z‖
        + ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
          (kernelRoot s (fun j => monicOrthoC s j w) n *
            (‖monicOrthoC s n z‖ * kernelRoot s (fun j => secondKindC s j z) n
              + ‖secondKindC s n z‖ * kernelRoot s (fun j => monicOrthoC s j z) n)) := by
  have h0pos : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    monicOrtho_inner_self_pos h 0
  have hnormAux : ∀ c : ℝ, 0 < c → ‖(c : ℂ)‖ = c := by
    intro c hc
    simp [abs_of_pos hc]
  have hnorm : ‖((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ)‖
      = momentInner s (monicOrtho s 0) (monicOrtho s 0) := hnormAux _ h0pos
  have hT := norm_weightedSum_le h n (fun j => monicOrthoC s j w) (fun j => secondKindC s j z)
  have hS := norm_weightedSum_le h n (fun j => monicOrthoC s j w) (fun j => monicOrthoC s j z)
  have hd := monicOrthoC_duhamel h n z w
  have hbr : ‖monicOrthoC s n z *
        (∑ j ∈ Finset.range (n + 1), monicOrthoC s j w * secondKindC s j z /
          ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))
      - secondKindC s n z *
        (∑ j ∈ Finset.range (n + 1), monicOrthoC s j w * monicOrthoC s j z /
          ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))‖
      ≤ ‖monicOrthoC s n z‖ *
          (kernelRoot s (fun j => monicOrthoC s j w) n *
            kernelRoot s (fun j => secondKindC s j z) n)
        + ‖secondKindC s n z‖ *
          (kernelRoot s (fun j => monicOrthoC s j w) n *
            kernelRoot s (fun j => monicOrthoC s j z) n) := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_mul, norm_mul]
    gcongr
  calc ‖monicOrthoC s n w‖
      = ‖monicOrthoC s n z
          - (w - z) * ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) *
            (monicOrthoC s n z *
                (∑ j ∈ Finset.range (n + 1), monicOrthoC s j w * secondKindC s j z /
                  ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))
              - secondKindC s n z *
                (∑ j ∈ Finset.range (n + 1), monicOrthoC s j w * monicOrthoC s j z /
                  ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ)))‖ := by
        rw [← hd]
    _ ≤ ‖monicOrthoC s n z‖
        + ‖(w - z) * ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) *
            (monicOrthoC s n z *
                (∑ j ∈ Finset.range (n + 1), monicOrthoC s j w * secondKindC s j z /
                  ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))
              - secondKindC s n z *
                (∑ j ∈ Finset.range (n + 1), monicOrthoC s j w * monicOrthoC s j z /
                  ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ)))‖ :=
        norm_sub_le _ _
    _ = ‖monicOrthoC s n z‖
        + ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
          ‖monicOrthoC s n z *
              (∑ j ∈ Finset.range (n + 1), monicOrthoC s j w * secondKindC s j z /
                ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))
            - secondKindC s n z *
              (∑ j ∈ Finset.range (n + 1), monicOrthoC s j w * monicOrthoC s j z /
                ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))‖ := by
        rw [norm_mul, norm_mul, hnorm]
    _ ≤ ‖monicOrthoC s n z‖
        + ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
          (‖monicOrthoC s n z‖ *
              (kernelRoot s (fun j => monicOrthoC s j w) n *
                kernelRoot s (fun j => secondKindC s j z) n)
            + ‖secondKindC s n z‖ *
              (kernelRoot s (fun j => monicOrthoC s j w) n *
                kernelRoot s (fun j => monicOrthoC s j z) n)) := by
        gcongr
    _ = ‖monicOrthoC s n z‖
        + ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
          (kernelRoot s (fun j => monicOrthoC s j w) n *
            (‖monicOrthoC s n z‖ * kernelRoot s (fun j => secondKindC s j z) n
              + ‖secondKindC s n z‖ * kernelRoot s (fun j => monicOrthoC s j z) n)) := by
        ring

/-! ## Kernel root infrastructure

The absorption step uses monotonicity of the kernel roots in `n` and the identification of their
squares with the kernel sums of the summability criterion. -/

theorem kernelRoot_sq (h : PositiveMomentForm s) (p : ℕ → ℂ) (n : ℕ) :
    kernelRoot s p n ^ (2 : ℕ) = ∑ j ∈ Finset.range (n + 1),
      ‖p j‖ ^ (2 : ℕ) / momentInner s (monicOrtho s j) (monicOrtho s j) := by
  rw [kernelRoot, Real.sq_sqrt]
  exact Finset.sum_nonneg fun j _ =>
    div_nonneg (sq_nonneg _) (monicOrtho_inner_self_pos h j).le

theorem kernelRoot_mono (h : PositiveMomentForm s) (p : ℕ → ℂ) {m n : ℕ} (hmn : m ≤ n) :
    kernelRoot s p m ≤ kernelRoot s p n := by
  refine Real.sqrt_le_sqrt ?_
  have hsub : Finset.range (m + 1) ⊆ Finset.range (n + 1) := by
    intro x hx
    exact Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.succ_le_succ hmn))
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro j _ _
  exact div_nonneg (sq_nonneg _) (monicOrtho_inner_self_pos h j).le

/-- The square of the kernel root is the kernel sum of the summability criterion. -/
theorem kernelRoot_sq_eq_normSq_sum (h : PositiveMomentForm s) (p : ℕ → ℂ) (n : ℕ) :
    kernelRoot s p n ^ (2 : ℕ) = ∑ j ∈ Finset.range (n + 1),
      Complex.normSq (p j) / momentInner s (monicOrtho s j) (monicOrtho s j) := by
  rw [kernelRoot_sq h]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact Complex.sq_norm (p j)

/-- **A uniform kernel-root bound gives summability.**  This is the form the absorption argument
produces, connected to the criterion of `ComplexChristoffelDarboux`. -/
theorem summable_of_kernelRoot_le (h : PositiveMomentForm s) (z : ℂ) {C : ℝ}
    (hC : ∀ n, kernelRoot s (fun j => monicOrthoC s j z) n ≤ C) :
    Summable (fun k => Complex.normSq (monicOrthoC s k z) /
      momentInner s (monicOrtho s k) (monicOrtho s k)) := by
  refine summable_kernel_of_sum_range_le (C := C ^ (2 : ℕ)) h z ?_
  intro n
  match n with
  | 0 =>
      have hC0 : 0 ≤ C := le_trans (kernelRoot_nonneg s _ 0) (hC 0)
      simpa using sq_nonneg C
  | (m + 1) =>
      rw [← kernelRoot_sq_eq_normSq_sum h]
      have hnn := kernelRoot_nonneg s (fun j => monicOrthoC s j z) m
      have := hC m
      nlinarith [hnn, this]

/-! ## Toward absorption

The pointwise estimate with all kernel roots frozen at the top level `N`, and its squared form.
Freezing is legitimate by `kernelRoot_mono`, and the squared form is what survives division by `hₙ`
and summation. -/

theorem norm_monicOrthoC_duhamel_le_of_le (h : PositiveMomentForm s) {N n : ℕ} (hn : n ≤ N)
    (z w : ℂ) :
    ‖monicOrthoC s n w‖
      ≤ ‖monicOrthoC s n z‖
        + ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
          (kernelRoot s (fun j => monicOrthoC s j w) N *
            (‖monicOrthoC s n z‖ * kernelRoot s (fun j => secondKindC s j z) N
              + ‖secondKindC s n z‖ * kernelRoot s (fun j => monicOrthoC s j z) N)) := by
  refine le_trans (norm_monicOrthoC_duhamel_le h n z w) ?_
  have h0 : 0 ≤ momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    (monicOrtho_inner_self_pos h 0).le
  gcongr <;>
    first
      | exact kernelRoot_mono h _ hn
      | exact kernelRoot_nonneg _ _ _
      | exact mul_nonneg (norm_nonneg _) (kernelRoot_nonneg _ _ _)
      | exact add_nonneg (mul_nonneg (norm_nonneg _) (kernelRoot_nonneg _ _ _))
          (mul_nonneg (norm_nonneg _) (kernelRoot_nonneg _ _ _))

/-- The squared pointwise estimate: the form that survives division by `hₙ` and summation. -/
theorem normSq_monicOrthoC_duhamel_le (h : PositiveMomentForm s) {N n : ℕ} (hn : n ≤ N)
    (z w : ℂ) :
    ‖monicOrthoC s n w‖ ^ (2 : ℕ)
      ≤ 2 * ‖monicOrthoC s n z‖ ^ (2 : ℕ)
        + 4 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
          kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) *
          (‖monicOrthoC s n z‖ ^ (2 : ℕ) * kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ)
            + ‖secondKindC s n z‖ ^ (2 : ℕ) * kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ)) := by
  have h0 : 0 ≤ momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    (monicOrtho_inner_self_pos h 0).le
  have hA := norm_monicOrthoC_duhamel_le_of_le h hn z w
  have hK : 0 ≤ kernelRoot s (fun j => monicOrthoC s j w) N := kernelRoot_nonneg _ _ _
  have hP : 0 ≤ kernelRoot s (fun j => secondKindC s j z) N := kernelRoot_nonneg _ _ _
  have hS : 0 ≤ kernelRoot s (fun j => monicOrthoC s j z) N := kernelRoot_nonneg _ _ _
  have ha : (0 : ℝ) ≤ ‖monicOrthoC s n z‖ := norm_nonneg _
  have hb : (0 : ℝ) ≤ ‖secondKindC s n z‖ := norm_nonneg _
  have he : (0 : ℝ) ≤ ‖monicOrthoC s n w‖ := norm_nonneg _
  have hD : (0 : ℝ) ≤ ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    mul_nonneg (norm_nonneg _) h0
  set a := ‖monicOrthoC s n z‖
  set b := ‖secondKindC s n z‖
  set e := ‖monicOrthoC s n w‖
  set D := ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)
  set K := kernelRoot s (fun j => monicOrthoC s j w) N
  set P := kernelRoot s (fun j => secondKindC s j z) N
  set S := kernelRoot s (fun j => monicOrthoC s j z) N
  have hX : 0 ≤ D * (K * (a * P + b * S)) := by positivity
  have h2 : e ^ (2 : ℕ) ≤ (a + D * (K * (a * P + b * S))) ^ (2 : ℕ) := by
    have hsum : 0 ≤ a + D * (K * (a * P + b * S)) := by positivity
    nlinarith [hA, he, hsum]
  have h3 : (a + D * (K * (a * P + b * S))) ^ (2 : ℕ)
      ≤ 2 * a ^ (2 : ℕ) + 2 * (D * (K * (a * P + b * S))) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (a - D * (K * (a * P + b * S)))]
  have h5 : (a * P + b * S) ^ (2 : ℕ) ≤ 2 * (a ^ (2 : ℕ) * P ^ (2 : ℕ) + b ^ (2 : ℕ) * S ^ (2 : ℕ)) := by
    nlinarith [sq_nonneg (a * P - b * S)]
  have h6 : (D * (K * (a * P + b * S))) ^ (2 : ℕ) = D ^ (2 : ℕ) * K ^ (2 : ℕ) * (a * P + b * S) ^ (2 : ℕ) := by ring
  nlinarith [h2, h3, h5, h6, sq_nonneg D, sq_nonneg K, mul_nonneg (sq_nonneg D) (sq_nonneg K)]

/-- **The absorption inequality.**  Dividing the squared pointwise estimate by `hₙ` and summing over
`n ≤ N` gives a self-referential bound on the kernel root at `w`. -/
theorem kernelRoot_sq_le_absorption (h : PositiveMomentForm s) (N : ℕ) (z w : ℂ) :
    kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ)
      ≤ 2 * kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ)
        + 8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
          kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) *
          kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) *
          kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ) := by
  have hpos : ∀ j, 0 < momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => monicOrtho_inner_self_pos h j
  have hterm : ∀ n ∈ Finset.range (N + 1),
      ‖monicOrthoC s n w‖ ^ (2 : ℕ) / momentInner s (monicOrtho s n) (monicOrtho s n)
        ≤ 2 * (‖monicOrthoC s n z‖ ^ (2 : ℕ) /
              momentInner s (monicOrtho s n) (monicOrtho s n))
          + 4 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
              kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) *
              kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ) *
              (‖monicOrthoC s n z‖ ^ (2 : ℕ) /
                momentInner s (monicOrtho s n) (monicOrtho s n))
          + 4 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
              kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) *
              kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) *
              (‖secondKindC s n z‖ ^ (2 : ℕ) /
                momentInner s (monicOrtho s n) (monicOrtho s n)) := by
    intro n hn'
    have hn : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn')
    have hsq := normSq_monicOrthoC_duhamel_le h hn z w
    have hdiv : ‖monicOrthoC s n w‖ ^ (2 : ℕ) /
          momentInner s (monicOrtho s n) (monicOrtho s n)
        ≤ (2 * ‖monicOrthoC s n z‖ ^ (2 : ℕ)
            + 4 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
              kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) *
              (‖monicOrthoC s n z‖ ^ (2 : ℕ) *
                  kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ)
                + ‖secondKindC s n z‖ ^ (2 : ℕ) *
                  kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ))) /
          momentInner s (monicOrtho s n) (monicOrtho s n) := by
      gcongr
      exact (hpos n).le
    refine le_trans hdiv (le_of_eq ?_)
    field_simp
    ring
  calc kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ)
      = ∑ n ∈ Finset.range (N + 1),
          ‖monicOrthoC s n w‖ ^ (2 : ℕ) / momentInner s (monicOrtho s n) (monicOrtho s n) :=
        kernelRoot_sq h _ _
    _ ≤ ∑ n ∈ Finset.range (N + 1),
          (2 * (‖monicOrthoC s n z‖ ^ (2 : ℕ) /
                momentInner s (monicOrtho s n) (monicOrtho s n))
            + 4 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
                kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) *
                kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ) *
                (‖monicOrthoC s n z‖ ^ (2 : ℕ) /
                  momentInner s (monicOrtho s n) (monicOrtho s n))
            + 4 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
                kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) *
                kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) *
                (‖secondKindC s n z‖ ^ (2 : ℕ) /
                  momentInner s (monicOrtho s n) (monicOrtho s n))) :=
        Finset.sum_le_sum hterm
    _ = 2 * kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ)
        + 8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
          kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) *
          kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) *
          kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.mul_sum, ← kernelRoot_sq h, ← kernelRoot_sq h]
        ring

/-! ## Absorption: transfer of convergence

If both kernel roots at `z` are bounded and `w` is close enough to `z`, the self-referential term in
`kernelRoot_sq_le_absorption` absorbs into the left side, giving a bound at `w` uniform in `N` --
hence summability at `w`. -/

theorem summable_kernel_transfer (h : PositiveMomentForm s) (z w : ℂ) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j z) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j z) N ≤ P)
    (hsmall : 8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ)
      ≤ 1 / 2) :
    Summable (fun k => Complex.normSq (monicOrthoC s k w) /
      momentInner s (monicOrtho s k) (monicOrtho s k)) := by
  have hSnn : 0 ≤ S := le_trans (kernelRoot_nonneg s _ 0) (hS 0)
  have hPnn : 0 ≤ P := le_trans (kernelRoot_nonneg s _ 0) (hP 0)
  have hDnn : 0 ≤ ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    mul_nonneg (norm_nonneg _) (monicOrtho_inner_self_pos h 0).le
  refine summable_of_kernelRoot_le h w (C := 2 * S) ?_
  intro N
  have habs := kernelRoot_sq_le_absorption h N z w
  have hKnn := kernelRoot_nonneg s (fun j => monicOrthoC s j w) N
  have hSNnn := kernelRoot_nonneg s (fun j => monicOrthoC s j z) N
  have hPNnn := kernelRoot_nonneg s (fun j => secondKindC s j z) N
  have h1 : kernelRoot s (fun j => monicOrthoC s j z) N ≤ S := hS N
  have h2 : kernelRoot s (fun j => secondKindC s j z) N ≤ P := hP N
  have hSq1 : kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) ≤ S ^ (2 : ℕ) := by
    gcongr
  have hSq2 : kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ) ≤ P ^ (2 : ℕ) := by
    gcongr
  have hbig : 8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
      kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) *
      kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) *
      kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ)
      ≤ 1 / 2 * kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) := by
    have hmid : 8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
        kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) *
        kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) *
        kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ)
        ≤ 8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
          kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ) := by
      gcongr
    nlinarith [hmid, hsmall, sq_nonneg (kernelRoot s (fun j => monicOrthoC s j w) N)]
  have hK2 : kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) ≤ (2 * S) ^ (2 : ℕ) := by
    nlinarith [habs, hbig, hSq1]
  have hfin := Real.sqrt_le_sqrt hK2
  rwa [Real.sqrt_sq hKnn, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * S)] at hfin

/-- The explicit transfer radius: `1 / (4 h₀ S P)`. -/
noncomputable def transferRadius (s : ℕ → ℝ) (S P : ℝ) : ℝ :=
  1 / (4 * momentInner s (monicOrtho s 0) (monicOrtho s 0) * S * P)

theorem transferRadius_pos (h : PositiveMomentForm s) {S P : ℝ} (hS : 0 < S) (hP : 0 < P) :
    0 < transferRadius s S P := by
  have h0 : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    monicOrtho_inner_self_pos h 0
  rw [transferRadius]
  positivity

/-- **Transfer on an explicit disc.**  Convergence of the kernel at `z` propagates to every `w`
within `transferRadius s S P` of `z`. -/
theorem summable_kernel_transfer_of_dist (h : PositiveMomentForm s) (z w : ℂ) {S P : ℝ}
    (hSpos : 0 < S) (hPpos : 0 < P)
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j z) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j z) N ≤ P)
    (hdist : ‖w - z‖ ≤ transferRadius s S P) :
    Summable (fun k => Complex.normSq (monicOrthoC s k w) /
      momentInner s (monicOrtho s k) (monicOrtho s k)) := by
  have h0 : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    monicOrtho_inner_self_pos h 0
  refine summable_kernel_transfer h z w hS hP ?_
  have hDnn : 0 ≤ ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    mul_nonneg (norm_nonneg _) h0.le
  have hD : ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)
      ≤ 1 / (4 * S * P) := by
    have hmul := mul_le_mul_of_nonneg_right hdist h0.le
    refine le_trans hmul (le_of_eq ?_)
    rw [transferRadius]
    field_simp
    try ring
  have hkey : 8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ)
      ≤ 8 * (1 / (4 * S * P)) ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ) := by
    gcongr
  have hval : 8 * (1 / (4 * S * P)) ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ) = 1 / 2 := by
    field_simp
    try ring
  linarith [hkey, hval]

/-- **Second-kind Christoffel--Darboux over `ℂ`.**  As over `ℝ`, the `n = 0` boundary term vanishes
because `R₀ = 0`, so no constant survives.  This is the third bilinear identity at complex points,
and the one an `R`-side Duhamel comparison requires. -/
theorem secondKindChristoffelDarbouxC (h : PositiveMomentForm s) (n : ℕ) (z w : ℂ) :
    (z - w) * ∑ k ∈ Finset.range (n + 1),
        secondKindC s k z * secondKindC s k w /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)
      = (secondKindC s (n + 1) z * secondKindC s n w -
          secondKindC s n z * secondKindC s (n + 1) w) /
        ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn : ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast h.self_ne_zero (monicOrtho_ne_zero s n)
      have hn1 : ((momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast h.self_ne_zero (monicOrtho_ne_zero s (n + 1))
      have hRz := secondKindC_succ_succ s n z
      have hRw := secondKindC_succ_succ s n w
      simp only [recurOff] at hRz hRw
      push_cast at hRz hRw
      rw [Finset.sum_range_succ, mul_add, ih, hRz, hRw]
      field_simp [hn, hn1]
      ring

/-- **Duhamel comparison for the second-kind family.**  The same shape as `monicOrthoC_duhamel`:
the `Q`-side identities are replaced by the R/R and R/Q ones, the cross terms cancel identically,
and the constant Wronskian collapses the result. -/
theorem secondKindC_duhamel (h : PositiveMomentForm s) (n : ℕ) (z w : ℂ) :
    secondKindC s n w
      = secondKindC s n z
        - (w - z) * ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) *
          (monicOrthoC s n z *
              (∑ j ∈ Finset.range (n + 1), secondKindC s j w * secondKindC s j z /
                ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))
            - secondKindC s n z *
              (∑ j ∈ Finset.range (n + 1), monicOrthoC s j z * secondKindC s j w /
                ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))) := by
  have h0 : ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast h.self_ne_zero (monicOrtho_ne_zero s 0)
  have hn : ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast h.self_ne_zero (monicOrtho_ne_zero s n)
  have hRR := secondKindChristoffelDarbouxC h n w z
  have hMix := mixedChristoffelDarbouxC h n z w
  have hWz := monicOrthoC_wronskian h n z
  have hnum : monicOrthoC s n z *
        (secondKindC s (n + 1) w * secondKindC s n z -
          secondKindC s n w * secondKindC s (n + 1) z)
      + secondKindC s n z *
        (monicOrthoC s (n + 1) z * secondKindC s n w -
          monicOrthoC s n z * secondKindC s (n + 1) w)
      = -(secondKindC s n w *
          ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ)) := by
    have hb : monicOrthoC s n z *
          (secondKindC s (n + 1) w * secondKindC s n z -
            secondKindC s n w * secondKindC s (n + 1) z)
        + secondKindC s n z *
          (monicOrthoC s (n + 1) z * secondKindC s n w -
            monicOrthoC s n z * secondKindC s (n + 1) w)
        = secondKindC s n w *
          (monicOrthoC s (n + 1) z * secondKindC s n z -
            monicOrthoC s n z * secondKindC s (n + 1) z) := by
      ring
    rw [hb, hWz]
    push_cast
    ring
  have key : (w - z) * ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) *
      (monicOrthoC s n z *
          (∑ j ∈ Finset.range (n + 1), secondKindC s j w * secondKindC s j z /
            ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))
        - secondKindC s n z *
          (∑ j ∈ Finset.range (n + 1), monicOrthoC s j z * secondKindC s j w /
            ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ)))
      = secondKindC s n z - secondKindC s n w := by
    calc (w - z) * ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) *
          (monicOrthoC s n z *
              (∑ j ∈ Finset.range (n + 1), secondKindC s j w * secondKindC s j z /
                ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))
            - secondKindC s n z *
              (∑ j ∈ Finset.range (n + 1), monicOrthoC s j z * secondKindC s j w /
                ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ)))
        = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) *
            (monicOrthoC s n z *
                ((w - z) * ∑ j ∈ Finset.range (n + 1), secondKindC s j w * secondKindC s j z /
                  ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))
              + secondKindC s n z *
                ((z - w) * ∑ j ∈ Finset.range (n + 1), monicOrthoC s j z * secondKindC s j w /
                  ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))) := by
          ring
      _ = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) *
            (monicOrthoC s n z *
                ((secondKindC s (n + 1) w * secondKindC s n z -
                    secondKindC s n w * secondKindC s (n + 1) z) /
                  ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ))
              + secondKindC s n z *
                ((monicOrthoC s (n + 1) z * secondKindC s n w -
                    monicOrthoC s n z * secondKindC s (n + 1) w) /
                  ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ)
                  + 1 / ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ))) := by
          rw [hRR, hMix]
      _ = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) *
            (monicOrthoC s n z *
                (secondKindC s (n + 1) w * secondKindC s n z -
                  secondKindC s n w * secondKindC s (n + 1) z)
              + secondKindC s n z *
                (monicOrthoC s (n + 1) z * secondKindC s n w -
                  monicOrthoC s n z * secondKindC s (n + 1) w)) /
              ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ)
            + secondKindC s n z := by
          field_simp [h0, hn]
          ring
      _ = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) *
            (-(secondKindC s n w *
              ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) /
              ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ))) /
              ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ)
            + secondKindC s n z := by
          rw [hnum]
      _ = secondKindC s n z - secondKindC s n w := by
          field_simp [h0, hn]
          ring
  linear_combination key

/-- **The pointwise Duhamel estimate for the second-kind family.**  Mirror of
`norm_monicOrthoC_duhamel_le`, with the second-kind kernel root as the factored quantity. -/
theorem norm_secondKindC_duhamel_le (h : PositiveMomentForm s) (n : ℕ) (z w : ℂ) :
    ‖secondKindC s n w‖
      ≤ ‖secondKindC s n z‖
        + ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
          (kernelRoot s (fun j => secondKindC s j w) n *
            (‖monicOrthoC s n z‖ * kernelRoot s (fun j => secondKindC s j z) n
              + ‖secondKindC s n z‖ * kernelRoot s (fun j => monicOrthoC s j z) n)) := by
  have h0pos : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    monicOrtho_inner_self_pos h 0
  have hnormAux : ∀ c : ℝ, 0 < c → ‖(c : ℂ)‖ = c := by
    intro c hc
    simp [abs_of_pos hc]
  have hnorm : ‖((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ)‖
      = momentInner s (monicOrtho s 0) (monicOrtho s 0) := hnormAux _ h0pos
  have hT := norm_weightedSum_le h n (fun j => secondKindC s j w) (fun j => secondKindC s j z)
  have hS := norm_weightedSum_le h n (fun j => monicOrthoC s j z) (fun j => secondKindC s j w)
  have hd := secondKindC_duhamel h n z w
  have hbr : ‖monicOrthoC s n z *
        (∑ j ∈ Finset.range (n + 1), secondKindC s j w * secondKindC s j z /
          ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))
      - secondKindC s n z *
        (∑ j ∈ Finset.range (n + 1), monicOrthoC s j z * secondKindC s j w /
          ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))‖
      ≤ ‖monicOrthoC s n z‖ *
          (kernelRoot s (fun j => secondKindC s j w) n *
            kernelRoot s (fun j => secondKindC s j z) n)
        + ‖secondKindC s n z‖ *
          (kernelRoot s (fun j => monicOrthoC s j z) n *
            kernelRoot s (fun j => secondKindC s j w) n) := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_mul, norm_mul]
    gcongr
  calc ‖secondKindC s n w‖
      = ‖secondKindC s n z
          - (w - z) * ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) *
            (monicOrthoC s n z *
                (∑ j ∈ Finset.range (n + 1), secondKindC s j w * secondKindC s j z /
                  ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))
              - secondKindC s n z *
                (∑ j ∈ Finset.range (n + 1), monicOrthoC s j z * secondKindC s j w /
                  ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ)))‖ := by
        rw [← hd]
    _ ≤ ‖secondKindC s n z‖
        + ‖(w - z) * ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) *
            (monicOrthoC s n z *
                (∑ j ∈ Finset.range (n + 1), secondKindC s j w * secondKindC s j z /
                  ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))
              - secondKindC s n z *
                (∑ j ∈ Finset.range (n + 1), monicOrthoC s j z * secondKindC s j w /
                  ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ)))‖ :=
        norm_sub_le _ _
    _ = ‖secondKindC s n z‖
        + ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
          ‖monicOrthoC s n z *
              (∑ j ∈ Finset.range (n + 1), secondKindC s j w * secondKindC s j z /
                ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))
            - secondKindC s n z *
              (∑ j ∈ Finset.range (n + 1), monicOrthoC s j z * secondKindC s j w /
                ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))‖ := by
        rw [norm_mul, norm_mul, hnorm]
    _ ≤ ‖secondKindC s n z‖
        + ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
          (‖monicOrthoC s n z‖ *
              (kernelRoot s (fun j => secondKindC s j w) n *
                kernelRoot s (fun j => secondKindC s j z) n)
            + ‖secondKindC s n z‖ *
              (kernelRoot s (fun j => monicOrthoC s j z) n *
                kernelRoot s (fun j => secondKindC s j w) n)) := by
        gcongr
    _ = ‖secondKindC s n z‖
        + ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
          (kernelRoot s (fun j => secondKindC s j w) n *
            (‖monicOrthoC s n z‖ * kernelRoot s (fun j => secondKindC s j z) n
              + ‖secondKindC s n z‖ * kernelRoot s (fun j => monicOrthoC s j z) n)) := by
        ring

/-! ## The second-kind absorption chain

Mirrors of links for the first-kind family.  The bracket is *identical* to the first-kind one, so
the summed inequality has the same shape and the same smallness threshold. -/

theorem norm_secondKindC_duhamel_le_of_le (h : PositiveMomentForm s) {N n : ℕ} (hn : n ≤ N)
    (z w : ℂ) :
    ‖secondKindC s n w‖
      ≤ ‖secondKindC s n z‖
        + ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
          (kernelRoot s (fun j => secondKindC s j w) N *
            (‖monicOrthoC s n z‖ * kernelRoot s (fun j => secondKindC s j z) N
              + ‖secondKindC s n z‖ * kernelRoot s (fun j => monicOrthoC s j z) N)) := by
  refine le_trans (norm_secondKindC_duhamel_le h n z w) ?_
  have h0 : 0 ≤ momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    (monicOrtho_inner_self_pos h 0).le
  gcongr <;>
    first
      | exact kernelRoot_mono h _ hn
      | exact kernelRoot_nonneg _ _ _
      | exact mul_nonneg (norm_nonneg _) (kernelRoot_nonneg _ _ _)
      | exact add_nonneg (mul_nonneg (norm_nonneg _) (kernelRoot_nonneg _ _ _))
          (mul_nonneg (norm_nonneg _) (kernelRoot_nonneg _ _ _))

theorem normSq_secondKindC_duhamel_le (h : PositiveMomentForm s) {N n : ℕ} (hn : n ≤ N)
    (z w : ℂ) :
    ‖secondKindC s n w‖ ^ (2 : ℕ)
      ≤ 2 * ‖secondKindC s n z‖ ^ (2 : ℕ)
        + 4 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
          kernelRoot s (fun j => secondKindC s j w) N ^ (2 : ℕ) *
          (‖monicOrthoC s n z‖ ^ (2 : ℕ) * kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ)
            + ‖secondKindC s n z‖ ^ (2 : ℕ) * kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ)) := by
  have h0 : 0 ≤ momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    (monicOrtho_inner_self_pos h 0).le
  have hA := norm_secondKindC_duhamel_le_of_le h hn z w
  have hKnn := kernelRoot_nonneg s (fun j => secondKindC s j w) N
  have hPnn := kernelRoot_nonneg s (fun j => secondKindC s j z) N
  have hSnn := kernelRoot_nonneg s (fun j => monicOrthoC s j z) N
  have ha : (0 : ℝ) ≤ ‖monicOrthoC s n z‖ := norm_nonneg _
  have hb : (0 : ℝ) ≤ ‖secondKindC s n z‖ := norm_nonneg _
  have he : (0 : ℝ) ≤ ‖secondKindC s n w‖ := norm_nonneg _
  set a := ‖monicOrthoC s n z‖
  set b := ‖secondKindC s n z‖
  set e := ‖secondKindC s n w‖
  set D := ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)
  set K := kernelRoot s (fun j => secondKindC s j w) N
  set P := kernelRoot s (fun j => secondKindC s j z) N
  set S := kernelRoot s (fun j => monicOrthoC s j z) N
  have hDnn : 0 ≤ D := mul_nonneg (norm_nonneg _) h0
  have h2 : e ^ (2 : ℕ) ≤ (b + D * (K * (a * P + b * S))) ^ (2 : ℕ) := by
    have hsum : 0 ≤ b + D * (K * (a * P + b * S)) := by positivity
    nlinarith [hA, he, hsum]
  have h3 : (b + D * (K * (a * P + b * S))) ^ (2 : ℕ)
      ≤ 2 * b ^ (2 : ℕ) + 2 * (D * (K * (a * P + b * S))) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (b - D * (K * (a * P + b * S)))]
  have h5 : (a * P + b * S) ^ (2 : ℕ) ≤ 2 * (a ^ (2 : ℕ) * P ^ (2 : ℕ) + b ^ (2 : ℕ) * S ^ (2 : ℕ)) := by
    nlinarith [sq_nonneg (a * P - b * S)]
  have h6 : (D * (K * (a * P + b * S))) ^ (2 : ℕ) = D ^ (2 : ℕ) * K ^ (2 : ℕ) * (a * P + b * S) ^ (2 : ℕ) := by ring
  nlinarith [h2, h3, h5, h6, sq_nonneg D, sq_nonneg K, mul_nonneg (sq_nonneg D) (sq_nonneg K)]

/-- **The second-kind absorption inequality.**  Same shape as the first-kind one, with the same
coefficient `8 D² κ_Q(z)² κ_R(z)²`, hence the same smallness threshold. -/
theorem kernelRootR_sq_le_absorption (h : PositiveMomentForm s) (N : ℕ) (z w : ℂ) :
    kernelRoot s (fun j => secondKindC s j w) N ^ (2 : ℕ)
      ≤ 2 * kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ)
        + 8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
          kernelRoot s (fun j => secondKindC s j w) N ^ (2 : ℕ) *
          kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) *
          kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ) := by
  have hpos : ∀ j, 0 < momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => monicOrtho_inner_self_pos h j
  have hterm : ∀ n ∈ Finset.range (N + 1),
      ‖secondKindC s n w‖ ^ (2 : ℕ) / momentInner s (monicOrtho s n) (monicOrtho s n)
        ≤ 2 * (‖secondKindC s n z‖ ^ (2 : ℕ) /
              momentInner s (monicOrtho s n) (monicOrtho s n))
          + 4 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
              kernelRoot s (fun j => secondKindC s j w) N ^ (2 : ℕ) *
              kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ) *
              (‖monicOrthoC s n z‖ ^ (2 : ℕ) /
                momentInner s (monicOrtho s n) (monicOrtho s n))
          + 4 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
              kernelRoot s (fun j => secondKindC s j w) N ^ (2 : ℕ) *
              kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) *
              (‖secondKindC s n z‖ ^ (2 : ℕ) /
                momentInner s (monicOrtho s n) (monicOrtho s n)) := by
    intro n hn'
    have hn : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn')
    have hsq := normSq_secondKindC_duhamel_le h hn z w
    have hdiv : ‖secondKindC s n w‖ ^ (2 : ℕ) /
          momentInner s (monicOrtho s n) (monicOrtho s n)
        ≤ (2 * ‖secondKindC s n z‖ ^ (2 : ℕ)
            + 4 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
              kernelRoot s (fun j => secondKindC s j w) N ^ (2 : ℕ) *
              (‖monicOrthoC s n z‖ ^ (2 : ℕ) *
                  kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ)
                + ‖secondKindC s n z‖ ^ (2 : ℕ) *
                  kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ))) /
          momentInner s (monicOrtho s n) (monicOrtho s n) := by
      gcongr
      exact (hpos n).le
    refine le_trans hdiv (le_of_eq ?_)
    field_simp
    ring
  calc kernelRoot s (fun j => secondKindC s j w) N ^ (2 : ℕ)
      = ∑ n ∈ Finset.range (N + 1),
          ‖secondKindC s n w‖ ^ (2 : ℕ) / momentInner s (monicOrtho s n) (monicOrtho s n) :=
        kernelRoot_sq h _ _
    _ ≤ ∑ n ∈ Finset.range (N + 1),
          (2 * (‖secondKindC s n z‖ ^ (2 : ℕ) /
                momentInner s (monicOrtho s n) (monicOrtho s n))
            + 4 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
                kernelRoot s (fun j => secondKindC s j w) N ^ (2 : ℕ) *
                kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ) *
                (‖monicOrthoC s n z‖ ^ (2 : ℕ) /
                  momentInner s (monicOrtho s n) (monicOrtho s n))
            + 4 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
                kernelRoot s (fun j => secondKindC s j w) N ^ (2 : ℕ) *
                kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) *
                (‖secondKindC s n z‖ ^ (2 : ℕ) /
                  momentInner s (monicOrtho s n) (monicOrtho s n))) :=
        Finset.sum_le_sum hterm
    _ = 2 * kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ)
        + 8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
          kernelRoot s (fun j => secondKindC s j w) N ^ (2 : ℕ) *
          kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) *
          kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.mul_sum, ← kernelRoot_sq h, ← kernelRoot_sq h]
        ring

/-! ## Propagated bounds

Both kernel roots at the new centre are bounded by twice the old bounds, under the *same* smallness
condition.  This is the data an iteration over discs consumes: each step doubles the constants. -/

theorem kernelRootQ_le_of_small (h : PositiveMomentForm s) (z w : ℂ) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j z) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j z) N ≤ P)
    (hsmall : 8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ)
      ≤ 1 / 2) (N : ℕ) :
    kernelRoot s (fun j => monicOrthoC s j w) N ≤ 2 * S := by
  have hSnn : 0 ≤ S := le_trans (kernelRoot_nonneg s _ 0) (hS 0)
  have habs := kernelRoot_sq_le_absorption h N z w
  have hKnn := kernelRoot_nonneg s (fun j => monicOrthoC s j w) N
  have hSNnn := kernelRoot_nonneg s (fun j => monicOrthoC s j z) N
  have hPNnn := kernelRoot_nonneg s (fun j => secondKindC s j z) N
  have hSq1 : kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) ≤ S ^ (2 : ℕ) := by
    gcongr
    exact hS N
  have hSq2 : kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ) ≤ P ^ (2 : ℕ) := by
    gcongr
    exact hP N
  have hbig : 8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
      kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) *
      kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) *
      kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ)
      ≤ 1 / 2 * kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) := by
    have hmid : 8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
        kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) *
        kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) *
        kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ)
        ≤ 8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
          kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ) := by
      gcongr
    nlinarith [hmid, hsmall, sq_nonneg (kernelRoot s (fun j => monicOrthoC s j w) N)]
  have hK2 : kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) ≤ (2 * S) ^ (2 : ℕ) := by
    nlinarith [habs, hbig, hSq1]
  have hfin := Real.sqrt_le_sqrt hK2
  rwa [Real.sqrt_sq hKnn, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * S)] at hfin

theorem kernelRootR_le_of_small (h : PositiveMomentForm s) (z w : ℂ) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j z) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j z) N ≤ P)
    (hsmall : 8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ)
      ≤ 1 / 2) (N : ℕ) :
    kernelRoot s (fun j => secondKindC s j w) N ≤ 2 * P := by
  have hPnn : 0 ≤ P := le_trans (kernelRoot_nonneg s _ 0) (hP 0)
  have habs := kernelRootR_sq_le_absorption h N z w
  have hKnn := kernelRoot_nonneg s (fun j => secondKindC s j w) N
  have hSNnn := kernelRoot_nonneg s (fun j => monicOrthoC s j z) N
  have hPNnn := kernelRoot_nonneg s (fun j => secondKindC s j z) N
  have hSq1 : kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) ≤ S ^ (2 : ℕ) := by
    gcongr
    exact hS N
  have hSq2 : kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ) ≤ P ^ (2 : ℕ) := by
    gcongr
    exact hP N
  have hbig : 8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
      kernelRoot s (fun j => secondKindC s j w) N ^ (2 : ℕ) *
      kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) *
      kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ)
      ≤ 1 / 2 * kernelRoot s (fun j => secondKindC s j w) N ^ (2 : ℕ) := by
    have hmid : 8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
        kernelRoot s (fun j => secondKindC s j w) N ^ (2 : ℕ) *
        kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) *
        kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ)
        ≤ 8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
          kernelRoot s (fun j => secondKindC s j w) N ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ) := by
      gcongr
    nlinarith [hmid, hsmall, sq_nonneg (kernelRoot s (fun j => secondKindC s j w) N)]
  have hK2 : kernelRoot s (fun j => secondKindC s j w) N ^ (2 : ℕ) ≤ (2 * P) ^ (2 : ℕ) := by
    nlinarith [habs, hbig, hSq2]
  have hfin := Real.sqrt_le_sqrt hK2
  rwa [Real.sqrt_sq hKnn, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * P)] at hfin

/-- **Both bounds propagate.**  On the transfer disc, the kernel roots at the new centre are
bounded by twice the old bounds -- so the hypotheses of the transfer regenerate at `w`. -/
theorem kernelRoot_bounds_propagate (h : PositiveMomentForm s) (z w : ℂ) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j z) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j z) N ≤ P)
    (hsmall : 8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ)
      ≤ 1 / 2) :
    (∀ N, kernelRoot s (fun j => monicOrthoC s j w) N ≤ 2 * S)
      ∧ (∀ N, kernelRoot s (fun j => secondKindC s j w) N ≤ 2 * P) :=
  ⟨kernelRootQ_le_of_small h z w hS hP hsmall, kernelRootR_le_of_small h z w hS hP hsmall⟩

/-! ## The set of good points is open

Convergence of the kernel with *both* bounds is an open condition: the transfer disc has positive
radius and both bounds regenerate on it.  This is the openness half of the classical
local-to-global argument. -/

theorem transferSmall_of_dist (h : PositiveMomentForm s) (z w : ℂ) {S P : ℝ}
    (hSpos : 0 < S) (hPpos : 0 < P) (hdist : ‖w - z‖ ≤ transferRadius s S P) :
    8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ)
      ≤ 1 / 2 := by
  have h0 : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    monicOrtho_inner_self_pos h 0
  have hDnn : 0 ≤ ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    mul_nonneg (norm_nonneg _) h0.le
  have hD : ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)
      ≤ 1 / (4 * S * P) := by
    have hmul := mul_le_mul_of_nonneg_right hdist h0.le
    refine le_trans hmul (le_of_eq ?_)
    rw [transferRadius]
    field_simp
    try ring
  have hkey : 8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ)
      ≤ 8 * (1 / (4 * S * P)) ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ) := by
    gcongr
  have hval : 8 * (1 / (4 * S * P)) ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ) = 1 / 2 := by
    field_simp
    try ring
  linarith [hkey, hval]

/-- Both kernel roots are bounded at `z`, with strictly positive bounds. -/
def BoundedKernel (s : ℕ → ℝ) (z : ℂ) : Prop :=
  ∃ S P : ℝ, 0 < S ∧ 0 < P ∧
    (∀ N, kernelRoot s (fun j => monicOrthoC s j z) N ≤ S) ∧
    (∀ N, kernelRoot s (fun j => secondKindC s j z) N ≤ P)

/-- At a good point the first-kind kernel is summable: the criterion is met. -/
theorem summable_of_boundedKernel (h : PositiveMomentForm s) {z : ℂ} (hz : BoundedKernel s z) :
    Summable (fun k => Complex.normSq (monicOrthoC s k z) /
      momentInner s (monicOrtho s k) (monicOrtho s k)) := by
  obtain ⟨S, _, _, _, hS, _⟩ := hz
  exact summable_of_kernelRoot_le h z hS

/-- **The good set is open.**  If both kernel roots are bounded at `z`, they are bounded on a whole
disc about `z`, with the bounds merely doubled. -/
theorem isOpen_boundedKernel (h : PositiveMomentForm s) :
    IsOpen {z : ℂ | BoundedKernel s z} := by
  rw [Metric.isOpen_iff]
  rintro z ⟨S, P, hSpos, hPpos, hS, hP⟩
  refine ⟨transferRadius s S P, transferRadius_pos h hSpos hPpos, ?_⟩
  intro w hw
  have hdist : ‖w - z‖ ≤ transferRadius s S P := by
    rw [Metric.mem_ball, Complex.dist_eq] at hw
    exact hw.le
  have hsmall := transferSmall_of_dist h z w hSpos hPpos hdist
  obtain ⟨hQ, hR⟩ := kernelRoot_bounds_propagate h z w hS hP hsmall
  exact ⟨2 * S, 2 * P, by linarith, by linarith, hQ, hR⟩

end HTGeometry
