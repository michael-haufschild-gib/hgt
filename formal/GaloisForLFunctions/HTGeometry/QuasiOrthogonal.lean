import GaloisForLFunctions.HTGeometry.ComplexChristoffelDarboux
import GaloisForLFunctions.HTGeometry.MomentRealRootedness
import GaloisForLFunctions.HTGeometry.ConfluentDarboux

/-!
# Quasi-orthogonal polynomials

`Q_{n+1} + t·Qₙ` is monic of degree `n+1` for every real `t`, and its roots are real and simple.

Both facts come from the reproducing kernel rather than from any argument about interlacing.  For
real-rootedness, the conjugate Christoffel--Darboux identity computes the positive kernel sum as
`Im(Q_{n+1}(z)·conj(Qₙ(z)))/(hₙ·Im z)`; if `Q_{n+1}(z) = −t·Qₙ(z)` with `t` real that numerator is
`−t|Qₙ(z)|²`, whose imaginary part vanishes, forcing the kernel sum to be zero — impossible, since its
`k = 0` term is `1/h₀`.

For simplicity, the two-variable identity at a root `r` collapses to
`(x − r)·Kₙ(x,r)·hₙ = Qₙ(r)·(Q_{n+1}(x) + t·Qₙ(x))`; a double root makes the right side divisible by
`(x − r)²`, and cancelling one factor and evaluating at `r` gives `Kₙ(r,r)·hₙ = 0`, again impossible.
No differentiation is involved.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The quasi-orthogonal polynomial `Q_{n+1} + t·Qₙ`. -/
noncomputable def quasiOrtho (s : ℕ → ℝ) (n : ℕ) (t : ℝ) : Polynomial ℝ :=
  monicOrtho s (n + 1) + C t * monicOrtho s n

theorem quasiOrtho_eval (s : ℕ → ℝ) (n : ℕ) (t x : ℝ) :
    (quasiOrtho s n t).eval x
      = (monicOrtho s (n + 1)).eval x + t * (monicOrtho s n).eval x := by
  rw [quasiOrtho]
  simp

theorem aeval_quasiOrtho (s : ℕ → ℝ) (n : ℕ) (t : ℝ) (z : ℂ) :
    Polynomial.aeval z (quasiOrtho s n t)
      = monicOrthoC s (n + 1) z + (t : ℂ) * monicOrthoC s n z := by
  rw [quasiOrtho, map_add, map_mul, monicOrthoC, monicOrthoC]
  simp

theorem quasiOrtho_aux_degree_lt (s : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    (C t * monicOrtho s n).degree < (monicOrtho s (n + 1)).degree := by
  have h1 : (C t * monicOrtho s n).degree ≤ ((n : ℕ) : WithBot ℕ) := by
    refine le_trans (degree_mul_le _ _) ?_
    rw [monicOrtho_degree]
    calc (C t).degree + ((n : ℕ) : WithBot ℕ)
        ≤ 0 + ((n : ℕ) : WithBot ℕ) := add_le_add degree_C_le le_rfl
      _ = ((n : ℕ) : WithBot ℕ) := zero_add _
  rw [monicOrtho_degree]
  exact lt_of_le_of_lt h1 (by exact_mod_cast Nat.lt_succ_self n)

theorem quasiOrtho_monic (s : ℕ → ℝ) (n : ℕ) (t : ℝ) : (quasiOrtho s n t).Monic :=
  (monicOrtho_monic s (n + 1)).add_of_left (quasiOrtho_aux_degree_lt s n t)

theorem quasiOrtho_degree (s : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    (quasiOrtho s n t).degree = (((n + 1 : ℕ)) : WithBot ℕ) := by
  rw [quasiOrtho, degree_add_eq_left_of_degree_lt (quasiOrtho_aux_degree_lt s n t),
    monicOrtho_degree]

theorem quasiOrtho_natDegree (s : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    (quasiOrtho s n t).natDegree = n + 1 :=
  natDegree_eq_of_degree_eq_some (quasiOrtho_degree s n t)

theorem quasiOrtho_ne_zero (s : ℕ → ℝ) (n : ℕ) (t : ℝ) : quasiOrtho s n t ≠ 0 :=
  (quasiOrtho_monic s n t).ne_zero

/-- **No nonreal root.**  A nonreal root would make the reproducing kernel sum vanish. -/
theorem quasiOrtho_aeval_ne_zero (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) : Polynomial.aeval z (quasiOrtho s n t) ≠ 0 := by
  intro hzero
  rw [aeval_quasiOrtho] at hzero
  have hQ : monicOrthoC s (n + 1) z = -(t : ℂ) * monicOrthoC s n z := by
    linear_combination hzero
  have hkey := kernelSum_mul_im h n z
  rw [hQ] at hkey
  have hreal : -(t : ℂ) * monicOrthoC s n z * (starRingEnd ℂ) (monicOrthoC s n z)
      = (((-t * Complex.normSq (monicOrthoC s n z) : ℝ)) : ℂ) := by
    rw [mul_assoc, Complex.mul_conj]
    push_cast
    ring
  rw [hreal, Complex.ofReal_im] at hkey
  have hzero0 : monicOrthoC s 0 z = 1 := by
    rw [monicOrthoC, monicOrtho_zero]
    simp
  have hsum_pos : 0 < ∑ k ∈ Finset.range (n + 1),
      Complex.normSq (monicOrthoC s k z) / momentInner s (monicOrtho s k) (monicOrtho s k) := by
    refine Finset.sum_pos'
      (fun k _ => div_nonneg (Complex.normSq_nonneg _) (monicOrtho_inner_self_pos h k).le)
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos n), ?_⟩
    rw [hzero0, Complex.normSq_one]
    exact div_pos one_pos (monicOrtho_inner_self_pos h 0)
  exact absurd hkey
    (mul_ne_zero (mul_ne_zero hsum_pos.ne' hz) (monicOrtho_inner_self_pos h n).ne')

theorem quasiOrtho_root_im_eq_zero (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) {z : ℂ}
    (hz : Polynomial.aeval z (quasiOrtho s n t) = 0) : z.im = 0 := by
  by_contra hne
  exact quasiOrtho_aeval_ne_zero h n t hne hz

/-- **The quasi-orthogonal polynomial splits over `ℝ`.** -/
theorem quasiOrtho_splits (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) :
    (quasiOrtho s n t).Splits :=
  splits_of_forall_aeval_im_eq_zero (quasiOrtho s n t).natDegree (quasiOrtho s n t) le_rfl
    fun _ hz => quasiOrtho_root_im_eq_zero h n t hz

/-- **No repeated root.**  Cancelling the linear factor in the collapsed Christoffel--Darboux
identity and evaluating at the root would make the kernel diagonal vanish. -/
theorem quasiOrtho_not_sq_dvd (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) (r : ℝ) :
    ¬ (((X - C r) ^ 2 : Polynomial ℝ) ∣ quasiOrtho s n t) := by
  rintro ⟨H, hH⟩
  have hn0 : momentInner s (monicOrtho s n) (monicOrtho s n) ≠ 0 :=
    (monicOrtho_inner_self_pos h n).ne'
  have hPr : (quasiOrtho s n t).eval r = 0 := by
    rw [hH]
    simp
  rw [quasiOrtho_eval] at hPr
  have hrel : (monicOrtho s (n + 1)).eval r = -t * (monicOrtho s n).eval r := by linarith
  have hpoly : (X - C r) *
        (cdKernel s n r * C (momentInner s (monicOrtho s n) (monicOrtho s n)))
      = (X - C r) * (C ((monicOrtho s n).eval r) * ((X - C r) * H)) := by
    refine Polynomial.funext fun x => ?_
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    have hcd := christoffelDarboux h n x r
    rw [eq_div_iff hn0, hrel] at hcd
    have h1 : (cdKernel s n r).eval x = ∑ k ∈ Finset.range (n + 1),
        (monicOrtho s k).eval x * (monicOrtho s k).eval r /
          momentInner s (monicOrtho s k) (monicOrtho s k) := by
      rw [cdKernel_symm, cdKernel_eval]
    have hPx : (monicOrtho s (n + 1)).eval x + t * (monicOrtho s n).eval x
        = (x - r) ^ 2 * H.eval x := by
      rw [← quasiOrtho_eval, hH]
      simp
    rw [h1]
    linear_combination hcd + (monicOrtho s n).eval r * hPx
  have hcancel := mul_left_cancel₀ (X_sub_C_ne_zero r) hpoly
  have hev := congrArg (Polynomial.eval r) hcancel
  simp only [eval_mul, eval_C, eval_sub, eval_X, sub_self, zero_mul, mul_zero] at hev
  exact absurd hev
    (ne_of_gt (mul_pos (cdKernel_eval_self_pos h n r) (monicOrtho_inner_self_pos h n)))

theorem quasiOrtho_rootMultiplicity_le_one (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) (r : ℝ) :
    rootMultiplicity r (quasiOrtho s n t) ≤ 1 := by
  by_contra hc
  exact quasiOrtho_not_sq_dvd h n t r
    (dvd_trans (pow_dvd_pow _ (not_le.mp hc)) (pow_rootMultiplicity_dvd _ _))

theorem quasiOrtho_roots_nodup (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) :
    (quasiOrtho s n t).roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro r
  rw [count_roots]
  exact quasiOrtho_rootMultiplicity_le_one h n t r

theorem quasiOrtho_roots_card (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) :
    Multiset.card (quasiOrtho s n t).roots = n + 1 := by
  rw [← (quasiOrtho_splits h n t).natDegree_eq_card_roots]
  exact quasiOrtho_natDegree s n t

/-- The nodes of the quasi-orthogonal quadrature rule of level `n` and parameter `t`. -/
noncomputable def quasiNodes (s : ℕ → ℝ) (n : ℕ) (t : ℝ) : Finset ℝ :=
  (quasiOrtho s n t).roots.toFinset

theorem mem_quasiNodes_iff (n : ℕ) (t : ℝ) (r : ℝ) :
    r ∈ quasiNodes s n t ↔ (quasiOrtho s n t).eval r = 0 := by
  classical
  rw [quasiNodes, Multiset.mem_toFinset, mem_roots']
  constructor
  · rintro ⟨-, hr⟩
    exact hr
  · intro hr
    exact ⟨quasiOrtho_ne_zero s n t, hr⟩

/-- **There are exactly `n+1` nodes**, for every real parameter. -/
theorem quasiNodes_card (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) :
    (quasiNodes s n t).card = n + 1 := by
  classical
  rw [quasiNodes, Multiset.toFinset_card_of_nodup (quasiOrtho_roots_nodup h n t),
    quasiOrtho_roots_card h n t]

end HTGeometry
