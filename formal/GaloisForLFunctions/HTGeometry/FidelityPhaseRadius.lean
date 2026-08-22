/-
# Fidelity deficit and the phase-lattice radius are quadratically comparable

The Loschmidt return amplitude of a weighted spectral packet is the weighted overlap of the
evolved phases, so its fidelity deficit is one half of the weighted pairwise squared chord.  Each
chord is bounded above by the residual phase difference and below, by Jordan's inequality, by four
times the distance of that difference to the turn lattice.  Hence a phase return of radius `r`
makes the deficit at most `8 pi^2 r^2`, and a deficit below `d` forces every anchored gap phase to
within `sqrt d / (2 c)` of a whole turn, where `c` is a lower bound for the weights.

Fidelity deficit is therefore locally equivalent to the squared projective phase radius, which is
what halves a first-return exponent read in fidelity rather than in phase.

Main results:
* `norm_expI_sub_expI`, `norm_expI_sub_expI_shift` — the chord of two unit phases.
* `norm_expI_sub_expI_le`, `four_mul_abs_sub_int_le_norm` — its two-sided lattice estimate.
* `two_mul_spectralReturnDeficit_eq` — the dispersion form of the deficit.
* `spectralReturnDeficit_le_of_latticeClose` — **a phase return makes the deficit quadratically
  small**.
* `latticeClose_of_spectralReturnDeficit_lt` — **a small deficit forces a phase return**.
-/
import GaloisForLFunctions.HTGeometry.FinitePhaseFidelityDispersion
import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet

open scoped BigOperators
open Real

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

set_option linter.unusedVariables false

noncomputable section

/-! ## The chord between two unit phases -/

theorem norm_expI_sub_one (c : ℝ) :
    ‖Complex.exp ((c : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (c / 2)| := by
  have hre : (Complex.exp ((c : ℂ) * Complex.I) - 1).re = Real.cos c - 1 := by
    simp [Complex.exp_ofReal_mul_I_re]
  have him : (Complex.exp ((c : ℂ) * Complex.I) - 1).im = Real.sin c := by
    simp [Complex.exp_ofReal_mul_I_im]
  have hsq : ‖Complex.exp ((c : ℂ) * Complex.I) - 1‖ ^ 2 = (2 * |Real.sin (c / 2)|) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    have hcos : Real.cos c = 1 - 2 * Real.sin (c / 2) ^ 2 := by
      have := Real.cos_two_mul_eq_one_sub (c / 2)
      rw [show 2 * (c / 2) = c from by ring] at this
      exact this
    have hpy : Real.sin c ^ 2 = 1 - Real.cos c ^ 2 := by
      have := Real.sin_sq_add_cos_sq c
      linarith
    rw [mul_pow, sq_abs]
    nlinarith [hcos, hpy]
  have h1 : (0 : ℝ) ≤ ‖Complex.exp ((c : ℂ) * Complex.I) - 1‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ 2 * |Real.sin (c / 2)| := by positivity
  nlinarith [hsq, h1, h2]

theorem norm_expI_sub_expI (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖
      = 2 * |Real.sin ((a - b) / 2)| := by
  have hfac : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)
      = Complex.exp ((b : ℂ) * Complex.I) *
        (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_expI_sub_one]

theorem abs_sin_sub_int_mul_pi (x : ℝ) (m : ℤ) :
    |Real.sin (x - (m : ℝ) * π)| = |Real.sin x| := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
      push_cast at ih ⊢
      rw [show x - ((k : ℝ) + 1) * π = (x - (k : ℝ) * π) - π from by ring, Real.sin_sub_pi,
        abs_neg]
      exact ih
  | pred k ih =>
      push_cast at ih ⊢
      rw [show x - (-(k : ℝ) - 1) * π = (x - -(k : ℝ) * π) + π from by ring, Real.sin_add_pi,
        abs_neg]
      exact ih

/-- The chord is periodic: shifting by a whole number of turns does not change it. -/
theorem norm_expI_sub_expI_shift (a b : ℝ) (m : ℤ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖
      = 2 * |Real.sin ((a - b - 2 * π * m) / 2)| := by
  rw [norm_expI_sub_expI]
  congr 1
  rw [show (a - b - 2 * π * (m : ℝ)) / 2 = (a - b) / 2 - (m : ℝ) * π from by ring,
    abs_sin_sub_int_mul_pi]

/-- The chord is at most the residual phase difference. -/
theorem norm_expI_sub_expI_le (a b : ℝ) (m : ℤ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖
      ≤ |a - b - 2 * π * m| := by
  rw [norm_expI_sub_expI_shift a b m]
  have h : |Real.sin ((a - b - 2 * π * (m : ℝ)) / 2)| ≤ |(a - b - 2 * π * (m : ℝ)) / 2| :=
    abs_sin_le_abs
  have habs : |(a - b - 2 * π * (m : ℝ)) / 2| = |a - b - 2 * π * (m : ℝ)| / 2 := by
    rw [abs_div]
    norm_num
  rw [habs] at h
  linarith

/-- The sine of a half chord is the sine of its absolute value. -/
theorem abs_sin_eq_sin_abs_of_le {y : ℝ} (hy : |y| ≤ π / 2) :
    |Real.sin y| = Real.sin |y| := by
  rcases le_or_gt 0 y with hy0 | hy0
  · rw [abs_of_nonneg hy0]
    rw [abs_of_nonneg hy0] at hy
    exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hy0 (by linarith [Real.pi_pos]))
  · rw [abs_of_neg hy0, Real.sin_neg]
    rw [abs_of_neg hy0] at hy
    have : Real.sin y ≤ 0 := by
      have := Real.sin_nonneg_of_nonneg_of_le_pi (x := -y) (by linarith)
        (by linarith [Real.pi_pos])
      rw [Real.sin_neg] at this
      linarith
    rw [abs_of_nonpos this]

/-- **Jordan's inequality for the phase chord.**  The chord between two unit phases dominates
four times the distance of their phase difference to the turn lattice. -/
theorem four_mul_abs_sub_int_le_norm (a b : ℝ) (m : ℤ)
    (hm : |(a - b) / (2 * π) - (m : ℝ)| ≤ 1 / 2) :
    4 * |(a - b) / (2 * π) - (m : ℝ)|
      ≤ ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  set u : ℝ := (a - b) / (2 * π) with hu
  set c : ℝ := a - b - 2 * π * (m : ℝ) with hc
  have hcu : c = 2 * π * (u - (m : ℝ)) := by
    rw [hc, hu]
    field_simp
  have hcabs : |c| = 2 * π * |u - (m : ℝ)| := by
    rw [hcu, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * π)]
  have hchalf : |c / 2| ≤ π / 2 := by
    rw [abs_div, show |(2 : ℝ)| = 2 from by norm_num, hcabs]
    nlinarith [abs_nonneg (u - (m : ℝ))]
  have hjordan : 2 / π * |c / 2| ≤ Real.sin |c / 2| :=
    Real.mul_le_sin (abs_nonneg _) hchalf
  have hsin : |Real.sin (c / 2)| = Real.sin |c / 2| := abs_sin_eq_sin_abs_of_le hchalf
  have hnorm : ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖
      = 2 * |Real.sin (c / 2)| := norm_expI_sub_expI_shift a b m
  rw [hnorm, hsin]
  have hhalf : |c / 2| = |c| / 2 := by
    rw [abs_div]
    norm_num
  have hkey : 2 / π * |c / 2| = 2 * |u - (m : ℝ)| := by
    rw [hhalf, hcabs]
    field_simp
  nlinarith [hjordan, hkey]

/-! ## The fidelity deficit of a weighted spectral packet -/

variable {D : ℕ}

/-- The Loschmidt return amplitude of a weighted spectral packet. -/
def spectralReturnAmplitude (E p : Fin D → ℝ) (t : ℝ) : ℂ :=
  ∑ j, (p j : ℂ) * Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)

/-- The fidelity deficit of the weighted spectral packet at time `t`. -/
def spectralReturnDeficit (E p : Fin D → ℝ) (t : ℝ) : ℝ :=
  1 - ‖spectralReturnAmplitude E p t‖ ^ 2

theorem spectralReturnAmplitude_eq_finitePhaseOverlap (E p : Fin D → ℝ) (t : ℝ) :
    spectralReturnAmplitude E p t
      = _root_.HTGeometry.finitePhaseOverlap p
          (fun j => Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)) := rfl

/-- **The dispersion form of the fidelity deficit.**  Twice the deficit is the weighted pairwise
squared chord of the evolved phases. -/
theorem two_mul_spectralReturnDeficit_eq (E p : Fin D → ℝ) (hp1 : ∑ j, p j = 1) (t : ℝ) :
    2 * spectralReturnDeficit E p t
      = ∑ j, ∑ k, p j * p k *
          ‖Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)
            - Complex.exp (((-(t * E k) : ℝ) : ℂ) * Complex.I)‖ ^ 2 := by
  have h := _root_.HTGeometry.finitePhasePairwiseDispersion_eq_two_mul_fidelityDeficit
    p (fun j => Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)) hp1
    (fun j => Complex.norm_exp_ofReal_mul_I _)
  rw [spectralReturnDeficit, spectralReturnAmplitude_eq_finitePhaseOverlap, ← h,
    _root_.HTGeometry.finitePhasePairwiseDispersion]

theorem spectralReturnDeficit_nonneg (E p : Fin D → ℝ) (hp1 : ∑ j, p j = 1)
    (hpnn : ∀ j, 0 ≤ p j) (t : ℝ) : 0 ≤ spectralReturnDeficit E p t := by
  rw [spectralReturnDeficit, spectralReturnAmplitude_eq_finitePhaseOverlap]
  exact _root_.HTGeometry.finitePhase_fidelityDeficit_nonneg p _ hp1 hpnn
    (fun j => Complex.norm_exp_ofReal_mul_I _)

/-- **A phase return makes the fidelity deficit quadratically small.** -/
theorem spectralReturnDeficit_le_of_latticeClose (E p : Fin D → ℝ)
    (hp1 : ∑ j, p j = 1) (hpnn : ∀ j, 0 ≤ p j) (anchor : Fin D) {r t : ℝ} (hr : 0 ≤ r)
    (hret : ∀ j, latticeClose (t * (E j - E anchor) / (2 * π)) r) :
    spectralReturnDeficit E p t ≤ 8 * π ^ 2 * r ^ 2 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hchord : ∀ j k, ‖Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)
        - Complex.exp (((-(t * E k) : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤ 16 * π ^ 2 * r ^ 2 := by
    intro j k
    obtain ⟨mj, hmj⟩ := hret j
    obtain ⟨mk, hmk⟩ := hret k
    have hle := norm_expI_sub_expI_le (-(t * E j)) (-(t * E k)) (mk - mj)
    have hval : (-(t * E j)) - (-(t * E k)) - 2 * π * (((mk - mj : ℤ)) : ℝ)
        = 2 * π * ((t * (E k - E anchor) / (2 * π) - (mk : ℝ))
            - (t * (E j - E anchor) / (2 * π) - (mj : ℝ))) := by
      push_cast
      field_simp
      ring
    have hb : |(t * (E k - E anchor) / (2 * π) - (mk : ℝ))
        - (t * (E j - E anchor) / (2 * π) - (mj : ℝ))| ≤ 2 * r := by
      calc |(t * (E k - E anchor) / (2 * π) - (mk : ℝ))
            - (t * (E j - E anchor) / (2 * π) - (mj : ℝ))|
          ≤ |t * (E k - E anchor) / (2 * π) - (mk : ℝ)|
            + |t * (E j - E anchor) / (2 * π) - (mj : ℝ)| := abs_sub _ _
        _ ≤ 2 * r := by linarith [hmj, hmk]
    have habs : |(-(t * E j)) - (-(t * E k)) - 2 * π * (((mk - mj : ℤ)) : ℝ)|
        ≤ 2 * π * (2 * r) := by
      rw [hval, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * π)]
      nlinarith [hb, hpi, abs_nonneg ((t * (E k - E anchor) / (2 * π) - (mk : ℝ))
        - (t * (E j - E anchor) / (2 * π) - (mj : ℝ)))]
    have hnn : (0 : ℝ) ≤ ‖Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)
        - Complex.exp (((-(t * E k) : ℝ) : ℂ) * Complex.I)‖ := norm_nonneg _
    have hfin : ‖Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)
        - Complex.exp (((-(t * E k) : ℝ) : ℂ) * Complex.I)‖ ≤ 4 * π * r := by
      have := hle.trans habs
      linarith
    nlinarith [hfin, hnn, hr, hpi.le]
  have hsum : ∑ j, ∑ k, p j * p k *
        ‖Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((-(t * E k) : ℝ) : ℂ) * Complex.I)‖ ^ 2
      ≤ 16 * π ^ 2 * r ^ 2 := by
    have hstep : ∀ j ∈ (Finset.univ : Finset (Fin D)),
        ∑ k, p j * p k *
            ‖Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)
              - Complex.exp (((-(t * E k) : ℝ) : ℂ) * Complex.I)‖ ^ 2
          ≤ p j * (16 * π ^ 2 * r ^ 2) := by
      intro j _
      have hb : ∑ k, p j * p k *
            ‖Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)
              - Complex.exp (((-(t * E k) : ℝ) : ℂ) * Complex.I)‖ ^ 2
          ≤ ∑ k, p j * (16 * π ^ 2 * r ^ 2) * p k := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hpp : (0 : ℝ) ≤ p j * p k := mul_nonneg (hpnn j) (hpnn k)
        calc p j * p k *
              ‖Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)
                - Complex.exp (((-(t * E k) : ℝ) : ℂ) * Complex.I)‖ ^ 2
            ≤ p j * p k * (16 * π ^ 2 * r ^ 2) :=
              mul_le_mul_of_nonneg_left (hchord j k) hpp
          _ = p j * (16 * π ^ 2 * r ^ 2) * p k := by ring
      calc _ ≤ ∑ k, p j * (16 * π ^ 2 * r ^ 2) * p k := hb
        _ = p j * (16 * π ^ 2 * r ^ 2) := by rw [← Finset.mul_sum, hp1, mul_one]
    calc ∑ j, ∑ k, p j * p k *
          ‖Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)
            - Complex.exp (((-(t * E k) : ℝ) : ℂ) * Complex.I)‖ ^ 2
        ≤ ∑ j, p j * (16 * π ^ 2 * r ^ 2) := Finset.sum_le_sum hstep
      _ = 16 * π ^ 2 * r ^ 2 := by rw [← Finset.sum_mul, hp1, one_mul]
  have hdisp := two_mul_spectralReturnDeficit_eq E p hp1 t
  linarith [hdisp ▸ hsum]

/-- **The fidelity deficit controls the distance to the phase lattice.** -/
theorem sixteen_mul_sq_abs_sub_round_le (E p : Fin D → ℝ) (hp1 : ∑ j, p j = 1)
    (hpnn : ∀ j, 0 ≤ p j) (anchor : Fin D) (t : ℝ) (j : Fin D) :
    16 * (p j * p anchor)
        * (t * (E j - E anchor) / (2 * π)
            - (round (t * (E j - E anchor) / (2 * π)) : ℝ)) ^ 2
      ≤ 2 * spectralReturnDeficit E p t := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  set x : ℝ := t * (E j - E anchor) / (2 * π) with hx
  set d : ℝ := x - (round x : ℝ) with hd
  have hkey : 4 * |d|
      ≤ ‖Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((-(t * E anchor) : ℝ) : ℂ) * Complex.I)‖ := by
    have harg : ((-(t * E j)) - (-(t * E anchor))) / (2 * π) = -x := by
      rw [hx]
      field_simp
      ring
    have hbnd : |((-(t * E j)) - (-(t * E anchor))) / (2 * π) - ((-(round x) : ℤ) : ℝ)|
        ≤ 1 / 2 := by
      rw [harg]
      push_cast
      rw [show -x - -(round x : ℝ) = -(x - (round x : ℝ)) from by ring, abs_neg, ← hd]
      exact abs_sub_round x
    have h := four_mul_abs_sub_int_le_norm (-(t * E j)) (-(t * E anchor))
      (-(round x)) hbnd
    rw [harg] at h
    have heq : |(-x) - ((-(round x) : ℤ) : ℝ)| = |d| := by
      push_cast
      rw [show -x - -(round x : ℝ) = -(x - (round x : ℝ)) from by ring, abs_neg, ← hd]
    rw [heq] at h
    exact h
  have hnn : ∀ y ∈ (Finset.univ : Finset (Fin D)),
      0 ≤ ∑ k, p y * p k *
        ‖Complex.exp (((-(t * E y) : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((-(t * E k) : ℝ) : ℂ) * Complex.I)‖ ^ 2 := fun y _ =>
    Finset.sum_nonneg fun k _ => mul_nonneg (mul_nonneg (hpnn y) (hpnn k)) (sq_nonneg _)
  have hrow : ∑ k, p j * p k *
        ‖Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((-(t * E k) : ℝ) : ℂ) * Complex.I)‖ ^ 2
      ≤ ∑ y, ∑ k, p y * p k *
        ‖Complex.exp (((-(t * E y) : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((-(t * E k) : ℝ) : ℂ) * Complex.I)‖ ^ 2 :=
    Finset.single_le_sum hnn (Finset.mem_univ j)
  have hcell : p j * p anchor *
        ‖Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((-(t * E anchor) : ℝ) : ℂ) * Complex.I)‖ ^ 2
      ≤ ∑ k, p j * p k *
        ‖Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((-(t * E k) : ℝ) : ℂ) * Complex.I)‖ ^ 2 :=
    Finset.single_le_sum
      (f := fun k => p j * p k *
        ‖Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((-(t * E k) : ℝ) : ℂ) * Complex.I)‖ ^ 2)
      (fun k _ => mul_nonneg (mul_nonneg (hpnn j) (hpnn k)) (sq_nonneg _))
      (Finset.mem_univ anchor)
  have hdisp := two_mul_spectralReturnDeficit_eq E p hp1 t
  have hsq : 16 * d ^ 2
      ≤ ‖Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((-(t * E anchor) : ℝ) : ℂ) * Complex.I)‖ ^ 2 := by
    have h0 : (0 : ℝ) ≤ 4 * |d| := by positivity
    nlinarith [hkey, h0, sq_abs d]
  have hpp : (0 : ℝ) ≤ p j * p anchor := mul_nonneg (hpnn j) (hpnn anchor)
  have hmul : p j * p anchor * (16 * d ^ 2)
      ≤ p j * p anchor *
        ‖Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((-(t * E anchor) : ℝ) : ℂ) * Complex.I)‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hpp
  rw [hdisp]
  linarith [hmul, hcell, hrow]

/-- **A small fidelity deficit forces a phase return.** -/
theorem latticeClose_of_spectralReturnDeficit_lt (E p : Fin D → ℝ)
    (hp1 : ∑ j, p j = 1) (hpnn : ∀ j, 0 ≤ p j) (anchor : Fin D)
    {c δ t : ℝ} (hc : 0 < c) (hcp : ∀ j, c ≤ p j)
    (hdef : spectralReturnDeficit E p t < δ) (j : Fin D) :
    latticeClose (t * (E j - E anchor) / (2 * π)) (Real.sqrt δ / (2 * c)) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hnn := spectralReturnDeficit_nonneg E p hp1 hpnn t
  have hδ : 0 < δ := lt_of_le_of_lt hnn hdef
  set x : ℝ := t * (E j - E anchor) / (2 * π) with hx
  set d : ℝ := x - (round x : ℝ) with hd
  have hmain := sixteen_mul_sq_abs_sub_round_le E p hp1 hpnn anchor t j
  have hcc : c * c ≤ p j * p anchor :=
    mul_le_mul (hcp j) (hcp anchor) hc.le (le_trans hc.le (hcp j))
  have hbound : 16 * (c * c) * d ^ 2 ≤ 2 * δ := by
    nlinarith [hmain, hdef, sq_nonneg d]
  have hrhs : (Real.sqrt δ / (2 * c)) ^ 2 = δ / (4 * (c * c)) := by
    rw [div_pow, Real.sq_sqrt hδ.le]
    ring_nf
  have hsq : d ^ 2 < (Real.sqrt δ / (2 * c)) ^ 2 := by
    rw [hrhs, lt_div_iff₀ (by positivity)]
    nlinarith [hbound, hδ, sq_nonneg d, hc]
  have h0 : (0 : ℝ) < Real.sqrt δ / (2 * c) := by positivity
  refine ⟨round x, ?_⟩
  have habs : |d| < Real.sqrt δ / (2 * c) := by
    nlinarith [hsq, sq_abs d, abs_nonneg d, h0]
  exact habs

end

end GaloisForLFunctions.HTGeometry
