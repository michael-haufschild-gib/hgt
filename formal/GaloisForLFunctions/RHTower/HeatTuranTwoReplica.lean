import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.MeanInequalities

/-!
# The heat Turán defect is an exact two-replica sum

For a finite spectral family with weights `c_q` and points `w_q` the three filtered heat moments
`H_k(t) = ∑_q c_q w_q^k e^{-t w_q}` are the successive negative time derivatives of `H_0`, and their
adjacent determinant has the exact two-replica form

`2(H_0 H_2 − H_1²) = ∑_{q,r} (w_q − w_r)² (c_q e^{-t w_q})(c_r e^{-t w_r})`.

Two consequences are immediate and opposite.  If every `w_q` is real and every `c_q` is nonnegative
the determinant is the variance determinant of a positive measure, hence nonnegative — this is
Cauchy--Schwarz.  If instead the family is one off-line shell `w_q = A + iB_q`, every squared
difference is `-(B_q − B_r)²`, so

`2 e^{2tA} (H_0 H_2 − H_1²) = -∑_{q,r} (B_q − B_r)² e^{-it(B_q + B_r)}`,

whose value at a simultaneous phase recurrence is `-2·card·∑ B_q²` for a balanced shell: strictly
negative as soon as one transverse part is nonzero.
-/

open Complex

namespace RHTower

noncomputable section

variable {ι : Type*}

/-! ## The filtered heat moments -/

/-- The filtered heat moment of a finite spectral family. -/
def turanHeatMoment (s : Finset ι) (c w : ι → ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  ∑ q ∈ s, c q * w q ^ k * Complex.exp (-(t : ℂ) * w q)

/-- **(24.140)** The adjacent determinant of the three filtered moments. -/
def heatTuranDefect (s : Finset ι) (c w : ι → ℂ) (t : ℝ) : ℂ :=
  turanHeatMoment s c w 0 t * turanHeatMoment s c w 2 t - turanHeatMoment s c w 1 t ^ 2

/-- **(24.140)** Each filtered moment is the negative time derivative of the previous one. -/
theorem hasDerivAt_turanHeatMoment (s : Finset ι) (c w : ι → ℂ) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun tau : ℝ => turanHeatMoment s c w k tau) (-turanHeatMoment s c w (k + 1) t) t := by
  have hterm : ∀ q ∈ s, HasDerivAt
      (fun tau : ℝ => c q * w q ^ k * Complex.exp (-(tau : ℂ) * w q))
      (-(c q * w q ^ (k + 1) * Complex.exp (-(t : ℂ) * w q))) t := by
    intro q _
    have h1 : HasDerivAt (fun tau : ℝ => (tau : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have h2 : HasDerivAt (fun tau : ℝ => -(tau : ℂ) * w q) (-w q) t := by
      simpa using h1.neg.mul_const (w q)
    have h3 : HasDerivAt (fun tau : ℝ => Complex.exp (-(tau : ℂ) * w q))
        (Complex.exp (-(t : ℂ) * w q) * -w q) t := h2.cexp
    have h4 := h3.const_mul (c q * w q ^ k)
    refine h4.congr_deriv ?_
    rw [pow_succ]
    ring
  have hsum := HasDerivAt.sum hterm
  have hfun : (fun tau : ℝ => turanHeatMoment s c w k tau)
      = ∑ q ∈ s, fun tau : ℝ => c q * w q ^ k * Complex.exp (-(tau : ℂ) * w q) := by
    funext tau
    rw [turanHeatMoment, Finset.sum_apply]
  rw [hfun]
  refine hsum.congr_deriv ?_
  rw [turanHeatMoment, ← Finset.sum_neg_distrib]

/-! ## The two-replica identity -/

/-- **The exact two-replica form of the heat Turán defect.** -/
theorem two_mul_heatTuranDefect (s : Finset ι) (c w : ι → ℂ) (t : ℝ) :
    2 * heatTuranDefect s c w t
      = ∑ q ∈ s, ∑ r ∈ s, (w q - w r) ^ 2
          * (c q * Complex.exp (-(t : ℂ) * w q)) * (c r * Complex.exp (-(t : ℂ) * w r)) := by
  classical
  set u : ι → ℂ := fun q => c q * Complex.exp (-(t : ℂ) * w q) with hu
  have hM0 : turanHeatMoment s c w 0 t = ∑ q ∈ s, u q := by
    rw [turanHeatMoment]
    exact Finset.sum_congr rfl fun q _ => by rw [hu]; ring
  have hM1 : turanHeatMoment s c w 1 t = ∑ q ∈ s, w q * u q := by
    rw [turanHeatMoment]
    exact Finset.sum_congr rfl fun q _ => by rw [hu]; ring
  have hM2 : turanHeatMoment s c w 2 t = ∑ q ∈ s, w q ^ 2 * u q := by
    rw [turanHeatMoment]
    exact Finset.sum_congr rfl fun q _ => by rw [hu]; ring
  have hexpand : ∀ q ∈ s, ∀ r ∈ s,
      (w q - w r) ^ 2 * u q * u r
        = (w q ^ 2 * u q) * u r - 2 * (w q * u q) * (w r * u r) + u q * (w r ^ 2 * u r) := by
    intro q _ r _
    ring
  have hsum : ∑ q ∈ s, ∑ r ∈ s, (w q - w r) ^ 2 * u q * u r
      = (∑ q ∈ s, w q ^ 2 * u q) * (∑ r ∈ s, u r)
        - 2 * ((∑ q ∈ s, w q * u q) * (∑ r ∈ s, w r * u r))
        + (∑ q ∈ s, u q) * (∑ r ∈ s, w r ^ 2 * u r) := by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [Finset.sum_congr rfl (hexpand q hq), Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [← Finset.mul_sum]
    ring
  rw [heatTuranDefect, hM0, hM1, hM2]
  rw [show (∑ q ∈ s, ∑ r ∈ s, (w q - w r) ^ 2 * (c q * Complex.exp (-(t : ℂ) * w q))
        * (c r * Complex.exp (-(t : ℂ) * w r)))
      = ∑ q ∈ s, ∑ r ∈ s, (w q - w r) ^ 2 * u q * u r from rfl, hsum]
  ring

/-! ## The real shell: Cauchy--Schwarz positivity -/

/-- **The forward implication.**  A real spectral family with nonnegative weights has a nonnegative
heat Turán defect: it is the variance determinant of a positive measure. -/
theorem heatTuranDefect_real_nonneg (s : Finset ι) (c w : ι → ℝ) (hc : ∀ q ∈ s, 0 ≤ c q)
    (t : ℝ) :
    (∑ q ∈ s, c q * w q * Real.exp (-(t * w q))) ^ 2
      ≤ (∑ q ∈ s, c q * Real.exp (-(t * w q)))
        * ∑ q ∈ s, c q * w q ^ 2 * Real.exp (-(t * w q)) := by
  classical
  have hsq : ∀ q ∈ s, Real.sqrt (c q * Real.exp (-(t * w q))) ^ 2
      = c q * Real.exp (-(t * w q)) :=
    fun q hq => Real.sq_sqrt (mul_nonneg (hc q hq) (Real.exp_nonneg _))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun q => Real.sqrt (c q * Real.exp (-(t * w q))))
    (fun q => w q * Real.sqrt (c q * Real.exp (-(t * w q))))
  have h1 : ∑ q ∈ s, Real.sqrt (c q * Real.exp (-(t * w q)))
        * (w q * Real.sqrt (c q * Real.exp (-(t * w q))))
      = ∑ q ∈ s, c q * w q * Real.exp (-(t * w q)) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [show Real.sqrt (c q * Real.exp (-(t * w q)))
          * (w q * Real.sqrt (c q * Real.exp (-(t * w q))))
        = w q * Real.sqrt (c q * Real.exp (-(t * w q))) ^ 2 from by ring, hsq q hq]
    ring
  have h2 : ∑ q ∈ s, Real.sqrt (c q * Real.exp (-(t * w q))) ^ 2
      = ∑ q ∈ s, c q * Real.exp (-(t * w q)) := Finset.sum_congr rfl hsq
  have h3 : ∑ q ∈ s, (w q * Real.sqrt (c q * Real.exp (-(t * w q)))) ^ 2
      = ∑ q ∈ s, c q * w q ^ 2 * Real.exp (-(t * w q)) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [mul_pow, hsq q hq]
    ring
  rw [h1, h2, h3] at hcs
  exact hcs

/-! ## The off-line shell -/

/-- **(24.142) The off-line shell identity.**  On a single shell `w = A + iB` the two-replica sum is
the negative of a squared-transverse phase sum. -/
theorem two_mul_heatTuranDefect_shell (s : Finset ι) (A : ℝ) (B : ι → ℝ) (t : ℝ) :
    2 * Complex.exp (2 * (t : ℂ) * (A : ℂ))
        * heatTuranDefect s (fun _ => 1) (fun q => (A : ℂ) + Complex.I * (B q : ℂ)) t
      = -∑ q ∈ s, ∑ r ∈ s, ((B q - B r : ℝ) : ℂ) ^ 2
          * Complex.exp (-Complex.I * (t : ℂ) * ((B q : ℂ) + (B r : ℂ))) := by
  classical
  have hbase := two_mul_heatTuranDefect s (fun _ => 1)
    (fun q => (A : ℂ) + Complex.I * (B q : ℂ)) t
  have hterm : ∀ q ∈ s, ∀ r ∈ s,
      Complex.exp (2 * (t : ℂ) * (A : ℂ)) *
          (((A : ℂ) + Complex.I * (B q : ℂ)) - ((A : ℂ) + Complex.I * (B r : ℂ))) ^ 2
            * ((1 : ℂ) * Complex.exp (-(t : ℂ) * ((A : ℂ) + Complex.I * (B q : ℂ))))
            * ((1 : ℂ) * Complex.exp (-(t : ℂ) * ((A : ℂ) + Complex.I * (B r : ℂ))))
        = -(((B q - B r : ℝ) : ℂ) ^ 2
            * Complex.exp (-Complex.I * (t : ℂ) * ((B q : ℂ) + (B r : ℂ)))) := by
    intro q _ r _
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have hexp : Complex.exp (2 * (t : ℂ) * (A : ℂ))
        * (Complex.exp (-(t : ℂ) * ((A : ℂ) + Complex.I * (B q : ℂ)))
          * Complex.exp (-(t : ℂ) * ((A : ℂ) + Complex.I * (B r : ℂ))))
        = Complex.exp (-Complex.I * (t : ℂ) * ((B q : ℂ) + (B r : ℂ))) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring
    have hsq : (((A : ℂ) + Complex.I * (B q : ℂ)) - ((A : ℂ) + Complex.I * (B r : ℂ))) ^ 2
        = -((B q - B r : ℝ) : ℂ) ^ 2 := by
      push_cast
      linear_combination ((B q : ℂ) - (B r : ℂ)) ^ 2 * hI
    calc Complex.exp (2 * (t : ℂ) * (A : ℂ)) *
          (((A : ℂ) + Complex.I * (B q : ℂ)) - ((A : ℂ) + Complex.I * (B r : ℂ))) ^ 2
            * ((1 : ℂ) * Complex.exp (-(t : ℂ) * ((A : ℂ) + Complex.I * (B q : ℂ))))
            * ((1 : ℂ) * Complex.exp (-(t : ℂ) * ((A : ℂ) + Complex.I * (B r : ℂ))))
        = (((A : ℂ) + Complex.I * (B q : ℂ)) - ((A : ℂ) + Complex.I * (B r : ℂ))) ^ 2
            * (Complex.exp (2 * (t : ℂ) * (A : ℂ))
              * (Complex.exp (-(t : ℂ) * ((A : ℂ) + Complex.I * (B q : ℂ)))
                * Complex.exp (-(t : ℂ) * ((A : ℂ) + Complex.I * (B r : ℂ))))) := by ring
      _ = -((B q - B r : ℝ) : ℂ) ^ 2
            * Complex.exp (-Complex.I * (t : ℂ) * ((B q : ℂ) + (B r : ℂ))) := by
          rw [hexp, hsq]
      _ = -(((B q - B r : ℝ) : ℂ) ^ 2
            * Complex.exp (-Complex.I * (t : ℂ) * ((B q : ℂ) + (B r : ℂ)))) := by ring
  calc 2 * Complex.exp (2 * (t : ℂ) * (A : ℂ))
        * heatTuranDefect s (fun _ => 1) (fun q => (A : ℂ) + Complex.I * (B q : ℂ)) t
      = Complex.exp (2 * (t : ℂ) * (A : ℂ)) *
          (2 * heatTuranDefect s (fun _ => 1) (fun q => (A : ℂ) + Complex.I * (B q : ℂ)) t) := by
        ring
    _ = ∑ q ∈ s, ∑ r ∈ s, Complex.exp (2 * (t : ℂ) * (A : ℂ)) *
          (((A : ℂ) + Complex.I * (B q : ℂ)) - ((A : ℂ) + Complex.I * (B r : ℂ))) ^ 2
            * ((1 : ℂ) * Complex.exp (-(t : ℂ) * ((A : ℂ) + Complex.I * (B q : ℂ))))
            * ((1 : ℂ) * Complex.exp (-(t : ℂ) * ((A : ℂ) + Complex.I * (B r : ℂ)))) := by
        rw [hbase, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
    _ = -∑ q ∈ s, ∑ r ∈ s, ((B q - B r : ℝ) : ℂ) ^ 2
          * Complex.exp (-Complex.I * (t : ℂ) * ((B q : ℂ) + (B r : ℂ))) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun q hq => ?_
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun r hr => hterm q hq r hr

/-! ## The recurrence value -/

/-- The squared-difference sum of a finite family. -/
theorem sum_sq_diff_eq (s : Finset ι) (B : ι → ℝ) :
    ∑ q ∈ s, ∑ r ∈ s, (B q - B r) ^ 2
      = 2 * (s.card : ℝ) * (∑ q ∈ s, B q ^ 2) - 2 * (∑ q ∈ s, B q) ^ 2 := by
  classical
  have hexpand : ∀ q ∈ s, ∑ r ∈ s, (B q - B r) ^ 2
      = (s.card : ℝ) * B q ^ 2 - 2 * B q * (∑ r ∈ s, B r) + ∑ r ∈ s, B r ^ 2 := by
    intro q _
    have hterm : ∀ r ∈ s, (B q - B r) ^ 2 = B q ^ 2 - 2 * B q * B r + B r ^ 2 := by
      intro r _
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-- **(24.142) The recurrence value.**  For a balanced shell with one nonzero transverse part the
squared-difference sum is strictly positive, so the recurrence value of the defect is strictly
negative. -/
theorem sum_sq_diff_pos_of_balanced (s : Finset ι) (B : ι → ℝ) (hbal : ∑ q ∈ s, B q = 0)
    {q₀ : ι} (hq₀ : q₀ ∈ s) (hne : B q₀ ≠ 0) :
    0 < ∑ q ∈ s, ∑ r ∈ s, (B q - B r) ^ 2 := by
  classical
  have hcard : (1 : ℝ) ≤ (s.card : ℝ) := by
    have h : 1 ≤ s.card := Finset.card_pos.2 ⟨q₀, hq₀⟩
    exact_mod_cast h
  have hsq : 0 < ∑ q ∈ s, B q ^ 2 := by
    refine Finset.sum_pos' (fun q _ => sq_nonneg _) ⟨q₀, hq₀, ?_⟩
    exact pow_pos (abs_pos.2 hne) 2 |>.trans_le (le_of_eq (sq_abs _))
  rw [sum_sq_diff_eq, hbal]
  nlinarith

end

end RHTower
