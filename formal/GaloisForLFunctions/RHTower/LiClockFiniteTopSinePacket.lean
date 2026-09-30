import GaloisForLFunctions.RHTower.SimultaneousPhaseRecurrence
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The negative coherent limit of a finite top sine packet

For a finite nonempty family of complex frequencies with common positive absolute imaginary
part `b`, simultaneous phase recurrence supplies clocks tending to infinity along which the
sine packet, normalized by `exp (-b * t)`, converges to `-b * card / 2`.

The exact atom identity treats both signs of the imaginary part uniformly. No independence
of the real frequencies or arithmetic source premise is required.
-/

open Complex Filter Topology

namespace RHTower

private theorem sine_atom_re (w : ℂ) (t : ℝ) :
    (w * Complex.sin ((t : ℂ) * w)).re =
      w.re * Real.sin (t * w.re) * Real.cosh (t * w.im) -
      w.im * Real.cos (t * w.re) * Real.sinh (t * w.im) := by
  rw [Complex.sin_eq]
  simp [Complex.mul_re, Complex.mul_im, -Complex.ofReal_mul,
    Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re,
    Complex.cosh_ofReal_re]
  ring

/-- Both signs of the imaginary part give the same leading normalized sine atom. -/
theorem liClockTopSineAtom_normalized_eq (w : ℂ) {b : ℝ}
    (hw : |w.im| = b) (t : ℝ) :
    Real.exp (-b * t) * (w * Complex.sin ((t : ℂ) * w)).re =
      (w.re * Real.sin (t * w.re) - b * Real.cos (t * w.re)) / 2 +
      Real.exp (-2 * b * t) *
        (w.re * Real.sin (t * w.re) + b * Real.cos (t * w.re)) / 2 := by
  have hi : w.im = b ∨ w.im = -b := by
    rcases le_total 0 w.im with h | h
    · left
      simpa only [abs_of_nonneg h] using hw
    · right
      rw [abs_of_nonpos h] at hw
      linarith
  have hc : Real.cosh (t * w.im) = Real.cosh (t * b) := by
    rcases hi with h | h
    · rw [h]
    · rw [h, mul_neg, Real.cosh_neg]
  have hs : w.im * Real.sinh (t * w.im) = b * Real.sinh (t * b) := by
    rcases hi with h | h
    · rw [h]
    · rw [h, mul_neg, Real.sinh_neg]
      ring
  have hp : Real.exp (-b * t) * Real.exp (t * b) = 1 := by
    rw [← Real.exp_add]
    have hz : -b * t + t * b = 0 := by ring
    rw [hz, Real.exp_zero]
  have hn : Real.exp (-b * t) * Real.exp (-(t * b)) = Real.exp (-2 * b * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcosh : Real.exp (-b * t) * Real.cosh (t * b) =
      (1 + Real.exp (-2 * b * t)) / 2 := by
    rw [Real.cosh_eq]
    calc
      _ = (Real.exp (-b * t) * Real.exp (t * b) +
        Real.exp (-b * t) * Real.exp (-(t * b))) / 2 := by ring
      _ = _ := by rw [hp, hn]
  have hsinh : Real.exp (-b * t) * Real.sinh (t * b) =
      (1 - Real.exp (-2 * b * t)) / 2 := by
    rw [Real.sinh_eq]
    calc
      _ = (Real.exp (-b * t) * Real.exp (t * b) -
        Real.exp (-b * t) * Real.exp (-(t * b))) / 2 := by ring
      _ = _ := by rw [hp, hn]
  rw [sine_atom_re, hc]
  calc
    _ = w.re * Real.sin (t * w.re) * (Real.exp (-b * t) * Real.cosh (t * b)) -
        Real.cos (t * w.re) * Real.exp (-b * t) *
          (w.im * Real.sinh (t * w.im)) := by ring
    _ = _ := by rw [hs]; rw [hcosh];
                calc
                  _ = w.re * Real.sin (t * w.re) * ((1 + Real.exp (-2 * b * t)) / 2) -
                    b * Real.cos (t * w.re) *
                      (Real.exp (-b * t) * Real.sinh (t * b)) := by ring
                  _ = _ := by rw [hsinh]; ring

/-- A finite nonempty top-growth packet has its negative normalized limit along cofinal clocks.
The clocks also satisfy the explicit lower bound `(n : ℝ) + 1`. -/
theorem exists_liClockFiniteTopSinePacket_negative_limit
    {ι : Type*} [Fintype ι] [Nonempty ι] (w : ι → ℂ) {b : ℝ}
    (hb : 0 < b) (hw : ∀ j, |(w j).im| = b) :
    ∃ t : ℕ → ℝ,
      (∀ n : ℕ, (n : ℝ) + 1 ≤ t n) ∧
      Tendsto t atTop atTop ∧
      Tendsto (fun n => Real.exp (-b * t n) *
        ∑ j, (w j * Complex.sin ((t n : ℂ) * w j)).re)
        atTop (𝓝 (-b * (Fintype.card ι : ℝ) / 2)) := by
  classical
  have hrec (n : ℕ) : ∃ t : ℝ, (n : ℝ) + 1 ≤ t ∧
      ∀ j, ‖GaloisForLFunctions.bohrChar (-(w j).re) t - 1‖ ≤
        1 / ((n : ℝ) + 1) :=
    exists_simultaneous_phase_recurrence (fun j => -(w j).re)
      (by positivity) ((n : ℝ) + 1)
  choose t ht hphase using hrec
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have htop : Tendsto t atTop atTop := tendsto_atTop_mono ht hnat
  have heps : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hnat
  have hchar (j : ι) :
      Tendsto (fun n => GaloisForLFunctions.bohrChar (-(w j).re) (t n))
        atTop (𝓝 1) := by
    apply tendsto_iff_dist_tendsto_zero.2
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun n => by simpa only [dist_eq_norm] using hphase n j) heps
  have hchar_eq (n : ℕ) (j : ι) :
      GaloisForLFunctions.bohrChar (-(w j).re) (t n) =
        Complex.exp ((t n * (w j).re : ℝ) * Complex.I) := by
    have ha : - (-(w j).re * t n) = t n * (w j).re := by ring
    rw [GaloisForLFunctions.bohrChar, ha]
  have hcos (j : ι) : Tendsto (fun n => Real.cos (t n * (w j).re)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, hchar_eq,
      Complex.exp_ofReal_mul_I_re, Complex.one_re] using
      (Complex.continuous_re.tendsto (1 : ℂ)).comp (hchar j)
  have hsin (j : ι) : Tendsto (fun n => Real.sin (t n * (w j).re)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hchar_eq,
      Complex.exp_ofReal_mul_I_im, Complex.one_im] using
      (Complex.continuous_im.tendsto (1 : ℂ)).comp (hchar j)
  have hexp : Tendsto (fun n => Real.exp (-2 * b * t n)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (htop.const_mul_atTop_of_neg (by linarith))
  have hatom (j : ι) : Tendsto (fun n => Real.exp (-b * t n) *
      (w j * Complex.sin ((t n : ℂ) * w j)).re) atTop (𝓝 (-b / 2)) := by
    simp_rw [liClockTopSineAtom_normalized_eq (w j) (hw j)]
    have h := (((hsin j).const_mul (w j).re).sub ((hcos j).const_mul b)).div_const 2
    have he := (hexp.mul ((((hsin j).const_mul (w j).re).add
      ((hcos j).const_mul b)))).div_const 2
    simpa using h.add he
  refine ⟨t, ht, htop, ?_⟩
  have hsum := tendsto_finsetSum Finset.univ (fun j _ => hatom j)
  have hc : (Fintype.card ι : ℝ) * (-b / 2) = -b * (Fintype.card ι : ℝ) / 2 := by ring
  simpa only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hc] using hsum

end RHTower
