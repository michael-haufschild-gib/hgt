import GaloisForLFunctions.HTGeometry.MultiPairLocalization
import GaloisForLFunctions.HTGeometry.BohrFiniteRecurrence

/-!
# The top layer of a nonnegative exponential polynomial

Group the exponents of a real exponential polynomial by their real part:

`F(t) = ∑_m e^{β_m t} T_m(t)`,  `β_1 < … < β_M`,

each `T_m` a real trigonometric polynomial with purely imaginary frequencies.  Dividing by
`e^{β_M t}` and letting `t → +∞` kills every layer but the top one, and the top layer is almost
periodic: a negative value of `T_M` recurs at arbitrarily large times.  So nonnegativity of `F` on a
half-line forces `T_M ≥ 0` everywhere — the top layer must itself be a nonnegative trigonometric
polynomial, hence a Fejér–Riesz square.

This makes precise, for the cone of exponential polynomials, the dominant-term principle familiar
from ultimate positivity of linear recurrences.  It is the necessary condition that the localization
of `MultiPairLocalization` leaves behind at `+∞`, and it is exactly what fails when a comparison
function is placed at a real part above every exponent of the compared sum.
-/

open Set Real

namespace GaloisForLFunctions.HTGeometry

/-- A layer: the real part of a finite sum of unimodular characters with prescribed weights. -/
noncomputable def bohrLayer {n : ℕ} (mm : Fin n → ℂ) (uu : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ j, mm j * Complex.exp (Complex.I * ((t : ℂ) * ((uu j : ℝ) : ℂ)))).re

theorem bohrLayer_shift {n : ℕ} (mm : Fin n → ℂ) (uu : Fin n → ℝ) (t₀ ξ : ℝ) :
    bohrLayer (fun j => mm j * Complex.exp (Complex.I * ((t₀ : ℂ) * ((uu j : ℝ) : ℂ)))) uu ξ
      = bohrLayer mm uu (t₀ + ξ) := by
  rw [bohrLayer, bohrLayer]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **Recurrence of the layer.**  A value of a layer recurs, to any tolerance, at arbitrarily large
times. -/
theorem exists_large_bohrLayer_near {n : ℕ} (mm : Fin n → ℂ) (uu : Fin n → ℝ) (t₀ : ℝ)
    {ε : ℝ} (hε : 0 < ε) (Rbound : ℝ) :
    ∃ s : ℝ, Rbound ≤ s ∧ |bohrLayer mm uu s - bohrLayer mm uu t₀| ≤ (∑ j, ‖mm j‖) * ε := by
  set mm' : Fin n → ℂ :=
    fun j => mm j * Complex.exp (Complex.I * ((t₀ : ℂ) * ((uu j : ℝ) : ℂ))) with hmm'
  have hnorm : ∀ j, ‖mm' j‖ = ‖mm j‖ := by
    intro j
    rw [hmm', norm_mul]
    have : ‖Complex.exp (Complex.I * ((t₀ : ℂ) * ((uu j : ℝ) : ℂ)))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [this, mul_one]
  obtain ⟨ξ, hξ, hbound⟩ :=
    GaloisForLFunctions.exists_large_atomicSymbol_revival uu mm' hε (Rbound - t₀)
  refine ⟨t₀ + ξ, by linarith, ?_⟩
  have hre : |((∑ j, mm' j * Complex.exp (Complex.I * ((ξ : ℂ) * ((uu j : ℝ) : ℂ)))) - ∑ j, mm' j).re|
      ≤ ‖(∑ j, mm' j * Complex.exp (Complex.I * ((ξ : ℂ) * ((uu j : ℝ) : ℂ)))) - ∑ j, mm' j‖ :=
    Complex.abs_re_le_norm _
  have hA : (∑ j, mm' j * Complex.exp (Complex.I * ((ξ : ℂ) * ((uu j : ℝ) : ℂ)))).re
      = bohrLayer mm uu (t₀ + ξ) := by
    rw [← bohrLayer_shift mm uu t₀ ξ]
    rfl
  have hB : (∑ j, mm' j).re = bohrLayer mm uu t₀ := rfl
  have hsum : (∑ j, ‖mm' j‖) = ∑ j, ‖mm j‖ := Finset.sum_congr rfl (fun j _ => hnorm j)
  rw [Complex.sub_re, hA, hB] at hre
  rw [hsum] at hbound
  linarith

/-- **The top layer of a nonnegative exponential polynomial is nonnegative.**  If `F` splits as a
top layer of rate `β` plus a remainder decaying by a fixed exponential factor, and `F ≥ 0`, then the
top layer is nonnegative at every point. -/
theorem bohrLayer_nonneg_of_nonneg {n : ℕ} (mm : Fin n → ℂ) (uu : Fin n → ℝ)
    {F G : ℝ → ℝ} {bM K delta : ℝ} (hdelta : 0 < delta) (hK : 0 ≤ K)
    (hF : ∀ t : ℝ, F t = Real.exp (bM * t) * bohrLayer mm uu t + G t)
    (hG : ∀ t : ℝ, |G t| ≤ K * Real.exp ((bM - delta) * t))
    (hnn : ∀ t : ℝ, 0 ≤ F t) :
    ∀ t : ℝ, 0 ≤ bohrLayer mm uu t := by
  intro t₀
  by_contra hcon
  push Not at hcon
  set cc : ℝ := -bohrLayer mm uu t₀ with hcc
  have hccpos : 0 < cc := by rw [hcc]; linarith
  set Msum : ℝ := ∑ j, ‖mm j‖ with hMsum
  have hMnn : 0 ≤ Msum := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  set ε : ℝ := cc / (2 * (Msum + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hsmall : Msum * ε < cc / 2 := by
    have hden : (0 : ℝ) < 2 * (Msum + 1) := by linarith
    rw [hε, ← mul_div_assoc, div_lt_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]
    nlinarith [hccpos, hMnn]
  set Kp : ℝ := K + 1 with hKp
  have hKppos : 0 < Kp := by rw [hKp]; linarith
  set S₀ : ℝ := Real.log (2 * Kp / cc) / delta with hS₀
  obtain ⟨s, hs, hnear⟩ := exists_large_bohrLayer_near mm uu t₀ hεpos (S₀ + 1)
  have hsS : S₀ < s := by linarith
  -- the layer is still strictly negative at the large time `s`
  have hlayer : bohrLayer mm uu s < -(cc / 2) := by
    have h2 : bohrLayer mm uu s - bohrLayer mm uu t₀ ≤ Msum * ε := (abs_le.mp hnear).2
    have h3 : bohrLayer mm uu t₀ = -cc := by rw [hcc]; ring
    rw [h3] at h2
    linarith [hsmall]
  -- the remainder is too small to repair it
  have hexp : Kp * Real.exp (-(delta * s)) < cc / 2 := by
    have hlog : Real.log (2 * Kp / cc) < delta * s := by
      rw [hS₀, div_lt_iff₀ hdelta] at hsS
      linarith
    have hpos : (0 : ℝ) < 2 * Kp / cc := by positivity
    have := Real.exp_lt_exp.mpr hlog
    rw [Real.exp_log hpos] at this
    have hE : (0 : ℝ) < Real.exp (delta * s) := Real.exp_pos _
    have hgt : Real.exp (-(delta * s)) < cc / (2 * Kp) := by
      rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2 * Kp), Real.exp_neg, inv_mul_eq_div,
        div_lt_iff₀ hE]
      have hmul := (div_lt_iff₀ hccpos).mp this
      linarith
    calc Kp * Real.exp (-(delta * s)) < Kp * (cc / (2 * Kp)) :=
          mul_lt_mul_of_pos_left hgt hKppos
      _ = cc / 2 := by field_simp
  have hGs : G s ≤ Kp * Real.exp (bM * s) * Real.exp (-(delta * s)) := by
    have h1 := (abs_le.mp (hG s)).2
    have h2 : K * Real.exp ((bM - delta) * s)
        ≤ Kp * Real.exp (bM * s) * Real.exp (-(delta * s)) := by
      have hrw : Kp * Real.exp (bM * s) * Real.exp (-(delta * s))
          = Kp * Real.exp ((bM - delta) * s) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      rw [hrw]
      have hKle : K ≤ Kp := by rw [hKp]; linarith
      exact mul_le_mul_of_nonneg_right hKle (Real.exp_pos _).le
    linarith
  have hFneg : F s < 0 := by
    rw [hF s]
    have hpos : (0 : ℝ) < Real.exp (bM * s) := Real.exp_pos _
    have h1 : Real.exp (bM * s) * bohrLayer mm uu s < Real.exp (bM * s) * -(cc / 2) :=
      mul_lt_mul_of_pos_left hlayer hpos
    have h2 : Kp * Real.exp (bM * s) * Real.exp (-(delta * s))
        < Real.exp (bM * s) * (cc / 2) := by
      have hml := mul_lt_mul_of_pos_left hexp hpos
      linarith [hml]
    linarith
  exact absurd (hnn s) (not_le.mpr hFneg)

end GaloisForLFunctions.HTGeometry
