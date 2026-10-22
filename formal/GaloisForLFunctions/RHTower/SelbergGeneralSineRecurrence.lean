import GaloisForLFunctions.RHTower.CCM.CCMPrimePoleFiniteCoherence
import GaloisForLFunctions.HTGeometry.SineVerticalDecay
import GaloisForLFunctions.RHTower.SelbergFullShiftRootLaw

/-!
# General-rank recurrence of the Selberg asymmetric sine factor

Finite-dimensional simultaneous Diophantine recurrence supplies a cofinal sequence of shift
indices on which every sine factor stays above an explicit positive margin.  This discharges the
frequent-lower-bound premise in the cusp root law at every base point off its stated exceptional
lattice, with no rank-one or commensurability hypothesis.
-/

open Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

def SelbergGammaData.sineBaseArgument (G : SelbergGammaData) (s₀ : ℂ)
    (j : Fin G.rank) : ℂ :=
  (Real.pi : ℂ) * ((G.lambda j : ℂ) * s₀ + G.mu j)

def SelbergGammaData.sineShiftFrequency (G : SelbergGammaData)
    (j : Fin G.rank) : ℝ :=
  Real.pi * G.lambda j / G.degree

def SelbergGammaData.sineRecurrenceMargin (G : SelbergGammaData) (s₀ : ℂ)
    (j : Fin G.rank) : ℝ :=
  let z := G.sineBaseArgument s₀ j
  if z.im = 0 then |Real.sin z.re| / 2 else Real.sinh |z.im|

theorem SelbergGammaData.sineBaseArgument_sin_ne_zero
    (G : SelbergGammaData) (s₀ : ℂ) (hS : G.asymmetricS s₀ ≠ 0)
    (j : Fin G.rank) : Complex.sin (G.sineBaseArgument s₀ j) ≠ 0 := by
  have hprod : (∏ j, Complex.sin (G.sineBaseArgument s₀ j)) ≠ 0 := by
    intro hzero
    apply hS
    unfold SelbergGammaData.asymmetricS
    rw [show (∏ j, Complex.sin
      ((Real.pi : ℂ) * ((G.lambda j : ℂ) * s₀ + G.mu j))) = 0 by
        simpa only [SelbergGammaData.sineBaseArgument] using hzero,
      mul_zero]
  exact Finset.prod_ne_zero_iff.mp hprod j (Finset.mem_univ j)

theorem SelbergGammaData.sineRecurrenceMargin_pos
    (G : SelbergGammaData) (s₀ : ℂ) (hS : G.asymmetricS s₀ ≠ 0)
    (j : Fin G.rank) : 0 < G.sineRecurrenceMargin s₀ j := by
  let z := G.sineBaseArgument s₀ j
  have hsin : Complex.sin z ≠ 0 := G.sineBaseArgument_sin_ne_zero s₀ hS j
  unfold SelbergGammaData.sineRecurrenceMargin
  dsimp only [z]
  split_ifs with him
  · have hz : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    have hsreal : Real.sin z.re ≠ 0 := by
      intro hs
      apply hsin
      rw [hz, ← Complex.ofReal_sin, hs]
      norm_num
    exact div_pos (abs_pos.mpr hsreal) (by norm_num)
  · rw [Real.sinh_pos_iff]
    exact abs_pos.mpr him

theorem SelbergGammaData.sineShiftArgument_im
    (G : SelbergGammaData) (s₀ : ℂ) (k : ℕ) (j : Fin G.rank) :
    ((Real.pi : ℂ) * ((G.lambda j : ℂ) *
      (s₀ - (k : ℂ) / (G.degree : ℂ)) + G.mu j)).im =
      (G.sineBaseArgument s₀ j).im := by
  rw [G.sine_arg_im s₀ k j]
  unfold SelbergGammaData.sineBaseArgument
  simp [Complex.mul_im, Complex.mul_re]

theorem SelbergGammaData.sineShiftArgument_re
    (G : SelbergGammaData) (hd : 0 < G.degree) (s₀ : ℂ)
    (k : ℕ) (j : Fin G.rank) :
    ((Real.pi : ℂ) * ((G.lambda j : ℂ) *
      (s₀ - (k : ℂ) / (G.degree : ℂ)) + G.mu j)).re =
      (G.sineBaseArgument s₀ j).re - (k : ℝ) * G.sineShiftFrequency j := by
  have hdne : (G.degree : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  unfold SelbergGammaData.sineBaseArgument SelbergGammaData.sineShiftFrequency
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.add_re, Complex.sub_re, Complex.div_re, Complex.natCast_re,
    Complex.natCast_im, mul_zero, Complex.normSq_ofReal]
  field_simp
  ring

theorem SelbergGammaData.sineRecurrenceMargin_le_shift
    (G : SelbergGammaData) (hd : 0 < G.degree) (s₀ : ℂ)
    {k : ℕ} {r : Fin G.rank → ℤ} {ε : ℝ}
    (hε : ∀ j, ε ≤ G.sineRecurrenceMargin s₀ j)
    (hphase : ∀ j, |(k : ℝ) * G.sineShiftFrequency j - 2 * Real.pi * r j| ≤ ε)
    (j : Fin G.rank) :
    G.sineRecurrenceMargin s₀ j ≤
      ‖Complex.sin ((Real.pi : ℂ) * ((G.lambda j : ℂ) *
        (s₀ - (k : ℂ) / (G.degree : ℂ)) + G.mu j))‖ := by
  let z := G.sineBaseArgument s₀ j
  let w : ℂ := (Real.pi : ℂ) * ((G.lambda j : ℂ) *
    (s₀ - (k : ℂ) / (G.degree : ℂ)) + G.mu j)
  have hwim : w.im = z.im := G.sineShiftArgument_im s₀ k j
  by_cases him : z.im = 0
  · have hwim0 : w.im = 0 := hwim.trans him
    let e : ℝ := (k : ℝ) * G.sineShiftFrequency j - 2 * Real.pi * r j
    have hwre : w.re = z.re - (k : ℝ) * G.sineShiftFrequency j :=
      G.sineShiftArgument_re hd s₀ k j
    have hperiod : Real.sin w.re = Real.sin (z.re - e) := by
      have hsin := Real.sin_add_int_mul_two_pi (z.re - e) (-r j)
      have heq : (z.re - e) + ((-r j : ℤ) : ℝ) * (2 * Real.pi) =
          z.re - (k : ℝ) * G.sineShiftFrequency j := by
        dsimp only [e]
        push_cast
        ring
      rw [heq, ← hwre] at hsin
      exact hsin
    have hdiff : |Real.sin w.re - Real.sin z.re| ≤ ε := by
      calc
        |Real.sin w.re - Real.sin z.re| =
            |Real.sin (z.re - e) - Real.sin z.re| := by rw [hperiod]
        _ ≤ |(z.re - e) - z.re| := Real.abs_sin_sub_sin_le _ _
        _ = |-e| := by ring_nf
        _ = |e| := abs_neg e
        _ ≤ ε := by simpa only [e] using hphase j
    have hmargin : G.sineRecurrenceMargin s₀ j = |Real.sin z.re| / 2 := by
      simp only [SelbergGammaData.sineRecurrenceMargin, z, him, if_pos]
    have htri : |Real.sin z.re| ≤
        |Real.sin w.re - Real.sin z.re| + |Real.sin w.re| := by
      calc
        |Real.sin z.re| = |(Real.sin z.re - Real.sin w.re) + Real.sin w.re| := by
          congr 1
          ring
        _ ≤ |Real.sin z.re - Real.sin w.re| + |Real.sin w.re| := abs_add_le _ _
        _ = |Real.sin w.re - Real.sin z.re| + |Real.sin w.re| := by
          rw [abs_sub_comm]
    have hhalf : |Real.sin z.re| / 2 ≤ |Real.sin w.re| := by
      have hεj := hε j
      rw [hmargin] at hεj
      linarith
    rw [hmargin]
    exact hhalf.trans (abs_sin_re_le_norm_sin w)
  · have hsinh := sinh_abs_im_le_norm_sin w
    rw [hwim] at hsinh
    rw [show G.sineRecurrenceMargin s₀ j = Real.sinh |z.im| by
      simp [SelbergGammaData.sineRecurrenceMargin, z, him]]
    exact hsinh

def SelbergGammaData.sineRecurrenceTolerance (G : SelbergGammaData) (s₀ : ℂ) : ℝ :=
  ∏ j, min 1 (G.sineRecurrenceMargin s₀ j)

theorem SelbergGammaData.sineRecurrenceTolerance_pos
    (G : SelbergGammaData) (s₀ : ℂ) (hS : G.asymmetricS s₀ ≠ 0) :
    0 < G.sineRecurrenceTolerance s₀ := by
  unfold SelbergGammaData.sineRecurrenceTolerance
  exact Finset.prod_pos fun j _ ↦
    lt_min zero_lt_one (G.sineRecurrenceMargin_pos s₀ hS j)

theorem SelbergGammaData.sineRecurrenceTolerance_le_margin
    (G : SelbergGammaData) (s₀ : ℂ) (hS : G.asymmetricS s₀ ≠ 0)
    (j : Fin G.rank) :
    G.sineRecurrenceTolerance s₀ ≤ G.sineRecurrenceMargin s₀ j := by
  let f : Fin G.rank → ℝ := fun i ↦ min 1 (G.sineRecurrenceMargin s₀ i)
  have hfpos (i : Fin G.rank) : 0 < f i :=
    lt_min zero_lt_one (G.sineRecurrenceMargin_pos s₀ hS i)
  have herase : ∏ i ∈ Finset.univ.erase j, f i ≤ 1 :=
    Finset.prod_le_one (fun i _ ↦ (hfpos i).le) (fun i _ ↦ min_le_left _ _)
  have hsplit := Finset.prod_erase_mul Finset.univ f (Finset.mem_univ j)
  unfold SelbergGammaData.sineRecurrenceTolerance
  change (∏ i, f i) ≤ G.sineRecurrenceMargin s₀ j
  rw [← hsplit]
  calc
    (∏ i ∈ Finset.univ.erase j, f i) * f j ≤ 1 * f j :=
      mul_le_mul_of_nonneg_right herase (hfpos j).le
    _ = f j := one_mul _
    _ ≤ G.sineRecurrenceMargin s₀ j := min_le_right _ _

def SelbergGammaData.sineRecurrenceFloor (G : SelbergGammaData) (s₀ : ℂ) : ℝ :=
  2 ^ G.rank * ∏ j, G.sineRecurrenceMargin s₀ j

theorem SelbergGammaData.sineRecurrenceFloor_pos
    (G : SelbergGammaData) (s₀ : ℂ) (hS : G.asymmetricS s₀ ≠ 0) :
    0 < G.sineRecurrenceFloor s₀ := by
  unfold SelbergGammaData.sineRecurrenceFloor
  exact mul_pos (pow_pos (by norm_num) _)
    (Finset.prod_pos fun j _ ↦ G.sineRecurrenceMargin_pos s₀ hS j)

theorem SelbergGammaData.exists_frequently_sineRecurrenceFloor_le_norm_asymmetricS_shift
    (G : SelbergGammaData) (hd : 0 < G.degree) (s₀ : ℂ)
    (hS : G.asymmetricS s₀ ≠ 0) :
    ∃ᶠ k : ℕ in atTop,
      G.sineRecurrenceFloor s₀ ≤
        ‖G.asymmetricS (s₀ - (k : ℂ) / (G.degree : ℂ))‖ := by
  let ε := G.sineRecurrenceTolerance s₀
  have hε : 0 < ε := G.sineRecurrenceTolerance_pos s₀ hS
  obtain ⟨Q : ℕ, hQ⟩ := exists_nat_gt (2 * Real.pi / ε)
  have herror : 2 * Real.pi / (Q + 1 : ℝ) ≤ ε := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Q : ℝ) + 1)]
    have hQ' : 2 * Real.pi < ε * (Q : ℝ) := by
      rw [div_lt_iff₀ hε] at hQ
      nlinarith
    nlinarith
  rw [Filter.frequently_atTop]
  intro L
  obtain ⟨k, hL, -, r, hr⟩ :=
    exists_fin_simultaneous_two_pi_phase_approximation_delayed_quantitative
      (Q := Q) (L := L) G.sineShiftFrequency
  refine ⟨k, hL, ?_⟩
  have hfactor (j : Fin G.rank) :
      G.sineRecurrenceMargin s₀ j ≤
        ‖Complex.sin ((Real.pi : ℂ) * ((G.lambda j : ℂ) *
          (s₀ - (k : ℂ) / (G.degree : ℂ)) + G.mu j))‖ := by
    apply G.sineRecurrenceMargin_le_shift hd s₀
    · intro i
      exact G.sineRecurrenceTolerance_le_margin s₀ hS i
    · intro i
      exact (hr i).trans herror
  unfold SelbergGammaData.sineRecurrenceFloor SelbergGammaData.asymmetricS
  rw [norm_mul, norm_pow, norm_prod]
  have htwo : ‖(2 : ℂ)‖ ^ G.rank = (2 : ℝ) ^ G.rank := by norm_num
  rw [htwo]
  exact mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod (fun j _ ↦ (G.sineRecurrenceMargin_pos s₀ hS j).le)
      (fun j _ ↦ hfactor j)) (by positivity)

theorem SelbergGammaData.exists_frequently_le_norm_asymmetricS_shift_of_ne_zero
    (G : SelbergGammaData) (hd : 0 < G.degree) (s₀ : ℂ)
    (hS : G.asymmetricS s₀ ≠ 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ᶠ k : ℕ in atTop,
      c₀ ≤ ‖G.asymmetricS (s₀ - (k : ℂ) / (G.degree : ℂ))‖ :=
  ⟨G.sineRecurrenceFloor s₀, G.sineRecurrenceFloor_pos s₀ hS,
    G.exists_frequently_sineRecurrenceFloor_le_norm_asymmetricS_shift hd s₀ hS⟩

/-- General-rank cusp root law away from the sine exceptional lattice.  Finite-dimensional
simultaneous recurrence discharges the frequent sine lower-bound premise. -/
theorem ExtendedSelbergClass.limsup_norm_shift_rpow_inv_of_height_of_asymmetricS_ne_zero
    (F : ExtendedSelbergClass) (hd : 0 < F.gammaData.degree) {s₀ : ℂ}
    (ha1 : (F.coeff 1 : ℂ) ≠ 0)
    (hheight : F.gammaData.gammaTailHeight < |s₀.im|)
    (hS : F.gammaData.asymmetricS s₀ ≠ 0) :
    limsup (fun k : ℕ =>
        (‖F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ / (k.factorial : ℝ)) ^
          (1 / (k : ℝ))) atTop
      = F.gammaData.conductor ^ (1 / F.gammaData.degree)
        / (2 * Real.pi * F.gammaData.degree) := by
  obtain ⟨c₀, hc₀, hfreq⟩ :=
    F.gammaData.exists_frequently_le_norm_asymmetricS_shift_of_ne_zero hd s₀ hS
  exact F.limsup_norm_shift_rpow_inv_of_height hd ha1 hheight hc₀ hfreq

/-- Full-Selberg-class general-rank cusp root law away from the stated exceptional lattice.
Normalization discharges the first-coefficient premise, and recurrence constructs the sine
lower bound. -/
theorem SelbergClass.limsup_norm_shift_rpow_inv_of_height_of_asymmetricS_ne_zero
    (F : SelbergClass) (hd : 0 < F.gammaData.degree) {s₀ : ℂ}
    (hheight : F.gammaData.gammaTailHeight < |s₀.im|)
    (hS : F.gammaData.asymmetricS s₀ ≠ 0) :
    limsup (fun k : ℕ =>
        (‖F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ / (k.factorial : ℝ)) ^
          (1 / (k : ℝ))) atTop
      = F.gammaData.conductor ^ (1 / F.gammaData.degree)
        / (2 * Real.pi * F.gammaData.degree) := by
  have ha1 : (F.toExtendedSelbergClass.coeff 1 : ℂ) ≠ 0 := by
    rw [F.coeff_one]
    exact one_ne_zero
  exact F.toExtendedSelbergClass.limsup_norm_shift_rpow_inv_of_height_of_asymmetricS_ne_zero
    hd ha1 hheight hS

end

end RHTower
