import GaloisForLFunctions.RHTower.Sieve.KuzminLandau

/-!
# Exact cotangent transport of chronological phase prefixes

Finite summation by parts with the corpus's Kuzmin–Landau coefficient retains a signed
`1 - cos` cost. Arbitrary phase increments and real weights are allowed in the exact identity:
resonant samples survive as a separate finite sum. Decreasing increments in `(0, 1)` give
nonpositive unweighted defect, strictly negative after two samples when the decrease is strict.

The cutoff `M` means `M + 1` samples, with terminal phase at `M + 1`; the interior cost has
`M` terms. Power weights introduce a sine drift and a product-cotangent drift. This module
proves no sign for those weighted terms and assumes no statement about zeta zeros.
-/

set_option autoImplicit false

open scoped BigOperators
open Complex Real
namespace RHTower.PhaseCotangent
noncomputable section

/-- Unit complex sample of a real phase measured in turns. -/
def phaseUnit (φ : ℕ → ℝ) (j : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * φ j : ℝ) : ℂ) * Complex.I)

/-- Real cotangent coefficient of one phase increment, including Lean's value at a pole. -/
def chordCotangent (φ : ℕ → ℝ) (j : ℕ) : ℝ :=
  Real.cos (Real.pi * (φ (j+1) - φ j)) / Real.sin (Real.pi * (φ (j+1) - φ j))

/-- Weighted imaginary prefix with its exact terminal phase correction. -/
def weightedPhaseDefect (φ w : ℕ → ℝ) (M : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (M+1), w j * Real.sin (2 * Real.pi * φ j)) +
    w M * Real.sin (2 * Real.pi * φ (M+1)) / 2 -
    w M * chordCotangent φ M * (1 - Real.cos (2 * Real.pi * φ (M+1))) / 2

/-- Unweighted corrected prefix through sample `M`. -/
def phaseDefect (φ : ℕ → ℝ) (M : ℕ) : ℝ := weightedPhaseDefect φ (fun _ => 1) M

/-- Real part of the literal unit phase. -/
theorem phaseUnit_re (φ : ℕ → ℝ) (j : ℕ) :
    (phaseUnit φ j).re = Real.cos (2 * Real.pi * φ j) := by
  rw [phaseUnit, Complex.exp_re]
  simp

/-- Imaginary part of the literal unit phase. -/
theorem phaseUnit_im (φ : ℕ → ℝ) (j : ℕ) :
    (phaseUnit φ j).im = Real.sin (2 * Real.pi * φ j) := by
  rw [phaseUnit, Complex.exp_im]
  simp

/-- The inverse-chord formula in every nonresonant winding band. -/
theorem klCoeff_mul_of_sin_ne_zero {β : ℝ} (hs : Real.sin (Real.pi * β) ≠ 0) :
    RHTower.Sieve.klCoeff β * (Complex.exp (((2 * Real.pi * β : ℝ) : ℂ) * Complex.I) - 1) = 1 := by
  set S : ℂ := ((Real.sin (Real.pi * β) : ℝ) : ℂ) with hSdef
  set C : ℂ := ((Real.cos (Real.pi * β) : ℝ) : ℂ) with hCdef
  have hSne : S ≠ 0 := by
    rw [hSdef]
    exact_mod_cast hs
  have hklc : RHTower.Sieve.klCoeff β = -(1/2 : ℂ) - Complex.I / 2 * (C / S) := by
    rw [RHTower.Sieve.klCoeff, Complex.ofReal_div, hSdef, hCdef]
  have hexp : Complex.exp (((2 * Real.pi * β : ℝ) : ℂ) * Complex.I)
      = ((Real.cos (2 * Real.pi * β) : ℝ) : ℂ)
        + ((Real.sin (2 * Real.pi * β) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hc2 : Real.cos (2 * Real.pi * β) = 1 - 2 * Real.sin (Real.pi * β) ^ 2 := by
    have h := Real.cos_two_mul' (Real.pi * β)
    rw [show 2 * (Real.pi * β) = 2 * Real.pi * β by ring] at h
    linarith [Real.sin_sq_add_cos_sq (Real.pi * β)]
  have hs2 : Real.sin (2 * Real.pi * β)
      = 2 * Real.sin (Real.pi * β) * Real.cos (Real.pi * β) := by
    have h := Real.sin_two_mul (Real.pi * β)
    rw [show 2 * (Real.pi * β) = 2 * Real.pi * β by ring] at h
    exact h
  have hfact : Complex.exp (((2 * Real.pi * β : ℝ) : ℂ) * Complex.I) - 1
      = 2 * S * (-S + C * Complex.I) := by
    rw [hexp, hc2, hs2]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_one, Complex.ofReal_ofNat, hSdef, hCdef]
    ring_nf
  have hpy : S ^ 2 + C ^ 2 = 1 := by
    rw [hSdef, hCdef]
    exact_mod_cast Real.sin_sq_add_cos_sq (Real.pi * β)
  rw [hklc, hfact]
  have hexpand : (-(1/2 : ℂ) - Complex.I / 2 * (C / S)) * (2 * S * (-S + C * Complex.I))
      = S ^ 2 - Complex.I ^ 2 * C ^ 2 := by
    field_simp
    ring
  rw [hexpand]
  linear_combination (-(C ^ 2)) * Complex.I_sq + hpy

/-- A resonant increment leaves the unit phase unchanged. -/
theorem phaseChord_eq_one_of_sin_eq_zero {β : ℝ} (hs : Real.sin (Real.pi * β) = 0) :
    Complex.exp (((2 * Real.pi * β : ℝ) : ℂ) * Complex.I) = 1 := by
  have hc : Real.cos (2 * Real.pi * β) = 1 := by
    rw [show 2 * Real.pi * β = 2 * (Real.pi * β) by ring, Real.cos_two_mul', hs]
    norm_num
    exact Real.sin_eq_zero_iff_cos_eq.mp hs
  have hsin : Real.sin (2 * Real.pi * β) = 0 := by
    rw [show 2 * Real.pi * β = 2 * (Real.pi * β) by ring, Real.sin_two_mul, hs]
    ring
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hsin]
  simp

/-- Exact nonresonant phase transport across one chronological step. -/
theorem phaseUnit_step {φ : ℕ → ℝ} {j : ℕ}
    (hs : Real.sin (Real.pi * (φ (j+1) - φ j)) ≠ 0) :
    phaseUnit φ j = RHTower.Sieve.klCoeff (φ (j+1) - φ j) *
      (phaseUnit φ (j+1) - phaseUnit φ j) := by
  have hshift : phaseUnit φ (j+1) = phaseUnit φ j *
      Complex.exp (((2 * Real.pi * (φ (j+1) - φ j) : ℝ) : ℂ) * Complex.I) := by
    rw [phaseUnit, phaseUnit, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hk := klCoeff_mul_of_sin_ne_zero hs
  rw [hshift]
  calc
    phaseUnit φ j = phaseUnit φ j * (RHTower.Sieve.klCoeff (φ (j+1) - φ j) *
      (Complex.exp (((2 * Real.pi * (φ (j+1) - φ j) : ℝ) : ℂ) * Complex.I) - 1)) := by
        rw [hk, mul_one]
    _ = _ := by ring

/-- Samples lost by chord inversion are retained explicitly at every resonant increment. -/
def resonantPhasePrefix (φ w : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (M+1),
    if Real.sin (Real.pi * (φ (j+1) - φ j)) = 0 then
      w j * Real.sin (2 * Real.pi * φ j) else 0

/-- Universal phase transport, including the full original sample at resonance. -/
theorem phaseUnit_step_with_resonance (φ : ℕ → ℝ) (j : ℕ) :
    phaseUnit φ j = RHTower.Sieve.klCoeff (φ (j+1) - φ j) *
      (phaseUnit φ (j+1) - phaseUnit φ j) +
      if Real.sin (Real.pi * (φ (j+1) - φ j)) = 0 then phaseUnit φ j else 0 := by
  by_cases hs : Real.sin (Real.pi * (φ (j+1) - φ j)) = 0
  · have he : phaseUnit φ (j+1) = phaseUnit φ j := by
      have hshift : phaseUnit φ (j+1) = phaseUnit φ j *
          Complex.exp (((2 * Real.pi * (φ (j+1) - φ j) : ℝ) : ℂ) * Complex.I) := by
        rw [phaseUnit, phaseUnit, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [hshift, phaseChord_eq_one_of_sin_eq_zero hs, mul_one]
    simp [hs, he]
  · simpa [hs] using phaseUnit_step hs

/-- Exact weighted decomposition with every drift, endpoint, and resonant sample retained. -/
theorem weightedPhaseDefect_eq {φ : ℕ → ℝ} (w : ℕ → ℝ) (M : ℕ)
    (hφ : φ 0 = 0) :
    weightedPhaseDefect φ w M =
      (∑ j ∈ Finset.range M,
        ((w (j+1) - w j) * Real.sin (2 * Real.pi * φ (j+1)) / 2 -
        (w (j+1) * chordCotangent φ (j+1) - w j * chordCotangent φ j) *
          (1 - Real.cos (2 * Real.pi * φ (j+1))) / 2)) + resonantPhasePrefix φ w M := by
  let E := phaseUnit φ
  let c : ℕ → ℂ := fun j => (w j : ℂ) * RHTower.Sieve.klCoeff (φ (j+1) - φ j)
  let r : ℕ → ℂ := fun j =>
    if Real.sin (Real.pi * (φ (j+1) - φ j)) = 0 then (w j : ℂ) * E j else 0
  have he0 : E 0 = 1 := by simp [E, phaseUnit, hφ]
  have hstep : ∀ j ∈ Finset.range (M+1),
      (w j : ℂ) * E j = c j * (E (j+1) - E j) + r j := by
    intro j hj
    have he := congrArg (fun z : ℂ => (w j : ℂ) * z) (phaseUnit_step_with_resonance φ j)
    dsimp only [c, r, E]
    simpa only [mul_add, mul_ite, mul_zero, mul_assoc] using he
  have hs := Finset.sum_range_by_parts c (fun j => E (j+1) - E j) (M+1)
  simp only [smul_eq_mul, Nat.add_sub_cancel, Finset.sum_range_sub] at hs
  have he : ∑ j ∈ Finset.range (M+1), (w j : ℂ) * E j =
      c M * (E (M+1) - 1) -
        (∑ j ∈ Finset.range M, (c (j+1) - c j) * (E (j+1) - 1)) +
        ∑ j ∈ Finset.range (M+1), r j := by
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, hs, he0]
  have hcre (j : ℕ) : (c j).re = -(w j) / 2 := by
    change ((w j : ℂ) * (-(1/2:ℂ) - Complex.I/2 * (chordCotangent φ j : ℂ))).re = _
    generalize chordCotangent φ j = q
    simp
    ring
  have hcim (j : ℕ) : (c j).im = -(w j * chordCotangent φ j) / 2 := by
    change ((w j : ℂ) * (-(1/2:ℂ) - Complex.I/2 * (chordCotangent φ j : ℂ))).im = _
    generalize chordCotangent φ j = q
    simp
    ring
  have hei (j : ℕ) : (E j).im = Real.sin (2 * Real.pi * φ j) := phaseUnit_im φ j
  have her (j : ℕ) : (E j).re = Real.cos (2 * Real.pi * φ j) := phaseUnit_re φ j
  have hrim (j : ℕ) : (r j).im =
      if Real.sin (Real.pi * (φ (j+1) - φ j)) = 0 then
        w j * Real.sin (2 * Real.pi * φ j) else 0 := by
    dsimp only [r]
    split_ifs <;> simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, Complex.zero_im, hei]
  have hi := congrArg Complex.im he
  simp only [Complex.im_sum, Complex.add_im, hrim, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.sub_im, Complex.sub_re, Complex.one_im, Complex.one_re,
    sub_zero, hcre, hcim, hei, her] at hi
  have hsum : (∑ j ∈ Finset.range M,
      ((-(w (j+1)) / 2 - -(w j) / 2) * Real.sin (2 * Real.pi * φ (j+1)) +
      (-(w (j+1) * chordCotangent φ (j+1)) / 2 - -(w j * chordCotangent φ j) / 2) *
        (Real.cos (2 * Real.pi * φ (j+1)) - 1))) =
      -(∑ j ∈ Finset.range M,
        ((w (j+1) - w j) * Real.sin (2 * Real.pi * φ (j+1)) / 2 -
        (w (j+1) * chordCotangent φ (j+1) - w j * chordCotangent φ j) *
          (1 - Real.cos (2 * Real.pi * φ (j+1))) / 2)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum] at hi
  dsimp only [weightedPhaseDefect, resonantPhasePrefix]
  linarith

/-- In the first winding band the unweighted defect is the negative cotangent cost. -/
theorem phaseDefect_eq {φ : ℕ → ℝ} (M : ℕ)
    (hφ : φ 0 = 0) (h0 : ∀ j ≤ M, 0 < φ (j+1) - φ j)
    (h1 : ∀ j ≤ M, φ (j+1) - φ j < 1) :
    phaseDefect φ M = -(∑ j ∈ Finset.range M,
      ((chordCotangent φ (j+1) - chordCotangent φ j) *
        (1 - Real.cos (2 * Real.pi * φ (j+1))) / 2)) := by
  have hr : resonantPhasePrefix φ (fun _ => 1) M = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjM : j ≤ M := by simpa using Finset.mem_range.mp hj
    rw [if_neg (ne_of_gt (RHTower.Sieve.sin_pi_mul_pos (h0 j hjM) (h1 j hjM)))]
  simpa [phaseDefect, hr] using weightedPhaseDefect_eq (φ := φ) (fun _ => 1) M hφ

/-- Cotangent strictly decreases as a phase increment increases within `(0, 1)`. -/
theorem cotangent_strictAnti {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    Real.cos (Real.pi * y) / Real.sin (Real.pi * y) <
      Real.cos (Real.pi * x) / Real.sin (Real.pi * x) := by
  have hsy := RHTower.Sieve.sin_pi_mul_pos (lt_trans hx hxy) hy
  have hsx := RHTower.Sieve.sin_pi_mul_pos hx (lt_trans hxy hy)
  have hd : 0 < Real.sin (Real.pi * y - Real.pi * x) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  rw [Real.sin_sub] at hd
  rw [div_lt_div_iff₀ hsy hsx]
  nlinarith

/-- Decreasing first-band increments orient every finite corrected unweighted prefix. -/
theorem phaseDefect_nonpos {φ : ℕ → ℝ} (M : ℕ)
    (hφ : φ 0 = 0) (h0 : ∀ j ≤ M, 0 < φ (j+1) - φ j)
    (h1 : ∀ j ≤ M, φ (j+1) - φ j < 1)
    (hanti : ∀ j < M, φ (j+2) - φ (j+1) ≤ φ (j+1) - φ j) :
    phaseDefect φ M ≤ 0 := by
  rw [phaseDefect_eq M hφ h0 h1]
  apply neg_nonpos.mpr
  apply Finset.sum_nonneg
  intro j hj
  have hjM := Finset.mem_range.mp hj
  have hq : 0 ≤ chordCotangent φ (j+1) - chordCotangent φ j := by
    rcases eq_or_lt_of_le (hanti j hjM) with he | he
    · simp only [chordCotangent, show j+1+1=j+2 by omega, he, sub_self, le_refl]
    · exact sub_nonneg.mpr (le_of_lt (cotangent_strictAnti (h0 (j+1) (by omega)) he
        (h1 j (by omega))))
  exact div_nonneg (mul_nonneg hq (sub_nonneg.mpr (Real.cos_le_one _))) (by norm_num)

/-- Strictly decreasing first-band increments give strict orientation after two samples. -/
theorem phaseDefect_neg {φ : ℕ → ℝ} {M : ℕ} (hM : 0 < M)
    (hφ : φ 0 = 0) (h0 : ∀ j ≤ M, 0 < φ (j+1) - φ j)
    (h1 : ∀ j ≤ M, φ (j+1) - φ j < 1)
    (hanti : ∀ j < M, φ (j+2) - φ (j+1) < φ (j+1) - φ j) :
    phaseDefect φ M < 0 := by
  rw [phaseDefect_eq M hφ h0 h1]
  apply neg_neg_of_pos
  apply Finset.sum_pos'
  · intro j hj
    have hjM := Finset.mem_range.mp hj
    have hq : 0 < chordCotangent φ (j+1) - chordCotangent φ j :=
      sub_pos.mpr (cotangent_strictAnti (h0 (j+1) (by omega)) (hanti j hjM) (h1 j (by omega)))
    exact div_nonneg (mul_nonneg hq.le (sub_nonneg.mpr (Real.cos_le_one _))) (by norm_num)
  · refine ⟨0, Finset.mem_range.mpr hM, ?_⟩
    have hq : 0 < chordCotangent φ 1 - chordCotangent φ 0 :=
      sub_pos.mpr (cotangent_strictAnti (h0 1 (by omega)) (hanti 0 hM) (h1 0 (by omega)))
    have hφ1 : 0 < φ 1 ∧ φ 1 < 1 := by simpa [hφ] using And.intro (h0 0 (by omega)) (h1 0 (by omega))
    have hcos : Real.cos (2 * Real.pi * φ 1) < 1 := by
      apply lt_of_le_of_ne (Real.cos_le_one _)
      intro he
      have hx : -(2 * Real.pi) < 2 * Real.pi * φ 1 := by nlinarith [Real.pi_pos]
      have hy : 2 * Real.pi * φ 1 < 2 * Real.pi := by nlinarith [Real.pi_pos]
      have hz := (Real.cos_eq_one_iff_of_lt_of_lt hx hy).mp he
      nlinarith [Real.pi_pos]
    simpa using div_pos (mul_pos hq (sub_pos.mpr hcos)) (by norm_num : (0:ℝ)<2)


/-- The unweighted cost identity across arbitrary winding bands, retaining resonances. -/
theorem phaseDefect_eq_with_resonance {φ : ℕ → ℝ} (M : ℕ) (hφ : φ 0 = 0) :
    phaseDefect φ M = -(∑ j ∈ Finset.range M,
      ((chordCotangent φ (j+1) - chordCotangent φ j) *
        (1 - Real.cos (2 * Real.pi * φ (j+1))) / 2)) +
      resonantPhasePrefix φ (fun _ => 1) M := by
  simpa [phaseDefect] using weightedPhaseDefect_eq (φ := φ) (fun _ => 1) M hφ

/-- Exact change of the unweighted defect when the next increment is nonresonant. -/
theorem phaseDefect_step {φ : ℕ → ℝ} (M : ℕ) (hφ : φ 0 = 0)
    (hs : Real.sin (Real.pi * (φ (M+2) - φ (M+1))) ≠ 0) :
    phaseDefect φ (M+1) = phaseDefect φ M -
      (chordCotangent φ (M+1) - chordCotangent φ M) *
        (1 - Real.cos (2 * Real.pi * φ (M+1))) / 2 := by
  rw [phaseDefect_eq_with_resonance (M+1) hφ, phaseDefect_eq_with_resonance M hφ]
  simp only [resonantPhasePrefix, Finset.sum_range_succ, one_mul]
  simp only [show M+1+1=M+2 by omega, if_neg hs]
  ring

end
end RHTower.PhaseCotangent
