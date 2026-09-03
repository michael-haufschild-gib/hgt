import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownWideIntervalHandoff
import GaloisForLFunctions.RHTower.Sieve.MellinDecayUniform

/-!
# Uniform Mellin majorant for wide-smoothed intervals

The smoothing width remains a parameter.  Its quadratic-decay cost is therefore
`H⁻² X^(sigma+2)` instead of the fixed half-width cost `X^(sigma+2)`.  For Menon's wide schedule
this leaves only a polylogarithmic factor over the unavoidable `X^sigma` Mellin mass.
-/

namespace RHTower.Sieve

open Complex GaloisForLFunctions.HTGeometry

noncomputable section

/-- Explicit common-width kernel majorant built from one absolute derivative constant. -/
def menonWideIntervalAmbientKernelMajorant
    (C0 : ℝ) (X : ℕ) (H sigma : ℝ) : ℝ :=
  let Z : ℝ := (X : ℝ) + 1
  let M0 : ℝ := Z ^ sigma / sigma
  let M2 : ℝ := C0 / H ^ 2 * Z ^ 2 * Z ^ sigma
  1 + 4 * (M0 + M2)

/-- One absolute derivative constant controls all common-width subinterval kernels whose two
transition windows fit below the enlarged cutoff `X`. -/
theorem exists_menonWideIntervalAmbientKernelMajorant :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ {X a b : ℕ} {H sigma : ℝ},
        1 ≤ a → a ≤ b → (b : ℝ) + H ≤ (X : ℝ) →
        0 < H → 0 < sigma →
        1 ≤ menonWideIntervalAmbientKernelMajorant C0 X H sigma ∧
        ∀ y : ℝ,
          ‖menonWideIntervalMellinKernel
              (a : ℝ) (b : ℝ) H sigma y‖ ≤
            menonWideIntervalAmbientKernelMajorant C0 X H sigma *
              (1 + y ^ 2)⁻¹ := by
  obtain ⟨C0, hC0, hdecay⟩ := exists_bound_mellin_smoothWeight_uniform_all 1
  refine ⟨C0, hC0, ?_⟩
  intro X a b H sigma ha hab hsupport hH hsigma
  let Z : ℝ := (X : ℝ) + 1
  let M0 : ℝ := Z ^ sigma / sigma
  let M2 : ℝ := C0 / H ^ 2 * Z ^ 2 * Z ^ sigma
  let C : ℝ := 1 + 4 * (M0 + M2)
  have hbPos : 0 < b := (Nat.zero_lt_of_lt ha).trans_le hab
  have hXpos : 0 < (X : ℝ) := by
    have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbPos
    linarith
  have hZ : 1 ≤ Z := by
    dsimp only [Z]
    linarith
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hM0 : 0 ≤ M0 := by
    dsimp only [M0]
    positivity
  have hM2 : 0 ≤ M2 := by
    dsimp only [M2]
    positivity
  have hsingle : ∀ N : ℕ, 1 ≤ N → N ≤ b → ∀ y : ℝ,
      ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight
          (N : ℝ) H x : ℝ) : ℂ))
        ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ ≤
          (2 * (M0 + M2)) * (1 + y ^ 2)⁻¹ := by
    intro N hN hNb y
    have hNR : 0 ≤ (N : ℝ) := by positivity
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
    have hNbR : (N : ℝ) ≤ (b : ℝ) := by exact_mod_cast hNb
    have hNX : (N : ℝ) + H ≤ (X : ℝ) := by linarith
    have hNZ : (N : ℝ) + H ≤ Z := by
      dsimp only [Z]
      linarith
    have hNZ' : (N : ℝ) + H + 1 ≤ Z := by
      dsimp only [Z]
      nlinarith
    have htrivRaw := norm_mellin_smoothWeight_le_pow hNR hH
      (s := ((sigma : ℂ) + (y : ℝ) * Complex.I)) (by simpa using hsigma)
    have hre : ((sigma : ℂ) + (y : ℝ) * Complex.I).re = sigma := by simp
    rw [hre] at htrivRaw
    have hpow0 : ((N : ℝ) + H) ^ sigma ≤ Z ^ sigma :=
      Real.rpow_le_rpow (by positivity) hNZ hsigma.le
    have htriv :
        ‖mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight
            (N : ℝ) H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ ≤ M0 := by
      dsimp only [M0]
      exact htrivRaw.trans (div_le_div_of_nonneg_right hpow0 hsigma.le)
    have hdecayRaw := hdecay (N : ℝ) H hNpos hH
      ((sigma : ℂ) + (y : ℝ) * Complex.I) (by simpa using hsigma)
    rw [hre] at hdecayRaw
    have him : ((sigma : ℂ) + (y : ℝ) * Complex.I).im = y := by simp
    have hdecayRaw' : |y| ^ 2 *
        ‖mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight
            (N : ℝ) H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ ≤
        C0 / H ^ (1 + 1) *
          ((N : ℝ) + H + 1) ^ (1 + 1 : ℕ) *
          ((N : ℝ) + H + 1) ^ sigma := by
      simpa only [him, Nat.reduceAdd] using hdecayRaw
    have hpow2 : ((N : ℝ) + H + 1) ^ (2 : ℕ) ≤ Z ^ 2 :=
      pow_le_pow_left₀ (by positivity) hNZ' 2
    have hpowSigma : ((N : ℝ) + H + 1) ^ sigma ≤ Z ^ sigma :=
      Real.rpow_le_rpow (by positivity) hNZ' hsigma.le
    have hdecayBound : C0 / H ^ (1 + 1) *
          ((N : ℝ) + H + 1) ^ (1 + 1 : ℕ) *
          ((N : ℝ) + H + 1) ^ sigma ≤ M2 := by
      dsimp only [M2]
      calc
        C0 / H ^ (1 + 1) *
              ((N : ℝ) + H + 1) ^ (1 + 1 : ℕ) *
              ((N : ℝ) + H + 1) ^ sigma =
            (C0 / H ^ 2) *
              (((N : ℝ) + H + 1) ^ 2 *
                ((N : ℝ) + H + 1) ^ sigma) := by norm_num; ring
        _ ≤ (C0 / H ^ 2) * (Z ^ 2 * Z ^ sigma) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hpow2 hpowSigma (by positivity) (by positivity)) (by positivity)
        _ = C0 / H ^ 2 * Z ^ 2 * Z ^ sigma := by ring
    have hdecay' : y ^ 2 *
        ‖mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight
            (N : ℝ) H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ ≤ M2 := by
      rw [← sq_abs]
      exact hdecayRaw'.trans hdecayBound
    have hden : 0 < 1 + y ^ 2 := by positivity
    apply (le_div_iff₀ hden).2
    by_cases hy : y ^ 2 ≤ 1
    · have hnorm := norm_nonneg (mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight
            (N : ℝ) H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * Complex.I))
      nlinarith
    · have hnorm := norm_nonneg (mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight
            (N : ℝ) H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * Complex.I))
      have hy' : 1 ≤ y ^ 2 := le_of_not_ge hy
      nlinarith
  refine ⟨?_, ?_⟩
  · change 1 ≤ 1 + 4 * (M0 + M2)
    nlinarith
  intro y
  have haBound := hsingle a ha hab y
  have hb : 1 ≤ b := ha.trans hab
  have hbBound := hsingle b hb le_rfl y
  have htri := norm_sub_le
    (mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight
        (b : ℝ) H x : ℝ) : ℂ))
      ((sigma : ℂ) + (y : ℝ) * Complex.I))
    (mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight
        (a : ℝ) H x : ℝ) : ℂ))
      ((sigma : ℂ) + (y : ℝ) * Complex.I))
  change ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight
          (b : ℝ) H x : ℝ) : ℂ))
        ((sigma : ℂ) + (y : ℝ) * Complex.I) -
      mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight
          (a : ℝ) H x : ℝ) : ℂ))
        ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ ≤ C * (1 + y ^ 2)⁻¹
  calc
    _ ≤ ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight
          (b : ℝ) H x : ℝ) : ℂ))
        ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ +
      ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight
          (a : ℝ) H x : ℝ) : ℂ))
        ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ := htri
    _ ≤ 2 * (M0 + M2) * (1 + y ^ 2)⁻¹ +
        2 * (M0 + M2) * (1 + y ^ 2)⁻¹ := add_le_add hbBound haBound
    _ = 4 * (M0 + M2) * (1 + y ^ 2)⁻¹ := by ring
    _ ≤ C * (1 + y ^ 2)⁻¹ := by
      apply mul_le_mul_of_nonneg_right
      · dsimp only [C]
        linarith
      · positivity

end

end RHTower.Sieve
