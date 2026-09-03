import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCaseIIExplicitAggregate
import GaloisForLFunctions.RHTower.Sieve.MellinDecayUniform

/-!
# Uniform Mellin kernel for Menon's variable sharp endpoints

Reverse Abel selects a different upper endpoint at each exceptional frequency.  This theorem gives
one ambient-scale quadratic Mellin majorant for every endpoint in the source interval, so no
endpoint coloring or endpoint-cardinality loss is introduced.
-/

namespace RHTower.Sieve

open Complex GaloisForLFunctions.HTGeometry

noncomputable section

/-- One absolute derivative constant yields an explicit quadratic-decay majorant, uniform over
all sharp intervals `(a,b]` contained in `[1,X]`. -/
theorem exists_menonSharpIntervalUniformKernelMajorant :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ {X a b : ℕ} {sigma : ℝ},
        1 ≤ a → a ≤ b → b ≤ X → 0 < sigma →
        let Z : ℝ := (X : ℝ) + 2
        let M0 : ℝ := Z ^ sigma / sigma
        let M2 : ℝ := 4 * C0 * Z ^ 2 * Z ^ sigma
        let C : ℝ := 1 + 4 * (M0 + M2)
        1 ≤ C ∧ ∀ y : ℝ,
          ‖menonSharpIntervalMellinKernel (a : ℝ) (b : ℝ) sigma y‖ ≤
            C * (1 + y ^ 2)⁻¹ := by
  obtain ⟨C0, hC0, hdecay⟩ := exists_bound_mellin_smoothWeight_uniform_all 1
  refine ⟨C0, hC0, ?_⟩
  intro X a b sigma ha hab hbX hsigma
  let Z : ℝ := (X : ℝ) + 2
  let M0 : ℝ := Z ^ sigma / sigma
  let M2 : ℝ := 4 * C0 * Z ^ 2 * Z ^ sigma
  let C : ℝ := 1 + 4 * (M0 + M2)
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
  have hsingle : ∀ N : ℕ, 1 ≤ N → N ≤ X → ∀ y : ℝ,
      ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight
          (N : ℝ) (1 / 2 : ℝ) x : ℝ) : ℂ))
        ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ ≤
          (2 * (M0 + M2)) * (1 + y ^ 2)⁻¹ := by
    intro N hN hNX y
    have hNR : 0 ≤ (N : ℝ) := by positivity
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
    have hNXR : (N : ℝ) ≤ (X : ℝ) := by exact_mod_cast hNX
    have hNZ : (N : ℝ) + (1 / 2 : ℝ) ≤ Z := by
      dsimp only [Z]
      linarith
    have hNZ' : (N : ℝ) + (1 / 2 : ℝ) + 1 ≤ Z := by
      dsimp only [Z]
      linarith
    have htrivRaw := norm_mellin_smoothWeight_le_pow hNR
      (by norm_num : (0 : ℝ) < 1 / 2)
      (s := ((sigma : ℂ) + (y : ℝ) * Complex.I)) (by simpa using hsigma)
    have hre : ((sigma : ℂ) + (y : ℝ) * Complex.I).re = sigma := by simp
    rw [hre] at htrivRaw
    have hpow0 : ((N : ℝ) + (1 / 2 : ℝ)) ^ sigma ≤ Z ^ sigma :=
      Real.rpow_le_rpow (by positivity) hNZ hsigma.le
    have htriv :
        ‖mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight
            (N : ℝ) (1 / 2 : ℝ) x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ ≤ M0 := by
      dsimp only [M0]
      exact htrivRaw.trans (div_le_div_of_nonneg_right hpow0 hsigma.le)
    have hdecayRaw := hdecay (N : ℝ) (1 / 2 : ℝ) hNpos (by norm_num)
      ((sigma : ℂ) + (y : ℝ) * Complex.I) (by simpa using hsigma)
    rw [hre] at hdecayRaw
    have him : ((sigma : ℂ) + (y : ℝ) * Complex.I).im = y := by simp
    have hdecayRaw' : |y| ^ 2 *
        ‖mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight
            (N : ℝ) (1 / 2 : ℝ) x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ ≤
        C0 / (1 / 2 : ℝ) ^ (1 + 1) *
          ((N : ℝ) + (1 / 2 : ℝ) + 1) ^ (1 + 1 : ℕ) *
          ((N : ℝ) + (1 / 2 : ℝ) + 1) ^ sigma := by
      simpa only [him, Nat.reduceAdd] using hdecayRaw
    have hpow2 : ((N : ℝ) + (1 / 2 : ℝ) + 1) ^ (2 : ℕ) ≤ Z ^ 2 :=
      pow_le_pow_left₀ (by positivity) hNZ' 2
    have hpowSigma : ((N : ℝ) + (1 / 2 : ℝ) + 1) ^ sigma ≤ Z ^ sigma :=
      Real.rpow_le_rpow (by positivity) hNZ' hsigma.le
    have hdecayBound : C0 / (1 / 2 : ℝ) ^ (1 + 1) *
          ((N : ℝ) + (1 / 2 : ℝ) + 1) ^ (1 + 1 : ℕ) *
          ((N : ℝ) + (1 / 2 : ℝ) + 1) ^ sigma ≤ M2 := by
      dsimp only [M2]
      calc
        C0 / (1 / 2 : ℝ) ^ (1 + 1) *
              ((N : ℝ) + (1 / 2 : ℝ) + 1) ^ (1 + 1 : ℕ) *
              ((N : ℝ) + (1 / 2 : ℝ) + 1) ^ sigma =
            4 * C0 * (((N : ℝ) + (1 / 2 : ℝ) + 1) ^ 2 *
              ((N : ℝ) + (1 / 2 : ℝ) + 1) ^ sigma) := by norm_num; ring
        _ ≤ 4 * C0 * (Z ^ 2 * Z ^ sigma) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hpow2 hpowSigma (by positivity) (by positivity)) (by positivity)
        _ = 4 * C0 * Z ^ 2 * Z ^ sigma := by ring
    have hdecay' : y ^ 2 *
        ‖mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight
            (N : ℝ) (1 / 2 : ℝ) x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ ≤ M2 := by
      rw [← sq_abs]
      exact hdecayRaw'.trans hdecayBound
    have hden : 0 < 1 + y ^ 2 := by positivity
    apply (le_div_iff₀ hden).2
    rw [div_eq_mul_inv]
    by_cases hy : y ^ 2 ≤ 1
    · have hnorm := norm_nonneg (mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight
            (N : ℝ) (1 / 2 : ℝ) x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * Complex.I))
      nlinarith
    · have hnorm := norm_nonneg (mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight
            (N : ℝ) (1 / 2 : ℝ) x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * Complex.I))
      have hy' : 1 ≤ y ^ 2 := le_of_not_ge hy
      nlinarith
  refine ⟨?_, ?_⟩
  · change 1 ≤ 1 + 4 * (M0 + M2)
    nlinarith
  intro y
  have haX : a ≤ X := hab.trans hbX
  have hb : 1 ≤ b := ha.trans hab
  have haBound := hsingle a ha haX y
  have hbBound := hsingle b hb hbX y
  have htri := norm_sub_le
    (mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight
        (b : ℝ) (1 / 2 : ℝ) x : ℝ) : ℂ))
      ((sigma : ℂ) + (y : ℝ) * Complex.I))
    (mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight
        (a : ℝ) (1 / 2 : ℝ) x : ℝ) : ℂ))
      ((sigma : ℂ) + (y : ℝ) * Complex.I))
  change ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight
          (b : ℝ) (1 / 2 : ℝ) x : ℝ) : ℂ))
        ((sigma : ℂ) + (y : ℝ) * Complex.I) -
      mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight
          (a : ℝ) (1 / 2 : ℝ) x : ℝ) : ℂ))
        ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ ≤ C * (1 + y ^ 2)⁻¹
  calc
    _ ≤ ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight
          (b : ℝ) (1 / 2 : ℝ) x : ℝ) : ℂ))
        ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ +
      ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight
          (a : ℝ) (1 / 2 : ℝ) x : ℝ) : ℂ))
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
