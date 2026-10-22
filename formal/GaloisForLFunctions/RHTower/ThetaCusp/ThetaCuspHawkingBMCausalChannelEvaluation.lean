import Mathlib

/-!
# Birmingham--Mokhtari causal channel evaluation

For the exact `d = 4`, `M = 0` gravitational spectrum, write the angular square root as `chi` and
the two branch frequencies as

`omega₊(n) = chi - I * (2n + 3/2)`,

`omega₋(k) = -chi - I * (2k + 3/2)`.

Time-translation invariance fixes the frequencies of the quadratic and cubic Einstein sources.
The mixed quadratic source is an exact odd Hawking--Matsubara harmonic. Its hypergeometric horizon
parameter `c` is a negative integer, so this channel is a Frobenius-resonant boundary problem.
The reciprocal-Jost factors below are only radial denominator factors; they do not include the
logarithmic horizon normalization, angular source projection, metric reconstruction, or stationary
charge completion required by the full causal response.

At the local `++-` frequency, the plus connection parameter is a negative half-integer. Hence the
same-angular-fibre Jost determinant is nonzero and the local third Einstein jet does not lie at a
Birmingham--Mokhtari QNM pole. This excludes a coincident source pole, but not causal excitation of
another QNM: half-line turn-on and retarded Green tails evaluate the source transform away from its
natural frequency. Full residues therefore still require the causal convolution of all three
channels.
-/

open Complex

namespace RHTower

noncomputable section

/-- Universal decay offset of a `d = 4` Birmingham--Mokhtari gravitational overtone. -/
def d4BMCausalDecay (n : ℕ) : ℂ :=
  2 * n + 3 / 2

/-- Positive Birmingham--Mokhtari branch in angular-square-root normal form. -/
def d4BMCausalQNMPlus (n : ℕ) (chi : ℂ) : ℂ :=
  chi - Complex.I * d4BMCausalDecay n

/-- Negative Birmingham--Mokhtari branch in angular-square-root normal form. -/
def d4BMCausalQNMMinus (n : ℕ) (chi : ℂ) : ℂ :=
  -chi - Complex.I * d4BMCausalDecay n

/-- Frequency of the quadratic `++` source. -/
def d4BMCausalPlusPlusFrequency (n : ℕ) (chi : ℂ) : ℂ :=
  2 * d4BMCausalQNMPlus n chi

/-- Frequency of the quadratic `+-` source. -/
def d4BMCausalPlusMinusFrequency (n k : ℕ) (chi : ℂ) : ℂ :=
  d4BMCausalQNMPlus n chi + d4BMCausalQNMMinus k chi

/-- Frequency of the local cubic `++-` source. -/
def d4BMCausalPlusPlusMinusFrequency (n k : ℕ) (chi : ℂ) : ℂ :=
  2 * d4BMCausalQNMPlus n chi + d4BMCausalQNMMinus k chi

/-- Birmingham--Mokhtari plus connection exponent. -/
def d4BMCausalRadialA (omega chi : ℂ) : ℂ :=
  3 / 4 - Complex.I * (omega - chi) / 2

/-- Birmingham--Mokhtari minus connection exponent. -/
def d4BMCausalRadialB (omega chi : ℂ) : ℂ :=
  3 / 4 - Complex.I * (omega + chi) / 2

/-- Birmingham--Mokhtari horizon hypergeometric parameter. -/
def d4BMCausalRadialC (omega : ℂ) : ℂ :=
  1 - Complex.I * omega

/-- Reciprocal-Gamma plus Jost factor. -/
def d4BMCausalJostPlus (omega chi : ℂ) : ℂ :=
  (Complex.Gamma (d4BMCausalRadialA omega chi))⁻¹

/-- Reciprocal-Gamma minus Jost factor. -/
def d4BMCausalJostMinus (omega chi : ℂ) : ℂ :=
  (Complex.Gamma (d4BMCausalRadialB omega chi))⁻¹

/-- Product of the two radial Jost factors. -/
def d4BMCausalJost (omega chi : ℂ) : ℂ :=
  d4BMCausalJostPlus omega chi * d4BMCausalJostMinus omega chi

/-- Plus inverse-Jost denominator factor. This is not the full sourced causal Green operator. -/
def d4BMCausalGreenPlusFactor (omega chi : ℂ) : ℂ :=
  (d4BMCausalJostPlus omega chi)⁻¹

/-- Minus inverse-Jost denominator factor. This is not the full sourced causal Green operator. -/
def d4BMCausalGreenMinusFactor (omega chi : ℂ) : ℂ :=
  (d4BMCausalJostMinus omega chi)⁻¹

/-- Opposite BM branches cancel their angular square root in the mixed quadratic frequency. -/
theorem d4BMCausalPlusMinusFrequency_eq
    (n k : ℕ) (chi : ℂ) :
    d4BMCausalPlusMinusFrequency n k chi =
      -Complex.I * (2 * (n : ℂ) + 2 * (k : ℂ) + 3) := by
  simp [d4BMCausalPlusMinusFrequency, d4BMCausalQNMPlus,
    d4BMCausalQNMMinus, d4BMCausalDecay]
  ring

/-- Exact frequency carried by every local time-translation-invariant `++-` Einstein monomial. -/
theorem d4BMCausalPlusPlusMinusFrequency_eq
    (n k : ℕ) (chi : ℂ) :
    d4BMCausalPlusPlusMinusFrequency n k chi =
      chi - Complex.I * (4 * (n : ℂ) + 2 * (k : ℂ) + 9 / 2) := by
  simp [d4BMCausalPlusPlusMinusFrequency, d4BMCausalQNMPlus,
    d4BMCausalQNMMinus, d4BMCausalDecay]
  ring

/-- Plus connection exponent at the second harmonic. -/
theorem d4BMCausalRadialA_plusPlus
    (n : ℕ) (chi : ℂ) :
    d4BMCausalRadialA (d4BMCausalPlusPlusFrequency n chi) chi =
      -2 * (n : ℂ) - 3 / 4 - Complex.I * chi / 2 := by
  simp [d4BMCausalRadialA, d4BMCausalPlusPlusFrequency,
    d4BMCausalQNMPlus, d4BMCausalDecay]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Minus connection exponent at the second harmonic. -/
theorem d4BMCausalRadialB_plusPlus
    (n : ℕ) (chi : ℂ) :
    d4BMCausalRadialB (d4BMCausalPlusPlusFrequency n chi) chi =
      -2 * (n : ℂ) - 3 / 4 - 3 * Complex.I * chi / 2 := by
  simp [d4BMCausalRadialB, d4BMCausalPlusPlusFrequency,
    d4BMCausalQNMPlus, d4BMCausalDecay]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Mixed quadratic channel lies exactly at a negative-integral horizon parameter. -/
theorem d4BMCausalRadialC_plusMinus_eq_negNat
    (n k : ℕ) (chi : ℂ) :
    d4BMCausalRadialC (d4BMCausalPlusMinusFrequency n k chi) =
      -((2 * n + 2 * k + 2 : ℕ) : ℂ) := by
  rw [d4BMCausalPlusMinusFrequency_eq]
  simp [d4BMCausalRadialC]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Plus connection exponent in the mixed quadratic channel. -/
theorem d4BMCausalRadialA_plusMinus
    (n k : ℕ) (chi : ℂ) :
    d4BMCausalRadialA (d4BMCausalPlusMinusFrequency n k chi) chi =
      -(n : ℂ) - (k : ℂ) - 3 / 4 + Complex.I * chi / 2 := by
  rw [d4BMCausalPlusMinusFrequency_eq]
  simp [d4BMCausalRadialA]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Minus connection exponent in the mixed quadratic channel. -/
theorem d4BMCausalRadialB_plusMinus
    (n k : ℕ) (chi : ℂ) :
    d4BMCausalRadialB (d4BMCausalPlusMinusFrequency n k chi) chi =
      -(n : ℂ) - (k : ℂ) - 3 / 4 - Complex.I * chi / 2 := by
  rw [d4BMCausalPlusMinusFrequency_eq]
  simp [d4BMCausalRadialB]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Local `++-` source hits a half-integer, rather than integral, plus Jost lattice point. -/
theorem d4BMCausalRadialA_plusPlusMinus
    (n k : ℕ) (chi : ℂ) :
    d4BMCausalRadialA (d4BMCausalPlusPlusMinusFrequency n k chi) chi =
      -2 * (n : ℂ) - (k : ℂ) - 3 / 2 := by
  rw [d4BMCausalPlusPlusMinusFrequency_eq]
  simp [d4BMCausalRadialA]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Minus connection exponent at the local `++-` source frequency. -/
theorem d4BMCausalRadialB_plusPlusMinus
    (n k : ℕ) (chi : ℂ) :
    d4BMCausalRadialB (d4BMCausalPlusPlusMinusFrequency n k chi) chi =
      -2 * (n : ℂ) - (k : ℂ) - 3 / 2 - Complex.I * chi := by
  rw [d4BMCausalPlusPlusMinusFrequency_eq]
  simp [d4BMCausalRadialB]
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem d4BMCausalRadialA_qnmPlus
    (N : ℕ) (chi : ℂ) :
    d4BMCausalRadialA (d4BMCausalQNMPlus N chi) chi = -(N : ℂ) := by
  simp [d4BMCausalRadialA, d4BMCausalQNMPlus, d4BMCausalDecay]
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem d4BMCausalRadialB_qnmMinus
    (N : ℕ) (chi : ℂ) :
    d4BMCausalRadialB (d4BMCausalQNMMinus N chi) chi = -(N : ℂ) := by
  simp [d4BMCausalRadialB, d4BMCausalQNMMinus, d4BMCausalDecay]
  ring_nf
  rw [Complex.I_sq]
  ring

private lemma d4BMNegativeHalfInteger_ne_negNat (n k m : ℕ) :
    (-2 * (n : ℂ) - (k : ℂ) - 3 / 2) ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre
  have htwo : (2 : ℝ) * (m : ℝ) = 4 * (n : ℝ) + 2 * (k : ℝ) + 3 := by
    linarith
  have hcast : (2 : ℤ) * (m : ℤ) = 4 * (n : ℤ) + 2 * (k : ℤ) + 3 := by
    exact_mod_cast htwo
  omega

/-- No local `++-` source frequency is a plus QNM in the same angular fibre. -/
theorem d4BMCausalPlusPlusMinusFrequency_ne_qnmPlus
    (n k N : ℕ) (chi : ℂ) :
    d4BMCausalPlusPlusMinusFrequency n k chi ≠ d4BMCausalQNMPlus N chi := by
  intro h
  have hA := congrArg (fun omega => d4BMCausalRadialA omega chi) h
  rw [d4BMCausalRadialA_plusPlusMinus, d4BMCausalRadialA_qnmPlus] at hA
  exact d4BMNegativeHalfInteger_ne_negNat n k N hA

/-- With nonzero physical angular real part, the local `++-` source also misses every minus QNM. -/
theorem d4BMCausalPlusPlusMinusFrequency_ne_qnmMinus_of_re_ne_zero
    (n k N : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMCausalPlusPlusMinusFrequency n k chi ≠ d4BMCausalQNMMinus N chi := by
  intro h
  have hre := congrArg Complex.re h
  simp [d4BMCausalPlusPlusMinusFrequency_eq, d4BMCausalQNMMinus,
    d4BMCausalDecay] at hre
  exact hchi (by linarith)

private lemma d4BMCausalRadialA_plusPlus_ne_negNat_of_re_ne_zero
    (n m : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMCausalRadialA (d4BMCausalPlusPlusFrequency n chi) chi ≠ -(m : ℂ) := by
  rw [d4BMCausalRadialA_plusPlus]
  intro h
  have him := congrArg Complex.im h
  simp at him
  exact hchi (by linarith)

private lemma d4BMCausalRadialB_plusPlus_ne_negNat_of_re_ne_zero
    (n m : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMCausalRadialB (d4BMCausalPlusPlusFrequency n chi) chi ≠ -(m : ℂ) := by
  rw [d4BMCausalRadialB_plusPlus]
  intro h
  have him := congrArg Complex.im h
  simp at him
  exact hchi (by linarith)

private lemma d4BMCausalRadialA_plusMinus_ne_negNat_of_re_ne_zero
    (n k m : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMCausalRadialA (d4BMCausalPlusMinusFrequency n k chi) chi ≠ -(m : ℂ) := by
  rw [d4BMCausalRadialA_plusMinus]
  intro h
  have him := congrArg Complex.im h
  simp at him
  exact hchi (by linarith)

private lemma d4BMCausalRadialB_plusMinus_ne_negNat_of_re_ne_zero
    (n k m : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMCausalRadialB (d4BMCausalPlusMinusFrequency n k chi) chi ≠ -(m : ℂ) := by
  rw [d4BMCausalRadialB_plusMinus]
  intro h
  have him := congrArg Complex.im h
  simp at him
  exact hchi (by linarith)

/-- Both second-harmonic radial Jost factors are regular for nonzero angular real part. -/
theorem d4BMCausalJost_plusPlus_ne_zero_of_re_ne_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMCausalJost (d4BMCausalPlusPlusFrequency n chi) chi ≠ 0 := by
  apply mul_ne_zero
  · unfold d4BMCausalJostPlus
    exact inv_ne_zero (Complex.Gamma_ne_zero fun m =>
      d4BMCausalRadialA_plusPlus_ne_negNat_of_re_ne_zero n m chi hchi)
  · unfold d4BMCausalJostMinus
    exact inv_ne_zero (Complex.Gamma_ne_zero fun m =>
      d4BMCausalRadialB_plusPlus_ne_negNat_of_re_ne_zero n m chi hchi)

/-- Mixed-channel reciprocal-Gamma factors are regular despite its horizon Frobenius resonance. -/
theorem d4BMCausalJost_plusMinus_ne_zero_of_re_ne_zero
    (n k : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMCausalJost (d4BMCausalPlusMinusFrequency n k chi) chi ≠ 0 := by
  apply mul_ne_zero
  · unfold d4BMCausalJostPlus
    exact inv_ne_zero (Complex.Gamma_ne_zero fun m =>
      d4BMCausalRadialA_plusMinus_ne_negNat_of_re_ne_zero n k m chi hchi)
  · unfold d4BMCausalJostMinus
    exact inv_ne_zero (Complex.Gamma_ne_zero fun m =>
      d4BMCausalRadialB_plusMinus_ne_negNat_of_re_ne_zero n k m chi hchi)

/-- Plus Jost factor is regular at every local `++-` source frequency. -/
lemma d4BMCausalJostPlus_plusPlusMinus_ne_zero
    (n k : ℕ) (chi : ℂ) :
    d4BMCausalJostPlus (d4BMCausalPlusPlusMinusFrequency n k chi) chi ≠ 0 := by
  unfold d4BMCausalJostPlus
  apply inv_ne_zero
  apply Complex.Gamma_ne_zero
  intro m hm
  rw [d4BMCausalRadialA_plusPlusMinus] at hm
  exact d4BMNegativeHalfInteger_ne_negNat n k m hm

/-- Minus Jost factor is regular at a local `++-` source when the angular real part is nonzero. -/
lemma d4BMCausalJostMinus_plusPlusMinus_ne_zero_of_re_ne_zero
    (n k : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMCausalJostMinus (d4BMCausalPlusPlusMinusFrequency n k chi) chi ≠ 0 := by
  unfold d4BMCausalJostMinus
  apply inv_ne_zero
  apply Complex.Gamma_ne_zero
  intro m hm
  have him := congrArg Complex.im hm
  rw [d4BMCausalRadialB_plusPlusMinus] at him
  simp at him
  exact hchi (by linarith)

/-- Full same-fibre radial Jost determinant is regular at the local `++-` source frequency. -/
theorem d4BMCausalJost_plusPlusMinus_ne_zero_of_re_ne_zero
    (n k : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMCausalJost (d4BMCausalPlusPlusMinusFrequency n k chi) chi ≠ 0 := by
  exact mul_ne_zero (d4BMCausalJostPlus_plusPlusMinus_ne_zero n k chi)
    (d4BMCausalJostMinus_plusPlusMinus_ne_zero_of_re_ne_zero n k chi hchi)

/-- Exact plus inverse-Jost factor in the `++` channel. -/
theorem d4BMCausalGreenPlusFactor_plusPlus
    (n : ℕ) (chi : ℂ) :
    d4BMCausalGreenPlusFactor (d4BMCausalPlusPlusFrequency n chi) chi =
      Complex.Gamma (-2 * (n : ℂ) - 3 / 4 - Complex.I * chi / 2) := by
  simp [d4BMCausalGreenPlusFactor, d4BMCausalJostPlus,
    d4BMCausalRadialA_plusPlus]

/-- Exact plus inverse-Jost factor in the transient `+-` channel. -/
theorem d4BMCausalGreenPlusFactor_plusMinus
    (n k : ℕ) (chi : ℂ) :
    d4BMCausalGreenPlusFactor (d4BMCausalPlusMinusFrequency n k chi) chi =
      Complex.Gamma (-(n : ℂ) - (k : ℂ) - 3 / 4 + Complex.I * chi / 2) := by
  simp [d4BMCausalGreenPlusFactor, d4BMCausalJostPlus,
    d4BMCausalRadialA_plusMinus]

/-- Exact minus inverse-Jost factor in the transient `+-` channel. -/
theorem d4BMCausalGreenMinusFactor_plusMinus
    (n k : ℕ) (chi : ℂ) :
    d4BMCausalGreenMinusFactor (d4BMCausalPlusMinusFrequency n k chi) chi =
      Complex.Gamma (-(n : ℂ) - (k : ℂ) - 3 / 4 - Complex.I * chi / 2) := by
  simp [d4BMCausalGreenMinusFactor, d4BMCausalJostMinus,
    d4BMCausalRadialB_plusMinus]

end

end RHTower
