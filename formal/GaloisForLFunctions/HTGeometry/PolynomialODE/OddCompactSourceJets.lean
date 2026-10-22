import GaloisForLFunctions.HTGeometry.PolynomialODE.JetRankThreeLyapunovClosure
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Exact modular source jets through order ten

The source jets obey a covariant polynomial derivative recurrence. Explicit
jet polynomials are verified by extensionality and ring identities. The
all-order derivative interface retains the literal mass factor.
-/

open MvPolynomial
namespace HTGeometry
noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

private theorem states_univ : (Finset.univ : Finset ModularThetaLyapunovState) =
    {.S, .A, .W} := by
  ext i
  cases i <;> simp

private theorem normalizedLie_sub (P Q : ModularThetaLyapunovPolynomial) :
    modularThetaLyapunovNormalizedLie (P-Q) =
      modularThetaLyapunovNormalizedLie P - modularThetaLyapunovNormalizedLie Q := by
  simp only [modularThetaLyapunovNormalizedLie, modularThetaLyapunovLie,
    map_sub, sub_mul, Finset.sum_sub_distrib]
  ring

private theorem normalizedLie_C_mul (c : ℂ) (P : ModularThetaLyapunovPolynomial) :
    modularThetaLyapunovNormalizedLie (C c*P) =
      C c*modularThetaLyapunovNormalizedLie P := by
  simp only [modularThetaLyapunovNormalizedLie, modularThetaLyapunovLie,
    pderiv_mul, pderiv_C, zero_mul, zero_add, mul_assoc, ← Finset.mul_sum]
  ring

private theorem normalizedLie_mul_C (P : ModularThetaLyapunovPolynomial) (c : ℂ) :
    modularThetaLyapunovNormalizedLie (P*C c) =
      modularThetaLyapunovNormalizedLie P*C c := by
  rw [mul_comm P (C c), normalizedLie_C_mul, mul_comm]

/-- Source jets themselves obey the covariant modular derivative recurrence. -/
theorem modularThetaLyapunovNormalizedSourceJet_succ (n : ℕ) :
    modularThetaLyapunovNormalizedSourceJet (n+1) =
      modularThetaLyapunovNormalizedLie (modularThetaLyapunovNormalizedSourceJet n) := by
  unfold modularThetaLyapunovNormalizedSourceJet
  change (modularThetaLyapunovNormalizedLie (modularThetaLyapunovNormalizedHJet (n+2)) -
    C (1/4 : ℂ)*modularThetaLyapunovNormalizedLie (modularThetaLyapunovNormalizedHJet n))*
      C (1/2 : ℂ) = _
  rw [normalizedLie_mul_C, normalizedLie_sub, normalizedLie_C_mul]

/-- Every source jet is the derivative of its exact mass-normalized polynomial observable. -/
theorem iteratedDeriv_mass_mul_eval_lyapunovSourceJet
    (v : ModularThetaLyapunovState → ℝ → ℂ)
    (hv : ∀ x i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x) (modularThetaLyapunovVectorField i)) x)
    (M : ℝ → ℂ)
    (hM : ∀ x, HasDerivAt M (-(1/6 : ℂ)*M x*v .S x) x) (n : ℕ) :
    iteratedDeriv n (fun x => M x * MvPolynomial.eval (fun j => v j x)
      (modularThetaLyapunovNormalizedSourceJet 0)) =
    fun x => M x * MvPolynomial.eval (fun j => v j x)
      (modularThetaLyapunovNormalizedSourceJet n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have hP := hasDerivAt_eval_modularThetaLyapunovPolynomial
        (modularThetaLyapunovNormalizedSourceJet n) v x (hv x)
      have hprod := (hM x).mul hP
      change deriv (M * (fun y => MvPolynomial.eval (fun j => v j y)
        (modularThetaLyapunovNormalizedSourceJet n))) x = _
      rw [hprod.deriv, modularThetaLyapunovNormalizedSourceJet_succ]
      unfold modularThetaLyapunovNormalizedLie
      simp only [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      ring

/-- Explicit normalized source jet of order 0 in the modular chart. -/
def oddCompactSourceJet0 : ModularThetaLyapunovPolynomial :=
  (C (1 / 24 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) +
    (C (1 / 16 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-3 / 8 : ℂ)))

/-- Symbolic covariant-derivative verification of source jet 0. -/
theorem oddCompactSourceJet0_eq : modularThetaLyapunovNormalizedSourceJet 0 =
    oddCompactSourceJet0 := by
  apply MvPolynomial.funext
  intro v
  simp [modularThetaLyapunovNormalizedSourceJet, modularThetaLyapunovNormalizedHJet,
    oddCompactSourceJet0, modularThetaLyapunovNormalizedLie, modularThetaLyapunovLie,
    modularThetaLyapunovVectorField, states_univ, pderiv_mul, pderiv_pow, pderiv_C]
  ring

/-- Explicit normalized source jet of order 1 in the modular chart. -/
def oddCompactSourceJet1 : ModularThetaLyapunovPolynomial :=
  ((C (-5 / 144 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) +
    C (-7 / 96 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ)) +
    (C (5 / 16 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) +
    C (-1 / 8 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ)))

/-- Symbolic covariant-derivative verification of source jet 1. -/
theorem oddCompactSourceJet1_eq : modularThetaLyapunovNormalizedSourceJet 1 =
    oddCompactSourceJet1 := by
  rw [show (1 : ℕ) = 0+1 by norm_num,
    modularThetaLyapunovNormalizedSourceJet_succ, oddCompactSourceJet0_eq]
  apply MvPolynomial.funext
  intro v
  simp [oddCompactSourceJet0, oddCompactSourceJet1,
    modularThetaLyapunovNormalizedLie, modularThetaLyapunovLie,
    modularThetaLyapunovVectorField, states_univ, pderiv_mul, pderiv_pow, pderiv_C]
  ring

/-- Explicit normalized source jet of order 2 in the modular chart. -/
def oddCompactSourceJet2 : ModularThetaLyapunovPolynomial :=
  (((C (35 / 864 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) +
    C (25 / 288 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ)) +
    (C (-15 / 32 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) +
    C (1 / 4 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ))) +
    ((C (-1 / 128 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (1 / 4 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ)) +
    (C (-45 / 64 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (15 / 16 : ℂ))))

/-- Symbolic covariant-derivative verification of source jet 2. -/
theorem oddCompactSourceJet2_eq : modularThetaLyapunovNormalizedSourceJet 2 =
    oddCompactSourceJet2 := by
  rw [show (2 : ℕ) = 1+1 by norm_num,
    modularThetaLyapunovNormalizedSourceJet_succ, oddCompactSourceJet1_eq]
  apply MvPolynomial.funext
  intro v
  simp [oddCompactSourceJet1, oddCompactSourceJet2,
    modularThetaLyapunovNormalizedLie, modularThetaLyapunovLie,
    modularThetaLyapunovVectorField, states_univ, pderiv_mul, pderiv_pow, pderiv_C]
  ring

/-- Explicit normalized source jet of order 3 in the modular chart. -/
def oddCompactSourceJet3 : ModularThetaLyapunovPolynomial :=
  (((C (-35 / 576 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) +
    C (-239 / 1728 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ)) +
    (C (505 / 576 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) +
    (C (-17 / 48 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-1 / 256 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ)))) +
    ((C (-7 / 8 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    (C (707 / 384 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-95 / 32 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ))) +
    (C (3 / 32 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    (C (-1 / 2 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (101 / 32 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ)))))

/-- Symbolic covariant-derivative verification of source jet 3. -/
theorem oddCompactSourceJet3_eq : modularThetaLyapunovNormalizedSourceJet 3 =
    oddCompactSourceJet3 := by
  rw [show (3 : ℕ) = 2+1 by norm_num,
    modularThetaLyapunovNormalizedSourceJet_succ, oddCompactSourceJet2_eq]
  apply MvPolynomial.funext
  intro v
  simp [oddCompactSourceJet2, oddCompactSourceJet3,
    modularThetaLyapunovNormalizedLie, modularThetaLyapunovLie,
    modularThetaLyapunovVectorField, states_univ, pderiv_mul, pderiv_pow, pderiv_C]
  ring

/-- Explicit normalized source jet of order 4 in the modular chart. -/
def oddCompactSourceJet4 : ModularThetaLyapunovPolynomial :=
  ((((C (385 / 3456 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) +
    C (6439 / 20736 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ)) +
    (C (-6685 / 3456 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) +
    C (181 / 432 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ))) +
    ((C (241 / 1536 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (95 / 48 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ)) +
    (C (-4775 / 1152 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    (C (75 / 8 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) +
    C (-13 / 32 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ))))) +
    (((C (17 / 6 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-191 / 16 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ)) +
    (C (51 / 1024 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (-15 / 32 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ))) +
    ((C (191 / 512 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (1 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ)) +
    (C (-191 / 16 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    (C (225 / 16 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-285 / 32 : ℂ))))))

/-- Symbolic covariant-derivative verification of source jet 4. -/
theorem oddCompactSourceJet4_eq : modularThetaLyapunovNormalizedSourceJet 4 =
    oddCompactSourceJet4 := by
  rw [show (4 : ℕ) = 3+1 by norm_num,
    modularThetaLyapunovNormalizedSourceJet_succ, oddCompactSourceJet3_eq]
  apply MvPolynomial.funext
  intro v
  simp [oddCompactSourceJet3, oddCompactSourceJet4,
    modularThetaLyapunovNormalizedLie, modularThetaLyapunovLie,
    modularThetaLyapunovVectorField, states_univ, pderiv_mul, pderiv_pow, pderiv_C]
  ring

/-- Explicit normalized source jet of order 5 in the modular chart. -/
def oddCompactSourceJet5 : ModularThetaLyapunovPolynomial :=
  ((((C (-5005 / 20736 : ℂ) * X ModularThetaLyapunovState.S^(7 : ℕ) +
    (C (-108737 / 124416 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (11305 / 2304 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ))) +
    (C (-587 / 1152 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    (C (-26075 / 27648 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (-2797 / 864 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ)))) +
    ((C (77197 / 6912 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    (C (-8935 / 288 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) +
    C (259 / 384 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ))) +
    (C (-731 / 72 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    (C (5491 / 192 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-915 / 2048 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ))))) +
    (((C (231 / 64 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    (C (323 / 1024 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (-17 / 2 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ))) +
    (C (2261 / 32 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    (C (-12509 / 192 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (3695 / 64 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ)))) +
    ((C (-237 / 512 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    (C (7 / 4 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-969 / 128 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ))) +
    (C (-2 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    (C (323 / 8 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-1787 / 16 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ))))))

/-- Symbolic covariant-derivative verification of source jet 5. -/
theorem oddCompactSourceJet5_eq : modularThetaLyapunovNormalizedSourceJet 5 =
    oddCompactSourceJet5 := by
  rw [show (5 : ℕ) = 4+1 by norm_num,
    modularThetaLyapunovNormalizedSourceJet_succ, oddCompactSourceJet4_eq]
  apply MvPolynomial.funext
  intro v
  simp [oddCompactSourceJet4, oddCompactSourceJet5,
    modularThetaLyapunovNormalizedLie, modularThetaLyapunovLie,
    modularThetaLyapunovVectorField, states_univ, pderiv_mul, pderiv_pow, pderiv_C]
  ring

/-- Explicit normalized source jet of order 6 in the modular chart. -/
def oddCompactSourceJet6 : ModularThetaLyapunovPolynomial :=
  (((((C (25025 / 41472 : ℂ) * X ModularThetaLyapunovState.S^(8 : ℕ) +
    C (514381 / 186624 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ)) +
    (C (-194425 / 13824 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) +
    C (407 / 288 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ))) +
    ((C (118135 / 27648 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (75 / 32 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ)) +
    (C (-3251695 / 82944 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (758905 / 6912 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ)))) +
    (((C (85 / 32 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (1495 / 54 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ)) +
    (C (-91405 / 1728 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (7925 / 3072 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ))) +
    ((C (-515 / 32 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-121705 / 6144 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ)) +
    (C (45 / 1 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    (C (-47975 / 192 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (542075 / 2304 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ)))))) +
    ((((C (-39435 / 128 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) +
    C (725 / 128 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ)) +
    (C (-20 / 1 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (6565 / 128 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ))) +
    ((C (24 / 1 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (-8585 / 24 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ)) +
    (C (21683 / 32 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    (C (849 / 8192 : ℂ) * X ModularThetaLyapunovState.A^(4 : ℕ) +
    C (345 / 128 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ))))) +
    (((C (-25755 / 4096 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (-45 / 8 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ)) +
    (C (7575 / 128 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-21683 / 1024 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ))) +
    ((C (4 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(6 : ℕ) +
    C (-505 / 4 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ)) +
    (C (21683 / 32 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    (C (-118305 / 256 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (11085 / 64 : ℂ)))))))

/-- Symbolic covariant-derivative verification of source jet 6. -/
theorem oddCompactSourceJet6_eq : modularThetaLyapunovNormalizedSourceJet 6 =
    oddCompactSourceJet6 := by
  rw [show (6 : ℕ) = 5+1 by norm_num,
    modularThetaLyapunovNormalizedSourceJet_succ, oddCompactSourceJet5_eq]
  apply MvPolynomial.funext
  intro v
  simp [oddCompactSourceJet5, oddCompactSourceJet6,
    modularThetaLyapunovNormalizedLie, modularThetaLyapunovLie,
    modularThetaLyapunovVectorField, states_univ, pderiv_mul, pderiv_pow, pderiv_C]
  ring

/-- Explicit normalized source jet of order 7 in the modular chart. -/
def oddCompactSourceJet7 : ModularThetaLyapunovPolynomial :=
  (((((C (-425425 / 248832 : ℂ) * X ModularThetaLyapunovState.S^(9 : ℕ) +
    C (-10389355 / 1119744 : ℂ) * X ModularThetaLyapunovState.S^(7 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ)) +
    (C (3728725 / 82944 : ℂ) * X ModularThetaLyapunovState.S^(7 : ℕ) +
    (C (-746851 / 93312 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-2905603 / 165888 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ)))) +
    ((C (46603 / 5184 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    (C (81009065 / 497664 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-1925455 / 4608 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ))) +
    (C (-221665 / 6912 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    (C (-67855 / 1296 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (437315 / 4608 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ))))) +
    (((C (-228215 / 18432 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (26155 / 576 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ)) +
    (C (19425875 / 110592 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    (C (-10055 / 54 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (2083765 / 3456 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ)))) +
    ((C (-13148107 / 13824 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    (C (3627145 / 2304 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) +
    C (-21995 / 512 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ))) +
    (C (1645 / 12 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    (C (-192955 / 1536 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-530 / 3 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ)))))) +
    ((((C (544595 / 288 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-935221 / 384 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ)) +
    (C (-17283 / 16384 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(4 : ℕ) +
    (C (-11235 / 256 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (681675 / 8192 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ)))) +
    ((C (1415 / 16 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    (C (-172095 / 256 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-55013 / 2048 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ))) +
    (C (-194 / 3 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(6 : ℕ) +
    (C (12665 / 8 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (-385091 / 64 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ))))) +
    (((C (5078003 / 1536 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    (C (-240305 / 128 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) +
    C (-2439 / 1024 : ℂ) * X ModularThetaLyapunovState.A^(4 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ))) +
    (C (-795 / 64 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    (C (176565 / 2048 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (33 / 2 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ)))) +
    ((C (-5215 / 16 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    (C (165039 / 256 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-8 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(7 : ℕ))) +
    (C (745 / 2 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    (C (-55013 / 16 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (725429 / 128 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ)))))))

/-- Symbolic covariant-derivative verification of source jet 7. -/
theorem oddCompactSourceJet7_eq : modularThetaLyapunovNormalizedSourceJet 7 =
    oddCompactSourceJet7 := by
  rw [show (7 : ℕ) = 6+1 by norm_num,
    modularThetaLyapunovNormalizedSourceJet_succ, oddCompactSourceJet6_eq]
  apply MvPolynomial.funext
  intro v
  simp [oddCompactSourceJet6, oddCompactSourceJet7,
    modularThetaLyapunovNormalizedLie, modularThetaLyapunovLie,
    modularThetaLyapunovVectorField, states_univ, pderiv_mul, pderiv_pow, pderiv_C]
  ring

/-- Explicit normalized source jet of order 8 in the modular chart. -/
def oddCompactSourceJet8 : ModularThetaLyapunovPolynomial :=
  (((((C (8083075 / 1492992 : ℂ) * X ModularThetaLyapunovState.S^(10 : ℕ) +
    (C (885697661 / 26873856 : ℂ) * X ModularThetaLyapunovState.S^(8 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-26301275 / 165888 : ℂ) * X ModularThetaLyapunovState.S^(8 : ℕ))) +
    ((C (4220461 / 93312 : ℂ) * X ModularThetaLyapunovState.S^(7 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (208106413 / 2985984 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ)) +
    (C (-4419709 / 93312 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-540614431 / 746496 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ)))) +
    (((C (1970045 / 1152 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) +
    C (4245367 / 20736 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ)) +
    (C (-947 / 3888 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-427757 / 1152 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ))) +
    ((C (12064865 / 221184 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (-4685 / 768 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ)) +
    (C (-124159885 / 110592 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (134395 / 216 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ))))) +
    (((C (-78825 / 128 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    (C (32948363 / 6912 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-56017745 / 6912 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ))) +
    ((C (1201945 / 4608 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-38165 / 54 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ)) +
    (C (-89335 / 128 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (27602 / 27 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ)))) +
    (((C (-1571245 / 216 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (926177 / 144 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ)) +
    (C (208959 / 32768 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(4 : ℕ) +
    C (221895 / 512 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ))) +
    ((C (-8329175 / 12288 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (-79945 / 96 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ)) +
    (C (541265 / 128 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (1233197 / 512 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ)))))) +
    ((((C (5687 / 9 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(6 : ℕ) +
    (C (-47295 / 4 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (486115 / 16 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ))) +
    ((C (-40012675 / 2304 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (1933725 / 128 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ)) +
    (C (31719 / 1024 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(4 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (16735 / 64 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ)))) +
    (((C (-761975 / 512 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-681 / 2 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ)) +
    (C (5255 / 1 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-199563 / 32 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ))) +
    ((C (168 / 1 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(7 : ℕ) +
    C (-6306 / 1 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ)) +
    (C (86989 / 2 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-1600507 / 32 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ))))) +
    ((((C (-26199 / 65536 : ℂ) * X ModularThetaLyapunovState.A^(5 : ℕ) +
    C (34137 / 1024 : ℂ) * X ModularThetaLyapunovState.A^(4 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ)) +
    (C (-892299 / 32768 : ℂ) * X ModularThetaLyapunovState.A^(4 : ℕ) +
    C (3165 / 64 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ))) +
    ((C (-362595 / 512 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (782901 / 1024 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ)) +
    (C (-91 / 2 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(6 : ℕ) +
    C (47295 / 32 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ)))) +
    (((C (-230265 / 32 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (1600507 / 1024 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ)) +
    (C (16 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(8 : ℕ) +
    C (-1051 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(6 : ℕ))) +
    ((C (15351 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (-1600507 / 32 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ)) +
    (C (5801175 / 256 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-720915 / 128 : ℂ)))))))

/-- Symbolic covariant-derivative verification of source jet 8. -/
theorem oddCompactSourceJet8_eq : modularThetaLyapunovNormalizedSourceJet 8 =
    oddCompactSourceJet8 := by
  rw [show (8 : ℕ) = 7+1 by norm_num,
    modularThetaLyapunovNormalizedSourceJet_succ, oddCompactSourceJet7_eq]
  apply MvPolynomial.funext
  intro v
  simp [oddCompactSourceJet7, oddCompactSourceJet8,
    modularThetaLyapunovNormalizedLie, modularThetaLyapunovLie,
    modularThetaLyapunovVectorField, states_univ, pderiv_mul, pderiv_pow, pderiv_C]
  ring

/-- Monomial group 0 of the order-9 normalized source jet. -/
def oddCompactSourceJet9Part0 : ModularThetaLyapunovPolynomial :=
  C (-56581525 / 2985984 : ℂ) * X ModularThetaLyapunovState.S^(11 : ℕ) +
    C (-19983493963 / 161243136 : ℂ) * X ModularThetaLyapunovState.S^(9 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (22547525 / 36864 : ℂ) * X ModularThetaLyapunovState.S^(9 : ℕ) +
    C (-1031029751 / 4478976 : ℂ) * X ModularThetaLyapunovState.S^(8 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-558655477 / 1990656 : ℂ) * X ModularThetaLyapunovState.S^(7 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (14025815 / 186624 : ℂ) * X ModularThetaLyapunovState.S^(7 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (550635815 / 165888 : ℂ) * X ModularThetaLyapunovState.S^(7 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-12977965 / 1728 : ℂ) * X ModularThetaLyapunovState.S^(7 : ℕ) +
    C (-268276799 / 248832 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (10089037 / 15552 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (39583103 / 13824 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-312020387 / 1327104 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (-542745 / 512 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (153996959 / 24576 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (-1887137 / 1296 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (-2469959 / 768 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-281955041 / 10368 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (197860985 / 4608 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) +
    C (-153360235 / 110592 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (265685 / 96 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (11748245 / 1024 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-540239 / 108 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (3596315 / 192 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-1522091 / 96 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-6222931 / 196608 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(4 : ℕ) +
    C (-31072265 / 9216 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (36286185 / 8192 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (3486245 / 576 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (-4158645 / 256 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-67612475 / 2304 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (-87073 / 18 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(6 : ℕ) +
    C (532915 / 8 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (-7252621 / 72 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (1351107869 / 13824 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-253076855 / 2304 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) +
    C (-925023 / 4096 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(4 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-2523185 / 768 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (31474845 / 2048 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (33369 / 8 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (-784665 / 16 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ)

/-- Monomial group 1 of the order-9 normalized source jet. -/
def oddCompactSourceJet9Part1 : ModularThetaLyapunovPolynomial :=
  C (671587 / 32 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-6310 / 3 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(7 : ℕ) +
    C (126405 / 2 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (-1895483 / 6 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (96103907 / 384 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (784995 / 131072 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(5 : ℕ) +
    C (-1138005 / 2048 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(4 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (24731973 / 65536 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(4 : ℕ) +
    C (-167825 / 128 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (16077285 / 1024 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-7117785 / 512 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (4767 / 4 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(6 : ℕ) +
    C (-2024865 / 64 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (1796949 / 16 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (5653171 / 2048 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (-424 / 1 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(8 : ℕ) +
    C (46269 / 2 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(6 : ℕ) +
    C (-264486 / 1 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (39572197 / 64 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-354307597 / 1536 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (23445005 / 256 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) +
    C (462123 / 32768 : ℂ) * X ModularThetaLyapunovState.A^(5 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-93159 / 256 : ℂ) * X ModularThetaLyapunovState.A^(4 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (3490209 / 4096 : ℂ) * X ModularThetaLyapunovState.A^(4 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-5691 / 32 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (1137645 / 256 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-1843623 / 128 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (120 / 1 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(7 : ℕ) +
    C (-47223 / 8 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (54453 / 1 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-16959513 / 256 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-32 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(9 : ℕ) +
    C (2862 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(7 : ℕ) +
    C (-62232 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (5653171 / 16 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-50615371 / 128 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ)

/-- Explicit normalized source jet of order 9 in the modular chart. -/
def oddCompactSourceJet9 : ModularThetaLyapunovPolynomial :=
  oddCompactSourceJet9Part0 +
    oddCompactSourceJet9Part1
/-- Symbolic covariant-derivative verification of source jet 9. -/
theorem oddCompactSourceJet9_eq : modularThetaLyapunovNormalizedSourceJet 9 =
    oddCompactSourceJet9 := by
  rw [show (9 : ℕ) = 8+1 by norm_num,
    modularThetaLyapunovNormalizedSourceJet_succ, oddCompactSourceJet8_eq]
  apply MvPolynomial.funext
  intro v
  simp [oddCompactSourceJet8, oddCompactSourceJet9, oddCompactSourceJet9Part0, oddCompactSourceJet9Part1,
    modularThetaLyapunovNormalizedLie, modularThetaLyapunovLie,
    modularThetaLyapunovVectorField, states_univ, pderiv_mul, pderiv_pow, pderiv_C]
  ring

/-- Monomial group 0 of the order-10 normalized source jet. -/
def oddCompactSourceJet10Part0 : ModularThetaLyapunovPolynomial :=
  C (1301375075 / 17915904 : ℂ) * X ModularThetaLyapunovState.S^(12 : ℕ) +
    C (240719686787 / 483729408 : ℂ) * X ModularThetaLyapunovState.S^(10 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-5100420325 / 1990656 : ℂ) * X ModularThetaLyapunovState.S^(10 : ℕ) +
    C (21907831189 / 20155392 : ℂ) * X ModularThetaLyapunovState.S^(9 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (28270507225 / 23887872 : ℂ) * X ModularThetaLyapunovState.S^(8 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (150487757 / 248832 : ℂ) * X ModularThetaLyapunovState.S^(8 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-558875224091 / 35831808 : ℂ) * X ModularThetaLyapunovState.S^(8 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (3902823925 / 110592 : ℂ) * X ModularThetaLyapunovState.S^(8 : ℕ) +
    C (642295043 / 124416 : ℂ) * X ModularThetaLyapunovState.S^(7 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-96757127 / 23328 : ℂ) * X ModularThetaLyapunovState.S^(7 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-2663110891 / 124416 : ℂ) * X ModularThetaLyapunovState.S^(7 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (4208898365 / 3981312 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (418575269 / 41472 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-131315146603 / 3981312 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (-1177729 / 3888 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (2788836379 / 124416 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (80221317617 / 497664 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-6537067075 / 27648 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) +
    C (370946317 / 55296 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-318479 / 54 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-2678826577 / 27648 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (1114547 / 54 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (597557 / 5184 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (63474499 / 768 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (619517245 / 3538944 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(4 : ℕ) +
    C (139379485 / 6144 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-7612929815 / 294912 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (-42257635 / 1152 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (2956235 / 1024 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (18423980195 / 73728 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (126903 / 4 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(6 : ℕ) +
    C (-84803245 / 288 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (35090325 / 256 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-109330324405 / 165888 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (5337641155 / 6912 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) +
    C (20894671 / 18432 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(4 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (37065455 / 1152 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-758427295 / 6144 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-158025 / 4 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (24082115 / 72 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ)

/-- Monomial group 1 of the order-10 normalized source jet. -/
def oddCompactSourceJet10Part1 : ModularThetaLyapunovPolynomial :=
  C (39769035 / 256 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (61468 / 3 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(7 : ℕ) +
    C (-8708431 / 18 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (233155715 / 144 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-3073270495 / 3456 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-5447693 / 131072 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(5 : ℕ) +
    C (10732979 / 2048 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(4 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-395559387 / 131072 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(4 : ℕ) +
    C (2620975 / 128 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (-420047235 / 2048 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (1235959225 / 8192 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (-73353 / 4 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(6 : ℕ) +
    C (50445295 / 128 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (-240953565 / 256 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-4092034195 / 12288 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (6616 / 1 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(8 : ℕ) +
    C (-3588497 / 12 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(6 : ℕ) +
    C (21054195 / 8 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (-1613042525 / 384 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (3812600825 / 2304 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-529598715 / 512 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) +
    C (-4727697 / 16384 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(5 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (965071 / 128 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(4 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-60044067 / 4096 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(4 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (92925 / 16 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (-31679355 / 256 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (339206475 / 1024 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-3888 / 1 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(7 : ℕ) +
    C (1289133 / 8 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (-2339355 / 2 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (220732135 / 256 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (3136 / 3 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(9 : ℕ) +
    C (-79506 / 1 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(7 : ℕ) +
    C (1403613 / 1 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (-288649715 / 48 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (152504033 / 32 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (1341999 / 524288 : ℂ) * X ModularThetaLyapunovState.A^(6 : ℕ) +
    C (-4425849 / 16384 : ℂ) * X ModularThetaLyapunovState.A^(5 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (49594707 / 262144 : ℂ) * X ModularThetaLyapunovState.A^(5 : ℕ) +
    C (1766379 / 512 : ℂ) * X ModularThetaLyapunovState.A^(4 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ)

/-- Monomial group 2 of the order-10 normalized source jet. -/
def oddCompactSourceJet10Part2 : ModularThetaLyapunovPolynomial :=
  C (-64621341 / 4096 : ℂ) * X ModularThetaLyapunovState.A^(4 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (397222479 / 65536 : ℂ) * X ModularThetaLyapunovState.A^(4 : ℕ) +
    C (2373 / 4 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(6 : ℕ) +
    C (-5991345 / 256 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (161415495 / 1024 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-865949145 / 8192 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (-306 / 1 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(8 : ℕ) +
    C (172263 / 8 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(6 : ℕ) +
    C (-21054195 / 64 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (254690925 / 256 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-152504033 / 1024 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (64 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(10 : ℕ) +
    C (-7572 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(8 : ℕ) +
    C (467871 / 2 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(6 : ℕ) +
    C (-16979395 / 8 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (152504033 / 32 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-1588796145 / 1024 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (70335015 / 256 : ℂ)

/-- Explicit normalized source jet of order 10 in the modular chart. -/
def oddCompactSourceJet10 : ModularThetaLyapunovPolynomial :=
  oddCompactSourceJet10Part0 +
    oddCompactSourceJet10Part1 +
    oddCompactSourceJet10Part2
/-- Symbolic covariant-derivative verification of source jet 10. -/
theorem oddCompactSourceJet10_eq : modularThetaLyapunovNormalizedSourceJet 10 =
    oddCompactSourceJet10 := by
  rw [show (10 : ℕ) = 9+1 by norm_num,
    modularThetaLyapunovNormalizedSourceJet_succ, oddCompactSourceJet9_eq]
  apply MvPolynomial.funext
  intro v
  simp [oddCompactSourceJet9, oddCompactSourceJet9Part0, oddCompactSourceJet9Part1, oddCompactSourceJet10, oddCompactSourceJet10Part0, oddCompactSourceJet10Part1, oddCompactSourceJet10Part2,
    modularThetaLyapunovNormalizedLie, modularThetaLyapunovLie,
    modularThetaLyapunovVectorField, states_univ, pderiv_mul, pderiv_pow, pderiv_C]
  ring

end
end HTGeometry
