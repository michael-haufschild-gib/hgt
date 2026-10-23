import GaloisForLFunctions.HTGeometry.PolynomialODE.JetRankThreeLyapunovClosure
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Exact compact-chart expansion of the theta reflected determinant

The covariant Lyapunov derivative generates the ten normalized mass jets.
Polynomial extensionality and ring identities check each jet and the complete
540-monomial D1 expansion. Monomial groups keep elaboration bounded.
This module proves identities only; the compact sign is checked separately.
-/

open MvPolynomial
namespace HTGeometry
noncomputable section
set_option linter.unusedSimpArgs false


private def compactH0 : ModularThetaLyapunovPolynomial :=
  C (1 / 1 : ℂ)

private theorem compactH0_eq : modularThetaLyapunovNormalizedHJet 0 = compactH0 := by

  simp [modularThetaLyapunovNormalizedHJet, compactH0]

private def compactH1 : ModularThetaLyapunovPolynomial :=
  C (-1 / 6 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ)

private theorem compactH1_eq : modularThetaLyapunovNormalizedHJet 1 = compactH1 := by

  rw [modularThetaLyapunovNormalizedHJet, compactH0_eq]
  apply MvPolynomial.funext
  intro v
  simp [compactH0, compactH1, modularThetaLyapunovNormalizedLie,
    modularThetaLyapunovLie, pderiv_mul, pderiv_pow, pderiv_C,
    modularThetaLyapunovVectorField,
    show (Finset.univ : Finset ModularThetaLyapunovState) = {.S, .A, .W} by decide]
  all_goals ring

private def compactH2 : ModularThetaLyapunovPolynomial :=
  C (1 / 12 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) +
    C (1 / 8 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-1 / 2 : ℂ)

private theorem compactH2_eq : modularThetaLyapunovNormalizedHJet 2 = compactH2 := by

  rw [modularThetaLyapunovNormalizedHJet, compactH1_eq]
  apply MvPolynomial.funext
  intro v
  simp [compactH1, compactH2, modularThetaLyapunovNormalizedLie,
    modularThetaLyapunovLie, pderiv_mul, pderiv_pow, pderiv_C,
    modularThetaLyapunovVectorField,
    show (Finset.univ : Finset ModularThetaLyapunovState) = {.S, .A, .W} by decide]
  all_goals ring

private def compactH3 : ModularThetaLyapunovPolynomial :=
  C (-5 / 72 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) +
    C (-7 / 48 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (7 / 12 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) +
    C (-1 / 4 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ)

private theorem compactH3_eq : modularThetaLyapunovNormalizedHJet 3 = compactH3 := by

  rw [modularThetaLyapunovNormalizedHJet, compactH2_eq]
  apply MvPolynomial.funext
  intro v
  simp [compactH2, compactH3, modularThetaLyapunovNormalizedLie,
    modularThetaLyapunovLie, pderiv_mul, pderiv_pow, pderiv_C,
    modularThetaLyapunovVectorField,
    show (Finset.univ : Finset ModularThetaLyapunovState) = {.S, .A, .W} by decide]
  all_goals ring

private def compactH4 : ModularThetaLyapunovPolynomial :=
  C (35 / 432 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) +
    C (25 / 144 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-11 / 12 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) +
    C (1 / 2 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-1 / 64 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (1 / 2 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-11 / 8 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (7 / 4 : ℂ)

private theorem compactH4_eq : modularThetaLyapunovNormalizedHJet 4 = compactH4 := by

  rw [modularThetaLyapunovNormalizedHJet, compactH3_eq]
  apply MvPolynomial.funext
  intro v
  simp [compactH3, compactH4, modularThetaLyapunovNormalizedLie,
    modularThetaLyapunovLie, pderiv_mul, pderiv_pow, pderiv_C,
    modularThetaLyapunovVectorField,
    show (Finset.univ : Finset ModularThetaLyapunovState) = {.S, .A, .W} by decide]
  all_goals ring

private def compactH5 : ModularThetaLyapunovPolynomial :=
  C (-35 / 288 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) +
    C (-239 / 864 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (125 / 72 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) +
    C (-17 / 24 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-1 / 128 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (-7 / 4 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (175 / 48 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-139 / 24 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) +
    C (3 / 16 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-1 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (25 / 4 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ)

private theorem compactH5_eq : modularThetaLyapunovNormalizedHJet 5 = compactH5 := by

  rw [modularThetaLyapunovNormalizedHJet, compactH4_eq]
  apply MvPolynomial.funext
  intro v
  simp [compactH4, compactH5, modularThetaLyapunovNormalizedLie,
    modularThetaLyapunovLie, pderiv_mul, pderiv_pow, pderiv_C,
    modularThetaLyapunovVectorField,
    show (Finset.univ : Finset ModularThetaLyapunovState) = {.S, .A, .W} by decide]
  all_goals ring

private def compactH6 : ModularThetaLyapunovPolynomial :=
  C (385 / 1728 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) +
    C (6439 / 10368 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-3325 / 864 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) +
    C (181 / 216 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (241 / 768 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (95 / 24 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-2375 / 288 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (889 / 48 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) +
    C (-13 / 16 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (17 / 3 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-95 / 4 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (51 / 512 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (-15 / 16 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (95 / 128 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (2 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (-95 / 4 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (889 / 32 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-139 / 8 : ℂ)

private theorem compactH6_eq : modularThetaLyapunovNormalizedHJet 6 = compactH6 := by

  rw [modularThetaLyapunovNormalizedHJet, compactH5_eq]
  apply MvPolynomial.funext
  intro v
  simp [compactH5, compactH6, modularThetaLyapunovNormalizedLie,
    modularThetaLyapunovLie, pderiv_mul, pderiv_pow, pderiv_C,
    modularThetaLyapunovVectorField,
    show (Finset.univ : Finset ModularThetaLyapunovState) = {.S, .A, .W} by decide]
  all_goals ring

private def compactH7 : ModularThetaLyapunovPolynomial :=
  C (-5005 / 10368 : ℂ) * X ModularThetaLyapunovState.S^(7 : ℕ) +
    C (-108737 / 62208 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (5635 / 576 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) +
    C (-587 / 576 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-26075 / 13824 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (-2797 / 432 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (38479 / 1728 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-5915 / 96 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) +
    C (259 / 192 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-731 / 36 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (2737 / 48 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-915 / 1024 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (231 / 32 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (161 / 256 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (-17 / 1 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (1127 / 8 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-8281 / 64 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (5473 / 48 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) +
    C (-237 / 256 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (7 / 2 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-483 / 32 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-4 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (161 / 2 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-3549 / 16 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ)

private theorem compactH7_eq : modularThetaLyapunovNormalizedHJet 7 = compactH7 := by

  rw [modularThetaLyapunovNormalizedHJet, compactH6_eq]
  apply MvPolynomial.funext
  intro v
  simp [compactH6, compactH7, modularThetaLyapunovNormalizedLie,
    modularThetaLyapunovLie, pderiv_mul, pderiv_pow, pderiv_C,
    modularThetaLyapunovVectorField,
    show (Finset.univ : Finset ModularThetaLyapunovState) = {.S, .A, .W} by decide]
  all_goals ring

private def compactH8 : ModularThetaLyapunovPolynomial :=
  C (25025 / 20736 : ℂ) * X ModularThetaLyapunovState.S^(8 : ℕ) +
    C (514381 / 93312 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-2695 / 96 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) +
    C (407 / 144 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (118135 / 13824 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (75 / 16 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-45073 / 576 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (62965 / 288 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) +
    C (85 / 16 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (1495 / 27 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-1267 / 12 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (7925 / 1536 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (-515 / 16 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-5061 / 128 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (90 / 1 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (-1995 / 4 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (44975 / 96 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-14677 / 24 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) +
    C (725 / 64 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-40 / 1 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (819 / 8 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (48 / 1 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (-714 / 1 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (5397 / 4 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (849 / 4096 : ℂ) * X ModularThetaLyapunovState.A^(4 : ℕ) +
    C (345 / 64 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-3213 / 256 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (-45 / 4 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (945 / 8 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-5397 / 128 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (8 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(6 : ℕ) +
    C (-252 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (5397 / 4 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-14677 / 16 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (5473 / 16 : ℂ)

private theorem compactH8_eq : modularThetaLyapunovNormalizedHJet 8 = compactH8 := by

  rw [modularThetaLyapunovNormalizedHJet, compactH7_eq]
  apply MvPolynomial.funext
  intro v
  simp [compactH7, compactH8, modularThetaLyapunovNormalizedLie,
    modularThetaLyapunovLie, pderiv_mul, pderiv_pow, pderiv_C,
    modularThetaLyapunovVectorField,
    show (Finset.univ : Finset ModularThetaLyapunovState) = {.S, .A, .W} by decide]
  all_goals ring

private def compactH9 : ModularThetaLyapunovPolynomial :=
  C (-425425 / 124416 : ℂ) * X ModularThetaLyapunovState.S^(9 : ℕ) +
    C (-10389355 / 559872 : ℂ) * X ModularThetaLyapunovState.S^(7 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (155155 / 1728 : ℂ) * X ModularThetaLyapunovState.S^(7 : ℕ) +
    C (-746851 / 46656 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-2905603 / 82944 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (46603 / 2592 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (3370847 / 10368 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-159985 / 192 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) +
    C (-221665 / 3456 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-67855 / 648 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (18197 / 96 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-228215 / 9216 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (26155 / 288 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (808325 / 2304 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (-10055 / 27 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (86707 / 72 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-1092469 / 576 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (451175 / 144 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) +
    C (-21995 / 256 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (1645 / 6 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-8029 / 32 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-1060 / 3 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (22661 / 6 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-77707 / 16 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-17283 / 8192 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(4 : ℕ) +
    C (-11235 / 128 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (85095 / 512 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (1415 / 8 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (-21483 / 16 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-13713 / 256 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (-388 / 3 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(6 : ℕ) +
    C (3162 / 1 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (-95991 / 8 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (631645 / 96 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-357721 / 96 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) +
    C (-2439 / 512 : ℂ) * X ModularThetaLyapunovState.A^(4 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-795 / 32 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (22041 / 128 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (33 / 1 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (-651 / 1 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (41139 / 32 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-16 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(7 : ℕ) +
    C (744 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (-13713 / 2 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (90235 / 8 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ)

private theorem compactH9_eq : modularThetaLyapunovNormalizedHJet 9 = compactH9 := by

  rw [modularThetaLyapunovNormalizedHJet, compactH8_eq]
  apply MvPolynomial.funext
  intro v
  simp [compactH8, compactH9, modularThetaLyapunovNormalizedLie,
    modularThetaLyapunovLie, pderiv_mul, pderiv_pow, pderiv_C,
    modularThetaLyapunovVectorField,
    show (Finset.univ : Finset ModularThetaLyapunovState) = {.S, .A, .W} by decide]
  all_goals ring

private def compactH10 : ModularThetaLyapunovPolynomial :=
  C (8083075 / 746496 : ℂ) * X ModularThetaLyapunovState.S^(10 : ℕ) +
    C (885697661 / 13436928 : ℂ) * X ModularThetaLyapunovState.S^(8 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-4379375 / 13824 : ℂ) * X ModularThetaLyapunovState.S^(8 : ℕ) +
    C (4220461 / 46656 : ℂ) * X ModularThetaLyapunovState.S^(7 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (208106413 / 1492992 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (-4419709 / 46656 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-90016675 / 62208 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (3932005 / 1152 : ℂ) * X ModularThetaLyapunovState.S^(6 : ℕ) +
    C (4245367 / 10368 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-947 / 1944 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-71225 / 96 : ℂ) * X ModularThetaLyapunovState.S^(5 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (12064865 / 110592 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (-4685 / 384 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-20673625 / 9216 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (134395 / 108 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (-39375 / 32 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (65761507 / 6912 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-27914425 / 1728 : ℂ) * X ModularThetaLyapunovState.S^(4 : ℕ) +
    C (1201945 / 2304 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-38165 / 27 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-44625 / 32 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (55204 / 27 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (-261625 / 18 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (1848553 / 144 : ℂ) * X ModularThetaLyapunovState.S^(3 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (208959 / 16384 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(4 : ℕ) +
    C (221895 / 256 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-1386875 / 1024 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (-79945 / 48 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (270375 / 32 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (2461333 / 512 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (11374 / 9 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(6 : ℕ) +
    C (-23625 / 1 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (970235 / 16 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-19938875 / 576 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (5771821 / 192 : ℂ) * X ModularThetaLyapunovState.S^(2 : ℕ) +
    C (31719 / 512 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(4 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (16735 / 32 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-380625 / 128 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-681 / 1 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (10500 / 1 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-398307 / 32 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (336 / 1 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(7 : ℕ) +
    C (-12600 / 1 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(5 : ℕ) +
    C (173621 / 2 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(3 : ℕ) +
    C (-797555 / 8 : ℂ) * X ModularThetaLyapunovState.S^(1 : ℕ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(1 : ℕ) +
    C (-26199 / 32768 : ℂ) * X ModularThetaLyapunovState.A^(5 : ℕ) +
    C (34137 / 512 : ℂ) * X ModularThetaLyapunovState.A^(4 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (-445725 / 8192 : ℂ) * X ModularThetaLyapunovState.A^(4 : ℕ) +
    C (3165 / 32 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (-181125 / 128 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (1562589 / 1024 : ℂ) * X ModularThetaLyapunovState.A^(3 : ℕ) +
    C (-91 / 1 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(6 : ℕ) +
    C (23625 / 8 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (-459585 / 32 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (797555 / 256 : ℂ) * X ModularThetaLyapunovState.A^(2 : ℕ) +
    C (32 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(8 : ℕ) +
    C (-2100 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(6 : ℕ) +
    C (30639 / 1 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(4 : ℕ) +
    C (-797555 / 8 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) * X ModularThetaLyapunovState.W^(2 : ℕ) +
    C (5771821 / 128 : ℂ) * X ModularThetaLyapunovState.A^(1 : ℕ) +
    C (-357721 / 32 : ℂ)

private theorem compactH10_eq : modularThetaLyapunovNormalizedHJet 10 = compactH10 := by

  rw [modularThetaLyapunovNormalizedHJet, compactH9_eq]
  apply MvPolynomial.funext
  intro v
  simp [compactH9, compactH10, modularThetaLyapunovNormalizedLie,
    modularThetaLyapunovLie, pderiv_mul, pderiv_pow, pderiv_C,
    modularThetaLyapunovVectorField,
    show (Finset.univ : Finset ModularThetaLyapunovState) = {.S, .A, .W} by decide]
  all_goals ring

/- Monomial group 0 of the exact D1 expansion. -/
def modularThetaCompactD1Part0 (S A W : ℝ) : ℝ :=
  ((((((4704000 : ℝ) * S^(24 : ℕ) +
    ((58720640 : ℝ) * S^(22 : ℕ) * A^(1 : ℕ) +
    (-463680000 : ℝ) * S^(22 : ℕ))) +
    (((55928320 : ℝ) * S^(21 : ℕ) * A^(1 : ℕ) * W^(1 : ℕ) +
    (312019792 : ℝ) * S^(20 : ℕ) * A^(2 : ℕ)) +
    ((274341120 : ℝ) * S^(20 : ℕ) * A^(1 : ℕ) * W^(2 : ℕ) +
    (-5815173120 : ℝ) * S^(20 : ℕ) * A^(1 : ℕ)))) +
    ((((20876486400 : ℝ) * S^(20 : ℕ) +
    (471293952 : ℝ) * S^(19 : ℕ) * A^(2 : ℕ) * W^(1 : ℕ)) +
    ((-350818560 : ℝ) * S^(19 : ℕ) * A^(1 : ℕ) * W^(3 : ℕ) +
    (-5165614080 : ℝ) * S^(19 : ℕ) * A^(1 : ℕ) * W^(1 : ℕ))) +
    (((914942304 : ℝ) * S^(18 : ℕ) * A^(3 : ℕ) +
    (3335316480 : ℝ) * S^(18 : ℕ) * A^(2 : ℕ) * W^(2 : ℕ)) +
    ((-31241500128 : ℝ) * S^(18 : ℕ) * A^(2 : ℕ) +
    (-471916800 : ℝ) * S^(18 : ℕ) * A^(1 : ℕ) * W^(4 : ℕ))))) +
    ((((-16539863040 : ℝ) * S^(18 : ℕ) * A^(1 : ℕ) * W^(2 : ℕ) +
    ((261134409600 : ℝ) * S^(18 : ℕ) * A^(1 : ℕ) +
    (-567486259200 : ℝ) * S^(18 : ℕ))) +
    (((1372119552 : ℝ) * S^(17 : ℕ) * A^(3 : ℕ) * W^(1 : ℕ) +
    (-1326939840 : ℝ) * S^(17 : ℕ) * A^(2 : ℕ) * W^(3 : ℕ)) +
    ((-49527016704 : ℝ) * S^(17 : ℕ) * A^(2 : ℕ) * W^(1 : ℕ) +
    (1916835840 : ℝ) * S^(17 : ℕ) * A^(1 : ℕ) * W^(5 : ℕ)))) +
    ((((25263083520 : ℝ) * S^(17 : ℕ) * A^(1 : ℕ) * W^(3 : ℕ) +
    (176434951680 : ℝ) * S^(17 : ℕ) * A^(1 : ℕ) * W^(1 : ℕ)) +
    ((1582981389 : ℝ) * S^(16 : ℕ) * A^(4 : ℕ) +
    (15549859008 : ℝ) * S^(16 : ℕ) * A^(3 : ℕ) * W^(2 : ℕ))) +
    (((-93681714672 : ℝ) * S^(16 : ℕ) * A^(3 : ℕ) +
    (-64514880 : ℝ) * S^(16 : ℕ) * A^(2 : ℕ) * W^(4 : ℕ)) +
    ((-196036495488 : ℝ) * S^(16 : ℕ) * A^(2 : ℕ) * W^(2 : ℕ) +
    (1413371704752 : ℝ) * S^(16 : ℕ) * A^(2 : ℕ))))))) / (45137758519296 : ℝ)

/- Monomial group 1 of the exact D1 expansion. -/
def modularThetaCompactD1Part1 (S A W : ℝ) : ℝ :=
  ((((((218142720 : ℝ) * S^(16 : ℕ) * A^(1 : ℕ) * W^(6 : ℕ) +
    ((-494899200 : ℝ) * S^(16 : ℕ) * A^(1 : ℕ) * W^(4 : ℕ) +
    (35862013440 : ℝ) * S^(16 : ℕ) * A^(1 : ℕ) * W^(2 : ℕ))) +
    (((-517558809600 : ℝ) * S^(16 : ℕ) * A^(1 : ℕ) +
    (768013747200 : ℝ) * S^(16 : ℕ)) +
    ((81047648 : ℝ) * S^(15 : ℕ) * A^(4 : ℕ) * W^(1 : ℕ) +
    (116046432 : ℝ) * S^(15 : ℕ) * A^(3 : ℕ) * W^(3 : ℕ)))) +
    ((((-13854406272 : ℝ) * S^(15 : ℕ) * A^(3 : ℕ) * W^(1 : ℕ) +
    (38974464 : ℝ) * S^(15 : ℕ) * A^(2 : ℕ) * W^(5 : ℕ)) +
    ((5876310528 : ℝ) * S^(15 : ℕ) * A^(2 : ℕ) * W^(3 : ℕ) +
    (128464759296 : ℝ) * S^(15 : ℕ) * A^(2 : ℕ) * W^(1 : ℕ))) +
    (((95109120 : ℝ) * S^(15 : ℕ) * A^(1 : ℕ) * W^(7 : ℕ) +
    (-11510968320 : ℝ) * S^(15 : ℕ) * A^(1 : ℕ) * W^(5 : ℕ)) +
    ((-45431746560 : ℝ) * S^(15 : ℕ) * A^(1 : ℕ) * W^(3 : ℕ) +
    (-213847326720 : ℝ) * S^(15 : ℕ) * A^(1 : ℕ) * W^(1 : ℕ))))) +
    ((((109907037 : ℝ) * S^(14 : ℕ) * A^(5 : ℕ) +
    ((2611004784 : ℝ) * S^(14 : ℕ) * A^(4 : ℕ) * W^(2 : ℕ) +
    (-12762427788 : ℝ) * S^(14 : ℕ) * A^(4 : ℕ))) +
    (((2399630688 : ℝ) * S^(14 : ℕ) * A^(3 : ℕ) * W^(4 : ℕ) +
    (-68085278784 : ℝ) * S^(14 : ℕ) * A^(3 : ℕ) * W^(2 : ℕ)) +
    ((319509876960 : ℝ) * S^(14 : ℕ) * A^(3 : ℕ) +
    (-778467456 : ℝ) * S^(14 : ℕ) * A^(2 : ℕ) * W^(6 : ℕ)))) +
    ((((-443276928 : ℝ) * S^(14 : ℕ) * A^(2 : ℕ) * W^(4 : ℕ) +
    (400040211456 : ℝ) * S^(14 : ℕ) * A^(2 : ℕ) * W^(2 : ℕ)) +
    ((-2758697626752 : ℝ) * S^(14 : ℕ) * A^(2 : ℕ) +
    (13271040 : ℝ) * S^(14 : ℕ) * A^(1 : ℕ) * W^(8 : ℕ))) +
    (((-14086586880 : ℝ) * S^(14 : ℕ) * A^(1 : ℕ) * W^(6 : ℕ) +
    (116737044480 : ℝ) * S^(14 : ℕ) * A^(1 : ℕ) * W^(4 : ℕ)) +
    ((-759922145280 : ℝ) * S^(14 : ℕ) * A^(1 : ℕ) * W^(2 : ℕ) +
    (9152270922240 : ℝ) * S^(14 : ℕ) * A^(1 : ℕ))))))) / (3343537668096 : ℝ)

/- Monomial group 2 of the exact D1 expansion. -/
def modularThetaCompactD1Part2 (S A W : ℝ) : ℝ :=
  ((((((-26480601907200 : ℝ) * S^(14 : ℕ) +
    ((-359446976 : ℝ) * S^(13 : ℕ) * A^(5 : ℕ) * W^(1 : ℕ) +
    (1012974528 : ℝ) * S^(13 : ℕ) * A^(4 : ℕ) * W^(3 : ℕ))) +
    (((-64239977472 : ℝ) * S^(13 : ℕ) * A^(4 : ℕ) * W^(1 : ℕ) +
    (-1005626880 : ℝ) * S^(13 : ℕ) * A^(3 : ℕ) * W^(5 : ℕ)) +
    ((-58227669504 : ℝ) * S^(13 : ℕ) * A^(3 : ℕ) * W^(3 : ℕ) +
    (1405278950400 : ℝ) * S^(13 : ℕ) * A^(3 : ℕ) * W^(1 : ℕ)))) +
    ((((5669498880 : ℝ) * S^(13 : ℕ) * A^(2 : ℕ) * W^(7 : ℕ) +
    (-1784291328 : ℝ) * S^(13 : ℕ) * A^(2 : ℕ) * W^(5 : ℕ)) +
    ((-468462071808 : ℝ) * S^(13 : ℕ) * A^(2 : ℕ) * W^(3 : ℕ) +
    (-5528406601728 : ℝ) * S^(13 : ℕ) * A^(2 : ℕ) * W^(1 : ℕ))) +
    (((-15407677440 : ℝ) * S^(13 : ℕ) * A^(1 : ℕ) * W^(7 : ℕ) +
    (1066553671680 : ℝ) * S^(13 : ℕ) * A^(1 : ℕ) * W^(5 : ℕ)) +
    ((630102343680 : ℝ) * S^(13 : ℕ) * A^(1 : ℕ) * W^(3 : ℕ) +
    (4036274012160 : ℝ) * S^(13 : ℕ) * A^(1 : ℕ) * W^(1 : ℕ))))) +
    ((((17701947 : ℝ) * S^(12 : ℕ) * A^(6 : ℕ) +
    ((7738116096 : ℝ) * S^(12 : ℕ) * A^(5 : ℕ) * W^(2 : ℕ) +
    (-40877887920 : ℝ) * S^(12 : ℕ) * A^(5 : ℕ))) +
    (((31535800128 : ℝ) * S^(12 : ℕ) * A^(4 : ℕ) * W^(4 : ℕ) +
    (-441534540672 : ℝ) * S^(12 : ℕ) * A^(4 : ℕ) * W^(2 : ℕ)) +
    ((1595612821392 : ℝ) * S^(12 : ℕ) * A^(4 : ℕ) +
    (-18565314048 : ℝ) * S^(12 : ℕ) * A^(3 : ℕ) * W^(6 : ℕ)))) +
    ((((-228141114624 : ℝ) * S^(12 : ℕ) * A^(3 : ℕ) * W^(4 : ℕ) +
    (4768766535168 : ℝ) * S^(12 : ℕ) * A^(3 : ℕ) * W^(2 : ℕ)) +
    ((-22144950498816 : ℝ) * S^(12 : ℕ) * A^(3 : ℕ) +
    (22083010560 : ℝ) * S^(12 : ℕ) * A^(2 : ℕ) * W^(8 : ℕ))) +
    (((-106310071296 : ℝ) * S^(12 : ℕ) * A^(2 : ℕ) * W^(6 : ℕ) +
    (610246960128 : ℝ) * S^(12 : ℕ) * A^(2 : ℕ) * W^(4 : ℕ)) +
    ((-19317862305792 : ℝ) * S^(12 : ℕ) * A^(2 : ℕ) * W^(2 : ℕ) +
    (124131281075712 : ℝ) * S^(12 : ℕ) * A^(2 : ℕ))))))) / (8916100448256 : ℝ)

/- Monomial group 3 of the exact D1 expansion. -/
def modularThetaCompactD1Part3 (S A W : ℝ) : ℝ :=
  ((((((-238878720 : ℝ) * S^(12 : ℕ) * A^(1 : ℕ) * W^(8 : ℕ) +
    ((117145128960 : ℝ) * S^(12 : ℕ) * A^(1 : ℕ) * W^(6 : ℕ) +
    (-1221623562240 : ℝ) * S^(12 : ℕ) * A^(1 : ℕ) * W^(4 : ℕ))) +
    (((4027651153920 : ℝ) * S^(12 : ℕ) * A^(1 : ℕ) * W^(2 : ℕ) +
    (-33303820861440 : ℝ) * S^(12 : ℕ) * A^(1 : ℕ)) +
    ((27587356876800 : ℝ) * S^(12 : ℕ) +
    (-52246208 : ℝ) * S^(11 : ℕ) * A^(6 : ℕ) * W^(1 : ℕ)))) +
    ((((-857152384 : ℝ) * S^(11 : ℕ) * A^(5 : ℕ) * W^(3 : ℕ) +
    (-3143819008 : ℝ) * S^(11 : ℕ) * A^(5 : ℕ) * W^(1 : ℕ)) +
    ((948109824 : ℝ) * S^(11 : ℕ) * A^(4 : ℕ) * W^(5 : ℕ) +
    (-31987089792 : ℝ) * S^(11 : ℕ) * A^(4 : ℕ) * W^(3 : ℕ))) +
    (((346083083520 : ℝ) * S^(11 : ℕ) * A^(4 : ℕ) * W^(1 : ℕ) +
    (-2029068288 : ℝ) * S^(11 : ℕ) * A^(3 : ℕ) * W^(7 : ℕ)) +
    ((36810187776 : ℝ) * S^(11 : ℕ) * A^(3 : ℕ) * W^(5 : ℕ) +
    (157696503552 : ℝ) * S^(11 : ℕ) * A^(3 : ℕ) * W^(3 : ℕ))))) +
    ((((-2545815720960 : ℝ) * S^(11 : ℕ) * A^(3 : ℕ) * W^(1 : ℕ) +
    ((2813460480 : ℝ) * S^(11 : ℕ) * A^(2 : ℕ) * W^(9 : ℕ) +
    (-80286031872 : ℝ) * S^(11 : ℕ) * A^(2 : ℕ) * W^(7 : ℕ))) +
    (((229424652288 : ℝ) * S^(11 : ℕ) * A^(2 : ℕ) * W^(5 : ℕ) +
    (686597492736 : ℝ) * S^(11 : ℕ) * A^(2 : ℕ) * W^(3 : ℕ)) +
    ((4300823457792 : ℝ) * S^(11 : ℕ) * A^(2 : ℕ) * W^(1 : ℕ) +
    (44511068160 : ℝ) * S^(11 : ℕ) * A^(1 : ℕ) * W^(7 : ℕ)))) +
    ((((-2315278909440 : ℝ) * S^(11 : ℕ) * A^(1 : ℕ) * W^(5 : ℕ) +
    (2846515322880 : ℝ) * S^(11 : ℕ) * A^(1 : ℕ) * W^(3 : ℕ)) +
    ((934851870720 : ℝ) * S^(11 : ℕ) * A^(1 : ℕ) * W^(1 : ℕ) +
    (-44328927 : ℝ) * S^(10 : ℕ) * A^(7 : ℕ))) +
    (((444481224 : ℝ) * S^(10 : ℕ) * A^(6 : ℕ) * W^(2 : ℕ) +
    (-4121461314 : ℝ) * S^(10 : ℕ) * A^(6 : ℕ)) +
    ((6986684928 : ℝ) * S^(10 : ℕ) * A^(5 : ℕ) * W^(4 : ℕ) +
    (-67169977632 : ℝ) * S^(10 : ℕ) * A^(5 : ℕ) * W^(2 : ℕ))))))) / (990677827584 : ℝ)

/- Monomial group 4 of the exact D1 expansion. -/
def modularThetaCompactD1Part4 (S A W : ℝ) : ℝ :=
  ((((((5720847438 : ℝ) * S^(10 : ℕ) * A^(5 : ℕ) +
    ((-64221760 : ℝ) * S^(10 : ℕ) * A^(4 : ℕ) * W^(6 : ℕ) +
    (-3446352832 : ℝ) * S^(10 : ℕ) * A^(4 : ℕ) * W^(4 : ℕ))) +
    (((33604536288 : ℝ) * S^(10 : ℕ) * A^(4 : ℕ) * W^(2 : ℕ) +
    (-126956322832 : ℝ) * S^(10 : ℕ) * A^(4 : ℕ)) +
    ((-57618432 : ℝ) * S^(10 : ℕ) * A^(3 : ℕ) * W^(8 : ℕ) +
    (2557896192 : ℝ) * S^(10 : ℕ) * A^(3 : ℕ) * W^(6 : ℕ)))) +
    ((((5542195776 : ℝ) * S^(10 : ℕ) * A^(3 : ℕ) * W^(4 : ℕ) +
    (-233784616320 : ℝ) * S^(10 : ℕ) * A^(3 : ℕ) * W^(2 : ℕ)) +
    ((1086978466752 : ℝ) * S^(10 : ℕ) * A^(3 : ℕ) +
    (39518208 : ℝ) * S^(10 : ℕ) * A^(2 : ℕ) * W^(10 : ℕ))) +
    (((-4021567488 : ℝ) * S^(10 : ℕ) * A^(2 : ℕ) * W^(8 : ℕ) +
    (32308008192 : ℝ) * S^(10 : ℕ) * A^(2 : ℕ) * W^(6 : ℕ)) +
    ((-115441042176 : ℝ) * S^(10 : ℕ) * A^(2 : ℕ) * W^(4 : ℕ) +
    (851360698368 : ℝ) * S^(10 : ℕ) * A^(2 : ℕ) * W^(2 : ℕ))))) +
    ((((-4336111526400 : ℝ) * S^(10 : ℕ) * A^(2 : ℕ) +
    ((172523520 : ℝ) * S^(10 : ℕ) * A^(1 : ℕ) * W^(8 : ℕ) +
    (-51801431040 : ℝ) * S^(10 : ℕ) * A^(1 : ℕ) * W^(6 : ℕ))) +
    (((602248919040 : ℝ) * S^(10 : ℕ) * A^(1 : ℕ) * W^(4 : ℕ) +
    (-1604934881280 : ℝ) * S^(10 : ℕ) * A^(1 : ℕ) * W^(2 : ℕ)) +
    ((8077431352320 : ℝ) * S^(10 : ℕ) * A^(1 : ℕ) +
    (-5245328793600 : ℝ) * S^(10 : ℕ)))) +
    ((((2348363 : ℝ) * S^(9 : ℕ) * A^(7 : ℕ) * W^(1 : ℕ) +
    (-94698916 : ℝ) * S^(9 : ℕ) * A^(6 : ℕ) * W^(3 : ℕ)) +
    ((249390536 : ℝ) * S^(9 : ℕ) * A^(6 : ℕ) * W^(1 : ℕ) +
    (120380672 : ℝ) * S^(9 : ℕ) * A^(5 : ℕ) * W^(5 : ℕ))) +
    (((-1219500976 : ℝ) * S^(9 : ℕ) * A^(5 : ℕ) * W^(3 : ℕ) +
    (12532648336 : ℝ) * S^(9 : ℕ) * A^(5 : ℕ) * W^(1 : ℕ)) +
    ((17454336 : ℝ) * S^(9 : ℕ) * A^(4 : ℕ) * W^(7 : ℕ) +
    (71686272 : ℝ) * S^(9 : ℕ) * A^(4 : ℕ) * W^(5 : ℕ))))))) / (27518828544 : ℝ)

/- Monomial group 5 of the exact D1 expansion. -/
def modularThetaCompactD1Part5 (S A W : ℝ) : ℝ :=
  ((((((152425244416 : ℝ) * S^(9 : ℕ) * A^(4 : ℕ) * W^(3 : ℕ) +
    ((-868298190848 : ℝ) * S^(9 : ℕ) * A^(4 : ℕ) * W^(1 : ℕ) +
    (-391643136 : ℝ) * S^(9 : ℕ) * A^(3 : ℕ) * W^(9 : ℕ))) +
    (((10026221568 : ℝ) * S^(9 : ℕ) * A^(3 : ℕ) * W^(7 : ℕ) +
    (-128850425856 : ℝ) * S^(9 : ℕ) * A^(3 : ℕ) * W^(5 : ℕ)) +
    ((-70542409728 : ℝ) * S^(9 : ℕ) * A^(3 : ℕ) * W^(3 : ℕ) +
    (2481192505344 : ℝ) * S^(9 : ℕ) * A^(3 : ℕ) * W^(1 : ℕ)))) +
    ((((37748736 : ℝ) * S^(9 : ℕ) * A^(2 : ℕ) * W^(11 : ℕ) +
    (-18246795264 : ℝ) * S^(9 : ℕ) * A^(2 : ℕ) * W^(9 : ℕ)) +
    ((413788520448 : ℝ) * S^(9 : ℕ) * A^(2 : ℕ) * W^(7 : ℕ) +
    (-1560036999168 : ℝ) * S^(9 : ℕ) * A^(2 : ℕ) * W^(5 : ℕ))) +
    (((370166243328 : ℝ) * S^(9 : ℕ) * A^(2 : ℕ) * W^(3 : ℕ) +
    (406208397312 : ℝ) * S^(9 : ℕ) * A^(2 : ℕ) * W^(1 : ℕ)) +
    ((-95109120000 : ℝ) * S^(9 : ℕ) * A^(1 : ℕ) * W^(7 : ℕ) +
    (4133928960000 : ℝ) * S^(9 : ℕ) * A^(1 : ℕ) * W^(5 : ℕ))))) +
    ((((-9934461665280 : ℝ) * S^(9 : ℕ) * A^(1 : ℕ) * W^(3 : ℕ) +
    ((-6253747568640 : ℝ) * S^(9 : ℕ) * A^(1 : ℕ) * W^(1 : ℕ) +
    (-11055545 : ℝ) * S^(8 : ℕ) * A^(8 : ℕ))) +
    (((59825184 : ℝ) * S^(8 : ℕ) * A^(7 : ℕ) * W^(2 : ℕ) +
    (-564584068 : ℝ) * S^(8 : ℕ) * A^(7 : ℕ)) +
    ((775576160 : ℝ) * S^(8 : ℕ) * A^(6 : ℕ) * W^(4 : ℕ) +
    (-7241334816 : ℝ) * S^(8 : ℕ) * A^(6 : ℕ) * W^(2 : ℕ)))) +
    ((((20576648588 : ℝ) * S^(8 : ℕ) * A^(6 : ℕ) +
    (-387204608 : ℝ) * S^(8 : ℕ) * A^(5 : ℕ) * W^(6 : ℕ)) +
    ((-30694479232 : ℝ) * S^(8 : ℕ) * A^(5 : ℕ) * W^(4 : ℕ) +
    (222742001792 : ℝ) * S^(8 : ℕ) * A^(5 : ℕ) * W^(2 : ℕ))) +
    (((-793923272512 : ℝ) * S^(8 : ℕ) * A^(5 : ℕ) +
    (1280507904 : ℝ) * S^(8 : ℕ) * A^(4 : ℕ) * W^(8 : ℕ)) +
    ((3306157056 : ℝ) * S^(8 : ℕ) * A^(4 : ℕ) * W^(6 : ℕ) +
    (178968214272 : ℝ) * S^(8 : ℕ) * A^(4 : ℕ) * W^(4 : ℕ))))))) / (146767085568 : ℝ)

/- Monomial group 6 of the exact D1 expansion. -/
def modularThetaCompactD1Part6 (S A W : ℝ) : ℝ :=
  ((((((-207855942784 : ℝ) * S^(8 : ℕ) * A^(4 : ℕ) * W^(2 : ℕ) +
    ((835774356432 : ℝ) * S^(8 : ℕ) * A^(4 : ℕ) +
    (-8257536 : ℝ) * S^(8 : ℕ) * A^(3 : ℕ) * W^(10 : ℕ))) +
    (((863207424 : ℝ) * S^(8 : ℕ) * A^(3 : ℕ) * W^(8 : ℕ) +
    (-17094925824 : ℝ) * S^(8 : ℕ) * A^(3 : ℕ) * W^(6 : ℕ)) +
    ((-24364197120 : ℝ) * S^(8 : ℕ) * A^(3 : ℕ) * W^(4 : ℕ) +
    (1201178230272 : ℝ) * S^(8 : ℕ) * A^(3 : ℕ) * W^(2 : ℕ)))) +
    ((((-4864347554304 : ℝ) * S^(8 : ℕ) * A^(3 : ℕ) +
    (-672399360 : ℝ) * S^(8 : ℕ) * A^(2 : ℕ) * W^(10 : ℕ)) +
    ((41197436928 : ℝ) * S^(8 : ℕ) * A^(2 : ℕ) * W^(8 : ℕ) +
    (-375290164224 : ℝ) * S^(8 : ℕ) * A^(2 : ℕ) * W^(6 : ℕ))) +
    (((1283331419136 : ℝ) * S^(8 : ℕ) * A^(2 : ℕ) * W^(4 : ℕ) +
    (-4456425996288 : ℝ) * S^(8 : ℕ) * A^(2 : ℕ) * W^(2 : ℕ)) +
    ((14979044860416 : ℝ) * S^(8 : ℕ) * A^(2 : ℕ) +
    (-1105920000 : ℝ) * S^(8 : ℕ) * A^(1 : ℕ) * W^(8 : ℕ))))) +
    ((((227120025600 : ℝ) * S^(8 : ℕ) * A^(1 : ℕ) * W^(6 : ℕ) +
    ((-2833267507200 : ℝ) * S^(8 : ℕ) * A^(1 : ℕ) * W^(4 : ℕ) +
    (7410103050240 : ℝ) * S^(8 : ℕ) * A^(1 : ℕ) * W^(2 : ℕ))) +
    (((-22414244659200 : ℝ) * S^(8 : ℕ) * A^(1 : ℕ) +
    (11548815667200 : ℝ) * S^(8 : ℕ)) +
    ((2021619 : ℝ) * S^(7 : ℕ) * A^(8 : ℕ) * W^(1 : ℕ) +
    (-53083292 : ℝ) * S^(7 : ℕ) * A^(7 : ℕ) * W^(3 : ℕ)))) +
    ((((196219348 : ℝ) * S^(7 : ℕ) * A^(7 : ℕ) * W^(1 : ℕ) +
    (90494656 : ℝ) * S^(7 : ℕ) * A^(6 : ℕ) * W^(5 : ℕ)) +
    ((-261868800 : ℝ) * S^(7 : ℕ) * A^(6 : ℕ) * W^(3 : ℕ) +
    (4403742400 : ℝ) * S^(7 : ℕ) * A^(6 : ℕ) * W^(1 : ℕ))) +
    (((-187764736 : ℝ) * S^(7 : ℕ) * A^(5 : ℕ) * W^(7 : ℕ) +
    (-165878016 : ℝ) * S^(7 : ℕ) * A^(5 : ℕ) * W^(5 : ℕ)) +
    ((22356582400 : ℝ) * S^(7 : ℕ) * A^(5 : ℕ) * W^(3 : ℕ) +
    (-101851517440 : ℝ) * S^(7 : ℕ) * A^(5 : ℕ) * W^(1 : ℕ))))))) / (12230590464 : ℝ)

/- Monomial group 7 of the exact D1 expansion. -/
def modularThetaCompactD1Part7 (S A W : ℝ) : ℝ :=
  ((((((129499136 : ℝ) * S^(7 : ℕ) * A^(4 : ℕ) * W^(9 : ℕ) +
    ((-926203904 : ℝ) * S^(7 : ℕ) * A^(4 : ℕ) * W^(7 : ℕ) +
    (4663816192 : ℝ) * S^(7 : ℕ) * A^(4 : ℕ) * W^(5 : ℕ))) +
    (((-173810609152 : ℝ) * S^(7 : ℕ) * A^(4 : ℕ) * W^(3 : ℕ) +
    (582674007040 : ℝ) * S^(7 : ℕ) * A^(4 : ℕ) * W^(1 : ℕ)) +
    ((1428160512 : ℝ) * S^(7 : ℕ) * A^(3 : ℕ) * W^(9 : ℕ) +
    (-11253645312 : ℝ) * S^(7 : ℕ) * A^(3 : ℕ) * W^(7 : ℕ)))) +
    ((((74032128000 : ℝ) * S^(7 : ℕ) * A^(3 : ℕ) * W^(5 : ℕ) +
    (-210383981568 : ℝ) * S^(7 : ℕ) * A^(3 : ℕ) * W^(3 : ℕ)) +
    ((162319552512 : ℝ) * S^(7 : ℕ) * A^(3 : ℕ) * W^(1 : ℕ) +
    (-150994944 : ℝ) * S^(7 : ℕ) * A^(2 : ℕ) * W^(11 : ℕ))) +
    (((35474374656 : ℝ) * S^(7 : ℕ) * A^(2 : ℕ) * W^(9 : ℕ) +
    (-735860293632 : ℝ) * S^(7 : ℕ) * A^(2 : ℕ) * W^(7 : ℕ)) +
    ((3185082335232 : ℝ) * S^(7 : ℕ) * A^(2 : ℕ) * W^(5 : ℕ) +
    (-3139193290752 : ℝ) * S^(7 : ℕ) * A^(2 : ℕ) * W^(3 : ℕ))))) +
    ((((-3858253627392 : ℝ) * S^(7 : ℕ) * A^(2 : ℕ) * W^(1 : ℕ) +
    ((91304755200 : ℝ) * S^(7 : ℕ) * A^(1 : ℕ) * W^(7 : ℕ) +
    (-3504456990720 : ℝ) * S^(7 : ℕ) * A^(1 : ℕ) * W^(5 : ℕ))) +
    (((11342173962240 : ℝ) * S^(7 : ℕ) * A^(1 : ℕ) * W^(3 : ℕ) +
    (5358102773760 : ℝ) * S^(7 : ℕ) * A^(1 : ℕ) * W^(1 : ℕ)) +
    ((-1040851 : ℝ) * S^(6 : ℕ) * A^(9 : ℕ) +
    (12869444 : ℝ) * S^(6 : ℕ) * A^(8 : ℕ) * W^(2 : ℕ)))) +
    ((((-59348865 : ℝ) * S^(6 : ℕ) * A^(8 : ℕ) +
    (-16863392 : ℝ) * S^(6 : ℕ) * A^(7 : ℕ) * W^(4 : ℕ)) +
    ((-158809168 : ℝ) * S^(6 : ℕ) * A^(7 : ℕ) * W^(2 : ℕ) +
    (651210184 : ℝ) * S^(6 : ℕ) * A^(7 : ℕ))) +
    (((232641280 : ℝ) * S^(6 : ℕ) * A^(6 : ℕ) * W^(6 : ℕ) +
    (-3241035264 : ℝ) * S^(6 : ℕ) * A^(6 : ℕ) * W^(4 : ℕ)) +
    ((16755853888 : ℝ) * S^(6 : ℕ) * A^(6 : ℕ) * W^(2 : ℕ) +
    (-63534256784 : ℝ) * S^(6 : ℕ) * A^(6 : ℕ))))))) / (16307453952 : ℝ)

/- Monomial group 8 of the exact D1 expansion. -/
def modularThetaCompactD1Part8 (S A W : ℝ) : ℝ :=
  ((((((-466714624 : ℝ) * S^(6 : ℕ) * A^(5 : ℕ) * W^(8 : ℕ) +
    ((1627916288 : ℝ) * S^(6 : ℕ) * A^(5 : ℕ) * W^(6 : ℕ) +
    (51770248192 : ℝ) * S^(6 : ℕ) * A^(5 : ℕ) * W^(4 : ℕ))) +
    (((-574061925888 : ℝ) * S^(6 : ℕ) * A^(5 : ℕ) * W^(2 : ℕ) +
    (2396229423552 : ℝ) * S^(6 : ℕ) * A^(5 : ℕ)) +
    ((73924608 : ℝ) * S^(6 : ℕ) * A^(4 : ℕ) * W^(10 : ℕ) +
    (-10395451392 : ℝ) * S^(6 : ℕ) * A^(4 : ℕ) * W^(8 : ℕ)))) +
    ((((7745654784 : ℝ) * S^(6 : ℕ) * A^(4 : ℕ) * W^(6 : ℕ) +
    (-148343095296 : ℝ) * S^(6 : ℕ) * A^(4 : ℕ) * W^(4 : ℕ)) +
    ((5225471419392 : ℝ) * S^(6 : ℕ) * A^(4 : ℕ) * W^(2 : ℕ) +
    (-19040311905024 : ℝ) * S^(6 : ℕ) * A^(4 : ℕ))) +
    (((622854144 : ℝ) * S^(6 : ℕ) * A^(3 : ℕ) * W^(10 : ℕ) +
    (-30357061632 : ℝ) * S^(6 : ℕ) * A^(3 : ℕ) * W^(8 : ℕ)) +
    ((207836282880 : ℝ) * S^(6 : ℕ) * A^(3 : ℕ) * W^(6 : ℕ) +
    (2863423604736 : ℝ) * S^(6 : ℕ) * A^(3 : ℕ) * W^(4 : ℕ))))) +
    ((((-29318620557312 : ℝ) * S^(6 : ℕ) * A^(3 : ℕ) * W^(2 : ℕ) +
    ((83844277585920 : ℝ) * S^(6 : ℕ) * A^(3 : ℕ) +
    (26612858880 : ℝ) * S^(6 : ℕ) * A^(2 : ℕ) * W^(10 : ℕ))) +
    (((-1272009719808 : ℝ) * S^(6 : ℕ) * A^(2 : ℕ) * W^(8 : ℕ) +
    (12425805471744 : ℝ) * S^(6 : ℕ) * A^(2 : ℕ) * W^(6 : ℕ)) +
    ((-43775832416256 : ℝ) * S^(6 : ℕ) * A^(2 : ℕ) * W^(4 : ℕ) +
    (105519106031616 : ℝ) * S^(6 : ℕ) * A^(2 : ℕ) * W^(2 : ℕ)))) +
    ((((-214864694599680 : ℝ) * S^(6 : ℕ) * A^(2 : ℕ) +
    (25480396800 : ℝ) * S^(6 : ℕ) * A^(1 : ℕ) * W^(8 : ℕ)) +
    ((-3786267525120 : ℝ) * S^(6 : ℕ) * A^(1 : ℕ) * W^(6 : ℕ) +
    (49908665548800 : ℝ) * S^(6 : ℕ) * A^(1 : ℕ) * W^(4 : ℕ))) +
    (((-138709387837440 : ℝ) * S^(6 : ℕ) * A^(1 : ℕ) * W^(2 : ℕ) +
    (263710859673600 : ℝ) * S^(6 : ℕ) * A^(1 : ℕ)) +
    ((-107527672627200 : ℝ) * S^(6 : ℕ) +
    (1493403 : ℝ) * S^(5 : ℕ) * A^(9 : ℕ) * W^(1 : ℕ))))))) / (32614907904 : ℝ)

/- Monomial group 9 of the exact D1 expansion. -/
def modularThetaCompactD1Part9 (S A W : ℝ) : ℝ :=
  ((((((-2293836 : ℝ) * S^(5 : ℕ) * A^(8 : ℕ) * W^(3 : ℕ) +
    ((12090499 : ℝ) * S^(5 : ℕ) * A^(8 : ℕ) * W^(1 : ℕ) +
    (-5835552 : ℝ) * S^(5 : ℕ) * A^(7 : ℕ) * W^(5 : ℕ))) +
    (((29487452 : ℝ) * S^(5 : ℕ) * A^(7 : ℕ) * W^(3 : ℕ) +
    (235601564 : ℝ) * S^(5 : ℕ) * A^(7 : ℕ) * W^(1 : ℕ)) +
    ((14552320 : ℝ) * S^(5 : ℕ) * A^(6 : ℕ) * W^(7 : ℕ) +
    (-104151488 : ℝ) * S^(5 : ℕ) * A^(6 : ℕ) * W^(5 : ℕ)))) +
    ((((2071827808 : ℝ) * S^(5 : ℕ) * A^(6 : ℕ) * W^(3 : ℕ) +
    (-10123058816 : ℝ) * S^(5 : ℕ) * A^(6 : ℕ) * W^(1 : ℕ)) +
    ((-6258688 : ℝ) * S^(5 : ℕ) * A^(5 : ℕ) * W^(9 : ℕ) +
    (536922112 : ℝ) * S^(5 : ℕ) * A^(5 : ℕ) * W^(7 : ℕ))) +
    (((48613120 : ℝ) * S^(5 : ℕ) * A^(5 : ℕ) * W^(5 : ℕ) +
    (-26823042176 : ℝ) * S^(5 : ℕ) * A^(5 : ℕ) * W^(3 : ℕ)) +
    ((61404672192 : ℝ) * S^(5 : ℕ) * A^(5 : ℕ) * W^(1 : ℕ) +
    (786432 : ℝ) * S^(5 : ℕ) * A^(4 : ℕ) * W^(11 : ℕ))))) +
    ((((-248905728 : ℝ) * S^(5 : ℕ) * A^(4 : ℕ) * W^(9 : ℕ) +
    ((2133030912 : ℝ) * S^(5 : ℕ) * A^(4 : ℕ) * W^(7 : ℕ) +
    (-14187236352 : ℝ) * S^(5 : ℕ) * A^(4 : ℕ) * W^(5 : ℕ))) +
    (((34008865344 : ℝ) * S^(5 : ℕ) * A^(4 : ℕ) * W^(3 : ℕ) +
    (18748099584 : ℝ) * S^(5 : ℕ) * A^(4 : ℕ) * W^(1 : ℕ)) +
    ((-1450967040 : ℝ) * S^(5 : ℕ) * A^(3 : ℕ) * W^(9 : ℕ) +
    (493387776 : ℝ) * S^(5 : ℕ) * A^(3 : ℕ) * W^(7 : ℕ)))) +
    ((((60237153792 : ℝ) * S^(5 : ℕ) * A^(3 : ℕ) * W^(5 : ℕ) +
    (28767407616 : ℝ) * S^(5 : ℕ) * A^(3 : ℕ) * W^(3 : ℕ)) +
    ((-783701111808 : ℝ) * S^(5 : ℕ) * A^(3 : ℕ) * W^(1 : ℕ) +
    (169869312 : ℝ) * S^(5 : ℕ) * A^(2 : ℕ) * W^(11 : ℕ))) +
    (((-25841369088 : ℝ) * S^(5 : ℕ) * A^(2 : ℕ) * W^(9 : ℕ) +
    (511455154176 : ℝ) * S^(5 : ℕ) * A^(2 : ℕ) * W^(7 : ℕ)) +
    ((-2433394040832 : ℝ) * S^(5 : ℕ) * A^(2 : ℕ) * W^(5 : ℕ) +
    (3191201501184 : ℝ) * S^(5 : ℕ) * A^(2 : ℕ) * W^(3 : ℕ))))))) / (1358954496 : ℝ)

/- Monomial group 10 of the exact D1 expansion. -/
def modularThetaCompactD1Part10 (S A W : ℝ) : ℝ :=
  ((((((9438262788096 : ℝ) * S^(5 : ℕ) * A^(2 : ℕ) * W^(1 : ℕ) +
    ((-210000936960 : ℝ) * S^(5 : ℕ) * A^(1 : ℕ) * W^(7 : ℕ) +
    (7357960028160 : ℝ) * S^(5 : ℕ) * A^(1 : ℕ) * W^(5 : ℕ))) +
    (((-28443306885120 : ℝ) * S^(5 : ℕ) * A^(1 : ℕ) * W^(3 : ℕ) +
    (-8285322608640 : ℝ) * S^(5 : ℕ) * A^(1 : ℕ) * W^(1 : ℕ)) +
    ((-181945 : ℝ) * S^(4 : ℕ) * A^(10 : ℕ) +
    (4013513 : ℝ) * S^(4 : ℕ) * A^(9 : ℕ) * W^(2 : ℕ)))) +
    ((((-16931793 : ℝ) * S^(4 : ℕ) * A^(9 : ℕ) +
    (3846848 : ℝ) * S^(4 : ℕ) * A^(8 : ℕ) * W^(4 : ℕ)) +
    ((45927792 : ℝ) * S^(4 : ℕ) * A^(8 : ℕ) * W^(2 : ℕ) +
    (-65915260 : ℝ) * S^(4 : ℕ) * A^(8 : ℕ))) +
    (((-15915520 : ℝ) * S^(4 : ℕ) * A^(7 : ℕ) * W^(6 : ℕ) +
    (-604001920 : ℝ) * S^(4 : ℕ) * A^(7 : ℕ) * W^(4 : ℕ)) +
    ((2772739648 : ℝ) * S^(4 : ℕ) * A^(7 : ℕ) * W^(2 : ℕ) +
    (-11206508512 : ℝ) * S^(4 : ℕ) * A^(7 : ℕ))))) +
    ((((29622272 : ℝ) * S^(4 : ℕ) * A^(6 : ℕ) * W^(8 : ℕ) +
    ((-1570278400 : ℝ) * S^(4 : ℕ) * A^(6 : ℕ) * W^(6 : ℕ) +
    (11772803840 : ℝ) * S^(4 : ℕ) * A^(6 : ℕ) * W^(4 : ℕ))) +
    (((-67156760320 : ℝ) * S^(4 : ℕ) * A^(6 : ℕ) * W^(2 : ℕ) +
    (342819155184 : ℝ) * S^(4 : ℕ) * A^(6 : ℕ)) +
    ((-5767168 : ℝ) * S^(4 : ℕ) * A^(5 : ℕ) * W^(10 : ℕ) +
    (1667825664 : ℝ) * S^(4 : ℕ) * A^(5 : ℕ) * W^(8 : ℕ)))) +
    ((((-1713774592 : ℝ) * S^(4 : ℕ) * A^(5 : ℕ) * W^(6 : ℕ) +
    (-26837242880 : ℝ) * S^(4 : ℕ) * A^(5 : ℕ) * W^(4 : ℕ)) +
    ((969757160448 : ℝ) * S^(4 : ℕ) * A^(5 : ℕ) * W^(2 : ℕ) +
    (-3577244815104 : ℝ) * S^(4 : ℕ) * A^(5 : ℕ))) +
    (((-349175808 : ℝ) * S^(4 : ℕ) * A^(4 : ℕ) * W^(10 : ℕ) +
    (28041805824 : ℝ) * S^(4 : ℕ) * A^(4 : ℕ) * W^(8 : ℕ)) +
    ((-31515205632 : ℝ) * S^(4 : ℕ) * A^(4 : ℕ) * W^(6 : ℕ) +
    (363377513472 : ℝ) * S^(4 : ℕ) * A^(4 : ℕ) * W^(4 : ℕ))))))) / (7247757312 : ℝ)

/- Monomial group 11 of the exact D1 expansion. -/
def modularThetaCompactD1Part11 (S A W : ℝ) : ℝ :=
  ((((((-1261673112576 : ℝ) * S^(4 : ℕ) * A^(4 : ℕ) * W^(2 : ℕ) +
    ((3417709905792 : ℝ) * S^(4 : ℕ) * A^(4 : ℕ) +
    (-226492416 : ℝ) * S^(4 : ℕ) * A^(3 : ℕ) * W^(10 : ℕ))) +
    (((7361003520 : ℝ) * S^(4 : ℕ) * A^(3 : ℕ) * W^(8 : ℕ) +
    (41730895872 : ℝ) * S^(4 : ℕ) * A^(3 : ℕ) * W^(6 : ℕ)) +
    ((-1500597811200 : ℝ) * S^(4 : ℕ) * A^(3 : ℕ) * W^(4 : ℕ) +
    (7199494410240 : ℝ) * S^(4 : ℕ) * A^(3 : ℕ) * W^(2 : ℕ)))) +
    ((((-12973036105728 : ℝ) * S^(4 : ℕ) * A^(3 : ℕ) +
    (-6983516160 : ℝ) * S^(4 : ℕ) * A^(2 : ℕ) * W^(10 : ℕ)) +
    ((286994202624 : ℝ) * S^(4 : ℕ) * A^(2 : ℕ) * W^(8 : ℕ) +
    (-2984219172864 : ℝ) * S^(4 : ℕ) * A^(2 : ℕ) * W^(6 : ℕ))) +
    (((11204710981632 : ℝ) * S^(4 : ℕ) * A^(2 : ℕ) * W^(4 : ℕ) +
    (-22995648479232 : ℝ) * S^(4 : ℕ) * A^(2 : ℕ) * W^(2 : ℕ)) +
    ((29188724336640 : ℝ) * S^(4 : ℕ) * A^(2 : ℕ) +
    (-4883742720 : ℝ) * S^(4 : ℕ) * A^(1 : ℕ) * W^(8 : ℕ))))) +
    ((((541604413440 : ℝ) * S^(4 : ℕ) * A^(1 : ℕ) * W^(6 : ℕ) +
    ((-7499677040640 : ℝ) * S^(4 : ℕ) * A^(1 : ℕ) * W^(4 : ℕ) +
    (22930247024640 : ℝ) * S^(4 : ℕ) * A^(1 : ℕ) * W^(2 : ℕ))) +
    (((-29301500805120 : ℝ) * S^(4 : ℕ) * A^(1 : ℕ) +
    (9284618649600 : ℝ) * S^(4 : ℕ)) +
    ((-48785 : ℝ) * S^(3 : ℕ) * A^(10 : ℕ) * W^(1 : ℕ) +
    (-504676 : ℝ) * S^(3 : ℕ) * A^(9 : ℕ) * W^(3 : ℕ)))) +
    ((((-123222 : ℝ) * S^(3 : ℕ) * A^(9 : ℕ) * W^(1 : ℕ) +
    (-1125248 : ℝ) * S^(3 : ℕ) * A^(8 : ℕ) * W^(5 : ℕ)) +
    ((39393024 : ℝ) * S^(3 : ℕ) * A^(8 : ℕ) * W^(3 : ℕ) +
    (55565320 : ℝ) * S^(3 : ℕ) * A^(8 : ℕ) * W^(1 : ℕ))) +
    (((-2453504 : ℝ) * S^(3 : ℕ) * A^(7 : ℕ) * W^(7 : ℕ) +
    (-11172864 : ℝ) * S^(3 : ℕ) * A^(7 : ℕ) * W^(5 : ℕ)) +
    ((516563168 : ℝ) * S^(3 : ℕ) * A^(7 : ℕ) * W^(3 : ℕ) +
    (-4812508448 : ℝ) * S^(3 : ℕ) * A^(7 : ℕ) * W^(1 : ℕ))))))) / (1207959552 : ℝ)

/- Monomial group 12 of the exact D1 expansion. -/
def modularThetaCompactD1Part12 (S A W : ℝ) : ℝ :=
  ((((((896 : ℝ) * S^(3 : ℕ) * A^(6 : ℕ) * W^(9 : ℕ) +
    ((-272264 : ℝ) * S^(3 : ℕ) * A^(6 : ℕ) * W^(7 : ℕ) +
    (-416947 : ℝ) * S^(3 : ℕ) * A^(6 : ℕ) * W^(5 : ℕ))) +
    (((-30287574 : ℝ) * S^(3 : ℕ) * A^(6 : ℕ) * W^(3 : ℕ) +
    (77994216 : ℝ) * S^(3 : ℕ) * A^(6 : ℕ) * W^(1 : ℕ)) +
    ((136704 : ℝ) * S^(3 : ℕ) * A^(5 : ℕ) * W^(9 : ℕ) +
    (-7197056 : ℝ) * S^(3 : ℕ) * A^(5 : ℕ) * W^(7 : ℕ)))) +
    ((((-15217068 : ℝ) * S^(3 : ℕ) * A^(5 : ℕ) * W^(5 : ℕ) +
    (169968822 : ℝ) * S^(3 : ℕ) * A^(5 : ℕ) * W^(3 : ℕ)) +
    ((-46374972 : ℝ) * S^(3 : ℕ) * A^(5 : ℕ) * W^(1 : ℕ) +
    (-24576 : ℝ) * S^(3 : ℕ) * A^(4 : ℕ) * W^(11 : ℕ))) +
    (((3225600 : ℝ) * S^(3 : ℕ) * A^(4 : ℕ) * W^(9 : ℕ) +
    (-38458944 : ℝ) * S^(3 : ℕ) * A^(4 : ℕ) * W^(7 : ℕ)) +
    ((187396200 : ℝ) * S^(3 : ℕ) * A^(4 : ℕ) * W^(5 : ℕ) +
    (306843882 : ℝ) * S^(3 : ℕ) * A^(4 : ℕ) * W^(3 : ℕ))))) +
    ((((-1597026564 : ℝ) * S^(3 : ℕ) * A^(4 : ℕ) * W^(1 : ℕ) +
    ((13492224 : ℝ) * S^(3 : ℕ) * A^(3 : ℕ) * W^(9 : ℕ) +
    (68759424 : ℝ) * S^(3 : ℕ) * A^(3 : ℕ) * W^(7 : ℕ))) +
    (((-1226757744 : ℝ) * S^(3 : ℕ) * A^(3 : ℕ) * W^(5 : ℕ) +
    (2638188612 : ℝ) * S^(3 : ℕ) * A^(3 : ℕ) * W^(3 : ℕ)) +
    ((3248743248 : ℝ) * S^(3 : ℕ) * A^(3 : ℕ) * W^(1 : ℕ) +
    (-1769472 : ℝ) * S^(3 : ℕ) * A^(2 : ℕ) * W^(11 : ℕ)))) +
    ((((195913728 : ℝ) * S^(3 : ℕ) * A^(2 : ℕ) * W^(9 : ℕ) +
    (-3768391296 : ℝ) * S^(3 : ℕ) * A^(2 : ℕ) * W^(7 : ℕ)) +
    ((19335915648 : ℝ) * S^(3 : ℕ) * A^(2 : ℕ) * W^(5 : ℕ) +
    (-29207870784 : ℝ) * S^(3 : ℕ) * A^(2 : ℕ) * W^(3 : ℕ))) +
    (((-4124986560 : ℝ) * S^(3 : ℕ) * A^(2 : ℕ) * W^(1 : ℕ) +
    (196162560 : ℝ) * S^(3 : ℕ) * A^(1 : ℕ) * W^(7 : ℕ)) +
    ((-6413022720 : ℝ) * S^(3 : ℕ) * A^(1 : ℕ) * W^(5 : ℕ) +
    (27969727680 : ℝ) * S^(3 : ℕ) * A^(1 : ℕ) * W^(3 : ℕ))))))) / (2359296 : ℝ)

/- Monomial group 13 of the exact D1 expansion. -/
def modularThetaCompactD1Part13 (S A W : ℝ) : ℝ :=
  ((((((4972499435520 : ℝ) * S^(3 : ℕ) * A^(1 : ℕ) * W^(1 : ℕ) +
    ((-2009 : ℝ) * S^(2 : ℕ) * A^(11 : ℕ) +
    (491784 : ℝ) * S^(2 : ℕ) * A^(10 : ℕ) * W^(2 : ℕ))) +
    (((-2171020 : ℝ) * S^(2 : ℕ) * A^(10 : ℕ) +
    (2247232 : ℝ) * S^(2 : ℕ) * A^(9 : ℕ) * W^(4 : ℕ)) +
    ((-4652488 : ℝ) * S^(2 : ℕ) * A^(9 : ℕ) * W^(2 : ℕ) +
    (-27178248 : ℝ) * S^(2 : ℕ) * A^(9 : ℕ)))) +
    ((((2573312 : ℝ) * S^(2 : ℕ) * A^(8 : ℕ) * W^(6 : ℕ) +
    (14938624 : ℝ) * S^(2 : ℕ) * A^(8 : ℕ) * W^(4 : ℕ)) +
    ((429614016 : ℝ) * S^(2 : ℕ) * A^(8 : ℕ) * W^(2 : ℕ) +
    (-751867824 : ℝ) * S^(2 : ℕ) * A^(8 : ℕ))) +
    (((-196608 : ℝ) * S^(2 : ℕ) * A^(7 : ℕ) * W^(8 : ℕ) +
    (-5898240 : ℝ) * S^(2 : ℕ) * A^(7 : ℕ) * W^(6 : ℕ)) +
    ((3268129280 : ℝ) * S^(2 : ℕ) * A^(7 : ℕ) * W^(4 : ℕ) +
    (-9782594304 : ℝ) * S^(2 : ℕ) * A^(7 : ℕ) * W^(2 : ℕ))))) +
    ((((52196256960 : ℝ) * S^(2 : ℕ) * A^(7 : ℕ) +
    ((-90177536 : ℝ) * S^(2 : ℕ) * A^(6 : ℕ) * W^(8 : ℕ) +
    (3025129472 : ℝ) * S^(2 : ℕ) * A^(6 : ℕ) * W^(6 : ℕ))) +
    (((-12497555456 : ℝ) * S^(2 : ℕ) * A^(6 : ℕ) * W^(4 : ℕ) +
    (170310882816 : ℝ) * S^(2 : ℕ) * A^(6 : ℕ) * W^(2 : ℕ)) +
    ((-697257873792 : ℝ) * S^(2 : ℕ) * A^(6 : ℕ) +
    (29360128 : ℝ) * S^(2 : ℕ) * A^(5 : ℕ) * W^(10 : ℕ)))) +
    ((((-3007578112 : ℝ) * S^(2 : ℕ) * A^(5 : ℕ) * W^(8 : ℕ) +
    (-2878750720 : ℝ) * S^(2 : ℕ) * A^(5 : ℕ) * W^(6 : ℕ)) +
    ((93744881664 : ℝ) * S^(2 : ℕ) * A^(5 : ℕ) * W^(4 : ℕ) +
    (-1910464985088 : ℝ) * S^(2 : ℕ) * A^(5 : ℕ) * W^(2 : ℕ))) +
    (((4852489637376 : ℝ) * S^(2 : ℕ) * A^(5 : ℕ) +
    (1019215872 : ℝ) * S^(2 : ℕ) * A^(4 : ℕ) * W^(10 : ℕ)) +
    ((-56796119040 : ℝ) * S^(2 : ℕ) * A^(4 : ℕ) * W^(8 : ℕ) +
    (101243437056 : ℝ) * S^(2 : ℕ) * A^(4 : ℕ) * W^(6 : ℕ))))))) / (3221225472 : ℝ)

/- Monomial group 14 of the exact D1 expansion. -/
def modularThetaCompactD1Part14 (S A W : ℝ) : ℝ :=
  ((((((-133611589632 : ℝ) * S^(2 : ℕ) * A^(4 : ℕ) * W^(4 : ℕ) +
    ((1074960009216 : ℝ) * S^(2 : ℕ) * A^(4 : ℕ) * W^(2 : ℕ) +
    (-2022125856768 : ℝ) * S^(2 : ℕ) * A^(4 : ℕ))) +
    (((188743680 : ℝ) * S^(2 : ℕ) * A^(3 : ℕ) * W^(10 : ℕ) +
    (-5537267712 : ℝ) * S^(2 : ℕ) * A^(3 : ℕ) * W^(8 : ℕ)) +
    ((-109017661440 : ℝ) * S^(2 : ℕ) * A^(3 : ℕ) * W^(6 : ℕ) +
    (1778165526528 : ℝ) * S^(2 : ℕ) * A^(3 : ℕ) * W^(4 : ℕ)))) +
    ((((-6295562625024 : ℝ) * S^(2 : ℕ) * A^(3 : ℕ) * W^(2 : ℕ) +
    (7684346327040 : ℝ) * S^(2 : ℕ) * A^(3 : ℕ)) +
    ((5096079360 : ℝ) * S^(2 : ℕ) * A^(2 : ℕ) * W^(10 : ℕ) +
    (-189243850752 : ℝ) * S^(2 : ℕ) * A^(2 : ℕ) * W^(8 : ℕ))) +
    (((2131750010880 : ℝ) * S^(2 : ℕ) * A^(2 : ℕ) * W^(6 : ℕ) +
    (-8821484568576 : ℝ) * S^(2 : ℕ) * A^(2 : ℕ) * W^(4 : ℕ)) +
    ((17223368048640 : ℝ) * S^(2 : ℕ) * A^(2 : ℕ) * W^(2 : ℕ) +
    (-15093767577600 : ℝ) * S^(2 : ℕ) * A^(2 : ℕ))))) +
    ((((3114270720 : ℝ) * S^(2 : ℕ) * A^(1 : ℕ) * W^(8 : ℕ) +
    ((-261979176960 : ℝ) * S^(2 : ℕ) * A^(1 : ℕ) * W^(6 : ℕ) +
    (3808868106240 : ℝ) * S^(2 : ℕ) * A^(1 : ℕ) * W^(4 : ℕ))) +
    (((-13041822597120 : ℝ) * S^(2 : ℕ) * A^(1 : ℕ) * W^(2 : ℕ) +
    (12081092198400 : ℝ) * S^(2 : ℕ) * A^(1 : ℕ)) +
    ((-2876099788800 : ℝ) * S^(2 : ℕ) +
    (-4621 : ℝ) * S^(1 : ℕ) * A^(11 : ℕ) * W^(1 : ℕ)))) +
    ((((-62860 : ℝ) * S^(1 : ℕ) * A^(10 : ℕ) * W^(3 : ℕ) +
    (-278310 : ℝ) * S^(1 : ℕ) * A^(10 : ℕ) * W^(1 : ℕ)) +
    ((-67072 : ℝ) * S^(1 : ℕ) * A^(9 : ℕ) * W^(5 : ℕ) +
    (1122472 : ℝ) * S^(1 : ℕ) * A^(9 : ℕ) * W^(3 : ℕ))) +
    (((-135462 : ℝ) * S^(1 : ℕ) * A^(9 : ℕ) * W^(1 : ℕ) +
    (-1024 : ℝ) * S^(1 : ℕ) * A^(8 : ℕ) * W^(7 : ℕ)) +
    ((2638080 : ℝ) * S^(1 : ℕ) * A^(8 : ℕ) * W^(5 : ℕ) +
    (-9993280 : ℝ) * S^(1 : ℕ) * A^(8 : ℕ) * W^(3 : ℕ))))))) / (268435456 : ℝ)

/- Monomial group 15 of the exact D1 expansion. -/
def modularThetaCompactD1Part15 (S A W : ℝ) : ℝ :=
  ((((((-14889975 : ℝ) * S^(1 : ℕ) * A^(8 : ℕ) * W^(1 : ℕ) +
    ((111616 : ℝ) * S^(1 : ℕ) * A^(7 : ℕ) * W^(7 : ℕ) +
    (3095968 : ℝ) * S^(1 : ℕ) * A^(7 : ℕ) * W^(5 : ℕ))) +
    (((-42177628 : ℝ) * S^(1 : ℕ) * A^(7 : ℕ) * W^(3 : ℕ) +
    (182518536 : ℝ) * S^(1 : ℕ) * A^(7 : ℕ) * W^(1 : ℕ)) +
    ((-40960 : ℝ) * S^(1 : ℕ) * A^(6 : ℕ) * W^(9 : ℕ) +
    (3904768 : ℝ) * S^(1 : ℕ) * A^(6 : ℕ) * W^(7 : ℕ)))) +
    ((((26827712 : ℝ) * S^(1 : ℕ) * A^(6 : ℕ) * W^(5 : ℕ) +
    (459760560 : ℝ) * S^(1 : ℕ) * A^(6 : ℕ) * W^(3 : ℕ)) +
    ((-368800416 : ℝ) * S^(1 : ℕ) * A^(6 : ℕ) * W^(1 : ℕ) +
    (-2490368 : ℝ) * S^(1 : ℕ) * A^(5 : ℕ) * W^(9 : ℕ))) +
    (((111454208 : ℝ) * S^(1 : ℕ) * A^(5 : ℕ) * W^(7 : ℕ) +
    (609634560 : ℝ) * S^(1 : ℕ) * A^(5 : ℕ) * W^(5 : ℕ)) +
    ((-676388544 : ℝ) * S^(1 : ℕ) * A^(5 : ℕ) * W^(3 : ℕ) +
    (-3212483904 : ℝ) * S^(1 : ℕ) * A^(5 : ℕ) * W^(1 : ℕ))))) +
    ((((786432 : ℝ) * S^(1 : ℕ) * A^(4 : ℕ) * W^(11 : ℕ) +
    ((-54657024 : ℝ) * S^(1 : ℕ) * A^(4 : ℕ) * W^(9 : ℕ) +
    (953177088 : ℝ) * S^(1 : ℕ) * A^(4 : ℕ) * W^(7 : ℕ))) +
    (((-2538837504 : ℝ) * S^(1 : ℕ) * A^(4 : ℕ) * W^(5 : ℕ) +
    (-6633734976 : ℝ) * S^(1 : ℕ) * A^(4 : ℕ) * W^(3 : ℕ)) +
    ((13891488768 : ℝ) * S^(1 : ℕ) * A^(4 : ℕ) * W^(1 : ℕ) +
    (-189923328 : ℝ) * S^(1 : ℕ) * A^(3 : ℕ) * W^(9 : ℕ)))) +
    ((((-1944354816 : ℝ) * S^(1 : ℕ) * A^(3 : ℕ) * W^(7 : ℕ) +
    (23584504320 : ℝ) * S^(1 : ℕ) * A^(3 : ℕ) * W^(5 : ℕ)) +
    ((-89170633728 : ℝ) * S^(1 : ℕ) * A^(3 : ℕ) * W^(3 : ℕ) +
    (44236108800 : ℝ) * S^(1 : ℕ) * A^(3 : ℕ) * W^(1 : ℕ))) +
    (((28311552 : ℝ) * S^(1 : ℕ) * A^(2 : ℕ) * W^(11 : ℕ) +
    (-2431254528 : ℝ) * S^(1 : ℕ) * A^(2 : ℕ) * W^(9 : ℕ)) +
    ((45892251648 : ℝ) * S^(1 : ℕ) * A^(2 : ℕ) * W^(7 : ℕ) +
    (-251464310784 : ℝ) * S^(1 : ℕ) * A^(2 : ℕ) * W^(5 : ℕ))))))) / (16777216 : ℝ)

/- Monomial group 16 of the exact D1 expansion. -/
def modularThetaCompactD1Part16 (S A W : ℝ) : ℝ :=
  ((((((213471579340800 : ℝ) * S^(1 : ℕ) * A^(2 : ℕ) * W^(3 : ℕ) +
    ((-24394931896320 : ℝ) * S^(1 : ℕ) * A^(2 : ℕ) * W^(1 : ℕ) +
    (-876525649920 : ℝ) * S^(1 : ℕ) * A^(1 : ℕ) * W^(7 : ℕ))) +
    (((27151910830080 : ℝ) * S^(1 : ℕ) * A^(1 : ℕ) * W^(5 : ℕ) +
    (-129369070632960 : ℝ) * S^(1 : ℕ) * A^(1 : ℕ) * W^(3 : ℕ)) +
    ((902006046720 : ℝ) * S^(1 : ℕ) * A^(1 : ℕ) * W^(1 : ℕ) +
    (14025 : ℝ) * A^(12 : ℕ)))) +
    ((((297096 : ℝ) * A^(11 : ℕ) * W^(2 : ℕ) +
    (-211920 : ℝ) * A^(11 : ℕ)) +
    ((304896 : ℝ) * A^(10 : ℕ) * W^(4 : ℕ) +
    (-14581632 : ℝ) * A^(10 : ℕ) * W^(2 : ℕ))) +
    (((-7542720 : ℝ) * A^(10 : ℕ) +
    (12288 : ℝ) * A^(9 : ℕ) * W^(6 : ℕ)) +
    ((-29852160 : ℝ) * A^(9 : ℕ) * W^(4 : ℕ) +
    (265283424 : ℝ) * A^(9 : ℕ) * W^(2 : ℕ))))) +
    ((((63974304 : ℝ) * A^(9 : ℕ) +
    ((-21602304 : ℝ) * A^(8 : ℕ) * W^(6 : ℕ) +
    (819406848 : ℝ) * A^(8 : ℕ) * W^(4 : ℕ))) +
    (((-5788445184 : ℝ) * A^(8 : ℕ) * W^(2 : ℕ) +
    (18394725888 : ℝ) * A^(8 : ℕ)) +
    ((1572864 : ℝ) * A^(7 : ℕ) * W^(8 : ℕ) +
    (853917696 : ℝ) * A^(7 : ℕ) * W^(6 : ℕ)))) +
    ((((-16193015808 : ℝ) * A^(7 : ℕ) * W^(4 : ℕ) +
    (96529545216 : ℝ) * A^(7 : ℕ) * W^(2 : ℕ)) +
    ((-313636382208 : ℝ) * A^(7 : ℕ) +
    (100663296 : ℝ) * A^(6 : ℕ) * W^(8 : ℕ))) +
    (((-8796733440 : ℝ) * A^(6 : ℕ) * W^(6 : ℕ) +
    (93009530880 : ℝ) * A^(6 : ℕ) * W^(4 : ℕ)) +
    ((-1123168038912 : ℝ) * A^(6 : ℕ) * W^(2 : ℕ) +
    (2345804914176 : ℝ) * A^(6 : ℕ))))))) / (8589934592 : ℝ)

/- Monomial group 17 of the exact D1 expansion. -/
def modularThetaCompactD1Part17 (_S A W : ℝ) : ℝ :=
  ((((((-18432 : ℝ) * A^(5 : ℕ) * W^(10 : ℕ) +
    ((205056 : ℝ) * A^(5 : ℕ) * W^(8 : ℕ) +
    (8513064 : ℝ) * A^(5 : ℕ) * W^(6 : ℕ))) +
    (((-171373554 : ℝ) * A^(5 : ℕ) * W^(4 : ℕ) +
    (960760062 : ℝ) * A^(5 : ℕ) * W^(2 : ℕ)) +
    ((-1723813569 : ℝ) * A^(5 : ℕ) +
    (-626688 : ℝ) * A^(4 : ℕ) * W^(10 : ℕ)))) +
    ((((21399552 : ℝ) * A^(4 : ℕ) * W^(8 : ℕ) +
    (-119308752 : ℝ) * A^(4 : ℕ) * W^(6 : ℕ)) +
    ((1309914828 : ℝ) * A^(4 : ℕ) * W^(4 : ℕ) +
    (-6563995704 : ℝ) * A^(4 : ℕ) * W^(2 : ℕ))) +
    (((10403454510 : ℝ) * A^(4 : ℕ) +
    (-663552 : ℝ) * A^(3 : ℕ) * W^(10 : ℕ)) +
    ((32679936 : ℝ) * A^(3 : ℕ) * W^(8 : ℕ) +
    (1048247136 : ℝ) * A^(3 : ℕ) * W^(6 : ℕ))))) +
    ((((-12220044912 : ℝ) * A^(3 : ℕ) * W^(4 : ℕ) +
    ((41151875040 : ℝ) * A^(3 : ℕ) * W^(2 : ℕ) +
    (-42350681520 : ℝ) * A^(3 : ℕ))) +
    (((-22560768 : ℝ) * A^(2 : ℕ) * W^(10 : ℕ) +
    (781332480 : ℝ) * A^(2 : ℕ) * W^(8 : ℕ)) +
    ((-10126461888 : ℝ) * A^(2 : ℕ) * W^(6 : ℕ) +
    (48752565120 : ℝ) * A^(2 : ℕ) * W^(4 : ℕ)))) +
    ((((-97228771200 : ℝ) * A^(2 : ℕ) * W^(2 : ℕ) +
    (67107132720 : ℝ) * A^(2 : ℕ)) +
    ((-14929920 : ℝ) * A^(1 : ℕ) * W^(8 : ℕ) +
    (958314240 : ℝ) * A^(1 : ℕ) * W^(6 : ℕ))) +
    (((-14679843840 : ℝ) * A^(1 : ℕ) * W^(4 : ℕ) +
    (56969775360 : ℝ) * A^(1 : ℕ) * W^(2 : ℕ)) +
    ((-41346547200 : ℝ) * A^(1 : ℕ) +
    (7054387200 : ℝ))))))) / (1048576 : ℝ)

/- Explicit real polynomial for the mass-normalized reflected rank-three determinant. -/

def modularThetaCompactD1 (S A W : ℝ) : ℝ :=
  ((((modularThetaCompactD1Part0 S A W +
    modularThetaCompactD1Part1 S A W) +
    (modularThetaCompactD1Part2 S A W +
    modularThetaCompactD1Part3 S A W)) +
    ((modularThetaCompactD1Part4 S A W +
    modularThetaCompactD1Part5 S A W) +
    (modularThetaCompactD1Part6 S A W +
    (modularThetaCompactD1Part7 S A W +
    modularThetaCompactD1Part8 S A W)))) +
    (((modularThetaCompactD1Part9 S A W +
    modularThetaCompactD1Part10 S A W) +
    (modularThetaCompactD1Part11 S A W +
    modularThetaCompactD1Part12 S A W)) +
    ((modularThetaCompactD1Part13 S A W +
    modularThetaCompactD1Part14 S A W) +
    (modularThetaCompactD1Part15 S A W +
    (modularThetaCompactD1Part16 S A W +
    modularThetaCompactD1Part17 S A W)))))

/- Exact symbolic expansion; no source or positivity assumption. -/
theorem modularThetaLyapunovReflectedEighthPolynomial_eval_ofReal (S A W : ℝ) :
    MvPolynomial.eval (fun i : ModularThetaLyapunovState =>
      match i with | .S => (S : ℂ) | .A => (A : ℂ) | .W => (W : ℂ))
        modularThetaLyapunovReflectedEighthPolynomial = (modularThetaCompactD1 S A W : ℂ) := by
  unfold modularThetaLyapunovReflectedEighthPolynomial
  simp only [modularThetaLyapunovNormalizedSourceJet]
  norm_num only [Nat.reduceAdd]

  rw [compactH0_eq, compactH1_eq, compactH2_eq, compactH3_eq, compactH4_eq, compactH5_eq, compactH6_eq, compactH7_eq, compactH8_eq, compactH9_eq, compactH10_eq]

  simp only [compactH0, compactH1, compactH2, compactH3, compactH4, compactH5, compactH6, compactH7, compactH8, compactH9, compactH10, map_add, map_sub, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  try dsimp only

  unfold modularThetaCompactD1 modularThetaCompactD1Part0 modularThetaCompactD1Part1 modularThetaCompactD1Part2 modularThetaCompactD1Part3 modularThetaCompactD1Part4 modularThetaCompactD1Part5 modularThetaCompactD1Part6 modularThetaCompactD1Part7 modularThetaCompactD1Part8 modularThetaCompactD1Part9 modularThetaCompactD1Part10 modularThetaCompactD1Part11 modularThetaCompactD1Part12 modularThetaCompactD1Part13 modularThetaCompactD1Part14 modularThetaCompactD1Part15 modularThetaCompactD1Part16 modularThetaCompactD1Part17
  push_cast
  ring
end
end HTGeometry
