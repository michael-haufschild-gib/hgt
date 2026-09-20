import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeLyapunovClosure
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
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false


private def compactH0 : ModularThetaLyapunovPolynomial :=
  C (1 / 1 : ℂ)

private theorem compactH0_eq : modularThetaLyapunovNormalizedHJet 0 = compactH0 := by

  simp [modularThetaLyapunovNormalizedHJet, compactH0]

private def compactH1 : ModularThetaLyapunovPolynomial :=
  C (-1 / 6 : ℂ) * X ModularThetaLyapunovState.S^1

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
  C (1 / 12 : ℂ) * X ModularThetaLyapunovState.S^2 +
    C (1 / 8 : ℂ) * X ModularThetaLyapunovState.A^1 +
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
  C (-5 / 72 : ℂ) * X ModularThetaLyapunovState.S^3 +
    C (-7 / 48 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 +
    C (7 / 12 : ℂ) * X ModularThetaLyapunovState.S^1 +
    C (-1 / 4 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1

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
  C (35 / 432 : ℂ) * X ModularThetaLyapunovState.S^4 +
    C (25 / 144 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 +
    C (-11 / 12 : ℂ) * X ModularThetaLyapunovState.S^2 +
    C (1 / 2 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    C (-1 / 64 : ℂ) * X ModularThetaLyapunovState.A^2 +
    C (1 / 2 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (-11 / 8 : ℂ) * X ModularThetaLyapunovState.A^1 +
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
  C (-35 / 288 : ℂ) * X ModularThetaLyapunovState.S^5 +
    C (-239 / 864 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 +
    C (125 / 72 : ℂ) * X ModularThetaLyapunovState.S^3 +
    C (-17 / 24 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    C (-1 / 128 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 +
    C (-7 / 4 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (175 / 48 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 +
    C (-139 / 24 : ℂ) * X ModularThetaLyapunovState.S^1 +
    C (3 / 16 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1 +
    C (-1 / 1 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3 +
    C (25 / 4 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1

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
  C (385 / 1728 : ℂ) * X ModularThetaLyapunovState.S^6 +
    C (6439 / 10368 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^1 +
    C (-3325 / 864 : ℂ) * X ModularThetaLyapunovState.S^4 +
    C (181 / 216 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    C (241 / 768 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^2 +
    C (95 / 24 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (-2375 / 288 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 +
    C (889 / 48 : ℂ) * X ModularThetaLyapunovState.S^2 +
    C (-13 / 16 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1 +
    C (17 / 3 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3 +
    C (-95 / 4 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    C (51 / 512 : ℂ) * X ModularThetaLyapunovState.A^3 +
    C (-15 / 16 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^2 +
    C (95 / 128 : ℂ) * X ModularThetaLyapunovState.A^2 +
    C (2 / 1 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^4 +
    C (-95 / 4 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (889 / 32 : ℂ) * X ModularThetaLyapunovState.A^1 +
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
  C (-5005 / 10368 : ℂ) * X ModularThetaLyapunovState.S^7 +
    C (-108737 / 62208 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^1 +
    C (5635 / 576 : ℂ) * X ModularThetaLyapunovState.S^5 +
    C (-587 / 576 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    C (-26075 / 13824 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^2 +
    C (-2797 / 432 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (38479 / 1728 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 +
    C (-5915 / 96 : ℂ) * X ModularThetaLyapunovState.S^3 +
    C (259 / 192 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1 +
    C (-731 / 36 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3 +
    C (2737 / 48 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    C (-915 / 1024 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^3 +
    C (231 / 32 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^2 +
    C (161 / 256 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 +
    C (-17 / 1 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^4 +
    C (1127 / 8 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (-8281 / 64 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 +
    C (5473 / 48 : ℂ) * X ModularThetaLyapunovState.S^1 +
    C (-237 / 256 : ℂ) * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^1 +
    C (7 / 2 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^3 +
    C (-483 / 32 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1 +
    C (-4 / 1 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^5 +
    C (161 / 2 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3 +
    C (-3549 / 16 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1

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
  C (25025 / 20736 : ℂ) * X ModularThetaLyapunovState.S^8 +
    C (514381 / 93312 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^1 +
    C (-2695 / 96 : ℂ) * X ModularThetaLyapunovState.S^6 +
    C (407 / 144 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    C (118135 / 13824 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^2 +
    C (75 / 16 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (-45073 / 576 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^1 +
    C (62965 / 288 : ℂ) * X ModularThetaLyapunovState.S^4 +
    C (85 / 16 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1 +
    C (1495 / 27 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3 +
    C (-1267 / 12 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    C (7925 / 1536 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^3 +
    C (-515 / 16 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^2 +
    C (-5061 / 128 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^2 +
    C (90 / 1 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^4 +
    C (-1995 / 4 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (44975 / 96 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 +
    C (-14677 / 24 : ℂ) * X ModularThetaLyapunovState.S^2 +
    C (725 / 64 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^1 +
    C (-40 / 1 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^3 +
    C (819 / 8 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1 +
    C (48 / 1 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^5 +
    C (-714 / 1 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3 +
    C (5397 / 4 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    C (849 / 4096 : ℂ) * X ModularThetaLyapunovState.A^4 +
    C (345 / 64 : ℂ) * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^2 +
    C (-3213 / 256 : ℂ) * X ModularThetaLyapunovState.A^3 +
    C (-45 / 4 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^4 +
    C (945 / 8 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^2 +
    C (-5397 / 128 : ℂ) * X ModularThetaLyapunovState.A^2 +
    C (8 / 1 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^6 +
    C (-252 / 1 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^4 +
    C (5397 / 4 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (-14677 / 16 : ℂ) * X ModularThetaLyapunovState.A^1 +
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
  C (-425425 / 124416 : ℂ) * X ModularThetaLyapunovState.S^9 +
    C (-10389355 / 559872 : ℂ) * X ModularThetaLyapunovState.S^7 * X ModularThetaLyapunovState.A^1 +
    C (155155 / 1728 : ℂ) * X ModularThetaLyapunovState.S^7 +
    C (-746851 / 46656 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    C (-2905603 / 82944 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^2 +
    C (46603 / 2592 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (3370847 / 10368 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^1 +
    C (-159985 / 192 : ℂ) * X ModularThetaLyapunovState.S^5 +
    C (-221665 / 3456 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1 +
    C (-67855 / 648 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3 +
    C (18197 / 96 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    C (-228215 / 9216 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^3 +
    C (26155 / 288 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^2 +
    C (808325 / 2304 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^2 +
    C (-10055 / 27 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^4 +
    C (86707 / 72 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (-1092469 / 576 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 +
    C (451175 / 144 : ℂ) * X ModularThetaLyapunovState.S^3 +
    C (-21995 / 256 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^1 +
    C (1645 / 6 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^3 +
    C (-8029 / 32 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1 +
    C (-1060 / 3 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^5 +
    C (22661 / 6 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3 +
    C (-77707 / 16 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    C (-17283 / 8192 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^4 +
    C (-11235 / 128 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^2 +
    C (85095 / 512 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^3 +
    C (1415 / 8 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^4 +
    C (-21483 / 16 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^2 +
    C (-13713 / 256 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 +
    C (-388 / 3 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^6 +
    C (3162 / 1 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^4 +
    C (-95991 / 8 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (631645 / 96 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 +
    C (-357721 / 96 : ℂ) * X ModularThetaLyapunovState.S^1 +
    C (-2439 / 512 : ℂ) * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^1 +
    C (-795 / 32 : ℂ) * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^3 +
    C (22041 / 128 : ℂ) * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^1 +
    C (33 / 1 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^5 +
    C (-651 / 1 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^3 +
    C (41139 / 32 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1 +
    C (-16 / 1 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^7 +
    C (744 / 1 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^5 +
    C (-13713 / 2 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3 +
    C (90235 / 8 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1

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
  C (8083075 / 746496 : ℂ) * X ModularThetaLyapunovState.S^10 +
    C (885697661 / 13436928 : ℂ) * X ModularThetaLyapunovState.S^8 * X ModularThetaLyapunovState.A^1 +
    C (-4379375 / 13824 : ℂ) * X ModularThetaLyapunovState.S^8 +
    C (4220461 / 46656 : ℂ) * X ModularThetaLyapunovState.S^7 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    C (208106413 / 1492992 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^2 +
    C (-4419709 / 46656 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (-90016675 / 62208 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^1 +
    C (3932005 / 1152 : ℂ) * X ModularThetaLyapunovState.S^6 +
    C (4245367 / 10368 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1 +
    C (-947 / 1944 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3 +
    C (-71225 / 96 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    C (12064865 / 110592 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^3 +
    C (-4685 / 384 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^2 +
    C (-20673625 / 9216 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^2 +
    C (134395 / 108 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^4 +
    C (-39375 / 32 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (65761507 / 6912 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^1 +
    C (-27914425 / 1728 : ℂ) * X ModularThetaLyapunovState.S^4 +
    C (1201945 / 2304 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^1 +
    C (-38165 / 27 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^3 +
    C (-44625 / 32 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1 +
    C (55204 / 27 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^5 +
    C (-261625 / 18 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3 +
    C (1848553 / 144 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    C (208959 / 16384 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^4 +
    C (221895 / 256 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^2 +
    C (-1386875 / 1024 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^3 +
    C (-79945 / 48 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^4 +
    C (270375 / 32 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^2 +
    C (2461333 / 512 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^2 +
    C (11374 / 9 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^6 +
    C (-23625 / 1 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^4 +
    C (970235 / 16 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (-19938875 / 576 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 +
    C (5771821 / 192 : ℂ) * X ModularThetaLyapunovState.S^2 +
    C (31719 / 512 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^1 +
    C (16735 / 32 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^3 +
    C (-380625 / 128 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^1 +
    C (-681 / 1 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^5 +
    C (10500 / 1 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^3 +
    C (-398307 / 32 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1 +
    C (336 / 1 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^7 +
    C (-12600 / 1 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^5 +
    C (173621 / 2 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3 +
    C (-797555 / 8 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    C (-26199 / 32768 : ℂ) * X ModularThetaLyapunovState.A^5 +
    C (34137 / 512 : ℂ) * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^2 +
    C (-445725 / 8192 : ℂ) * X ModularThetaLyapunovState.A^4 +
    C (3165 / 32 : ℂ) * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^4 +
    C (-181125 / 128 : ℂ) * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^2 +
    C (1562589 / 1024 : ℂ) * X ModularThetaLyapunovState.A^3 +
    C (-91 / 1 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^6 +
    C (23625 / 8 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^4 +
    C (-459585 / 32 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^2 +
    C (797555 / 256 : ℂ) * X ModularThetaLyapunovState.A^2 +
    C (32 / 1 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^8 +
    C (-2100 / 1 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^6 +
    C (30639 / 1 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^4 +
    C (-797555 / 8 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (5771821 / 128 : ℂ) * X ModularThetaLyapunovState.A^1 +
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
  ((((((4704000 : ℝ) * S^24 +
    ((58720640 : ℝ) * S^22 * A^1 +
    (-463680000 : ℝ) * S^22)) +
    (((55928320 : ℝ) * S^21 * A^1 * W^1 +
    (312019792 : ℝ) * S^20 * A^2) +
    ((274341120 : ℝ) * S^20 * A^1 * W^2 +
    (-5815173120 : ℝ) * S^20 * A^1))) +
    ((((20876486400 : ℝ) * S^20 +
    (471293952 : ℝ) * S^19 * A^2 * W^1) +
    ((-350818560 : ℝ) * S^19 * A^1 * W^3 +
    (-5165614080 : ℝ) * S^19 * A^1 * W^1)) +
    (((914942304 : ℝ) * S^18 * A^3 +
    (3335316480 : ℝ) * S^18 * A^2 * W^2) +
    ((-31241500128 : ℝ) * S^18 * A^2 +
    (-471916800 : ℝ) * S^18 * A^1 * W^4)))) +
    ((((-16539863040 : ℝ) * S^18 * A^1 * W^2 +
    ((261134409600 : ℝ) * S^18 * A^1 +
    (-567486259200 : ℝ) * S^18)) +
    (((1372119552 : ℝ) * S^17 * A^3 * W^1 +
    (-1326939840 : ℝ) * S^17 * A^2 * W^3) +
    ((-49527016704 : ℝ) * S^17 * A^2 * W^1 +
    (1916835840 : ℝ) * S^17 * A^1 * W^5))) +
    ((((25263083520 : ℝ) * S^17 * A^1 * W^3 +
    (176434951680 : ℝ) * S^17 * A^1 * W^1) +
    ((1582981389 : ℝ) * S^16 * A^4 +
    (15549859008 : ℝ) * S^16 * A^3 * W^2)) +
    (((-93681714672 : ℝ) * S^16 * A^3 +
    (-64514880 : ℝ) * S^16 * A^2 * W^4) +
    ((-196036495488 : ℝ) * S^16 * A^2 * W^2 +
    (1413371704752 : ℝ) * S^16 * A^2)))))) / (45137758519296 : ℝ)

/- Monomial group 1 of the exact D1 expansion. -/
def modularThetaCompactD1Part1 (S A W : ℝ) : ℝ :=
  ((((((218142720 : ℝ) * S^16 * A^1 * W^6 +
    ((-494899200 : ℝ) * S^16 * A^1 * W^4 +
    (35862013440 : ℝ) * S^16 * A^1 * W^2)) +
    (((-517558809600 : ℝ) * S^16 * A^1 +
    (768013747200 : ℝ) * S^16) +
    ((81047648 : ℝ) * S^15 * A^4 * W^1 +
    (116046432 : ℝ) * S^15 * A^3 * W^3))) +
    ((((-13854406272 : ℝ) * S^15 * A^3 * W^1 +
    (38974464 : ℝ) * S^15 * A^2 * W^5) +
    ((5876310528 : ℝ) * S^15 * A^2 * W^3 +
    (128464759296 : ℝ) * S^15 * A^2 * W^1)) +
    (((95109120 : ℝ) * S^15 * A^1 * W^7 +
    (-11510968320 : ℝ) * S^15 * A^1 * W^5) +
    ((-45431746560 : ℝ) * S^15 * A^1 * W^3 +
    (-213847326720 : ℝ) * S^15 * A^1 * W^1)))) +
    ((((109907037 : ℝ) * S^14 * A^5 +
    ((2611004784 : ℝ) * S^14 * A^4 * W^2 +
    (-12762427788 : ℝ) * S^14 * A^4)) +
    (((2399630688 : ℝ) * S^14 * A^3 * W^4 +
    (-68085278784 : ℝ) * S^14 * A^3 * W^2) +
    ((319509876960 : ℝ) * S^14 * A^3 +
    (-778467456 : ℝ) * S^14 * A^2 * W^6))) +
    ((((-443276928 : ℝ) * S^14 * A^2 * W^4 +
    (400040211456 : ℝ) * S^14 * A^2 * W^2) +
    ((-2758697626752 : ℝ) * S^14 * A^2 +
    (13271040 : ℝ) * S^14 * A^1 * W^8)) +
    (((-14086586880 : ℝ) * S^14 * A^1 * W^6 +
    (116737044480 : ℝ) * S^14 * A^1 * W^4) +
    ((-759922145280 : ℝ) * S^14 * A^1 * W^2 +
    (9152270922240 : ℝ) * S^14 * A^1)))))) / (3343537668096 : ℝ)

/- Monomial group 2 of the exact D1 expansion. -/
def modularThetaCompactD1Part2 (S A W : ℝ) : ℝ :=
  ((((((-26480601907200 : ℝ) * S^14 +
    ((-359446976 : ℝ) * S^13 * A^5 * W^1 +
    (1012974528 : ℝ) * S^13 * A^4 * W^3)) +
    (((-64239977472 : ℝ) * S^13 * A^4 * W^1 +
    (-1005626880 : ℝ) * S^13 * A^3 * W^5) +
    ((-58227669504 : ℝ) * S^13 * A^3 * W^3 +
    (1405278950400 : ℝ) * S^13 * A^3 * W^1))) +
    ((((5669498880 : ℝ) * S^13 * A^2 * W^7 +
    (-1784291328 : ℝ) * S^13 * A^2 * W^5) +
    ((-468462071808 : ℝ) * S^13 * A^2 * W^3 +
    (-5528406601728 : ℝ) * S^13 * A^2 * W^1)) +
    (((-15407677440 : ℝ) * S^13 * A^1 * W^7 +
    (1066553671680 : ℝ) * S^13 * A^1 * W^5) +
    ((630102343680 : ℝ) * S^13 * A^1 * W^3 +
    (4036274012160 : ℝ) * S^13 * A^1 * W^1)))) +
    ((((17701947 : ℝ) * S^12 * A^6 +
    ((7738116096 : ℝ) * S^12 * A^5 * W^2 +
    (-40877887920 : ℝ) * S^12 * A^5)) +
    (((31535800128 : ℝ) * S^12 * A^4 * W^4 +
    (-441534540672 : ℝ) * S^12 * A^4 * W^2) +
    ((1595612821392 : ℝ) * S^12 * A^4 +
    (-18565314048 : ℝ) * S^12 * A^3 * W^6))) +
    ((((-228141114624 : ℝ) * S^12 * A^3 * W^4 +
    (4768766535168 : ℝ) * S^12 * A^3 * W^2) +
    ((-22144950498816 : ℝ) * S^12 * A^3 +
    (22083010560 : ℝ) * S^12 * A^2 * W^8)) +
    (((-106310071296 : ℝ) * S^12 * A^2 * W^6 +
    (610246960128 : ℝ) * S^12 * A^2 * W^4) +
    ((-19317862305792 : ℝ) * S^12 * A^2 * W^2 +
    (124131281075712 : ℝ) * S^12 * A^2)))))) / (8916100448256 : ℝ)

/- Monomial group 3 of the exact D1 expansion. -/
def modularThetaCompactD1Part3 (S A W : ℝ) : ℝ :=
  ((((((-238878720 : ℝ) * S^12 * A^1 * W^8 +
    ((117145128960 : ℝ) * S^12 * A^1 * W^6 +
    (-1221623562240 : ℝ) * S^12 * A^1 * W^4)) +
    (((4027651153920 : ℝ) * S^12 * A^1 * W^2 +
    (-33303820861440 : ℝ) * S^12 * A^1) +
    ((27587356876800 : ℝ) * S^12 +
    (-52246208 : ℝ) * S^11 * A^6 * W^1))) +
    ((((-857152384 : ℝ) * S^11 * A^5 * W^3 +
    (-3143819008 : ℝ) * S^11 * A^5 * W^1) +
    ((948109824 : ℝ) * S^11 * A^4 * W^5 +
    (-31987089792 : ℝ) * S^11 * A^4 * W^3)) +
    (((346083083520 : ℝ) * S^11 * A^4 * W^1 +
    (-2029068288 : ℝ) * S^11 * A^3 * W^7) +
    ((36810187776 : ℝ) * S^11 * A^3 * W^5 +
    (157696503552 : ℝ) * S^11 * A^3 * W^3)))) +
    ((((-2545815720960 : ℝ) * S^11 * A^3 * W^1 +
    ((2813460480 : ℝ) * S^11 * A^2 * W^9 +
    (-80286031872 : ℝ) * S^11 * A^2 * W^7)) +
    (((229424652288 : ℝ) * S^11 * A^2 * W^5 +
    (686597492736 : ℝ) * S^11 * A^2 * W^3) +
    ((4300823457792 : ℝ) * S^11 * A^2 * W^1 +
    (44511068160 : ℝ) * S^11 * A^1 * W^7))) +
    ((((-2315278909440 : ℝ) * S^11 * A^1 * W^5 +
    (2846515322880 : ℝ) * S^11 * A^1 * W^3) +
    ((934851870720 : ℝ) * S^11 * A^1 * W^1 +
    (-44328927 : ℝ) * S^10 * A^7)) +
    (((444481224 : ℝ) * S^10 * A^6 * W^2 +
    (-4121461314 : ℝ) * S^10 * A^6) +
    ((6986684928 : ℝ) * S^10 * A^5 * W^4 +
    (-67169977632 : ℝ) * S^10 * A^5 * W^2)))))) / (990677827584 : ℝ)

/- Monomial group 4 of the exact D1 expansion. -/
def modularThetaCompactD1Part4 (S A W : ℝ) : ℝ :=
  ((((((5720847438 : ℝ) * S^10 * A^5 +
    ((-64221760 : ℝ) * S^10 * A^4 * W^6 +
    (-3446352832 : ℝ) * S^10 * A^4 * W^4)) +
    (((33604536288 : ℝ) * S^10 * A^4 * W^2 +
    (-126956322832 : ℝ) * S^10 * A^4) +
    ((-57618432 : ℝ) * S^10 * A^3 * W^8 +
    (2557896192 : ℝ) * S^10 * A^3 * W^6))) +
    ((((5542195776 : ℝ) * S^10 * A^3 * W^4 +
    (-233784616320 : ℝ) * S^10 * A^3 * W^2) +
    ((1086978466752 : ℝ) * S^10 * A^3 +
    (39518208 : ℝ) * S^10 * A^2 * W^10)) +
    (((-4021567488 : ℝ) * S^10 * A^2 * W^8 +
    (32308008192 : ℝ) * S^10 * A^2 * W^6) +
    ((-115441042176 : ℝ) * S^10 * A^2 * W^4 +
    (851360698368 : ℝ) * S^10 * A^2 * W^2)))) +
    ((((-4336111526400 : ℝ) * S^10 * A^2 +
    ((172523520 : ℝ) * S^10 * A^1 * W^8 +
    (-51801431040 : ℝ) * S^10 * A^1 * W^6)) +
    (((602248919040 : ℝ) * S^10 * A^1 * W^4 +
    (-1604934881280 : ℝ) * S^10 * A^1 * W^2) +
    ((8077431352320 : ℝ) * S^10 * A^1 +
    (-5245328793600 : ℝ) * S^10))) +
    ((((2348363 : ℝ) * S^9 * A^7 * W^1 +
    (-94698916 : ℝ) * S^9 * A^6 * W^3) +
    ((249390536 : ℝ) * S^9 * A^6 * W^1 +
    (120380672 : ℝ) * S^9 * A^5 * W^5)) +
    (((-1219500976 : ℝ) * S^9 * A^5 * W^3 +
    (12532648336 : ℝ) * S^9 * A^5 * W^1) +
    ((17454336 : ℝ) * S^9 * A^4 * W^7 +
    (71686272 : ℝ) * S^9 * A^4 * W^5)))))) / (27518828544 : ℝ)

/- Monomial group 5 of the exact D1 expansion. -/
def modularThetaCompactD1Part5 (S A W : ℝ) : ℝ :=
  ((((((152425244416 : ℝ) * S^9 * A^4 * W^3 +
    ((-868298190848 : ℝ) * S^9 * A^4 * W^1 +
    (-391643136 : ℝ) * S^9 * A^3 * W^9)) +
    (((10026221568 : ℝ) * S^9 * A^3 * W^7 +
    (-128850425856 : ℝ) * S^9 * A^3 * W^5) +
    ((-70542409728 : ℝ) * S^9 * A^3 * W^3 +
    (2481192505344 : ℝ) * S^9 * A^3 * W^1))) +
    ((((37748736 : ℝ) * S^9 * A^2 * W^11 +
    (-18246795264 : ℝ) * S^9 * A^2 * W^9) +
    ((413788520448 : ℝ) * S^9 * A^2 * W^7 +
    (-1560036999168 : ℝ) * S^9 * A^2 * W^5)) +
    (((370166243328 : ℝ) * S^9 * A^2 * W^3 +
    (406208397312 : ℝ) * S^9 * A^2 * W^1) +
    ((-95109120000 : ℝ) * S^9 * A^1 * W^7 +
    (4133928960000 : ℝ) * S^9 * A^1 * W^5)))) +
    ((((-9934461665280 : ℝ) * S^9 * A^1 * W^3 +
    ((-6253747568640 : ℝ) * S^9 * A^1 * W^1 +
    (-11055545 : ℝ) * S^8 * A^8)) +
    (((59825184 : ℝ) * S^8 * A^7 * W^2 +
    (-564584068 : ℝ) * S^8 * A^7) +
    ((775576160 : ℝ) * S^8 * A^6 * W^4 +
    (-7241334816 : ℝ) * S^8 * A^6 * W^2))) +
    ((((20576648588 : ℝ) * S^8 * A^6 +
    (-387204608 : ℝ) * S^8 * A^5 * W^6) +
    ((-30694479232 : ℝ) * S^8 * A^5 * W^4 +
    (222742001792 : ℝ) * S^8 * A^5 * W^2)) +
    (((-793923272512 : ℝ) * S^8 * A^5 +
    (1280507904 : ℝ) * S^8 * A^4 * W^8) +
    ((3306157056 : ℝ) * S^8 * A^4 * W^6 +
    (178968214272 : ℝ) * S^8 * A^4 * W^4)))))) / (146767085568 : ℝ)

/- Monomial group 6 of the exact D1 expansion. -/
def modularThetaCompactD1Part6 (S A W : ℝ) : ℝ :=
  ((((((-207855942784 : ℝ) * S^8 * A^4 * W^2 +
    ((835774356432 : ℝ) * S^8 * A^4 +
    (-8257536 : ℝ) * S^8 * A^3 * W^10)) +
    (((863207424 : ℝ) * S^8 * A^3 * W^8 +
    (-17094925824 : ℝ) * S^8 * A^3 * W^6) +
    ((-24364197120 : ℝ) * S^8 * A^3 * W^4 +
    (1201178230272 : ℝ) * S^8 * A^3 * W^2))) +
    ((((-4864347554304 : ℝ) * S^8 * A^3 +
    (-672399360 : ℝ) * S^8 * A^2 * W^10) +
    ((41197436928 : ℝ) * S^8 * A^2 * W^8 +
    (-375290164224 : ℝ) * S^8 * A^2 * W^6)) +
    (((1283331419136 : ℝ) * S^8 * A^2 * W^4 +
    (-4456425996288 : ℝ) * S^8 * A^2 * W^2) +
    ((14979044860416 : ℝ) * S^8 * A^2 +
    (-1105920000 : ℝ) * S^8 * A^1 * W^8)))) +
    ((((227120025600 : ℝ) * S^8 * A^1 * W^6 +
    ((-2833267507200 : ℝ) * S^8 * A^1 * W^4 +
    (7410103050240 : ℝ) * S^8 * A^1 * W^2)) +
    (((-22414244659200 : ℝ) * S^8 * A^1 +
    (11548815667200 : ℝ) * S^8) +
    ((2021619 : ℝ) * S^7 * A^8 * W^1 +
    (-53083292 : ℝ) * S^7 * A^7 * W^3))) +
    ((((196219348 : ℝ) * S^7 * A^7 * W^1 +
    (90494656 : ℝ) * S^7 * A^6 * W^5) +
    ((-261868800 : ℝ) * S^7 * A^6 * W^3 +
    (4403742400 : ℝ) * S^7 * A^6 * W^1)) +
    (((-187764736 : ℝ) * S^7 * A^5 * W^7 +
    (-165878016 : ℝ) * S^7 * A^5 * W^5) +
    ((22356582400 : ℝ) * S^7 * A^5 * W^3 +
    (-101851517440 : ℝ) * S^7 * A^5 * W^1)))))) / (12230590464 : ℝ)

/- Monomial group 7 of the exact D1 expansion. -/
def modularThetaCompactD1Part7 (S A W : ℝ) : ℝ :=
  ((((((129499136 : ℝ) * S^7 * A^4 * W^9 +
    ((-926203904 : ℝ) * S^7 * A^4 * W^7 +
    (4663816192 : ℝ) * S^7 * A^4 * W^5)) +
    (((-173810609152 : ℝ) * S^7 * A^4 * W^3 +
    (582674007040 : ℝ) * S^7 * A^4 * W^1) +
    ((1428160512 : ℝ) * S^7 * A^3 * W^9 +
    (-11253645312 : ℝ) * S^7 * A^3 * W^7))) +
    ((((74032128000 : ℝ) * S^7 * A^3 * W^5 +
    (-210383981568 : ℝ) * S^7 * A^3 * W^3) +
    ((162319552512 : ℝ) * S^7 * A^3 * W^1 +
    (-150994944 : ℝ) * S^7 * A^2 * W^11)) +
    (((35474374656 : ℝ) * S^7 * A^2 * W^9 +
    (-735860293632 : ℝ) * S^7 * A^2 * W^7) +
    ((3185082335232 : ℝ) * S^7 * A^2 * W^5 +
    (-3139193290752 : ℝ) * S^7 * A^2 * W^3)))) +
    ((((-3858253627392 : ℝ) * S^7 * A^2 * W^1 +
    ((91304755200 : ℝ) * S^7 * A^1 * W^7 +
    (-3504456990720 : ℝ) * S^7 * A^1 * W^5)) +
    (((11342173962240 : ℝ) * S^7 * A^1 * W^3 +
    (5358102773760 : ℝ) * S^7 * A^1 * W^1) +
    ((-1040851 : ℝ) * S^6 * A^9 +
    (12869444 : ℝ) * S^6 * A^8 * W^2))) +
    ((((-59348865 : ℝ) * S^6 * A^8 +
    (-16863392 : ℝ) * S^6 * A^7 * W^4) +
    ((-158809168 : ℝ) * S^6 * A^7 * W^2 +
    (651210184 : ℝ) * S^6 * A^7)) +
    (((232641280 : ℝ) * S^6 * A^6 * W^6 +
    (-3241035264 : ℝ) * S^6 * A^6 * W^4) +
    ((16755853888 : ℝ) * S^6 * A^6 * W^2 +
    (-63534256784 : ℝ) * S^6 * A^6)))))) / (16307453952 : ℝ)

/- Monomial group 8 of the exact D1 expansion. -/
def modularThetaCompactD1Part8 (S A W : ℝ) : ℝ :=
  ((((((-466714624 : ℝ) * S^6 * A^5 * W^8 +
    ((1627916288 : ℝ) * S^6 * A^5 * W^6 +
    (51770248192 : ℝ) * S^6 * A^5 * W^4)) +
    (((-574061925888 : ℝ) * S^6 * A^5 * W^2 +
    (2396229423552 : ℝ) * S^6 * A^5) +
    ((73924608 : ℝ) * S^6 * A^4 * W^10 +
    (-10395451392 : ℝ) * S^6 * A^4 * W^8))) +
    ((((7745654784 : ℝ) * S^6 * A^4 * W^6 +
    (-148343095296 : ℝ) * S^6 * A^4 * W^4) +
    ((5225471419392 : ℝ) * S^6 * A^4 * W^2 +
    (-19040311905024 : ℝ) * S^6 * A^4)) +
    (((622854144 : ℝ) * S^6 * A^3 * W^10 +
    (-30357061632 : ℝ) * S^6 * A^3 * W^8) +
    ((207836282880 : ℝ) * S^6 * A^3 * W^6 +
    (2863423604736 : ℝ) * S^6 * A^3 * W^4)))) +
    ((((-29318620557312 : ℝ) * S^6 * A^3 * W^2 +
    ((83844277585920 : ℝ) * S^6 * A^3 +
    (26612858880 : ℝ) * S^6 * A^2 * W^10)) +
    (((-1272009719808 : ℝ) * S^6 * A^2 * W^8 +
    (12425805471744 : ℝ) * S^6 * A^2 * W^6) +
    ((-43775832416256 : ℝ) * S^6 * A^2 * W^4 +
    (105519106031616 : ℝ) * S^6 * A^2 * W^2))) +
    ((((-214864694599680 : ℝ) * S^6 * A^2 +
    (25480396800 : ℝ) * S^6 * A^1 * W^8) +
    ((-3786267525120 : ℝ) * S^6 * A^1 * W^6 +
    (49908665548800 : ℝ) * S^6 * A^1 * W^4)) +
    (((-138709387837440 : ℝ) * S^6 * A^1 * W^2 +
    (263710859673600 : ℝ) * S^6 * A^1) +
    ((-107527672627200 : ℝ) * S^6 +
    (1493403 : ℝ) * S^5 * A^9 * W^1)))))) / (32614907904 : ℝ)

/- Monomial group 9 of the exact D1 expansion. -/
def modularThetaCompactD1Part9 (S A W : ℝ) : ℝ :=
  ((((((-2293836 : ℝ) * S^5 * A^8 * W^3 +
    ((12090499 : ℝ) * S^5 * A^8 * W^1 +
    (-5835552 : ℝ) * S^5 * A^7 * W^5)) +
    (((29487452 : ℝ) * S^5 * A^7 * W^3 +
    (235601564 : ℝ) * S^5 * A^7 * W^1) +
    ((14552320 : ℝ) * S^5 * A^6 * W^7 +
    (-104151488 : ℝ) * S^5 * A^6 * W^5))) +
    ((((2071827808 : ℝ) * S^5 * A^6 * W^3 +
    (-10123058816 : ℝ) * S^5 * A^6 * W^1) +
    ((-6258688 : ℝ) * S^5 * A^5 * W^9 +
    (536922112 : ℝ) * S^5 * A^5 * W^7)) +
    (((48613120 : ℝ) * S^5 * A^5 * W^5 +
    (-26823042176 : ℝ) * S^5 * A^5 * W^3) +
    ((61404672192 : ℝ) * S^5 * A^5 * W^1 +
    (786432 : ℝ) * S^5 * A^4 * W^11)))) +
    ((((-248905728 : ℝ) * S^5 * A^4 * W^9 +
    ((2133030912 : ℝ) * S^5 * A^4 * W^7 +
    (-14187236352 : ℝ) * S^5 * A^4 * W^5)) +
    (((34008865344 : ℝ) * S^5 * A^4 * W^3 +
    (18748099584 : ℝ) * S^5 * A^4 * W^1) +
    ((-1450967040 : ℝ) * S^5 * A^3 * W^9 +
    (493387776 : ℝ) * S^5 * A^3 * W^7))) +
    ((((60237153792 : ℝ) * S^5 * A^3 * W^5 +
    (28767407616 : ℝ) * S^5 * A^3 * W^3) +
    ((-783701111808 : ℝ) * S^5 * A^3 * W^1 +
    (169869312 : ℝ) * S^5 * A^2 * W^11)) +
    (((-25841369088 : ℝ) * S^5 * A^2 * W^9 +
    (511455154176 : ℝ) * S^5 * A^2 * W^7) +
    ((-2433394040832 : ℝ) * S^5 * A^2 * W^5 +
    (3191201501184 : ℝ) * S^5 * A^2 * W^3)))))) / (1358954496 : ℝ)

/- Monomial group 10 of the exact D1 expansion. -/
def modularThetaCompactD1Part10 (S A W : ℝ) : ℝ :=
  ((((((9438262788096 : ℝ) * S^5 * A^2 * W^1 +
    ((-210000936960 : ℝ) * S^5 * A^1 * W^7 +
    (7357960028160 : ℝ) * S^5 * A^1 * W^5)) +
    (((-28443306885120 : ℝ) * S^5 * A^1 * W^3 +
    (-8285322608640 : ℝ) * S^5 * A^1 * W^1) +
    ((-181945 : ℝ) * S^4 * A^10 +
    (4013513 : ℝ) * S^4 * A^9 * W^2))) +
    ((((-16931793 : ℝ) * S^4 * A^9 +
    (3846848 : ℝ) * S^4 * A^8 * W^4) +
    ((45927792 : ℝ) * S^4 * A^8 * W^2 +
    (-65915260 : ℝ) * S^4 * A^8)) +
    (((-15915520 : ℝ) * S^4 * A^7 * W^6 +
    (-604001920 : ℝ) * S^4 * A^7 * W^4) +
    ((2772739648 : ℝ) * S^4 * A^7 * W^2 +
    (-11206508512 : ℝ) * S^4 * A^7)))) +
    ((((29622272 : ℝ) * S^4 * A^6 * W^8 +
    ((-1570278400 : ℝ) * S^4 * A^6 * W^6 +
    (11772803840 : ℝ) * S^4 * A^6 * W^4)) +
    (((-67156760320 : ℝ) * S^4 * A^6 * W^2 +
    (342819155184 : ℝ) * S^4 * A^6) +
    ((-5767168 : ℝ) * S^4 * A^5 * W^10 +
    (1667825664 : ℝ) * S^4 * A^5 * W^8))) +
    ((((-1713774592 : ℝ) * S^4 * A^5 * W^6 +
    (-26837242880 : ℝ) * S^4 * A^5 * W^4) +
    ((969757160448 : ℝ) * S^4 * A^5 * W^2 +
    (-3577244815104 : ℝ) * S^4 * A^5)) +
    (((-349175808 : ℝ) * S^4 * A^4 * W^10 +
    (28041805824 : ℝ) * S^4 * A^4 * W^8) +
    ((-31515205632 : ℝ) * S^4 * A^4 * W^6 +
    (363377513472 : ℝ) * S^4 * A^4 * W^4)))))) / (7247757312 : ℝ)

/- Monomial group 11 of the exact D1 expansion. -/
def modularThetaCompactD1Part11 (S A W : ℝ) : ℝ :=
  ((((((-1261673112576 : ℝ) * S^4 * A^4 * W^2 +
    ((3417709905792 : ℝ) * S^4 * A^4 +
    (-226492416 : ℝ) * S^4 * A^3 * W^10)) +
    (((7361003520 : ℝ) * S^4 * A^3 * W^8 +
    (41730895872 : ℝ) * S^4 * A^3 * W^6) +
    ((-1500597811200 : ℝ) * S^4 * A^3 * W^4 +
    (7199494410240 : ℝ) * S^4 * A^3 * W^2))) +
    ((((-12973036105728 : ℝ) * S^4 * A^3 +
    (-6983516160 : ℝ) * S^4 * A^2 * W^10) +
    ((286994202624 : ℝ) * S^4 * A^2 * W^8 +
    (-2984219172864 : ℝ) * S^4 * A^2 * W^6)) +
    (((11204710981632 : ℝ) * S^4 * A^2 * W^4 +
    (-22995648479232 : ℝ) * S^4 * A^2 * W^2) +
    ((29188724336640 : ℝ) * S^4 * A^2 +
    (-4883742720 : ℝ) * S^4 * A^1 * W^8)))) +
    ((((541604413440 : ℝ) * S^4 * A^1 * W^6 +
    ((-7499677040640 : ℝ) * S^4 * A^1 * W^4 +
    (22930247024640 : ℝ) * S^4 * A^1 * W^2)) +
    (((-29301500805120 : ℝ) * S^4 * A^1 +
    (9284618649600 : ℝ) * S^4) +
    ((-48785 : ℝ) * S^3 * A^10 * W^1 +
    (-504676 : ℝ) * S^3 * A^9 * W^3))) +
    ((((-123222 : ℝ) * S^3 * A^9 * W^1 +
    (-1125248 : ℝ) * S^3 * A^8 * W^5) +
    ((39393024 : ℝ) * S^3 * A^8 * W^3 +
    (55565320 : ℝ) * S^3 * A^8 * W^1)) +
    (((-2453504 : ℝ) * S^3 * A^7 * W^7 +
    (-11172864 : ℝ) * S^3 * A^7 * W^5) +
    ((516563168 : ℝ) * S^3 * A^7 * W^3 +
    (-4812508448 : ℝ) * S^3 * A^7 * W^1)))))) / (1207959552 : ℝ)

/- Monomial group 12 of the exact D1 expansion. -/
def modularThetaCompactD1Part12 (S A W : ℝ) : ℝ :=
  ((((((896 : ℝ) * S^3 * A^6 * W^9 +
    ((-272264 : ℝ) * S^3 * A^6 * W^7 +
    (-416947 : ℝ) * S^3 * A^6 * W^5)) +
    (((-30287574 : ℝ) * S^3 * A^6 * W^3 +
    (77994216 : ℝ) * S^3 * A^6 * W^1) +
    ((136704 : ℝ) * S^3 * A^5 * W^9 +
    (-7197056 : ℝ) * S^3 * A^5 * W^7))) +
    ((((-15217068 : ℝ) * S^3 * A^5 * W^5 +
    (169968822 : ℝ) * S^3 * A^5 * W^3) +
    ((-46374972 : ℝ) * S^3 * A^5 * W^1 +
    (-24576 : ℝ) * S^3 * A^4 * W^11)) +
    (((3225600 : ℝ) * S^3 * A^4 * W^9 +
    (-38458944 : ℝ) * S^3 * A^4 * W^7) +
    ((187396200 : ℝ) * S^3 * A^4 * W^5 +
    (306843882 : ℝ) * S^3 * A^4 * W^3)))) +
    ((((-1597026564 : ℝ) * S^3 * A^4 * W^1 +
    ((13492224 : ℝ) * S^3 * A^3 * W^9 +
    (68759424 : ℝ) * S^3 * A^3 * W^7)) +
    (((-1226757744 : ℝ) * S^3 * A^3 * W^5 +
    (2638188612 : ℝ) * S^3 * A^3 * W^3) +
    ((3248743248 : ℝ) * S^3 * A^3 * W^1 +
    (-1769472 : ℝ) * S^3 * A^2 * W^11))) +
    ((((195913728 : ℝ) * S^3 * A^2 * W^9 +
    (-3768391296 : ℝ) * S^3 * A^2 * W^7) +
    ((19335915648 : ℝ) * S^3 * A^2 * W^5 +
    (-29207870784 : ℝ) * S^3 * A^2 * W^3)) +
    (((-4124986560 : ℝ) * S^3 * A^2 * W^1 +
    (196162560 : ℝ) * S^3 * A^1 * W^7) +
    ((-6413022720 : ℝ) * S^3 * A^1 * W^5 +
    (27969727680 : ℝ) * S^3 * A^1 * W^3)))))) / (2359296 : ℝ)

/- Monomial group 13 of the exact D1 expansion. -/
def modularThetaCompactD1Part13 (S A W : ℝ) : ℝ :=
  ((((((4972499435520 : ℝ) * S^3 * A^1 * W^1 +
    ((-2009 : ℝ) * S^2 * A^11 +
    (491784 : ℝ) * S^2 * A^10 * W^2)) +
    (((-2171020 : ℝ) * S^2 * A^10 +
    (2247232 : ℝ) * S^2 * A^9 * W^4) +
    ((-4652488 : ℝ) * S^2 * A^9 * W^2 +
    (-27178248 : ℝ) * S^2 * A^9))) +
    ((((2573312 : ℝ) * S^2 * A^8 * W^6 +
    (14938624 : ℝ) * S^2 * A^8 * W^4) +
    ((429614016 : ℝ) * S^2 * A^8 * W^2 +
    (-751867824 : ℝ) * S^2 * A^8)) +
    (((-196608 : ℝ) * S^2 * A^7 * W^8 +
    (-5898240 : ℝ) * S^2 * A^7 * W^6) +
    ((3268129280 : ℝ) * S^2 * A^7 * W^4 +
    (-9782594304 : ℝ) * S^2 * A^7 * W^2)))) +
    ((((52196256960 : ℝ) * S^2 * A^7 +
    ((-90177536 : ℝ) * S^2 * A^6 * W^8 +
    (3025129472 : ℝ) * S^2 * A^6 * W^6)) +
    (((-12497555456 : ℝ) * S^2 * A^6 * W^4 +
    (170310882816 : ℝ) * S^2 * A^6 * W^2) +
    ((-697257873792 : ℝ) * S^2 * A^6 +
    (29360128 : ℝ) * S^2 * A^5 * W^10))) +
    ((((-3007578112 : ℝ) * S^2 * A^5 * W^8 +
    (-2878750720 : ℝ) * S^2 * A^5 * W^6) +
    ((93744881664 : ℝ) * S^2 * A^5 * W^4 +
    (-1910464985088 : ℝ) * S^2 * A^5 * W^2)) +
    (((4852489637376 : ℝ) * S^2 * A^5 +
    (1019215872 : ℝ) * S^2 * A^4 * W^10) +
    ((-56796119040 : ℝ) * S^2 * A^4 * W^8 +
    (101243437056 : ℝ) * S^2 * A^4 * W^6)))))) / (3221225472 : ℝ)

/- Monomial group 14 of the exact D1 expansion. -/
def modularThetaCompactD1Part14 (S A W : ℝ) : ℝ :=
  ((((((-133611589632 : ℝ) * S^2 * A^4 * W^4 +
    ((1074960009216 : ℝ) * S^2 * A^4 * W^2 +
    (-2022125856768 : ℝ) * S^2 * A^4)) +
    (((188743680 : ℝ) * S^2 * A^3 * W^10 +
    (-5537267712 : ℝ) * S^2 * A^3 * W^8) +
    ((-109017661440 : ℝ) * S^2 * A^3 * W^6 +
    (1778165526528 : ℝ) * S^2 * A^3 * W^4))) +
    ((((-6295562625024 : ℝ) * S^2 * A^3 * W^2 +
    (7684346327040 : ℝ) * S^2 * A^3) +
    ((5096079360 : ℝ) * S^2 * A^2 * W^10 +
    (-189243850752 : ℝ) * S^2 * A^2 * W^8)) +
    (((2131750010880 : ℝ) * S^2 * A^2 * W^6 +
    (-8821484568576 : ℝ) * S^2 * A^2 * W^4) +
    ((17223368048640 : ℝ) * S^2 * A^2 * W^2 +
    (-15093767577600 : ℝ) * S^2 * A^2)))) +
    ((((3114270720 : ℝ) * S^2 * A^1 * W^8 +
    ((-261979176960 : ℝ) * S^2 * A^1 * W^6 +
    (3808868106240 : ℝ) * S^2 * A^1 * W^4)) +
    (((-13041822597120 : ℝ) * S^2 * A^1 * W^2 +
    (12081092198400 : ℝ) * S^2 * A^1) +
    ((-2876099788800 : ℝ) * S^2 +
    (-4621 : ℝ) * S^1 * A^11 * W^1))) +
    ((((-62860 : ℝ) * S^1 * A^10 * W^3 +
    (-278310 : ℝ) * S^1 * A^10 * W^1) +
    ((-67072 : ℝ) * S^1 * A^9 * W^5 +
    (1122472 : ℝ) * S^1 * A^9 * W^3)) +
    (((-135462 : ℝ) * S^1 * A^9 * W^1 +
    (-1024 : ℝ) * S^1 * A^8 * W^7) +
    ((2638080 : ℝ) * S^1 * A^8 * W^5 +
    (-9993280 : ℝ) * S^1 * A^8 * W^3)))))) / (268435456 : ℝ)

/- Monomial group 15 of the exact D1 expansion. -/
def modularThetaCompactD1Part15 (S A W : ℝ) : ℝ :=
  ((((((-14889975 : ℝ) * S^1 * A^8 * W^1 +
    ((111616 : ℝ) * S^1 * A^7 * W^7 +
    (3095968 : ℝ) * S^1 * A^7 * W^5)) +
    (((-42177628 : ℝ) * S^1 * A^7 * W^3 +
    (182518536 : ℝ) * S^1 * A^7 * W^1) +
    ((-40960 : ℝ) * S^1 * A^6 * W^9 +
    (3904768 : ℝ) * S^1 * A^6 * W^7))) +
    ((((26827712 : ℝ) * S^1 * A^6 * W^5 +
    (459760560 : ℝ) * S^1 * A^6 * W^3) +
    ((-368800416 : ℝ) * S^1 * A^6 * W^1 +
    (-2490368 : ℝ) * S^1 * A^5 * W^9)) +
    (((111454208 : ℝ) * S^1 * A^5 * W^7 +
    (609634560 : ℝ) * S^1 * A^5 * W^5) +
    ((-676388544 : ℝ) * S^1 * A^5 * W^3 +
    (-3212483904 : ℝ) * S^1 * A^5 * W^1)))) +
    ((((786432 : ℝ) * S^1 * A^4 * W^11 +
    ((-54657024 : ℝ) * S^1 * A^4 * W^9 +
    (953177088 : ℝ) * S^1 * A^4 * W^7)) +
    (((-2538837504 : ℝ) * S^1 * A^4 * W^5 +
    (-6633734976 : ℝ) * S^1 * A^4 * W^3) +
    ((13891488768 : ℝ) * S^1 * A^4 * W^1 +
    (-189923328 : ℝ) * S^1 * A^3 * W^9))) +
    ((((-1944354816 : ℝ) * S^1 * A^3 * W^7 +
    (23584504320 : ℝ) * S^1 * A^3 * W^5) +
    ((-89170633728 : ℝ) * S^1 * A^3 * W^3 +
    (44236108800 : ℝ) * S^1 * A^3 * W^1)) +
    (((28311552 : ℝ) * S^1 * A^2 * W^11 +
    (-2431254528 : ℝ) * S^1 * A^2 * W^9) +
    ((45892251648 : ℝ) * S^1 * A^2 * W^7 +
    (-251464310784 : ℝ) * S^1 * A^2 * W^5)))))) / (16777216 : ℝ)

/- Monomial group 16 of the exact D1 expansion. -/
def modularThetaCompactD1Part16 (S A W : ℝ) : ℝ :=
  ((((((213471579340800 : ℝ) * S^1 * A^2 * W^3 +
    ((-24394931896320 : ℝ) * S^1 * A^2 * W^1 +
    (-876525649920 : ℝ) * S^1 * A^1 * W^7)) +
    (((27151910830080 : ℝ) * S^1 * A^1 * W^5 +
    (-129369070632960 : ℝ) * S^1 * A^1 * W^3) +
    ((902006046720 : ℝ) * S^1 * A^1 * W^1 +
    (14025 : ℝ) * A^12))) +
    ((((297096 : ℝ) * A^11 * W^2 +
    (-211920 : ℝ) * A^11) +
    ((304896 : ℝ) * A^10 * W^4 +
    (-14581632 : ℝ) * A^10 * W^2)) +
    (((-7542720 : ℝ) * A^10 +
    (12288 : ℝ) * A^9 * W^6) +
    ((-29852160 : ℝ) * A^9 * W^4 +
    (265283424 : ℝ) * A^9 * W^2)))) +
    ((((63974304 : ℝ) * A^9 +
    ((-21602304 : ℝ) * A^8 * W^6 +
    (819406848 : ℝ) * A^8 * W^4)) +
    (((-5788445184 : ℝ) * A^8 * W^2 +
    (18394725888 : ℝ) * A^8) +
    ((1572864 : ℝ) * A^7 * W^8 +
    (853917696 : ℝ) * A^7 * W^6))) +
    ((((-16193015808 : ℝ) * A^7 * W^4 +
    (96529545216 : ℝ) * A^7 * W^2) +
    ((-313636382208 : ℝ) * A^7 +
    (100663296 : ℝ) * A^6 * W^8)) +
    (((-8796733440 : ℝ) * A^6 * W^6 +
    (93009530880 : ℝ) * A^6 * W^4) +
    ((-1123168038912 : ℝ) * A^6 * W^2 +
    (2345804914176 : ℝ) * A^6)))))) / (8589934592 : ℝ)

/- Monomial group 17 of the exact D1 expansion. -/
def modularThetaCompactD1Part17 (S A W : ℝ) : ℝ :=
  ((((((-18432 : ℝ) * A^5 * W^10 +
    ((205056 : ℝ) * A^5 * W^8 +
    (8513064 : ℝ) * A^5 * W^6)) +
    (((-171373554 : ℝ) * A^5 * W^4 +
    (960760062 : ℝ) * A^5 * W^2) +
    ((-1723813569 : ℝ) * A^5 +
    (-626688 : ℝ) * A^4 * W^10))) +
    ((((21399552 : ℝ) * A^4 * W^8 +
    (-119308752 : ℝ) * A^4 * W^6) +
    ((1309914828 : ℝ) * A^4 * W^4 +
    (-6563995704 : ℝ) * A^4 * W^2)) +
    (((10403454510 : ℝ) * A^4 +
    (-663552 : ℝ) * A^3 * W^10) +
    ((32679936 : ℝ) * A^3 * W^8 +
    (1048247136 : ℝ) * A^3 * W^6)))) +
    ((((-12220044912 : ℝ) * A^3 * W^4 +
    ((41151875040 : ℝ) * A^3 * W^2 +
    (-42350681520 : ℝ) * A^3)) +
    (((-22560768 : ℝ) * A^2 * W^10 +
    (781332480 : ℝ) * A^2 * W^8) +
    ((-10126461888 : ℝ) * A^2 * W^6 +
    (48752565120 : ℝ) * A^2 * W^4))) +
    ((((-97228771200 : ℝ) * A^2 * W^2 +
    (67107132720 : ℝ) * A^2) +
    ((-14929920 : ℝ) * A^1 * W^8 +
    (958314240 : ℝ) * A^1 * W^6)) +
    (((-14679843840 : ℝ) * A^1 * W^4 +
    (56969775360 : ℝ) * A^1 * W^2) +
    ((-41346547200 : ℝ) * A^1 +
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
