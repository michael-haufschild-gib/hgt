import GaloisForLFunctions.RHTower.RoutePFourthDepthCoPoissonJuliaKreinPivot
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolMatrixCompleteColligation
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Route P primitive Burnol Julia--Krein matrix completion

P-G105B realized the fourth-depth Julia co-graph as a two-channel Krein pivot, but only on
one even co-Poisson vector at a time.  P-G186's actual finite feature packets live instead in
Burnol's half-line aperture space.  This file proves that the same coefficient law tensorizes
over that entire carrier, including every off-diagonal prime/depth/ordinate interaction.

For a half-line feature `f`, put

```text
child f = ((1 / 8) f, 0),
pivot f = (sqrt 63 f, 8 f).
```

Their signature `(+, -)` Gram is the universal Julia--Krein block

```text
B = [[1 / 64, d], [d, -1]],   d = sqrt 63 / 8,
```

times the original feature Gram.  Consequently the complete `2N`-dimensional matrix is exactly
`B ⊗ G`, its determinant is `(-1)^N det(G)^(2 : ℕ)`, and completion is nondegenerate exactly when
the original P-G186 Gram is nondegenerate.  No diagonal or orthogonality assumption is used.

This is a matrix-complete algebraic completion theorem.  It does not yet prove that the negative
channel is the literal Gamma/Stokes co-source, nor that the resulting cofinal incidence lands in
the Xi divisor.
-/

open Complex Matrix Set MeasureTheory
open scoped InnerProductSpace Kronecker

namespace RHTower

noncomputable section

/-- Two-channel Krein carrier over Burnol's actual P-G186 half-line feature space. -/
abbrev routePPrimitiveBurnolJuliaKreinCarrier :=
  routePBurnolHalfLineL2 × routePBurnolHalfLineL2

/-- Diagonal signature `(+, -)` pairing on the P-G186 carrier. -/
def routePPrimitiveBurnolJuliaKreinPair
    (x y : routePPrimitiveBurnolJuliaKreinCarrier) : ℂ :=
  ⟪x.1, y.1⟫_ℂ - ⟪x.2, y.2⟫_ℂ

/-- Fourth-depth contracted child in the positive channel. -/
def routePPrimitiveBurnolJuliaKreinChild
    (f : routePBurnolHalfLineL2) : routePPrimitiveBurnolJuliaKreinCarrier :=
  ((routeEPCubicFourthDepthNormalizedContraction : ℂ) • f, 0)

/-- Canonical Julia co-graph pivot, with coefficients `d / c = sqrt 63` and `1 / c = 8`. -/
def routePPrimitiveBurnolJuliaKreinPivot
    (f : routePBurnolHalfLineL2) : routePPrimitiveBurnolJuliaKreinCarrier :=
  ((Real.sqrt 63 : ℂ) • f, (8 : ℂ) • f)

/-- Child--child pairing preserves every off-diagonal feature inner product at scale `1 / 64`. -/
theorem routePPrimitiveBurnolJuliaKreinPair_child_child
    (f g : routePBurnolHalfLineL2) :
    routePPrimitiveBurnolJuliaKreinPair
        (routePPrimitiveBurnolJuliaKreinChild f)
        (routePPrimitiveBurnolJuliaKreinChild g) =
      (1 / 64 : ℂ) * ⟪f, g⟫_ℂ := by
  rw [routePPrimitiveBurnolJuliaKreinPair,
    routePPrimitiveBurnolJuliaKreinChild,
    routePPrimitiveBurnolJuliaKreinChild]
  simp only [sub_zero, inner_zero_left]
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  norm_num [routeEPCubicFourthDepthNormalizedContraction]
  ring

/-- Child--pivot pairing is the Julia defect times the full feature inner product. -/
theorem routePPrimitiveBurnolJuliaKreinPair_child_pivot
    (f g : routePBurnolHalfLineL2) :
    routePPrimitiveBurnolJuliaKreinPair
        (routePPrimitiveBurnolJuliaKreinChild f)
        (routePPrimitiveBurnolJuliaKreinPivot g) =
      (routeEPCubicFourthDepthJuliaDefect : ℂ) * ⟪f, g⟫_ℂ := by
  rw [routePPrimitiveBurnolJuliaKreinPair,
    routePPrimitiveBurnolJuliaKreinChild,
    routePPrimitiveBurnolJuliaKreinPivot]
  simp only [inner_zero_left, sub_zero]
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    routeEPCubicFourthDepthJuliaDefect_eq_sqrt63_div_eight]
  norm_num [routeEPCubicFourthDepthNormalizedContraction]
  ring

/-- Pivot--child pairing is the same real Julia defect times the reverse feature entry. -/
theorem routePPrimitiveBurnolJuliaKreinPair_pivot_child
    (f g : routePBurnolHalfLineL2) :
    routePPrimitiveBurnolJuliaKreinPair
        (routePPrimitiveBurnolJuliaKreinPivot f)
        (routePPrimitiveBurnolJuliaKreinChild g) =
      (routeEPCubicFourthDepthJuliaDefect : ℂ) * ⟪f, g⟫_ℂ := by
  rw [routePPrimitiveBurnolJuliaKreinPair,
    routePPrimitiveBurnolJuliaKreinPivot,
    routePPrimitiveBurnolJuliaKreinChild]
  simp only [inner_zero_right, sub_zero]
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    routeEPCubicFourthDepthJuliaDefect_eq_sqrt63_div_eight]
  norm_num [routeEPCubicFourthDepthNormalizedContraction]
  ring

/-- Julia's Pythagorean identity makes the pivot pairing exactly the negative original Gram. -/
theorem routePPrimitiveBurnolJuliaKreinPair_pivot_pivot
    (f g : routePBurnolHalfLineL2) :
    routePPrimitiveBurnolJuliaKreinPair
        (routePPrimitiveBurnolJuliaKreinPivot f)
        (routePPrimitiveBurnolJuliaKreinPivot g) =
      -⟪f, g⟫_ℂ := by
  rw [routePPrimitiveBurnolJuliaKreinPair,
    routePPrimitiveBurnolJuliaKreinPivot,
    routePPrimitiveBurnolJuliaKreinPivot]
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [inner_smul_left, inner_smul_right]
  have hsqrt : Real.sqrt 63 ^ (2 : ℕ) = 63 := Real.sq_sqrt (by norm_num)
  have hsqrtC : (Real.sqrt 63 : ℂ) ^ (2 : ℕ) = 63 := by
    exact_mod_cast hsqrt
  rw [starRingEnd_apply, star_ofNat]
  calc
    (Real.sqrt 63 : ℂ) * ((Real.sqrt 63 : ℂ) * ⟪f, g⟫_ℂ) -
        8 * (8 * ⟪f, g⟫_ℂ) =
        (((Real.sqrt 63 : ℂ) ^ (2 : ℕ)) - 64) * ⟪f, g⟫_ℂ := by ring
    _ = -⟪f, g⟫_ℂ := by rw [hsqrtC]; ring

/-- Universal two-channel Julia--Krein coefficient block. -/
def routePPrimitiveBurnolJuliaKreinBlock : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 / 64 : ℂ), (routeEPCubicFourthDepthJuliaDefect : ℂ);
    (routeEPCubicFourthDepthJuliaDefect : ℂ), -1]

/-- The universal coefficient block has determinant `-1`; no target-dependent fitting remains. -/
theorem routePPrimitiveBurnolJuliaKreinBlock_det :
    routePPrimitiveBurnolJuliaKreinBlock.det = -1 := by
  rw [routePPrimitiveBurnolJuliaKreinBlock, Matrix.det_fin_two]
  simp
  have h := routeEPCubicFourthDepthJulia_pythagoras
  norm_num [routeEPCubicFourthDepthNormalizedContraction] at h
  have hd : routeEPCubicFourthDepthJuliaDefect ^ (2 : ℕ) = (63 / 64 : ℝ) := by
    nlinarith
  have hdC : (routeEPCubicFourthDepthJuliaDefect : ℂ) ^ (2 : ℕ) = 63 / 64 := by
    calc
      (routeEPCubicFourthDepthJuliaDefect : ℂ) ^ (2 : ℕ) =
          ((routeEPCubicFourthDepthJuliaDefect ^ (2 : ℕ) : ℝ) : ℂ) :=
        (Complex.ofReal_pow _ _).symm
      _ = ((63 / 64 : ℝ) : ℂ) := congrArg (fun x : ℝ => (x : ℂ)) hd
      _ = 63 / 64 := Complex.ofReal_div _ _
  rw [show (routeEPCubicFourthDepthJuliaDefect : ℂ) *
      routeEPCubicFourthDepthJuliaDefect = 63 / 64 by
    simpa [pow_two] using hdC]
  norm_num

/-- Child and pivot channels attached functorially to one P-G186 half-line feature. -/
def routePPrimitiveBurnolJuliaKreinChannels
    (f : routePBurnolHalfLineL2) : Fin 2 → routePPrimitiveBurnolJuliaKreinCarrier :=
  ![routePPrimitiveBurnolJuliaKreinChild f,
    routePPrimitiveBurnolJuliaKreinPivot f]

/-- Matrix-complete Julia--Krein pairing for an arbitrary finite P-G186 feature packet. -/
def routePPrimitiveBurnolJuliaKreinCompletedGramMatrix {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ :=
  fun ai bj => routePPrimitiveBurnolJuliaKreinPair
    (routePPrimitiveBurnolJuliaKreinChannels
      (routePPrimitiveBurnolWindowFeatureLp (pe ai.2) (kappa ai.2)) ai.1)
    (routePPrimitiveBurnolJuliaKreinChannels
      (routePPrimitiveBurnolWindowFeatureLp (pe bj.2) (kappa bj.2)) bj.1)

/-- **P-G105C Kronecker law.** The complete Krein matrix is the universal Julia block tensor the
actual P-G186 Gram, including all off-diagonal prime/depth/ordinate incidences. -/
theorem routePPrimitiveBurnolJuliaKreinCompletedGramMatrix_eq_kronecker {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    routePPrimitiveBurnolJuliaKreinCompletedGramMatrix pe kappa =
      routePPrimitiveBurnolJuliaKreinBlock ⊗ₖ
        routePPrimitiveBurnolWindowGramMatrix pe kappa := by
  rw [routePPrimitiveBurnolWindowGramMatrix_eq_gram_L2]
  ext ai bj
  rcases ai with ⟨a, i⟩
  rcases bj with ⟨b, j⟩
  fin_cases a <;> fin_cases b
  · simp [routePPrimitiveBurnolJuliaKreinCompletedGramMatrix,
      routePPrimitiveBurnolJuliaKreinChannels,
      routePPrimitiveBurnolJuliaKreinBlock, Matrix.gram_apply,
      routePPrimitiveBurnolJuliaKreinPair_child_child]
  · simp [routePPrimitiveBurnolJuliaKreinCompletedGramMatrix,
      routePPrimitiveBurnolJuliaKreinChannels,
      routePPrimitiveBurnolJuliaKreinBlock, Matrix.gram_apply,
      routePPrimitiveBurnolJuliaKreinPair_child_pivot]
  · simp [routePPrimitiveBurnolJuliaKreinCompletedGramMatrix,
      routePPrimitiveBurnolJuliaKreinChannels,
      routePPrimitiveBurnolJuliaKreinBlock, Matrix.gram_apply,
      routePPrimitiveBurnolJuliaKreinPair_pivot_child]
  · simp [routePPrimitiveBurnolJuliaKreinCompletedGramMatrix,
      routePPrimitiveBurnolJuliaKreinChannels,
      routePPrimitiveBurnolJuliaKreinBlock, Matrix.gram_apply,
      routePPrimitiveBurnolJuliaKreinPair_pivot_pivot]

/-- Exact finite determinant factorization of the matrix-complete Julia--Krein lift. -/
theorem routePPrimitiveBurnolJuliaKreinCompletedGramMatrix_det {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    (routePPrimitiveBurnolJuliaKreinCompletedGramMatrix pe kappa).det =
      (-1 : ℂ) ^ N *
        (routePPrimitiveBurnolWindowGramMatrix pe kappa).det ^ (2 : ℕ) := by
  rw [routePPrimitiveBurnolJuliaKreinCompletedGramMatrix_eq_kronecker,
    Matrix.det_kronecker, routePPrimitiveBurnolJuliaKreinBlock_det]
  simp

/-- Julia--Krein completion introduces no new finite degeneracy and hides none from P-G186. -/
theorem routePPrimitiveBurnolJuliaKreinCompletedGramMatrix_det_ne_zero_iff {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    (routePPrimitiveBurnolJuliaKreinCompletedGramMatrix pe kappa).det ≠ 0 ↔
      (routePPrimitiveBurnolWindowGramMatrix pe kappa).det ≠ 0 := by
  rw [routePPrimitiveBurnolJuliaKreinCompletedGramMatrix_det]
  simp

/-- P-G105C capstone: exact full-matrix factorization and determinant law, without hypotheses. -/
theorem routePPrimitiveBurnol_JuliaKrein_matrixCompletion {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    routePPrimitiveBurnolJuliaKreinCompletedGramMatrix pe kappa =
        routePPrimitiveBurnolJuliaKreinBlock ⊗ₖ
          routePPrimitiveBurnolWindowGramMatrix pe kappa ∧
      (routePPrimitiveBurnolJuliaKreinCompletedGramMatrix pe kappa).det =
        (-1 : ℂ) ^ N *
          (routePPrimitiveBurnolWindowGramMatrix pe kappa).det ^ (2 : ℕ) :=
  ⟨routePPrimitiveBurnolJuliaKreinCompletedGramMatrix_eq_kronecker pe kappa,
    routePPrimitiveBurnolJuliaKreinCompletedGramMatrix_det pe kappa⟩

end
end RHTower
