import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSourcePositiveClosure
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Source-positive/Lyapunov differential chart equivalence

The source-positive coordinates `(U,B,Q)` and Lyapunov coordinates `(S,A,W)` are polynomially
equivalent:
`S=-3B`, `A=16Q+6-6B²`, `W=U+B`.  This file proves both coordinate substitutions are inverse,
intertwines their polynomial vector fields and covariant Lie operators, and transports every
normalized source jet and the full rank-three reflected eighth polynomial without expansion.
-/

open Complex Real

namespace HTGeometry

noncomputable section

/-- Pull Lyapunov coordinates back to source-positive coordinates. -/
def modularThetaSourcePositiveChartCoordinate :
    ModularThetaLyapunovState → ModularThetaSourcePositivePolynomial
  | .S => MvPolynomial.C (-3 : ℂ) * MvPolynomial.X .B
  | .A => modularThetaSourcePositiveGap
  | .W => MvPolynomial.X .U + MvPolynomial.X .B

def modularThetaSourcePositiveChartPullback :
    ModularThetaLyapunovPolynomial →+* ModularThetaSourcePositivePolynomial :=
  MvPolynomial.eval₂Hom MvPolynomial.C modularThetaSourcePositiveChartCoordinate

@[simp] theorem modularThetaSourcePositiveChartPullback_C (c : ℂ) :
    modularThetaSourcePositiveChartPullback (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [modularThetaSourcePositiveChartPullback]

@[simp] theorem modularThetaSourcePositiveChartPullback_X
    (i : ModularThetaLyapunovState) :
    modularThetaSourcePositiveChartPullback (MvPolynomial.X i) =
      modularThetaSourcePositiveChartCoordinate i := by
  simp [modularThetaSourcePositiveChartPullback]

/-- Inverse coordinate chart: `(S,A,W)` recovered from `(U,B,Q)`. -/
def modularThetaLyapunovChartCoordinate :
    ModularThetaSourcePositiveState → ModularThetaLyapunovPolynomial
  | .U => MvPolynomial.X .W +
      MvPolynomial.C (1 / 3 : ℂ) * MvPolynomial.X .S
  | .B => MvPolynomial.C (-(1 / 3 : ℂ)) * MvPolynomial.X .S
  | .Q => MvPolynomial.C (1 / 16 : ℂ) * MvPolynomial.X .A +
      MvPolynomial.C (1 / 24 : ℂ) * MvPolynomial.X .S ^ 2 -
      MvPolynomial.C (3 / 8 : ℂ)

def modularThetaSourcePositiveChartInverse :
    ModularThetaSourcePositivePolynomial →+* ModularThetaLyapunovPolynomial :=
  MvPolynomial.eval₂Hom MvPolynomial.C modularThetaLyapunovChartCoordinate

@[simp] theorem modularThetaSourcePositiveChartInverse_C (c : ℂ) :
    modularThetaSourcePositiveChartInverse (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [modularThetaSourcePositiveChartInverse]

@[simp] theorem modularThetaSourcePositiveChartInverse_X
    (i : ModularThetaSourcePositiveState) :
    modularThetaSourcePositiveChartInverse (MvPolynomial.X i) =
      modularThetaLyapunovChartCoordinate i := by
  simp [modularThetaSourcePositiveChartInverse]

theorem modularThetaSourcePositiveChartInverse_comp_pullback :
    modularThetaSourcePositiveChartInverse.comp
        modularThetaSourcePositiveChartPullback =
      RingHom.id ModularThetaLyapunovPolynomial := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    cases i <;>
      simp [modularThetaSourcePositiveChartCoordinate,
        modularThetaLyapunovChartCoordinate,
        modularThetaSourcePositiveGap]
    all_goals
      apply MvPolynomial.funext
      intro v
      simp
    all_goals ring

theorem modularThetaSourcePositiveChartPullback_comp_inverse :
    modularThetaSourcePositiveChartPullback.comp
        modularThetaSourcePositiveChartInverse =
      RingHom.id ModularThetaSourcePositivePolynomial := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    cases i <;>
      simp [modularThetaSourcePositiveChartCoordinate,
        modularThetaLyapunovChartCoordinate,
        modularThetaSourcePositiveGap]
    all_goals
      apply MvPolynomial.funext
      intro v
      simp
    all_goals ring

theorem modularThetaSourcePositiveChartPullback_injective :
    Function.Injective modularThetaSourcePositiveChartPullback := by
  intro P Q hPQ
  have h := congrArg modularThetaSourcePositiveChartInverse hPQ
  simpa [← RingHom.comp_apply,
    modularThetaSourcePositiveChartInverse_comp_pullback] using h

theorem modularThetaSourcePositiveLie_mul
    (P Q : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveLie (P * Q) =
      modularThetaSourcePositiveLie P * Q + P * modularThetaSourcePositiveLie Q := by
  unfold modularThetaSourcePositiveLie
  simp_rw [MvPolynomial.pderiv_mul, add_mul]
  rw [Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem modularThetaSourcePositiveLie_add
    (P Q : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveLie (P + Q) =
      modularThetaSourcePositiveLie P + modularThetaSourcePositiveLie Q := by
  simp [modularThetaSourcePositiveLie, add_mul, Finset.sum_add_distrib]

theorem modularThetaSourcePositiveLie_sub
    (P Q : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveLie (P - Q) =
      modularThetaSourcePositiveLie P - modularThetaSourcePositiveLie Q := by
  simp [modularThetaSourcePositiveLie, sub_mul, Finset.sum_sub_distrib]

theorem modularThetaSourcePositiveLie_C (c : ℂ) :
    modularThetaSourcePositiveLie (MvPolynomial.C c) = 0 := by
  simp [modularThetaSourcePositiveLie]

theorem modularThetaSourcePositiveLie_X (i : ModularThetaSourcePositiveState) :
    modularThetaSourcePositiveLie (MvPolynomial.X i) =
      modularThetaSourcePositiveVectorField i := by
  unfold modularThetaSourcePositiveLie
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [MvPolynomial.pderiv_X, Ne.symm hji]
  · intro hi
    simp at hi

theorem modularThetaSourcePositiveLie_gap :
    modularThetaSourcePositiveLie modularThetaSourcePositiveGap =
      MvPolynomial.C (-2 : ℂ) * modularThetaSourcePositiveGap *
        (MvPolynomial.X .U + MvPolynomial.X .B) := by
  unfold modularThetaSourcePositiveGap
  simp only [modularThetaSourcePositiveLie_sub,
    modularThetaSourcePositiveLie_add,
    modularThetaSourcePositiveLie_mul,
    modularThetaSourcePositiveLie_C,
    modularThetaSourcePositiveLie_X,
    pow_two, zero_mul, zero_add]
  unfold modularThetaSourcePositiveVectorField modularThetaSourcePositiveGap
  apply MvPolynomial.funext
  intro v
  simp
  ring

theorem modularThetaLyapunovLie_mul_local
    (P Q : ModularThetaLyapunovPolynomial) :
    modularThetaLyapunovLie (P * Q) =
      modularThetaLyapunovLie P * Q + P * modularThetaLyapunovLie Q := by
  unfold modularThetaLyapunovLie
  simp_rw [MvPolynomial.pderiv_mul, add_mul]
  rw [Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem modularThetaLyapunovLie_add_local
    (P Q : ModularThetaLyapunovPolynomial) :
    modularThetaLyapunovLie (P + Q) =
      modularThetaLyapunovLie P + modularThetaLyapunovLie Q := by
  simp [modularThetaLyapunovLie, add_mul, Finset.sum_add_distrib]

theorem modularThetaLyapunovLie_C_local (c : ℂ) :
    modularThetaLyapunovLie (MvPolynomial.C c) = 0 := by
  simp [modularThetaLyapunovLie]

theorem modularThetaLyapunovLie_X_local (i : ModularThetaLyapunovState) :
    modularThetaLyapunovLie (MvPolynomial.X i) =
      modularThetaLyapunovVectorField i := by
  unfold modularThetaLyapunovLie
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [MvPolynomial.pderiv_X, hji]
  · simp

theorem modularThetaSourcePositiveChart_vectorField (i : ModularThetaLyapunovState) :
    modularThetaSourcePositiveChartPullback (modularThetaLyapunovVectorField i) =
      modularThetaSourcePositiveLie (modularThetaSourcePositiveChartCoordinate i) := by
  cases i with
  | S =>
      simp only [modularThetaLyapunovVectorField, map_sub, map_mul, map_pow,
        modularThetaSourcePositiveChartPullback_C,
        modularThetaSourcePositiveChartPullback_X,
        modularThetaSourcePositiveChartCoordinate]
      rw [modularThetaSourcePositiveLie_mul,
        modularThetaSourcePositiveLie_C,
        modularThetaSourcePositiveLie_X]
      unfold modularThetaSourcePositiveVectorField modularThetaSourcePositiveGap
      apply MvPolynomial.funext
      intro v
      simp
      ring
  | A =>
      simp only [modularThetaLyapunovVectorField, map_mul,
        modularThetaSourcePositiveChartPullback_C,
        modularThetaSourcePositiveChartPullback_X,
        modularThetaSourcePositiveChartCoordinate]
      rw [modularThetaSourcePositiveLie_gap]
  | W =>
      simp only [modularThetaLyapunovVectorField, map_sub, map_mul, map_pow,
        map_add, modularThetaSourcePositiveChartPullback_C,
        modularThetaSourcePositiveChartPullback_X,
        modularThetaSourcePositiveChartCoordinate]
      rw [modularThetaSourcePositiveLie_add,
        modularThetaSourcePositiveLie_X,
        modularThetaSourcePositiveLie_X]
      unfold modularThetaSourcePositiveVectorField modularThetaSourcePositiveGap
      apply MvPolynomial.funext
      intro v
      simp
      ring

theorem modularThetaSourcePositiveChart_lie
    (P : ModularThetaLyapunovPolynomial) :
    modularThetaSourcePositiveChartPullback (modularThetaLyapunovLie P) =
      modularThetaSourcePositiveLie (modularThetaSourcePositiveChartPullback P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [modularThetaLyapunovLie_C_local,
        modularThetaSourcePositiveChartPullback_C,
        modularThetaSourcePositiveLie_C]
      simp
  | add P Q hP hQ =>
      rw [modularThetaLyapunovLie_add_local, map_add, hP, hQ, map_add,
        modularThetaSourcePositiveLie_add]
  | mul_X P i hP =>
      rw [modularThetaLyapunovLie_mul_local, modularThetaLyapunovLie_X_local,
        map_add, map_mul, map_mul, map_mul, hP,
        modularThetaSourcePositiveChartPullback_X,
        modularThetaSourcePositiveLie_mul,
        modularThetaSourcePositiveChart_vectorField]

theorem modularThetaSourcePositiveChart_normalizedLie
    (P : ModularThetaLyapunovPolynomial) :
    modularThetaSourcePositiveChartPullback (modularThetaLyapunovNormalizedLie P) =
      modularThetaSourcePositiveNormalizedLie
        (modularThetaSourcePositiveChartPullback P) := by
  unfold modularThetaLyapunovNormalizedLie modularThetaSourcePositiveNormalizedLie
  rw [map_add, map_mul, modularThetaSourcePositiveChart_lie]
  rw [map_mul, modularThetaSourcePositiveChartPullback_C,
    modularThetaSourcePositiveChartPullback_X]
  unfold modularThetaSourcePositiveChartCoordinate
  apply MvPolynomial.funext
  intro v
  simp
  left
  ring

/-- Completed theta jets expressed directly in source-positive coordinates. -/
def modularThetaSourcePositiveNormalizedHJet :
    ℕ → ModularThetaSourcePositivePolynomial
  | 0 => 1
  | n + 1 => modularThetaSourcePositiveNormalizedLie
      (modularThetaSourcePositiveNormalizedHJet n)

theorem modularThetaSourcePositiveChart_normalizedHJet (n : ℕ) :
    modularThetaSourcePositiveChartPullback
        (modularThetaLyapunovNormalizedHJet n) =
      modularThetaSourcePositiveNormalizedHJet n := by
  induction n with
  | zero => simp [modularThetaLyapunovNormalizedHJet,
      modularThetaSourcePositiveNormalizedHJet]
  | succ n ih =>
      rw [modularThetaLyapunovNormalizedHJet,
        modularThetaSourcePositiveNormalizedHJet,
        modularThetaSourcePositiveChart_normalizedLie, ih]

def modularThetaSourcePositiveNormalizedSourceJetFromH (n : ℕ) :
    ModularThetaSourcePositivePolynomial :=
  (modularThetaSourcePositiveNormalizedHJet (n + 2) -
    MvPolynomial.C (1 / 4 : ℂ) *
      modularThetaSourcePositiveNormalizedHJet n) *
    MvPolynomial.C (1 / 2 : ℂ)

theorem modularThetaSourcePositiveChart_normalizedSourceJet (n : ℕ) :
    modularThetaSourcePositiveChartPullback
        (modularThetaLyapunovNormalizedSourceJet n) =
      modularThetaSourcePositiveNormalizedSourceJetFromH n := by
  simp only [modularThetaLyapunovNormalizedSourceJet,
    modularThetaSourcePositiveNormalizedSourceJetFromH,
    map_sub, map_mul, modularThetaSourcePositiveChartPullback_C,
    modularThetaSourcePositiveChart_normalizedHJet]

theorem modularThetaSourcePositiveNormalizedSourceJetFromH_zero :
    modularThetaSourcePositiveNormalizedSourceJetFromH 0 =
      MvPolynomial.X ModularThetaSourcePositiveState.Q := by
  have hNLone : modularThetaSourcePositiveNormalizedLie
      (1 : ModularThetaSourcePositivePolynomial) =
      MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .B := by
    unfold modularThetaSourcePositiveNormalizedLie
    change modularThetaSourcePositiveLie (MvPolynomial.C 1) + _ = _
    rw [modularThetaSourcePositiveLie_C]
    ring
  unfold modularThetaSourcePositiveNormalizedSourceJetFromH
  change (modularThetaSourcePositiveNormalizedLie
      (modularThetaSourcePositiveNormalizedLie 1) -
      MvPolynomial.C (1 / 4 : ℂ) * 1) * MvPolynomial.C (1 / 2 : ℂ) = _
  rw [hNLone]
  unfold modularThetaSourcePositiveNormalizedLie
  rw [modularThetaSourcePositiveLie_mul,
    modularThetaSourcePositiveLie_C,
    modularThetaSourcePositiveLie_X]
  unfold modularThetaSourcePositiveVectorField
  apply MvPolynomial.funext
  intro v
  simp
  ring

theorem modularThetaSourcePositiveNormalizedLie_sub
    (P Q : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveNormalizedLie (P - Q) =
      modularThetaSourcePositiveNormalizedLie P -
        modularThetaSourcePositiveNormalizedLie Q := by
  unfold modularThetaSourcePositiveNormalizedLie
  rw [modularThetaSourcePositiveLie_sub]
  ring

theorem modularThetaSourcePositiveNormalizedLie_C_mul
    (c : ℂ) (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveNormalizedLie (MvPolynomial.C c * P) =
      MvPolynomial.C c * modularThetaSourcePositiveNormalizedLie P := by
  unfold modularThetaSourcePositiveNormalizedLie
  rw [modularThetaSourcePositiveLie_mul,
    modularThetaSourcePositiveLie_C]
  ring

theorem modularThetaSourcePositiveNormalizedLie_mul_C
    (P : ModularThetaSourcePositivePolynomial) (c : ℂ) :
    modularThetaSourcePositiveNormalizedLie (P * MvPolynomial.C c) =
      modularThetaSourcePositiveNormalizedLie P * MvPolynomial.C c := by
  unfold modularThetaSourcePositiveNormalizedLie
  rw [modularThetaSourcePositiveLie_mul,
    modularThetaSourcePositiveLie_C]
  ring

theorem modularThetaSourcePositiveNormalizedSourceJetFromH_succ (n : ℕ) :
    modularThetaSourcePositiveNormalizedSourceJetFromH (n + 1) =
      modularThetaSourcePositiveNormalizedLie
        (modularThetaSourcePositiveNormalizedSourceJetFromH n) := by
  unfold modularThetaSourcePositiveNormalizedSourceJetFromH
  change (modularThetaSourcePositiveNormalizedLie
        (modularThetaSourcePositiveNormalizedHJet (n + 2)) -
      MvPolynomial.C (1 / 4 : ℂ) *
        modularThetaSourcePositiveNormalizedLie
          (modularThetaSourcePositiveNormalizedHJet n)) *
      MvPolynomial.C (1 / 2 : ℂ) = _
  rw [modularThetaSourcePositiveNormalizedLie_mul_C,
    modularThetaSourcePositiveNormalizedLie_sub,
    modularThetaSourcePositiveNormalizedLie_C_mul]

theorem modularThetaSourcePositiveNormalizedSourceJetFromH_eq (n : ℕ) :
    modularThetaSourcePositiveNormalizedSourceJetFromH n =
      modularThetaSourcePositiveNormalizedSourceJet n := by
  induction n with
  | zero =>
      simpa [modularThetaSourcePositiveNormalizedSourceJet] using
        modularThetaSourcePositiveNormalizedSourceJetFromH_zero
  | succ n ih =>
      rw [modularThetaSourcePositiveNormalizedSourceJetFromH_succ, ih]
      rfl

theorem modularThetaSourcePositiveChart_sourceJet (n : ℕ) :
    modularThetaSourcePositiveChartPullback
        (modularThetaLyapunovNormalizedSourceJet n) =
      modularThetaSourcePositiveNormalizedSourceJet n := by
  rw [modularThetaSourcePositiveChart_normalizedSourceJet,
    modularThetaSourcePositiveNormalizedSourceJetFromH_eq]

theorem modularThetaSourcePositiveChart_reflectedEighthPolynomial :
    modularThetaSourcePositiveChartPullback
        modularThetaLyapunovReflectedEighthPolynomial =
      modularThetaSourcePositiveReflectedEighthPolynomial := by
  unfold modularThetaLyapunovReflectedEighthPolynomial
    modularThetaSourcePositiveReflectedEighthPolynomial
  dsimp only
  simp only [map_sub, map_mul, map_pow, map_add,
    modularThetaSourcePositiveChartPullback_C]
  rw [modularThetaSourcePositiveChart_sourceJet 0,
    modularThetaSourcePositiveChart_sourceJet 1,
    modularThetaSourcePositiveChart_sourceJet 2,
    modularThetaSourcePositiveChart_sourceJet 3,
    modularThetaSourcePositiveChart_sourceJet 4,
    modularThetaSourcePositiveChart_sourceJet 5,
    modularThetaSourcePositiveChart_sourceJet 6,
    modularThetaSourcePositiveChart_sourceJet 7,
    modularThetaSourcePositiveChart_sourceJet 8]

end


end HTGeometry
