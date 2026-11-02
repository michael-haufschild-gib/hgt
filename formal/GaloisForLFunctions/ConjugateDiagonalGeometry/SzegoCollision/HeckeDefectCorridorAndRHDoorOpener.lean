import GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.PolynomialPrefixStabilization
import GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.FiniteStratumAndCorridorClassification
import GaloisForLFunctions.SquareRootThreshold.ZetaLagFamilyVinogradovKorobovEnvelope
import GaloisForLFunctions.HTGeometry.HurwitzMaxModulusZeros
import GaloisForLFunctions.RHTower.FinitePeeling
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.ReImTopology

/-!
# Hecke-Defect Logarithmic Corridor Equivalence and the Unconditional `RiemannHypothesis` Door Opener

Final synthesis of the integer-theta Birkhoff–Szegő collision theory (`ArithmeticRealityAndBirkhoffSzego`),
the sharp `Θ(N² log N)` / `Ω(√T)` strip zero-growth law (`SharpStripZeroGrowthAndSqrtLowerBound`),
zero-separation-free polynomial-prefix stabilization (`PolynomialPrefixStabilization`), and
unit-window prime-polynomial self-absorption (`LogScaleHeckeDefect.FiniteStratumAndCorridorClassification`):

1. **Quantitative `Θ(√m)` local Hurwitz–Rouché zero capture**
   (`exists_prefix_zero_in_ball_of_xi_zero`):
   Peeling the `O(log(m + 5))` local `xi` zeros on `[burnolUnitLower m, burnolUnitUpper m]`,
   bounding the nonvanishing cofactor from below by the rectangle minimum-modulus principle, and
   selecting a concentric circle via pigeonhole proves that for every `m : ℕ`, every
   `ρ ∈ xiUnitWindowZeros (m : ℝ)`, every radius `exp(-√(m + 5)) ≤ r ≤ 1 / 48`, and every
   `N ≥ doorSqrtPrefix m` (`= doorOpenerSqrtConst * (Nat.sqrt m + 1)`), `finiteThetaAmplitude N`
   vanishes inside `Metric.closedBall ρ r`.

2. **Deterministic two-way equivalence between `Θ(√m)`-prefix Szegő positivity and the
   inverse-logarithmic zero-free corridor** (`logStage_sqrtPrefix_szego_iff_invLog_corridor`):
   Unconditional 6-way `List.TFAE` proving that a classical `A / log |γ|` zero-free corridor for
   `xi` (or `zetaZeroConfig.carrier`) holds if and only if for some `c > 0` and `m₀ : ℕ`, across all
   `m ≥ m₀` and `N ≥ doorSqrtPrefix m`, the centered integer-theta Laurent loop at stage
   `logDoorStage c m = max 6 ⌈c log(m + 5)⌉₊` admits Devinatz–Widom closed-disk sectorial Szegő
   positivity, outer polynomial Birkhoff–Szegő factorization, `L²(ℝ)` Wiener–Hopf invertibility,
   and circle-nonvanishing with `fredholmIndex < 2`.

3. **Unconditional Hecke-defect `E_γ(c₀ log T) = O(1)` door-opener implication**
   (`heckeDefect_log_bound_implies_szego_corridor_and_lindelof`,
    `heckeDefect_log_O1_implies_szego_corridor_and_lindelof`):
   Any uniform prime-polynomial or `O(1)` bound on `heckeDefect (baseTwistTest γ) (c₀ * log T)` across
   `[T, T + 1)` (`c₀ > 0`, `α ≥ 0`) unconditionally forces all 6 equivalent conditions of
   `logStage_sqrtPrefix_szego_iff_invLog_corridor` together with `ZerosApproachLine`,
   `OffLineSparse`, `LindelofCriticalLine`, and `∃ β < 1 / 2, XiZeroHalfPlaneBound β`.

4. **Master 9-way unconditional `RiemannHypothesis` door-opener equivalence**
   (`riemannHypothesis_door_opener_tfae` and `burnolUnit_subexp_sqrtPrefix_szego_of_rh`):
   `RiemannHypothesis` is unconditionally equivalent to Devinatz–Widom closed-disk Szegő positivity,
   outer polynomial Birkhoff–Szegő factorization, `L²(ℝ)` Wiener–Hopf invertibility, and
   height-uniform `fredholmIndex < 2` at both the zero-separation-free `O(m log²(m + S))` cumulative
   prefix (`doorCumulPrefix m S`) and the Burnol-bracketed unit-window prefix (`doorUnitPrefix m S`,
   which equals pure `Θ(√m)` across all `(S : ℝ) ≤ exp(√m)`, matching the `Ω(√T)` cumulative lower
   bound `firstArtifactFreePrefix_sqrt_lower_bound`).
-/

set_option autoImplicit false

open Complex Filter Topology Set Metric
open scoped BigOperators Real ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision

/-! ## §1 Canonical Burnol unit-window and cumulative door-opener schedules -/

/-- Bundled witness tuple for `centeredTheta_sqrtPrefix_stabilization`, avoiding nested
`Exists.choose` motive duplication across the five existential quantifiers. -/
structure BurnolUnitWitness where
  C_unit : ℕ
  c_good : ℝ
  y₁ : ℕ → ℝ
  y₂ : ℕ → ℝ
  Z_xi : ℕ → Finset ℂ

theorem exists_burnolUnitWitness :
    ∃ w : BurnolUnitWitness,
      4 ≤ w.C_unit ∧ 0 < w.c_good ∧ w.c_good ≤ 1 ∧
      (∀ m : ℕ,
        (-1 / 12 : ℝ) ≤ w.y₁ m ∧ w.y₁ m ≤ (m : ℝ) - 1 / 12 ∧
        (m : ℝ) + 2 ≤ w.y₂ m ∧ w.y₂ m ≤ (m : ℝ) + 3 ∧ w.y₂ m - w.y₁ m ≤ 5 ∧
        (∀ t : ℝ,
          w.c_good * Real.exp (-((m + 3 : ℕ) : ℝ)) ≤
            ‖_root_.RHTower.xi (_root_.RHTower.rectangleBoundaryPath
              (centeredWindowLowerLeft (w.y₁ m)) (centeredWindowUpperRight (w.y₂ m)) t)‖) ∧
        (∀ z : ℂ, z ∈ w.Z_xi m ↔
          (0 < z.re ∧ z.re < 1 ∧ w.y₁ m < z.im ∧ z.im < w.y₂ m) ∧ _root_.RHTower.xi z = 0) ∧
        xiUnitWindowZeros (m : ℝ) ⊆ w.Z_xi m ∧
        (∀ z ∈ w.Z_xi m, 1 - star z ∈ w.Z_xi m) ∧
        ((∑ z ∈ w.Z_xi m, (analyticOrderAt _root_.RHTower.xi z).toNat : ℕ) : ℝ) ≤
          (w.C_unit : ℝ) * Real.log ((m + 5 : ℕ) : ℝ) ∧
        (∀ N : ℕ, w.C_unit * (Nat.sqrt m + 1) ≤ N →
          thetaStripTailBound N ≤ (w.c_good / 2) * Real.exp (-((m + 3 : ℕ) : ℝ)) ∧
          (∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
            (_root_.RHTower.rectangleBoundaryPath
              (centeredWindowLowerLeft (w.y₁ m)) (centeredWindowUpperRight (w.y₂ m)) t) ≠ 0) ∧
          centeredThetaWindowDegree (w.y₁ m) (w.y₂ m) N =
            ∑ z ∈ w.Z_xi m, (analyticOrderAt _root_.RHTower.xi z).toNat) ∧
        (∀ (n S_max : ℕ), 6 ≤ n → n ≤ S_max →
          (S_max : ℝ) ≤ 6 * Real.exp (Real.sqrt ((m + 5 : ℕ) : ℝ)) +
            2 * ((∑ z ∈ w.Z_xi m, (analyticOrderAt _root_.RHTower.xi z).toNat : ℕ) : ℝ) ^ 2 →
          (∀ z ∈ w.Z_xi m, ∀ z' ∈ w.Z_xi m,
            1 / (8 * (S_max : ℝ) ^ 3) ≤ |zhukovskyEllipseForm n (z - z') - 1|) →
          ∀ N : ℕ, w.C_unit * (Nat.sqrt m + 1) ≤ N →
            (∀ u : HTGeometry.UnitCircle,
              centeredThetaLaurentLoop (w.y₁ m) (w.y₂ m) n N u ≠ 0) ∧
            HTGeometry.fredholmIndex (centeredThetaCollisionOperator (w.y₁ m) (w.y₂ m) n N) =
              2 * ∑ z ∈ w.Z_xi m, ∑ z' ∈ w.Z_xi m,
                ((analyticOrderAt _root_.RHTower.xi z).toNat : ℤ) *
                  ((analyticOrderAt _root_.RHTower.xi z').toNat : ℤ) *
                  (if zhukovskyEllipseForm n (z - z') < 1 then 1 else 0)) ∧
        (∀ S : ℕ, (S : ℝ) ≤ Real.exp (Real.sqrt (m : ℝ)) →
          ∃ n_star ∈ Finset.Icc (max S 6)
              (max S 6 + 2 * (∑ z ∈ w.Z_xi m, (analyticOrderAt _root_.RHTower.xi z).toNat) ^ 2),
            ∀ N : ℕ, w.C_unit * (Nat.sqrt m + 1) ≤ N →
              (∀ u : HTGeometry.UnitCircle,
                centeredThetaLaurentLoop (w.y₁ m) (w.y₂ m) n_star N u ≠ 0) ∧
              HTGeometry.fredholmIndex
                  (centeredThetaCollisionOperator (w.y₁ m) (w.y₂ m) n_star N) =
                2 * ∑ z ∈ w.Z_xi m, ∑ z' ∈ w.Z_xi m,
                  ((analyticOrderAt _root_.RHTower.xi z).toNat : ℤ) *
                    ((analyticOrderAt _root_.RHTower.xi z').toNat : ℤ) *
                    (if zhukovskyEllipseForm n_star (z - z') < 1 then 1 else 0)) ∧
        (∀ S : ℕ,
          ∃ n_star ∈ Finset.Icc (max S 6)
              (max S 6 + 2 * (∑ z ∈ w.Z_xi m, (analyticOrderAt _root_.RHTower.xi z).toNat) ^ 2),
            ∀ N : ℕ,
              w.C_unit * (Nat.sqrt m + 1 +
                (Nat.ceil (Real.log ((m + 5 : ℕ) : ℝ)) + 1) *
                  (Nat.ceil (Real.sqrt (Real.log ((S + 6 : ℕ) : ℝ))) + 1)) ≤ N →
              (∀ u : HTGeometry.UnitCircle,
                centeredThetaLaurentLoop (w.y₁ m) (w.y₂ m) n_star N u ≠ 0) ∧
              HTGeometry.fredholmIndex
                  (centeredThetaCollisionOperator (w.y₁ m) (w.y₂ m) n_star N) =
                2 * ∑ z ∈ w.Z_xi m, ∑ z' ∈ w.Z_xi m,
                  ((analyticOrderAt _root_.RHTower.xi z).toNat : ℤ) *
                    ((analyticOrderAt _root_.RHTower.xi z').toNat : ℤ) *
                    (if zhukovskyEllipseForm n_star (z - z') < 1 then 1 else 0))) := by
  obtain ⟨C_unit, c_good, y₁, y₂, Z_xi, h1, h2, h3, hm⟩ := centeredTheta_sqrtPrefix_stabilization
  exact ⟨⟨C_unit, c_good, y₁, y₂, Z_xi⟩, h1, h2, h3, hm⟩

/-- Canonical Burnol unit-window witness chosen once from `exists_burnolUnitWitness`. -/
def burnolWitness : BurnolUnitWitness :=
  exists_burnolUnitWitness.choose

/-- Canonical Burnol unit-window prefix constant `C_unit ≥ 4` extracted from
`centeredTheta_sqrtPrefix_stabilization`. -/
def burnolPrefixConst : ℕ :=
  burnolWitness.C_unit

/-- Canonical Burnol good-height boundary lower-bound constant `0 < c_good ≤ 1`. -/
def burnolGoodLowerConst : ℝ :=
  burnolWitness.c_good

/-- Canonical lower Burnol good height `y₁(m) ∈ [-1/12, m - 1/12]` bracketing `[m, m + 1]`. -/
def burnolUnitLower : ℕ → ℝ :=
  burnolWitness.y₁

/-- Canonical upper Burnol good height `y₂(m) ∈ [m + 2, m + 3]` bracketing `[m, m + 1]`. -/
def burnolUnitUpper : ℕ → ℝ :=
  burnolWitness.y₂

/-- Enclosed `xi` zero finset on `(-1/2, 3/2) × (burnolUnitLower m, burnolUnitUpper m)`. -/
def burnolUnitXiZeros : ℕ → Finset ℂ :=
  burnolWitness.Z_xi

theorem four_le_burnolPrefixConst : 4 ≤ burnolPrefixConst := by
  dsimp only [burnolPrefixConst, burnolWitness]
  exact exists_burnolUnitWitness.choose_spec.1

theorem burnolGoodLowerConst_pos : 0 < burnolGoodLowerConst := by
  dsimp only [burnolGoodLowerConst, burnolWitness]
  exact exists_burnolUnitWitness.choose_spec.2.1

theorem burnolGoodLowerConst_le_one : burnolGoodLowerConst ≤ 1 := by
  dsimp only [burnolGoodLowerConst, burnolWitness]
  exact exists_burnolUnitWitness.choose_spec.2.2.1

theorem burnolUnit_coords (m : ℕ) :
    (-1 / 12 : ℝ) ≤ burnolUnitLower m ∧ burnolUnitLower m ≤ (m : ℝ) - 1 / 12 ∧
    (m : ℝ) + 2 ≤ burnolUnitUpper m ∧ burnolUnitUpper m ≤ (m : ℝ) + 3 ∧
    burnolUnitUpper m - burnolUnitLower m ≤ 5 := by
  dsimp only [burnolUnitLower, burnolUnitUpper, burnolWitness]
  have h := exists_burnolUnitWitness.choose_spec.2.2.2 m
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem burnolUnit_xi_bdry_ge (m : ℕ) :
    ∀ t : ℝ,
      burnolGoodLowerConst * Real.exp (-((m + 3 : ℕ) : ℝ)) ≤
        ‖_root_.RHTower.xi (_root_.RHTower.rectangleBoundaryPath
          (centeredWindowLowerLeft (burnolUnitLower m))
          (centeredWindowUpperRight (burnolUnitUpper m)) t)‖ := by
  dsimp only [burnolGoodLowerConst, burnolUnitLower, burnolUnitUpper, burnolWitness]
  exact (exists_burnolUnitWitness.choose_spec.2.2.2 m).2.2.2.2.2.1

theorem mem_burnolUnitXiZeros_iff (m : ℕ) :
    ∀ z : ℂ, z ∈ burnolUnitXiZeros m ↔
      (0 < z.re ∧ z.re < 1 ∧ burnolUnitLower m < z.im ∧ z.im < burnolUnitUpper m) ∧
        _root_.RHTower.xi z = 0 := by
  dsimp only [burnolUnitXiZeros, burnolUnitLower, burnolUnitUpper, burnolWitness]
  exact (exists_burnolUnitWitness.choose_spec.2.2.2 m).2.2.2.2.2.2.1

theorem xiUnitWindowZeros_subset_burnolUnitXiZeros (m : ℕ) :
    xiUnitWindowZeros (m : ℝ) ⊆ burnolUnitXiZeros m := by
  dsimp only [burnolUnitXiZeros, burnolWitness]
  exact (exists_burnolUnitWitness.choose_spec.2.2.2 m).2.2.2.2.2.2.2.1

theorem one_sub_star_mem_burnolUnitXiZeros (m : ℕ) :
    ∀ z ∈ burnolUnitXiZeros m, 1 - star z ∈ burnolUnitXiZeros m := by
  dsimp only [burnolUnitXiZeros, burnolWitness]
  exact (exists_burnolUnitWitness.choose_spec.2.2.2 m).2.2.2.2.2.2.2.2.1

theorem burnolUnitXiZeros_totalOrder_le (m : ℕ) :
    ((∑ z ∈ burnolUnitXiZeros m, (analyticOrderAt _root_.RHTower.xi z).toNat : ℕ) : ℝ) ≤
      (burnolPrefixConst : ℝ) * Real.log ((m + 5 : ℕ) : ℝ) := by
  dsimp only [burnolUnitXiZeros, burnolPrefixConst, burnolWitness]
  exact (exists_burnolUnitWitness.choose_spec.2.2.2 m).2.2.2.2.2.2.2.2.2.1

theorem burnolUnit_bdry_regular (m : ℕ) {N : ℕ}
    (hN : burnolPrefixConst * (Nat.sqrt m + 1) ≤ N) :
    ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft (burnolUnitLower m))
        (centeredWindowUpperRight (burnolUnitUpper m)) t) ≠ 0 := by
  dsimp only [burnolPrefixConst, burnolUnitLower, burnolUnitUpper, burnolWitness] at hN ⊢
  exact ((exists_burnolUnitWitness.choose_spec.2.2.2 m).2.2.2.2.2.2.2.2.2.2.1 N hN).2.1

theorem burnolUnit_singleStage_stabilization (m : ℕ) :
    ∀ (n S_max : ℕ), 6 ≤ n → n ≤ S_max →
      (S_max : ℝ) ≤ 6 * Real.exp (Real.sqrt ((m + 5 : ℕ) : ℝ)) +
        2 * ((∑ z ∈ burnolUnitXiZeros m, (analyticOrderAt _root_.RHTower.xi z).toNat : ℕ) : ℝ) ^ 2 →
      (∀ z ∈ burnolUnitXiZeros m, ∀ z' ∈ burnolUnitXiZeros m,
        1 / (8 * (S_max : ℝ) ^ 3) ≤ |zhukovskyEllipseForm n (z - z') - 1|) →
      ∀ N : ℕ, burnolPrefixConst * (Nat.sqrt m + 1) ≤ N →
        (∀ u : HTGeometry.UnitCircle,
          centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m) n N u ≠ 0) ∧
        HTGeometry.fredholmIndex
            (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m) n N) =
          2 * ∑ z ∈ burnolUnitXiZeros m, ∑ z' ∈ burnolUnitXiZeros m,
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℤ) *
              ((analyticOrderAt _root_.RHTower.xi z').toNat : ℤ) *
              (if zhukovskyEllipseForm n (z - z') < 1 then 1 else 0) := by
  dsimp only [burnolPrefixConst, burnolUnitLower, burnolUnitUpper, burnolUnitXiZeros, burnolWitness]
  exact (exists_burnolUnitWitness.choose_spec.2.2.2 m).2.2.2.2.2.2.2.2.2.2.2.1

theorem burnolUnit_subexp_stabilization (m : ℕ) :
    ∀ S : ℕ, (S : ℝ) ≤ Real.exp (Real.sqrt (m : ℝ)) →
      ∃ n_star ∈ Finset.Icc (max S 6)
          (max S 6 + 2 * (∑ z ∈ burnolUnitXiZeros m, (analyticOrderAt _root_.RHTower.xi z).toNat) ^ 2),
        ∀ N : ℕ, burnolPrefixConst * (Nat.sqrt m + 1) ≤ N →
          (∀ u : HTGeometry.UnitCircle,
            centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m) n_star N u ≠ 0) ∧
          HTGeometry.fredholmIndex
              (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m) n_star N) =
            2 * ∑ z ∈ burnolUnitXiZeros m, ∑ z' ∈ burnolUnitXiZeros m,
              ((analyticOrderAt _root_.RHTower.xi z).toNat : ℤ) *
                ((analyticOrderAt _root_.RHTower.xi z').toNat : ℤ) *
                (if zhukovskyEllipseForm n_star (z - z') < 1 then 1 else 0) := by
  dsimp only [burnolPrefixConst, burnolUnitLower, burnolUnitUpper, burnolUnitXiZeros, burnolWitness]
  exact (exists_burnolUnitWitness.choose_spec.2.2.2 m).2.2.2.2.2.2.2.2.2.2.2.2.1

theorem burnolUnit_unrestricted_stabilization (m S : ℕ) :
    ∃ n_star ∈ Finset.Icc (max S 6)
        (max S 6 + 2 * (∑ z ∈ burnolUnitXiZeros m, (analyticOrderAt _root_.RHTower.xi z).toNat) ^ 2),
      ∀ N : ℕ,
        burnolPrefixConst * (Nat.sqrt m + 1 +
          (Nat.ceil (Real.log ((m + 5 : ℕ) : ℝ)) + 1) *
            (Nat.ceil (Real.sqrt (Real.log ((S + 6 : ℕ) : ℝ))) + 1)) ≤ N →
        (∀ u : HTGeometry.UnitCircle,
          centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m) n_star N u ≠ 0) ∧
        HTGeometry.fredholmIndex
            (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m) n_star N) =
          2 * ∑ z ∈ burnolUnitXiZeros m, ∑ z' ∈ burnolUnitXiZeros m,
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℤ) *
              ((analyticOrderAt _root_.RHTower.xi z').toNat : ℤ) *
              (if zhukovskyEllipseForm n_star (z - z') < 1 then 1 else 0) := by
  dsimp only [burnolPrefixConst, burnolUnitLower, burnolUnitUpper, burnolUnitXiZeros, burnolWitness]
  exact (exists_burnolUnitWitness.choose_spec.2.2.2 m).2.2.2.2.2.2.2.2.2.2.2.2.2 S

theorem burnolUnitLower_lt_upper (m : ℕ) : burnolUnitLower m < burnolUnitUpper m := by
  have h := burnolUnit_coords m
  linarith [h.2.1, h.2.2.1]

theorem burnolUnitLower_le_upper (m : ℕ) : burnolUnitLower m ≤ burnolUnitUpper m :=
  (burnolUnitLower_lt_upper m).le

theorem sub_three_le_burnolUnitLower (m : ℕ) : (m : ℝ) - 3 ≤ burnolUnitLower m := by
  have h := burnolUnit_coords m
  linarith [h.2.2.1, h.2.2.2.2]

/-- Canonical unrestricted-`S` Burnol unit-window prefix schedule:
`burnolPrefixConst * (√m + 1 + (⌈log(m + 5)⌉₊ + 1) * (⌈√(log(S + 6))⌉₊ + 1))`. -/
def doorUnitPrefix (m S : ℕ) : ℕ :=
  burnolPrefixConst *
    (Nat.sqrt m + 1 +
      (Nat.ceil (Real.log ((m + 5 : ℕ) : ℝ)) + 1) *
        (Nat.ceil (Real.sqrt (Real.log ((S + 6 : ℕ) : ℝ))) + 1))

/-- Canonical ellipse-avoiding stage `doorUnitStage m S ∈ [max S 6, max S 6 + 2 d_m²]` on the `m`-th
Burnol unit window. -/
def doorUnitStage (m S : ℕ) : ℕ :=
  (burnolUnit_unrestricted_stabilization m S).choose

theorem doorUnitStage_spec (m S : ℕ) :
    doorUnitStage m S ∈ Finset.Icc (max S 6)
      (max S 6 + 2 * (∑ w ∈ burnolUnitXiZeros m, (analyticOrderAt _root_.RHTower.xi w).toNat) ^ 2) ∧
    ∀ N : ℕ, doorUnitPrefix m S ≤ N →
      (∀ u : HTGeometry.UnitCircle,
        centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
          (doorUnitStage m S) N u ≠ 0) ∧
      HTGeometry.fredholmIndex
        (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m)
          (doorUnitStage m S) N) =
        2 * ∑ z ∈ burnolUnitXiZeros m, ∑ w ∈ burnolUnitXiZeros m,
          ((analyticOrderAt _root_.RHTower.xi z).toNat : ℤ) *
            ((analyticOrderAt _root_.RHTower.xi w).toNat : ℤ) *
            (if zhukovskyEllipseForm (doorUnitStage m S) (z - w) < 1 then 1 else 0) := by
  dsimp only [doorUnitStage, doorUnitPrefix]
  exact (burnolUnit_unrestricted_stabilization m S).choose_spec

/-- Canonical cumulative `O(m log²(m + S))` prefix constant `C_cum ≥ 1` extracted from
`integerThetaCollisionOperator_polynomial_stabilization`. -/
def doorCumulConst : ℕ :=
  integerThetaCollisionOperator_polynomial_stabilization.choose

theorem one_le_doorCumulConst : 1 ≤ doorCumulConst :=
  integerThetaCollisionOperator_polynomial_stabilization.choose_spec.1

/-- Canonical cumulative zero-separation-free prefix schedule
`doorCumulConst * (m + 1) * (⌈log(m + S + 4)⌉₊ + 1)²`. -/
def doorCumulPrefix (m S : ℕ) : ℕ :=
  doorCumulConst * (m + 1) * (Nat.ceil (Real.log ((m + S + 4 : ℕ) : ℝ)) + 1) ^ 2

/-- Canonical Burnol good height `doorCumulHeight m S ∈ [m, m + 1]` for the cumulative operator. -/
def doorCumulHeight (m S : ℕ) : ℝ :=
  (integerThetaCollisionOperator_polynomial_stabilization.choose_spec.2 m S).choose

/-- Canonical ellipse-avoiding stage `doorCumulStage m S` for the cumulative operator. -/
def doorCumulStage (m S : ℕ) : ℕ :=
  (integerThetaCollisionOperator_polynomial_stabilization.choose_spec.2 m S).choose_spec.choose

/-- Shifted cumulative window height `T_* + 1 / (2 * zhukovskyStage n_*)`. -/
def doorCumulWindowHeight (m S : ℕ) : ℝ :=
  doorCumulHeight m S + 1 / (2 * (zhukovskyStage (doorCumulStage m S) : ℝ))

theorem doorCumul_spec (m S : ℕ) :
    (m : ℝ) ≤ doorCumulHeight m S ∧ doorCumulHeight m S ≤ (m : ℝ) + 1 ∧
    doorCumulStage m S ∈ Finset.Icc (max S 6)
      (max S 6 + 2 * (_root_.RHTower.xiStripWindowTotalOrder (doorCumulHeight m S)) ^ 2) ∧
    ∀ N : ℕ,
      doorCumulConst * (m + 1) * (Nat.ceil (Real.log ((m + S + 4 : ℕ) : ℝ)) + 1) ^ 2 ≤ N →
      (∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
        (_root_.RHTower.rectangleBoundaryPath
          (thetaWindowLowerLeft (doorCumulStage m S))
          (thetaWindowUpperRight (doorCumulWindowHeight m S) (doorCumulStage m S)) t) ≠ 0) ∧
      integerThetaWindowDegree (doorCumulWindowHeight m S) (doorCumulStage m S) N =
        _root_.RHTower.xiStripWindowTotalOrder (doorCumulHeight m S) ∧
      (∀ u : HTGeometry.UnitCircle,
        integerThetaLaurentLoop (doorCumulWindowHeight m S) (doorCumulStage m S) N u ≠ 0) ∧
      (∀ z ∈ prefixEnclosedZeros (doorCumulWindowHeight m S) (doorCumulStage m S) N,
        ∀ w ∈ prefixEnclosedZeros (doorCumulWindowHeight m S) (doorCumulStage m S) N,
          zhukovskyEllipseForm (doorCumulStage m S) (z - w) ≠ 1) ∧
      HTGeometry.fredholmIndex
          (integerThetaCollisionOperator (doorCumulWindowHeight m S) (doorCumulStage m S) N) =
        2 * ∑ z ∈ (_root_.RHTower.stripZeros_finite (doorCumulHeight m S)).toFinset,
          ∑ w ∈ (_root_.RHTower.stripZeros_finite (doorCumulHeight m S)).toFinset,
            ((analyticOrderAt _root_.RHTower.xi z).toNat : ℤ) *
              ((analyticOrderAt _root_.RHTower.xi w).toNat : ℤ) *
              (if zhukovskyEllipseForm (doorCumulStage m S) (z - w) < 1 then 1 else 0) ∧
      (thetaWindowScale (doorCumulHeight m S) ≤ S →
        HTGeometry.fredholmIndex
          (integerThetaCollisionOperator (doorCumulWindowHeight m S) (doorCumulStage m S) N) =
          (_root_.RHTower.xiHorizontalCollisionCharge (doorCumulHeight m S) : ℤ)) :=
  (integerThetaCollisionOperator_polynomial_stabilization.choose_spec.2 m S).choose_spec.choose_spec

/-- Deterministic logarithmic stage schedule `max 6 ⌈c * log(m + 5)⌉₊` for the `A / log |γ|`
corridor equivalence. -/
def logDoorStage (c : ℝ) (m : ℕ) : ℕ :=
  max 6 (Nat.ceil (c * Real.log ((m + 5 : ℕ) : ℝ)))

theorem six_le_logDoorStage (c : ℝ) (m : ℕ) : 6 ≤ logDoorStage c m :=
  le_max_left 6 _


/-! ## §2 Quantitative `Θ(√m)` local Hurwitz–Rouché zero capture -/

/-- Every point on the four edges of `[z₁.re, z₂.re] × [z₁.im, z₂.im]` lies in the range of
`rectangleBoundaryPath z₁ z₂`. -/
private lemma exists_boundaryPath_eq_of_edges {z₁ z₂ z : ℂ}
    (hre : z₁.re ≤ z₂.re) (_ : z₁.im ≤ z₂.im)
    (hx : z₁.re ≤ z.re ∧ z.re ≤ z₂.re) (hy : z₁.im ≤ z.im ∧ z.im ≤ z₂.im)
    (hedge : z.re = z₁.re ∨ z.re = z₂.re ∨ z.im = z₁.im ∨ z.im = z₂.im) :
    ∃ t : ℝ, _root_.RHTower.rectangleBoundaryPath z₁ z₂ t = z := by
  by_cases hy1 : z.im = z₁.im
  · rcases eq_or_lt_of_le hre with hxeq | hxlt
    · refine ⟨0, ?_⟩
      rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_zero, _root_.RHTower.rectangleEdgePath_zero]
      exact Complex.ext (by linarith [hx.1, hx.2]) hy1.symm
    · set τ : ℝ := (z.re - z₁.re) / (4 * (z₂.re - z₁.re))
      have hdx : 0 < z₂.re - z₁.re := sub_pos.mpr hxlt
      have hτ_nn : 0 ≤ τ := div_nonneg (by linarith [hx.1]) (by positivity)
      have hτ_le : τ ≤ 1 / 4 := by
        dsimp only [τ]
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [hx.2]
      refine ⟨τ, ?_⟩
      rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨hτ_nn, by linarith⟩,
        _root_.RHTower.rectangleEdgePath, if_pos hτ_le]
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, mul_zero]
        dsimp only [τ]; field_simp [hdx.ne']; ring
      · simp [hy1]
  · have hy1_lt : z₁.im < z.im := lt_of_le_of_ne hy.1 (Ne.symm hy1)
    have hdy : 0 < z₂.im - z₁.im := by linarith [hy.2]
    by_cases hx2 : z.re = z₂.re
    · set τ : ℝ := 1 / 4 + (z.im - z₁.im) / (4 * (z₂.im - z₁.im))
      have hτ_gt : 1 / 4 < τ := by
        dsimp only [τ]
        linarith [div_pos (sub_pos.mpr hy1_lt) (by positivity : 0 < 4 * (z₂.im - z₁.im))]
      have hτ_le : τ ≤ 1 / 2 := by
        dsimp only [τ]
        have h1 : (z.im - z₁.im) / (4 * (z₂.im - z₁.im)) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [hy.2]
        linarith
      refine ⟨τ, ?_⟩
      rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩,
        _root_.RHTower.rectangleEdgePath, if_neg (not_le.mpr hτ_gt), if_pos hτ_le]
      apply Complex.ext
      · simp [hx2]
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
          Complex.ofReal_re, Complex.I_im, mul_one, zero_add]
        dsimp only [τ]; field_simp [hdy.ne']; ring
    · have hx2_lt : z.re < z₂.re := lt_of_le_of_ne hx.2 hx2
      have hdx : 0 < z₂.re - z₁.re := by linarith [hx.1]
      by_cases hy2 : z.im = z₂.im
      · set τ : ℝ := 1 / 2 + (z₂.re - z.re) / (4 * (z₂.re - z₁.re))
        have hτ_gt : 1 / 2 < τ := by
          dsimp only [τ]
          linarith [div_pos (sub_pos.mpr hx2_lt) (by positivity : 0 < 4 * (z₂.re - z₁.re))]
        have hτ_le : τ ≤ 3 / 4 := by
          dsimp only [τ]
          have h1 : (z₂.re - z.re) / (4 * (z₂.re - z₁.re)) ≤ 1 / 4 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [hx.1]
          linarith
        refine ⟨τ, ?_⟩
        rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩,
          _root_.RHTower.rectangleEdgePath, if_neg (by linarith), if_neg (not_le.mpr hτ_gt),
          if_pos hτ_le]
        apply Complex.ext
        · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            Complex.ofReal_im, Complex.I_im, mul_zero]
          dsimp only [τ]; field_simp [hdx.ne']; ring
        · simp [hy2]
      · have hy2_lt : z.im < z₂.im := lt_of_le_of_ne hy.2 hy2
        have hx1 : z.re = z₁.re := by
          rcases hedge with h | h | h | h
          · exact h
          · exact absurd h hx2
          · exact absurd h hy1
          · exact absurd h hy2
        set τ : ℝ := 3 / 4 + (z₂.im - z.im) / (4 * (z₂.im - z₁.im))
        have hτ_gt : 3 / 4 < τ := by
          dsimp only [τ]
          linarith [div_pos (sub_pos.mpr hy2_lt) (by positivity : 0 < 4 * (z₂.im - z₁.im))]
        have hτ_lt : τ < 1 := by
          dsimp only [τ]
          have h1 : (z₂.im - z.im) / (4 * (z₂.im - z₁.im)) < 1 / 4 := by
            rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith [hy1_lt]
          linarith
        refine ⟨τ, ?_⟩
        rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨by linarith, hτ_lt⟩,
          _root_.RHTower.rectangleEdgePath, if_neg (by linarith), if_neg (by linarith),
          if_neg (not_le.mpr hτ_gt)]
        apply Complex.ext
        · simp [hx1]
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
            Complex.ofReal_re, Complex.I_im, mul_one, zero_add]
          dsimp only [τ]; field_simp [hdy.ne']; ring

/-- Elementary bound `Real.log x ≤ 2 * Real.sqrt x` for `x > 0`. -/
private lemma log_le_two_sqrt_of_pos {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have hrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hl : Real.log x = 2 * Real.log (Real.sqrt x) := by
    calc Real.log x = Real.log (Real.sqrt x ^ 2) := congrArg Real.log (Real.sq_sqrt hx.le).symm
      _ = 2 * Real.log (Real.sqrt x) := by rw [Real.log_pow, Nat.cast_ofNat]
  linarith [Real.log_le_sub_one_of_pos hrt_pos]

/-- Elementary bound `Real.log ((m + 5 : ℕ) : ℝ) ≤ 4 * Real.sqrt ((m + 5 : ℕ) : ℝ)`. -/
private lemma log_le_four_sqrt_add_five (m : ℕ) :
    Real.log ((m + 5 : ℕ) : ℝ) ≤ 4 * Real.sqrt ((m + 5 : ℕ) : ℝ) := by
  have hx_pos : (0 : ℝ) < ((m + 5 : ℕ) : ℝ) := by exact_mod_cast (show 0 < m + 5 by omega)
  have hrt_nn : 0 ≤ Real.sqrt ((m + 5 : ℕ) : ℝ) := Real.sqrt_nonneg _
  linarith [log_le_two_sqrt_of_pos hx_pos]

/-- Concentric-radius pigeonhole lemma: given a finite point set `Z : Finset ℂ` with `Z.card ≤ d`
and `δ > 0`, among the `d + 1` concentric radii `(2 * k - 1) * δ` (`k ∈ [1, d + 1]`) around `ρ`,
at least one avoids every `‖w - ρ‖` (`w ∈ Z`) by at least `δ`. -/
private lemma exists_concentric_sphere_gap (Z : Finset ℂ) (d : ℕ) (hcard : Z.card ≤ d)
    (ρ : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k ∈ Finset.Icc 1 (d + 1),
      ∀ z ∈ Metric.sphere ρ (((2 * k - 1 : ℕ) : ℝ) * δ), ∀ w ∈ Z, δ ≤ ‖z - w‖ := by
  classical
  let rad : ℕ → ℝ := fun k => ((2 * k - 1 : ℕ) : ℝ) * δ
  let bad : Finset ℕ := (Finset.Icc 1 (d + 1)).filter fun k =>
    ∃ w ∈ Z, |‖w - ρ‖ - rad k| < δ
  have hbad_sub : bad ⊆ Z.biUnion (fun w =>
      (Finset.Icc 1 (d + 1)).filter fun k => |‖w - ρ‖ - rad k| < δ) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    obtain ⟨hk_Icc, w, hwZ, hlt⟩ := hk
    exact Finset.mem_biUnion.mpr ⟨w, hwZ, Finset.mem_filter.mpr ⟨hk_Icc, hlt⟩⟩
  have hfib_le1 : ∀ w ∈ Z,
      ((Finset.Icc 1 (d + 1)).filter fun k => |‖w - ρ‖ - rad k| < δ).card ≤ 1 := by
    intro w _
    refine Finset.card_le_one.mpr fun k₁ hk₁ k₂ hk₂ => ?_
    rw [Finset.mem_filter, Finset.mem_Icc] at hk₁ hk₂
    by_contra hne
    have hgap_nat : 2 ≤ (if k₁ ≤ k₂ then 2 * k₂ - 1 - (2 * k₁ - 1) else 2 * k₁ - 1 - (2 * k₂ - 1)) := by
      split_ifs <;> omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hrad_diff : 2 * δ ≤ rad k₂ - rad k₁ := by
        dsimp only [rad]
        have h2 : (2 : ℝ) ≤ ((2 * k₂ - 1 : ℕ) : ℝ) - ((2 * k₁ - 1 : ℕ) : ℝ) := by
          have hn : 2 * k₁ - 1 + 2 ≤ 2 * k₂ - 1 := by omega
          have hc : ((2 * k₁ - 1 + 2 : ℕ) : ℝ) ≤ ((2 * k₂ - 1 : ℕ) : ℝ) := by exact_mod_cast hn
          push_cast at hc; linarith
        nlinarith only [h2, hδ]
      have habs1 := abs_lt.mp hk₁.2
      have habs2 := abs_lt.mp hk₂.2
      linarith
    · have hrad_diff : 2 * δ ≤ rad k₁ - rad k₂ := by
        dsimp only [rad]
        have h2 : (2 : ℝ) ≤ ((2 * k₁ - 1 : ℕ) : ℝ) - ((2 * k₂ - 1 : ℕ) : ℝ) := by
          have hn : 2 * k₂ - 1 + 2 ≤ 2 * k₁ - 1 := by omega
          have hc : ((2 * k₂ - 1 + 2 : ℕ) : ℝ) ≤ ((2 * k₁ - 1 : ℕ) : ℝ) := by exact_mod_cast hn
          push_cast at hc; linarith
        nlinarith only [h2, hδ]
      have habs1 := abs_lt.mp hk₁.2
      have habs2 := abs_lt.mp hk₂.2
      linarith
  have hbad_lt : bad.card < (Finset.Icc 1 (d + 1)).card := by
    have hcard_Icc : (Finset.Icc 1 (d + 1)).card = d + 1 := by simp
    have hcard_bad : bad.card ≤ d := by
      calc bad.card
          ≤ (Z.biUnion (fun w =>
              (Finset.Icc 1 (d + 1)).filter fun k => |‖w - ρ‖ - rad k| < δ)).card :=
            Finset.card_le_card hbad_sub
        _ ≤ ∑ w ∈ Z, ((Finset.Icc 1 (d + 1)).filter fun k => |‖w - ρ‖ - rad k| < δ).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _w ∈ Z, 1 := Finset.sum_le_sum hfib_le1
        _ = Z.card := by simp
        _ ≤ d := hcard
    omega
  obtain ⟨k, hk_Icc, hk_not_bad⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad_lt
  refine ⟨k, hk_Icc, fun z hz w hw => ?_⟩
  have hge : δ ≤ |‖w - ρ‖ - rad k| := by
    by_contra hlt
    exact hk_not_bad (Finset.mem_filter.mpr ⟨hk_Icc, w, hw, not_le.mp hlt⟩)
  have hzr : ‖z - ρ‖ = rad k := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
  have hrev : |‖w - ρ‖ - ‖z - ρ‖| ≤ ‖(w - ρ) - (z - ρ)‖ := abs_norm_sub_norm_le (w - ρ) (z - ρ)
  rw [hzr, show (w - ρ) - (z - ρ) = w - z by ring, norm_sub_rev w z] at hrev
  exact hge.trans hrev

/-- Quantitative local Hurwitz–Rouché zero capture theorem (existential constant form, unpacked
immediately into `doorOpenerSqrtConst` and `doorSqrtPrefix`). -/
private theorem exists_doorOpenerSqrtConst :
    ∃ K_door : ℕ, burnolPrefixConst ≤ K_door ∧
      ∀ (m : ℕ) (ρ : ℂ), ρ ∈ xiUnitWindowZeros (m : ℝ) →
        ∀ r : ℝ, Real.exp (-Real.sqrt ((m + 5 : ℕ) : ℝ)) ≤ r → r ≤ 1 / 48 →
          ∀ N : ℕ, K_door * (Nat.sqrt m + 1) ≤ N →
            ∃ z_N ∈ Metric.closedBall ρ r, _root_.RHTower.finiteThetaAmplitude N z_N = 0 := by
  set C_u : ℕ := burnolPrefixConst
  set c_good : ℝ := burnolGoodLowerConst
  have hCu4 : 4 ≤ C_u := four_le_burnolPrefixConst
  have hc_pos : 0 < c_good := burnolGoodLowerConst_pos
  let C_env : ℝ :=
    _root_.RHTower.thetaCuspIntegerTailConstant * _root_.RHTower.thetaAmplitudeEnvelope 2 + 1
  have hC_env1 : 1 ≤ C_env := by
    dsimp only [C_env]
    have hnn := mul_nonneg _root_.RHTower.thetaCuspIntegerTailConstant_nonneg
      (_root_.RHTower.thetaAmplitudeEnvelope_nonneg 2)
    linarith
  have hC_env_tail : ∀ N : ℕ,
      thetaStripTailBound N ≤ C_env * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) := fun N => by
    unfold thetaStripTailBound
    exact mul_le_mul_of_nonneg_right (by dsimp only [C_env]; linarith) (Real.exp_pos _).le
  let M_fac : ℝ := 16 * (4 * (C_u : ℝ) + 1)
  have hM_fac1 : 1 ≤ M_fac := by
    dsimp only [M_fac]
    have : (0 : ℝ) ≤ (C_u : ℝ) := Nat.cast_nonneg _
    linarith
  let B_door : ℝ :=
    |Real.log (4 * C_env / c_good)| + 1 +
      4 * (C_u : ℝ) * (Real.log M_fac + 2) + 2
  have hB_door2 : 2 ≤ B_door := by
    dsimp only [B_door]
    have h1 : 0 ≤ 4 * (C_u : ℝ) * (Real.log M_fac + 2) :=
      mul_nonneg (by positivity) (by linarith [Real.log_nonneg hM_fac1])
    linarith [abs_nonneg (Real.log (4 * C_env / c_good))]
  let K_door : ℕ := max C_u (Nat.ceil (Real.sqrt (5 * B_door)) + 1)
  have hKd_ge : C_u ≤ K_door := le_max_left _ _
  have hKd_sq : 5 * B_door ≤ (K_door : ℝ) ^ 2 := by
    have hrt : Real.sqrt (5 * B_door) ≤ (K_door : ℝ) := by
      calc Real.sqrt (5 * B_door)
          ≤ ((Nat.ceil (Real.sqrt (5 * B_door)) + 1 : ℕ) : ℝ) := by
            push_cast; linarith [Nat.le_ceil (Real.sqrt (5 * B_door))]
        _ ≤ (K_door : ℝ) := by exact_mod_cast (le_max_right C_u _)
    calc 5 * B_door = (Real.sqrt (5 * B_door)) ^ 2 := (Real.sq_sqrt (by linarith)).symm
      _ ≤ (K_door : ℝ) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hrt 2
  have hB_bound :
      |Real.log (4 * C_env / c_good)| + 1 +
        4 * (C_u : ℝ) * (Real.log M_fac + 2) + 1 ≤ B_door := by
    dsimp only [B_door]; linarith
  have hM_fac_def : 16 * (4 * (C_u : ℝ) + 1) = M_fac := rfl
  generalize K_door = K_d at hKd_ge hKd_sq
  generalize B_door = B_d at hB_door2 hKd_sq hB_bound
  generalize M_fac = M_f at hM_fac1 hM_fac_def hB_bound
  generalize C_env = C_e at hC_env1 hC_env_tail hB_bound
  clear K_door B_door M_fac C_env
  have hCe_pos : 0 < C_e := by linarith only [hC_env1]
  have hMf_pos : 0 < M_f := by linarith only [hM_fac1]
  have hBd_pos : 0 < B_d := by linarith only [hB_door2]
  have hKd_pos : 0 < (K_d : ℝ) := by
    have : 0 < K_d := lt_of_lt_of_le (by omega : 0 < C_u) hKd_ge
    exact_mod_cast this
  refine ⟨K_d, hKd_ge, fun m ρ hρ_unit r hr_lo hr_hi N hN => ?_⟩
  obtain ⟨hy₁_lo, hy₁_hi, hy₂_lo, hy₂_hi, hspan5⟩ := burnolUnit_coords m
  have hbdry_m := burnolUnit_xi_bdry_ge m
  have hZ_iff := mem_burnolUnitXiZeros_iff m
  have hsub_unit := xiUnitWindowZeros_subset_burnolUnitXiZeros m
  have hd_Cu := burnolUnitXiZeros_totalOrder_le m
  set y₁ := burnolUnitLower m
  set y₂ := burnolUnitUpper m
  set Z_m := burnolUnitXiZeros m
  set d := ∑ w ∈ Z_m, (analyticOrderAt _root_.RHTower.xi w).toNat
  set X_m : ℝ := ((m + 5 : ℕ) : ℝ)
  have hX5 : 5 ≤ X_m := by dsimp only [X_m]; exact_mod_cast (show 5 ≤ m + 5 by omega)
  have hX1 : 1 ≤ X_m := by linarith only [hX5]
  have hX_pos : 0 < X_m := by linarith only [hX1]
  have hr_pos : 0 < r := lt_of_lt_of_le (Real.exp_pos _) hr_lo
  -- Extract `ρ` coordinates from `ρ ∈ xiUnitWindowZeros (m : ℝ)`.
  have hρ_Z : ρ ∈ Z_m := hsub_unit hρ_unit
  have hρ_xi : _root_.RHTower.xi ρ = 0 := ((hZ_iff ρ).mp hρ_Z).2
  have hρ_strip : 0 < ρ.re ∧ ρ.re < 1 ∧ (m : ℝ) ≤ ρ.im ∧ ρ.im ≤ (m : ℝ) + 1 := by
    obtain ⟨hmem_s, hm_le⟩ := mem_xiUnitWindowZeros.mp hρ_unit
    obtain ⟨⟨hr0, hr1, _, hm_lt⟩, _⟩ :=
      (_root_.RHTower.stripZeros_finite ((m : ℝ) + 1)).mem_toFinset.mp hmem_s
    exact ⟨hr0, hr1, hm_le, hm_lt.le⟩
  -- Peel `Z_m` from `xi` on `Set.univ` using `_root_.RHTower.exists_finite_peel`.
  obtain ⟨m_ord, h_cof, hh_an, hm_ord_eq, hh_Z_nz, hxi_peel⟩ :=
    _root_.RHTower.exists_finite_peel isOpen_univ (_root_.RHTower.xi_analyticOnNhd Set.univ) Z_m
      (fun w _ => Set.mem_univ w) (fun w _ => _root_.RHTower.xi_orderAt_ne_top w)
  have hh_diff : Differentiable ℂ h_cof := fun z => (hh_an z (Set.mem_univ z)).differentiableAt
  have hd_sum_eq : ∑ w ∈ Z_m, m_ord w = d := Finset.sum_congr rfl hm_ord_eq
  -- Minimum modulus of `h_cof` on `closure U_box = [-1/2, 3/2] ×ℂ [y₁, y₂]`.
  let U_box : Set ℂ := Set.Ioo (-1 / 2 : ℝ) (3 / 2 : ℝ) ×ℂ Set.Ioo y₁ y₂
  have hy_lt : y₁ < y₂ := by linarith [hy₁_hi, hy₂_lo]
  have hre_lt : (-1 / 2 : ℝ) < (3 / 2 : ℝ) := by norm_num
  have hcl_box : closure U_box = Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ) ×ℂ Set.Icc y₁ y₂ := by
    rw [Complex.closure_reProdIm, closure_Ioo hre_lt.ne, closure_Ioo hy_lt.ne]
  have hbdd_box : Bornology.IsBounded U_box := by
    refine Bornology.IsBounded.subset
      (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2 + |y₁| + |y₂|)) ?_
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre_abs : |z.re| ≤ 3 / 2 := abs_le.mpr ⟨by linarith [hz.1.1], hz.1.2.le⟩
    have him_abs : |z.im| ≤ |y₁| + |y₂| :=
      abs_le.mpr ⟨by linarith [hz.2.1, neg_abs_le y₁, abs_nonneg y₂],
                  by linarith [hz.2.2, le_abs_self y₂, abs_nonneg y₁]⟩
    linarith [Complex.norm_le_abs_re_add_abs_im z]
  have hfront_xi : ∀ z ∈ frontier U_box,
      c_good * Real.exp (-((m + 3 : ℕ) : ℝ)) ≤ ‖_root_.RHTower.xi z‖ := by
    intro z hz
    rw [Complex.frontier_reProdIm, closure_Ioo hre_lt.ne, frontier_Ioo hre_lt,
      closure_Ioo hy_lt.ne, frontier_Ioo hy_lt] at hz
    have hmem_edge : (-1 / 2 ≤ z.re ∧ z.re ≤ 3 / 2) ∧ (y₁ ≤ z.im ∧ z.im ≤ y₂) ∧
        (z.re = -1 / 2 ∨ z.re = 3 / 2 ∨ z.im = y₁ ∨ z.im = y₂) := by
      rcases hz with hz1 | hz2
      · simp only [Complex.mem_reProdIm, Set.mem_Icc, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hz1
        rcases hz1.2 with hy_eq | hy_eq
        · exact ⟨hz1.1, ⟨le_of_eq hy_eq.symm, by linarith [hy_lt]⟩, Or.inr (Or.inr (Or.inl hy_eq))⟩
        · exact ⟨hz1.1, ⟨by linarith [hy_lt], le_of_eq hy_eq⟩, Or.inr (Or.inr (Or.inr hy_eq))⟩
      · simp only [Complex.mem_reProdIm, Set.mem_Icc, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hz2
        rcases hz2.1 with hx_eq | hx_eq
        · exact ⟨⟨le_of_eq hx_eq.symm, by linarith [hre_lt]⟩, hz2.2, Or.inl hx_eq⟩
        · exact ⟨⟨by linarith [hre_lt], le_of_eq hx_eq⟩, hz2.2, Or.inr (Or.inl hx_eq)⟩
    obtain ⟨t, ht⟩ := exists_boundaryPath_eq_of_edges
      (z₁ := centeredWindowLowerLeft y₁) (z₂ := centeredWindowUpperRight y₂)
      (by simp; norm_num) (by simp [hy_lt.le])
      (by simpa using hmem_edge.1) (by simpa using hmem_edge.2.1)
      (by simpa using hmem_edge.2.2)
    rw [← ht]
    exact hbdry_m t
  have hh_cl_nz : ∀ z ∈ closure U_box, h_cof z ≠ 0 := by
    intro z hz h0
    by_cases hzZ : z ∈ Z_m
    · exact hh_Z_nz z hzZ h0
    · have hxi0 : _root_.RHTower.xi z = 0 := by
        rw [hxi_peel z (Set.mem_univ z), h0, mul_zero]
      by_cases hzU : z ∈ U_box
      · rw [Complex.mem_reProdIm] at hzU
        obtain ⟨hr0, hr1⟩ := _root_.RHTower.xi_zero_re_mem_open_unit hxi0
        exact hzZ ((hZ_iff z).mpr ⟨⟨hr0, hr1, hzU.2.1, hzU.2.2⟩, hxi0⟩)
      · have hzF : z ∈ frontier U_box := ⟨hz, fun h_int => hzU (interior_subset h_int)⟩
        have hb := hfront_xi z hzF
        rw [hxi0, norm_zero] at hb
        have : 0 < c_good * Real.exp (-((m + 3 : ℕ) : ℝ)) := by positivity
        linarith
  have hprod_upper : ∀ z ∈ closure U_box, ‖∏ w ∈ Z_m, (z - w) ^ m_ord w‖ ≤ (8 : ℝ) ^ d := by
    intro z hz
    rw [hcl_box, Complex.mem_reProdIm] at hz
    rw [norm_prod]
    have hterm_le : ∀ w ∈ Z_m, ‖(z - w) ^ m_ord w‖ ≤ (8 : ℝ) ^ m_ord w := by
      intro w hw
      rw [norm_pow]
      obtain ⟨⟨hw_r0, hw_r1, hw_y1, hw_y2⟩, _⟩ := (hZ_iff w).mp hw
      have hzw_le : ‖z - w‖ ≤ 8 := by
        have hn := Complex.norm_le_abs_re_add_abs_im (z - w)
        have hre_d : |(z - w).re| ≤ 2 := by
          rw [Complex.sub_re]; exact abs_le.mpr ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
        have him_d : |(z - w).im| ≤ 5 := by
          rw [Complex.sub_im]; exact abs_le.mpr ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
        linarith
      exact pow_le_pow_left₀ (norm_nonneg _) hzw_le _
    calc ∏ w ∈ Z_m, ‖(z - w) ^ m_ord w‖
        ≤ ∏ w ∈ Z_m, (8 : ℝ) ^ m_ord w :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) hterm_le
      _ = (8 : ℝ) ^ (∑ w ∈ Z_m, m_ord w) := by rw [Finset.prod_pow_eq_pow_sum]
      _ = (8 : ℝ) ^ d := by rw [hd_sum_eq]
  have hh_inv_dc : DiffContOnCl ℂ (fun z => (h_cof z)⁻¹) U_box := by
    refine DifferentiableOn.diffContOnCl ?_
    exact (hh_diff.differentiableOn).inv hh_cl_nz
  have hh_lower : ∀ z ∈ closure U_box,
      c_good * Real.exp (-((m + 3 : ℕ) : ℝ)) / (8 : ℝ) ^ d ≤ ‖h_cof z‖ := by
    have hfront_inv : ∀ z ∈ frontier U_box,
        ‖(h_cof z)⁻¹‖ ≤ (8 : ℝ) ^ d / (c_good * Real.exp (-((m + 3 : ℕ) : ℝ))) := by
      intro z hzF
      have hzCl : z ∈ closure U_box := hzF.1
      have hxi_ge := hfront_xi z hzF
      have hpeel_norm : ‖_root_.RHTower.xi z‖ ≤ (8 : ℝ) ^ d * ‖h_cof z‖ := by
        rw [hxi_peel z (Set.mem_univ z), norm_mul]
        exact mul_le_mul_of_nonneg_right (hprod_upper z hzCl) (norm_nonneg _)
      have hh_pos : 0 < ‖h_cof z‖ := norm_pos_iff.mpr (hh_cl_nz z hzCl)
      rw [norm_inv, inv_le_comm₀ hh_pos (by positivity), inv_div]
      rw [div_le_iff₀ (by positivity)]
      linarith
    intro z hzCl
    have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le hbdd_box hh_inv_dc hfront_inv hzCl
    have hh_pos : 0 < ‖h_cof z‖ := norm_pos_iff.mpr (hh_cl_nz z hzCl)
    rw [norm_inv] at hmax
    have hflip := (inv_le_comm₀ hh_pos (by positivity)).mp hmax
    rwa [inv_div] at hflip
  -- Concentric-sphere pigeonhole inside `closedBall ρ r`.
  have hcard_Z : Z_m.card ≤ d := by
    have h1 : ∀ w ∈ Z_m, 1 ≤ (analyticOrderAt _root_.RHTower.xi w).toNat := by
      intro w hw
      have hw0 := ((hZ_iff w).mp hw).2
      have hne0 : analyticOrderAt _root_.RHTower.xi w ≠ 0 := by
        intro h0
        rcases analyticOrderAt_eq_zero.mp h0 with hnot | hnz
        · exact hnot (_root_.RHTower.xi_analyticOnNhd Set.univ w (Set.mem_univ w))
        · exact hnz hw0
      have hcoe := ENat.coe_toNat (_root_.RHTower.xi_orderAt_ne_top w)
      by_contra hlt
      have hz : (analyticOrderAt _root_.RHTower.xi w).toNat = 0 := by omega
      rw [hz, ENat.coe_zero] at hcoe
      exact hne0 hcoe.symm
    calc Z_m.card = ∑ _w ∈ Z_m, 1 := by simp
      _ ≤ ∑ w ∈ Z_m, (analyticOrderAt _root_.RHTower.xi w).toNat := Finset.sum_le_sum h1
      _ = d := rfl
  set δ_r : ℝ := r / (2 * ((d + 1 : ℕ) : ℝ))
  have hδ_pos : 0 < δ_r := by dsimp only [δ_r]; positivity
  obtain ⟨k_star, hk_Icc, hgap_sphere⟩ := exists_concentric_sphere_gap Z_m d hcard_Z ρ hδ_pos
  obtain ⟨hk_lo, hk_hi⟩ := Finset.mem_Icc.mp hk_Icc
  set r_star : ℝ := ((2 * k_star - 1 : ℕ) : ℝ) * δ_r
  have hr_star_pos : 0 < r_star := by
    dsimp only [r_star]
    have hk_pos : (0 : ℝ) < ((2 * k_star - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < 2 * k_star - 1 by omega)
    positivity
  have hr_star_le : r_star ≤ r := by
    dsimp only [r_star, δ_r]
    have hk_le : ((2 * k_star - 1 : ℕ) : ℝ) ≤ 2 * ((d + 1 : ℕ) : ℝ) := by
      have hn : 2 * k_star - 1 ≤ 2 * (d + 1) := by omega
      exact_mod_cast hn
    have hden_pos : (0 : ℝ) < 2 * ((d + 1 : ℕ) : ℝ) := by positivity
    calc ((2 * k_star - 1 : ℕ) : ℝ) * (r / (2 * ((d + 1 : ℕ) : ℝ)))
        ≤ (2 * ((d + 1 : ℕ) : ℝ)) * (r / (2 * ((d + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right hk_le (by positivity)
      _ = r := mul_div_cancel₀ r hden_pos.ne'
  have hball_in_box : ∀ z ∈ Metric.closedBall ρ r_star, z ∈ closure U_box ∧ |z.re| ≤ 2 := by
    intro z hz
    have hzr_star : ‖z - ρ‖ ≤ r_star := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hzr : ‖z - ρ‖ ≤ r := hzr_star.trans hr_star_le
    have hre_d : |z.re - ρ.re| ≤ 1 / 48 :=
      (Complex.abs_re_le_norm (z - ρ)).trans (hzr.trans hr_hi)
    have him_d : |z.im - ρ.im| ≤ 1 / 48 :=
      (Complex.abs_im_le_norm (z - ρ)).trans (hzr.trans hr_hi)
    obtain ⟨hre_l, hre_u⟩ := abs_le.mp hre_d
    obtain ⟨him_l, him_u⟩ := abs_le.mp him_d
    rw [hcl_box, Complex.mem_reProdIm]
    exact ⟨⟨⟨by linarith [hρ_strip.1], by linarith [hρ_strip.2.1]⟩,
            ⟨by linarith [hρ_strip.2.2.1, hy₁_hi], by linarith [hρ_strip.2.2.2, hy₂_lo]⟩⟩,
           abs_le.mpr ⟨by linarith [hρ_strip.1], by linarith [hρ_strip.2.1]⟩⟩
  -- Lower bound `m₀` on `‖xi‖` along `sphere ρ r_star`.
  set m₀ : ℝ := c_good * Real.exp (-((m + 3 : ℕ) : ℝ)) * (δ_r / 8) ^ d
  have hm₀_pos : 0 < m₀ := by dsimp only [m₀]; positivity
  have hsphere_xi : ∀ z ∈ Metric.sphere ρ r_star, m₀ ≤ ‖_root_.RHTower.xi z‖ := by
    intro z hzS
    have hzCl := (hball_in_box z (Metric.sphere_subset_closedBall hzS)).1
    have hprod_ge : δ_r ^ d ≤ ‖∏ w ∈ Z_m, (z - w) ^ m_ord w‖ := by
      rw [norm_prod, ← hd_sum_eq, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod (fun _ _ => pow_nonneg hδ_pos.le _) fun w hw => ?_
      rw [norm_pow]
      exact pow_le_pow_left₀ hδ_pos.le (hgap_sphere z hzS w hw) (m_ord w)
    calc m₀
        = δ_r ^ d * (c_good * Real.exp (-((m + 3 : ℕ) : ℝ)) / (8 : ℝ) ^ d) := by
            dsimp only [m₀]; rw [div_pow]; ring
      _ ≤ ‖∏ w ∈ Z_m, (z - w) ^ m_ord w‖ * ‖h_cof z‖ :=
            mul_le_mul hprod_ge (hh_lower z hzCl) (by positivity) (norm_nonneg _)
      _ = ‖_root_.RHTower.xi z‖ := by
            rw [hxi_peel z (Set.mem_univ z), norm_mul]
  -- Show `thetaStripTailBound N < m₀ / 2` for all `N ≥ K_d * (Nat.sqrt m + 1)`.
  have htail_lt : thetaStripTailBound N < m₀ / 2 := by
    have hN1_sq : B_d * X_m ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := by
      have hm1_sq : m + 1 ≤ (Nat.sqrt m + 1) ^ 2 := Nat.succ_le_of_lt (Nat.lt_succ_sqrt' m)
      have hX_sq : X_m ≤ 5 * ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ 2 := by
        have hnat : m + 5 ≤ 5 * (Nat.sqrt m + 1) ^ 2 :=
          (show m + 5 ≤ 5 * (m + 1) by omega).trans (Nat.mul_le_mul_left 5 hm1_sq)
        dsimp only [X_m]; exact_mod_cast hnat
      have hN1_ge : (K_d : ℝ) * ((Nat.sqrt m + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
        exact_mod_cast (hN.trans (Nat.le_succ N))
      calc B_d * X_m
          ≤ B_d * (5 * ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hX_sq hBd_pos.le
        _ = (5 * B_d) * ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ 2 := by ring
        _ ≤ (K_d : ℝ) ^ 2 * ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hKd_sq (by positivity)
        _ = ((K_d : ℝ) * ((Nat.sqrt m + 1 : ℕ) : ℝ)) ^ 2 := by ring
        _ ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hN1_ge 2
    have hd_sqrt : (d : ℝ) ≤ 4 * (C_u : ℝ) * Real.sqrt X_m := by
      have hl4 := log_le_four_sqrt_add_five m
      calc (d : ℝ) ≤ (C_u : ℝ) * Real.log X_m := hd_Cu
        _ ≤ (C_u : ℝ) * (4 * Real.sqrt X_m) := mul_le_mul_of_nonneg_left hl4 (Nat.cast_nonneg _)
        _ = 4 * (C_u : ℝ) * Real.sqrt X_m := by ring
    have hinv_δ8 : (8 / δ_r) ≤ M_f * Real.exp (2 * Real.sqrt X_m) := by
      have h8δ : 8 / δ_r = (16 * ((d + 1 : ℕ) : ℝ)) * (1 / r) := by
        dsimp only [δ_r]; field_simp [hr_pos.ne']; ring
      have h1r : 1 / r ≤ Real.exp (Real.sqrt X_m) := by
        rw [one_div]
        have hinv := inv_anti₀ (Real.exp_pos _) hr_lo
        rwa [Real.exp_neg, inv_inv] at hinv
      have hsqrt1 : 1 ≤ Real.sqrt X_m := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hX1
      have hd1_exp : 16 * ((d + 1 : ℕ) : ℝ) ≤ M_f * Real.exp (Real.sqrt X_m) := by
        have h1 : 16 * ((d + 1 : ℕ) : ℝ) ≤ M_f * Real.sqrt X_m := by
          have hc : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
          rw [← hM_fac_def, hc]
          linarith only [hd_sqrt, hsqrt1]
        have h2 : Real.sqrt X_m ≤ Real.exp (Real.sqrt X_m) := by
          linarith [Real.add_one_le_exp (Real.sqrt X_m)]
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hMf_pos.le)
      rw [h8δ]
      calc (16 * ((d + 1 : ℕ) : ℝ)) * (1 / r)
          ≤ (M_f * Real.exp (Real.sqrt X_m)) * Real.exp (Real.sqrt X_m) :=
            mul_le_mul hd1_exp h1r (by positivity) (by positivity)
        _ = M_f * Real.exp (2 * Real.sqrt X_m) := by
            rw [mul_assoc, ← Real.exp_add, show Real.sqrt X_m + Real.sqrt X_m = 2 * Real.sqrt X_m by ring]
    have hpow_inv : (8 / δ_r) ^ d ≤
        Real.exp (4 * (C_u : ℝ) * (Real.log M_f + 2) * X_m) := by
      have h1 : 8 / δ_r ≤ Real.exp (Real.log M_f + 2 * Real.sqrt X_m) := by
        rw [Real.exp_add, Real.exp_log hMf_pos]; exact hinv_δ8
      have hp := pow_le_pow_left₀ (by positivity) h1 d
      rw [← Real.exp_nat_mul] at hp
      refine hp.trans (Real.exp_le_exp.mpr ?_)
      have hsqrt1 : 1 ≤ Real.sqrt X_m := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hX1
      have hMf_rt : Real.log M_f + 2 * Real.sqrt X_m ≤ (Real.log M_f + 2) * Real.sqrt X_m := by
        have hl : Real.log M_f ≤ Real.log M_f * Real.sqrt X_m :=
          le_mul_of_one_le_right (Real.log_nonneg hM_fac1) hsqrt1
        linarith only [hl]
      calc (d : ℝ) * (Real.log M_f + 2 * Real.sqrt X_m)
          ≤ (4 * (C_u : ℝ) * Real.sqrt X_m) * ((Real.log M_f + 2) * Real.sqrt X_m) :=
            mul_le_mul hd_sqrt hMf_rt
              (add_nonneg (Real.log_nonneg hM_fac1) (by positivity)) (by positivity)
        _ = 4 * (C_u : ℝ) * (Real.log M_f + 2) * (Real.sqrt X_m ^ 2) := by ring
        _ = 4 * (C_u : ℝ) * (Real.log M_f + 2) * X_m := by rw [Real.sq_sqrt hX_pos.le]
    have hm₀_ge :
        (c_good / 2) *
          Real.exp (-(((m + 3 : ℕ) : ℝ) + 4 * (C_u : ℝ) * (Real.log M_f + 2) * X_m)) ≤
        m₀ / 2 := by
      have hpow_pos : 0 < (δ_r / 8) ^ d := by positivity
      have hinv_pow : ((8 / δ_r) ^ d)⁻¹ = (δ_r / 8) ^ d := by rw [← inv_pow, inv_div]
      have hpow_ge : Real.exp (-(4 * (C_u : ℝ) * (Real.log M_f + 2) * X_m)) ≤ (δ_r / 8) ^ d := by
        rw [Real.exp_neg, ← hinv_pow]
        exact inv_anti₀ (by positivity) hpow_inv
      calc (c_good / 2) *
            Real.exp (-(((m + 3 : ℕ) : ℝ) + 4 * (C_u : ℝ) * (Real.log M_f + 2) * X_m))
          = (c_good / 2) * Real.exp (-((m + 3 : ℕ) : ℝ)) *
              Real.exp (-(4 * (C_u : ℝ) * (Real.log M_f + 2) * X_m)) := by
            rw [neg_add, Real.exp_add, ← mul_assoc]
        _ ≤ (c_good / 2) * Real.exp (-((m + 3 : ℕ) : ℝ)) * (δ_r / 8) ^ d :=
            mul_le_mul_of_nonneg_left hpow_ge (by positivity)
        _ = m₀ / 2 := by dsimp only [m₀]; ring
    have hexp_lt : C_e * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) <
        (c_good / 2) *
          Real.exp (-(((m + 3 : ℕ) : ℝ) + 4 * (C_u : ℝ) * (Real.log M_f + 2) * X_m)) := by
      have harg_lt :
          Real.log (4 * C_e / c_good) + ((m + 3 : ℕ) : ℝ) +
            4 * (C_u : ℝ) * (Real.log M_f + 2) * X_m < ((N + 1 : ℕ) : ℝ) ^ 2 := by
        have hm3_X : ((m + 3 : ℕ) : ℝ) ≤ X_m := by
          dsimp only [X_m]; exact_mod_cast (show m + 3 ≤ m + 5 by omega)
        have habs_X : |Real.log (4 * C_e / c_good)| ≤ |Real.log (4 * C_e / c_good)| * X_m :=
          le_mul_of_one_le_right (abs_nonneg _) hX1
        have hle_abs := le_abs_self (Real.log (4 * C_e / c_good))
        have hmul_B := mul_le_mul_of_nonneg_right hB_bound hX_pos.le
        have hring_B :
            (|Real.log (4 * C_e / c_good)| + 1 +
              4 * (C_u : ℝ) * (Real.log M_f + 2) + 1) * X_m =
            |Real.log (4 * C_e / c_good)| * X_m + X_m +
              4 * (C_u : ℝ) * (Real.log M_f + 2) * X_m + X_m := by ring
        linarith only [hm3_X, habs_X, hle_abs, hmul_B, hring_B, hX1, hN1_sq]
      have hlt_e :
          C_e * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) <
          C_e * Real.exp (-(Real.log (4 * C_e / c_good) + ((m + 3 : ℕ) : ℝ) +
            4 * (C_u : ℝ) * (Real.log M_f + 2) * X_m)) :=
        mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by linarith only [harg_lt])) hCe_pos
      refine hlt_e.trans_le ?_
      rw [show -(Real.log (4 * C_e / c_good) + ((m + 3 : ℕ) : ℝ) +
            4 * (C_u : ℝ) * (Real.log M_f + 2) * X_m) =
          -Real.log (4 * C_e / c_good) +
            -(((m + 3 : ℕ) : ℝ) + 4 * (C_u : ℝ) * (Real.log M_f + 2) * X_m) by ring,
        Real.exp_add, Real.exp_neg, Real.exp_log (by positivity), ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have hCe_ne : C_e ≠ 0 := hCe_pos.ne'
      have hcg_ne : c_good ≠ 0 := hc_pos.ne'
      have heq : C_e * (4 * C_e / c_good)⁻¹ = c_good / 4 := by
        rw [inv_div]
        calc C_e * (c_good / (4 * C_e))
            = (c_good / 4) * (C_e / C_e) := by ring
          _ = c_good / 4 := by rw [div_self hCe_ne, mul_one]
      rw [heq]; linarith only [hc_pos]
    exact (hC_env_tail N).trans_lt (hexp_lt.trans_le hm₀_ge)
  -- Apply `GaloisForLFunctions.HTGeometry.exists_zero_mem_closedBall_of_norm_sub_lt` on `closedBall ρ r_star`!
  have hA_diff : Differentiable ℂ (_root_.RHTower.finiteThetaAmplitude N) := fun z => by
    have hfun : _root_.RHTower.finiteThetaAmplitude N = finiteThetaShellPencil N 0 :=
      (funext (finiteThetaShellPencil_zero N)).symm
    rw [hfun]
    exact (analyticOnNhd_finiteThetaShellPencil N 0 z (Set.mem_univ z)).differentiableAt
  have hclose_N : ∀ z ∈ Metric.closedBall ρ r_star,
      ‖_root_.RHTower.finiteThetaAmplitude N z - _root_.RHTower.xi z‖ < m₀ / 2 := by
    intro z hz
    have hle : ‖_root_.RHTower.finiteThetaAmplitude N z - _root_.RHTower.xi z‖ ≤
        thetaStripTailBound N := by
      have h := norm_finiteThetaAmplitude_sub_xi_le_strip N (by norm_num : (0 : ℝ) ≤ 2)
        (hball_in_box z hz).2
      simpa only [thetaStripTailBound, mul_right_comm] using h
    exact hle.trans_lt htail_lt
  obtain ⟨z_N, hz_N_star, hz_N_zero⟩ :=
    GaloisForLFunctions.HTGeometry.exists_zero_mem_closedBall_of_norm_sub_lt
      hr_star_pos hA_diff hρ_xi hsphere_xi hclose_N
  exact ⟨z_N, Metric.closedBall_subset_closedBall hr_star_le hz_N_star, hz_N_zero⟩

/-- Absolute `Θ(√m)` prefix constant dominating both `burnolPrefixConst` and local ball capture. -/
def doorOpenerSqrtConst : ℕ :=
  exists_doorOpenerSqrtConst.choose

theorem burnolPrefixConst_le_doorOpenerSqrtConst : burnolPrefixConst ≤ doorOpenerSqrtConst :=
  exists_doorOpenerSqrtConst.choose_spec.1

theorem four_le_doorOpenerSqrtConst : 4 ≤ doorOpenerSqrtConst :=
  four_le_burnolPrefixConst.trans burnolPrefixConst_le_doorOpenerSqrtConst

/-- Canonical `Θ(√m)` door-opener prefix `doorOpenerSqrtConst * (Nat.sqrt m + 1)`. -/
def doorSqrtPrefix (m : ℕ) : ℕ :=
  doorOpenerSqrtConst * (Nat.sqrt m + 1)

theorem burnolPrefix_le_doorSqrtPrefix (m : ℕ) :
    burnolPrefixConst * (Nat.sqrt m + 1) ≤ doorSqrtPrefix m :=
  Nat.mul_le_mul_right _ burnolPrefixConst_le_doorOpenerSqrtConst

/-- **Quantitative `Θ(√m)` local Hurwitz–Rouché zero capture (`exists_prefix_zero_in_ball_of_xi_zero`).**
For every natural height `m : ℕ`, every `ρ ∈ xiUnitWindowZeros (m : ℝ)`, every radius
`exp(-√(m + 5)) ≤ r ≤ 1 / 48`, and every `N ≥ doorSqrtPrefix m`, `finiteThetaAmplitude N` vanishes
at some point `z_N ∈ Metric.closedBall ρ r`. -/
theorem exists_prefix_zero_in_ball_of_xi_zero (m : ℕ) {ρ : ℂ}
    (hρ : ρ ∈ xiUnitWindowZeros (m : ℝ)) {r : ℝ}
    (hr_lo : Real.exp (-Real.sqrt ((m + 5 : ℕ) : ℝ)) ≤ r) (hr_hi : r ≤ 1 / 48)
    {N : ℕ} (hN : doorSqrtPrefix m ≤ N) :
    ∃ z_N ∈ Metric.closedBall ρ r, _root_.RHTower.finiteThetaAmplitude N z_N = 0 :=
  exists_doorOpenerSqrtConst.choose_spec.2 m ρ hρ r hr_lo hr_hi N hN


/-! ## §3 Two-way equivalence between `Θ(√m)`-prefix Szegő positivity and the `A / log |γ|` corridor -/

/-- Elementary dominance of the Vinogradov–Korobov width `(log y)^{-2/3} (log log y)^{-5/3} / 10⁸`
over `K / log y` for any constant `K > 0` at sufficiently large height `y`. -/
private lemma exists_height_vkZeroFreeWidth_gt_div_log (K : ℝ) (hK : 0 < K) :
    ∃ M_vk : ℝ, Real.exp (Real.exp 30) ≤ M_vk ∧
      ∀ y : ℝ, M_vk ≤ y → K / Real.log y < SquareRootThreshold.vkZeroFreeWidth y := by
  let M_base : ℝ := 256 * (10 : ℝ) ^ 8 * (K + 1) + 1
  have hM_base1 : 1 ≤ M_base := by
    dsimp only [M_base]
    have hnn : 0 ≤ 256 * (10 : ℝ) ^ 8 * (K + 1) :=
      mul_nonneg (by norm_num) (by linarith only [hK])
    linarith only [hnn]
  let M_vk : ℝ := max (Real.exp (Real.exp 30)) (Real.exp (M_base ^ 8))
  refine ⟨M_vk, le_max_left _ _, fun y hy => ?_⟩
  have hy_e30 : Real.exp (Real.exp 30) ≤ y := (le_max_left _ _).trans hy
  have hy_M8 : Real.exp (M_base ^ 8) ≤ y := (le_max_right _ _).trans hy
  have hy_pos : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy_e30
  set u : ℝ := Real.log y
  have hu_e30 : Real.exp 30 ≤ u := (Real.le_log_iff_exp_le hy_pos).mpr hy_e30
  have hu_M8 : M_base ^ 8 ≤ u := (Real.le_log_iff_exp_le hy_pos).mpr hy_M8
  have hu1 : 1 ≤ u := by linarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 30)]
  have hu_pos : 0 < u := by linarith only [hu1]
  have hlu30 : 30 ≤ Real.log u := by
    rw [← Real.log_exp 30]; exact Real.log_le_log (Real.exp_pos 30) hu_e30
  have hlu1 : 1 ≤ Real.log u := by linarith only [hlu30]
  have hlu_pos : 0 < Real.log u := by linarith only [hlu1]
  set q : ℝ := u ^ ((1 : ℝ) / 16)
  have hq_pos : 0 < q := Real.rpow_pos_of_pos hu_pos _
  have hq1 : 1 ≤ q := Real.one_le_rpow hu1 (by norm_num)
  have hq16 : q ^ (16 : ℕ) = u := by
    dsimp only [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu_pos.le]
    norm_num
  have hlog_u : Real.log u ≤ 16 * q := by
    rw [← hq16, Real.log_pow, Nat.cast_ofNat]
    linarith [Real.log_le_sub_one_of_pos hq_pos]
  have hrpow1 : u ^ ((2 : ℝ) / 3) ≤ q ^ (12 : ℕ) := by
    calc u ^ ((2 : ℝ) / 3)
        ≤ u ^ ((3 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
      _ = (q ^ (16 : ℕ)) ^ ((3 : ℝ) / 4) := by rw [hq16]
      _ = q ^ (12 : ℕ) := by
          rw [← Real.rpow_natCast q 16, ← Real.rpow_mul hq_pos.le]
          norm_num
  have hrpow2 : (Real.log u) ^ ((5 : ℝ) / 3) ≤ 256 * q ^ 2 := by
    calc (Real.log u) ^ ((5 : ℝ) / 3)
        ≤ (Real.log u) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hlu1 (by norm_num)
      _ = (Real.log u) ^ 2 := Real.rpow_two _
      _ ≤ (16 * q) ^ 2 := pow_le_pow_left₀ hlu_pos.le hlog_u 2
      _ = 256 * q ^ 2 := by ring
  have hden_le : u ^ ((2 : ℝ) / 3) * (Real.log u) ^ ((5 : ℝ) / 3) ≤ 256 * q ^ 14 := by
    calc u ^ ((2 : ℝ) / 3) * (Real.log u) ^ ((5 : ℝ) / 3)
        ≤ q ^ 12 * (256 * q ^ 2) := mul_le_mul hrpow1 hrpow2 (by positivity) (by positivity)
      _ = 256 * q ^ 14 := by ring
  have hq2_ge : M_base ≤ q ^ 2 := by
    by_contra hlt
    replace hlt : q ^ 2 < M_base := not_le.mp hlt
    have hp8 : (q ^ 2) ^ 8 < M_base ^ 8 :=
      pow_lt_pow_left₀ hlt (by positivity) (by norm_num : 8 ≠ 0)
    have heq16 : (q ^ 2) ^ 8 = u := by rw [← pow_mul, show 2 * 8 = 16 by norm_num, hq16]
    linarith
  have hvk_eq : SquareRootThreshold.vkZeroFreeWidth y =
      (u ^ ((2 : ℝ) / 3) * (Real.log u) ^ ((5 : ℝ) / 3))⁻¹ / (10 : ℝ) ^ 8 := by
    unfold SquareRootThreshold.vkZeroFreeWidth
    dsimp only [u]
    rw [show -(2 : ℝ) / 3 = -((2 : ℝ) / 3) by ring,
        show -(5 : ℝ) / 3 = -((5 : ℝ) / 3) by ring,
        Real.rpow_neg hu_pos.le, Real.rpow_neg hlu_pos.le, mul_inv]
  rw [hvk_eq]
  have hvk_ge : (K + 1) / u ≤
      (u ^ ((2 : ℝ) / 3) * (Real.log u) ^ ((5 : ℝ) / 3))⁻¹ / (10 : ℝ) ^ 8 := by
    have hinv_ge : (256 * q ^ 14)⁻¹ ≤ (u ^ ((2 : ℝ) / 3) * (Real.log u) ^ ((5 : ℝ) / 3))⁻¹ :=
      inv_anti₀ (by positivity) hden_le
    calc (K + 1) / u
        = ((256 * (10 : ℝ) ^ 8 * (K + 1)) / q ^ 2) * ((256 * q ^ 14)⁻¹ / (10 : ℝ) ^ 8) := by
          rw [← hq16]
          have hq_ne : q ≠ 0 := hq_pos.ne'
          field_simp [hq_ne]
      _ ≤ 1 * ((256 * q ^ 14)⁻¹ / (10 : ℝ) ^ 8) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [div_le_one (by positivity)]
          have hMb_le : 256 * (10 : ℝ) ^ 8 * (K + 1) ≤ M_base := by dsimp only [M_base]; linarith
          exact hMb_le.trans hq2_ge
      _ ≤ (u ^ ((2 : ℝ) / 3) * (Real.log u) ^ ((5 : ℝ) / 3))⁻¹ / (10 : ℝ) ^ 8 := by
          rw [one_mul]; exact div_le_div_of_nonneg_right hinv_ge (by positivity)
  have hK_lt : K / u < (K + 1) / u := div_lt_div_of_pos_right (by linarith) hu_pos
  exact hK_lt.trans_le hvk_ge

/-- Symmetric Vinogradov–Korobov margin `|ρ.re - 1 / 2| ≤ 1 / 2 - vkZeroFreeWidth |ρ.im|` for all
`ρ ∈ zetaZeroConfig.carrier` above `γ₀`. -/
private lemma abs_re_sub_half_le_vk :
    ∃ γ₀ : ℝ, Real.exp (Real.exp 30) ≤ γ₀ ∧
      ∀ ρ ∈ _root_.Zeta23.zetaZeroConfig.carrier, γ₀ ≤ |ρ.im| →
        |ρ.re - 1 / 2| ≤ 1 / 2 - SquareRootThreshold.vkZeroFreeWidth |ρ.im| := by
  obtain ⟨γ₀, hγ₀, hvk⟩ := SquareRootThreshold.exists_re_le_of_mem_zetaCarrier_vk
  refine ⟨γ₀, hγ₀, fun ρ hρ him => ?_⟩
  have hup : ρ.re ≤ 1 - SquareRootThreshold.vkZeroFreeWidth |ρ.im| := hvk ρ hρ him
  obtain ⟨hxi, hr0, hr1⟩ :=
    _root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ
  have hrefl_mem : 1 - star ρ ∈ _root_.Zeta23.zetaZeroConfig.carrier := by
    rw [_root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip]
    refine ⟨?_, by simp; linarith, by simp; linarith⟩
    rw [_root_.RHTower.xi_one_sub]
    change _root_.RHTower.xi ((starRingEnd ℂ) ρ) = 0
    rw [_root_.RHTower.xi_conj, hxi, map_zero]
  have hrefl_im : |(1 - star ρ).im| = |ρ.im| := by simp
  have hup_refl := hvk (1 - star ρ) hrefl_mem (by rw [hrefl_im]; exact him)
  rw [hrefl_im] at hup_refl
  have hlo : SquareRootThreshold.vkZeroFreeWidth |ρ.im| ≤ ρ.re := by
    have : (1 - star ρ).re = 1 - ρ.re := by simp
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **Deterministic 6-way equivalence (`List.TFAE`) between `Θ(√m)`-prefix logarithmic-stage Szegő
positivity and the classical `A / log |γ|` zero-free corridor.** -/
theorem logStage_sqrtPrefix_szego_iff_invLog_corridor :
    [ -- 1. Classical `xi` inverse-logarithmic zero-free corridor:
      ∃ T₁ A : ℝ, 2 ≤ T₁ ∧ 0 < A ∧
        ∀ ρ : ℂ, _root_.RHTower.xi ρ = 0 → T₁ ≤ |ρ.im| →
          |ρ.re - 1 / 2| ≤ A / Real.log |ρ.im|,
      -- 2. `zetaZeroConfig.carrier` inverse-logarithmic zero-free corridor:
      ∃ T₁ A : ℝ, 2 ≤ T₁ ∧ 0 < A ∧
        ∀ ρ ∈ _root_.Zeta23.zetaZeroConfig.carrier, T₁ ≤ |ρ.im| →
          |ρ.re - 1 / 2| ≤ A / Real.log |ρ.im|,
      -- 3. Deterministic `Θ(√m)`-prefix Devinatz–Widom closed-disk Szegő positivity at `logDoorStage c m`:
      ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ N ≥ doorSqrtPrefix m,
        ∃ F : ℂ → ℂ, IsDiskUnit F ∧
          ∀ u : HTGeometry.UnitCircle,
            0 < (F (u : ℂ) *
              centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
                (logDoorStage c m) N u).re,
      -- 4. Deterministic `Θ(√m)`-prefix outer polynomial Birkhoff–Szegő factorization:
      ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ N ≥ doorSqrtPrefix m,
        ∃ G H : Polynomial ℂ, IsOuterPolynomial G ∧ IsOuterPolynomial H ∧
          centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
            (logDoorStage c m) N = circlePoly G * star (circlePoly H),
      -- 5. Deterministic `Θ(√m)`-prefix circle-nonvanishing + `L²(ℝ)` Wiener–Hopf invertibility:
      ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ N ≥ doorSqrtPrefix m,
        (∀ u : HTGeometry.UnitCircle,
          centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
            (logDoorStage c m) N u ≠ 0) ∧
        IsUnit (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m)
          (logDoorStage c m) N),
      -- 6. Deterministic `Θ(√m)`-prefix circle-nonvanishing + height-uniform `fredholmIndex < 2`:
      ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ N ≥ doorSqrtPrefix m,
        (∀ u : HTGeometry.UnitCircle,
          centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
            (logDoorStage c m) N u ≠ 0) ∧
        HTGeometry.fredholmIndex
          (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m)
            (logDoorStage c m) N) < 2
    ].TFAE := by
  tfae_have 1 → 2 := by
    rintro ⟨T₁, A, hT₁, hA, hcorr⟩
    refine ⟨T₁, A, hT₁, hA, fun ρ hρ him => hcorr ρ ?_ him⟩
    exact (_root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ).1
  tfae_have 2 → 1 := by
    rintro ⟨T₁, A, hT₁, hA, hcorr⟩
    refine ⟨T₁, A, hT₁, hA, fun ρ hxi him => hcorr ρ ?_ him⟩
    exact _root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_of_xi_eq_zero hxi
  tfae_have 2 → 3 := by
    rintro ⟨T₁, A, hT₁, hA, hcorr⟩
    set c : ℝ := 1 / (32 * A + 1)
    have hc_pos : 0 < c := by dsimp only [c]; positivity
    have hc_le1 : c ≤ 1 := by
      dsimp only [c]
      exact div_le_one_of_le₀ (by linarith) (by positivity)
    have h32Ac : 32 * A * c < 1 := by
      dsimp only [c]
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith
    set m₀ : ℕ := max 20 (Nat.ceil (max (T₁ + 5) (Real.exp (6 / c))))
    refine ⟨c, hc_pos, m₀, fun m hm N hN => ?_⟩
    have hm20 : 20 ≤ m := (le_max_left 20 _).trans hm
    have hm_ceil : Nat.ceil (max (T₁ + 5) (Real.exp (6 / c))) ≤ m := (le_max_right 20 _).trans hm
    have hm_max : max (T₁ + 5) (Real.exp (6 / c)) ≤ (m : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hm_ceil)
    have hm_T1 : T₁ + 5 ≤ (m : ℝ) := (le_max_left _ _).trans hm_max
    have hm_exp : Real.exp (6 / c) ≤ (m : ℝ) := (le_max_right _ _).trans hm_max
    set X_m : ℝ := ((m + 5 : ℕ) : ℝ)
    have hX_gt_m : (m : ℝ) ≤ X_m := by dsimp only [X_m]; exact_mod_cast (show m ≤ m + 5 by omega)
    have hX_pos : 0 < X_m := by dsimp only [X_m]; exact_mod_cast (show 0 < m + 5 by omega)
    have h6_le_clog : 6 ≤ c * Real.log X_m := by
      have hlog_ge : 6 / c ≤ Real.log X_m :=
        (Real.le_log_iff_exp_le hX_pos).mpr (hm_exp.trans hX_gt_m)
      have hm_c := mul_le_mul_of_nonneg_left hlog_ge hc_pos.le
      rwa [mul_div_cancel₀ 6 hc_pos.ne'] at hm_c
    set n_m : ℕ := logDoorStage c m
    have hn6 : 6 ≤ n_m := six_le_logDoorStage c m
    have hn_le : (n_m : ℝ) ≤ 2 * c * Real.log X_m := by
      have hceil_ge6 : 6 ≤ Nat.ceil (c * Real.log X_m) :=
        Nat.ceil_mono h6_le_clog |>.trans_eq' (by simp)
      have hn_eq : n_m = Nat.ceil (c * Real.log X_m) := by
        dsimp only [n_m, logDoorStage]; exact max_eq_right hceil_ge6
      rw [hn_eq]
      have hlt := (Nat.ceil_lt_add_one (by linarith : 0 ≤ c * Real.log X_m)).le
      linarith
    have hn_Smax :
        (n_m : ℝ) ≤ 6 * Real.exp (Real.sqrt X_m) +
          2 * ((∑ w ∈ burnolUnitXiZeros m, (analyticOrderAt _root_.RHTower.xi w).toNat : ℕ) : ℝ) ^ 2 := by
      have hl4 := log_le_four_sqrt_add_five m
      have hrt_exp : Real.sqrt X_m ≤ Real.exp (Real.sqrt X_m) := by
        linarith [Real.add_one_le_exp (Real.sqrt X_m)]
      have hsq_nn : 0 ≤ 2 * ((∑ w ∈ burnolUnitXiZeros m,
          (analyticOrderAt _root_.RHTower.xi w).toNat : ℕ) : ℝ) ^ 2 := by positivity
      have hn_log : (n_m : ℝ) ≤ 2 * Real.log X_m := by
        have hlog_nn : 0 ≤ Real.log X_m := by
          have : 0 < c * Real.log X_m := by linarith only [h6_le_clog]
          exact (mul_pos_iff_of_pos_left hc_pos).mp this |>.le
        calc (n_m : ℝ) ≤ 2 * c * Real.log X_m := hn_le
          _ ≤ 2 * 1 * Real.log X_m :=
              mul_le_mul_of_nonneg_right (by linarith only [hc_le1]) hlog_nn
          _ = 2 * Real.log X_m := by ring
      have hlog_2rt : Real.log X_m ≤ 2 * Real.sqrt X_m := log_le_two_sqrt_of_pos hX_pos
      calc (n_m : ℝ) ≤ 2 * Real.log X_m := hn_log
        _ ≤ 4 * Real.sqrt X_m := by linarith only [hlog_2rt]
        _ ≤ 6 * Real.exp (Real.sqrt X_m) := by linarith [Real.exp_pos (Real.sqrt X_m)]
        _ ≤ 6 * Real.exp (Real.sqrt X_m) +
            2 * ((∑ w ∈ burnolUnitXiZeros m,
              (analyticOrderAt _root_.RHTower.xi w).toNat : ℕ) : ℝ) ^ 2 :=
            le_add_of_nonneg_right hsq_nn
    -- Verify `|z.re - 1 / 2| ≤ 1 / (8 * n_m)` for every `z ∈ burnolUnitXiZeros m`.
    have hZ_iff := mem_burnolUnitXiZeros_iff m
    have hy1_ge := sub_three_le_burnolUnitLower m
    have hm_margin : ∀ z ∈ burnolUnitXiZeros m, |z.re - 1 / 2| ≤ 1 / (8 * (n_m : ℝ)) := by
      intro z hz
      obtain ⟨⟨hr0, hr1, hy1_z, _⟩, hxi_z⟩ := (hZ_iff z).mp hz
      have hm20_r : (20 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm20
      have hzim_17 : 17 ≤ z.im := by linarith
      have hzim_T1 : T₁ ≤ |z.im| := by rw [abs_of_pos (by linarith)]; linarith
      have hz_carr : z ∈ _root_.Zeta23.zetaZeroConfig.carrier :=
        _root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mpr
          ⟨hxi_z, hr0, hr1⟩
      have hcz := hcorr z hz_carr hzim_T1
      have hX_le_sq : X_m ≤ |z.im| ^ 2 := by
        rw [abs_of_pos (by linarith)]
        have hcast : X_m = (m : ℝ) + 5 := by dsimp only [X_m]; push_cast; ring
        rw [hcast]
        have hlin : (m : ℝ) + 5 ≤ z.im + 8 := by linarith
        nlinarith only [hzim_17, hlin]
      have hlogX_le : Real.log X_m ≤ 2 * Real.log |z.im| := by
        calc Real.log X_m
            ≤ Real.log (|z.im| ^ 2) := Real.log_le_log hX_pos hX_le_sq
          _ = 2 * Real.log |z.im| := by rw [Real.log_pow, Nat.cast_ofNat]
      have hlog_im_pos : 0 < Real.log |z.im| :=
        Real.log_pos (by rw [abs_of_pos (by linarith)]; linarith)
      have h8An : 8 * A * (n_m : ℝ) ≤ Real.log |z.im| := by
        calc 8 * A * (n_m : ℝ)
            ≤ 8 * A * (2 * c * Real.log X_m) :=
              mul_le_mul_of_nonneg_left hn_le (by positivity)
          _ = (32 * A * c) * ((1 / 2) * Real.log X_m) := by ring
          _ ≤ 1 * ((1 / 2) * (2 * Real.log |z.im|)) := by
              refine mul_le_mul h32Ac.le ?_ (by positivity) zero_le_one
              linarith only [hlogX_le]
          _ = Real.log |z.im| := by ring
      have hn_pos : (0 : ℝ) < (n_m : ℝ) := by exact_mod_cast (show 0 < n_m by omega)
      refine hcz.trans ?_
      rw [div_le_div_iff₀ hlog_im_pos (by positivity), one_mul]
      linarith only [h8An]
    have hgap : ∀ z ∈ burnolUnitXiZeros m, ∀ w ∈ burnolUnitXiZeros m,
        1 < zhukovskyEllipseForm n_m (z - w) ∧
          1 / (8 * (n_m : ℝ) ^ 3) ≤ |zhukovskyEllipseForm n_m (z - w) - 1| :=
      fun z hz w hw => zhukovskyEllipseForm_gt_one_of_re_margin.2 hn6 (hm_margin z hz) (hm_margin w hw)
    have hN_base : burnolPrefixConst * (Nat.sqrt m + 1) ≤ N :=
      (burnolPrefix_le_doorSqrtPrefix m).trans hN
    have hbdry := burnolUnit_bdry_regular m hN_base
    obtain ⟨hloop_nz, hind_sum⟩ := burnolUnit_singleStage_stabilization m
      n_m n_m hn6 le_rfl hn_Smax (fun z hz w hw => (hgap z hz w hw).2) N hN_base
    have hind0 :
        HTGeometry.fredholmIndex
          (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m) n_m N) = 0 := by
      rw [hind_sum, mul_eq_zero]
      right
      refine Finset.sum_eq_zero fun z hz => Finset.sum_eq_zero fun w hw => ?_
      rw [if_neg (not_lt.mpr (hgap z hz w hw).1.le), mul_zero]
    exact ((centeredTheta_szego_positivity_tfae (burnolUnitLower_le_upper m) n_m N
      hbdry hloop_nz).out 1 5).mp hind0
  tfae_have 3 → 4 := by
    rintro ⟨c, hc, m₀, hsz⟩
    refine ⟨c, hc, m₀, fun m hm N hN => ?_⟩
    obtain ⟨F, hF, hpos⟩ := hsz m hm N hN
    have hnz : ∀ u : HTGeometry.UnitCircle,
        centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
          (logDoorStage c m) N u ≠ 0 := by
      intro u h0
      have hp := hpos u
      rw [h0, mul_zero, Complex.zero_re] at hp
      exact lt_irrefl 0 hp
    have hbdry := burnolUnit_bdry_regular m ((burnolPrefix_le_doorSqrtPrefix m).trans hN)
    exact ((centeredTheta_szego_positivity_tfae (burnolUnitLower_le_upper m)
      (logDoorStage c m) N hbdry hnz).out 5 4).mp (hsz m hm N hN)
  tfae_have 4 → 5 := by
    rintro ⟨c, hc, m₀, hout⟩
    refine ⟨c, hc, m₀, fun m hm N hN => ?_⟩
    obtain ⟨G, H, hG, hH, hGH⟩ := hout m hm N hN
    have hnz : ∀ u : HTGeometry.UnitCircle,
        centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
          (logDoorStage c m) N u ≠ 0 := by
      intro u
      rw [hGH, ContinuousMap.mul_apply, ContinuousMap.star_apply, circlePoly_apply, circlePoly_apply]
      exact mul_ne_zero (hG (u : ℂ) (HTGeometry.norm_coe_unitCircle u).le)
        (star_ne_zero.mpr (hH (u : ℂ) (HTGeometry.norm_coe_unitCircle u).le))
    have hbdry := burnolUnit_bdry_regular m ((burnolPrefix_le_doorSqrtPrefix m).trans hN)
    exact ⟨hnz, ((centeredTheta_szego_positivity_tfae (burnolUnitLower_le_upper m)
      (logDoorStage c m) N hbdry hnz).out 4 2).mp (hout m hm N hN)⟩
  tfae_have 5 → 6 := by
    rintro ⟨c, hc, m₀, hunit⟩
    refine ⟨c, hc, m₀, fun m hm N hN => ?_⟩
    obtain ⟨hnz, hu⟩ := hunit m hm N hN
    have hbdry := burnolUnit_bdry_regular m ((burnolPrefix_le_doorSqrtPrefix m).trans hN)
    exact ⟨hnz, ((centeredTheta_szego_positivity_tfae (burnolUnitLower_le_upper m)
      (logDoorStage c m) N hbdry hnz).out 2 0).mp hu⟩
  tfae_have 6 → 2 := by
    rintro ⟨c, hc, m₀, hind_all⟩
    obtain ⟨γ₀, hγ₀_e30, hvk_sym⟩ := abs_re_sub_half_le_vk
    obtain ⟨M_vk, hM_e30, hvk_dom⟩ :=
      exists_height_vkZeroFreeWidth_gt_div_log (1 / c + 1) (by positivity)
    set T₁ : ℝ := max (max (γ₀ + 2) (M_vk + 2))
      (max (((m₀ + 20 : ℕ) : ℝ)) ((2 * |Real.log (32 * (c + 6))| + 4) ^ 2))
    have hT₁2 : 2 ≤ T₁ := by
      have h1 : (20 : ℝ) ≤ ((m₀ + 20 : ℕ) : ℝ) := by exact_mod_cast (show 20 ≤ m₀ + 20 by omega)
      linarith [(le_max_left _ _).trans (le_max_right _ _ : max (((m₀ + 20 : ℕ) : ℝ)) _ ≤ T₁)]
    set A : ℝ := 1 / c + 1
    have hA_pos : 0 < A := by dsimp only [A]; positivity
    -- Prove for positive ordinates `ρ.im ≥ T₁`, then extend to `|ρ.im| ≥ T₁` via `conj ρ`.
    have hpos_im : ∀ ρ ∈ _root_.Zeta23.zetaZeroConfig.carrier, T₁ ≤ ρ.im →
        |ρ.re - 1 / 2| ≤ A / Real.log ρ.im := by
      intro ρ hρ him
      have him_pos : 0 < ρ.im := by linarith only [hT₁2, him]
      have him_γ₀ : γ₀ ≤ |ρ.im| := by
        rw [abs_of_pos him_pos]
        linarith [(le_max_left _ _).trans (le_max_left _ _ : max (γ₀ + 2) _ ≤ T₁), him]
      have him_Mvk : M_vk ≤ ρ.im := by
        linarith [(le_max_right _ _).trans (le_max_left _ _ : max (γ₀ + 2) (M_vk + 2) ≤ T₁), him]
      have him_m₀ : ((m₀ + 20 : ℕ) : ℝ) ≤ ρ.im :=
        ((le_max_left _ _).trans (le_max_right _ _)).trans him
      have him_rad : (2 * |Real.log (32 * (c + 6))| + 4) ^ 2 ≤ ρ.im :=
        ((le_max_right _ _).trans (le_max_right _ _)).trans him
      set m : ℕ := Nat.floor ρ.im
      have hm_le_im : (m : ℝ) ≤ ρ.im := Nat.floor_le him_pos.le
      have him_lt_m1 : ρ.im < (m : ℝ) + 1 := Nat.lt_floor_add_one ρ.im
      have hm_ge : m₀ ≤ m := by
        have hnat : m₀ + 20 ≤ m := Nat.le_floor him_m₀
        omega
      set n_m : ℕ := logDoorStage c m
      have hn6 : 6 ≤ n_m := six_le_logDoorStage c m
      have hn_pos : (0 : ℝ) < (n_m : ℝ) := by exact_mod_cast (show 0 < n_m by omega)
      have hs_eq : (zhukovskyStage n_m : ℝ) = (n_m : ℝ) := by
        exact_mod_cast zhukovskyStage_eq_self hn6
      -- Show `|ρ.re - 1 / 2| ≤ 3 / (8 * n_m)` by contradiction via local root capture!
      have hre_38 : |ρ.re - 1 / 2| ≤ 3 / (8 * (n_m : ℝ)) := by
        by_contra hgt_raw
        replace hgt_raw : 3 / (8 * (n_m : ℝ)) < |ρ.re - 1 / 2| := not_le.mp hgt_raw
        set N : ℕ := doorSqrtPrefix m
        obtain ⟨hnz, hind_lt⟩ := hind_all m hm_ge N le_rfl
        set X_m : ℝ := ((m + 5 : ℕ) : ℝ)
        have hX_gt_im : ρ.im ≤ X_m := by
          have hc_X : X_m = (m : ℝ) + 5 := by dsimp only [X_m]; push_cast; ring
          linarith
        have hX_pos : 0 < X_m := by linarith only [him_pos, hX_gt_im]
        -- Verify radius bounds `exp(-√X_m) ≤ 1 / (8 * n_m) ≤ 1 / 48`.
        set r : ℝ := 1 / (8 * (n_m : ℝ))
        have hr_hi : r ≤ 1 / 48 := by
          dsimp only [r]
          have hn6_r : (6 : ℝ) ≤ (n_m : ℝ) := by exact_mod_cast hn6
          exact one_div_le_one_div_of_le (by norm_num) (by linarith)
        have hr_lo : Real.exp (-Real.sqrt X_m) ≤ r := by
          have hn_ub : 8 * (n_m : ℝ) ≤ 32 * (c + 6) * Real.sqrt X_m := by
            have hlog_rt : Real.log X_m ≤ 2 * Real.sqrt X_m := log_le_two_sqrt_of_pos hX_pos
            have hlog_nn : 0 ≤ Real.log X_m := Real.log_nonneg (by linarith [hT₁2, him, hX_gt_im])
            have hceil_ub : (Nat.ceil (c * Real.log X_m) : ℝ) ≤ c * Real.log X_m + 1 :=
              (Nat.ceil_lt_add_one (by positivity)).le
            have hn_max : (n_m : ℝ) ≤ (2 * c + 6) * Real.sqrt X_m := by
              have hrt1 : 1 ≤ Real.sqrt X_m := by
                rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith [hT₁2, him, hX_gt_im])
              unfold n_m logDoorStage
              rw [Nat.cast_max, Nat.cast_ofNat]
              refine max_le (by nlinarith only [hc, hrt1]) ?_
              have hcr : c * Real.log X_m + 1 ≤ 2 * c * Real.sqrt X_m + Real.sqrt X_m := by
                have := mul_le_mul_of_nonneg_left hlog_rt hc.le
                linarith
              linarith
            have hrt_nn : 0 ≤ Real.sqrt X_m := Real.sqrt_nonneg X_m
            nlinarith only [hn_max, hc, hrt_nn]
          have hrt_half_ge : |Real.log (32 * (c + 6))| + 2 ≤ (1 / 2) * Real.sqrt X_m := by
            have hrt_ge : 2 * |Real.log (32 * (c + 6))| + 4 ≤ Real.sqrt X_m := by
              rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * |Real.log (32 * (c + 6))| + 4)]
              exact Real.sqrt_le_sqrt (him_rad.trans hX_gt_im)
            linarith
          have h32_exp : 32 * (c + 6) ≤ Real.exp ((1 / 2) * Real.sqrt X_m) := by
            rw [← Real.exp_log (by positivity : 0 < 32 * (c + 6))]
            exact Real.exp_le_exp.mpr
              ((le_abs_self _).trans (by linarith only [hrt_half_ge]))
          have hrt_exp : Real.sqrt X_m ≤ Real.exp ((1 / 2) * Real.sqrt X_m) := by
            have hu2 : 2 ≤ (1 / 2) * Real.sqrt X_m := by
              linarith [abs_nonneg (Real.log (32 * (c + 6))), hrt_half_ge]
            set u : ℝ := (1 / 2) * Real.sqrt X_m
            have he2 : Real.exp (u / 2) * Real.exp (u / 2) = Real.exp u := by
              rw [← Real.exp_add, add_halves]
            have ha1 : u / 2 + 1 ≤ Real.exp (u / 2) := Real.add_one_le_exp (u / 2)
            have hprod : (u / 2 + 1) * (u / 2 + 1) ≤ Real.exp u := by
              rw [← he2]; exact mul_le_mul ha1 ha1 (by linarith) (Real.exp_pos _).le
            have hquad : 2 * u ≤ (u / 2 + 1) * (u / 2 + 1) := by nlinarith only [hu2]
            calc Real.sqrt X_m = 2 * u := by dsimp only [u]; ring
              _ ≤ Real.exp u := hquad.trans hprod
          have h8n_exp : 8 * (n_m : ℝ) ≤ Real.exp (Real.sqrt X_m) := by
            calc 8 * (n_m : ℝ)
                ≤ (32 * (c + 6)) * Real.sqrt X_m := by linarith only [hn_ub]
              _ ≤ Real.exp ((1 / 2) * Real.sqrt X_m) * Real.exp ((1 / 2) * Real.sqrt X_m) :=
                  mul_le_mul h32_exp hrt_exp (Real.sqrt_nonneg _) (Real.exp_pos _).le
              _ = Real.exp (Real.sqrt X_m) := by rw [← Real.exp_add]; exact congrArg Real.exp (by ring)
          dsimp only [r]
          rw [Real.exp_neg, one_div]
          exact inv_anti₀ (by positivity) h8n_exp
        -- Capture a root `z_N` of `finiteThetaAmplitude N` in `closedBall ρ r`!
        obtain ⟨hxi_ρ, hr0_ρ, hr1_ρ⟩ :=
          _root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ
        have hρ_unit : ρ ∈ xiUnitWindowZeros (m : ℝ) :=
          mem_xiUnitWindowZeros.mpr
            ⟨(_root_.RHTower.stripZeros_finite ((m : ℝ) + 1)).mem_toFinset.mpr
              ⟨⟨hr0_ρ, hr1_ρ, him_pos.le, him_lt_m1⟩, hxi_ρ⟩, hm_le_im⟩
        obtain ⟨z_N, hz_ball, hz_zero⟩ :=
          exists_prefix_zero_in_ball_of_xi_zero m hρ_unit hr_lo hr_hi (N := N) le_rfl
        -- Apply `exists_birkhoffSzego_of_prod_eval` to the actual enclosed roots `Z_N` of `finiteThetaAmplitude N`!
        have hcoords := burnolUnit_coords m
        have hbdry := burnolUnit_bdry_regular m (burnolPrefix_le_doorSqrtPrefix m)
        obtain ⟨Z_N, hZN_mem, _, heval_N⟩ :=
          eval_centeredThetaDifferencePoly_eq_prod (burnolUnitLower_le_upper m) N hbdry
        have hmult_N_pos : ∀ z ∈ Z_N,
            1 ≤ (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z).toNat := by
          intro z hz
          have hz0 := ((hZN_mem z).mp hz).2
          have han_z : AnalyticAt ℂ (_root_.RHTower.finiteThetaAmplitude N) z := by
            have hfun : _root_.RHTower.finiteThetaAmplitude N = finiteThetaShellPencil N 0 :=
              (funext (finiteThetaShellPencil_zero N)).symm
            rw [hfun]
            exact analyticOnNhd_finiteThetaShellPencil N 0 z (Set.mem_univ z)
          have hord_ne_top : analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z ≠ ⊤ := by
            have hfun : _root_.RHTower.finiteThetaAmplitude N = finiteThetaShellPencil N 0 :=
              (funext (finiteThetaShellPencil_zero N)).symm
            rw [hfun]
            exact finiteThetaShellPencil_orderAt_ne_top N ⟨le_rfl, zero_le_one⟩ z
          have hne0 : analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z ≠ 0 := by
            intro h0
            rcases analyticOrderAt_eq_zero.mp h0 with hnot | hnz_z
            · exact hnot han_z
            · exact hnz_z hz0
          have hcoe := ENat.coe_toNat hord_ne_top
          by_contra hlt
          have hz_ord : (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z).toNat = 0 := by omega
          rw [hz_ord, ENat.coe_zero] at hcoe
          exact hne0 hcoe.symm
        have hell_N := ellipse_nondegenerate_of_prod_eval_ne_zero heval_N
          (fun z hz => hmult_N_pos z hz) fun u => by
            simpa only [centeredThetaLaurentLoop, polyZhukovskyLaurentLoop_apply] using hnz u
        obtain ⟨_, hwind_N, _⟩ := exists_birkhoffSzego_of_prod_eval heval_N hell_N
        have hind_eq_N :
            HTGeometry.fredholmIndex
              (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m) n_m N) =
            2 * ∑ z ∈ Z_N, ∑ w ∈ Z_N,
              ((analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z).toNat : ℤ) *
                ((analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat : ℤ) *
                (if zhukovskyEllipseForm n_m (z - w) < 1 then 1 else 0) := by
          unfold centeredThetaCollisionOperator centeredThetaCollisionSymbol
          rw [fredholmIndex_wienerHopfLift_unitNormalizeSymbol,
            circleWinding_unitNormalizeSymbol_of_ne_zero hnz]
          change _root_.RHTower.windingNumber
              (fun θ => ((centeredThetaDifferencePoly (burnolUnitLower m) (burnolUnitUpper m) N).eval
                (zhukovskyLoop n_m (HTGeometry.circleExp θ))) ^ 2) 0 (2 * Real.pi) = _
          rw [hwind_N]
          congr 1
          rw [Nat.cast_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Nat.cast_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          dsimp only [n_m]
          by_cases hlt : zhukovskyEllipseForm (logDoorStage c m) (z - w) < 1
          · rw [if_pos hlt, if_pos hlt]; push_cast; ring
          · rw [if_neg hlt, if_neg hlt, mul_zero, Nat.cast_zero, mul_zero]
        have hrefl_ZN : ∀ w ∈ Z_N, 1 - star w ∈ Z_N := by
          intro w hw
          obtain ⟨⟨hx1, hx2, hy1, hy2⟩, hw0⟩ := (hZN_mem w).mp hw
          rw [hZN_mem]
          refine ⟨⟨by simp; linarith, by simp; linarith, by simpa using hy1, by simpa using hy2⟩, ?_⟩
          rw [finiteThetaAmplitude_one_sub]
          have hconj := finiteThetaAmplitude_conj N w
          rw [hw0] at hconj
          exact star_eq_zero.mp hconj
        -- Verify `z_N ∈ Z_N` and that `z_N` lies in the resolved horizontal collision band!
        have hz_norm_r : ‖z_N - ρ‖ ≤ r := by
          simpa only [Metric.mem_closedBall, dist_eq_norm] using hz_ball
        have hz_re_diff : |z_N.re - ρ.re| ≤ r :=
          (Complex.abs_re_le_norm (z_N - ρ)).trans hz_norm_r
        have hz_im_diff : |z_N.im - ρ.im| ≤ r :=
          (Complex.abs_im_le_norm (z_N - ρ)).trans hz_norm_r
        have hz_mem_ZN : z_N ∈ Z_N := by
          rw [hZN_mem]
          obtain ⟨hxl, hxu⟩ := abs_le.mp hz_re_diff
          obtain ⟨hyl, hyu⟩ := abs_le.mp hz_im_diff
          exact ⟨⟨by linarith [hr0_ρ, hr_hi], by linarith [hr1_ρ, hr_hi],
            by linarith [hcoords.2.1, hm_le_im, hr_hi],
            by linarith [hcoords.2.2.1, him_lt_m1, hr_hi]⟩, hz_zero⟩
        have hband_lo : 1 / (4 * (zhukovskyStage n_m : ℝ)) < |z_N.re - 1 / 2| := by
          rw [hs_eq]
          have htri : |ρ.re - 1 / 2| ≤ |z_N.re - 1 / 2| + |z_N.re - ρ.re| := by
            have := abs_add_le (z_N.re - 1 / 2) (ρ.re - z_N.re)
            rw [show (z_N.re - 1 / 2) + (ρ.re - z_N.re) = ρ.re - 1 / 2 by ring,
                abs_sub_comm ρ.re z_N.re] at this
            exact this
          have h31 : 3 / (8 * (n_m : ℝ)) - 1 / (8 * (n_m : ℝ)) = 1 / (4 * (n_m : ℝ)) := by ring
          dsimp only [r] at hz_re_diff
          linarith
        have hband_hi : |z_N.re - 1 / 2| < 1 / 2 - 1 / (4 * (zhukovskyStage n_m : ℝ)) := by
          rw [hs_eq]
          have hvk_ρ := hvk_sym ρ hρ him_γ₀
          rw [abs_of_pos him_pos] at hvk_ρ
          have hvk_gt : A / Real.log ρ.im < SquareRootThreshold.vkZeroFreeWidth ρ.im :=
            hvk_dom ρ.im him_Mvk
          have hn_ge_c : c * Real.log ρ.im ≤ (n_m : ℝ) := by
            have hl_mono : Real.log ρ.im ≤ Real.log X_m := Real.log_le_log him_pos hX_gt_im
            calc c * Real.log ρ.im
                ≤ c * Real.log X_m := mul_le_mul_of_nonneg_left hl_mono hc.le
              _ ≤ (Nat.ceil (c * Real.log X_m) : ℝ) := Nat.le_ceil _
              _ ≤ (n_m : ℝ) := by exact_mod_cast (le_max_right 6 _)
          have hlog_im_pos : 0 < Real.log ρ.im := Real.log_pos (by linarith only [hT₁2, him])
          have h38_le_A : 3 / (8 * (n_m : ℝ)) ≤ A / Real.log ρ.im := by
            rw [div_le_div_iff₀ (by positivity) hlog_im_pos]
            have h1 : 3 * Real.log ρ.im ≤ 8 * (1 / c) * (c * Real.log ρ.im) := by
              rw [show 8 * (1 / c) * (c * Real.log ρ.im) = 8 * ((1 / c * c) * Real.log ρ.im) by ring,
                one_div_mul_cancel hc.ne', one_mul]
              linarith
            have h2 : 8 * (1 / c) * (c * Real.log ρ.im) ≤ 8 * A * (n_m : ℝ) := by
              have hA_ge : 1 / c ≤ A := by dsimp only [A]; linarith
              exact mul_le_mul (by linarith) hn_ge_c (by positivity) (by positivity)
            linarith
          have htri2 : |z_N.re - 1 / 2| ≤ |ρ.re - 1 / 2| + |z_N.re - ρ.re| := by
            have := abs_add_le (ρ.re - 1 / 2) (z_N.re - ρ.re)
            rwa [show (ρ.re - 1 / 2) + (z_N.re - ρ.re) = z_N.re - 1 / 2 by ring] at this
          have h18_14 : 1 / (8 * (n_m : ℝ)) + 1 / (4 * (n_m : ℝ)) = 3 / (8 * (n_m : ℝ)) := by ring
          dsimp only [r] at hz_re_diff
          linarith
        have hge2 := two_le_collision_sum_of_offLine_in_band hrefl_ZN hmult_N_pos
          hz_mem_ZN hband_lo hband_hi
        dsimp only [n_m] at hind_eq_N
        rw [← hind_eq_N] at hge2
        omega
      -- Deduce `|ρ.re - 1 / 2| ≤ A / Real.log ρ.im` from `|ρ.re - 1 / 2| ≤ 3 / (8 * n_m)`.
      have hlog_im_pos : 0 < Real.log ρ.im := Real.log_pos (by linarith only [hT₁2, him])
      have hn_ge_c : c * Real.log ρ.im ≤ (n_m : ℝ) := by
        have hX_gt_im : ρ.im ≤ ((m + 5 : ℕ) : ℝ) := by
          have : ((m + 5 : ℕ) : ℝ) = (m : ℝ) + 5 := by push_cast; ring
          linarith
        calc c * Real.log ρ.im
            ≤ c * Real.log ((m + 5 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left (Real.log_le_log him_pos hX_gt_im) hc.le
          _ ≤ (Nat.ceil (c * Real.log ((m + 5 : ℕ) : ℝ)) : ℝ) := Nat.le_ceil _
          _ ≤ (n_m : ℝ) := by exact_mod_cast (le_max_right 6 _)
      refine hre_38.trans ?_
      rw [div_le_div_iff₀ (by positivity) hlog_im_pos]
      have h1 : 3 * Real.log ρ.im ≤ 8 * (1 / c) * (c * Real.log ρ.im) := by
        rw [show 8 * (1 / c) * (c * Real.log ρ.im) = 8 * ((1 / c * c) * Real.log ρ.im) by ring,
          one_div_mul_cancel hc.ne', one_mul]
        linarith
      have h2 : 8 * (1 / c) * (c * Real.log ρ.im) ≤ 8 * A * (n_m : ℝ) := by
        have hA_ge : 1 / c ≤ A := by dsimp only [A]; linarith
        exact mul_le_mul (by linarith) hn_ge_c (by positivity) (by positivity)
      linarith
    refine ⟨T₁, A, hT₁2, hA_pos, fun ρ hρ habs => ?_⟩
    rcases le_or_gt 0 ρ.im with him0 | him_neg
    · rw [abs_of_nonneg him0] at habs ⊢
      exact hpos_im ρ hρ habs
    · have hc_mem : (starRingEnd ℂ) ρ ∈ _root_.Zeta23.zetaZeroConfig.carrier :=
        _root_.RHTower.conj_mem_zetaZeroConfig hρ
      have hconj_im : ((starRingEnd ℂ) ρ).im = -ρ.im := Complex.conj_im ρ
      rw [abs_of_neg him_neg] at habs ⊢
      have hres := hpos_im ((starRingEnd ℂ) ρ) hc_mem (by rw [hconj_im]; exact habs)
      rwa [Complex.conj_re, hconj_im] at hres
  tfae_finish


/-! ## §4 Fixed-scale Hecke-defect `E_γ(c₀ log T) = O(1)` implies `Θ(√m)` Szegő positivity,
the `A / log |γ|` corridor, and `LindelofCriticalLine` -/

/-- **Unconditional Hecke-defect door-opener implication (`heckeDefect_log_bound_implies_szego_corridor_and_lindelof`).**
For any `c₀ > 0` and `α ≥ 0`, any uniform unit-window prime-polynomial bound on
`heckeDefect (baseTwistTest γ) (c₀ * log T)` (including `α = 0`, i.e., `E_γ(c₀ log T) = O(1)`, or any
of the 5 equivalent conditions of `LogScaleHeckeDefect.heckeDefect_log_unitWindow_tfae`) forces:
1. Deterministic `Θ(√m)`-prefix Devinatz–Widom closed-disk Szegő positivity, outer polynomial
   Birkhoff–Szegő factorization, `L²(ℝ)` Wiener–Hopf invertibility, and `fredholmIndex = 0 < 2` at
   `logDoorStage c m` across all `m ≥ m₀` and `N ≥ doorSqrtPrefix m`;
2. Classical `A / log |γ|` zero-free corridor for `xi` and `zetaZeroConfig.carrier`;
3. `ZerosApproachLine`, `OffLineSparse`, `LindelofCriticalLine`, and `∃ β < 1 / 2, XiZeroHalfPlaneBound β`. -/
theorem heckeDefect_log_bound_implies_szego_corridor_and_lindelof {c₀ α : ℝ}
    (hc₀ : 0 < c₀) (hα : 0 ≤ α)
    (hhyp : ∃ C : ℝ, ∀ᶠ T : ℝ in atTop, ∀ γ ∈ Set.Icc T (T + 1),
      heckeDefect (baseTwistTest γ) (c₀ * Real.log T) ≤
        α * ‖SquareRootThreshold.primePolynomial (heckeAvgBump (c₀ * Real.log T))
          ⌊Real.exp (2 * (c₀ * Real.log T + 1 / 4))⌋₊ (-γ / (2 * Real.pi))‖ + C) :
    (∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ N ≥ doorSqrtPrefix m,
      (∀ u : HTGeometry.UnitCircle,
        centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
          (logDoorStage c m) N u ≠ 0) ∧
      HTGeometry.fredholmIndex
        (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m)
          (logDoorStage c m) N) = 0 ∧
      IsUnit (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m)
        (logDoorStage c m) N) ∧
      (∃ G H : Polynomial ℂ, IsOuterPolynomial G ∧ IsOuterPolynomial H ∧
        centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
          (logDoorStage c m) N = circlePoly G * star (circlePoly H)) ∧
      (∃ F : ℂ → ℂ, IsDiskUnit F ∧
        ∀ u : HTGeometry.UnitCircle,
          0 < (F (u : ℂ) *
            centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
              (logDoorStage c m) N u).re)) ∧
    (∃ T₁ A : ℝ, 2 ≤ T₁ ∧ 0 < A ∧
      ∀ ρ : ℂ, _root_.RHTower.xi ρ = 0 → T₁ ≤ |ρ.im| →
        |ρ.re - 1 / 2| ≤ A / Real.log |ρ.im|) ∧
    _root_.RHTower.BacklundConverse.ZerosApproachLine ∧
    _root_.RHTower.CosineSparseCluster.OffLineSparse ∧
    _root_.RHTower.LindelofSparse.LindelofCriticalLine ∧
    (∃ β : ℝ, β < 1 / 2 ∧ _root_.RHTower.XiZeroHalfPlaneBound β) := by
  obtain ⟨B, hB, hev_w⟩ :=
    ((LogScaleHeckeDefect.heckeDefect_log_unitWindow_tfae hc₀ hα).out 0 4).mp hhyp
  have hcorr_zeta :=
    LogScaleHeckeDefect.exists_log_zeroFree_corridor_of_heckeDefect_bound hc₀ hB hev_w
  have hcorr_xi := (logStage_sqrtPrefix_szego_iff_invLog_corridor.out 1 0).mp hcorr_zeta
  obtain ⟨c, hc_pos, m₀, hsz⟩ :=
    (logStage_sqrtPrefix_szego_iff_invLog_corridor.out 1 2).mp hcorr_zeta
  have hlind := LogScaleHeckeDefect.zerosApproachLine_and_lindelof_of_heckeDefect_log_bound hc₀ hα hhyp
  refine ⟨⟨c, hc_pos, m₀, fun m hm N hN => ?_⟩, hcorr_xi, hlind⟩
  obtain ⟨F, hF, hpos⟩ := hsz m hm N hN
  have hnz : ∀ u : HTGeometry.UnitCircle,
      centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
        (logDoorStage c m) N u ≠ 0 := by
    intro u h0
    have hp := hpos u
    rw [h0, mul_zero, Complex.zero_re] at hp
    exact lt_irrefl 0 hp
  have hbdry := burnolUnit_bdry_regular m ((burnolPrefix_le_doorSqrtPrefix m).trans hN)
  have htfae := centeredTheta_szego_positivity_tfae (burnolUnitLower_le_upper m)
    (logDoorStage c m) N hbdry hnz
  exact ⟨hnz, (htfae.out 5 1).mp (hsz m hm N hN), (htfae.out 5 2).mp (hsz m hm N hN),
    (htfae.out 5 4).mp (hsz m hm N hN), hsz m hm N hN⟩

/-- Direct `E_γ(c₀ log T) = O(1)` (`α = 0`) specialization of
`heckeDefect_log_bound_implies_szego_corridor_and_lindelof`. -/
theorem heckeDefect_log_O1_implies_szego_corridor_and_lindelof {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hO1 : ∃ B : ℝ, ∀ᶠ T : ℝ in atTop, ∀ γ ∈ Set.Icc T (T + 1),
      heckeDefect (baseTwistTest γ) (c₀ * Real.log T) ≤ B) :
    (∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ N ≥ doorSqrtPrefix m,
      (∀ u : HTGeometry.UnitCircle,
        centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
          (logDoorStage c m) N u ≠ 0) ∧
      HTGeometry.fredholmIndex
        (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m)
          (logDoorStage c m) N) = 0 ∧
      IsUnit (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m)
        (logDoorStage c m) N) ∧
      (∃ G H : Polynomial ℂ, IsOuterPolynomial G ∧ IsOuterPolynomial H ∧
        centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
          (logDoorStage c m) N = circlePoly G * star (circlePoly H)) ∧
      (∃ F : ℂ → ℂ, IsDiskUnit F ∧
        ∀ u : HTGeometry.UnitCircle,
          0 < (F (u : ℂ) *
            centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
              (logDoorStage c m) N u).re)) ∧
    (∃ T₁ A : ℝ, 2 ≤ T₁ ∧ 0 < A ∧
      ∀ ρ : ℂ, _root_.RHTower.xi ρ = 0 → T₁ ≤ |ρ.im| →
        |ρ.re - 1 / 2| ≤ A / Real.log |ρ.im|) ∧
    _root_.RHTower.BacklundConverse.ZerosApproachLine ∧
    _root_.RHTower.CosineSparseCluster.OffLineSparse ∧
    _root_.RHTower.LindelofSparse.LindelofCriticalLine ∧
    (∃ β : ℝ, β < 1 / 2 ∧ _root_.RHTower.XiZeroHalfPlaneBound β) := by
  obtain ⟨B, hev⟩ := hO1
  refine heckeDefect_log_bound_implies_szego_corridor_and_lindelof hc₀ le_rfl ⟨B, ?_⟩
  exact hev.mono fun T hT γ hγ => by simpa only [zero_mul, zero_add] using hT γ hγ


/-! ## §5 Master 9-way unconditional `RiemannHypothesis` door-opener equivalence -/

/-- Under `RiemannHypothesis`, every zero `z` of `xi` lies on `Re z = 1 / 2`. -/
private lemma xi_zero_re_eq_half_of_rh (hRH : RiemannHypothesis) {z : ℂ}
    (hz : _root_.RHTower.xi z = 0) : z.re = 1 / 2 := by
  have hempty := _root_.RHTower.rh_iff_forall_boxZeros_empty.mp hRH
  obtain ⟨hr0, hr1⟩ := _root_.RHTower.xi_zero_re_mem_open_unit hz
  have him_ne0 : z.im ≠ 0 := by
    intro him0
    have hpos := xi_re_ge_lowWindow (z := z)
      (abs_le.mpr ⟨by linarith, by linarith⟩) (by rw [him0, abs_zero]; norm_num)
    rw [hz, Complex.zero_re] at hpos
    have : (0 : ℝ) < (5026 / 16875) * Real.exp (-Real.pi) := by positivity
    linarith
  by_contra hne
  let w₁ : ℂ := if 1 / 2 < z.re then z else 1 - z
  have hw₁_xi : _root_.RHTower.xi w₁ = 0 := by
    dsimp only [w₁]; split_ifs
    · exact hz
    · rw [_root_.RHTower.xi_one_sub, hz]
  have hw₁_re : 1 / 2 < w₁.re ∧ w₁.re < 1 := by
    dsimp only [w₁]
    split_ifs with hgt
    · exact ⟨hgt, hr1⟩
    · have hlt : z.re < 1 / 2 := lt_of_le_of_ne (not_lt.mp hgt) hne
      exact ⟨by simp; linarith, by simp; linarith⟩
  have hw₁_im_ne : w₁.im ≠ 0 := by
    dsimp only [w₁]; split_ifs <;> simp [him_ne0]
  let w₂ : ℂ := if 0 < w₁.im then w₁ else (starRingEnd ℂ) w₁
  have hw₂_xi : _root_.RHTower.xi w₂ = 0 := by
    dsimp only [w₂]; split_ifs
    · exact hw₁_xi
    · rw [_root_.RHTower.xi_conj, hw₁_xi, map_zero]
  have hw₂_re : 1 / 2 < w₂.re ∧ w₂.re < 1 := by
    dsimp only [w₂]; split_ifs <;> simpa using hw₁_re
  have hw₂_im : 0 < w₂.im := by
    dsimp only [w₂]
    split_ifs with hp
    · exact hp
    · have hlt : w₁.im < 0 := lt_of_le_of_ne (not_lt.mp hp) hw₁_im_ne
      simp; linarith
  have hmem : w₂ ∈ _root_.RHTower.boxZeros (w₂.im + 1) :=
    ⟨⟨hw₂_re.1, hw₂_re.2, hw₂_im.le, by linarith⟩, hw₂_xi⟩
  rw [hempty (w₂.im + 1)] at hmem
  exact Set.notMem_empty _ hmem

/-- **Master 9-way unconditional `RiemannHypothesis` door-opener equivalence (`List.TFAE`).**
`RiemannHypothesis` is unconditionally equivalent to Devinatz–Widom closed-disk Szegő positivity,
outer polynomial Birkhoff–Szegő factorization, `L²(ℝ)` Wiener–Hopf invertibility, and
height-uniform `fredholmIndex < 2` at both:
- the zero-separation-free `O(m log²(m + S))` cumulative prefix `doorCumulPrefix m S` (`[1..4]`), and
- the Burnol-bracketed unit-window prefix `doorUnitPrefix m S` (`[5..8]`). -/
theorem riemannHypothesis_door_opener_tfae :
    [ -- 1. `RiemannHypothesis`:
      RiemannHypothesis,
      -- 2. Cumulative `O(m log²(m + S))`-prefix Devinatz–Widom closed-disk Szegő positivity:
      ∀ (m S : ℕ), ∀ N ≥ doorCumulPrefix m S,
        ∃ F : ℂ → ℂ, IsDiskUnit F ∧
          ∀ u : HTGeometry.UnitCircle,
            0 < (F (u : ℂ) *
              integerThetaLaurentLoop (doorCumulWindowHeight m S) (doorCumulStage m S) N u).re,
      -- 3. Cumulative `O(m log²(m + S))`-prefix outer polynomial Birkhoff–Szegő factorization:
      ∀ (m S : ℕ), ∀ N ≥ doorCumulPrefix m S,
        ∃ G H : Polynomial ℂ, IsOuterPolynomial G ∧ IsOuterPolynomial H ∧
          integerThetaLaurentLoop (doorCumulWindowHeight m S) (doorCumulStage m S) N =
            circlePoly G * star (circlePoly H),
      -- 4. Cumulative `O(m log²(m + S))`-prefix circle-nonvanishing + `L²(ℝ)` Wiener–Hopf invertibility:
      ∀ (m S : ℕ), ∀ N ≥ doorCumulPrefix m S,
        (∀ u : HTGeometry.UnitCircle,
          integerThetaLaurentLoop (doorCumulWindowHeight m S) (doorCumulStage m S) N u ≠ 0) ∧
        IsUnit (integerThetaCollisionOperator (doorCumulWindowHeight m S) (doorCumulStage m S) N),
      -- 5. Cumulative `O(m log²(m + S))`-prefix circle-nonvanishing + height-uniform `fredholmIndex < 2`:
      ∀ (m S : ℕ), ∀ N ≥ doorCumulPrefix m S,
        (∀ u : HTGeometry.UnitCircle,
          integerThetaLaurentLoop (doorCumulWindowHeight m S) (doorCumulStage m S) N u ≠ 0) ∧
        HTGeometry.fredholmIndex
          (integerThetaCollisionOperator (doorCumulWindowHeight m S) (doorCumulStage m S) N) < 2,
      -- 6. Burnol unit-window Devinatz–Widom closed-disk Szegő positivity:
      ∀ (m S : ℕ), ∀ N ≥ doorUnitPrefix m S,
        ∃ F : ℂ → ℂ, IsDiskUnit F ∧
          ∀ u : HTGeometry.UnitCircle,
            0 < (F (u : ℂ) *
              centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
                (doorUnitStage m S) N u).re,
      -- 7. Burnol unit-window outer polynomial Birkhoff–Szegő factorization:
      ∀ (m S : ℕ), ∀ N ≥ doorUnitPrefix m S,
        ∃ G H : Polynomial ℂ, IsOuterPolynomial G ∧ IsOuterPolynomial H ∧
          centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
            (doorUnitStage m S) N = circlePoly G * star (circlePoly H),
      -- 8. Burnol unit-window circle-nonvanishing + `L²(ℝ)` Wiener–Hopf invertibility:
      ∀ (m S : ℕ), ∀ N ≥ doorUnitPrefix m S,
        (∀ u : HTGeometry.UnitCircle,
          centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
            (doorUnitStage m S) N u ≠ 0) ∧
        IsUnit (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m)
          (doorUnitStage m S) N),
      -- 9. Burnol unit-window circle-nonvanishing + height-uniform `fredholmIndex < 2`:
      ∀ (m S : ℕ), ∀ N ≥ doorUnitPrefix m S,
        (∀ u : HTGeometry.UnitCircle,
          centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
            (doorUnitStage m S) N u ≠ 0) ∧
        HTGeometry.fredholmIndex
          (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m)
            (doorUnitStage m S) N) < 2
    ].TFAE := by
  tfae_have 1 → 2 := by
    intro hRH m S N hN
    obtain ⟨_, _, _, hN_spec⟩ := doorCumul_spec m S
    obtain ⟨hbdry, _, _, hell, hind_sum, _⟩ := hN_spec N hN
    have hind0 :
        HTGeometry.fredholmIndex
          (integerThetaCollisionOperator (doorCumulWindowHeight m S) (doorCumulStage m S) N) = 0 := by
      change HTGeometry.fredholmIndex (integerThetaCollisionOperator _ _ N) = _ at hind_sum
      rw [hind_sum, mul_eq_zero]
      right
      refine Finset.sum_eq_zero fun z hz => Finset.sum_eq_zero fun w hw => ?_
      have hz_re := xi_zero_re_eq_half_of_rh hRH (((_root_.RHTower.stripZeros_finite _).mem_toFinset.mp hz).2)
      have hw_re := xi_zero_re_eq_half_of_rh hRH (((_root_.RHTower.stripZeros_finite _).mem_toFinset.mp hw).2)
      have hgt1 : 1 < zhukovskyEllipseForm (doorCumulStage m S) (z - w) :=
        zhukovskyEllipseForm_gt_one_of_re_margin.1 (doorCumulStage m S)
          (by
            rw [hz_re, sub_self, abs_zero]
            exact one_div_pos.mpr (mul_pos (by norm_num) (zhukovskyStage_pos _)))
          (by
            rw [hw_re, sub_self, abs_zero]
            exact one_div_pos.mpr (mul_pos (by norm_num) (zhukovskyStage_pos _)))
      rw [if_neg (not_lt.mpr hgt1.le), mul_zero]
    exact ((integerTheta_szego_positivity_tfae (doorCumulWindowHeight m S)
      (doorCumulStage m S) N hbdry hell).out 1 5).mp hind0
  tfae_have 2 → 3 := by
    intro h m S N hN
    obtain ⟨_, _, _, hN_spec⟩ := doorCumul_spec m S
    obtain ⟨hbdry, _, _, hell, _, _⟩ := hN_spec N hN
    exact ((integerTheta_szego_positivity_tfae (doorCumulWindowHeight m S)
      (doorCumulStage m S) N hbdry hell).out 5 4).mp (h m S N hN)
  tfae_have 3 → 4 := by
    intro h m S N hN
    obtain ⟨_, _, _, hN_spec⟩ := doorCumul_spec m S
    obtain ⟨hbdry, _, hnz, hell, _, _⟩ := hN_spec N hN
    exact ⟨hnz, ((integerTheta_szego_positivity_tfae (doorCumulWindowHeight m S)
      (doorCumulStage m S) N hbdry hell).out 4 2).mp (h m S N hN)⟩
  tfae_have 4 → 5 := by
    intro h m S N hN
    obtain ⟨_, _, _, hN_spec⟩ := doorCumul_spec m S
    obtain ⟨hbdry, _, _, hell, _, _⟩ := hN_spec N hN
    obtain ⟨hnz, hu⟩ := h m S N hN
    exact ⟨hnz, ((integerTheta_szego_positivity_tfae (doorCumulWindowHeight m S)
      (doorCumulStage m S) N hbdry hell).out 2 0).mp hu⟩
  tfae_have 5 → 1 := by
    intro h
    rw [_root_.RHTower.rh_iff_forall_boxZeros_empty]
    intro U
    rw [Set.eq_empty_iff_forall_notMem]
    intro ρ hρ
    obtain ⟨⟨hr_lo, hr_hi, him_pos, _⟩, hxi_ρ⟩ := hρ
    set m : ℕ := Nat.ceil ρ.im + 1
    set δ_ρ : ℝ := min (ρ.re - 1 / 2) (1 - ρ.re)
    have hδ_pos : 0 < δ_ρ := lt_min (by linarith) (by linarith)
    set S : ℕ := Nat.ceil (1 / δ_ρ) + 6
    set N : ℕ := doorCumulPrefix m S
    obtain ⟨hT_lo, _, hn_Icc, hN_spec⟩ := doorCumul_spec m S
    obtain ⟨_, _, _, _, hind_sum, _⟩ := hN_spec N le_rfl
    have hind_lt := (h m S N le_rfl).2
    change HTGeometry.fredholmIndex
        (integerThetaCollisionOperator (doorCumulWindowHeight m S) (doorCumulStage m S) N) = _ at hind_sum
    have hn_ge_S : S ≤ doorCumulStage m S := (le_max_left S 6).trans (Finset.mem_Icc.mp hn_Icc).1
    have hn6 : 6 ≤ doorCumulStage m S := (le_max_right S 6).trans (Finset.mem_Icc.mp hn_Icc).1
    have hs_eq : (zhukovskyStage (doorCumulStage m S) : ℝ) = (doorCumulStage m S : ℝ) := by
      exact_mod_cast zhukovskyStage_eq_self hn6
    have hinv_lt : 1 / (4 * (zhukovskyStage (doorCumulStage m S) : ℝ)) < δ_ρ := by
      rw [hs_eq]
      have hS_gt : 1 / δ_ρ < (doorCumulStage m S : ℝ) := by
        calc 1 / δ_ρ ≤ (Nat.ceil (1 / δ_ρ) : ℝ) := Nat.le_ceil _
          _ < ((Nat.ceil (1 / δ_ρ) + 6 : ℕ) : ℝ) := by push_cast; linarith
          _ ≤ (doorCumulStage m S : ℝ) := by exact_mod_cast hn_ge_S
      have hn_pos : (0 : ℝ) < (doorCumulStage m S : ℝ) := by
        exact_mod_cast (show 0 < doorCumulStage m S by omega)
      have h1 : 1 / (doorCumulStage m S : ℝ) < δ_ρ := (div_lt_iff₀ hn_pos).mpr
        (by have := (div_lt_iff₀ hδ_pos).mp hS_gt; linarith)
      have h4 : 1 / (4 * (doorCumulStage m S : ℝ)) ≤ 1 / (doorCumulStage m S : ℝ) :=
        one_div_le_one_div_of_le hn_pos (by linarith)
      exact h4.trans_lt h1
    set Z_cum := (_root_.RHTower.stripZeros_finite (doorCumulHeight m S)).toFinset
    have hρ_Z : ρ ∈ Z_cum := by
      rw [Set.Finite.mem_toFinset]
      have him_lt_m : ρ.im < (m : ℝ) := by
        calc ρ.im ≤ (Nat.ceil ρ.im : ℝ) := Nat.le_ceil _
          _ < ((Nat.ceil ρ.im + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact ⟨⟨by linarith, hr_hi, him_pos, him_lt_m.trans_le hT_lo⟩, hxi_ρ⟩
    have hrefl_Z : ∀ w ∈ Z_cum, 1 - star w ∈ Z_cum := by
      intro w hw
      obtain ⟨⟨hw0, hw1, hwy0, hwyT⟩, hxi_w⟩ := (Set.Finite.mem_toFinset _).mp hw
      rw [Set.Finite.mem_toFinset]
      refine ⟨⟨by simp; linarith, by simp; linarith, by simpa using hwy0, by simpa using hwyT⟩, ?_⟩
      rw [_root_.RHTower.xi_one_sub]
      change _root_.RHTower.xi ((starRingEnd ℂ) w) = 0
      rw [_root_.RHTower.xi_conj, hxi_w, map_zero]
    have hmult_pos : ∀ w ∈ Z_cum, 1 ≤ (analyticOrderAt _root_.RHTower.xi w).toNat := by
      intro w hw
      exact Nat.one_le_iff_ne_zero.mpr
        (_root_.RHTower.xi_order_toNat_ne_zero (((Set.Finite.mem_toFinset _).mp hw).2))
    have hge2 := two_le_collision_sum_of_offLine_in_band hrefl_Z hmult_pos hρ_Z
      (hinv_lt.trans_le ((min_le_left _ _).trans (le_abs_self _)))
      (by
        rw [abs_of_pos (by linarith : 0 < ρ.re - 1 / 2)]
        have := (min_le_right (ρ.re - 1 / 2) (1 - ρ.re))
        linarith)
    rw [← hind_sum] at hge2
    omega
  tfae_have 1 → 6 := by
    intro hRH m S N hN
    obtain ⟨_, hspec⟩ := doorUnitStage_spec m S
    obtain ⟨hnz, hind_sum⟩ := hspec N hN
    have hN_base : burnolPrefixConst * (Nat.sqrt m + 1) ≤ N :=
      (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans hN
    have hbdry := burnolUnit_bdry_regular m hN_base
    have hZ_iff := mem_burnolUnitXiZeros_iff m
    have hind0 :
        HTGeometry.fredholmIndex
          (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m)
            (doorUnitStage m S) N) = 0 := by
      rw [hind_sum, mul_eq_zero]
      right
      refine Finset.sum_eq_zero fun z hz => Finset.sum_eq_zero fun w hw => ?_
      have hz_re := xi_zero_re_eq_half_of_rh hRH (((hZ_iff z).mp hz).2)
      have hw_re := xi_zero_re_eq_half_of_rh hRH (((hZ_iff w).mp hw).2)
      have hgt1 : 1 < zhukovskyEllipseForm (doorUnitStage m S) (z - w) :=
        zhukovskyEllipseForm_gt_one_of_re_margin.1 (doorUnitStage m S)
          (by
            rw [hz_re, sub_self, abs_zero]
            exact one_div_pos.mpr (mul_pos (by norm_num) (zhukovskyStage_pos _)))
          (by
            rw [hw_re, sub_self, abs_zero]
            exact one_div_pos.mpr (mul_pos (by norm_num) (zhukovskyStage_pos _)))
      rw [if_neg (not_lt.mpr hgt1.le), mul_zero]
    exact ((centeredTheta_szego_positivity_tfae (burnolUnitLower_le_upper m)
      (doorUnitStage m S) N hbdry hnz).out 1 5).mp hind0
  tfae_have 6 → 7 := by
    intro h m S N hN
    obtain ⟨_, hspec⟩ := doorUnitStage_spec m S
    obtain ⟨hnz, _⟩ := hspec N hN
    have hN_base : burnolPrefixConst * (Nat.sqrt m + 1) ≤ N :=
      (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans hN
    have hbdry := burnolUnit_bdry_regular m hN_base
    exact ((centeredTheta_szego_positivity_tfae (burnolUnitLower_le_upper m)
      (doorUnitStage m S) N hbdry hnz).out 5 4).mp (h m S N hN)
  tfae_have 7 → 8 := by
    intro h m S N hN
    obtain ⟨_, hspec⟩ := doorUnitStage_spec m S
    obtain ⟨hnz, _⟩ := hspec N hN
    have hN_base : burnolPrefixConst * (Nat.sqrt m + 1) ≤ N :=
      (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans hN
    have hbdry := burnolUnit_bdry_regular m hN_base
    exact ⟨hnz, ((centeredTheta_szego_positivity_tfae (burnolUnitLower_le_upper m)
      (doorUnitStage m S) N hbdry hnz).out 4 2).mp (h m S N hN)⟩
  tfae_have 8 → 9 := by
    intro h m S N hN
    obtain ⟨_, hspec⟩ := doorUnitStage_spec m S
    have hN_base : burnolPrefixConst * (Nat.sqrt m + 1) ≤ N :=
      (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans hN
    have hbdry := burnolUnit_bdry_regular m hN_base
    obtain ⟨hnz, hu⟩ := h m S N hN
    exact ⟨hnz, ((centeredTheta_szego_positivity_tfae (burnolUnitLower_le_upper m)
      (doorUnitStage m S) N hbdry hnz).out 2 0).mp hu⟩
  tfae_have 9 → 1 := by
    intro h
    rw [_root_.RHTower.rh_iff_forall_boxZeros_empty]
    intro U
    rw [Set.eq_empty_iff_forall_notMem]
    intro ρ hρ
    obtain ⟨⟨hr_lo, hr_hi, him_pos, _⟩, hxi_ρ⟩ := hρ
    set m : ℕ := Nat.floor ρ.im
    set δ_ρ : ℝ := min (ρ.re - 1 / 2) (1 - ρ.re)
    have hδ_pos : 0 < δ_ρ := lt_min (by linarith) (by linarith)
    set S : ℕ := Nat.ceil (1 / δ_ρ) + 6
    set N : ℕ := doorUnitPrefix m S
    obtain ⟨hn_Icc, hspec⟩ := doorUnitStage_spec m S
    obtain ⟨_, hind_sum⟩ := hspec N le_rfl
    have hind_lt := (h m S N le_rfl).2
    have hn_ge_S : S ≤ doorUnitStage m S := (le_max_left S 6).trans (Finset.mem_Icc.mp hn_Icc).1
    have hn6 : 6 ≤ doorUnitStage m S := (le_max_right S 6).trans (Finset.mem_Icc.mp hn_Icc).1
    have hs_eq : (zhukovskyStage (doorUnitStage m S) : ℝ) = (doorUnitStage m S : ℝ) := by
      exact_mod_cast zhukovskyStage_eq_self hn6
    have hinv_lt : 1 / (4 * (zhukovskyStage (doorUnitStage m S) : ℝ)) < δ_ρ := by
      rw [hs_eq]
      have hS_gt : 1 / δ_ρ < (doorUnitStage m S : ℝ) := by
        calc 1 / δ_ρ ≤ (Nat.ceil (1 / δ_ρ) : ℝ) := Nat.le_ceil _
          _ < ((Nat.ceil (1 / δ_ρ) + 6 : ℕ) : ℝ) := by push_cast; linarith
          _ ≤ (doorUnitStage m S : ℝ) := by exact_mod_cast hn_ge_S
      have hn_pos : (0 : ℝ) < (doorUnitStage m S : ℝ) := by
        exact_mod_cast (show 0 < doorUnitStage m S by omega)
      have h1 : 1 / (doorUnitStage m S : ℝ) < δ_ρ := (div_lt_iff₀ hn_pos).mpr
        (by have := (div_lt_iff₀ hδ_pos).mp hS_gt; linarith)
      have h4 : 1 / (4 * (doorUnitStage m S : ℝ)) ≤ 1 / (doorUnitStage m S : ℝ) :=
        one_div_le_one_div_of_le hn_pos (by linarith)
      exact h4.trans_lt h1
    have hZ_iff := mem_burnolUnitXiZeros_iff m
    have hsub_unit := xiUnitWindowZeros_subset_burnolUnitXiZeros m
    have hrefl_Z := one_sub_star_mem_burnolUnitXiZeros m
    have hρ_unit : ρ ∈ xiUnitWindowZeros (m : ℝ) :=
      mem_xiUnitWindowZeros.mpr
        ⟨(_root_.RHTower.stripZeros_finite ((m : ℝ) + 1)).mem_toFinset.mpr
          ⟨⟨by linarith, hr_hi, him_pos, Nat.lt_floor_add_one ρ.im⟩, hxi_ρ⟩,
          Nat.floor_le him_pos⟩
    have hρ_Z : ρ ∈ burnolUnitXiZeros m := hsub_unit hρ_unit
    have hmult_pos : ∀ w ∈ burnolUnitXiZeros m, 1 ≤ (analyticOrderAt _root_.RHTower.xi w).toNat := by
      intro w hw
      exact Nat.one_le_iff_ne_zero.mpr
        (_root_.RHTower.xi_order_toNat_ne_zero (((hZ_iff w).mp hw).2))
    have hge2 := two_le_collision_sum_of_offLine_in_band hrefl_Z hmult_pos hρ_Z
      (hinv_lt.trans_le ((min_le_left _ _).trans (le_abs_self _)))
      (by
        rw [abs_of_pos (by linarith : 0 < ρ.re - 1 / 2)]
        have := min_le_right (ρ.re - 1 / 2) (1 - ρ.re)
        linarith)
    rw [← hind_sum] at hge2
    omega
  tfae_finish

/-- **Optimal pure `Θ(√m)` Burnol unit-window Szegő positivity across all sub-exponential stages
`(S : ℝ) ≤ exp(√m)`, matching the `Ω(√T)` cumulative lower bound `firstArtifactFreePrefix_sqrt_lower_bound`.**
Under `RiemannHypothesis`, for every `m : ℕ` and every `(S : ℝ) ≤ exp(√m)`, there exists an
ellipse-avoiding stage `n_* ∈ [max S 6, max S 6 + 2 d_m²]` such that at EVERY prefix
`N ≥ burnolPrefixConst * (Nat.sqrt m + 1)`, the centered integer-theta Laurent loop satisfies
Devinatz–Widom closed-disk Szegő positivity, outer polynomial Birkhoff–Szegő factorization,
`L²(ℝ)` Wiener–Hopf invertibility, and `fredholmIndex = 0`. -/
theorem burnolUnit_subexp_sqrtPrefix_szego_of_rh (hRH : RiemannHypothesis)
    (m S : ℕ) (hS : (S : ℝ) ≤ Real.exp (Real.sqrt (m : ℝ))) :
    ∃ n_star ∈ Finset.Icc (max S 6)
      (max S 6 + 2 * (∑ w ∈ burnolUnitXiZeros m, (analyticOrderAt _root_.RHTower.xi w).toNat) ^ 2),
      ∀ N : ℕ, burnolPrefixConst * (Nat.sqrt m + 1) ≤ N →
        (∀ u : HTGeometry.UnitCircle,
          centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m) n_star N u ≠ 0) ∧
        HTGeometry.fredholmIndex
          (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m) n_star N) = 0 ∧
        IsUnit (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m) n_star N) ∧
        (∃ G H : Polynomial ℂ, IsOuterPolynomial G ∧ IsOuterPolynomial H ∧
          centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m) n_star N =
            circlePoly G * star (circlePoly H)) ∧
        (∃ F : ℂ → ℂ, IsDiskUnit F ∧
          ∀ u : HTGeometry.UnitCircle,
            0 < (F (u : ℂ) *
              centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m) n_star N u).re) := by
  obtain ⟨n_star, hn_Icc, hspec⟩ := burnolUnit_subexp_stabilization m S hS
  refine ⟨n_star, hn_Icc, fun N hN => ?_⟩
  obtain ⟨hnz, hind_sum⟩ := hspec N hN
  have hbdry := burnolUnit_bdry_regular m hN
  have hZ_iff := mem_burnolUnitXiZeros_iff m
  have hind0 :
      HTGeometry.fredholmIndex
        (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m) n_star N) = 0 := by
    rw [hind_sum, mul_eq_zero]
    right
    refine Finset.sum_eq_zero fun z hz => Finset.sum_eq_zero fun w hw => ?_
    have hz_re := xi_zero_re_eq_half_of_rh hRH (((hZ_iff z).mp hz).2)
    have hw_re := xi_zero_re_eq_half_of_rh hRH (((hZ_iff w).mp hw).2)
    have hgt1 : 1 < zhukovskyEllipseForm n_star (z - w) :=
      zhukovskyEllipseForm_gt_one_of_re_margin.1 n_star
        (by
          rw [hz_re, sub_self, abs_zero]
          exact one_div_pos.mpr (mul_pos (by norm_num) (zhukovskyStage_pos _)))
        (by
          rw [hw_re, sub_self, abs_zero]
          exact one_div_pos.mpr (mul_pos (by norm_num) (zhukovskyStage_pos _)))
    rw [if_neg (not_lt.mpr hgt1.le), mul_zero]
  have htfae := centeredTheta_szego_positivity_tfae (burnolUnitLower_le_upper m) n_star N hbdry hnz
  exact ⟨hnz, hind0, (htfae.out 1 2).mp hind0, (htfae.out 1 4).mp hind0, (htfae.out 1 5).mp hind0⟩

end GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.exists_prefix_zero_in_ball_of_xi_zero
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.logStage_sqrtPrefix_szego_iff_invLog_corridor
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.heckeDefect_log_bound_implies_szego_corridor_and_lindelof
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.heckeDefect_log_O1_implies_szego_corridor_and_lindelof
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.riemannHypothesis_door_opener_tfae
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.burnolUnit_subexp_sqrtPrefix_szego_of_rh

