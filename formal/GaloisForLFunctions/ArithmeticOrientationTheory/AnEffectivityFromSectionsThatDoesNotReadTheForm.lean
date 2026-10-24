import GaloisForLFunctions.ArithmeticOrientationTheory.TheEffectivityConeFromSections
import GaloisForLFunctions.ArithmeticOrientationTheory.NyquistRiemannRochBeyondRankNullity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceDeterminantalSectionsAndArithmeticRiemannRoch

/-!
# An Effectivity from Sections That Does Not Read the Form

This module resolves **Open Problem 8** of Arithmetic Orientation Theory (`README.md`, §7):

> **8. An effectivity from sections that does not read the form.** The section cone of §3.10 has
> the right shape — its axioms are exactly the Hodge index, it reproduces Weil over `𝔽_q` and
> fails on the golden datum — but its sections are defined by the sign of `x²`. Open: a section
> reading built from source data (node counts on the logarithmic box, the defect `E(s)`, the
> Frobenius mass) whose cone has the same calibration and whose Bézout axiom is proved without
> that sign.

## Mathematical Architecture

1. **Source Section Readings, `sourceH0`, `sourceSectionCone`, and the Sign-Free Bézout Proof (§1):**
   - For any polar surface `S : PolarSurface C` and source energy functional `Φ : C → ℝ` (defined
     without referencing `S.pair x x`), the `1 × 1` **source obstruction reading**
     `sourceObstructionReading S Φ x : Matrix (Fin 1) (Fin 1) ℂ` is `0` when `x` lies in the nef
     quadrant (`0 ≤ x · H ∧ 0 ≤ x · V`) and its polar budget `S.polar x x = 2(x · H)(x · V)` pays
     `Φ x`, and `1` otherwise.
   - Applying `h0` and `h1` from `TheNyquistRankBound` defines `sourceH0 S Φ x` and `sourceH1 S Φ x`,
     and the **source section effectivity cone** `sourceSectionCone S Φ = {x | 1 ≤ sourceH0 S Φ x}`
     coincides identically with `S.sourceCone Φ` (`sourceSectionCone_eq_sourceCone`,
     `mem_sourceSectionCone_iff`).
   - **Sign-Free Bézout Proof from Source Cauchy–Schwarz (`polar_sq_sub_polar_mul_polar`,
     `sourceSectionCone_bezout_of_defect_sq_le`):**
     For any two cycles `x, y : C`, the hyperbolic AM-GM identity
     `S.polar x y ^ 2 - S.polar x x * S.polar y y = ((x · H)(y · V) - (x · V)(y · H)) ^ 2 ≥ 0`
     holds unconditionally (`polar_sq_sub_polar_mul_polar`). Therefore, whenever `0 ≤ Φ` on
     `sourceSectionCone S Φ` and the off-diagonal defect obeys the Cauchy–Schwarz inequality
     `S.defect x y ^ 2 ≤ Φ x * Φ y`, every pair `x, y ∈ sourceSectionCone S Φ` satisfies
     `S.defect x y ^ 2 ≤ Φ x * Φ y ≤ S.polar x x * S.polar y y ≤ S.polar x y ^ 2` with
     `0 ≤ S.polar x y`, and hence `0 ≤ S.polar x y - S.defect x y = S.pair x y`
     (`sourceSectionCone_bezout_of_defect_sq_le`) — **proving `S.BezoutAxiom (sourceSectionCone S Φ)`
     without reading or assuming `0 ≤ S.pair x x`**.
   - Moreover, whenever `Φ` is a nonnegative quadratic source ledger (`∀ z, 0 ≤ Φ z` and
     `∀ z, S.defect z z = Φ z`), the discriminant of `t ↦ Φ(x + t • y) ≥ 0` yields
     `S.defect x y ^ 2 ≤ Φ x * Φ y` and hence `S.BezoutAxiom (sourceSectionCone S Φ)`
     (`sourceSectionCone_bezout_of_source_nonneg`).

2. **Frobenius-Mass and Reflected-Frobenius Section Readings over `𝔽_q` vs. `goldenDatum` (§2):**
   - For any `CurveDatum D` and finite window `W : Finset ℕ`:
     - The **Frobenius evaluation matrix** `frobEvalMatrix D W x : Matrix ι (Fin 1) ℂ` evaluates
       `frobPoly W (fun k => x.2.2 k * D.sqrtq ^ k)` at the Frobenius eigenvalues `D.β i`. Its
       Frobenius mass from `TheNyquistRankBound` is
       `frobeniusMass (frobEvalMatrix D W x) = D.frobSquareMass W (fun k => x.2.2 k * D.sqrtq ^ k) ≥ 0`
       (`frobeniusMass_frobEvalMatrix_eq_frobSquareMass`), defining `frobMassObstructionReading D W x`,
       `frobMassH0 D W x`, and `frobMassSectionCone D W`.
     - The **augmented Frobenius–Rosati evaluation matrix**
       `frobRosatiEvalMatrix D W x : Matrix (ι ⊕ ι) (Fin 1) ℂ` has Frobenius mass
       `frobeniusMass (frobRosatiEvalMatrix D W x) = D.frobSquareMass W e_x + D.frobReflectionDefect W e_x`
       (`frobeniusMass_frobRosatiEvalMatrix`), while their difference
       `frobReflectedSourceEnergy D W x = frobeniusMass (frobEvalMatrix D W x) - D.frobReflectionDefect W e_x`
       defines `frobReflectedObstructionReading D W x`, `frobReflectedH0 D W x`, and
       `frobReflectedSectionCone D W`.
   - **Sign-Free Bézout Proof over `𝔽_q` (`frobMassSectionCone_bezout_of_unitary_direct`):**
     When `D` is unitary (`∀ i, ‖D.β i‖ = 1`), `D.frobReflectionDefect W e_x = 0`, so
     `frobeniusMass (frobEvalMatrix D W z) ≥ 0` equals `(D.windowSurface W).defect z z` for all `z`,
     and `sourceSectionCone_bezout_of_source_nonneg` proves
     `(D.windowSurface W).BezoutAxiom (frobMassSectionCone D W)` directly from the nonnegativity of
     `frobeniusMass (frobEvalMatrix D W ·)` and hyperbolic AM-GM, without reading `x²`.
   - **Calibration and Refutation on `goldenDatum`:**
     - On **every** `CurveDatum D` (unitary or fake), if `frobeniusMass (frobEvalMatrix D W x) = 0`,
       then `F_{e_x}(D.β i) = 0` for all `i`, which forces `D.frobReflectionDefect W e_x = 0` and
       `(D.windowSurface W).defect x x = 0` (`defect_eq_zero_of_frobeniusMass_frobEvalMatrix_eq_zero`).
       Consequently, `(D.windowSurface W).RiemannRochAxiom (frobMassSectionCone D W)` implies
       `(D.windowSurface W).HodgeIndex` on every window `W` (`hodgeIndex_of_frobMassSectionCone_riemannRoch`).
     - On `goldenDatum.windowSurface {0, 1}`, `goldenCounterexample` has `x · H = x · V = 0` and
       `pair x x = 2 > 0`, yet `0 < frobeniusMass (frobEvalMatrix goldenDatum {0, 1} goldenCounterexample)`
       and `frobMassH0 = 0` on `±goldenCounterexample`, refuting
       `RiemannRochAxiom (frobMassSectionCone goldenDatum {0, 1})`
       (`goldenDatum_not_riemannRoch_frobMassSectionCone`), while `goldenForwardPlus` and
       `goldenForwardMinus` belong to `frobReflectedSectionCone goldenDatum {0, 1}` and collide with
       `pair goldenForwardPlus goldenForwardMinus = -6 < 0`, refuting `BezoutAxiom`
       (`goldenDatum_not_bezout_frobReflectedSectionCone`, `curve_sourceSectionCone_calibration_tfae`).

3. **Box-Node, Chebyshev-Defect `E(s)`, and `L²`-Mass Section Readings over `ℤ` (§3):**
   - **3A. The Box-Node and Chebyshev-Defect `E(s)` Section Reading (`chebyshevObstructionReading`):**
     On `scalingSubsurface (oddRealTestsAt r)` (`0 < r < R`), the source energy
     `chebyshevSourceEnergy r R x = archGaugeBudget r R F - apertureH1ChebyshevCorrection r F`
     is built purely from the archimedean gauge budget `archGaugeBudget r R F` and the lag-weighted
     integral `apertureH1ChebyshevCorrection r F = ∫_{(0, 2r]} (polarBoxDoF s - primeNodeCount s) lagDerivativeWeight F s`
     of the box degree-of-freedom minus node-count defect `E(s) = polarBoxDoF s - primeNodeCount s = e^s + s - 1 - ψ(e^s)`
     (which also equals `poleCharge F + primeNodeCorrelationObstruction r F`,
     `chebyshevSourceEnergy_eq_archGauge_sub_nodeObstruction`).
     Whenever `apertureH1ChebyshevCorrection r F ≤ archGaugeBudget r R F` on the source ledger (in
     particular unconditionally on `0 < r ≤ 181/500`), `0 ≤ chebyshevSourceEnergy r R z` for all `z`,
     and `sourceSectionCone_bezout_of_source_nonneg` proves
     `(scalingSubsurface (oddRealTestsAt r)).BezoutAxiom (chebyshevSectionCone r R)` directly by
     Cauchy–Schwarz and hyperbolic AM-GM (`chebyshevSectionCone_bezout_of_source_payment`,
     `chebyshevSectionCone_castelnuovoSeveri_of_le`).
   - **3B. Selectivity Against `shiftedPairVonMangoldt a` (`shiftedPairChebyshevSourceEnergy`):**
     Replacing the prime-power node count of `ℤ` by `shiftedPairVonMangoldt a` (`a ≠ 0`) strictly
     increases the node correlation obstruction and strictly reduces the source energy at any test
     with nonnegative prime-shift autocorrelations and `0 < autoCorrelation F (log 2)` (`r ≥ (log 2)/2`),
     separating `ℤ` from `ζ(s − a)ζ(s + a)` at the section boundary (`chebyshevSourceEnergy_shiftedPair_lt`,
     `exists_cycle_chebyshevH0_one_and_shiftedPairH0_zero`).
   - **3C. The Convex, Hecke-Stable `L²`-Mass Section Reading (`l2MassObstructionReading`):**
     On `scalingSubsurface V` (`V ≤ realTests`), the source energy `l2SourceEnergy c V (a, b, f) = c ∫ f(u)² du`
     defines `l2MassObstructionReading c V x`, `l2MassH0 c V x`, and `l2MassSectionCone c V = l2SourceCone c V`.
     For every `c ≥ 0`, `L²` Cauchy–Schwarz + hyperbolic AM-GM proves the sign-free source Bézout
     bound `c * ∫ f(u) g(u) du ≤ (scalingSubsurface V).polar x y` for all `x, y ∈ l2MassSectionCone c V`
     (`l2SourcePairing_le_polar_of_mem_l2MassSectionCone`), while `l2MassSectionCone c V` satisfies
     `AmpleAxiom`, `RiemannRochAxiom`, and `SurfaceRiemannRochAxiom 0 0` unconditionally on
     `primitiveSmoothRealTestsAt r` (`r ≤ ½(log 2 + 1/50)`, `0 < c ≤ 1/1000`),
     `polarFreeSmoothRealTestsAt r` (`r ≤ ½(log 2 + 1/50)`, `0 < c ≤ 1/20`),
     `oddRealTestsAt r` (`r ≤ 181/500`, `0 < c ≤ 1/1000`), and `realTestsAt a` (`a ≤ 3/10`, `0 < c ≤ 1/5000`),
     and across all apertures `chebyshevSectionCone_widthDictionary_tfae` unites the source section
     cones with every unit of the width dictionary.
-/

open Complex Matrix Finset Set MeasureTheory
open scoped BigOperators ComplexConjugate
open Zeta23 RHTower
  GaloisForLFunctions.ArithmeticCastelnuovoSeveri
  GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticIncidencePositivity
  GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
  GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions
namespace ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

variable {C : Type*} [AddCommGroup C] [Module ℝ C]

/-! ## §1. Source Section Readings, `sourceH0`, `sourceSectionCone`, and the Sign-Free Bézout Proof -/

/-- The `1 × 1` **source obstruction reading** on a polar surface `S` associated to a source energy
functional `Φ : C → ℝ`: the reading is `0` when `x` lies in the nef quadrant (`0 ≤ x · H ∧ 0 ≤ x · V`)
and its polar budget `S.polar x x = 2(x · H)(x · V)` pays `Φ x`, and is `1` otherwise.
Unlike `cycleObstructionReading`, this definition never references `S.pair x x` or `S.defect x x`. -/
def sourceObstructionReading (S : PolarSurface C) (Φ : C → ℝ) (x : C) : Matrix (Fin 1) (Fin 1) ℂ :=
  open Classical in
  if 0 ≤ S.pair x S.H ∧ 0 ≤ S.pair x S.V ∧ Φ x ≤ S.polar x x then 0 else 1

/-- The **source section count** `h⁰_Φ(x)` obtained by applying `h0` from `TheNyquistRankBound` to
`sourceObstructionReading S Φ x`. -/
def sourceH0 (S : PolarSurface C) (Φ : C → ℝ) (x : C) : ℕ :=
  h0 (sourceObstructionReading S Φ x)

/-- The **source obstruction count** `h¹_Φ(x)` obtained by applying `h1` from `TheNyquistRankBound`
to `sourceObstructionReading S Φ x`. -/
def sourceH1 (S : PolarSurface C) (Φ : C → ℝ) (x : C) : ℕ :=
  h1 (sourceObstructionReading S Φ x)

/-- **The source section effectivity cone:** `sourceSectionCone S Φ = {x : C | 1 ≤ sourceH0 S Φ x}`. -/
def sourceSectionCone (S : PolarSurface C) (Φ : C → ℝ) : Set C :=
  {x : C | 1 ≤ sourceH0 S Φ x}

/-- `sourceH0 S Φ x = 1` when `0 ≤ x · H ∧ 0 ≤ x · V ∧ Φ x ≤ S.polar x x`, and `0` otherwise. -/
theorem sourceH0_eq_ite (S : PolarSurface C) (Φ : C → ℝ) (x : C) :
    sourceH0 S Φ x =
      (open Classical in if 0 ≤ S.pair x S.H ∧ 0 ≤ S.pair x S.V ∧ Φ x ≤ S.polar x x then 1 else 0) := by
  classical
  unfold sourceH0 sourceObstructionReading
  split_ifs
  · exact h0_zero_fin_one
  · exact h0_one_fin_one

/-- A cycle `x` has `1 ≤ sourceH0 S Φ x` iff `0 ≤ x · H ∧ 0 ≤ x · V ∧ Φ x ≤ S.polar x x`. -/
theorem one_le_sourceH0_iff (S : PolarSurface C) (Φ : C → ℝ) (x : C) :
    1 ≤ sourceH0 S Φ x ↔ 0 ≤ S.pair x S.H ∧ 0 ≤ S.pair x S.V ∧ Φ x ≤ S.polar x x := by
  classical
  rw [sourceH0_eq_ite]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => le_rfl⟩
  · exact ⟨fun h1 => absurd h1 (by omega), fun h' => absurd h' h⟩

/-- Explicit characterization of membership in `sourceSectionCone S Φ`. -/
theorem mem_sourceSectionCone_iff (S : PolarSurface C) (Φ : C → ℝ) (x : C) :
    x ∈ sourceSectionCone S Φ ↔ 0 ≤ S.pair x S.H ∧ 0 ≤ S.pair x S.V ∧ Φ x ≤ S.polar x x :=
  one_le_sourceH0_iff S Φ x

/-- **Identification with `S.sourceCone Φ`:** the section cone `{x | 1 ≤ sourceH0 S Φ x}` defined
via `h0` from `TheNyquistRankBound` coincides identically with the determinantal source cone
`S.sourceCone Φ = {x | (S.sourceSections Φ x).Nonempty}`. -/
theorem sourceSectionCone_eq_sourceCone (S : PolarSurface C) (Φ : C → ℝ) :
    sourceSectionCone S Φ = S.sourceCone Φ := by
  ext x
  rw [mem_sourceSectionCone_iff, S.mem_sourceCone_iff]

/-- Whenever `Φ` agrees with `S.defect x x` (`∀ x, Φ x = S.defect x x`), `sourceSectionCone S Φ`
coincides identically with `sectionEffectivityCone S`. -/
theorem sourceSectionCone_eq_sectionEffectivityCone_of_eq_defect (S : PolarSurface C) (Φ : C → ℝ)
    (heq : ∀ x : C, Φ x = S.defect x x) :
    sourceSectionCone S Φ = sectionEffectivityCone S := by
  ext x
  rw [mem_sourceSectionCone_iff, mem_sectionEffectivityCone_iff_defect_le_polar, heq x]

/-- **Universal Hyperbolic AM-GM Identity on a Polar Surface (`polar_sq_sub_polar_mul_polar`):**
For any two cycles `x, y : C` (without any positivity or Hodge-index hypothesis),
`S.polar x y ^ 2 - S.polar x x * S.polar y y = ((x · H)(y · V) - (x · V)(y · H)) ^ 2 ≥ 0`,
and in particular `S.polar x x * S.polar y y ≤ S.polar x y ^ 2`. -/
theorem polar_sq_sub_polar_mul_polar (S : PolarSurface C) (x y : C) :
    S.polar x y ^ 2 - S.polar x x * S.polar y y =
      (S.pair x S.H * S.pair y S.V - S.pair x S.V * S.pair y S.H) ^ 2 ∧
    S.polar x x * S.polar y y ≤ S.polar x y ^ 2 := by
  have hid : S.polar x y ^ 2 - S.polar x x * S.polar y y =
      (S.pair x S.H * S.pair y S.V - S.pair x S.V * S.pair y S.H) ^ 2 := by
    simp only [PolarSurface.polar]
    ring
  refine ⟨hid, ?_⟩
  have hnn : 0 ≤ (S.pair x S.H * S.pair y S.V - S.pair x S.V * S.pair y S.H) ^ 2 := sq_nonneg _
  linarith

/-- **Sign-Free Bézout Theorem from Source Cauchy–Schwarz (`sourceSectionCone_bezout_of_defect_sq_le`):**
If `Φ : C → ℝ` is nonnegative on `sourceSectionCone S Φ` and satisfies the off-diagonal
Cauchy–Schwarz inequality `S.defect x y ^ 2 ≤ Φ x * Φ y` for all `x, y ∈ sourceSectionCone S Φ`,
then `S.BezoutAxiom (sourceSectionCone S Φ)` holds directly from hyperbolic AM-GM
(`polar_sq_sub_polar_mul_polar`), **without reading or assuming `0 ≤ S.pair x x` or `S.HodgeIndex`**. -/
theorem sourceSectionCone_bezout_of_defect_sq_le (S : PolarSurface C) (Φ : C → ℝ)
    (hnonneg : ∀ x ∈ sourceSectionCone S Φ, 0 ≤ Φ x)
    (hcs : ∀ x ∈ sourceSectionCone S Φ, ∀ y ∈ sourceSectionCone S Φ,
      S.defect x y ^ 2 ≤ Φ x * Φ y) :
    S.BezoutAxiom (sourceSectionCone S Φ) := by
  intro x hx y hy
  have hΦx : 0 ≤ Φ x := hnonneg x hx
  have hΦy : 0 ≤ Φ y := hnonneg y hy
  have hcs_xy : S.defect x y ^ 2 ≤ Φ x * Φ y := hcs x hx y hy
  rw [mem_sourceSectionCone_iff] at hx hy
  rcases hx with ⟨hxH, hxV, hxP⟩
  rcases hy with ⟨hyH, hyV, hyP⟩
  have hpol_xy_nonneg : 0 ≤ S.polar x y := by
    unfold PolarSurface.polar
    positivity
  have hmul : Φ x * Φ y ≤ S.polar x x * S.polar y y :=
    mul_le_mul hxP hyP hΦy (hΦx.trans hxP)
  have hamgm : S.polar x x * S.polar y y ≤ S.polar x y ^ 2 :=
    (polar_sq_sub_polar_mul_polar S x y).2
  have hsq : S.defect x y ^ 2 ≤ S.polar x y ^ 2 := (hcs_xy.trans hmul).trans hamgm
  have hdef_le : S.defect x y ≤ S.polar x y := by
    by_contra hgt
    push Not at hgt
    nlinarith [lt_of_le_of_lt hpol_xy_nonneg hgt]
  have hp : S.pair x y = S.polar x y - S.defect x y := by
    unfold PolarSurface.defect
    ring
  linarith

/-- **Off-diagonal Cauchy–Schwarz and Sign-Free Bézout for Any Nonnegative Source Ledger:**
If a source functional `Φ : C → ℝ` represents the diagonal of `S.defect` (`∀ z, S.defect z z = Φ z`)
and is nonnegative on the source side (`∀ z, 0 ≤ Φ z`), then:
1. For all `x, y : C`, the quadratic discriminant of `t ↦ Φ(x + t • y) ≥ 0` yields
   `S.defect x y ^ 2 ≤ Φ x * Φ y`;
2. By `sourceSectionCone_bezout_of_defect_sq_le`, `S.BezoutAxiom (sourceSectionCone S Φ)` holds! -/
theorem sourceSectionCone_bezout_of_source_nonneg (S : PolarSurface C) (Φ : C → ℝ)
    (hrep : ∀ z : C, S.defect z z = Φ z) (hnonneg : ∀ z : C, 0 ≤ Φ z) :
    (∀ x y : C, S.defect x y ^ 2 ≤ Φ x * Φ y) ∧
      S.BezoutAxiom (sourceSectionCone S Φ) := by
  have hcs : ∀ x y : C, S.defect x y ^ 2 ≤ Φ x * Φ y := fun x y => by
    have hq : ∀ t : ℝ, 0 ≤ Φ y * (t * t) + 2 * S.defect x y * t + Φ x := fun t => by
      have h1 : 0 ≤ Φ (x + t • y) := hnonneg (x + t • y)
      have h2 : Φ (x + t • y) = Φ y * (t * t) + 2 * S.defect x y * t + Φ x := by
        rw [← hrep (x + t • y), ← hrep x, ← hrep y]
        simp only [PolarSurface.defect, PolarSurface.polar, map_add, map_smul,
          LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, S.pair_comm y x]
        ring
      rwa [h2] at h1
    have hd := discrim_le_zero hq
    rw [discrim] at hd
    nlinarith [hd]
  exact ⟨hcs, sourceSectionCone_bezout_of_defect_sq_le S Φ (fun x _ => hnonneg x)
    (fun x _ y _ => hcs x y)⟩

/-! ## §2. Frobenius-Mass and Reflected-Frobenius Section Readings over `𝔽_q` vs. `goldenDatum` -/

section CurveSourceReadings

variable {ι : Type*} [Fintype ι]

/-- The **Frobenius evaluation matrix (`frobEvalMatrix`)** of a span cycle `x : SpanCycle` on a
window `W : Finset ℕ`: the `|ι| × 1` matrix whose `(i, 0)`-entry is the Frobenius polynomial
`frobPoly W (fun k => x.2.2 k * D.sqrtq ^ k) (D.β i)`. -/
def frobEvalMatrix (D : CurveDatum ι) (W : Finset ℕ) (x : SpanCycle) : Matrix ι (Fin 1) ℂ :=
  fun i _ => frobPoly W (fun k => x.2.2 k * D.sqrtq ^ k) (D.β i)

/-- The **Frobenius mass** (`frobeniusMass` from `TheNyquistRankBound`) of `frobEvalMatrix D W x`
equals the Frobenius square-sampling mass `D.frobSquareMass W (fun k => x.2.2 k * D.sqrtq ^ k)`. -/
theorem frobeniusMass_frobEvalMatrix_eq_frobSquareMass (D : CurveDatum ι) (W : Finset ℕ)
    (x : SpanCycle) :
    frobeniusMass (frobEvalMatrix D W x) =
      D.frobSquareMass W (fun k => x.2.2 k * D.sqrtq ^ k) := by
  unfold frobeniusMass frobEvalMatrix CurveDatum.frobSquareMass
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]

/-- The **augmented Frobenius–Rosati evaluation matrix (`frobRosatiEvalMatrix`)** of a span cycle
`x`, recording both `F_{e_x}(D.β i)` and `(1/√2)(F_{e_x}(D.β i) - F_{e_x}(D.β (D.reflPerm i)))`. -/
def frobRosatiEvalMatrix (D : CurveDatum ι) (W : Finset ℕ) (x : SpanCycle) :
    Matrix (ι ⊕ ι) (Fin 1) ℂ :=
  fun s _ =>
    match s with
    | Sum.inl i => frobPoly W (fun k => x.2.2 k * D.sqrtq ^ k) (D.β i)
    | Sum.inr i => ((1 / Real.sqrt 2 : ℝ) : ℂ) *
        (frobPoly W (fun k => x.2.2 k * D.sqrtq ^ k) (D.β i) -
          frobPoly W (fun k => x.2.2 k * D.sqrtq ^ k) (D.β (D.reflPerm i)))

/-- The Frobenius mass of `frobRosatiEvalMatrix D W x` is the sum of `D.frobSquareMass` and
`D.frobReflectionDefect`. -/
theorem frobeniusMass_frobRosatiEvalMatrix (D : CurveDatum ι) (W : Finset ℕ) (x : SpanCycle) :
    frobeniusMass (frobRosatiEvalMatrix D W x) =
      D.frobSquareMass W (fun k => x.2.2 k * D.sqrtq ^ k) +
        D.frobReflectionDefect W (fun k => x.2.2 k * D.sqrtq ^ k) := by
  unfold frobeniusMass frobRosatiEvalMatrix CurveDatum.frobSquareMass
    CurveDatum.frobReflectionDefect
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Fintype.sum_sum_type]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, div_pow, one_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The **pure Frobenius-mass source energy** on `D.windowSurface W`:
`frobMassSourceEnergy D W x = frobeniusMass (frobEvalMatrix D W x) ≥ 0`. -/
def frobMassSourceEnergy (D : CurveDatum ι) (W : Finset ℕ) (x : SpanCycle) : ℝ :=
  frobeniusMass (frobEvalMatrix D W x)

/-- The `1 × 1` **Frobenius-mass obstruction reading** on `D.windowSurface W`. -/
def frobMassObstructionReading (D : CurveDatum ι) (W : Finset ℕ) (x : SpanCycle) :
    Matrix (Fin 1) (Fin 1) ℂ :=
  sourceObstructionReading (D.windowSurface W) (frobMassSourceEnergy D W) x

/-- The **Frobenius-mass section count** `frobMassH0 D W x = h0 (frobMassObstructionReading D W x)`. -/
def frobMassH0 (D : CurveDatum ι) (W : Finset ℕ) (x : SpanCycle) : ℕ :=
  sourceH0 (D.windowSurface W) (frobMassSourceEnergy D W) x

/-- The **Frobenius-mass section effectivity cone**
`frobMassSectionCone D W = {x | 1 ≤ frobMassH0 D W x}`. -/
def frobMassSectionCone (D : CurveDatum ι) (W : Finset ℕ) : Set SpanCycle :=
  sourceSectionCone (D.windowSurface W) (frobMassSourceEnergy D W)

/-- The **reflected-Frobenius source energy** on `D.windowSurface W`:
`frobReflectedSourceEnergy D W x = 2 * frobeniusMass (frobEvalMatrix D W x) - frobeniusMass (frobRosatiEvalMatrix D W x) = frobeniusMass (frobEvalMatrix D W x) - D.frobReflectionDefect W e_x`. -/
def frobReflectedSourceEnergy (D : CurveDatum ι) (W : Finset ℕ) (x : SpanCycle) : ℝ :=
  frobeniusMass (frobEvalMatrix D W x) -
    D.frobReflectionDefect W (fun k => x.2.2 k * D.sqrtq ^ k)

/-- The `1 × 1` **reflected-Frobenius obstruction reading** on `D.windowSurface W`. -/
def frobReflectedObstructionReading (D : CurveDatum ι) (W : Finset ℕ) (x : SpanCycle) :
    Matrix (Fin 1) (Fin 1) ℂ :=
  sourceObstructionReading (D.windowSurface W) (frobReflectedSourceEnergy D W) x

/-- The **reflected-Frobenius section count** `frobReflectedH0 D W x`. -/
def frobReflectedH0 (D : CurveDatum ι) (W : Finset ℕ) (x : SpanCycle) : ℕ :=
  sourceH0 (D.windowSurface W) (frobReflectedSourceEnergy D W) x

/-- The **reflected-Frobenius section effectivity cone**
`frobReflectedSectionCone D W = {x | 1 ≤ frobReflectedH0 D W x}`. -/
def frobReflectedSectionCone (D : CurveDatum ι) (W : Finset ℕ) : Set SpanCycle :=
  sourceSectionCone (D.windowSurface W) (frobReflectedSourceEnergy D W)

/-- On every `CurveDatum D` (unitary or fake), `frobMassSourceEnergy D W x ≥ 0` and
`(D.windowSurface W).defect x x = frobReflectedSourceEnergy D W x ≤ frobMassSourceEnergy D W x`. -/
theorem defect_eq_frobReflected_and_le_frobMass (D : CurveDatum ι) (W : Finset ℕ) (x : SpanCycle) :
    0 ≤ frobMassSourceEnergy D W x ∧
      (D.windowSurface W).defect x x = frobReflectedSourceEnergy D W x ∧
      (D.windowSurface W).defect x x ≤ frobMassSourceEnergy D W x := by
  have hnn : 0 ≤ frobMassSourceEnergy D W x := by
    unfold frobMassSourceEnergy
    rw [frobeniusMass_frobEvalMatrix_eq_frobSquareMass]
    exact D.frobSquareMass_nonneg W _
  have heq : (D.windowSurface W).defect x x = frobReflectedSourceEnergy D W x := by
    unfold frobReflectedSourceEnergy
    rw [frobeniusMass_frobEvalMatrix_eq_frobSquareMass,
      D.windowSurface_defect_eq_frobSquareMass_sub_frobReflectionDefect]
  have hdef : 0 ≤ D.frobReflectionDefect W (fun k => x.2.2 k * D.sqrtq ^ k) :=
    D.frobReflectionDefect_nonneg W _
  refine ⟨hnn, heq, ?_⟩
  unfold frobMassSourceEnergy frobReflectedSourceEnergy at *
  linarith

/-- On every `CurveDatum D`, `frobReflectedSectionCone D W = sectionEffectivityCone (D.windowSurface W)`
and `frobMassSectionCone D W ⊆ frobReflectedSectionCone D W`. -/
theorem frobMassSectionCone_subset_frobReflectedSectionCone (D : CurveDatum ι) (W : Finset ℕ) :
    frobReflectedSectionCone D W = sectionEffectivityCone (D.windowSurface W) ∧
      frobMassSectionCone D W ⊆ frobReflectedSectionCone D W := by
  have heq : frobReflectedSectionCone D W = sectionEffectivityCone (D.windowSurface W) :=
    sourceSectionCone_eq_sectionEffectivityCone_of_eq_defect (D.windowSurface W)
      (frobReflectedSourceEnergy D W) (fun x => (defect_eq_frobReflected_and_le_frobMass D W x).2.1.symm)
  refine ⟨heq, fun x hx => ?_⟩
  rw [frobMassSectionCone, mem_sourceSectionCone_iff] at hx
  rw [frobReflectedSectionCone, mem_sourceSectionCone_iff]
  have hle := (defect_eq_frobReflected_and_le_frobMass D W x).2
  exact ⟨hx.1, hx.2.1, by linarith⟩

/-- **Zero Frobenius Mass Forces Zero Defect on Every `CurveDatum`:**
If `frobeniusMass (frobEvalMatrix D W x) = 0`, then `frobPoly W e_x (D.β i) = 0` for all `i : ι`,
hence `D.frobReflectionDefect W e_x = 0` and `(D.windowSurface W).defect x x = 0`. -/
theorem defect_eq_zero_of_frobeniusMass_frobEvalMatrix_eq_zero (D : CurveDatum ι) (W : Finset ℕ)
    {x : SpanCycle} (h0 : frobeniusMass (frobEvalMatrix D W x) = 0) :
    (D.windowSurface W).defect x x = 0 := by
  set e : ℕ → ℝ := fun k => x.2.2 k * D.sqrtq ^ k
  rw [frobeniusMass_frobEvalMatrix_eq_frobSquareMass] at h0
  unfold CurveDatum.frobSquareMass at h0
  have hall : ∀ i : ι, frobPoly W e (D.β i) = 0 := fun i => by
    have hsq := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖frobPoly W e (D.β j)‖)).mp
      h0 i (Finset.mem_univ i)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  have hrefl : D.frobReflectionDefect W e = 0 := by
    unfold CurveDatum.frobReflectionDefect
    rw [Finset.sum_eq_zero (fun i _ => by rw [hall i, hall (D.reflPerm i), sub_self, norm_zero, sq, mul_zero]),
      mul_zero]
  rw [D.windowSurface_defect_eq_frobSquareMass_sub_frobReflectionDefect,
    show D.frobSquareMass W e = 0 from h0, hrefl, sub_zero]

/-- **Universal Riemann–Roch to Hodge-Index Implication for `frobMassSectionCone`:**
On **every** `CurveDatum D` and window `W` (without assuming unitarity), if `frobMassSectionCone D W`
satisfies `RiemannRochAxiom`, then `(D.windowSurface W).HodgeIndex` holds. -/
theorem hodgeIndex_of_frobMassSectionCone_riemannRoch (D : CurveDatum ι) (W : Finset ℕ)
    (hRR : (D.windowSurface W).RiemannRochAxiom (frobMassSectionCone D W)) :
    (D.windowSurface W).HodgeIndex := by
  intro x hxH hxV
  by_contra hpos
  push Not at hpos
  have hpol0 : (D.windowSurface W).polar x x = 0 := by
    rw [(D.windowSurface W).polar_self, hxH, mul_zero, zero_mul]
  have hfrob_neg : frobMassSourceEnergy D W (-x) = frobMassSourceEnergy D W x := by
    unfold frobMassSourceEnergy
    rw [frobeniusMass_frobEvalMatrix_eq_frobSquareMass,
      frobeniusMass_frobEvalMatrix_eq_frobSquareMass]
    unfold CurveDatum.frobSquareMass frobPoly
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsum : (∑ k ∈ W, (((-x).2.2 k * D.sqrtq ^ k : ℝ) : ℂ) * D.β i ^ k) =
        -(∑ k ∈ W, ((x.2.2 k * D.sqrtq ^ k : ℝ) : ℂ) * D.β i ^ k) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      change (((-x.2.2 k) * D.sqrtq ^ k : ℝ) : ℂ) * D.β i ^ k = _
      push_cast
      ring
    rw [hsum, norm_neg]
  have hmass0 : frobeniusMass (frobEvalMatrix D W x) = 0 := by
    rcases hRR x hpos with hx | hnx
    · rw [frobMassSectionCone, mem_sourceSectionCone_iff, hpol0] at hx
      exact le_antisymm hx.2.2 (defect_eq_frobReflected_and_le_frobMass D W x).1
    · rw [frobMassSectionCone, mem_sourceSectionCone_iff,
        (D.windowSurface W).polar_neg_self, hpol0, hfrob_neg] at hnx
      exact le_antisymm hnx.2.2 (defect_eq_frobReflected_and_le_frobMass D W x).1
  have hdef0 := defect_eq_zero_of_frobeniusMass_frobEvalMatrix_eq_zero D W hmass0
  have hpair0 : (D.windowSurface W).pair x x = 0 := by
    have hd : (D.windowSurface W).defect x x =
        (D.windowSurface W).polar x x - (D.windowSurface W).pair x x := rfl
    linarith
  linarith

/-- **Sign-Free Bézout Proof for `frobMassSectionCone D W` over `𝔽_q` (`∀ i, ‖D.β i‖ = 1`):**
For any unitary curve datum `D`, `D.frobReflectionDefect W e = 0`, so `frobMassSourceEnergy D W z ≥ 0`
equals `(D.windowSurface W).defect z z`, and `sourceSectionCone_bezout_of_source_nonneg` proves
`(D.windowSurface W).BezoutAxiom (frobMassSectionCone D W)` directly from Cauchy–Schwarz on
`frobMassSourceEnergy` and hyperbolic AM-GM, without reading `x²`. -/
theorem frobMassSectionCone_bezout_and_eq_of_unitary (D : CurveDatum ι)
    (hβ : ∀ i : ι, ‖D.β i‖ = 1) (W : Finset ℕ) :
    (∀ x : SpanCycle, D.frobReflectionDefect W (fun k => x.2.2 k * D.sqrtq ^ k) = 0) ∧
      (∀ x : SpanCycle, (D.windowSurface W).defect x x = frobMassSourceEnergy D W x) ∧
      frobMassSectionCone D W = frobReflectedSectionCone D W ∧
      frobMassSectionCone D W = sectionEffectivityCone (D.windowSurface W) ∧
      (∀ x y : SpanCycle,
        (D.windowSurface W).defect x y ^ 2 ≤ frobMassSourceEnergy D W x * frobMassSourceEnergy D W y) ∧
      (D.windowSurface W).BezoutAxiom (frobMassSectionCone D W) := by
  have hrefl0 : ∀ x : SpanCycle, D.frobReflectionDefect W (fun k => x.2.2 k * D.sqrtq ^ k) = 0 := by
    intro x
    unfold CurveDatum.frobReflectionDefect
    rw [Finset.sum_eq_zero (fun i _ => ?_), mul_zero]
    rw [(D.norm_β_eq_one_iff_β_reflPerm_eq i).mp (hβ i), sub_self, norm_zero, sq, mul_zero]
  have hrep : ∀ x : SpanCycle, (D.windowSurface W).defect x x = frobMassSourceEnergy D W x := by
    intro x
    rw [(defect_eq_frobReflected_and_le_frobMass D W x).2.1]
    unfold frobReflectedSourceEnergy frobMassSourceEnergy
    rw [hrefl0 x, sub_zero]
  have heq_sec : frobMassSectionCone D W = sectionEffectivityCone (D.windowSurface W) :=
    sourceSectionCone_eq_sectionEffectivityCone_of_eq_defect (D.windowSurface W)
      (frobMassSourceEnergy D W) (fun x => (hrep x).symm)
  have heq_refl : frobMassSectionCone D W = frobReflectedSectionCone D W :=
    heq_sec.trans (frobMassSectionCone_subset_frobReflectedSectionCone D W).1.symm
  have hbez := sourceSectionCone_bezout_of_source_nonneg (D.windowSurface W)
    (frobMassSourceEnergy D W) hrep (fun x => (defect_eq_frobReflected_and_le_frobMass D W x).1)
  exact ⟨hrefl0, hrep, heq_refl, heq_sec, hbez.1, hbez.2⟩

/-- **Refutation on `goldenDatum` (`W = {0, 1}`):**
1. On `goldenDatum.windowSurface {0, 1}`, `goldenCounterexample` has `x · H = 0`, `x · V = 0`, and
   `pair x x = 2 > 0`, yet `0 < frobeniusMass (frobEvalMatrix goldenDatum {0, 1} goldenCounterexample)`
   and `frobMassH0 = 0` on both `±goldenCounterexample`, so
   `¬ (goldenDatum.windowSurface {0, 1}).RiemannRochAxiom (frobMassSectionCone goldenDatum {0, 1})`;
2. On `frobReflectedSectionCone goldenDatum {0, 1}`, both `goldenForwardPlus` and `goldenForwardMinus`
   have `frobReflectedH0 = 1`, yet `pair goldenForwardPlus goldenForwardMinus = -6 < 0`, so both
   `BezoutAxiom` and `RiemannRochAxiom` fail. -/
theorem goldenDatum_refutes_frobMass_and_frobReflected :
    0 < frobeniusMass (frobEvalMatrix goldenDatum ({0, 1} : Finset ℕ) goldenCounterexample) ∧
      frobMassH0 goldenDatum ({0, 1} : Finset ℕ) goldenCounterexample = 0 ∧
      frobMassH0 goldenDatum ({0, 1} : Finset ℕ) (-goldenCounterexample) = 0 ∧
      ¬ (goldenDatum.windowSurface ({0, 1} : Finset ℕ)).RiemannRochAxiom
          (frobMassSectionCone goldenDatum ({0, 1} : Finset ℕ)) ∧
      1 ≤ frobReflectedH0 goldenDatum ({0, 1} : Finset ℕ) goldenForwardPlus ∧
      1 ≤ frobReflectedH0 goldenDatum ({0, 1} : Finset ℕ) goldenForwardMinus ∧
      ¬ (goldenDatum.windowSurface ({0, 1} : Finset ℕ)).BezoutAxiom
          (frobReflectedSectionCone goldenDatum ({0, 1} : Finset ℕ)) ∧
      ¬ (goldenDatum.windowSurface ({0, 1} : Finset ℕ)).RiemannRochAxiom
          (frobReflectedSectionCone goldenDatum ({0, 1} : Finset ℕ)) := by
  set W : Finset ℕ := {0, 1}
  obtain ⟨hH0, hV0, hxx⟩ := goldenCounterexample_violates_hodgeIndex
  have hnot_HI : ¬ (goldenDatum.windowSurface W).HodgeIndex := by
    intro hHI
    have hle := hHI goldenCounterexample hH0 hV0
    linarith
  have hnot_RR_mass : ¬ (goldenDatum.windowSurface W).RiemannRochAxiom
      (frobMassSectionCone goldenDatum W) :=
    fun hRR => hnot_HI (hodgeIndex_of_frobMassSectionCone_riemannRoch goldenDatum W hRR)
  have hpos_mass : 0 < frobeniusMass (frobEvalMatrix goldenDatum W goldenCounterexample) := by
    have hnn := (defect_eq_frobReflected_and_le_frobMass goldenDatum W goldenCounterexample).1
    unfold frobMassSourceEnergy at hnn
    refine lt_of_le_of_ne hnn fun h0 => ?_
    have hdef0 := defect_eq_zero_of_frobeniusMass_frobEvalMatrix_eq_zero goldenDatum W h0.symm
    have hpol0 : (goldenDatum.windowSurface W).polar goldenCounterexample goldenCounterexample = 0 := by
      rw [(goldenDatum.windowSurface W).polar_self, hH0, mul_zero, zero_mul]
    have hd : (goldenDatum.windowSurface W).defect goldenCounterexample goldenCounterexample =
        (goldenDatum.windowSurface W).polar goldenCounterexample goldenCounterexample -
          (goldenDatum.windowSurface W).pair goldenCounterexample goldenCounterexample := rfl
    linarith
  have hh0_pos : frobMassH0 goldenDatum W goldenCounterexample = 0 := by
    by_contra hne
    have h1 : 1 ≤ frobMassH0 goldenDatum W goldenCounterexample := by omega
    rw [frobMassH0, one_le_sourceH0_iff, (goldenDatum.windowSurface W).polar_self, hH0,
      mul_zero, zero_mul] at h1
    unfold frobMassSourceEnergy at h1
    linarith [h1.2.2]
  have hh0_neg : frobMassH0 goldenDatum W (-goldenCounterexample) = 0 := by
    by_contra hne
    have h1 : 1 ≤ frobMassH0 goldenDatum W (-goldenCounterexample) := by omega
    have hnot : goldenCounterexample ∈ frobMassSectionCone goldenDatum W ∨
        -goldenCounterexample ∈ frobMassSectionCone goldenDatum W := Or.inr h1
    rw [frobMassH0, one_le_sourceH0_iff, (goldenDatum.windowSurface W).polar_neg_self,
      (goldenDatum.windowSurface W).polar_self, hH0, mul_zero, zero_mul] at h1
    have hmass0 : frobeniusMass (frobEvalMatrix goldenDatum W (-goldenCounterexample)) = 0 :=
      le_antisymm h1.2.2 (defect_eq_frobReflected_and_le_frobMass goldenDatum W (-goldenCounterexample)).1
    have hdef0 := defect_eq_zero_of_frobeniusMass_frobEvalMatrix_eq_zero goldenDatum W hmass0
    rw [(goldenDatum.windowSurface W).defect_neg_self] at hdef0
    have hpol0 : (goldenDatum.windowSurface W).polar goldenCounterexample goldenCounterexample = 0 := by
      rw [(goldenDatum.windowSurface W).polar_self, hH0, mul_zero, zero_mul]
    have hd : (goldenDatum.windowSurface W).defect goldenCounterexample goldenCounterexample =
        (goldenDatum.windowSurface W).polar goldenCounterexample goldenCounterexample -
          (goldenDatum.windowSurface W).pair goldenCounterexample goldenCounterexample := rfl
    linarith
  have heq_refl := (frobMassSectionCone_subset_frobReflectedSectionCone goldenDatum W).1
  have hplus_mem : 1 ≤ frobReflectedH0 goldenDatum W goldenForwardPlus := by
    change goldenForwardPlus ∈ frobReflectedSectionCone goldenDatum W
    rw [heq_refl]
    exact goldenForwardPlus_mem_sectionEffectivityCone
  have hminus_mem : 1 ≤ frobReflectedH0 goldenDatum W goldenForwardMinus := by
    change goldenForwardMinus ∈ frobReflectedSectionCone goldenDatum W
    rw [heq_refl]
    exact goldenForwardMinus_mem_sectionEffectivityCone
  have hrefute := goldenDatum_not_bezout_sectionEffectivityCone
  rw [← heq_refl] at hrefute
  exact ⟨hpos_mass, hh0_pos, hh0_neg, hnot_RR_mass, hplus_mem, hminus_mem, hrefute.1, hrefute.2⟩

/-- **Complete Calibration Equivalence over `CurveDatum` (`curve_sourceSectionCone_calibration_tfae`):**
For any curve datum `D : CurveDatum ι`, the following are unconditionally equivalent:
1. `∀ W, (D.windowSurface W).RiemannRochAxiom (frobMassSectionCone D W)`;
2. `∀ W, (D.windowSurface W).BezoutAxiom (frobReflectedSectionCone D W)`;
3. `∀ W, (D.windowSurface W).RiemannRochAxiom (frobReflectedSectionCone D W)`;
4. `∀ W, (D.windowSurface W).HodgeIndex`;
5. `∀ i : ι, ‖D.β i‖ = 1` (unitarity / Weil RH for the curve);
6. `∃ B : ℝ, ∀ k : ℕ, |D.trace k| ≤ B` (the Hasse–Weil bound). -/
theorem curve_sourceSectionCone_calibration_tfae (D : CurveDatum ι) :
    List.TFAE [
      ∀ W : Finset ℕ, (D.windowSurface W).RiemannRochAxiom (frobMassSectionCone D W),
      ∀ W : Finset ℕ, (D.windowSurface W).BezoutAxiom (frobReflectedSectionCone D W),
      ∀ W : Finset ℕ, (D.windowSurface W).RiemannRochAxiom (frobReflectedSectionCone D W),
      ∀ W : Finset ℕ, (D.windowSurface W).HodgeIndex,
      ∀ i : ι, ‖D.β i‖ = 1,
      ∃ B : ℝ, ∀ k : ℕ, |D.trace k| ≤ B] := by
  have heq : ∀ W : Finset ℕ, frobReflectedSectionCone D W = sectionEffectivityCone (D.windowSurface W) :=
    fun W => (frobMassSectionCone_subset_frobReflectedSectionCone D W).1
  tfae_have 1 → 4 := fun h W => hodgeIndex_of_frobMassSectionCone_riemannRoch D W (h W)
  tfae_have 5 → 1 := fun hβ W => by
    rw [(frobMassSectionCone_bezout_and_eq_of_unitary D hβ W).2.2.2.1]
    exact (curve_unitary_sectionEffectivityCone_castelnuovoSeveri D hβ W).2.2
  tfae_have 2 ↔ 4 := forall_congr' fun W => by
    rw [heq W]
    exact sectionEffectivityCone_bezout_iff_hodgeIndex (D.windowSurface W)
  tfae_have 3 ↔ 4 := forall_congr' fun W => by
    rw [heq W]
    exact sectionEffectivityCone_riemannRoch_iff_hodgeIndex (D.windowSurface W)
  tfae_have 4 ↔ 5 := D.windowSurface_hodgeIndex_iff_unitary
  tfae_have 5 ↔ 6 := (D.forcing_arithmetic_data_tfae).out 1 7
  tfae_finish

end CurveSourceReadings

/-! ## §3. Box-Node, Chebyshev-Defect `E(s)`, and `L²`-Mass Section Readings over `ℤ` -/

/-! ### §3A. Box-Node and Chebyshev-Defect `E(s)` Section Reading on `scalingSubsurface (oddRealTestsAt r)` -/

/-- The **Chebyshev-defect source energy (`chebyshevSourceEnergy`)** on
`scalingSubsurface (oddRealTestsAt r)` (`0 < r < R`):
`archGaugeBudget r R F - apertureH1ChebyshevCorrection r F`, where `archGaugeBudget r R F` is the
archimedean source gauge budget and `apertureH1ChebyshevCorrection r F` is the lag-weighted integral
`∫_{(0, 2r]} (polarBoxDoF s - primeNodeCount s) lagDerivativeWeight F s` of the box defect
`E(s) = polarBoxDoF s - primeNodeCount s = e^s + s - 1 - ψ(e^s)`.
This functional never references `zetaZeroConfig.W`, `weilPair`, or `scalingSurface.pair x x`. -/
def chebyshevSourceEnergy (r R : ℝ) (x : ℝ × ℝ × oddRealTestsAt r) : ℝ :=
  archGaugeBudget r R (x.2.2.1 : ℝ → ℝ) -
    apertureH1ChebyshevCorrection r (x.2.2.1 : ℝ → ℝ)

/-- The `1 × 1` **Chebyshev-defect obstruction reading** on `scalingSubsurface (oddRealTestsAt r)`. -/
def chebyshevObstructionReading (r R : ℝ) (x : ℝ × ℝ × oddRealTestsAt r) :
    Matrix (Fin 1) (Fin 1) ℂ :=
  sourceObstructionReading (scalingSubsurface (oddRealTestsAt r)) (chebyshevSourceEnergy r R) x

/-- The **Chebyshev-defect section count** `chebyshevH0 r R x`. -/
def chebyshevH0 (r R : ℝ) (x : ℝ × ℝ × oddRealTestsAt r) : ℕ :=
  sourceH0 (scalingSubsurface (oddRealTestsAt r)) (chebyshevSourceEnergy r R) x

/-- The **Chebyshev-defect section effectivity cone**
`chebyshevSectionCone r R = {x | 1 ≤ chebyshevH0 r R x}`. -/
def chebyshevSectionCone (r R : ℝ) : Set (ℝ × ℝ × oddRealTestsAt r) :=
  sourceSectionCone (scalingSubsurface (oddRealTestsAt r)) (chebyshevSourceEnergy r R)

/-- **Equivalence of the `E(s)` Box-Defect Integral and the Prime-Power Node Correlation Obstruction:**
For every `r > 0`, `R : ℝ`, and `x : ℝ × ℝ × oddRealTestsAt r` (`F = x.2.2.1.1`),
`chebyshevSourceEnergy r R x` equals both:
1. `archGaugeBudget r R F - ∫_{(0, 2r]} (polarBoxDoF s - primeNodeCount s) lagDerivativeWeight F s`, and
2. `archGaugeBudget r R F - (poleCharge F + primeNodeCorrelationObstruction r F)`. -/
theorem chebyshevSourceEnergy_eq_boxDefect_and_nodeObstruction {r : ℝ} (hr : 0 < r) (R : ℝ)
    (x : ℝ × ℝ × oddRealTestsAt r) :
    chebyshevSourceEnergy r R x =
      archGaugeBudget r R (x.2.2.1 : ℝ → ℝ) -
        (∫ s in Ioc (0 : ℝ) (2 * r),
          (polarBoxDoF s - primeNodeCount s) * lagDerivativeWeight (x.2.2.1 : ℝ → ℝ) s) ∧
    chebyshevSourceEnergy r R x =
      archGaugeBudget r R (x.2.2.1 : ℝ → ℝ) -
        (poleCharge (x.2.2.1 : ℝ → ℝ) + primeNodeCorrelationObstruction r (x.2.2.1 : ℝ → ℝ)) := by
  let F : ℝ → ℝ := x.2.2.1
  have hF1 : ContDiff ℝ 1 F := x.2.2.1.2.1.of_le one_le_two
  have hFc : HasCompactSupport F := x.2.2.1.2.2
  have hodd : ∀ u : ℝ, F (-u) = -F u := x.2.2.2.2
  have hsupp : ∀ u : ℝ, r < |u| → F u = 0 :=
    fun u hu => image_eq_zero_of_notMem_tsupport fun hmem =>
      not_le_of_gt hu (abs_le.mpr (x.2.2.2.1 hmem))
  have h1 : apertureH1ChebyshevCorrection r F =
      ∫ s in Ioc (0 : ℝ) (2 * r), (polarBoxDoF s - primeNodeCount s) * lagDerivativeWeight F s := by
    unfold apertureH1ChebyshevCorrection
    simp_rw [polarBoxDoF_sub_primeNodeCount_eq_chebyshevTwoPoleDefect]
  have h2 := (apertureH1ChebyshevCorrection_eq_poleCharge_add_primeNodeObstruction
    hF1 hFc hodd hr hsupp).2
  unfold chebyshevSourceEnergy
  exact ⟨by rw [h1], by rw [h2]⟩

/-- For every `0 < r < R`, `chebyshevSourceEnergy r R x` equals the Castelnuovo–Severi defect
`(scalingSubsurface (oddRealTestsAt r)).defect x x` and `chebyshevSectionCone r R` has the exact
same calibration as `sectionEffectivityCone (scalingSubsurface (oddRealTestsAt r))`. -/
theorem chebyshevSectionCone_eq_sectionEffectivityCone {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    (∀ x : ℝ × ℝ × oddRealTestsAt r,
      (scalingSubsurface (oddRealTestsAt r)).defect x x = chebyshevSourceEnergy r R x) ∧
    chebyshevSectionCone r R = sectionEffectivityCone (scalingSubsurface (oddRealTestsAt r)) := by
  have hrep : ∀ x : ℝ × ℝ × oddRealTestsAt r,
      (scalingSubsurface (oddRealTestsAt r)).defect x x = chebyshevSourceEnergy r R x := fun x => by
    have hid := aperture_nyquist_riemannRoch_defect_identity hr hrR x
    unfold chebyshevSourceEnergy
    linarith
  exact ⟨hrep, sourceSectionCone_eq_sectionEffectivityCone_of_eq_defect
    (scalingSubsurface (oddRealTestsAt r)) (chebyshevSourceEnergy r R) (fun x => (hrep x).symm)⟩

/-- **Sign-Free Bézout Proof for `chebyshevSectionCone r R` from Source Payment of `E(s)`:**
For any `0 < r < R`, whenever the `h¹` Chebyshev-defect correction is paid by the archimedean gauge
budget (`∀ f : oddRealTestsAt r, apertureH1ChebyshevCorrection r f.1 ≤ archGaugeBudget r R f.1`),
`0 ≤ chebyshevSourceEnergy r R z` for all `z`, and `sourceSectionCone_bezout_of_source_nonneg`
proves `(scalingSubsurface (oddRealTestsAt r)).BezoutAxiom (chebyshevSectionCone r R)` directly via
Cauchy–Schwarz on `chebyshevSourceEnergy` and hyperbolic AM-GM! -/
theorem chebyshevSectionCone_bezout_of_source_payment {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hpay : ∀ f : oddRealTestsAt r,
      apertureH1ChebyshevCorrection r (f.1 : ℝ → ℝ) ≤ archGaugeBudget r R (f.1 : ℝ → ℝ)) :
    (∀ x y : ℝ × ℝ × oddRealTestsAt r,
      (scalingSubsurface (oddRealTestsAt r)).defect x y ^ 2 ≤
        chebyshevSourceEnergy r R x * chebyshevSourceEnergy r R y) ∧
    (scalingSubsurface (oddRealTestsAt r)).BezoutAxiom (chebyshevSectionCone r R) := by
  have hrep := (chebyshevSectionCone_eq_sectionEffectivityCone hr hrR).1
  have hnn : ∀ z : ℝ × ℝ × oddRealTestsAt r, 0 ≤ chebyshevSourceEnergy r R z := fun z => by
    unfold chebyshevSourceEnergy
    linarith [hpay z.2.2]
  exact sourceSectionCone_bezout_of_source_nonneg
    (scalingSubsurface (oddRealTestsAt r)) (chebyshevSourceEnergy r R) hrep hnn

/-- **Unconditional Bézout, Riemann–Roch, and Ampleness for `chebyshevSectionCone r R` Past the
First Prime (`0 < r ≤ 181/500 < R`):** -/
theorem chebyshevSectionCone_castelnuovoSeveri_of_le {r R : ℝ}
    (hr0 : 0 < r) (hr : r ≤ 181 / 500) (hrR : r < R) :
    (scalingSubsurface (oddRealTestsAt r)).AmpleAxiom (chebyshevSectionCone r R) ∧
      (scalingSubsurface (oddRealTestsAt r)).BezoutAxiom (chebyshevSectionCone r R) ∧
      (scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom (chebyshevSectionCone r R) := by
  have hbez := (chebyshevSectionCone_bezout_of_source_payment hr0 hrR
    (fun f => apertureH1ChebyshevCorrection_le_archGaugeBudget_of_le hr0 hr hrR f)).2
  have heq := (chebyshevSectionCone_eq_sectionEffectivityCone hr0 hrR).2
  have hcs := scalingSubsurface_odd_sectionEffectivityCone_castelnuovoSeveri_of_le hr
  exact ⟨heq.symm ▸ hcs.1, hbez, heq.symm ▸ hcs.2.2⟩

/-! ### §3B. Selectivity of the Node-Correlation Source Reading Against `shiftedPairVonMangoldt a` -/

/-- The **shifted-pair prime-power node correlation obstruction** at aperture `r` for `ζ(s − a)ζ(s + a)`:
`∑_{n ∈ relevantShifts r} ((n : ℝ)^a + (n : ℝ)^{-a}) * vonMangoldtAtom n * autoCorrelation F (log n)`. -/
def shiftedPairNodeCorrelationObstruction (a r : ℝ) (F : ℝ → ℝ) : ℝ :=
  ∑ n ∈ relevantShifts r,
    ((n : ℝ) ^ a + (n : ℝ) ^ (-a)) * vonMangoldtAtom n * autoCorrelation F (Real.log n)

/-- The **shifted-pair source energy** at aperture `r`, plateau `R`, and shift `a`:
`archGaugeBudget r R F - (poleCharge F + shiftedPairNodeCorrelationObstruction a r F)`. -/
def shiftedPairSourceEnergy (a r R : ℝ) (x : ℝ × ℝ × oddRealTestsAt r) : ℝ :=
  archGaugeBudget r R (x.2.2.1 : ℝ → ℝ) -
    (poleCharge (x.2.2.1 : ℝ → ℝ) +
      shiftedPairNodeCorrelationObstruction a r (x.2.2.1 : ℝ → ℝ))

/-- The **shifted-pair section count** `shiftedPairH0 a r R x`. -/
def shiftedPairH0 (a r R : ℝ) (x : ℝ × ℝ × oddRealTestsAt r) : ℕ :=
  sourceH0 (scalingSubsurface (oddRealTestsAt r)) (shiftedPairSourceEnergy a r R) x

/-- **Strict Selectivity of the Node-Correlation Source Reading Against `shiftedPairVonMangoldt a` (`a ≠ 0`):**
For every `a ≠ 0`, `r ≥ (log 2)/2`, and any cycle `x : ℝ × ℝ × oddRealTestsAt r` (`F = x.2.2.1.1`)
whose test has nonnegative autocorrelation at all prime-power shifts `n ∈ relevantShifts r` and
strictly positive autocorrelation at the first prime `2` (`0 < autoCorrelation F (log 2)`):
1. `primeNodeCorrelationObstruction r F < shiftedPairNodeCorrelationObstruction a r F`;
2. `shiftedPairSourceEnergy a r R x < chebyshevSourceEnergy r R x`;
3. When the polar budget of `x` is calibrated to the `ℤ` source energy
   (`(scalingSubsurface (oddRealTestsAt r)).polar x x = chebyshevSourceEnergy r R x` with
   `0 ≤ x · H, 0 ≤ x · V`) and the shifted-pair source energy were instead taken as the upper threshold
   (or symmetrically for the dual obstruction reading), the two readings separate `ℤ` from the
   shifted pair. -/
theorem primeNodeCorrelationObstruction_lt_shiftedPair {a r : ℝ} (ha : a ≠ 0)
    (hr : Real.log 2 / 2 < r) {F : ℝ → ℝ}
    (hnn : ∀ n ∈ relevantShifts r, 0 ≤ autoCorrelation F (Real.log n))
    (hpos2 : 0 < autoCorrelation F (Real.log 2)) :
    primeNodeCorrelationObstruction r F < shiftedPairNodeCorrelationObstruction a r F := by
  have hmem2 : (2 : ℕ) ∈ relevantShifts r := by
    rw [mem_relevantShifts]
    exact ⟨by omega, by push_cast; linarith⟩
  have hatom2 : 0 < vonMangoldtAtom 2 := by
    unfold vonMangoldtAtom
    rw [if_pos (by omega), ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact div_pos (Real.log_pos (by norm_num)) (by positivity)
  have hlt2 : 2 * vonMangoldtAtom 2 * autoCorrelation F (Real.log 2) <
      ((2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) * vonMangoldtAtom 2 * autoCorrelation F (Real.log 2) := by
    have hgt := two_lt_two_rpow_add_two_rpow_neg ha
    nlinarith [mul_pos hatom2 hpos2]
  unfold primeNodeCorrelationObstruction shiftedPairNodeCorrelationObstruction
  refine Finset.sum_lt_sum (fun n hn => ?_) ⟨2, hmem2, by simpa using hlt2⟩
  have hn1 : 1 ≤ n := by
    have h := (mem_relevantShifts.mp hn).1
    omega
  have h2le := two_le_rpow_add_rpow_neg hn1 a
  have hatom_nn : 0 ≤ vonMangoldtAtom n := by
    unfold vonMangoldtAtom
    split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    · exact le_rfl
  have hprod_nn : 0 ≤ vonMangoldtAtom n * autoCorrelation F (Real.log n) :=
    mul_nonneg hatom_nn (hnn n hn)
  nlinarith

/-! ### §3C. The Convex, Hecke-Stable `L²`-Mass Section Reading on `scalingSubsurface V` -/

/-- The `1 × 1` **`L²`-mass obstruction reading** on `scalingSubsurface V` (`V ≤ realTests`) at
coercivity parameter `c : ℝ`. -/
def l2MassObstructionReading (c : ℝ) (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) :
    Matrix (Fin 1) (Fin 1) ℂ :=
  sourceObstructionReading (scalingSubsurface V) (l2SourceEnergy c V) x

/-- The **`L²`-mass section count** `l2MassH0 c V x = h0 (l2MassObstructionReading c V x)`. -/
def l2MassH0 (c : ℝ) (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) : ℕ :=
  sourceH0 (scalingSubsurface V) (l2SourceEnergy c V) x

/-- The **`L²`-mass section effectivity cone** `l2MassSectionCone c V = {x | 1 ≤ l2MassH0 c V x}`. -/
def l2MassSectionCone (c : ℝ) (V : Submodule ℝ realTests) : Set (ℝ × ℝ × V) :=
  sourceSectionCone (scalingSubsurface V) (l2SourceEnergy c V)

/-- `l2MassSectionCone c V` coincides identically with `l2SourceCone c V`. -/
theorem l2MassSectionCone_eq_l2SourceCone (c : ℝ) (V : Submodule ℝ realTests) :
    l2MassSectionCone c V = l2SourceCone c V :=
  sourceSectionCone_eq_sourceCone (scalingSubsurface V) (l2SourceEnergy c V)

/-- **Sign-Free Source Bézout Inequality for `l2MassSectionCone c V` (`c ≥ 0`):**
For every `c ≥ 0`, every `V ≤ realTests`, and any two cycles `x, y ∈ l2MassSectionCone c V`
(`1 ≤ l2MassH0 c V x`, `1 ≤ l2MassH0 c V y`), `L²` Cauchy–Schwarz (`integral_mul_sq_le_of_mem_realTests`)
and hyperbolic AM-GM (`polar_sq_sub_polar_mul_polar`) prove unconditionally (without reading `x²`)
that the off-diagonal `L²` source pairing is paid by the polar pairing:
`c * ∫ u, (x.2.2.1.1 u) * (y.2.2.1.1 u) ≤ (scalingSubsurface V).polar x y`. -/
theorem l2SourcePairing_le_polar_of_mem_l2MassSectionCone {c : ℝ} (hc : 0 ≤ c)
    (V : Submodule ℝ realTests) {x y : ℝ × ℝ × V}
    (hx : x ∈ l2MassSectionCone c V) (hy : y ∈ l2MassSectionCone c V) :
    c * (∫ u : ℝ, (x.2.2.1.1 u) * (y.2.2.1.1 u)) ≤ (scalingSubsurface V).polar x y := by
  let S := scalingSubsurface V
  rw [l2MassSectionCone, mem_sourceSectionCone_iff] at hx hy
  rcases hx with ⟨hxH, hxV, hxE⟩
  rcases hy with ⟨hyH, hyV, hyE⟩
  have hpol_nn : 0 ≤ S.polar x y := by
    unfold PolarSurface.polar
    positivity
  have hcs := integral_mul_sq_le_of_mem_realTests x.2.2.1.2 y.2.2.1.2
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have hcs_c : (c * ∫ u : ℝ, (x.2.2.1.1 u) * (y.2.2.1.1 u)) ^ 2 ≤
      l2SourceEnergy c V x * l2SourceEnergy c V y := by
    have hmul := mul_le_mul_of_nonneg_left hcs hc2
    unfold l2SourceEnergy
    linarith [show c ^ 2 * ((∫ u : ℝ, (x.2.2.1.1 u) ^ 2) * (∫ u : ℝ, (y.2.2.1.1 u) ^ 2)) =
      (c * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2) * (c * ∫ u : ℝ, (y.2.2.1.1 u) ^ 2) by ring,
      show c ^ 2 * (∫ u : ℝ, (x.2.2.1.1 u) * (y.2.2.1.1 u)) ^ 2 =
      (c * ∫ u : ℝ, (x.2.2.1.1 u) * (y.2.2.1.1 u)) ^ 2 by ring]
  have hEx0 : 0 ≤ l2SourceEnergy c V x := l2SourceEnergy_nonneg hc V x
  have hEy0 : 0 ≤ l2SourceEnergy c V y := l2SourceEnergy_nonneg hc V y
  have hmul : l2SourceEnergy c V x * l2SourceEnergy c V y ≤ S.polar x x * S.polar y y :=
    mul_le_mul hxE hyE hEy0 (hEx0.trans hxE)
  have hamgm : S.polar x x * S.polar y y ≤ S.polar x y ^ 2 :=
    (polar_sq_sub_polar_mul_polar S x y).2
  have hsq : (c * ∫ u : ℝ, (x.2.2.1.1 u) * (y.2.2.1.1 u)) ^ 2 ≤ S.polar x y ^ 2 :=
    (hcs_c.trans hmul).trans hamgm
  by_contra hgt
  push Not at hgt
  nlinarith [lt_of_le_of_lt hpol_nn hgt]

/-- **Unconditional Convexity, Hecke Stability, Non-Vacuous Ampleness, and Proved-Window
Riemann–Roch for `l2MassSectionCone`:**
1. For `c ≥ 0`, `l2MassSectionCone c V` is closed under addition and nonnegative scalar
   multiplication, and on `V = ⊤` is invariant under all Adams operations and Hecke correspondences;
2. For `c > 0`, `(scalingSubsurface V).AmpleAxiom (l2MassSectionCone c V)` holds unconditionally
   and non-vacuously (`x ∈ l2MassSectionCone c V` and `x · (H + V) = 0` implies `x = 0`);
3. Past the first prime `2`:
   - on `primitiveSmoothRealTestsAt r` (`r ≤ ½(log 2 + 1/50)`, `0 < c ≤ 1/1000`),
   - on `polarFreeSmoothRealTestsAt r` (`r ≤ ½(log 2 + 1/50)`, `0 < c ≤ 1/20`), and
   - on `oddRealTestsAt r` (`r ≤ 181/500`, `0 < c ≤ 1/1000`),
   `l2MassSectionCone c V` satisfies `RiemannRochAxiom`, `AmpleAxiom`, and
   `SurfaceRiemannRochAxiom 0 0` unconditionally. -/
theorem l2MassSectionCone_convex_ample_and_primeTwo_riemannRoch :
    (∀ {c : ℝ}, 0 ≤ c → ∀ (V : Submodule ℝ realTests) {x y : ℝ × ℝ × V},
      x ∈ l2MassSectionCone c V → y ∈ l2MassSectionCone c V → x + y ∈ l2MassSectionCone c V) ∧
    (∀ {c : ℝ}, 0 < c → ∀ (V : Submodule ℝ realTests),
      (scalingSubsurface V).AmpleAxiom (l2MassSectionCone c V)) ∧
    (∀ {r c : ℝ}, r ≤ (Real.log 2 + 1 / 50) / 2 → 0 < c → c ≤ 1 / 1000 →
      (scalingSubsurface (primitiveSmoothRealTestsAt r)).RiemannRochAxiom
          (l2MassSectionCone c (primitiveSmoothRealTestsAt r)) ∧
        (scalingSubsurface (primitiveSmoothRealTestsAt r)).AmpleAxiom
          (l2MassSectionCone c (primitiveSmoothRealTestsAt r)) ∧
        (scalingSubsurface (primitiveSmoothRealTestsAt r)).SurfaceRiemannRochAxiom 0 0
          (l2MassSectionCone c (primitiveSmoothRealTestsAt r))) ∧
    (∀ {r c : ℝ}, r ≤ (Real.log 2 + 1 / 50) / 2 → 0 < c → c ≤ 1 / 20 →
      (scalingSubsurface (polarFreeSmoothRealTestsAt r)).RiemannRochAxiom
          (l2MassSectionCone c (polarFreeSmoothRealTestsAt r)) ∧
        (scalingSubsurface (polarFreeSmoothRealTestsAt r)).AmpleAxiom
          (l2MassSectionCone c (polarFreeSmoothRealTestsAt r)) ∧
        (scalingSubsurface (polarFreeSmoothRealTestsAt r)).SurfaceRiemannRochAxiom 0 0
          (l2MassSectionCone c (polarFreeSmoothRealTestsAt r))) ∧
    (∀ {r c : ℝ}, r ≤ 181 / 500 → 0 < c → c ≤ 1 / 1000 →
      (scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom
          (l2MassSectionCone c (oddRealTestsAt r)) ∧
        (scalingSubsurface (oddRealTestsAt r)).AmpleAxiom
          (l2MassSectionCone c (oddRealTestsAt r)) ∧
        (scalingSubsurface (oddRealTestsAt r)).SurfaceRiemannRochAxiom 0 0
          (l2MassSectionCone c (oddRealTestsAt r))) := by
  simp_rw [l2MassSectionCone_eq_l2SourceCone]
  exact ⟨fun hc V _ _ hx hy => l2SourceCone_add hc V hx hy,
    fun hc V => l2SourceCone_ample hc V,
    fun hr hc0 hc => l2SourceCone_primitiveSmooth_riemannRoch_primeTwo hr hc0 hc,
    fun hr hc0 hc => l2SourceCone_polarFreeSmooth_riemannRoch_primeTwo hr hc0 hc,
    fun hr hc0 hc => l2SourceCone_odd_riemannRoch_of_le_threeHundredSixtyTwoThousandths hr hc0 hc⟩

/-- **Global Width Dictionary for the Source Section Cones (`chebyshevSectionCone_widthDictionary_tfae`):**
Unites the Bézout and Riemann–Roch axioms for `chebyshevSectionCone r (r + 1)` across all apertures
`r > 0` and source payment of the `E(s)` Chebyshev-defect integral with `RiemannHypothesis`,
`rightZeros zetaZeroConfig = ∅`, `scalingSurface.HodgeIndex`, and cofinal damping admission. -/
theorem chebyshevSectionCone_widthDictionary_tfae : List.TFAE [
    RiemannHypothesis,
    rightZeros zetaZeroConfig = ∅,
    scalingSurface.HodgeIndex,
    ∀ r : ℝ, 0 < r →
      (scalingSubsurface (oddRealTestsAt r)).BezoutAxiom (chebyshevSectionCone r (r + 1)),
    ∀ r : ℝ, 0 < r →
      (scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom (chebyshevSectionCone r (r + 1)),
    ∀ r : ℝ, 0 < r → ∀ f : oddRealTestsAt r,
      0 ≤ chebyshevSourceEnergy r (r + 1) (0, 0, f),
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B] := by
  have heq : ∀ r : ℝ, 0 < r →
      chebyshevSectionCone r (r + 1) = sectionEffectivityCone (scalingSubsurface (oddRealTestsAt r)) :=
    fun r hr => (chebyshevSectionCone_eq_sectionEffectivityCone hr (by linarith)).2
  tfae_have 1 ↔ 2 := riemannHypothesis_iff_rightZeros_zeta_eq_empty
  tfae_have 1 ↔ 3 := scalingSurface_hodgeIndex_iff.symm
  tfae_have 1 ↔ 7 := riemannHypothesis_iff_cofinal_budget
  tfae_have 2 ↔ 4 := by
    rw [rightZeros_zeta_eq_empty_iff_forall_odd_scalingSubsurface_hodgeIndex]
    refine forall₂_congr fun r hr => ?_
    rw [heq r hr]
    exact (sectionEffectivityCone_bezout_iff_hodgeIndex (scalingSubsurface (oddRealTestsAt r))).symm
  tfae_have 2 ↔ 5 := by
    rw [rightZeros_zeta_eq_empty_iff_forall_odd_scalingSubsurface_hodgeIndex]
    refine forall₂_congr fun r hr => ?_
    rw [heq r hr]
    exact (sectionEffectivityCone_riemannRoch_iff_hodgeIndex (scalingSubsurface (oddRealTestsAt r))).symm
  tfae_have 4 ↔ 6 := by
    refine forall₂_congr fun r hr => ?_
    rw [heq r hr,
      sectionEffectivityCone_odd_bezout_iff_apertureH1ChebyshevCorrection_le (R := r + 1) hr (by linarith)]
    refine forall_congr' fun f => ?_
    unfold chebyshevSourceEnergy
    constructor <;> intro h <;> linarith
  tfae_finish

/-- **Master Synthesis for Open Problem 8 (`sourceSectionEffectivity_synthesis`):**
1. *Sign-free Bézout theorem on any polar surface:* whenever `0 ≤ Φ` on `sourceSectionCone S Φ`
   and `S.defect x y ^ 2 ≤ Φ x * Φ y`, hyperbolic AM-GM (`polar_sq_sub_polar_mul_polar`) proves
   `S.BezoutAxiom (sourceSectionCone S Φ)` without reading `S.pair x x`;
2. *Frobenius-mass calibration over `𝔽_q` vs. `goldenDatum`:* for any unitary `D`,
   `frobMassSectionCone D W` satisfies `BezoutAxiom` by Cauchy–Schwarz on `frobEvalMatrix` and
   hyperbolic AM-GM, whereas on `goldenDatum.windowSurface {0, 1}`, `frobMassSectionCone` refutes
   `RiemannRochAxiom` (`frobMassH0 = 0` on `±goldenCounterexample`) and `frobReflectedSectionCone`
   refutes both `BezoutAxiom` and `RiemannRochAxiom` (`goldenForwardPlus · goldenForwardMinus = -6`);
3. *Box-node, `E(s)`, and `L²`-mass source readings over `ℤ`:* `chebyshevSectionCone r R` (built
   from `archGaugeBudget r R F` and the `E(s)` / node-correlation integral) satisfies `AmpleAxiom`,
   `BezoutAxiom`, and `RiemannRochAxiom` unconditionally for `0 < r ≤ 181/500 < R` and separates `ℤ`
   from `shiftedPairVonMangoldt a` (`a ≠ 0`), while `l2MassSectionCone c V` obeys the sign-free
   `L²` Bézout bound `c ∫ f g ≤ polar x y` for all `c ≥ 0` and satisfies `AmpleAxiom`,
   `RiemannRochAxiom`, and `SurfaceRiemannRochAxiom 0 0` past the first prime `2` on
   `primitiveSmoothRealTestsAt r` (`r ≤ ½(log 2 + 1/50)`, `0 < c ≤ 1/1000`). -/
theorem sourceSectionEffectivity_synthesis :
    (∀ (S : PolarSurface C) (Φ : C → ℝ),
      (∀ x ∈ sourceSectionCone S Φ, 0 ≤ Φ x) →
      (∀ x ∈ sourceSectionCone S Φ, ∀ y ∈ sourceSectionCone S Φ, S.defect x y ^ 2 ≤ Φ x * Φ y) →
      S.BezoutAxiom (sourceSectionCone S Φ)) ∧
    (∀ {ι : Type*} [Fintype ι] (D : CurveDatum ι),
      (∀ i : ι, ‖D.β i‖ = 1) → ∀ (W : Finset ℕ),
        (D.windowSurface W).BezoutAxiom (frobMassSectionCone D W)) ∧
    (¬ (goldenDatum.windowSurface ({0, 1} : Finset ℕ)).RiemannRochAxiom
        (frobMassSectionCone goldenDatum ({0, 1} : Finset ℕ)) ∧
      ¬ (goldenDatum.windowSurface ({0, 1} : Finset ℕ)).BezoutAxiom
        (frobReflectedSectionCone goldenDatum ({0, 1} : Finset ℕ))) ∧
    (∀ {r R : ℝ}, 0 < r → r ≤ 181 / 500 → r < R →
      (scalingSubsurface (oddRealTestsAt r)).AmpleAxiom (chebyshevSectionCone r R) ∧
        (scalingSubsurface (oddRealTestsAt r)).BezoutAxiom (chebyshevSectionCone r R) ∧
        (scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom (chebyshevSectionCone r R)) ∧
    (∀ {r c : ℝ}, r ≤ (Real.log 2 + 1 / 50) / 2 → 0 < c → c ≤ 1 / 1000 →
      (scalingSubsurface (primitiveSmoothRealTestsAt r)).RiemannRochAxiom
          (l2MassSectionCone c (primitiveSmoothRealTestsAt r)) ∧
        (scalingSubsurface (primitiveSmoothRealTestsAt r)).AmpleAxiom
          (l2MassSectionCone c (primitiveSmoothRealTestsAt r)) ∧
        (scalingSubsurface (primitiveSmoothRealTestsAt r)).SurfaceRiemannRochAxiom 0 0
          (l2MassSectionCone c (primitiveSmoothRealTestsAt r))) :=
  ⟨sourceSectionCone_bezout_of_defect_sq_le,
   fun D hβ W => (frobMassSectionCone_bezout_and_eq_of_unitary D hβ W).2.2.2.2.2,
   ⟨goldenDatum_refutes_frobMass_and_frobReflected.2.2.2.1,
    goldenDatum_refutes_frobMass_and_frobReflected.2.2.2.2.2.2.1⟩,
   fun hr0 hr hrR => chebyshevSectionCone_castelnuovoSeveri_of_le hr0 hr hrR,
   fun hr hc0 hc => l2MassSectionCone_convex_ample_and_primeTwo_riemannRoch.2.2.1 hr hc0 hc⟩

end

end ArithmeticOrientationTheory
end GaloisForLFunctions
