import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.Stage1ReciprocityAndUnpuncture
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsHighTransport
import GaloisForLFunctions.MetaplecticMobiusDescent.Dictionary.MarkedReferenceEnergies

/-!
# Stage-1 dual sixth-power-free unpunctured energy

After `Stage1ReciprocityAndUnpuncture` transfers `firstCoreTwist` to `bad12Elem idx * w`, splits
`w₁ = g₆ ^ 6 * u_free.val` via `bad12FreeSplit`, unpunctures finite prime factors via
`inputConjugateRow_markedRadial_unpuncture_total_scale`, and decouples prime-slot collisions via
`disjTupleSum_l2_le_factored`, the Stage-1 tiny-bin `parentPoisson` energy reduces to unpunctured
factored `L^2` sums over dual sixth-power-free rows `u_free : FreeRow`:
`(X' * ∏_{j ∈ T'} Z_slot j)⁻¹ * ‖inputConjugateRow ... X' u_free.val * ∏_{j ∈ T'} slotCharSum j u_free.val‖^2`.

This module proves the unconditional `O(U^{(stage1DualScale r - V₀) + stage1Width r + ε})` bound
on those factored sums across `1/2 ≤ d_outer ≤ 5/6` and `17/25 ≤ r ≤ 19/26`.
-/

noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Classical Topology ContDiff SchwartzMap FourierTransform ComplexConjugate

namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

namespace Stage1DualSixthFreeEnergy

open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open CubicSieve CenteredMomentFourier
open FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialRayAttachment InverseFirstRayAttachment InverseMoment
open InverseSecondPrincipalCaller InverseFirstPriorityParents InversePrioritySecondSource
open InversePrincipalEnergy UniqueFactorizationMonoid
open InverseInitialArithmetic RayFourExpansion
open CanonicalCoefficientClass IdealDivisorBound
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeHighRowFamily ProbeFinalAssembly ProbeFinalAssemblyCertifiedBands Parameters
open HeckeDetectorRawFiber HeckeDetectorFiberPartition HeckeDetectorBatch
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection
open HeckeDetectorAmplitudeFirst HeckeDetectorRowCount HeckeDetectorRowwisePolynomial
open HeckeDetectorClassBudget
open DetectorDictionaryInverseRawInput DetectorDictionaryInverseRawInitialGates
open DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseMarkedPhysicalRows
open InverseInitialDetectorSource InverseInitialExcludedEnergy InverseInitialExcludedPool
open JointLogSeparation Stage1CubeBins Stage1DualRowMoments Stage1ReciprocityAndUnpuncture
open SubSevenEighthsHighTransport
open GaloisForLFunctions.FamilyContinuationTheory
open GaloisForLFunctions.FamilyContinuationTheory.Budget

local notation "O" => Eisenstein.O

/-! ### Part I: Dual `HighData` completion and zero-coprimality row counts -/

/-- Clean `Fin (D.N + N₂)` dual `HighData` constructor: given `D : HighData subDelta` with
`D.t ≤ min (subDelta / 8) (1 / 100000000)` and fine mesh, constructs `D_dual : HighData subDelta`
with `D_dual.N = D.N + N₂`, `D_dual.t = D.t`, `D_dual.e ≤ D.e`, `D_dual.ε ≤ D.ε`, fine mesh, and
`emb : Fin D.N ↪ Fin D_dual.N` satisfying `D_dual.ell (emb j) = (2 / 3) * D.ell j`. -/
theorem exists_dual_high_data_explicit (D : HighData subDelta)
    (ht_le : D.t ≤ min (subDelta / 8) (1 / 100000000))
    (hfine : ∀ j, D.ell j ≤ detectorMesh subDelta D.t / 200) :
    ∃ (D_dual : HighData subDelta) (emb : Fin D.N ↪ Fin D_dual.N),
      D_dual.t = D.t ∧
      D_dual.e ≤ D.e ∧
      D_dual.ε ≤ D.ε ∧
      2000 * D_dual.ε ≤ D_dual.t ∧
      2000 * D_dual.e ≤ D_dual.t ∧
      (∀ k, D_dual.ell k ≤ detectorMesh subDelta D_dual.t / 200) ∧
      (∀ j : Fin D.N, D_dual.ell (emb j) = (2 / 3 : ℝ) * D.ell j) := by
  have ht : 0 < D.t := D.t_pos
  have hm_lo : 0 < (7 / 8 : ℝ) * D.rmin := mul_pos (by norm_num) D.rmin_pos
  let mesh_cap := min ((7 / 8 : ℝ) * D.rmin) (min D.t (detectorMesh subDelta D.t))
  have hmc_pos : 0 < mesh_cap :=
    lt_min hm_lo (lt_min ht (detectorMesh_pos subDelta_pos ht))
  obtain ⟨N₂, hN₂, ell₂, rmin₂, hr₂, hell₂_inj, hsum₂, hbounds₂, _⟩ :=
    exists_physical_slot_lengths (1 / 200) (7 / 8) mesh_cap D.t
      (by norm_num) (by norm_num) hmc_pos ht
  let N_tot := D.N + N₂
  have hN_tot : 0 < N_tot := Nat.add_pos_left D.slots_pos N₂
  let ell_dual : Fin N_tot → ℝ :=
    Fin.append (fun j => (2 / 3 : ℝ) * D.ell j) (fun k => (1 / 3 : ℝ) * ell₂ k)
  let rmin_dual : ℝ := min ((2 / 3 : ℝ) * D.rmin) ((1 / 3 : ℝ) * rmin₂)
  have hr_dual : 0 < rmin_dual := lt_min (by linarith [D.rmin_pos]) (by linarith [hr₂])
  have hell_inj : Function.Injective ell_dual := by
    intro a b
    refine Fin.addCases (m := D.N) (n := N₂) (fun j₁ => ?_) (fun k₁ => ?_) a
    · refine Fin.addCases (m := D.N) (n := N₂) (fun j₂ => ?_) (fun k₂ => ?_) b
      · intro hab
        simp only [ell_dual, Fin.append_left] at hab
        exact congrArg (Fin.castAdd N₂)
          (D.slots_injective (mul_left_cancel₀ (by norm_num : (2 / 3 : ℝ) ≠ 0) hab))
      · intro hab
        exfalso
        simp only [ell_dual, Fin.append_left, Fin.append_right] at hab
        have h1 : (2 / 3 : ℝ) * ((7 / 8 : ℝ) * D.rmin) ≤ (2 / 3 : ℝ) * D.ell j₁ :=
          mul_le_mul_of_nonneg_left (D.slots_bounds j₁).2.1 (by norm_num)
        have h2 : ell₂ k₂ ≤ (1 / 200 : ℝ) * ((7 / 8 : ℝ) * D.rmin) :=
          (hbounds₂ k₂).2.2.1.trans
            (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
        linarith [D.rmin_pos]
    · refine Fin.addCases (m := D.N) (n := N₂) (fun j₂ => ?_) (fun k₂ => ?_) b
      · intro hab
        exfalso
        simp only [ell_dual, Fin.append_left, Fin.append_right] at hab
        have h1 : (2 / 3 : ℝ) * ((7 / 8 : ℝ) * D.rmin) ≤ (2 / 3 : ℝ) * D.ell j₂ :=
          mul_le_mul_of_nonneg_left (D.slots_bounds j₂).2.1 (by norm_num)
        have h2 : ell₂ k₁ ≤ (1 / 200 : ℝ) * ((7 / 8 : ℝ) * D.rmin) :=
          (hbounds₂ k₁).2.2.1.trans
            (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
        linarith [D.rmin_pos]
      · intro hab
        simp only [ell_dual, Fin.append_right] at hab
        exact congrArg (Fin.natAdd D.N)
          (hell₂_inj (mul_left_cancel₀ (by norm_num : (1 / 3 : ℝ) ≠ 0) hab))
  have hell_sum : (∑ k : Fin N_tot, ell_dual k) = 1 / 6 := by
    rw [Fin.sum_univ_add]
    simp only [ell_dual, Fin.append_left, Fin.append_right, ← Finset.mul_sum, D.slots_sum, hsum₂]
    norm_num
  have hell_bounds (k : Fin N_tot) :
      0 < ell_dual k ∧ (7 / 8) * rmin_dual ≤ ell_dual k ∧
        ell_dual k ≤ (1 / 200) * D.t ∧ ell_dual k ≤ detectorMesh subDelta D.t / 200 := by
    refine Fin.addCases (m := D.N) (n := N₂) (fun j => ?_) (fun j₂ => ?_) k
    · simp only [ell_dual, Fin.append_left]
      have hb := D.slots_bounds j
      have hf := hfine j
      have hr_le : rmin_dual ≤ (2 / 3 : ℝ) * D.rmin := min_le_left _ _
      have hdet_pos : 0 < detectorMesh subDelta D.t := detectorMesh_pos subDelta_pos ht
      refine ⟨by linarith [hb.1], by linarith [hb.2.1], by linarith [hb.2.2, ht], by linarith⟩
    · simp only [ell_dual, Fin.append_right]
      have hb := hbounds₂ j₂
      have hr_le : rmin_dual ≤ (1 / 3 : ℝ) * rmin₂ := min_le_right _ _
      have hdet_le : mesh_cap ≤ detectorMesh subDelta D.t :=
        (min_le_right _ _).trans (min_le_right _ _)
      have hdet_pos : 0 < detectorMesh subDelta D.t := detectorMesh_pos subDelta_pos ht
      have hm2 : ell₂ j₂ ≤ (1 / 200 : ℝ) * detectorMesh subDelta D.t :=
        hb.2.2.1.trans (mul_le_mul_of_nonneg_left hdet_le (by norm_num))
      refine ⟨by linarith [hb.1], by linarith [hb.2.1], by linarith [hb.2.2.2, ht], by linarith⟩
  let allowance := D.t / ((N_tot : ℝ) + 2000)
  have hden : 0 < (N_tot : ℝ) + 2000 := by positivity
  have ha : 0 < allowance := div_pos ht hden
  let small := min allowance (min D.e D.ε)
  have hsmall : 0 < small := lt_min ha (lt_min D.e_pos D.epsilon_pos)
  have hsa : small ≤ allowance := min_le_left _ _
  have hse : small ≤ D.e := (min_le_right _ _).trans (min_le_left _ _)
  have hsε : small ≤ D.ε := (min_le_right _ _).trans (min_le_right _ _)
  have ha0 : allowance ≤ D.t / 2000 :=
    div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) N_tot])
  have hst0 : small ≤ D.t / 2000 := hsa.trans ha0
  let ellMin := (7 / 8 : ℝ) * rmin_dual
  have hmin : 0 < ellMin := mul_pos (by norm_num) hr_dual
  obtain ⟨ε, e, κ, cost, _, hε, hε1, hεgap, hεa, he, he1, heell, hea, hκ, hκ1, hcost,
    hdet, hphase, _, _, _, _, _⟩ :=
    exists_detector_scales D.t rmin_dual D.t (1 / 200) D.t ellMin small 0
      ht.le hr_dual ht (by norm_num) ht hmin hsmall (by norm_num)
  let eps := small / 2
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hepss : eps ≤ small := by dsimp [eps]; linarith only [hsmall]
  have ht1 : D.t ≤ 1 / 100000000 := ht_le.trans (min_le_right _ _)
  have heps1 : eps ≤ 1 := by linarith only [hepss, hst0, ht1]
  have heN : ((N_tot : ℝ) + 2000) * eps ≤ D.t := by
    have h := (le_div_iff₀ hden).mp (hepss.trans hsa)
    simpa only [mul_comm] using h
  have he8 : ((N_tot : ℝ) + 8) * eps ≤ D.t := by nlinarith only [heN, heps.le]
  have hεt : 2000 * ε ≤ D.t := by linarith only [hεa, hst0]
  have het : 2000 * e ≤ D.t := by linarith only [hea, hst0]
  let sigma := min (D.t / 2) (ellMin / 4)
  have hs_pos : 0 < sigma := lt_min (by positivity) (by positivity)
  have hst2 : sigma ≤ D.t / 2 := min_le_left _ _
  have hsell : sigma ≤ ellMin / 4 := min_le_right _ _
  let D_dual : HighData subDelta := {
    t := D.t, N := N_tot, ell := ell_dual, rmin := rmin_dual, ε := ε, e := e, κ := κ,
    cost := cost, eps := eps, sigma := sigma
    t_pos := ht, t_delta := D.t_delta, t_small := ht1, slots_pos := hN_tot
    slots_injective := hell_inj, slots_sum := hell_sum
    slots_bounds := fun k => ⟨(hell_bounds k).1, (hell_bounds k).2.1, (hell_bounds k).2.2.1⟩
    rmin_pos := hr_dual, epsilon_pos := hε, epsilon_small := hε1, epsilon_gap := hεgap
    e_pos := he, e_small := he1, kappa_pos := hκ, kappa_small := hκ1, cost_pos := hcost
    eps_pos := heps, eps_small := heps1, sigma_pos := hs_pos
    detector_budget := by linarith only [hdet]
    phase_budget := hphase
    count_budget := by linarith only [hεt, ht1]
    central_budget := by nlinarith only [hεt, het, he8, ht1]
    geometric_budget := by linarith only [hst2, het, ht1]
    principal_budget := by linarith only [hst2, ht1]
    window_budget := by change sigma + e ≤ (7 / 8) * ellMin; linarith only [hsell, heell, hmin]
    floor_budget := by linarith only [hst2, het, he8, ht1]
    high_saving := by linarith only [hst2, ht]
    height_choice := by
      intro J hJ
      let τ := min ((1 / 200 : ℝ) * cost / 16) (min (1 / 800) (D.t / (4 * (J + 7))))
      have htau : 0 < τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
      have hτc : τ ≤ (1 / 200 : ℝ) * cost / 16 := min_le_left _ _
      have hτd : τ ≤ 1 / 800 := (min_le_right _ _).trans (min_le_left _ _)
      have hτt : τ ≤ D.t / (4 * (J + 7)) := (min_le_right _ _).trans (min_le_right _ _)
      have hτJ : τ * (4 * (J + 7)) ≤ D.t := (le_div_iff₀ (by positivity)).mp hτt
      have hprod : 0 ≤ τ * J := mul_nonneg htau.le hJ
      have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
      exact ⟨τ, htau, by linarith only [hτd], by linarith only [hτc, hcost],
        by nlinarith only [hτJ, hprod, htau], by nlinarith only [hτJ, hprod, htau],
        by nlinarith only [hτJ, hprod, hprodeps, htau]⟩ }
  let emb : Fin D.N ↪ Fin D_dual.N := Fin.castAddEmb N₂
  refine ⟨D_dual, emb, rfl, hea.trans hse, hεa.trans hsε, hεt, het,
    fun k => (hell_bounds k).2.2.2, fun j => ?_⟩
  change ell_dual (Fin.castAdd N₂ j) = _
  exact Fin.append_left _ _ j

/-- Transfers `F_dual : SourceData D_dual` up to `D` whenever `D_dual.e ≤ D.e`, preserving
`F_dual.S`, `F_dual.modulus`, `F_dual.w`, and `F_dual.W` definitionally. -/
def transferSourceDataUp {D D_dual : HighData subDelta} (F_dual : SourceData D_dual)
    (he : D_dual.e ≤ D.e) : SourceData D where
  S := F_dual.S
  exclusions := F_dual.exclusions
  maximal := F_dual.maximal
  first := F_dual.first.mono_parameter (by linarith)
  w := F_dual.w
  W := F_dual.W
  smooth := F_dual.smooth
  compact := F_dual.compact
  support := F_dual.support
  positive_support := F_dual.positive_support
  bounded := F_dual.bounded
  nonzero := F_dual.nonzero
  complex_eq := F_dual.complex_eq
  complex_nonzero := F_dual.complex_nonzero
  complex_support := F_dual.complex_support
  real := F_dual.real
  nonnegative := F_dual.nonnegative

/-- Zero-coprimality `SupportedWitness` family: replacing `source_ray_nonprincipal_eventually` by
`freeRow_nonprincipal_eventually` eliminates the `calibrationForSet` assumption on `FreeRow`s. -/
theorem supported_witnesses_uncalibrated
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character)
    (dmin dmax τ ε e κ heightCost margin : ℝ) (I : ℕ)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hτ : 0 < τ)
    (hτzero : τ < dmin / 2) (hτheight : 4 * τ < dmin * heightCost)
    (hε : 0 < ε) (he : 0 < e) (he' : e < 1 / 1000) (hκ : 0 < κ) (hκ' : κ ≤ 1)
    (hheightCost : 0 ≤ heightCost) (hmargin : 0 < margin)
    (hbudget : 12 * e * ((22 : ℝ) + 2) + 8 * κ + 2 * heightCost ≤ ε / 2) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ rows : Finset FreeRow, (∀ u ∈ rows, Z ^ (1 / 100 : ℝ) ≤ rowNorm u) →
      (∀ u ∈ rows, rowNorm u ≤ Z ^ (d - margin)) →
      let χ := fun u : rows => sourceDetectorFamily S hS.prime η u.val (rayCubeFamily M H hH u.val)
      ∀ (a : ℝ) (i : ℕ), i ≤ I → 51 / 100 < a → a ≤ 1 →
        (∀ u : rows, detectorMaximum (χ u) (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * e) →
        (∀ u : rows, a ≤ detectorMaximum (χ u) ((3 * i : ℕ) * Z ^ τ)) →
        ∀ tstar : ℝ, 1 ≤ tstar → tstar ≤ 3 / 2 →
          Nonempty (∀ u : rows, SupportedWitness (χ u) (Z ^ d) a ε tstar (Z ^ τ)
            ((Z ^ d) ^ (τ / (2 * dmax))) i) := by
  obtain ⟨Z0, hdet⟩ := actual_supported_witness_family dmin dmax τ ε e κ heightCost I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hheightCost hbudget
  filter_upwards [eventually_ge_atTop Z0,
    freeRow_nonprincipal_eventually M H hH S hS.prime η (1 / 100) (by norm_num),
    source_ray_conductor_eventually M H hH S hS.prime η margin hmargin] with Z hZ hnp hcond
  intro d hd hd' rows hlo hhi
  dsimp only
  intro a i hi ha ha' hnext hcurrent tstar ht ht'
  let χ := fun u : rows => sourceDetectorFamily S hS.prime η u.val (rayCubeFamily M H hH u.val)
  have hχ : ∀ u j, (χ u j).residue ≠ 1 := fun u => hnp u.val (hlo u.val u.property)
  have heq (u : rows) := detectorMaximum_eq_nonprincipal (χ u) (hχ u)
  exact hdet Z hZ d hd hd' χ hχ a i hi ha ha'
    (fun u => by rw [← heq u]; exact hnext u)
    (fun u => by rw [← heq u]; exact hcurrent u)
    (fun u => hcond u.val d (hhi u.val u.property)) tstar ht ht'

/-- Zero-coprimality `Batch` constructor on `Finset.univ` (`d ≤ 37/42`). -/
theorem actual_source_batch_uncalibrated
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth : ℝ) (I : ℕ)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hdtop : dmax ≤ 37 / 42) (hτ : 0 < τ)
    (hτzero : τ < dmin / 2) (hτheight : 4 * τ < dmin * heightCost)
    (hε : 0 < ε) (he : 0 < e) (he' : e < 1 / 1000) (hκ : 0 < κ) (hκ' : κ ≤ 1)
    (hheightCost : 0 ≤ heightCost) (hmargin : 0 < margin) (hm : 0 ≤ mesh) (hb : 0 < binWidth)
    (hbudget : 12 * e * ((22 : ℝ) + 2) + 8 * κ + 2 * heightCost ≤ ε / 2) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ rows : Finset FreeRow, rows.Nonempty →
        (∀ u ∈ rows, Z ^ (1 / 100 : ℝ) ≤ rowNorm u) →
        (∀ u ∈ rows, rowNorm u ≤ Z ^ (d - margin)) →
      ∀ (a : ℝ) (i : ℕ), i ≤ I → 51 / 100 < a → a ≤ 1 →
        (∀ u ∈ rows, detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * e) →
        (∀ u ∈ rows, a ≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          ((3 * i : ℕ) * Z ^ τ)) →
      ∀ tstar : ℝ, 1 ≤ tstar → tstar ≤ 3 / 2 →
      ∀ (N : ℕ) (ell : Fin N → ℝ), (∀ j, 0 < ell j) → (∀ j, ell j ≤ dmin * mesh) →
        (∑ j, ell j) = 1 / 6 →
      ∀ (W : Fin N → ℝ → ℂ) (upper : Fin N → ℝ) (z : Fin N → ℂ),
      ∃ B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
          (Z ^ d) a ε tstar (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i,
        B.rows = rows ∧ B.data = sourceMomentData M H hH S hS.prime η ∧
        B.reverse = sourceMomentReverse M H ∧ B.slots = Finset.univ ∧
        B.widths = (fun j => ell j / d) ∧ B.profile = W ∧ B.upper = upper ∧ B.external = z ∧
        B.mesh = mesh ∧ B.binWidth = binWidth ∧
        (∀ u ∈ rows, ∀ j, B.family u j =
          sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) := by
  have hw := supported_witnesses_uncalibrated M H hH S hS η
    dmin dmax τ ε e κ heightCost margin I hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ'
    hheightCost hmargin hbudget
  filter_upwards [hw, eventually_ge_atTop (1 : ℝ)] with Z hw hZ
  intro d hd hd' rows hne hlo hhi a i hi ha ha' hnext hcurrent tstar ht ht' N ell hell hsmall hsum
    W upper z
  obtain ⟨w⟩ := hw d hd hd' rows hlo hhi a i hi ha ha'
    (fun u => hnext u.val u.property) (fun u => hcurrent u.val u.property) tstar ht ht'
  obtain ⟨u0, h0⟩ := hne
  have hnorm (u : FreeRow) (hu : u ∈ rows) : rowNorm u ≤ Z ^ d :=
    (hhi u hu).trans (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
  obtain ⟨hwp, hwm, hsp⟩ :=
    physical_slot_widths ell d dmin mesh hdmin hd (hd'.trans hdtop) hell hsmall hsum
  let B := retainedSourceBatch M H hH S hS η rows u0 h0 (Z ^ d) a ε tstar (Z ^ τ)
    ((Z ^ d) ^ (τ / (2 * dmax))) i (fun u hu => w ⟨u, hu⟩) hnorm
    Finset.univ W upper (fun j => ell j / d) z mesh binWidth hm hb
    (fun j _ => hwp j) (fun j _ => hwm j) hsp
  refine ⟨B, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro u hu j
  dsimp [B, retainedSourceBatch]
  rw [retainedProjection_of_mem rows u0 u hu]

/-- Unconditional four-field moment supply on `F : SourceData D` at arbitrary raw parameters
`(c_raw, κ_raw)` (`0 < c_raw`, `0 < κ_raw`) WITHOUT `calibrationForSet`. -/
theorem sub_moments_uncalibrated
    (hβ51 : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (D : HighData subDelta)
    (hfine : ∀ j, D.ell j ≤ detectorMesh subDelta D.t / 200)
    (F : SourceData D) {c_raw κ_raw : ℝ} (hc_raw : 0 < c_raw) (hκ_raw : 0 < κ_raw) :
    ∃ τ : ℝ, 0 < τ ∧ τ < (1 / 200 : ℝ) / 2 ∧ 4 * τ < (1 / 200) * D.cost ∧ τ < D.t ∧
      2 * τ ≤ D.t ∧ τ * (2 + 4 * D.eps) < D.t ∧
      ∀ η : Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
        1 < Z ∧ ∀ rows : Finset FreeRow, (∀ u ∈ rows, Z ^ (1 / 100 : ℝ) ≤ rowNorm u) →
        ∀ d : ℝ, (1 / 200 : ℝ) ≤ d →
        ∀ (a tstar T allowance : ℝ) (i : ℕ)
          (B : Batch F.modulus ⊤ (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin D.N)
            (Z ^ d) a D.ε tstar T allowance i),
          B.rows ⊆ rows →
          B.data = sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η →
          B.profile = (fun _ x => (F.w x : ℂ)) →
          B.widths = (fun s => D.ell s / d) →
          B.upper = (fun _ => 2) →
          (∀ s, (B.external s).re = 17 / 50) →
          (∀ s, |(B.external s).im| ≤ Z ^ (2 * τ)) →
          ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
            Moments (B.fiber bin label left right hne) subDelta
              c_raw κ_raw (C * Z ^ D.t) (Z ^ (2 * τ)) D.t := by
  let Label := Sum Bool (RayQuotient.Characters F.modulus ⊤)
  letI : Fintype Label := Fintype.ofFinite _
  have hcert : ∀ bΦ : ℝ, 0 < bΦ →
      CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α := Fin D.N) F.modulus ⊤ le_top
        (fun x => conj (F.W x)) 2 (1 / 4) (9 / 4) bΦ 0 1 (33 / 50) (33 / 50) 2
        (CenteredMomentDetectorPlainMomentParameters.kappaPlain D)
        (CenteredMomentDetectorPlainMomentParameters.stageError D)
        (CenteredMomentEnergyWidthSchedule.count 2
          (CenteredMomentDetectorPlainMomentParameters.stageError D)) := by
    intro bΦ hbΦ
    have hp := CenteredMomentDetectorPlainMomentParameters.fixed_parameters D
    apply CenteredMomentEnergyCertifiedExistence.terminal_certificate (α := Fin D.N)
      F.modulus ⊤ le_top (fun x => conj (F.W x)) 1 2 (1 / 4) (9 / 4) bΦ 0 1
      (33 / 50) (33 / 50) 2
      (CenteredMomentDetectorPlainMomentParameters.kappaPlain D)
      (CenteredMomentDetectorPlainMomentParameters.stageError D)
    · norm_num
    · exact CenteredMomentDetectorPlainSlotProfile.conjugate_source_support F
    · exact Complex.conjCLE.contDiff.comp (F.W.smooth (⊤ : ℕ∞))
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact hbΦ
    · norm_num
    · norm_num
    · exact hp.2.2.2.2.1.le
    · exact hp.2.2.1
    · exact hβ51
    · unfold CenteredMomentDetectorPlainMomentParameters.kappaPlain
      have hβ_hi : HeckeZeroSupremum.beta ≤ 7 / 8 :=
        HeckeCommonProbe.beta_le_seven_eighths ProbeFinalAssemblyUnconditional.common_probe
      have hsubD : subDelta = 1 / 100000000 := rfl
      linarith
  obtain ⟨hp, hz⟩ := plain_inputs F hcert
  let mesh := detectorMesh subDelta D.t
  have hmesh : 0 < mesh := detectorMesh_pos subDelta_pos D.t_pos
  obtain ⟨Jr, hraw_prof⟩ := ProbeDetectorInverseRawField.fixed_raw_profiles c_raw κ_raw hc_raw hκ_raw
  obtain ⟨Jim, him⟩ := ProbeDetectorInverseMarkedField.source_batch_inverse_marked F.modulus ⊤ le_top F
  obtain ⟨Jm, hm⟩ := ProbeDetectorPlainMarkedFineField.source_batch_plain_marked_fine F mesh hmesh hfine hp
  obtain ⟨Ju, hu⟩ := ProbeDetectorPlainUnmarkedRestrictedField.source_batch_plain_unmarked D F hz
  let Jtot : ℕ := Jr + Jim + Jm + Ju
  obtain ⟨τ, hτ, hτd, hτcost, hτt, hτJ, hτeps⟩ := D.height_choice (Jtot : ℝ) (Nat.cast_nonneg Jtot)
  have hτ2 : 2 * τ ≤ D.t := by
    have h0 : 0 ≤ (Jtot : ℝ) := Nat.cast_nonneg Jtot
    nlinarith
  refine ⟨τ, hτ, hτd, hτcost, hτt, hτ2, hτeps, ?_⟩
  intro η
  let data_η := sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η
  choose Cr_l hCr_l hb_raw using (fun label : Label => hraw_prof (data_η label))
  let Cr : ℝ := 1 + ∑ label : Label, Cr_l label
  have hCr : 0 < Cr := by
    have h0 := Finset.sum_nonneg (fun label (_ : label ∈ Finset.univ) => (hCr_l label).le)
    dsimp [Cr]; linarith
  have hCr_le (label : Label) : Cr_l label ≤ Cr := by
    have he := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hCr_l j).le) (Finset.mem_univ label)
    dsimp [Cr]; linarith
  obtain ⟨Cim, hCim, him⟩ := him η
  obtain ⟨Cm, hCm, hm⟩ := hm η
  obtain ⟨Cu, hCu, hu⟩ := hu η
  let Ctot : ℝ := (Cr + Cim + Cm + Cu) * (2 : ℝ) ^ Jtot
  refine ⟨Ctot, by dsimp [Ctot]; positivity, ?_⟩
  filter_upwards [him, hm, hu] with Z him hm hu
  have hZ1 : 1 < Z := him.1
  have hZp : 0 < Z := zero_lt_one.trans hZ1
  refine ⟨hZ1, ?_⟩
  intro rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth hupper hextre hextim
    bin label left right hne
  let height : ℝ := Z ^ (2 * τ)
  have hh0 : 0 ≤ height := Real.rpow_nonneg hZp.le _
  have hh1 : 1 ≤ height := Real.one_le_rpow hZ1.le (by positivity)
  have h1h : 1 + height ≤ 2 * height := by linarith
  have hpow_le (K : ℕ) (hK : K ≤ Jtot) :
      (1 + height) ^ K ≤ (2 : ℝ) ^ Jtot * Z ^ D.t := by
    calc (1 + height) ^ K
        ≤ (1 + height) ^ Jtot := pow_le_pow_right₀ (by linarith) hK
      _ ≤ (2 * height) ^ Jtot := pow_le_pow_left₀ (by positivity) h1h Jtot
      _ = (2 : ℝ) ^ Jtot * (Z ^ (2 * τ)) ^ Jtot := by rw [mul_pow]
      _ = (2 : ℝ) ^ Jtot * Z ^ (2 * τ * (Jtot : ℝ)) := by
          rw [← Real.rpow_natCast (Z ^ (2 * τ)) Jtot, ← Real.rpow_mul hZp.le]
      _ ≤ (2 : ℝ) ^ Jtot * Z ^ D.t :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hZ1.le (by nlinarith [hτ.le]))
            (by positivity)
  have hCr' (l : Label) : Cr_l l * (1 + height) ^ Jr ≤ Ctot * Z ^ D.t := by
    calc Cr_l l * (1 + height) ^ Jr
        ≤ (Cr + Cim + Cm + Cu) * ((2 : ℝ) ^ Jtot * Z ^ D.t) :=
          mul_le_mul (by linarith [hCr_le l]) (hpow_le Jr (by dsimp [Jtot]; omega))
            (by positivity) (by positivity)
      _ = Ctot * Z ^ D.t := by dsimp [Ctot]; ring
  have hCim' : Cim * (1 + height) ^ Jim ≤ Ctot * Z ^ D.t := by
    calc Cim * (1 + height) ^ Jim
        ≤ (Cr + Cim + Cm + Cu) * ((2 : ℝ) ^ Jtot * Z ^ D.t) :=
          mul_le_mul (by linarith) (hpow_le Jim (by dsimp [Jtot]; omega)) (by positivity) (by positivity)
      _ = Ctot * Z ^ D.t := by dsimp [Ctot]; ring
  have hCm' : Cm * (1 + height) ^ Jm ≤ Ctot * Z ^ D.t := by
    calc Cm * (1 + height) ^ Jm
        ≤ (Cr + Cim + Cm + Cu) * ((2 : ℝ) ^ Jtot * Z ^ D.t) :=
          mul_le_mul (by linarith) (hpow_le Jm (by dsimp [Jtot]; omega)) (by positivity) (by positivity)
      _ = Ctot * Z ^ D.t := by dsimp [Ctot]; ring
  have hCu' : Cu * (1 + height) ^ Ju ≤ Ctot * Z ^ D.t := by
    calc Cu * (1 + height) ^ Ju
        ≤ (Cr + Cim + Cm + Cu) * ((2 : ℝ) ^ Jtot * Z ^ D.t) :=
          mul_le_mul (by linarith) (hpow_le Ju (by dsimp [Jtot]; omega)) (by positivity) (by positivity)
      _ = Ctot * Z ^ D.t := by dsimp [Ctot]; ring
  let F_fib := B.fiber bin label left right hne
  have hUp : 0 < Z ^ d := Real.rpow_pos_of_pos hZp _
  have hU0 : 0 ≤ Z ^ d := hUp.le
  have hfd : F_fib.rowData = data_η label := by
    change B.data label = data_η label; rw [hdata]
  have him_val := him.2 d hd a D.ε tstar T allowance i B hdata hprofile hupper hwidth hextre
    bin label left right hne height hh0
  have hmarked := hm.2 rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth
    (fun s => by rw [hupper]) hextre bin label left right hne height hh0 hextim
  have hunmarked := hu.2 rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth
    bin label left right hne height hh0
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn σ hσ t ht
    have hpair := hb_raw label F_fib.reverse n hn (Z ^ d) hUp tstar F_fib.r σ hσ height t hh0 ht
    rw [hfd]
    exact ⟨ProbeFinalAssembly.rawMoment_mono_constant hpair.1 (hCr' label),
      ProbeFinalAssembly.rawMoment_mono_constant hpair.2 (hCr' label)⟩
  · intro selected hselected hfirst hsecond n hn σ hσ t ht
    exact (him_val selected hselected hfirst hsecond n hn σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCim' (Real.rpow_nonneg hU0 _))
  · intro selected hselected hcap j k hjk σ hσ t ht
    exact (hmarked selected hselected hcap j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU0 _))
  · intro j k hjk σ hσ t ht
    exact (hunmarked j k hjk σ hσ t ht).1.trans
      (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU0 _))

private lemma batch_fiber_rows_subset {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
    {U a ε tstar T allowance : ℝ} {i : ℕ}
    (B : Batch M H Label Slot U a ε tstar T allowance i)
    (bin : B.Bin) (j : Label) (J K : Fin (dyadicLength U))
    (hne : (B.fiberRows bin j J K).Nonempty) :
    (B.fiber bin j J K hne).rows ⊆ B.rows :=
  Finset.filter_subset _ B.rows

private lemma batch_const_card_bound {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label : Type} [Fintype Label]
    {Slot : Type} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (B : Batch M H Label Slot U a ε tstar T allowance i)
    (C e : ℝ) (hC : 0 ≤ C) (hU : 0 < U)
    (hfiber : ∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
      ((B.fiber bin j J K hne).rows.card : ℝ) ≤ C * U ^ e) :
    (B.rows.card : ℝ) ≤
      (Fintype.card Label : ℝ) * (dyadicLength U : ℝ) ^ 2 * C * (Fintype.card B.Bin : ℝ) * U ^ e := by
  have hb := B.card_bound C (fun _ => e) hC hU hfiber
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hb

private lemma subset_no_slot_inverse_loss (r a ε t : ℝ)
    (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    HeckeInverseAmplification.sourceExponent r - (2 * a - 1) * r + 2 * ε + t ≤
      max 1 ((1 + 5 * r) / 6) - (2 * a - 1) * r + (160 * ε + 4 * t + subDelta) := by
  have hsrc : HeckeInverseAmplification.sourceExponent r = max 1 ((1 + 5 * r) / 6) := rfl
  rw [hsrc]
  linarith [subDelta_pos]

private lemma subset_no_slot_plain_loss (m a ε t : ℝ)
    (hε : 0 ≤ ε) (ht : 0 ≤ t) (hm : m ≤ 1 / 2 + 75 * ε) :
    max 1 (2 * m) - 2 * (2 * a - 1) * m + 4 * ε + t ≤
      1 - 2 * (2 * a - 1) * m + (160 * ε + 4 * t + subDelta) := by
  have hmax_m : max 1 (2 * m) ≤ 1 + 150 * ε := max_le (by linarith) (by linarith)
  linarith [subDelta_pos]

private lemma subset_inverse_marked_loss (r a x_rem q_rem ε t : ℝ)
    (hqx : (2 * a - 1) * x_rem = q_rem)
    (_hδ0 : 0 ≤ 2 * a - 1) (hδ1 : 2 * a - 1 ≤ 3 / 4)
    (_hx0 : 0 ≤ x_rem) (hx1 : x_rem ≤ 1 / 2)
    (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    1 - (2 * a - 1) * r - 2 * q_rem * ((1 - r) / 2 - t) + 2 * ε + (2 * a - 1) * t + t ≤
      inverseExponent (2 * a - 1) x_rem r + (160 * ε + 4 * t + subDelta) := by
  unfold inverseExponent
  rw [← hqx]
  have hid : 1 - (2 * a - 1) * r - 2 * ((2 * a - 1) * x_rem) * ((1 - r) / 2 - t) =
      1 - (2 * a - 1) * (x_rem + (1 - x_rem) * r) + 2 * ((2 * a - 1) * x_rem) * t := by ring
  have h2qx : 2 * ((2 * a - 1) * x_rem) ≤ 1 := by nlinarith
  have ht_mul : 2 * ((2 * a - 1) * x_rem) * t ≤ t :=
    (mul_le_mul_of_nonneg_right h2qx ht).trans_eq (one_mul t)
  have hat : (2 * a - 1) * t ≤ t := mul_le_of_le_one_left ht (by linarith)
  linarith [hid, ht_mul, hat, subDelta_pos]

private lemma subset_plain_marked_loss (m a x_rem q_rem z_req ε t : ℝ)
    (hqx : (2 * a - 1) * x_rem = q_rem)
    (hδ0 : 0 ≤ 2 * a - 1) (hδ1 : 2 * a - 1 ≤ 3 / 4)
    (hx0 : 0 ≤ x_rem) (hx1 : x_rem ≤ 1 / 2)
    (_hm0 : 0 ≤ m) (hm1 : m < 1 / 2)
    (hz_lb : (1 - 2 * m) / (9 / 2 + 12 * subDelta) - t ≤ z_req)
    (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    1 - 2 * (2 * a - 1) * m - 2 * q_rem * z_req + 4 * ε + (2 * a - 1) * t + t ≤
      1 - 2 * (2 * a - 1) * m - 2 * ((2 * a - 1) * x_rem) * (1 - 2 * m) / (9 / 2) +
        (160 * ε + 4 * t + subDelta) := by
  rw [← hqx]
  have hden_pos : 0 < 9 / 2 + 12 * subDelta := by have := subDelta_pos; linarith
  have h12m_pos : 0 ≤ 1 - 2 * m := by linarith
  have h12m_le1 : 1 - 2 * m ≤ 1 := by linarith
  have hgap_Δ : (1 - 2 * m) / (9 / 2) - (1 - 2 * m) / (9 / 2 + 12 * subDelta) ≤ subDelta := by
    rw [div_sub_div _ _ (by norm_num : (9 / 2 : ℝ) ≠ 0) hden_pos.ne',
      div_le_iff₀ (mul_pos (by norm_num) hden_pos)]
    have := subDelta_pos
    nlinarith
  have h2qx_nn : 0 ≤ 2 * ((2 * a - 1) * x_rem) := mul_nonneg (by norm_num) (mul_nonneg hδ0 hx0)
  have h2qx_le1 : 2 * ((2 * a - 1) * x_rem) ≤ 1 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hz_lb h2qx_nn
  have h2 := mul_le_mul_of_nonneg_left hgap_Δ h2qx_nn
  rw [mul_sub] at h1 h2
  have h3 : 2 * ((2 * a - 1) * x_rem) * subDelta ≤ subDelta :=
    (mul_le_mul_of_nonneg_right h2qx_le1 subDelta_pos.le).trans_eq (one_mul _)
  have h4 : 2 * ((2 * a - 1) * x_rem) * t ≤ t :=
    (mul_le_mul_of_nonneg_right h2qx_le1 ht).trans_eq (one_mul _)
  have hat : (2 * a - 1) * t ≤ t := mul_le_of_le_one_left ht (by linarith)
  have h_div_eq : 2 * ((2 * a - 1) * x_rem) * (1 - 2 * m) / (9 / 2) =
      2 * ((2 * a - 1) * x_rem) * ((1 - 2 * m) / (9 / 2)) := mul_div_assoc _ _ _
  linarith

private lemma subset_plain_cap_and_supply (m t tstar c_st ε L_rem : ℝ)
    (ht0 : 0 < t) (hε_t : (4 / 9) * ε ≤ t) (hL0 : 0 ≤ L_rem)
    (hm_lt : m < 1 / 2) (hm_lo : tstar - c_st - ε ≤ m)
    (hsup : (1 - 2 * (tstar - c_st)) * (2 / 9) + 2 * t ≤ L_rem) :
    max 0 ((1 - 2 * m) / (9 / 2 + 12 * subDelta) - t) ≤ L_rem ∧
      2 * m + 6 * (3 / 4 + 2 * subDelta) *
        max 0 ((1 - 2 * m) / (9 / 2 + 12 * subDelta) - t) ≤ 1 := by
  have hden_pos : 0 < 9 / 2 + 12 * subDelta := by have := subDelta_pos; linarith
  have h6κ : 6 * (3 / 4 + 2 * subDelta : ℝ) = 9 / 2 + 12 * subDelta := by ring
  constructor
  · apply max_le hL0
    have hnum_pos : 0 ≤ 1 - 2 * m := by linarith
    have hdiv_le : (1 - 2 * m) / (9 / 2 + 12 * subDelta) ≤ (1 - 2 * m) * (2 / 9) := by
      rw [div_le_iff₀ hden_pos]
      have := subDelta_pos
      nlinarith
    linarith
  · rw [h6κ]
    rcases le_total 0 ((1 - 2 * m) / (9 / 2 + 12 * subDelta) - t) with hle | hle
    · rw [max_eq_right hle, mul_sub, mul_div_cancel₀ _ hden_pos.ne']
      have hdt : 0 < (9 / 2 + 12 * subDelta) * t := mul_pos hden_pos ht0
      linarith
    · rw [max_eq_left hle, mul_zero, add_zero]
      linarith

private lemma subset_inv_sup_step (r c_st t L_rem : ℝ)
    (hcr : c_st ≤ r) (hsup : (1 - c_st) / 2 + 2 * t ≤ L_rem) (ht : 0 < t) :
    (1 - r) / 2 - t ≤ L_rem := by
  linarith

private theorem subset_slot_fiber_count
    {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
    {U a ε tstar T allowance c_no κ_no K₀ C_mom height t q_rem x_rem : ℝ} {i : ℕ}
    (F_sub : Fiber M H Label Slot U a ε tstar T allowance i)
    (hmom_sub : Moments F_sub subDelta c_no κ_no C_mom height t)
    (hamp_sub : (F_sub.rows.card : ℝ) ≤ (12 * (1 + height) * (C_mom * K₀)) *
      U ^ (HeckeInverseAmplification.sourceExponent F_sub.r - (2 * a - 1) * F_sub.r + 2 * ε + t))
    (hU : 1 < U) (hδ_lo : 11 / 25 ≤ 2 * a - 1) (hδ_hi : 2 * a - 1 ≤ 3 / 4)
    (hε0 : 0 ≤ ε) (_hε_small : ε ≤ 1 / 1000)
    (ht0 : 0 < t) (hε_t : (4 / 9) * ε ≤ t)
    (hC_mom : 0 ≤ C_mom) (hh0 : 0 ≤ height) (hf_le : 2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height)
    (hK₀ : 0 ≤ K₀)
    (hx0 : 0 ≤ x_rem) (hx1 : x_rem ≤ 1 / 2) (hqx : (2 * a - 1) * x_rem = q_rem)
    (ht_lo : 1 ≤ tstar) (ht_hi : tstar ≤ 3 / 2)
    (hcross_eq : crossing x_rem tstar = stage1Crossing (2 * a - 1) x_rem ∧
      max (shortExponent (2 * a - 1) x_rem tstar) (longExponent (2 * a - 1) tstar) =
        Budget.rowCount (2 * a - 1) x_rem)
    (S_rem' : Finset Slot) (hS_sub : S_rem' ⊆ F_sub.slots)
    (hw_pos : ∀ s ∈ S_rem', 0 < F_sub.widths s)
    (hw_mesh : ∀ s ∈ S_rem', F_sub.widths s ≤ t)
    (hL_rem : 0 < ∑ s ∈ S_rem', F_sub.widths s)
    (g_rem : Slot → ℝ)
    (hmean_g : weightedMean S_rem' F_sub.widths g_rem = q_rem)
    (hbins_sub : ∀ u ∈ F_sub.rows, ∀ s ∈ S_rem',
      HeckePrimeAmplitudeBins.amplitude (U ^ (F_sub.widths s)) ((2 * a - 1) / 2) t
        (physical M H (fun u : FreeRow => u.val) F_sub.profile F_sub.upper
          F_sub.widths F_sub.external U u s) = g_rem s)
    (hsup_inv : (1 - stage1Crossing (2 * a - 1) x_rem) / 2 + 2 * t ≤ ∑ s ∈ S_rem', F_sub.widths s)
    (hsup_plain : (1 - 2 * (tstar - stage1Crossing (2 * a - 1) x_rem)) * (2 / 9) + 2 * t ≤
      ∑ s ∈ S_rem', F_sub.widths s) :
    (F_sub.rows.card : ℝ) ≤ fiberConstant C_mom height K₀ *
      U ^ (Budget.rowCount (2 * a - 1) x_rem + (160 * ε + 4 * t + subDelta) + 6 * t + 5 * ε) := by
  have hUp : 0 < U := zero_lt_one.trans hU
  have ha12 : 1 / 2 ≤ a := by linarith
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨hconst0, hconstP, hconstI, hconstI0⟩ := fiberConstant_bounds C_mom height K₀ hC_mom hh0 hK₀
  have hgeom := F_sub.lengths hU
  have hcross_bnd := crossing_bounds hx0 hx1 ht_lo ht_hi
  have promote (C' p q : ℝ) (hC' : C' ≤ fiberConstant C_mom height K₀)
      (hb : (F_sub.rows.card : ℝ) ≤ C' * U ^ p) (hpq : p ≤ q) :
      (F_sub.rows.card : ℝ) ≤ fiberConstant C_mom height K₀ * U ^ q :=
    hb.trans ((mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hUp.le _)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hpq) hconst0))
  have hI0 : (F_sub.rows.card : ℝ) ≤ fiberConstant C_mom height K₀ *
      U ^ (max 1 ((1 + 5 * F_sub.r) / 6) - (2 * a - 1) * F_sub.r + (160 * ε + 4 * t + subDelta)) :=
    promote _ _ _ hconstI0 hamp_sub (subset_no_slot_inverse_loss F_sub.r a ε t hε0 ht0.le)
  have hp0 := F_sub.plain_unmarked_count hmom_sub hU ha0 hC_mom hh0 hf_le
  have hP0 : (F_sub.rows.card : ℝ) ≤ fiberConstant C_mom height K₀ *
      U ^ (1 - 2 * (2 * a - 1) * F_sub.m + (160 * ε + 4 * t + subDelta)) :=
    promote _ _ _ hconstP hp0 (subset_no_slot_plain_loss F_sub.m a ε t hε0 ht0.le hgeom.2.2.1)
  have hI_br : crossing x_rem tstar ≤ F_sub.r → F_sub.r < 1 → t < (1 - F_sub.r) / 2 →
      (F_sub.rows.card : ℝ) ≤ fiberConstant C_mom height K₀ *
        U ^ (inverseExponent (2 * a - 1) x_rem F_sub.r + (160 * ε + 4 * t + subDelta)) := by
    intro hrc hr1 hvt
    obtain ⟨hz0, _, hcap1, hcap2⟩ :=
      HeckeDetectorBranchBudget.inverse_requested_capacity F_sub.r t
        (hcross_bnd.1.trans hrc) hr1 ht0 hvt
    have hz_sup : (1 - F_sub.r) / 2 - t ≤ ∑ s ∈ S_rem', F_sub.widths s :=
      subset_inv_sup_step F_sub.r (stage1Crossing (2 * a - 1) x_rem) t _
        (hcross_eq.1 ▸ hrc) hsup_inv ht0
    have hb := HeckeDetectorInverseFiberCount.inverse_fiber_count M H
      F_sub.rows F_sub.nonempty F_sub.family U a ε tstar T allowance i hU ha12
      (fun u => (F_sub.witness u).toWitness) F_sub.label F_sub.left F_sub.right
      F_sub.fixed_label F_sub.fixed_left F_sub.fixed_right S_rem' (fun u => u.val)
      F_sub.profile F_sub.upper F_sub.widths g_rem F_sub.external
      t t ((1 - F_sub.r) / 2 - t) t C_mom height
      ht0.le ht0 hw_pos hw_mesh hL_rem hz0 hz_sup hbins_sub
      hC_mom hh0 hf_le hcap1 hcap2
      (fun selected hsel hc1 hc2 n hn σ hσ freq hfreq' =>
        hmom_sub.inverse_marked selected (hsel.trans hS_sub) hc1 hc2 n hn σ hσ freq hfreq')
    rw [hmean_g] at hb
    exact promote _ _ _ hconstI hb
      (subset_inverse_marked_loss F_sub.r a x_rem q_rem ε t hqx (by linarith) hδ_hi hx0 hx1 hε0 ht0.le)
  have hP_br : F_sub.r ≤ crossing x_rem tstar → F_sub.m < 1 / 2 →
      t < (1 - 2 * F_sub.m) / (9 / 2) →
      (F_sub.rows.card : ℝ) ≤ fiberConstant C_mom height K₀ *
        U ^ (1 - 2 * (2 * a - 1) * F_sub.m -
          2 * ((2 * a - 1) * x_rem) * (1 - 2 * F_sub.m) / (9 / 2) +
          (160 * ε + 4 * t + subDelta)) := by
    intro hrc hm_lt _
    let z_req : ℝ := max 0 ((1 - 2 * F_sub.m) / (9 / 2 + 12 * subDelta) - t)
    have hm_lo : tstar - stage1Crossing (2 * a - 1) x_rem - ε ≤ F_sub.m := by
      have hcr : F_sub.r ≤ stage1Crossing (2 * a - 1) x_rem := hcross_eq.1 ▸ hrc
      exact (sub_le_sub_right (sub_le_sub_left hcr tstar) ε).trans hgeom.1
    obtain ⟨hz_sup, hcap_pl⟩ := subset_plain_cap_and_supply F_sub.m t tstar
      (stage1Crossing (2 * a - 1) x_rem) ε (∑ s ∈ S_rem', F_sub.widths s)
      ht0 hε_t hL_rem.le hm_lt hm_lo hsup_plain
    have hb := HeckeDetectorPlainFiberCount.plain_fiber_count M H
      F_sub.rows F_sub.nonempty F_sub.family U a ε tstar T allowance i hU ha12
      (fun u => (F_sub.witness u).toWitness) F_sub.label F_sub.left F_sub.right
      F_sub.fixed_label F_sub.fixed_left F_sub.fixed_right S_rem' (fun u => u.val)
      F_sub.profile F_sub.upper F_sub.widths g_rem F_sub.external
      t t z_req (3 / 4 + 2 * subDelta) t C_mom height
      ht0.le ht0 hw_pos hw_mesh hL_rem (le_max_left _ _) hz_sup hbins_sub
      (by have := subDelta_pos; positivity)
      hC_mom hh0 hf_le hcap_pl
      (fun selected hsel hcap' j k hjk σ hσ freq hfreq' =>
        hmom_sub.plain_marked selected (hsel.trans hS_sub) hcap' j k hjk σ hσ freq hfreq')
    rw [hmean_g] at hb
    exact promote _ _ _ hconstP hb
      (subset_plain_marked_loss F_sub.m a x_rem q_rem z_req ε t hqx (by linarith) hδ_hi
        hx0 hx1 hgeom.2.2.2.2 hm_lt (le_max_right _ _) hε0 ht0.le)
  have hc_br := count_bound_of_crossing_branches (F_sub.rows.card : ℝ)
    (fiberConstant C_mom height K₀) U (2 * a - 1) x_rem tstar F_sub.r F_sub.m
    (160 * ε + 4 * t + subDelta) t ε hconst0 hU.le (by linarith) (by linarith) hx0 hx1
    ht_lo ht_hi ht0.le hε0 hgeom.1 hgeom.2.1 hI0 hP0 hI_br hP_br
  rwa [hcross_eq.2] at hc_br

/-- **Subset-slot uncalibrated row-count bound on `S_rem'` (`11/25 ≤ 2*a - 1 ≤ 3/4`):**
Given `rows_bin : Finset FreeRow` in a fixed `S_rem'`-amplitude class `bin_rem` at `U_dual = Z ^ d`
(`1/100 ≤ d ≤ 4/5`) where `S_rem'` satisfies the Stage-1 crossing slot-supply inequalities at
`tstar = Endpoint.balancedCutoff (2*a - 1) (1/2 - x_rem)`, the cardinality `(rows_bin.card : ℝ)` is
bounded by `K_cnt * C0 * Z ^ (d * Budget.rowCount (2*a - 1) x_rem + 200 * D_dual.ε + 20 * D_dual.t + subDelta)`. -/
theorem uncalibrated_subset_slot_row_count
    (hβ51 : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (D_dual : HighData subDelta)
    (hfine : ∀ j, D_dual.ell j ≤ detectorMesh subDelta D_dual.t / 200)
    (F_dual : SourceData D_dual) (n_bins : ℕ) :
    ∃ (τ : ℝ) (K_cnt : ℝ), 0 < τ ∧ 2 * τ ≤ D_dual.t ∧ 0 < K_cnt ∧
      ∀ η : Character, ∃ C0 : ℝ, 0 < C0 ∧ ∀ᶠ Z : ℝ in atTop,
        1 < Z ∧
        ∀ d : ℝ, 1 / 100 ≤ d → d ≤ 4 / 5 →
        ∀ (a : ℝ) (i : ℕ), i ≤ n_bins → 11 / 25 ≤ 2 * a - 1 → 2 * a - 1 ≤ 3 / 4 →
        ∀ S_rem' : Finset (Fin D_dual.N), S_rem'.Nonempty →
        ∀ zs : Fin D_dual.N → ℂ, (∀ s, (zs s).re = 17 / 50) → (∀ s, |(zs s).im| ≤ Z ^ (2 * τ)) →
        ∀ bin_rem : BinLabel S_rem' ((2 * a - 1) / 2) D_dual.t,
        let U_d := Z ^ d
        let widths_d : Fin D_dual.N → ℝ := fun s => D_dual.ell s / d
        let q_rem := weightedMean S_rem' widths_d (binValue S_rem' ((2 * a - 1) / 2) D_dual.t bin_rem)
        let δ := 2 * a - 1
        let x_rem := q_rem / δ
        let tstar := Endpoint.balancedCutoff δ (1 / 2 - x_rem)
        (1 - stage1Crossing δ x_rem) / 2 + 2 * D_dual.t ≤ ∑ s ∈ S_rem', widths_d s →
        (1 - 2 * (tstar - stage1Crossing δ x_rem)) * (2 / 9) + 2 * D_dual.t ≤
          ∑ s ∈ S_rem', widths_d s →
        ∀ rows_bin : Finset FreeRow,
          (∀ u ∈ rows_bin, Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧ rowNorm u ≤ Z ^ (d - D_dual.t)) →
          (∀ u ∈ rows_bin, detectorMaximum
            (sourceDetectorFamily F_dual.S F_dual.exclusions.prime η u
              (rayCubeFamily F_dual.modulus ⊤ le_top u))
            (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * D_dual.e) →
          (∀ u ∈ rows_bin, a ≤ detectorMaximum
            (sourceDetectorFamily F_dual.S F_dual.exclusions.prime η u
              (rayCubeFamily F_dual.modulus ⊤ le_top u))
            ((3 * i : ℕ) * Z ^ τ)) →
          (∀ u ∈ rows_bin, ∀ s ∈ S_rem',
            HeckePrimeAmplitudeBins.amplitude (U_d ^ (widths_d s)) ((2 * a - 1) / 2) D_dual.t
              (physical F_dual.modulus ⊤ (fun u : FreeRow => u.val)
                (fun _ x => (F_dual.w x : ℂ)) (fun _ => 2) widths_d zs U_d u s) =
              binValue S_rem' ((2 * a - 1) / 2) D_dual.t bin_rem s) →
          (rows_bin.card : ℝ) ≤ K_cnt * C0 *
            Z ^ (d * Budget.rowCount δ x_rem + 200 * D_dual.ε + 20 * D_dual.t + subDelta) := by
  let Label := Sum Bool (RayQuotient.Characters F_dual.modulus ⊤)
  letI : Fintype Label := Fintype.ofFinite _
  obtain ⟨c_no, κ_no, K₀, hc_no, _, hκ_no, hK₀, hamp⟩ :=
    HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
      F_dual.modulus ⊤ le_top F_dual.S F_dual.w F_dual.smooth F_dual.compact
      F_dual.positive_support (fun y => (F_dual.bounded y).1) F_dual.nonzero
      1 2 1 (by norm_num) (by norm_num) (by norm_num) F_dual.support
      (fun y => (F_dual.bounded y).2) 2 D_dual.t (by norm_num) D_dual.t_pos
  obtain ⟨τ, hτ, hτd, hτcost, _, hτ2, _, hmom_all⟩ :=
    sub_moments_uncalibrated hβ51 D_dual hfine F_dual hc_no hκ_no
  obtain ⟨K_pref, hK_pref, hpref⟩ :=
    source_count_prefactor_eventually (Label := Label) D_dual.N (1 / 100) (4 / 5)
      D_dual.t (2 * τ) D_dual.t D_dual.t K₀ (by norm_num) (by norm_num)
      D_dual.t_pos (by positivity) D_dual.t_pos
  refine ⟨τ, K_pref, hτ, hτ2, hK_pref, ?_⟩
  intro η
  obtain ⟨C0, hC0, hmom_η⟩ := hmom_all η
  have hbatches := actual_source_batch_uncalibrated F_dual.modulus ⊤ le_top
    F_dual.S F_dual.exclusions η
    (1 / 100) (4 / 5) τ D_dual.ε D_dual.e D_dual.κ D_dual.cost D_dual.t (1 / 2) D_dual.t n_bins
    (by norm_num) (by norm_num) (by norm_num) hτ
    (by linarith) (by linarith) D_dual.epsilon_pos D_dual.e_pos D_dual.e_small
    D_dual.kappa_pos D_dual.kappa_small D_dual.cost_pos.le D_dual.t_pos (by norm_num) D_dual.t_pos
    (by nlinarith [D_dual.detector_budget])
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [hmom_η, hbatches, hpref,
    eventually_all_rpow_ge hamp (1 / 100) (by norm_num),
    source_count_frequency_eventually n_bins (4 / 5) τ (2 * τ) (by norm_num) hτ (by linarith),
    eventually_all_rpow_ge (eventually_gt_atTop (1 : ℝ)) (1 / 100) (by norm_num)]
    with Z hmomZ hbatch hpref hampZ hfreq hU1
  have hZ1 : 1 < Z := hmomZ.1
  have hZp : 0 < Z := zero_lt_one.trans hZ1
  refine ⟨hZ1, ?_⟩
  intro d hd hd' a i hi hδ_lo hδ_hi S_rem' hS_ne zs hzre hzim bin_rem
    U_d widths_d q_rem δ x_rem tstar hsup_inv hsup_plain rows_bin hrows hnext hcurrent hbins_rem
  by_cases hrows_ne : rows_bin.Nonempty
  · have ha_lo : 51 / 100 < a := by linarith
    have ha_hi : a ≤ 1 := by linarith
    have hδ_pos : 0 < δ := by linarith
    have hδ_56 : δ ≤ 5 / 6 := by linarith
    have hd_pos : 0 < d := by linarith
    have hU_gt1 : 1 < U_d := hU1 d hd
    have hU_pos : 0 < U_d := zero_lt_one.trans hU_gt1
    have hw_pos (s : Fin D_dual.N) : 0 < widths_d s :=
      div_pos (D_dual.slots_bounds s).1 hd_pos
    have hw_mesh (s : Fin D_dual.N) : widths_d s ≤ D_dual.t := by
      dsimp [widths_d]
      rw [div_le_iff₀ hd_pos]
      have h1 := (D_dual.slots_bounds s).2.2
      have h2 := D_dual.t_pos
      nlinarith
    have hL_rem : 0 < ∑ s ∈ S_rem', widths_d s :=
      Finset.sum_pos (fun s _ => hw_pos s) hS_ne
    have ⟨u_wit, hu_wit⟩ := hrows_ne
    have hq_bounds : 0 ≤ q_rem ∧ q_rem ≤ δ / 2 := by
      dsimp [q_rem, δ]
      apply weightedMean_bounds S_rem' widths_d _ (2 * a - 1)
        (fun s _ => (hw_pos s).le) hL_rem
      intro s hs
      rw [← hbins_rem u_wit hu_wit s hs]
      exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith)
    have hx0 : 0 ≤ x_rem := div_nonneg hq_bounds.1 hδ_pos.le
    have hx1 : x_rem ≤ 1 / 2 := (div_le_iff₀ hδ_pos).mpr (by linarith [hq_bounds.2])
    have hqx : δ * x_rem = q_rem := by dsimp [x_rem]; field_simp [hδ_pos.ne']
    have ht_bounds : 1 ≤ tstar ∧ tstar ≤ 3 / 2 := by
      have hc := HeckeDetectorAdaptiveCutoff.cutoff_bounds δ q_rem hδ_pos.le
      rwa [HeckeDetectorAdaptiveCutoff.cutoff_eq_balanced δ q_rem hδ_pos hδ_56
        hq_bounds.1 hq_bounds.2] at hc
    have hcross_eq := stage1_crossing_and_count_eq hδ_pos.le hδ_56 hx0 hx1
    have hcross_bnd := crossing_bounds hx0 hx1 ht_bounds.1 ht_bounds.2
    have hell_pos (k : Fin D_dual.N) : 0 < D_dual.ell k := (D_dual.slots_bounds k).1
    have hell_hi (k : Fin D_dual.N) : D_dual.ell k ≤ (1 / 100 : ℝ) * (1 / 2) := by
      have h1 := (D_dual.slots_bounds k).2.2
      have h2 := D_dual.t_small
      linarith
    let WC : Fin D_dual.N → ℝ → ℂ := fun _ x => (F_dual.w x : ℂ)
    obtain ⟨B, hBr, hBd, hRev, hSlots, hWidths, hW, hUpper, hExt, hMesh, hBin, hFam⟩ :=
      hbatch d hd hd' rows_bin hrows_ne (fun u hu => (hrows u hu).1)
        (fun u hu => (hrows u hu).2) a i hi ha_lo ha_hi hnext hcurrent
        tstar ht_bounds.1 ht_bounds.2 D_dual.N D_dual.ell hell_pos hell_hi D_dual.slots_sum
        WC (fun _ => 2) zs
    let C_mom := C0 * Z ^ D_dual.t
    let height := Z ^ (2 * τ)
    have hC_mom : 0 ≤ C_mom := mul_nonneg hC0.le (Real.rpow_nonneg hZp.le _)
    have hh0 : 0 ≤ height := Real.rpow_nonneg hZp.le _
    have hf_le : 2 * Real.pi * ((Z ^ d) ^ (τ / (2 * (4 / 5 : ℝ)))) + (3 * i : ℕ) * Z ^ τ ≤ height :=
      hfreq d hd' i hi
    obtain ⟨hconst0, hconstP, hconstI, hconstI0⟩ := fiberConstant_bounds C_mom height K₀ hC_mom hh0 hK₀
    -- Bound every non-empty sub-fiber `B.fiber bin_f label J K hne` using `subset_slot_fiber_count`.
    let exp_fib : ℝ := Budget.rowCount δ x_rem + (160 * D_dual.ε + 4 * D_dual.t + subDelta) +
      6 * D_dual.t + 5 * D_dual.ε
    have hε_t : (4 / 9) * D_dual.ε ≤ D_dual.t := by
      have hr_le : D_dual.rmin ≤ 1 := by
        have hb0 := (D_dual.slots_bounds ⟨0, D_dual.slots_pos⟩).2
        linarith [D_dual.t_small]
      nlinarith [D_dual.epsilon_gap, D_dual.epsilon_pos, D_dual.t_pos]
    have hsub_fiber : ∀ bin_f label J K, ∀ hne : (B.fiberRows bin_f label J K).Nonempty,
        ((B.fiber bin_f label J K hne).rows.card : ℝ) ≤
          fiberConstant C_mom height K₀ * U_d ^ exp_fib := by
      intro bin_f label J K hne
      have hmom_sub := hmomZ.2 rows_bin (fun u hu => (hrows u hu).1) d (by linarith)
        a tstar (Z ^ τ) ((Z ^ d) ^ (τ / (2 * (4 / 5 : ℝ)))) i B
        (by rw [hBr]) hBd hW hWidths hUpper (by rw [hExt]; exact hzre)
        (by rw [hExt]; exact hzim) bin_f label J K hne
      have hgeom := (B.fiber bin_f label J K hne).lengths hU_gt1
      have hr0 : 0 ≤ (B.fiber bin_f label J K hne).r := by
        linarith [hgeom.2.2.2.1, ht_bounds.1, D_dual.epsilon_small]
      have hr2 : (B.fiber bin_f label J K hne).r ≤ 2 := by
        linarith [hgeom.2.1, ht_bounds.2, D_dual.epsilon_small]
      have hsub_rows : (B.fiber bin_f label J K hne).rows ⊆ rows_bin := by
        intro u hu
        have huB : u ∈ B.rows := batch_fiber_rows_subset B bin_f label J K hne hu
        rwa [hBr] at huB
      have hi0 := hampZ d hd (B.fiber bin_f label J K hne).rows
        (B.fiber bin_f label J K hne).family a D_dual.ε tstar (Z ^ τ)
        ((Z ^ d) ^ (τ / (2 * (4 / 5 : ℝ)))) i hU_gt1 (by linarith)
        (fun u => ((B.fiber bin_f label J K hne).witness u).toWitness)
        (B.fiber bin_f label J K hne).label (B.fiber bin_f label J K hne).left
        (B.fiber bin_f label J K hne).right
        (B.fiber bin_f label J K hne).fixed_label (B.fiber bin_f label J K hne).fixed_left
        (B.fiber bin_f label J K hne).fixed_right hr0 hr2
        (B.fiber bin_f label J K hne).rowData (B.fiber bin_f label J K hne).reverse
        C_mom height hC_mom hh0 hf_le
        (B.fiber bin_f label J K hne).row_norm (B.fiber bin_f label J K hne).row_coeff
        hmom_sub.inverse_raw
      have hS_sub : S_rem' ⊆ (B.fiber bin_f label J K hne).slots := by
        change S_rem' ⊆ B.slots; rw [hSlots]; exact Finset.subset_univ _
      have hw_eq : (B.fiber bin_f label J K hne).widths = widths_d := hWidths
      have hp_eq : (B.fiber bin_f label J K hne).profile = WC := hW
      have hu_eq : (B.fiber bin_f label J K hne).upper = (fun _ => 2) := hUpper
      have he_eq : (B.fiber bin_f label J K hne).external = zs := hExt
      exact subset_slot_fiber_count (B.fiber bin_f label J K hne) hmom_sub hi0
        hU_gt1 hδ_lo hδ_hi D_dual.epsilon_pos.le D_dual.epsilon_small
        D_dual.t_pos hε_t hC_mom hh0 hf_le hK₀ hx0 hx1 hqx ht_bounds.1 ht_bounds.2 hcross_eq
        S_rem' hS_sub (fun s _ => by rw [hw_eq]; exact hw_pos s)
        (fun s _ => by rw [hw_eq]; exact hw_mesh s) (by rw [hw_eq]; exact hL_rem)
        (binValue S_rem' ((2 * a - 1) / 2) D_dual.t bin_rem)
        (by rw [hw_eq])
        (fun u hu s hs => by
          rw [hp_eq, hu_eq, hw_eq, he_eq]
          exact hbins_rem u (hsub_rows hu) s hs)
        (by rw [hw_eq]; exact hsup_inv)
        (by rw [hw_eq]; exact hsup_plain)
    -- Sum `hsub_fiber` over `(bin_f, label, J, K)` via `batch_const_card_bound` + `hpref`.
    have hB_card := batch_const_card_bound (Label := Label) B
      (fiberConstant C_mom height K₀) exp_fib hconst0 hU_pos hsub_fiber
    have hpref_val := hpref d hd hd' C0 a D_dual.ε tstar (Z ^ τ)
      ((Z ^ d) ^ (τ / (2 * (4 / 5 : ℝ)))) i hC0.le ha_hi B
      (by rw [hSlots]; simp) hBin
    have hcard_le : (rows_bin.card : ℝ) ≤
        (K_pref * C0 * Z ^ (D_dual.t + 2 * τ + D_dual.t)) * U_d ^ exp_fib := by
      rw [← hBr]
      exact hB_card.trans (mul_le_mul_of_nonneg_right hpref_val (Real.rpow_nonneg hU_pos.le _))
    calc (rows_bin.card : ℝ)
        ≤ (K_pref * C0 * Z ^ (D_dual.t + 2 * τ + D_dual.t)) * U_d ^ exp_fib := hcard_le
      _ = K_pref * C0 * (Z ^ (D_dual.t + 2 * τ + D_dual.t) * Z ^ (d * exp_fib)) := by
          dsimp [U_d]; rw [← Real.rpow_mul hZp.le]; ring
      _ = K_pref * C0 * Z ^ ((D_dual.t + 2 * τ + D_dual.t) + d * exp_fib) := by
          rw [← Real.rpow_add hZp]
      _ ≤ K_pref * C0 * Z ^ (d * Budget.rowCount δ x_rem + 200 * D_dual.ε + 20 * D_dual.t + subDelta) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK_pref.le hC0.le)
          apply Real.rpow_le_rpow_of_exponent_le hZ1.le
          dsimp [exp_fib]
          have herr_nn : 0 ≤ 165 * D_dual.ε + 10 * D_dual.t + subDelta := by
            have := D_dual.epsilon_pos; have := D_dual.t_pos; have := subDelta_pos; positivity
          have hd_err : d * (165 * D_dual.ε + 10 * D_dual.t + subDelta) ≤
              (4 / 5) * (165 * D_dual.ε + 10 * D_dual.t + subDelta) :=
            mul_le_mul_of_nonneg_right hd' herr_nn
          linarith [hτ2, D_dual.epsilon_pos, D_dual.t_pos, subDelta_pos]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hrows_ne]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

/-! ### Part II: Exact prime-slot & target-row dictionary and `markedRadial` Fourier decoupling -/

section DictionaryAndFourier

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

/-- Sharpened `disjTupleSum_l2_le_factored` retaining the collision scale drop
`X' ≤ X₀ / ∏ i ∈ (S_sub ∪ T_ext) \ T', Z_slot i`: every slot peeled along the collision branch
simultaneously leaves `T'` and divides `X₀` by `‖ringComplex (p q)‖^2 ≥ Z_slot i`! -/
theorem disjTupleSum_l2_le_factored_sharp
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hinj_p : Function.Injective p)
    (pool P_punc : Finset ι) (Ψ₀ : O →* ℂ) (hΨ1 : ∀ u, ‖Ψ₀ u‖ ≤ 1)
    (S_sub T_ext : Finset σ) (hST_disj : Disjoint S_sub T_ext)
    (lists : σ → Finset ι)
    (hlists_pool : ∀ i ∈ S_sub, lists i ⊆ pool \ P_punc)
    (hdisj : ((S_sub ∪ T_ext : Finset σ) : Set σ).PairwiseDisjoint lists)
    (a : σ → ι → ℂ) (ha : ∀ i ∈ S_sub, ∀ q ∈ lists i, ‖a i q‖ ≤ 1)
    (Z_slot : σ → ℝ) (hZ1 : ∀ i ∈ S_sub ∪ T_ext, 1 ≤ Z_slot i)
    (hZ_lo : ∀ i ∈ S_sub, ∀ q ∈ lists i, Z_slot i ≤ ‖ringComplex (p q)‖ ^ 2)
    (hZ_hi : ∀ i ∈ S_sub, ∀ q ∈ lists i, ‖ringComplex (p q)‖ ^ 2 ≤ 2 * Z_slot i)
    (V₀ : ℝ → ℂ) {b_hi : ℝ} (hb : ∀ y, V₀ y ≠ 0 → y ≤ b_hi)
    (S_w : Finset O) {B_sup : ℝ} (hB : 0 ≤ B_sup) (X₀ : ℝ) (hX₀ : 0 < X₀)
    (hfactored : ∀ T' : Finset σ, T' ⊆ S_sub ∪ T_ext → ∀ X' : ℝ, 0 < X' →
      X' ≤ X₀ / (∏ i ∈ (S_sub ∪ T_ext) \ T', Z_slot i) →
      (∑ w ∈ S_w, (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
        ‖inputConjugateRow p (fun j => complexSexticChar (Ideal.span {p j}) (hg j))
            pool Ψ₀ 1 1 1 (fun U => V₀ (primeProductNorm p U / X')) w *
          ∏ j ∈ T', slotCharSum p hg lists a Ψ₀ j w‖ ^ 2) ≤ B_sup) :
    (∑ w ∈ S_w, (X₀ * ∏ i ∈ S_sub ∪ T_ext, Z_slot i)⁻¹ *
      ‖disjTupleSum p hg (pool \ P_punc) S_sub lists a Ψ₀ V₀ X₀ w *
        ∏ j ∈ T_ext, slotCharSum p hg lists a Ψ₀ j w‖ ^ 2) ≤
      (307330 : ℝ) ^ S_sub.card * (16 : ℝ) ^ P_punc.card * B_sup := by
  let χ := fun j => complexSexticChar (Ideal.span {p j}) (hg j)
  revert P_punc T_ext X₀
  induction S_sub using Finset.induction_on with
  | empty =>
    intro P_punc T_ext hST_disj hlists_pool hdisj hZ1 X₀ hX₀ hfactored
    simp only [Finset.empty_union, Finset.card_empty, pow_zero, one_mul] at hfactored ⊢
    have hempty (w' : O) := disjTupleSum_empty p hg (pool \ P_punc) lists a Ψ₀ V₀ X₀ w'
    simp_rw [hempty]
    let wt : O → ℝ := fun w =>
      (∏ j ∈ T_ext, Z_slot j)⁻¹ * ‖∏ j ∈ T_ext, slotCharSum p hg lists a Ψ₀ j w‖ ^ 2
    have hZprod_pos : 0 < ∏ j ∈ T_ext, Z_slot j :=
      Finset.prod_pos (fun j hj => zero_lt_one.trans_le (hZ1 j (Finset.mem_union_right _ hj)))
    have hwt_nn : ∀ w ∈ S_w, 0 ≤ wt w := fun _ _ =>
      mul_nonneg (inv_nonneg.mpr hZprod_pos.le) (sq_nonneg _)
    have hrew (X' : ℝ) (w : O) :
        (X' * ∏ j ∈ T_ext, Z_slot j)⁻¹ *
          ‖inputConjugateRow p χ (pool \ P_punc) Ψ₀ 1 1 1
              (fun U => V₀ (primeProductNorm p U / X')) w *
            ∏ j ∈ T_ext, slotCharSum p hg lists a Ψ₀ j w‖ ^ 2 =
        wt w * ((X')⁻¹ * ‖inputConjugateRow p χ (pool \ P_punc) Ψ₀ 1 1 1
              (fun U => V₀ (primeProductNorm p U / X')) w‖ ^ 2) := by
      dsimp [wt]; rw [mul_inv, norm_mul, mul_pow]; ring
    have hrew0 (X' : ℝ) (w : O) :
        wt w * ((X')⁻¹ * ‖inputConjugateRow p χ pool Ψ₀ 1 1 1
              (fun U => V₀ (primeProductNorm p U / X')) w‖ ^ 2) =
        (X' * ∏ j ∈ T_ext, Z_slot j)⁻¹ *
          ‖inputConjugateRow p χ pool Ψ₀ 1 1 1
              (fun U => V₀ (primeProductNorm p U / X')) w *
            ∏ j ∈ T_ext, slotCharSum p hg lists a Ψ₀ j w‖ ^ 2 := by
      dsimp [wt]; rw [mul_inv, norm_mul, mul_pow]; ring
    rw [Finset.sum_congr rfl (fun w _ => hrew X₀ w)]
    apply inputConjugateRow_unpuncture_weighted_l2_le p hp hg pool P_punc Ψ₀ hΨ1 V₀ hb
      S_w wt hwt_nn hB X₀ hX₀
    intro X' hX' hX'_le
    rw [Finset.sum_congr rfl (fun w _ => hrew0 X' w)]
    exact hfactored T_ext Finset.Subset.rfl X' hX' (by simpa using hX'_le)
  | @insert i₀ S₀ hi₀ ih =>
    intro P_punc T_ext hST_disj hlists_pool hdisj hZ1 X₀ hX₀ hfactored
    have hi₀_not_T : i₀ ∉ T_ext :=
      Finset.disjoint_left.mp hST_disj (Finset.mem_insert_self i₀ S₀)
    have hS₀T_disj : Disjoint S₀ T_ext :=
      Disjoint.mono_left (Finset.subset_insert i₀ S₀) hST_disj
    have hS₀_insT_disj : Disjoint S₀ (insert i₀ T_ext) :=
      Finset.disjoint_insert_right.mpr ⟨hi₀, hS₀T_disj⟩
    have hunion_eq : insert i₀ S₀ ∪ T_ext = S₀ ∪ insert i₀ T_ext := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    have hpool_i₀ : lists i₀ ⊆ pool \ P_punc :=
      hlists_pool i₀ (Finset.mem_insert_self i₀ S₀)
    have hdisj_i₀ : ∀ i ∈ S₀, Disjoint (lists i₀) (lists i) := fun i hi =>
      hdisj (Finset.mem_union_left _ (Finset.mem_insert_self i₀ S₀))
        (Finset.mem_union_left _ (Finset.mem_insert_of_mem hi))
        (fun he => hi₀ (he ▸ hi))
    have hZi₀_1 : 1 ≤ Z_slot i₀ :=
      hZ1 i₀ (Finset.mem_union_left _ (Finset.mem_insert_self i₀ S₀))
    have hZi₀_pos : 0 < Z_slot i₀ := zero_lt_one.trans_le hZi₀_1
    have hZprod_S₀T : 0 < ∏ i ∈ S₀ ∪ T_ext, Z_slot i :=
      Finset.prod_pos (fun i hi => zero_lt_one.trans_le (hZ1 i (by
        rcases Finset.mem_union.mp hi with h1 | h2
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem h1)
        · exact Finset.mem_union_right _ h2)))
    have hprod_split : (∏ i ∈ insert i₀ S₀ ∪ T_ext, Z_slot i) =
        Z_slot i₀ * ∏ i ∈ S₀ ∪ T_ext, Z_slot i := by
      have h1 : insert i₀ S₀ ∪ T_ext = insert i₀ (S₀ ∪ T_ext) := Finset.insert_union i₀ S₀ T_ext
      have hnot : i₀ ∉ S₀ ∪ T_ext := fun hm => by
        rcases Finset.mem_union.mp hm with hS | hT
        · exact hi₀ hS
        · exact hi₀_not_T hT
      rw [h1, Finset.prod_insert hnot]
    have hcard_L : ((lists i₀).card : ℝ) ≤ 98 * Z_slot i₀ := by
      have h1 := card_finset_injective_norm_sq_le_49_mul p hinj_p (lists i₀)
        (R := 2 * Z_slot i₀) (by linarith)
        (hZ_hi i₀ (Finset.mem_insert_self i₀ S₀))
      linarith
    let P_ext : O → ℂ := fun w => ∏ j ∈ T_ext, slotCharSum p hg lists a Ψ₀ j w
    have hpt (w : O) :
        (X₀ * ∏ i ∈ insert i₀ S₀ ∪ T_ext, Z_slot i)⁻¹ *
            ‖disjTupleSum p hg (pool \ P_punc) (insert i₀ S₀) lists a Ψ₀ V₀ X₀ w * P_ext w‖ ^ 2 ≤
          2 * ((X₀ * ∏ i ∈ S₀ ∪ insert i₀ T_ext, Z_slot i)⁻¹ *
            ‖disjTupleSum p hg (pool \ P_punc) S₀ lists a Ψ₀ V₀ X₀ w *
              ∏ j ∈ insert i₀ T_ext, slotCharSum p hg lists a Ψ₀ j w‖ ^ 2) +
          2 * ((lists i₀).card : ℝ) * (Z_slot i₀)⁻¹ ^ 2 *
            ∑ q ∈ lists i₀,
              (((X₀ / ‖ringComplex (p q)‖ ^ 2) * ∏ i ∈ S₀ ∪ T_ext, Z_slot i)⁻¹ *
                ‖disjTupleSum p hg (pool \ insert q P_punc) S₀ lists a Ψ₀ V₀
                    (X₀ / ‖ringComplex (p q)‖ ^ 2) w * P_ext w‖ ^ 2) := by
      rw [disjTupleSum_insert p hg (pool \ P_punc) hi₀ lists hpool_i₀ hdisj_i₀ a Ψ₀ V₀ X₀ w,
        sub_mul]
      set A := (-slotCharSum p hg lists a Ψ₀ i₀ w) *
        disjTupleSum p hg (pool \ P_punc) S₀ lists a Ψ₀ V₀ X₀ w * P_ext w
      set B := (∑ q ∈ lists i₀,
        (a i₀ q * (Ψ₀ (p q)) ^ 2 * (star (primeSubsetRow p χ {q} w)) ^ 2) *
          disjTupleSum p hg ((pool \ P_punc).erase q) S₀ lists a Ψ₀ V₀
            (X₀ / ‖ringComplex (p q)‖ ^ 2) w) * P_ext w
      have h2ab : ‖A - B‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := by
        have ht := norm_sub_le A B
        have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
        nlinarith [sq_nonneg (‖A‖ - ‖B‖)]
      have hA_eq : ‖A‖ = ‖disjTupleSum p hg (pool \ P_punc) S₀ lists a Ψ₀ V₀ X₀ w *
          ∏ j ∈ insert i₀ T_ext, slotCharSum p hg lists a Ψ₀ j w‖ := by
        dsimp [A, P_ext]
        rw [Finset.prod_insert hi₀_not_T,
          show (-slotCharSum p hg lists a Ψ₀ i₀ w) *
              disjTupleSum p hg (pool \ P_punc) S₀ lists a Ψ₀ V₀ X₀ w *
              ∏ j ∈ T_ext, slotCharSum p hg lists a Ψ₀ j w =
            -(disjTupleSum p hg (pool \ P_punc) S₀ lists a Ψ₀ V₀ X₀ w *
              (slotCharSum p hg lists a Ψ₀ i₀ w *
                ∏ j ∈ T_ext, slotCharSum p hg lists a Ψ₀ j w)) by ring,
          norm_neg]
      have hB_sq : ‖B‖ ^ 2 ≤ ((lists i₀).card : ℝ) *
          ∑ q ∈ lists i₀,
            ‖disjTupleSum p hg (pool \ insert q P_punc) S₀ lists a Ψ₀ V₀
              (X₀ / ‖ringComplex (p q)‖ ^ 2) w * P_ext w‖ ^ 2 := by
        dsimp [B]
        rw [Finset.sum_mul]
        apply (norm_sum_sq_le_card_sum_norm_sq (lists i₀) _).trans
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum; intro q hq
        have hsdiff_q : (pool \ P_punc).erase q = pool \ insert q P_punc := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]; tauto
        rw [hsdiff_q, mul_assoc, norm_mul, mul_pow]
        have hβ1 : ‖a i₀ q * (Ψ₀ (p q)) ^ 2 * (star (primeSubsetRow p χ {q} w)) ^ 2‖ ≤ 1 := by
          have h1 : ‖a i₀ q‖ ≤ 1 := ha i₀ (Finset.mem_insert_self i₀ S₀) q hq
          have h2 : ‖(Ψ₀ (p q)) ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hΨ1 _)
          have h3 : ‖(star (primeSubsetRow p χ {q} w)) ^ 2‖ ≤ 1 := by
            rw [norm_pow, norm_star]; exact pow_le_one₀ (norm_nonneg _) (primeSubsetRow_norm_le_one p χ {q} w)
          rw [norm_mul, norm_mul]
          exact (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3
            (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)).trans_eq (by norm_num)
        exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) hβ1)
      have hinner_B :
          (∑ q ∈ lists i₀,
            (X₀ * (Z_slot i₀ * ∏ i ∈ S₀ ∪ T_ext, Z_slot i))⁻¹ *
              ‖disjTupleSum p hg (pool \ insert q P_punc) S₀ lists a Ψ₀ V₀
                (X₀ / ‖ringComplex (p q)‖ ^ 2) w * P_ext w‖ ^ 2) ≤
          (Z_slot i₀)⁻¹ ^ 2 *
            ∑ q ∈ lists i₀,
              (((X₀ / ‖ringComplex (p q)‖ ^ 2) * ∏ i ∈ S₀ ∪ T_ext, Z_slot i)⁻¹ *
                ‖disjTupleSum p hg (pool \ insert q P_punc) S₀ lists a Ψ₀ V₀
                  (X₀ / ‖ringComplex (p q)‖ ^ 2) w * P_ext w‖ ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum; intro q hq
        rw [← mul_assoc ((Z_slot i₀)⁻¹ ^ 2)]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have hZq : Z_slot i₀ ≤ ‖ringComplex (p q)‖ ^ 2 :=
          hZ_lo i₀ (Finset.mem_insert_self i₀ S₀) q hq
        have hNq_pos : 0 < ‖ringComplex (p q)‖ ^ 2 := hZi₀_pos.trans_le hZq
        have h1 : (Z_slot i₀)⁻¹ ^ 2 * ((X₀ / ‖ringComplex (p q)‖ ^ 2) * ∏ i ∈ S₀ ∪ T_ext, Z_slot i)⁻¹ =
            (‖ringComplex (p q)‖ ^ 2 / Z_slot i₀) *
              (X₀ * (Z_slot i₀ * ∏ i ∈ S₀ ∪ T_ext, Z_slot i))⁻¹ := by
          field_simp [hZi₀_pos.ne', hX₀.ne', hNq_pos.ne', hZprod_S₀T.ne']
        rw [h1]
        exact le_mul_of_one_le_left
          (inv_nonneg.mpr (mul_pos hX₀ (mul_pos hZi₀_pos hZprod_S₀T)).le)
          ((one_le_div hZi₀_pos).mpr hZq)
      have hscale_B : (X₀ * ∏ i ∈ insert i₀ S₀ ∪ T_ext, Z_slot i)⁻¹ * ‖B‖ ^ 2 ≤
          ((lists i₀).card : ℝ) * (Z_slot i₀)⁻¹ ^ 2 *
            ∑ q ∈ lists i₀,
              (((X₀ / ‖ringComplex (p q)‖ ^ 2) * ∏ i ∈ S₀ ∪ T_ext, Z_slot i)⁻¹ *
                ‖disjTupleSum p hg (pool \ insert q P_punc) S₀ lists a Ψ₀ V₀
                    (X₀ / ‖ringComplex (p q)‖ ^ 2) w * P_ext w‖ ^ 2) := by
        calc (X₀ * ∏ i ∈ insert i₀ S₀ ∪ T_ext, Z_slot i)⁻¹ * ‖B‖ ^ 2
            ≤ (X₀ * (Z_slot i₀ * ∏ i ∈ S₀ ∪ T_ext, Z_slot i))⁻¹ *
                (((lists i₀).card : ℝ) * ∑ q ∈ lists i₀,
                  ‖disjTupleSum p hg (pool \ insert q P_punc) S₀ lists a Ψ₀ V₀
                    (X₀ / ‖ringComplex (p q)‖ ^ 2) w * P_ext w‖ ^ 2) := by
              rw [hprod_split]
              exact mul_le_mul_of_nonneg_left hB_sq
                (inv_nonneg.mpr (mul_pos hX₀ (mul_pos hZi₀_pos hZprod_S₀T)).le)
          _ = ((lists i₀).card : ℝ) * ∑ q ∈ lists i₀,
                ((X₀ * (Z_slot i₀ * ∏ i ∈ S₀ ∪ T_ext, Z_slot i))⁻¹ *
                  ‖disjTupleSum p hg (pool \ insert q P_punc) S₀ lists a Ψ₀ V₀
                    (X₀ / ‖ringComplex (p q)‖ ^ 2) w * P_ext w‖ ^ 2) := by
              rw [← mul_assoc, mul_comm _ ((lists i₀).card : ℝ), mul_assoc, Finset.mul_sum]
          _ ≤ ((lists i₀).card : ℝ) * ((Z_slot i₀)⁻¹ ^ 2 *
                ∑ q ∈ lists i₀,
                  (((X₀ / ‖ringComplex (p q)‖ ^ 2) * ∏ i ∈ S₀ ∪ T_ext, Z_slot i)⁻¹ *
                    ‖disjTupleSum p hg (pool \ insert q P_punc) S₀ lists a Ψ₀ V₀
                      (X₀ / ‖ringComplex (p q)‖ ^ 2) w * P_ext w‖ ^ 2)) :=
              mul_le_mul_of_nonneg_left hinner_B (Nat.cast_nonneg _)
          _ = _ := by ring
      have hscale_pos : 0 ≤ (X₀ * ∏ i ∈ insert i₀ S₀ ∪ T_ext, Z_slot i)⁻¹ := by
        rw [hprod_split]; exact inv_nonneg.mpr (mul_pos hX₀ (mul_pos hZi₀_pos hZprod_S₀T)).le
      have hstep1 := mul_le_mul_of_nonneg_left h2ab hscale_pos
      have hA_rew : (X₀ * ∏ i ∈ insert i₀ S₀ ∪ T_ext, Z_slot i)⁻¹ * (2 * ‖A‖ ^ 2) =
          2 * ((X₀ * ∏ i ∈ S₀ ∪ insert i₀ T_ext, Z_slot i)⁻¹ *
            ‖disjTupleSum p hg (pool \ P_punc) S₀ lists a Ψ₀ V₀ X₀ w *
              ∏ j ∈ insert i₀ T_ext, slotCharSum p hg lists a Ψ₀ j w‖ ^ 2) := by
        rw [hA_eq, hunion_eq]; ring
      have hB_rew : (X₀ * ∏ i ∈ insert i₀ S₀ ∪ T_ext, Z_slot i)⁻¹ * (2 * ‖B‖ ^ 2) =
          2 * ((X₀ * ∏ i ∈ insert i₀ S₀ ∪ T_ext, Z_slot i)⁻¹ * ‖B‖ ^ 2) := by ring
      rw [mul_add, hA_rew, hB_rew] at hstep1
      linarith [hstep1, hscale_B]
    have hterm1 :
        (∑ w ∈ S_w, (X₀ * ∏ i ∈ S₀ ∪ insert i₀ T_ext, Z_slot i)⁻¹ *
          ‖disjTupleSum p hg (pool \ P_punc) S₀ lists a Ψ₀ V₀ X₀ w *
            ∏ j ∈ insert i₀ T_ext, slotCharSum p hg lists a Ψ₀ j w‖ ^ 2) ≤
        (307330 : ℝ) ^ S₀.card * (16 : ℝ) ^ P_punc.card * B_sup := by
      exact ih
        (fun i hi => ha i (Finset.mem_insert_of_mem hi))
        (fun i hi => hZ_lo i (Finset.mem_insert_of_mem hi))
        (fun i hi => hZ_hi i (Finset.mem_insert_of_mem hi))
        P_punc (insert i₀ T_ext) hS₀_insT_disj
        (fun i hi => hlists_pool i (Finset.mem_insert_of_mem hi))
        (by rw [← hunion_eq]; exact hdisj)
        (by rw [← hunion_eq]; exact hZ1)
        X₀ hX₀
        (by rw [← hunion_eq]; exact hfactored)
    have hterm2 : ∀ q ∈ lists i₀,
        (∑ w ∈ S_w, ((X₀ / ‖ringComplex (p q)‖ ^ 2) * ∏ i ∈ S₀ ∪ T_ext, Z_slot i)⁻¹ *
          ‖disjTupleSum p hg (pool \ insert q P_punc) S₀ lists a Ψ₀ V₀
              (X₀ / ‖ringComplex (p q)‖ ^ 2) w * P_ext w‖ ^ 2) ≤
        (307330 : ℝ) ^ S₀.card * (16 : ℝ) ^ (P_punc.card + 1) * B_sup := by
      intro q hq
      have hq_not_P : q ∉ P_punc := (Finset.mem_sdiff.mp (hpool_i₀ hq)).2
      have hZq : Z_slot i₀ ≤ ‖ringComplex (p q)‖ ^ 2 :=
        hZ_lo i₀ (Finset.mem_insert_self i₀ S₀) q hq
      have hNq1 : 1 ≤ ‖ringComplex (p q)‖ ^ 2 := hZi₀_1.trans hZq
      have hNq_pos : 0 < ‖ringComplex (p q)‖ ^ 2 := zero_lt_one.trans_le hNq1
      have hsub_union : S₀ ∪ T_ext ⊆ insert i₀ S₀ ∪ T_ext :=
        Finset.union_subset_union_left (Finset.subset_insert i₀ S₀)
      have hlists_ins : ∀ i ∈ S₀, lists i ⊆ pool \ insert q P_punc := by
        intro i hi x hx
        have hx0 := hlists_pool i (Finset.mem_insert_of_mem hi) hx
        have hxq : x ≠ q := fun he =>
          Finset.disjoint_left.mp (hdisj_i₀ i hi) hq (he ▸ hx)
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx0).1,
          fun hm => (Finset.mem_insert.mp hm).elim hxq (Finset.mem_sdiff.mp hx0).2⟩
      rw [← Finset.card_insert_of_notMem hq_not_P]
      exact ih
        (fun i hi => ha i (Finset.mem_insert_of_mem hi))
        (fun i hi => hZ_lo i (Finset.mem_insert_of_mem hi))
        (fun i hi => hZ_hi i (Finset.mem_insert_of_mem hi))
        (insert q P_punc) T_ext hS₀T_disj hlists_ins
        (hdisj.subset (Finset.coe_subset.mpr hsub_union))
        (fun i hi => hZ1 i (hsub_union hi))
        (X₀ / ‖ringComplex (p q)‖ ^ 2) (div_pos hX₀ hNq_pos)
        (fun T' hT' X' hX' hX'_le => by
          have hi₀_not_T' : i₀ ∉ T' := fun hm => by
            rcases Finset.mem_union.mp (hT' hm) with hS | hT
            · exact hi₀ hS
            · exact hi₀_not_T hT
          have hsdiff_ins : (insert i₀ S₀ ∪ T_ext) \ T' = insert i₀ ((S₀ ∪ T_ext) \ T') := by
            ext x
            simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert]
            constructor
            · rintro ⟨(rfl | hS) | hT, hn⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨Or.inl hS, hn⟩
              · exact Or.inr ⟨Or.inr hT, hn⟩
            · rintro (rfl | ⟨hST, hn⟩)
              · exact ⟨Or.inl (Or.inl rfl), hi₀_not_T'⟩
              · exact ⟨hST.elim (fun hS => Or.inl (Or.inr hS)) Or.inr, hn⟩
          have hi₀_not_sdiff : i₀ ∉ (S₀ ∪ T_ext) \ T' := fun hm => by
            rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hm).1 with hS | hT
            · exact hi₀ hS
            · exact hi₀_not_T hT
          have hP_pos : 0 < ∏ i ∈ (S₀ ∪ T_ext) \ T', Z_slot i :=
            Finset.prod_pos (fun i hi => zero_lt_one.trans_le
              (hZ1 i (hsub_union (Finset.mem_sdiff.mp hi).1)))
          apply hfactored T' (hT'.trans hsub_union) X' hX'
          rw [hsdiff_ins, Finset.prod_insert hi₀_not_sdiff, ← div_div]
          exact hX'_le.trans (div_le_div_of_nonneg_right
            (div_le_div_of_nonneg_left hX₀.le hZi₀_pos hZq) hP_pos.le))
    rw [Finset.card_insert_of_notMem hi₀, pow_succ']
    have hM0 : 0 ≤ (307330 : ℝ) ^ S₀.card * (16 : ℝ) ^ P_punc.card * B_sup := by positivity
    calc
      (∑ w ∈ S_w, (X₀ * ∏ i ∈ insert i₀ S₀ ∪ T_ext, Z_slot i)⁻¹ *
          ‖disjTupleSum p hg (pool \ P_punc) (insert i₀ S₀) lists a Ψ₀ V₀ X₀ w * P_ext w‖ ^ 2)
        ≤ 2 * (∑ w ∈ S_w, (X₀ * ∏ i ∈ S₀ ∪ insert i₀ T_ext, Z_slot i)⁻¹ *
            ‖disjTupleSum p hg (pool \ P_punc) S₀ lists a Ψ₀ V₀ X₀ w *
              ∏ j ∈ insert i₀ T_ext, slotCharSum p hg lists a Ψ₀ j w‖ ^ 2) +
          2 * ((lists i₀).card : ℝ) * (Z_slot i₀)⁻¹ ^ 2 *
            ∑ q ∈ lists i₀,
              ∑ w ∈ S_w, ((X₀ / ‖ringComplex (p q)‖ ^ 2) * ∏ i ∈ S₀ ∪ T_ext, Z_slot i)⁻¹ *
                ‖disjTupleSum p hg (pool \ insert q P_punc) S₀ lists a Ψ₀ V₀
                    (X₀ / ‖ringComplex (p q)‖ ^ 2) w * P_ext w‖ ^ 2 := by
            refine (Finset.sum_le_sum (fun w _ => hpt w)).trans_eq ?_
            rw [Finset.sum_add_distrib]
            congr 1
            · rw [← Finset.mul_sum]
            · rw [← Finset.mul_sum, Finset.sum_comm]
        _ ≤ 2 * ((307330 : ℝ) ^ S₀.card * (16 : ℝ) ^ P_punc.card * B_sup) +
              2 * ((lists i₀).card : ℝ) * (Z_slot i₀)⁻¹ ^ 2 *
                ∑ _q ∈ lists i₀,
                  ((307330 : ℝ) ^ S₀.card * (16 : ℝ) ^ (P_punc.card + 1) * B_sup) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hterm1 (by norm_num)
            · apply mul_le_mul_of_nonneg_left
                (Finset.sum_le_sum (fun q hq => hterm2 q hq))
              positivity
        _ = 2 * ((307330 : ℝ) ^ S₀.card * (16 : ℝ) ^ P_punc.card * B_sup) +
              32 * (((lists i₀).card : ℝ) * (Z_slot i₀)⁻¹) ^ 2 *
                ((307330 : ℝ) ^ S₀.card * (16 : ℝ) ^ P_punc.card * B_sup) := by
            rw [Finset.sum_const, nsmul_eq_mul, pow_succ']; ring
        _ ≤ 2 * ((307330 : ℝ) ^ S₀.card * (16 : ℝ) ^ P_punc.card * B_sup) +
              32 * 98 ^ 2 * ((307330 : ℝ) ^ S₀.card * (16 : ℝ) ^ P_punc.card * B_sup) := by
            have hratio : ((lists i₀).card : ℝ) * (Z_slot i₀)⁻¹ ≤ 98 := by
              rw [← div_eq_mul_inv, div_le_iff₀ hZi₀_pos]; exact hcard_L
            have hsq_r : (((lists i₀).card : ℝ) * (Z_slot i₀)⁻¹) ^ 2 ≤ 98 ^ 2 :=
              pow_le_pow_left₀ (by positivity) hratio 2
            have hmul_r := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsq_r (by norm_num : (0 : ℝ) ≤ 32)) hM0
            linarith [hmul_r]
        _ = (307330 : ℝ) * (307330 : ℝ) ^ S₀.card * (16 : ℝ) ^ P_punc.card * B_sup := by ring

/-- Multiplying `primeProfile V X ζ P` by `kernelLogPhase t (Real.log (P.absNorm / X))` shifts
`ζ` to `ζ + 2 π t i` while preserving `Re = ζ.re`. -/
lemma primeProfile_mul_kernelLogPhase (V : ℝ → ℂ) {X : ℝ} (hX : 0 < X)
    (ζ : ℂ) (t : ℝ) {P : Ideal O} (hP : P ≠ 0) :
    primeProfile V X ζ P * kernelLogPhase t (Real.log ((P.absNorm : ℝ) / X)) =
      primeProfile V X (ζ + ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) P := by
  have hN_pos : 0 < (P.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP)
  have hy : 0 < (P.absNorm : ℝ) / X := div_pos hN_pos hX
  have hy_ne : (((P.absNorm : ℝ) / X : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hph : kernelLogPhase t (Real.log ((P.absNorm : ℝ) / X)) =
      (((P.absNorm : ℝ) / X : ℝ) : ℂ) ^ (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero hy_ne, ← Complex.ofReal_log hy.le]
    unfold kernelLogPhase
    congr 1; push_cast; ring
  unfold primeProfile
  rw [hph, mul_assoc, ← Complex.cpow_add _ _ hy_ne]
  congr 2; ring

omit [DecidableEq σ] in
/-- **Single-slot `slotCharSum` = `canonicalPrimeAmplitude` dictionary:**
When `2 * X_s ≤ Dpool` and `((deletedBase data).modulus.absNorm : ℝ) < X_s`, every prime in
`livePrimes F.modulus ⊤ F.W 2 X_s` belongs to `primePool F_pool` and `base (p q)` cancels
`star (idealCoeff (deletedBase data) q.val)` identically, turning `(X_s ^ (-1/2)) * slotCharSum`
into `canonicalPrimeAmplitude F.modulus ⊤ w F.W 2 X_s ζ_s`. -/
theorem slotCharSum_eq_canonicalPrimeAmplitude
    {Δ : ℝ} {D : Parameters.HighData Δ} (F : ProbeFinalAssembly.SourceData D)
    (data : RowData) (Dpool : ℕ)
    {X_s : ℝ} (hX_s : 0 < X_s) (hDpool : 2 * X_s ≤ (Dpool : ℝ))
    (hlarge : ((deletedBase data).modulus.absNorm : ℝ) < X_s)
    (ζ_s : ℂ) (hζ_re : ζ_s.re ≤ 1) (i : σ)
    (lists : σ → Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals
      (reflectionExcludedPrimes (InverseInitialExcludedPeriod.deletedPeriod (basePeriod data))) Dpool)))
    (a : σ → primePool (CanonicalRowCompletion.outsideSquarefreeIdeals
      (reflectionExcludedPrimes (InverseInitialExcludedPeriod.deletedPeriod (basePeriod data))) Dpool) → ℂ)
    (hlists_i : lists i = InverseInitialCommonLists.poolList
      (CanonicalRowCompletion.outsideSquarefreeIdeals
        (reflectionExcludedPrimes (InverseInitialExcludedPeriod.deletedPeriod (basePeriod data))) Dpool)
      (InverseInitialPhysicalSlots.livePrimes F.modulus ⊤ F.W 2 X_s))
    (ha_i : ∀ q ∈ lists i,
      a i q = primeProfile F.W X_s ζ_s q.val / star (idealCoeff (deletedBase data) q.val))
    (w : O) :
    let q_per := InverseInitialExcludedPeriod.deletedPeriod (basePeriod data)
    let F_pool := CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q_per) Dpool
    let hFa := CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q_per) Dpool
      (reflectionExcludedPrimes_bad q_per)
    letI : ∀ j : primePool F_pool, (Ideal.span {poolPrimary F_pool j}).IsMaximal :=
      fun j => by rw [poolPrimary_span F_pool hFa j]; infer_instance
    let base := elementCharacter
      (InverseInitialConjugateEnergy.conjugateIdealCharacter
        (idealCoeff (deletedBase data)).toMonoidHom)
    ((X_s ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      slotCharSum (poolPrimary F_pool) (poolPrimary_good F_pool hFa) lists a base i w =
      HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ w F.W 2 X_s ζ_s := by
  intro q_per F_pool hFa base
  letI : ∀ j : primePool F_pool, (Ideal.span {poolPrimary F_pool j}).IsMaximal :=
    fun j => by rw [poolPrimary_span F_pool hFa j]; infer_instance
  obtain ⟨_, hqset, _, _⟩ := DetectorDictionaryInverseRawConjugateGates.raw_conjugate_base_gates data
  let L_s := InverseInitialPhysicalSlots.livePrimes F.modulus ⊤ F.W 2 X_s
  have hL_in_pool : ∀ P ∈ L_s, P ∈ primePool F_pool := by
    intro P hP
    obtain ⟨hpr, hout, hne, _, _⟩ :=
      deleted_source_live_prime F data F.modulus ⊤ X_s hX_s ζ_s hζ_re hlarge P hP
    have hsup : CanonicalQuadraticSieve.Supported P := deletedBase_supported data P hne
    have hrat := F.complex_support (Finset.mem_filter.mp hP).2
    have hN_hi : (P.absNorm : ℝ) ≤ (Dpool : ℝ) :=
      ((div_le_iff₀ hX_s).mp hrat.2).trans hDpool
    have hN_lo : 1 ≤ P.absNorm :=
      Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hpr.ne_zero)
    have hout_q : InverseInitialExcludedPool.outside (reflectionExcludedPrimes q_per) P := by
      rwa [hqset]
    have hPF : P ∈ F_pool := Finset.mem_filter.mpr
      ⟨CanonicalRowCompletion.mem_outsideIdealsUpTo.mpr ⟨hN_lo, by exact_mod_cast hN_hi, hout_q⟩,
        hpr.squarefree⟩
    rw [CanonicalRowCompletion.mem_primePool_iff]
    refine ⟨P, hPF, ?_⟩
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hpr.irreducible, normalize_eq]
    exact Multiset.mem_singleton_self P
  have himg_lists : (lists i).image Subtype.val = L_s := by
    rw [hlists_i]
    ext P
    simp only [InverseInitialCommonLists.poolList, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨fun ⟨q, hqL, hqP⟩ => hqP ▸ hqL, fun hPL => ⟨⟨P, hL_in_pool P hPL⟩, hPL, rfl⟩⟩
  have hpow_X : ((X_s ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = ((X_s ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) := by
    congr 2; ring
  have hamp := InverseInitialPhysicalSlots.amplitude_eq_live F.modulus ⊤ w F.W 2 X_s 1 ζ_s hX_s
  simp only [Real.rpow_one] at hamp
  rw [hamp, hpow_X]
  congr 1
  unfold slotCharSum
  dsimp only
  dsimp only [L_s] at himg_lists
  rw [← himg_lists, Finset.sum_image (fun x _ y _ h => Subtype.ext h)]
  apply Finset.sum_congr rfl
  intro q hq
  have hqL : q.val ∈ L_s := by
    rw [hlists_i] at hq
    exact (Finset.mem_filter.mp hq).2
  obtain ⟨_, _, hne, _, _⟩ :=
    deleted_source_live_prime F data F.modulus ⊤ X_s hX_s ζ_s hζ_re hlarge q.val hqL
  have hspan_q : Ideal.span {poolPrimary F_pool q} = q.val := poolPrimary_span F_pool hFa q
  have hbase_q : base (poolPrimary F_pool q) = star (idealCoeff (deletedBase data) q.val) := by
    change InverseInitialConjugateEnergy.conjugateIdealCharacter
      (idealCoeff (deletedBase data)).toMonoidHom (Ideal.span {poolPrimary F_pool q}) = _
    rw [hspan_q]; rfl
  have hne_star : star (idealCoeff (deletedBase data) q.val) ≠ 0 := star_ne_zero.mpr hne
  have hpr_row : primeSubsetRow (poolPrimary F_pool)
      (fun j => complexSexticChar (Ideal.span {poolPrimary F_pool j}) (poolPrimary_good F_pool hFa j))
      {q} w = CanonicalRowCompletion.idealRowHom w q.val := by
    unfold primeSubsetRow
    rw [Finset.prod_singleton,
      ← CanonicalRowCompletion.idealRowHom_prime w (Ideal.span {poolPrimary F_pool q})
        (poolPrimary_good F_pool hFa q), hspan_q]
  rw [ha_i q hq, hbase_q, hpr_row, div_mul_cancel₀ _ hne_star]

/-- **Unpunctured `inputConjugateRow` = `targetRow` dyadic polynomial dictionary:**
When `b_hi * X' ≤ Dpool`, every squarefree ideal outside `excluded data` in the support of `V₀`
lies in `F_pool`, while `deletedBase data` vanishes outside `excluded data`, so
`((X') ^ (-1/2)) * inputConjugateRow ... Finset.univ base 1 1 1 ... u_free.val` equals
`HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u_free) true V₀ X' 0 0` identically! -/
theorem inputConjugateRow_eq_targetRow_polynomial
    (data : RowData) (Dpool : ℕ)
    (V₀ : ℝ → ℂ) {b_hi X' : ℝ} (hX' : 0 < X')
    (hb : ∀ y, V₀ y ≠ 0 → y ≤ b_hi) (hDpool : b_hi * X' ≤ (Dpool : ℝ))
    (u_free : FreeRow) :
    let q_per := InverseInitialExcludedPeriod.deletedPeriod (basePeriod data)
    let F_pool := CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q_per) Dpool
    let hFa := CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q_per) Dpool
      (reflectionExcludedPrimes_bad q_per)
    letI : ∀ j : primePool F_pool, (Ideal.span {poolPrimary F_pool j}).IsMaximal :=
      fun j => by rw [poolPrimary_span F_pool hFa j]; infer_instance
    let base := elementCharacter
      (InverseInitialConjugateEnergy.conjugateIdealCharacter
        (idealCoeff (deletedBase data)).toMonoidHom)
    (((X') ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      inputConjugateRow (poolPrimary F_pool)
        (fun j => complexSexticChar (Ideal.span {poolPrimary F_pool j}) (poolPrimary_good F_pool hFa j))
        Finset.univ base 1 1 1
        (fun U => V₀ (primeProductNorm (poolPrimary F_pool) U / X')) u_free.val =
      HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u_free) true V₀ X' 0 0 := by
  intro q_per F_pool hFa base
  letI : ∀ j : primePool F_pool, (Ideal.span {poolPrimary F_pool j}).IsMaximal :=
    fun j => by rw [poolPrimary_span F_pool hFa j]; infer_instance
  obtain ⟨_, hqset, _, _⟩ := DetectorDictionaryInverseRawConjugateGates.raw_conjugate_base_gates data
  have hF_adm : ∀ I ∈ F_pool, CanonicalQuadraticSieve.Admissible I :=
    fun I hI => (CanonicalQuadraticSieve.admissible_iff_native I).mpr (hFa I hI)
  have h1_adm : CanonicalQuadraticSieve.Admissible (1 : Ideal O) :=
    ⟨one_ne_zero, squarefree_one,
      fun P hP => by rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP; simp at hP⟩
  have hspan_1 : Ideal.span {(1 : O)} = Ideal.span {primaryIdealGenerator (1 : Ideal O)} := by
    rw [Ideal.span_singleton_one, ← Ideal.one_eq_top,
      CenteredMomentSourceRow.primary_span_supported 1 (CanonicalQuadraticSieve.admissible_supported h1_adm)]
  have hnorm_U (U : Finset (primePool F_pool)) :
      primeProductNorm (poolPrimary F_pool) U = ((∏ i ∈ U, i.val).absNorm : ℝ) := by
    unfold primeProductNorm
    rw [map_prod, norm_prod, ← Finset.prod_pow, map_prod, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [ringComplex_norm_sq_eq_absNorm_span, poolPrimary_span F_pool hFa i]
  have htest_eq : (fun U : Finset (primePool F_pool) => V₀ (primeProductNorm (poolPrimary F_pool) U / X')) =
      (fun U : Finset (primePool F_pool) =>
        if (∏ i ∈ U, i.val) ∈ F_pool then V₀ (((∏ i ∈ U, i.val).absNorm : ℝ) / X') else 0) := by
    funext U
    rw [hnorm_U U]
    by_cases hV : V₀ (((∏ i ∈ U, i.val).absNorm : ℝ) / X') = 0
    · rw [hV]; split_ifs <;> rfl
    · have hU_adm : CanonicalQuadraticSieve.Admissible (∏ i ∈ U, i.val) :=
        (CanonicalQuadraticSieve.admissible_iff_native _).mpr
          (CanonicalRowCompletion.poolProduct_admissible F_pool hFa U)
      have hU_out : InverseInitialExcludedPool.outside (reflectionExcludedPrimes q_per) (∏ i ∈ U, i.val) :=
        InverseInitialExcludedForcing.pool_product_outside F_pool (reflectionExcludedPrimes q_per)
          (reflectionExcludedPrimes_prime q_per)
          (fun I hI => (CanonicalRowCompletion.mem_outsideIdealsUpTo.mp (Finset.mem_filter.mp hI).1).2.2) U
      have hN_lo : 1 ≤ (∏ i ∈ U, i.val).absNorm :=
        Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hU_adm.1)
      have hN_hi : ((∏ i ∈ U, i.val).absNorm : ℝ) ≤ (Dpool : ℝ) :=
        ((div_le_iff₀ hX').mp (hb _ hV)).trans hDpool
      have hUF : (∏ i ∈ U, i.val) ∈ F_pool := Finset.mem_filter.mpr
        ⟨CanonicalRowCompletion.mem_outsideIdealsUpTo.mpr ⟨hN_lo, by exact_mod_cast hN_hi, hU_out⟩,
          hU_adm.2.1⟩
      rw [if_pos hUF]
  rw [htest_eq,
    InverseInitialInputReindex.input_puncture_span (poolPrimary F_pool) (poolPrimary_good F_pool hFa)
      Finset.univ base 1 (primaryIdealGenerator 1) hspan_1,
    ← InverseInitialRayAttachment.selected_conjugate_row F_pool hF_adm 1 h1_adm
      (fun _ _ => isCoprime_one_right)
      (InverseInitialConjugateEnergy.conjugateIdealCharacter
        (idealCoeff (deletedBase data)).toMonoidHom)
      (fun I => V₀ ((I.absNorm : ℝ) / X')) u_free.val]
  -- Match `HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u_free) true V₀ X' 0 0`.
  let χ_tgt := targetRow (deletedBase data).inverse u_free
  have hraw_on_out : ∀ I : Ideal O, I ≠ 0 →
      InverseInitialExcludedPool.outside (reflectionExcludedPrimes q_per) I →
      idealCoeff (rawRow u_free) I = CanonicalRowCompletion.idealRowHom u_free.val I := by
    intro I hI0 hout
    have hf1 := congrArg (fun G : Ideal O →*₀ ℂ => G I) (IdealEuler.primeValueHom_eq (idealCoeff (rawRow u_free)))
    have hf2 := congrArg (fun G : Ideal O →*₀ ℂ => G I)
      (IdealEuler.primeValueHom_eq (CanonicalRowCompletion.idealRowHom u_free.val))
    rw [← hf1, ← hf2]
    change (if I = 0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map (idealCoeff (rawRow u_free))).prod) =
      (if I = 0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map (CanonicalRowCompletion.idealRowHom u_free.val)).prod)
    rw [if_neg hI0, if_neg hI0]
    congr 1
    apply Multiset.map_congr rfl
    intro P hP
    have hpP : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    have hP_not_q : P ∉ reflectionExcludedPrimes q_per := fun hmem =>
      hout P hmem (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)
    have hP_not_bad : P ∉ CanonicalRowCompletion.fixedBadPrimes :=
      fun hbad => hP_not_q (reflectionExcludedPrimes_bad q_per hbad)
    exact rawRow_prime_outside CanonicalRowCompletion.fixedBadPrimes
      CanonicalRowCompletion.fixedBadPrimes_prime Finset.Subset.rfl u_free ⟨P, hpP⟩ hP_not_bad
  have htsum : (∑' I : Ideal O, (UniqueFactorizationMonoid.moebius I : ℂ) * idealCoeff χ_tgt I *
        (V₀ ((I.absNorm : ℝ) / X') * (((I.absNorm : ℝ) / X' : ℝ) : ℂ) ^ (-HeckeDyadic.shift 0 0))) =
      ∑ I ∈ F_pool, (UniqueFactorizationMonoid.moebius I : ℂ) * idealCoeff χ_tgt I *
        (V₀ ((I.absNorm : ℝ) / X') * (((I.absNorm : ℝ) / X' : ℝ) : ℂ) ^ (-HeckeDyadic.shift 0 0)) := by
    apply tsum_eq_sum
    intro I hnF
    by_cases hsq : Squarefree I
    · by_cases hout : InverseInitialExcludedPool.outside (reflectionExcludedPrimes q_per) I
      · by_cases hV : V₀ ((I.absNorm : ℝ) / X') = 0
        · simp [hV]
        · exfalso
          apply hnF
          refine Finset.mem_filter.mpr ⟨CanonicalRowCompletion.mem_outsideIdealsUpTo.mpr ⟨?_, ?_, hout⟩, hsq⟩
          · exact Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hsq.ne_zero)
          · exact_mod_cast ((div_le_iff₀ hX').mp (hb _ hV)).trans hDpool
      · have hout' : ¬ InverseInitialExcludedPool.outside (excluded data) I := by rwa [← hqset]
        have hz_del : idealCoeff (deletedBase data) I = 0 :=
          InverseInitialExcludedOverlap.deleted_zero_outside (baseCharacter data) (excluded data)
            (reflectionExcludedPrimes_prime (basePeriod data)) I hout'
        have hz_tgt : idealCoeff χ_tgt I = 0 := by
          change idealCoeff ((deletedBase data).inverse.product (rawRow u_free).inverse) I = 0
          rw [idealCoeff_product, idealCoeff_inverse_conj, hz_del, map_zero, zero_mul]
        simp [hz_tgt]
    · simp [UniqueFactorizationMonoid.moebius_of_not_squarefree hsq]
  rw [InverseInitialExcludedPolynomial.polynomial_all_ideals, htsum]
  have hpow_X : (((X') ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = (X' : ℂ) ^ (-(1 / 2 : ℂ)) := by
    rw [Complex.ofReal_cpow hX'.le]; push_cast; rfl
  have hshift0 : -HeckeDyadic.shift 0 0 = 0 := by
    apply Complex.ext <;> simp [HeckeDyadic.shift]
  rw [hpow_X]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  have hI_sq : Squarefree I := (Finset.mem_filter.mp hI).2
  have hI_out : InverseInitialExcludedPool.outside (reflectionExcludedPrimes q_per) I :=
    (CanonicalRowCompletion.mem_outsideIdealsUpTo.mp (Finset.mem_filter.mp hI).1).2.2
  have hcoeff_I : idealCoeff χ_tgt I =
      star (idealCoeff (deletedBase data) I) * star (CanonicalRowCompletion.idealRowHom u_free.val I) := by
    change idealCoeff ((deletedBase data).inverse.product (rawRow u_free).inverse) I = _
    rw [idealCoeff_product, idealCoeff_inverse_conj, idealCoeff_inverse_conj,
      hraw_on_out I hI_sq.ne_zero hI_out]
    rfl
  rw [hshift0, Complex.cpow_zero, mul_one, hcoeff_I]
  change (UniqueFactorizationMonoid.moebius I : ℂ) * star (idealCoeff (deletedBase data) I) *
      V₀ ((I.absNorm : ℝ) / X') * star (CanonicalRowCompletion.idealRowHom u_free.val I) = _
  ring

/-- Coarse `s`-independent norm bound on `HeckeDyadic.polynomial χ true V₀ X' 0 0`:
every nonzero summand has `1 ≤ I.absNorm ≤ b_hi * X'`, and `cubicIdealGenerator` embeds those
nonzero ideals injectively into `{z : O | ‖ringComplex z‖^2 ≤ b_hi * X'}` (`card ≤ 49 * (1 + b_hi * X')^2`). -/
lemma polynomial_coarse_norm_le
    (χ : Character) (V₀ : ℝ → ℂ) {b_hi B_norm X' : ℝ}
    (hX' : 0 < X') (hb0 : 0 ≤ b_hi) (hBn0 : 0 ≤ B_norm)
    (hb : ∀ y, V₀ y ≠ 0 → y ≤ b_hi) (hV_norm : ∀ y, ‖V₀ y‖ ≤ B_norm) :
    ‖HeckeDyadic.polynomial χ true V₀ X' 0 0‖ ≤
      (X') ^ (-(1 / 2 : ℝ)) * (B_norm * (49 * (1 + b_hi * X') ^ 2)) := by
  let N_hi : ℕ := ⌊b_hi * X'⌋₊
  let S_id := HeckeInverseAmplification.idealsUpTo N_hi
  have htsum : (∑' I : Ideal O, (UniqueFactorizationMonoid.moebius I : ℂ) * idealCoeff χ I *
        (V₀ ((I.absNorm : ℝ) / X') * (((I.absNorm : ℝ) / X' : ℝ) : ℂ) ^ (-HeckeDyadic.shift 0 0))) =
      ∑ I ∈ S_id, (UniqueFactorizationMonoid.moebius I : ℂ) * idealCoeff χ I *
        (V₀ ((I.absNorm : ℝ) / X') * (((I.absNorm : ℝ) / X' : ℝ) : ℂ) ^ (-HeckeDyadic.shift 0 0)) := by
    apply tsum_eq_sum
    intro I hnS
    by_cases hsq : Squarefree I
    · by_cases hV : V₀ ((I.absNorm : ℝ) / X') = 0
      · simp [hV]
      · exfalso
        apply hnS
        rw [HeckeInverseAmplification.mem_idealsUpTo]
        refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hsq.ne_zero),
          Nat.le_floor ((div_le_iff₀ hX').mp (hb _ hV))⟩
    · simp [UniqueFactorizationMonoid.moebius_of_not_squarefree hsq]
  have hcard : (S_id.card : ℝ) ≤ 49 * (1 + b_hi * X') ^ 2 := by
    have hinj : Set.InjOn cubicIdealGenerator (S_id : Set (Ideal O)) := by
      intro I _ J _ hIJ
      rw [← span_cubicIdealGenerator I, ← span_cubicIdealGenerator J, hIJ]
    have hcard_img : S_id.card = (S_id.image cubicIdealGenerator).card :=
      (Finset.card_image_of_injOn hinj).symm
    rw [hcard_img]
    have hR1 : 1 ≤ (1 + b_hi * X') ^ 2 :=
      one_le_pow₀ (by linarith [mul_nonneg hb0 hX'.le])
    apply card_finset_norm_sq_le_49_mul (S_id.image cubicIdealGenerator) hR1
    intro z hz
    obtain ⟨I, hIS, rfl⟩ := Finset.mem_image.mp hz
    rw [ringComplex_norm_sq_eq_absNorm_span, span_cubicIdealGenerator]
    have hle1 : (I.absNorm : ℝ) ≤ b_hi * X' :=
      (Nat.cast_le.mpr (HeckeInverseAmplification.mem_idealsUpTo.mp hIS).2).trans
        (Nat.floor_le (mul_nonneg hb0 hX'.le))
    nlinarith [mul_nonneg hb0 hX'.le]
  have hshift0 : -HeckeDyadic.shift 0 0 = 0 := by
    apply Complex.ext <;> simp [HeckeDyadic.shift]
  have hnorm_X : ‖(X' : ℂ) ^ (-(1 / 2 : ℂ))‖ = (X') ^ (-(1 / 2 : ℝ)) := by
    rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow hX'.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hX' _)]
  rw [InverseInitialExcludedPolynomial.polynomial_all_ideals, htsum, norm_mul, hnorm_X]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hX'.le _)
  apply (norm_sum_le S_id _).trans
  have hterm : ∀ I ∈ S_id,
      ‖(UniqueFactorizationMonoid.moebius I : ℂ) * idealCoeff χ I *
        (V₀ ((I.absNorm : ℝ) / X') * (((I.absNorm : ℝ) / X' : ℝ) : ℂ) ^ (-HeckeDyadic.shift 0 0))‖ ≤ B_norm := by
    intro I _
    rw [hshift0, Complex.cpow_zero, mul_one, norm_mul, norm_mul]
    have hm1 : ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖ ≤ 1 := by
      by_cases hsq : Squarefree I
      · simp only [hsq.moebius_eq, Int.cast_pow, Int.cast_neg, Int.cast_one,
          norm_pow, norm_neg, norm_one, one_pow, le_refl]
      · simp [UniqueFactorizationMonoid.moebius_of_not_squarefree hsq]
    have hc1 : ‖idealCoeff χ I‖ ≤ 1 := idealCoeff_norm_le_one χ I
    exact (mul_le_mul (mul_le_mul hm1 hc1 (norm_nonneg _) zero_le_one) (hV_norm _)
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)).trans_eq (by ring)
  calc (∑ I ∈ S_id, ‖(UniqueFactorizationMonoid.moebius I : ℂ) * idealCoeff χ I *
          (V₀ ((I.absNorm : ℝ) / X') * (((I.absNorm : ℝ) / X' : ℝ) : ℂ) ^ (-HeckeDyadic.shift 0 0))‖)
      ≤ ∑ _I ∈ S_id, B_norm := Finset.sum_le_sum hterm
    _ = (S_id.card : ℝ) * B_norm := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (49 * (1 + b_hi * X') ^ 2) * B_norm := mul_le_mul_of_nonneg_right hcard hBn0
    _ = B_norm * (49 * (1 + b_hi * X') ^ 2) := mul_comm _ _

/-- **Fourier log-separation + sharp collision decoupling on `markedRadial`:**
Given `V : 𝓢(ℝ, ℂ)` supported in `[a₀, b₀]` (`0 < a₀ ≤ b₀`) and slot cap `K : ℕ`, constructs a
compactly supported smooth window `wFresh : 𝓢(ℝ, ℂ)` on `[af, bf]` (`0 < af ≤ bf`, `‖wFresh‖ ≤ B_w`)
such that for any degree `deg` and tail order `N_tail`, the `L^2` sum of
`inputConjugateRow ... (markedRadial p S_rem lists a ∅ V X)` is bounded by
`C_four * (B_low + B_triv / (1 + S_cut) ^ (2 * N_tail))` purely from unpunctured factored products! -/
theorem markedRadial_fourier_l2_le_factored
    (V : 𝓢(ℝ, ℂ)) {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀)
    (hsV : Function.support (V : ℝ → ℂ) ⊆ Set.Icc a₀ b₀) (K : ℕ) :
    ∃ (wFresh : 𝓢(ℝ, ℂ)) (af bf B_w : ℝ),
      0 < af ∧ af ≤ bf ∧ 0 ≤ B_w ∧
      Function.support (wFresh : ℝ → ℂ) ⊆ Set.Icc af bf ∧
      (∀ x, ‖wFresh x‖ ≤ B_w) ∧
      ∀ (deg N_tail : ℕ), ∃ C_four : ℝ, 0 < C_four ∧
      ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
        (p : ι → O), (∀ i, p i ≠ 0) → ∀ [∀ i, (Ideal.span {p i}).IsMaximal],
        Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})) →
        ∀ (hg : ∀ i, lambda ∉ Ideal.span {p i}), Function.Injective p →
        ∀ (pool : Finset ι) (Ψ₀ : O →* ℂ), (∀ u, ‖Ψ₀ u‖ ≤ 1) →
        ∀ (S_rem : Finset σ), S_rem.card ≤ K →
        ∀ (lists : σ → Finset ι), (∀ i ∈ S_rem, lists i ⊆ pool) →
        (S_rem : Set σ).PairwiseDisjoint lists →
        ∀ (a : σ → ι → ℂ), (∀ i ∈ S_rem, ∀ q ∈ lists i, ‖a i q‖ ≤ 1) →
        ∀ (Z_slot : σ → ℝ), (∀ i ∈ S_rem, 1 ≤ Z_slot i) →
        (∀ i ∈ S_rem, ∀ q ∈ lists i, Z_slot i ≤ ‖ringComplex (p q)‖ ^ 2) →
        (∀ i ∈ S_rem, ∀ q ∈ lists i, ‖ringComplex (p q)‖ ^ 2 ≤ 2 * Z_slot i) →
        ∀ (S_w : Finset O) {X S_cut B_low B_triv : ℝ},
        0 < X → 0 ≤ S_cut → 0 ≤ B_low → 0 ≤ B_triv →
        let X₀ := X / ∏ i ∈ S_rem, Z_slot i
        let a_tw : ℝ → σ → ι → ℂ := fun s i q =>
          a i q * kernelLogPhase s (Real.log (‖ringComplex (p q)‖ ^ 2 / Z_slot i))
        (∀ s : ℝ, |s| ≤ S_cut → ∀ T' : Finset σ, T' ⊆ S_rem → ∀ X' : ℝ, 0 < X' →
          X' ≤ X₀ / (∏ i ∈ S_rem \ T', Z_slot i) →
          (∑ w ∈ S_w, (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
            ‖inputConjugateRow p (fun j => complexSexticChar (Ideal.span {p j}) (hg j))
                pool Ψ₀ 1 1 1 (fun U => childLogTest wFresh s (primeProductNorm p U / X')) w *
              ∏ j ∈ T', slotCharSum p hg lists (a_tw s) Ψ₀ j w‖ ^ 2) ≤
            B_low * (1 + |s|) ^ (2 * deg)) →
        (∀ s : ℝ, ∀ T' : Finset σ, T' ⊆ S_rem → ∀ X' : ℝ, 0 < X' →
          X' ≤ X₀ / (∏ i ∈ S_rem \ T', Z_slot i) →
          (∑ w ∈ S_w, (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
            ‖inputConjugateRow p (fun j => complexSexticChar (Ideal.span {p j}) (hg j))
                pool Ψ₀ 1 1 1 (fun U => childLogTest wFresh s (primeProductNorm p U / X')) w *
              ∏ j ∈ T', slotCharSum p hg lists (a_tw s) Ψ₀ j w‖ ^ 2) ≤ B_triv) →
        (∑ w ∈ S_w, X⁻¹ *
          ‖inputConjugateRow p (fun j => complexSexticChar (Ideal.span {p j}) (hg j))
            pool Ψ₀ 1 1 1 (markedRadial p S_rem lists a ∅ V X) w‖ ^ 2) ≤
          C_four * (B_low + B_triv / (1 + S_cut) ^ (2 * N_tail)) := by
  obtain ⟨wFresh, af, bf, B_w, haf, habf, hBw, _, htsup, hBw_norm, hFresh⟩ :=
    InverseInitialUniformFresh.exists_uniform_fresh K a₀ b₀ ha₀ hab₀
  have hsup_w : Function.support (wFresh : ℝ → ℂ) ⊆ Set.Icc af bf :=
    (subset_tsupport (wFresh : ℝ → ℂ)).trans htsup
  refine ⟨wFresh, af, bf, B_w, haf, habf, hBw, hsup_w, hBw_norm, ?_⟩
  intro deg N_tail
  let g : 𝓢(ℝ, ℂ) := kernelLogSource (V : ℝ → ℂ) a₀ b₀ ha₀ hsV (V.smooth ⊤)
  let J_tot : ℕ := deg + N_tail
  have hint_wt : Integrable (fun s : ℝ => (1 + ‖s‖) ^ J_tot * ‖(𝓕 g) s‖) :=
    CanonicalCubeSeparation.weighted_schwartz_integrable (𝓕 g) J_tot
  let I_wt : ℝ := ∫ s : ℝ, (1 + ‖s‖) ^ J_tot * ‖(𝓕 g) s‖
  have hI_wt_nn : 0 ≤ I_wt := integral_nonneg (fun _ => by positivity)
  let C_four : ℝ := (1 + I_wt ^ 2) * (307330 : ℝ) ^ K
  refine ⟨C_four, by dsimp [C_four]; positivity, ?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj_p pool Ψ₀ hΨ1 S_rem hK lists hlists_pool hdisj
    a ha Z_slot hZ1 hZ_lo hZ_hi S_w X S_cut B_low B_triv hX hS_cut hB_low hB_triv
    X₀ a_tw hlow htriv
  let χ := fun j => complexSexticChar (Ideal.span {p j}) (hg j)
  have hZprod_pos : 0 < ∏ i ∈ S_rem, Z_slot i :=
    Finset.prod_pos (fun i hi => zero_lt_one.trans_le (hZ1 i hi))
  have hX₀_pos : 0 < X₀ := div_pos hX hZprod_pos
  have hX_eq : X₀ * ∏ i ∈ S_rem, Z_slot i = X := div_mul_cancel₀ X hZprod_pos.ne'
  -- Step 1: Pointwise Fourier integral representation of `inputConjugateRow ... markedRadial`.
  have hfour_pt (w : O) :
      inputConjugateRow p χ pool Ψ₀ 1 1 1
        (markedRadial p S_rem lists a ∅ V X) w =
      ∫ s : ℝ, (𝓕 g) s *
        disjTupleSum p hg pool S_rem lists (a_tw s) Ψ₀ (childLogTest wFresh s) X₀ w := by
    have hmr_eq : markedRadial p S_rem lists a ∅ V X =
        (fun S => InverseMoment.primeMark S_rem lists a S * V (primeProductNorm p S / X)) := by
      funext S; simp [markedRadial]
    rw [hmr_eq, inputConjugateRow_markedRadial_eq_tuple_sum p hg pool Ψ₀ 1 S_rem lists hlists_pool
      hdisj a V X w]
    -- Rewrite each `(tup, U)` radial value by `schwartz_phase_inversion` + `hFresh`.
    have htup_int (tup : ∀ i : S_rem, lists i.val) :
        ((tupleCoeff a tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
            primeCoprimeMask p (tuplePrimeSet tup) 1 *
            star (primeSubsetRow p χ (tuplePrimeSet tup) w)) *
          inputConjugateRow p χ (pool \ tuplePrimeSet tup) Ψ₀ 1 1 1
            (fun U => V ((primeProductNorm p U * primeProductNorm p (tuplePrimeSet tup)) / X)) w) =
        ∫ s : ℝ, (𝓕 g) s *
          ((tupleCoeff (a_tw s) tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
              star (primeSubsetRow p χ (tuplePrimeSet tup) w)) *
            inputConjugateRow p χ (pool \ tuplePrimeSet tup) Ψ₀ 1 1 1
              (fun U => childLogTest wFresh s (primeProductNorm p U / X₀)) w) := by
      have hmask1 : primeCoprimeMask p (tuplePrimeSet tup) 1 = 1 := by
        rw [primeCoprimeMask_indicator, if_pos]
        intro j _ hdvd
        exact (inferInstance : (Ideal.span {p j}).IsMaximal).ne_top
          (Ideal.span_singleton_eq_top.mpr (isUnit_of_dvd_one hdvd))
      rw [hmask1, mul_one]
      -- Compute `yj = primeProductNorm p (tuplePrimeSet tup) / ∏ i ∈ S_rem, Z_slot i ∈ [1, 2^K]`.
      have hnorm_tup : primeProductNorm p (tuplePrimeSet tup) =
          ∏ i : S_rem, ‖ringComplex (p (tup i).val)‖ ^ 2 := by
        unfold primeProductNorm tuplePrimeSet
        rw [map_prod, norm_prod, Finset.prod_pow, Finset.prod_image (fun i₁ _ i₂ _ he => by
          by_contra hne
          exact Finset.disjoint_left.mp (hdisj i₁.property i₂.property (fun hv => hne (Subtype.ext hv)))
            (tup i₁).property (he ▸ (tup i₂).property))]
      let rat : S_rem → ℝ := fun i => ‖ringComplex (p (tup i).val)‖ ^ 2 / Z_slot i.val
      have hrat_bounds (i : S_rem) : rat i ∈ Set.Icc (1 : ℝ) 2 := by
        have hZi := zero_lt_one.trans_le (hZ1 i.val i.property)
        exact ⟨(one_le_div hZi).mpr (hZ_lo i.val i.property (tup i).val (tup i).property),
          (div_le_iff₀ hZi).mpr (hZ_hi i.val i.property (tup i).val (tup i).property)⟩
      let yj : ℝ := ∏ i : S_rem, rat i
      have hyj_pos : 0 < yj := Finset.prod_pos (fun i _ => zero_lt_one.trans_le (hrat_bounds i).1)
      have hyj_Icc : yj ∈ Set.Icc (1 : ℝ) ((2 : ℝ) ^ K) := by
        refine ⟨Finset.one_le_prod (fun i _ => (hrat_bounds i).1), ?_⟩
        calc (∏ i : S_rem, rat i)
            ≤ ∏ _i : S_rem, (2 : ℝ) := Finset.prod_le_prod (fun i _ => zero_le_one.trans (hrat_bounds i).1)
              (fun i _ => (hrat_bounds i).2)
          _ = (2 : ℝ) ^ S_rem.card := by simp
          _ ≤ (2 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hK
      have hyj_eq : primeProductNorm p (tuplePrimeSet tup) = yj * ∏ i ∈ S_rem, Z_slot i := by
        rw [hnorm_tup]
        dsimp [yj, rat]
        rw [Finset.prod_div_distrib, ← Finset.prod_coe_sort S_rem Z_slot]
        have hZp' : (∏ i : S_rem, Z_slot i.val) ≠ 0 := by
          rw [Finset.prod_coe_sort S_rem Z_slot]; exact hZprod_pos.ne'
        exact (div_mul_cancel₀ _ hZp').symm
      have hphase_tup (s : ℝ) :
          tupleCoeff (a_tw s) tup = tupleCoeff a tup * kernelLogPhase s (Real.log yj) := by
        unfold tupleCoeff
        dsimp only [a_tw]
        rw [Finset.prod_mul_distrib]
        congr 1
        -- Product of `kernelLogPhase s` equals `kernelLogPhase s` of sum of logs = `Real.log yj`.
        have hlog_sum : Real.log yj = ∑ i : S_rem, Real.log (rat i) :=
          Real.log_prod (fun i _ => (zero_lt_one.trans_le (hrat_bounds i).1).ne')
        rw [hlog_sum]
        have hkp : ∀ (S_f : Finset S_rem),
            (∏ i ∈ S_f, kernelLogPhase s (Real.log (rat i))) =
              kernelLogPhase s (∑ i ∈ S_f, Real.log (rat i)) := by
          intro S_f
          induction S_f using Finset.induction_on with
          | empty => simp [kernelLogPhase]
          | @insert x₀ s₀ hx₀ ih =>
            rw [Finset.prod_insert hx₀, Finset.sum_insert hx₀, ih]
            unfold kernelLogPhase
            rw [← Complex.exp_add]
            congr 1; push_cast; ring
        exact hkp Finset.univ
      -- Pointwise radial identity for every `U ∈ (pool \ tuplePrimeSet tup).powerset`.
      have hV_U (U : Finset ι) :
          V ((primeProductNorm p U * primeProductNorm p (tuplePrimeSet tup)) / X) =
            ∫ s : ℝ, (𝓕 g) s *
              (kernelLogPhase s (Real.log yj) * childLogTest wFresh s (primeProductNorm p U / X₀)) := by
        have hpnorm_pos : 0 < primeProductNorm p U := by
          unfold primeProductNorm
          rw [map_prod]
          exact sq_pos_of_pos (norm_pos_iff.mpr
            (Finset.prod_ne_zero_iff.mpr (fun j _ => ringComplex_ne_zero (hp j))))
        let yc : ℝ := primeProductNorm p U / X₀
        have hyc_pos : 0 < yc := div_pos hpnorm_pos hX₀_pos
        have harg_eq : (primeProductNorm p U * primeProductNorm p (tuplePrimeSet tup)) / X = yj * yc := by
          rw [hyj_eq, ← hX_eq]; dsimp [yc]; field_simp [hX₀_pos.ne', hZprod_pos.ne']
        rw [harg_eq]
        have hw_cut : V (yj * yc) = wFresh yc * V (yj * yc) := by
          by_cases hV0 : V (yj * yc) = 0
          · simp [hV0]
          · have hw1 := hFresh (∅ : Finset Unit) (Nat.zero_le K) (V : ℝ → ℂ) hsV
              (fun _ => 1) yj yc (by simp) hyj_Icc hyc_pos (by simpa using hV0)
            rw [hw1, one_mul]
        have hg_val : V (yj * yc) = g (Real.log yc + Real.log yj) := by
          dsimp [g]
          rw [kernelLogSource_apply, Real.exp_add, Real.exp_log hyc_pos,
            Real.exp_log hyj_pos, mul_comm]
        rw [hw_cut, hg_val, JointLogSeparation.schwartz_phase_inversion g (Real.log yc + Real.log yj),
          ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with s
        dsimp only [yc]
        unfold childLogTest kernelLogPhase
        rw [show (((2 * Real.pi * s * (Real.log (primeProductNorm p U / X₀) + Real.log yj) : ℝ) : ℂ) * Complex.I) =
            (((2 * Real.pi * s * Real.log (primeProductNorm p U / X₀) : ℝ) : ℂ) * Complex.I) +
              (((2 * Real.pi * s * Real.log yj : ℝ) : ℂ) * Complex.I) by push_cast; ring,
          Complex.exp_add]
        ring
      -- Pull `∫ s` across the finite `supportConjugateSum` over `U`.
      rw [initial_input_row p hg]
      unfold supportConjugateSum
      simp_rw [hV_U]
      let c_tup : ℂ := tupleCoeff a tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
        star (primeSubsetRow p χ (tuplePrimeSet tup) w)
      let f_U : Finset ι → ℝ → ℂ := fun U s =>
        (𝓕 g) s * (c_tup * (supportMobius U *
          (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U 1 *
            (kernelLogPhase s (Real.log yj) * childLogTest wFresh s (primeProductNorm p U / X₀))) *
          star (primeSubsetRow p χ U w)))
      have hf_int (U : Finset ι) : Integrable (f_U U) := by
        let K_U : ℂ := c_tup * (supportMobius U * Ψ₀ (∏ i ∈ U, p i) *
          primeCoprimeMask p U 1 * wFresh (primeProductNorm p U / X₀) *
          star (primeSubsetRow p χ U w))
        have hcont : Continuous (fun s : ℝ =>
            K_U * kernelLogPhase s (Real.log yj) *
              kernelLogPhase s (Real.log (primeProductNorm p U / X₀))) := by
          unfold kernelLogPhase; fun_prop
        have heq_f : f_U U = fun s => (𝓕 g) s *
            (K_U * kernelLogPhase s (Real.log yj) *
              kernelLogPhase s (Real.log (primeProductNorm p U / X₀))) := by
          funext s; dsimp [f_U, K_U, childLogTest]; ring
        rw [heq_f]
        refine ((𝓕 g).integrable.norm.mul_const ‖K_U‖).mono'
          ((𝓕 g).continuous.aestronglyMeasurable.mul hcont.aestronglyMeasurable) ?_
        filter_upwards with s
        rw [norm_mul, norm_mul, norm_mul, kernelLogPhase_norm,
          kernelLogPhase_norm, mul_one, mul_one]
      have hlhs_eq :
          c_tup * (∑ U ∈ (pool \ tuplePrimeSet tup).powerset,
            supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U 1 *
              ∫ s : ℝ, (𝓕 g) s * (kernelLogPhase s (Real.log yj) *
                childLogTest wFresh s (primeProductNorm p U / X₀))) *
              star (primeSubsetRow p χ U w)) =
          ∑ U ∈ (pool \ tuplePrimeSet tup).powerset, ∫ s : ℝ, f_U U s := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro U _
        have hfU_pull : (fun s : ℝ => f_U U s) =
            fun s : ℝ => (c_tup * supportMobius U * Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U 1 *
              star (primeSubsetRow p χ U w)) *
              ((𝓕 g) s * (kernelLogPhase s (Real.log yj) *
                childLogTest wFresh s (primeProductNorm p U / X₀))) := by
          funext s; dsimp only [f_U]; ring
        rw [hfU_pull, integral_const_mul]
        ring
      change c_tup * _ = _
      rw [hlhs_eq, ← integral_finsetSum _ (fun U _ => hf_int U)]
      apply integral_congr_ae
      filter_upwards with s
      rw [initial_input_row p hg]
      unfold supportConjugateSum
      rw [hphase_tup s]
      dsimp [f_U, c_tup]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U _; ring
    change (-1 : ℂ) ^ S_rem.card *
        ∑ tup : (∀ i : S_rem, lists i.val),
          ((tupleCoeff a tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
            primeCoprimeMask p (tuplePrimeSet tup) 1 *
            star (primeSubsetRow p χ (tuplePrimeSet tup) w)) *
          inputConjugateRow p χ (pool \ tuplePrimeSet tup) Ψ₀ 1 1 1
            (fun U => V ((primeProductNorm p U * primeProductNorm p (tuplePrimeSet tup)) / X)) w) = _
    simp_rw [htup_int]
    -- Pull `∫ s` across the finite sum over `tup : ∀ i : S_rem, lists i.val` and `(-1)^S_rem.card`.
    let G_tup : (∀ i : S_rem, lists i.val) → ℝ → ℂ := fun tup s =>
      (𝓕 g) s * ((tupleCoeff (a_tw s) tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
          star (primeSubsetRow p χ (tuplePrimeSet tup) w)) *
        inputConjugateRow p χ (pool \ tuplePrimeSet tup) Ψ₀ 1 1 1
          (fun U => childLogTest wFresh s (primeProductNorm p U / X₀)) w)
    have hG_int (tup : ∀ i : S_rem, lists i.val) : Integrable (G_tup tup) := by
      -- Each `G_tup tup` is a finite sum of integrable functions over `U`.
      have hexp : G_tup tup = fun s =>
          ∑ U ∈ (pool \ tuplePrimeSet tup).powerset,
            (𝓕 g) s * ((tupleCoeff (a_tw s) tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
              star (primeSubsetRow p χ (tuplePrimeSet tup) w)) *
              (supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U 1 *
                childLogTest wFresh s (primeProductNorm p U / X₀)) *
                star (primeSubsetRow p χ U w))) := by
        funext s
        dsimp [G_tup]
        rw [initial_input_row p hg]
        unfold supportConjugateSum
        simp only [Finset.mul_sum]; rfl
      rw [hexp]
      apply integrable_finsetSum
      intro U _
      have hcont : Continuous (fun s : ℝ =>
          (tupleCoeff (a_tw s) tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
            star (primeSubsetRow p χ (tuplePrimeSet tup) w)) *
            (supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U 1 *
              childLogTest wFresh s (primeProductNorm p U / X₀)) *
              star (primeSubsetRow p χ U w))) := by
        dsimp only [a_tw]
        unfold tupleCoeff childLogTest kernelLogPhase
        fun_prop
      refine ((𝓕 g).integrable.norm.mul_const B_w).mono'
        ((𝓕 g).continuous.aestronglyMeasurable.mul hcont.aestronglyMeasurable) ?_
      filter_upwards with s
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have htc1 : ‖tupleCoeff (a_tw s) tup‖ ≤ 1 := by
        apply tupleCoeff_norm_le_one
        intro i hi q hq
        dsimp [a_tw]
        rw [norm_mul, kernelLogPhase_norm, mul_one]
        exact ha i hi q hq
      have hcw : ‖childLogTest wFresh s (primeProductNorm p U / X₀)‖ ≤ B_w := by
        unfold childLogTest
        rw [norm_mul, kernelLogPhase_norm, mul_one]
        exact hBw_norm _
      have hp1 : ‖Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j)‖ ≤ 1 := hΨ1 _
      have hp2 : ‖star (primeSubsetRow p χ (tuplePrimeSet tup) w)‖ ≤ 1 := by
        rw [norm_star]; exact primeSubsetRow_norm_le_one p χ _ w
      have hm1 : ‖supportMobius U‖ = 1 := supportMobius_norm U
      have hp3 : ‖Ψ₀ (∏ i ∈ U, p i)‖ ≤ 1 := hΨ1 _
      have hm2 : ‖primeCoprimeMask p U 1‖ ≤ 1 := by
        rw [primeCoprimeMask_indicator]; split_ifs <;> norm_num
      have hp4 : ‖star (primeSubsetRow p χ U w)‖ ≤ 1 := by
        rw [norm_star]; exact primeSubsetRow_norm_le_one p χ U w
      change ‖(tupleCoeff (a_tw s) tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
          star (primeSubsetRow p χ (tuplePrimeSet tup) w)) *
        (supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U 1 *
          childLogTest wFresh s (primeProductNorm p U / X₀)) *
          star (primeSubsetRow p χ U w))‖ ≤ B_w
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, hm1, one_mul]
      have h_lhs : ‖tupleCoeff (a_tw s) tup‖ * ‖Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j)‖ *
          ‖star (primeSubsetRow p χ (tuplePrimeSet tup) w)‖ ≤ 1 :=
        (mul_le_mul (mul_le_mul htc1 hp1 (norm_nonneg _) zero_le_one) hp2
          (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)).trans_eq (by ring)
      have h_mid : ‖Ψ₀ (∏ i ∈ U, p i)‖ * ‖primeCoprimeMask p U 1‖ *
          ‖childLogTest wFresh s (primeProductNorm p U / X₀)‖ ≤ B_w := by
        have h12 : ‖Ψ₀ (∏ i ∈ U, p i)‖ * ‖primeCoprimeMask p U 1‖ ≤ 1 :=
          (mul_le_mul hp3 hm2 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
        exact (mul_le_mul h12 hcw (norm_nonneg _) zero_le_one).trans_eq (one_mul B_w)
      have h_rhs : (‖Ψ₀ (∏ i ∈ U, p i)‖ * ‖primeCoprimeMask p U 1‖ *
          ‖childLogTest wFresh s (primeProductNorm p U / X₀)‖) *
          ‖star (primeSubsetRow p χ U w)‖ ≤ B_w :=
        (mul_le_mul h_mid hp4 (norm_nonneg _) hBw).trans_eq (mul_one B_w)
      exact (mul_le_mul h_lhs h_rhs (by positivity) zero_le_one).trans_eq (one_mul B_w)
    change (-1 : ℂ) ^ S_rem.card * ∑ tup : (∀ i : S_rem, lists i.val), ∫ s : ℝ, G_tup tup s = _
    rw [← integral_finsetSum _ (fun tup _ => hG_int tup), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with s
    unfold disjTupleSum
    dsimp only [G_tup]
    rw [← Finset.mul_sum]; ring
  -- Step 2: Apply `disjTupleSum_l2_le_factored_sharp` at each `s : ℝ`, then `common_measure_energy`.
  let E_tot : ℝ := (307330 : ℝ) ^ K * (B_low + B_triv / (1 + S_cut) ^ (2 * N_tail))
  have hE_tot_nn : 0 ≤ E_tot := by dsimp [E_tot]; positivity
  have hpt_s (s : ℝ) :
      (∑ w ∈ S_w, X⁻¹ *
        ‖disjTupleSum p hg pool S_rem lists (a_tw s) Ψ₀ (childLogTest wFresh s) X₀ w‖ ^ 2) ≤
        E_tot * ((1 + ‖s‖) ^ J_tot) ^ 2 := by
    have ha_s : ∀ i ∈ S_rem, ∀ q ∈ lists i, ‖a_tw s i q‖ ≤ 1 := by
      intro i hi q hq; dsimp [a_tw]
      rw [norm_mul, kernelLogPhase_norm, mul_one]; exact ha i hi q hq
    have hb_s : ∀ y, childLogTest wFresh s y ≠ 0 → y ≤ bf := fun y hy =>
      (hsup_w (InverseInitialOriginalHeight.child_support wFresh s hy)).2
    have hpow_K : (307330 : ℝ) ^ S_rem.card ≤ (307330 : ℝ) ^ K :=
      pow_le_pow_right₀ (by norm_num) hK
    by_cases hs_le : |s| ≤ S_cut
    · have hB_s : 0 ≤ B_low * (1 + |s|) ^ (2 * deg) := by positivity
      have hd := disjTupleSum_l2_le_factored_sharp p hp hg hinj_p pool ∅ Ψ₀ hΨ1 S_rem ∅
        (Finset.disjoint_empty_right S_rem) lists (by simpa using hlists_pool) (by simpa using hdisj)
        (a_tw s) ha_s Z_slot (by simpa using hZ1) hZ_lo hZ_hi (childLogTest wFresh s) hb_s
        S_w hB_s X₀ hX₀_pos
        (fun T' hT' X' hX' hX'_le => by
          simpa [Finset.union_empty] using hlow s hs_le T' (by simpa using hT') X' hX'
            (by simpa using hX'_le))
      simp only [Finset.sdiff_empty, Finset.union_empty, Finset.prod_empty, mul_one,
        Finset.card_empty, pow_zero, hX_eq] at hd
      have h1 : (1 + |s|) ^ (2 * deg) ≤ ((1 + ‖s‖) ^ J_tot) ^ 2 := by
        rw [Real.norm_eq_abs, ← pow_mul]
        exact pow_le_pow_right₀ (by linarith [abs_nonneg s]) (by dsimp [J_tot]; omega)
      calc _ ≤ (307330 : ℝ) ^ S_rem.card * (B_low * (1 + |s|) ^ (2 * deg)) := hd
        _ ≤ (307330 : ℝ) ^ K * ((B_low + B_triv / (1 + S_cut) ^ (2 * N_tail)) * ((1 + ‖s‖) ^ J_tot) ^ 2) := by
            apply mul_le_mul hpow_K _ hB_s (by positivity)
            exact mul_le_mul (le_add_of_nonneg_right (by positivity)) h1 (by positivity) (by positivity)
        _ = E_tot * ((1 + ‖s‖) ^ J_tot) ^ 2 := by dsimp [E_tot]; ring
    · have hs_gt : S_cut < |s| := not_le.mp hs_le
      have hd := disjTupleSum_l2_le_factored_sharp p hp hg hinj_p pool ∅ Ψ₀ hΨ1 S_rem ∅
        (Finset.disjoint_empty_right S_rem) lists (by simpa using hlists_pool) (by simpa using hdisj)
        (a_tw s) ha_s Z_slot (by simpa using hZ1) hZ_lo hZ_hi (childLogTest wFresh s) hb_s
        S_w hB_triv X₀ hX₀_pos
        (fun T' hT' X' hX' hX'_le => by
          simpa [Finset.union_empty] using htriv s T' (by simpa using hT') X' hX'
            (by simpa using hX'_le))
      simp only [Finset.sdiff_empty, Finset.union_empty, Finset.prod_empty, mul_one,
        Finset.card_empty, pow_zero, hX_eq] at hd
      have hcut_pow : (1 + S_cut) ^ (2 * N_tail) ≤ ((1 + ‖s‖) ^ J_tot) ^ 2 := by
        rw [Real.norm_eq_abs, ← pow_mul]
        calc (1 + S_cut) ^ (2 * N_tail)
            ≤ (1 + |s|) ^ (2 * N_tail) := pow_le_pow_left₀ (by linarith) (by linarith) _
          _ ≤ (1 + |s|) ^ (J_tot * 2) := pow_le_pow_right₀ (by linarith [abs_nonneg s])
              (by dsimp [J_tot]; omega)
      have hcut_pos : 0 < (1 + S_cut) ^ (2 * N_tail) := pow_pos (by linarith) _
      have htriv_le : B_triv ≤ (B_low + B_triv / (1 + S_cut) ^ (2 * N_tail)) * ((1 + ‖s‖) ^ J_tot) ^ 2 := by
        calc B_triv = (B_triv / (1 + S_cut) ^ (2 * N_tail)) * (1 + S_cut) ^ (2 * N_tail) :=
              (div_mul_cancel₀ B_triv hcut_pos.ne').symm
          _ ≤ (B_low + B_triv / (1 + S_cut) ^ (2 * N_tail)) * ((1 + ‖s‖) ^ J_tot) ^ 2 :=
              mul_le_mul (le_add_of_nonneg_left hB_low) hcut_pow hcut_pos.le (by positivity)
      calc _ ≤ (307330 : ℝ) ^ S_rem.card * B_triv := hd
        _ ≤ (307330 : ℝ) ^ K * ((B_low + B_triv / (1 + S_cut) ^ (2 * N_tail)) * ((1 + ‖s‖) ^ J_tot) ^ 2) :=
            mul_le_mul hpow_K htriv_le hB_triv (by positivity)
        _ = E_tot * ((1 + ‖s‖) ^ J_tot) ^ 2 := by dsimp [E_tot]; ring
  -- Apply `common_measure_energy` on `κ := S_w` with `b s := (𝓕 g) s * ((1 + ‖s‖) ^ J_tot : ℂ)`.
  let h_wt : ℝ → ℝ := fun s => (1 + ‖s‖) ^ J_tot
  let b_meas : ℝ → ℂ := fun s => (𝓕 g) s * (h_wt s : ℂ)
  let f_meas : S_w → ℝ → ℂ := fun w s =>
    (((X ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      disjTupleSum p hg pool S_rem lists (a_tw s) Ψ₀ (childLogTest wFresh s) X₀ w.val) / (h_wt s : ℂ)
  have hh_pos (s : ℝ) : 0 < h_wt s := by dsimp [h_wt]; positivity
  have hb_norm (s : ℝ) : ‖b_meas s‖ = h_wt s * ‖(𝓕 g) s‖ := by
    dsimp [b_meas]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hh_pos s), mul_comm]
  have hb_int : Integrable (fun s => ‖b_meas s‖) := by
    simpa only [hb_norm] using hint_wt
  have hbf_eq (w : S_w) (s : ℝ) : b_meas s * f_meas w s =
      ((X ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((𝓕 g) s * disjTupleSum p hg pool S_rem lists (a_tw s) Ψ₀ (childLogTest wFresh s) X₀ w.val) := by
    dsimp [b_meas, f_meas]
    have hn : (h_wt s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hh_pos s).ne'
    field_simp [hn]
  have hbf_int (w : S_w) : Integrable (fun s => b_meas s * f_meas w s) := by
    simp_rw [hbf_eq w]
    apply Integrable.const_mul
    -- Same finite-sum integrability as in `hfour_pt`.
    unfold disjTupleSum
    simp only [Finset.mul_sum]
    apply integrable_finsetSum
    intro tup _
    simp_rw [initial_input_row p hg]
    unfold supportConjugateSum
    simp only [Finset.mul_sum]
    apply integrable_finsetSum
    intro U _
    have hcont : Continuous (fun s : ℝ =>
        (-1 : ℂ) ^ S_rem.card *
          ((tupleCoeff (a_tw s) tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
            star (primeSubsetRow p χ (tuplePrimeSet tup) w.val)) *
            (supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U 1 *
              childLogTest wFresh s (primeProductNorm p U / X₀)) *
              star (primeSubsetRow p χ U w.val)))) := by
      dsimp only [a_tw]
      unfold tupleCoeff childLogTest kernelLogPhase
      fun_prop
    refine ((𝓕 g).integrable.norm.mul_const B_w).mono'
      ((𝓕 g).continuous.aestronglyMeasurable.mul hcont.aestronglyMeasurable) ?_
    filter_upwards with s
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have htc1 : ‖tupleCoeff (a_tw s) tup‖ ≤ 1 := tupleCoeff_norm_le_one
      (fun i hi q hq => by dsimp [a_tw]; rw [norm_mul, kernelLogPhase_norm, mul_one]; exact ha i hi q hq) tup
    have hcw : ‖childLogTest wFresh s (primeProductNorm p U / X₀)‖ ≤ B_w := by
      unfold childLogTest; rw [norm_mul, kernelLogPhase_norm, mul_one]; exact hBw_norm _
    have hp1 : ‖Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j)‖ ≤ 1 := hΨ1 _
    have hp2 : ‖star (primeSubsetRow p χ (tuplePrimeSet tup) w.val)‖ ≤ 1 := by
      rw [norm_star]; exact primeSubsetRow_norm_le_one p χ _ w.val
    have hm1 : ‖supportMobius U‖ = 1 := supportMobius_norm U
    have hp3 : ‖Ψ₀ (∏ i ∈ U, p i)‖ ≤ 1 := hΨ1 _
    have hm2 : ‖primeCoprimeMask p U 1‖ ≤ 1 := by
      rw [primeCoprimeMask_indicator]; split_ifs <;> norm_num
    have hp4 : ‖star (primeSubsetRow p χ U w.val)‖ ≤ 1 := by
      rw [norm_star]; exact primeSubsetRow_norm_le_one p χ U w.val
    change ‖(tupleCoeff (a_tw s) tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
        star (primeSubsetRow p χ (tuplePrimeSet tup) w.val)) *
      (supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U 1 *
        childLogTest wFresh s (primeProductNorm p U / X₀)) *
        star (primeSubsetRow p χ U w.val))‖ ≤ B_w
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, hm1, one_mul]
    have h1 : ‖tupleCoeff (a_tw s) tup‖ * ‖Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j)‖ *
        ‖star (primeSubsetRow p χ (tuplePrimeSet tup) w.val)‖ ≤ 1 :=
      (mul_le_mul (mul_le_mul htc1 hp1 (norm_nonneg _) zero_le_one) hp2
        (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)).trans_eq (by ring)
    have h2 : ‖Ψ₀ (∏ i ∈ U, p i)‖ * ‖primeCoprimeMask p U 1‖ *
        ‖childLogTest wFresh s (primeProductNorm p U / X₀)‖ ≤ B_w := by
      have h12 : ‖Ψ₀ (∏ i ∈ U, p i)‖ * ‖primeCoprimeMask p U 1‖ ≤ 1 :=
        (mul_le_mul hp3 hm2 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
      exact (mul_le_mul h12 hcw (norm_nonneg _) zero_le_one).trans_eq (one_mul B_w)
    have h3 : (‖Ψ₀ (∏ i ∈ U, p i)‖ * ‖primeCoprimeMask p U 1‖ *
        ‖childLogTest wFresh s (primeProductNorm p U / X₀)‖) *
        ‖star (primeSubsetRow p χ U w.val)‖ ≤ B_w :=
      (mul_le_mul h2 hp4 (norm_nonneg _) hBw).trans_eq (mul_one B_w)
    exact (mul_le_mul h1 h3 (by positivity) zero_le_one).trans_eq (one_mul B_w)
  have hX_sq : ∀ z : ℂ, ‖((X ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * z‖ ^ 2 = X⁻¹ * ‖z‖ ^ 2 := by
    intro z
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hX _), ← Real.rpow_natCast _ 2,
      ← Real.rpow_mul hX.le]
    norm_num [Real.rpow_neg_one]
  have hf_energy (s : ℝ) : (∑ w : S_w, ‖f_meas w s‖ ^ 2) ≤ E_tot := by
    have hsum_eq : (∑ w : S_w, ‖f_meas w s‖ ^ 2) =
        (∑ w ∈ S_w, X⁻¹ *
          ‖disjTupleSum p hg pool S_rem lists (a_tw s) Ψ₀ (childLogTest wFresh s) X₀ w‖ ^ 2) /
          (h_wt s) ^ 2 := by
      rw [← Finset.sum_coe_sort S_w, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro w _
      simp only [f_meas, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hh_pos s),
        div_pow, hX_sq]
    rw [hsum_eq, div_le_iff₀ (sq_pos_of_pos (hh_pos s))]
    exact hpt_s s
  have hcme := InverseMoment.common_measure_energy volume b_meas f_meas E_tot
    hE_tot_nn hb_int hbf_int hf_energy
  have hlhs_cme :
      (∑ w ∈ S_w, X⁻¹ *
        ‖inputConjugateRow p χ pool Ψ₀ 1 1 1
          (markedRadial p S_rem lists a ∅ V X) w‖ ^ 2) =
      ∑ w : S_w, ‖∫ s : ℝ, b_meas s * f_meas w s‖ ^ 2 := by
    rw [← Finset.sum_coe_sort S_w]
    apply Finset.sum_congr rfl
    intro w _
    simp_rw [hbf_eq w]
    rw [integral_const_mul, hX_sq, ← hfour_pt w.val]
  rw [hlhs_cme]
  have hb_int_eq : (∫ s : ℝ, ‖b_meas s‖) = I_wt := by
    simp_rw [hb_norm]; rfl
  calc (∑ w : S_w, ‖∫ s : ℝ, b_meas s * f_meas w s‖ ^ 2)
      ≤ E_tot * (∫ s : ℝ, ‖b_meas s‖) ^ 2 := hcme
    _ = I_wt ^ 2 * E_tot := by rw [hb_int_eq]; ring
    _ ≤ (1 + I_wt ^ 2) * E_tot := mul_le_mul_of_nonneg_right (by linarith) hE_tot_nn
    _ = C_four * (B_low + B_triv / (1 + S_cut) ^ (2 * N_tail)) := by dsimp [C_four, E_tot]; ring

end DictionaryAndFourier

/-! ### Part III: Convex Stage-1 tiny-bin certificates and `IsBaseRayTwist` / `excludePrimes` bridges -/

/-- Across all `ν ∈ [11/25, 3/4]` and `x ∈ [0, 1/2]`, both the inverse-branch slot-width factor
`(1 - stage1Crossing ν x) / 2` and the plain-branch slot-width factor
`(1 - 2 * ((1 + ν * rowP x / (2 * rowJ ν x)) - stage1Crossing ν x)) * (2 / 9)` are nonnegative, so
sixth-power cofactors `x₆ ≥ 0` only decrease `H_free * W`. -/
theorem stage1_inv_plain_width_nonneg {ν x : ℝ}
    (hν0 : 11 / 25 ≤ ν) (hν1 : ν ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    0 ≤ (1 - stage1Crossing ν x) / 2 ∧
      0 ≤ (1 - 2 * ((1 + ν * rowP x / (2 * rowJ ν x)) - stage1Crossing ν x)) * (2 / 9) := by
  have hD : 37 / 18 ≤ rowD x := by unfold rowD; linarith
  have hD0 : 0 < rowD x := by linarith
  have hJ := rowJ_pos (δ := ν) (x := x) (by linarith) (by linarith) hx1
  have hJ0 : 0 < rowJ ν x := by linarith
  have hDJ : 0 < 2 * rowD x * rowJ ν x := mul_pos (by linarith) hJ0
  set u := (ν - 11 / 25) / (3 / 4 - 11 / 25)
  set v := x / (1 / 2)
  have hu0 : 0 ≤ u := div_nonneg (by linarith) (by norm_num)
  have hu1 : u ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 3 / 4 - 11 / 25)).mpr (by linarith)
  have hv0 : 0 ≤ v := div_nonneg hx0 (by norm_num)
  have hv1 : v ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 2)).mpr (by linarith)
  constructor
  · have hpos := bernstein23_nonneg hu0 hu1 hv0 hv1
      (c00 := 59 / 50) (c01 := 7847 / 8100) (c02 := 5723 / 7290) (c03 := 15281 / 24300)
      (c10 := 143 / 200) (c11 := 19019 / 32400) (c12 := 13871 / 29160) (c13 := 37037 / 97200)
      (c20 := 1 / 4) (c21 := 133 / 648) (c22 := 485 / 2916) (c23 := 259 / 1944)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hid : ((1 - stage1Crossing ν x) / 2) * (2 * rowD x * rowJ ν x) =
        bernstein23 u v
          (59 / 50) (7847 / 8100) (5723 / 7290) (15281 / 24300)
          (143 / 200) (19019 / 32400) (13871 / 29160) (37037 / 97200)
          (1 / 4) (133 / 648) (485 / 2916) (259 / 1944) := by
      dsimp [u, v]
      unfold stage1Crossing
      field_simp [hD0.ne', hJ0.ne']
      unfold bernstein23 rowJ rowD rowP
      ring
    nlinarith
  · have hpos := bernstein23_nonneg hu0 hu1 hv0 hv1
      (c00 := 118 / 225) (c01 := 6962 / 18225) (c02 := 649 / 2430) (c03 := 2183 / 12150)
      (c10 := 143 / 450) (c11 := 8437 / 36450) (c12 := 1573 / 9720) (c13 := 5291 / 48600)
      (c20 := 1 / 9) (c21 := 59 / 729) (c22 := 55 / 972) (c23 := 37 / 972)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hid : ((1 - 2 * ((1 + ν * rowP x / (2 * rowJ ν x)) - stage1Crossing ν x)) * (2 / 9)) *
        (2 * rowD x * rowJ ν x) =
        bernstein23 u v
          (118 / 225) (6962 / 18225) (649 / 2430) (2183 / 12150)
          (143 / 450) (8437 / 36450) (1573 / 9720) (5291 / 48600)
          (1 / 9) (59 / 729) (55 / 972) (37 / 972) := by
      dsimp [u, v]
      unfold stage1Crossing
      field_simp [hD0.ne', hJ0.ne']
      unfold bernstein23 rowJ rowD rowP
      ring
    nlinarith

/-- Endpoint Bernstein certificate at `ell = 3/500` for the inverse witness width on `[17/25, 19/26]`. -/
private lemma stage1_slot_supply_ell3_inv {r ν x : ℝ}
    (hr0 : 17 / 25 ≤ r) (hr1 : r ≤ 19 / 26)
    (hν0 : 11 / 25 ≤ ν) (hν1 : ν ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    (stage1DualScale r - 6 * (3 / 500)) * ((1 - stage1Crossing ν x) / 2) + 1 / 2500 ≤
      stage1RemWidth r - (25 / 3) * (stage1Line r - (1 - r) / 2) - 3 / 500 ∧
    (1 - 6 * (3 / 500)) * ((1 - stage1Crossing ν x) / 2) + 1 / 2500 ≤ 7 / 52 - 3 / 500 := by
  have hD : 37 / 18 ≤ rowD x := by unfold rowD; linarith
  have hD0 : 0 < rowD x := by linarith
  have hJ := rowJ_pos (δ := ν) (x := x) (by linarith) (by linarith) hx1
  have hJ0 : 0 < rowJ ν x := by linarith
  have hDJ : 0 < 2 * rowD x * rowJ ν x := mul_pos (by linarith) hJ0
  set u := (ν - 11 / 25) / (3 / 4 - 11 / 25)
  set v := x / (1 / 2)
  have hu0 : 0 ≤ u := div_nonneg (by linarith) (by norm_num)
  have hu1 : u ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 3 / 4 - 11 / 25)).mpr (by linarith)
  have hv0 : 0 ≤ v := div_nonneg hx0 (by norm_num)
  have hv1 : v ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 2)).mpr (by linarith)
  let W₁ := (1 - stage1Crossing ν x) / 2
  have h_lo : (stage1DualScale (17 / 25) - 6 * (3 / 500)) * W₁ + 1 / 2500 ≤
      stage1RemWidth (17 / 25) - (25 / 3) * (stage1Line (17 / 25) - (1 - 17 / 25) / 2) - 3 / 500 := by
    have hpos := bernstein23_nonneg hu0 hu1 hv0 hv1
      (c00 := 29411 / 62500) (c01 := 6315611 / 25312500)
      (c02 := 97361471 / 911250000) (c03 := 5949119 / 303750000)
      (c10 := 193997 / 250000) (c11 := 47826197 / 101250000)
      (c12 := 990047417 / 3645000000) (c13 := 173332013 / 1215000000)
      (c20 := 5407 / 5000) (c21 := 1407799 / 2025000)
      (c22 := 31812979 / 72900000) (c23 := 6457351 / 24300000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hid : (stage1RemWidth (17 / 25) - (25 / 3) * (stage1Line (17 / 25) - (1 - 17 / 25) / 2) -
        3 / 500 - 1 / 2500 - (stage1DualScale (17 / 25) - 6 * (3 / 500)) * W₁) *
        (2 * rowD x * rowJ ν x) =
        bernstein23 u v
          (29411 / 62500) (6315611 / 25312500) (97361471 / 911250000) (5949119 / 303750000)
          (193997 / 250000) (47826197 / 101250000) (990047417 / 3645000000) (173332013 / 1215000000)
          (5407 / 5000) (1407799 / 2025000) (31812979 / 72900000) (6457351 / 24300000) := by
      dsimp [W₁, u, v]
      unfold stage1RemWidth stage1DualScale stage1Width stage1Line stage1Crossing
      field_simp [hD0.ne', hJ0.ne']
      unfold bernstein23 rowJ rowD rowP
      ring
    nlinarith
  have h_19 : (1 - 6 * (3 / 500)) * W₁ + 1 / 2500 ≤ 7 / 52 - 3 / 500 := by
    have hpos := bernstein23_nonneg hu0 hu1 hv0 hv1
      (c00 := 90842 / 203125) (c01 := 29788961 / 131625000)
      (c02 := 201989521 / 2369250000) (c03 := 21571 / 60750000)
      (c10 := 1261393 / 1625000) (c11 := 246260897 / 526500000)
      (c12 := 2507684767 / 9477000000) (c13 := 425978521 / 3159000000)
      (c20 := 35921 / 32500) (c21 := 7467319 / 10530000)
      (c22 := 84148229 / 189540000) (c23 := 17016707 / 63180000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hid : (7 / 52 - 3 / 500 - 1 / 2500 - (1 - 6 * (3 / 500)) * W₁) *
        (2 * rowD x * rowJ ν x) =
        bernstein23 u v
          (90842 / 203125) (29788961 / 131625000) (201989521 / 2369250000) (21571 / 60750000)
          (1261393 / 1625000) (246260897 / 526500000) (2507684767 / 9477000000) (425978521 / 3159000000)
          (35921 / 32500) (7467319 / 10530000) (84148229 / 189540000) (17016707 / 63180000) := by
      dsimp [W₁, u, v]
      unfold stage1Crossing
      field_simp [hD0.ne', hJ0.ne']
      unfold bernstein23 rowJ rowD rowP
      ring
    nlinarith
  set α := (r - 17 / 25) / (19 / 26 - 17 / 25)
  have hα0 : 0 ≤ α := div_nonneg (by linarith) (by norm_num)
  have hα1 : 0 ≤ 1 - α := by
    have : α ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 19 / 26 - 17 / 25)).mpr (by linarith)
    linarith
  refine ⟨?_, h_19⟩
  have ha_lo := mul_le_mul_of_nonneg_left h_lo hα1
  have ha_hi := mul_le_mul_of_nonneg_left h_19 hα0
  have haff1 : (1 - α) * (stage1DualScale (17 / 25) - 6 * (3 / 500)) +
      α * (1 - 6 * (3 / 500)) = stage1DualScale r - 6 * (3 / 500) := by
    dsimp [α]; unfold stage1DualScale stage1Width stage1Line; ring
  have haff2 : (1 - α) * (stage1RemWidth (17 / 25) -
        (25 / 3) * (stage1Line (17 / 25) - (1 - 17 / 25) / 2) - 3 / 500) +
      α * (7 / 52 - 3 / 500) =
      stage1RemWidth r - (25 / 3) * (stage1Line r - (1 - r) / 2) - 3 / 500 := by
    dsimp [α]; unfold stage1RemWidth stage1Width stage1Line; ring
  have hlhs1 : (1 - α) * ((stage1DualScale (17 / 25) - 6 * (3 / 500)) * W₁ + 1 / 2500) +
      α * ((1 - 6 * (3 / 500)) * W₁ + 1 / 2500) =
      (stage1DualScale r - 6 * (3 / 500)) * W₁ + 1 / 2500 := by
    calc _ = ((1 - α) * (stage1DualScale (17 / 25) - 6 * (3 / 500)) + α * (1 - 6 * (3 / 500))) * W₁ +
        1 / 2500 := by ring
      _ = _ := by rw [haff1]
  exact (hlhs1.symm.trans_le (add_le_add ha_lo ha_hi)).trans_eq haff2

/-- Endpoint Bernstein certificate at `ell = 3/500` for the plain witness width on `[17/25, 19/26]`. -/
private lemma stage1_slot_supply_ell3_plain {r ν x : ℝ}
    (hr0 : 17 / 25 ≤ r) (hr1 : r ≤ 19 / 26)
    (hν0 : 11 / 25 ≤ ν) (hν1 : ν ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    (stage1DualScale r - 6 * (3 / 500)) *
        ((1 - 2 * ((1 + ν * rowP x / (2 * rowJ ν x)) - stage1Crossing ν x)) * (2 / 9)) +
      1 / 2500 ≤
      stage1RemWidth r - (25 / 3) * (stage1Line r - (1 - r) / 2) - 3 / 500 ∧
    (1 - 6 * (3 / 500)) *
        ((1 - 2 * ((1 + ν * rowP x / (2 * rowJ ν x)) - stage1Crossing ν x)) * (2 / 9)) +
      1 / 2500 ≤ 7 / 52 - 3 / 500 := by
  have hD : 37 / 18 ≤ rowD x := by unfold rowD; linarith
  have hD0 : 0 < rowD x := by linarith
  have hJ := rowJ_pos (δ := ν) (x := x) (by linarith) (by linarith) hx1
  have hJ0 : 0 < rowJ ν x := by linarith
  have hDJ : 0 < 2 * rowD x * rowJ ν x := mul_pos (by linarith) hJ0
  set u := (ν - 11 / 25) / (3 / 4 - 11 / 25)
  set v := x / (1 / 2)
  have hu0 : 0 ≤ u := div_nonneg (by linarith) (by norm_num)
  have hu1 : u ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 3 / 4 - 11 / 25)).mpr (by linarith)
  have hv0 : 0 ≤ v := div_nonneg hx0 (by norm_num)
  have hv1 : v ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 2)).mpr (by linarith)
  let W₂ := (1 - 2 * ((1 + ν * rowP x / (2 * rowJ ν x)) - stage1Crossing ν x)) * (2 / 9)
  have h_lo : (stage1DualScale (17 / 25) - 6 * (3 / 500)) * W₂ + 1 / 2500 ≤
      stage1RemWidth (17 / 25) - (25 / 3) * (stage1Line (17 / 25) - (1 - 17 / 25) / 2) - 3 / 500 := by
    have hpos := bernstein23_nonneg hu0 hu1 hv0 hv1
      (c00 := 598757 / 562500) (c01 := 44484131 / 56953125)
      (c02 := 174985237 / 303750000) (c03 := 129550579 / 303750000)
      (c10 := 2555639 / 2250000) (c11 := 361969849 / 455625000)
      (c12 := 675473299 / 1215000000) (c13 := 472908433 / 1215000000)
      (c20 := 2173 / 1800) (c21 := 7361333 / 9112500)
      (c22 := 13020113 / 24300000) (c23 := 8552291 / 24300000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hid : (stage1RemWidth (17 / 25) - (25 / 3) * (stage1Line (17 / 25) - (1 - 17 / 25) / 2) -
        3 / 500 - 1 / 2500 - (stage1DualScale (17 / 25) - 6 * (3 / 500)) * W₂) *
        (2 * rowD x * rowJ ν x) =
        bernstein23 u v
          (598757 / 562500) (44484131 / 56953125) (174985237 / 303750000) (129550579 / 303750000)
          (2555639 / 2250000) (361969849 / 455625000) (675473299 / 1215000000) (472908433 / 1215000000)
          (2173 / 1800) (7361333 / 9112500) (13020113 / 24300000) (8552291 / 24300000) := by
      dsimp [W₂, u, v]
      unfold stage1RemWidth stage1DualScale stage1Width stage1Line stage1Crossing
      field_simp [hD0.ne', hJ0.ne']
      unfold bernstein23 rowJ rowD rowP
      ring
    nlinarith
  have h_19 : (1 - 6 * (3 / 500)) * W₂ + 1 / 2500 ≤ 7 / 52 - 3 / 500 := by
    have hpos := bernstein23_nonneg hu0 hu1 hv0 hv1
      (c00 := 7891487 / 7312500) (c01 := 117271378 / 148078125)
      (c02 := 461670107 / 789750000) (c03 := 26326721 / 60750000)
      (c10 := 33905549 / 29250000) (c11 := 960104237 / 1184625000)
      (c12 := 1791668789 / 3159000000) (c13 := 1254813671 / 3159000000)
      (c20 := 724903 / 585000) (c21 := 19640749 / 23692500)
      (c22 := 34733143 / 63180000) (c23 := 22812757 / 63180000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hid : (7 / 52 - 3 / 500 - 1 / 2500 - (1 - 6 * (3 / 500)) * W₂) *
        (2 * rowD x * rowJ ν x) =
        bernstein23 u v
          (7891487 / 7312500) (117271378 / 148078125) (461670107 / 789750000) (26326721 / 60750000)
          (33905549 / 29250000) (960104237 / 1184625000) (1791668789 / 3159000000) (1254813671 / 3159000000)
          (724903 / 585000) (19640749 / 23692500) (34733143 / 63180000) (22812757 / 63180000) := by
      dsimp [W₂, u, v]
      unfold stage1Crossing
      field_simp [hD0.ne', hJ0.ne']
      unfold bernstein23 rowJ rowD rowP
      ring
    nlinarith
  set α := (r - 17 / 25) / (19 / 26 - 17 / 25)
  have hα0 : 0 ≤ α := div_nonneg (by linarith) (by norm_num)
  have hα1 : 0 ≤ 1 - α := by
    have : α ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 19 / 26 - 17 / 25)).mpr (by linarith)
    linarith
  refine ⟨?_, h_19⟩
  have ha_lo := mul_le_mul_of_nonneg_left h_lo hα1
  have ha_hi := mul_le_mul_of_nonneg_left h_19 hα0
  have haff1 : (1 - α) * (stage1DualScale (17 / 25) - 6 * (3 / 500)) +
      α * (1 - 6 * (3 / 500)) = stage1DualScale r - 6 * (3 / 500) := by
    dsimp [α]; unfold stage1DualScale stage1Width stage1Line; ring
  have haff2 : (1 - α) * (stage1RemWidth (17 / 25) -
        (25 / 3) * (stage1Line (17 / 25) - (1 - 17 / 25) / 2) - 3 / 500) +
      α * (7 / 52 - 3 / 500) =
      stage1RemWidth r - (25 / 3) * (stage1Line r - (1 - r) / 2) - 3 / 500 := by
    dsimp [α]; unfold stage1RemWidth stage1Width stage1Line; ring
  have hlhs2 : (1 - α) * ((stage1DualScale (17 / 25) - 6 * (3 / 500)) * W₂ + 1 / 2500) +
      α * ((1 - 6 * (3 / 500)) * W₂ + 1 / 2500) =
      (stage1DualScale r - 6 * (3 / 500)) * W₂ + 1 / 2500 := by
    calc _ = ((1 - α) * (stage1DualScale (17 / 25) - 6 * (3 / 500)) + α * (1 - 6 * (3 / 500))) * W₂ +
        1 / 2500 := by ring
      _ = _ := by rw [haff1]
  exact (hlhs2.symm.trans_le (add_le_add ha_lo ha_hi)).trans_eq haff2

/-- **Convex Stage-1 slot-supply certificate with `ell ∈ [0, 3/500]`, `z_Jv ≤ ell`, and `x₆ ≥ 0`:**
Across `r ∈ [17/25, 19/26]`, `θ ∈ [0, 1]`, `ell ∈ [0, 3/500]`, `z_Jv ≤ ell`, `x₆ ≥ 0`, and
`z_J ≤ θ * (25/3) * (stage1Line r - (1 - r)/2)`, the surviving marked width
`z_rem(θ) - z_Jv - z_J` exceeds both the inverse and plain witness widths at `H_free` by at least
`1 / 2500`. -/
theorem stage1_convex_slot_supply_with_ell {r θ ell z_Jv x6 z_J ν x : ℝ}
    (hr0 : 17 / 25 ≤ r) (hr1 : r ≤ 19 / 26)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hell0 : 0 ≤ ell) (hell1 : ell ≤ 3 / 500) (hJv : z_Jv ≤ ell) (hx6 : 0 ≤ x6)
    (hν0 : 11 / 25 ≤ ν) (hν1 : ν ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hzJ : z_J ≤ θ * (25 / 3) * (stage1Line r - (1 - r) / 2)) :
    let H_th := (1 - θ) * 1 + θ * stage1DualScale r
    let z_rem_th := (1 - θ) * ((1 - r) / 2) + θ * stage1RemWidth r
    let H_free := H_th - 6 * ell - 6 * x6
    H_free * (1 - stage1Crossing ν x) / 2 + 1 / 2500 ≤ z_rem_th - z_Jv - z_J ∧
      H_free * (1 - 2 * ((1 + ν * rowP x / (2 * rowJ ν x)) - stage1Crossing ν x)) * (2 / 9) +
          1 / 2500 ≤
        z_rem_th - z_Jv - z_J := by
  intro H_th z_rem_th H_free
  have hw_nn := stage1_inv_plain_width_nonneg hν0 hν1 hx0 hx1
  set β := ell / (3 / 500)
  have hβ0 : 0 ≤ β := div_nonneg hell0 (by norm_num)
  have hβ1 : 0 ≤ 1 - β := by
    have : β ≤ 1 := (div_le_one (by norm_num : (0 : ℝ) < 3 / 500)).mpr hell1
    linarith
  have hell_eq : ell = (1 - β) * 0 + β * (3 / 500) := by dsimp [β]; ring
  have h_ell0_th1 := stage1_slot_supply_with_zJ hr0 hr1 hν0 hν1 hx0 hx1 (le_refl _)
  have h_ell0_19 := stage1_slot_supply_certificate (r := 19 / 26) (by norm_num) le_rfl hν0 hν1 hx0 hx1
  have hsc19 : stage1DualScale (19 / 26) = 1 := by unfold stage1DualScale stage1Width stage1Line; norm_num
  have hrem19 : stage1RemWidth (19 / 26) = 7 / 52 := by
    unfold stage1RemWidth stage1Width stage1Line; norm_num
  rw [hsc19, hrem19] at h_ell0_19
  have h_ell3_inv := stage1_slot_supply_ell3_inv hr0 hr1 hν0 hν1 hx0 hx1
  have h_ell3_pl := stage1_slot_supply_ell3_plain hr0 hr1 hν0 hν1 hx0 hx1
  constructor
  · let W₁ := (1 - stage1Crossing ν x) / 2
    have h_ell0_th0 : 1 * W₁ + 1 / 2500 ≤ (1 - r) / 2 := by dsimp [W₁]; linarith [h_ell0_19.1]
    have h_ell0_th1' : stage1DualScale r * W₁ + 1 / 2500 ≤
        stage1RemWidth r - (25 / 3) * (stage1Line r - (1 - r) / 2) := by
      dsimp [W₁]; linarith [h_ell0_th1.1]
    have h_hi3_th0 : (1 - 6 * (3 / 500)) * W₁ + 1 / 2500 ≤ (1 - r) / 2 - 3 / 500 := by
      dsimp [W₁]; linarith [h_ell3_inv.2]
    have hc_ell0 : H_th * W₁ + 1 / 2500 ≤
        z_rem_th - θ * (25 / 3) * (stage1Line r - (1 - r) / 2) := by
      have h0 := mul_le_mul_of_nonneg_left h_ell0_th0 (sub_nonneg.mpr hθ1)
      have h1 := mul_le_mul_of_nonneg_left h_ell0_th1' hθ0
      have hlhs : (1 - θ) * (1 * W₁ + 1 / 2500) + θ * (stage1DualScale r * W₁ + 1 / 2500) =
          H_th * W₁ + 1 / 2500 := by dsimp [H_th]; ring
      have hrhs : (1 - θ) * ((1 - r) / 2) +
          θ * (stage1RemWidth r - (25 / 3) * (stage1Line r - (1 - r) / 2)) =
          z_rem_th - θ * (25 / 3) * (stage1Line r - (1 - r) / 2) := by dsimp [z_rem_th]; ring
      exact (hlhs.symm.trans_le (add_le_add h0 h1)).trans_eq hrhs
    have hc_ell3 : (H_th - 6 * (3 / 500)) * W₁ + 1 / 2500 ≤
        z_rem_th - 3 / 500 - θ * (25 / 3) * (stage1Line r - (1 - r) / 2) := by
      have h0 := mul_le_mul_of_nonneg_left h_hi3_th0 (sub_nonneg.mpr hθ1)
      have h1 := mul_le_mul_of_nonneg_left h_ell3_inv.1 hθ0
      have hlhs : (1 - θ) * ((1 - 6 * (3 / 500)) * W₁ + 1 / 2500) +
          θ * ((stage1DualScale r - 6 * (3 / 500)) * W₁ + 1 / 2500) =
          (H_th - 6 * (3 / 500)) * W₁ + 1 / 2500 := by dsimp [H_th, W₁]; ring
      have hrhs : (1 - θ) * ((1 - r) / 2 - 3 / 500) +
          θ * (stage1RemWidth r - (25 / 3) * (stage1Line r - (1 - r) / 2) - 3 / 500) =
          z_rem_th - 3 / 500 - θ * (25 / 3) * (stage1Line r - (1 - r) / 2) := by dsimp [z_rem_th]; ring
      exact (hlhs.symm.trans_le (add_le_add h0 h1)).trans_eq hrhs
    have hb0 := mul_le_mul_of_nonneg_left hc_ell0 hβ1
    have hb1 := mul_le_mul_of_nonneg_left hc_ell3 hβ0
    have hx6_nn : 0 ≤ 6 * x6 * W₁ := mul_nonneg (by linarith) hw_nn.1
    have hconv_b : (H_th - 6 * ell) * W₁ + 1 / 2500 ≤
        z_rem_th - ell - θ * (25 / 3) * (stage1Line r - (1 - r) / 2) := by
      have hlhs : (1 - β) * (H_th * W₁ + 1 / 2500) + β * ((H_th - 6 * (3 / 500)) * W₁ + 1 / 2500) =
          (H_th - 6 * ell) * W₁ + 1 / 2500 := by rw [hell_eq]; ring
      have hrhs : (1 - β) * (z_rem_th - θ * (25 / 3) * (stage1Line r - (1 - r) / 2)) +
          β * (z_rem_th - 3 / 500 - θ * (25 / 3) * (stage1Line r - (1 - r) / 2)) =
          z_rem_th - ell - θ * (25 / 3) * (stage1Line r - (1 - r) / 2) := by rw [hell_eq]; ring
      exact (hlhs.symm.trans_le (add_le_add hb0 hb1)).trans_eq hrhs
    rw [mul_div_assoc]
    change H_free * W₁ + 1 / 2500 ≤ z_rem_th - z_Jv - z_J
    have hHf : H_free * W₁ = (H_th - 6 * ell) * W₁ - 6 * x6 * W₁ := by dsimp [H_free]; ring
    linarith [hconv_b, hx6_nn, hHf, hJv, hzJ]
  · let W₂ := (1 - 2 * ((1 + ν * rowP x / (2 * rowJ ν x)) - stage1Crossing ν x)) * (2 / 9)
    have h_ell0_th0 : 1 * W₂ + 1 / 2500 ≤ (1 - r) / 2 := by dsimp [W₂]; linarith [h_ell0_19.2]
    have h_ell0_th1' : stage1DualScale r * W₂ + 1 / 2500 ≤
        stage1RemWidth r - (25 / 3) * (stage1Line r - (1 - r) / 2) := by
      dsimp [W₂]; linarith [h_ell0_th1.2]
    have h_hi3_th0 : (1 - 6 * (3 / 500)) * W₂ + 1 / 2500 ≤ (1 - r) / 2 - 3 / 500 := by
      dsimp [W₂]; linarith [h_ell3_pl.2]
    have hc_ell0 : H_th * W₂ + 1 / 2500 ≤
        z_rem_th - θ * (25 / 3) * (stage1Line r - (1 - r) / 2) := by
      have h0 := mul_le_mul_of_nonneg_left h_ell0_th0 (sub_nonneg.mpr hθ1)
      have h1 := mul_le_mul_of_nonneg_left h_ell0_th1' hθ0
      have hlhs : (1 - θ) * (1 * W₂ + 1 / 2500) + θ * (stage1DualScale r * W₂ + 1 / 2500) =
          H_th * W₂ + 1 / 2500 := by dsimp [H_th]; ring
      have hrhs : (1 - θ) * ((1 - r) / 2) +
          θ * (stage1RemWidth r - (25 / 3) * (stage1Line r - (1 - r) / 2)) =
          z_rem_th - θ * (25 / 3) * (stage1Line r - (1 - r) / 2) := by dsimp [z_rem_th]; ring
      exact (hlhs.symm.trans_le (add_le_add h0 h1)).trans_eq hrhs
    have hc_ell3 : (H_th - 6 * (3 / 500)) * W₂ + 1 / 2500 ≤
        z_rem_th - 3 / 500 - θ * (25 / 3) * (stage1Line r - (1 - r) / 2) := by
      have h0 := mul_le_mul_of_nonneg_left h_hi3_th0 (sub_nonneg.mpr hθ1)
      have h1 := mul_le_mul_of_nonneg_left h_ell3_pl.1 hθ0
      have hlhs : (1 - θ) * ((1 - 6 * (3 / 500)) * W₂ + 1 / 2500) +
          θ * ((stage1DualScale r - 6 * (3 / 500)) * W₂ + 1 / 2500) =
          (H_th - 6 * (3 / 500)) * W₂ + 1 / 2500 := by dsimp [H_th, W₂]; ring
      have hrhs : (1 - θ) * ((1 - r) / 2 - 3 / 500) +
          θ * (stage1RemWidth r - (25 / 3) * (stage1Line r - (1 - r) / 2) - 3 / 500) =
          z_rem_th - 3 / 500 - θ * (25 / 3) * (stage1Line r - (1 - r) / 2) := by dsimp [z_rem_th]; ring
      exact (hlhs.symm.trans_le (add_le_add h0 h1)).trans_eq hrhs
    have hb0 := mul_le_mul_of_nonneg_left hc_ell0 hβ1
    have hb1 := mul_le_mul_of_nonneg_left hc_ell3 hβ0
    have hx6_nn : 0 ≤ 6 * x6 * W₂ := mul_nonneg (by linarith) hw_nn.2
    have hconv_b : (H_th - 6 * ell) * W₂ + 1 / 2500 ≤
        z_rem_th - ell - θ * (25 / 3) * (stage1Line r - (1 - r) / 2) := by
      have hlhs : (1 - β) * (H_th * W₂ + 1 / 2500) + β * ((H_th - 6 * (3 / 500)) * W₂ + 1 / 2500) =
          (H_th - 6 * ell) * W₂ + 1 / 2500 := by rw [hell_eq]; ring
      have hrhs : (1 - β) * (z_rem_th - θ * (25 / 3) * (stage1Line r - (1 - r) / 2)) +
          β * (z_rem_th - 3 / 500 - θ * (25 / 3) * (stage1Line r - (1 - r) / 2)) =
          z_rem_th - ell - θ * (25 / 3) * (stage1Line r - (1 - r) / 2) := by rw [hell_eq]; ring
      exact (hlhs.symm.trans_le (add_le_add hb0 hb1)).trans_eq hrhs
    rw [mul_assoc]
    change H_free * W₂ + 1 / 2500 ≤ z_rem_th - z_Jv - z_J
    have hHf : H_free * W₂ = (H_th - 6 * ell) * W₂ - 6 * x6 * W₂ := by dsimp [H_free]; ring
    linarith [hconv_b, hx6_nn, hHf, hJv, hzJ]

/-- **Convex Stage-1 large-value exponent certificate with `ell`, `z_Jv`, `x₆`, `V₀`, `z_J`, `z_coll`:**
Across `r ∈ [17/25, 19/26]`, `θ ∈ [0, 1]`, `0 ≤ z_Jv ≤ ell`, `x₆ ≥ 0`, `V₀ ≥ 0`, `z_J ≥ 0`,
`z_coll ≥ 0`, `ν ∈ [11/25, 3/4]`, and `x ∈ [0, 1/2]`, the total dual exponent
`3 * ell + 5 * u_sel + x₆ + H_free * rowCount ν x + ν * r_unm + 2 * x * ν * z_T` is at most
`1 - 1 / 2000`. -/
theorem stage1_convex_large_value_with_ell {r θ ell z_Jv x6 V₀ z_J z_coll ν x : ℝ}
    (hr0 : 17 / 25 ≤ r) (hr1 : r ≤ 19 / 26)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (_hell0 : 0 ≤ ell) (hJv0 : 0 ≤ z_Jv) (hJv : z_Jv ≤ ell)
    (hx6 : 0 ≤ x6) (hV0 : 0 ≤ V₀) (hzJ0 : 0 ≤ z_J) (hzc0 : 0 ≤ z_coll)
    (hν0 : 11 / 25 ≤ ν) (hν1 : ν ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    let u_sel := θ * stage1Width r
    let H_th := (1 - θ) * 1 + θ * stage1DualScale r
    let z_rem_th := (1 - θ) * ((1 - r) / 2) + θ * stage1RemWidth r
    let H_free := H_th - 6 * ell - 6 * x6
    let r_unm := r - V₀ - 3 * ell + z_Jv - z_coll
    let z_T := z_rem_th - z_Jv - z_J - z_coll
    3 * ell + 5 * u_sel + x6 + H_free * rowCount ν x +
      ν * r_unm + 2 * x * ν * z_T ≤ 1 - 1 / 2000 := by
  intro u_sel H_th z_rem_th H_free r_unm z_T
  have hJ := rowJ_pos (δ := ν) (x := x) (by linarith) (by linarith) hx1
  have hP0 : 0 ≤ rowP x := by unfold rowP; exact mul_nonneg (by linarith) (by linarith)
  have hrc_lo : 1 - ν ≤ rowCount ν x := by
    unfold rowCount
    have hq : 0 ≤ (5 / 6 - ν) * ν * rowP x / (2 * rowJ ν x) :=
      div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hP0) (by linarith)
    linarith
  have hcert1 := stage1_large_value_certificate hr0 hr1 hν0 hν1 hx0 hx1
  have hcert19 := stage1_large_value_certificate (r := 19 / 26) (by norm_num) le_rfl hν0 hν1 hx0 hx1
  have hw19 : stage1Width (19 / 26) = 0 := by unfold stage1Width stage1Line; norm_num
  have hsc19 : stage1DualScale (19 / 26) = 1 := by unfold stage1DualScale stage1Width stage1Line; norm_num
  have hrem19 : stage1RemWidth (19 / 26) = (1 - 19 / 26) / 2 := by
    unfold stage1RemWidth stage1Width stage1Line; norm_num
  rw [hw19, hsc19, hrem19] at hcert19
  have hr_mono : ν * r + 2 * x * ν * ((1 - r) / 2) ≤
      ν * (19 / 26) + 2 * x * ν * ((1 - 19 / 26) / 2) := by
    have h1 : 0 ≤ ν * (1 - x) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hcert0 : 1 * rowCount ν x + ν * r + 2 * x * ν * ((1 - r) / 2) ≤ 1 - 1 / 2000 := by
    linarith
  have hcert1_5 : 5 * stage1Width r + stage1DualScale r * rowCount ν x + ν * r +
      2 * x * ν * stage1RemWidth r ≤ 1 - 1 / 2000 := by
    have hds : stage1DualScale r + 6 * stage1Width r = 1 := by unfold stage1DualScale; ring
    linarith
  have hconv0 := mul_le_mul_of_nonneg_left hcert0 (sub_nonneg.mpr hθ1)
  have hconv1 := mul_le_mul_of_nonneg_left hcert1_5 hθ0
  have hx6_drop : (1 - 6 * rowCount ν x) * x6 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hx6
  have hell_drop : 3 * ell - 6 * ell * rowCount ν x - 3 * ν * ell +
      (ν - 2 * x * ν) * z_Jv ≤ 0 := by
    have h1 : (ν - 2 * x * ν) * z_Jv ≤ ν * ell := by
      have h2xν : 0 ≤ 2 * x * ν * z_Jv := by positivity
      have hνJv : ν * z_Jv ≤ ν * ell := mul_le_mul_of_nonneg_left hJv (by linarith)
      linarith
    have h2 : (3 - 6 * rowCount ν x - 2 * ν) * ell ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (hJv0.trans hJv)
    linarith
  have hz_drop : 0 ≤ ν * V₀ + (ν + 2 * x * ν) * z_coll + 2 * x * ν * z_J := by positivity
  dsimp [u_sel, H_th, z_rem_th, H_free, r_unm, z_T]
  linarith

/-- **Case 2 slot-keeping exponent bound (`ν ≤ 11/25` or `z_J + z_coll ≥ z_J_cap(θ)`):**
Whenever `H_free > max (1/10) r_unm` and `T_keep ⊆ T'` keeps width `z_keep` within `mesh_err` of
`min z_T (min ((H_free - max 0 r_unm) / 2) ((3 * H_free - 2 * max 0 r_unm) / 8))`, the dual
deleted-source exponent `3 * ell + 5 * u_sel + x6 + H_free + ν * (z_T - z_keep)` is at most
`1 + ν * mesh_err` in both Case 2a (`0 ≤ ν ≤ 11/25`) and Case 2b (`0 ≤ ν ≤ 3/4` with
`z_J + z_coll ≥ θ * (25/3) * (stage1Line r - (1 - r)/2)`). -/
theorem stage1_case2_keep_bound {r θ ell z_Jv x6 V₀ z_J z_coll z_keep mesh_err ν : ℝ}
    (hr0 : 17 / 25 ≤ r) (hr1 : r ≤ 19 / 26)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (_hell0 : 0 ≤ ell) (_hJv0 : 0 ≤ z_Jv) (_hJv : z_Jv ≤ ell)
    (hx6 : 0 ≤ x6) (hV0 : 0 ≤ V₀) (hzJ0 : 0 ≤ z_J) (hzc0 : 0 ≤ z_coll)
    (hν0 : 0 ≤ ν)
    (hcase : ν ≤ 11 / 25 ∨
      (ν ≤ 3 / 4 ∧ θ * (25 / 3) * (stage1Line r - (1 - r) / 2) ≤ z_J + z_coll)) :
    let u_sel := θ * stage1Width r
    let H_th := (1 - θ) * 1 + θ * stage1DualScale r
    let z_rem_th := (1 - θ) * ((1 - r) / 2) + θ * stage1RemWidth r
    let H_free := H_th - 6 * ell - 6 * x6
    let r_unm := r - V₀ - 3 * ell + z_Jv - z_coll
    let r_pos := max 0 r_unm
    let z_T := z_rem_th - z_Jv - z_J - z_coll
    0 ≤ z_T →
    min z_T (min ((H_free - r_pos) / 2) ((3 * H_free - 2 * r_pos) / 8)) - mesh_err ≤ z_keep →
    3 * ell + 5 * u_sel + x6 + H_free + ν * (z_T - z_keep) ≤ 1 + ν * mesh_err := by
  intro u_sel H_th z_rem_th H_free r_unm r_pos z_T hzT0 hkeep
  have h5u : 5 * u_sel + x6 + H_free = 1 - u_sel - 6 * ell - 5 * x6 := by
    dsimp [u_sel, H_free, H_th]; unfold stage1DualScale; ring
  have hdz0 : 0 ≤ stage1Line r - (1 - r) / 2 := by unfold stage1Line; linarith
  set w : ℝ := θ * (stage1Line r - (1 - r) / 2)
  have hw0 : 0 ≤ w := mul_nonneg hθ0 hdz0
  have hw1 : w ≤ 269 / 500 - 69 * r / 125 - (1 - r) / 2 := by
    have h1 : w ≤ stage1Line r - (1 - r) / 2 := mul_le_of_le_one_left hdz0 hθ1
    unfold stage1Line at h1; exact h1
  have hu_eq : u_sel = (11 / 3) * w := by
    dsimp [u_sel, w]; unfold stage1Width; ring
  have hH_eq : H_free = 1 - 22 * w - 6 * ell - 6 * x6 := by
    dsimp [H_free, H_th, w]; unfold stage1DualScale stage1Width; ring
  have hzT_eq : z_T = (1 - r) / 2 - (8 / 3) * w - z_Jv - z_J - z_coll := by
    dsimp [z_T, z_rem_th, w]; unfold stage1RemWidth stage1Width; ring
  have hzJ_w : θ * (25 / 3) * (stage1Line r - (1 - r) / 2) = (25 / 3) * w := by
    dsimp [w]; ring
  let cap := min z_T (min ((H_free - r_pos) / 2) ((3 * H_free - 2 * r_pos) / 8))
  have hdiff_le : ν * (z_T - z_keep) ≤ ν * (z_T - cap) + ν * mesh_err := by
    have := mul_le_mul_of_nonneg_left (by linarith [hkeep] : z_T - z_keep ≤ z_T - cap + mesh_err) hν0
    linarith
  suffices hmain : 3 * ell + (1 - u_sel - 6 * ell - 5 * x6) + ν * (z_T - cap) ≤ 1 by linarith
  -- Split into the three branches of `cap = min z_T (min b1 b2)`.
  rcases le_total z_T (min ((H_free - r_pos) / 2) ((3 * H_free - 2 * r_pos) / 8)) with hcapT | hcapB
  · have hcap_eq : cap = z_T := min_eq_left hcapT
    rw [hcap_eq, sub_self, mul_zero, hu_eq]
    linarith
  · have hcap_eq : cap = min ((H_free - r_pos) / 2) ((3 * H_free - 2 * r_pos) / 8) :=
      min_eq_right hcapB
    rcases le_total 0 r_unm with hru0 | hru_neg
    · have hr_eq : r_pos = r_unm := max_eq_right hru0
      rcases le_total ((H_free - r_pos) / 2) ((3 * H_free - 2 * r_pos) / 8) with hb1 | hb2
      · have hmin_b : min ((H_free - r_pos) / 2) ((3 * H_free - 2 * r_pos) / 8) = (H_free - r_pos) / 2 :=
          min_eq_left hb1
        rw [hmin_b] at hcapB
        rw [hcap_eq, hmin_b]
        have hdiff_nn : 0 ≤ z_T - (H_free - r_pos) / 2 := by linarith
        rcases hcase with hν11 | ⟨hν34, hzJ_ge⟩
        · have hν_step := mul_le_mul_of_nonneg_right hν11 hdiff_nn
          rw [hr_eq, hH_eq] at hb1
          rw [hr_eq, hH_eq, hzT_eq] at hν_step ⊢
          rw [hu_eq]
          dsimp [r_unm] at hν_step hb1 hru0 ⊢
          linarith
        · have hν_step := mul_le_mul_of_nonneg_right hν34 hdiff_nn
          rw [hzJ_w] at hzJ_ge
          rw [hr_eq, hH_eq] at hb1
          rw [hr_eq, hH_eq, hzT_eq] at hν_step ⊢
          rw [hu_eq]
          dsimp [r_unm] at hν_step hb1 hru0 ⊢
          linarith
      · have hmin_b : min ((H_free - r_pos) / 2) ((3 * H_free - 2 * r_pos) / 8) =
            (3 * H_free - 2 * r_pos) / 8 := min_eq_right hb2
        rw [hmin_b] at hcapB
        rw [hcap_eq, hmin_b]
        have hdiff_nn : 0 ≤ z_T - (3 * H_free - 2 * r_pos) / 8 := by linarith
        rcases hcase with hν11 | ⟨hν34, hzJ_ge⟩
        · have hν_step := mul_le_mul_of_nonneg_right hν11 hdiff_nn
          rw [hr_eq, hH_eq] at hb2
          rw [hr_eq, hH_eq, hzT_eq] at hν_step ⊢
          rw [hu_eq]
          dsimp [r_unm] at hν_step hb2 hru0 ⊢
          linarith
        · have hν_step := mul_le_mul_of_nonneg_right hν34 hdiff_nn
          rw [hzJ_w] at hzJ_ge
          rw [hr_eq, hH_eq] at hb2
          rw [hr_eq, hH_eq, hzT_eq] at hν_step ⊢
          rw [hu_eq]
          dsimp [r_unm] at hν_step hb2 hru0 ⊢
          linarith
    · have hr_eq : r_pos = 0 := max_eq_left hru_neg
      rcases le_total ((H_free - r_pos) / 2) ((3 * H_free - 2 * r_pos) / 8) with hb1 | hb2
      · have hmin_b : min ((H_free - r_pos) / 2) ((3 * H_free - 2 * r_pos) / 8) = (H_free - r_pos) / 2 :=
          min_eq_left hb1
        rw [hmin_b] at hcapB
        rw [hcap_eq, hmin_b]
        have hdiff_nn : 0 ≤ z_T - (H_free - r_pos) / 2 := by linarith
        have hν34_all : ν ≤ 3 / 4 := hcase.elim (fun h => by linarith) And.left
        have hν_step := mul_le_mul_of_nonneg_right hν34_all hdiff_nn
        rw [hr_eq, hH_eq] at hb1
        rw [hr_eq, hH_eq, hzT_eq] at hν_step hcapB ⊢
        rw [hu_eq]
        linarith
      · have hmin_b : min ((H_free - r_pos) / 2) ((3 * H_free - 2 * r_pos) / 8) =
            (3 * H_free - 2 * r_pos) / 8 := min_eq_right hb2
        rw [hmin_b] at hcapB
        rw [hcap_eq, hmin_b]
        have hdiff_nn : 0 ≤ z_T - (3 * H_free - 2 * r_pos) / 8 := by linarith
        have hν34_all : ν ≤ 3 / 4 := hcase.elim (fun h => by linarith) And.left
        have hν_step := mul_le_mul_of_nonneg_right hν34_all hdiff_nn
        rw [hr_eq, hH_eq] at hb2
        rw [hr_eq, hH_eq, hzT_eq] at hν_step hcapB ⊢
        rw [hu_eq]
        linarith

/-- Cauchy-Schwarz wrapper around `InverseInitialExcludedPolynomial.inverse_polynomial_decomposition`:
passing from `polynomial χ` to `polynomial (χ.excludePrimes S hS)` costs at most
`((idealDivisors (∏ P ∈ S, P)).card : ℝ)` summed over `j ∈ idealDivisors (∏ P ∈ S, P)` at `X / j.absNorm`. -/
theorem polynomial_norm_sq_le_excludePrimes_sum
    (χ : Character) (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (W : ℝ → ℂ) {X b : ℝ} (hX : 0 < X) (hW : ∀ x, W x ≠ 0 → x ≤ b) :
    ‖HeckeDyadic.polynomial χ true W X 0 0‖ ^ 2 ≤
      ((idealDivisors (∏ P ∈ S, P)).card : ℝ) *
        ∑ j ∈ idealDivisors (∏ P ∈ S, P),
          ‖HeckeDyadic.polynomial (χ.excludePrimes S hS) true W (X / (j.absNorm : ℝ)) 0 0‖ ^ 2 := by
  let D_S := idealDivisors (∏ P ∈ S, P)
  rw [InverseInitialExcludedPolynomial.inverse_polynomial_decomposition χ S hS W X 0 0 b hX hW]
  apply (norm_sum_sq_le_card_sum_norm_sq D_S _).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro j hj
  have hP_sq := InverseInitialExcludedPolynomial.prime_product_squarefree S hS
  have hjd : j ∣ ∏ P ∈ S, P := (mem_idealDivisors hP_sq.ne_zero).mp hj
  have hj0 : j ≠ 0 := ne_zero_of_dvd_ne_zero hP_sq.ne_zero hjd
  have hj1 : 1 ≤ (j.absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj0)
  have hj_pos : 0 < (j.absNorm : ℝ) := zero_lt_one.trans_le hj1
  have hm1 : ‖(UniqueFactorizationMonoid.moebius j : ℂ)‖ ≤ 1 := by
    by_cases hsq : Squarefree j
    · simp only [hsq.moebius_eq, Int.cast_pow, Int.cast_neg, Int.cast_one,
        norm_pow, norm_neg, norm_one, one_pow, le_refl]
    · simp [UniqueFactorizationMonoid.moebius_of_not_squarefree hsq]
  have hc1 : ‖idealCoeff χ j‖ ≤ 1 := idealCoeff_norm_le_one χ j
  have hn1 : ‖(j.absNorm : ℂ) ^ (-(1 / 2 : ℂ))‖ ≤ 1 := by
    rw [show (j.absNorm : ℂ) = ((j.absNorm : ℝ) : ℂ) by push_cast; rfl,
      show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow hj_pos.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hj_pos _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hj1 (by norm_num)
  have hcoef1 : ‖(UniqueFactorizationMonoid.moebius j : ℂ) * idealCoeff χ j *
      (j.absNorm : ℂ) ^ (-(1 / 2 : ℂ))‖ ≤ 1 := by
    rw [norm_mul, norm_mul]
    exact (mul_le_mul (mul_le_mul hm1 hc1 (norm_nonneg _) zero_le_one) hn1
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)).trans_eq (by ring)
  rw [norm_mul, mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) hcoef1)

/-- **Exact `IsBaseRayTwist` + `bad12FreeSplit` transfer on `poolPrimary F_pool`:**
For any `Ψ₀` with `IsBaseRayTwist base Ψ₀`, there exists `idx : Bad12Idx` such that for every
`u₀ : FreeRow` (`u_free := (bad12FreeSplit idx u₀).1`), both `inputConjugateRow` and `slotCharSum`
at `(Ψ₀, u₀.val)` equal those at `(base, u_free.val)` identically! -/
theorem exists_bad12_base_transfer_on_pool
    {σ : Type*} [DecidableEq σ] (q_per Dpool : ℕ) (base Ψ₀ : O →* ℂ)
    (hΨ : CanonicalCoefficientClass.IsBaseRayTwist base Ψ₀) :
    let F_pool := CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q_per) Dpool
    let hFa := CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q_per) Dpool
      (reflectionExcludedPrimes_bad q_per)
    letI : ∀ j : primePool F_pool, (Ideal.span {poolPrimary F_pool j}).IsMaximal :=
      fun j => by rw [poolPrimary_span F_pool hFa j]; infer_instance
    ∃ idx : Bad12Idx, ∀ (u₀ : FreeRow),
      let u_free := (bad12FreeSplit idx u₀).1
      (∀ (pool : Finset (primePool F_pool)) (H_test : Finset (primePool F_pool) → ℂ),
        inputConjugateRow (poolPrimary F_pool)
          (fun j => complexSexticChar (Ideal.span {poolPrimary F_pool j}) (poolPrimary_good F_pool hFa j))
          pool Ψ₀ 1 1 1 H_test u₀.val =
        inputConjugateRow (poolPrimary F_pool)
          (fun j => complexSexticChar (Ideal.span {poolPrimary F_pool j}) (poolPrimary_good F_pool hFa j))
          pool base 1 1 1 H_test u_free.val) ∧
      (∀ (lists : σ → Finset (primePool F_pool)) (a : σ → primePool F_pool → ℂ) (i : σ),
        slotCharSum (poolPrimary F_pool) (poolPrimary_good F_pool hFa) lists a Ψ₀ i u₀.val =
          slotCharSum (poolPrimary F_pool) (poolPrimary_good F_pool hFa) lists a base i u_free.val) := by
  intro F_pool hFa
  letI : ∀ j : primePool F_pool, (Ideal.span {poolPrimary F_pool j}).IsMaximal :=
    fun j => by rw [poolPrimary_span F_pool hFa j]; infer_instance
  -- Construct `idx : Bad12Idx` and prove the single-prime transfer on `primePool F_pool`.
  have hidx_ex : ∃ idx : Bad12Idx, ∀ (u₀ : FreeRow) (j : primePool F_pool),
      let u_free := (bad12FreeSplit idx u₀).1
      Ψ₀ (poolPrimary F_pool j) *
        star (complexSexticChar (Ideal.span {poolPrimary F_pool j})
          (poolPrimary_good F_pool hFa j) u₀.val) =
      base (poolPrimary F_pool j) *
        star (complexSexticChar (Ideal.span {poolPrimary F_pool j})
          (poolPrimary_good F_pool hFa j) u_free.val) := by
    rcases hΨ with rfl | ⟨ξ, rfl⟩
    · refine ⟨(0, false, false), ?_⟩
      intro u₀ j u_free
      have hspan_j : Ideal.span {poolPrimary F_pool j} = j.val := poolPrimary_span F_pool hFa j
      have hadm_j : quadraticIdealAdmissible j.val := by
        simpa using CanonicalRowCompletion.poolProduct_admissible F_pool hFa {j}
      have hq_sup : quadraticSupported (Ideal.span {poolPrimary F_pool j}) := by
        rw [hspan_j]; exact ⟨hadm_j.1, hadm_j.2.2⟩
      have hbad_j := (bad12_freeRow_transfer (0, false, false) u₀).2.2.2
        (Ideal.span {poolPrimary F_pool j}) hq_sup
      have hb1 : bad12Elem (0, false, false) = 1 := by simp [bad12Elem]
      have hchar_eq (z : O) :
          complexSexticChar (Ideal.span {poolPrimary F_pool j}) (poolPrimary_good F_pool hFa j) z =
            CanonicalRowCompletion.idealRowHom z (Ideal.span {poolPrimary F_pool j}) :=
        (CanonicalRowCompletion.idealRowHom_prime z (Ideal.span {poolPrimary F_pool j})
          (poolPrimary_good F_pool hFa j)).symm
      rw [hchar_eq u₀.val, hchar_eq u_free.val, ← hbad_j, hb1,
        CanonicalRowCompletion.idealRowHom_argument_mul,
        ← hchar_eq 1, map_one, MulChar.map_one, one_mul]
    · obtain ⟨idx, hidx⟩ := rayCharacter_eq_sextic_bad12 ξ
      refine ⟨idx, ?_⟩
      intro u₀ j u_free
      have hspan_j : Ideal.span {poolPrimary F_pool j} = j.val := poolPrimary_span F_pool hFa j
      have hp_ne0 : poolPrimary F_pool j ≠ 0 := poolPrimary_ne_zero F_pool hFa j
      have hj_prime : Prime j.val := by
        obtain ⟨I, _, hjI⟩ := CanonicalRowCompletion.mem_primePool_iff.mp j.property
        exact UniqueFactorizationMonoid.prime_of_normalized_factor j.val hjI
      have hp_prime : Prime (poolPrimary F_pool j) :=
        (Ideal.span_singleton_prime hp_ne0).mp (hspan_j.symm ▸ Ideal.isPrime_of_prime hj_prime)
      have hp_prim : lambda ^ 2 ∣ poolPrimary F_pool j - 1 :=
        (primaryIdealPrime_spec j.val hp_ne0).2.2.2
      have hadm_j : quadraticIdealAdmissible j.val := by
        simpa using CanonicalRowCompletion.poolProduct_admissible F_pool hFa {j}
      have hq_sup : quadraticSupported (Ideal.span {poolPrimary F_pool j}) := by
        rw [hspan_j]; exact ⟨hadm_j.1, hadm_j.2.2⟩
      have hray_j := hidx (poolPrimary F_pool j) hp_prime hp_prim hq_sup
      have hbad_j := (bad12_freeRow_transfer idx u₀).2.2.2 (Ideal.span {poolPrimary F_pool j}) hq_sup
      have hchar_eq (z : O) :
          complexSexticChar (Ideal.span {poolPrimary F_pool j}) (poolPrimary_good F_pool hFa j) z =
            CanonicalRowCompletion.idealRowHom z (Ideal.span {poolPrimary F_pool j}) :=
        (CanonicalRowCompletion.idealRowHom_prime z (Ideal.span {poolPrimary F_pool j})
          (poolPrimary_good F_pool hFa j)).symm
      rw [MonoidHom.mul_apply, hray_j, hchar_eq u₀.val, hchar_eq u_free.val, ← hbad_j,
        CanonicalRowCompletion.idealRowHom_argument_mul, star_mul]
      ring
  obtain ⟨idx, hprime_all⟩ := hidx_ex
  refine ⟨idx, ?_⟩
  intro u₀ u_free
  have hprime_j : ∀ j : primePool F_pool,
      Ψ₀ (poolPrimary F_pool j) *
        star (complexSexticChar (Ideal.span {poolPrimary F_pool j})
          (poolPrimary_good F_pool hFa j) u₀.val) =
      base (poolPrimary F_pool j) *
        star (complexSexticChar (Ideal.span {poolPrimary F_pool j})
          (poolPrimary_good F_pool hFa j) u_free.val) := hprime_all u₀
  -- Lift `hprime_j` to arbitrary `U : Finset (primePool F_pool)`.
  have hprod_U (U : Finset (primePool F_pool)) :
      Ψ₀ (∏ j ∈ U, poolPrimary F_pool j) *
        star (primeSubsetRow (poolPrimary F_pool)
          (fun j => complexSexticChar (Ideal.span {poolPrimary F_pool j}) (poolPrimary_good F_pool hFa j))
          U u₀.val) =
      base (∏ j ∈ U, poolPrimary F_pool j) *
        star (primeSubsetRow (poolPrimary F_pool)
          (fun j => complexSexticChar (Ideal.span {poolPrimary F_pool j}) (poolPrimary_good F_pool hFa j))
          U u_free.val) := by
    unfold primeSubsetRow
    rw [map_prod, map_prod, star_prod, star_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j _ => hprime_j j)
  refine ⟨?_, ?_⟩
  · intro pool H_test
    rw [initial_input_row _ (poolPrimary_good F_pool hFa),
      initial_input_row _ (poolPrimary_good F_pool hFa)]
    unfold supportConjugateSum
    apply Finset.sum_congr rfl
    intro U _
    have hU := hprod_U U
    calc supportMobius U * (Ψ₀ (∏ j ∈ U, poolPrimary F_pool j) *
            primeCoprimeMask (poolPrimary F_pool) U 1 * H_test U) *
          star (primeSubsetRow (poolPrimary F_pool) _ U u₀.val)
        = supportMobius U * primeCoprimeMask (poolPrimary F_pool) U 1 * H_test U *
            (Ψ₀ (∏ j ∈ U, poolPrimary F_pool j) *
              star (primeSubsetRow (poolPrimary F_pool) _ U u₀.val)) := by ring
      _ = supportMobius U * primeCoprimeMask (poolPrimary F_pool) U 1 * H_test U *
            (base (∏ j ∈ U, poolPrimary F_pool j) *
              star (primeSubsetRow (poolPrimary F_pool) _ U u_free.val)) := by rw [hU]
      _ = supportMobius U * (base (∏ j ∈ U, poolPrimary F_pool j) *
            primeCoprimeMask (poolPrimary F_pool) U 1 * H_test U) *
          star (primeSubsetRow (poolPrimary F_pool) _ U u_free.val) := by ring
  · intro lists a i
    unfold slotCharSum
    apply Finset.sum_congr rfl
    intro q _
    have hq := hprod_U {q}
    simp only [Finset.prod_singleton] at hq
    rw [mul_assoc, hq, ← mul_assoc]



end Stage1DualSixthFreeEnergy

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

end
