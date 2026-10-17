import GaloisForLFunctions.RHTower.CHMDOddCardinalKernelEquationsAndReadoutGramMatrices

/-!
# Universal Stationary Generator/Resolvent Dictionary, Nodal Polarization, and Parity Nodal Symmetry

This module completes the stationary-coordinates dictionary for arbitrary universal `sourcePair`
representations `∀ p, sourcePair p q = ⟪p.val.fst, v⟫_ℝ` and establishes the nodal difference,
resolvent nodal polarization, and parity nodal symmetry laws on `SourceGraph`:

1. **Universal Stationary Generator and Stationary Resolvent Dictionary**:
   for any `q : SourceGraph` and `v : MassSpace`, the condition
   `∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ` is equivalent to each of:
   - `resolvent ((2 : ℝ) • q.val.fst + v) = q.val.fst`,
   - `fullGroundEquiv q = stationaryRieszLift (q.val.fst + archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst + v)`,
   - `stationaryResolvent (q.val.fst + archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst + v) = q.val.fst`,
   - `q.val.fst - stationaryResolvent (q.val.fst + archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst) = stationaryResolvent v`,
   - `∃ hq : q.val.fst ∈ arithmeticGenerator.domain, arithmeticGenerator ⟨q.val.fst, hq⟩ - q.val.fst = v`,
   - `∃ hq : q.val.fst ∈ stationaryGenerator.domain, stationaryGenerator ⟨q.val.fst, hq⟩ - archDiagonalOperator q.val.fst - primeShiftOperator q.val.fst = v`,
   - `∀ p : SourceGraph, ⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv q).val.snd⟫_ℝ = ⟪p.val.fst, archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst + v⟫_ℝ`.
   Specializes to `signedRadical`, `constantLift 1`, `oddPolarVectorAt`, `CHMDThetaTranslate.lift`,
   `F.reVector`, `F.imVector`, and the odd cardinal mode `q_odd`.

2. **Nodal Difference and Resolvent Nodal Polarization Laws**:
   - `sourcePair_absGraph_self`: `sourcePair (absGraph q) q = sourceEnergy (posGraph q) - sourceEnergy (negGraph q)`.
   - `sourceEnergy_posGraph_sub_negGraph_of_sourcePair_eq_inner`: if `∀ p, sourcePair p q = ⟪p.val.fst, v⟫_ℝ`,
     then `sourceEnergy (posGraph q) - sourceEnergy (negGraph q) = ⟪(absGraph q).val.fst, v⟫_ℝ`.
   - `inner_resolvent_absGraph_sub_self`:
     `⟪resolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ - ⟪resolvent p.val.fst, p.val.fst⟫_ℝ = 4 * ⟪resolvent (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`.
   - `inner_resolvent_primGraph_absGraph_sub_self_of_primitive`: for primitive `p` (`⟪p.val.fst, oneL⟫_ℝ = 0`),
     `⟪resolvent (primGraph (absGraph p)).val.fst, (primGraph (absGraph p)).val.fst⟫_ℝ - ⟪resolvent p.val.fst, p.val.fst⟫_ℝ = 4 * ⟪resolvent (primGraph (posGraph p)).val.fst, (primGraph (negGraph p)).val.fst⟫_ℝ`.

3. **Even and Odd Nodal Symmetry Laws**:
   - For odd `p` (`reflectGraph p = -p`):
     `evenGraphPart (posGraph p) = (1 / 2 : ℝ) • absGraph p`,
     `oddGraphPart (posGraph p) = (1 / 2 : ℝ) • p`,
     `sourceEnergy (posGraph p) = sourceEnergy (negGraph p) = (1 / 4) * sourceEnergy (absGraph p) + (1 / 4) * sourceEnergy p`,
     `sourcePair (posGraph p) (negGraph p) = (1 / 4) * sourceEnergy (absGraph p) - (1 / 4) * sourceEnergy p`.
   - For even `p` (`reflectGraph p = p`):
     `reflectGraph (posGraph p) = posGraph p`, `reflectGraph (negGraph p) = negGraph p`,
     `evenGraphPart (posGraph p) = posGraph p`, `oddGraphPart (posGraph p) = 0`.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace BigOperators
noncomputable section

namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump CHMDTranslation ThetaSourceWard

/-! ## Section 1: Universal Stationary Generator and Stationary Resolvent Dictionary -/

/-- For any `u : MassSpace`, `(2 : ℝ) • u - groundPerturbation u = u + archDiagonalOperator u + primeShiftOperator u`. -/
theorem two_smul_sub_groundPerturbation_eq (u : MassSpace) :
    (2 : ℝ) • u - groundPerturbation u =
      u + archDiagonalOperator u + primeShiftOperator u := by
  have h := congrArg (fun T : MassSpace →L[ℝ] MassSpace => T u) groundPerturbation_sub_id_eq
  change groundPerturbation u - u = -primeShiftOperator u - archDiagonalOperator u at h
  have h2 : groundPerturbation u = -primeShiftOperator u - archDiagonalOperator u + u :=
    sub_eq_iff_eq_add.mp h
  rw [h2, two_smul]
  abel

/-- Universal `sourcePair` representation is equivalent to the resolvent preimage equation
`resolvent ((2 : ℝ) • q.val.fst + v) = q.val.fst`. -/
theorem sourcePair_eq_inner_iff_resolvent_preimage (q : SourceGraph) (v : MassSpace) :
    (∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ) ↔
      resolvent ((2 : ℝ) • q.val.fst + v) = q.val.fst := by
  rw [sourcePair_eq_inner_iff_resolvent, map_add, map_smul]
  constructor <;> intro h
  · exact (sub_eq_iff_eq_add'.mp h).symm
  · exact sub_eq_iff_eq_add'.mpr h.symm

/-- **Universal Stationary Riesz-Lift Equivalence**:
`∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ` if and only if
`fullGroundEquiv q = stationaryRieszLift (q.val.fst + archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst + v)`. -/
theorem sourcePair_eq_inner_iff_stationaryRieszLift (q : SourceGraph) (v : MassSpace) :
    (∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ) ↔
      fullGroundEquiv q =
        stationaryRieszLift
          (q.val.fst + archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst + v) := by
  have hshift : (v + (2 : ℝ) • q.val.fst) - groundPerturbation q.val.fst =
      q.val.fst + archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst + v := by
    have h1 := two_smul_sub_groundPerturbation_eq q.val.fst
    calc (v + (2 : ℝ) • q.val.fst) - groundPerturbation q.val.fst
        = ((2 : ℝ) • q.val.fst - groundPerturbation q.val.fst) + v := by abel
      _ = q.val.fst + archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst + v := by
        rw [h1]
  constructor
  · intro h
    have hr : q = rieszLift (v + (2 : ℝ) • q.val.fst) :=
      sourcePair_eq_inner_iff_rieszLift.mp h
    have hres : resolvent (v + (2 : ℝ) • q.val.fst) = q.val.fst := by
      change (rieszLift (v + (2 : ℝ) • q.val.fst)).val.fst = q.val.fst
      rw [← hr]
    have hstat := stationaryRieszLift_full (v + (2 : ℝ) • q.val.fst)
    rw [hres, ← hr, hshift] at hstat
    exact hstat.symm
  · intro h
    rw [sourcePair_eq_inner_iff_resolvent_preimage]
    have hstat : stationaryResolvent
        (q.val.fst + archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst + v) =
        q.val.fst := by
      rw [stationaryResolvent_apply, ← h, fullGroundEquiv_source]
      rfl
    have h2 : q.val.fst + (q.val.fst + v) - groundPerturbation q.val.fst =
        q.val.fst + archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst + v := by
      calc q.val.fst + (q.val.fst + v) - groundPerturbation q.val.fst
          = (v + (2 : ℝ) • q.val.fst) - groundPerturbation q.val.fst := by
            rw [two_smul]; abel
        _ = q.val.fst + archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst + v := hshift
    have h3 : resolvent (q.val.fst + (q.val.fst + v)) = q.val.fst := by
      rw [full_generator_relation_iff_stationary, h2]
      exact hstat
    have h4 : q.val.fst + (q.val.fst + v) = (2 : ℝ) • q.val.fst + v := by
      rw [two_smul]; abel
    rwa [h4] at h3

/-- **Universal Stationary Resolvent Equivalence**:
`∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ` if and only if
`q.val.fst - stationaryResolvent (q.val.fst + archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst) = stationaryResolvent v`. -/
theorem sourcePair_eq_inner_iff_stationaryResolvent (q : SourceGraph) (v : MassSpace) :
    (∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ) ↔
      q.val.fst -
          stationaryResolvent
            (q.val.fst + archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst) =
        stationaryResolvent v := by
  rw [sourcePair_eq_inner_iff_stationaryRieszLift]
  constructor
  · intro h
    have h1 := congrArg stationaryGroundSourceMap h
    rw [fullGroundEquiv_source, ← stationaryResolvent_apply, map_add] at h1
    exact sub_eq_iff_eq_add'.mpr h1
  · intro h
    apply stationaryGroundSourceMap_injective
    rw [fullGroundEquiv_source, ← stationaryResolvent_apply, map_add]
    exact sub_eq_iff_eq_add'.mp h

/-- **Universal Maximal-Domain `arithmeticGenerator` Equivalence**:
`∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ` if and only if
`q.val.fst ∈ arithmeticGenerator.domain` and `arithmeticGenerator q.val.fst - q.val.fst = v`. -/
theorem sourcePair_eq_inner_iff_arithmeticGenerator (q : SourceGraph) (v : MassSpace) :
    (∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ) ↔
      ∃ hq : q.val.fst ∈ arithmeticGenerator.domain,
        arithmeticGenerator ⟨q.val.fst, hq⟩ - q.val.fst = v := by
  rw [sourcePair_eq_inner_iff_resolvent_preimage]
  constructor
  · intro h
    refine ⟨mem_arithmetic_domain_of_resolvent_preimage h, ?_⟩
    rw [arithmeticGenerator_of_resolvent_preimage h, add_sub_cancel_left]
  · rintro ⟨hq, hgen⟩
    have hid := generatorOfResolvent_identity resolvent resolvent_injective ⟨q.val.fst, hq⟩
    change resolvent (q.val.fst + arithmeticGenerator ⟨q.val.fst, hq⟩) = q.val.fst at hid
    have h2 : arithmeticGenerator ⟨q.val.fst, hq⟩ = v + q.val.fst := sub_eq_iff_eq_add.mp hgen
    have h3 : q.val.fst + (v + q.val.fst) = (2 : ℝ) • q.val.fst + v := by
      rw [two_smul]; abel
    rwa [h2, h3] at hid

/-- **Universal Maximal-Domain `stationaryGenerator` Equivalence**:
`∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ` if and only if
`q.val.fst ∈ stationaryGenerator.domain` and
`stationaryGenerator q.val.fst - archDiagonalOperator q.val.fst - primeShiftOperator q.val.fst = v`. -/
theorem sourcePair_eq_inner_iff_stationaryGenerator (q : SourceGraph) (v : MassSpace) :
    (∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ) ↔
      ∃ hq : q.val.fst ∈ stationaryGenerator.domain,
        stationaryGenerator ⟨q.val.fst, hq⟩ -
          archDiagonalOperator q.val.fst - primeShiftOperator q.val.fst = v := by
  rw [sourcePair_eq_inner_iff_arithmeticGenerator]
  constructor
  · rintro ⟨hq, hgen⟩
    refine ⟨arithmeticGenerator_domain_eq_stationary ▸ hq, ?_⟩
    rw [← arithmeticGenerator_sub_id_eq_stationary ⟨q.val.fst, hq⟩, hgen]
  · rintro ⟨hq, hgen⟩
    have hqa : q.val.fst ∈ arithmeticGenerator.domain :=
      arithmeticGenerator_domain_eq_stationary.symm ▸ hq
    refine ⟨hqa, ?_⟩
    rw [arithmeticGenerator_sub_id_eq_stationary ⟨q.val.fst, hqa⟩]
    exact hgen

/-- **Universal Stationary Edge-Pairing Equivalence**:
`∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ` if and only if for every `p : SourceGraph`,
`⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv q).val.snd⟫_ℝ = ⟪p.val.fst, archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst + v⟫_ℝ`. -/
theorem sourcePair_eq_inner_iff_stationary_edge_inner (q : SourceGraph) (v : MassSpace) :
    (∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ) ↔
      ∀ p : SourceGraph,
        ⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv q).val.snd⟫_ℝ =
          ⟪p.val.fst, archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst + v⟫_ℝ := by
  constructor
  · intro h p
    have h1 := sourcePair_eq_stationary_sub_arch_sub_primeShift p q
    rw [h p, ← inner_archDiagonalOperator, archDiagonalOperator_symmetric,
      primeShiftOperator_symmetric] at h1
    rw [inner_add_right, inner_add_right]
    linarith
  · intro h p
    have h1 := sourcePair_eq_stationary_sub_arch_sub_primeShift p q
    have h2 := h p
    rw [← inner_archDiagonalOperator, archDiagonalOperator_symmetric,
      primeShiftOperator_symmetric] at h1
    rw [inner_add_right, inner_add_right] at h2
    linarith

/-- For any `(q, v)` satisfying `∀ p, sourcePair p q = ⟪p.val.fst, v⟫_ℝ`, the stationary energy of
`Θ · q.val.fst` is `archGroundConstant * ‖thetaToVolume q.val.fst‖ ^ 2 + ⟪primeShiftOperator q.val.fst, q.val.fst⟫_ℝ + ⟪q.val.fst, v⟫_ℝ`. -/
theorem stationaryEnergy_of_sourcePair_eq_inner {q : SourceGraph} {v : MassSpace}
    (h : ∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ) :
    stationaryEnergy (thetaProduct q.val.fst) =
      archGroundConstant * ‖thetaToVolume q.val.fst‖ ^ 2 +
        ⟪primeShiftOperator q.val.fst, q.val.fst⟫_ℝ + ⟪q.val.fst, v⟫_ℝ := by
  have h1 := sourceEnergy_eq_stationary_sub_arch_sub_primeShift q
  have h2 := sourceEnergy_eq_inner_of_sourcePair_eq_inner h
  linarith

/-- Specialization to `signedRadical`: every `r ∈ signedRadical` lies in `stationaryGenerator.domain`
and satisfies `stationaryGenerator r = archDiagonalOperator r + primeShiftOperator r` and
`stationaryResolvent (r + archDiagonalOperator r + primeShiftOperator r) = r`. -/
theorem mem_signedRadical_iff_stationaryResolvent (r : SourceGraph) :
    r ∈ signedRadical ↔
      r.val.fst =
        stationaryResolvent
          (r.val.fst + archDiagonalOperator r.val.fst + primeShiftOperator r.val.fst) := by
  have h0 : r ∈ signedRadical ↔ ∀ p : SourceGraph, sourcePair p r = ⟪p.val.fst, (0 : MassSpace)⟫_ℝ := by
    constructor
    · intro hr p
      rw [sourcePair_symm, hr p, inner_zero_right]
    · intro hr p
      have hp := hr p
      rw [sourcePair_symm, inner_zero_right] at hp
      exact hp
  rw [h0, sourcePair_eq_inner_iff_stationaryResolvent, map_zero, sub_eq_zero]

theorem mem_signedRadical_iff_stationaryGenerator (r : SourceGraph) :
    r ∈ signedRadical ↔
      ∃ hr : r.val.fst ∈ stationaryGenerator.domain,
        stationaryGenerator ⟨r.val.fst, hr⟩ =
          archDiagonalOperator r.val.fst + primeShiftOperator r.val.fst := by
  have h0 : r ∈ signedRadical ↔ ∀ p : SourceGraph, sourcePair p r = ⟪p.val.fst, (0 : MassSpace)⟫_ℝ := by
    constructor
    · intro hr p
      rw [sourcePair_symm, hr p, inner_zero_right]
    · intro hr p
      have hp := hr p
      rw [sourcePair_symm, inner_zero_right] at hp
      exact hp
  rw [h0, sourcePair_eq_inner_iff_stationaryGenerator]
  refine exists_congr fun hr => ?_
  rw [sub_sub, sub_eq_zero]

/-- Specialization to `oneL = (constantLift 1).val.fst`: since `sourcePair p (constantLift 1) = ⟪p.val.fst, -oneL⟫_ℝ`,
the `+ oneL` term cancels, giving the exact ground-state identity
`stationaryResolvent (archDiagonalOperator oneL + primeShiftOperator oneL) = oneL`. -/
theorem stationaryResolvent_oneL_shift :
    stationaryResolvent (archDiagonalOperator oneL + primeShiftOperator oneL) = oneL := by
  have hfst : (constantLift 1).val.fst = oneL := by
    simpa using constantLift_fst_eq_smul_oneL 1
  have hpair : ∀ p : SourceGraph, sourcePair p (constantLift 1) = ⟪p.val.fst, -oneL⟫_ℝ := by
    intro p
    rw [sourcePair_symm, sourcePair_ground, hfst, inner_neg_right, real_inner_comm]
  have h1 := (sourcePair_eq_inner_iff_stationaryResolvent (constantLift 1) (-oneL)).mp hpair
  have h2 : stationaryResolvent
      ((oneL + archDiagonalOperator oneL + primeShiftOperator oneL) + -oneL) = oneL := by
    rw [map_add]
    rw [hfst] at h1
    exact (sub_eq_iff_eq_add'.mp h1).symm
  have h3 : (oneL + archDiagonalOperator oneL + primeShiftOperator oneL) + -oneL =
      archDiagonalOperator oneL + primeShiftOperator oneL := by abel
  rwa [h3] at h2

/-- Specialization to `oddPolarVectorAt`: for every nonzero small shift `|a| ≤ radius`,
`q = oddPolarVectorAt a ha` satisfies
`q.val.fst - stationaryResolvent (q.val.fst + archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst) = stationaryResolvent tanhL`. -/
theorem stationaryResolvent_oddPolarVectorAt_fst {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    (oddPolarVectorAt a ha).val.fst -
        stationaryResolvent
          ((oddPolarVectorAt a ha).val.fst +
            archDiagonalOperator (oddPolarVectorAt a ha).val.fst +
            primeShiftOperator (oddPolarVectorAt a ha).val.fst) =
      stationaryResolvent tanhL := by
  rw [← sourcePair_eq_inner_iff_stationaryResolvent]
  intro p
  rw [sourcePair_symm, sourcePair_oddPolarVectorAt_eq_inner_tanhL hane ha, real_inner_comm]

/-- Specialization to `CHMDThetaTranslate.lift`: for every small shift `|a| ≤ radius`,
`q = CHMDThetaTranslate.lift a ha` satisfies
`q.val.fst - stationaryResolvent (q.val.fst + archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst) = -Real.cosh (a / 2) • stationaryResolvent oneL + Real.sinh (a / 2) • stationaryResolvent tanhL`. -/
theorem stationaryResolvent_thetaTranslate_fst (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    (CHMDThetaTranslate.lift a ha).val.fst -
        stationaryResolvent
          ((CHMDThetaTranslate.lift a ha).val.fst +
            archDiagonalOperator (CHMDThetaTranslate.lift a ha).val.fst +
            primeShiftOperator (CHMDThetaTranslate.lift a ha).val.fst) =
      -Real.cosh (a / 2) • stationaryResolvent oneL +
        Real.sinh (a / 2) • stationaryResolvent tanhL := by
  have h1 : ∀ p : SourceGraph,
      sourcePair p (CHMDThetaTranslate.lift a ha) =
        ⟪p.val.fst, -Real.cosh (a / 2) • oneL + Real.sinh (a / 2) • tanhL⟫_ℝ := by
    intro p
    rw [sourcePair_symm, sourcePair_thetaTranslate a ha p, inner_add_right,
      real_inner_smul_right, real_inner_smul_right]
  have h2 := (sourcePair_eq_inner_iff_stationaryResolvent
    (CHMDThetaTranslate.lift a ha) (-Real.cosh (a / 2) • oneL + Real.sinh (a / 2) • tanhL)).mp h1
  rw [stationaryResolvent.map_add (-Real.cosh (a / 2) • oneL),
    stationaryResolvent.map_smul, stationaryResolvent.map_smul] at h2
  exact h2

/-- Specialization to the even cardinal real vector `F.reVector`:
`F.reVector.val.fst - stationaryResolvent (F.reVector.val.fst + archDiagonalOperator F.reVector.val.fst + primeShiftOperator F.reVector.val.fst) = cardinalOrbitMass a • stationaryResolvent (cosineKernelReL a)`. -/
theorem stationaryResolvent_reVector_fst {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) :
    F.reVector.val.fst -
        stationaryResolvent
          (F.reVector.val.fst +
            archDiagonalOperator F.reVector.val.fst +
            primeShiftOperator F.reVector.val.fst) =
      cardinalOrbitMass a • stationaryResolvent (cosineKernelReL a) := by
  have h1 : ∀ p : SourceGraph,
      sourcePair p F.reVector = ⟪p.val.fst, cardinalOrbitMass a • cosineKernelReL a⟫_ℝ := by
    intro p
    rw [F.pair_re ha hz p, graphCosineReadout_re_eq_inner, real_inner_smul_right]
  have h2 := (sourcePair_eq_inner_iff_stationaryResolvent
    F.reVector (cardinalOrbitMass a • cosineKernelReL a)).mp h1
  rwa [map_smul] at h2

/-- Specialization to the even cardinal imaginary vector `F.imVector`:
`F.imVector.val.fst - stationaryResolvent (F.imVector.val.fst + archDiagonalOperator F.imVector.val.fst + primeShiftOperator F.imVector.val.fst) = cardinalOrbitMass a • stationaryResolvent (cosineKernelImL a)`. -/
theorem stationaryResolvent_imVector_fst {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) :
    F.imVector.val.fst -
        stationaryResolvent
          (F.imVector.val.fst +
            archDiagonalOperator F.imVector.val.fst +
            primeShiftOperator F.imVector.val.fst) =
      cardinalOrbitMass a • stationaryResolvent (cosineKernelImL a) := by
  have h1 : ∀ p : SourceGraph,
      sourcePair p F.imVector = ⟪p.val.fst, cardinalOrbitMass a • cosineKernelImL a⟫_ℝ := by
    intro p
    rw [F.pair_im ha hz p, graphCosineReadout_im_eq_inner, real_inner_smul_right]
  have h2 := (sourcePair_eq_inner_iff_stationaryResolvent
    F.imVector (cardinalOrbitMass a • cosineKernelImL a)).mp h1
  rwa [map_smul] at h2

/-! ## Section 2: Nodal Difference Identity and Resolvent Nodal Polarization Laws -/

/-- For any `p, q : SourceGraph`,
`sourcePair (absGraph p) q = sourcePair (posGraph p) q + sourcePair (negGraph p) q`. -/
theorem sourcePair_absGraph_left (p q : SourceGraph) :
    sourcePair (absGraph p) q =
      sourcePair (posGraph p) q + sourcePair (negGraph p) q := by
  rw [← posGraph_add_negGraph, sourcePair_add_left]

/-- For any `p, q : SourceGraph`,
`sourcePair p q = sourcePair (posGraph p) q - sourcePair (negGraph p) q`. -/
theorem sourcePair_eq_posGraph_sub_negGraph_left (p q : SourceGraph) :
    sourcePair p q =
      sourcePair (posGraph p) q - sourcePair (negGraph p) q := by
  conv_lhs => rw [← posGraph_sub_negGraph p]
  rw [sourcePair_sub_left]

/-- **Nodal Difference Identity for `sourcePair (absGraph q) q`**:
for every `q : SourceGraph`, the cross-jump pairing `sourcePair (posGraph q) (negGraph q)` cancels
identically in `sourcePair (absGraph q) q`, giving
`sourcePair (absGraph q) q = sourceEnergy (posGraph q) - sourceEnergy (negGraph q)`. -/
theorem sourcePair_absGraph_self (q : SourceGraph) :
    sourcePair (absGraph q) q =
      sourceEnergy (posGraph q) - sourceEnergy (negGraph q) := by
  have h1 : sourcePair (absGraph q) q =
      sourcePair (posGraph q + negGraph q) (posGraph q - negGraph q) := by
    rw [posGraph_add_negGraph, posGraph_sub_negGraph]
  rw [h1, sourcePair_add_left, sourcePair_sub_right, sourcePair_sub_right,
    sourcePair_self, sourcePair_self, sourcePair_symm (negGraph q) (posGraph q)]
  ring

/-- Whenever `∀ p, sourcePair p q = ⟪p.val.fst, v⟫_ℝ`, the nodal energy difference is given by the
mass-space pairing against `(absGraph q).val.fst`:
`sourceEnergy (posGraph q) - sourceEnergy (negGraph q) = ⟪(absGraph q).val.fst, v⟫_ℝ`. -/
theorem sourceEnergy_posGraph_sub_negGraph_of_sourcePair_eq_inner {q : SourceGraph} {v : MassSpace}
    (h : ∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ) :
    sourceEnergy (posGraph q) - sourceEnergy (negGraph q) =
      ⟪(absGraph q).val.fst, v⟫_ℝ := by
  rw [← sourcePair_absGraph_self, h (absGraph q)]

/-- **Resolvent Nodal Polarization Identity on `SourceGraph`**:
for every `p : SourceGraph`,
`⟪resolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ - ⟪resolvent p.val.fst, p.val.fst⟫_ℝ = 4 * ⟪resolvent (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`. -/
theorem inner_resolvent_absGraph_sub_self (p : SourceGraph) :
    ⟪resolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ -
        ⟪resolvent p.val.fst, p.val.fst⟫_ℝ =
      4 * ⟪resolvent (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  have hadd : (absGraph p).val.fst = (posGraph p).val.fst + (negGraph p).val.fst :=
    congrArg (fun q : SourceGraph => q.val.fst) (posGraph_add_negGraph p).symm
  have hsub : p.val.fst = (posGraph p).val.fst - (negGraph p).val.fst :=
    congrArg (fun q : SourceGraph => q.val.fst) (posGraph_sub_negGraph p).symm
  rw [hadd]
  conv_lhs => enter [2]; rw [hsub]
  rw [map_add, map_sub, inner_add_left, inner_add_right, inner_add_right,
    inner_sub_left, inner_sub_right, inner_sub_right,
    resolvent_symm (negGraph p).val.fst (posGraph p).val.fst,
    real_inner_comm (negGraph p).val.fst (resolvent (posGraph p).val.fst)]
  ring

theorem primGraph_add (p q : SourceGraph) :
    primGraph (p + q) = primGraph p + primGraph q := by
  unfold primGraph
  have hfst : (p + q).val.fst = p.val.fst + q.val.fst := rfl
  rw [hfst, inner_add_left, mul_add, add_smul]
  abel

theorem primGraph_sub (p q : SourceGraph) :
    primGraph (p - q) = primGraph p - primGraph q := by
  unfold primGraph
  have hfst : (p - q).val.fst = p.val.fst - q.val.fst := rfl
  rw [hfst, inner_sub_left, mul_sub, sub_smul]
  abel

theorem primGraph_eq_self_of_primitive {p : SourceGraph} (hp : ⟪p.val.fst, oneL⟫_ℝ = 0) :
    primGraph p = p := by
  unfold primGraph
  rw [hp, mul_zero, zero_smul, sub_zero]

theorem primGraph_posGraph_add_negGraph (p : SourceGraph) :
    primGraph (posGraph p) + primGraph (negGraph p) = primGraph (absGraph p) := by
  rw [← primGraph_add, posGraph_add_negGraph]

theorem primGraph_posGraph_sub_negGraph (p : SourceGraph) :
    primGraph (posGraph p) - primGraph (negGraph p) = primGraph p := by
  rw [← primGraph_sub, posGraph_sub_negGraph]

/-- **Primitive Resolvent Nodal Polarization Identity**:
for every `p : SourceGraph`,
`⟪resolvent (primGraph (absGraph p)).val.fst, (primGraph (absGraph p)).val.fst⟫_ℝ - ⟪resolvent (primGraph p).val.fst, (primGraph p).val.fst⟫_ℝ = 4 * ⟪resolvent (primGraph (posGraph p)).val.fst, (primGraph (negGraph p)).val.fst⟫_ℝ`. -/
theorem inner_resolvent_primGraph_absGraph_sub_primGraph (p : SourceGraph) :
    ⟪resolvent (primGraph (absGraph p)).val.fst, (primGraph (absGraph p)).val.fst⟫_ℝ -
        ⟪resolvent (primGraph p).val.fst, (primGraph p).val.fst⟫_ℝ =
      4 * ⟪resolvent (primGraph (posGraph p)).val.fst, (primGraph (negGraph p)).val.fst⟫_ℝ := by
  have hadd : (primGraph (absGraph p)).val.fst =
      (primGraph (posGraph p)).val.fst + (primGraph (negGraph p)).val.fst :=
    congrArg (fun q : SourceGraph => q.val.fst) (primGraph_posGraph_add_negGraph p).symm
  have hsub : (primGraph p).val.fst =
      (primGraph (posGraph p)).val.fst - (primGraph (negGraph p)).val.fst :=
    congrArg (fun q : SourceGraph => q.val.fst) (primGraph_posGraph_sub_negGraph p).symm
  rw [hadd, hsub, map_add, map_sub, inner_add_left, inner_add_right, inner_add_right,
    inner_sub_left, inner_sub_right, inner_sub_right,
    resolvent_symm (primGraph (negGraph p)).val.fst (primGraph (posGraph p)).val.fst,
    real_inner_comm (primGraph (negGraph p)).val.fst (resolvent (primGraph (posGraph p)).val.fst)]
  ring

/-- When `p` is primitive (`⟪p.val.fst, oneL⟫_ℝ = 0`),
`⟪resolvent (primGraph (absGraph p)).val.fst, (primGraph (absGraph p)).val.fst⟫_ℝ - ⟪resolvent p.val.fst, p.val.fst⟫_ℝ = 4 * ⟪resolvent (primGraph (posGraph p)).val.fst, (primGraph (negGraph p)).val.fst⟫_ℝ`. -/
theorem inner_resolvent_primGraph_absGraph_sub_self_of_primitive {p : SourceGraph}
    (hp : ⟪p.val.fst, oneL⟫_ℝ = 0) :
    ⟪resolvent (primGraph (absGraph p)).val.fst, (primGraph (absGraph p)).val.fst⟫_ℝ -
        ⟪resolvent p.val.fst, p.val.fst⟫_ℝ =
      4 * ⟪resolvent (primGraph (posGraph p)).val.fst, (primGraph (negGraph p)).val.fst⟫_ℝ := by
  have h := inner_resolvent_primGraph_absGraph_sub_primGraph p
  rwa [primGraph_eq_self_of_primitive hp] at h

/-! ## Section 3: Even and Odd Nodal Symmetry Laws on `SourceGraph` -/

/-- For an odd graph vector `p` (`reflectGraph p = -p`), `reflectGraph (posGraph p) = negGraph p`. -/
theorem reflectGraph_posGraph_of_odd {p : SourceGraph} (hp : reflectGraph p = -p) :
    reflectGraph (posGraph p) = negGraph p := by
  rw [reflectGraph_posGraph, hp, posGraph_neg]

/-- For an odd graph vector `p` (`reflectGraph p = -p`), `reflectGraph (negGraph p) = posGraph p`. -/
theorem reflectGraph_negGraph_of_odd {p : SourceGraph} (hp : reflectGraph p = -p) :
    reflectGraph (negGraph p) = posGraph p := by
  rw [reflectGraph_negGraph, hp, negGraph_neg]

/-- For an odd graph vector `p` (`reflectGraph p = -p`), the even part of `posGraph p` is
`(1 / 2 : ℝ) • absGraph p`. -/
theorem evenGraphPart_posGraph_of_odd {p : SourceGraph} (hp : reflectGraph p = -p) :
    evenGraphPart (posGraph p) = (1 / 2 : ℝ) • absGraph p := by
  unfold evenGraphPart
  rw [reflectGraph_posGraph_of_odd hp, posGraph_add_negGraph]

/-- For an odd graph vector `p` (`reflectGraph p = -p`), the even part of `negGraph p` is
`(1 / 2 : ℝ) • absGraph p`. -/
theorem evenGraphPart_negGraph_of_odd {p : SourceGraph} (hp : reflectGraph p = -p) :
    evenGraphPart (negGraph p) = (1 / 2 : ℝ) • absGraph p := by
  unfold evenGraphPart
  rw [reflectGraph_negGraph_of_odd hp, add_comm, posGraph_add_negGraph]

/-- For an odd graph vector `p` (`reflectGraph p = -p`), the odd part of `posGraph p` is
`(1 / 2 : ℝ) • p`. -/
theorem oddGraphPart_posGraph_of_odd {p : SourceGraph} (hp : reflectGraph p = -p) :
    oddGraphPart (posGraph p) = (1 / 2 : ℝ) • p := by
  unfold oddGraphPart
  rw [reflectGraph_posGraph_of_odd hp, posGraph_sub_negGraph]

/-- For an odd graph vector `p` (`reflectGraph p = -p`), the odd part of `negGraph p` is
`-(1 / 2 : ℝ) • p`. -/
theorem oddGraphPart_negGraph_of_odd {p : SourceGraph} (hp : reflectGraph p = -p) :
    oddGraphPart (negGraph p) = -(1 / 2 : ℝ) • p := by
  unfold oddGraphPart
  rw [reflectGraph_negGraph_of_odd hp, ← neg_sub, posGraph_sub_negGraph, smul_neg, neg_smul]

/-- For an odd graph vector `p` (`reflectGraph p = -p`), `posGraph p` and `negGraph p` have equal
Doob energies: `sourceEnergy (posGraph p) = sourceEnergy (negGraph p)`. -/
theorem sourceEnergy_posGraph_eq_negGraph_of_odd {p : SourceGraph} (hp : reflectGraph p = -p) :
    sourceEnergy (posGraph p) = sourceEnergy (negGraph p) := by
  rw [← reflectGraph_posGraph_of_odd hp, ← sourcePair_self, ← sourcePair_self,
    sourcePair_reflectGraph]

/-- For an odd graph vector `p` (`reflectGraph p = -p`),
`sourceEnergy (posGraph p) = (1 / 4) * sourceEnergy (absGraph p) + (1 / 4) * sourceEnergy p`. -/
theorem sourceEnergy_posGraph_eq_quarter_absGraph_add_self_of_odd {p : SourceGraph}
    (hp : reflectGraph p = -p) :
    sourceEnergy (posGraph p) =
      (1 / 4 : ℝ) * sourceEnergy (absGraph p) + (1 / 4 : ℝ) * sourceEnergy p := by
  have h1 := sourceEnergy_eq_posGraph_add_negGraph_sub_two_sourcePair p
  have h2 := sourceEnergy_absGraph_eq p
  have h3 := sourceEnergy_posGraph_eq_negGraph_of_odd hp
  linarith

/-- For any `p : SourceGraph`,
`sourcePair (posGraph p) (negGraph p) = (1 / 4) * sourceEnergy (absGraph p) - (1 / 4) * sourceEnergy p`. -/
theorem sourcePair_posGraph_negGraph_eq_quarter_absGraph_sub_self (p : SourceGraph) :
    sourcePair (posGraph p) (negGraph p) =
      (1 / 4 : ℝ) * sourceEnergy (absGraph p) - (1 / 4 : ℝ) * sourceEnergy p := by
  have h := sourceEnergy_absGraph_eq p
  linarith

/-- For an even graph vector `p` (`reflectGraph p = p`), both `posGraph p` and `negGraph p` are even. -/
theorem reflectGraph_posGraph_and_negGraph_of_even {p : SourceGraph} (hp : reflectGraph p = p) :
    reflectGraph (posGraph p) = posGraph p ∧
    reflectGraph (negGraph p) = negGraph p ∧
    evenGraphPart (posGraph p) = posGraph p ∧
    oddGraphPart (posGraph p) = 0 := by
  have hpos : reflectGraph (posGraph p) = posGraph p := by rw [reflectGraph_posGraph, hp]
  have hneg : reflectGraph (negGraph p) = negGraph p := by rw [reflectGraph_negGraph, hp]
  refine ⟨hpos, hneg, ?_, ?_⟩
  · unfold evenGraphPart
    rw [hpos]
    module
  · unfold oddGraphPart
    rw [hpos, sub_self, smul_zero]

end RHTower.CHMDPolar
