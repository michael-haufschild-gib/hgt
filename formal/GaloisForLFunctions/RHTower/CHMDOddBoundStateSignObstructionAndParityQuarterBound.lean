import GaloisForLFunctions.RHTower.CHMDOddHarmonicIdentityAndPolarDoobAbsorption
import GaloisForLFunctions.RHTower.CHMDQuarterZeroBound

/-!
# Odd Polar Preimage, Sign Obstruction for Odd Bound States, and Parity Split of the Quarter-Zero Bound

This module establishes three unconditional structural results on the arithmetic resolvent `R` and
its completed Doob graph `SourceGraph`:

1. **Odd Polar Resolvent Preimage and Odd Polar Reduction of the Weil Form**:
   For every graph vector `p : SourceGraph`, its odd polar readout `polarSine p` is the mass inner
   product `⟪p.val.fst, tanhL⟫_ℝ` (`polarSine_eq_inner_tanhL`). Consequently, for every nonzero
   admissible shift `a`, the normalized odd theta shift-difference vector
   `Ψ_a = oddPolarVectorAt a ha` satisfies
   $$\operatorname{sourcePair}(\Psi_a, q) = \langle \text{tanhL}, q.\text{val.fst}\rangle_{\mathbb{R}}
     \qquad \forall q \in \text{SourceGraph}.$$
   By `resolvent_preimage_of_sourcePair`, `(2 : ℝ) • Ψ_a.val.fst + tanhL` is the exact Riesz/resolvent
   preimage of `Ψ_a` (`rieszLift_oddPolarVectorAt_preimage`, `resolvent_oddPolarVectorAt_preimage`),
   giving the shift-independent resolvent identity
   $$\operatorname{resolvent}(\text{tanhL})
     = (\operatorname{oddPolarVectorAt} a \, ha).\text{val.fst}
       - (2 : \mathbb{R}) \bullet \operatorname{resolvent}\bigl((\operatorname{oddPolarVectorAt} a \, ha).\text{val.fst}\bigr)$$
   and placing `Ψ_a` in the exact radical of `weilBilin` (`weilBilin_oddPolarVectorAt`) and
   `(2 : ℝ) • Ψ_a.val.fst + tanhL` in the kernel of `weilOperator`
   (`weilOperator_oddPolarVectorAt_preimage`). Subtracting `(2 * ⟪p.val.fst, tanhL⟫_ℝ) • Ψ_a`
   defines the odd polar reduction `oddPrimitivePart a ha p`, which satisfies
   $$\operatorname{weilForm}(p) = \operatorname{sourceEnergy}(\operatorname{oddPrimitivePart} a \, ha \, p)$$
   for every odd graph vector `p` (`weilForm_eq_sourceEnergy_oddPrimitivePart`), and yields the
   exact `sourcePair`-orthogonal energy decomposition
   $$\operatorname{sourceEnergy}(p)
     = \operatorname{sourceEnergy}(\operatorname{oddPrimitivePart} a \, ha \, p)
       + 2 \langle p.\text{val.fst}, \text{tanhL}\rangle_{\mathbb{R}}^2$$
   (`sourceEnergy_eq_oddPrimitivePart_add_sq`).

2. **Universal Eigenvector Pairing Law and Absence of One-Signed Odd Bound States Above `1/2`**:
   For every `w : MassSpace` and `q : SourceGraph`,
   $$\operatorname{sourcePair}(\operatorname{rieszLift} w, q)
     = \langle w, q.\text{val.fst}\rangle_{\mathbb{R}}
       - 2 \langle \operatorname{resolvent} w, q.\text{val.fst}\rangle_{\mathbb{R}}.$$
   Specializing to `q = Ψ_a = oddPolarVectorAt a ha` for any eigenvector `resolvent w = μ • w` gives
   the universal odd polar eigenvector identity
   $$(2\mu - 1) \langle w, (\operatorname{oddPolarVectorAt} a \, ha).\text{val.fst}\rangle_{\mathbb{R}}
     + \mu \langle w, \text{tanhL}\rangle_{\mathbb{R}} = 0$$
   (`eigenvector_oddPolarVectorAt_pairing`), showing that for `μ ≠ 1/2` the pairing
   `⟪w, Ψ_a.val.fst⟫_ℝ` is independent of `a`, and for `μ > 1/2` every eigenvector `w` of `R` is
   orthogonal in `MassSpace` to the strictly positive odd kernel
   `(2μ - 1) oddPolarFunction a x + μ tanh(x / 2) > 0` on `(0, ∞)`. Consequently, **no nonzero odd
   eigenvector of `R` with eigenvalue `μ > 1/2` can be nonnegative (or nonpositive) almost
   everywhere on `(0, ∞)`** (`eq_zero_of_odd_bound_state_nonneg_ae`,
   `eq_zero_of_odd_bound_state_nonpos_ae`).

3. **Parity Split of `zeroDefect` and Halving of the Quarter-Zero Bound in Each Parity Sector**:
   For an even real test `g`, `zeroDefect g ρ` is purely imaginary (`zeroDefect_ofReal_re_eq_zero_of_even`),
   and for an odd real test `g`, `zeroDefect g ρ` is purely real (`zeroDefect_ofReal_im_eq_zero_of_odd`).
   Projecting compact-test approximants onto the odd or even sector via `1/2 • (q ∓ reflectGraph q)`
   factors the defect map through the real vector space `quarterFinset hfin → ℝ` of real dimension
   `#(quarterZeros)` rather than `quarterFinset hfin → ℂ` of real dimension `2 · #(quarterZeros)`.
   Therefore:
   - every orthonormal family of **odd** bound states of `R` above `1/2` has cardinality at most
     `#(quarterZeros)` (`orthonormal_odd_bound_states_le_quarter`), and
   - every orthonormal family of **even primitive** bound states of `R` above `1/2` has cardinality
     at most `#(quarterZeros)` (`orthonormal_evenPrimitive_bound_states_le_quarter`).
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace BigOperators ComplexConjugate
noncomputable section

namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump

/-! ## Section 1: Odd Polar Resolvent Preimage and Odd Polar Reduction of the Weil Form -/

/-- For every graph vector `p : SourceGraph`, the odd polar readout `polarSine p` is the mass inner
product `⟪p.val.fst, tanhL⟫_ℝ`. -/
theorem polarSine_eq_inner_tanhL (p : SourceGraph) :
    polarSine p = ⟪p.val.fst, tanhL⟫_ℝ := by
  rw [polarSine_eq_integral_sinh, inner_tanhL, integral_mass]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold phiDoobTest massDensity tanhHalf
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos (x / 2)).ne']

theorem sourceMap_apply (p : SourceGraph) : sourceMap p = p.val.fst := rfl

/-- For every nonzero admissible shift `a` and every `q : SourceGraph`, pairing against
`oddPolarVectorAt a ha` in `sourcePair` is the mass inner product with `tanhL`. -/
theorem sourcePair_oddPolarVectorAt_eq_inner_tanhL {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (q : SourceGraph) :
    sourcePair (oddPolarVectorAt a ha) q = ⟪tanhL, q.val.fst⟫_ℝ := by
  rw [sourcePair_oddPolarVectorAt hane ha, polarSine_eq_inner_tanhL, real_inner_comm]

/-- **Exact Riesz Preimage of `oddPolarVectorAt a ha`**:
for every nonzero admissible shift `a`, `rieszLift ((2 : ℝ) • Ψ_a.val.fst + tanhL) = Ψ_a`. -/
theorem rieszLift_oddPolarVectorAt_preimage {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    rieszLift ((2 : ℝ) • (oddPolarVectorAt a ha).val.fst + tanhL) = oddPolarVectorAt a ha := by
  apply rieszLift_unique
  intro q
  have h := sourcePair_oddPolarVectorAt_eq_inner_tanhL hane ha q
  rw [sourcePair_eq_graph_inner, sourceMap_apply, sourceMap_apply] at h
  rw [inner_add_left, real_inner_smul_left]
  linarith

/-- **Exact Resolvent Preimage of `oddPolarVectorAt a ha`**:
`resolvent ((2 : ℝ) • Ψ_a.val.fst + tanhL) = Ψ_a.val.fst`. -/
theorem resolvent_oddPolarVectorAt_preimage {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    resolvent ((2 : ℝ) • (oddPolarVectorAt a ha).val.fst + tanhL) =
      (oddPolarVectorAt a ha).val.fst := by
  rw [resolvent_apply, rieszLift_oddPolarVectorAt_preimage hane ha]

/-- **Shift-Independent Resolvent Identity for `tanhL`**:
for every nonzero admissible shift `a`,
`resolvent tanhL = Ψ_a.val.fst - (2 : ℝ) • resolvent (Ψ_a.val.fst)`. -/
theorem resolvent_tanhL_eq_sub_two_smul_resolvent {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    resolvent tanhL =
      (oddPolarVectorAt a ha).val.fst -
        (2 : ℝ) • resolvent (oddPolarVectorAt a ha).val.fst := by
  have h := resolvent_oddPolarVectorAt_preimage hane ha
  rw [map_add, map_smul] at h
  exact eq_sub_of_add_eq' h

theorem oddPolarVectorAt_fst_mem_arithmetic_domain {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    (oddPolarVectorAt a ha).val.fst ∈ arithmeticGenerator.domain :=
  mem_arithmetic_domain_of_resolvent_preimage (resolvent_oddPolarVectorAt_preimage hane ha)

theorem arithmeticGenerator_oddPolarVectorAt_fst {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    arithmeticGenerator ⟨(oddPolarVectorAt a ha).val.fst,
      oddPolarVectorAt_fst_mem_arithmetic_domain hane ha⟩ =
      (oddPolarVectorAt a ha).val.fst + tanhL :=
  arithmeticGenerator_of_resolvent_preimage (resolvent_oddPolarVectorAt_preimage hane ha)

theorem oddPolarVectorAt_fst_mem_oddSector (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    (oddPolarVectorAt a ha).val.fst ∈ oddSector := by
  rw [mem_oddSector, Lp.ext_iff]
  have h1 := reflectMass_coeFn (oddPolarVectorAt a ha).val.fst
  have h2 := oddPolarVectorAt_source_ae a ha
  have h3 := measurePreserving_neg_mass.quasiMeasurePreserving.ae_eq_comp h2
  have h4 := Lp.coeFn_neg (oddPolarVectorAt a ha).val.fst
  filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4
  simp only [Function.comp_apply] at hx3
  rw [hx1, hx3, oddPolarFunction_neg, hx4, Pi.neg_apply, hx2]

theorem reflectGraph_oddPolarVectorAt (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    reflectGraph (oddPolarVectorAt a ha) = -oddPolarVectorAt a ha :=
  reflectGraph_eq_neg_of_odd (oddPolarVectorAt_fst_mem_oddSector a ha)

theorem inner_oneL_oddPolarVectorAt (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    ⟪(oddPolarVectorAt a ha).val.fst, oneL⟫_ℝ = 0 := by
  have h := reflectMass.inner_map_map (oddPolarVectorAt a ha).val.fst oneL
  rw [mem_oddSector.mp (oddPolarVectorAt_fst_mem_oddSector a ha), reflectMass_oneL,
    inner_neg_left] at h
  linarith

theorem inner_tanhL_oddPolarVectorAt {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    ⟪(oddPolarVectorAt a ha).val.fst, tanhL⟫_ℝ = 1 / 2 := by
  rw [← polarSine_eq_inner_tanhL, polarSine_oddPolarVectorAt hane ha]

/-- **Every normalized odd polar vector `Ψ_a` is null for the Weil bilinear form `weilBilin`**,
parallel to `weilBilin_constantLift_one` for the even ground vector `constantLift 1`. -/
theorem weilBilin_oddPolarVectorAt_left {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (q : SourceGraph) :
    weilBilin (oddPolarVectorAt a ha) q = 0 := by
  unfold weilBilin
  have hpair := sourcePair_oddPolarVectorAt hane ha q
  rw [sourcePair_eq_graph_inner, polarSine_eq_inner_tanhL, sourceMap_apply, sourceMap_apply] at hpair
  rw [inner_oneL_oddPolarVectorAt a ha, inner_tanhL_oddPolarVectorAt hane ha]
  linarith

theorem weilBilin_oddPolarVectorAt_right {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (q : SourceGraph) :
    weilBilin q (oddPolarVectorAt a ha) = 0 := by
  rw [weilBilin_comm, weilBilin_oddPolarVectorAt_left hane ha]

theorem weilForm_oddPolarVectorAt {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    weilForm (oddPolarVectorAt a ha) = 0 := by
  rw [weilForm_eq_weilBilin, weilBilin_oddPolarVectorAt_left hane ha]

/-- The bilinear identity connecting `weilOperator` on `MassSpace` to `weilBilin` on `SourceGraph`. -/
theorem inner_weilOperator_eq_weilBilin_rieszLift (w z : MassSpace) :
    ⟪weilOperator w, z⟫_ℝ = weilBilin (rieszLift w) (rieszLift z) := by
  rw [weilOperator_apply]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
  unfold weilBilin
  rw [← inner_resolventFun, ← resolvent_apply, ← resolvent_apply,
    inner_resolvent_oneL, inner_resolvent_oneL,
    inner_resolvent_tanhL, inner_resolvent_tanhL,
    resolvent_symm (resolvent w) z]
  rfl

/-- **The preimage `(2 : ℝ) • Ψ_a.val.fst + tanhL` lies in the exact kernel of `weilOperator`.** -/
theorem weilOperator_oddPolarVectorAt_preimage {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    weilOperator ((2 : ℝ) • (oddPolarVectorAt a ha).val.fst + tanhL) = 0 := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_weilOperator_eq_weilBilin_rieszLift, rieszLift_oddPolarVectorAt_preimage hane ha,
    weilBilin_oddPolarVectorAt_left hane ha, inner_zero_left]

/-- The odd polar-reduced part of a graph vector at admissible shift `a`: subtract the odd polar
vector `Ψ_a` carrying its `tanhL` moment. -/
def oddPrimitivePart (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) (p : SourceGraph) : SourceGraph :=
  p - (2 * ⟪p.val.fst, tanhL⟫_ℝ) • oddPolarVectorAt a ha

theorem oddPrimitivePart_fst (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) (p : SourceGraph) :
    (oddPrimitivePart a ha p).val.fst =
      p.val.fst - (2 * ⟪p.val.fst, tanhL⟫_ℝ) • (oddPolarVectorAt a ha).val.fst := rfl

theorem inner_oddPrimitivePart_tanhL {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (p : SourceGraph) :
    ⟪(oddPrimitivePart a ha p).val.fst, tanhL⟫_ℝ = 0 := by
  rw [oddPrimitivePart_fst, inner_sub_left, real_inner_smul_left,
    inner_tanhL_oddPolarVectorAt hane ha]
  ring

theorem inner_oddPrimitivePart_oneL (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) (p : SourceGraph) :
    ⟪(oddPrimitivePart a ha p).val.fst, oneL⟫_ℝ = ⟪p.val.fst, oneL⟫_ℝ := by
  rw [oddPrimitivePart_fst, inner_sub_left, real_inner_smul_left,
    inner_oneL_oddPolarVectorAt a ha, mul_zero, sub_zero]

theorem oddPrimitivePart_fst_mem_oddSector (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|))
    {p : SourceGraph} (hp : p.val.fst ∈ oddSector) :
    (oddPrimitivePart a ha p).val.fst ∈ oddSector :=
  oddSector.sub_mem hp (oddSector.smul_mem _ (oddPolarVectorAt_fst_mem_oddSector a ha))

theorem inner_oneL_eq_zero_of_odd {w : MassSpace} (hw : w ∈ oddSector) :
    ⟪w, oneL⟫_ℝ = 0 := by
  have h := reflectMass.inner_map_map w oneL
  rw [mem_oddSector.mp hw, reflectMass_oneL, inner_neg_left] at h
  linarith

/-- **Odd Polar Reduction of the Weil Form**:
for every graph vector `p` with `⟪p.val.fst, oneL⟫_ℝ = 0` (in particular for every `p` with
`p.val.fst ∈ oddSector`), the Weil form of `p` equals the Doob energy `sourceEnergy` of its odd
polar reduction `oddPrimitivePart a ha p`. -/
theorem weilForm_eq_sourceEnergy_oddPrimitivePart {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (p : SourceGraph) (hp : ⟪p.val.fst, oneL⟫_ℝ = 0) :
    weilForm p = sourceEnergy (oddPrimitivePart a ha p) := by
  have h0 : weilForm (oddPrimitivePart a ha p) = weilForm p := by
    rw [weilForm_eq_weilBilin, weilForm_eq_weilBilin]
    unfold oddPrimitivePart
    simp only [weilBilin_sub_left, weilBilin_sub_right, weilBilin_smul_left, weilBilin_smul_right,
      weilBilin_oddPolarVectorAt_left hane ha, weilBilin_oddPolarVectorAt_right hane ha]
    ring
  rw [← h0]
  unfold weilForm
  rw [inner_oddPrimitivePart_oneL a ha p, hp, inner_oddPrimitivePart_tanhL hane ha p]
  ring

/-- **Orthogonal Doob Energy Decomposition Along the Odd Polar Vector**:
because `sourceEnergy (oddPolarVectorAt a ha) = +1/2 > 0`, the Doob energy of any `p : SourceGraph`
splits into the Doob energy of its polar-annihilated part `oddPrimitivePart a ha p` plus the
nonnegative polar square `2 ⟪p.val.fst, tanhL⟫_ℝ ^ 2`. -/
theorem sourceEnergy_eq_oddPrimitivePart_add_sq {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (p : SourceGraph) :
    sourceEnergy p =
      sourceEnergy (oddPrimitivePart a ha p) + 2 * ⟪p.val.fst, tanhL⟫_ℝ ^ 2 := by
  have h1 : weilForm (oddPrimitivePart a ha p) = weilForm p := by
    rw [weilForm_eq_weilBilin, weilForm_eq_weilBilin]
    unfold oddPrimitivePart
    simp only [weilBilin_sub_left, weilBilin_sub_right, weilBilin_smul_left, weilBilin_smul_right,
      weilBilin_oddPolarVectorAt_left hane ha, weilBilin_oddPolarVectorAt_right hane ha]
    ring
  unfold weilForm at h1
  rw [inner_oddPrimitivePart_oneL a ha p, inner_oddPrimitivePart_tanhL hane ha p] at h1
  linarith

/-- On `oddSector`, nonnegativity of `sourceEnergy` is equivalent to nonnegativity of `weilForm`. -/
theorem riemannHypothesis_iff_odd_weilForm_nonneg :
    RiemannHypothesis ↔ ∀ p : SourceGraph, p.val.fst ∈ oddSector → 0 ≤ weilForm p := by
  rw [riemannHypothesis_iff_odd_half_bound]
  constructor
  · intro h p hp
    have hE := energy_nonneg_on_of_half_bound h
      (oddPrimitivePart (CHMDThetaTranslate.shifts 0) (CHMDThetaTranslate.shifts_admissible 0) p)
      (oddPrimitivePart_fst_mem_oddSector _ _ hp)
    rwa [← weilForm_eq_sourceEnergy_oddPrimitivePart
      (CHMDThetaTranslate.shifts_pos 0).ne' (CHMDThetaTranslate.shifts_admissible 0) p
      (inner_oneL_eq_zero_of_odd hp)] at hE
  · intro h
    refine half_bound_on_of_energy resolventInvariant_oddSector fun p hp => ?_
    have hW := h p hp
    unfold weilForm at hW
    rw [inner_oneL_eq_zero_of_odd hp] at hW
    nlinarith [sq_nonneg ⟪p.val.fst, tanhL⟫_ℝ]

/-! ## Section 2: Universal Eigenvector Pairing Law and Absence of One-Signed Odd Bound States Above `1/2` -/

/-- **Universal Riesz–Graph Pairing Identity**:
for every `w : MassSpace` and `q : SourceGraph`,
`sourcePair (rieszLift w) q = ⟪w, q.val.fst⟫_ℝ - 2 * ⟪resolvent w, q.val.fst⟫_ℝ`. -/
theorem sourcePair_rieszLift (w : MassSpace) (q : SourceGraph) :
    sourcePair (rieszLift w) q = ⟪w, q.val.fst⟫_ℝ - 2 * ⟪resolvent w, q.val.fst⟫_ℝ := by
  rw [sourcePair_eq_graph_inner, inner_rieszLift, sourceMap_apply, sourceMap_apply, ← resolvent_apply]

/-- **Universal Eigenvector–Graph Pairing Law**:
if `resolvent w = μ • w`, then for every `q : SourceGraph`,
`sourcePair (rieszLift w) q = (1 - 2 * μ) * ⟪w, q.val.fst⟫_ℝ`. -/
theorem sourcePair_rieszLift_of_eigenvector {μ : ℝ} {w : MassSpace}
    (heig : resolvent w = μ • w) (q : SourceGraph) :
    sourcePair (rieszLift w) q = (1 - 2 * μ) * ⟪w, q.val.fst⟫_ℝ := by
  rw [sourcePair_rieszLift, heig, real_inner_smul_left]
  ring

/-- For every `w : MassSpace` and every nonzero admissible shift `a`,
`⟪w, Ψ_a.val.fst⟫_ℝ - 2 * ⟪resolvent w, Ψ_a.val.fst⟫_ℝ = ⟪resolvent w, tanhL⟫_ℝ`. -/
theorem inner_sub_two_resolvent_oddPolarVectorAt {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (w : MassSpace) :
    ⟪w, (oddPolarVectorAt a ha).val.fst⟫_ℝ -
        2 * ⟪resolvent w, (oddPolarVectorAt a ha).val.fst⟫_ℝ =
      ⟪resolvent w, tanhL⟫_ℝ := by
  rw [← sourcePair_rieszLift, sourcePair_symm,
    sourcePair_oddPolarVectorAt_eq_inner_tanhL hane ha, ← resolvent_apply, real_inner_comm]

/-- **Universal Odd Polar Eigenvector Pairing Law**:
for every eigenvector `resolvent w = μ • w` and every nonzero admissible shift `a`,
`(2 * μ - 1) * ⟪w, (oddPolarVectorAt a ha).val.fst⟫_ℝ + μ * ⟪w, tanhL⟫_ℝ = 0`. -/
theorem eigenvector_oddPolarVectorAt_pairing {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) {μ : ℝ} {w : MassSpace}
    (heig : resolvent w = μ • w) :
    (2 * μ - 1) * ⟪w, (oddPolarVectorAt a ha).val.fst⟫_ℝ + μ * ⟪w, tanhL⟫_ℝ = 0 := by
  have h := inner_sub_two_resolvent_oddPolarVectorAt hane ha w
  rw [heig, real_inner_smul_left, real_inner_smul_left] at h
  linarith

/-- For any eigenvector `resolvent w = μ • w` with `μ ≠ 1/2`, the inner product
`⟪w, (oddPolarVectorAt a ha).val.fst⟫_ℝ` is independent of the nonzero admissible shift `a`. -/
theorem inner_oddPolarVectorAt_eq_of_eigenvector_ne_half {a b : ℝ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (hb : 1 < 2 * Real.exp (-2 * |b|))
    {μ : ℝ} (hμ : μ ≠ 1 / 2) {w : MassSpace} (heig : resolvent w = μ • w) :
    ⟪w, (oddPolarVectorAt a ha).val.fst⟫_ℝ = ⟪w, (oddPolarVectorAt b hb).val.fst⟫_ℝ := by
  have h1 := eigenvector_oddPolarVectorAt_pairing ha0 ha heig
  have h2 := eigenvector_oddPolarVectorAt_pairing hb0 hb heig
  have hsub : (2 * μ - 1) *
      (⟪w, (oddPolarVectorAt a ha).val.fst⟫_ℝ - ⟪w, (oddPolarVectorAt b hb).val.fst⟫_ℝ) = 0 := by
    linarith
  have hne : 2 * μ - 1 ≠ 0 := by
    intro h
    apply hμ
    linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left hne)

/-- The combined odd polar kernel `(2μ - 1) oddPolarFunction a x + μ tanhHalf x`, which is strictly
positive on `(0, ∞)` whenever `μ > 1/2` and `a > 0`. -/
def oddBoundStateKernel (μ a x : ℝ) : ℝ :=
  (2 * μ - 1) * oddPolarFunction a x + μ * tanhHalf x

theorem oddBoundStateKernel_neg (μ a x : ℝ) :
    oddBoundStateKernel μ a (-x) = -oddBoundStateKernel μ a x := by
  unfold oddBoundStateKernel
  rw [oddPolarFunction_neg, tanhHalf_neg]
  ring

theorem oddBoundStateKernel_zero (μ a : ℝ) :
    oddBoundStateKernel μ a 0 = 0 := by
  have h := oddBoundStateKernel_neg μ a 0
  rw [neg_zero] at h
  linarith

theorem oddBoundStateKernel_pos {μ a x : ℝ} (hμ : 1 / 2 < μ) (ha : 0 < a) (hx : 0 < x) :
    0 < oddBoundStateKernel μ a x := by
  unfold oddBoundStateKernel
  have h1 : 0 < (2 * μ - 1) * oddPolarFunction a x :=
    mul_pos (by linarith) (oddPolarFunction_pos ha hx)
  have h2 : 0 < μ * tanhHalf x := by
    unfold tanhHalf
    rw [Real.tanh_eq_sinh_div_cosh]
    exact mul_pos (by linarith) (div_pos (Real.sinh_pos_iff.mpr (half_pos hx)) (Real.cosh_pos _))
  linarith

theorem oddBoundStateKernel_ne_zero {μ a x : ℝ} (hμ : 1 / 2 < μ) (ha : 0 < a) (hx : x ≠ 0) :
    oddBoundStateKernel μ a x ≠ 0 := by
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · have hpos := oddBoundStateKernel_pos hμ ha (neg_pos.mpr hlt)
    rw [oddBoundStateKernel_neg] at hpos
    linarith
  · exact (oddBoundStateKernel_pos hμ ha hgt).ne'

theorem integral_mul_oddBoundStateKernel_eq_zero {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) {μ : ℝ} {w : MassSpace}
    (heig : resolvent w = μ • w) :
    (∫ x, w x * oddBoundStateKernel μ a x ∂massMeasure) = 0 := by
  have h1 : (2 * μ - 1) * ⟪w, (oddPolarVectorAt a ha).val.fst⟫_ℝ + μ * ⟪w, tanhL⟫_ℝ = 0 :=
    eigenvector_oddPolarVectorAt_pairing hane ha heig
  have hψ : ⟪w, (oddPolarVectorAt a ha).val.fst⟫_ℝ =
      ∫ x, w x * oddPolarFunction a x ∂massMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [oddPolarVectorAt_source_ae a ha] with x hx
    change inner ℝ (w x) ((oddPolarVectorAt a ha).val.fst x) = _
    simp [hx, mul_comm]
  have ht : ⟪w, tanhL⟫_ℝ = ∫ x, w x * tanhHalf x ∂massMeasure := inner_tanhL w
  have hint_ψ : Integrable (fun x => w x * oddPolarFunction a x) massMeasure := by
    refine (L2.integrable_inner w (oddPolarVectorAt a ha).val.fst).congr ?_
    filter_upwards [oddPolarVectorAt_source_ae a ha] with x hx
    change inner ℝ (w x) ((oddPolarVectorAt a ha).val.fst x) = _
    simp [hx, mul_comm]
  have hint_t : Integrable (fun x => w x * tanhHalf x) massMeasure := by
    refine (L2.integrable_inner w tanhL).congr ?_
    filter_upwards [memLp_tanhHalf.coeFn_toLp] with x hx
    change inner ℝ (w x) (tanhL x) = _
    unfold tanhL
    simp [hx, mul_comm]
  have hsum : (∫ x, w x * oddBoundStateKernel μ a x ∂massMeasure) =
      (2 * μ - 1) * (∫ x, w x * oddPolarFunction a x ∂massMeasure) +
        μ * (∫ x, w x * tanhHalf x ∂massMeasure) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hint_ψ.const_mul _) (hint_t.const_mul _)]
    apply integral_congr_ae
    filter_upwards [] with x
    unfold oddBoundStateKernel
    ring
  rw [hsum, ← hψ, ← ht, h1]

theorem ae_ne_zero_massMeasure : ∀ᵐ x ∂massMeasure, x ≠ (0 : ℝ) := by
  rw [ae_iff]
  have h : {x : ℝ | ¬x ≠ 0} = {(0 : ℝ)} := by ext x; simp
  rw [h]
  exact withDensity_absolutelyContinuous volume _ (measure_singleton (0 : ℝ))

/-- **No One-Signed Odd Bound State Above `1/2` (Nonnegative Case)**:
no nonzero odd eigenvector of the arithmetic resolvent `R` with eigenvalue `μ > 1/2` can be
nonnegative almost everywhere on `(0, ∞)`. -/
theorem eq_zero_of_odd_bound_state_nonneg_ae {μ : ℝ} (hμ : 1 / 2 < μ) {w : MassSpace}
    (hodd : reflectMass w = -w) (heig : resolvent w = μ • w)
    (hnonneg : ∀ᵐ x ∂massMeasure, 0 < x → 0 ≤ w x) : w = 0 := by
  set a := CHMDThetaTranslate.shifts 0
  have ha0 : 0 < a := CHMDThetaTranslate.shifts_pos 0
  have ha : 1 < 2 * Real.exp (-2 * |a|) := CHMDThetaTranslate.shifts_admissible 0
  have hw_odd : ∀ᵐ x ∂massMeasure, w (-x) = -w x := by
    have h1 := reflectMass_coeFn w
    have h2 : (reflectMass w : ℝ → ℝ) = (-w : MassSpace) := by rw [hodd]
    filter_upwards [h1, Lp.coeFn_neg w] with x hx1 hx2
    rw [← hx1, h2, hx2, Pi.neg_apply]
  have hneg_nonneg : ∀ᵐ x ∂massMeasure, x < 0 → w x ≤ 0 := by
    have hcomp := measurePreserving_neg_mass.quasiMeasurePreserving.ae hnonneg
    filter_upwards [hw_odd, hcomp] with x hxo hxc hxlt
    have hpos : 0 < -x := neg_pos.mpr hxlt
    have hwx : 0 ≤ w (-x) := hxc hpos
    rw [hxo] at hwx
    linarith
  have hprod_nonneg : ∀ᵐ x ∂massMeasure, 0 ≤ w x * oddBoundStateKernel μ a x := by
    filter_upwards [hnonneg, hneg_nonneg] with x hpos hneg
    rcases lt_trichotomy x 0 with hlt | rfl | hgt
    · have hk : oddBoundStateKernel μ a x < 0 := by
        have := oddBoundStateKernel_pos hμ ha0 (neg_pos.mpr hlt)
        rw [oddBoundStateKernel_neg] at this
        linarith
      exact mul_nonneg_of_nonpos_of_nonpos (hneg hlt) hk.le
    · rw [oddBoundStateKernel_zero, mul_zero]
    · exact mul_nonneg (hpos hgt) (oddBoundStateKernel_pos hμ ha0 hgt).le
  have hint : Integrable (fun x => w x * oddBoundStateKernel μ a x) massMeasure := by
    have hint_ψ : Integrable (fun x => w x * oddPolarFunction a x) massMeasure := by
      refine (L2.integrable_inner w (oddPolarVectorAt a ha).val.fst).congr ?_
      filter_upwards [oddPolarVectorAt_source_ae a ha] with x hx
      change inner ℝ (w x) ((oddPolarVectorAt a ha).val.fst x) = _
      simp [hx, mul_comm]
    have hint_t : Integrable (fun x => w x * tanhHalf x) massMeasure := by
      refine (L2.integrable_inner w tanhL).congr ?_
      filter_upwards [memLp_tanhHalf.coeFn_toLp] with x hx
      change inner ℝ (w x) (tanhL x) = _
      unfold tanhL
      simp [hx, mul_comm]
    refine ((hint_ψ.const_mul (2 * μ - 1)).add (hint_t.const_mul μ)).congr ?_
    filter_upwards [] with x
    simp only [Pi.add_apply, oddBoundStateKernel]
    ring
  have hint0 := integral_mul_oddBoundStateKernel_eq_zero ha0.ne' ha heig
  have hae0 : (fun x => w x * oddBoundStateKernel μ a x) =ᵐ[massMeasure] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hprod_nonneg hint).mp hint0
  rw [Lp.ext_iff]
  filter_upwards [hae0, ae_ne_zero_massMeasure, Lp.coeFn_zero ℝ 2 massMeasure] with x hx0 hne hzero
  rw [hzero]
  exact (mul_eq_zero.mp hx0).resolve_right (oddBoundStateKernel_ne_zero hμ ha0 hne)

/-- **No One-Signed Odd Bound State Above `1/2` (Nonpositive Case)**:
no nonzero odd eigenvector of the arithmetic resolvent `R` with eigenvalue `μ > 1/2` can be
nonpositive almost everywhere on `(0, ∞)`. -/
theorem eq_zero_of_odd_bound_state_nonpos_ae {μ : ℝ} (hμ : 1 / 2 < μ) {w : MassSpace}
    (hodd : reflectMass w = -w) (heig : resolvent w = μ • w)
    (hnonpos : ∀ᵐ x ∂massMeasure, 0 < x → w x ≤ 0) : w = 0 := by
  have hneg : -w = 0 := by
    refine eq_zero_of_odd_bound_state_nonneg_ae hμ ?_ ?_ ?_
    · rw [map_neg, hodd]
    · rw [map_neg, heig, smul_neg]
    · filter_upwards [hnonpos, Lp.coeFn_neg w] with x hx hneg_fn hpos
      rw [hneg_fn, Pi.neg_apply]
      linarith [hx hpos]
  exact neg_eq_zero.mp hneg

/-! ## Section 3: Parity Split of `zeroDefect` and Halving of the Quarter-Zero Bound -/

/-- For an even function `g : ℝ → ℂ`, `paperFT g (-z) = paperFT g z`. -/
theorem paperFT_neg_of_even {g : ℝ → ℂ} (heven : ∀ u, g (-u) = g u) (z : ℂ) :
    paperFT g (-z) = paperFT g z := by
  unfold paperFT
  rw [← integral_neg_eq_self _ (volume : Measure ℝ)]
  congr 1
  funext u
  rw [heven u]
  congr 2
  push_cast
  ring

/-- For an odd function `g : ℝ → ℂ`, `paperFT g (-z) = -paperFT g z`. -/
theorem paperFT_neg_of_odd {g : ℝ → ℂ} (hodd : ∀ u, g (-u) = -g u) (z : ℂ) :
    paperFT g (-z) = -paperFT g z := by
  unfold paperFT
  rw [← integral_neg_eq_self _ (volume : Measure ℝ), ← integral_neg]
  congr 1
  funext u
  rw [hodd u]
  have he : Complex.I * (-z) * ((-u : ℝ) : ℂ) = Complex.I * z * (u : ℂ) := by
    push_cast
    ring
  rw [he, neg_mul]

/-- For an even real test `g : ℝ → ℝ`, `paperFT g (conj z) = conj (paperFT g z)`. -/
theorem paperFT_conj_ofReal_of_even {g : ℝ → ℝ} (heven : ∀ u, g (-u) = g u) (z : ℂ) :
    paperFT (fun u => (g u : ℂ)) (conj z) = conj (paperFT (fun u => (g u : ℂ)) z) := by
  rw [conj_paperFT_ofReal, paperFT_neg_of_even (fun u => by simp [heven u])]

/-- For an odd real test `g : ℝ → ℝ`, `paperFT g (conj z) = -conj (paperFT g z)`. -/
theorem paperFT_conj_ofReal_of_odd {g : ℝ → ℝ} (hodd : ∀ u, g (-u) = -g u) (z : ℂ) :
    paperFT (fun u => (g u : ℂ)) (conj z) = -conj (paperFT (fun u => (g u : ℂ)) z) := by
  rw [conj_paperFT_ofReal, paperFT_neg_of_odd (fun u => by simp [hodd u]), neg_neg]

/-- **Parity Law for `zeroDefect` (Even Case)**:
for an even real test `g : ℝ → ℝ`, `zeroDefect g ρ` is purely imaginary (`re = 0`). -/
theorem zeroDefect_ofReal_re_eq_zero_of_even {g : ℝ → ℝ} (heven : ∀ u, g (-u) = g u) (ρ : ℂ) :
    (zeroDefect (fun u => (g u : ℂ)) ρ).re = 0 := by
  unfold zeroDefect
  rw [paperFT_conj_ofReal_of_even heven, Complex.sub_re, Complex.conj_re, sub_self]

/-- **Parity Law for `zeroDefect` (Odd Case)**:
for an odd real test `g : ℝ → ℝ`, `zeroDefect g ρ` is purely real (`im = 0`). -/
theorem zeroDefect_ofReal_im_eq_zero_of_odd {g : ℝ → ℝ} (hodd : ∀ u, g (-u) = -g u) (ρ : ℂ) :
    (zeroDefect (fun u => (g u : ℂ)) ρ).im = 0 := by
  unfold zeroDefect
  rw [paperFT_conj_ofReal_of_odd hodd, sub_neg_eq_add, Complex.add_im, Complex.conj_im,
    add_neg_cancel]

theorem reflectGraph_sub (p q : SourceGraph) :
    reflectGraph (p - q) = reflectGraph p - reflectGraph q :=
  reflectGraphₗᵢ.map_sub p q

/-- Even part of a compact test is an even compact test. -/
theorem evenPart_compactLift (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    (1 / 2 : ℝ) • (compactLift v hv hvc + reflectGraph (compactLift v hv hvc)) =
      compactLift (fun x => (1 / 2) * (v x + v (-x)))
        (contDiff_const.mul (hv.add (hv.comp contDiff_neg)))
        ((hvc.add (hvc.comp_homeomorph (Homeomorph.neg ℝ))).mul_left) := by
  apply source_projection_injective
  show ((1 / 2 : ℝ) • (compactLift v hv hvc + reflectGraph (compactLift v hv hvc))).val.fst =
    (compactLift (fun x => (1 / 2) * (v x + v (-x))) _ _).val.fst
  change (1 / 2 : ℝ) • ((compactLift v hv hvc).val.fst + (reflectGraph (compactLift v hv hvc)).val.fst) = _
  rw [reflectGraph_fst, reflectMass_compactLift_fst, Lp.ext_iff]
  have h1 := Lp.coeFn_smul (1 / 2 : ℝ) ((compactLift v hv hvc).val.fst +
    (compactLift (fun x => v (-x)) (hv.comp contDiff_neg) (hvc.comp_homeomorph (Homeomorph.neg ℝ))).val.fst)
  have h2 := Lp.coeFn_add (compactLift v hv hvc).val.fst
    (compactLift (fun x => v (-x)) (hv.comp contDiff_neg) (hvc.comp_homeomorph (Homeomorph.neg ℝ))).val.fst
  have h3 := compactLift_source_ae v hv hvc
  have h4 := compactLift_source_ae (fun x => v (-x)) (hv.comp contDiff_neg)
    (hvc.comp_homeomorph (Homeomorph.neg ℝ))
  have h5 := compactLift_source_ae (fun x => (1 / 2) * (v x + v (-x)))
    (contDiff_const.mul (hv.add (hv.comp contDiff_neg)))
    ((hvc.add (hvc.comp_homeomorph (Homeomorph.neg ℝ))).mul_left)
  filter_upwards [h1, h2, h3, h4, h5] with x hx1 hx2 hx3 hx4 hx5
  rw [hx1, Pi.smul_apply, hx2, Pi.add_apply, hx3, hx4, hx5, smul_eq_mul]

/-- A graph vector with even source is fixed by the graph reflection. -/
theorem reflectGraph_eq_self_of_even {p : SourceGraph} (hp : reflectMass p.val.fst = p.val.fst) :
    reflectGraph p = p := by
  apply source_projection_injective
  show (reflectGraph p).val.fst = p.val.fst
  rw [reflectGraph_fst, hp]

/-- **Odd Quarter-Strip Birman–Schwinger Count**:
a negative-definite family of `k` odd compact tests for the Weil form satisfies
`k ≤ #(quarterZeros)` (half the `2 · #(quarterZeros)` bound for general real tests). -/
theorem card_le_quarter_of_odd_negative_definite (hfin : offLineZeros.Finite) {k : ℕ}
    (v : Fin k → ℝ → ℝ) (hv : ∀ i, ContDiff ℝ 2 (v i)) (hvc : ∀ i, HasCompactSupport (v i))
    (hodd : ∀ i x, v i (-x) = -v i x)
    (hneg : ∀ c : Fin k → ℝ, c ≠ 0 →
      weilForm (∑ i, c i • compactLift (v i) (hv i) (hvc i)) < 0) :
    k ≤ quarterZeros.ncard := by
  classical
  let q : Fin k → SourceGraph := fun i => compactLift (v i) (hv i) (hvc i)
  have hq : ∀ i, q i ∈ compactTests := fun i => ⟨v i, hv i, hvc i, rfl⟩
  set T := quarterFinset hfin
  let a : Fin k → T → ℝ := fun i ρ =>
    (zeroDefect (fun x => (phiDoobTest (v i) x : ℂ)) (ρ : ℂ)).re
  let L : (Fin k → ℝ) →ₗ[ℝ] (T → ℝ) :=
    { toFun := fun c ρ => ∑ i, c i * a i ρ
      map_add' := fun c d => by
        funext ρ
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        funext ρ
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    by_contra hc0
    have hmem : (∑ i, c i • q i) ∈ compactTests :=
      Submodule.sum_mem _ fun i _ => compactTests.smul_mem _ (hq i)
    obtain ⟨w, hw, hwc, hqw⟩ := hmem
    have hW := weilForm_compactLift w hw hwc
    rw [← hqw] at hW
    have h2 : (compactLift w hw hwc).val.fst = ∑ i, c i • (q i).val.fst := by
      rw [← hqw]
      show sourceMap (∑ i, c i • q i) = ∑ i, c i • sourceMap (q i)
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
    have h1 : ((compactLift w hw hwc).val.fst : ℝ → ℝ) =ᵐ[massMeasure] w :=
      compactLift_source_ae w hw hwc
    rw [h2] at h1
    have h3 := Lp_coeFn_sum_smul Finset.univ c fun i => (q i).val.fst
    have h4 : ∀ i, ((q i).val.fst : ℝ → ℝ) =ᵐ[massMeasure] v i := fun i =>
      compactLift_source_ae _ _ _
    have h4' : ∀ᵐ x ∂massMeasure, ∀ i, (q i).val.fst x = v i x := ae_all_iff.mpr h4
    have h5 : w =ᵐ[massMeasure] fun x => ∑ i, c i * v i x := by
      filter_upwards [h1, h3, h4'] with x hx1 hx3 hx4
      rw [← hx1, hx3]
      exact Finset.sum_congr rfl fun i _ => by rw [hx4 i]
    have h6 := volume_absolutelyContinuous_mass.ae_eq h5
    have hae : (fun x => (phiDoobTest w x : ℂ)) =ᵐ[volume]
        fun x => ∑ i, (c i : ℂ) * (phiDoobTest (v i) x : ℂ) := by
      filter_upwards [h6] with x hx
      simp only [phiDoobTest, hx]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hFT : ∀ z, paperFT (fun x => (phiDoobTest w x : ℂ)) z =
        ∑ i, (c i : ℂ) * paperFT (fun x => (phiDoobTest (v i) x : ℂ)) z := by
      intro z
      rw [← paperFT_sum_mul c (fun i x => (phiDoobTest (v i) x : ℂ))
        (fun i => (contDiff_phiDoobTest_ofReal (hv i)).continuous)
        (fun i => hasCompactSupport_phiDoobTest_ofReal (hvc i)) z]
      simp only [paperFT_def]
      exact integral_congr_ae (hae.mul (ae_eq_refl _))
    have hdef_sum : ∀ ρ : ℂ, zeroDefect (fun x => (phiDoobTest w x : ℂ)) ρ =
        ∑ i, (c i : ℂ) * zeroDefect (fun x => (phiDoobTest (v i) x : ℂ)) ρ := by
      intro ρ
      unfold zeroDefect
      rw [hFT, hFT, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hdef_im : ∀ i (ρ : ℂ),
        (zeroDefect (fun x => (phiDoobTest (v i) x : ℂ)) ρ).im = 0 := by
      intro i ρ
      apply zeroDefect_ofReal_im_eq_zero_of_odd
      intro u
      unfold phiDoobTest
      rw [WeilExcess.riemannKernelReal_neg, hodd i u]
      ring
    have hdefq : ∀ ρ ∈ quarterZeros, zeroDefect (fun x => (phiDoobTest w x : ℂ)) ρ = 0 := by
      intro ρ hρ
      have hρT : ρ ∈ T := (mem_quarterFinset hfin).mpr hρ
      have hL : L c ⟨ρ, hρT⟩ = 0 := by rw [hc]; rfl
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, a] at hL
      rw [hdef_sum]
      apply Complex.ext
      · simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, Complex.zero_re]
        exact hL
      · simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          hdef_im, mul_zero, zero_mul, add_zero, Finset.sum_const_zero, Complex.zero_im]
    have hdef : ∀ ρ ∈ offLineFinset hfin, zeroDefect (fun x => (phiDoobTest w x : ℂ)) ρ = 0 := by
      intro ρ hρ
      rw [mem_offLineFinset] at hρ
      exact zeroDefect_ofReal_eq_zero_of_quarter (phiDoobTest w) hdefq ⟨ρ.2, hρ⟩
    have hbound := re_W_add_defect_nonneg hfin (contDiff_phiDoobTest_ofReal hw)
      (hasCompactSupport_phiDoobTest_ofReal hwc)
    have hzero : ∑ ρ ∈ offLineFinset hfin, defectWeight (fun x => (phiDoobTest w x : ℂ)) ρ = 0 :=
      Finset.sum_eq_zero fun ρ hρ => by
        unfold defectWeight
        rw [hdef ρ hρ, norm_zero]
        ring
    rw [hzero, add_zero] at hbound
    have hneg' := hneg c hc0
    linarith
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fin_fun, Module.finrank_pi, Fintype.card_coe, card_quarterFinset] at h
  exact h

/-- **Even Quarter-Strip Birman–Schwinger Count**:
a negative-definite family of `k` even compact tests for the Weil form satisfies
`k ≤ #(quarterZeros)`. -/
theorem card_le_quarter_of_even_negative_definite (hfin : offLineZeros.Finite) {k : ℕ}
    (v : Fin k → ℝ → ℝ) (hv : ∀ i, ContDiff ℝ 2 (v i)) (hvc : ∀ i, HasCompactSupport (v i))
    (heven : ∀ i x, v i (-x) = v i x)
    (hneg : ∀ c : Fin k → ℝ, c ≠ 0 →
      weilForm (∑ i, c i • compactLift (v i) (hv i) (hvc i)) < 0) :
    k ≤ quarterZeros.ncard := by
  classical
  let q : Fin k → SourceGraph := fun i => compactLift (v i) (hv i) (hvc i)
  have hq : ∀ i, q i ∈ compactTests := fun i => ⟨v i, hv i, hvc i, rfl⟩
  set T := quarterFinset hfin
  let a : Fin k → T → ℝ := fun i ρ =>
    (zeroDefect (fun x => (phiDoobTest (v i) x : ℂ)) (ρ : ℂ)).im
  let L : (Fin k → ℝ) →ₗ[ℝ] (T → ℝ) :=
    { toFun := fun c ρ => ∑ i, c i * a i ρ
      map_add' := fun c d => by
        funext ρ
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        funext ρ
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    by_contra hc0
    have hmem : (∑ i, c i • q i) ∈ compactTests :=
      Submodule.sum_mem _ fun i _ => compactTests.smul_mem _ (hq i)
    obtain ⟨w, hw, hwc, hqw⟩ := hmem
    have hW := weilForm_compactLift w hw hwc
    rw [← hqw] at hW
    have h2 : (compactLift w hw hwc).val.fst = ∑ i, c i • (q i).val.fst := by
      rw [← hqw]
      show sourceMap (∑ i, c i • q i) = ∑ i, c i • sourceMap (q i)
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
    have h1 : ((compactLift w hw hwc).val.fst : ℝ → ℝ) =ᵐ[massMeasure] w :=
      compactLift_source_ae w hw hwc
    rw [h2] at h1
    have h3 := Lp_coeFn_sum_smul Finset.univ c fun i => (q i).val.fst
    have h4 : ∀ i, ((q i).val.fst : ℝ → ℝ) =ᵐ[massMeasure] v i := fun i =>
      compactLift_source_ae _ _ _
    have h4' : ∀ᵐ x ∂massMeasure, ∀ i, (q i).val.fst x = v i x := ae_all_iff.mpr h4
    have h5 : w =ᵐ[massMeasure] fun x => ∑ i, c i * v i x := by
      filter_upwards [h1, h3, h4'] with x hx1 hx3 hx4
      rw [← hx1, hx3]
      exact Finset.sum_congr rfl fun i _ => by rw [hx4 i]
    have h6 := volume_absolutelyContinuous_mass.ae_eq h5
    have hae : (fun x => (phiDoobTest w x : ℂ)) =ᵐ[volume]
        fun x => ∑ i, (c i : ℂ) * (phiDoobTest (v i) x : ℂ) := by
      filter_upwards [h6] with x hx
      simp only [phiDoobTest, hx]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hFT : ∀ z, paperFT (fun x => (phiDoobTest w x : ℂ)) z =
        ∑ i, (c i : ℂ) * paperFT (fun x => (phiDoobTest (v i) x : ℂ)) z := by
      intro z
      rw [← paperFT_sum_mul c (fun i x => (phiDoobTest (v i) x : ℂ))
        (fun i => (contDiff_phiDoobTest_ofReal (hv i)).continuous)
        (fun i => hasCompactSupport_phiDoobTest_ofReal (hvc i)) z]
      simp only [paperFT_def]
      exact integral_congr_ae (hae.mul (ae_eq_refl _))
    have hdef_sum : ∀ ρ : ℂ, zeroDefect (fun x => (phiDoobTest w x : ℂ)) ρ =
        ∑ i, (c i : ℂ) * zeroDefect (fun x => (phiDoobTest (v i) x : ℂ)) ρ := by
      intro ρ
      unfold zeroDefect
      rw [hFT, hFT, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hdef_re : ∀ i (ρ : ℂ),
        (zeroDefect (fun x => (phiDoobTest (v i) x : ℂ)) ρ).re = 0 := by
      intro i ρ
      apply zeroDefect_ofReal_re_eq_zero_of_even
      intro u
      unfold phiDoobTest
      rw [WeilExcess.riemannKernelReal_neg, heven i u]
    have hdefq : ∀ ρ ∈ quarterZeros, zeroDefect (fun x => (phiDoobTest w x : ℂ)) ρ = 0 := by
      intro ρ hρ
      have hρT : ρ ∈ T := (mem_quarterFinset hfin).mpr hρ
      have hL : L c ⟨ρ, hρT⟩ = 0 := by rw [hc]; rfl
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, a] at hL
      rw [hdef_sum]
      apply Complex.ext
      · simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          hdef_re, mul_zero, zero_mul, sub_zero, Finset.sum_const_zero, Complex.zero_re]
      · simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, add_zero, Complex.zero_im]
        exact hL
    have hdef : ∀ ρ ∈ offLineFinset hfin, zeroDefect (fun x => (phiDoobTest w x : ℂ)) ρ = 0 := by
      intro ρ hρ
      rw [mem_offLineFinset] at hρ
      exact zeroDefect_ofReal_eq_zero_of_quarter (phiDoobTest w) hdefq ⟨ρ.2, hρ⟩
    have hbound := re_W_add_defect_nonneg hfin (contDiff_phiDoobTest_ofReal hw)
      (hasCompactSupport_phiDoobTest_ofReal hwc)
    have hzero : ∑ ρ ∈ offLineFinset hfin, defectWeight (fun x => (phiDoobTest w x : ℂ)) ρ = 0 :=
      Finset.sum_eq_zero fun ρ hρ => by
        unfold defectWeight
        rw [hdef ρ hρ, norm_zero]
        ring
    rw [hzero, add_zero] at hbound
    have hneg' := hneg c hc0
    linarith
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fin_fun, Module.finrank_pi, Fintype.card_coe, card_quarterFinset] at h
  exact h

/-- Perturbing odd graph vectors `p_i` (`reflectGraph (p_i) = -p_i`) on whose span `weilForm` is
negative definite yields odd compact tests on whose span `weilForm` remains negative definite. -/
theorem exists_odd_compactTests_negative_definite {k : ℕ} (p : Fin k → SourceGraph)
    (hpodd : ∀ i, reflectGraph (p i) = -p i) {δ : ℝ} (hδ : 0 < δ)
    (hneg : ∀ c : Fin k → ℝ, weilForm (∑ i, c i • p i) ≤ -δ * ∑ i, c i ^ 2) :
    ∃ (v : Fin k → ℝ → ℝ) (hv : ∀ i, ContDiff ℝ 2 (v i)) (hvc : ∀ i, HasCompactSupport (v i)),
      (∀ i x, v i (-x) = -v i x) ∧
      ∀ c : Fin k → ℝ, c ≠ 0 →
        weilForm (∑ i, c i • compactLift (v i) (hv i) (hvc i)) < 0 := by
  have hC := weilBilinConst_pos
  set C := weilBilinConst
  set P : ℝ := ∑ i, ‖p i‖ with hP
  set X : ℝ := C * (2 * P + 1) * ((k : ℝ) + 1) with hX
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hX0 : 0 < X := by positivity
  set η : ℝ := min 1 (δ / (2 * X))
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηδ : X * η ≤ δ / 2 := by
    have h := min_le_right 1 (δ / (2 * X))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have happ : ∀ i, ∃ (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v),
      (∀ x, v (-x) = -v x) ∧ ‖compactLift v hv hvc - p i‖ < η := by
    intro i
    obtain ⟨q₀, ⟨v₀, hv₀, hvc₀, rfl⟩, hd⟩ := dense_compactTests.exists_dist_lt (p i) hη0
    rw [dist_comm, dist_eq_norm] at hd
    refine ⟨fun x => (1 / 2) * (v₀ x - v₀ (-x)),
      contDiff_const.mul (hv₀.sub (hv₀.comp contDiff_neg)),
      (hvc₀.sub (hvc₀.comp_homeomorph (Homeomorph.neg ℝ))).mul_left,
      fun x => by simp only [neg_neg]; ring, ?_⟩
    rw [← oddPart_compactLift v₀ hv₀ hvc₀]
    have hsplit : (1 / 2 : ℝ) • (compactLift v₀ hv₀ hvc₀ - reflectGraph (compactLift v₀ hv₀ hvc₀)) - p i =
        (1 / 2 : ℝ) • ((compactLift v₀ hv₀ hvc₀ - p i) - reflectGraph (compactLift v₀ hv₀ hvc₀ - p i)) := by
      rw [reflectGraph_sub, hpodd i]
      module
    rw [hsplit, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have htri : ‖(compactLift v₀ hv₀ hvc₀ - p i) - reflectGraph (compactLift v₀ hv₀ hvc₀ - p i)‖ ≤
        2 * ‖compactLift v₀ hv₀ hvc₀ - p i‖ := by
      calc ‖(compactLift v₀ hv₀ hvc₀ - p i) - reflectGraph (compactLift v₀ hv₀ hvc₀ - p i)‖
          ≤ ‖compactLift v₀ hv₀ hvc₀ - p i‖ + ‖reflectGraph (compactLift v₀ hv₀ hvc₀ - p i)‖ :=
            norm_sub_le _ _
        _ = 2 * ‖compactLift v₀ hv₀ hvc₀ - p i‖ := by rw [norm_reflectGraph]; ring
    linarith
  choose v hv hvc hodd hqd using happ
  refine ⟨v, hv, hvc, hodd, fun c hc => ?_⟩
  let q : Fin k → SourceGraph := fun i => compactLift (v i) (hv i) (hvc i)
  set S : ℝ := ∑ i, |c i| with hS
  have hx : ‖∑ i, c i • p i‖ ≤ P * S := by
    calc ‖∑ i, c i • p i‖ ≤ ∑ i, ‖c i • p i‖ := norm_sum_le _ _
      _ = ∑ i, |c i| * ‖p i‖ := by simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ i, |c i| * P := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (fun j _ => norm_nonneg (p j)) (Finset.mem_univ i)) (abs_nonneg _)
      _ = P * S := by rw [hS, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hxy : ‖∑ i, c i • p i - ∑ i, c i • q i‖ ≤ η * S := by
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ i, (c i • p i - c i • q i)‖ ≤ ∑ i, ‖c i • p i - c i • q i‖ := norm_sum_le _ _
      _ = ∑ i, |c i| * ‖p i - q i‖ := by simp only [← smul_sub, norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ i, |c i| * η := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (by rw [norm_sub_rev]; exact (hqd i).le) (abs_nonneg _)
      _ = η * S := by rw [hS, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hy : ‖∑ i, c i • q i‖ ≤ (P + η) * S := by
    have h := norm_sub_norm_le (∑ i, c i • q i) (∑ i, c i • p i)
    rw [norm_sub_rev] at h
    nlinarith
  have hS2 : S ^ 2 ≤ k * ∑ i, c i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |c i|)
    simpa [sq_abs, Finset.card_univ, Fintype.card_fin] using h
  have hsumpos : 0 < ∑ i, c i ^ 2 := sum_sq_pos_of_ne_zero hc
  have hdiff := abs_weilForm_sub_le (∑ i, c i • q i) (∑ i, c i • p i)
  rw [norm_sub_rev] at hdiff
  have hub : weilForm (∑ i, c i • q i) ≤ weilForm (∑ i, c i • p i) +
      C * ((‖∑ i, c i • q i‖ + ‖∑ i, c i • p i‖) * ‖∑ i, c i • p i - ∑ i, c i • q i‖) := by
    have := (abs_le.mp hdiff).2
    linarith
  have hcorr : C * ((‖∑ i, c i • q i‖ + ‖∑ i, c i • p i‖) * ‖∑ i, c i • p i - ∑ i, c i • q i‖) ≤
      X * η * ∑ i, c i ^ 2 := by
    have h1 : (‖∑ i, c i • q i‖ + ‖∑ i, c i • p i‖) * ‖∑ i, c i • p i - ∑ i, c i • q i‖ ≤
        ((P + η) * S + P * S) * (η * S) :=
      mul_le_mul (add_le_add hy hx) hxy (norm_nonneg _) (by positivity)
    have h2 : ((P + η) * S + P * S) * (η * S) = (2 * P + η) * η * S ^ 2 := by ring
    have h3 : (2 * P + η) * η * S ^ 2 ≤ (2 * P + 1) * η * (k * ∑ i, c i ^ 2) := by
      have h : (2 * P + η) * η ≤ (2 * P + 1) * η := by nlinarith
      calc (2 * P + η) * η * S ^ 2 ≤ (2 * P + 1) * η * S ^ 2 :=
            mul_le_mul_of_nonneg_right h (sq_nonneg _)
        _ ≤ (2 * P + 1) * η * (k * ∑ i, c i ^ 2) :=
            mul_le_mul_of_nonneg_left hS2 (by positivity)
    have h4 : (2 * P + 1) * η * (k * ∑ i, c i ^ 2) ≤ (2 * P + 1) * ((k : ℝ) + 1) * η * ∑ i, c i ^ 2 := by
      have h5 : (0 : ℝ) ≤ (2 * P + 1) * η * ∑ i, c i ^ 2 := by positivity
      nlinarith
    calc C * ((‖∑ i, c i • q i‖ + ‖∑ i, c i • p i‖) * ‖∑ i, c i • p i - ∑ i, c i • q i‖)
        ≤ C * ((2 * P + 1) * ((k : ℝ) + 1) * η * ∑ i, c i ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith [h1, h2, h3, h4]) hC.le
      _ = X * η * ∑ i, c i ^ 2 := by rw [hX]; ring
  have hfinal : X * η * ∑ i, c i ^ 2 ≤ δ / 2 * ∑ i, c i ^ 2 :=
    mul_le_mul_of_nonneg_right hηδ hsumpos.le
  have hneg' := hneg c
  calc weilForm (∑ i, c i • q i) ≤ -δ * ∑ i, c i ^ 2 + δ / 2 * ∑ i, c i ^ 2 := by linarith
    _ = -(δ / 2) * ∑ i, c i ^ 2 := by ring
    _ < 0 := by nlinarith

/-- Perturbing even graph vectors `p_i` (`reflectGraph (p_i) = p_i`) on whose span `weilForm` is
negative definite yields even compact tests on whose span `weilForm` remains negative definite. -/
theorem exists_even_compactTests_negative_definite {k : ℕ} (p : Fin k → SourceGraph)
    (hpeven : ∀ i, reflectGraph (p i) = p i) {δ : ℝ} (hδ : 0 < δ)
    (hneg : ∀ c : Fin k → ℝ, weilForm (∑ i, c i • p i) ≤ -δ * ∑ i, c i ^ 2) :
    ∃ (v : Fin k → ℝ → ℝ) (hv : ∀ i, ContDiff ℝ 2 (v i)) (hvc : ∀ i, HasCompactSupport (v i)),
      (∀ i x, v i (-x) = v i x) ∧
      ∀ c : Fin k → ℝ, c ≠ 0 →
        weilForm (∑ i, c i • compactLift (v i) (hv i) (hvc i)) < 0 := by
  have hC := weilBilinConst_pos
  set C := weilBilinConst
  set P : ℝ := ∑ i, ‖p i‖ with hP
  set X : ℝ := C * (2 * P + 1) * ((k : ℝ) + 1) with hX
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hX0 : 0 < X := by positivity
  set η : ℝ := min 1 (δ / (2 * X))
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηδ : X * η ≤ δ / 2 := by
    have h := min_le_right 1 (δ / (2 * X))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have happ : ∀ i, ∃ (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v),
      (∀ x, v (-x) = v x) ∧ ‖compactLift v hv hvc - p i‖ < η := by
    intro i
    obtain ⟨q₀, ⟨v₀, hv₀, hvc₀, rfl⟩, hd⟩ := dense_compactTests.exists_dist_lt (p i) hη0
    rw [dist_comm, dist_eq_norm] at hd
    refine ⟨fun x => (1 / 2) * (v₀ x + v₀ (-x)),
      contDiff_const.mul (hv₀.add (hv₀.comp contDiff_neg)),
      (hvc₀.add (hvc₀.comp_homeomorph (Homeomorph.neg ℝ))).mul_left,
      fun x => by simp only [neg_neg]; ring, ?_⟩
    rw [← evenPart_compactLift v₀ hv₀ hvc₀]
    have hsplit : (1 / 2 : ℝ) • (compactLift v₀ hv₀ hvc₀ + reflectGraph (compactLift v₀ hv₀ hvc₀)) - p i =
        (1 / 2 : ℝ) • ((compactLift v₀ hv₀ hvc₀ - p i) + reflectGraph (compactLift v₀ hv₀ hvc₀ - p i)) := by
      rw [reflectGraph_sub, hpeven i]
      module
    rw [hsplit, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have htri : ‖(compactLift v₀ hv₀ hvc₀ - p i) + reflectGraph (compactLift v₀ hv₀ hvc₀ - p i)‖ ≤
        2 * ‖compactLift v₀ hv₀ hvc₀ - p i‖ := by
      calc ‖(compactLift v₀ hv₀ hvc₀ - p i) + reflectGraph (compactLift v₀ hv₀ hvc₀ - p i)‖
          ≤ ‖compactLift v₀ hv₀ hvc₀ - p i‖ + ‖reflectGraph (compactLift v₀ hv₀ hvc₀ - p i)‖ :=
            norm_add_le _ _
        _ = 2 * ‖compactLift v₀ hv₀ hvc₀ - p i‖ := by rw [norm_reflectGraph]; ring
    linarith
  choose v hv hvc heven hqd using happ
  refine ⟨v, hv, hvc, heven, fun c hc => ?_⟩
  let q : Fin k → SourceGraph := fun i => compactLift (v i) (hv i) (hvc i)
  set S : ℝ := ∑ i, |c i| with hS
  have hx : ‖∑ i, c i • p i‖ ≤ P * S := by
    calc ‖∑ i, c i • p i‖ ≤ ∑ i, ‖c i • p i‖ := norm_sum_le _ _
      _ = ∑ i, |c i| * ‖p i‖ := by simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ i, |c i| * P := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (fun j _ => norm_nonneg (p j)) (Finset.mem_univ i)) (abs_nonneg _)
      _ = P * S := by rw [hS, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hxy : ‖∑ i, c i • p i - ∑ i, c i • q i‖ ≤ η * S := by
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ i, (c i • p i - c i • q i)‖ ≤ ∑ i, ‖c i • p i - c i • q i‖ := norm_sum_le _ _
      _ = ∑ i, |c i| * ‖p i - q i‖ := by simp only [← smul_sub, norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ i, |c i| * η := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (by rw [norm_sub_rev]; exact (hqd i).le) (abs_nonneg _)
      _ = η * S := by rw [hS, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hy : ‖∑ i, c i • q i‖ ≤ (P + η) * S := by
    have h := norm_sub_norm_le (∑ i, c i • q i) (∑ i, c i • p i)
    rw [norm_sub_rev] at h
    nlinarith
  have hS2 : S ^ 2 ≤ k * ∑ i, c i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |c i|)
    simpa [sq_abs, Finset.card_univ, Fintype.card_fin] using h
  have hsumpos : 0 < ∑ i, c i ^ 2 := sum_sq_pos_of_ne_zero hc
  have hdiff := abs_weilForm_sub_le (∑ i, c i • q i) (∑ i, c i • p i)
  rw [norm_sub_rev] at hdiff
  have hub : weilForm (∑ i, c i • q i) ≤ weilForm (∑ i, c i • p i) +
      C * ((‖∑ i, c i • q i‖ + ‖∑ i, c i • p i‖) * ‖∑ i, c i • p i - ∑ i, c i • q i‖) := by
    have := (abs_le.mp hdiff).2
    linarith
  have hcorr : C * ((‖∑ i, c i • q i‖ + ‖∑ i, c i • p i‖) * ‖∑ i, c i • p i - ∑ i, c i • q i‖) ≤
      X * η * ∑ i, c i ^ 2 := by
    have h1 : (‖∑ i, c i • q i‖ + ‖∑ i, c i • p i‖) * ‖∑ i, c i • p i - ∑ i, c i • q i‖ ≤
        ((P + η) * S + P * S) * (η * S) :=
      mul_le_mul (add_le_add hy hx) hxy (norm_nonneg _) (by positivity)
    have h2 : ((P + η) * S + P * S) * (η * S) = (2 * P + η) * η * S ^ 2 := by ring
    have h3 : (2 * P + η) * η * S ^ 2 ≤ (2 * P + 1) * η * (k * ∑ i, c i ^ 2) := by
      have h : (2 * P + η) * η ≤ (2 * P + 1) * η := by nlinarith
      calc (2 * P + η) * η * S ^ 2 ≤ (2 * P + 1) * η * S ^ 2 :=
            mul_le_mul_of_nonneg_right h (sq_nonneg _)
        _ ≤ (2 * P + 1) * η * (k * ∑ i, c i ^ 2) :=
            mul_le_mul_of_nonneg_left hS2 (by positivity)
    have h4 : (2 * P + 1) * η * (k * ∑ i, c i ^ 2) ≤ (2 * P + 1) * ((k : ℝ) + 1) * η * ∑ i, c i ^ 2 := by
      have h5 : (0 : ℝ) ≤ (2 * P + 1) * η * ∑ i, c i ^ 2 := by positivity
      nlinarith
    calc C * ((‖∑ i, c i • q i‖ + ‖∑ i, c i • p i‖) * ‖∑ i, c i • p i - ∑ i, c i • q i‖)
        ≤ C * ((2 * P + 1) * ((k : ℝ) + 1) * η * ∑ i, c i ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith [h1, h2, h3, h4]) hC.le
      _ = X * η * ∑ i, c i ^ 2 := by rw [hX]; ring
  have hfinal : X * η * ∑ i, c i ^ 2 ≤ δ / 2 * ∑ i, c i ^ 2 :=
    mul_le_mul_of_nonneg_right hηδ hsumpos.le
  have hneg' := hneg c
  calc weilForm (∑ i, c i • q i) ≤ -δ * ∑ i, c i ^ 2 + δ / 2 * ∑ i, c i ^ 2 := by linarith
    _ = -(δ / 2) * ∑ i, c i ^ 2 := by ring
    _ < 0 := by nlinarith

/-- **Odd Bound-State Quarter-Zero Count**:
if only finitely many nontrivial zeros lie off the critical line, every orthonormal family of
**odd** eigenvectors of the arithmetic resolvent with eigenvalues above `1/2` has at most
`#(quarterZeros)` members. -/
theorem orthonormal_odd_bound_states_le_quarter (hfin : offLineZeros.Finite) {k : ℕ}
    {e : Fin k → MassSpace} (he : Orthonormal ℝ e) {μ : Fin k → ℝ} (hμ : ∀ i, 1 / 2 < μ i)
    (hodd : ∀ i, reflectMass (e i) = -e i) (heig : ∀ i, resolvent (e i) = μ i • e i) :
    k ≤ quarterZeros.ncard := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · omega
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => μ i * (2 * μ i - 1))
    Finset.univ_nonempty
  have hδ : 0 < μ i₀ * (2 * μ i₀ - 1) := mul_pos (by linarith [hμ i₀]) (by linarith [hμ i₀])
  have hprim : ∀ i, ⟪e i, oneL⟫_ℝ = 0 := fun i => inner_oneL_eq_zero_of_odd (mem_oddSector.mpr (hodd i))
  have hneg := weilForm_rieszLift_sum_le he hprim heig (fun i => hi₀ i (Finset.mem_univ i))
  have hpodd : ∀ i, reflectGraph (rieszLift (e i)) = -rieszLift (e i) := fun i => by
    rw [← rieszLift_reflectMass, hodd i, ← neg_one_smul ℝ (e i), rieszLift_smul, neg_one_smul]
  obtain ⟨v, hv, hvc, hoddv, hqneg⟩ :=
    exists_odd_compactTests_negative_definite (fun i => rieszLift (e i)) hpodd hδ hneg
  exact card_le_quarter_of_odd_negative_definite hfin v hv hvc hoddv hqneg

/-- **Even Primitive Bound-State Quarter-Zero Count**:
if only finitely many nontrivial zeros lie off the critical line, every orthonormal family of
**even primitive** eigenvectors of the arithmetic resolvent with eigenvalues above `1/2` has at most
`#(quarterZeros)` members. -/
theorem orthonormal_evenPrimitive_bound_states_le_quarter (hfin : offLineZeros.Finite) {k : ℕ}
    {e : Fin k → MassSpace} (he : Orthonormal ℝ e) {μ : Fin k → ℝ} (hμ : ∀ i, 1 / 2 < μ i)
    (heven : ∀ i, reflectMass (e i) = e i) (hprim : ∀ i, ⟪e i, oneL⟫_ℝ = 0)
    (heig : ∀ i, resolvent (e i) = μ i • e i) :
    k ≤ quarterZeros.ncard := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · omega
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => μ i * (2 * μ i - 1))
    Finset.univ_nonempty
  have hδ : 0 < μ i₀ * (2 * μ i₀ - 1) := mul_pos (by linarith [hμ i₀]) (by linarith [hμ i₀])
  have hneg := weilForm_rieszLift_sum_le he hprim heig (fun i => hi₀ i (Finset.mem_univ i))
  have hpeven : ∀ i, reflectGraph (rieszLift (e i)) = rieszLift (e i) := fun i => by
    rw [← rieszLift_reflectMass, heven i]
  obtain ⟨v, hv, hvc, hevenv, hqneg⟩ :=
    exists_even_compactTests_negative_definite (fun i => rieszLift (e i)) hpeven hδ hneg
  exact card_le_quarter_of_even_negative_definite hfin v hv hvc hevenv hqneg

end RHTower.CHMDPolar
