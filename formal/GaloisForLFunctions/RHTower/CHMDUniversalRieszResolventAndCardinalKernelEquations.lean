import GaloisForLFunctions.RHTower.CHMDSpectralBesselAndPrimitiveContractionNodalBounds

/-!
# Universal Riesz–Resolvent Dictionary, Threshold Radical Identification, and Cardinal Kernel Equations

This module establishes the universal Riesz–resolvent dictionary on `SourceGraph` and applies it to
the `signedRadical`, the odd polar ground family `oddPolarVectorAt`, the shifted-theta family
`CHMDThetaTranslate.lift`, and the divisor-cardinal frames `CardinalGraphFrame`:

1. **Universal Riesz–Resolvent Dictionary on `SourceGraph`**:
   For any $q \in \mathrm{SourceGraph}$ and $v \in \mathrm{MassSpace}$,
   $$\bigl(\forall p \in \mathrm{SourceGraph},\; \operatorname{sourcePair}(p, q) = \langle p.\mathrm{val}.\mathrm{fst}, v\rangle_{\mathbb{R}}\bigr)
     \iff q = \operatorname{rieszLift}(v + 2 \cdot q.\mathrm{val}.\mathrm{fst})
     \iff q.\mathrm{val}.\mathrm{fst} - 2 \cdot \operatorname{resolvent}(q.\mathrm{val}.\mathrm{fst}) = \operatorname{resolvent}(v).$$
   Moreover, whenever this holds:
   - $\langle p.\mathrm{val}.\mathrm{snd}, q.\mathrm{val}.\mathrm{snd}\rangle_{\mathbb{R}} = \langle p.\mathrm{val}.\mathrm{fst}, v + q.\mathrm{val}.\mathrm{fst}\rangle_{\mathbb{R}}$ for all $p \in \mathrm{SourceGraph}$,
   - $\operatorname{sourceEnergy}(\operatorname{posGraph} q) = \langle (\operatorname{posGraph} q).\mathrm{val}.\mathrm{fst}, v\rangle_{\mathbb{R}} + \operatorname{sourcePair}(\operatorname{posGraph} q, \operatorname{negGraph} q)$,
   - $\operatorname{sourceEnergy}(\operatorname{negGraph} q) = -\langle (\operatorname{negGraph} q).\mathrm{val}.\mathrm{fst}, v\rangle_{\mathbb{R}} + \operatorname{sourcePair}(\operatorname{posGraph} q, \operatorname{negGraph} q)$,
   - $\operatorname{sourceEnergy}(\operatorname{absGraph} q) = \langle q.\mathrm{val}.\mathrm{fst}, v\rangle_{\mathbb{R}} + 4\,\operatorname{sourcePair}(\operatorname{posGraph} q, \operatorname{negGraph} q)$.

2. **Exact Identification of `signedRadical` with the Threshold Eigenspace $\ker(\operatorname{resolvent} - \frac{1}{2} I)$ and Explicit Threshold Eigenvectors**:
   - $r \in \mathrm{signedRadical} \iff r = \operatorname{rieszLift}(2 \cdot r.\mathrm{val}.\mathrm{fst}) \iff \operatorname{resolvent}(r.\mathrm{val}.\mathrm{fst}) = \frac{1}{2} \cdot r.\mathrm{val}.\mathrm{fst}$.
   - For every nonzero admissible shift $a$,
     $\operatorname{oddPolarVectorAt} a\,ha = \operatorname{rieszLift}(\operatorname{tanhL} + 2 \cdot (\operatorname{oddPolarVectorAt} a\,ha).\mathrm{val}.\mathrm{fst})$,
     and $(\operatorname{oddPolarVectorAt} a\,ha).\mathrm{val}.\mathrm{fst} - 2 \cdot \operatorname{resolvent}((\operatorname{oddPolarVectorAt} a\,ha).\mathrm{val}.\mathrm{fst}) = \operatorname{resolvent}(\operatorname{tanhL})$
     (independent of $a$).
   - Consequently, for any two nonzero admissible shifts $a, b$,
     $\operatorname{oddPolarVectorAt} a\,ha - \operatorname{oddPolarVectorAt} b\,hb \in \mathrm{signedRadical}$,
     and its source is an odd eigenvector of `resolvent` at $\mu = 1/2$.
   - For every admissible shift $a$, the symmetrized shifted-theta vector minus its ground projection
     $\operatorname{lift} a\,ha + \operatorname{lift}(-a)\,ha_- - (2\cosh(a/2)) \cdot \operatorname{constantLift} 1$
     lies in `signedRadical`, and its source is an even primitive eigenvector of `resolvent` at $\mu = 1/2$.

3. **Exact Cardinal Riesz–Resolvent Equations and Cross-Orbit Spectral Identity**:
   Defining the explicit $L^2(\mathrm{massMeasure})$ cosine kernel vectors
   $\operatorname{cosineKernelReL}(z), \operatorname{cosineKernelImL}(z) \in \mathrm{MassSpace}$,
   for every $a \in \mathbb{C}$ with $0 < \operatorname{Re}(a)$ and $\Xi(a) = 0$ and every
   $F : \mathrm{CardinalGraphFrame}\,a$:
   - $F.\mathrm{reVector} = \operatorname{rieszLift}(\operatorname{cardinalOrbitMass}(a) \cdot \operatorname{cosineKernelReL}(a) + 2 \cdot F.\mathrm{reVector}.\mathrm{val}.\mathrm{fst})$,
   - $F.\mathrm{imVector} = \operatorname{rieszLift}(\operatorname{cardinalOrbitMass}(a) \cdot \operatorname{cosineKernelImL}(a) + 2 \cdot F.\mathrm{imVector}.\mathrm{val}.\mathrm{fst})$,
   - $(I - 2\,\operatorname{resolvent})(F.\mathrm{reVector}.\mathrm{val}.\mathrm{fst}) = \operatorname{cardinalOrbitMass}(a) \cdot \operatorname{resolvent}(\operatorname{cosineKernelReL}(a))$,
   - $(I - 2\,\operatorname{resolvent})(F.\mathrm{imVector}.\mathrm{val}.\mathrm{fst}) = \operatorname{cardinalOrbitMass}(a) \cdot \operatorname{resolvent}(\operatorname{cosineKernelImL}(a))$,
   together with the cross-orbit spectral identity `cardinal_im_cross_orbit_spectral_eq` and the
   positive-mode spectral identity `cardinal_re_spectral_eq`.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace BigOperators ComplexConjugate
noncomputable section

namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump CHMDTranslation ThetaSourceWard

/-! ## Section 1: Universal Riesz–Resolvent Dictionary on `SourceGraph` -/

/-- If `sourcePair p q = ⟪p.val.fst, v⟫_ℝ` for all `p : SourceGraph`, then
`q = rieszLift (v + 2 • q.val.fst)`. -/
theorem eq_rieszLift_of_sourcePair_eq_inner {q : SourceGraph} {v : MassSpace}
    (h : ∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ) :
    q = rieszLift (v + (2 : ℝ) • q.val.fst) := by
  symm
  apply rieszLift_unique
  intro p
  have hp := h p
  rw [sourcePair_eq_graph_inner] at hp
  change ⟪p, q⟫_ℝ - 2 * ⟪p.val.fst, q.val.fst⟫_ℝ = ⟪p.val.fst, v⟫_ℝ at hp
  have hcomm : ⟪q, p⟫_ℝ = ⟪p, q⟫_ℝ := real_inner_comm p q
  have hinner : ⟪v + (2 : ℝ) • q.val.fst, p.val.fst⟫_ℝ =
      ⟪p.val.fst, v⟫_ℝ + 2 * ⟪p.val.fst, q.val.fst⟫_ℝ := by
    rw [inner_add_left, real_inner_smul_left, real_inner_comm v p.val.fst,
      real_inner_comm q.val.fst p.val.fst]
  linarith

/-- Conversely, if `q = rieszLift (v + 2 • q.val.fst)`, then
`sourcePair p q = ⟪p.val.fst, v⟫_ℝ` for all `p : SourceGraph`. -/
theorem sourcePair_eq_inner_of_eq_rieszLift {q : SourceGraph} {v : MassSpace}
    (hq : q = rieszLift (v + (2 : ℝ) • q.val.fst)) (p : SourceGraph) :
    sourcePair p q = ⟪p.val.fst, v⟫_ℝ := by
  rw [sourcePair_eq_graph_inner]
  change ⟪p, q⟫_ℝ - 2 * ⟪p.val.fst, q.val.fst⟫_ℝ = ⟪p.val.fst, v⟫_ℝ
  have h1 : ⟪p, q⟫_ℝ = ⟪v + (2 : ℝ) • q.val.fst, p.val.fst⟫_ℝ := by
    conv_lhs => rw [hq]
    rw [real_inner_comm _ p, inner_rieszLift]
  rw [h1, inner_add_left, real_inner_smul_left, real_inner_comm p.val.fst v,
    real_inner_comm p.val.fst q.val.fst]
  ring

/-- **Universal Riesz-Lift Equivalence on `SourceGraph`**:
`(∀ p, sourcePair p q = ⟪p.val.fst, v⟫_ℝ) ↔ q = rieszLift (v + 2 • q.val.fst)`. -/
theorem sourcePair_eq_inner_iff_rieszLift {q : SourceGraph} {v : MassSpace} :
    (∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ) ↔
      q = rieszLift (v + (2 : ℝ) • q.val.fst) :=
  ⟨eq_rieszLift_of_sourcePair_eq_inner, sourcePair_eq_inner_of_eq_rieszLift⟩

/-- **Universal Resolvent Equation Equivalence on `SourceGraph`**:
`(∀ p, sourcePair p q = ⟪p.val.fst, v⟫_ℝ) ↔ q.val.fst - (2 : ℝ) • resolvent q.val.fst = resolvent v`. -/
theorem sourcePair_eq_inner_iff_resolvent {q : SourceGraph} {v : MassSpace} :
    (∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ) ↔
      q.val.fst - (2 : ℝ) • resolvent q.val.fst = resolvent v := by
  rw [sourcePair_eq_inner_iff_rieszLift]
  constructor
  · intro hq
    have hfst : q.val.fst = (rieszLift (v + (2 : ℝ) • q.val.fst)).val.fst :=
      congrArg (fun x : SourceGraph => x.val.fst) hq
    change q.val.fst = resolvent (v + (2 : ℝ) • q.val.fst) at hfst
    rw [map_add, map_smul] at hfst
    rw [sub_eq_iff_eq_add]
    exact hfst
  · intro hres
    apply source_projection_injective
    change q.val.fst = resolvent (v + (2 : ℝ) • q.val.fst)
    rw [map_add, map_smul]
    exact sub_eq_iff_eq_add.mp hres

/-- When `sourcePair p q = ⟪p.val.fst, v⟫_ℝ` for all `p`, the edge inner product against `q.val.snd`
is given by the mass inner product against `v + q.val.fst`. -/
theorem inner_snd_eq_inner_fst_add_of_sourcePair_eq_inner {q : SourceGraph} {v : MassSpace}
    (h : ∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ) (p : SourceGraph) :
    ⟪p.val.snd, q.val.snd⟫_ℝ = ⟪p.val.fst, v + q.val.fst⟫_ℝ := by
  have hp := h p
  change ⟪p.val.snd, q.val.snd⟫_ℝ - ⟪p.val.fst, q.val.fst⟫_ℝ = ⟪p.val.fst, v⟫_ℝ at hp
  rw [inner_add_right]
  linarith

/-- Exact nodal energy of `posGraph q` when `sourcePair (·) q = ⟪(·).val.fst, v⟫_ℝ`. -/
theorem sourceEnergy_posGraph_of_sourcePair_eq_inner {q : SourceGraph} {v : MassSpace}
    (h : ∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ) :
    sourceEnergy (posGraph q) =
      ⟪(posGraph q).val.fst, v⟫_ℝ + sourcePair (posGraph q) (negGraph q) := by
  have hp := h (posGraph q)
  have hsub : sourcePair (posGraph q) q =
      sourceEnergy (posGraph q) - sourcePair (posGraph q) (negGraph q) := by
    have h1 := congrArg (fun x : SourceGraph => sourcePair (posGraph q) x) (posGraph_sub_negGraph q).symm
    change sourcePair (posGraph q) q = sourcePair (posGraph q) (posGraph q - negGraph q) at h1
    rw [h1, sourcePair_sub_right, sourcePair_self]
  linarith

/-- Exact nodal energy of `negGraph q` when `sourcePair (·) q = ⟪(·).val.fst, v⟫_ℝ`. -/
theorem sourceEnergy_negGraph_of_sourcePair_eq_inner {q : SourceGraph} {v : MassSpace}
    (h : ∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ) :
    sourceEnergy (negGraph q) =
      -⟪(negGraph q).val.fst, v⟫_ℝ + sourcePair (posGraph q) (negGraph q) := by
  have hn := h (negGraph q)
  have hsub : sourcePair (negGraph q) q =
      sourcePair (posGraph q) (negGraph q) - sourceEnergy (negGraph q) := by
    have h1 := congrArg (fun x : SourceGraph => sourcePair (negGraph q) x) (posGraph_sub_negGraph q).symm
    change sourcePair (negGraph q) q = sourcePair (negGraph q) (posGraph q - negGraph q) at h1
    rw [h1, sourcePair_sub_right, sourcePair_self, sourcePair_symm (negGraph q) (posGraph q)]
  linarith

/-- Exact nodal energy of `absGraph q` when `sourcePair (·) q = ⟪(·).val.fst, v⟫_ℝ`. -/
theorem sourceEnergy_absGraph_of_sourcePair_eq_inner {q : SourceGraph} {v : MassSpace}
    (h : ∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ) :
    sourceEnergy (absGraph q) =
      ⟪q.val.fst, v⟫_ℝ + 4 * sourcePair (posGraph q) (negGraph q) := by
  rw [sourceEnergy_absGraph_eq, ← sourcePair_self, h q]

/-! ## Section 2: Exact Identification of `signedRadical` with the Threshold Eigenspace $\ker(\operatorname{resolvent} - \frac{1}{2} I)$ -/

/-- **Riesz-Lift Characterization of `signedRadical`**:
`r ∈ signedRadical ↔ r = rieszLift ((2 : ℝ) • r.val.fst)`. -/
theorem mem_signedRadical_iff_eq_rieszLift {r : SourceGraph} :
    r ∈ signedRadical ↔ r = rieszLift ((2 : ℝ) • r.val.fst) := by
  have h0 : r ∈ signedRadical ↔ ∀ p : SourceGraph, sourcePair p r = ⟪p.val.fst, (0 : MassSpace)⟫_ℝ := by
    constructor
    · intro hr p
      rw [sourcePair_symm, hr p, inner_zero_right]
    · intro hr p
      have hp := hr p
      rw [sourcePair_symm, inner_zero_right] at hp
      exact hp
  rw [h0, sourcePair_eq_inner_iff_rieszLift, zero_add]

/-- **Spectral Characterization of `signedRadical`**:
`r ∈ signedRadical ↔ resolvent r.val.fst = (1 / 2 : ℝ) • r.val.fst`. -/
theorem mem_signedRadical_iff_resolvent_eq_half {r : SourceGraph} :
    r ∈ signedRadical ↔ resolvent r.val.fst = (1 / 2 : ℝ) • r.val.fst := by
  rw [mem_signedRadical_iff_eq_rieszLift]
  constructor
  · intro hr
    have hfst : r.val.fst = (rieszLift ((2 : ℝ) • r.val.fst)).val.fst :=
      congrArg (fun x : SourceGraph => x.val.fst) hr
    change r.val.fst = resolvent ((2 : ℝ) • r.val.fst) at hfst
    rw [map_smul] at hfst
    have h2 : (1 / 2 : ℝ) • r.val.fst = (1 / 2 : ℝ) • ((2 : ℝ) • resolvent r.val.fst) :=
      congrArg ((1 / 2 : ℝ) • ·) hfst
    rw [smul_smul] at h2
    norm_num at h2
    exact h2.symm
  · intro hres
    apply source_projection_injective
    change r.val.fst = resolvent ((2 : ℝ) • r.val.fst)
    rw [map_smul, hres, smul_smul]
    norm_num

/-- Conversely, every threshold eigenvector `resolvent w = (1/2) • w` lifts via `rieszLift (2 • w)`
to an element of `signedRadical` with source `w`. -/
theorem rieszLift_two_smul_mem_signedRadical_of_resolvent_eq_half {w : MassSpace}
    (heig : resolvent w = (1 / 2 : ℝ) • w) :
    rieszLift ((2 : ℝ) • w) ∈ signedRadical ∧ (rieszLift ((2 : ℝ) • w)).val.fst = w := by
  have hfst : (rieszLift ((2 : ℝ) • w)).val.fst = w := by
    change resolvent ((2 : ℝ) • w) = w
    rw [map_smul, heig, smul_smul]
    norm_num
  refine ⟨?_, hfst⟩
  rw [mem_signedRadical_iff_eq_rieszLift, hfst]

/-- For every `r ∈ signedRadical`, the positive and negative parts have equal Doob energy
`sourcePair (posGraph r) (negGraph r) ≤ 0`, and `sourceEnergy (absGraph r) = 4 * sourcePair (posGraph r) (negGraph r)`. -/
theorem sourceEnergy_posGraph_and_negGraph_of_mem_signedRadical {r : SourceGraph}
    (hr : r ∈ signedRadical) :
    sourceEnergy (posGraph r) = sourcePair (posGraph r) (negGraph r) ∧
      sourceEnergy (negGraph r) = sourcePair (posGraph r) (negGraph r) ∧
      sourceEnergy (absGraph r) = 4 * sourcePair (posGraph r) (negGraph r) := by
  have h0 : ∀ p : SourceGraph, sourcePair p r = ⟪p.val.fst, (0 : MassSpace)⟫_ℝ := by
    intro p
    rw [sourcePair_symm, hr p, inner_zero_right]
  refine ⟨?_, ?_, ?_⟩
  · rw [sourceEnergy_posGraph_of_sourcePair_eq_inner h0, inner_zero_right, zero_add]
  · rw [sourceEnergy_negGraph_of_sourcePair_eq_inner h0, inner_zero_right, neg_zero, zero_add]
  · rw [sourceEnergy_absGraph_of_sourcePair_eq_inner h0, inner_zero_right, zero_add]

/-- **Exact Riesz-Lift Formula for `oddPolarVectorAt a ha`**:
for every nonzero admissible shift `a`,
`oddPolarVectorAt a ha = rieszLift (tanhL + 2 • (oddPolarVectorAt a ha).val.fst)`. -/
theorem oddPolarVectorAt_eq_rieszLift {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    oddPolarVectorAt a ha =
      rieszLift (tanhL + (2 : ℝ) • (oddPolarVectorAt a ha).val.fst) := by
  apply eq_rieszLift_of_sourcePair_eq_inner
  intro p
  rw [sourcePair_symm, sourcePair_oddPolarVectorAt_eq_inner_tanhL hane ha, real_inner_comm]

/-- **Shift-Invariant Resolvent Equation for `oddPolarVectorAt a ha`**:
for every nonzero admissible shift `a`,
`(oddPolarVectorAt a ha).val.fst - 2 • resolvent (oddPolarVectorAt a ha).val.fst = resolvent tanhL`. -/
theorem resolvent_oddPolarVectorAt_fst {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    (oddPolarVectorAt a ha).val.fst -
        (2 : ℝ) • resolvent (oddPolarVectorAt a ha).val.fst =
      resolvent tanhL := by
  rw [← sourcePair_eq_inner_iff_resolvent]
  intro p
  rw [sourcePair_symm, sourcePair_oddPolarVectorAt_eq_inner_tanhL hane ha, real_inner_comm]

/-- **Explicit Odd Threshold Eigenvectors from Shift Differences of `oddPolarVectorAt`**:
for any two nonzero admissible shifts `a, b`, the difference
`oddPolarVectorAt a ha - oddPolarVectorAt b hb` lies in `signedRadical` and its `.val.fst` is an
odd eigenvector of `resolvent` with eigenvalue `1/2`. -/
theorem oddPolarVectorAt_sub_mem_signedRadical_and_resolvent_eq_half {a b : ℝ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (hb : 1 < 2 * Real.exp (-2 * |b|)) :
    oddPolarVectorAt a ha - oddPolarVectorAt b hb ∈ signedRadical ∧
      resolvent ((oddPolarVectorAt a ha - oddPolarVectorAt b hb).val.fst) =
        (1 / 2 : ℝ) • (oddPolarVectorAt a ha - oddPolarVectorAt b hb).val.fst := by
  have hrad : oddPolarVectorAt a ha - oddPolarVectorAt b hb ∈ signedRadical := by
    intro p
    rw [sourcePair_sub_left, sourcePair_oddPolarVectorAt_eq_inner_tanhL ha0 ha,
      sourcePair_oddPolarVectorAt_eq_inner_tanhL hb0 hb, sub_self]
  exact ⟨hrad, mem_signedRadical_iff_resolvent_eq_half.mp hrad⟩

/-- **Exact Riesz-Lift Formula for `CHMDThetaTranslate.lift a ha`**:
for every admissible shift `a`,
`lift a ha = rieszLift (-cosh(a/2) • oneL + sinh(a/2) • tanhL + 2 • (lift a ha).val.fst)`. -/
theorem thetaTranslate_eq_rieszLift (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    CHMDThetaTranslate.lift a ha =
      rieszLift (-Real.cosh (a / 2) • oneL + Real.sinh (a / 2) • tanhL +
        (2 : ℝ) • (CHMDThetaTranslate.lift a ha).val.fst) := by
  apply eq_rieszLift_of_sourcePair_eq_inner
  intro p
  rw [sourcePair_symm, sourcePair_thetaTranslate a ha p, inner_add_right,
    real_inner_smul_right, real_inner_smul_right]

/-- **Exact Resolvent Equation for `CHMDThetaTranslate.lift a ha`**:
for every admissible shift `a`,
`(lift a ha).val.fst - 2 • resolvent (lift a ha).val.fst = -cosh(a/2) • oneL + sinh(a/2) • resolvent tanhL`. -/
theorem resolvent_thetaTranslate_fst (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    (CHMDThetaTranslate.lift a ha).val.fst -
        (2 : ℝ) • resolvent (CHMDThetaTranslate.lift a ha).val.fst =
      -Real.cosh (a / 2) • oneL + Real.sinh (a / 2) • resolvent tanhL := by
  have h1 : ∀ p : SourceGraph,
      sourcePair p (CHMDThetaTranslate.lift a ha) =
        ⟪p.val.fst, -Real.cosh (a / 2) • oneL + Real.sinh (a / 2) • tanhL⟫_ℝ := by
    intro p
    rw [sourcePair_symm, sourcePair_thetaTranslate a ha p, inner_add_right,
      real_inner_smul_right, real_inner_smul_right]
  have h2 := sourcePair_eq_inner_iff_resolvent.mp h1
  rw [map_add, map_smul, map_smul, resolvent_oneL] at h2
  exact h2

/-- **Explicit Even Primitive Threshold Eigenvectors from Symmetrized Theta Translates**:
for every admissible shift `a`, the graph vector
`lift a ha + lift (-a) (neg_admissible ha) - (2 * cosh(a / 2)) • constantLift 1`
lies in `signedRadical`, and its `.val.fst` is an eigenvector of `resolvent` at `1/2`. -/
theorem symmThetaTranslate_sub_constantLift_mem_signedRadical (a : ℝ)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    CHMDThetaTranslate.lift a ha +
        CHMDThetaTranslate.lift (-a) (CHMDThetaTranslate.neg_admissible ha) -
        (2 * Real.cosh (a / 2)) • constantLift 1 ∈ signedRadical ∧
      resolvent ((CHMDThetaTranslate.lift a ha +
          CHMDThetaTranslate.lift (-a) (CHMDThetaTranslate.neg_admissible ha) -
          (2 * Real.cosh (a / 2)) • constantLift 1).val.fst) =
        (1 / 2 : ℝ) • (CHMDThetaTranslate.lift a ha +
          CHMDThetaTranslate.lift (-a) (CHMDThetaTranslate.neg_admissible ha) -
          (2 * Real.cosh (a / 2)) • constantLift 1).val.fst := by
  have hrad : CHMDThetaTranslate.lift a ha +
      CHMDThetaTranslate.lift (-a) (CHMDThetaTranslate.neg_admissible ha) -
      (2 * Real.cosh (a / 2)) • constantLift 1 ∈ signedRadical := by
    intro p
    have hsinh : Real.sinh (-a / 2) = -Real.sinh (a / 2) := by
      rw [show -a / 2 = -(a / 2) by ring, Real.sinh_neg]
    have hcosh : Real.cosh (-a / 2) = Real.cosh (a / 2) := by
      rw [show -a / 2 = -(a / 2) by ring, Real.cosh_neg]
    have hconst : sourcePair (constantLift 1) p = -⟪p.val.fst, oneL⟫_ℝ := by
      rw [sourcePair_ground, constantLift_fst_eq_smul_oneL, one_smul,
        real_inner_comm]
    rw [sourcePair_sub_left, sourcePair_add_left, sourcePair_smul_left,
      sourcePair_thetaTranslate a ha p,
      sourcePair_thetaTranslate (-a) (CHMDThetaTranslate.neg_admissible ha) p,
      hsinh, hcosh, hconst]
    ring
  exact ⟨hrad, mem_signedRadical_iff_resolvent_eq_half.mp hrad⟩

/-! ## Section 3: Explicit $L^2$ Cosine Kernel Vectors and Cardinal Riesz–Resolvent Equations -/

/-- The real part of the cosine kernel `cos(z x) / cosh(x / 2)` as an element of `MassSpace`. -/
def cosineKernelReL (z : ℂ) : MassSpace :=
  (cosineKernel_memLp z).re.toLp (fun x => (cosineKernel z x).re)

/-- The imaginary part of the cosine kernel `cos(z x) / cosh(x / 2)` as an element of `MassSpace`. -/
def cosineKernelImL (z : ℂ) : MassSpace :=
  (cosineKernel_memLp z).im.toLp (fun x => (cosineKernel z x).im)

theorem graphCosineReadout_re_eq_inner (p : SourceGraph) (z : ℂ) :
    (graphCosineReadout p z).re = ⟪p.val.fst, cosineKernelReL z⟫_ℝ := by
  unfold graphCosineReadout cosineKernelReL
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, Complex.ofReal_im, sub_zero, add_zero]
  exact real_inner_comm p.val.fst _

theorem graphCosineReadout_im_eq_inner (p : SourceGraph) (z : ℂ) :
    (graphCosineReadout p z).im = ⟪p.val.fst, cosineKernelImL z⟫_ℝ := by
  unfold graphCosineReadout cosineKernelImL
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, zero_mul, one_mul, zero_add]
  exact real_inner_comm p.val.fst _

/-- **Exact Riesz-Lift Equation for `F.reVector`**:
for every `a : ℂ` with `0 < a.re` and `XiC a = 0` and every `F : CardinalGraphFrame a`,
`F.reVector = rieszLift (cardinalOrbitMass a • cosineKernelReL a + 2 • F.reVector.val.fst)`. -/
theorem reVector_eq_rieszLift {a : ℂ} (F : CardinalGraphFrame a) (ha : 0 < a.re) (hz : XiC a = 0) :
    F.reVector =
      rieszLift (cardinalOrbitMass a • cosineKernelReL a + (2 : ℝ) • F.reVector.val.fst) := by
  apply eq_rieszLift_of_sourcePair_eq_inner
  intro p
  rw [F.pair_re ha hz p, graphCosineReadout_re_eq_inner, real_inner_smul_right]

/-- **Exact Riesz-Lift Equation for `F.imVector`**:
for every `a : ℂ` with `0 < a.re` and `XiC a = 0` and every `F : CardinalGraphFrame a`,
`F.imVector = rieszLift (cardinalOrbitMass a • cosineKernelImL a + 2 • F.imVector.val.fst)`. -/
theorem imVector_eq_rieszLift {a : ℂ} (F : CardinalGraphFrame a) (ha : 0 < a.re) (hz : XiC a = 0) :
    F.imVector =
      rieszLift (cardinalOrbitMass a • cosineKernelImL a + (2 : ℝ) • F.imVector.val.fst) := by
  apply eq_rieszLift_of_sourcePair_eq_inner
  intro p
  rw [F.pair_im ha hz p, graphCosineReadout_im_eq_inner, real_inner_smul_right]

/-- **Exact Resolvent Equation for `F.reVector.val.fst`**:
for every `a : ℂ` with `0 < a.re` and `XiC a = 0` and every `F : CardinalGraphFrame a`,
`F.reVector.val.fst - 2 • resolvent F.reVector.val.fst = cardinalOrbitMass a • resolvent (cosineKernelReL a)`. -/
theorem resolvent_reVector_fst {a : ℂ} (F : CardinalGraphFrame a) (ha : 0 < a.re) (hz : XiC a = 0) :
    F.reVector.val.fst - (2 : ℝ) • resolvent F.reVector.val.fst =
      cardinalOrbitMass a • resolvent (cosineKernelReL a) := by
  have h1 : ∀ p : SourceGraph,
      sourcePair p F.reVector = ⟪p.val.fst, cardinalOrbitMass a • cosineKernelReL a⟫_ℝ := by
    intro p
    rw [F.pair_re ha hz p, graphCosineReadout_re_eq_inner, real_inner_smul_right]
  have h2 := sourcePair_eq_inner_iff_resolvent.mp h1
  rwa [map_smul] at h2

/-- **Exact Resolvent Equation for `F.imVector.val.fst`**:
for every `a : ℂ` with `0 < a.re` and `XiC a = 0` and every `F : CardinalGraphFrame a`,
`F.imVector.val.fst - 2 • resolvent F.imVector.val.fst = cardinalOrbitMass a • resolvent (cosineKernelImL a)`. -/
theorem resolvent_imVector_fst {a : ℂ} (F : CardinalGraphFrame a) (ha : 0 < a.re) (hz : XiC a = 0) :
    F.imVector.val.fst - (2 : ℝ) • resolvent F.imVector.val.fst =
      cardinalOrbitMass a • resolvent (cosineKernelImL a) := by
  have h1 : ∀ p : SourceGraph,
      sourcePair p F.imVector = ⟪p.val.fst, cardinalOrbitMass a • cosineKernelImL a⟫_ℝ := by
    intro p
    rw [F.pair_im ha hz p, graphCosineReadout_im_eq_inner, real_inner_smul_right]
  have h2 := sourcePair_eq_inner_iff_resolvent.mp h1
  rwa [map_smul] at h2

/-- **Positive-Mode Cardinal Spectral Identity at Any $\Xi$-Zero**:
for any `a : ℂ` with `0 < a.re` and `XiC a = 0`, any `F : CardinalGraphFrame a`, and
any orthonormal family of eigenvectors `resolvent (w i) = μ i • w i` with `μ i ≠ 0` and
`μ i ≠ 1 / 2`,
`cardinalPositiveMass a + cardinalOrbitMass a ^ 2 * ∑ i, (μ i / (2 * μ i - 1)) * (massCosineReadout (w i) a).re ^ 2 = sourceEnergy (eigenGraphRem μ w F.reVector)`. -/
theorem cardinal_re_spectral_eq {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0)
    {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ0 : ∀ i, μ i ≠ 0) (hμhalf : ∀ i, μ i ≠ 1 / 2)
    (hw : Orthonormal ℝ w) (heig : ∀ i, resolvent (w i) = μ i • w i) :
    cardinalPositiveMass a +
        cardinalOrbitMass a ^ 2 *
          (∑ i, (μ i / (2 * μ i - 1)) * (massCosineReadout (w i) a).re ^ 2) =
      sourceEnergy (eigenGraphRem μ w F.reVector) := by
  have hE := sourceEnergy_eq_neg_sum_eigen_add_rem hμ0 hw heig F.reVector
  rw [F.re_energy] at hE
  have hsum : (∑ i, ((2 * μ i - 1) / μ i) * ⟪w i, F.reVector.val.fst⟫_ℝ ^ 2) =
      cardinalOrbitMass a ^ 2 *
        (∑ i, (μ i / (2 * μ i - 1)) * (massCosineReadout (w i) a).re ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp := eigenvector_cardinal_re_pairing F ha hz (heig i)
    have hne : 2 * μ i - 1 ≠ 0 := by intro h; apply hμhalf i; linarith
    have hi0 := hμ0 i
    have hsq : (2 * μ i - 1) ^ 2 * ⟪w i, F.reVector.val.fst⟫_ℝ ^ 2 =
        μ i ^ 2 * cardinalOrbitMass a ^ 2 * (massCosineReadout (w i) a).re ^ 2 := by
      calc (2 * μ i - 1) ^ 2 * ⟪w i, F.reVector.val.fst⟫_ℝ ^ 2
          = ((1 - 2 * μ i) * ⟪w i, F.reVector.val.fst⟫_ℝ) ^ 2 := by ring
        _ = (μ i * cardinalOrbitMass a * (massCosineReadout (w i) a).re) ^ 2 := by rw [hp]
        _ = μ i ^ 2 * cardinalOrbitMass a ^ 2 * (massCosineReadout (w i) a).re ^ 2 := by ring
    calc ((2 * μ i - 1) / μ i) * ⟪w i, F.reVector.val.fst⟫_ℝ ^ 2
        = ((2 * μ i - 1) ^ 2 * ⟪w i, F.reVector.val.fst⟫_ℝ ^ 2) /
            (μ i * (2 * μ i - 1)) := by
          field_simp [hi0, hne]
      _ = (μ i ^ 2 * cardinalOrbitMass a ^ 2 * (massCosineReadout (w i) a).re ^ 2) /
            (μ i * (2 * μ i - 1)) := by rw [hsq]
      _ = cardinalOrbitMass a ^ 2 *
            ((μ i / (2 * μ i - 1)) * (massCosineReadout (w i) a).re ^ 2) := by
          field_simp [hi0, hne]
  linarith

/-- **Cross-Orbit Spectral Orthogonality Defect Identity**:
for any two nonreal $\Xi$-zeros `a, b` with `0 < a.re`, `0 < b.re`, `XiC a = 0`, `XiC b = 0`, and
`b ∉ cardinalOrbit a`, any `F : CardinalGraphFrame a` and `G : CardinalGraphFrame b`, and any
orthonormal family of eigenvectors `resolvent (w i) = μ i • w i` with `μ i ≠ 0` and `μ i ≠ 1 / 2`,
`cardinalOrbitMass a * cardinalOrbitMass b * ∑ i, (μ i / (2 * μ i - 1)) * (massCosineReadout (w i) a).im * (massCosineReadout (w i) b).im = sourcePair (eigenGraphRem μ w F.imVector) (eigenGraphRem μ w G.imVector)`. -/
theorem cardinal_im_cross_orbit_spectral_eq {a b : ℂ}
    (F : CardinalGraphFrame a) (G : CardinalGraphFrame b)
    (ha : 0 < a.re) (hz : XiC a = 0) (hb : 0 < b.re) (hwz : XiC b = 0)
    (hba : b ∉ cardinalOrbit a)
    {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ0 : ∀ i, μ i ≠ 0) (hμhalf : ∀ i, μ i ≠ 1 / 2)
    (hw : Orthonormal ℝ w) (heig : ∀ i, resolvent (w i) = μ i • w i) :
    cardinalOrbitMass a * cardinalOrbitMass b *
        (∑ i, (μ i / (2 * μ i - 1)) *
          (massCosineReadout (w i) a).im * (massCosineReadout (w i) b).im) =
      sourcePair (eigenGraphRem μ w F.imVector) (eigenGraphRem μ w G.imVector) := by
  have hpair0 : sourcePair F.imVector G.imVector = 0 := by
    rw [G.pair_im hb hwz, (F.readouts_outside_orbit ha hz hwz hba).2, Complex.zero_im, mul_zero]
  have hdecomp := sourcePair_eq_neg_sum_eigen_add_rem hμ0 hw heig F.imVector G.imVector
  rw [hpair0] at hdecomp
  have hsum : (∑ i, ((2 * μ i - 1) / μ i) *
      ⟪w i, F.imVector.val.fst⟫_ℝ * ⟪w i, G.imVector.val.fst⟫_ℝ) =
      cardinalOrbitMass a * cardinalOrbitMass b *
        (∑ i, (μ i / (2 * μ i - 1)) *
          (massCosineReadout (w i) a).im * (massCosineReadout (w i) b).im) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hpa := eigenvector_cardinal_im_pairing F ha hz (heig i)
    have hpb := eigenvector_cardinal_im_pairing G hb hwz (heig i)
    have hne : 2 * μ i - 1 ≠ 0 := by intro h; apply hμhalf i; linarith
    have hi0 := hμ0 i
    have hprod : (2 * μ i - 1) ^ 2 *
        (⟪w i, F.imVector.val.fst⟫_ℝ * ⟪w i, G.imVector.val.fst⟫_ℝ) =
        μ i ^ 2 * (cardinalOrbitMass a * cardinalOrbitMass b) *
          ((massCosineReadout (w i) a).im * (massCosineReadout (w i) b).im) := by
      calc (2 * μ i - 1) ^ 2 * (⟪w i, F.imVector.val.fst⟫_ℝ * ⟪w i, G.imVector.val.fst⟫_ℝ)
          = ((1 - 2 * μ i) * ⟪w i, F.imVector.val.fst⟫_ℝ) *
              ((1 - 2 * μ i) * ⟪w i, G.imVector.val.fst⟫_ℝ) := by ring
        _ = (μ i * cardinalOrbitMass a * (massCosineReadout (w i) a).im) *
              (μ i * cardinalOrbitMass b * (massCosineReadout (w i) b).im) := by rw [hpa, hpb]
        _ = μ i ^ 2 * (cardinalOrbitMass a * cardinalOrbitMass b) *
              ((massCosineReadout (w i) a).im * (massCosineReadout (w i) b).im) := by ring
    calc ((2 * μ i - 1) / μ i) * ⟪w i, F.imVector.val.fst⟫_ℝ * ⟪w i, G.imVector.val.fst⟫_ℝ
        = ((2 * μ i - 1) ^ 2 * (⟪w i, F.imVector.val.fst⟫_ℝ * ⟪w i, G.imVector.val.fst⟫_ℝ)) /
            (μ i * (2 * μ i - 1)) := by
          field_simp [hi0, hne]
      _ = (μ i ^ 2 * (cardinalOrbitMass a * cardinalOrbitMass b) *
            ((massCosineReadout (w i) a).im * (massCosineReadout (w i) b).im)) /
            (μ i * (2 * μ i - 1)) := by rw [hprod]
      _ = cardinalOrbitMass a * cardinalOrbitMass b *
            ((μ i / (2 * μ i - 1)) *
              (massCosineReadout (w i) a).im * (massCosineReadout (w i) b).im) := by
          field_simp [hi0, hne]
  linarith

end RHTower.CHMDPolar
