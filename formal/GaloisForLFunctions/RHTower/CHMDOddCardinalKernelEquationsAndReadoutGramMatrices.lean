import GaloisForLFunctions.RHTower.CHMDUniversalRieszResolventAndCardinalKernelEquations

/-!
# Odd Cardinal Kernel Equations, SourcePair Reciprocity, and Readout Gram Matrices

This module extends the universal Riesz–resolvent dictionary of
`CHMDUniversalRieszResolventAndCardinalKernelEquations` to parity-projected graph modes, the strip
Fourier and odd Fourier kernels in `MassSpace`, the odd cardinal negative-energy modes, and the full
$k \times k$ spectral readout Gram matrices across any finite family of distinct quarter-zeros:

1. **Universal `sourcePair` Reciprocity and Parity-Projected Pairing**:
   - `sourceEnergy_eq_inner_of_sourcePair_eq_inner`: if `∀ p, sourcePair p q = ⟪p.val.fst, v⟫_ℝ`,
     then `sourceEnergy q = ⟪q.val.fst, v⟫_ℝ`.
   - `sourcePair_reciprocity`: if `∀ p, sourcePair p q₁ = ⟪p.val.fst, v₁⟫_ℝ` and
     `∀ p, sourcePair p q₂ = ⟪p.val.fst, v₂⟫_ℝ`, then
     `⟪q₁.val.fst, v₂⟫_ℝ = ⟪q₂.val.fst, v₁⟫_ℝ` (and both equal `sourcePair q₁ q₂`).
   - `sourcePair_eq_oddGraphPart_of_odd` and `sourcePair_eq_evenGraphPart_of_even`: for any odd
     (resp. even) graph vector `q`, `sourcePair p q = sourcePair (oddGraphPart p) q`
     (resp. `sourcePair (evenGraphPart p) q`) for all `p : SourceGraph`.

2. **Explicit $L^2(\mathrm{massMeasure})$ Strip Fourier Kernels and Odd Cardinal Riesz–Resolvent Equations**:
   - Defines `fourierKernelReL`, `fourierKernelImL`, `oddFourierKernelReL`, and `oddFourierKernelImL`
     in `MassSpace` for any `z : ℂ` in the strip `|z.im| ≤ 1 / 2`.
   - Proves `exists_odd_cardinal_riesz_resolvent_mode`: for every nonreal $\Xi$-zero `a` with
     `0 < a.re`, `XiC a = 0`, and `a.im ≠ 0`, there exists an odd graph vector `q_odd : SourceGraph`
     (`reflectGraph q_odd = -q_odd`) such that on the **entire** `SourceGraph` and `MassSpace`:
     - `⟪q_odd.val.fst, oneL⟫_ℝ = 0` and `⟪q_odd.val.fst, tanhL⟫_ℝ = 0`,
     - `sourceEnergy q_odd = -(cardinalOrbitMass a / 2)` and `weilForm q_odd = -(cardinalOrbitMass a / 2)`,
     - `∀ p : SourceGraph, sourcePair p q_odd = ⟪p.val.fst, -cardinalOrbitMass a • oddFourierKernelReL a hst_a⟫_ℝ`,
     - `q_odd = rieszLift (-cardinalOrbitMass a • oddFourierKernelReL a hst_a + (2 : ℝ) • q_odd.val.fst)`,
     - `q_odd.val.fst - (2 : ℝ) • resolvent q_odd.val.fst = -cardinalOrbitMass a • resolvent (oddFourierKernelReL a hst_a)`.

3. **Full $k \times k$ Spectral Readout Gram Matrix Identities and Coercivity**:
   - `even_cardinal_im_gram_entry_eq`: unifies the diagonal spectral deficit identity
     (`cardinal_im_spectral_deficit_eq`) and off-diagonal cross-orbit identity
     (`cardinal_im_cross_orbit_spectral_eq`) into a single $k \times k$ matrix entry identity for
     any finite family of distinct quarter-zeros.
   - `even_cardinal_im_quadratic_form_eq`: the corresponding quadratic form identity for arbitrary
     real linear combinations `∑ r, c r • (F r).imVector`.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace BigOperators ComplexConjugate
noncomputable section

namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump CHMDTranslation ThetaSourceWard

/-! ## Section 1: Universal `sourcePair` Reciprocity and Parity-Projected Pairing -/

/-- If `sourcePair p q = ⟪p.val.fst, v⟫_ℝ` for all `p : SourceGraph`, then the Doob energy of `q`
is `sourceEnergy q = ⟪q.val.fst, v⟫_ℝ`. -/
theorem sourceEnergy_eq_inner_of_sourcePair_eq_inner {q : SourceGraph} {v : MassSpace}
    (h : ∀ p : SourceGraph, sourcePair p q = ⟪p.val.fst, v⟫_ℝ) :
    sourceEnergy q = ⟪q.val.fst, v⟫_ℝ := by
  rw [← sourcePair_self, h q]

/-- **Universal `sourcePair` Reciprocity Law**:
if `q₁, q₂ : SourceGraph` represent `v₁, v₂ : MassSpace` under `sourcePair`, then
`⟪q₁.val.fst, v₂⟫_ℝ = ⟪q₂.val.fst, v₁⟫_ℝ` and both equal `sourcePair q₁ q₂`. -/
theorem sourcePair_reciprocity {q₁ q₂ : SourceGraph} {v₁ v₂ : MassSpace}
    (h₁ : ∀ p : SourceGraph, sourcePair p q₁ = ⟪p.val.fst, v₁⟫_ℝ)
    (h₂ : ∀ p : SourceGraph, sourcePair p q₂ = ⟪p.val.fst, v₂⟫_ℝ) :
    ⟪q₁.val.fst, v₂⟫_ℝ = ⟪q₂.val.fst, v₁⟫_ℝ ∧
      sourcePair q₁ q₂ = ⟪q₁.val.fst, v₂⟫_ℝ := by
  have hp₂ := h₂ q₁
  have hp₁ := h₁ q₂
  rw [sourcePair_symm q₂ q₁] at hp₁
  exact ⟨hp₂.symm.trans hp₁, hp₂⟩

/-- Even projection of a graph vector `q : SourceGraph`, companion to `oddGraphPart`. -/
def evenGraphPart (q : SourceGraph) : SourceGraph :=
  (1 / 2 : ℝ) • (q + reflectGraph q)

theorem reflectGraph_evenGraphPart (q : SourceGraph) :
    reflectGraph (evenGraphPart q) = evenGraphPart q := by
  unfold evenGraphPart
  rw [reflectGraph_smul, reflectGraph_add, reflectGraph_reflectGraph, add_comm]

theorem evenGraphPart_add_oddGraphPart (q : SourceGraph) :
    evenGraphPart q + oddGraphPart q = q := by
  unfold evenGraphPart oddGraphPart
  module

theorem sourcePair_even_odd_eq_zero_of_reflect {p q : SourceGraph}
    (hp : reflectGraph p = p) (hq : reflectGraph q = -q) :
    sourcePair p q = 0 := by
  have h := sourcePair_reflectGraph p q
  rw [hp, hq, sourcePair_symm p (-q), sourcePair_neg_left, sourcePair_symm q p] at h
  linarith

theorem sourcePair_evenGraphPart_of_odd (p : SourceGraph) {q : SourceGraph}
    (hq : reflectGraph q = -q) :
    sourcePair (evenGraphPart p) q = 0 :=
  sourcePair_even_odd_eq_zero_of_reflect (reflectGraph_evenGraphPart p) hq

theorem sourcePair_oddGraphPart_of_even (p : SourceGraph) {q : SourceGraph}
    (hq : reflectGraph q = q) :
    sourcePair (oddGraphPart p) q = 0 := by
  rw [sourcePair_symm,
    sourcePair_even_odd_eq_zero_of_reflect hq (reflectGraph_oddGraphPart p)]

/-- For any odd graph vector `q` (`reflectGraph q = -q`) and any `p : SourceGraph`,
`sourcePair p q = sourcePair (oddGraphPart p) q`. -/
theorem sourcePair_eq_oddGraphPart_of_odd (p : SourceGraph) {q : SourceGraph}
    (hq : reflectGraph q = -q) :
    sourcePair p q = sourcePair (oddGraphPart p) q := by
  conv_lhs => rw [← evenGraphPart_add_oddGraphPart p]
  rw [sourcePair_add_left, sourcePair_evenGraphPart_of_odd p hq, zero_add]

/-- For any even graph vector `q` (`reflectGraph q = q`) and any `p : SourceGraph`,
`sourcePair p q = sourcePair (evenGraphPart p) q`. -/
theorem sourcePair_eq_evenGraphPart_of_even (p : SourceGraph) {q : SourceGraph}
    (hq : reflectGraph q = q) :
    sourcePair p q = sourcePair (evenGraphPart p) q := by
  conv_lhs => rw [← evenGraphPart_add_oddGraphPart p]
  rw [sourcePair_add_left, sourcePair_oddGraphPart_of_even p hq, add_zero]

/-! ## Section 2: Strip Fourier Kernels and Odd Cardinal Riesz–Resolvent Equations -/

/-- The real part of the strip Fourier kernel `exp(i z x) / cosh(x / 2)` in `MassSpace`. -/
def fourierKernelReL (z : ℂ) (hz : |z.im| ≤ 1 / 2) : MassSpace :=
  (fourierKernel_memLp hz).re.toLp (fun x => (fourierKernel z x).re)

/-- The imaginary part of the strip Fourier kernel `exp(i z x) / cosh(x / 2)` in `MassSpace`. -/
def fourierKernelImL (z : ℂ) (hz : |z.im| ≤ 1 / 2) : MassSpace :=
  (fourierKernel_memLp hz).im.toLp (fun x => (fourierKernel z x).im)

theorem massFourierReadout_re_eq_inner (w : MassSpace) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    (massFourierReadout w z).re = ⟪w, fourierKernelReL z hz⟫_ℝ := by
  change (paperFT (fun x => (phiDoobTest w x : ℂ)) z).re = _
  rw [← CHMDDoobGraph.massFourierReadout_eq_paperFT w z, ← massFourierReadoutCLM_apply w hz]
  change (((⟪fourierKernelReL z hz, w⟫_ℝ : ℂ) +
    I * (⟪fourierKernelImL z hz, w⟫_ℝ : ℂ)).re) = _
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, Complex.ofReal_im, sub_zero, add_zero]
  exact real_inner_comm w _

theorem massFourierReadout_im_eq_inner (w : MassSpace) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    (massFourierReadout w z).im = ⟪w, fourierKernelImL z hz⟫_ℝ := by
  change (paperFT (fun x => (phiDoobTest w x : ℂ)) z).im = _
  rw [← CHMDDoobGraph.massFourierReadout_eq_paperFT w z, ← massFourierReadoutCLM_apply w hz]
  change (((⟪fourierKernelReL z hz, w⟫_ℝ : ℂ) +
    I * (⟪fourierKernelImL z hz, w⟫_ℝ : ℂ)).im) = _
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, zero_mul, one_mul, zero_add]
  exact real_inner_comm w _

theorem graphFourierReadout_re_eq_inner (p : SourceGraph) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    (graphFourierReadout p z).re = ⟪p.val.fst, fourierKernelReL z hz⟫_ℝ := by
  rw [graphFourierReadout_eq_massFourierReadout, massFourierReadout_re_eq_inner p.val.fst hz]

theorem graphFourierReadout_im_eq_inner (p : SourceGraph) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    (graphFourierReadout p z).im = ⟪p.val.fst, fourierKernelImL z hz⟫_ℝ := by
  rw [graphFourierReadout_eq_massFourierReadout, massFourierReadout_im_eq_inner p.val.fst hz]

/-- Odd projection of `fourierKernelReL z hz` in `MassSpace`, representing
`(graphFourierReadout (oddGraphPart ·) z).re`. -/
def oddFourierKernelReL (z : ℂ) (hz : |z.im| ≤ 1 / 2) : MassSpace :=
  (1 / 2 : ℝ) • (fourierKernelReL z hz -
    fourierKernelReL (-z) (by simpa only [Complex.neg_im, abs_neg] using hz))

/-- Odd projection of `fourierKernelImL z hz` in `MassSpace`, representing
`(graphFourierReadout (oddGraphPart ·) z).im`. -/
def oddFourierKernelImL (z : ℂ) (hz : |z.im| ≤ 1 / 2) : MassSpace :=
  (1 / 2 : ℝ) • (fourierKernelImL z hz -
    fourierKernelImL (-z) (by simpa only [Complex.neg_im, abs_neg] using hz))

theorem graphFourierReadout_oddGraphPart_re_eq_inner (p : SourceGraph) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    (graphFourierReadout (oddGraphPart p) z).re =
      ⟪p.val.fst, oddFourierKernelReL z hz⟫_ℝ := by
  have hzn : |(-z).im| ≤ 1 / 2 := by simpa only [Complex.neg_im, abs_neg] using hz
  rw [graphFourierReadout_oddGraphPart p hz, Complex.div_ofNat_re, Complex.sub_re,
    graphFourierReadout_re_eq_inner p hz, graphFourierReadout_re_eq_inner p hzn,
    oddFourierKernelReL, real_inner_smul_right, inner_sub_right]
  ring

theorem graphFourierReadout_oddGraphPart_im_eq_inner (p : SourceGraph) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    (graphFourierReadout (oddGraphPart p) z).im =
      ⟪p.val.fst, oddFourierKernelImL z hz⟫_ℝ := by
  have hzn : |(-z).im| ≤ 1 / 2 := by simpa only [Complex.neg_im, abs_neg] using hz
  rw [graphFourierReadout_oddGraphPart p hz, Complex.div_ofNat_im, Complex.sub_im,
    graphFourierReadout_im_eq_inner p hz, graphFourierReadout_im_eq_inner p hzn,
    oddFourierKernelImL, real_inner_smul_right, inner_sub_right]
  ring

theorem oddGraphPart_eq_self_of_odd {p : SourceGraph} (hp : reflectGraph p = -p) :
    oddGraphPart p = p := by
  unfold oddGraphPart
  rw [hp]
  module

/-- **Universal Riesz–Resolvent Mode for the Odd Cardinal Negative-Energy Vector**:
for every nonreal $\Xi$-zero `a` with `0 < a.re`, `XiC a = 0`, and `a.im ≠ 0`, there exists an odd
graph vector `q_odd : SourceGraph` (`reflectGraph q_odd = -q_odd`) such that on the **entire**
`SourceGraph` and `MassSpace`:
1. `⟪q_odd.val.fst, oneL⟫_ℝ = 0` and `⟪q_odd.val.fst, tanhL⟫_ℝ = 0`,
2. `sourceEnergy q_odd = -(cardinalOrbitMass a / 2)` and `weilForm q_odd = -(cardinalOrbitMass a / 2)`,
3. `∀ p : SourceGraph, sourcePair p q_odd = ⟪p.val.fst, -cardinalOrbitMass a • oddFourierKernelReL a hst_a⟫_ℝ`,
4. `q_odd = rieszLift (-cardinalOrbitMass a • oddFourierKernelReL a hst_a + (2 : ℝ) • q_odd.val.fst)`,
5. `q_odd.val.fst - (2 : ℝ) • resolvent q_odd.val.fst = -cardinalOrbitMass a • resolvent (oddFourierKernelReL a hst_a)`. -/
theorem exists_odd_cardinal_riesz_resolvent_mode {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0)
    (hi : a.im ≠ 0) :
    let hst_a : |a.im| ≤ 1 / 2 := (abs_im_lt_half_of_XiC_eq_zero hz).le
    ∃ q_odd : SourceGraph,
      reflectGraph q_odd = -q_odd ∧
      ⟪q_odd.val.fst, oneL⟫_ℝ = 0 ∧
      ⟪q_odd.val.fst, tanhL⟫_ℝ = 0 ∧
      sourceEnergy q_odd = -(cardinalOrbitMass a / 2) ∧
      weilForm q_odd = -(cardinalOrbitMass a / 2) ∧
      (∀ p : SourceGraph,
        sourcePair p q_odd =
          ⟪p.val.fst, (-cardinalOrbitMass a) • oddFourierKernelReL a hst_a⟫_ℝ) ∧
      q_odd =
        rieszLift ((-cardinalOrbitMass a) • oddFourierKernelReL a hst_a +
          (2 : ℝ) • q_odd.val.fst) ∧
      q_odd.val.fst - (2 : ℝ) • resolvent q_odd.val.fst =
        (-cardinalOrbitMass a) • resolvent (oddFourierKernelReL a hst_a) := by
  intro hst_a
  obtain ⟨q_odd, hq_odd, hq_energy, hq_pair_odd, _⟩ :=
    exists_odd_cardinal_fourier_re_mode ha hz hi
  have hq_odd_sector : q_odd.val.fst ∈ oddSector := by
    rw [mem_oddSector, ← reflectGraph_fst, hq_odd]
    rfl
  have hq_oneL : ⟪q_odd.val.fst, oneL⟫_ℝ = 0 :=
    inner_oneL_eq_zero_of_odd hq_odd_sector
  have hq_tanhL : ⟪q_odd.val.fst, tanhL⟫_ℝ = 0 := by
    have hodd_pv : reflectGraph oddPolarVector = -oddPolarVector := by
      have h_eq : oddPolarVector =
          oddPolarVectorAt CHMDThetaTranslate.radius
            (CHMDThetaTranslate.small_shift (by rw [abs_of_pos CHMDThetaTranslate.radius_pos])) :=
        rfl
      rw [h_eq]
      exact reflectGraph_oddPolarVectorAt _ _
    rw [← polarSine_eq_inner_tanhL, ← sourcePair_oddPolarVector,
      hq_pair_odd oddPolarVector hodd_pv,
      oddPolarVector_mem_fullSpectralNullspace a hz, Complex.zero_re, mul_zero]
  have hq_weil : weilForm q_odd = -(cardinalOrbitMass a / 2) := by
    unfold weilForm
    rw [hq_energy, hq_oneL, hq_tanhL]
    ring
  have hq_pair_all : ∀ p : SourceGraph,
      sourcePair p q_odd =
        ⟪p.val.fst, (-cardinalOrbitMass a) • oddFourierKernelReL a hst_a⟫_ℝ := by
    intro p
    rw [sourcePair_eq_oddGraphPart_of_odd p hq_odd,
      hq_pair_odd (oddGraphPart p) (reflectGraph_oddGraphPart p),
      graphFourierReadout_oddGraphPart_re_eq_inner p hst_a, real_inner_smul_right]
  have hq_riesz : q_odd =
      rieszLift ((-cardinalOrbitMass a) • oddFourierKernelReL a hst_a +
        (2 : ℝ) • q_odd.val.fst) :=
    eq_rieszLift_of_sourcePair_eq_inner hq_pair_all
  have hq_res : q_odd.val.fst - (2 : ℝ) • resolvent q_odd.val.fst =
      (-cardinalOrbitMass a) • resolvent (oddFourierKernelReL a hst_a) := by
    have h1 := sourcePair_eq_inner_iff_resolvent.mp hq_pair_all
    rwa [map_smul] at h1
  exact ⟨q_odd, hq_odd, hq_oneL, hq_tanhL, hq_energy, hq_weil, hq_pair_all, hq_riesz, hq_res⟩

/-! ## Section 3: Full $k \times k$ Spectral Readout Gram Matrix Identities -/

/-- **Unified $k \times k$ Even Cardinal Readout Gram Matrix Entry Identity**:
for any finite family of $k$ distinct quarter-zeros `ρ : Fin k → ℂ` (`ρ r ∈ quarterZeros`,
`Function.Injective ρ`) with `a r = gammaOf (ρ r)`, any frames `F r : CardinalGraphFrame (a r)`,
and any orthonormal family of eigenvectors `resolvent (w i) = μ i • w i` with `μ i ≠ 0` and
`μ i ≠ 1 / 2`, for all `r, s : Fin k`:
`cardinalOrbitMass (a r) * cardinalOrbitMass (a s) * ∑ i, (μ i / (2 * μ i - 1)) * (massCosineReadout (w i) (a r)).im * (massCosineReadout (w i) (a s)).im = (if r = s then cardinalPositiveMass (a r) else 0) + sourcePair (eigenGraphRem μ w (F r).imVector) (eigenGraphRem μ w (F s).imVector)`. -/
theorem even_cardinal_im_gram_entry_eq {k : ℕ} (ρ : Fin k → ℂ)
    (hρ : ∀ r, ρ r ∈ quarterZeros) (hinj : Function.Injective ρ)
    (F : ∀ r, CardinalGraphFrame (gammaOf (ρ r)))
    {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ0 : ∀ i, μ i ≠ 0) (hμhalf : ∀ i, μ i ≠ 1 / 2)
    (hw : Orthonormal ℝ w) (heig : ∀ i, resolvent (w i) = μ i • w i)
    (r s : Fin k) :
    cardinalOrbitMass (gammaOf (ρ r)) * cardinalOrbitMass (gammaOf (ρ s)) *
        (∑ i, (μ i / (2 * μ i - 1)) *
          (massCosineReadout (w i) (gammaOf (ρ r))).im *
          (massCosineReadout (w i) (gammaOf (ρ s))).im) =
      (if r = s then cardinalPositiveMass (gammaOf (ρ r)) else 0) +
        sourcePair (eigenGraphRem μ w (F r).imVector) (eigenGraphRem μ w (F s).imVector) := by
  have ha : ∀ j, 0 < (gammaOf (ρ j)).re := fun j => re_gammaOf_pos_of_quarterZeros (hρ j)
  have hz : ∀ j, XiC (gammaOf (ρ j)) = 0 := fun j => XiC_gammaOf_of_quarterZeros (hρ j)
  have hi : ∀ j, (gammaOf (ρ j)).im ≠ 0 := fun j => im_gammaOf_ne_zero_of_quarterZeros (hρ j)
  by_cases hrs : r = s
  · subst hrs
    rw [if_pos rfl, sourcePair_self]
    have hdiag := cardinal_im_spectral_deficit_eq (F r) (ha r) (hz r) (hi r) hμ0 hμhalf hw heig
    have hsq : cardinalOrbitMass (gammaOf (ρ r)) * cardinalOrbitMass (gammaOf (ρ r)) *
        (∑ i, (μ i / (2 * μ i - 1)) *
          (massCosineReadout (w i) (gammaOf (ρ r))).im *
          (massCosineReadout (w i) (gammaOf (ρ r))).im) =
        cardinalOrbitMass (gammaOf (ρ r)) ^ 2 *
          (∑ i, (μ i / (2 * μ i - 1)) * (massCosineReadout (w i) (gammaOf (ρ r))).im ^ 2) := by
      rw [sq (cardinalOrbitMass _)]
      congr 1
      refine Finset.sum_congr rfl fun i _ => by ring
    linarith
  · rw [if_neg hrs, zero_add]
    have ho : gammaOf (ρ s) ∉ cardinalOrbit (gammaOf (ρ r)) :=
      gammaOf_notMem_cardinalOrbit_of_ne (hρ r) (hρ s) (fun h => hrs (hinj h).symm)
    exact cardinal_im_cross_orbit_spectral_eq (F r) (F s) (ha r) (hz r) (ha s) (hz s)
      ho hμ0 hμhalf hw heig

/-- **Even Cardinal Imaginary Readout Quadratic Form Identity**:
for any finite family of $k$ distinct quarter-zeros `ρ : Fin k → ℂ`, any frames
`F r : CardinalGraphFrame (gammaOf (ρ r))`, any coefficient vector `c : Fin k → ℝ`, and any
orthonormal family of eigenvectors `resolvent (w i) = μ i • w i` with `μ i ≠ 0`,
`∑ r, c r ^ 2 * cardinalPositiveMass (gammaOf (ρ r)) + sourceEnergy (eigenGraphRem μ w (∑ r, c r • (F r).imVector)) = ∑ i, ((2 * μ i - 1) / μ i) * ⟪w i, (∑ r, c r • (F r).imVector).val.fst⟫_ℝ ^ 2`. -/
theorem even_cardinal_im_quadratic_form_eq {k : ℕ} (ρ : Fin k → ℂ)
    (hρ : ∀ r, ρ r ∈ quarterZeros) (hinj : Function.Injective ρ)
    (F : ∀ r, CardinalGraphFrame (gammaOf (ρ r)))
    {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ0 : ∀ i, μ i ≠ 0)
    (hw : Orthonormal ℝ w) (heig : ∀ i, resolvent (w i) = μ i • w i)
    (c : Fin k → ℝ) :
    (∑ r, c r ^ 2 * cardinalPositiveMass (gammaOf (ρ r))) +
        sourceEnergy (eigenGraphRem μ w (∑ r, c r • (F r).imVector)) =
      ∑ i, ((2 * μ i - 1) / μ i) *
        ⟪w i, (∑ r, c r • (F r).imVector).val.fst⟫_ℝ ^ 2 := by
  have ha : ∀ j, 0 < (gammaOf (ρ j)).re := fun j => re_gammaOf_pos_of_quarterZeros (hρ j)
  have hz : ∀ j, XiC (gammaOf (ρ j)) = 0 := fun j => XiC_gammaOf_of_quarterZeros (hρ j)
  have hi : ∀ j, (gammaOf (ρ j)).im ≠ 0 := fun j => im_gammaOf_ne_zero_of_quarterZeros (hρ j)
  have ho : ∀ r s, r ≠ s → gammaOf (ρ s) ∉ cardinalOrbit (gammaOf (ρ r)) :=
    fun r s hrs => gammaOf_notMem_cardinalOrbit_of_ne (hρ r) (hρ s) (fun h => hrs (hinj h).symm)
  let p : Fin k → SourceGraph := fun r => (F r).imVector
  have hdiag : ∀ r s, sourcePair (p r) (p s) =
      if r = s then -cardinalPositiveMass (gammaOf (ρ r)) else 0 := by
    intro r s
    by_cases hrs : r = s
    · subst hrs
      rw [if_pos rfl, sourcePair_self, (F r).im_energy,
        ← cardinalPositiveMass_eq_negative (ha r) (hi r)]
    · rw [if_neg hrs, (F s).pair_im (ha s) (hz s),
        ((F r).readouts_outside_orbit (ha r) (hz r) (hz s) (ho r s hrs)).2,
        Complex.zero_im, mul_zero]
  have hE := sourceEnergy_eq_neg_sum_eigen_add_rem hμ0 hw heig (∑ r, c r • p r)
  have hdiag_sum := sum_sourceEnergy_diagonal p
    (fun r => -cardinalPositiveMass (gammaOf (ρ r))) hdiag c
  have hneg_sum : (∑ r, c r ^ 2 * -cardinalPositiveMass (gammaOf (ρ r))) =
      -(∑ r, c r ^ 2 * cardinalPositiveMass (gammaOf (ρ r))) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  linarith

end RHTower.CHMDPolar
