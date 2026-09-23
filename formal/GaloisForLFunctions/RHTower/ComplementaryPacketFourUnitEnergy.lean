import GaloisForLFunctions.RHTower.ComplementaryPacketKernelIntegrability

/-!
# The four-unit transfer of a cofinal affine packet

The critical packet energy of a source-framed curvature kernel is

```text
E_i = 4 ε_i · E_{μ_i} [ D_i (|H - H'|) ] ,
```

where `μ_i` is the law of the oriented clock gap and `D_i` is the two-point modulus of the packet
path.  If the modulus is a cofinal affine isometry of slope `c_i^(2 : ℕ)` with a **uniform** defect `C`,

```text
|D_i a - c_i^(2 : ℕ) a| ≤ C      (a ≥ 0),
```

then the whole packet energy collapses onto the Gini mean difference of the clock:

```text
E_i = 4 c_i^(2 : ℕ) · (ε_i E|H - H'|) + O(ε_i) .
```

Hence `ε_i → 0`, `ε_i E|H - H'| → 1` and `c_i → 1` force `E_i → 4`.  Nothing about the packet
survives except its cofinal slope; the bounded local defect — the `ζ(2)` expansion at
infinitesimal separation — is annihilated by the escaping arithmetic clock.

This is the source-independent half of the four-unit law.  It is stated for an arbitrary filtered
family of probability measures, so it applies verbatim to the squarefree critical clock gap and to
any other escaping clock.
-/

open MeasureTheory Filter

namespace RHTower

noncomputable section

/-- **Uniform cofinal defect collapses the packet energy onto the Gini mean difference.** -/
theorem abs_packetEnergy_sub_le
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {c C ε : ℝ} {D : ℝ → ℝ}
    (hD : ∀ a : ℝ, 0 ≤ a → |D a - c ^ (2 : ℕ) * a| ≤ C)
    (hDint : Integrable (fun x => D |x|) μ)
    (habs : Integrable (fun x => |x|) μ)
    (hε : 0 ≤ ε) :
    |4 * ε * (∫ x, D |x| ∂μ) - 4 * c ^ (2 : ℕ) * (ε * ∫ x, |x| ∂μ)|
      ≤ 4 * ε * C := by
  have hsub : (∫ x, (D |x| - c ^ (2 : ℕ) * |x|) ∂μ)
      = (∫ x, D |x| ∂μ) - c ^ (2 : ℕ) * ∫ x, |x| ∂μ := by
    rw [integral_sub hDint (habs.const_mul _), integral_const_mul]
  have hpt : ∀ x : ℝ, ‖D |x| - c ^ (2 : ℕ) * |x|‖ ≤ C := by
    intro x
    rw [Real.norm_eq_abs]
    exact hD |x| (abs_nonneg x)
  have hnorm : ‖∫ x, (D |x| - c ^ (2 : ℕ) * |x|) ∂μ‖ ≤ C := by
    have h := norm_integral_le_of_norm_le_const (μ := μ) (C := C) (Filter.Eventually.of_forall hpt)
    simpa using h
  rw [hsub, Real.norm_eq_abs] at hnorm
  have hfac : 4 * ε * (∫ x, D |x| ∂μ)
      - 4 * c ^ (2 : ℕ) * (ε * ∫ x, |x| ∂μ)
      = (4 * ε) * ((∫ x, D |x| ∂μ) - c ^ (2 : ℕ) * ∫ x, |x| ∂μ) := by
    ring
  rw [hfac, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 4 * ε)]
  exact mul_le_mul_of_nonneg_left hnorm (by linarith)

/-- **Four-unit packet energy law.**  A cofinal affine packet with uniformly bounded defect,
carried by an escaping clock whose rescaled Gini mean difference tends to one and whose slope
tends to one, has critical packet energy exactly four. -/
theorem tendsto_four_mul_packetEnergy
    {ι : Type*} {F : Filter ι} [F.NeBot]
    {μ : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)] {ε c : ι → ℝ}
    {D : ι → ℝ → ℝ} {C : ℝ}
    (hD : ∀ i, ∀ a : ℝ, 0 ≤ a → |D i a - c i ^ (2 : ℕ) * a| ≤ C)
    (hDint : ∀ i, Integrable (fun x => D i |x|) (μ i))
    (habs : ∀ i, Integrable (fun x => |x|) (μ i))
    (hεnn : ∀ᶠ i in F, 0 ≤ ε i)
    (hε : Tendsto ε F (nhds 0))
    (hεabs : Tendsto (fun i => ε i * ∫ x, |x| ∂μ i) F (nhds 1))
    (hc : Tendsto c F (nhds 1)) :
    Tendsto (fun i => 4 * ε i * ∫ x, D i |x| ∂μ i) F (nhds 4) := by
  -- the Gini leading term
  have hmain : Tendsto
      (fun i => 4 * c i ^ (2 : ℕ) * (ε i * ∫ x, |x| ∂μ i)) F (nhds 4) := by
    have h := (((hc.pow 2).const_mul (4 : ℝ))).mul hεabs
    simpa using h
  -- the uniformly bounded remainder
  have hrem : Tendsto
      (fun i => 4 * ε i * (∫ x, D i |x| ∂μ i)
        - 4 * c i ^ (2 : ℕ) * (ε i * ∫ x, |x| ∂μ i)) F (nhds 0) := by
    have hbound : Tendsto (fun i => 4 * C * ε i) F (nhds 0) := by
      have h := hε.const_mul (4 * C)
      simpa using h
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hεnn] with i hi
    rw [Real.norm_eq_abs]
    calc |4 * ε i * (∫ x, D i |x| ∂μ i)
            - 4 * c i ^ (2 : ℕ) * (ε i * ∫ x, |x| ∂μ i)|
        ≤ 4 * ε i * C := abs_packetEnergy_sub_le (hD i) (hDint i) (habs i) hi
      _ = 4 * C * ε i := by ring
  have hsum := hrem.add hmain
  rw [zero_add] at hsum
  refine hsum.congr fun i => ?_
  ring

end

end RHTower
