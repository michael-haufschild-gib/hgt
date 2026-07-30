import GaloisForLFunctions.RHTower.SoninCofinalContractiveInwardIncidence
import GaloisForLFunctions.RHTower.SemilocalCompressedEulerOrientation

/-!
# Ambidextrous cofinal Sonin incidence

The oriented inward Sonin corner

`C = (1 - Q) U_r Q`

is contractive and transports cofinal inverse-dilated shells to their
interior mates.  Its Hilbert adjoint is the reverse corner

`R = Q U_{r⁻¹} (1 - Q)`.

On the same shell family, `R` transports every interior shell back to its
inverse-dilated mate.  Thus both compositions converge strongly to the
identity on the corresponding complete cofinal `ell²` embeddings.

This is a carrier theorem.  It does not identify Xi conormal fibres with
these shell classes and does not create a source codiagonal.
-/

open Complex Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RHTower

/-- Reverse-oriented Sonin dilation corner. -/
def centralSoninOutwardDilationCorner
    (a r : ℝ) (hr : 1 < r) : SoninL2 →L[ℂ] SoninL2 :=
  upperBoundary (centralSoninProjection a)
    (dilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)))

/-- The reverse corner is exactly the Hilbert adjoint of the inward
corner. -/
theorem adjoint_centralSoninInwardDilationCorner
    (a r : ℝ) (hr : 1 < r) :
    ContinuousLinearMap.adjoint
        (centralSoninInwardDilationCorner a r hr) =
      centralSoninOutwardDilationCorner a r hr := by
  rw [centralSoninInwardDilationCorner,
    centralSoninOutwardDilationCorner,
    adjoint_crossBoundary_eq_upperBoundary_of_adjoint_eq]
  · exact
      (isSelfAdjoint_starProjection (centralSoninCarrier a)).star_eq
  · exact adjoint_dilationCLM r (zero_lt_one.trans hr)

/-- The reverse-oriented corner is a contraction. -/
theorem norm_centralSoninOutwardDilationCorner_le_one
    (a r : ℝ) (hr : 1 < r) :
    ‖centralSoninOutwardDilationCorner a r hr‖ ≤ 1 := by
  rw [← adjoint_centralSoninInwardDilationCorner a r hr,
    LinearIsometryEquiv.norm_map]
  exact norm_centralSoninInwardDilationCorner_le_one a r hr

/-- Exact reverse shell error identity. -/
theorem centralSoninOutwardDilationCorner_evenShell_sub_eq
    (a c d r : ℝ) (hcd : c < d) (hda : d < a)
    (hr : 1 < r) (n : ℕ) :
    centralSoninOutwardDilationCorner a r hr
        (evenShellVector c d hcd n) -
      inverseDilatedEvenShell c d r hcd hr n =
        centralSoninProjection a
            (inverseDilatedEvenShell c d r hcd hr n) -
          inverseDilatedEvenShell c d r hcd hr n := by
  let Q : SoninL2 →L[ℂ] SoninL2 := centralSoninProjection a
  let Dinv : SoninL2 →L[ℂ] SoninL2 :=
    dilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))
  let v : SoninL2 := evenShellVector c d hcd n
  let g : SoninL2 := inverseDilatedEvenShell c d r hcd hr n
  have hQv : Q v = 0 := by
    exact centralSoninProjection_eq_zero_of_mem_physicalForbidden a
      (evenShellVector_mem_centralPhysicalForbidden a c d hcd hda n)
  have hBv : (1 - Q) v = v := by
    simp [hQv]
  have hDinvv : Dinv v = g := by
    rfl
  change Q (Dinv ((1 - Q) v)) - g = Q g - g
  rw [hBv, hDinvv]

/-- The reverse corner transports every interior shell to its
inverse-dilated mate. -/
theorem centralSoninOutwardDilationCorner_evenShell_tendsto
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c) :
    Tendsto (fun n =>
      ‖centralSoninOutwardDilationCorner a r hr
          (evenShellVector c d hcd n) -
        inverseDilatedEvenShell c d r hcd hr n‖)
      atTop (𝓝 0) := by
  apply
    (centralSoninProjection_inverseDilatedEvenShell_tendsto
      a c d r ha hc hcd hr harc).congr'
  exact Filter.Eventually.of_forall fun n => by
    exact congrArg norm
      (centralSoninOutwardDilationCorner_evenShell_sub_eq
        a c d r hcd hda hr n).symm

/-- Complete cofinal reverse transport on the `ell²` shell carrier. -/
theorem centralSoninOutwardDilationCorner_cofinalEmbedding_tendsto
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (x : lp (fun _ : ℕ => ℂ) 2) :
    Tendsto (fun N =>
      ‖centralSoninOutwardDilationCorner a r hr
          (cofinalEvenShellEmbedding c d hc hcd N x) -
        cofinalInverseDilatedShellEmbedding c d r hc hcd hr N x‖)
      atTop (𝓝 0) := by
  apply cofinalOrthonormalEmbedding_strong_transport
    (A := cofinalEvenShellEmbedding c d hc hcd)
    (B := cofinalInverseDilatedShellEmbedding c d r hc hcd hr)
    (T := centralSoninOutwardDilationCorner a r hr)
  intro i
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa [cofinalEvenShell, cofinalInverseDilatedEvenShell] using!
    (centralSoninOutwardDilationCorner_evenShell_tendsto
      a c d r ha hc hcd hda hr harc).comp
        (tendsto_add_atTop_nat i)

/-- The adjoint-after-inward composition converges strongly to the
identity on every cofinal inverse-dilated shell vector. -/
theorem centralSoninOutward_comp_inward_cofinalEmbedding_tendsto
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (x : lp (fun _ : ℕ => ℂ) 2) :
    Tendsto (fun N =>
      ‖centralSoninOutwardDilationCorner a r hr
          (centralSoninInwardDilationCorner a r hr
            (cofinalInverseDilatedShellEmbedding
              c d r hc hcd hr N x)) -
        cofinalInverseDilatedShellEmbedding c d r hc hcd hr N x‖)
      atTop (𝓝 0) := by
  let C : SoninL2 →L[ℂ] SoninL2 :=
    centralSoninInwardDilationCorner a r hr
  let R : SoninL2 →L[ℂ] SoninL2 :=
    centralSoninOutwardDilationCorner a r hr
  let A : ℕ → SoninL2 := fun N =>
    cofinalInverseDilatedShellEmbedding c d r hc hcd hr N x
  let B : ℕ → SoninL2 := fun N =>
    cofinalEvenShellEmbedding c d hc hcd N x
  have hforward :
      Tendsto (fun N => C (A N) - B N) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact centralSoninInwardDilationCorner_cofinalEmbedding_tendsto
      a c d r ha hc hcd hda hr harc x
  have hreverse :
      Tendsto (fun N => R (B N) - A N) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact centralSoninOutwardDilationCorner_cofinalEmbedding_tendsto
      a c d r ha hc hcd hda hr harc x
  have hmapped :
      Tendsto (fun N => R (C (A N) - B N)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using
      R.continuous.continuousAt.tendsto.comp hforward
  have hsum :
      Tendsto
        (fun N => R (C (A N) - B N) + (R (B N) - A N))
        atTop (𝓝 0) := by
    simpa using hmapped.add hreverse
  apply tendsto_zero_iff_norm_tendsto_zero.mp
  convert hsum using 1
  funext N
  rw [map_sub]
  abel

/-- The inward-after-adjoint composition converges strongly to the
identity on every cofinal interior shell vector. -/
theorem centralSoninInward_comp_outward_cofinalEmbedding_tendsto
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (x : lp (fun _ : ℕ => ℂ) 2) :
    Tendsto (fun N =>
      ‖centralSoninInwardDilationCorner a r hr
          (centralSoninOutwardDilationCorner a r hr
            (cofinalEvenShellEmbedding c d hc hcd N x)) -
        cofinalEvenShellEmbedding c d hc hcd N x‖)
      atTop (𝓝 0) := by
  let C : SoninL2 →L[ℂ] SoninL2 :=
    centralSoninInwardDilationCorner a r hr
  let R : SoninL2 →L[ℂ] SoninL2 :=
    centralSoninOutwardDilationCorner a r hr
  let A : ℕ → SoninL2 := fun N =>
    cofinalInverseDilatedShellEmbedding c d r hc hcd hr N x
  let B : ℕ → SoninL2 := fun N =>
    cofinalEvenShellEmbedding c d hc hcd N x
  have hforward :
      Tendsto (fun N => C (A N) - B N) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact centralSoninInwardDilationCorner_cofinalEmbedding_tendsto
      a c d r ha hc hcd hda hr harc x
  have hreverse :
      Tendsto (fun N => R (B N) - A N) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact centralSoninOutwardDilationCorner_cofinalEmbedding_tendsto
      a c d r ha hc hcd hda hr harc x
  have hmapped :
      Tendsto (fun N => C (R (B N) - A N)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using
      C.continuous.continuousAt.tendsto.comp hreverse
  have hsum :
      Tendsto
        (fun N => C (R (B N) - A N) + (C (A N) - B N))
        atTop (𝓝 0) := by
    simpa using hmapped.add hforward
  apply tendsto_zero_iff_norm_tendsto_zero.mp
  convert hsum using 1
  funext N
  rw [map_sub]
  abel

end RHTower
