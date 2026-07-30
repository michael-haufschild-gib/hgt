import GaloisForLFunctions.RHTower.SoninCofinalGlobalEulerCarrier

/-!
# Contractive cofinal inward Sonin incidence

The self-adjoint Sonin dilation corner uses the doubled operator
`U_r + U_{r⁻¹}` and therefore has only a norm-two ceiling.  One oriented
boundary incidence needs only the inward unitary dilation `U_r`.

The resulting corner `(1 - Q) U_r Q` is contractive and retains the same
cofinal exterior-to-interior shell transport.  Consequently it transports
arbitrary moving source two-jets and their codiagonal through every vanishing
positive normal scale while preserving an exact norm-one ceiling.
-/

open Complex Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RHTower

/-- Oriented inward Sonin corner. -/
def centralSoninInwardDilationCorner
    (a r : ℝ) (hr : 1 < r) : SoninL2 →L[ℂ] SoninL2 :=
  crossBoundary (centralSoninProjection a)
    (dilationCLM r (zero_lt_one.trans hr))

/-- The oriented inward corner is a contraction. -/
theorem norm_centralSoninInwardDilationCorner_le_one
    (a r : ℝ) (hr : 1 < r) :
    ‖centralSoninInwardDilationCorner a r hr‖ ≤ 1 := by
  let Q : SoninL2 →L[ℂ] SoninL2 := centralSoninProjection a
  let D : SoninL2 →L[ℂ] SoninL2 :=
    dilationCLM r (zero_lt_one.trans hr)
  have hQ : ‖Q‖ ≤ 1 := by
    dsimp [Q, centralSoninProjection]
    exact Submodule.starProjection_norm_le _
  have hB : ‖(1 : SoninL2 →L[ℂ] SoninL2) - Q‖ ≤ 1 := by
    simpa [Q] using norm_one_sub_centralSoninProjection_le_one a
  apply (centralSoninInwardDilationCorner a r hr).opNorm_le_bound zero_le_one
  intro f
  change ‖((1 - Q) * D * Q) f‖ ≤ 1 * ‖f‖
  calc
    ‖((1 - Q) * D * Q) f‖ =
        ‖(1 - Q) (D (Q f))‖ := by rfl
    _ ≤ ‖1 - Q‖ * ‖D (Q f)‖ := (1 - Q).le_opNorm _
    _ ≤ 1 * ‖D (Q f)‖ :=
      mul_le_mul_of_nonneg_right hB (norm_nonneg _)
    _ = ‖Q f‖ := by
      simp [D, dilationCLM]
    _ ≤ ‖Q‖ * ‖f‖ := Q.le_opNorm _
    _ ≤ 1 * ‖f‖ :=
      mul_le_mul_of_nonneg_right hQ (norm_nonneg _)

/-- Exact shell error identity for the inward corner. -/
theorem centralSoninInwardDilationCorner_inverseDilatedEvenShell_sub_eq
    (a c d r : ℝ) (hcd : c < d) (hda : d < a)
    (hr : 1 < r) (n : ℕ) :
    centralSoninInwardDilationCorner a r hr
        (inverseDilatedEvenShell c d r hcd hr n) -
      evenShellVector c d hcd n =
        ((1 : SoninL2 →L[ℂ] SoninL2) - centralSoninProjection a)
          (dilationCLM r (zero_lt_one.trans hr)
            (centralSoninProjection a
                (inverseDilatedEvenShell c d r hcd hr n) -
              inverseDilatedEvenShell c d r hcd hr n)) := by
  let Q : SoninL2 →L[ℂ] SoninL2 := centralSoninProjection a
  let D : SoninL2 →L[ℂ] SoninL2 :=
    dilationCLM r (zero_lt_one.trans hr)
  let v : SoninL2 := evenShellVector c d hcd n
  let g : SoninL2 := inverseDilatedEvenShell c d r hcd hr n
  have hQv : Q v = 0 := by
    exact centralSoninProjection_eq_zero_of_mem_physicalForbidden a
      (evenShellVector_mem_centralPhysicalForbidden a c d hcd hda n)
  have hDg : D g = v := by
    dsimp [D, g, v, inverseDilatedEvenShell, dilationCLM]
    rw [dilation_dilation_inv]
  have hBv : (1 - Q) v = v := by
    simp [hQv]
  change (1 - Q) (D (Q g)) - v = (1 - Q) (D (Q g - g))
  rw [map_sub, hDg, map_sub, hBv]

/-- The contractive inward corner transports every inverse-dilated shell to
its interior mate. -/
theorem centralSoninInwardDilationCorner_inverseDilatedEvenShell_tendsto
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c) :
    Tendsto (fun n =>
      ‖centralSoninInwardDilationCorner a r hr
          (inverseDilatedEvenShell c d r hcd hr n) -
        evenShellVector c d hcd n‖) atTop (𝓝 0) := by
  have hsource :
      Tendsto (fun n =>
        centralSoninProjection a
            (inverseDilatedEvenShell c d r hcd hr n) -
          inverseDilatedEvenShell c d r hcd hr n)
        atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact centralSoninProjection_inverseDilatedEvenShell_tendsto
      a c d r ha hc hcd hr harc
  let B : SoninL2 →L[ℂ] SoninL2 :=
    ((1 : SoninL2 →L[ℂ] SoninL2) - centralSoninProjection a) ∘L
      dilationCLM r (zero_lt_one.trans hr)
  have himage : Tendsto (fun n =>
      B (centralSoninProjection a
          (inverseDilatedEvenShell c d r hcd hr n) -
        inverseDilatedEvenShell c d r hcd hr n))
      atTop (𝓝 0) := by
    convert B.continuous.continuousAt.tendsto.comp hsource using 1
    · rfl
    · simp
  apply tendsto_zero_iff_norm_tendsto_zero.mp
  apply himage.congr'
  exact Filter.Eventually.of_forall fun n => by
    simpa [B] using
      (centralSoninInwardDilationCorner_inverseDilatedEvenShell_sub_eq
        a c d r hcd hda hr n).symm

/-- Complete cofinal `ell²` carrier transport for the contractive inward
corner. -/
theorem centralSoninInwardDilationCorner_cofinalEmbedding_tendsto
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (x : lp (fun _ : ℕ => ℂ) 2) :
    Tendsto (fun N =>
      ‖centralSoninInwardDilationCorner a r hr
          (cofinalInverseDilatedShellEmbedding c d r hc hcd hr N x) -
        cofinalEvenShellEmbedding c d hc hcd N x‖)
      atTop (𝓝 0) := by
  apply cofinalOrthonormalEmbedding_strong_transport
    (A := cofinalInverseDilatedShellEmbedding c d r hc hcd hr)
    (B := cofinalEvenShellEmbedding c d hc hcd)
    (T := centralSoninInwardDilationCorner a r hr)
  intro i
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa [cofinalInverseDilatedEvenShell, cofinalEvenShell] using!
    (centralSoninInwardDilationCorner_inverseDilatedEvenShell_tendsto
      a c d r ha hc hcd hda hr harc).comp
        (tendsto_add_atTop_nat i)

/-- Every cofinal embedded source vector is transported contractively. -/
theorem norm_centralSoninInwardDilationCorner_cofinalEmbedding_le
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d)
    (hr : 1 < r) (N : ℕ) (x : lp (fun _ : ℕ => ℂ) 2) :
    ‖centralSoninInwardDilationCorner a r hr
        (cofinalInverseDilatedShellEmbedding c d r hc hcd hr N x)‖ ≤
      ‖x‖ := by
  calc
    ‖centralSoninInwardDilationCorner a r hr
        (cofinalInverseDilatedShellEmbedding c d r hc hcd hr N x)‖ ≤
        ‖centralSoninInwardDilationCorner a r hr‖ *
          ‖cofinalInverseDilatedShellEmbedding c d r hc hcd hr N x‖ :=
      (centralSoninInwardDilationCorner a r hr).le_opNorm _
    _ ≤ 1 * ‖cofinalInverseDilatedShellEmbedding c d r hc hcd hr N x‖ :=
      mul_le_mul_of_nonneg_right
        (norm_centralSoninInwardDilationCorner_le_one a r hr)
        (norm_nonneg _)
    _ = ‖x‖ := by rw [one_mul, LinearIsometry.norm_map]

/-- Conjugation by the inward corner contracts Hilbert--Schmidt energy. -/
theorem hsNormSq_centralSoninInwardDilationCorner_conjugation_le
    (a r : ℝ) (hr : 1 < r)
    (X : SoninL2 →L[ℂ] SoninL2)
    (hX : ContinuousLinearMap.IsHilbertSchmidt X) :
    ContinuousLinearMap.hsNormSq
        (centralSoninInwardDilationCorner a r hr ∘L X ∘L
          ContinuousLinearMap.adjoint
            (centralSoninInwardDilationCorner a r hr)) ≤
      ContinuousLinearMap.hsNormSq X := by
  let C := centralSoninInwardDilationCorner a r hr
  have hC : ‖C‖ ≤ 1 :=
    norm_centralSoninInwardDilationCorner_le_one a r hr
  have hCsq : ‖C‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg C]
  have hCX : ContinuousLinearMap.IsHilbertSchmidt (C ∘L X) :=
    hX.comp_left C
  have hright :=
    ContinuousLinearMap.hsNormSq_comp_right_le hCX
      (ContinuousLinearMap.adjoint C)
  have hleft :=
    ContinuousLinearMap.hsNormSq_comp_left_le hX C
  have hAdjNorm :
      ‖ContinuousLinearMap.adjoint C‖ = ‖C‖ :=
    (ContinuousLinearMap.adjoint :
      (SoninL2 →L[ℂ] SoninL2) ≃ₗᵢ⋆[ℂ]
        (SoninL2 →L[ℂ] SoninL2)).norm_map C
  calc
    ContinuousLinearMap.hsNormSq
        (C ∘L X ∘L ContinuousLinearMap.adjoint C) ≤
        ‖ContinuousLinearMap.adjoint C‖ ^ 2 *
          ContinuousLinearMap.hsNormSq (C ∘L X) := hright
    _ = ‖C‖ ^ 2 *
          ContinuousLinearMap.hsNormSq (C ∘L X) := by rw [hAdjNorm]
    _ ≤ 1 * ContinuousLinearMap.hsNormSq (C ∘L X) :=
      mul_le_mul_of_nonneg_right hCsq
        (ContinuousLinearMap.hsNormSq_nonneg _)
    _ = ContinuousLinearMap.hsNormSq (C ∘L X) := one_mul _
    _ ≤ ‖C‖ ^ 2 * ContinuousLinearMap.hsNormSq X := hleft
    _ ≤ 1 * ContinuousLinearMap.hsNormSq X :=
      mul_le_mul_of_nonneg_right hCsq
        (ContinuousLinearMap.hsNormSq_nonneg _)
    _ = ContinuousLinearMap.hsNormSq X := one_mul _

/-- Singular two-jet and codiagonal transport through one common contractive
inward Sonin schedule. -/
theorem exists_centralSoninInwardDilationCorner_singularDiagonal_pair_codiagonal
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (father detail : ℕ → lp (fun _ : ℕ => ℂ) 2)
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (hepsilonZero : Tendsto epsilon atTop (𝓝 0)) :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      Tendsto (fun n =>
        ‖centralSoninInwardDilationCorner a r hr
              (cofinalInverseDilatedShellEmbedding
                c d r hc hcd hr (depth n) (father n)) -
            cofinalEvenShellEmbedding c d hc hcd
              (depth n) (father n)‖ /
          epsilon n)
        atTop (𝓝 0) ∧
      Tendsto (fun n =>
        ‖centralSoninInwardDilationCorner a r hr
              (cofinalInverseDilatedShellEmbedding
                c d r hc hcd hr (depth n) (detail n)) -
            cofinalEvenShellEmbedding c d hc hcd
              (depth n) (detail n)‖ /
          epsilon n)
        atTop (𝓝 0) ∧
      Tendsto (fun n =>
        ‖inner ℂ
              (centralSoninInwardDilationCorner a r hr
                (cofinalInverseDilatedShellEmbedding
                  c d r hc hcd hr (depth n) (father n)))
              (centralSoninInwardDilationCorner a r hr
                (cofinalInverseDilatedShellEmbedding
                  c d r hc hcd hr (depth n) (detail n))) -
            inner ℂ (father n) (detail n)‖ / epsilon n)
        atTop (𝓝 0) := by
  apply exists_strictMono_singularDiagonal_transport_pair_codiagonal
    (A := cofinalInverseDilatedShellEmbedding c d r hc hcd hr)
    (B := cofinalEvenShellEmbedding c d hc hcd)
    (T := centralSoninInwardDilationCorner a r hr)
    (hbasis := by
      intro i
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa [cofinalInverseDilatedEvenShell, cofinalEvenShell] using!
        (centralSoninInwardDilationCorner_inverseDilatedEvenShell_tendsto
          a c d r ha hc hcd hda hr harc).comp
            (tendsto_add_atTop_nat i))
    (father := father) (detail := detail)
    (epsilon := epsilon) hepsilon hepsilonZero

end RHTower
