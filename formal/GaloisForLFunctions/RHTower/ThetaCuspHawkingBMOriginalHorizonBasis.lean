import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalHorizonWronskian
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalHorizonDomain

/-! Every original homogeneous solution has its actual horizon coefficients. -/
open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The original horizon coefficient extracted from one interior physical jet. -/
def horizonRegularCoefficient (w chi : ℂ) (U D : ℝ → ℂ) : ℂ :=
  radialBracket U D (horizon (-w) chi) (horizonFirst (-w) chi) (1/2) / (-w)

/-- The opposite coefficient extracted from the actual original Green bracket. -/
def horizonOppositeCoefficient (w chi : ℂ) (U D : ℝ → ℂ) : ℂ :=
  radialBracket (horizon w chi) (horizonFirst w chi) U D (1/2) / (-w)

/-- The two original horizon modes span every actual homogeneous solution and its derivative. -/
theorem original_homogeneous_horizon_representation (w chi : ℂ) (hw : w.im ≠ 0)
    {U D DD : ℝ → ℂ}
    (hU : ∀ b ∈ Ioo 0 1, HasDerivAt U (D b) b)
    (hD : ∀ b ∈ Ioo 0 1, HasDerivAt D (DD b) b)
    (hL : ∀ b : ℝ, b ∈ Ioo 0 1 →
      D4BMPhysicalMaster.radialJet (I*w) chi b (U b) (D b) (DD b)=0)
    {b : ℝ} (hb : b ∈ Ioo 0 1) :
    U b = horizonRegularCoefficient w chi U D * horizon w chi b +
      horizonOppositeCoefficient w chi U D * horizon (-w) chi b ∧
    D b = horizonRegularCoefficient w chi U D * horizonFirst w chi b +
      horizonOppositeCoefficient w chi U D * horizonFirst (-w) chi b := by
  have hm : (1/2:ℝ) ∈ Ioo 0 1 := by constructor <;> norm_num
  have hA := radialBracket_constant w chi hU hD
    (fun z hz => (horizon_derivatives_continued hz).1)
    (fun z hz => (horizon_derivatives_continued hz).2)
    hL (fun z hz => oppositeHorizon_equation w chi hw hz) hm hb
  have hB := radialBracket_constant w chi
    (fun z hz => (horizon_derivatives_continued hz).1)
    (fun z hz => (horizon_derivatives_continued hz).2)
    hU hD (fun z hz => horizon_equation_continued hw hz) hL hm hb
  have hw0 : w ≠ 0 := by intro he; apply hw; rw [he,Complex.zero_im]
  have hW := original_horizon_wronskian w chi hw hb
  dsimp [horizonRegularCoefficient,horizonOppositeCoefficient]
  rw [hA,hB]
  dsimp [radialBracket] at hW ⊢
  constructor
  · field_simp [hw0]
    linear_combination (U b)*hW
  · field_simp [hw0]
    linear_combination (D b)*hW

/-- The fixed C² horizon domain is exactly vanishing of the actual opposite coefficient. -/
theorem original_homogeneous_horizon_domain_iff (w chi : ℂ) (hw : w.im ≠ 0)
    (hwr : -2 < w.re) {U D DD : ℝ → ℂ}
    (hU : ∀ b ∈ Ioo 0 1, HasDerivAt U (D b) b)
    (hD : ∀ b ∈ Ioo 0 1, HasDerivAt D (DD b) b)
    (hL : ∀ b : ℝ, b ∈ Ioo 0 1 →
      D4BMPhysicalMaster.radialJet (I*w) chi b (U b) (D b) (DD b)=0) :
    OriginalHorizonC2 w U ↔ horizonOppositeCoefficient w chi U D=0 := by
  let A := horizonRegularCoefficient w chi U D
  let B := horizonOppositeCoefficient w chi U D
  have he : (fun b => power (-w/2) b*U b) =ᶠ[𝓝[>] (0:ℝ)]
      fun b => power (-w/2) b*(A*horizon w chi b+B*horizon (-w) chi b) := by
    have hlt : ∀ᶠ b : ℝ in 𝓝[>] (0:ℝ), b < 1 :=
      (show ∀ᶠ b : ℝ in 𝓝 0, b < 1 from Iio_mem_nhds (by norm_num)).filter_mono inf_le_left
    filter_upwards [self_mem_nhdsWithin,hlt] with b hb hb1
    rw [(original_homogeneous_horizon_representation w chi hw hU hD hL ⟨hb,hb1⟩).1]
  have hc : OriginalHorizonC2 w U ↔
      OriginalHorizonC2 w (fun b => A*horizon w chi b+B*horizon (-w) chi b) := by
    constructor
    · rintro ⟨g,hg,heq⟩
      exact ⟨g,hg,heq.trans he⟩
    · rintro ⟨g,hg,heq⟩
      exact ⟨g,hg,heq.trans he.symm⟩
  exact hc.trans (originalHorizonC2_modes_iff w chi A B hw hwr)

end
end RHTower.D4BMLaplaceRadial
