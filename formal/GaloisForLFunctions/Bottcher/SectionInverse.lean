/-
# The analytic inverse of a tower section

A tower section is injective with nonvanishing derivative, so it is a biholomorphism onto its
(open) image: the global set-theoretic inverse `invFunOn` is analytic, by patching with the local
inverses of the holomorphic inverse function theorem — the far-field pattern
(`FarFieldUnivalence.exists_analytic_inverse_far`) transported to the tower.  The inverse is the
Böttcher coordinate of the section's image region; its powers are the deep radicands.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.SectionTowerStep
import GaloisForLFunctions.Bottcher.BottcherInverse

open Complex Set Filter Metric

namespace Bottcher

/-- The holomorphic local inverse of a tower section at any point of its annulus. -/
theorem TowerSection.exists_localInverse {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi)
    {w₀ : ℂ} (hw₀ : w₀ ∈ annulusSet rlo rhi) :
    ∃ ι : ℂ → ℂ, AnalyticAt ℂ ι (S.T w₀) ∧
      (∀ᶠ w in nhds w₀, ι (S.T w) = w) ∧
      (∀ᶠ z in nhds (S.T w₀), S.T (ι z) = z) := by
  have han : AnalyticAt ℂ S.T w₀ := S.an w₀ hw₀
  have hd0 : deriv S.T w₀ ≠ 0 := S.dne w₀ hw₀
  have hsd : HasStrictDerivAt S.T (deriv S.T w₀) w₀ := han.hasStrictDerivAt
  refine ⟨hsd.localInverse _ _ _ hd0, ?_, ?_, ?_⟩
  · exact han.analyticAt_localInverse hd0
  · exact hsd.eventually_left_inverse hd0
  · exact hsd.eventually_right_inverse hd0

/-- The image of a tower section is open. -/
theorem TowerSection.isOpen_image {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi) :
    IsOpen (S.T '' annulusSet rlo rhi) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨w₀, hw₀, rfl⟩
  obtain ⟨ι, hι, hl, hr⟩ := S.exists_localInverse hw₀
  have hcont : ContinuousAt ι (S.T w₀) := hι.continuousAt
  have hι₀ : ι (S.T w₀) = w₀ := hl.self_of_nhds
  have hev : ∀ᶠ z in nhds (S.T w₀), ι z ∈ annulusSet rlo rhi := by
    apply hcont.preimage_mem_nhds
    rw [hι₀]
    exact (isOpen_annulusSet _ _).mem_nhds hw₀
  filter_upwards [hev, hr] with z hz1 hz2
  exact ⟨ι z, hz1, hz2⟩

/-- The global inverse of a tower section (junk off the image). -/
noncomputable def TowerSection.inv {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi) : ℂ → ℂ :=
  Function.invFunOn S.T (annulusSet rlo rhi)

theorem TowerSection.inv_left {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi)
    {w : ℂ} (hw : w ∈ annulusSet rlo rhi) : S.inv (S.T w) = w :=
  S.inj.leftInvOn_invFunOn hw

theorem TowerSection.inv_right {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi)
    {z : ℂ} (hz : z ∈ S.T '' annulusSet rlo rhi) : S.T (S.inv z) = z := by
  obtain ⟨w, hw, rfl⟩ := hz
  exact Function.invFunOn_eq ⟨w, hw, rfl⟩

theorem TowerSection.inv_mem {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi)
    {z : ℂ} (hz : z ∈ S.T '' annulusSet rlo rhi) : S.inv z ∈ annulusSet rlo rhi := by
  obtain ⟨w, hw, rfl⟩ := hz
  exact Function.invFunOn_mem ⟨w, hw, rfl⟩

/-- **The tower section's inverse is analytic on the image.** -/
theorem TowerSection.inv_analytic {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi) :
    AnalyticOnNhd ℂ S.inv (S.T '' annulusSet rlo rhi) := by
  rintro z ⟨w₀, hw₀, rfl⟩
  obtain ⟨ι, hι, hl, hr⟩ := S.exists_localInverse hw₀
  have hcont : ContinuousAt ι (S.T w₀) := hι.continuousAt
  have hι₀ : ι (S.T w₀) = w₀ := hl.self_of_nhds
  have hlocInA : ∀ᶠ z in nhds (S.T w₀), ι z ∈ annulusSet rlo rhi := by
    apply hcont.preimage_mem_nhds
    rw [hι₀]
    exact (isOpen_annulusSet _ _).mem_nhds hw₀
  have hagree : S.inv =ᶠ[nhds (S.T w₀)] ι := by
    filter_upwards [hlocInA, hr] with z hzA hzR
    have hex : ∃ a ∈ annulusSet rlo rhi, S.T a = z := ⟨ι z, hzA, hzR⟩
    have h1 : S.T (S.inv z) = z := Function.invFunOn_eq hex
    have h2 : S.inv z ∈ annulusSet rlo rhi := Function.invFunOn_mem hex
    exact S.inj h2 hzA (by rw [h1, hzR])
  exact hι.congr hagree.symm

/-- The level identity for the inverse: `‖S.inv z‖ = exp (G_c z)` on the image. -/
theorem TowerSection.norm_inv {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi)
    {z : ℂ} (hz : z ∈ S.T '' annulusSet rlo rhi) :
    Real.log ‖S.inv z‖ = greenFunctionDyn c z := by
  obtain ⟨w, hw, rfl⟩ := hz
  rw [S.inv_left hw, S.level w hw]

end Bottcher
