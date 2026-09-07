import GaloisForLFunctions.HTGeometry.ModularFundamentalDomainMeasure
import GaloisForLFunctions.HTGeometry.HolomorphicPoincareSeriesModularForm
import GaloisForLFunctions.Bottcher.Gamma2ProperAction

/-!
Locally finite real-smooth modular periodization preserves compact interior test functions on the entire closed fundamental cell.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
noncomputable section

instance : ProperlyDiscontinuousSMul PSL2Z UpperHalfPlane :=
  Bottcher.properlyDiscontinuousSMul_of_surjective
    (QuotientGroup.mk : SL(2, ℤ) → PSL2Z) QuotientGroup.mk_surjective PSL2Z_mk_smul

instance : ContinuousConstSMul PSL2Z UpperHalfPlane where
  continuous_const_smul γ := by
    induction γ using QuotientGroup.induction_on with
    | H A =>
      simp_rw [PSL2Z_mk_smul,sl_moeb]
      exact continuous_const_smul _

/-- Real smoothness in the original upper-half-plane coordinate. -/
def ChartSmooth (f : UpperHalfPlane → ℂ) : Prop :=
  ∀ z : UpperHalfPlane, ContDiffAt ℝ ∞ (f ∘ UpperHalfPlane.ofComplex) (z : ℂ)

/-- The locally finite modular periodization of a compactly supported function. -/
def periodize (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  ∑' γ : PSL2Z, f (γ • z)

/-- Modular periodization is invariant under the actual projective modular action. -/
theorem periodize_invariant (f : UpperHalfPlane → ℂ) (γ : PSL2Z) (z : UpperHalfPlane) :
    periodize f (γ • z) = periodize f z := by
  unfold periodize
  simp only [← mul_smul]
  exact (Equiv.mulRight γ).tsum_eq (fun a => f (a • z))

/-- Compact support makes the full modular sum a fixed finite sum on a neighborhood
of every point, including points on the modular seams. -/
theorem periodize_locally_finite (f : UpperHalfPlane → ℂ) (hf : HasCompactSupport f)
    (z : UpperHalfPlane) :
    ∃ s : Finset PSL2Z, ∀ᶠ w in 𝓝 z, periodize f w = ∑ γ ∈ s, f (γ • w) := by
  classical
  obtain ⟨K,hK,hKz⟩ := exists_compact_mem_nhds z
  have hfinite := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := PSL2Z) hK hf
  refine ⟨hfinite.toFinset, ?_⟩
  filter_upwards [hKz] with w hw
  apply tsum_eq_sum
  intro γ hγ
  by_contra hn
  apply hγ
  simp only [Set.Finite.mem_toFinset]
  exact ⟨γ • w,⟨w,hw,rfl⟩,subset_tsupport f hn⟩

private theorem smul_chart_smooth (γ : PSL2Z) (z : UpperHalfPlane) :
    ContDiffAt ℝ ∞ (fun w : ℂ => ((γ • UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ))
      (z : ℂ) := by
  induction γ using QuotientGroup.induction_on with
  | H A =>
    simp only [PSL2Z_mk_smul]
    have hd : ((A 1 0 : ℤ) : ℂ)*(z:ℂ)+((A 1 1 : ℤ):ℂ) ≠ 0 := by
      simpa using UpperHalfPlane.linear_ne_zero z (SL2_bottomRow_real_ne_zero A)
    have hrat : ContDiffAt ℂ ∞ (fun w : ℂ =>
        (((A 0 0 : ℤ):ℂ)*w+((A 0 1 : ℤ):ℂ))/
        (((A 1 0 : ℤ):ℂ)*w+((A 1 1 : ℤ):ℂ))) (z:ℂ) := by
      exact (contDiffAt_const.mul contDiffAt_id |>.add contDiffAt_const).div
        (contDiffAt_const.mul contDiffAt_id |>.add contDiffAt_const) hd
    apply (hrat.restrict_scalars ℝ).congr_of_eventuallyEq
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    exact coe_smul_ofComplex_eq A hw

private theorem ChartSmooth.smul {f : UpperHalfPlane → ℂ} (hf : ChartSmooth f) (γ : PSL2Z) :
    ChartSmooth (fun z => f (γ • z)) := by
  intro z
  have hf' : ContDiffAt ℝ ∞ (f ∘ UpperHalfPlane.ofComplex)
      ((γ • UpperHalfPlane.ofComplex (z:ℂ) : UpperHalfPlane):ℂ) := by
    simpa only [UpperHalfPlane.ofComplex_apply] using hf (γ • z)
  have h := hf'.comp (z:ℂ) (smul_chart_smooth γ z)
  simpa only [Function.comp_def, UpperHalfPlane.ofComplex_apply] using h

/-- Periodization retains real smoothness on the entire upper half-plane. -/
theorem periodize_smooth (f : UpperHalfPlane → ℂ) (hf : HasCompactSupport f)
    (hs : ChartSmooth f) : ChartSmooth (periodize f) := by
  intro z
  obtain ⟨s,he⟩ := periodize_locally_finite f hf z
  have hsum := ContDiffAt.sum (fun γ (_ : γ ∈ s) => ChartSmooth.smul hs γ z)
  apply hsum.congr_of_eventuallyEq
  have hc := (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) z.im_pos).continuousAt
  have he' := hc.eventually (by simpa only [UpperHalfPlane.ofComplex_apply] using he)
  exact he'

private theorem smul_not_mem_fdo (γ : PSL2Z) (hγ : γ ≠ 1) (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) : γ • z ∉ ModularGroup.fdo := by
  induction γ using QuotientGroup.induction_on with
  | H A =>
    intro hf
    rw [PSL2Z_mk_smul] at hf
    have hback : A⁻¹ • (A • z) ∈ ModularGroup.fd := by simpa using hz
    obtain ha | ha := ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hf hback
    · apply hγ
      have hA : A = 1 := inv_eq_one.mp ha
      simp [hA]
    · apply hγ
      have hA : A = -1 := by simpa using congrArg Inv.inv ha
      rw [hA]
      exact (QuotientGroup.eq_one_iff _).mpr neg_one_mem_modularActionKernel

/-- An interior-supported test extends to a globally modular smooth function while
preserving every value on the original closed fundamental cell. -/
theorem periodize_eq_on_fd (f : UpperHalfPlane → ℂ)
    (hf : Function.support f ⊆ ModularGroup.fdo) (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) : periodize f z = f z := by
  unfold periodize
  rw [tsum_eq_single (1:PSL2Z)]
  · simp
  · intro γ hγ
    exact Function.notMem_support.mp (fun hn => smul_not_mem_fdo γ hγ z hz (hf hn))

end
end RHTower.D4BMModularCore
