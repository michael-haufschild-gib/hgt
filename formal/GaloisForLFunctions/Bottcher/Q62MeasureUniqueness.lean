/-
# q62 — GAP-A Half A substrate: measure uniqueness from equal logarithmic potentials

Two compact-carrier finite measures on `ℂ` whose negative logarithmic potentials agree
Lebesgue-a.e. are equal.  `−Uᵘ` has distributional Laplacian `2π μ` (free fundamental-solution
representation, reflexivity of `isRieszMeasureOfSmooth_of_potentialRep_ae_carrier`), so equal
potentials force equal smooth Riesz functionals; the `C²`-tested equality is promoted to all `C_c`
test functions by mollification (`tendsto_mollified` + dominated convergence).  Uniqueness engine
for Half A: on `ℂ ∖ K_c` the target-Brolin and shifted measures share `−G_c`; once `volume(K_c)=0`
they agree a.e., hence coincide, giving `f_*μ = μ`.
-/
import GaloisForLFunctions.Bottcher.Brolin.WeylLemma
open MeasureTheory Complex Filter Metric Set Topology
namespace Bottcher
noncomputable section

theorem isRieszMeasureOfSmooth_neg_logPotential {μ : Measure ℂ} [IsFiniteMeasure μ] {A : ℝ}
    (hA : μ (Metric.closedBall 0 A)ᶜ = 0) :
    IsRieszMeasureOfSmooth μ (fun z => - logPotential μ z) :=
  isRieszMeasureOfSmooth_of_potentialRep_ae_carrier μ hA _ (Filter.EventuallyEq.refl _ _)

theorem integral_eq_of_neg_logPotential_ae_eq {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A B : ℝ} (hA : μ (Metric.closedBall 0 A)ᶜ = 0) (hB : ν (Metric.closedBall 0 B)ᶜ = 0)
    (hpot : (fun z => - logPotential μ z) =ᵐ[volume] fun z => - logPotential ν z)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    ∫ z, φ z ∂μ = ∫ z, φ z ∂ν := by
  rw [isRieszMeasureOfSmooth_neg_logPotential hA φ hφ hφc,
      isRieszMeasureOfSmooth_neg_logPotential hB φ hφ hφc]
  congr 1
  exact integral_congr_ae (by filter_upwards [hpot] with z hz; rw [hz])

/-- **Measure uniqueness from equal potentials.**  Two compact-carrier finite measures on `ℂ`
with `−logPot` agreeing Lebesgue-a.e. are equal.  The `C²`-tested equality
(`integral_eq_of_neg_logPotential_ae_eq`) is upgraded to all `C_c` test functions by mollification
(`tendsto_mollified` + dominated convergence). -/
theorem measure_eq_of_neg_logPotential_ae_eq {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A B : ℝ} (hA : μ (Metric.closedBall 0 A)ᶜ = 0) (hB : ν (Metric.closedBall 0 B)ᶜ = 0)
    (hpot : (fun z => - logPotential μ z) =ᵐ[volume] fun z => - logPotential ν z) :
    μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  set g : ℂ → ℝ := fun z => f z with hgdef
  have hgcont : Continuous g := f.continuous
  have hgcs : HasCompactSupport g := f.hasCompactSupport
  obtain ⟨Mg, hMg⟩ : ∃ Mg : ℝ, ∀ z, |g z| ≤ Mg := by
    obtain ⟨Mg, hMg⟩ := hgcs.exists_bound_of_continuous hgcont
    exact ⟨Mg, fun z => by simpa [Real.norm_eq_abs] using hMg z⟩
  set fn : ℕ → ℂ → ℝ := fun n => convolution g (mollN n) (ContinuousLinearMap.lsmul ℝ ℝ) volume with hfndef
  have hfn_cd : ∀ n, ContDiff ℝ 2 (fn n) := fun n =>
    (mollN_hasCompactSupport n).contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      hgcont.locallyIntegrable ((mollN_contDiff n).of_le (by norm_num))
  have hfn_cs : ∀ n, HasCompactSupport (fn n) := fun n =>
    HasCompactSupport.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hgcs
      (mollN_hasCompactSupport n)
  have hfn_bound : ∀ n z, |fn n z| ≤ Mg := by
    intro n z
    have hn0 : (0:ℝ) < (n:ℝ)+1 := by
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    have hr1 : 1/((n:ℝ)+1) ≤ 1 := by
      rw [div_le_one hn0]
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    exact convolution_mollN_le n hr1 (fun t _ => hMg t)
  have hfn_eq : ∀ n, ∫ z, fn n z ∂μ = ∫ z, fn n z ∂ν :=
    fun n => integral_eq_of_neg_logPotential_ae_eq hA hB hpot (hfn_cd n) (hfn_cs n)
  have hlim : ∀ (ρ : Measure ℂ), IsFiniteMeasure ρ →
      Tendsto (fun n => ∫ z, fn n z ∂ρ) atTop (𝓝 (∫ z, g z ∂ρ)) := by
    intro ρ _
    refine tendsto_integral_of_dominated_convergence (fun _ => Mg)
      (fun n => (hfn_cd n).continuous.aestronglyMeasurable) (integrable_const Mg) ?_ ?_
    · exact fun n => Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs]; exact hfn_bound n z)
    · exact Filter.Eventually.of_forall (fun z => tendsto_mollified g hgcont z)
  have hμ := hlim μ ‹_›
  have hν := hlim ν ‹_›
  have : ∫ z, g z ∂μ = ∫ z, g z ∂ν :=
    tendsto_nhds_unique (hμ.congr (fun n => hfn_eq n)) hν
  exact this

end
end Bottcher
