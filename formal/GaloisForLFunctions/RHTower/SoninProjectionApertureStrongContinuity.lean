import GaloisForLFunctions.RHTower.SoninCarrierApertureChain
import GaloisForLFunctions.RHTower.SoninCarrierFromExtended
import GaloisForLFunctions.HTGeometry.CommutingProjectionIntersectionEnergy
import Mathlib.Topology.Order.AtTopBotIxx

/-!
# Strong continuity of the Sonin projection in the aperture

The concrete Sonin carriers form a genuinely continuous decreasing flag.  Burnol's dense-union
theorem gives continuity from larger apertures.  In the other direction, a vector lying in every
strictly smaller-aperture carrier vanishes on every inner central interval, hence almost everywhere
on the limiting closed interval: only its two null endpoints are omitted.  Applying the same
argument after the Fourier unitary identifies the full carrier intersection.

The two lattice limits, combined with monotone convergence of orthogonal projections, prove that
the actual Sonin projection is strongly continuous at every positive aperture.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

private def innerAperture (a : ℝ) (n : ℕ) : ℝ :=
  a - 1 / ((n : ℝ) + 1)

private theorem innerAperture_lt (a : ℝ) (n : ℕ) :
    innerAperture a n < a := by
  dsimp [innerAperture]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hn
  linarith

private theorem eventually_zero_on_centralInterval_of_mem_all_lt
    {a : ℝ} {f : SoninL2}
    (hf : ∀ b : Set.Iio a, f ∈ centralSoninCarrier b.1) :
    ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a → (f : ℝ → ℂ) x = 0 := by
  have hzero : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure ℝ),
      x ∈ centralInterval (innerAperture a n) → (f : ℝ → ℂ) x = 0 := by
    intro n
    have hmem := physical_indicator_ae_zero_of_mem_centralSoninCarrier
      (hf ⟨innerAperture a n, innerAperture_lt a n⟩)
    filter_upwards [hmem] with x hx
    intro hxmem
    simpa [Set.indicator_of_mem hxmem] using hx
  rw [← ae_all_iff] at hzero
  filter_upwards [hzero, volume.ae_ne (-a), volume.ae_ne a] with x hx hleft hright
  intro hxmem
  have hxlt : |x| < a := by
    rw [centralInterval, Set.mem_Icc] at hxmem
    rw [abs_lt]
    exact ⟨lt_of_le_of_ne hxmem.1 (Ne.symm hleft),
      lt_of_le_of_ne hxmem.2 hright⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < a - |x| by linarith)
  apply hx n
  rw [centralInterval, Set.mem_Icc]
  have hbound : |x| ≤ innerAperture a n := by
    dsimp [innerAperture]
    have : 1 / ((n : ℝ) + 1) < a - |x| := hn
    linarith
  exact abs_le.mp hbound

private theorem eventually_fourier_zero_on_centralInterval_of_mem_all_lt
    {a : ℝ} {f : SoninL2}
    (hf : ∀ b : Set.Iio a, f ∈ centralSoninCarrier b.1) :
    ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) x = 0 := by
  have hzero : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure ℝ),
      x ∈ centralInterval (innerAperture a n) →
        ((fourierUnitary f : SoninL2) : ℝ → ℂ) x = 0 := by
    intro n
    have hmem := fourier_indicator_ae_zero_of_mem_fourierOrthogonal
      (hf ⟨innerAperture a n, innerAperture_lt a n⟩).2
    filter_upwards [hmem] with x hx
    intro hxmem
    simpa [Set.indicator_of_mem hxmem] using hx
  rw [← ae_all_iff] at hzero
  filter_upwards [hzero, volume.ae_ne (-a), volume.ae_ne a] with x hx hleft hright
  intro hxmem
  have hxlt : |x| < a := by
    rw [centralInterval, Set.mem_Icc] at hxmem
    rw [abs_lt]
    exact ⟨lt_of_le_of_ne hxmem.1 (Ne.symm hleft),
      lt_of_le_of_ne hxmem.2 hright⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < a - |x| by linarith)
  apply hx n
  rw [centralInterval, Set.mem_Icc]
  have hbound : |x| ≤ innerAperture a n := by
    dsimp [innerAperture]
    have : 1 / ((n : ℝ) + 1) < a - |x| := hn
    linarith
  exact abs_le.mp hbound

/-- The Sonin carrier is the closed intersection of all strictly smaller-aperture carriers. -/
theorem iInf_lt_centralSoninCarrier (a : ℝ) :
    (⨅ b : Set.Iio a, centralSoninCarrier b.1) = centralSoninCarrier a := by
  refine le_antisymm ?_ ?_
  · intro f hf
    rw [Submodule.mem_iInf] at hf
    exact mem_centralSoninCarrier_of_ae_zero
      (eventually_zero_on_centralInterval_of_mem_all_lt hf)
      (eventually_fourier_zero_on_centralInterval_of_mem_all_lt hf)
  · exact le_iInf fun b => centralSoninCarrier_antitone (le_of_lt b.2)

/-- Strong continuity of the Sonin projection from smaller apertures. -/
theorem tendsto_centralSoninProjection_apply_nhdsLT (a : ℝ) (g : SoninL2) :
    Tendsto (fun b : ℝ => centralSoninProjection b g) (𝓝[<] a)
      (𝓝 (centralSoninProjection a g)) := by
  rw [← tendsto_comp_coe_Iio_atTop]
  have hanti : Antitone (fun b : Set.Iio a => centralSoninCarrier b.1) := by
    intro b c hbc
    exact centralSoninCarrier_antitone hbc
  letI : (⨅ b : Set.Iio a, centralSoninCarrier b.1).HasOrthogonalProjection := by
    rw [iInf_lt_centralSoninCarrier]
    infer_instance
  have h := starProjection_tendsto_iInf_of_antitone
    (fun b : Set.Iio a => centralSoninCarrier b.1) hanti g
  have hproj : (⨅ b : Set.Iio a, centralSoninCarrier b.1).starProjection g =
      (centralSoninCarrier a).starProjection g :=
    starProjection_congr (iInf_lt_centralSoninCarrier a) g
  rw [hproj] at h
  simpa [centralSoninProjection] using h

/-- Strong continuity of the Sonin projection from larger apertures. -/
theorem tendsto_centralSoninProjection_apply_nhdsGT
    (a : ℝ) (ha : 0 < a) (g : SoninL2) :
    Tendsto (fun b : ℝ => centralSoninProjection b g) (𝓝[>] a)
      (𝓝 (centralSoninProjection a g)) := by
  rw [← tendsto_comp_coe_Ioi_atBot]
  let U : (Set.Ioi a)ᵒᵈ → Submodule ℂ SoninL2 :=
    fun b => centralSoninCarrier b.1
  have hmono : Monotone U := by
    intro b c hbc
    exact centralSoninCarrier_antitone hbc
  have h := Submodule.starProjection_tendsto_closure_iSup U hmono g
  have hclosure : (⨆ b, U b).topologicalClosure = centralSoninCarrier a := by
    change (⨆ b : (Set.Ioi a)ᵒᵈ, centralSoninCarrier b.1).topologicalClosure =
      centralSoninCarrier a
    exact topologicalClosure_iSup_centralSoninCarrier a ha
  have hproj : (⨆ b, U b).topologicalClosure.starProjection g =
      (centralSoninCarrier a).starProjection g :=
    starProjection_congr hclosure g
  rw [hproj] at h
  change Tendsto
    (fun x : (Set.Ioi a)ᵒᵈ => (centralSoninCarrier x.1).starProjection g)
    atTop (𝓝 ((centralSoninCarrier a).starProjection g))
  simpa [U] using h

/-- The actual Sonin projection is strongly continuous at every positive aperture. -/
theorem continuousAt_centralSoninProjection_apply
    {a : ℝ} (ha : 0 < a) (g : SoninL2) :
    ContinuousAt (fun b : ℝ => centralSoninProjection b g) a := by
  rw [continuousAt_iff_continuous_left'_right']
  exact ⟨tendsto_centralSoninProjection_apply_nhdsLT a g,
    tendsto_centralSoninProjection_apply_nhdsGT a ha g⟩

/-- The actual Sonin projection is strongly continuous on positive apertures. -/
theorem continuousOn_centralSoninProjection_apply (g : SoninL2) :
    ContinuousOn (fun a : ℝ => centralSoninProjection a g) (Set.Ioi 0) := by
  intro a ha
  exact (continuousAt_centralSoninProjection_apply ha g).continuousWithinAt

end RHTower
