import GaloisForLFunctions.RHTower.SoninExtendedMellinExtension
import GaloisForLFunctions.RHTower.MellinHeadHardy

/-!
# Burnol's Proposition 2.2, right half-plane

A vector `f` of the extended Sonine space `L_a` is constant on the band, so its Mellin integral
splits as

`∫_0^∞ f(t) t^{-s} dt = c·a^{1-s}/(1-s) + ∫_a^∞ f(t) t^{-s} dt`   (`1/2 < Re s < 1`),

where `c` is the physical head.  The tail continues holomorphically to the whole half-plane
`Re s > 0` (`SoninExtendedMellinExtension`), so multiplying by `1 - s` produces a *holomorphic*
function on `Re s > 0`: the Mellin transform of a vector of `L_a` is meromorphic there with at most
a simple pole at `s = 1`, and no other singularity.

## Main results

* `ae_eq_of_mem_extended` — the physical head constant
* `integrableOn_extendedMellin_Ioi_zero` — absolute convergence on `1/2 < Re s < 1`
* `exists_extendedMellin_pole_normalised` — **Burnol's Proposition 2.2 on `Re s > 0`**
-/

noncomputable section

open MeasureTheory Set Filter Topology

open scoped InnerProductSpace

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem ae_eq_of_mem_extended {a : ℝ} {f : SoninL2}
    (hf : f ∈ centralSoninExtendedCarrier a) :
    ∃ c : ℂ, ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = c :=
  (mem_orthogonal_meanZeroBand_iff a f).1 (mem_orthogonal_meanZeroBand_of_mem_extended hf)

theorem integrableOn_head_cpow {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : s.re < 1) (c : ℂ) :
    IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * c) (Ioc (0 : ℝ) a) volume := by
  have hr : -1 < (-s).re := by
    rw [Complex.neg_re]
    linarith
  have h := (intervalIntegral.intervalIntegrable_cpow' (a := (0 : ℝ)) (b := a) hr).1
  exact h.mul_const c

theorem integrableOn_head_of_mem_extended {a : ℝ} (ha : 0 < a) {f : SoninL2} {c : ℂ}
    (hc : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = c)
    {s : ℂ} (hs : s.re < 1) :
    IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t) (Ioc (0 : ℝ) a) volume := by
  refine (integrableOn_head_cpow ha hs c).congr ?_
  filter_upwards [ae_restrict_of_ae hc, ae_restrict_mem measurableSet_Ioc] with t ht hmem
  have hband : t ∈ centralInterval a := by
    rw [centralInterval, Set.mem_Icc]
    exact ⟨by linarith [hmem.1, ha], hmem.2⟩
  rw [ht hband]

theorem integral_head_of_mem_extended {a : ℝ} (ha : 0 < a) {f : SoninL2} {c : ℂ}
    (hc : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = c)
    {s : ℂ} (hs : s.re < 1) :
    (∫ t in Ioc (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t)
      = c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) / (1 - s) := by
  rw [← integral_head_cpow_Ioc ha hs c]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hc, ae_restrict_mem measurableSet_Ioc] with t ht hmem
  have hband : t ∈ centralInterval a := by
    rw [centralInterval, Set.mem_Icc]
    exact ⟨by linarith [hmem.1, ha], hmem.2⟩
  rw [ht hband]

theorem integral_split_extendedMellin {a : ℝ} (ha : 0 < a) {f : SoninL2} {c : ℂ}
    (hc : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = c)
    {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s.re < 1) :
    (∫ t in Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t)
      = c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) / (1 - s)
        + ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t := by
  have h1 := integrableOn_head_of_mem_extended ha hc hs1 (s := s)
  have h2 := integrableOn_cpow_mul_Ioi ha f hs
  have hunion : Set.Ioc (0 : ℝ) a ∪ Set.Ioi a = Set.Ioi (0 : ℝ) := Set.Ioc_union_Ioi_eq_Ioi ha.le
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) a) (Set.Ioi a) := Set.Ioc_disjoint_Ioi le_rfl
  rw [← hunion, setIntegral_union hdisj measurableSet_Ioi h1 h2,
    integral_head_of_mem_extended ha hc hs1]

/-- **Burnol's Proposition 2.2 on the right half-plane.**  For a vector of the extended Sonine
space the product `(1-s)·M(f)(s)` extends holomorphically to `Re s > 0`, so `M(f)` is meromorphic
there with at most a simple pole, located at `s = 1`. -/
theorem exists_extendedMellin_pole_normalised {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ centralSoninExtendedCarrier a) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 0 < s.re} ∧
      ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
        (1 - s) * ∫ t in Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t = G s := by
  obtain ⟨c, hc⟩ := ae_eq_of_mem_extended hf
  obtain ⟨F, hFdiff, hFeq⟩ := exists_differentiableOn_extendedTailMellin ha hf
  have hane : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  refine ⟨fun s => c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) + (1 - s) * F s, ?_, ?_⟩
  · refine DifferentiableOn.add ?_ ?_
    · refine DifferentiableOn.const_mul ?_ c
      intro s _
      refine DifferentiableAt.differentiableWithinAt ?_
      exact DifferentiableAt.const_cpow
        ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id) (Or.inl hane)
    · exact (((differentiable_const (1 : ℂ)).sub differentiable_id).differentiableOn).mul hFdiff
  · intro s hs hs1
    have hne : (1 : ℂ) - s ≠ 0 := by
      intro h
      have hre : ((1 : ℂ) - s).re = 0 := by rw [h]; simp
      rw [Complex.sub_re, Complex.one_re] at hre
      linarith
    simp only
    rw [integral_split_extendedMellin ha hc hs hs1, ← hFeq s hs]
    field_simp

end RHTower

end
