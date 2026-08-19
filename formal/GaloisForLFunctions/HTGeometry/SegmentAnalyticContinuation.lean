import Mathlib

/-!
# Analytic continuation along a real segment

If two functions are analytic on an open set containing a real segment and agree near its left
endpoint, they agree near its right endpoint.  The witness is the convex tube
`⋃_{t ∈ [a,b]} B(t, η)`, which is a *convex* open subset of the ambient open set for small `η` by
compactness, so the identity theorem applies to it directly.
-/

open Metric Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The open tube of radius `η` around the real segment `[a, b]`. -/
def realTube (a b η : ℝ) : Set ℂ := ⋃ t ∈ Set.Icc a b, Metric.ball ((t : ℝ) : ℂ) η

theorem isOpen_realTube (a b η : ℝ) : IsOpen (realTube a b η) :=
  isOpen_biUnion fun _ _ => Metric.isOpen_ball

theorem mem_realTube_iff {a b η : ℝ} {z : ℂ} :
    z ∈ realTube a b η ↔ ∃ t ∈ Set.Icc a b, ‖z - (t : ℂ)‖ < η := by
  simp [realTube, Metric.mem_ball, Complex.dist_eq]

theorem real_mem_realTube {a b η : ℝ} (hη : 0 < η) {t : ℝ} (ht : t ∈ Set.Icc a b) :
    ((t : ℝ) : ℂ) ∈ realTube a b η :=
  mem_realTube_iff.mpr ⟨t, ht, by simpa using hη⟩

theorem convex_realTube (a b η : ℝ) : Convex ℝ (realTube a b η) := by
  intro z hz w hw p q hp hq hpq
  obtain ⟨s, hs, hsz⟩ := mem_realTube_iff.mp hz
  obtain ⟨t, ht, htw⟩ := mem_realTube_iff.mp hw
  refine mem_realTube_iff.mpr ⟨p * s + q * t, ?_, ?_⟩
  · constructor
    · have h1 : a = p * a + q * a := by rw [← add_mul, hpq, one_mul]
      rw [h1]
      exact add_le_add (mul_le_mul_of_nonneg_left hs.1 hp) (mul_le_mul_of_nonneg_left ht.1 hq)
    · have h1 : b = p * b + q * b := by rw [← add_mul, hpq, one_mul]
      rw [h1]
      exact add_le_add (mul_le_mul_of_nonneg_left hs.2 hp) (mul_le_mul_of_nonneg_left ht.2 hq)
  · have hsplit : (p • z + q • w) - (((p * s + q * t : ℝ)) : ℂ)
        = (p : ℂ) * (z - (s : ℂ)) + (q : ℂ) * (w - (t : ℂ)) := by
      simp only [Complex.real_smul]
      push_cast
      ring
    rw [hsplit]
    refine lt_of_le_of_lt (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hp, abs_of_nonneg hq]
    rcases eq_or_lt_of_le hp with hp0 | hp0
    · rw [← hp0]
      have hq1 : q = 1 := by linarith
      rw [hq1]
      simpa using htw
    · rcases eq_or_lt_of_le hq with hq0 | hq0
      · rw [← hq0]
        have hp1 : p = 1 := by linarith
        rw [hp1]
        simpa using hsz
      · have h1 : p * ‖z - (s : ℂ)‖ < p * η := by nlinarith
        have h2 : q * ‖w - (t : ℂ)‖ < q * η := by nlinarith
        calc p * ‖z - (s : ℂ)‖ + q * ‖w - (t : ℂ)‖ < p * η + q * η := add_lt_add h1 h2
          _ = η := by rw [← add_mul, hpq, one_mul]

theorem exists_realTube_subset {V : Set ℂ} (hV : IsOpen V) {a b : ℝ}
    (hseg : ∀ t : ℝ, t ∈ Set.Icc a b → ((t : ℝ) : ℂ) ∈ V) :
    ∃ η > 0, realTube a b η ⊆ V := by
  classical
  set K : Set ℂ := (fun t : ℝ => (t : ℂ)) '' (Set.Icc a b) with hK
  have hKcomp : IsCompact K := (isCompact_Icc).image (by fun_prop)
  have hKV : K ⊆ V := by
    rintro _ ⟨t, ht, rfl⟩
    exact hseg t ht
  obtain ⟨δ, hδ, hsub⟩ := hKcomp.exists_thickening_subset_open hV hKV
  refine ⟨δ, hδ, fun z hz => ?_⟩
  obtain ⟨t, ht, hzt⟩ := mem_realTube_iff.mp hz
  refine hsub ?_
  rw [Metric.mem_thickening_iff]
  exact ⟨(t : ℂ), ⟨t, ht, rfl⟩, by rwa [Complex.dist_eq]⟩

/-- **Analytic continuation along a real segment.**  Two functions analytic on an open set
containing `[a,b] ⊆ ℝ ⊆ ℂ` and agreeing near `a` agree near `b`. -/
theorem eventuallyEq_of_segment {V : Set ℂ} (hV : IsOpen V) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f V) (hg : AnalyticOnNhd ℂ g V) {a b : ℝ} (hab : a ≤ b)
    (hseg : ∀ t : ℝ, t ∈ Set.Icc a b → ((t : ℝ) : ℂ) ∈ V)
    (hagree : f =ᶠ[nhds ((a : ℝ) : ℂ)] g) :
    f =ᶠ[nhds ((b : ℝ) : ℂ)] g := by
  obtain ⟨η, hη, hsub⟩ := exists_realTube_subset hV hseg
  have hTopen : IsOpen (realTube a b η) := isOpen_realTube a b η
  have hTconn : IsPreconnected (realTube a b η) := (convex_realTube a b η).isPreconnected
  have haT : ((a : ℝ) : ℂ) ∈ realTube a b η := real_mem_realTube hη ⟨le_rfl, hab⟩
  have hbT : ((b : ℝ) : ℂ) ∈ realTube a b η := real_mem_realTube hη ⟨hab, le_rfl⟩
  have hEq : Set.EqOn f g (realTube a b η) :=
    (hf.mono hsub).eqOn_of_preconnected_of_eventuallyEq (hg.mono hsub) hTconn haT hagree
  filter_upwards [hTopen.mem_nhds hbT] with w hw
  exact hEq hw

end

end GaloisForLFunctions.HTGeometry
