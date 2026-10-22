import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.FormRow96Sign
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open scoped BigOperators
open HTGeometry.EvenCompactBernstein


theorem boundaryBernstein77_clock_one (f : ℕ → ℕ → ℝ) (v : ℝ) :
    boundaryBernstein77 f 1 v=
      ∑ B ∈ Finset.range 37, f 96 B*unscaledBernstein 36 B v := by
  unfold boundaryBernstein77
  rw [Finset.sum_eq_single 96]
  · simp [unscaledBernstein]
  · intro A hA hne
    have hAlt : A<96 := by have := Finset.mem_range.mp hA; omega
    have he : 96-A≠0 := by omega
    simp [unscaledBernstein,he]
  · norm_num

theorem boundaryRegularCore77_clock_face_unit_pos {v : ℝ}
    (hv0 : 0≤v) (hv1 : v≤1) :
    0<boundaryRegularCore77 boundaryH77 (boundaryS77*v) := by
  have he := boundaryFullCoefficient77_reconstruction 1 v
  rw [boundaryBernstein77_clock_one] at he
  simp only [mul_one] at he
  rw [←he]
  apply Finset.sum_pos'
  · intro B hB
    have hc := boundaryFullCoefficient77_row96_pos ⟨B,Finset.mem_range.mp hB⟩
    have hw : 0≤unscaledBernstein 36 B v :=
      mul_nonneg (pow_nonneg hv0 _) (pow_nonneg (sub_nonneg.mpr hv1) _)
    exact mul_nonneg hc.le hw
  · by_cases hv : v=1
    · refine ⟨36,by norm_num,?_⟩
      simpa [hv,unscaledBernstein] using
        (boundaryFullCoefficient77_row96_pos ⟨36,by norm_num⟩)
    · refine ⟨0,by norm_num,?_⟩
      have hp : 0<1-v := by
        have hvlt : v<1 := by
          by_contra hn
          have he : v=1 := by linarith
          exact hv he
        linarith
      have hc := boundaryFullCoefficient77_row96_pos ⟨0,by norm_num⟩
      simpa [unscaledBernstein] using mul_pos hc (pow_pos hp 36)

theorem boundaryRegularCore77_clock_face_pos {s : ℝ}
    (hs0 : 0≤s) (hs1 : s≤boundaryS77) :
    0<boundaryRegularCore77 boundaryH77 s := by
  have hS : 0<boundaryS77 := by norm_num [boundaryS77]
  have hv0 : 0≤s/boundaryS77 := div_nonneg hs0 hS.le
  have hv1 : s/boundaryS77≤1 := by
    apply (div_le_iff₀ hS).mpr
    simpa using hs1
  have hp := boundaryRegularCore77_clock_face_unit_pos hv0 hv1
  have he : boundaryS77*(s/boundaryS77)=s := by field_simp [hS.ne']
  rw [he] at hp
  exact hp

end
end HTGeometry.ThetaRatioInfinity
