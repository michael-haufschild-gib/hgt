import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WeilEnergyIsUnboundedAtEveryAperture

/-!
# Finite readings and exact source mass do not supply Bézout

Unit-mass Weil energy is unbounded in every finite-dimensional linear reading kernel.
Consequently no arbitrary nonlinear function of those readings and the exact L² mass can
serve as a Bézout source reserve. The obstruction applies even to the strict source cone.
-/

noncomputable section
open MeasureTheory

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Fixing source mass to one does not bound Weil energy on any finite reading kernel. -/
theorem exists_realTestAt_unit_mass_in_ker_weilPair_gt {r : ℝ} (hr : 0 < r) (M : ℝ)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : realTestsAt r →ₗ[ℝ] V) :
    ∃ f : realTestsAt r, (∫ u : ℝ, f.1.1 u ^ 2) = 1 ∧
      L f = 0 ∧ M < weilPair f.1.1 f.1.1 := by
  obtain ⟨f, hm, hW, hker⟩ := exists_realTestAt_in_ker_weilPair_gt_mul_integral_sq hr M L
  let m := ∫ u : ℝ, f.1.1 u ^ 2
  have hm' : 0 < m := hm
  let t := Real.sqrt (1 / m)
  have ht2 : t ^ 2 = 1 / m := Real.sq_sqrt (by positivity)
  have htpos : 0 < t ^ 2 := by rw [ht2]; positivity
  have htm : t ^ 2 * m = 1 := by rw [ht2]; field_simp [hm'.ne']
  refine ⟨t • f, ?_, ?_, ?_⟩
  · have he : (fun u : ℝ => ((t • f).1.1 u) ^ 2) =
        fun u : ℝ => t ^ 2 * f.1.1 u ^ 2 := by
      funext u
      change (t * f.1.1 u) ^ 2 = _
      ring
    rw [he, integral_const_mul]
    exact htm
  · rw [map_smul, hker, smul_zero]
  · have hscaled := mul_lt_mul_of_pos_left hW htpos
    have hleft : t ^ 2 * (M * m) = M := by
      calc
        _ = M * (t ^ 2 * m) := by ring
        _ = M := by rw [htm, mul_one]
    change t ^ 2 * (M * m) < t ^ 2 * weilPair f.1.1 f.1.1 at hscaled
    rw [hleft] at hscaled
    change M < weilPair (t • f.1.1) (t • f.1.1)
    rw [weilPair_smul_left, weilPair_comm f.1.1 (t • f.1.1), weilPair_smul_left]
    nlinarith only [hscaled]

/-- An arbitrary nonlinear mass-and-reading reserve still admits a strict effective negative square. -/
theorem exists_strictSourceCone_finite_readings_and_mass_negative_square
    {r : ℝ} (hr : 0 < r)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : realTestsAt r →ₗ[ℝ] V) (F : V → ℝ → ℝ) :
    ∃ x ∈ (scalingSubsurface (realTestsAt r)).strictSourceCone
        (fun y => F (L y.2.2) (∫ u : ℝ, y.2.2.1.1 u ^ 2)),
      (scalingSubsurface (realTestsAt r)).pair x x < 0 := by
  let S := scalingSubsurface (realTestsAt r)
  let Φ : (ℝ × ℝ × realTestsAt r) → ℝ :=
    fun y => F (L y.2.2) (∫ u : ℝ, y.2.2.1.1 u ^ 2)
  let c := max (F 0 1) 0 + 1
  have hc : 0 < c := by dsimp only [c]; linarith only [le_max_right (F 0 1) 0]
  have hFc : F 0 1 < c := by dsimp only [c]; linarith only [le_max_left (F 0 1) 0]
  have hfib (x : ℝ × ℝ × realTestsAt r) (a b : ℝ) :
      Φ (x + a • S.H + b • S.V) = Φ x := by
    have hs : (x + a • S.H + b • S.V).2.2 = x.2.2 := by
      change x.2.2 + a • (0 : realTestsAt r) + b • 0 = x.2.2
      simp only [smul_zero, add_zero]
    simp only [Φ, hs]
  obtain ⟨f, hm, hker, hW⟩ := exists_realTestAt_unit_mass_in_ker_weilPair_gt hr c L
  have hΦ : Φ (0, 0, f) = F 0 1 := by
    dsimp only [Φ]
    rw [hker, hm]
  let x := S.withFibreDegrees (0, 0, f) c (1 / 2)
  refine ⟨x, ?_, ?_⟩
  · change x ∈ S.strictSourceCone Φ
    rw [S.mem_strictSourceCone_iff]
    dsimp only [x]
    rw [S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V,
      S.source_withFibreDegrees hfib, hΦ, S.polar_self,
      S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V]
    exact ⟨hc, by positivity, by linarith only [hFc]⟩
  · change S.pair x x < 0
    dsimp only [x]
    rw [S.pair_withFibreDegrees, scalingSubsurface_defect_self]
    linarith only [hW]

/-- Exact source mass plus finitely many linear readings cannot supply Bézout in any source-cone variant. -/
theorem finite_readings_and_mass_sourceCones_not_bezout {r : ℝ} (hr : 0 < r)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : realTestsAt r →ₗ[ℝ] V) (F : V → ℝ → ℝ) :
    let S := scalingSubsurface (realTestsAt r)
    let Φ := fun y : ℝ × ℝ × realTestsAt r => F (L y.2.2) (∫ u : ℝ, y.2.2.1.1 u ^ 2)
    ¬ S.BezoutAxiom (S.sourceCone Φ) ∧ ¬ S.BezoutAxiom (S.strictSourceCone Φ) ∧
      ¬ S.BezoutAxiom (S.gradedSourceCone Φ) := by
  dsimp only
  obtain ⟨x, hx, hxx⟩ := exists_strictSourceCone_finite_readings_and_mass_negative_square hr L F
  have hx' := (scalingSubsurface (realTestsAt r)).strictSourceCone_subset_sourceCone _ hx
  have hxg := (scalingSubsurface (realTestsAt r)).sourceCone_subset_gradedSourceCone _ hx'
  exact ⟨fun hB => (not_lt_of_ge (hB x hx' x hx')) hxx,
    fun hB => (not_lt_of_ge (hB x hx x hx)) hxx,
    fun hB => (not_lt_of_ge (hB x hxg x hxg)) hxx⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

