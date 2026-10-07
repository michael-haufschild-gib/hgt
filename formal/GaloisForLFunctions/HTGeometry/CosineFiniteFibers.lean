import GaloisForLFunctions.HTGeometry.CosineFiniteSequence
import GaloisForLFunctions.HTGeometry.CosineQuadraticLattice

/-! # Off-integer cosine intersections with a finite coordinate and a pole

The finite coordinate has a ramified analytic cosine inverse, including
critical values. The conic branch gives actual source points. Their exact
quadratic correction tends to zero but is eventually nonzero, so closed
integer-lattice stabilization excludes eventual integer containment.
-/

namespace GaloisForLFunctions.HTGeometry.CosineFiniteFibers

open Complex Filter LabeledCosineDescent
open CosineFiniteCorner CosineFiniteSequence
open scoped Topology

noncomputable section

theorem exists_off_integer_cosine_pair {f B : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hnc : ∀ c : ℂ, ¬ ∀ᶠ s in 𝓝 (0 : ℂ), f s = c)
    (hB : AnalyticAt ℂ B 0) (hB0 : B 0 ≠ 0) (m : ℕ) (hm : 0 < m) :
    ∃ s w : ℕ → ℂ, Tendsto s atTop (𝓝 0) ∧ (∀ n, s n ≠ 0) ∧
      (∀ᶠ n in atTop, source (w n) = f (s n ^ 2) ∧
        source (-w n) = B (s n ^ 2) / s n ^ (2 * m)) ∧
      (¬ ∀ᶠ n in atTop, w n ∈ Set.range (Int.cast : ℤ → ℂ)) ∧
      (∀ E : Finset ℂ, ∀ᶠ n in atTop, w n ∉ E) ∧
      (∀ E : Finset ℂ, ∀ᶠ n in atTop, source (-w n) ∉ E) := by
  obtain ⟨u, H, k, hu, hH, hH0, hk, hcos, hfact⟩ :=
    CosineRamifiedInverse.exists_nonconstant_cosine_inverse hf hnc
  let M := 2 * m
  have hM : 0 < M := by dsimp [M]; omega
  have hsquare : AnalyticAt ℂ (fun s : ℂ => s ^ 2) 0 := analyticAt_id.pow 2
  have hB' : AnalyticAt ℂ B ((0 : ℂ) ^ 2) := by simpa using hB
  have hB2 : AnalyticAt ℂ (fun s : ℂ => B (s ^ 2)) 0 :=
    hB'.comp (f := fun s : ℂ => s ^ 2) hsquare
  obtain ⟨β, hβ, _, hβeq⟩ := CosinePoleUnit.exists_logarithmic_unit hB2
    (by simpa using hB0) M hM
  obtain ⟨ell, hell, _, heq⟩ := CosineFiniteCorner.exists_corner hu hβ M hM
    CosineCornerMarker.conicConstant
  let s := smallSequence M ell
  let w := fun n : ℕ => squareCoordinate (firstLift u M n (ell (parameters M n)))
  have hs : Tendsto s atTop (𝓝 0) := smallSequence_limit hM hell
  have hs0 : ∀ n, s n ≠ 0 := fun n => smallSequence_ne_zero M n ell
  have hpair : ∀ᶠ n in atTop, source (w n) = f (s n ^ 2) ∧
      source (-w n) = B (s n ^ 2) / s n ^ (2 * m) := by
    filter_upwards [hs.eventually hcos, hs.eventually hβeq,
      (parameters_limit M hM).eventually heq, eventually_gt_atTop (0 : ℕ)]
      with n hcn hβn hen hn
    have hconic := CosineFiniteCorner.conic_of_equation hn hen
    constructor
    · change source (squareCoordinate _) = _
      rw [source_squareCoordinate, firstLift_cos]
      exact hcn
    · change source (-squareCoordinate _) = _
      rw [CosineCornerCoordinates.reflected_source hconic]
      exact CosinePoleUnit.cosine_of_unit_equation (hs0 n) (exp_ne_zero _) hβn
        (secondLift_exp β M n hM (ell (parameters M n)))
  have hflat := scaled_germ_displacement_limit hH hk hfact hs (scaled_smallSequence_limit hM hell)
  have hcorr := correction_limit hu hs hflat
  have hcorrne := correction_eventually_ne_zero hu hH hH0 hfact hs hs0
  have hw : Tendsto (fun n : ℕ => (n : ℂ)⁻¹ ^ 2 * w n) atTop (𝓝 27) :=
    point_scaled_limit hu hs
  refine ⟨s, w, hs, hs0, hpair, ?_, ?_, ?_⟩
  · intro hint
    have hpoly : ∀ᶠ (n : ℕ) in atTop,
        27 * (n : ℂ) ^ 2 + (27 * u 0 / Real.pi) * n +
          (27 * u 0 ^ 2 / (4 * (Real.pi : ℂ) ^ 2) - 1 / 12) + correction u s n ∈
          Set.range (Int.cast : ℤ → ℂ) := by
      filter_upwards [hint] with n hn
      rw [← point_decomposition]
      exact hn
    have hz := CosineQuadraticLattice.eventually_zero_of_quadratic_integer_values
      27 (27 * u 0 / Real.pi) (27 * u 0 ^ 2 / (4 * (Real.pi : ℂ) ^ 2) - 1 / 12)
      hcorr hpoly
    obtain ⟨n, hn0, hnne⟩ := (hz.and hcorrne).exists
    exact hnne hn0
  · exact CosineTwoPoleSequence.eventually_avoids_finite_of_scaled_limit
      (by simpa using CosineCornerSequence.inverse_parameter_limit.pow 2) hw (by norm_num)
  · have hy : Tendsto (fun n => s n ^ M * source (-w n)) atTop (𝓝 (B 0)) := by
      have hlim : Tendsto (fun n => B (s n ^ 2)) atTop (𝓝 (B 0)) := by
        convert! hB2.continuousAt.tendsto.comp hs using 1
        simp
      apply hlim.congr'
      filter_upwards [hpair] with n hn
      rw [hn.2]
      change B (s n ^ 2) = s n ^ M * (B (s n ^ 2) / s n ^ M)
      rw [mul_div_cancel₀ _ (pow_ne_zero M (hs0 n))]
    exact CosineTwoPoleSequence.eventually_avoids_finite_of_scaled_limit
      (by simpa [Nat.ne_zero_of_lt hM] using hs.pow M) hy hB0

end

end GaloisForLFunctions.HTGeometry.CosineFiniteFibers
