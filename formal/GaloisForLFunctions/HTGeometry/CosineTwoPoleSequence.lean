import GaloisForLFunctions.HTGeometry.CosineTwoPoleCorner
import GaloisForLFunctions.HTGeometry.CosineCornerSequence

/-! # Nonreal intersections along an arbitrary two-pole analytic branch

The general logarithmic conic branch yields actual reflected-cosine values.
Its scaled source points have nonzero imaginary limit, and both the source
points and their first cosine coordinates eventually avoid every finite set.
Only exact identities and qualitative topological limits are used.
-/

namespace GaloisForLFunctions.HTGeometry.CosineTwoPoleSequence

open Complex Filter LabeledCosineDescent CosineTwoPoleCorner
open scoped Topology

noncomputable section

theorem parameters_limit : Tendsto CosineTwoPoleCorner.parameters atTop (𝓝 (0, 0)) :=
  CosineCornerSequence.parameters_limit

theorem small_limit {ell : ℂ × ℂ → ℂ} (h : AnalyticAt ℂ ell (0, 0)) :
    Tendsto (fun n => small (CosineTwoPoleCorner.parameters n, ell (CosineTwoPoleCorner.parameters n)))
      atTop (𝓝 0) := by
  have he := Complex.continuous_exp.continuousAt.tendsto.comp
    (h.continuousAt.tendsto.comp parameters_limit)
  simpa [small, CosineTwoPoleCorner.parameters, CosineCornerCoordinates.exponentialParameter] using
    CosineCornerSequence.exponential_parameter_limit.mul he

theorem argument_limit {α : ℂ → ℂ} {ell : ℂ × ℂ → ℂ}
    (hα : AnalyticAt ℂ α 0) (hell : AnalyticAt ℂ ell (0, 0)) (m : ℕ) :
    Tendsto (fun n => argument α m
      (CosineTwoPoleCorner.parameters n, ell (CosineTwoPoleCorner.parameters n))) atTop
      (𝓝 (argument α m ((0, 0), ell (0, 0)))) := by
  exact (argument_analyticAt hα m (ell (0, 0))).continuousAt.tendsto.comp
    (parameters_limit.prodMk_nhds (hell.continuousAt.tendsto.comp parameters_limit))

theorem firstLift_scaled_limit {α : ℂ → ℂ} {ell : ℂ × ℂ → ℂ}
    (hα : AnalyticAt ℂ α 0) (hell : AnalyticAt ℂ ell (0, 0)) (m r : ℕ) :
    Tendsto (fun n : ℕ => (n : ℂ)⁻¹ * firstLift α m r n (ell (CosineTwoPoleCorner.parameters n)))
      atTop (𝓝 (direction m r)) := by
  have ht := CosineCornerSequence.inverse_parameter_limit
  have hu := argument_limit hα hell m
  have hlim : Tendsto (fun n : ℕ => direction m r + (n : ℂ)⁻¹ *
      argument α m (CosineTwoPoleCorner.parameters n, ell (CosineTwoPoleCorner.parameters n)))
      atTop (𝓝 (direction m r)) := by
    simpa using tendsto_const_nhds.add (ht.mul hu)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hn
  simp only [firstLift, mul_add, ← mul_assoc, inv_mul_cancel₀ hn', one_mul]

theorem scaled_squareCoordinate (t U : ℂ) :
    t ^ 2 * squareCoordinate U =
      27 * (t * U) ^ 2 / (4 * (Real.pi : ℂ) ^ 2) - t ^ 2 / 12 := by
  dsimp [squareCoordinate]
  ring

theorem direction_scaled_square (m r : ℕ) :
    27 * direction m r ^ 2 / (4 * (Real.pi : ℂ) ^ 2) =
      27 * ((r : ℂ) - I * m) ^ 2 := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  dsimp [direction]
  field_simp
  ring

theorem point_scaled_limit {α : ℂ → ℂ} {ell : ℂ × ℂ → ℂ}
    (hα : AnalyticAt ℂ α 0) (hell : AnalyticAt ℂ ell (0, 0)) (m r : ℕ) :
    Tendsto (fun n : ℕ => (n : ℂ)⁻¹ ^ 2 *
      squareCoordinate (firstLift α m r n (ell (CosineTwoPoleCorner.parameters n))))
      atTop (𝓝 (27 * ((r : ℂ) - I * m) ^ 2)) := by
  simp_rw [scaled_squareCoordinate]
  rw [← direction_scaled_square m r]
  convert (((tendsto_const_nhds.mul ((firstLift_scaled_limit hα hell m r).pow 2)).div_const
    (4 * (Real.pi : ℂ) ^ 2)).sub
    ((CosineCornerSequence.inverse_parameter_limit.pow 2).div_const 12)) using 1
  simp

theorem direction_scaled_square_im (m r : ℕ) :
    (27 * ((r : ℂ) - I * m) ^ 2).im = -54 * (m : ℝ) * r := by
  simp [pow_two]
  ring

theorem eventually_nonreal {w : ℕ → ℂ} {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hw : Tendsto (fun n : ℕ => (n : ℂ)⁻¹ ^ 2 * w n)
      atTop (𝓝 (27 * ((r : ℂ) - I * m) ^ 2))) :
    ∀ᶠ n in atTop, (w n).im ≠ 0 := by
  have hi := Complex.continuous_im.continuousAt.tendsto.comp hw
  have hn : (27 * ((r : ℂ) - I * m) ^ 2).im ≠ 0 := by
    rw [direction_scaled_square_im]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Nat.ne_zero_of_lt hm))
      (by exact_mod_cast Nat.ne_zero_of_lt hr)
  filter_upwards [hi.eventually_ne hn] with n hn'
  intro hz
  exact hn' (by simp [mul_im, pow_two, hz])

theorem eventually_avoids_finite_of_scaled_limit {s w : ℕ → ℂ} {L : ℂ}
    (hs : Tendsto s atTop (𝓝 0)) (hw : Tendsto (fun n => s n * w n) atTop (𝓝 L))
    (hL : L ≠ 0) (B : Finset ℂ) : ∀ᶠ n in atTop, w n ∉ B := by
  have hone (b : ℂ) : ∀ᶠ n in atTop, w n ≠ b := by
    have ht : Tendsto (fun n => s n * w n - s n * b) atTop (𝓝 L) := by
      simpa using hw.sub (hs.mul_const b)
    filter_upwards [ht.eventually_ne hL] with n hn
    intro hb
    exact hn (by rw [hb, sub_self])
  have hall := (Finset.eventually_all B).mpr (fun b _ => hone b)
  filter_upwards [hall] with n hn
  intro hb
  exact hn (w n) hb rfl

theorem exists_nonreal_cosine_pair {A B : ℂ → ℂ}
    (hA : AnalyticAt ℂ A 0) (hA0 : A 0 ≠ 0)
    (hB : AnalyticAt ℂ B 0) (hB0 : B 0 ≠ 0)
    (m r : ℕ) (hm : 0 < m) (hr : 0 < r) :
    ∃ s w : ℕ → ℂ, Tendsto s atTop (𝓝 0) ∧ (∀ n, s n ≠ 0) ∧
      (∀ᶠ n in atTop, source (w n) = A (s n) / s n ^ m ∧
        source (-w n) = B (s n) / s n ^ r ∧ (w n).im ≠ 0) ∧
      (∀ E : Finset ℂ, ∀ᶠ n in atTop, w n ∉ E) ∧
      (∀ E : Finset ℂ, ∀ᶠ n in atTop, source (w n) ∉ E) := by
  obtain ⟨α, hα, _, hαeq⟩ := CosinePoleUnit.exists_logarithmic_unit hA hA0 m hm
  obtain ⟨β, hβ, _, hβeq⟩ := CosinePoleUnit.exists_logarithmic_unit hB hB0 r hr
  obtain ⟨ell, hell, _, heq⟩ := exists_corner hα hβ m r hr CosineCornerMarker.conicConstant
  let s := fun n => small (CosineTwoPoleCorner.parameters n, ell (CosineTwoPoleCorner.parameters n))
  let w := fun n => squareCoordinate (firstLift α m r n (ell (CosineTwoPoleCorner.parameters n)))
  have hs : Tendsto s atTop (𝓝 0) := small_limit hell
  have hs0 : ∀ n, s n ≠ 0 := fun n => small_parameters_ne_zero n _
  have hpair : ∀ᶠ n in atTop,
      source (w n) = A (s n) / s n ^ m ∧ source (-w n) = B (s n) / s n ^ r := by
    filter_upwards [hs.eventually hαeq, hs.eventually hβeq,
      parameters_limit.eventually heq, eventually_gt_atTop (0 : ℕ)] with n hAn hBn hen hn
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hn
    have hc : firstLift α m r n (ell (CosineTwoPoleCorner.parameters n)) ^ 2 +
        secondLift β m r n (ell (CosineTwoPoleCorner.parameters n)) ^ 2 =
        CosineCornerMarker.conicConstant := conic_of_equation hn' hen
    have hp := cosine_lifts hAn hBn
    constructor
    · change source (squareCoordinate _) = _
      rw [source_squareCoordinate]
      exact hp.1
    · change source (-squareCoordinate _) = _
      rw [CosineCornerCoordinates.reflected_source hc]
      exact hp.2
  have hw : Tendsto (fun n : ℕ => (n : ℂ)⁻¹ ^ 2 * w n) atTop
      (𝓝 (27 * ((r : ℂ) - I * m) ^ 2)) := point_scaled_limit hα hell m r
  have hL : 27 * ((r : ℂ) - I * m) ^ 2 ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    rw [direction_scaled_square_im] at hi
    have hn : -54 * (m : ℝ) * r ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Nat.ne_zero_of_lt hm))
        (by exact_mod_cast Nat.ne_zero_of_lt hr)
    exact hn hi
  refine ⟨s, w, hs, hs0, ?_, ?_, ?_⟩
  · filter_upwards [hpair, eventually_nonreal hm hr hw] with n hp hn
    exact ⟨hp.1, hp.2, hn⟩
  · exact eventually_avoids_finite_of_scaled_limit
      (by simpa using CosineCornerSequence.inverse_parameter_limit.pow 2) hw hL
  · have hx : Tendsto (fun n => s n ^ m * source (w n)) atTop (𝓝 (A 0)) := by
      apply (hA.continuousAt.tendsto.comp hs).congr'
      filter_upwards [hpair] with n hn
      rw [hn.1, mul_div_cancel₀ _ (pow_ne_zero m (hs0 n))]
      rfl
    exact eventually_avoids_finite_of_scaled_limit
      (by simpa [Nat.ne_zero_of_lt hm] using hs.pow m) hx hA0

end

end GaloisForLFunctions.HTGeometry.CosineTwoPoleSequence
