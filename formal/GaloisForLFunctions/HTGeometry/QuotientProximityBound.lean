/-
# The quotient proximity bound and subquadratic-logarithmic rigidity

Two value-distribution facts about entire quotients.

The first is submultiplicativity in the form needed for factorization arguments: if `G = H · F`
with all three entire, then `m(r, H) ≤ m(r, G) + m(r, F) + O(1)`.  The proof passes to the
characteristic — for entire functions the two agree — writes `H` as `G · F⁻¹` off the discrete zero
set of `F`, and pays the first main theorem's constant `T(r, F⁻¹) = T(r, F) + O(1)`.  No lower
bound on `|F|`, hence no minimum-modulus estimate, is involved.

The second turns a subquadratic-logarithmic proximity bound into constancy: for a zero-free entire
`h`, the Poisson bound gives `log |h(z)| ≤ 3 m(2(1+|z|))`, so an eventual bound
`m(R) ≤ (log R)²` yields `log |h(z)| ≤ B (log (2+|z|))²` after absorbing the compact range into the
constant, and Borel--Carathéodory plus a Cauchy estimate then force `h` to be constant.
-/
import GaloisForLFunctions.HTGeometry.NevanlinnaEntireCharacteristic
import GaloisForLFunctions.HTGeometry.PoissonKernelBound
import GaloisForLFunctions.HTGeometry.EntireLogarithm
import GaloisForLFunctions.HTGeometry.QuadraticSubtypeCanonicalDivisor

noncomputable section

open Filter Topology Metric ValueDistribution Asymptotics
open GaloisForLFunctions.Nevanlinna GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.QuotientProximity

theorem proximity_nonneg_of_entire {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F Set.univ) {r : ℝ}
    (hr : 1 ≤ r) : 0 ≤ proximity F ⊤ r := by
  have h := characteristic_nonneg (f := F) (a := (⊤ : WithTop ℂ)) hr
  rwa [characteristic_top_eq_proximity_of_analyticOnNhd hF] at h

/-- **The quotient proximity bound.**  For an entire quotient the proximity of `H = G/F` is
bounded by those of `G` and `F` up to one constant: submultiplicativity of the characteristic
together with the first main theorem `T(r, F⁻¹) = T(r, F) + O(1)`. -/
theorem proximity_quotient_le {F G H : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F Set.univ) (hG : AnalyticOnNhd ℂ G Set.univ)
    (hH : AnalyticOnNhd ℂ H Set.univ)
    (hFord : ∀ z, meromorphicOrderAt F z ≠ ⊤)
    (hGord : ∀ z, meromorphicOrderAt G z ≠ ⊤)
    (hfac : ∀ z, G z = H z * F z) :
    ∃ K : ℝ, ∀ r : ℝ, 1 ≤ r →
      proximity H ⊤ r ≤ proximity G ⊤ r + proximity F ⊤ r + K := by
  have hFmer : Meromorphic F := fun z => (hF z (Set.mem_univ z)).meromorphicAt
  have hGmer : Meromorphic G := fun z => (hG z (Set.mem_univ z)).meromorphicAt
  have hFinvmer : Meromorphic F⁻¹ := fun z => (hFmer z).inv
  have hFinvord : ∀ z, meromorphicOrderAt F⁻¹ z ≠ ⊤ := by
    intro z h
    rw [meromorphicOrderAt_inv] at h
    apply hFord z
    have hneg := congrArg (fun t => -t) h
    simpa using hneg
  have hcod : H =ᶠ[codiscrete ℂ] G * F⁻¹ := by
    have hne : ∀ᶠ x in codiscrete ℂ, F x ≠ 0 := by
      have hmerOn : MeromorphicOn F Set.univ := fun z _ => hFmer z
      have := MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero hmerOn
        (fun u _ => hFord u)
      simpa [Filter.codiscrete] using this
    filter_upwards [hne] with x hx
    rw [Pi.mul_apply, Pi.inv_apply, hfac x, mul_assoc, mul_inv_cancel₀ hx, mul_one]
  set K : ℝ := max |Real.log ‖F 0‖| |Real.log ‖meromorphicTrailingCoeffAt F 0‖| with hK
  refine ⟨K, fun r hr => ?_⟩
  have h1 : proximity H ⊤ r = characteristic (G * F⁻¹) ⊤ r := by
    rw [← characteristic_top_eq_proximity_of_analyticOnNhd hH]
    exact characteristic_congr_codiscrete hcod (by linarith)
  have h2 : characteristic (G * F⁻¹) ⊤ r
      ≤ characteristic G ⊤ r + characteristic F⁻¹ ⊤ r := by
    have := characteristic_mul_top_le (f₁ := G) (f₂ := F⁻¹) hr hGmer hGord hFinvmer hFinvord
    simpa using this
  have h3 : characteristic F⁻¹ ⊤ r ≤ characteristic F ⊤ r + K := by
    have habs := characteristic_sub_characteristic_inv_le (f := F) (R := r) hFmer
    have := (abs_le.mp habs).1
    linarith
  rw [h1]
  have hFch : characteristic F ⊤ r = proximity F ⊤ r :=
    congrFun (characteristic_top_eq_proximity_of_analyticOnNhd hF) r
  have hGch : characteristic G ⊤ r = proximity G ⊤ r :=
    congrFun (characteristic_top_eq_proximity_of_analyticOnNhd hG) r
  rw [hFch] at h3
  rw [hGch] at h2
  linarith

/-- **The Poisson bound at triple radius.**  For a zero-free entire function the log-modulus at
`z` is at most three times the proximity at radius `2(1 + ‖z‖)`. -/
theorem log_norm_le_three_mul_proximity {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h Set.univ) (hne : ∀ z, h z ≠ 0) (z : ℂ) :
    Real.log ‖h z‖ ≤ 3 * proximity h ⊤ (2 * (1 + ‖z‖)) := by
  set R : ℝ := 2 * (1 + ‖z‖) with hR
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hRpos : (0 : ℝ) < R := by rw [hR]; linarith
  have hR1 : (1 : ℝ) ≤ R := by rw [hR]; linarith
  have hzR : ‖z‖ < R := by rw [hR]; linarith
  have hpo := log_norm_le_poisson_proximity (f := h) (c := 0) (w := z) (R := R) (r := ‖z‖)
    (hh.mono (Set.subset_univ _)) (fun w _ => hne w)
    (by rw [mem_ball_zero_iff]; exact hzR) (by simp) hzR
  have hav : Real.circleAverage (fun w => Real.posLog ‖h w‖) 0 R = proximity h ⊤ R := by
    have := characteristic_top_eq_circleAverage_of_analyticOnNhd hh
    have h2 := characteristic_top_eq_proximity_of_analyticOnNhd hh
    rw [h2] at this
    exact (congrFun this R).symm
  rw [hav] at hpo
  have hcoef : (R + ‖z‖) / (R - ‖z‖) ≤ 3 := by
    rw [div_le_iff₀ (by rw [hR]; linarith)]
    rw [hR]; linarith
  have hprnn : 0 ≤ proximity h ⊤ R := proximity_nonneg_of_entire hh hR1
  calc Real.log ‖h z‖ ≤ (R + ‖z‖) / (R - ‖z‖) * proximity h ⊤ R := hpo
    _ ≤ 3 * proximity h ⊤ R := mul_le_mul_of_nonneg_right hcoef hprnn

/-- Every constant is absorbed by a positive multiple of `(log (2 + ‖z‖))²`. -/
theorem abs_le_logSq (c : ℝ) (z : ℂ) :
    |c| ≤ ((|c| + 1) / (Real.log 2) ^ (2 : ℕ)) * (Real.log (2 + ‖z‖)) ^ (2 : ℕ) := by
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogz : Real.log 2 ≤ Real.log (2 + ‖z‖) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hsq : (Real.log 2) ^ (2 : ℕ) ≤ (Real.log (2 + ‖z‖)) ^ (2 : ℕ) := by nlinarith
  have hstep : ((|c| + 1) / (Real.log 2) ^ (2 : ℕ)) * (Real.log 2) ^ (2 : ℕ) = |c| + 1 := by
    field_simp
  nlinarith [abs_nonneg c, div_nonneg (by positivity : (0:ℝ) ≤ |c| + 1)
    (by positivity : (0:ℝ) ≤ (Real.log 2) ^ (2 : ℕ))]

/-- **Subquadratic-logarithmic proximity forces constancy.**  A zero-free entire function whose
proximity is eventually below `(log R)²` is constant. -/
theorem const_of_zeroFree_of_proximity_le_logSq {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h Set.univ) (hne : ∀ z, h z ≠ 0)
    (hprox : ∀ᶠ R : ℝ in atTop, proximity h ⊤ R ≤ (Real.log R) ^ (2 : ℕ)) :
    ∀ z, h z = h 0 := by
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hprox
  set S : ℝ := max 1 R₀ with hS
  have hS1 : (1 : ℝ) ≤ S := le_max_left _ _
  have hSR₀ : R₀ ≤ S := le_max_right _ _
  -- a crude bound on the compact disc of radius `S`
  have hcont : ContinuousOn (fun z : ℂ => Real.log ‖h z‖) (closedBall (0 : ℂ) S) := by
    intro w _
    exact ((hh w (Set.mem_univ w)).continuousAt.continuousWithinAt.norm).log
      (norm_ne_zero_iff.mpr (hne w))
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : ℂ) S).exists_bound_of_continuousOn hcont
  -- the envelope
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set B : ℝ := 12 + (|C₀| + 1) / (Real.log 2) ^ (2 : ℕ) with hB
  have hBnn : 0 ≤ B := by positivity
  have hbound : ∀ z : ℂ, Real.log ‖h z‖ ≤ B * (Real.log (2 + ‖z‖)) ^ (2 : ℕ) := by
    intro z
    have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    have hlogz : Real.log 2 ≤ Real.log (2 + ‖z‖) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hlogzpos : (0 : ℝ) < Real.log (2 + ‖z‖) := lt_of_lt_of_le hlog2 hlogz
    have hsq : (Real.log 2) ^ (2 : ℕ) ≤ (Real.log (2 + ‖z‖)) ^ (2 : ℕ) := by nlinarith
    by_cases hzS : ‖z‖ ≤ S
    · -- compact range: absorb into the constant
      have hmem : z ∈ closedBall (0 : ℂ) S := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hzS
      have h1 : Real.log ‖h z‖ ≤ |C₀| := by
        have hb := hC₀ z hmem
        rw [Real.norm_eq_abs] at hb
        exact le_trans (le_abs_self _) (le_trans hb (le_abs_self C₀))
      have h2 := abs_le_logSq C₀ z
      have h3 : ((|C₀| + 1) / (Real.log 2) ^ (2 : ℕ)) * (Real.log (2 + ‖z‖)) ^ (2 : ℕ)
          ≤ B * (Real.log (2 + ‖z‖)) ^ (2 : ℕ) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hB]; linarith
      linarith
    · -- large range: the Poisson bound
      have hzS' : S < ‖z‖ := lt_of_not_ge hzS
      have hRge : R₀ ≤ 2 * (1 + ‖z‖) := by linarith
      have hpr := hR₀ (2 * (1 + ‖z‖)) hRge
      have hpo := log_norm_le_three_mul_proximity hh hne z
      have hlogR : Real.log (2 * (1 + ‖z‖)) ≤ 2 * Real.log (2 + ‖z‖) := by
        have hle : 2 * (1 + ‖z‖) ≤ (2 + ‖z‖) ^ (2 : ℕ) := by nlinarith
        calc Real.log (2 * (1 + ‖z‖)) ≤ Real.log ((2 + ‖z‖) ^ (2 : ℕ)) :=
              Real.log_le_log (by linarith) hle
          _ = 2 * Real.log (2 + ‖z‖) := by
              rw [Real.log_pow]; push_cast; ring
      have hlogRnn : (0 : ℝ) ≤ Real.log (2 * (1 + ‖z‖)) :=
        Real.log_nonneg (by linarith)
      have hsq2 : (Real.log (2 * (1 + ‖z‖))) ^ (2 : ℕ) ≤ 4 * (Real.log (2 + ‖z‖)) ^ (2 : ℕ) := by
        nlinarith
      have h4 : Real.log ‖h z‖ ≤ 12 * (Real.log (2 + ‖z‖)) ^ (2 : ℕ) := by
        calc Real.log ‖h z‖ ≤ 3 * proximity h ⊤ (2 * (1 + ‖z‖)) := hpo
          _ ≤ 3 * (Real.log (2 * (1 + ‖z‖))) ^ (2 : ℕ) := by linarith
          _ ≤ 12 * (Real.log (2 + ‖z‖)) ^ (2 : ℕ) := by linarith
      have h5 : 12 * (Real.log (2 + ‖z‖)) ^ (2 : ℕ) ≤ B * (Real.log (2 + ‖z‖)) ^ (2 : ℕ) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hB]
        have : (0 : ℝ) ≤ (|C₀| + 1) / (Real.log 2) ^ (2 : ℕ) := by positivity
        linarith
      linarith
  -- exponentiate
  obtain ⟨g, hg, hg0, hexp⟩ := exists_entire_log_of_ne_zero
    (f := h) (fun z => (hh z (Set.mem_univ z)).differentiableAt) hne
  have hh0 : ‖h 0‖ ≠ 0 := norm_ne_zero_iff.mpr (hne 0)
  have hre : ∀ z, (g z).re = Real.log ‖h z‖ - Real.log ‖h 0‖ := by
    intro z
    have hnorm : ‖h z‖ = ‖h 0‖ * Real.exp ((g z).re) := by
      rw [hexp z, norm_mul, Complex.norm_exp]
    rw [hnorm, Real.log_mul hh0 (Real.exp_pos _).ne', Real.log_exp]
    ring
  set B' : ℝ := B + (|Real.log ‖h 0‖| + 1) / (Real.log 2) ^ (2 : ℕ) with hB'
  have hB'nn : 0 ≤ B' := by positivity
  have hbound' : ∀ z : ℂ, (g z).re ≤ B' * (Real.log (2 + ‖z‖)) ^ (2 : ℕ) := by
    intro z
    have h1 := hbound z
    have h2 := abs_le_logSq (Real.log ‖h 0‖) z
    have h3 : -Real.log ‖h 0‖ ≤ |Real.log ‖h 0‖| := neg_le_abs _
    rw [hre z, hB', add_mul]
    linarith
  have hgconst := GaloisForLFunctions.QuadraticSubtypeDivisor.entire_reBound_sq_imp_const g hg B' hB'nn hbound'
  intro z
  rw [hexp z, hgconst z, hg0, Complex.exp_zero, mul_one]

end GaloisForLFunctions.QuotientProximity
