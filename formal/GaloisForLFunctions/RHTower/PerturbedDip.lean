/-
Docs 50 §4 + 51 §4 closure at the walk level (task #161 continuation): the
perturbed rotation dip.

The real tower pushes differ from the exact lattice rotation in two ways:
(i) the phase carries the drift/cubic error ε_m (certified ≤ 2πm³/3N-scale),
(ii) the amplitude envelope decays (a_m ∈ [a_min, a_max] on the block).
Both are absorbed here as EXPLICIT error budgets on the first-wrap dip:

  Σ amp_m·cos(β + mθ + ε_m) ≤ −a_min·r·(δ − (1 − cos(θ/2)))
                               + Mmax·(a_min·e₀ + (a_max − a_min)),

with Mmax = (2π + 2θ)/θ the wrap length. `birthKilled_of_perturbed_rotation`
then kills every misaligned birth whose depth is below the budgeted dip —
the `dip_kills` field of `MidCentral` discharged for REAL pushes given only:
polar data, misalignment, pointwise phase-error bound, envelope bounds, and
the depth inequality. What remains above this layer is purely the analytic
supply of those bounds from the carrier (the log-Taylor step bounds and the
per-entry dichotomy reading).
-/
import GaloisForLFunctions.RHTower.RotationDip

namespace RHTower

/-- Cosine is 1-Lipschitz: |cos x − cos y| ≤ |x − y|. -/
theorem abs_cos_sub_cos_le (x y : ℝ) :
    |Real.cos x - Real.cos y| ≤ |x - y| := by
  rw [Real.cos_sub_cos, abs_mul, abs_mul, abs_neg]
  have h1 : |Real.sin ((x + y) / 2)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have h2 : |Real.sin ((x - y) / 2)| ≤ |(x - y) / 2| :=
    Real.abs_sin_le_abs
  have h3 : |(x - y) / 2| = |x - y| / 2 := by
    rw [abs_div]
    norm_num
  calc |(2 : ℝ)| * |Real.sin ((x + y) / 2)| * |Real.sin ((x - y) / 2)|
      ≤ |(2 : ℝ)| * 1 * (|x - y| / 2) := by
        rw [h3] at h2
        have habs2 : |(2 : ℝ)| = 2 := by norm_num
        rw [habs2]
        have hs := abs_nonneg (Real.sin ((x - y) / 2))
        nlinarith [abs_nonneg (Real.sin ((x + y) / 2))]
    _ = |x - y| := by
        rw [show |(2 : ℝ)| = 2 by norm_num]
        ring

/-- **The perturbed rotation dip**: pointwise phase errors ≤ e₀ cost at most
M·e₀ against the exact first-wrap dip. -/
theorem perturbed_rotation_dip {θ β r γ δ e₀ : ℝ} {ε : ℕ → ℝ}
    (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi) (hr : 0 ≤ r)
    (hpolar : Complex.exp ((β : ℂ) * Complex.I)
        / (1 - Complex.exp ((θ : ℂ) * Complex.I))
      = (r : ℂ) * Complex.exp ((γ : ℂ) * Complex.I))
    (hne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 1)
    (hmis : Real.cos γ ≤ 1 - δ)
    (hε : ∀ m : ℕ, |ε m| ≤ e₀) :
    ∃ M : ℕ, 1 ≤ M ∧ (M : ℝ) * θ ≤ 2 * Real.pi + 2 * θ ∧
      ∑ m ∈ Finset.range M, Real.cos (β + m * θ + ε m)
        ≤ -(r * (δ - (1 - Real.cos (θ / 2)))) + M * e₀ := by
  obtain ⟨M, hM1, hMb, hdip⟩ := rotation_dip hθ0 hθπ hr hpolar hne hmis
  refine ⟨M, hM1, hMb, ?_⟩
  have hterm : ∀ m ∈ Finset.range M,
      Real.cos (β + m * θ + ε m) ≤ Real.cos (β + m * θ) + e₀ := by
    intro m _
    have hlip := abs_cos_sub_cos_le (β + m * θ + ε m) (β + m * θ)
    have harg : |β + m * θ + ε m - (β + m * θ)| = |ε m| := by
      congr 1
      ring
    rw [harg] at hlip
    have h2 := hε m
    have h4 : |Real.cos (β + m * θ + ε m) - Real.cos (β + m * θ)| ≤ e₀ :=
      le_trans hlip h2
    have h5 := (abs_le.mp h4).2
    linarith
  calc ∑ m ∈ Finset.range M, Real.cos (β + m * θ + ε m)
      ≤ ∑ m ∈ Finset.range M, (Real.cos (β + m * θ) + e₀) :=
        Finset.sum_le_sum hterm
    _ = (∑ m ∈ Finset.range M, Real.cos (β + m * θ)) + M * e₀ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
    _ ≤ -(r * (δ - (1 - Real.cos (θ / 2)))) + M * e₀ := by linarith

/-- **`dip_kills` for real pushes**: envelope in [a_min, a_max], phase error
≤ e₀, misaligned start — a birth whose depth is below the budgeted dip is
killed. -/
theorem birthKilled_of_perturbed_rotation {pushes : List ℝ}
    {birth : CascadeBirth} {θ β r γ δ e₀ amin amax : ℝ} {amp ε : ℕ → ℝ} {P : ℕ}
    (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi) (hr : 0 ≤ r)
    (hamin : 0 ≤ amin) (hamp : ∀ m : ℕ, amin ≤ amp m ∧ amp m ≤ amax)
    (hdep : 0 < birth.depthSq)
    (hpush : futurePushes pushes birth
      = (List.range P).map fun m : ℕ => amp m * Real.cos (β + (m : ℝ) * θ + ε m))
    (hlen : 2 * Real.pi + 2 * θ ≤ (P : ℝ) * θ)
    (hpolar : Complex.exp ((β : ℂ) * Complex.I)
        / (1 - Complex.exp ((θ : ℂ) * Complex.I))
      = (r : ℂ) * Complex.exp ((γ : ℂ) * Complex.I))
    (hne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 1)
    (hmis : Real.cos γ ≤ 1 - δ)
    (hε : ∀ m : ℕ, |ε m| ≤ e₀)
    (hdeep : birth.depthSq
      ≤ amin * (r * (δ - (1 - Real.cos (θ / 2))))
        - ((2 * Real.pi + 2 * θ) / θ) * (amin * e₀ + (amax - amin))) :
    BirthKilled pushes birth := by
  obtain ⟨M, _, hMb, hdip⟩ := perturbed_rotation_dip hθ0 hθπ hr hpolar hne
    hmis hε
  have hMP : M ≤ P := by
    by_contra hcon
    rw [not_le] at hcon
    have : (P : ℝ) * θ < (M : ℝ) * θ := by
      have hPM : (P : ℝ) < (M : ℝ) := by exact_mod_cast hcon
      exact mul_lt_mul_of_pos_right hPM hθ0
    linarith
  have hMmax : (M : ℝ) ≤ (2 * Real.pi + 2 * θ) / θ := by
    rw [le_div_iff₀ hθ0]
    exact hMb
  apply birthKilled_of_prefix_dip hdep
  refine ⟨(((List.range P).map fun m : ℕ =>
    amp m * Real.cos (β + (m : ℝ) * θ + ε m)).take M), ?_, ?_⟩
  · rw [hpush]
    exact List.take_prefix _ _
  · rw [pushSum_take_range_map _ hMP]
    -- split amplitudes: amp = amin + (amp − amin), cos ≤ 1 on the excess
    have hsplit : ∑ m ∈ Finset.range M, amp m * Real.cos (β + m * θ + ε m)
        ≤ amin * (∑ m ∈ Finset.range M, Real.cos (β + m * θ + ε m))
          + M * (amax - amin) := by
      have hterm : ∀ m ∈ Finset.range M,
          amp m * Real.cos (β + m * θ + ε m)
            ≤ amin * Real.cos (β + m * θ + ε m) + (amax - amin) := by
        intro m _
        obtain ⟨h1, h2⟩ := hamp m
        have hcos1 : Real.cos (β + m * θ + ε m) ≤ 1 := Real.cos_le_one _
        have hcos2 : -1 ≤ Real.cos (β + m * θ + ε m) := Real.neg_one_le_cos _
        nlinarith
      calc ∑ m ∈ Finset.range M, amp m * Real.cos (β + m * θ + ε m)
          ≤ ∑ m ∈ Finset.range M,
              (amin * Real.cos (β + m * θ + ε m) + (amax - amin)) :=
            Finset.sum_le_sum hterm
        _ = amin * (∑ m ∈ Finset.range M, Real.cos (β + m * θ + ε m))
              + M * (amax - amin) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
              nsmul_eq_mul, Finset.mul_sum]
    have hdipmul : amin * (∑ m ∈ Finset.range M, Real.cos (β + m * θ + ε m))
        ≤ amin * (-(r * (δ - (1 - Real.cos (θ / 2)))) + M * e₀) :=
      mul_le_mul_of_nonneg_left hdip hamin
    have hbudget : (M : ℝ) * (amin * e₀ + (amax - amin))
        ≤ ((2 * Real.pi + 2 * θ) / θ) * (amin * e₀ + (amax - amin)) := by
      apply mul_le_mul_of_nonneg_right hMmax
      have h01 := (hamp 0).1
      have h02 := (hamp 0).2
      have he0 : 0 ≤ e₀ := le_trans (abs_nonneg (ε 0)) (hε 0)
      nlinarith
    nlinarith [hsplit, hdipmul, hbudget, hdeep]

end RHTower

namespace RHTower

/-- The tower step-angle bounds 1/j ≤ log(j/(j−1)) ≤ 1/(j−1): what the
carrier tier feeds into the walk's [θmin, θmax] hypotheses (doc 50 §4). -/
theorem log_ratio_bounds {j : ℕ} (hj : 2 ≤ j) :
    1 / (j : ℝ) ≤ Real.log ((j : ℝ) / ((j : ℝ) - 1)) ∧
      Real.log ((j : ℝ) / ((j : ℝ) - 1)) ≤ 1 / ((j : ℝ) - 1) := by
  have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < (j : ℝ) := by linarith
  have hjm : (0 : ℝ) < (j : ℝ) - 1 := by linarith
  have hx : (0 : ℝ) < (j : ℝ) / ((j : ℝ) - 1) := by positivity
  constructor
  · have h1 := Real.log_le_sub_one_of_pos
      (x := ((j : ℝ) - 1) / (j : ℝ)) (by positivity)
    have hinv : Real.log (((j : ℝ) - 1) / (j : ℝ))
        = -Real.log ((j : ℝ) / ((j : ℝ) - 1)) := by
      rw [Real.log_div hjm.ne' hj0.ne', Real.log_div hj0.ne' hjm.ne']
      ring
    rw [hinv] at h1
    have h2 : ((j : ℝ) - 1) / (j : ℝ) - 1 = -(1 / (j : ℝ)) := by
      field_simp
      ring
    rw [h2] at h1
    linarith
  · have h1 := Real.log_le_sub_one_of_pos hx
    have h2 : (j : ℝ) / ((j : ℝ) - 1) - 1 = 1 / ((j : ℝ) - 1) := by
      field_simp
      ring
    rw [h2] at h1
    exact h1

end RHTower

namespace RHTower

/-- 1 − e^{iθ} in closed polar form: −2i·sin(θ/2)·e^{iθ/2}. -/
theorem one_sub_exp_eq (θ : ℝ) :
    1 - Complex.exp ((θ : ℂ) * Complex.I)
      = -2 * Complex.I * (Real.sin (θ / 2) : ℂ)
          * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) := by
  have hhalf : ((θ : ℂ)) = ((θ / 2 : ℝ) : ℂ) + ((θ / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hhalf, add_mul, Complex.exp_add]
  set u : ℂ := ((θ / 2 : ℝ) : ℂ) with hu
  have hsin : Complex.exp (u * Complex.I) - Complex.exp (-(u * Complex.I))
      = 2 * Complex.I * Complex.sin u := by
    rw [Complex.sin]
    field_simp
    rw [Complex.I_sq]
    ring
  have hinv : Complex.exp (-(u * Complex.I)) * Complex.exp (u * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    simp
  calc 1 - Complex.exp (u * Complex.I) * Complex.exp (u * Complex.I)
      = (Complex.exp (-(u * Complex.I)) - Complex.exp (u * Complex.I))
          * Complex.exp (u * Complex.I) := by
        rw [sub_mul, hinv]
    _ = -(2 * Complex.I * Complex.sin u) * Complex.exp (u * Complex.I) := by
        rw [show Complex.exp (-(u * Complex.I)) - Complex.exp (u * Complex.I)
            = -(Complex.exp (u * Complex.I) - Complex.exp (-(u * Complex.I))) from by
          ring, hsin]
    _ = -2 * Complex.I * (Real.sin (θ / 2) : ℂ)
          * Complex.exp (u * Complex.I) := by
        rw [hu, Complex.ofReal_sin]
        ring


/-- **The explicit polar data of the rotation circle**: for θ ∈ (0, 2π),
e^{iβ}/(1 − e^{iθ}) = (1/(2 sin(θ/2)))·e^{i(β − θ/2 + π/2)} — alignment
angle γ = β − θ/2 + π/2 and radius r = 1/(2 sin(θ/2)) in closed form, so the
misalignment hypothesis of the kill constructors is an explicit condition on
(β, θ) alone. -/
theorem polar_ratio_explicit {θ : ℝ} (h0 : 0 < θ) (h2 : θ < 2 * Real.pi)
    (β : ℝ) :
    Complex.exp ((β : ℂ) * Complex.I)
        / (1 - Complex.exp ((θ : ℂ) * Complex.I))
      = ((1 / (2 * Real.sin (θ / 2)) : ℝ) : ℂ)
          * Complex.exp (((β - θ / 2 + Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
  have hs : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsC : ((Real.sin (θ / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hs.ne'
  set E1 : ℂ := Complex.exp ((β : ℂ) * Complex.I) with hE1
  set E2 : ℂ := Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) with hE2
  have hE2ne : E2 ≠ 0 := Complex.exp_ne_zero _
  have hden : 1 - Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := by
    rw [one_sub_exp_eq]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ Complex.I_ne_zero) hsC)
      (Complex.exp_ne_zero _)
    norm_num
  rw [div_eq_iff hden, one_sub_exp_eq]
  have hI : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  have hC : Complex.exp (((β - θ / 2 + Real.pi / 2 : ℝ) : ℂ) * Complex.I)
      = E1 * E2⁻¹ * Complex.I := by
    have h1 : ((β - θ / 2 + Real.pi / 2 : ℝ) : ℂ) * Complex.I
        = (β : ℂ) * Complex.I + (-(((θ / 2 : ℝ) : ℂ) * Complex.I))
          + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h1, Complex.exp_add, Complex.exp_add, hI, Complex.exp_neg]
  rw [hC]
  have hof : ((1 / (2 * Real.sin (θ / 2)) : ℝ) : ℂ)
      = 1 / (2 * ((Real.sin (θ / 2) : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [hof]
  have hE2' : E2⁻¹ * E2 = 1 := inv_mul_cancel₀ hE2ne
  calc E1 = ((Complex.I * Complex.I) * (E2⁻¹ * E2) * E1)
      * (((-2) * ((Real.sin (θ / 2) : ℝ) : ℂ))
        / (2 * ((Real.sin (θ / 2) : ℝ) : ℂ))) := by
        rw [Complex.I_mul_I, hE2']
        rw [show ((-2 : ℂ)) * ((Real.sin (θ / 2) : ℝ) : ℂ)
            / (2 * ((Real.sin (θ / 2) : ℝ) : ℂ)) = -1 from by
          rw [div_eq_iff (mul_ne_zero two_ne_zero hsC)]
          ring]
        ring
    _ = 1 / (2 * ((Real.sin (θ / 2) : ℝ) : ℂ)) * (E1 * E2⁻¹ * Complex.I)
        * (-2 * Complex.I * ((Real.sin (θ / 2) : ℝ) : ℂ) * E2) := by
        ring

end RHTower

namespace RHTower

/-- Nonresonance of the unit rotation for `0 < θ < 2π`, in the exact form
consumed by the rotation-dip constructors. -/
theorem exp_mul_I_ne_one_of_pos_lt_two_pi {θ : ℝ} (h0 : 0 < θ)
    (h2 : θ < 2 * Real.pi) :
    Complex.exp ((θ : ℂ) * Complex.I) ≠ 1 := by
  intro h
  have hzero : 1 - Complex.exp ((θ : ℂ) * Complex.I) = 0 := by
    rw [h, sub_self]
  rw [one_sub_exp_eq] at hzero
  have hs : ((Real.sin (θ / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hprod : -2 * Complex.I * ((Real.sin (θ / 2) : ℝ) : ℂ)
      * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hs)
      (Complex.exp_ne_zero _)
  exact hprod hzero

/-- The explicit rotation-circle radius is nonnegative on `0 < θ < 2π`. -/
theorem polar_radius_nonneg_of_pos_lt_two_pi {θ : ℝ} (h0 : 0 < θ)
    (h2 : θ < 2 * Real.pi) : 0 ≤ 1 / (2 * Real.sin (θ / 2)) := by
  have hs : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  positivity

/-- **Perturbed kill with explicit polar data.** The closed polar form of
`e^{iβ}/(1-e^{iθ})` discharges the separate `r`, `γ`, polar, and nonresonance
premises of `birthKilled_of_perturbed_rotation`. -/
theorem birthKilled_of_perturbed_rotation_explicit_polar {pushes : List ℝ}
    {birth : CascadeBirth} {θ β δ e₀ amin amax : ℝ} {amp ε : ℕ → ℝ} {P : ℕ}
    (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi)
    (hamin : 0 ≤ amin) (hamp : ∀ m : ℕ, amin ≤ amp m ∧ amp m ≤ amax)
    (hdep : 0 < birth.depthSq)
    (hpush : futurePushes pushes birth
      = (List.range P).map fun m : ℕ => amp m * Real.cos (β + (m : ℝ) * θ + ε m))
    (hlen : 2 * Real.pi + 2 * θ ≤ (P : ℝ) * θ)
    (hmis : Real.cos (β - θ / 2 + Real.pi / 2) ≤ 1 - δ)
    (hε : ∀ m : ℕ, |ε m| ≤ e₀)
    (hdeep : birth.depthSq
      ≤ amin * ((1 / (2 * Real.sin (θ / 2))) * (δ - (1 - Real.cos (θ / 2))))
        - ((2 * Real.pi + 2 * θ) / θ) * (amin * e₀ + (amax - amin))) :
    BirthKilled pushes birth := by
  have hθ2 : θ < 2 * Real.pi := by linarith [Real.pi_pos]
  exact birthKilled_of_perturbed_rotation hθ0 hθπ
    (polar_radius_nonneg_of_pos_lt_two_pi hθ0 hθ2) hamin hamp hdep hpush hlen
    (polar_ratio_explicit hθ0 hθ2 β) (exp_mul_I_ne_one_of_pos_lt_two_pi hθ0 hθ2)
    hmis hε hdeep

end RHTower
