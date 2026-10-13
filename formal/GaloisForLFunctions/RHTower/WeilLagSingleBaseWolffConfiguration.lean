import GaloisForLFunctions.HTGeometry.PositiveWolffMeasure

/-!
# A positive configuration whose single-base lag samples all vanish

A single-base lag sequence samples `Φ(u) = Σ_ρ w_ρ e^{u(ρ − ½)}` on the lattice `u = mℓ`. If the
maximal real part of the configuration is attained, every progression is unbounded above
(`exists_lag_progression_gt_of_attainedTop`), and a bounded progression forces the other nodes to
accumulate in the vertical shadow of every off-line point (the shadow law). This file shows that
without attainment nothing more follows from positivity of the weights.

**Theorem** (`exists_positive_lag_configuration_vanishing_progression`). For `ℓ > 0` and `Θ > 0` there
is a countable, injective, locally finite family of points `ρ_i` with positive summable weights `c_i`,
real parts in `(½, ½ + Θ)` whose supremum `½ + Θ` is not attained, such that

`Σ_i c_i e^{mℓ(ρ_i − ½)} = 0` for every integer `m ≥ 1`.

**Theorem** (`exists_symmetric_lag_configuration_vanishing_samples`). The same holds for the full
symmetric configuration `{ρ_i, ρ̄_i, 1 − ρ̄_i, 1 − ρ_i}`: for every integer `m ≠ 0` its samples
`Σ_i c_i (e^{mℓ(ρ_i−½)} + e^{mℓ(ρ̄_i−½)} + e^{mℓ(½−ρ̄_i)} + e^{mℓ(½−ρ_i)})` vanish. Added to any
configuration, it changes the two-sided sample sequence `m ↦ Φ(mℓ)` (`m ∈ ℤ`) only at `m = 0`, by a
positive constant. So boundedness, one-sided bounds and Toeplitz positive-definiteness of a single-base
sample sequence all fail to detect a non-attained top.

**Proof.** Take the positive Wolff measure on the annulus `1 < |z| < e^{Θℓ}`
(`exists_positive_wolff_annulus`): points `x` with weights `c_x > 0` and `Σ c_x x^m = 0` for `m ≥ 1`,
accumulating at the outer circle. Put `ρ_x = ½ + (log x + 2πi N_x)/ℓ` with `N` an injection into `ℕ`.
Then `e^{mℓ(ρ_x − ½)} = x^m`, `Re ρ_x = ½ + log|x|/ℓ`, and the shifts `2πN_x/ℓ` make the ordinates
locally finite. The four symmetric copies give `x^m + x̄^m + x̄^{−m} + x^{−m}`; the Wolff measure kills
positive and negative moments alike, and complex conjugation transports the vanishing.
-/

open Complex Set
open scoped ComplexConjugate

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry.PositiveWolffMeasure

theorem exp_mul_wolffLift (ℓ : ℝ) (hℓ : ℓ ≠ 0) (x : ℂ) (hx : x ≠ 0) (n m : ℕ) :
    Complex.exp (((m : ℝ) * ℓ : ℝ) * ((1 / 2 + (Complex.log x + 2 * Real.pi * I * n) / ℓ) - 1 / 2)) =
      x ^ m := by
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ
  have h1 : (((m : ℝ) * ℓ : ℝ) : ℂ) * ((1 / 2 + (Complex.log x + 2 * Real.pi * I * n) / ℓ) - 1 / 2) =
      (m : ℂ) * Complex.log x + ((m * n : ℕ) : ℂ) * (2 * Real.pi * I) := by
    push_cast; field_simp; ring
  rw [h1, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_log hx, Complex.exp_nat_mul_two_pi_mul_I,
    mul_one]

theorem re_wolffLift (ℓ : ℝ) (x : ℂ) (n : ℕ) :
    (1 / 2 + (Complex.log x + 2 * Real.pi * I * n) / ℓ : ℂ).re = 1 / 2 + Real.log ‖x‖ / ℓ := by
  rw [Complex.add_re, Complex.div_ofReal_re, Complex.add_re, Complex.log_re]
  simp

theorem im_wolffLift (ℓ : ℝ) (x : ℂ) (n : ℕ) :
    (1 / 2 + (Complex.log x + 2 * Real.pi * I * n) / ℓ : ℂ).im = (Complex.arg x + 2 * Real.pi * n) / ℓ := by
  rw [Complex.add_im, Complex.div_ofReal_im, Complex.add_im, Complex.log_im]
  simp

/-- **Vanishing single-base samples at a non-attained top.** -/
theorem exists_positive_lag_configuration_vanishing_progression {ℓ Θ : ℝ} (hℓ : 0 < ℓ) (hΘ : 0 < Θ) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : ι → ℂ) (c : ι → ℝ), Function.Injective ρ ∧
      (∀ i, 1 / 2 < (ρ i).re ∧ (ρ i).re < 1 / 2 + Θ) ∧
      (∀ β < 1 / 2 + Θ, ∃ i, β < (ρ i).re) ∧
      (∀ T : ℝ, {i | |(ρ i).im| ≤ T}.Finite) ∧
      (∀ i, 0 < c i) ∧ Summable c ∧
      ∀ m : ℕ, 1 ≤ m →
        HasSum (fun i => (c i : ℂ) * Complex.exp (((m : ℝ) * ℓ : ℝ) * (ρ i - 1 / 2))) 0 := by
  have hR : (1 : ℝ) < Real.exp (Θ * ℓ) := Real.one_lt_exp_iff.mpr (by positivity)
  obtain ⟨t, c, htc, htA, hc, hacc, hmass, hmom, -⟩ :=
    exists_positive_wolff_annulus (r := 1) (R := Real.exp (Θ * ℓ)) zero_le_one hR
  haveI : Countable t := htc.to_subtype
  obtain ⟨N, hN⟩ := Countable.exists_injective_nat t
  have hxA : ∀ x : t, 1 < ‖(x : ℂ)‖ ∧ ‖(x : ℂ)‖ < Real.exp (Θ * ℓ) := fun x => htA x.2
  have hx0 : ∀ x : t, (x : ℂ) ≠ 0 := fun x h => by
    have := (hxA x).1; rw [h, norm_zero] at this; linarith
  set ρ : t → ℂ := fun x => 1 / 2 + (Complex.log x + 2 * Real.pi * I * (N x)) / ℓ with hρdef
  have hexp : ∀ x : t, ∀ m : ℕ,
      Complex.exp (((m : ℝ) * ℓ : ℝ) * (ρ x - 1 / 2)) = (x : ℂ) ^ m := fun x m =>
    exp_mul_wolffLift ℓ hℓ.ne' x (hx0 x) (N x) m
  refine ⟨t, inferInstance, ρ, fun x => c x, ?_, ?_, ?_, ?_, fun x => hc x x.2,
    hmass.summable, ?_⟩
  · intro x y hxy
    have h := hexp x 1
    rw [hxy, hexp y 1, pow_one, pow_one] at h
    exact Subtype.ext h.symm
  · intro x
    rw [hρdef, re_wolffLift]
    have h1 := (hxA x).1
    have h2 := (hxA x).2
    have hl1 : 0 < Real.log ‖(x : ℂ)‖ := Real.log_pos h1
    have hl2 : Real.log ‖(x : ℂ)‖ < Θ * ℓ := by
      rw [← Real.log_exp (Θ * ℓ)]
      exact Real.log_lt_log (by linarith) h2
    constructor
    · have : 0 < Real.log ‖(x : ℂ)‖ / ℓ := div_pos hl1 hℓ
      linarith
    · have : Real.log ‖(x : ℂ)‖ / ℓ < Θ := by rw [div_lt_iff₀ hℓ]; exact hl2
      linarith
  · intro β hβ
    obtain ⟨x, hxt, hx⟩ := hacc (Real.exp ((β - 1 / 2) * ℓ))
      (Real.exp_lt_exp.mpr (by nlinarith))
    refine ⟨⟨x, hxt⟩, ?_⟩
    rw [hρdef]
    simp only
    rw [re_wolffLift]
    have hpos : 0 < ‖x‖ := (Real.exp_pos _).trans hx
    have hl : (β - 1 / 2) * ℓ < Real.log ‖x‖ := by
      rw [← Real.log_exp ((β - 1 / 2) * ℓ)]
      exact Real.log_lt_log (Real.exp_pos _) hx
    have : β - 1 / 2 < Real.log ‖x‖ / ℓ := by rw [lt_div_iff₀ hℓ]; exact hl
    linarith
  · intro T
    have hsub : {x : t | |(ρ x).im| ≤ T} ⊆ N ⁻¹' Set.Iic ⌈(T * ℓ + Real.pi) / (2 * Real.pi)⌉₊ := by
      intro x hx
      simp only [mem_setOf_eq] at hx
      rw [hρdef] at hx
      simp only at hx
      rw [im_wolffLift] at hx
      simp only [mem_preimage, mem_Iic]
      have hπ := Real.pi_pos
      have harg := Complex.neg_pi_lt_arg (x : ℂ)
      have hle := (abs_le.mp hx).2
      rw [div_le_iff₀ hℓ] at hle
      have hN' : (N x : ℝ) ≤ (T * ℓ + Real.pi) / (2 * Real.pi) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      exact_mod_cast hN'.trans (Nat.le_ceil _)
    exact ((Set.finite_Iic _).preimage hN.injOn).subset hsub
  · intro m hm
    have h := hmom m hm
    refine h.congr_fun ?_
    intro x
    rw [hexp x m]

/-- The single-base sample of the symmetric quadruple `{ρ, ρ̄, 1 − ρ̄, 1 − ρ}` at the integer `m`. -/
def symLagSample (ℓ : ℝ) (ρ : ℂ) (m : ℤ) : ℂ :=
  Complex.exp (((m : ℝ) * ℓ : ℝ) * (ρ - 1 / 2)) + Complex.exp (((m : ℝ) * ℓ : ℝ) * (conj ρ - 1 / 2)) +
    Complex.exp (((m : ℝ) * ℓ : ℝ) * ((1 - conj ρ) - 1 / 2)) +
    Complex.exp (((m : ℝ) * ℓ : ℝ) * ((1 - ρ) - 1 / 2))

theorem symLagSample_eq (ℓ : ℝ) (ρ : ℂ) (m : ℤ) :
    symLagSample ℓ ρ m = Complex.exp ((ℓ : ℂ) * (ρ - 1 / 2)) ^ m +
      conj (Complex.exp ((ℓ : ℂ) * (ρ - 1 / 2))) ^ m +
      (conj (Complex.exp ((ℓ : ℂ) * (ρ - 1 / 2))) ^ m)⁻¹ + (Complex.exp ((ℓ : ℂ) * (ρ - 1 / 2)) ^ m)⁻¹ := by
  unfold symLagSample
  have e1 : (((m : ℝ) * ℓ : ℝ) : ℂ) * (ρ - 1 / 2) = (m : ℂ) * ((ℓ : ℂ) * (ρ - 1 / 2)) := by push_cast; ring
  have e2 : (((m : ℝ) * ℓ : ℝ) : ℂ) * (conj ρ - 1 / 2) = (m : ℂ) * conj ((ℓ : ℂ) * (ρ - 1 / 2)) := by
    simp only [map_mul, map_sub, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]; push_cast; ring
  have e3 : (((m : ℝ) * ℓ : ℝ) : ℂ) * ((1 - conj ρ) - 1 / 2) = -((m : ℂ) * conj ((ℓ : ℂ) * (ρ - 1 / 2))) := by
    simp only [map_mul, map_sub, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]; push_cast; ring
  have e4 : (((m : ℝ) * ℓ : ℝ) : ℂ) * ((1 - ρ) - 1 / 2) = -((m : ℂ) * ((ℓ : ℂ) * (ρ - 1 / 2))) := by
    push_cast; ring
  rw [e1, e2, e3, e4, Complex.exp_neg, Complex.exp_neg, Complex.exp_int_mul, Complex.exp_int_mul,
    Complex.exp_conj]

/-- **The symmetric configuration is invisible to every single-base sample `m ≠ 0`.** -/
theorem exists_symmetric_lag_configuration_vanishing_samples {ℓ Θ : ℝ} (hℓ : 0 < ℓ) (hΘ : 0 < Θ) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : ι → ℂ) (c : ι → ℝ), Function.Injective ρ ∧
      (∀ i, 1 / 2 < (ρ i).re ∧ (ρ i).re < 1 / 2 + Θ) ∧
      (∀ β < 1 / 2 + Θ, ∃ i, β < (ρ i).re) ∧
      (∀ T : ℝ, {i | |(ρ i).im| ≤ T}.Finite) ∧
      (∀ i, 0 < c i) ∧ Summable c ∧
      ∀ m : ℤ, m ≠ 0 → HasSum (fun i => (c i : ℂ) * symLagSample ℓ (ρ i) m) 0 := by
  have hR : (1 : ℝ) < Real.exp (Θ * ℓ) := Real.one_lt_exp_iff.mpr (by positivity)
  obtain ⟨t, c, htc, htA, hc, hacc, hmass, hmom, hinv⟩ :=
    exists_positive_wolff_annulus (r := 1) (R := Real.exp (Θ * ℓ)) zero_le_one hR
  have hinv' := hinv zero_lt_one
  haveI : Countable t := htc.to_subtype
  obtain ⟨N, hN⟩ := Countable.exists_injective_nat t
  have hxA : ∀ x : t, 1 < ‖(x : ℂ)‖ ∧ ‖(x : ℂ)‖ < Real.exp (Θ * ℓ) := fun x => htA x.2
  have hx0 : ∀ x : t, (x : ℂ) ≠ 0 := fun x h => by
    have := (hxA x).1; rw [h, norm_zero] at this; linarith
  set ρ' : t → ℂ := fun x => 1 / 2 + (Complex.log x + 2 * Real.pi * I * (N x)) / ℓ with hρ'def
  have hnode : ∀ x : t, Complex.exp ((ℓ : ℂ) * (ρ' x - 1 / 2)) = x := by
    intro x
    have h := exp_mul_wolffLift ℓ hℓ.ne' x (hx0 x) (N x) 1
    rw [pow_one] at h
    rw [← h]; congr 1; push_cast; ring
  refine ⟨t, inferInstance, ρ', fun x => c x, ?_, ?_, ?_, ?_, fun x => hc x x.2, hmass.summable, ?_⟩
  · intro x y hxy
    have h := hnode x
    rw [hxy, hnode y] at h
    exact Subtype.ext h.symm
  · intro x
    rw [hρ'def, re_wolffLift]
    have h1 := (hxA x).1
    have h2 := (hxA x).2
    have hl1 : 0 < Real.log ‖(x : ℂ)‖ := Real.log_pos h1
    have hl2 : Real.log ‖(x : ℂ)‖ < Θ * ℓ := by
      rw [← Real.log_exp (Θ * ℓ)]
      exact Real.log_lt_log (by linarith) h2
    constructor
    · have : 0 < Real.log ‖(x : ℂ)‖ / ℓ := div_pos hl1 hℓ
      linarith
    · have : Real.log ‖(x : ℂ)‖ / ℓ < Θ := by rw [div_lt_iff₀ hℓ]; exact hl2
      linarith
  · intro β hβ
    obtain ⟨x, hxt, hx⟩ := hacc (Real.exp ((β - 1 / 2) * ℓ))
      (Real.exp_lt_exp.mpr (by nlinarith))
    refine ⟨⟨x, hxt⟩, ?_⟩
    rw [hρ'def]
    simp only
    rw [re_wolffLift]
    have hl : (β - 1 / 2) * ℓ < Real.log ‖x‖ := by
      rw [← Real.log_exp ((β - 1 / 2) * ℓ)]
      exact Real.log_lt_log (Real.exp_pos _) hx
    have : β - 1 / 2 < Real.log ‖x‖ / ℓ := by rw [lt_div_iff₀ hℓ]; exact hl
    linarith
  · intro T
    have hsub : {x : t | |(ρ' x).im| ≤ T} ⊆ N ⁻¹' Set.Iic ⌈(T * ℓ + Real.pi) / (2 * Real.pi)⌉₊ := by
      intro x hx
      simp only [mem_setOf_eq] at hx
      rw [hρ'def] at hx
      simp only at hx
      rw [im_wolffLift] at hx
      simp only [mem_preimage, mem_Iic]
      have hπ := Real.pi_pos
      have harg := Complex.neg_pi_lt_arg (x : ℂ)
      have hle := (abs_le.mp hx).2
      rw [div_le_iff₀ hℓ] at hle
      have hN' : (N x : ℝ) ≤ (T * ℓ + Real.pi) / (2 * Real.pi) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      exact_mod_cast hN'.trans (Nat.le_ceil _)
    exact ((Set.finite_Iic _).preimage hN.injOn).subset hsub
  · intro m hm
    have hfour : ∀ n : ℕ, 1 ≤ n →
        HasSum (fun x : t => (c x : ℂ) * ((x : ℂ) ^ n + conj (x : ℂ) ^ n + (conj (x : ℂ) ^ n)⁻¹ +
          ((x : ℂ) ^ n)⁻¹)) 0 := by
      intro n hn
      have h1 := hmom n hn
      have h2 : HasSum (fun x : t => (c x : ℂ) * conj (x : ℂ) ^ n) 0 := by
        have := (Complex.hasSum_conj' (f := fun x : t => (c x : ℂ) * (x : ℂ) ^ n) (x := 0)).mpr h1
        simpa [map_mul, Complex.conj_ofReal, map_pow] using this
      have h3 : HasSum (fun x : t => (c x : ℂ) * (conj (x : ℂ) ^ n)⁻¹) 0 := by
        have := (Complex.hasSum_conj' (f := fun x : t => (c x : ℂ) * ((x : ℂ) ^ n)⁻¹) (x := 0)).mpr
          (hinv' n hn)
        simpa [map_mul, Complex.conj_ofReal, map_pow, map_inv₀] using this
      have h4 := hinv' n hn
      have := ((h1.add h2).add h3).add h4
      simp only [add_zero] at this
      refine this.congr_fun fun x => ?_
      ring
    rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
    · have hn : 1 ≤ n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · exact absurd (by rw [h]; rfl) hm
        · exact h
      refine (hfour n hn).congr_fun fun x => ?_
      rw [symLagSample_eq, hnode x, zpow_natCast, zpow_natCast]
    · have hn : 1 ≤ n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · exact absurd (by rw [h]; rfl) hm
        · exact h
      refine (hfour n hn).congr_fun fun x => ?_
      rw [symLagSample_eq, hnode x, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, inv_inv, inv_inv]
      ring

end RHTower

end
