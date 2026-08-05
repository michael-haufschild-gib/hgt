import GaloisForLFunctions.HTGeometry.KleinGordonTimeBandStability

/-!
# The optimal probing time, and the cube-root law

Reconstructing a moving background from the short-time field costs

`η·A/x² + B·x`,

noise divided by the square of the probing time, plus drift multiplied by it. The two terms pull in
opposite directions, so the estimate has a genuine optimum rather than improving as the probe
shortens — which is what makes an integration time a real parameter of such a measurement and not an
artefact of the proof.

The optimum is elementary. At the balance point `Bx³ = 2A` the first term is exactly half the second,
so the total is `(3/2)Bx`; and for every other probing time the total is larger, by the identity

`(A/y² + By) − (A/x² + Bx) = A(x−y)²(x+2y)/(x³y²)`,

which is manifestly non-negative. No inequality of means is needed: the difference is a square times
a positive factor.

Since `x = (2A/B)^{1/3}`, both the optimal probe and the optimal error scale like the **cube root** of
the noise. Halving the noise buys a factor `2^{1/3} ≈ 1.26` in the reconstruction, not a factor two.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

/-! ## The optimum of `A/x² + Bx` -/

/-- The balance point exists. -/
theorem exists_balance_probe {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∃ x : ℝ, 0 < x ∧ B * x ^ 3 = 2 * A := by
  have hc : (0 : ℝ) < 2 * A / B := by positivity
  refine ⟨(2 * A / B) ^ (((3 : ℕ) : ℝ))⁻¹, Real.rpow_pos_of_pos hc _, ?_⟩
  rw [Real.rpow_inv_natCast_pow hc.le (by norm_num)]
  field_simp

/-- **The optimal probing time is the cube root of twice the noise-to-drift ratio.** -/
theorem balance_probe_eq {A B x : ℝ} (hB : 0 < B) (hx : 0 < x) (hbal : B * x ^ 3 = 2 * A) :
    x = (2 * A / B) ^ (((3 : ℕ) : ℝ))⁻¹ := by
  have hval : x ^ (3 : ℕ) = 2 * A / B := by
    field_simp
    linarith
  rw [← hval, Real.pow_rpow_inv_natCast hx.le (by norm_num)]

/-- At the balance point the noise term is exactly half the drift term. -/
theorem inv_sq_add_linear_at_balance {A B x : ℝ} (hx : 0 < x) (hbal : B * x ^ 3 = 2 * A) :
    A / x ^ 2 + B * x = 3 / 2 * (B * x) := by
  have hA : A = B * x ^ 3 / 2 := by linarith
  rw [hA]
  field_simp
  ring

/-- **The balance point is the optimum.** The difference from any other probing time is a square
times a positive factor. -/
theorem inv_sq_add_linear_le_of_balance {A B x y : ℝ} (hA : 0 < A) (hx : 0 < x) (hy : 0 < y)
    (hbal : B * x ^ 3 = 2 * A) :
    A / x ^ 2 + B * x ≤ A / y ^ 2 + B * y := by
  have hx3 : x ^ 3 ≠ 0 := pow_ne_zero 3 hx.ne'
  have hB : B = 2 * A / x ^ 3 := by
    field_simp
    linarith
  have hid : (A / y ^ 2 + B * y) - (A / x ^ 2 + B * x)
      = A * (x - y) ^ 2 * (x + 2 * y) / (x ^ 3 * y ^ 2) := by
    rw [hB]
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ A * (x - y) ^ 2 * (x + 2 * y) / (x ^ 3 * y ^ 2) := by positivity
  linarith

/-! ## The optimal reconstruction of a moving background -/

section Optimal

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {W₁ W₂ : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b L : ℝ}

/-- **The optimal reconstruction error.** Probing at the balance point, the two error sources
contribute in the ratio `1 : 2`, and the bound is three halves of the drift term. Since the balance
point is `(2A/B)^{1/3}`, both the optimal probe and the optimal error scale like the cube root of the
observational noise. -/
theorem norm_sub_zero_le_optimal (hb0 : 0 ≤ b) (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r y)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r y) {R : ℝ}
    (hL0 : 0 ≤ L) (hLip : ∀ s : ℝ, ‖(W₁ s - W₂ s) - (W₁ 0 - W₂ 0)‖ ≤ L * |s|)
    (hAdom : ∀ v : Lp ℂ 2 (volume : Measure E),
      (W₁ 0 - W₂ 0) (kgLowPassOp R v) = (W₁ 0 - W₂ 0) v)
    (hAran : ∀ v : Lp ℂ 2 (volume : Measure E),
      kgLowPassOp R ((W₁ 0 - W₂ 0) v) = (W₁ 0 - W₂ 0) v)
    {η T x : ℝ} (hη0 : 0 ≤ η) (hx0 : 0 < x) (hxT : x ≤ T)
    (hxK : x ^ 2 * ((1 + R ^ 2) / 2 + b * Real.exp (b * T)) ≤ 1 / 8)
    (hbal : 8 * (L * Real.exp (b * T)) * x ^ 3 = 2 * (8 * (η * (1 + b * T))))
    (hobs : ∀ (g k : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
      ‖kgFieldMildT W₁ g k t - kgFieldMildT W₂ g k t‖ ≤ η * (‖g‖ + ‖k‖)) :
    ‖W₁ 0 - W₂ 0‖ ≤ 3 / 2 * (8 * (L * Real.exp (b * T)) * x) := by
  have hmain := norm_sub_zero_le_of_lowPassT hb0 hW₁b hW₁s hW₂b hW₂s hL0 hLip hAdom hAran
    hη0 hx0 hxT hxK hobs
  have hval := inv_sq_add_linear_at_balance (A := 8 * (η * (1 + b * T)))
    (B := 8 * (L * Real.exp (b * T))) hx0 hbal
  rw [← hval]
  exact hmain

/-- **No probing time does better.** For any other probing time the same estimate is weaker, so the
balance point is genuinely the optimum of the bound. -/
theorem kgProbe_bound_optimal {η T b L x y : ℝ} (hη : 0 < 8 * (η * (1 + b * T)))
    (hx0 : 0 < x) (hy0 : 0 < y)
    (hbal : 8 * (L * Real.exp (b * T)) * x ^ 3 = 2 * (8 * (η * (1 + b * T)))) :
    8 * (η * (1 + b * T)) / x ^ 2 + 8 * (L * Real.exp (b * T)) * x
      ≤ 8 * (η * (1 + b * T)) / y ^ 2 + 8 * (L * Real.exp (b * T)) * y :=
  inv_sq_add_linear_le_of_balance hη hx0 hy0 hbal

end Optimal

end GaloisForLFunctions.HTGeometry
