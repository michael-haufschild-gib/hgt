import GaloisForLFunctions.RHTower.PrimeLogFiniteOrderUniqueness

/-!
# Compact-band reader obstruction for the flat Gamma seam

Prime-log uniqueness forces any finite-order analytic function matching the
horizontal grade current at every prime log to match it identically.  Its
imaginary-axis trace is unbounded, unlike the transform of a finite compact
spectral measure.  The theorem below formalizes the exact analytic obstruction;
the compact-measure and Hilbert specializations are proved on paper in
`stc-flat-gap-exterior-spectral-reader.md` and remain to be formalized.
-/

open Complex Filter Topology

namespace RHTower

private theorem stc_gradeCurrent_unbounded_imaginary (a : ℝ) (ha : 0 < a) (C : ℝ) :
    ∃ t : ℝ, C < ‖(I * (t : ℂ)) * Complex.sinh ((a : ℂ) * I * (t : ℂ))‖ := by
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (C * a / (2 * Real.pi))
  let t : ℝ := (Real.pi / 2 + 2 * Real.pi * n) / a
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have harg : (a : ℂ) * I * (t : ℂ) = ((Real.pi / 2 + 2 * Real.pi * n : ℝ) : ℂ) * I := by
    push_cast [t]
    field_simp [hac]
  have hsin : Real.sin (Real.pi / 2 + 2 * Real.pi * n) = 1 := by
    rw [show Real.pi / 2 + 2 * Real.pi * (n : ℝ) =
      Real.pi / 2 + (n : ℤ) * (2 * Real.pi) by push_cast; ring]
    simp only [Real.sin_add_int_mul_two_pi, Real.sin_pi_div_two]
  have ht : C < t := by
    dsimp [t]
    rw [lt_div_iff₀ ha]
    have hpi : 0 < Real.pi := Real.pi_pos
    have hn' : C * a / (2 * Real.pi) < (n : ℝ) := by exact_mod_cast hn
    have hprod : C * a < (n : ℝ) * (2 * Real.pi) :=
      (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hn'
    nlinarith
  refine ⟨t, ?_⟩
  have htpos : 0 < t := div_pos (by positivity) ha
  rw [harg, Complex.sinh_mul_I, ← Complex.ofReal_sin, norm_mul, norm_mul]
  simpa [hsin, abs_of_pos htpos] using ht

/-- An entire finite-order candidate with bounded imaginary trace cannot agree
with the literal horizontal grade current on every prime logarithm. -/
theorem stc_no_finiteOrder_boundedImaginary_gradeCurrent
    (a : ℝ) (ha : 0 < a) (F : ℂ → ℂ)
    (hF : Differentiable ℂ F)
    (A B ρ : ℝ) (hA : 1 ≤ A) (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hgrowth : ∀ z : ℂ,
      ‖F z - z * Complex.sinh ((a : ℂ) * z)‖ ≤
        A * Real.exp (B * ‖z‖ ^ ρ))
    (himag : ∃ M : ℝ, ∀ t : ℝ, ‖F (I * (t : ℂ))‖ ≤ M)
    (hprime : ∀ p : ℕ, p.Prime →
      F (Real.log p) = (Real.log p) * Complex.sinh ((a : ℂ) * (Real.log p))) :
    False := by
  have htarg : Differentiable ℂ
      (fun z : ℂ => z * Complex.sinh ((a : ℂ) * z)) := by fun_prop
  have hdiff : Differentiable ℂ
      (fun z : ℂ => F z - z * Complex.sinh ((a : ℂ) * z)) := hF.sub htarg
  have hzero : (fun z : ℂ => F z - z * Complex.sinh ((a : ℂ) * z)) = 0 := by
    apply RHTower.eq_zero_of_exponentialPower_of_primeLog_zeros
      hdiff hA hB hρ hgrowth
    intro p hp
    exact sub_eq_zero.mpr (hprime p hp)
  obtain ⟨M, hM⟩ := himag
  obtain ⟨t, ht⟩ := stc_gradeCurrent_unbounded_imaginary a ha M
  have heq := congrFun hzero (I * (t : ℂ))
  simp only [Pi.zero_apply] at heq
  have heq' : F (I * (t : ℂ)) =
      (I * (t : ℂ)) * Complex.sinh ((a : ℂ) * (I * (t : ℂ))) :=
    sub_eq_zero.mp heq
  have hbound := hM t
  rw [heq'] at hbound
  exact (not_lt_of_ge hbound) (by simpa only [mul_assoc] using ht)

end RHTower
