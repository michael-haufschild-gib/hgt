import GaloisForLFunctions.ArithmeticDiscreteness.ACuspOfTheBohrLiftForcesNearCoincidences
import GaloisForLFunctions.ArithmeticDiscreteness.EulerProductsCreateTheNearCoincidences
import GaloisForLFunctions.Bottcher.FigureEight

/-!
# A smooth tangency needs transcendental coefficients

For two primes and integer coefficients, a consistent tangency of the Bohr lift at the torsion
point `(1, 1)` must be a singular point of `G`: the tangency equation `log 2 · G_x + log 3 · G_y = 0`
with integers `G_x, G_y` forces both to vanish (`log 3/log 2 ∉ ℚ`). With coefficients involving
the prime logarithms the tangency can be smooth. The carrier

`D(s) = −(log 3 − log 2) + log 3 · 2^{−s} − log 2 · 3^{−s}`

has an affine Bohr lift, vanishes at `s = 0` with `D'(0) = 0` and
`D''(0) = log 2 · log 3 · (log 2 − log 3) ≠ 0` (`logTrinomial_deriv_zero`,
`logTrinomial_second_deriv_zero`), so its tangency is smooth, isolated and of order two
(`zeroMult_logTrinomial`).

* **Near-coincidences at every scale** (`logTrinomial_collision_or_close_pair`), by
  `exists_collision_or_close_pair`.

Compare `1 + 2^{−s} + 3^{−s}`, with integer coefficients and the same shape, which repels uniformly
(`trinomial_uniform_repulsion`).
-/

open Complex Metric Filter

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- The affine Bohr lift `−(log 3 − log 2) + log 3 · x − log 2 · y`. -/
def logLift (x : Fin 2 → ℂ) : ℂ :=
  -(Complex.log 3 - Complex.log 2) + Complex.log 3 * x 0 - Complex.log 2 * x 1

/-- The carrier `−(log 3 − log 2) + log 3 · 2^{−s} − log 2 · 3^{−s}`. -/
def logTrinomial (s : ℂ) : ℂ :=
  -(Complex.log 3 - Complex.log 2) + Complex.log 3 * (2 : ℂ) ^ (-s) - Complex.log 2 * (3 : ℂ) ^ (-s)

theorem translateCarrier_log (v : Fin 2 → ℂ) (s : ℂ) :
    translateCarrier (fun i => ((primesTwoThree i : ℕ) : ℝ)) logLift v s =
      -(Complex.log 3 - Complex.log 2) + Complex.log 3 * (v 0 * (2 : ℂ) ^ (-s)) -
        Complex.log 2 * (v 1 * (3 : ℂ) ^ (-s)) := by
  simp [translateCarrier, logLift, primesTwoThree]

/-- `D'(s) = −log 2 log 3 · 2^{−s} + log 2 log 3 · 3^{−s}`. -/
theorem hasDerivAt_logTrinomial (s : ℂ) :
    HasDerivAt logTrinomial (Complex.log 2 * Complex.log 3 * ((3 : ℂ) ^ (-s) - (2 : ℂ) ^ (-s))) s := by
  have h := (((hasDerivAt_cpow_neg two_ne_zero s).const_mul (Complex.log 3)).const_add
    (-(Complex.log 3 - Complex.log 2))).sub
    ((hasDerivAt_cpow_neg three_ne_zero s).const_mul (Complex.log 2))
  unfold logTrinomial
  exact h.congr_deriv (by ring)

theorem deriv_logTrinomial :
    deriv logTrinomial = fun s => Complex.log 2 * Complex.log 3 * ((3 : ℂ) ^ (-s) - (2 : ℂ) ^ (-s)) :=
  funext fun s => (hasDerivAt_logTrinomial s).deriv

theorem logTrinomial_deriv_zero : deriv logTrinomial 0 = 0 := by
  rw [deriv_logTrinomial]; simp

theorem logTrinomial_second_deriv_zero :
    deriv (deriv logTrinomial) 0 =
      Complex.log 2 * Complex.log 3 * (Complex.log 2 - Complex.log 3) := by
  rw [deriv_logTrinomial]
  have h : HasDerivAt (fun s : ℂ => Complex.log 2 * Complex.log 3 * ((3 : ℂ) ^ (-s) - (2 : ℂ) ^ (-s)))
      (Complex.log 2 * Complex.log 3 * (-(Complex.log 3 * (3 : ℂ) ^ (-(0 : ℂ))) -
        -(Complex.log 2 * (2 : ℂ) ^ (-(0 : ℂ))))) 0 :=
    ((hasDerivAt_cpow_neg three_ne_zero 0).sub (hasDerivAt_cpow_neg two_ne_zero 0)).const_mul
      (Complex.log 2 * Complex.log 3)
  rw [h.deriv]
  simp only [neg_zero, Complex.cpow_zero, mul_one]
  ring

theorem log_two_ne_log_three : Complex.log 2 ≠ Complex.log 3 := by
  intro h
  have h2 : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num)]; norm_num
  have h3 : Complex.log 3 = ((Real.log 3 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num)]; norm_num
  rw [h2, h3] at h
  have := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3)
  exact absurd (Complex.ofReal_injective h) this.ne

theorem complex_log_ne_zero {n : ℕ} (hn : 1 < n) : Complex.log (n : ℂ) ≠ 0 := by
  rw [← Complex.natCast_log]
  exact_mod_cast (Real.log_pos (by exact_mod_cast hn)).ne'

/-- **The tangency is smooth, isolated and of order two.** -/
theorem logTrinomial_factor :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ G 0 ≠ 0 ∧ ∀ᶠ z in nhds 0, logTrinomial z = z ^ 2 * G z := by
  have han : AnalyticAt ℂ logTrinomial 0 :=
    Differentiable.analyticAt (f := logTrinomial)
      (fun s => (hasDerivAt_logTrinomial s).differentiableAt) 0
  have h2 : deriv (deriv logTrinomial) 0 ≠ 0 := by
    rw [logTrinomial_second_deriv_zero]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) (sub_ne_zero.mpr log_two_ne_log_three)
    · simpa using complex_log_ne_zero (n := 2) (by norm_num)
    · simpa using complex_log_ne_zero (n := 3) (by norm_num)
  obtain ⟨G, hG, hG0, hev⟩ := Bottcher.exists_factor_order_two han logTrinomial_deriv_zero h2
  have h0 : logTrinomial 0 = 0 := by simp [logTrinomial]
  exact ⟨G, hG, hG0, hev.mono fun z hz => by rw [← hz, h0, sub_zero]⟩

theorem zeroMult_logTrinomial : HTGeometry.zeroMult logTrinomial 0 = 2 := by
  obtain ⟨G, hG, hG0, hev⟩ := logTrinomial_factor
  have han : AnalyticAt ℂ logTrinomial 0 :=
    Differentiable.analyticAt (f := logTrinomial)
      (fun s => (hasDerivAt_logTrinomial s).differentiableAt) 0
  have hord : analyticOrderAt logTrinomial 0 = (2 : ℕ) :=
    (han.analyticOrderAt_eq_natCast).mpr ⟨G, hG, hG0, hev.mono fun z hz => by
      rw [hz, sub_zero, smul_eq_mul]⟩
  rw [HTGeometry.zeroMult, hord]; rfl

theorem exists_isolation_logTrinomial :
    ∃ ρ > 0, ∀ w ∈ closedBall (0 : ℂ) ρ, logTrinomial w = 0 → w = 0 := by
  obtain ⟨G, hG, hG0, hev⟩ := logTrinomial_factor
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (hev.and (hG.continuousAt.eventually_ne hG0))
  refine ⟨ε / 2, half_pos hε, fun w hw h0 => ?_⟩
  obtain ⟨hfac, hGw⟩ := hball (lt_of_le_of_lt (mem_closedBall.mp hw) (half_lt_self hε))
  rw [hfac] at h0
  exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp ((mul_eq_zero.mp h0).resolve_right hGw)

/-- **Near-coincidences at every scale.** For every `δ > 0` and `T₀` there is `t > T₀` such that
`−(log 3 − log 2) + log 3 · 2^{−s} − log 2 · 3^{−s}` has, within `δ` of `it`, a multiple zero or two
distinct zeros. -/
theorem logTrinomial_collision_or_close_pair {δ : ℝ} (hδ : 0 < δ) (T₀ : ℝ) :
    ∃ t : ℝ, T₀ < t ∧
      ((∃ z ∈ ball (0 : ℂ) δ, logTrinomial (t * I + z) = 0 ∧
          2 ≤ HTGeometry.zeroMult (fun w => logTrinomial (t * I + w)) z) ∨
        ∃ z ∈ ball (0 : ℂ) δ, ∃ z' ∈ ball (0 : ℂ) δ, z ≠ z' ∧
          logTrinomial (t * I + z) = 0 ∧ logTrinomial (t * I + z') = 0) := by
  obtain ⟨ρ, hρ, hiso⟩ := exists_isolation_logTrinomial
  have hlift : ∀ w, translateCarrier (fun i => ((primesTwoThree i : ℕ) : ℝ)) logLift
      (fun _ => 1) (((0 : ℝ) : ℂ) + w) = logTrinomial w := fun w => by
    rw [translateCarrier_log]; simp [logTrinomial]
  have hcont : Continuous logLift :=
    (continuous_const.add (continuous_const.mul (continuous_apply 0))).sub
      (continuous_const.mul (continuous_apply 1))
  have hhol : ∀ v : Fin 2 → ℂ,
      Differentiable ℂ (translateCarrier (fun i => ((primesTwoThree i : ℕ) : ℝ)) logLift v) := by
    intro v
    have : translateCarrier (fun i => ((primesTwoThree i : ℕ) : ℝ)) logLift v =
        fun s => -(Complex.log 3 - Complex.log 2) + Complex.log 3 * (v 0 * (2 : ℂ) ^ (-s)) -
          Complex.log 2 * (v 1 * (3 : ℂ) ^ (-s)) := funext (translateCarrier_log v)
    rw [this]
    exact ((differentiable_const _).add ((differentiable_const _).mul ((differentiable_const _).mul
      (differentiable_cpow_neg two_ne_zero)))).sub ((differentiable_const _).mul
      ((differentiable_const _).mul (differentiable_cpow_neg three_ne_zero)))
  have hord : 2 ≤ HTGeometry.zeroMult (fun w => translateCarrier
      (fun i => ((primesTwoThree i : ℕ) : ℝ)) logLift (fun _ => 1) (((0 : ℝ) : ℂ) + w)) 0 := by
    rw [show (fun w => translateCarrier (fun i => ((primesTwoThree i : ℕ) : ℝ)) logLift
      (fun _ => 1) (((0 : ℝ) : ℂ) + w)) = logTrinomial from funext hlift, zeroMult_logTrinomial]
  obtain ⟨t, ht, hres⟩ := exists_collision_or_close_pair primesTwoThree primesTwoThree_injective
    hcont hhol (u := fun _ => 1) (fun _ => norm_one) (by simpa using (hlift 0).trans (by
      simp [logTrinomial])) hρ (fun w hw h0 => hiso w hw (by rw [← hlift]; exact h0)) hord hδ T₀
  have hshift : ∀ w, translateCarrier (fun i => ((primesTwoThree i : ℕ) : ℝ)) logLift 1
      (((0 : ℝ) : ℂ) + t * I + w) = logTrinomial (t * I + w) := fun w => by
    rw [translateCarrier_log]; simp [logTrinomial]
  refine ⟨t, ht, ?_⟩
  rcases hres with ⟨z, hz, hz0, hm⟩ | ⟨z, hz, z', hz', hne, h1, h2⟩
  · refine Or.inl ⟨z, hz, by rw [← hshift]; exact hz0, ?_⟩
    have : (fun w => translateCarrier (fun i => ((primesTwoThree i : ℕ) : ℝ)) logLift 1
        (((0 : ℝ) : ℂ) + t * I + w)) = fun w => logTrinomial (t * I + w) := funext hshift
    rwa [this] at hm
  · exact Or.inr ⟨z, hz, z', hz', hne, by rw [← hshift]; exact h1, by rw [← hshift]; exact h2⟩

end GaloisForLFunctions.ArithmeticDiscreteness
