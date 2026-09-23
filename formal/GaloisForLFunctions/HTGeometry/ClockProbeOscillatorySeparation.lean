import GaloisForLFunctions.HTGeometry.ClockProbeChartRiccati

/-!
# The determined class is strictly larger than the nonvanishing-probe class

A potential carries a globally nonvanishing smooth probe exactly when it is `-(□w + Γ(w,w))`. But
determination never needs one probe nonvanishing everywhere: it needs, at each event, *some* probe
nonvanishing there. The two conditions are not the same.

The oscillatory potential separates them. Its Wronskian against `sin(kx)` is constant, which forces
`u(π/k) = -u(0)` for **every** solution, so every solution changes sign and none is nowhere zero —
while the centred cosines already give a probe nonvanishing at each event.

So the exact reachable class of the previous file is a proper subclass of the determined potentials,
and the open ground of the inverse step is narrower than that characterisation suggests.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

/-- Wronskian of a solution against the sine of the same frequency. -/
noncomputable def oscWronskian (u : ℝ → ℝ) (k : ℝ) : ℝ → ℝ :=
  fun x => k * u x * Real.cos (k * x) - deriv u x * Real.sin (k * x)

/-- **The Wronskian is conserved.** -/
theorem hasDerivAt_oscWronskian {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (k : ℝ)
    (heq : ∀ x, secondDeriv u x = -(k ^ (2 : ℕ)) * u x) (x : ℝ) :
    HasDerivAt (oscWronskian u k) 0 x := by
  have hu1 : ∀ t : ℝ, HasDerivAt u (deriv u t) t := fun t =>
    (hu.differentiable (by simp) t).hasDerivAt
  have hdu : Differentiable ℝ (deriv u) := differentiable_deriv_of_contDiff hu
  have hu2 : ∀ t : ℝ, HasDerivAt (deriv u) (secondDeriv u t) t := fun t => (hdu t).hasDerivAt
  have hlin : HasDerivAt (fun t : ℝ => k * t) k x := by
    simpa using (hasDerivAt_id x).const_mul k
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (k * t)) (-Real.sin (k * x) * k) x := hlin.cos
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (k * t)) (Real.cos (k * x) * k) x := hlin.sin
  have hA : HasDerivAt (fun t : ℝ => k * u t * Real.cos (k * t))
      (k * deriv u x * Real.cos (k * x) + k * u x * (-Real.sin (k * x) * k)) x :=
    ((hu1 x).const_mul k).mul hcos
  have hB : HasDerivAt (fun t : ℝ => deriv u t * Real.sin (k * t))
      (secondDeriv u x * Real.sin (k * x) + deriv u x * (Real.cos (k * x) * k)) x :=
    (hu2 x).mul hsin
  have hsub := hA.sub hB
  have hval : k * deriv u x * Real.cos (k * x) + k * u x * (-Real.sin (k * x) * k)
      - (secondDeriv u x * Real.sin (k * x) + deriv u x * (Real.cos (k * x) * k)) = 0 := by
    rw [heq x]
    ring
  rw [hval] at hsub
  exact hsub

theorem oscWronskian_const {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (k : ℝ)
    (heq : ∀ x, secondDeriv u x = -(k ^ (2 : ℕ)) * u x) (x y : ℝ) :
    oscWronskian u k x = oscWronskian u k y :=
  is_const_of_deriv_eq_zero
    (fun t => (hasDerivAt_oscWronskian hu k heq t).differentiableAt)
    (fun t => (hasDerivAt_oscWronskian hu k heq t).deriv) x y

/-- **Every solution changes sign over a half period.** -/
theorem half_period_neg {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) {k : ℝ} (hk : k ≠ 0)
    (heq : ∀ x, secondDeriv u x = -(k ^ (2 : ℕ)) * u x) :
    u (Real.pi / k) = -u 0 := by
  have h := oscWronskian_const hu k heq 0 (Real.pi / k)
  have h0 : oscWronskian u k 0 = k * u 0 := by
    simp [oscWronskian]
  have hkp : k * (Real.pi / k) = Real.pi := by field_simp
  have h1 : oscWronskian u k (Real.pi / k) = -(k * u (Real.pi / k)) := by
    simp only [oscWronskian, hkp, Real.cos_pi, Real.sin_pi]
    ring
  rw [h0, h1] at h
  have hmul : k * u (Real.pi / k) = k * (-u 0) := by linarith [h]
  exact mul_left_cancel₀ hk hmul

/-- **The oscillatory potential has no nowhere-vanishing probe.** -/
theorem not_exists_nonvanishing_oscillatory_probe {k : ℝ} (hk : 0 < k) :
    ¬ ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧ (∀ x, u x ≠ 0) ∧
        SolvesPotentialWave secondDeriv (fun _ => k ^ (2 : ℕ)) u := by
  rintro ⟨u, hu, hu0, hsolve⟩
  have heq : ∀ x, secondDeriv u x = -(k ^ (2 : ℕ)) * u x := by
    intro x
    have h2 : secondDeriv u x + k ^ (2 : ℕ) * u x = 0 := hsolve x
    linarith [h2]
  have hflip := half_period_neg hu (ne_of_gt hk) heq
  have hb : (0 : ℝ) ≤ Real.pi / k := le_of_lt (div_pos Real.pi_pos hk)
  have hcont : ContinuousOn u (Set.Icc 0 (Real.pi / k)) := hu.continuous.continuousOn
  rcases lt_or_gt_of_ne (hu0 0) with hneg | hpos
  · have hmem : (0 : ℝ) ∈ Set.Icc (u 0) (u (Real.pi / k)) := by
      rw [hflip]
      constructor <;> linarith
    obtain ⟨z, _, hz⟩ := intermediate_value_Icc hb hcont hmem
    exact hu0 z hz
  · have hmem : (0 : ℝ) ∈ Set.Icc (u (Real.pi / k)) (u 0) := by
      rw [hflip]
      constructor <;> linarith
    obtain ⟨z, _, hz⟩ := intermediate_value_Icc' hb hcont hmem
    exact hu0 z hz

/-- **The oscillatory potential is not a Riccati potential.** -/
theorem not_riccatiPotential_oscillatory {k : ℝ} (hk : 0 < k) :
    ¬ ∃ w : ℝ → ℝ, ContDiff ℝ ∞ w ∧ riccatiPotential w = fun _ => k ^ (2 : ℕ) := by
  rintro ⟨w, hw, hEq⟩
  refine not_exists_nonvanishing_oscillatory_probe hk
    ⟨expProbe w, Real.contDiff_exp.comp hw, expProbe_ne_zero w, ?_⟩
  intro x
  have hk2 : riccatiPotential w x = k ^ (2 : ℕ) := congrFun hEq x
  have h := solvesPotentialWave_expProbe hw x
  rw [hk2] at h
  exact h

/-- **Strict separation.** There is a determined potential carrying no nowhere-vanishing probe, so
the nonvanishing-probe class is a proper subclass of the determined potentials. -/
theorem exists_noCommonZero_without_nonvanishing_probe :
    ∃ V : ℝ → ℝ, NoCommonZero secondDeriv V ∧
      ¬ ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧ (∀ x, u x ≠ 0) ∧
          SolvesPotentialWave secondDeriv V u :=
  ⟨fun _ => (1 : ℝ) ^ (2 : ℕ), noCommonZero_oscillatory 1,
    not_exists_nonvanishing_oscillatory_probe one_pos⟩

/-- The same separation stated against the Riccati description of the nonvanishing-probe class. -/
theorem exists_noCommonZero_not_riccatiPotential :
    ∃ V : ℝ → ℝ, NoCommonZero secondDeriv V ∧
      ¬ ∃ w : ℝ → ℝ, ContDiff ℝ ∞ w ∧ riccatiPotential w = V :=
  ⟨fun _ => (1 : ℝ) ^ (2 : ℕ), noCommonZero_oscillatory 1, not_riccatiPotential_oscillatory one_pos⟩

end GaloisForLFunctions.HTGeometry
