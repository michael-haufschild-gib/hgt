import GaloisForLFunctions.RHTower.SpurHermite

/-!
# The Theorem-M critical scaling of the Hermite carrier

The Jensen-section positivity assembly uses the critically rescaled Hermite polynomial
`C_d(w) = a · He_{2d}(w / √(2d))`, whose defining feature is the **curvature-equals-value** identity
at its critical points: the Hermite ODE `He_m'' = X·He_m' − m·He_m` rescales to

`C_d'' = (w/m)·C_d' − C_d`,

so at a critical point `C_d''(c) = −C_d(c)` and hence `κ = |C_d''(c)| = |C_d(c)|`.  This is the
identity that makes the hyperbolicity barrier `β_i = m_i w_i ≍ κ_i δ_i` an `O(1)` quantity rather
than a shrinking one.

`SpurHermite` supplies the unscaled statement (`hermite_equilibrium_energy`, Lemma W: at every real
critical point `k` of `He_m` with `m ≥ 2`, `He_m''(k) = −m·He_m(k)` and `He_m(k) ≠ 0`); this file
transports it through the critical scaling.

## Main results

* `criticalScale` — the rescaling `p ↦ a · p(· / √m)`;
* `criticalScaledHermite_ode` — the Theorem-M ODE `C_d'' = (w/m)·C_d' − C_d`;
* `abs_second_derivative_criticalScaledHermite` — `κ = |C_d(c)|` at every critical point;
* `eval_criticalScaledHermite_ne_zero` — the critical values do not vanish (`F_i > 0`).
-/

namespace RHTower

open Polynomial

noncomputable section

/-- The probabilists' Hermite polynomial with real coefficients. -/
noncomputable def hermiteR (m : ℕ) : ℝ[X] := (hermite m).map (Int.castRingHom ℝ)

theorem eval_mapZ (p : ℤ[X]) (x : ℝ) : ((p.map (Int.castRingHom ℝ)).eval x) = (aeval x p : ℝ) := by
  rw [Polynomial.eval_map, Polynomial.aeval_def]
  rfl

@[simp] theorem eval_hermiteR (m : ℕ) (x : ℝ) : (hermiteR m).eval x = aeval x (hermite m) :=
  eval_mapZ _ _

@[simp] theorem derivative_hermiteR (m : ℕ) :
    (hermiteR m).derivative = ((hermite m).derivative).map (Int.castRingHom ℝ) := by
  rw [hermiteR, Polynomial.derivative_map]

/-- The Theorem-M critical rescaling `p ↦ a · p(· / √m)`. -/
noncomputable def criticalScale (a : ℝ) (m : ℕ) (p : ℝ[X]) : ℝ[X] :=
  Polynomial.C a * p.comp (Polynomial.C ((Real.sqrt m)⁻¹) * X)

theorem derivative_comp_linear (p : ℝ[X]) (s : ℝ) :
    (p.comp (Polynomial.C s * X)).derivative
      = Polynomial.C s * (p.derivative.comp (Polynomial.C s * X)) := by
  rw [Polynomial.derivative_comp]
  simp

theorem eval_criticalScale (a : ℝ) (m : ℕ) (p : ℝ[X]) (w : ℝ) :
    (criticalScale a m p).eval w = a * p.eval ((Real.sqrt m)⁻¹ * w) := by
  simp [criticalScale, Polynomial.eval_comp]

theorem derivative_criticalScale (a : ℝ) (m : ℕ) (p : ℝ[X]) :
    (criticalScale a m p).derivative
      = Polynomial.C ((Real.sqrt m)⁻¹) * criticalScale a m p.derivative := by
  rw [criticalScale, criticalScale, Polynomial.derivative_C_mul, derivative_comp_linear]
  ring

/-- **The Theorem-M ODE.**  The critically rescaled Hermite polynomial
`C_d(w) = a · He_m(w/√m)` satisfies `C_d'' = (w/m)·C_d' − C_d`. -/
theorem criticalScaledHermite_ode (a : ℝ) {m : ℕ} (hm : 0 < m) (w : ℝ) :
    (criticalScale a m (hermiteR m)).derivative.derivative.eval w
      = (w / m) * (criticalScale a m (hermiteR m)).derivative.eval w
        - (criticalScale a m (hermiteR m)).eval w := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set s : ℝ := (Real.sqrt m)⁻¹ with hs
  have hs2 : s ^ 2 = (m : ℝ)⁻¹ := by
    rw [hs, inv_pow, Real.sq_sqrt hmR.le]
  have hd1 : (criticalScale a m (hermiteR m)).derivative
      = Polynomial.C s * criticalScale a m (hermiteR m).derivative :=
    derivative_criticalScale a m (hermiteR m)
  have hd2 : (criticalScale a m (hermiteR m)).derivative.derivative
      = Polynomial.C (s ^ 2) * criticalScale a m (hermiteR m).derivative.derivative := by
    rw [hd1, Polynomial.derivative_C_mul, derivative_criticalScale, ← mul_assoc,
      ← Polynomial.C_mul, ← hs, ← sq]
  have hode := aeval_hermite_ode m (s * w)
  rw [hd2, hd1]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, eval_criticalScale, ← hs, hermiteR,
    Polynomial.derivative_map, eval_mapZ]
  have hmne : (m : ℝ) ≠ 0 := hmR.ne'
  have hkey : (aeval (s * w) ((hermite m).derivative.derivative) : ℝ)
      = (s * w) * (aeval (s * w) ((hermite m).derivative) : ℝ)
        - (m : ℝ) * (aeval (s * w) (hermite m) : ℝ) := by linarith [hode]
  rw [hkey, hs2]
  field_simp

/-- **`κ = |C_d(c)|` at every critical point.**  The curvature of the critically rescaled Hermite
polynomial at a critical point is the absolute critical value: this is the card's `§2` identity. -/
theorem abs_second_derivative_criticalScaledHermite (a : ℝ) {m : ℕ} (hm : 0 < m) {c : ℝ}
    (hc : (criticalScale a m (hermiteR m)).derivative.eval c = 0) :
    |(criticalScale a m (hermiteR m)).derivative.derivative.eval c|
      = |(criticalScale a m (hermiteR m)).eval c| := by
  rw [criticalScaledHermite_ode a hm c, hc, mul_zero, zero_sub, abs_neg]

/-- The critical value of the rescaled Hermite polynomial is nonzero: the card's `F_i > 0`. -/
theorem eval_criticalScaledHermite_ne_zero {a : ℝ} (ha : a ≠ 0) {m : ℕ} (hm : 2 ≤ m) {c : ℝ}
    (hc : (criticalScale a m (hermiteR m)).derivative.eval c = 0) :
    (criticalScale a m (hermiteR m)).eval c ≠ 0 := by
  have hmpos : (0 : ℕ) < m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  set s : ℝ := (Real.sqrt m)⁻¹ with hs
  have hsne : s ≠ 0 := by
    rw [hs]
    simp only [ne_eq, inv_eq_zero]
    exact (Real.sqrt_pos.mpr hmR).ne'
  have hcrit : (aeval (s * c) ((hermite m).derivative) : ℝ) = 0 := by
    rw [derivative_criticalScale] at hc
    simp only [Polynomial.eval_mul, Polynomial.eval_C, eval_criticalScale, ← hs] at hc
    have h2 : ((hermiteR m).derivative).eval (s * c)
        = (aeval (s * c) ((hermite m).derivative) : ℝ) := by
      rw [derivative_hermiteR, Polynomial.eval_map, Polynomial.aeval_def]
      rfl
    rw [h2] at hc
    rcases mul_eq_zero.mp hc with h | h
    · exact absurd h hsne
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' ha
      · exact h'
  obtain ⟨-, hne⟩ := hermite_equilibrium_energy hm hcrit
  rw [eval_criticalScale, ← hs, eval_hermiteR]
  exact mul_ne_zero ha hne

end

end RHTower
