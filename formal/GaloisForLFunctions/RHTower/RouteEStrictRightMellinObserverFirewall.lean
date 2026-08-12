import GaloisForLFunctions.RHTower.MobiusGammaXiSingularGraphNormalLanding
import GaloisForLFunctions.HTGeometry.ClockCapacityHilbertBoundary

/-!
# Route E strict-right Mellin observer firewall

The singular graph-normal Gamma--Xi landing is contractive on inward nodes
`0 ≤ re u`, but its affine spectral coordinate is

`s = sigma + u * (sigma - 1)`.

This module closes the two exact no-go statements left in Theorem G of the
Route E diffuse-codiagonal paper.

* A point on the Mellin half-line has the unique node real part
  `(1 / 2 - sigma) / (sigma - 1)`, which is negative for `1 < sigma`.
* The squared magnitude forced on a scalar observer by the normalized
  squarefree source is not summable on that half-line.  The stronger formal
  statement is phase-independent: no complex coefficient sequence with that
  squared-magnitude profile belongs to `ℓ²`.

The divergence proof uses cofinally many prime (hence squarefree) indices.
Every such coordinate is bounded below by the positive squarefree partition
mass, so summability would contradict termwise convergence to zero.
-/

open Complex
open Filter

namespace RHTower

noncomputable section

/-- Squared magnitude forced on a scalar Mellin observer by the normalized
squarefree source.  This is the summand in the norm formula
`Z_sigma * sum_{Squarefree n} n ^ (sigma - 2 * re s)`. -/
def routeEMellinObserverNormSqProfile (sigma : ℝ) (s : ℂ) (n : ℕ) : ℝ :=
  if Squarefree n then
    squarefreeMobiusTotal sigma * (n : ℝ) ^ (sigma - 2 * s.re)
  else 0

/-- On the Mellin half-line, the squared observer magnitude is exactly
`Z_sigma * n ^ (sigma - 1)` at every squarefree index. -/
theorem routeEMellinObserverNormSqProfile_halfLine
    (sigma : ℝ) {s : ℂ} (hs : s.re = 1 / 2) (n : ℕ) :
    routeEMellinObserverNormSqProfile sigma s n =
      if Squarefree n then
        squarefreeMobiusTotal sigma * (n : ℝ) ^ (sigma - 1)
      else 0 := by
  rw [routeEMellinObserverNormSqProfile, hs]
  ring_nf

/-- Exact node equation for reaching the Mellin half-line. -/
theorem routeEMellinAffineRealPart_eq_half_iff
    {sigma : ℝ} (hsigma : 1 < sigma) (u : ℂ) :
    ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)).re = 1 / 2 ↔
      u.re = (1 / 2 - sigma) / (sigma - 1) := by
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  constructor <;> intro h
  · apply (eq_div_iff (sub_ne_zero.mpr hsigma.ne')).mpr
    nlinarith
  · rw [h]
    field_simp [sub_ne_zero.mpr hsigma.ne']
    ring

/-- The node needed to reach `re s = 1/2` from `1 < sigma` is outward. -/
theorem routeEMellinHalfLine_forces_outward_node
    {sigma : ℝ} (hsigma : 1 < sigma) {u : ℂ}
    (hhalf : ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)).re = 1 / 2) :
    u.re < 0 := by
  rw [routeEMellinAffineRealPart_eq_half_iff hsigma] at hhalf
  rw [hhalf]
  exact div_neg_of_neg_of_pos (by linarith) (sub_pos.mpr hsigma)

/-- No inward Hardy node reaches the Mellin half-line. -/
theorem routeEMellinHalfLine_ne_of_inward_node
    {sigma : ℝ} (hsigma : 1 < sigma) {u : ℂ} (hu : 0 ≤ u.re) :
    ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)).re ≠ 1 / 2 := by
  intro hhalf
  exact (not_lt_of_ge hu) (routeEMellinHalfLine_forces_outward_node hsigma hhalf)

theorem routeEMellinObserverNormSqProfile_nonneg
    {sigma : ℝ} (hsigma : 1 < sigma) (s : ℂ) (n : ℕ) :
    0 ≤ routeEMellinObserverNormSqProfile sigma s n := by
  rw [routeEMellinObserverNormSqProfile]
  split_ifs
  · exact mul_nonneg (squarefreeMobiusTotal_pos hsigma).le
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · exact le_rfl

/-- Strong phase-blind divergence range.  If `re s ≤ sigma/2`, every prime
coordinate is at least the positive squarefree partition mass, so the norm
square profile cannot be summable. -/
theorem not_summable_routeEMellinObserverNormSqProfile
    {sigma : ℝ} (hsigma : 1 < sigma) {s : ℂ} (hs : s.re ≤ sigma / 2) :
    ¬ Summable (routeEMellinObserverNormSqProfile sigma s) := by
  intro hsum
  have htotal : 0 < squarefreeMobiusTotal sigma :=
    squarefreeMobiusTotal_pos hsigma
  have heventually := hsum.tendsto_atTop_zero.eventually_lt_const htotal
  obtain ⟨N, hN⟩ := eventually_atTop.mp heventually
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  have hpOne : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hp.one_le
  have hexponent : 0 ≤ sigma - 2 * s.re := by linarith
  have hpower : 1 ≤ (p : ℝ) ^ (sigma - 2 * s.re) :=
    Real.one_le_rpow hpOne hexponent
  have hlower : squarefreeMobiusTotal sigma ≤
      routeEMellinObserverNormSqProfile sigma s p := by
    rw [routeEMellinObserverNormSqProfile, if_pos hp.squarefree]
    exact le_mul_of_one_le_right htotal.le hpower
  exact (not_lt_of_ge hlower) (hN p hpN)

/-- Equation (46) diverges at every point of the Mellin half-line. -/
theorem not_summable_routeEMellinHalfLineObserverNormSqProfile
    {sigma : ℝ} (hsigma : 1 < sigma) {s : ℂ} (hs : s.re = 1 / 2) :
    ¬ Summable (routeEMellinObserverNormSqProfile sigma s) := by
  apply not_summable_routeEMellinObserverNormSqProfile hsigma
  rw [hs]
  linarith

/-- Phase-independent scalar-observer firewall: any complex coefficient
sequence with the norm profile forced by Equation (46) lies outside `ℓ²`. -/
theorem routeEMellinHalfLineObserver_not_memℓp
    {sigma : ℝ} (hsigma : 1 < sigma) {s : ℂ} (hs : s.re = 1 / 2)
    (v : ℕ → ℂ)
    (hv : ∀ n, ‖v n‖ ^ 2 = routeEMellinObserverNormSqProfile sigma s n) :
    ¬ Memℓp v 2 := by
  intro hvMem
  have hsum : Summable (fun n => ‖v n‖ ^ 2) :=
    (GaloisForLFunctions.HTGeometry.memℓp_two_iff_summable_norm_sq v).mp hvMem
  exact not_summable_routeEMellinHalfLineObserverNormSqProfile hsigma hs
    (hsum.congr hv)

/-- There is no Hilbert-space scalar observer realizing the Mellin half-line
norm profile of the normalized squarefree source. -/
theorem no_routeEMellinHalfLineObserver_in_l2
    {sigma : ℝ} (hsigma : 1 < sigma) {s : ℂ} (hs : s.re = 1 / 2) :
    ¬ ∃ v : lp (fun _ : ℕ => ℂ) 2,
      ∀ n, ‖v n‖ ^ 2 = routeEMellinObserverNormSqProfile sigma s n := by
  rintro ⟨v, hv⟩
  exact routeEMellinHalfLineObserver_not_memℓp hsigma hs v hv (lp.memℓp v)

/-- Claim-complete Theorem G firewall: the half-line is outside the inward
graph-normal column, and its forced scalar-observer profile has no `ℓ²`
realization. -/
theorem routeEStrictRightMellinObserverFirewall
    {sigma : ℝ} (hsigma : 1 < sigma) {s : ℂ} (hs : s.re = 1 / 2) :
    (∀ u : ℂ,
        ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)).re = 1 / 2 → u.re < 0) ∧
      ¬ ∃ v : lp (fun _ : ℕ => ℂ) 2,
        ∀ n, ‖v n‖ ^ 2 = routeEMellinObserverNormSqProfile sigma s n := by
  exact ⟨fun _ hhalf => routeEMellinHalfLine_forces_outward_node hsigma hhalf,
    no_routeEMellinHalfLineObserver_in_l2 hsigma hs⟩

end

end RHTower
