import GaloisForLFunctions.HTGeometry.TranslationOrbitVanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The Riemann zeta function is almost periodic on a vertical line

For `sigma > 1` the Dirichlet series converges absolutely, and on the line `Re s = sigma` each term
factors as a modulus times a unit character:

`n^(-(sigma+it)) = n^(-sigma) * exp(I * ((-log n) * t))`.

So `t ↦ zeta (sigma + i t)` is an absolutely convergent exponential series with frequencies
`-log n` and coefficient sum `zeta sigma`.  By the orbit theorem its translation orbit is totally
bounded, which is Bochner's criterion for almost periodicity.

This is the instantiation step that connects the abstract almost-periodicity substrate to zeta.  It
is classical (Bohr); it is recorded because the substrate needs it in exactly this form.
-/

open Complex Filter

namespace HTGeometry

/-- The Dirichlet coefficient of `zeta` on the line `Re s = sigma`, as a complex scalar. -/
noncomputable def zetaLineCoeff (sigma : ℝ) (n : ℕ) : ℂ := 1 / (n : ℂ) ^ (sigma : ℂ)

/-- The exponential-series model of `zeta` restricted to the vertical line `Re s = sigma`. -/
noncomputable def zetaLineSeries (sigma : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  ∑' n : ℕ, zetaLineCoeff sigma n • cisBCF (-Real.log n)

/-- On a vertical line in the half-plane of absolute convergence the coefficients are summable in
norm: their norms are the terms of `zeta sigma`. -/
theorem summable_norm_zetaLineCoeff {sigma : ℝ} (h : 1 < sigma) :
    Summable fun n : ℕ => ‖zetaLineCoeff sigma n‖ := by
  have hs : Summable fun n : ℕ => 1 / (n : ℝ) ^ sigma := by
    simpa [Real.rpow_natCast, one_div] using Real.summable_one_div_nat_rpow.mpr h
  refine hs.congr fun n => ?_
  rw [zetaLineCoeff, norm_div, norm_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Complex.norm_natCast_cpow_of_pos hn]
    simp

/-- Logarithmic factors do not affect convergence of a `p`-series: `sum (log n)^k / n^sigma`
converges for every `sigma > 1`.  From `log y <= y - 1` one gets `delta * log n <= n^delta`, so
choosing `delta = (sigma-1)/(2k)` bounds the terms by a constant times `n^(-(sigma+1)/2)`. -/
theorem summable_log_pow_div_nat_rpow (k : ℕ) {sigma : ℝ} (h : 1 < sigma) :
    Summable fun n : ℕ => (Real.log n) ^ k / (n : ℝ) ^ sigma := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using Real.summable_one_div_nat_rpow.mpr h
  set delta : ℝ := (sigma - 1) / (2 * k) with hdelta
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hdpos : 0 < delta := by
    rw [hdelta]; positivity
  have htail : Summable fun n : ℕ => (1 / delta ^ k) * (1 / (n : ℝ) ^ ((sigma + 1) / 2)) := by
    refine Summable.mul_left _ (Real.summable_one_div_nat_rpow.mpr ?_)
    linarith
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) htail
  · positivity
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hs0 : (0:ℝ) ^ sigma = 0 :=
      Real.zero_rpow (ne_of_gt (show (0:ℝ) < sigma by linarith))
    have hs1 : (0:ℝ) ^ ((sigma + 1) / 2) = 0 :=
      Real.zero_rpow (ne_of_gt (show (0:ℝ) < (sigma + 1) / 2 by linarith))
    simp [hs0, hs1]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  -- `delta * log n <= n ^ delta`
  have hlog : delta * Real.log n ≤ (n : ℝ) ^ delta := by
    have hrp : Real.log ((n : ℝ) ^ delta) = delta * Real.log n := Real.log_rpow hnpos delta
    have hle : Real.log ((n : ℝ) ^ delta) ≤ (n : ℝ) ^ delta - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    linarith
  have hlogn : Real.log n ≤ (n : ℝ) ^ delta / delta := by
    rw [le_div_iff₀ hdpos]; linarith [hlog]
  have hlognn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hpow : (Real.log n) ^ k ≤ ((n : ℝ) ^ delta / delta) ^ k :=
    pow_le_pow_left₀ hlognn hlogn k
  have hrpow : ((n : ℝ) ^ delta) ^ k = (n : ℝ) ^ ((sigma - 1) / 2) := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ delta) k, ← Real.rpow_mul (le_of_lt hnpos)]
    congr 1
    rw [hdelta]
    field_simp
  have hnum : (Real.log n) ^ k ≤ (1 / delta ^ k) * (n : ℝ) ^ ((sigma - 1) / 2) := by
    calc (Real.log n) ^ k ≤ ((n : ℝ) ^ delta / delta) ^ k := hpow
      _ = ((n : ℝ) ^ delta) ^ k / delta ^ k := by rw [div_pow]
      _ = (n : ℝ) ^ ((sigma - 1) / 2) / delta ^ k := by rw [hrpow]
      _ = (1 / delta ^ k) * (n : ℝ) ^ ((sigma - 1) / 2) := by ring
  have hden : (0 : ℝ) < (n : ℝ) ^ sigma := Real.rpow_pos_of_pos hnpos sigma
  rw [div_le_iff₀ hden]
  have hinner : (1 : ℝ) / (n : ℝ) ^ ((sigma + 1) / 2) * (n : ℝ) ^ sigma
      = (n : ℝ) ^ ((sigma - 1) / 2) := by
    rw [one_div, ← Real.rpow_neg (le_of_lt hnpos), ← Real.rpow_add hnpos]
    congr 1
    ring
  have hsplit : (1 / delta ^ k) * (1 / (n : ℝ) ^ ((sigma + 1) / 2)) * (n : ℝ) ^ sigma
      = (1 / delta ^ k) * (n : ℝ) ^ ((sigma - 1) / 2) := by
    rw [mul_assoc, hinner]
  rw [hsplit]
  exact hnum

/-- **`zeta` is almost periodic on every vertical line of absolute convergence.**  Its translation
orbit is totally bounded, which is Bochner's criterion. -/
theorem totallyBounded_translationOrbit_zetaLineSeries {sigma : ℝ} (h : 1 < sigma) :
    TotallyBounded (translationOrbit (zetaLineSeries sigma)) :=
  totallyBounded_translationOrbit_tsum _ _ (summable_norm_zetaLineCoeff h)

/-- The Dirichlet coefficient of the `k`-th derivative of `zeta` on the line `Re s = sigma`.
Differentiating the series brings down a factor `-log n` each time. -/
noncomputable def zetaJetLineCoeff (sigma : ℝ) (k n : ℕ) : ℂ :=
  ((-Real.log n : ℝ) : ℂ) ^ k / (n : ℂ) ^ (sigma : ℂ)

/-- The exponential-series model of `zeta^{(k)}` restricted to the line `Re s = sigma`. -/
noncomputable def zetaJetLineSeries (sigma : ℝ) (k : ℕ) : BoundedContinuousFunction ℝ ℂ :=
  ∑' n : ℕ, zetaJetLineCoeff sigma k n • cisBCF (-Real.log n)

theorem summable_norm_zetaJetLineCoeff {sigma : ℝ} (h : 1 < sigma) (k : ℕ) :
    Summable fun n : ℕ => ‖zetaJetLineCoeff sigma k n‖ := by
  refine (summable_log_pow_div_nat_rpow k h).congr fun n => ?_
  rw [zetaJetLineCoeff, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Complex.norm_natCast_cpow_of_pos hn, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hn))]
    simp

/-- **Every jet of `zeta` is almost periodic on a vertical line of absolute convergence.**  The
coefficients gain a factor `(log n)^k`, which does not disturb summability. -/
theorem totallyBounded_translationOrbit_zetaJetLineSeries {sigma : ℝ} (h : 1 < sigma) (k : ℕ) :
    TotallyBounded (translationOrbit (zetaJetLineSeries sigma k)) :=
  totallyBounded_translationOrbit_tsum _ _ (summable_norm_zetaJetLineCoeff h k)

/-- The constant function `1` has totally bounded orbit: it is the character of frequency zero. -/
theorem totallyBounded_translationOrbit_one :
    TotallyBounded (translationOrbit (1 : BoundedContinuousFunction ℝ ℂ)) := by
  have hone : (1 : BoundedContinuousFunction ℝ ℂ) = cisBCF 0 := by
    ext t
    simp [cisBCF_apply]
  rw [hone]
  simpa using totallyBounded_translationOrbit_expSum (n := 1) (fun _ => (0:ℝ)) (fun _ => (1:ℂ))

/-- **Monomials in the jets are almost periodic.**  Products preserve totally bounded orbits, so any
finite product of jets of `zeta` on a vertical line of absolute convergence is almost periodic. -/
theorem totallyBounded_translationOrbit_zetaJetMonomial {sigma : ℝ} (h : 1 < sigma)
    (s : Finset ℕ) (e : ℕ → ℕ) :
    TotallyBounded (translationOrbit (∏ k ∈ s, zetaJetLineSeries sigma k ^ e k)) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa using totallyBounded_translationOrbit_one
  | insert k s hk ih =>
      rw [Finset.prod_insert hk]
      refine totallyBounded_translationOrbit_mul _ _ ?_ ih
      induction e k with
      | zero =>
          simpa using totallyBounded_translationOrbit_one
      | succ m ihm =>
          rw [pow_succ]
          exact totallyBounded_translationOrbit_mul _ _ ihm
            (totallyBounded_translationOrbit_zetaJetLineSeries h k)

/-- **Degree stratification.**  If a finite sum vanishes identically, its almost-periodic stratum is
annihilated by the strata that decay.

This is the structural form of the first step in separating a differential relation by the decay rate
of its archimedean factors: the stratum carrying no decaying factor has totally bounded translation
orbit, every other stratum decays at `+infinity`, and the two cannot cancel.  Supplying the decay of
the higher strata (Stirling on vertical lines) and the identification of the zeroth stratum as a
monomial combination of `zeta`-jets turns this into that step. -/
theorem stratum_zero_eq_zero_of_sum_eq_zero
    (Q0 : BoundedContinuousFunction ℝ ℂ)
    (hQ0 : TotallyBounded (translationOrbit Q0))
    {n : ℕ} (Q : Fin n → ℝ → ℂ)
    (hdecay : ∀ i, Filter.Tendsto (Q i) Filter.atTop (nhds 0))
    (hrel : ∀ t, Q0 t + ∑ i, Q i t = 0) :
    ∀ t, Q0 t = 0 := by
  refine eq_zero_of_totallyBounded_orbit_of_add_tendsto_zero Q0 hQ0
    (fun t => ∑ i, Q i t) ?_ hrel
  have : Filter.Tendsto (fun t : ℝ => ∑ i, Q i t) Filter.atTop (nhds (∑ _i : Fin n, (0 : ℂ))) :=
    tendsto_finsetSum _ fun i _ => hdecay i
  simpa using this

end HTGeometry
