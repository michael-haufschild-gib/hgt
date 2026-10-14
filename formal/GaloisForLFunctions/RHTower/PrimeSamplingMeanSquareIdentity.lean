import GaloisForLFunctions.RHTower.JointAncestryShellArithmeticCriterion

/-!
# The prime-sampled explicit-formula error is concave in the prime number theorem error

Let `ψ` be Chebyshev's function, `E(t) = ψ(t) − t`, `M(t) = Σ_{n≤t} Λ(n)/n`, and

`J(t) = ψ(t)/t + log t − γ − 1 − M(t) = E(t)/t − (M(t) − log t + γ)`   (`pmsTail`).

`J` is continuous: at a prime power `n` the jumps `Λ(n)/n` of `ψ/t` and of `M` cancel.  Between
integers `J' = −E/t²`.  The prime side of the genus-kernel explicit formula is
`𝓔(X) = −X J(X) − log 2π + Σ_j X^{−2j}/(2j(2j+1))` (`lagPrimeSide_eq_neg_mul_pmsTail`), with no prime
number theorem needed.

**Theorem** (`sum_vonMangoldt_mul_pmsTail_div_sqrt`).  For `X ≥ 1`,

`Σ_{n≤X} Λ(n) J(n)/√n = H(X) − H(1) + ∫_1^X (J/√t + J²/(8√t) + E²/(t²√t)) dt`,

with `H(t) = E(t)J(t)/√t − √t J(t)²/4` (`pmsBoundary`).

**Proof.**  Between consecutive integers `ψ` and `M` are constant, and the smooth model of `H` has
derivative minus the integrand (`hasDerivAt_pmsBoundaryModel`).  At an integer `n` the left side
gains `Λ(n)J(n)/√n`, and `H` gains the same amount because `E` jumps by `Λ(n)` while `J` is
continuous.

**Reading.**  By `𝓔(n) = −nJ(n) + c(n)` the prime-weighted explicit-formula sum is
`Σ_{n≤X} Λ(n) n^{−3/2}(𝓔(n) − c(n)) = −(H(X) − H(1)) − ∫_1^X J/√t − Q(X)`, where
`Q(X) = ∫_1^X (J²/(8√t) + E²/(t²√t)) dt ≥ 0` is the mean square of the prime number theorem
error.  So the level-one prime side of the shell tests is a concave quadratic functional of `E`.
Its negative-definite part is the classical mean square, whose diagonal carries the one-signed
contribution `X^{2β−3/2}` of every zero with `β > ¾`.  The unconditional inequality
`Σ_{n≤X} Λ(n)J(n)/√n ≥ ∫_1^X J/√t + H(X) − H(1)` (`integral_add_pmsBoundary_le_sum`) records the sign.
-/

open ArithmeticFunction (vonMangoldt)
open Real MeasureTheory Set

namespace RHTower

noncomputable section

/-! ## The functions -/

/-- `M(t) = Σ_{n ≤ t} Λ(n)/n`. -/
def pmsMertens (t : ℝ) : ℝ := ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, vonMangoldt n / (n : ℝ)

/-- `E(t) = ψ(t) − t`. -/
def pmsErr (t : ℝ) : ℝ := Chebyshev.psi t - t

/-- `J(t) = ψ(t)/t + log t − γ − 1 − M(t)`. -/
def pmsTail (t : ℝ) : ℝ :=
  Chebyshev.psi t / t + Real.log t - Real.eulerMascheroniConstant - 1 - pmsMertens t

/-- `H(t) = E(t)J(t)/√t − √t J(t)²/4`. -/
def pmsBoundary (t : ℝ) : ℝ := pmsErr t * pmsTail t / √t - √t * pmsTail t ^ 2 / 4

/-- The mean-square density `J²/(8√t) + E²/(t²√t)`. -/
def pmsQuadDensity (t : ℝ) : ℝ := pmsTail t ^ 2 / (8 * √t) + pmsErr t ^ 2 / (t ^ 2 * √t)

/-- The full density `J/√t + J²/(8√t) + E²/(t²√t)`. -/
def pmsDensity (t : ℝ) : ℝ := pmsTail t / √t + pmsQuadDensity t

/-! ## The smooth model between integers -/

/-- `J` with `ψ = a`, `M = b` frozen. -/
def pmsTailModel (a b t : ℝ) : ℝ := a / t + Real.log t - Real.eulerMascheroniConstant - 1 - b

/-- `H` with `ψ = a`, `M = b` frozen. -/
def pmsBoundaryModel (a b t : ℝ) : ℝ :=
  (a - t) * pmsTailModel a b t / √t - √t * pmsTailModel a b t ^ 2 / 4

/-- The mean-square density with `ψ = a`, `M = b` frozen. -/
def pmsQuadModel (a b t : ℝ) : ℝ :=
  pmsTailModel a b t ^ 2 / (8 * √t) + (a - t) ^ 2 / (t ^ 2 * √t)

/-- The density with `ψ = a`, `M = b` frozen. -/
def pmsDensityModel (a b t : ℝ) : ℝ := pmsTailModel a b t / √t + pmsQuadModel a b t

theorem hasDerivAt_pmsTailModel (a b : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (pmsTailModel a b) (-(a - t) / t ^ 2) t := by
  have h1 : HasDerivAt (fun y : ℝ => a * y⁻¹) (a * -(t ^ 2)⁻¹) t :=
    (hasDerivAt_inv ht.ne').const_mul a
  have h := (((h1.add (Real.hasDerivAt_log ht.ne')).sub_const
    Real.eulerMascheroniConstant).sub_const 1).sub_const b
  have e : pmsTailModel a b = fun y => ((fun y : ℝ => a * y⁻¹) + Real.log) y -
      Real.eulerMascheroniConstant - 1 - b := by
    funext y; simp only [pmsTailModel, Pi.add_apply, div_eq_mul_inv]
  rw [e]
  exact h.congr_deriv (by field_simp; ring)

/-- **The model of `H` has derivative minus the density.** -/
theorem hasDerivAt_pmsBoundaryModel (a b : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (pmsBoundaryModel a b) (-pmsDensityModel a b t) t := by
  have hs := Real.hasDerivAt_sqrt ht.ne'
  have hJ := hasDerivAt_pmsTailModel a b ht
  have hE : HasDerivAt (fun t : ℝ => a - t) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub a
  have hr : 0 < √t := Real.sqrt_pos.mpr ht
  have h := ((hE.mul hJ).div hs hr.ne').sub ((hs.mul (hJ.pow 2)).div_const 4)
  have e : pmsBoundaryModel a b = (((fun t : ℝ => a - t) * pmsTailModel a b / fun x => √x) -
      fun x => ((fun x => √x) * pmsTailModel a b ^ 2) x / 4) := by
    funext x; simp only [pmsBoundaryModel, Pi.sub_apply, Pi.div_apply, Pi.mul_apply, Pi.pow_apply]
  rw [e]
  refine h.congr_deriv ?_
  have hsq : √t ^ 2 = t := Real.sq_sqrt ht.le
  simp only [pmsDensityModel, pmsQuadModel, Pi.mul_apply, Pi.pow_apply]
  generalize pmsTailModel a b t = J
  generalize √t = r at hr hsq ⊢
  subst hsq
  field_simp
  ring

theorem continuousOn_pmsTailModel (a b : ℝ) {u v : ℝ} (hu : 0 < u) :
    ContinuousOn (pmsTailModel a b) (Icc u v) := fun _ ht =>
  (hasDerivAt_pmsTailModel a b (hu.trans_le ht.1)).continuousAt.continuousWithinAt

theorem continuousOn_sqrt_inv {u v : ℝ} (hu : 0 < u) :
    ContinuousOn (fun t : ℝ => (√t)⁻¹) (Icc u v) := fun _ ht =>
  (Real.continuous_sqrt.continuousAt.inv₀
    (Real.sqrt_pos.mpr (hu.trans_le ht.1)).ne').continuousWithinAt

theorem continuousOn_pmsQuadModel (a b : ℝ) {u v : ℝ} (hu : 0 < u) :
    ContinuousOn (pmsQuadModel a b) (Icc u v) := by
  have hJ := continuousOn_pmsTailModel a b (v := v) hu
  have hs := continuousOn_sqrt_inv (v := v) hu
  have hpos : ∀ t ∈ Icc u v, 0 < t := fun t ht => hu.trans_le ht.1
  have e : pmsQuadModel a b = fun t => pmsTailModel a b t ^ 2 * (√t)⁻¹ / 8 +
      (a - t) ^ 2 * (t ^ 2)⁻¹ * (√t)⁻¹ := by
    funext t; simp only [pmsQuadModel]; ring
  rw [e]
  refine ((hJ.pow 2).mul hs |>.div_const 8).add
    ((((continuousOn_const.sub continuousOn_id).pow 2).mul
      ((continuousOn_id.pow 2).inv₀ fun t ht => pow_ne_zero 2 (hpos t ht).ne')).mul hs)

theorem continuousOn_pmsDensityModel (a b : ℝ) {u v : ℝ} (hu : 0 < u) :
    ContinuousOn (pmsDensityModel a b) (Icc u v) := by
  have e : pmsDensityModel a b = fun t => pmsTailModel a b t * (√t)⁻¹ + pmsQuadModel a b t := by
    funext t; simp only [pmsDensityModel, div_eq_mul_inv]
  rw [e]
  exact ((continuousOn_pmsTailModel a b hu).mul (continuousOn_sqrt_inv hu)).add
    (continuousOn_pmsQuadModel a b hu)

/-- **Integral of the model density.** -/
theorem integral_pmsDensityModel (a b : ℝ) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    ∫ t in u..v, pmsDensityModel a b t = pmsBoundaryModel a b u - pmsBoundaryModel a b v := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := pmsBoundaryModel a b)
    (f' := fun t => -pmsDensityModel a b t) (a := u) (b := v)
    (fun x hx => hasDerivAt_pmsBoundaryModel a b
      (hu.trans_le (by rw [uIcc_of_le huv] at hx; exact hx.1)))
    ((continuousOn_pmsDensityModel a b hu).neg.intervalIntegrable_of_Icc huv)
  rw [intervalIntegral.integral_neg] at h
  linarith

/-! ## Freezing between integers -/

theorem nat_floor_eq_of_mem {n : ℕ} {t : ℝ} (h1 : (n : ℝ) ≤ t) (h2 : t < n + 1) : ⌊t⌋₊ = n :=
  (Nat.floor_eq_iff ((Nat.cast_nonneg n).trans h1)).mpr ⟨h1, h2⟩

theorem psi_eq_of_mem {n : ℕ} {t : ℝ} (h1 : (n : ℝ) ≤ t) (h2 : t < n + 1) :
    Chebyshev.psi t = Chebyshev.psi n := by
  simp only [Chebyshev.psi, nat_floor_eq_of_mem h1 h2, Nat.floor_natCast]

theorem pmsMertens_eq_of_mem {n : ℕ} {t : ℝ} (h1 : (n : ℝ) ≤ t) (h2 : t < n + 1) :
    pmsMertens t = pmsMertens n := by
  simp only [pmsMertens, nat_floor_eq_of_mem h1 h2, Nat.floor_natCast]

theorem pmsTail_eq_model {n : ℕ} {t : ℝ} (h1 : (n : ℝ) ≤ t) (h2 : t < n + 1) :
    pmsTail t = pmsTailModel (Chebyshev.psi n) (pmsMertens n) t := by
  simp only [pmsTail, pmsTailModel, psi_eq_of_mem h1 h2, pmsMertens_eq_of_mem h1 h2]

theorem pmsErr_eq_model {n : ℕ} {t : ℝ} (h1 : (n : ℝ) ≤ t) (h2 : t < n + 1) :
    pmsErr t = Chebyshev.psi n - t := by
  simp only [pmsErr, psi_eq_of_mem h1 h2]

theorem pmsBoundary_eq_model {n : ℕ} {t : ℝ} (h1 : (n : ℝ) ≤ t) (h2 : t < n + 1) :
    pmsBoundary t = pmsBoundaryModel (Chebyshev.psi n) (pmsMertens n) t := by
  simp only [pmsBoundary, pmsBoundaryModel, pmsTail_eq_model h1 h2, pmsErr_eq_model h1 h2]

theorem pmsQuadDensity_eq_model {n : ℕ} {t : ℝ} (h1 : (n : ℝ) ≤ t) (h2 : t < n + 1) :
    pmsQuadDensity t = pmsQuadModel (Chebyshev.psi n) (pmsMertens n) t := by
  simp only [pmsQuadDensity, pmsQuadModel, pmsTail_eq_model h1 h2, pmsErr_eq_model h1 h2]

theorem pmsDensity_eq_model {n : ℕ} {t : ℝ} (h1 : (n : ℝ) ≤ t) (h2 : t < n + 1) :
    pmsDensity t = pmsDensityModel (Chebyshev.psi n) (pmsMertens n) t := by
  simp only [pmsDensity, pmsDensityModel, pmsTail_eq_model h1 h2, pmsQuadDensity_eq_model h1 h2]

/-- A function frozen to a continuous model on every `[n, n+1)`, `n ≥ 1`, is integrable on `[n, n+1]`. -/
theorem intervalIntegrable_step_of_frozen {F : ℝ → ℝ} (G : ℕ → ℝ → ℝ)
    (hG : ∀ n : ℕ, 1 ≤ n → ContinuousOn (G n) (Icc (n : ℝ) (n + 1)))
    (hFG : ∀ n : ℕ, ∀ t : ℝ, (n : ℝ) ≤ t → t < n + 1 → F t = G n t) {n : ℕ} (hn : 1 ≤ n) :
    IntervalIntegrable F volume (n : ℝ) (n + 1) := by
  have h1 : IntervalIntegrable (G n) volume (n : ℝ) (n + 1) :=
    (hG n hn).intervalIntegrable_of_Icc (by linarith)
  refine (intervalIntegrable_congr_ae ?_).mp h1
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [Measure.ae_ne volume ((n : ℝ) + 1)] with t hne ht
  rw [uIoc_of_le (by linarith)] at ht
  exact (hFG n t ht.1.le (lt_of_le_of_ne ht.2 hne)).symm

theorem intervalIntegrable_of_frozen {F : ℝ → ℝ} (G : ℕ → ℝ → ℝ)
    (hG : ∀ n : ℕ, 1 ≤ n → ContinuousOn (G n) (Icc (n : ℝ) (n + 1)))
    (hFG : ∀ n : ℕ, ∀ t : ℝ, (n : ℝ) ≤ t → t < n + 1 → F t = G n t) :
    ∀ N : ℕ, 1 ≤ N → IntervalIntegrable F volume 1 (N : ℝ) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    push_cast
    exact ih.trans (intervalIntegrable_step_of_frozen G hG hFG hN)

theorem intervalIntegrable_pmsDensity (N : ℕ) (hN : 1 ≤ N) :
    IntervalIntegrable pmsDensity volume 1 (N : ℝ) :=
  intervalIntegrable_of_frozen (fun n => pmsDensityModel (Chebyshev.psi n) (pmsMertens n))
    (fun n hn => continuousOn_pmsDensityModel _ _ (by exact_mod_cast hn))
    (fun _ _ h1 h2 => pmsDensity_eq_model h1 h2) N hN

theorem intervalIntegrable_pmsQuadDensity (N : ℕ) (hN : 1 ≤ N) :
    IntervalIntegrable pmsQuadDensity volume 1 (N : ℝ) :=
  intervalIntegrable_of_frozen (fun n => pmsQuadModel (Chebyshev.psi n) (pmsMertens n))
    (fun n hn => continuousOn_pmsQuadModel _ _ (by exact_mod_cast hn))
    (fun _ _ h1 h2 => pmsQuadDensity_eq_model h1 h2) N hN

/-! ## The integer identity -/

theorem pmsTail_natCast_succ (n : ℕ) :
    pmsTail ((n + 1 : ℕ) : ℝ) = pmsTailModel (Chebyshev.psi n) (pmsMertens n) ((n + 1 : ℕ) : ℝ) := by
  have hpsi : Chebyshev.psi ((n + 1 : ℕ) : ℝ) = Chebyshev.psi n + vonMangoldt (n + 1) := by
    simp only [Chebyshev.psi, Nat.floor_natCast]
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]
  have hM : pmsMertens ((n + 1 : ℕ) : ℝ) = pmsMertens n + vonMangoldt (n + 1) / ((n + 1 : ℕ) : ℝ) := by
    simp only [pmsMertens, Nat.floor_natCast]
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  simp only [pmsTail, pmsTailModel, hpsi, hM]
  field_simp
  ring

theorem pmsBoundary_natCast_succ (n : ℕ) :
    pmsBoundary ((n + 1 : ℕ) : ℝ) = pmsBoundaryModel (Chebyshev.psi n) (pmsMertens n) ((n + 1 : ℕ) : ℝ) +
      vonMangoldt (n + 1) * pmsTail ((n + 1 : ℕ) : ℝ) / √((n + 1 : ℕ) : ℝ) := by
  have hpsi : Chebyshev.psi ((n + 1 : ℕ) : ℝ) = Chebyshev.psi n + vonMangoldt (n + 1) := by
    simp only [Chebyshev.psi, Nat.floor_natCast]
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]
  simp only [pmsBoundary, pmsBoundaryModel, pmsErr, hpsi, pmsTail_natCast_succ n]
  ring

/-- **The identity at integers.** -/
theorem sum_vonMangoldt_mul_pmsTail_div_sqrt_nat (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc 0 N, vonMangoldt n * pmsTail n / √(n : ℝ) =
      pmsBoundary N - pmsBoundary 1 + ∫ t in (1 : ℝ)..N, pmsDensity t := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp [ArithmeticFunction.vonMangoldt_apply_one]
  | succ N hN ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), ih]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hstep : ∫ t in (N : ℝ)..((N + 1 : ℕ) : ℝ), pmsDensity t =
        pmsBoundaryModel (Chebyshev.psi N) (pmsMertens N) N -
          pmsBoundaryModel (Chebyshev.psi N) (pmsMertens N) ((N + 1 : ℕ) : ℝ) := by
      rw [← integral_pmsDensityModel _ _ hN0 (by push_cast; linarith)]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [Measure.ae_ne volume ((N : ℝ) + 1)] with t hne ht
      rw [uIoc_of_le (by push_cast; linarith)] at ht
      push_cast at ht
      exact pmsDensity_eq_model ht.1.le (lt_of_le_of_ne ht.2 hne)
    have hint1 := intervalIntegrable_pmsDensity N hN
    have hint2 : IntervalIntegrable pmsDensity volume (N : ℝ) ((N + 1 : ℕ) : ℝ) := by
      push_cast
      exact intervalIntegrable_step_of_frozen
        (fun n => pmsDensityModel (Chebyshev.psi n) (pmsMertens n))
        (fun n hn => continuousOn_pmsDensityModel _ _ (by exact_mod_cast hn))
        (fun _ _ h1 h2 => pmsDensity_eq_model h1 h2) hN
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2, hstep,
      pmsBoundary_natCast_succ N,
      show pmsBoundary (N : ℝ) = pmsBoundaryModel (Chebyshev.psi N) (pmsMertens N) N from
        pmsBoundary_eq_model le_rfl (by linarith)]
    ring

/-! ## The identity for real `X` -/

/-- **The prime-sampled tail identity.**  For `X ≥ 1`,
`Σ_{n≤X} Λ(n)J(n)/√n = H(X) − H(1) + ∫_1^X (J/√t + J²/(8√t) + E²/(t²√t)) dt`. -/
theorem sum_vonMangoldt_mul_pmsTail_div_sqrt {X : ℝ} (hX : 1 ≤ X) :
    ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, vonMangoldt n * pmsTail n / √(n : ℝ) =
      pmsBoundary X - pmsBoundary 1 + ∫ t in (1 : ℝ)..X, pmsDensity t := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌊X⌋₊ := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by rw [hN]; exact Nat.one_le_floor_iff _ |>.mpr hX
  have hNX : (N : ℝ) ≤ X := by rw [hN]; exact Nat.floor_le (by linarith)
  have hXN : X < N + 1 := by rw [hN]; exact Nat.lt_floor_add_one X
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [← hN, sum_vonMangoldt_mul_pmsTail_div_sqrt_nat N hN1]
  have hint2 : IntervalIntegrable pmsDensity volume (N : ℝ) X := by
    refine ((continuousOn_pmsDensityModel (Chebyshev.psi N) (pmsMertens N) (v := X)
      hN0).intervalIntegrable_of_Icc hNX).congr ?_
    intro t ht
    rw [uIoc_of_le hNX] at ht
    exact (pmsDensity_eq_model ht.1.le (ht.2.trans_lt hXN)).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_pmsDensity N hN1)
    hint2]
  have hstep : ∫ t in (N : ℝ)..X, pmsDensity t =
      pmsBoundaryModel (Chebyshev.psi N) (pmsMertens N) N -
        pmsBoundaryModel (Chebyshev.psi N) (pmsMertens N) X := by
    rw [← integral_pmsDensityModel _ _ hN0 hNX]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hNX] at ht
    exact pmsDensity_eq_model ht.1 (ht.2.trans_lt hXN)
  rw [hstep, pmsBoundary_eq_model hNX hXN, pmsBoundary_eq_model le_rfl (by linarith)]
  ring

/-- **The sign.**  Unconditionally, `Σ_{n≤X} Λ(n)J(n)/√n ≥ ∫_1^X J/√t + H(X) − H(1)`: the
mean-square part only pushes the prime-sampled sum up. -/
theorem integral_add_pmsBoundary_le_sum {X : ℝ} (hX : 1 ≤ X) :
    (∫ t in (1 : ℝ)..X, pmsTail t / √t) + pmsBoundary X - pmsBoundary 1 ≤
      ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, vonMangoldt n * pmsTail n / √(n : ℝ) := by
  rw [sum_vonMangoldt_mul_pmsTail_div_sqrt hX]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌊X⌋₊ := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by rw [hN]; exact Nat.one_le_floor_iff _ |>.mpr hX
  have hNX : (N : ℝ) ≤ X := by rw [hN]; exact Nat.floor_le (by linarith)
  have hXN : X < N + 1 := by rw [hN]; exact Nat.lt_floor_add_one X
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  -- integrability of the two parts on `[1, X]`
  have hlin : ∀ n : ℕ, 1 ≤ n → ContinuousOn
      (fun t => pmsTailModel (Chebyshev.psi n) (pmsMertens n) t / √t) (Icc (n : ℝ) (n + 1)) := by
    intro n hn
    have e : (fun t => pmsTailModel (Chebyshev.psi n) (pmsMertens n) t / √t) =
        fun t => pmsTailModel (Chebyshev.psi n) (pmsMertens n) t * (√t)⁻¹ := by
      funext t; rw [div_eq_mul_inv]
    rw [e]
    exact (continuousOn_pmsTailModel _ _ (by exact_mod_cast hn)).mul
      (continuousOn_sqrt_inv (by exact_mod_cast hn))
  have hlinFG : ∀ n : ℕ, ∀ t : ℝ, (n : ℝ) ≤ t → t < n + 1 →
      pmsTail t / √t = pmsTailModel (Chebyshev.psi n) (pmsMertens n) t / √t :=
    fun _ _ h1 h2 => by rw [pmsTail_eq_model h1 h2]
  have hL1 := intervalIntegrable_of_frozen _ hlin hlinFG N hN1
  have hL2 : IntervalIntegrable (fun t => pmsTail t / √t) volume (N : ℝ) X :=
    ((hlin N hN1).mono (Icc_subset_Icc le_rfl hXN.le)).intervalIntegrable_of_Icc hNX |>.congr
      (fun t ht => by
        rw [uIoc_of_le hNX] at ht
        exact (hlinFG N t ht.1.le (ht.2.trans_lt hXN)).symm)
  have hQ1 := intervalIntegrable_pmsQuadDensity N hN1
  have hQ2 : IntervalIntegrable pmsQuadDensity volume (N : ℝ) X :=
    ((continuousOn_pmsQuadModel (Chebyshev.psi N) (pmsMertens N) (v := X)
      hN0).intervalIntegrable_of_Icc hNX).congr (fun t ht => by
        rw [uIoc_of_le hNX] at ht
        exact (pmsQuadDensity_eq_model ht.1.le (ht.2.trans_lt hXN)).symm)
  have hL := hL1.trans hL2
  have hQ := hQ1.trans hQ2
  have hsplit : ∫ t in (1 : ℝ)..X, pmsDensity t =
      (∫ t in (1 : ℝ)..X, pmsTail t / √t) + ∫ t in (1 : ℝ)..X, pmsQuadDensity t :=
    intervalIntegral.integral_add hL hQ
  have hnonneg : 0 ≤ ∫ t in (1 : ℝ)..X, pmsQuadDensity t := by
    refine intervalIntegral.integral_nonneg hX fun t ht => ?_
    have ht0 : 0 < t := by linarith [ht.1]
    have hr : 0 < √t := Real.sqrt_pos.mpr ht0
    unfold pmsQuadDensity
    positivity
  rw [hsplit]
  linarith

/-! ## The link with the explicit formula -/

/-- **The prime side of the genus-kernel explicit formula is `−X J(X)` up to its constant.** -/
theorem lagPrimeSide_eq_neg_mul_pmsTail {X : ℝ} (hX : 0 < X) :
    lagPrimeSide X = ((-(X * pmsTail X) : ℝ) : ℂ) - Real.log (2 * Real.pi) + trivialZeroSeries X := by
  have hIcc : Finset.Icc 1 ⌊X⌋₊ = Finset.Ioc 0 ⌊X⌋₊ := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have e : -(X * pmsTail X) = (X - Chebyshev.psi X) +
      X * (pmsMertens X - Real.log X + Real.eulerMascheroniConstant) := by
    simp only [pmsTail]
    field_simp
    ring
  rw [lagPrimeSide, e, hIcc]
  simp only [pmsMertens]
  push_cast
  ring

/-- **The prime-weighted explicit-formula sum is concave in `E`.**  For `X ≥ 1`,
`Σ_{n≤X} Λ(n)(𝓔(n) + log 2π − Σ_j n^{−2j}/(2j(2j+1)))/n^{3/2} = −(H(X) − H(1) + ∫_1^X (J/√t + Q'))`,
with the mean-square density `Q' = J²/(8√t) + E²/(t²√t) ≥ 0`. -/
theorem sum_vonMangoldt_mul_lagPrimeSide_eq {X : ℝ} (hX : 1 ≤ X) :
    ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (vonMangoldt n : ℂ) *
        (lagPrimeSide n + Real.log (2 * Real.pi) - trivialZeroSeries n) / ((n : ℂ) * √(n : ℝ)) =
      -(((pmsBoundary X - pmsBoundary 1 + ∫ t in (1 : ℝ)..X, pmsDensity t : ℝ)) : ℂ) := by
  rw [← sum_vonMangoldt_mul_pmsTail_div_sqrt hX, Complex.ofReal_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : (0 : ℝ) < n := by
    have := (Finset.mem_Ioc.mp hn).1
    exact_mod_cast this
  have hr : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hn1
  rw [lagPrimeSide_eq_neg_mul_pmsTail hn1]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn1.ne'
  have hr0 : ((√(n : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp
  ring

end

end RHTower
