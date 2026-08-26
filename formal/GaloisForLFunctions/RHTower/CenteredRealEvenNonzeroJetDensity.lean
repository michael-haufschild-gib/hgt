import GaloisForLFunctions.RHTower.CenteredRealEvenFiniteJetDensity

/-!
# Nonzero repair inside centered real-even finite-jet fibers

The product of a finite Hermite modulus with all its sign/Schwarz transforms is a nonzero
real-even, Schwarz-real polynomial vanishing to every prescribed depth. Small multiples repair a
zero approximating polynomial without changing any jet or the compact-open limit.
-/

open Complex Filter Set Topology Polynomial Function
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Symmetry norm of a finite Hermite modulus. -/
def finiteHermiteSymmetryVanishingPolynomial {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (m : ι → ℕ) : Polynomial ℂ :=
  let M := finiteHermiteModulus a m
  M * polynomialNegPullback M * polynomialConj M *
    polynomialConj (polynomialNegPullback M)

theorem finiteHermiteSymmetryVanishingPolynomial_eval_neg
    {ι : Type*} [Fintype ι] (a : ι → ℂ) (m : ι → ℕ) (z : ℂ) :
    (finiteHermiteSymmetryVanishingPolynomial a m).eval (-z) =
      (finiteHermiteSymmetryVanishingPolynomial a m).eval z := by
  simp [finiteHermiteSymmetryVanishingPolynomial, eval_polynomialNegPullback,
    eval_polynomialConj]
  ring

theorem finiteHermiteSymmetryVanishingPolynomial_eval_conj
    {ι : Type*} [Fintype ι] (a : ι → ℂ) (m : ι → ℕ) (z : ℂ) :
    (finiteHermiteSymmetryVanishingPolynomial a m).eval ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) ((finiteHermiteSymmetryVanishingPolynomial a m).eval z) := by
  simp [finiteHermiteSymmetryVanishingPolynomial, eval_polynomialNegPullback,
    eval_polynomialConj, map_mul]
  ring

theorem polynomialNegPullback_ne_zero {P : Polynomial ℂ} (hP : P ≠ 0) :
    polynomialNegPullback P ≠ 0 := by
  intro h
  apply hP
  apply Polynomial.funext
  intro z
  have hz := congrArg (fun Q : Polynomial ℂ => Q.eval (-z)) h
  simpa using hz

theorem polynomialConj_ne_zero {P : Polynomial ℂ} (hP : P ≠ 0) :
    polynomialConj P ≠ 0 := by
  intro h
  apply hP
  rw [polynomialConj] at h
  exact (Polynomial.map_eq_zero_iff (f := starRingEnd ℂ)
    (fun x y hxy => by simpa using congrArg (starRingEnd ℂ) hxy)).mp h

theorem finiteHermiteSymmetryVanishingPolynomial_ne_zero
    {ι : Type*} [Fintype ι] (a : ι → ℂ) (m : ι → ℕ) :
    finiteHermiteSymmetryVanishingPolynomial a m ≠ 0 := by
  have hM : finiteHermiteModulus a m ≠ 0 := (finiteHermiteModulus_monic a m).ne_zero
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hM (polynomialNegPullback_ne_zero hM))
    (polynomialConj_ne_zero hM))
    (polynomialConj_ne_zero (polynomialNegPullback_ne_zero hM))

theorem finiteHermiteSymmetryVanishingPolynomial_jet_zero
    {ι : Type*} [Fintype ι] (a : ι → ℂ) (m : ι → ℕ)
    (i : ι) {k : ℕ} (hk : k < m i) :
    (derivative^[k] (finiteHermiteSymmetryVanishingPolynomial a m)).eval (a i) = 0 := by
  let M := finiteHermiteModulus a m
  have hpowM : (X - C (a i)) ^ m i ∣ M := power_linear_dvd_finiteHermiteModulus a m i
  have hMS : M ∣ finiteHermiteSymmetryVanishingPolynomial a m := by
    refine ⟨polynomialNegPullback M * polynomialConj M *
      polynomialConj (polynomialNegPullback M), ?_⟩
    simp only [finiteHermiteSymmetryVanishingPolynomial, M]
    ring
  have hdiv : (X - C (a i)) ^ m i ∣
      finiteHermiteSymmetryVanishingPolynomial a m - 0 := by
    simpa using hpowM.trans hMS
  simpa using eval_iterate_derivative_eq_of_power_linear_dvd_sub hdiv hk

/-- Nonzero real scale tending to zero. -/
def compactOpenRepairScale (n : ℕ) : ℂ := (((n : ℂ) + 1)⁻¹)

theorem compactOpenRepairScale_ne_zero (n : ℕ) : compactOpenRepairScale n ≠ 0 := by
  rw [compactOpenRepairScale]
  apply inv_ne_zero
  intro h
  have hre : (n : ℝ) + 1 = 0 := by
    simpa using congrArg Complex.re h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem compactOpenRepairScale_conj (n : ℕ) :
    (starRingEnd ℂ) (compactOpenRepairScale n) = compactOpenRepairScale n := by
  simp [compactOpenRepairScale]

theorem compactOpenRepairScale_tendsto_zero :
    Tendsto compactOpenRepairScale atTop (𝓝 0) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hadd := Filter.tendsto_atTop_add_const_right atTop 1 hcast
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hadd
  have hcomplex := (Complex.continuous_ofReal.tendsto 0).comp hinv
  change Tendsto (fun n : ℕ => ((n : ℂ) + 1)⁻¹) atTop (𝓝 0)
  simpa [Function.comp_def] using hcomplex

theorem constMulPolynomial_tendstoLocallyUniformly_zero
    {c : ℕ → ℂ} (hc : Tendsto c atTop (𝓝 0)) (S : Polynomial ℂ) :
    TendstoLocallyUniformly (fun n z => (C (c n) * S).eval z) (fun _ => 0) atTop := by
  have hs := hc.smul_const (deningerCompactOpenPolynomial S)
  have hsval := (continuous_subtype_val.tendsto
    ((0 : ℂ) • deningerCompactOpenPolynomial S)).comp hs
  have hloc := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hsval
  convert hloc using 1
  · funext n z
    simp [deningerCompactOpenPolynomial, Polynomial.eval_mul]
  · funext z
    simp

/-- Replace every zero approximant while retaining symmetry, jets, and compact-open convergence. -/
theorem exists_nonzero_realEvenPolynomial_compactOpen_approximation_with_finiteJets
    {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (m : ι → ℕ) {f : ℂ → ℂ}
    {P : ℕ → Polynomial ℂ}
    (heven : ∀ n z, (P n).eval (-z) = (P n).eval z)
    (hschwarz : ∀ n z, (P n).eval ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) ((P n).eval z))
    (hjets : ∀ n i k, k < m i →
      (derivative^[k] (P n)).eval (a i) = iteratedDeriv k f (a i))
    (hconv : TendstoLocallyUniformly (fun n z => (P n).eval z) f atTop) :
    ∃ Q : ℕ → Polynomial ℂ,
      (∀ n, Q n ≠ 0) ∧
      (∀ n z, (Q n).eval (-z) = (Q n).eval z) ∧
      (∀ n z, (Q n).eval ((starRingEnd ℂ) z) =
        (starRingEnd ℂ) ((Q n).eval z)) ∧
      (∀ n i k, k < m i →
        (derivative^[k] (Q n)).eval (a i) = iteratedDeriv k f (a i)) ∧
      TendstoLocallyUniformly (fun n z => (Q n).eval z) f atTop := by
  let S := finiteHermiteSymmetryVanishingPolynomial a m
  let d : ℕ → ℂ := fun n => if P n = 0 then compactOpenRepairScale n else 0
  have hd : Tendsto d atTop (𝓝 0) := by
    have hscaleNorm : Tendsto (fun n => ‖compactOpenRepairScale n‖) atTop (𝓝 0) := by
      simpa using compactOpenRepairScale_tendsto_zero.norm
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg (d n))
      (Eventually.of_forall fun n => ?_) hscaleNorm
    by_cases hPn : P n = 0
    · simp [d, hPn]
    · simp [d, hPn]
  have hdconj (n : ℕ) : (starRingEnd ℂ) (d n) = d n := by
    by_cases hPn : P n = 0
    · simp [d, hPn, compactOpenRepairScale_conj]
    · simp [d, hPn]
  have hsmall := constMulPolynomial_tendstoLocallyUniformly_zero hd S
  let Q : ℕ → Polynomial ℂ := fun n => P n + C (d n) * S
  refine ⟨Q, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    by_cases hPn : P n = 0
    · simp only [Q, hPn, zero_add]
      exact mul_ne_zero (C_ne_zero.mpr (by
        simp [d, hPn, compactOpenRepairScale_ne_zero]))
        (finiteHermiteSymmetryVanishingPolynomial_ne_zero a m)
    · have hdn : d n = 0 := by simp [d, hPn]
      simpa [Q, hdn] using hPn
  · intro n z
    simp only [Q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    rw [heven, finiteHermiteSymmetryVanishingPolynomial_eval_neg]
  · intro n z
    simp only [Q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, map_add, map_mul]
    rw [hschwarz, finiteHermiteSymmetryVanishingPolynomial_eval_conj, hdconj]
  · intro n i k hk
    change (derivative^[k] (P n + C (d n) * S)).eval (a i) = _
    rw [iterate_map_add, Polynomial.eval_add, iterate_derivative_C_mul,
      Polynomial.eval_mul, Polynomial.eval_C,
      finiteHermiteSymmetryVanishingPolynomial_jet_zero a m i hk, mul_zero, add_zero]
    exact hjets n i k hk
  · have hadd := hconv.add hsmall
    convert hadd using 1
    · funext n z
      simp [Q]
    · funext z
      simp

end

end RHTower
