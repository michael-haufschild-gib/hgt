import GaloisForLFunctions.RHTower.CCMPrimeCliqueCoercivity

/-!
# Full complex positivity and a literal arithmetic phase action

The actual prime-packet spaces have a positive gap for arbitrary complex
coefficients. Their complex dimensions are unbounded, and their phase
potential equals the full Weil energy of one complex phase source.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace RHTower

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem ccmFinite_realGram_complex_collective_gap (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a)
    (hreal : ∀ i j, (ccmRestrictedWeilForm a (u i) (u j)).im = 0) (d : ℝ)
    (hgap : ∀ x : ι → ℝ, d * (∑ i, x i ^ 2) +
      finiteSignedCliqueCorrection (fun i j => ccmWeilRealPolar a (u i) (u j)) x ≤
      ccmRestrictedWeilSourceQuadratic a (∑ i, (x i : ℂ) • u i)) (z : ι → ℂ) :
    d * (∑ i, ‖z i‖ ^ 2) +
      finiteSignedCliqueCorrection (fun i j => ccmWeilRealPolar a (u i) (u j)) (fun i => (z i).re) +
      finiteSignedCliqueCorrection (fun i j => ccmWeilRealPolar a (u i) (u j)) (fun i => (z i).im) ≤
      ccmRestrictedWeilSourceQuadratic a (∑ i, z i • u i) := by
  have hr := hgap (fun i => (z i).re)
  have hi := hgap (fun i => (z i).im)
  have hm : (∑ i, (z i).re ^ 2) + (∑ i, (z i).im ^ 2) = ∑ i, ‖z i‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hd := congrArg (fun s : ℝ => d * s) hm
  rw [ccmRestrictedWeilSourceQuadratic_complex_sum_realImag a u hreal]
  nlinarith only [hr, hi, hd]

omit [DecidableEq ι] in
theorem ccmFinite_complex_gap_linearIndependent (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) {d : ℝ} (hd : 0 < d)
    (hgap : ∀ z : ι → ℂ, d * (∑ i, ‖z i‖ ^ 2) ≤
      ccmRestrictedWeilSourceQuadratic a (∑ i, z i • u i)) :
    LinearIndependent ℂ u := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro z hz i
  have h := hgap z
  rw [hz, ← ccmWeilRealPolar_self, ccmWeilRealPolar_zero_left] at h
  have hs : (∑ j, ‖z j‖ ^ 2) ≤ 0 := by nlinarith only [h, hd]
  have hi : ‖z i‖ ^ 2 ≤ ∑ j, ‖z j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖z j‖) (Finset.mem_univ i)
  apply norm_eq_zero.mp
  nlinarith only [hs, hi, sq_nonneg ‖z i‖, norm_nonneg (z i)]

omit [Fintype ι] [DecidableEq ι] in
theorem exists_cofinal_ccmComplexPrimeClique_coercivity :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ N n : ℕ,
      ∃ (p : Fin n → ℕ) (r mu : ℝ) (a : SuzukiPositiveAperture)
        (u : CCMComplexSmoothInteriorSource a) (v : Fin n → CCMComplexSmoothInteriorSource a),
        0 < r ∧ 0 < mu ∧
        (∀ i, N ≤ p i ∧ Nat.Prime (p i)) ∧
        (∀ i j, i < j → 2 * p i < p j) ∧
        Function.support u = Metric.ball 0 r ∧
        (∀ i, Function.support (v i) = Metric.ball (Real.log (p i)) r) ∧
        let f := ccmWeilPrimeCliqueFamily u.toCCMFormVector (fun i => (v i).toCCMFormVector)
        (∀ i, ‖ccmArchimedeanFormEmbedding a (f i)‖ ^ 2 = mu) ∧
        (∀ i j, i ≠ j → 0 < ccmWeilRealPolar a (f i) (f j)) ∧
        LinearIndependent ℂ f ∧
        (∀ z : Option (Fin n) → ℂ,
          (kappa * mu) * (∑ i, ‖z i‖ ^ 2) +
            finiteSignedCliqueCorrection (fun i j => ccmWeilRealPolar a (f i) (f j)) (fun i => (z i).re) +
            finiteSignedCliqueCorrection (fun i j => ccmWeilRealPolar a (f i) (f j)) (fun i => (z i).im) ≤
          ccmRestrictedWeilSourceQuadratic a (∑ i, z i • f i)) ∧
        (∀ theta : Option (Fin n) → ℝ,
          let q := ccmRestrictedWeilSourceQuadratic a
            (∑ i, Complex.exp ((theta i : ℂ) * Complex.I) • f i)
          q = ccmWeilFinitePhaseEnergy a f theta ∧
          (kappa * mu) * (n + 1) ≤ q ∧ 0 < q) := by
  classical
  obtain ⟨kappa, hk, hfamily⟩ := exists_cofinal_ccmPrimeClique_coercivity
  refine ⟨kappa, hk, fun N n => ?_⟩
  obtain ⟨p, r, mu, a, u, v, hr, hm, hp, hpair, hsu, hsv, hmass, hpos, hreal, hgap⟩ := hfamily N n
  let f := ccmWeilPrimeCliqueFamily u.toCCMFormVector (fun i => (v i).toCCMFormVector)
  have hd : 0 < kappa * mu := mul_pos hk hm
  have hcomplex (z : Option (Fin n) → ℂ) :=
    ccmFinite_realGram_complex_collective_gap a f hreal (kappa * mu) hgap z
  have hbasic (z : Option (Fin n) → ℂ) : (kappa * mu) * (∑ i, ‖z i‖ ^ 2) ≤
      ccmRestrictedWeilSourceQuadratic a (∑ i, z i • f i) := by
    have h := hcomplex z
    have hr := finiteSignedCliqueCorrection_nonneg (fun i j => ccmWeilRealPolar a (f i) (f j))
      (fun i => (z i).re)
    have hi := finiteSignedCliqueCorrection_nonneg (fun i j => ccmWeilRealPolar a (f i) (f j))
      (fun i => (z i).im)
    linarith only [h, hr, hi]
  refine ⟨p, r, mu, a, u, v, hr, hm, hp, hpair, hsu, hsv, hmass, hpos,
    ccmFinite_complex_gap_linearIndependent a f hd hbasic, hcomplex, ?_⟩
  intro theta
  dsimp only
  refine ⟨(ccmWeilFinitePhaseEnergy_eq_complex_phase a f hreal theta).symm, ?_⟩
  have h := hbasic (fun i => Complex.exp ((theta i : ℂ) * Complex.I))
  simp only [Complex.norm_exp_ofReal_mul_I, one_pow, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_option,
    Fintype.card_fin, Nat.cast_add, Nat.cast_one] at h
  exact ⟨h, (mul_pos hd (by positivity)).trans_le h⟩

end RHTower
