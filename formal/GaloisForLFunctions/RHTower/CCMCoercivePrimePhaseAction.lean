import GaloisForLFunctions.RHTower.CCMPrimeCliqueCoercivity
import GaloisForLFunctions.RHTower.CCMFinitePhaseNoether

/-!
# Positive arithmetic phase actions in unbounded finite dimensions

The constructed prime packets are linearly independent over the reals. Their
finite phase action has a positive, mass-normalized energy floor at every
phase, together with the previously proved exact Noether symmetry and charge.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace RHTower

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ccmFinite_collective_gap_linearIndependent (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) {d : ℝ} (hd : 0 < d)
    (hgap : ∀ x : ι → ℝ, d * (∑ i, x i ^ 2) +
      finiteSignedCliqueCorrection (fun i j => ccmWeilRealPolar a (u i) (u j)) x ≤
      ccmRestrictedWeilSourceQuadratic a (∑ i, (x i : ℂ) • u i)) :
    LinearIndependent ℝ u := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro x hx i
  have hzero : (∑ j, (x j : ℂ) • u j) = 0 := by
    convert! hx using 1
  have h := hgap x
  rw [hzero, ← ccmWeilRealPolar_self, ccmWeilRealPolar_zero_left] at h
  have hcorr := finiteSignedCliqueCorrection_nonneg (fun i j => ccmWeilRealPolar a (u i) (u j)) x
  have hs : (∑ j, x j ^ 2) ≤ 0 := by nlinarith only [h, hcorr, hd]
  have hi : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  nlinarith only [hs, hi, sq_nonneg (x i)]

omit [DecidableEq ι] in
theorem ccmFinite_collective_gap_phase_floor (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) (d : ℝ)
    (hgap : ∀ x : ι → ℝ, d * (∑ i, x i ^ 2) +
      finiteSignedCliqueCorrection (fun i j => ccmWeilRealPolar a (u i) (u j)) x ≤
      ccmRestrictedWeilSourceQuadratic a (∑ i, (x i : ℂ) • u i)) (theta : ι → ℝ) :
    d * Fintype.card ι +
      finiteSignedCliqueGain (fun i j => ccmWeilRealPolar a (u i) (u j)) *
        ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 2) +
          (∑ i, Real.cos (theta i)) ^ 2 + (∑ i, Real.sin (theta i)) ^ 2) ≤
      ccmWeilFinitePhaseEnergy a u theta := by
  have hc := hgap (fun i => Real.cos (theta i))
  have hs := hgap (fun i => Real.sin (theta i))
  have hmass : (∑ i, Real.cos (theta i) ^ 2) + (∑ i, Real.sin (theta i) ^ 2) = Fintype.card ι := by
    rw [← Finset.sum_add_distrib]
    have he (i : ι) : Real.cos (theta i) ^ 2 + Real.sin (theta i) ^ 2 = 1 := by
      linarith only [Real.sin_sq_add_cos_sq (theta i)]
    simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hd := congrArg (fun s : ℝ => d * s) hmass
  have hg := congrArg (fun s : ℝ =>
    finiteSignedCliqueGain (fun i j => ccmWeilRealPolar a (u i) (u j)) *
      ((Fintype.card ι : ℝ) - 2) * s) hmass
  unfold finiteSignedCliqueCorrection at hc hs
  unfold ccmWeilFinitePhaseEnergy
  nlinarith only [hc, hs, hd, hg]

theorem ccmFinite_collective_gap_phase_floor_basic (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) (d : ℝ)
    (hgap : ∀ x : ι → ℝ, d * (∑ i, x i ^ 2) +
      finiteSignedCliqueCorrection (fun i j => ccmWeilRealPolar a (u i) (u j)) x ≤
      ccmRestrictedWeilSourceQuadratic a (∑ i, (x i : ℂ) • u i)) (theta : ι → ℝ) :
    d * Fintype.card ι ≤ ccmWeilFinitePhaseEnergy a u theta := by
  have hc := hgap (fun i => Real.cos (theta i))
  have hs := hgap (fun i => Real.sin (theta i))
  have hcc := finiteSignedCliqueCorrection_nonneg (fun i j => ccmWeilRealPolar a (u i) (u j))
    (fun i => Real.cos (theta i))
  have hsc := finiteSignedCliqueCorrection_nonneg (fun i j => ccmWeilRealPolar a (u i) (u j))
    (fun i => Real.sin (theta i))
  have hmass : (∑ i, Real.cos (theta i) ^ 2) + (∑ i, Real.sin (theta i) ^ 2) = Fintype.card ι := by
    rw [← Finset.sum_add_distrib]
    have he (i : ι) : Real.cos (theta i) ^ 2 + Real.sin (theta i) ^ 2 = 1 := by
      linarith only [Real.sin_sq_add_cos_sq (theta i)]
    simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hd := congrArg (fun s : ℝ => d * s) hmass
  unfold ccmWeilFinitePhaseEnergy
  nlinarith only [hc, hs, hcc, hsc, hd]

omit [Fintype ι] [DecidableEq ι] in
theorem exists_ccmPrimeClique_positive_phase_action :
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
        LinearIndependent ℝ f ∧
        (∀ theta : Option (Fin n) → ℝ,
          (kappa * mu) * (n + 1) ≤ ccmWeilFinitePhaseEnergy a f theta ∧
          0 < ccmWeilFinitePhaseEnergy a f theta) ∧
        (∀ c omega t : ℝ, ∀ i : Option (Fin n),
          HasDerivAt (deriv (ccmWeilTriangleUniformPhase c omega))
            (ccmWeilFinitePhaseTorque a f (fun _ => ccmWeilTriangleUniformPhase c omega t) i) t) := by
  classical
  obtain ⟨kappa, hk, hfamily⟩ := exists_cofinal_ccmPrimeClique_coercivity
  refine ⟨kappa, hk, fun N n => ?_⟩
  obtain ⟨p, r, mu, a, u, v, hr, hm, hp, hpair, hsu, hsv, hmass, _, _, hgap⟩ := hfamily N n
  let f := ccmWeilPrimeCliqueFamily u.toCCMFormVector (fun i => (v i).toCCMFormVector)
  have hd : 0 < kappa * mu := mul_pos hk hm
  refine ⟨p, r, mu, a, u, v, hr, hm, hp, hpair, hsu, hsv, hmass,
    ccmFinite_collective_gap_linearIndependent a f hd hgap, ?_, ?_⟩
  · intro theta
    have h := ccmFinite_collective_gap_phase_floor_basic a f (kappa * mu) hgap theta
    have h' : (kappa * mu) * (n + 1) ≤ ccmWeilFinitePhaseEnergy a f theta := by
      simpa only [Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using h
    exact ⟨h', (mul_pos hd (by positivity)).trans_le h'⟩
  · intro c omega t i
    exact ccmWeilFinitePhase_uniform_rotation_newton a f c omega t i

end RHTower
