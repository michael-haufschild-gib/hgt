import GaloisForLFunctions.HTGeometry.GeometricPatternAlgebraicTie
import GaloisForLFunctions.HTGeometry.GeometricPolynomialFaceGap

/-!
# Periodic exact-level cascade from an ADE coefficient identity

This module connects the abstract finite geometric cascade to the actual regrouped Taylor
coefficient identity.  A finite translated pattern window is evaluated along one late phase-period
progression.  If its active complement has a uniform geometric valuation gap, the complement is
proved negligible from the project weight-mass bound, and every level polynomial in the window
vanishes identically.
-/

namespace GaloisForLFunctions

open Filter Finset MvPolynomial Polynomial PowerSeries Topology

noncomputable section

def periodicGeometricPatternPhase
    {M D : ℕ} (u : ℕ → ℂ) (c : ℝ) (q₀ K : ℕ)
    (p : Fin M → Fin (D + 1)) : ℂ :=
  ((Real.exp (-(D : ℝ) * c) : ℝ) : ℂ) *
    ∏ r : Fin M, u (windowShift q₀ K (r : ℕ)) ^ (p r : ℕ)

def periodicGeometricPatternWeight
    (n D K τ : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (q₀ period : ℕ) {M : ℕ} (p : Fin M → Fin (D + 1)) : ℂ[X] :=
  arithmeticProgressionPolynomial q₀ period
    (polynomialPatternWeightPoly n D K τ Q p)

def periodicGeometricLevelPolynomial
    (n D K τ : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (q₀ period : ℕ) {M : ℕ} (S : Finset (Fin M → Fin (D + 1)))
    (u : ℕ → ℂ) (c lam v : ℝ) : ℂ[X] :=
  exactGeometricLevelPolynomial S (geometricPatternValue lam)
    (periodicGeometricPatternWeight n D K τ Q q₀ period)
    (periodicGeometricPatternPhase u c q₀ K) v

def periodicADEOutsideRemainder
    (F : PowerSeries ℂ) (n D K τ : ℕ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (A lam c : ℝ) (q₀ period : ℕ)
    {M : ℕ} (S : Finset (Fin M → Fin (D + 1))) (k : ℕ) : ℂ :=
  let q := q₀ + period * k
  let T := activeAevalAtoms n (D * q + τ) Q
  let C := S.image (shiftedAtomPatternKey q K)
  ∑ ν ∈ T \ C,
    aevalWeight n (D * q + τ) Q ν *
      ((Real.exp (-atomValuation (fun i => A * lam ^ i + c) ν) : ℝ) : ℂ) *
        normalizedAtomPhase F (fun i => A * lam ^ i + c) ν

theorem periodicGeometricLevelPolynomial_eq_zero_of_activeComplement_gap
    {F : PowerSeries ℂ} {u : ℕ → ℂ}
    {A lam c : ℝ} (hA : 0 < A) (hlam : 1 < lam)
    (hcoeff : ∀ i, PowerSeries.coeff i F =
      ((Real.exp (-(A * lam ^ i + c)) : ℝ) : ℂ) * u i)
    (huNorm : ∀ i, ‖u i‖ = 1)
    {period T₀ q₀ : ℕ} (hperiod : 0 < period)
    (huPeriod : PeriodicFrom u period T₀)
    {n D K τ M : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hrel : aeval (formalJets n F) Q = 0)
    (S : Finset (Fin M → Fin (D + 1)))
    (hcount : ∀ p ∈ S, (∑ r, (p r : ℕ)) = D)
    (hq₀ : K + n ≤ q₀) (hT₀ : T₀ ≤ q₀ - K)
    (hactive : ∀ k p, p ∈ S →
      aevalWeight n (D * (q₀ + period * k) + τ) Q
        (shiftedAtomPatternKey (q₀ + period * k) K p) ≠ 0)
    (P : ℕ)
    (hmass : ∀ k,
      (∑ ν ∈ activeAevalAtoms n (D * (q₀ + period * k) + τ) Q,
        ‖aevalWeight n (D * (q₀ + period * k) + τ) Q ν‖) ≤
          (((q₀ + period * k : ℕ) : ℝ) ^ P))
    (hgap : ∀ v ∈ S.image (geometricPatternValue lam),
      ∃ gamma : ℝ, 0 < gamma ∧ ∀ k,
        ∀ ν ∈ activeAevalAtoms n (D * (q₀ + period * k) + τ) Q \
            S.image (shiftedAtomPatternKey (q₀ + period * k) K),
          A * lam ^ (q₀ - K) * v * (lam ^ period) ^ k +
              gamma * (lam ^ period) ^ k ≤
            atomValuation (fun i => A * lam ^ i + c) ν) :
    ∀ v : ℝ,
      periodicGeometricLevelPolynomial n D K τ Q q₀ period S u c lam v = 0 := by
  classical
  have hKq₀ : K ≤ q₀ := by omega
  have hbase : 0 < A * lam ^ (q₀ - K) :=
    mul_pos hA (pow_pos (zero_lt_one.trans hlam) _)
  have hratio : 1 < lam ^ period := one_lt_pow₀ hlam hperiod.ne'
  have hb : ∀ i, ‖PowerSeries.coeff i F‖ = Real.exp (-(A * lam ^ i + c)) := by
    intro i
    rw [hcoeff, norm_mul, huNorm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  let level : (Fin M → Fin (D + 1)) → ℝ := geometricPatternValue lam
  let weight : (Fin M → Fin (D + 1)) → ℂ[X] :=
    periodicGeometricPatternWeight n D K τ Q q₀ period
  let phase : (Fin M → Fin (D + 1)) → ℂ :=
    periodicGeometricPatternPhase u c q₀ K
  let remainder := periodicADEOutsideRemainder F n D K τ Q A lam c q₀ period S
  have hidentity : ∀ k : ℕ,
      (∑ p ∈ S, (weight p).eval (k : ℂ) * phase p *
        ((Real.exp (-(A * lam ^ (q₀ - K)) * level p *
          (lam ^ period) ^ k) : ℝ) : ℂ)) + remainder k = 0 := by
    intro k
    let q := q₀ + period * k
    let TA := activeAevalAtoms n (D * q + τ) Q
    let Ckey := S.image (shiftedAtomPatternKey q K)
    let f : (ℕ →₀ ℕ) → ℂ := fun ν =>
      aevalWeight n (D * q + τ) Q ν *
        ((Real.exp (-atomValuation (fun i => A * lam ^ i + c) ν) : ℝ) : ℂ) *
          normalizedAtomPhase F (fun i => A * lam ^ i + c) ν
    have hCkeyTA : Ckey ⊆ TA := by
      intro ν hν
      obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp hν
      rw [mem_activeAevalAtoms]
      have hw := hactive k p hpS
      exact ⟨mem_appearingAtoms_of_aevalWeight_ne_zero hw, hw⟩
    have hzero : ∑ ν ∈ TA, f ν = 0 := by
      simpa [TA, f, q] using normalized_active_aeval_coefficient_identity
        n (D * q + τ) F Q (fun i => A * lam ^ i + c) hrel 0
    have hsplit := Finset.sum_sdiff hCkeyTA (f := f)
    have hCeq : ∑ ν ∈ Ckey, f ν =
        ∑ p ∈ S, (weight p).eval (k : ℂ) * phase p *
          ((Real.exp (-(A * lam ^ (q₀ - K)) * level p *
            (lam ^ period) ^ k) : ℝ) : ℂ) := by
      rw [sum_image_shiftedAtomPatternKey S f]
      apply Finset.sum_congr rfl
      intro p hpS
      have hlarge : K + n ≤ q := by dsimp [q]; omega
      have hrem : geometricPatternRemainder (fun _ => c) q K p = D * c := by
        rw [geometricPatternRemainder]
        have hcountr : ∑ r, (p r : ℝ) = (D : ℝ) := by exact_mod_cast hcount p hpS
        rw [← Finset.sum_mul, hcountr]
      have hpow : lam ^ (q - K) = lam ^ (q₀ - K) * (lam ^ period) ^ k := by
        have hidx : q - K = (q₀ - K) + period * k := by dsimp [q]; omega
        rw [hidx, pow_add, pow_mul]
      rw [show f (shiftedAtomPatternKey q K p) =
        aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) *
          ((Real.exp (-atomValuation (fun i => A * lam ^ i + c)
            (shiftedAtomPatternKey q K p)) : ℝ) : ℂ) *
            normalizedAtomPhase F (fun i => A * lam ^ i + c)
              (shiftedAtomPatternKey q K p) by rfl]
      rw [aevalWeight_shiftedAtomPatternKey_eq_eval_poly n D K τ Q p
        (hcount p hpS) hlarge]
      rw [atomValuation_shiftedAtomPatternKey_geometric A lam (fun _ => c) q K p,
        hrem, hpow]
      rw [huPeriod.normalizedAtomPhase_shifted_add_mul hcoeff hKq₀ hT₀ p k]
      simp only [weight, periodicGeometricPatternWeight, phase,
        periodicGeometricPatternPhase, level, arithmeticProgressionPolynomial_eval]
      push_cast
      have hqcast : (q : ℂ) = (q₀ : ℂ) + (period : ℂ) * (k : ℂ) := by
        dsimp [q]
        push_cast
        ring
      rw [hqcast]
      have hexp :
          Complex.exp (-((A : ℂ) * ((lam : ℂ) ^ (q₀ - K) *
              ((lam : ℂ) ^ period) ^ k) * (geometricPatternValue lam p : ℂ) +
                (D : ℂ) * (c : ℂ))) =
            Complex.exp (-(D : ℂ) * (c : ℂ)) *
              Complex.exp (-((A : ℂ) * (lam : ℂ) ^ (q₀ - K)) *
                (geometricPatternValue lam p : ℂ) * ((lam : ℂ) ^ period) ^ k) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      rw [hexp]
      ring
    have hremEq : ∑ ν ∈ TA \ Ckey, f ν = remainder k := by
      rfl
    rw [← hCeq, ← hremEq]
    calc
      (∑ ν ∈ Ckey, f ν) + ∑ ν ∈ TA \ Ckey, f ν =
          (∑ ν ∈ TA \ Ckey, f ν) + ∑ ν ∈ Ckey, f ν := add_comm _ _
      _ = ∑ ν ∈ TA, f ν := hsplit
      _ = 0 := hzero
  have hremainder : ∀ v ∈ S.image level,
      Tendsto (fun k : ℕ =>
        ((Real.exp ((A * lam ^ (q₀ - K)) * v *
          (lam ^ period) ^ k) : ℝ) : ℂ) * remainder k)
        atTop (nhds 0) := by
    intro v hv
    obtain ⟨gamma, hgamma, hgapv⟩ := hgap v (by simpa [level] using hv)
    have hbound : ∀ k,
        ‖((Real.exp ((A * lam ^ (q₀ - K)) * v *
            (lam ^ period) ^ k) : ℝ) : ℂ) * remainder k‖ ≤
          (((q₀ + period * k : ℕ) : ℝ) ^ P) *
            Real.exp (-gamma * (lam ^ period) ^ k) := by
      intro k
      let q := q₀ + period * k
      let TA := activeAevalAtoms n (D * q + τ) Q
      let Ckey := S.image (shiftedAtomPatternKey q K)
      calc
        ‖((Real.exp ((A * lam ^ (q₀ - K)) * v *
              (lam ^ period) ^ k) : ℝ) : ℂ) * remainder k‖ ≤
            ∑ ν ∈ TA \ Ckey,
              ‖aevalWeight n (D * q + τ) Q ν‖ *
                Real.exp (-gamma * (lam ^ period) ^ k) := by
          simp only [remainder, periodicADEOutsideRemainder]
          rw [Finset.mul_sum]
          calc
            ‖∑ ν ∈ TA \ Ckey,
                ((Real.exp ((A * lam ^ (q₀ - K)) * v *
                    (lam ^ period) ^ k) : ℝ) : ℂ) *
                  (aevalWeight n (D * q + τ) Q ν *
                    ((Real.exp (-atomValuation (fun i => A * lam ^ i + c) ν) : ℝ) : ℂ) *
                      normalizedAtomPhase F (fun i => A * lam ^ i + c) ν)‖ ≤
                ∑ ν ∈ TA \ Ckey,
                  ‖((Real.exp ((A * lam ^ (q₀ - K)) * v *
                      (lam ^ period) ^ k) : ℝ) : ℂ) *
                    (aevalWeight n (D * q + τ) Q ν *
                      ((Real.exp (-atomValuation (fun i => A * lam ^ i + c) ν) : ℝ) : ℂ) *
                        normalizedAtomPhase F (fun i => A * lam ^ i + c) ν)‖ :=
              norm_sum_le _ _
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro ν hν
              have hgapν := hgapv k ν (by simpa [TA, Ckey, q] using hν)
              rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
                Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
                abs_of_pos (Real.exp_pos _), norm_normalizedAtomPhase F _ hb ν]
              have hexp :
                  Real.exp (A * lam ^ (q₀ - K) * v * (lam ^ period) ^ k) *
                      Real.exp (-atomValuation (fun i => A * lam ^ i + c) ν) ≤
                    Real.exp (-gamma * (lam ^ period) ^ k) := by
                rw [← Real.exp_add]
                apply Real.exp_le_exp.mpr
                linarith
              calc
                Real.exp (A * lam ^ (q₀ - K) * v * (lam ^ period) ^ k) *
                    (‖aevalWeight n (D * q + τ) Q ν‖ *
                      Real.exp (-atomValuation (fun i => A * lam ^ i + c) ν) * 1) =
                    ‖aevalWeight n (D * q + τ) Q ν‖ *
                      (Real.exp (A * lam ^ (q₀ - K) * v * (lam ^ period) ^ k) *
                        Real.exp (-atomValuation (fun i => A * lam ^ i + c) ν)) := by ring
                _ ≤ ‖aevalWeight n (D * q + τ) Q ν‖ *
                    Real.exp (-gamma * (lam ^ period) ^ k) :=
                  mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
        _ ≤ (∑ ν ∈ TA, ‖aevalWeight n (D * q + τ) Q ν‖) *
              Real.exp (-gamma * (lam ^ period) ^ k) := by
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
            (fun _ _ _ => mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))
        _ ≤ (((q₀ + period * k : ℕ) : ℝ) ^ P) *
              Real.exp (-gamma * (lam ^ period) ^ k) := by
          apply mul_le_mul_of_nonneg_right (by simpa [TA, q] using hmass k)
            (Real.exp_nonneg _)
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun k => norm_nonneg _
    · exact Filter.Eventually.of_forall hbound
    · exact tendsto_add_mul_pow_mul_exp_neg_geometric hratio hgamma q₀ period P
  simpa [periodicGeometricLevelPolynomial, level, weight, phase] using
    finite_exactGeometricLevel_cascade_of_remainder S level weight phase hbase hratio
      remainder hidentity hremainder

end

end GaloisForLFunctions
