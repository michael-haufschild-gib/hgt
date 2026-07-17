import GaloisForLFunctions.HTGeometry.GeometricPeriodicADELevelCascade
import GaloisForLFunctions.HTGeometry.PolynomialTaylorProuhetPhaseLock

/-!
# Unconditional least-level exactness for periodic geometric phases

For an actual integer ADE relation with one surviving top-degree pattern, the project confinement
theorem constructs a finite least geometric face and an exponentially separated active complement.
Along a sufficiently late phase-period progression, the full ADE level-cascade theorem therefore
forces the least grouped level polynomial to vanish identically.
-/

namespace GaloisForLFunctions

open Filter Finset MvPolynomial Polynomial PowerSeries Topology

noncomputable section

set_option maxHeartbeats 2000000 in
theorem exists_periodicGeometric_leastLevelPolynomial_eq_zero
    {F : PowerSeries ℂ} {u : ℕ → ℂ}
    {A lam c : ℝ} (hA : 0 < A) (hlam : 1 < lam)
    (hbpos : ∀ i, 0 < A * lam ^ i + c)
    (hcoeff : ∀ i, PowerSeries.coeff i F =
      ((Real.exp (-(A * lam ^ i + c)) : ℝ) : ℂ) * u i)
    (huNorm : ∀ i, ‖u i‖ = 1)
    {period T₀ : ℕ} (hperiod : 0 < period)
    (huPeriod : PeriodicFrom u period T₀)
    {n D K₀ τ M₀ : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hrel : aeval (formalJets n F) Q = 0)
    (hD : 0 < D) (hDmax : D = magnitudeMaxJetDegree n Q)
    (p₀ : Fin M₀ → Fin (D + 1))
    (hcount₀ : (∑ r, (p₀ r : ℕ)) = D)
    (hw₀ : ∀ᶠ q : ℕ in atTop,
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K₀ p₀) ≠ 0) :
    ∃ K M q₀ : ℕ,
      let S := polynomialPatternSurvivors n D K τ Q M
      let Face := geometricPatternFace lam S
      S.Nonempty ∧ q₀ ≥ K ∧
        periodicGeometricLevelPolynomial n D K τ Q q₀ period Face u c lam
          (geometricPatternMinimum lam S) = 0 := by
  classical
  have hc : Tendsto (fun _ : ℕ => c) atTop (nhds c) := tendsto_const_nhds
  have hgrowth : UniformGeometricGrowth (fun i => A * lam ^ i + c) :=
    uniformGeometricGrowth_hierarchical hlam hA
      (isLittleO_constPow_of_tendsto hlam hc)
  have hw₀' : ∀ᶠ q : ℕ in atTop,
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K₀ p₀) ≠ 0 := hw₀
  obtain ⟨K, M, hS, gamma, hgamma, hgap⟩ :=
    exists_geometricPolynomialFace_activeAtom_gap hA hlam hc hbpos hgrowth
      Q hD hDmax p₀ hcount₀ hw₀'
  let S := polynomialPatternSurvivors n D K τ Q M
  let Face := geometricPatternFace lam S
  have hactiveEv := polynomialPatternSurvivors_eventually_weight_ne_zero
    (n := n) (D := D) (K := K) (τ := τ) (M := M) Q
  obtain ⟨P, hmassEv⟩ := exists_aevalWeight_mass_natPow_bound n D τ Q
  have habsorb : ∀ᶠ t : ℕ in atTop,
      -(D : ℝ) * c ≤ gamma / 2 * lam ^ t := by
    have htop : Tendsto (fun t : ℕ => gamma / 2 * lam ^ t) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt hlam).const_mul_atTop (by positivity)
    exact htop.eventually_ge_atTop (-(D : ℝ) * c)
  have hactiveShift := (tendsto_add_atTop_nat K).eventually hactiveEv
  have hmassShift := (tendsto_add_atTop_nat K).eventually hmassEv
  obtain ⟨Qa, hQa⟩ := Filter.eventually_atTop.mp
    (hactiveShift.and (hmassShift.and (hgap.and habsorb)))
  let q₀ := K + max Qa (max n T₀)
  have hq₀K : K ≤ q₀ := by simp [q₀]
  have hq₀large : K + n ≤ q₀ := by dsimp [q₀]; omega
  have hq₀tail : T₀ ≤ q₀ - K := by dsimp [q₀]; omega
  have hqprog : ∀ k, Qa ≤ q₀ - K + period * k := by
    intro k
    dsimp [q₀]
    omega
  have hactive : ∀ k p, p ∈ Face →
      aevalWeight n (D * (q₀ + period * k) + τ) Q
        (shiftedAtomPatternKey (q₀ + period * k) K p) ≠ 0 := by
    intro k p hpFace
    have hpS : p ∈ S := (mem_geometricPatternFace_iff.mp hpFace).1
    have hq : q₀ + period * k = (q₀ - K + period * k) + K := by omega
    have hdata := hQa (q₀ - K + period * k) (hqprog k)
    rw [hq]
    exact hdata.1 p hpS
  have hmass : ∀ k,
      (∑ ν ∈ activeAevalAtoms n (D * (q₀ + period * k) + τ) Q,
        ‖aevalWeight n (D * (q₀ + period * k) + τ) Q ν‖) ≤
          (((q₀ + period * k : ℕ) : ℝ) ^ P) := by
    intro k
    have hq : q₀ + period * k = (q₀ - K + period * k) + K := by omega
    have hdata := hQa (q₀ - K + period * k) (hqprog k)
    rw [hq]
    exact hdata.2.1
  have hgapFinal : ∀ v ∈ Face.image (geometricPatternValue lam),
      ∃ gamma' : ℝ, 0 < gamma' ∧ ∀ k,
        ∀ ν ∈ activeAevalAtoms n (D * (q₀ + period * k) + τ) Q \
            Face.image (shiftedAtomPatternKey (q₀ + period * k) K),
          A * lam ^ (q₀ - K) * v * (lam ^ period) ^ k +
              gamma' * (lam ^ period) ^ k ≤
            atomValuation (fun i => A * lam ^ i + c) ν := by
    intro v hv
    obtain ⟨p, hpFace, hpv⟩ := Finset.mem_image.mp hv
    have hvmin : v = geometricPatternMinimum lam S := by
      rw [← hpv]
      exact (mem_geometricPatternFace_iff.mp hpFace).2
    refine ⟨gamma / 2 * lam ^ (q₀ - K), by positivity, fun k ν hν => ?_⟩
    let t := q₀ - K + period * k
    have hq : q₀ + period * k = t + K := by dsimp [t]; omega
    have hdata := hQa t (hqprog k)
    have hgapν := hdata.2.2.1 ν (by simpa [Face, S, hq] using hν)
    have habs := hdata.2.2.2
    have hpow : lam ^ t = lam ^ (q₀ - K) * (lam ^ period) ^ k := by
      dsimp [t]
      rw [pow_add, pow_mul]
    rw [geometricPolynomialFaceBaseline] at hgapν
    rw [hpow] at hgapν habs
    rw [hvmin]
    dsimp [S]
    linarith
  have hzero := periodicGeometricLevelPolynomial_eq_zero_of_activeComplement_gap
    hA hlam hcoeff huNorm hperiod huPeriod Q hrel Face
    (fun p hp => polynomialPatternSurvivors_count
      (mem_geometricPatternFace_iff.mp hp).1)
    hq₀large hq₀tail hactive P hmass hgapFinal
  refine ⟨K, M, q₀, hS, hq₀K, ?_⟩
  exact hzero (geometricPatternMinimum lam S)

/-- The unconditional least-level identity cannot be a singleton.  Hence every exact geometric
integer ADE with a positive-period phase tail produces two distinct tied patterns, so `lam` is
algebraic. -/
theorem isAlgebraic_of_periodicGeometric_integerADE
    {F : PowerSeries ℂ} {u : ℕ → ℂ}
    {A lam c : ℝ} (hA : 0 < A) (hlam : 1 < lam)
    (hbpos : ∀ i, 0 < A * lam ^ i + c)
    (hcoeff : ∀ i, PowerSeries.coeff i F =
      ((Real.exp (-(A * lam ^ i + c)) : ℝ) : ℂ) * u i)
    (huNorm : ∀ i, ‖u i‖ = 1)
    {period T₀ : ℕ} (hperiod : 0 < period)
    (huPeriod : PeriodicFrom u period T₀)
    {n D K₀ τ M₀ : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hrel : aeval (formalJets n F) Q = 0)
    (hD : 0 < D) (hDmax : D = magnitudeMaxJetDegree n Q)
    (p₀ : Fin M₀ → Fin (D + 1))
    (hcount₀ : (∑ r, (p₀ r : ℕ)) = D)
    (hw₀ : ∀ᶠ q : ℕ in atTop,
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K₀ p₀) ≠ 0) :
    IsAlgebraic ℤ lam := by
  classical
  obtain ⟨K, M, q₀, hS, hq₀K, hzero⟩ :=
    exists_periodicGeometric_leastLevelPolynomial_eq_zero
      hA hlam hbpos hcoeff huNorm hperiod huPeriod Q hrel hD hDmax
        p₀ hcount₀ hw₀
  let S := polynomialPatternSurvivors n D K τ Q M
  let Face := geometricPatternFace lam S
  have hFace : Face.Nonempty := geometricPatternFace_nonempty lam S hS
  have hcard : Face.card ≠ 1 := by
    intro hcardOne
    obtain ⟨p, hFaceEq⟩ := Finset.card_eq_one.mp hcardOne
    have hpFace : p ∈ Face := by simp [hFaceEq]
    have hpS : p ∈ S := (mem_geometricPatternFace_iff.mp hpFace).1
    have hphase : periodicGeometricPatternPhase u c q₀ K p ≠ 0 := by
      apply mul_ne_zero
      · exact_mod_cast Real.exp_ne_zero (-(D : ℝ) * c)
      · apply Finset.prod_ne_zero_iff.mpr
        intro r hr
        exact pow_ne_zero _ (norm_ne_zero_iff.mp (by rw [huNorm]; exact one_ne_zero))
    have hweight : periodicGeometricPatternWeight n D K τ Q q₀ period p ≠ 0 :=
      arithmeticProgressionPolynomial_ne_zero hperiod
        (polynomialPatternSurvivors_weightPoly_ne_zero hpS)
    have hfilter : Face.filter (fun x =>
        geometricPatternValue lam x = geometricPatternMinimum lam S) = Face := by
      apply Finset.filter_eq_self.mpr
      intro x hx
      exact (mem_geometricPatternFace_iff.mp hx).2
    have hzero' : exactGeometricLevelPolynomial Face (geometricPatternValue lam)
        (periodicGeometricPatternWeight n D K τ Q q₀ period)
        (periodicGeometricPatternPhase u c q₀ K)
        (geometricPatternMinimum lam S) = 0 := by
      simpa [periodicGeometricLevelPolynomial] using hzero
    have hmul : Polynomial.C (periodicGeometricPatternPhase u c q₀ K p) *
        periodicGeometricPatternWeight n D K τ Q q₀ period p = 0 := by
      rw [exactGeometricLevelPolynomial, hfilter, hFaceEq] at hzero'
      simpa using hzero'
    rcases mul_eq_zero.mp hmul with hpz | hwz
    · apply hphase
      apply Polynomial.C_injective
      simpa using hpz
    · exact hweight hwz
  obtain ⟨p, hpFace⟩ := hFace
  have htie : ∃ r ∈ Face, r ≠ p := by
    by_contra hnot
    have hFaceEq : Face = {p} := by
      ext r
      constructor
      · intro hr
        have hrp : r = p := by
          by_contra hne
          exact hnot ⟨r, hr, hne⟩
        simpa [hrp]
      · intro hr
        have hrp : r = p := by simpa using hr
        simpa [hrp] using hpFace
    apply hcard
    rw [hFaceEq]
    simp
  obtain ⟨r, hrFace, hrp⟩ := htie
  have hpvalue := (mem_geometricPatternFace_iff.mp hpFace).2
  have hrvalue := (mem_geometricPatternFace_iff.mp hrFace).2
  exact isAlgebraic_of_distinct_geometricPatternValue_eq hrp.symm
    (hpvalue.trans hrvalue.symm)

end

end GaloisForLFunctions
