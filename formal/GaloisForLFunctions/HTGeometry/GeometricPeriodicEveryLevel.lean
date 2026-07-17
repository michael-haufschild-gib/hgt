import GaloisForLFunctions.HTGeometry.GeometricPeriodicLeastLevel

/-!
# Every periodic geometric ADE valuation level

For an arbitrary admissible translated top-degree pattern and an arbitrary phase residue, enlarge
the pattern window, retain every survivor whose geometric value is no larger than the target, and
prove that the active complement is uniformly separated above the target.  The exact finite
cascade then forces the target grouped level polynomial to vanish identically.  This is the
source-faithful all-level iteration required by the periodic geometric-profile theorem.
-/

namespace GaloisForLFunctions

open Filter Finset MvPolynomial Polynomial PowerSeries Topology

noncomputable section

theorem exists_pos_finset_strictUpper_gap
    {α : Type*} [DecidableEq α] (S : Finset α) (V : α → ℝ) (v : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ a ∈ S, v < V a → v + delta ≤ V a := by
  classical
  let C := S.filter fun a => v < V a
  by_cases hC : C.Nonempty
  · let gaps := C.image fun a => V a - v
    have hgaps : gaps.Nonempty := hC.image _
    let delta := gaps.min' hgaps
    have hdeltaMem : delta ∈ gaps := Finset.min'_mem gaps hgaps
    have hdelta : 0 < delta := by
      obtain ⟨a, haC, haeq⟩ := Finset.mem_image.mp hdeltaMem
      rw [← haeq]
      exact sub_pos.mpr (Finset.mem_filter.mp haC).2
    refine ⟨delta, hdelta, fun a haS hva => ?_⟩
    have hmem : V a - v ∈ gaps :=
      Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨haS, hva⟩, rfl⟩
    have hle := Finset.min'_le gaps _ hmem
    linarith
  · refine ⟨1, zero_lt_one, fun a haS hva => ?_⟩
    exact (hC ⟨a, Finset.mem_filter.mpr ⟨haS, hva⟩⟩).elim

set_option maxHeartbeats 3000000 in
theorem exists_periodicGeometric_targetLevelPolynomial_eq_zero
    {F : PowerSeries ℂ} {u : ℕ → ℂ}
    {A lam c : ℝ} (hA : 0 < A) (hlam : 1 < lam)
    (hbpos : ∀ i, 0 < A * lam ^ i + c)
    (hcoeff : ∀ i, PowerSeries.coeff i F =
      ((Real.exp (-(A * lam ^ i + c)) : ℝ) : ℂ) * u i)
    (huNorm : ∀ i, ‖u i‖ = 1)
    {period T₀ : ℕ} (hperiod : 0 < period)
    {sigma : ℕ} (hsigma : sigma < period)
    (huPeriod : PeriodicFrom u period T₀)
    {n D K₀ τ M₀ : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hrel : aeval (formalJets n F) Q = 0)
    (hD : 0 < D) (hDmax : D = magnitudeMaxJetDegree n Q)
    (p₀ : Fin M₀ → Fin (D + 1))
    (hcount₀ : (∑ r, (p₀ r : ℕ)) = D)
    (hw₀ : ∀ᶠ q : ℕ in atTop,
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K₀ p₀) ≠ 0) :
    ∃ K M q₀ : ℕ,
      let target := lam ^ (K - K₀) * geometricPatternValue lam p₀
      let S := (polynomialPatternSurvivors n D K τ Q M).filter
        fun p => geometricPatternValue lam p ≤ target
      S.Nonempty ∧
        (S.filter fun p => geometricPatternValue lam p = target).Nonempty ∧
        (S.filter fun p => geometricPatternValue lam p = target).card ≠ 1 ∧
        K ≤ q₀ ∧ q₀ % period = sigma ∧
        periodicGeometricLevelPolynomial n D K τ Q q₀ period S u c lam target = 0 := by
  classical
  have hc : Tendsto (fun _ : ℕ => c) atTop (nhds c) := tendsto_const_nhds
  have hgrowth : UniformGeometricGrowth (fun i => A * lam ^ i + c) :=
    uniformGeometricGrowth_hierarchical hlam hA
      (isLittleO_constPow_of_tendsto hlam hc)
  obtain ⟨K, M, hK₀K, hpattern⟩ :=
    exists_eventually_activeAtom_geometricWitness_pattern hbpos hgrowth
      Q hD hDmax p₀ hcount₀
  let Sfull := polynomialPatternSurvivors n D K τ Q M
  let target := lam ^ (K - K₀) * geometricPatternValue lam p₀
  let S := Sfull.filter fun p => geometricPatternValue lam p ≤ target
  have hwpat := hpattern.and (hw₀.and (eventually_ge_atTop (max (K + n) K₀)))
  obtain ⟨qstar, hpatstar, hwstar, hqstar⟩ := hwpat.exists
  let νstar := shiftedAtomPatternKey qstar K₀ p₀
  have hνstar : νstar ∈ activeAevalAtoms n (D * qstar + τ) Q := by
    rw [mem_activeAevalAtoms]
    exact ⟨mem_appearingAtoms_of_aevalWeight_ne_zero hwstar, hwstar⟩
  have hnearstar : atomValuation (fun i => A * lam ^ i + c) νstar <
      atomValuation (fun i => A * lam ^ i + c) νstar +
        (A * lam ^ (qstar - K₀ + atomPatternMaxOffset p₀ hcount₀) + c) :=
    lt_add_of_pos_right _ (hbpos _)
  obtain ⟨pstar, hpstarCount, hpstarKey⟩ :=
    hpatstar νstar hνstar hnearstar
  have hpstarWeight : aevalWeight n (D * qstar + τ) Q
      (shiftedAtomPatternKey qstar K pstar) ≠ 0 := by
    rw [hpstarKey]
    exact hwstar
  have hpstarFull : pstar ∈ Sfull := by
    exact mem_polynomialPatternSurvivors_of_aevalWeight_ne_zero hpstarCount
      (by omega) hpstarWeight
  have hpstarValue : geometricPatternValue lam pstar = target := by
    have hrem₀ : geometricPatternRemainder (fun _ => c) qstar K₀ p₀ = D * c := by
      rw [geometricPatternRemainder]
      have hs : ∑ r, (p₀ r : ℝ) = (D : ℝ) := by exact_mod_cast hcount₀
      rw [← Finset.sum_mul, hs]
    have hremstar : geometricPatternRemainder (fun _ => c) qstar K pstar = D * c := by
      rw [geometricPatternRemainder]
      have hs : ∑ r, (pstar r : ℝ) = (D : ℝ) := by exact_mod_cast hpstarCount
      rw [← Finset.sum_mul, hs]
    have hval := congrArg (atomValuation (fun i => A * lam ^ i + c)) hpstarKey
    rw [atomValuation_shiftedAtomPatternKey_geometric A lam (fun _ => c) qstar K pstar,
      atomValuation_shiftedAtomPatternKey_geometric A lam (fun _ => c) qstar K₀ p₀,
      hremstar, hrem₀] at hval
    have hpow : lam ^ (qstar - K₀) = lam ^ (qstar - K) * lam ^ (K - K₀) := by
      have hidx : qstar - K₀ = (qstar - K) + (K - K₀) := by omega
      rw [hidx, pow_add]
    rw [hpow] at hval
    have hscale : 0 < A * lam ^ (qstar - K) :=
      mul_pos hA (pow_pos (zero_lt_one.trans hlam) _)
    dsimp [target]
    nlinarith
  have hpstarS : pstar ∈ S := by
    exact Finset.mem_filter.mpr ⟨hpstarFull, hpstarValue.le⟩
  have hS : S.Nonempty := ⟨pstar, hpstarS⟩
  obtain ⟨delta, hdelta, hupperGap⟩ :=
    exists_pos_finset_strictUpper_gap Sfull (geometricPatternValue lam) target
  let gamma := min (A * delta) (A / 2)
  have hgamma : 0 < gamma := lt_min (mul_pos hA hdelta) (by positivity)
  have hactiveEv := polynomialPatternSurvivors_eventually_weight_ne_zero
    (n := n) (D := D) (K := K) (τ := τ) (M := M) Q
  obtain ⟨P, hmassEv⟩ := exists_aevalWeight_mass_natPow_bound n D τ Q
  let C₀ := K - K₀ + atomPatternMaxOffset p₀ hcount₀
  have hcenter : ∀ᶠ t : ℕ in atTop,
      A / 2 * lam ^ t ≤ A * lam ^ (t + C₀) + c :=
    eventually_geometricProfile_half_lower hA hlam hc C₀
  have habsorb : ∀ᶠ t : ℕ in atTop,
      -(D : ℝ) * c ≤ gamma / 2 * lam ^ t := by
    have htop : Tendsto (fun t : ℕ => gamma / 2 * lam ^ t) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt hlam).const_mul_atTop (by positivity)
    exact htop.eventually_ge_atTop (-(D : ℝ) * c)
  have hpatternShift := (tendsto_add_atTop_nat K).eventually hpattern
  have hactiveShift := (tendsto_add_atTop_nat K).eventually hactiveEv
  have hmassShift := (tendsto_add_atTop_nat K).eventually hmassEv
  obtain ⟨Qa, hQa⟩ := Filter.eventually_atTop.mp
    (hpatternShift.and (hactiveShift.and (hmassShift.and (hcenter.and habsorb))))
  let B := K + max Qa (max n T₀)
  let q₀ := period * B + sigma
  have hBq₀ : B ≤ q₀ := by
    exact (Nat.le_mul_of_pos_left B hperiod).trans (Nat.le_add_right _ sigma)
  have hq₀K : K ≤ q₀ := by dsimp [B] at hBq₀; omega
  have hq₀large : K + n ≤ q₀ := by dsimp [B] at hBq₀; omega
  have hq₀tail : T₀ ≤ q₀ - K := by dsimp [B] at hBq₀; omega
  have hq₀mod : q₀ % period = sigma := by
    simp [q₀, Nat.add_mod, Nat.mod_eq_of_lt hsigma]
  have hqprog : ∀ k, Qa ≤ q₀ - K + period * k := by
    intro k
    dsimp [B] at hBq₀
    omega
  have hactive : ∀ k p, p ∈ S →
      aevalWeight n (D * (q₀ + period * k) + τ) Q
        (shiftedAtomPatternKey (q₀ + period * k) K p) ≠ 0 := by
    intro k p hpS
    have hpFull : p ∈ Sfull := (Finset.mem_filter.mp hpS).1
    let t := q₀ - K + period * k
    have hq : q₀ + period * k = t + K := by dsimp [t]; omega
    have hdata := hQa t (hqprog k)
    rw [hq]
    exact hdata.2.1 p hpFull
  have hmass : ∀ k,
      (∑ ν ∈ activeAevalAtoms n (D * (q₀ + period * k) + τ) Q,
        ‖aevalWeight n (D * (q₀ + period * k) + τ) Q ν‖) ≤
          (((q₀ + period * k : ℕ) : ℝ) ^ P) := by
    intro k
    let t := q₀ - K + period * k
    have hq : q₀ + period * k = t + K := by dsimp [t]; omega
    have hdata := hQa t (hqprog k)
    rw [hq]
    exact hdata.2.2.1
  have hgapFinal : ∀ v ∈ S.image (geometricPatternValue lam),
      ∃ gamma' : ℝ, 0 < gamma' ∧ ∀ k,
        ∀ ν ∈ activeAevalAtoms n (D * (q₀ + period * k) + τ) Q \
            S.image (shiftedAtomPatternKey (q₀ + period * k) K),
          A * lam ^ (q₀ - K) * v * (lam ^ period) ^ k +
              gamma' * (lam ^ period) ^ k ≤
            atomValuation (fun i => A * lam ^ i + c) ν := by
    intro v hv
    obtain ⟨pv, hpvS, hpvv⟩ := Finset.mem_image.mp hv
    have hvtarget : v ≤ target := by
      rw [← hpvv]
      exact (Finset.mem_filter.mp hpvS).2
    refine ⟨gamma / 2 * lam ^ (q₀ - K), by positivity, fun k ν hν => ?_⟩
    let t := q₀ - K + period * k
    let q := t + K
    have hq : q = q₀ + period * k := by dsimp [q, t]; omega
    have hdata := hQa t (hqprog k)
    have hpat := hdata.1
    have hcenterT := hdata.2.2.2.1
    have habs := hdata.2.2.2.2
    have hpow : lam ^ t = lam ^ (q₀ - K) * (lam ^ period) ^ k := by
      dsimp [t]
      rw [pow_add, pow_mul]
    have hwrem : geometricPatternRemainder (fun _ => c) q K₀ p₀ = D * c := by
      rw [geometricPatternRemainder]
      have hs : ∑ r, (p₀ r : ℝ) = (D : ℝ) := by exact_mod_cast hcount₀
      rw [← Finset.sum_mul, hs]
    have hwval : atomValuation (fun i => A * lam ^ i + c)
        (shiftedAtomPatternKey q K₀ p₀) = A * lam ^ t * target + D * c := by
      rw [atomValuation_shiftedAtomPatternKey_geometric A lam (fun _ => c) q K₀ p₀,
        hwrem]
      have hidx : q - K₀ = t + (K - K₀) := by dsimp [q]; omega
      rw [hidx, pow_add]
      dsimp [target]
      ring
    have hcenterEq : q - K₀ + atomPatternMaxOffset p₀ hcount₀ = t + C₀ := by
      dsimp [q, C₀]
      omega
    have hraw : A * lam ^ t * target + D * c + gamma * lam ^ t ≤
        atomValuation (fun i => A * lam ^ i + c) ν := by
      by_cases hnear : atomValuation (fun i => A * lam ^ i + c) ν <
          atomValuation (fun i => A * lam ^ i + c)
              (shiftedAtomPatternKey q K₀ p₀) +
            (A * lam ^ (q - K₀ + atomPatternMaxOffset p₀ hcount₀) + c)
      · have hνactive : ν ∈ activeAevalAtoms n (D * q + τ) Q := by
          simpa [hq] using (Finset.mem_sdiff.mp hν).1
        obtain ⟨p, hpcount, hpkey⟩ := hpat ν hνactive hnear
        have hpweight : aevalWeight n (D * q + τ) Q
            (shiftedAtomPatternKey q K p) ≠ 0 := by
          rw [hpkey]
          exact (mem_activeAevalAtoms.mp hνactive).2
        have hpFull : p ∈ Sfull :=
          mem_polynomialPatternSurvivors_of_aevalWeight_ne_zero hpcount
            (by dsimp [q, t, q₀]; omega) hpweight
        have hpNotS : p ∉ S := by
          intro hpS
          apply (Finset.mem_sdiff.mp hν).2
          rw [← hq]
          exact Finset.mem_image.mpr ⟨p, hpS, hpkey⟩
        have hpgt : target < geometricPatternValue lam p := by
          apply lt_of_not_ge
          intro hle
          exact hpNotS (Finset.mem_filter.mpr ⟨hpFull, hle⟩)
        have hpGap := hupperGap p hpFull hpgt
        have hprem : geometricPatternRemainder (fun _ => c) q K p = D * c := by
          rw [geometricPatternRemainder]
          have hs : ∑ r, (p r : ℝ) = (D : ℝ) := by exact_mod_cast hpcount
          rw [← Finset.sum_mul, hs]
        rw [← hpkey,
          atomValuation_shiftedAtomPatternKey_geometric A lam (fun _ => c) q K p,
          show q - K = t by dsimp [q]; omega, hprem]
        have hscale : 0 ≤ A * lam ^ t :=
          mul_nonneg hA.le (pow_nonneg (zero_lt_one.trans hlam).le _)
        have hscaled := mul_le_mul_of_nonneg_left hpGap hscale
        have hgammaLe : gamma ≤ A * delta := min_le_left _ _
        have hpowNonneg : 0 ≤ lam ^ t := pow_nonneg (zero_lt_one.trans hlam).le _
        have := mul_le_mul_of_nonneg_right hgammaLe hpowNonneg
        linarith
      · have hfar := le_of_not_gt hnear
        rw [hwval, hcenterEq] at hfar
        have hgammaLe : gamma ≤ A / 2 := min_le_right _ _
        have hpowNonneg : 0 ≤ lam ^ t := pow_nonneg (zero_lt_one.trans hlam).le _
        have hgle := mul_le_mul_of_nonneg_right hgammaLe hpowNonneg
        linarith
    rw [hpow] at hraw habs
    have hscaleV : A * lam ^ (q₀ - K) * v * (lam ^ period) ^ k ≤
        A * lam ^ (q₀ - K) * target * (lam ^ period) ^ k := by
      have hnonneg : 0 ≤ A * lam ^ (q₀ - K) * (lam ^ period) ^ k := by positivity
      nlinarith
    dsimp [gamma]
    dsimp [gamma] at hraw habs
    nlinarith
  have hzero := periodicGeometricLevelPolynomial_eq_zero_of_activeComplement_gap
    hA hlam hcoeff huNorm hperiod huPeriod Q hrel S
    (fun p hp => polynomialPatternSurvivors_count (Finset.mem_filter.mp hp).1)
    hq₀large hq₀tail hactive P hmass hgapFinal
  have htargetZero := hzero target
  have htarget : (S.filter fun p => geometricPatternValue lam p = target).Nonempty :=
    ⟨pstar, Finset.mem_filter.mpr ⟨hpstarS, hpstarValue⟩⟩
  have htargetCard : (S.filter fun p => geometricPatternValue lam p = target).card ≠ 1 := by
    intro hcard
    obtain ⟨p, hFaceEq⟩ := Finset.card_eq_one.mp hcard
    have hpTarget : p ∈ S.filter (fun x => geometricPatternValue lam x = target) := by
      simp [hFaceEq]
    have hpS : p ∈ S := (Finset.mem_filter.mp hpTarget).1
    have hpFull : p ∈ Sfull := (Finset.mem_filter.mp hpS).1
    have hphase : periodicGeometricPatternPhase u c q₀ K p ≠ 0 := by
      apply mul_ne_zero
      · exact_mod_cast Real.exp_ne_zero (-(D : ℝ) * c)
      · apply Finset.prod_ne_zero_iff.mpr
        intro r hr
        exact pow_ne_zero _ (norm_ne_zero_iff.mp (by rw [huNorm]; exact one_ne_zero))
    have hweight : periodicGeometricPatternWeight n D K τ Q q₀ period p ≠ 0 :=
      arithmeticProgressionPolynomial_ne_zero hperiod
        (polynomialPatternSurvivors_weightPoly_ne_zero hpFull)
    have hzero' : exactGeometricLevelPolynomial S (geometricPatternValue lam)
        (periodicGeometricPatternWeight n D K τ Q q₀ period)
        (periodicGeometricPatternPhase u c q₀ K) target = 0 := by
      simpa [periodicGeometricLevelPolynomial] using htargetZero
    have hmul : Polynomial.C (periodicGeometricPatternPhase u c q₀ K p) *
        periodicGeometricPatternWeight n D K τ Q q₀ period p = 0 := by
      rw [exactGeometricLevelPolynomial, hFaceEq] at hzero'
      simpa using hzero'
    rcases mul_eq_zero.mp hmul with hpz | hwz
    · apply hphase
      apply Polynomial.C_injective
      simpa using hpz
    · exact hweight hwz
  refine ⟨K, M, q₀, hS, htarget, htargetCard, hq₀K, hq₀mod, htargetZero⟩

end

end GaloisForLFunctions
