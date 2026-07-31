import GaloisForLFunctions.HTGeometry.PolynomialPhaseLockAssembly

open Filter Finset PowerSeries MvPolynomial Polynomial Topology Asymptotics Set

namespace GaloisForLFunctions

noncomputable section

theorem exists_aevalWeight_mass_natPow_bound
    (n D τ : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) :
    ∃ P : ℕ, ∀ᶠ q : ℕ in atTop,
      (∑ ν ∈ activeAevalAtoms n (D * q + τ) Q,
          ‖aevalWeight n (D * q + τ) Q ν‖) ≤ (q : ℝ) ^ P := by
  let O := magnitudeMaxJetOrder n Q
  let E := magnitudeMaxJetDegree n Q + O
  let A : ℝ := magnitudeCoefficientMass Q *
    (((O + 1) ^ O : ℕ) : ℝ)
  have hA : 0 ≤ A := by
    dsimp [A]
    apply mul_nonneg
    · rw [magnitudeCoefficientMass]
      positivity
    · positivity
  obtain ⟨A₀, hA₀⟩ := exists_nat_ge A
  let L := D + τ + 2
  let C := A₀ * L ^ E
  refine ⟨E + 1, ?_⟩
  filter_upwards [eventually_ge_atTop (max C 1)] with q hq
  have hq1 : 1 ≤ q := (le_max_right _ _).trans hq
  have hCq : C ≤ q := (le_max_left _ _).trans hq
  have hlevel : D * q + τ + 1 ≤ L * q := by
    dsimp [L]
    nlinarith
  have hpow : (D * q + τ + 1) ^ E ≤ (L * q) ^ E :=
    Nat.pow_le_pow_left hlevel E
  calc
    (∑ ν ∈ activeAevalAtoms n (D * q + τ) Q,
        ‖aevalWeight n (D * q + τ) Q ν‖)
        ≤ ∑ ν ∈ (sigmaIdx n (D * q + τ) Q).image (atomKeyOf n),
            ‖aevalWeight n (D * q + τ) Q ν‖ :=
      activeAevalWeight_mass_le n (D * q + τ) Q
    _ ≤ A * (((D * q + τ + 1) ^ E : ℕ) : ℝ) := by
      simpa [A, E, O, mul_assoc] using
        aevalWeight_mass_le_singlePolynomial n Q (D * q + τ)
    _ ≤ (A₀ : ℝ) * (((L * q) ^ E : ℕ) : ℝ) := by
      apply mul_le_mul hA₀
      · exact_mod_cast hpow
      · positivity
      · exact_mod_cast Nat.zero_le A₀
    _ = (C : ℝ) * (q : ℝ) ^ E := by
      push_cast
      simp [C, mul_pow]
      ring
    _ ≤ (q : ℝ) * (q : ℝ) ^ E := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hCq)
        (pow_nonneg (Nat.cast_nonneg q) E)
    _ = (q : ℝ) ^ (E + 1) := by rw [pow_succ']

/-- An eventual active-atom valuation gap implies the exponentially accurate
normalized phase lock for the corresponding finite shifted cluster. -/
theorem eventually_polynomialPhaseLock_of_activeAtom_gap
    {β B c η : ℝ} {n D K τ M : ℕ}
    (F : PowerSeries ℂ) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ =
      Real.exp (-(B * (i : ℝ) ^ β)))
    (hrel : aeval (formalJets n F) Q = 0)
    (C : Finset (Fin M → Fin (D + 1))) (m : ℕ → ℝ)
    (hactive : ∀ᶠ q : ℕ in atTop, ∀ p ∈ C,
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) ≠ 0)
    (hgap : ∀ᶠ q : ℕ in atTop,
      ∀ ν ∈ activeAevalAtoms n (D * q + τ) Q \
          C.image (shiftedAtomPatternKey q K),
        m q + c * (q : ℝ) ^ η ≤
          atomValuation (fun i => B * (i : ℝ) ^ β) ν) :
    ∃ P : ℕ, ∀ᶠ q : ℕ in atTop,
      ‖∑ p ∈ C,
          aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) *
            (Real.exp (-(atomValuation (fun i => B * (i : ℝ) ^ β)
              (shiftedAtomPatternKey q K p) - m q)) : ℂ) *
            normalizedAtomPhase F (fun i => B * (i : ℝ) ^ β)
              (shiftedAtomPatternKey q K p)‖ ≤
        (q : ℝ) ^ P * Real.exp (-(c * (q : ℝ) ^ η)) := by
  classical
  obtain ⟨P, hmass⟩ := exists_aevalWeight_mass_natPow_bound n D τ Q
  refine ⟨P, ?_⟩
  filter_upwards [hactive, hgap, hmass] with q hactiveq hgapq hmassq
  let T := activeAevalAtoms n (D * q + τ) Q
  let Ckey := C.image (shiftedAtomPatternKey q K)
  have hCkeyT : Ckey ⊆ T := by
    intro ν hν
    obtain ⟨p, hp, hpν⟩ := Finset.mem_image.mp hν
    subst ν
    rw [mem_activeAevalAtoms]
    have hw := hactiveq p hp
    exact ⟨mem_appearingAtoms_of_aevalWeight_ne_zero hw, hw⟩
  let f : (ℕ →₀ ℕ) → ℂ := fun ν =>
    aevalWeight n (D * q + τ) Q ν *
      (Real.exp (-(atomValuation (fun i => B * (i : ℝ) ^ β) ν - m q)) : ℂ) *
        normalizedAtomPhase F (fun i => B * (i : ℝ) ^ β) ν
  have hzero : ∑ ν ∈ T, f ν = 0 := by
    simpa [T, f] using normalized_active_aeval_coefficient_identity
      n (D * q + τ) F Q (fun i => B * (i : ℝ) ^ β) hrel (m q)
  have hbalance : ∑ ν ∈ Ckey, f ν = -∑ ν ∈ T \ Ckey, f ν :=
    normalized_cluster_balance_of_identity T Ckey hCkeyT f hzero
  have hphase : ∀ ν ∈ T,
      ‖normalizedAtomPhase F (fun i => B * (i : ℝ) ^ β) ν‖ ≤ 1 := by
    intro ν hν
    rw [norm_normalizedAtomPhase F (fun i => B * (i : ℝ) ^ β) hb ν]
  have hbound := norm_cluster_sum_le_mass_mul_exp_neg_gap T Ckey
    (fun ν => aevalWeight n (D * q + τ) Q ν)
    (fun ν => normalizedAtomPhase F (fun i => B * (i : ℝ) ^ β) ν)
    (fun ν => atomValuation (fun i => B * (i : ℝ) ^ β) ν)
    (m q) (c * (q : ℝ) ^ η) ((q : ℝ) ^ P)
    (by simpa [f] using hbalance) hphase hgapq hmassq
  rw [sum_image_shiftedAtomPatternKey C (fun ν =>
    aevalWeight n (D * q + τ) Q ν *
      (Real.exp (-(atomValuation (fun i => B * (i : ℝ) ^ β) ν - m q)) : ℂ) *
        normalizedAtomPhase F (fun i => B * (i : ℝ) ^ β) ν)] at hbound
  exact hbound

def polynomialPhaseLockExponent (β : ℝ) : ℝ :=
  min (β - 2) (β - (Nat.ceil β - 1 : ℕ))

theorem polynomialPhaseLockExponent_pos {β : ℝ} (hβ : 2 < β) :
    0 < polynomialPhaseLockExponent β := by
  rw [polynomialPhaseLockExponent, lt_min_iff]
  refine ⟨sub_pos.mpr hβ, ?_⟩
  have hceil3 : 3 ≤ Nat.ceil β := by
    by_contra hnot
    have hceil2 : Nat.ceil β ≤ 2 := by omega
    have : β ≤ (2 : ℝ) := Nat.ceil_le.mp hceil2
    linarith
  have hceilLt : (Nat.ceil β : ℝ) < β + 1 :=
    Nat.ceil_lt_add_one (by linarith : 0 ≤ β)
  have hcast : ((Nat.ceil β - 1 : ℕ) : ℝ) = (Nat.ceil β : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcast]
  linarith

theorem atomValuation_scaledPower
    (β B : ℝ) (ν : ℕ →₀ ℕ) :
    atomValuation (fun i => B * (i : ℝ) ^ β) ν =
      B * ν.sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) := by
  rw [atomValuation, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The least source class and its least moment signature give one uniform
`x^η` gap against every surviving bounded pattern outside the cluster. -/
theorem eventually_uniform_survivor_gap_from_cluster
    {β : ℝ} (hβ : 2 < β) {M D : ℕ}
    (S : Finset (Fin M → Fin (D + 1))) (hS : S.Nonempty)
    (hcount : ∀ p ∈ S, (∑ r, (p r : ℕ)) = D)
    (p₀ : Fin M → Fin (D + 1))
    (hp₀ : p₀ ∈ polynomialPatternMinimalCluster
      (R := Nat.ceil β - 2)
      (polynomialPatternLeastSourceClass S hS)
      (polynomialPatternLeastSourceClass_nonempty S hS)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      ∀ p ∈ S \ polynomialPatternMinimalCluster
          (R := Nat.ceil β - 2)
          (polynomialPatternLeastSourceClass S hS)
          (polynomialPatternLeastSourceClass_nonempty S hS),
        c * x ^ polynomialPhaseLockExponent β ≤
          polynomialPatternPowerValuation β p x -
            polynomialPatternPowerValuation β p₀ x := by
  classical
  let T := polynomialPatternLeastSourceClass S hS
  let hT : T.Nonempty := polynomialPatternLeastSourceClass_nonempty S hS
  let C := polynomialPatternMinimalCluster (R := Nat.ceil β - 2) T hT
  have hp₀T : p₀ ∈ T := polynomialPatternMinimalCluster_subset T hT hp₀
  have hp₀S : p₀ ∈ S := polynomialPatternLeastSourceClass_subset S hS hp₀T
  obtain ⟨csrc, hcsrc, hsrc⟩ :=
    eventually_uniform_polynomialPatternPower_source_gap hβ S hS hcount p₀ hp₀T
  have hcountT : ∀ p ∈ T, (∑ r, (p r : ℕ)) = D := fun p hp =>
    hcount p (polynomialPatternLeastSourceClass_subset S hS hp)
  have hsumT : ∀ p ∈ T,
      (∑ r : Fin M, (r : ℕ) * (p r : ℕ)) =
        minimalPolynomialPatternSourceSum S hS := by
    intro p hp
    exact sourceSum_eq_of_mem_polynomialPatternLeastSourceClass hp
  obtain ⟨csig, hcsig, hsig⟩ :=
    eventually_uniform_polynomialPatternPower_gap hβ T hT hcountT hsumT p₀ hp₀
  let c := min csrc csig
  have hc : 0 < c := lt_min hcsrc hcsig
  refine ⟨c, hc, ?_⟩
  filter_upwards [hsrc, hsig, eventually_ge_atTop (1 : ℝ)] with x hsrcx hsigx hx
  intro p hpSC
  have hpS : p ∈ S := (Finset.mem_sdiff.mp hpSC).1
  have hpC : p ∉ C := by simpa [C, T, hT] using (Finset.mem_sdiff.mp hpSC).2
  have heta_le_two : polynomialPhaseLockExponent β ≤ β - 2 := min_le_left _ _
  have heta_le_sig : polynomialPhaseLockExponent β ≤
      β - (Nat.ceil β - 1 : ℕ) := min_le_right _ _
  by_cases hpT : p ∈ T
  · have hbase := hsigx p (Finset.mem_sdiff.mpr ⟨hpT, hpC⟩)
    have hpow : x ^ polynomialPhaseLockExponent β ≤
        x ^ (β - (Nat.ceil β - 1 : ℕ)) :=
      Real.rpow_le_rpow_of_exponent_le hx heta_le_sig
    calc
      c * x ^ polynomialPhaseLockExponent β ≤
          csig * x ^ polynomialPhaseLockExponent β :=
        mul_le_mul_of_nonneg_right (min_le_right _ _)
          (Real.rpow_nonneg (by linarith) _)
      _ ≤ csig * x ^ (β - (Nat.ceil β - 1 : ℕ)) :=
        mul_le_mul_of_nonneg_left hpow hcsig.le
      _ ≤ _ := hbase
  · have hbase := hsrcx p (Finset.mem_sdiff.mpr ⟨hpS, hpT⟩)
    have hpow : x ^ polynomialPhaseLockExponent β ≤ x ^ (β - 1) := by
      apply Real.rpow_le_rpow_of_exponent_le hx
      exact heta_le_two.trans (by linarith)
    calc
      c * x ^ polynomialPhaseLockExponent β ≤
          csrc * x ^ polynomialPhaseLockExponent β :=
        mul_le_mul_of_nonneg_right (min_le_left _ _)
          (Real.rpow_nonneg (by linarith) _)
      _ ≤ csrc * x ^ (β - 1) :=
        mul_le_mul_of_nonneg_left hpow hcsrc.le
      _ ≤ _ := hbase

set_option maxHeartbeats 600000 in
theorem exists_residueCluster_activeAtom_gap
    {β B : ℝ} (hβ : 2 < β) (hB : 0 < B) {n : ℕ}
    (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hDpos : 0 < magnitudeMaxJetDegree n Q)
    (τ : ℕ) (hτ : τ < magnitudeMaxJetDegree n Q) :
    ∃ (K M : ℕ),
      let D := magnitudeMaxJetDegree n Q
      let S := polynomialPatternSurvivors n D K τ Q M
      ∃ hS : S.Nonempty,
        let T := polynomialPatternLeastSourceClass S hS
        let hT := polynomialPatternLeastSourceClass_nonempty S hS
        let C := polynomialPatternMinimalCluster (R := Nat.ceil β - 2) T hT
        let hC := polynomialPatternMinimalCluster_nonempty T hT
        let m : ℕ → ℝ := fun q => B *
          polynomialPatternClusterMinValuation β C hC ((q : ℝ) - K)
        ∃ c : ℝ, 0 < c ∧ ∀ᶠ q : ℕ in atTop,
          ∀ ν ∈ activeAevalAtoms n (D * q + τ) Q \
              C.image (shiftedAtomPatternKey q K),
            m q + c * (q : ℝ) ^ polynomialPhaseLockExponent β ≤
              atomValuation (fun i => B * (i : ℝ) ^ β) ν := by
  classical
  obtain ⟨anchor, ha, haD, haMax⟩ :=
    exists_maxShiftCode_topDegree_anchor Q hDpos
  rw [← haD] at hDpos hτ haMax ⊢
  let D := jetMonomialDegree n anchor
  let J := jetMonomialOrder n anchor
  have hD : 0 < D := by simpa [D, haD] using hDpos
  have hτD : τ < D := by simpa [D, haD] using hτ
  obtain ⟨Kshift, δ, Qres, hres⟩ :=
    exists_eventually_balancedKey_nonzero_exact_residue ha hD τ hτD
  obtain ⟨Kconf, cgap, hcgap, hgapEv⟩ :=
    exists_eventually_activeAtom_powerGap_or_window hβ Q ha haD haMax hD δ
  obtain ⟨Qgap, hgap⟩ := Filter.eventually_atTop.mp hgapEv
  let K := Kshift + Kconf
  let M := 2 * Kconf + 1
  let q₀ := max Qres (max (Qgap + Kshift) (max (K + n) (Kshift + J + 1)))
  have hqres : Qres ≤ q₀ := le_max_left _ _
  have hqgap : Qgap ≤ q₀ - Kshift := by dsimp [q₀]; omega
  have hqlarge : K + n ≤ q₀ := by dsimp [q₀]; omega
  have hqshift : Kshift ≤ q₀ := by dsimp [q₀]; omega
  have hqrawPos : 0 < q₀ - Kshift := by dsimp [q₀]; omega
  let qraw := q₀ - Kshift
  let s : Fin D → ℕ := fun i => qraw + δ i
  have hres₀ := hres q₀ hqres
  have hmem : key s ∈ (sigmaIdx n (D * q₀ + τ) Q).image (atomKeyOf n) := by
    simpa only [D, qraw, s] using hres₀.1
  have hweight : aevalWeight n (D * q₀ + τ) Q (key s) ≠ 0 := by
    simpa only [D, qraw, s] using hres₀.2.1
  have hinv : (key s).sum (fun i k => i * k) + magnitudeShiftCode n Q anchor =
      D * q₀ + τ + magnitudeMaxJetOrder n Q := by
    simpa only [D, qraw, s] using hres₀.2.2
  have hJle : J ≤ ∑ i, s i := by
    obtain ⟨i₀⟩ : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
    have hbase : J ≤ qraw := by dsimp [qraw, q₀]; omega
    exact hbase.trans ((show qraw ≤ s i₀ by simp [s]).trans
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀)))
  let Nraw := (∑ i, s i) + anchor 0 - J
  have hwraw := witness_sum_add_shiftCode Q ha δ Nraw rfl hJle
  have hNraw : Nraw = D * q₀ + τ := by
    rw [key_weighted_sum] at hinv
    change (∑ i, s i) + magnitudeShiftCode n Q anchor =
      Nraw + magnitudeMaxJetOrder n Q at hwraw
    omega
  have hgap₀ := hgap qraw hqgap (key s) (by
    simpa [hNraw, Nraw, J, D, s, qraw] using hmem)
  have hwitnessWindow :
      (key s).sum (fun _ k => k) = D ∧
        ∀ i, key s i ≠ 0 → qraw - Kconf ≤ i ∧ i ≤ qraw + Kconf := by
    rcases hgap₀ with hwin | hlose
    · simpa only [D, s] using hwin
    · have hpowPos : 0 < (qraw : ℝ) ^ (β - 2) :=
        Real.rpow_pos_of_pos (by exact_mod_cast hqrawPos) _
      have hcpos : 0 < cgap * (qraw : ℝ) ^ (β - 2) := mul_pos hcgap hpowPos
      have hself : (key s).sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) +
          cgap * (qraw : ℝ) ^ (β - 2) ≤
          (key s).sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) := by
        simpa only [s] using hlose
      linarith
  have hδle : ∀ i, δ i ≤ Kconf := by
    intro i
    have hkeyi : key s (s i) ≠ 0 := by
      rw [key_count_map]
      apply Multiset.count_ne_zero.mpr
      simp
    have hi := (hwitnessWindow.2 (s i) hkeyi).2
    dsimp [s] at hi
    omega
  let g : Fin D → Fin M := fun i => ⟨Kconf + δ i, by
    dsimp [M]
    have := hδle i
    omega⟩
  have hgCount : (key (fun i => (g i : ℕ))).sum (fun _ k => k) = D :=
    key_total_count (fun i => (g i : ℕ))
  have hgSupp : ∀ r, key (fun i => (g i : ℕ)) r ≠ 0 → r < M := by
    intro r hr
    rw [key_count_map] at hr
    have hrmem : r ∈ Multiset.map (fun i => (g i : ℕ))
        (Finset.univ : Finset (Fin D)).val := Multiset.count_ne_zero.mp hr
    rw [Multiset.mem_map] at hrmem
    obtain ⟨i, hi, hir⟩ := hrmem
    rw [← hir]
    exact (g i).isLt
  let pW : Fin M → Fin (D + 1) :=
    boundedPatternOfFinsupp (key (fun i => (g i : ℕ))) D M hgCount
  have hpWcount : (∑ r, (pW r : ℕ)) = D :=
    boundedPatternOfFinsupp_count _ D M hgCount hgSupp
  have hg : g ∈ atomPatternAssignments pW := by
    rw [mem_atomPatternAssignments]
    exact (atomPatternKey_boundedPatternOfFinsupp _ D M hgCount hgSupp).symm
  have hkeyW : shiftedAtomPatternKey q₀ K pW = key s := by
    calc
      shiftedAtomPatternKey q₀ K pW =
          key (fun i => windowShift q₀ K (g i : ℕ)) :=
        (key_windowShift_eq_shiftedAtomPatternKey pW g hg).symm
      _ = key s := by
        congr 1
        funext i
        dsimp [windowShift, K, g, s, qraw]
        omega
  let S := polynomialPatternSurvivors n D K τ Q M
  have hpWS : pW ∈ S := by
    apply mem_polynomialPatternSurvivors_of_aevalWeight_ne_zero hpWcount hqlarge
    simpa [hkeyW] using hweight
  have hS : S.Nonempty := ⟨pW, hpWS⟩
  have hpWFloor : polynomialPatternSourceSum pW + magnitudeShiftCode n Q anchor =
      D * K + τ + magnitudeMaxJetOrder n Q := by
    apply polynomialPattern_source_floor_eq_of_anchor_invariant pW hpWcount
      ((Nat.le_add_right K n).trans hqlarge)
    simpa [hkeyW] using hinv
  let T := polynomialPatternLeastSourceClass S hS
  have hT : T.Nonempty := polynomialPatternLeastSourceClass_nonempty S hS
  have hpWT : pW ∈ T := by
    dsimp [T]
    rw [polynomialPatternLeastSourceClass, Finset.mem_filter]
    refine ⟨hpWS, ?_⟩
    apply le_antisymm
    · have hfloor : ∀ p ∈ S, polynomialPatternSourceSum pW ≤
          polynomialPatternSourceSum p := by
        intro p hp
        have hpFloor := polynomialPattern_source_floor_of_survivor
          (Q := Q) (anchor := anchor) (by
            intro m hm hmD
            apply haMax m hm
            simpa [D, haD] using hmD) hp
        omega
      have hminmem : minimalPolynomialPatternSourceSum S hS ∈
          S.image polynomialPatternSourceSum := Finset.min'_mem _ _
      obtain ⟨p, hpS, hpEq⟩ := Finset.mem_image.mp hminmem
      rw [← hpEq]
      exact hfloor p hpS
    · exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨pW, hpWS, rfl⟩)
  let C := polynomialPatternMinimalCluster (R := Nat.ceil β - 2) T hT
  have hC : C.Nonempty := polynomialPatternMinimalCluster_nonempty T hT
  have hcount : ∀ p ∈ S, (∑ r, (p r : ℕ)) = D := fun p hp =>
    polynomialPatternSurvivors_count hp
  obtain ⟨p₀, hp₀⟩ := hC
  have hC : C.Nonempty := ⟨p₀, hp₀⟩
  obtain ⟨cpat, hcpat, hpatReal⟩ :=
    eventually_uniform_survivor_gap_from_cluster hβ S hS hcount p₀ hp₀
  have hbaseT : Tendsto (fun q : ℕ => (q : ℝ) - K) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-(K : ℝ)) tendsto_natCast_atTop_atTop
  have hpatNat := hbaseT.eventually hpatReal
  have hη : 0 < polynomialPhaseLockExponent β :=
    polynomialPhaseLockExponent_pos hβ
  obtain ⟨cpatShift, hcpatShift, hpatShift⟩ :=
    exists_eventually_const_mul_natCast_rpow_le_sub_rpow hη hcpat K
  obtain ⟨cglobShift, hcglobShift, hglobShift⟩ :=
    exists_eventually_const_mul_natCast_rpow_le_sub_rpow hη hcgap Kshift
  let c₀ := min cpatShift cglobShift
  have hc₀ : 0 < c₀ := lt_min hcpatShift hcglobShift
  let c := B * c₀
  have hc : 0 < c := mul_pos hB hc₀
  refine ⟨K, M, ?_⟩
  dsimp only
  refine ⟨hS, ?_⟩
  change ∃ c : ℝ, 0 < c ∧ ∀ᶠ q : ℕ in atTop,
    ∀ ν ∈ activeAevalAtoms n (D * q + τ) Q \
        C.image (shiftedAtomPatternKey q K),
      B * polynomialPatternClusterMinValuation β C hC ((q : ℝ) - K) +
          c * (q : ℝ) ^ polynomialPhaseLockExponent β ≤
        atomValuation (fun i => B * (i : ℝ) ^ β) ν
  refine ⟨c, hc, ?_⟩
  let qLower := max Qres (max (Qgap + Kshift)
    (max (K + n) (max K (Kshift + J + 1))))
  filter_upwards [hpatNat, hpatShift, hglobShift,
    eventually_ge_atTop qLower] with q hpatq hpatShiftq hglobShiftq hq
  intro ν hν
  have hqres' : Qres ≤ q := (le_max_left _ _).trans hq
  have hqgap' : Qgap + Kshift ≤ q := by dsimp [qLower] at hq; omega
  have hqlarge' : K + n ≤ q := by dsimp [qLower] at hq; omega
  have hKq : K ≤ q := by dsimp [qLower] at hq; omega
  have hqshift : Kshift ≤ q := by dsimp [qLower] at hq; omega
  let qraw := q - Kshift
  have hqrawPos : 0 < qraw := by dsimp [qraw, qLower] at *; omega
  have hqgapRaw : Qgap ≤ qraw := by dsimp [qraw]; omega
  let s : Fin D → ℕ := fun i => qraw + δ i
  have hresq := hres q hqres'
  have hinvq := hresq.2.2
  have hJle' : J ≤ ∑ i, s i := by
    obtain ⟨i₀⟩ : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
    have hbase : J ≤ qraw := by dsimp [qraw, qLower] at *; omega
    exact hbase.trans ((show qraw ≤ s i₀ by simp [s]).trans
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀)))
  let Nraw := (∑ i, s i) + anchor 0 - J
  have hwraw' := witness_sum_add_shiftCode Q ha δ Nraw rfl hJle'
  have hNraw : Nraw = D * q + τ := by
    rw [key_weighted_sum] at hinvq
    change (∑ i, s i) + magnitudeShiftCode n Q anchor =
      Nraw + magnitudeMaxJetOrder n Q at hwraw'
    change (∑ i, s i) + magnitudeShiftCode n Q anchor =
      D * q + τ + magnitudeMaxJetOrder n Q at hinvq
    omega
  have hνActive : ν ∈ activeAevalAtoms n (D * q + τ) Q :=
    (Finset.mem_sdiff.mp hν).1
  have hνOutside : ν ∉ C.image (shiftedAtomPatternKey q K) :=
    (Finset.mem_sdiff.mp hν).2
  have hνAppears := (mem_activeAevalAtoms.mp hνActive).1
  have hgapq := hgap qraw hqgapRaw ν (by
    simpa only [hNraw, Nraw, J, D, s, qraw] using hνAppears)
  have hx0 : 0 ≤ (q : ℝ) - K :=
    sub_nonneg.mpr (by exact_mod_cast hKq)
  have hkeyWq : shiftedAtomPatternKey q K pW = key s := by
    calc
      shiftedAtomPatternKey q K pW =
          key (fun i => windowShift q K (g i : ℕ)) :=
        (key_windowShift_eq_shiftedAtomPatternKey pW g hg).symm
      _ = key s := by
        congr 1
        funext i
        dsimp [windowShift, K, g, s, qraw]
        omega
  have hminWitness :
      polynomialPatternClusterMinValuation β C hC ((q : ℝ) - K) ≤
        polynomialPatternPowerValuation β pW ((q : ℝ) - K) := by
    by_cases hpWC : pW ∈ C
    · exact polynomialPatternClusterMinValuation_le β hC _ hpWC
    · have hpWgap := hpatq pW (Finset.mem_sdiff.mpr ⟨hpWS, hpWC⟩)
      have hgapNonneg : 0 ≤ cpat * ((q : ℝ) - K) ^
          polynomialPhaseLockExponent β :=
        mul_nonneg hcpat.le (Real.rpow_nonneg hx0 _)
      have hp₀le : polynomialPatternPowerValuation β p₀ ((q : ℝ) - K) ≤
          polynomialPatternPowerValuation β pW ((q : ℝ) - K) := by
        linarith
      exact (polynomialPatternClusterMinValuation_le β hC _ hp₀).trans hp₀le
  have hpatCost : c₀ * (q : ℝ) ^ polynomialPhaseLockExponent β ≤
      cpat * ((q : ℝ) - K) ^ polynomialPhaseLockExponent β :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (Real.rpow_nonneg (Nat.cast_nonneg q) _)).trans hpatShiftq
  have hrawCast : (qraw : ℝ) = (q : ℝ) - Kshift := by
    dsimp [qraw]
    rw [Nat.cast_sub hqshift]
  have hrawOne : (1 : ℝ) ≤ qraw := by
    exact_mod_cast (show 1 ≤ qraw by omega)
  have hrawPow : (qraw : ℝ) ^ polynomialPhaseLockExponent β ≤
      (qraw : ℝ) ^ (β - 2) :=
    Real.rpow_le_rpow_of_exponent_le hrawOne (min_le_left _ _)
  have hglobCost : c₀ * (q : ℝ) ^ polynomialPhaseLockExponent β ≤
      cgap * (qraw : ℝ) ^ (β - 2) := by
    calc
      c₀ * (q : ℝ) ^ polynomialPhaseLockExponent β ≤
          cglobShift * (q : ℝ) ^ polynomialPhaseLockExponent β :=
        mul_le_mul_of_nonneg_right (min_le_right _ _)
          (Real.rpow_nonneg (Nat.cast_nonneg q) _)
      _ ≤ cgap * (qraw : ℝ) ^ polynomialPhaseLockExponent β := by
        simpa only [hrawCast] using hglobShiftq
      _ ≤ cgap * (qraw : ℝ) ^ (β - 2) :=
        mul_le_mul_of_nonneg_left hrawPow hcgap.le
  rcases hgapq with hwindow | hlose
  · have hsupp : ∀ i, ν i ≠ 0 →
        q - K ≤ i ∧ i < q - K + M := by
      intro i hi
      have hiw := hwindow.2 i hi
      dsimp [K, M, qraw] at *
      omega
    obtain ⟨p, hpcount, hpkey⟩ :=
      exists_boundedPattern_of_atom_support_interval ν hwindow.1 hsupp
    have hpS : p ∈ S := by
      apply mem_polynomialPatternSurvivors_of_aevalWeight_ne_zero hpcount hqlarge'
      rw [hpkey]
      exact (mem_activeAevalAtoms.mp hνActive).2
    have hpC : p ∉ C := by
      intro hp
      apply hνOutside
      exact Finset.mem_image.mpr ⟨p, hp, hpkey⟩
    have hpGap := hpatq p (Finset.mem_sdiff.mpr ⟨hpS, hpC⟩)
    have hminp₀ := polynomialPatternClusterMinValuation_le β hC
      ((q : ℝ) - K) hp₀
    have htotal :
        polynomialPatternClusterMinValuation β C hC ((q : ℝ) - K) +
            c₀ * (q : ℝ) ^ polynomialPhaseLockExponent β ≤
          polynomialPatternPowerValuation β p ((q : ℝ) - K) := by
      linarith
    have hpVal := atomValuation_shiftedAtomPatternKey
      (B := B) (β := β) p hKq
    rw [hpkey] at hpVal
    calc
      B * polynomialPatternClusterMinValuation β C hC ((q : ℝ) - K) +
          c * (q : ℝ) ^ polynomialPhaseLockExponent β =
          B * (polynomialPatternClusterMinValuation β C hC ((q : ℝ) - K) +
            c₀ * (q : ℝ) ^ polynomialPhaseLockExponent β) := by
        dsimp [c]
        ring
      _ ≤ B * polynomialPatternPowerValuation β p ((q : ℝ) - K) :=
        mul_le_mul_of_nonneg_left htotal hB.le
      _ = atomValuation (fun i => B * (i : ℝ) ^ β) ν := hpVal.symm
  · have hwitVal :
        (key s).sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) =
          polynomialPatternPowerValuation β pW ((q : ℝ) - K) := by
      calc
        (key s).sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) =
            atomValuation (fun i => (1 : ℝ) * (i : ℝ) ^ β) (key s) := by
          rw [atomValuation_scaledPower]
          simp
        _ = atomValuation (fun i => (1 : ℝ) * (i : ℝ) ^ β)
            (shiftedAtomPatternKey q K pW) := by rw [hkeyWq]
        _ = polynomialPatternPowerValuation β pW ((q : ℝ) - K) := by
          simpa using atomValuation_shiftedAtomPatternKey
            (B := (1 : ℝ)) (β := β) pW hKq
    have htotal :
        polynomialPatternClusterMinValuation β C hC ((q : ℝ) - K) +
            c₀ * (q : ℝ) ^ polynomialPhaseLockExponent β ≤
          ν.sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) := by
      rw [← hwitVal] at hminWitness
      linarith
    calc
      B * polynomialPatternClusterMinValuation β C hC ((q : ℝ) - K) +
          c * (q : ℝ) ^ polynomialPhaseLockExponent β =
          B * (polynomialPatternClusterMinValuation β C hC ((q : ℝ) - K) +
            c₀ * (q : ℝ) ^ polynomialPhaseLockExponent β) := by
        dsimp [c]
        ring
      _ ≤ B * ν.sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) :=
        mul_le_mul_of_nonneg_left htotal hB.le
      _ = atomValuation (fun i => B * (i : ℝ) ^ β) ν :=
        (atomValuation_scaledPower β B ν).symm

theorem eventually_natPow_mul_exp_neg_rpow_lt_one
    (P : ℕ) {c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    ∀ᶠ q : ℕ in atTop,
      (q : ℝ) ^ P * Real.exp (-(c * (q : ℝ) ^ η)) < 1 := by
  have hbase : Tendsto (fun q : ℕ => (q : ℝ) ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop
  have hdecayReal : Tendsto
      (fun x : ℝ => x ^ ((P : ℝ) / η) * Real.exp (-c * x))
      atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((P : ℝ) / η) c hc
  have hdecay := hdecayReal.comp hbase
  have hlt : ∀ᶠ q : ℕ in atTop,
      ((q : ℝ) ^ η) ^ ((P : ℝ) / η) *
        Real.exp (-c * (q : ℝ) ^ η) < 1 :=
    hdecay.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hlt] with q hq
  have hpow : ((q : ℝ) ^ η) ^ ((P : ℝ) / η) = (q : ℝ) ^ P := by
    rw [← Real.rpow_mul (Nat.cast_nonneg q),
      show η * ((P : ℝ) / η) = (P : ℝ) by field_simp,
      Real.rpow_natCast]
  simpa only [hpow, neg_mul] using hq

/-- An exponentially accurate normalized phase lock for integer ADE weights
cannot be supported by a singleton cluster. -/
theorem two_le_card_of_polynomialPhaseLock
    {β B c η : ℝ} (hc : 0 < c) (hη : 0 < η)
    {n D K τ M : ℕ}
    (F : PowerSeries ℂ) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ =
      Real.exp (-(B * (i : ℝ) ^ β)))
    (C : Finset (Fin M → Fin (D + 1))) (hC : C.Nonempty)
    (hactive : ∀ᶠ q : ℕ in atTop, ∀ p ∈ C,
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) ≠ 0)
    (P : ℕ)
    (hlock : ∀ᶠ q : ℕ in atTop,
      ‖∑ p ∈ C,
          aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) *
            (Real.exp (-(atomValuation (fun i => B * (i : ℝ) ^ β)
              (shiftedAtomPatternKey q K p) -
                B * polynomialPatternClusterMinValuation β C hC
                  ((q : ℝ) - K))) : ℂ) *
            normalizedAtomPhase F (fun i => B * (i : ℝ) ^ β)
              (shiftedAtomPatternKey q K p)‖ ≤
        (q : ℝ) ^ P * Real.exp (-(c * (q : ℝ) ^ η))) :
    2 ≤ C.card := by
  classical
  by_contra hnot
  have hcardLe : C.card ≤ 1 := by omega
  have hcardPos : 0 < C.card := Finset.card_pos.mpr hC
  have hcard : C.card = 1 := by omega
  obtain ⟨p, hCeq⟩ := Finset.card_eq_one.mp hcard
  have hpC : p ∈ C := by simp [hCeq]
  have hmin : ∀ q : ℕ,
      polynomialPatternClusterMinValuation β C hC ((q : ℝ) - K) =
        polynomialPatternPowerValuation β p ((q : ℝ) - K) := by
    intro q
    obtain ⟨r, hrC, hr⟩ := exists_pattern_eq_clusterMinValuation β hC
      ((q : ℝ) - K)
    have hrp : r = p := by simpa [hCeq] using hrC
    subst r
    exact hr.symm
  have hsmall := eventually_natPow_mul_exp_neg_rpow_lt_one P hc hη
  have hfalse : ∀ᶠ q : ℕ in atTop, False := by
    filter_upwards [hactive, hlock, hsmall, eventually_ge_atTop K] with
        q hactiveq hlockq hsmallq hKq
    have hw := hactiveq p hpC
    have hwLower := aevalWeight_norm_ge_one n (D * q + τ) Q
      (shiftedAtomPatternKey q K p) hQint hw
    have hval := atomValuation_shiftedAtomPatternKey
      (B := B) (β := β) p hKq
    have hdelta :
        atomValuation (fun i => B * (i : ℝ) ^ β)
            (shiftedAtomPatternKey q K p) -
          B * polynomialPatternClusterMinValuation β C hC ((q : ℝ) - K) = 0 := by
      rw [hval, hmin]
      ring
    let f : (Fin M → Fin (D + 1)) → ℂ := fun r =>
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K r) *
        (Real.exp (-(atomValuation (fun i => B * (i : ℝ) ^ β)
          (shiftedAtomPatternKey q K r) -
            B * polynomialPatternClusterMinValuation β C hC
              ((q : ℝ) - K))) : ℂ) *
        normalizedAtomPhase F (fun i => B * (i : ℝ) ^ β)
          (shiftedAtomPatternKey q K r)
    have hsum : ∑ r ∈ C, f r = f p := by simp [hCeq]
    have hlockp : ‖f p‖ ≤
        (q : ℝ) ^ P * Real.exp (-(c * (q : ℝ) ^ η)) := by
      rw [← hsum]
      simpa only [f] using hlockq
    have hphase :
        ‖normalizedAtomPhase F (fun i => B * (i : ℝ) ^ β)
          (shiftedAtomPatternKey q K p)‖ = 1 :=
      norm_normalizedAtomPhase F (fun i => B * (i : ℝ) ^ β) hb _
    have hterm : 1 ≤ ‖f p‖ := by
      dsimp only [f]
      rw [norm_mul, norm_mul, hdelta, neg_zero, Real.exp_zero, hphase]
      simpa using hwLower
    exact (not_lt_of_ge (hterm.trans hlockp)) hsmallq
  obtain ⟨q, hq⟩ := hfalse.exists
  exact hq.elim

/- Exact polynomial Taylor magnitudes force a finite, nonsingleton minimal
Prouhet cluster whose normalized ADE phase sum is exponentially small on
every prescribed top-degree residue class. -/
set_option maxHeartbeats 600000 in
theorem exists_polynomialTaylorProuhetPhaseLock
    {β B : ℝ} (hβ : 2 < β) (hB : 0 < B) {n : ℕ}
    (F : PowerSeries ℂ) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQint : ∀ a, ∃ z : ℤ, MvPolynomial.coeff a Q = (z : ℂ))
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ =
      Real.exp (-(B * (i : ℝ) ^ β)))
    (hrel : aeval (formalJets n F) Q = 0)
    (hDpos : 0 < magnitudeMaxJetDegree n Q)
    (τ : ℕ) (hτ : τ < magnitudeMaxJetDegree n Q) :
    ∃ (K M : ℕ),
      let D := magnitudeMaxJetDegree n Q
      let S := polynomialPatternSurvivors n D K τ Q M
      ∃ hS : S.Nonempty,
        let T := polynomialPatternLeastSourceClass S hS
        let hT := polynomialPatternLeastSourceClass_nonempty S hS
        let C := polynomialPatternMinimalCluster (R := Nat.ceil β - 2) T hT
        let hC := polynomialPatternMinimalCluster_nonempty T hT
        let m : ℕ → ℝ := fun q => B *
          polynomialPatternClusterMinValuation β C hC ((q : ℝ) - K)
        ∃ (W : (Fin M → Fin (D + 1)) → Polynomial ℤ)
            (c A : ℝ) (P : ℕ),
          0 < c ∧ 0 < A ∧ 2 ≤ C.card ∧ C ⊆ S ∧
          (∀ p ∈ S, W p ≠ 0 ∧ ∀ q, K + n ≤ q →
            aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) =
              (((W p).eval (q : ℤ) : ℤ) : ℂ)) ∧
          (∀ p ∈ C, ∀ r ∈ C,
            (∀ j < Nat.ceil β,
              polynomialPatternMoment p j = polynomialPatternMoment r j) ∧
            (Polynomial.X - 1) ^ Nat.ceil β ∣
              atomPatternDifferencePolynomial p r) ∧
          (∀ᶠ q : ℕ in atTop, ∀ p ∈ C,
            0 ≤ atomValuation (fun i => B * (i : ℝ) ^ β)
                (shiftedAtomPatternKey q K p) - m q ∧
            atomValuation (fun i => B * (i : ℝ) ^ β)
                (shiftedAtomPatternKey q K p) - m q ≤ A) ∧
          (∀ᶠ q : ℕ in atTop,
            ‖∑ p ∈ C,
                aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) *
                  (Real.exp (-(atomValuation (fun i => B * (i : ℝ) ^ β)
                    (shiftedAtomPatternKey q K p) - m q)) : ℂ) *
                  normalizedAtomPhase F (fun i => B * (i : ℝ) ^ β)
                    (shiftedAtomPatternKey q K p)‖ ≤
              (q : ℝ) ^ P * Real.exp (-(c * (q : ℝ) ^
                polynomialPhaseLockExponent β))) := by
  classical
  obtain ⟨K, M, hdata⟩ :=
    exists_residueCluster_activeAtom_gap hβ hB Q hDpos τ hτ
  let D := magnitudeMaxJetDegree n Q
  let S := polynomialPatternSurvivors n D K τ Q M
  change ∃ hS : S.Nonempty,
    let T := polynomialPatternLeastSourceClass S hS
    let hT := polynomialPatternLeastSourceClass_nonempty S hS
    let C := polynomialPatternMinimalCluster (R := Nat.ceil β - 2) T hT
    let hC := polynomialPatternMinimalCluster_nonempty T hT
    let m : ℕ → ℝ := fun q => B *
      polynomialPatternClusterMinValuation β C hC ((q : ℝ) - K)
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ q : ℕ in atTop,
      ∀ ν ∈ activeAevalAtoms n (D * q + τ) Q \
          C.image (shiftedAtomPatternKey q K),
        m q + c * (q : ℝ) ^ polynomialPhaseLockExponent β ≤
          atomValuation (fun i => B * (i : ℝ) ^ β) ν at hdata
  obtain ⟨hS, c, hc, hgap⟩ := hdata
  let T := polynomialPatternLeastSourceClass S hS
  let hT : T.Nonempty := polynomialPatternLeastSourceClass_nonempty S hS
  let C := polynomialPatternMinimalCluster (R := Nat.ceil β - 2) T hT
  let hC : C.Nonempty := polynomialPatternMinimalCluster_nonempty T hT
  let m : ℕ → ℝ := fun q => B *
    polynomialPatternClusterMinValuation β C hC ((q : ℝ) - K)
  have hcountS : ∀ p ∈ S, (∑ r, (p r : ℕ)) = D := fun p hp =>
    polynomialPatternSurvivors_count hp
  have hCS : C ⊆ S :=
    (polynomialPatternMinimalCluster_subset T hT).trans
      (polynomialPatternLeastSourceClass_subset S hS)
  let cint : (Fin (n + 2) →₀ ℕ) → ℤ := fun a => (hQint a).choose
  have hcint : ∀ a, MvPolynomial.coeff a Q = (cint a : ℂ) := fun a =>
    (hQint a).choose_spec
  let W : (Fin M → Fin (D + 1)) → Polynomial ℤ := fun p =>
    polynomialPatternWeightPolyInt n D K τ Q cint p
  have hW : ∀ p ∈ S, W p ≠ 0 ∧ ∀ q, K + n ≤ q →
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) =
        (((W p).eval (q : ℤ) : ℤ) : ℂ) := by
    intro p hp
    have hmap := map_polynomialPatternWeightPolyInt n D K τ Q cint hcint p
    have hWne : W p ≠ 0 := by
      intro hzero
      apply polynomialPatternSurvivors_weightPoly_ne_zero hp
      rw [← hmap]
      have hz : polynomialPatternWeightPolyInt n D K τ Q cint p = 0 := by
        simpa [W] using hzero
      rw [hz, Polynomial.map_zero]
    refine ⟨hWne, fun q hq => ?_⟩
    rw [aevalWeight_shiftedAtomPatternKey_eq_eval_poly n D K τ Q p
      (hcountS p hp) hq, ← hmap]
    simp [W]
  have hcluster : ∀ p ∈ C, ∀ r ∈ C,
      (∀ j < Nat.ceil β,
        polynomialPatternMoment p j = polynomialPatternMoment r j) ∧
      (Polynomial.X - 1) ^ Nat.ceil β ∣
        atomPatternDifferencePolynomial p r := by
    intro p hp r hr
    exact ⟨polynomialPatternCluster_moments S hS hcountS hp hr,
      polynomialPatternCluster_prouhet_dvd S hS hcountS hp hr⟩
  have hactiveS := polynomialPatternSurvivors_eventually_weight_ne_zero
    (n := n) (D := D) (K := K) (τ := τ) (M := M) Q
  have hactive : ∀ᶠ q : ℕ in atTop, ∀ p ∈ C,
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) ≠ 0 := by
    filter_upwards [hactiveS] with q hq
    intro p hp
    exact hq p (hCS hp)
  have hgap' : ∀ᶠ q : ℕ in atTop,
      ∀ ν ∈ activeAevalAtoms n (D * q + τ) Q \
          C.image (shiftedAtomPatternKey q K),
        m q + c * (q : ℝ) ^ polynomialPhaseLockExponent β ≤
          atomValuation (fun i => B * (i : ℝ) ^ β) ν := by
    simpa [m] using hgap
  obtain ⟨P, hlock⟩ := eventually_polynomialPhaseLock_of_activeAtom_gap
    F Q hb hrel C m hactive hgap'
  obtain ⟨p₀, hp₀⟩ := hC
  have hC : C.Nonempty := ⟨p₀, hp₀⟩
  have hcountT : ∀ p ∈ T, (∑ r, (p r : ℕ)) = D := fun p hp =>
    hcountS p (polynomialPatternLeastSourceClass_subset S hS hp)
  have hsumT : ∀ p ∈ T,
      (∑ r : Fin M, (r : ℕ) * (p r : ℕ)) =
        minimalPolynomialPatternSourceSum S hS := by
    intro p hp
    simpa [polynomialPatternSourceSum] using
      sourceSum_eq_of_mem_polynomialPatternLeastSourceClass hp
  obtain ⟨C₀, hC₀, hdeltaReal⟩ :=
    eventually_polynomialPatternPower_cluster_delta_bounds
      hβ T hT hcountT hsumT p₀ hp₀
  have hbaseT : Tendsto (fun q : ℕ => (q : ℝ) - K) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-(K : ℝ)) tendsto_natCast_atTop_atTop
  have hdeltaNat := hbaseT.eventually hdeltaReal
  let A := 2 * B * C₀
  have hA : 0 < A := mul_pos (mul_pos (by norm_num) hB) hC₀
  have hdelta : ∀ᶠ q : ℕ in atTop, ∀ p ∈ C,
      0 ≤ atomValuation (fun i => B * (i : ℝ) ^ β)
          (shiftedAtomPatternKey q K p) - m q ∧
      atomValuation (fun i => B * (i : ℝ) ^ β)
          (shiftedAtomPatternKey q K p) - m q ≤ A := by
    filter_upwards [hdeltaNat, eventually_ge_atTop K] with q hq hKq
    intro p hp
    have hpdelta := hq p hp
    have hpval := atomValuation_shiftedAtomPatternKey
      (B := B) (β := β) p hKq
    dsimp [m]
    rw [hpval]
    constructor
    · rw [← mul_sub]
      exact mul_nonneg hB.le hpdelta.1
    · rw [← mul_sub]
      calc
        B * (polynomialPatternPowerValuation β p ((q : ℝ) - K) -
            polynomialPatternClusterMinValuation β C hC ((q : ℝ) - K)) ≤
            B * (2 * C₀) := mul_le_mul_of_nonneg_left hpdelta.2 hB.le
        _ = A := by dsimp [A]; ring
  have hη : 0 < polynomialPhaseLockExponent β :=
    polynomialPhaseLockExponent_pos hβ
  have hcard : 2 ≤ C.card :=
    two_le_card_of_polynomialPhaseLock hc hη F Q hQint hb C hC
      hactive P (by simpa [m] using hlock)
  refine ⟨K, M, ?_⟩
  dsimp only
  refine ⟨hS, ?_⟩
  exact ⟨W, c, A, P, hc, hA, hcard, hCS, hW, hcluster, hdelta, hlock⟩

end

end GaloisForLFunctions
