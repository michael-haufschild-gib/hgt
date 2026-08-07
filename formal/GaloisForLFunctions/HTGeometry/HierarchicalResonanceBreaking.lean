import GaloisForLFunctions.HTGeometry.DATaylorLogRatioResonance

open Filter Finset PowerSeries MvPolynomial Polynomial Topology
open scoped Topology ENNReal

namespace GaloisForLFunctions

noncomputable section

/-- An eventual multiplicative lower step makes a positive sequence monotone on its tail. -/
theorem monotone_tail_of_geometric_lower {b : ℕ → ℝ} (hbpos : ∀ i, 0 < b i)
    {r : ℝ} (hr1 : 1 < r) {N i j : ℕ}
    (hlower : ∀ m ≥ N, r * b m ≤ b (m + 1)) (hi : N ≤ i) (hij : i ≤ j) :
    b i ≤ b j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
      have hjN : N ≤ j := hi.trans hij
      calc
        b i ≤ b j := ih
        _ ≤ r * b j := by nlinarith [hbpos j]
        _ ≤ b (j + 1) := hlower j hjN

/-- Under an eventual geometric lower step, the sequence beats every fixed polynomial scale. -/
theorem exists_const_mul_pow_lt_of_geometric_lower
    {b : ℕ → ℝ} (hbpos : ∀ i, 0 < b i)
    {r : ℝ} (hr1 : 1 < r) {N : ℕ}
    (hlower : ∀ m ≥ N, r * b m ≤ b (m + 1))
    (A : ℝ) (hA : 0 < A) (C E : ℕ) (hC : 0 < C) :
    ∃ Q₀ : ℕ, ∀ q ≥ Q₀,
      A * (((C * (q + 1)) ^ E : ℕ) : ℝ) < b q := by
  have hr0 : 0 ≤ r := (zero_lt_one.trans hr1).le
  have hratio : ∀ m ≥ N, r ≤ b (m + 1) / b m := by
    intro m hm
    rw [le_div_iff₀ (hbpos m)]
    exact hlower m hm
  let c : ℝ := b N / r ^ N
  have hc : 0 < c := div_pos (hbpos N) (pow_pos (zero_lt_one.trans hr1) N)
  let K : ℝ := A * (C : ℝ) ^ E * 2 ^ E / c
  have hK : 0 < K := by dsimp [K]; positivity
  have hlittle : (fun q : ℕ => K * (q : ℝ) ^ E) =o[atTop] fun q => r ^ q :=
    (isLittleO_pow_const_const_pow_of_one_lt E hr1).const_mul_left K
  have hright : ∀ᶠ q : ℕ in atTop, 0 < ‖r ^ q‖ :=
    Filter.Eventually.of_forall fun q =>
      norm_pos_iff.mpr (pow_ne_zero q (ne_of_gt (zero_lt_one.trans hr1)))
  have hlt : ∀ᶠ q : ℕ in atTop, K * (q : ℝ) ^ E < r ^ q := by
    filter_upwards [hlittle.eventuallyLT_norm_of_eventually_pos hright,
      eventually_ge_atTop 1] with q hq hq1
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (mul_pos hK (pow_pos (by exact_mod_cast hq1) E)),
      abs_of_pos (pow_pos (zero_lt_one.trans hr1) q)] at hq
    exact hq
  obtain ⟨Q₁, hQ₁⟩ := Filter.eventually_atTop.mp hlt
  refine ⟨max N (max Q₁ 1), fun q hq => ?_⟩
  have hqN : N ≤ q := (le_max_left _ _).trans hq
  have hqQ₁ : Q₁ ≤ q := (le_trans (le_max_left _ _) (le_max_right N _)).trans hq
  have hq1 : 1 ≤ q := (le_trans (le_max_right _ _) (le_max_right N _)).trans hq
  have hqcast : (q + 1 : ℕ) ≤ 2 * q := by omega
  have hpoly :
      A * (((C * (q + 1)) ^ E : ℕ) : ℝ) ≤
        A * (C : ℝ) ^ E * 2 ^ E * (q : ℝ) ^ E := by
    push_cast
    have hcast : (q : ℝ) + 1 ≤ 2 * q := by exact_mod_cast hqcast
    calc
      A * ((C : ℝ) * ((q : ℝ) + 1)) ^ E
          ≤ A * ((C : ℝ) * (2 * (q : ℝ))) ^ E := by gcongr
      _ = A * (C : ℝ) ^ E * 2 ^ E * (q : ℝ) ^ E := by ring
  have hscaled : A * (C : ℝ) ^ E * 2 ^ E * (q : ℝ) ^ E < c * r ^ q := by
    have h := mul_lt_mul_of_pos_left (hQ₁ q hqQ₁) hc
    dsimp [K] at h
    field_simp [ne_of_gt hc] at h
    simpa only [mul_assoc] using h
  have hgeo := ratio_iterate_lower_bound (N := N) (n := N) (k := q - N)
    hr0 (fun m _ => hbpos m) hratio le_rfl
  have hpow : r ^ (q - N) = r ^ q / r ^ N :=
    pow_sub₀ r (ne_of_gt (zero_lt_one.trans hr1)) hqN
  rw [hpow] at hgeo
  have hcgeo : c * r ^ q ≤ b q := by
    dsimp [c]
    calc
      b N / r ^ N * r ^ q = (r ^ q / r ^ N) * b N := by ring
      _ ≤ b q := by simpa [Nat.add_sub_of_le hqN] using hgeo
  exact hpoly.trans_lt (hscaled.trans_le hcgeo)

/-- With only a geometric lower step, measure the balanced witness at its largest fixed offset.
Every atom inside the logarithmic bend then still has top jet degree and bounded maximum source. -/
theorem near_balanced_atom_count_eq_and_supportMax_lt_of_geometric_lower
    {b : ℕ → ℝ} (hbpos : ∀ i, 0 < b i)
    {r : ℝ} (hr1 : 1 < r) {Ntail : ℕ}
    (hlower : ∀ m ≥ Ntail, r * b m ≤ b (m + 1))
    {n N D J q K : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hD : 0 < D) (hDmax : D = magnitudeMaxJetDegree n Q)
    (δ : Fin D → ℕ) {P : ℝ} {ν : ℕ →₀ ℕ}
    (hν : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n))
    (hnear : ν.sum (fun i k => (k : ℝ) * b i) <
      (key (fun i : Fin D => q + δ i)).sum (fun i k => (k : ℝ) * b i) +
        Real.log (P + 1))
    (hlog : Real.log (P + 1) ≤ b (q + magnitudeOffsetMax δ))
    (hDqN : D * q ≤ N + J) (hNZ : magnitudeMaxXDegree Q < N)
    (hqtail : Ntail ≤ q)
    (hqthreshold : max (2 * (J + magnitudeMaxXDegree Q) + 2)
      (2 * D * (magnitudeOffsetMax δ + K)) ≤ q)
    (hK : (D : ℝ) + 1 < r ^ K) :
    ν.sum (fun _ k => k) = D ∧
      ν.support.max' (appearing_atom_support_nonempty_of_maxX_lt_level Q hν hNZ) <
        q + magnitudeOffsetMax δ + K := by
  let hsupp : ν.support.Nonempty :=
    appearing_atom_support_nonempty_of_maxX_lt_level Q hν hNZ
  let imax := ν.support.max' hsupp
  let B := magnitudeOffsetMax δ
  have hr0 : 0 ≤ r := (zero_lt_one.trans hr1).le
  have hratio : ∀ m ≥ Ntail, r ≤ b (m + 1) / b m := by
    intro m hm
    rw [le_div_iff₀ (hbpos m)]
    exact hlower m hm
  have hWval :
      (key (fun i : Fin D => q + δ i)).sum (fun i k => (k : ℝ) * b i) ≤
        (D : ℝ) * b (q + B) := by
    rw [valuation_eq_key_sum]
    calc
      ∑ i : Fin D, b (q + δ i) ≤ ∑ _i : Fin D, b (q + B) := by
        apply Finset.sum_le_sum
        intro i _
        exact monotone_tail_of_geometric_lower hbpos hr1 hlower
          (hqtail.trans (Nat.le_add_right q (δ i)))
          (Nat.add_le_add_left (offset_le_magnitudeOffsetMax δ i) q)
      _ = (D : ℝ) * b (q + B) := by
        simp [Finset.card_univ]
  have hfar : q + B + K ≤ imax → False := by
    intro hqBK
    have hcenterMax : q + B ≤ imax := (Nat.le_add_right (q + B) K).trans hqBK
    have hKdiff : K ≤ imax - (q + B) := by omega
    have hcenterTail : Ntail ≤ q + B := hqtail.trans (Nat.le_add_right q B)
    have hgeo := ratio_iterate_lower_bound (N := Ntail) (n := q + B)
      (k := imax - (q + B)) hr0 (fun m _ => hbpos m) hratio hcenterTail
    have hcenterAdd : q + B + (imax - (q + B)) = imax :=
      Nat.add_sub_of_le hcenterMax
    rw [hcenterAdd] at hgeo
    have hpow : r ^ K ≤ r ^ (imax - (q + B)) :=
      pow_le_pow_right₀ hr1.le hKdiff
    have hpowb : r ^ K * b (q + B) ≤ b imax :=
      (mul_le_mul_of_nonneg_right hpow (hbpos (q + B)).le).trans hgeo
    have hvalMax : b imax ≤ ν.sum (fun i k => (k : ℝ) * b i) := by
      simpa [imax] using valuation_ge_b_max (fun i => (hbpos i).le) hsupp
    have hscale : ((D : ℝ) + 1) * b (q + B) < r ^ K * b (q + B) :=
      mul_lt_mul_of_pos_right hK (hbpos (q + B))
    have hnear' : ν.sum (fun i k => (k : ℝ) * b i) <
        ((D : ℝ) + 1) * b (q + B) := by
      calc
        ν.sum (fun i k => (k : ℝ) * b i) <
            (key (fun i : Fin D => q + δ i)).sum (fun i k => (k : ℝ) * b i) +
              Real.log (P + 1) := hnear
        _ ≤ (D : ℝ) * b (q + B) + b (q + B) := add_le_add hWval hlog
        _ = ((D : ℝ) + 1) * b (q + B) := by ring
    exact (not_lt_of_ge (hpowb.trans hvalMax)) (hscale.trans' hnear')
  have hcountle := appearing_atom_count_le Q hν
  rw [← hDmax] at hcountle
  have hcount : ν.sum (fun _ k => k) = D := by
    rcases hcountle.eq_or_lt with heq | hlt
    · exact heq
    · by_cases hDone : D = 1
      · have hzero : ν.sum (fun _ k => k) = 0 := by omega
        obtain ⟨i, hi⟩ := hsupp
        have hibound := finsupp_apply_le_count ν i
        rw [hzero] at hibound
        exact False.elim ((Finsupp.mem_support_iff.mp hi)
          (Nat.eq_zero_of_le_zero hibound))
      · have hDtwo : 2 ≤ D := by omega
        have hcountSmall : ν.sum (fun _ k => k) ≤ D - 1 := by omega
        have hweightLower := (appearing_atom_weighted_sum_bounds Q hν).1
        have hweightMax := weighted_sum_le_max_mul_count hsupp
        have hweightUpper : ν.sum (fun i k => i * k) ≤ imax * (D - 1) :=
          hweightMax.trans (Nat.mul_le_mul_left imax hcountSmall)
        have hDqMax : D * q ≤
            imax * (D - 1) + J + magnitudeMaxXDegree Q := by
          have hNsplit : N - magnitudeMaxXDegree Q + magnitudeMaxXDegree Q = N :=
            Nat.sub_add_cancel hNZ.le
          omega
        have hfactor := lowerDegree_max_ge_ratio_factor hDtwo hDqMax
          ((le_max_left _ _).trans hqthreshold)
        have hqDK : 2 * D * (B + K) ≤ q := by
          simpa only [B] using (le_max_right _ _).trans hqthreshold
        have hBKq : ((B + K : ℕ) : ℝ) ≤ (q : ℝ) / (2 * D : ℕ) := by
          rw [le_div_iff₀]
          · have hnat : (B + K) * (2 * D) ≤ q := by
              calc
                (B + K) * (2 * D) = 2 * D * (B + K) := by ring
                _ ≤ q := hqDK
            exact_mod_cast hnat
          · exact_mod_cast (show 0 < 2 * D by omega)
        have hqBKreal : ((q + B + K : ℕ) : ℝ) ≤ (imax : ℝ) := by
          push_cast
          have hsplit :
              (1 + 1 / (2 * (D : ℝ))) * (q : ℝ) =
                (q : ℝ) + (q : ℝ) / (2 * (D : ℝ)) := by ring
          rw [hsplit] at hfactor
          norm_num at hBKq
          linarith
        have hqBK : q + B + K ≤ imax := by exact_mod_cast hqBKreal
        exact False.elim (hfar hqBK)
  refine ⟨hcount, ?_⟩
  exact lt_of_not_ge hfar

/-- A positive-degree integer-normalized ADE under an eventual geometric lower step produces two
distinct top-degree atoms in one fixed window with logarithmic valuation defect at every large
balanced scale. -/
theorem exists_eventually_uniformGeometric_bend_pair_of_positiveJetDegree
    {b : ℕ → ℝ} (hbpos : ∀ i, 0 < b i)
    {r : ℝ} (hr1 : 1 < r) {Nlower : ℕ}
    (hlower : ∀ m ≥ Nlower, r * b m ≤ b (m + 1))
    {n : ℕ} (F : PowerSeries ℂ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ = Real.exp (-b i))
    (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hrel : aeval (formalJets n F) Q = 0)
    (hDpos : 0 < magnitudeMaxJetDegree n Q) :
    ∃ D K C Q₀ : ℕ, 0 < D ∧ 0 < C ∧ ∀ q ≥ Q₀,
      ∃ ν₀ ν₁ : ℕ →₀ ℕ,
        ν₀ ≠ ν₁ ∧
        ν₀.sum (fun _ k => k) = D ∧ ν₁.sum (fun _ k => k) = D ∧
        (∀ i, ν₀ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        (∀ i, ν₁ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        0 ≤ ν₁.sum (fun i k => (k : ℝ) * b i) -
          ν₀.sum (fun i k => (k : ℝ) * b i) ∧
        ν₁.sum (fun i k => (k : ℝ) * b i) -
            ν₀.sum (fun i k => (k : ℝ) * b i) <
          (C : ℝ) * Real.log ((q : ℝ) + 2) := by
  classical
  let Z := magnitudeMaxXDegree Q
  let O := magnitudeMaxJetOrder n Q
  obtain ⟨anchor, ha, haD, _haMax⟩ :=
    exists_maxShiftCode_topDegree_anchor Q hDpos
  let D := jetMonomialDegree n anchor
  have hDmax : D = magnitudeMaxJetDegree n Q := by simpa [D] using haD
  have hD : 0 < D := by rw [hDmax]; exact hDpos
  have haPos : 0 < jetMonomialDegree n anchor := by simpa [D] using hD
  obtain ⟨δ, _hδinj, Qbal, hbalanced⟩ :=
    exists_eventually_balanced_nonzero_aevalWeight ha haPos
  let J := jetMonomialOrder n anchor
  let Boff := magnitudeOffsetMax δ
  let E := D + O
  let C := E + 1
  let A : ℝ := magnitudeCoefficientMass Q * (((O + 1) ^ O : ℕ) : ℝ)
  have hCoeffMass : 0 < magnitudeCoefficientMass Q := by
    rw [magnitudeCoefficientMass]
    exact Finset.sum_pos' (fun _ _ => norm_nonneg _)
      ⟨anchor, ha, norm_pos_iff.mpr (MvPolynomial.mem_support_iff.mp ha)⟩
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos hCoeffMass (by positivity)
  have hpowT : Tendsto (fun k : ℕ => r ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hr1
  obtain ⟨Kstep, hKstep⟩ : ∃ Kstep : ℕ, (D : ℝ) + 1 < r ^ Kstep :=
    (hpowT.eventually_gt_atTop ((D : ℝ) + 1)).exists
  let Kraw := Boff + Kstep
  let K := D * Kraw + J + Z
  let Llevel := D * (Boff + 1) + anchor 0 + 1
  have hLlevel : 0 < Llevel := by dsimp [Llevel]; omega
  obtain ⟨Qdom, hQdom⟩ := exists_const_mul_pow_lt_of_geometric_lower
    hbpos hr1 hlower A hA Llevel E hLlevel
  have hlargeEv : ∀ᶠ q : ℕ in atTop,
      A * (Llevel : ℝ) ^ E + 1 ≤ (q : ℝ) + 2 :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).eventually_ge_atTop
      (A * (Llevel : ℝ) ^ E + 1)
  obtain ⟨Qlarge, hQlarge⟩ := Filter.eventually_atTop.mp hlargeEv
  let Q₀ := max Qbal (max Qdom (max Qlarge
    (max Nlower (max (D * Kraw + J + Z)
      (max (2 * (J + Z) + 2) (2 * D * Kraw))))))
  refine ⟨D, K, C, Q₀, hD, by dsimp [C, E]; omega, fun q hq => ?_⟩
  have hqbal : Qbal ≤ q := by dsimp [Q₀] at hq; omega
  have hqdom : Qdom ≤ q := by dsimp [Q₀] at hq; omega
  have hqlarge : Qlarge ≤ q := by dsimp [Q₀] at hq; omega
  have hqlower : Nlower ≤ q := by dsimp [Q₀] at hq; omega
  have hqK : D * Kraw + J + Z ≤ q := by dsimp [Q₀] at hq; omega
  have hqthreshold : max (2 * (J + Z) + 2) (2 * D * Kraw) ≤ q := by
    dsimp [Q₀] at hq
    omega
  let s : Fin (jetMonomialDegree n anchor) → ℕ := fun i => q + δ i
  let N := (∑ i, s i) + anchor 0 - J
  have hqJ : J ≤ q := by omega
  have hqsum : q ≤ ∑ i, s i :=
    le_sum_of_le_apply haPos fun i => by simp [s]
  have hJsum : J ≤ (∑ i, s i) + anchor 0 :=
    hqJ.trans (hqsum.trans (Nat.le_add_right _ _))
  have hNadd : N + J = (∑ i, s i) + anchor 0 := by
    dsimp [N]
    exact Nat.sub_add_cancel hJsum
  have hsLower : D * q ≤ ∑ i, s i :=
    mul_le_sum_of_le_apply fun i => by simp [s]
  have hDqN : D * q ≤ N + J := by rw [hNadd]; omega
  have hNZ : Z < N := by
    have hqJZ : J + Z < q := by
      have hbase : J + Z < D * Kraw + J + Z + 1 := by omega
      dsimp [Q₀] at hq
      omega
    have hqD : q ≤ D * q := by
      simpa [one_mul] using Nat.mul_le_mul_right q (show 1 ≤ D by omega)
    dsimp [Z]
    change magnitudeMaxXDegree Q < N
    omega
  obtain ⟨hνw, hww, _hgroup⟩ :
      key s ∈ (sigmaIdx n N Q).image (atomKeyOf n) ∧
        aevalWeight n N Q (key s) ≠ 0 ∧
        balancedJetGroup n N (jetMonomialDegree n anchor) Q s =
          topShiftJetGroup n Q anchor := by
    simpa only [s, N, J] using hbalanced q hqbal
  let P : ℝ := A * (((N + 1) ^ E : ℕ) : ℝ)
  have hsUpper : (∑ i, s i) ≤ D * (q + Boff) :=
    sum_le_mul_of_apply_le fun i => by
      dsimp [s]
      exact Nat.add_le_add_left (offset_le_magnitudeOffsetMax δ i) q
  have hNupper : N + 1 ≤ D * (q + Boff) + anchor 0 + 1 := by
    dsimp [N]
    omega
  have hlevel : N + 1 ≤ Llevel * (q + 1) := by
    have hbaseNat : q + Boff ≤ (Boff + 1) * (q + 1) := by
      calc
        q + Boff ≤ q + Boff + (Boff * q + 1) := Nat.le_add_right _ _
        _ = (Boff + 1) * (q + 1) := by ring
    have hjet : D * (q + Boff) ≤ D * (Boff + 1) * (q + 1) := by
      calc
        D * (q + Boff) ≤ D * ((Boff + 1) * (q + 1)) :=
          Nat.mul_le_mul_left D hbaseNat
        _ = D * (Boff + 1) * (q + 1) := by ring
    have hconst : anchor 0 + 1 ≤ (anchor 0 + 1) * (q + 1) := by
      calc
        anchor 0 + 1 ≤ (anchor 0 + 1) + (anchor 0 + 1) * q := Nat.le_add_right _ _
        _ = (anchor 0 + 1) * (q + 1) := by ring
    calc
      N + 1 ≤ D * (q + Boff) + anchor 0 + 1 := hNupper
      _ ≤ D * (Boff + 1) * (q + 1) + (anchor 0 + 1) * (q + 1) := by omega
      _ = Llevel * (q + 1) := by dsimp [Llevel]; ring
  have hPdom : P < b q := by
    have hpowLevel : (((N + 1) ^ E : ℕ) : ℝ) ≤
        (((Llevel * (q + 1)) ^ E : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_left hlevel E
    calc
      P ≤ A * (((Llevel * (q + 1)) ^ E : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hpowLevel hA.le
      _ < b q := hQdom q hqdom
  have hP0 : 0 < P := by dsimp [P]; positivity
  have hlog : Real.log (P + 1) ≤ b q := by
    exact (Real.log_le_sub_one_of_pos (by linarith : 0 < P + 1)).trans
      (by simpa using hPdom.le)
  have hlogCenter : Real.log (P + 1) ≤ b (q + magnitudeOffsetMax δ) :=
    hlog.trans (monotone_tail_of_geometric_lower hbpos hr1 hlower hqlower
      (Nat.le_add_right q (magnitudeOffsetMax δ)))
  obtain ⟨ν₀, ν₁, hν₀, hw₀, hmin, hν₁, hw₁, hne, hgap⟩ :=
    exists_near_min_nonzero_aevalWeight_of_relation F Q hb hQint hrel hνw hww
  have hgapP : ν₁.sum (fun i k => (k : ℝ) * b i) <
      ν₀.sum (fun i k => (k : ℝ) * b i) + Real.log (P + 1) := by
    simpa [P, A, E, O, hDmax] using hgap
  have hlogpos : 0 < Real.log (P + 1) := Real.log_pos (by linarith)
  have hν₀near : ν₀.sum (fun i k => (k : ℝ) * b i) <
      (key s).sum (fun i k => (k : ℝ) * b i) + Real.log (P + 1) :=
    (hmin (key s) hνw hww).trans_lt (lt_add_of_pos_right _ hlogpos)
  have hν₁near : ν₁.sum (fun i k => (k : ℝ) * b i) <
      (key s).sum (fun i k => (k : ℝ) * b i) + Real.log (P + 1) :=
    hgapP.trans_le (add_le_add (hmin (key s) hνw hww) le_rfl)
  obtain ⟨hν₀count, hν₀max⟩ :=
    near_balanced_atom_count_eq_and_supportMax_lt_of_geometric_lower
      hbpos hr1 hlower Q hD hDmax δ hν₀ (by simpa [s] using hν₀near)
      hlogCenter hDqN (by simpa [Z] using hNZ) hqlower
      (by simpa [Kraw, Boff, Z, J] using hqthreshold) hKstep
  obtain ⟨hν₁count, hν₁max⟩ :=
    near_balanced_atom_count_eq_and_supportMax_lt_of_geometric_lower
      hbpos hr1 hlower Q hD hDmax δ hν₁ (by simpa [s] using hν₁near)
      hlogCenter hDqN (by simpa [Z] using hNZ) hqlower
      (by simpa [Kraw, Boff, Z, J] using hqthreshold) hKstep
  have hν₀window := appearing_topDegree_support_window Q hD hν₀ hν₀count hDqN
    (by simpa [Z] using hNZ) (by simpa [Kraw, Boff, Nat.add_assoc] using hν₀max)
    (by simpa [Kraw, K, Z, J] using hqK)
  have hν₁window := appearing_topDegree_support_window Q hD hν₁ hν₁count hDqN
    (by simpa [Z] using hNZ) (by simpa [Kraw, Boff, Nat.add_assoc] using hν₁max)
    (by simpa [Kraw, K, Z, J] using hqK)
  have hlogBound : Real.log (P + 1) ≤ (C : ℝ) * Real.log ((q : ℝ) + 2) := by
    have := log_polynomial_mass_le_mul_log hA.le hlevel (hQlarge q hqlarge)
    simpa [P, C, A, E] using this
  have hdiff0 : 0 ≤ ν₁.sum (fun i k => (k : ℝ) * b i) -
      ν₀.sum (fun i k => (k : ℝ) * b i) := sub_nonneg.mpr (hmin ν₁ hν₁ hw₁)
  have hdiff : ν₁.sum (fun i k => (k : ℝ) * b i) -
        ν₀.sum (fun i k => (k : ℝ) * b i) <
      (C : ℝ) * Real.log ((q : ℝ) + 2) := by
    have : ν₁.sum (fun i k => (k : ℝ) * b i) -
        ν₀.sum (fun i k => (k : ℝ) * b i) < Real.log (P + 1) := by
      linarith [hgapP]
    exact this.trans_le hlogBound
  refine ⟨ν₀, ν₁, hne.symm, hν₀count, hν₁count, ?_, ?_, hdiff0, hdiff⟩
  · simpa [K] using hν₀window
  · simpa [K] using hν₁window

/-- Eventual uniform geometric growth, stated in the exact lower-step form used by the bend
argument. -/
def UniformGeometricGrowth (b : ℕ → ℝ) : Prop :=
  ∃ r : ℝ, ∃ N : ℕ, 1 < r ∧ ∀ n ≥ N, r * b n ≤ b (n + 1)

/-- Every nonzero fixed integer shift polynomial has superlogarithmic defect. -/
def LogarithmicallyShiftSeparated (b : ℕ → ℝ) : Prop :=
  ∀ Q : Polynomial ℤ, Q ≠ 0 →
    Tendsto (fun n =>
      |∑ j ∈ Finset.range (Q.natDegree + 1), (Q.coeff j : ℝ) * b (n + j)| /
        Real.log ((n : ℝ) + 2)) atTop atTop

def polynomialRealCoeffFinsupp (Q : Polynomial ℤ) : ℕ →₀ ℝ :=
  Q.toFinsupp.coeff.mapRange (fun z : ℤ => (z : ℝ)) (by simp)

@[simp]
theorem polynomialRealCoeffFinsupp_apply (Q : Polynomial ℤ) (n : ℕ) :
    polynomialRealCoeffFinsupp Q n = (Q.coeff n : ℝ) := by
  simp [polynomialRealCoeffFinsupp, Polynomial.toFinsupp_apply]

theorem stretchedFiniteDifference_polynomialRealCoeffFinsupp
    (Q : Polynomial ℤ) (α x : ℝ) :
    stretchedFiniteDifference α (polynomialRealCoeffFinsupp Q) x =
      ∑ j ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff j : ℝ) * stretchedExp α (x + j) := by
  rw [stretchedFiniteDifference, Finsupp.sum_of_support_subset
    (s := Finset.range (Q.natDegree + 1))]
  · apply Finset.sum_congr rfl
    intro j hj
    simp
  · intro j hj
    simp only [Finsupp.mem_support_iff, polynomialRealCoeffFinsupp_apply, ne_eq] at hj
    have hj' : Q.coeff j ≠ 0 := fun hz => hj (by simp [hz])
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Polynomial.le_natDegree_of_ne_zero hj'))
  · intro i hi
    simp

theorem stretchedMoment_polynomialRealCoeffFinsupp_eq_sum_range
    (Q : Polynomial ℤ) (k : ℕ) :
    stretchedMoment (polynomialRealCoeffFinsupp Q) k =
      ∑ j ∈ Finset.range (Q.natDegree + 1), (Q.coeff j : ℝ) * (j : ℝ) ^ k := by
  rw [stretchedMoment, Finsupp.sum_of_support_subset
    (s := Finset.range (Q.natDegree + 1))]
  · apply Finset.sum_congr rfl
    intro j hj
    simp
  · intro j hj
    simp only [Finsupp.mem_support_iff, polynomialRealCoeffFinsupp_apply, ne_eq] at hj
    have hj' : Q.coeff j ≠ 0 := fun hz => hj (by simp [hz])
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Polynomial.le_natDegree_of_ne_zero hj'))
  · intro i hi
    simp

/-- A nonzero polynomial coefficient stencil has a first nonvanishing power moment. -/
theorem exists_stretchedMoment_ne_of_polynomial {Q : Polynomial ℤ} (hQ : Q ≠ 0) :
    ∃ j ≤ Q.natDegree, stretchedMoment (polynomialRealCoeffFinsupp Q) j ≠ 0 := by
  classical
  by_contra hno
  push Not at hno
  let M := Q.natDegree + 1
  let v : Fin M → ℝ := fun j => polynomialRealCoeffFinsupp Q j
  let x : Fin M → ℝ := fun j => (j : ℕ)
  have hx : Function.Injective x := by
    intro i j hij
    apply Fin.ext
    dsimp [x] at hij
    exact_mod_cast hij
  have hvzero : v = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hx
    intro i
    have hm := hno (i : ℕ) (by dsimp [M] at i; omega)
    rw [stretchedMoment_polynomialRealCoeffFinsupp_eq_sum_range,
      ← Fin.sum_univ_eq_sum_range
        (fun j => (Q.coeff j : ℝ) * (j : ℝ) ^ (i : ℕ)) M] at hm
    simpa [v, x, M] using hm
  apply hQ
  ext n
  by_cases hn : n < M
  · have hz := congrFun hvzero (⟨n, hn⟩ : Fin M)
    simpa [v] using hz
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by dsimp [M] at hn; omega)

/-- **Uniform-geometric DA resonance law, relation form.**  Every positive-degree
integer-normalized relation under a geometric lower step forces one fixed nonzero integer shift
polynomial with root `1` and logarithmic defect along an unbounded subsequence. -/
theorem exists_uniformGeometric_resonancePolynomial_of_positiveJetDegree_relation
    {b : ℕ → ℝ} (hbpos : ∀ i, 0 < b i)
    {r : ℝ} (hr1 : 1 < r) {Nlower : ℕ}
    (hlower : ∀ m ≥ Nlower, r * b m ≤ b (m + 1))
    {n : ℕ} (F : PowerSeries ℂ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ = Real.exp (-b i))
    (R : MvPolynomial (Fin (n + 2)) ℂ)
    (hRint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m R = (z : ℂ))
    (hrel : aeval (formalJets n F) R = 0)
    (hDpos : 0 < magnitudeMaxJetDegree n R) :
    ∃ Q : Polynomial ℤ, ∃ C K : ℕ, ∃ q : ℕ → ℕ,
      Q ≠ 0 ∧ Q.eval 1 = 0 ∧ Tendsto q atTop atTop ∧ ∀ k,
        0 ≤ ∑ j ∈ Finset.range (Q.natDegree + 1),
          (Q.coeff j : ℝ) * b (q k + j) ∧
        (∑ j ∈ Finset.range (Q.natDegree + 1),
          (Q.coeff j : ℝ) * b (q k + j)) <
          (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) := by
  classical
  obtain ⟨D, K, C, Q₀, hD, hC, hpairs⟩ :=
    exists_eventually_uniformGeometric_bend_pair_of_positiveJetDegree
      hbpos hr1 hlower F hb R hRint hrel hDpos
  obtain ⟨p₀, p₁, hpne, hsum₀, hsum₁, q, hq, hdefect⟩ :=
    exists_persistent_atomWindow_resonance hpairs
  let Q : Polynomial ℤ := atomPatternDifferencePolynomial p₀ p₁
  have hQ : Q ≠ 0 := atomPatternDifferencePolynomial_ne_zero hpne
  have hQone : Q.eval 1 = 0 :=
    atomPatternDifferencePolynomial_eval_one p₀ p₁ (hsum₀.trans hsum₁.symm)
  refine ⟨Q, C, K, q, hQ, hQone, hq, fun k => ?_⟩
  have hsum := sum_range_atomPatternDifferencePolynomial (M := 2 * K + 1)
    (by omega) p₀ p₁ b (q k)
  constructor
  · rw [hsum]
    exact (hdefect k).1
  · rw [hsum]
    exact (hdefect k).2

/-- The logarithmic cost of a fixed translated window is eventually at most twice the base
logarithm. -/
theorem log_nat_add_shift_le_two_mul_log {n K : ℕ} (hKn : K ≤ n) :
    Real.log (((n + K : ℕ) : ℝ) + 2) ≤ 2 * Real.log ((n : ℝ) + 2) := by
  have hbase : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have htwo : (0 : ℝ) < 2 := by norm_num
  have harg : (((n + K : ℕ) : ℝ) + 2) ≤ 2 * ((n : ℝ) + 2) := by
    have hargNat : n + K + 2 ≤ 2 * (n + 2) := by omega
    exact_mod_cast hargNat
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < ((n + K : ℕ) : ℝ) + 2) harg
  rw [Real.log_mul htwo.ne' hbase.ne'] at hlog
  have hlogtwo : Real.log 2 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log htwo (by norm_num)
  linarith

/-- Analytic DA form of the uniform-geometric resonance law. -/
theorem exists_uniformGeometric_resonancePolynomial_of_differentiallyAlgebraic
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℝ} (hbpos : ∀ i, 0 < b i)
    (hb : ∀ i, ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    (hgrowth : UniformGeometricGrowth b)
    (hDA : DifferentiallyAlgebraic f) :
    ∃ Q : Polynomial ℤ, ∃ C K : ℕ, ∃ q : ℕ → ℕ,
      Q ≠ 0 ∧ Q.eval 1 = 0 ∧ Tendsto q atTop atTop ∧ ∀ k,
        0 ≤ ∑ j ∈ Finset.range (Q.natDegree + 1),
          (Q.coeff j : ℝ) * b (q k + j) ∧
        (∑ j ∈ Finset.range (Q.natDegree + 1),
          (Q.coeff j : ℝ) * b (q k + j)) <
          (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) := by
  obtain ⟨r, Nlower, hr1, hlower⟩ := hgrowth
  obtain ⟨n, P, hP, hPfun⟩ := hDA
  have hjz : jetFun f n P = 0 := by
    funext z
    exact hPfun z
  have hformal : aeval (formalJets n (taylorPS f)) P = 0 := by
    rw [← taylorPS_jetFun f n hf P, hjz,
      show (0 : ℂ → ℂ) = fun _ => (0 : ℂ) from rfl, taylorPS_const, map_zero]
  obtain ⟨n', R, hR, hRint, hrel⟩ := formal_mahler_integer_normalization hP hformal
  have hDpos := magnitudeMaxJetDegree_pos_of_integer_relation
    (taylorPS f) hb R hR hRint hrel
  exact exists_uniformGeometric_resonancePolynomial_of_positiveJetDegree_relation
    hbpos hr1 hlower (taylorPS f) hb R hRint hrel hDpos

/-- **Uniform-geometric shift-separation master theorem.**  If every fixed integer shift defect is
superlogarithmic, no algebraic differential relation can survive an eventual geometric lower
step. -/
theorem hypertranscendental_of_uniformGeometric_logarithmicallyShiftSeparated
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℝ} (hbpos : ∀ i, 0 < b i)
    (hb : ∀ i, ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    (hgrowth : UniformGeometricGrowth b)
    (hsep : LogarithmicallyShiftSeparated b) :
    Hypertranscendental f := by
  intro hDA
  obtain ⟨Q, C, K, q, hQ, _hQone, hq, hdefect⟩ :=
    exists_uniformGeometric_resonancePolynomial_of_differentiallyAlgebraic
      hf hbpos hb hgrowth hDA
  have hsepq := (hsep Q hQ).comp hq
  have hlarge := hsepq.eventually_gt_atTop ((2 : ℝ) * C + 1)
  obtain ⟨k, hk, hqK⟩ := (hlarge.and (hq.eventually_ge_atTop K)).exists
  let S : ℝ := ∑ j ∈ Finset.range (Q.natDegree + 1),
    (Q.coeff j : ℝ) * b (q k + j)
  have hS0 : 0 ≤ S := (hdefect k).1
  have hSupper : S < (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) :=
    (hdefect k).2
  have hlogBound := log_nat_add_shift_le_two_mul_log hqK
  have hlogPos : 0 < Real.log ((q k : ℝ) + 2) := Real.log_pos (by
    have : (0 : ℝ) ≤ q k := by positivity
    linarith)
  have hratioUpper : |S| / Real.log ((q k : ℝ) + 2) < (2 : ℝ) * C := by
    rw [abs_of_nonneg hS0]
    rw [div_lt_iff₀ hlogPos]
    calc
      S < (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) := hSupper
      _ ≤ (C : ℝ) * (2 * Real.log ((q k : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hlogBound (by positivity)
      _ = (2 : ℝ) * C * Real.log ((q k : ℝ) + 2) := by ring
  change (2 : ℝ) * C + 1 < |S| / Real.log ((q k : ℝ) + 2) at hk
  linarith

theorem UniformGeometricGrowth.of_eventuallyEq {b b' : ℕ → ℝ}
    (hgrowth : UniformGeometricGrowth b) (heq : b' =ᶠ[atTop] b) :
    UniformGeometricGrowth b' := by
  obtain ⟨r, N, hr1, hlower⟩ := hgrowth
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp heq
  refine ⟨r, max N T, hr1, fun n hn => ?_⟩
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnT : T ≤ n := (le_max_right _ _).trans hn
  rw [hT n hnT, hT (n + 1) (hnT.trans (Nat.le_add_right n 1))]
  exact hlower n hnN

theorem LogarithmicallyShiftSeparated.of_eventuallyEq {b b' : ℕ → ℝ}
    (hsep : LogarithmicallyShiftSeparated b) (heq : b' =ᶠ[atTop] b) :
    LogarithmicallyShiftSeparated b' := by
  intro Q hQ
  refine (hsep Q hQ).congr' ?_
  have hall : ∀ᶠ n : ℕ in atTop,
      ∀ j ∈ Finset.range (Q.natDegree + 1), b' (n + j) = b (n + j) := by
    rw [Finset.eventually_all]
    intro j hj
    simpa only [Function.comp_apply] using! heq.comp_tendsto (tendsto_add_atTop_nat j)
  filter_upwards [hall] with n hn
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  rw [hn j hj]

/-- Eventual full support and positivity suffice for the uniform-geometric shift-separation master
theorem; a finite Taylor correction supplies the all-index hypotheses. -/
theorem hypertranscendental_of_eventually_uniformGeometric_logarithmicallyShiftSeparated
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℝ}
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    (hbpos : ∀ᶠ i in atTop, 0 < b i)
    (hgrowth : UniformGeometricGrowth b)
    (hsep : LogarithmicallyShiftSeparated b) :
    Hypertranscendental f := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hb.and hbpos)
  let F := taylorPS f
  let p := finiteTaylorCorrection F T
  let g : ℂ → ℂ := fun z => f z + p.eval z
  let b' : ℕ → ℝ := fun i => if i < T then 1 else b i
  have hp : ContDiff ℂ (⊤ : ℕ∞) (fun z : ℂ => p.eval z) :=
    contDiff_polynomial_eval p
  have hgsm : ContDiff ℂ (⊤ : ℕ∞) g := hf.add hp
  have htaylor : taylorPS g = F + (p : PowerSeries ℂ) := by
    change taylorPS (fun z => f z + p.eval z) = _
    rw [show (fun z => f z + p.eval z) = f + (fun z => p.eval z) from rfl,
      taylorPS_add hf hp, taylorPS_polynomial_eval]
  have hb' : ∀ i, ‖PowerSeries.coeff i (taylorPS g)‖ = Real.exp (-b' i) := by
    intro i
    rw [htaylor, map_add, Polynomial.coeff_coe, coeff_finiteTaylorCorrection]
    by_cases hi : i < T
    · simp [b', hi, Complex.norm_exp]
    · have hiT : T ≤ i := Nat.le_of_not_gt hi
      simp only [if_neg hi, add_zero]
      rw [show b' i = b i by simp [b', hi]]
      change ‖PowerSeries.coeff i F‖ = Real.exp (-b i)
      simpa only [F] using (hT i hiT).1
  have hb'pos : ∀ i, 0 < b' i := by
    intro i
    by_cases hi : i < T
    · simp [b', hi]
    · simpa [b', hi] using (hT i (Nat.le_of_not_gt hi)).2
  have heq : b' =ᶠ[atTop] b := by
    filter_upwards [eventually_ge_atTop T] with i hi
    simp [b', Nat.not_lt.mpr hi]
  have hgrowth' : UniformGeometricGrowth b' := hgrowth.of_eventuallyEq heq
  have hsep' : LogarithmicallyShiftSeparated b' := hsep.of_eventuallyEq heq
  have hg : Hypertranscendental g :=
    hypertranscendental_of_uniformGeometric_logarithmicallyShiftSeparated
      hgsm hb'pos hb' hgrowth' hsep'
  exact (hypertranscendental_add_polynomial_iff hf p).mp hg

/-- Eventual full-support DA resonance law.  After discarding finitely many terms of the produced
subsequence, the fixed polynomial defect is nonnegative and logarithmic for the original profile. -/
theorem exists_eventually_uniformGeometric_resonancePolynomial_of_differentiallyAlgebraic
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℝ}
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    (hbpos : ∀ᶠ i in atTop, 0 < b i)
    (hgrowth : UniformGeometricGrowth b)
    (hDA : DifferentiallyAlgebraic f) :
    ∃ Q : Polynomial ℤ, ∃ C K : ℕ, ∃ q : ℕ → ℕ,
      Q ≠ 0 ∧ Q.eval 1 = 0 ∧ Tendsto q atTop atTop ∧
      ∀ᶠ k in atTop,
        0 ≤ ∑ j ∈ Finset.range (Q.natDegree + 1),
          (Q.coeff j : ℝ) * b (q k + j) ∧
        (∑ j ∈ Finset.range (Q.natDegree + 1),
          (Q.coeff j : ℝ) * b (q k + j)) <
          (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hb.and hbpos)
  let F := taylorPS f
  let p := finiteTaylorCorrection F T
  let g : ℂ → ℂ := fun z => f z + p.eval z
  let b' : ℕ → ℝ := fun i => if i < T then 1 else b i
  have hp : ContDiff ℂ (⊤ : ℕ∞) (fun z : ℂ => p.eval z) :=
    contDiff_polynomial_eval p
  have hgsm : ContDiff ℂ (⊤ : ℕ∞) g := hf.add hp
  have htaylor : taylorPS g = F + (p : PowerSeries ℂ) := by
    change taylorPS (fun z => f z + p.eval z) = _
    rw [show (fun z => f z + p.eval z) = f + (fun z => p.eval z) from rfl,
      taylorPS_add hf hp, taylorPS_polynomial_eval]
  have hb' : ∀ i, ‖PowerSeries.coeff i (taylorPS g)‖ = Real.exp (-b' i) := by
    intro i
    rw [htaylor, map_add, Polynomial.coeff_coe, coeff_finiteTaylorCorrection]
    by_cases hi : i < T
    · simp [b', hi, Complex.norm_exp]
    · have hiT : T ≤ i := Nat.le_of_not_gt hi
      simp only [if_neg hi, add_zero]
      rw [show b' i = b i by simp [b', hi]]
      change ‖PowerSeries.coeff i F‖ = Real.exp (-b i)
      simpa only [F] using (hT i hiT).1
  have hb'pos : ∀ i, 0 < b' i := by
    intro i
    by_cases hi : i < T
    · simp [b', hi]
    · simpa [b', hi] using (hT i (Nat.le_of_not_gt hi)).2
  have heq : b' =ᶠ[atTop] b := by
    filter_upwards [eventually_ge_atTop T] with i hi
    simp [b', Nat.not_lt.mpr hi]
  have hgrowth' : UniformGeometricGrowth b' := hgrowth.of_eventuallyEq heq
  have hgDA : DifferentiallyAlgebraic g :=
    DifferentiallyAlgebraic.add_polynomial hDA hf p
  obtain ⟨Q, C, K, q, hQ, hQone, hq, hdefect⟩ :=
    exists_uniformGeometric_resonancePolynomial_of_differentiallyAlgebraic
      hgsm hb'pos hb' hgrowth' hgDA
  refine ⟨Q, C, K, q, hQ, hQone, hq, ?_⟩
  have hall : ∀ᶠ k : ℕ in atTop,
      ∀ j ∈ Finset.range (Q.natDegree + 1), b' (q k + j) = b (q k + j) := by
    rw [Finset.eventually_all]
    intro j hj
    simpa only [Function.comp_apply] using!
      heq.comp_tendsto ((tendsto_add_atTop_nat j).comp hq)
  filter_upwards [hall] with k hk
  have hsum : (∑ j ∈ Finset.range (Q.natDegree + 1),
      (Q.coeff j : ℝ) * b' (q k + j)) =
      ∑ j ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff j : ℝ) * b (q k + j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hk j hj]
  rw [← hsum]
  exact hdefect k

lemma eventually_log_nat_add_two_le_two_mul_log_nat :
    ∀ᶠ n : ℕ in atTop,
      Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hquad : (n : ℝ) + 2 ≤ n ^ 2 := by nlinarith
  calc
    Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) ^ 2) :=
      Real.log_le_log (by positivity) hquad
    _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num

/-- The fixed forward-shift defect attached to an integer polynomial. -/
def integerPolynomialShift (Q : Polynomial ℤ) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (Q.natDegree + 1), (Q.coeff r : ℝ) * b (n + r)

/-- Evaluation of an integer polynomial after casting its coefficients to `ℝ`. -/
def integerPolynomialRealEval (Q : Polynomial ℤ) (lam : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (Q.natDegree + 1), (Q.coeff r : ℝ) * lam ^ r

lemma integerPolynomialShift_geometric (Q : Polynomial ℤ) (lam : ℝ) (n : ℕ) :
    integerPolynomialShift Q (fun k => lam ^ k) n =
      lam ^ n * integerPolynomialRealEval Q lam := by
  rw [integerPolynomialShift, integerPolynomialRealEval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [pow_add]
  ring

lemma integerPolynomialShift_add (Q : Polynomial ℤ) (b h : ℕ → ℝ) (n : ℕ) :
    integerPolynomialShift Q (fun k => b k + h k) n =
      integerPolynomialShift Q b n + integerPolynomialShift Q h n := by
  simp only [integerPolynomialShift, mul_add, Finset.sum_add_distrib]

lemma integerPolynomialShift_const_mul (Q : Polynomial ℤ) (A : ℝ)
    (b : ℕ → ℝ) (n : ℕ) :
    integerPolynomialShift Q (fun k => A * b k) n =
      A * integerPolynomialShift Q b n := by
  simp only [integerPolynomialShift, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

lemma integerPolynomialShift_C_mul (c : ℤ) (Q : Polynomial ℤ)
    (b : ℕ → ℝ) (n : ℕ) :
    integerPolynomialShift (Polynomial.C c * Q) b n =
      (c : ℝ) * integerPolynomialShift Q b n := by
  rw [integerPolynomialShift, integerPolynomialShift]
  by_cases hc : c = 0
  · simp [hc]
  have hdeg : (Polynomial.C c * Q).natDegree = Q.natDegree :=
    Polynomial.natDegree_C_mul hc
  rw [hdeg, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Polynomial.coeff_C_mul]
  push_cast
  ring

lemma integerPolynomialShift_isLittleO_const_pow
    {h : ℕ → ℝ} {lam : ℝ} (hlam0 : 0 < lam)
    (hh : h =o[atTop] fun n : ℕ => lam ^ n) (Q : Polynomial ℤ) :
    (fun n => integerPolynomialShift Q h n) =o[atTop]
      fun n : ℕ => lam ^ n := by
  change (fun n => ∑ r ∈ Finset.range (Q.natDegree + 1),
    (Q.coeff r : ℝ) * h (n + r)) =o[atTop] fun n : ℕ => lam ^ n
  apply Asymptotics.IsLittleO.sum
  intro r hr
  have hs := hh.comp_tendsto (tendsto_add_atTop_nat r)
  have hs' : (fun n : ℕ => h (n + r)) =o[atTop]
      (fun n : ℕ => lam ^ r * lam ^ n) := by
    refine hs.congr' (Filter.Eventually.of_forall fun _ => rfl)
      (Filter.Eventually.of_forall fun n => ?_)
    simp only [Function.comp_apply, pow_add]
    ring
  have hs'' : (fun n : ℕ => h (n + r)) =o[atTop]
      (fun n : ℕ => lam ^ n) :=
    (Asymptotics.isLittleO_const_mul_right_iff
      (pow_ne_zero r hlam0.ne')).mp hs'
  exact hs''.const_mul_left (Q.coeff r : ℝ)

lemma eventually_pos_hierarchical
    {h : ℕ → ℝ} {lam A : ℝ} (hlam1 : 1 < lam) (hA : 0 < A)
    (hh : h =o[atTop] fun n : ℕ => lam ^ n) :
    ∀ᶠ n : ℕ in atTop, 0 < A * lam ^ n + h n := by
  have hbound := hh.bound (half_pos hA)
  filter_upwards [hbound] with n hn
  have hlamn : 0 < lam ^ n := pow_pos (zero_lt_one.trans hlam1) n
  simp only [Real.norm_eq_abs, abs_of_pos hlamn] at hn
  have hlow := (abs_le.mp hn).1
  linarith [mul_pos hA hlamn]

/-- A geometric leading scale is uniformly geometric after any little-`o` perturbation. -/
theorem uniformGeometricGrowth_hierarchical
    {h : ℕ → ℝ} {lam A : ℝ} (hlam1 : 1 < lam) (hA : 0 < A)
    (hh : h =o[atTop] fun n : ℕ => lam ^ n) :
    UniformGeometricGrowth (fun n => A * lam ^ n + h n) := by
  let r : ℝ := (lam + 1) / 2
  have hr1 : 1 < r := by dsimp [r]; linarith
  have hrlam : r < lam := by dsimp [r]; linarith
  have hlam0 : 0 < lam := zero_lt_one.trans hlam1
  have hr0 : 0 < r := zero_lt_one.trans hr1
  let eps : ℝ := A * (lam - r) / (2 * (lam + r))
  have hden : 0 < 2 * (lam + r) := by positivity
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  have hepsA : eps < A := by
    have hratio : lam - r < 2 * (lam + r) := by linarith
    dsimp [eps]
    rw [div_lt_iff₀ hden]
    nlinarith
  have hscale : r * (A + eps) < lam * (A - eps) := by
    have hid : lam * (A - eps) - r * (A + eps) = A * (lam - r) / 2 := by
      dsimp [eps]
      field_simp [ne_of_gt hden]
      ring
    have : 0 < A * (lam - r) / 2 := by positivity
    linarith
  have hbound := hh.bound heps
  have hboundNext := (tendsto_add_atTop_nat 1).eventually hbound
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hbound.and hboundNext)
  refine ⟨r, N, hr1, ?_⟩
  intro n hn
  obtain ⟨hhn, hhnext⟩ := hN n hn
  have hlamn : 0 < lam ^ n := pow_pos hlam0 n
  have hlamnext : 0 < lam ^ (n + 1) := pow_pos hlam0 (n + 1)
  simp only [Real.norm_eq_abs, abs_of_pos hlamn] at hhn
  simp only [Real.norm_eq_abs, abs_of_pos hlamnext] at hhnext
  have hhnUpper := (abs_le.mp hhn).2
  have hhnextLower := (abs_le.mp hhnext).1
  rw [pow_succ] at hhnextLower
  change r * (A * lam ^ n + h n) ≤ A * lam ^ (n + 1) + h (n + 1)
  rw [pow_succ]
  have hleft : r * (A * lam ^ n + h n) ≤ r * (A + eps) * lam ^ n := by
    nlinarith
  have hright : lam * (A - eps) * lam ^ n ≤
      A * (lam ^ n * lam) + h (n + 1) := by
    nlinarith
  exact hleft.trans ((mul_lt_mul_of_pos_right hscale hlamn).le.trans hright)

lemma log_nat_add_two_isLittleO_const_pow {lam : ℝ} (hlam1 : 1 < lam) :
    (fun n : ℕ => Real.log ((n : ℝ) + 2)) =o[atTop]
      fun n : ℕ => lam ^ n := by
  have hlin : (fun n : ℕ => (n : ℝ)) =o[atTop] fun n : ℕ => lam ^ n := by
    simpa using (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 1 hlam1)
  have hconst : (fun _ : ℕ => (2 : ℝ)) =o[atTop] fun n : ℕ => lam ^ n := by
    have h := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 0 hlam1).const_mul_left 2
    simpa using h
  have hadd : (fun n : ℕ => (n : ℝ) + 2) =o[atTop]
      fun n : ℕ => lam ^ n := hlin.add hconst
  have hlog : (fun n : ℕ => Real.log ((n : ℝ) + 2)) =O[atTop]
      fun n : ℕ => (n : ℝ) + 2 := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with n
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have harg1 : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith
    have harg0 : (0 : ℝ) < (n : ℝ) + 2 := by linarith
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg harg1),
      Real.norm_eq_abs, abs_of_pos harg0, one_mul]
    exact Real.log_le_self (by positivity)
  exact hlog.trans_isLittleO hadd

/-- A perturbation breaks every exact integer resonance of the leading geometric scale. -/
def LogarithmicallyResonanceBreakingAt
    (lam : ℝ) (h : ℕ → ℝ) : Prop :=
  h =o[atTop] (fun n : ℕ => lam ^ n) ∧
    ∀ Q : Polynomial ℤ, Q ≠ 0 → integerPolynomialRealEval Q lam = 0 →
      Tendsto (fun n =>
        |integerPolynomialShift Q h n| / Real.log ((n : ℝ) + 2))
        atTop atTop

lemma isLittleO_sub_geometric_of_ratio_tendsto
    {b : ℕ → ℝ} {lam A : ℝ} (hlam1 : 1 < lam) (hA : 0 < A)
    (hEG : Tendsto (fun n => b n / (A * lam ^ n)) atTop (𝓝 1)) :
    (fun n => b n - A * lam ^ n) =o[atTop]
      fun n : ℕ => lam ^ n := by
  refine (Asymptotics.isLittleO_iff_tendsto' ?_).2 ?_
  · filter_upwards with n
    intro hzero
    exact (pow_ne_zero n (zero_lt_one.trans hlam1).ne' hzero).elim
  · have ht : Tendsto (fun n => A * (b n / (A * lam ^ n) - 1))
        atTop (𝓝 0) := by
      convert (hEG.sub tendsto_const_nhds).const_mul A using 1
      ring
    refine ht.congr' ?_
    filter_upwards with n
    have hlamn : lam ^ n ≠ 0 := pow_ne_zero n (zero_lt_one.trans hlam1).ne'
    field_simp [hA.ne', hlamn]

/-- Integer minimal-polynomial interface at a real algebraic ratio.  The last clause is Gauss
divisibility with denominators cleared: every integer relation at `lam` is a nonzero integer
multiple of this canonical relation. -/
def IsIntegerMinimalPolynomialAt
    (m : Polynomial ℤ) (lam : ℝ) : Prop :=
  m ≠ 0 ∧ integerPolynomialRealEval m lam = 0 ∧
    ∀ Q : Polynomial ℤ, Q ≠ 0 → integerPolynomialRealEval Q lam = 0 →
      ∃ c : ℤ, c ≠ 0 ∧ ∃ R : Polynomial ℤ, R ≠ 0 ∧
        Polynomial.C c * Q = m * R

/-- Separation of every polynomial shift of the canonical lower-scale residue `m(S)b`.  The
product `m * R` is the polynomial calculus identity `R(S)(m(S)b) = (mR)(S)b`. -/
def CanonicalResidueShiftSeparated
    (m : Polynomial ℤ) (b : ℕ → ℝ) : Prop :=
  ∀ R : Polynomial ℤ, R ≠ 0 →
    Tendsto (fun n =>
      |integerPolynomialShift (m * R) b n| / Real.log ((n : ℝ) + 2))
      atTop atTop

lemma integerPolynomialRealEval_eq_eval₂ (Q : Polynomial ℤ) (lam : ℝ) :
    integerPolynomialRealEval Q lam =
      Polynomial.eval₂ (algebraMap ℤ ℝ) lam Q := by
  rw [Polynomial.eval₂_eq_sum_range]
  rfl

/-- A canonical integer normalization of the rational minimal polynomial. -/
noncomputable def rationalMinpolyIntegerNormalization (lam : ℝ) : Polynomial ℤ :=
  IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ lam)

lemma rationalMinpolyIntegerNormalization_ne_zero
    {lam : ℝ} (hlam : IsAlgebraic ℚ lam) :
    rationalMinpolyIntegerNormalization lam ≠ 0 := by
  intro hzero
  have hminzero : minpoly ℚ lam = 0 :=
    IsFractionRing.integerNormalization_eq_zero_iff.mp
      (by simpa only [rationalMinpolyIntegerNormalization] using hzero)
  exact (minpoly.ne_zero hlam.isIntegral) hminzero

lemma rationalMinpolyIntegerNormalization_eval_eq_zero
    (lam : ℝ) :
    integerPolynomialRealEval (rationalMinpolyIntegerNormalization lam) lam = 0 := by
  rw [integerPolynomialRealEval_eq_eval₂]
  change (Polynomial.aeval lam) (rationalMinpolyIntegerNormalization lam) = 0
  exact IsLocalization.integerNormalization_aeval_eq_zero
    (nonZeroDivisors ℤ) (minpoly ℚ lam) (minpoly.aeval ℚ lam)

lemma aeval_map_int_rat_eq_zero_of_integerPolynomialRealEval_eq_zero
    {Q : Polynomial ℤ} {lam : ℝ}
    (hQ : integerPolynomialRealEval Q lam = 0) :
    (Polynomial.aeval lam) (Q.map (algebraMap ℤ ℚ)) = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  rw [← IsScalarTower.algebraMap_eq ℤ ℚ ℝ]
  simpa only [integerPolynomialRealEval_eq_eval₂] using hQ

theorem isIntegerMinimalPolynomialAt_rationalMinpolyIntegerNormalization
    {lam : ℝ} (hlam : IsAlgebraic ℚ lam) :
    IsIntegerMinimalPolynomialAt
      (rationalMinpolyIntegerNormalization lam) lam := by
  refine ⟨rationalMinpolyIntegerNormalization_ne_zero hlam,
    rationalMinpolyIntegerNormalization_eval_eq_zero lam, ?_⟩
  intro Q hQ hQeval
  have hQrat :=
    aeval_map_int_rat_eq_zero_of_integerPolynomialRealEval_eq_zero hQeval
  obtain ⟨U, hU⟩ := minpoly.dvd ℚ lam hQrat
  have hmapQ : Q.map (algebraMap ℤ ℚ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (Int.cast_injective :
      Function.Injective (algebraMap ℤ ℚ))).2 hQ
  have hU0 : U ≠ 0 := by
    intro hzero
    apply hmapQ
    rw [hU, hzero, mul_zero]
  let m := rationalMinpolyIntegerNormalization lam
  let R := IsLocalization.integerNormalization (nonZeroDivisors ℤ) U
  obtain ⟨a, haM, hma⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (minpoly ℚ lam)
  obtain ⟨d, hdM, hdR⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) U
  have ha : a ≠ 0 := nonZeroDivisors.ne_zero haM
  have hd : d ≠ 0 := nonZeroDivisors.ne_zero hdM
  have hR : R ≠ 0 := by
    intro hzero
    apply hU0
    exact IsFractionRing.integerNormalization_eq_zero_iff.mp
      (by simpa only [R] using hzero)
  have hma' : m.map (algebraMap ℤ ℚ) =
      Polynomial.C (a : ℚ) * minpoly ℚ lam := by
    simpa only [m, rationalMinpolyIntegerNormalization, Algebra.smul_def,
      map_intCast, Polynomial.algebraMap_apply] using! hma
  have hdR' : R.map (algebraMap ℤ ℚ) =
      Polynomial.C (d : ℚ) * U := by
    simpa only [R, Algebra.smul_def, map_intCast,
      Polynomial.algebraMap_apply] using! hdR
  refine ⟨a * d, mul_ne_zero ha hd, R, hR, ?_⟩
  apply Polynomial.map_injective (algebraMap ℤ ℚ) Int.cast_injective
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_mul]
  rw [hU, hma', hdR']
  push_cast
  rw [Polynomial.C_mul]
  simp only [mul_assoc, mul_left_comm, mul_comm]
  rfl

/-- The primitive integer minimal polynomial obtained from the rational minpoly. -/
noncomputable def primitiveRationalMinpolyInteger (lam : ℝ) : Polynomial ℤ :=
  (rationalMinpolyIntegerNormalization lam).primPart

theorem primitiveRationalMinpolyInteger_isPrimitive (lam : ℝ) :
    (primitiveRationalMinpolyInteger lam).IsPrimitive :=
  Polynomial.isPrimitive_primPart _

theorem isIntegerMinimalPolynomialAt_primitiveRationalMinpolyInteger
    {lam : ℝ} (hlam : IsAlgebraic ℚ lam) :
    IsIntegerMinimalPolynomialAt (primitiveRationalMinpolyInteger lam) lam := by
  let p := rationalMinpolyIntegerNormalization lam
  have hp := isIntegerMinimalPolynomialAt_rationalMinpolyIntegerNormalization hlam
  have hp0 : p ≠ 0 := by simpa only [p] using hp.1
  have hc : p.content ≠ 0 := by
    exact (Polynomial.content_eq_zero_iff.not.mpr hp0)
  have hfactor : p = Polynomial.C p.content * p.primPart :=
    p.eq_C_content_mul_primPart
  refine ⟨by
      simpa only [primitiveRationalMinpolyInteger, p] using p.primPart_ne_zero,
    ?_, ?_⟩
  · have heval : (Polynomial.aeval lam) p = 0 := by
      simpa only [Polynomial.aeval_def, ← integerPolynomialRealEval_eq_eval₂] using hp.2.1
    rw [hfactor, map_mul, Polynomial.aeval_C] at heval
    have hccast : (p.content : ℝ) ≠ 0 := by exact_mod_cast hc
    have hprimEval : (Polynomial.aeval lam) p.primPart = 0 :=
      (mul_eq_zero.mp heval).resolve_left hccast
    simpa only [primitiveRationalMinpolyInteger, p,
      Polynomial.aeval_def, ← integerPolynomialRealEval_eq_eval₂] using hprimEval
  · intro Q hQ hQeval
    obtain ⟨c, hc0, R, hR, hQR⟩ := hp.2.2 Q hQ hQeval
    refine ⟨c, hc0, Polynomial.C p.content * R,
      mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hR, ?_⟩
    calc
      Polynomial.C c * Q = p * R := by simpa only [p] using hQR
      _ = (Polynomial.C p.content * p.primPart) * R :=
        congrArg (fun z : Polynomial ℤ => z * R) hfactor
      _ = p.primPart * (Polynomial.C p.content * R) := by
        simp only [mul_left_comm, mul_comm]
      _ = primitiveRationalMinpolyInteger lam *
          (Polynomial.C p.content * R) := by rfl

/-- The hierarchy principle: a little-`o` perturbation only has to break the integer relations
which survive the leading geometric scale. -/
theorem logarithmicallyShiftSeparated_hierarchical
    {h : ℕ → ℝ} {lam A : ℝ} (hlam1 : 1 < lam) (hA : 0 < A)
    (hRB : LogarithmicallyResonanceBreakingAt lam h) :
    LogarithmicallyShiftSeparated (fun n => A * lam ^ n + h n) := by
  rcases hRB with ⟨hh, hres⟩
  intro Q hQ
  change Tendsto (fun n =>
    |integerPolynomialShift Q (fun k => A * lam ^ k + h k) n| /
      Real.log ((n : ℝ) + 2)) atTop atTop
  by_cases heval : integerPolynomialRealEval Q lam = 0
  · have heq : ∀ n,
        integerPolynomialShift Q (fun k => A * lam ^ k + h k) n =
          integerPolynomialShift Q h n := by
      intro n
      rw [integerPolynomialShift_add, integerPolynomialShift_const_mul,
        integerPolynomialShift_geometric, heval]
      ring
    simpa only [heq] using hres Q hQ heval
  · rw [Filter.tendsto_atTop]
    intro X
    let c : ℝ := A * integerPolynomialRealEval Q lam
    have hc : c ≠ 0 := mul_ne_zero hA.ne' heval
    have hcabs : 0 < |c| := abs_pos.mpr hc
    have herr := integerPolynomialShift_isLittleO_const_pow
      (zero_lt_one.trans hlam1) hh Q
    have herrBound := herr.bound (half_pos hcabs)
    have hlog := log_nat_add_two_isLittleO_const_pow hlam1
    let δ : ℝ := |c| / (2 * (|X| + 1))
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    have hlogBound := hlog.bound hδ
    filter_upwards [herrBound, hlogBound] with n hnerr hnlog
    have hlamn : 0 < lam ^ n := pow_pos (zero_lt_one.trans hlam1) n
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hlogpos : 0 < Real.log ((n : ℝ) + 2) :=
      Real.log_pos (by linarith)
    simp only [Real.norm_eq_abs, abs_of_pos hlamn] at hnerr
    simp only [Real.norm_eq_abs, abs_of_pos hlamn,
      abs_of_pos hlogpos] at hnlog
    have hshift :
        integerPolynomialShift Q (fun k => A * lam ^ k + h k) n =
          c * lam ^ n + integerPolynomialShift Q h n := by
      rw [integerPolynomialShift_add, integerPolynomialShift_const_mul,
        integerPolynomialShift_geometric]
      dsimp [c]
      ring
    rw [hshift]
    have hnonneg : 0 ≤
        |c * lam ^ n + integerPolynomialShift Q h n| /
          Real.log ((n : ℝ) + 2) := by positivity
    by_cases hX : X ≤ 0
    · exact hX.trans hnonneg
    have hrev : |c| * lam ^ n - |integerPolynomialShift Q h n| ≤
        |c * lam ^ n + integerPolynomialShift Q h n| := by
      have h := abs_sub_abs_le_abs_sub
        (c * lam ^ n) (-integerPolynomialShift Q h n)
      rw [abs_mul, abs_of_pos hlamn, abs_neg, sub_neg_eq_add] at h
      exact h
    have hlower : |c| / 2 * lam ^ n ≤
        |c * lam ^ n + integerPolynomialShift Q h n| := by
      linarith
    have hXabs : |X| = X := abs_of_pos (lt_of_not_ge hX)
    have hden : 0 < 2 * (|X| + 1) := by positivity
    have hcoef : X * δ < |c| / 2 := by
      dsimp [δ]
      rw [hXabs]
      have hdenX : 0 < 2 * (X + 1) := by linarith
      calc
        X * (|c| / (2 * (X + 1))) =
            (X * |c|) / (2 * (X + 1)) := by ring
        _ < |c| / 2 := (div_lt_iff₀ hdenX).2 (by nlinarith [hcabs])
    have hscaled := mul_lt_mul_of_pos_right hcoef hlamn
    have hnum : X * Real.log ((n : ℝ) + 2) <
        |c * lam ^ n + integerPolynomialShift Q h n| := by
      have hxpos : 0 < X := lt_of_not_ge hX
      have hlogScaled : X * Real.log ((n : ℝ) + 2) ≤
          X * (δ * lam ^ n) := mul_le_mul_of_nonneg_left hnlog hxpos.le
      exact hlogScaled.trans_lt
        (by
          calc
            X * (δ * lam ^ n) = (X * δ) * lam ^ n := by ring
            _ < |c| / 2 * lam ^ n := hscaled
            _ ≤ _ := hlower)
    exact (le_of_lt ((lt_div_iff₀ hlogpos).2 hnum))

/-- Canonical algebraic-ratio residue criterion.  Under an asymptotically geometric leading
scale, full shift separation is equivalent to separation of all polynomial shifts of one
integer minimal-polynomial residue. -/
theorem logarithmicallyShiftSeparated_iff_canonicalResidue
    {b : ℕ → ℝ} {lam A : ℝ} {m : Polynomial ℤ}
    (hlam1 : 1 < lam) (hA : 0 < A)
    (hm : IsIntegerMinimalPolynomialAt m lam)
    (hEG : Tendsto (fun n => b n / (A * lam ^ n)) atTop (𝓝 1)) :
    LogarithmicallyShiftSeparated b ↔
      CanonicalResidueShiftSeparated m b := by
  constructor
  · intro hsep R hR
    exact hsep (m * R) (mul_ne_zero hm.1 hR)
  · intro hcan
    let h : ℕ → ℝ := fun n => b n - A * lam ^ n
    have hh : h =o[atTop] fun n : ℕ => lam ^ n := by
      simpa only [h] using
        isLittleO_sub_geometric_of_ratio_tendsto hlam1 hA hEG
    have hRB : LogarithmicallyResonanceBreakingAt lam h := by
      refine ⟨hh, ?_⟩
      intro Q hQ hQeval
      obtain ⟨c, hc, R, hR, hfactor⟩ := hm.2.2 Q hQ hQeval
      have hQb : ∀ n, integerPolynomialShift Q b n =
          integerPolynomialShift Q h n := by
        intro n
        have hbdecomp : b = fun k => A * lam ^ k + h k := by
          funext k
          simp only [h]
          ring
        rw [hbdecomp, integerPolynomialShift_add,
          integerPolynomialShift_const_mul,
          integerPolynomialShift_geometric, hQeval]
        ring
      have hshift : ∀ n,
          integerPolynomialShift (m * R) b n =
            (c : ℝ) * integerPolynomialShift Q h n := by
        intro n
        rw [← hfactor, integerPolynomialShift_C_mul, hQb]
      have hcast : (c : ℝ) ≠ 0 := by exact_mod_cast hc
      have hcabs : 0 < |(c : ℝ)| := abs_pos.mpr hcast
      have ht := (hcan R hR).atTop_div_const hcabs
      refine ht.congr' ?_
      filter_upwards with n
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hlogpos : 0 < Real.log ((n : ℝ) + 2) :=
        Real.log_pos (by linarith)
      rw [hshift n, abs_mul]
      field_simp [hcabs.ne', hlogpos.ne']
    have hsep := logarithmicallyShiftSeparated_hierarchical hlam1 hA hRB
    have hbdecomp : (fun n => A * lam ^ n + h n) = b := by
      funext n
      simp only [h]
      ring
    simpa only [hbdecomp] using hsep

/-- The card's primitive-minimal-polynomial formulation of the canonical residue criterion. -/
theorem logarithmicallyShiftSeparated_iff_primitiveMinpolyResidue
    {b : ℕ → ℝ} {lam A : ℝ}
    (hlam1 : 1 < lam) (hA : 0 < A) (hlam : IsAlgebraic ℚ lam)
    (hEG : Tendsto (fun n => b n / (A * lam ^ n)) atTop (𝓝 1)) :
    LogarithmicallyShiftSeparated b ↔
      CanonicalResidueShiftSeparated (primitiveRationalMinpolyInteger lam) b :=
  logarithmicallyShiftSeparated_iff_canonicalResidue hlam1 hA
    (isIntegerMinimalPolynomialAt_primitiveRationalMinpolyInteger hlam) hEG

lemma stretchedExp_isLittleO_const_pow
    {α lam : ℝ} (_hα0 : 0 < α) (hα1 : α < 1) (hlam1 : 1 < lam) :
    (fun n : ℕ => stretchedExp α n) =o[atTop]
      fun n : ℕ => lam ^ n := by
  have hpow : (fun x : ℝ => x ^ α) =o[atTop] fun x : ℝ => x := by
    refine (Asymptotics.isLittleO_iff_tendsto' ?_).2 ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      intro hzero
      exact (hx.ne' hzero).elim
    · have ht := tendsto_rpow_neg_atTop (sub_pos.mpr hα1)
      have ht' : Tendsto (fun x : ℝ => x ^ (α - 1)) atTop (𝓝 0) := by
        convert ht using 1
        ring
      refine ht'.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact Real.rpow_sub_one hx.ne' α
  have hloglam : 0 < Real.log lam := Real.log_pos hlam1
  have hpowBound := hpow.bound (half_pos hloglam)
  have hdiff : Tendsto (fun x : ℝ => x * Real.log lam - x ^ α) atTop atTop := by
    have hlinear : Tendsto (fun x : ℝ => (Real.log lam / 2) * x) atTop atTop :=
      tendsto_id.const_mul_atTop (half_pos hloglam)
    refine tendsto_atTop_mono' atTop ?_ hlinear
    filter_upwards [hpowBound, eventually_gt_atTop (0 : ℝ)] with x hxpow hx
    simp only [Real.norm_eq_abs, abs_of_pos hx,
      abs_of_pos (Real.rpow_pos_of_pos hx α)] at hxpow
    nlinarith
  have hreal : (fun x : ℝ => stretchedExp α x) =o[atTop]
      fun x : ℝ => Real.exp (x * Real.log lam) := by
    change (fun x : ℝ => Real.exp (x ^ α)) =o[atTop]
      fun x : ℝ => Real.exp (x * Real.log lam)
    rw [Real.isLittleO_exp_comp_exp_comp]
    exact hdiff
  have hnat := hreal.comp_tendsto tendsto_natCast_atTop_atTop
  refine hnat.congr' (Filter.Eventually.of_forall fun _ => rfl)
    (Filter.Eventually.of_forall fun n => ?_)
  simp only [Function.comp_apply]
  rw [Real.exp_nat_mul, Real.exp_log (zero_lt_one.trans hlam1)]

/-- Every nonzero fixed integer stencil separates the stretched-exponential profile at a rate
larger than logarithmic.  This is the phase-free finite-difference input used by the hierarchy
corollary. -/
theorem logarithmicallyShiftSeparated_stretchedExp
    {α B : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hB : 0 < B) :
    LogarithmicallyShiftSeparated (fun n => B * stretchedExp α n) := by
  intro Q hQ
  let d := polynomialRealCoeffFinsupp Q
  have hex : ∃ j, stretchedMoment d j ≠ 0 := by
    obtain ⟨j, _hj, hjne⟩ := exists_stretchedMoment_ne_of_polynomial hQ
    exact ⟨j, by simpa only [d] using hjne⟩
  let j := Nat.find hex
  have hmoment : stretchedMoment d j ≠ 0 := Nat.find_spec hex
  have hcancel : ∀ k < j, stretchedMoment d k = 0 := by
    intro k hk
    exact not_ne_iff.mp (Nat.find_min hex hk)
  rw [Filter.tendsto_atTop]
  intro A
  let C : ℝ := 2 * (|A| + 1) / B
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hgapReal := eventually_const_mul_log_lt_abs_stretchedFiniteDifference
    hα0 hα1 d j hcancel hmoment hC
  have hgapNat := tendsto_natCast_atTop_atTop.eventually hgapReal
  filter_upwards [hgapNat, eventually_log_nat_add_two_le_two_mul_log_nat,
      eventually_ge_atTop 2] with n hgap hlog hn
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogpos : 0 < Real.log ((n : ℝ) + 2) :=
    Real.log_pos (by linarith)
  have hsum :
      (∑ r ∈ Finset.range (Q.natDegree + 1),
          (Q.coeff r : ℝ) * (B * stretchedExp α (n + r))) =
        B * stretchedFiniteDifference α d n := by
    rw [stretchedFiniteDifference_polynomialRealCoeffFinsupp]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  simp only [Nat.cast_add]
  rw [hsum, abs_mul, abs_of_pos hB]
  have hnonneg : 0 ≤
      B * |stretchedFiniteDifference α d n| /
        Real.log ((n : ℝ) + 2) := by positivity
  by_cases hA : A ≤ 0
  · exact hA.trans hnonneg
  have hratio :
      A * Real.log ((n : ℝ) + 2) <
        B * |stretchedFiniteDifference α d n| := by
    have hClog : C * Real.log n < |stretchedFiniteDifference α d n| := by
      simpa only [Nat.cast_ofNat] using hgap
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have hAabs : A ≤ |A| + 1 := by
      have := le_abs_self A
      linarith
    dsimp [C] at hClog
    have hleft : A * Real.log ((n : ℝ) + 2) ≤
        2 * (|A| + 1) * Real.log n := by nlinarith
    have hright : 2 * (|A| + 1) * Real.log n <
        B * |stretchedFiniteDifference α d n| := by
      have hClog' :
          (2 * (|A| + 1) * Real.log n) / B <
            |stretchedFiniteDifference α d n| := by
        convert hClog using 1
        ring
      simpa [mul_comm] using (div_lt_iff₀ hB).mp hClog'
    exact hleft.trans_lt hright
  exact (le_of_lt ((lt_div_iff₀ hlogpos).2 hratio))

theorem logarithmicallyResonanceBreakingAt_stretchedExp
    {α lam B : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hlam1 : 1 < lam) (hB : 0 < B) :
    LogarithmicallyResonanceBreakingAt lam
      (fun n => B * stretchedExp α n) := by
  refine ⟨(stretchedExp_isLittleO_const_pow hα0 hα1 hlam1).const_mul_left B, ?_⟩
  intro Q hQ _heval
  have hsep := logarithmicallyShiftSeparated_stretchedExp hα0 hα1 hB
  simpa only [LogarithmicallyShiftSeparated, integerPolynomialShift] using hsep Q hQ

/-- Phase-uniform HT for a geometric leading magnitude plus any resonance-breaking lower scale. -/
theorem hypertranscendental_of_hierarchical_resonanceBreaking
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {h : ℕ → ℝ} {lam A : ℝ} (hlam1 : 1 < lam) (hA : 0 < A)
    (hRB : LogarithmicallyResonanceBreakingAt lam h)
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ =
        Real.exp (-(A * lam ^ i + h i))) :
    Hypertranscendental f := by
  apply hypertranscendental_of_eventually_uniformGeometric_logarithmicallyShiftSeparated
    hf hb
  · exact eventually_pos_hierarchical hlam1 hA hRB.1
  · exact uniformGeometricGrowth_hierarchical hlam1 hA hRB.1
  · exact logarithmicallyShiftSeparated_hierarchical hlam1 hA hRB

/-- Stretched-exponential resonance breaking below an arbitrary geometric leading scale. -/
theorem hypertranscendental_of_geometric_add_stretchedExp
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {α lam A B : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hlam1 : 1 < lam) (hA : 0 < A) (hB : 0 < B)
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ =
        Real.exp (-(A * lam ^ i + B * stretchedExp α i))) :
    Hypertranscendental f := by
  exact hypertranscendental_of_hierarchical_resonanceBreaking hf hlam1 hA
    (logarithmicallyResonanceBreakingAt_stretchedExp hα0 hα1 hlam1 hB) hb

/-- The explicit `2^n + exp(sqrt n)` phase-uniform example. -/
theorem hypertranscendental_of_twoPow_add_expSqrt
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ =
        Real.exp (-((2 : ℝ) ^ i + Real.exp (Real.sqrt i)))) :
    Hypertranscendental f := by
  apply hypertranscendental_of_geometric_add_stretchedExp hf
    (α := (1 / 2 : ℝ)) (lam := 2) (A := 1) (B := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [hb] with i hi
  rw [hi]
  have hsqrt : Real.exp (Real.sqrt (i : ℝ)) =
      stretchedExp (1 / 2 : ℝ) i := by
    change Real.exp (Real.sqrt (i : ℝ)) =
      Real.exp ((i : ℝ) ^ (1 / 2 : ℝ))
    exact congrArg Real.exp (Real.sqrt_eq_rpow (i : ℝ))
  rw [hsqrt]
  simp only [one_mul]

end

end GaloisForLFunctions
