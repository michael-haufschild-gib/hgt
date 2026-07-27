import GaloisForLFunctions.HTGeometry.PolynomialPowerDegreeSeparation

open Filter Finset PowerSeries MvPolynomial Polynomial Topology Asymptotics Set

namespace GaloisForLFunctions

noncomputable section

lemma key_scaledPowerValuation {β B : ℝ} {D : ℕ} (t : Fin D → ℕ) :
    (key t).sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) =
      B * tuplePowerValuation β t := by
  rw [valuation_eq_key_sum, tuplePowerValuation, Finset.mul_sum]

lemma support_window_of_key_tupleInWindow {q K D : ℕ} (t : Fin D → ℕ)
    (hwindow : tupleInWindow q K t) {ν : ℕ →₀ ℕ} (hkey : key t = ν) :
    ∀ i, ν i ≠ 0 → q - K ≤ i ∧ i ≤ q + K := by
  intro i hi
  have hkeyi : key t i ≠ 0 := by simpa [hkey] using hi
  have hex : ∃ j, t j = i := by
    by_contra hno
    push Not at hno
    apply hkeyi
    simp [key, hno]
  obtain ⟨j, hj⟩ := hex
  have hjw := hwindow j
  omega

/-- The atom norm formula only needs the coefficient profile at indices actually used by a
nonzero atom.  This support-local form is what lets finite zero prefixes disappear from a
regrouped ADE identity. -/
lemma norm_aval_of_nonzero_coefficients {F : PowerSeries ℂ} {b : ℕ → ℝ}
    (hb : ∀ i, PowerSeries.coeff i F ≠ 0 →
      ‖PowerSeries.coeff i F‖ = Real.exp (-b i))
    (ν : ℕ →₀ ℕ)
    (hνprod : ν.prod (fun i k => (PowerSeries.coeff i F) ^ k) ≠ 0) :
    ‖ν.prod (fun i k => (PowerSeries.coeff i F) ^ k)‖ =
      Real.exp (-ν.sum (fun i k => (k : ℝ) * b i)) := by
  rw [Finsupp.prod, norm_prod]
  rw [show (-ν.sum (fun i k => (k : ℝ) * b i)) =
      ∑ i ∈ ν.support, (-(ν i : ℝ) * b i) by
    rw [Finsupp.sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)]
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hpow : (PowerSeries.coeff i F) ^ ν i ≠ 0 := by
    rw [Finsupp.prod] at hνprod
    exact Finset.prod_ne_zero_iff.mp hνprod i hi
  have hcoeff : PowerSeries.coeff i F ≠ 0 := by
    exact fun hzero => hpow (by rw [hzero, zero_pow (Finsupp.mem_support_iff.mp hi)])
  rw [norm_pow, hb i hcoeff, ← Real.exp_nat_mul]
  ring_nf

/-- Support domination with zero atom products removed.  Only atoms for which both the grouped
integer weight and the coefficient product are nonzero participate in the valuation comparison. -/
theorem aeval_coeff_ne_zero_of_int_dominant_on_active_support
    (n N : ℕ) (F : PowerSeries ℂ) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    {b : ℕ → ℝ}
    (hb : ∀ i, PowerSeries.coeff i F ≠ 0 →
      ‖PowerSeries.coeff i F‖ = Real.exp (-b i))
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (ν₀ : ℕ →₀ ℕ)
    (hν₀ : ν₀ ∈ (sigmaIdx n N Q).image (atomKeyOf n))
    (hw₀ : aevalWeight n N Q ν₀ ≠ 0)
    (ha₀ : ν₀.prod (fun i k => (PowerSeries.coeff i F) ^ k) ≠ 0)
    {G : ℝ}
    (hgap : ∀ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
      aevalWeight n N Q ν ≠ 0 →
      ν.prod (fun i k => (PowerSeries.coeff i F) ^ k) ≠ 0 → ν ≠ ν₀ →
        ν₀.sum (fun i k => (k : ℝ) * b i) + G ≤
          ν.sum (fun i k => (k : ℝ) * b i))
    (hmass : (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
        ‖aevalWeight n N Q ν‖) < Real.exp G) :
    PowerSeries.coeff N (aeval (formalJets n F) Q) ≠ 0 := by
  classical
  let s := (sigmaIdx n N Q).image (atomKeyOf n)
  let a : (ℕ →₀ ℕ) → ℂ := fun ν =>
    ν.prod (fun i k => (PowerSeries.coeff i F) ^ k)
  let c : (ℕ →₀ ℕ) → ℂ := fun ν => aevalWeight n N Q ν
  let s' := s.filter (fun ν => c ν ≠ 0 ∧ a ν ≠ 0)
  have hsum : ∑ ν ∈ s, c ν * a ν = ∑ ν ∈ s', c ν * a ν := by
    change ∑ ν ∈ s, c ν * a ν =
      ∑ ν ∈ s.filter (fun ν => c ν ≠ 0 ∧ a ν ≠ 0), c ν * a ν
    refine (Finset.sum_filter_of_ne fun ν hν hnot => ?_).symm
    exact mul_ne_zero_iff.mp hnot
  have hν₀s' : ν₀ ∈ s' := by
    exact Finset.mem_filter.mpr ⟨hν₀, hw₀, ha₀⟩
  have hmass' : (∑ ν ∈ s', ‖c ν‖) < Real.exp G := by
    apply lt_of_le_of_lt _ hmass
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => norm_nonneg _)
  let V : (ℕ →₀ ℕ) → ℝ := fun ν => ν.sum (fun i k => (k : ℝ) * b i)
  let a' : (ℕ →₀ ℕ) → ℂ := fun ν =>
    if ν ∈ s' then a ν else (Real.exp (-V ν) : ℝ)
  have ha' : ∀ ν, ‖a' ν‖ = Real.exp (-V ν) := by
    intro ν
    by_cases hν : ν ∈ s'
    · simp only [a', if_pos hν]
      obtain ⟨_hνs, _hw, ha⟩ := Finset.mem_filter.mp hν
      exact norm_aval_of_nonzero_coefficients hb ν ha
    · simp only [a', if_neg hν, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.exp_nonneg _)]
  have hsurvive' : ∑ ν ∈ s', c ν * a' ν ≠ 0 := by
    refine weighted_sum_ne_zero_of_min_valuation_complex s'
      V a' ha' c hν₀s' hw₀ (G := G) ?_ ?_
    · intro ν hν
      obtain ⟨hne, hνs'⟩ := Finset.mem_erase.mp hν
      obtain ⟨hνs, hw, ha⟩ := Finset.mem_filter.mp hνs'
      exact hgap ν hνs hw ha hne
    · calc
        (∑ ν ∈ s', ‖c ν‖) < Real.exp G := hmass'
        _ = 1 * Real.exp G := (one_mul _).symm
        _ ≤ ‖c ν₀‖ * Real.exp G := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg G)
          exact aevalWeight_norm_ge_one n N Q ν₀ hQint hw₀
  have hsurvive : ∑ ν ∈ s', c ν * a ν ≠ 0 := by
    have heq : ∑ ν ∈ s', c ν * a ν = ∑ ν ∈ s', c ν * a' ν := by
      apply Finset.sum_congr rfl
      intro ν hν
      simp only [a', if_pos hν]
    rw [heq]
    exact hsurvive'
  rw [coeff_aeval_regrouped_weight]
  rw [Finset.sum_congr rfl fun ν (_ : ν ∈ s) => mul_comm (a ν) (c ν)]
  exact fun hzero => hsurvive (by simpa [hsum] using hzero)

/-- A valuation profile which agrees with `B i^β` on the certified tail and records the actual
nonzero coefficient norm on the finite prefix. -/
noncomputable def eventualPolynomialPowerValuation
    (F : PowerSeries ℂ) (T : ℕ) (B β : ℝ) (i : ℕ) : ℝ :=
  if T ≤ i then B * (i : ℝ) ^ β else -Real.log ‖PowerSeries.coeff i F‖

lemma eventualPolynomialPowerValuation_eq_of_ge
    (F : PowerSeries ℂ) (T : ℕ) (B β : ℝ) {i : ℕ} (hi : T ≤ i) :
    eventualPolynomialPowerValuation F T B β i = B * (i : ℝ) ^ β := by
  simp [eventualPolynomialPowerValuation, hi]

lemma norm_coeff_eq_exp_eventualPolynomialPowerValuation_of_ne
    {F : PowerSeries ℂ} {T : ℕ} {B β : ℝ}
    (htail : ∀ i ≥ T, ‖PowerSeries.coeff i F‖ =
      Real.exp (-(B * (i : ℝ) ^ β)))
    (i : ℕ) (hi : PowerSeries.coeff i F ≠ 0) :
    ‖PowerSeries.coeff i F‖ =
      Real.exp (-eventualPolynomialPowerValuation F T B β i) := by
  by_cases hTi : T ≤ i
  · simpa [eventualPolynomialPowerValuation, hTi] using htail i hTi
  · have hnorm : 0 < ‖PowerSeries.coeff i F‖ := norm_pos_iff.mpr hi
    simp only [eventualPolynomialPowerValuation, if_neg hTi, neg_neg]
    exact (Real.exp_log hnorm).symm

/-- A nonzero active atom admits a valuation minimizer among all active atoms at the coefficient
level. -/
theorem exists_min_active_aevalWeight {n N : ℕ}
    (F : PowerSeries ℂ) (Q : MvPolynomial (Fin (n + 2)) ℂ) (b : ℕ → ℝ)
    {νw : ℕ →₀ ℕ}
    (hνw : νw ∈ (sigmaIdx n N Q).image (atomKeyOf n))
    (hww : aevalWeight n N Q νw ≠ 0)
    (haw : νw.prod (fun i k => (PowerSeries.coeff i F) ^ k) ≠ 0) :
    ∃ ν₀ ∈ (sigmaIdx n N Q).image (atomKeyOf n),
      aevalWeight n N Q ν₀ ≠ 0 ∧
      ν₀.prod (fun i k => (PowerSeries.coeff i F) ^ k) ≠ 0 ∧
      (∀ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
        aevalWeight n N Q ν ≠ 0 →
        ν.prod (fun i k => (PowerSeries.coeff i F) ^ k) ≠ 0 →
          ν₀.sum (fun i k => (k : ℝ) * b i) ≤
            ν.sum (fun i k => (k : ℝ) * b i)) ∧
      ν₀.sum (fun i k => (k : ℝ) * b i) ≤
        νw.sum (fun i k => (k : ℝ) * b i) := by
  classical
  let K := ((sigmaIdx n N Q).image (atomKeyOf n)).filter (fun ν =>
    aevalWeight n N Q ν ≠ 0 ∧
      ν.prod (fun i k => (PowerSeries.coeff i F) ^ k) ≠ 0)
  have hνwK : νw ∈ K := Finset.mem_filter.mpr ⟨hνw, hww, haw⟩
  obtain ⟨ν₀, hν₀K, hmin⟩ :=
    K.exists_min_image (fun ν => ν.sum (fun i k => (k : ℝ) * b i)) ⟨νw, hνwK⟩
  obtain ⟨hν₀, hw₀, ha₀⟩ := Finset.mem_filter.mp hν₀K
  refine ⟨ν₀, hν₀, hw₀, ha₀, ?_, hmin νw hνwK⟩
  intro ν hν hw ha
  exact hmin ν (Finset.mem_filter.mpr ⟨hν, hw, ha⟩)

/-- An eventual coefficient profile still obeys the logarithmic ADE bend law after inactive zero
products are removed. -/
theorem exists_near_min_active_aevalWeight_of_relation
    {n N : ℕ} (F : PowerSeries ℂ) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    {b : ℕ → ℝ}
    (hb : ∀ i, PowerSeries.coeff i F ≠ 0 →
      ‖PowerSeries.coeff i F‖ = Real.exp (-b i))
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hrel : aeval (formalJets n F) Q = 0)
    {νw : ℕ →₀ ℕ}
    (hνw : νw ∈ (sigmaIdx n N Q).image (atomKeyOf n))
    (hww : aevalWeight n N Q νw ≠ 0)
    (haw : νw.prod (fun i k => (PowerSeries.coeff i F) ^ k) ≠ 0) :
    let P : ℝ :=
      magnitudeCoefficientMass Q *
        (((magnitudeMaxJetOrder n Q + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ) *
        (((N + 1) ^ (magnitudeMaxJetDegree n Q + magnitudeMaxJetOrder n Q) : ℕ) : ℝ)
    ∃ ν₀ ν₁ : ℕ →₀ ℕ,
      ν₀ ∈ (sigmaIdx n N Q).image (atomKeyOf n) ∧
      aevalWeight n N Q ν₀ ≠ 0 ∧
      ν₀.prod (fun i k => (PowerSeries.coeff i F) ^ k) ≠ 0 ∧
      (∀ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
        aevalWeight n N Q ν ≠ 0 →
        ν.prod (fun i k => (PowerSeries.coeff i F) ^ k) ≠ 0 →
          ν₀.sum (fun i k => (k : ℝ) * b i) ≤
            ν.sum (fun i k => (k : ℝ) * b i)) ∧
      ν₁ ∈ (sigmaIdx n N Q).image (atomKeyOf n) ∧
      aevalWeight n N Q ν₁ ≠ 0 ∧
      ν₁.prod (fun i k => (PowerSeries.coeff i F) ^ k) ≠ 0 ∧
      ν₁ ≠ ν₀ ∧
      ν₁.sum (fun i k => (k : ℝ) * b i) <
        ν₀.sum (fun i k => (k : ℝ) * b i) + Real.log (P + 1) := by
  classical
  dsimp only
  obtain ⟨ν₀, hν₀, hw₀, ha₀, hmin, _⟩ :=
    exists_min_active_aevalWeight F Q b hνw hww haw
  let P : ℝ :=
    magnitudeCoefficientMass Q *
      (((magnitudeMaxJetOrder n Q + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ) *
      (((N + 1) ^ (magnitudeMaxJetDegree n Q + magnitudeMaxJetOrder n Q) : ℕ) : ℝ)
  have hP0 : 0 ≤ P := by
    have hcoeff0 : 0 ≤ magnitudeCoefficientMass Q := by
      rw [magnitudeCoefficientMass]
      positivity
    dsimp [P]
    exact mul_nonneg (mul_nonneg hcoeff0 (by positivity)) (by positivity)
  have hmassLe :
      (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖) ≤ P := by
    simpa only [P] using aevalWeight_mass_le_singlePolynomial n Q N
  have hmass :
      (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖) <
        Real.exp (Real.log (P + 1)) := by
    rw [Real.exp_log (by linarith : 0 < P + 1)]
    exact hmassLe.trans_lt (lt_add_one P)
  have hcoeffzero : PowerSeries.coeff N (aeval (formalJets n F) Q) = 0 := by
    rw [hrel, map_zero]
  have hex : ∃ ν₁ ∈ (sigmaIdx n N Q).image (atomKeyOf n),
      aevalWeight n N Q ν₁ ≠ 0 ∧
      ν₁.prod (fun i k => (PowerSeries.coeff i F) ^ k) ≠ 0 ∧ ν₁ ≠ ν₀ ∧
      ν₁.sum (fun i k => (k : ℝ) * b i) <
        ν₀.sum (fun i k => (k : ℝ) * b i) + Real.log (P + 1) := by
    by_contra hno
    push Not at hno
    have hgap : ∀ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
        aevalWeight n N Q ν ≠ 0 →
        ν.prod (fun i k => (PowerSeries.coeff i F) ^ k) ≠ 0 → ν ≠ ν₀ →
          ν₀.sum (fun i k => (k : ℝ) * b i) + Real.log (P + 1) ≤
            ν.sum (fun i k => (k : ℝ) * b i) := by
      intro ν hν hw ha hne
      exact hno ν hν hw ha hne
    have hne := aeval_coeff_ne_zero_of_int_dominant_on_active_support
      n N F Q hb hQint ν₀ hν₀ hw₀ ha₀ hgap hmass
    exact hne hcoeffzero
  obtain ⟨ν₁, hν₁, hw₁, ha₁, hne, hnear⟩ := hex
  exact ⟨ν₀, ν₁, hν₀, hw₀, ha₀, hmin, hν₁, hw₁, ha₁, hne,
    by simpa [P] using hnear⟩

/-- Total discrepancy between two valuation profiles on the finite prefix `[0,T)`. -/
noncomputable def valuationPrefixDeviation (T : ℕ) (b p : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range T, |b i - p i|

lemma valuationPrefixDeviation_nonneg (T : ℕ) (b p : ℕ → ℝ) :
    0 ≤ valuationPrefixDeviation T b p := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Changing a valuation profile on a finite prefix perturbs a multi-index valuation by at most
its total count times the fixed prefix discrepancy. -/
lemma abs_finsupp_valuation_sub_le_count_mul_prefixDeviation
    {T : ℕ} {b p : ℕ → ℝ} (htail : ∀ i ≥ T, b i = p i)
    (ν : ℕ →₀ ℕ) :
    |ν.sum (fun i k => (k : ℝ) * b i) -
        ν.sum (fun i k => (k : ℝ) * p i)| ≤
      ((ν.sum (fun _ k => k) : ℕ) : ℝ) * valuationPrefixDeviation T b p := by
  classical
  have hdiff :
      ν.sum (fun i k => (k : ℝ) * b i) -
          ν.sum (fun i k => (k : ℝ) * p i) =
        ∑ i ∈ ν.support, (ν i : ℝ) * (b i - p i) := by
    rw [Finsupp.sum, Finsupp.sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hdiff]
  calc
    |∑ i ∈ ν.support, (ν i : ℝ) * (b i - p i)|
        ≤ ∑ i ∈ ν.support, |(ν i : ℝ) * (b i - p i)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ ν.support.filter (fun i => i < T),
          |(ν i : ℝ) * (b i - p i)| := by
          symm
          apply Finset.sum_filter_of_ne
          intro i hi hne
          by_contra hnot
          have hTi : T ≤ i := Nat.le_of_not_gt hnot
          rw [htail i hTi, sub_self, mul_zero, abs_zero] at hne
          exact hne rfl
    _ ≤ ∑ i ∈ ν.support.filter (fun i => i < T),
          ((ν.sum (fun _ k => k) : ℕ) : ℝ) * |b i - p i| := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul, abs_of_nonneg (show 0 ≤ (ν i : ℝ) by positivity)]
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast finsupp_apply_le_count ν i) (abs_nonneg _)
    _ ≤ ∑ i ∈ Finset.range T,
          ((ν.sum (fun _ k => k) : ℕ) : ℝ) * |b i - p i| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
          · intro i hi hnot
            exact mul_nonneg (by positivity) (abs_nonneg _)
    _ = ((ν.sum (fun _ k => k) : ℕ) : ℝ) * valuationPrefixDeviation T b p := by
          rw [valuationPrefixDeviation, Finset.mul_sum]

set_option maxHeartbeats 800000 in
/-- The full bend-pair theorem is insensitive to a finite Taylor prefix.  Inactive atoms using a
zero prefix coefficient disappear, while every active prefix contribution changes the power
valuation by one fixed bounded amount. -/
theorem exists_eventually_polynomialPower_bend_pair_of_eventual_profile
    {β B : ℝ} (hβ : 2 < β) (hB : 0 < B)
    {n T : ℕ} (F : PowerSeries ℂ)
    (htail : ∀ i ≥ T, ‖PowerSeries.coeff i F‖ =
      Real.exp (-(B * (i : ℝ) ^ β)))
    (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hrel : aeval (formalJets n F) Q = 0)
    (hDpos : 0 < magnitudeMaxJetDegree n Q) :
    ∃ D K C Q₀ : ℕ,
      D = magnitudeMaxJetDegree n Q ∧ 0 < D ∧ 0 < C ∧ ∀ q ≥ Q₀,
      ∃ ν₀ ν₁ : ℕ →₀ ℕ,
        ν₀ ≠ ν₁ ∧
        ν₀.sum (fun _ k => k) = D ∧ ν₁.sum (fun _ k => k) = D ∧
        (∀ i, ν₀ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        (∀ i, ν₁ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        0 ≤ ν₁.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) -
          ν₀.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) ∧
        ν₁.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) -
            ν₀.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) <
          (C : ℝ) * Real.log ((q : ℝ) + 2) := by
  classical
  let Z := magnitudeMaxXDegree Q
  let O := magnitudeMaxJetOrder n Q
  obtain ⟨anchor, ha, haD, haMax⟩ :=
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
  let Csum := magnitudeShiftCode n Q anchor
  let Amass : ℝ := magnitudeCoefficientMass Q * (((O + 1) ^ O : ℕ) : ℝ)
  let p : ℕ → ℝ := fun i => B * (i : ℝ) ^ β
  let b : ℕ → ℝ := eventualPolynomialPowerValuation F T B β
  let R : ℝ := (D : ℝ) * valuationPrefixDeviation T b p
  have hR : 0 ≤ R := mul_nonneg (by positivity) (valuationPrefixDeviation_nonneg T b p)
  have hbtail : ∀ i ≥ T, b i = p i := by
    intro i hi
    simp [b, p, eventualPolynomialPowerValuation, hi]
  have hbactive : ∀ i, PowerSeries.coeff i F ≠ 0 →
      ‖PowerSeries.coeff i F‖ = Real.exp (-b i) := by
    intro i hi
    simpa [b] using
      norm_coeff_eq_exp_eventualPolynomialPowerValuation_of_ne htail i hi
  have hCoeffMass : 0 < magnitudeCoefficientMass Q := by
    rw [magnitudeCoefficientMass]
    exact Finset.sum_pos' (fun _ _ => norm_nonneg _)
      ⟨anchor, ha, norm_pos_iff.mpr (MvPolynomial.mem_support_iff.mp ha)⟩
  have hAmass : 0 < Amass := by
    dsimp [Amass]
    exact mul_pos hCoeffMass (by positivity)
  obtain ⟨S, hS⟩ : ∃ S : ℕ, ((C : ℝ) + 1) / B < S :=
    exists_nat_gt (((C : ℝ) + 1) / B)
  have hCS : (C : ℝ) + 1 < B * (S : ℝ) := by
    have := (div_lt_iff₀ hB).mp hS
    simpa [mul_comm] using this
  have hSpos : 0 < S := by
    have hCpos : (0 : ℝ) < (C : ℝ) + 1 := by positivity
    have : (0 : ℝ) < S := (div_pos hCpos hB).trans hS
    exact_mod_cast this
  have hdegEv := eventually_lowerDegree_tuplePower_gap
    (by linarith : 1 < β) hD δ (J + Z) S
  obtain ⟨Qdeg, hQdeg⟩ := Filter.eventually_atTop.mp hdegEv
  obtain ⟨K, hconfEv⟩ := exists_eventually_bounded_powerNearMinimizer hβ hD δ Csum S
  obtain ⟨Qconf, hQconf⟩ := Filter.eventually_atTop.mp hconfEv
  let Llevel := D * (Boff + 1) + anchor 0 + 1
  have hLlevel : 0 < Llevel := by dsimp [Llevel]; omega
  have hlargeEv : ∀ᶠ q : ℕ in atTop,
      Amass * (Llevel : ℝ) ^ E + 1 ≤ (q : ℝ) + 2 :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).eventually_ge_atTop
      (Amass * (Llevel : ℝ) ^ E + 1)
  obtain ⟨Qlarge, hQlarge⟩ := Filter.eventually_atTop.mp hlargeEv
  have hlogTendsto : Tendsto (fun q : ℕ => Real.log ((q : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  obtain ⟨Qlog, hQlog⟩ := Filter.eventually_atTop.mp
    (hlogTendsto.eventually_gt_atTop R)
  let Q₀ := max Qbal (max Qdeg (max Qconf (max Qlarge
    (max Qlog (max (T + K) (max (2 * (J + Z) + 2) 2))))))
  refine ⟨D, K, C, Q₀, hDmax, hD, by dsimp [C, E]; omega, fun q hq => ?_⟩
  have hqbal : Qbal ≤ q := by dsimp [Q₀] at hq; omega
  have hqdeg : Qdeg ≤ q := by dsimp [Q₀] at hq; omega
  have hqconf : Qconf ≤ q := by dsimp [Q₀] at hq; omega
  have hqlarge : Qlarge ≤ q := by dsimp [Q₀] at hq; omega
  have hqlog : Qlog ≤ q := by dsimp [Q₀] at hq; omega
  have hqTK : T + K ≤ q := by dsimp [Q₀] at hq; omega
  have hqthreshold : 2 * (J + Z) + 2 ≤ q := by dsimp [Q₀] at hq; omega
  have hq2 : 2 ≤ q := by dsimp [Q₀] at hq; omega
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
  have hDqN : D * q ≤ N + J := by
    rw [hNadd]
    have hsLower : D * q ≤ ∑ i, s i :=
      mul_le_sum_of_le_apply fun i => by simp [s]
    omega
  have hNZ : Z < N := by
    have hqJZ : J + Z < q := by omega
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
  have hsw_ge : ∀ i, (key s) i ≠ 0 → T ≤ i := by
    intro i hi
    have hex : ∃ j, s j = i := by
      by_contra hno
      push Not at hno
      apply hi
      simp [key, hno]
    obtain ⟨j, rfl⟩ := hex
    dsimp [s]
    omega
  have haw : (key s).prod (fun i k => (PowerSeries.coeff i F) ^ k) ≠ 0 := by
    rw [prod_eq_key_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hnorm := htail (s i) (by dsimp [s]; omega)
    exact norm_pos_iff.mp (by rw [hnorm]; exact Real.exp_pos _)
  let P : ℝ := Amass * (((N + 1) ^ E : ℕ) : ℝ)
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
  have hP0 : 0 < P := by dsimp [P]; positivity
  obtain ⟨ν₀, ν₁, hν₀, hw₀, ha₀, hmin, hν₁, hw₁, ha₁, hne, hgap⟩ :=
    exists_near_min_active_aevalWeight_of_relation
      F Q hbactive hQint hrel hνw hww haw
  have hgapB : ν₁.sum (fun i k => (k : ℝ) * b i) <
      ν₀.sum (fun i k => (k : ℝ) * b i) + Real.log (P + 1) := by
    simpa [P, Amass, E, O, hDmax] using hgap
  have hwitEq : (key s).sum (fun i k => (k : ℝ) * b i) =
      (key s).sum (fun i k => (k : ℝ) * p i) := by
    rw [Finsupp.sum, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hbtail i (hsw_ge i (Finsupp.mem_support_iff.mp hi))]
  have hlogpos : 0 < Real.log (P + 1) := Real.log_pos (by linarith)
  have hν₀nearB : ν₀.sum (fun i k => (k : ℝ) * b i) <
      (key s).sum (fun i k => (k : ℝ) * b i) + Real.log (P + 1) :=
    (hmin (key s) hνw hww haw).trans_lt (lt_add_of_pos_right _ hlogpos)
  have hν₁nearB : ν₁.sum (fun i k => (k : ℝ) * b i) <
      (key s).sum (fun i k => (k : ℝ) * b i) + Real.log (P + 1) :=
    hgapB.trans_le (add_le_add (hmin (key s) hνw hww haw) le_rfl)
  have hlogBound : Real.log (P + 1) ≤ (C : ℝ) * Real.log ((q : ℝ) + 2) := by
    have := log_polynomial_mass_le_mul_log hAmass.le hlevel (hQlarge q hqlarge)
    simpa [P, C, Amass, E] using this
  have hRq : R < Real.log ((q : ℝ) + 2) := hQlog q hqlog
  have hqlogpos : 0 < Real.log ((q : ℝ) + 2) := hR.trans_lt hRq
  have hlogScale : (C : ℝ) * Real.log ((q : ℝ) + 2) + R <
      B * (S : ℝ) * Real.log ((q : ℝ) + 2) := by
    have hmul := mul_lt_mul_of_pos_right hCS hqlogpos
    nlinarith
  have deviation_le (ν : ℕ →₀ ℕ)
      (hν : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n)) :
      |ν.sum (fun i k => (k : ℝ) * b i) -
          ν.sum (fun i k => (k : ℝ) * p i)| ≤ R := by
    have hdev := abs_finsupp_valuation_sub_le_count_mul_prefixDeviation hbtail ν
    have hcountle := appearing_atom_count_le Q hν
    change ν.sum (fun _ k => k) ≤ magnitudeMaxJetDegree n Q at hcountle
    rw [← hDmax] at hcountle
    exact hdev.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcountle)
      (valuationPrefixDeviation_nonneg T b p))
  have hν₀dev := deviation_le ν₀ hν₀
  have hν₁dev := deviation_le ν₁ hν₁
  have hν₀nearScaled : ν₀.sum (fun i k => (k : ℝ) * p i) <
      (key s).sum (fun i k => (k : ℝ) * p i) +
        B * (S : ℝ) * Real.log ((q : ℝ) + 2) := by
    have hp_le : ν₀.sum (fun i k => (k : ℝ) * p i) ≤
        ν₀.sum (fun i k => (k : ℝ) * b i) + R := by
      linarith [neg_le_abs (ν₀.sum (fun i k => (k : ℝ) * b i) -
        ν₀.sum (fun i k => (k : ℝ) * p i))]
    rw [hwitEq] at hν₀nearB
    linarith
  have hν₁nearScaled : ν₁.sum (fun i k => (k : ℝ) * p i) <
      (key s).sum (fun i k => (k : ℝ) * p i) +
        B * (S : ℝ) * Real.log ((q : ℝ) + 2) := by
    have hp_le : ν₁.sum (fun i k => (k : ℝ) * p i) ≤
        ν₁.sum (fun i k => (k : ℝ) * b i) + R := by
      linarith [neg_le_abs (ν₁.sum (fun i k => (k : ℝ) * b i) -
        ν₁.sum (fun i k => (k : ℝ) * p i))]
    rw [hwitEq] at hν₁nearB
    linarith
  have count_eq_top (ν : ℕ →₀ ℕ)
      (hν : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n))
      (hnearScaled : ν.sum (fun i k => (k : ℝ) * p i) <
        (key s).sum (fun i k => (k : ℝ) * p i) +
          B * (S : ℝ) * Real.log ((q : ℝ) + 2)) :
      ν.sum (fun _ k => k) = D := by
    have hcountle := appearing_atom_count_le Q hν
    change ν.sum (fun _ k => k) ≤ magnitudeMaxJetDegree n Q at hcountle
    rw [← hDmax] at hcountle
    rcases hcountle.eq_or_lt with heq | hlt
    · exact heq
    · let d := ν.sum (fun _ k => k)
      have hdD : d < D := by simpa [d] using hlt
      have hsupport := appearing_atom_support_nonempty_of_maxX_lt_level Q hν
        (by simpa [Z] using hNZ)
      have hd : 0 < d := by
        by_contra hd0
        have hdEq : d = 0 := Nat.eq_zero_of_not_pos hd0
        obtain ⟨i, hi⟩ := hsupport
        have hiBound := finsupp_apply_le_count ν i
        have hiNe : ν i ≠ 0 := Finsupp.mem_support_iff.mp hi
        apply hiNe
        apply Nat.eq_zero_of_le_zero
        rw [← hdEq]
        simpa [d] using hiBound
      let t : Fin d → ℕ := tupleOfFinsupp ν d (by rfl)
      have hweightLower := (appearing_atom_weighted_sum_bounds Q hν).1
      change N - Z ≤ ν.sum (fun i k => i * k) at hweightLower
      have hsumt := sum_tupleOfFinsupp ν d (by rfl)
      have hmass : D * q ≤ (∑ i, t i) + (J + Z) := by
        rw [show (∑ i, t i) = ν.sum (fun i k => i * k) by
          simpa [t] using hsumt]
        have hNsplit : N - Z + Z = N := Nat.sub_add_cancel hNZ.le
        omega
      have hνval : ν.sum (fun i k => (k : ℝ) * p i) =
          B * tuplePowerValuation β t := by
        rw [valuation_tupleOfFinsupp ν d (by rfl)]
        simp only [p]
        rw [tuplePowerValuation, Finset.mul_sum]
      have hwitval : (key s).sum (fun i k => (k : ℝ) * p i) =
          B * tuplePowerValuation β (fun i => q + δ i) := by
        simpa [s, p] using key_scaledPowerValuation (β := β) (B := B) s
      have hnearPower : tuplePowerValuation β t <
          tuplePowerValuation β (fun i => q + δ i) +
            (S : ℝ) * Real.log ((q : ℝ) + 2) := by
        rw [hνval, hwitval] at hnearScaled
        nlinarith
      have hsep := hQdeg q hqdeg d hd hdD t hmass
      exact False.elim (not_lt_of_ge hsep.le hnearPower)
  have hν₀count := count_eq_top ν₀ hν₀ hν₀nearScaled
  have hν₁count := count_eq_top ν₁ hν₁ hν₁nearScaled
  have tuple_bounds (ν : ℕ →₀ ℕ)
      (hν : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n))
      (hcount : ν.sum (fun _ k => k) = D) :
      let t := tupleOfFinsupp ν D hcount
      D * q + (∑ i, δ i) ≤ ∑ i, t i ∧
        (∑ i, t i) ≤ D * q + (∑ i, δ i) + Csum := by
    dsimp only
    obtain ⟨m, hm, hmD, hinv⟩ := appearing_atom_sum_add_shiftCode Q hν
    have hmTop : jetMonomialDegree n m = magnitudeMaxJetDegree n Q := by
      rw [hmD, hcount]
      exact hDmax
    have hcodele := haMax m hm hmTop
    have hwitinv := witness_sum_add_shiftCode Q ha δ N rfl (hqJ.trans hqsum)
    have hsumt := sum_tupleOfFinsupp ν D hcount
    have hsEq : (∑ i, s i) = D * q + ∑ i, δ i := by
      simp [s, D, Finset.sum_add_distrib]
    change ν.sum (fun i k => i * k) + magnitudeShiftCode n Q m = N + O at hinv
    change (∑ i, s i) + Csum = N + O at hwitinv
    change magnitudeShiftCode n Q m ≤ Csum at hcodele
    constructor <;> rw [hsumt] <;> omega
  have confined (ν : ℕ →₀ ℕ)
      (hν : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n))
      (hcount : ν.sum (fun _ k => k) = D)
      (hnearScaled : ν.sum (fun i k => (k : ℝ) * p i) <
        (key s).sum (fun i k => (k : ℝ) * p i) +
          B * (S : ℝ) * Real.log ((q : ℝ) + 2)) :
      ∀ i, ν i ≠ 0 → q - K ≤ i ∧ i ≤ q + K := by
    let t : Fin D → ℕ := tupleOfFinsupp ν D hcount
    have hνval : ν.sum (fun i k => (k : ℝ) * p i) =
        B * tuplePowerValuation β t := by
      rw [valuation_tupleOfFinsupp ν D hcount]
      simp only [p]
      rw [tuplePowerValuation, Finset.mul_sum]
    have hwitval : (key s).sum (fun i k => (k : ℝ) * p i) =
        B * tuplePowerValuation β (fun i => q + δ i) := by
      simpa [s, p] using key_scaledPowerValuation (β := β) (B := B) s
    have hnearPower : tuplePowerValuation β t <
        tuplePowerValuation β (fun i => q + δ i) +
          (S : ℝ) * Real.log ((q : ℝ) + 2) := by
      rw [hνval, hwitval] at hnearScaled
      nlinarith
    have hwindow : tupleInWindow q K t :=
      hQconf q hqconf t (by simpa [t] using tuple_bounds ν hν hcount) hnearPower
    exact support_window_of_key_tupleInWindow t hwindow
      (key_tupleOfFinsupp ν D hcount)
  have hν₀window := confined ν₀ hν₀ hν₀count hν₀nearScaled
  have hν₁window := confined ν₁ hν₁ hν₁count hν₁nearScaled
  have valEq_of_window (ν : ℕ →₀ ℕ)
      (hwindow : ∀ i, ν i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) :
      ν.sum (fun i k => (k : ℝ) * b i) =
        ν.sum (fun i k => (k : ℝ) * p i) := by
    rw [Finsupp.sum, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hlow := (hwindow i (Finsupp.mem_support_iff.mp hi)).1
    rw [hbtail i (by omega)]
  have hval₀ := valEq_of_window ν₀ hν₀window
  have hval₁ := valEq_of_window ν₁ hν₁window
  have hmin01 := hmin ν₁ hν₁ hw₁ ha₁
  rw [hval₀, hval₁] at hmin01
  have hgapP : ν₁.sum (fun i k => (k : ℝ) * p i) <
      ν₀.sum (fun i k => (k : ℝ) * p i) + Real.log (P + 1) := by
    rw [hval₀, hval₁] at hgapB
    exact hgapB
  have hdiff0 : 0 ≤ ν₁.sum (fun i k => (k : ℝ) * p i) -
      ν₀.sum (fun i k => (k : ℝ) * p i) := sub_nonneg.mpr hmin01
  have hdiff : ν₁.sum (fun i k => (k : ℝ) * p i) -
        ν₀.sum (fun i k => (k : ℝ) * p i) <
      (C : ℝ) * Real.log ((q : ℝ) + 2) := by
    have : ν₁.sum (fun i k => (k : ℝ) * p i) -
        ν₀.sum (fun i k => (k : ℝ) * p i) < Real.log (P + 1) := by
      linarith
    exact this.trans_le hlogBound
  simpa only [p] using ⟨ν₀, ν₁, hne.symm, hν₀count, hν₁count,
    hν₀window, hν₁window, hdiff0, hdiff⟩

set_option maxHeartbeats 500000 in
/-- Degree one needs no convex confinement: coefficient grading alone puts every large active
atom in a fixed tail window, so the eventual profile gives the same bounded bend pairs for every
real exponent. -/
theorem exists_eventually_polynomialPower_bend_pair_of_eventual_profile_jetDegree_one
    {β B : ℝ} {n T : ℕ} (F : PowerSeries ℂ)
    (htail : ∀ i ≥ T, ‖PowerSeries.coeff i F‖ =
      Real.exp (-(B * (i : ℝ) ^ β)))
    (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hrel : aeval (formalJets n F) Q = 0)
    (hDegreeOne : magnitudeMaxJetDegree n Q = 1) :
    ∃ K C Q₀ : ℕ, 0 < C ∧ ∀ q ≥ Q₀,
      ∃ ν₀ ν₁ : ℕ →₀ ℕ,
        ν₀ ≠ ν₁ ∧
        ν₀.sum (fun _ k => k) = 1 ∧ ν₁.sum (fun _ k => k) = 1 ∧
        (∀ i, ν₀ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        (∀ i, ν₁ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        0 ≤ ν₁.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) -
          ν₀.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) ∧
        ν₁.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) -
            ν₀.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) <
          (C : ℝ) * Real.log ((q : ℝ) + 2) := by
  classical
  let Z := magnitudeMaxXDegree Q
  let O := magnitudeMaxJetOrder n Q
  have hDpos : 0 < magnitudeMaxJetDegree n Q := by rw [hDegreeOne]; omega
  obtain ⟨anchor, ha, haD, haMax⟩ :=
    exists_maxShiftCode_topDegree_anchor Q hDpos
  let D := jetMonomialDegree n anchor
  have hDmax : D = magnitudeMaxJetDegree n Q := by simpa [D] using haD
  have hDone : D = 1 := hDmax.trans hDegreeOne
  have hD : 0 < D := by rw [hDone]; omega
  have haPos : 0 < jetMonomialDegree n anchor := by simpa [D] using hD
  obtain ⟨δ, _hδinj, Qbal, hbalanced⟩ :=
    exists_eventually_balanced_nonzero_aevalWeight ha haPos
  let J := jetMonomialOrder n anchor
  let Boff := magnitudeOffsetMax δ
  let E := D + O
  let C := E + 1
  let Csum := magnitudeShiftCode n Q anchor
  let K := (∑ i, δ i) + Csum
  let Amass : ℝ := magnitudeCoefficientMass Q * (((O + 1) ^ O : ℕ) : ℝ)
  let p : ℕ → ℝ := fun i => B * (i : ℝ) ^ β
  let b : ℕ → ℝ := eventualPolynomialPowerValuation F T B β
  have hbtail : ∀ i ≥ T, b i = p i := by
    intro i hi
    simp [b, p, eventualPolynomialPowerValuation, hi]
  have hbactive : ∀ i, PowerSeries.coeff i F ≠ 0 →
      ‖PowerSeries.coeff i F‖ = Real.exp (-b i) := by
    intro i hi
    simpa [b] using
      norm_coeff_eq_exp_eventualPolynomialPowerValuation_of_ne htail i hi
  have hCoeffMass : 0 < magnitudeCoefficientMass Q := by
    rw [magnitudeCoefficientMass]
    exact Finset.sum_pos' (fun _ _ => norm_nonneg _)
      ⟨anchor, ha, norm_pos_iff.mpr (MvPolynomial.mem_support_iff.mp ha)⟩
  have hAmass : 0 < Amass := by
    dsimp [Amass]
    exact mul_pos hCoeffMass (by positivity)
  let Llevel := D * (Boff + 1) + anchor 0 + 1
  have hlargeEv : ∀ᶠ q : ℕ in atTop,
      Amass * (Llevel : ℝ) ^ E + 1 ≤ (q : ℝ) + 2 :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).eventually_ge_atTop
      (Amass * (Llevel : ℝ) ^ E + 1)
  obtain ⟨Qlarge, hQlarge⟩ := Filter.eventually_atTop.mp hlargeEv
  let Q₀ := max Qbal (max Qlarge (max (T + K) (max (2 * (J + Z) + 2) 2)))
  refine ⟨K, C, Q₀, by dsimp [C, E]; omega, fun q hq => ?_⟩
  have hqbal : Qbal ≤ q := by dsimp [Q₀] at hq; omega
  have hqlarge : Qlarge ≤ q := by dsimp [Q₀] at hq; omega
  have hqTK : T + K ≤ q := by dsimp [Q₀] at hq; omega
  have hqthreshold : 2 * (J + Z) + 2 ≤ q := by dsimp [Q₀] at hq; omega
  have hq2 : 2 ≤ q := by dsimp [Q₀] at hq; omega
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
  have hDqN : D * q ≤ N + J := by
    rw [hNadd]
    have hsLower : D * q ≤ ∑ i, s i :=
      mul_le_sum_of_le_apply fun i => by simp [s]
    omega
  have hNZ : Z < N := by
    have hqJZ : J + Z < q := by omega
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
  have haw : (key s).prod (fun i k => (PowerSeries.coeff i F) ^ k) ≠ 0 := by
    rw [prod_eq_key_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hnorm := htail (s i) (by dsimp [s]; omega)
    exact norm_pos_iff.mp (by rw [hnorm]; exact Real.exp_pos _)
  let P : ℝ := Amass * (((N + 1) ^ E : ℕ) : ℝ)
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
  have hP0 : 0 < P := by dsimp [P]; positivity
  obtain ⟨ν₀, ν₁, hν₀, hw₀, ha₀, hmin, hν₁, hw₁, ha₁, hne, hgap⟩ :=
    exists_near_min_active_aevalWeight_of_relation
      F Q hbactive hQint hrel hνw hww haw
  have hgapB : ν₁.sum (fun i k => (k : ℝ) * b i) <
      ν₀.sum (fun i k => (k : ℝ) * b i) + Real.log (P + 1) := by
    simpa [P, Amass, E, O, hDmax] using hgap
  have hlogBound : Real.log (P + 1) ≤ (C : ℝ) * Real.log ((q : ℝ) + 2) := by
    have := log_polynomial_mass_le_mul_log hAmass.le hlevel (hQlarge q hqlarge)
    simpa [P, C, Amass, E] using this
  have count_eq_one (ν : ℕ →₀ ℕ)
      (hν : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n)) :
      ν.sum (fun _ k => k) = 1 := by
    have hcountle := appearing_atom_count_le Q hν
    change ν.sum (fun _ k => k) ≤ magnitudeMaxJetDegree n Q at hcountle
    rw [hDegreeOne] at hcountle
    rcases hcountle.eq_or_lt with heq | hlt
    · exact heq
    · have hcountZero : ν.sum (fun _ k => k) = 0 := by omega
      have hsupport := appearing_atom_support_nonempty_of_maxX_lt_level Q hν
        (by simpa [Z] using hNZ)
      obtain ⟨i, hi⟩ := hsupport
      have hiBound := finsupp_apply_le_count ν i
      rw [hcountZero] at hiBound
      exact False.elim ((Finsupp.mem_support_iff.mp hi) (Nat.eq_zero_of_le_zero hiBound))
  have hν₀count := count_eq_one ν₀ hν₀
  have hν₁count := count_eq_one ν₁ hν₁
  have confined_one (ν : ℕ →₀ ℕ)
      (hν : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n))
      (hcountOne : ν.sum (fun _ k => k) = 1) :
      ∀ i, ν i ≠ 0 → q - K ≤ i ∧ i ≤ q + K := by
    let t : Fin 1 → ℕ := tupleOfFinsupp ν 1 hcountOne
    obtain ⟨m, hm, hmD, hinv⟩ := appearing_atom_sum_add_shiftCode Q hν
    have hmTop : jetMonomialDegree n m = magnitudeMaxJetDegree n Q := by
      rw [hmD, hcountOne, hDegreeOne]
    have hcodele := haMax m hm hmTop
    have hwitinv := witness_sum_add_shiftCode Q ha δ N rfl (hqJ.trans hqsum)
    have hsumt := sum_tupleOfFinsupp ν 1 hcountOne
    have hsEq : (∑ i, s i) = D * q + ∑ i, δ i := by
      simp [s, D, Finset.sum_add_distrib]
    change ν.sum (fun i k => i * k) + magnitudeShiftCode n Q m = N + O at hinv
    change (∑ i, s i) + Csum = N + O at hwitinv
    change magnitudeShiftCode n Q m ≤ Csum at hcodele
    have hbounds : q + (∑ i, δ i) ≤ ∑ i, t i ∧
        (∑ i, t i) ≤ q + (∑ i, δ i) + Csum := by
      rw [hsumt]
      have hsEqOne : (∑ i, s i) = q + ∑ i, δ i := by
        rw [hsEq, hDone]
        simp
      rw [hsEqOne] at hwitinv
      omega
    have hwindow : tupleInWindow q K t := by
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      have hsumone : (∑ j, t j) = t 0 := by simp
      dsimp [K]
      rw [hsumone] at hbounds
      omega
    exact support_window_of_key_tupleInWindow t hwindow
      (key_tupleOfFinsupp ν 1 hcountOne)
  have hν₀window := confined_one ν₀ hν₀ hν₀count
  have hν₁window := confined_one ν₁ hν₁ hν₁count
  have valEq_of_window (ν : ℕ →₀ ℕ)
      (hwindow : ∀ i, ν i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) :
      ν.sum (fun i k => (k : ℝ) * b i) =
        ν.sum (fun i k => (k : ℝ) * p i) := by
    rw [Finsupp.sum, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hlow := (hwindow i (Finsupp.mem_support_iff.mp hi)).1
    rw [hbtail i (by omega)]
  have hval₀ := valEq_of_window ν₀ hν₀window
  have hval₁ := valEq_of_window ν₁ hν₁window
  have hmin01 := hmin ν₁ hν₁ hw₁ ha₁
  rw [hval₀, hval₁] at hmin01
  rw [hval₀, hval₁] at hgapB
  have hdiff0 : 0 ≤ ν₁.sum (fun i k => (k : ℝ) * p i) -
      ν₀.sum (fun i k => (k : ℝ) * p i) := sub_nonneg.mpr hmin01
  have hdiff : ν₁.sum (fun i k => (k : ℝ) * p i) -
        ν₀.sum (fun i k => (k : ℝ) * p i) <
      (C : ℝ) * Real.log ((q : ℝ) + 2) := by
    have : ν₁.sum (fun i k => (k : ℝ) * p i) -
        ν₀.sum (fun i k => (k : ℝ) * p i) < Real.log (P + 1) := by
      linarith
    exact this.trans_le hlogBound
  simpa only [p] using ⟨ν₀, ν₁, hne.symm, hν₀count, hν₁count,
    hν₀window, hν₁window, hdiff0, hdiff⟩

/-- Every positive-degree integer-normalized ADE relation for an exact polynomial power
log-magnitude profile has two distinct top-degree atoms in one fixed window with logarithmic
valuation defect at every sufficiently large balanced scale. -/
theorem exists_eventually_polynomialPower_bend_pair_of_positiveJetDegree
    {β B : ℝ} (hβ : 2 < β) (hB : 0 < B)
    {n : ℕ} (F : PowerSeries ℂ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ = Real.exp (-(B * (i : ℝ) ^ β)))
    (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hrel : aeval (formalJets n F) Q = 0)
    (hDpos : 0 < magnitudeMaxJetDegree n Q) :
    ∃ D K C Q₀ : ℕ,
      D = magnitudeMaxJetDegree n Q ∧ 0 < D ∧ 0 < C ∧ ∀ q ≥ Q₀,
      ∃ ν₀ ν₁ : ℕ →₀ ℕ,
        ν₀ ≠ ν₁ ∧
        ν₀.sum (fun _ k => k) = D ∧ ν₁.sum (fun _ k => k) = D ∧
        (∀ i, ν₀ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        (∀ i, ν₁ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        0 ≤ ν₁.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) -
          ν₀.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) ∧
        ν₁.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) -
            ν₀.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) <
          (C : ℝ) * Real.log ((q : ℝ) + 2) :=
  exists_eventually_polynomialPower_bend_pair_of_eventual_profile (T := 0) hβ hB F
    (fun i _ => hb i) Q hQint hrel hDpos

/-- An integer ADE relation for a polynomial power profile with exponent greater than two forces
one fixed recurrent Prouhet pair whose first surviving moment is at least `ceil β` and at most the
relation's total jet degree. -/
theorem exists_recurrentProuhetLock_of_polynomialPower_relation
    {β B : ℝ} (hβ : 2 < β) (hB : 0 < B)
    {n : ℕ} (F : PowerSeries ℂ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ = Real.exp (-(B * (i : ℝ) ^ β)))
    (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hrel : aeval (formalJets n F) Q = 0)
    (hDpos : 0 < magnitudeMaxJetDegree n Q) :
    ∃ (K C μ : ℕ)
        (p₀ p₁ : Fin (2 * K + 1) → Fin (magnitudeMaxJetDegree n Q + 1))
        (Qlock : Polynomial ℤ) (q : ℕ → ℕ),
      0 < C ∧ Nat.ceil β ≤ μ ∧ μ ≤ magnitudeMaxJetDegree n Q ∧
      p₀ ≠ p₁ ∧
      (∑ j, (p₀ j : ℕ)) = magnitudeMaxJetDegree n Q ∧
      (∑ j, (p₁ j : ℕ)) = magnitudeMaxJetDegree n Q ∧
      (∑ j : Fin (2 * K + 1), (j : ℕ) * (p₀ j : ℕ)) =
        ∑ j : Fin (2 * K + 1), (j : ℕ) * (p₁ j : ℕ) ∧
      Qlock = atomPatternDifferencePolynomial p₀ p₁ ∧ Qlock ≠ 0 ∧
      (Polynomial.X - 1) ^ μ ∣ Qlock ∧
      Tendsto q atTop atTop ∧
      ∀ k,
        0 ≤ B * polynomialPowerFiniteDifference β
          (polynomialRealCoeffFinsupp Qlock) (q k) ∧
        B * polynomialPowerFiniteDifference β
            (polynomialRealCoeffFinsupp Qlock) (q k) <
          (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) := by
  obtain ⟨D, K, C, Q₀, hDmax, _hD, hC, hpairs⟩ :=
    exists_eventually_polynomialPower_bend_pair_of_positiveJetDegree
      hβ hB F hb Q hQint hrel hDpos
  subst D
  have hβone : 1 < β := by linarith
  obtain ⟨μ, p₀, p₁, Qlock, q, hceil, hμD, hpne, hcount₀, hcount₁,
      hsum, hQeq, hQne, hdiv, hq, hdefect⟩ :=
    exists_recurrentProuhetLock_of_polynomialPower_bend_pairs hβone hB hpairs
  exact ⟨K, C, μ, p₀, p₁, Qlock, q, hC, hceil, hμD, hpne,
    hcount₀, hcount₁, hsum, hQeq, hQne, hdiv, hq, hdefect⟩

/-- The logarithmic bend-pair surface alone forces the ADE degree to be at least `ceil β` for
every exponent greater than one.  The stronger `β > 2` assumption is needed only to manufacture
the bounded pairs for arbitrary degree, not for this moment obstruction. -/
theorem natCeil_le_degree_of_polynomialPower_bend_pairs
    {β B : ℝ} (hB : 0 < B)
    {D K C Q₀ : ℕ}
    (hpairs : ∀ q ≥ Q₀,
      ∃ ν₀ ν₁ : ℕ →₀ ℕ,
        ν₀ ≠ ν₁ ∧
        ν₀.sum (fun _ k => k) = D ∧ ν₁.sum (fun _ k => k) = D ∧
        (∀ i, ν₀ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        (∀ i, ν₁ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        0 ≤ ν₁.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) -
          ν₀.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) ∧
        ν₁.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) -
            ν₀.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) <
          (C : ℝ) * Real.log ((q : ℝ) + 2)) :
    Nat.ceil β ≤ D := by
  obtain ⟨p₀, p₁, hpne, hcount₀, hcount₁, q, hq, hdefect⟩ :=
    exists_persistent_atomWindow_resonance hpairs
  let Qlock := atomPatternDifferencePolynomial p₀ p₁
  let d := polynomialRealCoeffFinsupp Qlock
  obtain ⟨μ, hμD, hcancel, hmoment⟩ :=
    exists_first_atomPatternDifference_moment p₀ p₁ hpne hcount₀ hcount₁
  have hdefect' : ∀ k,
      0 ≤ B * polynomialPowerFiniteDifference β d (q k) ∧
      B * polynomialPowerFiniteDifference β d (q k) <
        (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) := by
    intro k
    have hsum : B * polynomialPowerFiniteDifference β d (q k) =
        ∑ j : Fin (2 * K + 1),
          ((((p₁ j : ℕ) : ℤ) - ((p₀ j : ℕ) : ℤ) : ℤ) : ℝ) *
            (B * ((q k + (j : ℕ) : ℕ) : ℝ) ^ β) := by
      change B * polynomialPowerFiniteDifference β
        (polynomialRealCoeffFinsupp (atomPatternDifferencePolynomial p₀ p₁)) (q k) = _
      rw [polynomialPowerFiniteDifference_polynomialRealCoeffFinsupp]
      have hbase := sum_range_atomPatternDifferencePolynomial (by omega) p₀ p₁
        (fun n => (n : ℝ) ^ β) (q k)
      have hbase' :
          (∑ r ∈ Finset.range ((atomPatternDifferencePolynomial p₀ p₁).natDegree + 1),
            ((atomPatternDifferencePolynomial p₀ p₁).coeff r : ℝ) *
              ((q k : ℝ) + (r : ℝ)) ^ β) =
          ∑ j : Fin (2 * K + 1),
            ((((p₁ j : ℕ) : ℤ) - ((p₀ j : ℕ) : ℤ) : ℤ) : ℝ) *
              ((q k + (j : ℕ) : ℕ) : ℝ) ^ β := by
        simpa only [Nat.cast_add] using hbase
      rw [hbase', Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum]
    simpa only [Nat.cast_add] using hdefect k
  exact (natCeil_le_firstMoment_of_polynomialPower_log_defect
    hB hcancel hmoment hq C K hdefect').trans hμD

/-- When the maximal jet degree is one, grading alone confines every nonzero large-level atom to
a fixed window.  Thus the ADE bend law yields bounded degree-one pairs for every power exponent. -/
theorem exists_eventually_polynomialPower_bend_pair_of_jetDegree_one
    {β B : ℝ}
    {n : ℕ} (F : PowerSeries ℂ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ = Real.exp (-(B * (i : ℝ) ^ β)))
    (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hrel : aeval (formalJets n F) Q = 0)
    (hDegreeOne : magnitudeMaxJetDegree n Q = 1) :
    ∃ K C Q₀ : ℕ, 0 < C ∧ ∀ q ≥ Q₀,
      ∃ ν₀ ν₁ : ℕ →₀ ℕ,
        ν₀ ≠ ν₁ ∧
        ν₀.sum (fun _ k => k) = 1 ∧ ν₁.sum (fun _ k => k) = 1 ∧
        (∀ i, ν₀ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        (∀ i, ν₁ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        0 ≤ ν₁.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) -
          ν₀.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) ∧
        ν₁.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) -
            ν₀.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ β)) <
          (C : ℝ) * Real.log ((q : ℝ) + 2) :=
  exists_eventually_polynomialPower_bend_pair_of_eventual_profile_jetDegree_one (T := 0) F
    (fun i _ => hb i) Q hQint hrel hDegreeOne

/-- Every positive-degree integer ADE relation for an exact polynomial power profile has total
jet degree at least `ceil β`. -/
theorem natCeil_le_magnitudeMaxJetDegree_of_polynomialPower_relation
    {β B : ℝ} (hB : 0 < B)
    {n : ℕ} (F : PowerSeries ℂ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ = Real.exp (-(B * (i : ℝ) ^ β)))
    (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hrel : aeval (formalJets n F) Q = 0)
    (hDpos : 0 < magnitudeMaxJetDegree n Q) :
    Nat.ceil β ≤ magnitudeMaxJetDegree n Q := by
  by_cases hβtwo : 2 < β
  · obtain ⟨K, C, μ, p₀, p₁, Qlock, q, hC, hceil, hμD, _⟩ :=
      exists_recurrentProuhetLock_of_polynomialPower_relation
        hβtwo hB F hb Q hQint hrel hDpos
    exact hceil.trans hμD
  · have hβle : β ≤ 2 := le_of_not_gt hβtwo
    by_cases hDtwo : 2 ≤ magnitudeMaxJetDegree n Q
    · have hceilTwo : Nat.ceil β ≤ 2 := Nat.ceil_le.mpr hβle
      exact hceilTwo.trans hDtwo
    · have hDegreeOne : magnitudeMaxJetDegree n Q = 1 := by omega
      obtain ⟨K, C, Q₀, hC, hpairs⟩ :=
        exists_eventually_polynomialPower_bend_pair_of_jetDegree_one
          F hb Q hQint hrel hDegreeOne
      have hceilOne := natCeil_le_degree_of_polynomialPower_bend_pairs
        (D := 1) (K := K) (C := C) (Q₀ := Q₀) hB hpairs
      simpa [hDegreeOne] using hceilOne

/-- The set of maximal total jet degrees of all nonzero integer-coefficient formal ADE relations
annihilating `F`. -/
def integerADERelationDegrees (F : PowerSeries ℂ) : Set ℕ :=
  {D | ∃ (n : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ),
    Q ≠ 0 ∧
    (∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ)) ∧
    aeval (formalJets n F) Q = 0 ∧
    magnitudeMaxJetDegree n Q = D}

/-- Least integer ADE total jet degree.  It is zero only when no integer ADE exists; Mahler
normalization makes the relation-degree set nonempty for every differentially algebraic series. -/
def integerADEDegree (F : PowerSeries ℂ) : ℕ :=
  sInf (integerADERelationDegrees F)

theorem integerADERelationDegrees_nonempty_of_relation
    {F : PowerSeries ℂ} {n : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    (hQ : Q ≠ 0)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hrel : aeval (formalJets n F) Q = 0) :
    (integerADERelationDegrees F).Nonempty := by
  exact ⟨magnitudeMaxJetDegree n Q, n, Q, hQ, hQint, hrel, rfl⟩

/-- Exact formal-series degree floor: the least integer ADE degree is at least `ceil β`. -/
theorem natCeil_le_integerADEDegree_of_polynomialPower
    {F : PowerSeries ℂ} {β B : ℝ} (hB : 0 < B)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ = Real.exp (-(B * (i : ℝ) ^ β)))
    (hne : (integerADERelationDegrees F).Nonempty) :
    Nat.ceil β ≤ integerADEDegree F := by
  have hminmem := Nat.sInf_mem hne
  change ∃ (n : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ),
    Q ≠ 0 ∧
    (∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ)) ∧
    aeval (formalJets n F) Q = 0 ∧
    magnitudeMaxJetDegree n Q = integerADEDegree F at hminmem
  obtain ⟨n, Q, hQ, hQint, hrel, hdegree⟩ := hminmem
  have hDpos := magnitudeMaxJetDegree_pos_of_integer_relation
    F hb Q hQ hQint hrel
  have hfloor := natCeil_le_magnitudeMaxJetDegree_of_polynomialPower_relation
    hB F hb Q hQint hrel hDpos
  simpa [hdegree] using hfloor

theorem integerADERelationDegrees_nonempty_of_differentiallyAlgebraic
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    (hDA : DifferentiallyAlgebraic f) :
    (integerADERelationDegrees (taylorPS f)).Nonempty := by
  obtain ⟨n, P, hP, hPfun⟩ := hDA
  have hjz : jetFun f n P = 0 := by
    funext z
    exact hPfun z
  have hformal : aeval (formalJets n (taylorPS f)) P = 0 := by
    rw [← taylorPS_jetFun f n hf P, hjz,
      show (0 : ℂ → ℂ) = fun _ => (0 : ℂ) from rfl, taylorPS_const, map_zero]
  obtain ⟨n', Q, hQ, hQint, hrel⟩ := formal_mahler_integer_normalization hP hformal
  exact integerADERelationDegrees_nonempty_of_relation hQ hQint hrel

/-- Analytic DA degree floor for exact polynomial Taylor log-magnitudes. -/
theorem natCeil_le_integerADEDegree_of_differentiallyAlgebraic_polynomialPower
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {β B : ℝ} (hB : 0 < B)
    (hb : ∀ i, ‖PowerSeries.coeff i (taylorPS f)‖ =
      Real.exp (-(B * (i : ℝ) ^ β)))
    (hDA : DifferentiallyAlgebraic f) :
    Nat.ceil β ≤ integerADEDegree (taylorPS f) := by
  exact natCeil_le_integerADEDegree_of_polynomialPower hB hb
    (integerADERelationDegrees_nonempty_of_differentiallyAlgebraic hf hDA)

/-- A nonzero integer formal relation has positive jet degree even when the coefficient profile is
only specified at nonzero coefficients.  In degree zero the unique atom is `0`, whose coefficient
product is `1`, so the active-support survival theorem applies. -/
theorem magnitudeMaxJetDegree_pos_of_integer_relation_on_active_support
    {b : ℕ → ℝ} {n : ℕ} (F : PowerSeries ℂ)
    (hb : ∀ i, PowerSeries.coeff i F ≠ 0 →
      ‖PowerSeries.coeff i F‖ = Real.exp (-b i))
    (Q : MvPolynomial (Fin (n + 2)) ℂ) (hQ : Q ≠ 0)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hrel : aeval (formalJets n F) Q = 0) :
    0 < magnitudeMaxJetDegree n Q := by
  rcases Nat.eq_zero_or_pos (magnitudeMaxJetDegree n Q) with hzero | hpos
  · obtain ⟨N, ν₀, G, hν₀, hw₀, hgap, hmass⟩ :=
      exists_intDominance_of_zeroJetDegree (b := b) Q hQ hzero
    have hcount := appearing_atom_count_le Q hν₀
    rw [hzero] at hcount
    have hν₀zero : ν₀ = 0 := by
      ext i
      have hi := finsupp_apply_le_count ν₀ i
      have hcountZero : ν₀.sum (fun _ k => k) = 0 := Nat.eq_zero_of_le_zero hcount
      rw [hcountZero] at hi
      simpa using Nat.eq_zero_of_le_zero hi
    have ha₀ : ν₀.prod (fun i k => (PowerSeries.coeff i F) ^ k) ≠ 0 := by
      rw [hν₀zero]
      simp
    have hne := aeval_coeff_ne_zero_of_int_dominant_on_active_support
      n N F Q hb hQint ν₀ hν₀ hw₀ ha₀
      (fun ν hν hw ha hne => hgap ν hν hw hne) hmass
    rw [hrel, map_zero] at hne
    exact False.elim (hne rfl)
  · exact hpos

/-- Every integer ADE for an eventual polynomial-power profile with exponent greater than two
forces one recurrent fixed Prouhet lock, with multiplicity bounded below by `ceil β` and above by
the ADE jet degree. -/
theorem exists_recurrentProuhetLock_of_eventual_polynomialPower_relation
    {β B : ℝ} (hβ : 2 < β) (hB : 0 < B)
    {n T : ℕ} (F : PowerSeries ℂ)
    (htail : ∀ i ≥ T, ‖PowerSeries.coeff i F‖ =
      Real.exp (-(B * (i : ℝ) ^ β)))
    (Q : MvPolynomial (Fin (n + 2)) ℂ) (hQ : Q ≠ 0)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hrel : aeval (formalJets n F) Q = 0) :
    ∃ (K C μ : ℕ)
        (p₀ p₁ : Fin (2 * K + 1) → Fin (magnitudeMaxJetDegree n Q + 1))
        (Qlock : Polynomial ℤ) (q : ℕ → ℕ),
      0 < C ∧ Nat.ceil β ≤ μ ∧ μ ≤ magnitudeMaxJetDegree n Q ∧
      p₀ ≠ p₁ ∧
      (∑ j, (p₀ j : ℕ)) = magnitudeMaxJetDegree n Q ∧
      (∑ j, (p₁ j : ℕ)) = magnitudeMaxJetDegree n Q ∧
      (∑ j : Fin (2 * K + 1), (j : ℕ) * (p₀ j : ℕ)) =
        ∑ j : Fin (2 * K + 1), (j : ℕ) * (p₁ j : ℕ) ∧
      Qlock = atomPatternDifferencePolynomial p₀ p₁ ∧ Qlock ≠ 0 ∧
      (Polynomial.X - 1) ^ μ ∣ Qlock ∧ Tendsto q atTop atTop ∧
      ∀ k,
        0 ≤ B * polynomialPowerFiniteDifference β
          (polynomialRealCoeffFinsupp Qlock) (q k) ∧
        B * polynomialPowerFiniteDifference β
            (polynomialRealCoeffFinsupp Qlock) (q k) <
          (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) := by
  let b := eventualPolynomialPowerValuation F T B β
  have hbactive : ∀ i, PowerSeries.coeff i F ≠ 0 →
      ‖PowerSeries.coeff i F‖ = Real.exp (-b i) := by
    intro i hi
    simpa [b] using
      norm_coeff_eq_exp_eventualPolynomialPowerValuation_of_ne htail i hi
  have hDpos := magnitudeMaxJetDegree_pos_of_integer_relation_on_active_support
    F hbactive Q hQ hQint hrel
  obtain ⟨D, K, C, Q₀, hDmax, _hD, hC, hpairs⟩ :=
    exists_eventually_polynomialPower_bend_pair_of_eventual_profile
      hβ hB F htail Q hQint hrel hDpos
  subst D
  have hβone : 1 < β := by linarith
  obtain ⟨μ, p₀, p₁, Qlock, q, hceil, hμD, hpne, hcount₀, hcount₁,
      hsum, hQeq, hQne, hdiv, hq, hdefect⟩ :=
    exists_recurrentProuhetLock_of_polynomialPower_bend_pairs hβone hB hpairs
  exact ⟨K, C, μ, p₀, p₁, Qlock, q, hC, hceil, hμD, hpne,
    hcount₀, hcount₁, hsum, hQeq, hQne, hdiv, hq, hdefect⟩

/-- Relation-level ADE degree floor for an eventual polynomial-power coefficient profile. -/
theorem natCeil_le_magnitudeMaxJetDegree_of_eventual_polynomialPower_relation
    {β B : ℝ} (hB : 0 < B)
    {n T : ℕ} (F : PowerSeries ℂ)
    (htail : ∀ i ≥ T, ‖PowerSeries.coeff i F‖ =
      Real.exp (-(B * (i : ℝ) ^ β)))
    (Q : MvPolynomial (Fin (n + 2)) ℂ) (hQ : Q ≠ 0)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hrel : aeval (formalJets n F) Q = 0) :
    Nat.ceil β ≤ magnitudeMaxJetDegree n Q := by
  let b := eventualPolynomialPowerValuation F T B β
  have hbactive : ∀ i, PowerSeries.coeff i F ≠ 0 →
      ‖PowerSeries.coeff i F‖ = Real.exp (-b i) := by
    intro i hi
    simpa [b] using
      norm_coeff_eq_exp_eventualPolynomialPowerValuation_of_ne htail i hi
  have hDpos := magnitudeMaxJetDegree_pos_of_integer_relation_on_active_support
    F hbactive Q hQ hQint hrel
  by_cases hβtwo : 2 < β
  · obtain ⟨K, C, μ, p₀, p₁, Qlock, q, hC, hceil, hμD, _⟩ :=
      exists_recurrentProuhetLock_of_eventual_polynomialPower_relation
        hβtwo hB F htail Q hQ hQint hrel
    exact hceil.trans hμD
  · have hβle : β ≤ 2 := le_of_not_gt hβtwo
    by_cases hDtwo : 2 ≤ magnitudeMaxJetDegree n Q
    · exact (Nat.ceil_le.mpr hβle).trans hDtwo
    · have hDegreeOne : magnitudeMaxJetDegree n Q = 1 := by omega
      obtain ⟨K, C, Q₀, hC, hpairs⟩ :=
        exists_eventually_polynomialPower_bend_pair_of_eventual_profile_jetDegree_one
          F htail Q hQint hrel hDegreeOne
      have hceilOne := natCeil_le_degree_of_polynomialPower_bend_pairs
        (D := 1) (K := K) (C := C) (Q₀ := Q₀) hB hpairs
      simpa [hDegreeOne] using hceilOne

/-- Eventual-profile formal-series floor for the least integer ADE degree. -/
theorem natCeil_le_integerADEDegree_of_eventual_polynomialPower
    {F : PowerSeries ℂ} {β B : ℝ} (hB : 0 < B)
    (htail : ∀ᶠ i : ℕ in atTop,
      ‖PowerSeries.coeff i F‖ = Real.exp (-(B * (i : ℝ) ^ β)))
    (hne : (integerADERelationDegrees F).Nonempty) :
    Nat.ceil β ≤ integerADEDegree F := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp htail
  have hminmem := Nat.sInf_mem hne
  change ∃ (n : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ),
    Q ≠ 0 ∧
    (∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ)) ∧
    aeval (formalJets n F) Q = 0 ∧
    magnitudeMaxJetDegree n Q = integerADEDegree F at hminmem
  obtain ⟨n, Q, hQ, hQint, hrel, hdegree⟩ := hminmem
  have hfloor := natCeil_le_magnitudeMaxJetDegree_of_eventual_polynomialPower_relation
    hB F hT Q hQ hQint hrel
  simpa [hdegree] using hfloor

/-- Analytic DA degree floor for the card's eventual Taylor-magnitude hypothesis. -/
theorem natCeil_le_integerADEDegree_of_differentiallyAlgebraic_eventual_polynomialPower
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {β B : ℝ} (hB : 0 < B)
    (htail : ∀ᶠ i : ℕ in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ =
        Real.exp (-(B * (i : ℝ) ^ β)))
    (hDA : DifferentiallyAlgebraic f) :
    Nat.ceil β ≤ integerADEDegree (taylorPS f) := by
  exact natCeil_le_integerADEDegree_of_eventual_polynomialPower hB htail
    (integerADERelationDegrees_nonempty_of_differentiallyAlgebraic hf hDA)

/-- No integer ADE whose total jet degree lies below `ceil β` can annihilate an eventual
polynomial-power profile. -/
theorem no_integerADERelation_below_natCeil_of_eventual_polynomialPower
    {F : PowerSeries ℂ} {β B : ℝ} (hB : 0 < B)
    (htail : ∀ᶠ i : ℕ in atTop,
      ‖PowerSeries.coeff i F‖ = Real.exp (-(B * (i : ℝ) ^ β))) :
    ¬ ∃ (n : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ),
      Q ≠ 0 ∧
      (∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ)) ∧
      aeval (formalJets n F) Q = 0 ∧
      magnitudeMaxJetDegree n Q < Nat.ceil β := by
  rintro ⟨n, Q, hQ, hQint, hrel, hlt⟩
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp htail
  have hfloor := natCeil_le_magnitudeMaxJetDegree_of_eventual_polynomialPower_relation
    hB F hT Q hQ hQint hrel
  omega

lemma natCeil_pi_eq_four : Nat.ceil Real.pi = 4 := by
  rw [Nat.ceil_eq_iff (by omega : (4 : ℕ) ≠ 0)]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub]
  exact ⟨Real.pi_gt_three, Real.pi_lt_four.le⟩

/-- The `exp (-n^π)` family admits no integer ADE of total jet degree at most three, for any
choice of coefficient phases and any finite prefix. -/
theorem no_integerADERelation_degree_le_three_of_eventual_piPower
    {F : PowerSeries ℂ}
    (htail : ∀ᶠ i : ℕ in atTop,
      ‖PowerSeries.coeff i F‖ = Real.exp (-((i : ℝ) ^ Real.pi))) :
    ¬ ∃ (n : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ),
      Q ≠ 0 ∧
      (∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ)) ∧
      aeval (formalJets n F) Q = 0 ∧
      magnitudeMaxJetDegree n Q ≤ 3 := by
  rintro ⟨n, Q, hQ, hQint, hrel, hle⟩
  have htail' : ∀ᶠ i : ℕ in atTop,
      ‖PowerSeries.coeff i F‖ =
        Real.exp (-((1 : ℝ) * (i : ℝ) ^ Real.pi)) := by
    simpa using htail
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp htail'
  have hfloor := natCeil_le_magnitudeMaxJetDegree_of_eventual_polynomialPower_relation
    (B := (1 : ℝ)) (β := Real.pi) one_pos F hT Q hQ hQint hrel
  rw [natCeil_pi_eq_four] at hfloor
  omega

/-- If an eventual `exp (-n^π)` phase realization is DA, its least integer ADE degree is at least
four. -/
theorem four_le_integerADEDegree_of_differentiallyAlgebraic_eventual_piPower
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    (htail : ∀ᶠ i : ℕ in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ =
        Real.exp (-((i : ℝ) ^ Real.pi)))
    (hDA : DifferentiallyAlgebraic f) :
    4 ≤ integerADEDegree (taylorPS f) := by
  have htail' : ∀ᶠ i : ℕ in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ =
        Real.exp (-((1 : ℝ) * (i : ℝ) ^ Real.pi)) := by
    simpa using htail
  have hfloor :=
    natCeil_le_integerADEDegree_of_differentiallyAlgebraic_eventual_polynomialPower
      hf (B := (1 : ℝ)) (β := Real.pi) one_pos htail' hDA
  simpa [natCeil_pi_eq_four] using hfloor

/-- Along any family whose polynomial decay exponents tend to infinity, the least integer ADE
degrees tend to infinity whenever the relation-degree sets are nonempty. -/
theorem tendsto_integerADEDegree_of_eventual_polynomialPower_family
    (F : ℕ → PowerSeries ℂ) (B β : ℕ → ℝ)
    (hB : ∀ r, 0 < B r)
    (hβ : Tendsto β atTop atTop)
    (htail : ∀ r, ∀ᶠ i : ℕ in atTop,
      ‖PowerSeries.coeff i (F r)‖ =
        Real.exp (-(B r * (i : ℝ) ^ β r)))
    (hne : ∀ r, (integerADERelationDegrees (F r)).Nonempty) :
    Tendsto (fun r => integerADEDegree (F r)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro d
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp
    (hβ.eventually_ge_atTop (d : ℝ))
  refine ⟨R, fun r hr => ?_⟩
  have hdceil : d ≤ Nat.ceil (β r) := by
    exact_mod_cast (hR r hr).trans (Nat.le_ceil (β r))
  exact hdceil.trans
    (natCeil_le_integerADEDegree_of_eventual_polynomialPower
      (hB r) (htail r) (hne r))

end

end GaloisForLFunctions
