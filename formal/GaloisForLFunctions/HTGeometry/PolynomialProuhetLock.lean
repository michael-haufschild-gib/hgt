import GaloisForLFunctions.HTGeometry.PolynomialPowerFiniteDifference
import GaloisForLFunctions.HTGeometry.HierarchicalResonanceBreaking
import GaloisForLFunctions.HTGeometry.ProuhetMomentDivisibility

open Filter Finset PowerSeries MvPolynomial Polynomial Topology Asymptotics Set

namespace GaloisForLFunctions

noncomputable section

/-- The multiplicity key encoded by a finite atom-window pattern. -/
def atomPatternKey {M D : ℕ} (p : Fin M → Fin (D + 1)) : ℕ →₀ ℕ :=
  ∑ j : Fin M, Finsupp.single (j : ℕ) (p j : ℕ)

theorem atomPatternKey_apply {M D : ℕ} (p : Fin M → Fin (D + 1)) (r : ℕ) :
    atomPatternKey p r = if h : r < M then (p ⟨r, h⟩ : ℕ) else 0 := by
  classical
  rw [atomPatternKey, Finsupp.finsetSum_apply]
  split_ifs with hr
  · rw [Finset.sum_eq_single ⟨r, hr⟩]
    · simp
    · intro j hj hne
      simp only [Finsupp.single_apply]
      split_ifs with heq
      · exact (hne (Fin.ext heq)).elim
      · rfl
    · simp
  · apply Finset.sum_eq_zero
    intro j hj
    simp only [Finsupp.single_apply]
    split_ifs with heq
    · exact (hr (heq ▸ j.isLt)).elim
    · rfl

theorem atomPatternKey_count {M D : ℕ} (p : Fin M → Fin (D + 1)) :
    (atomPatternKey p).sum (fun _ k => k) = ∑ j, (p j : ℕ) := by
  classical
  rw [atomPatternKey, ← Finsupp.sum_finsetSum_index (s := Finset.univ)
    (g := fun j : Fin M => Finsupp.single (j : ℕ) (p j : ℕ))
    (h := fun _ k => k)]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finsupp.sum_single_index]
    simp
  · intro a
    simp
  · intro a b c
    simp

theorem atomPatternKey_injective {M D : ℕ} :
    Function.Injective (atomPatternKey : (Fin M → Fin (D + 1)) → ℕ →₀ ℕ) := by
  intro p q hpq
  funext j
  apply Fin.ext
  have h := Finsupp.ext_iff.mp hpq (j : ℕ)
  simpa [atomPatternKey_apply] using h

theorem tupleDifference_apply_eq_key_sub {D r : ℕ} (u v : Fin D → ℕ) :
    tupleDifference u v r = ((key u r : ℕ) : ℝ) - ((key v r : ℕ) : ℝ) := by
  classical
  simp only [tupleDifference, key, Finsupp.sub_apply, Finsupp.finsetSum_apply,
    Finsupp.single_apply]
  push_cast
  ring

/-- The real coefficient stencil of a pattern-difference polynomial is exactly the difference
of any two tuples enumerating the two multiplicity keys. -/
theorem polynomialRealCoeffFinsupp_atomPatternDifferencePolynomial
    {M D : ℕ} (p₀ p₁ : Fin M → Fin (D + 1))
    (hcount₀ : (∑ j, (p₀ j : ℕ)) = D)
    (hcount₁ : (∑ j, (p₁ j : ℕ)) = D) :
    polynomialRealCoeffFinsupp (atomPatternDifferencePolynomial p₀ p₁) =
      tupleDifference
        (tupleOfFinsupp (atomPatternKey p₁) D
          (by simpa [atomPatternKey_count] using hcount₁))
        (tupleOfFinsupp (atomPatternKey p₀) D
          (by simpa [atomPatternKey_count] using hcount₀)) := by
  classical
  ext r
  rw [polynomialRealCoeffFinsupp_apply,
    atomPatternDifferencePolynomial_coeff, tupleDifference_apply_eq_key_sub,
    key_tupleOfFinsupp, key_tupleOfFinsupp]
  rw [atomPatternKey_apply, atomPatternKey_apply]
  split_ifs <;> push_cast <;> ring

/-- Two distinct `D`-element atom patterns have a first nonzero power moment of order at most
`D`.  This is the sharp Newton bound behind the ADE degree floor. -/
theorem exists_first_atomPatternDifference_moment
    {M D : ℕ} (p₀ p₁ : Fin M → Fin (D + 1))
    (hne : p₀ ≠ p₁)
    (hcount₀ : (∑ j, (p₀ j : ℕ)) = D)
    (hcount₁ : (∑ j, (p₁ j : ℕ)) = D) :
    ∃ μ ≤ D,
      (∀ k < μ, stretchedMoment
        (polynomialRealCoeffFinsupp (atomPatternDifferencePolynomial p₀ p₁)) k = 0) ∧
      stretchedMoment
        (polynomialRealCoeffFinsupp (atomPatternDifferencePolynomial p₀ p₁)) μ ≠ 0 := by
  let ν₀ := atomPatternKey p₀
  let ν₁ := atomPatternKey p₁
  have hν₀count : ν₀.sum (fun _ k => k) = D := by
    simpa [ν₀, atomPatternKey_count] using hcount₀
  have hν₁count : ν₁.sum (fun _ k => k) = D := by
    simpa [ν₁, atomPatternKey_count] using hcount₁
  let u := tupleOfFinsupp ν₁ D hν₁count
  let v := tupleOfFinsupp ν₀ D hν₀count
  have hkey : key u ≠ key v := by
    rw [show key u = ν₁ by exact key_tupleOfFinsupp _ _ _,
      show key v = ν₀ by exact key_tupleOfFinsupp _ _ _]
    exact fun h => hne (atomPatternKey_injective (by simpa [ν₀, ν₁] using h.symm))
  obtain ⟨μ, hμD, hcancel, hmoment⟩ := exists_first_stretchedMoment_ne u v hkey
  refine ⟨μ, hμD, ?_, ?_⟩
  · intro k hk
    rw [polynomialRealCoeffFinsupp_atomPatternDifferencePolynomial p₀ p₁
      hcount₀ hcount₁]
    exact hcancel k hk
  · rw [polynomialRealCoeffFinsupp_atomPatternDifferencePolynomial p₀ p₁
      hcount₀ hcount₁]
    exact hmoment

/-- Vanishing real coefficient moments lift back through the injective integer cast and force
the corresponding Prouhet divisor over `ℤ`. -/
theorem sub_one_pow_dvd_of_polynomialRealCoeff_moments
    (Q : Polynomial ℤ) (μ : ℕ)
    (hcancel : ∀ k < μ, stretchedMoment (polynomialRealCoeffFinsupp Q) k = 0) :
    (Polynomial.X - 1) ^ μ ∣ Q := by
  have hdSupport : (polynomialRealCoeffFinsupp Q).support = Q.support := by
    ext n
    simp [polynomialRealCoeffFinsupp, Polynomial.toFinsupp_apply]
  have hint : Function.Injective (Int.castRingHom ℝ) :=
    fun a b h => Int.cast_injective h
  have hmap : ((Polynomial.X - 1) ^ μ : Polynomial ℤ).map (Int.castRingHom ℝ) ∣
      Q.map (Int.castRingHom ℝ) := by
    have htarget : ((Polynomial.X - 1) ^ μ : Polynomial ℤ).map (Int.castRingHom ℝ) =
        ((Polynomial.X - 1) ^ μ : Polynomial ℝ) := by simp
    rw [htarget]
    rcases μ with _ | L
    · simp
    · apply pte_sub_one_pow_dvd_of_power_moments (L := L)
      intro j hj
      have hm := hcancel j (by omega)
      rw [stretchedMoment, Finsupp.sum, hdSupport] at hm
      rw [Polynomial.support_map_of_injective Q hint]
      simpa [Polynomial.coeff_map, mul_comm] using hm
  exact (Polynomial.map_dvd_map (Int.castRingHom ℝ) hint
    ((Polynomial.monic_X_sub_C (1 : ℤ)).pow μ)).mp hmap

lemma eventually_const_mul_log_lt_abs_polynomialPowerFiniteDifference
    {β : ℝ} (d : ℕ →₀ ℝ) (j : ℕ)
    (hcancel : ∀ k < j, stretchedMoment d k = 0)
    (hmoment : stretchedMoment d j ≠ 0)
    (hjβ : (j : ℝ) < β) {A : ℝ} (hA : 0 < A) :
    ∀ᶠ x : ℝ in atTop,
      A * Real.log x < |polynomialPowerFiniteDifference β d x| := by
  have ho := (log_isLittleO_abs_polynomialPowerFiniteDifference
    d j hcancel hmoment hjβ).const_mul_left A
  have hpoch := descPochhammer_eval_ne_zero_of_natCast_lt hjβ
  let c := polynomialPowerDifferenceCoefficient β d j
  have hc : c ≠ 0 := by
    dsimp [c, polynomialPowerDifferenceCoefficient]
    exact div_ne_zero (mul_ne_zero hmoment hpoch) (by positivity)
  have hequiv := polynomialPowerFiniteDifference_isEquivalent d j hcancel hmoment hpoch
  have hequiv' : polynomialPowerFiniteDifference β d ~[atTop]
      fun x => c * x ^ (β - j) := by simpa [c] using hequiv
  have hdiff : ∀ᶠ x : ℝ in atTop,
      0 < ‖|polynomialPowerFiniteDifference β d x|‖ := by
    rcases lt_or_gt_of_ne hc with hcneg | hcpos
    · have hleadNeg : ∀ᶠ x : ℝ in atTop, c * x ^ (β - j) < 0 := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        exact mul_neg_of_neg_of_pos hcneg (Real.rpow_pos_of_pos hx _)
      have hneg := hequiv'.eventually_neg hleadNeg
      filter_upwards [hneg] with x hx
      simpa [Real.norm_eq_abs] using (abs_pos.mpr hx.ne)
    · have hleadPos : ∀ᶠ x : ℝ in atTop, 0 < c * x ^ (β - j) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        exact mul_pos hcpos (Real.rpow_pos_of_pos hx _)
      have hpos := hequiv'.eventually_pos hleadPos
      filter_upwards [hpos] with x hx
      simpa [Real.norm_eq_abs] using (abs_pos.mpr hx.ne')
  have hlt := ho.eventuallyLT_norm_of_eventually_pos hdiff
  filter_upwards [hlt, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs,
    abs_of_pos (mul_pos hA (Real.log_pos hx1))] at hx
  exact hx

lemma eventually_log_nat_add_const_le_two_mul_log_nat (K : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (((n + K : ℕ) : ℝ) + 2) ≤ 2 * Real.log n := by
  filter_upwards [eventually_ge_atTop (max 2 (K + 2))] with n hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnK : K + 2 ≤ n := (le_max_right _ _).trans hn
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hKreal : ((K : ℝ) + 2) ≤ n := by exact_mod_cast hnK
  have hnpos : (0 : ℝ) < n := by linarith
  have hquad : ((n + K : ℕ) : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by
    push_cast
    nlinarith
  calc
    Real.log (((n + K : ℕ) : ℝ) + 2) ≤ Real.log ((n : ℝ) ^ 2) :=
      Real.log_le_log (by positivity) hquad
    _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num

/-- A logarithmically bounded real-power defect cannot have its first nonzero moment below the
power exponent. -/
theorem natCeil_le_firstMoment_of_polynomialPower_log_defect
    {β B : ℝ} (hB : 0 < B) {d : ℕ →₀ ℝ} {μ : ℕ}
    (hcancel : ∀ k < μ, stretchedMoment d k = 0)
    (hmoment : stretchedMoment d μ ≠ 0)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) (C K : ℕ)
    (hdefect : ∀ k,
      0 ≤ B * polynomialPowerFiniteDifference β d (q k) ∧
      B * polynomialPowerFiniteDifference β d (q k) <
        (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2)) :
    Nat.ceil β ≤ μ := by
  by_contra hnot
  have hμceil : μ < Nat.ceil β := Nat.lt_of_not_ge hnot
  have hμβ : (μ : ℝ) < β := Nat.lt_ceil.mp hμceil
  let A : ℝ := (2 * (C : ℝ) + 1) / B
  have hA : 0 < A := by dsimp [A]; positivity
  have hgapReal := eventually_const_mul_log_lt_abs_polynomialPowerFiniteDifference
    d μ hcancel hmoment hμβ hA
  have hqReal : Tendsto (fun k => (q k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  have hgap := hqReal.eventually hgapReal
  have hlog := hq.eventually (eventually_log_nat_add_const_le_two_mul_log_nat K)
  have hqlarge := hq.eventually (eventually_ge_atTop 2)
  obtain ⟨k, hgapk, hlogk, hqk⟩ := (hgap.and (hlog.and hqlarge)).exists
  have hqreal : (2 : ℝ) ≤ q k := by exact_mod_cast hqk
  have hlogpos : 0 < Real.log (q k) := Real.log_pos (by linarith)
  have hnonneg := (hdefect k).1
  have habs : B * |polynomialPowerFiniteDifference β d (q k)| =
      B * polynomialPowerFiniteDifference β d (q k) := by
    rw [abs_of_nonneg (nonneg_of_mul_nonneg_right hnonneg hB)]
  have hupper : B * |polynomialPowerFiniteDifference β d (q k)| <
      2 * (C : ℝ) * Real.log (q k) := by
    rw [habs]
    exact (hdefect k).2.trans_le (by
      have := mul_le_mul_of_nonneg_left hlogk (Nat.cast_nonneg C)
      nlinarith)
  have hlower : (2 * (C : ℝ) + 1) * Real.log (q k) <
      B * |polynomialPowerFiniteDifference β d (q k)| := by
    dsimp [A] at hgapk
    have := mul_lt_mul_of_pos_left hgapk hB
    field_simp [hB.ne'] at this
    simpa [mul_assoc] using this
  linarith

theorem polynomialPowerFiniteDifference_polynomialRealCoeffFinsupp
    (Q : Polynomial ℤ) (β x : ℝ) :
    polynomialPowerFiniteDifference β (polynomialRealCoeffFinsupp Q) x =
      ∑ j ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff j : ℝ) * (x + j) ^ β := by
  rw [polynomialPowerFiniteDifference, Finsupp.sum_of_support_subset
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

theorem atomPattern_weighted_sum_eq_of_moment_one
    {M D : ℕ} (hM : 0 < M) (p₀ p₁ : Fin M → Fin (D + 1))
    (hmoment : stretchedMoment
      (polynomialRealCoeffFinsupp (atomPatternDifferencePolynomial p₀ p₁)) 1 = 0) :
    (∑ j : Fin M, (j : ℕ) * (p₀ j : ℕ)) =
      ∑ j : Fin M, (j : ℕ) * (p₁ j : ℕ) := by
  have hsum := sum_range_atomPatternDifferencePolynomial hM p₀ p₁
    (fun n => (n : ℝ)) 0
  rw [stretchedMoment_polynomialRealCoeffFinsupp_eq_sum_range] at hmoment
  have hzero : ∑ j : Fin M,
      ((((p₁ j : ℕ) : ℤ) - ((p₀ j : ℕ) : ℤ) : ℤ) : ℝ) * (j : ℝ) = 0 := by
    calc
      _ = ∑ r ∈ Finset.range ((atomPatternDifferencePolynomial p₀ p₁).natDegree + 1),
          ((atomPatternDifferencePolynomial p₀ p₁).coeff r : ℝ) * ((0 + r : ℕ) : ℝ) :=
        by simpa only [zero_add] using hsum.symm
      _ = 0 := by simpa only [zero_add, pow_one] using hmoment
  have hreal : (∑ j : Fin M, (j : ℝ) * (p₀ j : ℕ)) =
      ∑ j : Fin M, (j : ℝ) * (p₁ j : ℕ) := by
    push_cast at hzero
    simp_rw [sub_mul] at hzero
    rw [Finset.sum_sub_distrib] at hzero
    simpa [mul_comm] using (sub_eq_zero.mp hzero).symm
  exact_mod_cast hreal

/-- Persistent bounded ADE bends for the profile `B n^β`, with `β > 1`, force one fixed
Prouhet pair whose root multiplicity at one lies between `ceil β` and the ADE degree. -/
theorem exists_recurrentProuhetLock_of_polynomialPower_bend_pairs
    {β B : ℝ} (hβ : 1 < β) (hB : 0 < B)
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
    ∃ (μ : ℕ) (p₀ p₁ : Fin (2 * K + 1) → Fin (D + 1))
        (Q : Polynomial ℤ) (q : ℕ → ℕ),
      Nat.ceil β ≤ μ ∧ μ ≤ D ∧
      p₀ ≠ p₁ ∧
      (∑ j, (p₀ j : ℕ)) = D ∧ (∑ j, (p₁ j : ℕ)) = D ∧
      (∑ j : Fin (2 * K + 1), (j : ℕ) * (p₀ j : ℕ)) =
        ∑ j : Fin (2 * K + 1), (j : ℕ) * (p₁ j : ℕ) ∧
      Q = atomPatternDifferencePolynomial p₀ p₁ ∧ Q ≠ 0 ∧
      (Polynomial.X - 1) ^ μ ∣ Q ∧
      Tendsto q atTop atTop ∧
      ∀ k,
        0 ≤ B * polynomialPowerFiniteDifference β (polynomialRealCoeffFinsupp Q) (q k) ∧
        B * polynomialPowerFiniteDifference β (polynomialRealCoeffFinsupp Q) (q k) <
          (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) := by
  obtain ⟨p₀, p₁, hpne, hcount₀, hcount₁, q, hq, hdefect⟩ :=
    exists_persistent_atomWindow_resonance hpairs
  let Q := atomPatternDifferencePolynomial p₀ p₁
  let d := polynomialRealCoeffFinsupp Q
  obtain ⟨μ, hμD, hcancel, hmoment⟩ :=
    exists_first_atomPatternDifference_moment p₀ p₁ hpne hcount₀ hcount₁
  have hQ : Q ≠ 0 := atomPatternDifferencePolynomial_ne_zero hpne
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
      rw [hbase']
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum]
    simpa only [Nat.cast_add] using hdefect k
  have hceilμ := natCeil_le_firstMoment_of_polynomialPower_log_defect
    hB hcancel hmoment hq C K hdefect'
  have hdiv : (Polynomial.X - 1) ^ μ ∣ Q :=
    sub_one_pow_dvd_of_polynomialRealCoeff_moments Q μ hcancel
  have honeCeil : 1 < Nat.ceil β := Nat.lt_ceil.mpr (by simpa using hβ)
  have honeμ : 1 < μ := lt_of_lt_of_le honeCeil hceilμ
  have hmomentOne : stretchedMoment d 1 = 0 := hcancel 1 honeμ
  have hweighted := atomPattern_weighted_sum_eq_of_moment_one (by omega) p₀ p₁
    (by simpa [d, Q] using hmomentOne)
  refine ⟨μ, p₀, p₁, Q, q, hceilμ, hμD, hpne, hcount₀, hcount₁,
    hweighted, rfl, hQ, hdiv, hq, ?_⟩
  simpa [d] using hdefect'

end

end GaloisForLFunctions
