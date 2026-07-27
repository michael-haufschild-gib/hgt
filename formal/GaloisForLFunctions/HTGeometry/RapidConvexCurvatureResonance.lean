import GaloisForLFunctions.HTGeometry.PolynomialPowerADEResonance
import GaloisForLFunctions.HTGeometry.PolynomialPhaseMomentGap

open Filter Finset PowerSeries MvPolynomial Polynomial Set Asymptotics Topology

namespace GaloisForLFunctions

noncomputable section

def rapidCurvature (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  b (n + 2) - 2 * b (n + 1) + b n

def rapidIncrement (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  b (n + 1) - b n

def tupleProfileValuation (b : ℕ → ℝ) {D : ℕ} (s : Fin D → ℕ) : ℝ :=
  ∑ i, b (s i)

theorem tupleProfileValuation_smoothTuple_lt
    {b : ℕ → ℝ} {D Q : ℕ}
    (hrecord : ∀ a c : ℕ, Q ≤ c → a < c →
      rapidIncrement b a < rapidIncrement b c)
    (s : Fin D → ℕ) {lo hi : Fin D} (hne : lo ≠ hi)
    (hQ : Q ≤ s hi - 1) (hgap : s lo + 1 < s hi) :
    tupleProfileValuation b (smoothTuple s lo hi) <
      tupleProfileValuation b s := by
  classical
  rw [tupleProfileValuation, tupleProfileValuation]
  rw [sum_comp_smoothTuple s hne b, sum_eq_two_add_rest (fun i => b (s i)) hne]
  have hhi : 0 < s hi := by omega
  have hinc := hrecord (s lo) (s hi - 1) hQ (by omega)
  dsimp [rapidIncrement] at hinc
  rw [Nat.sub_add_cancel hhi] at hinc
  linarith

theorem exists_boundaryShell_of_rapidProfile_sum_bounds
    {b : ℕ → ℝ} {D q K C Q : ℕ}
    (hD : 0 < D) (hKC : C < K) (hqQ : Q + 1 ≤ q)
    (hrecord : ∀ a c : ℕ, Q ≤ c → a < c →
      rapidIncrement b a < rapidIncrement b c)
    (s : Fin D → ℕ)
    (hsumLower : D * q ≤ ∑ i, s i)
    (hsumUpper : ∑ i, s i ≤ D * q + C)
    (hout : ¬ tupleInWindow q K s) :
    ∃ t : Fin D → ℕ,
      ∑ i, t i = ∑ i, s i ∧
      tupleInWindow q (K + 1) t ∧
      ¬ tupleInWindow q K t ∧
      tupleProfileValuation b t ≤ tupleProfileValuation b s := by
  apply exists_boundaryShell_of_sum_bounds_of_smoothing hD hKC
    (tupleProfileValuation b)
  · intro t lo hi hne hqhi hgap
    apply (tupleProfileValuation_smoothTuple_lt hrecord t hne ?_ hgap).le
    omega
  · exact hsumLower
  · exact hsumUpper
  · exact hout

def sequenceShift : Module.End ℝ (ℕ → ℝ) where
  toFun b n := b (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem intCastEnd_commute_sequenceShift (z : ℤ) :
    Commute (z : Module.End ℝ (ℕ → ℝ)) sequenceShift := by
  apply LinearMap.ext
  intro b
  funext n
  simp [sequenceShift]

def polynomialShiftOperator (Q : Polynomial ℤ) : Module.End ℝ (ℕ → ℝ) :=
  Polynomial.eval₂ (Int.castRingHom (Module.End ℝ (ℕ → ℝ))) sequenceShift Q

theorem sequenceShift_pow_apply (k n : ℕ) (b : ℕ → ℝ) :
    (sequenceShift ^ k) b n = b (n + k) := by
  induction k generalizing b n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply]
      rw [ih, sequenceShift]
      congr 1

theorem polynomialShiftOperator_apply (Q : Polynomial ℤ) (b : ℕ → ℝ) (n : ℕ) :
    polynomialShiftOperator Q b n =
      ∑ k ∈ Finset.range (Q.natDegree + 1), (Q.coeff k : ℝ) * b (n + k) := by
  rw [polynomialShiftOperator, Polynomial.eval₂_eq_sum_range]
  simp only [LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply]
  apply Finset.sum_congr rfl
  intro k hk
  simp [sequenceShift_pow_apply]

theorem atomPattern_defect_eq_polynomialShiftOperator
    {M D : ℕ} (hM : 0 < M) (p₀ p₁ : Fin M → Fin (D + 1))
    (b : ℕ → ℝ) (q : ℕ) :
    (∑ j : Fin M,
      ((((p₁ j : ℕ) : ℤ) - ((p₀ j : ℕ) : ℤ) : ℤ) : ℝ) *
        b (q + (j : ℕ))) =
      polynomialShiftOperator (atomPatternDifferencePolynomial p₀ p₁) b q := by
  rw [polynomialShiftOperator_apply]
  exact (sum_range_atomPatternDifferencePolynomial hM p₀ p₁ b q).symm

theorem polynomialShiftOperator_sub_one_sq_apply (b : ℕ → ℝ) :
    polynomialShiftOperator (((Polynomial.X : Polynomial ℤ) - 1) ^ 2) b =
      rapidCurvature b := by
  funext n
  rw [show ((Polynomial.X : Polynomial ℤ) - 1) ^ 2 =
      (Polynomial.X - 1) * (Polynomial.X - 1) by ring]
  rw [polynomialShiftOperator, Polynomial.eval₂_mul_noncomm]
  · simp [rapidCurvature, sequenceShift]
    ring
  · intro k
    exact intCastEnd_commute_sequenceShift _

theorem polynomialShiftOperator_sub_one_apply (b : ℕ → ℝ) :
    polynomialShiftOperator ((Polynomial.X : Polynomial ℤ) - 1) b =
      rapidIncrement b := by
  funext n
  simp [polynomialShiftOperator, rapidIncrement, sequenceShift]

theorem polynomialShiftOperator_mul_sub_one
    (R : Polynomial ℤ) (b : ℕ → ℝ) :
    polynomialShiftOperator (R * ((Polynomial.X : Polynomial ℤ) - 1)) b =
      polynomialShiftOperator R (rapidIncrement b) := by
  rw [polynomialShiftOperator, Polynomial.eval₂_mul_noncomm]
  · change polynomialShiftOperator R
      (polynomialShiftOperator ((Polynomial.X : Polynomial ℤ) - 1) b) =
        polynomialShiftOperator R (rapidIncrement b)
    rw [polynomialShiftOperator_sub_one_apply]
  · intro k
    exact intCastEnd_commute_sequenceShift _

theorem polynomialShiftOperator_mul_sub_one_sq
    (R : Polynomial ℤ) (b : ℕ → ℝ) :
    polynomialShiftOperator (R * ((Polynomial.X : Polynomial ℤ) - 1) ^ 2) b =
      polynomialShiftOperator R (rapidCurvature b) := by
  rw [polynomialShiftOperator, Polynomial.eval₂_mul_noncomm]
  · rw [show Polynomial.eval₂ (Int.castRingHom (Module.End ℝ (ℕ → ℝ)))
        sequenceShift ((Polynomial.X - 1) ^ 2) =
      polynomialShiftOperator (((Polynomial.X : Polynomial ℤ) - 1) ^ 2) by rfl]
    change polynomialShiftOperator R
      (polynomialShiftOperator (((Polynomial.X : Polynomial ℤ) - 1) ^ 2) b) =
        polynomialShiftOperator R (rapidCurvature b)
    rw [polynomialShiftOperator_sub_one_sq_apply]
  · intro k
    exact intCastEnd_commute_sequenceShift _

theorem rapidCurvature_natSquare :
    rapidCurvature (fun n : ℕ => (n : ℝ) ^ 2) = fun _ => (2 : ℝ) := by
  funext n
  simp only [rapidCurvature, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem rapidIncrement_natIdentity :
    rapidIncrement (fun n : ℕ => (n : ℝ)) = fun _ => (1 : ℝ) := by
  funext n
  simp [rapidIncrement]

theorem polynomialShiftOperator_const_one (R : Polynomial ℤ) (n : ℕ) :
    polynomialShiftOperator R (fun _ => (1 : ℝ)) n =
      (R.eval 1 : ℤ) := by
  rw [polynomialShiftOperator_apply]
  have heval := Polynomial.eval_eq_sum_range (p := R) (x := (1 : ℤ))
  simp only [one_pow, mul_one] at heval
  have hevalR : ((R.eval 1 : ℤ) : ℝ) =
      ∑ k ∈ Finset.range (R.natDegree + 1), (R.coeff k : ℝ) := by
    exact_mod_cast heval
  simpa [hevalR]

theorem polynomialShiftOperator_const_two (R : Polynomial ℤ) (n : ℕ) :
    polynomialShiftOperator R (fun _ => (2 : ℝ)) n =
      2 * (R.eval 1 : ℤ) := by
  rw [polynomialShiftOperator_apply]
  have heval := Polynomial.eval_eq_sum_range (p := R) (x := (1 : ℤ))
  simp only [one_pow, mul_one] at heval
  have hevalR : ((R.eval 1 : ℤ) : ℝ) =
      ∑ k ∈ Finset.range (R.natDegree + 1), (R.coeff k : ℝ) := by
    exact_mod_cast heval
  rw [hevalR, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem polynomialShiftOperator_natSquare_zero (Q : Polynomial ℤ) :
    polynomialShiftOperator Q (fun n : ℕ => (n : ℝ) ^ 2) 0 =
      stretchedMoment (polynomialRealCoeffFinsupp Q) 2 := by
  rw [polynomialShiftOperator_apply,
    stretchedMoment_polynomialRealCoeffFinsupp_eq_sum_range]
  simp

theorem polynomialShiftOperator_natIdentity_zero (Q : Polynomial ℤ) :
    polynomialShiftOperator Q (fun n : ℕ => (n : ℝ)) 0 =
      stretchedMoment (polynomialRealCoeffFinsupp Q) 1 := by
  rw [polynomialShiftOperator_apply,
    stretchedMoment_polynomialRealCoeffFinsupp_eq_sum_range]
  simp

theorem eval_one_eq_stretchedMoment_one_of_factor
    {Q R : Polynomial ℤ}
    (hfactor : Q = R * ((Polynomial.X : Polynomial ℤ) - 1)) :
    ((R.eval 1 : ℤ) : ℝ) =
      stretchedMoment (polynomialRealCoeffFinsupp Q) 1 := by
  have haction := congrArg
    (fun T : Module.End ℝ (ℕ → ℝ) => T (fun n : ℕ => (n : ℝ)) 0)
    (congrArg polynomialShiftOperator hfactor)
  change polynomialShiftOperator Q (fun n : ℕ => (n : ℝ)) 0 =
    polynomialShiftOperator (R * ((Polynomial.X : Polynomial ℤ) - 1))
      (fun n : ℕ => (n : ℝ)) 0 at haction
  rw [polynomialShiftOperator_natIdentity_zero] at haction
  rw [show polynomialShiftOperator
      (R * ((Polynomial.X : Polynomial ℤ) - 1))
      (fun n : ℕ => (n : ℝ)) =
        polynomialShiftOperator R
          (rapidIncrement (fun n : ℕ => (n : ℝ))) from
    polynomialShiftOperator_mul_sub_one R _] at haction
  rw [rapidIncrement_natIdentity, polynomialShiftOperator_const_one] at haction
  exact haction.symm

theorem eval_one_eq_half_stretchedMoment_two_of_factor
    {Q R : Polynomial ℤ}
    (hfactor : Q = R * ((Polynomial.X : Polynomial ℤ) - 1) ^ 2) :
    ((R.eval 1 : ℤ) : ℝ) =
      stretchedMoment (polynomialRealCoeffFinsupp Q) 2 / 2 := by
  have haction := congrArg
    (fun T : Module.End ℝ (ℕ → ℝ) => T (fun n : ℕ => (n : ℝ) ^ 2) 0)
    (congrArg polynomialShiftOperator hfactor)
  change polynomialShiftOperator Q (fun n : ℕ => (n : ℝ) ^ 2) 0 =
    polynomialShiftOperator (R * ((Polynomial.X : Polynomial ℤ) - 1) ^ 2)
      (fun n : ℕ => (n : ℝ) ^ 2) 0 at haction
  rw [polynomialShiftOperator_natSquare_zero] at haction
  rw [show polynomialShiftOperator
      (R * ((Polynomial.X : Polynomial ℤ) - 1) ^ 2)
      (fun n : ℕ => (n : ℝ) ^ 2) =
        polynomialShiftOperator R
          (rapidCurvature (fun n : ℕ => (n : ℝ) ^ 2)) from
    polynomialShiftOperator_mul_sub_one_sq R _] at haction
  rw [rapidCurvature_natSquare, polynomialShiftOperator_const_two] at haction
  linarith

theorem tendsto_polynomialShiftOperator_div_of_shiftStable
    {κ : ℕ → ℝ}
    (hshift : ∀ r : ℕ,
      Tendsto (fun n => κ (n + r) / κ n) atTop (𝓝 1))
    (R : Polynomial ℤ) :
    Tendsto (fun n => polynomialShiftOperator R κ n / κ n)
      atTop (𝓝 ((R.eval 1 : ℤ) : ℝ)) := by
  have hterm : ∀ r ∈ Finset.range (R.natDegree + 1),
      Tendsto (fun n => (R.coeff r : ℝ) * (κ (n + r) / κ n))
        atTop (𝓝 ((R.coeff r : ℝ) * 1)) := by
    intro r hr
    exact (hshift r).const_mul _
  have hsum := tendsto_finsetSum (s := Finset.range (R.natDegree + 1)) hterm
  have heval := Polynomial.eval_eq_sum_range (p := R) (x := (1 : ℤ))
  simp only [one_pow, mul_one] at heval
  have hevalR : ((R.eval 1 : ℤ) : ℝ) =
      ∑ r ∈ Finset.range (R.natDegree + 1), (R.coeff r : ℝ) := by
    exact_mod_cast heval
  simp only [mul_one] at hsum
  rw [← hevalR] at hsum
  refine hsum.congr' ?_
  filter_upwards with n
  rw [polynomialShiftOperator_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hr
  ring

def tupleDifferenceIntPolynomial {D : ℕ}
    (u v : Fin D → ℕ) : Polynomial ℤ :=
  (∑ i, Polynomial.monomial (u i) 1) -
    ∑ i, Polynomial.monomial (v i) 1

theorem polynomialRealCoeffFinsupp_tupleDifferenceIntPolynomial
    {D : ℕ} (u v : Fin D → ℕ) :
    polynomialRealCoeffFinsupp (tupleDifferenceIntPolynomial u v) =
      tupleDifference u v := by
  classical
  ext r
  simp only [polynomialRealCoeffFinsupp_apply, tupleDifferenceIntPolynomial,
    Polynomial.coeff_sub, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [tupleDifference_apply_eq_key_sub]
  simp only [key, Finsupp.finsetSum_apply, Finsupp.single_apply]
  push_cast
  ring

theorem polynomialShiftOperator_tupleDifferenceIntPolynomial
    {D : ℕ} (u v : Fin D → ℕ) (b : ℕ → ℝ) (q : ℕ) :
    polynomialShiftOperator (tupleDifferenceIntPolynomial u v) b q =
      (∑ i, b (q + u i)) - ∑ i, b (q + v i) := by
  have hsum (w : Fin D → ℕ) :
      Polynomial.eval₂ (Int.castRingHom (Module.End ℝ (ℕ → ℝ))) sequenceShift
          (∑ i, Polynomial.monomial (w i) 1) b q =
        ∑ i, b (q + w i) := by
    rw [Polynomial.eval₂_finsetSum]
    simp only [LinearMap.sum_apply, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.eval₂_monomial, Module.End.mul_apply]
    simp [sequenceShift_pow_apply]
  rw [tupleDifferenceIntPolynomial, polynomialShiftOperator, Polynomial.eval₂_sub,
    LinearMap.sub_apply, Pi.sub_apply, hsum u, hsum v]

theorem exists_curvaturePolynomial_of_double_momentPolynomial
    {Q : Polynomial ℤ} (hQ : Q ≠ 0)
    (hmoment0 : stretchedMoment (polynomialRealCoeffFinsupp Q) 0 = 0)
    (hmoment1 : stretchedMoment (polynomialRealCoeffFinsupp Q) 1 = 0) :
    ∃ R : Polynomial ℤ, R ≠ 0 ∧
      Q = R * ((Polynomial.X : Polynomial ℤ) - 1) ^ 2 ∧
      ∀ b : ℕ → ℝ,
        polynomialShiftOperator Q b =
          polynomialShiftOperator R (rapidCurvature b) := by
  have hdiv : ((Polynomial.X : Polynomial ℤ) - 1) ^ 2 ∣ Q := by
    apply sub_one_pow_dvd_of_polynomialRealCoeff_moments
    intro k hk
    interval_cases k
    · exact hmoment0
    · exact hmoment1
  obtain ⟨R, hR⟩ := hdiv
  have hfactor : Q = R * ((Polynomial.X : Polynomial ℤ) - 1) ^ 2 := by
    simpa [mul_comm] using hR
  have hRne : R ≠ 0 := by
    intro hz
    apply hQ
    rw [hfactor, hz, zero_mul]
  refine ⟨R, hRne, hfactor, fun b => ?_⟩
  rw [hfactor, polynomialShiftOperator_mul_sub_one_sq]

theorem tendsto_tupleDifference_div_curvature
    {b : ℕ → ℝ} {D : ℕ} {u v : Fin D → ℕ}
    (hmoment0 : stretchedMoment (tupleDifference u v) 0 = 0)
    (hmoment1 : stretchedMoment (tupleDifference u v) 1 = 0)
    (hmoment2 : stretchedMoment (tupleDifference u v) 2 ≠ 0)
    (hshift : ∀ r : ℕ, Tendsto
      (fun n => rapidCurvature b (n + r) / rapidCurvature b n)
      atTop (𝓝 1)) :
    Tendsto (fun n =>
      ((∑ i, b (n + u i)) - ∑ i, b (n + v i)) /
        rapidCurvature b n)
      atTop (𝓝 (stretchedMoment (tupleDifference u v) 2 / 2)) := by
  let Q := tupleDifferenceIntPolynomial u v
  have hQ : Q ≠ 0 := by
    intro hzero
    apply hmoment2
    rw [← polynomialRealCoeffFinsupp_tupleDifferenceIntPolynomial u v,
      show tupleDifferenceIntPolynomial u v = Q from rfl, hzero]
    have hz : polynomialRealCoeffFinsupp (0 : Polynomial ℤ) = 0 := by
      ext n
      simp
    rw [hz]
    rw [stretchedMoment]
    exact Finsupp.sum_zero_index
  have hmoment0Q : stretchedMoment (polynomialRealCoeffFinsupp Q) 0 = 0 := by
    simpa [Q, polynomialRealCoeffFinsupp_tupleDifferenceIntPolynomial] using hmoment0
  have hmoment1Q : stretchedMoment (polynomialRealCoeffFinsupp Q) 1 = 0 := by
    simpa [Q, polynomialRealCoeffFinsupp_tupleDifferenceIntPolynomial] using hmoment1
  obtain ⟨R, _hR, hfactor, hoperator⟩ :=
    exists_curvaturePolynomial_of_double_momentPolynomial
      hQ hmoment0Q hmoment1Q
  have heval := eval_one_eq_half_stretchedMoment_two_of_factor hfactor
  rw [polynomialRealCoeffFinsupp_tupleDifferenceIntPolynomial] at heval
  have ht := tendsto_polynomialShiftOperator_div_of_shiftStable hshift R
  rw [heval] at ht
  refine ht.congr' ?_
  filter_upwards with n
  rw [← hoperator b]
  congr 1
  simpa [Q] using polynomialShiftOperator_tupleDifferenceIntPolynomial u v b n

theorem eventually_half_curvature_le_tupleDifference
    {b : ℕ → ℝ} {D : ℕ} {u v : Fin D → ℕ}
    (hmoment0 : stretchedMoment (tupleDifference u v) 0 = 0)
    (hmoment1 : stretchedMoment (tupleDifference u v) 1 = 0)
    (hmoment2 : 0 < stretchedMoment (tupleDifference u v) 2)
    (hκpos : ∀ᶠ n : ℕ in atTop, 0 < rapidCurvature b n)
    (hshift : ∀ r : ℕ, Tendsto
      (fun n => rapidCurvature b (n + r) / rapidCurvature b n)
      atTop (𝓝 1)) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 4 : ℝ) * rapidCurvature b n ≤
        (∑ i, b (n + u i)) - ∑ i, b (n + v i) := by
  have hlim := tendsto_tupleDifference_div_curvature
    hmoment0 hmoment1 hmoment2.ne' hshift
  have hhalf : (1 / 4 : ℝ) <
      stretchedMoment (tupleDifference u v) 2 / 2 := by
    have hmomentOne : (1 : ℝ) ≤ stretchedMoment (tupleDifference u v) 2 := by
      rw [stretchedMoment_tupleDifference] at hmoment2 ⊢
      have hreal : (∑ i, ((v i : ℕ) : ℝ) ^ 2) <
          ∑ i, ((u i : ℕ) : ℝ) ^ 2 := sub_pos.mp hmoment2
      have hnat : (∑ i, (v i) ^ 2) < ∑ i, (u i) ^ 2 := by
        exact_mod_cast hreal
      have hcast : ((∑ i, (v i) ^ 2 : ℕ) : ℝ) + 1 ≤
          (∑ i, (u i) ^ 2 : ℕ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hnat)
      push_cast at hcast
      linarith
    linarith
  have hevent := hlim.eventually_const_lt hhalf
  filter_upwards [hevent, hκpos] with n hn hκ
  rw [lt_div_iff₀ hκ] at hn
  exact hn.le

theorem boundaryOffsetCandidate_eventually_half_curvature_gap
    {b : ℕ → ℝ} {D L : ℕ} (δ : Fin D → ℕ)
    (hLsq : (∑ i, (δ i : ℝ) ^ 2) < (L : ℝ) ^ 2)
    (u : Fin D → Fin (2 * L + 1))
    (hu : boundaryOffsetCandidate δ u)
    (hmoment1 : stretchedMoment
      (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) 1 = 0)
    (hκpos : ∀ᶠ n : ℕ in atTop, 0 < rapidCurvature b n)
    (hshift : ∀ r : ℕ, Tendsto
      (fun n => rapidCurvature b (n + r) / rapidCurvature b n)
      atTop (𝓝 1)) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 4 : ℝ) * rapidCurvature b n ≤
        (∑ i, b (n + (u i : ℕ))) - ∑ i, b (n + δ i + L) := by
  have hmoment0 : stretchedMoment
      (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) 0 = 0 := by
    rw [stretchedMoment_tupleDifference]
    simp
  have hmoment2 :=
    boundaryOffsetCandidate_moment_two_pos_of_moment_one_zero
      δ u hu hLsq hmoment1
  have hgap := eventually_half_curvature_le_tupleDifference
    hmoment0 hmoment1 hmoment2 hκpos hshift
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hgap

theorem boundaryOffsetCandidate_eventually_all_half_curvature_gap
    {b : ℕ → ℝ} {D L : ℕ} (δ : Fin D → ℕ)
    (hLsq : (∑ i, (δ i : ℝ) ^ 2) < (L : ℝ) ^ 2)
    (hκpos : ∀ᶠ n : ℕ in atTop, 0 < rapidCurvature b n)
    (hshift : ∀ r : ℕ, Tendsto
      (fun n => rapidCurvature b (n + r) / rapidCurvature b n)
      atTop (𝓝 1)) :
    ∀ᶠ n : ℕ in atTop, ∀ u : Fin D → Fin (2 * L + 1),
      boundaryOffsetCandidate δ u →
      stretchedMoment
        (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) 1 = 0 →
      (1 / 4 : ℝ) * rapidCurvature b n ≤
        (∑ i, b (n + (u i : ℕ))) - ∑ i, b (n + δ i + L) := by
  rw [Filter.eventually_all]
  intro u
  by_cases hu : boundaryOffsetCandidate δ u ∧
      stretchedMoment
        (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) 1 = 0
  · exact boundaryOffsetCandidate_eventually_half_curvature_gap
      δ hLsq u hu.1 hu.2 hκpos hshift |>.mono (fun _ hn _ _ => hn)
  · filter_upwards with n
    intro hcandidate hmoment
    exact (hu ⟨hcandidate, hmoment⟩).elim

theorem eventually_log_nat_add_two_lt_quarter_curvature_sub
    {b : ℕ → ℝ}
    (hκlog : Tendsto
      (fun n => rapidCurvature b n / Real.log ((n : ℝ) + 2))
      atTop atTop)
    (A L : ℕ) :
    ∀ᶠ q : ℕ in atTop,
      (A : ℝ) * Real.log ((q : ℝ) + 2) <
        (1 / 4 : ℝ) * rapidCurvature b (q - L) := by
  have hratio := hκlog.comp (tendsto_sub_atTop_nat L)
  have hlarge := hratio.eventually_gt_atTop ((8 : ℝ) * A + 1)
  filter_upwards [hlarge, eventually_ge_atTop (2 * L)] with q hqLarge hq
  let n := q - L
  have hnL : L ≤ n := by dsimp [n]; omega
  have hnq : n + L = q := by dsimp [n]; omega
  have hlogBound := log_nat_add_shift_le_two_mul_log hnL
  rw [hnq] at hlogBound
  have hlogPos : 0 < Real.log ((n : ℝ) + 2) := by
    apply Real.log_pos
    have hn0 : (0 : ℝ) ≤ n := by positivity
    linarith
  have hcurv :
      (((8 : ℝ) * A + 1) * Real.log ((n : ℝ) + 2)) <
        rapidCurvature b n := by
    exact (lt_div_iff₀ hlogPos).mp hqLarge
  have hA0 : (0 : ℝ) ≤ A := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hlogBound hA0
  dsimp [n] at hcurv hlogPos hscaled ⊢
  nlinarith

theorem tupleProfileValuation_shellOffset {b : ℕ → ℝ} {D q L : ℕ}
    (t : Fin D → ℕ) (hLq : L ≤ q) (hwide : tupleInWindow q L t) :
    tupleProfileValuation b t =
      ∑ i, b ((q - L) + (shellOffset t hLq hwide i : ℕ)) := by
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  simp only [shellOffset]
  have hlo := (hwide i).1
  omega

theorem tupleProfileValuation_witness_as_offset
    {b : ℕ → ℝ} {D q L : ℕ}
    (δ : Fin D → ℕ) (hLq : L ≤ q) :
    tupleProfileValuation b (fun i => q + δ i) =
      ∑ i, b ((q - L) + (δ i + L)) := by
  apply Finset.sum_congr rfl
  intro i hi
  apply congrArg b
  simp only
  have hqsplit : q - L + L = q := Nat.sub_add_cancel hLq
  omega

theorem exists_eventually_bounded_rapidSameSumNearMinimizer
    {b : ℕ → ℝ}
    (hrecord : ∃ Q : ℕ, ∀ a c : ℕ, Q ≤ c → a < c →
      rapidIncrement b a < rapidIncrement b c)
    (hκpos : ∀ᶠ n : ℕ in atTop, 0 < rapidCurvature b n)
    (hshift : ∀ r : ℕ, Tendsto
      (fun n => rapidCurvature b (n + r) / rapidCurvature b n)
      atTop (𝓝 1))
    (hκlog : Tendsto
      (fun n => rapidCurvature b n / Real.log ((n : ℝ) + 2))
      atTop atTop)
    {D : ℕ} (hD : 0 < D) (δ : Fin D → ℕ) (A : ℕ) :
    ∃ K : ℕ, ∀ᶠ q : ℕ in atTop, ∀ s : Fin D → ℕ,
      (∑ i, s i) = D * q + ∑ i, δ i →
      tupleProfileValuation b s <
        tupleProfileValuation b (fun i => q + δ i) +
          (A : ℝ) * Real.log ((q : ℝ) + 2) →
      tupleInWindow q K s := by
  classical
  obtain ⟨Q, hQ⟩ := hrecord
  let Aδ := ∑ i, δ i
  let Sδ := ∑ i, (δ i) ^ 2
  let K := Aδ + Sδ + 1
  let L := K + 1
  have hAδK : Aδ < K := by dsimp [K]; omega
  have hLpos : 0 < L := by dsimp [L, K]; omega
  have hSltL : Sδ < L := by dsimp [L, K]; omega
  have hSltLsq : Sδ < L ^ 2 := hSltL.trans_le (by nlinarith : L ≤ L ^ 2)
  have hLsq : (∑ i, (δ i : ℝ) ^ 2) < (L : ℝ) ^ 2 := by
    have hcast : (Sδ : ℝ) < (L : ℝ) ^ 2 := by exact_mod_cast hSltLsq
    simpa [Sδ] using hcast
  have hgapBase :=
    boundaryOffsetCandidate_eventually_all_half_curvature_gap
      (b := b) δ hLsq hκpos hshift
  have hgapNat := (tendsto_sub_atTop_nat L).eventually hgapBase
  have hlogGap :=
    eventually_log_nat_add_two_lt_quarter_curvature_sub hκlog A L
  refine ⟨K, ?_⟩
  filter_upwards [hgapNat, hlogGap,
    eventually_ge_atTop (max (Q + 1) (2 * L))] with q hgap hlog hq
  intro s hsum hnear
  by_contra hout
  have hQq : Q + 1 ≤ q := (le_max_left _ _).trans hq
  have hLq : L ≤ q := by
    have : 2 * L ≤ q := (le_max_right _ _).trans hq
    omega
  have hsumLower : D * q ≤ ∑ i, s i := by
    rw [hsum]
    omega
  have hsumUpper : (∑ i, s i) ≤ D * q + Aδ := by
    simpa [Aδ] using hsum.le
  obtain ⟨t, htsum, htwide, htout, htval⟩ :=
    exists_boundaryShell_of_rapidProfile_sum_bounds
      hD hAδK hQq hQ s hsumLower hsumUpper hout
  have htsumWitness : D * q + (∑ i, δ i) ≤ ∑ i, t i := by
    rw [htsum, hsum]
  have hcand := shellOffset_boundaryCandidate δ t hLq htwide htout htsumWitness
  let u := shellOffset t hLq htwide
  have hmoment1 : stretchedMoment
      (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) 1 = 0 := by
    rw [stretchedMoment_tupleDifference]
    simp only [pow_one]
    apply sub_eq_zero.mpr
    norm_cast
    dsimp [u]
    change (∑ i, (shellOffset t hLq htwide i : ℕ)) =
      ∑ i, (δ i + L)
    rw [shellOffset_sum t hLq htwide, htsum, hsum,
      Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hDsplit : D * q = D * (q - L) + D * L := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hLq]
    rw [hDsplit]
    have hreassoc :
        D * (q - L) + D * L + (∑ i, δ i) =
          D * (q - L) + (D * L + ∑ i, δ i) := by omega
    rw [hreassoc, Nat.add_sub_cancel_left]
    change D * L + (∑ i, δ i) = (∑ i, δ i) + D * L
    omega
  have hgap' := hgap u hcand hmoment1
  have hgapVal : (1 / 4 : ℝ) * rapidCurvature b (q - L) ≤
      tupleProfileValuation b t -
        tupleProfileValuation b (fun i => q + δ i) := by
    rw [tupleProfileValuation_shellOffset t hLq htwide,
      tupleProfileValuation_witness_as_offset δ hLq]
    simpa [u, Nat.add_assoc] using hgap'
  have hnearT : tupleProfileValuation b t -
      tupleProfileValuation b (fun i => q + δ i) <
        (A : ℝ) * Real.log ((q : ℝ) + 2) := by
    linarith
  linarith

theorem tendsto_rapidCurvature_atTop_of_div_log_atTop
    {b : ℕ → ℝ}
    (hκlog : Tendsto
      (fun n => rapidCurvature b n / Real.log ((n : ℝ) + 2))
      atTop atTop) :
    Tendsto (rapidCurvature b) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  rw [tendsto_atTop]
  intro A
  filter_upwards [hκlog.eventually_gt_atTop 1,
    hlog.eventually_gt_atTop A] with n hratio hlogA
  have hlogPos : 0 < Real.log ((n : ℝ) + 2) :=
    Real.log_pos (by
      have hn0 : (0 : ℝ) ≤ n := by positivity
      linarith)
  have hκgt : Real.log ((n : ℝ) + 2) < rapidCurvature b n := by
    have := (lt_div_iff₀ hlogPos).mp hratio
    simpa using this
  exact (hlogA.trans hκgt).le

theorem rapidIncrement_succ (b : ℕ → ℝ) (n : ℕ) :
    rapidIncrement b (n + 1) =
      rapidIncrement b n + rapidCurvature b n := by
  simp only [rapidIncrement, rapidCurvature]
  ring

theorem rapidIncrement_add_eq (b : ℕ → ℝ) (n r : ℕ) :
    rapidIncrement b (n + r) =
      rapidIncrement b n + ∑ t ∈ Finset.range r, rapidCurvature b (n + t) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.add_succ, rapidIncrement_succ, ih, Finset.sum_range_succ]
      ring

theorem tendsto_rapidIncrement_shift_ratio
    {b : ℕ → ℝ}
    (hinc : ∀ᶠ n : ℕ in atTop, b n < b (n + 1))
    (hκpos : ∀ᶠ n : ℕ in atTop, 0 < rapidCurvature b n)
    (hκshift : ∀ r : ℕ, Tendsto
      (fun n => rapidCurvature b (n + r) / rapidCurvature b n)
      atTop (𝓝 1))
    (hκinc : Tendsto
      (fun n => rapidCurvature b n / rapidIncrement b n)
      atTop (𝓝 0))
    (r : ℕ) :
    Tendsto (fun n => rapidIncrement b (n + r) / rapidIncrement b n)
      atTop (𝓝 1) := by
  have hterm : ∀ t ∈ Finset.range r,
      Tendsto (fun n =>
        rapidCurvature b (n + t) / rapidIncrement b n)
        atTop (𝓝 0) := by
    intro t ht
    have hmul := (hκshift t).mul hκinc
    simpa only [one_mul] using hmul.congr' (by
      filter_upwards [hκpos] with n hκ
      field_simp [ne_of_gt hκ])
  have hsum := tendsto_finsetSum (s := Finset.range r) hterm
  simp only [Finset.sum_const_zero] at hsum
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) +
      ∑ t ∈ Finset.range r,
        rapidCurvature b (n + t) / rapidIncrement b n)
      atTop (𝓝 ((1 : ℝ) + 0)) := tendsto_const_nhds.add hsum
  simpa only [add_zero] using hone.congr' (by
    filter_upwards [hinc] with n hn
    have hΔne : rapidIncrement b n ≠ 0 := by
      dsimp [rapidIncrement]
      linarith
    rw [rapidIncrement_add_eq, add_div, div_self hΔne, Finset.sum_div])

theorem tendsto_rapidIncrement_atTop
    {b : ℕ → ℝ}
    (hinc : ∀ᶠ n : ℕ in atTop, b n < b (n + 1))
    (hκlog : Tendsto
      (fun n => rapidCurvature b n / Real.log ((n : ℝ) + 2))
      atTop atTop) :
    Tendsto (rapidIncrement b) atTop atTop := by
  have hκtop := tendsto_rapidCurvature_atTop_of_div_log_atTop hκlog
  have hsucc : Tendsto (fun n => rapidIncrement b (n + 1)) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hκtop
    filter_upwards [hinc] with n hn
    rw [rapidIncrement_succ]
    have hn' : 0 < rapidIncrement b n := by
      dsimp [rapidIncrement]
      linarith
    linarith
  rw [tendsto_atTop] at hsucc ⊢
  intro A
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hsucc A)
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  have hNm : N ≤ n - 1 := by omega
  have hv := hN (n - 1) hNm
  have hnpos : 1 ≤ n := by omega
  simpa [Nat.sub_add_cancel hnpos] using hv

theorem exists_rapidIncrement_record_strict
    {b : ℕ → ℝ}
    (hinc : ∀ᶠ n : ℕ in atTop, b n < b (n + 1))
    (hκpos : ∀ᶠ n : ℕ in atTop, 0 < rapidCurvature b n)
    (hκlog : Tendsto
      (fun n => rapidCurvature b n / Real.log ((n : ℝ) + 2))
      atTop atTop) :
    ∃ Q : ℕ, ∀ a c : ℕ, Q ≤ c → a < c →
      rapidIncrement b a < rapidIncrement b c := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hκpos
  have hadj : ∀ n ≥ T,
      rapidIncrement b n < rapidIncrement b (n + 1) := by
    intro n hn
    rw [rapidIncrement_succ]
    exact lt_add_of_pos_right _ (hT n hn)
  have htail : StrictMono (fun r : ℕ => rapidIncrement b (T + r)) := by
    apply strictMono_nat_of_lt_succ
    intro r
    simpa [Nat.add_assoc] using hadj (T + r) (Nat.le_add_right T r)
  have htop := tendsto_rapidIncrement_atTop hinc hκlog
  have hprefix : ∀ᶠ c : ℕ in atTop, ∀ a ∈ Finset.range T,
      rapidIncrement b a < rapidIncrement b c := by
    rw [Filter.eventually_all_finset]
    intro a ha
    exact htop.eventually (eventually_gt_atTop (rapidIncrement b a))
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.mp hprefix
  let Q := max Q₀ T
  refine ⟨Q, fun a c hQc hac => ?_⟩
  by_cases ha : a < T
  · exact hQ₀ c ((le_max_left Q₀ T).trans hQc)
      a (Finset.mem_range.mpr ha)
  · have hTa : T ≤ a := Nat.le_of_not_gt ha
    have hTc : T ≤ c := hTa.trans hac.le
    have hsub : a - T < c - T := Nat.sub_lt_sub_right hTa hac
    simpa [Nat.add_sub_of_le hTa, Nat.add_sub_of_le hTc] using htail hsub

theorem atomPatternDifference_sub_one_sq_dvd
    {M D : ℕ} (p₀ p₁ : Fin M → Fin (D + 1))
    (hcount₀ : (∑ j, (p₀ j : ℕ)) = D)
    (hcount₁ : (∑ j, (p₁ j : ℕ)) = D)
    (hweight : (∑ j : Fin M, (j : ℕ) * (p₀ j : ℕ)) =
      ∑ j : Fin M, (j : ℕ) * (p₁ j : ℕ)) :
    ((Polynomial.X : Polynomial ℤ) - 1) ^ 2 ∣
      atomPatternDifferencePolynomial p₀ p₁ := by
  apply sub_one_pow_dvd_of_polynomialRealCoeff_moments
  intro k hk
  interval_cases k
  · rw [stretchedMoment_atomPatternDifference p₀ p₁ hcount₀ hcount₁]
    simp [polynomialPatternMoment, hcount₀, hcount₁]
  · rw [stretchedMoment_atomPatternDifference p₀ p₁ hcount₀ hcount₁]
    have hweightNat :
        polynomialPatternMoment p₀ 1 =
          polynomialPatternMoment p₁ 1 := by
      simpa [polynomialPatternMoment, mul_comm] using hweight
    have hweightReal :
        (polynomialPatternMoment p₀ 1 : ℝ) =
          polynomialPatternMoment p₁ 1 := by
      exact_mod_cast hweightNat
    exact sub_eq_zero.mpr hweightReal.symm

theorem exists_curvaturePolynomial_of_atomPattern_pair
    {M D : ℕ} {p₀ p₁ : Fin M → Fin (D + 1)}
    (hne : p₀ ≠ p₁)
    (hcount₀ : (∑ j, (p₀ j : ℕ)) = D)
    (hcount₁ : (∑ j, (p₁ j : ℕ)) = D)
    (hweight : (∑ j : Fin M, (j : ℕ) * (p₀ j : ℕ)) =
      ∑ j : Fin M, (j : ℕ) * (p₁ j : ℕ)) :
    ∃ R : Polynomial ℤ, R ≠ 0 ∧
      atomPatternDifferencePolynomial p₀ p₁ =
        R * ((Polynomial.X : Polynomial ℤ) - 1) ^ 2 ∧
      ∀ b : ℕ → ℝ,
        polynomialShiftOperator (atomPatternDifferencePolynomial p₀ p₁) b =
          polynomialShiftOperator R (rapidCurvature b) := by
  have hQ : atomPatternDifferencePolynomial p₀ p₁ ≠ 0 :=
    atomPatternDifferencePolynomial_ne_zero hne
  obtain ⟨R, hR⟩ := atomPatternDifference_sub_one_sq_dvd
    p₀ p₁ hcount₀ hcount₁ hweight
  have hfactor : atomPatternDifferencePolynomial p₀ p₁ =
      R * ((Polynomial.X : Polynomial ℤ) - 1) ^ 2 := by
    simpa [mul_comm] using hR
  have hRne : R ≠ 0 := by
    intro hz
    apply hQ
    rw [hfactor, hz, zero_mul]
  refine ⟨R, hRne, hfactor, fun b => ?_⟩
  rw [hfactor, polynomialShiftOperator_mul_sub_one_sq]

theorem atomPattern_defect_eq_curvaturePolynomial
    {M D : ℕ} (hM : 0 < M) {p₀ p₁ : Fin M → Fin (D + 1)}
    (hne : p₀ ≠ p₁)
    (hcount₀ : (∑ j, (p₀ j : ℕ)) = D)
    (hcount₁ : (∑ j, (p₁ j : ℕ)) = D)
    (hweight : (∑ j : Fin M, (j : ℕ) * (p₀ j : ℕ)) =
      ∑ j : Fin M, (j : ℕ) * (p₁ j : ℕ)) :
    ∃ R : Polynomial ℤ, R ≠ 0 ∧ ∀ (b : ℕ → ℝ) (q : ℕ),
      (∑ j : Fin M,
        ((((p₁ j : ℕ) : ℤ) - ((p₀ j : ℕ) : ℤ) : ℤ) : ℝ) *
          b (q + (j : ℕ))) =
        polynomialShiftOperator R (rapidCurvature b) q := by
  obtain ⟨R, hR, _hfactor, hoperator⟩ :=
    exists_curvaturePolynomial_of_atomPattern_pair
      hne hcount₀ hcount₁ hweight
  refine ⟨R, hR, fun b q => ?_⟩
  rw [atomPattern_defect_eq_polynomialShiftOperator hM, hoperator b]

theorem tendsto_atomPattern_defect_div_curvature
    {b : ℕ → ℝ} {M D : ℕ} (hM : 0 < M)
    {p₀ p₁ : Fin M → Fin (D + 1)}
    (hne : p₀ ≠ p₁)
    (hcount₀ : (∑ j, (p₀ j : ℕ)) = D)
    (hcount₁ : (∑ j, (p₁ j : ℕ)) = D)
    (hweight : (∑ j : Fin M, (j : ℕ) * (p₀ j : ℕ)) =
      ∑ j : Fin M, (j : ℕ) * (p₁ j : ℕ))
    (hshift : ∀ r : ℕ, Tendsto
      (fun n => rapidCurvature b (n + r) / rapidCurvature b n)
      atTop (𝓝 1)) :
    Tendsto (fun n =>
      (∑ j : Fin M,
        ((((p₁ j : ℕ) : ℤ) - ((p₀ j : ℕ) : ℤ) : ℤ) : ℝ) *
          b (n + (j : ℕ))) / rapidCurvature b n)
      atTop
      (𝓝 ((((polynomialPatternMoment p₁ 2 : ℕ) : ℝ) -
        polynomialPatternMoment p₀ 2) / 2)) := by
  obtain ⟨R, _hR, hfactor, hoperator⟩ :=
    exists_curvaturePolynomial_of_atomPattern_pair
      hne hcount₀ hcount₁ hweight
  have heval := eval_one_eq_half_stretchedMoment_two_of_factor hfactor
  rw [stretchedMoment_atomPatternDifference p₀ p₁ hcount₀ hcount₁] at heval
  have ht := tendsto_polynomialShiftOperator_div_of_shiftStable hshift R
  rw [heval] at ht
  refine ht.congr' ?_
  filter_upwards with n
  rw [← hoperator b]
  congr 1
  exact (atomPattern_defect_eq_polynomialShiftOperator hM p₀ p₁ b n).symm

theorem eventually_half_curvature_le_atomPattern_defect
    {b : ℕ → ℝ} {M D : ℕ} (hM : 0 < M)
    {p₀ p₁ : Fin M → Fin (D + 1)}
    (hne : p₀ ≠ p₁)
    (hcount₀ : (∑ j, (p₀ j : ℕ)) = D)
    (hcount₁ : (∑ j, (p₁ j : ℕ)) = D)
    (hweight : (∑ j : Fin M, (j : ℕ) * (p₀ j : ℕ)) =
      ∑ j : Fin M, (j : ℕ) * (p₁ j : ℕ))
    (hmoment : polynomialPatternMoment p₀ 2 <
      polynomialPatternMoment p₁ 2)
    (hκpos : ∀ᶠ n : ℕ in atTop, 0 < rapidCurvature b n)
    (hshift : ∀ r : ℕ, Tendsto
      (fun n => rapidCurvature b (n + r) / rapidCurvature b n)
      atTop (𝓝 1)) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 4 : ℝ) * rapidCurvature b n ≤
        ∑ j : Fin M,
          ((((p₁ j : ℕ) : ℤ) - ((p₀ j : ℕ) : ℤ) : ℤ) : ℝ) *
            b (n + (j : ℕ)) := by
  have hlim := tendsto_atomPattern_defect_div_curvature
    hM hne hcount₀ hcount₁ hweight hshift
  have hmomentR : (1 : ℝ) ≤
      ((polynomialPatternMoment p₁ 2 : ℕ) : ℝ) -
        polynomialPatternMoment p₀ 2 := by
    have hcast : ((polynomialPatternMoment p₀ 2 : ℕ) : ℝ) + 1 ≤
        polynomialPatternMoment p₁ 2 := by
      exact_mod_cast (Nat.succ_le_iff.mpr hmoment)
    linarith
  have hquarter : (1 / 4 : ℝ) <
      (((polynomialPatternMoment p₁ 2 : ℕ) : ℝ) -
        polynomialPatternMoment p₀ 2) / 2 := by linarith
  have hevent := hlim.eventually_const_lt hquarter
  filter_upwards [hevent, hκpos] with n hn hκ
  rw [lt_div_iff₀ hκ] at hn
  exact hn.le

theorem exists_curvaturePolynomial_resonance_of_persistent_atomPattern
    {b : ℕ → ℝ} {M D C K : ℕ} (hM : 0 < M)
    {p₀ p₁ : Fin M → Fin (D + 1)}
    (hne : p₀ ≠ p₁)
    (hcount₀ : (∑ j, (p₀ j : ℕ)) = D)
    (hcount₁ : (∑ j, (p₁ j : ℕ)) = D)
    (hweight : (∑ j : Fin M, (j : ℕ) * (p₀ j : ℕ)) =
      ∑ j : Fin M, (j : ℕ) * (p₁ j : ℕ))
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    (hdefect : ∀ k,
      0 ≤ ∑ j : Fin M,
        ((((p₁ j : ℕ) : ℤ) - ((p₀ j : ℕ) : ℤ) : ℤ) : ℝ) *
          b (q k + (j : ℕ)) ∧
      (∑ j : Fin M,
        ((((p₁ j : ℕ) : ℤ) - ((p₀ j : ℕ) : ℤ) : ℤ) : ℝ) *
          b (q k + (j : ℕ))) <
        (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2)) :
    ∃ R : Polynomial ℤ, R ≠ 0 ∧ Tendsto q atTop atTop ∧ ∀ k,
      0 ≤ ∑ r ∈ Finset.range (R.natDegree + 1),
        (R.coeff r : ℝ) * rapidCurvature b (q k + r) ∧
      (∑ r ∈ Finset.range (R.natDegree + 1),
        (R.coeff r : ℝ) * rapidCurvature b (q k + r)) <
        (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) := by
  obtain ⟨R, hR, hcurv⟩ :=
    atomPattern_defect_eq_curvaturePolynomial hM hne hcount₀ hcount₁ hweight
  refine ⟨R, hR, hq, fun k => ?_⟩
  rw [← polynomialShiftOperator_apply]
  rw [← hcurv b (q k)]
  exact hdefect k

theorem no_persistent_atomPattern_of_curvature_shiftSeparated
    {b : ℕ → ℝ} (hsep : LogarithmicallyShiftSeparated (rapidCurvature b))
    {M D C K : ℕ} (hM : 0 < M)
    {p₀ p₁ : Fin M → Fin (D + 1)}
    (hne : p₀ ≠ p₁)
    (hcount₀ : (∑ j, (p₀ j : ℕ)) = D)
    (hcount₁ : (∑ j, (p₁ j : ℕ)) = D)
    (hweight : (∑ j : Fin M, (j : ℕ) * (p₀ j : ℕ)) =
      ∑ j : Fin M, (j : ℕ) * (p₁ j : ℕ))
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    (hdefect : ∀ k,
      0 ≤ ∑ j : Fin M,
        ((((p₁ j : ℕ) : ℤ) - ((p₀ j : ℕ) : ℤ) : ℤ) : ℝ) *
          b (q k + (j : ℕ)) ∧
      (∑ j : Fin M,
        ((((p₁ j : ℕ) : ℤ) - ((p₀ j : ℕ) : ℤ) : ℤ) : ℝ) *
          b (q k + (j : ℕ))) <
        (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2)) :
    False := by
  obtain ⟨R, hR, _hq, hres⟩ :=
    exists_curvaturePolynomial_resonance_of_persistent_atomPattern
      hM hne hcount₀ hcount₁ hweight hq hdefect
  have hsepq := (hsep R hR).comp hq
  have hlarge := hsepq.eventually_gt_atTop ((2 : ℝ) * C + 1)
  obtain ⟨k, hk, hqK⟩ := (hlarge.and (hq.eventually_ge_atTop K)).exists
  let S : ℝ := ∑ r ∈ Finset.range (R.natDegree + 1),
    (R.coeff r : ℝ) * rapidCurvature b (q k + r)
  have hS0 : 0 ≤ S := (hres k).1
  have hSupper : S < (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) :=
    (hres k).2
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

end

end GaloisForLFunctions

-- First-order source-class separation.

namespace GaloisForLFunctions

noncomputable section

theorem exists_incrementPolynomial_of_zero_momentPolynomial
    {Q : Polynomial ℤ} (hQ : Q ≠ 0)
    (hmoment0 : stretchedMoment (polynomialRealCoeffFinsupp Q) 0 = 0) :
    ∃ R : Polynomial ℤ, R ≠ 0 ∧
      Q = R * ((Polynomial.X : Polynomial ℤ) - 1) ∧
      ∀ b : ℕ → ℝ,
        polynomialShiftOperator Q b =
          polynomialShiftOperator R (rapidIncrement b) := by
  have hdiv : ((Polynomial.X : Polynomial ℤ) - 1) ^ 1 ∣ Q := by
    apply sub_one_pow_dvd_of_polynomialRealCoeff_moments
    intro k hk
    interval_cases k
    exact hmoment0
  obtain ⟨R, hR⟩ := hdiv
  have hfactor : Q = R * ((Polynomial.X : Polynomial ℤ) - 1) := by
    simpa [mul_comm] using hR
  have hRne : R ≠ 0 := by
    intro hz
    apply hQ
    rw [hfactor, hz, zero_mul]
  refine ⟨R, hRne, hfactor, fun b => ?_⟩
  rw [hfactor, polynomialShiftOperator_mul_sub_one]

theorem tendsto_tupleDifference_div_increment
    {b : ℕ → ℝ} {D : ℕ} {u v : Fin D → ℕ}
    (hmoment0 : stretchedMoment (tupleDifference u v) 0 = 0)
    (hmoment1 : stretchedMoment (tupleDifference u v) 1 ≠ 0)
    (hshift : ∀ r : ℕ, Tendsto
      (fun n => rapidIncrement b (n + r) / rapidIncrement b n)
      atTop (𝓝 1)) :
    Tendsto (fun n =>
      ((∑ i, b (n + u i)) - ∑ i, b (n + v i)) /
        rapidIncrement b n)
      atTop (𝓝 (stretchedMoment (tupleDifference u v) 1)) := by
  let Q := tupleDifferenceIntPolynomial u v
  have hQ : Q ≠ 0 := by
    intro hzero
    apply hmoment1
    rw [← polynomialRealCoeffFinsupp_tupleDifferenceIntPolynomial u v,
      show tupleDifferenceIntPolynomial u v = Q from rfl, hzero]
    have hz : polynomialRealCoeffFinsupp (0 : Polynomial ℤ) = 0 := by
      ext n
      simp
    rw [hz, stretchedMoment]
    exact Finsupp.sum_zero_index
  have hmoment0Q : stretchedMoment (polynomialRealCoeffFinsupp Q) 0 = 0 := by
    simpa [Q, polynomialRealCoeffFinsupp_tupleDifferenceIntPolynomial] using hmoment0
  obtain ⟨R, _hR, hfactor, hoperator⟩ :=
    exists_incrementPolynomial_of_zero_momentPolynomial hQ hmoment0Q
  have heval := eval_one_eq_stretchedMoment_one_of_factor hfactor
  rw [polynomialRealCoeffFinsupp_tupleDifferenceIntPolynomial] at heval
  have ht := tendsto_polynomialShiftOperator_div_of_shiftStable hshift R
  rw [heval] at ht
  refine ht.congr' ?_
  filter_upwards with n
  rw [← hoperator b]
  congr 1
  simpa [Q] using polynomialShiftOperator_tupleDifferenceIntPolynomial u v b n

theorem eventually_half_increment_le_tupleDifference
    {b : ℕ → ℝ} {D : ℕ} {u v : Fin D → ℕ}
    (hmoment0 : stretchedMoment (tupleDifference u v) 0 = 0)
    (hmoment1 : 0 < stretchedMoment (tupleDifference u v) 1)
    (hinc : ∀ᶠ n : ℕ in atTop, b n < b (n + 1))
    (hshift : ∀ r : ℕ, Tendsto
      (fun n => rapidIncrement b (n + r) / rapidIncrement b n)
      atTop (𝓝 1)) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) * rapidIncrement b n ≤
        (∑ i, b (n + u i)) - ∑ i, b (n + v i) := by
  have hlim := tendsto_tupleDifference_div_increment
    hmoment0 hmoment1.ne' hshift
  have hhalf : (1 / 2 : ℝ) <
      stretchedMoment (tupleDifference u v) 1 := by
    rw [stretchedMoment_tupleDifference] at hmoment1 ⊢
    simp only [pow_one] at hmoment1 ⊢
    have hreal : (∑ i, ((v i : ℕ) : ℝ)) < ∑ i, ((u i : ℕ) : ℝ) :=
      sub_pos.mp (by simpa using hmoment1)
    have hnat : (∑ i, v i) < ∑ i, u i := by exact_mod_cast hreal
    have hcast : ((∑ i, v i : ℕ) : ℝ) + 1 ≤ (∑ i, u i : ℕ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hnat)
    push_cast at hcast
    linarith
  have hevent := hlim.eventually_const_lt hhalf
  filter_upwards [hevent, hinc] with n hn hbn
  have hΔpos : 0 < rapidIncrement b n := by
    dsimp [rapidIncrement]
    linarith
  rw [lt_div_iff₀ hΔpos] at hn
  exact hn.le

theorem eventually_curvature_le_increment
    {b : ℕ → ℝ}
    (hinc : ∀ᶠ n : ℕ in atTop, b n < b (n + 1))
    (hκinc : Tendsto
      (fun n => rapidCurvature b n / rapidIncrement b n)
      atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, rapidCurvature b n ≤ rapidIncrement b n := by
  have hratio := hκinc.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hratio, hinc] with n hn hbn
  have hΔpos : 0 < rapidIncrement b n := by
    dsimp [rapidIncrement]
    linarith
  rw [div_lt_iff₀ hΔpos] at hn
  simpa using hn.le

theorem boundaryOffsetCandidate_eventually_first_or_second_gap
    {b : ℕ → ℝ} {D L : ℕ} (δ : Fin D → ℕ)
    (hLsq : (∑ i, (δ i : ℝ) ^ 2) < (L : ℝ) ^ 2)
    (hinc : ∀ᶠ n : ℕ in atTop, b n < b (n + 1))
    (hκpos : ∀ᶠ n : ℕ in atTop, 0 < rapidCurvature b n)
    (hκshift : ∀ r : ℕ, Tendsto
      (fun n => rapidCurvature b (n + r) / rapidCurvature b n)
      atTop (𝓝 1))
    (hκinc : Tendsto
      (fun n => rapidCurvature b n / rapidIncrement b n)
      atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, ∀ u : Fin D → Fin (2 * L + 1),
      boundaryOffsetCandidate δ u →
      0 ≤ stretchedMoment
        (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) 1 →
      (1 / 4 : ℝ) * rapidCurvature b n ≤
        (∑ i, b (n + (u i : ℕ))) - ∑ i, b (n + δ i + L) := by
  have hΔshift := tendsto_rapidIncrement_shift_ratio
    hinc hκpos hκshift hκinc
  have hκΔ := eventually_curvature_le_increment hinc hκinc
  rw [Filter.eventually_all]
  intro u
  by_cases hu : boundaryOffsetCandidate δ u ∧
      0 ≤ stretchedMoment
        (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) 1
  · rcases hu with ⟨hcandidate, hmomentNonneg⟩
    rcases hmomentNonneg.eq_or_lt with hzero | hpos
    · have hgap := boundaryOffsetCandidate_eventually_half_curvature_gap
        δ hLsq u hcandidate hzero.symm hκpos hκshift
      exact hgap.mono fun _ hn _ _ => hn
    · have hmoment0 : stretchedMoment
          (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) 0 = 0 := by
        rw [stretchedMoment_tupleDifference]
        simp
      have hgap := eventually_half_increment_le_tupleDifference
        hmoment0 hpos hinc hΔshift
      filter_upwards [hgap, hκΔ, hκpos] with n hn hκn hκpositive
      intro _ _
      calc
        (1 / 4 : ℝ) * rapidCurvature b n ≤
            (1 / 2 : ℝ) * rapidIncrement b n := by linarith
        _ ≤ (∑ i, b (n + (u i : ℕ))) - ∑ i, b (n + δ i + L) := by
          simpa [Nat.add_assoc] using hn
  · filter_upwards with n
    intro hcandidate hmoment
    exact (hu ⟨hcandidate, hmoment⟩).elim

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- A fixed positive source-sum displacement has first-difference cost, uniformly over a bounded
window. -/
theorem eventually_all_half_increment_le_boundedTupleDifference
    {b : ℕ → ℝ} {D L : ℕ} (δ : Fin D → ℕ)
    (hinc : ∀ᶠ n : ℕ in atTop, b n < b (n + 1))
    (hshift : ∀ r : ℕ, Tendsto
      (fun n => rapidIncrement b (n + r) / rapidIncrement b n)
      atTop (𝓝 1)) :
    ∀ᶠ n : ℕ in atTop, ∀ u : Fin D → Fin (2 * L + 1),
      0 < stretchedMoment
        (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) 1 →
      (1 / 2 : ℝ) * rapidIncrement b n ≤
        (∑ i, b (n + (u i : ℕ))) - ∑ i, b (n + δ i + L) := by
  rw [Filter.eventually_all]
  intro u
  by_cases hpos : 0 < stretchedMoment
      (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) 1
  · have hmoment0 : stretchedMoment
        (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) 0 = 0 := by
      rw [stretchedMoment_tupleDifference]
      simp
    exact (eventually_half_increment_le_tupleDifference
      hmoment0 hpos hinc hshift).mono fun _ hn _ => by
        simpa [Nat.add_assoc] using hn
  · filter_upwards with n
    exact fun hp => (hpos hp).elim

/-- Near-minimal tuples in every bounded active source-sum range are forced into the least source
class and one fixed coordinate window.  The first-moment gap removes larger source classes; the
second-moment gap then confines the least class. -/
theorem exists_eventually_bounded_rapidNearMinimizer
    {b : ℕ → ℝ}
    (hrecord : ∃ Q : ℕ, ∀ a c : ℕ, Q ≤ c → a < c →
      rapidIncrement b a < rapidIncrement b c)
    (hinc : ∀ᶠ n : ℕ in atTop, b n < b (n + 1))
    (hκpos : ∀ᶠ n : ℕ in atTop, 0 < rapidCurvature b n)
    (hκshift : ∀ r : ℕ, Tendsto
      (fun n => rapidCurvature b (n + r) / rapidCurvature b n)
      atTop (𝓝 1))
    (hκinc : Tendsto
      (fun n => rapidCurvature b n / rapidIncrement b n)
      atTop (𝓝 0))
    (hκlog : Tendsto
      (fun n => rapidCurvature b n / Real.log ((n : ℝ) + 2))
      atTop atTop)
    {D : ℕ} (hD : 0 < D) (δ : Fin D → ℕ) (A C : ℕ) :
    ∃ K : ℕ, ∀ᶠ q : ℕ in atTop, ∀ s : Fin D → ℕ,
      D * q + (∑ i, δ i) ≤ ∑ i, s i →
      (∑ i, s i) ≤ D * q + (∑ i, δ i) + C →
      tupleProfileValuation b s <
        tupleProfileValuation b (fun i => q + δ i) +
          (A : ℝ) * Real.log ((q : ℝ) + 2) →
      (∑ i, s i) = D * q + (∑ i, δ i) ∧ tupleInWindow q K s := by
  classical
  obtain ⟨Q, hQ⟩ := hrecord
  let Ctot := (∑ i, δ i) + C
  let Ksrc := Ctot + 1
  let L := Ksrc + 1
  have hCtotK : Ctot < Ksrc := by dsimp [Ksrc]; omega
  have hLpos : 0 < L := by dsimp [L, Ksrc]; omega
  have hΔshift := tendsto_rapidIncrement_shift_ratio
    hinc hκpos hκshift hκinc
  have hsourceBase := eventually_all_half_increment_le_boundedTupleDifference
    (b := b) (L := L) δ hinc hΔshift
  have hsource := (tendsto_sub_atTop_nat L).eventually hsourceBase
  have hκΔ := (tendsto_sub_atTop_nat L).eventually
    (eventually_curvature_le_increment hinc hκinc)
  have hlogGap := eventually_log_nat_add_two_lt_quarter_curvature_sub
    hκlog A L
  obtain ⟨Kconf, hconf⟩ := exists_eventually_bounded_rapidSameSumNearMinimizer
    ⟨Q, hQ⟩ hκpos hκshift hκlog hD δ A
  let K := max Ksrc Kconf
  refine ⟨K, ?_⟩
  filter_upwards [hsource, hκΔ, hlogGap, hconf,
    eventually_ge_atTop (max (Q + 1) (2 * L))] with
      q hsourceq hκΔq hlogq hconfq hq
  intro s hsumLower hsumUpper hnear
  have hLq : L ≤ q := by
    have : 2 * L ≤ q := (le_max_right _ _).trans hq
    omega
  have hsumEq : (∑ i, s i) = D * q + (∑ i, δ i) := by
    apply le_antisymm
    · by_contra hnot
      have hsumStrict : D * q + (∑ i, δ i) < ∑ i, s i :=
        Nat.lt_of_not_ge hnot
      have hsumBase : D * q ≤ ∑ i, s i := hsumLower.trans' (Nat.le_add_right _ _)
      have hsumTop : (∑ i, s i) ≤ D * q + Ctot := by
        simpa [Ctot, Nat.add_assoc] using hsumUpper
      obtain ⟨t, htsum, htwide, htval⟩ :
          ∃ t : Fin D → ℕ,
            (∑ i, t i) = ∑ i, s i ∧
            tupleInWindow q (Ksrc + 1) t ∧
            tupleProfileValuation b t ≤ tupleProfileValuation b s := by
        by_cases hout : ¬ tupleInWindow q Ksrc s
        · obtain ⟨t, htsum, htwide, _htout, htval⟩ :=
            exists_boundaryShell_of_rapidProfile_sum_bounds
              hD hCtotK (by
                have : Q + 1 ≤ q := (le_max_left _ _).trans hq
                exact this) hQ s hsumBase hsumTop hout
          exact ⟨t, htsum, htwide, htval⟩
        · have hin : tupleInWindow q Ksrc s := not_not.mp hout
          have hwide : tupleInWindow q (Ksrc + 1) s := by
            intro i
            have hi := hin i
            omega
          exact ⟨s, rfl, hwide, le_rfl⟩
      have htwideL : tupleInWindow q L t := by simpa [L] using htwide
      let u := shellOffset t hLq htwideL
      have hmoment1 : 0 < stretchedMoment
          (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) 1 := by
        rw [stretchedMoment_tupleDifference]
        simp only [pow_one]
        apply sub_pos.mpr
        norm_cast
        dsimp [u]
        rw [shellOffset_sum t hLq htwideL, htsum]
        have hDsplit : D * q = D * (q - L) + D * L := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hLq]
        have hoffset : (∑ i, δ i) + D * L <
            (∑ i, s i) - D * (q - L) := by
          apply Nat.lt_sub_of_add_lt
          omega
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        exact hoffset
      have hgap := hsourceq u hmoment1
      have hgapVal : (1 / 2 : ℝ) * rapidIncrement b (q - L) ≤
          tupleProfileValuation b t -
            tupleProfileValuation b (fun i => q + δ i) := by
        rw [tupleProfileValuation_shellOffset t hLq htwideL,
          tupleProfileValuation_witness_as_offset δ hLq]
        simpa [u, Nat.add_assoc] using hgap
      have hcurvGap : (1 / 4 : ℝ) * rapidCurvature b (q - L) ≤
          tupleProfileValuation b t -
            tupleProfileValuation b (fun i => q + δ i) := by
        calc
          (1 / 4 : ℝ) * rapidCurvature b (q - L) ≤
              (1 / 2 : ℝ) * rapidIncrement b (q - L) := by
                have hlogNonneg : 0 ≤
                    (A : ℝ) * Real.log ((q : ℝ) + 2) := by
                  exact mul_nonneg (Nat.cast_nonneg _)
                    (Real.log_nonneg (by
                      have hqnonneg : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
                      linarith))
                have hκnonneg : 0 ≤ rapidCurvature b (q - L) := by
                  linarith
                linarith
          _ ≤ tupleProfileValuation b t -
              tupleProfileValuation b (fun i => q + δ i) := hgapVal
      have hnearT : tupleProfileValuation b t -
          tupleProfileValuation b (fun i => q + δ i) <
            (A : ℝ) * Real.log ((q : ℝ) + 2) := by linarith
      linarith
    · exact hsumLower
  have hwindowConf := hconfq s hsumEq hnear
  refine ⟨hsumEq, fun i => ?_⟩
  have hi := hwindowConf i
  dsimp [K]
  omega

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- Karamata rapid variation for a sequence sampled on the natural lattice. -/
def RapidlyVarying (b : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 1 < c →
    Tendsto (fun n : ℕ => b ⌊c * (n : ℝ)⌋₊ / b n) atTop atTop

/-- Adjacent ratio one propagates to every fixed forward shift. -/
theorem tendsto_fixedShift_div_of_adjacentRatio_one
    {b : ℕ → ℝ}
    (hpos : ∀ᶠ n : ℕ in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop (𝓝 1))
    (r : ℕ) :
    Tendsto (fun n => b (n + r) / b n) atTop (𝓝 1) := by
  induction r with
  | zero =>
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hpos] with n hn
      simp [ne_of_gt hn]
  | succ r ih =>
      have hratioShift := hratio.comp (tendsto_add_atTop_nat r)
      have hprod := hratioShift.mul ih
      simpa only [one_mul] using hprod.congr' (by
        have hposShift := (tendsto_add_atTop_nat r).eventually hpos
        filter_upwards [hpos, hposShift] with n hn hnr
        have hn0 := ne_of_gt hn
        have hnr0 := ne_of_gt hnr
        simp only [Function.comp_apply, Nat.add_assoc]
        field_simp)

/-- Rapid variation remains true when the denominator is moved by a fixed lattice shift. -/
theorem rapidlyVarying_fixedShift_denominator
    {b : ℕ → ℝ}
    (hpos : ∀ᶠ n : ℕ in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop (𝓝 1))
    (hRV : RapidlyVarying b) (c : ℝ) (hc : 1 < c) (B : ℕ) :
    Tendsto (fun n : ℕ => b ⌊c * (n : ℝ)⌋₊ / b (n + B)) atTop atTop := by
  have hnum := hRV c hc
  have hden := tendsto_fixedShift_div_of_adjacentRatio_one hpos hratio B
  have hdenPos := hden.eventually_const_lt (show (0 : ℝ) < 1 by norm_num)
  have hdenTwo := hden.eventually_lt_const (show (1 : ℝ) < 2 by norm_num)
  have hposShift := (tendsto_add_atTop_nat B).eventually hpos
  rw [tendsto_atTop]
  intro M
  let M₀ := max M 0
  filter_upwards [hnum.eventually_gt_atTop (2 * M₀ + 1), hdenPos,
    hdenTwo, hpos, hposShift] with n hn hden0 hden2 hbn hbnB
  have hM : M ≤ M₀ := le_max_left _ _
  have hM₀ : 0 ≤ M₀ := le_max_right _ _
  have hquot : M <
      (b ⌊c * (n : ℝ)⌋₊ / b n) / (b (n + B) / b n) := by
    rw [lt_div_iff₀ hden0]
    nlinarith
  have heq :
      (b ⌊c * (n : ℝ)⌋₊ / b n) / (b (n + B) / b n) =
        b ⌊c * (n : ℝ)⌋₊ / b (n + B) := by
    field_simp [ne_of_gt hbn, ne_of_gt hbnB]
  rw [heq] at hquot
  exact hquot.le

/-- Curvature domination of logarithms forces the profile itself, at every shift at least two, to
dominate any fixed logarithmic allowance. -/
theorem eventually_const_mul_log_lt_profile_shift
    {b : ℕ → ℝ}
    (hpos : ∀ n, 0 < b n) (hmono : Monotone b)
    (hκlog : Tendsto
      (fun n => rapidCurvature b n / Real.log ((n : ℝ) + 2))
      atTop atTop)
    (A B : ℕ) (hB : 2 ≤ B) :
    ∀ᶠ q : ℕ in atTop,
      (A : ℝ) * Real.log ((q : ℝ) + 2) < b (q + B) := by
  have hlarge := hκlog.eventually_gt_atTop (2 * A + 1)
  filter_upwards [hlarge] with q hq
  have hlogPos : 0 < Real.log ((q : ℝ) + 2) := Real.log_pos (by
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    linarith)
  have hκLower : (2 * (A : ℝ) + 1) * Real.log ((q : ℝ) + 2) <
      rapidCurvature b q := by
    exact (lt_div_iff₀ hlogPos).mp (by simpa using hq)
  have hκUpper : rapidCurvature b q < 2 * b (q + 2) := by
    dsimp [rapidCurvature]
    have hbq := hpos q
    have hbq1 := hpos (q + 1)
    have hbqle : b q ≤ b (q + 2) := hmono (by omega)
    linarith
  have hshift : b (q + 2) ≤ b (q + B) := hmono (Nat.add_le_add_left hB q)
  nlinarith

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- Rapid variation excludes every positive convolution degree below the balanced witness degree. -/
theorem eventually_lowerDegree_rapidProfile_gap
    {b : ℕ → ℝ}
    (hpos : ∀ n, 0 < b n) (hmono : Monotone b)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop (𝓝 1))
    (hRV : RapidlyVarying b)
    (hκlog : Tendsto
      (fun n => rapidCurvature b n / Real.log ((n : ℝ) + 2))
      atTop atTop)
    {D : ℕ} (hD : 0 < D) (δ : Fin D → ℕ) (J A : ℕ) :
    ∀ᶠ q : ℕ in atTop, ∀ (d : ℕ), 0 < d → d < D → ∀ t : Fin d → ℕ,
      D * q ≤ (∑ i, t i) + J →
      tupleProfileValuation b (fun i => q + δ i) +
          (A : ℝ) * Real.log ((q : ℝ) + 2) <
        tupleProfileValuation b t := by
  classical
  let B := magnitudeOffsetMax δ + 2
  have hB : 2 ≤ B := by dsimp [B]; omega
  have hlog := eventually_const_mul_log_lt_profile_shift
    hpos hmono hκlog A B hB
  have hdEvent : ∀ d ∈ Finset.range D,
      ∀ᶠ q : ℕ in atTop, 0 < d → ∀ t : Fin d → ℕ,
        D * q ≤ (∑ i, t i) + J →
        tupleProfileValuation b (fun i => q + δ i) +
            (A : ℝ) * Real.log ((q : ℝ) + 2) <
          tupleProfileValuation b t := by
    intro d hdD
    by_cases hd0 : d = 0
    · subst d
      filter_upwards with q
      intro hzero
      omega
    · have hd : 0 < d := Nat.pos_of_ne_zero hd0
      have hdltD : d < D := Finset.mem_range.mp hdD
      let c : ℝ := ((D : ℝ) + (d : ℝ)) / (2 * (d : ℝ))
      have hden : 0 < (2 : ℝ) * (d : ℝ) := by positivity
      have hc : 1 < c := by
        rw [lt_div_iff₀ hden]
        have hdDreal : (d : ℝ) < (D : ℝ) := by exact_mod_cast hdltD
        linarith
      have hRVd := rapidlyVarying_fixedShift_denominator
        (Filter.Eventually.of_forall hpos) hratio hRV c hc B
      have hratioGap := hRVd.eventually_gt_atTop (D + 1)
      filter_upwards [hratioGap, hlog, eventually_ge_atTop (2 * J)] with
        q hrapid hlogq hq
      intro _hd t hsum
      have hfloorBound :
          d * ⌊c * (q : ℝ)⌋₊ + J ≤ D * q := by
        have hcpos : 0 ≤ c := (zero_lt_one.trans hc).le
        have hfloor := Nat.floor_le
          (mul_nonneg hcpos (Nat.cast_nonneg q))
        have hcEq : (d : ℝ) * c = ((D : ℝ) + (d : ℝ)) / 2 := by
          dsimp [c]
          field_simp
        have hDd : (1 : ℝ) ≤ (D : ℝ) - (d : ℝ) := by
          have hdDreal : (d : ℝ) + 1 ≤ (D : ℝ) := by
            exact_mod_cast (show d + 1 ≤ D by omega)
          linarith
        have hqJ : (2 : ℝ) * (J : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
        have hreal :
            ((d * ⌊c * (q : ℝ)⌋₊ + J : ℕ) : ℝ) ≤
              ((D * q : ℕ) : ℝ) := by
          push_cast
          calc
            (d : ℝ) * (⌊c * (q : ℝ)⌋₊ : ℝ) + (J : ℝ) ≤
                (d : ℝ) * (c * (q : ℝ)) + (J : ℝ) := by
                  gcongr
            _ = (((D : ℝ) + (d : ℝ)) / 2) * (q : ℝ) + (J : ℝ) := by
                  rw [← hcEq]
                  ring
            _ ≤ (D : ℝ) * (q : ℝ) := by nlinarith
        exact_mod_cast hreal
      have hfloorSum : d * ⌊c * (q : ℝ)⌋₊ ≤ ∑ i, t i := by omega
      have huniv : (Finset.univ : Finset (Fin d)).Nonempty := by
        obtain ⟨i₀⟩ := Fin.pos_iff_nonempty.mp hd
        exact ⟨i₀, Finset.mem_univ i₀⟩
      have hconst : (∑ _i : Fin d, ⌊c * (q : ℝ)⌋₊) ≤ ∑ i, t i := by
        simpa using hfloorSum
      obtain ⟨i, _hi, hindex⟩ := Finset.exists_le_of_sum_le huniv hconst
      have hwit : tupleProfileValuation b (fun i => q + δ i) ≤
          (D : ℝ) * b (q + B) := by
        rw [tupleProfileValuation]
        calc
          (∑ i, b (q + δ i)) ≤ ∑ _i : Fin D, b (q + B) := by
            apply Finset.sum_le_sum
            intro i hi
            apply hmono
            have hoff := offset_le_magnitudeOffsetMax δ i
            dsimp [B]
            omega
          _ = (D : ℝ) * b (q + B) := by simp
      have hfloorVal : b ⌊c * (q : ℝ)⌋₊ ≤ tupleProfileValuation b t := by
        have hmonoIndex : b ⌊c * (q : ℝ)⌋₊ ≤ b (t i) := hmono hindex
        have hsingle : b (t i) ≤ ∑ j : Fin d, b (t j) :=
          Finset.single_le_sum (fun j _ => (hpos (t j)).le)
            (Finset.mem_univ i)
        exact hmonoIndex.trans (by simpa [tupleProfileValuation] using hsingle)
      have hbden : 0 < b (q + B) := hpos _
      have hscaled : ((D + 1 : ℕ) : ℝ) * b (q + B) <
          b ⌊c * (q : ℝ)⌋₊ := by
        exact (lt_div_iff₀ hbden).mp (by simpa using hrapid)
      push_cast at hscaled
      linarith
  have hall : ∀ᶠ q : ℕ in atTop, ∀ d ∈ Finset.range D,
      0 < d → ∀ t : Fin d → ℕ,
        D * q ≤ (∑ i, t i) + J →
        tupleProfileValuation b (fun i => q + δ i) +
            (A : ℝ) * Real.log ((q : ℝ) + 2) <
          tupleProfileValuation b t := by
    rw [Filter.eventually_all_finset]
    exact hdEvent
  filter_upwards [hall] with q hq
  intro d hd hdD t hsum
  exact hq d (Finset.mem_range.mpr hdD) hd t hsum

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

set_option maxHeartbeats 800000 in
/-- Generic ADE bend extraction for a magnitude profile.  All profile-specific analysis is isolated
in the lower-degree separation and least-source confinement providers. -/
theorem exists_eventually_profile_bend_pair_of_positiveJetDegree
    {b : ℕ → ℝ}
    (hdegree : ∀ {D : ℕ} (hD : 0 < D) (δ : Fin D → ℕ) (J A : ℕ),
      ∀ᶠ q : ℕ in atTop, ∀ (d : ℕ), 0 < d → d < D → ∀ t : Fin d → ℕ,
        D * q ≤ (∑ i, t i) + J →
        tupleProfileValuation b (fun i => q + δ i) +
            (A : ℝ) * Real.log ((q : ℝ) + 2) <
          tupleProfileValuation b t)
    (hconfine : ∀ {D : ℕ} (hD : 0 < D) (δ : Fin D → ℕ) (A C : ℕ),
      ∃ K : ℕ, ∀ᶠ q : ℕ in atTop, ∀ s : Fin D → ℕ,
        D * q + (∑ i, δ i) ≤ ∑ i, s i →
        (∑ i, s i) ≤ D * q + (∑ i, δ i) + C →
        tupleProfileValuation b s <
          tupleProfileValuation b (fun i => q + δ i) +
            (A : ℝ) * Real.log ((q : ℝ) + 2) →
        (∑ i, s i) = D * q + (∑ i, δ i) ∧ tupleInWindow q K s)
    {n : ℕ} (F : PowerSeries ℂ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ = Real.exp (-b i))
    (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hrel : aeval (formalJets n F) Q = 0)
    (hDpos : 0 < magnitudeMaxJetDegree n Q) :
    ∃ D K C Q₀ : ℕ,
      D = magnitudeMaxJetDegree n Q ∧ 0 < D ∧ 0 < C ∧ ∀ q ≥ Q₀,
      ∃ ν₀ ν₁ : ℕ →₀ ℕ,
        ν₀ ≠ ν₁ ∧
        ν₀.sum (fun _ k => k) = D ∧ ν₁.sum (fun _ k => k) = D ∧
        ν₀.sum (fun i k => i * k) = ν₁.sum (fun i k => i * k) ∧
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
  have hCoeffMass : 0 < magnitudeCoefficientMass Q := by
    rw [magnitudeCoefficientMass]
    exact Finset.sum_pos' (fun _ _ => norm_nonneg _)
      ⟨anchor, ha, norm_pos_iff.mpr (MvPolynomial.mem_support_iff.mp ha)⟩
  have hAmass : 0 < Amass := by
    dsimp [Amass]
    exact mul_pos hCoeffMass (by positivity)
  have hdegEv := hdegree hD δ (J + Z) C
  obtain ⟨K, hconfEv⟩ := hconfine hD δ C Csum
  obtain ⟨Qdeg, hQdeg⟩ := Filter.eventually_atTop.mp hdegEv
  obtain ⟨Qconf, hQconf⟩ := Filter.eventually_atTop.mp hconfEv
  let Llevel := D * (Boff + 1) + anchor 0 + 1
  have hLlevel : 0 < Llevel := by dsimp [Llevel]; omega
  have hlargeEv : ∀ᶠ q : ℕ in atTop,
      Amass * (Llevel : ℝ) ^ E + 1 ≤ (q : ℝ) + 2 :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).eventually_ge_atTop
      (Amass * (Llevel : ℝ) ^ E + 1)
  obtain ⟨Qlarge, hQlarge⟩ := Filter.eventually_atTop.mp hlargeEv
  let Q₀ := max Qbal (max Qdeg (max Qconf
    (max Qlarge (max (2 * (J + Z) + 2) 2))))
  refine ⟨D, K, C, Q₀, hDmax, hD, by dsimp [C, E]; omega, fun q hq => ?_⟩
  have hqbal : Qbal ≤ q := by dsimp [Q₀] at hq; omega
  have hqdeg : Qdeg ≤ q := by dsimp [Q₀] at hq; omega
  have hqconf : Qconf ≤ q := by dsimp [Q₀] at hq; omega
  have hqlarge : Qlarge ≤ q := by dsimp [Q₀] at hq; omega
  have hqthreshold : 2 * (J + Z) + 2 ≤ q := by dsimp [Q₀] at hq; omega
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
  obtain ⟨ν₀, ν₁, hν₀, hw₀, hmin, hν₁, hw₁, hne, hgap⟩ :=
    exists_near_min_nonzero_aevalWeight_of_relation F Q hb hQint hrel hνw hww
  have hgapP : ν₁.sum (fun i k => (k : ℝ) * b i) <
      ν₀.sum (fun i k => (k : ℝ) * b i) + Real.log (P + 1) := by
    simpa [P, Amass, E, O, hDmax] using hgap
  have hlogpos : 0 < Real.log (P + 1) := Real.log_pos (by linarith)
  have hν₀near : ν₀.sum (fun i k => (k : ℝ) * b i) <
      (key s).sum (fun i k => (k : ℝ) * b i) + Real.log (P + 1) :=
    (hmin (key s) hνw hww).trans_lt (lt_add_of_pos_right _ hlogpos)
  have hν₁near : ν₁.sum (fun i k => (k : ℝ) * b i) <
      (key s).sum (fun i k => (k : ℝ) * b i) + Real.log (P + 1) :=
    hgapP.trans_le (add_le_add (hmin (key s) hνw hww) le_rfl)
  have hlogBound : Real.log (P + 1) ≤ (C : ℝ) * Real.log ((q : ℝ) + 2) := by
    have := log_polynomial_mass_le_mul_log hAmass.le hlevel (hQlarge q hqlarge)
    simpa [P, C, Amass, E] using this
  have hwitVal : (key s).sum (fun i k => (k : ℝ) * b i) =
      tupleProfileValuation b s := by
    rw [valuation_eq_key_sum, tupleProfileValuation]
  have hν₀near' : ν₀.sum (fun i k => (k : ℝ) * b i) <
      tupleProfileValuation b s + (C : ℝ) * Real.log ((q : ℝ) + 2) := by
    rw [hwitVal] at hν₀near
    linarith
  have hν₁near' : ν₁.sum (fun i k => (k : ℝ) * b i) <
      tupleProfileValuation b s + (C : ℝ) * Real.log ((q : ℝ) + 2) := by
    rw [hwitVal] at hν₁near
    linarith
  have count_eq_top (ν : ℕ →₀ ℕ)
      (hν : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n))
      (hnear : ν.sum (fun i k => (k : ℝ) * b i) <
        tupleProfileValuation b s + (C : ℝ) * Real.log ((q : ℝ) + 2)) :
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
        rw [show (∑ i, t i) = ν.sum (fun i k => i * k) by simpa [t] using hsumt]
        have hNsplit : N - Z + Z = N := Nat.sub_add_cancel hNZ.le
        omega
      have hνval : ν.sum (fun i k => (k : ℝ) * b i) =
          tupleProfileValuation b t := by
        rw [valuation_tupleOfFinsupp ν d (by rfl)]
        rfl
      have hsep := hQdeg q hqdeg d hd hdD t hmass
      rw [hνval] at hnear
      exact False.elim (by linarith)
  have hν₀count := count_eq_top ν₀ hν₀ hν₀near'
  have hν₁count := count_eq_top ν₁ hν₁ hν₁near'
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
      (hnear : ν.sum (fun i k => (k : ℝ) * b i) <
        tupleProfileValuation b s + (C : ℝ) * Real.log ((q : ℝ) + 2)) :
      ν.sum (fun i k => i * k) = D * q + (∑ i, δ i) ∧
        ∀ i, ν i ≠ 0 → q - K ≤ i ∧ i ≤ q + K := by
    let t : Fin D → ℕ := tupleOfFinsupp ν D hcount
    have hνval : ν.sum (fun i k => (k : ℝ) * b i) =
        tupleProfileValuation b t := by
      rw [valuation_tupleOfFinsupp ν D hcount]
      rfl
    have hsval : tupleProfileValuation b s =
        tupleProfileValuation b (fun i => q + δ i) := by rfl
    have hbounds := tuple_bounds ν hν hcount
    have hclose := hQconf q hqconf t hbounds.1 hbounds.2 (by
      rw [hνval, hsval] at hnear
      exact hnear)
    have hsumt := sum_tupleOfFinsupp ν D hcount
    constructor
    · rw [← hsumt]
      exact hclose.1
    · exact support_window_of_key_tupleInWindow t hclose.2
        (key_tupleOfFinsupp ν D hcount)
  have hν₀conf := confined ν₀ hν₀ hν₀count hν₀near'
  have hν₁conf := confined ν₁ hν₁ hν₁count hν₁near'
  have hdiff0 : 0 ≤ ν₁.sum (fun i k => (k : ℝ) * b i) -
      ν₀.sum (fun i k => (k : ℝ) * b i) := sub_nonneg.mpr (hmin ν₁ hν₁ hw₁)
  have hdiff : ν₁.sum (fun i k => (k : ℝ) * b i) -
        ν₀.sum (fun i k => (k : ℝ) * b i) <
      (C : ℝ) * Real.log ((q : ℝ) + 2) := by
    have : ν₁.sum (fun i k => (k : ℝ) * b i) -
        ν₀.sum (fun i k => (k : ℝ) * b i) < Real.log (P + 1) := by
      linarith
    exact this.trans_le hlogBound
  exact ⟨ν₀, ν₁, hne.symm, hν₀count, hν₁count,
    hν₀conf.1.trans hν₁conf.1.symm, hν₀conf.2, hν₁conf.2, hdiff0, hdiff⟩

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- Global-tail form of the admissibly rapid convex hypotheses.  Eventual profiles are reduced to
this form by a finite Taylor correction. -/
structure AdmissiblyRapidConvex (b : ℕ → ℝ) : Prop where
  positive : ∀ n, 0 < b n
  strictMono : StrictMono b
  curvaturePositive : ∀ᶠ n : ℕ in atTop, 0 < rapidCurvature b n
  adjacentRatioOne : Tendsto (fun n => b (n + 1) / b n) atTop (𝓝 1)
  curvatureShiftStable : ∀ r : ℕ, Tendsto
    (fun n => rapidCurvature b (n + r) / rapidCurvature b n) atTop (𝓝 1)
  curvatureOverIncrementZero : Tendsto
    (fun n => rapidCurvature b n / rapidIncrement b n) atTop (𝓝 0)
  rapidlyVarying : RapidlyVarying b
  curvatureOverLogAtTop : Tendsto
    (fun n => rapidCurvature b n / Real.log ((n : ℝ) + 2)) atTop atTop

/-- Every integer-normalized positive-degree ADE relation on an admissibly rapid convex profile has
an eventual logarithmic bend between two distinct, equal-degree, equal-source, fixed-window atoms. -/
theorem exists_eventually_rapidConvex_bend_pair_of_positiveJetDegree
    {b : ℕ → ℝ} (hbRapid : AdmissiblyRapidConvex b)
    {n : ℕ} (F : PowerSeries ℂ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ = Real.exp (-b i))
    (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hrel : aeval (formalJets n F) Q = 0)
    (hDpos : 0 < magnitudeMaxJetDegree n Q) :
    ∃ D K C Q₀ : ℕ,
      D = magnitudeMaxJetDegree n Q ∧ 0 < D ∧ 0 < C ∧ ∀ q ≥ Q₀,
      ∃ ν₀ ν₁ : ℕ →₀ ℕ,
        ν₀ ≠ ν₁ ∧
        ν₀.sum (fun _ k => k) = D ∧ ν₁.sum (fun _ k => k) = D ∧
        ν₀.sum (fun i k => i * k) = ν₁.sum (fun i k => i * k) ∧
        (∀ i, ν₀ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        (∀ i, ν₁ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        0 ≤ ν₁.sum (fun i k => (k : ℝ) * b i) -
          ν₀.sum (fun i k => (k : ℝ) * b i) ∧
        ν₁.sum (fun i k => (k : ℝ) * b i) -
            ν₀.sum (fun i k => (k : ℝ) * b i) <
          (C : ℝ) * Real.log ((q : ℝ) + 2) := by
  have hinc : ∀ᶠ n : ℕ in atTop, b n < b (n + 1) :=
    Filter.Eventually.of_forall fun n => hbRapid.strictMono (by omega)
  have hκpos := hbRapid.curvaturePositive
  have hrecord := exists_rapidIncrement_record_strict
    hinc hκpos hbRapid.curvatureOverLogAtTop
  apply exists_eventually_profile_bend_pair_of_positiveJetDegree
    (b := b)
    (fun hD δ J A => eventually_lowerDegree_rapidProfile_gap
      hbRapid.positive hbRapid.strictMono.monotone hbRapid.adjacentRatioOne
      hbRapid.rapidlyVarying hbRapid.curvatureOverLogAtTop hD δ J A)
    (fun hD δ A C => exists_eventually_bounded_rapidNearMinimizer
      hrecord hinc hκpos hbRapid.curvatureShiftStable
      hbRapid.curvatureOverIncrementZero hbRapid.curvatureOverLogAtTop hD δ A C)
    F hb Q hQint hrel hDpos

/-- A window-supported atom's natural source sum is its translated pattern moment. -/
theorem sourceSum_eq_atomWindowPattern_sum
    {q K D : ℕ} (hq : K ≤ q) {ν : ℕ →₀ ℕ}
    (hcount : ν.sum (fun _ k => k) = D)
    (hwin : ∀ i, ν i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) :
    ν.sum (fun i k => i * k) =
      ∑ j : Fin (2 * K + 1),
        (atomWindowPattern q K D ν j : ℕ) * (q - K + (j : ℕ)) := by
  have hval := valuation_eq_atomWindowPattern_sum
    (b := fun n => (n : ℝ)) hq hcount hwin
  have hleft : ((ν.sum (fun i k => i * k) : ℕ) : ℝ) =
      ν.sum (fun i k => (k : ℝ) * (i : ℝ)) := by
    rw [Finsupp.sum]
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hright :
      (((∑ j : Fin (2 * K + 1),
        (atomWindowPattern q K D ν j : ℕ) * (q - K + (j : ℕ)) : ℕ)) : ℝ) =
      ∑ j : Fin (2 * K + 1),
        (((atomWindowPattern q K D ν j : Fin (D + 1)) : ℕ) : ℝ) *
          ((q - K + (j : ℕ) : ℕ) : ℝ) := by
    push_cast
    rfl
  exact_mod_cast (hleft.trans (hval.trans hright.symm))

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- Persistent bounded-window bends with equal source sum yield one recurrent pair of multiplicity
patterns with equal mass and equal first moment. -/
theorem exists_persistent_atomWindow_curvatureResonance
    {b : ℕ → ℝ} {D K C Q₀ : ℕ}
    (hpairs : ∀ q ≥ Q₀,
      ∃ ν₀ ν₁ : ℕ →₀ ℕ,
        ν₀ ≠ ν₁ ∧
        ν₀.sum (fun _ k => k) = D ∧ ν₁.sum (fun _ k => k) = D ∧
        ν₀.sum (fun i k => i * k) = ν₁.sum (fun i k => i * k) ∧
        (∀ i, ν₀ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        (∀ i, ν₁ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        0 ≤ ν₁.sum (fun i k => (k : ℝ) * b i) -
          ν₀.sum (fun i k => (k : ℝ) * b i) ∧
        ν₁.sum (fun i k => (k : ℝ) * b i) -
            ν₀.sum (fun i k => (k : ℝ) * b i) <
          (C : ℝ) * Real.log ((q : ℝ) + 2)) :
    ∃ p₀ p₁ : Fin (2 * K + 1) → Fin (D + 1),
      p₀ ≠ p₁ ∧
      (∑ j, (p₀ j : ℕ)) = D ∧ (∑ j, (p₁ j : ℕ)) = D ∧
      (∑ j : Fin (2 * K + 1), (j : ℕ) * (p₀ j : ℕ)) =
        ∑ j : Fin (2 * K + 1), (j : ℕ) * (p₁ j : ℕ) ∧
      ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧ ∀ k,
        0 ≤ ∑ j : Fin (2 * K + 1),
          ((((p₁ j : ℕ) : ℤ) - ((p₀ j : ℕ) : ℤ) : ℤ) : ℝ) *
            b (q k + (j : ℕ)) ∧
        (∑ j : Fin (2 * K + 1),
          ((((p₁ j : ℕ) : ℤ) - ((p₀ j : ℕ) : ℤ) : ℤ) : ℝ) *
            b (q k + (j : ℕ))) <
          (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) := by
  classical
  let center : ℕ → ℕ := fun t => max Q₀ K + t
  let Good : ℕ → ((ℕ →₀ ℕ) × (ℕ →₀ ℕ)) → Prop := fun q ν =>
    ν.1 ≠ ν.2 ∧
      ν.1.sum (fun _ k => k) = D ∧ ν.2.sum (fun _ k => k) = D ∧
      ν.1.sum (fun i k => i * k) = ν.2.sum (fun i k => i * k) ∧
      (∀ i, ν.1 i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
      (∀ i, ν.2 i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
      0 ≤ ν.2.sum (fun i k => (k : ℝ) * b i) -
        ν.1.sum (fun i k => (k : ℝ) * b i) ∧
      ν.2.sum (fun i k => (k : ℝ) * b i) -
          ν.1.sum (fun i k => (k : ℝ) * b i) <
        (C : ℝ) * Real.log ((q : ℝ) + 2)
  have hex : ∀ t, ∃ ν, Good (center t) ν := by
    intro t
    obtain ⟨ν₀, ν₁, h⟩ := hpairs (center t) (by dsimp [center]; omega)
    exact ⟨(ν₀, ν₁), h⟩
  let chosen : ℕ → ((ℕ →₀ ℕ) × (ℕ →₀ ℕ)) := fun t => Classical.choose (hex t)
  have hchosen : ∀ t, Good (center t) (chosen t) :=
    fun t => Classical.choose_spec (hex t)
  let patternPair : ℕ →
      (Fin (2 * K + 1) → Fin (D + 1)) × (Fin (2 * K + 1) → Fin (D + 1)) :=
    fun t =>
      (atomWindowPattern (center t) K D (chosen t).1,
        atomWindowPattern (center t) K D (chosen t).2)
  obtain ⟨p, hpInf⟩ := Finite.exists_infinite_fiber patternPair
  have hpSet : (patternPair ⁻¹' {p}).Infinite := Set.infinite_coe_iff.mp hpInf
  have hpUnbounded : ∀ N, ∃ t > N, patternPair t = p := by
    intro N
    obtain ⟨t, htmem, hNt⟩ := hpSet.exists_gt N
    exact ⟨t, hNt, by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using htmem⟩
  obtain ⟨s, hsMono, hsPattern⟩ := Nat.exists_strictMono_subsequence hpUnbounded
  let q : ℕ → ℕ := fun k => center (s k) - K
  have hcenterK : ∀ t, K ≤ center t := by intro t; dsimp [center]; omega
  have hqTop : Tendsto q atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hsMono.tendsto_atTop
    exact Filter.Eventually.of_forall fun k => by dsimp [q, center]; omega
  have hpattern₀ : ∀ k,
      atomWindowPattern (center (s k)) K D (chosen (s k)).1 = p.1 := by
    intro k
    exact congrArg Prod.fst (hsPattern k)
  have hpattern₁ : ∀ k,
      atomWindowPattern (center (s k)) K D (chosen (s k)).2 = p.2 := by
    intro k
    exact congrArg Prod.snd (hsPattern k)
  have hpne : p.1 ≠ p.2 := by
    intro heq
    rcases hchosen (s 0) with ⟨hne, hcount₀, hcount₁, _hsource,
      hwin₀, hwin₁, _hgap0, _hgap⟩
    exact hne (atomWindowPattern_injective_on_window (hcenterK (s 0))
      hcount₀ hcount₁ hwin₀ hwin₁
      ((hpattern₀ 0).trans (heq.trans (hpattern₁ 0).symm)))
  have hpsum₀ : (∑ j, (p.1 j : ℕ)) = D := by
    rcases hchosen (s 0) with ⟨_hne, hcount₀, _hcount₁, _hsource,
      hwin₀, _hwin₁, _hgap0, _hgap⟩
    rw [← hpattern₀ 0]
    exact sum_atomWindowPattern_eq_count (hcenterK (s 0)) hcount₀ hwin₀
  have hpsum₁ : (∑ j, (p.2 j : ℕ)) = D := by
    rcases hchosen (s 0) with ⟨_hne, _hcount₀, hcount₁, _hsource,
      _hwin₀, hwin₁, _hgap0, _hgap⟩
    rw [← hpattern₁ 0]
    exact sum_atomWindowPattern_eq_count (hcenterK (s 0)) hcount₁ hwin₁
  have hpweight :
      (∑ j : Fin (2 * K + 1), (j : ℕ) * (p.1 j : ℕ)) =
        ∑ j : Fin (2 * K + 1), (j : ℕ) * (p.2 j : ℕ) := by
    rcases hchosen (s 0) with ⟨_hne, hcount₀, hcount₁, hsource,
      hwin₀, hwin₁, _hgap0, _hgap⟩
    have hv₀ := sourceSum_eq_atomWindowPattern_sum
      (hcenterK (s 0)) hcount₀ hwin₀
    have hv₁ := sourceSum_eq_atomWindowPattern_sum
      (hcenterK (s 0)) hcount₁ hwin₁
    rw [hpattern₀ 0] at hv₀
    rw [hpattern₁ 0] at hv₁
    have htranslated := hv₀.symm.trans (hsource.trans hv₁)
    have hexpand (a : Fin (2 * K + 1) → Fin (D + 1)) :
        (∑ j : Fin (2 * K + 1),
          (a j : ℕ) * (center (s 0) - K + (j : ℕ))) =
        (center (s 0) - K) * (∑ j, (a j : ℕ)) +
          ∑ j : Fin (2 * K + 1), (j : ℕ) * (a j : ℕ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hexpand p.1, hexpand p.2, hpsum₀, hpsum₁] at htranslated
    omega
  refine ⟨p.1, p.2, hpne, hpsum₀, hpsum₁, hpweight, q, hqTop, fun k => ?_⟩
  rcases hchosen (s k) with ⟨_hne, hcount₀, hcount₁, _hsource,
    hwin₀, hwin₁, hgap0, hgap⟩
  have hv₀ := valuation_eq_atomWindowPattern_sum (b := b)
    (hcenterK (s k)) hcount₀ hwin₀
  have hv₁ := valuation_eq_atomWindowPattern_sum (b := b)
    (hcenterK (s k)) hcount₁ hwin₁
  have hcenter : center (s k) = q k + K :=
    (Nat.sub_add_cancel (hcenterK (s k))).symm
  have hdiff :
      (∑ j : Fin (2 * K + 1),
          ((((p.2 j : ℕ) : ℤ) - ((p.1 j : ℕ) : ℤ) : ℤ) : ℝ) *
            b (q k + (j : ℕ))) =
        (chosen (s k)).2.sum (fun i m => (m : ℝ) * b i) -
          (chosen (s k)).1.sum (fun i m => (m : ℝ) * b i) := by
    rw [hv₀, hv₁, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hidx : center (s k) - K + (j : ℕ) = q k + (j : ℕ) := rfl
    rw [hidx, hpattern₀ k, hpattern₁ k]
    push_cast
    ring
  constructor
  · rw [hdiff]
    exact hgap0
  · rw [hdiff]
    simpa only [hcenter] using hgap

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- Positive-degree integer ADE relations force one fixed nonzero curvature polynomial to return to
logarithmic width along an unbounded sequence. -/
theorem exists_rapidConvex_curvatureResonance_of_positiveJetDegree_relation
    {b : ℕ → ℝ} (hbRapid : AdmissiblyRapidConvex b)
    {n : ℕ} (F : PowerSeries ℂ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ = Real.exp (-b i))
    (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hrel : aeval (formalJets n F) Q = 0)
    (hDpos : 0 < magnitudeMaxJetDegree n Q) :
    ∃ R : Polynomial ℤ, ∃ C K : ℕ, ∃ q : ℕ → ℕ,
      R ≠ 0 ∧ Tendsto q atTop atTop ∧ ∀ k,
        0 ≤ ∑ r ∈ Finset.range (R.natDegree + 1),
          (R.coeff r : ℝ) * rapidCurvature b (q k + r) ∧
        (∑ r ∈ Finset.range (R.natDegree + 1),
          (R.coeff r : ℝ) * rapidCurvature b (q k + r)) <
          (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) := by
  obtain ⟨D, K, C, Q₀, _hDmax, _hD, _hC, hpairs⟩ :=
    exists_eventually_rapidConvex_bend_pair_of_positiveJetDegree
      hbRapid F hb Q hQint hrel hDpos
  obtain ⟨p₀, p₁, hpne, hsum₀, hsum₁, hweight, q, hq, hdefect⟩ :=
    exists_persistent_atomWindow_curvatureResonance hpairs
  obtain ⟨R, hR, _hq, hres⟩ :=
    exists_curvaturePolynomial_resonance_of_persistent_atomPattern
      (M := 2 * K + 1) (by omega) hpne hsum₀ hsum₁ hweight hq hdefect
  exact ⟨R, C, K, q, hR, hq, hres⟩

/-- Differential algebraicity of a smooth entire realization forces recurrent curvature
resonance. -/
theorem exists_rapidConvex_curvatureResonance_of_differentiallyAlgebraic
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℝ} (hbRapid : AdmissiblyRapidConvex b)
    (hb : ∀ i, ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    (hDA : DifferentiallyAlgebraic f) :
    ∃ R : Polynomial ℤ, ∃ C K : ℕ, ∃ q : ℕ → ℕ,
      R ≠ 0 ∧ Tendsto q atTop atTop ∧ ∀ k,
        0 ≤ ∑ r ∈ Finset.range (R.natDegree + 1),
          (R.coeff r : ℝ) * rapidCurvature b (q k + r) ∧
        (∑ r ∈ Finset.range (R.natDegree + 1),
          (R.coeff r : ℝ) * rapidCurvature b (q k + r)) <
          (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) := by
  obtain ⟨n, P, hP, hPfun⟩ := hDA
  have hjz : jetFun f n P = 0 := by
    funext z
    exact hPfun z
  have hformal : aeval (formalJets n (taylorPS f)) P = 0 := by
    rw [← taylorPS_jetFun f n hf P, hjz,
      show (0 : ℂ → ℂ) = fun _ => (0 : ℂ) from rfl, taylorPS_const, map_zero]
  obtain ⟨n', Q, hQ, hQint, hrel⟩ := formal_mahler_integer_normalization hP hformal
  have hDpos := magnitudeMaxJetDegree_pos_of_integer_relation
    (taylorPS f) hb Q hQ hQint hrel
  exact exists_rapidConvex_curvatureResonance_of_positiveJetDegree_relation
    hbRapid (taylorPS f) hb Q hQint hrel hDpos

/-- Logarithmic shift-separation of the curvature excludes every algebraic differential equation. -/
theorem hypertranscendental_of_rapidConvex_curvatureShiftSeparated
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℝ} (hbRapid : AdmissiblyRapidConvex b)
    (hb : ∀ i, ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    (hsep : LogarithmicallyShiftSeparated (rapidCurvature b)) :
    Hypertranscendental f := by
  intro hDA
  obtain ⟨R, C, K, q, hR, hq, hres⟩ :=
    exists_rapidConvex_curvatureResonance_of_differentiallyAlgebraic
      hf hbRapid hb hDA
  have hsepq := (hsep R hR).comp hq
  have hlarge := hsepq.eventually_gt_atTop ((2 : ℝ) * C + 1)
  obtain ⟨k, hk, hqK⟩ := (hlarge.and (hq.eventually_ge_atTop K)).exists
  let S : ℝ := ∑ r ∈ Finset.range (R.natDegree + 1),
    (R.coeff r : ℝ) * rapidCurvature b (q k + r)
  have hS0 : 0 ≤ S := (hres k).1
  have hSupper : S < (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) :=
    (hres k).2
  have hlogBound := log_nat_add_shift_le_two_mul_log hqK
  have hlogPos : 0 < Real.log ((q k : ℝ) + 2) := Real.log_pos (by
    have hq0 : (0 : ℝ) ≤ q k := Nat.cast_nonneg _
    linarith)
  have hratioUpper : |S| / Real.log ((q k : ℝ) + 2) < (2 : ℝ) * C := by
    rw [abs_of_nonneg hS0, div_lt_iff₀ hlogPos]
    calc
      S < (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) := hSupper
      _ ≤ (C : ℝ) * (2 * Real.log ((q k : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hlogBound (by positivity)
      _ = (2 : ℝ) * C * Real.log ((q k : ℝ) + 2) := by ring
  change (2 : ℝ) * C + 1 < |S| / Real.log ((q k : ℝ) + 2) at hk
  linarith

end

end GaloisForLFunctions
