import GaloisForLFunctions.HTGeometry.BesselOrderMeromorphic
import GaloisForLFunctions.HTGeometry.RationalExponentialProgressionGrowth
import GaloisForLFunctions.Bottcher.DiskAlgebraicContinuation

open Filter Polynomial Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private def shiftedOuterCoeff (q : Polynomial (Polynomial ℂ)) (i : ℕ) : Polynomial ℂ :=
  (q.coeff i).comp (Polynomial.X + Polynomial.C 1)

private theorem shiftedOuterCoeff_eval (q : Polynomial (Polynomial ℂ)) (i n : ℕ) :
    (shiftedOuterCoeff q i).eval (n : ℂ) = (q.coeff i).eval ((n : ℂ) + 1) := by
  simp [shiftedOuterCoeff, Polynomial.eval_comp]

private theorem shiftedOuterCoeff_ne_zero {q : Polynomial (Polynomial ℂ)} {i : ℕ}
    (hi : q.coeff i ≠ 0) : shiftedOuterCoeff q i ≠ 0 := by
  intro hzero
  rcases Polynomial.comp_eq_zero_iff.mp hzero with h | h
  · exact hi h
  · have hnot : Polynomial.X + Polynomial.C (1 : ℂ) ≠
        Polynomial.C ((Polynomial.X + Polynomial.C (1 : ℂ)).coeff 0) := by
      intro heq
      have := congrArg (fun p : Polynomial ℂ => p.coeff 1) heq
      simpa at this
    exact hnot h.2

private theorem eventually_shiftedOuterCoeff_eval_ne_zero
    {q : Polynomial (Polynomial ℂ)} {i : ℕ} (hi : q.coeff i ≠ 0) :
    ∀ᶠ n : ℕ in atTop, (shiftedOuterCoeff q i).eval (n : ℂ) ≠ 0 := by
  let Q := shiftedOuterCoeff q i
  have hQ : Q ≠ 0 := shiftedOuterCoeff_ne_zero hi
  have hld : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hlimReal := PolyAsymptotics.tendsto_eval_div_pow_natDegree Q
  have hlimNat : Tendsto
      (fun n : ℕ => Q.eval (n : ℂ) / (n : ℂ) ^ Q.natDegree)
      atTop (nhds Q.leadingCoeff) :=
    hlimReal.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlimNat.eventually_ne hld] with n hn hzero
  apply hn
  rw [hzero, zero_div]

/-- A polynomial relation whose coefficients are polynomials in the positive integer coordinate
forces polynomial growth of its roots. -/
theorem exists_eventually_norm_le_polynomial_of_eval₂_relation
    {q : Polynomial (Polynomial ℂ)} (hq : q ≠ 0)
    {y : ℕ → ℂ}
    (hy : ∀ n : ℕ,
      q.eval₂ (Polynomial.evalRingHom ((n : ℂ) + 1)) (y n) = 0) :
    ∃ (C : ℝ) (d : ℕ), 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ‖y n‖ ≤ C * ((n : ℝ) + 1) ^ d := by
  classical
  let N := q.natDegree
  let P : ℕ → Polynomial ℂ := fun i => shiftedOuterCoeff q i
  let d : ℕ := ∑ i ∈ Finset.range N, (P i).natDegree
  let S : ℝ := ∑ i ∈ Finset.range N, rationalExpPolynomialCoeffNormSum (P i)
  have htop : q.coeff N ≠ 0 := by
    dsimp [N]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq
  have hPN : P N ≠ 0 := shiftedOuterCoeff_ne_zero htop
  obtain ⟨B, hB, hBinv⟩ := exists_eventually_norm_inv_polynomial_eval_natCast_le hPN
  have hPne : ∀ᶠ n : ℕ in atTop, (P N).eval (n : ℂ) ≠ 0 :=
    eventually_shiftedOuterCoeff_eval_ne_zero htop
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨1 + S * B, d, by positivity, ?_⟩
  filter_upwards [hBinv, hPne] with n hInv hLead
  have hroot : ∑ i ∈ Finset.range (N + 1), (P i).eval (n : ℂ) * (y n) ^ i = 0 := by
    have h := hy n
    rw [Polynomial.eval₂_eq_sum_range] at h
    simpa [P, shiftedOuterCoeff_eval, N] using h
  have hcauchy := Bottcher.norm_le_of_fibre_root hLead hroot
  have hsum : ∑ i ∈ Finset.range N, ‖(P i).eval (n : ℂ)‖ ≤
      S * ((n : ℝ) + 1) ^ d := by
    calc
      ∑ i ∈ Finset.range N, ‖(P i).eval (n : ℂ)‖ ≤
          ∑ i ∈ Finset.range N,
            rationalExpPolynomialCoeffNormSum (P i) *
              ((n : ℝ) + 1) ^ (P i).natDegree := by
        apply Finset.sum_le_sum
        intro i hi
        exact norm_polynomial_eval_natCast_le (P i) n
      _ ≤ ∑ i ∈ Finset.range N,
            rationalExpPolynomialCoeffNormSum (P i) * ((n : ℝ) + 1) ^ d := by
        apply Finset.sum_le_sum
        intro i hi
        have hideg : (P i).natDegree ≤ d := by
          dsimp [d]
          exact Finset.single_le_sum (fun j _ => Nat.zero_le (P j).natDegree) hi
        have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 := by
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hbase hideg)
          (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      _ = S * ((n : ℝ) + 1) ^ d := by
        rw [Finset.sum_mul]
  have hdenInv : ‖(P N).eval (n : ℂ)‖⁻¹ ≤ B := by
    simpa only [norm_inv] using hInv
  have hquot : (∑ i ∈ Finset.range N, ‖(P i).eval (n : ℂ)‖) /
        ‖(P N).eval (n : ℂ)‖ ≤ S * B * ((n : ℝ) + 1) ^ d := by
    rw [div_eq_mul_inv]
    calc
      (∑ i ∈ Finset.range N, ‖(P i).eval (n : ℂ)‖) *
          ‖(P N).eval (n : ℂ)‖⁻¹ ≤
          (S * ((n : ℝ) + 1) ^ d) * B := by
        exact mul_le_mul hsum hdenInv (inv_nonneg.mpr (norm_nonneg _))
          (mul_nonneg hS (pow_nonneg (by positivity) _))
      _ = S * B * ((n : ℝ) + 1) ^ d := by ring
  calc
    ‖y n‖ ≤ 1 + (∑ i ∈ Finset.range N, ‖(P i).eval (n : ℂ)‖) /
        ‖(P N).eval (n : ℂ)‖ := hcauchy
    _ ≤ 1 + S * B * ((n : ℝ) + 1) ^ d := by linarith
    _ ≤ (1 + S * B) * ((n : ℝ) + 1) ^ d := by
      have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hpow : 1 ≤ ((n : ℝ) + 1) ^ d := one_le_pow₀ hbase
      nlinarith [mul_nonneg hS hB.le]

private theorem eval₂_polyToAnalytic_analyticFunction_val {U : Set ℂ}
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (q : Polynomial (Polynomial ℂ)) :
    (q.eval₂ (Bottcher.polyToAnalytic U)
        (analyticFunctionElement f hf) : Bottcher.analyticSubring U).val =
      (↑(fun z => q.eval₂ (Polynomial.evalRingHom z) (f z)) :
        Germ (Filter.principal U) ℂ) := by
  rw [show ((q.eval₂ (Bottcher.polyToAnalytic U)
        (analyticFunctionElement f hf) : Bottcher.analyticSubring U).val) =
      (Bottcher.analyticSubring U).subtype
        (q.eval₂ (Bottcher.polyToAnalytic U) (analyticFunctionElement f hf)) from rfl]
  rw [Polynomial.hom_eval₂ q (Bottcher.polyToAnalytic U)
    (Bottcher.analyticSubring U).subtype (analyticFunctionElement f hf)]
  have hpi : (fun z => q.eval₂ (Polynomial.evalRingHom z) (f z)) =
      q.eval₂ (RingHom.pi (fun z : ℂ => Polynomial.evalRingHom z)) f := by
    funext z
    change Polynomial.eval₂ (Polynomial.evalRingHom z) (f z) q =
      Pi.evalRingHom (fun _ : ℂ => ℂ) z
        (q.eval₂ (RingHom.pi fun z : ℂ => Polynomial.evalRingHom z) f)
    rw [Polynomial.hom_eval₂ q
      (RingHom.pi (fun z : ℂ => Polynomial.evalRingHom z))
      (Pi.evalRingHom (fun _ : ℂ => ℂ) z) f]
    rfl
  rw [hpi]
  rw [show (↑(q.eval₂ (RingHom.pi (fun z : ℂ => Polynomial.evalRingHom z)) f) :
        Germ (Filter.principal U) ℂ) =
      Germ.coeRingHom (Filter.principal U)
        (q.eval₂ (RingHom.pi (fun z : ℂ => Polynomial.evalRingHom z)) f) from rfl]
  rw [Polynomial.hom_eval₂ q
    (RingHom.pi (fun z : ℂ => Polynomial.evalRingHom z))
    (Germ.coeRingHom (Filter.principal U)) f]
  rfl

private theorem eqOn_eval₂_of_eval₂_polyToMero_zero {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (q : Polynomial (Polynomial ℂ))
    (hzero : q.eval₂ (Bottcher.polyToMero U) (analyticMeroElement f hf) = 0) :
    Set.EqOn (fun z => q.eval₂ (Polynomial.evalRingHom z) (f z)) 0 U := by
  have hrewrite : q.eval₂ (Bottcher.polyToMero U) (analyticMeroElement f hf) =
      algebraMap (Bottcher.analyticSubring U) (Bottcher.meroField U)
        (q.eval₂ (Bottcher.polyToAnalytic U) (analyticFunctionElement f hf)) := by
    rw [Polynomial.hom_eval₂ q (Bottcher.polyToAnalytic U)
      (algebraMap (Bottcher.analyticSubring U) (Bottcher.meroField U))
      (analyticFunctionElement f hf)]
    rfl
  rw [hrewrite, Bottcher.meroField_algebraMap_eq_zero_iff U hUo hUc hUne] at hzero
  have hval := eval₂_polyToAnalytic_analyticFunction_val hf q
  rw [hzero, ZeroMemClass.coe_zero] at hval
  have hgerm :
      (↑(fun z => q.eval₂ (Polynomial.evalRingHom z) (f z)) :
        Germ (Filter.principal U) ℂ) = 0 := hval.symm
  rw [← Germ.coe_zero, Germ.coe_eq] at hgerm
  exact fun z hz => Filter.eventually_principal.mp hgerm z hz

/-- The fixed-argument modified-Bessel order carrier is transcendental over the rational
coordinate field.  Algebraicity would impose a polynomial root bound on positive integers,
contradicting the recurrence's factorial lower growth. -/
theorem modifiedBesselKOrderMero_transcendental (s : ℝ) (hs : 0 < s) :
    letI := (Bottcher.ratfuncToMero (Set.univ : Set ℂ) isOpen_univ
      isPreconnected_univ Set.univ_nonempty Set.infinite_univ).toAlgebra
    Transcendental (RatFunc ℂ) (modifiedBesselKOrderMero s hs) := by
  letI algK : Algebra (RatFunc ℂ) (Bottcher.meroField (Set.univ : Set ℂ)) :=
    (Bottcher.ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ).toAlgebra
  letI algA : Algebra (Polynomial ℂ) (Bottcher.meroField (Set.univ : Set ℂ)) :=
    (Bottcher.polyToMero Set.univ).toAlgebra
  haveI hst : IsScalarTower (Polynomial ℂ) (RatFunc ℂ)
      (Bottcher.meroField (Set.univ : Set ℂ)) := by
    apply IsScalarTower.of_algebraMap_eq
    intro p
    show Bottcher.polyToMero Set.univ p =
      Bottcher.ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
    rw [Bottcher.ratfuncToMero_algebraMap_polynomial]
  show ¬ IsAlgebraic (RatFunc ℂ) (modifiedBesselKOrderMero s hs)
  rw [← IsFractionRing.isAlgebraic_iff (Polynomial ℂ) (RatFunc ℂ)
    (Bottcher.meroField (Set.univ : Set ℂ))]
  rintro ⟨q, hq, hqe⟩
  rw [aeval_def] at hqe
  have halg : algebraMap (Polynomial ℂ) (Bottcher.meroField (Set.univ : Set ℂ)) =
      Bottcher.polyToMero Set.univ := rfl
  rw [halg] at hqe
  have hrel : ∀ z : ℂ,
      q.eval₂ (Polynomial.evalRingHom z) (modifiedBesselKOrder s z) = 0 := by
    have hEqOn := eqOn_eval₂_of_eval₂_polyToMero_zero isOpen_univ isPreconnected_univ
      Set.univ_nonempty (analyticOnNhd_modifiedBesselKOrder hs) q hqe
    exact fun z => hEqOn (Set.mem_univ z)
  obtain ⟨C, d, hC, hupper⟩ :=
    exists_eventually_norm_le_polynomial_of_eval₂_relation hq
      (y := fun n => modifiedBesselKOrder s ((n : ℂ) + 1)) (fun n => hrel _)
  apply realModifiedBesselKOrder_not_eventually_polynomialExponential_upper
    hs (by norm_num : (1 : ℝ) ≤ 1) hC (by norm_num : (0 : ℝ) < 1) d
  filter_upwards [hupper] with n hn
  have hcast : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, modifiedBesselKOrder_ofReal hs, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (realModifiedBesselKOrder_pos hs ((n : ℝ) + 1))] at hn
  simpa [one_pow, add_comm] using hn

end

end GaloisForLFunctions.HTGeometry
