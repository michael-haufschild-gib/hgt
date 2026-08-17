import GaloisForLFunctions.RHTower.BakerGeneralProof.PolynomialAuxiliaryExpansion

/-!
# Closed scalar bounds for the full Baker component jets

The analytic boundary sum and the conjugate sum of a full component jet are finite expressions in
the houses of four algebraic families: the exponential-base scale, the component eigenvalues, the
Siegel coefficients, and the natural sample.  Each family has a uniform bound depending only on the
solved relation and the construction parameters, so both sums collapse to closed products of
powers.  These are the scalar quantities the long extrapolation compares.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- Total house of all component eigen-coordinates. -/
noncomputable def SolvedRelation.eigenCoordinateHouseSum
    (R : SolvedRelation) (c : ℤ) : ℝ :=
  ∑ dir : R.Direction, ∑ i : Fin R.n, house (R.componentEigenCoordinate c dir i)

theorem SolvedRelation.eigenCoordinateHouseSum_nonneg
    (R : SolvedRelation) (c : ℤ) : 0 ≤ R.eigenCoordinateHouseSum c :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => house_nonneg _

/-- Uniform house bound for every component eigenvalue on a bounded exponent box. -/
noncomputable def SolvedRelation.eigenHouseBound
    (R : SolvedRelation) (c : ℤ) (V : ℕ) : ℝ :=
  1 + (V : ℝ) * R.eigenCoordinateHouseSum c

theorem SolvedRelation.one_le_eigenHouseBound
    (R : SolvedRelation) (c : ℤ) (V : ℕ) : 1 ≤ R.eigenHouseBound c V := by
  unfold SolvedRelation.eigenHouseBound
  have : 0 ≤ (V : ℝ) * R.eigenCoordinateHouseSum c :=
    mul_nonneg (Nat.cast_nonneg _) (R.eigenCoordinateHouseSum_nonneg c)
  linarith

theorem SolvedRelation.house_componentEigenvalue_le
    (R : SolvedRelation) (c : ℤ) (dir : R.Direction) {V : ℕ} (m : R.ExponentialColumn V) :
    house (R.componentEigenvalue c dir m) ≤ R.eigenHouseBound c V := by
  have heq : R.componentEigenvalue c dir m =
      ∑ i : Fin R.n, (m i : R.CoefficientField) * R.componentEigenCoordinate c dir i := rfl
  have hstep : house (R.componentEigenvalue c dir m) ≤
      ∑ i : Fin R.n, house ((m i : R.CoefficientField) * R.componentEigenCoordinate c dir i) := by
    rw [heq]
    exact house_sum_le_sum_house Finset.univ
      (fun i => (m i : R.CoefficientField) * R.componentEigenCoordinate c dir i)
  refine hstep.trans ?_
  have hterm : ∀ i : Fin R.n,
      house ((m i : R.CoefficientField) * R.componentEigenCoordinate c dir i) ≤
        (V : ℝ) * house (R.componentEigenCoordinate c dir i) := by
    intro i
    have hcast : ((m i : ℕ) : R.CoefficientField) * R.componentEigenCoordinate c dir i =
        ((m i : ℕ) : R.CoefficientField) * R.componentEigenCoordinate c dir i := rfl
    rw [hcast, house_nat_mul]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast (m i).isLt.le) (house_nonneg _)
  refine le_trans (Finset.sum_le_sum fun i _ => hterm i) ?_
  rw [← Finset.mul_sum]
  unfold SolvedRelation.eigenHouseBound SolvedRelation.eigenCoordinateHouseSum
  have hle : (∑ i : Fin R.n, house (R.componentEigenCoordinate c dir i)) ≤
      ∑ e : R.Direction, ∑ i : Fin R.n, house (R.componentEigenCoordinate c e i) :=
    Finset.single_le_sum
      (f := fun e : R.Direction => ∑ i : Fin R.n, house (R.componentEigenCoordinate c e i))
      (fun e _ => Finset.sum_nonneg fun i _ => house_nonneg _) (Finset.mem_univ dir)
  nlinarith [Nat.cast_nonneg (α := ℝ) V,
    Finset.sum_nonneg (f := fun i : Fin R.n => house (R.componentEigenCoordinate c dir i))
      (s := Finset.univ) (fun i _ => house_nonneg _)]

/-- Total modulus of the chosen logarithms. -/
noncomputable def SolvedRelation.lambdaNormSum (R : SolvedRelation) : ℝ :=
  ∑ i, ‖R.lambda i‖

theorem SolvedRelation.lambdaNormSum_nonneg (R : SolvedRelation) : 0 ≤ R.lambdaNormSum :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem SolvedRelation.norm_exponentialFrequency_le
    (R : SolvedRelation) {V : ℕ} (m : R.ExponentialColumn V) :
    ‖R.exponentialFrequency m‖ ≤ (V : ℝ) * R.lambdaNormSum := by
  unfold SolvedRelation.exponentialFrequency SolvedRelation.lambdaNormSum
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (m i).isLt.le) (norm_nonneg _)


theorem house_natCast_field {K : Type*} [Field K] [NumberField K] (n : ℕ) :
    house ((n : K)) = (n : ℝ) := by
  have hcast : ((n : ℕ) : K) = ((n : ℤ) : K) := by push_cast; ring
  rw [hcast, house_intCast]
  simp

theorem house_one_field {K : Type*} [Field K] [NumberField K] :
    house ((1 : K)) = 1 := by
  simpa using house_natCast_field (K := K) 1

/-- A uniformly bounded family has geometrically bounded weighted products. -/
theorem house_prod_pow_le {K : Type*} [Field K] [NumberField K]
    {iota : Type*} [Fintype iota] (f : iota -> K) (e : iota -> Nat) (G : Real)
    (hG : 1 <= G) (hf : forall i, house (f i) <= G) :
    house (∏ i, f i ^ e i) <= G ^ (∑ i, e i) := by
  classical
  have hG0 : (0 : Real) <= G := le_trans zero_le_one hG
  induction (Finset.univ : Finset iota) using Finset.induction_on with
  | empty => simp [house_one_field]
  | insert i s his ih =>
      rw [Finset.prod_insert his, Finset.sum_insert his, pow_add]
      refine le_trans (house_mul_le _ _) ?_
      refine mul_le_mul ?_ ih (house_nonneg _) (pow_nonneg hG0 _)
      exact le_trans (house_pow_le _ _) (pow_le_pow_left₀ (house_nonneg _) (hf i) _)

theorem SolvedRelation.house_integerScalar
    (R : SolvedRelation) (c : ℤ) : house (R.integerScalar c) = |(c : ℝ)| := by
  have hval : R.integerScalar c = ((c : ℤ) : R.CoefficientField) := by
    simp [SolvedRelation.integerScalar, zsmul_eq_mul]
  rw [hval, house_intCast]
  push_cast
  ring

/-- Uniform geometric base controlling every jet coefficient of the auxiliary polynomial. -/
noncomputable def SolvedRelation.jetGrowthBase
    (R : SolvedRelation) (c : ℤ) (U V : ℕ) : ℝ :=
  (1 + 2 * (U : ℝ)) * (1 + |(c : ℝ)|) * R.eigenHouseBound c V

theorem SolvedRelation.one_le_jetGrowthBase
    (R : SolvedRelation) (c : ℤ) (U V : ℕ) : 1 ≤ R.jetGrowthBase c U V := by
  unfold SolvedRelation.jetGrowthBase
  have h1 : (1 : ℝ) ≤ 1 + 2 * (U : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) U
    linarith
  have h2 : (1 : ℝ) ≤ 1 + |(c : ℝ)| := by
    have := abs_nonneg ((c : ℝ))
    linarith
  have h3 := R.one_le_eigenHouseBound c V
  have h12 : (1 : ℝ) ≤ (1 + 2 * (U : ℝ)) * (1 + |(c : ℝ)|) := by
    simpa using mul_le_mul h1 h2 zero_le_one (by linarith)
  simpa using mul_le_mul h12 h3 zero_le_one (by linarith)

theorem SolvedRelation.eigenHouseBound_le_jetGrowthBase
    (R : SolvedRelation) (c : ℤ) (U V : ℕ) :
    R.eigenHouseBound c V ≤ R.jetGrowthBase c U V := by
  unfold SolvedRelation.jetGrowthBase
  have h1 : (1 : ℝ) ≤ 1 + 2 * (U : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) U
    linarith
  have h2 : (1 : ℝ) ≤ 1 + |(c : ℝ)| := by
    have := abs_nonneg ((c : ℝ))
    linarith
  have h3 := R.one_le_eigenHouseBound c V
  have h12 : (1 : ℝ) ≤ (1 + 2 * (U : ℝ)) * (1 + |(c : ℝ)|) := by
    simpa using mul_le_mul h1 h2 zero_le_one (by linarith)
  nlinarith

theorem SolvedRelation.house_nonconstantEigenProduct_le
    (R : SolvedRelation) (c : ℤ) {U V : ℕ}
    (nu : R.Direction → ℕ) (m : R.ExponentialColumn V) :
    house (R.nonconstantEigenProduct c nu m) ≤
      R.jetGrowthBase c U V ^ (∑ i : R.NonPivot, nu (some i)) := by
  unfold SolvedRelation.nonconstantEigenProduct
  refine house_prod_pow_le _ _ _ (R.one_le_jetGrowthBase c U V) fun i => ?_
  exact (R.house_componentEigenvalue_le c (some i) m).trans
    (R.eigenHouseBound_le_jetGrowthBase c U V)


theorem SolvedRelation.house_jetLoweringCoeff_le
    (R : SolvedRelation) (c : ℤ) {U V : ℕ} (hU : 1 ≤ U) (r a k : ℕ)
    (ha : a ≤ U) (hk : k ≤ r) (m : R.ExponentialColumn V) :
    house (R.jetLoweringCoeff c r a k m) ≤ R.jetGrowthBase c U V ^ r := by
  set E := R.eigenHouseBound c V with hE
  have hE1 : 1 ≤ E := R.one_le_eigenHouseBound c V
  have hc1 : (1 : ℝ) ≤ 1 + |(c : ℝ)| := by
    have := abs_nonneg ((c : ℝ)); linarith
  have hU1 : (1 : ℝ) ≤ 1 + 2 * (U : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) U; linarith
  have hfactors : house (R.jetLoweringCoeff c r a k m) ≤
      (Nat.choose r k : ℝ) * (a.descFactorial k : ℝ) * |(c : ℝ)| ^ k * E ^ (r - k) := by
    unfold SolvedRelation.jetLoweringCoeff
    have h4 : house (R.componentEigenvalue c none m ^ (r - k)) ≤ E ^ (r - k) :=
      (house_pow_le _ _).trans
        (pow_le_pow_left₀ (house_nonneg _) (R.house_componentEigenvalue_le c none m) _)
    have h3 : house (R.integerScalar c ^ k) ≤ |(c : ℝ)| ^ k := by
      refine (house_pow_le _ _).trans ?_
      rw [R.house_integerScalar]
    refine le_trans (house_mul_le _ _) ?_
    refine mul_le_mul ?_ h4 (house_nonneg _)
      (by positivity)
    refine le_trans (house_mul_le _ _) ?_
    refine mul_le_mul ?_ h3 (house_nonneg _) (by positivity)
    refine le_trans (house_mul_le _ _) ?_
    rw [house_natCast_field, house_natCast_field]
  refine hfactors.trans ?_
  have hchoose : (Nat.choose r k : ℝ) ≤ 2 ^ r := by
    exact_mod_cast Nat.choose_le_two_pow r k
  have hdesc : (a.descFactorial k : ℝ) ≤ (U : ℝ) ^ r := by
    have h1 : a.descFactorial k ≤ a ^ k := Nat.descFactorial_le_pow a k
    have h2 : a ^ k ≤ U ^ k := Nat.pow_le_pow_left ha k
    have h3 : U ^ k ≤ U ^ r := Nat.pow_le_pow_right hU hk
    exact_mod_cast le_trans (le_trans h1 h2) h3
  have hcpow : |(c : ℝ)| ^ k ≤ (1 + |(c : ℝ)|) ^ r :=
    le_trans (pow_le_pow_left₀ (abs_nonneg _) (by linarith) k)
      (pow_le_pow_right₀ hc1 hk)
  have hEpow : E ^ (r - k) ≤ E ^ r := pow_le_pow_right₀ hE1 (Nat.sub_le r k)
  have hnn1 : (0 : ℝ) ≤ (Nat.choose r k : ℝ) := Nat.cast_nonneg _
  have hnn2 : (0 : ℝ) ≤ (a.descFactorial k : ℝ) := Nat.cast_nonneg _
  have hnn3 : (0 : ℝ) ≤ |(c : ℝ)| ^ k := by positivity
  have hnn4 : (0 : ℝ) ≤ E ^ (r - k) := by positivity
  have hstep : (Nat.choose r k : ℝ) * (a.descFactorial k : ℝ) * |(c : ℝ)| ^ k * E ^ (r - k) ≤
      (2 : ℝ) ^ r * (U : ℝ) ^ r * (1 + |(c : ℝ)|) ^ r * E ^ r := by
    have hA : (Nat.choose r k : ℝ) * (a.descFactorial k : ℝ) ≤ (2 : ℝ) ^ r * (U : ℝ) ^ r :=
      mul_le_mul hchoose hdesc hnn2 (by positivity)
    have hB : (Nat.choose r k : ℝ) * (a.descFactorial k : ℝ) * |(c : ℝ)| ^ k ≤
        (2 : ℝ) ^ r * (U : ℝ) ^ r * (1 + |(c : ℝ)|) ^ r :=
      mul_le_mul hA hcpow hnn3 (by positivity)
    exact mul_le_mul hB hEpow hnn4 (by positivity)
  refine hstep.trans ?_
  unfold SolvedRelation.jetGrowthBase
  rw [← hE, mul_pow, mul_pow]
  have h2U : (2 : ℝ) ^ r * (U : ℝ) ^ r = (2 * (U : ℝ)) ^ r := by rw [mul_pow]
  rw [h2U]
  have hbase : (2 * (U : ℝ)) ^ r ≤ (1 + 2 * (U : ℝ)) ^ r := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hnnB : (0 : ℝ) ≤ (1 + |(c : ℝ)|) ^ r := by positivity
  have hnnE : (0 : ℝ) ≤ E ^ r := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbase hnnB) hnnE


/-- Closed scalar majorant for the boundary size of a full component jet. -/
noncomputable def SolvedRelation.jetScalarBound
    (R : SolvedRelation) (c : ℤ) (U V : ℕ) (nu : R.Direction → ℕ)
    (Heta radius : ℝ) : ℝ :=
  ((U * V ^ R.n : ℕ) : ℝ) * Heta * ((nu none + 1 : ℕ) : ℝ) *
    R.jetGrowthBase c U V ^ (∑ dir, nu dir) * radius ^ U *
      Real.exp (((V : ℝ) * R.lambdaNormSum) * radius)

theorem SolvedRelation.sum_direction_eq
    (R : SolvedRelation) (nu : R.Direction → ℕ) :
    (∑ dir, nu dir) = nu none + ∑ i : R.NonPivot, nu (some i) :=
  Fintype.sum_option nu

theorem SolvedRelation.jetAnalyticBound_le_scalar
    (R : SolvedRelation) (c : ℤ) {U V : ℕ} (hU : 1 ≤ U)
    (nu : R.Direction → ℕ) (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    {radius Heta : ℝ} (hradius : 1 ≤ radius) (hHeta : 0 ≤ Heta)
    (hEta : ∀ col, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) ≤
      Heta) :
    R.jetAnalyticBound c nu eta radius ≤ R.jetScalarBound c U V nu Heta radius := by
  have hG1 : (1 : ℝ) ≤ R.jetGrowthBase c U V := R.one_le_jetGrowthBase c U V
  have hG0 : (0 : ℝ) ≤ R.jetGrowthBase c U V := le_trans zero_le_one hG1
  have hrad0 : (0 : ℝ) ≤ radius := le_trans zero_le_one hradius
  have hL0 : (0 : ℝ) ≤ Real.exp (((V : ℝ) * R.lambdaNormSum) * radius) := Real.exp_nonneg _
  have hterm : ∀ col : R.AuxiliaryColumn U V,
      house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) *
        (house (R.nonconstantEigenProduct c nu col.2) *
          ∑ k ∈ Finset.range (nu none + 1),
            house (R.jetLoweringCoeff c (nu none) (col.1 : ℕ) k col.2) *
              (radius ^ ((col.1 : ℕ) - k) *
                Real.exp (‖R.exponentialFrequency col.2‖ * radius))) ≤
        Heta * (R.jetGrowthBase c U V ^ (∑ i : R.NonPivot, nu (some i)) *
          (((nu none + 1 : ℕ) : ℝ) * (R.jetGrowthBase c U V ^ (nu none) *
            (radius ^ U * Real.exp (((V : ℝ) * R.lambdaNormSum) * radius))))) := by
    intro col
    have hinner : ∀ k ∈ Finset.range (nu none + 1),
        house (R.jetLoweringCoeff c (nu none) (col.1 : ℕ) k col.2) *
          (radius ^ ((col.1 : ℕ) - k) *
            Real.exp (‖R.exponentialFrequency col.2‖ * radius)) ≤
          R.jetGrowthBase c U V ^ (nu none) *
            (radius ^ U * Real.exp (((V : ℝ) * R.lambdaNormSum) * radius)) := by
      intro k hk
      have hkr : k ≤ nu none := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have h1 : house (R.jetLoweringCoeff c (nu none) (col.1 : ℕ) k col.2) ≤
          R.jetGrowthBase c U V ^ (nu none) :=
        R.house_jetLoweringCoeff_le c hU (nu none) (col.1 : ℕ) k col.1.isLt.le hkr col.2
      have h2 : radius ^ ((col.1 : ℕ) - k) ≤ radius ^ U :=
        pow_le_pow_right₀ hradius (le_trans (Nat.sub_le _ _) col.1.isLt.le)
      have h3 : Real.exp (‖R.exponentialFrequency col.2‖ * radius) ≤
          Real.exp (((V : ℝ) * R.lambdaNormSum) * radius) :=
        Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (R.norm_exponentialFrequency_le col.2) hrad0)
      refine mul_le_mul h1 ?_
        (mul_nonneg (pow_nonneg hrad0 _) (Real.exp_nonneg _)) (pow_nonneg hG0 _)
      exact mul_le_mul h2 h3 (Real.exp_nonneg _) (pow_nonneg hrad0 _)
    have hsum : (∑ k ∈ Finset.range (nu none + 1),
        house (R.jetLoweringCoeff c (nu none) (col.1 : ℕ) k col.2) *
          (radius ^ ((col.1 : ℕ) - k) *
            Real.exp (‖R.exponentialFrequency col.2‖ * radius))) ≤
        ((nu none + 1 : ℕ) : ℝ) * (R.jetGrowthBase c U V ^ (nu none) *
          (radius ^ U * Real.exp (((V : ℝ) * R.lambdaNormSum) * radius))) := by
      refine le_trans (Finset.sum_le_sum hinner) ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hnc : house (R.nonconstantEigenProduct c nu col.2) ≤
        R.jetGrowthBase c U V ^ (∑ i : R.NonPivot, nu (some i)) :=
      R.house_nonconstantEigenProduct_le (U := U) c nu col.2
    have hsum0 : (0 : ℝ) ≤ ∑ k ∈ Finset.range (nu none + 1),
        house (R.jetLoweringCoeff c (nu none) (col.1 : ℕ) k col.2) *
          (radius ^ ((col.1 : ℕ) - k) *
            Real.exp (‖R.exponentialFrequency col.2‖ * radius)) :=
      Finset.sum_nonneg fun k _ => mul_nonneg (house_nonneg _)
        (mul_nonneg (pow_nonneg hrad0 _) (Real.exp_nonneg _))
    refine mul_le_mul (hEta col) ?_ (mul_nonneg (house_nonneg _) hsum0) hHeta
    exact mul_le_mul hnc hsum hsum0 (pow_nonneg hG0 _)
  refine le_trans (Finset.sum_le_sum fun col _ => hterm col) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ : Finset (R.AuxiliaryColumn U V)).card = U * V ^ R.n := by
    simp [R.card_auxiliaryColumn U V]
  rw [hcard]
  refine le_of_eq ?_
  unfold SolvedRelation.jetScalarBound
  rw [R.sum_direction_eq nu, pow_add]
  push_cast
  ring


/-- Uniform house bound for the integrally scaled exponential bases. -/
noncomputable def SolvedRelation.baseHouseBound (R : SolvedRelation) (d : ℤ) : ℝ :=
  1 + ∑ i, house (R.scaledBase d i)

theorem SolvedRelation.one_le_baseHouseBound (R : SolvedRelation) (d : ℤ) :
    1 ≤ R.baseHouseBound d := by
  unfold SolvedRelation.baseHouseBound
  have : (0 : ℝ) ≤ ∑ i, house (R.scaledBase d i) :=
    Finset.sum_nonneg fun _ _ => house_nonneg _
  linarith

theorem SolvedRelation.house_scaledBase_le
    (R : SolvedRelation) (d : ℤ) (i : Fin R.n) :
    house (R.scaledBase d i) ≤ R.baseHouseBound d := by
  unfold SolvedRelation.baseHouseBound
  have hsingle : house (R.scaledBase d i) ≤ ∑ j, house (R.scaledBase d j) :=
    Finset.single_le_sum (f := fun j => house (R.scaledBase d j))
      (fun j _ => house_nonneg _) (Finset.mem_univ i)
  linarith

theorem SolvedRelation.house_scaledBaseSample_le
    (R : SolvedRelation) (d : ℤ) {V S : ℕ} (sample : Fin S) (m : R.ExponentialColumn V) :
    house (R.scaledBaseSample d sample m) ≤
      R.baseHouseBound d ^ (R.n * V * (sample : ℕ)) := by
  have hstep : house (R.scaledBaseSample d sample m) ≤
      R.baseHouseBound d ^ (∑ i : Fin R.n, (m i : ℕ) * (sample : ℕ)) := by
    unfold SolvedRelation.scaledBaseSample
    exact house_prod_pow_le _ _ _ (R.one_le_baseHouseBound d)
      (fun i => R.house_scaledBase_le d i)
  refine hstep.trans (pow_le_pow_right₀ (R.one_le_baseHouseBound d) ?_)
  calc
    (∑ i : Fin R.n, (m i : ℕ) * (sample : ℕ)) ≤ ∑ _i : Fin R.n, V * (sample : ℕ) := by
      exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (m i).isLt.le
    _ = R.n * V * (sample : ℕ) := by
      simp [Finset.sum_const, mul_assoc]

theorem SolvedRelation.constantJetTerm_eq_jetLoweringCoeff
    (R : SolvedRelation) (c : ℤ) {V : ℕ} (r a sample k : ℕ) (m : R.ExponentialColumn V) :
    R.constantJetTerm c r a sample k m =
      R.jetLoweringCoeff c r a k m * ((sample : R.CoefficientField) ^ (a - k)) := by
  unfold SolvedRelation.constantJetTerm SolvedRelation.jetLoweringCoeff
  ring

theorem SolvedRelation.house_additiveComponentJetCoefficient_le
    (R : SolvedRelation) (c : ℤ) {U V : ℕ} (hU : 1 ≤ U)
    (nu : R.Direction → ℕ) (a sample : ℕ) (ha : a ≤ U) (m : R.ExponentialColumn V) :
    house (R.additiveComponentJetCoefficient c nu a sample m) ≤
      ((nu none + 1 : ℕ) : ℝ) * R.jetGrowthBase c U V ^ (∑ dir, nu dir) *
        (1 + (sample : ℝ)) ^ U := by
  have hG1 : (1 : ℝ) ≤ R.jetGrowthBase c U V := R.one_le_jetGrowthBase c U V
  have hG0 : (0 : ℝ) ≤ R.jetGrowthBase c U V := le_trans zero_le_one hG1
  have hs1 : (1 : ℝ) ≤ 1 + (sample : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) sample; linarith
  have hterm : ∀ k ∈ Finset.range (nu none + 1),
      house (R.constantJetTerm c (nu none) a sample k m) ≤
        R.jetGrowthBase c U V ^ (nu none) * (1 + (sample : ℝ)) ^ U := by
    intro k hk
    have hkr : k ≤ nu none := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [R.constantJetTerm_eq_jetLoweringCoeff]
    refine le_trans (house_mul_le _ _) ?_
    refine mul_le_mul
      (R.house_jetLoweringCoeff_le c hU (nu none) a k ha hkr m) ?_
      (house_nonneg _) (pow_nonneg hG0 _)
    refine le_trans (house_pow_le _ _) ?_
    rw [house_natCast_field]
    exact le_trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _)
      (pow_le_pow_right₀ hs1 (le_trans (Nat.sub_le _ _) ha))
  have hconst : house (R.constantJetCoefficient c (nu none) a sample m) ≤
      ((nu none + 1 : ℕ) : ℝ) *
        (R.jetGrowthBase c U V ^ (nu none) * (1 + (sample : ℝ)) ^ U) := by
    unfold SolvedRelation.constantJetCoefficient
    refine le_trans (house_sum_le_sum_house _ _) ?_
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold SolvedRelation.additiveComponentJetCoefficient
  refine le_trans (house_mul_le _ _) ?_
  have hnc : house (R.nonconstantEigenProduct c nu m) ≤
      R.jetGrowthBase c U V ^ (∑ i : R.NonPivot, nu (some i)) :=
    R.house_nonconstantEigenProduct_le (U := U) c nu m
  refine le_trans (mul_le_mul hnc hconst (house_nonneg _) (pow_nonneg hG0 _)) ?_
  rw [R.sum_direction_eq nu, pow_add]
  refine le_of_eq ?_
  ring


/-- Closed scalar majorant for the conjugates of a cleared full component jet. -/
noncomputable def SolvedRelation.jetHouseScalarBound
    (R : SolvedRelation) (c d : ℤ) (U V : ℕ) (nu : R.Direction → ℕ)
    (Heta : ℝ) (sample : ℕ) : ℝ :=
  ((U * V ^ R.n : ℕ) : ℝ) * (1 + |(d : ℝ)|) ^ (sample * (R.n * V)) *
    (((nu none + 1 : ℕ) : ℝ) * R.jetGrowthBase c U V ^ (∑ dir, nu dir) *
      (1 + (sample : ℝ)) ^ U) * Heta * R.baseHouseBound d ^ (R.n * V * sample)

theorem SolvedRelation.polynomialComponentJetHouseBound_le_scalar
    (R : SolvedRelation) (c d : ℤ) {U V : ℕ} (hU : 1 ≤ U)
    (nu : R.Direction → ℕ) (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (sample : ℕ) {Heta : ℝ} (hHeta : 0 ≤ Heta)
    (hEta : ∀ col, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) ≤
      Heta) :
    R.polynomialComponentJetHouseBound c d nu eta sample ≤
      R.jetHouseScalarBound c d U V nu Heta sample := by
  have hG1 : (1 : ℝ) ≤ R.jetGrowthBase c U V := R.one_le_jetGrowthBase c U V
  have hG0 : (0 : ℝ) ≤ R.jetGrowthBase c U V := le_trans zero_le_one hG1
  have hd1 : (1 : ℝ) ≤ 1 + |(d : ℝ)| := by
    have := abs_nonneg ((d : ℝ)); linarith
  have hs1 : (1 : ℝ) ≤ 1 + (sample : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) sample; linarith
  have hB1 : (1 : ℝ) ≤ R.baseHouseBound d := R.one_le_baseHouseBound d
  refine le_trans
    (R.polynomialComponentJetHouseBound_le_of_coefficient_house_le c d nu eta sample Heta hEta) ?_
  have hterm : ∀ col : R.AuxiliaryColumn U V,
      house (R.integerScalar d) ^ R.polynomialComponentJetClearingExponent sample col.2 *
        house (R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2) *
          Heta * house (R.scaledBaseSample d ⟨sample, Nat.lt_add_one sample⟩ col.2) ≤
      (1 + |(d : ℝ)|) ^ (sample * (R.n * V)) *
        (((nu none + 1 : ℕ) : ℝ) * R.jetGrowthBase c U V ^ (∑ dir, nu dir) *
          (1 + (sample : ℝ)) ^ U) * Heta * R.baseHouseBound d ^ (R.n * V * sample) := by
    intro col
    have h1 : house (R.integerScalar d) ^
        R.polynomialComponentJetClearingExponent sample col.2 ≤
        (1 + |(d : ℝ)|) ^ (sample * (R.n * V)) := by
      rw [R.house_integerScalar]
      have hdle : |(d : ℝ)| ≤ 1 + |(d : ℝ)| := by linarith
      refine le_trans (pow_le_pow_left₀ (abs_nonneg _) hdle _) ?_
      refine pow_le_pow_right₀ hd1 ?_
      unfold SolvedRelation.polynomialComponentJetClearingExponent
      exact Nat.sub_le _ _
    have h2 : house (R.additiveComponentJetCoefficient c nu (col.1 : ℕ) sample col.2) ≤
        ((nu none + 1 : ℕ) : ℝ) * R.jetGrowthBase c U V ^ (∑ dir, nu dir) *
          (1 + (sample : ℝ)) ^ U :=
      R.house_additiveComponentJetCoefficient_le c hU nu (col.1 : ℕ) sample col.1.isLt.le col.2
    have h3 : house (R.scaledBaseSample d ⟨sample, Nat.lt_add_one sample⟩ col.2) ≤
        R.baseHouseBound d ^ (R.n * V * sample) :=
      R.house_scaledBaseSample_le d ⟨sample, Nat.lt_add_one sample⟩ col.2
    have hpos2 : (0 : ℝ) ≤ ((nu none + 1 : ℕ) : ℝ) *
        R.jetGrowthBase c U V ^ (∑ dir, nu dir) * (1 + (sample : ℝ)) ^ U := by
      have : (0 : ℝ) ≤ (1 + (sample : ℝ)) ^ U := by positivity
      have h0 : (0 : ℝ) ≤ ((nu none + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      exact mul_nonneg (mul_nonneg h0 (pow_nonneg hG0 _)) this
    refine mul_le_mul ?_ h3 (house_nonneg _) (by positivity)
    refine mul_le_mul ?_ le_rfl hHeta (by positivity)
    exact mul_le_mul h1 h2 (house_nonneg _) (by positivity)
  refine le_trans (Finset.sum_le_sum fun col _ => hterm col) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ : Finset (R.AuxiliaryColumn U V)).card = U * V ^ R.n := by
    simp [R.card_auxiliaryColumn U V]
  rw [hcard]
  refine le_of_eq ?_
  unfold SolvedRelation.jetHouseScalarBound
  push_cast
  ring

end GaloisForLFunctions.RHTower.BakerGeneralProof
