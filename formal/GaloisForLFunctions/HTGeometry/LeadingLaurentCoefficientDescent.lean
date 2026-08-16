import GaloisForLFunctions.HTGeometry.LaurentCoefficientwiseDerivation

/-!
# Differential algebraicity descends to the leading Laurent coefficient

A formal Laurent series in a differential-constant parameter is the monomial `E^m` times a formal
power series, and `E^m` is a unit.  Rescaling the variables of a differential relation by that unit
multiplies each monomial by a power of `E` determined by its total degree, so after multiplying by
one fixed compensating power the relation descends to a relation over `k[E]` on the power-series
part.  The normalization and specialization steps then apply verbatim, and the constant coefficient
of the power-series part is exactly the leading Laurent coefficient.

## Main results

* `parameterRescale` — the degreewise rescaling of a relation's coefficients;
* `ofPowerSeries_eval₂_parameterRescale` — rescaling matches the unit substitution;
* `differentialAlgebraicOver_leadingCoeff_of_laurentRelation` — the theorem;
* `no_laurentRelation_of_not_differentialAlgebraicOver_leadingCoeff` — its contrapositive: a
  hypertranscendental leading coefficient forces the Laurent series to be hypertranscendental.
-/

noncomputable section

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace LaurentDeriv

open HahnSeries PowerSeriesDeriv

/-- Interpret a polynomial in the formal parameter as a Laurent series. -/
def laurentParameterMap {F K : Type*} [CommRing F] [CommRing K] [Algebra F K] :
    Polynomial F →+* LaurentSeries K :=
  (HahnSeries.ofPowerSeries ℤ K).comp polynomialFormalParameterMap

/-- Rescale each coefficient of a formal-parameter relation by a power of the parameter. -/
def parameterRescale {F ι : Type*} [CommRing F]
    (Q : MvPolynomial ι (Polynomial F)) (k : (ι →₀ ℕ) → ℕ) : MvPolynomial ι (Polynomial F) :=
  ∑ d ∈ Q.support, MvPolynomial.monomial d (MvPolynomial.coeff d Q * Polynomial.X ^ k d)

theorem coeff_parameterRescale {F ι : Type*} [CommRing F]
    (Q : MvPolynomial ι (Polynomial F)) (k : (ι →₀ ℕ) → ℕ) (d : ι →₀ ℕ) :
    MvPolynomial.coeff d (parameterRescale Q k)
      = MvPolynomial.coeff d Q * Polynomial.X ^ k d := by
  classical
  rw [parameterRescale, MvPolynomial.coeff_sum,
    Finset.sum_congr rfl (fun d' _ => MvPolynomial.coeff_monomial d d'
      (MvPolynomial.coeff d' Q * Polynomial.X ^ k d')),
    Finset.sum_ite_eq' Q.support d
      (fun d' => MvPolynomial.coeff d' Q * Polynomial.X ^ k d')]
  by_cases hd : d ∈ Q.support
  · rw [if_pos hd]
  · rw [if_neg hd, MvPolynomial.notMem_support_iff.mp hd, zero_mul]

/-- Rescaling never destroys a relation: the parameter is a nonzerodivisor. -/
theorem parameterRescale_ne_zero {F ι : Type*} [CommRing F]
    {Q : MvPolynomial ι (Polynomial F)} (hQ : Q ≠ 0) (k : (ι →₀ ℕ) → ℕ) :
    parameterRescale Q k ≠ 0 := by
  classical
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hQ
  have hc : MvPolynomial.coeff d Q ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  intro h
  have hz : MvPolynomial.coeff d Q * Polynomial.X ^ k d = 0 := by
    rw [← coeff_parameterRescale Q k d, h, MvPolynomial.coeff_zero]
  apply hc
  refine Polynomial.ext (fun j => ?_)
  have hcoe := congrArg (fun p : Polynomial F => Polynomial.coeff p (j + k d)) hz
  simpa [Polynomial.coeff_mul_X_pow] using hcoe

/-- **Rescaling matches substitution by the monomial unit.**  Substituting `E^m * v i` for the
variables of `Q` is, up to one fixed power of `E`, the same as evaluating the rescaled relation at
`v`. -/
theorem ofPowerSeries_eval₂_parameterRescale {F K ι : Type*} [CommRing F] [CommRing K]
    [Algebra F K] (Q : MvPolynomial ι (Polynomial F)) (k : (ι →₀ ℕ) → ℕ) (c : ℕ) (m : ℤ)
    (v : ι → PowerSeries K)
    (hk : ∀ d ∈ Q.support, (k d : ℤ) = (c : ℤ) + m * ((d.sum fun _ e => e : ℕ) : ℤ)) :
    HahnSeries.ofPowerSeries ℤ K
        (MvPolynomial.eval₂ polynomialFormalParameterMap v (parameterRescale Q k))
      = HahnSeries.single (c : ℤ) (1 : K) *
          MvPolynomial.eval₂ laurentParameterMap
            (fun i => HahnSeries.single m (1 : K) * ((v i : PowerSeries K) : LaurentSeries K)) Q := by
  classical
  have hL : MvPolynomial.eval₂ polynomialFormalParameterMap v (parameterRescale Q k)
      = ∑ d ∈ Q.support,
          polynomialFormalParameterMap (MvPolynomial.coeff d Q * Polynomial.X ^ k d)
            * ∏ i ∈ d.support, v i ^ d i := by
    rw [parameterRescale, ← MvPolynomial.coe_eval₂Hom, map_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, Finsupp.prod]
  rw [hL, map_sum, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hXpow : HahnSeries.ofPowerSeries ℤ K (polynomialFormalParameterMap
      (Polynomial.X ^ k d : Polynomial F)) = HahnSeries.single ((k d : ℤ)) (1 : K) := by
    rw [polynomialFormalParameterMap]
    simp only [map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      HahnSeries.ofPowerSeries_X, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
  have hprodv : HahnSeries.ofPowerSeries ℤ K (∏ i ∈ d.support, v i ^ d i)
      = ∏ i ∈ d.support, ((v i : PowerSeries K) : LaurentSeries K) ^ d i := by
    rw [map_prod]
    exact Finset.prod_congr rfl (fun i _ => map_pow _ _ _)
  have hprodu : ∏ i ∈ d.support,
      (HahnSeries.single m (1 : K) * ((v i : PowerSeries K) : LaurentSeries K)) ^ d i
      = HahnSeries.single (((d.sum fun _ e => e : ℕ) : ℤ) * m) (1 : K)
        * ∏ i ∈ d.support, ((v i : PowerSeries K) : LaurentSeries K) ^ d i := by
    rw [Finset.prod_congr rfl (fun i (_ : i ∈ d.support) => mul_pow (HahnSeries.single m (1 : K))
      (((v i : PowerSeries K) : LaurentSeries K)) (d i)), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [HahnSeries.single_pow, one_pow, nsmul_eq_mul]
    rfl
  rw [map_mul, map_mul, map_mul, hXpow, hprodv, hprodu]
  have hbase : HahnSeries.ofPowerSeries ℤ K
      (polynomialFormalParameterMap (MvPolynomial.coeff d Q))
      = laurentParameterMap (MvPolynomial.coeff d Q) := rfl
  rw [hbase]
  have hsingle : HahnSeries.single ((k d : ℤ)) (1 : K)
      = HahnSeries.single (c : ℤ) (1 : K)
        * HahnSeries.single (((d.sum fun _ e => e : ℕ) : ℤ) * m) (1 : K) := by
    have hidx : (k d : ℤ) = (c : ℤ) + ((d.sum fun _ e => e : ℕ) : ℤ) * m := by
      rw [hk d hd]; ring
    rw [HahnSeries.single_mul_single, one_mul, hidx]
  rw [hsingle]
  simp only [mul_assoc, mul_comm, mul_left_comm]

/-! ### The theorem -/

variable {F K : Type*} [CommRing F] [CommRing K] [IsDomain K] [Algebra F K] [Differential K]

/-- **Differential algebraicity descends to the leading Laurent coefficient.**  A nonzero
formal-parameter relation on the coefficientwise jets of a Laurent series forces its leading
coefficient to be differentially algebraic over the coefficient base. -/
theorem differentialAlgebraicOver_leadingCoeff_of_laurentRelation
    {n : ℕ} {Q : MvPolynomial (Fin (n + 1)) (Polynomial F)} (hQ : Q ≠ 0)
    (f : LaurentSeries K)
    (hann : MvPolynomial.eval₂ laurentParameterMap
      (fun j : Fin (n + 1) => laurentCoeffwiseJet (j : ℕ) f) Q = 0) :
    GaloisForLFunctions.DifferentialAlgebraicOver F f.leadingCoeff := by
  classical
  set m : ℤ := f.order with hm
  set G : PowerSeries K := f.powerSeriesPart with hG
  set v : Fin (n + 1) → PowerSeries K := fun j => coeffwiseJet (j : ℕ) G with hv
  have hjets : (fun j : Fin (n + 1) => laurentCoeffwiseJet (j : ℕ) f)
      = fun j : Fin (n + 1) => HahnSeries.single m (1 : K)
        * ((v j : PowerSeries K) : LaurentSeries K) := by
    funext j
    exact laurentCoeffwiseJet_eq_single_mul f (j : ℕ)
  rw [hjets] at hann
  set N : ℕ := Q.totalDegree with hN
  -- choose the compensating power and the degreewise rescaling
  obtain ⟨c, k, hk⟩ : ∃ (c : ℕ) (k : (Fin (n + 1) →₀ ℕ) → ℕ), ∀ d ∈ Q.support,
      (k d : ℤ) = (c : ℤ) + m * ((d.sum fun _ e => e : ℕ) : ℤ) := by
    rcases le_or_gt 0 m with hmpos | hmneg
    · refine ⟨0, fun d => m.toNat * (d.sum fun _ e => e), fun d _ => ?_⟩
      push_cast
      rw [Int.toNat_of_nonneg hmpos]
      ring
    · refine ⟨(-m).toNat * N, fun d => (-m).toNat * (N - (d.sum fun _ e => e)), fun d hd => ?_⟩
      have hle : (d.sum fun _ e => e) ≤ N := MvPolynomial.le_totalDegree hd
      have hcast : (((N - (d.sum fun _ e => e) : ℕ)) : ℤ)
          = (N : ℤ) - ((d.sum fun _ e => e : ℕ) : ℤ) := by
        exact_mod_cast Int.ofNat_sub hle
      push_cast [hcast]
      rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -m)]
      ring
  have hzero : MvPolynomial.eval₂ polynomialFormalParameterMap v (parameterRescale Q k) = 0 := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    rw [ofPowerSeries_eval₂_parameterRescale Q k c m v hk, hann, mul_zero, map_zero]
  have hfinal := differentialAlgebraicOver_constantCoeff_of_formalRelation
    (F := F) (K := K) (parameterRescale_ne_zero hQ k) G hzero
  rwa [constantCoeff_powerSeriesPart f] at hfinal

/-- **The contrapositive.**  If the leading coefficient is hypertranscendental over the base, the
Laurent series admits no nonzero formal-parameter differential relation. -/
theorem no_laurentRelation_of_not_differentialAlgebraicOver_leadingCoeff
    (f : LaurentSeries K)
    (h : ¬ GaloisForLFunctions.DifferentialAlgebraicOver F f.leadingCoeff)
    {n : ℕ} (Q : MvPolynomial (Fin (n + 1)) (Polynomial F)) (hQ : Q ≠ 0) :
    MvPolynomial.eval₂ laurentParameterMap
      (fun j : Fin (n + 1) => laurentCoeffwiseJet (j : ℕ) f) Q ≠ 0 := fun hann =>
  h (differentialAlgebraicOver_leadingCoeff_of_laurentRelation hQ f hann)

end LaurentDeriv

end GaloisForLFunctions.HTGeometry
