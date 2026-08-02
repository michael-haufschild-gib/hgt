import GaloisForLFunctions.HTGeometry.SquarefreeVeroneseIdeal

/-!
# Physical arc contact of the squarefree annihilator

The physical exponential arc sends each translation direction to `λ τ_j`.  Pulling a difference
operator back along it turns a monomial of total degree `|d|` into a constant multiple of `λ^{|d|}`.

Every element of the squarefree degree-`r` ideal is monomial-wide of width `r`, so its pullback is
divisible by `λ^r`; and the pullback of a coface generator is a nonzero constant times `λ^r`
whenever no period vanishes.  The order of contact of the ideal along the arc is therefore exactly
`r`, which is its least augmentation degree: the hierarchy has zero physical tangency excess.
-/

open scoped BigOperators

namespace GaloisForLFunctions.VeroneseIdeal

open MvPolynomial

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-! ## The arc pullback -/

/-- Pullback along the physical exponential arc `X_j ↦ τ_j λ`. -/
def physicalArcPullback (τ : ι → ℂ) : MvPolynomial ι ℂ →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval fun j => Polynomial.C (τ j) * Polynomial.X

omit [DecidableEq ι] in
theorem physicalArcPullback_X (τ : ι → ℂ) (j : ι) :
    physicalArcPullback τ (MvPolynomial.X j) = Polynomial.C (τ j) * Polynomial.X := by
  rw [physicalArcPullback, MvPolynomial.aeval_X]

/-- The pullback of a coface generator is a constant multiple of a pure power. -/
theorem physicalArcPullback_prod_X (τ : ι → ℂ) (S : Finset ι) :
    physicalArcPullback τ (∏ j ∈ S, MvPolynomial.X j) =
      Polynomial.C (∏ j ∈ S, τ j) * Polynomial.X ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [physicalArcPullback]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, map_mul, physicalArcPullback_X, ih,
        Finset.prod_insert ha, Finset.card_insert_of_notMem ha, map_mul, pow_succ]
      ring

/-! ## Monomial-wide operators have high contact -/

omit [DecidableEq ι] in
theorem physicalArcPullback_monomial (τ : ι → ℂ) (d : ι →₀ ℕ) (a : ℂ) :
    physicalArcPullback τ (MvPolynomial.monomial d a) =
      Polynomial.C (a * ∏ i ∈ d.support, τ i ^ d i) *
        Polynomial.X ^ (∑ i ∈ d.support, d i) := by
  classical
  rw [physicalArcPullback, MvPolynomial.aeval_monomial, Finsupp.prod]
  have h1 : ∀ i ∈ d.support, (Polynomial.C (τ i) * Polynomial.X) ^ d i =
      Polynomial.C (τ i ^ d i) * Polynomial.X ^ d i := by
    intro i _
    rw [mul_pow, ← Polynomial.C_pow]
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, ← map_prod,
    ← Finset.prod_pow_eq_pow_sum, Polynomial.C_mul, Polynomial.algebraMap_eq]
  ring

omit [DecidableEq ι] in
theorem card_le_sum_of_mem_support (d : ι →₀ ℕ) :
    d.support.card ≤ ∑ i ∈ d.support, d i := by
  classical
  rw [Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun i hi => ?_
  exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)

omit [DecidableEq ι] in
/-- **Lower contact bound.**  A monomial-wide operator of width `r` pulls back to a multiple of
`λ^r`. -/
theorem pow_dvd_physicalArcPullback_of_monoWide (τ : ι → ℂ) {r : ℕ}
    {P : MvPolynomial ι ℂ} (hP : MonoWide r P) :
    (Polynomial.X : Polynomial ℂ) ^ r ∣ physicalArcPullback τ P := by
  classical
  rw [P.as_sum, map_sum]
  refine Finset.dvd_sum fun d hd => ?_
  rw [physicalArcPullback_monomial]
  have hwide : r ≤ d.support.card := hP d (MvPolynomial.mem_support_iff.mp hd)
  have hdeg : r ≤ ∑ i ∈ d.support, d i := le_trans hwide (card_le_sum_of_mem_support d)
  exact Dvd.dvd.mul_left (pow_dvd_pow _ hdeg) _

/-- Every element of the squarefree degree-`r` ideal pulls back to a multiple of `λ^r`. -/
theorem pow_dvd_physicalArcPullback_of_mem_veroneseIdeal (τ : ι → ℂ) {r : ℕ}
    {P : MvPolynomial ι ℂ} (hP : P ∈ veroneseIdeal ℂ ι r) :
    (Polynomial.X : Polynomial ℂ) ^ r ∣ physicalArcPullback τ P :=
  pow_dvd_physicalArcPullback_of_monoWide τ (monoWide_of_mem_ideal hP)

/-! ## Contact is attained: zero physical tangency -/

/-- **Exact contact at a coface generator.**  If no period vanishes, a coface generator pulls back
to a nonzero constant times `λ^r`, so the contact order is not larger than `r`. -/
theorem physicalArcPullback_generator_ne_zero (τ : ι → ℂ) (hτ : ∀ j, τ j ≠ 0)
    {r : ℕ} {S : Finset ι} (hS : S.card = r) :
    physicalArcPullback τ (∏ j ∈ S, MvPolynomial.X j) ≠ 0 ∧
      ¬ (Polynomial.X : Polynomial ℂ) ^ (r + 1) ∣
        physicalArcPullback τ (∏ j ∈ S, MvPolynomial.X j) := by
  classical
  have hprod : (∏ j ∈ S, τ j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hτ j
  rw [physicalArcPullback_prod_X, hS]
  constructor
  · exact mul_ne_zero (Polynomial.C_ne_zero.mpr hprod) (pow_ne_zero _ Polynomial.X_ne_zero)
  · intro hdvd
    have hcoeff : (Polynomial.C (∏ j ∈ S, τ j) * Polynomial.X ^ r).coeff r =
        ∏ j ∈ S, τ j := by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    have hzero : (Polynomial.C (∏ j ∈ S, τ j) * Polynomial.X ^ r).coeff r = 0 :=
      Polynomial.X_pow_dvd_iff.mp hdvd r (by omega)
    rw [hcoeff] at hzero
    exact hprod hzero

/-- **Zero physical tangency of the squarefree hierarchy.**  Along an arc with no vanishing period
the squarefree degree-`r` ideal has contact order exactly `r`: every element is divisible by `λ^r`,
and some coface generator is not divisible by `λ^{r+1}`. -/
theorem veroneseIdeal_physicalArcContact (τ : ι → ℂ) (hτ : ∀ j, τ j ≠ 0) {r : ℕ}
    {S : Finset ι} (hS : S.card = r) :
    (∀ P ∈ veroneseIdeal ℂ ι r,
        (Polynomial.X : Polynomial ℂ) ^ r ∣ physicalArcPullback τ P) ∧
      (∏ j ∈ S, MvPolynomial.X j) ∈ veroneseIdeal ℂ ι r ∧
      ¬ (Polynomial.X : Polynomial ℂ) ^ (r + 1) ∣
        physicalArcPullback τ (∏ j ∈ S, MvPolynomial.X j) :=
  ⟨fun _ hP => pow_dvd_physicalArcPullback_of_mem_veroneseIdeal τ hP,
    Ideal.subset_span ⟨S, hS, rfl⟩,
    (physicalArcPullback_generator_ne_zero τ hτ hS).2⟩

/-! ## Least augmentation degree does not determine contact -/

/-- An explicit operator with a nonzero linear part whose arc pullback is a nonzero multiple of
`lambda^2`: the linear part cancels along the arc, so contact exceeds the least augmentation
degree. -/
def positiveTangencyWitness : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.X 0 - MvPolynomial.X 1 + MvPolynomial.X 0 ^ 2

/-- The comparison operator, whose linear part survives. -/
def zeroTangencyWitness : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0

theorem physicalArcPullback_positiveTangencyWitness :
    physicalArcPullback (fun _ : Fin 2 => (1 : ℂ)) positiveTangencyWitness =
      Polynomial.X ^ 2 := by
  rw [positiveTangencyWitness, map_add, map_sub, map_pow, physicalArcPullback_X,
    physicalArcPullback_X]
  simp

theorem physicalArcPullback_zeroTangencyWitness :
    physicalArcPullback (fun _ : Fin 2 => (1 : ℂ)) zeroTangencyWitness = Polynomial.X := by
  rw [zeroTangencyWitness, physicalArcPullback_X]
  simp

theorem coeff_positiveTangencyWitness :
    MvPolynomial.coeff (Finsupp.single 0 1) positiveTangencyWitness = 1 := by
  classical
  have hsq : MvPolynomial.coeff (Finsupp.single 0 1)
      ((MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ^ 2) = 0 := by
    have hne : (Finsupp.single (0 : Fin 2) 2) ≠ (Finsupp.single (0 : Fin 2) 1) := by
      intro hcontra
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hcontra
      simp at this
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial, if_neg hne]
  rw [positiveTangencyWitness, MvPolynomial.coeff_add, MvPolynomial.coeff_sub, hsq,
    MvPolynomial.coeff_X, MvPolynomial.coeff_X]
  simp [Finsupp.single_eq_single_iff]

theorem coeff_zeroTangencyWitness :
    MvPolynomial.coeff (Finsupp.single 0 1) zeroTangencyWitness = 1 := by
  classical
  rw [zeroTangencyWitness, MvPolynomial.coeff_X, if_pos rfl]

/-- **The tangency discriminator.**  Two operators with the same least augmentation degree can have
different physical contact orders along the same arc: the first keeps contact one, the second is
pushed to contact two because its linear part cancels on the arc.  So differential-algebraic source
height alone does not determine physical obstruction multiplicity. -/
theorem physicalContact_not_determined_by_leastDegree :
    MvPolynomial.coeff (Finsupp.single 0 1) zeroTangencyWitness ≠ 0 ∧
      MvPolynomial.coeff (Finsupp.single 0 1) positiveTangencyWitness ≠ 0 ∧
      ¬ (Polynomial.X : Polynomial ℂ) ^ 2 ∣
        physicalArcPullback (fun _ : Fin 2 => (1 : ℂ)) zeroTangencyWitness ∧
      (Polynomial.X : Polynomial ℂ) ^ 2 ∣
        physicalArcPullback (fun _ : Fin 2 => (1 : ℂ)) positiveTangencyWitness ∧
      physicalArcPullback (fun _ : Fin 2 => (1 : ℂ)) positiveTangencyWitness ≠ 0 := by
  refine ⟨by rw [coeff_zeroTangencyWitness]; exact one_ne_zero,
    by rw [coeff_positiveTangencyWitness]; exact one_ne_zero, ?_, ?_, ?_⟩
  · rw [physicalArcPullback_zeroTangencyWitness]
    intro hdvd
    have := Polynomial.X_pow_dvd_iff.mp hdvd 1 (by omega)
    simp at this
  · rw [physicalArcPullback_positiveTangencyWitness]
  · rw [physicalArcPullback_positiveTangencyWitness]
    exact pow_ne_zero _ Polynomial.X_ne_zero

end

end GaloisForLFunctions.VeroneseIdeal
