import GaloisForLFunctions.HTGeometry.UniversalProjectiveConstraintRealization
import GaloisForLFunctions.HTGeometry.PrimePowerAnalyticDilation
import GaloisForLFunctions.RHTower.MFreeTower

/-!
# Homogeneous constraint maps as valuation--clock dilations

Static prime-valuation realization is natural for homogeneous polynomial maps.  A coordinate map
of degree `q` sends degree `m` constraints to degree `q*m` constraints, and the corresponding
arithmetic carriers are related by the `q`-fold prime-power dilation.  Every rotated logarithmic
jet acquires the exact chain factor `q^k`.

Thus projective degree, prime valuation, analytic argument scale, and differential-clock weight
are four descriptions of the same functorial grading.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial ArithmeticFunction

noncomputable section

/-- A polynomial map whose coordinates are homogeneous of one common degree. -/
structure HomogeneousConstraintMap (σ τ : Type*) (q : ℕ) where
  coord : τ → homogeneousSubmodule σ ℂ q

/-- Pointwise evaluation of a homogeneous constraint map. -/
def HomogeneousConstraintMap.apply {σ τ : Type*} {q : ℕ}
    (Φ : HomogeneousConstraintMap σ τ q) (v : σ → ℂ) : τ → ℂ :=
  fun j => eval v (Φ.coord j).1

/-- Pullback multiplies homogeneous degree by the degree of the constraint map. -/
def HomogeneousConstraintMap.pullback {σ τ : Type*} {q m : ℕ}
    (Φ : HomogeneousConstraintMap σ τ q)
    (Q : homogeneousSubmodule τ ℂ m) : homogeneousSubmodule σ ℂ (q * m) :=
  ⟨MvPolynomial.bind₁ (fun j => (Φ.coord j).1) Q.1,
    by
      change IsHomogeneous (MvPolynomial.bind₁ (fun j => (Φ.coord j).1) Q.1) (q * m)
      rw [← MvPolynomial.aeval_eq_bind₁]
      exact Q.2.aeval _ (fun j => (Φ.coord j).2)⟩

/-- Evaluation commutes exactly with homogeneous pullback. -/
@[simp]
theorem HomogeneousConstraintMap.eval_pullback {σ τ : Type*} {q m : ℕ}
    (Φ : HomogeneousConstraintMap σ τ q)
    (v : σ → ℂ) (Q : homogeneousSubmodule τ ℂ m) :
    eval v (Φ.pullback Q).1 = eval (Φ.apply v) Q.1 := by
  exact MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℂ) v
    (fun j => (Φ.coord j).1) Q.1

/-- Constraint pullback preserves vanishing relations. -/
theorem HomogeneousConstraintMap.pullback_mem_constraintVanishing
    {σ τ : Type*} {q m : ℕ}
    (Φ : HomogeneousConstraintMap σ τ q)
    {K : Set (σ → ℂ)} {L : Set (τ → ℂ)}
    (hmap : ∀ v ∈ K, Φ.apply v ∈ L)
    {Q : homogeneousSubmodule τ ℂ m}
    (hQ : Q ∈ homogeneousConstraintVanishingSubmodule L m) :
    Φ.pullback Q ∈ homogeneousConstraintVanishingSubmodule K (q * m) := by
  intro v hv
  rw [Φ.eval_pullback]
  exact hQ (Φ.apply v) (hmap v hv)

/-- Linear pullback on one homogeneous layer. -/
def HomogeneousConstraintMap.pullbackLinearMap
    {σ τ : Type*} {q m : ℕ}
    (Φ : HomogeneousConstraintMap σ τ q) :
    homogeneousSubmodule τ ℂ m →ₗ[ℂ]
      homogeneousSubmodule σ ℂ (q * m) where
  toFun := Φ.pullback
  map_add' Q R := by
    apply Subtype.ext
    simp [HomogeneousConstraintMap.pullback]
  map_smul' z Q := by
    apply Subtype.ext
    simp [HomogeneousConstraintMap.pullback]

/-- Pullback descends canonically to homogeneous coordinate quotients. -/
def HomogeneousConstraintMap.constraintQuotientPullback
    {σ τ : Type*} {q m : ℕ}
    (Φ : HomogeneousConstraintMap σ τ q)
    {K : Set (σ → ℂ)} {L : Set (τ → ℂ)}
    (hmap : ∀ v ∈ K, Φ.apply v ∈ L) :
    (homogeneousSubmodule τ ℂ m ⧸
        homogeneousConstraintVanishingSubmodule L m) →ₗ[ℂ]
      (homogeneousSubmodule σ ℂ (q * m) ⧸
        homogeneousConstraintVanishingSubmodule K (q * m)) :=
  Submodule.mapQ
    (homogeneousConstraintVanishingSubmodule L m)
    (homogeneousConstraintVanishingSubmodule K (q * m))
    Φ.pullbackLinearMap (by
      intro Q hQ
      exact Φ.pullback_mem_constraintVanishing hmap hQ)

/-- The quotient pullback is represented by literal polynomial substitution. -/
@[simp]
theorem HomogeneousConstraintMap.constraintQuotientPullback_mk
    {σ τ : Type*} {q m : ℕ}
    (Φ : HomogeneousConstraintMap σ τ q)
    {K : Set (σ → ℂ)} {L : Set (τ → ℂ)}
    (hmap : ∀ v ∈ K, Φ.apply v ∈ L)
    (Q : homogeneousSubmodule τ ℂ m) :
    Φ.constraintQuotientPullback hmap
        ((homogeneousConstraintVanishingSubmodule L m).mkQ Q) =
      (homogeneousConstraintVanishingSubmodule K (q * m)).mkQ
        (Φ.pullback Q) := by
  rfl

/-- Composition multiplies constraint degrees. -/
def HomogeneousConstraintMap.comp {σ τ υ : Type*} {q r : ℕ}
    (Ψ : HomogeneousConstraintMap τ υ r)
    (Φ : HomogeneousConstraintMap σ τ q) :
    HomogeneousConstraintMap σ υ (q * r) where
  coord j := Φ.pullback (Ψ.coord j)

/-- Pointwise application respects composition. -/
@[simp]
theorem HomogeneousConstraintMap.apply_comp {σ τ υ : Type*} {q r : ℕ}
    (Ψ : HomogeneousConstraintMap τ υ r)
    (Φ : HomogeneousConstraintMap σ τ q) (v : σ → ℂ) :
    (Ψ.comp Φ).apply v = Ψ.apply (Φ.apply v) := by
  funext j
  exact Φ.eval_pullback v (Ψ.coord j)

/-- Polynomial pullback respects composition. -/
theorem HomogeneousConstraintMap.pullback_comp {σ τ υ : Type*}
    {q r m : ℕ}
    (Ψ : HomogeneousConstraintMap τ υ r)
    (Φ : HomogeneousConstraintMap σ τ q)
    (Q : homogeneousSubmodule υ ℂ m) :
    ((Ψ.comp Φ).pullback Q).1 = (Φ.pullback (Ψ.pullback Q)).1 := by
  change MvPolynomial.bind₁ (fun j => (Φ.pullback (Ψ.coord j)).1) Q.1 =
    MvPolynomial.bind₁ (fun j => (Φ.coord j).1)
      (MvPolynomial.bind₁ (fun j => (Ψ.coord j).1) Q.1)
  simpa [HomogeneousConstraintMap.pullback] using
    (MvPolynomial.bind₁_bind₁
      (fun j => (Ψ.coord j).1) (fun j => (Φ.coord j).1) Q.1).symm

/-- Dilation of a positive prime-power layer multiplies its valuation degree. -/
theorem mPart_arithmeticOfPrimePowerColumn_mul
    (q m : ℕ) (hq : q ≠ 0) (hm : m ≠ 0) (a : Nat.Primes → ℂ) :
    RHTower.mPart q (arithmeticOfPrimePowerColumn (m - 1) a) =
      arithmeticOfPrimePowerColumn (q * m - 1) a := by
  have hm_succ : m - 1 + 1 = m :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)
  have hqm : q * m ≠ 0 := mul_ne_zero hq hm
  have hqm_succ : q * m - 1 + 1 = q * m :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hqm)
  rw [← mPart_arithmeticOfPrimeColumn]
  rw [hm_succ]
  rw [RHTower.mPart_mPart hq hm]
  rw [← mPart_arithmeticOfPrimeColumn]
  rw [hqm_succ]

/-- Prime-power columns are complex-linear in their coefficient profile. -/
theorem smul_arithmeticOfPrimePowerColumn
    (z : ℂ) (e : ℕ) (c : Nat.Primes → ℂ) :
    z • arithmeticOfPrimePowerColumn e c =
      arithmeticOfPrimePowerColumn e (fun p => z * c p) := by
  ext n
  simp only [ArithmeticFunction.smul_map, smul_eq_mul]
  by_cases hpow : ∃ p : Nat.Primes, n = (p : ℕ) ^ (e + 1)
  · simp [arithmeticOfPrimePowerColumn, hpow]
  · simp [arithmeticOfPrimePowerColumn, hpow]

/-- The valuation carrier of one homogeneous observable. -/
def homogeneousConstraintValuationCarrier
    {σ : Type*} (x : Nat.Primes → σ → ℂ) (m : ℕ)
    (Q : homogeneousSubmodule σ ℂ m) : ArithmeticFunction ℂ :=
  arithmeticOfPrimePowerColumn (m - 1) (fun p => eval (x p) Q.1)

/-- The shifted order-`k` rotated jet of one homogeneous valuation carrier. -/
def homogeneousConstraintValuationJet
    {σ : Type*} (x : Nat.Primes → σ → ℂ) (m : ℕ)
    (Q : homogeneousSubmodule σ ℂ m) (a : ℂ) (k : ℕ) :
    ArithmeticFunction ℂ :=
  primePowerCoefficientShiftedRotatedJet (m - 1)
    (fun p => eval (x p) Q.1) a k

/-- **All-order valuation clock covariance.**  Dilation by `q` multiplies valuation degree by
`q` and the order-`k` rotated logarithmic clock by exactly `q^k`. -/
theorem primePowerCoefficientShiftedRotatedJet_dilation
    (q m : ℕ) (hq : q ≠ 0) (hm : m ≠ 0)
    (c : Nat.Primes → ℂ) (a : ℂ) (k : ℕ) :
    primePowerCoefficientShiftedRotatedJet (q * m - 1) c a k =
      (((q : ℂ) ^ k) •
        RHTower.mPart q
          (primePowerCoefficientShiftedRotatedJet (m - 1) c a k)) := by
  rw [primePowerCoefficientShiftedRotatedJet,
    primePowerCoefficientShiftedRotatedJet,
    mPart_arithmeticOfPrimePowerColumn_mul q m hq hm]
  rw [smul_arithmeticOfPrimePowerColumn]
  congr 1
  funext p
  have hqm : q * m ≠ 0 := mul_ne_zero hq hm
  have hqm_succ : q * m - 1 + 1 = q * m :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hqm)
  have hm_succ : m - 1 + 1 = m :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)
  rw [hqm_succ, hm_succ]
  push_cast
  rw [mul_assoc, mul_pow]
  ring

/-- Homogeneous pullback is represented by prime-valuation dilation. -/
theorem HomogeneousConstraintMap.valuationCarrier_pullback
    {σ τ : Type*} {q m : ℕ} (hq : q ≠ 0) (hm : m ≠ 0)
    (Φ : HomogeneousConstraintMap σ τ q)
    (x : Nat.Primes → σ → ℂ) (Q : homogeneousSubmodule τ ℂ m) :
    RHTower.mPart q
        (homogeneousConstraintValuationCarrier (fun p => Φ.apply (x p)) m Q) =
      homogeneousConstraintValuationCarrier x (q * m) (Φ.pullback Q) := by
  rw [homogeneousConstraintValuationCarrier,
    homogeneousConstraintValuationCarrier,
    mPart_arithmeticOfPrimePowerColumn_mul q m hq hm]
  congr 1
  funext p
  exact (Φ.eval_pullback (x p) Q).symm

/-- **Constraint-map valuation--clock law.**  Pullback of a degree-`m` observable through a
degree-`q` map is the `q`-dilation of its image-profile carrier, with exact jet weight `q^k`. -/
theorem HomogeneousConstraintMap.valuationJet_pullback
    {σ τ : Type*} {q m : ℕ} (hq : q ≠ 0) (hm : m ≠ 0)
    (Φ : HomogeneousConstraintMap σ τ q)
    (x : Nat.Primes → σ → ℂ)
    (Q : homogeneousSubmodule τ ℂ m) (a : ℂ) (k : ℕ) :
    homogeneousConstraintValuationJet x (q * m) (Φ.pullback Q) a k =
      (((q : ℂ) ^ k) •
        RHTower.mPart q
          (homogeneousConstraintValuationJet (fun p => Φ.apply (x p)) m Q a k)) := by
  rw [homogeneousConstraintValuationJet, homogeneousConstraintValuationJet]
  rw [primePowerCoefficientShiftedRotatedJet_dilation q m hq hm]
  apply congrArg (fun f : ArithmeticFunction ℂ =>
    ((q : ℂ) ^ k) • RHTower.mPart q f)
  congr 1
  funext p
  exact Φ.eval_pullback (x p) Q

/-- The natural prime realization of the image of a homogeneous constraint map. -/
def HomogeneousConstraintMap.pushforwardRepeatedDensePrimeProfile
    {σ τ : Type*} [Fintype σ] {q : ℕ}
    (Φ : HomogeneousConstraintMap σ τ q)
    (e : ℕ ≃ Nat.Primes) (K : Set (σ → ℂ)) [Nonempty K] :
    Nat.Primes → τ → ℂ :=
  infinitelyRepeatedPrimeProfile e
    (fun n => Φ.apply (denseConstraintProfile K n))

/-- Every point selected in the pushforward profile still has an infinite prime fibre. -/
theorem HomogeneousConstraintMap.pushforwardRepeatedDensePrimeProfile_cofinitelyRecurring
    {σ τ : Type*} [Fintype σ] {q : ℕ}
    (Φ : HomogeneousConstraintMap σ τ q)
    (e : ℕ ≃ Nat.Primes) (K : Set (σ → ℂ)) [Nonempty K] :
    CofinitelyRecurring (Φ.pushforwardRepeatedDensePrimeProfile e K) :=
  infinitelyRepeatedPrimeProfile_cofinitelyRecurring e
    (fun n => Φ.apply (denseConstraintProfile K n))

/-- Polynomial testing on the pushed dense sequence is exactly testing on the full image
constraint. -/
theorem HomogeneousConstraintMap.eval_pushforward_dense_eq_zero_iff
    {σ τ : Type*} [Fintype σ] {q m : ℕ}
    (Φ : HomogeneousConstraintMap σ τ q)
    (K : Set (σ → ℂ)) [Nonempty K]
    (Q : homogeneousSubmodule τ ℂ m) :
    (∀ n, eval (Φ.apply (denseConstraintProfile K n)) Q.1 = 0) ↔
      ∀ w ∈ Φ.apply '' K, eval w Q.1 = 0 := by
  constructor
  · intro hzero
    have hpull : ∀ n, eval (denseConstraintProfile K n) (Φ.pullback Q).1 = 0 := by
      intro n
      rw [Φ.eval_pullback]
      exact hzero n
    have hall := (eval_denseConstraintProfile_eq_zero_iff K (Φ.pullback Q).1).mp hpull
    rintro w ⟨v, hv, rfl⟩
    rw [← Φ.eval_pullback]
    exact hall v hv
  · intro hzero n
    exact hzero (Φ.apply (denseConstraintProfile K n))
      ⟨denseConstraintProfile K n, (TopologicalSpace.denseSeq K n).2, rfl⟩

/-- **Natural image realization.**  Pushing a dense repeated-prime realization through a
homogeneous map realizes exactly the homogeneous vanishing ideal of its geometric image. -/
theorem HomogeneousConstraintMap.pushforward_tailRelation_eq_imageConstraint
    {σ τ : Type*} [Fintype σ] {q : ℕ}
    (Φ : HomogeneousConstraintMap σ τ q)
    (e : ℕ ≃ Nat.Primes) (K : Set (σ → ℂ)) [Nonempty K] (m : ℕ) :
    homogeneousTailRelationSubmodule
        (Φ.pushforwardRepeatedDensePrimeProfile e K) m =
      homogeneousConstraintVanishingSubmodule (Φ.apply '' K) m := by
  rw [homogeneousTailRelationSubmodule_eq_recurringVanishing_of_cofinitelyRecurring
    (Φ.pushforwardRepeatedDensePrimeProfile e K)
    (Φ.pushforwardRepeatedDensePrimeProfile_cofinitelyRecurring e K) m]
  ext Q
  change (∀ v ∈ recurringValueSet
      (infinitelyRepeatedPrimeProfile e
        (fun n => Φ.apply (denseConstraintProfile K n))),
      eval v Q.1 = 0) ↔
    ∀ w ∈ Φ.apply '' K, eval w Q.1 = 0
  rw [recurringValueSet_infinitelyRepeatedPrimeProfile]
  constructor
  · intro hrec
    apply (Φ.eval_pushforward_dense_eq_zero_iff K Q).mp
    intro n
    exact hrec (Φ.apply (denseConstraintProfile K n)) ⟨n, rfl⟩
  · intro hvanish v hv
    obtain ⟨n, rfl⟩ := hv
    exact (Φ.eval_pushforward_dense_eq_zero_iff K Q).mpr hvanish n

/-- The valuation-resolved rank spectrum of the natural pushforward is the Hilbert function of
the image constraint. -/
theorem HomogeneousConstraintMap.valuationTailHilbertFunction_pushforward
    {σ τ : Type*} [Fintype σ] [Fintype τ] {q : ℕ}
    (Φ : HomogeneousConstraintMap σ τ q)
    (e : ℕ ≃ Nat.Primes) (K : Set (σ → ℂ)) [Nonempty K] (m : ℕ) :
    valuationTailHilbertFunction
        (Φ.pushforwardRepeatedDensePrimeProfile e K) m =
      constraintHomogeneousHilbertFunction (Φ.apply '' K) m := by
  unfold valuationTailHilbertFunction constraintHomogeneousHilbertFunction
  rw [Φ.pushforward_tailRelation_eq_imageConstraint e K m]

/-- The recurrent rank spectrum of the natural pushforward is the same image Hilbert function. -/
theorem HomogeneousConstraintMap.recurrentHomogeneousHilbertFunction_pushforward
    {σ τ : Type*} [Fintype σ] [Fintype τ] {q : ℕ}
    (Φ : HomogeneousConstraintMap σ τ q)
    (e : ℕ ≃ Nat.Primes) (K : Set (σ → ℂ)) [Nonempty K] (m : ℕ) :
    recurrentHomogeneousHilbertFunction
        (Φ.pushforwardRepeatedDensePrimeProfile e K) m =
      constraintHomogeneousHilbertFunction (Φ.apply '' K) m := by
  rw [← valuationTailHilbertFunction_eq_recurrent_of_cofinitelyRecurring
    (Φ.pushforwardRepeatedDensePrimeProfile e K)
    (Φ.pushforwardRepeatedDensePrimeProfile_cofinitelyRecurring e K) m]
  exact Φ.valuationTailHilbertFunction_pushforward e K m

end

end GaloisForLFunctions.HTGeometry
