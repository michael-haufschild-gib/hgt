import GaloisForLFunctions.HTGeometry.CompactCofinalEssentialMargin
import GaloisForLFunctions.HTGeometry.DiagonalEllTwoIndexed
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact
import GaloisForLFunctions.HTGeometry.MinimalCompleteSystemChain
import GaloisForLFunctions.HTGeometry.PeriodIncidenceMultiplier
import GaloisForLFunctions.RHTower.PrimeLogExponentialTypeUniqueness
import GaloisForLFunctions.RHTower.SoninCarrierApertureChain
import GaloisForLFunctions.RHTower.SoninOrthonormalCompactVanishing
import GaloisForLFunctions.RHTower.SuzukiCompactL2Fourier

/-!
# Faithful compact prime formation and boundary interception

Literal summably weighted prime sampling is Hilbert--Schmidt. Finite exponential type and
prime-log uniqueness make the sampler injective, hence compact with nonclosed range on an
infinite-dimensional source. Compact boundary reporters cannot restore properness; any reporter
that does restore a joint lower bound must intercept every prime-null sequence and cannot factor
through the sampler. The final section instantiates the full mechanism on `PW²_σ`.
-/

open Filter MeasureTheory Set
open scoped InnerProductSpace Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open ContinuousLinearMap

abbrev PrimeFormationEllTwo := _root_.HTGeometry.IndexedEllTwo Nat.Primes

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Weighted prime-evaluation functional attached to a Riesz representer. -/
def primeFormationRestriction (w : Nat.Primes → ℝ) (k : Nat.Primes → H)
    (p : Nat.Primes) : H →L[ℂ] ℂ :=
  (Real.sqrt (w p) : ℂ) • innerSL ℂ (k p)

@[simp] theorem primeFormationRestriction_apply
    (w : Nat.Primes → ℝ) (k : Nat.Primes → H) (p : Nat.Primes) (x : H) :
    primeFormationRestriction w k p x =
      (Real.sqrt (w p) : ℂ) * inner ℂ (k p) x := by
  simp [primeFormationRestriction]

theorem normSq_primeFormationRestriction
    (w : Nat.Primes → ℝ) (k : Nat.Primes → H) (p : Nat.Primes)
    (hp : 0 ≤ w p) (x : H) :
    ‖primeFormationRestriction w k p x‖ ^ 2 =
      w p * ‖inner ℂ (k p) x‖ ^ 2 := by
  rw [primeFormationRestriction_apply, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt hp]

theorem summable_normSq_primeFormationRestriction
    (w : Nat.Primes → ℝ) (k : Nat.Primes → H)
    (hw0 : ∀ p, 0 ≤ w p) (hw : Summable w)
    {K : ℝ} (_hK : 0 ≤ K) (hk : ∀ p, ‖k p‖ ≤ K) (x : H) :
    Summable (fun p => ‖primeFormationRestriction w k p x‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun p => sq_nonneg _) (fun p => ?_)
    (hw.mul_right ((K * ‖x‖) ^ 2))
  rw [normSq_primeFormationRestriction w k p (hw0 p)]
  have hi : ‖inner ℂ (k p) x‖ ≤ K * ‖x‖ :=
    (norm_inner_le_norm (k p) x).trans
      (mul_le_mul_of_nonneg_right (hk p) (norm_nonneg x))
  exact mul_le_mul_of_nonneg_left (by
    simpa [pow_two] using mul_self_le_mul_self (norm_nonneg _) hi) (hw0 p)

theorem primeFormationRestriction_memℓp
    (w : Nat.Primes → ℝ) (k : Nat.Primes → H)
    (hw0 : ∀ p, 0 ≤ w p) (hw : Summable w)
    {K : ℝ} (hK : 0 ≤ K) (hk : ∀ p, ‖k p‖ ≤ K) (x : H) :
    Memℓp (fun p => primeFormationRestriction w k p x) 2 := by
  apply memℓp_gen
  simpa [Real.rpow_two] using
    summable_normSq_primeFormationRestriction w k hw0 hw hK hk x

/-- Literal weighted all-prime sampling map. -/
def primeFormationLinearMap
    (w : Nat.Primes → ℝ) (k : Nat.Primes → H)
    (hw0 : ∀ p, 0 ≤ w p) (hw : Summable w)
    {K : ℝ} (hK : 0 ≤ K) (hk : ∀ p, ‖k p‖ ≤ K) :
    H →ₗ[ℂ] PrimeFormationEllTwo where
  toFun x := ⟨fun p => primeFormationRestriction w k p x,
    primeFormationRestriction_memℓp w k hw0 hw hK hk x⟩
  map_add' := by
    intro x y
    ext p
    simp [mul_add]
  map_smul' := by
    intro c x
    ext p
    simp

@[simp] theorem primeFormationLinearMap_apply
    (w : Nat.Primes → ℝ) (k : Nat.Primes → H)
    (hw0 : ∀ p, 0 ≤ w p) (hw : Summable w)
    {K : ℝ} (hK : 0 ≤ K) (hk : ∀ p, ‖k p‖ ≤ K)
    (x : H) (p : Nat.Primes) :
    primeFormationLinearMap w k hw0 hw hK hk x p =
      primeFormationRestriction w k p x := rfl

theorem norm_primeFormationLinearMap_le
    (w : Nat.Primes → ℝ) (k : Nat.Primes → H)
    (hw0 : ∀ p, 0 ≤ w p) (hw : Summable w)
    {K : ℝ} (hK : 0 ≤ K) (hk : ∀ p, ‖k p‖ ≤ K) (x : H) :
    ‖primeFormationLinearMap w k hw0 hw hK hk x‖ ≤
      (Real.sqrt (∑' p, w p) * K) * ‖x‖ := by
  have hsum0 : 0 ≤ ∑' p, w p := tsum_nonneg hw0
  have hleft : 0 ≤ ‖primeFormationLinearMap w k hw0 hw hK hk x‖ := norm_nonneg _
  have hright : 0 ≤ (Real.sqrt (∑' p, w p) * K) * ‖x‖ := by positivity
  have hdiag :
      ‖primeFormationLinearMap w k hw0 hw hK hk x‖ ^ 2 =
        ∑' p, ‖primeFormationRestriction w k p x‖ ^ 2 := by
    simpa [Real.rpow_two] using
      lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : Nat.Primes => ℂ) (by norm_num)
        (primeFormationLinearMap w k hw0 hw hK hk x)
  have hsum :
      (∑' p, ‖primeFormationRestriction w k p x‖ ^ 2) ≤
        (∑' p, w p) * (K * ‖x‖) ^ 2 := by
    rw [← tsum_mul_right]
    exact Summable.tsum_le_tsum
      (fun p => by
        rw [normSq_primeFormationRestriction w k p (hw0 p)]
        have hi : ‖inner ℂ (k p) x‖ ≤ K * ‖x‖ :=
          (norm_inner_le_norm (k p) x).trans
            (mul_le_mul_of_nonneg_right (hk p) (norm_nonneg x))
        exact mul_le_mul_of_nonneg_left (by
          simpa [pow_two] using mul_self_le_mul_self (norm_nonneg _) hi) (hw0 p))
      (summable_normSq_primeFormationRestriction w k hw0 hw hK hk x)
      (hw.mul_right _)
  have hpow :
      ‖primeFormationLinearMap w k hw0 hw hK hk x‖ ^ 2 ≤
        ((Real.sqrt (∑' p, w p) * K) * ‖x‖) ^ 2 := by
    rw [hdiag]
    calc
      ∑' p, ‖primeFormationRestriction w k p x‖ ^ 2
          ≤ (∑' p, w p) * (K * ‖x‖) ^ 2 := hsum
      _ = (Real.sqrt (∑' p, w p)) ^ 2 * (K * ‖x‖) ^ 2 := by
        rw [Real.sq_sqrt hsum0]
      _ = ((Real.sqrt (∑' p, w p) * K) * ‖x‖) ^ 2 := by ring
  nlinarith

/-- Bounded weighted all-prime formation operator. -/
def primeFormationOperator
    (w : Nat.Primes → ℝ) (k : Nat.Primes → H)
    (hw0 : ∀ p, 0 ≤ w p) (hw : Summable w)
    {K : ℝ} (hK : 0 ≤ K) (hk : ∀ p, ‖k p‖ ≤ K) :
    H →L[ℂ] PrimeFormationEllTwo :=
  LinearMap.mkContinuous (primeFormationLinearMap w k hw0 hw hK hk)
    (Real.sqrt (∑' p, w p) * K)
    (norm_primeFormationLinearMap_le w k hw0 hw hK hk)

@[simp] theorem primeFormationOperator_apply
    (w : Nat.Primes → ℝ) (k : Nat.Primes → H)
    (hw0 : ∀ p, 0 ≤ w p) (hw : Summable w)
    {K : ℝ} (hK : 0 ≤ K) (hk : ∀ p, ‖k p‖ ≤ K)
    (x : H) (p : Nat.Primes) :
    primeFormationOperator w k hw0 hw hK hk x p =
      (Real.sqrt (w p) : ℂ) * inner ℂ (k p) x := rfl

variable [CompleteSpace H]

/-- The adjoint sends a prime coordinate to its weighted Riesz representer. -/
theorem adjoint_primeFormationOperator_coordinateBasis
    (w : Nat.Primes → ℝ) (k : Nat.Primes → H)
    (hw0 : ∀ p, 0 ≤ w p) (hw : Summable w)
    {K : ℝ} (hK : 0 ≤ K) (hk : ∀ p, ‖k p‖ ≤ K)
    (p : Nat.Primes) :
    adjoint (primeFormationOperator w k hw0 hw hK hk)
        (_root_.HTGeometry.ellTwoCoordinateBasis Nat.Primes p) =
      (Real.sqrt (w p) : ℂ) • k p := by
  classical
  apply ext_inner_left ℂ
  intro x
  rw [adjoint_inner_right, _root_.HTGeometry.ellTwoCoordinateBasis_apply,
    lp.inner_single_right, primeFormationOperator_apply, inner_smul_right]
  simp [RCLike.inner_apply]

/-- Exact coordinate energy of the adjoint. -/
theorem normSq_adjoint_primeFormationOperator_coordinateBasis
    (w : Nat.Primes → ℝ) (k : Nat.Primes → H)
    (hw0 : ∀ p, 0 ≤ w p) (hw : Summable w)
    {K : ℝ} (hK : 0 ≤ K) (hk : ∀ p, ‖k p‖ ≤ K)
    (p : Nat.Primes) :
    ‖adjoint (primeFormationOperator w k hw0 hw hK hk)
        (_root_.HTGeometry.ellTwoCoordinateBasis Nat.Primes p)‖ ^ 2 =
      w p * ‖k p‖ ^ 2 := by
  rw [adjoint_primeFormationOperator_coordinateBasis,
    norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hw0 p)]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem summable_primeFormation_kernelEnergy
    (w : Nat.Primes → ℝ) (k : Nat.Primes → H)
    (hw0 : ∀ p, 0 ≤ w p) (hw : Summable w)
    {K : ℝ} (hk : ∀ p, ‖k p‖ ≤ K) :
    Summable (fun p => w p * ‖k p‖ ^ 2) := by
  have hK0 : 0 ≤ K := le_trans (norm_nonneg (k ⟨2, Nat.prime_two⟩)) (hk ⟨2, Nat.prime_two⟩)
  apply Summable.of_nonneg_of_le
    (fun p => mul_nonneg (hw0 p) (sq_nonneg _)) (fun p => ?_)
    (hw.mul_right (K ^ 2))
  exact mul_le_mul_of_nonneg_left (by
    simpa [pow_two] using mul_self_le_mul_self (norm_nonneg _) (hk p)) (hw0 p)

/-- `(FCP.8)`: exact Hilbert--Schmidt energy and its uniform-kernel bound. -/
theorem primeFormationOperator_isHilbertSchmidt_and_hsNormSq
    (w : Nat.Primes → ℝ) (k : Nat.Primes → H)
    (hw0 : ∀ p, 0 ≤ w p) (hw : Summable w)
    {K : ℝ} (hK : 0 ≤ K) (hk : ∀ p, ‖k p‖ ≤ K) :
    (primeFormationOperator w k hw0 hw hK hk).IsHilbertSchmidt ∧
      ContinuousLinearMap.hsNormSq (primeFormationOperator w k hw0 hw hK hk) =
        ∑' p, w p * ‖k p‖ ^ 2 ∧
      (∑' p, w p * ‖k p‖ ^ 2) ≤ K ^ 2 * ∑' p, w p := by
  let A := primeFormationOperator w k hw0 hw hK hk
  have henergy := summable_primeFormation_kernelEnergy w k hw0 hw hk
  have hadj : (adjoint A).IsHilbertSchmidt := by
    apply isHilbertSchmidt_of_summable
      (_root_.HTGeometry.ellTwoCoordinateBasis Nat.Primes)
    exact henergy.congr fun p =>
      (normSq_adjoint_primeFormationOperator_coordinateBasis w k hw0 hw hK hk p).symm
  have hA : A.IsHilbertSchmidt := by
    have := hadj.adjoint
    simpa [adjoint_adjoint] using this
  refine ⟨hA, ?_, ?_⟩
  · calc
      hsNormSq A = hsNormSq (adjoint A) := (hA.hsNormSq_adjoint).symm
      _ = ∑' p, ‖adjoint A
          (_root_.HTGeometry.ellTwoCoordinateBasis Nat.Primes p)‖ ^ 2 :=
        hsNormSq_eq hadj (_root_.HTGeometry.ellTwoCoordinateBasis Nat.Primes)
      _ = ∑' p, w p * ‖k p‖ ^ 2 := by
        apply tsum_congr
        exact normSq_adjoint_primeFormationOperator_coordinateBasis w k hw0 hw hK hk
  · calc
      (∑' p, w p * ‖k p‖ ^ 2) ≤ ∑' p, K ^ 2 * w p :=
        Summable.tsum_le_tsum
          (fun p => by
            rw [mul_comm (K ^ 2) (w p)]
            exact mul_le_mul_of_nonneg_left (by
              simpa [pow_two] using mul_self_le_mul_self (norm_nonneg _) (hk p)) (hw0 p))
          henergy (hw.mul_left (K ^ 2))
      _ = K ^ 2 * ∑' p, w p := tsum_mul_left

/-- An infinite-dimensional Hilbert space contains a countable orthonormal sequence. -/
theorem exists_orthonormal_sequence_of_not_finiteDimensional
    (hH : ¬ FiniteDimensional ℂ H) :
    ∃ u : ℕ → H, Orthonormal ℂ u := by
  let ι := (exists_hilbertBasis ℂ H).choose
  let b : HilbertBasis ι ℂ H := hsBasis ℂ H
  have hι : Infinite ι := by
    rw [← not_finite_iff_infinite]
    intro hfin
    letI : Finite ι := hfin
    letI : Fintype ι := Fintype.ofFinite ι
    let W : Submodule ℂ H := Submodule.span ℂ (Set.range b)
    haveI : FiniteDimensional ℂ W :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
    have hW : W = ⊤ := by
      simpa [W] using b.dense_span
    apply hH
    exact Module.Finite.equiv (hW ▸ Submodule.topEquiv)
  letI : Infinite ι := hι
  let e : ℕ ↪ ι := Infinite.natEmbedding ι
  exact ⟨b ∘ e, b.orthonormal.comp e e.injective⟩

/-- A compact reporter on an infinite-dimensional Hilbert source has orthonormal escape. -/
theorem exists_orthonormal_compact_escape
    (hH : ¬ FiniteDimensional ℂ H)
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (T : H →L[ℂ] F) (hT : IsCompactOperator T) :
    ∃ u : ℕ → H, Orthonormal ℂ u ∧
      Tendsto (fun n => ‖T (u n)‖) atTop (𝓝 0) := by
  obtain ⟨u, hu⟩ := exists_orthonormal_sequence_of_not_finiteDimensional hH
  exact ⟨u, hu, _root_.RHTower.tendsto_norm_compactOperator_apply_orthonormal hT hu⟩

/-- `(FCP.9)`: summably weighted prime formation has adaptive orthonormal escape. -/
theorem primeFormationOperator_exists_orthonormal_escape
    (hH : ¬ FiniteDimensional ℂ H)
    (w : Nat.Primes → ℝ) (k : Nat.Primes → H)
    (hw0 : ∀ p, 0 ≤ w p) (hw : Summable w)
    {K : ℝ} (hK : 0 ≤ K) (hk : ∀ p, ‖k p‖ ≤ K) :
    ∃ u : ℕ → H, Orthonormal ℂ u ∧
      Tendsto (fun n => ‖primeFormationOperator w k hw0 hw hK hk (u n)‖)
        atTop (𝓝 0) := by
  exact exists_orthonormal_compact_escape hH _
    (primeFormationOperator_isHilbertSchmidt_and_hsNormSq
      w k hw0 hw hK hk).1.isCompactOperator

/-- `(FCP.10)`: compact prime formation has no positive squared lower frame bound. -/
theorem primeFormationOperator_no_positive_lowerBound
    (hH : ¬ FiniteDimensional ℂ H)
    (w : Nat.Primes → ℝ) (k : Nat.Primes → H)
    (hw0 : ∀ p, 0 ≤ w p) (hw : Summable w)
    {K : ℝ} (hK : 0 ≤ K) (hk : ∀ p, ‖k p‖ ≤ K) :
    ¬ ∃ α : ℝ, 0 < α ∧ ∀ x : H,
      α * ‖x‖ ^ 2 ≤ ‖primeFormationOperator w k hw0 hw hK hk x‖ ^ 2 := by
  rintro ⟨α, hα, hlower⟩
  obtain ⟨u, hu, hzero⟩ :=
    primeFormationOperator_exists_orthonormal_escape hH w k hw0 hw hK hk
  have hsqrt : 0 < Real.sqrt α := Real.sqrt_pos.2 hα
  obtain ⟨n, hn⟩ : ∃ n, ‖primeFormationOperator w k hw0 hw hK hk (u n)‖ <
      Real.sqrt α := ((tendsto_order.1 hzero).2 _ hsqrt).exists
  have hbound := hlower (u n)
  rw [hu.norm_eq_one, one_pow, mul_one] at hbound
  nlinarith [Real.sq_sqrt hα.le,
    norm_nonneg (primeFormationOperator w k hw0 hw hK hk (u n))]

omit [CompleteSpace H] in
/-- Prime-log uniqueness makes every strictly positively weighted finite-type sampler injective. -/
theorem primeFormationOperator_injective_of_finiteExponentialType
    (w : Nat.Primes → ℝ) (k : Nat.Primes → H)
    (hwpos : ∀ p, 0 < w p) (hw : Summable w)
    {K : ℝ} (hK : 0 ≤ K) (hk : ∀ p, ‖k p‖ ≤ K)
    (carrier : H → ℂ → ℂ)
    (hrepr : ∀ x (p : Nat.Primes),
      carrier x (Real.log (p : ℕ)) = inner ℂ (k p) x)
    (hdiff : ∀ x, Differentiable ℂ (carrier x))
    (htype : ∀ x, ∃ A C : ℝ, 0 ≤ A ∧ 1 ≤ C ∧
      ∀ z : ℂ, ‖carrier x z‖ ≤ C * Real.exp (A * ‖z‖))
    (hfaithful : ∀ x, carrier x = 0 → x = 0) :
    Function.Injective
      (primeFormationOperator w k (fun p => (hwpos p).le) hw hK hk) := by
  intro x y hxy
  let Aop := primeFormationOperator w k (fun p => (hwpos p).le) hw hK hk
  let d := x - y
  have hA0 : Aop d = 0 := by
    rw [map_sub, hxy, sub_self]
  have hprime : ∀ p : ℕ, p.Prime → carrier d (Real.log p) = 0 := by
    intro p hp
    let q : Nat.Primes := ⟨p, hp⟩
    have hcoord := congrArg (fun v : PrimeFormationEllTwo => v q) hA0
    change (Real.sqrt (w q) : ℂ) * inner ℂ (k q) d = 0 at hcoord
    have hsqrt : (Real.sqrt (w q) : ℂ) ≠ 0 := by
      exact_mod_cast Real.sqrt_ne_zero'.mpr (hwpos q)
    have hinner : inner ℂ (k q) d = 0 := (mul_eq_zero.mp hcoord).resolve_left hsqrt
    rw [hrepr d q]
    exact hinner
  obtain ⟨a, c, ha, hc, hgrowth⟩ := htype d
  have hzero := _root_.RHTower.eq_zero_of_exponentialType_of_primeLog_zeros
    (hdiff d) ha hc hgrowth hprime
  have hd : d = 0 := hfaithful d hzero
  exact sub_eq_zero.mp hd

/-- `(FCP.1)`: faithful compact prime formation has nonclosed range. -/
theorem primeFormationOperator_not_isClosed_range
    (hH : ¬ FiniteDimensional ℂ H)
    (w : Nat.Primes → ℝ) (k : Nat.Primes → H)
    (hwpos : ∀ p, 0 < w p) (hw : Summable w)
    {K : ℝ} (hK : 0 ≤ K) (hk : ∀ p, ‖k p‖ ≤ K)
    (carrier : H → ℂ → ℂ)
    (hrepr : ∀ x (p : Nat.Primes),
      carrier x (Real.log (p : ℕ)) = inner ℂ (k p) x)
    (hdiff : ∀ x, Differentiable ℂ (carrier x))
    (htype : ∀ x, ∃ A C : ℝ, 0 ≤ A ∧ 1 ≤ C ∧
      ∀ z : ℂ, ‖carrier x z‖ ≤ C * Real.exp (A * ‖z‖))
    (hfaithful : ∀ x, carrier x = 0 → x = 0) :
    ¬ IsClosed (Set.range
      (primeFormationOperator w k (fun p => (hwpos p).le) hw hK hk)) := by
  intro hclosed
  let Aop := primeFormationOperator w k (fun p => (hwpos p).le) hw hK hk
  have hcompact : IsCompactOperator Aop :=
    (primeFormationOperator_isHilbertSchmidt_and_hsNormSq
      w k (fun p => (hwpos p).le) hw hK hk).1.isCompactOperator
  have hinj : Function.Injective Aop :=
    primeFormationOperator_injective_of_finiteExponentialType
      w k hwpos hw hK hk carrier hrepr hdiff htype hfaithful
  exact hH (finiteDimensional_of_compact_injective_isClosed_range
    Aop hcompact hinj hclosed)

/-! ## Boundary interception -/

/-- `(FCP.13)`: two compact reporters admit one common orthonormal escape sequence. -/
theorem compactBoundary_exists_orthonormal_joint_escape
    (hH : ¬ FiniteDimensional ℂ H)
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z)
    (hA : IsCompactOperator A) (hR : IsCompactOperator R) :
    IsCompactOperator (A.prod R) ∧
      (∃ u : ℕ → H, Orthonormal ℂ u ∧
        Tendsto (fun n => ‖A (u n)‖ ^ 2 + ‖R (u n)‖ ^ 2) atTop (𝓝 0)) := by
  have hpair := isCompactOperator_clmProd A R hA hR
  obtain ⟨u, hu⟩ := exists_orthonormal_sequence_of_not_finiteDimensional hH
  have hAz := _root_.RHTower.tendsto_norm_compactOperator_apply_orthonormal hA hu
  have hRz := _root_.RHTower.tendsto_norm_compactOperator_apply_orthonormal hR hu
  refine ⟨hpair, u, hu, ?_⟩
  simpa using (hAz.pow 2).add (hRz.pow 2)

/-- A jointly compact boundary packet cannot satisfy any positive squared lower bound. -/
theorem compactBoundary_no_positive_joint_lowerBound
    (hH : ¬ FiniteDimensional ℂ H)
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z)
    (hA : IsCompactOperator A) (hR : IsCompactOperator R) :
    ¬ ∃ α : ℝ, 0 < α ∧ ∀ x : H,
      α * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2 + ‖R x‖ ^ 2 := by
  rintro ⟨α, hα, hlower⟩
  obtain ⟨_, u, hu, hzero⟩ :=
    compactBoundary_exists_orthonormal_joint_escape hH A R hA hR
  have hα2 : 0 < α / 2 := by positivity
  obtain ⟨n, hn⟩ : ∃ n, ‖A (u n)‖ ^ 2 + ‖R (u n)‖ ^ 2 < α :=
    ((tendsto_order.1 hzero).2 α hα).exists
  have hbound := hlower (u n)
  rw [hu.norm_eq_one, one_pow, mul_one] at hbound
  linarith

/-- The finite-type prime sampler plus any compact boundary reporter remains nonproper. -/
theorem primeFormation_compactBoundary_no_positive_joint_lowerBound
    (hH : ¬ FiniteDimensional ℂ H)
    {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (w : Nat.Primes → ℝ) (k : Nat.Primes → H)
    (hw0 : ∀ p, 0 ≤ w p) (hw : Summable w)
    {K : ℝ} (hK : 0 ≤ K) (hk : ∀ p, ‖k p‖ ≤ K)
    (R : H →L[ℂ] Z) (hR : IsCompactOperator R) :
    IsCompactOperator ((primeFormationOperator w k hw0 hw hK hk).prod R) ∧
      (∃ u : ℕ → H, Orthonormal ℂ u ∧
        Tendsto (fun n =>
          ‖primeFormationOperator w k hw0 hw hK hk (u n)‖ ^ 2 + ‖R (u n)‖ ^ 2)
          atTop (𝓝 0)) ∧
      ¬ ∃ α : ℝ, 0 < α ∧ ∀ x : H,
        α * ‖x‖ ^ 2 ≤
          ‖primeFormationOperator w k hw0 hw hK hk x‖ ^ 2 + ‖R x‖ ^ 2 := by
  have hA := (primeFormationOperator_isHilbertSchmidt_and_hsNormSq
    w k hw0 hw hK hk).1.isCompactOperator
  exact ⟨(compactBoundary_exists_orthonormal_joint_escape hH _ R hA hR).1,
    (compactBoundary_exists_orthonormal_joint_escape hH _ R hA hR).2,
    compactBoundary_no_positive_joint_lowerBound hH _ R hA hR⟩

omit [CompleteSpace H] in
/-- `(FCP.15)`: every unit prime-null sequence is asymptotically intercepted at `sqrt α`. -/
theorem boundary_intercepts_every_unit_primeNull_sequence
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z)
    {α : ℝ} (hα : 0 < α)
    (hlower : ∀ x : H, α * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2 + ‖R x‖ ^ 2)
    (u : ℕ → H) (hu : ∀ n, ‖u n‖ = 1)
    (hAzero : Tendsto (fun n => ‖A (u n)‖) atTop (𝓝 0)) :
    Real.sqrt α ≤ Filter.liminf (fun n => ‖R (u n)‖) atTop := by
  let g : ℕ → ℝ := fun n => Real.sqrt (max 0 (α - ‖A (u n)‖ ^ 2))
  have hAsq : Tendsto (fun n => ‖A (u n)‖ ^ 2) atTop (𝓝 0) := by
    simpa using hAzero.pow 2
  have hinside : Tendsto (fun n => max 0 (α - ‖A (u n)‖ ^ 2))
      atTop (𝓝 α) := by
    have hsub : Tendsto (fun n => α - ‖A (u n)‖ ^ 2) atTop (𝓝 (α - 0)) :=
      tendsto_const_nhds.sub hAsq
    have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
    have hmax := hzero.max hsub
    simpa [max_eq_right hα.le] using hmax
  have hg : Tendsto g atTop (𝓝 (Real.sqrt α)) := by
    change Tendsto ((fun x : ℝ => Real.sqrt x) ∘
      (fun n => max 0 (α - ‖A (u n)‖ ^ 2))) atTop (𝓝 (Real.sqrt α))
    exact Real.continuous_sqrt.continuousAt.tendsto.comp hinside
  have hle : ∀ n, g n ≤ ‖R (u n)‖ := by
    intro n
    have hbound := hlower (u n)
    rw [hu n, one_pow, mul_one] at hbound
    have hmaxle : max 0 (α - ‖A (u n)‖ ^ 2) ≤ ‖R (u n)‖ ^ 2 := by
      rw [max_le_iff]
      constructor
      · exact sq_nonneg _
      · linarith
    dsimp [g]
    have hsqrt := Real.sqrt_le_sqrt hmaxle
    simpa [Real.sqrt_sq (norm_nonneg _)] using hsqrt
  have hgbounded : Filter.IsBoundedUnder (fun x₁ x₂ : ℝ => x₁ ≥ x₂) atTop g :=
    ⟨0, by
      rw [Filter.eventually_map]
      exact Filter.Eventually.of_forall fun n => Real.sqrt_nonneg _⟩
  have hRbounded : Filter.IsBoundedUnder (fun x₁ x₂ : ℝ => x₁ ≤ x₂) atTop
      (fun n => ‖R (u n)‖) :=
    ⟨‖R‖, by
      rw [Filter.eventually_map]
      exact Filter.Eventually.of_forall fun n => by
        simpa [hu n] using R.le_opNorm (u n)⟩
  have hlim := Filter.liminf_le_liminf
    (Filter.Eventually.of_forall hle) hgbounded hRbounded.isCoboundedUnder_ge
  rwa [hg.liminf_eq] at hlim

/-- Any boundary satisfying the survivor lower bound is noncompact. -/
theorem boundary_not_isCompactOperator_of_joint_lowerBound
    (hH : ¬ FiniteDimensional ℂ H)
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z)
    (hA : IsCompactOperator A)
    {α : ℝ} (hα : 0 < α)
    (hlower : ∀ x : H, α * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2 + ‖R x‖ ^ 2) :
    ¬ IsCompactOperator R := by
  intro hR
  exact compactBoundary_no_positive_joint_lowerBound hH A R hA hR
    ⟨α, hα, hlower⟩

omit [CompleteSpace H] in
/-- A survivor boundary cannot factor boundedly through the prime-null reporter. -/
theorem boundary_not_factors_through_of_joint_lowerBound
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z)
    {α : ℝ} (hα : 0 < α)
    (hlower : ∀ x : H, α * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2 + ‖R x‖ ^ 2)
    (u : ℕ → H) (hu : ∀ n, ‖u n‖ = 1)
    (hAzero : Tendsto (fun n => ‖A (u n)‖) atTop (𝓝 0)) :
    ¬ ∃ S : Y →L[ℂ] Z, R = S ∘L A := by
  rintro ⟨S, rfl⟩
  have hRzero : Tendsto (fun n => ‖(S ∘L A) (u n)‖) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n => norm_nonneg _
    · exact Filter.Eventually.of_forall fun n => S.le_opNorm (A (u n))
    · simpa using hAzero.const_mul ‖S‖
  have hsqrt : 0 < Real.sqrt α := Real.sqrt_pos.2 hα
  obtain ⟨n, hnA, hnR⟩ : ∃ n,
      ‖A (u n)‖ < Real.sqrt α / 2 ∧
      ‖(S ∘L A) (u n)‖ < Real.sqrt α / 2 := by
    have hhalf : 0 < Real.sqrt α / 2 := by positivity
    exact ((tendsto_order.1 hAzero).2 _ hhalf).and
      ((tendsto_order.1 hRzero).2 _ hhalf) |>.exists
  have hbound := hlower (u n)
  rw [hu n, one_pow, mul_one] at hbound
  nlinarith [Real.sq_sqrt hα.le, norm_nonneg (A (u n)),
    norm_nonneg ((S ∘L A) (u n))]

/-! ## Functional-equation and recovery neutrality -/

/-- Source-unitary and receiver-isometric transport of a rectangular reporter. -/
def formationIsometricTransport
    {H' Y Y' : Type*}
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Y'] [InnerProductSpace ℂ Y']
    (u : H ≃ₗᵢ[ℂ] H') (v : Y →ₗᵢ[ℂ] Y') (A : H →L[ℂ] Y) :
    H' →L[ℂ] Y' :=
  v.toContinuousLinearMap ∘L A ∘L u.symm.toLinearIsometry.toContinuousLinearMap

omit [CompleteSpace H] in
@[simp] theorem formationIsometricTransport_apply
    {H' Y Y' : Type*}
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Y'] [InnerProductSpace ℂ Y']
    (u : H ≃ₗᵢ[ℂ] H') (v : Y →ₗᵢ[ℂ] Y') (A : H →L[ℂ] Y) (x : H') :
    formationIsometricTransport u v A x = v (A (u.symm x)) := by
  rfl

omit [CompleteSpace H] in
theorem norm_formationIsometricTransport
    {H' Y Y' : Type*}
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Y'] [InnerProductSpace ℂ Y']
    (u : H ≃ₗᵢ[ℂ] H') (v : Y →ₗᵢ[ℂ] Y') (A : H →L[ℂ] Y) (x : H') :
    ‖formationIsometricTransport u v A x‖ = ‖A (u.symm x)‖ := by
  rw [formationIsometricTransport_apply, v.norm_map]

theorem formationIsometricTransport_isHilbertSchmidt
    {H' Y Y' : Type*}
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Y'] [InnerProductSpace ℂ Y'] [CompleteSpace Y']
    (u : H ≃ₗᵢ[ℂ] H') (v : Y →ₗᵢ[ℂ] Y') (A : H →L[ℂ] Y)
    (hA : A.IsHilbertSchmidt) :
    (formationIsometricTransport u v A).IsHilbertSchmidt :=
  (hA.comp_right u.symm.toLinearIsometry.toContinuousLinearMap).comp_left
    v.toContinuousLinearMap

/-- Isometric transport preserves Hilbert--Schmidt energy exactly. -/
theorem hsNormSq_formationIsometricTransport
    {H' Y Y' : Type*}
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Y'] [InnerProductSpace ℂ Y'] [CompleteSpace Y']
    (u : H ≃ₗᵢ[ℂ] H') (v : Y →ₗᵢ[ℂ] Y') (A : H →L[ℂ] Y)
    (hA : A.IsHilbertSchmidt) :
    hsNormSq (formationIsometricTransport u v A) = hsNormSq A := by
  let S : H' →L[ℂ] Y := A ∘L u.symm.toLinearIsometry.toContinuousLinearMap
  have hS : S.IsHilbertSchmidt :=
    hA.comp_right u.symm.toLinearIsometry.toContinuousLinearMap
  have hright : hsNormSq S = hsNormSq A := by
    calc
      hsNormSq S = hsNormSq (adjoint S) := hS.hsNormSq_adjoint.symm
      _ = hsNormSq (u.toLinearIsometry.toContinuousLinearMap ∘L adjoint A) := by
        congr 1
        dsimp [S]
        rw [adjoint_comp]
        have huadj : adjoint u.symm.toLinearIsometry.toContinuousLinearMap =
            u.toLinearIsometry.toContinuousLinearMap := by
          change adjoint (u.symm : H' →L[ℂ] H) = (u : H →L[ℂ] H')
          simpa using LinearIsometryEquiv.adjoint_eq_symm u.symm
        change adjoint u.symm.toLinearIsometry.toContinuousLinearMap ∘L adjoint A = _
        rw [huadj]
      _ = hsNormSq (adjoint A) :=
        hsNormSq_comp_left_eq_of_norm_map hA.adjoint
          u.toLinearIsometry.toContinuousLinearMap (fun x => u.norm_map x)
      _ = hsNormSq A := hA.hsNormSq_adjoint
  change hsNormSq (v.toContinuousLinearMap ∘L S) = hsNormSq A
  rw [hsNormSq_comp_left_eq_of_norm_map hS
    v.toContinuousLinearMap (fun x => v.norm_map x), hright]

omit [CompleteSpace H] in
/-- Injectivity is preserved by source-unitary and receiver-isometric transport. -/
theorem formationIsometricTransport_injective
    {H' Y Y' : Type*}
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Y'] [InnerProductSpace ℂ Y']
    (u : H ≃ₗᵢ[ℂ] H') (v : Y →ₗᵢ[ℂ] Y') (A : H →L[ℂ] Y)
    (hA : Function.Injective A) :
    Function.Injective (formationIsometricTransport u v A) := by
  intro x y hxy
  have hxy' : v (A (u.symm x)) = v (A (u.symm y)) := by
    simpa using hxy
  have hv : A (u.symm x) = A (u.symm y) := v.injective hxy'
  exact u.symm.injective (hA hv)

omit [CompleteSpace H] in
theorem not_finiteDimensional_unitary_target
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (hH : ¬ FiniteDimensional ℂ H) (u : H ≃ₗᵢ[ℂ] H') :
    ¬ FiniteDimensional ℂ H' := by
  intro hH'
  apply hH
  exact FiniteDimensional.of_injective u.toLinearEquiv.toLinearMap u.injective

omit [CompleteSpace H] in
/-- Compact faithful nonclosed-range obstruction survives every isometric transport. -/
theorem formationIsometricTransport_compact_injective_nonclosed
    {H' Y Y' : Type*}
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Y'] [InnerProductSpace ℂ Y'] [CompleteSpace Y']
    (hH : ¬ FiniteDimensional ℂ H)
    (u : H ≃ₗᵢ[ℂ] H') (v : Y →ₗᵢ[ℂ] Y') (A : H →L[ℂ] Y)
    (hcompact : IsCompactOperator A) (hinj : Function.Injective A) :
    IsCompactOperator (formationIsometricTransport u v A) ∧
      Function.Injective (formationIsometricTransport u v A) ∧
      ¬ IsClosed (Set.range (formationIsometricTransport u v A)) := by
  have hcompact' : IsCompactOperator (formationIsometricTransport u v A) :=
    (hcompact.comp_clm u.symm.toLinearIsometry.toContinuousLinearMap).clm_comp
      v.toContinuousLinearMap
  have hinj' := formationIsometricTransport_injective u v A hinj
  refine ⟨hcompact', hinj', ?_⟩
  intro hclosed
  exact not_finiteDimensional_unitary_target hH u
    (finiteDimensional_of_compact_injective_isClosed_range
      _ hcompact' hinj' hclosed)

omit [CompleteSpace H] in
/-- Every positive lower-frame bound is invariant under isometric transport. -/
theorem formationIsometricTransport_lowerBound_iff
    {H' Y Y' : Type*}
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Y'] [InnerProductSpace ℂ Y']
    (u : H ≃ₗᵢ[ℂ] H') (v : Y →ₗᵢ[ℂ] Y') (A : H →L[ℂ] Y)
    (α : ℝ) :
    (∀ x : H', α * ‖x‖ ^ 2 ≤ ‖formationIsometricTransport u v A x‖ ^ 2) ↔
      ∀ x : H, α * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2 := by
  constructor
  · intro h x
    have hx := h (u x)
    simpa [norm_formationIsometricTransport] using hx
  · intro h x
    have hx := h (u.symm x)
    simpa [norm_formationIsometricTransport] using hx

/-! ## Concrete Paley--Wiener prime formation -/

local instance primeFormationCompactNonproperLocalInst1 : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- Frequency-side realization of `PW²_σ`: `L²` data supported on `[-σ, σ]`. -/
abbrev PrimePaleyWienerSource (σ : ℝ) :=
  _root_.RHTower.physicalForbidden (Set.Icc (-σ) σ) measurableSet_Icc

noncomputable instance primePaleyWienerSource_completeSpace (σ : ℝ) :
    CompleteSpace (PrimePaleyWienerSource σ) := by
  letI : IsClosed
      ((_root_.RHTower.physicalForbidden (Set.Icc (-σ) σ) measurableSet_Icc :
        Submodule ℂ _root_.RHTower.SoninL2) : Set _root_.RHTower.SoninL2) :=
    isClosed_of_hasOrthogonalProjection _
  exact IsClosed.completeSpace_coe

/-- Entire Paley--Wiener carrier obtained from the compactly supported `L²` datum. -/
def primePaleyWienerEntire (σ : ℝ) (f : PrimePaleyWienerSource σ) : ℂ → ℂ :=
  _root_.RHTower.suzukiCompactL2Fourier σ (f : _root_.RHTower.SoninL2)

theorem suzukiCutoff_primePaleyWienerSource
    (σ : ℝ) (f : PrimePaleyWienerSource σ) :
    _root_.RHTower.suzukiCutoff σ (f : _root_.RHTower.SoninL2) = f := by
  rw [_root_.RHTower.suzukiCutoff,
    _root_.RHTower.indicatorCutoff_eq_physicalForbidden_starProjection]
  exact Submodule.starProjection_eq_self_iff.mpr f.property

theorem differentiable_primePaleyWienerEntire
    {σ : ℝ} (hσ : 0 ≤ σ) (f : PrimePaleyWienerSource σ) :
    Differentiable ℂ (primePaleyWienerEntire σ f) :=
  _root_.RHTower.differentiable_suzukiCompactL2Fourier hσ f

theorem primePaleyWienerEntire_exponentialType
    {σ : ℝ} (hσ : 0 ≤ σ) (f : PrimePaleyWienerSource σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : ℂ,
      ‖primePaleyWienerEntire σ f z‖ ≤ C * Real.exp (σ * ‖z‖) :=
  _root_.RHTower.suzukiCompactL2Fourier_exponentialType hσ f

theorem primePaleyWienerKernel_memLp (σ t : ℝ) :
    MemLp ((Set.Icc (-σ) σ).indicator fun y : ℝ =>
      Complex.exp (((-t * y : ℝ) : ℂ) * Complex.I)) 2
      (volume : Measure ℝ) := by
  apply (memLp_indicator_iff_restrict measurableSet_Icc).2
  refine MemLp.of_bound (p := (2 : ENNReal)) ?_ 1 ?_
  · exact (by fun_prop : Continuous fun y : ℝ =>
      Complex.exp (((-t * y : ℝ) : ℂ) * Complex.I)).aestronglyMeasurable
  · filter_upwards with y
    rw [Complex.norm_exp_ofReal_mul_I]

/-- Zero-extended plane wave representing evaluation at the real point `t`. -/
def primePaleyWienerKernelAmbient (σ t : ℝ) : _root_.RHTower.SoninL2 :=
  (primePaleyWienerKernel_memLp σ t).toLp
    ((Set.Icc (-σ) σ).indicator fun y : ℝ =>
      Complex.exp (((-t * y : ℝ) : ℂ) * Complex.I))

theorem primePaleyWienerKernelAmbient_coeFn (σ t : ℝ) :
    (primePaleyWienerKernelAmbient σ t : ℝ → ℂ) =ᵐ[volume]
      (Set.Icc (-σ) σ).indicator fun y : ℝ =>
        Complex.exp (((-t * y : ℝ) : ℂ) * Complex.I) :=
  MemLp.coeFn_toLp (primePaleyWienerKernel_memLp σ t)

theorem primePaleyWienerKernelAmbient_mem (σ t : ℝ) :
    primePaleyWienerKernelAmbient σ t ∈
      _root_.RHTower.physicalForbidden (Set.Icc (-σ) σ) measurableSet_Icc := by
  rw [_root_.RHTower.mem_physicalForbidden_iff]
  filter_upwards [primePaleyWienerKernelAmbient_coeFn σ t] with x hx
  intro hout
  rw [hx, Set.indicator_of_notMem hout]

/-- Literal Paley--Wiener evaluation kernel at `t`. -/
def primePaleyWienerKernel (σ t : ℝ) : PrimePaleyWienerSource σ :=
  ⟨primePaleyWienerKernelAmbient σ t,
    primePaleyWienerKernelAmbient_mem σ t⟩

/-- Reproducing identity for the literal compact-support Paley--Wiener model. -/
theorem primePaleyWienerEntire_eq_inner
    (σ : ℝ) (f : PrimePaleyWienerSource σ) (t : ℝ) :
    primePaleyWienerEntire σ f t = inner ℂ (primePaleyWienerKernel σ t) f := by
  change (∫ y : ℝ, (_root_.RHTower.suzukiCutoff σ
      (f : _root_.RHTower.SoninL2)) y *
        Complex.exp (Complex.I * (t : ℂ) * (y : ℂ))) =
      inner ℂ (primePaleyWienerKernelAmbient σ t)
        (f : _root_.RHTower.SoninL2)
  rw [suzukiCutoff_primePaleyWienerSource, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  have hsupp := (_root_.RHTower.mem_physicalForbidden_iff
    (Set.Icc (-σ) σ) measurableSet_Icc (f : _root_.RHTower.SoninL2)).mp f.property
  filter_upwards [primePaleyWienerKernelAmbient_coeFn σ t, hsupp] with y hy hfy
  change (f : _root_.RHTower.SoninL2) y *
      Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)) =
    inner ℂ (primePaleyWienerKernelAmbient σ t y)
      ((f : _root_.RHTower.SoninL2) y)
  rw [hy]
  by_cases hymem : y ∈ Set.Icc (-σ) σ
  · rw [Set.indicator_of_mem hymem, RCLike.inner_apply, ← Complex.exp_conj]
    have hstar :
        (starRingEnd ℂ) (((-t * y : ℝ) : ℂ) * Complex.I) =
          (((t * y : ℝ) : ℂ) * Complex.I) := by simp
    rw [hstar]
    congr 2
    push_cast
    ring
  · have hfzero : (f : _root_.RHTower.SoninL2) y = 0 := by
      exact hfy hymem
    rw [Set.indicator_of_notMem hymem, hfzero]
    simp

/-- Every real evaluation kernel has squared norm `2σ`. -/
theorem norm_primePaleyWienerKernel_sq
    (σ t : ℝ) (hσ : 0 ≤ σ) :
    ‖primePaleyWienerKernel σ t‖ ^ 2 = 2 * σ := by
  change ‖primePaleyWienerKernelAmbient σ t‖ ^ 2 = 2 * σ
  rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  calc
    ∫ y, ‖primePaleyWienerKernelAmbient σ t y‖ ^ 2 ∂volume =
        ∫ y in Set.Icc (-σ) σ, (1 : ℝ) ∂volume := by
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards [primePaleyWienerKernelAmbient_coeFn σ t] with y hy
      rw [hy]
      by_cases hymem : y ∈ Set.Icc (-σ) σ
      · simp [hymem, Complex.norm_exp]
      · simp [hymem]
    _ = 2 * σ := by
      simp [measureReal_def, Real.volume_Icc]
      rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ σ + σ)]
      ring

theorem norm_primePaleyWienerKernel
    (σ t : ℝ) (hσ : 0 ≤ σ) :
    ‖primePaleyWienerKernel σ t‖ = Real.sqrt (2 * σ) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [norm_primePaleyWienerKernel_sq σ t hσ,
    Real.sq_sqrt (mul_nonneg (by norm_num) hσ)]

/-- The entire carrier is faithful on the compact-support source. -/
theorem primePaleyWienerEntire_faithful
    {σ : ℝ} (hσ : 0 ≤ σ) (f : PrimePaleyWienerSource σ)
    (hzero : primePaleyWienerEntire σ f = 0) : f = 0 := by
  apply Subtype.ext
  exact _root_.RHTower.eq_zero_of_supported_fourier_constant_on_xiZeros
    hσ (suzukiCutoff_primePaleyWienerSource σ f) (c := 0) (by
      intro z _
      exact congrFun hzero z)

/-- Positive-aperture compact-support Paley--Wiener source is infinite dimensional. -/
theorem primePaleyWienerSource_not_finiteDimensional
    {σ : ℝ} (hσ : 0 < σ) :
    ¬ FiniteDimensional ℂ (PrimePaleyWienerSource σ) := by
  let u : ℕ → PrimePaleyWienerSource σ := fun n =>
    ⟨_root_.RHTower.evenShellVector (σ / 2) σ (by linarith) n, by
      rw [_root_.RHTower.mem_physicalForbidden_iff]
      filter_upwards [_root_.RHTower.normalizedIndicator_ae
        (_root_.RHTower.evenShellCell (σ / 2) σ n)
        (_root_.RHTower.measurableSet_evenShellCell (σ / 2) σ n)
        (_root_.RHTower.evenShellCell_measure_ne_top (by linarith) n)] with x hx
      intro hout
      change _root_.RHTower.normalizedIndicator
        (_root_.RHTower.evenShellCell (σ / 2) σ n)
        (_root_.RHTower.measurableSet_evenShellCell (σ / 2) σ n)
        (_root_.RHTower.evenShellCell_measure_ne_top (by linarith) n) x = 0
      have hnot : x ∉ _root_.RHTower.evenShellCell (σ / 2) σ n := fun hmem => hout
        (_root_.RHTower.evenShellCell_subset_Icc (by linarith) n hmem)
      rw [hx, Set.indicator_of_notMem hnot]
      simp⟩
  have huAmbient : LinearIndependent ℂ
      (_root_.RHTower.evenShellVector (σ / 2) σ (by linarith)) :=
    (_root_.RHTower.evenShellVector_orthonormal
      (σ / 2) σ (by linarith) (by linarith)).linearIndependent
  have hu : LinearIndependent ℂ u := by
    apply LinearIndependent.of_comp
      (Submodule.subtype (_root_.RHTower.physicalForbidden
        (Set.Icc (-σ) σ) measurableSet_Icc))
    simpa [u, Function.comp_def] using huAmbient
  intro hfinite
  letI : FiniteDimensional ℂ (PrimePaleyWienerSource σ) := hfinite
  exact Module.Finite.not_linearIndependent_of_infinite u hu

/-- Literal summably weighted prime sampler on `PW²_σ`. -/
def paleyWienerPrimeFormationOperator
    (σ : ℝ) (hσ : 0 ≤ σ) (w : Nat.Primes → ℝ)
    (hwpos : ∀ p, 0 < w p) (hw : Summable w) :
    PrimePaleyWienerSource σ →L[ℂ] PrimeFormationEllTwo :=
  primeFormationOperator w
    (fun p => primePaleyWienerKernel σ (Real.log (p : ℕ)))
    (fun p => (hwpos p).le) hw (Real.sqrt_nonneg _)
    (fun _ => (norm_primePaleyWienerKernel σ _ hσ).le)

@[simp] theorem paleyWienerPrimeFormationOperator_apply
    (σ : ℝ) (hσ : 0 ≤ σ) (w : Nat.Primes → ℝ)
    (hwpos : ∀ p, 0 < w p) (hw : Summable w)
    (f : PrimePaleyWienerSource σ) (p : Nat.Primes) :
    paleyWienerPrimeFormationOperator σ hσ w hwpos hw f p =
      (Real.sqrt (w p) : ℂ) *
        primePaleyWienerEntire σ f (Real.log (p : ℕ)) := by
  rw [paleyWienerPrimeFormationOperator, primeFormationOperator_apply,
    ← primePaleyWienerEntire_eq_inner]

/-- Exact Hilbert--Schmidt energy of the concrete Paley--Wiener prime sampler. -/
theorem paleyWienerPrimeFormationOperator_isHilbertSchmidt_and_hsNormSq
    {σ : ℝ} (hσ : 0 ≤ σ) (w : Nat.Primes → ℝ)
    (hwpos : ∀ p, 0 < w p) (hw : Summable w) :
    (paleyWienerPrimeFormationOperator σ hσ w hwpos hw).IsHilbertSchmidt ∧
      hsNormSq (paleyWienerPrimeFormationOperator σ hσ w hwpos hw) =
        (2 * σ) * ∑' p, w p := by
  let k : Nat.Primes → PrimePaleyWienerSource σ := fun p =>
    primePaleyWienerKernel σ (Real.log (p : ℕ))
  have hk : ∀ p, ‖k p‖ ≤ Real.sqrt (2 * σ) := fun p => by
    rw [norm_primePaleyWienerKernel σ _ hσ]
  have hbase := primeFormationOperator_isHilbertSchmidt_and_hsNormSq
    w k (fun p => (hwpos p).le) hw (Real.sqrt_nonneg _) hk
  have hop : primeFormationOperator w k (fun p => (hwpos p).le) hw
      (Real.sqrt_nonneg _) hk =
      paleyWienerPrimeFormationOperator σ hσ w hwpos hw := by
    rfl
  rw [← hop]
  refine ⟨hbase.1, hbase.2.1.trans ?_⟩
  calc
    (∑' p, w p * ‖k p‖ ^ 2) = ∑' p, w p * (2 * σ) := by
      apply tsum_congr
      intro p
      rw [norm_primePaleyWienerKernel_sq σ _ hσ]
    _ = (∑' p, w p) * (2 * σ) := tsum_mul_right
    _ = (2 * σ) * ∑' p, w p := by ring

/-- Concrete `PW²_σ` instance of faithful compact nonproper prime formation. -/
theorem paleyWienerPrimeFormation_compact_injective_nonproper
    {σ : ℝ} (hσ : 0 < σ) (w : Nat.Primes → ℝ)
    (hwpos : ∀ p, 0 < w p) (hw : Summable w) :
    let A := paleyWienerPrimeFormationOperator σ hσ.le w hwpos hw
    A.IsHilbertSchmidt ∧ IsCompactOperator A ∧ Function.Injective A ∧
      ¬ IsClosed (Set.range A) ∧
      (∃ u : ℕ → PrimePaleyWienerSource σ, Orthonormal ℂ u ∧
        Tendsto (fun n => ‖A (u n)‖) atTop (𝓝 0)) ∧
      ¬ ∃ α : ℝ, 0 < α ∧ ∀ f : PrimePaleyWienerSource σ,
        α * ‖f‖ ^ 2 ≤ ‖A f‖ ^ 2 := by
  dsimp only
  let k : Nat.Primes → PrimePaleyWienerSource σ := fun p =>
    primePaleyWienerKernel σ (Real.log (p : ℕ))
  have hk : ∀ p, ‖k p‖ ≤ Real.sqrt (2 * σ) := fun p => by
    rw [norm_primePaleyWienerKernel σ _ hσ.le]
  let A := primeFormationOperator w k (fun p => (hwpos p).le) hw
    (Real.sqrt_nonneg _) hk
  have hop : A = paleyWienerPrimeFormationOperator σ hσ.le w hwpos hw := by rfl
  have hH := primePaleyWienerSource_not_finiteDimensional hσ
  have hhs : A.IsHilbertSchmidt :=
    (primeFormationOperator_isHilbertSchmidt_and_hsNormSq
      w k (fun p => (hwpos p).le) hw (Real.sqrt_nonneg _) hk).1
  have hinj : Function.Injective A :=
    primeFormationOperator_injective_of_finiteExponentialType
      w k hwpos hw (Real.sqrt_nonneg _) hk
      (primePaleyWienerEntire σ)
      (fun f p => primePaleyWienerEntire_eq_inner σ f (Real.log (p : ℕ)))
      (fun f => differentiable_primePaleyWienerEntire hσ.le f)
      (fun f => by
        obtain ⟨C, hC, hbound⟩ :=
          primePaleyWienerEntire_exponentialType hσ.le f
        exact ⟨σ, C, hσ.le, hC, hbound⟩)
      (fun f => primePaleyWienerEntire_faithful hσ.le f)
  have hclosed : ¬ IsClosed (Set.range A) :=
    primeFormationOperator_not_isClosed_range hH
      w k hwpos hw (Real.sqrt_nonneg _) hk
      (primePaleyWienerEntire σ)
      (fun f p => primePaleyWienerEntire_eq_inner σ f (Real.log (p : ℕ)))
      (fun f => differentiable_primePaleyWienerEntire hσ.le f)
      (fun f => by
        obtain ⟨C, hC, hbound⟩ :=
          primePaleyWienerEntire_exponentialType hσ.le f
        exact ⟨σ, C, hσ.le, hC, hbound⟩)
      (fun f => primePaleyWienerEntire_faithful hσ.le f)
  have hescape := primeFormationOperator_exists_orthonormal_escape hH
    w k (fun p => (hwpos p).le) hw (Real.sqrt_nonneg _) hk
  have hnolower := primeFormationOperator_no_positive_lowerBound hH
    w k (fun p => (hwpos p).le) hw (Real.sqrt_nonneg _) hk
  rw [← hop]
  exact ⟨hhs, hhs.isCompactOperator, hinj, hclosed, hescape, hnolower⟩

end

end GaloisForLFunctions.HTGeometry
