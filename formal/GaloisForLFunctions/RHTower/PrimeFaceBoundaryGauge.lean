import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Nat.Prime.Basic

/-!
# Dirichlet prime-face boundary graphs have a constant topological family

A coefficient family assigns a complex number to every finite set of primes. Its boundary row
at a face `A` sums over primes outside `A`, with the alternating deletion sign and weight `p^(-s)`.
The domain requires each row to be unconditionally summable. All spaces use the product topology
and its induced subtype topology.

Multiplying the coefficient at `A` by the product of its prime weights is a homeomorphism. It
transports the weighted rows, their summability domain and their boundary graph to the unweighted
ones. The coordinate changes and inverses are jointly continuous in the complex parameter, giving
an explicit trivialization of the entire graph family.

This is a statement about the specified coefficient domain. It asserts neither that the boundary
is continuous nor that this domain is a chain complex or an analytic completion of exterior chains.
It does not transport an independently fixed stronger norm, distinguished source or extra arithmetic
constraint, and supplies no zeta-zero correspondence.
-/

open scoped BigOperators

noncomputable section
namespace RHTower

/-- All face coefficients, with the product topology. -/
abbrev PrimeFaceCoefficients := Finset Nat.Primes → ℂ

/-- The product of the literal Dirichlet weights of the vertices. -/
def primeFaceWeight (s : ℂ) (A : Finset Nat.Primes) : ℂ :=
  ∏ p ∈ A, ((p : ℕ) : ℂ) ^ (-s)

theorem primeFaceWeight_ne_zero (s : ℂ) (A : Finset Nat.Primes) :
    primeFaceWeight s A ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p _
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr p.property.ne_zero))

/-- Coordinate multiplication by nonzero weights needs no uniform bound in the product topology. -/
def primeFaceGauge (s : ℂ) : PrimeFaceCoefficients ≃ₜ PrimeFaceCoefficients :=
  Homeomorph.piCongrRight fun A =>
    Homeomorph.mulLeft₀ (primeFaceWeight s A) (primeFaceWeight_ne_zero s A)

@[simp] theorem primeFaceGauge_apply (s : ℂ) (c : PrimeFaceCoefficients)
    (A : Finset Nat.Primes) :
    primeFaceGauge s c A = primeFaceWeight s A * c A := rfl

@[simp] theorem primeFaceGauge_apply_eq_zero_iff (s : ℂ) (c : PrimeFaceCoefficients)
    (A : Finset Nat.Primes) : primeFaceGauge s c A = 0 ↔ c A = 0 := by
  rw [primeFaceGauge_apply, mul_eq_zero]
  exact or_iff_right (primeFaceWeight_ne_zero s A)

/-- The coefficient contributed by deleting the extra prime, oriented by natural prime order. -/
def primeFaceBoundaryTerm (s : ℂ) (c : PrimeFaceCoefficients)
    (A : Finset Nat.Primes) (p : Nat.Primes) : ℂ :=
  if p ∈ A then 0 else
    (-1 : ℂ) ^ (A.filter (fun q : Nat.Primes => (q : ℕ) < (p : ℕ))).card *
      ((p : ℕ) : ℂ) ^ (-s) * c (insert p A)

/-- Every output row is unconditionally summable; no iterated-boundary condition is imposed. -/
def PrimeFaceRowsSummable (s : ℂ) (c : PrimeFaceCoefficients) : Prop :=
  ∀ A, Summable (primeFaceBoundaryTerm s c A)

/-- The boundary is interpreted analytically on `PrimeFaceRowsSummable`; elsewhere `tsum` is totalized. -/
def primeFaceBoundary (s : ℂ) (c : PrimeFaceCoefficients) : PrimeFaceCoefficients :=
  fun A => ∑' p, primeFaceBoundaryTerm s c A p

theorem primeFaceBoundaryTerm_gauge (s : ℂ) (c : PrimeFaceCoefficients)
    (A : Finset Nat.Primes) (p : Nat.Primes) :
    primeFaceBoundaryTerm 0 (primeFaceGauge s c) A p =
      primeFaceWeight s A * primeFaceBoundaryTerm s c A p := by
  by_cases hp : p ∈ A
  · simp only [primeFaceBoundaryTerm, if_pos hp, mul_zero]
  · simp only [primeFaceBoundaryTerm, if_neg hp, neg_zero, Complex.cpow_zero, mul_one,
      primeFaceGauge_apply, primeFaceWeight, Finset.prod_insert hp]
    ac_rfl

theorem primeFaceRowsSummable_gauge_iff (s : ℂ) (c : PrimeFaceCoefficients) :
    PrimeFaceRowsSummable 0 (primeFaceGauge s c) ↔ PrimeFaceRowsSummable s c := by
  unfold PrimeFaceRowsSummable
  apply forall_congr'
  intro A
  change Summable (fun p => primeFaceBoundaryTerm 0 (primeFaceGauge s c) A p) ↔ _
  simp_rw [primeFaceBoundaryTerm_gauge]
  exact summable_mul_left_iff (primeFaceWeight_ne_zero s A)

theorem primeFaceBoundary_gauge (s : ℂ) (c : PrimeFaceCoefficients) :
    primeFaceBoundary 0 (primeFaceGauge s c) = primeFaceGauge s (primeFaceBoundary s c) := by
  funext A
  simp_rw [primeFaceBoundary, primeFaceBoundaryTerm_gauge, primeFaceGauge_apply]
  exact tsum_mul_left

/-- Exact homeomorphism of admitted coefficient domains. -/
def primeFaceRowsHomeomorph (s : ℂ) :
    {c : PrimeFaceCoefficients // PrimeFaceRowsSummable s c} ≃ₜ
      {c : PrimeFaceCoefficients // PrimeFaceRowsSummable 0 c} :=
  (primeFaceGauge s).subtype fun c => (primeFaceRowsSummable_gauge_iff s c).symm

/-- The graph retains both the summability obligation and the actual boundary value. -/
def PrimeFaceBoundaryGraph (s : ℂ) (x : PrimeFaceCoefficients × PrimeFaceCoefficients) : Prop :=
  PrimeFaceRowsSummable s x.1 ∧ primeFaceBoundary s x.1 = x.2

theorem primeFaceBoundaryGraph_gauge_iff (s : ℂ)
    (x : PrimeFaceCoefficients × PrimeFaceCoefficients) :
    PrimeFaceBoundaryGraph 0 ((primeFaceGauge s).prodCongr (primeFaceGauge s) x) ↔
      PrimeFaceBoundaryGraph s x := by
  change (PrimeFaceRowsSummable 0 (primeFaceGauge s x.1) ∧
    primeFaceBoundary 0 (primeFaceGauge s x.1) = primeFaceGauge s x.2) ↔ _
  rw [primeFaceRowsSummable_gauge_iff, primeFaceBoundary_gauge,
    (primeFaceGauge s).injective.eq_iff]
  rfl

def primeFaceBoundaryGraphHomeomorph (s : ℂ) :
    {x // PrimeFaceBoundaryGraph s x} ≃ₜ {x // PrimeFaceBoundaryGraph 0 x} :=
  ((primeFaceGauge s).prodCongr (primeFaceGauge s)).subtype
    fun x => (primeFaceBoundaryGraph_gauge_iff s x).symm

/-- Any two parameter fibres have explicitly homeomorphic boundary graphs. -/
def primeFaceBoundaryGraphParameterHomeomorph (s t : ℂ) :
    {x // PrimeFaceBoundaryGraph s x} ≃ₜ {x // PrimeFaceBoundaryGraph t x} :=
  (primeFaceBoundaryGraphHomeomorph s).trans (primeFaceBoundaryGraphHomeomorph t).symm

@[simp] theorem primeFaceGauge_symm_apply (s : ℂ) (c : PrimeFaceCoefficients)
    (A : Finset Nat.Primes) :
    (primeFaceGauge s).symm c A = (primeFaceWeight s A)⁻¹ * c A := rfl

theorem continuous_primeFaceWeight (A : Finset Nat.Primes) :
    Continuous (fun s : ℂ => primeFaceWeight s A) := by
  apply continuous_finsetProd
  intro p _
  exact continuous_id.neg.const_cpow (Or.inl (Nat.cast_ne_zero.mpr p.property.ne_zero))

theorem continuous_primeFaceGauge :
    Continuous (fun x : ℂ × PrimeFaceCoefficients => primeFaceGauge x.1 x.2) := by
  apply continuous_pi
  intro A
  exact ((continuous_primeFaceWeight A).comp continuous_fst).mul
    ((continuous_apply A).comp continuous_snd)

theorem continuous_primeFaceGauge_symm :
    Continuous (fun x : ℂ × PrimeFaceCoefficients => (primeFaceGauge x.1).symm x.2) := by
  apply continuous_pi
  intro A
  exact (((continuous_primeFaceWeight A).comp continuous_fst).inv₀
    (fun x => primeFaceWeight_ne_zero x.1 A)).mul
      ((continuous_apply A).comp continuous_snd)

/-- Simultaneously change input and output coordinates, preserving the parameter. -/
def primeFaceGraphTotalGauge :
    (ℂ × (PrimeFaceCoefficients × PrimeFaceCoefficients)) ≃ₜ
      (ℂ × (PrimeFaceCoefficients × PrimeFaceCoefficients)) where
  toFun x := (x.1, primeFaceGauge x.1 x.2.1, primeFaceGauge x.1 x.2.2)
  invFun x := (x.1, (primeFaceGauge x.1).symm x.2.1, (primeFaceGauge x.1).symm x.2.2)
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := by
    apply Continuous.prodMk continuous_fst
    apply Continuous.prodMk
    · apply continuous_pi
      intro A
      change Continuous (fun x : ℂ × (PrimeFaceCoefficients × PrimeFaceCoefficients) =>
        primeFaceWeight x.1 A * x.2.1 A)
      exact ((continuous_primeFaceWeight A).comp continuous_fst).mul
        ((continuous_apply A).comp continuous_snd.fst)
    · apply continuous_pi
      intro A
      change Continuous (fun x : ℂ × (PrimeFaceCoefficients × PrimeFaceCoefficients) =>
        primeFaceWeight x.1 A * x.2.2 A)
      exact ((continuous_primeFaceWeight A).comp continuous_fst).mul
        ((continuous_apply A).comp continuous_snd.snd)
  continuous_invFun := by
    apply Continuous.prodMk continuous_fst
    apply Continuous.prodMk
    · apply continuous_pi
      intro A
      change Continuous (fun x : ℂ × (PrimeFaceCoefficients × PrimeFaceCoefficients) =>
        (primeFaceWeight x.1 A)⁻¹ * x.2.1 A)
      exact (((continuous_primeFaceWeight A).comp continuous_fst).inv₀
        (fun x => primeFaceWeight_ne_zero x.1 A)).mul
          ((continuous_apply A).comp continuous_snd.fst)
    · apply continuous_pi
      intro A
      change Continuous (fun x : ℂ × (PrimeFaceCoefficients × PrimeFaceCoefficients) =>
        (primeFaceWeight x.1 A)⁻¹ * x.2.2 A)
      exact (((continuous_primeFaceWeight A).comp continuous_fst).inv₀
        (fun x => primeFaceWeight_ne_zero x.1 A)).mul
          ((continuous_apply A).comp continuous_snd.snd)

/-- The full graph family is homeomorphic over the parameter to the constant unweighted family. -/
def primeFaceBoundaryGraphTrivialization :
    {x : ℂ × (PrimeFaceCoefficients × PrimeFaceCoefficients) //
      PrimeFaceBoundaryGraph x.1 x.2} ≃ₜ
    {x : ℂ × (PrimeFaceCoefficients × PrimeFaceCoefficients) //
      PrimeFaceBoundaryGraph 0 x.2} :=
  primeFaceGraphTotalGauge.subtype
    fun x => (primeFaceBoundaryGraph_gauge_iff x.1 x.2).symm

end RHTower
