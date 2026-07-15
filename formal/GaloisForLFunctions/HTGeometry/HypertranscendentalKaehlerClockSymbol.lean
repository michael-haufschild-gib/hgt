import GaloisForLFunctions.HTGeometry.HypertranscendentalClockBoundary
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# The filtered Kähler clock and its principal symbol

The Kähler clock of a hypertranscendental jet tower is the free module on the countable
covectors `d(j_n)`.  On coefficient packets the Lie derivative has two terms: differentiation
of the coefficient in the same layer and the forward shift to the next layer.  The first term is
lower order, so the induced map between consecutive associated-graded lines is exactly the
identity on the coefficient field.

This file constructs that filtered operator, its one-dimensional graded quotients, and the
principal-symbol isomorphism.  The construction is algebraic and does not interpret the
derivation as a flow.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The first `N` clock covectors, represented by finitely supported coefficient packets. -/
def kaehlerClockFiltration (K : Type*) [Field K] (N : ℕ) :
    Submodule K (ℕ →₀ K) :=
  Finsupp.supported K K (Set.Iio N)

theorem kaehlerClockFiltration_mono (K : Type*) [Field K] {M N : ℕ} (hMN : M ≤ N) :
    kaehlerClockFiltration K M ≤ kaehlerClockFiltration K N :=
  Finsupp.supported_mono (Set.Iio_subset_Iio hMN)

/-- The coefficient part of the Lie derivative on a free clock packet. -/
def kaehlerClockCoefficientDeriv
    {K : Type*} [Field K] (δ : K →+ K) : (ℕ →₀ K) →+ (ℕ →₀ K) :=
  Finsupp.mapRange.addMonoidHom δ

/-- The filtered Lie derivative `a_n d(j_n) ↦ δ(a_n)d(j_n) + a_n d(j_(n+1))`. -/
def kaehlerClockLie
    {K : Type*} [Field K] (δ : K →+ K) : (ℕ →₀ K) →+ (ℕ →₀ K) where
  toFun a := kaehlerClockCoefficientDeriv δ a + tateClockIndForward a
  map_zero' := by simp [kaehlerClockCoefficientDeriv]
  map_add' a b := by
    simp only [map_add]
    abel

@[simp] theorem kaehlerClockLie_apply_zero
    {K : Type*} [Field K] (δ : K →+ K) (a : ℕ →₀ K) :
    kaehlerClockLie δ a 0 = δ (a 0) := by
  simp [kaehlerClockLie, kaehlerClockCoefficientDeriv]

@[simp] theorem kaehlerClockLie_apply_succ
    {K : Type*} [Field K] (δ : K →+ K) (a : ℕ →₀ K) (n : ℕ) :
    kaehlerClockLie δ a (n + 1) = δ (a (n + 1)) + a n := by
  simp [kaehlerClockLie, kaehlerClockCoefficientDeriv]

/-- The Lie derivative raises the clock filtration by at most one. -/
theorem kaehlerClockLie_mem_succ
    {K : Type*} [Field K] (δ : K →+ K) {N : ℕ} {a : ℕ →₀ K}
    (ha : a ∈ kaehlerClockFiltration K N) :
    kaehlerClockLie δ a ∈ kaehlerClockFiltration K (N + 1) := by
  rw [kaehlerClockFiltration, Finsupp.mem_supported'] at ha ⊢
  intro i hi
  cases i with
  | zero =>
      have hN : N ≤ 0 := by simpa using hi
      have ha0 : a 0 = 0 := ha 0 (by omega)
      simp [ha0]
  | succ i =>
      have hNi : N ≤ i := by omega
      have hai : a i = 0 := ha i (by omega)
      have hais : a (i + 1) = 0 := ha (i + 1) (by omega)
      simp [hai, hais]

/-- The `N`-th coefficient on the first `N+1` clock layers. -/
def kaehlerClockTopCoordinate (K : Type*) [Field K] (N : ℕ) :
    kaehlerClockFiltration K (N + 1) →ₗ[K] K :=
  (Finsupp.lapply N).comp (kaehlerClockFiltration K (N + 1)).subtype

/-- The earlier filtration, regarded inside the next finite clock cut. -/
def kaehlerClockPreviousFiltration (K : Type*) [Field K] (N : ℕ) :
    Submodule K (kaehlerClockFiltration K (N + 1)) :=
  (kaehlerClockFiltration K N).comap (kaehlerClockFiltration K (N + 1)).subtype

theorem kaehlerClockPreviousFiltration_eq_ker_topCoordinate
    (K : Type*) [Field K] (N : ℕ) :
    kaehlerClockPreviousFiltration K N = LinearMap.ker (kaehlerClockTopCoordinate K N) := by
  ext a
  rw [LinearMap.mem_ker]
  constructor
  · intro ha
    rw [kaehlerClockPreviousFiltration] at ha
    exact (Finsupp.mem_supported' K a.1).mp ha N (by simp)
  · intro ha
    rw [kaehlerClockPreviousFiltration]
    apply (Finsupp.mem_supported' K a.1).mpr
    intro i hi
    have hai : a.1 i = 0 := by
      have hle : N ≤ i := by simpa using hi
      by_cases hEq : i = N
      · subst i
        exact ha
      · have hNlt : N < i := lt_of_le_of_ne hle (Ne.symm hEq)
        exact (Finsupp.mem_supported' K a.1).mp a.2 i (by omega)
    exact hai

/-- The `N`-th associated-graded clock line. -/
abbrev KaehlerClockGradedLine (K : Type*) [Field K] (N : ℕ) :=
  kaehlerClockFiltration K (N + 1) ⧸ kaehlerClockPreviousFiltration K N

/-- Coordinate on the `N`-th associated-graded line. -/
def kaehlerClockGradedCoordinate (K : Type*) [Field K] (N : ℕ) :
    KaehlerClockGradedLine K N →ₗ[K] K :=
  (kaehlerClockPreviousFiltration K N).liftQ
    (kaehlerClockTopCoordinate K N)
    (by rw [kaehlerClockPreviousFiltration_eq_ker_topCoordinate])

theorem kaehlerClockGradedCoordinate_bijective
    (K : Type*) [Field K] (N : ℕ) :
    Function.Bijective (kaehlerClockGradedCoordinate K N) := by
  constructor
  · intro a b hab
    apply Submodule.Quotient.eq
    refine (kaehlerClockPreviousFiltration_eq_ker_topCoordinate K N).trans_le ?_
    rw [LinearMap.mem_ker]
    exact sub_eq_zero.mpr hab
  · intro c
    let e : kaehlerClockFiltration K (N + 1) :=
      ⟨Finsupp.single N c, Finsupp.single_mem_supported K c (by simp)⟩
    refine ⟨Submodule.Quotient.mk e, ?_⟩
    simp [kaehlerClockGradedCoordinate, kaehlerClockTopCoordinate, e]

/-- Every associated-graded Kähler clock layer is canonically one-dimensional. -/
noncomputable def kaehlerClockGradedCoordinateEquiv
    (K : Type*) [Field K] (N : ℕ) :
    KaehlerClockGradedLine K N ≃ₗ[K] K :=
  LinearEquiv.ofBijective (kaehlerClockGradedCoordinate K N)
    (kaehlerClockGradedCoordinate_bijective K N)

/-- The degree-one principal symbol of the filtered Kähler Lie derivative. -/
noncomputable def kaehlerClockPrincipalSymbol
    (K : Type*) [Field K] (N : ℕ) :
    KaehlerClockGradedLine K N →ₗ[K] KaehlerClockGradedLine K (N + 1) :=
  (kaehlerClockGradedCoordinateEquiv K (N + 1)).symm.toLinearMap.comp
    (kaehlerClockGradedCoordinateEquiv K N).toLinearMap

theorem kaehlerClockPrincipalSymbol_coordinate
    (K : Type*) [Field K] (N : ℕ) (a : KaehlerClockGradedLine K N) :
    kaehlerClockGradedCoordinateEquiv K (N + 1)
        (kaehlerClockPrincipalSymbol K N a) =
      kaehlerClockGradedCoordinateEquiv K N a := by
  simp [kaehlerClockPrincipalSymbol]

/-- The principal symbol is a canonical linear isomorphism between adjacent clock lines. -/
noncomputable def kaehlerClockPrincipalSymbolEquiv
    (K : Type*) [Field K] (N : ℕ) :
    KaehlerClockGradedLine K N ≃ₗ[K] KaehlerClockGradedLine K (N + 1) :=
  (kaehlerClockGradedCoordinateEquiv K N).trans
    (kaehlerClockGradedCoordinateEquiv K (N + 1)).symm

/-- The top coefficient of the Lie derivative is the preceding top coefficient; the coefficient
derivative is a lower-order term. -/
theorem kaehlerClockLie_topCoordinate
    {K : Type*} [Field K] (δ : K →+ K) (N : ℕ)
    (a : kaehlerClockFiltration K (N + 1)) :
    kaehlerClockLie δ a.1 (N + 1) = a.1 N := by
  rw [kaehlerClockLie_apply_succ]
  have hzero : a.1 (N + 1) = 0 :=
    (Finsupp.mem_supported' K a.1).mp a.2 (N + 1) (by simp)
  simp [hzero]

/-- The coordinate-defined principal symbol is exactly the map induced by the filtered Lie
derivative on representatives. -/
theorem kaehlerClockPrincipalSymbol_mk_eq_lie
    {K : Type*} [Field K] (δ : K →+ K) (N : ℕ)
    (a : kaehlerClockFiltration K (N + 1)) :
    kaehlerClockPrincipalSymbol K N (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk
        (⟨kaehlerClockLie δ a.1, kaehlerClockLie_mem_succ δ a.2⟩ :
          kaehlerClockFiltration K (N + 2)) := by
  apply (kaehlerClockGradedCoordinateEquiv K (N + 1)).injective
  rw [kaehlerClockPrincipalSymbol_coordinate]
  change a.1 N = kaehlerClockLie δ a.1 (N + 1)
  exact (kaehlerClockLie_topCoordinate δ N a).symm

end

end GaloisForLFunctions.HTGeometry
