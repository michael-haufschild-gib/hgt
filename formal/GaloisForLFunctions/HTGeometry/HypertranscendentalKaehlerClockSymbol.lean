import GaloisForLFunctions.HTGeometry.HypertranscendentalClockBoundary
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Smooth.Field

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

open scoped TensorProduct

/-- The first `N` clock covectors, represented by finitely supported coefficient packets. -/
def kaehlerClockFiltration (K : Type*) [Ring K] (N : ℕ) :
    Submodule K (ℕ →₀ K) :=
  Finsupp.supported K K (Set.Iio N)

theorem kaehlerClockFiltration_mono (K : Type*) [Ring K] {M N : ℕ} (hMN : M ≤ N) :
    kaehlerClockFiltration K M ≤ kaehlerClockFiltration K N :=
  Finsupp.supported_mono (Set.Iio_subset_Iio hMN)

/-- The coefficient part of the Lie derivative on a free clock packet. -/
def kaehlerClockCoefficientDeriv
    {K : Type*} [Ring K] (δ : K →+ K) : (ℕ →₀ K) →+ (ℕ →₀ K) :=
  Finsupp.mapRange.addMonoidHom δ

/-- The forward clock embedding, bundled as an additive map. -/
def kaehlerClockForward
    {K : Type*} [Ring K] : (ℕ →₀ K) →+ (ℕ →₀ K) :=
  Finsupp.embDomain.addMonoidHom tateClockSucc

/-- The filtered Lie derivative `a_n d(j_n) ↦ δ(a_n)d(j_n) + a_n d(j_(n+1))`. -/
def kaehlerClockLie
    {K : Type*} [Ring K] (δ : K →+ K) : (ℕ →₀ K) →+ (ℕ →₀ K) where
  toFun a := kaehlerClockCoefficientDeriv δ a + kaehlerClockForward a
  map_zero' := by simp
  map_add' a b := by simp only [map_add, add_add_add_comm]

@[simp] theorem kaehlerClockLie_apply_zero
    {K : Type*} [Ring K] (δ : K →+ K) (a : ℕ →₀ K) :
    kaehlerClockLie δ a 0 = δ (a 0) := by
  change δ (a 0) + tateClockIndForward a 0 = δ (a 0)
  simp

@[simp] theorem kaehlerClockLie_apply_succ
    {K : Type*} [Ring K] (δ : K →+ K) (a : ℕ →₀ K) (n : ℕ) :
    kaehlerClockLie δ a (n + 1) = δ (a (n + 1)) + a n := by
  change δ (a (n + 1)) + tateClockIndForward a (n + 1) = δ (a (n + 1)) + a n
  simp

@[simp] theorem kaehlerClockLie_single
    {K : Type*} [Ring K] (δ : K →+ K) (n : ℕ) (a : K) :
    kaehlerClockLie δ (Finsupp.single n a) =
      Finsupp.single n (δ a) + Finsupp.single (n + 1) a := by
  classical
  ext i
  cases i with
  | zero =>
      cases n with
      | zero => simp
      | succ n => simp
  | succ i =>
      simp only [kaehlerClockLie_apply_succ, Finsupp.single_apply]
      split_ifs <;> simp_all

/-- The Lie derivative raises the clock filtration by at most one. -/
theorem kaehlerClockLie_mem_succ
    {K : Type*} [Ring K] (δ : K →+ K) {N : ℕ} {a : ℕ →₀ K}
    (ha : a ∈ kaehlerClockFiltration K N) :
    kaehlerClockLie δ a ∈ kaehlerClockFiltration K (N + 1) := by
  rw [kaehlerClockFiltration, Finsupp.mem_supported'] at ha ⊢
  intro i hi
  cases i with
  | zero =>
      simp at hi
  | succ i =>
      simp only [Set.mem_Iio, not_lt, Nat.succ_le_succ_iff] at hi
      have hai : a i = 0 := ha i (by simpa [Set.mem_Iio, not_lt] using hi)
      have hais : a (i + 1) = 0 := ha (i + 1) (by
        simp only [Set.mem_Iio, not_lt]
        omega)
      simp [hai, hais]

/-- The `N`-th coefficient on the first `N+1` clock layers. -/
def kaehlerClockTopCoordinate (K : Type*) [Ring K] (N : ℕ) :
    kaehlerClockFiltration K (N + 1) →ₗ[K] K :=
  (Finsupp.lapply N).comp (kaehlerClockFiltration K (N + 1)).subtype

/-- The earlier filtration, regarded inside the next finite clock cut. -/
def kaehlerClockPreviousFiltration (K : Type*) [Ring K] (N : ℕ) :
    Submodule K (kaehlerClockFiltration K (N + 1)) :=
  (kaehlerClockFiltration K N).comap (kaehlerClockFiltration K (N + 1)).subtype

theorem kaehlerClockPreviousFiltration_eq_ker_topCoordinate
    (K : Type*) [Ring K] (N : ℕ) :
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
    simp only [Set.mem_Iio, not_lt] at hi
    have hai : a.1 i = 0 := by
      by_cases hEq : i = N
      · subst i
        exact ha
      · apply (Finsupp.mem_supported' K a.1).mp a.2 i
        simp only [Set.mem_Iio, not_lt]
        omega
    exact hai

theorem kaehlerClockTopCoordinate_surjective
    (K : Type*) [Ring K] (N : ℕ) :
    Function.Surjective (kaehlerClockTopCoordinate K N) := by
  intro c
  refine ⟨⟨Finsupp.single N c, ?_⟩, ?_⟩
  · rw [kaehlerClockFiltration, Finsupp.mem_supported']
    intro i hi
    simp only [Set.mem_Iio, not_lt] at hi
    have hne : N ≠ i := by omega
    simp [hne]
  · simp [kaehlerClockTopCoordinate]

/-- The `N`-th homogeneous Kähler clock line `K e_N`. -/
def kaehlerClockGradedLine (K : Type*) [Ring K] (N : ℕ) :
    Submodule K (ℕ →₀ K) :=
  LinearMap.range (Finsupp.lsingle N : K →ₗ[K] ℕ →₀ K)

/-- The `N`-th line lies in the first `N+1` clock covectors. -/
theorem kaehlerClockGradedLine_le_filtration
    (K : Type*) [Ring K] (N : ℕ) :
    kaehlerClockGradedLine K N ≤ kaehlerClockFiltration K (N + 1) := by
  rintro a ⟨c, rfl⟩
  exact Finsupp.single_mem_supported K c (by simp)

/-- Coordinate on the `N`-th homogeneous clock line. -/
def kaehlerClockGradedCoordinate (K : Type*) [Ring K] (N : ℕ) :
    kaehlerClockGradedLine K N →ₗ[K] K :=
  (Finsupp.lapply N).comp (kaehlerClockGradedLine K N).subtype

/-- Every homogeneous Kähler clock layer is canonically one-dimensional. -/
noncomputable def kaehlerClockGradedCoordinateEquiv
    (K : Type*) [Ring K] (N : ℕ) :
    kaehlerClockGradedLine K N ≃ₗ[K] K :=
  LinearEquiv.ofBijective (kaehlerClockGradedCoordinate K N) <| by
    constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      rcases ha with ⟨c, rfl⟩
      rcases hb with ⟨d, rfl⟩
      have hcd : c = d := by
        simpa [kaehlerClockGradedCoordinate] using hab
      subst d
      rfl
    · intro c
      refine ⟨⟨Finsupp.single N c, ⟨c, rfl⟩⟩, ?_⟩
      simp [kaehlerClockGradedCoordinate]

/-- The degree-one principal symbol of the filtered Kähler Lie derivative. -/
noncomputable def kaehlerClockPrincipalSymbol
    (K : Type*) [Ring K] (N : ℕ) :
    kaehlerClockGradedLine K N →ₗ[K] kaehlerClockGradedLine K (N + 1) :=
  (kaehlerClockGradedCoordinateEquiv K (N + 1)).symm.toLinearMap.comp
    (kaehlerClockGradedCoordinateEquiv K N).toLinearMap

theorem kaehlerClockPrincipalSymbol_coordinate
    (K : Type*) [Ring K] (N : ℕ) (a : kaehlerClockGradedLine K N) :
    kaehlerClockGradedCoordinateEquiv K (N + 1)
        (kaehlerClockPrincipalSymbol K N a) =
      kaehlerClockGradedCoordinateEquiv K N a := by
  simp [kaehlerClockPrincipalSymbol]

/-- The principal symbol is a canonical linear isomorphism between adjacent clock lines. -/
noncomputable def kaehlerClockPrincipalSymbolEquiv
    (K : Type*) [Ring K] (N : ℕ) :
    kaehlerClockGradedLine K N ≃ₗ[K] kaehlerClockGradedLine K (N + 1) :=
  (kaehlerClockGradedCoordinateEquiv K N).trans
    (kaehlerClockGradedCoordinateEquiv K (N + 1)).symm

@[simp] theorem kaehlerClockPrincipalSymbolEquiv_apply
    (K : Type*) [Ring K] (N : ℕ) (a : kaehlerClockGradedLine K N) :
    kaehlerClockPrincipalSymbolEquiv K N a = kaehlerClockPrincipalSymbol K N a :=
  rfl

/-- The top coefficient of the Lie derivative is the preceding top coefficient; the coefficient
derivative is a lower-order term. -/
theorem kaehlerClockLie_topCoordinate
    {K : Type*} [Ring K] (δ : K →+ K) (N : ℕ)
    (a : kaehlerClockFiltration K (N + 1)) :
    kaehlerClockLie δ a.1 (N + 1) = a.1 N := by
  rw [kaehlerClockLie_apply_succ]
  have hzero : a.1 (N + 1) = 0 :=
    (Finsupp.mem_supported' K a.1).mp a.2 (N + 1) (by simp)
  simp [hzero]

/-- Projection of a clock packet to its `N`-th homogeneous line. -/
def kaehlerClockGradedProjection (K : Type*) [Ring K] (N : ℕ) :
    (ℕ →₀ K) →ₗ[K] kaehlerClockGradedLine K N where
  toFun a := ⟨Finsupp.single N (a N), ⟨a N, rfl⟩⟩
  map_add' a b := by ext i; by_cases hi : i = N <;> simp [hi]
  map_smul' c a := by ext i; by_cases hi : i = N <;> simp [hi]

/-- The coordinate-defined principal symbol is exactly the next-layer projection of the
filtered Lie derivative. -/
theorem kaehlerClockPrincipalSymbol_eq_lie_projection
    {K : Type*} [Ring K] (δ : K →+ K) (N : ℕ)
    (a : kaehlerClockGradedLine K N) :
    kaehlerClockPrincipalSymbol K N a =
      kaehlerClockGradedProjection K (N + 1) (kaehlerClockLie δ a.1) := by
  apply (kaehlerClockGradedCoordinateEquiv K (N + 1)).injective
  rw [kaehlerClockPrincipalSymbol_coordinate]
  have hzero : a.1 (N + 1) = 0 := by
    rcases a.2 with ⟨c, hc⟩
    rw [← hc]
    simp
  simp [kaehlerClockGradedCoordinateEquiv, kaehlerClockGradedCoordinate,
    kaehlerClockGradedProjection, kaehlerClockLie_apply_succ, hzero]

/-! ### The universal Kähler Lie derivative -/

/-- Presentation-level formula `a db ↦ δ(a) db + a d(δ b)`. -/
noncomputable def kaehlerLiePresentation
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (δ : Derivation R S S) : (S →₀ S) →+ Ω[S⁄R] :=
  Finsupp.liftAddHom fun b ↦
    { toFun := fun a ↦
        δ a • KaehlerDifferential.D R S b +
          a • KaehlerDifferential.D R S (δ b)
      map_zero' := by simp
      map_add' := by
        intro x y
        simp [add_smul]
        module }

@[simp] theorem kaehlerLiePresentation_single
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (δ : Derivation R S S) (b a : S) :
    kaehlerLiePresentation δ (Finsupp.single b a) =
      δ a • KaehlerDifferential.D R S b +
        a • KaehlerDifferential.D R S (δ b) := by
  simp [kaehlerLiePresentation]

/-- The presentation operator obeys the connection Leibniz rule with respect to coefficients. -/
theorem kaehlerLiePresentation_smul
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (δ : Derivation R S S) (c : S) (f : S →₀ S) :
    kaehlerLiePresentation δ (c • f) =
      δ c • Finsupp.linearCombination S (KaehlerDifferential.D R S) f +
        c • kaehlerLiePresentation δ f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [smul_add, map_add, map_add, hf, hg, map_add, smul_add]
      module
  | single b a =>
      simp [Derivation.leibniz, smul_add, add_smul, smul_smul]
      module

/-- The presentation formula kills every Kähler relation, so it descends to universal
differentials. -/
theorem kaehlerLiePresentation_eq_zero_of_mem_kerTotal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (δ : Derivation R S S) {f : S →₀ S}
    (hf : f ∈ KaehlerDifferential.kerTotal R S) :
    kaehlerLiePresentation δ f = 0 := by
  rw [KaehlerDifferential.kerTotal] at hf
  suffices h :
      Finsupp.linearCombination S (KaehlerDifferential.D R S) f = 0 ∧
        kaehlerLiePresentation δ f = 0 by
    exact h.2
  induction hf using Submodule.span_induction with
  | mem g hg =>
      rcases hg with (hg | hg) | hg
      · obtain ⟨⟨a, b⟩, rfl⟩ := hg
        constructor <;> simp [kaehlerLiePresentation_single]
      · obtain ⟨⟨a, b⟩, rfl⟩ := hg
        constructor
        · simp [Derivation.leibniz]
        · simp [kaehlerLiePresentation_single, Derivation.leibniz,
            smul_add]
          module
      · obtain ⟨r, rfl⟩ := hg
        constructor <;> simp [kaehlerLiePresentation_single]
  | zero => simp
  | add f g _ _ hf hg =>
      constructor
      · rw [map_add, hf.1, hg.1, add_zero]
      · rw [map_add, hf.2, hg.2, add_zero]
  | smul c f _ hf =>
      constructor
      · rw [map_smul, hf.1, smul_zero]
      · rw [kaehlerLiePresentation_smul, hf.1, hf.2, smul_zero,
          zero_add]
        simp

/-- The presentation formula descended to the quotient presentation of universal differentials. -/
noncomputable def kaehlerLieQuotient
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (δ : Derivation R S S) :
    ((S →₀ S) ⧸ KaehlerDifferential.kerTotal R S) →+ Ω[S⁄R] :=
  QuotientAddGroup.lift (KaehlerDifferential.kerTotal R S).toAddSubgroup
    (kaehlerLiePresentation δ) fun f hf ↦ by
      exact kaehlerLiePresentation_eq_zero_of_mem_kerTotal δ hf

/-- The universal Kähler Lie derivative attached to an `R`-derivation of `S`. -/
noncomputable def kaehlerLieDifferential
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (δ : Derivation R S S) : Ω[S⁄R] →+ Ω[S⁄R] where
  toFun w := kaehlerLieQuotient δ
    ((KaehlerDifferential.quotKerTotalEquiv R S).symm w)
  map_zero' := by simp
  map_add' a b := by simp

@[simp] theorem kaehlerLieDifferential_D
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (δ : Derivation R S S) (b : S) :
    kaehlerLieDifferential δ (KaehlerDifferential.D R S b) =
      KaehlerDifferential.D R S (δ b) := by
  have h := Derivation.congr_fun
    (KaehlerDifferential.quotKerTotalEquiv_symm_comp_D R S) b
  change (KaehlerDifferential.quotKerTotalEquiv R S).symm
      (KaehlerDifferential.D R S b) =
    (KaehlerDifferential.kerTotal R S).mkQ (Finsupp.single b 1) at h
  change kaehlerLieQuotient δ
      ((KaehlerDifferential.quotKerTotalEquiv R S).symm
        (KaehlerDifferential.D R S b)) = _
  rw [h]
  change kaehlerLiePresentation δ (Finsupp.single b 1) = _
  simp [kaehlerLiePresentation]

/-- Exact Kähler Lie formula on every elementary one-form. -/
theorem kaehlerLieDifferential_smul_D
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (δ : Derivation R S S) (a b : S) :
    kaehlerLieDifferential δ
        (a • KaehlerDifferential.D R S b) =
      δ a • KaehlerDifferential.D R S b +
        a • KaehlerDifferential.D R S (δ b) := by
  have h := Derivation.congr_fun
    (KaehlerDifferential.quotKerTotalEquiv_symm_comp_D R S) b
  change (KaehlerDifferential.quotKerTotalEquiv R S).symm
      (KaehlerDifferential.D R S b) =
    (KaehlerDifferential.kerTotal R S).mkQ (Finsupp.single b 1) at h
  change kaehlerLieQuotient δ
      ((KaehlerDifferential.quotKerTotalEquiv R S).symm
        (a • KaehlerDifferential.D R S b)) = _
  rw [map_smul, h]
  change kaehlerLieQuotient δ
      ((KaehlerDifferential.kerTotal R S).mkQ
        (a • Finsupp.single b 1)) = _
  change kaehlerLiePresentation δ
      (a • Finsupp.single b 1) = _
  simp [kaehlerLiePresentation]

/-- The Kähler Lie derivative is a connection for the coefficient action. -/
theorem kaehlerLieDifferential_smul
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (δ : Derivation R S S) (a : S) (w : Ω[S⁄R]) :
    kaehlerLieDifferential δ (a • w) =
      δ a • w + a • kaehlerLieDifferential δ w := by
  let q := (KaehlerDifferential.quotKerTotalEquiv R S).symm w
  obtain ⟨f, hf⟩ :=
    (KaehlerDifferential.kerTotal R S).mkQ_surjective q
  have hw : w = (KaehlerDifferential.quotKerTotalEquiv R S)
      ((KaehlerDifferential.kerTotal R S).mkQ f) := by
    calc
      w = (KaehlerDifferential.quotKerTotalEquiv R S) q :=
        (KaehlerDifferential.quotKerTotalEquiv R S).apply_symm_apply w |>.symm
      _ = (KaehlerDifferential.quotKerTotalEquiv R S)
          ((KaehlerDifferential.kerTotal R S).mkQ f) := by rw [hf]
  rw [hw]
  let e := KaehlerDifferential.quotKerTotalEquiv R S
  let mk := (KaehlerDifferential.kerTotal R S).mkQ
  have hlinear : e (mk f) =
      Finsupp.linearCombination S (KaehlerDifferential.D R S) f := rfl
  have hLie : kaehlerLieDifferential δ (e (mk f)) =
      kaehlerLiePresentation δ f := by
    change kaehlerLieQuotient δ (e.symm (e (mk f))) = _
    rw [e.symm_apply_apply]
    rfl
  calc
    kaehlerLieDifferential δ (a • e (mk f)) =
        kaehlerLieDifferential δ (e (a • mk f)) := by
          congr 1
          exact (e.map_smul a (mk f)).symm
    _ = kaehlerLieQuotient δ (a • mk f) := by
          change kaehlerLieQuotient δ (e.symm (e (a • mk f))) = _
          rw [e.symm_apply_apply]
    _ = kaehlerLiePresentation δ (a • f) := by
          rw [← mk.map_smul a f]
          rfl
    _ = δ a • Finsupp.linearCombination S (KaehlerDifferential.D R S) f +
          a • kaehlerLiePresentation δ f :=
        kaehlerLiePresentation_smul δ a f
    _ = δ a • e (mk f) +
          a • kaehlerLieDifferential δ (e (mk f)) := by
          rw [hLie, hlinear]

/-! ### Kähler connections for derivations preserving the base algebra -/

/-- Presentation formula for a ring derivation acting as a connection on relative
differentials.  Descent only requires that derivatives of base scalars still have zero relative
differential. -/
noncomputable def kaehlerConnectionPresentation
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (δ : Derivation ℤ S S) : (S →₀ S) →+ Ω[S⁄R] :=
  Finsupp.liftAddHom fun b ↦
    { toFun := fun a ↦
        δ a • KaehlerDifferential.D R S b +
          a • KaehlerDifferential.D R S (δ b)
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [map_add, add_smul]
        module }

@[simp] theorem kaehlerConnectionPresentation_single
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (δ : Derivation ℤ S S) (b a : S) :
    kaehlerConnectionPresentation (R := R) δ (Finsupp.single b a) =
      δ a • KaehlerDifferential.D R S b +
        a • KaehlerDifferential.D R S (δ b) := by
  simp [kaehlerConnectionPresentation]

theorem kaehlerConnectionPresentation_smul
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (δ : Derivation ℤ S S) (c : S) (f : S →₀ S) :
    kaehlerConnectionPresentation (R := R) δ (c • f) =
      δ c • Finsupp.linearCombination S (KaehlerDifferential.D R S) f +
        c • kaehlerConnectionPresentation (R := R) δ f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [smul_add, map_add, map_add, hf, hg, map_add, smul_add]
      module
  | single b a =>
      simp [Derivation.leibniz, smul_add, add_smul, smul_smul]
      module

theorem kaehlerConnectionPresentation_eq_zero_of_mem_kerTotal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (δ : Derivation ℤ S S)
    (hbase : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    {f : S →₀ S} (hf : f ∈ KaehlerDifferential.kerTotal R S) :
    kaehlerConnectionPresentation (R := R) δ f = 0 := by
  rw [KaehlerDifferential.kerTotal] at hf
  suffices h :
      Finsupp.linearCombination S (KaehlerDifferential.D R S) f = 0 ∧
        kaehlerConnectionPresentation (R := R) δ f = 0 by
    exact h.2
  induction hf using Submodule.span_induction with
  | mem g hg =>
      rcases hg with (hg | hg) | hg
      · obtain ⟨⟨a, b⟩, rfl⟩ := hg
        constructor <;> simp [kaehlerConnectionPresentation_single]
      · obtain ⟨⟨a, b⟩, rfl⟩ := hg
        constructor
        · simp [Derivation.leibniz]
        · simp [kaehlerConnectionPresentation_single, Derivation.leibniz,
            smul_add]
          module
      · obtain ⟨r, rfl⟩ := hg
        constructor
        · simp
        · simpa [kaehlerConnectionPresentation_single] using hbase r
  | zero => simp
  | add f g _ _ hf hg =>
      constructor
      · rw [map_add, hf.1, hg.1, add_zero]
      · rw [map_add, hf.2, hg.2, add_zero]
  | smul c f _ hf =>
      constructor
      · rw [map_smul, hf.1, smul_zero]
      · rw [kaehlerConnectionPresentation_smul, hf.1, hf.2, smul_zero,
          zero_add]
        simp

noncomputable def kaehlerConnectionQuotient
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (δ : Derivation ℤ S S)
    (hbase : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) :
    ((S →₀ S) ⧸ KaehlerDifferential.kerTotal R S) →+ Ω[S⁄R] :=
  QuotientAddGroup.lift (KaehlerDifferential.kerTotal R S).toAddSubgroup
    (kaehlerConnectionPresentation (R := R) δ) fun _ hf ↦
      kaehlerConnectionPresentation_eq_zero_of_mem_kerTotal δ hbase hf

/-- The canonical connection on relative Kähler differentials induced by a ring derivation
that preserves the base algebra. -/
noncomputable def kaehlerConnectionDifferential
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (δ : Derivation ℤ S S)
    (hbase : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) :
    Ω[S⁄R] →+ Ω[S⁄R] where
  toFun w := kaehlerConnectionQuotient δ hbase
    ((KaehlerDifferential.quotKerTotalEquiv R S).symm w)
  map_zero' := by simp
  map_add' a b := by simp

@[simp] theorem kaehlerConnectionDifferential_D
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (δ : Derivation ℤ S S)
    (hbase : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    (b : S) :
    kaehlerConnectionDifferential δ hbase (KaehlerDifferential.D R S b) =
      KaehlerDifferential.D R S (δ b) := by
  have h := Derivation.congr_fun
    (KaehlerDifferential.quotKerTotalEquiv_symm_comp_D R S) b
  change (KaehlerDifferential.quotKerTotalEquiv R S).symm
      (KaehlerDifferential.D R S b) =
    (KaehlerDifferential.kerTotal R S).mkQ (Finsupp.single b 1) at h
  change kaehlerConnectionQuotient δ hbase
      ((KaehlerDifferential.quotKerTotalEquiv R S).symm
        (KaehlerDifferential.D R S b)) = _
  rw [h]
  change kaehlerConnectionPresentation δ (Finsupp.single b 1) = _
  simp [kaehlerConnectionPresentation]

/-- Connection Leibniz rule for arbitrary relative one-forms. -/
theorem kaehlerConnectionDifferential_smul
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (δ : Derivation ℤ S S)
    (hbase : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    (a : S) (w : Ω[S⁄R]) :
    kaehlerConnectionDifferential δ hbase (a • w) =
      δ a • w + a • kaehlerConnectionDifferential δ hbase w := by
  let q := (KaehlerDifferential.quotKerTotalEquiv R S).symm w
  obtain ⟨f, hf⟩ :=
    (KaehlerDifferential.kerTotal R S).mkQ_surjective q
  have hw : w = (KaehlerDifferential.quotKerTotalEquiv R S)
      ((KaehlerDifferential.kerTotal R S).mkQ f) := by
    calc
      w = (KaehlerDifferential.quotKerTotalEquiv R S) q :=
        (KaehlerDifferential.quotKerTotalEquiv R S).apply_symm_apply w |>.symm
      _ = (KaehlerDifferential.quotKerTotalEquiv R S)
          ((KaehlerDifferential.kerTotal R S).mkQ f) := by rw [hf]
  rw [hw]
  let e := KaehlerDifferential.quotKerTotalEquiv R S
  let mk := (KaehlerDifferential.kerTotal R S).mkQ
  have hlinear : e (mk f) =
      Finsupp.linearCombination S (KaehlerDifferential.D R S) f := rfl
  have hconnection : kaehlerConnectionDifferential δ hbase (e (mk f)) =
      kaehlerConnectionPresentation δ f := by
    change kaehlerConnectionQuotient δ hbase (e.symm (e (mk f))) = _
    rw [e.symm_apply_apply]
    rfl
  calc
    kaehlerConnectionDifferential δ hbase (a • e (mk f)) =
        kaehlerConnectionDifferential δ hbase (e (a • mk f)) := by
          congr 1
          exact (e.map_smul a (mk f)).symm
    _ = kaehlerConnectionQuotient δ hbase (a • mk f) := by
          change kaehlerConnectionQuotient δ hbase (e.symm (e (a • mk f))) = _
          rw [e.symm_apply_apply]
    _ = kaehlerConnectionPresentation δ (a • f) := by
          rw [← mk.map_smul a f]
          rfl
    _ = δ a • Finsupp.linearCombination S (KaehlerDifferential.D R S) f +
          a • kaehlerConnectionPresentation δ f :=
        kaehlerConnectionPresentation_smul δ a f
    _ = δ a • e (mk f) +
          a • kaehlerConnectionDifferential δ hbase (e (mk f)) := by
          rw [hconnection, hlinear]

/-- Changing from absolute to relative Kähler differentials intertwines the two connections
whenever the same ring derivation preserves both base algebras. -/
theorem kaehlerConnectionDifferential_map
    {C F P : Type*} [CommRing C] [CommRing F] [CommRing P]
    [Algebra C F] [Algebra C P] [Algebra F P] [IsScalarTower C F P]
    (δ : Derivation ℤ P P)
    (hC : ∀ c : C, KaehlerDifferential.D C P (δ (algebraMap C P c)) = 0)
    (hF : ∀ a : F, KaehlerDifferential.D F P (δ (algebraMap F P a)) = 0)
    (w : Ω[P⁄C]) :
    KaehlerDifferential.map C F P P
        (kaehlerConnectionDifferential δ hC w) =
      kaehlerConnectionDifferential δ hF
        (KaehlerDifferential.map C F P P w) := by
  let V : Submodule P Ω[P⁄C] :=
    { carrier := {z | KaehlerDifferential.map C F P P
          (kaehlerConnectionDifferential δ hC z) =
        kaehlerConnectionDifferential δ hF
          (KaehlerDifferential.map C F P P z)}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq, map_add]
        rw [hx, hy]
      smul_mem' := by
        intro a z hz
        simp only [Set.mem_setOf_eq, map_smul]
        rw [kaehlerConnectionDifferential_smul,
          kaehlerConnectionDifferential_smul, map_add, map_smul, map_smul,
          hz] }
  have hV : V = ⊤ := by
    apply top_unique
    rw [← KaehlerDifferential.span_range_derivation]
    apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    change KaehlerDifferential.D C P b ∈ V
    change KaehlerDifferential.map C F P P
        (kaehlerConnectionDifferential δ hC
          (KaehlerDifferential.D C P b)) =
      kaehlerConnectionDifferential δ hF
        (KaehlerDifferential.map C F P P
          (KaehlerDifferential.D C P b))
    simp
  have hw : w ∈ V := by rw [hV]; trivial
  exact hw

/-- The base-change summand is invariant under the absolute Kähler connection. -/
theorem kaehlerConnectionDifferential_mem_range_mapBaseChange
    {C F P : Type*} [CommRing C] [CommRing F] [CommRing P]
    [Algebra C F] [Algebra C P] [Algebra F P] [IsScalarTower C F P]
    (δ : Derivation ℤ P P)
    (hC : ∀ c : C, KaehlerDifferential.D C P (δ (algebraMap C P c)) = 0)
    (hF : ∀ a : F, KaehlerDifferential.D F P (δ (algebraMap F P a)) = 0)
    {w : Ω[P⁄C]}
    (hw : w ∈ LinearMap.range (KaehlerDifferential.mapBaseChange C F P)) :
    kaehlerConnectionDifferential δ hC w ∈
      LinearMap.range (KaehlerDifferential.mapBaseChange C F P) := by
  rw [KaehlerDifferential.range_mapBaseChange, LinearMap.mem_ker] at hw ⊢
  rw [kaehlerConnectionDifferential_map δ hC hF, hw, map_zero]

/-! ### Identification with the intrinsic Kähler covectors -/

/-- The universal differentials of algebraically independent generators span the Kähler module
of their rational function field.  Together with the existing coordinate-derivation argument,
this upgrades jet-covector independence to an actual basis theorem. -/
theorem kaehlerD_adjoin_coordinates_span_eq_top
    {I K L : Type*} [DecidableEq I] [Field K] [Field L] [Algebra K L]
    {x : I → L} :
    let P := IntermediateField.adjoin K (Set.range x)
    Submodule.span P (Set.range fun i : I ↦
      KaehlerDifferential.D K P
        (⟨x i, IntermediateField.subset_adjoin K (Set.range x) ⟨i, rfl⟩⟩ : P)) = ⊤ := by
  classical
  dsimp only
  let P := IntermediateField.adjoin K (Set.range x)
  let S : Submodule P Ω[P⁄K] :=
    Submodule.span P (Set.range fun i : I ↦
      KaehlerDifferential.D K P
        (⟨x i, IntermediateField.subset_adjoin K (Set.range x) ⟨i, rfl⟩⟩ : P))
  apply top_unique
  rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨z, rfl⟩
  apply IntermediateField.adjoin_induction K
    (s := Set.range x)
    (p := fun y hy ↦ KaehlerDifferential.D K P (⟨y, hy⟩ : P) ∈ S)
  · rintro y ⟨i, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self i)
  · intro c
    have hc :
        (⟨algebraMap K L c, IntermediateField.algebraMap_mem P c⟩ : P) =
          algebraMap K P c := Subtype.ext (by simp)
    rw [hc]
    simp
  · intro a b ha hb hda hdb
    have hab :
        (⟨a + b, P.add_mem ha hb⟩ : P) = (⟨a, ha⟩ : P) + ⟨b, hb⟩ :=
      Subtype.ext rfl
    rw [hab, map_add]
    exact S.add_mem hda hdb
  · intro a ha hda
    have hainv :
        (⟨a⁻¹, P.inv_mem ha⟩ : P) = (⟨a, ha⟩ : P)⁻¹ := Subtype.ext rfl
    rw [hainv, Derivation.leibniz_inv]
    exact S.smul_mem _ hda
  · intro a b ha hb hda hdb
    have hab :
        (⟨a * b, P.mul_mem ha hb⟩ : P) = (⟨a, ha⟩ : P) * ⟨b, hb⟩ :=
      Subtype.ext rfl
    rw [hab, Derivation.leibniz]
    exact S.add_mem (S.smul_mem _ hdb) (S.smul_mem _ hda)

/-- The universal differentials of algebraically independent rational coordinates form a basis. -/
noncomputable def kaehlerD_adjoin_coordinates_basis
    {I K L : Type*} [DecidableEq I] [Field K] [Field L] [Algebra K L]
    {x : I → L} (hx : AlgebraicIndependent K x) :
    let P := IntermediateField.adjoin K (Set.range x)
    Module.Basis I P Ω[P⁄K] := by
  let P := IntermediateField.adjoin K (Set.range x)
  let dx : I → Ω[P⁄K] := fun i ↦
    KaehlerDifferential.D K P
      (⟨x i, IntermediateField.subset_adjoin K (Set.range x) ⟨i, rfl⟩⟩ : P)
  exact Module.Basis.mk
    (kaehlerD_adjoin_coordinates_linearIndependent hx)
    (by
      rw [kaehlerD_adjoin_coordinates_span_eq_top (x := x)])

@[simp] theorem kaehlerD_adjoin_coordinates_basis_apply
    {I K L : Type*} [DecidableEq I] [Field K] [Field L] [Algebra K L]
    {x : I → L} (hx : AlgebraicIndependent K x) (i : I) :
    (kaehlerD_adjoin_coordinates_basis hx) i =
      KaehlerDifferential.D K (IntermediateField.adjoin K (Set.range x))
        (⟨x i, IntermediateField.subset_adjoin K (Set.range x) ⟨i, rfl⟩⟩ :
          IntermediateField.adjoin K (Set.range x)) := by
  simp only [kaehlerD_adjoin_coordinates_basis, Module.Basis.mk_apply]

/-- For a purely transcendental field interval, the base-change summand in the
Jacobi--Zariski sequence embeds in the absolute Kähler module. -/
theorem kaehlerMapBaseChange_injective_adjoin_of_algebraicIndependent
    {C F E I : Type*} [Field C] [Field F] [Field E]
    [Algebra C F] [Algebra C E] [Algebra F E] [IsScalarTower C F E]
    {x : I → E} (hx : AlgebraicIndependent F x) :
    Function.Injective
      (KaehlerDifferential.mapBaseChange C F
        (IntermediateField.adjoin F (Set.range x))) := by
  let P := IntermediateField.adjoin F (Set.range x)
  letI : Algebra.FormallySmooth F P :=
    Algebra.FormallySmooth.adjoin_of_algebraicIndependent hx
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨z, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange C F P y).mp hy
  rw [Subsingleton.elim z 0, map_zero]

/-- Lift a relative Kähler form to the absolute module by sending each rational coordinate
covector `d_F x_i` to its absolute covector `d_C x_i`. -/
noncomputable def kaehlerD_adjoin_absoluteLift
    {C F E I : Type*} [DecidableEq I] [Field C] [Field F] [Field E]
    [Algebra C F] [Algebra C E] [Algebra F E] [IsScalarTower C F E]
    {x : I → E} (hx : AlgebraicIndependent F x) :
    let P := IntermediateField.adjoin F (Set.range x)
    Ω[P⁄F] →ₗ[P] Ω[P⁄C] := by
  let P := IntermediateField.adjoin F (Set.range x)
  let dx : I → P := fun i ↦
    ⟨x i, IntermediateField.subset_adjoin F (Set.range x) ⟨i, rfl⟩⟩
  exact (kaehlerD_adjoin_coordinates_basis hx).constr P
    (fun i ↦ KaehlerDifferential.D C P (dx i))

/-- Reduction from absolute to relative differentials is a left inverse of the coordinate lift. -/
theorem kaehlerMap_comp_adjoin_absoluteLift
    {C F E I : Type*} [DecidableEq I] [Field C] [Field F] [Field E]
    [Algebra C F] [Algebra C E] [Algebra F E] [IsScalarTower C F E]
    {x : I → E} (hx : AlgebraicIndependent F x)
    (w : let P := IntermediateField.adjoin F (Set.range x); Ω[P⁄F]) :
    let P := IntermediateField.adjoin F (Set.range x)
    KaehlerDifferential.map C F P P (kaehlerD_adjoin_absoluteLift hx w) = w := by
  let P := IntermediateField.adjoin F (Set.range x)
  let b : Module.Basis I P Ω[P⁄F] := kaehlerD_adjoin_coordinates_basis hx
  have hcomp :
      (KaehlerDifferential.map C F P P).comp
          (kaehlerD_adjoin_absoluteLift hx) = LinearMap.id := by
    apply b.ext
    intro i
    change KaehlerDifferential.map C F P P
        ((kaehlerD_adjoin_coordinates_basis hx).constr P
          (fun j ↦ KaehlerDifferential.D C P
            (⟨x j, IntermediateField.subset_adjoin F (Set.range x) ⟨j, rfl⟩⟩ : P))
          ((kaehlerD_adjoin_coordinates_basis hx) i)) =
      (kaehlerD_adjoin_coordinates_basis hx) i
    rw [Module.Basis.constr_basis, KaehlerDifferential.map_D]
    rw [kaehlerD_adjoin_coordinates_basis_apply]
    congr 1
  exact LinearMap.congr_fun hcomp w

/-- The base-change map lands in the kernel of reduction to relative differentials. -/
theorem kaehlerMap_comp_mapBaseChange_eq_zero
    {C F E I : Type*} [Field C] [Field F] [Field E]
    [Algebra C F] [Algebra C E] [Algebra F E] [IsScalarTower C F E]
    {x : I → E}
    (u : let P := IntermediateField.adjoin F (Set.range x); P ⊗[F] Ω[F⁄C]) :
    let P := IntermediateField.adjoin F (Set.range x)
    KaehlerDifferential.map C F P P
        (KaehlerDifferential.mapBaseChange C F P u) = 0 := by
  let P := IntermediateField.adjoin F (Set.range x)
  exact (KaehlerDifferential.exact_mapBaseChange_map C F P
    (KaehlerDifferential.mapBaseChange C F P u)).mpr ⟨u, rfl⟩

/-- The canonical sum of the base differential summand and the relative coordinate summand. -/
noncomputable def kaehlerD_adjoin_absoluteDecompositionMap
    {C F E I : Type*} [DecidableEq I] [Field C] [Field F] [Field E]
    [Algebra C F] [Algebra C E] [Algebra F E] [IsScalarTower C F E]
    {x : I → E} (hx : AlgebraicIndependent F x) :
    let P := IntermediateField.adjoin F (Set.range x)
    (P ⊗[F] Ω[F⁄C]) × Ω[P⁄F] →ₗ[P] Ω[P⁄C] := by
  let P := IntermediateField.adjoin F (Set.range x)
  exact LinearMap.coprod
    (KaehlerDifferential.mapBaseChange C F P)
    (kaehlerD_adjoin_absoluteLift hx)

theorem kaehlerD_adjoin_absoluteDecompositionMap_bijective
    {C F E I : Type*} [DecidableEq I] [Field C] [Field F] [Field E]
    [Algebra C F] [Algebra C E] [Algebra F E] [IsScalarTower C F E]
    {x : I → E} (hx : AlgebraicIndependent F x) :
    Function.Bijective
      (kaehlerD_adjoin_absoluteDecompositionMap (C := C) hx) := by
  let P := IntermediateField.adjoin F (Set.range x)
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro ⟨u, v⟩ huv
    have hv : v = 0 := by
      have hmap := congrArg (KaehlerDifferential.map C F P P) huv
      change KaehlerDifferential.map C F P P
          (KaehlerDifferential.mapBaseChange C F P u +
            kaehlerD_adjoin_absoluteLift hx v) =
        KaehlerDifferential.map C F P P 0 at hmap
      rw [map_add,
        kaehlerMap_comp_mapBaseChange_eq_zero (C := C) (x := x),
        kaehlerMap_comp_adjoin_absoluteLift (C := C) hx, map_zero,
        zero_add] at hmap
      exact hmap
    subst v
    have hu : u = 0 :=
      kaehlerMapBaseChange_injective_adjoin_of_algebraicIndependent hx <| by
        simpa [kaehlerD_adjoin_absoluteDecompositionMap] using huv
    exact Prod.ext hu rfl
  · intro w
    let v := KaehlerDifferential.map C F P P w
    have hres : KaehlerDifferential.map C F P P
        (w - kaehlerD_adjoin_absoluteLift hx v) = 0 := by
      rw [map_sub, kaehlerMap_comp_adjoin_absoluteLift (C := C) hx]
      exact sub_self _
    obtain ⟨u, hu⟩ :=
      (KaehlerDifferential.exact_mapBaseChange_map C F P
        (w - kaehlerD_adjoin_absoluteLift hx v)).mp hres
    refine ⟨⟨u, v⟩, ?_⟩
    change KaehlerDifferential.mapBaseChange C F P u +
        kaehlerD_adjoin_absoluteLift hx v = w
    rw [hu]
    abel

/-- Absolute Kähler differentials split canonically into the embedded base-change module and
the free relative coordinate module. -/
noncomputable def kaehlerD_adjoin_absoluteDecomposition
    {C F E I : Type*} [DecidableEq I] [Field C] [Field F] [Field E]
    [Algebra C F] [Algebra C E] [Algebra F E] [IsScalarTower C F E]
    {x : I → E} (hx : AlgebraicIndependent F x) :=
  LinearEquiv.ofBijective
    (kaehlerD_adjoin_absoluteDecompositionMap (C := C) hx)
    (kaehlerD_adjoin_absoluteDecompositionMap_bijective (C := C) hx)

/-- Hypertranscendence identifies the intrinsic relative Kähler module with the free countable
clock packet module. -/
noncomputable def hypertranscendentalKaehlerClockEquiv
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) :
    Ω[jetObservableFieldInfinity F x⁄F] ≃ₗ[jetObservableFieldInfinity F x]
      (ℕ →₀ jetObservableFieldInfinity F x) :=
  (kaehlerD_adjoin_coordinates_basis
    (algebraicIndependent_differentialJet_of_hypertranscendentalOver hx)).repr

/-- Equation `(3)` specialized to a hypertranscendental jet tower: absolute differentials split
as the embedded base-change module plus the free relative jet-covector module. -/
noncomputable def hypertranscendentalKaehlerAbsoluteDecomposition
    {C F E : Type*} [Field C] [Field F] [Field E]
    [Algebra C F] [Algebra C E] [Algebra F E] [IsScalarTower C F E]
    [Differential E] {x : E} (hx : HypertranscendentalOver F x) :=
  kaehlerD_adjoin_absoluteDecomposition (C := C)
    (algebraicIndependent_differentialJet_of_hypertranscendentalOver hx)

@[simp] theorem hypertranscendentalKaehlerClockEquiv_apply_jet
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (n : ℕ) :
    hypertranscendentalKaehlerClockEquiv hx
        (KaehlerDifferential.D F (jetObservableFieldInfinity F x)
          (⟨differentialJet n x,
            IntermediateField.subset_adjoin F
              (Set.range fun q : ℕ ↦ differentialJet q x) ⟨n, rfl⟩⟩ :
            jetObservableFieldInfinity F x)) =
      Finsupp.single n 1 := by
  simpa [hypertranscendentalKaehlerClockEquiv,
    kaehlerD_adjoin_coordinates_basis] using
      (Module.Basis.repr_self
        (kaehlerD_adjoin_coordinates_basis
          (algebraicIndependent_differentialJet_of_hypertranscendentalOver hx)) n)

/-- The full jet-observable field is the differential field generated by the pointed source. -/
theorem jetObservableFieldInfinity_eq_differentialAdjoin_singleton
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (x : E) :
    jetObservableFieldInfinity F x = differentialAdjoin F {x} := by
  rw [jetObservableFieldInfinity, differentialAdjoin]
  congr 1
  ext y
  simp [differentialJetSet]

/-- The full jet-observable field is closed under the ambient derivation. -/
theorem derivationClosed_jetObservableFieldInfinity
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E] (x : E) :
    DerivationClosed (jetObservableFieldInfinity F x) := by
  rw [jetObservableFieldInfinity_eq_differentialAdjoin_singleton]
  exact derivationClosed_differentialAdjoin F {x}

/-- The ambient ring derivation restricted to the full rational jet field. -/
noncomputable def jetObservableFieldInfinityDerivation
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E] (x : E) :
    Derivation ℤ (jetObservableFieldInfinity F x)
      (jetObservableFieldInfinity F x) := by
  let P := jetObservableFieldInfinity F x
  letI : Differential P :=
    derivationClosedDifferential P (derivationClosed_jetObservableFieldInfinity x)
  exact Differential.deriv

@[simp] theorem jetObservableFieldInfinityDerivation_apply
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E] (x : E)
    (a : jetObservableFieldInfinity F x) :
    (jetObservableFieldInfinityDerivation x a : E) = Differential.deriv a.1 :=
  rfl

@[simp] theorem jetObservableFieldInfinityDerivation_jet
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E] (x : E) (n : ℕ) :
    jetObservableFieldInfinityDerivation x
        (⟨differentialJet n x,
          IntermediateField.subset_adjoin F
            (Set.range fun q : ℕ ↦ differentialJet q x) ⟨n, rfl⟩⟩ :
          jetObservableFieldInfinity F x) =
      (⟨differentialJet (n + 1) x,
        IntermediateField.subset_adjoin F
          (Set.range fun q : ℕ ↦ differentialJet q x) ⟨n + 1, rfl⟩⟩ :
        jetObservableFieldInfinity F x) := by
  apply Subtype.ext
  exact (differentialJet_succ n x).symm

/-- Derivatives of base-field scalars have zero relative differential in the full jet field. -/
theorem jetObservableFieldInfinityDerivation_baseCondition
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E] (x : E) (a : F) :
    KaehlerDifferential.D F (jetObservableFieldInfinity F x)
      (jetObservableFieldInfinityDerivation x
        (algebraMap F (jetObservableFieldInfinity F x) a)) = 0 := by
  let P := jetObservableFieldInfinity F x
  have hderiv : jetObservableFieldInfinityDerivation x (algebraMap F P a) =
      algebraMap F P (Differential.deriv a) := by
    apply Subtype.ext
    exact DifferentialAlgebra.deriv_algebraMap a
  rw [hderiv]
  exact (KaehlerDifferential.D F P).map_algebraMap _

/-- If `C` has zero derivation, then its scalars have zero absolute differential after applying
the jet-field derivation. -/
theorem jetObservableFieldInfinityDerivation_constantBaseCondition
    {C F E : Type*} [Field C] [Field F] [Field E]
    [Differential C] [Differential F] [Differential E]
    [Algebra C F] [Algebra C E] [Algebra F E] [IsScalarTower C F E]
    [DifferentialAlgebra C F] [DifferentialAlgebra F E]
    (hC : ∀ c : C, Differential.deriv c = 0) (x : E) (c : C) :
    KaehlerDifferential.D C (jetObservableFieldInfinity F x)
      (jetObservableFieldInfinityDerivation x
        (algebraMap C (jetObservableFieldInfinity F x) c)) = 0 := by
  let P := jetObservableFieldInfinity F x
  have hderiv : jetObservableFieldInfinityDerivation x (algebraMap C P c) = 0 := by
    apply Subtype.ext
    change Differential.deriv (algebraMap C E c) = 0
    rw [IsScalarTower.algebraMap_apply C F E,
      DifferentialAlgebra.deriv_algebraMap,
      DifferentialAlgebra.deriv_algebraMap, hC, map_zero, map_zero]
  rw [hderiv]
  simp

/-- The restricted derivation as an additive coefficient map used by the free clock model. -/
noncomputable def jetObservableFieldInfinityCoefficientDeriv
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E] (x : E) :
    jetObservableFieldInfinity F x →+ jetObservableFieldInfinity F x :=
  (jetObservableFieldInfinityDerivation x).toLinearMap.toAddMonoidHom

@[simp] theorem jetObservableFieldInfinityCoefficientDeriv_apply
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E] (x : E)
    (a : jetObservableFieldInfinity F x) :
    (jetObservableFieldInfinityCoefficientDeriv x a : E) = Differential.deriv a.1 :=
  rfl

/-- The intrinsic relative Kähler connection induced by the differential-field derivation. -/
noncomputable def hypertranscendentalRelativeKaehlerConnection
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E] (x : E) :
    Ω[jetObservableFieldInfinity F x⁄F] →+
      Ω[jetObservableFieldInfinity F x⁄F] :=
  kaehlerConnectionDifferential
    (jetObservableFieldInfinityDerivation x)
    (jetObservableFieldInfinityDerivation_baseCondition x)

/-- Exact connection formula on every elementary relative jet-field one-form. -/
theorem hypertranscendentalRelativeKaehlerConnection_smul_D
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E] (x : E)
    (a b : jetObservableFieldInfinity F x) :
    hypertranscendentalRelativeKaehlerConnection x
        (a • KaehlerDifferential.D F (jetObservableFieldInfinity F x) b) =
      jetObservableFieldInfinityDerivation x a •
          KaehlerDifferential.D F (jetObservableFieldInfinity F x) b +
        a • KaehlerDifferential.D F (jetObservableFieldInfinity F x)
          (jetObservableFieldInfinityDerivation x b) := by
  rw [hypertranscendentalRelativeKaehlerConnection,
    kaehlerConnectionDifferential_smul,
    kaehlerConnectionDifferential_D]
  rfl

/-- The absolute Kähler Lie derivative over a zero-derivation constant field. -/
noncomputable def hypertranscendentalAbsoluteKaehlerLie
    {C F E : Type*} [Field C] [Field F] [Field E]
    [Differential C] [Differential F] [Differential E]
    [Algebra C F] [Algebra C E] [Algebra F E] [IsScalarTower C F E]
    [DifferentialAlgebra C F] [DifferentialAlgebra F E]
    (hC : ∀ c : C, Differential.deriv c = 0) (x : E) :
    Ω[jetObservableFieldInfinity F x⁄C] →+
      Ω[jetObservableFieldInfinity F x⁄C] :=
  kaehlerConnectionDifferential
    (jetObservableFieldInfinityDerivation x)
    (jetObservableFieldInfinityDerivation_constantBaseCondition hC x)

/-- Formula `(4)`: the absolute Lie derivative obeys the connection Leibniz rule on every
elementary one-form. -/
theorem hypertranscendentalAbsoluteKaehlerLie_smul_D
    {C F E : Type*} [Field C] [Field F] [Field E]
    [Differential C] [Differential F] [Differential E]
    [Algebra C F] [Algebra C E] [Algebra F E] [IsScalarTower C F E]
    [DifferentialAlgebra C F] [DifferentialAlgebra F E]
    (hC : ∀ c : C, Differential.deriv c = 0) (x : E)
    (a b : jetObservableFieldInfinity F x) :
    hypertranscendentalAbsoluteKaehlerLie hC x
        (a • KaehlerDifferential.D C (jetObservableFieldInfinity F x) b) =
      jetObservableFieldInfinityDerivation x a •
          KaehlerDifferential.D C (jetObservableFieldInfinity F x) b +
        a • KaehlerDifferential.D C (jetObservableFieldInfinity F x)
          (jetObservableFieldInfinityDerivation x b) := by
  rw [hypertranscendentalAbsoluteKaehlerLie,
    kaehlerConnectionDifferential_smul,
    kaehlerConnectionDifferential_D]
  rfl

/-- Absolute-to-relative reduction intertwines the actual Kähler Lie derivative and the
relative jet connection. -/
theorem hypertranscendentalKaehlerLie_map_absoluteToRelative
    {C F E : Type*} [Field C] [Field F] [Field E]
    [Differential C] [Differential F] [Differential E]
    [Algebra C F] [Algebra C E] [Algebra F E] [IsScalarTower C F E]
    [DifferentialAlgebra C F] [DifferentialAlgebra F E]
    (hC : ∀ c : C, Differential.deriv c = 0) (x : E)
    (w : Ω[jetObservableFieldInfinity F x⁄C]) :
    KaehlerDifferential.map C F (jetObservableFieldInfinity F x)
        (jetObservableFieldInfinity F x)
        (hypertranscendentalAbsoluteKaehlerLie hC x w) =
      hypertranscendentalRelativeKaehlerConnection x
        (KaehlerDifferential.map C F (jetObservableFieldInfinity F x)
          (jetObservableFieldInfinity F x) w) := by
  exact kaehlerConnectionDifferential_map
    (jetObservableFieldInfinityDerivation x)
    (jetObservableFieldInfinityDerivation_constantBaseCondition hC x)
    (jetObservableFieldInfinityDerivation_baseCondition x) w

/-- The base differential summand `P ⊗_F Ω[F/C]` is invariant under the absolute Lie
derivative. -/
theorem hypertranscendentalAbsoluteKaehlerLie_mem_baseSummand
    {C F E : Type*} [Field C] [Field F] [Field E]
    [Differential C] [Differential F] [Differential E]
    [Algebra C F] [Algebra C E] [Algebra F E] [IsScalarTower C F E]
    [DifferentialAlgebra C F] [DifferentialAlgebra F E]
    (hC : ∀ c : C, Differential.deriv c = 0) (x : E)
    {w : Ω[jetObservableFieldInfinity F x⁄C]}
    (hw : w ∈ LinearMap.range (KaehlerDifferential.mapBaseChange C F
      (jetObservableFieldInfinity F x))) :
    hypertranscendentalAbsoluteKaehlerLie hC x w ∈
      LinearMap.range (KaehlerDifferential.mapBaseChange C F
        (jetObservableFieldInfinity F x)) := by
  exact kaehlerConnectionDifferential_mem_range_mapBaseChange
    (jetObservableFieldInfinityDerivation x)
    (jetObservableFieldInfinityDerivation_constantBaseCondition hC x)
    (jetObservableFieldInfinityDerivation_baseCondition x) hw

/-- The intrinsic finite Kähler clock filtration, transported from basis coefficients. -/
noncomputable def hypertranscendentalKaehlerFiltration
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (N : ℕ) :
    Submodule (jetObservableFieldInfinity F x)
      Ω[jetObservableFieldInfinity F x⁄F] :=
  (kaehlerClockFiltration (jetObservableFieldInfinity F x) N).comap
    (hypertranscendentalKaehlerClockEquiv hx).toLinearMap

/-- Equation `(2)`: the absolute clock filtration is the inverse image of the first `N`
relative jet-covector layers.  Its kernel is exactly the base differential summand by the
Jacobi--Zariski exact sequence. -/
noncomputable def hypertranscendentalAbsoluteKaehlerFiltration
    {C F E : Type*} [Field C] [Field F] [Field E]
    [Algebra C F] [Algebra C E] [Algebra F E] [IsScalarTower C F E]
    [Differential E] {x : E} (hx : HypertranscendentalOver F x) (N : ℕ) :
    Submodule (jetObservableFieldInfinity F x)
      Ω[jetObservableFieldInfinity F x⁄C] :=
  (hypertranscendentalKaehlerFiltration hx N).comap
    (KaehlerDifferential.map C F (jetObservableFieldInfinity F x)
      (jetObservableFieldInfinity F x))

/-- Every base differential lies in every absolute clock cut. -/
theorem hypertranscendentalBaseSummand_le_absoluteFiltration
    {C F E : Type*} [Field C] [Field F] [Field E]
    [Algebra C F] [Algebra C E] [Algebra F E] [IsScalarTower C F E]
    [Differential E] {x : E} (hx : HypertranscendentalOver F x) (N : ℕ) :
    LinearMap.range (KaehlerDifferential.mapBaseChange C F
      (jetObservableFieldInfinity F x)) ≤
        hypertranscendentalAbsoluteKaehlerFiltration hx N := by
  rw [KaehlerDifferential.range_mapBaseChange]
  intro w hw
  change KaehlerDifferential.map C F (jetObservableFieldInfinity F x)
      (jetObservableFieldInfinity F x) w ∈
    hypertranscendentalKaehlerFiltration hx N
  rw [LinearMap.mem_ker] at hw
  rw [hw]
  exact Submodule.zero_mem _

/-- The intrinsic rank-one Kähler clock line, transported from the `N`-th basis coordinate. -/
noncomputable def hypertranscendentalKaehlerGradedLine
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (N : ℕ) :
    Submodule (jetObservableFieldInfinity F x)
      Ω[jetObservableFieldInfinity F x⁄F] :=
  (kaehlerClockGradedLine (jetObservableFieldInfinity F x) N).comap
    (hypertranscendentalKaehlerClockEquiv hx).toLinearMap

/-- The intrinsic `N`-th Kähler clock line lies in the first `N+1` jet covectors. -/
theorem hypertranscendentalKaehlerGradedLine_le_filtration
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (N : ℕ) :
    hypertranscendentalKaehlerGradedLine hx N ≤
      hypertranscendentalKaehlerFiltration hx (N + 1) :=
  Submodule.comap_mono (kaehlerClockGradedLine_le_filtration _ N)

/-- The intrinsic Lie derivative on the relative Kähler jet basis. -/
noncomputable def hypertranscendentalKaehlerLie
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E]
    {x : E} (hx : HypertranscendentalOver F x) :
    Ω[jetObservableFieldInfinity F x⁄F] →+ Ω[jetObservableFieldInfinity F x⁄F] where
  toFun ω := (hypertranscendentalKaehlerClockEquiv hx).symm
    (kaehlerClockLie (jetObservableFieldInfinityCoefficientDeriv x)
      (hypertranscendentalKaehlerClockEquiv hx ω))
  map_zero' := by simp
  map_add' a b := by simp

/-- The basis-transported clock operator is the canonical relative Kähler connection, not a
coordinate wrapper. -/
theorem hypertranscendentalKaehlerLie_eq_relativeConnection
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E]
    {x : E} (hx : HypertranscendentalOver F x)
    (w : Ω[jetObservableFieldInfinity F x⁄F]) :
    hypertranscendentalKaehlerLie hx w =
      hypertranscendentalRelativeKaehlerConnection x w := by
  let e := hypertranscendentalKaehlerClockEquiv hx
  let a := e w
  have hw : w = e.symm a := by
    exact (e.symm_apply_apply w).symm
  apply e.injective
  rw [hw]
  change (hypertranscendentalKaehlerClockEquiv hx)
      ((hypertranscendentalKaehlerClockEquiv hx).symm
        (kaehlerClockLie (jetObservableFieldInfinityCoefficientDeriv x)
          ((hypertranscendentalKaehlerClockEquiv hx)
            ((hypertranscendentalKaehlerClockEquiv hx).symm a)))) =
    (hypertranscendentalKaehlerClockEquiv hx)
      (hypertranscendentalRelativeKaehlerConnection x
        ((hypertranscendentalKaehlerClockEquiv hx).symm a))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      simp only [map_add, hf, hg]
  | single n c =>
      let jn : jetObservableFieldInfinity F x :=
        ⟨differentialJet n x,
          IntermediateField.subset_adjoin F
            (Set.range fun q : ℕ ↦ differentialJet q x) ⟨n, rfl⟩⟩
      let jn1 : jetObservableFieldInfinity F x :=
        ⟨differentialJet (n + 1) x,
          IntermediateField.subset_adjoin F
            (Set.range fun q : ℕ ↦ differentialJet q x) ⟨n + 1, rfl⟩⟩
      have hejn : e (KaehlerDifferential.D F
          (jetObservableFieldInfinity F x) jn) = Finsupp.single n 1 := by
        simpa only [e, jn] using
          hypertranscendentalKaehlerClockEquiv_apply_jet hx n
      have hejn1 : e (KaehlerDifferential.D F
          (jetObservableFieldInfinity F x) jn1) =
          Finsupp.single (n + 1) 1 := by
        simpa only [e, jn1] using
          hypertranscendentalKaehlerClockEquiv_apply_jet hx (n + 1)
      have hsingle : e.symm (Finsupp.single n c) =
          c • KaehlerDifferential.D F (jetObservableFieldInfinity F x) jn := by
        apply e.injective
        rw [e.apply_symm_apply, map_smul, hejn]
        simp
      have hjet : jetObservableFieldInfinityDerivation x jn = jn1 := by
        simp [jn, jn1]
      rw [hsingle, hypertranscendentalRelativeKaehlerConnection_smul_D]
      rw [kaehlerClockLie_single]
      rw [hjet]
      rw [map_add, map_smul, map_smul, hejn, hejn1]
      simp [jetObservableFieldInfinityCoefficientDeriv]

@[simp] theorem hypertranscendentalKaehlerClockEquiv_apply_lie
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E]
    {x : E} (hx : HypertranscendentalOver F x)
    (ω : Ω[jetObservableFieldInfinity F x⁄F]) :
    hypertranscendentalKaehlerClockEquiv hx
        (hypertranscendentalKaehlerLie hx ω) =
      kaehlerClockLie (jetObservableFieldInfinityCoefficientDeriv x)
        (hypertranscendentalKaehlerClockEquiv hx ω) := by
  simp [hypertranscendentalKaehlerLie]

/-- The intrinsic Kähler Lie operator raises the finite clock filtration by at most one. -/
theorem hypertranscendentalKaehlerLie_mem_succ
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E]
    {x : E} (hx : HypertranscendentalOver F x) {N : ℕ}
    {ω : Ω[jetObservableFieldInfinity F x⁄F]}
    (hω : ω ∈ hypertranscendentalKaehlerFiltration hx N) :
    hypertranscendentalKaehlerLie hx ω ∈
      hypertranscendentalKaehlerFiltration hx (N + 1) := by
  change hypertranscendentalKaehlerClockEquiv hx ω ∈
    kaehlerClockFiltration (jetObservableFieldInfinity F x) N at hω
  change hypertranscendentalKaehlerClockEquiv hx
      (hypertranscendentalKaehlerLie hx ω) ∈
    kaehlerClockFiltration (jetObservableFieldInfinity F x) (N + 1)
  simpa [hypertranscendentalKaehlerLie] using
    (kaehlerClockLie_mem_succ
      (jetObservableFieldInfinityCoefficientDeriv x) hω)

/-- Equation `(5)`: the absolute Kähler Lie derivative raises the base-plus-jet filtration by
at most one. -/
theorem hypertranscendentalAbsoluteKaehlerLie_mem_succ
    {C F E : Type*} [Field C] [Field F] [Field E]
    [Differential C] [Differential F] [Differential E]
    [Algebra C F] [Algebra C E] [Algebra F E] [IsScalarTower C F E]
    [DifferentialAlgebra C F] [DifferentialAlgebra F E]
    (hC : ∀ c : C, Differential.deriv c = 0)
    {x : E} (hx : HypertranscendentalOver F x) {N : ℕ}
    {w : Ω[jetObservableFieldInfinity F x⁄C]}
    (hw : w ∈ hypertranscendentalAbsoluteKaehlerFiltration hx N) :
    hypertranscendentalAbsoluteKaehlerLie hC x w ∈
      hypertranscendentalAbsoluteKaehlerFiltration hx (N + 1) := by
  change KaehlerDifferential.map C F (jetObservableFieldInfinity F x)
      (jetObservableFieldInfinity F x) w ∈
    hypertranscendentalKaehlerFiltration hx N at hw
  change KaehlerDifferential.map C F (jetObservableFieldInfinity F x)
      (jetObservableFieldInfinity F x)
        (hypertranscendentalAbsoluteKaehlerLie hC x w) ∈
    hypertranscendentalKaehlerFiltration hx (N + 1)
  rw [hypertranscendentalKaehlerLie_map_absoluteToRelative]
  rw [← hypertranscendentalKaehlerLie_eq_relativeConnection hx]
  exact hypertranscendentalKaehlerLie_mem_succ hx hw

/-- Basis coordinates restrict to an equivalence from each intrinsic Kähler clock line to its
free rank-one coefficient line. -/
noncomputable def hypertranscendentalKaehlerGradedEquiv
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (N : ℕ) :
    hypertranscendentalKaehlerGradedLine hx N ≃ₗ[jetObservableFieldInfinity F x]
      kaehlerClockGradedLine (jetObservableFieldInfinity F x) N :=
  (hypertranscendentalKaehlerClockEquiv hx).ofSubmodule'
    (kaehlerClockGradedLine (jetObservableFieldInfinity F x) N)

/-- Every intrinsic homogeneous Kähler jet line is canonically one-dimensional. -/
noncomputable def hypertranscendentalKaehlerGradedCoordinateEquiv
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (N : ℕ) :
    hypertranscendentalKaehlerGradedLine hx N ≃ₗ[jetObservableFieldInfinity F x]
      jetObservableFieldInfinity F x :=
  (hypertranscendentalKaehlerGradedEquiv hx N).trans
    (kaehlerClockGradedCoordinateEquiv (jetObservableFieldInfinity F x) N)

/-- The intrinsic degree-one principal symbol on adjacent Kähler clock lines. -/
noncomputable def hypertranscendentalKaehlerPrincipalSymbolEquiv
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (N : ℕ) :
    hypertranscendentalKaehlerGradedLine hx N ≃ₗ[jetObservableFieldInfinity F x]
      hypertranscendentalKaehlerGradedLine hx (N + 1) :=
  (hypertranscendentalKaehlerGradedEquiv hx N).trans <|
    (kaehlerClockPrincipalSymbolEquiv (jetObservableFieldInfinity F x) N).trans <|
      (hypertranscendentalKaehlerGradedEquiv hx (N + 1)).symm

@[simp] theorem hypertranscendentalKaehlerGradedEquiv_apply_principalSymbol
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (N : ℕ)
    (a : hypertranscendentalKaehlerGradedLine hx N) :
    hypertranscendentalKaehlerGradedEquiv hx (N + 1)
        (hypertranscendentalKaehlerPrincipalSymbolEquiv hx N a) =
      kaehlerClockPrincipalSymbolEquiv (jetObservableFieldInfinity F x) N
        (hypertranscendentalKaehlerGradedEquiv hx N a) := by
  simp [hypertranscendentalKaehlerPrincipalSymbolEquiv]

/-- The intrinsic principal symbol is the identity on the scalar coordinate of adjacent lines. -/
theorem hypertranscendentalKaehlerPrincipalSymbol_coordinate
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (N : ℕ)
    (a : hypertranscendentalKaehlerGradedLine hx N) :
    hypertranscendentalKaehlerGradedCoordinateEquiv hx (N + 1)
        (hypertranscendentalKaehlerPrincipalSymbolEquiv hx N a) =
      hypertranscendentalKaehlerGradedCoordinateEquiv hx N a := by
  simp [hypertranscendentalKaehlerPrincipalSymbolEquiv,
    hypertranscendentalKaehlerGradedCoordinateEquiv,
    kaehlerClockPrincipalSymbolEquiv]

/-- Projection of an intrinsic Kähler form to its `N`-th homogeneous clock line. -/
noncomputable def hypertranscendentalKaehlerGradedProjection
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (N : ℕ) :
    Ω[jetObservableFieldInfinity F x⁄F] →ₗ[jetObservableFieldInfinity F x]
      hypertranscendentalKaehlerGradedLine hx N where
  toFun ω := ⟨(hypertranscendentalKaehlerClockEquiv hx).symm
      (kaehlerClockGradedProjection (jetObservableFieldInfinity F x) N
        (hypertranscendentalKaehlerClockEquiv hx ω)), by
    change hypertranscendentalKaehlerClockEquiv hx
        ((hypertranscendentalKaehlerClockEquiv hx).symm
          (kaehlerClockGradedProjection (jetObservableFieldInfinity F x) N
            (hypertranscendentalKaehlerClockEquiv hx ω))) ∈
        kaehlerClockGradedLine (jetObservableFieldInfinity F x) N
    rw [LinearEquiv.apply_symm_apply]
    exact (kaehlerClockGradedProjection (jetObservableFieldInfinity F x) N
      (hypertranscendentalKaehlerClockEquiv hx ω)).2⟩
  map_add' a b := by
    apply Subtype.ext
    simp
  map_smul' c a := by
    apply Subtype.ext
    simp

@[simp] theorem hypertranscendentalKaehlerGradedEquiv_apply_projection
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (N : ℕ)
    (ω : Ω[jetObservableFieldInfinity F x⁄F]) :
    hypertranscendentalKaehlerGradedEquiv hx N
        (hypertranscendentalKaehlerGradedProjection hx N ω) =
      kaehlerClockGradedProjection (jetObservableFieldInfinity F x) N
        (hypertranscendentalKaehlerClockEquiv hx ω) := by
  apply Subtype.ext
  let p := kaehlerClockGradedProjection (jetObservableFieldInfinity F x) N
    (hypertranscendentalKaehlerClockEquiv hx ω)
  change hypertranscendentalKaehlerClockEquiv hx
      ((hypertranscendentalKaehlerClockEquiv hx).symm (p : ℕ →₀ jetObservableFieldInfinity F x)) =
    (p : ℕ →₀ jetObservableFieldInfinity F x)
  exact (hypertranscendentalKaehlerClockEquiv hx).apply_symm_apply _

/-- The intrinsic principal symbol is exactly the next homogeneous projection of the intrinsic
Kähler Lie derivative. -/
theorem hypertranscendentalKaehlerPrincipalSymbol_eq_lie_projection
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E]
    {x : E} (hx : HypertranscendentalOver F x) (N : ℕ)
    (a : hypertranscendentalKaehlerGradedLine hx N) :
    hypertranscendentalKaehlerPrincipalSymbolEquiv hx N a =
      hypertranscendentalKaehlerGradedProjection hx (N + 1)
        (hypertranscendentalKaehlerLie hx a.1) := by
  apply (hypertranscendentalKaehlerGradedEquiv hx (N + 1)).injective
  rw [hypertranscendentalKaehlerGradedEquiv_apply_principalSymbol,
    hypertranscendentalKaehlerGradedEquiv_apply_projection,
    hypertranscendentalKaehlerClockEquiv_apply_lie,
    kaehlerClockPrincipalSymbolEquiv_apply]
  exact kaehlerClockPrincipalSymbol_eq_lie_projection
    (jetObservableFieldInfinityCoefficientDeriv x) N
      (hypertranscendentalKaehlerGradedEquiv hx N a)

end

end GaloisForLFunctions.HTGeometry
