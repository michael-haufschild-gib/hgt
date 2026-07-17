import GaloisForLFunctions.HTGeometry.OrbitMarkerSourceFaceReconstruction
import GaloisForLFunctions.HTGeometry.EllipticThetaLogComparisonRigidity
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Inductions

/-!
# Differential localization of finite orbit markers

An additive reporter on marker coefficients can only forget translation symmetry: the
translation stabilizer of the reported marker contains that of the original marker.  An injective
reporter preserves the stabilizer exactly, and two reporters recover it jointly whenever their
paired coefficient map is injective.

For polynomial principal-part labels this produces an exact differential thickening.  Constant
coefficient (simple-residue) data are the quotient of the full marker by multiplication by `X`,
while the kernel is exactly the `X`-shifted tail.  Every finite coefficient window is blind to an
aperiodic high-order atom, but the all-coefficient reporter preserves every stabilizer.  Thus no
fixed finite principal-part depth is conservative on all markers, whereas the cofinal reporter is.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Apply an additive reporter coefficientwise to a finite orbit marker. -/
def mapFiniteSupportCoefficients
    {G A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (phi : A →+ B) (D : G →₀ A) : G →₀ B :=
  D.mapRange phi phi.map_zero

@[simp]
theorem mapFiniteSupportCoefficients_apply
    {G A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (phi : A →+ B) (D : G →₀ A) (x : G) :
    mapFiniteSupportCoefficients phi D x = phi (D x) :=
  rfl

/-- Translation commutes with every additive coefficient reporter. -/
theorem translateFiniteSupport_mapFiniteSupportCoefficients
    {G A B : Type*} [AddCommGroup G] [AddCommMonoid A] [AddCommMonoid B]
    (q : G) (phi : A →+ B) (D : G →₀ A) :
    translateFiniteSupport q (mapFiniteSupportCoefficients phi D) =
      mapFiniteSupportCoefficients phi (translateFiniteSupport q D) := by
  exact Finsupp.mapDomain_mapRange (fun x : G ↦ x + q) D phi phi.map_zero phi.map_add

/-- Coefficient forgetting can only enlarge the group of invisible translations. -/
theorem finiteSupportTranslationStabilizer_le_of_coefficientReporter
    {G A B : Type*} [AddCommGroup G] [AddCommMonoid A] [AddCommMonoid B]
    (phi : A →+ B) (D : G →₀ A) :
    finiteSupportTranslationStabilizer D ≤
      finiteSupportTranslationStabilizer (mapFiniteSupportCoefficients phi D) := by
  intro q hq
  change translateFiniteSupport q (mapFiniteSupportCoefficients phi D) =
    mapFiniteSupportCoefficients phi D
  rw [translateFiniteSupport_mapFiniteSupportCoefficients]
  exact congrArg (mapFiniteSupportCoefficients phi) hq

/-- An injective coefficient reporter loses no translation symmetry. -/
theorem finiteSupportTranslationStabilizer_mapCoefficients_eq_of_injective
    {G A B : Type*} [AddCommGroup G] [AddCommMonoid A] [AddCommMonoid B]
    (phi : A →+ B) (hphi : Function.Injective phi) (D : G →₀ A) :
    finiteSupportTranslationStabilizer (mapFiniteSupportCoefficients phi D) =
      finiteSupportTranslationStabilizer D := by
  apply le_antisymm
  · intro q hq
    change translateFiniteSupport q (mapFiniteSupportCoefficients phi D) =
      mapFiniteSupportCoefficients phi D at hq
    change translateFiniteSupport q D = D
    apply Finsupp.mapRange_injective phi phi.map_zero hphi
    rw [translateFiniteSupport_mapFiniteSupportCoefficients] at hq
    exact hq
  · exact finiteSupportTranslationStabilizer_le_of_coefficientReporter phi D

/-- Two coarse coefficient reporters recover the exact stabilizer whenever their joint reporter
is injective.  This is the marker-level common-kernel conservativity theorem. -/
theorem pairedCoefficientReporters_stabilizer_inf_eq
    {G A B C : Type*} [AddCommGroup G]
    [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]
    (phi : A →+ B) (psi : A →+ C)
    (hpair : Function.Injective (fun a ↦ (phi a, psi a)))
    (D : G →₀ A) :
    finiteSupportTranslationStabilizer (mapFiniteSupportCoefficients phi D) ⊓
        finiteSupportTranslationStabilizer (mapFiniteSupportCoefficients psi D) =
      finiteSupportTranslationStabilizer D := by
  apply le_antisymm
  · intro q hq
    rcases hq with ⟨hphi, hpsi⟩
    change translateFiniteSupport q D = D
    apply Finsupp.ext
    intro x
    apply hpair
    apply Prod.ext
    · have hx := congrArg (fun E : G →₀ B ↦ E x) hphi
      simpa only [translateFiniteSupport_mapFiniteSupportCoefficients,
        mapFiniteSupportCoefficients_apply] using hx
    · have hx := congrArg (fun E : G →₀ C ↦ E x) hpsi
      simpa only [translateFiniteSupport_mapFiniteSupportCoefficients,
        mapFiniteSupportCoefficients_apply] using hx
  · intro q hq
    exact ⟨
      finiteSupportTranslationStabilizer_le_of_coefficientReporter phi D hq,
      finiteSupportTranslationStabilizer_le_of_coefficientReporter psi D hq⟩

/-! ## Polynomial principal-part labels -/

/-- The finite reporter retaining coefficients of orders strictly below `n`. -/
def polynomialJetReporter (n : ℕ) : Polynomial ℂ →+ (Fin n → ℂ) where
  toFun p i := p.coeff i
  map_zero' := by ext i; simp
  map_add' p q := by ext i; simp

/-- The cofinal reporter retaining every polynomial coefficient. -/
def polynomialAllCoefficients : Polynomial ℂ →+ (ℕ → ℂ) where
  toFun p i := p.coeff i
  map_zero' := by ext i; simp
  map_add' p q := by ext i; simp

theorem polynomialAllCoefficients_injective :
    Function.Injective polynomialAllCoefficients := by
  intro p q hpq
  apply Polynomial.ext
  intro n
  exact congrFun hpq n

@[simp]
theorem polynomialJetReporter_X_pow (n : ℕ) :
    polynomialJetReporter n (Polynomial.X ^ n) = 0 := by
  ext i
  simp [polynomialJetReporter, Polynomial.coeff_X_pow, Nat.ne_of_lt i.isLt]

/-- Exact finite-depth kernel: the first `n` coefficient reporters vanish precisely on labels
divisible by `X^n`. -/
theorem polynomialJetReporter_eq_zero_iff (n : ℕ) (p : Polynomial ℂ) :
    polynomialJetReporter n p = 0 ↔ Polynomial.X ^ n ∣ p := by
  rw [Polynomial.X_pow_dvd_iff]
  constructor
  · intro hp d hd
    have hd' := congrFun hp ⟨d, hd⟩
    simpa [polynomialJetReporter] using hd'
  · intro hp
    ext i
    exact hp i i.isLt

/-- The coefficientwise depth-`n` kernel consists exactly of markers whose every label is
divisible by `X^n`. -/
theorem finiteJetMarker_eq_zero_iff_pointwise_X_pow_dvd
    {G : Type*} (n : ℕ) (D : G →₀ Polynomial ℂ) :
    mapFiniteSupportCoefficients (polynomialJetReporter n) D = 0 ↔
      ∀ x, Polynomial.X ^ n ∣ D x := by
  constructor
  · intro hD x
    apply (polynomialJetReporter_eq_zero_iff n (D x)).mp
    have hx := congrArg (fun E : G →₀ (Fin n → ℂ) ↦ E x) hD
    simpa only [mapFiniteSupportCoefficients_apply, Finsupp.zero_apply] using hx
  · intro hD
    apply Finsupp.ext
    intro x
    simpa only [mapFiniteSupportCoefficients_apply, Finsupp.zero_apply] using
      (polynomialJetReporter_eq_zero_iff n (D x)).mpr (hD x)

/-- Although no fixed finite depth is conservative on all markers, every particular nonzero
finite marker is detected at some finite coefficient depth. -/
theorem exists_finiteJetMarker_ne_zero_of_ne_zero
    {G : Type*} (D : G →₀ Polynomial ℂ) (hD : D ≠ 0) :
    ∃ n, mapFiniteSupportCoefficients (polynomialJetReporter n) D ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, D x ≠ 0 := by
    simpa [Finsupp.ext_iff] using hD
  obtain ⟨k, hk⟩ : ∃ k, (D x).coeff k ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hx (Polynomial.ext fun n ↦ by simpa using hall n)
  refine ⟨k + 1, ?_⟩
  intro hzero
  have hxzero := congrArg (fun E : G →₀ (Fin (k + 1) → ℂ) ↦ E x) hzero
  have hkzero := congrFun hxzero ⟨k, Nat.lt_succ_self k⟩
  exact hk (by simpa [polynomialJetReporter] using hkzero)

/-- At every finite principal-part depth there is a high-order atom which becomes the zero marker,
although the full differential marker is aperiodic. -/
theorem finiteJetMarker_blind_fullMarker_aperiodic
    {G : Type*} [AddCommGroup G] (n : ℕ) (x : G) :
    finiteSupportTranslationStabilizer
        (mapFiniteSupportCoefficients (polynomialJetReporter n)
          (Finsupp.single x (Polynomial.X ^ n : Polynomial ℂ))) = ⊤ ∧
      finiteSupportTranslationStabilizer
        (Finsupp.single x (Polynomial.X ^ n : Polynomial ℂ)) = ⊥ := by
  constructor
  · have hzero : mapFiniteSupportCoefficients (polynomialJetReporter n)
        (Finsupp.single x (Polynomial.X ^ n : Polynomial ℂ)) = 0 := by
      simp [mapFiniteSupportCoefficients]
    rw [hzero, finiteSupportTranslationStabilizer_zero_eq_top]
  · exact finiteSupportTranslationStabilizer_single_eq_bot x
      (pow_ne_zero n Polynomial.X_ne_zero)

/-- The all-order coefficient reporter is exactly conservative for translation symmetry. -/
theorem allCoefficientMarker_stabilizer_eq
    {G : Type*} [AddCommGroup G] (D : G →₀ Polynomial ℂ) :
    finiteSupportTranslationStabilizer
        (mapFiniteSupportCoefficients polynomialAllCoefficients D) =
      finiteSupportTranslationStabilizer D :=
  finiteSupportTranslationStabilizer_mapCoefficients_eq_of_injective
    polynomialAllCoefficients polynomialAllCoefficients_injective D

/-! ## The exact differential-divisor shadow -/

/-- Forget every differential principal-part coefficient except the constant/simple-residue
coefficient. -/
def polynomialDivisorReporter : Polynomial ℂ →+ ℂ where
  toFun p := p.coeff 0
  map_zero' := by simp
  map_add' p q := by simp

/-- Multiplication by `X`, the differential prolongation direction. -/
def polynomialXShift : Polynomial ℂ →+ Polynomial ℂ where
  toFun p := Polynomial.X * p
  map_zero' := by simp
  map_add' p q := by simp [mul_add]

/-- Remove one differential order from a polynomial principal-part label. -/
def polynomialTailReporter : Polynomial ℂ →+ Polynomial ℂ :=
  Polynomial.divX_hom

def divisorShadow {G : Type*} (D : G →₀ Polynomial ℂ) : G →₀ ℂ :=
  mapFiniteSupportCoefficients polynomialDivisorReporter D

def differentialMarkerShift {G : Type*} (D : G →₀ Polynomial ℂ) :
    G →₀ Polynomial ℂ :=
  mapFiniteSupportCoefficients polynomialXShift D

def differentialMarkerTail {G : Type*} (D : G →₀ Polynomial ℂ) :
    G →₀ Polynomial ℂ :=
  mapFiniteSupportCoefficients polynomialTailReporter D

@[simp]
theorem divisorShadow_differentialMarkerShift
    {G : Type*} (D : G →₀ Polynomial ℂ) :
    divisorShadow (differentialMarkerShift D) = 0 := by
  ext x
  simp [divisorShadow, differentialMarkerShift, mapFiniteSupportCoefficients,
    polynomialDivisorReporter, polynomialXShift]

/-- The simple-residue shadow has exactly one information-loss direction: its kernel is the image
of differential prolongation by `X`. -/
theorem divisorShadow_eq_zero_iff_exists_differentialMarkerShift
    {G : Type*} (D : G →₀ Polynomial ℂ) :
    divisorShadow D = 0 ↔
      ∃ E : G →₀ Polynomial ℂ, differentialMarkerShift E = D := by
  constructor
  · intro hD
    refine ⟨differentialMarkerTail D, ?_⟩
    apply Finsupp.ext
    intro x
    have hx := congrArg (fun E : G →₀ ℂ ↦ E x) hD
    have hcoeff : (D x).coeff 0 = 0 := by
      simpa [divisorShadow, mapFiniteSupportCoefficients, polynomialDivisorReporter] using hx
    simpa [differentialMarkerShift, differentialMarkerTail,
      mapFiniteSupportCoefficients, polynomialXShift, polynomialTailReporter, hcoeff]
      using Polynomial.X_mul_divX_add (D x)
  · rintro ⟨E, rfl⟩
    exact divisorShadow_differentialMarkerShift E

/-- A single `X`-labelled atom proves strictness of the divisor shadow: the ordinary shadow is
totally translation-blind while the differential marker reconstructs the orbit subgroup exactly. -/
theorem divisorShadow_blind_differentialAtom_aperiodic
    {G : Type*} [AddCommGroup G] (x : G) :
    finiteSupportTranslationStabilizer
        (divisorShadow (Finsupp.single x (Polynomial.X : Polynomial ℂ))) = ⊤ ∧
      finiteSupportTranslationStabilizer
        (Finsupp.single x (Polynomial.X : Polynomial ℂ)) = ⊥ := by
  constructor
  · have hzero : divisorShadow
        (Finsupp.single x (Polynomial.X : Polynomial ℂ)) = 0 := by
      ext y
      simp [divisorShadow, mapFiniteSupportCoefficients, polynomialDivisorReporter]
    rw [hzero, finiteSupportTranslationStabilizer_zero_eq_top]
  · exact finiteSupportTranslationStabilizer_single_eq_bot x Polynomial.X_ne_zero

/-! ## The regular complement at two independent periods -/

open Metric

/-- An entire function with two oriented lattice periods is constant.  This is the regular-sector
complement to the singular marker theorem: after principal parts remove every zero and pole of a
rank-two source-fixed gauge, compact period reduction kills the remaining entire gauge. -/
theorem analyticOnNhd_constant_of_period_one_tau
    (f : ℂ → ℂ) (tau : ℂ) (htau : 0 < tau.im)
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hone : Function.Periodic f 1) (htauPeriod : Function.Periodic f tau) :
    ∀ z w, f z = f w := by
  have hdiff : Differentiable ℂ f := fun z =>
    (hf z (Set.mem_univ z)).differentiableAt
  have hcont : Continuous f := hdiff.continuous
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : ℂ) (1 + ‖tau‖)).bddAbove_image
      hcont.norm.continuousOn
  have hglobal : ∀ z, ‖f z‖ ≤ C := by
    intro z
    let r := ellipticReduce tau z
    have hr : r ∈ closedBall (0 : ℂ) (1 + ‖tau‖) := by
      simpa [mem_closedBall] using ellipticReduce_norm_le tau z
    have hfr : ‖f r‖ ≤ C := hC (Set.mem_image_of_mem (fun w => ‖f w‖) hr)
    have hdecomp := ellipticReduce_lattice_decomposition
      (τ := tau) (z := z) (ne_of_gt htau)
    have honeM := hone.int_mul ⌊tauCoordX tau z⌋
    have htauN := htauPeriod.int_mul ⌊tauCoordY tau z⌋
    have hfzr : f z = f r := by
      rw [hdecomp]
      rw [htauN (r + (⌊tauCoordX tau z⌋ : ℂ))]
      simpa using honeM r
    rw [hfzr]
    exact hfr
  have hbounded : Bornology.IsBounded (Set.range f) := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨C, by rintro y ⟨z, rfl⟩; exact hglobal z⟩
  exact fun z w => hdiff.apply_eq_apply_of_bounded hbounded z w

/-- One regular pointing kills the scalar left by two-period entire-gauge rigidity. -/
theorem analyticOnNhd_eq_one_of_period_one_tau_of_pointed
    (f : ℂ → ℂ) (tau z0 : ℂ) (htau : 0 < tau.im)
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hone : Function.Periodic f 1) (htauPeriod : Function.Periodic f tau)
    (hpoint : f z0 = 1) :
    ∀ z, f z = 1 := by
  intro z
  exact (analyticOnNhd_constant_of_period_one_tau
    f tau htau hf hone htauPeriod z z0).trans hpoint

end

end GaloisForLFunctions
