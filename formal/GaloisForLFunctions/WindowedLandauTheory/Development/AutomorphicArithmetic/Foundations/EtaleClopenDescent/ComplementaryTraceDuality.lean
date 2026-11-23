import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ComplementaryRegularForms
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TracedLaurentResidue

/-! The scaled logarithmic trace pairing detects regularity of
complementary forms on a normalized projective intersection. -/

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

omit [CharZero k] in
private theorem normalizedIntersection_properties (h : IsFinCover k E x)
    {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) :
    IsNoetherianRing (rB k E x I) ∧ IsIntegrallyClosed (rB k E x I) ∧
      IsFractionRing (rB k E x I) E ∧ Algebra.Smooth k (rB k E x I) := by
  let A := rA k x {i}
  let B := rB k E x {i}
  let T := rB k E x I
  let u : B := algebraMap A (integralClosure A E) (chartDenominator k x I i)
  letI : IsFractionRing A F := h.pd.isFractionRing_rA i
  letI := h.fin
  letI := h.sep
  let e := h.pd.chartPolynomialEquiv i
  letI : IsNoetherianRing A := isNoetherianRing_of_ringEquiv _ e.toRingEquiv
  letI : IsIntegrallyClosed (MvPolynomial (Fin d) k) :=
    UpperTheory.Cb.isIntegrallyClosed_fin_polynomialRing k d
  letI : IsIntegrallyClosed A := .of_equiv e.toRingEquiv
  letI : IsNoetherianRing B := integralClosure.isNoetherianRing (K := F) (L := E)
  letI : IsIntegrallyClosed B := integralClosure.isIntegrallyClosedOfFiniteExtension F
  letI : IsFractionRing B E := integralClosure.isFractionRing_of_finite_extension F E
  letI : Algebra.Smooth k B := h.smooth i
  letI : Algebra B T := normalizedIntersectionAlgebra (k := k) (x := x) (E := E) hi
  letI : IsScalarTower B T E := normalizedIntersection_tower (k := k) (x := x) (E := E) hi
  letI : IsScalarTower k B T := .of_algebraMap_eq fun _ => rfl
  letI : IsLocalization.Away u T := normalizedIntersection_isLocalization (E := E) h.pd hi
  letI : Algebra.Smooth B T := .of_isLocalization_Away u
  refine ⟨IsLocalization.isNoetherianRing (Submonoid.powers u) T inferInstance, ?_,
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers u) T E,
    Algebra.Smooth.comp k B T⟩
  apply isIntegrallyClosed_of_isLocalization T (Submonoid.powers u)
  intro v hv
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hv'
  have hunit := IsLocalization.map_units T (⟨v, hv⟩ : Submonoid.powers u)
  exact hunit.ne_zero ((congrArg (algebraMap B T) hv').trans (map_zero _))

private theorem regular_top_of_logarithmic_trace (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ)
    {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I)
    (w : DR k E) (hw : w ∈ ⋀[E]^d Ω[E⁄k])
    (htrace : ∀ v : rB k E x I,
      (∏ j, x i / x j) * Algebra.trace F E ((v : E) * τ w) ∈ rA k x I) :
    w ∈ omB k E (rB k E x I) d := by
  have hwvol := h.topDegreeForms.2.1 τ hτ w hw
  let c : F := ∏ j, x i / x j
  let f : F := ∏ j, x j / x i
  have hcf : c * f = 1 := by
    change (∏ j, x i / x j) * (∏ j, x j / x i) = 1
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun j _ => by
      rw [div_mul_div_cancel₀ (h.pd.ne j), div_self (h.pd.ne i)]
  let z := algebraMap F E c * τ w
  have hz : ∀ v : rB k E x I, Algebra.trace F E (z * (v : E)) ∈ rA k x I := by
    intro v
    have hscale : z * (v : E) = c • ((v : E) * τ w) := by
      rw [Algebra.smul_def]
      change algebraMap F E c * τ w * (v : E) = _
      rw [mul_assoc, mul_comm (τ w)]
    rw [hscale, map_smul, smul_eq_mul]
    exact htrace v
  have hreg := (h.intersection_trace_dual_iff hi z).mp hz
  obtain ⟨ε, hε⟩ := volume_chart_change (K := E) h.pd i
  change z • (ExteriorAlgebra.ιMulti E d fun j =>
    D k E (algebraMap F E (x (i.succAbove j) / x i))) ∈ _ at hreg
  have hzf : z * algebraMap F E f = τ w := by
    change algebraMap F E c * τ w * algebraMap F E f = τ w
    rw [mul_right_comm, ← map_mul, hcf, map_one, one_mul]
  rw [hε, Units.smul_def, ← Int.cast_smul_eq_zsmul E,
    smul_comm z (((ε : ℤ) : E)), smul_smul z (algebraMap F E f), hzf, ← hwvol,
    Int.cast_smul_eq_zsmul] at hreg
  simpa only [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul] using
    zsmul_mem hreg (ε : ℤ)

/-- A complementary rational form is regular if every trace pairing
with a regular form is integral in affine-volume coordinates. -/
theorem IsFinCover.complementary_trace_dual_iff (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ)
    {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I)
    {p q : ℕ} (hpq : p + q = d) (y : ExteriorDifferentials k E q) :
    (∀ a ∈ omB k E (rB k E x I) p,
      (∏ j, x i / x j) * Algebra.trace F E (τ (a * (y : DR k E))) ∈ rA k x I) ↔
      (y : DR k E) ∈ omB k E (rB k E x I) q := by
  subst d
  constructor
  · intro hy
    let T := rB k E x I
    obtain ⟨hn, hcl, hf, hsm⟩ := normalizedIntersection_properties h hi
    letI : IsNoetherianRing T := hn
    letI : IsIntegrallyClosed T := hcl
    letI : IsFractionRing T E := hf
    letI : Algebra.Smooth k T := hsm
    obtain ⟨b, _⟩ := h.exists_coordinateDifferentialBasis
    refine mem_omB_of_complementary_wedge_regular T b y fun a ha => ?_
    have ha' : a ∈ ⋀[E]^p Ω[E⁄k] := omB_le_degree (B := T) (p := p) ha
    have hw : a * (y : DR k E) ∈ ⋀[E]^(p + q) Ω[E⁄k] :=
      SetLike.mul_mem_graded ha' y.property
    refine regular_top_of_logarithmic_trace h τ hτ hi _ hw (fun v => ?_)
    have hv := hy ((v : E) • a) (smul_mem_omB (B := T) (p := p) v.property ha)
    rwa [smul_mul_assoc, map_smul, smul_eq_mul] at hv
  · intro hy a ha
    exact h.trace_logarithmic_coefficient_mem_chart τ hτ hi _
      (mul_mem_omB (B := rB k E x I) (p := p) (q := q) ha hy)

end GlobalTheory.PD
