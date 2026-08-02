import GaloisForLFunctions.HTGeometry.AffineBaseJetGauge
import GaloisForLFunctions.HTGeometry.DifferentialIndependentTopEquiv
import GaloisForLFunctions.HTGeometry.KolchinExchangeGaugeObstruction
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Scalar isotropy of a freely generated differential family
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F K ι : Type*} [Field F] [Field K]
  [Algebra F K] [Differential F] [Differential K]
  [DifferentialAlgebra F K]

/-- Simultaneous nonzero base-scalar rescaling of every member of a
freely generating differential family extends to an automorphism of
the generated field. -/
def differentialIndependentFamilyScaleEquiv
    (x : ι → K) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤)
    (u : Fˣ) : K ≃ₐ[F] K := by
  let y : ι → K := fun i =>
    algebraMap F K (u : F) * x i
  have hy : DifferentialIndependent F y := by
    exact hx.mulBase (fun _ => (u : F))
      (fun _ => Units.ne_zero u)
  have hygen :
      differentialAdjoin F (Set.range y) = ⊤ := by
    rw [show y = fun i =>
        algebraMap F K (u : F) * x i by rfl,
      differentialAdjoin_range_mulBase_eq
        x (fun _ => (u : F)) (fun _ => Units.ne_zero u),
      hgen]
  exact GaloisForLFunctions.differentialIndependentTopAlgEquiv
    x y hx hy hgen hygen

@[simp]
theorem differentialIndependentFamilyScaleEquiv_apply
    (x : ι → K) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤)
    (u : Fˣ) (i : ι) :
    differentialIndependentFamilyScaleEquiv x hx hgen u (x i) =
      algebraMap F K (u : F) * x i := by
  let y : ι → K := fun j =>
    algebraMap F K (u : F) * x j
  have hy : DifferentialIndependent F y := by
    exact hx.mulBase (fun _ => (u : F))
      (fun _ => Units.ne_zero u)
  have hygen :
      differentialAdjoin F (Set.range y) = ⊤ := by
    rw [show y = fun j =>
        algebraMap F K (u : F) * x j by rfl,
      differentialAdjoin_range_mulBase_eq
        x (fun _ => (u : F)) (fun _ => Units.ne_zero u),
      hgen]
  exact GaloisForLFunctions.differentialIndependentTopAlgEquiv_apply
    x y hx hy hgen hygen i

theorem differentialIndependentFamilyScaleEquiv_deriv
    (x : ι → K) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤)
    (u : Fˣ) (z : K) :
    differentialIndependentFamilyScaleEquiv x hx hgen u z′ =
      (differentialIndependentFamilyScaleEquiv
        x hx hgen u z)′ := by
  let y : ι → K := fun j =>
    algebraMap F K (u : F) * x j
  have hy : DifferentialIndependent F y := by
    exact hx.mulBase (fun _ => (u : F))
      (fun _ => Units.ne_zero u)
  have hygen :
      differentialAdjoin F (Set.range y) = ⊤ := by
    rw [show y = fun j =>
        algebraMap F K (u : F) * x j by rfl,
      differentialAdjoin_range_mulBase_eq
        x (fun _ => (u : F)) (fun _ => Units.ne_zero u),
      hgen]
  exact GaloisForLFunctions.differentialIndependentTopAlgEquiv_deriv
    x y hx hy hgen hygen z

/-- Differential-automorphism package for simultaneous scalar
rescaling of a free differential palette. -/
def differentialIndependentFamilyScaleDifferentialAlgEquiv
    (x : ι → K) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤)
    (u : Fˣ) : DifferentialAlgEquiv F K where
  toAlgEquiv :=
    differentialIndependentFamilyScaleEquiv x hx hgen u
  map_deriv' :=
    differentialIndependentFamilyScaleEquiv_deriv
      x hx hgen u

@[simp]
theorem
    differentialIndependentFamilyScaleDifferentialAlgEquiv_apply
    (x : ι → K) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤)
    (u : Fˣ) (i : ι) :
    (differentialIndependentFamilyScaleDifferentialAlgEquiv
      x hx hgen u).toAlgEquiv (x i) =
        algebraMap F K (u : F) * x i :=
  differentialIndependentFamilyScaleEquiv_apply
    x hx hgen u i

/-- Simultaneous scale commutes with every differential
automorphism which permutes the freely generating palette, fixes the
chosen scalar, and commutes with scale on the differential base.
This formulation includes translations which act nontrivially on
the rational-coordinate base. -/
theorem
    differentialIndependentFamilyScale_commutes_of_permutes
    {C G : Type*} [Field C] [Algebra C K]
    (x : ι → K) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤)
    (u : Fˣ) (τ : G → DifferentialAlgEquiv C K)
    (act : G → ι → ι)
    (hτ : ∀ g i, (τ g).toAlgEquiv (x i) = x (act g i))
    (hscalar : ∀ g,
      (τ g).toAlgEquiv (algebraMap F K (u : F)) =
        algebraMap F K (u : F))
    (hbase : ∀ g a,
      (differentialIndependentFamilyScaleDifferentialAlgEquiv
          x hx hgen u).toAlgEquiv
          ((τ g).toAlgEquiv (algebraMap F K a)) =
        (τ g).toAlgEquiv (algebraMap F K a))
    (g : G) (z : K) :
    let σ :=
      differentialIndependentFamilyScaleDifferentialAlgEquiv
        x hx hgen u
    σ.toAlgEquiv ((τ g).toAlgEquiv z) =
      (τ g).toAlgEquiv (σ.toAlgEquiv z) := by
  dsimp only
  let σ :=
    differentialIndependentFamilyScaleDifferentialAlgEquiv
      x hx hgen u
  let p : ∀ y : K,
      y ∈ differentialAdjoin F (Set.range x) → Prop :=
    fun y _ =>
      σ.toAlgEquiv ((τ g).toAlgEquiv y) =
        (τ g).toAlgEquiv (σ.toAlgEquiv y)
  have hz : z ∈ differentialAdjoin F (Set.range x) := by
    rw [hgen]
    trivial
  change p z hz
  refine IntermediateField.adjoin_induction F
    (p := p) ?_ ?_ ?_ ?_ ?_ hz
  · rintro y ⟨y₀, ⟨i, rfl⟩, n, rfl⟩
    show σ.toAlgEquiv
        ((τ g).toAlgEquiv (differentialJet n (x i))) =
      (τ g).toAlgEquiv
        (σ.toAlgEquiv (differentialJet n (x i)))
    rw [(τ g).map_differentialJet, hτ,
      σ.map_differentialJet,
      differentialIndependentFamilyScaleDifferentialAlgEquiv_apply,
      σ.map_differentialJet,
      differentialIndependentFamilyScaleDifferentialAlgEquiv_apply,
      (τ g).map_differentialJet, map_mul,
      hscalar, hτ]
  · intro c
    show σ.toAlgEquiv
        ((τ g).toAlgEquiv (algebraMap F K c)) =
      (τ g).toAlgEquiv
        (σ.toAlgEquiv (algebraMap F K c))
    rw [σ.toAlgEquiv.commutes]
    exact hbase g c
  · intro y w hy hw hpy hpw
    show σ.toAlgEquiv ((τ g).toAlgEquiv (y + w)) =
      (τ g).toAlgEquiv (σ.toAlgEquiv (y + w))
    simpa only [map_add] using congrArg₂ (· + ·) hpy hpw
  · intro y hy hpy
    show σ.toAlgEquiv ((τ g).toAlgEquiv y⁻¹) =
      (τ g).toAlgEquiv (σ.toAlgEquiv y⁻¹)
    simpa only [map_inv₀] using congrArg Inv.inv hpy
  · intro y w hy hw hpy hpw
    show σ.toAlgEquiv ((τ g).toAlgEquiv (y * w)) =
      (τ g).toAlgEquiv (σ.toAlgEquiv (y * w))
    simpa only [map_mul] using congrArg₂ (· * ·) hpy hpw

/-- Complex sesquilinear form, linear in the first variable and
conjugate-linear in the second. -/
abbrev ComplexSesquilinearForm
    (V : Type*) [AddCommMonoid V] [Module ℂ V] :=
  V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ

/-- A complex sesquilinear form is determined by its diagonal. -/
theorem complexSesquilinearForm_eq_zero_of_diagonal_eq_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : ComplexSesquilinearForm V)
    (hdiag : ∀ v : V, B v v = 0) :
    B = 0 := by
  ext u v
  have hplus := hdiag (u + v)
  have hI := hdiag (u + Complex.I • v)
  have huu := hdiag u
  have hvv := hdiag v
  simp only [map_add, LinearMap.add_apply, map_smul,
    LinearMap.smul_apply, LinearMap.map_smulₛₗ,
    smul_eq_mul] at hplus hI
  rw [huu, hvv] at hplus hI
  have hstarI :
      (starRingEnd ℂ) Complex.I = -Complex.I :=
    Complex.conj_I
  rw [hstarI] at hI
  have hsum : B u v + B v u = 0 := by
    linear_combination hplus
  have hdiff :
      -Complex.I * B u v + Complex.I * B v u = 0 := by
    linear_combination hI
  have hvu : B v u = -B u v := by
    linear_combination hsum
  rw [hvu] at hdiff
  have hmul : (-2 * Complex.I) * B u v = 0 := by
    linear_combination hdiff
  exact (mul_eq_zero.mp hmul).resolve_left
    (by norm_num [Complex.I_ne_zero])

/-- Invariance under simultaneous scaling by `2` forces every
complex sesquilinear form to vanish. -/
theorem complexSesquilinearForm_eq_zero_of_scaleTwo_invariant
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : ComplexSesquilinearForm V)
    (hscale : ∀ v : V,
      B ((2 : ℂ) • v) ((2 : ℂ) • v) = B v v) :
    B = 0 := by
  apply complexSesquilinearForm_eq_zero_of_diagonal_eq_zero B
  intro v
  have h := hscale v
  simp only [map_smul, LinearMap.smul_apply,
    LinearMap.map_smulₛₗ, smul_eq_mul, map_ofNat] at h
  have hthree : (3 : ℂ) * B v v = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp hthree).resolve_left (by norm_num)

end

end GaloisForLFunctions.HTGeometry
