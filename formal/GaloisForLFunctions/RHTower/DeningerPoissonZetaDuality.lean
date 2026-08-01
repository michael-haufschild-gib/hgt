import GaloisForLFunctions.RHTower.DeningerArithmeticArakelovPoissonComplex
import GaloisForLFunctions.RHTower.DeningerArithmeticJetDeterminant

/-!
# Duality and determinant normalization of the Poisson--zeta complex

Two complementary statements about the assembled Poisson--zeta three-term complex.

First, the descended cup pairings are nondegenerate as soon as their chain-level inputs are: the
endpoint pairing `H⁰ × H² → R` is nondegenerate whenever the degree map is onto and the endpoint
sequence is exact, and the middle pairing `H¹ × H¹ → R` is nondegenerate whenever the source
pairing is nondegenerate modulo the image of the Poisson map.  Both are proved from the concrete
description of cocycles and boundaries of the assembled complex.

Second, the determinant normalization of the endpoint lines.  With `D₀(s) = s/2π` and
`D₂(s) = (s-1)/2π`, the product `D₀ D₂ Λ` is the entire symmetric function of the determinant
formula; it is the corpus `xi` rescaled by `2π²`, it is invariant under `s ↦ 1 - s`, and dividing
by the two endpoint determinants returns the completed zeta function.

* `deningerPoissonZetaPairH02_nondegenerate_left`, `..._right` : endpoint duality.
* `deningerPoissonZetaPairH11_nondegenerate` : middle duality.
* `deningerXiD_eq_xi`, `deningerXiD_one_sub`, `deningerCompletedZeta_eq_det_quotient`.
-/

namespace RHTower

noncomputable section

section PoissonZetaDuality

variable {R Hcap Hminus P D : Type*}
variable [Field R]
variable [AddCommGroup Hcap] [Module R Hcap]
variable [AddCommGroup Hminus] [Module R Hminus]
variable [AddCommGroup P] [Module R P]
variable [AddCommGroup D] [Module R D]

/-- **The endpoint pairing is nondegenerate in the degree-zero variable.**  A nonzero constant
pairs nontrivially with a divisor class of degree one. -/
theorem deningerPoissonZetaPairH02_nondegenerate_left
    (Z : Hcap →ₗ[R] Hminus) (principal : P →ₗ[R] D) (degree : D →ₗ[R] R)
    (psi : Hminus →ₗ[R] Hminus →ₗ[R] R)
    (hdegree : degree.comp principal = 0)
    (hpsiBoundary : ∀ f h, psi (Z f) h = 0)
    (hpsiSkew : ∀ h k, psi h k = -psi k h)
    (hZ : Function.Injective Z)
    (hdeg : Function.Surjective degree)
    {x : (deningerPoissonZetaComplex Z principal).H0} (hx : x ≠ 0) :
    ∃ z : (deningerPoissonZetaComplex Z principal).H2,
      (deningerPoissonZetaCupPairing Z principal degree psi hdegree hpsiBoundary
        hpsiSkew).pairH02 _ x z ≠ 0 := by
  obtain ⟨d, hd⟩ := hdeg 1
  refine ⟨Submodule.Quotient.mk d, ?_⟩
  rw [show (Submodule.Quotient.mk d : (deningerPoissonZetaComplex Z principal).H2)
      = (deningerPoissonZetaComplex Z principal).boundaries2.mkQ d from rfl,
    DeningerArithmeticThreeTermCupPairing.pairH02_mkQ]
  show (x : R × Hcap).1 * degree d ≠ 0
  rw [hd, mul_one]
  intro hcon
  refine hx ?_
  refine Subtype.ext ?_
  refine Prod.ext hcon ?_
  exact (deningerPoissonZeta_mem_cycles0_iff Z principal hZ (x : R × Hcap)).1 x.2

/-- **The endpoint pairing is nondegenerate in the degree-two variable.**  A divisor class is zero
exactly when its degree vanishes, so a nonzero class pairs nontrivially with the constant `1`. -/
theorem deningerPoissonZetaPairH02_nondegenerate_right
    (Z : Hcap →ₗ[R] Hminus) (principal : P →ₗ[R] D) (degree : D →ₗ[R] R)
    (psi : Hminus →ₗ[R] Hminus →ₗ[R] R)
    (hdegree : degree.comp principal = 0)
    (hpsiBoundary : ∀ f h, psi (Z f) h = 0)
    (hpsiSkew : ∀ h k, psi h k = -psi k h)
    (hZ : Function.Injective Z)
    (hexact : Function.Exact principal degree)
    {z : (deningerPoissonZetaComplex Z principal).H2} (hz : z ≠ 0) :
    ∃ x : (deningerPoissonZetaComplex Z principal).H0,
      (deningerPoissonZetaCupPairing Z principal degree psi hdegree hpsiBoundary
        hpsiSkew).pairH02 _ x z ≠ 0 := by
  obtain ⟨d, rfl⟩ :=
    Submodule.Quotient.mk_surjective (deningerPoissonZetaComplex Z principal).boundaries2 z
  have hdeg_ne : degree d ≠ 0 := by
    intro hcon
    refine hz ?_
    rw [(deningerPoissonZetaComplex Z principal).H2_mk_eq_zero_iff]
    rw [deningerPoissonZeta_boundaries2_eq_range]
    exact (hexact d).mp hcon
  refine ⟨⟨((1 : R), 0), (deningerPoissonZeta_mem_cycles0_iff Z principal hZ ((1 : R), 0)).2 rfl⟩,
    ?_⟩
  rw [show (Submodule.Quotient.mk d : (deningerPoissonZetaComplex Z principal).H2)
      = (deningerPoissonZetaComplex Z principal).boundaries2.mkQ d from rfl,
    DeningerArithmeticThreeTermCupPairing.pairH02_mkQ]
  show (1 : R) * degree d ≠ 0
  rw [one_mul]
  exact hdeg_ne

/-- **The middle pairing is nondegenerate.**  A degree-one class is nonzero exactly when its
generic component is not in the image of the Poisson map, and there the source pairing already
separates it. -/
theorem deningerPoissonZetaPairH11_nondegenerate
    (Z : Hcap →ₗ[R] Hminus) (principal : P →ₗ[R] D) (degree : D →ₗ[R] R)
    (psi : Hminus →ₗ[R] Hminus →ₗ[R] R)
    (hdegree : degree.comp principal = 0)
    (hpsiBoundary : ∀ f h, psi (Z f) h = 0)
    (hpsiSkew : ∀ h k, psi h k = -psi k h)
    (hprincipal : Function.Injective principal)
    (hpsiSeparating : ∀ h : Hminus, (∀ k : Hminus, psi h k = 0) → h ∈ LinearMap.range Z)
    {x : (deningerPoissonZetaComplex Z principal).H1} (hx : x ≠ 0) :
    ∃ y : (deningerPoissonZetaComplex Z principal).H1,
      (deningerPoissonZetaCupPairing Z principal degree psi hdegree hpsiBoundary
        hpsiSkew).pairH11 _ x y ≠ 0 := by
  obtain ⟨c, rfl⟩ :=
    Submodule.Quotient.mk_surjective
      ((deningerPoissonZetaComplex Z principal).boundaries1.comap
        (deningerPoissonZetaComplex Z principal).cycles1.subtype) x
  have hc2 : (c : Hminus × P).2 = 0 :=
    (deningerPoissonZeta_mem_cycles1_iff Z principal hprincipal (c : Hminus × P)).1 c.2
  have hnot : (c : Hminus × P).1 ∉ LinearMap.range Z := by
    intro ⟨f, hf⟩
    refine hx ?_
    rw [(deningerPoissonZetaComplex Z principal).H1_mk_eq_zero_iff]
    refine (deningerPoissonZeta_mem_boundaries1_iff Z principal (c : Hminus × P)).2 ⟨f, ?_⟩
    exact Prod.ext hf.symm hc2
  have hexists : ∃ k : Hminus, psi (c : Hminus × P).1 k ≠ 0 := by
    by_contra hcon
    refine hnot (hpsiSeparating _ fun k => ?_)
    by_contra hk
    exact hcon ⟨k, hk⟩
  obtain ⟨k, hk⟩ := hexists
  have hkcyc : ((k, 0) : Hminus × P) ∈ (deningerPoissonZetaComplex Z principal).cycles1 :=
    (deningerPoissonZeta_mem_cycles1_iff Z principal hprincipal (k, 0)).2 rfl
  refine ⟨Submodule.Quotient.mk ⟨(k, 0), hkcyc⟩, ?_⟩
  rw [show (Submodule.Quotient.mk ⟨(k, 0), hkcyc⟩ :
        (deningerPoissonZetaComplex Z principal).H1)
      = ((deningerPoissonZetaComplex Z principal).boundaries1.comap
        (deningerPoissonZetaComplex Z principal).cycles1.subtype).mkQ ⟨(k, 0), hkcyc⟩ from rfl,
    show (Submodule.Quotient.mk c : (deningerPoissonZetaComplex Z principal).H1)
      = ((deningerPoissonZetaComplex Z principal).boundaries1.comap
        (deningerPoissonZetaComplex Z principal).cycles1.subtype).mkQ c from rfl,
    DeningerArithmeticThreeTermCupPairing.pairH11_mkQ_mkQ]
  show psi k (c : Hminus × P).1 ≠ 0
  rw [hpsiSkew]
  exact neg_ne_zero.mpr hk

end PoissonZetaDuality

section EndpointDeterminants

open Complex

/-- The degree-zero endpoint determinant. -/
def deningerDet0 (s : ℂ) : ℂ := s / (2 * (Real.pi : ℂ))

/-- The degree-two endpoint determinant. -/
def deningerDet2 (s : ℂ) : ℂ := (s - 1) / (2 * (Real.pi : ℂ))

/-- The symmetric determinant normalization of the completed zeta function. -/
def deningerXiD (s : ℂ) : ℂ :=
  deningerDet0 s * deningerDet2 s * completedRiemannZeta s

theorem deningerPi_ne_zero : ((Real.pi : ℂ)) ≠ 0 := by
  exact_mod_cast Real.pi_ne_zero

theorem deningerDet0_ne_zero {s : ℂ} (hs : s ≠ 0) : deningerDet0 s ≠ 0 := by
  rw [deningerDet0]
  refine div_ne_zero hs ?_
  exact mul_ne_zero two_ne_zero deningerPi_ne_zero

theorem deningerDet2_ne_zero {s : ℂ} (hs : s ≠ 1) : deningerDet2 s ≠ 0 := by
  rw [deningerDet2]
  refine div_ne_zero (sub_ne_zero.mpr hs) ?_
  exact mul_ne_zero two_ne_zero deningerPi_ne_zero

/-- **The determinant normalization is the entire `xi` rescaled.**  The poles of the completed zeta
function at `0` and `1` are exactly cancelled by the two endpoint determinants. -/
theorem deningerXiD_eq_xi {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    deningerXiD s = xi s / (2 * (Real.pi : ℂ) ^ 2) := by
  have hpi := deningerPi_ne_zero
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  rw [deningerXiD, deningerDet0, deningerDet2, completedRiemannZeta_eq, xi]
  field_simp
  ring

/-- **The functional equation of the determinant normalization.** -/
theorem deningerXiD_one_sub (s : ℂ) : deningerXiD (1 - s) = deningerXiD s := by
  rw [deningerXiD, deningerXiD, deningerDet0, deningerDet2, deningerDet0, deningerDet2,
    completedRiemannZeta_one_sub]
  ring

/-- **The determinant quotient formula.**  Dividing the symmetric determinant by the two endpoint
determinants returns the completed zeta function. -/
theorem deningerCompletedZeta_eq_det_quotient {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    completedRiemannZeta s = deningerXiD s / (deningerDet0 s * deningerDet2 s) := by
  rw [deningerXiD, mul_comm (deningerDet0 s * deningerDet2 s) (completedRiemannZeta s),
    mul_div_assoc, div_self (mul_ne_zero (deningerDet0_ne_zero hs0) (deningerDet2_ne_zero hs1)),
    mul_one]

/-- **The middle determinant is the source jet determinant.**  The regularized determinant of the
source jet Frobenius, in Deninger's uncentered coordinate, is `xi`, hence it is the symmetric
determinant normalization up to the fixed scalar `2π²`. -/
theorem deningerXiD_eq_jetDeterminant {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    deningerXiD s
      = deningerArithmeticJetUncenteredRegularizedDeterminant s / (2 * (Real.pi : ℂ) ^ 2) := by
  rw [deningerArithmeticJetUncenteredRegularizedDeterminant_eq_xi, deningerXiD_eq_xi hs0 hs1]

/-- The completed zeta function is the source jet determinant divided by the two endpoint
determinants. -/
theorem deningerCompletedZeta_eq_jetDeterminant_quotient {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    completedRiemannZeta s
      = (deningerArithmeticJetUncenteredRegularizedDeterminant s / (2 * (Real.pi : ℂ) ^ 2))
        / (deningerDet0 s * deningerDet2 s) := by
  rw [← deningerXiD_eq_jetDeterminant hs0 hs1]
  exact deningerCompletedZeta_eq_det_quotient hs0 hs1

end EndpointDeterminants

end

end RHTower
