import GaloisForLFunctions.HTGeometry.PolyCoeffDerivation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Derivation.Lie

/-!
# A derivation extends uniquely to a simple algebraic extension

Let `K` be a field of characteristic zero, `p` an irreducible polynomial over `K` and
`L = K[X]/(p)`.  A derivation `D` of `K` extends to `L` in exactly one way: the value at the root
is forced by differentiating the equation `p(α) = 0`,

`D' α = − p^D(α) / p'(α)`,

where `p^D` is `p` with `D` applied to its coefficients and `p'` is the formal derivative.  The
denominator is nonzero because an irreducible polynomial in characteristic zero is separable.

`adjoinRootDeriv` is the extension and `eq_adjoinRootDeriv` is its uniqueness.  The construction is
the concrete form of the formal étaleness of a separable algebraic extension; it is stated here
with the explicit shift so that the value at the root can be computed.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]
variable {p : K[X]}

/-- Evaluation at the root, as an `R`-algebra map. -/
noncomputable def rootEval (R : Type*) [CommRing R] [Algebra R K] (p : K[X]) :
    K[X] →ₐ[R] AdjoinRoot p :=
  (Polynomial.aeval (AdjoinRoot.root p)).restrictScalars R

@[simp]
theorem rootEval_apply (q : K[X]) :
    rootEval R p q = Polynomial.aeval (AdjoinRoot.root p) q := rfl

theorem rootEval_eq_mk (q : K[X]) : rootEval R p q = AdjoinRoot.mk p q := by
  rw [rootEval_apply, AdjoinRoot.aeval_eq]

@[simp]
theorem rootEval_self : rootEval R p p = 0 := by
  rw [rootEval_eq_mk, AdjoinRoot.mk_self]

theorem rootEval_derivative_ne_zero [CharZero K] [hp : Fact (Irreducible p)] :
    rootEval R p (derivative p) ≠ 0 := by
  intro h
  obtain ⟨a, b, hab⟩ := hp.out.separable
  have hone := congrArg (rootEval R p) hab
  rw [map_add, map_mul, map_mul, rootEval_self, h, map_one] at hone
  simp only [mul_zero, add_zero] at hone
  exact zero_ne_one hone

/-! ## The forced value at the root -/

variable [Fact (Irreducible p)]

/-- The value a derivation of `K` forces on the root of an irreducible polynomial. -/
noncomputable def rootShift (D : Derivation R K K) (p : K[X]) [Fact (Irreducible p)] :
    AdjoinRoot p :=
  -(rootEval R p (polyD D p)) / rootEval R p (derivative p)

/-- The extension, computed on a polynomial representative. -/
noncomputable def rootExtFun (D : Derivation R K K) (p : K[X]) [Fact (Irreducible p)]
    (q : K[X]) : AdjoinRoot p :=
  rootEval R p (polyD D q) + rootEval R p (derivative q) * rootShift D p

theorem rootExtFun_add (D : Derivation R K K) (q r : K[X]) :
    rootExtFun D p (q + r) = rootExtFun D p q + rootExtFun D p r := by
  simp only [rootExtFun, map_add, add_mul]
  ring

theorem rootExtFun_smul (D : Derivation R K K) (c : R) (q : K[X]) :
    rootExtFun D p (c • q) = c • rootExtFun D p q := by
  have h1 : (polyD D) (c • q) = c • (polyD D) q := map_smul (polyD D).toLinearMap c q
  have h2 : derivative (c • q) = c • derivative q := by
    rw [← algebraMap_smul (R := R) K c q, Polynomial.derivative_smul]
    exact algebraMap_smul K c (derivative q)
  rw [rootExtFun, rootExtFun, h1, h2, map_smul, map_smul, smul_add, smul_mul_assoc]

theorem rootExtFun_mul (D : Derivation R K K) (q r : K[X]) :
    rootExtFun D p (q * r)
      = rootEval R p q * rootExtFun D p r + rootEval R p r * rootExtFun D p q := by
  simp only [rootExtFun, Derivation.leibniz, smul_eq_mul, Polynomial.derivative_mul, map_add,
    map_mul]
  ring

/-- **The defining equation is preserved.** -/
theorem rootExtFun_self [CharZero K] (D : Derivation R K K) : rootExtFun D p p = 0 := by
  have hne : rootEval R p (derivative p) ≠ 0 := rootEval_derivative_ne_zero
  rw [rootExtFun, rootShift]
  field_simp
  ring

theorem rootExtFun_eq_zero_of_mem [CharZero K] (D : Derivation R K K) {x : K[X]}
    (hx : x ∈ Ideal.span ({p} : Set K[X])) : rootExtFun D p x = 0 := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [rootExtFun_mul, rootExtFun_self, rootEval_self]
  simp

/-- The extension, as an `R`-linear map on polynomial representatives. -/
noncomputable def rootExtLin (D : Derivation R K K) (p : K[X]) [Fact (Irreducible p)] :
    K[X] →ₗ[R] AdjoinRoot p where
  toFun := rootExtFun D p
  map_add' := rootExtFun_add D
  map_smul' c q := rootExtFun_smul D c q

theorem rootExtLin_ker [CharZero K] (D : Derivation R K K) :
    Submodule.restrictScalars R (Ideal.span ({p} : Set K[X])) ≤ LinearMap.ker (rootExtLin D p) :=
  fun _ hx => rootExtFun_eq_zero_of_mem D hx

/-- The extension, descended to the quotient. -/
noncomputable def adjoinRootDerivLin [CharZero K] (D : Derivation R K K) (p : K[X])
    [Fact (Irreducible p)] :
    AdjoinRoot p →ₗ[R] AdjoinRoot p :=
  (Submodule.liftQ (Submodule.restrictScalars R (Ideal.span ({p} : Set K[X])))
      (rootExtLin D p) (rootExtLin_ker D)).comp
    (show AdjoinRoot p →ₗ[R]
        (K[X] ⧸ Submodule.restrictScalars R (Ideal.span ({p} : Set K[X]))) from
      (Submodule.Quotient.restrictScalarsEquiv R
        (Ideal.span ({p} : Set K[X]))).symm.toLinearMap)

@[simp]
theorem adjoinRootDerivLin_mk [CharZero K] (D : Derivation R K K) (q : K[X]) :
    adjoinRootDerivLin D p (AdjoinRoot.mk p q) = rootExtFun D p q := rfl

/-- **The unique extension of a derivation of `K` to a simple algebraic extension.** -/
noncomputable def adjoinRootDeriv [CharZero K] (D : Derivation R K K) (p : K[X])
    [Fact (Irreducible p)] :
    Derivation R (AdjoinRoot p) (AdjoinRoot p) :=
  Derivation.mk' (adjoinRootDerivLin D p) <| by
    intro x y
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
    obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective y
    rw [← map_mul, adjoinRootDerivLin_mk, adjoinRootDerivLin_mk, adjoinRootDerivLin_mk,
      rootExtFun_mul, rootEval_eq_mk, rootEval_eq_mk]
    simp only [smul_eq_mul]

@[simp]
theorem adjoinRootDeriv_mk [CharZero K] (D : Derivation R K K) (q : K[X]) :
    adjoinRootDeriv D p (AdjoinRoot.mk p q) = rootExtFun D p q := rfl

/-- The extension really extends `D`. -/
@[simp]
theorem adjoinRootDeriv_algebraMap [CharZero K] (D : Derivation R K K) (a : K) :
    adjoinRootDeriv D p (algebraMap K (AdjoinRoot p) a)
      = algebraMap K (AdjoinRoot p) (D a) := by
  have hC : algebraMap K (AdjoinRoot p) a = AdjoinRoot.mk p (C a) := rfl
  rw [hC, adjoinRootDeriv_mk, rootExtFun, polyD_C, Polynomial.derivative_C, map_zero, zero_mul,
    add_zero, rootEval_eq_mk]
  rfl

/-- The value at the root is the forced shift. -/
@[simp]
theorem adjoinRootDeriv_root [CharZero K] (D : Derivation R K K) :
    adjoinRootDeriv D p (AdjoinRoot.root p) = rootShift D p := by
  have hX : (AdjoinRoot.root p) = AdjoinRoot.mk p X := rfl
  rw [hX, adjoinRootDeriv_mk, rootExtFun, polyD_X, map_zero, Polynomial.derivative_X, map_one,
    one_mul, zero_add]

/-! ## Uniqueness -/

/-- **The extension is unique.** Any derivation of the extension restricting to `D` on `K` is the
one constructed above; differentiating `p(α) = 0` forces the value at the root. -/
theorem eq_adjoinRootDeriv [CharZero K] (D : Derivation R K K)
    (D' : Derivation R (AdjoinRoot p) (AdjoinRoot p))
    (hD : ∀ a : K, D' (algebraMap K (AdjoinRoot p) a) = algebraMap K (AdjoinRoot p) (D a)) :
    D' = adjoinRootDeriv D p := by
  have hne : rootEval R p (derivative p) ≠ 0 := rootEval_derivative_ne_zero
  have hchain : ∀ q : K[X], D' (Polynomial.aeval (AdjoinRoot.root p) q)
      = Polynomial.aeval (AdjoinRoot.root p) (polyD D q)
        + Polynomial.aeval (AdjoinRoot.root p) (derivative q) * D' (AdjoinRoot.root p) :=
    fun q => aeval_polyD D D' (AdjoinRoot.root p) hD q
  have hroot : D' (AdjoinRoot.root p) = rootShift D p := by
    have h := hchain p
    rw [show Polynomial.aeval (AdjoinRoot.root p) p = 0 from rootEval_self (R := R), map_zero] at h
    rw [rootShift, eq_div_iff hne, rootEval_apply, rootEval_apply]
    linear_combination -h
  refine DFunLike.ext _ _ fun x => ?_
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [adjoinRootDeriv_mk, rootExtFun, ← rootEval_eq_mk (R := R), rootEval_apply, hchain q, hroot,
    rootEval_apply, rootEval_apply]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] {p : K[X]} [Fact (Irreducible p)]

@[simp]
theorem rootShift_zero : rootShift (0 : Derivation R K K) p = 0 := by
  rw [rootShift, polyD_zero, Derivation.zero_apply, map_zero, neg_zero, zero_div]

@[simp]
theorem adjoinRootDeriv_zero [CharZero K] :
    adjoinRootDeriv (0 : Derivation R K K) p = 0 := by
  refine DFunLike.ext _ _ fun x => ?_
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [adjoinRootDeriv_mk, rootExtFun, rootShift_zero, mul_zero, add_zero, polyD_zero,
    Derivation.zero_apply, map_zero, Derivation.zero_apply]

/-- **Commuting derivations extend to commuting derivations.** The commutator of the two
extensions is a derivation restricting to the commutator on the base, so uniqueness of the
extension of the zero derivation forces it to vanish. -/
theorem adjoinRootDeriv_commutator [CharZero K] (D₁ D₂ : Derivation R K K)
    (h : ⁅D₁, D₂⁆ = (0 : Derivation R K K)) :
    ⁅adjoinRootDeriv D₁ p, adjoinRootDeriv D₂ p⁆ = 0 := by
  have hres : ∀ a : K,
      ⁅adjoinRootDeriv D₁ p, adjoinRootDeriv D₂ p⁆ (algebraMap K (AdjoinRoot p) a)
        = algebraMap K (AdjoinRoot p) ((0 : Derivation R K K) a) := by
    intro a
    have hcomm : D₁ (D₂ a) - D₂ (D₁ a) = 0 := by
      rw [← Derivation.commutator_apply, h, Derivation.zero_apply]
    rw [Derivation.commutator_apply, adjoinRootDeriv_algebraMap, adjoinRootDeriv_algebraMap,
      adjoinRootDeriv_algebraMap, adjoinRootDeriv_algebraMap, ← map_sub, hcomm,
      Derivation.zero_apply]
  rw [eq_adjoinRootDeriv (0 : Derivation R K K) _ hres, adjoinRootDeriv_zero]

end GaloisForLFunctions.HTGeometry
