import GaloisForLFunctions.HTGeometry.FreeCoordinateAlgebraicConstantDescent
import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import GaloisForLFunctions.HTGeometry.TensorEigenvectorSpecialization
import GaloisForLFunctions.HTGeometry.TensorProductAlgClosedFieldDomain

/-!
# Algebraic descent of rank-one derivation eigenvectors

If an algebraic element is an eigenvector for a derivation extending one on the base field, its
minimal polynomial's constant coefficient is an eigenvector whose weight is multiplied by the
minimal-polynomial degree.  For a product function field this coefficient is a tensor fraction, so
finite-support specialization descends it to one factor.  Algebraic closedness then extracts the
required root and divides the multiplied eigenvalue back to its original weight.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential TensorProduct

noncomputable section

/-- A derivation with values in its source ring, transported through an algebra map to a larger
codomain. -/
def derivationAlgebraMap
    (C A F : Type*) [CommRing C] [CommRing A] [CommRing F]
    [Algebra C A] [Algebra A F] [Algebra C F] [IsScalarTower C A F]
    (D : Derivation C A A) : Derivation C A F :=
  Derivation.mk'
    ((IsScalarTower.toAlgHom C A F).toLinearMap.comp D.toLinearMap) (by
      intro x y
      calc
        ((IsScalarTower.toAlgHom C A F).toLinearMap.comp D.toLinearMap) (x * y) =
            algebraMap A F (D (x * y)) := rfl
        _ = algebraMap A F (x * D y + y * D x) := by
          congr 1
          simpa [Algebra.smul_def] using D.leibniz x y
        _ = x • ((IsScalarTower.toAlgHom C A F).toLinearMap.comp D.toLinearMap) y +
            y • ((IsScalarTower.toAlgHom C A F).toLinearMap.comp D.toLinearMap) x := by
          simp [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
            Algebra.smul_def, IsScalarTower.toAlgHom])

@[simp]
theorem derivationAlgebraMap_apply
    (C A F : Type*) [CommRing C] [CommRing A] [CommRing F]
    [Algebra C A] [Algebra A F] [Algebra C F] [IsScalarTower C A F]
    (D : Derivation C A A) (x : A) :
    derivationAlgebraMap C A F D x = algebraMap A F (D x) :=
  rfl

/-- Quotient-rule extension to a fraction field of the derivation acting on the left tensor
factor.  The tensor product is a domain because both factors are fields over an algebraically
closed base. -/
def tensorFieldsFractionDerivation
    (C A B K : Type*) [Field C] [IsAlgClosed C] [Field A] [Field B]
    [Algebra C A] [Algebra C B]
    [Field K] [Algebra (A ⊗[C] B) K] [Algebra C K]
    [IsScalarTower C (A ⊗[C] B) K] [IsFractionRing (A ⊗[C] B) K]
    (D : Derivation C A A) : Derivation C K K := by
  letI : IsDomain (A ⊗[C] B) := isDomain_tensorProduct_of_fields
  exact GaloisForLFunctions.fractionRingDerivation
    (derivationAlgebraMap C (A ⊗[C] B) K
      (tensorLeftDerivation C A B D))

/-- The constant coefficient of the minimal polynomial of an algebraic derivation eigenvector is
an eigenvector with weight multiplied by the minimal-polynomial degree. -/
theorem minpoly_constantCoeff_deriv_of_eigenvector
    {C K L : Type*} [Field C] [Field K] [CharZero K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L] [IsScalarTower C K L]
    (DK : Derivation C K K) (DL : Derivation C L L)
    (hmap : ∀ x : K, DL (algebraMap K L x) = algebraMap K L (DK x))
    {u : L} (hu : IsAlgebraic K u) (q : K)
    (hDu : DL u = algebraMap K L q * u) :
    DK ((minpoly K u).coeff 0) =
      ((minpoly K u).natDegree : K) * q * (minpoly K u).coeff 0 := by
  classical
  letI : Differential K := differentialOfDerivation DK
  letI : Differential L := differentialOfDerivation DL
  let p : Polynomial K := minpoly K u
  let P : Polynomial L := p.map (algebraMap K L)
  let Q : Polynomial K := coeffDeriv p +
    Polynomial.C q *
      (Polynomial.X * p.derivative - Polynomial.C (p.natDegree : K) * p)
  have hp0 : p ≠ 0 := minpoly.ne_zero hu.isIntegral
  have hpmonic : p.Monic := minpoly.monic hu.isIntegral
  have hPeval : Polynomial.eval u P = 0 := by
    simp only [P, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval K u
  have hcoeffmap : (coeffDeriv p).map (algebraMap K L) = coeffDeriv P := by
    ext n
    rw [Polynomial.coeff_map, coeffDeriv_coeff, coeffDeriv_coeff,
      show P.coeff n = (p.map (algebraMap K L)).coeff n from rfl,
      Polynomial.coeff_map]
    exact (hmap _).symm
  have hQmap : Q.map (algebraMap K L) = coeffDeriv P +
      Polynomial.C (algebraMap K L q) *
        (Polynomial.X * P.derivative -
          Polynomial.C (algebraMap K L (p.natDegree : K)) * P) := by
    simp only [Q, Polynomial.map_add, hcoeffmap, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_sub, Polynomial.map_X]
    rw [show P = p.map (algebraMap K L) from rfl,
      Polynomial.derivative_map]
  have hQeval : Polynomial.aeval u Q = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hQmap]
    have hchain := deriv_eval P u
    rw [hPeval] at hchain
    change DL 0 = Polynomial.eval u (coeffDeriv P) +
      Polynomial.eval u (Polynomial.derivative P) * DL u at hchain
    rw [map_zero, hDu] at hchain
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
      hPeval, mul_zero, sub_zero]
    linear_combination -hchain
  have hQ0 : Q = 0 := by
    by_contra hQne
    have hle := minpoly.degree_le_of_ne_zero K u hQne hQeval
    have hlt : Q.degree < (p.natDegree : WithBot ℕ) := by
      rw [Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      simp only [Q, Polynomial.coeff_add, coeffDeriv_coeff,
        Polynomial.coeff_C_mul, Polynomial.coeff_sub]
      rcases eq_or_lt_of_le hm with rfl | hlt
      · have hnpos : 0 < p.natDegree := minpoly.natDegree_pos hu.isIntegral
        obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
        have hlead : p.coeff d.succ = 1 := by
          rw [← hd]
          exact hpmonic.coeff_natDegree
        rw [hd, Polynomial.coeff_X_mul, Polynomial.coeff_derivative, hlead]
        simp
      · have hcoeff : p.coeff m = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt hlt
        have hmpos : 0 < m := lt_of_lt_of_le (minpoly.natDegree_pos hu.isIntegral) hm
        obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
        rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, hcoeff]
        simp
    rw [Polynomial.degree_eq_natDegree hp0] at hle
    exact (not_le_of_gt hlt) hle
  have hcoeff0 := congrArg (fun r : Polynomial K => r.coeff 0) hQ0
  simp only [Q, Polynomial.coeff_add, coeffDeriv_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_zero] at hcoeff0
  have hX0 : (Polynomial.X * p.derivative).coeff 0 = 0 := by simp
  rw [hX0] at hcoeff0
  change DK (p.coeff 0) + q *
    (0 - (p.natDegree : K) * p.coeff 0) = 0 at hcoeff0
  change DK (p.coeff 0) = (p.natDegree : K) * q * p.coeff 0
  linear_combination hcoeff0

/-- A nonzero algebraic element has a minimal polynomial with nonzero constant coefficient. -/
theorem minpoly_constantCoeff_ne_zero
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {u : L} (hu : IsAlgebraic K u) (hu0 : u ≠ 0) :
    (minpoly K u).coeff 0 ≠ 0 := by
  intro h0
  have hdvd : Polynomial.X ∣ minpoly K u := Polynomial.X_dvd_iff.2 h0
  have hassoc : Associated (Polynomial.X : Polynomial K) (minpoly K u) :=
    Polynomial.irreducible_X.associated_of_dvd (minpoly.irreducible hu.isIntegral) hdvd
  have hXeq : (Polynomial.X : Polynomial K) = minpoly K u :=
    Polynomial.eq_of_monic_of_associated Polynomial.monic_X
      (minpoly.monic hu.isIntegral) hassoc
  have hev := minpoly.aeval K u
  rw [← hXeq] at hev
  exact hu0 (by simpa using hev)

/-- **Algebraic tensor-fraction eigenvector descent.**  Let `K` be a fraction field of
`A ⊗[C] B`, and let an algebraic extension contain a nonzero eigenvector for the extension of the
left-factor derivation.  If `C` and `A` are algebraically closed of characteristic zero, then the
same eigenvalue already has a nonzero eigenvector in `A`.

The proof applies the minimal-polynomial coefficient law, specializes its nonzero tensor-fraction
constant coefficient, and extracts a root in `A`. -/
theorem exists_left_eigenvector_of_algebraic_tensor_fraction
    (C A B K L : Type*)
    [Field C] [IsAlgClosed C] [CharZero C]
    [Field A] [IsAlgClosed A] [Field B]
    [Algebra C A] [Algebra C B]
    [Field K] [Algebra (A ⊗[C] B) K] [Algebra C K]
    [IsScalarTower C (A ⊗[C] B) K] [IsFractionRing (A ⊗[C] B) K]
    [Field L] [Algebra C L] [Algebra K L] [IsScalarTower C K L]
    (D : Derivation C A A) (DL : Derivation C L L)
    (hmap : ∀ x : K,
      DL (algebraMap K L x) =
        algebraMap K L (tensorFieldsFractionDerivation C A B K D x))
    (q : A) {u : L} (hu : IsAlgebraic K u) (hu0 : u ≠ 0)
    (hDu : DL u =
      algebraMap K L
        (algebraMap (A ⊗[C] B) K (q ⊗ₜ[C] (1 : B))) * u) :
    ∃ v : A, v ≠ 0 ∧ D v = q * v := by
  letI : IsDomain (A ⊗[C] B) := isDomain_tensorProduct_of_fields
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap C K).injective
  letI : CharZero A := charZero_of_injective_algebraMap (algebraMap C A).injective
  let T := A ⊗[C] B
  let DT : Derivation C T T := tensorLeftDerivation C A B D
  let DK : Derivation C K K := tensorFieldsFractionDerivation C A B K D
  let qK : K := algebraMap T K (q ⊗ₜ[C] (1 : B))
  let p : Polynomial K := minpoly K u
  let n : ℕ := p.natDegree
  have hn : 0 < n := minpoly.natDegree_pos hu.isIntegral
  have hc0 : p.coeff 0 ≠ 0 := minpoly_constantCoeff_ne_zero hu hu0
  have hcEig : DK (p.coeff 0) = (n : K) * qK * p.coeff 0 := by
    exact minpoly_constantCoeff_deriv_of_eigenvector DK DL hmap hu qK hDu
  obtain ⟨N, S, hSnd, hfrac⟩ := IsFractionRing.div_surjective T (p.coeff 0)
  have hS : S ≠ 0 := nonZeroDivisors.ne_zero hSnd
  have hμS : algebraMap T K S ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hSnd
  have hN : N ≠ 0 := by
    intro hzero
    apply hc0
    rw [hzero, map_zero, zero_div] at hfrac
    exact hfrac.symm
  have hNS : p.coeff 0 * algebraMap T K S = algebraMap T K N := by
    calc
      p.coeff 0 * algebraMap T K S =
          (algebraMap T K N / algebraMap T K S) * algebraMap T K S := by rw [hfrac]
      _ = algebraMap T K N := div_mul_cancel₀ _ hμS
  have hdNS := congr_arg DK hNS
  have hdNS' : p.coeff 0 * DK (algebraMap T K S) +
        algebraMap T K S * DK (p.coeff 0) = DK (algebraMap T K N) := by
    simpa only [Derivation.leibniz, smul_eq_mul] using hdNS
  have hDKmap (X : T) : DK (algebraMap T K X) = algebraMap T K (DT X) := by
    exact GaloisForLFunctions.fractionRingDerivation_algebraMap
      (derivationAlgebraMap C T K DT) X
  rw [hDKmap, hDKmap] at hdNS'
  have hidentity : DT N * S - N * DT S =
      (((n : A) * q) ⊗ₜ[C] (1 : B)) * N * S := by
    apply IsFractionRing.injective T K
    simp only [map_sub, map_mul]
    change algebraMap T K (DT N) * algebraMap T K S -
        algebraMap T K N * algebraMap T K (DT S) =
      algebraMap T K (((n : A) * q) ⊗ₜ[C] (1 : B)) *
        algebraMap T K N * algebraMap T K S
    have hqmap : algebraMap T K (((n : A) * q) ⊗ₜ[C] (1 : B)) =
        (n : K) * qK := by
      change algebraMap T K (((n : A) * q) ⊗ₜ[C] (1 : B)) =
        (n : K) * algebraMap T K (q ⊗ₜ[C] (1 : B))
      change algebraMap T K
          ((Algebra.TensorProduct.includeLeft : A →ₐ[C] T) ((n : A) * q)) =
        (n : K) * algebraMap T K
          ((Algebra.TensorProduct.includeLeft : A →ₐ[C] T) q)
      let f : A →+* K := (algebraMap T K).comp
        (Algebra.TensorProduct.includeLeft : A →ₐ[C] T).toRingHom
      change f ((n : A) * q) = (n : K) * f q
      rw [map_mul, map_natCast]
    rw [hqmap]
    calc
      algebraMap T K (DT N) * algebraMap T K S -
          algebraMap T K N * algebraMap T K (DT S) =
        (p.coeff 0 * algebraMap T K (DT S) +
            algebraMap T K S * DK (p.coeff 0)) * algebraMap T K S -
          (p.coeff 0 * algebraMap T K S) * algebraMap T K (DT S) := by
            rw [hdNS', hNS]
      _ = (n : K) * qK * (p.coeff 0 * algebraMap T K S) *
          algebraMap T K S := by rw [hcEig]; ring
      _ = (n : K) * qK * algebraMap T K N * algebraMap T K S := by rw [hNS]
  obtain ⟨w, hw0, hw⟩ :=
    exists_left_eigenvector_of_arbitrary_right_tensor_fraction_identity
      C A B D ((n : A) * q) N S hN hS hidentity
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq w hn
  have hv0 : v ≠ 0 := by
    intro hvzero
    apply hw0
    rw [← hv, hvzero, zero_pow hn.ne']
  refine ⟨v, hv0, ?_⟩
  have hpow := congr_arg D hv
  have hpow' : (n : A) * v ^ (n - 1) * D v =
      (n : A) * q * v ^ n := by
    rw [D.leibniz_pow] at hpow
    rw [hw, ← hv] at hpow
    simpa [nsmul_eq_mul, mul_assoc] using hpow
  have hn0 : (n : A) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hvpow0 : v ^ (n - 1) ≠ 0 := pow_ne_zero _ hv0
  have hcancel : (n : A) * v ^ (n - 1) * (D v - q * v) = 0 := by
    rw [mul_sub]
    calc
      (n : A) * v ^ (n - 1) * D v -
          (n : A) * v ^ (n - 1) * (q * v) =
        (n : A) * v ^ (n - 1) * D v - (n : A) * q * v ^ n := by
          have hvp : v ^ (n - 1) * v = v ^ n := by
            rw [← pow_succ, Nat.sub_add_cancel hn]
          rw [show (n : A) * v ^ (n - 1) * (q * v) =
            (n : A) * q * (v ^ (n - 1) * v) by ring, hvp]
      _ = 0 := sub_eq_zero.mpr hpow'
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hcancel).resolve_left (mul_ne_zero hn0 hvpow0))

end

end GaloisForLFunctions.HTGeometry
