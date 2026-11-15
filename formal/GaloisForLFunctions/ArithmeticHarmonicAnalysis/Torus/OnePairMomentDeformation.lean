import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.AffineMomentMultiplicity
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
# Moment fibers with identical weight multiplicities and different rings

Let `Rₜ = K[z,w]/(zw-t)`. Both coordinate classes are nonzero for every `t`,
as witnessed by evaluation at `(1,t)` and `(t,1)`. For `t ≠ 0`, Laurent
evaluation gives an explicit algebra equivalence `Rₜ ≃ K[T,T⁻¹]`. At zero,
the two nonzero coordinates multiply to zero.

Consequently two fibers are isomorphic as rings, or as `K`-algebras, exactly
when their parameters are both zero or both nonzero. Nevertheless every
filtered weight dimension is independent of `t`: weight `q` has dimension
one at cut `D ≥ max(-q,0)` and dimension zero below that cut.

Thus the affine extension of the moment multiplicity formula does not recover
the fiber algebra. The complete isomorphism classification detects precisely
the distinction that all these multiplicities miss.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.OnePairMoment
open MvPolynomial
variable (K : Type*) [Field K]

abbrev Variables := Fin 1 ⊕ Fin 1

/-- The single bilinear moment equation at scalar level `t`. -/
def equation (t : K) : MvPolynomial Variables K := X (Sum.inl 0) * X (Sum.inr 0) - C t

/-- The actual coordinate ring of the moment fiber. -/
abbrev CoordinateRing (t : K) := MvPolynomial Variables K ⧸ Ideal.span {equation K t}

/-- The positively weighted coordinate class. -/
def z (t : K) : CoordinateRing K t := Ideal.Quotient.mk _ (X (Sum.inl 0))
/-- The negatively weighted coordinate class. -/
def w (t : K) : CoordinateRing K t := Ideal.Quotient.mk _ (X (Sum.inr 0))

/-- The coordinate product equals the scalar moment level in the quotient. -/
theorem z_mul_w (t : K) : z K t * w K t = algebraMap K (CoordinateRing K t) t := by
  change Ideal.Quotient.mk _ (X (Sum.inl 0)) * Ideal.Quotient.mk _ (X (Sum.inr 0)) =
    Ideal.Quotient.mk _ (C t)
  rw [← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- A polynomial algebra map descends precisely after annihilating the defining relation. -/
def desc {A : Type*} [CommRing A] [Algebra K A] (t : K)
    (F : MvPolynomial Variables K →ₐ[K] A) (h : F (equation K t) = 0) :
    CoordinateRing K t →ₐ[K] A :=
  Ideal.Quotient.liftₐ _ F (by
    intro f hf
    have hi : Ideal.span {equation K t} ≤ RingHom.ker F.toRingHom := by
      rw [Ideal.span_le]
      rintro f rfl
      exact h
    exact hi hf)

/-- Evaluation at `(1,t)` is a point of every moment fiber. -/
def pointZ (t : K) : CoordinateRing K t →ₐ[K] K :=
  desc K t (aeval (Sum.elim (fun _ : Fin 1 => (1 : K)) (fun _ => t))) (by
    simp [equation])

/-- Evaluation at `(t,1)` is a point of every moment fiber. -/
def pointW (t : K) : CoordinateRing K t →ₐ[K] K :=
  desc K t (aeval (Sum.elim (fun _ : Fin 1 => t) (fun _ => (1 : K)))) (by
    simp [equation])

theorem z_ne_zero (t : K) : z K t ≠ 0 := by
  intro h
  have he := congrArg (pointZ K t) h
  simp [pointZ, desc, z] at he

theorem w_ne_zero (t : K) : w K t ≠ 0 := by
  intro h
  have he := congrArg (pointW K t) h
  simp [pointW, desc, w] at he

instance (t : K) : Nontrivial (CoordinateRing K t) :=
  ⟨⟨z K t, 0, z_ne_zero K t⟩⟩

/-- At a nonzero level, the inverse of `z` is `t⁻¹w`. -/
def zUnit (t : K) (ht : t ≠ 0) : (CoordinateRing K t)ˣ where
  val := z K t
  inv := algebraMap K (CoordinateRing K t) t⁻¹ * w K t
  val_inv := by
    rw [mul_left_comm, z_mul_w, ← map_mul, inv_mul_cancel₀ ht, map_one]
  inv_val := by
    rw [mul_assoc, mul_comm (w K t), z_mul_w, ← map_mul, inv_mul_cancel₀ ht, map_one]

/-- The positive coordinate is invertible exactly away from zero level. -/
theorem z_isUnit_iff (t : K) : IsUnit (z K t) ↔ t ≠ 0 := by
  constructor
  · rintro ⟨u, hu⟩ rfl
    have h := z_mul_w K 0
    rw [← hu, map_zero] at h
    have he := congrArg (fun x => (↑u⁻¹ : CoordinateRing K 0) * x) h
    apply w_ne_zero K 0
    simpa only [← mul_assoc, Units.inv_mul, one_mul, mul_zero] using he
  · intro ht
    exact ⟨zUnit K t ht, rfl⟩

/-- The negative coordinate is invertible exactly away from zero level. -/
theorem w_isUnit_iff (t : K) : IsUnit (w K t) ↔ t ≠ 0 := by
  constructor
  · rintro ⟨u, hu⟩ rfl
    have h := z_mul_w K 0
    rw [← hu, map_zero] at h
    have he := congrArg (fun x => x * (↑u⁻¹ : CoordinateRing K 0)) h
    apply z_ne_zero K 0
    simpa only [mul_assoc, Units.mul_inv, mul_one, zero_mul] using he
  · intro ht
    have hm : w K t * (algebraMap K (CoordinateRing K t) t⁻¹ * z K t) = 1 := by
      rw [mul_left_comm, mul_comm (w K t) (z K t), z_mul_w,
        ← map_mul, inv_mul_cancel₀ ht, map_one]
    exact ⟨⟨w K t, _, hm, (mul_comm _ _).trans hm⟩, rfl⟩

/-- Send `z` to `T` and `w` to `tT⁻¹`; the moment relation vanishes. -/
def toLaurent (t : K) : CoordinateRing K t →ₐ[K] LaurentPolynomial K :=
  desc K t (aeval (Sum.elim
    (fun _ : Fin 1 => LaurentPolynomial.T 1)
    (fun _ => LaurentPolynomial.C t * LaurentPolynomial.T (-1)))) (by
      simp only [equation, map_sub, map_mul, aeval_X, Sum.elim_inl, Sum.elim_inr, aeval_C]
      rw [mul_left_comm, ← LaurentPolynomial.T_add]
      simp only [add_neg_cancel, LaurentPolynomial.T_zero, mul_one,
        ← LaurentPolynomial.C_eq_algebraMap, sub_self])

@[simp] theorem toLaurent_z (t : K) : toLaurent K t (z K t) = LaurentPolynomial.T 1 := by
  simp [toLaurent, desc, z]

@[simp] theorem toLaurent_w (t : K) :
    toLaurent K t (w K t) = LaurentPolynomial.C t * LaurentPolynomial.T (-1) := by
  simp [toLaurent, desc, w]

/-- Evaluate a Laurent polynomial at the unit represented by `z`. -/
def ofLaurent (t : K) (ht : t ≠ 0) : LaurentPolynomial K →ₐ[K] CoordinateRing K t where
  toRingHom := LaurentPolynomial.eval₂ (algebraMap K (CoordinateRing K t)) (zUnit K t ht)
  commutes' r := LaurentPolynomial.eval₂_C _ _ r

@[simp] theorem ofLaurent_T_one (t : K) (ht : t ≠ 0) :
    ofLaurent K t ht (LaurentPolynomial.T 1) = z K t := by
  simp [ofLaurent, zUnit]

@[simp] theorem ofLaurent_T_neg_one (t : K) (ht : t ≠ 0) :
    ofLaurent K t ht (LaurentPolynomial.T (-1)) =
      algebraMap K (CoordinateRing K t) t⁻¹ * w K t := by
  simp [ofLaurent, zUnit]

/-- Constants and the two Laurent generators determine the first inverse identity. -/
theorem toLaurent_ofLaurent (t : K) (ht : t ≠ 0) (f : LaurentPolynomial K) :
    toLaurent K t (ofLaurent K t ht f) = f := by
  let F := (toLaurent K t).comp (ofLaurent K t ht)
  have hC (a : K) : F (LaurentPolynomial.C a) = LaurentPolynomial.C a := F.commutes a
  have hT : F (LaurentPolynomial.T 1) = LaurentPolynomial.T 1 := by simp [F]
  have hTi : F (LaurentPolynomial.T (-1)) = LaurentPolynomial.T (-1) := by
    change toLaurent K t (ofLaurent K t ht (LaurentPolynomial.T (-1))) = _
    rw [ofLaurent_T_neg_one, map_mul, AlgHom.commutes, toLaurent_w]
    change LaurentPolynomial.C t⁻¹ * (LaurentPolynomial.C t * LaurentPolynomial.T (-1)) = _
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul]
  change F f = f
  induction f using LaurentPolynomial.induction_on with
  | h_C a => exact hC a
  | h_add hp hq => simp only [map_add, hp, hq]
  | h_C_mul_T n a ih =>
    rw [LaurentPolynomial.T_add, ← mul_assoc, map_mul, ih, hT]
  | h_C_mul_T_Z n a ih =>
    rw [sub_eq_add_neg, LaurentPolynomial.T_add, ← mul_assoc, map_mul, ih, hTi]

/-- The second inverse identity follows from the two original coordinate generators. -/
theorem ofLaurent_toLaurent (t : K) (ht : t ≠ 0) (f : CoordinateRing K t) :
    ofLaurent K t ht (toLaurent K t f) = f := by
  have he : (ofLaurent K t ht).comp (toLaurent K t) = AlgHom.id K _ := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    rcases i with i | i
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      change ofLaurent K t ht (toLaurent K t (z K t)) = z K t
      simp
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      change ofLaurent K t ht (toLaurent K t (w K t)) = w K t
      rw [toLaurent_w, map_mul, ofLaurent_T_neg_one]
      have hC : ofLaurent K t ht (LaurentPolynomial.C t) = algebraMap K (CoordinateRing K t) t :=
        (ofLaurent K t ht).commutes t
      rw [hC, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]
  exact DFunLike.congr_fun he f

/-- Every nonzero moment fiber is explicitly the Laurent polynomial algebra. -/
def laurentEquiv (t : K) (ht : t ≠ 0) : CoordinateRing K t ≃ₐ[K] LaurentPolynomial K :=
  AlgEquiv.ofAlgHom (toLaurent K t) (ofLaurent K t ht)
    (by apply AlgHom.ext; intro f; exact toLaurent_ofLaurent K t ht f)
    (by apply AlgHom.ext; intro f; exact ofLaurent_toLaurent K t ht f)

/-- The zero fiber is exactly the failure of the domain property. -/
theorem coordinateRing_isDomain_iff (t : K) : IsDomain (CoordinateRing K t) ↔ t ≠ 0 := by
  constructor
  · intro h ht
    subst t
    letI := h
    have hz := z_mul_w K 0
    rw [map_zero] at hz
    exact (mul_ne_zero (z_ne_zero K 0) (w_ne_zero K 0)) hz
  · intro ht
    letI : NoZeroDivisors (CoordinateRing K t) := (laurentEquiv K t ht).toMulEquiv.noZeroDivisors
    exact NoZeroDivisors.to_isDomain _

/-- The vanishing of the parameter completely classifies the fibers as rings. -/
theorem nonempty_ringEquiv_iff (s t : K) :
    Nonempty (CoordinateRing K s ≃+* CoordinateRing K t) ↔ (s = 0 ↔ t = 0) := by
  constructor
  · rintro ⟨e⟩
    have hn : (s ≠ 0) ↔ (t ≠ 0) := by
      constructor
      · intro hs
        letI : IsDomain (CoordinateRing K s) := (coordinateRing_isDomain_iff K s).mpr hs
        letI : NoZeroDivisors (CoordinateRing K t) := e.symm.toMulEquiv.noZeroDivisors
        exact (coordinateRing_isDomain_iff K t).mp (NoZeroDivisors.to_isDomain _)
      · intro ht
        letI : IsDomain (CoordinateRing K t) := (coordinateRing_isDomain_iff K t).mpr ht
        letI : NoZeroDivisors (CoordinateRing K s) := e.toMulEquiv.noZeroDivisors
        exact (coordinateRing_isDomain_iff K s).mp (NoZeroDivisors.to_isDomain _)
    exact not_iff_not.mp hn
  · intro h
    by_cases hs : s = 0
    · have ht := h.mp hs
      subst s
      subst t
      exact ⟨RingEquiv.refl _⟩
    · have ht : t ≠ 0 := fun ht => hs (h.mpr ht)
      exact ⟨((laurentEquiv K s hs).trans (laurentEquiv K t ht).symm).toRingEquiv⟩

/-- The same two classes give the complete classification as algebras over the field. -/
theorem nonempty_algEquiv_iff (s t : K) :
    Nonempty (CoordinateRing K s ≃ₐ[K] CoordinateRing K t) ↔ (s = 0 ↔ t = 0) := by
  constructor
  · rintro ⟨e⟩
    exact (nonempty_ringEquiv_iff K s t).mp ⟨e.toRingEquiv⟩
  · intro h
    by_cases hs : s = 0
    · have ht := h.mp hs
      subst s
      subst t
      exact ⟨AlgEquiv.refl⟩
    · have ht : t ≠ 0 := fun ht => hs (h.mpr ht)
      exact ⟨(laurentEquiv K s hs).trans (laurentEquiv K t ht).symm⟩

/-- The image of bounded-cut weight polynomials in the actual moment fiber. -/
def boundedWeightSpace (t : K) (q : ℤ) (D : ℕ) : Submodule K (CoordinateRing K t) :=
  (boundedPairedWeightSpace K (fun _ : Fin 1 => q) D).map
    (Ideal.Quotient.mkₐ K (Ideal.span {equation K t})).toLinearMap

/-- Every level has the same one-dimensional weight component once its slack is reached. -/
theorem finrank_boundedWeightSpace (t : K) (q : ℤ) (D : ℕ) :
    Module.finrank K (boundedWeightSpace K t q D) =
      if (-q).toNat ≤ D then 1 else 0 := by
  have h := finrank_singlePairAffineMomentWeightSpace K t (fun _ : Fin 1 => q) D
  have hs : weightSlack (fun _ : Fin 1 => q) = (-q).toNat := by simp [weightSlack]
  rw [hs] at h
  exact h

/-- Zero and unit levels have identical filtered weight dimensions but nonisomorphic rings. -/
theorem same_multiplicities_nonisomorphic_fibers :
    (∀ q D, Module.finrank K (boundedWeightSpace K 0 q D) =
      Module.finrank K (boundedWeightSpace K 1 q D)) ∧
    ¬ Nonempty (CoordinateRing K 0 ≃+* CoordinateRing K 1) := by
  constructor
  · intro q D
    rw [finrank_boundedWeightSpace, finrank_boundedWeightSpace]
  · rw [nonempty_ringEquiv_iff]
    intro h
    exact one_ne_zero (h.mp rfl)

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.OnePairMoment

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.OnePairMoment.laurentEquiv
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.OnePairMoment.coordinateRing_isDomain_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.OnePairMoment.nonempty_ringEquiv_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.OnePairMoment.same_multiplicities_nonisomorphic_fibers
