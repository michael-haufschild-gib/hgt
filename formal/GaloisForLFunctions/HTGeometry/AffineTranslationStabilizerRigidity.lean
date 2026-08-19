import GaloisForLFunctions.HTGeometry.DifferentialIndependence

/-!
# Translation stabilizers of affine loci are exact

A translation of affine space that maps an algebraic set into itself maps it *onto* itself.  Over a
Noetherian coefficient ring this is a finiteness statement, not a dimension statement: translation
by a fixed vector induces a surjective endomorphism of the coordinate ring of the locus, and a
surjective endomorphism of a Noetherian ring is injective.

The point form is the one used by horizon arguments: if a translated point satisfies every
polynomial relation of the original point, then the two points satisfy exactly the same relations,
so the translation preserves the locus.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-! ### Surjective endomorphisms of Noetherian rings -/

/-- A surjective ring endomorphism of a Noetherian commutative ring is injective. -/
theorem injective_of_surjective_endomorphism_of_isNoetherianRing
    {S : Type*} [CommRing S] [IsNoetherianRing S] (θ : S →+* S) (hθ : Function.Surjective θ) :
    Function.Injective θ := by
  classical
  set J : ℕ → Ideal S := fun n => Nat.rec (⊥ : Ideal S) (fun _ I => Ideal.comap θ I) n with hJ
  have hJzero : J 0 = ⊥ := rfl
  have hJsucc : ∀ n, J (n + 1) = Ideal.comap θ (J n) := fun n => rfl
  have hmem : ∀ n (x : S), x ∈ J n ↔ (⇑θ)^[n] x = 0 := by
    intro n
    induction n with
    | zero => intro x; simp [hJzero, Submodule.mem_bot]
    | succ n ih =>
        intro x
        rw [hJsucc, Ideal.mem_comap, ih, Function.iterate_succ_apply]
  have hmono : Monotone J := by
    refine monotone_nat_of_le_succ fun n => ?_
    intro x hx
    exact (hmem (n + 1) x).2 (by
      rw [Function.iterate_succ_apply', (hmem n x).1 hx, map_zero])
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian.2 (by infer_instance)) ⟨J, hmono⟩
  have hstab : J n = J (n + 1) := hn (n + 1) (Nat.le_succ n)
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hθ.iterate n x
  have hy : y ∈ J (n + 1) := (hmem (n + 1) y).2 (by
    rw [Function.iterate_succ_apply']
    exact hx)
  rw [← hstab] at hy
  exact (hmem n y).1 hy

/-! ### Translation of an ideal -/

variable {K ι : Type*} [CommRing K]

/-- Evaluating a translated polynomial is evaluating it at the translated point. -/
theorem aeval_mvPolynomialBaseTranslation {L : Type*} [CommRing L] [Algebra K L]
    (z : ι → L) (c : ι → K) (P : MvPolynomial ι K) :
    MvPolynomial.aeval z (mvPolynomialBaseTranslation c P)
      = MvPolynomial.aeval (fun i => z i + algebraMap K L (c i)) P := by
  have h : (MvPolynomial.aeval z : MvPolynomial ι K →ₐ[K] L).comp
        (mvPolynomialBaseTranslation c).toAlgHom
      = (MvPolynomial.aeval (fun i => z i + algebraMap K L (c i)) :
          MvPolynomial ι K →ₐ[K] L) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp
  exact congrArg (fun f : MvPolynomial ι K →ₐ[K] L => f P) h

/-- **Translation rigidity for an ideal.**  A translation mapping an ideal of a Noetherian
polynomial ring into itself reflects membership as well. -/
theorem mvPolynomialBaseTranslation_mem_iff [Finite ι] [IsNoetherianRing K]
    (I : Ideal (MvPolynomial ι K)) (c : ι → K)
    (hc : ∀ P ∈ I, mvPolynomialBaseTranslation c P ∈ I) (P : MvPolynomial ι K) :
    mvPolynomialBaseTranslation c P ∈ I ↔ P ∈ I := by
  classical
  have hle : I ≤ Ideal.comap
      ((Ideal.Quotient.mk I).comp (mvPolynomialBaseTranslation c).toAlgHom.toRingHom) ⊥ := by
    intro P hP
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hc P hP
  let θ : (MvPolynomial ι K ⧸ I) →+* (MvPolynomial ι K ⧸ I) :=
    Ideal.Quotient.lift I
      ((Ideal.Quotient.mk I).comp (mvPolynomialBaseTranslation c).toAlgHom.toRingHom)
      (fun P hP => by simpa [Ideal.Quotient.eq_zero_iff_mem] using hc P hP)
  have hθmk : ∀ Q : MvPolynomial ι K,
      θ (Ideal.Quotient.mk I Q) = Ideal.Quotient.mk I (mvPolynomialBaseTranslation c Q) := by
    intro Q
    simp [θ]
  have hsurj : Function.Surjective θ := by
    intro q
    obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨Ideal.Quotient.mk I ((mvPolynomialBaseTranslation c).symm Q), ?_⟩
    rw [hθmk]
    simp
  have hinj : Function.Injective θ :=
    injective_of_surjective_endomorphism_of_isNoetherianRing θ hsurj
  constructor
  · intro hP
    have h0 : θ (Ideal.Quotient.mk I P) = θ 0 := by
      rw [hθmk, map_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem).2 hP
    have := hinj h0
    exact (Ideal.Quotient.eq_zero_iff_mem).1 this
  · exact hc P

/-- **Translation rigidity at a point.**  If the translate of a point satisfies every polynomial
relation of the point, the two points satisfy exactly the same relations. -/
theorem aeval_add_eq_zero_iff [Finite ι] [IsNoetherianRing K]
    {L : Type*} [CommRing L] [Algebra K L] (z : ι → L) (c : ι → K)
    (hz : ∀ P : MvPolynomial ι K, MvPolynomial.aeval z P = 0 →
        MvPolynomial.aeval (fun i => z i + algebraMap K L (c i)) P = 0)
    (P : MvPolynomial ι K) :
    MvPolynomial.aeval (fun i => z i + algebraMap K L (c i)) P = 0 ↔
      MvPolynomial.aeval z P = 0 := by
  classical
  set I : Ideal (MvPolynomial ι K) :=
    RingHom.ker (MvPolynomial.aeval z : MvPolynomial ι K →ₐ[K] L).toRingHom with hI
  have hmemI : ∀ Q : MvPolynomial ι K, Q ∈ I ↔ MvPolynomial.aeval z Q = 0 := by
    intro Q; rw [hI]; exact RingHom.mem_ker
  have hc : ∀ Q ∈ I, mvPolynomialBaseTranslation c Q ∈ I := by
    intro Q hQ
    rw [hmemI] at hQ ⊢
    rw [aeval_mvPolynomialBaseTranslation]
    exact hz Q hQ
  have hkey := mvPolynomialBaseTranslation_mem_iff I c hc P
  rw [hmemI, hmemI, aeval_mvPolynomialBaseTranslation] at hkey
  exact hkey

end

end GaloisForLFunctions.HTGeometry
