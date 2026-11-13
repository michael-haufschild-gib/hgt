import GaloisForLFunctions.RHTower.Artin.ArtinLocalEulerFactorOfAnInducedRepresentation
import GaloisForLFunctions.RHTower.Artin.ArtinNumberFieldEulerProductAnalytic

/-!
# The Artin Euler product of an induced representation

Let `K ⊂ M ⊂ L` be number fields, `G` the Galois group of `L/K` and `H ≤ G` the Galois group
of `L/M`. Let `ρ` be a representation of `G` whose character is induced from a representation
`σ` of `H`.

* **Local** (`numberFieldFinitePlaceLocalEulerPolynomial_induced`): at a prime `v` of `K`,

  `P_v(ρ; X) = Π_{w | v} P_w(σ; X^{f(w|v)})`,

  the product over the primes `w` of `M` above `v`.
* **Euler factors** (`numberFieldFinitePlaceArtinEulerReciprocal_induced`): since
  `N(w) = N(v)^{f(w|v)}`, the Euler factor of `ρ` at `v` is the product of the Euler factors of
  `σ` at the primes above `v`.
* **Global** (`numberFieldFinitePlaceArtinEulerReciprocalProduct_induced`): for `Re s > 1`,

  `L(s, ρ, L/K) = L(s, σ, L/M)`,

  by regrouping the absolutely convergent product over the primes of `M` along the fibres of
  `w ↦ w ∩ K`.
-/

open scoped Classical BigOperators NumberField Pointwise
open Polynomial IsDedekindDomain

noncomputable section

universe u

namespace GaloisForLFunctions

attribute [local instance] Ideal.Quotient.field

variable {K M L G V W : Type u} [Field K] [NumberField K] [Field M] [NumberField M]
  [Field L] [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
  [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  (H : Subgroup G) [IsGaloisGroup H M L]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-! ### The primes of the intermediate field -/

omit [Algebra K L] [IsScalarTower K M L] [Fintype G] [IsGaloisGroup G K L] in
/-- The subgroup `H`, acting on `𝓞 L` through `G`, is the Galois group of `𝓞 L` over `𝓞 M`. -/
theorem isGaloisGroup_subgroup_ringOfIntegers : IsGaloisGroup H (𝓞 M) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing H (𝓞 M) (𝓞 L) M L

/-- **The norm of a prime above**: `N(w) = N(w ∩ K)^{f(w | w ∩ K)}`. -/
theorem absNorm_eq_absNorm_under_pow_inertiaDeg (w : HeightOneSpectrum (𝓞 M)) :
    w.asIdeal.absNorm =
      (w.under (𝓞 K)).asIdeal.absNorm ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  haveI := w.isMaximal
  haveI : (w.asIdeal.under (𝓞 K)).IsMaximal := (w.under (𝓞 K)).isMaximal
  have hcard : Nat.card (𝓞 M ⧸ w.asIdeal) =
      Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal (w.asIdeal.under (𝓞 K)) w.asIdeal,
      Module.natCard_eq_pow_finrank (K := 𝓞 K ⧸ w.asIdeal.under (𝓞 K)) (V := 𝓞 M ⧸ w.asIdeal)]
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]
  exact hcard

/-- Only finitely many primes of `M` lie above a prime of `K`. -/
theorem finite_setOf_under_eq (v : HeightOneSpectrum (𝓞 K)) :
    {w : HeightOneSpectrum (𝓞 M) | w.under (𝓞 K) = v}.Finite := by
  haveI := v.isMaximal
  refine Set.Finite.of_finite_image
    ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)).subset ?_)
    (fun w _ w' _ h => HeightOneSpectrum.ext h)
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal (Eq.symm hw)⟩⟩

variable (M) in
/-- The primes of `M` above a prime of `K`. -/
def finitePlacesAbove (v : HeightOneSpectrum (𝓞 K)) : Finset (HeightOneSpectrum (𝓞 M)) :=
  (finite_setOf_under_eq (M := M) v).toFinset

theorem mem_finitePlacesAbove {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)} :
    w ∈ finitePlacesAbove M v ↔ w.under (𝓞 K) = v :=
  Set.Finite.mem_toFinset _

omit [NumberField K] [NumberField M] [NumberField L] [Fintype G] [IsGaloisGroup G K L]
  [IsGaloisGroup H M L] in
/-- A prime of `𝓞 L` above the prime `v` of `K` lies above a nonzero prime of `M`. -/
theorem under_ne_bot_of_under_eq {v : HeightOneSpectrum (𝓞 K)} {Q : Ideal (𝓞 L)}
    (hQ : Q.under (𝓞 K) = v.asIdeal) : Q.under (𝓞 M) ≠ ⊥ := by
  intro h0
  refine v.ne_bot ?_
  rw [← hQ, ← Ideal.under_under (B := 𝓞 M) Q, h0]
  exact Ideal.under_bot (𝓞 K) (𝓞 M)

omit [IsGaloisGroup H M L] in
/-- **Every prime of `M` above `v` lies below a conjugate of a given prime of `L` above `v`.** -/
theorem exists_smul_under_eq_asIdeal {v : HeightOneSpectrum (𝓞 K)} (Q : Ideal (𝓞 L))
    [Q.IsPrime] (hQ : Q.under (𝓞 K) = v.asIdeal) {w : HeightOneSpectrum (𝓞 M)}
    (hw : w.under (𝓞 K) = v) : ∃ x : G, (x • Q).under (𝓞 M) = w.asIdeal := by
  haveI := w.isMaximal
  obtain ⟨Q', hQ'max, hQ'over⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) w.asIdeal
  haveI := hQ'max.isPrime
  have hv : v.asIdeal = w.asIdeal.under (𝓞 K) :=
    congrArg HeightOneSpectrum.asIdeal (Eq.symm hw)
  have hQ' : Q.under (𝓞 K) = Q'.under (𝓞 K) := by
    rw [hQ, hv, ← Ideal.under_under (B := 𝓞 M) Q', ← hQ'over.over]
  obtain ⟨x, hx⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 L) G Q Q' hQ'
  exact ⟨x, by rw [← hx, ← hQ'over.over]⟩

/-! ### The local factor -/

/-- **The local Euler polynomial of an induced representation**: at a prime `v` of `K`, it is
the product of the local polynomials of `σ` at the primes `w` of `M` above `v`, in the
variables `X^{f(w|v)}`. -/
theorem numberFieldFinitePlaceLocalEulerPolynomial_induced (ρ : Representation ℂ G V)
    (σ : Representation ℂ H W) (hρ : ρ.character = inducedFunction H σ.character)
    (v : HeightOneSpectrum (𝓞 K)) :
    numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v ρ =
      ∏ w ∈ finitePlacesAbove M v, Polynomial.expand ℂ (w.asIdeal.inertiaDeg (𝓞 K))
        (numberFieldFinitePlaceLocalEulerPolynomial (K := M) (L := L) w σ) := by
  haveI := v.isMaximal
  haveI := isGaloisGroup_subgroup_ringOfIntegers (M := M) (L := L) H
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  haveI := hQmax.isPrime
  have hQ : Q.under (𝓞 K) = v.asIdeal := hQover.over.symm
  -- the local polynomial of `σ` as a function of an ideal of `𝓞 M`
  let R : Ideal (𝓞 M) → ℂ[X] := fun I =>
    if h : I.IsPrime ∧ I ≠ ⊥ then
      numberFieldFinitePlaceLocalEulerPolynomial (K := M) (L := L) ⟨I, h.1, h.2⟩ σ
    else 1
  have hRw : ∀ w : HeightOneSpectrum (𝓞 M),
      R w.asIdeal = numberFieldFinitePlaceLocalEulerPolynomial (K := M) (L := L) w σ :=
    fun w => dif_pos ⟨w.isPrime, w.ne_bot⟩
  have hR : ∀ (Q' : Ideal (𝓞 L)) [Q'.IsPrime] [Finite (𝓞 L ⧸ Q')],
      Q'.under (𝓞 K) = Q.under (𝓞 K) →
        R (Q'.under (𝓞 M)) = frobeniusInertiaEulerPolynomial (R := 𝓞 M) Q' σ := by
    intro Q' _ _ hQ'
    let w' : HeightOneSpectrum (𝓞 M) :=
      ⟨Q'.under (𝓞 M), Ideal.IsPrime.under (𝓞 M) Q',
        under_ne_bot_of_under_eq (M := M) (hQ'.trans hQ)⟩
    haveI : Q'.IsMaximal :=
      Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (𝓞 L ⧸ Q'))
    haveI : Q'.LiesOver w'.asIdeal := ⟨rfl⟩
    rw [show R (Q'.under (𝓞 M)) = _ from hRw w']
    exact (frobeniusInertiaEulerPolynomial_eq_numberFieldFinitePlaceLocalEulerPolynomial
      (K := M) (G := H) w' Q' σ).symm
  rw [← frobeniusInertiaEulerPolynomial_eq_numberFieldFinitePlaceLocalEulerPolynomial
      (K := K) (L := L) (G := G) v Q ρ,
    frobeniusInertiaEulerPolynomial_induced_eq_prod H Q ρ σ hρ R hR]
  symm
  -- the primes above `v` are the primes below the conjugates of `Q`
  refine Finset.prod_bij (fun w _ => w.asIdeal) ?_ ?_ ?_ ?_
  · intro w hw
    obtain ⟨x, hx⟩ :=
      exists_smul_under_eq_asIdeal (G := G) Q hQ (mem_finitePlacesAbove.mp hw)
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩
  · intro w _ w' _ h
    exact HeightOneSpectrum.ext h
  · intro I hI
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hI
    have hx : (x • Q).under (𝓞 K) = v.asIdeal := by rw [Ideal.under_smul, hQ]
    refine ⟨⟨(x • Q).under (𝓞 M), Ideal.IsPrime.under (𝓞 M) (x • Q),
      under_ne_bot_of_under_eq (M := M) hx⟩, mem_finitePlacesAbove.mpr ?_, rfl⟩
    refine HeightOneSpectrum.ext ?_
    change ((x • Q).under (𝓞 M)).under (𝓞 K) = v.asIdeal
    rw [Ideal.under_under, hx]
  · intro w _
    rw [hRw w]

/-! ### Euler factors and Euler products -/

/-- **The Euler factor of an induced representation** at a prime `v` of `K` is the product of
the Euler factors of `σ` at the primes of `M` above `v`. -/
theorem numberFieldFinitePlaceArtinEulerReciprocal_induced (ρ : Representation ℂ G V)
    (σ : Representation ℂ H W) (hρ : ρ.character = inducedFunction H σ.character)
    (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s =
      ∏ w ∈ finitePlacesAbove M v,
        numberFieldFinitePlaceArtinEulerReciprocal (K := M) (L := L) σ w s := by
  unfold numberFieldFinitePlaceArtinEulerReciprocal
  rw [numberFieldFinitePlaceLocalEulerPolynomial_induced (M := M) H ρ σ hρ v,
    Polynomial.eval_prod,
    ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun w hw => ?_
  -- `N(w)^{-s} = (N(v)^{-s})^f`
  have hN : (w.asIdeal.absNorm : ℂ) ^ (-s) =
      ((v.asIdeal.absNorm : ℂ) ^ (-s)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
    rw [absNorm_eq_absNorm_under_pow_inertiaDeg (K := K) w, mem_finitePlacesAbove.mp hw,
      Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
  rw [Polynomial.expand_eval, hN]

/-- **Artin's induction formula for the Euler product**: for `Re s > 1`, the Artin Euler
product of a representation of `Gal(L/K)` with character induced from `σ` is the Artin Euler
product of `σ` over the intermediate field. -/
theorem numberFieldFinitePlaceArtinEulerReciprocalProduct_induced (ρ : Representation ℂ G V)
    (σ : Representation ℂ H W) (hρ : ρ.character = inducedFunction H σ.character) {s : ℂ}
    (hs : 1 < s.re) :
    numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ s =
      numberFieldFinitePlaceArtinEulerReciprocalProduct (K := M) (L := L) σ s := by
  have hK := (hasProdLocallyUniformlyOn_numberFieldFinitePlaceArtinEulerReciprocal
    (K := K) (L := L) ρ).hasProd (show s ∈ artinEulerAbsoluteHalfPlane from hs)
  have hM := (hasProdLocallyUniformlyOn_numberFieldFinitePlaceArtinEulerReciprocal
    (K := M) (L := L) σ).hasProd (show s ∈ artinEulerAbsoluteHalfPlane from hs)
  -- regroup the product over the primes of `M` along the fibres of `w ↦ w ∩ K`
  have hsig := (Equiv.hasProd_iff
    (Equiv.sigmaFiberEquiv (HeightOneSpectrum.under (𝓞 K) (B := 𝓞 M)))).mpr hM
  refine hK.unique (hsig.sigma fun v => ?_)
  haveI : Finite {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} :=
    (finite_setOf_under_eq (M := M) v).to_subtype
  haveI : Fintype {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} := Fintype.ofFinite _
  have h := hasProd_fintype (fun c : {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} =>
    numberFieldFinitePlaceArtinEulerReciprocal (K := M) (L := L) σ c.1 s)
  have e : ∏ c : {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v},
      numberFieldFinitePlaceArtinEulerReciprocal (K := M) (L := L) σ c.1 s =
      numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s := by
    rw [numberFieldFinitePlaceArtinEulerReciprocal_induced (M := M) H ρ σ hρ v s]
    exact (Finset.prod_subtype (finitePlacesAbove M v) (fun w => mem_finitePlacesAbove)
      (fun w => numberFieldFinitePlaceArtinEulerReciprocal (K := M) (L := L) σ w s)).symm
  rw [e] at h
  exact h

end GaloisForLFunctions
