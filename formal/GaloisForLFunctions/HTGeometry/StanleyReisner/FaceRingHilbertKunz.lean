import GaloisForLFunctions.HTGeometry.StanleyReisner.FiniteFieldPoints
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Truncated Stanley–Reisner algebras and Hilbert–Kunz multiplicity

Surviving exponent vectors give a basis for the monomial quotient. Counting by
support identifies the Hilbert–Kunz function and its leading coefficient.
-/

namespace GaloisForLFunctions.HTGeometry
open Finset MvPolynomial ArithmeticHarmonicAnalysis.Codes
open scoped Classical
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (K : Type*) [Field K]


private def boxExponent {r : ι → ℕ} (x : ∀ i, Fin (r i+1)) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (x i).val

private theorem boxExponent_apply {r : ι → ℕ} (x : ∀ i, Fin (r i+1)) (i : ι) :
    boxExponent x i = (x i).val := rfl

private theorem boxExponent_injective (r : ι → ℕ) : Function.Injective (boxExponent (r := r)) := by
  intro x y he
  funext i
  exact Fin.ext (DFunLike.congr_fun he i)

private def allowedBox (facets : Finset (Finset ι)) (r : ι → ℕ) : Finset (∀ i, Fin (r i+1)) :=
  univ.filter fun x => IsFaceOf (facets : Set (Finset ι)) (boxExponent x).support

/-- The Stanley–Reisner ideal with one pure power cut in each coordinate. -/
def truncatedFaceIdeal (facets : Finset (Finset ι)) (r : ι → ℕ) : Ideal (MvPolynomial ι K) :=
  Ideal.span ((fun e => monomial e (1:K)) '' (nonfaceExponents facets ∪
    Set.range fun i => Finsupp.single i (r i+1)))

theorem truncatedFaceIdeal_eq (facets : Finset (Finset ι)) (r : ι → ℕ) :
    truncatedFaceIdeal K facets r = stanleyReisnerIdeal K facets ⊔
      Ideal.span (Set.range fun i => (X i : MvPolynomial ι K)^(r i+1)) := by
  rw [truncatedFaceIdeal,Set.image_union,Ideal.span_union,stanleyReisnerIdeal,Set.image_range]
  simp [Function.comp_def,X_pow_eq_monomial]

private theorem nonface_divisor_iff (facets : Finset (Finset ι)) (e : ι →₀ ℕ) :
    (∃ d ∈ nonfaceExponents facets, d ≤ e) ↔ ¬IsFaceOf (facets : Set (Finset ι)) e.support := by
  have h := mem_stanleyReisnerIdeal_iff (R := K) facets (monomial e (1:K))
  rw [stanleyReisnerIdeal,mem_ideal_span_monomial_image] at h
  simpa [support_monomial] using h

theorem mem_truncatedFaceIdeal (facets : Finset (Finset ι)) (r : ι → ℕ) (p : MvPolynomial ι K) :
    p ∈ truncatedFaceIdeal K facets r ↔ ∀ e ∈ p.support,
      ¬(IsFaceOf (facets : Set (Finset ι)) e.support ∧ ∀ i, e i ≤ r i) := by
  rw [truncatedFaceIdeal,mem_ideal_span_monomial_image]
  apply forall₂_congr
  intro e _
  constructor
  · rintro ⟨d,hd,hde⟩ ⟨hf,hb⟩
    rcases hd with hn | ⟨i,rfl⟩
    · exact ((nonface_divisor_iff K facets e).mp ⟨d,hn,hde⟩) hf
    · have hi := hde i
      rw [Finsupp.single_eq_same] at hi
      exact Nat.not_succ_le_self _ (hi.trans (hb i))
  · intro h
    by_cases hf : IsFaceOf (facets : Set (Finset ι)) e.support
    · have hh : ¬∀ i, e i ≤ r i := fun hb => h ⟨hf,hb⟩
      push_neg at hh
      obtain ⟨i,hi⟩ := hh
      refine ⟨Finsupp.single i (r i+1),Or.inr ⟨i,rfl⟩,?_⟩
      intro j
      by_cases hj : i = j
      · subst j
        simpa using hi
      · simp [Finsupp.single_eq_of_ne hj]
    · obtain ⟨d,hd,hde⟩ := (nonface_divisor_iff K facets e).mpr hf
      exact ⟨d,Or.inl hd,hde⟩

private def boxCoordinates (facets : Finset (Finset ι)) (r : ι → ℕ) :
    MvPolynomial ι K →ₗ[K] (↥(allowedBox facets r) → K) :=
  LinearMap.pi fun x => MvPolynomial.lcoeff K (boxExponent x.val)

private theorem ker_boxCoordinates (facets : Finset (Finset ι)) (r : ι → ℕ) :
    LinearMap.ker (boxCoordinates K facets r) = (truncatedFaceIdeal K facets r).restrictScalars K := by
  ext p
  rw [LinearMap.mem_ker,Submodule.restrictScalars_mem,mem_truncatedFaceIdeal]
  constructor
  · rintro h e he ⟨hf,hb⟩
    let x (i : ι) : Fin (r i+1) := ⟨e i,Nat.lt_succ_of_le (hb i)⟩
    have he' : boxExponent x = e := by ext i; rfl
    have hx : x ∈ allowedBox facets r := mem_filter.mpr ⟨mem_univ _,he' ▸ hf⟩
    have hz := congrFun h ⟨x,hx⟩
    change coeff (boxExponent x) p = 0 at hz
    rw [he'] at hz
    exact (mem_support_iff.mp he) hz
  · intro h
    funext x
    change coeff (boxExponent x.val) p = 0
    by_contra hn
    exact h _ (mem_support_iff.mpr hn) ⟨(mem_filter.mp x.property).2,
      fun i => Nat.le_of_lt_succ (x.val i).isLt⟩

private theorem boxCoordinates_surjective (facets : Finset (Finset ι)) (r : ι → ℕ) :
    Function.Surjective (boxCoordinates K facets r) := by
  intro f
  refine ⟨∑ x, monomial (boxExponent x.val) (f x),?_⟩
  funext x
  change coeff (boxExponent x.val) (∑ y, monomial (boxExponent y.val) (f y)) = f x
  rw [coeff_sum]
  have he (y : ↥(allowedBox facets r)) : boxExponent y.val = boxExponent x.val ↔ y = x :=
    (boxExponent_injective r).eq_iff.trans Subtype.val_inj
  simp [coeff_monomial,he]

/-- Standard monomial coordinates of the actual Artinian quotient. -/
def truncatedFaceCoordinates (facets : Finset (Finset ι)) (r : ι → ℕ) :
    (MvPolynomial ι K ⧸ truncatedFaceIdeal K facets r) ≃ₗ[K] (↥(allowedBox facets r) → K) :=
  (Submodule.quotEquivOfEq _ _ (ker_boxCoordinates K facets r).symm).trans
    ((boxCoordinates K facets r).quotKerEquivOfSurjective (boxCoordinates_surjective K facets r))

/-- The colength with independently chosen coordinate truncations is a multiaffine
face enumerator. Its values count standard monomials over every coefficient field. -/
theorem truncatedFace_finrank (facets : Finset (Finset ι)) (r : ι → ℕ) :
    Module.finrank K (MvPolynomial ι K ⧸ truncatedFaceIdeal K facets r) =
      ∑ s ∈ facetFaces facets, ∏ i ∈ s, r i := by
  rw [(truncatedFaceCoordinates K facets r).finrank_eq,finrank_pi,Fintype.card_coe]
  let D := fun i => ({0} : Finset (Fin (r i+1)))ᶜ
  have he (x : ∀ i, Fin (r i+1)) : matchSet D x = (boxExponent x).support := by
    ext i
    simp [matchSet,D,Finsupp.mem_support_iff,boxExponent_apply,Fin.ext_iff]
  have h := card_arrangementWords D (facetFaces facets)
  have hW : allowedBox facets r = arrangementWords D (facetFaces facets) := by
    ext x
    simp [arrangementWords,allowedBox,he,mem_facetFaces]
  rw [hW,h]
  refine sum_congr rfl fun s _ => ?_
  simp [D,card_compl,prod_ite]

/-- At the order of a finite field the actual point count equals the length
of the quotient by the corresponding powers of the coordinate functions. -/
theorem truncatedFace_finrank_eq_character_count (F : Type*) [Field F] [Fintype F]
    (facets : Finset (Finset ι)) :
    Module.finrank K (MvPolynomial ι K ⧸ truncatedFaceIdeal K facets (fun _ => Fintype.card F-1)) =
      Nat.card (stanleyReisnerRing F facets →ₐ[F] F) := by
  rw [truncatedFace_finrank,card_stanleyReisner_characters]
  simp
/-- Frobenius images of the homogeneous coordinate ideal give exactly the
pure-power cuts, even in the presence of nonface relations. -/
theorem truncatedFaceIdeal_frobenius (facets : Finset (Finset ι)) (p e : ℕ)
    [Fact p.Prime] [CharP K p] :
    truncatedFaceIdeal K facets (fun _ => p^e-1) = stanleyReisnerIdeal K facets ⊔
      (Ideal.span (Set.range (X : ι → MvPolynomial ι K))).map
        (iterateFrobenius (MvPolynomial ι K) p e) := by
  have hpos := pow_pos (Fact.out : p.Prime).pos e
  rw [truncatedFaceIdeal_eq,Ideal.map_span,Set.image_range]
  congr 2
  funext i
  simp only [Function.comp_apply,iterateFrobenius_def,Nat.sub_add_cancel hpos]

/-- The actual quotient of the face ring by powers of its coordinate
generators agrees with the single ambient monomial-ideal presentation. -/
def truncatedFaceAlgEquiv (facets : Finset (Finset ι)) (r : ι → ℕ) :
    (stanleyReisnerRing K facets ⧸ Ideal.span (Set.range fun i =>
      (srVertexX K facets i)^(r i+1))) ≃ₐ[K] (MvPolynomial ι K ⧸ truncatedFaceIdeal K facets r) := by
  let I := stanleyReisnerIdeal K facets
  let J := Ideal.span (Set.range fun i => (X i : MvPolynomial ι K)^(r i+1))
  have he : J.map (Ideal.Quotient.mkₐ K I) =
      Ideal.span (Set.range fun i => (srVertexX K facets i)^(r i+1)) := by
    rw [Ideal.map_span,Set.image_range]
    congr 2
    funext i
    exact map_pow _ _ _
  rw [← he,truncatedFaceIdeal_eq]
  exact DoubleQuot.quotQuotEquivQuotSupₐ K I J

/-- Hilbert--Kunz values at every Frobenius power, as actual colengths in
the face ring. The expression counts each coordinate torus once. -/
theorem faceRing_hilbertKunz (facets : Finset (Finset ι)) (p e : ℕ) [Fact p.Prime] [CharP K p] :
    Module.finrank K (stanleyReisnerRing K facets ⧸ Ideal.span
      (Set.range fun i => (srVertexX K facets i)^(p^e))) =
      ∑ s ∈ facetFaces facets, (p^e-1)^s.card := by
  have hpos := pow_pos (Fact.out : p.Prime).pos e
  have he := (truncatedFaceAlgEquiv K facets (fun _ => p^e-1)).toLinearEquiv.finrank_eq
  simp only [Nat.sub_add_cancel hpos] at he
  rw [he,truncatedFace_finrank]
  simp

open Filter Topology

/-- The Frobenius-normalized colength tends to the number of faces of maximal
dimension. The formula also applies when the face family is empty. -/
theorem faceRing_hilbertKunz_multiplicity (facets : Finset (Finset ι)) (p : ℕ)
    [Fact p.Prime] [CharP K p] :
    let S := facetFaces facets
    let D := S.sup Finset.card
    Tendsto (fun e : ℕ => (Module.finrank K (stanleyReisnerRing K facets ⧸ Ideal.span
        (Set.range fun i => (srVertexX K facets i)^(p^e))):ℝ) / ((p:ℝ)^e)^D)
      atTop (𝓝 ((S.filter fun s => s.card=D).card:ℝ)) := by
  let S := facetFaces facets
  let D := S.sup Finset.card
  let q (e : ℕ) := (p:ℝ)^e
  have hp : 1 < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hq (e : ℕ) : 0 < q e := pow_pos (zero_lt_one.trans hp) e
  have hlim : Tendsto (fun e => (q e)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hp)
  have hnorm (e : ℕ) {k : ℕ} (hk : k ≤ D) :
      (q e-1)^k/(q e)^D = (1-(q e)⁻¹)^k*((q e)⁻¹)^(D-k) := by
    have he : D = k+(D-k) := by omega
    conv_lhs => rw [he,pow_add]
    rw [show 1-(q e)⁻¹ = (q e-1)/(q e) by field_simp [(hq e).ne'],div_pow,inv_pow]
    ring
  have hterm (s : Finset ι) (hs : s ∈ S) :
      Tendsto (fun e => (q e-1)^s.card/(q e)^D) atTop (𝓝 (if s.card=D then 1 else 0)) := by
    have hk : s.card ≤ D := le_sup hs
    simp_rw [hnorm _ hk]
    have h := ((tendsto_const_nhds.sub hlim).pow s.card).mul (hlim.pow (D-s.card))
    by_cases he : s.card=D
    · simpa [he] using h
    · simpa [he,zero_pow (Nat.sub_ne_zero_of_lt (lt_of_le_of_ne hk he))] using h
  have hsum := tendsto_finsetSum S hterm
  have ht : (∑ s ∈ S, if s.card=D then (1:ℝ) else 0) = (S.filter fun s => s.card=D).card := by
    simp only [← sum_filter,sum_const,nsmul_eq_mul,mul_one]
  rw [ht] at hsum
  refine hsum.congr' (Eventually.of_forall fun e => ?_)
  rw [faceRing_hilbertKunz,Nat.cast_sum,sum_div]
  refine sum_congr rfl fun s _ => ?_
  simp only [Nat.cast_pow,Nat.cast_sub (pow_pos (Fact.out : p.Prime).pos e),Nat.cast_one,q]

end
end GaloisForLFunctions.HTGeometry
