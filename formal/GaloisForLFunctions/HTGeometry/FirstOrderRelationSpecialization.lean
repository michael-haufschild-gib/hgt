import Mathlib

/-!
# Irreducibility of a first-order relation descends from finite extensions of `ℂ(U)`

For `P = ∑_{i ∈ S} Aᵢ(U) V^(i₁) W^(i₂)` with complex polynomial coefficients and a ring map
`φ : ℂ(U) → R`, `relPolyVia S A φ` is `P(φ U, V, W)`, a polynomial in `W` over `R[V]`.

**Specialisation.**  If `P(φU, V, W)` factors over `F(V)` for some field `F` with positive-degree
factors, then it already factors in the same way over `K(V)` for a *finite* extension `K` of
`ℂ(U)`.  Gauss's lemma moves the factorization to `F[V][W]`; its finitely many coefficients
generate a finitely generated `ℂ(U)`-subalgebra `R ⊆ F`; a maximal ideal of `R` localized at the
product of two leading coefficients has a residue field `K`, finite over `ℂ(U)` by Zariski's lemma,
and reducing the factorization there keeps both degrees.

Consequently irreducibility of `P(U, V, W)` over `K(V)` for every finite extension `K` of `ℂ(U)`
implies irreducibility over `F(V)` for *every* field `F ⊇ ℂ(U)`.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ)

/-- `P(φ U, V, W)` as a polynomial in `W` over `R[V]`. -/
def relPolyVia {R : Type*} [CommRing R] (φ : RatFunc ℂ →+* R) : Polynomial (Polynomial R) :=
  ∑ i ∈ S, C (C (φ (algebraMap (Polynomial ℂ) (RatFunc ℂ) (A i))) * X ^ i.1) * X ^ i.2

/-- The relation over `R(V)`: irreducibility of `P(φ U, V, W)` over the rational function field. -/
def RelIrrVia {F : Type*} [Field F] (φ : RatFunc ℂ →+* F) : Prop :=
  Irreducible ((relPolyVia S A φ).map (algebraMap (Polynomial F) (RatFunc F)))

theorem relPolyVia_map {R R' : Type*} [CommRing R] [CommRing R'] (φ : RatFunc ℂ →+* R)
    (ψ : R →+* R') :
    (relPolyVia S A φ).map (mapRingHom ψ) = relPolyVia S A (ψ.comp φ) := by
  simp only [relPolyVia, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, coe_mapRingHom, RingHom.comp_apply]

variable {S A}

/-- The `W`-coefficient of `P(φU, V, W)` in degree `k`. -/
theorem coeff_relPolyVia {R : Type*} [CommRing R] (φ : RatFunc ℂ →+* R) (k : ℕ) :
    (relPolyVia S A φ).coeff k =
      ∑ i ∈ S.filter (fun i => i.2 = k),
        C (φ (algebraMap (Polynomial ℂ) (RatFunc ℂ) (A i))) * X ^ i.1 := by
  classical
  rw [relPolyVia, finsetSum_coeff, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [coeff_C_mul_X_pow]
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)

/-- The `W`-coefficient of `P(φU, V, W)` in the degree of any pair of `S` is nonzero: distinct
pairs over the same `W`-degree have distinct `V`-degrees. -/
theorem coeff_relPolyVia_ne_zero {F : Type*} [Field F] (φ : RatFunc ℂ →+* F)
    (hA : ∀ i ∈ S, A i ≠ 0) {i₀ : ℕ × ℕ} (hi₀ : i₀ ∈ S) :
    (relPolyVia S A φ).coeff i₀.2 ≠ 0 := by
  classical
  rw [coeff_relPolyVia]
  intro hzero
  have hc := congrArg (fun p : Polynomial F => p.coeff i₀.1) hzero
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at hc
  have hmem : i₀ ∈ S.filter (fun i => i.2 = i₀.2) := Finset.mem_filter.mpr ⟨hi₀, rfl⟩
  rw [Finset.sum_eq_single_of_mem i₀ hmem] at hc
  · rw [if_pos rfl] at hc
    have hinj := φ.injective
    have hA0 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (A i₀) ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
      exact hA i₀ hi₀
    exact hA0 (hinj (by rw [hc, map_zero]))
  · intro i hi hne
    rw [if_neg]
    intro h1
    exact hne (Prod.ext h1.symm (Finset.mem_filter.mp hi).2)

/-- Every `W`-degree of `P(φU, V, W)` is at most the maximal second coordinate. -/
theorem natDegree_relPolyVia_le {R : Type*} [CommRing R] (φ : RatFunc ℂ →+* R) (m : ℕ)
    (hm : ∀ i ∈ S, i.2 ≤ m) : (relPolyVia S A φ).natDegree ≤ m := by
  rw [relPolyVia]
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (hm i hi)

/-- The finite set of coefficients of coefficients of a polynomial over a polynomial ring. -/
def coeffCoeffs {F : Type*} [CommRing F] [DecidableEq F] (p : Polynomial (Polynomial F)) :
    Finset F :=
  p.support.biUnion fun i => (p.coeff i).support.image fun j => (p.coeff i).coeff j

theorem coeff_coeff_mem_coeffCoeffs {F : Type*} [CommRing F] [DecidableEq F]
    (p : Polynomial (Polynomial F))
    (i j : ℕ) (h : (p.coeff i).coeff j ≠ 0) : (p.coeff i).coeff j ∈ coeffCoeffs p := by
  have hi : i ∈ p.support := by
    rw [mem_support_iff]
    intro h0
    rw [h0, coeff_zero] at h
    exact h rfl
  exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image_of_mem _ (mem_support_iff.mpr h)⟩

/-- A polynomial over a polynomial ring whose coefficients of coefficients lie in a subalgebra comes
from that subalgebra. -/
theorem exists_map_eq_of_coeffCoeffs_subset {F : Type*} [Field F] [DecidableEq F]
    [Algebra (RatFunc ℂ) F]
    (R : Subalgebra (RatFunc ℂ) F) (p : Polynomial (Polynomial F))
    (hp : ∀ x ∈ coeffCoeffs p, x ∈ R) :
    ∃ pR : Polynomial (Polynomial R), pR.map (mapRingHom (algebraMap R F)) = p := by
  rw [← mem_lifts, lifts_iff_coeff_lifts]
  intro n
  have hn : p.coeff n ∈ lifts (algebraMap R F) := by
    rw [lifts_iff_coeff_lifts]
    intro m
    by_cases h : (p.coeff n).coeff m = 0
    · exact ⟨0, by rw [map_zero, h]⟩
    · exact ⟨⟨_, hp _ (coeff_coeff_mem_coeffCoeffs p n m h)⟩, rfl⟩
  obtain ⟨q, hq⟩ := (mem_lifts _).mp hn
  exact ⟨q, by rw [coe_mapRingHom, hq]⟩

/-- **Specialisation to a finite extension of `ℂ(U)`.**  A factorization of `P(φU, V, W)` over
`F[V]` with two factors of positive `W`-degree yields one over `K[V]`, `K` finite over `ℂ(U)`. -/
theorem exists_finite_specialization {F : Type} [Field F] (φ : RatFunc ℂ →+* F)
    (c : Polynomial F) (a b : Polynomial (Polynomial F))
    (ha : 1 ≤ a.natDegree) (hb : 1 ≤ b.natDegree)
    (hq : relPolyVia S A φ = C c * a * b) :
    ∃ (K : Type) (_ : Field K) (ψ : RatFunc ℂ →+* K) (c' : Polynomial K)
      (a' b' : Polynomial (Polynomial K)),
      ψ.Finite ∧ 1 ≤ a'.natDegree ∧ 1 ≤ b'.natDegree ∧ relPolyVia S A ψ = C c' * a' * b' := by
  classical
  letI : Algebra (RatFunc ℂ) F := φ.toAlgebra
  let T : Finset F := coeffCoeffs a ∪ coeffCoeffs b ∪ c.support.image c.coeff
  let R : Subalgebra (RatFunc ℂ) F := Algebra.adjoin (RatFunc ℂ) (T : Set F)
  have hTR : ∀ x ∈ T, x ∈ R := fun x hx => Algebra.subset_adjoin hx
  obtain ⟨aR, haR⟩ := exists_map_eq_of_coeffCoeffs_subset R a fun x hx =>
    hTR x (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
  obtain ⟨bR, hbR⟩ := exists_map_eq_of_coeffCoeffs_subset R b fun x hx =>
    hTR x (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
  obtain ⟨cR, hcR⟩ : ∃ cR : Polynomial R, cR.map (algebraMap R F) = c := by
    rw [← mem_lifts, lifts_iff_coeff_lifts]
    intro m
    by_cases h : c.coeff m = 0
    · exact ⟨0, by rw [map_zero, h]⟩
    · refine ⟨⟨_, hTR _ (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨m, mem_support_iff.mpr h, rfl⟩))⟩, rfl⟩
  let ι : R →+* F := algebraMap R F
  have hι : Function.Injective ι := Subtype.val_injective
  let φR : RatFunc ℂ →+* R := algebraMap (RatFunc ℂ) R
  have hφ : ι.comp φR = φ := by
    ext x
    rfl
  have hqR : relPolyVia S A φR = C cR * aR * bR := by
    apply Polynomial.map_injective (mapRingHom ι) (Polynomial.map_injective ι hι)
    rw [relPolyVia_map, hφ, hq, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
      coe_mapRingHom, hcR, haR, hbR]
  have haRdeg : aR.natDegree = a.natDegree := by
    rw [← haR, natDegree_map_eq_of_injective (Polynomial.map_injective ι hι)]
  have hbRdeg : bR.natDegree = b.natDegree := by
    rw [← hbR, natDegree_map_eq_of_injective (Polynomial.map_injective ι hι)]
  have haR0 : aR ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at haRdeg
    omega
  have hbR0 : bR ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hbRdeg
    omega
  let α : R := aR.leadingCoeff.leadingCoeff
  let β : R := bR.leadingCoeff.leadingCoeff
  have hα : α ≠ 0 := leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr haR0)
  have hβ : β ≠ 0 := leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hbR0)
  let D : R := α * β
  have hD : D ≠ 0 := mul_ne_zero hα hβ
  let RD := Localization.Away D
  haveI : IsDomain RD :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hD)
  haveI : Algebra.FiniteType (RatFunc ℂ) R :=
    Algebra.FiniteType.adjoin_of_finite (Finset.finite_toSet T)
  obtain ⟨M, hM⟩ := Ideal.exists_maximal RD
  let K := RD ⧸ M
  letI : Field K := Ideal.Quotient.field M
  haveI : Module.Finite (RatFunc ℂ) K := finite_of_finite_type_of_isJacobsonRing (RatFunc ℂ) K
  let θ : R →+* K := (Ideal.Quotient.mk M).comp (algebraMap R RD)
  have hψ : algebraMap (RatFunc ℂ) K = θ.comp φR := by
    ext x
    change algebraMap (RatFunc ℂ) K x = Ideal.Quotient.mk M (algebraMap R RD (φR x))
    rw [← Ideal.Quotient.mk_algebraMap, IsScalarTower.algebraMap_apply (RatFunc ℂ) R RD x]
  have hθD : θ D ≠ 0 := by
    have hunit : IsUnit (algebraMap R RD D) := IsLocalization.Away.algebraMap_isUnit D
    exact (hunit.map (Ideal.Quotient.mk M)).ne_zero
  have hθα : θ α ≠ 0 := fun h => hθD (by simp only [D, map_mul, h, zero_mul])
  have hθβ : θ β ≠ 0 := fun h => hθD (by simp only [D, map_mul, h, mul_zero])
  refine ⟨K, inferInstance, algebraMap (RatFunc ℂ) K, cR.map θ,
    aR.map (mapRingHom θ), bR.map (mapRingHom θ), RingHom.finite_algebraMap.mpr inferInstance,
    ?_, ?_, ?_⟩
  · rw [natDegree_map_of_leadingCoeff_ne_zero, haRdeg]
    · exact ha
    · intro h0
      apply hθα
      have := congrArg (fun p : Polynomial K => p.coeff aR.leadingCoeff.natDegree) h0
      simpa [coeff_map] using this
  · rw [natDegree_map_of_leadingCoeff_ne_zero, hbRdeg]
    · exact hb
    · intro h0
      apply hθβ
      have := congrArg (fun p : Polynomial K => p.coeff bR.leadingCoeff.natDegree) h0
      simpa [coeff_map] using this
  · rw [hψ, ← relPolyVia_map, hqR, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
      coe_mapRingHom]

/-- The `W`-degree of `P(φU, V, W)` is the largest second coordinate. -/
theorem natDegree_relPolyVia {F : Type*} [Field F] (φ : RatFunc ℂ →+* F)
    (hA : ∀ i ∈ S, A i ≠ 0) {i₀ : ℕ × ℕ} (hi₀ : i₀ ∈ S) (hmax : ∀ i ∈ S, i.2 ≤ i₀.2) :
    (relPolyVia S A φ).natDegree = i₀.2 :=
  le_antisymm (natDegree_relPolyVia_le φ i₀.2 hmax)
    (le_natDegree_of_ne_zero (coeff_relPolyVia_ne_zero φ hA hi₀))

/-- A primitive polynomial of degree zero is a unit. -/
theorem isUnit_of_isPrimitive_natDegree_eq_zero {R : Type*} [CommRing R] {p : Polynomial R}
    (hp : p.IsPrimitive) (h0 : p.natDegree = 0) : IsUnit p := by
  rw [eq_C_of_natDegree_eq_zero h0] at hp ⊢
  exact (hp (p.coeff 0) dvd_rfl).map C

/-- **Irreducibility of a first-order relation descends from finite extensions.**  If
`P(U, V, W)` is irreducible over `K(V)` for every finite extension `K` of `ℂ(U)`, it is irreducible
over `F(V)` for every field `F ⊇ ℂ(U)`. -/
theorem relIrrVia_of_finite (hA : ∀ i ∈ S, A i ≠ 0) {i₀ : ℕ × ℕ} (hi₀ : i₀ ∈ S)
    (hdeg : 1 ≤ i₀.2) (hmax : ∀ i ∈ S, i.2 ≤ i₀.2)
    (hfin : ∀ (K : Type) [Field K] (ψ : RatFunc ℂ →+* K), ψ.Finite → RelIrrVia S A ψ)
    {F : Type} [Field F] (φ : RatFunc ℂ →+* F) : RelIrrVia S A φ := by
  classical
  by_contra hnot
  set q := relPolyVia S A φ with hqdef
  have hqdeg : q.natDegree = i₀.2 := natDegree_relPolyVia φ hA hi₀ hmax
  have hq0 : q ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hqdeg
    omega
  have hcont : q.content ≠ 0 := by rwa [ne_eq, content_eq_zero_iff]
  have hprim := q.isPrimitive_primPart
  have hsplit := q.eq_C_content_mul_primPart
  have hpdeg : q.primPart.natDegree = q.natDegree := by
    conv_rhs => rw [hsplit]
    rw [natDegree_C_mul hcont]
  -- the primitive part is not irreducible
  have hpirr : ¬ Irreducible q.primPart := by
    intro hirr
    apply hnot
    have hmapirr := (hprim.irreducible_iff_irreducible_map_fraction_map
      (K := RatFunc F)).mp hirr
    have hassoc : Associated (q.primPart.map (algebraMap (Polynomial F) (RatFunc F)))
        (q.map (algebraMap (Polynomial F) (RatFunc F))) := by
      conv_rhs => rw [hsplit]
      rw [Polynomial.map_mul, Polynomial.map_C, mul_comm]
      refine associated_mul_unit_right _ _ (isUnit_C.mpr ?_)
      exact (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial F) (RatFunc F))).mpr
        hcont |>.isUnit
    exact hassoc.irreducible hmapirr
  have hpnu : ¬ IsUnit q.primPart := by
    intro hu
    have := natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨a, b, hab, hau, hbu⟩ : ∃ a b, q.primPart = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
    by_contra hall
    push Not at hall
    exact hpirr ⟨hpnu, fun a b h => by
      by_cases ha : IsUnit a
      · exact Or.inl ha
      · exact Or.inr (hall a b h ha)⟩
  have hadeg : 1 ≤ a.natDegree := by
    by_contra h0
    exact hau (isUnit_of_isPrimitive_natDegree_eq_zero
      (isPrimitive_of_dvd hprim ⟨b, hab⟩) (by omega))
  have hbdeg : 1 ≤ b.natDegree := by
    by_contra h0
    exact hbu (isUnit_of_isPrimitive_natDegree_eq_zero
      (isPrimitive_of_dvd hprim ⟨a, by rw [hab, mul_comm]⟩) (by omega))
  obtain ⟨K, _, ψ, c', a', b', hψ, ha', hb', hq'⟩ :=
    exists_finite_specialization (S := S) (A := A) φ q.content a b hadeg hbdeg
      (by rw [mul_assoc, ← hab, ← hsplit])
  have hirr := hfin K ψ hψ
  have hq'deg : (relPolyVia S A ψ).natDegree = i₀.2 := natDegree_relPolyVia ψ hA hi₀ hmax
  have hc' : c' ≠ 0 := by
    intro h0
    rw [hq', h0, map_zero, zero_mul, zero_mul, natDegree_zero] at hq'deg
    omega
  unfold RelIrrVia at hirr
  rw [hq', Polynomial.map_mul] at hirr
  rcases hirr.isUnit_or_isUnit rfl with hu | hu
  · have := natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.map_mul, Polynomial.map_C,
      natDegree_C_mul ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial K)
        (RatFunc K))).mpr hc'),
      natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial K) (RatFunc K))] at this
    omega
  · have := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial K) (RatFunc K))]
      at this
    omega

end

end GaloisForLFunctions.HTGeometry
