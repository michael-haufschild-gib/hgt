import GaloisForLFunctions.RHTower.DeningerDynSysWittGaloisFiniteOrbits
import GaloisForLFunctions.RHTower.DeningerDynSysWittRingAction
import GaloisForLFunctions.RHTower.DeningerRationalWittFatouIntersection

/-!
# Galois descent for the rational Witt ring

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.2(a)
(`t21n`) on the rational Witt *ring*: if a group `G` acts on a commutative ring `A` by ring
automorphisms with all orbits finite, then

`W_rat (A) ^ G = W_rat (A ^ G)`.

A rational Witt vector is a normalized fraction `P / Q` in the localization of `A[T]` at the
polynomials with constant coefficient one.  `G`-invariance of the fraction gives the cross relation
`σP · Q = σQ · P` (the denominators are non-zero-divisors, so the localization map is injective),
and `deningerPolyGaloisDescent` then replaces `P / Q` by the equivalent fraction

`α / β`,  `β = ∏_{R ∈ T} R`,  `α = P · ∏_{R ∈ T, R ≠ Q} R`,  `T = {σ Q | σ ∈ G}`,

whose numerator and denominator have `G`-invariant coefficients.  `deningerPolyLift` descends them
to the fixed subring, and the descended fraction maps back to the original Witt vector.
-/

namespace RHTower

open Finset

variable {G A : Type*} [Group G] [CommRing A] [MulSemiringAction G A]

/-- A polynomial all of whose coefficients lie in a subring descends to that subring. -/
theorem deningerPolyLift {B : Type*} [CommRing B] [Algebra B A] (P : Polynomial A)
    (h : ∀ n, ∃ b : B, algebraMap B A b = P.coeff n) :
    ∃ P₀ : Polynomial B, P₀.map (algebraMap B A) = P := by
  classical
  choose b hb using h
  refine ⟨∑ n ∈ Finset.range (P.natDegree + 1), Polynomial.monomial n (b n), ?_⟩
  ext n
  rw [Polynomial.coeff_map, Polynomial.finsetSum_coeff]
  by_cases hn : n ≤ P.natDegree
  · rw [Finset.sum_eq_single n]
    · rw [Polynomial.coeff_monomial, if_pos rfl, hb]
    · intro m _ hmn
      simp [Polynomial.coeff_monomial, hmn]
    · intro hcon
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)) hcon
  · rw [not_le] at hn
    have hsum : (∑ m ∈ Finset.range (P.natDegree + 1),
        (Polynomial.monomial m (b m) : Polynomial B).coeff n) = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      have hmn : m ≠ n := by
        intro hmn'
        rw [hmn'] at hm
        exact absurd (Finset.mem_range.mp hm) (by omega)
      simp [Polynomial.coeff_monomial, hmn]
    rw [hsum, map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt hn]

/-- **Deninger, Proposition 1.2(a), polynomial form.**  Given a `G`-invariant normalized fraction
`P / Q`, presented by the cross relation `σP · Q = σQ · P`, there is an equivalent normalized
fraction `α / β` whose numerator and denominator have `G`-invariant coefficients. -/
theorem deningerPolyGaloisDescent (horb : ∀ a : A, (MulAction.orbit G a).Finite)
    (P Q : Polynomial A) (hP0 : P.coeff 0 = 1) (hQ0 : Q.coeff 0 = 1)
    (hQreg : Q ∈ nonZeroDivisors (Polynomial A))
    (hcross : ∀ σ : G, deningerPolyAct σ P * Q = deningerPolyAct σ Q * P) :
    ∃ α β : Polynomial A,
      (∀ (σ : G) (n : ℕ), σ • α.coeff n = α.coeff n) ∧
      (∀ (σ : G) (n : ℕ), σ • β.coeff n = β.coeff n) ∧
      α.coeff 0 = 1 ∧ β.coeff 0 = 1 ∧ α * Q = P * β := by
  classical
  have hTfin := deningerPolyAct_range_finite horb Q
  set T : Finset (Polynomial A) := hTfin.toFinset with hT
  have hmemT : ∀ R : Polynomial A, R ∈ T ↔ ∃ σ : G, deningerPolyAct σ Q = R := by
    intro R
    rw [hT, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hQT : Q ∈ T := (hmemT Q).mpr ⟨1, deningerPolyAct_one Q⟩
  have hstable : ∀ τ : G, T.image (deningerPolyAct τ) = T := by
    intro τ
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro R hR
      obtain ⟨R', hR', rfl⟩ := Finset.mem_image.mp hR
      obtain ⟨σ, rfl⟩ := (hmemT R').mp hR'
      exact (hmemT _).mpr ⟨τ * σ, (deningerPolyAct_mul τ σ Q).symm ▸ rfl⟩
    · exact le_of_eq (Finset.card_image_of_injective T (deningerPolyAct_injective τ)).symm
  have hconst : ∀ R ∈ T, R.coeff 0 = 1 := by
    intro R hR
    obtain ⟨σ, rfl⟩ := (hmemT R).mp hR
    rw [deningerPolyAct_coeff, hQ0, smul_one]
  refine ⟨P * ∏ R ∈ T.erase Q, R, ∏ R ∈ T, R, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ n
    have key : deningerPolyAct σ (P * ∏ R ∈ T.erase Q, R) = P * ∏ R ∈ T.erase Q, R := by
      rw [map_mul, map_prod]
      have himg : (T.erase Q).image (deningerPolyAct σ) = T.erase (deningerPolyAct σ Q) := by
        rw [Finset.image_erase (deningerPolyAct_injective σ), hstable σ]
      have hinj : Set.InjOn (fun R : Polynomial A => deningerPolyAct σ R) ↑(T.erase Q) :=
        fun x _ y _ h => deningerPolyAct_injective σ h
      have hprod : ∏ R ∈ T.erase Q, deningerPolyAct σ R
          = ∏ R ∈ T.erase (deningerPolyAct σ Q), R := by
        rw [← himg]
        exact (Finset.prod_image (f := fun R : Polynomial A => R) hinj).symm
      rw [hprod]
      by_cases hfix : deningerPolyAct σ Q = Q
      · have hPfix : deningerPolyAct σ P = P := by
          have h := hcross σ
          rw [hfix] at h
          have hsub : (deningerPolyAct σ P - P) * Q = 0 := by
            rw [sub_mul, h]
            ring
          have hzero : deningerPolyAct σ P - P = 0 :=
            (mem_nonZeroDivisors_iff.mp hQreg).2 _ hsub
          exact sub_eq_zero.mp hzero
        rw [hfix, hPfix]
      · have h1 : Q ∈ T.erase (deningerPolyAct σ Q) :=
          Finset.mem_erase.mpr ⟨fun h => hfix h.symm, hQT⟩
        have h2 : deningerPolyAct σ Q ∈ T.erase Q :=
          Finset.mem_erase.mpr ⟨hfix, (hmemT _).mpr ⟨σ, rfl⟩⟩
        rw [← Finset.mul_prod_erase _ _ h1, ← Finset.mul_prod_erase _ _ h2,
          Finset.erase_right_comm]
        rw [← mul_assoc, ← mul_assoc, hcross σ]
        ring
    have h : (deningerPolyAct σ (P * ∏ R ∈ T.erase Q, R)).coeff n
        = (P * ∏ R ∈ T.erase Q, R).coeff n := by rw [key]
    rwa [deningerPolyAct_coeff] at h
  · intro σ n
    have key : deningerPolyAct σ (∏ R ∈ T, R) = ∏ R ∈ T, R := by
      rw [map_prod]
      have hinj : Set.InjOn (fun R : Polynomial A => deningerPolyAct σ R) ↑T :=
        fun x _ y _ h => deningerPolyAct_injective σ h
      conv_rhs => rw [← hstable σ]
      exact (Finset.prod_image (f := fun R : Polynomial A => R) hinj).symm
    have h : (deningerPolyAct σ (∏ R ∈ T, R)).coeff n = (∏ R ∈ T, R).coeff n := by rw [key]
    rwa [deningerPolyAct_coeff] at h
  · rw [Polynomial.mul_coeff_zero, deningerPolyProd_coeff_zero, hP0, one_mul,
      Finset.prod_congr rfl (fun R hR => hconst R (Finset.mem_of_mem_erase hR)),
      Finset.prod_const_one]
  · rw [deningerPolyProd_coeff_zero, Finset.prod_congr rfl hconst, Finset.prod_const_one]
  · have hsplit : (∏ R ∈ T, R) = Q * ∏ R ∈ T.erase Q, R :=
      (Finset.mul_prod_erase T (fun R => R) hQT).symm
    rw [hsplit]
    ring

open scoped DeningerWittRing

/-- **Deninger, Proposition 1.2(a) (`t21n`), for the rational Witt ring.**  If all orbits of `G`
on `A` are finite, every `G`-invariant rational Witt vector over `A` comes from a rational Witt
vector over the fixed subring: `W_rat (A) ^ G = W_rat (A ^ G)`. -/
theorem deningerWittRing_galoisDescent (horb : ∀ a : A, (MulAction.orbit G a).Finite)
    (w : DeningerCanonicalRationalWittRing A) (hw : ∀ σ : G, σ • w = w) :
    ∃ w₀ : DeningerCanonicalRationalWittRing (FixedPoints.subring A G),
      deningerCanonicalRationalWittMap
        (algebraMap (FixedPoints.subring A G) A) w₀ = w := by
  classical
  set B : Subring A := FixedPoints.subring A G with hB
  set u : DeningerRationalWittAdditive A := Additive.toMul w.additiveVal with hu
  obtain ⟨P, Q, hQmem, hP0, hQ0, hval⟩ :=
    deningerRationalWittAdditive_exists_normalized_fraction A u
  have hden := deningerRationalWittDenominators_le_nonZeroDivisors A
  have hinjLoc : Function.Injective
      (algebraMap (Polynomial A) (DeningerRationalWittLocalization A)) :=
    IsLocalization.injective _ hden
  have hspec : ((u.1 : (DeningerRationalWittLocalization A)ˣ)
        : DeningerRationalWittLocalization A)
      * algebraMap (Polynomial A) (DeningerRationalWittLocalization A) Q
      = algebraMap (Polynomial A) (DeningerRationalWittLocalization A) P := by
    rw [hval]
    exact IsLocalization.mk'_spec _ P ⟨Q, hQmem⟩
  -- the cross relation
  have hcross : ∀ σ : G, deningerPolyAct σ P * Q = deningerPolyAct σ Q * P := by
    intro σ
    have hfix : deningerRationalWittLocalizationMap (MulSemiringAction.toRingHom G A σ)
        ((u.1 : (DeningerRationalWittLocalization A)ˣ) : DeningerRationalWittLocalization A)
        = ((u.1 : (DeningerRationalWittLocalization A)ˣ)
            : DeningerRationalWittLocalization A) := by
      have h := hw σ
      have h2 : deningerRationalWittAdditiveMap (MulSemiringAction.toRingHom G A σ) u = u := by
        have h3 := congrArg DeningerCanonicalRationalWittRing.additiveVal h
        exact congrArg Additive.toMul h3
      exact congrArg (fun v : DeningerRationalWittAdditive A =>
        ((v.1 : (DeningerRationalWittLocalization A)ˣ)
          : DeningerRationalWittLocalization A)) h2
    have hmapped := congrArg
      (deningerRationalWittLocalizationMap (MulSemiringAction.toRingHom G A σ)) hspec
    rw [map_mul, hfix] at hmapped
    have hQmap : deningerRationalWittLocalizationMap (MulSemiringAction.toRingHom G A σ)
        (algebraMap (Polynomial A) (DeningerRationalWittLocalization A) Q)
        = algebraMap (Polynomial A) (DeningerRationalWittLocalization A)
            (deningerPolyAct σ Q) := by
      rw [deningerRationalWittLocalizationMap, IsLocalization.map_eq]
      rfl
    have hPmap : deningerRationalWittLocalizationMap (MulSemiringAction.toRingHom G A σ)
        (algebraMap (Polynomial A) (DeningerRationalWittLocalization A) P)
        = algebraMap (Polynomial A) (DeningerRationalWittLocalization A)
            (deningerPolyAct σ P) := by
      rw [deningerRationalWittLocalizationMap, IsLocalization.map_eq]
      rfl
    rw [hQmap, hPmap] at hmapped
    apply hinjLoc
    rw [map_mul, map_mul]
    calc algebraMap (Polynomial A) (DeningerRationalWittLocalization A) (deningerPolyAct σ P)
          * algebraMap (Polynomial A) (DeningerRationalWittLocalization A) Q
        = (((u.1 : (DeningerRationalWittLocalization A)ˣ)
              : DeningerRationalWittLocalization A)
            * algebraMap (Polynomial A) (DeningerRationalWittLocalization A)
                (deningerPolyAct σ Q))
          * algebraMap (Polynomial A) (DeningerRationalWittLocalization A) Q := by
          rw [hmapped]
      _ = algebraMap (Polynomial A) (DeningerRationalWittLocalization A) (deningerPolyAct σ Q)
          * (((u.1 : (DeningerRationalWittLocalization A)ˣ)
              : DeningerRationalWittLocalization A)
            * algebraMap (Polynomial A) (DeningerRationalWittLocalization A) Q) := by ring
      _ = algebraMap (Polynomial A) (DeningerRationalWittLocalization A) (deningerPolyAct σ Q)
          * algebraMap (Polynomial A) (DeningerRationalWittLocalization A) P := by rw [hspec]
  obtain ⟨α, β, hα, hβ, hα0, hβ0, hαβ⟩ :=
    deningerPolyGaloisDescent horb P Q hP0 hQ0 (hden hQmem) hcross
  -- descend the invariant fraction to the fixed subring
  obtain ⟨α₀, hα₀⟩ := deningerPolyLift (B := B) α (fun n => ⟨⟨α.coeff n, fun σ => hα σ n⟩, rfl⟩)
  obtain ⟨β₀, hβ₀⟩ := deningerPolyLift (B := B) β (fun n => ⟨⟨β.coeff n, fun σ => hβ σ n⟩, rfl⟩)
  have hinjB : Function.Injective (algebraMap B A) := Subtype.val_injective
  have hβ₀0 : β₀.coeff 0 = 1 := by
    apply hinjB
    have := congrArg (fun R : Polynomial A => R.coeff 0) hβ₀
    rw [Polynomial.coeff_map] at this
    rw [this, hβ0, map_one]
  have hα₀0 : α₀.coeff 0 = 1 := by
    apply hinjB
    have := congrArg (fun R : Polynomial A => R.coeff 0) hα₀
    rw [Polynomial.coeff_map] at this
    rw [this, hα0, map_one]
  have hβ₀mem : β₀ ∈ deningerRationalWittDenominators B := hβ₀0
  set x₀ : DeningerRationalWittLocalization B :=
    IsLocalization.mk' (DeningerRationalWittLocalization B) α₀ ⟨β₀, hβ₀mem⟩ with hx₀
  have hev : deningerRationalWittEvaluationZero B x₀ = 1 := by
    have hsp := IsLocalization.mk'_spec (DeningerRationalWittLocalization B) α₀ ⟨β₀, hβ₀mem⟩
    have h := congrArg (deningerRationalWittEvaluationZero B) hsp
    rw [map_mul, deningerRationalWittEvaluationZero_algebraMap,
      deningerRationalWittEvaluationZero_algebraMap, hβ₀0, hα₀0, mul_one] at h
    exact h
  have hunit : IsUnit x₀ :=
    deningerRationalWittLocalization_isUnit_of_evaluationZero_eq_one B x₀ hev
  refine ⟨⟨Additive.ofMul ⟨hunit.unit, ?_⟩⟩, ?_⟩
  · apply Units.ext
    show deningerRationalWittEvaluationZero B (hunit.unit : DeningerRationalWittLocalization B) = 1
    rw [hunit.unit_spec]
    exact hev
  · -- the image of the descended vector is `w`
    apply DeningerCanonicalRationalWittRing.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    show deningerRationalWittLocalizationMap (algebraMap B A)
        (hunit.unit : DeningerRationalWittLocalization B)
      = ((u.1 : (DeningerRationalWittLocalization A)ˣ) : DeningerRationalWittLocalization A)
    rw [hunit.unit_spec, hx₀, deningerRationalWittLocalizationMap, IsLocalization.map_mk']
    have hβmem : β ∈ deningerRationalWittDenominators A := hβ0
    have hQunit : IsUnit (algebraMap (Polynomial A) (DeningerRationalWittLocalization A) Q) :=
      IsLocalization.map_units _ ⟨Q, hQmem⟩
    rw [IsLocalization.mk'_eq_iff_eq_mul]
    have hmapα : (Polynomial.mapRingHom (algebraMap B A)) α₀ = α := hα₀
    have hmapβ : (Polynomial.mapRingHom (algebraMap B A)) β₀ = β := hβ₀
    show algebraMap (Polynomial A) (DeningerRationalWittLocalization A)
        ((Polynomial.mapRingHom (algebraMap B A)) α₀)
      = ((u.1 : (DeningerRationalWittLocalization A)ˣ) : DeningerRationalWittLocalization A)
        * algebraMap (Polynomial A) (DeningerRationalWittLocalization A)
          ((Polynomial.mapRingHom (algebraMap B A)) β₀)
    rw [hmapα, hmapβ]
    apply hQunit.mul_left_cancel
    calc algebraMap (Polynomial A) (DeningerRationalWittLocalization A) Q
          * algebraMap (Polynomial A) (DeningerRationalWittLocalization A) α
        = algebraMap (Polynomial A) (DeningerRationalWittLocalization A) (α * Q) := by
          rw [map_mul]; ring
      _ = algebraMap (Polynomial A) (DeningerRationalWittLocalization A) (P * β) := by
          rw [hαβ]
      _ = algebraMap (Polynomial A) (DeningerRationalWittLocalization A) β
          * (((u.1 : (DeningerRationalWittLocalization A)ˣ)
              : DeningerRationalWittLocalization A)
            * algebraMap (Polynomial A) (DeningerRationalWittLocalization A) Q) := by
          rw [hspec, map_mul]; ring
      _ = algebraMap (Polynomial A) (DeningerRationalWittLocalization A) Q
          * (((u.1 : (DeningerRationalWittLocalization A)ˣ)
              : DeningerRationalWittLocalization A)
            * algebraMap (Polynomial A) (DeningerRationalWittLocalization A) β) := by ring

end RHTower
