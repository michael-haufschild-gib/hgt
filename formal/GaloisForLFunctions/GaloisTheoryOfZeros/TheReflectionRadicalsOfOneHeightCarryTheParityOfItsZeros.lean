import GaloisForLFunctions.GaloisTheoryOfZeros.TheFibreFieldsOverThePrimeTracesAreFiniteGaloisAndGenerateTheSpectralField
import GaloisForLFunctions.GaloisTheoryOfZeros.ConjugationIsCentralAtAZeroIffItsOrdinateValueLiesInThePrimeTraceField

/-!
# The reflection radicals of one height carry the parity of its zeros

`B` is the prime trace field, `G = Gal(E/B)`. The reflection radical of a zero at a prime `p` is
`d_p(ρ) = p^ρ − p^{1−ρ}`; its square `(p^ρ − p^{1−ρ})²` is the reflection radicand, and the lift
of `ρ ↦ 1 − ρ` to `G` is governed by the square relations among the radicands. For a height `t`
let `U_t` be the finite set of zeros with `Im ρ = t` and
`A_{t,p} = ∏_{ρ ∈ U_t} (p^ρ − p^{1−ρ})`, so that `A_{t,p}²` is the product of the radicands of
height `t`.

* **Conjugation** (`primeTraceConjugation_heightReflectionProduct`).
  `c(A_{t,p}) = (−1)^{|U_t|} A_{t,p}`: conjugation followed by the functional equation permutes
  `U_t` (as `ρ ↦ 1 − ρ̄`), and each radical changes sign.
* **The source class** (`heightReflectionProduct_map`, `heightReflectionProduct_mul_self_mem`).
  Every `σ ∈ G` sends `A_{t,p}` to `±A_{t,p}`; the product of the radicands of height `t` lies
  in `B`.
* **Parity of a height** (`odd_card_primeUpperFibre_iff`). `|U_t|` is odd iff `½ + it` is a zero:
  `ρ ↦ 1 − ρ̄` pairs the off-line zeros of `U_t`.
* **Forced non-squares** (`exists_prime_radicand_product_not_square`). If `½ + it` is a zero,
  then for some prime `p` the product of the radicands of height `t` is a negative element of
  `B` that is not a square in `B`.
* **Lifts** (`lift_heightReflectionProduct`). A lift of the reflection acts on every `A_{t,p}` as
  conjugation does.

The class of the product of the radicands of one height in `B^×/B^{×2}` is thus read off from the
zeros of that height: nontrivial and negative whenever the height carries a critical zero.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
open scoped BigOperators Classical
namespace GaloisForLFunctions.GaloisTheoryOfZeros

local notation "B" => primeTraceField
local notation "E" => primeTraceExtension
local notation "G" => (E ≃ₐ[B] E)
local instance : IsGalois B E := ⟨⟩

/-! ## The zeros of one ordinate and the mirror `ρ ↦ 1 − ρ̄` -/

/-- The zeros with `Im ρ = t`. -/
def primeUpperFibre (t : ℝ) : Finset XiDivisorSupport :=
  (ordinateFibreCopies t).image fun q => q.1

theorem mem_primeUpperFibre {t : ℝ} {ρ : XiDivisorSupport} :
    ρ ∈ primeUpperFibre t ↔ (ρ : ℂ).im = t := by
  rw [primeUpperFibre, Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [← xiSpectralPoint_re_eq_im]
    exact (mem_ordinateFibreCopies t q).1 hq
  · intro h
    refine ⟨primeTraceSupportCopy ρ, (mem_ordinateFibreCopies t _).2 ?_, rfl⟩
    rw [xiSpectralPoint_re_eq_im]
    exact h

/-- The mirror `ρ ↦ 1 − ρ̄`, which keeps the ordinate and reflects the real part. -/
def xiZeroMirror (ρ : XiDivisorSupport) : XiDivisorSupport :=
  xiZeroReflectEquiv (xiZeroConjEquiv ρ)

theorem xiZeroMirror_coe (ρ : XiDivisorSupport) :
    (xiZeroMirror ρ : ℂ) = 1 - starRingEnd ℂ (ρ : ℂ) := rfl

theorem xiZeroMirror_im (ρ : XiDivisorSupport) : (xiZeroMirror ρ : ℂ).im = (ρ : ℂ).im := by
  rw [xiZeroMirror_coe, Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub, neg_neg]

theorem xiZeroMirror_re (ρ : XiDivisorSupport) : (xiZeroMirror ρ : ℂ).re = 1 - (ρ : ℂ).re := by
  rw [xiZeroMirror_coe, Complex.sub_re, Complex.one_re, Complex.conj_re]

theorem xiZeroMirror_mirror (ρ : XiDivisorSupport) : xiZeroMirror (xiZeroMirror ρ) = ρ :=
  Subtype.ext (by
    rw [xiZeroMirror_coe, xiZeroMirror_coe, map_sub, map_one, Complex.conj_conj]
    ring)

theorem xiZeroMirror_mem {t : ℝ} {ρ : XiDivisorSupport} (h : ρ ∈ primeUpperFibre t) :
    xiZeroMirror ρ ∈ primeUpperFibre t :=
  mem_primeUpperFibre.2 ((xiZeroMirror_im ρ).trans (mem_primeUpperFibre.1 h))

theorem prod_primeUpperFibre_mirror (t : ℝ) (f : XiDivisorSupport → E) :
    ∏ ρ ∈ primeUpperFibre t, f (xiZeroMirror ρ) = ∏ ρ ∈ primeUpperFibre t, f ρ :=
  Finset.prod_nbij' xiZeroMirror xiZeroMirror (fun _ h => xiZeroMirror_mem h)
    (fun _ h => xiZeroMirror_mem h) (fun ρ _ => xiZeroMirror_mirror ρ)
    (fun ρ _ => xiZeroMirror_mirror ρ) fun _ _ => rfl

/-! ## The product of the reflection radicals of one height -/

/-- `A_{t,p} = ∏_{Im ρ = t} (p^ρ − p^{1−ρ})`. -/
def primeHeightReflectionProduct (p : Nat.Primes) (t : ℝ) : E :=
  ∏ ρ ∈ primeUpperFibre t, primeReflectionDifference p ρ

/-- The reflection radicand `(p^ρ − p^{1−ρ})²`. -/
def primeReflectionSquare (p : Nat.Primes) (ρ : XiDivisorSupport) : E :=
  primeReflectionDifference p ρ * primeReflectionDifference p ρ

theorem primeReflectionSquare_reflect (p : Nat.Primes) (ρ : XiDivisorSupport) :
    primeReflectionSquare p (xiZeroReflectEquiv ρ) = primeReflectionSquare p ρ := by
  rw [primeReflectionSquare, primeReflectionSquare, primeReflectionDifference_reflection,
    neg_mul_neg]

/-- `A_{t,p}²` is the product of the radicands of height `t`. -/
theorem heightReflectionProduct_mul_self (p : Nat.Primes) (t : ℝ) :
    primeHeightReflectionProduct p t * primeHeightReflectionProduct p t =
      ∏ ρ ∈ primeUpperFibre t, primeReflectionSquare p ρ := by
  rw [primeHeightReflectionProduct, ← Finset.prod_mul_distrib]
  rfl

/-- Conjugation sends the radical of `ρ` to minus the radical of `1 − ρ̄`. -/
theorem primeTraceConjugation_reflectionDifference (p : Nat.Primes) (ρ : XiDivisorSupport) :
    primeTraceConjugation (primeReflectionDifference p ρ) =
      -1 * primeReflectionDifference p (xiZeroMirror ρ) := by
  rw [neg_one_mul, primeReflectionDifference_map, primeTraceZeroMap_conjugation, xiZeroMirror,
    primeReflectionDifference_reflection, neg_neg]

/-- **Conjugation.** `c(A_{t,p}) = (−1)^{|U_t|} A_{t,p}`. -/
theorem primeTraceConjugation_heightReflectionProduct (p : Nat.Primes) (t : ℝ) :
    primeTraceConjugation (primeHeightReflectionProduct p t) =
      (-1) ^ (primeUpperFibre t).card * primeHeightReflectionProduct p t := by
  have h1 : ∏ ρ ∈ primeUpperFibre t, primeTraceConjugation (primeReflectionDifference p ρ) =
      ∏ ρ ∈ primeUpperFibre t, (-1 * primeReflectionDifference p (xiZeroMirror ρ)) :=
    Finset.prod_congr rfl fun ρ _ => primeTraceConjugation_reflectionDifference p ρ
  rw [primeHeightReflectionProduct, map_prod, h1, Finset.prod_mul_distrib, Finset.prod_const,
    prod_primeUpperFibre_mirror t (primeReflectionDifference p)]

/-- Every arithmetic automorphism permutes the radicands of height `t`: it fixes `A_{t,p}²`. -/
theorem heightReflectionProduct_map_mul_self (p : Nat.Primes) (t : ℝ) (σ : G) :
    σ (primeHeightReflectionProduct p t) * σ (primeHeightReflectionProduct p t) =
      primeHeightReflectionProduct p t * primeHeightReflectionProduct p t := by
  have hσ : Function.Injective (primeTraceZeroMap σ) := (primeTraceZeroPermutation σ).injective
  -- `f ρ` is `σρ` or `1 − σρ`, whichever has ordinate `t`
  let f : XiDivisorSupport → XiDivisorSupport := fun ρ =>
    if (primeTraceZeroMap σ ρ : ℂ).im = t then primeTraceZeroMap σ ρ
    else xiZeroReflectEquiv (primeTraceZeroMap σ ρ)
  have hfD : ∀ ρ, primeReflectionSquare p (f ρ) = primeReflectionSquare p (primeTraceZeroMap σ ρ) :=
    fun ρ => by
      simp only [f]
      split_ifs
      · rfl
      · exact primeReflectionSquare_reflect p _
  have hfU : ∀ ρ ∈ primeUpperFibre t, f ρ ∈ primeUpperFibre t := by
    intro ρ hρ
    have hi := abs_eq_abs.1 ((primeTraceZeroMap_height σ ρ).trans
      (by rw [mem_primeUpperFibre.1 hρ]))
    simp only [f]
    split_ifs with h
    · exact mem_primeUpperFibre.2 h
    · refine mem_primeUpperFibre.2 ?_
      rw [xiZeroReflectEquiv_apply, Complex.sub_im, Complex.one_im]
      rcases hi with hi | hi
      · exact (h hi).elim
      · linarith only [hi]
  have hinj : Set.InjOn f (primeUpperFibre t) := by
    intro a ha b hb hab
    have ha' := mem_primeUpperFibre.1 (Finset.mem_coe.1 ha)
    have hb' := mem_primeUpperFibre.1 (Finset.mem_coe.1 hb)
    have ht : t ≠ 0 := fun h0 => xi_divisor_support_im_ne_zero a (ha'.trans h0)
    -- `σa = 1 − σb` would force `Im a = −Im b`
    have hcross : ∀ x y : XiDivisorSupport, (x : ℂ).im = t → (y : ℂ).im = t →
        primeTraceZeroMap σ x ≠ xiZeroReflectEquiv (primeTraceZeroMap σ y) := by
      intro x y hx hy e
      rw [← primeTraceZeroMap_reflection] at e
      have hi := congrArg (fun z : XiDivisorSupport => (z : ℂ).im) (hσ e)
      change (x : ℂ).im = (1 - (y : ℂ)).im at hi
      rw [Complex.sub_im, Complex.one_im, hx, hy] at hi
      exact ht (by linarith only [hi])
    simp only [f] at hab
    split_ifs at hab
    · exact hσ hab
    · exact (hcross a b ha' hb' hab).elim
    · exact (hcross b a hb' ha' hab.symm).elim
    · exact hσ (xiZeroReflectEquiv.injective hab)
  have himg : (primeUpperFibre t).image f = primeUpperFibre t :=
    Finset.eq_of_subset_of_card_le
      (fun x hx => by
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hx
        exact hfU ρ hρ)
      (by rw [Finset.card_image_of_injOn hinj])
  have hsq : ∀ τ : G, τ (primeHeightReflectionProduct p t) * τ (primeHeightReflectionProduct p t) =
      ∏ ρ ∈ primeUpperFibre t, primeReflectionSquare p (primeTraceZeroMap τ ρ) := by
    intro τ
    rw [primeHeightReflectionProduct, map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun ρ _ => by
      simp only [primeReflectionDifference_map, primeReflectionSquare]
  calc σ (primeHeightReflectionProduct p t) * σ (primeHeightReflectionProduct p t)
      = ∏ ρ ∈ primeUpperFibre t, primeReflectionSquare p (primeTraceZeroMap σ ρ) := hsq σ
    _ = ∏ ρ ∈ primeUpperFibre t, primeReflectionSquare p (f ρ) :=
        Finset.prod_congr rfl fun ρ _ => (hfD ρ).symm
    _ = ∏ x ∈ (primeUpperFibre t).image f, primeReflectionSquare p x :=
        (Finset.prod_image hinj).symm
    _ = ∏ x ∈ primeUpperFibre t, primeReflectionSquare p x := by rw [himg]
    _ = primeHeightReflectionProduct p t * primeHeightReflectionProduct p t :=
        (heightReflectionProduct_mul_self p t).symm

/-- **The source class.** Every arithmetic automorphism sends `A_{t,p}` to `±A_{t,p}`. -/
theorem heightReflectionProduct_map (p : Nat.Primes) (t : ℝ) (σ : G) :
    σ (primeHeightReflectionProduct p t) = primeHeightReflectionProduct p t ∨
      σ (primeHeightReflectionProduct p t) = -primeHeightReflectionProduct p t := by
  have h := heightReflectionProduct_map_mul_self p t σ
  have h0 : (σ (primeHeightReflectionProduct p t) - primeHeightReflectionProduct p t) *
      (σ (primeHeightReflectionProduct p t) + primeHeightReflectionProduct p t) = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact Or.inl (sub_eq_zero.1 h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h1)

/-- The product of the reflection radicands of height `t` lies in `B`. -/
theorem heightReflectionProduct_mul_self_mem (p : Nat.Primes) (t : ℝ) :
    ((primeHeightReflectionProduct p t * primeHeightReflectionProduct p t : E) : ℂ) ∈ B :=
  (coe_mem_primeTraceField_iff_fixed _).2 fun σ => by
    rw [map_mul]
    exact heightReflectionProduct_map_mul_self p t σ

/-- **Lifts.** A lift of the reflection acts on `A_{t,p}` as conjugation does. -/
theorem lift_heightReflectionProduct {σ : G}
    (hσ : ∀ ρ, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ) (p : Nat.Primes) (t : ℝ) :
    σ (primeHeightReflectionProduct p t) =
      primeTraceConjugation (primeHeightReflectionProduct p t) := by
  have h1 : ∏ ρ ∈ primeUpperFibre t, σ (primeReflectionDifference p ρ) =
      ∏ ρ ∈ primeUpperFibre t, (-1 * primeReflectionDifference p ρ) :=
    Finset.prod_congr rfl fun ρ _ => by
      rw [primeReflectionDifference_map, hσ, primeReflectionDifference_reflection, neg_one_mul]
  rw [primeTraceConjugation_heightReflectionProduct, primeHeightReflectionProduct, map_prod, h1,
    Finset.prod_mul_distrib, Finset.prod_const]

/-! ## The parity of a height -/

/-- **Parity of a height.** The number of zeros of ordinate `t` is odd iff `½ + it` is a zero. -/
theorem odd_card_primeUpperFibre_iff (t : ℝ) :
    Odd (primeUpperFibre t).card ↔ ∃ ρ ∈ primeUpperFibre t, (ρ : ℂ).re = 1 / 2 := by
  set U := primeUpperFibre t
  have hsplit := Finset.card_filter_add_card_filter_not (s := U)
    fun ρ : XiDivisorSupport => (ρ : ℂ).re = 1 / 2
  have hC : (U.filter fun ρ : XiDivisorSupport => (ρ : ℂ).re = 1 / 2).card ≤ 1 :=
    Finset.card_le_one.2 fun a ha b hb => by
      rw [Finset.mem_filter] at ha hb
      exact Subtype.ext (Complex.ext (ha.2.trans hb.2.symm)
        ((mem_primeUpperFibre.1 ha.1).trans (mem_primeUpperFibre.1 hb.1).symm))
  -- the off-line zeros of the height: those left of the line and their mirrors
  let L := U.filter fun ρ : XiDivisorSupport => (ρ : ℂ).re < 1 / 2
  have hVL : (U.filter fun ρ : XiDivisorSupport => ¬ (ρ : ℂ).re = 1 / 2) =
      L ∪ L.image xiZeroMirror := by
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image, L]
    constructor
    · rintro ⟨hρ, hne⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨hρ, h⟩
      · refine Or.inr ⟨xiZeroMirror ρ, ⟨xiZeroMirror_mem hρ, ?_⟩, xiZeroMirror_mirror ρ⟩
        rw [xiZeroMirror_re]
        linarith only [h]
    · rintro (⟨hρ, h⟩ | ⟨x, ⟨hx, h⟩, rfl⟩)
      · exact ⟨hρ, h.ne⟩
      · refine ⟨xiZeroMirror_mem hx, ?_⟩
        rw [xiZeroMirror_re]
        intro e
        linarith only [h, e]
  have hdisj : Disjoint L (L.image xiZeroMirror) := by
    rw [Finset.disjoint_left]
    intro ρ hρ hρ'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hρ'
    have h1 := (Finset.mem_filter.1 hρ).2
    have h2 := (Finset.mem_filter.1 hx).2
    rw [xiZeroMirror_re] at h1
    linarith only [h1, h2]
  have hV : Even (U.filter fun ρ : XiDivisorSupport => ¬ (ρ : ℂ).re = 1 / 2).card := by
    rw [hVL, (Finset.card_union_eq_card_add_card).2 hdisj,
      Finset.card_image_of_injective _ (Function.LeftInverse.injective xiZeroMirror_mirror)]
    exact ⟨_, rfl⟩
  constructor
  · intro hodd
    by_contra hno
    have h0 : (U.filter fun ρ : XiDivisorSupport => (ρ : ℂ).re = 1 / 2).card = 0 :=
      Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun ρ hρ hc => hno ⟨ρ, hρ, hc⟩)
    rw [h0, zero_add] at hsplit
    rw [← hsplit] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) hV
  · rintro ⟨ρ, hρ, hc⟩
    have h1 : (U.filter fun ρ : XiDivisorSupport => (ρ : ℂ).re = 1 / 2).card = 1 :=
      le_antisymm hC (Finset.card_pos.2 ⟨ρ, Finset.mem_filter.2 ⟨hρ, hc⟩⟩)
    rw [← hsplit, h1]
    exact hV.one_add

/-! ## Forced non-squares -/

/-- If the height carries an odd number of zeros, `A_{t,p}` lies in `B` only when it vanishes. -/
theorem heightReflectionProduct_eq_zero_of_mem {p : Nat.Primes} {t : ℝ}
    (hodd : Odd (primeUpperFibre t).card) (h : (primeHeightReflectionProduct p t : ℂ) ∈ B) :
    primeHeightReflectionProduct p t = 0 := by
  have hc : primeTraceConjugation (primeHeightReflectionProduct p t) =
      -primeHeightReflectionProduct p t := by
    rw [primeTraceConjugation_heightReflectionProduct, hodd.neg_one_pow, neg_one_mul]
  have hfix := (coe_mem_primeTraceField_iff_fixed _).1 h primeTraceConjugation
  rw [hc] at hfix
  have hC : ((-primeHeightReflectionProduct p t : E) : ℂ) =
      (primeHeightReflectionProduct p t : ℂ) := congrArg (fun x : E => (x : ℂ)) hfix
  push_cast at hC
  have h2 : (2 : ℂ) * (primeHeightReflectionProduct p t : ℂ) = 0 := by
    linear_combination (-1 : ℂ) * hC
  exact Subtype.ext ((mul_eq_zero.1 h2).resolve_left two_ne_zero)

/-- At most one prime kills the radical of a zero: two would force `ρ = 1 − ρ`. -/
theorem reflectionDifference_ne_zero_of_ne (ρ : XiDivisorSupport) {p q : Nat.Primes}
    (hpq : p ≠ q) (hp : primeReflectionDifference p ρ = 0) :
    primeReflectionDifference q ρ ≠ 0 := by
  intro hq
  have h1 : (primeResidueValue p ρ : ℂ) = (primeResidueValue p (xiZeroReflectEquiv ρ) : ℂ) :=
    congrArg (fun x : E => (x : ℂ)) (sub_eq_zero.1 hp)
  have h2 : (primeResidueValue q ρ : ℂ) = (primeResidueValue q (xiZeroReflectEquiv ρ) : ℂ) :=
    congrArg (fun x : E => (x : ℂ)) (sub_eq_zero.1 hq)
  rw [primeResidueValue_coe, primeResidueValue_coe, xiZeroReflectEquiv_apply] at h1 h2
  have he : (ρ : ℂ) = 1 - (ρ : ℂ) :=
    two_prime_exponential_injective p.2 q.2 (fun h => hpq (Subtype.ext h)) (Prod.ext h1 h2)
  have hi := congrArg Complex.im he
  rw [Complex.sub_im, Complex.one_im] at hi
  exact xi_divisor_support_im_ne_zero ρ (by linarith only [hi])

/-- Some prime gives a nonzero product of the reflection radicals of height `t`. -/
theorem exists_prime_heightReflectionProduct_ne_zero (t : ℝ) :
    ∃ p : Nat.Primes, primeHeightReflectionProduct p t ≠ 0 := by
  let k : XiDivisorSupport → Nat.Primes := fun ρ =>
    if h : ∃ p : Nat.Primes, primeReflectionDifference p ρ = 0 then h.choose
    else ⟨2, Nat.prime_two⟩
  obtain ⟨p, hp⟩ := Infinite.exists_notMem_finset ((primeUpperFibre t).image k)
  refine ⟨p, Finset.prod_ne_zero_iff.2 fun ρ hρ h0 => hp (Finset.mem_image.2 ⟨ρ, hρ, ?_⟩)⟩
  have hex : ∃ p : Nat.Primes, primeReflectionDifference p ρ = 0 := ⟨p, h0⟩
  have hk : k ρ = hex.choose := dif_pos hex
  by_contra hne
  rw [hk] at hne
  exact reflectionDifference_ne_zero_of_ne ρ hne hex.choose_spec h0

/-- **Forced non-squares.** If `½ + it` is a zero, then for some prime `p` the product of the
reflection radicands `(p^ρ − p^{1−ρ})²` over the zeros of ordinate `t` is a negative element of
`B` that is not a square in `B`. -/
theorem exists_prime_radicand_product_not_square (t : ℝ)
    (h : ∃ ρ : XiDivisorSupport, (ρ : ℂ).re = 1 / 2 ∧ (ρ : ℂ).im = t) :
    ∃ p : Nat.Primes,
      ((primeHeightReflectionProduct p t * primeHeightReflectionProduct p t : E) : ℂ) ∈ B ∧
      ((primeHeightReflectionProduct p t * primeHeightReflectionProduct p t : E) : ℂ).re < 0 ∧
      ¬ ∃ b : E, (b : ℂ) ∈ B ∧
        b * b = primeHeightReflectionProduct p t * primeHeightReflectionProduct p t := by
  obtain ⟨ρ, hre, him⟩ := h
  have hodd : Odd (primeUpperFibre t).card :=
    (odd_card_primeUpperFibre_iff t).2 ⟨ρ, mem_primeUpperFibre.2 him, hre⟩
  obtain ⟨p, hA⟩ := exists_prime_heightReflectionProduct_ne_zero t
  refine ⟨p, heightReflectionProduct_mul_self_mem p t, ?_, ?_⟩
  · -- `A` is purely imaginary and nonzero
    have hc : primeTraceConjugation (primeHeightReflectionProduct p t) =
        -primeHeightReflectionProduct p t := by
      rw [primeTraceConjugation_heightReflectionProduct, hodd.neg_one_pow, neg_one_mul]
    have hC : starRingEnd ℂ (primeHeightReflectionProduct p t : ℂ) =
        -(primeHeightReflectionProduct p t : ℂ) := congrArg (fun x : E => (x : ℂ)) hc
    have hre0 : (primeHeightReflectionProduct p t : ℂ).re = 0 := by
      have := congrArg Complex.re hC
      rw [Complex.conj_re, Complex.neg_re] at this
      linarith only [this]
    have him0 : (primeHeightReflectionProduct p t : ℂ).im ≠ 0 := fun h0 =>
      hA (Subtype.ext (Complex.ext hre0 h0))
    push_cast
    rw [Complex.mul_re, hre0]
    linarith only [mul_self_pos.2 him0]
  · rintro ⟨b, hb, he⟩
    have h0 : (primeHeightReflectionProduct p t - b) *
        (primeHeightReflectionProduct p t + b) = 0 := by
      linear_combination (-1 : E) * he
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact hA (heightReflectionProduct_eq_zero_of_mem hodd (by rw [sub_eq_zero.1 h1]; exact hb))
    · refine hA (heightReflectionProduct_eq_zero_of_mem hodd ?_)
      rw [eq_neg_of_add_eq_zero_left h1]
      push_cast
      exact neg_mem hb

end GaloisForLFunctions.GaloisTheoryOfZeros
