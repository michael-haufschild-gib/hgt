/-
Quadratic mask ideals adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticSieve.QuadraticRaysAndIdeals

/-!
# Quadratic mask ideals

Mask ideals `quadraticMaskIdeal`, column rays and canonical quadratic pair ideals. Equal
conductor rays agree on Eisenstein units and multiply to a ray with trivial Gauss phase;
squarefree ideal balls and the nonzero-lattice decay of radial sources.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SchwartzPlanePoisson
open Eisenstein QuadraticPhase.Eisenstein

lemma principalTraceChar_star (c : O) (hc : c ≠ 0) (x : O ⧸ Ideal.span {c}) :
    star (principalTraceChar c hc x) = principalTraceChar c hc (-x) := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_neg, principalTraceChar_apply, principalTraceChar_apply,
    Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_neg, neg_div, Rat.cast_neg, map_mul, map_ofNat, map_ratCast,
    Complex.conj_ofReal, Complex.conj_I]
  ring

lemma quadraticTraceGauss_star (c : O) (hc : c ≠ 0) :
    star (quadraticTraceGauss c hc) = quadraticTraceTwist c hc (-1) := by
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  change star (∑ x : O ⧸ Ideal.span {c}, principalTraceChar c hc (x ^ 2)) =
    ∑ x : O ⧸ Ideal.span {c}, principalTraceChar c hc (Ideal.Quotient.mk _ (-1) * x ^ 2)
  simp only [star_sum, principalTraceChar_star, map_neg, map_one, neg_one_mul]

/-- The value at minus one is determined by the fixed quadratic Gauss phase. -/
lemma prime_quadratic_neg_one_phase {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) :
    primeCuspRowCharacter p (fun i => complexQuadraticChar (Ideal.span {p i})) (-1) *
      fixedDualAverage (∏ i, p i) = star (fixedDualAverage (∏ i, p i)) := by
  let c := ∏ i, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hn : (‖ringComplex c‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (ringComplex_ne_zero hc))
  have hG : quadraticTraceGauss c hc = (‖ringComplex c‖ : ℂ) * fixedDualAverage c := by
    have h := normalizedQuadraticTraceGauss_eq_fixedDualAverage c hc
    exact ((div_eq_iff hn).mp h).trans (mul_comm _ _)
  have ht := prime_quadratic_trace_twist p hp hinj hodd (-1)
    (show IsCoprime (∏ i, p i) (-1) from ⟨0, -1, by ring⟩)
  change quadraticTraceTwist c hc (-1) = _ at ht
  rw [← quadraticTraceGauss_star, hG] at ht
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal] at ht
  change _ = _ * ((‖ringComplex c‖ : ℂ) * fixedDualAverage c) at ht
  apply mul_right_cancel₀ hn
  calc
    _ = primeCuspRowCharacter p (fun i => complexQuadraticChar (Ideal.span {p i})) (-1) *
        ((‖ringComplex c‖ : ℂ) * fixedDualAverage c) := by ring
    _ = star (fixedDualAverage c) * (‖ringComplex c‖ : ℂ) := by
      simpa only [Complex.star_def] using ht.symm

lemma canonicalQuadraticRow_phase_norm (I : QuadraticIdeal) :
    ‖fixedDualAverage (primaryIdealGenerator I.val)‖ = 1 := by
  have h := prime_quadratic_phase_norm (fun P : quadraticIdealSupport I => quadraticPrimeGenerator P.val)
    (fun P => quadraticPrimeGenerator_ne_zero P.val)
    (quadraticPrimeGenerator_span_injective.comp Subtype.val_injective)
    (fun P => quadraticPrimeGenerator_odd P.val)
  simpa only [Finset.prod_coe_sort, quadraticIdealSupport_product] using h

lemma canonicalQuadraticRow_neg_one_phase (I : QuadraticIdeal) :
    canonicalQuadraticRow I (-1) * fixedDualAverage (primaryIdealGenerator I.val) =
      star (fixedDualAverage (primaryIdealGenerator I.val)) := by
  have h := prime_quadratic_neg_one_phase (fun P : quadraticIdealSupport I => quadraticPrimeGenerator P.val)
    (fun P => quadraticPrimeGenerator_ne_zero P.val)
    (quadraticPrimeGenerator_span_injective.comp Subtype.val_injective)
    (fun P => quadraticPrimeGenerator_odd P.val)
  have hrow : primeCuspRowCharacter
      (fun P : quadraticIdealSupport I => quadraticPrimeGenerator P.val)
      (fun P => complexQuadraticChar (Ideal.span {quadraticPrimeGenerator P.val})) (-1) =
      canonicalQuadraticRow I (-1) := by
    change (∏ P : quadraticIdealSupport I,
      complexQuadraticChar (Ideal.span {quadraticPrimeGenerator P.val})
        (Ideal.Quotient.mk _ (-1))) = _
    exact Finset.prod_coe_sort (s := quadraticIdealSupport I)
      (f := fun P => complexQuadraticChar (Ideal.span {quadraticPrimeGenerator P}) (Ideal.Quotient.mk _ (-1)))
  rw [hrow] at h
  simpa only [Finset.prod_coe_sort, quadraticIdealSupport_product] using h

/-- The conductor class modulo four is the finite ray parameter for quadratic pairs. -/
def quadraticColumnRay (I : QuadraticIdeal) : QuadraticRayRing :=
  Ideal.Quotient.mk (Ideal.span {(4 : O)}) (primaryIdealGenerator I.val)

lemma canonicalQuadraticRow_neg_one_eq_of_same_ray (I J : QuadraticIdeal)
    (h : quadraticColumnRay I = quadraticColumnRay J) :
    canonicalQuadraticRow I (-1) = canonicalQuadraticRow J (-1) := by
  have he := fixedDualAverage_eq_of_mod_four (primaryIdealGenerator I.val) (primaryIdealGenerator J.val) h
  have hI := canonicalQuadraticRow_neg_one_phase I
  rw [he] at hI
  have hn : fixedDualAverage (primaryIdealGenerator J.val) ≠ 0 := by
    intro hz
    have hh := canonicalQuadraticRow_phase_norm J
    rw [hz, norm_zero] at hh
    exact zero_ne_one hh
  exact mul_right_cancel₀ hn (hI.trans (canonicalQuadraticRow_neg_one_phase J).symm)

lemma canonicalQuadraticRow_unit_sq (I : QuadraticIdeal) (u : Oˣ) :
    canonicalQuadraticRow I (u : O) ^ 2 = 1 := by
  apply quadraticSubsetRow_sq
  exact ⟨0, ((u⁻¹ : Oˣ) : O), by simp⟩

@[simp] lemma canonicalQuadraticRow_one (I : QuadraticIdeal) : canonicalQuadraticRow I 1 = 1 := by
  simp only [canonicalQuadraticRow, primeSubsetRow, map_one, Finset.prod_const_one]

lemma canonicalQuadraticRow_unit_cube (I : QuadraticIdeal) (u : Oˣ) :
    canonicalQuadraticRow I ((u : O) ^ 3) = canonicalQuadraticRow I (u : O) := by
  have hs := canonicalQuadraticRow_unit_sq I u
  rw [pow_succ, pow_two,
    canonicalQuadraticRow_mul, canonicalQuadraticRow_mul, ← pow_two, hs, one_mul]

/-- Equal conductor rays have equal values on every Eisenstein unit. -/
lemma canonicalQuadraticRow_unit_eq_of_same_ray (I J : QuadraticIdeal)
    (h : quadraticColumnRay I = quadraticColumnRay J) (u : Oˣ) :
    canonicalQuadraticRow I (u : O) = canonicalQuadraticRow J (u : O) := by
  rw [← canonicalQuadraticRow_unit_cube I u, ← canonicalQuadraticRow_unit_cube J u]
  rcases unit_cube_eq_sign u with hu | hu
  · rw [hu, canonicalQuadraticRow_one, canonicalQuadraticRow_one]
  · rw [hu]
    exact canonicalQuadraticRow_neg_one_eq_of_same_ray I J h

lemma canonicalQuadraticPair_unit_invariant (I J : QuadraticIdeal)
    (h : quadraticColumnRay I = quadraticColumnRay J) (u : Oˣ) (z : O) :
    canonicalQuadraticRow I ((u : O) * z) * canonicalQuadraticRow J ((u : O) * z) =
      canonicalQuadraticRow I z * canonicalQuadraticRow J z := by
  rw [canonicalQuadraticRow_mul, canonicalQuadraticRow_mul,
    canonicalQuadraticRow_unit_eq_of_same_ray I J h]
  calc
    _ = canonicalQuadraticRow J (u : O) ^ 2 * (canonicalQuadraticRow I z * canonicalQuadraticRow J z) := by ring
    _ = _ := by rw [canonicalQuadraticRow_unit_sq, one_mul]

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein Eisenstein.Coordinates QuadraticPhase.Eisenstein

/-- Equal odd rays multiply to a ray with trivial quadratic Gauss phase. -/
lemma fixedDualAverage_product_of_same_ray (c d : O)
    (h : Ideal.Quotient.mk (Ideal.span {(4 : O)}) c =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) d)
    (hc : ‖fixedDualAverage c‖ = 1) : fixedDualAverage (c * d) = 1 := by
  obtain ⟨⟨a, b⟩, hab⟩ := (rationalCoordEquiv 4 (by decide)).surjective
    (Ideal.Quotient.mk (Ideal.span {(4 : O)}) c)
  change Ideal.Quotient.mk (Ideal.span {(4 : O)})
    (eval (ZMod.cast a) (ZMod.cast b)) = Ideal.Quotient.mk (Ideal.span {(4 : O)}) c at hab
  have hp : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (c * d) =
      Ideal.Quotient.mk (Ideal.span {(4 : O)})
        (eval (ZMod.cast a) (ZMod.cast b) * eval (ZMod.cast a) (ZMod.cast b)) := by
    rw [map_mul, map_mul, ← h, hab]
  rw [fixedDualAverage_eq_of_mod_four c _ hab.symm, fixedDualAverage_formula] at hc
  rw [fixedDualAverage_eq_of_mod_four (c * d) _ hp, eval_mul, fixedDualAverage_formula]
  fin_cases a <;> fin_cases b <;>
    norm_num [ZMod.cast, ZMod.val, zpow_neg, zpow_ofNat, Complex.I_sq, Complex.I_pow_three, Complex.inv_I] at * <;>
    ring_nf at * <;> norm_num [zpow_ofNat, neg_pow, Complex.I_pow_eq_pow_mod,
      Complex.I_sq, Complex.I_pow_three, Complex.inv_I] at * <;> ring

lemma quadraticIdealSupport_disjoint_of_coprime (I J : QuadraticIdeal)
    (h : IsCoprime I.val J.val) : Disjoint (quadraticIdealSupport I) (quadraticIdealSupport J) := by
  apply Finset.disjoint_left.mpr
  intro P hP hQ
  have hpI := Multiset.mem_toFinset.mp ((mem_quadraticIdealSupport I P).mp hP)
  have hpJ := Multiset.mem_toFinset.mp ((mem_quadraticIdealSupport J P).mp hQ)
  exact (UniqueFactorizationMonoid.prime_of_normalized_factor P.val hpI).2.1
    (h.isUnit_of_dvd' (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hpI)
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hpJ))

open MeasureTheory
open scoped SchwartzMap

/-- On a fixed conductor ray, Poisson reflection of a coprime pair has phase one. -/
theorem canonical_same_ray_pair_poisson {κ : Type*}
    (I J : QuadraticIdeal) (hcop : IsCoprime I.val J.val)
    (hray : quadraticColumnRay I = quadraticColumnRay J)
    (q : κ → O) (hq : ∀ i, q i ≠ 0)
    (hqc : Pairwise (Function.onFun IsCoprime q)) (S : Finset κ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, primeCoprimeMask q S z *
      (canonicalQuadraticRow I z * canonicalQuadraticRow J z) * W (‖ringComplex z‖ ^ 2 / Y)) =
      ((Y : ℂ) / (‖ringComplex (primaryIdealGenerator I.val * primaryIdealGenerator J.val)‖ : ℂ)) *
        ∑ E ∈ S.powerset,
          ((-1 : ℂ) ^ E.card *
            (canonicalQuadraticRow I (∏ i ∈ E, q i) * canonicalQuadraticRow J (∏ i ∈ E, q i)) /
              (‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 : ℝ)) *
            ∑' z : O, (canonicalQuadraticRow I z * canonicalQuadraticRow J z) *
              paperRadialFourier W (Y * ‖ringComplex z‖ ^ 2 /
                (‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 *
                  ‖ringComplex (primaryIdealGenerator I.val * primaryIdealGenerator J.val)‖ ^ 2)) := by
  classical
  let U := quadraticIdealSupport I ∪ quadraticIdealSupport J
  have hd := quadraticIdealSupport_disjoint_of_coprime I J hcop
  have hp : (∏ P : U, quadraticPrimeGenerator P.val) =
      primaryIdealGenerator I.val * primaryIdealGenerator J.val := by
    rw [Finset.prod_coe_sort, Finset.prod_union hd,
      quadraticIdealSupport_product, quadraticIdealSupport_product]
  have hphase : fixedDualAverage (primaryIdealGenerator I.val * primaryIdealGenerator J.val) = 1 := by
    exact fixedDualAverage_product_of_same_ray _ _ hray (canonicalQuadraticRow_phase_norm I)
  have hrow (z : O) :
      primeCuspRowCharacter (fun P : U => quadraticPrimeGenerator P.val)
        (fun P => complexQuadraticChar (Ideal.span {quadraticPrimeGenerator P.val})) z =
      canonicalQuadraticRow I z * canonicalQuadraticRow J z := by
    change (∏ P : U, complexQuadraticChar (Ideal.span {quadraticPrimeGenerator P.val})
      (Ideal.Quotient.mk _ z)) = _
    rw [Finset.prod_coe_sort (s := U) (f := fun P : QuadraticPrime =>
      complexQuadraticChar (Ideal.span {quadraticPrimeGenerator P}) (Ideal.Quotient.mk _ z))]
    exact Finset.prod_union hd
  have ht := quadratic_row_masked_radial_poisson
    (fun P : U => quadraticPrimeGenerator P.val) (fun P => quadraticPrimeGenerator_ne_zero P.val)
    (quadraticPrimeGenerator_span_injective.comp Subtype.val_injective)
    (fun P => quadraticPrimeGenerator_odd P.val) q hq hqc S W Y hY
  simpa only [hphase, hp, hrow, mul_one] using ht

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein

/-- Every nonzero Eisenstein integer is a unique unit multiple of the chosen ideal generator. -/
def unitIdealElement (p : NonzeroIdeal × Oˣ) : {z : O // z ≠ 0} :=
  ⟨(p.2 : O) * cubicIdealGenerator p.1.val, mul_ne_zero p.2.ne_zero (cubicIdealGenerator_ne_zero _ p.1.property)⟩

lemma unitIdealElement_bijective : Function.Bijective unitIdealElement := by
  constructor
  · rintro ⟨I, u⟩ ⟨J, v⟩ he
    have hv := congrArg (fun z : {z : O // z ≠ 0} => z.val) he
    change (u : O) * cubicIdealGenerator I.val = (v : O) * cubicIdealGenerator J.val at hv
    have hi := congrArg (fun z : O => Ideal.span {z}) hv
    rw [Ideal.span_singleton_mul_left_unit u.isUnit, Ideal.span_singleton_mul_left_unit v.isUnit,
      span_cubicIdealGenerator, span_cubicIdealGenerator] at hi
    have hIJ : I = J := Subtype.ext hi
    subst J
    have huv : u = v := Units.ext (mul_right_cancel₀ (cubicIdealGenerator_ne_zero _ I.property) hv)
    subst v
    rfl
  · intro z
    let I : NonzeroIdeal := ⟨Ideal.span {z.val}, by
      exact Ideal.span_singleton_eq_bot.not.mpr z.property⟩
    have ha : Associated (cubicIdealGenerator I.val) z.val :=
      Ideal.span_singleton_eq_span_singleton.mp (span_cubicIdealGenerator I.val)
    obtain ⟨u, hu⟩ := ha
    refine ⟨(I, u), Subtype.ext ?_⟩
    simpa only [unitIdealElement, mul_comm] using hu

def unitIdealElementEquiv : NonzeroIdeal × Oˣ ≃ {z : O // z ≠ 0} :=
  Equiv.ofBijective unitIdealElement unitIdealElement_bijective

/-- Unit-invariant lattice sums are ideal sums with the exact unit multiplicity. -/
theorem tsum_unit_invariant_ideals (f : O → ℂ) (hf : Summable f) (h0 : f 0 = 0)
    (hu : ∀ (u : Oˣ) (z : O), f ((u : O) * z) = f z) :
    (∑' z : O, f z) = (Nat.card Oˣ : ℂ) * ∑' I : NonzeroIdeal, f (cubicIdealGenerator I.val) := by
  letI : Finite Oˣ := cubic_units_finite
  letI : Fintype Oˣ := Fintype.ofFinite _
  have hs := (hf.subtype (fun z => z ≠ 0)).comp_injective unitIdealElementEquiv.injective
  change Summable (fun p : NonzeroIdeal × Oˣ => f ((p.2 : O) * cubicIdealGenerator p.1.val)) at hs
  calc
    _ = ∑' z : {z : O // z ≠ 0}, f z.val := by
      symm
      apply tsum_subtype_eq_of_support_subset
      intro z hz he
      subst z
      exact hz h0
    _ = ∑' p : NonzeroIdeal × Oˣ, f ((p.2 : O) * cubicIdealGenerator p.1.val) :=
      (unitIdealElementEquiv.tsum_eq (fun z => f z.val)).symm
    _ = ∑' I : NonzeroIdeal, ∑' u : Oˣ, f ((u : O) * cubicIdealGenerator I.val) := hs.tsum_prod
    _ = ∑' I : NonzeroIdeal, (Nat.card Oˣ : ℂ) * f (cubicIdealGenerator I.val) := by
      apply tsum_congr
      intro I
      simp only [hu, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card]
    _ = _ := tsum_mul_left

/-- A same-ray quadratic pair descends to all ideals, independently of generator choice. -/
def canonicalQuadraticPairIdeal (I J : QuadraticIdeal) (D : Ideal O) : ℂ :=
  canonicalQuadraticRow I (cubicIdealGenerator D) * canonicalQuadraticRow J (cubicIdealGenerator D)

lemma canonicalQuadraticPairIdeal_span (I J : QuadraticIdeal)
    (hray : quadraticColumnRay I = quadraticColumnRay J) (z : O) :
    canonicalQuadraticPairIdeal I J (Ideal.span {z}) = canonicalQuadraticRow I z * canonicalQuadraticRow J z := by
  have ha : Associated (cubicIdealGenerator (Ideal.span {z})) z :=
    Ideal.span_singleton_eq_span_singleton.mp (span_cubicIdealGenerator _)
  obtain ⟨u, hu⟩ := ha
  have hv := canonicalQuadraticPair_unit_invariant I J hray u (cubicIdealGenerator (Ideal.span {z}))
  have he : (u : O) * cubicIdealGenerator (Ideal.span {z}) = z := by simpa only [mul_comm] using hu
  rw [he] at hv
  exact hv.symm

lemma canonicalQuadraticPairIdeal_mul (I J : QuadraticIdeal)
    (hray : quadraticColumnRay I = quadraticColumnRay J) (A B : Ideal O) :
    canonicalQuadraticPairIdeal I J (A * B) =
      canonicalQuadraticPairIdeal I J A * canonicalQuadraticPairIdeal I J B := by
  have hs : Ideal.span {cubicIdealGenerator A * cubicIdealGenerator B} = A * B := by
    rw [← Ideal.span_singleton_mul_span_singleton, span_cubicIdealGenerator, span_cubicIdealGenerator]
  rw [← hs, canonicalQuadraticPairIdeal_span I J hray, canonicalQuadraticRow_mul, canonicalQuadraticRow_mul]
  unfold canonicalQuadraticPairIdeal
  ring

lemma canonicalQuadraticPairIdeal_primary (I J : QuadraticIdeal)
    (hray : quadraticColumnRay I = quadraticColumnRay J) (D : Ideal O) (hD : primaryIdealGenerator D ≠ 0) :
    canonicalQuadraticPairIdeal I J D =
      canonicalQuadraticRow I (primaryIdealGenerator D) * canonicalQuadraticRow J (primaryIdealGenerator D) := by
  have h := canonicalQuadraticPairIdeal_span I J hray (primaryIdealGenerator D)
  rw [(primaryIdealGenerator_spec D hD).1] at h
  exact h

lemma canonicalQuadraticPairIdeal_norm_le_one (I J : QuadraticIdeal) (D : Ideal O) :
    ‖canonicalQuadraticPairIdeal I J D‖ ≤ 1 := by
  rw [canonicalQuadraticPairIdeal, norm_mul]
  exact (mul_le_mul (canonicalQuadraticRow_norm_le_one I _)
    (canonicalQuadraticRow_norm_le_one J _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped SchwartzMap

lemma canonicalQuadraticRow_zero_of_ne_one (I : QuadraticIdeal) (hI : I.val ≠ 1) :
    canonicalQuadraticRow I 0 = 0 := by
  classical
  have hs : (quadraticIdealSupport I).Nonempty := by
    by_contra h
    have he := quadraticIdealSupport_product I
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.prod_empty] at he
    have hi := (primaryIdealGenerator_spec I.val I.property.1).1
    rw [← he, Ideal.span_singleton_one] at hi
    exact hI (by simpa only [Ideal.one_eq_top] using hi.symm)
  unfold canonicalQuadraticRow primeSubsetRow
  apply Finset.prod_eq_zero hs.choose_spec
  simp only [map_zero, MulChar.map_zero]

lemma canonicalQuadraticPair_zero (I J : QuadraticIdeal) (h : I.val ≠ 1 ∨ J.val ≠ 1) :
    canonicalQuadraticRow I 0 * canonicalQuadraticRow J 0 = 0 := by
  rcases h with h | h
  · rw [canonicalQuadraticRow_zero_of_ne_one I h, zero_mul]
  · rw [canonicalQuadraticRow_zero_of_ne_one J h, mul_zero]

lemma canonicalQuadraticPair_fourier_summable (I J : QuadraticIdeal)
    (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    Summable (fun z : O => (canonicalQuadraticRow I z * canonicalQuadraticRow J z) *
      paperRadialFourier W (t * ‖ringComplex z‖ ^ 2)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun z => ?_) (paperRadialFourier_lattice_summable_norm W t ht)
  rw [norm_mul, norm_mul]
  have hrow : ‖canonicalQuadraticRow I z‖ * ‖canonicalQuadraticRow J z‖ ≤ 1 :=
    (mul_le_mul (canonicalQuadraticRow_norm_le_one I z)
      (canonicalQuadraticRow_norm_le_one J z) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  exact mul_le_of_le_one_left (norm_nonneg _) hrow

/-- Removing the zero frequency and unit orbit gives the exact unrestricted dual ideal sum. -/
theorem canonicalQuadraticPair_fourier_ideal_reindex (I J : QuadraticIdeal)
    (hray : quadraticColumnRay I = quadraticColumnRay J) (hnt : I.val ≠ 1 ∨ J.val ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    (∑' z : O, (canonicalQuadraticRow I z * canonicalQuadraticRow J z) *
      paperRadialFourier W (t * ‖ringComplex z‖ ^ 2)) =
      (Nat.card Oˣ : ℂ) * ∑' D : NonzeroIdeal, canonicalQuadraticPairIdeal I J D.val *
        paperRadialFourier W (t * (Ideal.absNorm D.val : ℝ)) := by
  let f : O → ℂ := fun z => (canonicalQuadraticRow I z * canonicalQuadraticRow J z) *
    paperRadialFourier W (t * ‖ringComplex z‖ ^ 2)
  have h0 : f 0 = 0 := by
    dsimp only [f]
    rw [canonicalQuadraticPair_zero I J hnt, zero_mul]
  have hu (u : Oˣ) (z : O) : f ((u : O) * z) = f z := by
    dsimp only [f]
    rw [canonicalQuadraticPair_unit_invariant I J hray, map_mul, norm_mul,
      norm_ringComplex_unit, one_mul]
  have he := tsum_unit_invariant_ideals f (canonicalQuadraticPair_fourier_summable I J W t ht) h0 hu
  simpa only [f, ringComplex_norm_sq_eq_absNorm_span, span_cubicIdealGenerator,
    canonicalQuadraticPairIdeal] using he

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein UniqueFactorizationMonoid

lemma canonicalQuadraticPairIdeal_one (I J : QuadraticIdeal)
    (hray : quadraticColumnRay I = quadraticColumnRay J) :
    canonicalQuadraticPairIdeal I J 1 = 1 := by
  have h := canonicalQuadraticPairIdeal_span I J hray 1
  simpa only [Ideal.span_singleton_one, canonicalQuadraticRow_one, one_mul,
    Ideal.one_eq_top] using h

/-- Normalizing by the square root of the ideal norm preserves multiplicativity. -/
def normalizedQuadraticPair (I J : QuadraticIdeal) (D : Ideal O) : ℂ :=
  canonicalQuadraticPairIdeal I J D / (Real.sqrt (Ideal.absNorm D : ℝ) : ℂ)

lemma normalizedQuadraticPair_mul (I J : QuadraticIdeal)
    (hray : quadraticColumnRay I = quadraticColumnRay J) (A B : Ideal O) :
    normalizedQuadraticPair I J (A * B) =
      normalizedQuadraticPair I J A * normalizedQuadraticPair I J B := by
  simp only [normalizedQuadraticPair, canonicalQuadraticPairIdeal_mul I J hray,
    map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul,
    div_mul_div_comm]

def normalizedQuadraticPairHom (I J : QuadraticIdeal)
    (hray : quadraticColumnRay I = quadraticColumnRay J) : Ideal O →* ℂ where
  toFun := normalizedQuadraticPair I J
  map_one' := by
    rw [normalizedQuadraticPair, canonicalQuadraticPairIdeal_one I J hray, map_one]
    norm_num
  map_mul' := normalizedQuadraticPair_mul I J hray

lemma normalizedQuadraticPair_square (I J : QuadraticIdeal) (D : Ideal O) :
    normalizedQuadraticPair I J D ^ 2 =
      (quadraticIdealMask I (cubicIdealGenerator D) * quadraticIdealMask J (cubicIdealGenerator D)) /
        (Ideal.absNorm D : ℂ) := by
  have hr (L : QuadraticIdeal) : canonicalQuadraticRow L (cubicIdealGenerator D) ^ 2 =
      quadraticIdealMask L (cubicIdealGenerator D) := by
    simpa only [pow_two, canonicalQuadraticRow_mul] using
      canonicalQuadraticRow_square L (cubicIdealGenerator D)
  have hn : (Real.sqrt (Ideal.absNorm D : ℝ) : ℂ) ^ 2 = (Ideal.absNorm D : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Ideal.absNorm D) : (0 : ℝ) ≤ _)
  rw [normalizedQuadraticPair, div_pow, canonicalQuadraticPairIdeal, mul_pow, hr, hr, hn]

/-- Divisors of a squarefree ideal are precisely products of subsets of its prime support. -/
lemma squarefree_ideal_divisor_sum (G : Ideal O) (hG : Squarefree G) (f : Ideal O → ℂ) :
    (∑ D ∈ idealDivisors G, f D) =
      ∑ S ∈ (primeSupport G).powerset, f (∏ P ∈ S, P) := by
  have hf : (idealDivisors G).filter Squarefree = idealDivisors G :=
    Finset.filter_eq_self.mpr (fun D hD => hG.squarefree_of_dvd ((mem_idealDivisors hG.ne_zero).mp hD))
  rw [← hf, squarefree_divisors_eq_image G hG.ne_zero, Finset.sum_image]
  intro S hS T hT he
  exact support_product_injective (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) he

lemma squarefree_ideal_signed_divisor_product (G : Ideal O) (hG : Squarefree G)
    (f : Ideal O →* ℂ) :
    (∑ D ∈ idealDivisors G, (moebius D : ℂ) * f D) = ∏ P ∈ primeSupport G, (1 - f P) := by
  rw [squarefree_ideal_divisor_sum G hG, Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro S hS
  rw [moebius_support_product (Finset.mem_powerset.mp hS), map_prod]
  simp only [Finset.prod_const_one, mul_one]

lemma squarefree_ideal_divisor_product (G : Ideal O) (hG : Squarefree G)
    (f : Ideal O →* ℂ) :
    (∑ D ∈ idealDivisors G, f D) = ∏ P ∈ primeSupport G, (f P + 1) := by
  rw [squarefree_ideal_divisor_sum G hG, Finset.prod_add]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [map_prod, Finset.prod_const_one, mul_one]

/-- Source and dual divisor densities agree exactly before imposing the norm cutoff. -/
theorem normalizedQuadraticPair_density (I J : QuadraticIdeal)
    (hray : quadraticColumnRay I = quadraticColumnRay J) (G : Ideal O) (hG : Squarefree G) :
    (∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
      (moebius E : ℂ) * normalizedQuadraticPair I J (D * E)) =
      ∏ P ∈ primeSupport G,
        (1 - (quadraticIdealMask I (cubicIdealGenerator P) * quadraticIdealMask J (cubicIdealGenerator P)) /
          (Ideal.absNorm P : ℂ)) := by
  let f := normalizedQuadraticPairHom I J hray
  have he : (∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
      (moebius E : ℂ) * normalizedQuadraticPair I J (D * E)) =
      (∑ D ∈ idealDivisors G, f D) * (∑ E ∈ idealDivisors G, (moebius E : ℂ) * f E) := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, f, normalizedQuadraticPairHom,
      MonoidHom.coe_mk, OneHom.coe_mk, normalizedQuadraticPair_mul I J hray]
    apply Finset.sum_congr rfl
    intro D hD
    apply Finset.sum_congr rfl
    intro E hE
    ring
  rw [he, squarefree_ideal_divisor_product G hG, squarefree_ideal_signed_divisor_product G hG,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  change (normalizedQuadraticPair I J P + 1) * (1 - normalizedQuadraticPair I J P) = _
  rw [show (normalizedQuadraticPair I J P + 1) * (1 - normalizedQuadraticPair I J P) =
    1 - normalizedQuadraticPair I J P ^ 2 by ring, normalizedQuadraticPair_square]

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein UniqueFactorizationMonoid

lemma ideal_coprime_of_isRelPrime (A B : Ideal O) (h : IsRelPrime A B) : IsCoprime A B := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  exact Ideal.isUnit_iff.mp (h (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))

/-- Removing the common prime divisors of a squarefree ideal leaves a coprime quotient. -/
lemma squarefree_sup_quotient_coprime (B G : Ideal O) (hB : Squarefree B) :
    IsCoprime (quadraticIdealQuotient (B ⊔ G) B) G := by
  let D := B ⊔ G
  have hDB : D ∣ B := Ideal.dvd_iff_le.mpr le_sup_left
  have hDG : D ∣ G := Ideal.dvd_iff_le.mpr le_sup_right
  have hD : D ≠ 0 := ne_zero_of_dvd_ne_zero hB.ne_zero hDB
  have hc : IsCoprime (quadraticIdealQuotient D B) (quadraticIdealQuotient D G) :=
    Ideal.isCoprime_iff_sup_eq.mpr ((quadraticIdealQuotient_coprime_iff D B G hD hDB hDG).mpr rfl)
  have hs : Squarefree (D * quadraticIdealQuotient D B) := by
    rw [quadraticIdeal_mul_quotient hDB]
    exact hB
  have hq := ideal_coprime_of_isRelPrime D (quadraticIdealQuotient D B) (squarefree_mul_iff.mp hs).1
  have ht := hq.symm.mul_right hc
  rw [quadraticIdeal_mul_quotient hDG] at ht
  exact ht

lemma ideal_sup_mul_of_coprime_divisor (D H G : Ideal O)
    (hDG : D ∣ G) (hHG : IsCoprime H G) : (D * H) ⊔ G = D := by
  have hleft : D ∣ (D * H) ⊔ G :=
    Ideal.dvd_iff_le.mpr (sup_le (Ideal.dvd_iff_le.mp (dvd_mul_right D H)) (Ideal.dvd_iff_le.mp hDG))
  have hcop : IsCoprime ((D * H) ⊔ G) H :=
    (hHG.mono (dvd_refl H) (Ideal.dvd_iff_le.mpr le_sup_right)).symm
  have hright : (D * H) ⊔ G ∣ D := hcop.dvd_of_dvd_mul_right (Ideal.dvd_iff_le.mpr le_sup_left)
  exact associated_iff_eq.mp (associated_of_dvd_dvd hright hleft)

/-- Splitting a squarefree ideal at a fixed squarefree support is unique. -/
def squarefreeIdealSplit (G : Ideal O) (hG : Squarefree G) :
    {B : Ideal O // Squarefree B} ≃
      (idealDivisors G) × {H : Ideal O // Squarefree H ∧ IsCoprime H G} where
  toFun B := (⟨B.val ⊔ G, (mem_idealDivisors hG.ne_zero).mpr (Ideal.dvd_iff_le.mpr le_sup_right)⟩,
    ⟨quadraticIdealQuotient (B.val ⊔ G) B.val,
      B.property.squarefree_of_dvd (quadraticIdealQuotient_dvd (Ideal.dvd_iff_le.mpr le_sup_left)),
      squarefree_sup_quotient_coprime B.val G B.property⟩)
  invFun p := ⟨p.1.val * p.2.val, squarefree_mul_iff.mpr
    ⟨(p.2.property.2.mono (dvd_refl _) ((mem_idealDivisors hG.ne_zero).mp p.1.property)).symm.isRelPrime,
      hG.squarefree_of_dvd ((mem_idealDivisors hG.ne_zero).mp p.1.property), p.2.property.1⟩⟩
  left_inv B := Subtype.ext (quadraticIdeal_mul_quotient (Ideal.dvd_iff_le.mpr le_sup_left))
  right_inv p := by
    have hDG := (mem_idealDivisors hG.ne_zero).mp p.1.property
    have hs := ideal_sup_mul_of_coprime_divisor p.1.val p.2.val G hDG p.2.property.2
    apply Prod.ext (Subtype.ext hs)
    apply Subtype.ext
    change quadraticIdealQuotient ((p.1.val * p.2.val) ⊔ G) (p.1.val * p.2.val) = p.2.val
    rw [hs]
    exact mul_left_cancel₀ (ne_zero_of_dvd_ne_zero hG.ne_zero hDG)
      (quadraticIdeal_mul_quotient (dvd_mul_right p.1.val p.2.val))

def squarefreeIdealBall (K : ℝ) : Finset (Ideal O) :=
  (Ideal.finite_setOf_absNorm_le (S := O) ⌈K⌉₊).toFinset.filter
    (fun I => Squarefree I ∧ (Ideal.absNorm I : ℝ) ≤ K)

lemma mem_squarefreeIdealBall {K : ℝ} {I : Ideal O} :
    I ∈ squarefreeIdealBall K ↔ Squarefree I ∧ (Ideal.absNorm I : ℝ) ≤ K := by
  simp only [squarefreeIdealBall, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  constructor
  · exact And.right
  · intro h
    exact ⟨by exact_mod_cast h.2.trans (Nat.le_ceil K), h⟩

def coprimeSquarefreeIdealBall (G : Ideal O) (K : ℝ) : Finset (Ideal O) :=
  (squarefreeIdealBall K).filter (fun H => IsCoprime H G)

lemma squarefreeIdeal_cutoff_summable (K : ℝ) (f : Ideal O → ℂ) :
    Summable (fun B : {B : Ideal O // Squarefree B} =>
      if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0) := by
  let e : squarefreeIdealBall K → {B : Ideal O // Squarefree B} :=
    fun B => ⟨B.val, (mem_squarefreeIdealBall.mp B.property).1⟩
  apply summable_of_hasFiniteSupport
  apply (Set.finite_range e).subset
  intro B hB
  have hN : (Ideal.absNorm B.val : ℝ) ≤ K := by
    by_contra hn
    exact hB (if_neg hn)
  exact ⟨⟨B.val, mem_squarefreeIdealBall.mpr ⟨B.property, hN⟩⟩, Subtype.ext rfl⟩

lemma tsum_squarefreeIdeal_cutoff (K : ℝ) (f : Ideal O → ℂ) :
    (∑' B : {B : Ideal O // Squarefree B}, if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0) =
      ∑ B : squarefreeIdealBall K, f B.val := by
  let e : squarefreeIdealBall K → {B : Ideal O // Squarefree B} :=
    fun B => ⟨B.val, (mem_squarefreeIdealBall.mp B.property).1⟩
  have he : Function.Injective e := fun B C h => Subtype.ext (congrArg (fun I : {B : Ideal O // Squarefree B} => I.val) h)
  let F : {B : Ideal O // Squarefree B} → ℂ := fun B =>
    if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0
  have hs : Function.support F ⊆ Set.range e := by
    intro B hB
    have hN : (Ideal.absNorm B.val : ℝ) ≤ K := by
      by_contra hn
      exact hB (if_neg hn)
    exact ⟨⟨B.val, mem_squarefreeIdealBall.mpr ⟨B.property, hN⟩⟩, Subtype.ext rfl⟩
  change (∑' B, F B) = _
  rw [← he.tsum_eq hs, tsum_fintype]
  apply Finset.sum_congr rfl
  intro B _
  exact if_pos (mem_squarefreeIdealBall.mp B.property).2

lemma tsum_coprimeSquarefreeIdeal_cutoff (G D : Ideal O) (hD : D ≠ 0) (K : ℝ) (f : Ideal O → ℂ) :
    (∑' H : {H : Ideal O // Squarefree H ∧ IsCoprime H G},
      if (Ideal.absNorm (D * H.val) : ℝ) ≤ K then f (D * H.val) else 0) =
      ∑ H : coprimeSquarefreeIdealBall G K,
        if (Ideal.absNorm (D * H.val) : ℝ) ≤ K then f (D * H.val) else 0 := by
  let e : coprimeSquarefreeIdealBall G K → {H : Ideal O // Squarefree H ∧ IsCoprime H G} :=
    fun H => ⟨H.val, (mem_squarefreeIdealBall.mp (Finset.mem_filter.mp H.property).1).1,
      (Finset.mem_filter.mp H.property).2⟩
  have he : Function.Injective e := fun H J h => Subtype.ext (congrArg (fun I : {H : Ideal O // Squarefree H ∧ IsCoprime H G} => I.val) h)
  let F : {H : Ideal O // Squarefree H ∧ IsCoprime H G} → ℂ := fun H =>
    if (Ideal.absNorm (D * H.val) : ℝ) ≤ K then f (D * H.val) else 0
  have hs : Function.support F ⊆ Set.range e := by
    intro H hH
    have hN : (Ideal.absNorm (D * H.val) : ℝ) ≤ K := by
      by_contra hn
      exact hH (if_neg hn)
    have hD1 : 1 ≤ Ideal.absNorm D := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD)
    have hHN : (Ideal.absNorm H.val : ℝ) ≤ K := by
      have hn : Ideal.absNorm H.val ≤ Ideal.absNorm (D * H.val) := by
        simpa only [one_mul, map_mul] using Nat.mul_le_mul_right (Ideal.absNorm H.val) hD1
      exact (Nat.cast_le.mpr hn).trans hN
    exact ⟨⟨H.val, Finset.mem_filter.mpr
      ⟨mem_squarefreeIdealBall.mpr ⟨H.property.1, hHN⟩, H.property.2⟩⟩, Subtype.ext rfl⟩
  simpa only [tsum_fintype, F, e] using (he.tsum_eq hs).symm

/-- A sharp norm cutoff differs from the coprime decomposition only at its boundary. -/
theorem squarefreeIdeal_split_sum (G : Ideal O) (hG : Squarefree G) (K : ℝ) (f : Ideal O → ℂ) :
    (∑ B : squarefreeIdealBall K, f B.val) =
      ∑ D : idealDivisors G, ∑ H : coprimeSquarefreeIdealBall G K,
        if (Ideal.absNorm (D.val * H.val) : ℝ) ≤ K then f (D.val * H.val) else 0 := by
  let F : {B : Ideal O // Squarefree B} → ℂ := fun B =>
    if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0
  have hs := (squarefreeIdealSplit G hG).symm.summable_iff.mpr (squarefreeIdeal_cutoff_summable K f)
  have he := ((squarefreeIdealSplit G hG).symm.tsum_eq F).symm
  calc
    _ = ∑' B : {B : Ideal O // Squarefree B}, F B := (tsum_squarefreeIdeal_cutoff K f).symm
    _ = ∑' p : (idealDivisors G) × {H : Ideal O // Squarefree H ∧ IsCoprime H G},
        if (Ideal.absNorm (p.1.val * p.2.val) : ℝ) ≤ K then f (p.1.val * p.2.val) else 0 := he
    _ = ∑' D : idealDivisors G, ∑' H : {H : Ideal O // Squarefree H ∧ IsCoprime H G},
        if (Ideal.absNorm (D.val * H.val) : ℝ) ≤ K then f (D.val * H.val) else 0 := hs.tsum_prod
    _ = _ := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro D _
      exact tsum_coprimeSquarefreeIdeal_cutoff G D.val
        (ne_zero_of_dvd_ne_zero hG.ne_zero ((mem_idealDivisors hG.ne_zero).mp D.property)) K f

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein UniqueFactorizationMonoid

/-- The difference is supported where multiplication by a divisor crosses the norm cutoff. -/
def quadraticCutoffDifference (K : ℝ) (H D : Ideal O) : ℝ :=
  (if (Ideal.absNorm (H * D) : ℝ) ≤ K then 1 else 0) -
    (if (Ideal.absNorm H : ℝ) ≤ K then 1 else 0)

lemma quadraticCutoffDifference_nonzero (K : ℝ) (H D : Ideal O) (hD : D ≠ 0) :
    quadraticCutoffDifference K H D ≠ 0 ↔
      (Ideal.absNorm H : ℝ) ≤ K ∧ K < (Ideal.absNorm (H * D) : ℝ) := by
  have hd : 1 ≤ Ideal.absNorm D := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hm : (Ideal.absNorm H : ℝ) ≤ Ideal.absNorm (H * D) := by
    exact_mod_cast (show Ideal.absNorm H ≤ Ideal.absNorm (H * D) by
      simpa only [map_mul, mul_one] using Nat.mul_le_mul_left (Ideal.absNorm H) hd)
  unfold quadraticCutoffDifference
  split_ifs <;> simp_all <;> linarith

lemma quadraticCutoffDifference_eq_neg_one (K : ℝ) (H D : Ideal O) (hD : D ≠ 0)
    (h : quadraticCutoffDifference K H D ≠ 0) : quadraticCutoffDifference K H D = -1 := by
  obtain ⟨hH, hHD⟩ := (quadraticCutoffDifference_nonzero K H D hD).mp h
  simp only [quadraticCutoffDifference, if_neg (not_le.mpr hHD), if_pos hH]
  norm_num

def quadraticBoundaryWeight (K : ℝ) (H D E : Ideal O) : ℂ :=
  (quadraticCutoffDifference K H D : ℂ) / (Real.sqrt (Ideal.absNorm (H * D * E) : ℝ) : ℂ)

lemma quadraticBoundaryWeight_norm_le (K : ℝ) (hK : 0 < K) (H D E : Ideal O)
    (hD : D ≠ 0) (hE : E ≠ 0) : ‖quadraticBoundaryWeight K H D E‖ ≤ 1 / Real.sqrt K := by
  by_cases hc : quadraticCutoffDifference K H D = 0
  · simp only [quadraticBoundaryWeight, hc, Complex.ofReal_zero, zero_div, norm_zero]
    positivity
  have he : 1 ≤ Ideal.absNorm E := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hE)
  have hN : (Ideal.absNorm (H * D) : ℝ) ≤ Ideal.absNorm (H * D * E) := by
    exact_mod_cast (show Ideal.absNorm (H * D) ≤ Ideal.absNorm (H * D * E) by
      simpa only [map_mul, mul_one] using Nat.mul_le_mul_left (Ideal.absNorm (H * D)) he)
  have hlt := ((quadraticCutoffDifference_nonzero K H D hD).mp hc).2.trans_le hN
  rw [quadraticBoundaryWeight, quadraticCutoffDifference_eq_neg_one K H D hD hc]
  simp only [Complex.ofReal_neg, Complex.ofReal_one, norm_div, norm_neg, norm_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hK) (Real.sqrt_le_sqrt hlt.le)

def quadraticPairPartial (I J : QuadraticIdeal) (K : ℝ) : ℂ :=
  ∑ B : squarefreeIdealBall K, normalizedQuadraticPair I J B.val

def quadraticPairCoprimePartial (I J : QuadraticIdeal) (G : Ideal O) (K : ℝ) : ℂ :=
  ∑ H : coprimeSquarefreeIdealBall G K, normalizedQuadraticPair I J H.val

def quadraticPairDivisors (I J : QuadraticIdeal) (G : Ideal O) : ℂ :=
  ∑ E ∈ idealDivisors G, (moebius E : ℂ) * normalizedQuadraticPair I J E

def quadraticPairDensity (I J : QuadraticIdeal) (G : Ideal O) : ℂ :=
  ∏ P ∈ primeSupport G,
    (1 - (quadraticIdealMask I (cubicIdealGenerator P) * quadraticIdealMask J (cubicIdealGenerator P)) /
      (Ideal.absNorm P : ℂ))

def quadraticNormCutoff (K : ℝ) (H : Ideal O) : ℂ :=
  if (Ideal.absNorm H : ℝ) ≤ K then 1 else 0

lemma quadraticPairPartial_split (I J : QuadraticIdeal)
    (hray : quadraticColumnRay I = quadraticColumnRay J) (G : Ideal O) (hG : Squarefree G) (K : ℝ) :
    quadraticPairPartial I J K =
      ∑ H : coprimeSquarefreeIdealBall G K, ∑ D ∈ idealDivisors G,
        normalizedQuadraticPair I J H.val * normalizedQuadraticPair I J D * quadraticNormCutoff K (H.val * D) := by
  rw [quadraticPairPartial, squarefreeIdeal_split_sum G hG K, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro H _
  rw [Finset.sum_coe_sort (s := idealDivisors G)
    (f := fun D => if (Ideal.absNorm (D * H.val) : ℝ) ≤ K then normalizedQuadraticPair I J (D * H.val) else 0)]
  apply Finset.sum_congr rfl
  intro D hD
  rw [mul_comm D H.val, normalizedQuadraticPair_mul I J hray]
  unfold quadraticNormCutoff
  split_ifs <;> ring

/-- The uncancelled principal contribution is exactly the cutoff boundary term. -/
theorem quadraticPair_main_difference (I J : QuadraticIdeal)
    (hray : quadraticColumnRay I = quadraticColumnRay J) (G : Ideal O) (hG : Squarefree G) (K : ℝ) :
    quadraticPairPartial I J K * quadraticPairDivisors I J G -
      quadraticPairCoprimePartial I J G K * quadraticPairDensity I J G =
      ∑ H : coprimeSquarefreeIdealBall G K, ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
        (moebius E : ℂ) * normalizedQuadraticPair I J (H.val * D * E) *
          (quadraticCutoffDifference K H.val D : ℂ) := by
  have hd : quadraticPairDensity I J G =
      ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
        (moebius E : ℂ) * (normalizedQuadraticPair I J D * normalizedQuadraticPair I J E) := by
    rw [quadraticPairDensity, ← normalizedQuadraticPair_density I J hray G hG]
    simp only [normalizedQuadraticPair_mul I J hray]
  rw [quadraticPairPartial_split I J hray G hG K, hd]
  unfold quadraticPairDivisors quadraticPairCoprimePartial
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro H _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  have hHN := (mem_squarefreeIdealBall.mp (Finset.mem_filter.mp H.property).1).2
  have hc : (quadraticCutoffDifference K H.val D : ℂ) = quadraticNormCutoff K (H.val * D) - 1 := by
    unfold quadraticCutoffDifference quadraticNormCutoff
    rw [if_pos hHN]
    split_ifs <;> norm_num
  rw [hc, normalizedQuadraticPair_mul I J hray, normalizedQuadraticPair_mul I J hray]
  ring

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein UniqueFactorizationMonoid

lemma quadratic_twoIdeal_prime : Prime cubicTwoIdeal := by
  have hn : cubicTwoIdeal ≠ 0 := by
    intro h
    have he := cubicTwoIdeal_absNorm
    rw [h, map_zero] at he
    norm_num at he
  exact Ideal.prime_of_isPrime hn inferInstance

lemma prime_ideal_char_two_iff (P : Ideal O) (hP : Prime P) :
    ringChar (O ⧸ P) = 2 ↔ P = cubicTwoIdeal := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  constructor
  · intro h
    have hz : (2 : O ⧸ P) = 0 := (ringChar.spec (O ⧸ P) 2).mpr (by rw [h])
    have hm : (2 : O) ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_ofNat] using hz)
    have hle : cubicTwoIdeal ≤ P := by
      rw [cubicTwoIdeal, Ideal.span_singleton_neg]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    exact ((inferInstance : cubicTwoIdeal.IsMaximal).eq_of_le
      (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal)) hle).symm
  · rintro rfl
    exact cubicTwoIdeal_residue_char

lemma quadraticSupported_iff_bad_not_dvd (I : Ideal O) :
    quadraticSupported I ↔ ¬ ramifiedIdeal ∣ I ∧ ¬ cubicTwoIdeal ∣ I := by
  constructor
  · intro h
    refine ⟨(goodIdeal_iff_not_ramified I).mp h.1, ?_⟩
    intro hd
    have hI := primaryIdealGenerator_ne_zero_ideal I h.1
    have hm : cubicTwoIdeal ∈ primeSupport I := Multiset.mem_toFinset.mpr
      ((Ideal.mem_normalizedFactors_iff hI).mpr ⟨inferInstance, Ideal.dvd_iff_le.mp hd⟩)
    exact h.2 cubicTwoIdeal hm cubicTwoIdeal_residue_char
  · rintro ⟨hr, ht⟩
    refine ⟨(goodIdeal_iff_not_ramified I).mpr hr, ?_⟩
    intro P hP hchar
    have he := (prime_ideal_char_two_iff P (support_prime hP)).mp hchar
    apply ht
    rw [← he]
    exact dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)

/-- The finite mask contains both excluded primes and the conductor prime support. -/
def quadraticMaskPrimes (D : Ideal O) : Finset (Ideal O) :=
  {ramifiedIdeal, cubicTwoIdeal} ∪ primeSupport D

def quadraticMaskIdeal (D : Ideal O) : Ideal O := ∏ P ∈ quadraticMaskPrimes D, P

lemma quadraticMaskPrimes_prime (D P : Ideal O) (hP : P ∈ quadraticMaskPrimes D) : Prime P := by
  rcases Finset.mem_union.mp hP with h | h
  · rcases Finset.mem_insert.mp h with h | h
    · simpa only [h] using ramifiedIdeal_prime
    · simpa only [Finset.mem_singleton.mp h] using quadratic_twoIdeal_prime
  · exact support_prime h

lemma quadraticMaskIdeal_squarefree (D : Ideal O) : Squarefree (quadraticMaskIdeal D) := by
  have hn : quadraticMaskIdeal D ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun P hP => (quadraticMaskPrimes_prime D P hP).ne_zero)
  have hf : normalizedFactors (quadraticMaskIdeal D) = (quadraticMaskPrimes D).val := by
    have hp : ∀ P ∈ (quadraticMaskPrimes D).val, Prime P := fun P hP => quadraticMaskPrimes_prime D P hP
    simpa [quadraticMaskIdeal] using normalizedFactors_prod_of_prime hp
  apply (squarefree_iff_nodup_normalizedFactors hn).mpr
  rw [hf]
  exact (quadraticMaskPrimes D).nodup

lemma ramifiedIdeal_dvd_quadraticMaskIdeal (D : Ideal O) : ramifiedIdeal ∣ quadraticMaskIdeal D :=
  Finset.dvd_prod_of_mem (fun P => P) (Finset.mem_union_left _ (Finset.mem_insert_self _ _))

lemma twoIdeal_dvd_quadraticMaskIdeal (D : Ideal O) : cubicTwoIdeal ∣ quadraticMaskIdeal D :=
  Finset.dvd_prod_of_mem (fun P => P)
    (Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))

/-- Coprimality with the fixed mask gives the exact admissibility needed by the native sieve. -/
lemma quadraticIdealAdmissible_of_mask_coprime (D H : Ideal O)
    (hH : Squarefree H) (hc : IsCoprime H (quadraticMaskIdeal D)) : quadraticIdealAdmissible H := by
  have hs : quadraticSupported H := (quadraticSupported_iff_bad_not_dvd H).mpr ⟨
    fun h => ramifiedIdeal_prime.2.1 (hc.isUnit_of_dvd' h (ramifiedIdeal_dvd_quadraticMaskIdeal D)),
    fun h => quadratic_twoIdeal_prime.2.1 (hc.isUnit_of_dvd' h (twoIdeal_dvd_quadraticMaskIdeal D))⟩
  exact ⟨hs.1, hH, hs.2⟩

lemma coprimeSquarefreeIdealBall_admissible (D : Ideal O) (K : ℝ)
    (H : coprimeSquarefreeIdealBall (quadraticMaskIdeal D) K) : quadraticIdealAdmissible H.val :=
  quadraticIdealAdmissible_of_mask_coprime D H.val
    (mem_squarefreeIdealBall.mp (Finset.mem_filter.mp H.property).1).1
    (Finset.mem_filter.mp H.property).2

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped SchwartzMap

/-- Schwartz decay on the Eisenstein lattice gives absolute convergence over all ideals. -/
lemma radial_ideal_summable_norm (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun H : Ideal O => ‖W ((Ideal.absNorm H : ℝ) / M)‖) := by
  have h := (actual_eisenstein_summable_norm (scaledRadialTest W M hM)).comp_injective
    cubicIdealGenerator_injective
  simpa only [Function.comp_def, scaledRadialTest_apply, ringComplex_norm_sq_eq_absNorm_span, span_cubicIdealGenerator] using h

lemma quadraticSourcePair_summable (I J : QuadraticIdeal) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun H : QuadraticSupportedIdeal =>
      (canonicalQuadraticRow I (primaryIdealGenerator H.val) * canonicalQuadraticRow J (primaryIdealGenerator H.val)) *
        W ((Ideal.absNorm H.val : ℝ) / M)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun H => ?_)
    ((radial_ideal_summable_norm W M hM).subtype quadraticSupported)
  rw [norm_mul, norm_mul]
  have hr : ‖canonicalQuadraticRow I (primaryIdealGenerator H.val)‖ *
      ‖canonicalQuadraticRow J (primaryIdealGenerator H.val)‖ ≤ 1 :=
    (mul_le_mul (canonicalQuadraticRow_norm_le_one I _) (canonicalQuadraticRow_norm_le_one J _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  exact mul_le_of_le_one_left (norm_nonneg _) hr

/-- The pair kernel over all ideals supported away from two and three. -/
def quadraticSourcePair (I J : QuadraticIdeal) (W : 𝓢(ℝ, ℂ)) (M : ℝ) : ℂ :=
  ∑' H : QuadraticSupportedIdeal,
    (canonicalQuadraticRow I (primaryIdealGenerator H.val) * canonicalQuadraticRow J (primaryIdealGenerator H.val)) *
      W ((Ideal.absNorm H.val : ℝ) / M)

/-- Separating the square part leaves a squarefree character and a coprimality mask. -/
theorem quadraticSourcePair_squarefree (I J : QuadraticIdeal) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    quadraticSourcePair I J W M =
      ∑' B : QuadraticIdeal, ∑' A : QuadraticSupportedIdeal,
        (canonicalQuadraticRow I (primaryIdealGenerator B.val) * canonicalQuadraticRow J (primaryIdealGenerator B.val)) *
          (quadraticIdealMask I (primaryIdealGenerator A.val) * quadraticIdealMask J (primaryIdealGenerator A.val)) *
            W (((Ideal.absNorm B.val : ℝ) * (Ideal.absNorm A.val : ℝ) ^ 2) / M) := by
  let f : QuadraticSupportedIdeal → ℂ := fun H =>
    (canonicalQuadraticRow I (primaryIdealGenerator H.val) * canonicalQuadraticRow J (primaryIdealGenerator H.val)) *
      W ((Ideal.absNorm H.val : ℝ) / M)
  have hs := quadraticSupportedPartsEquiv.symm.summable_iff.mpr (quadraticSourcePair_summable I J W M hM)
  change Summable (fun p : QuadraticIdeal × QuadraticSupportedIdeal => f (quadraticSupportedPartsEquiv.symm p)) at hs
  have he (p : QuadraticIdeal × QuadraticSupportedIdeal) :
      f (quadraticSupportedPartsEquiv.symm p) =
        (canonicalQuadraticRow I (primaryIdealGenerator p.1.val) * canonicalQuadraticRow J (primaryIdealGenerator p.1.val)) *
          (quadraticIdealMask I (primaryIdealGenerator p.2.val) * quadraticIdealMask J (primaryIdealGenerator p.2.val)) *
            W (((Ideal.absNorm p.1.val : ℝ) * (Ideal.absNorm p.2.val : ℝ) ^ 2) / M) := by
    change (canonicalQuadraticRow I (primaryIdealGenerator (p.1.val * p.2.val ^ 2)) *
      canonicalQuadraticRow J (primaryIdealGenerator (p.1.val * p.2.val ^ 2))) *
      W ((Ideal.absNorm (p.1.val * p.2.val ^ 2) : ℝ) / M) = _
    rw [canonicalQuadraticRow_squarefree_argument, canonicalQuadraticRow_squarefree_argument]
    simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
    ring
  change (∑' H, f H) = _
  rw [← quadraticSupportedPartsEquiv.symm.tsum_eq f, hs.tsum_prod]
  apply tsum_congr
  intro B
  apply tsum_congr
  intro A
  exact he (B, A)

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein UniqueFactorizationMonoid

lemma ideal_coprime_prime_iff_not_dvd (I P : Ideal O) (hP : Prime P) :
    IsCoprime I P ↔ ¬ P ∣ I := by
  constructor
  · intro hc hd
    exact hP.2.1 (hc.isUnit_of_dvd' hd (dvd_refl P))
  · intro hn
    apply Ideal.isCoprime_iff_sup_eq.mpr
    by_contra ht
    have hmax := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
    have he := hmax.eq_of_le ht (le_sup_right : P ≤ I ⊔ P)
    exact hn (Ideal.dvd_iff_le.mpr (he.symm ▸ (le_sup_left : I ≤ I ⊔ P)))

lemma ideal_coprime_support_iff (I J : Ideal O) (hJ : J ≠ 0) :
    IsCoprime I J ↔ ∀ P ∈ primeSupport J, ¬ P ∣ I := by
  constructor
  · intro hc P hP hd
    exact (support_prime hP).2.1
      (hc.isUnit_of_dvd' hd (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)))
  · intro h
    have hp : (∏ P ∈ primeSupport J, P ^ (normalizedFactors J).count P) = J := by
      change (∏ P ∈ (normalizedFactors J).toFinset, P ^ (normalizedFactors J).count P) = J
      rw [← Finset.prod_multiset_count]
      exact Ideal.prod_normalizedFactors_eq_self hJ
    rw [← hp]
    apply IsCoprime.prod_right
    intro P hP
    exact ((ideal_coprime_prime_iff_not_dvd I P (support_prime hP)).mpr (h P hP)).pow_right

lemma primeCoprimeMask_indicator {ι : Type*} (p : ι → O) (S : Finset ι) (z : O) :
    primeCoprimeMask p S z = if ∀ i ∈ S, ¬ p i ∣ z then 1 else 0 := by
  classical
  by_cases h : ∀ i ∈ S, ¬ p i ∣ z
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    rw [if_neg (h i hi), sub_zero]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi, hd⟩ := h
    exact Finset.prod_eq_zero hi (by rw [if_pos hd, sub_self])

lemma primeCoprimeMask_norm_le_one {ι : Type*} (p : ι → O) (S : Finset ι) (z : O) :
    ‖primeCoprimeMask p S z‖ ≤ 1 := by
  rw [primeCoprimeMask_indicator]
  split_ifs <;> norm_num

lemma primeCoprimeMask_unit_mul {ι : Type*} (p : ι → O) (S : Finset ι) (u : Oˣ) (z : O) :
    primeCoprimeMask p S ((u : O) * z) = primeCoprimeMask p S z := by
  have hd (i : ι) : p i ∣ (u : O) * z ↔ p i ∣ z := by
    constructor
    · intro h
      have hh := dvd_mul_of_dvd_right h ((u⁻¹ : Oˣ) : O)
      simpa only [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] using hh
    · intro h
      exact dvd_mul_of_dvd_right h (u : O)
  simp only [primeCoprimeMask, hd]

lemma primeCoprimeMask_zero {ι : Type*} (p : ι → O) (S : Finset ι) (hS : S.Nonempty) :
    primeCoprimeMask p S 0 = 0 := by
  rw [primeCoprimeMask_indicator, if_neg]
  intro h
  exact h hS.choose hS.choose_spec (dvd_zero _)

lemma ideal_generator_dvd_iff (P : Ideal O) (z : O) :
    cubicIdealGenerator P ∣ z ↔ P ∣ Ideal.span {z} := by
  rw [Ideal.dvd_iff_le]
  conv_rhs => rw [← span_cubicIdealGenerator P]
  exact Ideal.span_singleton_le_span_singleton.symm

/-- An ideal prime mask is the indicator of coprimality with its product. -/
lemma primeIdealMask_indicator (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (z : O) :
    primeCoprimeMask cubicIdealGenerator S z =
      if IsCoprime (Ideal.span {z}) (∏ P ∈ S, P) then 1 else 0 := by
  have he : IsCoprime (Ideal.span {z}) (∏ P ∈ S, P) ↔ ∀ P ∈ S, ¬ P ∣ Ideal.span {z} := by
    constructor
    · intro hc P hP hd
      exact (hS P hP).2.1 (hc.isUnit_of_dvd' hd (Finset.dvd_prod_of_mem (fun Q => Q) hP))
    · intro h
      exact IsCoprime.prod_right (fun P hP =>
        (ideal_coprime_prime_iff_not_dvd (Ideal.span {z}) P (hS P hP)).mpr (h P hP))
  simp only [primeCoprimeMask_indicator, ideal_generator_dvd_iff, he]

lemma quadraticMask_coprime_iff (D A : Ideal O) (hD : D ≠ 0) :
    IsCoprime A (quadraticMaskIdeal D) ↔ quadraticSupported A ∧ IsCoprime A D := by
  have he : IsCoprime A (quadraticMaskIdeal D) ↔ ∀ P ∈ quadraticMaskPrimes D, ¬ P ∣ A := by
    constructor
    · intro hc P hP hd
      exact (quadraticMaskPrimes_prime D P hP).2.1
        (hc.isUnit_of_dvd' hd (Finset.dvd_prod_of_mem (fun Q => Q) hP))
    · intro h
      exact IsCoprime.prod_right (fun P hP =>
        (ideal_coprime_prime_iff_not_dvd A P (quadraticMaskPrimes_prime D P hP)).mpr (h P hP))
  rw [he, quadraticSupported_iff_bad_not_dvd, ideal_coprime_support_iff A D hD]
  simp only [quadraticMaskPrimes, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    exact ⟨⟨h _ (Or.inl (Or.inl rfl)), h _ (Or.inl (Or.inr rfl))⟩,
      fun P hP => h P (Or.inr hP)⟩
  · rintro ⟨⟨hr, ht⟩, hd⟩ P (hp | hp)
    · rcases hp with rfl | rfl
      · exact hr
      · exact ht
    · exact hd P hp

lemma quadraticMask_generator_indicator (D A : Ideal O) (hD : D ≠ 0) :
    primeCoprimeMask cubicIdealGenerator (quadraticMaskPrimes D) (cubicIdealGenerator A) =
      if quadraticSupported A ∧ IsCoprime A D then 1 else 0 := by
  rw [primeIdealMask_indicator _ (quadraticMaskPrimes_prime D), span_cubicIdealGenerator]
  change (if IsCoprime A (quadraticMaskIdeal D) then (1 : ℂ) else 0) = _
  simp only [quadraticMask_coprime_iff D A hD]

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped SchwartzMap

lemma quadraticIdealMask_indicator (I : QuadraticIdeal) (z : O) :
    quadraticIdealMask I z = if IsCoprime (Ideal.span {z}) I.val then 1 else 0 := by
  have hd (P : QuadraticPrime) : quadraticPrimeGenerator P ∣ z ↔ P.val ∣ Ideal.span {z} := by
    rw [Ideal.dvd_iff_le]
    conv_rhs => rw [← quadraticPrimeGenerator_span P]
    exact Ideal.span_singleton_le_span_singleton.symm
  have he : (∀ P ∈ quadraticIdealSupport I, ¬ quadraticPrimeGenerator P ∣ z) ↔
      IsCoprime (Ideal.span {z}) I.val := by
    rw [ideal_coprime_support_iff _ _ (primaryIdealGenerator_ne_zero_ideal I.val I.property.1)]
    simp only [hd]
    constructor
    · intro h P hP
      let Q := quadraticIdealPrimeIndex I ⟨P, hP⟩
      exact h Q ((mem_quadraticIdealSupport I Q).mpr hP)
    · intro h P hP
      exact h P.val ((mem_quadraticIdealSupport I P).mp hP)
  simp only [quadraticIdealMask, primeCoprimeMask_indicator, he]

lemma quadratic_joint_mask_generator (I J : QuadraticIdeal) (A : Ideal O) :
    primeCoprimeMask cubicIdealGenerator (quadraticMaskPrimes (I.val * J.val)) (cubicIdealGenerator A) =
      if quadraticSupported A then
        quadraticIdealMask I (primaryIdealGenerator A) * quadraticIdealMask J (primaryIdealGenerator A) else 0 := by
  have hIJ := mul_ne_zero (primaryIdealGenerator_ne_zero_ideal I.val I.property.1)
    (primaryIdealGenerator_ne_zero_ideal J.val J.property.1)
  rw [quadraticMask_generator_indicator _ _ hIJ]
  have hc : IsCoprime A (I.val * J.val) ↔ IsCoprime A I.val ∧ IsCoprime A J.val := by
    constructor
    · intro h
      exact ⟨h.mono (dvd_refl A) (dvd_mul_right I.val J.val),
        h.mono (dvd_refl A) (dvd_mul_left J.val I.val)⟩
    · rintro ⟨hI, hJ⟩
      exact hI.mul_right hJ
  by_cases hA : quadraticSupported A
  · rw [if_pos hA, quadraticIdealMask_indicator, quadraticIdealMask_indicator,
      (primaryIdealGenerator_spec A hA.1).1]
    by_cases hI : IsCoprime A I.val <;> by_cases hJ : IsCoprime A J.val <;> simp [hA, hc, hI, hJ]
  · simp only [hA, false_and, ite_false]

/-- The low squarefree part leaves a radial sum in the remaining square variable. -/
def quadraticLowPrincipalIdeal (I J : QuadraticIdeal) (W : 𝓢(ℝ, ℂ)) (X : ℝ) : ℂ :=
  ∑' A : QuadraticSupportedIdeal,
    (quadraticIdealMask I (primaryIdealGenerator A.val) * quadraticIdealMask J (primaryIdealGenerator A.val)) *
      W (((Ideal.absNorm A.val : ℝ) / X) ^ 2)

def quadraticLowPrincipalLattice (I J : QuadraticIdeal) (W : 𝓢(ℝ, ℂ)) (X : ℝ) : ℂ :=
  ∑' z : O, primeCoprimeMask cubicIdealGenerator (quadraticMaskPrimes (I.val * J.val)) z *
    W ((‖ringComplex z‖ ^ 2 / X) ^ 2)

/-- The full unit orbit converts the principal lattice sum exactly into its ideal sum. -/
theorem quadraticLowPrincipalLattice_eq (I J : QuadraticIdeal) (W : 𝓢(ℝ, ℂ))
    (X : ℝ) (hX : 0 < X) :
    quadraticLowPrincipalLattice I J W X = (Nat.card Oˣ : ℂ) * quadraticLowPrincipalIdeal I J W X := by
  let S := quadraticMaskPrimes (I.val * J.val)
  let V := quadraticSquareProfile W
  let f : O → ℂ := fun z => primeCoprimeMask cubicIdealGenerator S z * V (‖ringComplex z‖ ^ 2 / X)
  have hv : Summable (fun z : O => ‖V (‖ringComplex z‖ ^ 2 / X)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest V X hX)
  have hf : Summable f := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_) hv
    dsimp only [f]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (primeCoprimeMask_norm_le_one _ _ _)
  have h0 : f 0 = 0 := by
    dsimp only [f]
    rw [primeCoprimeMask_zero _ _ ?_, zero_mul]
    exact ⟨ramifiedIdeal, Finset.mem_union_left _ (Finset.mem_insert_self _ _)⟩
  have hu (u : Oˣ) (z : O) : f ((u : O) * z) = f z := by
    dsimp only [f]
    rw [primeCoprimeMask_unit_mul, map_mul, norm_mul, norm_ringComplex_unit, one_mul]
  have he := tsum_unit_invariant_ideals f hf h0 hu
  have hn (A : Ideal O) : ‖ringComplex (cubicIdealGenerator A)‖ ^ 2 = (Ideal.absNorm A : ℝ) := by
    rw [ringComplex_norm_sq_eq_absNorm_span, span_cubicIdealGenerator]
  simp only [f, V, quadraticSquareProfile_apply, hn] at he
  have hi : (∑' A : NonzeroIdeal, primeCoprimeMask cubicIdealGenerator S (cubicIdealGenerator A.val) *
      W (((Ideal.absNorm A.val : ℝ) / X) ^ 2)) = quadraticLowPrincipalIdeal I J W X := by
    let F : Ideal O → ℂ := fun A => if quadraticSupported A then
      (quadraticIdealMask I (primaryIdealGenerator A) * quadraticIdealMask J (primaryIdealGenerator A)) *
        W (((Ideal.absNorm A : ℝ) / X) ^ 2) else 0
    calc
      _ = ∑' A : NonzeroIdeal, F A.val := by
        apply tsum_congr
        intro A
        rw [quadratic_joint_mask_generator]
        by_cases hA : quadraticSupported A.val <;> simp only [F, hA, ite_true, ite_false, zero_mul]
      _ = ∑' A : Ideal O, F A := by
        apply tsum_subtype_eq_of_support_subset
        intro A hA hz
        subst A
        exact hA (by simp [F, quadraticSupported, primaryIdealGenerator_zero])
      _ = _ := by
        change (∑' A : Ideal O, ({A | quadraticSupported A} : Set (Ideal O)).indicator
          (fun A => (quadraticIdealMask I (primaryIdealGenerator A) * quadraticIdealMask J (primaryIdealGenerator A)) *
            W (((Ideal.absNorm A : ℝ) / X) ^ 2)) A) = _
        exact (_root_.tsum_subtype _ _).symm
  rw [hi] at he
  exact he

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped SchwartzMap

/-- Any polynomial tail gain survives summation over the Eisenstein lattice. -/
theorem paperRadialFourier_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K T : ℝ), 0 < K → 0 ≤ T →
        (∑' z : {z : O // T ≤ K * ‖ringComplex z‖ ^ 2},
          ‖paperRadialFourier W (K * ‖ringComplex z.val‖ ^ 2)‖) ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound (A + 2)
  refine ⟨s, C * (eisensteinCauchyMass + 1), by have := eisensteinCauchyMass_nonneg; positivity, ?_⟩
  intro W K T hK hT
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let D := (min 1 K) ^ 2 * (1 + T) ^ A
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hp (z : {z : O // T ≤ K * ‖ringComplex z‖ ^ 2}) :
      ‖paperRadialFourier W (K * ‖ringComplex z.val‖ ^ 2)‖ ≤
        (B / D) * ((1 + ‖ringComplex z.val‖ ^ 2) ^ 2)⁻¹ :=
    polynomial_tail_majorant A K T _ B _ hK hT (sq_nonneg _) (norm_nonneg _)
      z.property (hb W _ (mul_nonneg hK.le (sq_nonneg _)))
  have hs := (paperRadialFourier_lattice_summable_norm W K hK).subtype
    (fun z => T ≤ K * ‖ringComplex z‖ ^ 2)
  calc
    _ ≤ ∑' z : {z : O // T ≤ K * ‖ringComplex z‖ ^ 2},
        (B / D) * ((1 + ‖ringComplex z.val‖ ^ 2) ^ 2)⁻¹ :=
      hs.tsum_le_tsum hp ((eisenstein_cauchy_summable.subtype _).mul_left (B / D))
    _ = (B / D) * ∑' z : {z : O // T ≤ K * ‖ringComplex z‖ ^ 2},
        ((1 + ‖ringComplex z.val‖ ^ 2) ^ 2)⁻¹ := tsum_mul_left
    _ ≤ (B / D) * eisensteinCauchyMass :=
      mul_le_mul_of_nonneg_left (eisensteinCauchyMass_subtype _) (div_nonneg hB hD.le)
    _ ≤ (B / D) * (eisensteinCauchyMass + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hB hD.le)
    _ = _ := by dsimp only [B, D]; ring

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory Set
open scoped SchwartzMap FourierTransform

/-- Integrating one Fourier coordinate restricts the original Schwartz function to the other axis. -/
lemma fourier_real_axis_integral (f : 𝓢(ℂ, ℂ)) :
    (∫ x : ℝ, 𝓕 (f : ℂ → ℂ) (x : ℂ)) = ∫ y : ℝ, f (Complex.I * (y : ℂ)) := by
  let g := partialFourier f 0
  have hF : 𝓕 g = fun x : ℝ => 𝓕 (f : ℂ → ℂ) (x : ℂ) := by
    funext x
    simpa only [g, complexPoint_eq, Complex.ofReal_zero, mul_zero, add_zero] using fourier_partialFourier f x 0
  have hgi : Integrable (𝓕 g) := by
    rw [hF]
    have hs := (horizontalSlice (𝓕 f) 0).integrable (μ := volume)
    change Integrable (fun x : ℝ => (𝓕 f) (complexPoint x 0)) at hs
    simpa only [complexPoint_eq, mul_zero, add_zero,
      Complex.ofReal_zero, SchwartzMap.fourier_coe] using hs
  have hinv : 𝓕⁻ (𝓕 g) (0 : ℝ) = g 0 :=
    (partialFourier_integrable f 0).fourierInv_fourier_eq hgi
      (partialFourier_continuous f 0).continuousAt
  calc
    _ = ∫ x : ℝ, 𝓕 g x := by rw [hF]
    _ = 𝓕⁻ (𝓕 g) 0 := by simp [Real.fourierInv_eq]
    _ = g 0 := hinv
    _ = _ := by simp [g, partialFourier_eq_integral, complexPoint_eq]

lemma paperRadialFourier_square_real_axis (W : 𝓢(ℝ, ℂ)) (x : ℝ) :
    paperRadialFourier W (x ^ 2) = (2 / Real.sqrt 3 : ℝ) •
      𝓕 (radialTest W : ℂ → ℂ) (((x / (ringComplex omega).im : ℝ) : ℂ)) := by
  have hn : ‖(x : ℂ) * Complex.I‖ ^ 2 = x ^ 2 := by
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hfreq : paperFrequency ((x : ℂ) * Complex.I) = (((x / (ringComplex omega).im : ℝ) : ℂ)) := by
    rw [paperFrequency_coordinates]
    simp [complexPoint_eq]
  have h := paperFourier_radial W ((x : ℂ) * Complex.I)
  rw [hn, paperFourier_eq_standard, hfreq] at h
  exact h.symm

/-- The trace-dual normalization preserves the integral of the squared radial profile. -/
lemma paperRadialFourier_square_integral (W : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, paperRadialFourier W (x ^ 2)) = ∫ x : ℝ, W (x ^ 2) := by
  have hscale : (2 / Real.sqrt 3 : ℝ) * (Real.sqrt 3 / 2) = 1 := by
    have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
  calc
    _ = (2 / Real.sqrt 3 : ℝ) •
        ∫ x : ℝ, 𝓕 (radialTest W : ℂ → ℂ) ((((ringComplex omega).im)⁻¹ * x : ℝ) : ℂ) := by
      simp only [paperRadialFourier_square_real_axis, div_eq_mul_inv, mul_comm, integral_smul]
    _ = ∫ x : ℝ, 𝓕 (radialTest W : ℂ → ℂ) (x : ℂ) := by
      rw [Measure.integral_comp_mul_left
        (fun x : ℝ => 𝓕 (radialTest W : ℂ → ℂ) (x : ℂ)) ((ringComplex omega).im)⁻¹]
      rw [inv_inv, complex_omega_im_abs, smul_smul, hscale, one_smul]
    _ = ∫ y : ℝ, radialTest W (Complex.I * (y : ℂ)) := fourier_real_axis_integral _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp [radialTest_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]

lemma integral_even_twice_halfline (F : ℝ → ℂ) (hF : Integrable F)
    (heven : ∀ x, F (-x) = F x) :
    (∫ x : ℝ, F x) = 2 * ∫ x : ℝ in Ioi 0, F x := by
  have hn : (∫ x : ℝ in Iic 0, F x) = ∫ x : ℝ in Ioi 0, F x := by
    calc
      _ = ∫ x : ℝ in Ioi 0, F (-x) := by simp
      _ = _ := setIntegral_congr_fun measurableSet_Ioi (fun x _ => heven x)
  rw [← integral_add_compl (s := Ioi 0) measurableSet_Ioi hF, compl_Ioi, hn]
  ring

lemma paperRadialFourier_halfline_integral (W : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ in Ioi 0, paperRadialFourier W (x ^ 2)) = ∫ x : ℝ in Ioi 0, W (x ^ 2) := by
  have hd : Integrable (fun x : ℝ => paperRadialFourier W (x ^ 2)) := by
    have h := (quadraticTransformedSquareProfile W).integrable (μ := volume)
    change Integrable (fun x : ℝ => quadraticTransformedSquareProfile W x) at h
    simpa only [quadraticTransformedSquareProfile_apply] using h
  have hs : Integrable (fun x : ℝ => W (x ^ 2)) := by
    have h := (quadraticSquareProfile W).integrable (μ := volume)
    change Integrable (fun x : ℝ => quadraticSquareProfile W x) at h
    simpa only [quadraticSquareProfile_apply] using h
  have h := paperRadialFourier_square_integral W
  rw [integral_even_twice_halfline _ hd (by intro x; simp),
    integral_even_twice_halfline _ hs (by intro x; simp)] at h
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory Set
open scoped SchwartzMap

/-- Area measure for a squared radial variable is π times Lebesgue measure on the positive half-line. -/
lemma complex_radial_norm_sq_integral (F : ℝ → ℂ) :
    (∫ z : ℂ, F (‖z‖ ^ 2)) = (Real.pi : ℂ) * ∫ t : ℝ in Ioi 0, F t := by
  have hv : volume.real (Metric.ball (0 : ℂ) 1) = Real.pi := by
    rw [measureReal_def, Complex.volume_ball]
    simp
  have hs : (2 : ℝ) • (∫ r : ℝ in Ioi 0, r • F (r ^ 2)) = ∫ t : ℝ in Ioi 0, F t := by
    have h := integral_comp_rpow_Ioi_of_pos (g := F) (by norm_num : (0 : ℝ) < 2)
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
      mul_smul, integral_smul] using h
  rw [integral_fun_norm_addHaar volume (fun r => F (r ^ 2)), Complex.finrank_real_complex, hv]
  norm_num only [Nat.reduceSub, pow_one]
  rw [← hs]
  simp only [Complex.real_smul, nsmul_eq_mul, Complex.ofReal_ofNat]
  ring

lemma paperRadialFourier_zero_eq_halfline (F : ℝ → ℂ) :
    paperRadialFourier F 0 = (2 * Real.pi / Real.sqrt 3 : ℂ) * ∫ t : ℝ in Ioi 0, F t := by
  have he : paperE 0 = 1 := by simp [paperE]
  simp only [paperRadialFourier, paperFourier, Real.sqrt_zero, Complex.ofReal_zero,
    mul_zero, neg_zero, he, one_mul]
  rw [complex_radial_norm_sq_integral]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

/-- The source and transformed square profiles have identical principal Poisson terms. -/
theorem quadraticSquareProfile_principal_equal (W : 𝓢(ℝ, ℂ)) :
    paperRadialFourier (quadraticTransformedSquareProfile W) 0 =
      paperRadialFourier (quadraticSquareProfile W) 0 := by
  rw [paperRadialFourier_zero_eq_halfline, paperRadialFourier_zero_eq_halfline]
  congr 1
  simpa only [quadraticTransformedSquareProfile_apply, quadraticSquareProfile_apply] using
    paperRadialFourier_halfline_integral W

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped SchwartzMap

lemma eisenstein_unit_card_ne_zero : (Nat.card Oˣ : ℂ) ≠ 0 := by
  letI : Finite Oˣ := cubic_units_finite
  letI : Fintype Oˣ := Fintype.ofFinite _
  exact Nat.cast_ne_zero.mpr (by rw [Nat.card_eq_fintype_card]; exact Fintype.card_ne_zero)

/-- A masked same-ray source pair descends to the unrestricted ideal sum. -/
theorem canonicalQuadraticPair_source_ideal_reindex {κ : Type*}
    (I J : QuadraticIdeal) (hray : quadraticColumnRay I = quadraticColumnRay J)
    (hnt : I.val ≠ 1 ∨ J.val ≠ 1) (q : κ → O) (S : Finset κ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, primeCoprimeMask q S z * (canonicalQuadraticRow I z * canonicalQuadraticRow J z) *
      W (‖ringComplex z‖ ^ 2 / Y)) =
      (Nat.card Oˣ : ℂ) * ∑' D : NonzeroIdeal,
        primeCoprimeMask q S (cubicIdealGenerator D.val) * canonicalQuadraticPairIdeal I J D.val *
          W ((Ideal.absNorm D.val : ℝ) / Y) := by
  let f : O → ℂ := fun z => primeCoprimeMask q S z *
    (canonicalQuadraticRow I z * canonicalQuadraticRow J z) * W (‖ringComplex z‖ ^ 2 / Y)
  have hs : Summable (fun z : O => ‖W (‖ringComplex z‖ ^ 2 / Y)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest W Y hY)
  have hf : Summable f := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_) hs
    dsimp only [f]
    rw [norm_mul, norm_mul, norm_mul]
    have hpair : ‖canonicalQuadraticRow I z‖ * ‖canonicalQuadraticRow J z‖ ≤ 1 :=
      (mul_le_mul (canonicalQuadraticRow_norm_le_one I z) (canonicalQuadraticRow_norm_le_one J z)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have hm : ‖primeCoprimeMask q S z‖ * (‖canonicalQuadraticRow I z‖ * ‖canonicalQuadraticRow J z‖) ≤ 1 :=
      (mul_le_mul (primeCoprimeMask_norm_le_one q S z) hpair (by positivity) zero_le_one).trans_eq (one_mul 1)
    exact mul_le_of_le_one_left (norm_nonneg _) hm
  have h0 : f 0 = 0 := by
    dsimp only [f]
    rw [canonicalQuadraticPair_zero I J hnt, mul_zero, zero_mul]
  have hu (u : Oˣ) (z : O) : f ((u : O) * z) = f z := by
    dsimp only [f]
    rw [primeCoprimeMask_unit_mul, canonicalQuadraticPair_unit_invariant I J hray,
      map_mul, norm_mul, norm_ringComplex_unit, one_mul]
  simpa only [f, canonicalQuadraticPairIdeal, ringComplex_norm_sq_eq_absNorm_span,
    span_cubicIdealGenerator] using tsum_unit_invariant_ideals f hf h0 hu

/-- The unit multiplicity cancels between source and dual, leaving an exact ideal Poisson identity. -/
theorem canonical_same_ray_pair_ideal_poisson {κ : Type*}
    (I J : QuadraticIdeal) (hcop : IsCoprime I.val J.val)
    (hray : quadraticColumnRay I = quadraticColumnRay J) (hnt : I.val ≠ 1 ∨ J.val ≠ 1)
    (q : κ → O) (hq : ∀ i, q i ≠ 0) (hqc : Pairwise (Function.onFun IsCoprime q)) (S : Finset κ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' D : NonzeroIdeal,
      primeCoprimeMask q S (cubicIdealGenerator D.val) * canonicalQuadraticPairIdeal I J D.val *
        W ((Ideal.absNorm D.val : ℝ) / Y)) =
      ((Y : ℂ) / (‖ringComplex (primaryIdealGenerator I.val * primaryIdealGenerator J.val)‖ : ℂ)) *
        ∑ E ∈ S.powerset,
          ((-1 : ℂ) ^ E.card * canonicalQuadraticPairIdeal I J (Ideal.span {∏ i ∈ E, q i}) /
            (‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 : ℝ)) *
            ∑' D : NonzeroIdeal, canonicalQuadraticPairIdeal I J D.val *
              paperRadialFourier W (Y * (Ideal.absNorm D.val : ℝ) /
                (‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 *
                  ‖ringComplex (primaryIdealGenerator I.val * primaryIdealGenerator J.val)‖ ^ 2)) := by
  classical
  have hn : primaryIdealGenerator I.val * primaryIdealGenerator J.val ≠ 0 :=
    mul_ne_zero I.property.1 J.property.1
  have hd (E : Finset κ) :
      (∑' z : O, (canonicalQuadraticRow I z * canonicalQuadraticRow J z) *
        paperRadialFourier W (Y * ‖ringComplex z‖ ^ 2 /
          (‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 *
            ‖ringComplex (primaryIdealGenerator I.val * primaryIdealGenerator J.val)‖ ^ 2))) =
        (Nat.card Oˣ : ℂ) * ∑' D : NonzeroIdeal, canonicalQuadraticPairIdeal I J D.val *
          paperRadialFourier W (Y * (Ideal.absNorm D.val : ℝ) /
            (‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 *
              ‖ringComplex (primaryIdealGenerator I.val * primaryIdealGenerator J.val)‖ ^ 2)) := by
    have he : (∏ i ∈ E, q i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hq i)
    have hden : 0 < ‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 *
        ‖ringComplex (primaryIdealGenerator I.val * primaryIdealGenerator J.val)‖ ^ 2 :=
      mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero he)))
        (sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hn)))
    simpa only [div_mul_eq_mul_div] using canonicalQuadraticPair_fourier_ideal_reindex
      I J hray hnt W _ (div_pos hY hden)
  have hp := canonical_same_ray_pair_poisson I J hcop hray q hq hqc S W Y hY
  rw [canonicalQuadraticPair_source_ideal_reindex I J hray hnt q S W Y hY] at hp
  simp_rw [hd, ← canonicalQuadraticPairIdeal_span I J hray] at hp
  apply mul_left_cancel₀ eisenstein_unit_card_ne_zero
  rw [hp]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  ring

end SchwartzPlanePoisson

open scoped BigOperators Classical SchwartzMap

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory

theorem radial_source_nonzero_lattice_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K : ℝ), 1 ≤ K →
        (∑' h : {h : O // h ≠ 0}, ‖W (K * ‖ringComplex h.val‖ ^ 2)‖) ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + K) ^ A := by
  let s : Finset (ℕ × ℕ) := Finset.Iic (A + 2, 0)
  let C : ℝ := 2 ^ (A + 2) * (eisensteinCauchyMass + 1)
  have hC : 0 < C := by
    have hm := eisensteinCauchyMass_nonneg
    dsimp [C]
    positivity
  refine ⟨s, C, hC, ?_⟩
  intro W K hK
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let B : ℝ := 2 ^ (A + 2) * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (q : ℝ) (hq : 0 ≤ q) : (1 + q) ^ (A + 2) * ‖W q‖ ≤ B := by
    have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (A + 2, 0)) (k := A + 2) (n := 0) le_rfl le_rfl W q
    simp only [norm_iteratedFDeriv_zero, Real.norm_of_nonneg hq] at hh
    change (1 + q) ^ (A + 2) * ‖W q‖ ≤ B at hh
    exact hh
  have hp (h : {h : O // h ≠ 0}) : ‖W (K * ‖ringComplex h.val‖ ^ 2)‖ ≤
      (B / (1 + K) ^ A) * ((1 + ‖ringComplex h.val‖ ^ 2) ^ 2)⁻¹ := by
    have hq : K ≤ K * ‖ringComplex h.val‖ ^ 2 := by
      nlinarith [one_le_eisenstein_norm_sq h.val h.property]
    have hh := polynomial_tail_majorant A K K (‖ringComplex h.val‖ ^ 2) B
      ‖W (K * ‖ringComplex h.val‖ ^ 2)‖ hK0 hK0.le (sq_nonneg _) (norm_nonneg _) hq
      (hb _ (by positivity))
    simpa only [min_eq_left hK, one_pow, one_mul] using hh
  have hmajor := (eisenstein_cauchy_summable.subtype (fun h => h ≠ 0)).mul_left
    (B / (1 + K) ^ A)
  have hs : Summable (fun h : {h : O // h ≠ 0} => ‖W (K * ‖ringComplex h.val‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp hmajor
  calc
    _ ≤ ∑' h : {h : O // h ≠ 0},
        (B / (1 + K) ^ A) * ((1 + ‖ringComplex h.val‖ ^ 2) ^ 2)⁻¹ :=
      hs.tsum_le_tsum hp hmajor
    _ = (B / (1 + K) ^ A) * ∑' h : {h : O // h ≠ 0},
        ((1 + ‖ringComplex h.val‖ ^ 2) ^ 2)⁻¹ := tsum_mul_left
    _ ≤ (B / (1 + K) ^ A) * eisensteinCauchyMass :=
      mul_le_mul_of_nonneg_left (eisensteinCauchyMass_subtype {h : O | h ≠ 0}) (by positivity)
    _ ≤ (B / (1 + K) ^ A) * (eisensteinCauchyMass + 1) := by
      gcongr
      linarith
    _ = _ := by dsimp [B, C]; ring

end SchwartzPlanePoisson

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
