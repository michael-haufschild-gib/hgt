import GaloisForLFunctions.HTGeometry.TranslationStableDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.MeromorphicReflectionTransport

/-!
# The reflection covers an automorphism of the coordinate field, and flips the jets

Differential algebraicity over `RatFunc C` transports along an automorphism of the meromorphic field
that covers an automorphism of the coordinate field and is compatible with the jets.  For the
translation the corpus already has both inputs.  This file supplies them for the reflection
`z |-> c - z`:

* it restricts to the coordinate automorphism `r(X) |-> r(C c - X)` of `RatFunc C`, which is an
  involution;
* it flips the jets by a sign, `jet n (reflect x) = (-1)^n · reflect (jet n x)`, because the
  reflection anti-commutes with the derivation.

The sign is the only difference from the translation case, and it is exactly one unit of the base
field per jet index.
-/

open Filter Topology Set Function Polynomial
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra

/-! ### The reflection of the coordinate field -/

/-- Precomposition of a polynomial with `C c - X`, landing in the rational function field. -/
def reflectCompHomBy (c : ℂ) : Polynomial ℂ →+* RatFunc ℂ :=
  (algebraMap (Polynomial ℂ) (RatFunc ℂ)).comp
    (Polynomial.aeval (Polynomial.C c - Polynomial.X) :
      Polynomial ℂ →ₐ[ℂ] Polynomial ℂ).toRingHom

theorem reflectCompHomBy_apply (c : ℂ) (p : Polynomial ℂ) :
    reflectCompHomBy c p
      = algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (p.comp (Polynomial.C c - Polynomial.X)) := by
  rw [reflectCompHomBy, RingHom.comp_apply]
  rfl

/-- Reflecting the variable of a nonzero polynomial keeps it nonzero: the substituted polynomial is
not constant. -/
theorem comp_reflect_ne_zero {c : ℂ} {p : Polynomial ℂ} (hp : p ≠ 0) :
    p.comp (Polynomial.C c - Polynomial.X) ≠ 0 := by
  intro hzero
  apply hp
  apply Polynomial.funext
  intro z
  have hz := congrArg (fun q => Polynomial.eval (c - z) q) hzero
  simpa [Polynomial.eval_comp] using hz

theorem reflectCompHomBy_mem_nonZeroDivisors (c : ℂ) :
    nonZeroDivisors (Polynomial ℂ)
      ≤ Submonoid.comap (reflectCompHomBy c) (nonZeroDivisors (RatFunc ℂ)) := by
  intro p hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  rw [mem_nonZeroDivisors_iff_ne_zero] at hp
  rw [reflectCompHomBy_apply]
  intro h0
  exact comp_reflect_ne_zero hp
    (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))

/-- The reflection endomorphism `r(X) |-> r(C c - X)` of the rational function field. -/
def ratReflectBy (c : ℂ) : RatFunc ℂ →+* RatFunc ℂ :=
  RatFunc.liftRingHom (reflectCompHomBy c) (reflectCompHomBy_mem_nonZeroDivisors c)

theorem ratReflectBy_algebraMap (c : ℂ) (p : Polynomial ℂ) :
    ratReflectBy c (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (p.comp (Polynomial.C c - Polynomial.X)) := by
  have h := RatFunc.liftRingHom_apply_div (reflectCompHomBy c)
    (reflectCompHomBy_mem_nonZeroDivisors c) p 1
  simp only [map_one, div_one] at h
  rw [ratReflectBy, h, reflectCompHomBy_apply]

theorem ratReflectBy_involutive (c : ℂ) (r : RatFunc ℂ) :
    ratReflectBy c (ratReflectBy c r) = r := by
  have hhom : (ratReflectBy c).comp (ratReflectBy c) = RingHom.id (RatFunc ℂ) := by
    apply IsFractionRing.ringHom_ext (A := Polynomial ℂ)
    intro p
    rw [RingHom.comp_apply, ratReflectBy_algebraMap, ratReflectBy_algebraMap,
      RingHom.id_apply]
    congr 1
    rw [Polynomial.comp_assoc]
    have hx : (Polynomial.C c - Polynomial.X).comp
        (Polynomial.C c - Polynomial.X) = Polynomial.X := by
      simp
    rw [hx, Polynomial.comp_X]
  exact RingHom.congr_fun hhom r

/-- The reflection automorphism of the rational function field. -/
def ratReflectEquivBy (c : ℂ) : RatFunc ℂ ≃+* RatFunc ℂ where
  toFun := ratReflectBy c
  invFun := ratReflectBy c
  left_inv := ratReflectBy_involutive c
  right_inv := ratReflectBy_involutive c
  map_mul' := map_mul _
  map_add' := map_add _

/-! ### The reflection covers it -/

theorem complexReflectionAnalyticEquiv_polyToAnalytic (c : ℂ) (p : Polynomial ℂ) :
    complexReflectionAnalyticEquiv c (polyToAnalytic Set.univ p) =
      polyToAnalytic Set.univ (p.comp (Polynomial.C c - Polynomial.X)) := by
  apply Subtype.ext
  rw [show ((complexReflectionAnalyticEquiv c (polyToAnalytic Set.univ p) :
      analyticSubring Set.univ) : Germ (𝓟 Set.univ) ℂ) =
        ((polyToAnalytic Set.univ p : analyticSubring Set.univ) :
          Germ (𝓟 Set.univ) ℂ).compTendsto (complexReflection c)
            (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)) from rfl]
  change Germ.ofFun (l := 𝓟 Set.univ) (fun z => p.eval (c - z)) =
    Germ.ofFun (l := 𝓟 Set.univ)
      (fun z => (p.comp (Polynomial.C c - Polynomial.X)).eval z)
  rw [Germ.coe_eq]
  exact eventually_principal.mpr fun z _ => by
    simp [Polynomial.eval_comp]

/-- **The reflection of the meromorphic field restricts to the coordinate reflection.** -/
theorem complexReflectionMeroEquiv_ratfuncToMero (c : ℂ) (r : RatFunc ℂ) :
    complexReflectionMeroEquiv c
        (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ r)
      = ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ (ratReflectBy c r) := by
  let rho := ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ
  have hhom : (complexReflectionMeroEquiv c).toRingHom.comp rho
      = rho.comp (ratReflectBy c) := by
    refine IsFractionRing.ringHom_ext (A := Polynomial ℂ) (K := RatFunc ℂ) ?_
    intro p
    rw [RingHom.comp_apply, RingHom.comp_apply,
      ratfuncToMero_algebraMap_polynomial, ratReflectBy_algebraMap,
      ratfuncToMero_algebraMap_polynomial]
    simp only [polyToMero, RingHom.comp_apply]
    change complexReflectionMeroEquiv c
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (polyToAnalytic Set.univ p)) = _
    rw [complexReflectionMeroEquiv_algebraMap,
      complexReflectionAnalyticEquiv_polyToAnalytic]
  exact RingHom.congr_fun hhom r

/-! ### The jets flip sign -/

/-- **Jets anti-commute with the reflection.**  Each derivation contributes one sign. -/
theorem differentialJet_complexReflectionMeroEquiv (c : ℂ) (n : ℕ)
    (x : meroField (Set.univ : Set ℂ)) :
    differentialJet n (complexReflectionMeroEquiv c x)
      = (-1 : meroField (Set.univ : Set ℂ)) ^ n *
        complexReflectionMeroEquiv c (differentialJet n x) := by
  induction n with
  | zero => rw [differentialJet_zero, differentialJet_zero, pow_zero, one_mul]
  | succ k ih =>
      have hd : (complexReflectionMeroEquiv c (differentialJet k x))′
          = -(complexReflectionMeroEquiv c (differentialJet (k + 1) x)) := by
        rw [differentialJet_succ,
          complexReflectionMeroEquiv_deriv c (differentialJet k x), neg_neg]
      rw [differentialJet_succ, ih]
      rcases Nat.even_or_odd k with hk | hk
      · rw [hk.neg_one_pow, one_mul, hd, (hk.add_one).neg_one_pow]
        ring
      · rw [hk.neg_one_pow, neg_one_mul, map_neg, hd, (hk.add_one).neg_one_pow]
        ring

end

end GaloisForLFunctions.HTGeometry
