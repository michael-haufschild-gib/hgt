import GaloisForLFunctions.HTGeometry.RationalNonSummability
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.Real.Irrational

/-!
# The multiplicative `q`-orbit residue obstruction to rational summability

`RationalNonSummability` proves that a rational function with exactly one pole on an *additive*
integer orbit `c + ℤ` is not a telescoped difference for the unit shift.  The double-sine
hypertranscendence argument needs the same obstruction on a *multiplicative* orbit `p₀ q^ℤ`, where
`q` is not a root of unity: after descending the paired telescoping relation to one multiplicative
cylinder, the equation to be contradicted is

```text
h(qX) - h(X) = A(b)(X),
```

with `h` rational and the right side carrying a single pole on the orbit `q^ℤ`.

Two things are built here.

Everything is proved over an arbitrary base field `K` (characteristic zero only where the additive
orbit is used), which is what removes the specialization step from the double-sine descent: the
descended equation lives in `ℂ(u₁)(u₂)`, and taking `K = ℂ(u₁)` applies the obstruction there
directly.

1. The dilation `X ↦ q X` as an algebra endomorphism `ratFuncScale q` of `K(X)`, together with the
   exact transport of regularity, `RegularAt (ratFuncScale q g) w ↔ RegularAt g (q w)`.  The
   dilation is genuine — it is the localization of the polynomial substitution `p ↦ p(qX)` — so the
   obstruction below is a statement about the actual `q`-difference equation, not about an abstract
   pole bookkeeping relation.

2. The orbit obstruction for an *arbitrary injective* orbit `orb : ℤ → ℂ`.  The additive proof used
   only that the orbit is injective and that the shifted function's poles are the orbit-translated
   poles of the original; both hypotheses are isolated here, so the additive and multiplicative
   cases become two instances of one theorem.

The main result is `not_dilationTelescoped_of_unique_multOrbit_pole`.
-/

open Polynomial

namespace GaloisForLFunctions

variable {K : Type*} [Field K]

noncomputable section

/-! ## Substituting `q X` in a polynomial -/

/-- Substituting `q * X` for the variable of a polynomial. -/
def polyScale (q : K) : Polynomial K →ₐ[K] Polynomial K :=
  Polynomial.aeval (Polynomial.C q * Polynomial.X)

theorem polyScale_eq_comp (q : K) (p : Polynomial K) :
    polyScale q p = p.comp (C q * X) := by
  rw [polyScale, Polynomial.aeval_def, Polynomial.comp, Polynomial.algebraMap_eq]

@[simp] theorem polyScale_X (q : K) : polyScale q X = C q * X := by
  rw [polyScale_eq_comp, Polynomial.X_comp]

@[simp] theorem eval_polyScale (q : K) (p : Polynomial K) (w : K) :
    (polyScale q p).eval w = p.eval (q * w) := by
  rw [polyScale_eq_comp, Polynomial.eval_comp]
  simp

theorem polyScale_polyScale (q r : K) (p : Polynomial K) :
    polyScale q (polyScale r p) = polyScale (q * r) p := by
  have h : (polyScale q).comp (polyScale r) = polyScale (q * r) := by
    refine Polynomial.algHom_ext ?_
    rw [AlgHom.comp_apply, polyScale_X, polyScale_X, polyScale_eq_comp, Polynomial.mul_comp,
      Polynomial.C_comp, Polynomial.X_comp, Polynomial.C_mul]
    ring
  have h' := DFunLike.congr_fun h p
  rwa [AlgHom.comp_apply] at h'

@[simp] theorem polyScale_one (p : Polynomial K) : polyScale 1 p = p := by
  rw [polyScale_eq_comp]
  simp

theorem polyScale_injective {q : K} (hq : q ≠ 0) : Function.Injective (polyScale q) := by
  intro p₁ p₂ h
  have := congrArg (polyScale q⁻¹) h
  rwa [polyScale_polyScale, polyScale_polyScale, inv_mul_cancel₀ hq, polyScale_one,
    polyScale_one] at this

/-! ## The dilation of the rational function field -/

/-- The multiplicative dilation `X ↦ q * X` of the rational function field, obtained by localizing
the polynomial substitution `p ↦ p(qX)`. -/
def ratFuncScale (q : K) (hq : q ≠ 0) : RatFunc K →ₐ[K] RatFunc K :=
  RatFunc.mapAlgHom (polyScale q)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (polyScale_injective hq))

theorem ratFuncScale_div (q : K) (hq : q ≠ 0) (p s : Polynomial K) :
    ratFuncScale q hq (algebraMap (Polynomial K) (RatFunc K) p /
        algebraMap (Polynomial K) (RatFunc K) s) =
      algebraMap (Polynomial K) (RatFunc K) (polyScale q p) /
        algebraMap (Polynomial K) (RatFunc K) (polyScale q s) := by
  show (RatFunc.mapAlgHom _ _ : RatFunc K →ₐ[K] RatFunc K) _ = _
  rw [show ((RatFunc.mapAlgHom (polyScale q)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (polyScale_injective hq)) :
      RatFunc K →ₐ[K] RatFunc K) :
      RatFunc K → RatFunc K) = RatFunc.map (polyScale q) _ from
    RatFunc.coe_mapAlgHom_eq_coe_map _ _]
  exact RatFunc.map_apply_div _ _ p s

theorem ratFuncScale_scale_inv (q : K) (hq : q ≠ 0) (f : RatFunc K) :
    ratFuncScale q⁻¹ (inv_ne_zero hq) (ratFuncScale q hq f) = f := by
  refine RatFunc.induction_on (P := fun f => ratFuncScale q⁻¹ (inv_ne_zero hq)
    (ratFuncScale q hq f) = f) f ?_
  intro p s _
  rw [ratFuncScale_div, ratFuncScale_div, polyScale_polyScale, polyScale_polyScale,
    inv_mul_cancel₀ hq, polyScale_one, polyScale_one]

/-- **Dilation moves poles by dilation.**  The dilate of `g` is regular at `w` exactly when `g` is
regular at `q w`. -/
theorem regularAt_ratFuncScale (q : K) (hq : q ≠ 0) (g : RatFunc K) (w : K) :
    RegularAt (ratFuncScale q hq g) w ↔ RegularAt g (q * w) := by
  constructor
  · rintro ⟨p, s, hs, hgs⟩
    refine ⟨polyScale q⁻¹ p, polyScale q⁻¹ s, ?_, ?_⟩
    · rw [eval_polyScale, inv_mul_cancel_left₀ hq]
      exact hs
    · have h := congrArg (ratFuncScale q⁻¹ (inv_ne_zero hq)) hgs
      rw [ratFuncScale_scale_inv q hq, ratFuncScale_div] at h
      exact h
  · rintro ⟨p, s, hs, rfl⟩
    exact ⟨polyScale q p, polyScale q s, by rw [eval_polyScale]; exact hs,
      ratFuncScale_div q hq p s⟩

end

/-! ## The orbit obstruction along an arbitrary injective orbit -/

theorem finite_orbit_poles_gen (g : RatFunc K) (orb : ℤ → K)
    (hinj : Function.Injective orb) : {n : ℤ | ¬ RegularAt g (orb n)}.Finite := by
  have hroot : {w : K | g.denom.IsRoot w}.Finite :=
    Polynomial.finite_setOf_isRoot (RatFunc.denom_ne_zero g)
  refine Set.Finite.subset (Set.Finite.preimage hinj.injOn hroot) ?_
  intro n hn
  rw [Set.mem_setOf_eq] at hn
  exact (poleOrder_ne_zero_iff g _).mp
    (fun hz => hn ((regularAt_iff_poleOrder_eq_zero g (orb n)).mpr hz))

/-- **No single-pole orbit for a telescoped difference, along an arbitrary injective orbit.**
The only inputs are injectivity of the orbit and the statement that `gs` has, at each orbit point,
the regularity of `g` one step along. -/
theorem regularAt_orbit_of_telescoped_pole_subsingleton_gen (g gs : RatFunc K)
    (orb : ℤ → K) (hinj : Function.Injective orb)
    (hshift : ∀ n : ℤ, RegularAt gs (orb n) ↔ RegularAt g (orb (n + 1)))
    (D : Set ℤ) (hD : ∀ n : ℤ, ¬ RegularAt (gs - g) (orb n) → n ∈ D)
    (hsub : D.Subsingleton) : ∀ n : ℤ, RegularAt g (orb n) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨n₀, hn₀⟩ := hcon
  set S : Finset ℤ := (finite_orbit_poles_gen g orb hinj).toFinset with hS
  have hmemS : ∀ n : ℤ, n ∈ S ↔ ¬ RegularAt g (orb n) := by
    intro n
    rw [hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hSne : S.Nonempty := ⟨n₀, (hmemS n₀).mpr hn₀⟩
  have hpole : ∀ n : ℤ, ¬ ((n ∈ S) ↔ (n + 1 ∈ S)) → ¬ RegularAt (gs - g) (orb n) := by
    intro n hjump
    by_cases hn : n ∈ S
    · have hnot : n + 1 ∉ S := fun hcontra => hjump ⟨fun _ => hcontra, fun _ => hn⟩
      have hgs : RegularAt gs (orb n) :=
        (hshift n).mpr (not_not.mp fun h => hnot ((hmemS (n + 1)).mpr h))
      exact not_regularAt_sub_of_not_regularAt ((hmemS n).mp hn) hgs
    · have hyes : n + 1 ∈ S := by
        by_contra hcontra
        exact hjump ⟨fun h => absurd h hn, fun h => absurd h hcontra⟩
      have hgreg : RegularAt g (orb n) := not_not.mp fun h => hn ((hmemS n).mpr h)
      have hgspole : ¬ RegularAt gs (orb n) := fun h => (hmemS (n + 1)).mp hyes ((hshift n).mp h)
      exact not_regularAt_sub_of_not_regularAt' hgspole hgreg
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_jumps S hSne
  exact hab (hsub (hD a (hpole a ha)) (hD b (hpole b hb)))

/-- **A rational function with exactly one pole on an injective orbit is not a telescoped
difference along that orbit.** -/
theorem not_telescoped_of_unique_orbit_pole_gen (r : RatFunc K) (orb : ℤ → K)
    (hinj : Function.Injective orb) (hpole : ¬ RegularAt r (orb 0))
    (hunique : ∀ n : ℤ, n ≠ 0 → RegularAt r (orb n)) :
    ¬ ∃ g gs : RatFunc K,
      (∀ n : ℤ, RegularAt gs (orb n) ↔ RegularAt g (orb (n + 1))) ∧ r = gs - g := by
  rintro ⟨g, gs, hshift, rfl⟩
  have hD : ∀ n : ℤ, ¬ RegularAt (gs - g) (orb n) → n ∈ ({0} : Set ℤ) := by
    intro n hn
    by_contra hne
    exact hn (hunique n (by simpa using hne))
  have hreg := regularAt_orbit_of_telescoped_pole_subsingleton_gen g gs orb hinj hshift
    ({0} : Set ℤ) hD Set.subsingleton_singleton
  exact hpole (((hshift 0).mpr (by simpa using hreg 1)).sub (hreg 0))

/-! ## The multiplicative orbit -/

noncomputable section

/-- The multiplicative orbit `n ↦ p₀ * q ^ n`. -/
def multOrbit (q p₀ : K) : ℤ → K := fun n => p₀ * q ^ n

@[simp] theorem multOrbit_zero (q p₀ : K) : multOrbit q p₀ 0 = p₀ := by
  simp [multOrbit]

theorem multOrbit_succ (q p₀ : K) (hq : q ≠ 0) (n : ℤ) :
    multOrbit q p₀ (n + 1) = q * multOrbit q p₀ n := by
  simp [multOrbit, zpow_add₀ hq]
  ring

theorem multOrbit_injective {q p₀ : K} (hq : q ≠ 0) (hp₀ : p₀ ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) : Function.Injective (multOrbit q p₀) := by
  intro m n hmn
  by_contra hne
  have hz : q ^ m = q ^ n := mul_left_cancel₀ hp₀ hmn
  have : q ^ (m - n) = 1 := by
    rw [zpow_sub₀ hq, hz, div_self (zpow_ne_zero _ hq)]
  exact hqtor (m - n) (sub_ne_zero.mpr hne) this

/-- **The multiplicative-orbit residue obstruction.**  If `q` is not a root of unity and a rational
function `r` has a pole at `p₀ ≠ 0` and no other pole on the multiplicative orbit `p₀ q^ℤ`, then the
`q`-difference equation `r = h(qX) - h(X)` has no rational solution `h`.

This is the exact obstruction used to contradict the descended paired telescoping relation in the
double-sine hypertranscendence argument. -/
theorem not_dilationTelescoped_of_unique_multOrbit_pole
    (q p₀ : K) (hq : q ≠ 0) (hp₀ : p₀ ≠ 0) (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1)
    (r : RatFunc K) (hpole : ¬ RegularAt r p₀)
    (hunique : ∀ n : ℤ, n ≠ 0 → RegularAt r (p₀ * q ^ n)) :
    ¬ ∃ h : RatFunc K, r = ratFuncScale q hq h - h := by
  rintro ⟨h, hr⟩
  refine not_telescoped_of_unique_orbit_pole_gen r (multOrbit q p₀)
    (multOrbit_injective hq hp₀ hqtor) (by simpa using hpole) (fun n hn => hunique n hn)
    ⟨h, ratFuncScale q hq h, ?_, hr⟩
  intro n
  rw [regularAt_ratFuncScale, ← multOrbit_succ q p₀ hq n]

/-! ## Irrational rotations are not roots of unity -/

/-- **An irrational rotation number gives a non-torsion multiplier.**  This is the exact source of
the non-torsion hypothesis in the double-sine argument: `q = exp(2πi ω₁/ω₂)` with `ω₁/ω₂`
irrational. -/
theorem exp_two_pi_I_zpow_ne_one {θ : ℝ} (hθ : Irrational θ) {n : ℤ} (hn : n ≠ 0) :
    Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ)) ^ n ≠ 1 := by
  intro hcon
  rw [← Complex.exp_int_mul] at hcon
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hcon
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  field_simp at hk
  have hR : (n : ℝ) * θ = (k : ℝ) := by exact_mod_cast hk
  have hirr := Irrational.intCast_mul hθ hn
  rw [hR] at hirr
  exact (Int.not_irrational k) hirr

end

end GaloisForLFunctions
