import GaloisForLFunctions.HTGeometry.LaurentShiftFirstOrder
import GaloisForLFunctions.HTGeometry.DifferentialSemilinearAutomorphism
import GaloisForLFunctions.HTGeometry.FiniteCommutingShiftPeeling

/-!
# The one-shift dichotomy and finite commuting-shift peeling in `ℂ((s⁻¹))`

A formal Laurent series at infinity whose translation increment is rational is either rational or
hypertranscendental over `ℂ(s)`.  If it is not hypertranscendental, the differential Ostrowski
criterion produces a constant-coefficient inhomogeneous equation with rational right-hand side;
factoring that operator into first-order factors and solving them one at a time inside `ℂ(s)`
makes the series rational.  Iterating over a word of translations peels an arbitrary finite
product of shift-differences.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential RatFunc

noncomputable section

local instance : Differential (LaurentSeries ℂ) := laurentSDifferential
attribute [local instance] ratFuncIntAlgebra'
local instance : Differential (RatFunc ℂ) := ratFuncSDifferential
attribute [local instance] ratLaurentAlgebra towerCRatLaurent towerCRatLaurentAlg

local instance : DifferentialAlgebra (RatFunc ℂ) (LaurentSeries ℂ) :=
  ⟨fun r => by rw [algebraMap_ratLaurent, algebraMap_ratLaurent, deriv_ratToLaurent]⟩

local instance : CharZero (LaurentSeries ℂ) :=
  charZero_of_injective_algebraMap (R := ℂ) (A := LaurentSeries ℂ)
    (fun a b hab => by
      have hc := congrArg (fun z : LaurentSeries ℂ => z.coeff 0) hab
      simpa [LaurentSeries.algebraMap_apply, HahnSeries.C_apply] using hc)

/-! ### Constant-coefficient differential operators as additive endomorphisms -/

theorem laurentSDeriv_algebraMap_complex (c : ℂ) :
    (algebraMap ℂ (LaurentSeries ℂ) c)′ = 0 := by
  rw [algebraMap_complex_laurent, laurentC, laurentSDeriv_algebraMap, coordDerivPS,
    PowerSeries.derivative_C, mul_zero, map_zero]

/-- Multiplication by a complex constant, as an additive endomorphism of the Laurent field. -/
def laurentConstEnd : ℂ →+* AddMonoid.End (LaurentSeries ℂ) where
  toFun c := AddMonoidHom.mulLeft (algebraMap ℂ (LaurentSeries ℂ) c)
  map_one' := AddMonoidHom.ext fun u => by
    show algebraMap ℂ (LaurentSeries ℂ) 1 * u = u
    rw [map_one, one_mul]
  map_mul' a b := AddMonoidHom.ext fun u => by
    show algebraMap ℂ (LaurentSeries ℂ) (a * b) * u
      = algebraMap ℂ (LaurentSeries ℂ) a * (algebraMap ℂ (LaurentSeries ℂ) b * u)
    rw [map_mul, mul_assoc]
  map_zero' := AddMonoidHom.ext fun u => by
    show algebraMap ℂ (LaurentSeries ℂ) 0 * u = 0
    rw [map_zero, zero_mul]
  map_add' a b := AddMonoidHom.ext fun u => by
    show algebraMap ℂ (LaurentSeries ℂ) (a + b) * u
      = algebraMap ℂ (LaurentSeries ℂ) a * u + algebraMap ℂ (LaurentSeries ℂ) b * u
    rw [map_add, add_mul]

@[simp] theorem laurentConstEnd_apply (c : ℂ) (u : LaurentSeries ℂ) :
    laurentConstEnd c u = algebraMap ℂ (LaurentSeries ℂ) c * u := rfl

/-- The derivation `d/ds`, as an additive endomorphism of the Laurent field. -/
def laurentDerivEnd : AddMonoid.End (LaurentSeries ℂ) :=
  AddMonoidHom.mk' (fun u : LaurentSeries ℂ => u′) laurentSDeriv_add

@[simp] theorem laurentDerivEnd_apply (u : LaurentSeries ℂ) : laurentDerivEnd u = u′ := rfl

theorem commute_laurentConstEnd (c : ℂ) : Commute (laurentConstEnd c) laurentDerivEnd := by
  have hc : (laurentConstEnd c) * laurentDerivEnd = laurentDerivEnd * (laurentConstEnd c) :=
    AddMonoidHom.ext fun u => by
      show algebraMap ℂ (LaurentSeries ℂ) c * (Differential.deriv u)
        = Differential.deriv (algebraMap ℂ (LaurentSeries ℂ) c * u)
      rw [laurentSDeriv_mul, laurentSDeriv_algebraMap_complex, mul_zero, add_zero]
  exact hc

/-- A complex polynomial evaluated at `d/ds`, as an additive endomorphism of the Laurent field. -/
def laurentDiffOp : Polynomial ℂ →+* AddMonoid.End (LaurentSeries ℂ) :=
  Polynomial.eval₂RingHom' laurentConstEnd laurentDerivEnd commute_laurentConstEnd

theorem laurentDiffOp_C (a : ℂ) : laurentDiffOp (Polynomial.C a) = laurentConstEnd a := by
  show Polynomial.eval₂ laurentConstEnd laurentDerivEnd (Polynomial.C a) = _
  rw [Polynomial.eval₂_C]

theorem laurentDiffOp_X : laurentDiffOp Polynomial.X = laurentDerivEnd := by
  show Polynomial.eval₂ laurentConstEnd laurentDerivEnd Polynomial.X = _
  rw [Polynomial.eval₂_X]

theorem laurentDerivEnd_pow : ∀ (n : ℕ) (u : LaurentSeries ℂ),
    (laurentDerivEnd ^ n) u = differentialJet n u := by
  intro n
  induction n with
  | zero => intro u; simp [differentialJet]
  | succ n ih =>
      intro u
      have hstep : ((laurentDerivEnd ^ n) * laurentDerivEnd) u
          = (laurentDerivEnd ^ n) (laurentDerivEnd u) := rfl
      rw [pow_succ, hstep, laurentDerivEnd_apply, ih]
      have h1 : differentialJet 1 u = u′ := by
        rw [differentialJet_succ, differentialJet_zero]
      rw [← h1, ← differentialJet_add]

theorem laurentDiffOp_monomial (a : ℂ) (n : ℕ) (u : LaurentSeries ℂ) :
    laurentDiffOp (Polynomial.C a * Polynomial.X ^ n) u
      = algebraMap ℂ (LaurentSeries ℂ) a * differentialJet n u := by
  rw [map_mul, map_pow, laurentDiffOp_C, laurentDiffOp_X]
  show laurentConstEnd a ((laurentDerivEnd ^ n) u) = _
  rw [laurentDerivEnd_pow, laurentConstEnd_apply]

theorem laurentDiffOp_X_sub_C (lam : ℂ) (u : LaurentSeries ℂ) :
    laurentDiffOp (Polynomial.X - Polynomial.C lam) u = firstOrderLaurentOp lam u := by
  rw [map_sub, laurentDiffOp_X, laurentDiffOp_C]
  show laurentDerivEnd u - laurentConstEnd lam u = _
  rw [laurentDerivEnd_apply, laurentConstEnd_apply, firstOrderLaurentOp]

theorem laurentDiffOp_listProd (l : List ℂ) (u : LaurentSeries ℂ) :
    laurentDiffOp ((l.map fun a => Polynomial.X - Polynomial.C a).prod) u
      = laurentOpWord l u := by
  induction l with
  | nil =>
      rw [List.map_nil, List.prod_nil, map_one, laurentOpWord_nil]
      rfl
  | cons a l ih =>
      rw [List.map_cons, List.prod_cons, map_mul, laurentOpWord_cons]
      show laurentDiffOp (Polynomial.X - Polynomial.C a)
        (laurentDiffOp ((l.map fun a => Polynomial.X - Polynomial.C a).prod) u) = _
      rw [ih, laurentDiffOp_X_sub_C]

/-- **Factoring a constant-coefficient operator into first-order factors.** -/
theorem exists_opWord_of_polynomial (P : Polynomial ℂ) (u : LaurentSeries ℂ) :
    ∃ l : List ℂ, laurentDiffOp P u
      = algebraMap ℂ (LaurentSeries ℂ) P.leadingCoeff * laurentOpWord l u := by
  refine ⟨P.roots.toList, ?_⟩
  conv_lhs => rw [(IsAlgClosed.splits (k := ℂ) P).eq_prod_roots]
  rw [map_mul, laurentDiffOp_C]
  show laurentConstEnd P.leadingCoeff
    (laurentDiffOp ((P.roots.map fun a => Polynomial.X - Polynomial.C a).prod) u) = _
  rw [laurentConstEnd_apply]
  congr 1
  rw [← laurentDiffOp_listProd P.roots.toList u]
  congr 2
  have hcoe : ((P.roots.toList : Multiset ℂ)) = P.roots := Multiset.coe_toList P.roots
  calc (Multiset.map (fun a : ℂ => Polynomial.X - Polynomial.C a) P.roots).prod
      = (Multiset.map (fun a : ℂ => Polynomial.X - Polynomial.C a)
          ((P.roots.toList : Multiset ℂ))).prod := by rw [hcoe]
    _ = (List.map (fun a : ℂ => Polynomial.X - Polynomial.C a) P.roots.toList).prod := by
          rw [Multiset.map_coe, Multiset.prod_coe]

theorem laurentDiffOp_finsetSum {ι : Type*} (s : Finset ι) (F : ι → Polynomial ℂ)
    (u : LaurentSeries ℂ) :
    laurentDiffOp (∑ i ∈ s, F i) u = ∑ i ∈ s, laurentDiffOp (F i) u := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, map_zero]
      rfl
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, map_add, ← ih]
      rfl

/-! ### From the constant-coefficient equation to rationality -/

/-- A Laurent series with rational translation increment that solves a nonzero
constant-coefficient equation with rational right-hand side is rational. -/
theorem exists_ratToLaurent_of_ode {h : ℂ} (hh : h ≠ 0) {f : LaurentSeries ℂ} {r g : RatFunc ℂ}
    (hfr : shiftLaurent h f = f + ratToLaurent r)
    {c : (Unit × ℕ) →₀ ℂ} (hc : c ≠ 0)
    (hode : ∑ p ∈ c.support, algebraMap ℂ (LaurentSeries ℂ) (c p) * differentialJet p.2 f
      = ratToLaurent g) :
    ∃ q : RatFunc ℂ, f = ratToLaurent q := by
  classical
  set P : Polynomial ℂ := ∑ p ∈ c.support, Polynomial.C (c p) * Polynomial.X ^ p.2 with hP
  have hPapply : laurentDiffOp P f = ratToLaurent g := by
    rw [hP, laurentDiffOp_finsetSum, ← hode]
    exact Finset.sum_congr rfl fun p _ => laurentDiffOp_monomial (c p) p.2 f
  obtain ⟨p₀, hp₀⟩ := Finsupp.support_nonempty_iff.mpr hc
  have hPne : P ≠ 0 := by
    intro hP0
    have hcoeff : P.coeff p₀.2 = c p₀ := by
      rw [hP, Polynomial.finsetSum_coeff, Finset.sum_eq_single p₀]
      · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
      · intro p _ hne
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
        intro hcon
        exact hne (Prod.ext (Subsingleton.elim _ _) hcon.symm)
      · intro hcon
        exact absurd hp₀ hcon
    rw [hP0, Polynomial.coeff_zero] at hcoeff
    exact (Finsupp.mem_support_iff.mp hp₀) hcoeff.symm
  have hlead : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hPne
  obtain ⟨l, hl⟩ := exists_opWord_of_polynomial P f
  have hword : laurentOpWord l f
      = ratToLaurent (algebraMap ℂ (RatFunc ℂ) P.leadingCoeff⁻¹ * g) := by
    have hmul : algebraMap ℂ (LaurentSeries ℂ) P.leadingCoeff * laurentOpWord l f
        = ratToLaurent g := by rw [← hl, hPapply]
    have hinvmul : algebraMap ℂ (LaurentSeries ℂ) P.leadingCoeff⁻¹
        * algebraMap ℂ (LaurentSeries ℂ) P.leadingCoeff = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hlead, map_one]
    rw [map_mul, ratToLaurent_algebraMap_complex]
    calc laurentOpWord l f
        = (algebraMap ℂ (LaurentSeries ℂ) P.leadingCoeff⁻¹
            * algebraMap ℂ (LaurentSeries ℂ) P.leadingCoeff) * laurentOpWord l f := by
          rw [hinvmul, one_mul]
      _ = algebraMap ℂ (LaurentSeries ℂ) P.leadingCoeff⁻¹
            * (algebraMap ℂ (LaurentSeries ℂ) P.leadingCoeff * laurentOpWord l f) := by ring
      _ = _ := by rw [hmul]
  exact exists_ratToLaurent_of_opWord hh l f r _ hfr hword

/-! ### The one-shift dichotomy -/

/-- **The Adamczewski–Dreyfus–Hardouin one-shift dichotomy in the formal Laurent field.**
A formal Laurent series at infinity whose translation increment is rational is either rational or
hypertranscendental over `ℂ(s)`. -/
theorem rational_or_hypertranscendental_of_shift {h : ℂ} (hh : h ≠ 0) {f : LaurentSeries ℂ}
    {r : RatFunc ℂ} (hfr : shiftLaurent h f = f + ratToLaurent r) :
    (∃ q : RatFunc ℂ, f = ratToLaurent q) ∨ HypertranscendentalOver (RatFunc ℂ) f := by
  classical
  by_cases hnot : ∀ c : (Unit × ℕ) →₀ ℂ, c ≠ 0 → ∀ k : RatFunc ℂ,
      ratShiftEquivBy h k - k ≠ Finsupp.linearCombination (RatFunc ℂ)
        (fun p : Unit × ℕ => differentialJet p.2 r)
        (Finsupp.mapRange (algebraMap ℂ (RatFunc ℂ)) (map_zero _) c)
  · exact Or.inr (hypertranscendental_of_no_telescoper hh hfr hnot)
  · push Not at hnot
    obtain ⟨c, hc, k, hk⟩ := hnot
    rw [linearCombination_mapRange_eq_sum
      (RingHom.injective (algebraMap ℂ (RatFunc ℂ)))] at hk
    obtain ⟨g, hg⟩ := exists_ode_of_telescoper hh hfr (c := c) (k := k) hk
    exact Or.inl (exists_ratToLaurent_of_ode hh hfr hc hg)

/-! ### Hypertranscendence descends through a shift difference -/

/-- The translation of the Laurent field, as a differential automorphism normalizing `ℂ(s)`. -/
def shiftSemilinear (h : ℂ) : DifferentialSemilinearEquiv (RatFunc ℂ) (LaurentSeries ℂ) where
  baseEquiv := ratShiftEquivBy h
  ambientEquiv := shiftLaurent h
  map_algebraMap' c := by
    rw [algebraMap_ratLaurent, algebraMap_ratLaurent]
    exact shiftLaurent_ratToLaurent h c
  map_base_deriv' c := by
    show ratShiftBy h (Differential.deriv c) = Differential.deriv (ratShiftBy h c)
    rw [ratFuncSDeriv_apply, ratFuncSDeriv_apply, ratShiftBy_eq_ratFuncShift,
      ratShiftBy_eq_ratFuncShift, ratFuncShift_ratFuncDerivative]
  map_ambient_deriv' x := shiftLaurent_deriv h x

/-- A hypertranscendental shift difference forces its source to be hypertranscendental. -/
theorem hypertranscendental_of_shiftDifference {h : ℂ} {u : LaurentSeries ℂ}
    (hdef : HypertranscendentalOver (RatFunc ℂ) (shiftLaurent h u - u)) :
    HypertranscendentalOver (RatFunc ℂ) u :=
  DifferentialSemilinearEquiv.hypertranscendentalOver_of_sub_self (shiftSemilinear h) hdef

/-! ### Finite commuting-shift peeling -/

/-- The shift difference `Δ_h u = u(s + h) - u(s)` on the Laurent field. -/
def laurentShiftDiff (h : ℂ) (u : LaurentSeries ℂ) : LaurentSeries ℂ :=
  shiftLaurent h u - u

/-- **Finite commuting-shift peeling law.**  If a word of nonzero constant-shift differences
sends a formal Laurent series at infinity to a rational function, the series is rational or
hypertranscendental over `ℂ(s)`.  No commensurability among the shifts is assumed. -/
theorem rational_or_hypertranscendental_of_shiftWord {n : ℕ} (hs : Fin n → ℂ)
    (hsne : ∀ i, hs i ≠ 0) (w : List (Fin n)) (f : LaurentSeries ℂ)
    (hw : ∃ q : RatFunc ℂ,
      _root_.HTGeometry.shiftWord (fun i => laurentShiftDiff (hs i)) w f = ratToLaurent q) :
    (∃ q : RatFunc ℂ, f = ratToLaurent q) ∨ HypertranscendentalOver (RatFunc ℂ) f := by
  refine _root_.HTGeometry.shiftWord_dichotomy
    (R := fun u => ∃ q : RatFunc ℂ, u = ratToLaurent q)
    (H := fun u => HypertranscendentalOver (RatFunc ℂ) u) ?_ ?_ w f hw
  · rintro i g ⟨q, hq⟩
    refine rational_or_hypertranscendental_of_shift (hsne i) (r := q) ?_
    rw [← hq, laurentShiftDiff]
    ring
  · intro i g hg
    exact hypertranscendental_of_shiftDifference (h := hs i) hg

/-- Hypertranscendence descends through a whole word of shift differences. -/
theorem hypertranscendental_of_foldr : ∀ (L : List ℂ) (f : LaurentSeries ℂ),
    HypertranscendentalOver (RatFunc ℂ) (L.foldr laurentShiftDiff f) →
    HypertranscendentalOver (RatFunc ℂ) f := by
  intro L
  induction L with
  | nil => intro f hf; simpa using hf
  | cons b M ih =>
      intro f hf
      rw [List.foldr_cons] at hf
      exact ih f (hypertranscendental_of_shiftDifference (h := b) hf)

/-- The list form of the peeling law: an arbitrary finite family of nonzero shifts. -/
theorem rational_or_hypertranscendental_of_shiftList :
    ∀ (L : List ℂ), (∀ h ∈ L, h ≠ 0) → ∀ f : LaurentSeries ℂ,
      (∃ q : RatFunc ℂ, L.foldr laurentShiftDiff f = ratToLaurent q) →
      (∃ q : RatFunc ℂ, f = ratToLaurent q) ∨ HypertranscendentalOver (RatFunc ℂ) f := by
  intro L
  induction L with
  | nil => intro _ f hf; exact Or.inl (by simpa using hf)
  | cons a L ih =>
      intro hL f hf
      obtain ⟨q, hq⟩ := hf
      rw [List.foldr_cons] at hq
      have ha : a ≠ 0 := hL a (List.mem_cons_self ..)
      have hrest : ∀ h ∈ L, h ≠ 0 := fun h hh => hL h (List.mem_cons_of_mem a hh)
      have hstep : shiftLaurent a (L.foldr laurentShiftDiff f)
          = L.foldr laurentShiftDiff f + ratToLaurent q := by
        rw [← hq, laurentShiftDiff]
        ring
      rcases rational_or_hypertranscendental_of_shift ha hstep with hr | hht
      · exact ih hrest f hr
      · exact Or.inr (hypertranscendental_of_foldr L f hht)

end

end GaloisForLFunctions.HTGeometry
