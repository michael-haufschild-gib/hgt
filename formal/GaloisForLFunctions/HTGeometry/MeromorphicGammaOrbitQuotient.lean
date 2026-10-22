import GaloisForLFunctions.HTGeometry.MeromorphicGammaNatScale

/-!
# Differential algebraicity of shifted Gamma products via integer-translation orbits

For finitely many shifts `b i ∈ ℂ` and integer exponents `m i`, consider
`∏_i Γ(z + b i)^{m i}` in the field of meromorphic functions on `ℂ`. Indices are grouped into
integer-translation orbits (`b i - b j ∈ ℤ`), and the orbit charge of an orbit is the sum of the
exponents `m i` over it. Since `Γ(z + b + q) = r(z) Γ(z + b)` with a nonzero rational function `r`
for every `q ∈ ℤ`, the product equals a nonzero rational gauge times the reduced product
`∏_c Γ(z + b_c)^{charge c}` over orbit representatives. The main theorem: the product is
differentially algebraic over `ℂ(z)` if and only if every orbit charge vanishes.

## Main results

- `exists_ratfunc_gammaShiftMero_add_int`: `Γ(z + b + q) = r(z) Γ(z + b)` with `r ∈ ℂ(z)`
  nonzero, for `q ∈ ℤ`.
- `gammaFintypeOrbitProductMero_automatic_normalForm`: product = rational gauge × reduced orbit
  product.
- `differentialAlgebraicOver_gammaShiftOrbitReducedProductMero_iff`: the reduced product is
  differentially algebraic over `ℂ(z)` iff all orbit charges are zero.
- `differentialAlgebraicOver_gammaFintypeOrbitProductMero_iff_orbitCharge`: the same criterion for
  the original product `∏_i Γ(z + b i)^{m i}`.

## Hypotheses

All results are unconditional. The hypertranscendence direction uses the separated-orbit Gamma
criterion `hypertranscendentalOver_gammaFintypeOrbitProductMero` from the imported modules.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set Topology Function Complex
open Bottcher
open scoped BigOperators Differential

noncomputable section

local instance gammaOrbitNormalFormDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

/-- Integer translation of the shift changes `Γ(z + b)` by a nonzero rational factor:
`Γ(z + b + q) = r(z) Γ(z + b)` for some nonzero `r ∈ ℂ(z)`. -/
theorem exists_ratfunc_gammaShiftMero_add_int (b : ℂ) (q : ℤ) :
    ∃ r : RatFunc ℂ, r ≠ 0 ∧
      gammaShiftMero (b + (q : ℂ)) =
        ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ r * gammaShiftMero b := by
  cases q with
  | ofNat n =>
      exact ⟨gammaOrbitNatFactor b n, gammaOrbitNatFactor_ne_zero b n,
        gammaShiftMero_add_nat b n⟩
  | negSucc n =>
      let c : ℂ := b - (n + 1 : ℕ)
      let p : RatFunc ℂ := gammaOrbitNatFactor c (n + 1)
      have hp : p ≠ 0 := gammaOrbitNatFactor_ne_zero c (n + 1)
      have hrec := gammaShiftMero_add_nat c (n + 1)
      have harg : c + ((n + 1 : ℕ) : ℂ) = b := by
        dsimp [c]
        ring
      rw [harg] at hrec
      refine ⟨p⁻¹, inv_ne_zero hp, ?_⟩
      have hshift : b + ((Int.negSucc n : ℤ) : ℂ) = c := by
        dsimp [c]
        push_cast
        ring
      rw [hshift, map_inv₀]
      rw [hrec]
      have hmap : ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ p ≠ 0 :=
        (map_ne_zero_iff _ (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ).injective).mpr hp
      field_simp [hmap]
      simp [p]

variable {ι : Type*}

/-- Two indices are related when their shifts differ by an integer. -/
def gammaShiftOrbitRel (b : ι → ℂ) (i j : ι) : Prop :=
  ∃ q : ℤ, b i - b j = (q : ℂ)

theorem gammaShiftOrbitRel_refl (b : ι → ℂ) (i : ι) :
    gammaShiftOrbitRel b i i := ⟨0, by simp⟩

theorem gammaShiftOrbitRel_symm (b : ι → ℂ) {i j : ι} :
    gammaShiftOrbitRel b i j → gammaShiftOrbitRel b j i := by
  rintro ⟨q, hq⟩
  exact ⟨-q, by push_cast; linear_combination -hq⟩

theorem gammaShiftOrbitRel_trans (b : ι → ℂ) {i j k : ι} :
    gammaShiftOrbitRel b i j → gammaShiftOrbitRel b j k → gammaShiftOrbitRel b i k := by
  rintro ⟨q, hq⟩ ⟨r, hr⟩
  exact ⟨q + r, by push_cast; linear_combination hq + hr⟩

/-- The integer-translation equivalence relation on indices. -/
def gammaShiftOrbitSetoid (b : ι → ℂ) : Setoid ι where
  r := gammaShiftOrbitRel b
  iseqv := ⟨gammaShiftOrbitRel_refl b, gammaShiftOrbitRel_symm b,
    gammaShiftOrbitRel_trans b⟩

/-- Integer-translation orbits of indices. -/
abbrev GammaShiftOrbit (b : ι → ℂ) := Quotient (gammaShiftOrbitSetoid b)

section Finite

variable [Fintype ι]

noncomputable instance gammaShiftOrbitDecidableEq (b : ι → ℂ) :
    DecidableEq (GammaShiftOrbit b) := Classical.decEq _

noncomputable instance gammaShiftOrbitFintype (b : ι → ℂ) :
    Fintype (GammaShiftOrbit b) :=
  Fintype.ofSurjective (fun i : ι => (Quotient.mk'' i : GammaShiftOrbit b))
    (fun c => ⟨c.out, Quotient.out_eq c⟩)

/-- The integer `b i - b (rep)` from the chosen orbit representative to index `i`. -/
noncomputable def gammaShiftOrbitTranslation (b : ι → ℂ) (i : ι) : ℤ :=
  Classical.choose (show gammaShiftOrbitRel b i
      (Quotient.mk'' i : GammaShiftOrbit b).out from
    Quotient.exact
      (show (Quotient.mk'' i : GammaShiftOrbit b) =
          Quotient.mk'' (Quotient.mk'' i : GammaShiftOrbit b).out from
        (Quotient.out_eq (Quotient.mk'' i : GammaShiftOrbit b)).symm))

omit [Fintype ι] in theorem gammaShiftOrbitTranslation_spec (b : ι → ℂ) (i : ι) :
    b i - b (Quotient.mk'' i : GammaShiftOrbit b).out =
      (gammaShiftOrbitTranslation b i : ℂ) :=
  Classical.choose_spec (show gammaShiftOrbitRel b i
      (Quotient.mk'' i : GammaShiftOrbit b).out from
    Quotient.exact
      (show (Quotient.mk'' i : GammaShiftOrbit b) =
          Quotient.mk'' (Quotient.mk'' i : GammaShiftOrbit b).out from
        (Quotient.out_eq (Quotient.mk'' i : GammaShiftOrbit b)).symm))

/-- Orbit charge: the sum of the exponents `m i` over the indices in orbit `c`. -/
def gammaShiftOrbitCharge (b : ι → ℂ) (m : ι → ℤ)
    (c : GammaShiftOrbit b) : ℤ :=
  ∑ i, if Quotient.mk'' i = c then m i else 0

/-- Regrouping a product over indices by orbits: `∏_i g([i])^{m i} = ∏_c g(c)^{charge c}` for
nonzero `g`. -/
theorem prod_zpow_eq_prod_quotient_charge
    {M : Type*} [CommGroupWithZero M] (b : ι → ℂ) (g : GammaShiftOrbit b → M)
    (m : ι → ℤ) (hg : ∀ c, g c ≠ 0) :
    ∏ i, g (Quotient.mk'' i) ^ m i =
      ∏ c, g c ^ gammaShiftOrbitCharge b m c := by
  classical
  rw [show (∏ i, g (Quotient.mk'' i) ^ m i) =
      ∏ i, ∏ c : GammaShiftOrbit b,
        if Quotient.mk'' i = c then g c ^ m i else 1 by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.prod_eq_single (Quotient.mk'' i)]
    · simp
    · intro c hc hci
      simp [hci.symm]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro c hc
  rw [gammaShiftOrbitCharge]
  have hcollapse : ∀ s : Finset ι,
      (∏ i ∈ s, if Quotient.mk'' i = c then g c ^ m i else 1) =
        g c ^ (∑ i ∈ s, if Quotient.mk'' i = c then m i else 0) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.sum_insert hi, ih,
          zpow_add₀ (hg c)]
        by_cases hic : Quotient.mk'' i = c <;> simp [hic]
  simpa using hcollapse Finset.univ

/-- A chosen nonzero rational factor with `Γ(z + b i) = r(z) Γ(z + b (rep))`. -/
noncomputable def gammaShiftOrbitGaugeFactorRat (b : ι → ℂ) (i : ι) : RatFunc ℂ :=
  Classical.choose
    (exists_ratfunc_gammaShiftMero_add_int
      (b (Quotient.mk'' i : GammaShiftOrbit b).out)
      (gammaShiftOrbitTranslation b i))

omit [Fintype ι] in theorem gammaShiftOrbitGaugeFactorRat_ne_zero (b : ι → ℂ) (i : ι) :
    gammaShiftOrbitGaugeFactorRat b i ≠ 0 :=
  (Classical.choose_spec
    (exists_ratfunc_gammaShiftMero_add_int
      (b (Quotient.mk'' i : GammaShiftOrbit b).out)
      (gammaShiftOrbitTranslation b i))).1

omit [Fintype ι] in theorem gammaShiftMero_eq_orbitGauge_mul_rep (b : ι → ℂ) (i : ι) :
    gammaShiftMero (b i) =
      ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ (gammaShiftOrbitGaugeFactorRat b i) *
        gammaShiftMero (b (Quotient.mk'' i : GammaShiftOrbit b).out) := by
  have h := (Classical.choose_spec
    (exists_ratfunc_gammaShiftMero_add_int
      (b (Quotient.mk'' i : GammaShiftOrbit b).out)
      (gammaShiftOrbitTranslation b i))).2
  have harg : b (Quotient.mk'' i : GammaShiftOrbit b).out +
      (gammaShiftOrbitTranslation b i : ℂ) = b i := by
    have hs := gammaShiftOrbitTranslation_spec b i
    calc
      b (Quotient.mk'' i : GammaShiftOrbit b).out +
          (gammaShiftOrbitTranslation b i : ℂ) =
        b (Quotient.mk'' i : GammaShiftOrbit b).out +
          (b i - b (Quotient.mk'' i : GammaShiftOrbit b).out) := by rw [hs]
      _ = b i := by ring
  calc
    gammaShiftMero (b i) = gammaShiftMero
        (b (Quotient.mk'' i : GammaShiftOrbit b).out +
          (gammaShiftOrbitTranslation b i : ℂ)) := congrArg gammaShiftMero harg.symm
    _ = _ := by simpa only [gammaShiftOrbitGaugeFactorRat] using h

/-- The total rational gauge `∏_i (gammaShiftOrbitGaugeFactorRat b i)^{m i}`. -/
def gammaShiftOrbitGaugeRat (b : ι → ℂ) (m : ι → ℤ) : RatFunc ℂ :=
  ∏ i, gammaShiftOrbitGaugeFactorRat b i ^ m i

/-- The reduced orbit product `∏_c Γ(z + b_c)^{charge c}` over orbit representatives. -/
def gammaShiftOrbitReducedProductMero (b : ι → ℂ) (m : ι → ℤ) :
    meroField Set.univ :=
  ∏ c : GammaShiftOrbit b,
    gammaShiftMero (b c.out) ^ gammaShiftOrbitCharge b m c

theorem gammaShiftOrbitGaugeRat_ne_zero (b : ι → ℂ) (m : ι → ℤ) :
    gammaShiftOrbitGaugeRat b m ≠ 0 := by
  rw [gammaShiftOrbitGaugeRat, Finset.prod_ne_zero_iff]
  intro i hi
  exact zpow_ne_zero _ (gammaShiftOrbitGaugeFactorRat_ne_zero b i)

/-- Normal form: `∏_i Γ(z + b i)^{m i}` equals the rational gauge times the reduced orbit
product. -/
theorem gammaFintypeOrbitProductMero_automatic_normalForm
    (b : ι → ℂ) (m : ι → ℤ) :
    gammaFintypeOrbitProductMero b m =
      ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ (gammaShiftOrbitGaugeRat b m) *
        gammaShiftOrbitReducedProductMero b m := by
  classical
  rw [gammaFintypeOrbitProductMero, gammaShiftOrbitGaugeRat,
    gammaShiftOrbitReducedProductMero]
  calc
    ∏ i, gammaShiftMero (b i) ^ m i =
        ∏ i, (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
            Set.univ_nonempty Set.infinite_univ (gammaShiftOrbitGaugeFactorRat b i) *
          gammaShiftMero (b (Quotient.mk'' i : GammaShiftOrbit b).out)) ^ m i := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [gammaShiftMero_eq_orbitGauge_mul_rep]
    _ = _ := by
      simp_rw [mul_zpow]
      rw [Finset.prod_mul_distrib, map_prod]
      simp_rw [map_zpow₀]
      congr 1
      exact prod_zpow_eq_prod_quotient_charge b
        (fun c => gammaShiftMero (b c.out)) m
        (fun c => gammaShiftMero_ne_zero (b c.out))

local instance gammaShiftOrbitComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance gammaShiftOrbitComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance gammaShiftOrbitDifferential : Differential (meroField Set.univ) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance gammaShiftOrbitRatFuncAlgebra : Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance gammaShiftOrbitRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance gammaShiftOrbitDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance gammaShiftOrbitCharZero : CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

omit [Fintype ι] in theorem gammaShiftOrbitRep_separated (b : ι → ℂ) :
    ∀ c e : GammaShiftOrbit b, c ≠ e → ∀ q : ℤ,
      b c.out - b e.out ≠ (q : ℂ) := by
  intro c e hce q hq
  apply hce
  rw [← Quotient.out_eq c, ← Quotient.out_eq e]
  exact Quotient.sound ⟨q, hq⟩

/-- The reduced orbit product is differentially algebraic over `ℂ(z)` iff every orbit charge is
zero; a nonzero charge makes it hypertranscendental. -/
theorem differentialAlgebraicOver_gammaShiftOrbitReducedProductMero_iff
    (b : ι → ℂ) (m : ι → ℤ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (gammaShiftOrbitReducedProductMero b m) ↔
      ∀ c, gammaShiftOrbitCharge b m c = 0 := by
  constructor
  · intro hDA c
    by_contra hc
    have hHT : HypertranscendentalOver (RatFunc ℂ)
        (gammaShiftOrbitReducedProductMero b m) := by
      rw [gammaShiftOrbitReducedProductMero]
      exact hypertranscendentalOver_gammaFintypeOrbitProductMero
        (fun e : GammaShiftOrbit b => b e.out)
        (gammaShiftOrbitCharge b m) c hc
        (fun e he => gammaShiftOrbitRep_separated b e c he)
    exact hHT hDA
  · intro hcharge
    rw [gammaShiftOrbitReducedProductMero]
    have hone : (∏ c : GammaShiftOrbit b,
        gammaShiftMero (b c.out) ^ gammaShiftOrbitCharge b m c) = 1 := by
      apply Finset.prod_eq_one
      intro c hc
      simp [hcharge c]
    rw [hone]
    rw [← map_one (algebraMap (RatFunc ℂ) (meroField Set.univ))]
    exact HTGeometry.differentialAlgebraicOver_algebraMap (1 : RatFunc ℂ)

/-- Orbit-charge criterion: `∏_i Γ(z + b i)^{m i}` is differentially algebraic over `ℂ(z)` iff the
exponents sum to zero on every integer-translation orbit of the shifts. -/
theorem differentialAlgebraicOver_gammaFintypeOrbitProductMero_iff_orbitCharge
    (b : ι → ℂ) (m : ι → ℤ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (gammaFintypeOrbitProductMero b m) ↔
      ∀ c, gammaShiftOrbitCharge b m c = 0 := by
  rw [gammaFintypeOrbitProductMero_automatic_normalForm,
    ← differentialAlgebraicOver_gammaShiftOrbitReducedProductMero_iff b m]
  constructor
  · intro hprod
    have hgaugeDA : DifferentialAlgebraicOver (RatFunc ℂ)
        (algebraMap (RatFunc ℂ) (meroField Set.univ) (gammaShiftOrbitGaugeRat b m)) :=
      HTGeometry.differentialAlgebraicOver_algebraMap _
    have hdiv := HTGeometry.differentialAlgebraicOver_div hprod hgaugeDA
    have hgauge : algebraMap (RatFunc ℂ) (meroField Set.univ)
        (gammaShiftOrbitGaugeRat b m) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective).mpr
        (gammaShiftOrbitGaugeRat_ne_zero b m)
    have heq : (algebraMap (RatFunc ℂ) (meroField Set.univ)
          (gammaShiftOrbitGaugeRat b m) * gammaShiftOrbitReducedProductMero b m) /
        algebraMap (RatFunc ℂ) (meroField Set.univ) (gammaShiftOrbitGaugeRat b m) =
          gammaShiftOrbitReducedProductMero b m := by
      field_simp [hgauge]
    change DifferentialAlgebraicOver (RatFunc ℂ)
      ((algebraMap (RatFunc ℂ) (meroField Set.univ)
          (gammaShiftOrbitGaugeRat b m) * gammaShiftOrbitReducedProductMero b m) /
        algebraMap (RatFunc ℂ) (meroField Set.univ) (gammaShiftOrbitGaugeRat b m)) at hdiv
    rwa [heq] at hdiv
  · exact HTGeometry.differentialAlgebraicOver_mul
      (HTGeometry.differentialAlgebraicOver_algebraMap _)

end Finite


end
end GaloisForLFunctions.HTGeometry
