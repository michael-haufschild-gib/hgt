/-
# Relative transcendence bridge: abstract relation → concrete function relation (value-function half)

The analysis half of wiring `TranscendentalOverAdjoin` (the hRigid / E–vS input). An abstract polynomial
`P` over `analyticSubring U` (the coefficients are the cleared `K[φ_{c₂}]`-coefficients of a relation)
whose evaluation at `phiAnalytic c₁` is `0` yields the **concrete function relation**
`∑ᵢ aᵢ(z)·φ_{c₁}(z)ⁱ = 0` on `U`, where `aᵢ` are the coefficient value-functions. Combined with
`RelativeNaturalBoundary.false_of_basin_branch_dendrite_analytic` (the analytic-coefficient
natural-boundary obstruction), this is the analysis spine of `hrig`.
-/
import GaloisForLFunctions.Bottcher.Q62Field
import GaloisForLFunctions.Bottcher.Rigidity
import GaloisForLFunctions.Bottcher.TranscendenceReduction
import GaloisForLFunctions.Bottcher.MeromorphicField
open Polynomial Filter Topology Set
namespace Bottcher
variable {U : Set ℂ}

theorem eval_phiAnalytic_val (c : ℂ) (hU : U ⊆ escapeOpen c) (P : Polynomial (analyticSubring U)) :
    ((P.eval (phiAnalytic c hU)).val : Germ (𝓟 U) ℂ)
      = P.eval₂ (analyticSubring U).subtype ((bottcherCoord c : ℂ → ℂ) : Germ (𝓟 U) ℂ) := by
  rw [show (P.eval (phiAnalytic c hU)).val
        = (analyticSubring U).subtype (P.eval (phiAnalytic c hU)) from rfl]
  rw [show P.eval (phiAnalytic c hU) = P.eval₂ (RingHom.id (analyticSubring U)) (phiAnalytic c hU)
        from rfl]
  rw [Polynomial.hom_eval₂, RingHom.comp_id]
  rfl

theorem function_eqOn_of_eval_phiAnalytic_zero (c : ℂ) (hU : U ⊆ escapeOpen c)
    (P : Polynomial (analyticSubring U))
    (a : ℕ → ℂ → ℂ)
    (ha : ∀ i ∈ P.support, ((P.coeff i).val : Germ (𝓟 U) ℂ) = ((a i : ℂ → ℂ) : Germ (𝓟 U) ℂ))
    (hP : P.eval (phiAnalytic c hU) = 0) :
    EqOn (fun z => ∑ i ∈ P.support, a i z * (bottcherCoord c z) ^ i) 0 U := by
  have hval0 : ((P.eval (phiAnalytic c hU)).val : Germ (𝓟 U) ℂ) = 0 := by rw [hP]; rfl
  rw [eval_phiAnalytic_val] at hval0
  have hsum : P.eval₂ (analyticSubring U).subtype ((bottcherCoord c : ℂ → ℂ) : Germ (𝓟 U) ℂ)
      = ((fun z => ∑ i ∈ P.support, a i z * (bottcherCoord c z) ^ i : ℂ → ℂ) : Germ (𝓟 U) ℂ) := by
    rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    rw [show (((fun z => ∑ i ∈ P.support, a i z * (bottcherCoord c z) ^ i) : ℂ → ℂ) : Germ (𝓟 U) ℂ)
          = Germ.coeRingHom (𝓟 U) (fun z => ∑ i ∈ P.support, a i z * (bottcherCoord c z) ^ i) from rfl]
    rw [show (fun z => ∑ i ∈ P.support, a i z * (bottcherCoord c z) ^ i)
          = ∑ i ∈ P.support, (fun z => a i z * (bottcherCoord c z) ^ i) from by
        funext z; rw [Finset.sum_apply]]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (analyticSubring U).subtype (P.coeff i) = (P.coeff i).val from rfl, ha i hi]
    rw [show ((a i : ℂ → ℂ) : Germ (𝓟 U) ℂ) = Germ.coeRingHom (𝓟 U) (a i) from rfl,
        show ((bottcherCoord c : ℂ → ℂ) : Germ (𝓟 U) ℂ) = Germ.coeRingHom (𝓟 U) (bottcherCoord c) from rfl,
        show (fun z => a i z * (bottcherCoord c z) ^ i) = (a i) * ((bottcherCoord c) ^ i) from rfl,
        map_mul, map_pow]
  rw [hsum] at hval0
  rw [← Germ.coe_zero, Germ.coe_eq] at hval0
  exact fun z hz => eventually_principal.mp hval0 z hz

/-- **`TranscendentalOverAdjoin ⟸ NoRelation` (pure algebra).** A relation of `F` over the subalgebra
`K[G]` unpacks (via `adjoin = range aeval`) into a nonzero bivariate relation of `(F,G)` over `K`,
contradicting `NoRelation`. So the hRigid input `hrig` reduces to the bivariate `NoRelation`. -/
theorem transcendentalOverAdjoin_of_noRelation {K M : Type*} [Field K] [Field M] [Algebra K M]
    (F G : M) (h : NoRelation K F G) : TranscendentalOverAdjoin (K := K) F G := by
  intro R hR0 hRcoeff hRF
  have hmem : ∀ i, R.coeff i ∈ AlgHom.range (Polynomial.aeval G : Polynomial K →ₐ[K] M) :=
    fun i => by rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact hRcoeff i
  choose s hs using hmem
  set P : Polynomial (Polynomial K) := ∑ i ∈ R.support, Polynomial.monomial i (s i) with hPdef
  have hPmap : (P.map (Polynomial.aeval G : Polynomial K →ₐ[K] M).toRingHom).eval F = 0 := by
    rw [hPdef, Polynomial.map_sum]
    simp only [Polynomial.map_monomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    rw [← hRF, Polynomial.eval_eq_sum, Polynomial.sum_def]
    apply Finset.sum_congr rfl
    intro i _
    rw [hs i]
  have hPeq0 : P = 0 := h P hPmap
  have hex : ∃ i, R.coeff i ≠ 0 := by
    by_contra hc; push Not at hc
    exact hR0 (Polynomial.ext fun i => by rw [hc i, Polynomial.coeff_zero])
  obtain ⟨i, hi⟩ := hex
  have hisupp : i ∈ R.support := Polynomial.mem_support_iff.mpr hi
  have hsi : s i ≠ 0 := by
    intro h0; apply hi; rw [← hs i, h0, map_zero]
  apply hsi
  have hcoef : P.coeff i = s i := by
    rw [hPdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' R.support i s, if_pos hisupp]
  rw [← hcoef, hPeq0, Polynomial.coeff_zero]

/-- **Denominator clearing.** A polynomial over `RatFunc ℂ` has a common denominator `D ∈ ℂ[z]∖0`
clearing every coefficient to a `ℂ[z]`-image: `algebraMap D · q.coeff i = algebraMap pᵢ`. The bridge
step that turns a `RatFunc ℂ`-coefficient relation into one whose coefficients lie in `analyticSubring`
(analytic on `U`), as `function_eqOn_of_eval_phiAnalytic_zero` requires. -/
theorem exists_clear_denominators (q : Polynomial (RatFunc ℂ)) :
    ∃ (D : Polynomial ℂ), D ≠ 0 ∧
      ∀ i, ∃ p : Polynomial ℂ, (algebraMap (Polynomial ℂ) (RatFunc ℂ) D) * q.coeff i
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) p := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples
    (M := nonZeroDivisors (Polynomial ℂ)) (S := RatFunc ℂ) q.support (fun i => q.coeff i)
  refine ⟨(b : Polynomial ℂ), nonZeroDivisors.coe_ne_zero b, fun i => ?_⟩
  by_cases hi : i ∈ q.support
  · obtain ⟨p, hp⟩ := hb i hi
    exact ⟨p, by rw [Algebra.smul_def] at hp; exact hp.symm⟩
  · have hc : q.coeff i = 0 := by
      by_contra h; exact hi (Polynomial.mem_support_iff.mpr h)
    exact ⟨0, by rw [hc, mul_zero, map_zero]⟩

/-- **φ_{c₂}-evaluation bridge.** Evaluating a `ℂ[z]`-coefficient polynomial (mapped into `RatFunc ℂ`)
at `phiMero c₂` equals the `algebraMap` of the `analyticSubring` element `eval₂ polyToAnalytic
(phiAnalytic c₂) q'` — whose value-function (via `eval₂_polyToAnalytic_val`) is `z ↦ ∑ⱼ (q'.coeff j)(z)·φ_{c₂}(z)ʲ`. This is the analytic realization of a `K[φ_{c₂}]`-coefficient. -/
theorem aeval_phiMero_eq (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUinf : U.Infinite) (c₂ : ℂ) (hU₂ : U ⊆ escapeOpen c₂) (q' : Polynomial (Polynomial ℂ)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Polynomial.aeval (phiMero c₂ hU₂) (q'.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)))
      = algebraMap (analyticSubring U) (meroField U)
          (q'.eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂)) := by
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have halg : (algebraMap (RatFunc ℂ) (meroField U)) = ratfuncToMero U hUo hUc hUne hUinf := rfl
  rw [Polynomial.aeval_def, halg, Polynomial.eval₂_map]
  have hcomp : (ratfuncToMero U hUo hUc hUne hUinf).comp
      (algebraMap (Polynomial ℂ) (RatFunc ℂ)) = polyToMero U := by
    refine RingHom.ext fun p => ?_
    exact ratfuncToMero_algebraMap_polynomial U hUo hUc hUne hUinf p
  rw [hcomp]
  rw [show polyToMero U = (algebraMap (analyticSubring U) (meroField U)).comp (polyToAnalytic U) from rfl]
  rw [show phiMero c₂ hU₂ = algebraMap (analyticSubring U) (meroField U) (phiAnalytic c₂ hU₂) from rfl]
  exact (Polynomial.hom_eval₂ q' (polyToAnalytic U) (algebraMap (analyticSubring U) (meroField U))
    (phiAnalytic c₂ hU₂)).symm

/-- **Denominator clearing, polynomial form.** A polynomial over `RatFunc ℂ` becomes, after scaling by
a common denominator `D`, the image of a `ℂ[z]`-coefficient polynomial `q'`. -/
theorem exists_clear_denominators_poly (q : Polynomial (RatFunc ℂ)) :
    ∃ (D : Polynomial ℂ) (q' : Polynomial (Polynomial ℂ)), D ≠ 0 ∧
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) D) • q = q'.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) := by
  obtain ⟨D, hD, hclear⟩ := exists_clear_denominators q
  choose p hp using hclear
  refine ⟨D, ∑ i ∈ q.support, Polynomial.monomial i (p i), hD, ?_⟩
  ext j
  rw [Polynomial.coeff_smul, Polynomial.coeff_map, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' q.support j p]
  by_cases hj : j ∈ q.support
  · rw [if_pos hj, smul_eq_mul, hp j]
  · rw [if_neg hj]
    have hqj : q.coeff j = 0 := by
      by_contra h; exact hj (Polynomial.mem_support_iff.mpr h)
    rw [hqj, smul_zero, map_zero]

/-- **Bivariate denominator clearing.** A polynomial over `RatFunc ℂ`-coefficients (doubly nested) is
cleared by a single common denominator `D ∈ ℂ[z]∖0`: every coefficient `P_abs.coeff i`, scaled by `D`,
is the image of a `ℂ[z]`-coefficient polynomial `Q i`. Common-`D` is the product of the per-coefficient
denominators. -/
theorem exists_clear_bivariate (P_abs : Polynomial (Polynomial (RatFunc ℂ))) :
    ∃ (D : Polynomial ℂ) (Q : ℕ → Polynomial (Polynomial ℂ)), D ≠ 0 ∧ ∀ i,
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) D) • (P_abs.coeff i)
        = (Q i).map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) := by
  classical
  choose Dfun q'fun hDfun hclear using fun i => exists_clear_denominators_poly (P_abs.coeff i)
  set D : Polynomial ℂ := ∏ i ∈ P_abs.support, Dfun i with hDdef
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hDfun i)
  refine ⟨D, fun i => Polynomial.C (∏ k ∈ P_abs.support.erase i, Dfun k) * q'fun i, hD, fun i => ?_⟩
  by_cases hi : i ∈ P_abs.support
  · have hDsplit : D = (∏ k ∈ P_abs.support.erase i, Dfun k) * Dfun i := by
      rw [hDdef, mul_comm, Finset.mul_prod_erase _ _ hi]
    rw [hDsplit, map_mul, mul_smul, hclear i, Polynomial.smul_eq_C_mul,
      Polynomial.map_mul, Polynomial.map_C]
  · have hP0 : P_abs.coeff i = 0 := by
      by_contra h; exact hi (Polynomial.mem_support_iff.mpr h)
    have hqmap0 : (q'fun i).map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) = 0 := by
      rw [← hclear i, hP0, smul_zero]
    rw [hP0, smul_zero, Polynomial.map_mul, hqmap0, mul_zero]

/-- **Scaling step of the assembly.** Scaling `aeval(phiMero c₂)(P_abs.coeff i)` by `polyToMero D`
(the common denominator) lands in `algebraMap (analyticSubring)` — the cleared coefficient is analytic. -/
theorem polyToMero_mul_aeval_phiMero (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUinf : U.Infinite) (c₂ : ℂ) (hU₂ : U ⊆ escapeOpen c₂)
    (D : Polynomial ℂ) (P_abs : Polynomial (Polynomial (RatFunc ℂ)))
    (Q : ℕ → Polynomial (Polynomial ℂ))
    (hQ : ∀ i, (algebraMap (Polynomial ℂ) (RatFunc ℂ) D) • (P_abs.coeff i)
        = (Q i).map (algebraMap (Polynomial ℂ) (RatFunc ℂ))) (i : ℕ) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    polyToMero U D * (Polynomial.aeval (phiMero c₂ hU₂) (P_abs.coeff i))
      = algebraMap (analyticSubring U) (meroField U)
          ((Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂)) := by
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hscalar : polyToMero U D = algebraMap (RatFunc ℂ) (meroField U)
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) D) := by
    rw [show algebraMap (RatFunc ℂ) (meroField U) = ratfuncToMero U hUo hUc hUne hUinf from rfl,
      ratfuncToMero_algebraMap_polynomial]
  rw [hscalar, ← Algebra.smul_def, ← map_smul, hQ i, aeval_phiMero_eq hUo hUc hUne hUinf c₂ hU₂]

/-- **Step 5 — the cleared-relation identity.** With `P` the analytic-coefficient polynomial assembled
from the cleared bivariate coefficients `Q i`, the value `algebraMap (P.eval φ_{c₁})` equals the common
denominator `polyToMero D` times the abstract bivariate relation evaluated at the carriers. This turns
"the abstract relation is `0`" into "the concrete analytic polynomial vanishes at `φ_{c₁}`". -/
theorem algebraMap_eval_eq_polyToMero_mul_relation
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (D : Polynomial ℂ) (P_abs : Polynomial (Polynomial (RatFunc ℂ)))
    (Q : ℕ → Polynomial (Polynomial ℂ))
    (hQ : ∀ i, (algebraMap (Polynomial ℂ) (RatFunc ℂ) D) • (P_abs.coeff i)
        = (Q i).map (algebraMap (Polynomial ℂ) (RatFunc ℂ))) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    algebraMap (analyticSubring U) (meroField U)
        ((∑ i ∈ P_abs.support,
            Polynomial.monomial i ((Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂))).eval
          (phiAnalytic c₁ hU₁))
      = polyToMero U D *
          (P_abs.map (Polynomial.aeval (phiMero c₂ hU₂) :
            Polynomial (RatFunc ℂ) →ₐ[RatFunc ℂ] meroField U).toRingHom).eval (phiMero c₁ hU₁) := by
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial, map_sum, map_mul, map_pow]
  rw [show phiMero c₁ hU₁ = algebraMap (analyticSubring U) (meroField U) (phiAnalytic c₁ hU₁) from rfl]
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (Polynomial.aeval (phiMero c₂ hU₂) :
        Polynomial (RatFunc ℂ) →ₐ[RatFunc ℂ] meroField U).toRingHom (P_abs.coeff i)
        = Polynomial.aeval (phiMero c₂ hU₂) (P_abs.coeff i) from rfl]
  rw [← polyToMero_mul_aeval_phiMero hUo hUc hUne hUinf c₂ hU₂ D P_abs Q hQ i]
  ring

/-- **`NoRelation` from the function-level no-relation (the hRigid bivariate core).** If `φ_{c₂}` is
transcendental over `ℂ(z)` (`hG`) and no nonzero cleared bivariate relation
`∑ᵢ Qᵢ(z, φ_{c₂}(z))·φ_{c₁}(z)ⁱ` vanishes on `U` (`hno` — the natural-boundary input at a dendrite point
of `J_{c₁}`), then the pair `(φ_{c₁}, φ_{c₂})` carries no bivariate algebraic relation over `ℂ(z)`. This
is the concrete `NoRelation ℂ(z) φ_{c₁} φ_{c₂}` consumed by `q62_independence_connected_of_inputs`,
reduced to the two analysis inputs (`hG` = `φ_{c₂}` transcendence; `hno` = the E–vS dendrite
obstruction). Combined with `transcendentalOverAdjoin_of_noRelation` it produces the `hrig` input. -/
theorem noRelation_phiMero_of_no_function_relation
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hno : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        ¬ Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  intro P_abs hrel
  by_contra hP0
  obtain ⟨D, Q, hD, hQ⟩ := exists_clear_bivariate P_abs
  -- the analytic-coefficient polynomial assembled from the cleared coefficients
  set P : Polynomial (analyticSubring U) :=
    ∑ i ∈ P_abs.support,
      Polynomial.monomial i ((Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂)) with hPdef
  -- coefficient formula for `P`
  have hPcoeff : ∀ i, P.coeff i =
      (if i ∈ P_abs.support then (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) else 0) := by
    intro i
    rw [hPdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' P_abs.support i
      (fun j => (Q j).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂))]
  -- step 5 collapses to: P.eval (phiAnalytic c₁) = 0
  have hstep5 := algebraMap_eval_eq_polyToMero_mul_relation
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ D P_abs Q hQ
  rw [← hPdef] at hstep5
  rw [hrel, mul_zero] at hstep5
  rw [meroField_algebraMap_eq_zero_iff U hUo hUc hUne] at hstep5
  -- `polyToMero D ≠ 0` (no root-counting: `polyToMero D = ratfuncToMero (algebraMap D)`, both injective)
  have hDr : algebraMap (Polynomial ℂ) (RatFunc ℂ) D ≠ 0 := by
    intro h; exact hD (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) (by rw [h, map_zero]))
  have hpoly0 : polyToMero U D ≠ 0 := by
    have heq : polyToMero U D
        = ratfuncToMero U hUo hUc hUne hUinf (algebraMap (Polynomial ℂ) (RatFunc ℂ) D) :=
      (ratfuncToMero_algebraMap_polynomial U hUo hUc hUne hUinf D).symm
    rw [heq]
    intro h
    exact hDr ((ratfuncToMero U hUo hUc hUne hUinf).injective (by rw [h, map_zero]))
  by_cases hPzero : P = 0
  · -- degenerate case: every cleared coefficient kills `φ_{c₂}` ⟹ via `hG`, `P_abs = 0`
    apply hP0
    apply Polynomial.ext
    intro i
    rw [Polynomial.coeff_zero]
    -- aeval φ_{c₂} (P_abs.coeff i) = 0 for every i
    have haeval0 : Polynomial.aeval (phiMero c₂ hU₂) (P_abs.coeff i) = 0 := by
      by_cases hi : i ∈ P_abs.support
      · have hbi : (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) = 0 := by
          have := hPcoeff i
          rw [if_pos hi] at this
          rw [hPzero, Polynomial.coeff_zero] at this
          exact this.symm
        have hmul := polyToMero_mul_aeval_phiMero hUo hUc hUne hUinf c₂ hU₂ D P_abs Q hQ i
        rw [hbi, map_zero] at hmul
        rcases mul_eq_zero.mp hmul with h | h
        · exact absurd h hpoly0
        · exact h
      · have : P_abs.coeff i = 0 := by
          by_contra h; exact hi (Polynomial.mem_support_iff.mpr h)
        rw [this, map_zero]
    -- transcendence of φ_{c₂} ⟹ coefficient is zero
    by_contra hci
    exact hG ⟨P_abs.coeff i, hci, haeval0⟩
  · -- generic case: nonzero relation ⟹ refuted by the natural-boundary input `hno`
    -- `P.support ⊆ P_abs.support`, and `P.coeff i = b i` there
    have hsub : ∀ i ∈ P.support, i ∈ P_abs.support := by
      intro i hi
      by_contra hni
      have := hPcoeff i
      rw [if_neg hni] at this
      exact (Polynomial.mem_support_iff.mp hi) this
    have ha : ∀ i ∈ P.support,
        ((P.coeff i).val : Germ (𝓟 U) ℂ)
          = ((fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z) : ℂ → ℂ)
              : Germ (𝓟 U) ℂ) := by
      intro i hi
      have hcoeff_eq : P.coeff i = (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) := by
        have := hPcoeff i; rw [if_pos (hsub i hi)] at this; exact this
      rw [hcoeff_eq, eval₂_polyToAnalytic_val c₂ hU₂ (Q i)]
    have hEqOn := function_eqOn_of_eval_phiAnalytic_zero c₁ hU₁ P
      (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ha hstep5
    -- nontriviality: some support index has nonzero cleared coefficient
    obtain ⟨i₀, hi₀⟩ := Polynomial.support_nonempty.mpr hPzero
    have hbi₀ : (Q i₀).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0 := by
      have hcoeff_eq : P.coeff i₀ = (Q i₀).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) := by
        have := hPcoeff i₀; rw [if_pos (hsub i₀ hi₀)] at this; exact this
      rw [← hcoeff_eq]; exact Polynomial.mem_support_iff.mp hi₀
    exact hno Q P.support ⟨i₀, hi₀, hbi₀⟩ hEqOn

end Bottcher
