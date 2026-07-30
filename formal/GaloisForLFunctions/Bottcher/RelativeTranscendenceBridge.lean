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
import GaloisForLFunctions.Bottcher.GlobalBasinBranch
import GaloisForLFunctions.Bottcher.RelativeBranchFamily
import GaloisForLFunctions.U0.HolomorphicIFT
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

namespace Bottcher

variable {U : Set ℂ}

/-- **`hG` as the concrete `C[z,Y]` kernel statement.**  If `φ_c` is transcendental over
`ℂ(z)`, then no nonzero bivariate polynomial `q(z,Y)` can vanish after substituting
`Y = φ_c` as an analytic-subring element on `U`. -/
theorem eval₂_polyToAnalytic_phiAnalytic_eq_zero_iff_of_transcendental
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c hU))
    (q : Polynomial (Polynomial ℂ)) :
    q.eval₂ (polyToAnalytic U) (phiAnalytic c hU) = 0 ↔ q = 0 := by
  constructor
  · intro hq
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    have haeval := aeval_phiMero_eq hUo hUc hUne hUinf c hU q
    rw [hq, map_zero] at haeval
    have haeval0 : Polynomial.aeval (phiMero c hU)
        (q.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))) = 0 := by
      exact haeval
    have hmap0 : q.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) = 0 := by
      by_contra hmapne
      exact (hG ⟨q.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)), hmapne, haeval0⟩).elim
    exact (Polynomial.map_eq_zero_iff
      (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ))).mp hmap0
  · intro hq
    rw [hq]
    simp

/-- Nonzero form of `eval₂_polyToAnalytic_phiAnalytic_eq_zero_iff_of_transcendental`. -/
theorem eval₂_polyToAnalytic_phiAnalytic_ne_zero_of_transcendental
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c hU))
    {q : Polynomial (Polynomial ℂ)} (hq : q ≠ 0) :
    q.eval₂ (polyToAnalytic U) (phiAnalytic c hU) ≠ 0 := by
  intro hzero
  exact hq ((eval₂_polyToAnalytic_phiAnalytic_eq_zero_iff_of_transcendental
    hUo hUc hUne hUinf c hU hG q).mp hzero)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- If the analytic-subring substitution `q(z, φ_c(z))` is nonzero, then it is nonzero at some
point of `U`.  This is the point-picking half of the primitive/squarefree normalization route. -/
theorem exists_mem_ne_zero_of_eval₂_polyToAnalytic_phiAnalytic_ne_zero
    (c : ℂ) (hU : U ⊆ escapeOpen c) (q : Polynomial (Polynomial ℂ))
    (hneq : q.eval₂ (polyToAnalytic U) (phiAnalytic c hU) ≠ 0) :
    ∃ w ∈ U, q.eval₂ (Polynomial.evalRingHom w) (bottcherCoord c w) ≠ 0 := by
  by_contra h
  push Not at h
  apply hneq
  apply Subtype.ext
  rw [eval₂_polyToAnalytic_val c hU q, ZeroMemClass.coe_zero, ← Germ.coe_zero, Germ.coe_eq]
  exact Filter.eventually_principal.mpr h

/-- **Good-point extraction from `hG`.**  A nonzero bivariate polynomial `q(z,Y)` cannot vanish at
`Y = γ(z)` for every `z ∈ U` when `γ` agrees with `φ_c` on `U`.  In particular, the good point may be
chosen in the other filled-Julia complement because `U ⊆ escapeOpen c`. -/
theorem exists_mem_compl_filledJulia_gamma_ne_zero_of_bivariate_ne_zero_transcendental
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c hU))
    (γ : ℂ → ℂ) (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c z)
    {q : Polynomial (Polynomial ℂ)} (hq : q ≠ 0) :
    ∃ w ∈ U, w ∈ (filledJulia c)ᶜ ∧ q.eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 := by
  have hne := eval₂_polyToAnalytic_phiAnalytic_ne_zero_of_transcendental
    hUo hUc hUne hUinf c hU hG hq
  obtain ⟨w, hwU, hwne⟩ :=
    exists_mem_ne_zero_of_eval₂_polyToAnalytic_phiAnalytic_ne_zero c hU q hne
  refine ⟨w, hwU, escapeOpen_subset_compl_filledJulia c (hU hwU), ?_⟩
  simpa [hγmatch w hwU] using hwne

end Bottcher

namespace Bottcher

/-- A nonzero polynomial in the fibre variable `X` with coefficients in `ℂ[z][Y]` has a squarefree
radical divisor.  This is the first algebraic brick for the primitive/squarefree normalization route:
apply the UFD radical lemma in the ring `ℂ[z][Y][X]`. -/
theorem exists_squarefree_divisor_pow_CzY
    (P : Polynomial (Polynomial (Polynomial ℂ))) (hP : P ≠ 0) :
    ∃ (D : Polynomial (Polynomial (Polynomial ℂ))) (n : ℕ),
      D ≠ 0 ∧ Squarefree D ∧ D ∣ P ∧ P ∣ D ^ n := by
  obtain ⟨D, n, hDsq, hDP, hPD⟩ :=
    exists_squarefree_dvd_pow_of_ne_zero (R := Polynomial (Polynomial (Polynomial ℂ))) (x := P) hP
  exact ⟨D, n, hDsq.ne_zero, hDsq, hDP, hPD⟩

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- The sparse relation `∑ i∈s Qᵢ(z,Y) X^i` as a single polynomial in the fibre variable `X`, with
coefficients in `ℂ[z][Y]`. -/
noncomputable def sparseRelationPoly (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ) :
    Polynomial (Polynomial (Polynomial ℂ)) :=
  ∑ i ∈ s, Polynomial.monomial i (Q i)

/-- Coefficients of `sparseRelationPoly` recover the sparse family on `s` and are zero off `s`. -/
theorem sparseRelationPoly_coeff (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ) (i : ℕ) :
    (sparseRelationPoly Q s).coeff i = if i ∈ s then Q i else 0 := by
  rw [sparseRelationPoly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' s i Q]

/-- The sparse relation polynomial is nonzero as soon as one sparse coefficient is nonzero after
substituting `Y = φ₂`. -/
theorem sparseRelationPoly_ne_zero_of_hnt
    (c₂ : ℂ) (hU₂ : U ⊆ escapeOpen c₂)
    (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ)
    (hnt : ∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) :
    sparseRelationPoly Q s ≠ 0 := by
  obtain ⟨i, hi, hQi_eval⟩ := hnt
  have hQi0 : Q i ≠ 0 := by
    intro h0
    rw [h0] at hQi_eval
    simp at hQi_eval
  intro hP0
  have hcoeff : (sparseRelationPoly Q s).coeff i = 0 := by
    simpa using congrArg (fun P : Polynomial (Polynomial (Polynomial ℂ)) => P.coeff i) hP0
  rw [sparseRelationPoly_coeff Q s i, if_pos hi] at hcoeff
  exact hQi0 hcoeff

/-- Evaluating the single sparse-relation polynomial is exactly the original sparse sum. -/
theorem eval_sparseRelationPoly (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ)
    (z y x : ℂ) :
    (sparseRelationPoly Q s).eval₂
        (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y) x
      = ∑ i ∈ s, (Q i).eval₂ (Polynomial.evalRingHom z) y * x ^ i := by
  rw [sparseRelationPoly, Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Polynomial.eval₂_monomial]
  rfl

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- Reassembling a polynomial from its coefficient family over its support gives the original
polynomial. -/
theorem sparseRelationPoly_coeff_support_eq (P : Polynomial (Polynomial (Polynomial ℂ))) :
    sparseRelationPoly (fun i => P.coeff i) P.support = P := by
  rw [sparseRelationPoly]
  exact P.as_sum_support.symm

/-- If `P` vanishes under a pointwise fibre substitution and `P ∣ D^n` with `n > 0`, then `D` also
vanishes under that substitution.  This is the radical step in the primitive/squarefree route, avoiding
any global analytic-domain argument: it is pointwise in `ℂ`. -/
theorem eval₂_eq_zero_of_dvd_pow_of_eval₂_eq_zero
    (P D : Polynomial (Polynomial (Polynomial ℂ))) {n : ℕ}
    (hdiv : P ∣ D ^ n) (hn : 0 < n)
    (β γ : ℂ → ℂ)
    (hPzero : ∀ z ∈ U,
      P.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) (γ z)) (β z) = 0) :
    ∀ z ∈ U, D.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) (γ z)) (β z) = 0 := by
  obtain ⟨S, hS⟩ := hdiv
  intro z hz
  let ev : Polynomial (Polynomial (Polynomial ℂ)) →+* ℂ :=
    Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) (γ z)) (β z)
  have hpow : (ev D) ^ n = 0 := by
    have h := congrArg ev hS
    dsimp [ev] at h
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_mul, hPzero z hz, zero_mul] at h
    exact h
  exact (pow_eq_zero_iff (Nat.ne_of_gt hn)).mp hpow

/-- Sparse-support form of `eval₂_eq_zero_of_dvd_pow_of_eval₂_eq_zero`: the coefficient family of the
radical divisor `D` is a new sparse relation vanishing on `U`. -/
theorem coeff_family_relation_zero_of_dvd_pow
    (P D : Polynomial (Polynomial (Polynomial ℂ))) {n : ℕ}
    (hdiv : P ∣ D ^ n) (hn : 0 < n)
    (β γ : ℂ → ℂ)
    (hPzero : ∀ z ∈ U,
      P.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) (γ z)) (β z) = 0) :
    Set.EqOn (fun z => ∑ i ∈ D.support,
        (D.coeff i).eval₂ (Polynomial.evalRingHom z) (γ z) * (β z) ^ i) 0 U := by
  intro z hz
  have hDzero := eval₂_eq_zero_of_dvd_pow_of_eval₂_eq_zero P D hdiv hn β γ hPzero z hz
  change (∑ i ∈ D.support, (D.coeff i).eval₂ (Polynomial.evalRingHom z) (γ z) * (β z) ^ i) = 0
  rw [← eval_sparseRelationPoly (fun i => D.coeff i) D.support z (γ z) (β z)]
  rw [sparseRelationPoly_coeff_support_eq D]
  exact hDzero

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- Support of a polynomial in the fibre variable is bounded by `natDegree`. -/
theorem support_subset_range_natDegree_add_one_CzY
    (D : Polynomial (Polynomial (Polynomial ℂ))) :
    D.support ⊆ Finset.range (D.natDegree + 1) := by
  intro i hi
  rw [Finset.mem_range]
  exact Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi))

/-- The top degree belongs to the support of a nonzero fibre polynomial. -/
theorem natDegree_mem_support_of_ne_zero_CzY
    {D : Polynomial (Polynomial (Polynomial ℂ))} (hD : D ≠ 0) :
    D.natDegree ∈ D.support := by
  rw [Polynomial.mem_support_iff, Polynomial.coeff_natDegree]
  exact Polynomial.leadingCoeff_ne_zero.mpr hD

/-- `hG` supplies nontriviality of the coefficient family of any nonzero fibre polynomial. -/
theorem exists_support_coeff_eval₂_ne_zero_of_transcendental
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c hU))
    {D : Polynomial (Polynomial (Polynomial ℂ))} (hD : D ≠ 0) :
    ∃ i ∈ D.support, (D.coeff i).eval₂ (polyToAnalytic U) (phiAnalytic c hU) ≠ 0 := by
  obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr hD
  refine ⟨i, hi, ?_⟩
  intro hzero
  have hcoeff0 : D.coeff i = 0 :=
    (eval₂_polyToAnalytic_phiAnalytic_eq_zero_iff_of_transcendental
      hUo hUc hUne hUinf c hU hG (D.coeff i)).mp hzero
  exact (Polynomial.mem_support_iff.mp hi) hcoeff0

/-- If a bivariate polynomial evaluated at the Böttcher coordinate vanishes pointwise on the carrier,
then its analytic-subring evaluation is zero. -/
theorem eval₂_polyToAnalytic_eq_zero_of_eqOn_bridge {c : ℂ} {hU : U ⊆ escapeOpen c}
    (q : Polynomial (Polynomial ℂ))
    (hEq : Set.EqOn (fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z)) 0 U) :
    q.eval₂ (polyToAnalytic U) (phiAnalytic c hU) = 0 := by
  apply Subtype.ext
  rw [eval₂_polyToAnalytic_val c hU q, ZeroMemClass.coe_zero, ← Germ.coe_zero, Germ.coe_eq]
  exact Filter.eventually_principal.mpr hEq

/-- Degree-zero sparse relations cannot vanish when their lone coefficient is nonzero after
substitution. -/
theorem false_of_singleton_zero_sparse_relation_bridge
    (c₁ c₂ : ℂ) (hU₂ : U ⊆ escapeOpen c₂)
    (Q : ℕ → Polynomial (Polynomial ℂ))
    (hQ0 : (Q 0).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0)
    (hEqOn : Set.EqOn (fun z => ∑ i ∈ ({0} : Finset ℕ),
        ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U) :
    False := by
  have hcoef : Set.EqOn
      (fun z => (Q 0).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) 0 U := by
    intro z hz
    have h := hEqOn hz
    simpa using h
  exact hQ0 (eval₂_polyToAnalytic_eq_zero_of_eqOn_bridge (c := c₂) (hU := hU₂) (Q 0) hcoef)

/-- A nontrivial sparse relation supported only in degree zero is impossible. -/
theorem false_of_sparse_relation_support_range_one_bridge
    (c₁ c₂ : ℂ) (hU₂ : U ⊆ escapeOpen c₂)
    (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ)
    (hnt : ∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0)
    (hsupp : s ⊆ Finset.range 1)
    (hEqOn : Set.EqOn (fun z => ∑ i ∈ s,
        ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U) :
    False := by
  obtain ⟨i, hi, hQi⟩ := hnt
  have hi0 : i = 0 := by
    exact Nat.lt_one_iff.mp (Finset.mem_range.mp (hsupp hi))
  have h0s : 0 ∈ s := by
    simpa [hi0] using hi
  have hs : s = ({0} : Finset ℕ) := by
    apply Finset.ext
    intro j
    constructor
    · intro hj
      have hj0 : j = 0 := Nat.lt_one_iff.mp (Finset.mem_range.mp (hsupp hj))
      simp [hj0]
    · intro hj
      have hj0 : j = 0 := by simpa using hj
      simpa [hj0] using h0s
  have hQ0 : (Q 0).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0 := by
    simpa [hi0] using hQi
  exact false_of_singleton_zero_sparse_relation_bridge c₁ c₂ hU₂ Q hQ0 (by
    intro z hz
    simpa [hs] using hEqOn hz)

/-- A radical-divisor relation has positive fibre degree.  Degree zero would be a scalar coefficient
relation in `φ₂`, contradicting the `hG` kernel. -/
theorem one_le_natDegree_of_coeff_family_relation_zero_of_transcendental
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    {D : Polynomial (Polynomial (Polynomial ℂ))} (hD : D ≠ 0)
    (hEqOn : Set.EqOn (fun z => ∑ i ∈ D.support,
        ((D.coeff i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U) :
    1 ≤ D.natDegree := by
  by_contra hnot
  have hN0 : D.natDegree = 0 := Nat.eq_zero_of_not_pos hnot
  have hnt := exists_support_coeff_eval₂_ne_zero_of_transcendental
    hUo hUc hUne hUinf c₂ hU₂ hG hD
  have hsupp : D.support ⊆ Finset.range 1 := by
    intro i hi
    have hirange := support_subset_range_natDegree_add_one_CzY D hi
    simpa [hN0] using hirange
  exact false_of_sparse_relation_support_range_one_bridge c₁ c₂ hU₂ (fun i => D.coeff i)
    D.support hnt hsupp hEqOn

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- Core output of the radical-divisor route: a raw sparse relation plus a divisor `D` with
`P ∣ D^n` produces the normalized coefficient family indexed by `D.support`, with positive top degree.
The only remaining primitive/squarefree output is the bad-locus polynomial forcing separability of one
specialized fibre. -/
theorem radical_coeff_family_core_of_sparse_relation
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ)
    (hEqOn : Set.EqOn (fun z => ∑ i ∈ s,
        ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U)
    {D : Polynomial (Polynomial (Polynomial ℂ))} {n : ℕ}
    (hD : D ≠ 0) (hdiv : sparseRelationPoly Q s ∣ D ^ n) (hn : 0 < n) :
    ∃ (Q' : ℕ → Polynomial (Polynomial ℂ)) (s' : Finset ℕ) (N : ℕ),
      (∃ i ∈ s', (Q' i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) ∧
      Set.EqOn (fun z => ∑ i ∈ s',
          ((Q' i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
            * (bottcherCoord c₁ z) ^ i) 0 U ∧
      s' ⊆ Finset.range (N + 1) ∧ N ∈ s' ∧ 1 ≤ N := by
  let P := sparseRelationPoly Q s
  have hPzero : ∀ z ∈ U,
      P.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
        (bottcherCoord c₁ z) = 0 := by
    intro z hz
    rw [show P = sparseRelationPoly Q s from rfl, eval_sparseRelationPoly]
    exact hEqOn hz
  have hDrel : Set.EqOn (fun z => ∑ i ∈ D.support,
        (D.coeff i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z) *
          (bottcherCoord c₁ z) ^ i) 0 U := by
    simpa [P] using
      (coeff_family_relation_zero_of_dvd_pow (U := U) P D hdiv hn
        (bottcherCoord c₁) (bottcherCoord c₂) hPzero)
  refine ⟨fun i => D.coeff i, D.support, D.natDegree, ?_, hDrel, ?_, ?_, ?_⟩
  · exact exists_support_coeff_eval₂_ne_zero_of_transcendental
      hUo hUc hUne hUinf c₂ hU₂ hG hD
  · exact support_subset_range_natDegree_add_one_CzY D
  · exact natDegree_mem_support_of_ne_zero_CzY hD
  · exact one_le_natDegree_of_coeff_family_relation_zero_of_transcendental
      hUo hUc hUne hUinf c₁ c₂ hU₂ hG hD hDrel

end Bottcher

namespace Bottcher

/-- The top `X`-coefficient of a fibre polynomial `D ∈ C[z][Y][X]`, viewed as a `Y`-polynomial
with coefficients in `C[z]`. -/
noncomputable def topCoeffY (D : Polynomial (Polynomial (Polynomial ℂ))) :
    Polynomial (Polynomial ℂ) :=
  D.leadingCoeff

/-- The `Y`-content of the top `X`-coefficient. -/
noncomputable def topCoeffYContent (D : Polynomial (Polynomial (Polynomial ℂ))) : Polynomial ℂ :=
  (topCoeffY D).content

/-- The primitive `Y`-part of the top `X`-coefficient. -/
noncomputable def topCoeffYPrim (D : Polynomial (Polynomial (Polynomial ℂ))) :
    Polynomial (Polynomial ℂ) :=
  (topCoeffY D).primPart

/-- Grok's top-stratum `Y`-derivative guard: differentiate only the primitive `Y`-part of the top
`X`-coefficient. -/
noncomputable def topCoeffYDerivGuard (D : Polynomial (Polynomial (Polynomial ℂ))) :
    Polynomial (Polynomial ℂ) :=
  (topCoeffYPrim D).derivative

/-- The GhostLeading bad-locus factor in `C[z][Y]`: top coefficient, its `Y`-content lifted to
`C[z][Y]`, and the primitive top-stratum `Y`-derivative guard. -/
noncomputable def ghostLeadingBadY (D : Polynomial (Polynomial (Polynomial ℂ))) :
    Polynomial (Polynomial ℂ) :=
  topCoeffY D * Polynomial.C (topCoeffYContent D) * topCoeffYDerivGuard D

/-- The top `Y`-coefficient is nonzero for nonzero `D`. -/
theorem topCoeffY_ne_zero_of_ne_zero {D : Polynomial (Polynomial (Polynomial ℂ))} (hD : D ≠ 0) :
    topCoeffY D ≠ 0 := by
  simpa [topCoeffY] using (Polynomial.leadingCoeff_ne_zero.mpr hD)

/-- The `Y`-content of the top `X`-coefficient is nonzero for nonzero `D`. -/
theorem topCoeffYContent_ne_zero_of_ne_zero {D : Polynomial (Polynomial (Polynomial ℂ))}
    (hD : D ≠ 0) :
    topCoeffYContent D ≠ 0 := by
  intro hzero
  exact topCoeffY_ne_zero_of_ne_zero hD ((Polynomial.content_eq_zero_iff.mp hzero))

/-- Factor the top `X`-coefficient into its `Y`-content and primitive `Y`-part. -/
theorem topCoeffY_factor (D : Polynomial (Polynomial (Polynomial ℂ))) :
    topCoeffY D = Polynomial.C (topCoeffYContent D) * topCoeffYPrim D := by
  simpa [topCoeffYContent, topCoeffYPrim] using
    (Polynomial.eq_C_content_mul_primPart (topCoeffY D))

/-- Pointwise form of `topCoeffY_factor`. -/
theorem eval₂_topCoeffY_factor (D : Polynomial (Polynomial (Polynomial ℂ))) (z y : ℂ) :
    (topCoeffY D).eval₂ (Polynomial.evalRingHom z) y =
      (topCoeffYContent D).eval z *
        (topCoeffYPrim D).eval₂ (Polynomial.evalRingHom z) y := by
  rw [topCoeffY_factor D, Polynomial.eval₂_mul, Polynomial.eval₂_C]
  rfl

/-- Nonvanishing of the GhostLeading bad-locus factor forces all top-stratum guards to be nonzero at
that point. -/
theorem ghostLeadingBadY_components_ne_zero
    (D : Polynomial (Polynomial (Polynomial ℂ))) {z y : ℂ}
    (hbad : (ghostLeadingBadY D).eval₂ (Polynomial.evalRingHom z) y ≠ 0) :
    (topCoeffY D).eval₂ (Polynomial.evalRingHom z) y ≠ 0 ∧
      (topCoeffYContent D).eval z ≠ 0 ∧
      (topCoeffYDerivGuard D).eval₂ (Polynomial.evalRingHom z) y ≠ 0 := by
  have hprod :
      (topCoeffY D).eval₂ (Polynomial.evalRingHom z) y *
          (topCoeffYContent D).eval z *
          (topCoeffYDerivGuard D).eval₂ (Polynomial.evalRingHom z) y ≠ 0 := by
    simpa [ghostLeadingBadY, Polynomial.eval₂_mul, Polynomial.eval₂_C, mul_assoc] using hbad
  constructor
  · intro htop
    exact hprod (by simp [htop])
  constructor
  · intro hcontent
    exact hprod (by simp [hcontent])
  · intro hderiv
    exact hprod (by simp [hderiv])

/-- The endpoint's leading-coefficient nonvanishing follows from the GhostLeading bad-locus factor. -/
theorem topCoeffY_eval₂_ne_zero_of_ghostLeadingBadY_ne_zero
    (D : Polynomial (Polynomial (Polynomial ℂ))) {z y : ℂ}
    (hbad : (ghostLeadingBadY D).eval₂ (Polynomial.evalRingHom z) y ≠ 0) :
    (topCoeffY D).eval₂ (Polynomial.evalRingHom z) y ≠ 0 :=
  (ghostLeadingBadY_components_ne_zero D hbad).1

end Bottcher

namespace Bottcher

/-- A `C[z][Y]` polynomial that is constant in `Y`. -/
def IsYConstant (q : Polynomial (Polynomial ℂ)) : Prop :=
  ∃ a : Polynomial ℂ, q = Polynomial.C a

/-- Vanishing `Y`-derivative over `C[z]` forces `Y`-constancy. -/
theorem isYConstant_of_derivative_eq_zero {q : Polynomial (Polynomial ℂ)}
    (hderiv : q.derivative = 0) :
    IsYConstant q := by
  exact ⟨q.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hderiv⟩

/-- Lifted top-content nonvanishing. -/
theorem C_topCoeffYContent_ne_zero_of_ne_zero {D : Polynomial (Polynomial (Polynomial ℂ))}
    (hD : D ≠ 0) :
    Polynomial.C (topCoeffYContent D) ≠ (0 : Polynomial (Polynomial ℂ)) := by
  exact Polynomial.C_ne_zero.mpr (topCoeffYContent_ne_zero_of_ne_zero hD)

/-- If the top GhostLeading bad-locus factor vanishes, the primitive top `Y`-derivative guard is zero. -/
theorem topCoeffYDerivGuard_eq_zero_of_ghostLeadingBadY_eq_zero
    {D : Polynomial (Polynomial (Polynomial ℂ))} (hD : D ≠ 0)
    (hbad : ghostLeadingBadY D = 0) :
    topCoeffYDerivGuard D = 0 := by
  have htop : topCoeffY D ≠ 0 := topCoeffY_ne_zero_of_ne_zero hD
  have hcontentC : Polynomial.C (topCoeffYContent D) ≠ (0 : Polynomial (Polynomial ℂ)) :=
    C_topCoeffYContent_ne_zero_of_ne_zero hD
  have hleft : topCoeffY D * Polynomial.C (topCoeffYContent D) ≠ 0 :=
    mul_ne_zero htop hcontentC
  have hprod : topCoeffY D * Polynomial.C (topCoeffYContent D) * topCoeffYDerivGuard D = 0 := by
    simpa [ghostLeadingBadY] using hbad
  exact (mul_eq_zero.mp hprod).resolve_left hleft

/-- Zero top GhostLeading factor means the primitive top coefficient is `Y`-constant. -/
theorem topCoeffYPrim_isYConstant_of_ghostLeadingBadY_eq_zero
    {D : Polynomial (Polynomial (Polynomial ℂ))} (hD : D ≠ 0)
    (hbad : ghostLeadingBadY D = 0) :
    IsYConstant (topCoeffYPrim D) := by
  exact isYConstant_of_derivative_eq_zero
    (topCoeffYDerivGuard_eq_zero_of_ghostLeadingBadY_eq_zero hD hbad)

/-- Primitive `Y`-part of the `k`th `X`-coefficient. -/
noncomputable def coeffYPrim (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) :
    Polynomial (Polynomial ℂ) :=
  (D.coeff k).primPart

/-- `Y`-derivative guard for the primitive part of the `k`th `X`-coefficient. -/
noncomputable def coeffYDerivGuard (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) :
    Polynomial (Polynomial ℂ) :=
  (coeffYPrim D k).derivative

/-- The finite set of `X`-strata whose primitive `Y`-part has nonzero `Y`-derivative. -/
noncomputable def ghostStratumSet (D : Polynomial (Polynomial (Polynomial ℂ))) : Finset ℕ :=
  D.support.filter (fun k => coeffYDerivGuard D k ≠ 0)

/-- The current GhostLeading stratum, if any: the highest `X`-coefficient with nonzero primitive
`Y`-derivative. -/
noncomputable def ghostLeadingStratum (D : Polynomial (Polynomial (Polynomial ℂ))) : Option ℕ :=
  if h : (ghostStratumSet D).Nonempty then some ((ghostStratumSet D).max' h) else none

/-- Membership in the GhostLeading stratum set. -/
theorem mem_ghostStratumSet_iff (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) :
    k ∈ ghostStratumSet D ↔ k ∈ D.support ∧ coeffYDerivGuard D k ≠ 0 := by
  simp [ghostStratumSet]

/-- The top primitive coefficient is the primitive part of the `natDegree` coefficient. -/
theorem topCoeffYPrim_eq_coeffYPrim_natDegree (D : Polynomial (Polynomial (Polynomial ℂ))) :
    topCoeffYPrim D = coeffYPrim D D.natDegree := by
  simp [topCoeffYPrim, topCoeffY, coeffYPrim, Polynomial.coeff_natDegree]

/-- The top derivative guard is the derivative guard of the `natDegree` coefficient. -/
theorem topCoeffYDerivGuard_eq_coeffYDerivGuard_natDegree
    (D : Polynomial (Polynomial (Polynomial ℂ))) :
    topCoeffYDerivGuard D = coeffYDerivGuard D D.natDegree := by
  rw [topCoeffYDerivGuard, coeffYDerivGuard, ← topCoeffYPrim_eq_coeffYPrim_natDegree]

/-- When the top GhostLeading factor vanishes, the top degree is not a nonconstant-`Y` stratum; the
GhostLeading search must descend in the `X`-degree. -/
theorem natDegree_not_mem_ghostStratumSet_of_ghostLeadingBadY_eq_zero
    {D : Polynomial (Polynomial (Polynomial ℂ))} (hD : D ≠ 0)
    (hbad : ghostLeadingBadY D = 0) :
    D.natDegree ∉ ghostStratumSet D := by
  rw [mem_ghostStratumSet_iff]
  intro hmem
  have htopderiv : topCoeffYDerivGuard D = 0 :=
    topCoeffYDerivGuard_eq_zero_of_ghostLeadingBadY_eq_zero hD hbad
  have hcoeffderiv : coeffYDerivGuard D D.natDegree = 0 := by
    simpa [topCoeffYDerivGuard_eq_coeffYDerivGuard_natDegree D] using htopderiv
  exact hmem.2 hcoeffderiv

end Bottcher

namespace Bottcher

/-- If the optional GhostLeading stratum is present, it lies in the stratum set. -/
theorem ghostLeadingStratum_mem {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ}
    (hk : ghostLeadingStratum D = some k) :
    k ∈ ghostStratumSet D := by
  by_cases h : (ghostStratumSet D).Nonempty
  · simp [ghostLeadingStratum, h] at hk
    rw [← hk]
    exact Finset.max'_mem (ghostStratumSet D) h
  · simp [ghostLeadingStratum, h] at hk

/-- A present GhostLeading stratum is an actual `X`-support index. -/
theorem ghostLeadingStratum_support {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ}
    (hk : ghostLeadingStratum D = some k) :
    k ∈ D.support := by
  exact (mem_ghostStratumSet_iff D k).mp (ghostLeadingStratum_mem hk) |>.1

/-- A present GhostLeading stratum has nonzero primitive `Y`-derivative guard. -/
theorem ghostLeadingStratum_derivGuard_ne_zero {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ}
    (hk : ghostLeadingStratum D = some k) :
    coeffYDerivGuard D k ≠ 0 := by
  exact (mem_ghostStratumSet_iff D k).mp (ghostLeadingStratum_mem hk) |>.2

/-- A present GhostLeading stratum is bounded by the fibre degree. -/
theorem ghostLeadingStratum_le_natDegree {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ}
    (hk : ghostLeadingStratum D = some k) :
    k ≤ D.natDegree := by
  exact Polynomial.le_natDegree_of_ne_zero
    (Polynomial.mem_support_iff.mp (ghostLeadingStratum_support hk))

/-- If the top GhostLeading factor vanished, any remaining GhostLeading stratum is strictly lower in
`X`-degree. -/
theorem ghostLeadingStratum_lt_natDegree_of_ghostLeadingBadY_eq_zero
    {D : Polynomial (Polynomial (Polynomial ℂ))} (hD : D ≠ 0)
    (hbad : ghostLeadingBadY D = 0) {k : ℕ}
    (hk : ghostLeadingStratum D = some k) :
    k < D.natDegree := by
  have hle : k ≤ D.natDegree := ghostLeadingStratum_le_natDegree hk
  have hne : k ≠ D.natDegree := by
    intro hEq
    have hk_mem : k ∈ ghostStratumSet D := ghostLeadingStratum_mem hk
    exact natDegree_not_mem_ghostStratumSet_of_ghostLeadingBadY_eq_zero hD hbad (by simpa [hEq] using hk_mem)
  exact lt_of_le_of_ne hle hne

end Bottcher

namespace Bottcher

/-- `ghostLeadingStratum = none` exactly means the stratum set is empty. -/
theorem ghostLeadingStratum_eq_none_iff_not_nonempty
    (D : Polynomial (Polynomial (Polynomial ℂ))) :
    ghostLeadingStratum D = none ↔ ¬ (ghostStratumSet D).Nonempty := by
  by_cases h : (ghostStratumSet D).Nonempty
  · simp [ghostLeadingStratum, h]
  · simp [ghostLeadingStratum, h]

/-- If no GhostLeading stratum remains, each support coefficient has zero primitive `Y`-derivative. -/
theorem coeffYDerivGuard_eq_zero_of_ghostLeadingStratum_none
    {D : Polynomial (Polynomial (Polynomial ℂ))}
    (hnone : ghostLeadingStratum D = none) {k : ℕ} (hk : k ∈ D.support) :
    coeffYDerivGuard D k = 0 := by
  have hnot : ¬ (ghostStratumSet D).Nonempty :=
    (ghostLeadingStratum_eq_none_iff_not_nonempty D).mp hnone
  by_contra hne
  exact hnot ⟨k, (mem_ghostStratumSet_iff D k).mpr ⟨hk, hne⟩⟩

/-- If no GhostLeading stratum remains, each primitive support coefficient is `Y`-constant. -/
theorem coeffYPrim_isYConstant_of_ghostLeadingStratum_none
    {D : Polynomial (Polynomial (Polynomial ℂ))}
    (hnone : ghostLeadingStratum D = none) {k : ℕ} (hk : k ∈ D.support) :
    IsYConstant (coeffYPrim D k) := by
  exact isYConstant_of_derivative_eq_zero
    (coeffYDerivGuard_eq_zero_of_ghostLeadingStratum_none hnone hk)

/-- If a coefficient's primitive `Y`-part is `Y`-constant, the coefficient itself is `Y`-constant. -/
theorem coeff_isYConstant_of_coeffYPrim_isYConstant
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ)
    (hconst : IsYConstant (coeffYPrim D k)) :
    IsYConstant (D.coeff k) := by
  obtain ⟨a, ha⟩ := hconst
  refine ⟨(D.coeff k).content * a, ?_⟩
  calc
    D.coeff k = Polynomial.C (D.coeff k).content * (D.coeff k).primPart :=
      Polynomial.eq_C_content_mul_primPart (D.coeff k)
    _ = Polynomial.C ((D.coeff k).content * a) := by
      rw [show (D.coeff k).primPart = Polynomial.C a from ha]
      rw [← Polynomial.C_mul]

/-- If no GhostLeading stratum remains, every support coefficient of `D` is `Y`-constant. -/
theorem coeff_isYConstant_of_ghostLeadingStratum_none
    {D : Polynomial (Polynomial (Polynomial ℂ))}
    (hnone : ghostLeadingStratum D = none) {k : ℕ} (hk : k ∈ D.support) :
    IsYConstant (D.coeff k) := by
  exact coeff_isYConstant_of_coeffYPrim_isYConstant D k
    (coeffYPrim_isYConstant_of_ghostLeadingStratum_none hnone hk)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- Chosen `C[z]` coefficient witnessing that the `i`th coefficient of a no-stratum `D` is
`Y`-constant. Outside support the coefficient is set to zero. -/
noncomputable def yConstantCoeffOf
    (D : Polynomial (Polynomial (Polynomial ℂ))) (hnone : ghostLeadingStratum D = none)
    (i : ℕ) : Polynomial ℂ :=
  if hi : i ∈ D.support then Classical.choose (coeff_isYConstant_of_ghostLeadingStratum_none hnone hi) else 0

/-- Rebuild a support coefficient from its chosen `C[z]` witness. -/
theorem coeff_eq_C_yConstantCoeffOf
    (D : Polynomial (Polynomial (Polynomial ℂ))) (hnone : ghostLeadingStratum D = none)
    {i : ℕ} (hi : i ∈ D.support) :
    D.coeff i = Polynomial.C (yConstantCoeffOf D hnone i) := by
  dsimp [yConstantCoeffOf]
  rw [dif_pos hi]
  exact Classical.choose_spec (coeff_isYConstant_of_ghostLeadingStratum_none hnone hi)

/-- Collapse a no-stratum `D ∈ C[z][Y][X]` to the corresponding `E ∈ C[z][X]`. -/
noncomputable def yConstantCollapseX
    (D : Polynomial (Polynomial (Polynomial ℂ))) (hnone : ghostLeadingStratum D = none) :
    Polynomial (Polynomial ℂ) :=
  ∑ i ∈ D.support, Polynomial.monomial i (yConstantCoeffOf D hnone i)

/-- Coefficients of the collapsed `C[z][X]` polynomial. -/
theorem yConstantCollapseX_coeff
    (D : Polynomial (Polynomial (Polynomial ℂ))) (hnone : ghostLeadingStratum D = none)
    (i : ℕ) :
    (yConstantCollapseX D hnone).coeff i =
      if i ∈ D.support then yConstantCoeffOf D hnone i else 0 := by
  rw [yConstantCollapseX, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' D.support i (fun i => yConstantCoeffOf D hnone i)]

/-- The collapsed `C[z][X]` polynomial is nonzero when `D` is nonzero. -/
theorem yConstantCollapseX_ne_zero_of_ne_zero
    {D : Polynomial (Polynomial (Polynomial ℂ))} (hD : D ≠ 0)
    (hnone : ghostLeadingStratum D = none) :
    yConstantCollapseX D hnone ≠ 0 := by
  have hN : D.natDegree ∈ D.support := natDegree_mem_support_of_ne_zero_CzY hD
  have hcoeffD : D.coeff D.natDegree ≠ 0 := Polynomial.mem_support_iff.mp hN
  have hcoeffEq := coeff_eq_C_yConstantCoeffOf D hnone hN
  have hcoeffE : (yConstantCollapseX D hnone).coeff D.natDegree =
      yConstantCoeffOf D hnone D.natDegree := by
    rw [yConstantCollapseX_coeff, if_pos hN]
  intro hE0
  have ha0 : yConstantCoeffOf D hnone D.natDegree = 0 := by
    rw [← hcoeffE, hE0, Polynomial.coeff_zero]
  exact hcoeffD (by rw [hcoeffEq, ha0, Polynomial.C_0])

/-- Evaluation of the collapsed `C[z][X]` polynomial. -/
theorem eval_yConstantCollapseX
    (D : Polynomial (Polynomial (Polynomial ℂ))) (hnone : ghostLeadingStratum D = none)
    (z x : ℂ) :
    (yConstantCollapseX D hnone).eval₂ (Polynomial.evalRingHom z) x =
      ∑ i ∈ D.support, (yConstantCoeffOf D hnone i).eval z * x ^ i := by
  rw [yConstantCollapseX, Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Polynomial.eval₂_monomial]
  rfl

/-- No-stratum GhostLeading endpoint: if all support coefficients are truly `C[z]`-only, then the
relation is a forbidden nonzero `C[z][X]` relation for `φ₁`. -/
theorem no_stratum_false_of_coeff_family_relation_zero_of_transcendental_left
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    {D : Polynomial (Polynomial (Polynomial ℂ))} (hD : D ≠ 0)
    (hnone : ghostLeadingStratum D = none)
    (hEqOn : Set.EqOn (fun z => ∑ i ∈ D.support,
        ((D.coeff i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U) :
    False := by
  let E := yConstantCollapseX D hnone
  have hE0 : E ≠ 0 := yConstantCollapseX_ne_zero_of_ne_zero hD hnone
  have hEeq : Set.EqOn (fun z => E.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₁ z)) 0 U := by
    intro z hz
    change E.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₁ z) = 0
    rw [show E = yConstantCollapseX D hnone from rfl, eval_yConstantCollapseX]
    have hrel := hEqOn hz
    calc
      ∑ i ∈ D.support, (yConstantCoeffOf D hnone i).eval z * (bottcherCoord c₁ z) ^ i
          = ∑ i ∈ D.support,
              ((D.coeff i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) *
                (bottcherCoord c₁ z) ^ i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [coeff_eq_C_yConstantCoeffOf D hnone hi, Polynomial.eval₂_C]
            rfl
      _ = 0 := hrel
  have hEvalZero : E.eval₂ (polyToAnalytic U) (phiAnalytic c₁ hU₁) = 0 :=
    eval₂_polyToAnalytic_eq_zero_of_eqOn_bridge (c := c₁) (hU := hU₁) E hEeq
  have hEzero := (eval₂_polyToAnalytic_phiAnalytic_eq_zero_iff_of_transcendental
    hUo hUc hUne hUinf c₁ hU₁ hG₁ E).mp hEvalZero
  exact hE0 hEzero

end Bottcher

namespace Bottcher

/-- Truncate a fibre polynomial to its `X`-support at degrees `≤ k`. -/
noncomputable def lowerTruncationX (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) :
    Polynomial (Polynomial (Polynomial ℂ)) :=
  ∑ i ∈ D.support.filter (fun j => j ≤ k), Polynomial.monomial i (D.coeff i)

/-- Coefficients of the lower `X`-truncation. -/
theorem lowerTruncationX_coeff (D : Polynomial (Polynomial (Polynomial ℂ))) (k i : ℕ) :
    (lowerTruncationX D k).coeff i =
      if i ∈ D.support.filter (fun j => j ≤ k) then D.coeff i else 0 := by
  rw [lowerTruncationX, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (D.support.filter (fun j => j ≤ k)) i (fun i => D.coeff i)]

/-- A retained coefficient is unchanged in the lower truncation. -/
theorem lowerTruncationX_coeff_of_mem
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k i : ℕ}
    (hi : i ∈ D.support) (hik : i ≤ k) :
    (lowerTruncationX D k).coeff i = D.coeff i := by
  rw [lowerTruncationX_coeff, if_pos]
  exact Finset.mem_filter.mpr ⟨hi, hik⟩

/-- Coefficients above the truncation degree vanish. -/
theorem lowerTruncationX_coeff_eq_zero_of_lt
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k i : ℕ} (hki : k < i) :
    (lowerTruncationX D k).coeff i = 0 := by
  rw [lowerTruncationX_coeff, if_neg]
  intro hi
  exact not_le_of_gt hki (Finset.mem_filter.mp hi).2

/-- The lower truncation has degree at most the truncation index. -/
theorem lowerTruncationX_natDegree_le
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) :
    (lowerTruncationX D k).natDegree ≤ k := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro i hki
  exact lowerTruncationX_coeff_eq_zero_of_lt D hki

/-- If `k` is in support, the lower truncation has exact degree `k`. -/
theorem lowerTruncationX_natDegree_eq_of_mem
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ} (hk : k ∈ D.support) :
    (lowerTruncationX D k).natDegree = k := by
  apply le_antisymm
  · exact lowerTruncationX_natDegree_le D k
  · have hcoeff : (lowerTruncationX D k).coeff k ≠ 0 := by
      rw [lowerTruncationX_coeff_of_mem hk le_rfl]
      exact Polynomial.mem_support_iff.mp hk
    exact Polynomial.le_natDegree_of_ne_zero hcoeff

/-- Leading coefficient of the lower truncation. -/
theorem lowerTruncationX_leadingCoeff_eq_of_mem
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ} (hk : k ∈ D.support) :
    (lowerTruncationX D k).leadingCoeff = D.coeff k := by
  rw [← Polynomial.coeff_natDegree, lowerTruncationX_natDegree_eq_of_mem hk,
    lowerTruncationX_coeff_of_mem hk le_rfl]

/-- Top `Y`-coefficient of the lower truncation. -/
theorem topCoeffY_lowerTruncationX_eq_of_mem
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ} (hk : k ∈ D.support) :
    topCoeffY (lowerTruncationX D k) = D.coeff k := by
  simpa [topCoeffY] using lowerTruncationX_leadingCoeff_eq_of_mem hk

/-- Primitive top `Y`-part of the lower truncation. -/
theorem topCoeffYPrim_lowerTruncationX_eq_coeffYPrim_of_mem
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ} (hk : k ∈ D.support) :
    topCoeffYPrim (lowerTruncationX D k) = coeffYPrim D k := by
  simp [topCoeffYPrim, coeffYPrim, topCoeffY_lowerTruncationX_eq_of_mem hk]

/-- Top `Y`-derivative guard of the lower truncation. -/
theorem topCoeffYDerivGuard_lowerTruncationX_eq_coeffYDerivGuard_of_mem
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ} (hk : k ∈ D.support) :
    topCoeffYDerivGuard (lowerTruncationX D k) = coeffYDerivGuard D k := by
  simp [topCoeffYDerivGuard, coeffYDerivGuard,
    topCoeffYPrim_lowerTruncationX_eq_coeffYPrim_of_mem hk]

/-- A selected GhostLeading stratum becomes a genuine nonzero top bad-locus after lower truncation. -/
theorem ghostLeadingBadY_lowerTruncationX_ne_zero_of_stratum
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ}
    (hk : ghostLeadingStratum D = some k) :
    ghostLeadingBadY (lowerTruncationX D k) ≠ 0 := by
  have hksupp : k ∈ D.support := ghostLeadingStratum_support hk
  have hcoeff0 : D.coeff k ≠ 0 := Polynomial.mem_support_iff.mp hksupp
  have htop0 : topCoeffY (lowerTruncationX D k) ≠ 0 := by
    rw [topCoeffY_lowerTruncationX_eq_of_mem hksupp]
    exact hcoeff0
  have hcontent0 : topCoeffYContent (lowerTruncationX D k) ≠ 0 := by
    intro hzero
    exact htop0 (Polynomial.content_eq_zero_iff.mp hzero)
  have hcontentC0 : Polynomial.C (topCoeffYContent (lowerTruncationX D k)) ≠
      (0 : Polynomial (Polynomial ℂ)) := by
    exact Polynomial.C_ne_zero.mpr hcontent0
  have hderiv0 : topCoeffYDerivGuard (lowerTruncationX D k) ≠ 0 := by
    rw [topCoeffYDerivGuard_lowerTruncationX_eq_coeffYDerivGuard_of_mem hksupp]
    exact ghostLeadingStratum_derivGuard_ne_zero hk
  simp [ghostLeadingBadY, mul_ne_zero htop0 hcontentC0, hderiv0]

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- `hG₂` chooses a concrete point where the lower-truncation GhostLeading bad-locus and all its
component guards are nonzero. -/
theorem exists_good_point_for_lowerTruncation_ghostLeadingStratum
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₂ : ℂ) (hU₂ : U ⊆ escapeOpen c₂)
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (γ : ℂ → ℂ) (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ}
    (hk : ghostLeadingStratum D = some k) :
    ∃ w ∈ U, w ∈ (filledJulia c₂)ᶜ ∧
      (topCoeffY (lowerTruncationX D k)).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
      (topCoeffYContent (lowerTruncationX D k)).eval w ≠ 0 ∧
      (topCoeffYDerivGuard (lowerTruncationX D k)).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 := by
  have hB0 : ghostLeadingBadY (lowerTruncationX D k) ≠ 0 :=
    ghostLeadingBadY_lowerTruncationX_ne_zero_of_stratum hk
  obtain ⟨w, hwU, hwoff, hBne⟩ :=
    exists_mem_compl_filledJulia_gamma_ne_zero_of_bivariate_ne_zero_transcendental
      hUo hUc hUne hUinf c₂ hU₂ hG₂ γ hγmatch hB0
  obtain ⟨htop, hcontent, hderiv⟩ :=
    ghostLeadingBadY_components_ne_zero (lowerTruncationX D k) hBne
  exact ⟨w, hwU, hwoff, htop, hcontent, hderiv⟩

end Bottcher

namespace Bottcher

/-- Any member of the GhostLeading stratum set is at most the selected maximum stratum. -/
theorem le_ghostLeadingStratum_of_mem
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k j : ℕ}
    (hk : ghostLeadingStratum D = some k) (hj : j ∈ ghostStratumSet D) :
    j ≤ k := by
  by_cases h : (ghostStratumSet D).Nonempty
  · simp [ghostLeadingStratum, h] at hk
    rw [← hk]
    exact Finset.le_max' (ghostStratumSet D) j hj
  · exact False.elim (h ⟨j, hj⟩)

/-- Above the selected GhostLeading stratum, primitive `Y`-derivative guards vanish. -/
theorem coeffYDerivGuard_eq_zero_of_ghostLeadingStratum_some_of_lt
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k j : ℕ}
    (hk : ghostLeadingStratum D = some k) (hj : j ∈ D.support) (hkj : k < j) :
    coeffYDerivGuard D j = 0 := by
  by_contra hne
  have hjghost : j ∈ ghostStratumSet D := (mem_ghostStratumSet_iff D j).mpr ⟨hj, hne⟩
  have hjle : j ≤ k := le_ghostLeadingStratum_of_mem hk hjghost
  exact not_le_of_gt hkj hjle

/-- Every support coefficient above the selected GhostLeading stratum is `Y`-constant. -/
theorem coeff_isYConstant_of_ghostLeadingStratum_some_of_lt
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k j : ℕ}
    (hk : ghostLeadingStratum D = some k) (hj : j ∈ D.support) (hkj : k < j) :
    IsYConstant (D.coeff j) := by
  have hderiv : coeffYDerivGuard D j = 0 :=
    coeffYDerivGuard_eq_zero_of_ghostLeadingStratum_some_of_lt hk hj hkj
  have hprim : IsYConstant (coeffYPrim D j) := isYConstant_of_derivative_eq_zero hderiv
  exact coeff_isYConstant_of_coeffYPrim_isYConstant D j hprim

end Bottcher

namespace Bottcher

/-- The high `X`-tail of a fibre polynomial above degree `k`. -/
noncomputable def highTailX (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) :
    Polynomial (Polynomial (Polynomial ℂ)) :=
  ∑ i ∈ D.support.filter (fun j => k < j), Polynomial.monomial i (D.coeff i)

/-- Coefficients of the high `X`-tail. -/
theorem highTailX_coeff (D : Polynomial (Polynomial (Polynomial ℂ))) (k i : ℕ) :
    (highTailX D k).coeff i =
      if i ∈ D.support.filter (fun j => k < j) then D.coeff i else 0 := by
  rw [highTailX, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (D.support.filter (fun j => k < j)) i (fun i => D.coeff i)]

/-- A coefficient above `k` is unchanged in the high tail. -/
theorem highTailX_coeff_of_mem
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k i : ℕ}
    (hi : i ∈ D.support) (hki : k < i) :
    (highTailX D k).coeff i = D.coeff i := by
  rw [highTailX_coeff, if_pos]
  exact Finset.mem_filter.mpr ⟨hi, hki⟩

/-- The high tail has zero coefficients at degrees `≤ k`. -/
theorem highTailX_coeff_eq_zero_of_le
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k i : ℕ} (hik : i ≤ k) :
    (highTailX D k).coeff i = 0 := by
  rw [highTailX_coeff, if_neg]
  intro hi
  exact not_lt_of_ge hik (Finset.mem_filter.mp hi).2

/-- Split a fibre polynomial into its lower truncation and high tail. -/
theorem lowerTruncationX_add_highTailX_eq
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) :
    lowerTruncationX D k + highTailX D k = D := by
  ext i
  rw [Polynomial.coeff_add]
  by_cases hi : i ∈ D.support
  · rcases le_or_gt i k with hik | hki
    · rw [lowerTruncationX_coeff_of_mem hi hik, highTailX_coeff_eq_zero_of_le D hik, add_zero]
    · rw [lowerTruncationX_coeff_eq_zero_of_lt D hki, highTailX_coeff_of_mem hi hki, zero_add]
  · have hcoeffD : D.coeff i = 0 := by
      by_contra hne
      exact hi (Polynomial.mem_support_iff.mpr hne)
    have hlow : (lowerTruncationX D k).coeff i = 0 := by
      rw [lowerTruncationX_coeff, if_neg]
      intro hif
      exact hi (Finset.mem_filter.mp hif).1
    have hhigh : (highTailX D k).coeff i = 0 := by
      rw [highTailX_coeff, if_neg]
      intro hif
      exact hi (Finset.mem_filter.mp hif).1
    rw [hlow, hhigh, hcoeffD, add_zero]

end Bottcher

namespace Bottcher

/-- Chosen `C[z]` coefficient for a high-tail support coefficient above the selected GhostLeading
stratum. -/
noncomputable def highTailCoeffOf
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k : ℕ} (hk : ghostLeadingStratum D = some k)
    (i : ℕ) : Polynomial ℂ :=
  if hi : i ∈ D.support ∧ k < i then
    Classical.choose (coeff_isYConstant_of_ghostLeadingStratum_some_of_lt hk hi.1 hi.2)
  else 0

/-- Rebuild a high-tail coefficient from its chosen `C[z]` witness. -/
theorem coeff_eq_C_highTailCoeffOf
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k i : ℕ}
    (hk : ghostLeadingStratum D = some k) (hi : i ∈ D.support) (hki : k < i) :
    D.coeff i = Polynomial.C (highTailCoeffOf D hk i) := by
  dsimp [highTailCoeffOf]
  rw [dif_pos ⟨hi, hki⟩]
  exact Classical.choose_spec (coeff_isYConstant_of_ghostLeadingStratum_some_of_lt hk hi hki)

/-- The collapsed `C[z][X]` polynomial corresponding to the high tail above the selected stratum. -/
noncomputable def highTailCollapseX
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k : ℕ} (hk : ghostLeadingStratum D = some k) :
    Polynomial (Polynomial ℂ) :=
  ∑ i ∈ D.support.filter (fun j => k < j), Polynomial.monomial i (highTailCoeffOf D hk i)

/-- Coefficients of the collapsed high-tail polynomial. -/
theorem highTailCollapseX_coeff
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k : ℕ} (hk : ghostLeadingStratum D = some k)
    (i : ℕ) :
    (highTailCollapseX D hk).coeff i =
      if i ∈ D.support.filter (fun j => k < j) then highTailCoeffOf D hk i else 0 := by
  rw [highTailCollapseX, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (D.support.filter (fun j => k < j)) i (fun i => highTailCoeffOf D hk i)]

/-- The high tail is exactly the lift of its collapsed `C[z][X]` version. -/
theorem highTailX_eq_map_C_highTailCollapseX
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k : ℕ} (hk : ghostLeadingStratum D = some k) :
    highTailX D k = (highTailCollapseX D hk).map Polynomial.C := by
  apply Polynomial.ext
  intro i
  rw [highTailX_coeff, Polynomial.coeff_map, highTailCollapseX_coeff]
  by_cases hi : i ∈ D.support.filter (fun j => k < j)
  · have hisupp := (Finset.mem_filter.mp hi).1
    have hki := (Finset.mem_filter.mp hi).2
    rw [if_pos hi, if_pos hi]
    exact coeff_eq_C_highTailCoeffOf D hk hisupp hki
  · rw [if_neg hi, if_neg hi, map_zero]

end Bottcher

namespace Bottcher

/-- Evaluating the high `X`-tail is independent of `Y`: it is the collapsed `C[z][X]` high tail
evaluated at `X = x`. -/
theorem eval_highTailX_eq_highTailCollapseX
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k : ℕ} (hk : ghostLeadingStratum D = some k)
    (z y x : ℂ) :
    (highTailX D k).eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y) x =
      (highTailCollapseX D hk).eval₂ (Polynomial.evalRingHom z) x := by
  rw [highTailX, highTailCollapseX, Polynomial.eval₂_finsetSum, Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  have hisupp := (Finset.mem_filter.mp hi).1
  have hki := (Finset.mem_filter.mp hi).2
  rw [Polynomial.eval₂_monomial, Polynomial.eval₂_monomial, coeff_eq_C_highTailCoeffOf D hk hisupp hki]
  simp

/-- Evaluation form of the lower/high-tail decomposition. -/
theorem eval_lowerTruncation_add_highTailCollapse_eq_eval_D
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k : ℕ} (hk : ghostLeadingStratum D = some k)
    (z y x : ℂ) :
    (lowerTruncationX D k).eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y) x +
        (highTailCollapseX D hk).eval₂ (Polynomial.evalRingHom z) x =
      D.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y) x := by
  rw [← eval_highTailX_eq_highTailCollapseX D hk z y x]
  rw [← Polynomial.eval₂_add]
  rw [lowerTruncationX_add_highTailX_eq]

/-- If `D` vanishes after specialization, the lower truncation equals the negative collapsed high tail. -/
theorem eval_lowerTruncation_eq_neg_highTailCollapse_of_eval_D_eq_zero
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k : ℕ} (hk : ghostLeadingStratum D = some k)
    {z y x : ℂ}
    (hzero : D.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y) x = 0) :
    (lowerTruncationX D k).eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y) x =
      - (highTailCollapseX D hk).eval₂ (Polynomial.evalRingHom z) x := by
  have h := eval_lowerTruncation_add_highTailCollapse_eq_eval_D D hk z y x
  rw [hzero] at h
  exact eq_neg_of_add_eq_zero_left h

end Bottcher

namespace Bottcher

/-- A `Y`-constant polynomial has zero `Y`-derivative. -/
theorem derivative_eq_zero_of_isYConstant {q : Polynomial (Polynomial ℂ)} (hq : IsYConstant q) :
    q.derivative = 0 := by
  obtain ⟨a, rfl⟩ := hq
  exact Polynomial.derivative_C

/-- Coefficientwise `Y`-derivative over a chosen finite `X`-support. -/
noncomputable def yDerivOnXSupport
    (D : Polynomial (Polynomial (Polynomial ℂ))) (s : Finset ℕ) :
    Polynomial (Polynomial (Polynomial ℂ)) :=
  ∑ i ∈ s, Polynomial.monomial i ((D.coeff i).derivative)

/-- Coefficients of the finite-support coefficientwise `Y`-derivative. -/
theorem yDerivOnXSupport_coeff
    (D : Polynomial (Polynomial (Polynomial ℂ))) (s : Finset ℕ) (i : ℕ) :
    (yDerivOnXSupport D s).coeff i = if i ∈ s then (D.coeff i).derivative else 0 := by
  rw [yDerivOnXSupport, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' s i (fun i => (D.coeff i).derivative)]

/-- Coefficientwise `Y`-derivative of the lower truncation. -/
noncomputable def yDerivLowerTruncationX
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) :
    Polynomial (Polynomial (Polynomial ℂ)) :=
  yDerivOnXSupport D (D.support.filter (fun j => j ≤ k))

/-- Coefficientwise `Y`-derivative of the high tail. -/
noncomputable def yDerivHighTailX
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) :
    Polynomial (Polynomial (Polynomial ℂ)) :=
  yDerivOnXSupport D (D.support.filter (fun j => k < j))

/-- Coefficients of the high-tail coefficientwise `Y`-derivative. -/
theorem yDerivHighTailX_coeff
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k i : ℕ) :
    (yDerivHighTailX D k).coeff i =
      if i ∈ D.support.filter (fun j => k < j) then (D.coeff i).derivative else 0 := by
  simp [yDerivHighTailX, yDerivOnXSupport_coeff]

/-- The high tail above the selected GhostLeading stratum has zero coefficientwise `Y`-derivative. -/
theorem yDerivHighTailX_eq_zero_of_ghostLeadingStratum
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ}
    (hk : ghostLeadingStratum D = some k) :
    yDerivHighTailX D k = 0 := by
  apply Polynomial.ext
  intro i
  rw [yDerivHighTailX_coeff, Polynomial.coeff_zero]
  by_cases hi : i ∈ D.support.filter (fun j => k < j)
  · rw [if_pos hi]
    have hisupp := (Finset.mem_filter.mp hi).1
    have hki := (Finset.mem_filter.mp hi).2
    exact derivative_eq_zero_of_isYConstant
      (coeff_isYConstant_of_ghostLeadingStratum_some_of_lt hk hisupp hki)
  · rw [if_neg hi]

end Bottcher

namespace Bottcher

/-- At the selected GhostLeading stratum, the actual `Y`-derivative of the coefficient is nonzero. -/
theorem coeff_derivative_ne_zero_of_ghostLeadingStratum
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ}
    (hk : ghostLeadingStratum D = some k) :
    (D.coeff k).derivative ≠ 0 := by
  have hksupp : k ∈ D.support := ghostLeadingStratum_support hk
  have hcoeff0 : D.coeff k ≠ 0 := Polynomial.mem_support_iff.mp hksupp
  have hcontent0 : (D.coeff k).content ≠ 0 := by
    intro hzero
    exact hcoeff0 (Polynomial.content_eq_zero_iff.mp hzero)
  have hcontentC0 : Polynomial.C (D.coeff k).content ≠ (0 : Polynomial (Polynomial ℂ)) :=
    Polynomial.C_ne_zero.mpr hcontent0
  have hprimderiv0 : (D.coeff k).primPart.derivative ≠ 0 := by
    simpa [coeffYDerivGuard, coeffYPrim] using ghostLeadingStratum_derivGuard_ne_zero hk
  have hderivEq : (D.coeff k).derivative =
      Polynomial.C (D.coeff k).content * (D.coeff k).primPart.derivative := by
    calc
      (D.coeff k).derivative
          = (Polynomial.C (D.coeff k).content * (D.coeff k).primPart).derivative := by
              rw [← Polynomial.eq_C_content_mul_primPart (D.coeff k)]
      _ = Polynomial.C (D.coeff k).content * (D.coeff k).primPart.derivative := by
              rw [Polynomial.derivative_C_mul]
  rw [hderivEq]
  exact mul_ne_zero hcontentC0 hprimderiv0

/-- Coefficients of the lower-truncation coefficientwise `Y`-derivative. -/
theorem yDerivLowerTruncationX_coeff
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k i : ℕ) :
    (yDerivLowerTruncationX D k).coeff i =
      if i ∈ D.support.filter (fun j => j ≤ k) then (D.coeff i).derivative else 0 := by
  simp [yDerivLowerTruncationX, yDerivOnXSupport_coeff]

/-- Coefficients above `k` vanish in the lower-truncation `Y`-derivative. -/
theorem yDerivLowerTruncationX_coeff_eq_zero_of_lt
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k i : ℕ} (hki : k < i) :
    (yDerivLowerTruncationX D k).coeff i = 0 := by
  rw [yDerivLowerTruncationX_coeff, if_neg]
  intro hi
  exact not_le_of_gt hki (Finset.mem_filter.mp hi).2

/-- The lower-truncation `Y`-derivative has `X`-degree at most `k`. -/
theorem yDerivLowerTruncationX_natDegree_le
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) :
    (yDerivLowerTruncationX D k).natDegree ≤ k := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro i hki
  exact yDerivLowerTruncationX_coeff_eq_zero_of_lt D hki

/-- The lower-truncation `Y`-derivative preserves the selected top `X` degree. -/
theorem yDerivLowerTruncationX_natDegree_eq_of_ghostLeadingStratum
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ}
    (hk : ghostLeadingStratum D = some k) :
    (yDerivLowerTruncationX D k).natDegree = k := by
  apply le_antisymm
  · exact yDerivLowerTruncationX_natDegree_le D k
  · have hksupp : k ∈ D.support := ghostLeadingStratum_support hk
    have hcoeff : (yDerivLowerTruncationX D k).coeff k ≠ 0 := by
      rw [yDerivLowerTruncationX_coeff]
      simpa [hksupp] using coeff_derivative_ne_zero_of_ghostLeadingStratum hk
    exact Polynomial.le_natDegree_of_ne_zero hcoeff

end Bottcher

namespace Bottcher

/-- The collapsed high tail has zero coefficients at degrees `≤ k`. -/
theorem highTailCollapseX_coeff_eq_zero_of_le
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k i : ℕ}
    (hk : ghostLeadingStratum D = some k) (hik : i ≤ k) :
    (highTailCollapseX D hk).coeff i = 0 := by
  rw [highTailCollapseX_coeff, if_neg]
  intro hi
  exact not_lt_of_ge hik (Finset.mem_filter.mp hi).2

/-- Coefficients above `k` are retained in the collapsed high tail. -/
theorem highTailCollapseX_coeff_of_mem
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k i : ℕ}
    (hk : ghostLeadingStratum D = some k) (hi : i ∈ D.support) (hki : k < i) :
    (highTailCollapseX D hk).coeff i = highTailCoeffOf D hk i := by
  rw [highTailCollapseX_coeff, if_pos]
  exact Finset.mem_filter.mpr ⟨hi, hki⟩

/-- Chosen collapsed high-tail coefficients are nonzero on actual high support. -/
theorem highTailCoeffOf_ne_zero_of_mem
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k i : ℕ}
    (hk : ghostLeadingStratum D = some k) (hi : i ∈ D.support) (hki : k < i) :
    highTailCoeffOf D hk i ≠ 0 := by
  have hcoeff : D.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  have hC := coeff_eq_C_highTailCoeffOf D hk hi hki
  intro hzero
  exact hcoeff (by rw [hC, hzero, Polynomial.C_0])

/-- If there is support above `k`, the collapsed high tail is nonzero. -/
theorem highTailCollapseX_ne_zero_of_support_above
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k i : ℕ}
    (hk : ghostLeadingStratum D = some k) (hi : i ∈ D.support) (hki : k < i) :
    highTailCollapseX D hk ≠ 0 := by
  have hcoeff : (highTailCollapseX D hk).coeff i ≠ 0 := by
    rw [highTailCollapseX_coeff_of_mem D hk hi hki]
    exact highTailCoeffOf_ne_zero_of_mem D hk hi hki
  intro hzero
  exact hcoeff (by rw [hzero, Polynomial.coeff_zero])

/-- Any actual high-tail support forces the collapsed high tail to have degree above `k`. -/
theorem lt_natDegree_highTailCollapseX_of_support_above
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k i : ℕ}
    (hk : ghostLeadingStratum D = some k) (hi : i ∈ D.support) (hki : k < i) :
    k < (highTailCollapseX D hk).natDegree := by
  have hcoeff : (highTailCollapseX D hk).coeff i ≠ 0 := by
    rw [highTailCollapseX_coeff_of_mem D hk hi hki]
    exact highTailCoeffOf_ne_zero_of_mem D hk hi hki
  exact lt_of_lt_of_le hki (Polynomial.le_natDegree_of_ne_zero hcoeff)

end Bottcher

namespace Bottcher

/-- Evaluation of the lower `X`-truncation as a sparse sum. -/
theorem eval_lowerTruncationX
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) (z y x : ℂ) :
    (lowerTruncationX D k).eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y) x =
      ∑ i ∈ D.support.filter (fun j => j ≤ k),
        (D.coeff i).eval₂ (Polynomial.evalRingHom z) y * x ^ i := by
  rw [lowerTruncationX, Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Polynomial.eval₂_monomial]
  rfl

/-- If `D` vanishes at two `Y`-values with the same `z,x`, then the lower truncation has equal
values at those two `Y`-values; the `C[z][X]` high tail cancels. -/
theorem eval_lowerTruncationX_eq_of_two_eval_D_eq_zero
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k : ℕ} (hk : ghostLeadingStratum D = some k)
    {z y₁ y₂ x : ℂ}
    (hzero₁ : D.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₁) x = 0)
    (hzero₂ : D.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) x = 0) :
    (lowerTruncationX D k).eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₁) x =
      (lowerTruncationX D k).eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) x := by
  rw [eval_lowerTruncation_eq_neg_highTailCollapse_of_eval_D_eq_zero D hk hzero₁,
    eval_lowerTruncation_eq_neg_highTailCollapse_of_eval_D_eq_zero D hk hzero₂]

/-- Finite-difference form of the two-branch cancellation: the lower part gives a relation after
subtracting the two `Y`-specializations. -/
theorem lowerTruncationX_finiteDifference_eq_zero_of_two_eval_D_eq_zero
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k : ℕ} (hk : ghostLeadingStratum D = some k)
    {z y₁ y₂ x : ℂ}
    (hzero₁ : D.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₁) x = 0)
    (hzero₂ : D.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) x = 0) :
    ∑ i ∈ D.support.filter (fun j => j ≤ k),
      ((D.coeff i).eval₂ (Polynomial.evalRingHom z) y₁ -
        (D.coeff i).eval₂ (Polynomial.evalRingHom z) y₂) * x ^ i = 0 := by
  have heq := eval_lowerTruncationX_eq_of_two_eval_D_eq_zero D hk hzero₁ hzero₂
  rw [eval_lowerTruncationX, eval_lowerTruncationX] at heq
  have hsub :
      (∑ i ∈ D.support.filter (fun j => j ≤ k),
        (D.coeff i).eval₂ (Polynomial.evalRingHom z) y₁ * x ^ i) -
      (∑ i ∈ D.support.filter (fun j => j ≤ k),
        (D.coeff i).eval₂ (Polynomial.evalRingHom z) y₂ * x ^ i) = 0 :=
    sub_eq_zero.mpr heq
  rw [← Finset.sum_sub_distrib] at hsub
  convert hsub using 2
  ring

end Bottcher

namespace Bottcher

/-- The evaluated quotient `(q(Y)-q(y₂))/(Y-y₂)` at `Y=y₁`, after first evaluating the
`ℂ[z]` coefficients at `z`. This is the first divided-difference object in the GhostLeading descent. -/
noncomputable def coeffEvalDividedDiff
    (q : Polynomial (Polynomial ℂ)) (z y₁ y₂ : ℂ) : ℂ :=
  (Classical.choose
    (Polynomial.X_sub_C_dvd_sub_C_eval
      (p := q.map (Polynomial.evalRingHom z)) (a := y₂))).eval y₁

/-- Coefficient-level divided-difference factorization: `q(z,y₁)-q(z,y₂)` is divisible by
`y₁-y₂`. -/
theorem coeff_eval_sub_eval_eq_sub_mul_dividedDiff
    (q : Polynomial (Polynomial ℂ)) (z y₁ y₂ : ℂ) :
    q.eval₂ (Polynomial.evalRingHom z) y₁ - q.eval₂ (Polynomial.evalRingHom z) y₂ =
      (y₁ - y₂) * coeffEvalDividedDiff q z y₁ y₂ := by
  let p : Polynomial ℂ := q.map (Polynomial.evalRingHom z)
  let Q : Polynomial ℂ := Classical.choose
    (Polynomial.X_sub_C_dvd_sub_C_eval (p := p) (a := y₂))
  have hQ : p - Polynomial.C (p.eval y₂) = (Polynomial.X - Polynomial.C y₂) * Q :=
    Classical.choose_spec (Polynomial.X_sub_C_dvd_sub_C_eval (p := p) (a := y₂))
  have heval := congrArg (fun r : Polynomial ℂ => r.eval y₁) hQ
  change Polynomial.eval y₁ (p - Polynomial.C (Polynomial.eval y₂ p)) =
    Polynomial.eval y₁ ((Polynomial.X - Polynomial.C y₂) * Q) at heval
  rw [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C] at heval
  change p.eval y₁ - p.eval y₂ = (y₁ - y₂) * Q.eval y₁ at heval
  rw [show p.eval y₁ = q.eval₂ (Polynomial.evalRingHom z) y₁ by
        simp [p, Polynomial.eval_map],
      show p.eval y₂ = q.eval₂ (Polynomial.evalRingHom z) y₂ by
        simp [p, Polynomial.eval_map]] at heval
  simpa [coeffEvalDividedDiff, p, Q] using heval

/-- Dividing Grok's two-branch finite-difference cancellation by the nonzero branch separation
`y₁-y₂` gives the new divided-difference relation. -/
theorem lowerTruncationX_dividedDifference_eq_zero_of_two_eval_D_eq_zero
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k : ℕ} (hk : ghostLeadingStratum D = some k)
    {z y₁ y₂ x : ℂ} (hy : y₁ ≠ y₂)
    (hzero₁ : D.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₁) x = 0)
    (hzero₂ : D.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) x = 0) :
    ∑ i ∈ D.support.filter (fun j => j ≤ k),
      coeffEvalDividedDiff (D.coeff i) z y₁ y₂ * x ^ i = 0 := by
  have hfd := lowerTruncationX_finiteDifference_eq_zero_of_two_eval_D_eq_zero D hk hzero₁ hzero₂
  have hfactor :
      ∑ i ∈ D.support.filter (fun j => j ≤ k),
        ((y₁ - y₂) * coeffEvalDividedDiff (D.coeff i) z y₁ y₂) * x ^ i = 0 := by
    rw [← hfd]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [coeff_eval_sub_eval_eq_sub_mul_dividedDiff]
  have hmul :
      (y₁ - y₂) * (∑ i ∈ D.support.filter (fun j => j ≤ k),
        coeffEvalDividedDiff (D.coeff i) z y₁ y₂ * x ^ i) = 0 := by
    rw [Finset.mul_sum]
    rw [← hfactor]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hnon : y₁ - y₂ ≠ 0 := sub_ne_zero.mpr hy
  have hcancel :
      (y₁ - y₂) * (∑ i ∈ D.support.filter (fun j => j ≤ k),
        coeffEvalDividedDiff (D.coeff i) z y₁ y₂ * x ^ i) = (y₁ - y₂) * 0 := by
    simpa using hmul
  exact mul_left_cancel₀ hnon hcancel

end Bottcher

namespace Bottcher

/-- The `X`-polynomial produced by dividing the lower finite-difference relation by `y₁-y₂`. -/
noncomputable def dividedDifferenceRelationX
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) (z y₁ y₂ : ℂ) : Polynomial ℂ :=
  ∑ i ∈ D.support.filter (fun j => j ≤ k),
    Polynomial.monomial i (coeffEvalDividedDiff (D.coeff i) z y₁ y₂)

/-- Coefficients of the divided-difference `X`-relation. -/
theorem dividedDifferenceRelationX_coeff
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) (z y₁ y₂ : ℂ) (i : ℕ) :
    (dividedDifferenceRelationX D k z y₁ y₂).coeff i =
      if i ∈ D.support.filter (fun j => j ≤ k)
      then coeffEvalDividedDiff (D.coeff i) z y₁ y₂ else 0 := by
  rw [dividedDifferenceRelationX, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases hi : i ∈ D.support.filter (fun j => j ≤ k)
  · rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j hj hji
      simp [hji]
    · intro hnot
      exact (hnot hi).elim
  · rw [if_neg hi]
    exact Finset.sum_eq_zero fun j hj => by
      rw [if_neg]
      intro hji
      exact hi (hji ▸ hj)

/-- The divided-difference relation has `X`-degree at most the selected stratum `k`. -/
theorem dividedDifferenceRelationX_natDegree_le
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) (z y₁ y₂ : ℂ) :
    (dividedDifferenceRelationX D k z y₁ y₂).natDegree ≤ k := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro i hki
  rw [dividedDifferenceRelationX_coeff, if_neg]
  intro hi
  exact not_le_of_gt hki (Finset.mem_filter.mp hi).2

/-- Evaluation of the divided-difference `X`-relation as the expected finite sum. -/
theorem eval_dividedDifferenceRelationX
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) (z y₁ y₂ x : ℂ) :
    (dividedDifferenceRelationX D k z y₁ y₂).eval x =
      ∑ i ∈ D.support.filter (fun j => j ≤ k),
        coeffEvalDividedDiff (D.coeff i) z y₁ y₂ * x ^ i := by
  rw [dividedDifferenceRelationX, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Polynomial.eval_monomial]

/-- The two-branch cancellation gives a genuine scalar polynomial relation in `x` after division by
`y₁-y₂`. -/
theorem eval_dividedDifferenceRelationX_eq_zero_of_two_eval_D_eq_zero
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k : ℕ} (hk : ghostLeadingStratum D = some k)
    {z y₁ y₂ x : ℂ} (hy : y₁ ≠ y₂)
    (hzero₁ : D.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₁) x = 0)
    (hzero₂ : D.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) x = 0) :
    (dividedDifferenceRelationX D k z y₁ y₂).eval x = 0 := by
  rw [eval_dividedDifferenceRelationX]
  exact lowerTruncationX_dividedDifference_eq_zero_of_two_eval_D_eq_zero D hk hy hzero₁ hzero₂

end Bottcher

namespace Bottcher

/-- Symbolic divided difference of a `C[z][Y]` coefficient, represented as a polynomial in `Y₁`
with coefficients in `C[z][Y₂]`. -/
noncomputable def symCoeffDividedDiff (q : Polynomial (Polynomial ℂ)) :
    Polynomial (Polynomial (Polynomial ℂ)) :=
  Classical.choose
    (Polynomial.X_sub_C_dvd_sub_C_eval
      (p := q.map (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)))
      (a := (Polynomial.X : Polynomial (Polynomial ℂ))))

/-- Evaluation factorization for the symbolic coefficient divided difference. -/
theorem coeff_eval_sub_eval_eq_sub_mul_symCoeffDividedDiff_eval
    (q : Polynomial (Polynomial ℂ)) (z y₁ y₂ : ℂ) :
    q.eval₂ (Polynomial.evalRingHom z) y₁ - q.eval₂ (Polynomial.evalRingHom z) y₂ =
      (y₁ - y₂) *
        (symCoeffDividedDiff q).eval₂
          (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) y₁ := by
  let R : Type := Polynomial (Polynomial ℂ)
  let cHom : Polynomial ℂ →+* R := Polynomial.C
  let p : Polynomial R := q.map cHom
  let Q : Polynomial R := symCoeffDividedDiff q
  have hQ : p - Polynomial.C (p.eval (Polynomial.X : R)) =
      (Polynomial.X - Polynomial.C (Polynomial.X : R)) * Q :=
    Classical.choose_spec
      (Polynomial.X_sub_C_dvd_sub_C_eval
        (p := q.map (Polynomial.C : Polynomial ℂ →+* R))
        (a := (Polynomial.X : R)))
  let f : R →+* ℂ := Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂
  have hfC : f.comp cHom = Polynomial.evalRingHom z := by
    ext a
    · change Polynomial.eval₂ (Polynomial.evalRingHom z) y₂ (Polynomial.C (Polynomial.C a)) =
        (Polynomial.evalRingHom z) (Polynomial.C a)
      rw [Polynomial.eval₂_C]
    · change Polynomial.eval₂ (Polynomial.evalRingHom z) y₂ (Polynomial.C Polynomial.X) =
        (Polynomial.evalRingHom z) Polynomial.X
      rw [Polynomial.eval₂_C]
  have hfX : f (Polynomial.X : R) = y₂ := by
    change Polynomial.eval₂ (Polynomial.evalRingHom z) y₂ (Polynomial.X : Polynomial (Polynomial ℂ)) = y₂
    rw [Polynomial.eval₂_X]
  have heval := congrArg (fun r : Polynomial R => r.eval₂ f y₁) hQ
  change Polynomial.eval₂ f y₁ (p - Polynomial.C (Polynomial.eval (Polynomial.X : R) p)) =
    Polynomial.eval₂ f y₁ ((Polynomial.X - Polynomial.C (Polynomial.X : R)) * Q) at heval
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, Polynomial.eval₂_mul, Polynomial.eval₂_sub,
    Polynomial.eval₂_X, Polynomial.eval₂_C] at heval
  have hp_y₁ : Polynomial.eval₂ f y₁ p = q.eval₂ (Polynomial.evalRingHom z) y₁ := by
    change Polynomial.eval₂ f y₁ (q.map cHom) = q.eval₂ (Polynomial.evalRingHom z) y₁
    rw [Polynomial.eval₂_map, hfC]
  have hp_evalX : Polynomial.eval (Polynomial.X : R) p = q := by
    change Polynomial.eval (Polynomial.X : R) (q.map cHom) = q
    rw [Polynomial.eval_map]
    change Polynomial.eval₂ cHom (Polynomial.X : R) q = q
    rw [show cHom = (Polynomial.C : Polynomial ℂ →+* R) from rfl]
    rw [Polynomial.eval₂_C_X]
  have hp_y₂ : f (Polynomial.eval (Polynomial.X : R) p) = q.eval₂ (Polynomial.evalRingHom z) y₂ := by
    rw [hp_evalX]
    rfl
  rw [hp_y₁, hp_y₂, hfX] at heval
  simpa [Q, symCoeffDividedDiff, f] using heval

/-- The symbolic divided-difference `X`-relation over the bivariate coefficient ring
`C[z][Y₂][Y₁]`. -/
noncomputable def symDividedDifferenceRelationX
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) :
    Polynomial (Polynomial (Polynomial (Polynomial ℂ))) :=
  ∑ i ∈ D.support.filter (fun j => j ≤ k),
    Polynomial.monomial i (symCoeffDividedDiff (D.coeff i))

/-- Coefficients of the symbolic divided-difference `X`-relation. -/
theorem symDividedDifferenceRelationX_coeff
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k i : ℕ) :
    (symDividedDifferenceRelationX D k).coeff i =
      if i ∈ D.support.filter (fun j => j ≤ k)
      then symCoeffDividedDiff (D.coeff i) else 0 := by
  rw [symDividedDifferenceRelationX, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases hi : i ∈ D.support.filter (fun j => j ≤ k)
  · rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j hj hji
      simp [hji]
    · intro hnot
      exact (hnot hi).elim
  · rw [if_neg hi]
    exact Finset.sum_eq_zero fun j hj => by
      rw [if_neg]
      intro hji
      exact hi (hji ▸ hj)

/-- The symbolic divided-difference relation has `X`-degree at most `k`. -/
theorem symDividedDifferenceRelationX_natDegree_le
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) :
    (symDividedDifferenceRelationX D k).natDegree ≤ k := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro i hki
  rw [symDividedDifferenceRelationX_coeff, if_neg]
  intro hi
  exact not_le_of_gt hki (Finset.mem_filter.mp hi).2

/-- Evaluation of the symbolic divided-difference relation. -/
theorem eval_symDividedDifferenceRelationX
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) (z y₁ y₂ x : ℂ) :
    (symDividedDifferenceRelationX D k).eval₂
        (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) y₁) x =
      ∑ i ∈ D.support.filter (fun j => j ≤ k),
        (symCoeffDividedDiff (D.coeff i)).eval₂
          (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) y₁ * x ^ i := by
  rw [symDividedDifferenceRelationX, Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Polynomial.eval₂_monomial]
  change Polynomial.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) y₁
      (symCoeffDividedDiff (D.coeff i)) * x ^ i =
    Polynomial.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) y₁
      (symCoeffDividedDiff (D.coeff i)) * x ^ i
  rfl

/-- The symbolic bivariate divided-difference relation evaluates to zero at any distinct two-branch
pair where the original relation vanishes at both branches. -/
theorem eval_symDividedDifferenceRelationX_eq_zero_of_two_eval_D_eq_zero
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k : ℕ} (hk : ghostLeadingStratum D = some k)
    {z y₁ y₂ x : ℂ} (hy : y₁ ≠ y₂)
    (hzero₁ : D.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₁) x = 0)
    (hzero₂ : D.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) x = 0) :
    (symDividedDifferenceRelationX D k).eval₂
        (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) y₁) x = 0 := by
  rw [eval_symDividedDifferenceRelationX]
  have hfd := lowerTruncationX_finiteDifference_eq_zero_of_two_eval_D_eq_zero D hk hzero₁ hzero₂
  have hfactor :
      ∑ i ∈ D.support.filter (fun j => j ≤ k),
        ((y₁ - y₂) *
          (symCoeffDividedDiff (D.coeff i)).eval₂
            (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) y₁) * x ^ i = 0 := by
    rw [← hfd]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [coeff_eval_sub_eval_eq_sub_mul_symCoeffDividedDiff_eval]
  have hmul :
      (y₁ - y₂) * (∑ i ∈ D.support.filter (fun j => j ≤ k),
        (symCoeffDividedDiff (D.coeff i)).eval₂
          (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) y₁ * x ^ i) = 0 := by
    rw [Finset.mul_sum]
    rw [← hfactor]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hnon : y₁ - y₂ ≠ 0 := sub_ne_zero.mpr hy
  have hcancel :
      (y₁ - y₂) * (∑ i ∈ D.support.filter (fun j => j ≤ k),
        (symCoeffDividedDiff (D.coeff i)).eval₂
          (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) y₁ * x ^ i) = (y₁ - y₂) * 0 := by
    simpa using hmul
  exact mul_left_cancel₀ hnon hcancel

end Bottcher

namespace Bottcher

/-- Canonical symbolic divided difference using `divByMonic`, suited for coefficient/degree descent. -/
noncomputable def symCoeffDividedDiffM (q : Polynomial (Polynomial ℂ)) :
    Polynomial (Polynomial (Polynomial ℂ)) :=
  ((q.map (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ))) - Polynomial.C q) /ₘ
    (Polynomial.X - Polynomial.C (Polynomial.X : Polynomial (Polynomial ℂ)))

/-- Evaluation factorization for the canonical symbolic divided difference. -/
theorem coeff_eval_sub_eval_eq_sub_mul_symCoeffDividedDiffM_eval
    (q : Polynomial (Polynomial ℂ)) (z y₁ y₂ : ℂ) :
    q.eval₂ (Polynomial.evalRingHom z) y₁ - q.eval₂ (Polynomial.evalRingHom z) y₂ =
      (y₁ - y₂) *
        (symCoeffDividedDiffM q).eval₂
          (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) y₁ := by
  let R : Type := Polynomial (Polynomial ℂ)
  let cHom : Polynomial ℂ →+* R := Polynomial.C
  let p : Polynomial R := q.map cHom
  let N : Polynomial R := p - Polynomial.C q
  let Q : Polynomial R := symCoeffDividedDiffM q
  have hp_evalX : Polynomial.eval (Polynomial.X : R) p = q := by
    change Polynomial.eval (Polynomial.X : R) (q.map cHom) = q
    rw [Polynomial.eval_map]
    change Polynomial.eval₂ cHom (Polynomial.X : R) q = q
    rw [show cHom = (Polynomial.C : Polynomial ℂ →+* R) from rfl]
    rw [Polynomial.eval₂_C_X]
  have hroot : Polynomial.IsRoot N (Polynomial.X : R) := by
    rw [Polynomial.IsRoot.def]
    change Polynomial.eval (Polynomial.X : R) (p - Polynomial.C q) = 0
    rw [Polynomial.eval_sub, hp_evalX, Polynomial.eval_C, sub_self]
  have hmul : (Polynomial.X - Polynomial.C (Polynomial.X : R)) * Q = N := by
    simpa [N, Q, symCoeffDividedDiffM, p]
      using (Polynomial.mul_divByMonic_eq_iff_isRoot (p := N) (a := (Polynomial.X : R))).2 hroot
  let f : R →+* ℂ := Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂
  have hfC : f.comp cHom = Polynomial.evalRingHom z := by
    ext a
    · change Polynomial.eval₂ (Polynomial.evalRingHom z) y₂ (Polynomial.C (Polynomial.C a)) =
        (Polynomial.evalRingHom z) (Polynomial.C a)
      rw [Polynomial.eval₂_C]
    · change Polynomial.eval₂ (Polynomial.evalRingHom z) y₂ (Polynomial.C Polynomial.X) =
        (Polynomial.evalRingHom z) Polynomial.X
      rw [Polynomial.eval₂_C]
  have hfX : f (Polynomial.X : R) = y₂ := by
    change Polynomial.eval₂ (Polynomial.evalRingHom z) y₂ (Polynomial.X : Polynomial (Polynomial ℂ)) = y₂
    rw [Polynomial.eval₂_X]
  have heval := congrArg (fun r : Polynomial R => r.eval₂ f y₁) hmul
  change Polynomial.eval₂ f y₁ ((Polynomial.X - Polynomial.C (Polynomial.X : R)) * Q) =
    Polynomial.eval₂ f y₁ N at heval
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
    Polynomial.eval₂_sub, Polynomial.eval₂_C] at heval
  have hp_y₁ : Polynomial.eval₂ f y₁ p = q.eval₂ (Polynomial.evalRingHom z) y₁ := by
    change Polynomial.eval₂ f y₁ (q.map cHom) = q.eval₂ (Polynomial.evalRingHom z) y₁
    rw [Polynomial.eval₂_map, hfC]
  have hq_y₂ : f q = q.eval₂ (Polynomial.evalRingHom z) y₂ := rfl
  rw [hp_y₁, hq_y₂, hfX] at heval
  simpa [Q, symCoeffDividedDiffM, f, N] using heval.symm

/-- The numerator of the canonical symbolic divided difference has the old `Y` degree. -/
theorem symCoeffDividedDiffM_numerator_natDegree_eq
    {q : Polynomial (Polynomial ℂ)} (hqpos : 0 < q.natDegree) :
    ((q.map (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ))) - Polynomial.C q).natDegree =
      q.natDegree := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · have hmap : (q.map (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ))).natDegree ≤ q.natDegree :=
      Polynomial.natDegree_map_le
    have hC : (Polynomial.C q : Polynomial (Polynomial (Polynomial ℂ))).natDegree ≤ q.natDegree := by
      rw [Polynomial.natDegree_C]
      exact Nat.zero_le _
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le hmap hC)
  · have hq0 : q ≠ 0 := by
      intro hzero
      rw [hzero] at hqpos
      exact (Nat.lt_irrefl 0) hqpos
    have hqcoeff : q.coeff q.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hq0
    have hn0 : q.natDegree ≠ 0 := ne_of_gt hqpos
    rw [Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_C, if_neg hn0]
    simpa using Polynomial.C_ne_zero.mpr hqcoeff

/-- Dividing by `Y₁-Y₂` lowers the outer symbolic `Y₁` degree by one. -/
theorem symCoeffDividedDiffM_natDegree_eq_pred
    {q : Polynomial (Polynomial ℂ)} (hqpos : 0 < q.natDegree) :
    (symCoeffDividedDiffM q).natDegree = q.natDegree - 1 := by
  rw [symCoeffDividedDiffM, Polynomial.natDegree_divByMonic (hg := Polynomial.monic_X_sub_C _)]
  rw [symCoeffDividedDiffM_numerator_natDegree_eq hqpos, Polynomial.natDegree_X_sub_C]

/-- The top `Y₁` coefficient of the canonical symbolic divided difference is the old leading
`Y` coefficient, constant in `Y₂`. -/
theorem symCoeffDividedDiffM_coeff_natDegree_sub_one
    {q : Polynomial (Polynomial ℂ)} (hqpos : 0 < q.natDegree) :
    (symCoeffDividedDiffM q).coeff (q.natDegree - 1) = Polynomial.C (q.coeff q.natDegree) := by
  have hpredsucc : q.natDegree - 1 + 1 = q.natDegree :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hqpos)
  have hn0 : q.natDegree ≠ 0 := ne_of_gt hqpos
  rw [symCoeffDividedDiffM, Polynomial.coeff_divByMonic_X_sub_C]
  rw [symCoeffDividedDiffM_numerator_natDegree_eq hqpos]
  rw [hpredsucc, Finset.Icc_self, Finset.sum_singleton]
  rw [Nat.sub_self, pow_zero, one_mul]
  rw [Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_C, if_neg hn0, sub_zero]

/-- A nonconstant coefficient has nonzero canonical symbolic divided difference. -/
theorem symCoeffDividedDiffM_ne_zero_of_natDegree_pos
    {q : Polynomial (Polynomial ℂ)} (hqpos : 0 < q.natDegree) :
    symCoeffDividedDiffM q ≠ 0 := by
  have hcoeff := symCoeffDividedDiffM_coeff_natDegree_sub_one (q := q) hqpos
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero] at hqpos
    exact (Nat.lt_irrefl 0) hqpos
  have hqcoeff : q.coeff q.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq0
  have hC : Polynomial.C (q.coeff q.natDegree) ≠ (0 : Polynomial (Polynomial ℂ)) :=
    Polynomial.C_ne_zero.mpr hqcoeff
  intro hzero
  apply hC
  rw [← hcoeff, hzero, Polynomial.coeff_zero]

/-- Nonzero derivative forces positive `Y` degree for a `C[z][Y]` coefficient. -/
theorem natDegree_pos_of_derivative_ne_zero {q : Polynomial (Polynomial ℂ)}
    (hderiv : q.derivative ≠ 0) :
    0 < q.natDegree := by
  by_contra hpos
  have hdeg : q.natDegree = 0 := Nat.eq_zero_of_not_pos hpos
  exact hderiv (Polynomial.derivative_of_natDegree_zero hdeg)

/-- The selected GhostLeading coefficient has positive `Y` degree. -/
theorem coeff_natDegree_pos_of_ghostLeadingStratum
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ}
    (hk : ghostLeadingStratum D = some k) :
    0 < (D.coeff k).natDegree :=
  natDegree_pos_of_derivative_ne_zero (coeff_derivative_ne_zero_of_ghostLeadingStratum hk)

/-- At the GhostLeading stratum, the canonical symbolic divided-difference coefficient is nonzero. -/
theorem symCoeffDividedDiffM_coeff_ne_zero_of_ghostLeadingStratum
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ}
    (hk : ghostLeadingStratum D = some k) :
    symCoeffDividedDiffM (D.coeff k) ≠ 0 :=
  symCoeffDividedDiffM_ne_zero_of_natDegree_pos
    (coeff_natDegree_pos_of_ghostLeadingStratum hk)

/-- The canonical symbolic divided-difference `X`-relation over `C[z][Y₂][Y₁]`. -/
noncomputable def symDividedDifferenceRelationXM
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) :
    Polynomial (Polynomial (Polynomial (Polynomial ℂ))) :=
  ∑ i ∈ D.support.filter (fun j => j ≤ k),
    Polynomial.monomial i (symCoeffDividedDiffM (D.coeff i))

/-- Coefficients of the canonical symbolic divided-difference `X`-relation. -/
theorem symDividedDifferenceRelationXM_coeff
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k i : ℕ) :
    (symDividedDifferenceRelationXM D k).coeff i =
      if i ∈ D.support.filter (fun j => j ≤ k)
      then symCoeffDividedDiffM (D.coeff i) else 0 := by
  rw [symDividedDifferenceRelationXM, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases hi : i ∈ D.support.filter (fun j => j ≤ k)
  · rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j hj hji
      simp [hji]
    · intro hnot
      exact (hnot hi).elim
  · rw [if_neg hi]
    exact Finset.sum_eq_zero fun j hj => by
      rw [if_neg]
      intro hji
      exact hi (hji ▸ hj)

/-- The canonical symbolic divided-difference relation has `X`-degree at most `k`. -/
theorem symDividedDifferenceRelationXM_natDegree_le
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) :
    (symDividedDifferenceRelationXM D k).natDegree ≤ k := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro i hki
  rw [symDividedDifferenceRelationXM_coeff, if_neg]
  intro hi
  exact not_le_of_gt hki (Finset.mem_filter.mp hi).2

/-- At a GhostLeading stratum, the canonical symbolic relation still has top `X` degree `k`. -/
theorem symDividedDifferenceRelationXM_natDegree_eq_of_ghostLeadingStratum
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ}
    (hk : ghostLeadingStratum D = some k) :
    (symDividedDifferenceRelationXM D k).natDegree = k := by
  apply le_antisymm
  · exact symDividedDifferenceRelationXM_natDegree_le D k
  · have hksupp : k ∈ D.support := ghostLeadingStratum_support hk
    have hkfilter : k ∈ D.support.filter (fun j => j ≤ k) := Finset.mem_filter.mpr ⟨hksupp, le_rfl⟩
    have hcoeff : (symDividedDifferenceRelationXM D k).coeff k ≠ 0 := by
      rw [symDividedDifferenceRelationXM_coeff, if_pos hkfilter]
      exact symCoeffDividedDiffM_coeff_ne_zero_of_ghostLeadingStratum hk
    exact Polynomial.le_natDegree_of_ne_zero hcoeff

/-- The leading `X` coefficient of the canonical symbolic relation has `Y₁` degree one less than the
old selected GhostLeading coefficient. -/
theorem symDividedDifferenceRelationXM_topCoeff_natDegree_eq_pred
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ}
    (hk : ghostLeadingStratum D = some k) :
    ((symDividedDifferenceRelationXM D k).coeff k).natDegree = (D.coeff k).natDegree - 1 := by
  have hksupp : k ∈ D.support := ghostLeadingStratum_support hk
  have hkfilter : k ∈ D.support.filter (fun j => j ≤ k) := Finset.mem_filter.mpr ⟨hksupp, le_rfl⟩
  rw [symDividedDifferenceRelationXM_coeff, if_pos hkfilter]
  exact symCoeffDividedDiffM_natDegree_eq_pred (coeff_natDegree_pos_of_ghostLeadingStratum hk)

/-- Evaluation of the canonical symbolic divided-difference relation. -/
theorem eval_symDividedDifferenceRelationXM
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) (z y₁ y₂ x : ℂ) :
    (symDividedDifferenceRelationXM D k).eval₂
        (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) y₁) x =
      ∑ i ∈ D.support.filter (fun j => j ≤ k),
        (symCoeffDividedDiffM (D.coeff i)).eval₂
          (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) y₁ * x ^ i := by
  rw [symDividedDifferenceRelationXM, Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Polynomial.eval₂_monomial]
  change Polynomial.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) y₁
      (symCoeffDividedDiffM (D.coeff i)) * x ^ i =
    Polynomial.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) y₁
      (symCoeffDividedDiffM (D.coeff i)) * x ^ i
  rfl

/-- The canonical symbolic bivariate divided-difference relation evaluates to zero at any distinct
pair where the original relation vanishes at both branches. -/
theorem eval_symDividedDifferenceRelationXM_eq_zero_of_two_eval_D_eq_zero
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k : ℕ} (hk : ghostLeadingStratum D = some k)
    {z y₁ y₂ x : ℂ} (hy : y₁ ≠ y₂)
    (hzero₁ : D.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₁) x = 0)
    (hzero₂ : D.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) x = 0) :
    (symDividedDifferenceRelationXM D k).eval₂
        (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) y₁) x = 0 := by
  rw [eval_symDividedDifferenceRelationXM]
  have hfd := lowerTruncationX_finiteDifference_eq_zero_of_two_eval_D_eq_zero D hk hzero₁ hzero₂
  have hfactor :
      ∑ i ∈ D.support.filter (fun j => j ≤ k),
        ((y₁ - y₂) *
          (symCoeffDividedDiffM (D.coeff i)).eval₂
            (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) y₁) * x ^ i = 0 := by
    rw [← hfd]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [coeff_eval_sub_eval_eq_sub_mul_symCoeffDividedDiffM_eval]
  have hmul :
      (y₁ - y₂) * (∑ i ∈ D.support.filter (fun j => j ≤ k),
        (symCoeffDividedDiffM (D.coeff i)).eval₂
          (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) y₁ * x ^ i) = 0 := by
    rw [Finset.mul_sum]
    rw [← hfactor]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hnon : y₁ - y₂ ≠ 0 := sub_ne_zero.mpr hy
  have hcancel :
      (y₁ - y₂) * (∑ i ∈ D.support.filter (fun j => j ≤ k),
        (symCoeffDividedDiffM (D.coeff i)).eval₂
          (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y₂) y₁ * x ^ i) = (y₁ - y₂) * 0 := by
    simpa using hmul
  exact mul_left_cancel₀ hnon hcancel

end Bottcher

namespace Bottcher

/-- Specialize a bivariate coefficient `C[z][Y₂][Y₁]` at a deck-partner polynomial `τ(Y)`, sending
`Y₁ ↦ Y` and `Y₂ ↦ τ(Y)`. -/
noncomputable def specializeBivarAtDeckPartner (τ : Polynomial (Polynomial ℂ)) :
    Polynomial (Polynomial (Polynomial ℂ)) →+* Polynomial (Polynomial ℂ) :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) τ)
    Polynomial.X

/-- Specialize an `X`-polynomial with bivariate coefficients at a deck partner. -/
noncomputable def specializeRelationAtDeckPartner
    (τ : Polynomial (Polynomial ℂ))
    (F : Polynomial (Polynomial (Polynomial (Polynomial ℂ)))) :
    Polynomial (Polynomial (Polynomial ℂ)) :=
  F.map (specializeBivarAtDeckPartner τ)

/-- Coefficients after deck-partner specialization. -/
theorem specializeRelationAtDeckPartner_coeff
    (τ : Polynomial (Polynomial ℂ))
    (F : Polynomial (Polynomial (Polynomial (Polynomial ℂ)))) (i : ℕ) :
    (specializeRelationAtDeckPartner τ F).coeff i =
      specializeBivarAtDeckPartner τ (F.coeff i) := by
  rw [specializeRelationAtDeckPartner, Polynomial.coeff_map]

/-- Deck-partner specialization cannot increase `X` degree. -/
theorem specializeRelationAtDeckPartner_natDegree_le
    (τ : Polynomial (Polynomial ℂ))
    (F : Polynomial (Polynomial (Polynomial (Polynomial ℂ)))) :
    (specializeRelationAtDeckPartner τ F).natDegree ≤ F.natDegree :=
  Polynomial.natDegree_map_le

/-- If the specialized leading `X` coefficient is nonzero, deck-partner specialization preserves the
`X` degree exactly. -/
theorem specializeRelationAtDeckPartner_natDegree_eq_of_leading_coeff_ne_zero
    (τ : Polynomial (Polynomial ℂ))
    {F : Polynomial (Polynomial (Polynomial (Polynomial ℂ)))}
    (hlead : specializeBivarAtDeckPartner τ (F.coeff F.natDegree) ≠ 0) :
    (specializeRelationAtDeckPartner τ F).natDegree = F.natDegree := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact specializeRelationAtDeckPartner_natDegree_le τ F
  · rw [specializeRelationAtDeckPartner_coeff]
    exact hlead

/-- The specialized canonical symbolic divided-difference relation has `X` degree `k` whenever the
deck specialization preserves the selected leading coefficient. -/
theorem specialize_symDividedDifferenceRelationXM_natDegree_eq_of_ghostLeadingStratum
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ}
    (hk : ghostLeadingStratum D = some k) (τ : Polynomial (Polynomial ℂ))
    (hpreserve : specializeBivarAtDeckPartner τ ((symDividedDifferenceRelationXM D k).coeff k) ≠ 0) :
    (specializeRelationAtDeckPartner τ (symDividedDifferenceRelationXM D k)).natDegree = k := by
  have hFdeg := symDividedDifferenceRelationXM_natDegree_eq_of_ghostLeadingStratum hk
  have hlead : specializeBivarAtDeckPartner τ
      ((symDividedDifferenceRelationXM D k).coeff (symDividedDifferenceRelationXM D k).natDegree) ≠ 0 := by
    rwa [hFdeg]
  rw [specializeRelationAtDeckPartner_natDegree_eq_of_leading_coeff_ne_zero τ hlead, hFdeg]

/-- The specialized canonical relation itself, back in the original `C[z][Y][X]` shape. -/
noncomputable def deckSpecializedSymDividedDifferenceRelationXM
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) (τ : Polynomial (Polynomial ℂ)) :
    Polynomial (Polynomial (Polynomial ℂ)) :=
  specializeRelationAtDeckPartner τ (symDividedDifferenceRelationXM D k)

/-- Coefficients of the deck-specialized canonical symbolic relation. -/
theorem deckSpecializedSymDividedDifferenceRelationXM_coeff
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ) (τ : Polynomial (Polynomial ℂ)) (i : ℕ) :
    (deckSpecializedSymDividedDifferenceRelationXM D k τ).coeff i =
      specializeBivarAtDeckPartner τ ((symDividedDifferenceRelationXM D k).coeff i) := by
  rw [deckSpecializedSymDividedDifferenceRelationXM, specializeRelationAtDeckPartner_coeff]

/-- The deck-specialized canonical relation has exact `X` degree `k` under the nonzero-preservation
hypothesis for the selected leading coefficient. -/
theorem deckSpecializedSymDividedDifferenceRelationXM_natDegree_eq_of_ghostLeadingStratum
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ}
    (hk : ghostLeadingStratum D = some k) (τ : Polynomial (Polynomial ℂ))
    (hpreserve : specializeBivarAtDeckPartner τ ((symDividedDifferenceRelationXM D k).coeff k) ≠ 0) :
    (deckSpecializedSymDividedDifferenceRelationXM D k τ).natDegree = k :=
  specialize_symDividedDifferenceRelationXM_natDegree_eq_of_ghostLeadingStratum hk τ hpreserve

end Bottcher


namespace Bottcher

/-- Evaluation commutes with specializing `Y₂` to a deck-partner polynomial `τ(Y)`. -/
theorem eval_specializeY₂AtDeckPartner
    (τ : Polynomial (Polynomial ℂ)) (z y : ℂ) :
    (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y).comp
        (Polynomial.eval₂RingHom (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) τ) =
      Polynomial.eval₂RingHom (Polynomial.evalRingHom z)
        (τ.eval₂ (Polynomial.evalRingHom z) y) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [Polynomial.eval₂RingHom]
  · simp [Polynomial.eval₂RingHom]

/-- Evaluation commutes with the full bivariate deck-partner specialization `Y₁ ↦ Y`,
`Y₂ ↦ τ(Y)`. -/
theorem eval_specializeBivarAtDeckPartner
    (τ : Polynomial (Polynomial ℂ)) (B : Polynomial (Polynomial (Polynomial ℂ))) (z y : ℂ) :
    (specializeBivarAtDeckPartner τ B).eval₂ (Polynomial.evalRingHom z) y =
      B.eval₂
        (Polynomial.eval₂RingHom (Polynomial.evalRingHom z)
          (τ.eval₂ (Polynomial.evalRingHom z) y)) y := by
  let coeffLeft : Polynomial (Polynomial ℂ) →+* ℂ :=
    (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y).comp
      (Polynomial.eval₂RingHom (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) τ)
  let coeffRight : Polynomial (Polynomial ℂ) →+* ℂ :=
    Polynomial.eval₂RingHom (Polynomial.evalRingHom z)
      (τ.eval₂ (Polynomial.evalRingHom z) y)
  have hcoeff : coeffLeft = coeffRight := eval_specializeY₂AtDeckPartner τ z y
  let left : Polynomial (Polynomial (Polynomial ℂ)) →+* ℂ :=
    (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y).comp
      (specializeBivarAtDeckPartner τ)
  let right : Polynomial (Polynomial (Polynomial ℂ)) →+* ℂ :=
    Polynomial.eval₂RingHom coeffRight y
  have hhom : left = right := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa [left, right, specializeBivarAtDeckPartner, coeffLeft, coeffRight, Polynomial.eval₂RingHom]
        using RingHom.congr_fun hcoeff a
    · simp [left, right, specializeBivarAtDeckPartner, Polynomial.eval₂RingHom]
  change left B = right B
  rw [hhom]

/-- Evaluation of a deck-specialized `X`-relation agrees with bivariate evaluation before
specialization. -/
theorem eval_specializeRelationAtDeckPartner
    (τ : Polynomial (Polynomial ℂ))
    (F : Polynomial (Polynomial (Polynomial (Polynomial ℂ)))) (z y x : ℂ) :
    (specializeRelationAtDeckPartner τ F).eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y) x =
      F.eval₂
        (Polynomial.eval₂RingHom
          (Polynomial.eval₂RingHom (Polynomial.evalRingHom z)
            (τ.eval₂ (Polynomial.evalRingHom z) y)) y) x := by
  rw [specializeRelationAtDeckPartner, Polynomial.eval₂_map]
  let leftCoeff : Polynomial (Polynomial (Polynomial ℂ)) →+* ℂ :=
    (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y).comp (specializeBivarAtDeckPartner τ)
  let rightCoeff : Polynomial (Polynomial (Polynomial ℂ)) →+* ℂ :=
    Polynomial.eval₂RingHom
      (Polynomial.eval₂RingHom (Polynomial.evalRingHom z)
        (τ.eval₂ (Polynomial.evalRingHom z) y)) y
  have hcoeff : leftCoeff = rightCoeff := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa [leftCoeff, rightCoeff, specializeBivarAtDeckPartner, Polynomial.eval₂RingHom]
        using RingHom.congr_fun (eval_specializeY₂AtDeckPartner τ z y) a
    · simp [leftCoeff, rightCoeff, specializeBivarAtDeckPartner, Polynomial.eval₂RingHom]
  change F.eval₂ leftCoeff x = F.eval₂ rightCoeff x
  rw [hcoeff]

/-- Evaluation of the deck-specialized canonical symbolic relation. -/
theorem eval_deckSpecializedSymDividedDifferenceRelationXM
    (D : Polynomial (Polynomial (Polynomial ℂ))) (k : ℕ)
    (τ : Polynomial (Polynomial ℂ)) (z y x : ℂ) :
    (deckSpecializedSymDividedDifferenceRelationXM D k τ).eval₂
        (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y) x =
      (symDividedDifferenceRelationXM D k).eval₂
        (Polynomial.eval₂RingHom
          (Polynomial.eval₂RingHom (Polynomial.evalRingHom z)
            (τ.eval₂ (Polynomial.evalRingHom z) y)) y) x := by
  rw [deckSpecializedSymDividedDifferenceRelationXM, eval_specializeRelationAtDeckPartner]

end Bottcher

namespace Bottcher

/-- If the original relation vanishes at a branch and its deck partner, then the deck-specialized
canonical symbolic divided-difference relation vanishes at the original branch. -/
theorem eval_deckSpecializedSymDividedDifferenceRelationXM_eq_zero_of_deck_pair
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k : ℕ} (hk : ghostLeadingStratum D = some k)
    (τ : Polynomial (Polynomial ℂ)) {z y x : ℂ}
    (hsep : y ≠ τ.eval₂ (Polynomial.evalRingHom z) y)
    (hzero₁ : D.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y) x = 0)
    (hzero₂ : D.eval₂
      (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) (τ.eval₂ (Polynomial.evalRingHom z) y)) x = 0) :
    (deckSpecializedSymDividedDifferenceRelationXM D k τ).eval₂
        (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y) x = 0 := by
  rw [eval_deckSpecializedSymDividedDifferenceRelationXM]
  exact eval_symDividedDifferenceRelationXM_eq_zero_of_two_eval_D_eq_zero D hk hsep hzero₁ hzero₂

end Bottcher

namespace Bottcher

/-- Substituting a nonconstant deck-partner polynomial `τ(Y)` for a single polynomial variable is
injective over `C[z]`. This is the algebraic kernel behind the deck nonzero-preservation criterion. -/
theorem eval₂_C_injective_of_natDegree_pos {τ : Polynomial (Polynomial ℂ)}
    (hτ : 0 < τ.natDegree) :
    Function.Injective
      (Polynomial.eval₂RingHom (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) τ) := by
  intro p q hpq
  have hpq' : p.eval₂ (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) τ =
      q.eval₂ (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) τ := hpq
  have hzero : (p - q).eval₂ (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) τ = 0 := by
    rw [Polynomial.eval₂_sub]
    exact sub_eq_zero.mpr hpq'
  change (p - q).comp τ = 0 at hzero
  rw [Polynomial.comp_eq_zero_iff] at hzero
  rcases hzero with h | h
  · exact sub_eq_zero.mp h
  · rcases h with ⟨_, hτconst⟩
    have hτdeg : τ.natDegree = 0 := by
      rw [hτconst, Polynomial.natDegree_C]
    rw [hτdeg] at hτ
    exact (Nat.lt_irrefl 0 hτ).elim

/-- Nonzero single-variable polynomials stay nonzero after substituting a nonconstant deck partner. -/
theorem eval₂_C_ne_zero_of_natDegree_pos {τ p : Polynomial (Polynomial ℂ)}
    (hτ : 0 < τ.natDegree) (hp : p ≠ 0) :
    p.eval₂ (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) τ ≠ 0 := by
  intro hzero
  have hmap : (Polynomial.eval₂RingHom (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) τ) p =
      (Polynomial.eval₂RingHom (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) τ) 0 := by
    simpa using hzero
  exact hp ((eval₂_C_injective_of_natDegree_pos hτ) hmap)

end Bottcher

namespace Bottcher

/-- The canonical symbolic divided difference is a quotient of the literal difference
`q(Y₁) - q(Y₂)` by `Y₁ - Y₂`. -/
theorem symCoeffDividedDiffM_mul_eq (q : Polynomial (Polynomial ℂ)) :
    (Polynomial.X - Polynomial.C (Polynomial.X : Polynomial (Polynomial ℂ))) * symCoeffDividedDiffM q =
      q.map (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) - Polynomial.C q := by
  let R : Type := Polynomial (Polynomial ℂ)
  let cHom : Polynomial ℂ →+* R := Polynomial.C
  let p : Polynomial R := q.map cHom
  let N : Polynomial R := p - Polynomial.C q
  let Q : Polynomial R := symCoeffDividedDiffM q
  have hp_evalX : Polynomial.eval (Polynomial.X : R) p = q := by
    change Polynomial.eval (Polynomial.X : R) (q.map cHom) = q
    rw [Polynomial.eval_map]
    change Polynomial.eval₂ cHom (Polynomial.X : R) q = q
    rw [show cHom = (Polynomial.C : Polynomial ℂ →+* R) from rfl]
    rw [Polynomial.eval₂_C_X]
  have hroot : Polynomial.IsRoot N (Polynomial.X : R) := by
    rw [Polynomial.IsRoot.def]
    change Polynomial.eval (Polynomial.X : R) (p - Polynomial.C q) = 0
    rw [Polynomial.eval_sub, hp_evalX, Polynomial.eval_C, sub_self]
  have hmul : (Polynomial.X - Polynomial.C (Polynomial.X : R)) * Q = N := by
    simpa [N, Q, symCoeffDividedDiffM, p]
      using (Polynomial.mul_divByMonic_eq_iff_isRoot (p := N) (a := (Polynomial.X : R))).2 hroot
  simpa [R, cHom, p, N, Q] using hmul

/-- After specializing `Y₂` to a deck-partner polynomial `τ(Y)`, the symbolic divided difference
measures the failure of the leading coefficient `q` to be invariant under `Y ↦ τ(Y)`. -/
theorem sub_mul_specializeBivar_symCoeffDividedDiffM_eq
    (τ q : Polynomial (Polynomial ℂ)) :
    (Polynomial.X - τ) * specializeBivarAtDeckPartner τ (symCoeffDividedDiffM q) =
      q - q.comp τ := by
  have hY₁ : specializeBivarAtDeckPartner τ
      (Polynomial.X : Polynomial (Polynomial (Polynomial ℂ))) =
      (Polynomial.X : Polynomial (Polynomial ℂ)) := by
    simp [specializeBivarAtDeckPartner, Polynomial.eval₂RingHom]
  have hY₂ : specializeBivarAtDeckPartner τ
      (Polynomial.C (Polynomial.X : Polynomial (Polynomial ℂ))) = τ := by
    simp [specializeBivarAtDeckPartner, Polynomial.eval₂RingHom]
  have hqY₂ : specializeBivarAtDeckPartner τ (Polynomial.C q) = q.comp τ := by
    change Polynomial.eval₂
      (Polynomial.eval₂RingHom (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) τ)
      (Polynomial.X : Polynomial (Polynomial ℂ)) (Polynomial.C q) = q.comp τ
    rw [Polynomial.eval₂_C]
    rfl
  have hqY₁ : specializeBivarAtDeckPartner τ
      (q.map (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ))) = q := by
    change Polynomial.eval₂
      (Polynomial.eval₂RingHom (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) τ)
      (Polynomial.X : Polynomial (Polynomial ℂ))
      (q.map (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ))) = q
    rw [Polynomial.eval₂_map]
    have hcomp :
        (Polynomial.eval₂RingHom (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) τ).comp
          (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) =
        (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) := by
      apply Polynomial.ringHom_ext
      · intro a
        simp [Polynomial.eval₂RingHom]
      · simp [Polynomial.eval₂RingHom]
    rw [hcomp, Polynomial.eval₂_C_X]
  have hsubXY : specializeBivarAtDeckPartner τ
      (Polynomial.X - Polynomial.C (Polynomial.X : Polynomial (Polynomial ℂ))) =
      (Polynomial.X : Polynomial (Polynomial ℂ)) - τ := by
    calc
      specializeBivarAtDeckPartner τ
          (Polynomial.X - Polynomial.C (Polynomial.X : Polynomial (Polynomial ℂ))) =
          specializeBivarAtDeckPartner τ (Polynomial.X : Polynomial (Polynomial (Polynomial ℂ))) -
            specializeBivarAtDeckPartner τ
              (Polynomial.C (Polynomial.X : Polynomial (Polynomial ℂ))) :=
        RingHom.map_sub (specializeBivarAtDeckPartner τ)
          (Polynomial.X : Polynomial (Polynomial (Polynomial ℂ)))
          (Polynomial.C (Polynomial.X : Polynomial (Polynomial ℂ)))
      _ = (Polynomial.X : Polynomial (Polynomial ℂ)) - τ := by rw [hY₁, hY₂]
  have hsubq : specializeBivarAtDeckPartner τ
      (q.map (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) - Polynomial.C q) =
      q - q.comp τ := by
    calc
      specializeBivarAtDeckPartner τ
          (q.map (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) - Polynomial.C q) =
          specializeBivarAtDeckPartner τ
              (q.map (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ))) -
            specializeBivarAtDeckPartner τ (Polynomial.C q) :=
        RingHom.map_sub (specializeBivarAtDeckPartner τ)
          (q.map (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)))
          (Polynomial.C q)
      _ = q - q.comp τ := by rw [hqY₁, hqY₂]
  have hmap := congrArg (specializeBivarAtDeckPartner τ) (symCoeffDividedDiffM_mul_eq q)
  rw [RingHom.map_mul, hsubXY, hsubq] at hmap
  exact hmap

/-- If the leading coefficient is not invariant under `Y ↦ τ(Y)`, the deck-specialized symbolic
quotient is nonzero. -/
theorem specializeBivar_symCoeffDividedDiffM_ne_zero_of_comp_ne
    {τ q : Polynomial (Polynomial ℂ)} (hneq : q.comp τ ≠ q) :
    specializeBivarAtDeckPartner τ (symCoeffDividedDiffM q) ≠ 0 := by
  intro hzero
  have hmain := sub_mul_specializeBivar_symCoeffDividedDiffM_eq τ q
  rw [hzero, mul_zero] at hmain
  have hdiff : q - q.comp τ ≠ 0 := sub_ne_zero.mpr hneq.symm
  exact hdiff hmain.symm

/-- The top `X`-coefficient of the deck-specialized canonical symbolic relation is nonzero as soon
as the old leading coefficient is not invariant under the deck partner. -/
theorem specializeBivar_topCoeff_ne_zero_of_ghostLeadingStratum_comp_ne
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ} (hk : ghostLeadingStratum D = some k)
    {τ : Polynomial (Polynomial ℂ)} (hneq : (D.coeff k).comp τ ≠ D.coeff k) :
    specializeBivarAtDeckPartner τ ((symDividedDifferenceRelationXM D k).coeff k) ≠ 0 := by
  have hksupp : k ∈ D.support := ghostLeadingStratum_support hk
  have hkfilter : k ∈ D.support.filter (fun j => j ≤ k) := Finset.mem_filter.mpr ⟨hksupp, le_rfl⟩
  rw [symDividedDifferenceRelationXM_coeff, if_pos hkfilter]
  exact specializeBivar_symCoeffDividedDiffM_ne_zero_of_comp_ne hneq

/-- Grok branch: a non-invariant leading coefficient gives exact degree descent after deck
specialization, with no generic resultant/discriminant machinery. -/
theorem deckSpecializedSymDividedDifferenceRelationXM_natDegree_eq_of_ghostLeadingStratum_comp_ne
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ} (hk : ghostLeadingStratum D = some k)
    {τ : Polynomial (Polynomial ℂ)} (hneq : (D.coeff k).comp τ ≠ D.coeff k) :
    (deckSpecializedSymDividedDifferenceRelationXM D k τ).natDegree = k := by
  exact deckSpecializedSymDividedDifferenceRelationXM_natDegree_eq_of_ghostLeadingStratum hk τ
    (specializeBivar_topCoeff_ne_zero_of_ghostLeadingStratum_comp_ne hk hneq)

end Bottcher

namespace Bottcher

/-- Positive `Y` degree over `C[z]` forces a nonzero `Y` derivative. -/
theorem derivative_ne_zero_of_natDegree_pos {q : Polynomial (Polynomial ℂ)}
    (hqpos : 0 < q.natDegree) : q.derivative ≠ 0 := by
  intro hzero
  have hdeg : q.natDegree = 0 := Polynomial.derivative_eq_zero.mp hzero
  exact (Nat.ne_of_gt hqpos) hdeg

/-- Differentiating a deck-invariance equation gives the polynomial chain-rule identity. -/
theorem derivative_comp_eq_of_comp_eq {q τ : Polynomial (Polynomial ℂ)} (hinv : q.comp τ = q) :
    τ.derivative * (q.derivative).comp τ = q.derivative := by
  have h := congrArg Polynomial.derivative hinv
  rw [Polynomial.derivative_comp] at h
  exact h

/-- For a sign-type deck partner, invariance of `q` forces non-invariance of `q.derivative`, unless
`q.derivative = 0`. This is the derivative fallback for the `q.comp τ = q` obstruction. -/
theorem derivative_comp_ne_of_comp_eq_of_derivative_eq_neg_one
    {q τ : Polynomial (Polynomial ℂ)} (hinv : q.comp τ = q)
    (hτderiv : τ.derivative = -1) (hqderiv : q.derivative ≠ 0) :
    (q.derivative).comp τ ≠ q.derivative := by
  intro hsame
  have hchain := derivative_comp_eq_of_comp_eq (q := q) (τ := τ) hinv
  rw [hτderiv, hsame] at hchain
  have hnorm : (-1 : Polynomial (Polynomial ℂ)) * q.derivative = -q.derivative := by
    ring
  rw [hnorm] at hchain
  exact hqderiv (neg_eq_self.mp hchain)

/-- If `q` is invariant under a sign-type deck partner but has positive `Y` degree, the symbolic
quotient for `q.derivative` is nonzero after deck specialization. -/
theorem specializeBivar_symCoeffDividedDiffM_derivative_ne_zero_of_sign_invariant
    {q τ : Polynomial (Polynomial ℂ)} (hqpos : 0 < q.natDegree)
    (hinv : q.comp τ = q) (hτderiv : τ.derivative = -1) :
    specializeBivarAtDeckPartner τ (symCoeffDividedDiffM q.derivative) ≠ 0 := by
  exact specializeBivar_symCoeffDividedDiffM_ne_zero_of_comp_ne
    (derivative_comp_ne_of_comp_eq_of_derivative_eq_neg_one hinv hτderiv
      (derivative_ne_zero_of_natDegree_pos hqpos))

/-- Ghost-leading version of the sign-deck derivative fallback. -/
theorem specializeBivar_symCoeffDividedDiffM_coeff_derivative_ne_zero_of_ghostLeadingStratum_sign_invariant
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ} (hk : ghostLeadingStratum D = some k)
    {τ : Polynomial (Polynomial ℂ)} (hinv : (D.coeff k).comp τ = D.coeff k)
    (hτderiv : τ.derivative = -1) :
    specializeBivarAtDeckPartner τ (symCoeffDividedDiffM (D.coeff k).derivative) ≠ 0 := by
  exact specializeBivar_symCoeffDividedDiffM_derivative_ne_zero_of_sign_invariant
    (coeff_natDegree_pos_of_ghostLeadingStratum hk) hinv hτderiv

end Bottcher

namespace Bottcher

/-- If the original top coefficient is hidden by a sign-type deck invariance, the coefficientwise
`Y`-derivative lower-truncation still produces an exact-degree deck-specialized divided-difference
relation. This is the formal derivative descent branch for the non-invariant-leading-coefficient
criterion. -/
theorem deckSpecializedSymDividedDifferenceRelationXM_yDerivLowerTruncationX_natDegree_eq_of_sign_invariant
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ} (hk : ghostLeadingStratum D = some k)
    {τ : Polynomial (Polynomial ℂ)} (hinv : (D.coeff k).comp τ = D.coeff k)
    (hτderiv : τ.derivative = -1) :
    (deckSpecializedSymDividedDifferenceRelationXM (yDerivLowerTruncationX D k) k τ).natDegree = k := by
  let E : Polynomial (Polynomial (Polynomial ℂ)) := yDerivLowerTruncationX D k
  have hksupp : k ∈ D.support := ghostLeadingStratum_support hk
  have hEcoeff : E.coeff k = (D.coeff k).derivative := by
    simp [E, yDerivLowerTruncationX_coeff, hksupp]
  have hEcoeff0 : E.coeff k ≠ 0 := by
    rw [hEcoeff]
    exact coeff_derivative_ne_zero_of_ghostLeadingStratum hk
  have hkEsupp : k ∈ E.support := Polynomial.mem_support_iff.mpr hEcoeff0
  have hkEfilter : k ∈ E.support.filter (fun j => j ≤ k) := Finset.mem_filter.mpr ⟨hkEsupp, le_rfl⟩
  have hspec : specializeBivarAtDeckPartner τ (symCoeffDividedDiffM (D.coeff k).derivative) ≠ 0 :=
    specializeBivar_symCoeffDividedDiffM_coeff_derivative_ne_zero_of_ghostLeadingStratum_sign_invariant
      hk hinv hτderiv
  have hpreserve : specializeBivarAtDeckPartner τ ((symDividedDifferenceRelationXM E k).coeff k) ≠ 0 := by
    rw [symDividedDifferenceRelationXM_coeff, if_pos hkEfilter, hEcoeff]
    exact hspec
  have hFdeg : (symDividedDifferenceRelationXM E k).natDegree = k := by
    apply le_antisymm
    · exact symDividedDifferenceRelationXM_natDegree_le E k
    · have hcoeff : (symDividedDifferenceRelationXM E k).coeff k ≠ 0 := by
        intro hzero
        apply hpreserve
        rw [hzero, map_zero]
      exact Polynomial.le_natDegree_of_ne_zero hcoeff
  rw [deckSpecializedSymDividedDifferenceRelationXM]
  have hlead : specializeBivarAtDeckPartner τ
      ((symDividedDifferenceRelationXM E k).coeff (symDividedDifferenceRelationXM E k).natDegree) ≠ 0 := by
    rwa [hFdeg]
  rw [specializeRelationAtDeckPartner_natDegree_eq_of_leading_coeff_ne_zero τ hlead, hFdeg]

end Bottcher

namespace Bottcher

/-- The skew part of a coefficient under a deck polynomial. -/
noncomputable def deckSkew (τ q : Polynomial (Polynomial ℂ)) : Polynomial (Polynomial ℂ) :=
  q - q.comp τ

/-- The two-sheet trace of a coefficient under a deck polynomial. -/
noncomputable def deckTrace (τ q : Polynomial (Polynomial ℂ)) : Polynomial (Polynomial ℂ) :=
  q + q.comp τ

/-- Under an involutive deck polynomial, the skew part is anti-invariant. -/
theorem deckSkew_comp_eq_neg_of_comp_self
    {τ q : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X) :
    (deckSkew τ q).comp τ = -deckSkew τ q := by
  simp [deckSkew, Polynomial.comp_assoc, hτ₂]

/-- Under an involutive deck polynomial, the trace of any skew part vanishes. -/
theorem deckTrace_deckSkew_eq_zero_of_comp_self
    {τ q : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X) :
    deckTrace τ (deckSkew τ q) = 0 := by
  rw [deckTrace, deckSkew_comp_eq_neg_of_comp_self hτ₂]
  simp [deckSkew]

/-- Grok's twisted-average core: the derivative skew has zero two-sheet trace. -/
theorem deckTrace_derivative_skew_eq_zero_of_comp_self
    {τ q : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X) :
    deckTrace τ (deckSkew τ q.derivative) = 0 :=
  deckTrace_deckSkew_eq_zero_of_comp_self hτ₂

end Bottcher

namespace Bottcher

/-- Evaluating a composed coefficient at `Y = y` is evaluating the original coefficient at the deck
partner value `Y = τ(y)`. -/
theorem eval₂_comp_deckPartner (τ q : Polynomial (Polynomial ℂ)) (z y : ℂ) :
    (q.comp τ).eval₂ (Polynomial.evalRingHom z) y =
      q.eval₂ (Polynomial.evalRingHom z) (τ.eval₂ (Polynomial.evalRingHom z) y) := by
  rw [Polynomial.eval₂_comp]

/-- Evaluation of the two-sheet trace. -/
theorem eval₂_deckTrace (τ q : Polynomial (Polynomial ℂ)) (z y : ℂ) :
    (deckTrace τ q).eval₂ (Polynomial.evalRingHom z) y =
      q.eval₂ (Polynomial.evalRingHom z) y +
        q.eval₂ (Polynomial.evalRingHom z) (τ.eval₂ (Polynomial.evalRingHom z) y) := by
  rw [deckTrace, Polynomial.eval₂_add, eval₂_comp_deckPartner]

/-- Evaluation of the skew part. -/
theorem eval₂_deckSkew (τ q : Polynomial (Polynomial ℂ)) (z y : ℂ) :
    (deckSkew τ q).eval₂ (Polynomial.evalRingHom z) y =
      q.eval₂ (Polynomial.evalRingHom z) y -
        q.eval₂ (Polynomial.evalRingHom z) (τ.eval₂ (Polynomial.evalRingHom z) y) := by
  rw [deckSkew, Polynomial.eval₂_sub, eval₂_comp_deckPartner]

/-- The derivative skew has zero two-sheet trace after evaluation. -/
theorem eval₂_deckTrace_derivative_skew_eq_zero_of_comp_self
    {τ q : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X) (z y : ℂ) :
    (deckSkew τ q.derivative).eval₂ (Polynomial.evalRingHom z) y +
      (deckSkew τ q.derivative).eval₂ (Polynomial.evalRingHom z)
        (τ.eval₂ (Polynomial.evalRingHom z) y) = 0 := by
  have h := congrArg (fun p : Polynomial (Polynomial ℂ) => p.eval₂ (Polynomial.evalRingHom z) y)
    (deckTrace_derivative_skew_eq_zero_of_comp_self (τ := τ) (q := q) hτ₂)
  simp only [Polynomial.eval₂_zero] at h
  change (deckTrace τ (deckSkew τ q.derivative)).eval₂ (Polynomial.evalRingHom z) y = 0 at h
  rw [eval₂_deckTrace] at h
  exact h

end Bottcher

namespace Bottcher

/-- The scalar `1/2` is the inverse of `2` inside `C[z][Y]`. -/
theorem deckHalfScalar_mul_two :
    Polynomial.C (Polynomial.C ((1 / 2 : ℂ))) * (2 : Polynomial (Polynomial ℂ)) = 1 := by
  ext n m
  by_cases hn : n = 0
  · subst n
    by_cases hm : m = 0
    · subst m
      simp
    · simp [Polynomial.coeff_C, Polynomial.coeff_one, hm]
  · simp [Polynomial.coeff_C, Polynomial.coeff_one, hn]

/-- Multiplication by the scalar `1/2` cancels a factor `2`. -/
theorem deckHalfScalar_mul_mul_two (p : Polynomial (Polynomial ℂ)) :
    Polynomial.C (Polynomial.C ((1 / 2 : ℂ))) * p * 2 = p := by
  calc
    Polynomial.C (Polynomial.C ((1 / 2 : ℂ))) * p * 2 =
        (Polynomial.C (Polynomial.C ((1 / 2 : ℂ))) * (2 : Polynomial (Polynomial ℂ))) * p := by ring
    _ = p := by rw [deckHalfScalar_mul_two, one_mul]

/-- The invariant center coordinate for an involutive deck polynomial. -/
noncomputable def deckCenter (τ : Polynomial (Polynomial ℂ)) : Polynomial (Polynomial ℂ) :=
  Polynomial.C (Polynomial.C ((1 / 2 : ℂ))) * (Polynomial.X + τ)

/-- The anti-invariant half-difference coordinate for an involutive deck polynomial. -/
noncomputable def deckHalfDiff (τ : Polynomial (Polynomial ℂ)) : Polynomial (Polynomial ℂ) :=
  Polynomial.C (Polynomial.C ((1 / 2 : ℂ))) * (Polynomial.X - τ)

/-- The center coordinate is invariant under an involutive deck polynomial. -/
theorem deckCenter_comp_eq_self_of_comp_self
    {τ : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X) :
    (deckCenter τ).comp τ = deckCenter τ := by
  simp [deckCenter, hτ₂]
  ring_nf

/-- The half-difference coordinate is anti-invariant under an involutive deck polynomial. -/
theorem deckHalfDiff_comp_eq_neg_of_comp_self
    {τ : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X) :
    (deckHalfDiff τ).comp τ = -deckHalfDiff τ := by
  simp [deckHalfDiff, hτ₂]
  ring_nf

/-- The deck variable is center plus half-difference. -/
theorem deckCenter_add_halfDiff (τ : Polynomial (Polynomial ℂ)) :
    deckCenter τ + deckHalfDiff τ = Polynomial.X := by
  have h : deckCenter τ + deckHalfDiff τ =
      Polynomial.C (Polynomial.C ((1 / 2 : ℂ))) * ((Polynomial.X : Polynomial (Polynomial ℂ)) * 2) := by
    simp [deckCenter, deckHalfDiff]
    ring
  rw [h]
  simpa [mul_assoc] using deckHalfScalar_mul_mul_two (Polynomial.X : Polynomial (Polynomial ℂ))

/-- The deck partner is center minus half-difference. -/
theorem deckCenter_sub_halfDiff (τ : Polynomial (Polynomial ℂ)) :
    deckCenter τ - deckHalfDiff τ = τ := by
  have h : deckCenter τ - deckHalfDiff τ =
      Polynomial.C (Polynomial.C ((1 / 2 : ℂ))) * (τ * 2) := by
    simp [deckCenter, deckHalfDiff]
    ring
  rw [h]
  simpa [mul_assoc] using deckHalfScalar_mul_mul_two τ

end Bottcher

namespace Bottcher

/-- Evaluation of the invariant center coordinate. -/
theorem eval₂_deckCenter (τ : Polynomial (Polynomial ℂ)) (z y : ℂ) :
    (deckCenter τ).eval₂ (Polynomial.evalRingHom z) y =
      (1 / 2 : ℂ) * (y + τ.eval₂ (Polynomial.evalRingHom z) y) := by
  simp [deckCenter, Polynomial.eval₂_mul, Polynomial.eval₂_add]

/-- Evaluation of the anti-invariant half-difference coordinate. -/
theorem eval₂_deckHalfDiff (τ : Polynomial (Polynomial ℂ)) (z y : ℂ) :
    (deckHalfDiff τ).eval₂ (Polynomial.evalRingHom z) y =
      (1 / 2 : ℂ) * (y - τ.eval₂ (Polynomial.evalRingHom z) y) := by
  simp [deckHalfDiff, Polynomial.eval₂_mul, Polynomial.eval₂_sub]

end Bottcher

namespace Bottcher

/-- The deck-specialized divided-difference quotient of an anti-invariant coefficient is invariant. -/
theorem specializeBivar_symCoeffDividedDiffM_comp_eq_self_of_comp_eq_neg
    {τ p : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X) (hτX : τ ≠ Polynomial.X)
    (hpanti : p.comp τ = -p) :
    (specializeBivarAtDeckPartner τ (symCoeffDividedDiffM p)).comp τ =
      specializeBivarAtDeckPartner τ (symCoeffDividedDiffM p) := by
  let S : Polynomial (Polynomial ℂ) := specializeBivarAtDeckPartner τ (symCoeffDividedDiffM p)
  have hmain := sub_mul_specializeBivar_symCoeffDividedDiffM_eq τ p
  change (Polynomial.X - τ) * S = p - p.comp τ at hmain
  have hmain' : (Polynomial.X - τ) * S = p + p := by
    rw [hmain, hpanti]
    abel
  have hcomp := congrArg (fun r : Polynomial (Polynomial ℂ) => r.comp τ) hmain
  change (((Polynomial.X - τ) * S).comp τ) = ((p - p.comp τ).comp τ) at hcomp
  simp [hτ₂, hpanti, S] at hcomp
  have hcomp' : (Polynomial.X - τ) * S.comp τ = p + p := by
    have hneg := congrArg Neg.neg hcomp
    have hleft : -((τ - Polynomial.X) * S.comp τ) = (Polynomial.X - τ) * S.comp τ := by
      ring
    rw [hleft] at hneg
    simpa [S] using hneg
  have hfactor : Polynomial.X - τ ≠ 0 := sub_ne_zero.mpr hτX.symm
  exact mul_left_cancel₀ hfactor (by rw [hcomp', hmain'])

/-- If `q` is invariant under a sign-type deck partner, then its `Y`-derivative is anti-invariant. -/
theorem derivative_comp_eq_neg_of_comp_eq_of_derivative_eq_neg_one
    {q τ : Polynomial (Polynomial ℂ)} (hinv : q.comp τ = q) (hτderiv : τ.derivative = -1) :
    q.derivative.comp τ = -q.derivative := by
  have hchain := derivative_comp_eq_of_comp_eq (q := q) (τ := τ) hinv
  rw [hτderiv] at hchain
  have hnorm : (-1 : Polynomial (Polynomial ℂ)) * (q.derivative.comp τ) =
      -(q.derivative.comp τ) := by
    ring
  rw [hnorm] at hchain
  have hneg := congrArg Neg.neg hchain
  simpa using hneg

/-- In the sign-invariant case, the divided-difference quotient of the derivative is deck-invariant. -/
theorem specializeBivar_symCoeffDividedDiffM_derivative_comp_eq_self_of_sign_invariant
    {q τ : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X) (hτX : τ ≠ Polynomial.X)
    (hinv : q.comp τ = q) (hτderiv : τ.derivative = -1) :
    (specializeBivarAtDeckPartner τ (symCoeffDividedDiffM q.derivative)).comp τ =
      specializeBivarAtDeckPartner τ (symCoeffDividedDiffM q.derivative) := by
  exact specializeBivar_symCoeffDividedDiffM_comp_eq_self_of_comp_eq_neg hτ₂ hτX
    (derivative_comp_eq_neg_of_comp_eq_of_derivative_eq_neg_one hinv hτderiv)

end Bottcher

namespace Bottcher

/-- The square of the half-difference coordinate is deck-invariant. -/
theorem deckHalfDiff_sq_comp_eq_self_of_comp_self
    {τ : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X) :
    (deckHalfDiff τ ^ 2).comp τ = deckHalfDiff τ ^ 2 := by
  change (Polynomial.compRingHom τ) (deckHalfDiff τ ^ 2) = deckHalfDiff τ ^ 2
  have h := deckHalfDiff_comp_eq_neg_of_comp_self hτ₂
  change (Polynomial.compRingHom τ) (deckHalfDiff τ) = -deckHalfDiff τ at h
  rw [map_pow, h]
  ring

/-- Substitute the invariant deck coordinates `C = (Y+τ)/2` and `T = ((Y-τ)/2)^2` into a polynomial
`C[z][C][T]`. This is the algebraic shape of the single-branch even relation. -/
noncomputable def specializeAtDeckInvariantCoordinates (τ : Polynomial (Polynomial ℂ)) :
    Polynomial (Polynomial (Polynomial ℂ)) →+* Polynomial (Polynomial ℂ) :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) (deckCenter τ))
    (deckHalfDiff τ ^ 2)

/-- Any polynomial in the invariant coordinates `deckCenter τ` and `deckHalfDiff τ ^ 2` is
itself deck-invariant. -/
theorem specializeAtDeckInvariantCoordinates_comp_eq_self_of_comp_self
    {τ : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X)
    (R : Polynomial (Polynomial (Polynomial ℂ))) :
    (specializeAtDeckInvariantCoordinates τ R).comp τ =
      specializeAtDeckInvariantCoordinates τ R := by
  let coeffHom : Polynomial (Polynomial ℂ) →+* Polynomial (Polynomial ℂ) :=
    Polynomial.eval₂RingHom (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) (deckCenter τ)
  let φ : Polynomial (Polynomial (Polynomial ℂ)) →+* Polynomial (Polynomial ℂ) :=
    specializeAtDeckInvariantCoordinates τ
  have hcoeff : (Polynomial.compRingHom τ).comp coeffHom = coeffHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [coeffHom]
    · simp [coeffHom, deckCenter_comp_eq_self_of_comp_self hτ₂]
  have hhom : (Polynomial.compRingHom τ).comp φ = φ := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa [φ, specializeAtDeckInvariantCoordinates, coeffHom] using RingHom.congr_fun hcoeff a
    · simp [φ, specializeAtDeckInvariantCoordinates, deckHalfDiff_sq_comp_eq_self_of_comp_self hτ₂]
  change ((Polynomial.compRingHom τ).comp φ) R = φ R
  rw [hhom]

/-- Evaluation of invariant-coordinate specialization is the single-branch form
`R(z, center(z,y), halfDiff(z,y)^2)`. -/
theorem eval₂_specializeAtDeckInvariantCoordinates
    (τ : Polynomial (Polynomial ℂ)) (R : Polynomial (Polynomial (Polynomial ℂ))) (z y : ℂ) :
    (specializeAtDeckInvariantCoordinates τ R).eval₂ (Polynomial.evalRingHom z) y =
      R.eval₂
        (Polynomial.eval₂RingHom (Polynomial.evalRingHom z)
          ((deckCenter τ).eval₂ (Polynomial.evalRingHom z) y))
        ((deckHalfDiff τ).eval₂ (Polynomial.evalRingHom z) y ^ 2) := by
  let coeffHom : Polynomial (Polynomial ℂ) →+* Polynomial (Polynomial ℂ) :=
    Polynomial.eval₂RingHom (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)) (deckCenter τ)
  let leftCoeff : Polynomial (Polynomial ℂ) →+* ℂ :=
    (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y).comp coeffHom
  let rightCoeff : Polynomial (Polynomial ℂ) →+* ℂ :=
    Polynomial.eval₂RingHom (Polynomial.evalRingHom z)
      ((deckCenter τ).eval₂ (Polynomial.evalRingHom z) y)
  have hcoeff : leftCoeff = rightCoeff := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [leftCoeff, rightCoeff, coeffHom]
    · simp [leftCoeff, rightCoeff, coeffHom]
  let left : Polynomial (Polynomial (Polynomial ℂ)) →+* ℂ :=
    (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y).comp
      (specializeAtDeckInvariantCoordinates τ)
  let right : Polynomial (Polynomial (Polynomial ℂ)) →+* ℂ :=
    Polynomial.eval₂RingHom rightCoeff
      ((deckHalfDiff τ).eval₂ (Polynomial.evalRingHom z) y ^ 2)
  have hhom : left = right := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa [left, right, specializeAtDeckInvariantCoordinates, coeffHom, leftCoeff, rightCoeff]
        using RingHom.congr_fun hcoeff a
    · simp [left, right, specializeAtDeckInvariantCoordinates, Polynomial.eval₂_pow]
  change left R = right R
  rw [hhom]

end Bottcher

namespace Bottcher

/-- A deck polynomial with `Y`-derivative `-1` is affine in `Y`: `τ = a(z) - Y`. -/
theorem exists_C_sub_X_of_derivative_eq_neg_one {τ : Polynomial (Polynomial ℂ)}
    (hτderiv : τ.derivative = -1) :
    ∃ a : Polynomial ℂ, τ = Polynomial.C a - Polynomial.X := by
  have hderiv : (τ + Polynomial.X).derivative = 0 := by
    rw [Polynomial.derivative_add, hτderiv, Polynomial.derivative_X]
    ring
  obtain ⟨a, ha⟩ := isYConstant_of_derivative_eq_zero hderiv
  refine ⟨a, ?_⟩
  calc
    τ = (τ + Polynomial.X) - Polynomial.X := by ring
    _ = Polynomial.C a - Polynomial.X := by rw [ha]

/-- For a sign-type deck polynomial, the center coordinate is constant in `Y`. -/
theorem deckCenter_isYConstant_of_derivative_eq_neg_one {τ : Polynomial (Polynomial ℂ)}
    (hτderiv : τ.derivative = -1) :
    IsYConstant (deckCenter τ) := by
  have hderiv : (deckCenter τ).derivative = 0 := by
    rw [deckCenter, Polynomial.derivative_C_mul, Polynomial.derivative_add, Polynomial.derivative_X,
      hτderiv]
    ring
  exact isYConstant_of_derivative_eq_zero hderiv

/-- If the center is `Y`-constant, the half-difference is the original variable minus that center. -/
theorem deckHalfDiff_eq_X_sub_C_of_deckCenter_eq_C {τ : Polynomial (Polynomial ℂ)} {a : Polynomial ℂ}
    (hcenter : deckCenter τ = Polynomial.C a) :
    deckHalfDiff τ = Polynomial.X - Polynomial.C a := by
  have h := deckCenter_add_halfDiff τ
  rw [hcenter] at h
  calc
    deckHalfDiff τ = Polynomial.X - Polynomial.C a := by
      rw [← h]
      abel

end Bottcher

namespace Bottcher

/-- Powers of `-Y` in `C[z][Y]`. -/
theorem neg_X_pow_eq_C_mul_X_pow_polyPoly (n : ℕ) :
    (-Polynomial.X : Polynomial (Polynomial ℂ)) ^ n =
      Polynomial.C ((-1 : Polynomial ℂ) ^ n) * Polynomial.X ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih]
      simp [pow_succ]
      ring

/-- Coefficients after substituting `-Y` for `Y`. -/
theorem coeff_comp_neg_X_polyPoly (p : Polynomial (Polynomial ℂ)) (n : ℕ) :
    (p.comp (-Polynomial.X)).coeff n = (-1 : Polynomial ℂ) ^ n * p.coeff n := by
  classical
  rw [show p.comp (-Polynomial.X) = p.eval₂ Polynomial.C (-Polynomial.X) from rfl]
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single n]
  · rw [Polynomial.coeff_C_mul, neg_X_pow_eq_C_mul_X_pow_polyPoly, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow]
    simp
    ring
  · intro m hm hmn
    rw [Polynomial.coeff_C_mul, neg_X_pow_eq_C_mul_X_pow_polyPoly, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow]
    simp [Ne.symm hmn]
  · intro hn
    rw [Polynomial.notMem_support_iff.mp hn]
    simp

/-- If a polynomial is invariant under `Y ↦ -Y`, all odd coefficients vanish. -/
theorem coeff_odd_eq_zero_of_comp_neg_X_eq_self
    {p : Polynomial (Polynomial ℂ)} (h : p.comp (-Polynomial.X) = p) (k : ℕ) :
    p.coeff (2 * k + 1) = 0 := by
  have hcoeff := congrArg (fun r : Polynomial (Polynomial ℂ) => r.coeff (2 * k + 1)) h
  change (p.comp (-Polynomial.X)).coeff (2 * k + 1) = p.coeff (2 * k + 1) at hcoeff
  rw [coeff_comp_neg_X_polyPoly] at hcoeff
  have hpow : (-1 : Polynomial ℂ) ^ (2 * k + 1) = -1 := by
    norm_num [pow_succ]
  rw [hpow] at hcoeff
  have hneg : -p.coeff (2 * k + 1) = p.coeff (2 * k + 1) := by
    simpa using hcoeff
  exact neg_eq_self.mp hneg

end Bottcher

namespace Bottcher

/-- An even polynomial in the deck variable is recovered by contracting to the square coordinate and
expanding back along `Y ↦ Y^2`. This is the formal `p(Y) = P(Y^2)` brick. -/
theorem expand_contract_two_eq_self_of_comp_neg_X_eq_self
    {p : Polynomial (Polynomial ℂ)} (h : p.comp (-Polynomial.X) = p) :
    Polynomial.expand (Polynomial ℂ) 2 (Polynomial.contract 2 p) = p := by
  ext n
  rw [Polynomial.coeff_expand (by norm_num : 0 < 2)]
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · subst n
    rw [if_pos (dvd_mul_right 2 k), Polynomial.coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
    rw [Nat.mul_div_right k (by norm_num : 0 < 2)]
    rw [mul_comm]
  · subst n
    rw [if_neg (Nat.not_two_dvd_bit1 k)]
    rw [coeff_odd_eq_zero_of_comp_neg_X_eq_self h k]

end Bottcher

namespace Bottcher

/-- Shifting the reflection `Y ↦ 2c - Y` to the center gives `Y ↦ -Y`. -/
theorem comp_reflection_shift_eq_shift_comp_neg_X (c : Polynomial ℂ) :
    (Polynomial.C (2 * c) - Polynomial.X : Polynomial (Polynomial ℂ)).comp
        (Polynomial.X + Polynomial.C c) =
      (Polynomial.X + Polynomial.C c : Polynomial (Polynomial ℂ)).comp (-Polynomial.X) := by
  simp [Polynomial.sub_comp, Polynomial.add_comp]
  have hc2 : (Polynomial.C (2 : Polynomial ℂ) : Polynomial (Polynomial ℂ)) * Polynomial.C c =
      (Polynomial.C c + Polynomial.C c : Polynomial (Polynomial ℂ)) := by
    rw [← Polynomial.C_mul]
    rw [show 2 * c = c + c by ring]
    rw [Polynomial.C_add]
  rw [hc2]
  abel

/-- A polynomial invariant under reflection around `c` becomes even after shifting the center to zero. -/
theorem shifted_comp_neg_X_eq_self_of_comp_reflection_eq_self
    {p : Polynomial (Polynomial ℂ)} (c : Polynomial ℂ)
    (h : p.comp (Polynomial.C (2 * c) - Polynomial.X) = p) :
    (p.comp (Polynomial.X + Polynomial.C c)).comp (-Polynomial.X) =
      p.comp (Polynomial.X + Polynomial.C c) := by
  let shift : Polynomial (Polynomial ℂ) := Polynomial.X + Polynomial.C c
  have hc : (p.comp (Polynomial.C (2 * c) - Polynomial.X)).comp shift = p.comp shift :=
    congrArg (fun r : Polynomial (Polynomial ℂ) => r.comp shift) h
  change (p.comp shift).comp (-Polynomial.X) = p.comp shift
  rw [Polynomial.comp_assoc]
  rw [← comp_reflection_shift_eq_shift_comp_neg_X c]
  rw [← Polynomial.comp_assoc]
  exact hc

/-- Undoing the center shift returns the original polynomial. -/
theorem comp_shift_comp_unshift_eq_self (p : Polynomial (Polynomial ℂ)) (c : Polynomial ℂ) :
    (p.comp (Polynomial.X + Polynomial.C c)).comp (Polynomial.X - Polynomial.C c) = p := by
  rw [Polynomial.comp_assoc]
  have hinner : (Polynomial.X + Polynomial.C c : Polynomial (Polynomial ℂ)).comp
      (Polynomial.X - Polynomial.C c) = Polynomial.X := by
    simp [Polynomial.add_comp]
  rw [hinner, Polynomial.comp_X]

/-- If a polynomial is invariant under the reflection `Y ↦ 2c - Y`, it is a polynomial in
`(Y-c)^2`. This is the centered single-branch representation brick for a sign deck. -/
theorem exists_comp_square_of_comp_reflection_eq_self
    {p : Polynomial (Polynomial ℂ)} (c : Polynomial ℂ)
    (h : p.comp (Polynomial.C (2 * c) - Polynomial.X) = p) :
    ∃ P : Polynomial (Polynomial ℂ), p = P.comp ((Polynomial.X - Polynomial.C c) ^ 2) := by
  let shift : Polynomial (Polynomial ℂ) := Polynomial.X + Polynomial.C c
  let unshift : Polynomial (Polynomial ℂ) := Polynomial.X - Polynomial.C c
  let q : Polynomial (Polynomial ℂ) := p.comp shift
  let P : Polynomial (Polynomial ℂ) := Polynomial.contract 2 q
  refine ⟨P, ?_⟩
  have hq : q.comp (-Polynomial.X) = q := by
    simpa [q, shift] using shifted_comp_neg_X_eq_self_of_comp_reflection_eq_self (p := p) c h
  have hqrep : Polynomial.expand (Polynomial ℂ) 2 P = q := by
    simpa [P] using expand_contract_two_eq_self_of_comp_neg_X_eq_self hq
  calc
    p = q.comp unshift := by
      simpa [q, shift, unshift] using (comp_shift_comp_unshift_eq_self p c).symm
    _ = (Polynomial.expand (Polynomial ℂ) 2 P).comp unshift := by rw [hqrep]
    _ = P.comp (unshift ^ 2) := by
      rw [Polynomial.expand_eq_comp_X_pow]
      rw [Polynomial.comp_assoc]
      simp [unshift]

end Bottcher

namespace Bottcher

/-- A deck polynomial whose center is the constant `c` is the reflection `Y ↦ 2c - Y`. -/
theorem deck_eq_reflection_of_deckCenter_eq_C {τ : Polynomial (Polynomial ℂ)} {c : Polynomial ℂ}
    (hcenter : deckCenter τ = Polynomial.C c) :
    τ = Polynomial.C (2 * c) - Polynomial.X := by
  have hhalf := deckHalfDiff_eq_X_sub_C_of_deckCenter_eq_C hcenter
  have hsub := deckCenter_sub_halfDiff τ
  rw [hcenter, hhalf] at hsub
  calc
    τ = Polynomial.C c - (Polynomial.X - Polynomial.C c) := hsub.symm
    _ = Polynomial.C (2 * c) - Polynomial.X := by
      have hc2 : Polynomial.C (2 * c) =
          (Polynomial.C c + Polynomial.C c : Polynomial (Polynomial ℂ)) := by
        rw [show 2 * c = c + c by ring]
        rw [Polynomial.C_add]
      rw [hc2]
      abel

/-- A deck-invariant polynomial with constant deck center factors through the square of the
half-difference coordinate. -/
theorem exists_comp_deckHalfDiff_sq_of_comp_eq_self_of_deckCenter_eq_C
    {p τ : Polynomial (Polynomial ℂ)} {c : Polynomial ℂ}
    (hcenter : deckCenter τ = Polynomial.C c) (hinv : p.comp τ = p) :
    ∃ P : Polynomial (Polynomial ℂ), p = P.comp (deckHalfDiff τ ^ 2) := by
  have hτ := deck_eq_reflection_of_deckCenter_eq_C hcenter
  have href : p.comp (Polynomial.C (2 * c) - Polynomial.X) = p := by
    rw [← hτ]
    exact hinv
  obtain ⟨P, hP⟩ := exists_comp_square_of_comp_reflection_eq_self c href
  refine ⟨P, ?_⟩
  have hhalf := deckHalfDiff_eq_X_sub_C_of_deckCenter_eq_C hcenter
  rw [hP, ← hhalf]

/-- If the deck has derivative `-1`, every deck-invariant polynomial factors through
`deckHalfDiff τ ^ 2`. -/
theorem exists_comp_deckHalfDiff_sq_of_comp_eq_self_of_derivative_eq_neg_one
    {p τ : Polynomial (Polynomial ℂ)} (hτderiv : τ.derivative = -1) (hinv : p.comp τ = p) :
    ∃ P : Polynomial (Polynomial ℂ), p = P.comp (deckHalfDiff τ ^ 2) := by
  obtain ⟨c, hcenter⟩ := deckCenter_isYConstant_of_derivative_eq_neg_one hτderiv
  exact exists_comp_deckHalfDiff_sq_of_comp_eq_self_of_deckCenter_eq_C hcenter hinv

end Bottcher

namespace Bottcher

/-- In the sign-invariant branch, the specialized symmetric divided-difference quotient of the
`Y`-derivative factors through the squared half-difference deck coordinate. -/
theorem exists_comp_deckHalfDiff_sq_of_specializeBivar_symCoeffDividedDiffM_derivative_sign_invariant
    {q τ : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X) (hτX : τ ≠ Polynomial.X)
    (hinv : q.comp τ = q) (hτderiv : τ.derivative = -1) :
    ∃ P : Polynomial (Polynomial ℂ),
      specializeBivarAtDeckPartner τ (symCoeffDividedDiffM q.derivative) =
        P.comp (deckHalfDiff τ ^ 2) := by
  have hS : (specializeBivarAtDeckPartner τ (symCoeffDividedDiffM q.derivative)).comp τ =
      specializeBivarAtDeckPartner τ (symCoeffDividedDiffM q.derivative) :=
    specializeBivar_symCoeffDividedDiffM_derivative_comp_eq_self_of_sign_invariant
      hτ₂ hτX hinv hτderiv
  exact exists_comp_deckHalfDiff_sq_of_comp_eq_self_of_derivative_eq_neg_one hτderiv hS

end Bottcher

namespace Bottcher

/-- A sign deck has a linear half-difference coordinate. -/
theorem deckHalfDiff_natDegree_eq_one_of_derivative_eq_neg_one {τ : Polynomial (Polynomial ℂ)}
    (hτderiv : τ.derivative = -1) :
    (deckHalfDiff τ).natDegree = 1 := by
  obtain ⟨c, hcenter⟩ := deckCenter_isYConstant_of_derivative_eq_neg_one hτderiv
  rw [deckHalfDiff_eq_X_sub_C_of_deckCenter_eq_C hcenter, Polynomial.natDegree_X_sub_C]

/-- Anything factoring through the square of a linear deck half-difference has even `Y`-degree. -/
theorem even_natDegree_of_comp_deckHalfDiff_sq_of_derivative_eq_neg_one
    {p P τ : Polynomial (Polynomial ℂ)} (hτderiv : τ.derivative = -1)
    (hP : p = P.comp (deckHalfDiff τ ^ 2)) :
    2 ∣ p.natDegree := by
  rw [hP, Polynomial.natDegree_comp, Polynomial.natDegree_pow,
    deckHalfDiff_natDegree_eq_one_of_derivative_eq_neg_one hτderiv]
  simp

/-- Every deck-invariant polynomial under a sign deck has even `Y`-degree. -/
theorem even_natDegree_of_comp_eq_self_of_derivative_eq_neg_one
    {p τ : Polynomial (Polynomial ℂ)} (hτderiv : τ.derivative = -1) (hinv : p.comp τ = p) :
    2 ∣ p.natDegree := by
  obtain ⟨P, hP⟩ := exists_comp_deckHalfDiff_sq_of_comp_eq_self_of_derivative_eq_neg_one hτderiv hinv
  exact even_natDegree_of_comp_deckHalfDiff_sq_of_derivative_eq_neg_one hτderiv hP

/-- In the sign-invariant branch, the specialized derivative divided-difference quotient has even
`Y`-degree. This is the parity obstruction opened by the squared half-difference representation. -/
theorem even_natDegree_specializeBivar_symCoeffDividedDiffM_derivative_sign_invariant
    {q τ : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X) (hτX : τ ≠ Polynomial.X)
    (hinv : q.comp τ = q) (hτderiv : τ.derivative = -1) :
    2 ∣ (specializeBivarAtDeckPartner τ (symCoeffDividedDiffM q.derivative)).natDegree := by
  have hS : (specializeBivarAtDeckPartner τ (symCoeffDividedDiffM q.derivative)).comp τ =
      specializeBivarAtDeckPartner τ (symCoeffDividedDiffM q.derivative) :=
    specializeBivar_symCoeffDividedDiffM_derivative_comp_eq_self_of_sign_invariant
      hτ₂ hτX hinv hτderiv
  exact even_natDegree_of_comp_eq_self_of_derivative_eq_neg_one hτderiv hS

end Bottcher

namespace Bottcher

/-- A deck-invariant polynomial under a sign deck cannot have odd `Y`-degree. -/
theorem natDegree_ne_two_mul_add_one_of_comp_eq_self_of_derivative_eq_neg_one
    {p τ : Polynomial (Polynomial ℂ)} (hτderiv : τ.derivative = -1) (hinv : p.comp τ = p)
    (n : ℕ) :
    p.natDegree ≠ 2 * n + 1 := by
  intro hdeg
  have heven := even_natDegree_of_comp_eq_self_of_derivative_eq_neg_one hτderiv hinv
  rw [hdeg] at heven
  exact Nat.not_two_dvd_bit1 n heven

/-- The specialized derivative divided-difference quotient in the sign-invariant branch cannot have
odd `Y`-degree. -/
theorem natDegree_specializeBivar_symCoeffDividedDiffM_derivative_ne_two_mul_add_one_sign_invariant
    {q τ : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X) (hτX : τ ≠ Polynomial.X)
    (hinv : q.comp τ = q) (hτderiv : τ.derivative = -1) (n : ℕ) :
    (specializeBivarAtDeckPartner τ (symCoeffDividedDiffM q.derivative)).natDegree ≠ 2 * n + 1 := by
  intro hdeg
  have heven := even_natDegree_specializeBivar_symCoeffDividedDiffM_derivative_sign_invariant
    hτ₂ hτX hinv hτderiv
  rw [hdeg] at heven
  exact Nat.not_two_dvd_bit1 n heven

end Bottcher

namespace Bottcher

/-- Evaluating a polynomial after composing with the squared half-difference coordinate is the same as
one-variable evaluation at the squared half-difference value. -/
theorem eval₂_comp_deckHalfDiff_sq (P τ : Polynomial (Polynomial ℂ)) (z y : ℂ) :
    (P.comp (deckHalfDiff τ ^ 2)).eval₂ (Polynomial.evalRingHom z) y =
      P.eval₂ (Polynomial.evalRingHom z)
        ((deckHalfDiff τ).eval₂ (Polynomial.evalRingHom z) y ^ 2) := by
  rw [Polynomial.eval₂_comp, Polynomial.eval₂_pow]

/-- Evaluated single-branch form of the sign-invariant derivative divided-difference quotient. -/
theorem exists_eval₂_square_form_specializeBivar_symCoeffDividedDiffM_derivative_sign_invariant
    {q τ : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X) (hτX : τ ≠ Polynomial.X)
    (hinv : q.comp τ = q) (hτderiv : τ.derivative = -1) :
    ∃ P : Polynomial (Polynomial ℂ), ∀ z y : ℂ,
      (specializeBivarAtDeckPartner τ (symCoeffDividedDiffM q.derivative)).eval₂
          (Polynomial.evalRingHom z) y =
        P.eval₂ (Polynomial.evalRingHom z)
          (((1 / 2 : ℂ) * (y - τ.eval₂ (Polynomial.evalRingHom z) y)) ^ 2) := by
  obtain ⟨P, hP⟩ :=
    exists_comp_deckHalfDiff_sq_of_specializeBivar_symCoeffDividedDiffM_derivative_sign_invariant
      hτ₂ hτX hinv hτderiv
  refine ⟨P, fun z y => ?_⟩
  rw [hP, eval₂_comp_deckHalfDiff_sq, eval₂_deckHalfDiff]

end Bottcher

namespace Bottcher

/-- Pointwise sign flip of the half-difference coordinate on the deck partner branch. -/
theorem eval₂_deckHalfDiff_deckPartner_eq_neg_of_comp_self
    {τ : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X) (z y : ℂ) :
    (deckHalfDiff τ).eval₂ (Polynomial.evalRingHom z)
        (τ.eval₂ (Polynomial.evalRingHom z) y) =
      - (deckHalfDiff τ).eval₂ (Polynomial.evalRingHom z) y := by
  have h := deckHalfDiff_comp_eq_neg_of_comp_self hτ₂
  have heval := congrArg (fun r : Polynomial (Polynomial ℂ) =>
      r.eval₂ (Polynomial.evalRingHom z) y) h
  change ((deckHalfDiff τ).comp τ).eval₂ (Polynomial.evalRingHom z) y =
    (-deckHalfDiff τ).eval₂ (Polynomial.evalRingHom z) y at heval
  rw [eval₂_comp_deckPartner, Polynomial.eval₂_neg] at heval
  exact heval

/-- The square of the half-difference coordinate takes the same value on both deck partner branches. -/
theorem eval₂_deckHalfDiff_sq_deckPartner_eq_self_of_comp_self
    {τ : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X) (z y : ℂ) :
    ((deckHalfDiff τ).eval₂ (Polynomial.evalRingHom z)
        (τ.eval₂ (Polynomial.evalRingHom z) y)) ^ 2 =
      ((deckHalfDiff τ).eval₂ (Polynomial.evalRingHom z) y) ^ 2 := by
  rw [eval₂_deckHalfDiff_deckPartner_eq_neg_of_comp_self hτ₂]
  ring

/-- The square-form quotient has identical evaluations on deck partner branches. -/
theorem eval₂_square_form_deckPartner_eq_self_of_comp_self
    {P τ : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X) (z y : ℂ) :
    P.eval₂ (Polynomial.evalRingHom z)
        (((deckHalfDiff τ).eval₂ (Polynomial.evalRingHom z)
          (τ.eval₂ (Polynomial.evalRingHom z) y)) ^ 2) =
      P.eval₂ (Polynomial.evalRingHom z)
        (((deckHalfDiff τ).eval₂ (Polynomial.evalRingHom z) y) ^ 2) := by
  rw [eval₂_deckHalfDiff_sq_deckPartner_eq_self_of_comp_self hτ₂]

end Bottcher

namespace Bottcher

/-- The selected top `X` coefficient of the derivative lower-truncation relation is exactly the
specialized derivative divided-difference quotient. This is the top-coefficient relocation suggested
by the square-coordinate branch. -/
theorem deckSpecialized_yDerivLowerTruncationX_topCoeff_eq_specializeBivar_symCoeffDividedDiffM_derivative
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ} (hk : ghostLeadingStratum D = some k)
    (τ : Polynomial (Polynomial ℂ)) :
    (deckSpecializedSymDividedDifferenceRelationXM (yDerivLowerTruncationX D k) k τ).coeff k =
      specializeBivarAtDeckPartner τ (symCoeffDividedDiffM (D.coeff k).derivative) := by
  let E : Polynomial (Polynomial (Polynomial ℂ)) := yDerivLowerTruncationX D k
  have hksupp : k ∈ D.support := ghostLeadingStratum_support hk
  have hEcoeff : E.coeff k = (D.coeff k).derivative := by
    simp [E, yDerivLowerTruncationX_coeff, hksupp]
  have hEcoeff0 : E.coeff k ≠ 0 := by
    rw [hEcoeff]
    exact coeff_derivative_ne_zero_of_ghostLeadingStratum hk
  have hkEsupp : k ∈ E.support := Polynomial.mem_support_iff.mpr hEcoeff0
  have hkEfilter : k ∈ E.support.filter (fun j => j ≤ k) := Finset.mem_filter.mpr ⟨hkEsupp, le_rfl⟩
  change (deckSpecializedSymDividedDifferenceRelationXM E k τ).coeff k =
    specializeBivarAtDeckPartner τ (symCoeffDividedDiffM (D.coeff k).derivative)
  rw [deckSpecializedSymDividedDifferenceRelationXM_coeff]
  rw [symDividedDifferenceRelationXM_coeff, if_pos hkEfilter, hEcoeff]

/-- The relocated top coefficient is nonzero in the sign-invariant derivative branch. -/
theorem deckSpecialized_yDerivLowerTruncationX_topCoeff_ne_zero_sign_invariant
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ} (hk : ghostLeadingStratum D = some k)
    {τ : Polynomial (Polynomial ℂ)} (hinv : (D.coeff k).comp τ = D.coeff k)
    (hτderiv : τ.derivative = -1) :
    (deckSpecializedSymDividedDifferenceRelationXM (yDerivLowerTruncationX D k) k τ).coeff k ≠ 0 := by
  rw [deckSpecialized_yDerivLowerTruncationX_topCoeff_eq_specializeBivar_symCoeffDividedDiffM_derivative hk τ]
  exact specializeBivar_symCoeffDividedDiffM_coeff_derivative_ne_zero_of_ghostLeadingStratum_sign_invariant
    hk hinv hτderiv

/-- In the sign-invariant branch, the relocated top coefficient is a nonzero polynomial in the
squared half-difference deck coordinate. -/
theorem exists_nonzero_comp_deckHalfDiff_sq_deckSpecialized_yDerivLowerTruncationX_topCoeff_sign_invariant
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ} (hk : ghostLeadingStratum D = some k)
    {τ : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X) (hτX : τ ≠ Polynomial.X)
    (hinv : (D.coeff k).comp τ = D.coeff k) (hτderiv : τ.derivative = -1) :
    ∃ P : Polynomial (Polynomial ℂ), P ≠ 0 ∧
      (deckSpecializedSymDividedDifferenceRelationXM (yDerivLowerTruncationX D k) k τ).coeff k =
        P.comp (deckHalfDiff τ ^ 2) := by
  obtain ⟨P, hP⟩ :=
    exists_comp_deckHalfDiff_sq_of_specializeBivar_symCoeffDividedDiffM_derivative_sign_invariant
      hτ₂ hτX hinv hτderiv
  refine ⟨P, ?_, ?_⟩
  · intro hPzero
    have hspec : specializeBivarAtDeckPartner τ (symCoeffDividedDiffM (D.coeff k).derivative) ≠ 0 :=
      specializeBivar_symCoeffDividedDiffM_coeff_derivative_ne_zero_of_ghostLeadingStratum_sign_invariant
        hk hinv hτderiv
    apply hspec
    rw [hP, hPzero]
    simp
  · rw [deckSpecialized_yDerivLowerTruncationX_topCoeff_eq_specializeBivar_symCoeffDividedDiffM_derivative hk τ]
    exact hP

/-- Evaluated single-branch square form for the nonzero relocated top coefficient. -/
theorem exists_nonzero_eval₂_square_form_deckSpecialized_yDerivLowerTruncationX_topCoeff_sign_invariant
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ} (hk : ghostLeadingStratum D = some k)
    {τ : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X) (hτX : τ ≠ Polynomial.X)
    (hinv : (D.coeff k).comp τ = D.coeff k) (hτderiv : τ.derivative = -1) :
    ∃ P : Polynomial (Polynomial ℂ), P ≠ 0 ∧ ∀ z y : ℂ,
      Polynomial.eval₂ (Polynomial.evalRingHom z) y
          ((deckSpecializedSymDividedDifferenceRelationXM (yDerivLowerTruncationX D k) k τ).coeff k) =
        P.eval₂ (Polynomial.evalRingHom z)
          (((1 / 2 : ℂ) * (y - τ.eval₂ (Polynomial.evalRingHom z) y)) ^ 2) := by
  obtain ⟨P, hP0, hP⟩ :=
    exists_nonzero_comp_deckHalfDiff_sq_deckSpecialized_yDerivLowerTruncationX_topCoeff_sign_invariant
      hk hτ₂ hτX hinv hτderiv
  refine ⟨P, hP0, fun z y => ?_⟩
  rw [hP, eval₂_comp_deckHalfDiff_sq, eval₂_deckHalfDiff]

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- Good-point form of the square-coordinate top-coefficient relocation: after the sign-invariant
branch is converted to a nonzero square form, transcendence of the branch coordinate gives an actual
point where the relocated top coefficient is nonzero. -/
theorem exists_good_point_square_form_deckSpecialized_yDerivLowerTruncationX_topCoeff_sign_invariant
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₂ : ℂ) (hU₂ : U ⊆ escapeOpen c₂)
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (γ : ℂ → ℂ) (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ} (hk : ghostLeadingStratum D = some k)
    {τ : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X) (hτX : τ ≠ Polynomial.X)
    (hinv : (D.coeff k).comp τ = D.coeff k) (hτderiv : τ.derivative = -1) :
    ∃ (P : Polynomial (Polynomial ℂ)) (w : ℂ), P ≠ 0 ∧ w ∈ U ∧ w ∈ (filledJulia c₂)ᶜ ∧
      Polynomial.eval₂ (Polynomial.evalRingHom w) (γ w)
          ((deckSpecializedSymDividedDifferenceRelationXM (yDerivLowerTruncationX D k) k τ).coeff k) ≠ 0 ∧
      Polynomial.eval₂ (Polynomial.evalRingHom w) (γ w)
          ((deckSpecializedSymDividedDifferenceRelationXM (yDerivLowerTruncationX D k) k τ).coeff k) =
        P.eval₂ (Polynomial.evalRingHom w)
          (((1 / 2 : ℂ) * (γ w - τ.eval₂ (Polynomial.evalRingHom w) (γ w))) ^ 2) := by
  obtain ⟨P, hP0, hPeval⟩ :=
    exists_nonzero_eval₂_square_form_deckSpecialized_yDerivLowerTruncationX_topCoeff_sign_invariant
      hk hτ₂ hτX hinv hτderiv
  have hcoeff0 :
      (deckSpecializedSymDividedDifferenceRelationXM (yDerivLowerTruncationX D k) k τ).coeff k ≠ 0 :=
    deckSpecialized_yDerivLowerTruncationX_topCoeff_ne_zero_sign_invariant hk hinv hτderiv
  obtain ⟨w, hwU, hwoff, htop_ne⟩ :=
    exists_mem_compl_filledJulia_gamma_ne_zero_of_bivariate_ne_zero_transcendental
      hUo hUc hUne hUinf c₂ hU₂ hG₂ γ hγmatch hcoeff0
  exact ⟨P, w, hP0, hwU, hwoff, htop_ne, hPeval w (γ w)⟩

end Bottcher

namespace Bottcher

/-- Evaluating coefficients of an `X`-polynomial preserves the exact `X` degree when the selected
leading coefficient survives at the point. -/
theorem natDegree_map_eval₂_eq_of_natDegree_eq_of_coeff_eval₂_ne_zero
    {F : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ} {z y : ℂ}
    (hFdeg : F.natDegree = k)
    (hcoeff : Polynomial.eval₂ (Polynomial.evalRingHom z) y (F.coeff k) ≠ 0) :
    (F.map (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y)).natDegree = k := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [← hFdeg]
    exact Polynomial.natDegree_map_le
  · rw [Polynomial.coeff_map]
    exact hcoeff

/-- At any point where the relocated top coefficient survives, the scalar fibre polynomial produced
by the sign-invariant derivative branch has exact `X` degree `k`. -/
theorem scalar_natDegree_deckSpecialized_yDerivLowerTruncationX_eq_of_topCoeff_ne_zero_sign_invariant
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ} (hk : ghostLeadingStratum D = some k)
    {τ : Polynomial (Polynomial ℂ)} (hinv : (D.coeff k).comp τ = D.coeff k)
    (hτderiv : τ.derivative = -1) {z y : ℂ}
    (htop : Polynomial.eval₂ (Polynomial.evalRingHom z) y
      ((deckSpecializedSymDividedDifferenceRelationXM (yDerivLowerTruncationX D k) k τ).coeff k) ≠ 0) :
    ((deckSpecializedSymDividedDifferenceRelationXM (yDerivLowerTruncationX D k) k τ).map
        (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y)).natDegree = k := by
  exact natDegree_map_eval₂_eq_of_natDegree_eq_of_coeff_eval₂_ne_zero
    (deckSpecializedSymDividedDifferenceRelationXM_yDerivLowerTruncationX_natDegree_eq_of_sign_invariant
      hk hinv hτderiv)
    htop

/-- Once the good point keeps exact scalar `X` degree `k`, the scalar `X`-derivative has strictly
smaller degree. This is the derivative gate for the simple-root/separability descent lead. -/
theorem scalar_derivative_natDegree_lt_deckSpecialized_yDerivLowerTruncationX_of_topCoeff_ne_zero_sign_invariant
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ} (hk : ghostLeadingStratum D = some k)
    {τ : Polynomial (Polynomial ℂ)} (hinv : (D.coeff k).comp τ = D.coeff k)
    (hτderiv : τ.derivative = -1) {z y : ℂ} (hkpos : 0 < k)
    (htop : Polynomial.eval₂ (Polynomial.evalRingHom z) y
      ((deckSpecializedSymDividedDifferenceRelationXM (yDerivLowerTruncationX D k) k τ).coeff k) ≠ 0) :
    (((deckSpecializedSymDividedDifferenceRelationXM (yDerivLowerTruncationX D k) k τ).map
        (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y)).derivative).natDegree < k := by
  let F : Polynomial ℂ :=
    (deckSpecializedSymDividedDifferenceRelationXM (yDerivLowerTruncationX D k) k τ).map
      (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y)
  have hdeg : F.natDegree = k :=
    scalar_natDegree_deckSpecialized_yDerivLowerTruncationX_eq_of_topCoeff_ne_zero_sign_invariant
      hk hinv hτderiv htop
  have hFdeg_ne : F.natDegree ≠ 0 := by
    rw [hdeg]
    exact ne_of_gt hkpos
  have hlt : F.derivative.natDegree < F.natDegree :=
    Polynomial.natDegree_derivative_lt hFdeg_ne
  simpa [F, hdeg] using hlt

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- Good-point package with exact scalar fibre degree, square-coordinate top coefficient, and the
lower-degree scalar `X`-derivative available when the selected stratum is positive. -/
theorem exists_good_point_scalar_fullDegree_square_form_deckSpecialized_yDerivLowerTruncationX_topCoeff_sign_invariant
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₂ : ℂ) (hU₂ : U ⊆ escapeOpen c₂)
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (γ : ℂ → ℂ) (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ} (hk : ghostLeadingStratum D = some k)
    {τ : Polynomial (Polynomial ℂ)} (hτ₂ : τ.comp τ = Polynomial.X) (hτX : τ ≠ Polynomial.X)
    (hinv : (D.coeff k).comp τ = D.coeff k) (hτderiv : τ.derivative = -1) :
    ∃ (P : Polynomial (Polynomial ℂ)) (w : ℂ), P ≠ 0 ∧ w ∈ U ∧ w ∈ (filledJulia c₂)ᶜ ∧
      Polynomial.eval₂ (Polynomial.evalRingHom w) (γ w)
          ((deckSpecializedSymDividedDifferenceRelationXM (yDerivLowerTruncationX D k) k τ).coeff k) ≠ 0 ∧
      ((deckSpecializedSymDividedDifferenceRelationXM (yDerivLowerTruncationX D k) k τ).map
          (Polynomial.eval₂RingHom (Polynomial.evalRingHom w) (γ w))).natDegree = k ∧
      Polynomial.eval₂ (Polynomial.evalRingHom w) (γ w)
          ((deckSpecializedSymDividedDifferenceRelationXM (yDerivLowerTruncationX D k) k τ).coeff k) =
        P.eval₂ (Polynomial.evalRingHom w)
          (((1 / 2 : ℂ) * (γ w - τ.eval₂ (Polynomial.evalRingHom w) (γ w))) ^ 2) := by
  obtain ⟨P, w, hP0, hwU, hwoff, htop, hsquare⟩ :=
    exists_good_point_square_form_deckSpecialized_yDerivLowerTruncationX_topCoeff_sign_invariant
      hUo hUc hUne hUinf c₂ hU₂ hG₂ γ hγmatch hk hτ₂ hτX hinv hτderiv
  have hscalar :=
    scalar_natDegree_deckSpecialized_yDerivLowerTruncationX_eq_of_topCoeff_ne_zero_sign_invariant
      hk hinv hτderiv htop
  exact ⟨P, w, hP0, hwU, hwoff, htop, hscalar, hsquare⟩

end Bottcher

namespace Bottcher

/-- Evaluating an `X`-polynomial after evaluating its `C[z][Y]` coefficients is the same as direct
nested `eval₂`. -/
theorem eval_map_eval₂RingHom_eq_eval₂
    (F : Polynomial (Polynomial (Polynomial ℂ))) (z y x : ℂ) :
    (F.map (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y)).eval x =
      F.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y) x := by
  rw [Polynomial.eval_map]

/-- A direct `eval₂` zero gives a root of the scalar fibre polynomial obtained by evaluating the
`C[z][Y]` coefficients. -/
theorem scalar_root_of_eval₂_eq_zero
    (F : Polynomial (Polynomial (Polynomial ℂ))) {z y x : ℂ}
    (hzero : F.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y) x = 0) :
    (F.map (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y)).eval x = 0 := by
  rw [eval_map_eval₂RingHom_eq_eval₂]
  exact hzero

/-- Separable scalar fibre turns a direct `eval₂` root into a simple root. This is the local
simple-root gate behind the resultant/separability bad-locus route. -/
theorem scalar_derivative_eval_ne_zero_of_separable_of_eval₂_eq_zero
    (F : Polynomial (Polynomial (Polynomial ℂ))) {z y x : ℂ}
    (hsep : (F.map (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y)).Separable)
    (hzero : F.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y) x = 0) :
    ((F.map (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y)).derivative).eval x ≠ 0 := by
  exact eval_derivative_ne_zero_of_separable hsep (scalar_root_of_eval₂_eq_zero F hzero)

/-- Deck-pair vanishing plus scalar-fibre separability gives the simple-root derivative nonvanishing
for the deck-specialized divided-difference relation. -/
theorem scalar_derivative_eval_ne_zero_of_separable_deckSpecializedSymDividedDifferenceRelationXM_deck_pair
    (D : Polynomial (Polynomial (Polynomial ℂ))) {k : ℕ} (hk : ghostLeadingStratum D = some k)
    (τ : Polynomial (Polynomial ℂ)) {z y x : ℂ}
    (hsep_branch : y ≠ τ.eval₂ (Polynomial.evalRingHom z) y)
    (hsep_scalar : ((deckSpecializedSymDividedDifferenceRelationXM D k τ).map
      (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y)).Separable)
    (hzero₁ : D.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y) x = 0)
    (hzero₂ : D.eval₂
      (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) (τ.eval₂ (Polynomial.evalRingHom z) y)) x = 0) :
    (((deckSpecializedSymDividedDifferenceRelationXM D k τ).map
      (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y)).derivative).eval x ≠ 0 := by
  have hzero := eval_deckSpecializedSymDividedDifferenceRelationXM_eq_zero_of_deck_pair
    D hk τ hsep_branch hzero₁ hzero₂
  exact scalar_derivative_eval_ne_zero_of_separable_of_eval₂_eq_zero
    (deckSpecializedSymDividedDifferenceRelationXM D k τ) hsep_scalar hzero

end Bottcher

namespace Bottcher

/-- Grok bad-locus bridge, lifted from `C[z]` to `C[z][Y]`: if the leading coefficient,
the derivative leading coefficient, and the resultant all survive at `(z,y)`, then the scalar
`X`-fibre is separable. -/
theorem separable_map_eval₂_of_avoids_squarefree_bad_locus_CzY
    (F : Polynomial (Polynomial (Polynomial ℂ))) {z y : ℂ}
    (hlead : Polynomial.eval₂ (Polynomial.evalRingHom z) y F.leadingCoeff ≠ 0)
    (hlead' : Polynomial.eval₂ (Polynomial.evalRingHom z) y (Polynomial.derivative F).leadingCoeff ≠ 0)
    (hres : Polynomial.eval₂ (Polynomial.evalRingHom z) y
      (Polynomial.resultant F (Polynomial.derivative F)) ≠ 0) :
    (F.map (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y)).Separable := by
  set ψ := Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y with hψ
  have hd1 : (F.map ψ).natDegree = F.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlead
  have hd2 : ((Polynomial.derivative F).map ψ).natDegree = (Polynomial.derivative F).natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlead'
  have hFmap_ne : F.map ψ ≠ 0 := by
    intro h
    have hc : (F.map ψ).coeff F.natDegree =
        Polynomial.eval₂ (Polynomial.evalRingHom z) y F.leadingCoeff := by
      rw [Polynomial.coeff_map]
      rfl
    rw [h, Polynomial.coeff_zero] at hc
    exact hlead hc.symm
  have key : Polynomial.resultant (F.map ψ) ((Polynomial.derivative F).map ψ) =
      Polynomial.eval₂ (Polynomial.evalRingHom z) y
        (Polynomial.resultant F (Polynomial.derivative F)) := by
    have e := Polynomial.resultant_map_map ψ (f := F) (g := Polynomial.derivative F)
      (m := F.natDegree) (n := (Polynomial.derivative F).natDegree)
    rw [show Polynomial.resultant (F.map ψ) ((Polynomial.derivative F).map ψ)
          = Polynomial.resultant (F.map ψ) ((Polynomial.derivative F).map ψ)
              (F.map ψ).natDegree ((Polynomial.derivative F).map ψ).natDegree
        from rfl, hd1, hd2, e]
    rfl
  rw [Polynomial.Separable, Polynomial.derivative_map]
  by_contra hnc
  have hzero : Polynomial.resultant (F.map ψ) ((Polynomial.derivative F).map ψ) = 0 := by
    rw [Polynomial.resultant_eq_zero_iff]
    exact ⟨Or.inl hFmap_ne, hnc⟩
  rw [key] at hzero
  exact hres hzero

/-- The Grok squarefree bad-locus polynomial for an `X`-polynomial over `C[z][Y]`. -/
noncomputable def squarefreeBadCzY (F : Polynomial (Polynomial (Polynomial ℂ))) :
    Polynomial (Polynomial ℂ) :=
  F.leadingCoeff * (Polynomial.derivative F).leadingCoeff *
    Polynomial.resultant F (Polynomial.derivative F)

/-- Avoiding the product bad locus means each of its three factors survives. -/
theorem squarefreeBadCzY_eval₂_ne_zero_parts
    (F : Polynomial (Polynomial (Polynomial ℂ))) {z y : ℂ}
    (hB : Polynomial.eval₂ (Polynomial.evalRingHom z) y (squarefreeBadCzY F) ≠ 0) :
    Polynomial.eval₂ (Polynomial.evalRingHom z) y F.leadingCoeff ≠ 0 ∧
    Polynomial.eval₂ (Polynomial.evalRingHom z) y (Polynomial.derivative F).leadingCoeff ≠ 0 ∧
    Polynomial.eval₂ (Polynomial.evalRingHom z) y
      (Polynomial.resultant F (Polynomial.derivative F)) ≠ 0 := by
  unfold squarefreeBadCzY at hB
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_mul] at hB
  obtain ⟨hleft, hres⟩ := mul_ne_zero_iff.mp hB
  obtain ⟨hlead, hlead'⟩ := mul_ne_zero_iff.mp hleft
  exact ⟨hlead, hlead', hres⟩

/-- Avoiding the Grok squarefree bad locus gives a separable scalar `X`-fibre. -/
theorem squarefreeBadCzY_eval₂_ne_zero_separable
    (F : Polynomial (Polynomial (Polynomial ℂ))) {z y : ℂ}
    (hB : Polynomial.eval₂ (Polynomial.evalRingHom z) y (squarefreeBadCzY F) ≠ 0) :
    (F.map (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y)).Separable := by
  rcases squarefreeBadCzY_eval₂_ne_zero_parts F hB with ⟨hlead, hlead', hres⟩
  exact separable_map_eval₂_of_avoids_squarefree_bad_locus_CzY F hlead hlead' hres

/-- For the sign-invariant Böttcher derivative branch, avoiding the Grok squarefree bad locus gives
both the relocated top coefficient and separability of the scalar fibre. -/
theorem squarefreeBadCzY_eval₂_ne_zero_topCoeff_and_separable_deckSpecialized_yDerivLowerTruncationX
    {D : Polynomial (Polynomial (Polynomial ℂ))} {k : ℕ} (hk : ghostLeadingStratum D = some k)
    {τ : Polynomial (Polynomial ℂ)} (hinv : (D.coeff k).comp τ = D.coeff k)
    (hτderiv : τ.derivative = -1) {z y : ℂ}
    (hB : Polynomial.eval₂ (Polynomial.evalRingHom z) y
      (squarefreeBadCzY
        (deckSpecializedSymDividedDifferenceRelationXM (yDerivLowerTruncationX D k) k τ)) ≠ 0) :
    Polynomial.eval₂ (Polynomial.evalRingHom z) y
      ((deckSpecializedSymDividedDifferenceRelationXM (yDerivLowerTruncationX D k) k τ).coeff k) ≠ 0 ∧
    ((deckSpecializedSymDividedDifferenceRelationXM (yDerivLowerTruncationX D k) k τ).map
      (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y)).Separable := by
  let F : Polynomial (Polynomial (Polynomial ℂ)) :=
    deckSpecializedSymDividedDifferenceRelationXM (yDerivLowerTruncationX D k) k τ
  have hB' : Polynomial.eval₂ (Polynomial.evalRingHom z) y (squarefreeBadCzY F) ≠ 0 := by
    simpa [F] using hB
  rcases squarefreeBadCzY_eval₂_ne_zero_parts F hB' with ⟨hlead, _, _⟩
  have hsep : (F.map (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y)).Separable :=
    squarefreeBadCzY_eval₂_ne_zero_separable F hB'
  have hdeg : F.natDegree = k :=
    deckSpecializedSymDividedDifferenceRelationXM_yDerivLowerTruncationX_natDegree_eq_of_sign_invariant
      hk hinv hτderiv
  have htop : Polynomial.eval₂ (Polynomial.evalRingHom z) y (F.coeff k) ≠ 0 := by
    simpa [F, Polynomial.leadingCoeff, hdeg] using hlead
  exact ⟨by simpa [F] using htop, by simpa [F] using hsep⟩

end Bottcher

namespace Bottcher

/-- The endpoint fibre polynomial attached to the coefficient family of `D` is exactly the scalar
specialization of `D` at the same `(z, γ z)`. -/
theorem fibrePoly_coeff_support_eq_map_eval₂
    (D : Polynomial (Polynomial (Polynomial ℂ))) (γ : ℂ → ℂ) (w : ℂ) :
    fibrePoly (fun i z => (D.coeff i).eval₂ (Polynomial.evalRingHom z) (γ z)) D.support w =
      D.map (Polynomial.eval₂RingHom (Polynomial.evalRingHom w) (γ w)) := by
  ext i
  rw [coeff_fibrePoly, Polynomial.coeff_map]
  by_cases hi : i ∈ D.support
  · simp [hi]
  · have hcoeff : D.coeff i = 0 := by
      simpa [Polynomial.mem_support_iff] using hi
    simp [hi, hcoeff]

/-- Avoiding `squarefreeBadCzY D` gives exactly the endpoint's top-coefficient and separable-fibre
conclusions for the sparse coefficient family of `D`. -/
theorem squarefreeBadCzY_eval₂_ne_zero_topCoeff_and_fibrePoly_separable
    (D : Polynomial (Polynomial (Polynomial ℂ))) (γ : ℂ → ℂ) {w : ℂ}
    (hB : (squarefreeBadCzY D).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0) :
    (D.coeff D.natDegree).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
    (fibrePoly (fun i z => (D.coeff i).eval₂ (Polynomial.evalRingHom z) (γ z)) D.support w).Separable := by
  rcases squarefreeBadCzY_eval₂_ne_zero_parts D hB with ⟨hlead, _, _⟩
  have hsep : (D.map (Polynomial.eval₂RingHom (Polynomial.evalRingHom w) (γ w))).Separable :=
    squarefreeBadCzY_eval₂_ne_zero_separable D hB
  have htop : (D.coeff D.natDegree).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 := by
    change Polynomial.eval₂ (Polynomial.evalRingHom w) (γ w) D.leadingCoeff ≠ 0
    exact hlead
  have hfib :
      (fibrePoly (fun i z => (D.coeff i).eval₂ (Polynomial.evalRingHom z) (γ z))
        D.support w).Separable := by
    rw [fibrePoly_coeff_support_eq_map_eval₂ D γ w]
    exact hsep
  exact ⟨htop, hfib⟩

/-- Radical coefficient-family core, upgraded with any already-proven nonzero Grok squarefree bad
locus for `D`.  This is the direct producer shape consumed by the q62 primitive/squarefree endpoint. -/
theorem radical_coeff_family_core_with_squarefreeBadCzY_of_sparse_relation
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (γ : ℂ → ℂ)
    (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ)
    (hEqOn : Set.EqOn (fun z => ∑ i ∈ s,
        ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U)
    {D : Polynomial (Polynomial (Polynomial ℂ))} {n : ℕ}
    (hD : D ≠ 0) (hdiv : sparseRelationPoly Q s ∣ D ^ n) (hn : 0 < n)
    (hB0 : squarefreeBadCzY D ≠ 0) :
    ∃ (Q' : ℕ → Polynomial (Polynomial ℂ)) (s' : Finset ℕ) (N : ℕ)
      (B : Polynomial (Polynomial ℂ)),
      (∃ i ∈ s', (Q' i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) ∧
      Set.EqOn (fun z => ∑ i ∈ s',
          ((Q' i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
            * (bottcherCoord c₁ z) ^ i) 0 U ∧
      s' ⊆ Finset.range (N + 1) ∧ N ∈ s' ∧ 1 ≤ N ∧ B ≠ 0 ∧
      (∀ w : ℂ,
        B.eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 →
          (Q' N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q' i).eval₂ (Polynomial.evalRingHom z) (γ z)) s' w).Separable) := by
  let P := sparseRelationPoly Q s
  have hPzero : ∀ z ∈ U,
      P.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
        (bottcherCoord c₁ z) = 0 := by
    intro z hz
    rw [show P = sparseRelationPoly Q s from rfl, eval_sparseRelationPoly]
    exact hEqOn hz
  have hDrel : Set.EqOn (fun z => ∑ i ∈ D.support,
        (D.coeff i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z) *
          (bottcherCoord c₁ z) ^ i) 0 U := by
    simpa [P] using
      (coeff_family_relation_zero_of_dvd_pow (U := U) P D hdiv hn
        (bottcherCoord c₁) (bottcherCoord c₂) hPzero)
  refine ⟨fun i => D.coeff i, D.support, D.natDegree, squarefreeBadCzY D, ?_, hDrel,
    ?_, ?_, ?_, hB0, ?_⟩
  · exact exists_support_coeff_eval₂_ne_zero_of_transcendental
      hUo hUc hUne hUinf c₂ hU₂ hG hD
  · exact support_subset_range_natDegree_add_one_CzY D
  · exact natDegree_mem_support_of_ne_zero_CzY hD
  · exact one_le_natDegree_of_coeff_family_relation_zero_of_transcendental
      hUo hUc hUne hUinf c₁ c₂ hU₂ hG hD hDrel
  · intro w hB
    exact squarefreeBadCzY_eval₂_ne_zero_topCoeff_and_fibrePoly_separable D γ hB

end Bottcher

namespace Bottcher

/-- Positive `X`-degree makes the derivative leading coefficient nonzero for `C[z][Y][X]`. -/
theorem derivative_leadingCoeff_ne_zero_of_natDegree_pos_CzY
    (F : Polynomial (Polynomial (Polynomial ℂ))) (hdeg : 1 ≤ F.natDegree) :
    (Polynomial.derivative F).leadingCoeff ≠ 0 := by
  have hderiv : Polynomial.derivative F ≠ 0 := by
    intro h
    have := Polynomial.derivative_eq_zero.mp h
    omega
  exact Polynomial.leadingCoeff_ne_zero.mpr hderiv

/-- If the fraction-field `X`-polynomial is separable and `F` has positive degree, then Grok's
squarefree bad-locus product is genuinely nonzero in `C[z][Y]`. -/
theorem squarefreeBadCzY_ne_zero_of_fractionField_separable
    (F : Polynomial (Polynomial (Polynomial ℂ))) (hF : F ≠ 0) (hdeg : 1 ≤ F.natDegree)
    (hsep : (F.map (algebraMap (Polynomial (Polynomial ℂ))
      (FractionRing (Polynomial (Polynomial ℂ))))).Separable) :
    squarefreeBadCzY F ≠ 0 := by
  unfold squarefreeBadCzY
  exact mul_ne_zero
    (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hF)
      (derivative_leadingCoeff_ne_zero_of_natDegree_pos_CzY F hdeg))
    (HolomorphicIFT.resultant_ne_zero_of_separable F hsep)

end Bottcher

namespace Bottcher

/-- Radical coefficient-family producer when the radical divisor is already known to be separable over
`Frac(C[z][Y])`.  This packages the remaining squarefree/localization algebra into one hypothesis. -/
theorem radical_coeff_family_core_with_fractionField_separable_of_sparse_relation
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (γ : ℂ → ℂ)
    (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ)
    (hEqOn : Set.EqOn (fun z => ∑ i ∈ s,
        ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U)
    {D : Polynomial (Polynomial (Polynomial ℂ))} {n : ℕ}
    (hD : D ≠ 0) (hdiv : sparseRelationPoly Q s ∣ D ^ n) (hn : 0 < n)
    (hsep : (D.map (algebraMap (Polynomial (Polynomial ℂ))
      (FractionRing (Polynomial (Polynomial ℂ))))).Separable) :
    ∃ (Q' : ℕ → Polynomial (Polynomial ℂ)) (s' : Finset ℕ) (N : ℕ)
      (B : Polynomial (Polynomial ℂ)),
      (∃ i ∈ s', (Q' i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) ∧
      Set.EqOn (fun z => ∑ i ∈ s',
          ((Q' i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
            * (bottcherCoord c₁ z) ^ i) 0 U ∧
      s' ⊆ Finset.range (N + 1) ∧ N ∈ s' ∧ 1 ≤ N ∧ B ≠ 0 ∧
      (∀ w : ℂ,
        B.eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 →
          (Q' N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q' i).eval₂ (Polynomial.evalRingHom z) (γ z)) s' w).Separable) := by
  let P := sparseRelationPoly Q s
  have hPzero : ∀ z ∈ U,
      P.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
        (bottcherCoord c₁ z) = 0 := by
    intro z hz
    rw [show P = sparseRelationPoly Q s from rfl, eval_sparseRelationPoly]
    exact hEqOn hz
  have hDrel : Set.EqOn (fun z => ∑ i ∈ D.support,
        (D.coeff i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z) *
          (bottcherCoord c₁ z) ^ i) 0 U := by
    simpa [P] using
      (coeff_family_relation_zero_of_dvd_pow (U := U) P D hdiv hn
        (bottcherCoord c₁) (bottcherCoord c₂) hPzero)
  have hdeg : 1 ≤ D.natDegree :=
    one_le_natDegree_of_coeff_family_relation_zero_of_transcendental
      hUo hUc hUne hUinf c₁ c₂ hU₂ hG hD hDrel
  exact radical_coeff_family_core_with_squarefreeBadCzY_of_sparse_relation
    hUo hUc hUne hUinf c₁ c₂ hU₂ hG γ Q s hEqOn hD hdiv hn
    (squarefreeBadCzY_ne_zero_of_fractionField_separable D hD hdeg hsep)

end Bottcher

namespace Bottcher

open scoped nonZeroDivisors Polynomial

/-- Clearing denominators and taking primitive part gives a polynomial associated to the original
fraction-field polynomial.  This is the denominator-clearing half of the squarefree-localization lead. -/
theorem fractionField_integerNormalization_primPart_associated_CzY
    (q : (FractionRing (Polynomial (Polynomial ℂ)))[X]) (hq0 : q ≠ 0) :
    Associated
      ((IsLocalization.integerNormalization (nonZeroDivisors (Polynomial (Polynomial ℂ))) q).primPart.map
        (algebraMap (Polynomial (Polynomial ℂ)) (FractionRing (Polynomial (Polynomial ℂ)))))
      q := by
  let R := Polynomial (Polynomial ℂ)
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  let g : R[X] := IsLocalization.integerNormalization (nonZeroDivisors R) q
  have hg0 : g ≠ 0 := by
    change IsLocalization.integerNormalization (nonZeroDivisors R) q ≠ 0
    intro h
    exact hq0 (IsFractionRing.integerNormalization_eq_zero_iff.mp h)
  have hcont0 : g.content ≠ 0 := by
    intro h
    exact hg0 (Polynomial.content_eq_zero_iff.mp h)
  obtain ⟨b, hbmem, hbmap⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) q
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero hbmem
  have hbmap' : g.map φ = Polynomial.C (φ b) * q := by
    simpa [g, R, K, φ, Algebra.smul_def] using hbmap
  have hgfactor : g.map φ = Polynomial.C (φ g.content) * g.primPart.map φ := by
    rw [← Polynomial.map_C, ← Polynomial.map_mul, ← Polynomial.eq_C_content_mul_primPart]
  have hbunit : IsUnit (Polynomial.C (φ b) : K[X]) := by
    exact Polynomial.isUnit_C.mpr
      (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff φ (IsFractionRing.injective R K)).mpr hb0))
  have hcunit : IsUnit (Polynomial.C (φ g.content) : K[X]) := by
    exact Polynomial.isUnit_C.mpr
      (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff φ (IsFractionRing.injective R K)).mpr hcont0))
  have h1 : Associated (g.map φ) q := by
    rw [hbmap']
    exact associated_unit_mul_left q (Polynomial.C (φ b)) hbunit
  have h2 : Associated (g.map φ) (g.primPart.map φ) := by
    rw [hgfactor]
    exact associated_unit_mul_left (g.primPart.map φ) (Polynomial.C (φ g.content)) hcunit
  exact h2.symm.trans h1

/-- Over the fraction field, a nonzero polynomial is associated to its primitive part. -/
theorem fractionField_primPart_associated_CzY
    (D : Polynomial (Polynomial (Polynomial ℂ))) (hD0 : D ≠ 0) :
    Associated
      (D.primPart.map
        (algebraMap (Polynomial (Polynomial ℂ)) (FractionRing (Polynomial (Polynomial ℂ)))))
      (D.map (algebraMap (Polynomial (Polynomial ℂ))
        (FractionRing (Polynomial (Polynomial ℂ))))) := by
  let R := Polynomial (Polynomial ℂ)
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  have hcont0 : D.content ≠ 0 := by
    intro h
    exact hD0 (Polynomial.content_eq_zero_iff.mp h)
  have hfactor : D.map φ = Polynomial.C (φ D.content) * D.primPart.map φ := by
    rw [← Polynomial.map_C, ← Polynomial.map_mul, ← Polynomial.eq_C_content_mul_primPart]
  have hcunit : IsUnit (Polynomial.C (φ D.content) : K[X]) := by
    exact Polynomial.isUnit_C.mpr
      (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff φ (IsFractionRing.injective R K)).mpr hcont0))
  have h : Associated (D.map φ) (D.primPart.map φ) := by
    rw [hfactor]
    exact associated_unit_mul_left (D.primPart.map φ) (Polynomial.C (φ D.content)) hcunit
  exact h.symm

end Bottcher

namespace Bottcher

open scoped nonZeroDivisors Polynomial

/-- Squarefreeness over `C[z][Y][X]` survives passage to the fraction field in the coefficient ring.
This is the Gauss/primitive-part implementation of Grok's localization lead. -/
theorem fractionField_squarefree_of_squarefree_CzY
    (D : Polynomial (Polynomial (Polynomial ℂ))) (hDsq : Squarefree D) :
    Squarefree (D.map (algebraMap (Polynomial (Polynomial ℂ))
      (FractionRing (Polynomial (Polynomial ℂ))))) := by
  let R := Polynomial (Polynomial ℂ)
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  change Squarefree (D.map φ)
  intro q hqdiv
  by_cases hq0 : q = 0
  · exfalso
    have hD0 : D ≠ 0 := hDsq.ne_zero
    have hmapD0 : D.map φ ≠ 0 := by
      exact (Polynomial.map_eq_zero_iff (IsFractionRing.injective R K)).not.mpr hD0
    have hzero : D.map φ = 0 := by
      rcases hqdiv with ⟨a, ha⟩
      rw [hq0, zero_mul, zero_mul] at ha
      exact ha
    exact hmapD0 hzero
  · let g : R[X] := IsLocalization.integerNormalization (nonZeroDivisors R) q
    let gp : R[X] := g.primPart
    have hD0 : D ≠ 0 := hDsq.ne_zero
    have hDprim_sq : Squarefree D.primPart :=
      hDsq.squarefree_of_dvd (Polynomial.primPart_dvd D)
    have hgp_prim : gp.IsPrimitive := by
      dsimp [gp]
      exact Polynomial.isPrimitive_primPart g
    have hgp2_prim : (gp * gp).IsPrimitive := hgp_prim.mul hgp_prim
    have hassoc_q : Associated (gp.map φ) q := by
      simpa [g, gp, R, K, φ] using fractionField_integerNormalization_primPart_associated_CzY q hq0
    have hassoc_q2 : Associated ((gp * gp).map φ) (q * q) := by
      rw [Polynomial.map_mul]
      exact (Associated.mul_left (gp.map φ) hassoc_q).trans (hassoc_q.mul_right q)
    have hassoc_D : Associated (D.primPart.map φ) (D.map φ) := by
      simpa [R, K, φ] using fractionField_primPart_associated_CzY D hD0
    have hmap_dvd : (gp * gp).map φ ∣ D.primPart.map φ := by
      exact (hassoc_q2.dvd_iff_dvd_left).mpr ((hassoc_D.dvd_iff_dvd_right).mpr hqdiv)
    have hgp2_dvd : gp * gp ∣ D.primPart := by
      exact (hgp2_prim.dvd_iff_fraction_map_dvd_fraction_map K).mpr hmap_dvd
    have hgp_unit : IsUnit gp := hDprim_sq gp hgp2_dvd
    simpa [g, gp, R, K] using
      (Polynomial.isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart hq0 hgp_unit)

/-- A squarefree `C[z][Y][X]` polynomial is separable after base-change to `Frac(C[z][Y])`. -/
theorem fractionField_separable_of_squarefree_CzY
    (D : Polynomial (Polynomial (Polynomial ℂ))) (hDsq : Squarefree D) :
    (D.map (algebraMap (Polynomial (Polynomial ℂ))
      (FractionRing (Polynomial (Polynomial ℂ))))).Separable := by
  exact PerfectField.separable_iff_squarefree.mpr
    (fractionField_squarefree_of_squarefree_CzY D hDsq)

end Bottcher

namespace Bottcher

/-- Full primitive/squarefree bad-locus producer from the raw sparse relation.  This closes the algebraic
producer required by the q62 primitive/squarefree endpoint: take the squarefree radical divisor, use
Gauss/localization to get fraction-field separability, and use the Grok bad-locus product as `B`. -/
theorem primitiveSqfreeBad_of_sparse_relation
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (γ : ℂ → ℂ)
    (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ)
    (hnt : ∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0)
    (hEqOn : Set.EqOn (fun z => ∑ i ∈ s,
        ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U) :
    ∃ (Q' : ℕ → Polynomial (Polynomial ℂ)) (s' : Finset ℕ) (N : ℕ)
      (B : Polynomial (Polynomial ℂ)),
      (∃ i ∈ s', (Q' i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) ∧
      Set.EqOn (fun z => ∑ i ∈ s',
          ((Q' i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
            * (bottcherCoord c₁ z) ^ i) 0 U ∧
      s' ⊆ Finset.range (N + 1) ∧ N ∈ s' ∧ 1 ≤ N ∧ B ≠ 0 ∧
      (∀ w : ℂ,
        B.eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 →
          (Q' N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q' i).eval₂ (Polynomial.evalRingHom z) (γ z)) s' w).Separable) := by
  let P := sparseRelationPoly Q s
  have hP0 : P ≠ 0 := by
    simpa [P] using sparseRelationPoly_ne_zero_of_hnt (U := U) c₂ hU₂ Q s hnt
  have hPzero : ∀ z ∈ U,
      P.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
        (bottcherCoord c₁ z) = 0 := by
    intro z hz
    rw [show P = sparseRelationPoly Q s from rfl, eval_sparseRelationPoly]
    exact hEqOn hz
  have hPrel : Set.EqOn (fun z => ∑ i ∈ P.support,
        ((P.coeff i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U := by
    intro z hz
    change (∑ i ∈ P.support,
        ((P.coeff i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) = 0
    rw [← eval_sparseRelationPoly (fun i => P.coeff i) P.support z
      (bottcherCoord c₂ z) (bottcherCoord c₁ z)]
    rw [sparseRelationPoly_coeff_support_eq P]
    exact hPzero z hz
  have hPdeg : 1 ≤ P.natDegree :=
    one_le_natDegree_of_coeff_family_relation_zero_of_transcendental
      hUo hUc hUne hUinf c₁ c₂ hU₂ hG hP0 hPrel
  obtain ⟨D, n, hD0, hDsq, _hDP, hPD⟩ := exists_squarefree_divisor_pow_CzY P hP0
  have hn : 0 < n := by
    cases n with
    | zero =>
        have hP_dvd_one : P ∣ (1 : Polynomial (Polynomial (Polynomial ℂ))) := by
          simpa using hPD
        have hdeg0 : P.natDegree = 0 := by
          have hle : P.natDegree ≤ (1 : Polynomial (Polynomial (Polynomial ℂ))).natDegree :=
            Polynomial.natDegree_le_of_dvd hP_dvd_one (by simp)
          simpa using hle
        omega
    | succ n => omega
  exact radical_coeff_family_core_with_fractionField_separable_of_sparse_relation
    hUo hUc hUne hUinf c₁ c₂ hU₂ hG γ Q s hEqOn hD0 hPD hn
    (fractionField_separable_of_squarefree_CzY D hDsq)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **Function-level no-relation from `phiMero` transcendence.**
This is the reverse use of the analytic-subring bridge: a pointwise vanishing relation on `U` would
make `q.eval₂ (polyToAnalytic U) (phiAnalytic c hU)` zero, contradicting transcendence unless
`q = 0`. -/
theorem no_eval₂_bottcher_relation_of_phiMero_transcendental
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c hU)) :
    ∀ q : Polynomial (Polynomial ℂ), q ≠ 0 →
      ¬ Set.EqOn (fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z)) 0 U := by
  intro q hq hEq
  have hzero : q.eval₂ (polyToAnalytic U) (phiAnalytic c hU) = 0 :=
    eval₂_polyToAnalytic_eq_zero_of_eqOn_bridge (c := c) (hU := hU) q hEq
  have hqzero : q = 0 :=
    (eval₂_polyToAnalytic_phiAnalytic_eq_zero_iff_of_transcendental
      hUo hUc hUne hUinf c hU hG q).mp hzero
  exact hq hqzero

end Bottcher
