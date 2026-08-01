import GaloisForLFunctions.HTGeometry.DigammaFieldJetPresentation
import GaloisForLFunctions.HTGeometry.RatCoeffJetPoly
import GaloisForLFunctions.HTGeometry.RatCoeffClearing

/-!
# The digamma field over the rational base

Adjoining the digamma jets to `ℂ(s)` instead of `ℂ` changes nothing essential: an element of the jet
algebra over `ℂ(s)` becomes, after multiplication by one nonzero polynomial, a jet polynomial with
polynomial coefficients — an analytic germ whose values on the line are an explicit polynomial in the
polygammas with polynomial coefficients.
-/

open Filter Set Topology Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance digammaRatDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance digammaRatDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance digammaRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

/-- **A jet-algebra element over the rational base, cleared to polynomial coefficients.** -/
theorem exists_ratAlgebra_analytic {y : upperEndMeroField}
    (hy : y ∈ differentialJetAlgebra (RatFunc ℂ) ({digammaMero} : Set upperEndMeroField)) :
    ∃ (q : Polynomial ℂ) (M K : ℕ) (p : Fin M → Polynomial ℂ) (E : Fin M → Fin (K + 1) → ℕ)
      (A : upperEndAnalyticSubring),
      q ≠ 0 ∧ Function.Injective E
        ∧ upperEndPolyToMero q * y = algebraMap upperEndAnalyticSubring upperEndMeroField A
        ∧ upperEndAnalyticSubring.subtype A = Germ.coeRingHom upperEndFilter
            (fun z : ℂ => ∑ α : Fin M, (p α).eval z
              * ∏ j : Fin (K + 1), iteratedDeriv (j : ℕ) Complex.digamma z ^ E α j) := by
  classical
  obtain ⟨M, N, b, e, h, hb, hh, hhinj, heinj, hy'⟩ :=
    exists_fin_jetPoly_of_mem_algebra_inj (F := RatFunc ℂ) hy
  rw [differentialJetSet_digamma] at hh
  choose k hk using hb
  choose n hn using hh
  have hninj : Function.Injective n := by
    intro i i' hii'
    refine hhinj ?_
    rw [← hn i, ← hn i', hii']
  obtain ⟨q, p, hq0, hqp⟩ := exists_common_denom_poly k
  obtain ⟨K, E, hEinj, hE⟩ :=
    exists_canonical_exponents_family_inj (R := upperEndMeroField) digammaJetMero n hninj e heinj
  obtain ⟨A, hA, hgerm⟩ := exists_jetPolyPoly_analytic p E (fun j : Fin (K + 1) => (j : ℕ))
  refine ⟨q, M, K, p, E, A, hq0, hEinj, ?_, hgerm⟩
  rw [← hA, hy', Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hcoeff : upperEndPolyToMero q * b α = upperEndPolyToMero (p α) := by
    rw [← hk α]
    have h1 : upperEndPolyToMero q
        = upperEndRatfuncToMero (algebraMap (Polynomial ℂ) (RatFunc ℂ) q) :=
      (upperEndRatfuncToMero_algebraMap_polynomial q).symm
    have h2 : (algebraMap (RatFunc ℂ) upperEndMeroField) (k α) = upperEndRatfuncToMero (k α) := rfl
    rw [h1, h2, ← map_mul, hqp α, upperEndRatfuncToMero_algebraMap_polynomial]
  rw [← mul_assoc, hcoeff, ← hE α]
  exact congrArg _ (Finset.prod_congr rfl fun i _ => by rw [hn i])

/-- **The datum of a nonzero analytic jet polynomial with polynomial coefficients.** -/
theorem exists_polyCoeff_jet_datum {σ : ℝ} (hσ : 0 < σ) {M K : ℕ} (p : Fin M → Polynomial ℂ)
    (E : Fin M → Fin (K + 1) → ℕ) (hE : Function.Injective E) {A : upperEndAnalyticSubring}
    (hA0 : A ≠ 0)
    (hgerm : upperEndAnalyticSubring.subtype A = Germ.coeRingHom upperEndFilter
      (fun z : ℂ => ∑ α : Fin M, (p α).eval z
        * ∏ j : Fin (K + 1), iteratedDeriv (j : ℕ) Complex.digamma z ^ E α j)) :
    ∃ (a d b : ℕ) (r : ℂ), r ≠ 0 ∧ Tendsto (fun t : ℝ =>
      (∑ α : Fin M, (p α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        * ∏ j : Fin (K + 1), iteratedDeriv (j : ℕ) Complex.digamma
          ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E α j)
        / polyJetShape σ a d b t) atTop (nhds r) := by
  classical
  obtain ⟨M', ι, hιinj, hιmem, hιsurj, hsum⟩ :=
    exists_fin_reindex_of_finset (A := ℂ → ℂ) (Finset.univ.filter (fun α => p α ≠ 0))
      (fun α => fun z : ℂ => (p α).eval z
        * ∏ j : Fin (K + 1), iteratedDeriv (j : ℕ) Complex.digamma z ^ E α j)
  have hrestrict : ∑ α ∈ Finset.univ.filter (fun α => p α ≠ 0),
      (fun z : ℂ => (p α).eval z
        * ∏ j : Fin (K + 1), iteratedDeriv (j : ℕ) Complex.digamma z ^ E α j)
      = ∑ α : Fin M, (fun z : ℂ => (p α).eval z
        * ∏ j : Fin (K + 1), iteratedDeriv (j : ℕ) Complex.digamma z ^ E α j) := by
    refine Finset.sum_subset (Finset.subset_univ _) fun α _ hα => ?_
    have hp0 : p α = 0 := by
      by_contra hne
      exact hα (Finset.mem_filter.mpr ⟨Finset.mem_univ α, hne⟩)
    funext z
    simp [hp0]
  have hpne : ∀ j : Fin M', p (ι j) ≠ 0 := fun j => (Finset.mem_filter.mp (hιmem j)).2
  have hfun : ∀ z : ℂ, (∑ α : Fin M, (p α).eval z
        * ∏ j : Fin (K + 1), iteratedDeriv (j : ℕ) Complex.digamma z ^ E α j)
      = ∑ j : Fin M', (p (ι j)).eval z
        * ∏ i : Fin (K + 1), iteratedDeriv (i : ℕ) Complex.digamma z ^ E (ι j) i := by
    intro z
    have hz := congrFun (hrestrict.symm.trans hsum) z
    simpa [Finset.sum_apply] using hz
  have hM'pos : 0 < M' := by
    rcases Nat.eq_zero_or_pos M' with h0 | h
    · exfalso
      refine hA0 (Subtype.ext ?_)
      show upperEndAnalyticSubring.subtype A = 0
      rw [hgerm]
      have hzero : (fun z : ℂ => ∑ α : Fin M, (p α).eval z
          * ∏ j : Fin (K + 1), iteratedDeriv (j : ℕ) Complex.digamma z ^ E α j) = 0 := by
        funext z
        rw [hfun z]
        subst h0
        simp
      rw [hzero]
      exact map_zero (Germ.coeRingHom upperEndFilter)
    · exact h
  set d : ℕ := Finset.univ.sup (fun j : Fin M' => (p (ι j)).natDegree) with hd
  obtain ⟨a, b, r, hr, hlim⟩ :=
    exists_full_jetPolyCoeff_datum hσ hM'pos (fun j => p (ι j))
      (fun j => Finset.le_sup (f := fun j' : Fin M' => (p (ι j')).natDegree)
        (Finset.mem_univ j)) (fun j => E (ι j)) hpne
      (fun j k hjk => hιinj (hE hjk))
  refine ⟨a, d, b, r, hr, ?_⟩
  have hshift := tendsto_div_polyJetShape_num_pow (K := d) hσ hlim
  refine hshift.congr' ?_
  filter_upwards [eventually_vertical_ne_zero σ] with t hs
  have hpow : ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d ≠ 0 := pow_ne_zero _ hs
  congr 1
  rw [hfun ((σ : ℂ) + (t : ℂ) * Complex.I), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp
  ring

/-- **Every nonzero element of the digamma field over the rational base has a datum.**  Clearing the
coefficient denominators and the field denominator presents the element as a quotient of two jet
polynomials with polynomial coefficients, each with its own residue. -/
theorem exists_digamma_ratField_datum {σ : ℝ} (hσ : 0 < σ) {x : upperEndMeroField}
    (hx : x ∈ differentialAdjoin (RatFunc ℂ) ({digammaMero} : Set upperEndMeroField))
    (hx0 : x ≠ 0) :
    ∃ (M₁ K₁ a₁ d₁ b₁ M₂ K₂ a₂ d₂ b₂ : ℕ) (p₁ : Fin M₁ → Polynomial ℂ)
      (E₁ : Fin M₁ → Fin (K₁ + 1) → ℕ) (p₂ : Fin M₂ → Polynomial ℂ)
      (E₂ : Fin M₂ → Fin (K₂ + 1) → ℕ) (r : ℂ) (U V : upperEndAnalyticSubring),
      r ≠ 0 ∧ V ≠ 0
        ∧ x = algebraMap upperEndAnalyticSubring upperEndMeroField U
            / algebraMap upperEndAnalyticSubring upperEndMeroField V
        ∧ upperEndAnalyticSubring.subtype U = Germ.coeRingHom upperEndFilter
            (fun z : ℂ => ∑ α : Fin M₁, (p₁ α).eval z
              * ∏ j : Fin (K₁ + 1), iteratedDeriv (j : ℕ) Complex.digamma z ^ E₁ α j)
        ∧ upperEndAnalyticSubring.subtype V = Germ.coeRingHom upperEndFilter
            (fun z : ℂ => ∑ α : Fin M₂, (p₂ α).eval z
              * ∏ j : Fin (K₂ + 1), iteratedDeriv (j : ℕ) Complex.digamma z ^ E₂ α j)
        ∧ Tendsto (fun t : ℝ =>
            ((∑ α : Fin M₁, (p₁ α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
              * ∏ j : Fin (K₁ + 1), iteratedDeriv (j : ℕ) Complex.digamma
                ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E₁ α j) / polyJetShape σ a₁ d₁ b₁ t)
            / ((∑ α : Fin M₂, (p₂ α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
              * ∏ j : Fin (K₂ + 1), iteratedDeriv (j : ℕ) Complex.digamma
                ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E₂ α j) / polyJetShape σ a₂ d₂ b₂ t))
          atTop (nhds r) := by
  classical
  obtain ⟨D, hDmem, hD0, hxD⟩ := exists_jetAlgebra_denominator (F := RatFunc ℂ) hx
  obtain ⟨q₁, M₁, K₁, p, E₁, U₀, hq₁, hE₁, hU₀, hgU₀⟩ := exists_ratAlgebra_analytic hxD
  obtain ⟨q₂, M₂, K₂, w, E₂, V₀, hq₂, hE₂, hV₀, hgV₀⟩ := exists_ratAlgebra_analytic hDmem
  have hq₁mero : upperEndPolyToMero q₁ ≠ 0 := fun h =>
    hq₁ (upperEndPolyToMero_injective (by rw [h, map_zero]))
  have hq₂mero : upperEndPolyToMero q₂ ≠ 0 := fun h =>
    hq₂ (upperEndPolyToMero_injective (by rw [h, map_zero]))
  have hxD0 : x * D ≠ 0 := mul_ne_zero hx0 hD0
  have hpolyimg : ∀ q : Polynomial ℂ,
      algebraMap upperEndAnalyticSubring upperEndMeroField (upperEndPolyToAnalytic q)
        = upperEndPolyToMero q := fun _ => rfl
  have hUimg : algebraMap upperEndAnalyticSubring upperEndMeroField
      (U₀ * upperEndPolyToAnalytic q₂)
      = upperEndPolyToMero q₁ * (x * D) * upperEndPolyToMero q₂ := by
    rw [map_mul, ← hU₀, hpolyimg]
  have hVimg : algebraMap upperEndAnalyticSubring upperEndMeroField
      (V₀ * upperEndPolyToAnalytic q₁)
      = upperEndPolyToMero q₂ * D * upperEndPolyToMero q₁ := by
    rw [map_mul, ← hV₀, hpolyimg]
  have hV0 : V₀ * upperEndPolyToAnalytic q₁ ≠ 0 := by
    intro h
    rw [h, map_zero] at hVimg
    exact (mul_ne_zero (mul_ne_zero hq₂mero hD0) hq₁mero) hVimg.symm
  have hU0 : U₀ * upperEndPolyToAnalytic q₂ ≠ 0 := by
    intro h
    rw [h, map_zero] at hUimg
    exact (mul_ne_zero (mul_ne_zero hq₁mero hxD0) hq₂mero) hUimg.symm
  have hxeq : x = algebraMap upperEndAnalyticSubring upperEndMeroField
        (U₀ * upperEndPolyToAnalytic q₂)
      / algebraMap upperEndAnalyticSubring upperEndMeroField
        (V₀ * upperEndPolyToAnalytic q₁) := by
    rw [hUimg, hVimg]
    field_simp
  have hgU : upperEndAnalyticSubring.subtype (U₀ * upperEndPolyToAnalytic q₂)
      = Germ.coeRingHom upperEndFilter
        (fun z : ℂ => ∑ α : Fin M₁, (q₂ * p α).eval z
          * ∏ j : Fin (K₁ + 1), iteratedDeriv (j : ℕ) Complex.digamma z ^ E₁ α j) := by
    rw [map_mul, hgU₀, polyToAnalytic_subtype, ← map_mul]
    congr 1
    funext z
    simp only [Pi.mul_apply, Polynomial.eval_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun α _ => by ring
  have hgV : upperEndAnalyticSubring.subtype (V₀ * upperEndPolyToAnalytic q₁)
      = Germ.coeRingHom upperEndFilter
        (fun z : ℂ => ∑ α : Fin M₂, (q₁ * w α).eval z
          * ∏ j : Fin (K₂ + 1), iteratedDeriv (j : ℕ) Complex.digamma z ^ E₂ α j) := by
    rw [map_mul, hgV₀, polyToAnalytic_subtype, ← map_mul]
    congr 1
    funext z
    simp only [Pi.mul_apply, Polynomial.eval_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun α _ => by ring
  obtain ⟨a₁, d₁, b₁, r₁, hr₁, hlim₁⟩ :=
    exists_polyCoeff_jet_datum hσ (fun α => q₂ * p α) E₁ hE₁ hU0 hgU
  obtain ⟨a₂, d₂, b₂, r₂, hr₂, hlim₂⟩ :=
    exists_polyCoeff_jet_datum hσ (fun α => q₁ * w α) E₂ hE₂ hV0 hgV
  have hquot : Tendsto (fun t : ℝ =>
      ((∑ α : Fin M₁, (q₂ * p α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        * ∏ j : Fin (K₁ + 1), iteratedDeriv (j : ℕ) Complex.digamma
          ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E₁ α j) / polyJetShape σ a₁ d₁ b₁ t)
      / ((∑ α : Fin M₂, (q₁ * w α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        * ∏ j : Fin (K₂ + 1), iteratedDeriv (j : ℕ) Complex.digamma
          ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E₂ α j) / polyJetShape σ a₂ d₂ b₂ t))
      atTop (nhds (r₁ / r₂)) := hlim₁.div hlim₂ hr₂
  exact ⟨M₁, K₁, a₁, d₁, b₁, M₂, K₂, a₂, d₂, b₂, fun α => q₂ * p α, E₁, fun α => q₁ * w α, E₂,
    r₁ / r₂, U₀ * upperEndPolyToAnalytic q₂, V₀ * upperEndPolyToAnalytic q₁,
    div_ne_zero hr₁ hr₂, hV0, hxeq, hgU, hgV, hquot⟩

end

end GaloisForLFunctions.HTGeometry
