import GaloisForLFunctions.HTGeometry.GammaLineRepresentative
import GaloisForLFunctions.HTGeometry.GammaFieldGeneratedByDigamma
import GaloisForLFunctions.HTGeometry.DigammaRationalFieldDatum

/-!
# The Gamma exponent of the boundary datum, and transcendence of Gamma over the digamma field

The first component of the datum of eq. (3) is the `Γ`-exponent.  It is additive on products and
takes the value `1` at `Γ`; on the digamma field `L = ℂ(s)⟨ψ⟩` it is `0`, because an element of `L`
is a quotient of jet polynomials whose asymptotics carry no `Γ` factor.

That is exactly what makes `Γ` transcendental over `L`: in a polynomial relation `∑ A_i Γ^i = 0` the
terms have pairwise distinct `Γ`-exponents `i`, so the lowest one dominates all the others and the
sum cannot vanish.
-/

open Filter Set Topology Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance gammaValDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance gammaValIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance gammaValDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance gammaValComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance gammaValRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance gammaValRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance gammaValRatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

/-- The jet shape without a Gamma factor is the integer shape with Gamma exponent zero. -/
theorem polyJetShape_eq_gammaShapeZ {σ : ℝ} (a dP b : ℕ) :
    ∀ᶠ t : ℝ in atTop,
      polyJetShape σ a dP b t = gammaShapeZ σ 0 ((dP : ℤ) - (b : ℤ)) (a : ℤ) t := by
  filter_upwards [gammaJetShape_eq_gammaShapeZ (σ := σ) 0 a dP b] with t ht
  rw [Nat.cast_zero] at ht
  rw [← ht, gammaJetShape, pow_zero, one_mul]

/-- A representative of zero vanishes eventually on the line. -/
theorem representsOnLine_zero_eventually {σ : ℝ} {χ : ℝ → ℂ}
    (h : RepresentsOnLine σ (0 : upperEndMeroField) χ) : ∀ᶠ t : ℝ in atTop, χ t = 0 := by
  obtain ⟨U, V, G, H, hUg, hVg, hV0, hxeq, hχ⟩ := h
  have hU0 : U = 0 := by
    have : algebraMap upperEndAnalyticSubring upperEndMeroField U = 0 := by
      by_contra hne
      exact hne ((div_eq_zero_iff.mp hxeq.symm).resolve_right hV0)
    exact IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField
      (by rw [this, map_zero])
  have hgerm : Germ.coeRingHom upperEndFilter G = 0 := by
    rw [← hUg, hU0, map_zero]
  rw [← Germ.coe_zero] at hgerm
  have hev : ∀ᶠ z : ℂ in upperEndFilter, G z = (0 : ℂ → ℂ) z := Filter.Germ.coe_eq.mp hgerm
  filter_upwards [eventually_line_of_upperEnd hev σ] with t ht
  rw [hχ t, ht]
  simp

/-- **The datum of an element of the digamma field has Gamma exponent zero.** -/
theorem exists_digammaField_intDatum {σ : ℝ} (hσ : 0 < σ) {x : upperEndMeroField}
    (hx : x ∈ differentialAdjoin (RatFunc ℂ) ({digammaMero} : Set upperEndMeroField))
    (hx0 : x ≠ 0) :
    ∃ (a b : ℤ) (φ : ℝ → ℂ) (c : ℂ),
      c ≠ 0 ∧ RepresentsOnLine σ x φ
        ∧ Tendsto (fun t : ℝ => φ t / gammaShapeZ σ 0 a b t) atTop (nhds c) := by
  classical
  obtain ⟨M₁, K₁, a₁, d₁, b₁, M₂, K₂, a₂, d₂, b₂, p₁, E₁, p₂, E₂, r, U, V,
    hr, hV0, hxeq, hUg, hVg, hlim⟩ := exists_digamma_ratField_datum hσ hx hx0
  set G : ℂ → ℂ := fun z => ∑ α : Fin M₁, (p₁ α).eval z
    * ∏ j : Fin (K₁ + 1), iteratedDeriv (j : ℕ) Complex.digamma z ^ E₁ α j with hG
  set H : ℂ → ℂ := fun z => ∑ α : Fin M₂, (p₂ α).eval z
    * ∏ j : Fin (K₂ + 1), iteratedDeriv (j : ℕ) Complex.digamma z ^ E₂ α j with hH
  have hVmero : algebraMap upperEndAnalyticSubring upperEndMeroField V ≠ 0 := by
    intro h0
    exact hV0 (IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField
      (by rw [h0, map_zero]))
  refine ⟨((d₁ : ℤ) - (b₁ : ℤ)) - ((d₂ : ℤ) - (b₂ : ℤ)), (a₁ : ℤ) - (a₂ : ℤ),
    fun t => G ((σ : ℂ) + (t : ℂ) * Complex.I) / H ((σ : ℂ) + (t : ℂ) * Complex.I), r, hr,
    ⟨U, V, G, H, hUg, hVg, hVmero, hxeq, fun t => rfl⟩, ?_⟩
  have hlim' : Tendsto (fun t : ℝ =>
      (G ((σ : ℂ) + (t : ℂ) * Complex.I) / polyJetShape σ a₁ d₁ b₁ t)
        / (H ((σ : ℂ) + (t : ℂ) * Complex.I) / polyJetShape σ a₂ d₂ b₂ t)) atTop (nhds r) := hlim
  refine hlim'.congr' ?_
  filter_upwards [polyJetShape_eq_gammaShapeZ (σ := σ) a₁ d₁ b₁,
    polyJetShape_eq_gammaShapeZ (σ := σ) a₂ d₂ b₂,
    eventually_gammaShapeZ_ne_zero (σ := σ) hσ 0 ((d₁ : ℤ) - (b₁ : ℤ)) (a₁ : ℤ),
    eventually_gammaShapeZ_ne_zero (σ := σ) hσ 0 ((d₂ : ℤ) - (b₂ : ℤ)) (a₂ : ℤ),
    gammaShapeZ_div (σ := σ) hσ 0 ((d₁ : ℤ) - (b₁ : ℤ)) (a₁ : ℤ)
      0 ((d₂ : ℤ) - (b₂ : ℤ)) (a₂ : ℤ)] with t hS₁ hS₂ hne₁ hne₂ hdiv
  simp only [sub_zero] at hdiv
  rw [hS₁, hS₂, ← hdiv]
  by_cases hH0 : H ((σ : ℂ) + (t : ℂ) * Complex.I) = 0
  · simp only [hH0, zero_div, div_zero]
  · field_simp

/-- Gamma is represented on the line by itself, with datum `(1, 0, 0)` and residue `1`. -/
theorem tendsto_gammaLine_div_gammaShapeZ {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ => gammaLine σ t / gammaShapeZ σ 1 0 0 t) atTop (nhds 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_vertLog_ne_zero, eventually_vertical_ne_zero σ] with t hL hs
  have hΓ : gammaLine σ t ≠ 0 := gammaLine_ne_zero hσ t
  rw [gammaShapeZ, zpow_zero, zpow_zero, zpow_one, mul_one, mul_one, div_self hΓ]

theorem representsOnLine_gammaUpperMero {σ : ℝ} :
    RepresentsOnLine σ gammaUpperMero (fun t : ℝ => gammaLine σ t) :=
  representsOnLine_algebraMap gammaUpperAnalytic Complex.Gamma rfl

/-- A power of Gamma has datum `(n, 0, 0)` and residue `1`. -/
theorem tendsto_gammaLine_pow_div_gammaShapeZ {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    Tendsto (fun t : ℝ => gammaLine σ t ^ n / gammaShapeZ σ (n : ℤ) 0 0 t) atTop (nhds 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_vertLog_ne_zero, eventually_vertical_ne_zero σ] with t hL hs
  have hΓ : gammaLine σ t ≠ 0 := gammaLine_ne_zero hσ t
  rw [gammaShapeZ, zpow_zero, zpow_zero, mul_one, mul_one, zpow_natCast, div_self (pow_ne_zero _ hΓ)]

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance gammaTrDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance gammaTrIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance gammaTrDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance gammaTrComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance gammaTrRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance gammaTrRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance gammaTrRatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

/-- **Equation (22): Gamma is transcendental over the digamma field.**  In a polynomial relation
`∑ A_i Γ^i = 0` with coefficients in `ℂ(s)⟨ψ⟩` the terms have pairwise distinct `Γ`-exponents, so the
lowest one dominates every other on a vertical line and the sum cannot vanish. -/
theorem transcendental_gammaUpperMero_over_digammaField :
    Transcendental
      ↥(differentialAdjoin (RatFunc ℂ) ({digammaMero} : Set upperEndMeroField))
      gammaUpperMero := by
  classical
  intro halg
  obtain ⟨p, hp0, hproot⟩ := halg
  have hσ : (0 : ℝ) < 1 := one_pos
  -- index the support
  set S : Finset ℕ := p.support with hS
  have hSne : S.Nonempty := by
    rw [hS, Finset.nonempty_iff_ne_empty]
    intro hempty
    exact hp0 (Polynomial.support_eq_empty.mp hempty)
  set N : ℕ := S.card with hN
  have hNpos : 0 < N := Finset.card_pos.mpr hSne
  set idx : Fin N → ℕ := fun α => ((S.equivFin.symm α : {n // n ∈ S}) : ℕ) with hidx
  have hidxmem : ∀ α, idx α ∈ S := fun α => (S.equivFin.symm α).2
  have hidxinj : Function.Injective idx := by
    intro α β hab
    exact S.equivFin.symm.injective (Subtype.ext hab)
  -- the coefficients and their data
  have hcoeff0 : ∀ α : Fin N, p.coeff (idx α) ≠ 0 := fun α =>
    Polynomial.mem_support_iff.mp (hidxmem α)
  have hAmem : ∀ α : Fin N, (algebraMap
      ↥(differentialAdjoin (RatFunc ℂ) ({digammaMero} : Set upperEndMeroField))
      upperEndMeroField (p.coeff (idx α)))
      ∈ differentialAdjoin (RatFunc ℂ) ({digammaMero} : Set upperEndMeroField) :=
    fun α => (p.coeff (idx α)).2
  have hA0 : ∀ α : Fin N, (algebraMap
      ↥(differentialAdjoin (RatFunc ℂ) ({digammaMero} : Set upperEndMeroField))
      upperEndMeroField (p.coeff (idx α))) ≠ 0 := by
    intro α h0
    exact hcoeff0 α (Subtype.ext h0)
  choose a b φ c hc hrep hlim using fun α : Fin N =>
    exists_digammaField_intDatum (σ := 1) hσ (hAmem α) (hA0 α)
  -- the terms, their representatives and their data
  set x : Fin N → upperEndMeroField := fun α =>
    algebraMap ↥(differentialAdjoin (RatFunc ℂ) ({digammaMero} : Set upperEndMeroField))
      upperEndMeroField (p.coeff (idx α)) * gammaUpperMero ^ (idx α) with hx
  set Φ : Fin N → ℝ → ℂ := fun α t => φ α t * gammaLine 1 t ^ (idx α) with hΦ
  have hxrep : ∀ α, RepresentsOnLine 1 (x α) (Φ α) := fun α =>
    (hrep α).mul (representsOnLine_gammaUpperMero.pow (idx α))
  have hxlim : ∀ α, Tendsto (fun t : ℝ =>
      Φ α t / gammaShapeZ 1 ((idx α : ℤ)) (a α) (b α) t) atTop (nhds (c α)) := by
    intro α
    have hmul := tendsto_datum_mul (σ := 1) hσ (hlim α)
      (tendsto_gammaLine_pow_div_gammaShapeZ (σ := 1) hσ (idx α))
    rw [mul_one, zero_add, add_zero, add_zero] at hmul
    exact hmul
  have hxne : ∀ α, ∀ᶠ t : ℝ in atTop, Φ α t ≠ 0 := fun α =>
    eventually_ne_zero_of_datum (hc α) (hxlim α)
  -- the sum is zero
  set F : ℕ → upperEndMeroField := fun n => algebraMap
      ↥(differentialAdjoin (RatFunc ℂ) ({digammaMero} : Set upperEndMeroField))
      upperEndMeroField (p.coeff n) * gammaUpperMero ^ n with hF
  have hsum0 : ∑ α : Fin N, x α = 0 := by
    have h2 : ∑ α : Fin N, x α = ∑ i : {n // n ∈ S}, F (i : ℕ) :=
      Fintype.sum_equiv S.equivFin.symm _ _ fun α => rfl
    have h1 : ∑ i : {n // n ∈ S}, F (i : ℕ) = ∑ n ∈ S, F n := Finset.sum_coe_sort S F
    rw [h2, h1, hF, ← hproot, Polynomial.aeval_def, Polynomial.eval₂_eq_sum,
      Polynomial.sum_def, ← hS]
  obtain ⟨χ, hχrep, hχeq⟩ := representsOnLine_sum x Φ hxrep hxne
  have hχ0 : ∀ᶠ t : ℝ in atTop, χ t = 0 := by
    rw [hsum0] at hχrep
    exact representsOnLine_zero_eventually hχrep
  -- the dominant term
  obtain ⟨β, -, hβ⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin N)) idx
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hNpos))
  have hterm : ∀ α : Fin N, Tendsto (fun t : ℝ =>
      Φ α t / gammaShapeZ 1 ((idx β : ℤ)) (a β) (b β) t) atTop
      (nhds (if α = β then c β else 0)) := by
    intro α
    by_cases hαβ : α = β
    · subst hαβ
      rw [if_pos rfl]
      exact hxlim α
    · rw [if_neg hαβ]
      have hlt : (idx β : ℤ) < (idx α : ℤ) := by
        have hle := hβ α (Finset.mem_univ α)
        have hne : idx α ≠ idx β := fun h => hαβ (hidxinj h)
        omega
      have hzero := tendsto_gammaShapeZ_ratio_zero (σ := 1) hσ
        (k₁ := (idx α : ℤ)) (a₁ := a α) (b₁ := b α)
        (k₂ := (idx β : ℤ)) (a₂ := a β) (b₂ := b β) (Or.inl hlt)
      have hmul := (hxlim α).mul hzero
      rw [mul_zero] at hmul
      refine hmul.congr' ?_
      filter_upwards [eventually_gammaShapeZ_ne_zero (σ := 1) hσ ((idx α : ℤ)) (a α) (b α),
        eventually_gammaShapeZ_ne_zero (σ := 1) hσ ((idx β : ℤ)) (a β) (b β)] with t h₁ h₂
      field_simp
  have hsumlim : Tendsto (fun t : ℝ =>
      ∑ α : Fin N, Φ α t / gammaShapeZ 1 ((idx β : ℤ)) (a β) (b β) t) atTop
      (nhds (∑ α : Fin N, if α = β then c β else 0)) :=
    tendsto_finsetSum _ fun α _ => hterm α
  rw [Finset.sum_ite_eq' Finset.univ β (fun _ => c β), if_pos (Finset.mem_univ β)] at hsumlim
  -- but the sum vanishes eventually
  have hzerolim : Tendsto (fun t : ℝ =>
      ∑ α : Fin N, Φ α t / gammaShapeZ 1 ((idx β : ℤ)) (a β) (b β) t) atTop (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hχeq, hχ0] with t h1 h2
    rw [← Finset.sum_div, ← h1, h2, zero_div]
  exact hc β (tendsto_nhds_unique hsumlim hzerolim)

end

end GaloisForLFunctions.HTGeometry
