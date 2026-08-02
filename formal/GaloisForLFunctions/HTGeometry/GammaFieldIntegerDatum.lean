import GaloisForLFunctions.HTGeometry.GammaShapeInteger
import GaloisForLFunctions.HTGeometry.GammaFieldRatDatum

/-!
# Equation (3) with integer exponents, and equation (5)

Every nonzero element of `K_Γ = ℂ(s)⟨Γ⟩` is a quotient of two analytic germs, and each of them has a
residue against a shape with natural exponents.  Dividing, the element itself has a residue against a
shape with *integer* exponents — the `(k, a, b)` of eq. (3) — and the clearing polynomials only shift
the argument exponent.

With the dominance order on integer data, a finite tuple then has a dominant member, and every ratio
against it converges: eq. (5), the one-point projective boundary of a finite tuple.
-/

open Filter Set Topology Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance gammaIntDatumDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance gammaIntDatumIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance gammaIntDatumDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance gammaIntDatumComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance gammaIntDatumRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

/-- `φ` is the restriction of the carrier element `x` to the vertical line through `σ`: `x` is a
quotient of two analytic germs and `φ` is the corresponding quotient of representatives. -/
def RepresentsOnLine (σ : ℝ) (x : upperEndMeroField) (φ : ℝ → ℂ) : Prop :=
  ∃ (U V : upperEndAnalyticSubring) (G H : ℂ → ℂ),
    upperEndAnalyticSubring.subtype U = Germ.coeRingHom upperEndFilter G
      ∧ upperEndAnalyticSubring.subtype V = Germ.coeRingHom upperEndFilter H
      ∧ algebraMap upperEndAnalyticSubring upperEndMeroField V ≠ 0
      ∧ x = algebraMap upperEndAnalyticSubring upperEndMeroField U
          / algebraMap upperEndAnalyticSubring upperEndMeroField V
      ∧ ∀ t : ℝ, φ t = G ((σ : ℂ) + (t : ℂ) * Complex.I) / H ((σ : ℂ) + (t : ℂ) * Complex.I)

/-- A nonzero polynomial is eventually nonzero on a vertical line, and its ratio to the
corresponding power of the argument converges to its leading coefficient. -/
theorem eventually_poly_eval_vertical_ne_zero {σ : ℝ} {q : Polynomial ℂ} (hq : q ≠ 0) :
    ∀ᶠ t : ℝ in atTop, q.eval ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  have hlim := tendsto_eval_div_pow_natDegree_of_norm_atTop (tendsto_norm_vertical σ) q
  have hne : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  have := hlim.eventually (eventually_ne_nhds hne)
  filter_upwards [this] with t ht
  intro h0
  exact ht (by rw [h0, zero_div])

/-- **Equation (3) with integer exponents.**  Every nonzero element of the Gamma field has a line
representative with a nonzero residue against a shape `Γ^k·s^a·(log s)^b`. -/
theorem exists_gammaField_intDatum {σ : ℝ} (hσ : 0 < σ) {x : upperEndMeroField}
    (hx : x ∈ differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
    (hx0 : x ≠ 0) :
    ∃ (k a b : ℤ) (φ : ℝ → ℂ) (c : ℂ),
      c ≠ 0 ∧ RepresentsOnLine σ x φ
        ∧ Tendsto (fun t : ℝ => φ t / gammaShapeZ σ k a b t) atTop (nhds c) := by
  classical
  obtain ⟨q₁, q₂, U, V, G, H, u₁, a₁, d₁, b₁, u₂, a₂, d₂, b₂, r,
    hq₁, hq₂, hr, hxeq, hUgerm, hVgerm, hlim⟩ := exists_gammaField_datum hσ hx hx0
  -- the two shapes, as integer shapes
  set S₁ : ℝ → ℂ := fun t => gammaJetShape σ u₁ a₁ d₁ b₁ t with hS₁
  set S₂ : ℝ → ℂ := fun t => gammaJetShape σ u₂ a₂ d₂ b₂ t with hS₂
  set Δ : ℤ := (q₂.natDegree : ℤ) - (q₁.natDegree : ℤ) with hΔ
  set k : ℤ := (u₁ : ℤ) - (u₂ : ℤ) with hk
  set A : ℤ := (((d₁ : ℤ) - (b₁ : ℤ)) - ((d₂ : ℤ) - (b₂ : ℤ))) + Δ with hA
  set B : ℤ := (a₁ : ℤ) - (a₂ : ℤ) with hB
  -- the line function of `x`
  set φ : ℝ → ℂ := fun t =>
    (q₂.eval ((σ : ℂ) + (t : ℂ) * Complex.I) * G ((σ : ℂ) + (t : ℂ) * Complex.I))
      / (q₁.eval ((σ : ℂ) + (t : ℂ) * Complex.I) * H ((σ : ℂ) + (t : ℂ) * Complex.I)) with hφ
  -- the polynomial ratio contributes its leading coefficients
  have hpoly₁ := tendsto_eval_div_pow_natDegree_of_norm_atTop (tendsto_norm_vertical σ) q₁
  have hpoly₂ := tendsto_eval_div_pow_natDegree_of_norm_atTop (tendsto_norm_vertical σ) q₂
  have hlead₁ : q₁.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq₁
  have hratio : Tendsto (fun t : ℝ =>
      (q₂.eval ((σ : ℂ) + (t : ℂ) * Complex.I) / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ q₂.natDegree)
        / (q₁.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ q₁.natDegree)) atTop
      (nhds (q₂.leadingCoeff / q₁.leadingCoeff)) := hpoly₂.div hpoly₁ hlead₁
  refine ⟨k, A, B, φ, (q₂.leadingCoeff / q₁.leadingCoeff) * r,
    mul_ne_zero (div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hq₂) hlead₁) hr, ?_, ?_⟩
  · refine ⟨upperEndPolyToAnalytic q₂ * U, upperEndPolyToAnalytic q₁ * V,
      fun z => q₂.eval z * G z, fun z => q₁.eval z * H z, ?_, ?_, ?_, ?_, fun t => rfl⟩
    · rw [map_mul, hUgerm, polyToAnalytic_subtype, ← map_mul]
      rfl
    · rw [map_mul, hVgerm, polyToAnalytic_subtype, ← map_mul]
      rfl
    · -- the denominator is nonzero because `x` is
      intro h0
      rw [hxeq] at hx0
      refine hx0 ?_
      rw [show upperEndPolyToMero q₁ * algebraMap upperEndAnalyticSubring upperEndMeroField V
          = algebraMap upperEndAnalyticSubring upperEndMeroField (upperEndPolyToAnalytic q₁ * V) by
        rw [map_mul]; rfl, h0, div_zero]
    · rw [hxeq, map_mul, map_mul]
      rfl
  · -- the residue: the polynomial ratio times the germ ratio
    have hmain := hratio.mul hlim
    refine hmain.congr' ?_
    filter_upwards [eventually_vertical_ne_zero σ,
      eventually_poly_eval_vertical_ne_zero (σ := σ) hq₁,
      eventually_gammaJetShape_ne_zero (σ := σ) hσ u₁ a₁ d₁ b₁,
      eventually_gammaJetShape_ne_zero (σ := σ) hσ u₂ a₂ d₂ b₂,
      gammaJetShape_eq_gammaShapeZ (σ := σ) u₁ a₁ d₁ b₁,
      gammaJetShape_eq_gammaShapeZ (σ := σ) u₂ a₂ d₂ b₂,
      gammaShapeZ_div (σ := σ) hσ (u₁ : ℤ) ((d₁ : ℤ) - (b₁ : ℤ)) (a₁ : ℤ)
        (u₂ : ℤ) ((d₂ : ℤ) - (b₂ : ℤ)) (a₂ : ℤ),
      gammaShapeZ_arg_add (σ := σ) k (((d₁ : ℤ) - (b₁ : ℤ)) - ((d₂ : ℤ) - (b₂ : ℤ))) B Δ]
      with t hs hq1t hS1t hS2t hZ1 hZ2 hdiv hadd
    have hΔpow : ((σ : ℂ) + (t : ℂ) * Complex.I) ^ Δ
        = ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (q₂.natDegree : ℤ)
          / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (q₁.natDegree : ℤ) := by
      rw [hΔ, zpow_sub₀ hs]
    have hshape : gammaShapeZ σ k A B t
        = (gammaJetShape σ u₁ a₁ d₁ b₁ t / gammaJetShape σ u₂ a₂ d₂ b₂ t)
          * (((σ : ℂ) + (t : ℂ) * Complex.I) ^ (q₂.natDegree : ℤ)
            / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (q₁.natDegree : ℤ)) := by
      rw [hA, hadd, hZ1, hZ2, hdiv, hΔpow]
    rw [hφ, hshape]
    field_simp
    simp only [zpow_natCast]
    ring

/-- **Equation (5): the one-point projective boundary of a finite tuple.**  A finite tuple of nonzero
elements of the Gamma field has a component whose datum dominates; dividing the tuple by that
component, every ratio converges on the vertical line, to the quotient of the residues at the
components sharing the dominant datum and to zero at every other. -/
theorem exists_dominant_gammaField_ratio {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 0 < N)
    (F : Fin N → upperEndMeroField)
    (hmem : ∀ α, F α ∈ differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
    (h0 : ∀ α, F α ≠ 0) :
    ∃ (β : Fin N) (φ : Fin N → ℝ → ℂ) (d : Fin N → ℂ),
      (∀ α, RepresentsOnLine σ (F α) (φ α)) ∧ d β = 1
        ∧ ∀ α, Tendsto (fun t : ℝ => φ α t / φ β t) atTop (nhds (d α)) := by
  classical
  choose k a b φ c hc hrep hlim using fun α => exists_gammaField_intDatum hσ (hmem α) (h0 α)
  obtain ⟨β, hβ⟩ := exists_dominant_shapeZ_index hN k a b
  refine ⟨β, φ, fun α => if k α = k β ∧ a α = a β ∧ b α = b β then c α / c β else 0, hrep, ?_, ?_⟩
  · dsimp only
    rw [if_pos ⟨rfl, rfl, rfl⟩, div_self (hc β)]
  · intro α
    have hinv : Tendsto (fun t : ℝ => (φ β t / gammaShapeZ σ (k β) (a β) (b β) t)⁻¹) atTop
        (nhds (c β)⁻¹) := (hlim β).inv₀ (hc β)
    dsimp only
    rcases hβ α with ⟨hk, ha, hb⟩ | hsub
    · rw [if_pos ⟨hk, ha, hb⟩]
      have hmain := (hlim α).mul hinv
      rw [show c α * (c β)⁻¹ = c α / c β from (div_eq_mul_inv _ _).symm] at hmain
      refine hmain.congr' ?_
      filter_upwards [eventually_gammaShapeZ_ne_zero (σ := σ) hσ (k β) (a β) (b β)] with t hS
      have hSα : gammaShapeZ σ (k α) (a α) (b α) t = gammaShapeZ σ (k β) (a β) (b β) t := by
        rw [hk, ha, hb]
      rw [hSα]
      by_cases hφβ : φ β t = 0
      · rw [hφβ]
        simp
      · field_simp
    · rw [if_neg (by rintro ⟨hk, ha, hb⟩; rcases hsub with h | ⟨-, h⟩ | ⟨-, -, h⟩ <;> omega)]
      have hzero := tendsto_gammaShapeZ_ratio_zero (σ := σ) hσ hsub
      have hmain := ((hlim α).mul hzero).mul hinv
      rw [show c α * 0 * (c β)⁻¹ = 0 by ring] at hmain
      refine hmain.congr' ?_
      filter_upwards [eventually_gammaShapeZ_ne_zero (σ := σ) hσ (k β) (a β) (b β),
        eventually_gammaShapeZ_ne_zero (σ := σ) hσ (k α) (a α) (b α)] with t hSβ hSα
      by_cases hφβ : φ β t = 0
      · rw [hφβ]
        simp
      · field_simp

end

end GaloisForLFunctions.HTGeometry
