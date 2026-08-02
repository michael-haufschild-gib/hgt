import GaloisForLFunctions.HTGeometry.GammaFieldIntegerDatumUnique

/-!
# The algebra of line representatives, and the datum of a product

A line representative of a carrier element is a quotient of representatives of two analytic germs.
Products of carrier elements are represented by the products of the representatives, and a finite sum
is represented by the sum put over a common denominator; an analytic germ is represented by any of its
representatives.

Since the shapes multiply — `Γ^k·s^a·(log s)^b · Γ^{k'}·s^{a'}·(log s)^{b'}` is the shape at
`(k+k', a+a', b+b')` — the datum of a product is the sum of the data with the product of the
residues.  That multiplicativity is what makes the triple `(k, a, b)` a valuation.
-/

open Filter Set Topology Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance gammaRepDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance gammaRepIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance gammaRepDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance gammaRepComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance gammaRepRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

/-- An analytic germ is represented on the line by any of its representatives. -/
theorem representsOnLine_algebraMap {σ : ℝ} (U : upperEndAnalyticSubring) (G : ℂ → ℂ)
    (hU : upperEndAnalyticSubring.subtype U = Germ.coeRingHom upperEndFilter G) :
    RepresentsOnLine σ (algebraMap upperEndAnalyticSubring upperEndMeroField U)
      (fun t : ℝ => G ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  refine ⟨U, 1, G, fun _ => 1, hU, ?_, ?_, ?_, fun t => by rw [div_one]⟩
  · rw [map_one]
    rfl
  · rw [map_one]
    exact one_ne_zero
  · rw [map_one, div_one]

/-- Products of represented elements are represented by the product of the representatives. -/
theorem RepresentsOnLine.mul {σ : ℝ} {x y : upperEndMeroField} {φ ψ : ℝ → ℂ}
    (hx : RepresentsOnLine σ x φ) (hy : RepresentsOnLine σ y ψ) :
    RepresentsOnLine σ (x * y) (fun t => φ t * ψ t) := by
  obtain ⟨U, V, G, H, hUg, hVg, hV0, hxeq, hφ⟩ := hx
  obtain ⟨U', V', G', H', hUg', hVg', hV0', hyeq, hψ⟩ := hy
  refine ⟨U * U', V * V', fun z => G z * G' z, fun z => H z * H' z, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, hUg, hUg', ← map_mul]
    rfl
  · rw [map_mul, hVg, hVg', ← map_mul]
    rfl
  · rw [map_mul]
    exact mul_ne_zero hV0 hV0'
  · rw [hxeq, hyeq, map_mul, map_mul, div_mul_div_comm]
  · intro t
    dsimp only
    rw [hφ t, hψ t, div_mul_div_comm]

/-- A power of a represented element is represented by the same power of the representative. -/
theorem RepresentsOnLine.pow {σ : ℝ} {x : upperEndMeroField} {φ : ℝ → ℂ}
    (hx : RepresentsOnLine σ x φ) (n : ℕ) :
    RepresentsOnLine σ (x ^ n) (fun t => φ t ^ n) := by
  induction n with
  | zero =>
      have h1 : RepresentsOnLine σ (1 : upperEndMeroField) (fun _ : ℝ => (1 : ℂ)) := by
        refine ⟨1, 1, fun _ => 1, fun _ => 1, ?_, ?_, ?_, ?_, fun t => by rw [div_one]⟩
        · rw [map_one]
          rfl
        · rw [map_one]
          rfl
        · rw [map_one]
          exact one_ne_zero
        · rw [map_one, div_one]
      simpa using h1
  | succ n ih =>
      have := ih.mul hx
      simpa [pow_succ] using this

/-- **A finite sum is represented over a common denominator.**  If every term is eventually nonzero
on the line — which a nonzero residue guarantees — the common-denominator representative is
eventually the sum of the individual ones. -/
theorem representsOnLine_sum {σ : ℝ} {N : ℕ} (x : Fin N → upperEndMeroField) (φ : Fin N → ℝ → ℂ)
    (hrep : ∀ i, RepresentsOnLine σ (x i) (φ i))
    (hne : ∀ i, ∀ᶠ t : ℝ in atTop, φ i t ≠ 0) :
    ∃ χ : ℝ → ℂ, RepresentsOnLine σ (∑ i, x i) χ
      ∧ ∀ᶠ t : ℝ in atTop, χ t = ∑ i, φ i t := by
  classical
  choose U V G H hUg hVg hV0 hxeq hφ using hrep
  -- the common denominator, and the numerator over it
  set Vp : upperEndAnalyticSubring := ∏ i, V i with hVp
  set Hp : ℂ → ℂ := fun z => ∏ i, H i z with hHp
  set Up : upperEndAnalyticSubring :=
    ∑ i, U i * ∏ j ∈ Finset.univ.erase i, V j with hUp
  set Gp : ℂ → ℂ := fun z => ∑ i, G i z * ∏ j ∈ Finset.univ.erase i, H j z with hGp
  have hVp0 : algebraMap upperEndAnalyticSubring upperEndMeroField Vp ≠ 0 := by
    rw [hVp, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hV0 i
  have hUpg : upperEndAnalyticSubring.subtype Up = Germ.coeRingHom upperEndFilter Gp := by
    rw [hUp, map_sum, hGp]
    have hterm : ∀ i : Fin N, upperEndAnalyticSubring.subtype
        (U i * ∏ j ∈ Finset.univ.erase i, V j)
        = Germ.coeRingHom upperEndFilter
          (fun z : ℂ => G i z * ∏ j ∈ Finset.univ.erase i, H j z) := by
      intro i
      rw [map_mul, hUg i, map_prod]
      have hprod : ∏ j ∈ Finset.univ.erase i, upperEndAnalyticSubring.subtype (V j)
          = Germ.coeRingHom upperEndFilter (fun z : ℂ => ∏ j ∈ Finset.univ.erase i, H j z) := by
        rw [Finset.prod_congr rfl fun j _ => hVg j, ← map_prod]
        refine congrArg _ ?_
        funext z
        simp
      rw [hprod, ← map_mul]
      rfl
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← map_sum]
    refine congrArg _ ?_
    funext z
    simp
  have hVpg : upperEndAnalyticSubring.subtype Vp = Germ.coeRingHom upperEndFilter Hp := by
    rw [hVp, map_prod, Finset.prod_congr rfl fun j _ => hVg j, ← map_prod, hHp]
    refine congrArg _ ?_
    funext z
    simp
  have hsum : (∑ i, x i)
      = algebraMap upperEndAnalyticSubring upperEndMeroField Up
        / algebraMap upperEndAnalyticSubring upperEndMeroField Vp := by
    rw [hUp, map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hxeq i, map_mul, map_prod, hVp, map_prod]
    have hsplit : ∏ j, algebraMap upperEndAnalyticSubring upperEndMeroField (V j)
        = algebraMap upperEndAnalyticSubring upperEndMeroField (V i)
          * ∏ j ∈ Finset.univ.erase i, algebraMap upperEndAnalyticSubring upperEndMeroField (V j) :=
      (Finset.mul_prod_erase Finset.univ
        (fun j => algebraMap upperEndAnalyticSubring upperEndMeroField (V j))
        (Finset.mem_univ i)).symm
    rw [hsplit]
    have hprod0 : ∏ j ∈ Finset.univ.erase i,
        algebraMap upperEndAnalyticSubring upperEndMeroField (V j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => hV0 j
    field_simp
  refine ⟨fun t => Gp ((σ : ℂ) + (t : ℂ) * Complex.I) / Hp ((σ : ℂ) + (t : ℂ) * Complex.I),
    ⟨Up, Vp, Gp, Hp, hUpg, hVpg, hVp0, hsum, fun t => rfl⟩, ?_⟩
  -- where every denominator is nonzero the common-denominator quotient is the sum
  have hHne : ∀ i, ∀ᶠ t : ℝ in atTop, H i ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro i
    filter_upwards [hne i] with t ht
    intro h0
    exact ht (by rw [hφ i t, h0, div_zero])
  have hHall : ∀ᶠ t : ℝ in atTop, ∀ i : Fin N, H i ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
    Filter.eventually_all.mpr hHne
  filter_upwards [hHall] with t ht
  have hHp0 : Hp ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    rw [hHp]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => ht i
  rw [hGp, hHp, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [hφ i t]
  have hsplit : ∏ j, H j ((σ : ℂ) + (t : ℂ) * Complex.I)
      = H i ((σ : ℂ) + (t : ℂ) * Complex.I)
        * ∏ j ∈ Finset.univ.erase i, H j ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    (Finset.mul_prod_erase Finset.univ
      (fun j => H j ((σ : ℂ) + (t : ℂ) * Complex.I)) (Finset.mem_univ i)).symm
  rw [hsplit]
  have hrest : ∏ j ∈ Finset.univ.erase i, H j ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => ht j
  field_simp

/-- The shapes multiply. -/
theorem gammaShapeZ_mul {σ : ℝ} (hσ : 0 < σ) (k a b k' a' b' : ℤ) :
    ∀ᶠ t : ℝ in atTop,
      gammaShapeZ σ k a b t * gammaShapeZ σ k' a' b' t
        = gammaShapeZ σ (k + k') (a + a') (b + b') t := by
  filter_upwards [eventually_vertLog_ne_zero, eventually_vertical_ne_zero σ] with t hL hs
  have hΓ : gammaLine σ t ≠ 0 := gammaLine_ne_zero hσ t
  rw [gammaShapeZ, gammaShapeZ, gammaShapeZ, zpow_add₀ hΓ, zpow_add₀ hs, zpow_add₀ hL]
  ring

/-- **The datum of a product is the sum of the data.**  The residue of the product is the product of
the residues, so it is nonzero. -/
theorem tendsto_datum_mul {σ : ℝ} (hσ : 0 < σ) {φ ψ : ℝ → ℂ} {k a b k' a' b' : ℤ} {c c' : ℂ}
    (h : Tendsto (fun t : ℝ => φ t / gammaShapeZ σ k a b t) atTop (nhds c))
    (h' : Tendsto (fun t : ℝ => ψ t / gammaShapeZ σ k' a' b' t) atTop (nhds c')) :
    Tendsto (fun t : ℝ => (φ t * ψ t) / gammaShapeZ σ (k + k') (a + a') (b + b') t) atTop
      (nhds (c * c')) := by
  refine (h.mul h').congr' ?_
  filter_upwards [gammaShapeZ_mul hσ k a b k' a' b',
    eventually_gammaShapeZ_ne_zero (σ := σ) hσ k a b,
    eventually_gammaShapeZ_ne_zero (σ := σ) hσ k' a' b'] with t hmul hS hS'
  rw [← hmul]
  field_simp

end

end GaloisForLFunctions.HTGeometry
