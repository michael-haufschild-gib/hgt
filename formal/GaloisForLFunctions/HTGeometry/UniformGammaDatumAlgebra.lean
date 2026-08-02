import GaloisForLFunctions.HTGeometry.UniformGammaDatumAbscissa
import GaloisForLFunctions.HTGeometry.GammaFieldGeneratedByDigamma

/-!
# The tube datum is a valuation

The datum read uniformly on a tube obeys the same laws as the datum of a line: it is additive on
products, it negates under inversion, it is `(1, 0, 0)` with residue `1` on `Γ`, and it is `0` in the
`Γ`-direction on the digamma field.  Since the tube datum is the datum of every line the tube covers,
these are the tube forms of the exponential valuation of §4.
-/

open Filter Set Topology Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance uniformDatAlgDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance uniformDatAlgIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance uniformDatAlgDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance uniformDatAlgComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance uniformDatAlgRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance uniformDatAlgRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance uniformDatAlgRatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

/-- The product of two boundary shapes, beyond a fixed height. -/
theorem gammaShapeZ_mul_of_le {σ t : ℝ} (hσ : 0 < σ) (ht : 3 ≤ t) (k a b k' a' b' : ℤ) :
    gammaShapeZ σ k a b t * gammaShapeZ σ k' a' b' t
      = gammaShapeZ σ (k + k') (a + a') (b + b') t := by
  have hΓ : gammaLine σ t ≠ 0 := gammaLine_ne_zero hσ t
  have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := vertical_ne_zero_of_le ht
  have hL : vertLog t ≠ 0 := vertLog_ne_zero_of_le ht
  rw [gammaShapeZ, gammaShapeZ, gammaShapeZ, zpow_add₀ hΓ, zpow_add₀ hs, zpow_add₀ hL]
  ring

/-- The constant function has itself as tube limit. -/
theorem tubeLimit_const {M : ℝ} (c : ℂ) : TubeLimit M (fun _ _ => c) c :=
  tubeLimit_of_bound (C := 0) le_rfl fun σ t _ _ _ => by simp

/-- Products of represented elements are represented by the product of the representatives. -/
theorem RepresentsOnTube.mul {x y : upperEndMeroField} {φ χ : ℝ → ℝ → ℂ}
    (hx : RepresentsOnTube x φ) (hy : RepresentsOnTube y χ) :
    RepresentsOnTube (x * y) (fun σ t => φ σ t * χ σ t) := by
  obtain ⟨U, V, G, H, hUg, hVg, hV0, hxeq, hφ⟩ := hx
  obtain ⟨U', V', G', H', hUg', hVg', hV0', hyeq, hχ⟩ := hy
  refine ⟨U * U', V * V', fun z => G z * G' z, fun z => H z * H' z, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, hUg, hUg', ← map_mul]
    rfl
  · rw [map_mul, hVg, hVg', ← map_mul]
    rfl
  · rw [map_mul]
    exact mul_ne_zero hV0 hV0'
  · rw [hxeq, hyeq, map_mul, map_mul, div_mul_div_comm]
  · intro σ t
    dsimp only
    rw [hφ σ t, hχ σ t, div_mul_div_comm]

/-- An element with a tube datum is nonzero. -/
theorem HasGammaTubeDatum.ne_zero {M : ℝ} (hM : 0 < M) {x : upperEndMeroField} {k a b : ℤ} {c : ℂ}
    (h : HasGammaTubeDatum M x k a b c) : x ≠ 0 := by
  intro hx0
  obtain ⟨hc, φ, hrep, hlim⟩ := h.hasGammaDatum hM le_rfl
  rw [hx0] at hrep
  obtain ⟨t, ht⟩ :=
    ((representsOnLine_zero_eventually hrep).and (eventually_ne_zero_of_datum hc hlim)).exists
  exact ht.2 ht.1

/-- **The tube datum is additive on products.** -/
theorem HasGammaTubeDatum.mul {M : ℝ} {x y : upperEndMeroField} {k a b k' a' b' : ℤ} {c c' : ℂ}
    (h : HasGammaTubeDatum M x k a b c) (h' : HasGammaTubeDatum M y k' a' b' c') :
    HasGammaTubeDatum M (x * y) (k + k') (a + a') (b + b') (c * c') := by
  obtain ⟨hc, φ, hrep, hlim⟩ := h
  obtain ⟨hc', χ, hrep', hlim'⟩ := h'
  refine ⟨mul_ne_zero hc hc', fun σ t => φ σ t * χ σ t, hrep.mul hrep', ?_⟩
  refine (hlim.mul hlim').congr (T₀ := 3) fun σ t hσ hσM ht => ?_
  have hS : gammaShapeZ σ k a b t ≠ 0 := gammaShapeZ_ne_zero_of_le hσ ht _ _ _
  have hS' : gammaShapeZ σ k' a' b' t ≠ 0 := gammaShapeZ_ne_zero_of_le hσ ht _ _ _
  rw [← gammaShapeZ_mul_of_le hσ ht]
  field_simp

/-- **Inversion negates the tube datum** and inverts the residue. -/
theorem HasGammaTubeDatum.inv {M : ℝ} (hM : 0 < M) {x : upperEndMeroField} {k a b : ℤ} {c : ℂ}
    (h : HasGammaTubeDatum M x k a b c) :
    HasGammaTubeDatum M x⁻¹ (-k) (-a) (-b) c⁻¹ := by
  have hx0 : x ≠ 0 := h.ne_zero hM
  obtain ⟨hc, φ, hrep, hlim⟩ := h
  obtain ⟨U, V, G, H, hUg, hVg, hV0, hxeq, hφ⟩ := hrep
  have hU0 : algebraMap upperEndAnalyticSubring upperEndMeroField U ≠ 0 := by
    intro h0
    exact hx0 (by rw [hxeq, h0, zero_div])
  refine ⟨inv_ne_zero hc, fun σ t => (φ σ t)⁻¹, ⟨V, U, H, G, hVg, hUg, hU0, ?_, ?_⟩, ?_⟩
  · rw [hxeq, inv_div]
  · intro σ t
    dsimp only
    rw [hφ σ t, inv_div]
  · refine (hlim.inv hc).congr (T₀ := 3) fun σ t hσ hσM ht => ?_
    have hS : gammaShapeZ σ k a b t ≠ 0 := gammaShapeZ_ne_zero_of_le hσ ht _ _ _
    have hone : gammaShapeZ σ k a b t * gammaShapeZ σ (-k) (-a) (-b) t = 1 := by
      rw [gammaShapeZ_mul_of_le hσ ht]
      simp [gammaShapeZ]
    have hSinv : gammaShapeZ σ (-k) (-a) (-b) t = (gammaShapeZ σ k a b t)⁻¹ :=
      eq_inv_of_mul_eq_one_right hone
    rw [hSinv, inv_div_inv, inv_div]

/-- The tube datum of `Γ` is `(1, 0, 0)` with residue `1`. -/
theorem hasGammaTubeDatum_gammaUpperMero {M : ℝ} :
    HasGammaTubeDatum M gammaUpperMero 1 0 0 1 := by
  refine ⟨one_ne_zero, fun σ t => gammaLine σ t, ?_, ?_⟩
  · refine ⟨gammaUpperAnalytic, 1, Complex.Gamma, fun _ => 1, rfl, ?_, ?_, ?_, ?_⟩
    · rw [map_one]
      rfl
    · rw [map_one]
      exact one_ne_zero
    · rw [map_one, div_one]
      rfl
    · intro σ t
      rw [div_one]
      rfl
  · refine (tubeLimit_const (M := M) 1).congr (T₀ := 3) fun σ t hσ hσM ht => ?_
    have hΓ : gammaLine σ t ≠ 0 := gammaLine_ne_zero hσ t
    have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := vertical_ne_zero_of_le ht
    have hL : vertLog t ≠ 0 := vertLog_ne_zero_of_le ht
    rw [gammaShapeZ, zpow_zero, zpow_zero, zpow_one, mul_one, mul_one, div_self hΓ]

/-- The digamma field sits inside the Gamma field. -/
theorem digammaAdjoin_le_gammaAdjoin :
    differentialAdjoin (RatFunc ℂ) ({digammaMero} : Set upperEndMeroField)
      ≤ differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField) :=
  differentialAdjoin_le (RatFunc ℂ)
    (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact digammaMero_mem_gammaAdjoin)
    (derivationClosed_differentialAdjoin (RatFunc ℂ) _)

/-- **An element of the digamma field has tube datum with `Γ`-exponent zero.** -/
theorem exists_hasGammaTubeDatum_digammaField {M : ℝ} (hM : 0 < M) {x : upperEndMeroField}
    (hx : x ∈ differentialAdjoin (RatFunc ℂ) ({digammaMero} : Set upperEndMeroField))
    (hx0 : x ≠ 0) : ∃ (a b : ℤ) (c : ℂ), HasGammaTubeDatum M x 0 a b c := by
  obtain ⟨k, a, b, c, hdat⟩ := exists_hasGammaTubeDatum hM (digammaAdjoin_le_gammaAdjoin hx) hx0
  obtain ⟨a', b', c', hline⟩ := exists_hasGammaDatum_digammaField hM hx hx0
  obtain ⟨hk, ha, hb, hc⟩ := hasGammaDatum_unique hM (hdat.hasGammaDatum hM le_rfl) hline
  refine ⟨a, b, c, ?_⟩
  rwa [← hk]

/-- **Equation (19) on a tube, existence and uniqueness.**  Every nonzero element of `ℂ(s)⟨ψ⟩` has
exactly one datum valid uniformly for `0 < σ ≤ M`, and its `Γ`-exponent is zero. -/
theorem existsUnique_digammaTube_datum {M : ℝ} (hM : 0 < M) {x : upperEndMeroField}
    (hx : x ∈ differentialAdjoin (RatFunc ℂ) ({digammaMero} : Set upperEndMeroField))
    (hx0 : x ≠ 0) :
    ∃ d : (ℤ × ℤ) × ℂ, HasGammaTubeDatum M x 0 d.1.1 d.1.2 d.2
      ∧ ∀ d' : (ℤ × ℤ) × ℂ, HasGammaTubeDatum M x 0 d'.1.1 d'.1.2 d'.2 → d' = d := by
  obtain ⟨a, b, c, hdat⟩ := exists_hasGammaTubeDatum_digammaField hM hx hx0
  refine ⟨((a, b), c), hdat, fun d' hd' => ?_⟩
  obtain ⟨-, h2, h3, h4⟩ := hasGammaTubeDatum_unique hM hd' hdat
  obtain ⟨⟨a', b'⟩, c'⟩ := d'
  simp only at h2 h3 h4
  rw [h2, h3, h4]

/-- **The `Γ`-exponent is a valuation on the tube.**  On a product it adds, and the residue
multiplies. -/
theorem gammaTubeExponent_mul {M : ℝ} (hM : 0 < M) {x y : upperEndMeroField}
    {k a b k' a' b' : ℤ} {c c' : ℂ} (h : HasGammaTubeDatum M x k a b c)
    (h' : HasGammaTubeDatum M y k' a' b' c') {K A B : ℤ} {C : ℂ}
    (hxy : HasGammaTubeDatum M (x * y) K A B C) :
    K = k + k' ∧ A = a + a' ∧ B = b + b' ∧ C = c * c' :=
  hasGammaTubeDatum_unique hM hxy (h.mul h')

/-- **The digamma field does not contain `Γ`**, read on a tube: its elements have `Γ`-exponent `0`
and `Γ` has exponent `1`. -/
theorem gammaUpperMero_not_mem_digammaAdjoin_tube :
    gammaUpperMero ∉ differentialAdjoin (RatFunc ℂ) ({digammaMero} : Set upperEndMeroField) := by
  intro hmem
  obtain ⟨a, b, c, hdat⟩ :=
    exists_hasGammaTubeDatum_digammaField (M := 1) one_pos hmem gammaUpperMero_ne_zero
  obtain ⟨hk, -, -, -⟩ := hasGammaTubeDatum_unique (M := 1) one_pos
    (hasGammaTubeDatum_gammaUpperMero (M := 1)) hdat
  exact absurd hk one_ne_zero

end

end GaloisForLFunctions.HTGeometry
