import GaloisForLFunctions.RHTower.DeBrangesGaugeInvariance
import GaloisForLFunctions.RHTower.Suzuki.SuzukiDeBrangesSpace
import GaloisForLFunctions.HTGeometry.CompactFourierEntire
import GaloisForLFunctions.HTGeometry.EntireZeroSetNull

/-!
# Gauge multiplication is a unitary map between de Branges spaces

For a nonzero entire function `E`, this module defines the de Branges-type space `H(E)` of
entire functions `F` such that `F/E` and `F#/E` restricted to `ℝ` lie in `L²(ℝ)` and in the
Hardy subspace `hardyL2`, where `F#(z) = conj (F (conj z))`. The space is normed through the
boundary map `F ↦ F/E` in `L²(ℝ)`, which is injective because an entire function vanishing almost
everywhere on `ℝ` is zero. For an entire gauge `H` that is zero-free and real (`H# = H`),
multiplication by `H` is a linear isometric isomorphism `H(E) ≃ H(HE)`, since the boundary
quotients `F/E` and `HF/(HE)` coincide.

## Main results

- `GenericMemDeBranges`, `genericDeBrangesSubmodule`: the membership predicate and the
  `ℂ`-subspace `H(E)` of entire functions.
- `genericDeBrangesBoundaryMap_injective`: the boundary map `F ↦ F/E ∈ L²(ℝ)` is injective.
- `deBrangesGaugeLinearEquiv`: multiplication by `H` is a linear equivalence `H(E) ≃ H(HE)`.
- `deBrangesGaugeUnitary`: the same map is a linear isometric equivalence, acting by
  `F ↦ H · F`.

## Hypotheses

The gauge results take as hypotheses that `H` is entire, zero-free (`ZeroFreeGauge H`) and fixed
by Schwarz reflection (`SchwarzRealGauge H`); these are Prop-valued conditions on the gauge, not
analytic inputs. `EntireDeBrangesDatum` bundles an entire `E` that is not identically zero. No
Hermite–Biehler condition on `E` is assumed.
-/

namespace GaloisForLFunctions.RHTower

open Complex Filter Topology Set MeasureTheory

noncomputable section

/-- An entire function `E` that is not identically zero, used as the structure function of a
de Branges-type space. -/
structure EntireDeBrangesDatum where
  E : ℂ → ℂ
  analytic : AnalyticOnNhd ℂ E Set.univ
  nontrivial : ∃ z, E z ≠ 0

/-- The boundary quotient `x ↦ F(x)/E(x)` on the real line. -/
def deBrangesBoundaryQuotient (D : EntireDeBrangesDatum) (F : ℂ → ℂ) (x : ℝ) : ℂ :=
  F (x : ℂ) / D.E (x : ℂ)

/-- The reflected boundary quotient `x ↦ F#(x)/E(x)`, with `F#(z) = conj (F (conj z))`. -/
def deBrangesSharpBoundaryQuotient (D : EntireDeBrangesDatum) (F : ℂ → ℂ)
    (x : ℝ) : ℂ :=
  suzukiEntireSharp F (x : ℂ) / D.E (x : ℂ)

/-- Membership in the de Branges-type space `H(E)`: `F` is entire and both `F/E` and `F#/E` on `ℝ`
lie in `L²(ℝ)` and in the Hardy subspace `hardyL2`. -/
structure GenericMemDeBranges (D : EntireDeBrangesDatum) (F : ℂ → ℂ) : Prop where
  entire : Differentiable ℂ F
  memLp : MemLp (deBrangesBoundaryQuotient D F) 2 (volume : Measure ℝ)
  memLpSharp : MemLp (deBrangesSharpBoundaryQuotient D F) 2 (volume : Measure ℝ)
  hardy : (memLp.toLp _ : _root_.RHTower.L2R) ∈ _root_.RHTower.hardyL2
  hardySharp : (memLpSharp.toLp _ : _root_.RHTower.L2R) ∈ _root_.RHTower.hardyL2

theorem genericMemDeBranges_zero (D : EntireDeBrangesDatum) :
    GenericMemDeBranges D 0 := by
  have hq : deBrangesBoundaryQuotient D 0 = 0 := by
    funext x
    simp [deBrangesBoundaryQuotient]
  have hqs : deBrangesSharpBoundaryQuotient D 0 = 0 := by
    funext x
    simp [deBrangesSharpBoundaryQuotient, suzukiEntireSharp]
  let h0 : MemLp (0 : ℝ → ℂ) 2 (volume : Measure ℝ) := MemLp.zero
  refine ⟨by fun_prop, ?_, ?_, ?_, ?_⟩
  · rw [hq]
    exact h0
  · rw [hqs]
    exact h0
  · simp [hq]
  · simp [hqs]

theorem genericMemDeBranges_add (D : EntireDeBrangesDatum) {F G : ℂ → ℂ}
    (hF : GenericMemDeBranges D F) (hG : GenericMemDeBranges D G) :
    GenericMemDeBranges D (F + G) := by
  have hq : deBrangesBoundaryQuotient D (F + G) =
      deBrangesBoundaryQuotient D F + deBrangesBoundaryQuotient D G := by
    funext x
    simp [deBrangesBoundaryQuotient, add_div]
  have hqs : deBrangesSharpBoundaryQuotient D (F + G) =
      deBrangesSharpBoundaryQuotient D F + deBrangesSharpBoundaryQuotient D G := by
    funext x
    simp [deBrangesSharpBoundaryQuotient, suzukiEntireSharp, add_div]
  have hm : MemLp (deBrangesBoundaryQuotient D (F + G)) 2 (volume : Measure ℝ) := by
    rw [hq]
    exact hF.memLp.add hG.memLp
  have hms : MemLp (deBrangesSharpBoundaryQuotient D (F + G)) 2
      (volume : Measure ℝ) := by
    rw [hqs]
    exact hF.memLpSharp.add hG.memLpSharp
  refine ⟨hF.entire.add hG.entire, hm, hms, ?_, ?_⟩
  · have htc : hm.toLp _ = (hF.memLp.add hG.memLp).toLp _ :=
      hm.toLp_congr _ (Filter.Eventually.of_forall fun x => congrFun hq x)
    rw [htc, hF.memLp.toLp_add hG.memLp]
    exact _root_.RHTower.hardyL2.add_mem hF.hardy hG.hardy
  · have htc : hms.toLp _ = (hF.memLpSharp.add hG.memLpSharp).toLp _ :=
      hms.toLp_congr _ (Filter.Eventually.of_forall fun x => congrFun hqs x)
    rw [htc, hF.memLpSharp.toLp_add hG.memLpSharp]
    exact _root_.RHTower.hardyL2.add_mem hF.hardySharp hG.hardySharp

theorem genericMemDeBranges_smul (D : EntireDeBrangesDatum) (c : ℂ) {F : ℂ → ℂ}
    (hF : GenericMemDeBranges D F) : GenericMemDeBranges D (c • F) := by
  have hq : deBrangesBoundaryQuotient D (c • F) = c • deBrangesBoundaryQuotient D F := by
    funext x
    simp [deBrangesBoundaryQuotient, smul_eq_mul, mul_div_assoc]
  have hqs : deBrangesSharpBoundaryQuotient D (c • F) =
      star c • deBrangesSharpBoundaryQuotient D F := by
    funext x
    simp [deBrangesSharpBoundaryQuotient, suzukiEntireSharp, smul_eq_mul,
      mul_div_assoc]
  have hm : MemLp (deBrangesBoundaryQuotient D (c • F)) 2 (volume : Measure ℝ) := by
    rw [hq]
    exact hF.memLp.const_smul c
  have hms : MemLp (deBrangesSharpBoundaryQuotient D (c • F)) 2
      (volume : Measure ℝ) := by
    rw [hqs]
    exact hF.memLpSharp.const_smul (star c)
  refine ⟨hF.entire.const_smul c, hm, hms, ?_, ?_⟩
  · have htc : hm.toLp _ = (hF.memLp.const_smul c).toLp _ :=
      hm.toLp_congr _ (Filter.Eventually.of_forall fun x => congrFun hq x)
    rw [htc, hF.memLp.toLp_const_smul c]
    exact _root_.RHTower.hardyL2.smul_mem c hF.hardy
  · have htc : hms.toLp _ = (hF.memLpSharp.const_smul (star c)).toLp _ :=
      hms.toLp_congr _ (Filter.Eventually.of_forall fun x => congrFun hqs x)
    rw [htc, hF.memLpSharp.toLp_const_smul (star c)]
    exact _root_.RHTower.hardyL2.smul_mem (star c) hF.hardySharp

/-- The space `H(E)` as a `ℂ`-linear subspace of functions `ℂ → ℂ`. -/
def genericDeBrangesSubmodule (D : EntireDeBrangesDatum) : Submodule ℂ (ℂ → ℂ) where
  carrier := {F | GenericMemDeBranges D F}
  zero_mem' := genericMemDeBranges_zero D
  add_mem' := genericMemDeBranges_add D
  smul_mem' := genericMemDeBranges_smul D

abbrev GenericDeBrangesSpace (D : EntireDeBrangesDatum) := genericDeBrangesSubmodule D

/-- The linear boundary map `H(E) → L²(ℝ)`, `F ↦ F/E` on the real line. -/
def genericDeBrangesBoundaryMap (D : EntireDeBrangesDatum) :
    GenericDeBrangesSpace D →ₗ[ℂ] _root_.RHTower.L2R where
  toFun F := F.property.memLp.toLp _
  map_add' F G := by
    let hFG := (F + G : GenericDeBrangesSpace D).property.memLp
    have hq : deBrangesBoundaryQuotient D ((F + G : GenericDeBrangesSpace D) : ℂ → ℂ) =
        deBrangesBoundaryQuotient D F + deBrangesBoundaryQuotient D G := by
      funext x
      simp [deBrangesBoundaryQuotient, add_div]
    calc
      hFG.toLp _ =
          (F.property.memLp.add G.property.memLp).toLp _ :=
        hFG.toLp_congr _
          (Filter.Eventually.of_forall fun x => congrFun hq x)
      _ = _ := F.property.memLp.toLp_add G.property.memLp
  map_smul' c F := by
    let hcF := (c • F : GenericDeBrangesSpace D).property.memLp
    have hq : deBrangesBoundaryQuotient D ((c • F : GenericDeBrangesSpace D) : ℂ → ℂ) =
        c • deBrangesBoundaryQuotient D F := by
      funext x
      simp [deBrangesBoundaryQuotient, smul_eq_mul, mul_div_assoc]
    calc
      hcF.toLp _ = (F.property.memLp.const_smul c).toLp _ :=
        hcF.toLp_congr _
          (Filter.Eventually.of_forall fun x => congrFun hq x)
      _ = _ := F.property.memLp.toLp_const_smul c

/-- The boundary map `F ↦ F/E` is injective: since `E` vanishes only on a null subset of `ℝ`, equal
quotients force `F = G` almost everywhere on `ℝ`, hence everywhere by analyticity. -/
theorem genericDeBrangesBoundaryMap_injective (D : EntireDeBrangesDatum) :
    Function.Injective (genericDeBrangesBoundaryMap D) := by
  intro F G hFG
  apply Subtype.ext
  funext z
  have hq : deBrangesBoundaryQuotient D F =ᵐ[(volume : Measure ℝ)]
      deBrangesBoundaryQuotient D G :=
    (F.property.memLp.toLp_eq_toLp_iff G.property.memLp).mp hFG
  have hEne : ∀ᵐ (x : ℝ) ∂(volume : Measure ℝ), D.E (x : ℂ) ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_ne_iff] using
      _root_.HTGeometry.volume_real_setOf_eq_zero_eq_zero D.analytic D.nontrivial
  have hreal : ∀ᵐ (x : ℝ) ∂(volume : Measure ℝ),
      (F : ℂ → ℂ) (x : ℂ) - (G : ℂ → ℂ) (x : ℂ) = 0 := by
    filter_upwards [hq, hEne] with x hx hEx
    rw [deBrangesBoundaryQuotient] at hx
    exact sub_eq_zero.mpr ((div_left_inj' hEx).mp hx)
  exact sub_eq_zero.mp
    (_root_.GaloisForLFunctions.HTGeometry.entire_eq_zero_of_ae_vanishing_on_real_interval
    (F.property.entire.sub G.property.entire) (t₀ := 0) (r := 1) (by norm_num)
    (MeasureTheory.ae_restrict_of_ae hreal) z)

/-- `H(E)` carries the norm `‖F‖ = ‖F/E‖_{L²(ℝ)}` induced by the injective boundary map. -/
noncomputable instance genericDeBrangesNormedAddCommGroup (D : EntireDeBrangesDatum) :
    NormedAddCommGroup (GenericDeBrangesSpace D) :=
  NormedAddCommGroup.induced (GenericDeBrangesSpace D) _
    (genericDeBrangesBoundaryMap D) (genericDeBrangesBoundaryMap_injective D)

noncomputable instance genericDeBrangesNormedSpace (D : EntireDeBrangesDatum) :
    NormedSpace ℂ (GenericDeBrangesSpace D) :=
  NormedSpace.induced ℂ (GenericDeBrangesSpace D) _ (genericDeBrangesBoundaryMap D)

theorem norm_genericDeBranges_eq_boundary (D : EntireDeBrangesDatum)
    (F : GenericDeBrangesSpace D) :
    ‖F‖ = ‖genericDeBrangesBoundaryMap D F‖ := rfl

/-- Membership transfers between structure functions: if `F₂` is entire and its two boundary quotients
for `E₂` equal those of `F₁ ∈ H(E₁)` for `E₁`, then `F₂ ∈ H(E₂)`. -/
theorem genericMemDeBranges_of_quotients_eq
    {D₁ D₂ : EntireDeBrangesDatum} {F₁ F₂ : ℂ → ℂ}
    (hF₁ : GenericMemDeBranges D₁ F₁) (hF₂entire : Differentiable ℂ F₂)
    (hq : deBrangesBoundaryQuotient D₂ F₂ = deBrangesBoundaryQuotient D₁ F₁)
    (hqs : deBrangesSharpBoundaryQuotient D₂ F₂ =
      deBrangesSharpBoundaryQuotient D₁ F₁) :
    GenericMemDeBranges D₂ F₂ := by
  have hm : MemLp (deBrangesBoundaryQuotient D₂ F₂) 2 (volume : Measure ℝ) := by
    rw [hq]
    exact hF₁.memLp
  have hms : MemLp (deBrangesSharpBoundaryQuotient D₂ F₂) 2
      (volume : Measure ℝ) := by
    rw [hqs]
    exact hF₁.memLpSharp
  refine ⟨hF₂entire, hm, hms, ?_, ?_⟩
  · have ht : hm.toLp _ = hF₁.memLp.toLp _ :=
      hm.toLp_congr hF₁.memLp
        (Filter.Eventually.of_forall fun x => congrFun hq x)
    rw [ht]
    exact hF₁.hardy
  · have ht : hms.toLp _ = hF₁.memLpSharp.toLp _ :=
      hms.toLp_congr hF₁.memLpSharp
        (Filter.Eventually.of_forall fun x => congrFun hqs x)
    rw [ht]
    exact hF₁.hardySharp

/-- The gauged structure function `H · E`, for an entire zero-free gauge `H`. -/
def EntireDeBrangesDatum.mulGauge (D : EntireDeBrangesDatum) (H : ℂ → ℂ)
    (hH : AnalyticOnNhd ℂ H Set.univ) (hHzero : ZeroFreeGauge H) :
    EntireDeBrangesDatum where
  E := fun z => H z * D.E z
  analytic := hH.mul D.analytic
  nontrivial := by
    obtain ⟨z, hz⟩ := D.nontrivial
    exact ⟨z, mul_ne_zero (hHzero z) hz⟩

def deBrangesGaugeMul (H F : ℂ → ℂ) (z : ℂ) : ℂ := H z * F z

def deBrangesGaugeDiv (H F : ℂ → ℂ) (z : ℂ) : ℂ := F z / H z

/-- For an entire, zero-free gauge `H` with `H# = H`, `F ∈ H(E)` implies `H · F ∈ H(H E)`. -/
theorem genericMemDeBranges_gaugeMul (D : EntireDeBrangesDatum)
    {H F : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H Set.univ)
    (hHzero : ZeroFreeGauge H) (hHreal : SchwarzRealGauge H)
    (hF : GenericMemDeBranges D F) :
    GenericMemDeBranges (D.mulGauge H hH hHzero) (deBrangesGaugeMul H F) := by
  apply genericMemDeBranges_of_quotients_eq hF
  · have hHdiff : Differentiable ℂ H := by
      rwa [Complex.analyticOnNhd_univ_iff_differentiable] at hH
    exact hHdiff.mul hF.entire
  · funext x
    change H (x : ℂ) * F (x : ℂ) / (H (x : ℂ) * D.E (x : ℂ)) =
      F (x : ℂ) / D.E (x : ℂ)
    exact mul_div_mul_left _ _ (hHzero (x : ℂ))
  · funext x
    change suzukiEntireSharp (fun z => H z * F z) (x : ℂ) /
      (H (x : ℂ) * D.E (x : ℂ)) =
      suzukiEntireSharp F (x : ℂ) / D.E (x : ℂ)
    rw [suzukiEntireSharp_mul_of_schwarzReal hHreal]
    exact mul_div_mul_left _ _ (hHzero (x : ℂ))

/-- For an entire, zero-free gauge `H` with `H# = H`, `F ∈ H(H E)` implies `F / H ∈ H(E)`. -/
theorem genericMemDeBranges_gaugeDiv (D : EntireDeBrangesDatum)
    {H F : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H Set.univ)
    (hHzero : ZeroFreeGauge H) (hHreal : SchwarzRealGauge H)
    (hF : GenericMemDeBranges (D.mulGauge H hH hHzero) F) :
    GenericMemDeBranges D (deBrangesGaugeDiv H F) := by
  apply genericMemDeBranges_of_quotients_eq hF
  · have hHdiff : Differentiable ℂ H := by
      rwa [Complex.analyticOnNhd_univ_iff_differentiable] at hH
    exact hF.entire.div hHdiff hHzero
  · funext x
    change F (x : ℂ) / H (x : ℂ) / D.E (x : ℂ) =
      F (x : ℂ) / (H (x : ℂ) * D.E (x : ℂ))
    exact div_div _ _ _
  · funext x
    have hHrealx := hHreal (x : ℂ)
    rw [suzukiEntireSharp] at hHrealx
    simp only [deBrangesSharpBoundaryQuotient, suzukiEntireSharp,
      EntireDeBrangesDatum.mulGauge, deBrangesGaugeDiv]
    have hxstar : (starRingEnd ℂ) (x : ℂ) = (x : ℂ) := by simp
    rw [hxstar]
    rw [hxstar] at hHrealx
    change star (F (x : ℂ) / H (x : ℂ)) / D.E (x : ℂ) =
      star (F (x : ℂ)) / (H (x : ℂ) * D.E (x : ℂ))
    calc
      star (F (x : ℂ) / H (x : ℂ)) / D.E (x : ℂ) =
          ((starRingEnd ℂ) (F (x : ℂ)) / (starRingEnd ℂ) (H (x : ℂ))) /
            D.E (x : ℂ) := by
              exact congrArg (fun q : ℂ => q / D.E (x : ℂ))
                (map_div₀ (starRingEnd ℂ) (F (x : ℂ)) (H (x : ℂ)))
      _ = star (F (x : ℂ)) / H (x : ℂ) / D.E (x : ℂ) := by
        rw [hHrealx, starRingEnd_apply]
      _ = _ := div_div _ _ _

/-- For an entire, zero-free, Schwarz-real gauge `H`, multiplication by `H` is a `ℂ`-linear
equivalence `H(E) ≃ H(H E)` with inverse division by `H`. -/
def deBrangesGaugeLinearEquiv (D : EntireDeBrangesDatum) (H : ℂ → ℂ)
    (hH : AnalyticOnNhd ℂ H Set.univ) (hHzero : ZeroFreeGauge H)
    (hHreal : SchwarzRealGauge H) :
    GenericDeBrangesSpace D ≃ₗ[ℂ]
      GenericDeBrangesSpace (D.mulGauge H hH hHzero) where
  toFun F := ⟨deBrangesGaugeMul H F,
    genericMemDeBranges_gaugeMul D hH hHzero hHreal F.property⟩
  invFun F := ⟨deBrangesGaugeDiv H F,
    genericMemDeBranges_gaugeDiv D hH hHzero hHreal F.property⟩
  left_inv F := by
    apply Subtype.ext
    funext z
    simp [deBrangesGaugeMul, deBrangesGaugeDiv, hHzero z]
  right_inv F := by
    apply Subtype.ext
    funext z
    change H z * ((F : ℂ → ℂ) z / H z) = (F : ℂ → ℂ) z
    exact mul_div_cancel₀ _ (hHzero z)
  map_add' F G := by
    apply Subtype.ext
    funext z
    simp [deBrangesGaugeMul, mul_add]
  map_smul' c F := by
    apply Subtype.ext
    funext z
    simp [deBrangesGaugeMul, smul_eq_mul, mul_left_comm]

/-- Gauge multiplication preserves the boundary vector: `(H F)/(H E) = F/E` in `L²(ℝ)`. -/
theorem deBrangesGaugeLinearEquiv_boundary (D : EntireDeBrangesDatum) (H : ℂ → ℂ)
    (hH : AnalyticOnNhd ℂ H Set.univ) (hHzero : ZeroFreeGauge H)
    (hHreal : SchwarzRealGauge H) (F : GenericDeBrangesSpace D) :
    genericDeBrangesBoundaryMap (D.mulGauge H hH hHzero)
      (deBrangesGaugeLinearEquiv D H hH hHzero hHreal F) =
    genericDeBrangesBoundaryMap D F := by
  apply (deBrangesGaugeLinearEquiv D H hH hHzero hHreal F).property.memLp.toLp_congr
    F.property.memLp
  filter_upwards [] with x
  change H (x : ℂ) * (F : ℂ → ℂ) (x : ℂ) /
      (H (x : ℂ) * D.E (x : ℂ)) =
    (F : ℂ → ℂ) (x : ℂ) / D.E (x : ℂ)
  exact mul_div_mul_left _ _ (hHzero (x : ℂ))

/-- For an entire, zero-free, Schwarz-real gauge `H`, multiplication by `H` is a linear isometric
equivalence (unitary) from `H(E)` onto `H(H E)`. -/
noncomputable def deBrangesGaugeUnitary (D : EntireDeBrangesDatum) (H : ℂ → ℂ)
    (hH : AnalyticOnNhd ℂ H Set.univ) (hHzero : ZeroFreeGauge H)
    (hHreal : SchwarzRealGauge H) :
    GenericDeBrangesSpace D ≃ₗᵢ[ℂ]
      GenericDeBrangesSpace (D.mulGauge H hH hHzero) :=
  LinearIsometryEquiv.mk (deBrangesGaugeLinearEquiv D H hH hHzero hHreal)
    (fun F => by
      rw [norm_genericDeBranges_eq_boundary, norm_genericDeBranges_eq_boundary,
        deBrangesGaugeLinearEquiv_boundary])

theorem deBrangesGaugeUnitary_apply (D : EntireDeBrangesDatum) (H : ℂ → ℂ)
    (hH : AnalyticOnNhd ℂ H Set.univ) (hHzero : ZeroFreeGauge H)
    (hHreal : SchwarzRealGauge H) (F : GenericDeBrangesSpace D) (z : ℂ) :
    (deBrangesGaugeUnitary D H hH hHzero hHreal F : ℂ → ℂ) z =
      H z * (F : ℂ → ℂ) z := rfl

end

end GaloisForLFunctions.RHTower
