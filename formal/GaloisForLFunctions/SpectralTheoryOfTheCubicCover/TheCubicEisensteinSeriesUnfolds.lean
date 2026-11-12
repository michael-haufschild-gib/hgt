import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicEisensteinSeries
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicQuotientHasFiniteVolume

/-!
# The cubic Eisenstein series unfolds

Let `Γ = levelThree` act on hyperbolic three-space with the invariant volume `μ`, let `κ` be the
cubic Kubota character, `Γ∞ = cuspSubgroup` the stabilizer of the cusp `∞`, `D_Γ` the strict
fundamental set of MMD (`hyperbolicFundamentalSet`) and `D_∞` any strict fundamental set of `Γ∞`
(`CuspDomain`: measurable, meeting every `Γ∞`-orbit exactly once). For a height profile `ψ` the
incomplete Eisenstein series is

`E(w ∣ ψ) = Σ_{x ∈ Γ∞\Γ} κ(x)⁻¹ ψ(v_x(w))`   (`incompleteEisenstein`),

with `v_x(w) = v(Mw)` the height of `w` seen from the coset `x = Γ∞M` (`cosetHeight`). For
`ψ(t) = t^s` it is the cubic Eisenstein series (`incompleteEisenstein_cpow`).

**Unfolding** (`integral_mul_incompleteEisenstein`). If `F(Mw) = κ(M)⁻¹ F(w)` for all `M ∈ Γ`
(multiplier `κ⁻¹ = κ²`, e.g. `F = θ²`) and `F · ψ(v)` is integrable on `D_∞`, then

`∫_{D_Γ} F(w) E(w ∣ ψ) dμ = ∫_{D_∞} F(w) ψ(v(w)) dμ`,

and the coset series converges absolutely in the sense of `lintegral_norm_mul_incompleteEisenstein`.

Mechanism: `D_∞` is a fundamental set for `Γ∞`, so for each `w` the elements `M ∈ Γ` with
`Mw ∈ D_∞` are exactly one per coset `Γ∞M` (`cuspSelect`). Hence
`Σ_{M ∈ Γ} 1_{D_∞}(Mw) f(Mw) = Σ_{x} f(M_x w)`, and the multiplier turns `f(M_x w)` into
`κ(x)⁻¹ F(w) ψ(v_x(w))`. Integrating over `D_Γ` and summing over `Γ` is the integral over `ℍ³`
(`IsFundamentalDomain.integral_eq_tsum''`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical MatrixGroups ENNReal

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein

/-! ### The cusp subgroup and its strict fundamental set -/

/-- The stabilizer `Γ∞` of the cusp `∞` as a subgroup of `SL₂(O)`. -/
def cuspSubgroup : Subgroup (SL(2, O)) := cuspStabilizer.map levelThree.subtype

theorem cuspSubgroup_le : cuspSubgroup ≤ levelThree := by
  rintro _ ⟨T, -, rfl⟩
  exact T.2

/-- A strict fundamental set of `Γ∞`: measurable, and every orbit meets it exactly once. -/
structure CuspDomain where
  carrier : Set HyperbolicSpace
  measurable : MeasurableSet carrier
  unique : ∀ w : HyperbolicSpace, ∃! k : cuspSubgroup, k • w ∈ carrier

/-- MMD's lexicographic fundamental set of `Γ∞`. -/
def CuspDomain.lex : CuspDomain :=
  ⟨hyperbolicFundamentalSet cuspSubgroup, hyperbolicFundamentalSet_measurable cuspSubgroup,
    hyperbolicFundamentalSet_unique cuspSubgroup cuspSubgroup_le⟩

/-- The strict fundamental set `D_Γ` of `Γ`. -/
abbrev levelSet : Set HyperbolicSpace := hyperbolicFundamentalSet levelThree

/-- A cusp-stabilizer element of `Γ` as an element of `Γ∞`. -/
def toCusp (T : levelThree) (hT : T ∈ cuspStabilizer) : cuspSubgroup :=
  ⟨(T : SL(2, O)), ⟨T, hT, rfl⟩⟩

theorem toCusp_smul (T : levelThree) (hT : T ∈ cuspStabilizer) (w : HyperbolicSpace) :
    toCusp T hT • w = T • w := rfl

/-- **One selected element per coset.** For each `w`, the elements `M ∈ Γ` with `Mw ∈ D_∞`
correspond bijectively to the cosets `Γ∞M`. -/
def cuspSelect (D : CuspDomain) (w : HyperbolicSpace) : {M : levelThree // M • w ∈ D.carrier} ≃ CuspCosets :=
  Equiv.ofBijective (fun M => cosetOf M.1) ⟨by
    rintro ⟨M, hM⟩ ⟨N, hN⟩ h
    obtain ⟨T, hT, rfl⟩ := (cosetOf_eq_iff M N).mp h
    have hT' : toCusp T hT • (N • w) ∈ D.carrier := by rwa [toCusp_smul, ← mul_smul]
    have h1 : (1 : cuspSubgroup) • (N • w) ∈ D.carrier := by rwa [one_smul]
    have hk : toCusp T hT = 1 := (D.unique (N • w)).unique hT' h1
    have hval : ((toCusp T hT : cuspSubgroup) : SL(2, O)) = ((1 : cuspSubgroup) : SL(2, O)) :=
      congrArg Subtype.val hk
    have hT1 : T = 1 := Subtype.ext hval
    exact Subtype.ext (by simp [hT1]), by
    intro c
    induction c using Quotient.inductionOn with | _ N =>
    obtain ⟨k, hk, -⟩ := D.unique (N • w)
    obtain ⟨T, hT, hTk⟩ := Subgroup.mem_map.mp k.2
    have hkT : k = toCusp T hT := Subtype.ext hTk.symm
    refine ⟨⟨T * N, ?_⟩, ?_⟩
    · rw [mul_smul, ← toCusp_smul T hT, ← hkT]
      exact hk
    · exact (cosetOf_eq_iff (T * N) N).mpr ⟨T, hT, rfl⟩⟩

theorem cosetOf_cuspSelect_symm (D : CuspDomain) (w : HyperbolicSpace) (c : CuspCosets) :
    cosetOf ((cuspSelect D w).symm c).1 = c :=
  (cuspSelect D w).apply_symm_apply c

/-- **The coset sum.** For any `g`, the sum over `Γ` of `1_{D_∞}(Mw) g(Mw)` is the sum over the
cosets of `g` at the selected elements. -/
theorem tsum_indicator_smul {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (D : CuspDomain)
    (g : HyperbolicSpace → E) (w : HyperbolicSpace) :
    ∑' M : levelThree, D.carrier.indicator g (M • w) =
      ∑' c : CuspCosets, g (((cuspSelect D w).symm c).1 • w) := by
  have h : ∀ M : levelThree, D.carrier.indicator g (M • w) =
      {M : levelThree | M • w ∈ D.carrier}.indicator (fun M => g (M • w)) M := by
    intro M
    by_cases hM : M • w ∈ D.carrier
    · rw [Set.indicator_of_mem hM, Set.indicator_of_mem
        (show M ∈ {M : levelThree | M • w ∈ D.carrier} from hM)]
    · rw [Set.indicator_of_notMem hM, Set.indicator_of_notMem
        (show M ∉ {M : levelThree | M • w ∈ D.carrier} from hM)]
  simp_rw [h]
  rw [← tsum_subtype {M : levelThree | M • w ∈ D.carrier} (fun M => g (M • w))]
  exact ((cuspSelect D w).symm.tsum_eq (fun M => g (M.1 • w))).symm

/-! ### The incomplete Eisenstein series -/

/-- The incomplete Eisenstein series `E(w ∣ ψ) = Σ_{x ∈ Γ∞\Γ} κ(x)⁻¹ ψ(v_x(w))`. -/
def incompleteEisenstein (ψ : ℝ → ℂ) (w : HyperbolicSpace) : ℂ :=
  ∑' x : CuspCosets, (cosetCharacter x)⁻¹ * ψ (cosetHeight x w)

/-- For `ψ(t) = t^s` the incomplete series is the cubic Eisenstein series. -/
theorem incompleteEisenstein_cpow (s : ℂ) (w : HyperbolicSpace) :
    incompleteEisenstein (fun t => (t : ℂ) ^ s) w = hyperbolicEisenstein s w :=
  (hyperbolicEisenstein_eq_height_series s w).symm

theorem levelThree_smul (M : levelThree) (w : HyperbolicSpace) : M • w = complexMatrix M • w := rfl

/-- At the selected element of a coset, `F(Mw) ψ(v(Mw)) = κ(x)⁻¹ F(w) ψ(v_x(w))`. -/
theorem selected_value (F : HyperbolicSpace → ℂ)
    (hF : ∀ (M : levelThree) (w : HyperbolicSpace), F (complexMatrix M • w) = (complexCharacter M)⁻¹ * F w)
    (ψ : ℝ → ℂ) (w : HyperbolicSpace) (M : levelThree) :
    F (M • w) * ψ (hyperbolicHeight (M • w)) =
      F w * ((cosetCharacter (cosetOf M))⁻¹ * ψ (cosetHeight (cosetOf M) w)) := by
  rw [levelThree_smul, hF, cosetHeight_cosetOf, cosetCharacter_cosetOf]
  ring

/-- The norm of the selected value is `|F(w)| |ψ(v_x(w))|` (`|κ| = 1`). -/
theorem selected_norm (F : HyperbolicSpace → ℂ)
    (hF : ∀ (M : levelThree) (w : HyperbolicSpace), F (complexMatrix M • w) = (complexCharacter M)⁻¹ * F w)
    (ψ : ℝ → ℂ) (w : HyperbolicSpace) (M : levelThree) :
    ‖F (M • w) * ψ (hyperbolicHeight (M • w))‖ₑ =
      ‖F w‖ₑ * ‖ψ (cosetHeight (cosetOf M) w)‖ₑ := by
  have hu : ‖(complexCharacter M)⁻¹‖ₑ = 1 := by
    rw [← ofReal_norm, norm_inv, norm_complexCharacter, inv_one, ENNReal.ofReal_one]
  rw [selected_value F hF ψ w M, enorm_mul, enorm_mul, cosetCharacter_cosetOf, hu, one_mul]

/-! ### Unfolding -/

section Unfolding

variable (D : CuspDomain) (F : HyperbolicSpace → ℂ)
  (hF : ∀ (M : levelThree) (w : HyperbolicSpace), F (complexMatrix M • w) = (complexCharacter M)⁻¹ * F w)
  (ψ : ℝ → ℂ)

/-- The unfolded integrand `f = F · ψ(v)`. -/
def unfolded (F : HyperbolicSpace → ℂ) (ψ : ℝ → ℂ) (w : HyperbolicSpace) : ℂ :=
  F w * ψ (hyperbolicHeight w)

include hF in
/-- **Absolute unfolding.** `∫⁻_{D_Γ} Σ_x |F(w)| |ψ(v_x(w))| dμ = ∫⁻_{D_∞} |F ψ(v)| dμ`. -/
theorem lintegral_norm_mul_incompleteEisenstein
    (hmeas : AEMeasurable (fun w => ‖unfolded F ψ w‖ₑ) hyperbolicVolume) :
    ∫⁻ w in levelSet, ∑' x : CuspCosets, ‖F w‖ₑ * ‖ψ (cosetHeight x w)‖ₑ ∂hyperbolicVolume =
      ∫⁻ w in D.carrier, ‖unfolded F ψ w‖ₑ ∂hyperbolicVolume := by
  have hD := hyperbolicFundamentalSet_isFundamentalDomain levelThree le_rfl hyperbolicVolume
  have hDm := D.measurable
  rw [← lintegral_indicator hDm, hD.lintegral_eq_tsum'']
  rw [← lintegral_tsum]
  · refine setLIntegral_congr_fun (hyperbolicFundamentalSet_measurable levelThree) fun w _ => ?_
    rw [tsum_indicator_smul D]
    refine tsum_congr fun c => ?_
    rw [unfolded, selected_norm F hF ψ w, cosetOf_cuspSelect_symm]
  · intro M
    exact ((hmeas.indicator hDm).comp_quasiMeasurePreserving
      (measurePreserving_smul M hyperbolicVolume).quasiMeasurePreserving).restrict

include hF in
/-- **Unfolding of the incomplete cubic Eisenstein series.** For `F` of multiplier `κ⁻¹` with
`F · ψ(v)` integrable on `D_∞`: `∫_{D_Γ} F · E(·∣ψ) dμ = ∫_{D_∞} F · ψ(v) dμ`. -/
theorem integral_mul_incompleteEisenstein
    (hint : IntegrableOn (unfolded F ψ) D.carrier hyperbolicVolume) :
    ∫ w in levelSet, F w * incompleteEisenstein ψ w ∂hyperbolicVolume =
      ∫ w in D.carrier, unfolded F ψ w ∂hyperbolicVolume := by
  have hD := hyperbolicFundamentalSet_isFundamentalDomain levelThree le_rfl hyperbolicVolume
  have hDm := D.measurable
  have hI : Integrable (D.carrier.indicator (unfolded F ψ)) hyperbolicVolume :=
    (integrable_indicator_iff hDm).mpr hint
  rw [← integral_indicator hDm, hD.integral_eq_tsum'' _ hI]
  rw [← integral_tsum]
  · refine setIntegral_congr_fun (hyperbolicFundamentalSet_measurable levelThree) fun w _ => ?_
    rw [tsum_indicator_smul D, incompleteEisenstein, ← tsum_mul_left]
    refine tsum_congr fun c => ?_
    rw [unfolded, selected_value F hF ψ w, cosetOf_cuspSelect_symm]
  · intro M
    exact (hI.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_smul M hyperbolicVolume)).restrict
  · rw [← hD.lintegral_eq_tsum'' (fun w => ‖D.carrier.indicator (unfolded F ψ) w‖ₑ)]
    exact hI.2.ne

end Unfolding

/-- **Unfolding of the cubic Eisenstein series.** For `F` of multiplier `κ⁻¹` with `F v^s`
integrable on `D_∞`: `∫_{D_Γ} F · E(·, s) dμ = ∫_{D_∞} F · v^s dμ`. -/
theorem integral_mul_hyperbolicEisenstein (D : CuspDomain) (F : HyperbolicSpace → ℂ)
    (hF : ∀ (M : levelThree) (w : HyperbolicSpace), F (complexMatrix M • w) = (complexCharacter M)⁻¹ * F w)
    (s : ℂ) (hint : IntegrableOn (unfolded F (fun t => (t : ℂ) ^ s)) D.carrier hyperbolicVolume) :
    ∫ w in levelSet, F w * hyperbolicEisenstein s w ∂hyperbolicVolume =
      ∫ w in D.carrier, F w * (hyperbolicHeight w : ℂ) ^ s ∂hyperbolicVolume := by
  simp_rw [← incompleteEisenstein_cpow]
  exact integral_mul_incompleteEisenstein D F hF _ hint

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
