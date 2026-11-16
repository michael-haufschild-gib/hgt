import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckeAtFourCorrelationReadsTheShiftedSquare
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.CubeCorrespondences

/-!
# The Hecke-at-four trace is automorphic on the cubic cover

The correlation `F_Θ(w) = Θ(Aw) Θ(A⁻¹w)` lives on `Γ_A = Γ(3) ∩ {2 ∣ b, 2 ∣ c}`, where no Eisenstein series is
available. Its trace

`Tr F_Θ(w) = Σ_{γΓ_A ∈ Γ(3)/Γ_A} κ(γ)² F_Θ(γ⁻¹w)`   (`heckeFourTrace`)

is automorphic on all of `Γ(3)` with the multiplier `κ²` of `Θ²` (`heckeFourTrace_automorphy`), so the
Rankin–Selberg machinery of `Γ(3)` applies to it.

* `cosetTrace`, `cosetTrace_smul`: for `H ≤ G` of finite index, a character `χ` of `G` and `F` with
  `F(δx) = χ(δ)F(x)` on `H`, the coset sum `Σ_{γH} χ(γ)F(γ⁻¹x)` is independent of representatives and transforms by
  `χ` under all of `G`.
* `fourCorrelationGroup_finiteIndex`: `Γ_A` contains `Γ(3) ∩ Γ₀(2) ∩ Γ⁰(2)`, the intersection of the two finite
  covers of the diagonal correspondence `diag(2, 1)`.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein SpectralTheoryOfTheCubicCover

/-! ### Coset traces -/

section CosetTrace

variable {G M X : Type*} [Group G] [Monoid M] [MulAction M X]

/-- The coset term `γ ↦ χ(γ) F(γ⁻¹x)`. -/
def cosetTerm (ρ : G →* M) (χ : G →* ℂ) (F : X → ℂ) (x : X) (γ : G) : ℂ := χ γ * F (ρ γ⁻¹ • x)

/-- The coset trace `Σ_{γH} χ(γ) F(γ⁻¹x)`. -/
def cosetTrace (ρ : G →* M) (H : Subgroup G) [Fintype (G ⧸ H)] (χ : G →* ℂ) (F : X → ℂ) (x : X) : ℂ :=
  ∑ q : G ⧸ H, cosetTerm ρ χ F x q.out

variable {ρ : G →* M} {H : Subgroup G} {χ : G →* ℂ} {F : X → ℂ}

/-- The coset term is constant on left cosets of `H`. -/
theorem cosetTerm_congr (hF : ∀ δ ∈ H, ∀ x, F (ρ δ • x) = χ δ * F x) (x : X) {γ γ' : G}
    (h : (γ : G ⧸ H) = γ') : cosetTerm ρ χ F x γ = cosetTerm ρ χ F x γ' := by
  rw [QuotientGroup.eq] at h
  obtain ⟨δ, hδ, rfl⟩ : ∃ δ ∈ H, γ' = γ * δ := ⟨γ⁻¹ * γ', h, by group⟩
  have hχ : χ δ * χ δ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  unfold cosetTerm
  rw [mul_inv_rev, map_mul ρ, mul_smul, hF δ⁻¹ (H.inv_mem hδ), map_mul χ,
    show χ γ * χ δ * (χ δ⁻¹ * F (ρ γ⁻¹ • x)) = χ γ * (χ δ * χ δ⁻¹) * F (ρ γ⁻¹ • x) by ring, hχ, mul_one]

/-- **The coset trace transforms by `χ` under all of `G`.** -/
theorem cosetTrace_smul [Fintype (G ⧸ H)] (hF : ∀ δ ∈ H, ∀ x, F (ρ δ • x) = χ δ * F x) (g : G) (x : X) :
    cosetTrace ρ H χ F (ρ g • x) = χ g * cosetTrace ρ H χ F x := by
  unfold cosetTrace
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ fun q => ?_
  have hq : ((g⁻¹ • q).out : G ⧸ H) = ((g⁻¹ * q.out : G) : G ⧸ H) := by
    rw [QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]
  rw [MulAction.toPerm_apply, cosetTerm_congr hF x hq]
  unfold cosetTerm
  rw [mul_inv_rev, inv_inv, map_mul ρ, mul_smul, ← mul_assoc, ← map_mul χ, mul_inv_cancel_left]

end CosetTrace

/-! ### The Hecke-at-four trace -/

/-- `Γ_A` has finite index in `Γ(3)`. -/
theorem fourCorrelationGroup_finiteIndex : fourCorrelationGroup.FiniteIndex := by
  have h2 : (2 : O) ≠ 0 := by
    intro h
    have h' := congrArg ringComplex h
    rw [map_ofNat, map_zero] at h'
    norm_num at h'
  obtain ⟨hL, hR⟩ := integralDiagonal_finite_covers 2 h2
  set K := (integralDiagonalLeft (2 : O)).range ⊓ (integralDiagonalRight (2 : O)).range
  haveI : (K.subgroupOf levelThree).FiniteIndex := inferInstance
  refine Subgroup.finiteIndex_of_le (H := K.subgroupOf levelThree) fun γ hγ => ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hγ
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hγ
  have ex := integralDiagonal_entries (2 : O) x
  have ey := integralDiagonal_entries (2 : O) y
  change x.1.1 = (γ : SL(2, O)) at hx
  change y.1.2 = (γ : SL(2, O)) at hy
  refine ⟨?_, ?_⟩
  · rw [← hy, ← ey.2.1]
    exact dvd_mul_right _ _
  · rw [← hx, ex.2.2.1]
    exact dvd_mul_left _ _

instance : fourCorrelationGroup.FiniteIndex := fourCorrelationGroup_finiteIndex

noncomputable instance : Fintype (levelThree ⧸ fourCorrelationGroup) :=
  Subgroup.fintypeQuotientOfFiniteIndex

/-- `κ²` as a character of `Γ(3)`. -/
def kubotaSquare : levelThree →* ℂ := (powMonoidHom 2).comp complexCharacter

theorem kubotaSquare_apply (M : levelThree) : kubotaSquare M = complexCharacter M ^ 2 := rfl

/-- **The Hecke-at-four trace** `Tr F_Θ(w) = Σ_{γΓ_A} κ(γ)² F_Θ(γ⁻¹w)`. -/
def heckeFourTrace (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ :=
  cosetTrace complexMatrix fourCorrelationGroup kubotaSquare (heckeFourCorrelation Θ) w

/-- **The Hecke-at-four trace has the multiplier `κ²` on `Γ(3)`.** -/
theorem heckeFourTrace_automorphy (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (M : levelThree) (w : HyperbolicSpace) :
    heckeFourTrace Θ (complexMatrix M • w) = complexCharacter M ^ 2 * heckeFourTrace Θ w :=
  cosetTrace_smul (ρ := complexMatrix) (H := fourCorrelationGroup) (χ := kubotaSquare)
    (F := heckeFourCorrelation Θ) (fun δ hδ x => by
      rw [kubotaSquare_apply]
      exact heckeFourCorrelation_automorphy Θ hΘ δ hδ x) M w

/-- The Hecke-at-four trace of the projected theta function. -/
abbrev sourceFourTrace : HyperbolicSpace → ℂ := heckeFourTrace sourceTheta

theorem sourceFourTrace_automorphy (M : levelThree) (w : HyperbolicSpace) :
    sourceFourTrace (complexMatrix M • w) = complexCharacter M ^ 2 * sourceFourTrace w :=
  heckeFourTrace_automorphy sourceTheta sourceTheta_automorphy M w

end GaloisForLFunctions.OrderSixMetaplecticTheory
