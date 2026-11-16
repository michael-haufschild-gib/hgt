import GaloisForLFunctions.OrderSixMetaplecticTheory.TheConjugateCubicTwistAtEveryOddPrimaryPrimeHasADoublePole

/-!
# The weighted fractional trace is invariant under the modular group

For a weight φ on O/q invariant under multiplication by nonzero squares (φ(xd²) = φ(x), e.g. the quadratic character
λ_q), the weighted sum of opposite fractional translations

G_φ(w) = Σ_{t ∈ O/q} φ(t) θ(T_tw)θ(T_{−t}w)   (`fracSumW`)

has the multiplier κ² on Γ(3) ∩ Γ₀(q²) (δ ∈ Γ₀(q²) moves t to td², which preserves φ) (`fracSumW_automorphy`), and its
trace to Γ(3) is invariant under SL₂(ℤ) (`fracTraceW_rational`): the S- and T-identities of the unweighted trace hold
pair by pair (`fracCorrelation_S`, `fracCorrelation_T`). Over the projective line modulo q² (`fracTraceW_eq`)

Tr G_φ(w) = G_φ(w) + Σ_{x ≢ 0} G_φ(L_{qx}w) + Σ_{s ∈ O/q²} G_φ(ST(3s)w),

and G_φ(Sy) = φ(0)θ(y)² + Σ_{x ≢ 0} φ(x)χ(−9x²)θ^{(−β_{−x})}(A_q⁻¹y)θ^{(−β_x)}(A_q⁻¹y) (`fracSumW_sO`).
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- A weight on O/q invariant under nonzero squares. -/
def SquareInvariant (φ : P.Res → ℂ) : Prop := ∀ x d : P.Res, d ≠ 0 → φ (x * d ^ 2) = φ x

/-- G_φ = Σ_t φ(t) θ(T_tw)θ(T_{−t}w). -/
def fracSumW (φ : P.Res → ℂ) (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ :=
  ∑ x : P.Res, φ x * P.fracCorrelation Θ (P.lift x) w

/-- **The weighted sum has the multiplier κ² on Γ(3) ∩ Γ₀(q²).** -/
theorem fracSumW_automorphy (φ : P.Res → ℂ) (hφ : P.SquareInvariant φ) (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (δ : levelThree) (hδ : δ ∈ P.levelSqGroup) (w : HyperbolicSpace) :
    P.fracSumW φ Θ (complexMatrix δ • w) = complexCharacter δ ^ 2 * P.fracSumW φ Θ w := by
  obtain ⟨c₂, hc⟩ := hδ
  have hdet : (δ : SL(2, O)) 0 0 * (δ : SL(2, O)) 1 1 - (δ : SL(2, O)) 0 1 * (P.p ^ 2 * c₂) = 1 := by
    rw [← hc, ← Matrix.det_fin_two]
    exact (δ : SL(2, O)).det_coe
  have ha : (3 : O) ∣ (δ : SL(2, O)) 0 0 - 1 := by simpa using levelThree_entry δ 0 0
  have hb : (3 : O) ∣ (δ : SL(2, O)) 0 1 := by simpa using levelThree_entry δ 0 1
  have hc3 : (3 : O) ∣ P.p ^ 2 * c₂ := by rw [← hc]; simpa using levelThree_entry δ 1 0
  have hd : (3 : O) ∣ (δ : SL(2, O)) 1 1 - 1 := by simpa using levelThree_entry δ 1 1
  set d := (δ : SL(2, O)) 1 1
  have hκ : complexCharacter δ = ringComplex (symbol (P.p ^ 2 * c₂) ((δ : SL(2, O)) 0 0)) := by
    rw [complexCharacter_eq_symbol, hc]
  have hterm : ∀ t : O, P.fracCorrelation Θ t (complexMatrix δ • w) =
      complexCharacter δ ^ 2 * P.fracCorrelation Θ (t * d ^ 2) w := by
    intro t
    unfold fracCorrelation
    rw [← mul_smul, P.fracShift_mul δ c₂ hc t hdet ha hb hc3 hd, mul_smul, hΘ, ← mul_smul,
      P.fracShift_mul δ c₂ hc (-t) hdet ha hb hc3 hd, mul_smul, hΘ, hκ,
      ← P.fracConj_character_mul _ _ c₂ _ t hdet ha hb hc3 hd, show -t * d ^ 2 = -(t * d ^ 2) by ring]
    ring
  have hd0 : P.res d ≠ 0 := by
    intro h0
    have h := congrArg P.res hdet
    rw [map_sub, map_mul, map_mul, h0, mul_zero, map_mul, map_pow, P.res_p] at h
    simp at h
  unfold fracSumW
  simp_rw [hterm]
  rw [Finset.mul_sum]
  have hbij : Function.Bijective (fun x : P.Res => x * P.res d ^ 2) :=
    mulRight_bijective₀ _ (pow_ne_zero 2 hd0)
  rw [← hbij.sum_comp (fun y => complexCharacter δ ^ 2 * (φ y * P.fracCorrelation Θ (P.lift y) w))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hφ x _ hd0, show x * P.res d ^ 2 = P.res (P.lift x * d ^ 2) by rw [map_mul, map_pow, res_lift],
    P.fracCorrelation_lift Θ hΘ]
  ring

/-- The weighted trace. -/
def fracTraceW (φ : P.Res → ℂ) (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ :=
  cosetTrace complexMatrix P.levelSqGroup kubotaSquare (P.fracSumW φ Θ) w

theorem fracTraceW_automorphy (φ : P.Res → ℂ) (hφ : P.SquareInvariant φ) (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (M : levelThree) (w : HyperbolicSpace) :
    P.fracTraceW φ Θ (complexMatrix M • w) = complexCharacter M ^ 2 * P.fracTraceW φ Θ w :=
  cosetTrace_smul (ρ := complexMatrix) (H := P.levelSqGroup) (χ := kubotaSquare)
    (F := P.fracSumW φ Θ) (fun δ hδ x => by
      rw [kubotaSquare_apply]
      exact P.fracSumW_automorphy φ hφ Θ hΘ δ hδ x) M w

theorem fracTraceW_conj (φ : P.Res → ℂ) (hφ : P.SquareInvariant φ) (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (g : SL(2, O)) (hA : ∀ γ : levelThree, conjLevel g γ ∈ P.levelSqGroup ↔ γ ∈ P.levelSqGroup)
    (hκ : ∀ γ : levelThree, complexCharacter (conjLevel g γ) = complexCharacter γ)
    (hF : ∀ w, P.fracSumW φ Θ (integralComplexMatrix g • w) = P.fracSumW φ Θ w)
    (w : HyperbolicSpace) :
    P.fracTraceW φ Θ (integralComplexMatrix g • w) = P.fracTraceW φ Θ w := by
  have hFΘ : ∀ δ ∈ P.levelSqGroup, ∀ x, P.fracSumW φ Θ (complexMatrix δ • x) = kubotaSquare δ * P.fracSumW φ Θ x :=
    fun δ hδ x => by
      rw [kubotaSquare_apply]
      exact P.fracSumW_automorphy φ hφ Θ hΘ δ hδ x
  unfold fracTraceW cosetTrace
  refine Fintype.sum_equiv (P.fracConjCoset g hA) _ _ fun q => ?_
  have hq : (((P.fracConjCoset g hA q).out : levelThree) : levelThree ⧸ P.levelSqGroup) =
      ((conjLevel g q.out : levelThree) : _) := by
    rw [QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    exact P.fracConjCoset_mk g hA q.out
  rw [cosetTerm_congr hFΘ w hq]
  unfold cosetTerm
  rw [kubotaSquare_apply, kubotaSquare_apply, hκ]
  have hmat : complexMatrix (conjLevel g q.out)⁻¹ =
      (integralComplexMatrix g)⁻¹ * complexMatrix q.out⁻¹ * integralComplexMatrix g := by
    rw [map_inv, map_inv, complexMatrix_eq, complexMatrix_eq, conjLevel_coe, map_mul, map_mul, map_inv]
    group
  have hw : complexMatrix q.out⁻¹ • integralComplexMatrix g • w =
      integralComplexMatrix g • (complexMatrix (conjLevel g q.out)⁻¹ • w) := by
    rw [hmat, ← mul_smul, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hw, hF]

section Rational

variable (Θ : HyperbolicSpace → ℂ)
  (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
  (hΘr : ∀ (r : SL(2, ℤ)) (w : HyperbolicSpace), Θ (integralComplexMatrix (rationalEmbedding r) • w) = Θ w)
include hΘ hΘr

omit hΘ in
theorem fracCorrelation_T (t : O) (w : HyperbolicSpace) :
    P.fracCorrelation Θ t (integralComplexMatrix (tPowO 1) • w) = P.fracCorrelation Θ t w := by
  unfold fracCorrelation
  rw [← mul_smul, ← mul_smul, P.fracShift_mul_T, P.fracShift_mul_T, mul_smul, mul_smul, tPowO, hΘr, hΘr]

theorem fracCorrelation_S {k m : O} (hkm : P.p ^ 4 * m + 9 * k ^ 2 = 1) (t : O) (w : HyperbolicSpace) :
    P.fracCorrelation Θ t (integralComplexMatrix sO • w) =
      P.fracCorrelation Θ t (complexMatrix (P.gammaS hkm) • w) := by
  have hS : ∀ y, Θ (integralComplexMatrix sO • y) = Θ y := hΘr ModularGroup.S
  have key : ∀ t : O, Θ (P.fracShift t • integralComplexMatrix sO • w) =
      complexCharacter (P.deltaS hkm t) * Θ (P.fracShift t • complexMatrix (P.gammaS hkm) • w) := by
    intro t
    rw [← mul_smul, P.fracShift_mul_S hkm, mul_smul, hS, mul_smul, hΘ, mul_smul]
  unfold fracCorrelation
  rw [key, key]
  linear_combination (Θ (P.fracShift t • complexMatrix (P.gammaS hkm) • w) *
    Θ (P.fracShift (-t) • complexMatrix (P.gammaS hkm) • w)) * P.deltaS_character_mul hkm t

theorem fracTraceW_rational (φ : P.Res → ℂ) (hφ : P.SquareInvariant φ) (r : SL(2, ℤ)) (w : HyperbolicSpace) :
    P.fracTraceW φ Θ (integralComplexMatrix (rationalEmbedding r) • w) = P.fracTraceW φ Θ w := by
  have hT : ∀ y, P.fracTraceW φ Θ (integralComplexMatrix (tPowO 1) • y) = P.fracTraceW φ Θ y := fun y =>
    P.fracTraceW_conj φ hφ Θ hΘ (tPowO 1) P.conjLevel_mem_iff_T (complexCharacter_conjLevel_rational _)
      (fun x => by
        unfold fracSumW
        exact Finset.sum_congr rfl fun t _ => by rw [P.fracCorrelation_T Θ hΘr]) y
  have hS : ∀ y, P.fracTraceW φ Θ (integralComplexMatrix sO • y) = P.fracTraceW φ Θ y := by
    intro y
    obtain ⟨k, m, hkm, hk⟩ := P.exists_sData
    have hg : P.gS hkm = sO * ((P.gammaS hkm : levelThree) : SL(2, O))⁻¹ := by
      rw [← P.gS_mul_gammaS hkm]
      group
    have hgS : ∀ x, P.fracSumW φ Θ (integralComplexMatrix (P.gS hkm) • x) = P.fracSumW φ Θ x := by
      intro x
      unfold fracSumW
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hg, map_mul, mul_smul, P.fracCorrelation_S Θ hΘ hΘr hkm, complexMatrix_eq, ← mul_smul, ← map_mul,
        mul_inv_cancel, map_one, one_smul]
    have hw : integralComplexMatrix sO • y = integralComplexMatrix (P.gS hkm) • (complexMatrix (P.gammaS hkm) • y) := by
      rw [← P.gS_mul_gammaS hkm, map_mul, mul_smul]
      rfl
    rw [hw, P.fracTraceW_conj φ hφ Θ hΘ (P.gS hkm) (P.conjLevel_mem_iff_gS hkm)
      (P.complexCharacter_conjLevel_gS hkm hk) hgS, P.fracTraceW_automorphy φ hφ Θ hΘ,
      P.gammaS_character hkm hk, one_pow, one_mul]
  have hr : r ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top r
  induction hr using Subgroup.closure_induction generalizing w with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hS w
    · rw [show rationalEmbedding ModularGroup.T = tPowO 1 by rw [tPowO, zpow_one]]
      exact hT w
  | one => rw [map_one, map_one, one_smul]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, mul_smul, hx, hy]
  | inv x _ hx =>
    rw [← hx (integralComplexMatrix (rationalEmbedding x⁻¹) • w), ← mul_smul, ← map_mul, ← map_mul, mul_inv_cancel,
      map_one, map_one, one_smul]

end Rational

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
