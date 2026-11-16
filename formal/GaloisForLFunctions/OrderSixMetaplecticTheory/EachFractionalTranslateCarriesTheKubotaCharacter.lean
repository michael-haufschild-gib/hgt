import GaloisForLFunctions.OrderSixMetaplecticTheory.TheSexticTwistAndTheQuadraticTwistShareTheDoublePole

/-!
# Each fractional translate carries the Kubota character

For `δ = [[a, b], [q²c₂, d]] ∈ Γ(3) ∩ Γ₀(q²)` the matrix `M_t = T_tδT_{−td²}` has `κ(M_t) = κ(δ)`
(`fracConj_character_eq`). Write `(q²c₂/b)₃ = (q/b)₃²(c₂/b)₃`. By cubic reciprocity the first factor only
sees `b mod q`; the second only sees `b mod 9c₂`; `3tqc₂` vanishes modulo both. So a single
translate already moves with the multiplier `κ`: `θ(T_tδw) = κ(δ)θ(T_{td²}w)`
(`theta_fracShift_automorphy`). At `S` it picks up the phase `κ(δ₀)`, and `κ(δ₀)² = 1`
(`theta_fracShift_S`).

Hence, for every ratio `c ∈ O/q` and every weight `φ` invariant under squares, the **ratio pair sum**

`G^{(c)}_φ(w) = Σ_x φ(x) θ(T_xw) θ(T_{cx}w)`   (`ratioSum`)

has the multiplier `κ²` on `Γ(3) ∩ Γ₀(q²)` (`ratioSum_automorphy`). Its trace to `Γ(3)` is
`SL₂(ℤ)`-invariant (`ratioTrace_rational`) and decomposes over `P¹(O/q²)`
(`ratioTrace_eq`). Over the cusp `0` it reads low points of low points with the phases
`χ(−3x)χ(−3cx)` (`ratioSum_sO`). The opposite pairs `c = −1` give the fractional sums.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### One translate -/

theorem three_dvd_of_three_dvd_sq_mul {c₂ : O} (h : (3 : O) ∣ P.p ^ 2 * c₂) : (3 : O) ∣ c₂ :=
  (P.isCoprime_three.pow_right (n := 2)).dvd_of_dvd_mul_left h

/-- **One fractional translate carries the Kubota character**: `κ(M_t) = κ(δ)`. -/
theorem fracConj_character_eq (a b c₂ d t : O) (hdet : a * d - b * (P.p ^ 2 * c₂) = 1) (ha : (3 : O) ∣ a - 1)
    (hb : (3 : O) ∣ b) (hc : (3 : O) ∣ P.p ^ 2 * c₂) (hd : (3 : O) ∣ d - 1) :
    complexCharacter (P.fracConj a b c₂ d t hdet ha hb hc hd) = ringComplex (symbol (P.p ^ 2 * c₂) a) := by
  rw [fracConj_character]
  congr 1
  obtain ⟨e, he⟩ := P.three_dvd_of_three_dvd_sq_mul hc
  have hla : lambda ^ 2 ∣ a - 1 := lambda_sq_dvd_three.trans ha
  have hX : lambda ^ 2 ∣ 3 * t * P.p * c₂ := dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left lambda_sq_dvd_three _) _) _
  have hA : lambda ^ 2 ∣ a + 3 * t * P.p * c₂ - 1 := by
    convert dvd_add hla hX using 1
    ring
  have hp : symbol P.p (a + 3 * t * P.p * c₂) = symbol P.p a := by
    rw [symbol_reciprocity _ _ P.primary hA, symbol_reciprocity _ _ P.primary hla]
    exact symbol_congr ⟨3 * t * c₂, by ring⟩
  have hc₂ : symbol c₂ (a + 3 * t * P.p * c₂) = symbol c₂ a :=
    symbol_denominator_congr c₂ _ _ hA hla ⟨t * P.p * e, by rw [he]; ring⟩ ⟨3 * t * P.p, by ring⟩
  rw [show P.p ^ 2 * c₂ = P.p * (P.p * c₂) by ring, symbol_mul_numerator, symbol_mul_numerator,
    symbol_mul_numerator, symbol_mul_numerator, hp, hc₂]

section Single

variable (Θ : HyperbolicSpace → ℂ)
  (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
include hΘ

/-- **A translate moves with the multiplier `κ`**: `Θ(T_tδw) = κ(δ)Θ(T_{td²}w)`. -/
theorem theta_fracShift_automorphy (δ : levelThree) (hδ : δ ∈ P.levelSqGroup) (t : O) (w : HyperbolicSpace) :
    Θ (P.fracShift t • complexMatrix δ • w) =
      complexCharacter δ * Θ (P.fracShift (t * (δ : SL(2, O)) 1 1 ^ 2) • w) := by
  obtain ⟨c₂, hc⟩ := hδ
  have hdet : (δ : SL(2, O)) 0 0 * (δ : SL(2, O)) 1 1 - (δ : SL(2, O)) 0 1 * (P.p ^ 2 * c₂) = 1 := by
    rw [← hc, ← Matrix.det_fin_two]
    exact (δ : SL(2, O)).det_coe
  have ha : (3 : O) ∣ (δ : SL(2, O)) 0 0 - 1 := by simpa using levelThree_entry δ 0 0
  have hb : (3 : O) ∣ (δ : SL(2, O)) 0 1 := by simpa using levelThree_entry δ 0 1
  have hc3 : (3 : O) ∣ P.p ^ 2 * c₂ := by rw [← hc]; simpa using levelThree_entry δ 1 0
  have hd : (3 : O) ∣ (δ : SL(2, O)) 1 1 - 1 := by simpa using levelThree_entry δ 1 1
  rw [← mul_smul, P.fracShift_mul δ c₂ hc t hdet ha hb hc3 hd, mul_smul, hΘ, P.fracConj_character_eq,
    complexCharacter_eq_symbol, hc]

theorem theta_fracShift_add (t s : O) (w : HyperbolicSpace) :
    Θ (P.fracShift (t + P.p * s) • w) = Θ (P.fracShift t • w) := by
  have hP := P.ringComplex_ne_zero
  have hsh : P.fracShift (t + P.p * s) = complexMatrix (transThree s) * P.fracShift t := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [fracShift, complexTranslation, complexMatrix_apply, transThree, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.mul_apply, Fin.sum_univ_two, map_ofNat]
    field_simp
  rw [hsh, mul_smul, hΘ, complexCharacter_transThree, one_mul]

theorem theta_fracShift_res (t : O) (w : HyperbolicSpace) :
    Θ (P.fracShift (P.lift (P.res t)) • w) = Θ (P.fracShift t • w) := by
  have h : P.res (P.lift (P.res t) - t) = 0 := by rw [map_sub, res_lift, sub_self]
  obtain ⟨s, hs⟩ := (P.res_eq_zero_iff _).mp h
  rw [show P.lift (P.res t) = t + P.p * s by linear_combination hs, P.theta_fracShift_add Θ hΘ]

variable (hΘr : ∀ (r : SL(2, ℤ)) (w : HyperbolicSpace), Θ (integralComplexMatrix (rationalEmbedding r) • w) = Θ w)
include hΘr

omit hΘ in
theorem theta_fracShift_T (t : O) (w : HyperbolicSpace) :
    Θ (P.fracShift t • integralComplexMatrix (tPowO 1) • w) = Θ (P.fracShift t • w) := by
  rw [← mul_smul, P.fracShift_mul_T, mul_smul, tPowO, hΘr]

omit hΘ hΘr in
theorem deltaS_character_eq {k m : O} (hkm : P.p ^ 4 * m + 9 * k ^ 2 = 1) (t : O) :
    complexCharacter (P.deltaS hkm t) = complexCharacter (P.deltaS hkm 0) := by
  rw [complexCharacter_eq_symbol, complexCharacter_eq_symbol, (P.deltaS_entries hkm t).1, (P.deltaS_entries hkm t).2,
    (P.deltaS_entries hkm 0).1, (P.deltaS_entries hkm 0).2]
  congr 1
  rw [show P.p ^ 2 * m = P.p * (P.p * m) by ring, symbol_mul_denominator, symbol_mul_denominator,
    symbol_mul_denominator, symbol_mul_denominator,
    symbol_congr (x := -3 * k - 3 * t * P.p * m) (y := -3 * k - 3 * 0 * P.p * m) (d := P.p) ⟨-(3 * t * m), by ring⟩,
    symbol_congr (x := -3 * k - 3 * t * P.p * m) (y := -3 * k - 3 * 0 * P.p * m) (d := m) ⟨-(3 * t * P.p), by ring⟩]

omit hΘ hΘr in
theorem deltaS_character_sq {k m : O} (hkm : P.p ^ 4 * m + 9 * k ^ 2 = 1) :
    complexCharacter (P.deltaS hkm 0) ^ 2 = 1 := by
  have h := P.deltaS_character_mul hkm 0
  rwa [neg_zero, ← pow_two] at h

/-- **A translate at `S`**: `Θ(T_tSw) = κ(δ₀)Θ(T_tγ₀w)`. -/
theorem theta_fracShift_S {k m : O} (hkm : P.p ^ 4 * m + 9 * k ^ 2 = 1) (t : O) (w : HyperbolicSpace) :
    Θ (P.fracShift t • integralComplexMatrix sO • w) =
      complexCharacter (P.deltaS hkm 0) * Θ (P.fracShift t • complexMatrix (P.gammaS hkm) • w) := by
  have hS : ∀ y, Θ (integralComplexMatrix sO • y) = Θ y := hΘr ModularGroup.S
  rw [← mul_smul, P.fracShift_mul_S hkm, mul_smul, hS, mul_smul, hΘ, mul_smul, P.deltaS_character_eq hkm t]

end Single

/-! ### Ratio pair sums -/

/-- `θ(T_xw)θ(T_{cx}w)`. -/
def ratioCorrelation (c : P.Res) (Θ : HyperbolicSpace → ℂ) (x : P.Res) (w : HyperbolicSpace) : ℂ :=
  Θ (P.fracShift (P.lift x) • w) * Θ (P.fracShift (P.lift (c * x)) • w)

/-- `G^{(c)}_φ = Σ_x φ(x) θ(T_xw)θ(T_{cx}w)`. -/
def ratioSum (φ : P.Res → ℂ) (c : P.Res) (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ :=
  ∑ x : P.Res, φ x * P.ratioCorrelation c Θ x w

/-- **The ratio pair sums have the multiplier `κ²` on `Γ(3) ∩ Γ₀(q²)`.** -/
theorem ratioSum_automorphy (φ : P.Res → ℂ) (hφ : P.SquareInvariant φ) (c : P.Res) (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (δ : levelThree) (hδ : δ ∈ P.levelSqGroup) (w : HyperbolicSpace) :
    P.ratioSum φ c Θ (complexMatrix δ • w) = complexCharacter δ ^ 2 * P.ratioSum φ c Θ w := by
  set d := (δ : SL(2, O)) 1 1 with hddef
  have hd0 : P.res d ≠ 0 := by
    obtain ⟨c₂, hc⟩ := hδ
    have hdet : (δ : SL(2, O)) 0 0 * (δ : SL(2, O)) 1 1 - (δ : SL(2, O)) 0 1 * (P.p ^ 2 * c₂) = 1 := by
      rw [← hc, ← Matrix.det_fin_two]
      exact (δ : SL(2, O)).det_coe
    intro h0
    have h := congrArg P.res hdet
    rw [map_sub, map_mul, map_mul, ← hddef, h0, mul_zero, map_mul, map_pow, P.res_p] at h
    simp at h
  have hterm : ∀ x : P.Res, P.ratioCorrelation c Θ x (complexMatrix δ • w) =
      complexCharacter δ ^ 2 * P.ratioCorrelation c Θ (x * P.res d ^ 2) w := by
    intro x
    unfold ratioCorrelation
    rw [P.theta_fracShift_automorphy Θ hΘ δ hδ, P.theta_fracShift_automorphy Θ hΘ δ hδ, ← hddef,
      ← P.theta_fracShift_res Θ hΘ (P.lift x * d ^ 2), ← P.theta_fracShift_res Θ hΘ (P.lift (c * x) * d ^ 2),
      show P.res (P.lift x * d ^ 2) = x * P.res d ^ 2 by rw [map_mul, map_pow, res_lift],
      show P.res (P.lift (c * x) * d ^ 2) = c * (x * P.res d ^ 2) by rw [map_mul, map_pow, res_lift]; ring]
    ring
  unfold ratioSum
  simp_rw [hterm]
  rw [Finset.mul_sum]
  have hbij : Function.Bijective (fun x : P.Res => x * P.res d ^ 2) := mulRight_bijective₀ _ (pow_ne_zero 2 hd0)
  rw [← hbij.sum_comp (fun y => complexCharacter δ ^ 2 * (φ y * P.ratioCorrelation c Θ y w))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hφ x _ hd0]
  ring

/-- The trace of a ratio pair sum to `Γ(3)`. -/
def ratioTrace (φ : P.Res → ℂ) (c : P.Res) (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ :=
  cosetTrace complexMatrix P.levelSqGroup kubotaSquare (P.ratioSum φ c Θ) w

section Trace

variable (φ : P.Res → ℂ) (hφ : P.SquareInvariant φ) (c : P.Res) (Θ : HyperbolicSpace → ℂ)
  (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
include hφ hΘ

theorem ratioTrace_automorphy (M : levelThree) (w : HyperbolicSpace) :
    P.ratioTrace φ c Θ (complexMatrix M • w) = complexCharacter M ^ 2 * P.ratioTrace φ c Θ w :=
  cosetTrace_smul (ρ := complexMatrix) (H := P.levelSqGroup) (χ := kubotaSquare)
    (F := P.ratioSum φ c Θ) (fun δ hδ x => by
      rw [kubotaSquare_apply]
      exact P.ratioSum_automorphy φ hφ c Θ hΘ δ hδ x) M w

theorem ratioTrace_conj (g : SL(2, O)) (hA : ∀ γ : levelThree, conjLevel g γ ∈ P.levelSqGroup ↔ γ ∈ P.levelSqGroup)
    (hκ : ∀ γ : levelThree, complexCharacter (conjLevel g γ) = complexCharacter γ)
    (hF : ∀ w, P.ratioSum φ c Θ (integralComplexMatrix g • w) = P.ratioSum φ c Θ w) (w : HyperbolicSpace) :
    P.ratioTrace φ c Θ (integralComplexMatrix g • w) = P.ratioTrace φ c Θ w := by
  have hFΘ : ∀ δ ∈ P.levelSqGroup, ∀ x, P.ratioSum φ c Θ (complexMatrix δ • x) = kubotaSquare δ * P.ratioSum φ c Θ x :=
    fun δ hδ x => by
      rw [kubotaSquare_apply]
      exact P.ratioSum_automorphy φ hφ c Θ hΘ δ hδ x
  unfold ratioTrace cosetTrace
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

theorem ratioTrace_eq_sum (w : HyperbolicSpace) :
    P.ratioTrace φ c Θ w = ∑ i : P.FracIndex, P.ratioSum φ c Θ (complexMatrix (P.fracRep i) • w) := by
  have hF : ∀ δ ∈ P.levelSqGroup, ∀ x, P.ratioSum φ c Θ (complexMatrix δ • x) = kubotaSquare δ * P.ratioSum φ c Θ x :=
    fun δ hδ x => by
      rw [kubotaSquare_apply]
      exact P.ratioSum_automorphy φ hφ c Θ hΘ δ hδ x
  unfold ratioTrace cosetTrace
  rw [← P.fracCoset_bijective.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cosetTerm_congr hF w (γ := (P.fracCoset i).out) (γ' := (P.fracRep i)⁻¹) (QuotientGroup.out_eq' _)]
  unfold cosetTerm
  rw [inv_inv, kubotaSquare_apply, map_inv, P.complexCharacter_fracRep, inv_one, one_pow, one_mul]

variable (hΘr : ∀ (r : SL(2, ℤ)) (w : HyperbolicSpace), Θ (integralComplexMatrix (rationalEmbedding r) • w) = Θ w)
include hΘr

omit hφ in
theorem ratioSum_S {k m : O} (hkm : P.p ^ 4 * m + 9 * k ^ 2 = 1) (w : HyperbolicSpace) :
    P.ratioSum φ c Θ (integralComplexMatrix sO • w) = P.ratioSum φ c Θ (complexMatrix (P.gammaS hkm) • w) := by
  unfold ratioSum ratioCorrelation
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [P.theta_fracShift_S Θ hΘ hΘr hkm, P.theta_fracShift_S Θ hΘ hΘr hkm]
  linear_combination (φ x * (Θ (P.fracShift (P.lift x) • complexMatrix (P.gammaS hkm) • w) *
    Θ (P.fracShift (P.lift (c * x)) • complexMatrix (P.gammaS hkm) • w))) * P.deltaS_character_sq hkm

/-- **The trace of a ratio pair sum is invariant under `SL₂(ℤ)`.** -/
theorem ratioTrace_rational (r : SL(2, ℤ)) (w : HyperbolicSpace) :
    P.ratioTrace φ c Θ (integralComplexMatrix (rationalEmbedding r) • w) = P.ratioTrace φ c Θ w := by
  have hT : ∀ y, P.ratioTrace φ c Θ (integralComplexMatrix (tPowO 1) • y) = P.ratioTrace φ c Θ y := fun y =>
    P.ratioTrace_conj φ hφ c Θ hΘ (tPowO 1) P.conjLevel_mem_iff_T (complexCharacter_conjLevel_rational _)
      (fun x => by
        unfold ratioSum ratioCorrelation
        exact Finset.sum_congr rfl fun t _ => by
          rw [P.theta_fracShift_T Θ hΘr, P.theta_fracShift_T Θ hΘr]) y
  have hS : ∀ y, P.ratioTrace φ c Θ (integralComplexMatrix sO • y) = P.ratioTrace φ c Θ y := by
    intro y
    obtain ⟨k, m, hkm, hk⟩ := P.exists_sData
    have hg : P.gS hkm = sO * ((P.gammaS hkm : levelThree) : SL(2, O))⁻¹ := by
      rw [← P.gS_mul_gammaS hkm]
      group
    have hgS : ∀ x, P.ratioSum φ c Θ (integralComplexMatrix (P.gS hkm) • x) = P.ratioSum φ c Θ x := by
      intro x
      rw [hg, map_mul, mul_smul, P.ratioSum_S φ c Θ hΘ hΘr hkm, complexMatrix_eq, ← mul_smul, ← map_mul,
        mul_inv_cancel, map_one, one_smul]
    have hw : integralComplexMatrix sO • y =
        integralComplexMatrix (P.gS hkm) • (complexMatrix (P.gammaS hkm) • y) := by
      rw [← P.gS_mul_gammaS hkm, map_mul, mul_smul]
      rfl
    rw [hw, P.ratioTrace_conj φ hφ c Θ hΘ (P.gS hkm) (P.conjLevel_mem_iff_gS hkm)
      (P.complexCharacter_conjLevel_gS hkm hk) hgS, P.ratioTrace_automorphy φ hφ c Θ hΘ,
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

/-- **The ratio trace over the projective line modulo `q²`.** -/
theorem ratioTrace_eq (w : HyperbolicSpace) :
    P.ratioTrace φ c Θ w = P.ratioSum φ c Θ w +
      (∑ x : {x : P.Res // x ≠ 0}, P.ratioSum φ c Θ (complexMatrix (lowerThree (P.p * P.lift x.1)) • w) +
        ∑ s : P.Res × P.Res, P.ratioSum φ c Θ (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • w)) := by
  rw [P.ratioTrace_eq_sum φ hφ c Θ hΘ, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_unique]
  have h1 : P.ratioSum φ c Θ (complexMatrix (P.fracRep (Sum.inl default)) • w) = P.ratioSum φ c Θ w := by
    rw [show P.fracRep (Sum.inl default) = 1 from rfl, map_one, one_smul]
  have h2 : ∀ x : {x : P.Res // x ≠ 0}, P.ratioSum φ c Θ (complexMatrix (P.fracRep (Sum.inr (Sum.inl x))) • w) =
      P.ratioSum φ c Θ (complexMatrix (lowerThree (P.p * P.lift x.1)) • w) := fun x => by
    rw [show P.fracRep (Sum.inr (Sum.inl x)) = lowerThree (P.p * P.lift x.1) from rfl]
  have h3 : ∀ s : P.Res × P.Res, P.ratioSum φ c Θ (complexMatrix (P.fracRep (Sum.inr (Sum.inr s))) • w) =
      P.ratioSum φ c Θ (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • w) := fun s => by
    rw [show P.fracRep (Sum.inr (Sum.inr s)) = P.gamma0 * transThree (P.sqLift s) from rfl, map_mul, mul_smul,
      P.ratioSum_S φ c Θ hΘ hΘr P.sKM]
  rw [h1, Finset.sum_congr rfl (fun x _ => h2 x), Finset.sum_congr rfl (fun s _ => h3 s)]

omit hφ in
/-- **The ratio sum at `S`**: low points of low points with the phases `χ(−3x)χ(−3cx)`. -/
theorem ratioSum_sO (hc : c ≠ 0) (y : HyperbolicSpace) :
    P.ratioSum φ c Θ (integralComplexMatrix sO • y) = φ 0 * Θ y ^ 2 +
      ∑ x : {x : P.Res // x ≠ 0}, φ x.1 * (P.chi (-3 * x.1) * P.chi (-3 * (c * x.1)) *
        (P.heckeLow Θ (-P.lowBeta (-P.lift x.1)) (P.contraction • y) *
          P.heckeLow Θ (-P.lowBeta (-P.lift (c * x.1))) (P.contraction • y))) := by
  have hS : ∀ x, Θ (integralComplexMatrix sO • x) = Θ x := hΘr ModularGroup.S
  have h0 : ∀ z, Θ (P.fracShift (P.lift 0) • z) = Θ z := fun z => by
    rw [show P.lift 0 = P.lift (P.res 0) by rw [map_zero], P.theta_fracShift_res Θ hΘ, P.fracShift_zero, one_smul]
  unfold ratioSum
  rw [Fintype.sum_eq_add_sum_compl (0 : P.Res),
    Finset.sum_subtype _ (fun x => by simp : ∀ x, x ∈ ({0}ᶜ : Finset P.Res) ↔ x ≠ 0)]
  congr 1
  · rw [ratioCorrelation, mul_zero, h0, hS, pow_two]
  · refine Finset.sum_congr rfl fun x _ => ?_
    have hx : ¬ P.p ∣ P.lift x.1 := fun h => x.2 (P.res_lift_eq_zero h)
    have hcx : ¬ P.p ∣ P.lift (c * x.1) := fun h => mul_ne_zero hc x.2 (P.res_lift_eq_zero h)
    have e1 : P.res (3 * -P.lift x.1) = -3 * x.1 := by rw [map_mul, map_neg, res_lift, map_ofNat]; ring
    have e2 : P.res (3 * -P.lift (c * x.1)) = -3 * (c * x.1) := by
      rw [map_mul, map_neg, res_lift, map_ofNat]; ring
    rw [ratioCorrelation, P.theta_fracShift_sO Θ hΘ hΘr _ hx, P.theta_fracShift_sO Θ hΘ hΘr _ hcx,
      ← P.chi_res, ← P.chi_res, e1, e2]
    ring

end Trace

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
