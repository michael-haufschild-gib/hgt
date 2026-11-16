import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckeCorrelationAtAPrimaryPrimeHasTheSquareMultiplier

/-!
# The Hecke trace at a primary prime is a sum over the projective line

`Γ_p = Γ(3) ∩ {p ∣ b, p ∣ c}` has finite index in `Γ(3)`, and the trace

`Tr_p F_Θ(w) = Σ_{γΓ_p ∈ Γ(3)/Γ_p} κ(γ)² F_Θ(γ⁻¹w)`   (`PrimaryPrime.heckeTrace`)

of the Hecke correlation `F_Θ(w) = Θ(A_pw)Θ(A_p⁻¹w)` has the multiplier `κ²` on `Γ(3)`.

The cosets are the ordered pairs of distinct points of `P¹(O/p)`: `γγ'⁻¹ ∈ Γ_p` iff the rows of `γ` and `γ'`
are proportional modulo `p` (`mul_inv_mem_heckeGroup_iff`). Representatives (`PrimaryPrime.rep`), with
`W = [[p, 3], [3k, δ]]`, `pδ − 9k = 1`:

* `U(x) = [[1, 3x], [0, 1]]`, rows `(1, 3x)`, `(0, 1)` modulo `p`;
* `W U(x)`, rows `(0, 3)`, `(3k, 9kx + δ)`;
* `L(y) U(x) = [[1, 3x], [3y, 9xy + 1]]`, `y ≢ 0`;

`N(p)(N(p) + 1)` in all (`cosetOf_bijective`), so (`heckeTrace_eq_sum`)

`Tr_p F_Θ(w) = Σ_i κ(δ_i)^{−2} F_Θ(δ_i w)`.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### The trace -/

theorem heckeGroup_finiteIndex : P.heckeGroup.FiniteIndex := by
  obtain ⟨hL, hR⟩ := integralDiagonal_finite_covers P.p P.ne_zero
  set K := (integralDiagonalLeft P.p).range ⊓ (integralDiagonalRight P.p).range
  haveI : (K.subgroupOf levelThree).FiniteIndex := inferInstance
  refine Subgroup.finiteIndex_of_le (H := K.subgroupOf levelThree) fun γ hγ => ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hγ
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hγ
  have ex := integralDiagonal_entries P.p x
  have ey := integralDiagonal_entries P.p y
  change x.1.1 = (γ : SL(2, O)) at hx
  change y.1.2 = (γ : SL(2, O)) at hy
  refine ⟨?_, ?_⟩
  · rw [← hy, ← ey.2.1]
    exact dvd_mul_right _ _
  · rw [← hx, ex.2.2.1]
    exact dvd_mul_left _ _

instance (P : PrimaryPrime) : P.heckeGroup.FiniteIndex := P.heckeGroup_finiteIndex

noncomputable instance (P : PrimaryPrime) : Fintype (levelThree ⧸ P.heckeGroup) :=
  Subgroup.fintypeQuotientOfFiniteIndex

/-- **The Hecke trace at `p`** `Tr_p F_Θ(w) = Σ_{γΓ_p} κ(γ)² F_Θ(γ⁻¹w)`. -/
def heckeTrace (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ :=
  cosetTrace complexMatrix P.heckeGroup kubotaSquare (P.heckeCorrelation Θ) w

/-- **The Hecke trace at `p` has the multiplier `κ²` on `Γ(3)`.** -/
theorem heckeTrace_automorphy (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (M : levelThree) (w : HyperbolicSpace) :
    P.heckeTrace Θ (complexMatrix M • w) = complexCharacter M ^ 2 * P.heckeTrace Θ w :=
  cosetTrace_smul (ρ := complexMatrix) (H := P.heckeGroup) (χ := kubotaSquare)
    (F := P.heckeCorrelation Θ) (fun δ hδ x => by
      rw [kubotaSquare_apply]
      exact P.heckeCorrelation_automorphy Θ hΘ δ hδ x) M w

/-! ### The residue field -/

instance isMaximal (P : PrimaryPrime) : (Ideal.span {P.p}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible P.prime.irreducible

/-- The residue field `O/p`. -/
abbrev Res := O ⧸ Ideal.span {P.p}

noncomputable instance (P : PrimaryPrime) : Field P.Res := Ideal.Quotient.field _

noncomputable instance (P : PrimaryPrime) : Fintype P.Res := Fintype.ofFinite _

/-- Reduction modulo `p`. -/
abbrev res (x : O) : P.Res := Ideal.Quotient.mk _ x

theorem res_eq_zero_iff (x : O) : P.res x = 0 ↔ P.p ∣ x := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- A lift of a residue. -/
def lift (r : P.Res) : O := (Ideal.Quotient.mk_surjective r).choose

@[simp] theorem res_lift (r : P.Res) : P.res (P.lift r) = r := (Ideal.Quotient.mk_surjective r).choose_spec

theorem res_p : P.res P.p = 0 := (P.res_eq_zero_iff _).mpr (dvd_refl _)

theorem three_ne_zero' : (3 : P.Res) ≠ 0 := by
  have h : P.res 3 ≠ 0 := by
    rw [Ne, res_eq_zero_iff]
    intro h
    exact P.prime.not_unit (P.isCoprime_three.symm.isUnit_of_dvd' (dvd_refl _) h)
  simpa using h

/-! ### Representatives -/

theorem exists_bezout : ∃ δ k : O, P.p * δ - 9 * k = 1 := by
  obtain ⟨u, v, h⟩ := P.isCoprime_three.pow_left (m := 2)
  exact ⟨v, -u, by linear_combination h⟩

/-- `δ` in `pδ − 9k = 1`. -/
def wDelta : O := P.exists_bezout.choose

/-- `k` in `pδ − 9k = 1`. -/
def wK : O := P.exists_bezout.choose_spec.choose

theorem w_det : P.p * P.wDelta - 9 * P.wK = 1 := P.exists_bezout.choose_spec.choose_spec

/-- `W = [[p, 3], [3k, δ]]`. -/
def wMat : levelThree :=
  ⟨⟨!![P.p, 3; 3 * P.wK, P.wDelta], by rw [Matrix.det_fin_two_of]; linear_combination P.w_det⟩,
    levelThree_of_entries _ (by
      obtain ⟨t, ht⟩ := P.three_dvd_sub_one
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using P.three_dvd_sub_one
      · simp
      · simp
      · exact ⟨3 * P.wK - P.wDelta * t, by simp; linear_combination P.w_det - P.wDelta * ht⟩)⟩

theorem res_wK_ne_zero : P.res P.wK ≠ 0 := by
  intro h
  have hd := congrArg P.res P.w_det
  rw [map_sub, map_mul, map_mul, h, P.res_p, map_one] at hd
  simp at hd

/-- Index of the cosets: `(∞-type) x`, `(W-type) x`, `(x, y)` with `y ≠ 0`. -/
abbrev Index := P.Res ⊕ P.Res ⊕ (P.Res × {y : P.Res // y ≠ 0})

/-- The representatives `U(x)`, `W U(x)`, `L(y) U(x)`. -/
def rep : P.Index → levelThree
  | .inl x => transThree (P.lift x)
  | .inr (.inl x) => P.wMat * transThree (P.lift x)
  | .inr (.inr (x, y)) => lowerThree (P.lift y.1) * transThree (P.lift x)

/-- The rows of the representatives modulo `p`. -/
def repRes : P.Index → P.Res × P.Res × P.Res × P.Res
  | .inl x => (1, 3 * x, 0, 1)
  | .inr (.inl x) => (0, 3, 3 * P.res P.wK, 9 * P.res P.wK * x + P.res P.wDelta)
  | .inr (.inr (x, y)) => (1, 3 * x, 3 * y.1, 9 * x * y.1 + 1)

theorem res_rep (i : P.Index) :
    (P.res ((P.rep i : SL(2, O)) 0 0), P.res ((P.rep i : SL(2, O)) 0 1),
      P.res ((P.rep i : SL(2, O)) 1 0), P.res ((P.rep i : SL(2, O)) 1 1)) = P.repRes i := by
  rcases i with x | x | ⟨x, y⟩
  · simp [rep, repRes, transThree]
  · simp [rep, repRes, wMat, transThree, Matrix.mul_apply, Fin.sum_univ_two, P.res_p]
    ring
  · simp [rep, repRes, lowerThree, transThree, Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- `γγ'⁻¹ ∈ Γ_p` iff the rows of `γ` and `γ'` are proportional modulo `p`. -/
theorem mul_inv_mem_heckeGroup_iff (M N : levelThree) :
    M * N⁻¹ ∈ P.heckeGroup ↔
      P.res ((M : SL(2, O)) 0 0) * P.res ((N : SL(2, O)) 0 1) -
          P.res ((M : SL(2, O)) 0 1) * P.res ((N : SL(2, O)) 0 0) = 0 ∧
        P.res ((M : SL(2, O)) 1 0) * P.res ((N : SL(2, O)) 1 1) -
          P.res ((M : SL(2, O)) 1 1) * P.res ((N : SL(2, O)) 1 0) = 0 := by
  have e1 : ((M * N⁻¹ : levelThree) : SL(2, O)) 0 1 = -((M : SL(2, O)) 0 0 * (N : SL(2, O)) 0 1 -
      (M : SL(2, O)) 0 1 * (N : SL(2, O)) 0 0) := by
    simp [Matrix.SpecialLinearGroup.SL2_inv_expl, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have e2 : ((M * N⁻¹ : levelThree) : SL(2, O)) 1 0 = (M : SL(2, O)) 1 0 * (N : SL(2, O)) 1 1 -
      (M : SL(2, O)) 1 1 * (N : SL(2, O)) 1 0 := by
    simp [Matrix.SpecialLinearGroup.SL2_inv_expl, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  change P.p ∣ ((M * N⁻¹ : levelThree) : SL(2, O)) 0 1 ∧ P.p ∣ ((M * N⁻¹ : levelThree) : SL(2, O)) 1 0 ↔ _
  rw [e1, e2, dvd_neg, ← P.res_eq_zero_iff, ← P.res_eq_zero_iff]
  simp only [map_sub, map_mul]

/-- Distinct representatives have non-proportional rows. -/
theorem repRes_injective (i j : P.Index)
    (h1 : (P.repRes i).1 * (P.repRes j).2.1 - (P.repRes i).2.1 * (P.repRes j).1 = 0)
    (h2 : (P.repRes i).2.2.1 * (P.repRes j).2.2.2 - (P.repRes i).2.2.2 * (P.repRes j).2.2.1 = 0) : i = j := by
  have h3 := P.three_ne_zero'
  have hk := P.res_wK_ne_zero
  rcases i with x | x | ⟨x, y⟩ <;> rcases j with x' | x' | ⟨x', y'⟩ <;>
    simp only [repRes] at h1 h2
  · congr 1
    have : 3 * (x' - x) = 0 := by linear_combination h1
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h3)).symm
  · exact absurd (by linear_combination h1) h3
  · exact absurd (by linear_combination -h2) (mul_ne_zero h3 y'.2)
  · exact absurd (by linear_combination -h1) h3
  · congr 2
    have : (3 * P.res P.wK) ^ 2 * 3 * (x' - x) = 0 := by linear_combination h2
    have hne : (3 * P.res P.wK) ^ 2 * 3 ≠ 0 := mul_ne_zero (pow_ne_zero _ (mul_ne_zero h3 hk)) h3
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hne)).symm
  · exact absurd (by linear_combination -h1) h3
  · exact absurd (by linear_combination h2) (mul_ne_zero h3 y.2)
  · exact absurd (by linear_combination h1) h3
  · have hx : x = x' := by
      have : 3 * (x' - x) = 0 := by linear_combination h1
      exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h3)).symm
    subst hx
    have : 3 * (y.1 - y'.1) = 0 := by linear_combination h2
    have hy := sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h3)
    congr 3
    exact Subtype.ext hy

/-- Every row pair with `ad − bc = 1` modulo `p` is proportional to a representative. -/
theorem exists_repRes (a b c d : P.Res) (hdet : a * d - b * c = 1) :
    ∃ i : P.Index, a * (P.repRes i).2.1 - b * (P.repRes i).1 = 0 ∧
      c * (P.repRes i).2.2.2 - d * (P.repRes i).2.2.1 = 0 := by
  have h3 := P.three_ne_zero'
  have hk := P.res_wK_ne_zero
  by_cases ha : a = 0
  · have hc : c ≠ 0 := by
      rintro rfl
      rw [ha] at hdet
      simp at hdet
    refine ⟨.inr (.inl ((3 * P.res P.wK * d - P.res P.wDelta * c) / (9 * P.res P.wK * c))), ?_, ?_⟩
    · simp only [repRes, ha]
      ring
    · simp only [repRes]
      field_simp
      ring
  · by_cases hc : c = 0
    · refine ⟨.inl (b / (3 * a)), ?_, ?_⟩
      · simp only [repRes]
        field_simp
        ring
      · simp only [repRes, hc]
        ring
    · refine ⟨.inr (.inr (b / (3 * a), ⟨a * c / 3, div_ne_zero (mul_ne_zero ha hc) h3⟩)), ?_, ?_⟩
      · simp only [repRes]
        field_simp
        ring
      · simp only [repRes]
        field_simp
        linear_combination (3 * c) * hdet

/-- The coset `δ_i⁻¹Γ_p`. -/
def cosetOf (i : P.Index) : levelThree ⧸ P.heckeGroup := ((P.rep i)⁻¹ : levelThree)

theorem cosetOf_bijective : Function.Bijective P.cosetOf := by
  constructor
  · intro i j h
    have h' := QuotientGroup.eq.mp h
    rw [inv_inv, P.mul_inv_mem_heckeGroup_iff] at h'
    have ri := P.res_rep i
    have rj := P.res_rep j
    simp only [Prod.ext_iff] at ri rj
    obtain ⟨ri1, ri2, ri3, ri4⟩ := ri
    obtain ⟨rj1, rj2, rj3, rj4⟩ := rj
    rw [ri1, ri2, ri3, ri4, rj1, rj2, rj3, rj4] at h'
    exact P.repRes_injective i j h'.1 h'.2
  · intro q
    set γ : levelThree := q.out⁻¹
    have hdet : (γ : SL(2, O)) 0 0 * (γ : SL(2, O)) 1 1 - (γ : SL(2, O)) 0 1 * (γ : SL(2, O)) 1 0 = 1 := by
      rw [← Matrix.det_fin_two]
      exact (γ : SL(2, O)).det_coe
    have hdet' := congrArg P.res hdet
    simp only [map_sub, map_mul, map_one] at hdet'
    obtain ⟨i, hi1, hi2⟩ := P.exists_repRes _ _ _ _ hdet'
    refine ⟨i, ?_⟩
    rw [← QuotientGroup.out_eq' q, cosetOf, QuotientGroup.eq, inv_inv,
      show q.out = γ⁻¹ by simp [γ], P.mul_inv_mem_heckeGroup_iff]
    have ri := P.res_rep i
    simp only [Prod.ext_iff] at ri
    obtain ⟨ri1, ri2, ri3, ri4⟩ := ri
    rw [ri1, ri2, ri3, ri4]
    constructor
    · linear_combination -hi1
    · linear_combination -hi2

/-- **The Hecke trace at `p` over the representatives.** -/
theorem heckeTrace_eq_sum (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (w : HyperbolicSpace) :
    P.heckeTrace Θ w = ∑ i : P.Index,
      (complexCharacter (P.rep i) ^ 2)⁻¹ * P.heckeCorrelation Θ (complexMatrix (P.rep i) • w) := by
  have hF : ∀ δ ∈ P.heckeGroup, ∀ x, P.heckeCorrelation Θ (complexMatrix δ • x) =
      kubotaSquare δ * P.heckeCorrelation Θ x := fun δ hδ x => by
    rw [kubotaSquare_apply]
    exact P.heckeCorrelation_automorphy Θ hΘ δ hδ x
  unfold heckeTrace cosetTrace
  rw [← P.cosetOf_bijective.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cosetTerm_congr hF w (γ := (P.cosetOf i).out) (γ' := (P.rep i)⁻¹) (QuotientGroup.out_eq' _)]
  unfold cosetTerm
  rw [inv_inv, kubotaSquare_apply, map_inv, inv_pow]

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
