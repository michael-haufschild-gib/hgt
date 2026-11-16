import GaloisForLFunctions.OrderSixMetaplecticTheory.TheFractionalTraceIsInvariantUnderTheModularGroup

/-!
# The fractional trace is a sum over the projective line modulo `q²`

The right cosets of `Γ(3) ∩ Γ₀(q²)` in `Γ(3)` are the bottom rows in `P¹(O/q²)`: `g g'⁻¹ ∈ Γ₀(q²)` iff
`q² ∣ cd' − dc'` (`mul_inv_mem_levelSqGroup_iff`). Representatives (`PrimaryPrime.fracRep`):

* `1` (row `(0, 1)`);
* `L_{qx} = [[1, 0], [3qx, 1]]`, `x ∈ (O/q)^×` (rows `(3qx, 1)`);
* `γ₀T(3s)`, `s = x₀ + qx₁ ∈ O/q²` (rows `(3k, 9ks + q²m) ≡ 3k(1, 3s)`), with `γ₀ ≡ S mod q²` from the
  `S`-symmetry of the trace.

All representatives have `κ = 1`, and `G_Θ ∘ γ₀ = G_Θ ∘ S`, so (`fracTrace_eq`)

`Tr G_Θ(w) = G_Θ(w) + Σ_{x ≠ 0} G_Θ(L_{qx}w) + Σ_{s ∈ O/q²} G_Θ(S T(3s)w)`.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- A fixed choice of `k, m` with `q⁴m + 9k² = 1`, `q² ∣ 3k − 1`. -/
def sK : O := P.exists_sData.choose

/-- See `sK`. -/
def sM : O := P.exists_sData.choose_spec.choose

theorem sKM : P.p ^ 4 * P.sM + 9 * P.sK ^ 2 = 1 := P.exists_sData.choose_spec.choose_spec.1

theorem sK_dvd : P.p ^ 2 ∣ 3 * P.sK - 1 := P.exists_sData.choose_spec.choose_spec.2

/-- `γ₀` for the fixed data. -/
abbrev gamma0 : levelThree := P.gammaS P.sKM

/-- The residue `x₀ + qx₁` of `O/q²`. -/
def sqLift (s : P.Res × P.Res) : O := P.lift s.1 + P.p * P.lift s.2

theorem sqLift_inj (s s' : P.Res × P.Res) (h : P.p ^ 2 ∣ P.sqLift s - P.sqLift s') : s = s' := by
  have hp : P.p ∣ P.lift s.1 - P.lift s'.1 := by
    have h1 : P.p ∣ P.sqLift s - P.sqLift s' := (dvd_pow_self _ two_ne_zero).trans h
    have h2 : P.p ∣ P.p * (P.lift s.2 - P.lift s'.2) := dvd_mul_right _ _
    have := dvd_sub h1 h2
    unfold sqLift at this
    convert this using 1
    ring
  have h1 : s.1 = s'.1 := by
    have := (P.res_eq_zero_iff _).mpr hp
    rwa [map_sub, res_lift, res_lift, sub_eq_zero] at this
  have h2 : P.p ∣ P.lift s.2 - P.lift s'.2 := by
    unfold sqLift at h
    rw [h1, show P.lift s'.1 + P.p * P.lift s.2 - (P.lift s'.1 + P.p * P.lift s'.2) =
      P.p * (P.lift s.2 - P.lift s'.2) by ring, pow_two] at h
    exact (mul_dvd_mul_iff_left P.ne_zero).mp h
  have h2' : s.2 = s'.2 := by
    have := (P.res_eq_zero_iff _).mpr h2
    rwa [map_sub, res_lift, res_lift, sub_eq_zero] at this
  exact Prod.ext h1 h2'

/-- Every class of `O/q²` is some `x₀ + qx₁`. -/
theorem exists_sqLift (r : O) : ∃ s : P.Res × P.Res, P.p ^ 2 ∣ P.sqLift s - r := by
  have h0 : P.res (P.lift (P.res r) - r) = 0 := by rw [map_sub, res_lift, sub_self]
  obtain ⟨a, ha⟩ := (P.res_eq_zero_iff _).mp h0
  have h1 : P.res (P.lift (P.res (-a)) - (-a)) = 0 := by rw [map_sub, res_lift, sub_self]
  obtain ⟨b, hb⟩ := (P.res_eq_zero_iff _).mp h1
  refine ⟨(P.res r, P.res (-a)), b, ?_⟩
  unfold sqLift
  simp only
  linear_combination ha + P.p * hb

/-- Index of the cosets: `∞`, the `N − 1` cusps `3qx`, the `N²` classes over the cusp `0`. -/
abbrev FracIndex := Unit ⊕ {x : P.Res // x ≠ 0} ⊕ (P.Res × P.Res)

/-- The representatives `1`, `L_{qx}`, `γ₀T(3s)`. -/
def fracRep : P.FracIndex → levelThree
  | .inl _ => 1
  | .inr (.inl x) => lowerThree (P.p * P.lift x.1)
  | .inr (.inr s) => P.gamma0 * transThree (P.sqLift s)

/-- `g g'⁻¹ ∈ Γ₀(q²)` iff `q² ∣ cd' − dc'`. -/
theorem mul_inv_mem_levelSqGroup_iff (M N : levelThree) :
    M * N⁻¹ ∈ P.levelSqGroup ↔
      P.p ^ 2 ∣ (M : SL(2, O)) 1 0 * (N : SL(2, O)) 1 1 - (M : SL(2, O)) 1 1 * (N : SL(2, O)) 1 0 := by
  have e : ((M * N⁻¹ : levelThree) : SL(2, O)) 1 0 = (M : SL(2, O)) 1 0 * (N : SL(2, O)) 1 1 -
      (M : SL(2, O)) 1 1 * (N : SL(2, O)) 1 0 := by
    simp [Matrix.SpecialLinearGroup.SL2_inv_expl, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [mem_levelSqGroup, e]

/-- The bottom rows of the representatives. -/
def fracRow : P.FracIndex → O × O
  | .inl _ => (0, 1)
  | .inr (.inl x) => (3 * (P.p * P.lift x.1), 1)
  | .inr (.inr s) => (3 * P.sK, 9 * P.sK * P.sqLift s + P.p ^ 2 * P.sM)

theorem fracRep_row (i : P.FracIndex) :
    (((P.fracRep i : levelThree) : SL(2, O)) 1 0, ((P.fracRep i : levelThree) : SL(2, O)) 1 1) = P.fracRow i := by
  rcases i with _ | x | s
  · simp [fracRep, fracRow]
  · simp [fracRep, fracRow, lowerThree]
  · simp [fracRep, fracRow, gamma0, gammaS, transThree, Matrix.mul_apply, Fin.sum_univ_two]
    ring

theorem not_dvd_sK : ¬ P.p ∣ 3 * P.sK := by
  intro h
  have h1 : P.p ∣ 1 := by
    have := dvd_sub h ((dvd_pow_self _ two_ne_zero).trans P.sK_dvd)
    simpa using this
  exact P.prime.not_unit (isUnit_of_dvd_one h1)

theorem isCoprime_sK : IsCoprime (3 * P.sK) P.p :=
  ((Irreducible.coprime_iff_not_dvd P.prime.irreducible).mpr P.not_dvd_sK).symm

end PrimaryPrime

namespace PrimaryPrime

variable (P : PrimaryPrime)

theorem dvd_of_sq_dvd_three_p (Y : O) (h : P.p ^ 2 ∣ 3 * (P.p * Y)) : P.p ∣ Y := by
  rw [pow_two, show 3 * (P.p * Y) = P.p * (3 * Y) by ring] at h
  exact P.isCoprime_three.symm.dvd_of_dvd_mul_left ((mul_dvd_mul_iff_left P.ne_zero).mp h)

theorem not_dvd_sK_add (Z : O) : ¬ P.p ∣ 3 * P.sK + P.p * Z := fun h =>
  P.not_dvd_sK ((dvd_add_left (dvd_mul_right _ _)).mp h)

theorem res_lift_eq_zero {x : P.Res} (h : P.p ∣ P.lift x) : x = 0 := by
  have := (P.res_eq_zero_iff _).mpr h
  rwa [res_lift] at this

/-- Distinct representatives have non-proportional rows modulo `q²`. -/
theorem fracRow_injective (i j : P.FracIndex)
    (h : P.p ^ 2 ∣ (P.fracRow i).1 * (P.fracRow j).2 - (P.fracRow i).2 * (P.fracRow j).1) : i = j := by
  have hp : ∀ {X : O}, P.p ^ 2 ∣ X → P.p ∣ X := fun hX => (dvd_pow_self _ two_ne_zero).trans hX
  rcases i with _ | x | s <;> rcases j with _ | y | s' <;> simp only [fracRow] at h
  · rfl
  · exact absurd (P.res_lift_eq_zero (P.dvd_of_sq_dvd_three_p _ (by simpa using h))) y.2
  · exact absurd (hp (by simpa using h)) P.not_dvd_sK
  · exact absurd (P.res_lift_eq_zero (P.dvd_of_sq_dvd_three_p _ (by simpa using h))) x.2
  · have h' : P.p ^ 2 ∣ 3 * (P.p * (P.lift x.1 - P.lift y.1)) := by convert h using 1; ring
    have := (P.res_eq_zero_iff _).mpr (P.dvd_of_sq_dvd_three_p _ h')
    rw [map_sub, res_lift, res_lift, sub_eq_zero] at this
    exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext this)
  · exact absurd (hp (show P.p ^ 2 ∣ -(3 * P.sK + P.p * (-(3 * (P.lift x.1 * (9 * P.sK * P.sqLift s' +
      P.p ^ 2 * P.sM))))) by convert h using 1; ring)) (fun h' => P.not_dvd_sK_add _ ((dvd_neg).mp h'))
  · exact absurd (hp (by simpa using h)) P.not_dvd_sK
  · exact absurd (hp (show P.p ^ 2 ∣ 3 * P.sK + P.p * (-(3 * (P.lift y.1 * (9 * P.sK * P.sqLift s +
      P.p ^ 2 * P.sM)))) by convert h using 1; ring)) (P.not_dvd_sK_add _)
  · have hc : IsCoprime ((3 * P.sK) ^ 2 * 3) (P.p ^ 2) :=
      ((P.isCoprime_sK.pow_left).mul_left P.isCoprime_three).pow_right
    have h' : P.p ^ 2 ∣ (3 * P.sK) ^ 2 * 3 * (P.sqLift s' - P.sqLift s) := by convert h using 1; ring
    exact congrArg (Sum.inr ∘ Sum.inr) (P.sqLift_inj s s' (by
      simpa using (hc.symm.dvd_of_dvd_mul_left h').neg_right)).symm |>.symm

/-- Every bottom row is proportional modulo `q²` to a representative's. -/
theorem exists_fracRow (a b c d : O) (hdet : a * d - b * c = 1) :
    ∃ i : P.FracIndex, P.p ^ 2 ∣ (P.fracRow i).1 * d - (P.fracRow i).2 * c := by
  by_cases hc1 : P.p ∣ c
  · by_cases hc2 : P.p ^ 2 ∣ c
    · exact ⟨.inl (), by simpa [fracRow] using hc2⟩
    · obtain ⟨c', rfl⟩ := hc1
      have hc' : P.res c' ≠ 0 := by
        rw [Ne, res_eq_zero_iff]
        rintro ⟨e, rfl⟩
        exact hc2 ⟨e, by ring⟩
      have hd : P.res d ≠ 0 := by
        intro h0
        have h := congrArg P.res hdet
        rw [map_sub, map_mul, map_mul, h0, map_mul, P.res_p] at h
        simp at h
      have h3 := P.three_ne_zero'
      refine ⟨.inr (.inl ⟨P.res c' / (3 * P.res d), div_ne_zero hc' (mul_ne_zero h3 hd)⟩), ?_⟩
      simp only [fracRow]
      have hr : P.res (3 * P.lift (P.res c' / (3 * P.res d)) * d - c') = 0 := by
        rw [map_sub, map_mul, map_mul, res_lift, map_ofNat]
        field_simp
        ring
      obtain ⟨e, he⟩ := (P.res_eq_zero_iff _).mp hr
      exact ⟨e, by linear_combination P.p * he⟩
  · have hco : IsCoprime (3 * c) (P.p ^ 2) :=
      (P.isCoprime_three.mul_left ((Irreducible.coprime_iff_not_dvd P.prime.irreducible).mpr hc1).symm).pow_right
    obtain ⟨e, f, hef⟩ := hco
    obtain ⟨s, t, hs⟩ := P.exists_sqLift (e * d)
    refine ⟨.inr (.inr s), ?_⟩
    simp only [fracRow]
    exact ⟨3 * P.sK * (d * f - 3 * c * t) - P.sM * c, by linear_combination (-3 * P.sK * d) * hef - (9 * P.sK * c) * hs⟩

/-- The coset `g_i⁻¹(Γ(3) ∩ Γ₀(q²))`. -/
def fracCoset (i : P.FracIndex) : levelThree ⧸ P.levelSqGroup := ((P.fracRep i)⁻¹ : levelThree)

theorem fracCoset_bijective : Function.Bijective P.fracCoset := by
  constructor
  · intro i j h
    have h' := QuotientGroup.eq.mp h
    rw [inv_inv, P.mul_inv_mem_levelSqGroup_iff] at h'
    have ri := P.fracRep_row i
    have rj := P.fracRep_row j
    simp only [Prod.ext_iff] at ri rj
    rw [ri.1, ri.2, rj.1, rj.2] at h'
    exact P.fracRow_injective i j h'
  · intro q
    set γ : levelThree := q.out⁻¹
    have hdet : (γ : SL(2, O)) 0 0 * (γ : SL(2, O)) 1 1 - (γ : SL(2, O)) 0 1 * (γ : SL(2, O)) 1 0 = 1 := by
      rw [← Matrix.det_fin_two]
      exact (γ : SL(2, O)).det_coe
    obtain ⟨i, hi⟩ := P.exists_fracRow _ _ _ _ hdet
    refine ⟨i, ?_⟩
    rw [← QuotientGroup.out_eq' q, fracCoset, QuotientGroup.eq, inv_inv,
      show q.out = γ⁻¹ by simp [γ], P.mul_inv_mem_levelSqGroup_iff]
    have ri := P.fracRep_row i
    simp only [Prod.ext_iff] at ri
    rw [ri.1, ri.2]
    exact hi

theorem complexCharacter_fracRep (i : P.FracIndex) : complexCharacter (P.fracRep i) = 1 := by
  rcases i with _ | x | s
  · exact map_one _
  · exact complexCharacter_lowerThree _
  · rw [fracRep, map_mul, P.gammaS_character P.sKM P.sK_dvd, complexCharacter_transThree, one_mul]

/-- **The trace over the representatives** (all weights are `1`). -/
theorem fracTrace_eq_sum (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (w : HyperbolicSpace) :
    P.fracTrace Θ w = ∑ i : P.FracIndex, P.fracSum Θ (complexMatrix (P.fracRep i) • w) := by
  have hF : ∀ δ ∈ P.levelSqGroup, ∀ x, P.fracSum Θ (complexMatrix δ • x) = kubotaSquare δ * P.fracSum Θ x :=
    fun δ hδ x => by
      rw [kubotaSquare_apply]
      exact P.fracSum_automorphy Θ hΘ δ hδ x
  unfold fracTrace cosetTrace
  rw [← P.fracCoset_bijective.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cosetTerm_congr hF w (γ := (P.fracCoset i).out) (γ' := (P.fracRep i)⁻¹) (QuotientGroup.out_eq' _)]
  unfold cosetTerm
  rw [inv_inv, kubotaSquare_apply, map_inv, P.complexCharacter_fracRep, inv_one, one_pow, one_mul]

/-- **The fractional trace over the projective line modulo `q²`.** -/
theorem fracTrace_eq (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (hΘr : ∀ (r : SL(2, ℤ)) (w : HyperbolicSpace), Θ (integralComplexMatrix (rationalEmbedding r) • w) = Θ w)
    (w : HyperbolicSpace) :
    P.fracTrace Θ w = P.fracSum Θ w +
      (∑ x : {x : P.Res // x ≠ 0}, P.fracSum Θ (complexMatrix (lowerThree (P.p * P.lift x.1)) • w) +
        ∑ s : P.Res × P.Res, P.fracSum Θ (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • w)) := by
  rw [P.fracTrace_eq_sum Θ hΘ, Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  · simp [fracRep]
  · congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [fracRep, map_mul, mul_smul, P.fracSum_S Θ hΘ hΘr P.sKM]

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
