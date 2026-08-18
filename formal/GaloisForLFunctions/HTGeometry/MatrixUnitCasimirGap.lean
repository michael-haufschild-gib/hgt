import GaloisForLFunctions.HTGeometry.MatrixUnitWeightSystem

/-!
# The spectral gap of a weighted matrix-unit Casimir

Every weight component of an eigenvector is again an eigenvector, because the Casimir preserves
weights.  Among the weights realized in one eigenspace, one maximizes a strictly antitone ranking
functional; a vector of that weight is annihilated by every raising generator, so the bracket
relations evaluate its Casimir energy as the weight's own Casimir value and identify the ordered
weight differences as the energies of the lowering generators.  The weight is therefore decreasing
with zero sum, and the combinatorial weight gap gives the spectral gap.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Gap

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]

/-- A strictly antitone integer ranking of the alphabet. -/
def alphaRank (a : α) : ℤ := -((Finset.univ.filter fun b => b < a).card : ℤ)

theorem alphaRank_lt {a b : α} (h : a < b) : alphaRank b < alphaRank a := by
  classical
  have hsubset : (Finset.univ.filter fun c => c < a) ⊆ (Finset.univ.filter fun c => c < b) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact lt_trans hc h
  have hss : (Finset.univ.filter fun c => c < a) ⊂ (Finset.univ.filter fun c => c < b) :=
    (Finset.ssubset_iff_of_subset hsubset).mpr ⟨a, by simp [h], by simp⟩
  have hcard := Finset.card_lt_card hss
  simp only [alphaRank]
  omega

/-- The ranking functional on weights. -/
def weightRank (nu : α → ℤ) : ℤ := ∑ a, alphaRank a * nu a

theorem weightRank_shiftWeight (a b : α) (nu : α → ℤ) :
    weightRank (shiftWeight a b nu) = weightRank nu + alphaRank a - alphaRank b := by
  classical
  rw [weightRank, weightRank]
  have hterm : ∀ c : α, alphaRank c * (shiftWeight a b nu) c
      = alphaRank c * nu c + (if c = a then alphaRank c else 0)
        - (if c = b then alphaRank c else 0) := by
    intro c
    have hexp : (shiftWeight a b nu) c
        = nu c + (if c = a then (1 : ℤ) else 0) - (if c = b then 1 else 0) := rfl
    rw [hexp]
    by_cases h1 : c = a
    · by_cases h2 : c = b
      · simp only [if_pos h1, if_pos h2]
        ring
      · simp only [if_pos h1, if_neg h2]
        ring
    · by_cases h2 : c = b
      · simp only [if_neg h1, if_pos h2]
        ring
      · simp only [if_neg h1, if_neg h2]
        ring
  rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ a (fun c => alphaRank c),
    Finset.sum_ite_eq' Finset.univ b (fun c => alphaRank c)]
  simp

/-- **Weight components of an eigenvector are eigenvectors.** -/
theorem wproj_eigen {gen : α → α → Matrix I I ℂ} {wt : I → α → ℤ}
    (hws : IsWeightSystem gen wt) {lam : ℂ} {X : I → ℂ}
    (hX : familyCasimir gen *ᵥ X = lam • X) (nu : α → ℤ) :
    familyCasimir gen *ᵥ (wproj wt nu X) = lam • (wproj wt nu X) := by
  classical
  by_cases hnu : nu ∈ weightSet wt
  · have hdec : X = ∑ mu ∈ weightSet wt, wproj wt mu X := (sum_wproj wt X).symm
    have hL : familyCasimir gen *ᵥ X
        = ∑ mu ∈ weightSet wt, familyCasimir gen *ᵥ (wproj wt mu X) := by
      conv_lhs => rw [hdec]
      rw [Matrix.mulVec_sum]
    have hsel : ∀ F : (α → ℤ) → I → ℂ, (∀ mu ∈ weightSet wt, HasWeight wt mu (F mu)) →
        wproj wt nu (∑ mu ∈ weightSet wt, F mu) = F nu := by
      intro F hF
      rw [wproj_sum, Finset.sum_eq_single nu]
      · exact wproj_of_hasWeight (hF nu hnu)
      · intro mu hmu hne
        exact wproj_of_hasWeight_ne (hF mu hmu) hne
      · intro h
        exact absurd hnu h
    have h1 : wproj wt nu (familyCasimir gen *ᵥ X)
        = familyCasimir gen *ᵥ (wproj wt nu X) := by
      rw [hL, hsel _ fun mu _ => hasWeight_casimir hws (hasWeight_wproj wt mu X)]
    rw [← h1, hX, wproj_smul]
  · have hzero : wproj wt nu X = 0 := by
      funext i
      have hne : wt i ≠ nu := by
        intro h
        apply hnu
        rw [← h]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      simp [wproj, hne]
    rw [hzero, Matrix.mulVec_zero, smul_zero]

/-- **The spectral gap.**  Every nonzero eigenvalue of the Casimir of a weighted matrix-unit family
is at least twice the alphabet size. -/
theorem casimir_eigenvalue_gap {gen : α → α → Matrix I I ℂ} {wt : I → α → ℤ}
    (hfam : IsMatrixUnitFamily gen) (hws : IsWeightSystem gen wt)
    {lam : ℝ} {Y : I → ℂ} (hY : Y ≠ 0)
    (heig : familyCasimir gen *ᵥ Y = (lam : ℂ) • Y) :
    lam = 0 ∨ 2 * (Fintype.card α : ℝ) ≤ lam := by
  classical
  -- the eigen-weights
  set Good : Finset (α → ℤ) :=
    (weightSet wt).filter (fun nu => ∃ Z : I → ℂ, Z ≠ 0 ∧ HasWeight wt nu Z ∧
      familyCasimir gen *ᵥ Z = (lam : ℂ) • Z) with hGood
  have hGoodne : Good.Nonempty := by
    obtain ⟨i, hi⟩ : ∃ i, Y i ≠ 0 := by
      by_contra hc
      exact hY (funext fun i => not_not.mp fun h => hc ⟨i, h⟩)
    refine ⟨wt i, ?_⟩
    rw [hGood, Finset.mem_filter]
    refine ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩,
      wproj wt (wt i) Y, ?_, hasWeight_wproj wt (wt i) Y, wproj_eigen hws heig (wt i)⟩
    intro hz
    apply hi
    have := congrFun hz i
    simpa [wproj] using this
  obtain ⟨nu, hnuGood, hnumax⟩ := Good.exists_max_image weightRank hGoodne
  rw [hGood, Finset.mem_filter] at hnuGood
  obtain ⟨-, Z, hZne, hZwt, hZeig⟩ := hnuGood
  have hZnorm : 0 < cnormSq Z := by
    rcases lt_or_eq_of_le (cnormSq_nonneg Z) with h | h
    · exact h
    · exact absurd ((cnormSq_eq_zero_iff Z).mp h.symm) hZne
  -- raising generators annihilate the maximal weight
  have hraise : ∀ a b : α, a < b → gen a b *ᵥ Z = 0 := by
    intro a b hab
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, (gen a b *ᵥ Z) i ≠ 0 := by
      by_contra hc
      exact hne (funext fun i => not_not.mp fun h => hc ⟨i, h⟩)
    have hwt : HasWeight wt (shiftWeight a b nu) (gen a b *ᵥ Z) := hasWeight_mulVec hws a b hZwt
    have hmem : shiftWeight a b nu ∈ weightSet wt := by
      have : wt i = shiftWeight a b nu := by
        by_contra hh
        exact hi (hwt i hh)
      rw [← this]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have heigshift : familyCasimir gen *ᵥ (gen a b *ᵥ Z) = (lam : ℂ) • (gen a b *ᵥ Z) := by
      rw [Matrix.mulVec_mulVec, familyCasimir_commute hfam a b, ← Matrix.mulVec_mulVec, hZeig,
        Matrix.mulVec_smul]
    have hgood : shiftWeight a b nu ∈ Good := by
      rw [hGood, Finset.mem_filter]
      exact ⟨hmem, gen a b *ᵥ Z, hne, hwt, heigshift⟩
    have hle := hnumax _ hgood
    rw [weightRank_shiftWeight] at hle
    have := alphaRank_lt hab
    omega
  -- the Cartan generators act by the weight
  have hcartan : ∀ a : α, gen a a *ᵥ Z = ((nu a : ℤ) : ℂ) • Z := by
    intro a
    funext i
    rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    have hterm : ∀ j : I, gen a a i j * Z j = if i = j then ((wt i a : ℤ) : ℂ) * Z j else 0 := by
      intro j
      rw [hws.diag a i j]
      by_cases h : i = j
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, zero_mul]
    rw [Finset.sum_congr rfl fun j _ => hterm j,
      Finset.sum_ite_eq Finset.univ i (fun j => ((wt i a : ℤ) : ℂ) * Z j)]
    simp only [Finset.mem_univ, if_true]
    by_cases hi : wt i = nu
    · rw [hi]
    · rw [hZwt i hi]
      ring
  -- the lowering generators carry the ordered differences
  have hlower : ∀ a b : α, a < b →
      cnormSq (gen b a *ᵥ Z) = ((nu a - nu b : ℤ) : ℝ) * cnormSq Z := by
    intro a b hab
    have hbr : gen a b * gen b a - gen b a * gen a b = gen a a - gen b b := by
      have h := hfam.2 a b b a
      simpa using h
    have hE1 : cinner Z ((gen a b * gen b a) *ᵥ Z) = ((cnormSq (gen b a *ᵥ Z) : ℝ) : ℂ) := by
      rw [← Matrix.mulVec_mulVec, cinner_mulVec, hfam.1 a b, cinner_self]
    have hE2 : cinner Z ((gen b a * gen a b) *ᵥ Z) = ((cnormSq (gen a b *ᵥ Z) : ℝ) : ℂ) := by
      rw [← Matrix.mulVec_mulVec, cinner_mulVec, hfam.1 b a, cinner_self]
    have hzero : cnormSq (gen a b *ᵥ Z) = 0 := by
      rw [hraise a b hab, cnormSq]
      simp
    have hdiff : (gen a b * gen b a) *ᵥ Z - (gen b a * gen a b) *ᵥ Z
        = ((nu a - nu b : ℤ) : ℂ) • Z := by
      rw [← Matrix.sub_mulVec, hbr, Matrix.sub_mulVec, hcartan a, hcartan b, ← sub_smul]
      push_cast
      ring_nf
    have hcin : cinner Z ((gen a b * gen b a) *ᵥ Z) - cinner Z ((gen b a * gen a b) *ᵥ Z)
        = ((nu a - nu b : ℤ) : ℂ) * ((cnormSq Z : ℝ) : ℂ) := by
      have hlin : cinner Z ((gen a b * gen b a) *ᵥ Z) - cinner Z ((gen b a * gen a b) *ᵥ Z)
          = cinner Z ((gen a b * gen b a) *ᵥ Z - (gen b a * gen a b) *ᵥ Z) := by
        rw [cinner, cinner, cinner, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        show _ = (starRingEnd ℂ) (Z i) * (((gen a b * gen b a) *ᵥ Z) i -
          ((gen b a * gen a b) *ᵥ Z) i)
        ring
      rw [hlin, hdiff]
      rw [cinner]
      have hstep : ∀ i : I, (starRingEnd ℂ) (Z i) * ((((nu a - nu b : ℤ) : ℂ) • Z) i)
          = ((nu a - nu b : ℤ) : ℂ) * ((starRingEnd ℂ) (Z i) * Z i) := by
        intro i
        rw [Pi.smul_apply, smul_eq_mul]
        ring
      rw [Finset.sum_congr rfl fun i _ => hstep i, ← Finset.mul_sum, ← cinner, cinner_self]
    rw [hE1, hE2, hzero] at hcin
    have : ((cnormSq (gen b a *ᵥ Z) : ℝ) : ℂ)
        = (((((nu a - nu b : ℤ) : ℝ) * cnormSq Z : ℝ)) : ℂ) := by
      push_cast at hcin ⊢
      linear_combination hcin
    exact_mod_cast this
  -- the weight is decreasing with zero sum
  have hmono : ∀ a b : α, a < b → nu b ≤ nu a := by
    intro a b hab
    have h1 := hlower a b hab
    have h2 : (0 : ℝ) ≤ ((nu a - nu b : ℤ) : ℝ) * cnormSq Z := by
      rw [← h1]
      exact cnormSq_nonneg _
    have h3 : (0 : ℝ) ≤ ((nu a - nu b : ℤ) : ℝ) := by
      by_contra hneg
      have hlt : ((nu a - nu b : ℤ) : ℝ) < 0 := lt_of_not_ge hneg
      nlinarith [h2, hZnorm, hlt]
    have h4 : (0 : ℤ) ≤ nu a - nu b := by exact_mod_cast h3
    omega
  have hzerosum : ∑ a, nu a = 0 := by
    obtain ⟨i, hi⟩ : ∃ i : I, wt i = nu := by
      by_contra hc
      apply hZne
      funext i
      exact hZwt i fun h => hc ⟨i, h⟩
    rw [← hi]
    exact hws.zerosum i
  -- the Casimir energy of the maximal weight vector
  have hsmul : ∀ (c : ℂ) (X : I → ℂ), cnormSq (c • X) = ‖c‖ ^ 2 * cnormSq X := by
    intro c X
    rw [cnormSq, cnormSq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  set F : α → α → ℝ := fun a b => cnormSq (gen a b *ᵥ Z) with hF
  have hFdiag : ∀ a : α, F a a = ((nu a : ℤ) : ℝ) ^ 2 * cnormSq Z := by
    intro a
    rw [hF]
    simp only
    rw [hcartan a, hsmul]
    congr 1
    rw [Complex.norm_intCast]
    rw [sq_abs]
  have hFup : ∀ a b : α, a < b → F a b = 0 := by
    intro a b hab
    rw [hF]
    simp only
    rw [hraise a b hab, cnormSq]
    simp
  have hFdown : ∀ a b : α, b < a → F a b = ((nu b - nu a : ℤ) : ℝ) * cnormSq Z := by
    intro a b hba
    exact hlower b a hba
  have hsplitb : ∀ a : α, (∑ b, F a b) = F a a + ∑ b, (if b < a then F a b else 0) := by
    intro a
    have hterm : ∀ b : α, F a b
        = (if b = a then F a a else 0) + (if b < a then F a b else 0)
          + (if a < b then F a b else 0) := by
      intro b
      rcases lt_trichotomy b a with h | h | h
      · simp only [if_neg (ne_of_lt h), if_pos h, if_neg (asymm h)]
        try ring
      · subst h
        simp
      · simp only [if_neg (ne_of_gt h), if_neg (asymm h), if_pos h]
        try ring
    have hzeroup : (∑ b, (if a < b then F a b else 0)) = 0 := by
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases h : a < b
      · rw [if_pos h, hFup a b h]
      · rw [if_neg h]
    rw [Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ a (fun _ => F a a), hzeroup]
    simp
  have henergy : ((lam : ℝ)) * cnormSq Z = ((weightCasimir nu : ℤ) : ℝ) * cnormSq Z := by
    have hC := cinner_familyCasimir hfam Z
    have hL : cinner Z (familyCasimir gen *ᵥ Z)
        = ((lam : ℝ) : ℂ) * ((cnormSq Z : ℝ) : ℂ) := by
      rw [hZeig, cinner]
      have hstep : ∀ i : I, (starRingEnd ℂ) (Z i) * (((lam : ℂ) • Z) i)
          = ((lam : ℝ) : ℂ) * ((starRingEnd ℂ) (Z i) * Z i) := by
        intro i
        rw [Pi.smul_apply, smul_eq_mul]
        ring
      rw [Finset.sum_congr rfl fun i _ => hstep i, ← Finset.mul_sum, ← cinner, cinner_self]
    have hR : (∑ a, ∑ b, ((cnormSq (gen b a *ᵥ Z) : ℝ) : ℂ))
        = ((∑ a, ∑ b, F a b : ℝ) : ℂ) := by
      rw [Finset.sum_comm]
      push_cast
      rfl
    rw [hL, hR] at hC
    have hreal : (lam : ℝ) * cnormSq Z = ∑ a, ∑ b, F a b := by
      have := hC
      push_cast at this
      exact_mod_cast this
    rw [hreal]
    -- evaluate the double sum
    have hdouble : (∑ a, ∑ b, F a b)
        = (∑ a, ((nu a : ℤ) : ℝ) ^ 2 * cnormSq Z)
          + ∑ a, ∑ b, (if b < a then ((nu b - nu a : ℤ) : ℝ) * cnormSq Z else 0) := by
      rw [Finset.sum_congr rfl fun a _ => hsplitb a, Finset.sum_add_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun a _ => hFdiag a
      · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        by_cases h : b < a
        · rw [if_pos h, if_pos h, hFdown a b h]
        · rw [if_neg h, if_neg h]
    have hswap : (∑ a, ∑ b, (if b < a then ((nu b - nu a : ℤ) : ℝ) * cnormSq Z else 0))
        = ∑ a, ∑ b, (if a < b then ((nu a - nu b : ℤ) : ℝ) * cnormSq Z else 0) := by
      rw [Finset.sum_comm]
    have hpairsum : (∑ a, ∑ b, (if a < b then ((nu a - nu b : ℤ) : ℝ) * cnormSq Z else 0))
        = ((∑ p ∈ Finset.univ.filter (fun p : α × α => p.1 < p.2),
            (nu p.1 - nu p.2) : ℤ) : ℝ) * cnormSq Z := by
      rw [Finset.sum_filter]
      push_cast
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases h : a < b
      · rw [if_pos h, if_pos h]
        try push_cast
        try ring
      · rw [if_neg h, if_neg h, zero_mul]
    rw [hdouble, hswap, hpairsum, ← Finset.sum_mul, weightCasimir]
    push_cast
    ring
  have hlamval : (lam : ℝ) = ((weightCasimir nu : ℤ) : ℝ) :=
    mul_right_cancel₀ (ne_of_gt hZnorm) henergy
  by_cases hzero : ∀ a : α, nu a = 0
  · left
    rw [hlamval, weightCasimir]
    have h1 : (∑ a, (nu a) ^ 2) = 0 := Finset.sum_eq_zero fun a _ => by rw [hzero a]; ring
    have h2 : (∑ p ∈ Finset.univ.filter (fun p : α × α => p.1 < p.2), (nu p.1 - nu p.2)) = 0 :=
      Finset.sum_eq_zero fun p _ => by rw [hzero p.1, hzero p.2]; ring
    rw [h1, h2]
    norm_num
  · right
    have hne : ∃ a, nu a ≠ 0 := by
      by_contra hc
      exact hzero fun a => not_not.mp fun h => hc ⟨a, h⟩
    have hgap := two_mul_card_le_weightCasimir nu hzerosum hmono hne
    rw [hlamval]
    exact_mod_cast hgap

end Gap

end

end GaloisForLFunctions.HTGeometry
