import GaloisForLFunctions.HTGeometry.SymmetricCharacters.CycleCharacterIdentification
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Geometric cycle values: positivity and integer multiplicity

The cycle values `pₖ = t^k` pass every common-pivot Gram test for `-1 ≤ t ≤ 1`.
Full character positivity holds exactly for `t = 0` or `t = ±1/m`, with positive integer `m`.
The alternating projection is `∏_{j<n}(1-jt)`: signed stabilizers cancel on repeated-letter
words, uniform alphabets count injections, and polynomial interpolation gives the formula
for arbitrary real `t`. Its first negative factor forces the positive-parameter classification.
The regular character, uniform coloring, and sign twist supply every surviving character.
-/

open scoped BigOperators Classical
noncomputable section
namespace GaloisForLFunctions.SymmetricCharacters

variable {X : Type} {A : Type*} [Fintype X]

/-- The permutation sign as a real character. -/
def realSign (σ : Equiv.Perm X) : ℝ :=
  ((@Equiv.Perm.sign X (Classical.decEq X) _ σ : ℤ) : ℝ)

/-- Equal weights on an alphabet of `m` colors. -/
def uniformColor (m : ℕ) : Fin m → NNReal := fun _ => (m : NNReal)⁻¹

theorem tsum_uniformColor_pow (m : ℕ) (hm : 0 < m) (k : ℕ) :
    (∑' a : Fin m, (uniformColor m a : ℝ) ^ (k + 1)) = ((m : ℝ)⁻¹) ^ k := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [uniformColor, tsum_fintype, NNReal.coe_inv, NNReal.coe_natCast,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_succ]
  field_simp [hmR]

theorem tsum_uniformColor (m : ℕ) (hm : 0 < m) :
    (∑' a : Fin m, (uniformColor m a : ℝ)) = 1 := by
  simpa only [zero_add, pow_one, pow_zero] using tsum_uniformColor_pow m hm 0
/-- Unnormalized projection of a cycle class function onto the sign character. -/
def alternatingCycleMass (p : ℕ → ℝ) : ℝ :=
  ∑ σ : Equiv.Perm X, realSign σ * cycleMomentCharacter p σ

/-- A positive character has nonnegative sign projection; test its Gram matrix on signs. -/
theorem alternatingCycleMass_nonneg (p : ℕ → ℝ) (h : PositiveCycleFamily p) :
    0 ≤ alternatingCycleMass (X := X) p := by
  let v : Equiv.Perm X → ℝ := fun σ => realSign σ
  have hq := (h X (Equiv.Perm X) id).dotProduct_mulVec_nonneg v
  have hi (σ : Equiv.Perm X) :
      (∑ τ, v σ * (cycleMomentCharacter p (σ⁻¹ * τ) * v τ)) = alternatingCycleMass (X := X) p := by
    unfold alternatingCycleMass
    refine Fintype.sum_bijective (fun τ => σ⁻¹ * τ) (Group.mulLeft_bijective _) _ _ ?_
    intro τ
    simp only [v, realSign, map_mul, Equiv.Perm.sign_inv, Units.val_mul, Int.cast_mul]
    ring
  change 0 ≤ ∑ σ, v σ * (∑ τ, cycleMomentCharacter p (σ⁻¹ * τ) * v τ) at hq
  simp only [Finset.mul_sum, hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hq
  have hc : (0 : ℝ) < Fintype.card (Equiv.Perm X) := by exact_mod_cast Fintype.card_pos
  nlinarith only [hq, hc]

/-- Signed cardinality of the subgroup fixing a word. -/
def stabilizerSignSum (x : X → A) : ℝ :=
  ∑ σ : Equiv.Perm X, if x ∘ σ = x then realSign σ else 0

/-- Repeated letters give a sign-reversing stabilizer involution; distinct letters fix only identity. -/
theorem stabilizerSignSum_eq (x : X → A) :
    stabilizerSignSum x = if Function.Injective x then 1 else 0 := by
  by_cases hx : Function.Injective x
  · have hf (σ : Equiv.Perm X) : x ∘ σ = x ↔ σ = 1 := by
      constructor
      · intro h
        ext i
        exact hx (congrFun h i)
      · rintro rfl
        rfl
    simp [stabilizerSignSum, hf, hx, realSign]
  · rw [if_neg hx]
    obtain ⟨a, b, hab, hne⟩ : ∃ a b, x a = x b ∧ a ≠ b := by
      by_contra hbad
      apply hx
      intro a b hab
      by_contra hne
      exact hbad ⟨a, b, hab, hne⟩
    let s : Equiv.Perm X := Equiv.swap a b
    have hs : x ∘ s = x := by
      funext i
      by_cases ha : i = a
      · subst i; simpa [s] using hab.symm
      · by_cases hb : i = b
        · subst i; simpa [s] using hab
        · simp [s, Equiv.swap_apply_def, ha, hb]
    have hf (σ : Equiv.Perm X) : x ∘ (s * σ) = x ↔ x ∘ σ = x := by
      change (x ∘ s) ∘ σ = x ↔ _
      rw [hs]
    have ht (σ : Equiv.Perm X) :
        (if x ∘ (s * σ) = x then realSign (s * σ) else 0) =
          -(if x ∘ σ = x then realSign σ else 0) := by
      simp only [hf]
      simp only [s, realSign, map_mul, Equiv.Perm.sign_swap hne, Units.val_mul]
      split_ifs <;> simp
    have he := Fintype.sum_bijective (fun σ : Equiv.Perm X => s * σ)
      (Group.mulLeft_bijective s)
      (fun σ => -(if x ∘ σ = x then realSign σ else 0))
      (fun σ => if x ∘ σ = x then realSign σ else 0)
      (fun σ => (ht σ).symm)
    simp only [Finset.sum_neg_distrib] at he
    change -stabilizerSignSum x = stabilizerSignSum x at he
    linarith only [he]

/-- Every geometric moment sequence with parameter in `[-1,1]` passes all common-pivot tests. -/
theorem geometric_all_pivotGram_posSemidef {I : Type*} [Fintype I]
    {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 1) (r : I → ℕ) :
    ∀ n, (pivotGram (fun k => t ^ k) r n).PosSemidef := by
  apply (forall_pivotGram_posSemidef_iff (fun k => t ^ k) (pow_zero t) r).mpr
  constructor
  · convert Matrix.posSemidef_vecMulVec_self_star (fun i => t ^ r i) using 1
    ext i j
    simp only [Matrix.vecMulVec_apply, star_trivial, pow_add]
  · intro i
    have ht2 : t ^ 2 ≤ 1 := by
      have h := mul_nonneg (sub_nonneg.mpr ht1) (show 0 ≤ 1 + t by linarith only [ht0])
      nlinarith only [h]
    rw [show r i + r i = 2 * r i by omega, pow_mul]
    exact pow_le_one₀ (sq_nonneg _) ht2

/-- The sign projection of independent coloring is exactly the mass of injective words. -/
theorem sum_sign_coloring [Fintype A] (w : A → NNReal) :
    (∑ σ : Equiv.Perm X, realSign σ * coloringCharacter w σ) =
      ∑ x : X → A, if Function.Injective x then wordWeight w x else 0 := by
  simp only [coloringCharacter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  calc
    (∑ σ : Equiv.Perm X, realSign σ *
        (if x ∘ σ = x then wordWeight w x else 0)) =
      ∑ σ : Equiv.Perm X, (if x ∘ σ = x then realSign σ else 0) * wordWeight w x := by
        apply Finset.sum_congr rfl
        intro σ _
        split_ifs <;> simp
    _ = stabilizerSignSum x * wordWeight w x := by rw [← Finset.sum_mul]; rfl
    _ = _ := by rw [stabilizerSignSum_eq]; split_ifs <;> simp

/-- A uniform alphabet counts injections by the falling factorial. -/
theorem sum_sign_coloring_uniform (m : ℕ) (a : NNReal) :
    (∑ σ : Equiv.Perm X, realSign σ * coloringCharacter (fun _ : Fin m => a) σ) =
      (m.descFactorial (Fintype.card X) : ℝ) * (a : ℝ) ^ Fintype.card X := by
  rw [sum_sign_coloring]
  simp only [wordWeight, Finset.prod_const, Finset.card_univ]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 1
  norm_cast
  rw [← Fintype.card_subtype,
    Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding X (Fin m)),
    Fintype.card_embedding_eq, Fintype.card_fin]

/-- Uniform coloring realizes the geometric cycle values at reciprocal integers. -/
theorem coloringCharacter_uniform_eq (m : ℕ) (hm : 0 < m) (σ : Equiv.Perm X) :
    coloringCharacter (uniformColor m) σ =
      cycleMomentCharacter (fun k => ((m : ℝ)⁻¹) ^ k) σ := by
  have h := wordCharacter_eq_cycleMomentCharacter (uniformColor m)
    (hasSum_fintype _).summable (tsum_uniformColor m hm) σ
  have he' : (fun n => ∑' a : Fin m, (uniformColor m a : ℝ) ^ (n + 1)) =
      (fun n => ((m : ℝ)⁻¹) ^ n) := by
    funext n
    exact tsum_uniformColor_pow m hm n
  rw [he'] at h
  simpa only [wordCharacter, coloringCharacter, tsum_fintype] using h

open Polynomial in
private def alternatingCyclePolynomial : Polynomial ℝ :=
  ∑ σ : Equiv.Perm X, C (realSign σ) *
    (σ.cycleType.map (fun k => (Polynomial.X : Polynomial ℝ) ^ (k - 1))).prod

open Polynomial in
private def alternatingProductPolynomial (n : ℕ) : Polynomial ℝ :=
  ∏ j ∈ Finset.range n, (1 - C (j : ℝ) * Polynomial.X)

private theorem alternatingCyclePolynomial_eval (t : ℝ) :
    (alternatingCyclePolynomial (X := X)).eval t =
      alternatingCycleMass (X := X) (fun k => t ^ k) := by
  simp only [alternatingCyclePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_multiset_prod, Multiset.map_map,
    Function.comp_def, Polynomial.eval_pow, Polynomial.eval_X]
  rfl

private theorem alternatingProductPolynomial_eval (n : ℕ) (t : ℝ) :
    (alternatingProductPolynomial n).eval t = ∏ j ∈ Finset.range n, (1 - j * t) := by
  simp only [alternatingProductPolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

/-- The zero parameter gives the regular character. -/
theorem cycleMomentCharacter_geometric_zero (σ : Equiv.Perm X) :
    cycleMomentCharacter (fun k => (0 : ℝ) ^ k) σ = if σ = 1 then 1 else 0 := by
  by_cases hs : σ = 1
  · simp [hs, cycleMomentCharacter_one]
  · rw [if_neg hs]
    have hc : σ.cycleType ≠ 0 := fun hc => hs (Equiv.Perm.cycleType_eq_zero.mp hc)
    obtain ⟨k, hk⟩ := Multiset.exists_mem_of_ne_zero hc
    have hk2 := Equiv.Perm.two_le_of_mem_cycleType hk
    apply Multiset.prod_eq_zero
    exact Multiset.mem_map.mpr ⟨k, hk, zero_pow (by omega)⟩

theorem positiveCycleFamily_geometric_zero : PositiveCycleFamily (fun k => (0 : ℝ) ^ k) := by
  intro X J _ _ g
  have h := (Matrix.PosSemidef.one :
    Matrix.PosSemidef (1 : Matrix (Equiv.Perm X) (Equiv.Perm X) ℝ)).submatrix g
  convert h using 1
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.one_apply]
  rw [cycleMomentCharacter_geometric_zero]
  simp only [inv_mul_eq_one]

private theorem alternatingProduct_inv_nat (m n : ℕ) (hm : 0 < m) :
    (∏ j ∈ Finset.range n, (1 - (j : ℝ) * (m : ℝ)⁻¹)) =
      (m.descFactorial n : ℝ) * ((m : ℝ)⁻¹) ^ n := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have he : (∏ j ∈ Finset.range n, (1 - (j : ℝ) * (m : ℝ)⁻¹)) =
      (descPochhammer ℝ n).eval (m : ℝ) * ((m : ℝ)⁻¹) ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, ih, descPochhammer_succ_right]
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_natCast, pow_succ]
      field_simp [hmR]
  rwa [descPochhammer_eval_eq_descFactorial] at he

/-- Agreement at infinitely many reciprocal integers determines the alternating polynomial. -/
private theorem alternatingCyclePolynomial_eq :
    alternatingCyclePolynomial (X := X) = alternatingProductPolynomial (Fintype.card X) := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Function.Injective (fun m : ℕ => ((m + 1 : ℕ) : ℝ)⁻¹) := by
    intro a b h
    have he := inv_injective h
    exact Nat.add_right_cancel (Nat.cast_injective he)
  apply (Set.infinite_range_of_injective hi).mono
  rintro t ⟨m, rfl⟩
  change (alternatingCyclePolynomial (X := X)).eval (((m + 1 : ℕ) : ℝ)⁻¹) =
    (alternatingProductPolynomial (Fintype.card X)).eval (((m + 1 : ℕ) : ℝ)⁻¹)
  rw [alternatingCyclePolynomial_eval, alternatingProductPolynomial_eval,
    alternatingProduct_inv_nat (m + 1) (Fintype.card X) (by omega)]
  unfold alternatingCycleMass
  simp_rw [← coloringCharacter_uniform_eq (m + 1) (by omega)]
  unfold uniformColor
  rw [sum_sign_coloring_uniform]
  simp only [NNReal.coe_inv, NNReal.coe_natCast]

/-- Exact alternating projection at every rank and every real geometric parameter. -/
theorem alternatingCycleMass_geometric (n : ℕ) (t : ℝ) :
    alternatingCycleMass (X := Fin n) (fun k => t ^ k) =
      ∏ j ∈ Finset.range n, (1 - (j : ℝ) * t) := by
  rw [← alternatingCyclePolynomial_eval, alternatingCyclePolynomial_eq,
    alternatingProductPolynomial_eval, Fintype.card_fin]

/-- The first negative factor excludes every positive parameter not equal to a reciprocal integer. -/
theorem geometric_positive_parameter_quantized {t : ℝ} (ht : 0 < t)
    (h : PositiveCycleFamily (fun k => t ^ k)) :
    ∃ m : ℕ, 0 < m ∧ t = (m : ℝ)⁻¹ := by
  have hroot : ∃ m : ℕ, (m : ℝ) * t = 1 := by
    by_contra hn
    push Not at hn
    have hex : ∃ m : ℕ, 1 < (m : ℝ) * t := by
      obtain ⟨m, hm⟩ := exists_nat_gt (1 / t)
      exact ⟨m, (div_lt_iff₀ ht).mp hm⟩
    let n := Nat.find hex
    have hlast : 1 < (n : ℝ) * t := Nat.find_spec hex
    have hprev : ∀ j ∈ Finset.range n, 0 < 1 - (j : ℝ) * t := by
      intro j hj
      have hjn : j < Nat.find hex := Finset.mem_range.mp hj
      have hle : (j : ℝ) * t ≤ 1 := le_of_not_gt (Nat.find_min hex hjn)
      exact sub_pos.mpr (lt_of_le_of_ne hle (hn j))
    have hp : 0 < ∏ j ∈ Finset.range n, (1 - (j : ℝ) * t) := Finset.prod_pos hprev
    have hneg : (∏ j ∈ Finset.range (n + 1), (1 - (j : ℝ) * t)) < 0 := by
      rw [Finset.prod_range_succ]
      exact mul_neg_of_pos_of_neg hp (sub_neg.mpr hlast)
    have hpos := alternatingCycleMass_nonneg (X := Fin (n + 1)) (fun k => t ^ k) h
    rw [alternatingCycleMass_geometric] at hpos
    exact (not_lt_of_ge hpos) hneg
  obtain ⟨m, hm⟩ := hroot
  have hm0 : 0 < m := by
    by_contra hh
    have he : m = 0 := by omega
    simp [he] at hm
  refine ⟨m, hm0, ?_⟩
  exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hm)

/-- Twisting by permutation sign alternates the cycle moments. -/
theorem cycleMomentCharacter_signTwist (p : ℕ → ℝ) (σ : Equiv.Perm X) :
    cycleMomentCharacter (fun k => (-1 : ℝ) ^ k * p k) σ =
      realSign σ * cycleMomentCharacter p σ := by
  have hd (q : ℕ → ℝ) (σ τ : Equiv.Perm X) (h : Equiv.Perm.Disjoint σ τ) :
      cycleMomentCharacter q (σ * τ) = cycleMomentCharacter q σ * cycleMomentCharacter q τ := by
    simp only [cycleMomentCharacter, h.cycleType_mul, Multiset.map_add, Multiset.prod_add]
  induction σ using Equiv.Perm.cycle_induction_on with
  | base_one => simp [cycleMomentCharacter_one, realSign]
  | base_cycles σ hσ =>
    have hk : 1 ≤ σ.support.card := by have := hσ.two_le_card_support; omega
    have hsg : realSign σ = -(-1 : ℝ) ^ σ.support.card := by
      rw [realSign, hσ.sign]
      norm_cast
    have hp : (-1 : ℝ) ^ (σ.support.card - 1) = -(-1 : ℝ) ^ σ.support.card := by
      calc
        _ = -((-1 : ℝ) ^ (σ.support.card - 1) * (-1)) := by ring
        _ = _ := by rw [← pow_succ, Nat.sub_add_cancel hk]
    simp only [cycleMomentCharacter, hσ.cycleType, Multiset.map_singleton,
      Multiset.prod_singleton, hp, hsg]
  | induction_disjoint σ τ hστ _ hσ hτ =>
    rw [hd _ _ _ hστ, hd _ _ _ hστ, hσ, hτ]
    simp only [realSign, map_mul, Units.val_mul, Int.cast_mul]
    ring

/-- Sign twist is a diagonal congruence of every test Gram matrix. -/
theorem positiveCycleFamily_signTwist (p : ℕ → ℝ) (h : PositiveCycleFamily p) :
    PositiveCycleFamily (fun k => (-1 : ℝ) ^ k * p k) := by
  intro X J _ _ g
  let d : J → ℝ := fun j => realSign (g j)
  have hd := (h X J g).mul_mul_conjTranspose_same (Matrix.diagonal d)
  convert hd using 1
  ext i j
  rw [cycleMomentCharacter_signTwist]
  simp only [realSign, map_mul, Equiv.Perm.sign_inv, Units.val_mul, Int.cast_mul]
  simp [Matrix.mul_apply, Matrix.diagonal, d, realSign,
    mul_assoc, mul_comm]

theorem positiveCycleFamily_geometric_neg {t : ℝ}
    (h : PositiveCycleFamily (fun k => t ^ k)) :
    PositiveCycleFamily (fun k => (-t) ^ k) := by
  have he : (fun k => (-t) ^ k) = (fun k => (-1 : ℝ) ^ k * t ^ k) := by
    funext k
    rw [← mul_pow, neg_one_mul]
  rw [he]
  exact positiveCycleFamily_signTwist _ h

theorem positiveCycleFamily_geometric_inv_nat (m : ℕ) (hm : 0 < m) :
    PositiveCycleFamily (fun k => ((m : ℝ)⁻¹) ^ k) := by
  have h := wordCharacter_positiveCycleFamily (uniformColor m)
    (hasSum_fintype _).summable (tsum_uniformColor m hm)
  have he' : (fun k => ∑' a : Fin m, (uniformColor m a : ℝ) ^ (k + 1)) =
      (fun k => ((m : ℝ)⁻¹) ^ k) := by
    funext k
    exact tsum_uniformColor_pow m hm k
  rwa [he'] at h

/-- Full geometric character positivity quantizes nonzero parameters to signed reciprocal integers. -/
theorem positiveCycleFamily_geometric_iff (t : ℝ) :
    PositiveCycleFamily (fun k => t ^ k) ↔
      t = 0 ∨ ∃ m : ℕ, 0 < m ∧ (t = (m : ℝ)⁻¹ ∨ t = -(m : ℝ)⁻¹) := by
  constructor
  · intro h
    rcases lt_trichotomy t 0 with ht | ht | ht
    · obtain ⟨m, hm, he⟩ := geometric_positive_parameter_quantized (neg_pos.mpr ht)
        (positiveCycleFamily_geometric_neg h)
      exact Or.inr ⟨m, hm, Or.inr (by linarith only [he])⟩
    · exact Or.inl ht
    · obtain ⟨m, hm, he⟩ := geometric_positive_parameter_quantized ht h
      exact Or.inr ⟨m, hm, Or.inl he⟩
  · rintro (rfl | ⟨m, hm, rfl | rfl⟩)
    · exact positiveCycleFamily_geometric_zero
    · exact positiveCycleFamily_geometric_inv_nat m hm
    · exact positiveCycleFamily_geometric_neg (positiveCycleFamily_geometric_inv_nat m hm)

end GaloisForLFunctions.SymmetricCharacters
