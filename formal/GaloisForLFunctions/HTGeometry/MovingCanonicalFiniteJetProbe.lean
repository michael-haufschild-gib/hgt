import GaloisForLFunctions.HTGeometry.MovingCanonicalJetControllability

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem natDegree_clearedCauchyJetPolynomial_lt_totalOrder
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (n : ι → ℕ) (c : (i : ι) → Fin (n i) → ℂ)
    (htotal : 0 < ∑ i, n i) :
    (clearedCauchyJetPolynomial x n c).natDegree < ∑ i, n i := by
  rw [clearedCauchyJetPolynomial]
  refine lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le _ _
      (fun i _ => Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)))
    (Nat.sub_lt htotal Nat.zero_lt_one)
  have hpow :
      ((X - C (x i)) ^ j.1).natDegree ≤ j.1 := by
    calc
      ((X - C (x i)) ^ j.1).natDegree ≤
          j.1 * (X - C (x i)).natDegree :=
        Polynomial.natDegree_pow_le
      _ = j.1 := by simp
  have hprod :
      (∏ k ∈ Finset.univ.erase i, (X - C (x k)) ^ n k).natDegree ≤
        ∑ k ∈ Finset.univ.erase i, n k := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro k hk
    calc
      ((X - C (x k)) ^ n k).natDegree ≤
          n k * (X - C (x k)).natDegree :=
        Polynomial.natDegree_pow_le
      _ = n k := by simp
  have hterm :
      (C (c i j.rev) * (X - C (x i)) ^ j.1 *
        ∏ k ∈ Finset.univ.erase i, (X - C (x k)) ^ n k).natDegree ≤
        j.1 + ∑ k ∈ Finset.univ.erase i, n k := by
    calc
      (C (c i j.rev) * (X - C (x i)) ^ j.1 *
          ∏ k ∈ Finset.univ.erase i, (X - C (x k)) ^ n k).natDegree ≤
          (C (c i j.rev) * (X - C (x i)) ^ j.1).natDegree +
            (∏ k ∈ Finset.univ.erase i,
              (X - C (x k)) ^ n k).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ j.1 + ∑ k ∈ Finset.univ.erase i, n k := by
        apply add_le_add
        · exact (Polynomial.natDegree_C_mul_le _ _).trans hpow
        · exact hprod
  have hsum :
      (∑ k ∈ Finset.univ.erase i, n k) + n i = ∑ k, n k := by
    exact Finset.sum_erase_add _ _ (Finset.mem_univ i)
  have hlt :
      j.1 + ∑ k ∈ Finset.univ.erase i, n k < ∑ k, n k := by
    omega
  omega

/-- A finite support whose cardinality reaches the total pole order already detects every
confluent Cauchy coefficient. -/
theorem cauchyJet_coeff_eq_zero_of_card_ge_totalOrder
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (x : ι → ℂ) (hx : Function.Injective x) (n : ι → ℕ)
    (htotal : 0 < ∑ i, n i)
    (t : κ → ℂ) (ht : Function.Injective t) (hsep : ∀ a i, t a ≠ x i)
    (hcard : ∑ i, n i ≤ Fintype.card κ)
    (c : (i : ι) → Fin (n i) → ℂ)
    (hzero : ∀ a, ∑ i, ∑ j : Fin (n i),
      c i j * ((t a - x i)⁻¹) ^ (j.1 + 1) = 0) :
    ∀ i j, c i j = 0 := by
  let Q := clearedCauchyJetPolynomial x n c
  let S : Finset ℂ := Finset.univ.image t
  have hroot : ∀ z ∈ S, Q.eval z = 0 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    dsimp only [Q]
    rw [eval_clearedCauchyJetPolynomial_eq_mul_sum x n c (t a) (hsep a),
      hzero a, mul_zero]
  have hQ : Q = 0 := by
    by_contra hQ
    have hsub : S.val ⊆ Q.roots := by
      intro z hz
      rw [Polynomial.mem_roots']
      exact ⟨hQ, hroot z hz⟩
    have hrootCard := Polynomial.card_le_degree_of_subset_roots hsub
    have hScard : S.card = Fintype.card κ := by
      change (Finset.univ.image t).card = Fintype.card κ
      rw [Finset.card_image_of_injective _ ht, Finset.card_univ]
    have hdegree : Q.natDegree < ∑ i, n i :=
      natDegree_clearedCauchyJetPolynomial_lt_totalOrder x n c htotal
    rw [hScard] at hrootCard
    omega
  let g : ι → ℂ[X] := fun i => X - C (x i)
  let r₁ : (i : ι) → Fin (n i) → ℂ[X] := fun i j => C (c i j.rev)
  let r₂ : (i : ι) → Fin (n i) → ℂ[X] := fun _ _ => 0
  have hg : ∀ i ∈ (Finset.univ : Finset ι), (g i).Monic := by
    intro i hi
    exact monic_X_sub_C (x i)
  have hcop : Set.Pairwise (↑(Finset.univ : Finset ι)) fun i j =>
      IsCoprime (g i) (g j) := by
    intro i hi j hj hij
    exact pairwise_coprime_X_sub_C hx hij
  have hr₁ : ∀ i ∈ (Finset.univ : Finset ι), ∀ j,
      (r₁ i j).degree < (g i).degree := by
    intro i hi j
    by_cases hc : c i j.rev = 0 <;> simp [r₁, g, hc]
  have hr₂ : ∀ i ∈ (Finset.univ : Finset ι), ∀ j,
      (r₂ i j).degree < (g i).degree := by
    intro i hi j
    simp [r₂, g]
  have hf : (0 : ℂ[X]) * (∏ i ∈ (Finset.univ : Finset ι), g i ^ n i) +
        ∑ i ∈ (Finset.univ : Finset ι), ∑ j,
          r₁ i j * g i ^ j.1 * ∏ k ∈ Finset.univ.erase i, g k ^ n k =
      (0 : ℂ[X]) * (∏ i ∈ (Finset.univ : Finset ι), g i ^ n i) +
        ∑ i ∈ (Finset.univ : Finset ι), ∑ j,
          r₂ i j * g i ^ j.1 * ∏ k ∈ Finset.univ.erase i, g k ^ n k := by
    simpa [Q, clearedCauchyJetPolynomial, g, r₁, r₂] using hQ
  have hu := Polynomial.quo_mul_prod_pow_add_sum_rem_mul_prod_pow_unique
    hg hcop hr₁ hr₂ hf
  intro i j
  have hij := congrFun (hu.2 i (Finset.mem_univ i)) j.rev
  simpa [r₁, r₂] using congrArg (fun P : ℂ[X] => P.coeff 0) hij
/-- Number of real support columns sufficient for joint inverse-square and complex Cauchy-jet
control. -/
def inverseSquareCauchyProbeCard
    {ι : Type*} [Fintype ι] (n : ι → ℕ) : ℕ :=
  2 * (∑ i, n i) + 2

/-- Quantitative finite form of inverse-square/Cauchy controllability. -/
theorem inverseSquareCauchyJetRealLinearCombination_surjective_of_card
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (t : κ → ℝ) (ht : Function.Injective t)
    (ht0 : ∀ a, t a ≠ 0)
    (hcard : inverseSquareCauchyProbeCard n ≤ Fintype.card κ) :
    Function.Surjective
      (inverseSquareCauchyJetRealLinearCombination x n t) := by
  apply inverseSquareCauchyJetRealLinearCombination_surjective_of_real_rigidity
  intro r c hreal
  let ι₂ := ι ⊕ ι
  let x₂ : ι₂ → ℂ := Sum.elim x (fun i => star (x i))
  let n₂ : ι₂ → ℕ := Sum.elim n n
  let c₂ : (i : ι₂) → Fin (n₂ i) → ℂ := fun i =>
    match i with
    | Sum.inl q => fun j => c q j
    | Sum.inr q => fun j => star (c q j)
  have hx₂ : Function.Injective x₂ := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · exact congrArg Sum.inl (hx hij)
    · exfalso
      have him := congrArg Complex.im hij
      simp [x₂] at him
      linarith [hupper i, hupper j]
    · exfalso
      have him := congrArg Complex.im hij
      simp [x₂] at him
      linarith [hupper i, hupper j]
    · apply congrArg Sum.inr
      apply hx
      have h := congrArg star hij
      simpa [x₂] using h
  let ι₃ := ι₂ ⊕ Fin 1
  let x₃ : ι₃ → ℂ := Sum.elim x₂ (fun _ => 0)
  let n₃ : ι₃ → ℕ := Sum.elim n₂ (fun _ => 2)
  let c₃ : (i : ι₃) → Fin (n₃ i) → ℂ := fun i =>
    match i with
    | Sum.inl q => fun j => c₂ q j
    | Sum.inr _ => fun j => if j.1 = 1 then ((2 * r : ℝ) : ℂ) else 0
  have hx₃ : Function.Injective x₃ := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · exact congrArg Sum.inl (hx₂ hij)
    · exfalso
      have him := congrArg Complex.im hij
      rcases i with i | i <;> simp [x₃, x₂] at him <;>
        linarith [hupper i]
    · exfalso
      have him := congrArg Complex.im hij
      rcases j with j | j <;> simp [x₃, x₂] at him <;>
        linarith [hupper j]
    · apply congrArg Sum.inr
      exact Subsingleton.elim _ _
  have htC : Function.Injective (fun a => (t a : ℂ)) := fun a b hab =>
    ht (Complex.ofReal_injective hab)
  have hsep₃ : ∀ a i, (t a : ℂ) ≠ x₃ i := by
    intro a i h
    rcases i with i | i
    · rcases i with i | i
      · have him := congrArg Complex.im h
        simp [x₃, x₂] at him
        linarith [hupper i]
      · have him := congrArg Complex.im h
        simp [x₃, x₂] at him
        linarith [hupper i]
    · apply ht0 a
      exact Complex.ofReal_injective (by simpa [x₃] using h)
  have hzero₃ : ∀ a, ∑ i, ∑ j : Fin (n₃ i),
      c₃ i j * (((t a : ℂ) - x₃ i)⁻¹) ^ (j.1 + 1) = 0 := by
    intro a
    rw [Fintype.sum_sum_type]
    change
      (∑ q : ι₂, ∑ j : Fin (n₂ q),
          c₂ q j * (((t a : ℂ) - x₂ q)⁻¹) ^ (j.1 + 1)) +
        (∑ _q : Fin 1, ∑ j : Fin 2,
          (if j.1 = 1 then ((2 * r : ℝ) : ℂ) else 0) *
            (((t a : ℂ) - 0)⁻¹) ^ (j.1 + 1)) = 0
    rw [Fin.sum_univ_one]
    have hpole :
        (∑ j : Fin 2,
          (if j.1 = 1 then ((2 * r : ℝ) : ℂ) else 0) *
            (((t a : ℂ) - 0)⁻¹) ^ (j.1 + 1)) =
          ((2 * r : ℝ) : ℂ) * (((t a : ℂ) - 0)⁻¹) ^ 2 := by
      rw [Fin.sum_univ_two]
      simp
    rw [hpole]
    rw [Fintype.sum_sum_type]
    change
      ((∑ i, ∑ j : Fin (n i),
          c i j * (((t a : ℂ) - x i)⁻¹) ^ (j.1 + 1)) +
        (∑ i, ∑ j : Fin (n i),
          star (c i j) * (((t a : ℂ) - star (x i))⁻¹) ^ (j.1 + 1))) +
        ((2 * r : ℝ) : ℂ) * (((t a : ℂ) - 0)⁻¹) ^ 2 = 0
    let R : ℂ := ∑ i, ∑ j : Fin (n i),
      c i j * (((t a : ℂ) - x i)⁻¹) ^ (j.1 + 1)
    have hconj : (∑ i, ∑ j : Fin (n i),
        star (c i j) * (((t a : ℂ) - star (x i))⁻¹) ^ (j.1 + 1)) =
        star R := by
      simp [R]
    change (R + (∑ i, ∑ j : Fin (n i),
      star (c i j) * (((t a : ℂ) - star (x i))⁻¹) ^ (j.1 + 1))) +
        ((2 * r : ℝ) : ℂ) * (((t a : ℂ) - 0)⁻¹) ^ 2 = 0
    rw [hconj]
    have hqC : (((t a : ℂ) - 0)⁻¹) ^ 2 =
        ((1 / (t a) ^ 2 : ℝ) : ℂ) := by
      simp only [sub_zero, ← Complex.ofReal_inv, ← Complex.ofReal_pow]
      congr 1
      simp [one_div, inv_pow]
    rw [hqC]
    have hstarre : (star R).re = R.re := by simp
    have hstarim : (star R).im = -R.im := by simp
    apply Complex.ext
    · simp only [Complex.add_re]
      rw [hstarre]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.zero_re, zero_mul, sub_zero]
      linarith [hreal a]
    · simp only [Complex.add_im]
      rw [hstarim]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.zero_im, mul_zero, zero_mul, add_zero]
      ring
  have htotal₃ :
      ∑ i, n₃ i = inverseSquareCauchyProbeCard n := by
    rw [Fintype.sum_sum_type]
    change (∑ i : ι₂, n₂ i) + ∑ _i : Fin 1, 2 =
      inverseSquareCauchyProbeCard n
    rw [Fintype.sum_sum_type]
    simp [n₂, inverseSquareCauchyProbeCard]
    omega
  have hc₃ := cauchyJet_coeff_eq_zero_of_card_ge_totalOrder
    x₃ hx₃ n₃ (by rw [htotal₃]; simp [inverseSquareCauchyProbeCard])
      (fun a => (t a : ℂ)) htC hsep₃
      (by simpa only [htotal₃] using hcard) c₃ hzero₃
  have hr : r = 0 := by
    have h := hc₃ (Sum.inr 0) (1 : Fin 2)
    simp [c₃] at h
    exact h
  have hc : ∀ i j, c i j = 0 := fun i j =>
    hc₃ (Sum.inl (Sum.inl i)) j
  exact ⟨hr, hc⟩

/-- Quantitative finite form of the regularized-pole location jet lemma. -/
theorem movingPoleLocationJetRealLinearCombination_surjective_of_card
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (t : κ → ℝ) (ht : Function.Injective t)
    (ht0 : ∀ a, t a ≠ 0)
    (hcard : inverseSquareCauchyProbeCard (fun i => n i + 1) ≤
      Fintype.card κ) :
    Function.Surjective
      (movingPoleLocationJetRealLinearCombination x n t) := by
  exact (inverseSquareCauchyToLocationJet_surjective n).comp
    (inverseSquareCauchyJetRealLinearCombination_surjective_of_card
      x hx hupper (fun i => n i + 1) t ht ht0 hcard)

/-- Universal finite parameter count for one canonical location-jet packet. -/
def movingCanonicalLocationProbeCard
    {ι : Type*} [Fintype ι] (n : ι → ℕ) : ℕ :=
  inverseSquareCauchyProbeCard (fun i => n i + 1)

/-- Exact location-jet control by the initial finite block of the moving canonical divisor. -/
def movingCanonicalFiniteLocationJetLinearMap
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (n : ι → ℕ) (θ : BoundedRealSequence) :
    (Fin (movingCanonicalLocationProbeCard n) → ℝ) →ₗ[ℝ]
      ((Σ i, Fin (n i)) → ℂ) :=
  (movingPoleLocationJetRealLinearCombination x n
      (fun a : Fin (movingCanonicalLocationProbeCard n) =>
        movingCanonicalZero θ a.1)).comp
    (Finsupp.linearEquivFunOnFinite ℝ ℝ
      (Fin (movingCanonicalLocationProbeCard n))).symm.toLinearMap

/-- The explicit initial finite canonical block spans every finite complex location-jet packet. -/
theorem movingCanonicalFiniteLocationJetLinearMap_surjective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence) :
    Function.Surjective
      (movingCanonicalFiniteLocationJetLinearMap x n θ) := by
  let t : Fin (movingCanonicalLocationProbeCard n) → ℝ :=
    fun a => movingCanonicalZero θ a.1
  have hloc : Function.Surjective
      (movingPoleLocationJetRealLinearCombination x n t) := by
    have ht : Function.Injective t :=
      (movingCanonicalZero_injective θ).comp Fin.val_injective
    have ht0 : ∀ a, t a ≠ 0 :=
      fun a => ne_of_gt (movingCanonicalZero_pos θ a.1)
    have hcard : inverseSquareCauchyProbeCard (fun i => n i + 1) ≤
        Fintype.card (Fin (movingCanonicalLocationProbeCard n)) := by
      rw [Fintype.card_fin, movingCanonicalLocationProbeCard]
    exact movingPoleLocationJetRealLinearCombination_surjective_of_card
      x hx hupper n t ht ht0 hcard
  have hequiv : Function.Surjective
      (Finsupp.linearEquivFunOnFinite ℝ ℝ
        (Fin (movingCanonicalLocationProbeCard n))).symm :=
    (Finsupp.linearEquivFunOnFinite ℝ ℝ
      (Fin (movingCanonicalLocationProbeCard n))).symm.surjective
  change Function.Surjective
    ((movingPoleLocationJetRealLinearCombination x n t).comp
      (Finsupp.linearEquivFunOnFinite ℝ ℝ
        (Fin (movingCanonicalLocationProbeCard n))).symm.toLinearMap)
  exact hloc.comp hequiv

/-- Positive diagonal speed map on the universal initial finite canonical probe. -/
def movingCanonicalFiniteSpeedLinearMap
    {ι : Type*} [Fintype ι] (n : ι → ℕ)
    (θ : BoundedRealSequence) :
    (Fin (movingCanonicalLocationProbeCard n) → ℝ) →ₗ[ℝ]
      (Fin (movingCanonicalLocationProbeCard n) → ℝ) where
  toFun p a := canonicalZeroSpeed (θ a.1) * p a
  map_add' p q := by
    funext a
    simp only [Pi.add_apply]
    ring
  map_smul' r p := by
    funext a
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

theorem movingCanonicalFiniteSpeedLinearMap_surjective
    {ι : Type*} [Fintype ι] (n : ι → ℕ)
    (θ : BoundedRealSequence) :
    Function.Surjective (movingCanonicalFiniteSpeedLinearMap n θ) := by
  intro y
  refine ⟨fun a => y a / canonicalZeroSpeed (θ a.1), ?_⟩
  funext a
  simp only [movingCanonicalFiniteSpeedLinearMap, LinearMap.coe_mk,
    AddHom.coe_mk]
  exact mul_div_cancel₀ (y a)
    (ne_of_gt (canonicalZeroSpeed_pos (θ a.1)))

/-- Exact finite derivative of the canonical parameter chart on the universal initial probe. -/
def movingCanonicalFiniteParameterJetLinearMap
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (n : ι → ℕ) (θ : BoundedRealSequence) :
    (Fin (movingCanonicalLocationProbeCard n) → ℝ) →ₗ[ℝ]
      ((Σ i, Fin (n i)) → ℂ) :=
  (movingCanonicalFiniteLocationJetLinearMap x n θ).comp
    (movingCanonicalFiniteSpeedLinearMap n θ)

/-- A fixed explicit initial coordinate block gives a finite-dimensional submersion onto every
finite canonical jet packet. -/
theorem movingCanonicalFiniteParameterJetLinearMap_surjective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence) :
    Function.Surjective
      (movingCanonicalFiniteParameterJetLinearMap x n θ) :=
  (movingCanonicalFiniteLocationJetLinearMap_surjective
    x hx hupper n θ).comp
      (movingCanonicalFiniteSpeedLinearMap_surjective n θ)

end

end GaloisForLFunctions.HTGeometry
