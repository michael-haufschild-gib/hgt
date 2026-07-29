import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Real Cauchy-jet controllability on infinite supports

A finite packet of confluent Cauchy kernels at distinct upper-half-plane nodes is controllable by
finitely supported real masses on any infinite injective real support.  The proof clears all
denominators, uses infinite-root polynomial rigidity and uniqueness of partial fractions, and then
passes from complex to real controls by adjoining the Schwarz-conjugate node packet.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The polynomial obtained after clearing all denominators of a confluent Cauchy-jet form. -/
def clearedCauchyJetPolynomial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (n : ι → ℕ) (c : (i : ι) → Fin (n i) → ℂ) : ℂ[X] :=
  ∑ i, ∑ j : Fin (n i), C (c i j.rev) * (X - C (x i)) ^ j.1 *
    ∏ k ∈ Finset.univ.erase i, (X - C (x k)) ^ n k

theorem eval_clearedCauchyJetPolynomial_eq_mul_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (n : ι → ℕ) (c : (i : ι) → Fin (n i) → ℂ)
    (t : ℂ) (ht : ∀ i, t ≠ x i) :
    (clearedCauchyJetPolynomial x n c).eval t =
      (∏ i, (t - x i) ^ n i) *
        (∑ i, ∑ j : Fin (n i), c i j * ((t - x i)⁻¹) ^ (j.1 + 1)) := by
  rw [clearedCauchyJetPolynomial, eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [eval_finsetSum, Finset.mul_sum]
  rw [← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_prod]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have hne : t - x i ≠ 0 := sub_ne_zero.mpr (ht i)
  simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  rw [pow_sub₀ _ hne (show j.1 + 1 ≤ n i by omega), inv_pow]
  ring

/-- An infinite separated set detects every coefficient of a finite confluent Cauchy-jet form. -/
theorem cauchyJet_coeff_eq_zero_of_infinite
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Infinite κ]
    (x : ι → ℂ) (hx : Function.Injective x) (n : ι → ℕ)
    (t : κ → ℂ) (ht : Function.Injective t) (hsep : ∀ a i, t a ≠ x i)
    (c : (i : ι) → Fin (n i) → ℂ)
    (hzero : ∀ a, ∑ i, ∑ j : Fin (n i),
      c i j * ((t a - x i)⁻¹) ^ (j.1 + 1) = 0) :
    ∀ i j, c i j = 0 := by
  let Q := clearedCauchyJetPolynomial x n c
  have hroot : Set.range t ⊆ {z | Q.IsRoot z} := by
    rintro z ⟨a, rfl⟩
    dsimp [Polynomial.IsRoot, Q]
    rw [eval_clearedCauchyJetPolynomial_eq_mul_sum x n c (t a) (hsep a), hzero a,
      mul_zero]
  have hQ : Q = 0 := Polynomial.eq_zero_of_infinite_isRoot Q
    ((Set.infinite_range_of_injective ht).mono hroot)
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

/-- One Cauchy-jet column indexed by a support point. -/
def cauchyJetColumn
    {ι κ : Type*} (x : ι → ℂ) (n : ι → ℕ) (t : κ → ℂ) (a : κ) :
    (Σ i, Fin (n i)) → ℂ :=
  fun s => ((t a - x s.1)⁻¹) ^ (s.2.1 + 1)

/-- Finite complex mass combinations of the Cauchy-jet columns. -/
def cauchyJetLinearCombination
    {ι κ : Type*} (x : ι → ℂ) (n : ι → ℕ) (t : κ → ℂ) :
    (κ →₀ ℂ) →ₗ[ℂ] ((Σ i, Fin (n i)) → ℂ) :=
  Finsupp.linearCombination ℂ (cauchyJetColumn x n t)

/-- Complex Cauchy masses realize every finite complex jet packet. -/
theorem cauchyJetLinearCombination_surjective
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Infinite κ]
    (x : ι → ℂ) (hx : Function.Injective x) (n : ι → ℕ)
    (t : κ → ℂ) (ht : Function.Injective t) (hsep : ∀ a i, t a ≠ x i) :
    Function.Surjective (cauchyJetLinearCombination x n t) := by
  rw [← LinearMap.dualMap_injective_iff]
  intro φ ψ hφψ
  let c : (i : ι) → Fin (n i) → ℂ := fun i j =>
    φ (Pi.single ⟨i, j⟩ 1) - ψ (Pi.single ⟨i, j⟩ 1)
  have hzero : ∀ a, ∑ i, ∑ j : Fin (n i),
      c i j * ((t a - x i)⁻¹) ^ (j.1 + 1) = 0 := by
    intro a
    have ha := LinearMap.congr_fun hφψ (Finsupp.single a 1)
    change φ ((cauchyJetLinearCombination x n t) (Finsupp.single a 1)) =
      ψ ((cauchyJetLinearCombination x n t) (Finsupp.single a 1)) at ha
    have hcol : (cauchyJetLinearCombination x n t) (Finsupp.single a 1) =
        cauchyJetColumn x n t a := by
      simp [cauchyJetLinearCombination]
    rw [hcol] at ha
    have hexpand (f : (Σ i, Fin (n i)) → ℂ) :
        f = ∑ s, f s • Pi.single s 1 := by
      funext s
      simp [Pi.single_apply]
    rw [hexpand (cauchyJetColumn x n t a)] at ha
    simp only [map_sum, map_smul] at ha
    have ha0 : (∑ s, cauchyJetColumn x n t a s * φ (Pi.single s 1)) -
        (∑ s, cauchyJetColumn x n t a s * ψ (Pi.single s 1)) = 0 := by
      exact sub_eq_zero.mpr (by simpa [smul_eq_mul] using ha)
    rw [← Fintype.sum_sigma (fun s : (Σ i, Fin (n i)) =>
      c s.1 s.2 * ((t a - x s.1)⁻¹) ^ (s.2.1 + 1))]
    calc
      _ = (∑ s, cauchyJetColumn x n t a s * φ (Pi.single s 1)) -
          (∑ s, cauchyJetColumn x n t a s * ψ (Pi.single s 1)) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro s hs
        simp only [c, cauchyJetColumn]
        ring
      _ = 0 := ha0
  have hc := cauchyJet_coeff_eq_zero_of_infinite x hx n t ht hsep c hzero
  apply LinearMap.ext
  intro f
  have hexpand : f = ∑ s, f s • Pi.single s 1 := by
    funext s
    simp [Pi.single_apply]
  rw [hexpand]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro s hs
  rw [show φ (Pi.single s 1) = ψ (Pi.single s 1) by
    exact sub_eq_zero.mp (hc s.1 s.2)]

/-- Finite real mass combinations of Cauchy-jet columns on a real support. -/
def cauchyJetRealLinearCombination
    {ι κ : Type*} (x : ι → ℂ) (n : ι → ℕ) (t : κ → ℝ) :
    (κ →₀ ℝ) →ₗ[ℝ] ((Σ i, Fin (n i)) → ℂ) :=
  Finsupp.linearCombination ℝ
    (cauchyJetColumn x n (fun a => (t a : ℂ)))

/-- **Real Cauchy-jet controllability.** Finitely supported real masses on any infinite injective
real support realize every finite complex jet packet at distinct upper-half-plane nodes. -/
theorem cauchyJetRealLinearCombination_surjective
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Infinite κ]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (t : κ → ℝ) (ht : Function.Injective t) :
    Function.Surjective (cauchyJetRealLinearCombination x n t) := by
  rw [← LinearMap.dualMap_injective_iff]
  intro φ ψ hφψ
  let A : (i : ι) → Fin (n i) → ℝ := fun i j =>
    φ (Pi.single ⟨i, j⟩ 1) - ψ (Pi.single ⟨i, j⟩ 1)
  let B : (i : ι) → Fin (n i) → ℝ := fun i j =>
    φ (Pi.single ⟨i, j⟩ Complex.I) - ψ (Pi.single ⟨i, j⟩ Complex.I)
  let c : (i : ι) → Fin (n i) → ℂ := fun i j =>
    (A i j : ℂ) - Complex.I * (B i j : ℂ)
  have hreal : ∀ a, (∑ i, ∑ j : Fin (n i),
      c i j * (((t a : ℂ) - x i)⁻¹) ^ (j.1 + 1)).re = 0 := by
    intro a
    have ha := LinearMap.congr_fun hφψ (Finsupp.single a 1)
    change φ ((cauchyJetRealLinearCombination x n t) (Finsupp.single a 1)) =
      ψ ((cauchyJetRealLinearCombination x n t) (Finsupp.single a 1)) at ha
    have hcol : (cauchyJetRealLinearCombination x n t) (Finsupp.single a 1) =
        cauchyJetColumn x n (fun a => (t a : ℂ)) a := by
      simp [cauchyJetRealLinearCombination]
    rw [hcol] at ha
    let v := cauchyJetColumn x n (fun a => (t a : ℂ)) a
    have hexpand : v = (∑ s, (v s).re • Pi.single s (1 : ℂ)) +
        ∑ s, (v s).im • Pi.single s Complex.I := by
      funext s
      simp [Pi.single_apply, Complex.re_add_im]
    change φ v = ψ v at ha
    rw [hexpand] at ha
    simp only [map_sum, map_add, map_smul] at ha
    change (∑ s, (v s).re * φ (Pi.single s 1)) +
        (∑ s, (v s).im * φ (Pi.single s Complex.I)) =
      (∑ s, (v s).re * ψ (Pi.single s 1)) +
        (∑ s, (v s).im * ψ (Pi.single s Complex.I)) at ha
    have ha0 : (∑ s, ((v s).re *
          (φ (Pi.single s 1) - ψ (Pi.single s 1)) +
        (v s).im * (φ (Pi.single s Complex.I) - ψ (Pi.single s Complex.I)))) = 0 := by
      rw [Finset.sum_add_distrib]
      calc
        _ = ((∑ s, (v s).re * φ (Pi.single s 1)) +
              ∑ s, (v s).im * φ (Pi.single s Complex.I)) -
            ((∑ s, (v s).re * ψ (Pi.single s 1)) +
              ∑ s, (v s).im * ψ (Pi.single s Complex.I)) := by
          simp only [mul_sub, Finset.sum_sub_distrib]
          ring
        _ = 0 := sub_eq_zero.mpr ha
    rw [Complex.re_sum]
    simp_rw [Complex.re_sum]
    rw [← Fintype.sum_sigma (fun s : (Σ i, Fin (n i)) =>
      (c s.1 s.2 * (((t a : ℂ) - x s.1)⁻¹) ^ (s.2.1 + 1)).re)]
    rw [← ha0]
    apply Finset.sum_congr rfl
    intro s hs
    have hcre : (c s.1 s.2).re = A s.1 s.2 := by
      simp [c, A, B, Complex.mul_re]
    have hcim : (c s.1 s.2).im = -B s.1 s.2 := by
      simp [c, A, B, Complex.mul_im]
    rw [Complex.mul_re, hcre, hcim]
    simp only [A, B, v, cauchyJetColumn]
    ring
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
  have htC : Function.Injective (fun a => (t a : ℂ)) := fun a b hab =>
    ht (Complex.ofReal_injective hab)
  have hsep₂ : ∀ a i, (t a : ℂ) ≠ x₂ i := by
    intro a i h
    rcases i with i | i
    · have him := congrArg Complex.im h
      simp [x₂] at him
      linarith [hupper i]
    · have him := congrArg Complex.im h
      simp [x₂] at him
      linarith [hupper i]
  have hzero₂ : ∀ a, ∑ i, ∑ j : Fin (n₂ i),
      c₂ i j * (((t a : ℂ) - x₂ i)⁻¹) ^ (j.1 + 1) = 0 := by
    intro a
    rw [Fintype.sum_sum_type]
    simp only [c₂, n₂, x₂, Sum.elim_inl, Sum.elim_inr]
    let R : ℂ := ∑ i, ∑ j : Fin (n i),
      c i j * (((t a : ℂ) - x i)⁻¹) ^ (j.1 + 1)
    have hconj : (∑ i, ∑ j : Fin (n i),
        star (c i j) * (((t a : ℂ) - star (x i))⁻¹) ^ (j.1 + 1)) = star R := by
      simp [R]
    change R + (∑ i, ∑ j : Fin (n i),
      star (c i j) * (((t a : ℂ) - star (x i))⁻¹) ^ (j.1 + 1)) = 0
    rw [hconj]
    have hR : R.re = 0 := hreal a
    have hstar : star R = -R := by
      apply Complex.ext
      · simp [hR]
      · simp
    rw [hstar, add_neg_cancel]
  have hc₂ := cauchyJet_coeff_eq_zero_of_infinite x₂ hx₂ n₂
    (fun a => (t a : ℂ)) htC hsep₂ c₂ hzero₂
  have hc : ∀ i j, c i j = 0 := fun i j => hc₂ (Sum.inl i) j
  apply LinearMap.ext
  intro f
  have hexpand : f = (∑ s, (f s).re • Pi.single s (1 : ℂ)) +
      ∑ s, (f s).im • Pi.single s Complex.I := by
    funext s
    simp [Pi.single_apply, Complex.re_add_im]
  rw [hexpand]
  simp only [map_sum, map_add, map_smul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro s hs
  · have hcre := congrArg Complex.re (hc s.1 s.2)
    simp only [c, A, B, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero,
      Complex.zero_re] at hcre
    rw [sub_eq_zero.mp hcre]
  · have hcim := congrArg Complex.im (hc s.1 s.2)
    simp only [c, A, B, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add,
      Complex.zero_im] at hcim
    have hB : φ (Pi.single s Complex.I) - ψ (Pi.single s Complex.I) = 0 := by
      linarith
    rw [sub_eq_zero.mp hB]

/-- Every finitely supported signed mass direction is tangent to the strict positive cone: after
an arbitrarily small positive rescaling, adding it to any pointwise positive base mass preserves
strict positivity at every coordinate. -/
theorem exists_small_positive_finsupp_perturbation
    {κ : Type*} (w : κ → ℝ) (hw : ∀ p, 0 < w p) (a : κ →₀ ℝ)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε < η ∧ ∀ p, 0 < w p + ε * a p := by
  induction a using Finsupp.induction with
  | zero =>
      refine ⟨η / 2, half_pos hη, half_lt_self hη, ?_⟩
      intro p
      simpa using hw p
  | @single_add p b a hp hb ih =>
      obtain ⟨ε, hε, hεη, hpos⟩ := ih
      have hap : a p = 0 := by
        simpa only [Finsupp.mem_support_iff, not_not] using hp
      let δ := min (ε / 2) (w p / (2 * (|b| + 1)))
      have hden : 0 < 2 * (|b| + 1) := by positivity
      have hδ : 0 < δ := by
        apply lt_min (half_pos hε)
        exact div_pos (hw p) hden
      have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
      refine ⟨δ, hδ, hδε.trans hεη, ?_⟩
      intro q
      by_cases hqp : q = p
      · subst q
        simp only [Finsupp.add_apply, Finsupp.single_eq_same, hap, add_zero]
        have hδbound : δ ≤ w p / (2 * (|b| + 1)) := min_le_right _ _
        have hmul : δ * (2 * (|b| + 1)) ≤ w p :=
          (le_div_iff₀ hden).mp hδbound
        nlinarith [abs_nonneg b, neg_abs_le b]
      · simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hqp, zero_add]
        by_cases haq : 0 ≤ a q
        · nlinarith [hw q]
        · have hδε' : δ ≤ ε := hδε.le
          nlinarith [hpos q]

/-- A surjective finite-mass control map has every target direction as an admissible tangent at
every strictly positive base mass.  The lift can be followed for an arbitrarily small positive
time without leaving the positive cone. -/
theorem surjective_finsupp_full_tangent_at_positive
    {κ E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : (κ →₀ ℝ) →ₗ[ℝ] E) (hL : Function.Surjective L)
    (w : κ → ℝ) (hw : ∀ p, 0 < w p) (y : E) {η : ℝ} (hη : 0 < η) :
    ∃ a : κ →₀ ℝ, ∃ ε : ℝ,
      L a = y ∧ 0 < ε ∧ ε < η ∧ ∀ p, 0 < w p + ε * a p := by
  obtain ⟨a, ha⟩ := hL y
  obtain ⟨ε, hε, hεη, hpos⟩ :=
    exists_small_positive_finsupp_perturbation w hw a hη
  exact ⟨a, ε, ha, hε, hεη, hpos⟩

end

end GaloisForLFunctions.HTGeometry
