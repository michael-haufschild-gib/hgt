import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheTwoHalvesOfAWindowOfRatioFourDoNotGlueThroughAProductOfCharges
import GaloisForLFunctions.HTGeometry.KernelOfDimensionDrop
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheTowerDeficitChangesSignBetweenFortyThreeAndFortySeven

/-!
# The binding of the two halves of a window of ratio four has rank proportional to the block size

Two forms `A`, `B` coupled by `K` are compared with a model coupling `M`. For weights `t_ij > 0`,

  `2 |K_ij − M_ij| |x_i y_j| ≤ |K_ij − M_ij| (t_ij x_i² + y_j² / t_ij)`,

so the coupled form is at least the form coupled by `M` of the two forms with potentials lowered
by `Σ_j |K_ij − M_ij| t_ij` and `Σ_i |K_ij − M_ij| / t_ij` (`bilin_lowered_le_coupled`,
`hermNegIndex_coupled_le_lowered`). A lowered model with one negative square would count one
bound state of the union; the product of two charges is the model of rank one.

For the halves `(2H, 4H]` and `(4H, 8H]` of a window of ratio four no model of small rank does
this. If `M = Σ_{k<r} p_k ⊗ q_k` and `600 (r + 1) ≤ H`, then for every choice of the weights one
of the two lowered halves has two negative squares (`two_le_hermNegIndex_lowered_half_of_rank`),
and so has the lowered model (`two_le_hermNegIndex_lowered_model_of_rank`). A coupling that
carries the binding of the two halves has rank at least `H / 600`: the rank grows with the block
size.

The proof has three steps.

* On the packets constant on its two quarters, a lowered window with at most one negative
  square bounds the lowerings of its quarters
  (`mul_le_sq_of_hermNegIndex_lowered_le_one`). By the Cauchy–Schwarz inequality the lowerings
  of a quarter of `(2H, 4H]` and of the quarter of `(4H, 8H]` above it bound the distance
  `Σ |K − M|` between them (`sq_sum_abs_le_lowering`). With the closed forms of the neutral
  part on the quarters, for one of the two pairs of quarters the distance is at most
  `(109/200) H`.
* Between a quarter and the quarter above it the couplings are the jets, at most `2/H`, and
  the contacts of the floor map of `2`: the block `a` meets `2a` and `2a + 1` with the weight
  `Λ(2)/2`. Summed over the two preimages the couplings are `log 2` times the identity, up to
  the jets (`abs_blockWeight_pair_sub_le`).
* A matrix of rank `r` on `n` indices is at distance at least `λ (n − r)` from `λ` times the
  identity, in the sum of the absolute values of the entries
  (`mul_card_sub_le_sum_abs_sub_diagonal`): the rows at distance below `λ` are diagonally
  dominant, hence independent. On the residue classes modulo `64`, where the jets are sparse,
  this gives `log 2 · (H − 64 r) ≤ Σ |K − M| + H/16 + 4` (`log_two_mul_sub_le_quarter`).
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Lowering the potentials by the distance from a model coupling -/

section Lowering

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- The lowering of the first potential: the distance of the couplings from the model, with the
weights `t`. -/
def loweringLeft (K M t : ι₁ → ι₂ → ℝ) (i : ι₁) : ℝ := ∑ j, |K i j - M i j| * t i j

/-- The lowering of the second potential: the distance of the couplings from the model, with
the weights `1/t`. -/
def loweringRight (K M t : ι₁ → ι₂ → ℝ) (j : ι₂) : ℝ := ∑ i, |K i j - M i j| / t i j

omit [Fintype ι₁] in
theorem loweringLeft_nonneg (K M : ι₁ → ι₂ → ℝ) {t : ι₁ → ι₂ → ℝ} (ht : ∀ i j, 0 < t i j)
    (i : ι₁) : 0 ≤ loweringLeft K M t i :=
  Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (ht i j).le

omit [Fintype ι₂] in
theorem loweringRight_nonneg (K M : ι₁ → ι₂ → ℝ) {t : ι₁ → ι₂ → ℝ} (ht : ∀ i j, 0 < t i j)
    (j : ι₂) : 0 ≤ loweringRight K M t j :=
  Finset.sum_nonneg fun i _ => div_nonneg (abs_nonneg _) (ht i j).le

/-- The weighted inequality of the means for one coupling. -/
theorem two_mul_mul_le_weighted (F x y : ℝ) {t : ℝ} (ht : 0 < t) :
    2 * (x * y * F) ≤ |F| * t * x ^ 2 + |F| / t * y ^ 2 := by
  have hts : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  have key : 2 * |x * y| ≤ t * x ^ 2 + t⁻¹ * y ^ 2 := by
    have h1 : 0 ≤ (t * |x| - |y|) ^ 2 := sq_nonneg _
    have h2 : t * (t * x ^ 2 + t⁻¹ * y ^ 2) = t ^ 2 * x ^ 2 + y ^ 2 := by
      linear_combination y ^ 2 * hts
    have h6 : t * (2 * |x * y|) ≤ t * (t * x ^ 2 + t⁻¹ * y ^ 2) := by
      rw [h2, abs_mul, ← sq_abs x, ← sq_abs y]
      nlinarith [h1]
    exact le_of_mul_le_mul_left h6 ht
  have hF : x * y * F ≤ |x * y| * |F| := (le_abs_self _).trans (abs_mul _ _).le
  have hfin := mul_le_mul_of_nonneg_left key (abs_nonneg F)
  have e3 : |F| * (t * x ^ 2 + t⁻¹ * y ^ 2) = |F| * t * x ^ 2 + |F| / t * y ^ 2 := by
    rw [div_eq_mul_inv]
    ring
  linarith

/-- The couplings beyond the model are at most the two lowerings. -/
theorem two_mul_sum_cross_le_lowering (K M : ι₁ → ι₂ → ℝ) {t : ι₁ → ι₂ → ℝ}
    (ht : ∀ i j, 0 < t i j) (x : ι₁ → ℝ) (y : ι₂ → ℝ) :
    2 * ∑ i, ∑ j, x i * y j * (K i j - M i j) ≤
      ∑ i, loweringLeft K M t i * x i ^ 2 + ∑ j, loweringRight K M t j * y j ^ 2 := by
  have h1 : ∑ i, loweringLeft K M t i * x i ^ 2 =
      ∑ i, ∑ j, |K i j - M i j| * t i j * x i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [loweringLeft, Finset.sum_mul]
  have h2 : ∑ j, loweringRight K M t j * y j ^ 2 =
      ∑ i, ∑ j, |K i j - M i j| / t i j * y j ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [loweringRight, Finset.sum_mul]
  rw [h1, h2, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => two_mul_mul_le_weighted _ _ _ (ht i j)

/-- A sum over the image of an injective map is at most the whole sum. -/
theorem sum_comp_le_of_injective {κ ι : Type*} [Fintype κ] [Fintype ι] (g : κ → ι)
    (hg : Function.Injective g) (h : ι → ℝ) (hh : ∀ x, 0 ≤ h x) : ∑ j, h (g j) ≤ ∑ x, h x := by
  classical
  rw [← Finset.sum_image (s := univ) (g := g) (f := h) fun a _ b _ hab => hg hab]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => hh j

/-- The Cauchy–Schwarz inequality for the weights `t` and `1/t`. -/
theorem sq_sum_le_sum_mul_sum_div {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂] (F t : κ₁ → κ₂ → ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (ht : ∀ i j, 0 < t i j) :
    (∑ i, ∑ j, F i j) ^ 2 ≤ (∑ i, ∑ j, F i j * t i j) * ∑ i, ∑ j, F i j / t i j := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset (κ₁ × κ₂))
    (r := fun x => F x.1 x.2) (f := fun x => F x.1 x.2 * t x.1 x.2)
    (g := fun x => F x.1 x.2 / t x.1 x.2)
    (fun x _ => mul_nonneg (hF _ _) (ht _ _).le) (fun x _ => div_nonneg (hF _ _) (ht _ _).le)
    (fun x _ => le_of_eq (by
      have := (ht x.1 x.2).ne'
      field_simp))
  rwa [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at h

/-- **The distance between two families of blocks is bounded by their lowerings**: the square
of `Σ |K − M|` over a rectangle is at most the product of the lowerings of its rows and of its
columns. -/
theorem sq_sum_abs_le_lowering {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂] (K M : ι₁ → ι₂ → ℝ)
    {t : ι₁ → ι₂ → ℝ} (ht : ∀ i j, 0 < t i j) (f : κ₁ → ι₁) (g : κ₂ → ι₂)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    (∑ i, ∑ j, |K (f i) (g j) - M (f i) (g j)|) ^ 2 ≤
      (∑ i, loweringLeft K M t (f i)) * ∑ j, loweringRight K M t (g j) := by
  have h := sq_sum_le_sum_mul_sum_div (fun i j => |K (f i) (g j) - M (f i) (g j)|)
    (fun i j => t (f i) (g j)) (fun _ _ => abs_nonneg _) fun _ _ => ht _ _
  have hX : ∑ i, ∑ j, |K (f i) (g j) - M (f i) (g j)| * t (f i) (g j) ≤
      ∑ i, loweringLeft K M t (f i) :=
    Finset.sum_le_sum fun i _ => by
      rw [loweringLeft]
      exact sum_comp_le_of_injective g hg (fun j => |K (f i) j - M (f i) j| * t (f i) j)
        fun j => mul_nonneg (abs_nonneg _) (ht _ _).le
  have hY : ∑ i, ∑ j, |K (f i) (g j) - M (f i) (g j)| / t (f i) (g j) ≤
      ∑ j, loweringRight K M t (g j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun j _ => by
      rw [loweringRight]
      exact sum_comp_le_of_injective f hf (fun i => |K i (g j) - M i (g j)| / t i (g j))
        fun i => div_nonneg (abs_nonneg _) (ht _ _).le
  exact h.trans (mul_le_mul hX hY
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      div_nonneg (abs_nonneg _) (ht _ _).le)
    (Finset.sum_nonneg fun i _ => loweringLeft_nonneg K M ht _))

variable [DecidableEq ι₁] [DecidableEq ι₂]

/-- **The coupled form is at least the lowered model of any coupling**, for all weights. -/
theorem bilin_lowered_le_coupled (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ) (K M : ι₁ → ι₂ → ℝ)
    {t : ι₁ → ι₂ → ℝ} (ht : ∀ i j, 0 < t i j) (w : ι₁ ⊕ ι₂ → ℝ) :
    bilin (coupled (A - diagonal (loweringLeft K M t)) (B - diagonal (loweringRight K M t)) M)
        w w ≤ bilin (coupled A B K) w w := by
  have h := two_mul_sum_cross_le_lowering K M ht (fun i => w (Sum.inl i)) fun j => w (Sum.inr j)
  have hsplit : ∑ i, ∑ j, w (Sum.inl i) * w (Sum.inr j) * (K i j - M i j) =
      ∑ i, ∑ j, w (Sum.inl i) * w (Sum.inr j) * K i j -
        ∑ i, ∑ j, w (Sum.inl i) * w (Sum.inr j) * M i j := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hsplit] at h
  rw [bilin_coupled, bilin_coupled, bilin_sub_diagonal, bilin_sub_diagonal]
  linarith

/-- **The coupled form has at most the negative squares of the lowered model of any
coupling.** -/
theorem hermNegIndex_coupled_le_lowered (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ)
    (K M : ι₁ → ι₂ → ℝ) {t : ι₁ → ι₂ → ℝ} (ht : ∀ i j, 0 < t i j) :
    hermNegIndex ((coupled A B K).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) ≤
      hermNegIndex ((coupled (A - diagonal (loweringLeft K M t))
        (B - diagonal (loweringRight K M t)) M).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) :=
  HeckeKreinToeplitz.hermNegIndex_le_of_hermQuad_le _ _ fun c => by
    rw [hermQuad_map_eq_bilin, hermQuad_map_eq_bilin]
    exact add_le_add (bilin_lowered_le_coupled A B K M ht _)
      (bilin_lowered_le_coupled A B K M ht _)

/-- A coupled form has at least the negative squares of its first form. -/
theorem hermNegIndex_left_le_coupled (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ)
    (K : ι₁ → ι₂ → ℝ) :
    hermNegIndex (A.map (↑) : Matrix ι₁ ι₁ ℂ) ≤
      hermNegIndex ((coupled A B K).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) :=
  HeckeKreinToeplitz.hermNegIndex_submatrix_le
    ((coupled A B K).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) Sum.inl

/-- A coupled form has at least the negative squares of its second form. -/
theorem hermNegIndex_right_le_coupled (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ)
    (K : ι₁ → ι₂ → ℝ) :
    hermNegIndex (B.map (↑) : Matrix ι₂ ι₂ ℂ) ≤
      hermNegIndex ((coupled A B K).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) :=
  HeckeKreinToeplitz.hermNegIndex_submatrix_le
    ((coupled A B K).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) Sum.inr

end Lowering

/-- **The lowered models of two adjacent windows.** For every model coupling and all weights,
the union holds at most the bound states of the two windows coupled by the model, with
potentials lowered by the distance of the couplings from the model. -/
theorem hermNegIndex_neutralWindow_add_le_lowered (Q R J₁ J₂ : ℕ) (M : Fin J₁ → Fin J₂ → ℝ)
    {t : Fin J₁ → Fin J₂ → ℝ} (ht : ∀ i j, 0 < t i j) :
    hermNegIndex ((neutralWindow Q R (J₁ + J₂)).map (↑) : Matrix (Fin (J₁ + J₂)) _ ℂ) ≤
      hermNegIndex ((coupled
        (neutralWindow Q R J₁ - diagonal (loweringLeft
          (fun (i : Fin J₁) (j : Fin J₂) => blockWeight Q (R + i) (R + J₁ + j)) M t))
        (neutralWindow Q (R + J₁) J₂ - diagonal (loweringRight
          (fun (i : Fin J₁) (j : Fin J₂) => blockWeight Q (R + i) (R + J₁ + j)) M t))
        M).map (↑) : Matrix (Fin J₁ ⊕ Fin J₂) (Fin J₁ ⊕ Fin J₂) ℂ) := by
  rw [hermNegIndex_neutralWindow_add]
  exact hermNegIndex_coupled_le_lowered _ _ _ M ht

/-! ### A matrix of small rank is far from a multiple of the identity -/

section Rank

/-- A matrix of rank `r` has at most `r` diagonally dominant rows: on a set of indices on which
every row is at distance below `λ` from `λ` times the identity, the rows are independent. -/
theorem card_le_of_rank_of_diagonally_dominant {κ : Type*} [DecidableEq κ] {r : ℕ}
    (T : Finset κ) (D : κ → κ → ℝ) (p q : κ → Fin r → ℝ)
    (hD : ∀ i ∈ T, ∀ j ∈ T, D i j = ∑ k, p i k * q j k) {lam : ℝ}
    (hdom : ∀ i ∈ T, ∑ j ∈ T, |D i j - if i = j then lam else 0| < lam) : T.card ≤ r := by
  by_contra hcon
  -- a nonzero vector on `T` killed by the `r` functionals `q`
  obtain ⟨y, hy0, hy⟩ := exists_ne_zero_forall_apply_eq_zero_of_finrank_lt
    (K := ℝ) (V := (T → ℝ))
    (fun k : Fin r => ∑ j : T, (q j k) • (LinearMap.proj j : (T → ℝ) →ₗ[ℝ] ℝ))
    (by
      rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
      exact not_le.mp hcon)
  have hy' : ∀ k : Fin r, ∑ j : T, q j k * y j = 0 := fun k => by
    have h := hy k
    simpa [LinearMap.sum_apply] using h
  -- it is killed by the matrix
  have hDy : ∀ i : T, ∑ j : T, D i j * y j = 0 := fun i => by
    have h1 : ∀ j : T, D i j * y j = ∑ k, p i k * (q j k * y j) := fun j => by
      rw [hD i i.2 j j.2, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Finset.mul_sum, hy' k, mul_zero]
  -- the row of its largest coordinate is not dominant
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset T) (fun i => |y i|)
    ⟨⟨x, hx⟩, Finset.mem_univ _⟩
  have hpos : 0 < |y i₀| := by
    by_contra h0
    refine hy0 (funext fun i => ?_)
    have h2 : |y i| ≤ 0 := (hmax i (Finset.mem_univ _)).trans (not_lt.mp h0)
    exact abs_eq_zero.mp (le_antisymm h2 (abs_nonneg _))
  have hsplit : ∑ j : T, D i₀ j * y j = lam * y i₀ +
      ∑ j : T, (D i₀ j - if (i₀ : κ) = j then lam else 0) * y j := by
    have h1 : ∀ j : T, D i₀ j * y j = (if (i₀ : κ) = j then lam else 0) * y j +
        (D i₀ j - if (i₀ : κ) = j then lam else 0) * y j := fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single i₀]
    · rw [if_pos rfl]
    · intro j _ hj
      rw [if_neg fun h => hj (Subtype.ext h.symm), zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
  have hbound : |∑ j : T, (D i₀ j - if (i₀ : κ) = j then lam else 0) * y j| ≤
      (∑ j : T, |D i₀ j - if (i₀ : κ) = j then lam else 0|) * |y i₀| := by
    calc |∑ j : T, (D i₀ j - if (i₀ : κ) = j then lam else 0) * y j|
        ≤ ∑ j : T, |(D i₀ j - if (i₀ : κ) = j then lam else 0) * y j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : T, |D i₀ j - if (i₀ : κ) = j then lam else 0| * |y j| := by
          simp only [abs_mul]
      _ ≤ ∑ j : T, |D i₀ j - if (i₀ : κ) = j then lam else 0| * |y i₀| :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hmax j (Finset.mem_univ _)) (abs_nonneg _)
      _ = _ := by rw [Finset.sum_mul]
  have hrow : ∑ j : T, |D i₀ j - if (i₀ : κ) = j then lam else 0| < lam := by
    have h := hdom i₀ i₀.2
    rwa [← Finset.sum_coe_sort T (fun j => |D i₀ j - if (i₀ : κ) = j then lam else 0|)] at h
  have hlam : 0 < lam := lt_of_le_of_lt (Finset.sum_nonneg fun _ _ => abs_nonneg _) hrow
  have habs : lam * |y i₀| = |∑ j : T, (D i₀ j - if (i₀ : κ) = j then lam else 0) * y j| := by
    have h1 : lam * y i₀ = -∑ j : T, (D i₀ j - if (i₀ : κ) = j then lam else 0) * y j := by
      linarith [hDy i₀, hsplit]
    rw [← abs_of_pos hlam, ← abs_mul, abs_of_pos hlam, h1, abs_neg]
  have := mul_lt_mul_of_pos_right hrow hpos
  linarith

/-- **A matrix of rank `r` is far from a multiple of the identity**: on `n` indices its distance
from `λ` times the identity, in the sum of the absolute values of the entries, is at least
`λ (n − r)`. -/
theorem mul_card_sub_le_sum_abs_sub_diagonal {κ : Type*} [DecidableEq κ] {r : ℕ} (S : Finset κ)
    (D : κ → κ → ℝ) (p q : κ → Fin r → ℝ) (hD : ∀ i ∈ S, ∀ j ∈ S, D i j = ∑ k, p i k * q j k)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    lam * ((S.card : ℝ) - r) ≤ ∑ i ∈ S, ∑ j ∈ S, |D i j - if i = j then lam else 0| := by
  classical
  -- the dominant rows
  obtain ⟨T, hT⟩ : ∃ T : Finset κ,
      T = S.filter fun i => ∑ j ∈ S, |D i j - if i = j then lam else 0| < lam := ⟨_, rfl⟩
  have hTS : T ⊆ S := by
    rw [hT]
    exact Finset.filter_subset _ _
  have hcard : T.card ≤ r :=
    card_le_of_rank_of_diagonally_dominant T D p q
      (fun i hi j hj => hD i (hTS hi) j (hTS hj)) fun i hi => by
        rw [hT] at hi
        exact lt_of_le_of_lt
          (Finset.sum_le_sum_of_subset_of_nonneg hTS fun _ _ _ => abs_nonneg _)
          (Finset.mem_filter.mp hi).2
  -- every other row is at distance at least `λ`
  have h1 : ∑ _i ∈ S \ T, lam ≤ ∑ i ∈ S, ∑ j ∈ S, |D i j - if i = j then lam else 0| :=
    calc ∑ _i ∈ S \ T, lam ≤ ∑ i ∈ S \ T, ∑ j ∈ S, |D i j - if i = j then lam else 0| :=
          Finset.sum_le_sum fun i hi => by
            have hi' := Finset.mem_sdiff.mp hi
            by_contra hlt
            exact hi'.2 (by rw [hT]; exact Finset.mem_filter.mpr ⟨hi'.1, not_le.mp hlt⟩)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ =>
          Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : ((S \ T).card : ℝ) + T.card = S.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hTS
  have h3 : (T.card : ℝ) ≤ r := by exact_mod_cast hcard
  have h4 : lam * ((S.card : ℝ) - r) ≤ lam * ((S \ T).card : ℝ) :=
    mul_le_mul_of_nonneg_left (by linarith) hlam
  linarith

/-- The distance from a multiple of the identity, counted on the pairs of indices in one
residue class modulo `s`: at least `λ (H − s r)` for a matrix of rank `r`. -/
theorem mul_sub_le_sum_abs_on_residue_classes {H r s : ℕ} (hs : 0 < s) (D : Fin H → Fin H → ℝ)
    (p q : Fin H → Fin r → ℝ) (hD : ∀ i j, D i j = ∑ k, p i k * q j k) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    lam * ((H : ℝ) - s * r) ≤ ∑ i : Fin H, ∑ j : Fin H,
      if (i : ℕ) % s = (j : ℕ) % s then |D i j - if i = j then lam else 0| else 0 := by
  classical
  have hclass : ∀ ρ ∈ range s,
      lam * (((univ.filter fun i : Fin H => (i : ℕ) % s = ρ).card : ℝ) - r) ≤
        ∑ i ∈ univ.filter (fun i : Fin H => (i : ℕ) % s = ρ),
          ∑ j ∈ univ.filter (fun j : Fin H => (j : ℕ) % s = ρ),
            |D i j - if i = j then lam else 0| := fun ρ _ =>
    mul_card_sub_le_sum_abs_sub_diagonal _ D p q (fun i _ j _ => hD i j) hlam
  have hsum := Finset.sum_le_sum hclass
  have hL : ∑ ρ ∈ range s,
      lam * (((univ.filter fun i : Fin H => (i : ℕ) % s = ρ).card : ℝ) - r) =
        lam * ((H : ℝ) - s * r) := by
    have hcard : ∑ ρ ∈ range s, (univ.filter fun i : Fin H => (i : ℕ) % s = ρ).card = H := by
      rw [← Finset.card_eq_sum_card_fiberwise
        (fun i _ => Finset.mem_range.mpr (Nat.mod_lt _ hs)), Finset.card_univ, Fintype.card_fin]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Nat.cast_sum, hcard]
  have hR : ∑ ρ ∈ range s, ∑ i ∈ univ.filter (fun i : Fin H => (i : ℕ) % s = ρ),
      ∑ j ∈ univ.filter (fun j : Fin H => (j : ℕ) % s = ρ),
        |D i j - if i = j then lam else 0| =
      ∑ i : Fin H, ∑ j : Fin H,
        if (i : ℕ) % s = (j : ℕ) % s then |D i j - if i = j then lam else 0| else 0 := by
    have h1 : ∀ ρ ∈ range s, ∑ i ∈ univ.filter (fun i : Fin H => (i : ℕ) % s = ρ),
        ∑ j ∈ univ.filter (fun j : Fin H => (j : ℕ) % s = ρ),
          |D i j - if i = j then lam else 0| =
        ∑ i ∈ univ.filter (fun i : Fin H => (i : ℕ) % s = ρ), ∑ j : Fin H,
          if (i : ℕ) % s = (j : ℕ) % s then |D i j - if i = j then lam else 0| else 0 :=
      fun ρ _ => Finset.sum_congr rfl fun i hi => by
        rw [Finset.sum_filter]
        have hi' := (Finset.mem_filter.mp hi).2
        exact Finset.sum_congr rfl fun j _ => if_congr (by rw [hi']; exact eq_comm) rfl rfl
    rw [Finset.sum_congr rfl h1]
    exact Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_range.mpr (Nat.mod_lt _ hs)) _
  rw [hL, hR] at hsum
  exact hsum

/-- A residue class modulo `s` has at most `H/s + 1` elements below `H`. -/
theorem card_filter_mod_le {H s : ℕ} (c : ℕ) :
    (univ.filter fun j : Fin H => (j : ℕ) % s = c).card ≤ H / s + 1 := by
  have h := Finset.card_le_card_of_injOn (s := univ.filter fun j : Fin H => (j : ℕ) % s = c)
    (t := range (H / s + 1)) (fun j => (j : ℕ) / s)
    (fun j _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right j.2.le)))
    (fun j hj j' hj' hjj => by
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hj')).2
      have h3 := Nat.div_add_mod (j : ℕ) s
      have h4 := Nat.div_add_mod (j' : ℕ) s
      have hjj' : (j : ℕ) / s = (j' : ℕ) / s := hjj
      exact Fin.ext (by rw [← h3, ← h4, h1, h2, hjj']))
  rwa [Finset.card_range] at h

/-- The even and the odd indices are part of all indices. -/
theorem sum_even_add_odd_le {H : ℕ} (h : Fin (H + H) → ℝ) (hh : ∀ j, 0 ≤ h j)
    (e₀ e₁ : Fin H → Fin (H + H)) (h₀ : ∀ j, (e₀ j : ℕ) = 2 * j)
    (h₁ : ∀ j, (e₁ j : ℕ) = 2 * j + 1) :
    ∑ j, (h (e₀ j) + h (e₁ j)) ≤ ∑ j, h j := by
  classical
  have i₀ : Function.Injective e₀ := fun a b hab => Fin.ext (by
    have h := congrArg Fin.val hab
    rw [h₀, h₀] at h
    omega)
  have i₁ : Function.Injective e₁ := fun a b hab => Fin.ext (by
    have h := congrArg Fin.val hab
    rw [h₁, h₁] at h
    omega)
  have hd : Disjoint (univ.image e₀) (univ.image e₁) := by
    rw [Finset.disjoint_left]
    intro x hx₀ hx₁
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx₀
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hx₁
    have h := congrArg Fin.val hb
    rw [h₀, h₁] at h
    omega
  calc ∑ j, (h (e₀ j) + h (e₁ j)) = ∑ x ∈ univ.image e₀ ∪ univ.image e₁, h x := by
        rw [Finset.sum_union hd, Finset.sum_image fun a _ b _ hab => i₀ hab,
          Finset.sum_image fun a _ b _ hab => i₁ hab, Finset.sum_add_distrib]
    _ ≤ ∑ j, h j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => hh j

end Rank

/-! ### Two lowered windows that both have one negative square -/

/-- If two pairs of lowerings `X_q`, `Y_q` satisfy the criteria of a window and of its double,
and bound two distances by `G_q² ≤ X_q Y_q`, then one of the distances is small. -/
theorem sq_le_or_sq_le_of_two_products {a₁ a₂ c e X₁ X₂ Y₁ Y₂ G₁ G₂ : ℝ} (ha₁ : 0 ≤ a₁)
    (ha₂ : 0 ≤ a₂) (he : 0 < e) (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂)
    (hL : (a₁ + X₁) * (a₂ + X₂) ≤ c ^ 2) (hU : (2 * a₁ + Y₁) * (2 * a₂ + Y₂) ≤ 4 * c ^ 2)
    (h1 : G₁ ^ 2 ≤ X₁ * Y₁) (h2 : G₂ ^ 2 ≤ X₂ * Y₂) (hc : c ^ 2 < (a₁ + e) * (a₂ + e)) :
    G₁ ^ 2 ≤ 2 * e ^ 2 ∨ G₂ ^ 2 ≤ 2 * e ^ 2 := by
  by_contra hcon
  obtain ⟨g1, g2⟩ := not_or.mp hcon
  -- the inequality of the means on each pair
  have key : ∀ {a X Y : ℝ}, 0 ≤ a → 0 ≤ X → 0 ≤ Y → 2 * e ^ 2 < X * Y →
      (a + e) ^ 2 ≤ (a + X) * (a + Y / 2) := by
    intro a X Y ha hX hY hXY
    have hs : 2 * e < X + Y / 2 := by
      by_contra hlt
      nlinarith [sq_nonneg (X - Y / 2), mul_nonneg hX hY, not_lt.mp hlt]
    nlinarith
  have p1 := key ha₁ hX₁ hY₁ (lt_of_lt_of_le (not_le.mp g1) h1)
  have p2 := key ha₂ hX₂ hY₂ (lt_of_lt_of_le (not_le.mp g2) h2)
  have hU' : (a₁ + Y₁ / 2) * (a₂ + Y₂ / 2) ≤ c ^ 2 := by nlinarith
  have hprod : (a₁ + e) ^ 2 * (a₂ + e) ^ 2 ≤
      (a₁ + X₁) * (a₁ + Y₁ / 2) * ((a₂ + X₂) * (a₂ + Y₂ / 2)) :=
    mul_le_mul p1 p2 (sq_nonneg _) (by positivity)
  have hprod2 : (a₁ + X₁) * (a₂ + X₂) * ((a₁ + Y₁ / 2) * (a₂ + Y₂ / 2)) ≤ c ^ 2 * c ^ 2 :=
    mul_le_mul hL hU' (by positivity) (sq_nonneg _)
  have hsq := mul_self_lt_mul_self (sq_nonneg c) hc
  nlinarith

/-- A model at distance `ε` from two couplings whose sum is at distance `ε'` from `δ`. -/
theorem abs_sub_le_of_pair {k₀ k₁ m₀ m₁ δ ε : ℝ} (h : |k₀ + k₁ - δ| ≤ ε) :
    |m₀ + m₁ - δ| ≤ |k₀ - m₀| + |k₁ - m₁| + ε := by
  have h1 := abs_le.mp h
  have a0 := le_abs_self (k₀ - m₀)
  have a0' := neg_abs_le (k₀ - m₀)
  have a1 := le_abs_self (k₁ - m₁)
  have a1' := neg_abs_le (k₁ - m₁)
  rw [abs_le]
  constructor <;> linarith

theorem log_three_add_lt_log_pi : Real.log 3 + 7 / 157 < Real.log Real.pi := by
  have h1 : Real.log (157 / 50) < Real.log Real.pi :=
    Real.log_lt_log (by norm_num) (by have := Real.pi_gt_d2; linarith)
  have h2 : Real.log (157 / 50 : ℝ) = Real.log 3 + Real.log (157 / 150) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h3 : 1 - (157 / 150 : ℝ)⁻¹ ≤ Real.log (157 / 150) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have h4 : (1 : ℝ) - (157 / 150)⁻¹ = 7 / 157 := by norm_num
  linarith

/-! ### A lowered window on the plane of its two halves -/

/-- The form of a window with lowered potential on the packets constant on its two halves. -/
theorem bilin_lowered_window_two_steps (Q R H : ℕ) (d : Fin (H + H) → ℝ) (s t : ℝ) :
    bilin (neutralWindow Q R (H + H) - diagonal d)
        (fun i : Fin (H + H) =>
          s * (if (i : ℕ) < H then (1 : ℝ) else 0) + t * (if (i : ℕ) < H then (0 : ℝ) else 1))
        (fun i : Fin (H + H) =>
          s * (if (i : ℕ) < H then (1 : ℝ) else 0) + t * (if (i : ℕ) < H then (0 : ℝ) else 1)) =
      ((∑ j ∈ range H, ∑ l ∈ range H, neutralBlock Q (R + j) (R + l)) -
          ∑ i : Fin H, d (Fin.castAdd H i)) * s ^ 2 +
        2 * (∑ j ∈ range H, ∑ l ∈ range H, neutralBlock Q (R + j) (R + (H + l))) * s * t +
        ((∑ j ∈ range H, ∑ l ∈ range H, neutralBlock Q (R + (H + j)) (R + (H + l))) -
          ∑ i : Fin H, d (Fin.natAdd H i)) * t ^ 2 := by
  have hx : (fun i : Fin (H + H) =>
      s * (if (i : ℕ) < H then (1 : ℝ) else 0) + t * (if (i : ℕ) < H then (0 : ℝ) else 1)) =
        fun i : Fin (H + H) => if (i : ℕ) < H then s else t := by
    funext i
    split_ifs <;> ring
  have hN : bilin (neutralWindow Q R (H + H))
      (fun i : Fin (H + H) => if (i : ℕ) < H then s else t)
      (fun i : Fin (H + H) => if (i : ℕ) < H then s else t) =
      (∑ j ∈ range H, ∑ l ∈ range H, neutralBlock Q (R + j) (R + l)) * s ^ 2 +
        2 * (∑ j ∈ range H, ∑ l ∈ range H, neutralBlock Q (R + j) (R + (H + l))) * s * t +
        (∑ j ∈ range H, ∑ l ∈ range H, neutralBlock Q (R + (H + j)) (R + (H + l))) * t ^ 2 :=
    (sum_fin_windowMatrix_coe (neutralBlock Q) R (H + H) (fun n => if n < H then s else t)).trans
      (sum_two_steps (fun j l => neutralBlock Q (R + j) (R + l))
        (fun j l => neutralBlock_comm Q _ _) H s t)
  have hD : ∑ i : Fin (H + H), d i * (if (i : ℕ) < H then s else t) ^ 2 =
      (∑ i : Fin H, d (Fin.castAdd H i)) * s ^ 2 + (∑ i : Fin H, d (Fin.natAdd H i)) * t ^ 2 := by
    rw [Fin.sum_univ_add, Finset.sum_mul, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [if_pos (show ((Fin.castAdd H i : Fin (H + H)) : ℕ) < H by
        rw [Fin.val_castAdd]
        exact i.2)]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [if_neg (show ¬((Fin.natAdd H i : Fin (H + H)) : ℕ) < H by
        rw [Fin.val_natAdd]
        omega)]
  rw [hx, bilin_sub_diagonal]
  show bilin (neutralWindow Q R (H + H))
      (fun i : Fin (H + H) => if (i : ℕ) < H then s else t)
      (fun i : Fin (H + H) => if (i : ℕ) < H then s else t) -
      ∑ i : Fin (H + H), d i * (if (i : ℕ) < H then s else t) ^ 2 = _
  rw [hN, hD]
  ring

/-- **A lowered window with at most one negative square bounds the lowerings of its halves.**
With `n₁`, `n₂`, `c` the neutral part on the constant packets of the two halves and their
pairing, and `E₁`, `E₂` the lowerings of the halves: `(n₁ − E₁)(n₂ − E₂) ≤ c²`. -/
theorem mul_le_sq_of_hermNegIndex_lowered_le_one {Q R H : ℕ} {d : Fin (H + H) → ℝ}
    {n₁ n₂ c : ℝ}
    (h₁ : ∑ j ∈ range H, ∑ l ∈ range H, neutralBlock Q (R + j) (R + l) = n₁)
    (hc : ∑ j ∈ range H, ∑ l ∈ range H, neutralBlock Q (R + j) (R + (H + l)) = c)
    (h₂ : ∑ j ∈ range H, ∑ l ∈ range H, neutralBlock Q (R + (H + j)) (R + (H + l)) = n₂)
    (hneg : n₁ - ∑ i : Fin H, d (Fin.castAdd H i) < 0)
    (hidx : hermNegIndex ((neutralWindow Q R (H + H) - diagonal d).map (↑) :
      Matrix (Fin (H + H)) (Fin (H + H)) ℂ) ≤ 1) :
    (n₁ - ∑ i : Fin H, d (Fin.castAdd H i)) * (n₂ - ∑ i : Fin H, d (Fin.natAdd H i)) ≤
      c ^ 2 := by
  by_contra hcon
  have h2 := two_le_hermNegIndex_of_two_vectors (neutralWindow Q R (H + H) - diagonal d)
    (fun i : Fin (H + H) => if (i : ℕ) < H then (1 : ℝ) else 0)
    (fun i : Fin (H + H) => if (i : ℕ) < H then (0 : ℝ) else 1)
    (α := n₁ - ∑ i : Fin H, d (Fin.castAdd H i)) (γ := n₂ - ∑ i : Fin H, d (Fin.natAdd H i))
    (c := c)
    (fun s t => (bilin_lowered_window_two_steps Q R H d s t).le.trans
      (le_of_eq (by rw [h₁, hc, h₂])))
    hneg (not_le.mp hcon)
  omega

/-! ### The couplings of a quarter with the quarter above it -/

/-- Between two blocks of ratio below three the only contact is the floor map of `2`. -/
theorem floorContact_eq_of_lt_three_mul {Q a b : ℕ} (hQ : 2 ≤ Q) (hb : b < 3 * a) :
    floorContact Q a b = if b / 2 = a then Real.log 2 / 2 else 0 := by
  unfold floorContact
  rw [Finset.sum_eq_single 2]
  · simp only [vonMangoldt_two, Nat.cast_ofNat]
  · intro k hk hk2
    have hk' := Finset.mem_Icc.mp hk
    have hlt : b / k < a :=
      Nat.div_lt_of_lt_mul (lt_of_lt_of_le hb (Nat.mul_le_mul_right a (by omega)))
    rw [if_neg (Nat.ne_of_lt hlt)]
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩) h

/-- The coupling of two blocks of ratio below three: the jet and the contact of the floor map
of `2`. -/
theorem blockWeight_eq_of_lt_three_mul {Q a b : ℕ} (hQ : 2 ≤ Q) (hab : a < b)
    (hb : b < 3 * a) :
    blockWeight Q a b = blockJet a b + if b / 2 = a then Real.log 2 / 2 else 0 := by
  rw [blockWeight, neutralBlock_of_lt hab, floorContact_eq_of_lt_three_mul hQ hb]
  ring

/-- The jet of two blocks at distance at least `H` is at most `2/H`. -/
theorem blockJet_le_two_div {a b H : ℕ} (hH : 1 ≤ H) (hab : a + H ≤ b) :
    blockJet a b ≤ 2 / H := by
  have h1 := blockJet_le (a := a) (l := b) (by omega)
  have h2 : (H : ℝ) ≤ (b : ℝ) - a := by
    have h : ((a + H : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    push_cast at h
    linarith
  exact h1.trans (div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hH) h2)

/-- **The couplings of a block with the two preimages of a block under the floor map of `2`**:
`log 2` if the blocks agree, and nothing otherwise, up to two jets. The blocks are
`2H + o + i` in `(2H, 4H]` and `4H + 2o + 2j`, `4H + 2o + 2j + 1` in `(4H, 8H]`. -/
theorem abs_blockWeight_pair_sub_le {H Q o i j : ℕ} (hH : 1 ≤ H) (hQ : 2 ≤ Q) (hi : i < H)
    (hj : j < H) :
    |blockWeight Q (H + H + (o + i)) (H + H + (H + H) + (2 * o + 2 * j)) +
        blockWeight Q (H + H + (o + i)) (H + H + (H + H) + (2 * o + (2 * j + 1))) -
          (if i = j then Real.log 2 else 0)| ≤ 4 / H := by
  have e₀ := blockWeight_eq_of_lt_three_mul (Q := Q) (a := H + H + (o + i))
    (b := H + H + (H + H) + (2 * o + 2 * j)) hQ (by omega) (by omega)
  have e₁ := blockWeight_eq_of_lt_three_mul (Q := Q) (a := H + H + (o + i))
    (b := H + H + (H + H) + (2 * o + (2 * j + 1))) hQ (by omega) (by omega)
  have j₀ := blockJet_nonneg_of_lt (a := H + H + (o + i))
    (l := H + H + (H + H) + (2 * o + 2 * j)) (by omega)
  have j₁ := blockJet_nonneg_of_lt (a := H + H + (o + i))
    (l := H + H + (H + H) + (2 * o + (2 * j + 1))) (by omega)
  have u₀ := blockJet_le_two_div (a := H + H + (o + i))
    (b := H + H + (H + H) + (2 * o + 2 * j)) hH (by omega)
  have u₁ := blockJet_le_two_div (a := H + H + (o + i))
    (b := H + H + (H + H) + (2 * o + (2 * j + 1))) hH (by omega)
  have h4 : (2 : ℝ) / H + 2 / H = 4 / H := by ring
  have c₀ : (H + H + (H + H) + (2 * o + 2 * j)) / 2 = H + H + (o + i) ↔ i = j := by omega
  have c₁ : (H + H + (H + H) + (2 * o + (2 * j + 1))) / 2 = H + H + (o + i) ↔ i = j := by
    omega
  rw [e₀, e₁, if_congr c₀ rfl rfl, if_congr c₁ rfl rfl]
  by_cases hij : i = j
  · simp only [if_pos hij]
    rw [abs_le]
    constructor <;> linarith
  · simp only [if_neg hij]
    rw [abs_le]
    constructor <;> linarith

/-- **The distance of a model of rank `r` from the couplings of a quarter with the quarter above
it.** For the blocks `2H + o + i`, `i < H`, and `4H + 2o + j`, `j < 2H`:
`log 2 · (H − 64 r) ≤ Σ |K − M| + H/16 + 4`. -/
theorem log_two_mul_sub_le_quarter {H Q r o : ℕ} (hH : 1 ≤ H) (hQ : 2 ≤ Q)
    (f : Fin H → Fin (H + H)) (hf : ∀ i, (f i : ℕ) = o + i)
    (g : Fin (H + H) → Fin (H + H + (H + H))) (hg : ∀ j, (g j : ℕ) = 2 * o + j)
    (P : Fin (H + H) → Fin r → ℝ) (Qm : Fin (H + H + (H + H)) → Fin r → ℝ) :
    Real.log 2 * ((H : ℝ) - 64 * r) ≤
      (∑ i : Fin H, ∑ j : Fin (H + H),
        |blockWeight Q (H + H + (f i : ℕ)) (H + H + (H + H) + (g j : ℕ)) -
          ∑ k, P (f i) k * Qm (g j) k|) + H / 16 + 4 := by
  have hHpos : (0 : ℝ) < H := Nat.cast_pos.mpr (by omega)
  -- the two preimages of a block
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : Fin H → Fin (H + H), ∀ j, (e₀ j : ℕ) = 2 * j :=
    ⟨fun j => ⟨2 * j, by have := j.2; omega⟩, fun _ => rfl⟩
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : Fin H → Fin (H + H), ∀ j, (e₁ j : ℕ) = 2 * j + 1 :=
    ⟨fun j => ⟨2 * j + 1, by have := j.2; omega⟩, fun _ => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Fin H → Fin (H + H) → ℝ, ∀ i j, W i j =
      |blockWeight Q (H + H + (f i : ℕ)) (H + H + (H + H) + (g j : ℕ)) -
        ∑ k, P (f i) k * Qm (g j) k| := ⟨_, fun _ _ => rfl⟩
  have hW0 : ∀ i j, 0 ≤ W i j := fun i j => by
    rw [hW]
    exact abs_nonneg _
  -- the model summed over the two preimages has rank `r`
  obtain ⟨D, hD⟩ : ∃ D : Fin H → Fin H → ℝ, ∀ i j, D i j =
      ∑ k, P (f i) k * (Qm (g (e₀ j)) k + Qm (g (e₁ j)) k) := ⟨_, fun _ _ => rfl⟩
  have hres := mul_sub_le_sum_abs_on_residue_classes (s := 64) (by norm_num) D
    (fun i k => P (f i) k) (fun j k => Qm (g (e₀ j)) k + Qm (g (e₁ j)) k) hD
    (Real.log_nonneg one_le_two)
  have h64 : ((64 : ℕ) : ℝ) = 64 := by norm_num
  rw [h64] at hres
  -- its distance from `log 2` times the identity: the distance from the couplings and the jets
  have hterm : ∀ i j : Fin H,
      (if (i : ℕ) % 64 = (j : ℕ) % 64 then |D i j - if i = j then Real.log 2 else 0| else 0) ≤
        W i (e₀ j) + W i (e₁ j) + if (i : ℕ) % 64 = (j : ℕ) % 64 then 4 / (H : ℝ) else 0 := by
    intro i j
    by_cases hmod : (i : ℕ) % 64 = (j : ℕ) % 64
    · rw [if_pos hmod, if_pos hmod]
      have hpair := abs_blockWeight_pair_sub_le (Q := Q) (o := o) hH hQ i.2 j.2
      have hδ : (if i = j then Real.log 2 else 0) =
          if (i : ℕ) = (j : ℕ) then Real.log 2 else 0 := if_congr Fin.ext_iff rfl rfl
      have hsum : D i j = (∑ k, P (f i) k * Qm (g (e₀ j)) k) +
          ∑ k, P (f i) k * Qm (g (e₁ j)) k := by
        rw [hD, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => mul_add _ _ _
      rw [hW, hW, hf, hg, hg, he₀, he₁, hδ, hsum]
      exact abs_sub_le_of_pair hpair
    · rw [if_neg hmod, if_neg hmod]
      linarith [hW0 i (e₀ j), hW0 i (e₁ j)]
  have hsumterm := Finset.sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin H))) =>
    Finset.sum_le_sum fun j (_ : j ∈ (univ : Finset (Fin H))) => hterm i j
  have hsplit : ∑ i : Fin H, ∑ j : Fin H, (W i (e₀ j) + W i (e₁ j) +
      if (i : ℕ) % 64 = (j : ℕ) % 64 then 4 / (H : ℝ) else 0) =
      (∑ i : Fin H, ∑ j : Fin H, (W i (e₀ j) + W i (e₁ j))) +
        ∑ i : Fin H, ∑ j : Fin H, if (i : ℕ) % 64 = (j : ℕ) % 64 then 4 / (H : ℝ) else 0 := by
    simp only [Finset.sum_add_distrib]
  have hWsum : ∑ i : Fin H, ∑ j : Fin H, (W i (e₀ j) + W i (e₁ j)) ≤
      ∑ i : Fin H, ∑ j : Fin (H + H), W i j :=
    Finset.sum_le_sum fun i _ =>
      sum_even_add_odd_le (fun j => W i j) (fun j => hW0 i j) e₀ e₁ he₀ he₁
  -- the jets on the residue classes
  have hrow : ∀ i : Fin H,
      ∑ j : Fin H, (if (i : ℕ) % 64 = (j : ℕ) % 64 then 4 / (H : ℝ) else 0) ≤
        ((H : ℝ) / 64 + 1) * (4 / H) := by
    intro i
    have e : ∑ j : Fin H, (if (i : ℕ) % 64 = (j : ℕ) % 64 then 4 / (H : ℝ) else 0) =
        ∑ _j ∈ univ.filter (fun j : Fin H => (j : ℕ) % 64 = (i : ℕ) % 64), 4 / (H : ℝ) := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun j _ => if_congr eq_comm rfl rfl
    rw [e, Finset.sum_const, nsmul_eq_mul]
    have hc : ((univ.filter fun j : Fin H => (j : ℕ) % 64 = (i : ℕ) % 64).card : ℝ) ≤
        ((H / 64 + 1 : ℕ) : ℝ) := by
      exact_mod_cast card_filter_mod_le (H := H) (s := 64) ((i : ℕ) % 64)
    have hdiv : ((H / 64 : ℕ) : ℝ) ≤ (H : ℝ) / 64 := by
      have h := Nat.cast_div_le (α := ℝ) (m := H) (n := 64)
      rwa [h64] at h
    push_cast at hc
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hJ : ∑ i : Fin H, ∑ j : Fin H,
      (if (i : ℕ) % 64 = (j : ℕ) % 64 then 4 / (H : ℝ) else 0) ≤ H / 16 + 4 := by
    calc ∑ i : Fin H, ∑ j : Fin H, (if (i : ℕ) % 64 = (j : ℕ) % 64 then 4 / (H : ℝ) else 0)
        ≤ ∑ _i : Fin H, ((H : ℝ) / 64 + 1) * (4 / H) := Finset.sum_le_sum fun i _ => hrow i
      _ = H / 16 + 4 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
          ring
  have hgoal : ∑ i : Fin H, ∑ j : Fin (H + H),
      |blockWeight Q (H + H + (f i : ℕ)) (H + H + (H + H) + (g j : ℕ)) -
        ∑ k, P (f i) k * Qm (g j) k| = ∑ i : Fin H, ∑ j : Fin (H + H), W i j :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (hW i j).symm
  rw [hgoal]
  linarith [hres.trans hsumterm]

/-! ### The depths of the quarters of a dyadic window -/

/-- The depth per block of the lower quarter `(2H, 3H]` of the window `(2H, 4H]`: minus the
neutral part on the constant packet of the quarter is `H` times this number. -/
def lowerQuarterDepth : ℝ :=
  Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - (5 * Real.log 5 - 9 * Real.log 2)

/-- The depth per block of the upper quarter `(3H, 4H]` of the window `(2H, 4H]`. -/
def upperQuarterDepth : ℝ :=
  Real.eulerMascheroniConstant + Real.log (2 * Real.pi) -
    (7 * Real.log 7 - 7 * Real.log 2 - 6 * Real.log 3)

/-- The pairing per block of the constant packets of the two quarters of `(2H, 4H]`. -/
def quarterPairing : ℝ :=
  (12 * Real.log 3 + 10 * Real.log 2 - 5 * Real.log 5 - 7 * Real.log 7) / 2

theorem lowerQuarterDepth_ge : (6027 / 10000 : ℝ) ≤ lowerQuarterDepth := by
  have l2 := Real.log_two_gt_d9
  have l3 := log_three_mem
  have l5 := log_five_mem
  have hγ := RenormalizedArithmeticPotentialTheory.eulerMascheroniConstant_gt_d4
  have hπ := log_three_add_lt_log_pi
  rw [lowerQuarterDepth, log_two_pi]
  linarith [l3.1, l5.2]

theorem upperQuarterDepth_ge : (2339 / 10000 : ℝ) ≤ upperQuarterDepth := by
  have l2 := Real.log_two_gt_d9
  have l3 := log_three_mem
  have l7 := log_seven_mem
  have hγ := RenormalizedArithmeticPotentialTheory.eulerMascheroniConstant_gt_d4
  have hπ := log_three_add_lt_log_pi
  rw [upperQuarterDepth, log_two_pi]
  linarith [l3.1, l7.2]

theorem abs_quarterPairing_le : |quarterPairing| ≤ 7769 / 10000 := by
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have l3 := log_three_mem
  have l5 := log_five_mem
  have l7 := log_seven_mem
  rw [quarterPairing, abs_le]
  constructor
  · linarith [l3.1, l5.2, l7.2]
  · linarith [l3.2, l5.1, l7.1]

/-- The pairing of the quarters is weaker than their depths raised by `77/200`. -/
theorem quarterPairing_sq_lt :
    quarterPairing ^ 2 < (lowerQuarterDepth + 77 / 200) * (upperQuarterDepth + 77 / 200) := by
  have h₁ := lowerQuarterDepth_ge
  have h₂ := upperQuarterDepth_ge
  have hC := abs_le.mp abs_quarterPairing_le
  have hCsq : quarterPairing ^ 2 ≤ (7769 / 10000 : ℝ) ^ 2 := sq_le_sq' hC.1 hC.2
  have hprod : (9877 / 10000 : ℝ) * (6189 / 10000) ≤
      (lowerQuarterDepth + 77 / 200) * (upperQuarterDepth + 77 / 200) :=
    mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
  have hnum : ((7769 : ℝ) / 10000) ^ 2 < 9877 / 10000 * (6189 / 10000) := by norm_num
  linarith

/-- **The criterion of a lowered dyadic window.** If the neutral part of `(2H, 4H]` with the
potential lowered by `d ≥ 0` has at most one negative square, the lowerings `E₁`, `E₂` of its
two quarters satisfy `(H a₁ + E₁)(H a₂ + E₂) ≤ (H c)²`, with the depths `a₁`, `a₂` and the
pairing `c` of the quarters. -/
theorem mul_le_sq_of_hermNegIndex_lowered_dyadic_le_one {Q H : ℕ} (hH : 1 ≤ H)
    {d : Fin (H + H) → ℝ} (hd : ∀ i, 0 ≤ d i)
    (hidx : hermNegIndex ((neutralWindow Q (H + H) (H + H) - diagonal d).map (↑) :
      Matrix (Fin (H + H)) (Fin (H + H)) ℂ) ≤ 1) :
    ((H : ℝ) * lowerQuarterDepth + ∑ i : Fin H, d (Fin.castAdd H i)) *
        ((H : ℝ) * upperQuarterDepth + ∑ i : Fin H, d (Fin.natAdd H i)) ≤
      ((H : ℝ) * quarterPairing) ^ 2 := by
  have hHpos : (0 : ℝ) < H := Nat.cast_pos.mpr (by omega)
  have hE : 0 ≤ ∑ i : Fin H, d (Fin.castAdd H i) := Finset.sum_nonneg fun i _ => hd _
  have hα := lowerQuarterDepth_ge
  have hneg : (H : ℝ) * -lowerQuarterDepth - ∑ i : Fin H, d (Fin.castAdd H i) < 0 := by
    have := mul_pos hHpos (by linarith : (0 : ℝ) < lowerQuarterDepth)
    linarith
  have h := mul_le_sq_of_hermNegIndex_lowered_le_one (Q := Q) (R := H + H) (H := H) (d := d)
    (n₁ := (H : ℝ) * -lowerQuarterDepth) (n₂ := (H : ℝ) * -upperQuarterDepth)
    (c := (H : ℝ) * quarterPairing)
    ((sum_neutralBlock_lower_quarter Q hH).trans (by rw [lowerQuarterDepth]; ring))
    ((sum_neutralBlock_cross_quarters Q hH).trans (by rw [quarterPairing]))
    ((sum_neutralBlock_upper_quarter Q hH).trans (by rw [upperQuarterDepth]; ring))
    hneg hidx
  calc ((H : ℝ) * lowerQuarterDepth + ∑ i : Fin H, d (Fin.castAdd H i)) *
        ((H : ℝ) * upperQuarterDepth + ∑ i : Fin H, d (Fin.natAdd H i)) =
      ((H : ℝ) * -lowerQuarterDepth - ∑ i : Fin H, d (Fin.castAdd H i)) *
        ((H : ℝ) * -upperQuarterDepth - ∑ i : Fin H, d (Fin.natAdd H i)) := by ring
    _ ≤ _ := h

/-- The criteria of a dyadic window and of its double, with the Cauchy–Schwarz inequality for
the two pairs of quarters, make one of the two distances small. -/
theorem sq_le_or_sq_le_of_two_criteria {H X₁ X₂ Y₁ Y₂ G₁ G₂ : ℝ} (hH : 0 < H) (hX₁ : 0 ≤ X₁)
    (hX₂ : 0 ≤ X₂) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂)
    (hL : (H * lowerQuarterDepth + X₁) * (H * upperQuarterDepth + X₂) ≤
      (H * quarterPairing) ^ 2)
    (hU : ((H + H) * lowerQuarterDepth + Y₁) * ((H + H) * upperQuarterDepth + Y₂) ≤
      ((H + H) * quarterPairing) ^ 2)
    (h1 : G₁ ^ 2 ≤ X₁ * Y₁) (h2 : G₂ ^ 2 ≤ X₂ * Y₂) :
    G₁ ^ 2 ≤ 2 * (H * (77 / 200)) ^ 2 ∨ G₂ ^ 2 ≤ 2 * (H * (77 / 200)) ^ 2 := by
  have h₁ := lowerQuarterDepth_ge
  have h₂ := upperQuarterDepth_ge
  have hU' : (2 * (H * lowerQuarterDepth) + Y₁) * (2 * (H * upperQuarterDepth) + Y₂) ≤
      4 * (H * quarterPairing) ^ 2 :=
    calc (2 * (H * lowerQuarterDepth) + Y₁) * (2 * (H * upperQuarterDepth) + Y₂) =
          ((H + H) * lowerQuarterDepth + Y₁) * ((H + H) * upperQuarterDepth + Y₂) := by ring
      _ ≤ ((H + H) * quarterPairing) ^ 2 := hU
      _ = 4 * (H * quarterPairing) ^ 2 := by ring
  have hc : (H * quarterPairing) ^ 2 <
      (H * lowerQuarterDepth + H * (77 / 200)) * (H * upperQuarterDepth + H * (77 / 200)) :=
    calc (H * quarterPairing) ^ 2 = H ^ 2 * quarterPairing ^ 2 := by ring
      _ < H ^ 2 * ((lowerQuarterDepth + 77 / 200) * (upperQuarterDepth + 77 / 200)) :=
          mul_lt_mul_of_pos_left quarterPairing_sq_lt (pow_pos hH 2)
      _ = _ := by ring
  exact sq_le_or_sq_le_of_two_products (mul_nonneg hH.le (by linarith))
    (mul_nonneg hH.le (by linarith)) (mul_pos hH (by norm_num)) hX₁ hX₂ hY₁ hY₂ hL hU' h1 h2 hc

/-- A small distance contradicts the bound of the rank: `G² ≤ 2 (77 H / 200)²` and
`log 2 · (H − 64 r) ≤ G + H/16 + 4` cannot both hold when `600 (r + 1) ≤ H`. -/
theorem false_of_sq_le_of_log_two_mul_sub_le {H r G : ℝ} (hr : 0 ≤ r)
    (hH : 600 * (r + 1) ≤ H) (hG : G ^ 2 ≤ 2 * (H * (77 / 200)) ^ 2)
    (hq : Real.log 2 * (H - 64 * r) ≤ G + H / 16 + 4) : False := by
  have l2 := Real.log_two_gt_d9
  have hHpos : 0 < H := by linarith
  have hG' : G ≤ 109 / 200 * H := by
    by_contra hlt
    have h1 := mul_self_lt_mul_self (mul_nonneg (by norm_num : (0 : ℝ) ≤ 109 / 200) hHpos.le)
      (not_le.mp hlt)
    nlinarith [sq_nonneg H]
  have hsub : 0 ≤ H - 64 * r := by linarith
  have h1 : (0.6931 : ℝ) * (H - 64 * r) ≤ Real.log 2 * (H - 64 * r) :=
    mul_le_mul_of_nonneg_right (by linarith) hsub
  linarith

/-! ### The halves of the window `(2H, 8H]` -/

/-- The statement on the two lowered halves, with the sizes written as sums. -/
theorem two_le_hermNegIndex_lowered_half_of_rank_aux {H Q r : ℕ} (hH : 600 * (r + 1) ≤ H)
    (hQ : 2 ≤ Q) (P : Fin (H + H) → Fin r → ℝ) (Qm : Fin (H + H + (H + H)) → Fin r → ℝ)
    (t : Fin (H + H) → Fin (H + H + (H + H)) → ℝ) (ht : ∀ i j, 0 < t i j) :
    2 ≤ hermNegIndex ((neutralWindow Q (H + H) (H + H) - diagonal (loweringLeft
        (fun (i : Fin (H + H)) (j : Fin (H + H + (H + H))) =>
          blockWeight Q (H + H + i) (H + H + (H + H) + j))
        (fun i j => ∑ k, P i k * Qm j k) t)).map (↑) :
          Matrix (Fin (H + H)) (Fin (H + H)) ℂ) ∨
      2 ≤ hermNegIndex ((neutralWindow Q (H + H + (H + H)) (H + H + (H + H)) -
        diagonal (loweringRight
          (fun (i : Fin (H + H)) (j : Fin (H + H + (H + H))) =>
            blockWeight Q (H + H + i) (H + H + (H + H) + j))
          (fun i j => ∑ k, P i k * Qm j k) t)).map (↑) :
            Matrix (Fin (H + H + (H + H))) (Fin (H + H + (H + H))) ℂ) := by
  by_contra hcon
  obtain ⟨hA, hB⟩ := not_or.mp hcon
  obtain ⟨K, hK⟩ : ∃ K : Fin (H + H) → Fin (H + H + (H + H)) → ℝ,
      K = fun (i : Fin (H + H)) (j : Fin (H + H + (H + H))) =>
        blockWeight Q (H + H + (i : ℕ)) (H + H + (H + H) + (j : ℕ)) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Fin (H + H) → Fin (H + H + (H + H)) → ℝ,
      M = fun i j => ∑ k, P i k * Qm j k := ⟨_, rfl⟩
  rw [← hK, ← hM] at hA hB
  have hH1 : 1 ≤ H := by omega
  -- the criteria of the two halves
  have hcL := mul_le_sq_of_hermNegIndex_lowered_dyadic_le_one (Q := Q) hH1
    (d := loweringLeft K M t) (fun i => loweringLeft_nonneg K M ht i) (by omega)
  have hcU := mul_le_sq_of_hermNegIndex_lowered_dyadic_le_one (Q := Q) (H := H + H) (by omega)
    (d := loweringRight K M t) (fun j => loweringRight_nonneg K M ht j) (by omega)
  rw [Nat.cast_add] at hcU
  -- the distances between a quarter and the quarter above it
  have hinjc : ∀ n m : ℕ, Function.Injective (Fin.castAdd m : Fin n → Fin (n + m)) :=
    fun n m a b h => Fin.ext (by
      have h' := congrArg Fin.val h
      rwa [Fin.val_castAdd, Fin.val_castAdd] at h')
  have hinjn : ∀ n m : ℕ, Function.Injective (Fin.natAdd n : Fin m → Fin (n + m)) :=
    fun n m a b h => Fin.ext (by
      have h' := congrArg Fin.val h
      rw [Fin.val_natAdd, Fin.val_natAdd] at h'
      omega)
  have hcs₁ := sq_sum_abs_le_lowering K M ht (Fin.castAdd H) (Fin.castAdd (H + H))
    (hinjc H H) (hinjc (H + H) (H + H))
  have hcs₂ := sq_sum_abs_le_lowering K M ht (Fin.natAdd H) (Fin.natAdd (H + H))
    (hinjn H H) (hinjn (H + H) (H + H))
  have hsmall := sq_le_or_sq_le_of_two_criteria (Nat.cast_pos.mpr (by omega : 0 < H))
    (Finset.sum_nonneg fun i _ => loweringLeft_nonneg K M ht _)
    (Finset.sum_nonneg fun i _ => loweringLeft_nonneg K M ht _)
    (Finset.sum_nonneg fun j _ => loweringRight_nonneg K M ht _)
    (Finset.sum_nonneg fun j _ => loweringRight_nonneg K M ht _) hcL hcU hcs₁ hcs₂
  -- a small distance contradicts the rank
  have hcase : ∀ (o : ℕ) (f : Fin H → Fin (H + H)) (g : Fin (H + H) → Fin (H + H + (H + H))),
      (∀ i, (f i : ℕ) = o + i) → (∀ j, (g j : ℕ) = 2 * o + j) →
      (∑ i, ∑ j, |K (f i) (g j) - M (f i) (g j)|) ^ 2 ≤ 2 * ((H : ℝ) * (77 / 200)) ^ 2 →
        False := by
    intro o f g hf hg hG
    have hq := log_two_mul_sub_le_quarter (Q := Q) (r := r) hH1 hQ f hf g hg P Qm
    have hGeq : ∑ i, ∑ j, |K (f i) (g j) - M (f i) (g j)| =
        ∑ i : Fin H, ∑ j : Fin (H + H),
          |blockWeight Q (H + H + (f i : ℕ)) (H + H + (H + H) + (g j : ℕ)) -
            ∑ k, P (f i) k * Qm (g j) k| :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hK, hM]
    rw [← hGeq] at hq
    exact false_of_sq_le_of_log_two_mul_sub_le (Nat.cast_nonneg r) (by exact_mod_cast hH) hG hq
  rcases hsmall with h | h
  · exact hcase 0 (Fin.castAdd H) (Fin.castAdd (H + H))
      (fun i => by rw [Fin.val_castAdd, zero_add])
      (fun j => by rw [Fin.val_castAdd, mul_zero, zero_add]) h
  · exact hcase H (Fin.natAdd H) (Fin.natAdd (H + H)) (fun i => by rw [Fin.val_natAdd])
      (fun j => by rw [Fin.val_natAdd, two_mul]) h

/-- **One of the two lowered halves has two negative squares.** Let `600 (r + 1) ≤ H`. For
every model coupling of rank `r` between `(2H, 4H]` and `(4H, 8H]` and all weights, the neutral
part of `(2H, 4H]` or the neutral part of `(4H, 8H]`, with the potential lowered by the distance
of the couplings from the model, has at least two negative squares. -/
theorem two_le_hermNegIndex_lowered_half_of_rank {H Q r : ℕ} (hH : 600 * (r + 1) ≤ H)
    (hQ : 2 ≤ Q) :
    ∀ (P : Fin (2 * H) → Fin r → ℝ) (Qm : Fin (4 * H) → Fin r → ℝ)
      (t : Fin (2 * H) → Fin (4 * H) → ℝ), (∀ i j, 0 < t i j) →
      2 ≤ hermNegIndex ((neutralWindow Q (2 * H) (2 * H) - diagonal (loweringLeft
          (fun (i : Fin (2 * H)) (j : Fin (4 * H)) =>
            blockWeight Q (2 * H + i) (2 * H + 2 * H + j))
          (fun i j => ∑ k, P i k * Qm j k) t)).map (↑) :
            Matrix (Fin (2 * H)) (Fin (2 * H)) ℂ) ∨
        2 ≤ hermNegIndex ((neutralWindow Q (2 * H + 2 * H) (4 * H) - diagonal (loweringRight
          (fun (i : Fin (2 * H)) (j : Fin (4 * H)) =>
            blockWeight Q (2 * H + i) (2 * H + 2 * H + j))
          (fun i j => ∑ k, P i k * Qm j k) t)).map (↑) :
            Matrix (Fin (4 * H)) (Fin (4 * H)) ℂ) := by
  rw [show 4 * H = 2 * H + 2 * H by ring, two_mul]
  exact fun P Qm t ht => two_le_hermNegIndex_lowered_half_of_rank_aux hH hQ P Qm t ht

/-- **No lowered model of small rank counts one bound state at ratio four.** Let
`600 (r + 1) ≤ H`. For every model coupling of rank `r` and all weights, the halves `(2H, 4H]`
and `(4H, 8H]` with potentials lowered by the distance of the couplings from the model, coupled
by the model, have at least two negative squares. -/
theorem two_le_hermNegIndex_lowered_model_of_rank {H Q r : ℕ} (hH : 600 * (r + 1) ≤ H)
    (hQ : 2 ≤ Q) (P : Fin (2 * H) → Fin r → ℝ) (Qm : Fin (4 * H) → Fin r → ℝ)
    (t : Fin (2 * H) → Fin (4 * H) → ℝ) (ht : ∀ i j, 0 < t i j) :
    2 ≤ hermNegIndex ((coupled
      (neutralWindow Q (2 * H) (2 * H) - diagonal (loweringLeft
        (fun (i : Fin (2 * H)) (j : Fin (4 * H)) =>
          blockWeight Q (2 * H + i) (2 * H + 2 * H + j))
        (fun i j => ∑ k, P i k * Qm j k) t))
      (neutralWindow Q (2 * H + 2 * H) (4 * H) - diagonal (loweringRight
        (fun (i : Fin (2 * H)) (j : Fin (4 * H)) =>
          blockWeight Q (2 * H + i) (2 * H + 2 * H + j))
        (fun i j => ∑ k, P i k * Qm j k) t))
      (fun i j => ∑ k, P i k * Qm j k)).map (↑) :
        Matrix (Fin (2 * H) ⊕ Fin (4 * H)) (Fin (2 * H) ⊕ Fin (4 * H)) ℂ) := by
  rcases two_le_hermNegIndex_lowered_half_of_rank hH hQ P Qm t ht with h | h
  · exact h.trans (hermNegIndex_left_le_coupled _ _ _)
  · exact h.trans (hermNegIndex_right_le_coupled _ _ _)

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
