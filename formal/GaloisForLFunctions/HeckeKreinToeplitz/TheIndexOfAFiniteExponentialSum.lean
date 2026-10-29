import GaloisForLFunctions.HeckeKreinToeplitz.HyperbolicPairsAndTheIndexFormula
import GaloisForLFunctions.HTGeometry.IsometricCongruenceInertia

/-!
# The index of a finite exponential sum

The covariant Krein–Langer classification for kernels of finite spectral support, on any group
and with no separation hypothesis.

A **finite exponential sum** is `k = Σ_{χ ∈ S} a_χ χ` for a finite set `S` of characters
`G →* ℂ`, closed under the reflection `χ ↦ χ†`, with `a_{χ†} = conj a_χ` (so `k` is Hermitian,
`isHermKernel_expSum`).

**The spectral matrix carries the index** (`negIndex_expSum_eq`). Every Gram matrix of `k`
factors as `Mᴴ A M`, where `M = (χ(x_b))` evaluates the characters on the family and `A` is the
spectral matrix (`a_χ` at `(χ†, χ)`). So `κ(k) ≤ κ(A)`. Distinct characters are linearly
independent (Dedekind–Artin), so some finite family makes `M` surjective, and then `κ(k) = κ(A)`.

**The index count** (`negIndex_expSum`). Choose one representative of each reflected pair. Then
`κ(k)` is the number of unitary characters (the fixed points of `†`, `reflectChar_eq_self_iff`)
with negative weight plus the number of reflected pairs of non-unitary characters with nonzero
weight. Each pair is a hyperbolic plane in the spectral matrix and each negative unitary weight
one negative line. There are twice as many non-unitary characters with nonzero weight as pairs
(`card_nonUnitary_eq_two_mul`).

On `ℚ_{>0}` with `χ_ρ(u) = u^{ρ−1/2}` this counts the off-line zeros of a finite zero
configuration exactly, at any choice of points: the separation hypothesis of the general index
formula is needed only when a positive-definite part of infinite rank is present.
-/

open Complex Finset Matrix
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (negIndex_le_card_of_nonneg_on_ker)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [Group G]

/-- Unitary characters are exactly the fixed points of the reflection. -/
theorem reflectChar_eq_self_iff {χ : G →* ℂ} : reflectChar χ = χ ↔ IsUnitaryChar χ := by
  refine ⟨fun h u => ?_, reflectChar_eq_of_unitary⟩
  have h1 := norm_reflectChar χ u
  rw [h] at h1
  have hpos : 0 < ‖χ u‖ := norm_pos_iff.mpr (map_ne_zero χ u)
  have h2 : ‖χ u‖ * ‖χ u‖ = 1 :=
    calc ‖χ u‖ * ‖χ u‖ = ‖χ u‖ * ‖χ u‖⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel₀ hpos.ne'
  nlinarith

/-- A **finite exponential sum** `Σ_{χ ∈ S} a_χ χ`. -/
def expSum (S : Finset (G →* ℂ)) (a : (G →* ℂ) → ℂ) (u : G) : ℂ := ∑ χ ∈ S, a χ * χ u

/-- The evaluation matrix `(χ(x_b))_{χ, b}`. -/
def evalMat (S : Finset (G →* ℂ)) {ι : Type*} (x : ι → G) : Matrix S ι ℂ :=
  fun χ b => (χ : G →* ℂ) (x b)

section Reflection

variable {S : Finset (G →* ℂ)} (hS : ∀ χ ∈ S, reflectChar χ ∈ S)

/-- The reflection `χ ↦ χ†` on a reflection-closed set of characters. -/
def reflS (χ : S) : S := ⟨reflectChar χ, hS χ χ.2⟩

theorem reflS_reflS (χ : S) : reflS hS (reflS hS χ) = χ :=
  Subtype.ext (reflectChar_reflectChar _)

open Classical in
/-- The **spectral matrix**: the weight `a_χ` at `(χ†, χ)`. -/
def specMat (a : (G →* ℂ) → ℂ) : Matrix S S ℂ :=
  fun ψ χ => if ψ = reflS hS χ then a χ else 0

/-- Gram matrices of a finite exponential sum factor through the spectral matrix. -/
theorem gram_expSum (a : (G →* ℂ) → ℂ) {ι : Type*} [Fintype ι] (x : ι → G) :
    gram (expSum S a) x = (evalMat S x)ᴴ * specMat hS a * evalMat S x := by
  classical
  ext i j
  have hrow : ∀ ψ : S, ((evalMat S x)ᴴ * specMat hS a) i ψ =
      conj (reflectChar (ψ : G →* ℂ) (x i)) * a ψ := fun ψ => by
    simp only [mul_apply, conjTranspose_apply, evalMat, specMat, RCLike.star_def, mul_ite,
      mul_zero, Finset.sum_ite_eq', mem_univ, if_true, reflS]
  rw [mul_apply]
  simp only [hrow, gram, expSum, evalMat, conj_reflectChar, map_mul]
  rw [← Finset.sum_coe_sort S]
  exact sum_congr rfl fun ψ _ => by ring

/-- The form of the spectral matrix couples each character with its reflection. -/
theorem hermQuad_specMat (a : (G →* ℂ) → ℂ) (y : S → ℂ) :
    hermQuad (specMat hS a) y = ∑ χ, (conj (y (reflS hS χ)) * a χ * y χ).re := by
  classical
  have h : star y ⬝ᵥ specMat hS a *ᵥ y = ∑ χ, conj (y (reflS hS χ)) * a χ * y χ := by
    simp only [dotProduct, mulVec, specMat, Pi.star_apply, RCLike.star_def, ite_mul, zero_mul,
      mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun χ _ => ?_
    rw [Finset.sum_ite_eq' univ (reflS hS χ), if_pos (mem_univ _), mul_assoc]
  rw [hermQuad, h, re_sum]

/-- Every finite exponential sum has at most as many negative squares as its spectral matrix. -/
theorem negIndex_expSum_le (a : (G →* ℂ) → ℂ) :
    negIndex (expSum S a) ≤ hermNegIndex (specMat hS a) :=
  negIndex_le_iff.mpr fun n x => Nat.cast_le.mpr <|
    hermNegIndex_le_of_hermQuad_eq _ _ (evalMat S x).mulVecLin fun c => by
      rw [mulVecLin_apply, gram_expSum hS, hermQuad_rect_conjugate]

end Reflection

/-- **Dedekind–Artin on finitely many points.** Some finite family makes the evaluation of
finitely many distinct characters surjective. -/
theorem exists_evalMat_surjective (S : Finset (G →* ℂ)) :
    ∃ (n : ℕ) (x : Fin n → G), LinearMap.range (evalMat S x).mulVecLin = ⊤ := by
  classical
  set ev : G → (S → ℂ) := fun g χ => (χ : G →* ℂ) g
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hfle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    have hf : ∀ v : S → ℂ, f v = ∑ χ, v χ * f (fun j => if χ = j then 1 else 0) := fun v => by
      conv_lhs => rw [pi_eq_sum_univ v]
      simp only [map_sum, map_smul, smul_eq_mul]
    have hzero : ∀ g, ∑ χ : S, f (fun j => if χ = j then 1 else 0) * (χ : G →* ℂ) g = 0 :=
      fun g => by
      have h1 : f (ev g) = 0 := hfle (Submodule.subset_span ⟨g, rfl⟩)
      rw [hf] at h1
      exact Eq.trans (sum_congr rfl fun χ _ => mul_comm _ _) h1
    have hli := (linearIndependent_monoidHom G ℂ).comp (fun χ : S => (χ : G →* ℂ))
      Subtype.val_injective
    have hc := Fintype.linearIndependent_iff.mp hli (fun χ => f (fun j => if χ = j then 1 else 0))
      (funext fun g => by simpa [Finset.sum_apply] using hzero g)
    exact hf0 (LinearMap.ext fun v => by rw [hf]; simp [hc])
  obtain ⟨b, hb, hbspan, hbli⟩ := exists_linearIndependent ℂ (Set.range ev)
  have hfin : b.Finite := hbli.setFinite
  set T := hfin.toFinset
  choose g hg using fun v : T => hb ((Set.Finite.mem_toFinset hfin).mp v.2)
  refine ⟨T.card, fun i => g (T.equivFin.symm i), ?_⟩
  rw [Matrix.range_mulVecLin, eq_top_iff, ← hspan, ← hbspan]
  refine Submodule.span_mono fun v hv => ?_
  have hvT : v ∈ T := (Set.Finite.mem_toFinset hfin).mpr hv
  refine ⟨T.equivFin ⟨v, hvT⟩, ?_⟩
  funext χ
  have := congrFun (hg ⟨v, hvT⟩) χ
  simpa [Matrix.col, evalMat, ev] using this

section Reflection

variable {S : Finset (G →* ℂ)} (hS : ∀ χ ∈ S, reflectChar χ ∈ S)

/-- **The spectral matrix carries the index.** -/
theorem negIndex_expSum_eq (a : (G →* ℂ) → ℂ) :
    negIndex (expSum S a) = hermNegIndex (specMat hS a) := by
  refine le_antisymm (negIndex_expSum_le hS a) ?_
  obtain ⟨n, x, hx⟩ := exists_evalMat_surjective S
  obtain ⟨R, hR⟩ := LinearMap.exists_rightInverse_of_surjective _ hx
  refine (Nat.cast_le.mpr (hermNegIndex_le_of_hermQuad_eq _ _ R fun y => ?_)).trans
    (hermNegIndex_gram_le_negIndex _ x)
  rw [gram_expSum hS, hermQuad_rect_conjugate]
  congr 1
  exact LinearMap.congr_fun hR y

/-! ### Counting the negative squares of the spectral matrix -/

variable (a : (G →* ℂ) → ℂ) (ha : ∀ χ ∈ S, a (reflectChar χ) = conj (a χ))
include ha

include hS in
/-- A finite exponential sum with reflection-symmetric weights is Hermitian. -/
theorem isHermKernel_expSum : IsHermKernel (expSum S a) := fun u => by
  simp only [expSum, map_sum, map_mul]
  rw [← Finset.sum_coe_sort S, ← Finset.sum_coe_sort S]
  refine Fintype.sum_equiv (Function.Involutive.toPerm _ (reflS_reflS hS)) _ _ fun χ => ?_
  show a χ * (χ : G →* ℂ) u⁻¹ = conj (a (reflectChar χ)) * conj ((reflectChar (χ : G →* ℂ)) u)
  rw [ha χ χ.2, Complex.conj_conj, conj_reflectChar]

omit ha in
/-- A label separating each character from its reflection. -/
def label (χ : S) : ℕ := (S.equivFin χ : ℕ)

omit ha in
theorem label_injective : Function.Injective (label (S := S)) :=
  fun _ _ h => S.equivFin.injective (Fin.ext h)

omit ha in
open Classical in
/-- The unitary characters of negative weight. -/
def negUnitary : Finset S := univ.filter fun χ => reflS hS χ = χ ∧ (a χ).re < 0

omit ha in
open Classical in
/-- One representative of each reflected pair of non-unitary characters with nonzero weight. -/
def pairReps : Finset S :=
  univ.filter fun χ => reflS hS χ ≠ χ ∧ a χ ≠ 0 ∧ label χ < label (reflS hS χ)

omit ha in
theorem mem_negUnitary {χ : S} : χ ∈ negUnitary hS a ↔ reflS hS χ = χ ∧ (a χ).re < 0 := by
  simp [negUnitary]

omit ha in
theorem mem_pairReps {χ : S} :
    χ ∈ pairReps hS a ↔ reflS hS χ ≠ χ ∧ a χ ≠ 0 ∧ label χ < label (reflS hS χ) := by
  simp [pairReps]

omit ha in
theorem reflS_not_mem_pairReps {χ : S} (h : χ ∈ pairReps hS a) : reflS hS χ ∉ pairReps hS a := by
  rw [mem_pairReps] at h ⊢
  rw [reflS_reflS]
  rintro ⟨-, -, h'⟩
  omega

theorem a_reflS (χ : S) : a (reflS hS χ) = conj (a χ) := ha χ χ.2

theorem mem_or_reflS_mem_pairReps {χ : S} (h1 : reflS hS χ ≠ χ) (h2 : a χ ≠ 0) :
    χ ∈ pairReps hS a ∨ reflS hS χ ∈ pairReps hS a := by
  have hl : label χ ≠ label (reflS hS χ) := fun e => h1 (label_injective e).symm
  rcases lt_or_gt_of_ne hl with h | h
  · exact Or.inl ((mem_pairReps hS a).mpr ⟨h1, h2, h⟩)
  · refine Or.inr ((mem_pairReps hS a).mpr ⟨?_, ?_, ?_⟩)
    · rw [reflS_reflS]; exact Ne.symm h1
    · rw [a_reflS hS a ha]; exact star_ne_zero.mpr h2
    · rw [reflS_reflS]; exact h

open Classical in
/-- There are twice as many non-unitary characters of nonzero weight as reflected pairs. -/
theorem card_nonUnitary_eq_two_mul :
    (univ.filter fun χ : S => reflS hS χ ≠ χ ∧ a χ ≠ 0).card = 2 * (pairReps hS a).card := by
  classical
  have hsplit : (univ.filter fun χ : S => reflS hS χ ≠ χ ∧ a χ ≠ 0) =
      pairReps hS a ∪ (pairReps hS a).image (reflS hS) := by
    ext χ
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      rcases mem_or_reflS_mem_pairReps hS a ha h1 h2 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨reflS hS χ, h, reflS_reflS hS χ⟩
    · rintro (h | ⟨ψ, hψ, rfl⟩)
      · obtain ⟨h1, h2, -⟩ := (mem_pairReps hS a).mp h
        exact ⟨h1, h2⟩
      · obtain ⟨h1, h2, -⟩ := (mem_pairReps hS a).mp hψ
        refine ⟨by rw [reflS_reflS]; exact Ne.symm h1, ?_⟩
        rw [a_reflS hS a ha]
        exact star_ne_zero.mpr h2
  have hdisj : Disjoint (pairReps hS a) ((pairReps hS a).image (reflS hS)) := by
    rw [Finset.disjoint_left]
    intro χ hχ hχ'
    obtain ⟨ψ, hψ, rfl⟩ := mem_image.mp hχ'
    exact reflS_not_mem_pairReps hS a hψ hχ
  rw [hsplit, card_union_of_disjoint hdisj,
    card_image_of_injective _ (Function.Involutive.injective (reflS_reflS hS))]
  ring

/-- The spectral matrix has at most one negative square per negative unitary weight and per
reflected pair. -/
theorem hermNegIndex_specMat_le :
    hermNegIndex (specMat hS a) ≤ (negUnitary hS a).card + (pairReps hS a).card := by
  classical
  let φ : negUnitary hS a ⊕ pairReps hS a → (S → ℂ) →ₗ[ℂ] ℂ :=
    Sum.elim (fun χ => LinearMap.proj (χ : S))
      (fun χ => LinearMap.proj (χ : S) - conj (a χ) • LinearMap.proj (reflS hS χ))
  have h := negIndex_le_card_of_nonneg_on_ker (specMat hS a) φ fun y hy => by
    have hU : ∀ χ ∈ negUnitary hS a, y χ = 0 := fun χ hχ => by
      simpa [φ] using hy (Sum.inl ⟨χ, hχ⟩)
    have hR : ∀ χ ∈ pairReps hS a, y χ = conj (a χ) * y (reflS hS χ) := fun χ hχ => by
      have := hy (Sum.inr ⟨χ, hχ⟩)
      simp only [φ, Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.coe_proj,
        Function.eval, smul_eq_mul] at this
      linear_combination this
    rw [hermQuad_specMat]
    refine sum_nonneg fun χ _ => ?_
    by_cases hf : reflS hS χ = χ
    · have hT : conj (y (reflS hS χ)) * a χ * y χ = a χ * (normSq (y χ) : ℂ) := by
        rw [hf, normSq_eq_conj_mul_self]
        ring
      rw [hT, re_mul_ofReal]
      by_cases hneg : (a χ).re < 0
      · rw [hU χ ((mem_negUnitary hS a).mpr ⟨hf, hneg⟩)]
        simp
      · exact mul_nonneg (not_lt.mp hneg) (normSq_nonneg _)
    · by_cases h0 : a χ = 0
      · simp [h0]
      rcases mem_or_reflS_mem_pairReps hS a ha hf h0 with hχ | hχ
      · rw [hR χ hχ]
        have : conj (y (reflS hS χ)) * a χ * (conj (a χ) * y (reflS hS χ)) =
            ((normSq (a χ) * normSq (y (reflS hS χ)) : ℝ) : ℂ) := by
          push_cast
          rw [normSq_eq_conj_mul_self, normSq_eq_conj_mul_self]
          ring
        rw [this, ofReal_re]
        exact mul_nonneg (normSq_nonneg _) (normSq_nonneg _)
      · have h2 := hR _ hχ
        rw [reflS_reflS, a_reflS hS a ha, Complex.conj_conj] at h2
        rw [h2]
        have : conj (a χ * y χ) * a χ * y χ = (normSq (a χ * y χ) : ℂ) := by
          rw [normSq_eq_conj_mul_self]
          ring
        rw [this, ofReal_re]
        exact normSq_nonneg _
  simpa [Fintype.card_sum] using h

/-- Each negative unitary weight and each reflected pair contributes a negative square. -/
theorem le_hermNegIndex_specMat :
    (negUnitary hS a).card + (pairReps hS a).card ≤ hermNegIndex (specMat hS a) := by
  classical
  set U := negUnitary hS a
  set R := pairReps hS a
  have hUf : ∀ χ ∈ U, reflS hS χ = χ := fun χ h => ((mem_negUnitary hS a).mp h).1
  have hRf : ∀ χ ∈ R, reflS hS χ ≠ χ := fun χ h => ((mem_pairReps hS a).mp h).1
  have hUR : ∀ χ ∈ U, χ ∉ R := fun χ h h' => hRf χ h' (hUf χ h)
  have hUR' : ∀ χ ∈ R, χ ∉ U := fun χ h h' => hUR χ h' h
  have hσU : ∀ χ ∈ R, reflS hS χ ∉ U := fun χ h h' => by
    have := hUf _ h'
    rw [reflS_reflS] at this
    exact hRf χ h this.symm
  let tU : (U ⊕ R → ℂ) → S → ℂ := fun t χ => if h : χ ∈ U then t (Sum.inl ⟨χ, h⟩) else 0
  let tR : (U ⊕ R → ℂ) → S → ℂ := fun t χ => if h : χ ∈ R then t (Sum.inr ⟨χ, h⟩) else 0
  let L : (U ⊕ R → ℂ) →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun t χ => tU t χ - conj (a χ) * tR t χ + tR t (reflS hS χ)
      map_add' := fun t t' => funext fun χ => by
        simp only [tU, tR, Pi.add_apply]
        split_ifs <;> ring
      map_smul' := fun c t => funext fun χ => by
        simp only [tU, tR, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> ring }
  have hL : ∀ t χ, L t χ = tU t χ - conj (a χ) * tR t χ + tR t (reflS hS χ) := fun _ _ => rfl
  have tU_out : ∀ t χ, χ ∉ U → tU t χ = 0 := fun t χ h => dif_neg h
  have tR_out : ∀ t χ, χ ∉ R → tR t χ = 0 := fun t χ h => dif_neg h
  -- the terms of the form on the image of `L`
  have caseU : ∀ t χ, χ ∈ U →
      (conj (L t (reflS hS χ)) * a χ * L t χ).re = (a χ).re * normSq (tU t χ) := fun t χ h => by
    have e : L t χ = tU t χ := by
      rw [hL, tR_out t χ (hUR χ h), hUf χ h, tR_out t χ (hUR χ h)]
      ring
    rw [hUf χ h, e, ← re_mul_ofReal, normSq_eq_conj_mul_self]
    ring_nf
  have caseR : ∀ t χ, χ ∈ R → (conj (L t (reflS hS χ)) * a χ * L t χ).re =
      -(normSq (a χ) * normSq (tR t χ)) := fun t χ h => by
    have hσR := reflS_not_mem_pairReps hS a h
    have e1 : L t (reflS hS χ) = tR t χ := by
      rw [hL, tU_out t _ (hσU χ h), tR_out t _ hσR, reflS_reflS]
      ring
    have e2 : L t χ = -conj (a χ) * tR t χ := by
      rw [hL, tU_out t χ (hUR' χ h), tR_out t _ hσR]
      ring
    rw [e1, e2]
    have : conj (tR t χ) * a χ * (-conj (a χ) * tR t χ) =
        ((-(normSq (a χ) * normSq (tR t χ)) : ℝ) : ℂ) := by
      push_cast
      rw [normSq_eq_conj_mul_self, normSq_eq_conj_mul_self]
      ring
    rw [this, ofReal_re]
  have key : ∀ t χ, (conj (L t (reflS hS χ)) * a χ * L t χ).re ≤ 0 := fun t χ => by
    by_cases hχU : χ ∈ U
    · rw [caseU t χ hχU]
      exact mul_nonpos_of_nonpos_of_nonneg ((mem_negUnitary hS a).mp hχU).2.le (normSq_nonneg _)
    by_cases hχR : χ ∈ R
    · rw [caseR t χ hχR, neg_nonpos]
      exact mul_nonneg (normSq_nonneg _) (normSq_nonneg _)
    by_cases hσR : reflS hS χ ∈ R
    · have h' := caseR t _ hσR
      have hσσ : reflS hS (reflS hS χ) = χ := reflS_reflS hS χ
      have e1 : L t χ = tR t (reflS hS χ) := by
        rw [hL, tU_out t χ hχU, tR_out t χ hχR]
        ring
      have e2 : L t (reflS hS χ) = -conj (a (reflS hS χ)) * tR t (reflS hS χ) := by
        rw [hL, tU_out t _ (hUR' _ hσR), hσσ, tR_out t χ hχR]
        ring
      have haχ : a χ = conj (a (reflS hS χ)) := by rw [a_reflS hS a ha, Complex.conj_conj]
      rw [e1, e2, haχ]
      have : conj (-conj (a (reflS hS χ)) * tR t (reflS hS χ)) * conj (a (reflS hS χ)) *
          tR t (reflS hS χ) =
          ((-(normSq (a (reflS hS χ)) * normSq (tR t (reflS hS χ)))) : ℝ) := by
        push_cast
        rw [normSq_eq_conj_mul_self, normSq_eq_conj_mul_self]
        simp only [map_mul, map_neg, Complex.conj_conj]
        ring
      rw [this, ofReal_re, neg_nonpos]
      exact mul_nonneg (normSq_nonneg _) (normSq_nonneg _)
    · have e : L t χ = 0 := by
        rw [hL, tU_out t χ hχU, tR_out t χ hχR, tR_out t _ hσR]
        ring
      rw [e]
      simp
  have h := card_le_hermNegIndex_of_forall_neg (specMat hS a) L fun t ht => by
    rw [hermQuad_specMat]
    obtain ⟨k, hk⟩ : ∃ k, t k ≠ 0 := by
      by_contra hc
      push Not at hc
      exact ht (funext hc)
    obtain ⟨χ, hχ⟩ : ∃ χ, (conj (L t (reflS hS χ)) * a χ * L t χ).re < 0 := by
      rcases k with ⟨χ, hχU⟩ | ⟨χ, hχR⟩
      · refine ⟨χ, ?_⟩
        rw [caseU t χ hχU, show tU t χ = t (Sum.inl ⟨χ, hχU⟩) from dif_pos hχU]
        exact mul_neg_of_neg_of_pos ((mem_negUnitary hS a).mp hχU).2 (normSq_pos.mpr hk)
      · refine ⟨χ, ?_⟩
        rw [caseR t χ hχR, show tR t χ = t (Sum.inr ⟨χ, hχR⟩) from dif_pos hχR, neg_neg_iff_pos]
        exact mul_pos (normSq_pos.mpr ((mem_pairReps hS a).mp hχR).2.1) (normSq_pos.mpr hk)
    have := Finset.sum_lt_sum (s := univ)
      (f := fun χ => (conj (L t (reflS hS χ)) * a χ * L t χ).re) (g := fun _ => 0)
      (fun χ _ => key t χ) ⟨χ, mem_univ _, hχ⟩
    simpa using this
  simpa [Fintype.card_sum] using h

/-- **The index of a finite exponential sum.** It is the number of unitary characters of negative
weight plus the number of reflected pairs of non-unitary characters of nonzero weight. -/
theorem negIndex_expSum :
    negIndex (expSum S a) = (negUnitary hS a).card + (pairReps hS a).card := by
  rw [negIndex_expSum_eq hS,
    le_antisymm (hermNegIndex_specMat_le hS a ha) (le_hermNegIndex_specMat hS a ha)]
  push_cast
  rfl

end Reflection

end GaloisForLFunctions.HeckeKreinToeplitz
