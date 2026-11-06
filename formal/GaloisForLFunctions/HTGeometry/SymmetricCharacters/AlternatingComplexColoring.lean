import GaloisForLFunctions.HTGeometry.SymmetricCharacters.ComplexColoring
import GaloisForLFunctions.HTGeometry.SymmetricCharacters.GeometricCharacters
import Mathlib.Data.Finset.Sort

/-!
# Alternating traces and elementary-symmetric masses

Signed stabilizers cancel every word with a repeated letter. An injective word consists of
its finite range and an ordering of that range, giving the factorial exterior coefficient.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.SymmetricCharacters

abbrev CardSubset (b : ℕ) (α : Type*) [DecidableEq α] :=
  {R : Finset α // R.card = b}

/-- Every injection is its range and the permutation comparing it with increasing order. -/
def embeddingSubsetPermEquiv
    (b : ℕ) (α : Type*) [LinearOrder α] :
    (Fin b ↪ α) ≃ CardSubset b α × Equiv.Perm (Fin b) where
  toFun f := by
    let R : Finset α := Finset.univ.image f
    have hR : R.card = b := by
      dsimp [R]
      rw [Finset.card_image_of_injective _ f.injective,
        Finset.card_univ, Fintype.card_fin]
    let e : Fin b ≃o ↥R := R.orderIsoOfFin hR
    let piFun : Fin b → Fin b := fun i => e.symm
      ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
    have hpiinj : Function.Injective piFun := by
      intro i j hij
      apply f.injective
      exact congrArg Subtype.val (e.symm.injective hij)
    have hpibij : Function.Bijective piFun :=
      (Fintype.bijective_iff_injective_and_card piFun).2
        ⟨hpiinj, rfl⟩
    exact (⟨R, hR⟩, Equiv.ofBijective piFun hpibij)
  invFun z :=
    ⟨fun i => ((z.1.1.orderIsoOfFin z.1.2) (z.2 i) : α),
      fun i j h => z.2.injective
        ((z.1.1.orderIsoOfFin z.1.2).injective (Subtype.ext h))⟩
  left_inv f := by
    apply Function.Embedding.ext
    intro i
    simp only
    exact congrArg Subtype.val
      (((Finset.univ.image f).orderIsoOfFin
        (by rw [Finset.card_image_of_injective _ f.injective,
          Finset.card_univ, Fintype.card_fin])).apply_symm_apply
        ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
  right_inv z := by
    rcases z with ⟨R, pi⟩
    let e : Fin b ≃o ↥R.1 := R.1.orderIsoOfFin R.2
    let f : Fin b ↪ α :=
      ⟨fun i => (e (pi i) : α),
        fun i j h => pi.injective (e.injective (Subtype.ext h))⟩
    have hRange : Finset.univ.image f = R.1 := by
      ext a
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact (e (pi i)).property
      · intro ha
        refine ⟨pi.symm (e.symm ⟨a, ha⟩), ?_⟩
        change (e (pi (pi.symm (e.symm ⟨a, ha⟩))) : α) = a
        rw [pi.apply_symm_apply]
        exact congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩)
    have hfcard : (Finset.univ.image f).card = b := by
      rw [Finset.card_image_of_injective _ f.injective,
        Finset.card_univ, Fintype.card_fin]
    apply Prod.ext
    · exact Subtype.ext hRange
    · apply Equiv.ext
      intro i
      change ((Finset.univ.image f).orderIsoOfFin hfcard).symm
          ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩ = pi i
      have hcanonical :
          R.1.orderEmbOfFin R.2 =
            (Finset.univ.image f).orderEmbOfFin hfcard := by
        apply Finset.orderEmbOfFin_unique' hfcard
        intro j
        rw [hRange]
        exact Finset.orderEmbOfFin_mem R.1 R.2 j
      apply (Finset.univ.image f).orderEmbOfFin hfcard |>.injective
      calc
        (Finset.univ.image f).orderEmbOfFin hfcard
            (((Finset.univ.image f).orderIsoOfFin hfcard).symm
              ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩) =
            f i := by
              exact congrArg Subtype.val
                (((Finset.univ.image f).orderIsoOfFin hfcard).apply_symm_apply
                  ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
        _ = R.1.orderEmbOfFin R.2 (pi i) := by rfl
        _ = (Finset.univ.image f).orderEmbOfFin hfcard (pi i) := by
          rw [hcanonical]

theorem prod_embeddingSubsetPermEquiv_symm
    (b : ℕ) (α : Type*) [LinearOrder α]
    (w : α → ℂ) (R : CardSubset b α)
    (pi : Equiv.Perm (Fin b)) :
    (∏ i, w ((R.1.orderIsoOfFin R.2) (pi i))) =
      ∏ a ∈ R.1, w a := by
  let e : Fin b ≃ ↥R.1 := pi.trans (R.1.orderIsoOfFin R.2).toEquiv
  calc
    (∏ i, w ((R.1.orderIsoOfFin R.2) (pi i))) =
        ∏ a : ↥R.1, w a := by
      exact Fintype.prod_equiv e
        (fun i : Fin b => w ((R.1.orderIsoOfFin R.2) (pi i)))
        (fun a : ↥R.1 => w a) (fun i => rfl)
    _ = ∏ a ∈ R.1, w a := Finset.prod_coe_sort R.1 w


variable {X : Type} {A : Type*} [Fintype X]

/-- Unnormalized projection of a complex class function onto the sign character. -/
def complexAlternatingMass (χ : Equiv.Perm X → ℂ) : ℂ :=
  ∑ σ : Equiv.Perm X, (realSign σ : ℂ) * χ σ

/-- The signed complex trace retains exactly the injective words. -/
theorem sum_sign_complexWordCharacter (w : A → ℂ) (hw : Summable w) :
    complexAlternatingMass (complexWordCharacter (X := X) w) =
      ∑' x : X → A, if Function.Injective x then complexWordWeight w x else 0 := by
  simp only [complexAlternatingMass, complexWordCharacter, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum
    (fun σ _ => (summable_complexFixedWordWeight w hw σ).mul_left (realSign σ : ℂ))]
  apply tsum_congr
  intro x
  have hs : (∑ σ : Equiv.Perm X, if x ∘ σ = x then (realSign σ : ℂ) else 0) =
      if Function.Injective x then 1 else 0 := by
    have h := congrArg Complex.ofReal (stabilizerSignSum_eq x)
    simpa only [stabilizerSignSum, Complex.ofReal_sum, apply_ite,
      Complex.ofReal_zero, Complex.ofReal_one] using h
  calc
    _ = (∑ σ : Equiv.Perm X, if x ∘ σ = x then (realSign σ : ℂ) else 0) *
        complexWordWeight w x := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ _
      split_ifs <;> simp
    _ = _ := by rw [hs]; split_ifs <;> simp

/-- Passing from all words to embeddings removes the zero terms from repeated letters. -/
theorem tsum_injective_complexWordWeight (w : A → ℂ) :
    (∑' x : X → A, if Function.Injective x then complexWordWeight w x else 0) =
      ∑' f : X ↪ A, complexWordWeight w f := by
  let c : (X ↪ A) → (X → A) := fun f => f
  have hc : Function.Injective c := fun f g h => Function.Embedding.ext (congrFun h)
  let g : (X → A) → ℂ := fun x => if Function.Injective x then complexWordWeight w x else 0
  have hs : Function.support g ⊆ Set.range c := by
    intro x hx
    have hi : Function.Injective x := by
      by_contra hn
      exact hx (if_neg hn)
    exact ⟨⟨x, hi⟩, rfl⟩
  change (∑' x, g x) = _
  rw [← hc.tsum_eq hs]
  apply tsum_congr
  intro f
  exact if_pos f.injective

/-- An injection is an unordered finite subset together with one of its factorial orderings. -/
theorem tsum_embedding_complexWordWeight [LinearOrder A] (w : A → ℂ)
    (hw : Summable w) (n : ℕ) :
    (∑' f : Fin n ↪ A, complexWordWeight w f) =
      (n.factorial : ℂ) * ∑' S : CardSubset n A, ∏ a ∈ S.val, w a := by
  let e := embeddingSubsetPermEquiv n A
  have he (p : CardSubset n A × Equiv.Perm (Fin n)) :
      complexWordWeight w (e.symm p) = ∏ a ∈ p.1.val, w a :=
    prod_embeddingSubsetPermEquiv_symm n A w p.1 p.2
  have hc : Function.Injective (fun f : Fin n ↪ A => (f : Fin n → A)) :=
    fun f g h => Function.Embedding.ext (congrFun h)
  have hs : Summable (fun f : Fin n ↪ A => complexWordWeight w f) :=
    (summable_complexWordWeight w hw).comp_injective hc
  have hp : Summable (fun p : CardSubset n A × Equiv.Perm (Fin n) =>
      ∏ a ∈ p.1.val, w a) := by
    have h := (e.symm.summable_iff
      (f := fun f : Fin n ↪ A => complexWordWeight w f)).mpr hs
    exact h.congr he
  rw [← e.symm.tsum_eq (fun f : Fin n ↪ A => complexWordWeight w f)]
  simp only [he]
  rw [hp.tsum_prod]
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : Fintype.card (Equiv.Perm (Fin n)) = n.factorial := by
    simpa using Fintype.card_equiv (Equiv.refl (Fin n))
  simp only [hn, ← tsum_mul_left]

/-- The alternating trace is factorial times its elementary-symmetric color mass. -/
theorem sum_sign_complexWordCharacter_eq_subset [LinearOrder A] (w : A → ℂ)
    (hw : Summable w) (n : ℕ) :
    complexAlternatingMass (complexWordCharacter (X := Fin n) w) =
      (n.factorial : ℂ) * ∑' S : CardSubset n A, ∏ a ∈ S.val, w a := by
  rw [sum_sign_complexWordCharacter w hw, tsum_injective_complexWordWeight,
    tsum_embedding_complexWordWeight w hw]


end GaloisForLFunctions.SymmetricCharacters
