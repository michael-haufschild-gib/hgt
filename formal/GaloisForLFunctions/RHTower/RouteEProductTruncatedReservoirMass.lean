import GaloisForLFunctions.RHTower.RouteESourceFaithfulEulerTiltUnitShell
import GaloisForLFunctions.RHTower.Sieve.MertensSecondSharp
import GaloisForLFunctions.RHTower.Sieve.PrimeWindow
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Route E product-truncated reservoir harmonic mass

This module proves the sharp weighted birthday-collision inequality, the exact marked-subset
first-moment identity, and the logarithmic Markov tail bound.  Their prime-reservoir specialization
is the paper theorem: product truncation retains the normalized elementary-symmetric harmonic mass
up to the explicit `choose b 2` collision loss and `b A / (S log T)` energy-tail loss.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

abbrev BreadthSubset (b : ℕ) (α : Type*) [DecidableEq α] :=
  {R : Finset α // R.card = b}

/-- Every injection is its range and the permutation comparing it with increasing order. -/
def embeddingRangePermEquiv
    (b : ℕ) (α : Type*) [Fintype α] [LinearOrder α] :
    (Fin b ↪ α) ≃ BreadthSubset b α × Equiv.Perm (Fin b) where
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

theorem prod_embedding_eq_prod_range
    (b : ℕ) (α : Type*) [Fintype α] [LinearOrder α]
    (w : α → ℝ) (R : BreadthSubset b α)
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

theorem sum_injective_tuple_mass
    (b : ℕ) (α : Type*) [Fintype α] [LinearOrder α]
    (w : α → ℝ) :
    (∑ f : Fin b ↪ α, ∏ i, w (f i)) =
      (b.factorial : ℝ) *
        ∑ R : BreadthSubset b α, ∏ a ∈ R.1, w a := by
  rw [Fintype.sum_equiv (embeddingRangePermEquiv b α)
    (fun f : Fin b ↪ α => ∏ i, w (f i))
    (fun z : BreadthSubset b α × Equiv.Perm (Fin b) =>
      ∏ a ∈ z.1.1, w a)]
  · rw [Fintype.sum_prod_type]
    simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro R hR
    have hcardperm :
        Fintype.card (Equiv.Perm (Fin b)) = b.factorial := by
      simpa using Fintype.card_equiv (Equiv.refl (Fin b))
    rw [hcardperm]
  · intro f
    let E := embeddingRangePermEquiv b α
    let z := E f
    have hback : E.symm z = f := E.symm_apply_apply f
    calc
      (∏ i, w (f i)) = ∏ i, w (E.symm z i) := by rw [hback]
      _ = ∏ a ∈ z.1.1, w a := by
        change (∏ i, w ((z.1.1.orderIsoOfFin z.1.2) (z.2 i))) =
          ∏ a ∈ z.1.1, w a
        exact prod_embedding_eq_prod_range b α w z.1 z.2


def functionPairRemainderEquiv
    (n : ℕ) (ι α : Type*) (e : (Fin 2 ⊕ Fin n) ≃ ι) :
    (ι → α) ≃ (Fin 2 → α) × (Fin n → α) :=
  (Equiv.arrowCongr e.symm (Equiv.refl α)).trans
    (Equiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin n => α))

theorem prod_reindex_pair_remainder
    (n : ℕ) (ι α : Type*) [Fintype ι]
    (e : (Fin 2 ⊕ Fin n) ≃ ι) (w : α → ℝ)
    (f : ι → α) :
    (∏ i, w (f i)) =
      (w (f (e (Sum.inl 0))) * w (f (e (Sum.inl 1)))) *
        ∏ j : Fin n, w (f (e (Sum.inr j))) := by
  calc
    (∏ i, w (f i)) = ∏ k : Fin 2 ⊕ Fin n, w (f (e k)) := by
      exact Fintype.prod_equiv e
        (fun k : Fin 2 ⊕ Fin n => w (f (e k)))
        (fun i : ι => w (f i)) (fun k => rfl) |>.symm
    _ = (∏ i : Fin 2, w (f (e (Sum.inl i)))) *
          ∏ j : Fin n, w (f (e (Sum.inr j))) := by
      rw [Fintype.prod_sum_type]
    _ = _ := by rw [Fin.prod_univ_two]

theorem pairCollisionMass_eq
    (n : ℕ) (ι α : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (e : (Fin 2 ⊕ Fin n) ≃ ι) (w : α → ℝ) :
    (∑ f : ι → α,
      if f (e (Sum.inl 0)) = f (e (Sum.inl 1))
      then ∏ i, w (f i) else 0) =
      (∑ a, w a ^ (2 : ℕ)) * (∑ a, w a) ^ n := by
  rw [Fintype.sum_equiv (functionPairRemainderEquiv n ι α e)
    (fun f : ι → α =>
      if f (e (Sum.inl 0)) = f (e (Sum.inl 1))
      then ∏ i, w (f i) else 0)
    (fun z : (Fin 2 → α) × (Fin n → α) =>
      if z.1 0 = z.1 1
      then (w (z.1 0) * w (z.1 1)) * ∏ j, w (z.2 j)
      else 0)]
  · rw [Fintype.sum_prod_type]
    have hinner : ∀ g : Fin 2 → α,
        (∑ h : Fin n → α,
          if g 0 = g 1
          then (w (g 0) * w (g 1)) * ∏ j, w (h j)
          else 0) =
        (if g 0 = g 1 then w (g 0) * w (g 1) else 0) *
          ∑ h : Fin n → α, ∏ j, w (h j) := by
      intro g
      by_cases hg : g 0 = g 1
      · simp only [hg, ↓reduceIte, Finset.mul_sum]
      · simp [hg]
    simp_rw [hinner]
    rw [← Finset.sum_mul]
    congr 1
    · calc
        (∑ g : Fin 2 → α, if g 0 = g 1 then w (g 0) * w (g 1) else 0) =
            ∑ g ∈ Finset.image (fun a : α => fun _ : Fin 2 => a) Finset.univ,
              if g 0 = g 1 then w (g 0) * w (g 1) else 0 := by
                symm
                apply Finset.sum_subset_zero_on_sdiff
                · exact Finset.image_subset_iff.mpr fun a ha => Finset.mem_univ _
                · intro g hg
                  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hg
                  have hne : g 0 ≠ g 1 := by
                    intro heq
                    apply hg
                    refine Finset.mem_image.mpr ⟨g 0, Finset.mem_univ _, ?_⟩
                    funext i
                    fin_cases i <;> simp [heq]
                  simp [hne]
                · intro g hg
                  rfl
        _ = ∑ a : α,
              if (fun _ : Fin 2 => a) 0 = (fun _ : Fin 2 => a) 1
              then w ((fun _ : Fin 2 => a) 0) * w ((fun _ : Fin 2 => a) 1)
              else 0 := by
                apply Finset.sum_image
                exact Set.injOn_of_injective fun a b h => congrFun h 0
        _ = ∑ a : α, w a ^ (2 : ℕ) := by
              apply Finset.sum_congr rfl
              intro a ha
              simp [pow_two]
    · rw [Fintype.sum_pow]
  · intro f
    simp only [functionPairRemainderEquiv, Equiv.trans_apply,
      Equiv.arrowCongr_apply, Function.comp_apply,
      Equiv.sumPiEquivProdPi_apply]
    rw [prod_reindex_pair_remainder n ι α e w f]
    simp

/-! ## Pair coordinates inside a finite breadth -/

/-- Canonical decomposition of `Fin b` into a selected pair and its complement. -/
def pairCoordinateEquiv
    (b : ℕ) (U : BreadthSubset 2 (Fin b)) :
    (Fin 2 ⊕ Fin (b - 2)) ≃ Fin b := by
  let ePair : Fin 2 ≃ {i : Fin b // i ∈ U.1} :=
    (U.1.orderIsoOfFin U.2).toEquiv
  have hcomp :
      Fintype.card {i : Fin b // i ∉ U.1} = b - 2 := by
    rw [Fintype.card_subtype_compl]
    simp [U.2]
  let eComp : Fin (b - 2) ≃ {i : Fin b // i ∉ U.1} :=
    Fintype.equivOfCardEq (by simp [hcomp])
  exact (Equiv.sumCongr ePair eComp).trans
    (Equiv.sumCompl fun i : Fin b => i ∈ U.1)

theorem pairCoordinateEquiv_inl_mem
    (b : ℕ) (U : BreadthSubset 2 (Fin b)) (i : Fin 2) :
    pairCoordinateEquiv b U (Sum.inl i) ∈ U.1 := by
  simp [pairCoordinateEquiv]

theorem pairCoordinateEquiv_pair_ne
    (b : ℕ) (U : BreadthSubset 2 (Fin b)) :
    pairCoordinateEquiv b U (Sum.inl 0) ≠
      pairCoordinateEquiv b U (Sum.inl 1) := by
  intro h
  have := (pairCoordinateEquiv b U).injective h
  exact Fin.zero_ne_one (Sum.inl.inj this)

/-- Breadth subsets are precisely members of `powersetCard` of the full finite type. -/
def breadthSubsetEquivPowersetCard
    (b : ℕ) (α : Type*) [Fintype α] [DecidableEq α] :
    BreadthSubset b α ≃
      ↥((Finset.univ : Finset α).powersetCard b) where
  toFun R := ⟨R.1, Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ R.1, R.2⟩⟩
  invFun R := ⟨R.1, (Finset.mem_powersetCard.mp R.2).2⟩
  left_inv R := by ext; rfl
  right_inv R := by ext; rfl

theorem card_breadthSubset
    (b : ℕ) (α : Type*) [Fintype α] [DecidableEq α] :
    Fintype.card (BreadthSubset b α) =
      (Fintype.card α).choose b := by
  rw [Fintype.card_congr (breadthSubsetEquivPowersetCard b α),
    Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ]

def tupleWeight
    {α ι : Type*} [Fintype ι] (w : α → ℝ) (f : ι → α) : ℝ :=
  ∏ i, w (f i)

def injectiveTupleWeight
    {α ι : Type*} [Fintype ι] [DecidableEq α]
    (w : α → ℝ) (f : ι → α) : ℝ :=
  if Function.Injective f then tupleWeight w f else 0

def pairCollisionWeight
    {α : Type*} [DecidableEq α]
    (b : ℕ) (w : α → ℝ) (U : BreadthSubset 2 (Fin b))
    (f : Fin b → α) : ℝ :=
  if (f (pairCoordinateEquiv b U (Sum.inl 0)) =
      f (pairCoordinateEquiv b U (Sum.inl 1)))
  then tupleWeight w f else 0

theorem tupleWeight_nonneg
    {α ι : Type*} [Fintype ι] (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (f : ι → α) :
    0 ≤ tupleWeight w f := by
  exact Finset.prod_nonneg fun i hi => hw (f i)

theorem pairCollisionWeight_nonneg
    {α : Type*} [DecidableEq α]
    (b : ℕ) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (U : BreadthSubset 2 (Fin b)) (f : Fin b → α) :
    0 ≤ pairCollisionWeight b w U f := by
  unfold pairCollisionWeight
  split_ifs
  · exact tupleWeight_nonneg w hw f
  · exact le_rfl

theorem noninjective_exists_pairCollision
    {α : Type*} (b : ℕ) (f : Fin b → α) (hf : ¬Function.Injective f) :
    ∃ U : BreadthSubset 2 (Fin b),
      f (pairCoordinateEquiv b U (Sum.inl 0)) =
        f (pairCoordinateEquiv b U (Sum.inl 1)) := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hf
  let U : BreadthSubset 2 (Fin b) := ⟨{i, j}, Finset.card_pair hne⟩
  refine ⟨U, ?_⟩
  have hconst : ∀ k ∈ U.1, f k = f i := by
    intro k hk
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · rfl
    · exact hij.symm
  calc
    f (pairCoordinateEquiv b U (Sum.inl 0)) = f i :=
      hconst _ (pairCoordinateEquiv_inl_mem b U 0)
    _ = f (pairCoordinateEquiv b U (Sum.inl 1)) :=
      (hconst _ (pairCoordinateEquiv_inl_mem b U 1)).symm

/-- Pointwise weighted birthday union bound. -/
theorem tupleWeight_le_injective_add_pairCollisions
    {α : Type*} [DecidableEq α]
    (b : ℕ) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (f : Fin b → α) :
    tupleWeight w f ≤ injectiveTupleWeight w f +
      ∑ U : BreadthSubset 2 (Fin b),
        pairCollisionWeight (α := α) b w U f := by
  by_cases hf : Function.Injective f
  · rw [injectiveTupleWeight, if_pos hf]
    exact le_add_of_nonneg_right
      (Fintype.sum_nonneg fun U =>
        pairCollisionWeight_nonneg (α := α) b w hw U f)
  · rw [injectiveTupleWeight, if_neg hf, zero_add]
    obtain ⟨U, hU⟩ := noninjective_exists_pairCollision b f hf
    calc
      tupleWeight w f = pairCollisionWeight (α := α) b w U f := by
        simp [pairCollisionWeight, hU]
      _ ≤ ∑ V : BreadthSubset 2 (Fin b),
          pairCollisionWeight (α := α) b w V f := by
        simpa only using (Finset.single_le_sum
          (s := (Finset.univ : Finset (BreadthSubset 2 (Fin b))))
          (fun V hV =>
            pairCollisionWeight_nonneg (α := α) b w hw V f)
          (Finset.mem_univ U))

theorem sum_tupleWeight
    (b : ℕ) (α : Type*) [Fintype α] [DecidableEq α]
    (w : α → ℝ) :
    (∑ f : Fin b → α, tupleWeight w f) = (∑ a, w a) ^ b := by
  simpa [tupleWeight] using (Fintype.sum_pow w b).symm

theorem sum_injectiveTupleWeight
    (b : ℕ) (α : Type*) [Fintype α] [LinearOrder α]
    (w : α → ℝ) :
    (∑ f : Fin b → α, injectiveTupleWeight w f) =
      (b.factorial : ℝ) *
        ∑ R : BreadthSubset b α, ∏ a ∈ R.1, w a := by
  calc
    (∑ f : Fin b → α, injectiveTupleWeight w f) =
        ∑ f : {f : Fin b → α // Function.Injective f},
          tupleWeight w f.1 := by
            calc
              (∑ f : Fin b → α, injectiveTupleWeight w f) =
                  ∑ f ∈ (Finset.univ.filter Function.Injective),
                    tupleWeight w f := by
                      exact (Finset.sum_filter Function.Injective
                        (tupleWeight w)).symm
              _ = ∑ f : {f : Fin b → α // Function.Injective f},
                    tupleWeight w f.1 := by
                      simpa using
                        (Finset.sum_subtype_eq_sum_filter
                          (s := Finset.univ)
                          (p := fun f : Fin b → α => Function.Injective f)
                          (fun f : Fin b → α => tupleWeight w f)).symm
    _ = ∑ f : Fin b ↪ α, ∏ i, w (f i) := by
      apply Fintype.sum_equiv
        (Equiv.subtypeInjectiveEquivEmbedding (Fin b) α)
        (fun f : {f : Fin b → α // Function.Injective f} =>
          tupleWeight w f.1)
        (fun f : Fin b ↪ α => ∏ i, w (f i))
      intro f
      simp [tupleWeight, Equiv.subtypeInjectiveEquivEmbedding]
    _ = (b.factorial : ℝ) *
        ∑ R : BreadthSubset b α, ∏ a ∈ R.1, w a :=
      sum_injective_tuple_mass b α w

theorem sum_pairCollisionWeight
    (b : ℕ) (α : Type*) [Fintype α] [DecidableEq α]
    (w : α → ℝ) :
    (∑ U : BreadthSubset 2 (Fin b),
      ∑ f : Fin b → α, pairCollisionWeight b w U f) =
      ((b.choose 2 : ℕ) : ℝ) *
        ((∑ a, w a ^ (2 : ℕ)) * (∑ a, w a) ^ (b - 2)) := by
  calc
    (∑ U : BreadthSubset 2 (Fin b),
        ∑ f : Fin b → α, pairCollisionWeight b w U f) =
        ∑ U : BreadthSubset 2 (Fin b),
          ((∑ a, w a ^ (2 : ℕ)) * (∑ a, w a) ^ (b - 2)) := by
            apply Finset.sum_congr rfl
            intro U hU
            simpa [pairCollisionWeight, tupleWeight] using
              pairCollisionMass_eq (b - 2) (Fin b) α
                (pairCoordinateEquiv b U) w
    _ = ((b.choose 2 : ℕ) : ℝ) *
        ((∑ a, w a ^ (2 : ℕ)) * (∑ a, w a) ^ (b - 2)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        card_breadthSubset]
      simp [Fintype.card_fin]

/-- Sharp finite weighted birthday-collision bound. -/
theorem weightedBirthdayCollisionBound
    (b : ℕ) (α : Type*) [Fintype α] [LinearOrder α]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) :
    (∑ a, w a) ^ b ≤
      (b.factorial : ℝ) *
          (∑ R : BreadthSubset b α, ∏ a ∈ R.1, w a) +
        ((b.choose 2 : ℕ) : ℝ) *
          ((∑ a, w a ^ (2 : ℕ)) * (∑ a, w a) ^ (b - 2)) := by
  have hsum :
      (∑ f : Fin b → α, tupleWeight w f) ≤
        ∑ f : Fin b → α,
          (injectiveTupleWeight w f +
            ∑ U : BreadthSubset 2 (Fin b), pairCollisionWeight b w U f) := by
    apply Finset.sum_le_sum
    intro f hf
    exact tupleWeight_le_injective_add_pairCollisions b w hw f
  rw [sum_tupleWeight, Finset.sum_add_distrib,
    sum_injectiveTupleWeight] at hsum
  rw [Finset.sum_comm, sum_pairCollisionWeight] at hsum
  exact hsum

/-! ## Marked-subset first moment -/

def weightedPowersetMass
    {α : Type*} [DecidableEq α]
    (s : Finset α) (b : ℕ) (w : α → ℝ) : ℝ :=
  ∑ R ∈ s.powersetCard b, ∏ a ∈ R, w a

def weightedPowersetFirstMoment
    {α : Type*} [DecidableEq α]
    (s : Finset α) (b : ℕ) (w energy : α → ℝ) : ℝ :=
  ∑ R ∈ s.powersetCard b,
    (∏ a ∈ R, w a) * ∑ a ∈ R, energy a

/-- Marking one member converts a breadth-`b` first moment into an insertion sum. -/
theorem weightedPowersetFirstMoment_marked
    {α : Type*} [DecidableEq α]
    (s : Finset α) (b : ℕ) (hb : 0 < b) (w energy : α → ℝ) :
    weightedPowersetFirstMoment s b w energy =
      ∑ T ∈ s.powersetCard (b - 1),
        ∑ a ∈ s with a ∉ T,
          w a * energy a * ∏ q ∈ T, w q := by
  unfold weightedPowersetFirstMoment
  calc
    (∑ R ∈ s.powersetCard b,
        (∏ a ∈ R, w a) * ∑ a ∈ R, energy a) =
      ∑ R ∈ s.powersetCard b,
        ∑ a ∈ R, w a * energy a * ∏ q ∈ R.erase a, w q := by
          apply Finset.sum_congr rfl
          intro R hR
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          rw [← Finset.mul_prod_erase R w ha]
          ring
    _ = ∑ (R ∈ s.powersetCard b) (a ∈ s) with a ∈ R,
        w a * energy a * ∏ q ∈ R.erase a, w q := by
          rw [← Finset.sum_finset_product']
          grind
    _ = ∑ (T ∈ s.powersetCard (b - 1)) (a ∈ s) with a ∉ T,
        w a * energy a * ∏ q ∈ T, w q := by
          apply Finset.sum_bij'
            (fun ⟨R, a⟩ _ => ⟨R.erase a, a⟩)
            (fun ⟨T, a⟩ _ => ⟨insert a T, a⟩)
          all_goals
            simp_all [Finset.mem_powersetCard, Finset.insert_erase]
          all_goals grind
    _ = ∑ T ∈ s.powersetCard (b - 1),
        ∑ a ∈ s with a ∉ T,
          w a * energy a * ∏ q ∈ T, w q := by
            rw [← Finset.sum_finset_product']
            grind

theorem weightedElementarySymmetricUpper
    (b : ℕ) (α : Type*) [Fintype α] [LinearOrder α]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) :
    (b.factorial : ℝ) *
        (∑ R : BreadthSubset b α, ∏ a ∈ R.1, w a) ≤
      (∑ a, w a) ^ b := by
  have hsum :
      (∑ f : Fin b → α, injectiveTupleWeight w f) ≤
        ∑ f : Fin b → α, tupleWeight w f := by
    apply Finset.sum_le_sum
    intro f hf
    unfold injectiveTupleWeight
    by_cases hinj : Function.Injective f
    · rw [if_pos hinj]
    · rw [if_neg hinj]
      exact tupleWeight_nonneg w hw f
  rw [sum_injectiveTupleWeight, sum_tupleWeight] at hsum
  exact hsum

theorem sum_breadthSubset_eq_weightedPowersetMass_univ
    (b : ℕ) (α : Type*) [Fintype α] [LinearOrder α]
    (w : α → ℝ) :
    (∑ R : BreadthSubset b α, ∏ a ∈ R.1, w a) =
      weightedPowersetMass Finset.univ b w := by
  unfold weightedPowersetMass
  rw [Fintype.sum_equiv (breadthSubsetEquivPowersetCard b α)
    (fun R : BreadthSubset b α => ∏ a ∈ R.1, w a)
    (fun R : ↥((Finset.univ : Finset α).powersetCard b) =>
      ∏ a ∈ R.1, w a)]
  · exact Finset.sum_coe_sort
      ((Finset.univ : Finset α).powersetCard b)
      (fun R : Finset α => ∏ a ∈ R, w a)
  · intro R
    rfl

theorem weightedPowersetMass_upper
    (b : ℕ) (α : Type*) [Fintype α] [LinearOrder α]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) :
    (b.factorial : ℝ) * weightedPowersetMass Finset.univ b w ≤
      (∑ a, w a) ^ b := by
  rw [← sum_breadthSubset_eq_weightedPowersetMass_univ]
  exact weightedElementarySymmetricUpper b α w hw

/-- Marked first moment is controlled by one energy moment and one lower-breadth mass. -/
theorem weightedPowersetFirstMoment_le_energy_mul_mass
    (b : ℕ) (hb : 0 < b) (α : Type*) [Fintype α] [LinearOrder α]
    (w energy : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (henergy : ∀ a, 0 ≤ energy a) :
    weightedPowersetFirstMoment Finset.univ b w energy ≤
      (∑ a, w a * energy a) *
        weightedPowersetMass Finset.univ (b - 1) w := by
  rw [weightedPowersetFirstMoment_marked Finset.univ b hb]
  unfold weightedPowersetMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T hT
  have hprod : 0 ≤ ∏ q ∈ T, w q :=
    Finset.prod_nonneg fun q hq => hw q
  calc
    (∑ a ∈ Finset.univ with a ∉ T,
        w a * energy a * ∏ q ∈ T, w q) ≤
      ∑ a ∈ Finset.univ,
        w a * energy a * ∏ q ∈ T, w q := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro a ha hnot
            exact mul_nonneg (mul_nonneg (hw a) (henergy a)) hprod
    _ = (∑ a, w a * energy a) * ∏ q ∈ T, w q := by
      rw [Finset.sum_mul]
    _ = (∑ a, w a * energy a) *
        (∏ q ∈ T, w q) := rfl

theorem weightedPowersetFirstMoment_upper
    (b : ℕ) (hb : 0 < b) (α : Type*) [Fintype α] [LinearOrder α]
    (w energy : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (henergy : ∀ a, 0 ≤ energy a) :
    weightedPowersetFirstMoment Finset.univ b w energy ≤
      (∑ a, w a * energy a) *
        ((∑ a, w a) ^ (b - 1) / ((b - 1).factorial : ℝ)) := by
  have hmoment := weightedPowersetFirstMoment_le_energy_mul_mass
    b hb α w energy hw henergy
  have hmass := weightedPowersetMass_upper (b - 1) α w hw
  have hfact : (0 : ℝ) < ((b - 1).factorial : ℕ) := by
    exact_mod_cast Nat.factorial_pos (b - 1)
  have hmass' : weightedPowersetMass Finset.univ (b - 1) w ≤
      (∑ a, w a) ^ (b - 1) / ((b - 1).factorial : ℝ) := by
    apply (le_div_iff₀ hfact).2
    simpa [mul_comm] using hmass
  have hA : 0 ≤ ∑ a, w a * energy a :=
    Fintype.sum_nonneg fun a => mul_nonneg (hw a) (henergy a)
  exact hmoment.trans (mul_le_mul_of_nonneg_left hmass' hA)

def weightedTruncatedPowersetMass
    {α : Type*} [DecidableEq α]
    (s : Finset α) (b : ℕ) (w energy : α → ℝ) (L : ℝ) : ℝ :=
  ∑ R ∈ s.powersetCard b,
    if (∑ a ∈ R, energy a) ≤ L then ∏ a ∈ R, w a else 0

def weightedPowersetTail
    {α : Type*} [DecidableEq α]
    (s : Finset α) (b : ℕ) (w energy : α → ℝ) (L : ℝ) : ℝ :=
  ∑ R ∈ s.powersetCard b,
    if L < ∑ a ∈ R, energy a then ∏ a ∈ R, w a else 0

theorem weightedPowersetMass_eq_truncated_add_tail
    {α : Type*} [DecidableEq α]
    (s : Finset α) (b : ℕ) (w energy : α → ℝ) (L : ℝ) :
    weightedPowersetMass s b w =
      weightedTruncatedPowersetMass s b w energy L +
        weightedPowersetTail s b w energy L := by
  unfold weightedPowersetMass weightedTruncatedPowersetMass
    weightedPowersetTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro R hR
  by_cases h : (∑ a ∈ R, energy a) ≤ L
  · simp [h, not_lt_of_ge h]
  · have hlt : L < ∑ a ∈ R, energy a := lt_of_not_ge h
    simp [h, hlt]

theorem weightedPowersetTail_mul_le_firstMoment
    {α : Type*} [DecidableEq α]
    (s : Finset α) (b : ℕ) (w energy : α → ℝ) (L : ℝ)
    (hw : ∀ a, 0 ≤ w a) (henergy : ∀ a, 0 ≤ energy a) :
    weightedPowersetTail s b w energy L * L ≤
      weightedPowersetFirstMoment s b w energy := by
  unfold weightedPowersetTail weightedPowersetFirstMoment
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro R hR
  have hprod : 0 ≤ ∏ a ∈ R, w a :=
    Finset.prod_nonneg fun a ha => hw a
  have hE : 0 ≤ ∑ a ∈ R, energy a :=
    Finset.sum_nonneg fun a ha => henergy a
  by_cases htail : L < ∑ a ∈ R, energy a
  · rw [if_pos htail]
    exact mul_le_mul_of_nonneg_left htail.le hprod
  · rw [if_neg htail]
    simpa using mul_nonneg hprod hE

theorem weightedPowersetTail_le_firstMoment_div
    {α : Type*} [DecidableEq α]
    (s : Finset α) (b : ℕ) (w energy : α → ℝ) (L : ℝ)
    (hL : 0 < L) (hw : ∀ a, 0 ≤ w a)
    (henergy : ∀ a, 0 ≤ energy a) :
    weightedPowersetTail s b w energy L ≤
      weightedPowersetFirstMoment s b w energy / L := by
  exact (le_div_iff₀ hL).2
    (weightedPowersetTail_mul_le_firstMoment s b w energy L hw henergy)

/-- Denominator-free product-truncated reservoir lower bound. -/
theorem weightedProductTruncationLowerBound
    (b : ℕ) (hb : 0 < b) (α : Type*) [Fintype α] [LinearOrder α]
    (w energy : α → ℝ) (L : ℝ) (hL : 0 < L)
    (hw : ∀ a, 0 ≤ w a) (henergy : ∀ a, 0 ≤ energy a) :
    weightedTruncatedPowersetMass Finset.univ b w energy L ≥
      ((∑ a, w a) ^ b -
          ((b.choose 2 : ℕ) : ℝ) *
            ((∑ a, w a ^ (2 : ℕ)) * (∑ a, w a) ^ (b - 2))) /
        (b.factorial : ℝ) -
      ((∑ a, w a * energy a) *
          ((∑ a, w a) ^ (b - 1) /
            ((b - 1).factorial : ℝ))) / L := by
  let full := weightedPowersetMass Finset.univ b w
  let truncated := weightedTruncatedPowersetMass
    Finset.univ b w energy L
  let tail := weightedPowersetTail Finset.univ b w energy L
  let collision := ((b.choose 2 : ℕ) : ℝ) *
    ((∑ a, w a ^ (2 : ℕ)) * (∑ a, w a) ^ (b - 2))
  have hfact : (0 : ℝ) < (b.factorial : ℕ) := by
    exact_mod_cast Nat.factorial_pos b
  have hcollision := weightedBirthdayCollisionBound b α w hw
  rw [sum_breadthSubset_eq_weightedPowersetMass_univ] at hcollision
  have hfullLower : ((∑ a, w a) ^ b - collision) /
      (b.factorial : ℝ) ≤ full := by
    apply (div_le_iff₀ hfact).2
    dsimp [full, collision]
    nlinarith
  have htailMoment : tail ≤
      weightedPowersetFirstMoment Finset.univ b w energy / L := by
    exact weightedPowersetTail_le_firstMoment_div
      Finset.univ b w energy L hL hw henergy
  have hmoment := weightedPowersetFirstMoment_upper
    b hb α w energy hw henergy
  have htailUpper : tail ≤
      ((∑ a, w a * energy a) *
        ((∑ a, w a) ^ (b - 1) /
          ((b - 1).factorial : ℝ))) / L :=
    htailMoment.trans ((div_le_div_iff_of_pos_right hL).2 hmoment)
  have hsplit : full = truncated + tail := by
    exact weightedPowersetMass_eq_truncated_add_tail
      Finset.univ b w energy L
  dsimp [truncated] at hsplit ⊢
  dsimp [full, tail] at hsplit hfullLower htailUpper
  linarith

/-- Paper-normalized form of the product-truncation law. -/
theorem weightedProductTruncationLowerBound_normalized
    (b : ℕ) (hb : 0 < b) (α : Type*) [Fintype α] [LinearOrder α]
    (w energy : α → ℝ) (L : ℝ) (hL : 0 < L)
    (hw : ∀ a, 0 ≤ w a) (henergy : ∀ a, 0 ≤ energy a)
    (hS : 0 < ∑ a, w a) :
    weightedTruncatedPowersetMass Finset.univ b w energy L ≥
      ((∑ a, w a) ^ b / (b.factorial : ℝ)) *
        (1 - ((b.choose 2 : ℕ) : ℝ) *
            (∑ a, w a ^ (2 : ℕ)) / (∑ a, w a) ^ (2 : ℕ) -
          (b : ℝ) * (∑ a, w a * energy a) /
            ((∑ a, w a) * L)) := by
  have hbase := weightedProductTruncationLowerBound
    b hb α w energy L hL hw henergy
  suffices hnormalize :
      ((∑ a, w a) ^ b / (b.factorial : ℝ)) *
          (1 - ((b.choose 2 : ℕ) : ℝ) *
              (∑ a, w a ^ (2 : ℕ)) / (∑ a, w a) ^ (2 : ℕ) -
            (b : ℝ) * (∑ a, w a * energy a) /
              ((∑ a, w a) * L)) =
        ((∑ a, w a) ^ b -
            ((b.choose 2 : ℕ) : ℝ) *
              ((∑ a, w a ^ (2 : ℕ)) * (∑ a, w a) ^ (b - 2))) /
          (b.factorial : ℝ) -
        ((∑ a, w a * energy a) *
            ((∑ a, w a) ^ (b - 1) /
              ((b - 1).factorial : ℝ))) / L by
    rw [hnormalize]
    exact hbase
  by_cases hb1 : b = 1
  · subst b
    simp
    field_simp [hS.ne', hL.ne']
  · have hb2 : 2 ≤ b := by omega
    have hfac : b.factorial = b * (b - 1).factorial := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
      simp [Nat.factorial_succ]
    have hpow2 : (∑ a, w a) ^ b =
        (∑ a, w a) ^ (b - 2) * (∑ a, w a) ^ (2 : ℕ) := by
      rw [← pow_add]
      congr
      omega
    have hpowPred : (∑ a, w a) ^ (b - 1) =
        (∑ a, w a) ^ (b - 2) * (∑ a, w a) := by
      rw [← pow_succ]
      congr
      omega
    rw [hfac]
    push_cast
    rw [hpow2, hpowPred]
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
    have hpredFact : (0 : ℝ) < ((b - 1).factorial : ℕ) := by
      exact_mod_cast Nat.factorial_pos (b - 1)
    field_simp [hS.ne', hL.ne', hbR, hpredFact.ne']

/-! ## Route E prime-reservoir specialization -/

local instance routeEPrimeLinearOrder : LinearOrder Nat.Primes :=
  LinearOrder.lift' (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective

/-- Valid finite prime reservoir and product cutoff. -/
structure RouteEProductTruncationData where
  P : Finset Nat.Primes
  P_nonempty : P.Nonempty
  b : ℕ
  b_pos : 0 < b
  T : ℝ
  T_gt_one : 1 < T

namespace RouteEProductTruncationData

def harmonicWeight (d : RouteEProductTruncationData) (p : ↥d.P) : ℝ :=
  1 / (p.1 : ℝ)

def logEnergy (d : RouteEProductTruncationData) (p : ↥d.P) : ℝ :=
  Real.log (p.1 : ℕ)

def harmonicSum (d : RouteEProductTruncationData) : ℝ :=
  ∑ p : ↥d.P, d.harmonicWeight p

def harmonicSquareSum (d : RouteEProductTruncationData) : ℝ :=
  ∑ p : ↥d.P, d.harmonicWeight p ^ (2 : ℕ)

def harmonicLogMoment (d : RouteEProductTruncationData) : ℝ :=
  ∑ p : ↥d.P, d.harmonicWeight p * d.logEnergy p

def subsetPrimeProduct
    (d : RouteEProductTruncationData) (R : Finset ↥d.P) : ℝ :=
  ∏ p ∈ R, (p.1 : ℝ)

def productTruncatedHarmonicMass (d : RouteEProductTruncationData) : ℝ :=
  ∑ R ∈ (Finset.univ : Finset ↥d.P).powersetCard d.b,
    if d.subsetPrimeProduct R ≤ d.T
    then ∏ p ∈ R, d.harmonicWeight p else 0

theorem harmonicWeight_pos
    (d : RouteEProductTruncationData) (p : ↥d.P) :
    0 < d.harmonicWeight p := by
  unfold harmonicWeight
  exact one_div_pos.mpr (by exact_mod_cast p.1.2.pos)

theorem logEnergy_nonneg
    (d : RouteEProductTruncationData) (p : ↥d.P) :
    0 ≤ d.logEnergy p := by
  unfold logEnergy
  apply Real.log_nonneg
  exact_mod_cast p.1.2.one_le

theorem harmonicSum_pos (d : RouteEProductTruncationData) :
    0 < d.harmonicSum := by
  unfold harmonicSum
  apply Finset.sum_pos'
  · intro p hp
    exact (d.harmonicWeight_pos p).le
  · obtain ⟨p, hp⟩ := d.P_nonempty
    exact ⟨⟨p, hp⟩, Finset.mem_univ _, d.harmonicWeight_pos ⟨p, hp⟩⟩

theorem log_T_pos (d : RouteEProductTruncationData) :
    0 < Real.log d.T := by
  exact Real.log_pos d.T_gt_one

theorem subsetPrimeProduct_pos
    (d : RouteEProductTruncationData) (R : Finset ↥d.P) :
    0 < d.subsetPrimeProduct R := by
  unfold subsetPrimeProduct
  exact Finset.prod_pos fun p hp => by exact_mod_cast p.1.2.pos

theorem log_subsetPrimeProduct
    (d : RouteEProductTruncationData) (R : Finset ↥d.P) :
    Real.log (d.subsetPrimeProduct R) =
      ∑ p ∈ R, d.logEnergy p := by
  unfold subsetPrimeProduct logEnergy
  rw [Real.log_prod]
  intro p hp
  exact_mod_cast p.1.2.ne_zero

theorem subsetPrimeProduct_le_iff_logEnergy_le
    (d : RouteEProductTruncationData) (R : Finset ↥d.P) :
    d.subsetPrimeProduct R ≤ d.T ↔
      (∑ p ∈ R, d.logEnergy p) ≤ Real.log d.T := by
  rw [← d.log_subsetPrimeProduct R]
  exact (Real.strictMonoOn_log.le_iff_le
    (d.subsetPrimeProduct_pos R) (d.T_gt_one.trans' zero_lt_one)).symm

theorem productTruncatedHarmonicMass_eq_weighted
    (d : RouteEProductTruncationData) :
    d.productTruncatedHarmonicMass =
      weightedTruncatedPowersetMass Finset.univ d.b
        d.harmonicWeight d.logEnergy (Real.log d.T) := by
  unfold productTruncatedHarmonicMass weightedTruncatedPowersetMass
  apply Finset.sum_congr rfl
  intro R hR
  by_cases hprod : d.subsetPrimeProduct R ≤ d.T
  · have hlog := (d.subsetPrimeProduct_le_iff_logEnergy_le R).mp hprod
    simp [hprod, hlog]
  · have hlog : ¬(∑ p ∈ R, d.logEnergy p) ≤ Real.log d.T :=
      fun h => hprod ((d.subsetPrimeProduct_le_iff_logEnergy_le R).mpr h)
    simp [hprod, hlog]

/-- Exact finite Route E product-truncated harmonic-mass law. -/
theorem productTruncatedHarmonicMass_lowerBound
    (d : RouteEProductTruncationData) :
    d.productTruncatedHarmonicMass ≥
      (d.harmonicSum ^ d.b / (d.b.factorial : ℝ)) *
        (1 - ((d.b.choose 2 : ℕ) : ℝ) *
            d.harmonicSquareSum / d.harmonicSum ^ (2 : ℕ) -
          (d.b : ℝ) * d.harmonicLogMoment /
            (d.harmonicSum * Real.log d.T)) := by
  rw [d.productTruncatedHarmonicMass_eq_weighted]
  convert weightedProductTruncationLowerBound_normalized
      d.b d.b_pos ↥d.P d.harmonicWeight d.logEnergy
      (Real.log d.T) d.log_T_pos
      (fun p => (d.harmonicWeight_pos p).le)
      d.logEnergy_nonneg d.harmonicSum_pos using 1
  all_goals simp [harmonicSum, harmonicSquareSum, harmonicLogMoment]
  case e'_3 =>
    unfold weightedTruncatedPowersetMass
    congr

/-- Positive-proportion form of product truncation.  Any certified collision loss `eta` and
logarithmic product-tail loss `delta` subtract additively from full elementary-symmetric mass.
This is the exact finite statement consumed by every cofinal specialization. -/
theorem productTruncatedHarmonicMass_lowerBound_of_normalizedLosses
    (d : RouteEProductTruncationData) {eta delta : ℝ}
    (hcollision :
      ((d.b.choose 2 : ℕ) : ℝ) * d.harmonicSquareSum /
          d.harmonicSum ^ (2 : ℕ) ≤ eta)
    (htail :
      (d.b : ℝ) * d.harmonicLogMoment /
          (d.harmonicSum * Real.log d.T) ≤ delta) :
    d.productTruncatedHarmonicMass ≥
      (d.harmonicSum ^ d.b / (d.b.factorial : ℝ)) *
        (1 - eta - delta) := by
  have hbase :
      0 ≤ d.harmonicSum ^ d.b / (d.b.factorial : ℝ) :=
    div_nonneg (pow_nonneg d.harmonicSum_pos.le d.b) (by positivity)
  have hloss :
      1 - eta - delta ≤
        1 - ((d.b.choose 2 : ℕ) : ℝ) *
            d.harmonicSquareSum / d.harmonicSum ^ (2 : ℕ) -
          (d.b : ℝ) * d.harmonicLogMoment /
            (d.harmonicSum * Real.log d.T) := by
    linarith
  exact (mul_le_mul_of_nonneg_left hloss hbase).trans
    d.productTruncatedHarmonicMass_lowerBound

end RouteEProductTruncationData

/-- Concrete prime window and product cutoff for the cofinal Route E reservoir. -/
structure RouteEPrimeReservoirCofinalData where
  W : ℕ
  U : ℕ
  b : ℕ
  T : ℝ
  W_ge_two : 2 ≤ W
  W_le_U : W ≤ U
  b_pos : 0 < b
  T_gt_one : 1 < T
  reservoir_nonempty : (Sieve.bigPrimeSet W U).Nonempty

namespace RouteEPrimeReservoirCofinalData

def reservoir (d : RouteEPrimeReservoirCofinalData) : Finset ℕ :=
  Sieve.bigPrimeSet d.W d.U

def harmonicSum (d : RouteEPrimeReservoirCofinalData) : ℝ :=
  ∑ p ∈ d.reservoir, 1 / (p : ℝ)

def harmonicSquareSum (d : RouteEPrimeReservoirCofinalData) : ℝ :=
  ∑ p ∈ d.reservoir, (1 / (p : ℝ)) ^ (2 : ℕ)

def harmonicLogMoment (d : RouteEPrimeReservoirCofinalData) : ℝ :=
  ∑ p ∈ d.reservoir, Real.log p / (p : ℝ)

def productTruncatedMass (d : RouteEPrimeReservoirCofinalData) : ℝ :=
  weightedTruncatedPowersetMass Finset.univ d.b
    (fun p : ↥d.reservoir => 1 / (p.1 : ℝ))
    (fun p : ↥d.reservoir => Real.log p.1) (Real.log d.T)

theorem harmonicSum_pos (d : RouteEPrimeReservoirCofinalData) :
    0 < d.harmonicSum := by
  unfold harmonicSum reservoir
  apply Finset.sum_pos'
  · intro p hp
    exact one_div_nonneg.mpr (Nat.cast_nonneg p)
  · obtain ⟨p, hp⟩ := d.reservoir_nonempty
    have hprime := Sieve.prime_of_mem_bigPrimeSet hp
    exact ⟨p, hp, one_div_pos.mpr (by exact_mod_cast hprime.pos)⟩

theorem harmonicLogMoment_nonneg (d : RouteEPrimeReservoirCofinalData) :
    0 ≤ d.harmonicLogMoment := by
  unfold harmonicLogMoment
  apply Finset.sum_nonneg
  intro p hp
  have hprime := Sieve.prime_of_mem_bigPrimeSet hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) (Nat.cast_nonneg p)

/-- Sharp decaying-error Mertens lower bound for actual reservoir harmonic mass. -/
theorem harmonicSum_ge_mertensWindow (d : RouteEPrimeReservoirCofinalData) :
    Sieve.logLog d.U - Sieve.logLog d.W -
        ((2 * Sieve.mertensFirstConst + 1 / 2) / Real.log d.U +
          (2 * Sieve.mertensFirstConst + 1 / 2) / Real.log d.W) ≤
      d.harmonicSum := by
  have hUtwo : 2 ≤ d.U := d.W_ge_two.trans d.W_le_U
  have hU := Sieve.abs_mertensS_sub_logLog_sub_const_le hUtwo
  have hW := Sieve.abs_mertensS_sub_logLog_sub_const_le d.W_ge_two
  rw [harmonicSum, reservoir, Sieve.sum_inv_bigPrimeSet d.W d.U d.W_le_U]
  have hUl := (abs_le.mp hU).1
  have hWu := (abs_le.mp hW).2
  linarith

/-- PNT/Mertens first-moment upper bound with no asymptotic notation. -/
theorem harmonicLogMoment_le (d : RouteEPrimeReservoirCofinalData) :
    d.harmonicLogMoment ≤ Real.log d.U + Sieve.mertensFirstConst := by
  have hWtwo := d.W_ge_two
  have hWU := d.W_le_U
  have hUone : 1 ≤ d.U := by omega
  have hU := Sieve.abs_mertensA_sub_log_le hUone
  have hWnonneg : 0 ≤ Sieve.mertensA d.W := by
    unfold Sieve.mertensA
    apply Finset.sum_nonneg
    intro p hp
    have hprime := Nat.prime_of_mem_primesLE hp
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) (Nat.cast_nonneg p)
  rw [harmonicLogMoment, reservoir,
    Sieve.sum_logDiv_bigPrimeSet d.W d.U d.W_le_U]
  have hupper := (abs_le.mp hU).2
  linarith

/-- Collision mass of the prime window gains one full reciprocal lower-edge factor. -/
theorem harmonicSquareSum_le (d : RouteEPrimeReservoirCofinalData) :
    d.harmonicSquareSum ≤ (1 / (d.W : ℝ)) * d.harmonicSum := by
  unfold harmonicSquareSum harmonicSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hWpNat : d.W < p := Sieve.lt_of_mem_bigPrimeSet hp
  have hWp : (d.W : ℝ) ≤ (p : ℝ) := by exact_mod_cast hWpNat.le
  have hWpos : (0 : ℝ) < d.W := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) d.W_ge_two)
  have hinv : 1 / (p : ℝ) ≤ 1 / (d.W : ℝ) :=
    one_div_le_one_div_of_le hWpos hWp
  have hpnonneg : 0 ≤ 1 / (p : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_right hinv hpnonneg
  simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this

/-- Generic exact product-truncation theorem instantiated on the actual prime window. -/
theorem productTruncatedMass_lowerBound (d : RouteEPrimeReservoirCofinalData) :
    d.productTruncatedMass ≥
      (d.harmonicSum ^ d.b / (d.b.factorial : ℝ)) *
        (1 - ((d.b.choose 2 : ℕ) : ℝ) * d.harmonicSquareSum /
            d.harmonicSum ^ (2 : ℕ) -
          (d.b : ℝ) * d.harmonicLogMoment /
            (d.harmonicSum * Real.log d.T)) := by
  have hsum :
      (∑ p : ↥d.reservoir, 1 / (p.1 : ℝ)) = d.harmonicSum := by
    rw [harmonicSum, Finset.sum_subtype d.reservoir (fun _ => Iff.rfl)]
  have hsquare :
      (∑ p : ↥d.reservoir, (1 / (p.1 : ℝ)) ^ (2 : ℕ)) =
        d.harmonicSquareSum := by
    rw [harmonicSquareSum, Finset.sum_subtype d.reservoir (fun _ => Iff.rfl)]
  have hmoment :
      (∑ p : ↥d.reservoir, (1 / (p.1 : ℝ)) * Real.log p.1) =
        d.harmonicLogMoment := by
    rw [harmonicLogMoment, Finset.sum_subtype d.reservoir (fun _ => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hSsub : 0 < ∑ p : ↥d.reservoir, 1 / (p.1 : ℝ) := by
    rw [hsum]
    exact d.harmonicSum_pos
  have h := weightedProductTruncationLowerBound_normalized
      d.b d.b_pos ↥d.reservoir
      (fun p : ↥d.reservoir => 1 / (p.1 : ℝ))
      (fun p : ↥d.reservoir => Real.log p.1)
      (Real.log d.T) (Real.log_pos d.T_gt_one)
      (fun p => one_div_nonneg.mpr (Nat.cast_nonneg p.1))
      (fun p => Real.log_nonneg (by
        exact_mod_cast (Sieve.prime_of_mem_bigPrimeSet p.2).one_le))
      hSsub
  rw [hsum, hsquare, hmoment] at h
  exact h

/-- **Explicit cofinal prime-reservoir truncation law.**  Collision loss is controlled by
the lower prime edge `W`, while product-tail loss is controlled by Mertens' first theorem at
the upper edge `U`.  No asymptotic notation or unproved prime estimate remains. -/
theorem productTruncatedMass_ge_explicitMertens
    (d : RouteEPrimeReservoirCofinalData) :
    d.productTruncatedMass ≥
      (d.harmonicSum ^ d.b / (d.b.factorial : ℝ)) *
        (1 - ((d.b.choose 2 : ℕ) : ℝ) /
              ((d.W : ℝ) * d.harmonicSum) -
          (d.b : ℝ) * (Real.log d.U + Sieve.mertensFirstConst) /
            (d.harmonicSum * Real.log d.T)) := by
  have hS := d.harmonicSum_pos
  have hW : (0 : ℝ) < d.W := by exact_mod_cast
    (lt_of_lt_of_le (by norm_num : 0 < 2) d.W_ge_two)
  have hlogT := Real.log_pos d.T_gt_one
  have hchoose : (0 : ℝ) ≤ ((d.b.choose 2 : ℕ) : ℝ) := by positivity
  have hcollision :
      ((d.b.choose 2 : ℕ) : ℝ) * d.harmonicSquareSum /
          d.harmonicSum ^ (2 : ℕ) ≤
        ((d.b.choose 2 : ℕ) : ℝ) /
          ((d.W : ℝ) * d.harmonicSum) := by
    calc
      ((d.b.choose 2 : ℕ) : ℝ) * d.harmonicSquareSum /
          d.harmonicSum ^ (2 : ℕ) ≤
        ((d.b.choose 2 : ℕ) : ℝ) *
            ((1 / (d.W : ℝ)) * d.harmonicSum) /
              d.harmonicSum ^ (2 : ℕ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left d.harmonicSquareSum_le hchoose)
          (sq_nonneg d.harmonicSum)
      _ = ((d.b.choose 2 : ℕ) : ℝ) /
          ((d.W : ℝ) * d.harmonicSum) := by
        field_simp [hS.ne', hW.ne']
  have htail :
      (d.b : ℝ) * d.harmonicLogMoment /
          (d.harmonicSum * Real.log d.T) ≤
        (d.b : ℝ) * (Real.log d.U + Sieve.mertensFirstConst) /
          (d.harmonicSum * Real.log d.T) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left d.harmonicLogMoment_le (by positivity))
      (mul_nonneg hS.le hlogT.le)
  have hfactor :
      1 - ((d.b.choose 2 : ℕ) : ℝ) /
              ((d.W : ℝ) * d.harmonicSum) -
          (d.b : ℝ) * (Real.log d.U + Sieve.mertensFirstConst) /
            (d.harmonicSum * Real.log d.T) ≤
        1 - ((d.b.choose 2 : ℕ) : ℝ) * d.harmonicSquareSum /
              d.harmonicSum ^ (2 : ℕ) -
          (d.b : ℝ) * d.harmonicLogMoment /
            (d.harmonicSum * Real.log d.T) := by
    linarith
  have hbase :
      0 ≤ d.harmonicSum ^ d.b / (d.b.factorial : ℝ) :=
    div_nonneg (pow_nonneg hS.le d.b) (by positivity)
  exact (mul_le_mul_of_nonneg_left hfactor hbase).trans
    d.productTruncatedMass_lowerBound

/-- Exact `7/10` positive-proportion certificate used by the Route E cofinal schedule.  All
arithmetic dependence is exposed in one finite loss budget. -/
theorem sevenTenths_fullMass_le_productTruncatedMass
    (d : RouteEPrimeReservoirCofinalData)
    (hbudget :
      ((d.b.choose 2 : ℕ) : ℝ) /
            ((d.W : ℝ) * d.harmonicSum) +
          (d.b : ℝ) * (Real.log d.U + Sieve.mertensFirstConst) /
            (d.harmonicSum * Real.log d.T) ≤ 3 / 10) :
    (7 / 10 : ℝ) *
        (d.harmonicSum ^ d.b / (d.b.factorial : ℝ)) ≤
      d.productTruncatedMass := by
  have hbase :
      0 ≤ d.harmonicSum ^ d.b / (d.b.factorial : ℝ) :=
    div_nonneg (pow_nonneg d.harmonicSum_pos.le d.b) (by positivity)
  have hfactor :
      (7 / 10 : ℝ) ≤
        1 - ((d.b.choose 2 : ℕ) : ℝ) /
              ((d.W : ℝ) * d.harmonicSum) -
          (d.b : ℝ) * (Real.log d.U + Sieve.mertensFirstConst) /
            (d.harmonicSum * Real.log d.T) := by
    linarith
  calc
    (7 / 10 : ℝ) *
        (d.harmonicSum ^ d.b / (d.b.factorial : ℝ)) ≤
      (1 - ((d.b.choose 2 : ℕ) : ℝ) /
              ((d.W : ℝ) * d.harmonicSum) -
          (d.b : ℝ) * (Real.log d.U + Sieve.mertensFirstConst) /
            (d.harmonicSum * Real.log d.T)) *
        (d.harmonicSum ^ d.b / (d.b.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_right hfactor hbase
    _ = (d.harmonicSum ^ d.b / (d.b.factorial : ℝ)) *
        (1 - ((d.b.choose 2 : ℕ) : ℝ) /
              ((d.W : ℝ) * d.harmonicSum) -
          (d.b : ℝ) * (Real.log d.U + Sieve.mertensFirstConst) /
            (d.harmonicSum * Real.log d.T)) := by ring
    _ ≤ d.productTruncatedMass := by
      exact d.productTruncatedMass_ge_explicitMertens

end RouteEPrimeReservoirCofinalData

end

end RHTower
