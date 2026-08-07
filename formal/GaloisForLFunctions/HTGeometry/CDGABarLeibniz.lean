import GaloisForLFunctions.HTGeometry.CDGABarComm

/-!
# The bar differential against the internal differential

The bar differential multiplies two adjacent shifted factors and the internal differential
differentiates each of them.  On the merged slot they are related by the Leibniz rule of the
shifted product, so the three ways of performing both operations — differentiate the product,
differentiate the first factor and then multiply, differentiate the second factor and then
multiply — cancel.

The three sums this produces are indexed differently: the one that differentiates the merged slot
by the splits of the predecessor of the target degree, the other two by the splits of the target
degree itself.  The two reindexings that compare them raise one part of a split by one, so each
misses exactly the splits whose corresponding part vanishes, and those terms are zero because a
degree-one map has no component in degree zero.

* `HTGeometry.barSplitLeft`, `HTGeometry.barSplitRight` : the two reindexings.
* `HTGeometry.barStageDL` : the internal differential on the outer shifted factor of a stage.
* `HTGeometry.barHead_leibniz_apply` : the Leibniz cancellation, componentwise.
-/

universe u

namespace GaloisForLFunctions.HTGeometry

open TensorProduct

variable {R : Type u} [CommRing R] {X : ℕ → Type u} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} (ε : CDGAHom A (groundCDGA R))
  (Z : ℕ → Type u) [∀ n, AddCommGroup (Z n)] [∀ n, Module R (Z n)]

section Reindex

/-- Degree zero has no splits. -/
theorem barSplit_zero_empty : (Finset.univ : Finset (BarSplit 0)) = ∅ := by
  refine Finset.eq_empty_of_forall_notMem ?_
  rintro ⟨⟨v, v'⟩, hv⟩ -
  exact absurd (hv : v + v' + 1 = 0) (Nat.succ_ne_zero _)

/-- A split with its first part raised by one. -/
def barSplitLeft {m : ℕ} (t : BarSplit m) : BarSplit (m + 1) :=
  ⟨(t.1.1 + 1, t.1.2), by have h := t.2; omega⟩

/-- A split with its second part raised by one. -/
def barSplitRight {m : ℕ} (t : BarSplit m) : BarSplit (m + 1) :=
  ⟨(t.1.1, t.1.2 + 1), by have h := t.2; omega⟩

theorem barSplitLeft_injective {m : ℕ} : Function.Injective (barSplitLeft (m := m)) := by
  rintro ⟨⟨a, a'⟩, h⟩ ⟨⟨b, b'⟩, h'⟩ hEq
  have h1 : ((a + 1, a') : ℕ × ℕ) = (b + 1, b') := congrArg Subtype.val hEq
  have ha : a + 1 = b + 1 := congrArg Prod.fst h1
  have ha' : a' = b' := congrArg Prod.snd h1
  refine Subtype.ext (Prod.ext ?_ ha')
  show a = b
  omega

theorem barSplitRight_injective {m : ℕ} : Function.Injective (barSplitRight (m := m)) := by
  rintro ⟨⟨a, a'⟩, h⟩ ⟨⟨b, b'⟩, h'⟩ hEq
  have h1 : ((a, a' + 1) : ℕ × ℕ) = (b, b' + 1) := congrArg Subtype.val hEq
  have ha : a = b := congrArg Prod.fst h1
  have ha' : a' + 1 = b' + 1 := congrArg Prod.snd h1
  refine Subtype.ext (Prod.ext ha ?_)
  show a' = b'
  omega

/-- **Summing over the splits of a successor when the terms with a vanishing first part vanish**:
the remaining splits are exactly the ones whose first part is raised by one. -/
theorem sum_barSplitLeft {β : Type*} [AddCommMonoid β] {m : ℕ} (f : BarSplit (m + 1) → β)
    (h0 : ∀ s : BarSplit (m + 1), s.1.1 = 0 → f s = 0) :
    ∑ s : BarSplit (m + 1), f s = ∑ t : BarSplit m, f (barSplitLeft t) := by
  classical
  rw [← Finset.sum_image (s := (Finset.univ : Finset (BarSplit m))) (f := f)
    (g := barSplitLeft) fun x _ y _ hxy => barSplitLeft_injective hxy]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  rintro ⟨⟨a, a'⟩, hsa⟩ - hs
  cases a with
  | zero => exact h0 _ rfl
  | succ p =>
      refine absurd ?_ hs
      exact Finset.mem_image.2 ⟨⟨(p, a'), by omega⟩, Finset.mem_univ _, rfl⟩

/-- The same for the second part of a split. -/
theorem sum_barSplitRight {β : Type*} [AddCommMonoid β] {m : ℕ} (f : BarSplit (m + 1) → β)
    (h0 : ∀ s : BarSplit (m + 1), s.1.2 = 0 → f s = 0) :
    ∑ s : BarSplit (m + 1), f s = ∑ t : BarSplit m, f (barSplitRight t) := by
  classical
  rw [← Finset.sum_image (s := (Finset.univ : Finset (BarSplit m))) (f := f)
    (g := barSplitRight) fun x _ y _ hxy => barSplitRight_injective hxy]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  rintro ⟨⟨a, a'⟩, hsa⟩ - hs
  cases a' with
  | zero => exact h0 _ rfl
  | succ q =>
      refine absurd ?_ hs
      exact Finset.mem_image.2 ⟨⟨(a, q), by omega⟩, Finset.mem_univ _, rfl⟩

end Reindex

section StageDifferential

variable (N : ℕ → Type u) [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]

/-- **The internal differential of a bar stage on its outer shifted factor.** -/
noncomputable def barStageDL (n : ℕ) :
    TensorCarrier (R := R) (barShiftFamily ε) N n →ₗ[R]
      TensorCarrier (R := R) (barShiftFamily ε) N (n + 1) :=
  tensorLeftDegOneₗ (M := barShiftFamily ε) (M' := barShiftFamily ε) (N := N)
    (augIdealShiftD ε) n

@[simp] theorem barStageDL_zero (n b : ℕ) (F : TensorCarrier (R := R) (barShiftFamily ε) N n)
    (h : (0, b).1 + (0, b).2 = n + 1) : barStageDL ε N n F ⟨(0, b), h⟩ = 0 := rfl

@[simp] theorem barStageDL_succ (n a b : ℕ) (F : TensorCarrier (R := R) (barShiftFamily ε) N n)
    (h : (a + 1, b).1 + (a + 1, b).2 = n + 1) :
    barStageDL ε N n F ⟨(a + 1, b), h⟩
      = TensorProduct.map (augIdealShiftD ε a) (LinearMap.id (R := R) (M := N b))
        (F ⟨(a, b), by omega⟩) := rfl

end StageDifferential

section Terms

/-- The component of the argument that all three terms of the Leibniz cancellation read, with its
two shifted factors separated. -/
noncomputable def barLeibnizArg (n p q e : ℕ) (hix : p + (q + e) = n)
    (F : TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε) Z) n) :
    TensorProduct R (barShiftFamily ε p) (TensorProduct R (barShiftFamily ε q) (Z e)) :=
  TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε p))
    (barProj (M := barShiftFamily ε) (N := Z) ⟨(q, e), rfl⟩) (F ⟨(p, q + e), hix⟩)

theorem barLeibnizArg_eq (n p q e : ℕ) (hix : p + (q + e) = n)
    (F : TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε) Z) n) :
    barLeibnizArg ε Z n p q e hix F
      = TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε p))
        (barProj (M := barShiftFamily ε) (N := Z) ⟨(q, e), rfl⟩) (F ⟨(p, q + e), hix⟩) := rfl

/-- The component of the argument a split of the predecessor of the target degree reads. -/
theorem barLeibniz_deg {m n e : ℕ} (hq : m + e = n + 1) (t : BarSplit m) :
    t.1.1 + (t.1.2 + e) = n := by
  obtain ⟨⟨p, q⟩, ht⟩ := t
  have h : p + q + 1 = m := ht
  show p + (q + e) = n
  omega

/-- One term of the head, as the multiplication of the first two of three separated factors. -/
theorem barHeadTermₗ_eq_mulTail (n c e : ℕ) (hq : c + e = n + 1) (a a' : ℕ) (hs : a + a' + 1 = c)
    (hix : a + (a' + e) = n)
    (V : TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε) Z) n) :
    barHeadTermₗ ε Z n c e hq a a' hs V
      = barMulTail ε hs (LinearMap.id (R := R) (M := Z e))
        (barLeibnizArg ε Z n a a' e hix V) := rfl

/-- **Differentiating the outer factor and then multiplying**, at one split of the target degree
whose first part is a successor. -/
theorem barHead_leibniz_left_term (n m e p q : ℕ) (hp : m + 1 + e = n + 1 + 1)
    (hs : p + 1 + q + 1 = m + 1) (hix : p + (q + e) = n)
    (F : TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε) Z) n) :
    barHeadTermₗ ε Z (n + 1) (m + 1) e hp (p + 1) q hs
        (barStageDL ε (fun b => TensorCarrier (R := R) (barShiftFamily ε) Z b) n F)
      = barMulTail ε hs (LinearMap.id (R := R) (M := Z e))
        (TensorProduct.map (augIdealShiftD ε p)
          (LinearMap.id (R := R) (M := TensorProduct R (barShiftFamily ε q) (Z e)))
          (barLeibnizArg ε Z n p q e hix F)) := by
  rw [barHeadTermₗ_eq_mulTail ε Z (n + 1) (m + 1) e hp (p + 1) q hs (by omega)]
  refine congrArg (barMulTail ε hs (LinearMap.id (R := R) (M := Z e))) ?_
  rw [barLeibnizArg_eq, barLeibnizArg_eq, barStageDL_succ, ← LinearMap.comp_apply,
    ← LinearMap.comp_apply, ← TensorProduct.map_comp, ← TensorProduct.map_comp]
  simp only [LinearMap.id_comp, LinearMap.comp_id]

/-- **A differentiated inner factor has nothing in the zeroth shifted degree**, so the head's term
at a split whose second part vanishes is zero. -/
theorem barHead_leibniz_right_vanish (n e a : ℕ) (h : a + (0 + e) = n + 1)
    (F : TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε) Z) n) :
    TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε a))
        (barProj (M := barShiftFamily ε) (N := Z) (n := 0 + e) ⟨(0, e), rfl⟩)
        (tensorRightDegOne (M := barShiftFamily ε) (fun b => barStageDL ε Z b) n F
          ⟨(a, 0 + e), h⟩) = 0 := by
  cases e with
  | zero =>
      rw [show tensorRightDegOne (M := barShiftFamily ε) (fun b => barStageDL ε Z b) n F
            ⟨(a, 0 + 0), h⟩ = 0 from
          tensorRightDegOne_zero (M := barShiftFamily ε) _ n a F _, map_zero]
  | succ e' =>
      rw [show tensorRightDegOne (M := barShiftFamily ε) (fun b => barStageDL ε Z b) n F
            ⟨(a, 0 + (e' + 1)), h⟩
            = ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (barStageDL ε Z (0 + e'))
              (F ⟨(a, 0 + e'), by omega⟩) from
          tensorRightDegOne_succ (M := barShiftFamily ε) _ n a (0 + e') F _,
        map_smul, ← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.comp_id,
        show (barProj (M := barShiftFamily ε) (N := Z) (n := 0 + (e' + 1))
              ⟨(0, e' + 1), rfl⟩).comp (barStageDL ε Z (0 + e')) = 0 from
          LinearMap.ext fun _ => rfl,
        TensorProduct.map_zero_right, LinearMap.zero_apply, smul_zero]

/-- **Differentiating the inner factor and then multiplying**, at one split of the target degree
whose second part is a successor.  The degree the argument is read at is a parameter with an
equation, so that the right-factor construction's defining equation applies without moving
anything. -/
theorem barHead_leibniz_right_term (n m e p q b : ℕ) (hp : m + 1 + e = n + 1 + 1)
    (hs : p + (q + 1) + 1 = m + 1) (hix : p + (q + e) = n) (hb : q + 1 + e = b + 1)
    (hix' : p + (b + 1) = n + 1)
    (F : TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε) Z) n) :
    TensorProduct.map (augIdealShiftMulOfTensor ε hs) (LinearMap.id (R := R) (M := Z e))
        ((TensorProduct.assoc R (barShiftFamily ε p) (barShiftFamily ε (q + 1)) (Z e)).symm
          (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε p))
            (barProj (M := barShiftFamily ε) (N := Z) (n := b + 1) ⟨(q + 1, e), hb⟩)
            (tensorRightDegOne (M := barShiftFamily ε) (fun c => barStageDL ε Z c) n F
              ⟨(p, b + 1), hix'⟩)))
      = ((-1 : R)) ^ p • barMulTail ε hs (LinearMap.id (R := R) (M := Z e))
        (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε p))
          (TensorProduct.map (augIdealShiftD ε q) (LinearMap.id (R := R) (M := Z e)))
          (barLeibnizArg ε Z n p q e hix F)) := by
  have hbq : b = q + e := by omega
  subst hbq
  have hinner : (barProj (M := barShiftFamily ε) (N := Z) (n := q + e + 1)
        ⟨(q + 1, e), hb⟩).comp (barStageDL ε Z (q + e))
      = (TensorProduct.map (augIdealShiftD ε q) (LinearMap.id (R := R) (M := Z e))).comp
        (barProj (M := barShiftFamily ε) (N := Z) (n := q + e) ⟨(q, e), rfl⟩) :=
    LinearMap.ext fun _ => rfl
  have hargs : (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε p))
        (barProj (M := barShiftFamily ε) (N := Z) (n := q + e + 1) ⟨(q + 1, e), hb⟩)).comp
      (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε p))
        (barStageDL ε Z (q + e)))
    = (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε p))
        (TensorProduct.map (augIdealShiftD ε q) (LinearMap.id (R := R) (M := Z e)))).comp
      (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε p))
        (barProj (M := barShiftFamily ε) (N := Z) (n := q + e) ⟨(q, e), rfl⟩)) := by
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, hinner]
  rw [tensorRightDegOne_succ, map_smul, map_smul, map_smul]
  refine congrArg (fun z => ((-1 : R)) ^ p • z) ?_
  rw [barLeibnizArg_eq, ← LinearMap.comp_apply, hargs, LinearMap.comp_apply]
  rfl

end Terms

set_option maxHeartbeats 1000000 in
/-- **The head of the bar differential and the internal differential satisfy the Leibniz rule**,
componentwise: differentiating the merged slot, differentiating the outer factor before
multiplying, and differentiating the inner factor before multiplying sum to zero. -/
theorem barHead_leibniz_apply (n c e : ℕ) (hp : c + e = n + 1 + 1)
    (F : TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε) Z) n) :
    barStageDL ε Z (n + 1) (barHeadₗ ε Z n F) ⟨(c, e), hp⟩
      + barHeadₗ ε Z (n + 1)
        (barStageDL ε (fun b => TensorCarrier (R := R) (barShiftFamily ε) Z b) n F) ⟨(c, e), hp⟩
      + barHeadₗ ε Z (n + 1)
        (tensorRightDegOne (M := barShiftFamily ε) (fun b => barStageDL ε Z b) n F)
        ⟨(c, e), hp⟩ = 0 := by
  cases c with
  | zero =>
      have hzero : ∀ V : TensorCarrier (R := R) (barShiftFamily ε)
            (TensorCarrier (R := R) (barShiftFamily ε) Z) (n + 1),
          barHeadₗ ε Z (n + 1) V ⟨(0, e), hp⟩ = 0 := by
        intro V
        rw [barHead_apply]
        refine Finset.sum_eq_zero fun s _ => ?_
        obtain ⟨⟨v, v'⟩, hv⟩ := s
        have hv0 : v + v' + 1 = 0 := hv
        exact absurd hv0 (Nat.succ_ne_zero _)
      rw [barStageDL_zero, hzero, hzero, add_zero, add_zero]
  | succ m =>
      have hq : m + e = n + 1 := by omega
      have hE : barStageDL ε Z (n + 1) (barHeadₗ ε Z n F) ⟨(m + 1, e), hp⟩
          = ∑ t : BarSplit m, TensorProduct.map (augIdealShiftD ε m)
              (LinearMap.id (R := R) (M := Z e))
              (barMulTail ε t.2 (LinearMap.id (R := R) (M := Z e))
                (barLeibnizArg ε Z n t.1.1 t.1.2 e (barLeibniz_deg hq t) F)) := by
        rw [barStageDL_succ, barHead_apply, map_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        exact congrArg (TensorProduct.map (augIdealShiftD ε m) (LinearMap.id (R := R) (M := Z e)))
          (barHeadTermₗ_eq_mulTail ε Z n m e hq t.1.1 t.1.2 t.2 (barLeibniz_deg hq t) F)
      have hA : barHeadₗ ε Z (n + 1)
            (barStageDL ε (fun b => TensorCarrier (R := R) (barShiftFamily ε) Z b) n F)
            ⟨(m + 1, e), hp⟩
          = ∑ t : BarSplit m, barMulTail ε (barSplitLeft t).2
              (LinearMap.id (R := R) (M := Z e))
              (TensorProduct.map (augIdealShiftD ε t.1.1)
                (LinearMap.id (R := R)
                  (M := TensorProduct R (barShiftFamily ε t.1.2) (Z e)))
                (barLeibnizArg ε Z n t.1.1 t.1.2 e (barLeibniz_deg hq t) F)) := by
        rw [barHead_apply]
        refine (sum_barSplitLeft _ ?_).trans (Finset.sum_congr rfl fun t _ => ?_)
        · rintro ⟨⟨a, a'⟩, hsa⟩ hs0
          cases a with
          | succ p => exact absurd (hs0 : p + 1 = 0) (Nat.succ_ne_zero p)
          | zero =>
              have hsa' : 0 + a' + 1 = m + 1 := hsa
              rw [barHeadTermₗ_eq_mulTail ε Z (n + 1) (m + 1) e hp 0 a' hsa (by omega),
                barLeibnizArg_eq, barStageDL_zero, map_zero, map_zero]
        · obtain ⟨⟨p, q⟩, ht⟩ := t
          exact barHead_leibniz_left_term ε Z n m e p q hp _ (barLeibniz_deg hq ⟨(p, q), ht⟩) F
      have hC : barHeadₗ ε Z (n + 1)
            (tensorRightDegOne (M := barShiftFamily ε) (fun b => barStageDL ε Z b) n F)
            ⟨(m + 1, e), hp⟩
          = ∑ t : BarSplit m, ((-1 : R)) ^ t.1.1 • barMulTail ε (barSplitRight t).2
              (LinearMap.id (R := R) (M := Z e))
              (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε t.1.1))
                (TensorProduct.map (augIdealShiftD ε t.1.2)
                  (LinearMap.id (R := R) (M := Z e)))
                (barLeibnizArg ε Z n t.1.1 t.1.2 e (barLeibniz_deg hq t) F)) := by
        rw [barHead_apply]
        refine (sum_barSplitRight _ ?_).trans (Finset.sum_congr rfl fun t _ => ?_)
        · rintro ⟨⟨a, a'⟩, hsa⟩ hs0
          cases a' with
          | succ q => exact absurd (hs0 : q + 1 = 0) (Nat.succ_ne_zero q)
          | zero =>
              have hsa' : a + 0 + 1 = m + 1 := hsa
              rw [barHeadTermₗ_eq_comp,
                barHead_leibniz_right_vanish ε Z n e a (by omega) F, map_zero, map_zero]
        · obtain ⟨⟨p, q⟩, ht⟩ := t
          rw [barHeadTermₗ_eq_comp]
          cases e with
          | zero =>
              exact barHead_leibniz_right_term ε Z n m 0 p q q hp _
                (barLeibniz_deg hq ⟨(p, q), ht⟩) (by omega) (by omega) F
          | succ e' =>
              exact barHead_leibniz_right_term ε Z n m (e' + 1) p q (q + 1 + e') hp _
                (barLeibniz_deg hq ⟨(p, q), ht⟩) (by omega) (by omega) F
      rw [hE, hA, hC, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun t _ => ?_
      exact barMulD_cancel ε t.2 (barLeibnizArg ε Z n t.1.1 t.1.2 e (barLeibniz_deg hq t) F)

end GaloisForLFunctions.HTGeometry
