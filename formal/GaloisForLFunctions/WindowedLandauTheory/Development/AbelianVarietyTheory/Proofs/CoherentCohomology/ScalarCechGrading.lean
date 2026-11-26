import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedHomology
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LinearCechComplex

/-! Alternating Čech cochains with varying coefficients form a finite graded
complex after removing the augmentation. -/

noncomputable section

open CategoryTheory GlobalTheory.CechDR

namespace HTGeometry.FinsetCechDatum

variable {K ι : Type} [Field K] [DecidableEq ι] [LinearOrder ι]
  (D : FinsetCechDatum.{0} ι) [coefficients : ∀ s, Module K (D.obj s)]

/-- The unaugmented cochains vanish on the empty index set. -/
def regular : Submodule K D.Cochain := LinearMap.ker (LinearMap.proj ∅)

private def dLinear
    (hres : ∀ {s t : Finset ι} (h : s ⊆ t) (r : K) (x : D.obj s),
      D.res h (r • x) = r • D.res h x) : D.Cochain →ₗ[K] D.Cochain where
  toFun := D.d
  map_add' := D.d_add
  map_smul' r x := funext fun s => by
    simp only [FinsetCechDatum.d, Pi.smul_apply, Finset.smul_sum, hres]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ r _

private def cardProj (n : ℕ) : D.Cochain →ₗ[K] D.Cochain :=
  LinearMap.pi fun s => if s.card = n then LinearMap.proj s else 0

omit [DecidableEq ι] [LinearOrder ι] in
private theorem cardProj_apply (n : ℕ) (x : D.Cochain) (s : Finset ι) :
    D.cardProj (K := K) n x s = if s.card = n then x s else 0 := by
  simp only [cardProj, LinearMap.pi_apply]
  split_ifs <;> rfl

private def cardSign : D.Cochain →ₗ[K] D.Cochain :=
  LinearMap.pi fun s => ((-1 : ℤ) ^ s.card) • LinearMap.proj s

omit [DecidableEq ι] [LinearOrder ι] in
private theorem cardSign_apply (x : D.Cochain) (s : Finset ι) :
    D.cardSign (K := K) x s = (-1 : ℤ) ^ s.card • x s := by
  simp only [cardSign, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply]

private theorem d_cardProj (n : ℕ) (x : D.Cochain) :
    D.d (D.cardProj (K := K) n x) = D.cardProj (K := K) (n + 1) (D.d x) := by
  funext s
  simp only [cardProj_apply, FinsetCechDatum.d]
  split_ifs with hs
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_pos (show (s.erase i).card = n by rw [Finset.card_erase_of_mem hi, hs]; omega)]
  · refine Finset.sum_eq_zero fun i hi => ?_
    rw [if_neg (show (s.erase i).card ≠ n by
      rw [Finset.card_erase_of_mem hi]
      have hpos := Finset.card_pos.2 ⟨i, hi⟩
      omega), map_zero, smul_zero]

variable [Fintype ι]
  (hres : ∀ {s t : Finset ι} (h : s ⊆ t) (r : K) (x : D.obj s),
    D.res h (r • x) = r • D.res h x)

/-- The projection to subsets of size `n + 1` selects the Čech cochains in degree `n`. -/
def graded : FiniteGradedComplex K (D.regular (K := K)) where
  d := (D.dLinear hres).restrict fun x _ => by
    change D.d x ∅ = 0
    simp only [FinsetCechDatum.d, Finset.sum_empty]
  π n := (D.cardProj n).restrict fun x hx => by
    change D.cardProj (K := K) n x ∅ = 0
    simp only [D.cardProj_apply (K := K), show x ∅ = 0 from hx, ite_self]
  σ := D.cardSign.restrict fun x hx => by
    change D.cardSign (K := K) x ∅ = 0
    rw [D.cardSign_apply (K := K), show x ∅ = 0 from hx, smul_zero]
  N := Fintype.card ι + 1
  dd x := Subtype.ext (D.d_d x.1)
  idem n x := by
    refine Subtype.ext (funext fun s => ?_)
    simp only [LinearMap.coe_restrict_apply, cardProj_apply]
    split_ifs <;> rfl
  orth n m x h := by
    refine Subtype.ext (funext fun s => ?_)
    simp only [LinearMap.coe_restrict_apply, cardProj_apply, ZeroMemClass.coe_zero, Pi.zero_apply]
    split_ifs with h₁ h₂
    · exact False.elim (h (h₁.symm.trans h₂))
    · rfl
    · rfl
  sum x := by
    refine Subtype.ext (funext fun s => ?_)
    have hs : s.card < Fintype.card ι + 1 := Nat.lt_succ_of_le (Finset.card_le_univ s)
    simp [cardProj_apply, Finset.sum_apply, hs]
  zero x := by
    refine Subtype.ext (funext fun s => ?_)
    simp only [LinearMap.coe_restrict_apply, cardProj_apply, ZeroMemClass.coe_zero, Pi.zero_apply]
    split_ifs with h
    · rw [Finset.card_eq_zero.1 h]
      exact x.2
    · rfl
  dπ n x := Subtype.ext (D.d_cardProj (K := K) n x.1)
  σπ n x := by
    refine Subtype.ext (funext fun s => ?_)
    simp only [LinearMap.coe_restrict_apply, cardProj_apply, cardSign_apply,
      Submodule.coe_smul_of_tower, Pi.smul_apply]
    split_ifs with hs
    · rw [hs]
    · rw [smul_zero, smul_zero]

theorem graded_d_apply (x : D.regular (K := K)) (s : Finset ι) :
    ((D.graded hres).d x).1 s = D.d x.1 s := rfl

theorem graded_π_apply (n : ℕ) (x : D.regular (K := K)) (s : Finset ι) :
    ((D.graded hres).π n x).1 s = if s.card = n then x.1 s else 0 :=
  D.cardProj_apply (K := K) n x.1 s

include coefficients in
/-- Exactness in each augmented degree gives a primitive for every cocycle
in the direct sum of the degrees. -/
theorem exists_primitive_of_augmented_exact (h₀ : D.ExactBot) (h : ∀ n, D.ExactAt n)
    (x : D.Cochain) (hx : D.d x = 0) : ∃ y : D.Cochain, D.d y = x := by
  have hclosed (n : ℕ) : D.d (D.cardProj (K := K) n x) = 0 := by
    rw [D.d_cardProj (K := K), hx, map_zero]
  have hlift (n : ℕ) : ∃ y : D.Cochain, D.d y = D.cardProj (K := K) n x := by
    cases n with
    | zero =>
      have hs : D.IsBot (D.cardProj (K := K) 0 x) := fun s hs =>
        (D.cardProj_apply (K := K) 0 x s).trans (if_neg (Nat.ne_of_gt (Finset.card_pos.2 hs)))
      exact ⟨0, D.d_zero.trans (h₀ _ hs (hclosed 0)).symm⟩
    | succ n =>
      have hs : D.IsDeg (D.cardProj (K := K) (n + 1) x) n := fun s hs =>
        (D.cardProj_apply (K := K) (n + 1) x s).trans (if_neg hs)
      obtain ⟨y, -, hy⟩ := h n _ hs (hclosed (n + 1))
      exact ⟨y, hy⟩
  choose y hy using hlift
  refine ⟨∑ n ∈ Finset.range (Fintype.card ι + 1), y n, ?_⟩
  change D.dHom _ = x
  rw [map_sum]
  funext s
  have hs : s.card < Fintype.card ι + 1 := Nat.lt_succ_of_le (Finset.card_le_univ s)
  rw [Finset.sum_apply]
  change (∑ n ∈ Finset.range (Fintype.card ι + 1), D.d (y n) s) = x s
  simp only [hy, cardProj_apply]
  simp [hs]

/-- Homogeneous representatives are exactly the cochains on intersections of
the required cardinality. -/
def gradedTermEquiv (n : ℕ) : (D.graded hres).term (n + 1) ≃ₗ[K] D.degreeSubmodule (R := K) n where
  toFun x := ⟨x.1.1, fun s hs => by
    have e := congrArg (fun a : D.regular (K := K) => a.1 s)
      ((D.graded hres).π_apply_term (n + 1) x)
    exact e.symm.trans ((D.graded_π_apply hres (n + 1) x.1 s).trans (if_neg hs))⟩
  invFun x := by
    let y : D.regular (K := K) := ⟨x.1, x.2 ∅ (by simp)⟩
    refine ⟨y, ⟨y, Subtype.ext (funext fun s => ?_)⟩⟩
    rw [D.graded_π_apply hres]
    by_cases hs : s.card = n + 1
    · exact if_pos hs
    · exact (if_neg hs).trans (x.2 s hs).symm
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

omit [Fintype ι] in
/-- With zero coefficient at the empty index, primitives for total cocycles
give exactness of the ordinary Čech complex in every degree. -/
theorem acyclic_linearComplex_of_total_exact (h₀ : Subsingleton (D.obj ∅))
    (hex : ∀ x : D.Cochain, D.d x = 0 → ∃ y, D.d y = x) :
    (D.linearComplex hres).Acyclic := by
  let C := D.linearComplex hres
  have hd (n : ℕ) (x : D.degreeSubmodule (R := K) n) :
      ((C.d n (n + 1)) x).1 = D.d x.1 := by
    change (CochainComplex.of.d (fun j : ℕ => ModuleCat.of K (D.degreeSubmodule (R := K) j))
      _ n (n + 1) x).1 = _
    rw [CochainComplex.of_d]
    rfl
  have project (n : ℕ) (x : D.degreeSubmodule (R := K) n) :
      D.cardProj (K := K) (n + 1) x.1 = x.1 := by
    funext s
    rw [D.cardProj_apply (K := K)]
    by_cases hs : s.card = n + 1
    · exact if_pos hs
    · exact (if_neg hs).trans (x.2 s hs).symm
  intro n
  cases n with
  | zero =>
    let S := C.sc' 0 0 1
    apply (C.exactAt_iff' 0 0 1 (by simp) (by simp)).2
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2
    intro x
    constructor
    · intro hx
      have hx' : D.d x.1 = 0 := (hd 0 x).symm.trans (congrArg Subtype.val hx)
      obtain ⟨y, hy⟩ := hex x.1 hx'
      have hBot : D.cardProj (K := K) 0 y = 0 := by
        funext s
        rw [D.cardProj_apply (K := K)]
        split_ifs with hs
        · obtain rfl := Finset.card_eq_zero.1 hs
          exact h₀.elim _ _
        · rfl
      have hzero := D.d_cardProj (K := K) 0 y
      rw [hBot, D.d_zero, hy, project 0 x] at hzero
      exact ⟨0, (map_zero S.f.hom).trans (Subtype.ext hzero)⟩
    · rintro ⟨y, rfl⟩
      exact congr($(S.zero).hom y)
  | succ n =>
    let S := C.sc' n (n + 1) (n + 2)
    apply (C.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).2
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2
    intro x
    constructor
    · intro hx
      have hx' : D.d x.1 = 0 := (hd (n + 1) x).symm.trans (congrArg Subtype.val hx)
      obtain ⟨y, hy⟩ := hex x.1 hx'
      have hyDeg : D.IsDeg (D.cardProj (K := K) (n + 1) y) n := fun s hs =>
        (D.cardProj_apply (K := K) (n + 1) y s).trans (if_neg hs)
      let z : D.degreeSubmodule (R := K) n := ⟨_, hyDeg⟩
      refine ⟨z, Subtype.ext ((hd n z).trans ?_)⟩
      change D.d (D.cardProj (K := K) (n + 1) y) = x.1
      rw [D.d_cardProj (K := K), hy, project (n + 1) x]
    · rintro ⟨y, rfl⟩
      exact congr($(S.zero).hom y)

end HTGeometry.FinsetCechDatum
