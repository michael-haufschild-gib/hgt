import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.CriticalSplineSlots

/-!
# Completing a sparse divisor with critical-line slots

Each unit block contains the two positive-height reflections of its sparse
core and enough rational critical points to reach the prescribed RVM count.
-/

set_option autoImplicit false
noncomputable section
open Finset Complex
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

def splineCoreBlockLabel {ι : Type*} (z : ι → ℂ) (i : ι) : ℕ :=
  ⌊(z i).im⌋₊-1

abbrev SplineCoreBlock {ι : Type*} (z : ι → ℂ) (j : ℕ) :=
  {i : ι // splineCoreBlockLabel z i=j}

lemma splineCoreBlock_im_bounds {ι : Type*} (z : ι → ℂ)
    (him : ∀ i,1≤(z i).im) (j : ℕ) (i : SplineCoreBlock z j) :
    (j:ℝ)+1≤(z i.val).im ∧ (z i.val).im<(j:ℝ)+2 := by
  have hf : 1≤⌊(z i.val).im⌋₊ := Nat.le_floor (by simpa using him i.val)
  have he : ⌊(z i.val).im⌋₊=j+1 := by
    have hh := i.property
    change ⌊(z i.val).im⌋₊-1=j at hh
    omega
  have hlo := Nat.floor_le (zero_le_one.trans (him i.val))
  have hhi := Nat.lt_floor_add_one (z i.val).im
  rw [he] at hlo hhi
  push_cast at hlo hhi
  constructor
  · exact hlo
  · linarith only [hhi]

def splineCoreBlockEmbedding {ι : Type*} (z : ι → ℂ)
    (him : ∀ i,1≤(z i).im)
    (hlocal : ∀ T : ℝ, Nonempty ({i : ι // (z i).im ∈ Set.Icc T (T+1)} ↪ Fin 3))
    (j : ℕ) : SplineCoreBlock z j ↪ Fin 3 := by
  let e := Classical.choice (hlocal ((j:ℝ)+1))
  refine ⟨fun i => e ⟨i.val,(splineCoreBlock_im_bounds z him j i).1,by
      have h := (splineCoreBlock_im_bounds z him j i).2
      linarith only [h]⟩,?_⟩
  intro i k he
  have hval := congrArg
    (fun v : {i : ι // (z i).im ∈ Set.Icc ((j:ℝ)+1) ((j:ℝ)+1+1)} => v.val)
    (e.injective he)
  exact Subtype.ext hval

abbrev splineCoreBlockFintype {ι : Type*} (z : ι → ℂ)
    (him : ∀ i,1≤(z i).im)
    (hlocal : ∀ T : ℝ, Nonempty ({i : ι // (z i).im ∈ Set.Icc T (T+1)} ↪ Fin 3))
    (j : ℕ) : Fintype (SplineCoreBlock z j) :=
  Fintype.ofInjective (splineCoreBlockEmbedding z him hlocal j)
    (splineCoreBlockEmbedding z him hlocal j).injective

lemma card_splineCoreBlock_le_three {ι : Type*} (z : ι → ℂ)
    (him : ∀ i,1≤(z i).im)
    (hlocal : ∀ T : ℝ, Nonempty ({i : ι // (z i).im ∈ Set.Icc T (T+1)} ↪ Fin 3))
    (j : ℕ) : Nat.card (SplineCoreBlock z j)≤3 := by
  letI := splineCoreBlockFintype z him hlocal j
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_le_of_injective _ (splineCoreBlockEmbedding z him hlocal j).injective).trans_eq
    (Fintype.card_fin 3)

def rvmCompletionCriticalCount {ι : Type*} (z : ι → ℂ) (j : ℕ) : ℕ :=
  rvmCompletionBlockSize (j+1)-2*Nat.card (SplineCoreBlock z j)

lemma rvmCompletionCriticalCount_le {ι : Type*} (z : ι → ℂ) (j : ℕ) :
    rvmCompletionCriticalCount z j≤rvmCompletionBlockSize (j+1) := Nat.sub_le _ _

abbrev RVMCompletionBlock {ι : Type*} (z : ι → ℂ) (j : ℕ) :=
  (SplineCoreBlock z j × Bool) ⊕ Fin (rvmCompletionCriticalCount z j)

def rvmPositiveCoreAtom {ι : Type*} (z : ι → ℂ) (i : ι × Bool) : ℂ :=
  prescribedSplineQuartetAtom z (i.1,i.2,i.2)

lemma rvmPositiveCoreAtom_im {ι : Type*} (z : ι → ℂ) (i : ι × Bool) :
    (rvmPositiveCoreAtom z i).im=(z i.1).im := by
  rcases i with ⟨i,b⟩
  cases b <;> simp [rvmPositiveCoreAtom,prescribedSplineQuartetAtom]

lemma rvmPositiveCoreAtom_abs_re {ι : Type*} (z : ι → ℂ) (i : ι × Bool) :
    |(rvmPositiveCoreAtom z i).re|=|(z i.1).re| := by
  rcases i with ⟨i,b⟩
  cases b <;> simp [rvmPositiveCoreAtom,prescribedSplineQuartetAtom]

lemma rvmPositiveCoreAtom_injective {ι : Type*} (z : ι → ℂ)
    (hinj : Function.Injective (prescribedSplineQuartetAtom z)) :
    Function.Injective (rvmPositiveCoreAtom z) := by
  intro i j he
  have hh := hinj he
  apply Prod.ext
  · exact congrArg (fun v : ι × Bool × Bool => v.1) hh
  · exact congrArg (fun v : ι × Bool × Bool => v.2.1) hh

def rvmCompletionPositiveAtom {ι : Type*} (z : ι → ℂ)
    (a : (j : ℕ) × RVMCompletionBlock z j) : ℂ :=
  match a.2 with
  | Sum.inl i => rvmPositiveCoreAtom z (i.1.val,i.2)
  | Sum.inr k => rvmCriticalSlotAtom (rvmCompletionCriticalCount z)
      (rvmCompletionCriticalCount_le z) ⟨a.1,k⟩

/-- Forgetting the core block label is a bijection; its inverse restores the floor label. -/
def rvmCompletionPositiveEquiv {ι : Type*} (z : ι → ℂ) :
    ((j : ℕ) × RVMCompletionBlock z j) ≃
      ((ι × Bool) ⊕ ((j : ℕ) × Fin (rvmCompletionCriticalCount z j))) where
  toFun a := match a.2 with
    | Sum.inl i => Sum.inl (i.1.val,i.2)
    | Sum.inr k => Sum.inr ⟨a.1,k⟩
  invFun a := match a with
    | Sum.inl i => ⟨splineCoreBlockLabel z i.1,Sum.inl (⟨i.1,rfl⟩,i.2)⟩
    | Sum.inr i => ⟨i.1,Sum.inr i.2⟩
  left_inv := by
    rintro ⟨j,⟨⟨i,hi⟩,b⟩|k⟩
    · change splineCoreBlockLabel z i=j at hi
      subst j
      rfl
    · rfl
  right_inv := by
    rintro (⟨i,b⟩|⟨j,k⟩) <;> rfl

lemma rvmCompletionPositiveAtom_bounds {ι : Type*} (z : ι → ℂ)
    (him : ∀ i,1≤(z i).im) (j : ℕ) (a : RVMCompletionBlock z j) :
    (j:ℝ)+1≤(rvmCompletionPositiveAtom z ⟨j,a⟩).im ∧
      (rvmCompletionPositiveAtom z ⟨j,a⟩).im<(j:ℝ)+2 := by
  rcases a with ⟨i,b⟩|k
  · simpa only [rvmCompletionPositiveAtom,rvmPositiveCoreAtom_im] using
      splineCoreBlock_im_bounds z him j i
  · exact ⟨(rvmCriticalSlotAtom_im_bounds (rvmCompletionCriticalCount z) (rvmCompletionCriticalCount_le z) ⟨j,k⟩).1.le,
      (rvmCriticalSlotAtom_im_bounds (rvmCompletionCriticalCount z) (rvmCompletionCriticalCount_le z) ⟨j,k⟩).2⟩

lemma rvmCompletionBlock_card {ι : Type*} (z : ι → ℂ)
    (him : ∀ i,1≤(z i).im)
    (hlocal : ∀ T : ℝ, Nonempty ({i : ι // (z i).im ∈ Set.Icc T (T+1)} ↪ Fin 3))
    (j : ℕ) [Fintype (SplineCoreBlock z j)] :
    Fintype.card (RVMCompletionBlock z j)=rvmCompletionBlockSize (j+1) := by
  have hc := card_splineCoreBlock_le_three z him hlocal j
  have hn := six_le_rvmCompletionBlockSize (j+1)
  change Fintype.card ((SplineCoreBlock z j × Bool) ⊕ Fin (rvmCompletionCriticalCount z j))=_
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,
    rvmCompletionCriticalCount,Nat.card_eq_fintype_card] at *
  omega

lemma rvmCriticalSlotAtom_injective (K : ℕ → ℕ)
    (hK : ∀ j,K j≤rvmCompletionBlockSize (j+1)) :
    Function.Injective (rvmCriticalSlotAtom K hK) := by
  rintro ⟨j,k⟩ ⟨l,m⟩ he
  have hi := congrArg Complex.im he
  have hj := rvmCriticalSlotAtom_im_bounds K hK ⟨j,k⟩
  have hl := rvmCriticalSlotAtom_im_bounds K hK ⟨l,m⟩
  have hjl : j=l := by
    have h1 : (j:ℝ)<(l:ℝ)+1 := by linarith only [hi,hj.1,hl.2]
    have h2 : (l:ℝ)<(j:ℝ)+1 := by linarith only [hi,hl.1,hj.2]
    have h1' : j<l+1 := by exact_mod_cast h1
    have h2' : l<j+1 := by exact_mod_cast h2
    omega
  subst l
  have heh : criticalSplineSlotHeight j (rvmCompletionBlockSize (j+1))
      ⟨k.val,lt_of_lt_of_le k.isLt (hK j)⟩=
    criticalSplineSlotHeight j (rvmCompletionBlockSize (j+1))
      ⟨m.val,lt_of_lt_of_le m.isLt (hK j)⟩ := by
    simpa only [rvmCriticalSlotAtom,criticalSplineSlotAtom,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      mul_one,zero_mul,add_zero] using hi
  have hFin := criticalSplineSlotHeight_injective j (rvmCompletionBlockSize (j+1)) heh
  have hkm : k=m := Fin.ext (congrArg (fun v : Fin (rvmCompletionBlockSize (j+1)) => v.val) hFin)
  subst m
  rfl

lemma rvmCompletionPositiveAtom_injective {ι : Type*} (z : ι → ℂ)
    (him : ∀ i,1≤(z i).im) (hre : ∀ i,0<(z i).re)
    (hinj : Function.Injective (prescribedSplineQuartetAtom z)) :
    Function.Injective (rvmCompletionPositiveAtom z) := by
  rintro ⟨j,a⟩ ⟨l,b⟩ he
  have hi := congrArg Complex.im he
  have hj := rvmCompletionPositiveAtom_bounds z him j a
  have hl := rvmCompletionPositiveAtom_bounds z him l b
  have hjl : j=l := by
    have h1 : (j:ℝ)<(l:ℝ)+1 := by linarith only [hi,hj.1,hl.2]
    have h2 : (l:ℝ)<(j:ℝ)+1 := by linarith only [hi,hl.1,hj.2]
    have h1' : j<l+1 := by exact_mod_cast h1
    have h2' : l<j+1 := by exact_mod_cast h2
    omega
  subst l
  rcases a with ⟨i,c⟩|k <;> rcases b with ⟨v,e⟩|m
  · have hh := rvmPositiveCoreAtom_injective z hinj he
    have hiv : i=v := Subtype.ext (congrArg Prod.fst hh)
    have hce : c=e := congrArg Prod.snd hh
    subst v
    subst e
    rfl
  · have hh := congrArg (fun w : ℂ => |w.re|) he
    change |(rvmPositiveCoreAtom z (i.val,c)).re|=|(rvmCriticalSlotAtom (rvmCompletionCriticalCount z) (rvmCompletionCriticalCount_le z) ⟨j,m⟩).re| at hh
    rw [rvmPositiveCoreAtom_abs_re,rvmCriticalSlotAtom_re,abs_zero,abs_of_pos (hre i.val)] at hh
    exact False.elim ((hre i.val).ne' hh)
  · have hh := congrArg (fun w : ℂ => |w.re|) he
    change |(rvmCriticalSlotAtom (rvmCompletionCriticalCount z) (rvmCompletionCriticalCount_le z) ⟨j,k⟩).re|=|(rvmPositiveCoreAtom z (v.val,e)).re| at hh
    rw [rvmPositiveCoreAtom_abs_re,rvmCriticalSlotAtom_re,abs_zero,abs_of_pos (hre v.val)] at hh
    exact False.elim ((hre v.val).ne' hh.symm)
  · have hh := rvmCriticalSlotAtom_injective _ (rvmCompletionCriticalCount_le z) he
    have hkm : k=m := by
      simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hh
    subst m
    rfl

theorem exists_rvmCompletionPositiveAtom_count {ι : Type*} (z : ι → ℂ)
    (him : ∀ i,1≤(z i).im)
    (hlocal : ∀ T : ℝ, Nonempty ({i : ι // (z i).im ∈ Set.Icc T (T+1)} ↪ Fin 3)) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ T : ℝ in Filter.atTop,
      |(Nat.card {a : (j : ℕ) × RVMCompletionBlock z j //
        (rvmCompletionPositiveAtom z a).im≤T}:ℝ)-_root_.RHTower.routeKSmoothRVMCount T|≤C*Real.log T := by
  letI (j : ℕ) := splineCoreBlockFintype z him hlocal j
  letI (j : ℕ) : Fintype (RVMCompletionBlock z j) :=
    inferInstanceAs (Fintype ((SplineCoreBlock z j × Bool) ⊕ Fin (rvmCompletionCriticalCount z j)))
  exact exists_unit_block_rvm_count (fun j a => (rvmCompletionPositiveAtom z ⟨j,a⟩).im)
    (rvmCompletionPositiveAtom_bounds z him) (fun j => rvmCompletionBlock_card z him hlocal j)

theorem finite_rvmCompletionPositive_truncation {ι : Type*} (z : ι → ℂ)
    (him : ∀ i,1≤(z i).im)
    (hlocal : ∀ T : ℝ, Nonempty ({i : ι // (z i).im ∈ Set.Icc T (T+1)} ↪ Fin 3))
    (T : ℝ) : Finite {a : (j : ℕ) × RVMCompletionBlock z j //
      (rvmCompletionPositiveAtom z a).im≤T} := by
  letI (j : ℕ) := splineCoreBlockFintype z him hlocal j
  by_cases hT : 1≤T
  · exact (finite_unit_block_count_sandwich
      (fun j a => (rvmCompletionPositiveAtom z ⟨j,a⟩).im)
      (rvmCompletionPositiveAtom_bounds z him) hT).1
  · letI : IsEmpty {a : (j : ℕ) × RVMCompletionBlock z j //
        (rvmCompletionPositiveAtom z a).im≤T} := ⟨fun a => by
      have hh := (rvmCompletionPositiveAtom_bounds z him a.val.1 a.val.2).1
      have hj := Nat.cast_nonneg (α := ℝ) a.val.1
      have ha := a.property
      exact hT (by linarith only [hh,hj,ha])⟩
    infer_instance

lemma rvmCompletionPositiveAtom_coefficient_ne_zero {ι : Type*} (z : ι → ℂ)
    (hc : ∀ i,splineMomentCoefficient (z i)≠0)
    (a : (j : ℕ) × RVMCompletionBlock z j) :
    splineMomentCoefficient (rvmCompletionPositiveAtom z a)≠0 := by
  rcases a with ⟨j,⟨i,b⟩|k⟩
  · cases b
    · exact hc i.val
    · change splineMomentCoefficient (-(starRingEnd ℂ) (z i.val))≠0
      rw [splineMomentCoefficient_neg,splineMomentCoefficient_conj]
      intro he
      apply hc i.val
      exact (starRingEnd ℂ).injective (he.trans (map_zero _).symm)
  · exact rvmCriticalSlotAtom_coefficient_ne_zero (rvmCompletionCriticalCount z) (rvmCompletionCriticalCount_le z) ⟨j,k⟩

lemma rvmCompletionPositiveAtom_width {ι : Type*} (z : ι → ℂ) {D : ℝ}
    (hD : 0<D) (hz : ∀ i,0≤(z i).re ∧ (z i).re<D)
    (a : (j : ℕ) × RVMCompletionBlock z j) :
    |(rvmCompletionPositiveAtom z a).re|<D := by
  rcases a with ⟨j,⟨i,b⟩|k⟩
  · change |(rvmPositiveCoreAtom z (i.val,b)).re|<D
    rw [rvmPositiveCoreAtom_abs_re,abs_of_nonneg (hz i.val).1]
    exact (hz i.val).2
  · simpa only [rvmCompletionPositiveAtom,rvmCriticalSlotAtom_re,abs_zero] using hD

lemma rvmCompletionPositiveAtom_width_cofinal {ι : Type*} (z : ι → ℂ) {D : ℝ}
    (hw : ∀ r : ℝ,r<D → ∃ i,r<(z i).re) :
    ∀ r : ℝ,r<D → ∃ a : (j : ℕ) × RVMCompletionBlock z j,
      r<(rvmCompletionPositiveAtom z a).re := by
  intro r hr
  obtain ⟨i,hi⟩ := hw r hr
  exact ⟨⟨splineCoreBlockLabel z i,Sum.inl (⟨i,rfl⟩,false)⟩,hi⟩

lemma rvmCompletionPositiveAtom_reflection {ι : Type*} (z : ι → ℂ)
    (a : (j : ℕ) × RVMCompletionBlock z j) :
    ∃ b : (j : ℕ) × RVMCompletionBlock z j,
      rvmCompletionPositiveAtom z b= -(starRingEnd ℂ) (rvmCompletionPositiveAtom z a) := by
  rcases a with ⟨j,⟨i,b⟩|k⟩
  · refine ⟨⟨j,Sum.inl (i,!b)⟩,?_⟩
    cases b <;> simp [rvmCompletionPositiveAtom,rvmPositiveCoreAtom,prescribedSplineQuartetAtom]
  · refine ⟨⟨j,Sum.inr k⟩,?_⟩
    change rvmCriticalSlotAtom (rvmCompletionCriticalCount z) (rvmCompletionCriticalCount_le z) ⟨j,k⟩= -(starRingEnd ℂ) (rvmCriticalSlotAtom (rvmCompletionCriticalCount z) (rvmCompletionCriticalCount_le z) ⟨j,k⟩)
    rw [conj_rvmCriticalSlotAtom,neg_neg]

/-- Adjoining the negative of each positive-height atom gives an even divisor. -/
def signedSplineAtom {α : Type*} (w : α → ℂ) (a : α × Bool) : ℂ :=
  if a.2 then -w a.1 else w a.1

lemma signedSplineAtom_injective {α : Type*} (w : α → ℂ)
    (hinj : Function.Injective w) (him : ∀ a,0<(w a).im) :
    Function.Injective (signedSplineAtom w) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ he
  have hi := congrArg Complex.im he
  have hbd : b=d := by
    cases b <;> cases d
    · rfl
    · simp only [signedSplineAtom,Bool.false_eq_true,if_false,if_true,Complex.neg_im] at hi
      exfalso
      linarith only [hi,him a,him c]
    · simp only [signedSplineAtom,Bool.false_eq_true,if_false,if_true,Complex.neg_im] at hi
      exfalso
      linarith only [hi,him a,him c]
    · rfl
  subst d
  have hw : w a=w c := by
    cases b <;> simpa only [signedSplineAtom,Bool.false_eq_true,if_false,if_true,neg_inj] using he
  have hac := hinj hw
  subst c
  rfl

lemma signedSplineAtom_neg {α : Type*} (w : α → ℂ) (a : α × Bool) :
    signedSplineAtom w (a.1,!a.2)= -signedSplineAtom w a := by
  rcases a with ⟨a,b⟩
  cases b <;> simp [signedSplineAtom]

lemma signedSplineAtom_abs_re {α : Type*} (w : α → ℂ) (a : α × Bool) :
    |(signedSplineAtom w a).re|=|(w a.1).re| := by
  rcases a with ⟨a,b⟩
  cases b <;> simp [signedSplineAtom]

lemma signedSplineAtom_coefficient_ne_zero {α : Type*} (w : α → ℂ)
    (hc : ∀ a,splineMomentCoefficient (w a)≠0) (a : α × Bool) :
    splineMomentCoefficient (signedSplineAtom w a)≠0 := by
  rcases a with ⟨a,b⟩
  cases b <;> simpa [signedSplineAtom,splineMomentCoefficient_neg] using hc a

/-- The positive part of the signed divisor has exactly the original positive count. -/
def signedSplineCountEquiv {α : Type*} (w : α → ℂ)
    (him : ∀ a,0<(w a).im) (T : ℝ) :
    {a : α // (w a).im≤T} ≃
      {a : α × Bool // 0<(signedSplineAtom w a).im ∧ (signedSplineAtom w a).im≤T} where
  toFun a := ⟨(a.val,false),him a.val,a.property⟩
  invFun a := ⟨a.val.1,by
    have ha := a.property
    rcases a with ⟨⟨a,b⟩,hab⟩
    cases b
    · exact ha.2
    · have hh : 0< -(w a).im := ha.1
      exfalso
      linarith only [hh,him a]⟩
  left_inv := by intro a; rfl
  right_inv := by
    rintro ⟨⟨a,b⟩,ha⟩
    cases b
    · rfl
    · have hh : 0< -(w a).im := ha.1
      exfalso
      linarith only [hh,him a]

#print axioms rvmCompletionPositiveAtom_injective
#print axioms exists_rvmCompletionPositiveAtom_count
#print axioms finite_rvmCompletionPositive_truncation
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
