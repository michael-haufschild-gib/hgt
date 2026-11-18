import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.SeparatedWordBoxes
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

/-!
# Projective pencil obstruction over the ternary field

Project from three coordinate axes to three copies of the projective line,
all using the same homogeneous denominator. Three classes, each containing
three projectively distinct points, cannot have disjoint images across
classes in all three pencils. Two points per class are possible.
-/

namespace GaloisForLFunctions.RepresentationLifting
open Finset ArithmeticHarmonicAnalysis.Codes
open scoped Classical
noncomputable section

local notation "K" => ZMod 3
local notation "Point" => K × (Fin 3 → K)

/-- Homogeneous two-coordinate minor for the kth pencil. The formula
includes all points on the common hyperplane at infinity. -/
def pencilMinor (x y : Point) (k : Fin 3) := x.2 k*y.1-y.2 k*x.1

private theorem pencil_swap (x y : Point) (k : Fin 3) : pencilMinor y x k = -pencilMinor x y k := by
  simp only [pencilMinor,neg_sub]

/-- Each class is projectively injective. Between classes every pencil separates. -/
def separatedPencils {m : ℕ} (v : Fin 3 → Fin m → Point) : Prop :=
  (∀ g i j (t : Kˣ), v g i = (t:K) • v g j → i = j) ∧
    ∀ g h, g ≠ h → ∀ i j k, pencilMinor (v g i) (v h j) k ≠ 0

private theorem two_affine_classes {m : ℕ} (v : Fin 3 → Fin m → Point)
    (hv : separatedPencils v) :
    ∃ g h : Fin 3, g ≠ h ∧ (∀ i, (v g i).1 ≠ 0) ∧ (∀ i, (v h i).1 ≠ 0) := by
  have clean (g h : Fin 3) (hne : g ≠ h) (hg : ¬ ∀ i, (v g i).1 ≠ 0) : ∀ j, (v h j).1 ≠ 0 := by
    push Not at hg
    obtain ⟨i,hi⟩ := hg
    intro j hj
    exact hv.2 g h hne i j 0 (by simp [pencilMinor,hi,hj])
  by_cases h₀ : ∀ i, (v 0 i).1 ≠ 0
  · by_cases h₁ : ∀ i, (v 1 i).1 ≠ 0
    · exact ⟨0,1,by decide,h₀,h₁⟩
    · exact ⟨0,2,by decide,h₀,clean 1 2 (by decide) h₁⟩
  · exact ⟨1,2,by decide,clean 0 1 (by decide) h₀,clean 0 2 (by decide) h₀⟩

private def affineCoordinates (p : Point) (k : Fin 3) : Fin 3 := (p.2 k/p.1 : K)

/-- Choi–Jang's projective chart bound already holds with three representatives
per class, even allowing any one class to meet infinity. -/
theorem separatedPencils_card_le_two {m : ℕ} (v : Fin 3 → Fin m → Point) (hv : separatedPencils v) :
    m ≤ 2 := by
  obtain ⟨g,h,hne,hg,hh⟩ := two_affine_classes v hv
  let S (a : Fin 3) := univ.image fun i => affineCoordinates (v a i)
  have hcard (a : Fin 3) (ha : ∀ i, (v a i).1 ≠ 0) : (S a).card = m := by
    have hinj : Function.Injective (fun i => affineCoordinates (v a i)) := by
      intro i j he
      let t := Units.mk0 ((v a i).1/(v a j).1) (div_ne_zero (ha i) (ha j))
      apply hv.1 a i j t
      apply Prod.ext
      · change (v a i).1 = ((v a i).1/(v a j).1)*(v a j).1
        rw [div_mul_cancel₀ _ (ha j)]
      · funext k
        have hc : (v a i).2 k/(v a i).1=(v a j).2 k/(v a j).1 := congrFun he k
        change (v a i).2 k=((v a i).1/(v a j).1)*(v a j).2 k
        field_simp [ha i,ha j] at hc ⊢
        linear_combination hc
    simp only [S,card_image_of_injective _ hinj,card_univ,Fintype.card_fin]
  by_contra! hm
  obtain ⟨x,hx,y,hy,k,he⟩ := ternary_chart_collision (S g) (S h)
    ⟨by rw [hcard g hg]; omega,by rw [hcard h hh]; omega⟩
  obtain ⟨i,_,rfl⟩ := mem_image.mp hx
  obtain ⟨j,_,rfl⟩ := mem_image.mp hy
  apply hv.2 g h hne i j k
  exact sub_eq_zero.mpr ((div_eq_div_iff (hg i) (hh j)).mp
    (show (v g i).2 k/(v g i).1=(v h j).2 k/(v h j).1 from he))

private def finiteLeft (i : Fin 2) : Point := (1,![(i.castSucc : Fin 3),0,0])
private def finiteRight (i : Fin 2) : Point := (1,![(2:K),(i.succ : Fin 3),1])
private def infiniteClass (i : Fin 2) : Point := (0,![(1:K),1,(i.succ : Fin 3)])

private theorem succ_ne_zero (i : Fin 2) : (i.succ : K) ≠ 0 := fun h =>
  (Nat.succ_ne_zero i.val) (congrArg Fin.val (show i.succ=(0:Fin 3) from h))

private theorem finite_left_right (i j : Fin 2) (k : Fin 3) :
    pencilMinor (finiteLeft i) (finiteRight j) k ≠ 0 := by
  change (finiteLeft i).2 k * 1 - (finiteRight j).2 k * 1 ≠ 0
  rw [mul_one,mul_one,sub_ne_zero]
  fin_cases k
  · intro h
    have he : i.val=2 := congrArg Fin.val (show i.castSucc=(2:Fin 3) from h)
    exact (Nat.ne_of_lt i.isLt) he
  · exact (succ_ne_zero j).symm
  · exact zero_ne_one

private theorem infinity_nonzero (i : Fin 2) (k : Fin 3) : (infiniteClass i).2 k ≠ 0 := by
  fin_cases k
  · exact one_ne_zero
  · exact one_ne_zero
  · exact succ_ne_zero i

private theorem finite_infinity (p : Point) (h : p.1=1) (i : Fin 2) (k : Fin 3) :
    pencilMinor p (infiniteClass i) k ≠ 0 := by
  change p.2 k * 0 - (infiniteClass i).2 k * p.1 ≠ 0
  simpa only [h,mul_zero,mul_one,zero_sub,neg_ne_zero] using infinity_nonzero i k

private theorem finite_scalar {p q : Point} (hp : p.1=1) (hq : q.1=1)
    (t : Kˣ) (e : p=(t:K) • q) : p=q := by
  have ht := congrArg Prod.fst e
  change p.1=(t:K)*q.1 at ht
  rw [hp,hq,mul_one] at ht
  simpa only [← ht,one_smul] using e

/-- Two affine pairs and one pair at infinity simultaneously separate in
all three pencils, attaining the bound. -/
theorem separatedPencils_two : ∃ v : Fin 3 → Fin 2 → Point, separatedPencils v := by
  let v : Fin 3 → Fin 2 → Point := ![finiteLeft,finiteRight,infiniteClass]
  refine ⟨v,?_,?_⟩
  · intro g
    fin_cases g
    · intro i j t e
      have h := finite_scalar (p:=finiteLeft i) (q:=finiteLeft j) rfl rfl t e
      exact Fin.ext (congrArg (fun p : Point => ((p.2 0 : Fin 3)).val) h)
    · intro i j t e
      have h := finite_scalar (p:=finiteRight i) (q:=finiteRight j) rfl rfl t e
      exact Fin.ext (Nat.succ.inj (congrArg (fun p : Point => ((p.2 1 : Fin 3)).val) h))
    · intro i j t e
      change infiniteClass i = (t:K) • infiniteClass j at e
      have h : (1:K)=(t:K)*1 := congrArg (fun p : Point => p.2 0) e
      rw [mul_one] at h
      rw [← h,one_smul] at e
      exact Fin.ext (Nat.succ.inj (congrArg (fun p : Point => ((p.2 2 : Fin 3)).val) e))
  · have forward (g h : Fin 3) (gh : g<h) (i j : Fin 2) (k : Fin 3) :
        pencilMinor (v g i) (v h j) k ≠ 0 := by
      fin_cases g <;> fin_cases h <;> first
        | exfalso; revert gh; decide
        | exact finite_left_right i j k
        | exact finite_infinity (finiteLeft i) rfl j k
        | exact finite_infinity (finiteRight i) rfl j k
    intro g h gh i j k
    rcases lt_or_gt_of_ne gh with hl|hl
    · exact forward _ _ hl _ _ _
    · rw [pencil_swap]
      exact neg_ne_zero.mpr (forward _ _ hl _ _ _)

theorem separatedPencils_capacity :
    IsGreatest {m : ℕ | ∃ v : Fin 3 → Fin m → Point, separatedPencils v} 2 :=
  ⟨separatedPencils_two,fun _ ⟨v,hv⟩ => separatedPencils_card_le_two v hv⟩

end
end GaloisForLFunctions.RepresentationLifting
