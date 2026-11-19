import GaloisForLFunctions.HTGeometry.Lattices.IntegralNormTwoCoordinates

/-!
# The 240 minimal vectors in doubled E₈ coordinates

The doubled lattice has uniform coordinate parity and coordinate sum
divisible by four. At squared norm eight its even vectors come from
the D₈ shell. Its odd vectors are sign vectors with one parity
constraint. Seven signs determine the eighth.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HTGeometry.EightShell
open IntegralZeroSum

def compatible (x : Fin 8 → ℤ) := (∀ i, x i%2=x 0%2) ∧ (∑ i, x i)%4=0
abbrev Shell := {x : Fin 8 → ℤ // compatible x ∧ energy x=8}

/-- Even minimal vectors are obtained by doubling unrestricted norm-two
integer vectors. Their coordinate sum is automatically divisible by four. -/
def evenVector (y : TwoShell (Fin 8)) : Shell := by
  let x := fun i => 2*y.val i
  have hs := energy_sub_sum_even y.val
  obtain ⟨k,hk⟩ := hs
  rw [y.property] at hk
  refine ⟨x,⟨fun i => by simp [x],?_⟩,?_⟩
  · dsimp only [x]
    rw [← mul_sum]
    omega
  · change (∑ i, (2*y.val i)^2)=8
    simp only [mul_pow,← mul_sum]
    change (2:ℤ)^2*energy y.val=8
    rw [y.property]
    norm_num

private def sumSeven (s : Fin 7 → Bool) := ∑ i, unitSign (s i)

private theorem sumSeven_odd (s : Fin 7 → Bool) : ∃ k : ℤ, sumSeven s=7+2*k := by
  let k := fun i => if s i then (-1:ℤ) else 0
  have e (i) : unitSign (s i)=1+2*k i := by cases h : s i <;> norm_num [unitSign,k,h]
  refine ⟨∑ i,k i,?_⟩
  simp only [sumSeven,e,sum_add_distrib,← mul_sum,sum_const,card_univ,Fintype.card_fin]
  norm_num

private def lastSign (s : Fin 7 → Bool) : ℤ := if (sumSeven s+1)%4=0 then 1 else -1

private theorem lastSign_spec (s : Fin 7 → Bool) :
    (lastSign s=1 ∨ lastSign s= -1) ∧ (sumSeven s+lastSign s)%4=0 := by
  obtain ⟨k,hk⟩ := sumSeven_odd s
  unfold lastSign
  split <;> omega

/-- One compensating sign imposes the E₈ parity constraint. -/
def oddVector (s : Fin 7 → Bool) : Shell := by
  let x := Fin.snoc (fun i => unitSign (s i)) (lastSign s)
  have unit (i : Fin 8) : x i=1 ∨ x i= -1 := by
    refine Fin.lastCases (by simpa [x] using (lastSign_spec s).1) (fun i => ?_) i
    cases h : s i <;> simp [x,unitSign,h]
  refine ⟨x,⟨fun i => by rcases unit i with h|h <;> rcases unit 0 with h'|h' <;> omega,?_⟩,?_⟩
  · simpa only [Fin.sum_univ_castSucc,x,Fin.snoc_castSucc,Fin.snoc_last,sumSeven] using (lastSign_spec s).2
  · have he (i) : (x i)^2=1 := by rcases unit i with h|h <;> rw [h] <;> norm_num
    simp [energy,he]

private theorem odd_units (x : Shell) (ho : x.val 0%2≠0) (i : Fin 8) : x.val i=1 ∨ x.val i= -1 := by
  have nonzero (j : Fin 8) : x.val j≠0 := by
    have h := x.property.1.1 j
    intro e
    rw [e] at h
    omega
  have positive (j : Fin 8) : 0≤(x.val j)^2-1 := by have h := sq_pos_of_ne_zero (nonzero j); omega
  have total : ∑ j, ((x.val j)^2-1)=0 := by
    rw [sum_sub_distrib,show ∑ j,(x.val j)^2=8 from x.property.2]
    norm_num
  have e := (sum_eq_zero_iff_of_nonneg fun j _ => positive j).mp total i (mem_univ i)
  have prod : (x.val i-1)*(x.val i+1)=0 := by linear_combination e
  rcases mul_eq_zero.mp prod with h|h <;> omega

/-- All 112 doubled coordinate roots and all 128 spin signs occur exactly once. -/
def shellEquiv : TwoShell (Fin 8) ⊕ (Fin 7 → Bool) ≃ Shell := by
  classical
  apply Equiv.ofBijective (Sum.elim evenVector oddVector)
  constructor
  · rintro (x|s) (y|t) h
    · apply congrArg Sum.inl
      apply Subtype.ext
      funext i
      have e := congrArg (fun z : Shell => z.val i) h
      change 2*x.val i=2*y.val i at e
      omega
    · have e := congrArg (fun z : Shell => z.val (Fin.last 7)) h
      change 2*x.val (Fin.last 7)=Fin.snoc _ (lastSign t) _ at e
      rw [Fin.snoc_last] at e
      rcases (lastSign_spec t).1 with hh|hh <;> omega
    · have e := congrArg (fun z : Shell => z.val (Fin.last 7)) h
      change Fin.snoc _ (lastSign s) _=2*y.val (Fin.last 7) at e
      rw [Fin.snoc_last] at e
      rcases (lastSign_spec s).1 with hh|hh <;> omega
    · apply congrArg Sum.inr
      funext i
      have e := congrArg (fun z : Shell => z.val i.castSucc) h
      change Fin.snoc _ (lastSign s) _=Fin.snoc _ (lastSign t) _ at e
      rw [Fin.snoc_castSucc,Fin.snoc_castSucc] at e
      cases hs : s i <;> cases ht : t i <;> simp_all [unitSign]
  · intro x
    by_cases he : x.val 0%2=0
    · let v := fun i => x.val i/2
      have hv (i) : 2*v i=x.val i := by dsimp [v]; have h := x.property.1.1 i; omega
      have e : energy x.val=4*energy v := by
        unfold energy
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        rw [← hv i]
        ring
      have eh := x.property.2
      refine ⟨Sum.inl (⟨v,by omega⟩ : TwoShell (Fin 8)),Subtype.ext (funext hv)⟩
    · let s := fun i : Fin 7 => decide (x.val i.castSucc<0)
      have hs (i : Fin 7) : unitSign (s i)=x.val i.castSucc := by
        rcases odd_units x he i.castSucc with e|e <;> simp [s,unitSign,e]
      have hlast : lastSign s=x.val (Fin.last 7) := by
        have hh := x.property.1.2
        rw [Fin.sum_univ_castSucc] at hh
        have e : sumSeven s=∑ i : Fin 7, x.val i.castSucc := sum_congr rfl fun i _ => hs i
        obtain ⟨unit,sum⟩ := lastSign_spec s
        rw [e] at sum
        rcases odd_units x he (Fin.last 7) with h|h <;> rcases unit with q|q <;> omega
      refine ⟨Sum.inr s,Subtype.ext (funext fun i => ?_)⟩
      refine Fin.lastCases (by simpa [oddVector] using hlast) (fun j => ?_) i
      simpa [oddVector] using hs j

theorem shell_card : Nat.card Shell=240 := by
  rw [← Nat.card_congr shellEquiv,Nat.card_sum,card_twoShell,Nat.card_fun,Nat.card_fin,
    Nat.card_eq_fintype_card (α:=Bool),Fintype.card_bool,Fintype.card_fin]
  norm_num [Nat.choose]

#print axioms evenVector
#print axioms oddVector
#print axioms shellEquiv
#print axioms shell_card
end GaloisForLFunctions.HTGeometry.EightShell
