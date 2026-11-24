import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.PNat.Basic

/-! # Finite intervals certifying exact factors of an occupation ladder -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

/-- Each occupation number has a unique digit and complementary occupation. -/
def tilesRay (A : Finset ℕ) (C : Set ℕ) : Prop :=
  Function.Bijective (fun v : A × C => v.1.val + v.2.val)

/-- The digit and translation sets cover exactly the first `L` occupations, without overlap. -/
def tilesInterval (A T : Finset ℕ) (L : ℕ) : Prop :=
  Function.Injective (fun v : A × T => v.1.val + v.2.val) ∧
    ∀ n, (∃ v : A × T, v.1.val + v.2.val = n) ↔ n < L

private def hit (C : Set ℕ) (n d : ℕ) := ∃ b ∈ C, d+b = n

private theorem hit_succ (C : Set ℕ) (n d : ℕ) : hit C (n+1) (d+1) ↔ hit C n d := by
  constructor <;> rintro ⟨b,hb,he⟩ <;> exact ⟨b,hb,by omega⟩

/-- The previous m possible starts, including the empty history at the vacuum. -/
private def history (C : Set ℕ) (m n : ℕ) : Set (Fin m) := {i | hit C n (i.val+1)}

private theorem largest_hit {A : Finset ℕ} {C : Set ℕ} (h : tilesRay A C)
    {m : ℕ} (hm : m ∈ A) (hmax : ∀ d ∈ A, d ≤ m) (n : ℕ) :
    hit C n m ↔ ¬ ∃ d : A, d.val < m ∧ hit C n d.val := by
  constructor
  · rintro ⟨b,hb,he⟩ ⟨d,hd,k,hk,hk'⟩
    have hh := h.1 (a₁ := (⟨m,hm⟩,⟨b,hb⟩)) (a₂ := (d,⟨k,hk⟩)) (he.trans hk'.symm)
    exact hd.ne (congrArg (fun u : A × C => u.1.val) hh).symm
  · intro hn
    obtain ⟨⟨d,b⟩,he⟩ := h.2 n
    have hitd : hit C n d.val := ⟨b.val,b.property,he⟩
    have hd : d.val = m := (hmax _ d.property).eq_of_not_lt (fun hl => hn ⟨d,hl,hitd⟩)
    exact hd ▸ hitd

/-- The maximal digit recovers the lost bit when a window is shifted backwards. -/
private theorem history_rewind {A : Finset ℕ} {C : Set ℕ} (h : tilesRay A C)
    {m : ℕ} (hm : m ∈ A) (hmax : ∀ d ∈ A, d ≤ m) (n k : ℕ)
    (he : history C m (n+1) = history C m (k+1)) : history C m n = history C m k := by
  have bits (j : Fin m) : hit C n j.val ↔ hit C k j.val :=
    (hit_succ C n j.val).symm.trans ((Set.ext_iff.mp he j).trans (hit_succ C k j.val))
  ext i
  change hit C n (i.val+1) ↔ hit C k (i.val+1)
  by_cases hi : i.val+1 < m
  · exact bits ⟨_,hi⟩
  · have ht := i.isLt
    rw [show i.val+1 = m by omega,largest_hit h hm hmax,largest_hit h hm hmax]
    exact not_congr (exists_congr fun d => and_congr_right fun hd => bits ⟨d.val,hd⟩)

private theorem rewind_to_zero {S : Type*} (f : ℕ → S)
    (h : ∀ n k, f (n+1) = f (k+1) → f n = f k) (p n : ℕ) (he : f (n+p) = f n) : f p = f 0 := by
  induction n with
  | zero => simpa using he
  | succ n ih => exact ih (h (n+p) n (by simpa only [Nat.succ_add] using he))

/-- A finite tile of the half-line closes at an empty cut within the number of possible histories. -/
theorem finite_interval_of_ray {A : Finset ℕ} {C : Set ℕ} (h : tilesRay A C) (hA : A.Nonempty) :
    ∃ L : ℕ+, L.val ≤ 2^(A.max' hA) ∧ ∃ T : Finset ℕ, tilesInterval A T L.val := by
  classical
  let m := A.max' hA
  have hm : m ∈ A := A.max'_mem hA
  have hmax : ∀ d ∈ A, d ≤ m := fun d hd => A.le_max' d hd
  let f := history C m
  obtain ⟨x,y,hne,he⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (2^m+1) => f i.val)
    (by simp : Fintype.card (Set (Fin m)) < Fintype.card (Fin (2^m+1)))
  have hr : ∃ i j : Fin (2^m+1), i < j ∧ f i.val = f j.val := by
    rcases lt_or_gt_of_ne hne with hl | hl
    · exact ⟨x,y,hl,he⟩
    · exact ⟨y,x,hl,he.symm⟩
  obtain ⟨i,j,hij,heq⟩ := hr
  let L := j.val-i.val
  have hij' : i.val < j.val := hij
  have hL : 0 < L := Nat.sub_pos_of_lt hij'
  have hbound := j.isLt
  have hempty := rewind_to_zero f (history_rewind h hm hmax) L i.val
    (by rw [show i.val+L = j.val by dsimp [L]; omega]; exact heq.symm)
  let T := (Finset.range L).filter (· ∈ C)
  have memT (b : ℕ) : b ∈ T ↔ b < L ∧ b ∈ C := by simp [T]
  refine ⟨⟨L,hL⟩,show L ≤ 2^m from (Nat.sub_le _ _).trans (Nat.le_of_lt_succ hbound),T,?_,?_⟩
  · intro u v huv
    have hh := h.1 (a₁ := (u.1,⟨u.2.val,((memT _).mp u.2.property).2⟩))
      (a₂ := (v.1,⟨v.2.val,((memT _).mp v.2.property).2⟩)) huv
    exact Prod.ext (congrArg (fun x : A × C => x.1) hh) (Subtype.ext (congrArg (fun x : A × C => x.2.val) hh))
  · intro n
    constructor
    · rintro ⟨⟨a,b⟩,rfl⟩
      change a.val + b.val < L
      obtain ⟨hb,hc⟩ := (memT _).mp b.property
      by_contra! hg
      have ha : a.val ≤ m := hmax _ a.property
      let k : Fin m := ⟨L-b.val-1,by omega⟩
      have hbit : k ∈ f L := ⟨b.val,hc,by dsimp [k]; omega⟩
      have hzero : hit C 0 (k.val+1) := (Set.ext_iff.mp hempty k).mp hbit
      obtain ⟨t,_,ht⟩ := hzero
      omega
    · intro hn
      change n < L at hn
      obtain ⟨⟨a,b⟩,he⟩ := h.2 n
      have hab : a.val+b.val = n := he
      exact ⟨(a,⟨b.val,(memT _).mpr ⟨by omega,b.property⟩⟩),hab⟩

#print axioms finite_interval_of_ray

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
