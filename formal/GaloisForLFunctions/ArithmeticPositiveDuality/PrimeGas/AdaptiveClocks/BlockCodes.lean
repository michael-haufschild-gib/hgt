import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks.LocalCounting

/-!
# Finite codes for accepted pairs of fixed energy ranges

Record the smaller label, the excess of the larger label over the first
accepted entry in its row, and the two logarithmic bins. This includes
disconnected sets of allowed integers within a row.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks.Clock

open scoped Classical
variable (M : Clock)

abbrev Ordered := {p : M.Word // p.val.2 ≤ p.val.1}

def block (p : M.Ordered) : ℕ × ℕ :=
  (M.bin p.val.val.2,M.bin p.val.val.1 - M.bin p.val.val.2)

theorem upper_index (p : M.Ordered) : (M.block p).1+(M.block p).2 = M.bin p.val.val.1 :=
  Nat.add_sub_of_le (M.bin_mono p.property)

def total (k : ℕ × ℕ) := M.base k.1 + M.base (k.1+k.2)

def room (k : ℕ × ℕ) := M.spread * Real.exp (M.base (k.1+k.2)-(M.exponent : ℝ)*M.total k)

def lowSlots (k : ℕ × ℕ) := ⌊Real.exp (M.base k.1+M.step)⌋₊

def highSlots (k : ℕ × ℕ) := ⌊M.room k⌋₊+1

abbrev Code := Σ k : ℕ × ℕ, Fin (M.lowSlots k) × Fin (M.highSlots k)

private def Entry (i : ℕ) (b : ℕ+) (n : ℕ) := ∃ a : ℕ+, a.val = n ∧ M.bin a = i ∧ M.Passes (a,b)

private def first (i : ℕ) (b : ℕ+) := if h : ∃ n, M.Entry i b n then Nat.find h else 0

private theorem first_spec (a b : ℕ+) (ha : M.Passes (a,b)) :
    M.Entry (M.bin a) b (M.first (M.bin a) b) ∧ M.first (M.bin a) b ≤ a.val := by
  have he : M.Entry (M.bin a) b a.val := ⟨a,rfl,rfl,ha⟩
  have hex : ∃ n, M.Entry (M.bin a) b n := ⟨_,he⟩
  rw [first,dif_pos hex]
  exact ⟨Nat.find_spec hex,Nat.find_min' hex he⟩

private def lowSlot (p : M.Ordered) : Fin (M.lowSlots (M.block p)) := by
  let b := p.val.val.2
  have hb : b.val ≤ M.lowSlots (M.block p) := Nat.le_floor
    ((exp_energy b).symm.le.trans (Real.exp_le_exp.mpr (M.bin_upper b)))
  exact ⟨b.val-1,by have := b.pos; omega⟩

private def highSlot (ht : M.time ≠ 0) (p : M.Ordered) : Fin (M.highSlots (M.block p)) := by
  let a := p.val.val.1
  let b := p.val.val.2
  refine ⟨a.val-M.first (M.bin a) b,Nat.lt_succ_of_le (Nat.le_floor ?_)⟩
  obtain ⟨⟨a',hfirst,hi,ha'⟩,hle⟩ := M.first_spec a b p.val.property
  rw [Nat.cast_sub hle,← hfirst]
  apply (le_abs_self _).trans
  have hd := M.row_diameter ht a a' b hi p.val.property ha'
  change _ ≤ M.spread*Real.exp (M.base ((M.block p).1+(M.block p).2) - (M.exponent : ℝ)*M.total (M.block p))
  rw [total,M.upper_index]
  change _ ≤ M.spread * Real.exp (M.base (M.bin a) - (M.exponent:ℝ)*(M.base (M.bin b)+M.base (M.bin a)))
  rw [add_comm (M.base (M.bin b)) (M.base (M.bin a))]
  exact hd

def encode (ht : M.time ≠ 0) (p : M.Ordered) : M.Code := ⟨M.block p,M.lowSlot p,M.highSlot ht p⟩

theorem encode_injective (ht : M.time ≠ 0) : Function.Injective (M.encode ht) := by
  intro p q he
  have hk : M.block p = M.block q := congrArg Sigma.fst he
  have hib : M.bin p.val.val.1 = M.bin q.val.val.1 :=
    (M.upper_index p).symm.trans ((congrArg (fun k : ℕ × ℕ => k.1+k.2) hk).trans (M.upper_index q))
  have hlow : p.val.val.2.val-1 = q.val.val.2.val-1 :=
    congrArg (fun z : M.Code => z.2.1.val) he
  have hb : p.val.val.2 = q.val.val.2 := PNat.coe_injective (by
    have hp := p.val.val.2.pos
    have hq := q.val.val.2.pos
    omega)
  have hhi : p.val.val.1.val-M.first (M.bin p.val.val.1) p.val.val.2 =
      q.val.val.1.val-M.first (M.bin q.val.val.1) q.val.val.2 := congrArg (fun z : M.Code => z.2.2.val) he
  have hp : M.first (M.bin p.val.val.1) p.val.val.2 ≤ p.val.val.1.val :=
    (M.first_spec p.val.val.1 p.val.val.2 p.val.property).2
  have hq : M.first (M.bin q.val.val.1) q.val.val.2 ≤ q.val.val.1.val :=
    (M.first_spec q.val.val.1 q.val.val.2 q.val.property).2
  rw [hib,hb] at hhi hp
  exact Subtype.ext (Subtype.ext (Prod.ext (PNat.coe_injective (by omega)) hb))

theorem block_weight {σ : ℝ} (hσ : 0 ≤ σ) (p : M.Ordered) :
    weight σ p.val.val ≤ Real.exp (-σ*M.total (M.block p)) := by
  rw [total,M.upper_index]
  change _ ≤ Real.exp (-σ * (M.base (M.bin p.val.val.2)+M.base (M.bin p.val.val.1)))
  rw [add_comm (M.base (M.bin p.val.val.2))]
  exact M.weight_le hσ p.val.val.1 p.val.val.2

#print axioms encode_injective
#print axioms block_weight

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks.Clock
