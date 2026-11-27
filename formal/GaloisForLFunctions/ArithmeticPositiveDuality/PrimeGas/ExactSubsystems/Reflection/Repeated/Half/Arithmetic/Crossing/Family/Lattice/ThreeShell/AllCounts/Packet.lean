import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.PrimeSquare
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts.Gap

/-! # Centered partition comparison for all multiplicities on three adjacent prime powers -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts

open Finset Real

abbrev States (l j r : ℕ) := Fin l ⊕ (Fin j ⊕ Fin r)

def occupations (l j r : ℕ) : States l j r → ℕ :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 2))

/-- Positive sign means the reflected centered partition exceeds the original one. -/
def reading (p : Nat.Primes) (l j r : ℕ) (t : ℝ) :=
  oddTrace (centered (primeModes p (occupations l j r))) t

def clock (p : Nat.Primes) (n : ℕ) (t : ℝ) := t*log p.val/n

theorem clock_pos (p : Nat.Primes) {n : ℕ} (hn : 0<n) {t : ℝ} (ht : 0<t) : 0<clock p n t :=
  div_pos (mul_pos ht (log_pos (Nat.one_lt_cast.mpr p.property.one_lt))) (Nat.cast_pos.mpr hn)

theorem clock_lt (p : Nat.Primes) {n : ℕ} (hn : 0<n) {t u : ℝ} (h : t<u) :
    clock p n t<clock p n u :=
  div_lt_div_of_pos_right (mul_lt_mul_of_pos_right h (log_pos (Nat.one_lt_cast.mpr p.property.one_lt)))
    (Nat.cast_pos.mpr hn)

private def offsets (l j r : ℕ) (n d : ℝ) : States l j r → ℝ :=
  Sum.elim (fun _ => -(n+d)) (Sum.elim (fun _ => -d) (fun _ => n-d))

private def shape (l j r n d x : ℝ) :=
  r*sinh ((n-d)*x)-j*sinh (d*x)-l*sinh ((n+d)*x)

private theorem formula (p : Nat.Primes) (l j r : ℕ) (t : ℝ) :
    reading p l j r t=2*shape l j r (l+j+r : ℕ) ((r : ℝ)-l) (clock p (l+j+r) t) := by
  let n : ℝ := ((l+j+r : ℕ) : ℝ)
  let d := (r : ℝ)-l
  by_cases nil : l+j+r=0
  · obtain ⟨rfl,rfl,rfl⟩ : l=0 ∧ j=0 ∧ r=0 := by omega
    simp [reading,oddTrace,shape,States]
  have nz : n≠0 := Nat.cast_ne_zero.mpr nil
  let D := offsets l j r n d
  have zero : (∑ i, D i)=0 := by
    simp only [D,offsets,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,sum_const,
      card_univ,Fintype.card_fin,nsmul_eq_mul,n,d,Nat.cast_add]
    ring
  have shifted : levels (occupations l j r)=fun i => (1/n)*D i+((n+d)/n) := by
    funext i
    rcases i with i | (i | i) <;> simp only [levels,occupations,D,offsets,Sum.elim_inl,
      Sum.elim_inr,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat] <;> field_simp <;> ring
  let x := clock p (l+j+r) t
  have term (z : ℝ) : oddTerm t (log p.val*((1/n)*z))=2*sinh (z*x) := by
    have arg : t*(log p.val*((1/n)*z))=z*x := by dsimp only [x,clock,n]; ring
    rw [oddTerm,neg_mul,arg,sinh_eq]
    ring
  rw [reading,Sparse.mode_grid,centered_affine,shifted,centered_affine,centered_eq_of_sum_zero zero]
  simp only [oddTrace,term,D,offsets,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,sum_const,
    card_univ,Fintype.card_fin,nsmul_eq_mul,neg_mul,sinh_neg,shape]
  change _=2*((r : ℝ)*sinh ((n-d)*x)-j*sinh (d*x)-l*sinh ((n+d)*x))
  ring

theorem reverse_reading (p : Nat.Primes) (l j r : ℕ) (t : ℝ) :
    reading p r j l t= -reading p l j r t := by
  rw [formula,formula,show r+j+l=l+j+r by omega]
  have eq : (l : ℝ)-r= -((r : ℝ)-l) := by ring
  rw [eq]
  simp only [shape,sub_neg_eq_add,← sub_eq_add_neg,neg_mul,sinh_neg]
  ring

/-- Multiplying the partition difference by the extreme-count imbalance
exhibits two positive-frequency gaps and integer weights. -/
theorem sorted_reading (p : Nat.Primes) (h j m : ℕ) (t : ℝ) :
    let n := h+j+(h+m)
    let x := clock p n t
    (m : ℝ)*reading p h j (h+m) t=
      2*((h+m : ℕ)*gap m ((n : ℝ)-m) x-h*gap m ((n : ℝ)+m) x) := by
  dsimp only
  rw [formula]
  simp only [shape,gap,Nat.cast_add,add_sub_cancel_left]
  ring

/-- Probe threshold for total count n and excess of m upper over lower states. -/
def threshold (n m : ℕ) (x : ℝ) := gap m ((n : ℝ)-m) x/gap m ((n : ℝ)+m) x

theorem threshold_strictAnti {n m : ℕ} (hm : 0< m) (hs : 2*m<n) :
    StrictAntiOn (threshold n m) (Set.Ioi 0) := by
  have pos : 0<(m : ℝ) := Nat.cast_pos.mpr hm
  have twice : 2*(m : ℝ)<n := by exact_mod_cast hs
  exact gap_ratio_strictAnti pos (by linarith only [twice]) (by linarith only [pos])

/-- Sorted and reversed packets compare the same threshold with opposite strict inequalities. -/
theorem sorted_bits (p : Nat.Primes) (h j m : ℕ) (hm : 0< m) {t : ℝ} (ht : 0<t) :
    let n := h+j+(h+m)
    let R := threshold n m (clock p n t)
    (0<reading p h j (h+m) t ↔ (h : ℝ)/(h+m : ℕ)<R) ∧
    (0<reading p (h+m) j h t ↔ R<(h : ℝ)/(h+m : ℕ)) := by
  let n := h+j+(h+m)
  let x := clock p n t
  have mp : 0<(m : ℝ) := Nat.cast_pos.mpr hm
  have np : 0<(n : ℝ) := Nat.cast_pos.mpr (by dsimp only [n]; omega)
  have den := gap_pos mp (show (m : ℝ)<n+m by linarith only [np]) (clock_pos p (n := n) (by dsimp only [n]; omega) ht)
  have hi : 0<((h+m : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have id := sorted_reading p h j m t
  change (m : ℝ)*reading p h j (h+m) t=2*(((h+m : ℕ) : ℝ)*gap m ((n : ℝ)-m) x-h*gap m ((n : ℝ)+m) x) at id
  dsimp only
  change (0<reading p h j (h+m) t ↔ (h : ℝ)/(h+m : ℕ)<threshold n m x) ∧
    (0<reading p (h+m) j h t ↔ threshold n m x<(h : ℝ)/(h+m : ℕ))
  rw [reverse_reading p h j (h+m) t,neg_pos,threshold,div_lt_div_iff₀ hi den,div_lt_div_iff₀ den hi]
  constructor
  · constructor
    · intro gt
      nlinarith only [id,mul_pos mp gt]
    · intro gt
      by_contra! non
      nlinarith only [id,mul_nonpos_of_nonneg_of_nonpos mp.le non,gt]
  · constructor
    · intro neg
      nlinarith only [id,mul_neg_of_pos_of_neg mp neg]
    · intro neg
      by_contra! non
      nlinarith only [id,mul_nonneg mp.le non,neg]

#print axioms reverse_reading
#print axioms sorted_reading
#print axioms sorted_bits

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts
