import GaloisForLFunctions.ExceptionalLayerTheory.TheLastQuotientClassDetectsEveryRightZero
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheHalfDampedReceiverIsTheBoundaryEnergyOfItsDirichletSeries
import GaloisForLFunctions.ArithmeticDefectRigidity.TheRenormalizedCofactorActsOnPowerRowsByZeta

/-!
# Mellin energy of the last quotient classes

The last-class symbol is the sum of Mellin cells immediately preceding a
multiple of the width. Its squared line norm after division by the frequency
is another value of the same symbol: the cell indicator is idempotent.
-/

noncomputable section

open Complex MeasureTheory Filter Finset
open GaloisForLFunctions.TransHorizonIncidenceMechanics

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The quotient cell immediately preceding a multiple of the width. -/
def lastCellIndicator (q n : ℕ) : ℝ := if q ∣ n+1 then 1 else 0

private theorem lastCellIndicator_zero {q : ℕ} (hq : 2≤q) : lastCellIndicator q 0=0 :=
  if_neg (fun h => by have := Nat.le_of_dvd (by omega : 0<0+1) h; omega)

private theorem lastCellIndicator_bound (q : ℕ) {n : ℕ} (hn : 1≤n) :
    |lastCellIndicator q n| ≤ 1*(n:ℝ)^(1/2:ℝ) := by
  have h := Real.one_le_rpow (by exact_mod_cast hn : 1≤(n:ℝ)) (by norm_num : (0:ℝ)≤1/2)
  unfold lastCellIndicator
  split <;> simp only [abs_one,abs_zero,one_mul] <;> linarith only [h]

/-- The indicator selects exactly the Mellin cells contributing to the
Hurwitz difference, throughout its half-plane of absolute cell convergence. -/
theorem lastQuotientClassSymbol_eq_tsum_cells {q : ℕ} (hq : 2≤q) {s : ℂ} (hs : 0<s.re) :
    lastQuotientClassSymbol q s = ∑' n : ℕ, (lastCellIndicator q n : ℂ)*cmellinCell s n := by
  let u := 1/(q:ℝ)
  have hqR : 2≤(q:ℝ) := by exact_mod_cast hq
  have hp : 0<(q:ℝ) := by linarith only [hqR]
  have hu : 0<u := one_div_pos.mpr hp
  have hhalf : u≤1/2 := one_div_le_one_div_of_le (by norm_num) hqR
  let f := fun k : ℕ => q*(k+1)-1
  have hf (k : ℕ) : f k+1=q*(k+1) := by
    have hh := Nat.mul_pos (by omega : 0<q) (Nat.succ_pos k)
    dsimp only [f]; omega
  have hinj : Function.Injective f := by
    intro i j e
    have hh := congrArg (·+1) e
    rw [hf,hf] at hh
    exact Nat.succ.inj (Nat.eq_of_mul_eq_mul_left (by omega : 0<q) hh)
  let F := fun n : ℕ => (lastCellIndicator q n : ℂ)*cmellinCell s n
  have hsupport : Function.support F ⊆ Set.range f := by
    intro n hn
    by_cases hd : q ∣ n+1
    · obtain ⟨k,he⟩ := hd
      cases k with
      | zero => simp at he
      | succ k => exact ⟨k,by have := hf k; omega⟩
    · exact (hn (by simp [F,lastCellIndicator,hd])).elim
  have hreduce : (∑' n : ℕ, F n) = ∑' k : ℕ, F (f k) := by
    rw [← tsum_subtype_eq_of_support_subset hsupport]
    exact ((Equiv.ofInjective f hinj).tsum_eq fun i => F i.val).symm
  change _ = ∑' n : ℕ, F n
  rw [hreduce,lastQuotientClassSymbol,_root_.RHTower.hurwitzZeta_neg_sub_riemannZeta_eq hu hhalf hs,
    _root_.RHTower.shiftDiffSeries,← tsum_mul_left]
  apply tsum_congr
  intro k
  have hd : q ∣ f k+1 := ⟨k+1,hf k⟩
  have hscale : (f k:ℝ)=(q:ℝ)*((k:ℝ)+1-u) := by
    have hcast : (f k:ℝ)+1=(q:ℝ)*((k:ℝ)+1) := by exact_mod_cast hf k
    dsimp only [u]; field_simp; linear_combination (q:ℝ)*hcast
  have hnext : (f k:ℝ)+1=(q:ℝ)*((k:ℝ)+1) := by exact_mod_cast hf k
  have hl : 0≤(k:ℝ)+1-u := by linarith only [hhalf,Nat.cast_nonneg k]
  simp only [F,lastCellIndicator,if_pos hd,ofReal_one,one_mul,cmellinCell,
    _root_.RHTower.shiftDiffTerm,← sub_eq_add_neg]
  rw [hnext,hscale,ofReal_mul,ofReal_mul,Complex.mul_cpow_ofReal_nonneg hp.le hl,
    Complex.mul_cpow_ofReal_nonneg hp.le (by positivity),mul_sub,ofReal_natCast]

theorem mellin_lastCellIndicator {q : ℕ} (hq : 2≤q) {s : ℂ} (hs : 1/2<s.re) :
    mellin (stepSource (lastCellIndicator q)) (-s)=lastQuotientClassSymbol q s/s := by
  rw [mellin_stepSource_neg (lastCellIndicator_zero hq) (fun _ hn => lastCellIndicator_bound q hn) hs,
    lastQuotientClassSymbol_eq_tsum_cells hq (by linarith only [hs])]

/-- Exact energy on a vertical line. Its dependence on the width is given by
the real symbol at twice the real part. -/
theorem lastQuotientClassSymbol_lineEnergy {q : ℕ} (hq : 2≤q) {σ : ℝ} (hσ : 1/2<σ) :
    (∫ t : ℝ, ‖lastQuotientClassSymbol q ((σ:ℂ)+t*I)/((σ:ℂ)+t*I)‖^2) =
      Real.pi/σ*(lastQuotientClassSymbol q (2*σ:ℝ)).re := by
  have he := lineEnergy_stepSource_eq (lastCellIndicator_zero hq)
    (fun _ hn => lastCellIndicator_bound q hn) hσ
  have hpt (t : ℝ) := mellin_lastCellIndicator hq (s := (σ:ℂ)+t*I) (by simpa using hσ)
  simp_rw [hpt] at he
  rw [he,lastQuotientClassSymbol_eq_tsum_cells hq (by simp only [ofReal_re]; linarith only [hσ])]
  congr 1
  have hcast (n : ℕ) : (lastCellIndicator q n:ℂ)*cmellinCell (2*σ:ℝ) n =
      ((lastCellIndicator q n^2*mellinCell (2*σ) n : ℝ):ℂ) := by
    rw [ofReal_mul,ArithmeticDefectRigidity.ofReal_mellinCell]
    unfold lastCellIndicator
    split <;> simp [cmellinCell]
  simp_rw [hcast]
  rw [← ofReal_tsum,ofReal_re]

end GaloisForLFunctions.ExceptionalLayerTheory
