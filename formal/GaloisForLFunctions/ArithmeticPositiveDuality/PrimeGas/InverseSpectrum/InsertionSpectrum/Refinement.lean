import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InsertionSpectrum.Sector
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ComplexGibbs.RelativePartition

/-! # Ordered refinement of an interlacing band by occupation insertion -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

/-- Zero-based slot of the multiple indexed by `n`. -/
def sectorStart (a : ℕ+) (n : ℕ) := (a.val-1)+a.val*n

theorem sectorStart_succ (a : ℕ+) (n : ℕ) : sectorStart a (n+1) = sectorStart a n+a.val := by
  simp only [sectorStart,Nat.mul_succ,Nat.add_assoc]

theorem occupationWeight_sectorStart (a : ℕ+) (n : ℕ) :
    occupationWeight (sectorStart a n) = sectorWeight a*occupationWeight n := by
  have hp := a.pos
  have hi : sectorStart a n+1 = a.val*(n+1) := by
    rw [sectorStart,Nat.mul_succ]
    omega
  have hr : (sectorStart a n:ℝ)+1 = (a.val:ℝ)*((n:ℝ)+1) := by exact_mod_cast hi
  rw [occupationWeight_eq,occupationWeight_eq,hr,sectorWeight_eq_inv,mul_inv]

theorem sectorStart_tendsto (a : ℕ+) : Tendsto (sectorStart a) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro n
  exact (Nat.le_mul_of_pos_left n a.pos).trans (Nat.le_add_left _ _)

/-- Inside each block clip its scaled survivor to the current native interlacing interval. -/
def refinedSpectrum (a : ℕ+) (b : SpectralBand 1) (j : ℕ) :
    Set.Icc (occupationWeight (j+1)) (occupationWeight j) :=
  if j < a.val-1 then ⟨_,occupationWeight_antitone (Nat.le_succ j),le_rfl⟩ else
    let t := sectorWeight a*(b ((j-(a.val-1))/a.val)).val
    ⟨min (occupationWeight j) (max (occupationWeight (j+1)) t),
      le_min (occupationWeight_antitone (Nat.le_succ j)) (le_max_left _ _),min_le_left _ _⟩

theorem refined_prefix (a : ℕ+) (b : SpectralBand 1) {j : ℕ} (hj : j < a.val-1) :
    (refinedSpectrum a b j).val = occupationWeight j := by simp only [refinedSpectrum,if_pos hj]

theorem refined_block (a : ℕ+) (b : SpectralBand 1) (n r : ℕ) (hr : r < a.val) :
    (refinedSpectrum a b (sectorStart a n+r)).val =
      min (occupationWeight (sectorStart a n+r))
        (max (occupationWeight (sectorStart a n+r+1)) (sectorWeight a*(b n).val)) := by
  have hn : ¬sectorStart a n+r < a.val-1 := by unfold sectorStart; omega
  have hs : sectorStart a n+r-(a.val-1) = r+a.val*n := by unfold sectorStart; omega
  have hd : (r+a.val*n)/a.val = n := by
    rw [Nat.add_div_of_dvd_left (dvd_mul_right _ _),Nat.div_eq_of_lt hr,Nat.mul_div_cancel_left _ a.pos,zero_add]
  simp only [refinedSpectrum,if_neg hn]
  rw [hs,hd]

#print axioms sectorStart_succ
#print axioms occupationWeight_sectorStart
#print axioms sectorStart_tendsto
#print axioms refined_prefix
#print axioms refined_block

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
