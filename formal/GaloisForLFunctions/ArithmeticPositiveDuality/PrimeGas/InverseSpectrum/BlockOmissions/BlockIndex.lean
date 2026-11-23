import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.SpectralBand

/-! # Occupation coordinates after deleting a consecutive block -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

/-- Original level of the kth surviving occupation after deleting r levels beginning at N. -/
def skipIndex (N r k : ℕ) := if k < N then k else k+r

theorem skipIndex_strictMono (N r : ℕ) : StrictMono (skipIndex N r) := by
  intro i j hij
  unfold skipIndex
  split <;> split <;> omega

/-- The increasing injection from surviving occupation labels to all occupation labels. -/
def skipLabel (N r : ℕ) : ℕ+ ↪ ℕ+ where
  toFun n := number (skipIndex N r (n.val-1))
  inj' := by
    intro a b h
    have he := (skipIndex_strictMono N r).injective (number_injective h)
    apply PNat.coe_injective
    have ha := a.pos
    have hb := b.pos
    omega

theorem skipLabel_number (N r k : ℕ) : skipLabel N r (number k) = number (skipIndex N r k) := by
  rfl

theorem skipLabel_increases (N r : ℕ) (i : ℕ+) : i ≤ skipLabel N r i := by
  obtain ⟨k,rfl⟩ := number_surjective i
  rw [skipLabel_number]
  change k+1 ≤ skipIndex N r k+1
  unfold skipIndex
  split <;> omega

/-- The r deleted occupations, in increasing order. -/
def blockLabel (N r : ℕ) : Fin r ↪ ℕ+ where
  toFun j := number (N+j.val)
  inj' := fun _ _ he => Fin.ext (Nat.add_left_cancel (number_injective he))

theorem skipLabel_not_block (N r : ℕ) (i : ℕ+) (j : Fin r) :
    skipLabel N r i ≠ blockLabel N r j := by
  obtain ⟨k,rfl⟩ := number_surjective i
  rw [skipLabel_number]
  intro he
  have h := number_injective he
  change skipIndex N r k = N+j.val at h
  have hj := j.isLt
  unfold skipIndex at h
  split at h <;> omega

theorem mem_block_of_not_skipped {N r : ℕ} {i : ℕ+} (hi : i ∉ Set.range (skipLabel N r)) :
    i ∈ Set.range (blockLabel N r) := by
  obtain ⟨k,rfl⟩ := number_surjective i
  have hN : N ≤ k := by
    by_contra! h
    exact hi ⟨number k,by rw [skipLabel_number,skipIndex,if_pos h]⟩
  have hr : k < N+r := by
    by_contra! h
    have hg : ¬ k-r < N := by omega
    exact hi ⟨number (k-r),by rw [skipLabel_number,skipIndex,if_neg hg,show k-r+r=k by omega]⟩
  exact ⟨⟨k-N,by omega⟩,congrArg number (show N+(k-N)=k by omega)⟩

/-- Ordered squared singular values of the ideal block deletion. -/
def blockSpectrum (N r : ℕ) : SpectralBand r := fun k =>
  ⟨occupationWeight (skipIndex N r k),
    occupationWeight_antitone (by unfold skipIndex; split <;> omega),
    occupationWeight_antitone (by unfold skipIndex; split <;> omega)⟩

#print axioms skipIndex_strictMono
#print axioms mem_block_of_not_skipped

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
