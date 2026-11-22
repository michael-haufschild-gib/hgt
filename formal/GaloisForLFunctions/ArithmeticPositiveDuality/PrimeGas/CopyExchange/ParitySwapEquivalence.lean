import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange.PrimeModeCoordinates
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ParityPairingOperator

/-!
# Energy-preserving unitary conjugacy between prime parity and copy exchange

One blockwise Walsh transform intertwines every partial exchange with the
parity of the same primes in the second copy. It carries the surviving
square state to the physical diagonal state with equal integer labels.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange

open GaloisForLFunctions.HTGeometry ContinuousLinearMap
open scoped Classical

private def parityCoordinates : PairGas ≃ₗᵢ[ℂ] BlockGas blockDim :=
  lpDomCongr (p := 2) (by norm_num) parityLabel

/-- Switch from the parity basis to the exchange basis and transform the active prime bits. -/
def parityToExchange : PairGas ≃ₗᵢ[ℂ] PairGas :=
  parityCoordinates.trans ((blockWalsh blockDim).trans
    (lpDomCongr (p := 2) (by norm_num) exchangeLabel.symm))

private theorem transform_at (f : PairGas) (z : BlockIndex blockDim) :
    parityToExchange f (exchangeLabel z) = blockWalsh blockDim (parityCoordinates f) z := by
  change blockWalsh blockDim (parityCoordinates f) (exchangeLabel.symm (exchangeLabel z)) = _
  rw [Equiv.symm_apply_apply]

theorem parityToExchange_apply (f : PairGas) (b : Block) (v : Vertex (blockDim b)) :
    parityToExchange f (exchangeLabel ⟨b,v⟩) =
      ∑ w, Walsh.walshMatrix (blockDim b) v w * f (parityLabel ⟨b,w⟩) := by
  rw [transform_at,blockWalsh_apply]
  rfl

/-- The product of the signs of the odd second-copy occupations in D. -/
def partialParity (D : Set Nat.Primes) : PairGas →L[ℂ] PairGas :=
  lpDiagonalCLM (fun x => (-1 : ℂ)^((pairCubes x).bits.filter (fun p => p ∈ D)).card)
    zero_le_one (fun _ => by simp)

private theorem partialParity_label (D : Set Nat.Primes) (f : PairGas) (b : Block) (w : Vertex (blockDim b)) :
    partialParity D f (parityLabel ⟨b,w⟩) = Walsh.cubeSign (modeMask D b) w * f (parityLabel ⟨b,w⟩) := by
  rw [partialParity,lpDiagonalCLM_apply,mode_sign]

/-- Independent prime exchanges compose by symmetric difference. -/
theorem exchangeModes_comp (D E : Set Nat.Primes) (x : ℕ+ × ℕ+) :
    exchangeModes D (exchangeModes E x) = exchangeModes ((D \ E) ∪ (E \ D)) x := by
  obtain ⟨⟨b,v⟩,rfl⟩ := exchangeLabel.surjective x
  simp only [exchangeModes_label]
  apply congrArg (fun w : Vertex (blockDim b) => exchangeLabel ⟨b,w⟩)
  funext i
  by_cases hD : (mode b i : Nat.Primes) ∈ D <;> by_cases hE : (mode b i : Nat.Primes) ∈ E <;>
    simp [modeMask,flipBits,hD,hE]

/-- The individual basis states fixed by every prime exchange are exactly the equal-copy states. -/
theorem jointly_fixed_iff (x : ℕ+ × ℕ+) : (∀ D, exchangeModes D x = x) ↔ ∃ n, x = (n,n) := by
  constructor
  · intro h
    have he := (exchangeModes_all x).symm.trans (h Set.univ)
    exact ⟨x.1,Prod.ext rfl (congrArg Prod.fst he)⟩
  · rintro ⟨n,rfl⟩ D
    apply Prod.ext <;> apply label.symm.injective <;> apply Finsupp.ext <;> intro p
    · have h := exchangeModes_apply D (n,n) p
      rw [ite_self] at h
      exact congrArg Prod.fst h
    · have h := exchangeModes_apply D (n,n) p
      rw [ite_self] at h
      exact congrArg Prod.snd h

/-- The unitary permuting the two copies only at the specified primes. -/
def copyExchange (D : Set Nat.Primes) : PairGas ≃ₗᵢ[ℂ] PairGas :=
  lpDomCongr (p := 2) (by norm_num) (exchangeModes D)

theorem partialParity_intertwined (D : Set Nat.Primes) (f : PairGas) :
    parityToExchange (partialParity D f) = copyExchange D (parityToExchange f) := by
  apply lp.ext
  funext z
  obtain ⟨⟨b,v⟩,rfl⟩ := exchangeLabel.surjective z
  change parityToExchange (partialParity D f) _ = parityToExchange f (exchangeModes D (exchangeLabel ⟨b,v⟩))
  rw [exchangeModes_label,parityToExchange_apply,parityToExchange_apply]
  apply Finset.sum_congr rfl
  intro w _
  rw [partialParity_label,walsh_flip,mul_assoc]

theorem partialParity_all : partialParity Set.univ = secondParity := by
  ext f x
  obtain ⟨c,rfl⟩ := pairCubes.symm.surjective x
  simp only [partialParity,secondParity,lpDiagonalCLM_apply,Equiv.apply_symm_apply,Set.mem_univ,
    Finset.filter_true,cube_parity,Circle.coe_pow,Circle.coe_neg,Circle.coe_one]

/-- Second-copy Liouville parity is conjugate to the ordinary permutation of the two integer labels. -/
theorem parity_intertwines_swap (f : PairGas) (x : ℕ+ × ℕ+) :
    parityToExchange (secondParity f) x = parityToExchange f x.swap := by
  have h := congrArg (fun g : PairGas => g x) (partialParity_intertwined Set.univ f)
  change parityToExchange (partialParity Set.univ f) x = parityToExchange f (exchangeModes Set.univ x) at h
  simpa only [partialParity_all,exchangeModes_all] using h

/-- Every bounded shell multiplier commutes with the change of basis. -/
theorem parityToExchange_shell (m : ℕ+ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hm : ∀ n, ‖m n‖ ≤ C) (f : PairGas) :
    let M := lpDiagonalCLM (fun x : ℕ+ × ℕ+ => m (x.1*x.2)) hC (fun x => hm (x.1*x.2))
    parityToExchange (M f) = M (parityToExchange f) := by
  intro M
  apply lp.ext
  funext z
  obtain ⟨⟨b,v⟩,rfl⟩ := exchangeLabel.surjective z
  simp only [M,parityToExchange_apply,lpDiagonalCLM_apply,parityLabel_product,exchangeLabel_product,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => mul_left_comm _ _ _

/-- The zero-dimensional block sends a square survivor to the equal-copy coordinate with amplitude one. -/
theorem parityToExchange_diagonal (f : PairGas) (n : ℕ+) :
    parityToExchange f (n,n) = f (squareState n) := by
  let k := label.symm n
  let z := cubeCoordinates.symm (emptyCube k)
  have he : exchangeLabel z = (n,n) := by
    simp only [exchangeLabel,z,Equiv.trans_apply,Equiv.apply_symm_apply,empty_exchange,k]
  have hp : parityLabel z = squareState n := by
    simp only [parityLabel,z,Equiv.trans_apply,Equiv.apply_symm_apply,empty_parity,k]
  have hz : blockDim z.1 = 0 := by
    change Fintype.card ↥(0 : Occupation).support = 0
    simp
  rw [← he,transform_at,← hp]
  exact blockWalsh_empty blockDim (parityCoordinates f) z.1 z.2 hz

theorem parityToExchange_square_state (n : ℕ+) :
    parityToExchange (lp.single 2 (squareState n) (1 : ℂ)) = lp.single 2 (n,n) (1 : ℂ) := by
  apply ext_inner_right ℂ
  intro g
  obtain ⟨f,rfl⟩ := parityToExchange.surjective g
  rw [parityToExchange.inner_map_map,lp.inner_single_left,lp.inner_single_left,parityToExchange_diagonal]

#print axioms parityToExchange
#print axioms exchangeModes_comp
#print axioms jointly_fixed_iff
#print axioms partialParity_intertwined
#print axioms parity_intertwines_swap
#print axioms parityToExchange_shell
#print axioms parityToExchange_diagonal
#print axioms parityToExchange_square_state

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange
