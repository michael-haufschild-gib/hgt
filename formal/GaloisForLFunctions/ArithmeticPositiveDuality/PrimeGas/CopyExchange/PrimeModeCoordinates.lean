import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange.OccupationCharts
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange.WalshBlocks

/-!
# Binary orientations of the active primes

The two energy-preserving charts use identical block indices. Toggling a bit
in the exchange chart swaps the two occupations at exactly that prime.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange

open scoped Classical

abbrev Block := Occupation × Occupation

def blockDim (b : Block) := Fintype.card ↥b.1.support

def mode (b : Block) : Fin (blockDim b) ≃ ↥b.1.support := (Fintype.equivFin _).symm

private def modeEmbedding (b : Block) : Fin (blockDim b) ↪ Nat.Primes :=
  (mode b).toEmbedding.trans (Function.Embedding.subtype _)

private def selected (b : Block) (v : Vertex (blockDim b)) : Finset Nat.Primes :=
  (Finset.univ.filter (fun i => v i = true)).map (modeEmbedding b)

private theorem selected_allowed (b : Block) (v : Vertex (blockDim b)) : selected b v ⊆ b.1.support := by
  intro p hp
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hp
  exact (mode b i).property

private theorem mem_selected (b : Block) (v : Vertex (blockDim b)) (i : Fin (blockDim b)) :
    (mode b i : Nat.Primes) ∈ selected b v ↔ v i = true := by
  constructor
  · intro h
    obtain ⟨j,hj,he⟩ := Finset.mem_map.mp h
    have hji : j = i := (modeEmbedding b).injective he
    exact hji ▸ (Finset.mem_filter.mp hj).2
  · intro h
    exact Finset.mem_map.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩

def cubeCoordinates : BlockIndex blockDim ≃ OccupationCube where
  toFun x := ⟨x.1.1,x.1.2,selected x.1 x.2,selected_allowed _ _⟩
  invFun c := ⟨(c.residual,c.pairs), fun i => decide ((mode (c.residual,c.pairs) i : Nat.Primes) ∈ c.bits)⟩
  left_inv := by
    rintro ⟨⟨a,k⟩,v⟩
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    funext i
    change decide ((mode (a,k) i : Nat.Primes) ∈ selected (a,k) v) = v i
    cases hv : v i with
    | false => exact decide_eq_false (fun h => Bool.noConfusion (hv.symm.trans ((mem_selected (a,k) v i).mp h)))
    | true => exact decide_eq_true ((mem_selected (a,k) v i).mpr hv)
  right_inv := by
    intro c
    apply OccupationCube.ext
    · rfl
    · rfl
    ext p
    let b : Block := (c.residual,c.pairs)
    let v : Vertex (blockDim b) := fun j => decide ((mode b j : Nat.Primes) ∈ c.bits)
    change p ∈ selected b v ↔ p ∈ c.bits
    by_cases h : p ∈ c.residual.support
    · obtain ⟨i,hi⟩ := (mode b).surjective (⟨p,h⟩ : ↥b.1.support)
      have he : (mode b i : Nat.Primes) = p := congrArg Subtype.val hi
      rw [← he,mem_selected]
      simp [v]
    · exact iff_of_false (fun hp => h (selected_allowed _ _ hp)) (fun hp => h (c.allowed hp))

def parityLabel : BlockIndex blockDim ≃ (ℕ+ × ℕ+) := cubeCoordinates.trans pairCubes.symm

def exchangeLabel : BlockIndex blockDim ≃ (ℕ+ × ℕ+) := cubeCoordinates.trans exchangeCubes.symm

theorem parityLabel_product (b : Block) (v : Vertex (blockDim b)) :
    (parityLabel ⟨b,v⟩).1 * (parityLabel ⟨b,v⟩).2 = label (b.1+(b.2+b.2)) :=
  cube_product (cubeCoordinates ⟨b,v⟩)

theorem exchangeLabel_product (b : Block) (v : Vertex (blockDim b)) :
    (exchangeLabel ⟨b,v⟩).1 * (exchangeLabel ⟨b,v⟩).2 = label (b.1+(b.2+b.2)) :=
  exchange_total (cubeCoordinates ⟨b,v⟩)

/-- Active bits belonging to the observed set of primes. -/
def modeMask (D : Set Nat.Primes) (b : Block) : Vertex (blockDim b) := fun i => decide ((mode b i : Nat.Primes) ∈ D)

theorem mode_sign (D : Set Nat.Primes) (b : Block) (v : Vertex (blockDim b)) :
    GaloisForLFunctions.HTGeometry.Walsh.cubeSign (modeMask D b) v =
      (-1 : ℂ)^((pairCubes (parityLabel ⟨b,v⟩)).bits.filter (fun p => p ∈ D)).card := by
  rw [cubeSign_eq_card]
  change _ = (-1 : ℂ)^((pairCubes (pairCubes.symm (cubeCoordinates ⟨b,v⟩))).bits.filter _).card
  rw [Equiv.apply_symm_apply]
  change _ = (-1 : ℂ)^((selected b v).filter _).card
  rw [selected, Finset.filter_map, Finset.card_map, Finset.filter_filter]
  congr 2
  ext i
  simp [modeMask,modeEmbedding,and_comm]

private def flipPoint (D : Set Nat.Primes) (x : BlockIndex blockDim) : BlockIndex blockDim :=
  ⟨x.1,flipBits (modeMask D x.1) x.2⟩

private theorem flip_twice (D : Set Nat.Primes) : Function.Involutive (flipPoint D) := by
  rintro ⟨b,v⟩
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  funext i
  change flipBits (modeMask D b) (flipBits (modeMask D b) v) i = v i
  cases h : modeMask D b i <;> simp [flipBits,h]

private def flipIndex (D : Set Nat.Primes) : Equiv.Perm (BlockIndex blockDim) :=
  ⟨flipPoint D,flipPoint D,flip_twice D,flip_twice D⟩

/-- Exchange the copies at the primes in D. -/
def exchangeModes (D : Set Nat.Primes) : Equiv.Perm (ℕ+ × ℕ+) :=
  exchangeLabel.symm.trans ((flipIndex D).trans exchangeLabel)

theorem exchangeModes_label (D : Set Nat.Primes) (b : Block) (v : Vertex (blockDim b)) :
    exchangeModes D (exchangeLabel ⟨b,v⟩) = exchangeLabel ⟨b,flipBits (modeMask D b) v⟩ := by
  simp only [exchangeModes, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

/-- Exchange is literal on the prime exponents of the two positive integers. -/
theorem exchangeModes_apply (D : Set Nat.Primes) (x : ℕ+ × ℕ+) (p : Nat.Primes) :
    (label.symm (exchangeModes D x).1 p, label.symm (exchangeModes D x).2 p) =
      if p ∈ D then (label.symm x.2 p, label.symm x.1 p) else (label.symm x.1 p, label.symm x.2 p) := by
  obtain ⟨⟨b,v⟩,rfl⟩ := exchangeLabel.surjective x
  rw [exchangeModes_label]
  have read (w : Vertex (blockDim b)) :
      label.symm (exchangeLabel ⟨b,w⟩).1 p = b.2 p + (if p ∈ selected b w then 0 else b.1 p) ∧
      label.symm (exchangeLabel ⟨b,w⟩).2 p = b.2 p + (if p ∈ selected b w then b.1 p else 0) :=
    exchange_occupations (cubeCoordinates ⟨b,w⟩) p
  rw [(read _).1,(read _).2,(read v).1,(read v).2]
  by_cases hp : p ∈ b.1.support
  · obtain ⟨i,hi⟩ := (mode b).surjective (⟨p,hp⟩ : ↥b.1.support)
    have he : (mode b i : Nat.Primes) = p := congrArg Subtype.val hi
    rw [← he]
    simp only [mem_selected]
    by_cases h : (mode b i : Nat.Primes) ∈ D <;> cases hv : v i <;> simp [modeMask,flipBits,h,hv]
  · have hz : b.1 p = 0 := not_not.mp (mt Finsupp.mem_support_iff.mpr hp)
    simp [hz]

theorem exchangeModes_all (x : ℕ+ × ℕ+) : exchangeModes Set.univ x = x.swap := by
  apply Prod.ext <;> apply label.symm.injective <;> apply Finsupp.ext <;> intro p
  · exact congrArg Prod.fst (by simpa only [Set.mem_univ,if_true] using exchangeModes_apply Set.univ x p)
  · exact congrArg Prod.snd (by simpa only [Set.mem_univ,if_true] using exchangeModes_apply Set.univ x p)

#print axioms cubeCoordinates
#print axioms mode_sign
#print axioms exchangeModes_apply
#print axioms exchangeModes_all

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange
