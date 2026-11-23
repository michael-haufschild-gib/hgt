import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedCechComplex
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedAffineCover

/-! On a joined cover the weighted differential is the sum of the
left differential and the signed right differential. -/

noncomputable section

open GlobalTheory.CechDR GaloisForLFunctions.HTGeometry.BorelWeil

namespace GlobalTheory.WH

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

private abbrev li (i : ι) : ι ⊕ₗ κ := toLex (Sum.inl i)
private abbrev ri (j : κ) : ι ⊕ₗ κ := toLex (Sum.inr j)

theorem sum_uni {M : Type} [AddCommMonoid M] (I : Finset ι) (J : Finset κ)
    (f : ι ⊕ₗ κ → M) :
    ∑ t ∈ uni I J, f t = (∑ i ∈ I, f (li i)) + ∑ j ∈ J, f (ri j) := by
  simp only [uni, Finset.sum_map, Finset.sum_disjSum, li, ri]
  rfl

private theorem erase_uni_left (I : Finset ι) (J : Finset κ) (i : ι) :
    (uni I J).erase (li i) = uni (I.erase i) J := by
  ext t
  rcases e : ofLex t with j | j <;> rw [← toLex_ofLex t, e] <;>
    simp [uni, li, Finset.mem_erase]

private theorem erase_uni_right (I : Finset ι) (J : Finset κ) (j : κ) :
    (uni I J).erase (ri j) = uni I (J.erase j) := by
  ext t
  rcases e : ofLex t with i | i <;> rw [← toLex_ofLex t, e] <;>
    simp [uni, ri, Finset.mem_erase]

private theorem cubeSign_uni_left (I : Finset ι) (J : Finset κ) (i : ι) :
    cubeSign (uni I J) (li i) = cubeSign I i := by
  unfold cubeSign cechSign belowCard
  congr 1
  rw [Finset.card_filter, Finset.card_filter, sum_uni]
  simp only [Sum.Lex.inl_lt_inl_iff, Sum.Lex.not_inr_lt_inl, if_false,
    Finset.sum_const_zero, add_zero]

private theorem cubeSign_uni_right (I : Finset ι) (J : Finset κ) (j : κ) :
    cubeSign (uni I J) (ri j) = (-1 : ℤ) ^ I.card * cubeSign J j := by
  unfold cubeSign cechSign belowCard
  rw [← pow_add]
  congr 1
  rw [Finset.card_filter, Finset.card_filter, sum_uni]
  simp

/-- Deleting a right index in the joined order contributes one sign for each
left index. -/
theorem wd_uni {k M : Type} [Field k] [AddCommGroup M] [Module k M]
    (w : ι ⊕ₗ κ → Module.End k M) (a : Finset (ι ⊕ₗ κ) → M) (I : Finset ι) (J : Finset κ) :
    wd w a (uni I J) = wd (fun i => w (li i)) (fun K => a (uni K J)) I +
      ((-1 : ℤ) ^ I.card) • wd (fun j => w (ri j)) (fun K => a (uni I K)) J := by
  rw [wd_apply, wd_apply, wd_apply, sum_uni, Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [cubeSign_uni_left]
    exact congrArg (fun s => cubeSign I i • w (li i) (a s)) (erase_uni_left I J i)
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [cubeSign_uni_right, mul_smul]
    exact congrArg (fun s => ((-1 : ℤ) ^ I.card) • cubeSign J j • w (ri j) (a s))
      (erase_uni_right I J j)

end GlobalTheory.WH
