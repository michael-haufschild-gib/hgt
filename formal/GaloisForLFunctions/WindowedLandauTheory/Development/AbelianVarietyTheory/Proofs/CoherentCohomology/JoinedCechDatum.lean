import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LinearCechComplex
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechEdge
import Mathlib.LinearAlgebra.Pi

/-! Two joined covers have a Čech differential given by the sum of the
two slice differentials, with the parity sign on the right slice. -/

noncomputable section

open GlobalTheory.WH GaloisForLFunctions.HTGeometry.BorelWeil

namespace HTGeometry.FinsetCechDatum

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

private abbrev li (i : ι) : ι ⊕ₗ κ := toLex (Sum.inl i)
private abbrev ri (j : κ) : ι ⊕ₗ κ := toLex (Sum.inr j)

theorem uni_mono {I I' : Finset ι} {J J' : Finset κ} (hI : I ⊆ I') (hJ : J ⊆ J') :
    uni I J ⊆ uni I' J' :=
  Finset.map_subset_map.2 (Finset.disjSum_mono hI hJ)

theorem lft_monotone : Monotone (@lft ι κ) :=
  fun _ _ h => Finset.toLeft_subset_toLeft (Finset.map_subset_map.2 h)

theorem rgt_monotone : Monotone (@rgt ι κ) :=
  fun _ _ h => Finset.toRight_subset_toRight (Finset.map_subset_map.2 h)

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

private theorem sign_uni_left (I : Finset ι) (J : Finset κ) (i : ι) :
    (cechSign (uni I J) (li i) : ℤ) = cechSign I i := by
  unfold cechSign belowCard
  congr 1
  rw [Finset.card_filter, Finset.card_filter, sum_uni]
  simp only [Sum.Lex.inl_lt_inl_iff, Sum.Lex.not_inr_lt_inl, if_false,
    Finset.sum_const_zero, add_zero]

private theorem sign_uni_right (I : Finset ι) (J : Finset κ) (j : κ) :
    cechSign (uni I J) (ri j) = (-1 : ℤ) ^ I.card * cechSign J j := by
  unfold cechSign belowCard
  rw [← pow_add]
  congr 1
  rw [Finset.card_filter, Finset.card_filter, sum_uni]
  simp

variable (D : FinsetCechDatum.{0} (ι ⊕ₗ κ))

/-- Pull back the restriction diagram along a monotone map of intersection indices. -/
def comap {T U : Type} (A : FinsetCechDatum.{0} T) (m : Finset U → Finset T)
    (hm : Monotone m) : FinsetCechDatum.{0} U where
  obj s := A.obj (m s)
  res h := A.res (hm h)
  res_refl s := A.res_refl (m s)
  res_res _ _ := A.res_res _ _

instance {R T U : Type} [CommRing R] (A : FinsetCechDatum.{0} T) [∀ s, Module R (A.obj s)]
    (m : Finset U → Finset T) (hm : Monotone m) (s : Finset U) :
    Module R ((A.comap m hm).obj s) := inferInstanceAs (Module R (A.obj (m s)))

/-- Restrict to the left cover while fixing one intersection on the right. -/
abbrev leftSlice (J : Finset κ) : FinsetCechDatum.{0} ι :=
  D.comap (fun I => uni I J) (fun _ _ h => uni_mono h (Finset.Subset.refl _))

/-- Restrict to the right cover while fixing one intersection on the left. -/
abbrev rightSlice (I : Finset ι) : FinsetCechDatum.{0} κ :=
  D.comap (uni I) (fun _ _ h => uni_mono (Finset.Subset.refl _) h)

theorem d_uni (x : D.Cochain) (I : Finset ι) (J : Finset κ) :
    D.d x (uni I J) = (D.leftSlice J).d (fun A => x (uni A J)) I +
      (-1 : ℤ) ^ I.card • (D.rightSlice I).d (fun B => x (uni I B)) J := by
  simp only [FinsetCechDatum.d, sum_uni, Finset.smul_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl ?_) (Finset.sum_congr rfl ?_)
  · intro i _
    rw [sign_uni_left]
    exact congrArg ((cechSign I i : ℤ) • ·)
      (D.res_cochain_congr x (erase_uni_left I J i) _ _)
  · intro j _
    rw [sign_uni_right, mul_smul]
    exact congrArg (((-1 : ℤ) ^ I.card) • (cechSign J j : ℤ) • ·)
      (D.res_cochain_congr x (erase_uni_right I J j) _ _)

private def joinedIndex : (Σ _ : Finset ι, Finset κ) ≃ Finset (ι ⊕ₗ κ) where
  toFun p := uni p.1 p.2
  invFun s := ⟨lft s, rgt s⟩
  left_inv := fun ⟨I, J⟩ => by simp only [lft_uni, rgt_uni]
  right_inv := uni_lft_rgt

/-- The joined cochains can be assembled from their slices. -/
def cochainSlices (R : Type) [CommRing R] [∀ s, Module R (D.obj s)] :
    D.Cochain ≃ₗ[R] (∀ I, (D.rightSlice I).Cochain) :=
  (LinearEquiv.piCongrLeft R D.obj (joinedIndex (ι := ι) (κ := κ))).symm.trans
    (LinearEquiv.piCurry R fun I J => D.obj (uni I J))

theorem cochainSlices_apply (R : Type) [CommRing R] [∀ s, Module R (D.obj s)]
    (x : D.Cochain) (I : Finset ι) (J : Finset κ) :
    D.cochainSlices R x I J = x (uni I J) := rfl

end HTGeometry.FinsetCechDatum
