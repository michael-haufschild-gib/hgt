import GaloisForLFunctions.RHTower.XiDeterminantLogarithmicSingularValueLaw
import GaloisForLFunctions.HTGeometry.SignedGreedyEigenspaceMultiplicity
import GaloisForLFunctions.RHTower.XiOrderedPrimeApproximationNumbers
import GaloisForLFunctions.RHTower.XiOrderedZeroCopyEnumeration
import GaloisForLFunctions.RHTower.XiWeilPolarization
import GaloisForLFunctions.RHTower.ArithmeticDilationStageDeterminant

/-!
# Exact Xi determinant spectral transfer

A zero-free-gauge Hilbert--Carleman determinant identity for a self-adjoint
Hilbert--Schmidt kernel determines its complete signed spectrum with multiplicity.
Signed-greedy spectral exhaustion, divisor-copy fibres, and monotone reindexing then
force exact pointwise equality with the canonical reciprocal-Xi approximation numbers.
No eigenbasis or spectral-realization hypothesis is assumed.
-/

open Complex Set
open HilbertSchmidt

namespace RHTower

noncomputable section

theorem xiDeterminant_antitone_eq_of_equiv
    (a b : ℕ → ℝ) (ha : Antitone a) (hb : Antitone b)
    (e : ℕ ≃ ℕ) (he : ∀ n, a n = b (e n)) :
    a = b := by
  have hle (u v : ℕ → ℝ) (hu : Antitone u) (hv : Antitone v)
      (p : ℕ ≃ ℕ) (hp : ∀ n, u n = v (p n)) : ∀ n, u n ≤ v n := by
    intro n
    by_contra hnot
    have hgt : v n < u n := lt_of_not_ge hnot
    let f : Fin (n + 1) → Fin n := fun k =>
      ⟨p k.1, by
        by_contra hpn
        have hk : k.1 ≤ n := Nat.lt_succ_iff.mp k.2
        have hchain : v n < v (p k.1) := by
          calc
            v n < u n := hgt
            _ ≤ u k.1 := hu hk
            _ = v (p k.1) := hp k.1
        exact (not_lt_of_ge (hv (Nat.le_of_not_gt hpn))) hchain⟩
    have hfinj : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      apply p.injective
      exact congrArg Fin.val hij
    have hcard := Fintype.card_le_of_injective f hfinj
    have : n + 1 ≤ n := by
      simpa only [Fintype.card_fin] using hcard
    omega
  apply funext
  intro n
  apply le_antisymm
  · exact hle a b ha hb e he n
  · apply hle b a hb ha e.symm
    intro k
    have hk := he (e.symm k)
    simpa using hk.symm

theorem xiDeterminant_XiC_inv_sgVal_eq_zero
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (H : ℂ → ℂ)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z)
    {n : ℕ} (hn : ContinuousLinearMap.sgVal (toOperator hK) n ≠ 0) :
    XiC ((ContinuousLinearMap.sgVal (toOperator hK) n : ℂ)⁻¹) = 0 := by
  let S := toOperator hK
  let c := ContinuousLinearMap.sgVal S n
  have hc : c ≠ 0 := hn
  have hvec : ContinuousLinearMap.sgVec S n ≠ 0 := by
    intro hzero
    exact hc (ContinuousLinearMap.sgVal_zero_of_dead hzero)
  have hz0 : (c : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hc)
  have hdet : GaloisForLFunctions.HTGeometry.entireDet2 K (c : ℂ)⁻¹ = 0 := by
    apply (GaloisForLFunctions.HTGeometry.entireDet2_eq_zero_iff_exists_eigenvector
      hK hz0).mpr
    refine ⟨ContinuousLinearMap.sgVec S n, hvec, ?_⟩
    change S (ContinuousLinearMap.sgVec S n) =
      ((c : ℂ)⁻¹)⁻¹ • ContinuousLinearMap.sgVec S n
    rw [ContinuousLinearMap.apply_sgVec, inv_inv]
  rw [hXi, hdet, mul_zero]

theorem xiDeterminant_ncard_sgVal_fiber_eq_xiSpectralMultiplicity
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z)
    {c : ℝ} (hc : c ≠ 0) :
    Set.ncard {n : ℕ | ContinuousLinearMap.sgVal (toOperator hK) n = c} =
      xiSpectralMultiplicity (c : ℂ)⁻¹ := by
  let S := toOperator hK
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hcpt : IsCompactOperator S :=
    (isHilbertSchmidt_toOperator hK).isCompactOperator
  have hsym : S.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself
  by_cases hz : XiC (c : ℂ)⁻¹ = 0
  · have hfin := ContinuousLinearMap.finrank_eigenspace_eq_ncard_sgVal_fiber
      hcpt hsym hc
    have hord := analyticOrderAt_XiC_eq_finrank_eigenspace_of_exactSelfAdjointDeterminant
      hK hself H hHanalytic hH hXi hz
    have hcinv : ((c : ℂ)⁻¹)⁻¹ = (c : ℂ) := inv_inv _
    rw [hcinv] at hord
    have hord' : analyticOrderAt XiC (c : ℂ)⁻¹ =
        (Module.finrank ℂ (Module.End.eigenspace
          (S : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) (c : ℂ)) : ℕ∞) := by
      exact hord
    calc
      Set.ncard {n : ℕ | ContinuousLinearMap.sgVal (toOperator hK) n = c} =
          Module.finrank ℂ (Module.End.eigenspace
            (S : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) (c : ℂ)) :=
        hfin.symm
      _ = (analyticOrderAt XiC (c : ℂ)⁻¹).toNat := by
        rw [hord']
        simp
      _ = xiSpectralMultiplicity (c : ℂ)⁻¹ :=
        (xiSpectralMultiplicity_eq_analyticOrderAt_toNat hz).symm
  · have hsgempty :
        {n : ℕ | ContinuousLinearMap.sgVal (toOperator hK) n = c} = ∅ := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hn
      apply hz
      have hzero := xiDeterminant_XiC_inv_sgVal_eq_zero hK H hXi (n := n) (by
        rw [hn]
        exact hc)
      simpa only [hn] using hzero
    have hxiempty :
        {q : XiZeroCopy | xiSpectralPoint q = (c : ℂ)⁻¹} = ∅ := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hq
      apply hz
      rw [← hq]
      exact XiC_xiSpectralPoint_eq_zero q
    rw [hsgempty, Set.ncard_empty]
    unfold xiSpectralMultiplicity
    rw [show (finite_xiSpectralPoint_fiber (c : ℂ)⁻¹).toFinset = ∅ by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨q, hq⟩
      have : q ∈ {q : XiZeroCopy | xiSpectralPoint q = (c : ℂ)⁻¹} := by
        simpa only [Set.Finite.mem_toFinset] using hq
      rw [hxiempty] at this
      exact this]
    rfl

def xiDeterminant_xiReciprocalEigenvalue (hRH : RiemannHypothesis)
    (q : XiZeroCopy) : ℝ :=
  ((xiSpectralPoint q)⁻¹).re

theorem xiDeterminant_coe_xiReciprocalEigenvalue
    (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    (xiDeterminant_xiReciprocalEigenvalue hRH q : ℂ) = (xiSpectralPoint q)⁻¹ := by
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
  rw [xiDeterminant_xiReciprocalEigenvalue, ht]
  simp

theorem xiDeterminant_xiReciprocalEigenvalue_ne_zero
    (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    xiDeterminant_xiReciprocalEigenvalue hRH q ≠ 0 := by
  intro hzero
  have hcast := xiDeterminant_coe_xiReciprocalEigenvalue hRH q
  rw [hzero, Complex.ofReal_zero] at hcast
  exact (inv_ne_zero (xiSpectralPoint_ne_zero q)) hcast.symm

def xiDeterminant_sgValLiveIndex
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : H →L[ℂ] H) :=
  {n : ℕ // ContinuousLinearMap.sgVal S n ≠ 0}

def xiDeterminant_sgValOnLive
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : H →L[ℂ] H) (n : xiDeterminant_sgValLiveIndex S) : ℝ :=
  ContinuousLinearMap.sgVal S n.1

def xiDeterminant_sgLiveFiberEquiv
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : H →L[ℂ] H) {c : ℝ} (hc : c ≠ 0) :
    {n : xiDeterminant_sgValLiveIndex S // xiDeterminant_sgValOnLive S n = c} ≃
      {n : ℕ // ContinuousLinearMap.sgVal S n = c} where
  toFun n := ⟨n.1.1, n.2⟩
  invFun n := ⟨⟨n.1, by rw [n.2]; exact hc⟩, n.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def xiDeterminant_xiRealFiberEquiv (hRH : RiemannHypothesis)
    {c : ℝ} (hc : c ≠ 0) :
    {q : XiZeroCopy // xiDeterminant_xiReciprocalEigenvalue hRH q = c} ≃
      {q : XiZeroCopy // xiSpectralPoint q = (c : ℂ)⁻¹} where
  toFun q := ⟨q.1, by
    have hcast := xiDeterminant_coe_xiReciprocalEigenvalue hRH q.1
    rw [q.2] at hcast
    have := congrArg Inv.inv hcast
    simpa using this.symm⟩
  invFun q := ⟨q.1, by
    apply Complex.ofReal_injective
    rw [xiDeterminant_coe_xiReciprocalEigenvalue hRH q.1, q.2]
    simp [hc]⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def xiDeterminant_exactXiFiberEquiv
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z)
    (c : ℝ) :
    {n : xiDeterminant_sgValLiveIndex (toOperator hK) //
      xiDeterminant_sgValOnLive (toOperator hK) n = c} ≃
      {q : XiZeroCopy //
        xiDeterminant_xiReciprocalEigenvalue
          (riemannHypothesis_of_XiC_eq_zeroFree_mul_entireDet2 hK hself H hH hXi) q = c} := by
  let hRH := riemannHypothesis_of_XiC_eq_zeroFree_mul_entireDet2 hK hself H hH hXi
  by_cases hc : c = 0
  · subst c
    letI : IsEmpty {n : xiDeterminant_sgValLiveIndex (toOperator hK) //
        xiDeterminant_sgValOnLive (toOperator hK) n = 0} :=
      ⟨fun n => n.1.2 n.2⟩
    letI : IsEmpty {q : XiZeroCopy //
        xiDeterminant_xiReciprocalEigenvalue hRH q = 0} :=
      ⟨fun q => xiDeterminant_xiReciprocalEigenvalue_ne_zero hRH q.1 q.2⟩
    exact Equiv.equivOfIsEmpty _ _
  · have hsgfin :
        {n : ℕ | ContinuousLinearMap.sgVal (toOperator hK) n = c}.Finite :=
      ContinuousLinearMap.finite_sgVal_fiber
        (isHilbertSchmidt_toOperator hK).isCompactOperator
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself) hc
    have hxifin := finite_xiSpectralPoint_fiber (c : ℂ)⁻¹
    letI : Fintype {n : ℕ // ContinuousLinearMap.sgVal (toOperator hK) n = c} :=
      Fintype.ofFinset hsgfin.toFinset (fun n => by
        rw [Set.Finite.mem_toFinset]
        change ((toOperator hK).sgVal n = c) ↔ ((toOperator hK).sgVal n = c)
        rfl)
    letI : Fintype {q : XiZeroCopy // xiSpectralPoint q = (c : ℂ)⁻¹} :=
      Fintype.ofFinset hxifin.toFinset (fun q => by
        rw [Set.Finite.mem_toFinset]
        change (xiSpectralPoint q = (c : ℂ)⁻¹) ↔
          (xiSpectralPoint q = (c : ℂ)⁻¹)
        rfl)
    letI : Fintype {n : xiDeterminant_sgValLiveIndex (toOperator hK) //
        xiDeterminant_sgValOnLive (toOperator hK) n = c} :=
      Fintype.ofEquiv _ (xiDeterminant_sgLiveFiberEquiv (toOperator hK) hc).symm
    letI : Fintype {q : XiZeroCopy //
        xiDeterminant_xiReciprocalEigenvalue hRH q = c} :=
      Fintype.ofEquiv _ (xiDeterminant_xiRealFiberEquiv hRH hc).symm
    apply Fintype.equivOfCardEq
    calc
      Fintype.card {n : xiDeterminant_sgValLiveIndex (toOperator hK) //
          xiDeterminant_sgValOnLive (toOperator hK) n = c} =
          Fintype.card {n : ℕ // ContinuousLinearMap.sgVal (toOperator hK) n = c} :=
        Fintype.card_congr (xiDeterminant_sgLiveFiberEquiv (toOperator hK) hc)
      _ = Set.ncard {n : ℕ | ContinuousLinearMap.sgVal (toOperator hK) n = c} := by
        rw [Set.ncard_eq_toFinset_card _ hsgfin]
        exact Fintype.card_ofFinset hsgfin.toFinset (fun n => by
          rw [Set.Finite.mem_toFinset]
          change ((toOperator hK).sgVal n = c) ↔ ((toOperator hK).sgVal n = c)
          rfl)
      _ = xiSpectralMultiplicity (c : ℂ)⁻¹ :=
        xiDeterminant_ncard_sgVal_fiber_eq_xiSpectralMultiplicity
          hK hself H hHanalytic hH hXi hc
      _ = Fintype.card {q : XiZeroCopy // xiSpectralPoint q = (c : ℂ)⁻¹} := by
        unfold xiSpectralMultiplicity
        exact (Fintype.card_ofFinset hxifin.toFinset (fun q => by
          rw [Set.Finite.mem_toFinset]
          change (xiSpectralPoint q = (c : ℂ)⁻¹) ↔
            (xiSpectralPoint q = (c : ℂ)⁻¹)
          rfl)).symm
      _ = Fintype.card {q : XiZeroCopy //
          xiDeterminant_xiReciprocalEigenvalue hRH q = c} :=
        (Fintype.card_congr (xiDeterminant_xiRealFiberEquiv hRH hc)).symm

noncomputable def xiDeterminant_exactXiLiveEquiv
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z) :
    xiDeterminant_sgValLiveIndex (toOperator hK) ≃ XiZeroCopy :=
  (Equiv.sigmaFiberEquiv (xiDeterminant_sgValOnLive (toOperator hK))).symm |>.trans
    ((Equiv.sigmaCongrRight fun c =>
      xiDeterminant_exactXiFiberEquiv hK hself H hHanalytic hH hXi c).trans
      (Equiv.sigmaFiberEquiv (xiDeterminant_xiReciprocalEigenvalue
        (riemannHypothesis_of_XiC_eq_zeroFree_mul_entireDet2 hK hself H hH hXi))))

theorem xiDeterminant_exactXiLiveEquiv_value
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z)
    (n : xiDeterminant_sgValLiveIndex (toOperator hK)) :
    xiDeterminant_xiReciprocalEigenvalue
        (riemannHypothesis_of_XiC_eq_zeroFree_mul_entireDet2 hK hself H hH hXi)
        (xiDeterminant_exactXiLiveEquiv hK hself H hHanalytic hH hXi n) =
      xiDeterminant_sgValOnLive (toOperator hK) n := by
  let p := (Equiv.sigmaFiberEquiv
    (xiDeterminant_sgValOnLive (toOperator hK))).symm n
  let q := xiDeterminant_exactXiFiberEquiv hK hself H hHanalytic hH hXi p.1 p.2
  have hq := q.2
  simpa [xiDeterminant_exactXiLiveEquiv, p, q] using hq

theorem xiDeterminant_sgVal_ne_zero_of_exactXiDeterminant
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z)
    (n : ℕ) :
    ContinuousLinearMap.sgVal (toOperator hK) n ≠ 0 := by
  let S := toOperator hK
  let E := xiDeterminant_exactXiLiveEquiv hK hself H hHanalytic hH hXi
  have hcpt : IsCompactOperator S :=
    (isHilbertSchmidt_toOperator hK).isCompactOperator
  have hsym : S.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself
  intro hnzero
  let f : Fin (n + 1) → Fin n := fun k =>
    let x := E.symm (xiZeroCopyThermalEquiv k.1)
    ⟨x.1, by
      by_contra hnot
      have hnle : n ≤ x.1 := Nat.le_of_not_gt hnot
      have hmono : |ContinuousLinearMap.sgVal S x.1| ≤
          |ContinuousLinearMap.sgVal S n| := by
        rw [ContinuousLinearMap.abs_sgVal hcpt hsym,
          ContinuousLinearMap.abs_sgVal hcpt hsym]
        exact ContinuousLinearMap.orthSup_antitone S
          (ContinuousLinearMap.sgVec S) hnle
      rw [hnzero, abs_zero] at hmono
      have hxzero : ContinuousLinearMap.sgVal S x.1 = 0 := by
        exact abs_eq_zero.mp (le_antisymm hmono (abs_nonneg _))
      exact x.2 hxzero⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have hlive : E.symm (xiZeroCopyThermalEquiv a.1) =
        E.symm (xiZeroCopyThermalEquiv b.1) := by
      apply Subtype.ext
      exact congrArg Fin.val hab
    have hq := E.symm.injective hlive
    exact xiZeroCopyThermalEquiv.injective hq
  have hcard := Fintype.card_le_of_injective f hfinj
  simpa using hcard

noncomputable def xiDeterminant_exactXiSignedGreedyEquiv
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z) :
    ℕ ≃ XiZeroCopy :=
  (Equiv.ofBijective
    (fun n : ℕ => (⟨n, xiDeterminant_sgVal_ne_zero_of_exactXiDeterminant
      hK hself H hHanalytic hH hXi n⟩ : xiDeterminant_sgValLiveIndex (toOperator hK)))
    ⟨fun _ _ h => congrArg Subtype.val h,
      fun n => ⟨n.1, Subtype.ext rfl⟩⟩).trans
    (xiDeterminant_exactXiLiveEquiv hK hself H hHanalytic hH hXi)

theorem xiDeterminant_exactXiSignedGreedyEquiv_value
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z)
    (n : ℕ) :
    xiDeterminant_xiReciprocalEigenvalue
        (riemannHypothesis_of_XiC_eq_zeroFree_mul_entireDet2 hK hself H hH hXi)
        (xiDeterminant_exactXiSignedGreedyEquiv hK hself H hHanalytic hH hXi n) =
      ContinuousLinearMap.sgVal (toOperator hK) n := by
  exact xiDeterminant_exactXiLiveEquiv_value hK hself H hHanalytic hH hXi
    ⟨n, xiDeterminant_sgVal_ne_zero_of_exactXiDeterminant
      hK hself H hHanalytic hH hXi n⟩

def xiDeterminant_xiCanonicalNatZeroCopyEquiv : ℕ ≃ XiZeroCopy :=
  routeKSignedPrimeEquiv.trans xiOrderedSignedPrimeZeroCopyEquiv

noncomputable def xiDeterminant_exactXiSignedGreedyPermutation
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z) :
    ℕ ≃ ℕ :=
  (xiDeterminant_exactXiSignedGreedyEquiv hK hself H hHanalytic hH hXi).trans
    xiDeterminant_xiCanonicalNatZeroCopyEquiv.symm

theorem xiDeterminant_abs_sgVal_eq_xiOrderedSignedApproxNumber_perm
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z)
    (n : ℕ) :
    |ContinuousLinearMap.sgVal (toOperator hK) n| =
      xiOrderedSignedApproxNumber
        (xiDeterminant_exactXiSignedGreedyPermutation hK hself H hHanalytic hH hXi n) := by
  let hRH := riemannHypothesis_of_XiC_eq_zeroFree_mul_entireDet2 hK hself H hH hXi
  let E := xiDeterminant_exactXiSignedGreedyEquiv hK hself H hHanalytic hH hXi
  let C := xiDeterminant_xiCanonicalNatZeroCopyEquiv
  let e := xiDeterminant_exactXiSignedGreedyPermutation hK hself H hHanalytic hH hXi
  let m := e n
  let i := routeKSignedPrimeEquiv m
  have hq : E n = C m := by
    change E n = C (C.symm (E n))
    exact (C.apply_symm_apply (E n)).symm
  have hval := xiDeterminant_exactXiSignedGreedyEquiv_value
    hK hself H hHanalytic hH hXi n
  have hcomplex :
      (ContinuousLinearMap.sgVal (toOperator hK) n : ℂ) =
        xiOrderedSignedPrimeMultiplier i := by
    calc
      (ContinuousLinearMap.sgVal (toOperator hK) n : ℂ) =
          (xiDeterminant_xiReciprocalEigenvalue hRH (E n) : ℂ) := by
        exact_mod_cast hval.symm
      _ = (xiSpectralPoint (E n))⁻¹ :=
        xiDeterminant_coe_xiReciprocalEigenvalue hRH (E n)
      _ = (xiSpectralPoint (C m))⁻¹ := by rw [hq]
      _ = ((xiOrderedSignedPrimeMultiplier i)⁻¹)⁻¹ := by
        rw [show C m = xiOrderedSignedPrimeZeroCopyEquiv i by rfl]
        rw [xiSpectralPoint_orderedSignedPrimeZeroCopyEquiv_eq_of_rh hRH]
      _ = xiOrderedSignedPrimeMultiplier i := inv_inv _
  have hnorm := congrArg norm hcomplex
  rw [Complex.norm_real, Real.norm_eq_abs,
    norm_xiOrderedSignedPrimeMultiplier] at hnorm
  simpa [i, m] using hnorm

theorem xiDeterminant_abs_sgVal_eq_xiOrderedSignedApproxNumber
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z)
    (n : ℕ) :
    |ContinuousLinearMap.sgVal (toOperator hK) n| =
      xiOrderedSignedApproxNumber n := by
  let S := toOperator hK
  let e := xiDeterminant_exactXiSignedGreedyPermutation hK hself H hHanalytic hH hXi
  have hcpt : IsCompactOperator S :=
    (isHilbertSchmidt_toOperator hK).isCompactOperator
  have hsym : S.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself
  have ha : Antitone (fun n => |ContinuousLinearMap.sgVal S n|) := by
    intro i j hij
    change |ContinuousLinearMap.sgVal S j| ≤ |ContinuousLinearMap.sgVal S i|
    rw [ContinuousLinearMap.abs_sgVal hcpt hsym,
      ContinuousLinearMap.abs_sgVal hcpt hsym]
    exact ContinuousLinearMap.orthSup_antitone S
      (ContinuousLinearMap.sgVec S) hij
  have heq := xiDeterminant_antitone_eq_of_equiv
    (fun n => |ContinuousLinearMap.sgVal S n|)
    xiOrderedSignedApproxNumber ha xiOrderedSignedApproxNumber_antitone e
    (xiDeterminant_abs_sgVal_eq_xiOrderedSignedApproxNumber_perm
      hK hself H hHanalytic hH hXi)
  exact congrFun heq n

theorem xiDeterminant_approxNumber_exactXiDeterminant
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z)
    (n : ℕ) :
    approxNumber (toOperator hK) n = xiOrderedSignedApproxNumber n := by
  have hcpt : IsCompactOperator (toOperator hK) :=
    (isHilbertSchmidt_toOperator hK).isCompactOperator
  have hsym : (toOperator hK).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself
  rw [approxNumber_eq_singVal hcpt,
    ← abs_sgVal_eq_singVal hcpt hsym]
  exact xiDeterminant_abs_sgVal_eq_xiOrderedSignedApproxNumber
    hK hself H hHanalytic hH hXi n

end

end RHTower

