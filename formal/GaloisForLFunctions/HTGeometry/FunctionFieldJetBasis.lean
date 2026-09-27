import GaloisForLFunctions.HTGeometry.FunctionFieldJetField
import GaloisForLFunctions.HTGeometry.TwistedDerivationKernel
import GaloisForLFunctions.HTGeometry.JacobianDomainCriterion
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Jets of an arbitrary transcendence basis

In the jet field `K = F(y_(i,k))` of `F/C` (built on a transcendence basis `t`), let `s` be any
other transcendence basis.  Its Jacobian `A_(ij) = ∂s_i/∂t_j` is invertible: a derivation killing
every `s_i` kills `C(s)` and hence the algebraic extension `F`.  By induction,

`δ^(k+1) s_i = Σ_j A_(ij) y_(j,k) + (a polynomial in the jets of order < k)`,

so the coordinate derivations `∂/∂y_(j,m)` give a block-triangular Jacobian of the jets of `s` with
diagonal blocks `A`.  Consequently the jets of `s` of positive order are algebraically independent
over `F`, and they generate `K` over `F`.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F : Type*} [Field F] {d : ℕ} {C : Type*} [Field C] [CharZero C] [Algebra C F]

/-- The coordinate derivation `∂/∂y_p` of the jet field over `F`. -/
def jetCoordPartial (p : Fin d × ℕ) :
    Derivation F (FunctionJetField F d) (FunctionJetField F d) :=
  fractionRingDerivation
    ((Algebra.linearMap (FunctionJetPoly F d) (FunctionJetField F d)).compDer (pderiv p))

theorem jetCoordPartial_functionJet (p q : Fin d × ℕ) :
    jetCoordPartial p (functionJet q : FunctionJetField F d) = if q = p then 1 else 0 := by
  classical
  rw [jetCoordPartial, functionJet, fractionRingDerivation_algebraMap]
  change algebraMap (FunctionJetPoly F d) (FunctionJetField F d) (pderiv p (X q)) = _
  rw [pderiv_X, Pi.single_apply]
  split_ifs <;> simp

/-- The jets of order `< k`, with coefficients in `F`. -/
def jetSubalgebra (k : ℕ) : Subalgebra F (FunctionJetField F d) :=
  Algebra.adjoin F (functionJet '' {q : Fin d × ℕ | q.2 < k})

theorem functionJet_mem_jetSubalgebra {q : Fin d × ℕ} {k : ℕ} (hq : q.2 < k) :
    (functionJet q : FunctionJetField F d) ∈ jetSubalgebra k :=
  Algebra.subset_adjoin ⟨q, hq, rfl⟩

theorem jetSubalgebra_mono {k l : ℕ} (hkl : k ≤ l) :
    (jetSubalgebra k : Subalgebra F (FunctionJetField F d)) ≤ jetSubalgebra l :=
  Algebra.adjoin_mono (Set.image_mono fun _ hq => lt_of_lt_of_le hq hkl)

/-- A coordinate derivation of order `≥ k` kills the jets of order `< k`. -/
theorem jetCoordPartial_eq_zero_of_mem {p : Fin d × ℕ} {k : ℕ} (hk : k ≤ p.2)
    {x : FunctionJetField F d} (hx : x ∈ jetSubalgebra k) : jetCoordPartial p x = 0 := by
  classical
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨q, hq, rfl⟩ := hx
      rw [jetCoordPartial_functionJet, if_neg]
      intro h
      rw [h] at hq
      exact absurd (lt_of_lt_of_le hq hk) (lt_irrefl _)
  | algebraMap a => exact (jetCoordPartial p).map_algebraMap a
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | mul x y _ _ hx hy => rw [Derivation.leibniz, hx, hy, smul_zero, smul_zero, add_zero]

variable {t : Fin d → F} (ht : IsTranscendenceBasis C t)

/-- The jet derivation raises the order bound by one. -/
theorem jetFieldDerivation_mem_jetSubalgebra {k : ℕ} {x : FunctionJetField F d}
    (hx : x ∈ jetSubalgebra k) : jetFieldDerivation ht x ∈ jetSubalgebra (k + 1) := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨q, hq, rfl⟩ := hx
      rw [jetFieldDerivation_functionJet]
      exact functionJet_mem_jetSubalgebra (Nat.succ_lt_succ hq)
  | algebraMap a =>
      rw [jetFieldDerivation_algebraMap]
      refine Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ ?_ (Subalgebra.algebraMap_mem _ _)
      exact functionJet_mem_jetSubalgebra (Nat.succ_pos k)
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y hx' hy' hx hy =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact Subalgebra.add_mem _
        (Subalgebra.mul_mem _ (jetSubalgebra_mono (Nat.le_succ k) hx') hy)
        (Subalgebra.mul_mem _ (jetSubalgebra_mono (Nat.le_succ k) hy') hx)

/-- The Jacobian `A_(ij) = ∂s_i/∂t_j` of a family `s` of `F`. -/
def jetJacobian (s : Fin d → F) : Matrix (Fin d) (Fin d) F :=
  Matrix.of fun i j => jetPartial ht j (s i)

/-- **The leading term of the jets of `s`.** -/
theorem jetFieldDerivation_iterate_sub_mem (s : Fin d → F) (k : ℕ) (i : Fin d) :
    ((jetFieldDerivation ht : FunctionJetField F d → FunctionJetField F d)^[k + 1])
        (algebraMap F (FunctionJetField F d) (s i)) -
      ∑ j, algebraMap F (FunctionJetField F d) (jetJacobian ht s i j) * functionJet (j, k) ∈
        jetSubalgebra k := by
  induction k with
  | zero =>
      rw [Function.iterate_one, jetFieldDerivation_algebraMap]
      have h : ∑ j, (functionJet (j, 0) : FunctionJetField F d) *
            algebraMap F (FunctionJetField F d) (jetPartial ht j (s i)) -
          ∑ j, algebraMap F (FunctionJetField F d) (jetJacobian ht s i j) * functionJet (j, 0) = 0 := by
        rw [sub_eq_zero]
        exact Finset.sum_congr rfl fun j _ => by rw [jetJacobian, Matrix.of_apply, mul_comm]
      rw [h]
      exact Subalgebra.zero_mem _
  | succ k ih =>
      set R := ((jetFieldDerivation ht : FunctionJetField F d → FunctionJetField F d)^[k + 1])
          (algebraMap F (FunctionJetField F d) (s i)) -
        ∑ j, algebraMap F (FunctionJetField F d) (jetJacobian ht s i j) * functionJet (j, k) with hR
      have hiter : ((jetFieldDerivation ht : FunctionJetField F d → FunctionJetField F d)^[k + 1 + 1])
          (algebraMap F (FunctionJetField F d) (s i)) =
          jetFieldDerivation ht (R + ∑ j, algebraMap F (FunctionJetField F d) (jetJacobian ht s i j) *
            functionJet (j, k)) := by
        rw [Function.iterate_succ_apply', hR, sub_add_cancel]
      rw [hiter, map_add, map_sum]
      have hsum : ∀ j, jetFieldDerivation ht (algebraMap F (FunctionJetField F d)
          (jetJacobian ht s i j) * functionJet (j, k)) =
          algebraMap F (FunctionJetField F d) (jetJacobian ht s i j) * functionJet (j, k + 1) +
            functionJet (j, k) * jetFieldDerivation ht
              (algebraMap F (FunctionJetField F d) (jetJacobian ht s i j)) := by
        intro j
        rw [Derivation.leibniz, jetFieldDerivation_functionJet, smul_eq_mul, smul_eq_mul]
      simp only [hsum, Finset.sum_add_distrib]
      have hrest : jetFieldDerivation ht R + ∑ j, (functionJet (j, k) : FunctionJetField F d) *
          jetFieldDerivation ht (algebraMap F (FunctionJetField F d) (jetJacobian ht s i j)) ∈
            jetSubalgebra (k + 1) := by
        refine Subalgebra.add_mem _ (jetFieldDerivation_mem_jetSubalgebra ht ih)
          (Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _
            (functionJet_mem_jetSubalgebra (Nat.lt_succ_self k)) ?_)
        exact jetSubalgebra_mono (Nat.succ_le_succ (Nat.zero_le k))
          (jetFieldDerivation_mem_jetSubalgebra ht (k := 0) (Subalgebra.algebraMap_mem _ _))
      convert hrest using 1
      ring

/-- **The Jacobian of a transcendence basis is invertible.**  A combination of partial derivations
killing every `s_i` kills `C(s)`, hence the algebraic extension `F`, hence every `t_j`. -/
theorem jetJacobian_det_ne_zero {s : Fin d → F} (hs : IsTranscendenceBasis C s) :
    (jetJacobian ht s).det ≠ 0 := by
  classical
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap C F).injective
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let δ : F → F := fun x => ∑ j, c j * jetPartial ht j x
  have hadd : ∀ x y, δ (x + y) = δ x + δ y := by
    intro x y
    simp only [δ, map_add, mul_add, Finset.sum_add_distrib]
  have hmul : ∀ x y, δ (x * y) = (RingHom.id F) x * δ y + (RingHom.id F) y * δ x := by
    intro x y
    simp only [δ, Derivation.leibniz, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hδs : ∀ i, δ (s i) = 0 := by
    intro i
    have h := congrFun hc i
    simp only [Matrix.mulVec, dotProduct, jetJacobian, Matrix.of_apply, Pi.zero_apply] at h
    simp only [δ]
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  let KI : IntermediateField C F :=
    (twistedKernel (RingHom.id F) δ hadd hmul).toIntermediateField fun a => by
      change δ (algebraMap C F a) = 0
      simp only [δ, Derivation.map_algebraMap, mul_zero, Finset.sum_const_zero]
  have hle : IntermediateField.adjoin C (Set.range s) ≤ KI := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact hδs i
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin C (Set.range s)) F := hs.isAlgebraic_field
  have hzero : ∀ x, δ x = 0 := fun x =>
    twisted_eq_zero_of_isIntegral (RingHom.id F) δ hadd hmul
      (S' := IntermediateField.adjoin C (Set.range s)) (fun a => hle a.2)
      (Algebra.IsIntegral.isIntegral x)
  apply hc0
  funext i
  have h := hzero (t i)
  simp only [δ, jetPartial_apply_basis] at h
  simpa using h

/-- The positive jets `δ^(k+1) s_i` of a family `s`. -/
def basisJets (s : Fin d → F) (q : ℕ × Fin d) : FunctionJetField F d :=
  ((jetFieldDerivation ht : FunctionJetField F d → FunctionJetField F d)^[q.1 + 1])
    (algebraMap F (FunctionJetField F d) (s q.2))

theorem basisJets_mem_jetSubalgebra (s : Fin d → F) (q : ℕ × Fin d) :
    basisJets ht s q ∈ jetSubalgebra (q.1 + 1) := by
  have h := jetFieldDerivation_iterate_sub_mem ht s q.1 q.2
  have hsum : ∑ j, algebraMap F (FunctionJetField F d) (jetJacobian ht s q.2 j) *
      (functionJet (j, q.1) : FunctionJetField F d) ∈ jetSubalgebra (q.1 + 1) :=
    Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (functionJet_mem_jetSubalgebra (Nat.lt_succ_self q.1))
  have := Subalgebra.add_mem _ (jetSubalgebra_mono (Nat.le_succ q.1) h) hsum
  rwa [sub_add_cancel] at this

/-- The coordinate derivation of the leading order reads off the Jacobian. -/
theorem jetCoordPartial_basisJets_same (s : Fin d → F) (k : ℕ) (i j : Fin d) :
    jetCoordPartial (j, k) (basisJets ht s (k, i)) =
      algebraMap F (FunctionJetField F d) (jetJacobian ht s i j) := by
  classical
  have h := jetFieldDerivation_iterate_sub_mem ht s k i
  have hR := jetCoordPartial_eq_zero_of_mem (p := (j, k)) (le_refl k) h
  rw [map_sub, sub_eq_zero] at hR
  change jetCoordPartial (j, k) (((jetFieldDerivation ht : FunctionJetField F d →
    FunctionJetField F d)^[k + 1]) (algebraMap F (FunctionJetField F d) (s i))) = _
  rw [hR, map_sum]
  simp only [Derivation.leibniz, jetCoordPartial_functionJet, Derivation.map_algebraMap,
    smul_eq_mul, mul_zero, add_zero, Prod.mk.injEq, and_true, mul_ite, mul_one]
  rw [Finset.sum_ite_eq']
  simp

/-- **Finite truncations of the jets of a transcendence basis are independent over `F`.** -/
theorem algebraicIndependent_basisJets_trunc {s : Fin d → F} (hs : IsTranscendenceBasis C s)
    (N : ℕ) : AlgebraicIndependent F (fun q : Fin N × Fin d => basisJets ht s ((q.1 : ℕ), q.2)) := by
  classical
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap C F).injective
  let M : Matrix (Fin N × Fin d) (Fin N × Fin d) (FunctionJetField F d) :=
    Matrix.of fun q' q => jetCoordPartial (q'.2, (q'.1 : ℕ)) (basisJets ht s ((q.1 : ℕ), q.2))
  have hblock : M.BlockTriangular (fun q => q.1) := by
    intro q' q hlt
    exact jetCoordPartial_eq_zero_of_mem (Nat.succ_le_of_lt hlt)
      (basisJets_mem_jetSubalgebra ht s _)
  have hdiag : ∀ k : Fin N, (M.toSquareBlock (fun q => q.1) k).det =
      algebraMap F (FunctionJetField F d) (jetJacobian ht s).det := by
    intro k
    let e : Fin d ≃ {q : Fin N × Fin d // q.1 = k} :=
      { toFun := fun i => ⟨(k, i), rfl⟩
        invFun := fun q => q.1.2
        left_inv := fun i => rfl
        right_inv := fun q => by
          obtain ⟨⟨a, b⟩, h⟩ := q
          simp only at h
          subst h
          rfl }
    rw [← Matrix.det_submatrix_equiv_self e, RingHom.map_det, ← Matrix.det_transpose]
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.toSquareBlock_def, Matrix.of_apply, M, e,
      Equiv.coe_fn_mk, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact jetCoordPartial_basisJets_same ht s k i j
  have hdet : M.det ≠ 0 := by
    rw [hblock.det_fintype]
    rw [Finset.prod_ne_zero_iff]
    intro k _
    rw [hdiag k, ne_eq, map_eq_zero_iff _ (algebraMap F (FunctionJetField F d)).injective]
    exact jetJacobian_det_ne_zero ht hs
  exact algebraicIndependent_of_domain_jacobian (K := F)
    (fun q : Fin N × Fin d => basisJets ht s ((q.1 : ℕ), q.2))
    (fun q' => ⇑(jetCoordPartial (q'.2, (q'.1 : ℕ))))
    (fun q' a b => map_add _ a b)
    (fun q' a b => by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul])
    (fun q' c => (jetCoordPartial _).map_algebraMap c) M hdet (fun q' q => rfl)

/-- **The positive jets of a transcendence basis are algebraically independent over `F`.** -/
theorem algebraicIndependent_basisJets {s : Fin d → F} (hs : IsTranscendenceBasis C s) :
    AlgebraicIndependent F (basisJets ht s) := by
  classical
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro P hP
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ q ∈ P.vars, q.1 < N :=
    ⟨P.vars.sup (fun q => q.1) + 1, fun q hq =>
      Nat.lt_succ_of_le (Finset.le_sup (f := fun q : ℕ × Fin d => q.1) hq)⟩
  let emb : Fin N × Fin d → ℕ × Fin d := fun q => ((q.1 : ℕ), q.2)
  have hemb : Function.Injective emb := by
    intro a b h
    simp only [emb, Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext h.1) h.2
  have hvars : (P.vars : Set (ℕ × Fin d)) ⊆ Set.range emb := by
    intro q hq
    exact ⟨(⟨q.1, hN q hq⟩, q.2), rfl⟩
  obtain ⟨Q, rfl⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range P emb hemb hvars
  rw [MvPolynomial.aeval_rename] at hP
  have hQ : Q = 0 :=
    (algebraicIndependent_iff_injective_aeval.mp (algebraicIndependent_basisJets_trunc ht hs N))
      (by rw [map_zero]; exact hP)
  rw [hQ, map_zero]

/-- The jet field is generated over `F` by the jets `y_(i,k)`. -/
theorem adjoin_functionJet_eq_top :
    IntermediateField.adjoin F (Set.range (functionJet : Fin d × ℕ → FunctionJetField F d)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (FunctionJetPoly F d) x
  have hmem : ∀ P : FunctionJetPoly F d, algebraMap (FunctionJetPoly F d) (FunctionJetField F d) P ∈
      IntermediateField.adjoin F (Set.range (functionJet : Fin d × ℕ → FunctionJetField F d)) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C c =>
        rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
        exact IntermediateField.algebraMap_mem _ c
    | add P Q hP hQ => rw [map_add]; exact IntermediateField.add_mem _ hP hQ
    | mul_X P q hP =>
        rw [map_mul]
        exact IntermediateField.mul_mem _ hP (IntermediateField.subset_adjoin F _ ⟨q, rfl⟩)
  exact IntermediateField.div_mem _ (hmem a) (hmem b)

/-- **The jets of a transcendence basis generate the jet field over `F`.** -/
theorem adjoin_basisJets_eq_top {s : Fin d → F} (hs : IsTranscendenceBasis C s) :
    IntermediateField.adjoin F (Set.range (basisJets ht s)) = ⊤ := by
  classical
  set L := IntermediateField.adjoin F (Set.range (basisJets ht s)) with hL
  -- every jet of order `k` lies in `L`, by induction on `k`
  have hjet : ∀ k : ℕ, ∀ j : Fin d, (functionJet (j, k) : FunctionJetField F d) ∈ L := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      have hsub : (jetSubalgebra k : Subalgebra F (FunctionJetField F d)) ≤ L.toSubalgebra := by
        rw [jetSubalgebra, Algebra.adjoin_le_iff]
        rintro _ ⟨q, hq, rfl⟩
        exact ih q.2 hq q.1
      have hlin : ∀ i, ∑ l, algebraMap F (FunctionJetField F d) (jetJacobian ht s i l) *
          (functionJet (l, k) : FunctionJetField F d) ∈ L := by
        intro i
        have h := hsub (jetFieldDerivation_iterate_sub_mem ht s k i)
        have hb : basisJets ht s (k, i) ∈ L := IntermediateField.subset_adjoin F _ ⟨(k, i), rfl⟩
        have := L.sub_mem hb h
        rwa [basisJets, sub_sub_cancel] at this
      intro j
      let A := jetJacobian ht s
      have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A
        (isUnit_iff_ne_zero.mpr (jetJacobian_det_ne_zero ht hs))
      have hA : (functionJet (j, k) : FunctionJetField F d) = ∑ i,
          algebraMap F (FunctionJetField F d) (A⁻¹ j i) *
            ∑ l, algebraMap F (FunctionJetField F d) (A i l) * functionJet (l, k) := by
        simp only [Finset.mul_sum, ← mul_assoc, ← map_mul]
        rw [Finset.sum_comm]
        simp only [← Finset.sum_mul, ← map_sum]
        have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A
          (isUnit_iff_ne_zero.mpr (jetJacobian_det_ne_zero ht hs))
        have hcoef : ∀ l, ∑ i, A⁻¹ j i * A i l = if j = l then 1 else 0 := by
          intro l
          have := congrFun (congrFun hinv j) l
          rw [Matrix.mul_apply] at this
          rw [this, Matrix.one_apply]
        simp only [hcoef]
        simp
      rw [hA]
      exact L.sum_mem fun i _ => L.mul_mem (L.algebraMap_mem _) (hlin i)
  rw [eq_top_iff, ← adjoin_functionJet_eq_top, IntermediateField.adjoin_le_iff]
  rintro _ ⟨⟨j, k⟩, rfl⟩
  exact hjet k j

end

end GaloisForLFunctions.HTGeometry
