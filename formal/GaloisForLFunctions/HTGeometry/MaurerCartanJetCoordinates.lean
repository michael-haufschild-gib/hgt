import GaloisForLFunctions.HTGeometry.FunctionFieldJetExtension

/-!
# Maurer–Cartan coordinates of the jet field

Let `D_1,…,D_d` be `C`-derivations of `F` forming a basis, i.e. with `det(D_i t_j) ≠ 0` for the
transcendence basis `t`.  The restriction of the jet derivation to `F` is a `K`-combination of them,

`δa = Σ_i ℓ_i D_i a`,  `ℓ_i = Σ_j (Dt)⁻¹_(ji) y_(j,0)`,

(the Maurer–Cartan coordinates of the generic point when the `D_i` are the invariant vector fields
of an algebraic group).  The jets `δ^k ℓ_i` are triangular with diagonal block `((Dt)⁻¹)ᵀ`, so they
are algebraically independent over `F` and generate the jet field.

Every `C`-algebra map `φ` of `F` satisfies `D_i ∘ φ = Σ_j a_ij φ ∘ D_j` for a unique matrix `a`,
invertible, and its differential extension acts on the coordinates by `φ̃ ℓ_j = Σ_i a_ij ℓ_i`.
In particular a map commuting with every `D_i` fixes every `ℓ_i`.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F : Type*} [Field F] {d : ℕ} {C : Type*} [Field C] [CharZero C] [Algebra C F]

/-- **A derivation along a field map killing a transcendence basis vanishes.**  Its kernel is a
subfield containing `C(t)`, and in characteristic zero it contains the algebraic extension `F`. -/
theorem twisted_eq_zero_of_isTranscendenceBasis {L : Type*} [Field L] (ι : F →+* L) (D : F → L)
    (hadd : ∀ x y, D (x + y) = D x + D y) (hmul : ∀ x y, D (x * y) = ι x * D y + ι y * D x)
    (hC : ∀ c : C, D (algebraMap C F c) = 0) {t : Fin d → F} (ht : IsTranscendenceBasis C t)
    (hD : ∀ j, D (t j) = 0) (a : F) : D a = 0 := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap C F).injective
  let KI : IntermediateField C F := (twistedKernel ι D hadd hmul).toIntermediateField hC
  have hle : IntermediateField.adjoin C (Set.range t) ≤ KI := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact hD i
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin C (Set.range t)) F := ht.isAlgebraic_field
  exact twisted_eq_zero_of_isIntegral ι D hadd hmul
    (S' := IntermediateField.adjoin C (Set.range t)) (fun b => hle b.2)
    (Algebra.IsIntegral.isIntegral a)

variable (D : Fin d → Derivation C F F)

/-- The matrix `(D_i s_j)` of a family `s` against the derivations `D`. -/
def derivationMatrix (s : Fin d → F) : Matrix (Fin d) (Fin d) F :=
  Matrix.of fun i j => D i (s j)

variable {D} {t : Fin d → F}

/-- **A derivation basis stays invertible on every transcendence basis.**  A combination
`Σ c_i D_i` killing a transcendence basis `s` kills `F`, hence every `t_j`. -/
theorem derivationMatrix_det_ne_zero (hD : (derivationMatrix D t).det ≠ 0) {s : Fin d → F}
    (hs : IsTranscendenceBasis C s) : (derivationMatrix D s).det ≠ 0 := by
  classical
  intro hdet
  have hdetT : (derivationMatrix D s).transpose.det = 0 := by rw [Matrix.det_transpose]; exact hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
  let Dc : F → F := fun x => ∑ i, c i * D i x
  have hadd : ∀ x y, Dc (x + y) = Dc x + Dc y := by
    intro x y
    simp only [Dc, map_add, mul_add, Finset.sum_add_distrib]
  have hmul : ∀ x y, Dc (x * y) = (RingHom.id F) x * Dc y + (RingHom.id F) y * Dc x := by
    intro x y
    simp only [Dc, Derivation.leibniz, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hDs : ∀ k, Dc (s k) = 0 := by
    intro k
    have h := congrFun hc k
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, derivationMatrix, Matrix.of_apply,
      Pi.zero_apply] at h
    simp only [Dc]
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hzero := twisted_eq_zero_of_isTranscendenceBasis (RingHom.id F) Dc hadd hmul
    (fun c' => by simp [Dc]) hs hDs
  apply hc0
  funext i
  refine vec_zero_of_det_ne_zero (derivationMatrix D t).transpose
    (by rwa [Matrix.det_transpose]) c (fun j => ?_) i
  have h := hzero (t j)
  simp only [Dc] at h
  rw [← h]
  exact Finset.sum_congr rfl fun l _ => by
    rw [Matrix.transpose_apply, derivationMatrix, Matrix.of_apply, mul_comm]

omit [CharZero C] in
/-- **The coefficients of a combination of a derivation basis are determined by its values on the
transcendence basis.** -/
theorem eq_zero_of_sum_mul_derivationMatrix (hD : (derivationMatrix D t).det ≠ 0) {L : Type*}
    [Field L] (ι : F →+* L) (c : Fin d → L) (h : ∀ j, ∑ i, c i * ι (D i (t j)) = 0) : c = 0 := by
  have hdet : ((derivationMatrix D t).map ι).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero ι).mpr hD
  funext i
  refine vec_zero_of_det_ne_zero _ hdet c (fun j => ?_) i
  rw [← h j]
  exact Finset.sum_congr rfl fun l _ => by
    rw [Matrix.transpose_apply, Matrix.map_apply, derivationMatrix, Matrix.of_apply, mul_comm]

/-! ### The Maurer–Cartan coordinates -/

variable (D t) in
/-- The Maurer–Cartan coordinates `ℓ_i = Σ_j (Dt)⁻¹_(ji) y_(j,0)`. -/
def maurerCartan (i : Fin d) : FunctionJetField F d :=
  ∑ j, algebraMap F (FunctionJetField F d) ((derivationMatrix D t)⁻¹ j i) * functionJet (j, 0)

variable (ht : IsTranscendenceBasis C t)

/-- **The jet derivation on `F` is `δa = Σ_i ℓ_i D_i a`.** -/
theorem jetFieldDerivation_eq_sum_maurerCartan (hD : (derivationMatrix D t).det ≠ 0) (a : F) :
    jetFieldDerivation ht (algebraMap F (FunctionJetField F d) a) =
      ∑ i, maurerCartan D t i * algebraMap F (FunctionJetField F d) (D i a) := by
  classical
  set K := FunctionJetField F d
  let E : F → K := fun a => jetFieldDerivation ht (algebraMap F K a) -
    ∑ i, maurerCartan D t i * algebraMap F K (D i a)
  have hadd : ∀ x y, E (x + y) = E x + E y := by
    intro x y
    simp only [E, map_add, mul_add, Finset.sum_add_distrib]
    ring
  have hmul : ∀ x y, E (x * y) = algebraMap F K x * E y + algebraMap F K y * E x := by
    intro x y
    have hs : ∑ i, maurerCartan D t i * algebraMap F K (D i (x * y)) =
        algebraMap F K x * ∑ i, maurerCartan D t i * algebraMap F K (D i y) +
          algebraMap F K y * ∑ i, maurerCartan D t i * algebraMap F K (D i x) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
      ring
    simp only [E]
    rw [hs, map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  have hC : ∀ c : C, E (algebraMap C F c) = 0 := by
    intro c
    simp only [E, ← IsScalarTower.algebraMap_apply, Derivation.map_algebraMap, map_zero,
      mul_zero, Finset.sum_const_zero, sub_zero]
    exact (jetFieldDerivation ht).map_algebraMap c
  have hA : (derivationMatrix D t)⁻¹ * derivationMatrix D t = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hD)
  have ht' : ∀ j, E (t j) = 0 := by
    intro j
    change jetFieldDerivation ht (algebraMap F K (t j)) -
      ∑ i, maurerCartan D t i * algebraMap F K (D i (t j)) = 0
    rw [jetFieldDerivation_basis, sub_eq_zero]
    have hexp : ∀ i, maurerCartan D t i * algebraMap F K (D i (t j)) = ∑ l,
        algebraMap F K ((derivationMatrix D t)⁻¹ l i * derivationMatrix D t i j) *
          functionJet (l, 0) := by
      intro i
      rw [maurerCartan, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, derivationMatrix, Matrix.of_apply]
      ring
    rw [Finset.sum_congr rfl fun i _ => hexp i, Finset.sum_comm]
    have hcol : ∀ l, ∑ i, algebraMap F K ((derivationMatrix D t)⁻¹ l i *
        derivationMatrix D t i j) * functionJet (l, 0) =
        algebraMap F K (((derivationMatrix D t)⁻¹ * derivationMatrix D t) l j) *
          functionJet (l, 0) := by
      intro l
      rw [← Finset.sum_mul, ← map_sum, Matrix.mul_apply]
    rw [Finset.sum_congr rfl fun l _ => hcol l, hA, Finset.sum_eq_single j]
    · rw [Matrix.one_apply_eq, map_one, one_mul]
    · intro l _ hl
      rw [Matrix.one_apply_ne hl, map_zero, zero_mul]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have h := twisted_eq_zero_of_isTranscendenceBasis (algebraMap F K) E hadd hmul hC ht ht' a
  exact sub_eq_zero.mp h

/-- The jets `δ^k ℓ_i` of the Maurer–Cartan coordinates. -/
def maurerCartanJet (q : ℕ × Fin d) : FunctionJetField F d :=
  ((jetFieldDerivation ht : FunctionJetField F d → FunctionJetField F d)^[q.1]) (maurerCartan D t q.2)

/-- The iterated derivatives of a linear combination of first jets are triangular. -/
theorem isJetTriangular_iterate (w : Fin d → FunctionJetField F d) (B : Matrix (Fin d) (Fin d) F)
    (hw : ∀ i, w i = ∑ j, algebraMap F (FunctionJetField F d) (B i j) * functionJet (j, 0)) :
    IsJetTriangular
      (fun q => ((jetFieldDerivation ht : FunctionJetField F d → FunctionJetField F d)^[q.1])
        (w q.2)) (fun _ => B) := by
  intro k
  induction k with
  | zero =>
      intro i
      simp only [Function.iterate_zero, id_eq, hw, sub_self]
      exact Subalgebra.zero_mem _
  | succ k ih =>
      intro i
      set R := ((jetFieldDerivation ht : FunctionJetField F d → FunctionJetField F d)^[k]) (w i) -
        ∑ j, algebraMap F (FunctionJetField F d) (B i j) * functionJet (j, k) with hR
      have hiter : ((jetFieldDerivation ht : FunctionJetField F d → FunctionJetField F d)^[k + 1])
          (w i) = jetFieldDerivation ht (R + ∑ j, algebraMap F (FunctionJetField F d) (B i j) *
            functionJet (j, k)) := by
        rw [Function.iterate_succ_apply', hR, sub_add_cancel]
      change ((jetFieldDerivation ht : FunctionJetField F d → FunctionJetField F d)^[k + 1])
          (w i) - _ ∈ _
      rw [hiter, map_add, map_sum]
      have hsum : ∀ j, jetFieldDerivation ht (algebraMap F (FunctionJetField F d) (B i j) *
          functionJet (j, k)) =
          algebraMap F (FunctionJetField F d) (B i j) * functionJet (j, k + 1) +
            functionJet (j, k) * jetFieldDerivation ht
              (algebraMap F (FunctionJetField F d) (B i j)) := by
        intro j
        rw [Derivation.leibniz, jetFieldDerivation_functionJet, smul_eq_mul, smul_eq_mul]
      simp only [hsum, Finset.sum_add_distrib]
      have hrest : jetFieldDerivation ht R + ∑ j, (functionJet (j, k) : FunctionJetField F d) *
          jetFieldDerivation ht (algebraMap F (FunctionJetField F d) (B i j)) ∈
            jetSubalgebra (k + 1) := by
        refine Subalgebra.add_mem _ (jetFieldDerivation_mem_jetSubalgebra ht (ih i))
          (Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _
            (functionJet_mem_jetSubalgebra (Nat.lt_succ_self k)) ?_)
        exact jetSubalgebra_mono (Nat.succ_le_succ (Nat.zero_le k))
          (jetFieldDerivation_mem_jetSubalgebra ht (k := 0) (Subalgebra.algebraMap_mem _ _))
      convert hrest using 1
      ring

theorem isJetTriangular_maurerCartanJet :
    IsJetTriangular (maurerCartanJet (D := D) ht) (fun _ => (derivationMatrix D t)⁻¹.transpose) :=
  isJetTriangular_iterate ht (maurerCartan D t) _ fun _ => rfl

omit [CharZero C] in
theorem derivationMatrix_inv_transpose_det_ne_zero (hD : (derivationMatrix D t).det ≠ 0) :
    (derivationMatrix D t)⁻¹.transpose.det ≠ 0 := by
  rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero hD

/-- **The jets of the Maurer–Cartan coordinates are algebraically independent over `F`.** -/
theorem algebraicIndependent_maurerCartanJet (hD : (derivationMatrix D t).det ≠ 0) :
    AlgebraicIndependent F (maurerCartanJet (D := D) ht) := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap C F).injective
  exact (isJetTriangular_maurerCartanJet ht).algebraicIndependent
    fun _ => derivationMatrix_inv_transpose_det_ne_zero hD

/-- **The jets of the Maurer–Cartan coordinates generate the jet field over `F`.** -/
theorem adjoin_maurerCartanJet_eq_top (hD : (derivationMatrix D t).det ≠ 0) :
    IntermediateField.adjoin F (Set.range (maurerCartanJet (D := D) ht)) = ⊤ :=
  (isJetTriangular_maurerCartanJet ht).adjoin_eq_top
    fun _ => derivationMatrix_inv_transpose_det_ne_zero hD

/-! ### Action of field maps on the coordinates -/

variable (D t) in
/-- The matrix `a` of `D_i ∘ φ = Σ_j a_ij φ ∘ D_j`. -/
def derivationPullbackMatrix (φ : F →ₐ[C] F) : Matrix (Fin d) (Fin d) F :=
  derivationMatrix D (φ ∘ t) * ((derivationMatrix D t).map φ)⁻¹

include ht in
/-- **The chain rule for a derivation basis.** -/
theorem derivation_comp_eq_sum (hD : (derivationMatrix D t).det ≠ 0) (φ : F →ₐ[C] F)
    (i : Fin d) (f : F) :
    D i (φ f) = ∑ j, derivationPullbackMatrix D t φ i j * φ (D j f) := by
  classical
  set M := derivationPullbackMatrix D t φ
  let E : F → F := fun f => D i (φ f) - ∑ j, M i j * φ (D j f)
  have hadd : ∀ x y, E (x + y) = E x + E y := by
    intro x y
    change D i (φ (x + y)) - ∑ j, M i j * φ (D j (x + y)) =
      (D i (φ x) - ∑ j, M i j * φ (D j x)) + (D i (φ y) - ∑ j, M i j * φ (D j y))
    simp only [map_add, mul_add, Finset.sum_add_distrib]
    ring
  have hmul : ∀ x y, E (x * y) = φ.toRingHom x * E y + φ.toRingHom y * E x := by
    intro x y
    have hs : ∑ j, M i j * φ (D j (x * y)) =
        φ x * ∑ j, M i j * φ (D j y) + φ y * ∑ j, M i j * φ (D j x) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
      ring
    change D i (φ (x * y)) - ∑ j, M i j * φ (D j (x * y)) =
      φ x * (D i (φ y) - ∑ j, M i j * φ (D j y)) + φ y * (D i (φ x) - ∑ j, M i j * φ (D j x))
    rw [hs, map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  have hC : ∀ c : C, E (algebraMap C F c) = 0 := by
    intro c
    simp only [E, AlgHom.commutes, Derivation.map_algebraMap, map_zero, mul_zero,
      Finset.sum_const_zero, sub_zero]
  have hdetφ : ((derivationMatrix D t).map φ).det ≠ 0 := by
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
    exact (map_ne_zero φ).mpr hD
  have hinv : ((derivationMatrix D t).map φ)⁻¹ * (derivationMatrix D t).map φ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdetφ)
  have ht' : ∀ k, E (t k) = 0 := by
    intro k
    change D i (φ (t k)) - ∑ j, M i j * φ (D j (t k)) = 0
    rw [sub_eq_zero]
    have h : (derivationMatrix D (φ ∘ t) * ((derivationMatrix D t).map φ)⁻¹ *
        (derivationMatrix D t).map φ) i k = derivationMatrix D (φ ∘ t) i k := by
      rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
    rw [Matrix.mul_apply] at h
    exact h.symm
  exact sub_eq_zero.mp
    (twisted_eq_zero_of_isTranscendenceBasis φ.toRingHom E hadd hmul hC ht ht' f)

include ht in
/-- The chain-rule matrix is invertible. -/
theorem derivationPullbackMatrix_det_ne_zero (hD : (derivationMatrix D t).det ≠ 0)
    (φ : F →ₐ[C] F) : (derivationPullbackMatrix D t φ).det ≠ 0 := by
  rw [derivationPullbackMatrix, Matrix.det_mul, Matrix.det_nonsing_inv]
  refine mul_ne_zero (derivationMatrix_det_ne_zero hD (isTranscendenceBasis_comp_algHom ht φ)) ?_
  rw [Ring.inverse_eq_inv']
  refine inv_ne_zero ?_
  rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
  exact (map_ne_zero φ).mpr hD

/-- **A field map acts on the Maurer–Cartan coordinates through its chain-rule matrix.** -/
theorem jetFieldExtension_maurerCartan (hD : (derivationMatrix D t).det ≠ 0) (φ : F →ₐ[C] F)
    (a : Matrix (Fin d) (Fin d) F) (ha : ∀ i f, D i (φ f) = ∑ j, a i j * φ (D j f)) (j : Fin d) :
    jetFieldExtension ht φ (maurerCartan D t j) =
      ∑ i, algebraMap F (FunctionJetField F d) (a i j) * maurerCartan D t i := by
  set K := FunctionJetField F d
  let c : Fin d → K := fun j =>
    jetFieldExtension ht φ (maurerCartan D t j) - ∑ i, algebraMap F K (a i j) * maurerCartan D t i
  suffices hc : c = 0 from sub_eq_zero.mp (congrFun hc j)
  refine eq_zero_of_sum_mul_derivationMatrix hD ((algebraMap F K).comp φ.toRingHom) c
    (fun k => ?_)
  have h1 := jetFieldExtension_deriv ht φ (algebraMap F K (t k))
  rw [jetFieldExtension_algebraMap, jetFieldDerivation_eq_sum_maurerCartan ht hD,
    jetFieldDerivation_eq_sum_maurerCartan ht hD, map_sum] at h1
  simp only [map_mul, jetFieldExtension_algebraMap, ha, map_sum] at h1
  simp only [c, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, sub_mul,
    Finset.sum_sub_distrib, sub_eq_zero]
  rw [← h1]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- **A field map commuting with every `D_i` fixes every Maurer–Cartan coordinate.** -/
theorem jetFieldExtension_maurerCartan_of_commute (hD : (derivationMatrix D t).det ≠ 0)
    (φ : F →ₐ[C] F) (hφ : ∀ i f, D i (φ f) = φ (D i f)) (j : Fin d) :
    jetFieldExtension ht φ (maurerCartan D t j) = maurerCartan D t j := by
  classical
  rw [jetFieldExtension_maurerCartan ht hD φ 1 (fun i f => by
    simp [Matrix.one_apply, hφ])]
  simp [Matrix.one_apply]

end

end GaloisForLFunctions.HTGeometry
