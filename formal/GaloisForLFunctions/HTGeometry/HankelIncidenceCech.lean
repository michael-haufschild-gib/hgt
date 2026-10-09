import GaloisForLFunctions.HTGeometry.HankelIncidenceRing
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.HomogeneousQuotient
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The Čech cohomology of the Hankel incidence variety

Let `B_j = T / (ℓ_0, …, ℓ_{j-1})`, graded by the degree in the coefficients `z` of the binary form,
and cover `Proj B_j` by the evaluation charts `D₊(G(k))`, `k = 0, …, r`.  For every `j ≤ N - r`
the augmented Čech complex of `𝒪(-e)` on `Proj B_j` is exact in every degree `p ≥ e`.  In particular
for the incidence variety `Y = Proj B_{N-r}`:

* `Ȟ^p(Y, 𝒪_Y) = 0` for `p ≥ 1`;
* every Čech `0`-cocycle comes from a polynomial in the moments.

The proof is an induction on `j` through the short exact sequences

`0 → 𝒪_{B_j}(-e-1) --ℓ_j--> 𝒪_{B_j}(-e) → 𝒪_{B_{j+1}}(-e) → 0`,

exact on every chart because `ℓ_j` is a nonzerodivisor there (`chartReg_chartForm`); the snake
chase (`FinsetCechDatum.exactAt_of_chase`) moves exactness from `(p + 1, e + 1)` and `(p, e)` on
`B_j` to `(p, e)` on `B_{j+1}`, preserving `e ≤ p`.  The case `j = 0` is projective space with
free fibre variables (`polyTwCech_exactAt`), transported along the Vandermonde change of projective
coordinates `z ↦ (G(0), …, G(r))`.
-/

namespace HTGeometry

open GaloisForLFunctions.HTGeometry.StableCoordinate.HomogeneousQuotient

universe u

variable {K : Type u} [Field K] {r N : ℕ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

local notation "𝒵" => projGrading K (Fin (r + 1)) (Fin N)

/-! ## Homogeneity -/

theorem zv_mem (i : Fin (r + 1)) : zv K r N i ∈ 𝒵 1 :=
  MvPolynomial.isWeightedHomogeneous_X K _ (Sum.inl i)

theorem vv_mem (n : Fin N) : vv K r N n ∈ 𝒵 0 :=
  MvPolynomial.isWeightedHomogeneous_X K _ (Sum.inr n)

theorem vAt_mem (m : ℕ) : vAt K r N m ∈ 𝒵 0 := by
  rw [vAt]
  split_ifs
  · exact vv_mem _
  · exact Submodule.zero_mem _

theorem hankelEq_mem (j : ℕ) : hankelEq K r N j ∈ 𝒵 1 := by
  rw [hankelEq_eq]
  exact Submodule.sum_mem _ fun i _ => by
    simpa using SetLike.mul_mem_graded (zv_mem (K := K) (N := N) i) (vAt_mem (K := K) (r := r) (i + j))

theorem algebraMap_mem (a : K) : algebraMap K (IncRing K r N) a ∈ 𝒵 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ (SetLike.one_mem_graded _)

theorem chartForm_mem (t : K) : chartForm K r N t ∈ 𝒵 1 := by
  rw [chartForm, gPoly, Polynomial.eval_finsetSum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← map_pow]
  simpa using SetLike.mul_mem_graded (zv_mem (K := K) (N := N) i) (algebraMap_mem (r := r) (N := N) (t ^ (i : ℕ)))

theorem hankelIdeal_isHomogeneous (j : ℕ) : (hankelIdeal K r N j).IsHomogeneous 𝒵 := by
  refine Ideal.homogeneous_span _ _ ?_
  rintro _ ⟨m, -, rfl⟩
  exact ⟨1, hankelEq_mem m⟩

/-- Substitutions by homogeneous elements of the right degrees preserve the grading. -/
theorem aeval_mem_projGrading {φ : Fin (r + 1) ⊕ Fin N → IncRing K r N}
    (hφ : ∀ k, φ k ∈ 𝒵 (projWeight (Fin (r + 1)) (Fin N) k)) {d : ℕ} {x : IncRing K r N}
    (hx : x ∈ 𝒵 d) : MvPolynomial.aeval φ x ∈ 𝒵 d := by
  classical
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun b hb => ?_
  have hw : Finsupp.weight (projWeight (Fin (r + 1)) (Fin N)) b = d :=
    (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp hx
      (MvPolynomial.mem_support_iff.mp hb)
  rw [MvPolynomial.aeval_monomial, ← hw, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  rw [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
  exact SetLike.prod_pow_mem_graded 𝒵 _ _ b fun k _ => hφ k

/-! ## The quotient rings -/

variable (K r N) in
/-- `B_j = T / (ℓ_0, …, ℓ_{j-1})`. -/
abbrev HankelQuot (j : ℕ) := IncRing K r N ⧸ hankelIdeal K r N j

variable (K r N) in
/-- The grading of `B_j`. -/
noncomputable abbrev quotGrading (j : ℕ) : ℕ → Submodule K (HankelQuot K r N j) :=
  piece 𝒵 (hankelIdeal K r N j)

noncomputable instance quotGradedAlgebra (j : ℕ) : GradedAlgebra (quotGrading K r N j) :=
  gradedAlgebra 𝒵 _ (hankelIdeal_isHomogeneous j)

variable (K) in
/-- The evaluation nodes `0, 1, …, r`. -/
def node (k : Fin (r + 1)) : K := ((k : ℕ) : K)

theorem node_injective [CharZero K] : Function.Injective (node K (r := r)) := by
  intro k l h
  have h' : ((k : ℕ) : K) = ((l : ℕ) : K) := h
  exact Fin.ext (by exact_mod_cast h')

variable (K r N) in
/-- The chart forms `G(k)` on `B_j`. -/
noncomputable def qChart (j : ℕ) (k : Fin (r + 1)) : HankelQuot K r N j :=
  Ideal.Quotient.mk _ (chartForm K r N (node K k))

theorem qChart_mem (j : ℕ) (k : Fin (r + 1)) : qChart K r N j k ∈ quotGrading K r N j 1 :=
  mk_mem_piece 𝒵 _ (chartForm_mem _)

variable (K r N) in
/-- **The Čech datum of `𝒪(-e)` on `Proj B_j`** for the evaluation charts. -/
noncomputable abbrev hankelCech (j e : ℕ) : FinsetCechDatum (Fin (r + 1)) :=
  twCech (quotGrading K r N j) (qChart K r N j) (qChart_mem j) e

/-! ## One more equation -/

section Step

variable (j : ℕ)

variable (K r N) in
/-- The quotient map `B_j → B_{j+1}`. -/
noncomputable def stepMap : HankelQuot K r N j →+* HankelQuot K r N (j + 1) :=
  Ideal.Quotient.factor (hankelIdeal_mono (Nat.le_succ j))

theorem stepMap_mk (x : IncRing K r N) :
    stepMap K r N j (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

theorem stepMap_qChart (k : Fin (r + 1)) :
    stepMap K r N j (qChart K r N j k) = qChart K r N (j + 1) k := rfl

theorem stepMap_mem {i : ℕ} {x : HankelQuot K r N j} (hx : x ∈ quotGrading K r N j i) :
    stepMap K r N j x ∈ quotGrading K r N (j + 1) i := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact mk_mem_piece 𝒵 _ ha

theorem stepMap_lift {i : ℕ} {x' : HankelQuot K r N (j + 1)} (hx' : x' ∈ quotGrading K r N (j + 1) i) :
    ∃ x ∈ quotGrading K r N j i, stepMap K r N j x = x' := by
  obtain ⟨a, ha, rfl⟩ := hx'
  exact ⟨Ideal.Quotient.mk _ a, mk_mem_piece 𝒵 _ ha, rfl⟩

variable (K r N) in
/-- The `j`-th equation on `B_j`. -/
noncomputable def qEq : HankelQuot K r N j := Ideal.Quotient.mk _ (hankelEq K r N j)

theorem qEq_mem : qEq K r N j ∈ quotGrading K r N j 1 := mk_mem_piece 𝒵 _ (hankelEq_mem j)

theorem stepMap_qEq : stepMap K r N j (qEq K r N j) = 0 := by
  rw [qEq, stepMap_mk, Ideal.Quotient.eq_zero_iff_mem]
  exact hankelEq_mem_hankelIdeal (Nat.lt_succ_self j)

/-- **The kernel of `B_j → B_{j+1}` is generated by `ℓ_j`.** -/
theorem stepMap_ker (x : HankelQuot K r N j) (hx : stepMap K r N j x = 0) :
    ∃ z, x = qEq K r N j * z := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [stepMap_mk, Ideal.Quotient.eq_zero_iff_mem, hankelIdeal_succ] at hx
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
  refine ⟨Ideal.Quotient.mk _ d, ?_⟩
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb, zero_add, map_mul, qEq, mul_comm]

/-- **Chart regularity in the localized quotient.** -/
theorem algebraMap_qEq_mem_nonZeroDivisors {f : IncRing K r N} (hf : ChartReg f j) :
    algebraMap (HankelQuot K r N j) (Localization.Away (Ideal.Quotient.mk (hankelIdeal K r N j) f))
      (qEq K r N j) ∈ nonZeroDivisors _ := by
  rw [mem_nonZeroDivisors_iff_right]
  intro y hy
  obtain ⟨⟨x', ⟨_, m, rfl⟩⟩, hxy⟩ := IsLocalization.surj
    (Submonoid.powers (Ideal.Quotient.mk (hankelIdeal K r N j) f)) y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x'
  simp only at hxy
  have h1 : algebraMap (HankelQuot K r N j) (Localization.Away (Ideal.Quotient.mk (hankelIdeal K r N j) f))
      (Ideal.Quotient.mk _ (x * hankelEq K r N j)) = 0 := by
    rw [map_mul, map_mul, ← hxy, mul_right_comm,
      show Ideal.Quotient.mk (hankelIdeal K r N j) (hankelEq K r N j) = qEq K r N j from rfl, hy,
      zero_mul]
  obtain ⟨⟨_, a, rfl⟩, ha⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (Ideal.Quotient.mk (hankelIdeal K r N j) f)) _ _).mp h1
  simp only [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at ha
  obtain ⟨b, hb⟩ := hf x ⟨a, by rwa [mul_comm (hankelEq K r N j)]⟩
  have h2 : algebraMap (HankelQuot K r N j) (Localization.Away (Ideal.Quotient.mk (hankelIdeal K r N j) f))
      (Ideal.Quotient.mk _ x) = 0 := by
    refine (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (Ideal.Quotient.mk (hankelIdeal K r N j) f)) _ _).mpr
        ⟨⟨_, b, rfl⟩, ?_⟩
    simp only [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hb
  have hu : IsUnit (algebraMap (HankelQuot K r N j) (Localization.Away (Ideal.Quotient.mk (hankelIdeal K r N j) f))
      (Ideal.Quotient.mk (hankelIdeal K r N j) f ^ m)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit _).pow m
  rw [h2] at hxy
  exact (hu.mul_left_eq_zero).mp hxy

end Step

/-! ## Isomorphisms of twisted data -/

section Iso

variable {K' : Type*} [CommRing K'] {M M' : Type u} [CommRing M] [CommRing M'] [Algebra K' M]
  [Algebra K' M'] {𝒜₁ : ℕ → Submodule K' M} {𝒜₂ : ℕ → Submodule K' M'} [GradedAlgebra 𝒜₁]
  [GradedAlgebra 𝒜₂] {ι : Type*} [DecidableEq ι] {w : ι → M} {w' : ι → M'}

omit [DecidableEq ι] in
theorem locMap_locMap (f : M →+* M') (g : M' →+* M) (hfw : ∀ i, f (w i) = w' i)
    (hgw : ∀ i, g (w' i) = w i) (hgf : ∀ a, g (f a) = a) (s : Finset ι) (y : LocAt w s) :
    locMap g hgw s (locMap f hfw s y) = y := by
  have : (locMap g hgw s).comp (locMap f hfw s) = RingHom.id _ :=
    IsLocalization.ringHom_ext (Submonoid.powers (wProd w s)) (RingHom.ext fun a => by
      simp only [RingHom.comp_apply, locMap_algebraMap, hgf, RingHom.id_apply])
  exact DFunLike.congr_fun this y

/-- **A graded ring isomorphism carrying the cover to the cover induces isomorphic twisted Čech
data.** -/
theorem twMap_app_bijective (f : M →+* M') (g : M' →+* M) (hfw : ∀ i, f (w i) = w' i)
    (hgw : ∀ i, g (w' i) = w i) (hgf : ∀ a, g (f a) = a) (hfg : ∀ a, f (g a) = a)
    (hf : ∀ i x, x ∈ 𝒜₁ i → f x ∈ 𝒜₂ i) (hg : ∀ i x, x ∈ 𝒜₂ i → g x ∈ 𝒜₁ i)
    (hw : ∀ i, w i ∈ 𝒜₁ 1) (hw' : ∀ i, w' i ∈ 𝒜₂ 1) (e : ℕ) (s : Finset ι) :
    Function.Bijective ((twMap f hfw hf hw hw' e).app s) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨(twMap g hgw hg hw' hw e).app s, fun y => ?_,
    fun y => ?_⟩
  · apply twVal_injective hw
    rw [twMap_app_val, twMap_app_val]
    exact locMap_locMap f g hfw hgw hgf s _
  · apply twVal_injective hw'
    rw [twMap_app_val, twMap_app_val]
    exact locMap_locMap g f hgw hfw hfg s _

end Iso

/-! ## The base case -/

section Base

theorem chartForm_eq_sum (t : K) :
    chartForm K r N t = ∑ i : Fin (r + 1), t ^ (i : ℕ) • zv K r N i := by
  rw [chartForm, gPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← map_pow,
    Algebra.smul_def, mul_comm]

variable (K r) in
/-- The Vandermonde matrix of the nodes. -/
noncomputable abbrev nodeMatrix : Matrix (Fin (r + 1)) (Fin (r + 1)) K := Matrix.vandermonde (node K)

theorem isUnit_det_nodeMatrix [CharZero K] : IsUnit (nodeMatrix K r).det :=
  isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr node_injective)

variable (K r N) in
/-- The change of projective coordinates `z_k ↦ G(k)`. -/
noncomputable def vandermondeSubst : IncRing K r N →ₐ[K] IncRing K r N :=
  MvPolynomial.aeval (Sum.elim (fun k => chartForm K r N (node K k)) (vv K r N))

variable (K r N) in
/-- Its inverse `z_i ↦ ∑_k (V⁻¹)_{ik} z_k`. -/
noncomputable def vandermondeSubstInv : IncRing K r N →ₐ[K] IncRing K r N :=
  MvPolynomial.aeval (Sum.elim (fun i => ∑ k, (nodeMatrix K r)⁻¹ i k • zv K r N k) (vv K r N))

theorem vandermondeSubst_zv (k : Fin (r + 1)) :
    vandermondeSubst K r N (zv K r N k) = chartForm K r N (node K k) := by
  simp [vandermondeSubst, zv]

theorem vandermondeSubst_vv (n : Fin N) : vandermondeSubst K r N (vv K r N n) = vv K r N n := by
  simp [vandermondeSubst, vv]

theorem vandermondeSubstInv_zv (i : Fin (r + 1)) :
    vandermondeSubstInv K r N (zv K r N i) = ∑ k, (nodeMatrix K r)⁻¹ i k • zv K r N k := by
  simp [vandermondeSubstInv, zv]

theorem vandermondeSubstInv_vv (n : Fin N) :
    vandermondeSubstInv K r N (vv K r N n) = vv K r N n := by
  simp [vandermondeSubstInv, vv]

theorem vandermondeSubstInv_comp [CharZero K] :
    (vandermondeSubstInv K r N).comp (vandermondeSubst K r N) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  rintro (k | n)
  · change vandermondeSubstInv K r N (vandermondeSubst K r N (zv K r N k)) = zv K r N k
    rw [vandermondeSubst_zv, chartForm_eq_sum, map_sum]
    simp only [map_smul, vandermondeSubstInv_zv, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have h := Matrix.mul_nonsing_inv (nodeMatrix K r) isUnit_det_nodeMatrix
    have hk : ∀ l : Fin (r + 1), ∑ i : Fin (r + 1), node K k ^ (i : ℕ) * (nodeMatrix K r)⁻¹ i l
        = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) K) k l := by
      intro l
      rw [← h, Matrix.mul_apply]
      rfl
    simp only [hk, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  · change vandermondeSubstInv K r N (vandermondeSubst K r N (vv K r N n)) = vv K r N n
    rw [vandermondeSubst_vv, vandermondeSubstInv_vv]

theorem vandermondeSubst_comp [CharZero K] :
    (vandermondeSubst K r N).comp (vandermondeSubstInv K r N) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  rintro (i | n)
  · change vandermondeSubst K r N (vandermondeSubstInv K r N (zv K r N i)) = zv K r N i
    rw [vandermondeSubstInv_zv, map_sum]
    simp only [map_smul, vandermondeSubst_zv, chartForm_eq_sum, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have h := Matrix.nonsing_inv_mul (nodeMatrix K r) isUnit_det_nodeMatrix
    have hk : ∀ l : Fin (r + 1), ∑ k : Fin (r + 1), (nodeMatrix K r)⁻¹ i k * node K k ^ (l : ℕ)
        = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) K) i l := by
      intro l
      rw [← h, Matrix.mul_apply]
      rfl
    simp only [hk, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  · change vandermondeSubst K r N (vandermondeSubstInv K r N (vv K r N n)) = vv K r N n
    rw [vandermondeSubstInv_vv, vandermondeSubst_vv]

theorem hankelIdeal_zero : hankelIdeal K r N 0 = ⊥ := by
  rw [hankelIdeal, Ideal.span_eq_bot]
  rintro _ ⟨m, hm, rfl⟩
  exact absurd hm (Nat.not_lt_zero m)

variable (K r N) in
/-- `T → B_0`, after the Vandermonde change of coordinates. -/
noncomputable def baseMap : IncRing K r N →+* HankelQuot K r N 0 :=
  (Ideal.Quotient.mk (hankelIdeal K r N 0)).comp (vandermondeSubst K r N).toRingHom

variable (K r N) in
/-- `B_0 → T`, the inverse. -/
noncomputable def baseMapInv : HankelQuot K r N 0 →+* IncRing K r N :=
  Ideal.Quotient.lift (hankelIdeal K r N 0) (vandermondeSubstInv K r N).toRingHom fun a ha => by
    rw [hankelIdeal_zero, Ideal.mem_bot] at ha
    rw [ha, map_zero]

theorem baseMapInv_mk (a : IncRing K r N) :
    baseMapInv K r N (Ideal.Quotient.mk _ a) = vandermondeSubstInv K r N a := rfl

theorem baseMapInv_baseMap [CharZero K] (a : IncRing K r N) :
    baseMapInv K r N (baseMap K r N a) = a :=
  DFunLike.congr_fun (vandermondeSubstInv_comp (K := K) (r := r) (N := N)) a

theorem baseMap_baseMapInv [CharZero K] (x : HankelQuot K r N 0) :
    baseMap K r N (baseMapInv K r N x) = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk _ (vandermondeSubst K r N (vandermondeSubstInv K r N a)) = _
  rw [show vandermondeSubst K r N (vandermondeSubstInv K r N a) = a from
    DFunLike.congr_fun (vandermondeSubst_comp (K := K) (r := r) (N := N)) a]

theorem baseMapInv_qChart [CharZero K] (k : Fin (r + 1)) :
    baseMapInv K r N (qChart K r N 0 k) = projCoord K (Fin (r + 1)) (Fin N) k := by
  rw [qChart, baseMapInv_mk, ← vandermondeSubst_zv]
  exact DFunLike.congr_fun (vandermondeSubstInv_comp (K := K) (r := r) (N := N)) _

theorem baseMap_projCoord (k : Fin (r + 1)) :
    baseMap K r N (projCoord K (Fin (r + 1)) (Fin N) k) = qChart K r N 0 k := by
  change Ideal.Quotient.mk _ (vandermondeSubst K r N (zv K r N k)) = _
  rw [vandermondeSubst_zv]
  rfl

theorem vandermondeSubst_mem {d : ℕ} {x : IncRing K r N} (hx : x ∈ 𝒵 d) :
    vandermondeSubst K r N x ∈ 𝒵 d := by
  refine aeval_mem_projGrading ?_ hx
  rintro (k | n)
  · exact chartForm_mem _
  · exact vv_mem n

theorem vandermondeSubstInv_mem {d : ℕ} {x : IncRing K r N} (hx : x ∈ 𝒵 d) :
    vandermondeSubstInv K r N x ∈ 𝒵 d := by
  refine aeval_mem_projGrading ?_ hx
  rintro (i | n)
  · exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (zv_mem k)
  · exact vv_mem n

theorem baseMap_mem (d : ℕ) (x : IncRing K r N) (hx : x ∈ 𝒵 d) :
    baseMap K r N x ∈ quotGrading K r N 0 d :=
  mk_mem_piece 𝒵 _ (vandermondeSubst_mem hx)

theorem baseMapInv_mem (d : ℕ) (x : HankelQuot K r N 0) (hx : x ∈ quotGrading K r N 0 d) :
    baseMapInv K r N x ∈ 𝒵 d := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact vandermondeSubstInv_mem ha

/-- **The base case**: Čech exactness of `𝒪(-e)` on `Proj B_0 = ℙ^r × 𝔸^N` for the evaluation
charts. -/
theorem hankelCech_zero_exactAt [CharZero K] {e p : ℕ} (hep : e ≤ p) :
    (hankelCech K r N 0 e).ExactAt p :=
  FinsetCechDatum.exactAt_of_bijective
    (twMap (baseMapInv K r N) baseMapInv_qChart baseMapInv_mem (qChart_mem 0) projCoord_mem e)
    (twMap_app_bijective (baseMapInv K r N) (baseMap K r N) baseMapInv_qChart baseMap_projCoord
      baseMap_baseMapInv baseMapInv_baseMap baseMapInv_mem baseMap_mem (qChart_mem 0)
      projCoord_mem e)
    (polyTwCech_exactAt (K := K) (ι := Fin (r + 1)) (ν := Fin N) hep)

end Base

/-! ## The induction -/

theorem chartReg_wProd {j : ℕ} (hj : j + r < N) {s : Finset (Fin (r + 1))} (hs : s.Nonempty) :
    ChartReg (wProd (fun k => chartForm K r N (node K k)) s) j := by
  classical
  obtain ⟨k, hk⟩ := hs
  rw [wProd, ← Finset.mul_prod_erase s _ hk]
  exact (chartReg_chartForm (node K k) hj).mul _

theorem algebraMap_qEq_mem_nonZeroDivisors' {j : ℕ} {f : IncRing K r N} (hf : ChartReg f j)
    {f' : HankelQuot K r N j} (hf' : f' = Ideal.Quotient.mk _ f) :
    algebraMap (HankelQuot K r N j) (Localization.Away f') (qEq K r N j) ∈ nonZeroDivisors _ := by
  subst hf'
  exact algebraMap_qEq_mem_nonZeroDivisors j hf

theorem wProd_qChart (j : ℕ) (s : Finset (Fin (r + 1))) :
    wProd (qChart K r N j) s
      = Ideal.Quotient.mk _ (wProd (fun k => chartForm K r N (node K k)) s) := by
  rw [wProd, wProd, map_prod]
  rfl

/-- **The Čech complexes of the Hankel quotients.**  For `j + r ≤ N` the augmented Čech complex of
`𝒪(-e)` on `Proj B_j` is exact in every degree `p ≥ e`. -/
theorem hankelCech_exactAt [CharZero K] :
    ∀ j : ℕ, j + r ≤ N → ∀ e p : ℕ, e ≤ p → (hankelCech K r N j e).ExactAt p := by
  intro j
  induction j with
  | zero => exact fun _ e p hep => hankelCech_zero_exactAt hep
  | succ j ih =>
    intro hj e p hep
    have hj' : j + r < N := by omega
    exact FinsetCechDatum.exactAt_of_chase
      (twMul (𝒜 := quotGrading K r N j) (qChart_mem j) (qEq_mem j) e)
      (twMap (𝒜 := quotGrading K r N j) (𝒜' := quotGrading K r N (j + 1)) (stepMap K r N j)
        (stepMap_qChart j) (fun _ _ hx => stepMap_mem j hx) (qChart_mem j) (qChart_mem (j + 1)) e) p
      (fun s _ x => twMap_twMul (𝒜 := quotGrading K r N j) (𝒜' := quotGrading K r N (j + 1))
        (stepMap K r N j) (stepMap_qChart j) (fun _ _ hx => stepMap_mem j hx) (qChart_mem j)
        (qChart_mem (j + 1)) (qEq_mem j) (stepMap_qEq j) e s x)
      (fun s hs => twMap_surjective (𝒜 := quotGrading K r N j) (𝒜' := quotGrading K r N (j + 1))
        (stepMap K r N j) (stepMap_qChart j) (fun _ _ hx => stepMap_mem j hx) (qChart_mem j)
        (qChart_mem (j + 1)) (fun _ _ hx' => stepMap_lift j hx') e (Finset.card_pos.mp (by omega)))
      (fun s hs y hy => twMap_exact (𝒜 := quotGrading K r N j) (𝒜' := quotGrading K r N (j + 1))
        (stepMap K r N j) (stepMap_qChart j) (fun _ _ hx => stepMap_mem j hx) (qChart_mem j)
        (qChart_mem (j + 1)) (qEq_mem j) (stepMap_ker j) e (Finset.card_pos.mp (by omega)) y hy)
      (fun s hs => twMul_injective (𝒜 := quotGrading K r N j) (qChart_mem j) (qEq_mem j) e
        (algebraMap_qEq_mem_nonZeroDivisors' (chartReg_wProd hj' (Finset.card_pos.mp (by omega)))
          (wProd_qChart j s)))
      (ih (by omega) (e + 1) (p + 1) (by omega)) (ih (by omega) e p hep)

end HTGeometry
