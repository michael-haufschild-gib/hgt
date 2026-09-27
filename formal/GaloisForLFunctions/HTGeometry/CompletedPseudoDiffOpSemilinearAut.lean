import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpVectorLattice

/-!
# Uniformizer-semilinear automorphisms of completed skew vector spaces

The slope theory is proved for the class of additive automorphisms `T` of a completed skew vector
space `E` that are semilinear for a ring automorphism `ρ` of `𝔻` preserving the valuation ring and
fixing the uniformizer.  The class contains the canonical variational action and is closed under
composition, inversion and uniformizer scaling, so it contains every normalized power `ϖ^c T^d`.

* `DiffOp.IsUniformizerRingAut`, `DiffOp.IsUniformizerSemilinear` — the class, with its closure
  under `1`, products, inverses and powers, and the scalings `DiffOp.uniformizerSMulAut`.
* `DiffOp.semilinearImage` — the image `T M` of an integral submodule, again an integral submodule;
  it is multiplicative in `T`, commutes with uniformizer dilations and sums, and preserves finite
  generation.  `DiffOp.semilinearSubspaceImage` is the image of a subspace.
* `DiffOp.finrank_semilinearSubspaceImage` — a semilinear bijection preserves dimension, so an
  image contained in its source equals it (`DiffOp.semilinearSubspaceImage_eq_of_le`).
* `DiffOp.forwardBoundedSubspace` — the vectors whose forward orbit stays in one finitely generated
  integral submodule form a subspace; the scalar step uses that `ρⁿ(a)` lies in `ϖ^{-t}𝒪` uniformly
  in `n` as soon as `ϖ^t a` is integral.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K]

attribute [local instance] completedPseudoDiffOpIntegerSMul

/-- Ring automorphisms of `𝔻` that preserve the valuation ring and fix the uniformizer. -/
def IsUniformizerRingAut (ρ : CompletedPseudoDiffOp K ≃+* CompletedPseudoDiffOp K) : Prop :=
  (∀ a, a ∈ CompletedPseudoDiffOpInteger (K := K) → ρ a ∈ CompletedPseudoDiffOpInteger (K := K)) ∧
    (∀ a, a ∈ CompletedPseudoDiffOpInteger (K := K) →
      ρ.symm a ∈ CompletedPseudoDiffOpInteger (K := K)) ∧
    ρ (completedPseudoDiffOpUniformizerUnit (K := K) : CompletedPseudoDiffOp K) =
      completedPseudoDiffOpUniformizerUnit (K := K)

namespace IsUniformizerRingAut

variable {ρ σ : CompletedPseudoDiffOp K ≃+* CompletedPseudoDiffOp K}

theorem refl : IsUniformizerRingAut (RingEquiv.refl (CompletedPseudoDiffOp K)) :=
  ⟨fun _ h => h, fun _ h => h, rfl⟩

theorem trans (hρ : IsUniformizerRingAut ρ) (hσ : IsUniformizerRingAut σ) :
    IsUniformizerRingAut (ρ.trans σ) :=
  ⟨fun a ha => hσ.1 _ (hρ.1 a ha), fun a ha => hρ.2.1 _ (hσ.2.1 a ha), by
    rw [RingEquiv.trans_apply, hρ.2.2, hσ.2.2]⟩

theorem symm (hρ : IsUniformizerRingAut ρ) : IsUniformizerRingAut ρ.symm :=
  ⟨hρ.2.1, fun a ha => by rw [RingEquiv.symm_symm]; exact hρ.1 a ha, by
    rw [RingEquiv.symm_apply_eq, hρ.2.2]⟩

theorem map_uniformizerZPow (hρ : IsUniformizerRingAut ρ) (k : ℤ) :
    ρ (uniformizerZPow (K := K) k) = uniformizerZPow k := by
  rw [uniformizerZPow, Units.val_zpow_eq_zpow_val, map_zpow₀, hρ.2.2]

theorem map_integer (hρ : IsUniformizerRingAut ρ) {a : CompletedPseudoDiffOp K}
    (ha : a ∈ CompletedPseudoDiffOpInteger (K := K)) :
    ρ a ∈ CompletedPseudoDiffOpInteger (K := K) := hρ.1 a ha

end IsUniformizerRingAut

/-- Conjugation by a uniformizer power. -/
def uniformizerConjRingEquiv (k : ℤ) : CompletedPseudoDiffOp K ≃+* CompletedPseudoDiffOp K where
  toFun a := uniformizerZPow k * a * uniformizerZPow (-k)
  invFun a := uniformizerZPow (-k) * a * uniformizerZPow k
  left_inv a := by
    simp only [← mul_assoc, uniformizerZPow_neg_mul, one_mul]
    rw [mul_assoc, uniformizerZPow_neg_mul, mul_one]
  right_inv a := by
    simp only [← mul_assoc, uniformizerZPow_mul_neg, one_mul]
    rw [mul_assoc, uniformizerZPow_mul_neg, mul_one]
  map_mul' a b := by
    simp only [mul_assoc]
    rw [← mul_assoc (uniformizerZPow (K := K) (-k)) (uniformizerZPow k), uniformizerZPow_neg_mul,
      one_mul]
  map_add' a b := by rw [mul_add, add_mul]

theorem uniformizerConjRingEquiv_apply (k : ℤ) (a : CompletedPseudoDiffOp K) :
    uniformizerConjRingEquiv k a = uniformizerZPow k * a * uniformizerZPow (-k) := rfl

theorem isUniformizerRingAut_uniformizerConjRingEquiv (k : ℤ) :
    IsUniformizerRingAut (uniformizerConjRingEquiv (K := K) k) := by
  refine ⟨fun a ha => uniformizerZPow_conj_mem_integer k ha, fun a ha => ?_, ?_⟩
  · have := uniformizerZPow_conj_mem_integer (K := K) (-k) ha
    rwa [neg_neg] at this
  · have hπ : (completedPseudoDiffOpUniformizerUnit (K := K) : CompletedPseudoDiffOp K) =
        uniformizerZPow 1 := by rw [uniformizerZPow, zpow_one]
    rw [uniformizerConjRingEquiv_apply, hπ, ← uniformizerZPow_add, ← uniformizerZPow_add]
    congr 1
    ring

variable {E : Type*} [AddCommGroup E] [Module (CompletedPseudoDiffOp K) E]

/-- Additive automorphisms semilinear for a uniformizer ring automorphism. -/
def IsUniformizerSemilinear (T : (E ≃ₗ[ℤ] E)) : Prop :=
  ∃ ρ : CompletedPseudoDiffOp K ≃+* CompletedPseudoDiffOp K,
    IsUniformizerRingAut ρ ∧ ∀ (a : CompletedPseudoDiffOp K) (x : E), T (a • x) = ρ a • T x

namespace IsUniformizerSemilinear

variable {T S : (E ≃ₗ[ℤ] E)}

theorem one : IsUniformizerSemilinear (K := K) (1 : (E ≃ₗ[ℤ] E)) :=
  ⟨RingEquiv.refl _, IsUniformizerRingAut.refl, fun _ _ => rfl⟩

theorem mul (hT : IsUniformizerSemilinear (K := K) T) (hS : IsUniformizerSemilinear (K := K) S) :
    IsUniformizerSemilinear (K := K) (T * S) := by
  obtain ⟨ρ, hρ, hTρ⟩ := hT
  obtain ⟨σ, hσ, hSσ⟩ := hS
  refine ⟨σ.trans ρ, hσ.trans hρ, fun a x => ?_⟩
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hSσ, hTρ, RingEquiv.trans_apply]

theorem inv (hT : IsUniformizerSemilinear (K := K) T) :
    IsUniformizerSemilinear (K := K) T⁻¹ := by
  obtain ⟨ρ, hρ, hTρ⟩ := hT
  refine ⟨ρ.symm, hρ.symm, fun a x => ?_⟩
  apply T.injective
  rw [hTρ, RingEquiv.apply_symm_apply]
  change T (T.symm (a • x)) = a • T (T.symm x)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem pow (hT : IsUniformizerSemilinear (K := K) T) (n : ℕ) :
    IsUniformizerSemilinear (K := K) (T ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact one
  | succ n ih => rw [pow_succ]; exact ih.mul hT

theorem zpow (hT : IsUniformizerSemilinear (K := K) T) (n : ℤ) :
    IsUniformizerSemilinear (K := K) (T ^ n) := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact hT.pow n
  | negSucc n => rw [zpow_negSucc]; exact (hT.pow (n + 1)).inv

theorem map_uniformizerZPow_smul (hT : IsUniformizerSemilinear (K := K) T) (k : ℤ) (x : E) :
    T (uniformizerZPow (K := K) k • x) = uniformizerZPow (K := K) k • T x := by
  obtain ⟨ρ, hρ, hTρ⟩ := hT
  rw [hTρ, hρ.map_uniformizerZPow]

theorem map_integer_smul (hT : IsUniformizerSemilinear (K := K) T)
    {a : CompletedPseudoDiffOp K} (ha : a ∈ CompletedPseudoDiffOpInteger (K := K)) (x : E) :
    ∃ b ∈ CompletedPseudoDiffOpInteger (K := K), T (a • x) = b • T x := by
  obtain ⟨ρ, hρ, hTρ⟩ := hT
  exact ⟨ρ a, hρ.map_integer ha, hTρ a x⟩

end IsUniformizerSemilinear

/-- Multiplication by a uniformizer power, as an additive automorphism. -/
def uniformizerSMulAut (k : ℤ) : (E ≃ₗ[ℤ] E) :=
  AddEquiv.toIntLinearEquiv
    { toFun x := uniformizerZPow (K := K) k • x
      invFun x := uniformizerZPow (K := K) (-k) • x
      left_inv x := by simp only [smul_smul, uniformizerZPow_neg_mul, one_smul]
      right_inv x := by simp only [smul_smul, uniformizerZPow_mul_neg, one_smul]
      map_add' x y := smul_add _ x y }

theorem uniformizerSMulAut_apply (k : ℤ) (x : E) :
    uniformizerSMulAut (K := K) k x = uniformizerZPow (K := K) k • x := rfl

theorem isUniformizerSemilinear_uniformizerSMulAut (k : ℤ) :
    IsUniformizerSemilinear (K := K) (uniformizerSMulAut (K := K) (E := E) k) := by
  refine ⟨uniformizerConjRingEquiv k, isUniformizerRingAut_uniformizerConjRingEquiv k,
    fun a x => ?_⟩
  rw [uniformizerSMulAut_apply, uniformizerSMulAut_apply, uniformizerConjRingEquiv_apply,
    smul_smul, smul_smul, mul_assoc (uniformizerZPow k * a), uniformizerZPow_neg_mul, mul_one]

variable {T S : (E ≃ₗ[ℤ] E)}

/-- The image `T M` of an integral submodule. -/
def semilinearImage (T : (E ≃ₗ[ℤ] E)) (hT : IsUniformizerSemilinear (K := K) T)
    (M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E) :
    Submodule (CompletedPseudoDiffOpInteger (K := K)) E where
  carrier := {y | T⁻¹ y ∈ M}
  add_mem' {x y} hx hy := by
    change T⁻¹ (x + y) ∈ M
    rw [_root_.map_add]
    exact M.add_mem hx hy
  zero_mem' := by
    change T⁻¹ 0 ∈ M
    rw [_root_.map_zero]
    exact M.zero_mem
  smul_mem' a y hy := by
    change T⁻¹ ((a : CompletedPseudoDiffOp K) • y) ∈ M
    obtain ⟨b, hb, hby⟩ := IsUniformizerSemilinear.map_integer_smul (hT.inv) a.2 y
    rw [hby]
    exact M.smul_mem ⟨b, hb⟩ hy

variable {hT : IsUniformizerSemilinear (K := K) T} {hS : IsUniformizerSemilinear (K := K) S}
variable {M N : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}

theorem mem_semilinearImage {y : E} : y ∈ semilinearImage T hT M ↔ T⁻¹ y ∈ M := Iff.rfl

theorem apply_mem_semilinearImage {x : E} (hx : x ∈ M) : T x ∈ semilinearImage T hT M := by
  rw [mem_semilinearImage]
  change T.symm (T x) ∈ M
  rwa [LinearEquiv.symm_apply_apply]

theorem mem_semilinearImage_iff_exists {y : E} :
    y ∈ semilinearImage T hT M ↔ ∃ x ∈ M, T x = y := by
  refine ⟨fun hy => ⟨_, hy, ?_⟩, ?_⟩
  · change T (T.symm y) = y
    exact LinearEquiv.apply_symm_apply _ _
  · rintro ⟨x, hx, rfl⟩
    exact apply_mem_semilinearImage hx

theorem semilinearImage_mono (h : M ≤ N) : semilinearImage T hT M ≤ semilinearImage T hT N :=
  fun _ hy => h hy

theorem semilinearImage_one (h1 : IsUniformizerSemilinear (K := K) (1 : (E ≃ₗ[ℤ] E))) :
    semilinearImage 1 h1 M = M := by
  ext y
  rw [mem_semilinearImage, inv_one]
  rfl

theorem semilinearImage_mul (hTS : IsUniformizerSemilinear (K := K) (T * S)) :
    semilinearImage (T * S) hTS M = semilinearImage T hT (semilinearImage S hS M) := by
  ext y
  rw [mem_semilinearImage, mem_semilinearImage, mem_semilinearImage, mul_inv_rev,
    LinearEquiv.mul_apply]

theorem semilinearImage_uniformizerDilate (k : ℤ) :
    semilinearImage T hT (uniformizerDilate k M) = uniformizerDilate k (semilinearImage T hT M) := by
  ext y
  rw [mem_semilinearImage, mem_uniformizerDilate, mem_uniformizerDilate, mem_semilinearImage,
    IsUniformizerSemilinear.map_uniformizerZPow_smul (hT.inv)]

theorem semilinearImage_sup :
    semilinearImage T hT (M ⊔ N) = semilinearImage T hT M ⊔ semilinearImage T hT N := by
  apply le_antisymm
  · intro y hy
    rw [mem_semilinearImage, Submodule.mem_sup] at hy
    obtain ⟨m, hm, n, hn, hmn⟩ := hy
    have hy' : y = T m + T n := by
      rw [← _root_.map_add, hmn]
      change y = T (T.symm y)
      rw [LinearEquiv.apply_symm_apply]
    rw [hy']
    exact Submodule.add_mem_sup (apply_mem_semilinearImage hm) (apply_mem_semilinearImage hn)
  · exact sup_le (semilinearImage_mono le_sup_left) (semilinearImage_mono le_sup_right)

theorem semilinearImage_span (s : Set E) :
    semilinearImage T hT (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) s) =
      Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (T '' s) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_semilinearImage_iff_exists.1 hy
    clear hy
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [_root_.map_zero]; exact Submodule.zero_mem _
    | add x z _ _ hx hz => rw [_root_.map_add]; exact Submodule.add_mem _ hx hz
    | smul a x _ hx =>
        obtain ⟨b, hb, hbx⟩ := hT.map_integer_smul a.2 x
        rw [integer_smul_eq, hbx]
        exact Submodule.smul_mem _ ⟨b, hb⟩ hx
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact apply_mem_semilinearImage (Submodule.subset_span hx)

theorem semilinearImage_fg (hM : M.FG) : (semilinearImage T hT M).FG := by
  classical
  obtain ⟨s, rfl⟩ := hM
  rw [semilinearImage_span, ← Finset.coe_image]
  exact ⟨_, rfl⟩

/-- The image `T W` of a subspace. -/
def semilinearSubspaceImage (T : (E ≃ₗ[ℤ] E)) (hT : IsUniformizerSemilinear (K := K) T)
    (W : Submodule (CompletedPseudoDiffOp K) E) : Submodule (CompletedPseudoDiffOp K) E where
  carrier := {y | T⁻¹ y ∈ W}
  add_mem' {x y} hx hy := by
    change T⁻¹ (x + y) ∈ W
    rw [_root_.map_add]
    exact W.add_mem hx hy
  zero_mem' := by
    change T⁻¹ 0 ∈ W
    rw [_root_.map_zero]
    exact W.zero_mem
  smul_mem' a y hy := by
    change T⁻¹ (a • y) ∈ W
    obtain ⟨ρ, _, hρ⟩ := hT.inv
    rw [hρ]
    exact W.smul_mem _ hy

theorem mem_semilinearSubspaceImage {W : Submodule (CompletedPseudoDiffOp K) E} {y : E} :
    y ∈ semilinearSubspaceImage T hT W ↔ T⁻¹ y ∈ W := Iff.rfl

theorem apply_mem_semilinearSubspaceImage {W : Submodule (CompletedPseudoDiffOp K) E} {x : E}
    (hx : x ∈ W) : T x ∈ semilinearSubspaceImage T hT W := by
  rw [mem_semilinearSubspaceImage]
  change T.symm (T x) ∈ W
  rwa [LinearEquiv.symm_apply_apply]

theorem semilinearImage_restrictScalars (W : Submodule (CompletedPseudoDiffOp K) E) :
    semilinearImage T hT (W.restrictScalars (CompletedPseudoDiffOpInteger (K := K))) =
      (semilinearSubspaceImage T hT W).restrictScalars (CompletedPseudoDiffOpInteger (K := K)) := by
  ext y
  rfl

theorem span_semilinearImage :
    Submodule.span (CompletedPseudoDiffOp K) (semilinearImage T hT M : Set E) =
      semilinearSubspaceImage T hT (Submodule.span (CompletedPseudoDiffOp K) (M : Set E)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro y hy
    rw [SetLike.mem_coe, mem_semilinearSubspaceImage]
    exact Submodule.subset_span hy
  · intro y hy
    rw [mem_semilinearSubspaceImage] at hy
    have hback : y = T (T⁻¹ y) := by
      change y = T (T.symm y)
      rw [LinearEquiv.apply_symm_apply]
    rw [hback]
    generalize T⁻¹ y = x at hy
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (apply_mem_semilinearImage hx)
    | zero => rw [_root_.map_zero]; exact Submodule.zero_mem _
    | add x z _ _ hx hz => rw [_root_.map_add]; exact Submodule.add_mem _ hx hz
    | smul a x _ hx =>
        obtain ⟨ρ, _, hρ⟩ := hT
        rw [hρ]
        exact Submodule.smul_mem _ _ hx

/-- A uniformizer-semilinear automorphism preserves the dimension of subspaces. -/
theorem finrank_semilinearSubspaceImage (W : Submodule (CompletedPseudoDiffOp K) E) :
    Module.finrank (CompletedPseudoDiffOp K) (semilinearSubspaceImage T hT W) =
      Module.finrank (CompletedPseudoDiffOp K) W := by
  obtain ⟨ρ, _, hρ⟩ := hT
  let j : W ≃+ semilinearSubspaceImage T ⟨ρ, ‹_›, hρ⟩ W :=
    { toFun := fun x => ⟨T x, apply_mem_semilinearSubspaceImage x.2⟩
      invFun := fun y => ⟨T⁻¹ y, y.2⟩
      left_inv := fun x => by
        ext
        change T.symm (T x) = x
        exact LinearEquiv.symm_apply_apply _ _
      right_inv := fun y => by
        ext
        change T (T.symm y) = y
        exact LinearEquiv.apply_symm_apply _ _
      map_add' := fun x y => by
        ext
        change T ((x : E) + y) = T x + T y
        exact _root_.map_add T _ _ }
  have hrank := rank_eq_of_equiv_equiv (R := CompletedPseudoDiffOp K)
    (R' := CompletedPseudoDiffOp K) ρ j ρ.bijective (fun a x => by
      ext
      exact hρ a x)
  unfold Module.finrank
  rw [hrank]

/-- An image contained in its source subspace is the whole subspace. -/
theorem semilinearSubspaceImage_eq_of_le [FiniteDimensional (CompletedPseudoDiffOp K) E]
    {W : Submodule (CompletedPseudoDiffOp K) E} (h : semilinearSubspaceImage T hT W ≤ W) :
    semilinearSubspaceImage T hT W = W :=
  Submodule.eq_of_le_of_finrank_eq h (finrank_semilinearSubspaceImage W)

/-- Forward-bounded vectors: the forward orbit stays in one finitely generated integral
submodule. -/
def IsForwardBounded (T : (E ≃ₗ[ℤ] E)) (x : E) : Prop :=
  ∃ M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E, M.FG ∧ ∀ n : ℕ, (T ^ n) x ∈ M

/-- The forward-bounded vectors of a uniformizer-semilinear automorphism form a subspace. -/
def forwardBoundedSubspace (T : (E ≃ₗ[ℤ] E)) (hT : IsUniformizerSemilinear (K := K) T) :
    Submodule (CompletedPseudoDiffOp K) E where
  carrier := {x | IsForwardBounded (K := K) T x}
  add_mem' {x y} hx hy := by
    obtain ⟨M, hM, hMx⟩ := hx
    obtain ⟨N, hN, hNy⟩ := hy
    refine ⟨M ⊔ N, hM.sup hN, fun n => ?_⟩
    rw [_root_.map_add]
    exact Submodule.add_mem_sup (hMx n) (hNy n)
  zero_mem' := ⟨⊥, Submodule.fg_bot, fun n => by rw [_root_.map_zero]; exact Submodule.zero_mem _⟩
  smul_mem' a x hx := by
    obtain ⟨M, hM, hMx⟩ := hx
    obtain ⟨t, ht⟩ := exists_uniformizer_left_scale_mem_integer a
    refine ⟨uniformizerDilate (-t) M, uniformizerDilate_fg _ hM, fun n => ?_⟩
    obtain ⟨ρ, hρ, hTρ⟩ := hT.pow n
    rw [hTρ, mem_uniformizerDilate, neg_neg, smul_smul]
    have hint : uniformizerZPow (K := K) t * ρ a ∈ CompletedPseudoDiffOpInteger (K := K) := by
      have := hρ.map_integer ht
      rwa [map_mul, hρ.map_uniformizerZPow] at this
    have := M.smul_mem ⟨_, hint⟩ (hMx n)
    rwa [integer_smul_eq] at this

theorem mem_forwardBoundedSubspace {x : E} :
    x ∈ forwardBoundedSubspace T hT ↔ IsForwardBounded (K := K) T x := Iff.rfl

theorem apply_mem_forwardBoundedSubspace {x : E} (hx : x ∈ forwardBoundedSubspace T hT) :
    T x ∈ forwardBoundedSubspace T hT := by
  obtain ⟨M, hM, hMx⟩ := hx
  refine ⟨M, hM, fun n => ?_⟩
  rw [← LinearEquiv.mul_apply, ← pow_succ]
  exact hMx (n + 1)

end

end DiffOp

end GaloisForLFunctions.HTGeometry
