import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Parity grading by an involution, and the block Gram determinant

An involution `J` on a real vector space splits it into its even and odd sectors,

```text
V = parityPlus J ⊕ parityMinus J,
```

and this module develops the consequences used by the rectangular Evans presentation.

* `isCompl_parity` — the splitting, with the explicit halves `(v ± J v)/2`.
* `inner_eq_zero_of_parity` — the two sectors are orthogonal whenever `J` is a self-adjoint isometry.
* `finrank_parityPlus_eq_finrank_parityMinus` — the sectors have **equal dimension** as soon as some
  linear automorphism `S` anticommutes with `J`; `S` carries one sector isomorphically onto the other.
* `map_parityPlus_le` / `map_parityMinus_le` and `ker_eq_bot_iff_parity` — an equivariant map is
  graded, and it is injective exactly when both graded blocks are.
* `det_eq_det_restrict_mul_det_restrict` — a `J`-commuting endomorphism has block-diagonal matrix, so
  its determinant is the product of the two sector determinants.  Applied to a Gram operator this is
  the parity factorization of the Gram determinant.
* `prodInvolution` and its sector computations — the graded excess target: with the reflection acting
  as `(x, y) ↦ (x, -y)` the even sector is the first factor and the odd sector the second, so a
  `2 + 1` split of a three-dimensional excess target has even dimension two and odd dimension one.
* `residualParity` and `finrank_residualParity_sectors` — the residual model
  `x^j e^x, x^j e^{-x}` for `0 ≤ j < L`, on which the reflection acts by `(-1)^j` times the branch
  swap: both sectors have dimension exactly `L`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Module

/-! ## Halving in a real vector space -/

theorem eq_zero_of_neg_eq {W : Type*} [AddCommGroup W] [Module ℝ W] {w : W} (h : -w = w) :
    w = 0 := by
  have hww : w + w = 0 := by
    calc w + w = -w + w := by rw [h]
      _ = 0 := neg_add_cancel w
  have h2 : (2 : ℝ) • w = 0 := by rw [two_smul]; exact hww
  rcases smul_eq_zero.mp h2 with hc | hw
  · norm_num at hc
  · exact hw

/-! ## The two parity sectors -/

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The even sector of an involution. -/
def parityPlus (J : V →ₗ[ℝ] V) : Submodule ℝ V := LinearMap.ker (J - LinearMap.id)

/-- The odd sector of an involution. -/
def parityMinus (J : V →ₗ[ℝ] V) : Submodule ℝ V := LinearMap.ker (J + LinearMap.id)

theorem mem_parityPlus {J : V →ₗ[ℝ] V} {v : V} : v ∈ parityPlus J ↔ J v = v := by
  simp [parityPlus, LinearMap.mem_ker, sub_eq_zero]

theorem mem_parityMinus {J : V →ₗ[ℝ] V} {v : V} : v ∈ parityMinus J ↔ J v = -v := by
  simp [parityMinus, LinearMap.mem_ker, add_eq_zero_iff_eq_neg]

theorem parityPlus_half_mem {J : V →ₗ[ℝ] V} (hJ : ∀ v, J (J v) = v) (v : V) :
    (2 : ℝ)⁻¹ • (v + J v) ∈ parityPlus J := by
  rw [mem_parityPlus, map_smul, map_add, hJ]
  rw [add_comm]

theorem parityMinus_half_mem {J : V →ₗ[ℝ] V} (hJ : ∀ v, J (J v) = v) (v : V) :
    (2 : ℝ)⁻¹ • (v - J v) ∈ parityMinus J := by
  rw [mem_parityMinus, map_smul, map_sub, hJ, ← smul_neg]
  congr 1
  abel

theorem parity_half_add {J : V →ₗ[ℝ] V} (v : V) :
    (2 : ℝ)⁻¹ • (v + J v) + (2 : ℝ)⁻¹ • (v - J v) = v := by
  rw [← smul_add]
  rw [show v + J v + (v - J v) = (2 : ℝ) • v from by rw [two_smul]; abel]
  rw [smul_smul]
  norm_num

/-- **The parity splitting.**  An involution decomposes the space into complementary even and odd
sectors. -/
theorem isCompl_parity {J : V →ₗ[ℝ] V} (hJ : ∀ v, J (J v) = v) :
    IsCompl (parityPlus J) (parityMinus J) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro v hv1 hv2
    rw [mem_parityPlus] at hv1
    rw [mem_parityMinus] at hv2
    exact eq_zero_of_neg_eq (hv2 ▸ hv1)
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    rw [← parity_half_add (J := J) v]
    exact Submodule.add_mem_sup (parityPlus_half_mem hJ v) (parityMinus_half_mem hJ v)

/-! ## Orthogonality of the sectors -/

/-- **The sectors are orthogonal** for a self-adjoint isometric reflection. -/
theorem inner_eq_zero_of_parity {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {J : V →ₗ[ℝ] V} (hJ : ∀ x y : V, inner ℝ (J x) (J y) = inner ℝ x y)
    {v w : V} (hv : v ∈ parityPlus J) (hw : w ∈ parityMinus J) : inner ℝ v w = 0 := by
  rw [mem_parityPlus] at hv
  rw [mem_parityMinus] at hw
  have h := hJ v w
  rw [hv, hw, inner_neg_right] at h
  linarith

/-! ## Equal dimension of the sectors -/

/-- An anticommuting automorphism maps the even sector onto the odd sector. -/
theorem map_parityPlus_eq_parityMinus {J : V →ₗ[ℝ] V} (S : V ≃ₗ[ℝ] V)
    (hS : ∀ v, S (J v) = -(J (S v))) :
    (parityPlus J).map (S : V →ₗ[ℝ] V) = parityMinus J := by
  apply le_antisymm
  · rintro w ⟨v, hv, rfl⟩
    have hv' : J v = v := mem_parityPlus.mp hv
    have hkey := hS v
    rw [hv'] at hkey
    exact mem_parityMinus.mpr (neg_eq_iff_eq_neg.mpr hkey).symm
  · intro w hw
    have hw' : J w = -w := mem_parityMinus.mp hw
    refine ⟨S.symm w, ?_, by simp⟩
    have hkey := hS (S.symm w)
    rw [S.apply_symm_apply, hw'] at hkey
    refine mem_parityPlus.mpr (S.injective ?_)
    rw [hkey, S.apply_symm_apply, neg_neg]

/-- **The two parity sectors have equal dimension** whenever some automorphism anticommutes with the
reflection. -/
theorem finrank_parityPlus_eq_finrank_parityMinus [FiniteDimensional ℝ V] {J : V →ₗ[ℝ] V}
    (S : V ≃ₗ[ℝ] V) (hS : ∀ v, S (J v) = -(J (S v))) :
    finrank ℝ (parityPlus J) = finrank ℝ (parityMinus J) := by
  have hiso := Submodule.equivMapOfInjective (S : V →ₗ[ℝ] V) S.injective (parityPlus J)
  rw [hiso.finrank_eq, map_parityPlus_eq_parityMinus S hS]

/-- **Both sectors have half the dimension.** -/
theorem finrank_parityPlus_eq_half [FiniteDimensional ℝ V] {J : V →ₗ[ℝ] V}
    (hJ : ∀ v, J (J v) = v) (S : V ≃ₗ[ℝ] V) (hS : ∀ v, S (J v) = -(J (S v))) :
    2 * finrank ℝ (parityPlus J) = finrank ℝ V := by
  have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_parity hJ)
  have heq := finrank_parityPlus_eq_finrank_parityMinus S hS
  omega

/-! ## Graded equivariant maps -/

theorem map_parityPlus_le {J : V →ₗ[ℝ] V} {K : W →ₗ[ℝ] W} (M : V →ₗ[ℝ] W)
    (hM : ∀ v, M (J v) = K (M v)) : (parityPlus J).map M ≤ parityPlus K := by
  rintro w ⟨v, hv, rfl⟩
  have hv' : J v = v := mem_parityPlus.mp hv
  exact mem_parityPlus.mpr (by rw [← hM, hv'])

theorem map_parityMinus_le {J : V →ₗ[ℝ] V} {K : W →ₗ[ℝ] W} (M : V →ₗ[ℝ] W)
    (hM : ∀ v, M (J v) = K (M v)) : (parityMinus J).map M ≤ parityMinus K := by
  rintro w ⟨v, hv, rfl⟩
  have hv' : J v = -v := mem_parityMinus.mp hv
  exact mem_parityMinus.mpr (by rw [← hM, hv', map_neg])

/-- **The kernel splits.**  An equivariant map is injective exactly when it is injective on each
parity sector. -/
theorem ker_eq_bot_iff_parity {J : V →ₗ[ℝ] V} {K : W →ₗ[ℝ] W}
    (hJ : ∀ v, J (J v) = v) (M : V →ₗ[ℝ] W) (hM : ∀ v, M (J v) = K (M v)) :
    LinearMap.ker M = ⊥ ↔
      ((∀ v ∈ parityPlus J, M v = 0 → v = 0) ∧ ∀ v ∈ parityMinus J, M v = 0 → v = 0) := by
  constructor
  · intro h
    refine ⟨fun v _ hv => ?_, fun v _ hv => ?_⟩
    · exact (Submodule.mem_bot ℝ).mp (h ▸ (LinearMap.mem_ker.mpr hv))
    · exact (Submodule.mem_bot ℝ).mp (h ▸ (LinearMap.mem_ker.mpr hv))
  · rintro ⟨hp, hm⟩
    rw [LinearMap.ker_eq_bot']
    intro v hv
    set p : V := (2 : ℝ)⁻¹ • (v + J v) with hpdef
    set q : V := (2 : ℝ)⁻¹ • (v - J v) with hqdef
    have hpmem : p ∈ parityPlus J := parityPlus_half_mem hJ v
    have hqmem : q ∈ parityMinus J := parityMinus_half_mem hJ v
    have hsum : p + q = v := parity_half_add (J := J) v
    have hMsum : M p + M q = 0 := by rw [← map_add, hsum, hv]
    have hKp : K (M p) = M p := mem_parityPlus.mp (map_parityPlus_le M hM ⟨p, hpmem, rfl⟩)
    have hKq : K (M q) = -M q := mem_parityMinus.mp (map_parityMinus_le M hM ⟨q, hqmem, rfl⟩)
    have hdiff : M p - M q = 0 := by
      have hK := congrArg K hMsum
      rw [map_add, hKp, hKq, map_zero, ← sub_eq_add_neg] at hK
      exact hK
    have hMp : M p = 0 := by
      have h2 : (2 : ℝ) • M p = 0 := by
        rw [two_smul, show M p + M p = M p + M q + (M p - M q) from by abel, hMsum, hdiff]
        simp
      rcases smul_eq_zero.mp h2 with hc | h
      · norm_num at hc
      · exact h
    have hMq : M q = 0 := by
      rw [hMp, zero_add] at hMsum
      exact hMsum
    rw [← hsum, hp p hpmem hMp, hm q hqmem hMq, add_zero]

/-- A reflection-commuting endomorphism preserves the even sector. -/
theorem mapsTo_parityPlus_of_commute {J G : V →ₗ[ℝ] V} (hG : ∀ v, G (J v) = J (G v)) :
    ∀ v ∈ parityPlus J, G v ∈ parityPlus J :=
  fun v hv => map_parityPlus_le G hG ⟨v, hv, rfl⟩

/-- A reflection-commuting endomorphism preserves the odd sector. -/
theorem mapsTo_parityMinus_of_commute {J G : V →ₗ[ℝ] V} (hG : ∀ v, G (J v) = J (G v)) :
    ∀ v ∈ parityMinus J, G v ∈ parityMinus J :=
  fun v hv => map_parityMinus_le G hG ⟨v, hv, rfl⟩

/-! ## The block determinant -/

/-- **Parity factorization of the determinant.**  A reflection-commuting endomorphism has
block-diagonal matrix in a parity-adapted basis, so its determinant factors. -/
theorem det_eq_det_restrict_mul_det_restrict [FiniteDimensional ℝ V] {J : V →ₗ[ℝ] V}
    (hJ : ∀ v, J (J v) = v) (G : V →ₗ[ℝ] V)
    (hp : ∀ v ∈ parityPlus J, G v ∈ parityPlus J)
    (hm : ∀ v ∈ parityMinus J, G v ∈ parityMinus J) :
    G.det = (G.restrict hp).det * (G.restrict hm).det := by
  classical
  set e := Submodule.prodEquivOfIsCompl (parityPlus J) (parityMinus J) (isCompl_parity hJ) with he
  have hcomm : ((e : (parityPlus J × parityMinus J) →ₗ[ℝ] V) ∘ₗ
      LinearMap.prodMap (G.restrict hp) (G.restrict hm))
      = G ∘ₗ (e : (parityPlus J × parityMinus J) →ₗ[ℝ] V) := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.prodMap_apply, he, Submodule.coe_prodEquivOfIsCompl',
      LinearMap.coe_restrict_apply, map_add]
  have hee : ((e : (parityPlus J × parityMinus J) →ₗ[ℝ] V) ∘ₗ (e.symm : V →ₗ[ℝ] _))
      = LinearMap.id := by
    apply LinearMap.ext
    intro v
    simp
  have hconj : (e : (parityPlus J × parityMinus J) →ₗ[ℝ] V) ∘ₗ
      (LinearMap.prodMap (G.restrict hp) (G.restrict hm)) ∘ₗ (e.symm : V →ₗ[ℝ] _) = G := by
    rw [← LinearMap.comp_assoc, hcomm, LinearMap.comp_assoc, hee, LinearMap.comp_id]
  calc G.det
      = LinearMap.det ((e : (parityPlus J × parityMinus J) →ₗ[ℝ] V) ∘ₗ
          (LinearMap.prodMap (G.restrict hp) (G.restrict hm)) ∘ₗ (e.symm : V →ₗ[ℝ] _)) := by
        rw [hconj]
    _ = LinearMap.det (LinearMap.prodMap (G.restrict hp) (G.restrict hm)) :=
        LinearMap.det_conj _ e
    _ = (G.restrict hp).det * (G.restrict hm).det := LinearMap.det_prodMap _ _

/-! ## The graded excess target -/

/-- The reflection of a graded target: identity on the even factor, negation on the odd factor. -/
def prodInvolution (Weven Wodd : Type*) [AddCommGroup Weven] [Module ℝ Weven] [AddCommGroup Wodd]
    [Module ℝ Wodd] : (Weven × Wodd) →ₗ[ℝ] (Weven × Wodd) :=
  LinearMap.prodMap LinearMap.id (-LinearMap.id)

theorem prodInvolution_apply {Weven Wodd : Type*} [AddCommGroup Weven] [Module ℝ Weven] [AddCommGroup Wodd]
    [Module ℝ Wodd] (p : Weven × Wodd) : prodInvolution Weven Wodd p = (p.1, -p.2) := rfl

theorem prodInvolution_involutive {Weven Wodd : Type*} [AddCommGroup Weven] [Module ℝ Weven]
    [AddCommGroup Wodd] [Module ℝ Wodd] (p : Weven × Wodd) :
    prodInvolution Weven Wodd (prodInvolution Weven Wodd p) = p := by
  simp [prodInvolution_apply]

theorem parityPlus_prodInvolution (Weven Wodd : Type*) [AddCommGroup Weven] [Module ℝ Weven]
    [AddCommGroup Wodd] [Module ℝ Wodd] :
    parityPlus (prodInvolution Weven Wodd) = Submodule.fst ℝ Weven Wodd := by
  ext p
  have hmem : p ∈ Submodule.fst ℝ Weven Wodd ↔ p.2 = 0 := by simp [Submodule.fst]
  rw [mem_parityPlus, hmem, prodInvolution_apply, Prod.ext_iff]
  constructor
  · intro h
    exact eq_zero_of_neg_eq h.2
  · intro h
    refine ⟨rfl, ?_⟩
    rw [h, neg_zero]

theorem parityMinus_prodInvolution (Weven Wodd : Type*) [AddCommGroup Weven] [Module ℝ Weven]
    [AddCommGroup Wodd] [Module ℝ Wodd] :
    parityMinus (prodInvolution Weven Wodd) = Submodule.snd ℝ Weven Wodd := by
  ext p
  have hmem : p ∈ Submodule.snd ℝ Weven Wodd ↔ p.1 = 0 := by simp [Submodule.snd]
  rw [mem_parityMinus, hmem, prodInvolution_apply, Prod.ext_iff]
  simp only [Prod.fst_neg, Prod.snd_neg]
  constructor
  · intro h
    exact eq_zero_of_neg_eq h.1.symm
  · intro h
    refine ⟨?_, trivial⟩
    rw [h]
    simp

/-- **The graded excess target: the even sector has the dimension of the even factor.**  With two
even channels and one odd channel this reads `2` and `1`. -/
theorem finrank_parityPlus_prodInvolution (Weven Wodd : Type*) [AddCommGroup Weven] [Module ℝ Weven]
    [AddCommGroup Wodd] [Module ℝ Wodd] :
    finrank ℝ (parityPlus (prodInvolution Weven Wodd)) = finrank ℝ Weven := by
  rw [parityPlus_prodInvolution]
  exact (Submodule.fstEquiv ℝ Weven Wodd).finrank_eq

theorem finrank_parityMinus_prodInvolution (Weven Wodd : Type*) [AddCommGroup Weven] [Module ℝ Weven]
    [AddCommGroup Wodd] [Module ℝ Wodd] :
    finrank ℝ (parityMinus (prodInvolution Weven Wodd)) = finrank ℝ Wodd := by
  rw [parityMinus_prodInvolution]
  exact (Submodule.sndEquiv ℝ Weven Wodd).finrank_eq

/-- The three-channel excess target of the rectangular Evans presentation: two even channels — the
mean and the affine constant — and one odd channel, the affine slope. -/
theorem finrank_evansExcess_parityPlus :
    finrank ℝ (parityPlus (prodInvolution (ℝ × ℝ) ℝ)) = 2 := by
  rw [finrank_parityPlus_prodInvolution]
  simp

theorem finrank_evansExcess_parityMinus :
    finrank ℝ (parityMinus (prodInvolution (ℝ × ℝ) ℝ)) = 1 := by
  rw [finrank_parityMinus_prodInvolution]
  simp

/-! ## The residual model -/

/-- The reflection on the residual model with basis `x^j e^x`, `x^j e^{-x}` for `0 ≤ j < L`:
it multiplies by `(-1)^j` and swaps the two exponential branches. -/
def residualParity (L : ℕ) : (Fin L × Bool → ℝ) →ₗ[ℝ] (Fin L × Bool → ℝ) where
  toFun f := fun p => (-1 : ℝ) ^ (p.1 : ℕ) * f (p.1, !p.2)
  map_add' f g := by funext p; simp [mul_add]
  map_smul' c f := by funext p; simp [smul_eq_mul]; ring

theorem residualParity_apply (L : ℕ) (f : Fin L × Bool → ℝ) (p : Fin L × Bool) :
    residualParity L f p = (-1 : ℝ) ^ (p.1 : ℕ) * f (p.1, !p.2) := rfl

theorem residualParity_involutive (L : ℕ) (f : Fin L × Bool → ℝ) :
    residualParity L (residualParity L f) = f := by
  funext p
  rw [residualParity_apply, residualParity_apply]
  have hsq : ((-1 : ℝ) ^ (p.1 : ℕ)) * ((-1 : ℝ) ^ (p.1 : ℕ)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  simp only [Bool.not_not]
  rw [← mul_assoc, hsq, one_mul]

/-- The sign of an exponential branch. -/
def boolSign : Bool → ℝ := fun b => if b then 1 else -1

theorem boolSign_mul_self (b : Bool) : boolSign b * boolSign b = 1 := by
  cases b <;> simp [boolSign]

theorem boolSign_not (b : Bool) : boolSign (!b) = -boolSign b := by
  cases b <;> simp [boolSign]

/-- The branch-sign map of the residual model: `+1` on one exponential branch and `-1` on the
other.  It anticommutes with the reflection. -/
def residualBranch (L : ℕ) : (Fin L × Bool → ℝ) →ₗ[ℝ] (Fin L × Bool → ℝ) where
  toFun f := fun p => boolSign p.2 * f p
  map_add' f g := by funext p; simp [mul_add]
  map_smul' c f := by funext p; simp [smul_eq_mul]; ring

theorem residualBranch_apply (L : ℕ) (f : Fin L × Bool → ℝ) (p : Fin L × Bool) :
    residualBranch L f p = boolSign p.2 * f p := rfl

theorem residualBranch_involutive (L : ℕ) (f : Fin L × Bool → ℝ) :
    residualBranch L (residualBranch L f) = f := by
  funext p
  rw [residualBranch_apply, residualBranch_apply, ← mul_assoc, boolSign_mul_self, one_mul]

/-- The branch-sign map as an automorphism. -/
def residualBranchEquiv (L : ℕ) : (Fin L × Bool → ℝ) ≃ₗ[ℝ] (Fin L × Bool → ℝ) :=
  LinearEquiv.ofLinear (residualBranch L) (residualBranch L)
    (LinearMap.ext fun f => residualBranch_involutive L f)
    (LinearMap.ext fun f => residualBranch_involutive L f)

theorem residualBranchEquiv_apply (L : ℕ) (f : Fin L × Bool → ℝ) :
    residualBranchEquiv L f = residualBranch L f := rfl

/-- The branch sign anticommutes with the reflection. -/
theorem residualBranch_anticommutes (L : ℕ) (f : Fin L × Bool → ℝ) :
    residualBranchEquiv L (residualParity L f)
      = -(residualParity L (residualBranchEquiv L f)) := by
  funext p
  simp only [residualBranchEquiv_apply, residualBranch_apply, residualParity_apply,
    Pi.neg_apply, boolSign_not]
  ring

/-- **The residual model splits into equal parity halves of dimension `L`.**  This is the
`dim F^+ = dim F^- = L_a` statement for the reflection-invariant residual space spanned by
`x^j e^x, x^j e^{-x}`, `0 ≤ j < L`. -/
theorem finrank_residualParity_parityPlus (L : ℕ) :
    finrank ℝ (parityPlus (residualParity L)) = L := by
  have hhalf := finrank_parityPlus_eq_half (residualParity_involutive L)
    (residualBranchEquiv L) (residualBranch_anticommutes L)
  have hdim : finrank ℝ (Fin L × Bool → ℝ) = L * 2 := by
    rw [finrank_pi ℝ]
    simp
  rw [hdim] at hhalf
  omega

theorem finrank_residualParity_parityMinus (L : ℕ) :
    finrank ℝ (parityMinus (residualParity L)) = L := by
  rw [← finrank_parityPlus_eq_finrank_parityMinus (residualBranchEquiv L)
    (residualBranch_anticommutes L)]
  exact finrank_residualParity_parityPlus L

end GaloisForLFunctions.RHTower

end
