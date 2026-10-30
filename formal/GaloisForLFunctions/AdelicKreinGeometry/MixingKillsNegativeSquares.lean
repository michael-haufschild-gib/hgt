import GaloisForLFunctions.AdelicKreinGeometry.HeckeSupportedStatesHaveIndexZeroOrInfinity
import GaloisForLFunctions.HeckeKreinToeplitz.BoundedIndexIsClosedUnderPointwiseLimits

/-!
# Mixing kills negative squares

An indefinite Howe–Moore theorem. Howe–Moore says that matrix coefficients of irreducible unitary
representations of simple groups vanish at infinity. In the indefinite theory decay at infinity
does not constrain the coefficients; it constrains the index.

* **Block additivity** (`hermNegIndex_add_le_fromBlocks`): a block-diagonal Hermitian matrix has at
  least the negative squares of both blocks.
* **Approximate escape** (`negIndex_eq_zero_of_tendsto_escape`). Suppose every pair of finite
  families `x, y` admits translates `t_j` with `k(x_a⁻¹ t_j y_b) → 0`. If `κ(k) < ∞`, a witness
  family `x` and any family `y` give Gram matrices on `x ⊔ t_j y` that converge to the block
  diagonal of `x` and `y`. Lower semicontinuity of the index gives `κ + ν(y) ≤ κ`, so `ν(y) = 0`:
  the kernel is positive. Exact escape (`negIndex_eq_zero_of_escape`) is the constant case.
* **Mixing kernels** (`negIndex_eq_zero_or_top_of_mixing`): if one sequence `t_j` makes every
  two-sided translate `k(g t_j h)` tend to zero, then `κ(k) ∈ {0, ∞}`. On `ℤ`: every Hermitian
  kernel vanishing at infinity (`negIndex_eq_zero_or_top_of_tendsto_int`).
* **On `Aff(ℚ)`** (`negIndex_eq_zero_or_top_of_heightDecay`): a Hermitian function that decays with
  the height `|num a|·den a` of the slope has index `0` or `∞`. The escape runs along the
  dilations `x ↦ 2^j x`; the height is submultiplicative (`slopeHeight_mul_le`), so the slopes of
  `g · 2^j · h` grow. The Hecke states decay for `s > 0`, which gives the index wall a second,
  mixing proof.

A Pontryagin state with a finite nonzero number of negative squares is therefore never mixing. Its
negative squares need a carrier that does not decay along any escape: over `ℚ` this is the
archimedean place, where the orbit kernels are continuous in `log a` and every height is reached
near `a = 1`.
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-! ### Block-diagonal matrices -/

theorem hermQuad_fromBlocks_diag {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℂ)
    (B : Matrix κ κ ℂ) (w : ι → ℂ) (c : κ → ℂ) :
    hermQuad (Matrix.fromBlocks A 0 0 B) (Sum.elim w c) = hermQuad A w + hermQuad B c := by
  simp only [hermQuad, ← Complex.add_re]
  congr 1
  simp [Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]

/-- **Block additivity of negative squares.** -/
theorem hermNegIndex_add_le_fromBlocks {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    hermNegIndex A + hermNegIndex B ≤ hermNegIndex (Matrix.fromBlocks A 0 0 B) := by
  obtain ⟨WA, hrA, hWA⟩ := exists_isPosDefOn_finrank_eq_posIndex (-A)
  obtain ⟨WB, hrB, hWB⟩ := exists_isPosDefOn_finrank_eq_posIndex (-B)
  set rA := Module.finrank ℂ WA
  set rB := Module.finrank ℂ WB
  set bA := Module.finBasis ℂ WA
  set bB := Module.finBasis ℂ WB
  have hA : hermNegIndex A = rA := hrA.symm
  have hB : hermNegIndex B = rB := hrB.symm
  have hA0 : ∀ w : WA, hermQuad A w ≤ 0 := fun w => by
    by_cases hw : (w : ι → ℂ) = 0
    · rw [hw]; simp [hermQuad]
    · have := hWA w w.2 hw
      rw [hermQuad_neg] at this
      linarith
  have hB0 : ∀ w : WB, hermQuad B w ≤ 0 := fun w => by
    by_cases hw : (w : κ → ℂ) = 0
    · rw [hw]; simp [hermQuad]
    · have := hWB w w.2 hw
      rw [hermQuad_neg] at this
      linarith
  have hA1 : ∀ w : WA, (w : ι → ℂ) ≠ 0 → hermQuad A w < 0 := fun w hw => by
    have := hWA w w.2 hw
    rw [hermQuad_neg] at this
    linarith
  have hB1 : ∀ w : WB, (w : κ → ℂ) ≠ 0 → hermQuad B w < 0 := fun w hw => by
    have := hWB w w.2 hw
    rw [hermQuad_neg] at this
    linarith
  set wA : (Fin rA ⊕ Fin rB → ℂ) → WA := fun β => ∑ i, β (Sum.inl i) • bA i
  set wB : (Fin rA ⊕ Fin rB → ℂ) → WB := fun β => ∑ j, β (Sum.inr j) • bB j
  let L : (Fin rA ⊕ Fin rB → ℂ) →ₗ[ℂ] (ι ⊕ κ → ℂ) :=
    { toFun := fun β => Sum.elim (fun a => ∑ i, β (Sum.inl i) * ((bA i : WA) : ι → ℂ) a)
        (fun b => ∑ j, β (Sum.inr j) * ((bB j : WB) : κ → ℂ) b)
      map_add' := fun β β' => by
        funext p
        cases p <;> simp [add_mul, sum_add_distrib]
      map_smul' := fun t β => by
        funext p
        cases p <;> simp [mul_assoc, mul_sum] }
  have hL : ∀ β, L β = Sum.elim ((wA β : WA) : ι → ℂ) ((wB β : WB) : κ → ℂ) := fun β => by
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, wA, wB]
    congr 1 <;> funext a <;> simp [Finset.sum_apply]
  have hneg : ∀ β, β ≠ 0 → hermQuad (Matrix.fromBlocks A 0 0 B) (L β) < 0 := by
    intro β hβ
    rw [hL, hermQuad_fromBlocks_diag]
    obtain ⟨p, hp⟩ : ∃ p, β p ≠ 0 := by
      by_contra h
      push Not at h
      exact hβ (funext h)
    cases p with
    | inl i =>
      have hw : ((wA β : WA) : ι → ℂ) ≠ 0 := fun h0 => hp
        (Fintype.linearIndependent_iff.mp bA.linearIndependent (fun i => β (Sum.inl i))
          (Subtype.ext h0) i)
      linarith [hA1 _ hw, hB0 (wB β)]
    | inr j =>
      have hw : ((wB β : WB) : κ → ℂ) ≠ 0 := fun h0 => hp
        (Fintype.linearIndependent_iff.mp bB.linearIndependent (fun j => β (Sum.inr j))
          (Subtype.ext h0) j)
      linarith [hB1 _ hw, hA0 (wA β)]
  have h := card_le_hermNegIndex_of_forall_neg _ L hneg
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
  rw [hA, hB]
  exact h

/-! ### Approximate escape -/

variable {G : Type*} [Group G]

/-- **Approximate escape.** If every pair of finite families has translates along which the kernel
between them tends to zero, a finite index is zero. -/
theorem negIndex_eq_zero_of_tendsto_escape {k : G → ℂ} (hk : IsHermKernel k)
    (hfin : negIndex k < ⊤)
    (hesc : ∀ (m n : ℕ) (x : Fin m → G) (y : Fin n → G), ∃ t : ℕ → G,
      ∀ a b, Tendsto (fun j => k ((x a)⁻¹ * (t j * y b))) atTop (𝓝 0)) :
    negIndex k = 0 := by
  classical
  obtain ⟨m, x, hx⟩ := exists_isWitness hfin
  refine nonpos_iff_eq_zero.mp (negIndex_le_iff.mpr fun n y => ?_)
  obtain ⟨t, ht⟩ := hesc m n x y
  set H : ℕ → Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun j => gram k (Sum.elim x fun b => t j * y b)
  set H₀ : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ := Matrix.fromBlocks (gram k x) 0 0 (gram k y)
  have hH₀ : H₀.IsHermitian :=
    (gram_isHermitian hk x).fromBlocks (by simp) (gram_isHermitian hk y)
  have hconv : ∀ i i', Tendsto (fun j => H j i i') atTop (𝓝 (H₀ i i')) := by
    rintro (a | b) (a' | b')
    · simp [H, H₀, gram]
    · simpa [H, H₀, gram] using ht a b'
    · have hc := ((Complex.continuous_conj.tendsto 0).comp (ht a' b))
      rw [map_zero] at hc
      refine hc.congr fun j => ?_
      simp only [Function.comp_apply, H, gram, Sum.elim_inr, Sum.elim_inl]
      rw [← hk, mul_inv_rev, inv_inv]
    · simp only [H, H₀, gram, Sum.elim_inr, Matrix.fromBlocks_apply₂₂]
      have e : ∀ j, (t j * y b)⁻¹ * (t j * y b') = (y b)⁻¹ * y b' := fun j => by group
      simp only [e]
      exact tendsto_const_nhds
  obtain ⟨j, hj⟩ := (eventually_le_hermNegIndex hH₀ hconv).exists
  have h1 := (hermNegIndex_add_le_fromBlocks (gram k x) (gram k y)).trans hj
  have h2 := hermNegIndex_gram_le_negIndex k (Sum.elim x fun b => t j * y b)
  rw [← hx] at h2
  have h3 : hermNegIndex (gram k x) + hermNegIndex (gram k y) ≤ hermNegIndex (gram k x) := by
    exact_mod_cast (Nat.cast_le.mpr h1).trans h2
  have h4 : hermNegIndex (gram k y) = 0 := by omega
  rw [h4]
  rfl

/-- **Mixing kills negative squares.** If one sequence `t_j` makes every two-sided translate of the
kernel tend to zero, the index is `0` or `∞`. -/
theorem negIndex_eq_zero_or_top_of_mixing {k : G → ℂ} (hk : IsHermKernel k) {t : ℕ → G}
    (ht : ∀ g h, Tendsto (fun j => k (g * t j * h)) atTop (𝓝 0)) :
    negIndex k = 0 ∨ negIndex k = ⊤ := by
  rcases eq_or_ne (negIndex k) ⊤ with h | h
  · exact Or.inr h
  · refine Or.inl (negIndex_eq_zero_of_tendsto_escape hk (lt_top_iff_ne_top.mpr h)
      fun _ _ x y => ⟨t, fun a b => ?_⟩)
    simpa [mul_assoc] using ht (x a)⁻¹ (y b)

/-- On `ℤ`: a Hermitian kernel vanishing at `+∞` has index `0` or `∞`. -/
theorem negIndex_eq_zero_or_top_of_tendsto_int {k : Multiplicative ℤ → ℂ} (hk : IsHermKernel k)
    (h0 : Tendsto (fun n : ℤ => k (Multiplicative.ofAdd n)) atTop (𝓝 0)) :
    negIndex k = 0 ∨ negIndex k = ⊤ := by
  refine negIndex_eq_zero_or_top_of_mixing hk (t := fun j => Multiplicative.ofAdd (j : ℤ))
    fun g h => ?_
  have hlim : Tendsto (fun j : ℕ => (j : ℤ) + (Multiplicative.toAdd g + Multiplicative.toAdd h))
      atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  refine (h0.comp hlim).congr fun j => ?_
  simp only [Function.comp_apply]
  congr 1
  apply Multiplicative.toAdd.injective
  simp only [toAdd_ofAdd, toAdd_mul]
  ring

/-! ### Height decay on the affine group -/

/-- The height `|num a|·den a` of the slope of `x ↦ ax + b`. -/
def slopeHeight (g : AffineGroupQ) : ℕ := (affSlope g).num.natAbs * (affSlope g).den

/-- The height of a product of rationals is at most the product of the heights. -/
theorem ratHeight_mul_le (q r : ℚ) :
    (q * r).num.natAbs * (q * r).den ≤ (q.num.natAbs * q.den) * (r.num.natAbs * r.den) := by
  have hnum : (q * r).num.natAbs ≤ q.num.natAbs * r.num.natAbs := by
    have h := Int.abs_ediv_le_abs (q.num * r.num) (Nat.gcd (q.num * r.num).natAbs (q.den * r.den))
    rw [← Rat.mul_num] at h
    have h' : ((q * r).num.natAbs : ℤ) ≤ ((q.num.natAbs * r.num.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, Nat.cast_mul, Int.natCast_natAbs, Int.natCast_natAbs, ← abs_mul]
      exact h
    exact_mod_cast h'
  have hden : (q * r).den ≤ q.den * r.den :=
    Nat.le_of_dvd (Nat.mul_pos q.den_pos r.den_pos) (Rat.mul_den_dvd q r)
  calc (q * r).num.natAbs * (q * r).den ≤ (q.num.natAbs * r.num.natAbs) * (q.den * r.den) :=
        Nat.mul_le_mul hnum hden
    _ = (q.num.natAbs * q.den) * (r.num.natAbs * r.den) := by ring

theorem slopeHeight_mul_le (g h : AffineGroupQ) :
    slopeHeight (g * h) ≤ slopeHeight g * slopeHeight h := by
  unfold slopeHeight
  rw [affSlope_mul]
  exact ratHeight_mul_le _ _

/-- A function on `Aff(ℚ)` **decays with the height** of the slope. -/
def HasHeightDecay (φ : AffineGroupQ → ℂ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ g, N ≤ slopeHeight g → ‖φ g‖ ≤ ε

/-- The doubling dilations `x ↦ 2^j x`. -/
def doubling (j : ℕ) : AffineGroupQ := dilation (Units.mk0 (2 : ℚ) two_ne_zero ^ j)

/-- Two-sided translates by the doubling dilations have slopes of height at least `2^j/C`. -/
theorem pow_le_mul_slopeHeight (g h : AffineGroupQ) (j : ℕ) :
    2 ^ j ≤ (((affSlope g * affSlope h)⁻¹).num.natAbs * ((affSlope g * affSlope h)⁻¹).den) *
      slopeHeight (g * doubling j * h) := by
  have hmul := ratHeight_mul_le ((affSlope g * affSlope h)⁻¹) (affSlope (g * doubling j * h))
  have hg := affSlope_ne_zero g
  have hh := affSlope_ne_zero h
  have e : (affSlope g * affSlope h)⁻¹ * affSlope (g * doubling j * h) = ((2 ^ j : ℕ) : ℚ) := by
    rw [affSlope_mul, affSlope_mul, doubling, affSlope_dilation, Units.val_pow_eq_pow_val,
      Units.val_mk0]
    push_cast
    field_simp
  rw [e, Rat.num_natCast, Rat.den_natCast] at hmul
  simpa [slopeHeight] using hmul

/-- **Height decay kills negative squares.** A Hermitian function on `Aff(ℚ)` that decays with the
height of the slope has index `0` or `∞`. -/
theorem negIndex_eq_zero_or_top_of_heightDecay {φ : AffineGroupQ → ℂ} (hk : IsHermKernel φ)
    (hφ : HasHeightDecay φ) : negIndex φ = 0 ∨ negIndex φ = ⊤ := by
  refine negIndex_eq_zero_or_top_of_mixing hk (t := doubling) fun g h => ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hφ (ε / 2) (half_pos hε)
  set q := (affSlope g * affSlope h)⁻¹
  set C := q.num.natAbs * q.den
  have hC : 0 < C := Nat.mul_pos (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr
    (inv_ne_zero (mul_ne_zero (affSlope_ne_zero g) (affSlope_ne_zero h))))) q.den_pos
  refine ⟨C * N, fun j hj => ?_⟩
  have hheight : N ≤ slopeHeight (g * doubling j * h) := by
    by_contra hlt
    push Not at hlt
    have h1 : 2 ^ j ≤ C * slopeHeight (g * doubling j * h) := pow_le_mul_slopeHeight g h j
    have h2 : C * N ≤ 2 ^ j := hj.trans (Nat.lt_two_pow_self).le
    have h3 : C * slopeHeight (g * doubling j * h) < C * N := Nat.mul_lt_mul_of_pos_left hlt hC
    omega
  rw [dist_zero_right]
  linarith [hN _ hheight]

/-- The Hecke states decay with the height for `s > 0`. -/
theorem hasHeightDecay_heckeState {s : ℝ} (hs : 0 < s) : HasHeightDecay (heckeState s) := by
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ) ^ (-s))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hlim.eventually (ge_mem_nhds hε))
  refine ⟨N, fun g hg => ?_⟩
  have hb := hN _ hg
  unfold heckeState
  split_ifs
  · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    simpa [slopeHeight] using hb
  · simpa using hε.le

/-- **The index wall, by mixing.** Below the critical line the Hecke states have infinite index. -/
theorem negIndex_heckeState_eq_top_of_mixing {s : ℝ} (hs : 0 < s) (hlt : s < 1 / 2) :
    negIndex (heckeState s) = ⊤ := by
  rcases negIndex_eq_zero_or_top_of_heightDecay (isHermKernel_heckeState s)
    (hasHeightDecay_heckeState hs) with h | h
  · exact absurd ((isPosDefOnGroup_heckeState_iff s).mp (isPosDefKernel_iff_isPosDefOnGroup.mp
      ((isPosDefKernel_iff (isHermKernel_heckeState s)).mpr h))) (not_le.mpr hlt)
  · exact h

end GaloisForLFunctions.AdelicKreinGeometry
