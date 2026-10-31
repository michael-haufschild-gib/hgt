import GaloisForLFunctions.AdelicKreinGeometry.ConformalSymmetryNeedsANegativeSquare
import GaloisForLFunctions.AdelicKreinGeometry.StableConformalSuccessors
import GaloisForLFunctions.AdelicKreinGeometry.TheAffineGroupOfAField

/-!
# The Hecke boost and the conformal successor are one state

Let `K` be a field and `v` an absolute value of `K` (a place). A successor `ψ` on `K` is
**conformal of exponent `s`** if `ψ(ub) = |u|_v^s ψ(b)`. Points of `ℙ¹(K)` then carry vectors `k_t`
(`t ∈ K`) and `k_∞` with

  `[k_s, k_t] = ψ(t − s)`,  `[k_∞, k_t] = 1`,  `[k_∞, k_∞] = 0`,

and `x ↦ ax + b` acts isometrically by `k_t ↦ |a|_v^{−s/2} k_{at+b}`, `k_∞ ↦ |a|_v^{s/2} k_∞`: the
dilations are boosts with eigenvalues `|a|_v^{∓s/2}` at the fixed points `0` and `∞`.

* **Conformal induction** (`negIndex_conformalInduction`): the coefficient at `k_0`,
  `Φ_ψ(x ↦ ax + b) = |a|_v^{−s/2} ψ(b)`, is a state of `Aff(K)` with `κ(Φ_ψ) = κ(ψ)`; its Gram
  matrices are diagonal congruences of those of `ψ` (`hermQuad_gram_conformalInduction`).
* **The pole–successor state** (`negIndex_poleSuccessor`): the coefficient at `k_0 + k_∞`,
  `|a|_v^{s/2} + |a|_v^{−s/2} + |a|_v^{−s/2} ψ(b)`, has Gram form `2 Re(X̄Y)` plus the form of `ψ`
  with total mass `X` (`hermQuad_gram_poleSuccessor`). For a nontrivial `v` and a conditionally
  positive `ψ` it has exactly one negative square.
* **Two actions in one state** (`poleSuccessor_dilation`, `poleSuccessor_translation`): on the
  dilations it is the boost pair `|u|_v^{s/2} + |u|_v^{−s/2}`, on the translations the successor
  `2 + ψ(b)`.
* **The real place**: `−c|b|` with `s = 1` (`negIndex_poleSuccessorState`), with the Hecke boost
  `|u|^{1/2} + |u|^{−1/2}`, the pole pair of Weil's kernel; `−c|b|^s` for `0 < s < 1`
  (`negIndex_poleSuccessor_negPowRat`).

So the boost on `K^×` and the conformal successor on `K` are the two readings of one index-one state
of `Aff(K)`, and the boost exponent is half the conformal exponent, as forced by
`dil_u ∘ trans_b ∘ dil_u⁻¹ = trans_{ub}`. The Hecke normalization `|u|^{1/2}` is the action of the
dilations on the point vectors of the archimedean successor `−|b|`.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ} {s : ℝ}

/-- `|a|_v^{s/2}` for `x ↦ ax + b`. -/
def slopePow (v : AbsoluteValue K ℝ) (s : ℝ) (g : AffineGroupOf K) : ℝ := v (slopeOf g) ^ (s / 2)

theorem slopePow_pos (v : AbsoluteValue K ℝ) (s : ℝ) (g : AffineGroupOf K) : 0 < slopePow v s g :=
  Real.rpow_pos_of_pos (v.pos (slopeOf_ne_zero g)) _

theorem slopePow_sq (v : AbsoluteValue K ℝ) (s : ℝ) (g : AffineGroupOf K) :
    slopePow v s g ^ 2 = v (slopeOf g) ^ s := by
  rw [slopePow, ← Real.rpow_natCast, ← Real.rpow_mul (v.nonneg _)]
  norm_num

theorem slopePow_inv_mul (v : AbsoluteValue K ℝ) (s : ℝ) (g h : AffineGroupOf K) :
    slopePow v s (g⁻¹ * h) = slopePow v s h / slopePow v s g := by
  rw [slopePow, slopePow, slopePow, slopeOf_mul, slopeOf_inv, map_mul, map_inv₀,
    ← div_eq_inv_mul, Real.div_rpow (v.nonneg _) (v.nonneg _)]

theorem slopePow_one (v : AbsoluteValue K ℝ) (s : ℝ) : slopePow v s 1 = 1 := by
  simp [slopePow, slopeOf_one]

theorem slopePow_translation (v : AbsoluteValue K ℝ) (s : ℝ) (b : K) :
    slopePow v s (translationOf b) = 1 := by
  simp [slopePow, slopeOf_translationOf]

theorem ofAdd_inv_mul_ofAdd (x y : K) :
    (Multiplicative.ofAdd x)⁻¹ * Multiplicative.ofAdd y = Multiplicative.ofAdd (y - x) := by
  rw [← ofAdd_neg, ← ofAdd_add, neg_add_eq_sub]

/-- Conformality of exponent `s` for the absolute value `v`: `ψ(ub) = |u|_v^s ψ(b)`. -/
def IsConformal (v : AbsoluteValue K ℝ) (s : ℝ) (ψ : Multiplicative K → ℂ) : Prop :=
  ∀ u b : K, u ≠ 0 →
    ψ (Multiplicative.ofAdd (u * b)) = ((v u ^ s : ℝ) : ℂ) * ψ (Multiplicative.ofAdd b)

/-- A conformal successor of positive exponent for a nontrivial `v` vanishes at `0`. -/
theorem IsConformal.apply_zero {ψ : Multiplicative K → ℂ} (hψ : IsConformal v s ψ) (hs : 0 < s)
    (hv : ∃ u : K, 1 < v u) : ψ (Multiplicative.ofAdd 0) = 0 := by
  obtain ⟨u, hu⟩ := hv
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu; linarith
  have h := hψ u 0 hu0
  rw [mul_zero] at h
  have h1' : ((v u ^ s : ℝ) : ℂ) ≠ 1 := by exact_mod_cast (Real.one_lt_rpow hu hs).ne'
  have : (((v u ^ s : ℝ) : ℂ) - 1) * ψ (Multiplicative.ofAdd 0) = 0 := by
    rw [sub_mul, ← h]; ring
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1')

/-! ### Conformal induction -/

/-- **The conformally induced state** `Φ_ψ(x ↦ ax + b) = |a|^{−s/2} ψ(b)`. -/
def conformalInduction (v : AbsoluteValue K ℝ) (s : ℝ) (ψ : Multiplicative K → ℂ)
    (g : AffineGroupOf K) : ℂ :=
  (((slopePow v s g)⁻¹ : ℝ) : ℂ) * ψ (Multiplicative.ofAdd (shiftOf g))

theorem conformalInduction_inv_mul {ψ : Multiplicative K → ℂ} (hψ : IsConformal v s ψ)
    (g h : AffineGroupOf K) :
    conformalInduction v s ψ (g⁻¹ * h) = (((slopePow v s g * slopePow v s h)⁻¹ : ℝ) : ℂ) *
      ψ (Multiplicative.ofAdd (shiftOf h - shiftOf g)) := by
  have hg := slopeOf_ne_zero g
  have h1 := (slopePow_pos v s g).ne'
  have h2 := (slopePow_pos v s h).ne'
  rw [conformalInduction, shiftOf_inv_mul, hψ _ _ (inv_ne_zero hg), slopePow_inv_mul, map_inv₀,
    Real.inv_rpow (v.nonneg _), ← slopePow_sq, ← mul_assoc]
  congr 1
  push_cast
  field_simp

/-- The shifts `b_g` of a family. -/
def shifts {n : ℕ} (g : Fin n → AffineGroupOf K) : Fin n → Multiplicative K :=
  fun a => Multiplicative.ofAdd (shiftOf (g a))

/-- The weights `w_g |a_g|^{−s/2}`. -/
def boostWeights (v : AbsoluteValue K ℝ) (s : ℝ) {n : ℕ} (g : Fin n → AffineGroupOf K)
    (w : Fin n → ℂ) : Fin n → ℂ :=
  fun a => w a / (slopePow v s (g a) : ℂ)

/-- The Gram form of `Φ_ψ` is the form of `ψ` at the shifts with weights `w_g |a_g|^{−s/2}`. -/
theorem hermQuad_gram_conformalInduction {ψ : Multiplicative K → ℂ} (hψ : IsConformal v s ψ)
    {n : ℕ} (g : Fin n → AffineGroupOf K) (w : Fin n → ℂ) :
    hermQuad (gram (conformalInduction v s ψ) g) w =
      hermQuad (gram ψ (shifts g)) (boostWeights v s g w) := by
  rw [hermQuad_gram, hermQuad_gram]
  congr 1
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [conformalInduction_inv_mul hψ]
  simp only [shifts, boostWeights, ofAdd_inv_mul_ofAdd, map_div₀, Complex.conj_ofReal]
  have := (slopePow_pos v s (g a)).ne'
  have := (slopePow_pos v s (g b)).ne'
  push_cast
  field_simp

/-- **Conformal induction keeps the index**: `κ(Φ_ψ) = κ(ψ)`. -/
theorem negIndex_conformalInduction {ψ : Multiplicative K → ℂ} (hψ : IsConformal v s ψ) :
    negIndex (conformalInduction v s ψ) = negIndex ψ := by
  refine le_antisymm (negIndex_le_iff.mpr fun n g => ?_) ?_
  · let L : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
      { toFun := boostWeights v s g
        map_add' := fun w w' => funext fun a => by simp [boostWeights, add_div]
        map_smul' := fun t w => funext fun a => by simp [boostWeights, mul_div_assoc] }
    exact (Nat.cast_le.mpr (hermNegIndex_le_of_hermQuad_eq _ _ L
      fun w => (hermQuad_gram_conformalInduction hψ g w).symm)).trans
      (hermNegIndex_gram_le_negIndex ψ (shifts g))
  · have e : conformalInduction v s ψ ∘ translationHomOf = ψ := funext fun b => by
      simp [conformalInduction, translationHomOf, slopePow_translation, shiftOf_translationOf]
    have h := negIndex_comp_le (conformalInduction v s ψ) translationHomOf
    rwa [e] at h

/-! ### The pole–successor state -/

/-- **The pole–successor state** `|a|^{s/2} + |a|^{−s/2} + |a|^{−s/2} ψ(b)`. -/
def poleSuccessor (v : AbsoluteValue K ℝ) (s : ℝ) (ψ : Multiplicative K → ℂ)
    (g : AffineGroupOf K) : ℂ :=
  ((slopePow v s g + (slopePow v s g)⁻¹ : ℝ) : ℂ) + conformalInduction v s ψ g

/-- The boost pair `2 Re(X̄Y)`, `X = Σ w_g|a_g|^{−s/2}`, `Y = Σ w_g|a_g|^{s/2}`. -/
theorem hermQuad_gram_boostPair (v : AbsoluteValue K ℝ) (s : ℝ) {n : ℕ} (g : Fin n → AffineGroupOf K)
    (w : Fin n → ℂ) :
    hermQuad (gram (fun x => ((slopePow v s x + (slopePow v s x)⁻¹ : ℝ) : ℂ)) g) w =
      (conj (∑ a, boostWeights v s g w a) * ∑ a, w a * slopePow v s (g a) +
        conj (∑ a, w a * slopePow v s (g a)) * ∑ a, boostWeights v s g w a).re := by
  rw [hermQuad_gram]
  congr 1
  rw [map_sum, map_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [slopePow_inv_mul]
  simp only [boostWeights, map_div₀, map_mul, Complex.conj_ofReal]
  have := (slopePow_pos v s (g a)).ne'
  have := (slopePow_pos v s (g b)).ne'
  push_cast
  field_simp

/-- **The Gram identity**: the boost pair plus the form of `ψ` with total mass `X`. -/
theorem hermQuad_gram_poleSuccessor {ψ : Multiplicative K → ℂ} (hψ : IsConformal v s ψ) {n : ℕ}
    (g : Fin n → AffineGroupOf K) (w : Fin n → ℂ) :
    hermQuad (gram (poleSuccessor v s ψ) g) w =
      (conj (∑ a, boostWeights v s g w a) * ∑ a, w a * slopePow v s (g a) +
        conj (∑ a, w a * slopePow v s (g a)) * ∑ a, boostWeights v s g w a).re +
      hermQuad (gram ψ (shifts g)) (boostWeights v s g w) := by
  have e : gram (poleSuccessor v s ψ) g =
      gram (fun x => ((slopePow v s x + (slopePow v s x)⁻¹ : ℝ) : ℂ)) g +
        gram (conformalInduction v s ψ) g := by
    ext a b; simp [gram, poleSuccessor]
  rw [e, HeckeKreinToeplitz.hermQuad_add, hermQuad_gram_boostPair, hermQuad_gram_conformalInduction hψ]

/-- **One negative square.** A conditionally positive conformal successor glued to the boost pair
gives a state of index one. -/
theorem negIndex_poleSuccessor {ψ : Multiplicative K → ℂ} (hs : 0 < s) (hv : ∃ u : K, 1 < v u)
    (hψ : IsConformal v s ψ) (hpol : ∀ (n : ℕ) (x : Fin n → Multiplicative K) (c : Fin n → ℂ),
      ∑ a, c a = 0 → 0 ≤ hermQuad (gram ψ x) c) :
    negIndex (poleSuccessor v s ψ) = 1 := by
  refine le_antisymm ?_ ?_
  · refine negIndex_le_iff.mpr fun n g => ?_
    -- nonnegative on the kernel of `w ↦ X`
    let φ : Fin 1 → (Fin n → ℂ) →ₗ[ℂ] ℂ := fun _ =>
      { toFun := fun w => ∑ a, boostWeights v s g w a
        map_add' := fun w w' => by simp only [boostWeights, Pi.add_apply, add_div, sum_add_distrib]
        map_smul' := fun t w => by
          simp only [boostWeights, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_div_assoc,
            mul_sum] }
    have h := ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker
      (gram (poleSuccessor v s ψ) g) φ fun w hw => by
        have h0 : ∑ a, boostWeights v s g w a = 0 := hw 0
        rw [hermQuad_gram_poleSuccessor hψ, h0]
        simp only [map_zero, zero_mul, mul_zero, add_zero, Complex.zero_re, zero_add]
        exact hpol n _ _ h0
    rw [Fintype.card_fin] at h
    exact_mod_cast h
  · -- a dilationOf with `t = |u|_v^{s/2} > 1`: `2 + 2 − 2(t + 1/t) < 0`
    obtain ⟨u, hu⟩ := hv
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu; linarith
    set d := dilationOf (Units.mk0 u hu0)
    have ht : 1 < slopePow v s d := by
      simp only [slopePow, d, slopeOf_dilationOf, Units.val_mk0]
      exact Real.one_lt_rpow hu (by positivity)
    have htp : 0 < slopePow v s d := slopePow_pos v s d
    have h0 := hψ.apply_zero hs ⟨u, hu⟩
    have hval : ∀ x y : AffineGroupOf K, shiftOf x = 0 → shiftOf y = 0 →
        poleSuccessor v s ψ (x⁻¹ * y) =
          ((slopePow v s y / slopePow v s x + slopePow v s x / slopePow v s y : ℝ) : ℂ) := by
      intro x y hx hy
      rw [poleSuccessor, conformalInduction_inv_mul hψ, hx, hy, sub_zero, h0, mul_zero, add_zero,
        slopePow_inv_mul, inv_div]
    have hd : shiftOf d = 0 := shiftOf_dilationOf _
    have hpair : 2 < slopePow v s d + (slopePow v s d)⁻¹ := by
      have e : slopePow v s d + (slopePow v s d)⁻¹ - 2 = (slopePow v s d - 1) ^ 2 / slopePow v s d := by
        field_simp; ring
      have : 0 < (slopePow v s d - 1) ^ 2 / slopePow v s d := div_pos (by nlinarith) htp
      linarith
    have hneg : hermQuad (gram (poleSuccessor v s ψ) ![1, d]) ![1, -1] < 0 := by
      rw [hermQuad_gram]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        hval _ _ shiftOf_one shiftOf_one, hval _ _ shiftOf_one hd, hval _ _ hd shiftOf_one,
        hval _ _ hd hd, slopePow_one, div_self htp.ne', div_one, one_div]
      simp only [map_one, map_neg, one_mul, mul_one, neg_mul, Complex.add_re, Complex.neg_re,
        Complex.ofReal_re]
      norm_num
      linarith
    simpa using card_le_negIndex_of_orthogonal_translates (J := Fin 1) hneg (fun _ => 1)
      fun j j' h => absurd (Subsingleton.elim j j') h

/-- On the dilations the pole–successor state is the boost pair `|u|^{s/2} + |u|^{−s/2}`. -/
theorem poleSuccessor_dilation {ψ : Multiplicative K → ℂ} (hs : 0 < s) (hv : ∃ u : K, 1 < v u)
    (hψ : IsConformal v s ψ) (u : Kˣ) :
    poleSuccessor v s ψ (dilationOf u) = ((v u ^ (s / 2) + (v u ^ (s / 2))⁻¹ : ℝ) : ℂ) := by
  have h0 : ψ 1 = 0 := by simpa using hψ.apply_zero hs hv
  simp [poleSuccessor, conformalInduction, slopePow, slopeOf_dilationOf, shiftOf_dilationOf, h0]

/-- On the translations the pole–successor state is the successor `2 + ψ(b)`. -/
theorem poleSuccessor_translation (ψ : Multiplicative K → ℂ) (b : K) :
    poleSuccessor v s ψ (translationOf b) = 2 + ψ (Multiplicative.ofAdd b) := by
  simp only [poleSuccessor, conformalInduction, slopePow_translation, shiftOf_translationOf]
  norm_num

/-! ### The real place -/

/-- The real place is nontrivial. -/
theorem exists_one_lt_real : ∃ u : ℚ, 1 < Rat.AbsoluteValue.real u :=
  ⟨2, by rw [Rat.AbsoluteValue.real_eq_abs]; norm_num⟩

theorem isConformal_negAbsRat (c : ℝ) :
    IsConformal Rat.AbsoluteValue.real 1 fun m => (c : ℂ) * negAbsRat m := fun u b _ => by
  simp only [negAbsRat, absRat, toAdd_ofAdd, Real.rpow_one, Rat.AbsoluteValue.real_eq_abs, abs_mul]
  push_cast
  rw [← Rat.cast_abs, Complex.ofReal_ratCast]
  ring

/-- **The Hecke pole–successor state** `|a|^{1/2} + |a|^{−1/2} − c|a|^{−1/2}|b|` has exactly one
negative square for every `c ≥ 0`: the pole pair of Weil's kernel and the archimedean successor
`2 − c|b|` in one state. -/
theorem negIndex_poleSuccessorState {c : ℝ} (hc : 0 ≤ c) :
    negIndex (poleSuccessor Rat.AbsoluteValue.real 1 fun m => (c : ℂ) * negAbsRat m) = 1 :=
  negIndex_poleSuccessor one_pos exists_one_lt_real (isConformal_negAbsRat c) fun n x w hw => by
    have e : gram (fun m => (c : ℂ) * negAbsRat m) x = (c : ℂ) • gram negAbsRat x := by
      ext a b; simp [gram]
    rw [e, hermQuad_smul]
    exact mul_nonneg hc (hermQuad_gram_negAbsRat_nonneg x w hw)

/-- The successor `−|b|^s` on `ℚ`. -/
def negPowRat (s : ℝ) (m : Multiplicative ℚ) : ℂ :=
  -(((|((Multiplicative.toAdd m : ℚ) : ℝ)|) ^ s : ℝ) : ℂ)

theorem isConformal_negPowRat (c : ℝ) :
    IsConformal Rat.AbsoluteValue.real s fun m => (c : ℂ) * negPowRat s m := fun u b _ => by
  simp only [negPowRat, toAdd_ofAdd, Rat.cast_mul, abs_mul, Rat.AbsoluteValue.real_eq_abs,
    Rat.cast_abs, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  push_cast
  ring
/-- `−|b|^s` is conditionally positive on `ℚ` for `0 < s < 1`: one integral rescaling reduces it
to `ℤ`. -/
theorem hermQuad_gram_negPowRat_nonneg (hs0 : 0 < s) (hs1 : s < 1) {n : ℕ}
    (x : Fin n → Multiplicative ℚ) (c : Fin n → ℂ) (hc : ∑ a, c a = 0) :
    0 ≤ hermQuad (gram (negPowRat s) x) c := by
  obtain ⟨D, X, hD, hX⟩ := exists_int_scaling x
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have e : gram (negPowRat s) x = ((((D : ℝ) ^ s)⁻¹ : ℝ) : ℂ) • gram (negPowKernel s) X := by
    ext a b
    simp only [gram, negPowRat, negPowKernel, toAdd_mul, toAdd_inv, Matrix.smul_apply,
      smul_eq_mul]
    -- the integral differences are `D` times the rational ones
    have hab : ((-Multiplicative.toAdd (X a) + Multiplicative.toAdd (X b) : ℤ) : ℝ) =
        (D : ℝ) * ((-Multiplicative.toAdd (x a) + Multiplicative.toAdd (x b) : ℚ) : ℝ) := by
      have : (((-Multiplicative.toAdd (X a) + Multiplicative.toAdd (X b) : ℤ) : ℚ) : ℝ) =
          (((D : ℚ) * (-Multiplicative.toAdd (x a) + Multiplicative.toAdd (x b)) : ℚ) : ℝ) := by
        congr 1; push_cast; rw [hX a, hX b]; ring
      exact_mod_cast this
    rw [hab, abs_mul, abs_of_pos hD', Real.mul_rpow hD'.le (abs_nonneg _)]
    have hDs : (((D : ℝ) ^ s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.rpow_pos_of_pos hD' s).ne'
    push_cast
    field_simp
  rw [e, hermQuad_smul]
  exact mul_nonneg (by positivity) (hermQuad_gram_negPow_nonneg hs0 hs1 X c hc)

/-- **Stable pole–successor states**: for `0 < s < 1` and `c ≥ 0`,
`|a|^{s/2} + |a|^{−s/2} − c|a|^{−s/2}|b|^s` has exactly one negative square. -/
theorem negIndex_poleSuccessor_negPowRat (hs0 : 0 < s) (hs1 : s < 1) {c : ℝ} (hc : 0 ≤ c) :
    negIndex (poleSuccessor Rat.AbsoluteValue.real s fun m => (c : ℂ) * negPowRat s m) = 1 :=
  negIndex_poleSuccessor hs0 exists_one_lt_real (isConformal_negPowRat c) fun n x w hw => by
    have e : gram (fun m => (c : ℂ) * negPowRat s m) x = (c : ℂ) • gram (negPowRat s) x := by
      ext a b; simp [gram]
    rw [e, hermQuad_smul]
    exact mul_nonneg hc (hermQuad_gram_negPowRat_nonneg hs0 hs1 x w hw)

end GaloisForLFunctions.AdelicKreinGeometry
