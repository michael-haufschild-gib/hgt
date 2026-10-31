import GaloisForLFunctions.AdelicKreinGeometry.WeilsCorrelationWithAnArchimedeanSuccessor
import GaloisForLFunctions.AdelicKreinGeometry.LocalSignaturesAddOverDistinctPlaces
import GaloisForLFunctions.AdelicKreinGeometry.MixingKillsNegativeSquares

/-!
# The archimedean gluing formula

Glue a dilation datum `K` on `ℚ_{>0}` to the archimedean successor `−c|b|`:

  `Φ_{K,c}(x ↦ ax + b) = K(|a|) − c|a|^{−1/2}|b|`  (`archGlue`).

The glue is the boost coordinate: for slopes `u_i` the functional `ℓ(w) = Σ w_i u_i^{−1/2}` is the
total mass of the weights the successor sees. The **boost-polar index** `κ^{(½)}(K)`
(`boostPolarIndex`) is the supremum of the negative squares of `K` on the hyperplanes `ℓ = 0`; it
satisfies `κ^{(½)}(K) ≤ κ(K) ≤ κ^{(½)}(K) + 1` (`boostPolarIndex_le_negIndex`,
`negIndex_le_boostPolarIndex_add_one`).

* **The gluing formula** (`negIndex_archGlue_eq`): `κ(Φ_{K,c}) = κ^{(½)}(K) + 1` for every
  Hermitian `K` and `c > 0`.
* Upper bound (`negIndex_archGlue_le`): on `ℓ = 0` the successor's form is nonnegative, so only
  `K`'s form on the hyperplane remains.
* Lower bound (`add_one_le_negIndex_archGlue`): a negative subspace of `K` on `ℓ = 0`, placed on
  dilations, and the pair `1, x ↦ x + L` with weights `L^{−1/2}`: the successor cross terms vanish
  because `ℓ = 0`, the dilation cross terms are `O(L^{−1/2})`, and the pair's own form tends to
  `−2c`.
* **Weil's correlation** (`negIndex_weilArchState_eq`): the archimedean Weil state has index
  `κ^{(½)}(K_ζ) + 1`, so `ε = 1` in `κ(K_ζ) + ε` exactly when the negative squares of Weil's
  correlation are all carried on the hyperplane orthogonal to the boost character `u^{−1/2}`.

* **Sub-boost data** (`boostPolarIndex_eq_negIndex_of_subBoost`, `negIndex_archGlue_eq_of_subBoost`):
  if `‖K(λ_N u)‖ λ_N^{−1/2} → 0` along slopes `λ_N → ∞`, then `κ^{(½)}(K) = κ(K)` and the gluing
  costs exactly one square, `κ = κ(K) + 1`.

So the archimedean place glues by a hyperplane: the scalar gluing square of separable assemblies is
replaced by the codimension-one constraint that the dilation data be orthogonal to the boost, and
the constraint is free for data that grow slower than the boost.
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate Matrix
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

theorem posUnits_val_pos (u : posUnits) : (0 : ℝ) < (((u : ℚˣ) : ℚ) : ℝ) := by
  exact_mod_cast u.2

/-- The boost coordinate `ℓ(w) = Σ w_i u_i^{−1/2}` of a family of positive slopes. -/
def boostMassU {n : ℕ} (u : Fin n → posUnits) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun w := ∑ i, w i * (((((u i : ℚˣ) : ℚ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
  map_add' w w' := by simp only [Pi.add_apply, add_mul, sum_add_distrib]
  map_smul' t w := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, mul_sum]

/-- **The boost-polar index**: negative squares of `K` on the hyperplanes `ℓ = 0`. -/
def boostPolarIndex (K : posUnits → ℂ) : ℕ∞ :=
  ⨆ (n : ℕ) (u : Fin n → posUnits), (negIndexOn (gram K u) (LinearMap.ker (boostMassU u)) : ℕ∞)

theorem negIndexOn_le_boostPolarIndex (K : posUnits → ℂ) {n : ℕ} (u : Fin n → posUnits) :
    (negIndexOn (gram K u) (LinearMap.ker (boostMassU u)) : ℕ∞) ≤ boostPolarIndex K :=
  le_iSup₂ (f := fun n (u : Fin n → posUnits) =>
    (negIndexOn (gram K u) (LinearMap.ker (boostMassU u)) : ℕ∞)) n u

theorem boostPolarIndex_le_negIndex (K : posUnits → ℂ) : boostPolarIndex K ≤ negIndex K :=
  iSup₂_le fun _ u =>
    (Nat.cast_le.mpr (negIndexOn_le_hermNegIndex _ _)).trans (hermNegIndex_gram_le_negIndex K u)

theorem negIndex_le_boostPolarIndex_add_one (K : posUnits → ℂ) :
    negIndex K ≤ boostPolarIndex K + 1 :=
  negIndex_le_iff.mpr fun n u => by
    have h := hermNegIndex_le_negIndexOn_ker_add_one (gram K u) (boostMassU u)
    calc (hermNegIndex (gram K u) : ℕ∞)
        ≤ ((negIndexOn (gram K u) (LinearMap.ker (boostMassU u)) + 1 : ℕ) : ℕ∞) := Nat.cast_le.mpr h
      _ ≤ boostPolarIndex K + 1 := by
          push_cast
          exact add_le_add (negIndexOn_le_boostPolarIndex K u) le_rfl

/-- A larger form on a subspace has fewer negative squares there. -/
theorem negIndexOn_le_of_hermQuad_le {ι : Type*} [Fintype ι] {H H' : Matrix ι ι ℂ}
    {V : Submodule ℂ (ι → ℂ)} (h : ∀ c ∈ V, hermQuad H' c ≤ hermQuad H c) :
    negIndexOn H V ≤ negIndexOn H' V := by
  obtain ⟨W, hWV, hWr, hW⟩ := exists_negIndexOn H V
  have hW' : IsPosDefOn (-H') W := fun c hc hc0 => by
    have := hW c hc hc0
    rw [hermQuad_neg] at this ⊢
    linarith [h c (hWV hc)]
  rw [← hWr]
  exact le_csSup (negIndexOn_bddAbove H' V) ⟨W, hWV, rfl, hW'⟩

/-- **The archimedean gluing** `K(|a|) − c|a|^{−1/2}|b|`. -/
def archGlue (K : posUnits → ℂ) (c : ℝ) (g : AffineGroupQ) : ℂ :=
  K (slopeAbs g) + conformalInduction Rat.AbsoluteValue.real 1 (fun m => (c : ℂ) * negAbsRat m) g

theorem weilArchState_eq_archGlue (c : ℝ) : weilArchState c = archGlue ratCorr c := rfl

theorem slopePow_real_eq (g : AffineGroupQ) :
    slopePow Rat.AbsoluteValue.real 1 g = ((((slopeAbs g : ℚˣ) : ℚ) : ℝ)) ^ (1 / 2 : ℝ) := by
  simp [slopePow, slopeAbs, absUnit, slopeUnit, Rat.AbsoluteValue.real_eq_abs]
  rfl

/-- The boost weights carry the boost coordinate as their total mass. -/
theorem sum_boostWeights_eq {n : ℕ} (g : Fin n → AffineGroupQ) (w : Fin n → ℂ) :
    ∑ a, boostWeights Rat.AbsoluteValue.real 1 g w a = boostMassU (fun a => slopeAbs (g a)) w := by
  simp only [boostWeights, boostMassU, LinearMap.coe_mk, AddHom.coe_mk, slopePow_real_eq]
  refine sum_congr rfl fun a _ => ?_
  rw [Real.rpow_neg (posUnits_val_pos _).le, Complex.ofReal_inv, div_eq_mul_inv]

theorem gram_comp_slopeAbs (K : posUnits → ℂ) {n : ℕ} (g : Fin n → AffineGroupQ) :
    gram (fun x => K (slopeAbs x)) g = gram K fun a => slopeAbs (g a) := by
  ext a b; simp [gram, map_mul, map_inv]

/-- **The Gram identity**: `K`'s form at the slopes plus the successor's form at the shifts. -/
theorem hermQuad_gram_archGlue (K : posUnits → ℂ) (c : ℝ) {n : ℕ} (g : Fin n → AffineGroupQ)
    (w : Fin n → ℂ) :
    hermQuad (gram (archGlue K c) g) w = hermQuad (gram K fun a => slopeAbs (g a)) w +
      hermQuad (gram (fun m => (c : ℂ) * negAbsRat m) (shifts g))
        (boostWeights Rat.AbsoluteValue.real 1 g w) := by
  have e : gram (archGlue K c) g = gram (fun x => K (slopeAbs x)) g +
      gram (conformalInduction Rat.AbsoluteValue.real 1 (fun m => (c : ℂ) * negAbsRat m)) g := by
    ext a b; simp [gram, archGlue]
  rw [e, HeckeKreinToeplitz.hermQuad_add, gram_comp_slopeAbs,
    hermQuad_gram_conformalInduction (isConformal_negAbsRat c)]

/-- **Upper bound**: `κ(Φ_{K,c}) ≤ κ^{(½)}(K) + 1`. -/
theorem negIndex_archGlue_le (K : posUnits → ℂ) {c : ℝ} (hc : 0 ≤ c) :
    negIndex (archGlue K c) ≤ boostPolarIndex K + 1 := by
  refine negIndex_le_iff.mpr fun n g => ?_
  set u : Fin n → posUnits := fun a => slopeAbs (g a)
  have h1 := hermNegIndex_le_negIndexOn_ker_add_one (gram (archGlue K c) g) (boostMassU u)
  have h2 : negIndexOn (gram (archGlue K c) g) (LinearMap.ker (boostMassU u)) ≤
      negIndexOn (gram K u) (LinearMap.ker (boostMassU u)) :=
    negIndexOn_le_of_hermQuad_le fun w hw => by
      rw [hermQuad_gram_archGlue]
      have hmass : ∑ a, boostWeights Rat.AbsoluteValue.real 1 g w a = 0 := by
        rw [sum_boostWeights_eq]; exact LinearMap.mem_ker.mp hw
      linarith [hermQuad_gram_ofReal_mul_nonneg hc (shifts g) _
        (hermQuad_gram_negAbsRat_nonneg (shifts g) _ hmass)]
  calc (hermNegIndex (gram (archGlue K c) g) : ℕ∞)
      ≤ ((negIndexOn (gram (archGlue K c) g) (LinearMap.ker (boostMassU u)) + 1 : ℕ) : ℕ∞) :=
        Nat.cast_le.mpr h1
    _ ≤ boostPolarIndex K + 1 := by
        push_cast
        exact add_le_add ((Nat.cast_le.mpr h2).trans (negIndexOn_le_boostPolarIndex K u)) le_rfl

/-! ### The lower bound -/

theorem archGlue_inv_mul (K : posUnits → ℂ) (c : ℝ) (g h : AffineGroupQ) :
    archGlue K c (g⁻¹ * h) = K ((slopeAbs g)⁻¹ * slopeAbs h) +
      (((slopePow Rat.AbsoluteValue.real 1 g * slopePow Rat.AbsoluteValue.real 1 h)⁻¹ : ℝ) : ℂ) *
        ((c : ℂ) * negAbsRat (Multiplicative.ofAdd (shiftOf h - shiftOf g))) := by
  rw [archGlue, conformalInduction_inv_mul (isConformal_negAbsRat c), map_mul, map_inv]

/-- **Lower bound**: every negative subspace of `K` on `ℓ = 0` survives next to one square of the
successor. -/
theorem add_one_le_negIndex_archGlue {K : posUnits → ℂ} (hK : IsHermKernel K) {c : ℝ} (hc : 0 < c)
    {m : ℕ} (u : Fin m → posUnits) :
    (negIndexOn (gram K u) (LinearMap.ker (boostMassU u)) : ℕ∞) + 1 ≤ negIndex (archGlue K c) := by
  classical
  obtain ⟨W, hWV, hWr, hW⟩ := exists_negIndexOn (gram K u) (LinearMap.ker (boostMassU u))
  set r := Module.finrank ℂ W
  set bW := Module.finBasis ℂ W
  set BW : Matrix (Fin m) (Fin r) ℂ := Matrix.of fun i k => (bW k : Fin m → ℂ) i
  have hBW : ∀ k, ∑ i, BW i k * (((((u i : ℚˣ) : ℚ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 0 :=
    fun k => LinearMap.mem_ker.mp (hWV (bW k).2)
  set Φ := archGlue K c
  set D : Fin m → AffineGroupQ := fun i => dilation ((u i : posUnits) : ℚˣ)
  have hDslope : ∀ i, slopeAbs (D i) = u i := fun i => slopeAbs_dilation _
  have hDshift : ∀ i, shiftOf (D i) = 0 := fun i => affShift_dilation _
  have hDpow : ∀ i, slopePow Rat.AbsoluteValue.real 1 (D i) =
      ((((u i : ℚˣ) : ℚ) : ℝ)) ^ (1 / 2 : ℝ) := fun i => by rw [slopePow_real_eq, hDslope]
  -- the translation pair `1, x ↦ x + (N + 1)`
  set T : ℕ → Fin 2 → AffineGroupQ := fun N => ![1, translation ((N : ℚ) + 1)]
  have hTslope : ∀ N e, slopeAbs (T N e) = 1 := fun N e => by
    fin_cases e
    · simp [T]
    · simp [T, slopeAbs_translation]
  have hTpow : ∀ N e, slopePow Rat.AbsoluteValue.real 1 (T N e) = 1 := fun N e => by
    fin_cases e
    · simp [T, slopePow_one]
    · exact slopePow_translation _ _ _
  set σ : ℕ → ℝ := fun N => (Real.sqrt ((N : ℝ) + 1))⁻¹
  -- the compression
  set Sig : ℕ → Matrix (Fin 2) (Fin 1) ℂ := fun N => Matrix.of fun _ _ => (σ N : ℂ)
  set S : ℕ → Matrix (Fin m ⊕ Fin 2) (Fin r ⊕ Fin 1) ℂ := fun N => Matrix.fromBlocks BW 0 0 (Sig N)
  set C : ℕ → Matrix (Fin m) (Fin 2) ℂ := fun N => Matrix.of fun i e => Φ ((D i)⁻¹ * T N e)
  set C' : ℕ → Matrix (Fin 2) (Fin m) ℂ := fun N => Matrix.of fun e i => Φ ((T N e)⁻¹ * D i)
  set A := gram Φ D
  set E : ℕ → Matrix (Fin 2) (Fin 2) ℂ := fun N => gram Φ (T N)
  have hblock : ∀ N, gram Φ (Sum.elim D (T N)) = Matrix.fromBlocks A (C N) (C' N) (E N) := by
    intro N
    ext p q
    rcases p with i | e <;> rcases q with j | e' <;> rfl
  set H : ℕ → Matrix (Fin r ⊕ Fin 1) (Fin r ⊕ Fin 1) ℂ := fun N =>
    (S N)ᴴ * gram Φ (Sum.elim D (T N)) * S N
  have hH : ∀ N, H N = Matrix.fromBlocks (BWᴴ * A * BW) (BWᴴ * C N * Sig N)
      ((Sig N)ᴴ * C' N * BW) ((Sig N)ᴴ * E N * Sig N) := by
    intro N
    simp only [H, hblock, S, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  set H₀ : Matrix (Fin r ⊕ Fin 1) (Fin r ⊕ Fin 1) ℂ :=
    Matrix.fromBlocks (BWᴴ * A * BW) 0 0 (Matrix.of fun _ _ => ((-2 * c : ℝ) : ℂ))
  have hσ : Tendsto (fun N : ℕ => σ N) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => Real.sqrt ((N : ℝ) + 1)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    exact tendsto_inv_atTop_zero.comp h1
  have hσc : Tendsto (fun N : ℕ => ((σ N : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp hσ
  have hσsq : ∀ N : ℕ, σ N * σ N = ((N : ℝ) + 1)⁻¹ := fun N => by
    simp only [σ]
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  have hneg0 : negAbsRat (Multiplicative.ofAdd 0) = 0 := by simp [negAbsRat, absRat]
  -- the boost coordinates `ρ_i = u_i^{−1/2}`; the basis of `W` has `ℓ = 0`
  set ρ : Fin m → ℂ := fun i => (((((u i : ℚˣ) : ℚ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
  have hzero : ∀ k, ∑ i, conj (BW i k) * ρ i = 0 := fun k => by
    have h := congrArg conj (hBW k)
    rw [map_sum, map_zero] at h
    rw [← h]
    refine sum_congr rfl fun i _ => ?_
    simp [ρ, Complex.conj_ofReal]
  have hzero' : ∀ k, ∑ i, ρ i * BW i k = 0 := fun k => by
    rw [← hBW k]; exact sum_congr rfl fun i _ => mul_comm _ _
  have hρ : ∀ i, (((slopePow Rat.AbsoluteValue.real 1 (D i))⁻¹ : ℝ) : ℂ) = ρ i := fun i => by
    rw [hDpow, ← Real.rpow_neg (posUnits_val_pos _).le]
  -- entries of the cross blocks
  have hcross : ∀ k, Tendsto (fun N => (BWᴴ * C N * Sig N) k 0) atTop (𝓝 0) := by
    intro k
    have hent : ∀ N, (BWᴴ * C N * Sig N) k 0 =
        (σ N : ℂ) * (2 * ∑ i, conj (BW i k) * K ((u i)⁻¹)) := by
      intro N
      have hterm : ∀ i e, Φ ((D i)⁻¹ * T N e) = K ((u i)⁻¹) +
          ((c : ℂ) * negAbsRat (Multiplicative.ofAdd (shiftOf (T N e)))) * ρ i := fun i e => by
        simp only [Φ, archGlue_inv_mul, hDslope, hTslope, mul_one, hTpow, hDshift, sub_zero]
        rw [hρ]
        ring
      have hs : ∀ l : ℂ, ∑ i, conj (BW i k) * (K ((u i)⁻¹) + l * ρ i) =
          ∑ i, conj (BW i k) * K ((u i)⁻¹) := fun l => by
        simp only [mul_add, sum_add_distrib]
        rw [show ∑ i, conj (BW i k) * (l * ρ i) = l * ∑ i, conj (BW i k) * ρ i by
          rw [mul_sum]; exact sum_congr rfl fun i _ => by ring, hzero k, mul_zero, add_zero]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, C, Sig, Matrix.of_apply,
        Fin.sum_univ_two, hterm, Complex.star_def, hs]
      ring
    simp_rw [hent]
    simpa using hσc.mul_const (2 * ∑ i, conj (BW i k) * K ((u i)⁻¹))
  -- the other cross block is the adjoint, since `Φ` is Hermitian
  have hΦ : IsHermKernel Φ := fun g => by
    have h1 : ∀ g : AffineGroupQ, K (slopeAbs g⁻¹) = conj (K (slopeAbs g)) := fun g => by
      rw [map_inv]; exact hK _
    have h2 := isHermKernel_conformalInduction (isConformal_negAbsRat c)
      (isHermKernel_ofReal_mul isHermKernel_negAbsRat c)
    show K (slopeAbs g⁻¹) + _ = conj (K (slopeAbs g) + _)
    rw [h1 g, h2 g, map_add]
  have hC' : ∀ N, C' N = (C N)ᴴ := fun N => by
    ext e i
    simp only [C, C', Matrix.of_apply, Matrix.conjTranspose_apply, Complex.star_def]
    rw [← hΦ, _root_.mul_inv_rev, inv_inv]
  have hcross' : ∀ k, Tendsto (fun N => ((Sig N)ᴴ * C' N * BW) 0 k) atTop (𝓝 0) := by
    intro k
    have e : ∀ N, ((Sig N)ᴴ * C' N * BW) 0 k = conj ((BWᴴ * C N * Sig N) k 0) := fun N => by
      rw [hC', ← Matrix.conjTranspose_conjTranspose BW, ← Matrix.conjTranspose_mul,
        ← Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_apply,
        Complex.star_def, Matrix.mul_assoc]
    simp_rw [e]
    simpa [Function.comp_def] using (Complex.continuous_conj.tendsto 0).comp (hcross k)
  -- the pair block tends to `−2c`
  have hpair : Tendsto (fun N => ((Sig N)ᴴ * E N * Sig N) 0 0) atTop
      (𝓝 ((-2 * c : ℝ) : ℂ)) := by
    have hent : ∀ N, ((Sig N)ᴴ * E N * Sig N) 0 0 =
        ((σ N * σ N : ℝ) : ℂ) * (4 * K 1) - ((2 * c * (σ N * σ N * ((N : ℝ) + 1)) : ℝ) : ℂ) := by
      intro N
      have hsp : slopePow Rat.AbsoluteValue.real 1 (translation ((N : ℚ) + 1)) = 1 :=
        slopePow_translation _ _ _
      have hsp' : slopePow Rat.AbsoluteValue.real 1 (translation (-((N : ℚ) + 1))) = 1 :=
        slopePow_translation _ _ _
      have hsh : shiftOf (translation ((N : ℚ) + 1)) = (N : ℚ) + 1 := affShift_translation _
      have hsh' : shiftOf (translation (-((N : ℚ) + 1))) = -((N : ℚ) + 1) := affShift_translation _
      have hinv : (translation ((N : ℚ) + 1))⁻¹ = translation (-((N : ℚ) + 1)) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← translation_add, neg_add_cancel, translation_zero]
      have e00 : Φ 1 = K 1 := by
        simp only [Φ, archGlue, map_one, conformalInduction, shiftOf_one, hneg0,
          mul_zero, add_zero]
      have e01 : Φ (translation ((N : ℚ) + 1)) = K 1 - (c : ℂ) * ((N : ℂ) + 1) := by
        simp only [Φ, archGlue, slopeAbs_translation, conformalInduction, hsp, hsh, inv_one,
          Complex.ofReal_one, one_mul, negAbsRat, absRat, toAdd_ofAdd]
        rw [abs_of_nonneg (by positivity)]; push_cast; ring
      have e10 : Φ (translation (-((N : ℚ) + 1))) = K 1 - (c : ℂ) * ((N : ℂ) + 1) := by
        simp only [Φ, archGlue, slopeAbs_translation, conformalInduction, hsp', hsh', inv_one,
          Complex.ofReal_one, one_mul, negAbsRat, absRat, toAdd_ofAdd]
        rw [abs_neg, abs_of_nonneg (by positivity)]; push_cast; ring
      have e11 : Φ (translation (-((N : ℚ) + 1)) * translation ((N : ℚ) + 1)) = K 1 := by
        rw [← translation_add, neg_add_cancel, translation_zero, e00]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, E, Sig, gram, T, Matrix.of_apply,
        Fin.sum_univ_two, Complex.star_def, Complex.conj_ofReal,
        Matrix.cons_val_zero, Matrix.cons_val_one, inv_one, one_mul, mul_one,
        hinv, e00, e01, e10, e11]
      push_cast
      ring
    have h3 : ∀ N : ℕ, σ N * σ N * ((N : ℝ) + 1) = 1 := fun N => by
      rw [hσsq]; field_simp
    simp_rw [hent, h3]
    have h1 : Tendsto (fun N : ℕ => ((σ N * σ N : ℝ) : ℂ)) atTop (𝓝 0) := by
      have := hσ.mul hσ
      rw [mul_zero] at this
      simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp this
    have := (h1.mul_const (4 * K 1)).sub_const ((2 * c * 1 : ℝ) : ℂ)
    simpa using this
  have hconv : ∀ p q, Tendsto (fun N => H N p q) atTop (𝓝 (H₀ p q)) := by
    intro p q
    simp only [hH]
    rcases p with k | e <;> rcases q with k' | e'
    · exact tendsto_const_nhds
    · fin_cases e'; simpa [H₀] using hcross k
    · fin_cases e; simpa [H₀] using hcross' k'
    · fin_cases e; fin_cases e'; simpa [H₀] using hpair
  -- the limit has `r + 1` negative squares
  have hA : A = gram K u := by
    ext i j
    simp only [A, gram, Φ, archGlue_inv_mul, hDslope, hDshift, sub_self, hneg0,
      mul_zero, add_zero]
  have hH₀ : H₀.IsHermitian := by
    refine Matrix.IsHermitian.fromBlocks ?_ (by simp) ?_
    · rw [hA]
      simpa [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
        congrArg (fun M => BWᴴ * M * BW) (gram_isHermitian hK u)
    · ext a b; simp [Matrix.conjTranspose_apply]
  have hP : r ≤ hermNegIndex (BWᴴ * A * BW) := by
    have h := card_le_hermNegIndex_of_forall_neg (BWᴴ * A * BW) LinearMap.id fun a ha => by
      rw [LinearMap.id_apply, HTGeometry.hermQuad_rect_conjugate, hA]
      have hmem : BW.mulVec a = (bW.equivFun.symm a : Fin m → ℂ) := by
        ext i
        simp only [Matrix.mulVec, dotProduct, BW, Matrix.of_apply, Module.Basis.equivFun_symm_apply,
          Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact sum_congr rfl fun k _ => mul_comm _ _
      have hc0 : (bW.equivFun.symm a : Fin m → ℂ) ≠ 0 := fun h =>
        ha (bW.equivFun.symm.injective (Subtype.ext (by rw [h, map_zero]; rfl)))
      rw [hmem]
      have := hW _ (bW.equivFun.symm a).2 hc0
      rw [hermQuad_neg] at this
      linarith
    simpa using h
  have hscal : 1 ≤ hermNegIndex (Matrix.of fun _ _ => ((-2 * c : ℝ) : ℂ) :
      Matrix (Fin 1) (Fin 1) ℂ) := by
    have hneg : hermQuad (Matrix.of fun _ _ => ((-2 * c : ℝ) : ℂ) : Matrix (Fin 1) (Fin 1) ℂ)
        ![1] < 0 := by
      simp [hermQuad, Matrix.mulVec, dotProduct]
      linarith
    exact (one_le_negIndexOn (V := ⊤) Submodule.mem_top hneg).trans (negIndexOn_le_hermNegIndex _ _)
  have hlimit : r + 1 ≤ hermNegIndex H₀ :=
    (add_le_add hP hscal).trans (hermNegIndex_add_le_fromBlocks _ _)
  obtain ⟨N, hN⟩ := (eventually_le_hermNegIndex hH₀ hconv).exists
  have hcomp : hermNegIndex (H N) ≤ hermNegIndex (gram Φ (Sum.elim D (T N))) :=
    hermNegIndex_le_of_hermQuad_eq _ _ (Matrix.mulVecLin (S N)) fun a => by
      rw [Matrix.mulVecLin_apply, ← HTGeometry.hermQuad_rect_conjugate]
  have hfin := hermNegIndex_gram_le_negIndex Φ (Sum.elim D (T N))
  have hfinal : r + 1 ≤ hermNegIndex (gram Φ (Sum.elim D (T N))) := (hlimit.trans hN).trans hcomp
  calc (negIndexOn (gram K u) (LinearMap.ker (boostMassU u)) : ℕ∞) + 1
      = ((r + 1 : ℕ) : ℕ∞) := by push_cast; rw [hWr]
    _ ≤ negIndex Φ := (Nat.cast_le.mpr hfinal).trans hfin

/-- **The archimedean gluing formula**: `κ(K(|a|) − c|a|^{−1/2}|b|) = κ^{(½)}(K) + 1`. -/
theorem negIndex_archGlue_eq {K : posUnits → ℂ} (hK : IsHermKernel K) {c : ℝ} (hc : 0 < c) :
    negIndex (archGlue K c) = boostPolarIndex K + 1 := by
  refine le_antisymm (negIndex_archGlue_le K hc.le) ?_
  rcases eq_or_ne (negIndex (archGlue K c)) ⊤ with htop | htop
  · rw [htop]; exact le_top
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp htop
  have hfam : ∀ (m : ℕ) (u : Fin m → posUnits),
      negIndexOn (gram K u) (LinearMap.ker (boostMassU u)) + 1 ≤ M := fun m u => by
    have h := add_one_le_negIndex_archGlue hK hc u
    rw [← hM] at h
    exact_mod_cast h
  have h1 : 1 ≤ M := by have := hfam 0 (fun i => i.elim0); omega
  have hall : ∀ (m : ℕ) (u : Fin m → posUnits),
      (negIndexOn (gram K u) (LinearMap.ker (boostMassU u)) : ℕ∞) ≤ ((M - 1 : ℕ) : ℕ∞) :=
    fun m u => Nat.cast_le.mpr (by have := hfam m u; omega)
  calc boostPolarIndex K + 1 ≤ ((M - 1 : ℕ) : ℕ∞) + 1 := add_le_add (iSup₂_le hall) le_rfl
    _ = negIndex (archGlue K c) := by
        rw [← hM]; norm_cast; omega

/-- **Weil's correlation with the archimedean successor**: `κ = κ^{(½)}(K_ζ) + 1`. -/
theorem negIndex_weilArchState_eq {c : ℝ} (hc : 0 < c) :
    negIndex (weilArchState c) = boostPolarIndex ratCorr + 1 := by
  rw [weilArchState_eq_archGlue, negIndex_archGlue_eq isHermKernel_ratCorr hc]

/-! ### Sub-boost dilation data -/

/-- **Sub-boost data are glued at full index.** If along slopes `λ_N` with `λ_N^{−1/2} → 0` the
data grow slower than the boost, `‖K(λ_N u)‖ λ_N^{−1/2} → 0`, then `κ^{(½)}(K) = κ(K)`: a negative
family dilated by `λ_N` and corrected at the slope `1` by the weight `−λ_N^{−1/2} ℓ` lies on `ℓ = 0`,
and its compressed Gram matrices tend to the original ones. -/
theorem boostPolarIndex_eq_negIndex_of_subBoost {K : posUnits → ℂ} (hK : IsHermKernel K)
    (lam : ℕ → posUnits)
    (hlam : Tendsto (fun N => ((((lam N : ℚˣ) : ℚ) : ℝ)) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0))
    (hgrow : ∀ u : posUnits, Tendsto (fun N => K (lam N * u) *
      (((((lam N : ℚˣ) : ℚ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) atTop (𝓝 0)) :
    boostPolarIndex K = negIndex K := by
  classical
  refine le_antisymm (boostPolarIndex_le_negIndex K) (negIndex_le_iff.mpr fun n F => ?_)
  set μ : ℕ → ℝ := fun N => ((((lam N : ℚˣ) : ℚ) : ℝ)) ^ (-(1 / 2 : ℝ))
  set ρ : Fin n → ℝ := fun i => ((((F i : ℚˣ) : ℚ) : ℝ)) ^ (-(1 / 2 : ℝ))
  set Fam : ℕ → Fin (n + 1) → posUnits := fun N => Fin.cons 1 fun i => lam N * F i
  set L : ℕ → Matrix (Fin (n + 1)) (Fin n) ℂ := fun N => Matrix.of fun p j =>
    Fin.cases (-((μ N * ρ j : ℝ) : ℂ)) (fun i => if i = j then (1 : ℂ) else 0) p
  set M : ℕ → Matrix (Fin n) (Fin n) ℂ := fun N => (L N)ᴴ * gram K (Fam N) * L N
  -- the entries
  have hM : ∀ N i j, M N i j = K ((F i)⁻¹ * F j) - ((μ N * ρ i : ℝ) : ℂ) * K (lam N * F j) -
      conj (K (lam N * F i)) * ((μ N * ρ j : ℝ) : ℂ) +
      ((μ N * ρ i : ℝ) : ℂ) * ((μ N * ρ j : ℝ) : ℂ) * K 1 := by
    intro N i j
    have e1 : ∀ i j, (lam N * F i)⁻¹ * (lam N * F j) = (F i)⁻¹ * F j := fun i j => by group
    have e2 : ∀ i, K (lam N * F i)⁻¹ = conj (K (lam N * F i)) := fun i => hK _
    simp only [M, L, Fam, Matrix.mul_apply, Matrix.conjTranspose_apply, gram, Matrix.of_apply,
      Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.cases_zero, Fin.cases_succ, e1, e2,
      inv_one, one_mul, mul_one, Complex.star_def, map_neg, Complex.conj_ofReal, apply_ite conj,
      map_one, map_zero, ite_mul, zero_mul, sum_ite_eq', mem_univ, if_true, mul_ite, mul_zero]
    ring
  have hconv : ∀ i j, Tendsto (fun N => M N i j) atTop (𝓝 (gram K F i j)) := by
    intro i j
    simp_rw [hM]
    have hμc : Tendsto (fun N => ((μ N : ℝ) : ℂ)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp hlam
    have t1 : Tendsto (fun N => ((μ N * ρ i : ℝ) : ℂ) * K (lam N * F j)) atTop (𝓝 0) := by
      have := (hgrow (F j)).const_mul ((ρ i : ℝ) : ℂ)
      rw [mul_zero] at this
      refine this.congr fun N => ?_
      push_cast; ring
    have t2 : Tendsto (fun N => conj (K (lam N * F i)) * ((μ N * ρ j : ℝ) : ℂ)) atTop (𝓝 0) := by
      have := ((Complex.continuous_conj.tendsto 0).comp (hgrow (F i))).const_mul ((ρ j : ℝ) : ℂ)
      simp only [Function.comp_def, map_zero, mul_zero] at this
      refine this.congr fun N => ?_
      simp only [map_mul, Complex.conj_ofReal]
      push_cast; ring
    have t3 : Tendsto (fun N => ((μ N * ρ i : ℝ) : ℂ) * ((μ N * ρ j : ℝ) : ℂ) * K 1) atTop (𝓝 0) := by
      have := ((hμc.mul hμc).const_mul (((ρ i * ρ j : ℝ) : ℂ) * K 1))
      rw [mul_zero, mul_zero] at this
      refine this.congr fun N => ?_
      push_cast; ring
    have := ((tendsto_const_nhds (x := K ((F i)⁻¹ * F j))).sub t1).sub t2 |>.add t3
    simpa [gram] using this
  obtain ⟨N, hN⟩ := (eventually_le_hermNegIndex (gram_isHermitian hK F) hconv).exists
  -- a negative subspace of `M N` lands on `ℓ = 0`
  obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-M N)
  set bW := Module.finBasis ℂ W
  set L' : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) :=
    (L N).mulVecLin ∘ₗ W.subtype ∘ₗ bW.equivFun.symm.toLinearMap
  have hroot : ∀ i, (((((lam N * F i : posUnits) : ℚˣ) : ℚ) : ℝ)) ^ (-(1 / 2 : ℝ)) = μ N * ρ i :=
    fun i => by
      simp only [Subgroup.coe_mul, Units.val_mul, Rat.cast_mul, μ, ρ]
      exact Real.mul_rpow (posUnits_val_pos _).le (posUnits_val_pos _).le
  have hV : ∀ a, L' a ∈ LinearMap.ker (boostMassU (Fam N)) := fun a => by
    rw [LinearMap.mem_ker]
    simp only [L', boostMassU, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp,
      Function.comp_apply, Matrix.mulVecLin_apply, Fin.sum_univ_succ, Fam, Fin.cons_zero,
      Fin.cons_succ, hroot, Matrix.mulVec, dotProduct, L, Matrix.of_apply, Fin.cases_zero,
      Fin.cases_succ, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, if_true,
      OneMemClass.coe_one, Units.val_one, Rat.cast_one, Real.one_rpow, Complex.ofReal_one, mul_one]
    rw [← sum_add_distrib]
    refine sum_eq_zero fun i _ => ?_
    push_cast; ring
  have hneg : ∀ a, a ≠ 0 → hermQuad (gram K (Fam N)) (L' a) < 0 := fun a ha => by
    have hw0 : (bW.equivFun.symm a : Fin n → ℂ) ≠ 0 := fun h =>
      ha (bW.equivFun.symm.injective (Subtype.ext (by rw [h, map_zero]; rfl)))
    have hpos := hW _ (bW.equivFun.symm a).2 hw0
    rw [hermQuad_neg] at hpos
    simp only [L', LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply]
    rw [← HTGeometry.hermQuad_rect_conjugate]
    exact neg_pos.mp hpos
  have h1 := card_le_negIndexOn_of_forall_neg (gram K (Fam N)) _ L' hV hneg
  rw [Fintype.card_fin] at h1
  have h2 : hermNegIndex (M N) = Module.finrank ℂ W := hrank.symm
  calc (hermNegIndex (gram K F) : ℕ∞) ≤ (hermNegIndex (M N) : ℕ∞) := Nat.cast_le.mpr hN
    _ ≤ (negIndexOn (gram K (Fam N)) (LinearMap.ker (boostMassU (Fam N))) : ℕ∞) :=
        Nat.cast_le.mpr (h2 ▸ h1)
    _ ≤ boostPolarIndex K := negIndexOn_le_boostPolarIndex K _

/-- **Sub-boost data cost exactly one square more**: `κ(K(|a|) − c|a|^{−1/2}|b|) = κ(K) + 1`. -/
theorem negIndex_archGlue_eq_of_subBoost {K : posUnits → ℂ} (hK : IsHermKernel K) {c : ℝ}
    (hc : 0 < c) (lam : ℕ → posUnits)
    (hlam : Tendsto (fun N => ((((lam N : ℚˣ) : ℚ) : ℝ)) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0))
    (hgrow : ∀ u : posUnits, Tendsto (fun N => K (lam N * u) *
      (((((lam N : ℚˣ) : ℚ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) atTop (𝓝 0)) :
    negIndex (archGlue K c) = negIndex K + 1 := by
  rw [negIndex_archGlue_eq hK hc, boostPolarIndex_eq_negIndex_of_subBoost hK lam hlam hgrow]

end GaloisForLFunctions.AdelicKreinGeometry
