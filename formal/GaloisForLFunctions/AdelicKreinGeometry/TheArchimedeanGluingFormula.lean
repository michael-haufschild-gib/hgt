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

So the archimedean place glues by a hyperplane: the scalar gluing square of separable assemblies is
replaced by the codimension-one constraint that the dilation data be orthogonal to the boost.
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate Matrix
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

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
  rw [Real.rpow_neg (by positivity), Complex.ofReal_inv, div_eq_mul_inv]

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
    simpa using (Complex.continuous_ofReal.tendsto 0).comp hσ
  have hσsq : ∀ N : ℕ, σ N * σ N = ((N : ℝ) + 1)⁻¹ := fun N => by
    simp only [σ]
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  -- entries of the cross blocks
  have hneg0 : negAbsRat (Multiplicative.ofAdd 0) = 0 := by simp [negAbsRat, absRat]
  have hcross : ∀ k, Tendsto (fun N => (BWᴴ * C N * Sig N) k 0) atTop (𝓝 0) := by
    intro k
    have hent : ∀ N, (BWᴴ * C N * Sig N) k 0 =
        (σ N : ℂ) * (2 * ∑ i, conj (BW i k) * K ((u i)⁻¹)) := by
      intro N
      have hterm : ∀ i e, Φ ((D i)⁻¹ * T N e) = K ((u i)⁻¹) +
          (((((u i : ℚˣ) : ℚ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ((c : ℂ) * negAbsRat (Multiplicative.ofAdd (shiftOf (T N e)))) := fun i e => by
        simp only [Φ, archGlue_inv_mul, hDslope, hTslope, mul_one, hDpow, hTpow, hDshift, sub_zero]
        rw [Real.rpow_neg (by positivity)]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, C, Sig, Matrix.of_apply,
        Fin.sum_univ_two, hterm, Complex.star_def]
      have hsum : ∀ e, ∑ i, conj (BW i k) * (((((u i : ℚˣ) : ℚ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((c : ℂ) * negAbsRat (Multiplicative.ofAdd (shiftOf (T N e)))) = 0 := fun e => by
        rw [← sum_mul]
        have : ∑ i, conj (BW i k) * (((((u i : ℚˣ) : ℚ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
            conj (∑ i, BW i k * (((((u i : ℚˣ) : ℚ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
          rw [map_sum]; simp [Complex.conj_ofReal]
        rw [this, hBW k, map_zero, zero_mul]
      simp only [mul_add, sum_add_distrib, ← mul_assoc]
      rw [hsum 0, hsum 1]
      ring
    simp_rw [hent]
    simpa using hσc.mul_const (2 * ∑ i, conj (BW i k) * K ((u i)⁻¹))
  have hcross' : ∀ k, Tendsto (fun N => ((Sig N)ᴴ * C' N * BW) 0 k) atTop (𝓝 0) := by
    intro k
    have hent : ∀ N, ((Sig N)ᴴ * C' N * BW) 0 k =
        (σ N : ℂ) * (2 * ∑ i, K (u i) * BW i k) := by
      intro N
      have hterm : ∀ e i, Φ ((T N e)⁻¹ * D i) = K (u i) +
          (((((u i : ℚˣ) : ℚ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ((c : ℂ) * negAbsRat (Multiplicative.ofAdd (-shiftOf (T N e)))) := fun e i => by
        simp only [Φ, archGlue_inv_mul, hDslope, hTslope, inv_one, one_mul, hDpow, hTpow,
          hDshift, zero_sub]
        rw [Real.rpow_neg (by positivity)]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, C', Sig, Matrix.of_apply,
        Fin.sum_univ_two, hterm, Complex.star_def, Complex.conj_ofReal]
      have hsum : ∀ e, ∑ i, (((((u i : ℚˣ) : ℚ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((c : ℂ) * negAbsRat (Multiplicative.ofAdd (-shiftOf (T N e)))) * BW i k = 0 :=
        fun e => by
          have : ∀ i, (((((u i : ℚˣ) : ℚ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              ((c : ℂ) * negAbsRat (Multiplicative.ofAdd (-shiftOf (T N e)))) * BW i k =
              ((c : ℂ) * negAbsRat (Multiplicative.ofAdd (-shiftOf (T N e)))) *
                (BW i k * (((((u i : ℚˣ) : ℚ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := fun i => by ring
          simp_rw [this]
          rw [← mul_sum, hBW k, mul_zero]
      simp only [add_mul, sum_add_distrib, mul_add, mul_sum]
      simp only [← mul_sum]
      rw [hsum 0, hsum 1]
      simp only [mul_zero, add_zero]
      rw [show ∑ i, K (u i) * BW i k = ∑ i, K (u i) * BW i k from rfl]
      ring
    simp_rw [hent]
    simpa using hσc.mul_const (2 * ∑ i, K (u i) * BW i k)
  -- the pair block tends to `−2c`
  have hpair : Tendsto (fun N => ((Sig N)ᴴ * E N * Sig N) 0 0) atTop
      (𝓝 ((-2 * c : ℝ) : ℂ)) := by
    have hent : ∀ N, ((Sig N)ᴴ * E N * Sig N) 0 0 =
        ((σ N * σ N * (4 * (K 1).re) : ℝ) : ℂ) + (σ N * σ N : ℝ) * (4 * (K 1).im * I) -
          ((2 * c * (σ N * σ N * ((N : ℝ) + 1)) : ℝ) : ℂ) := by
      intro N
      have hT0 : T N 0 = 1 := rfl
      have hT1 : T N 1 = translation ((N : ℚ) + 1) := rfl
      have e00 : Φ ((T N 0)⁻¹ * T N 0) = K 1 := by
        rw [hT0, mul_one, inv_one]; simp [Φ, archGlue, conformalInduction, hneg0, slopeAbs]
      have e11 : Φ ((T N 1)⁻¹ * T N 1) = K 1 := by
        rw [inv_mul_cancel]; simp [Φ, archGlue, conformalInduction, hneg0, slopeAbs]
      have e01 : Φ ((T N 0)⁻¹ * T N 1) = K 1 - (c : ℂ) * ((N : ℂ) + 1) := by
        rw [hT0, inv_one, one_mul, hT1]
        simp only [Φ, archGlue, slopeAbs_translation, conformalInduction, slopePow_translation,
          inv_one, Complex.ofReal_one, one_mul, affShift_translation, negAbsRat, absRat,
          toAdd_ofAdd]
        show K 1 + (c : ℂ) * -(((|(N : ℚ) + 1| : ℚ)) : ℂ) = _
        rw [abs_of_nonneg (by positivity)]; push_cast; ring
      have e10 : Φ ((T N 1)⁻¹ * T N 0) = K 1 - (c : ℂ) * ((N : ℂ) + 1) := by
        rw [hT0, mul_one, hT1]
        have hinv : (translation ((N : ℚ) + 1))⁻¹ = translation (-((N : ℚ) + 1)) := by
          rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← translation_add, neg_add_cancel, translation_zero]
        rw [hinv]
        simp only [Φ, archGlue, slopeAbs_translation, conformalInduction, slopePow_translation,
          inv_one, Complex.ofReal_one, one_mul, affShift_translation, negAbsRat, absRat,
          toAdd_ofAdd]
        show K 1 + (c : ℂ) * -(((|-((N : ℚ) + 1)| : ℚ)) : ℂ) = _
        rw [abs_neg, abs_of_nonneg (by positivity)]; push_cast; ring
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, E, Sig, gram, Matrix.of_apply,
        Fin.sum_univ_two, Fin.sum_univ_one, e00, e11, e01, e10, Complex.star_def,
        Complex.conj_ofReal]
      rw [← Complex.re_add_im (K 1)]
      push_cast
      ring
    have h1 : Tendsto (fun N : ℕ => σ N * σ N * (4 * (K 1).re)) atTop (𝓝 0) := by
      simpa using (hσ.mul hσ).mul_const (4 * (K 1).re)
    have h2 : Tendsto (fun N : ℕ => ((σ N * σ N : ℝ) : ℂ) * (4 * (K 1).im * I)) atTop (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto 0).comp (hσ.mul hσ)
      simpa using this.mul_const (4 * (K 1).im * I)
    have h3 : ∀ N : ℕ, σ N * σ N * ((N : ℝ) + 1) = 1 := fun N => by
      rw [hσsq]; field_simp
    simp_rw [hent, h3]
    have := ((Complex.continuous_ofReal.tendsto 0).comp h1).add h2
    simpa using this.sub_const ((2 * c * 1 : ℝ) : ℂ)
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
    simp only [A, gram, Matrix.of_apply, Φ, archGlue_inv_mul, hDslope, hDshift, sub_self, hneg0,
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

end GaloisForLFunctions.AdelicKreinGeometry
