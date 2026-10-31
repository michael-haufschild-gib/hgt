import GaloisForLFunctions.AdelicKreinGeometry.TheGluingSquareIsSharp

/-!
# The stable gluing formula

The archimedean gluing at exponent `s`: glue dilation data `K` on `ℚ_{>0}` to the stable successor
`−c|b|^s`, `0 < s < 1`, through the boost `|a|^{−s/2}`:

  `Φ_{K,c}^{(s)}(x ↦ ax + b) = K(|a|) − c|a|^{−s/2}|b|^s`  (`archGlueAt`).

The glue is the stable boost coordinate `ℓ_s(w) = Σ w_i u_i^{−s/2}` (`boostMassAt`) and the
**stable boost-polar index** `κ^{(s/2)}(K)` counts the negative squares of `K` on `ℓ_s = 0`
(`boostPolarIndexAt`).

* **The stable gluing formula** (`negIndex_archGlueAt_eq`): `κ(Φ_{K,c}^{(s)}) = κ^{(s/2)}(K) + 1` for
  every Hermitian `K`, `c > 0`, `0 < s < 1`. Upper bound: on `ℓ_s = 0` the stable successor's form is
  nonnegative (Poisson subordination). Lower bound: a negative subspace of `K` on `ℓ_s = 0` on the
  dilations and the pair `1, x ↦ x + L` with weights `L^{−s/2}`, whose own form tends to `−2c`.
* **Sub-boost data** (`negIndex_archGlueAt_eq_of_subBoost`): if `‖K(λ_N u)‖ λ_N^{−s/2} → 0`, then
  `κ^{(s/2)}(K) = κ(K)` and the gluing costs exactly one square.
* **The absorbed pair moves with `s`** (`archGlueAt_stablePair`, `boostPolarIndexAt_stablePair`): the
  pair `u^{s/2} + u^{−s/2}` glued at exponent `s` is the stable pole–successor state, of index `1`,
  and its square is the boost coordinate itself: `κ^{(s/2)} = 0`. In the variable of the zeros the
  absorbed pair sits at `ρ = (1 ± s)/2`; only at the Hecke exponent `s = 1` is it the pole pair `{0, 1}`.
* **Zero configurations** (`negIndex_archGlueAt_orbitCorr`): for a tempered configuration all of whose
  points satisfy `Re ρ > (1 − s)/2`, the stable glued orbit kernel has index `κ(K_Z) + 1`.
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate Matrix
open Zeta23
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx cx_contDiff cx_hasCompactSupport)
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)
open GaloisForLFunctions.ArithmeticOrientationGeometry (seenRightZeros)

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

variable {s : ℝ}

theorem isHermKernel_negPowRat (s : ℝ) : IsHermKernel (negPowRat s) := fun m => by
  simp [negPowRat, toAdd_inv, abs_neg]

/-- The stable boost coordinate `ℓ_s(w) = Σ w_i u_i^{−s/2}` of a family of positive slopes. -/
def boostMassAt (s : ℝ) {n : ℕ} (u : Fin n → posUnits) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun w := ∑ i, w i * (((((u i : ℚˣ) : ℚ) : ℝ) ^ (-(s / 2)) : ℝ) : ℂ)
  map_add' w w' := by simp only [Pi.add_apply, add_mul, sum_add_distrib]
  map_smul' t w := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, mul_sum]

/-- **The stable boost-polar index**: negative squares of `K` on the hyperplanes `ℓ_s = 0`. -/
def boostPolarIndexAt (s : ℝ) (K : posUnits → ℂ) : ℕ∞ :=
  ⨆ (n : ℕ) (u : Fin n → posUnits), (negIndexOn (gram K u) (LinearMap.ker (boostMassAt s u)) : ℕ∞)

theorem negIndexOn_le_boostPolarIndexAt (K : posUnits → ℂ) {n : ℕ} (u : Fin n → posUnits) :
    (negIndexOn (gram K u) (LinearMap.ker (boostMassAt s u)) : ℕ∞) ≤ boostPolarIndexAt s K :=
  le_iSup₂ (f := fun n (u : Fin n → posUnits) =>
    (negIndexOn (gram K u) (LinearMap.ker (boostMassAt s u)) : ℕ∞)) n u

theorem boostPolarIndexAt_le_negIndex (K : posUnits → ℂ) : boostPolarIndexAt s K ≤ negIndex K :=
  iSup₂_le fun _ u =>
    (Nat.cast_le.mpr (negIndexOn_le_hermNegIndex _ _)).trans (hermNegIndex_gram_le_negIndex K u)

theorem negIndex_le_boostPolarIndexAt_add_one (K : posUnits → ℂ) :
    negIndex K ≤ boostPolarIndexAt s K + 1 :=
  negIndex_le_iff.mpr fun n u => by
    have h := hermNegIndex_le_negIndexOn_ker_add_one (gram K u) (boostMassAt s u)
    calc (hermNegIndex (gram K u) : ℕ∞)
        ≤ ((negIndexOn (gram K u) (LinearMap.ker (boostMassAt s u)) + 1 : ℕ) : ℕ∞) := Nat.cast_le.mpr h
      _ ≤ boostPolarIndexAt s K + 1 := by
          push_cast
          exact add_le_add (negIndexOn_le_boostPolarIndexAt K u) le_rfl

/-- **The stable archimedean gluing** `K(|a|) − c|a|^{−s/2}|b|^s`. -/
def archGlueAt (s : ℝ) (K : posUnits → ℂ) (c : ℝ) (g : AffineGroupQ) : ℂ :=
  K (slopeAbs g) + conformalInduction Rat.AbsoluteValue.real s (fun m => (c : ℂ) * negPowRat s m) g

theorem slopePow_real_eq_at (g : AffineGroupQ) :
    slopePow Rat.AbsoluteValue.real s g = ((((slopeAbs g : ℚˣ) : ℚ) : ℝ)) ^ (s / 2) := by
  simp [slopePow, slopeAbs, absUnit, slopeUnit, Rat.AbsoluteValue.real_eq_abs]
  rfl

/-- The boost weights carry the boost coordinate as their total mass. -/
theorem sum_boostWeights_eq_at {n : ℕ} (g : Fin n → AffineGroupQ) (w : Fin n → ℂ) :
    ∑ a, boostWeights Rat.AbsoluteValue.real s g w a = boostMassAt s (fun a => slopeAbs (g a)) w := by
  simp only [boostWeights, boostMassAt, LinearMap.coe_mk, AddHom.coe_mk, slopePow_real_eq_at]
  refine sum_congr rfl fun a _ => ?_
  rw [Real.rpow_neg (posUnits_val_pos _).le, Complex.ofReal_inv, div_eq_mul_inv]

/-- **The Gram identity**: `K`'s form at the slopes plus the successor's form at the shifts. -/
theorem hermQuad_gram_archGlueAt (K : posUnits → ℂ) (c : ℝ) {n : ℕ} (g : Fin n → AffineGroupQ)
    (w : Fin n → ℂ) :
    hermQuad (gram (archGlueAt s K c) g) w = hermQuad (gram K fun a => slopeAbs (g a)) w +
      hermQuad (gram (fun m => (c : ℂ) * negPowRat s m) (shifts g))
        (boostWeights Rat.AbsoluteValue.real s g w) := by
  have e : gram (archGlueAt s K c) g = gram (fun x => K (slopeAbs x)) g +
      gram (conformalInduction Rat.AbsoluteValue.real s (fun m => (c : ℂ) * negPowRat s m)) g := by
    ext a b; simp [gram, archGlueAt]
  rw [e, HeckeKreinToeplitz.hermQuad_add, gram_comp_slopeAbs,
    hermQuad_gram_conformalInduction (isConformal_negPowRat c)]

/-- **Upper bound**: `κ(Φ^{(s)}_{K,c}) ≤ κ^{(s/2)}(K) + 1`. -/
theorem negIndex_archGlueAt_le (hs0 : 0 < s) (hs1 : s < 1) (K : posUnits → ℂ) {c : ℝ} (hc : 0 ≤ c) :
    negIndex (archGlueAt s K c) ≤ boostPolarIndexAt s K + 1 := by
  refine negIndex_le_iff.mpr fun n g => ?_
  set u : Fin n → posUnits := fun a => slopeAbs (g a)
  have h1 := hermNegIndex_le_negIndexOn_ker_add_one (gram (archGlueAt s K c) g) (boostMassAt s u)
  have h2 : negIndexOn (gram (archGlueAt s K c) g) (LinearMap.ker (boostMassAt s u)) ≤
      negIndexOn (gram K u) (LinearMap.ker (boostMassAt s u)) :=
    negIndexOn_le_of_hermQuad_le fun w hw => by
      rw [hermQuad_gram_archGlueAt]
      have hmass : ∑ a, boostWeights Rat.AbsoluteValue.real s g w a = 0 := by
        rw [sum_boostWeights_eq_at]; exact LinearMap.mem_ker.mp hw
      linarith [hermQuad_gram_ofReal_mul_nonneg hc (shifts g) _
        (hermQuad_gram_negPowRat_nonneg hs0 hs1 (shifts g) _ hmass)]
  calc (hermNegIndex (gram (archGlueAt s K c) g) : ℕ∞)
      ≤ ((negIndexOn (gram (archGlueAt s K c) g) (LinearMap.ker (boostMassAt s u)) + 1 : ℕ) : ℕ∞) :=
        Nat.cast_le.mpr h1
    _ ≤ boostPolarIndexAt s K + 1 := by
        push_cast
        exact add_le_add ((Nat.cast_le.mpr h2).trans (negIndexOn_le_boostPolarIndexAt K u)) le_rfl

/-! ### The lower bound -/

theorem archGlueAt_inv_mul (K : posUnits → ℂ) (c : ℝ) (g h : AffineGroupQ) :
    archGlueAt s K c (g⁻¹ * h) = K ((slopeAbs g)⁻¹ * slopeAbs h) +
      (((slopePow Rat.AbsoluteValue.real s g * slopePow Rat.AbsoluteValue.real s h)⁻¹ : ℝ) : ℂ) *
        ((c : ℂ) * negPowRat s (Multiplicative.ofAdd (shiftOf h - shiftOf g))) := by
  rw [archGlueAt, conformalInduction_inv_mul (isConformal_negPowRat c), map_mul, map_inv]

/-- **Lower bound**: every negative subspace of `K` on `ℓ_s = 0` survives next to one square of the
stable successor. -/
theorem add_one_le_negIndex_archGlueAt (hs0 : 0 < s) {K : posUnits → ℂ} (hK : IsHermKernel K)
    {c : ℝ} (hc : 0 < c)
    {m : ℕ} (u : Fin m → posUnits) :
    (negIndexOn (gram K u) (LinearMap.ker (boostMassAt s u)) : ℕ∞) + 1 ≤ negIndex (archGlueAt s K c) := by
  classical
  obtain ⟨W, hWV, hWr, hW⟩ := exists_negIndexOn (gram K u) (LinearMap.ker (boostMassAt s u))
  set r := Module.finrank ℂ W
  set bW := Module.finBasis ℂ W
  set BW : Matrix (Fin m) (Fin r) ℂ := Matrix.of fun i k => (bW k : Fin m → ℂ) i
  have hBW : ∀ k, ∑ i, BW i k * (((((u i : ℚˣ) : ℚ) : ℝ) ^ (-(s / 2)) : ℝ) : ℂ) = 0 :=
    fun k => LinearMap.mem_ker.mp (hWV (bW k).2)
  set Φ := archGlueAt s K c
  set D : Fin m → AffineGroupQ := fun i => dilation ((u i : posUnits) : ℚˣ)
  have hDslope : ∀ i, slopeAbs (D i) = u i := fun i => slopeAbs_dilation _
  have hDshift : ∀ i, shiftOf (D i) = 0 := fun i => affShift_dilation _
  have hDpow : ∀ i, slopePow Rat.AbsoluteValue.real s (D i) =
      ((((u i : ℚˣ) : ℚ) : ℝ)) ^ (s / 2) := fun i => by rw [slopePow_real_eq_at, hDslope]
  -- the translation pair `1, x ↦ x + (N + 1)`
  set T : ℕ → Fin 2 → AffineGroupQ := fun N => ![1, translation ((N : ℚ) + 1)]
  have hTslope : ∀ N e, slopeAbs (T N e) = 1 := fun N e => by
    fin_cases e
    · simp [T]
    · simp [T, slopeAbs_translation]
  have hTpow : ∀ N e, slopePow Rat.AbsoluteValue.real s (T N e) = 1 := fun N e => by
    fin_cases e
    · simp [T, slopePow_one]
    · exact slopePow_translation _ _ _
  set σ : ℕ → ℝ := fun N => ((N : ℝ) + 1) ^ (-(s / 2))
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
  have hσ : Tendsto (fun N : ℕ => σ N) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < s / 2)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hσc : Tendsto (fun N : ℕ => ((σ N : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp hσ
  have hσsq : ∀ N : ℕ, σ N * σ N * ((N : ℝ) + 1) ^ s = 1 := fun N => by
    simp only [σ]
    rw [← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity)]
    ring_nf
    exact Real.rpow_zero _
  have hneg0 : negPowRat s (Multiplicative.ofAdd 0) = 0 := by
    simp [negPowRat, Real.zero_rpow hs0.ne']
  -- the boost coordinates `ρ_i = u_i^{−s/2}`; the basis of `W` has `ℓ_s = 0`
  set ρ : Fin m → ℂ := fun i => (((((u i : ℚˣ) : ℚ) : ℝ) ^ (-(s / 2)) : ℝ) : ℂ)
  have hzero : ∀ k, ∑ i, conj (BW i k) * ρ i = 0 := fun k => by
    have h := congrArg conj (hBW k)
    rw [map_sum, map_zero] at h
    rw [← h]
    refine sum_congr rfl fun i _ => ?_
    simp [ρ, Complex.conj_ofReal]
  have hzero' : ∀ k, ∑ i, ρ i * BW i k = 0 := fun k => by
    rw [← hBW k]; exact sum_congr rfl fun i _ => mul_comm _ _
  have hρ : ∀ i, (((slopePow Rat.AbsoluteValue.real s (D i))⁻¹ : ℝ) : ℂ) = ρ i := fun i => by
    rw [hDpow, ← Real.rpow_neg (posUnits_val_pos _).le]
  -- entries of the cross blocks
  have hcross : ∀ k, Tendsto (fun N => (BWᴴ * C N * Sig N) k 0) atTop (𝓝 0) := by
    intro k
    have hent : ∀ N, (BWᴴ * C N * Sig N) k 0 =
        (σ N : ℂ) * (2 * ∑ i, conj (BW i k) * K ((u i)⁻¹)) := by
      intro N
      have hterm : ∀ i e, Φ ((D i)⁻¹ * T N e) = K ((u i)⁻¹) +
          ((c : ℂ) * negPowRat s (Multiplicative.ofAdd (shiftOf (T N e)))) * ρ i := fun i e => by
        simp only [Φ, archGlueAt_inv_mul, hDslope, hTslope, mul_one, hTpow, hDshift, sub_zero]
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
    have h2 := isHermKernel_conformalInduction (isConformal_negPowRat c)
      (isHermKernel_ofReal_mul (isHermKernel_negPowRat s) c)
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
        ((σ N * σ N : ℝ) : ℂ) * (4 * K 1) -
          ((2 * c * (σ N * σ N * ((N : ℝ) + 1) ^ s) : ℝ) : ℂ) := by
      intro N
      have hsp : slopePow Rat.AbsoluteValue.real s (translation ((N : ℚ) + 1)) = 1 :=
        slopePow_translation _ _ _
      have hsp' : slopePow Rat.AbsoluteValue.real s (translation (-((N : ℚ) + 1))) = 1 :=
        slopePow_translation _ _ _
      have hsh : shiftOf (translation ((N : ℚ) + 1)) = (N : ℚ) + 1 := affShift_translation _
      have hsh' : shiftOf (translation (-((N : ℚ) + 1))) = -((N : ℚ) + 1) := affShift_translation _
      have hinv : (translation ((N : ℚ) + 1))⁻¹ = translation (-((N : ℚ) + 1)) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← translation_add, neg_add_cancel, translation_zero]
      have e00 : Φ 1 = K 1 := by
        simp only [Φ, archGlueAt, map_one, conformalInduction, shiftOf_one, hneg0,
          mul_zero, add_zero]
      have e01 : Φ (translation ((N : ℚ) + 1)) =
          K 1 - (c : ℂ) * ((((N : ℝ) + 1) ^ s : ℝ) : ℂ) := by
        simp only [Φ, archGlueAt, slopeAbs_translation, conformalInduction, hsp, hsh, inv_one,
          Complex.ofReal_one, one_mul, negPowRat, toAdd_ofAdd]
        rw [show (((N : ℚ) + 1 : ℚ) : ℝ) = (N : ℝ) + 1 by push_cast; rfl,
          abs_of_nonneg (by positivity)]
        ring
      have e10 : Φ (translation (-((N : ℚ) + 1))) =
          K 1 - (c : ℂ) * ((((N : ℝ) + 1) ^ s : ℝ) : ℂ) := by
        simp only [Φ, archGlueAt, slopeAbs_translation, conformalInduction, hsp', hsh', inv_one,
          Complex.ofReal_one, one_mul, negPowRat, toAdd_ofAdd]
        rw [show ((-((N : ℚ) + 1) : ℚ) : ℝ) = -((N : ℝ) + 1) by push_cast; rfl, abs_neg,
          abs_of_nonneg (by positivity)]
        ring
      have e11 : Φ (translation (-((N : ℚ) + 1)) * translation ((N : ℚ) + 1)) = K 1 := by
        rw [← translation_add, neg_add_cancel, translation_zero, e00]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, E, Sig, gram, T, Matrix.of_apply,
        Fin.sum_univ_two, Complex.star_def, Complex.conj_ofReal,
        Matrix.cons_val_zero, Matrix.cons_val_one, inv_one, one_mul, mul_one,
        hinv, e00, e01, e10, e11]
      push_cast
      ring
    simp_rw [hent, hσsq]
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
    simp only [A, gram, Φ, archGlueAt_inv_mul, hDslope, hDshift, sub_self, hneg0,
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
  calc (negIndexOn (gram K u) (LinearMap.ker (boostMassAt s u)) : ℕ∞) + 1
      = ((r + 1 : ℕ) : ℕ∞) := by push_cast; rw [hWr]
    _ ≤ negIndex Φ := (Nat.cast_le.mpr hfinal).trans hfin

/-- **The stable gluing formula**: `κ(K(|a|) − c|a|^{−s/2}|b|^s) = κ^{(s/2)}(K) + 1`. -/
theorem negIndex_archGlueAt_eq (hs0 : 0 < s) (hs1 : s < 1) {K : posUnits → ℂ} (hK : IsHermKernel K)
    {c : ℝ} (hc : 0 < c) : negIndex (archGlueAt s K c) = boostPolarIndexAt s K + 1 := by
  refine le_antisymm (negIndex_archGlueAt_le hs0 hs1 K hc.le) ?_
  rcases eq_or_ne (negIndex (archGlueAt s K c)) ⊤ with htop | htop
  · rw [htop]; exact le_top
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp htop
  have hfam : ∀ (m : ℕ) (u : Fin m → posUnits),
      negIndexOn (gram K u) (LinearMap.ker (boostMassAt s u)) + 1 ≤ M := fun m u => by
    have h := add_one_le_negIndex_archGlueAt hs0 hK hc u
    rw [← hM] at h
    exact_mod_cast h
  have h1 : 1 ≤ M := by have := hfam 0 (fun i => i.elim0); omega
  have hall : ∀ (m : ℕ) (u : Fin m → posUnits),
      (negIndexOn (gram K u) (LinearMap.ker (boostMassAt s u)) : ℕ∞) ≤ ((M - 1 : ℕ) : ℕ∞) :=
    fun m u => Nat.cast_le.mpr (by have := hfam m u; omega)
  calc boostPolarIndexAt s K + 1 ≤ ((M - 1 : ℕ) : ℕ∞) + 1 := add_le_add (iSup₂_le hall) le_rfl
    _ = negIndex (archGlueAt s K c) := by
        rw [← hM]; norm_cast; omega

/-! ### Sub-boost dilation data -/

/-- **Sub-boost data are glued at full index.** If along slopes `λ_N` with `λ_N^{−s/2} → 0` the
data grow slower than the stable boost, `‖K(λ_N u)‖ λ_N^{−s/2} → 0`, then `κ^{(s/2)}(K) = κ(K)`: a
negative family dilated by `λ_N` and corrected at the slope `1` by `−λ_N^{−s/2} ℓ_s` lies on
`ℓ_s = 0`, and its compressed Gram matrices tend to the original ones. -/
theorem boostPolarIndexAt_eq_negIndex_of_subBoost {K : posUnits → ℂ} (hK : IsHermKernel K)
    (lam : ℕ → posUnits)
    (hlam : Tendsto (fun N => ((((lam N : ℚˣ) : ℚ) : ℝ)) ^ (-(s / 2))) atTop (𝓝 0))
    (hgrow : ∀ u : posUnits, Tendsto (fun N => K (lam N * u) *
      (((((lam N : ℚˣ) : ℚ) : ℝ) ^ (-(s / 2)) : ℝ) : ℂ)) atTop (𝓝 0)) :
    boostPolarIndexAt s K = negIndex K := by
  classical
  refine le_antisymm (boostPolarIndexAt_le_negIndex K) (negIndex_le_iff.mpr fun n F => ?_)
  set μ : ℕ → ℝ := fun N => ((((lam N : ℚˣ) : ℚ) : ℝ)) ^ (-(s / 2))
  set ρ : Fin n → ℝ := fun i => ((((F i : ℚˣ) : ℚ) : ℝ)) ^ (-(s / 2))
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
  have hroot : ∀ i, (((((lam N * F i : posUnits) : ℚˣ) : ℚ) : ℝ)) ^ (-(s / 2)) = μ N * ρ i :=
    fun i => by
      simp only [Subgroup.coe_mul, Units.val_mul, Rat.cast_mul, μ, ρ]
      exact Real.mul_rpow (posUnits_val_pos _).le (posUnits_val_pos _).le
  have hV : ∀ a, L' a ∈ LinearMap.ker (boostMassAt s (Fam N)) := fun a => by
    rw [LinearMap.mem_ker]
    simp only [L', boostMassAt, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp,
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
    _ ≤ (negIndexOn (gram K (Fam N)) (LinearMap.ker (boostMassAt s (Fam N))) : ℕ∞) :=
        Nat.cast_le.mpr (h2 ▸ h1)
    _ ≤ boostPolarIndexAt s K := negIndexOn_le_boostPolarIndexAt K _

/-- **Sub-boost data cost exactly one square more**: `κ(K(|a|) − c|a|^{−s/2}|b|^s) = κ(K) + 1`. -/
theorem negIndex_archGlueAt_eq_of_subBoost (hs0 : 0 < s) (hs1 : s < 1) {K : posUnits → ℂ}
    (hK : IsHermKernel K) {c : ℝ}
    (hc : 0 < c) (lam : ℕ → posUnits)
    (hlam : Tendsto (fun N => ((((lam N : ℚˣ) : ℚ) : ℝ)) ^ (-(s / 2))) atTop (𝓝 0))
    (hgrow : ∀ u : posUnits, Tendsto (fun N => K (lam N * u) *
      (((((lam N : ℚˣ) : ℚ) : ℝ) ^ (-(s / 2)) : ℝ) : ℂ)) atTop (𝓝 0)) :
    negIndex (archGlueAt s K c) = negIndex K + 1 := by
  rw [negIndex_archGlueAt_eq hs0 hs1 hK hc,
    boostPolarIndexAt_eq_negIndex_of_subBoost hK lam hlam hgrow]

/-! ### The gluing square is at most one -/

theorem archGlueAt_dilation (hs0 : 0 < s) (K : posUnits → ℂ) (c : ℝ) (u : posUnits) :
    archGlueAt s K c (dilation u) = K u := by
  have h0 : shiftOf (dilation (u : ℚˣ)) = 0 := affShift_dilation _
  simp [archGlueAt, slopeAbs_dilation, conformalInduction, h0, negPowRat, Real.zero_rpow hs0.ne']

/-- **The stable gluing square is at most one**: `κ(K) ≤ κ(Φ^{(s)}_{K,c}) ≤ κ(K) + 1`. -/
theorem negIndex_archGlueAt_eq_or (hs0 : 0 < s) (hs1 : s < 1) (K : posUnits → ℂ) {c : ℝ}
    (hc : 0 ≤ c) :
    negIndex (archGlueAt s K c) = negIndex K ∨ negIndex (archGlueAt s K c) = negIndex K + 1 := by
  have e : archGlueAt s K c ∘ (dilation.comp posUnits.subtype) = K :=
    funext fun u => archGlueAt_dilation hs0 K c u
  have h1 : negIndex K ≤ negIndex (archGlueAt s K c) :=
    calc negIndex K = negIndex (archGlueAt s K c ∘ (dilation.comp posUnits.subtype)) := by rw [e]
      _ ≤ _ := negIndex_comp_le _ _
  have h2 := (negIndex_archGlueAt_le hs0 hs1 K hc).trans
    (add_le_add (boostPolarIndexAt_le_negIndex (s := s) K) le_rfl)
  generalize negIndex (archGlueAt s K c) = x at h1 h2 ⊢
  generalize negIndex K = y at h1 h2 ⊢
  induction y using ENat.recTopCoe with
  | top => exact Or.inl (top_le_iff.mp h1)
  | coe m =>
    induction x using ENat.recTopCoe with
    | top => exact absurd (top_le_iff.mp h2) (by exact_mod_cast ENat.coe_ne_top (m + 1))
    | coe n =>
      have h1' : m ≤ n := by exact_mod_cast h1
      have h2' : n ≤ m + 1 := by exact_mod_cast h2
      rcases (show n = m ∨ n = m + 1 by omega) with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h]; push_cast; rfl)

/-! ### The absorbed pair moves with the exponent -/

/-- The stable pair `u^{s/2} + u^{−s/2}`: the characters `u^{1/2−ρ}` at `ρ = (1 ∓ s)/2`. -/
def stablePair (s : ℝ) (u : posUnits) : ℂ :=
  (((((u : ℚˣ) : ℚ) : ℝ) ^ (s / 2) + ((((u : ℚˣ) : ℚ) : ℝ) ^ (s / 2))⁻¹ : ℝ) : ℂ)

/-- Glued at exponent `s`, the stable pair is the stable pole–successor state. -/
theorem archGlueAt_stablePair (c : ℝ) :
    archGlueAt s (stablePair s) c =
      poleSuccessor Rat.AbsoluteValue.real s fun m => (c : ℂ) * negPowRat s m := by
  funext g
  simp only [archGlueAt, poleSuccessor, stablePair, slopePow_real_eq_at]

theorem stablePair_inv (u : posUnits) : stablePair s u⁻¹ = stablePair s u := by
  simp only [stablePair, InvMemClass.coe_inv, Units.val_inv_eq_inv_val, Rat.cast_inv]
  rw [Real.inv_rpow (posUnits_val_pos u).le, inv_inv, add_comm]

theorem isHermKernel_stablePair : IsHermKernel (stablePair s) := fun u => by
  rw [stablePair_inv, stablePair, Complex.conj_ofReal]

/-- **The stable pair has one square, and gluing at exponent `s` keeps it.** -/
theorem negIndex_stablePair (hs0 : 0 < s) (hs1 : s < 1) : negIndex (stablePair s) = 1 := by
  refine le_antisymm ?_ ?_
  · have e : archGlueAt s (stablePair s) 1 ∘ (dilation.comp posUnits.subtype) = stablePair s :=
      funext fun u => archGlueAt_dilation hs0 _ 1 u
    calc negIndex (stablePair s)
        = negIndex (archGlueAt s (stablePair s) 1 ∘ (dilation.comp posUnits.subtype)) := by rw [e]
      _ ≤ negIndex (archGlueAt s (stablePair s) 1) := negIndex_comp_le _ _
      _ = 1 := by rw [archGlueAt_stablePair, negIndex_poleSuccessor_negPowRat hs0 hs1 zero_le_one]
  · -- slopes `1, 4` with weights `1, −1`: `4 − 2(t + 1/t) < 0`, `t = 4^{s/2} > 1`
    set t : ℝ := (((posFour : ℚˣ) : ℚ) : ℝ) ^ (s / 2)
    have ht : 1 < t := Real.one_lt_rpow (by norm_num [posFour]) (by linarith)
    have h1 : stablePair s 1 = ((2 : ℝ) : ℂ) := by rw [stablePair]; norm_num
    have h4 : stablePair s posFour = ((t + t⁻¹ : ℝ) : ℂ) := rfl
    have hneg : hermQuad (gram (stablePair s) ![1, posFour]) ![1, -1] < 0 := by
      rw [hermQuad_gram]
      simp [Fin.sum_univ_two, stablePair_inv, h1, h4]
      have ht0 : 0 < t := by linarith
      have : 2 < t + t⁻¹ := by
        rw [← sub_pos]
        have : t + t⁻¹ - 2 = (t - 1) ^ 2 / t := by field_simp; ring
        rw [this]; exact div_pos (by nlinarith) ht0
      linarith
    have h1' := one_le_negIndexOn (V := ⊤) Submodule.mem_top hneg
    exact le_trans (by exact_mod_cast h1'.trans (negIndexOn_le_hermNegIndex _ ⊤))
      (hermNegIndex_gram_le_negIndex (stablePair s) _)

/-- The form of the stable pair is `2Re(ℓ̄_s m_s)`; it vanishes on the stable boost hyperplane. -/
theorem hermQuad_gram_stablePair_of_boostMass {n : ℕ} (u : Fin n → posUnits) {w : Fin n → ℂ}
    (hw : boostMassAt s u w = 0) : hermQuad (gram (stablePair s) u) w = 0 := by
  set D : Fin n → AffineGroupQ := fun a => dilation (u a : ℚˣ)
  have hD : (fun a => slopeAbs (D a)) = u := funext fun a => slopeAbs_dilation (u a)
  have e : gram (stablePair s) u = gram (fun x => ((slopePow Rat.AbsoluteValue.real s x +
      (slopePow Rat.AbsoluteValue.real s x)⁻¹ : ℝ) : ℂ)) D := by
    rw [← hD, ← gram_comp_slopeAbs]
    simp only [stablePair, slopePow_real_eq_at]
  have hmass : ∑ a, boostWeights Rat.AbsoluteValue.real s D w a = 0 := by
    rw [sum_boostWeights_eq_at, hD]; exact hw
  rw [e, hermQuad_gram_boostPair, hmass]
  simp

/-- **The stable pair is absorbed**: `κ^{(s/2)}(u^{s/2} + u^{−s/2}) = 0`. -/
theorem boostPolarIndexAt_stablePair (hs0 : 0 < s) : boostPolarIndexAt s (stablePair s) = 0 :=
  nonpos_iff_eq_zero.mp (iSup₂_le fun n u => by
    rw [negIndexOn_eq_zero_of_nonneg fun w hw =>
      (hermQuad_gram_stablePair_of_boostMass u (LinearMap.mem_ker.mp hw)).ge]
    rfl)

/-- **Blindness to the absorbed pair**: `κ^{(s/2)}(K + t·(u^{s/2} + u^{−s/2})) = κ^{(s/2)}(K)`. -/
theorem boostPolarIndexAt_add_stablePair (K : posUnits → ℂ) (t : ℝ) :
    boostPolarIndexAt s (fun u => K u + t * stablePair s u) = boostPolarIndexAt s K := by
  have key : ∀ {n : ℕ} (u : Fin n → posUnits), ∀ w ∈ LinearMap.ker (boostMassAt s u),
      hermQuad (gram (fun v => K v + t * stablePair s v) u) w = hermQuad (gram K u) w :=
    fun u w hw => by
      have e : gram (fun v => (t : ℂ) * stablePair s v) u = (t : ℂ) • gram (stablePair s) u := by
        ext a b; simp [gram]
      rw [hermQuad_gram_add, e, hermQuad_smul,
        hermQuad_gram_stablePair_of_boostMass u (LinearMap.mem_ker.mp hw), mul_zero, add_zero]
  simp only [boostPolarIndexAt]
  refine iSup_congr fun n => iSup_congr fun u => ?_
  exact congrArg _ (le_antisymm (negIndexOn_le_of_hermQuad_le fun w hw => (key u w hw).ge)
    (negIndexOn_le_of_hermQuad_le fun w hw => (key u w hw).le))

theorem isHermKernel_add_stablePair {K : posUnits → ℂ} (hK : IsHermKernel K) (t : ℝ) :
    IsHermKernel fun u => K u + t * stablePair s u := fun u => by
  show K u⁻¹ + t * stablePair s u⁻¹ = conj (K u + t * stablePair s u)
  rw [hK u, isHermKernel_stablePair u, map_add, map_mul, Complex.conj_ofReal]

/-- **The stable glue is blind to the pair at `(1 ± s)/2`.** -/
theorem negIndex_archGlueAt_add_stablePair (hs0 : 0 < s) (hs1 : s < 1) {K : posUnits → ℂ}
    (hK : IsHermKernel K) (t : ℝ) {c : ℝ} (hc : 0 < c) :
    negIndex (archGlueAt s (fun u => K u + t * stablePair s u) c) =
      negIndex (archGlueAt s K c) := by
  rw [negIndex_archGlueAt_eq hs0 hs1 (isHermKernel_add_stablePair hK t) hc,
    negIndex_archGlueAt_eq hs0 hs1 hK hc, boostPolarIndexAt_add_stablePair]

/-! ### Zero configurations -/

section Orbit

variable {Z : ZeroConfig} {f : ℝ → ℝ}

theorem tendsto_twoPos_pow_rpow_at (hs0 : 0 < s) :
    Tendsto (fun N : ℕ => ((((twoPos ^ N : posUnits) : ℚˣ) : ℚ) : ℝ) ^ (-(s / 2))) atTop
      (𝓝 0) := by
  have e : ∀ N : ℕ, ((((twoPos ^ N : posUnits) : ℚˣ) : ℚ) : ℝ) ^ (-(s / 2)) =
      ((2 : ℝ) ^ (-(s / 2))) ^ N := fun N => by
    rw [twoPos_pow_val, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
  simp_rw [e]
  refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

/-- **Orbit kernels grow slower than the stable boost** when every zero has `Re ρ > (1 − s)/2`:
`K(2^N u) 2^{−Ns/2} → 0`, since `u^{−s/2}|u^{1/2−ρ}| = u^{(1−s)/2 − Re ρ}`. -/
theorem orbitCorr_subBoostAt (hZ : TemperedConfig Z)
    (hf : f ∈ ArithmeticCastelnuovoSeveri.realTests)
    (hpos : ∀ ρ : Z.carrier, (1 - s) / 2 < (ρ : ℂ).re) (u : posUnits) :
    Tendsto (fun N : ℕ => orbitCorr Z f (twoPos ^ N * u) *
      (((((((twoPos ^ N : posUnits) : ℚˣ) : ℚ) : ℝ)) ^ (-(s / 2)) : ℝ) : ℂ)) atTop (𝓝 0) := by
  have hsum : Summable fun ρ : Z.carrier => ‖orbitWeight Z f ρ‖ :=
    ArithmeticCastelnuovoSeveri.summable_norm_Wsummand _ hZ (cx_contDiff hf.1)
      (cx_hasCompactSupport hf.2) (cx_contDiff hf.1) (cx_hasCompactSupport hf.2)
  set a : ℝ := Real.log (((u : ℚˣ) : ℚ) : ℝ)
  have hu : (0 : ℝ) < (((u : ℚˣ) : ℚ) : ℝ) := posUnits_val_pos u
  set F : ℕ → Z.carrier → ℂ := fun N ρ =>
    cexp (-(((N : ℝ) * Real.log 2 + a : ℝ) : ℂ) * ((ρ : ℂ) - 1 / 2)) * orbitWeight Z f ρ *
      ((Real.exp (-((N : ℝ) * Real.log 2) * (s / 2)) : ℝ) : ℂ)
  have hterm : ∀ N, orbitCorr Z f (twoPos ^ N * u) *
      (((((((twoPos ^ N : posUnits) : ℚˣ) : ℚ) : ℝ)) ^ (-(s / 2)) : ℝ) : ℂ) =
      ∑' ρ, F N ρ := by
    intro N
    have hlog : Real.log (((((twoPos ^ N * u : posUnits) : ℚˣ) : ℚ) : ℝ)) =
        (N : ℝ) * Real.log 2 + a := by
      have : ((((twoPos ^ N * u : posUnits) : ℚˣ) : ℚ) : ℝ) =
          (2 : ℝ) ^ N * (((u : ℚˣ) : ℚ) : ℝ) := by
        rw [← twoPos_pow_val]; push_cast; rfl
      rw [this, Real.log_mul (by positivity) hu.ne', Real.log_pow]
    have hpow : ((((twoPos ^ N : posUnits) : ℚˣ) : ℚ) : ℝ) ^ (-(s / 2)) =
        Real.exp (-((N : ℝ) * Real.log 2) * (s / 2)) := by
      rw [twoPos_pow_val, Real.rpow_def_of_pos (by positivity), Real.log_pow]
      congr 1; ring
    rw [orbitCorr_eq_tsum, hlog, hpow, ← tsum_mul_right]
  have hnorm : ∀ N ρ, ‖F N ρ‖ =
      Real.exp (-((N : ℝ) * Real.log 2) * ((ρ : ℂ).re - (1 - s) / 2) - a * ((ρ : ℂ).re - 1 / 2)) *
        ‖orbitWeight Z f ρ‖ := by
    intro N ρ
    simp only [F, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    rw [mul_right_comm, ← Real.exp_add]
    congr 2
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.div_ofNat_re,
      Complex.div_ofNat_im, Complex.one_im]
    ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbound : ∀ N ρ, ‖F N ρ‖ ≤ Real.exp (|a| / 2) * ‖orbitWeight Z f ρ‖ := by
    intro N ρ
    rw [hnorm]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have h0 := hpos ρ
    have h1 := (Z.strip ρ ρ.2).1
    have h2 := (Z.strip ρ ρ.2).2
    have hN : 0 ≤ (N : ℝ) * Real.log 2 := by positivity
    have : -(a * ((ρ : ℂ).re - 1 / 2)) ≤ |a| / 2 := by
      have habs : |a * ((ρ : ℂ).re - 1 / 2)| ≤ |a| * (1 / 2) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_nonneg _)
      linarith [neg_abs_le (a * ((ρ : ℂ).re - 1 / 2))]
    nlinarith
  have hlim : ∀ ρ, Tendsto (fun N => F N ρ) atTop (𝓝 0) := by
    intro ρ
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [hnorm]
    have h0 := hpos ρ
    have : Tendsto (fun N : ℕ => -((N : ℝ) * Real.log 2) * ((ρ : ℂ).re - (1 - s) / 2) -
        a * ((ρ : ℂ).re - 1 / 2)) atTop atBot := by
      refine tendsto_atBot_add_const_right _ _ ?_
      have : Tendsto (fun N : ℕ => (N : ℝ) * (Real.log 2 * ((ρ : ℂ).re - (1 - s) / 2))) atTop
          atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const (mul_pos hlog2 (by linarith))
      refine (tendsto_neg_atTop_atBot.comp this).congr fun N => ?_
      simp only [Function.comp_apply]; ring
    simpa using (Real.tendsto_exp_atBot.comp this).mul_const ‖orbitWeight Z f ρ‖
  simp_rw [hterm]
  have := tendsto_tsum_of_dominated_convergence (hsum.mul_left (Real.exp (|a| / 2)))
    hlim (Eventually.of_forall hbound)
  simpa using this

/-- **The stable archimedean state of a zero configuration counts its zeros** when every zero has
`Re ρ > (1 − s)/2`: `κ(K_f(|a|) − c|a|^{−s/2}|b|^s) = #{zeros right of the line seen by f} + 1`. -/
theorem negIndex_archGlueAt_orbitCorr (hs0 : 0 < s) (hs1 : s < 1) (hZ : TemperedConfig Z)
    (hf : f ∈ ArithmeticCastelnuovoSeveri.realTests)
    (hpos : ∀ ρ : Z.carrier, (1 - s) / 2 < (ρ : ℂ).re) {c : ℝ} (hc : 0 < c) :
    negIndex (archGlueAt s (orbitCorr Z f) c) = (seenRightZeros Z f).encard + 1 := by
  have hK : IsHermKernel (orbitCorr Z f) := (isHermKernel_orbitKernel Z f).comp _
  rw [negIndex_archGlueAt_eq hs0 hs1 hK hc,
    boostPolarIndexAt_eq_negIndex_of_subBoost hK (fun N => twoPos ^ N)
      (tendsto_twoPos_pow_rpow_at hs0) (orbitCorr_subBoostAt hZ hf hpos), orbitCorr,
    negIndex_comp_of_surjective _ _ posUnitsToHecke_surjective, negIndex_orbitKernel Z hZ hf]

end Orbit

end GaloisForLFunctions.AdelicKreinGeometry
