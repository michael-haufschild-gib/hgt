import GaloisForLFunctions.AdelicKreinGeometry.TheStableGluingFormula
import GaloisForLFunctions.AdelicKreinGeometry.EveryPlaceCarriesAPoleSuccessorState

/-!
# The gluing formula at every place

Glue dilation data `K` on `ℚ_{>0}` to a successor `ψ` at a place `v` of `ℚ` through the boost
`|a|_v^{−s/2}`:

  `Φ(x ↦ ax + b) = K(|a|) + |a|_v^{−s/2} ψ(b)`  (`glueAt`).

The successor is a **gluing successor** (`IsGluingSuccessor`): conformal of exponent `s` at `v`,
Hermitian, conditionally positive on mass-zero weights, and negative at `1`. The real successors
`−c|b|`, `−c|b|^s` and every ultrametric `−c|b|_p` are gluing successors.

* **The gluing formula at `v`** (`negIndex_glueAt_eq`): `κ(Φ) = κ_v(K) + 1`, where `κ_v(K)`
  (`placePolarIndex`) counts the negative squares of `K` on the hyperplanes
  `ℓ_v(w) = Σ w_i |u_i|_v^{−s/2} = 0`. The proof is the archimedean one with the translation pair
  `1, x ↦ x + u₀^N`, `|u₀|_v > 1`, weights `|u₀^N|_v^{−s/2}`, whose own form tends to `2 Re ψ(1) < 0`.
* **Sub-boost data** (`negIndex_glueAt_eq_of_subBoost`): data growing slower than the boost at `v`
  glue at full index, `κ(Φ) = κ(K) + 1`.
* **Weil's correlation glued at a prime** (`negIndex_weilPadicState_eq`,
  `negIndex_weilPadicState_eq_rightZeros`): `κ(ratCorr(|a|) − c|a|_p^{−1/2}|b|_p) = κ(K_ζ) + 1 =
  #{zeros right of the critical line} + 1` for every prime `p`, and likewise for every primitive
  Dirichlet `L(s, χ)` (`negIndex_glueAt_padic_dirichlet`). Against the `p`-adic boost the slopes
  `p^{−N}` are large, and `u^{1/2 − ρ}·p^{−N/2}` at `u = p^{−N}` is `p^{−N(1 − Re ρ)} → 0` since every
  zero has `Re ρ < 1`.

So the zero count of Weil's correlation does not depend on the place at which it is glued: the
archimedean place and every prime glue it at full index, each with one square of its own.
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate Matrix
open Zeta23
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx cx_contDiff cx_hasCompactSupport)
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)
open GaloisForLFunctions.ArithmeticOrientationGeometry (seenRightZeros seenRightZeros_cubicSpline)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-- A **gluing successor** at the place `v` with exponent `s`. -/
structure IsGluingSuccessor (v : AbsoluteValue ℚ ℝ) (s : ℝ) (ψ : Multiplicative ℚ → ℂ) : Prop where
  conformal : IsConformal v s ψ
  herm : IsHermKernel ψ
  polar : ∀ {n : ℕ} (x : Fin n → Multiplicative ℚ) (w : Fin n → ℂ), ∑ a, w a = 0 →
    0 ≤ hermQuad (gram ψ x) w
  neg_one : (ψ (Multiplicative.ofAdd 1)).re < 0

variable {v : AbsoluteValue ℚ ℝ} {s : ℝ} {ψ : Multiplicative ℚ → ℂ}

theorem placeVal_pos (v : AbsoluteValue ℚ ℝ) (u : posUnits) : 0 < v ((u : ℚˣ) : ℚ) :=
  v.pos (Units.ne_zero _)

/-- The boost coordinate `ℓ_v(w) = Σ w_i |u_i|_v^{−s/2}` of a family of positive slopes. -/
def placeMass (v : AbsoluteValue ℚ ℝ) (s : ℝ) {n : ℕ} (u : Fin n → posUnits) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun w := ∑ i, w i * (((v ((u i : ℚˣ) : ℚ)) ^ (-(s / 2)) : ℝ) : ℂ)
  map_add' w w' := by simp only [Pi.add_apply, add_mul, sum_add_distrib]
  map_smul' t w := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, mul_sum]

/-- **The boost-polar index at `v`**: negative squares of `K` on the hyperplanes `ℓ_v = 0`. -/
def placePolarIndex (v : AbsoluteValue ℚ ℝ) (s : ℝ) (K : posUnits → ℂ) : ℕ∞ :=
  ⨆ (n : ℕ) (u : Fin n → posUnits), (negIndexOn (gram K u) (LinearMap.ker (placeMass v s u)) : ℕ∞)

theorem negIndexOn_le_placePolarIndex (K : posUnits → ℂ) {n : ℕ} (u : Fin n → posUnits) :
    (negIndexOn (gram K u) (LinearMap.ker (placeMass v s u)) : ℕ∞) ≤ placePolarIndex v s K :=
  le_iSup₂ (f := fun n (u : Fin n → posUnits) =>
    (negIndexOn (gram K u) (LinearMap.ker (placeMass v s u)) : ℕ∞)) n u

theorem placePolarIndex_le_negIndex (K : posUnits → ℂ) : placePolarIndex v s K ≤ negIndex K :=
  iSup₂_le fun _ u =>
    (Nat.cast_le.mpr (negIndexOn_le_hermNegIndex _ _)).trans (hermNegIndex_gram_le_negIndex K u)

theorem negIndex_le_placePolarIndex_add_one (K : posUnits → ℂ) :
    negIndex K ≤ placePolarIndex v s K + 1 :=
  negIndex_le_iff.mpr fun n u => by
    have h := hermNegIndex_le_negIndexOn_ker_add_one (gram K u) (placeMass v s u)
    calc (hermNegIndex (gram K u) : ℕ∞)
        ≤ ((negIndexOn (gram K u) (LinearMap.ker (placeMass v s u)) + 1 : ℕ) : ℕ∞) := Nat.cast_le.mpr h
      _ ≤ placePolarIndex v s K + 1 := by
          push_cast
          exact add_le_add (negIndexOn_le_placePolarIndex K u) le_rfl

/-- **The gluing at `v`** `K(|a|) + |a|_v^{−s/2} ψ(b)`. -/
def glueAt (v : AbsoluteValue ℚ ℝ) (s : ℝ) (ψ : Multiplicative ℚ → ℂ) (K : posUnits → ℂ)
    (g : AffineGroupQ) : ℂ :=
  K (slopeAbs g) + conformalInduction v s ψ g

theorem val_slopeAbs (g : AffineGroupQ) : ((slopeAbs g : ℚˣ) : ℚ) = |affSlope g| := rfl

theorem slopePow_eq_place (g : AffineGroupQ) :
    slopePow v s g = (v ((slopeAbs g : ℚˣ) : ℚ)) ^ (s / 2) := by
  rw [val_slopeAbs]
  unfold slopePow
  congr 1
  rcases abs_choice (affSlope g) with h | h
  · rw [h]; rfl
  · rw [h, map_neg_eq_map]; rfl

/-- The boost weights carry the boost coordinate at `v` as their total mass. -/
theorem sum_boostWeights_eq_place {n : ℕ} (g : Fin n → AffineGroupQ) (w : Fin n → ℂ) :
    ∑ a, boostWeights v s g w a = placeMass v s (fun a => slopeAbs (g a)) w := by
  simp only [boostWeights, placeMass, LinearMap.coe_mk, AddHom.coe_mk, slopePow_eq_place]
  refine sum_congr rfl fun a _ => ?_
  rw [Real.rpow_neg (placeVal_pos v _).le, Complex.ofReal_inv, div_eq_mul_inv]

/-- **The Gram identity**: `K`'s form at the slopes plus the successor's form at the shifts. -/
theorem hermQuad_gram_glueAt (hS : IsGluingSuccessor v s ψ) (K : posUnits → ℂ) {n : ℕ}
    (g : Fin n → AffineGroupQ)
    (w : Fin n → ℂ) :
    hermQuad (gram (glueAt v s ψ K) g) w = hermQuad (gram K fun a => slopeAbs (g a)) w +
      hermQuad (gram ψ (shifts g))
        (boostWeights v s g w) := by
  have e : gram (glueAt v s ψ K) g = gram (fun x => K (slopeAbs x)) g +
      gram (conformalInduction v s ψ) g := by
    ext a b; simp [gram, glueAt]
  rw [e, HeckeKreinToeplitz.hermQuad_add, gram_comp_slopeAbs,
    hermQuad_gram_conformalInduction hS.conformal]

/-- **Upper bound**: `κ(Φ) ≤ κ_v(K) + 1`. -/
theorem negIndex_glueAt_le (hS : IsGluingSuccessor v s ψ) (K : posUnits → ℂ) :
    negIndex (glueAt v s ψ K) ≤ placePolarIndex v s K + 1 := by
  refine negIndex_le_iff.mpr fun n g => ?_
  set u : Fin n → posUnits := fun a => slopeAbs (g a)
  have h1 := hermNegIndex_le_negIndexOn_ker_add_one (gram (glueAt v s ψ K) g) (placeMass v s u)
  have h2 : negIndexOn (gram (glueAt v s ψ K) g) (LinearMap.ker (placeMass v s u)) ≤
      negIndexOn (gram K u) (LinearMap.ker (placeMass v s u)) :=
    negIndexOn_le_of_hermQuad_le fun w hw => by
      rw [hermQuad_gram_glueAt hS]
      have hmass : ∑ a, boostWeights v s g w a = 0 := by
        rw [sum_boostWeights_eq_place]; exact LinearMap.mem_ker.mp hw
      linarith [hS.polar (shifts g) _ hmass]
  calc (hermNegIndex (gram (glueAt v s ψ K) g) : ℕ∞)
      ≤ ((negIndexOn (gram (glueAt v s ψ K) g) (LinearMap.ker (placeMass v s u)) + 1 : ℕ) : ℕ∞) :=
        Nat.cast_le.mpr h1
    _ ≤ placePolarIndex v s K + 1 := by
        push_cast
        exact add_le_add ((Nat.cast_le.mpr h2).trans (negIndexOn_le_placePolarIndex K u)) le_rfl

/-! ### The lower bound -/

theorem glueAt_inv_mul (hS : IsGluingSuccessor v s ψ) (K : posUnits → ℂ) (g h : AffineGroupQ) :
    glueAt v s ψ K (g⁻¹ * h) = K ((slopeAbs g)⁻¹ * slopeAbs h) +
      (((slopePow v s g * slopePow v s h)⁻¹ : ℝ) : ℂ) *
        ψ (Multiplicative.ofAdd (shiftOf h - shiftOf g)) := by
  rw [glueAt, conformalInduction_inv_mul (hS.conformal), map_mul, map_inv]

/-- **Lower bound**: every negative subspace of `K` on `ℓ_v = 0` survives next to one square of the
successor. -/
theorem add_one_le_negIndex_glueAt (hS : IsGluingSuccessor v s ψ) (hs : 0 < s)
    (hv : ∃ u : ℚ, 1 < v u) {K : posUnits → ℂ} (hK : IsHermKernel K)
    {m : ℕ} (u : Fin m → posUnits) :
    (negIndexOn (gram K u) (LinearMap.ker (placeMass v s u)) : ℕ∞) + 1 ≤ negIndex (glueAt v s ψ K) := by
  classical
  obtain ⟨u0, hu0⟩ := hv
  have hu00 : u0 ≠ 0 := by rintro rfl; simp at hu0; linarith
  obtain ⟨W, hWV, hWr, hW⟩ := exists_negIndexOn (gram K u) (LinearMap.ker (placeMass v s u))
  set r := Module.finrank ℂ W
  set bW := Module.finBasis ℂ W
  set BW : Matrix (Fin m) (Fin r) ℂ := Matrix.of fun i k => (bW k : Fin m → ℂ) i
  have hBW : ∀ k, ∑ i, BW i k * (((v ((u i : ℚˣ) : ℚ)) ^ (-(s / 2)) : ℝ) : ℂ) = 0 :=
    fun k => LinearMap.mem_ker.mp (hWV (bW k).2)
  set Φ := glueAt v s ψ K
  set D : Fin m → AffineGroupQ := fun i => dilation ((u i : posUnits) : ℚˣ)
  have hDslope : ∀ i, slopeAbs (D i) = u i := fun i => slopeAbs_dilation _
  have hDshift : ∀ i, shiftOf (D i) = 0 := fun i => affShift_dilation _
  have hDpow : ∀ i, slopePow v s (D i) =
      (v ((u i : ℚˣ) : ℚ)) ^ (s / 2) := fun i => by rw [slopePow_eq_place, hDslope]
  -- the translation pair `1, x ↦ x + u₀^N`
  set T : ℕ → Fin 2 → AffineGroupQ := fun N => ![1, translation (u0 ^ N)]
  have hTslope : ∀ N e, slopeAbs (T N e) = 1 := fun N e => by
    fin_cases e
    · simp [T]
    · simp [T, slopeAbs_translation]
  have hTpow : ∀ N e, slopePow v s (T N e) = 1 := fun N e => by
    fin_cases e
    · simp [T, slopePow_one]
    · exact slopePow_translation _ _ _
  set σ : ℕ → ℝ := fun N => (v (u0 ^ N)) ^ (-(s / 2))
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
    Matrix.fromBlocks (BWᴴ * A * BW) 0 0
      (Matrix.of fun _ _ => ((2 * (ψ (Multiplicative.ofAdd 1)).re : ℝ) : ℂ))
  have hvL : ∀ N : ℕ, v (u0 ^ N) = (v u0) ^ N := fun N => map_pow v u0 N
  have hσN : ∀ N : ℕ, σ N = ((v u0) ^ (-(s / 2))) ^ N := fun N => by
    simp only [σ, hvL]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (v.nonneg _), mul_comm, Real.rpow_mul (v.nonneg _),
      Real.rpow_natCast]
  have hσ : Tendsto (fun N : ℕ => σ N) atTop (𝓝 0) := by
    simp_rw [hσN]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (Real.rpow_nonneg (v.nonneg _) _)
      (Real.rpow_lt_one_of_one_lt_of_neg hu0 (by linarith))
  have hσc : Tendsto (fun N : ℕ => ((σ N : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp hσ
  have hvpos : ∀ N : ℕ, 0 < v (u0 ^ N) := fun N => v.pos (pow_ne_zero _ hu00)
  have hσsq : ∀ N : ℕ, σ N * σ N * (v (u0 ^ N)) ^ s = 1 := fun N => by
    simp only [σ]
    rw [← Real.rpow_add (hvpos N), ← Real.rpow_add (hvpos N)]
    ring_nf
    exact Real.rpow_zero _
  have hneg0 : ψ (Multiplicative.ofAdd 0) = 0 := hS.conformal.apply_zero hs ⟨u0, hu0⟩
  -- the boost coordinates `ρ_i = |u_i|_v^{−s/2}`; the basis of `W` has `ℓ_v = 0`
  set ρ : Fin m → ℂ := fun i => (((v ((u i : ℚˣ) : ℚ)) ^ (-(s / 2)) : ℝ) : ℂ)
  have hzero : ∀ k, ∑ i, conj (BW i k) * ρ i = 0 := fun k => by
    have h := congrArg conj (hBW k)
    rw [map_sum, map_zero] at h
    rw [← h]
    refine sum_congr rfl fun i _ => ?_
    simp [ρ, Complex.conj_ofReal]
  have hzero' : ∀ k, ∑ i, ρ i * BW i k = 0 := fun k => by
    rw [← hBW k]; exact sum_congr rfl fun i _ => mul_comm _ _
  have hρ : ∀ i, (((slopePow v s (D i))⁻¹ : ℝ) : ℂ) = ρ i := fun i => by
    rw [hDpow, ← Real.rpow_neg (placeVal_pos v _).le]
  -- entries of the cross blocks
  have hcross : ∀ k, Tendsto (fun N => (BWᴴ * C N * Sig N) k 0) atTop (𝓝 0) := by
    intro k
    have hent : ∀ N, (BWᴴ * C N * Sig N) k 0 =
        (σ N : ℂ) * (2 * ∑ i, conj (BW i k) * K ((u i)⁻¹)) := by
      intro N
      have hterm : ∀ i e, Φ ((D i)⁻¹ * T N e) = K ((u i)⁻¹) +
          ψ (Multiplicative.ofAdd (shiftOf (T N e))) * ρ i := fun i e => by
        simp only [Φ, glueAt_inv_mul hS, hDslope, hTslope, mul_one, hTpow, hDshift, sub_zero]
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
    have h2 := isHermKernel_conformalInduction hS.conformal hS.herm
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
  -- the pair block tends to `2 Re ψ(1) < 0`
  set Y : ℕ → ℂ := fun N => (((v (u0 ^ N)) ^ s : ℝ) : ℂ) * ψ (Multiplicative.ofAdd 1)
  have hpair : Tendsto (fun N => ((Sig N)ᴴ * E N * Sig N) 0 0) atTop
      (𝓝 ((2 * (ψ (Multiplicative.ofAdd 1)).re : ℝ) : ℂ)) := by
    have hent : ∀ N, ((Sig N)ᴴ * E N * Sig N) 0 0 =
        ((σ N * σ N : ℝ) : ℂ) * (4 * K 1) + ((σ N * σ N : ℝ) : ℂ) * (Y N + conj (Y N)) := by
      intro N
      have hsp : slopePow v s (translation (u0 ^ N)) = 1 := slopePow_translation _ _ _
      have hsp' : slopePow v s (translation (-(u0 ^ N))) = 1 := slopePow_translation _ _ _
      have hsh : shiftOf (translation (u0 ^ N)) = u0 ^ N := affShift_translation _
      have hsh' : shiftOf (translation (-(u0 ^ N))) = -(u0 ^ N) := affShift_translation _
      have hinv : (translation (u0 ^ N))⁻¹ = translation (-(u0 ^ N)) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← translation_add, neg_add_cancel, translation_zero]
      have hconf : ψ (Multiplicative.ofAdd (u0 ^ N)) = Y N := by
        have h := hS.conformal (u0 ^ N) 1 (pow_ne_zero _ hu00)
        rwa [mul_one] at h
      have e00 : Φ 1 = K 1 := by
        simp only [Φ, glueAt, map_one, conformalInduction, shiftOf_one, hneg0,
          mul_zero, add_zero]
      have e01 : Φ (translation (u0 ^ N)) = K 1 + Y N := by
        simp only [Φ, glueAt, slopeAbs_translation, conformalInduction, hsp, hsh, inv_one,
          Complex.ofReal_one, one_mul, hconf]
      have e10 : Φ (translation (-(u0 ^ N))) = K 1 + conj (Y N) := by
        simp only [Φ, glueAt, slopeAbs_translation, conformalInduction, hsp', hsh', inv_one,
          Complex.ofReal_one, one_mul]
        rw [ofAdd_neg, hS.herm, hconf]
      have e11 : Φ (translation (-(u0 ^ N)) * translation (u0 ^ N)) = K 1 := by
        rw [← translation_add, neg_add_cancel, translation_zero, e00]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, E, Sig, gram, T, Matrix.of_apply,
        Fin.sum_univ_two, Complex.star_def, Complex.conj_ofReal,
        Matrix.cons_val_zero, Matrix.cons_val_one, inv_one, one_mul, mul_one,
        hinv, e00, e01, e10, e11]
      push_cast
      ring
    have hY : ∀ N, ((σ N * σ N : ℝ) : ℂ) * (Y N + conj (Y N)) =
        ((2 * (ψ (Multiplicative.ofAdd 1)).re : ℝ) : ℂ) := fun N => by
      rw [Complex.add_conj, ← Complex.ofReal_mul]
      congr 1
      simp only [Y, Complex.re_ofReal_mul]
      rw [show σ N * σ N * (2 * ((v (u0 ^ N)) ^ s * (ψ (Multiplicative.ofAdd 1)).re)) =
        2 * (ψ (Multiplicative.ofAdd 1)).re * (σ N * σ N * (v (u0 ^ N)) ^ s) by ring, hσsq, mul_one]
    simp_rw [hent, hY]
    have h1 : Tendsto (fun N : ℕ => ((σ N * σ N : ℝ) : ℂ)) atTop (𝓝 0) := by
      have := hσ.mul hσ
      rw [mul_zero] at this
      simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp this
    have := (h1.mul_const (4 * K 1)).add_const ((2 * (ψ (Multiplicative.ofAdd 1)).re : ℝ) : ℂ)
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
    simp only [A, gram, Φ, glueAt_inv_mul hS, hDslope, hDshift, sub_self, hneg0,
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
  have hscal : 1 ≤ hermNegIndex (Matrix.of fun _ _ =>
      ((2 * (ψ (Multiplicative.ofAdd 1)).re : ℝ) : ℂ) : Matrix (Fin 1) (Fin 1) ℂ) := by
    have hneg : hermQuad (Matrix.of fun _ _ => ((2 * (ψ (Multiplicative.ofAdd 1)).re : ℝ) : ℂ) :
        Matrix (Fin 1) (Fin 1) ℂ) ![1] < 0 := by
      simp [hermQuad, Matrix.mulVec, dotProduct]
      linarith [hS.neg_one]
    exact (one_le_negIndexOn (V := ⊤) Submodule.mem_top hneg).trans (negIndexOn_le_hermNegIndex _ _)
  have hlimit : r + 1 ≤ hermNegIndex H₀ :=
    (add_le_add hP hscal).trans (hermNegIndex_add_le_fromBlocks _ _)
  obtain ⟨N, hN⟩ := (eventually_le_hermNegIndex hH₀ hconv).exists
  have hcomp : hermNegIndex (H N) ≤ hermNegIndex (gram Φ (Sum.elim D (T N))) :=
    hermNegIndex_le_of_hermQuad_eq _ _ (Matrix.mulVecLin (S N)) fun a => by
      rw [Matrix.mulVecLin_apply, ← HTGeometry.hermQuad_rect_conjugate]
  have hfin := hermNegIndex_gram_le_negIndex Φ (Sum.elim D (T N))
  have hfinal : r + 1 ≤ hermNegIndex (gram Φ (Sum.elim D (T N))) := (hlimit.trans hN).trans hcomp
  calc (negIndexOn (gram K u) (LinearMap.ker (placeMass v s u)) : ℕ∞) + 1
      = ((r + 1 : ℕ) : ℕ∞) := by push_cast; rw [hWr]
    _ ≤ negIndex Φ := (Nat.cast_le.mpr hfinal).trans hfin

/-- **The gluing formula at `v`**: `κ(K(|a|) + |a|_v^{−s/2}ψ(b)) = κ_v(K) + 1`. -/
theorem negIndex_glueAt_eq (hS : IsGluingSuccessor v s ψ) (hs : 0 < s) (hv : ∃ u : ℚ, 1 < v u)
    {K : posUnits → ℂ} (hK : IsHermKernel K) :
    negIndex (glueAt v s ψ K) = placePolarIndex v s K + 1 := by
  refine le_antisymm (negIndex_glueAt_le hS K) ?_
  rcases eq_or_ne (negIndex (glueAt v s ψ K)) ⊤ with htop | htop
  · rw [htop]; exact le_top
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp htop
  have hfam : ∀ (m : ℕ) (u : Fin m → posUnits),
      negIndexOn (gram K u) (LinearMap.ker (placeMass v s u)) + 1 ≤ M := fun m u => by
    have h := add_one_le_negIndex_glueAt hS hs hv hK u
    rw [← hM] at h
    exact_mod_cast h
  have h1 : 1 ≤ M := by have := hfam 0 (fun i => i.elim0); omega
  have hall : ∀ (m : ℕ) (u : Fin m → posUnits),
      (negIndexOn (gram K u) (LinearMap.ker (placeMass v s u)) : ℕ∞) ≤ ((M - 1 : ℕ) : ℕ∞) :=
    fun m u => Nat.cast_le.mpr (by have := hfam m u; omega)
  calc placePolarIndex v s K + 1 ≤ ((M - 1 : ℕ) : ℕ∞) + 1 := add_le_add (iSup₂_le hall) le_rfl
    _ = negIndex (glueAt v s ψ K) := by
        rw [← hM]; norm_cast; omega

/-! ### Sub-boost dilation data -/

/-- **Sub-boost data are glued at full index.** If along slopes `λ_N` with `|λ_N|_v^{−s/2} → 0` the
data grow slower than the boost at `v`, `‖K(λ_N u)‖ |λ_N|_v^{−s/2} → 0`, then `κ_v(K) = κ(K)`: a
negative family dilated by `λ_N` and corrected at the slope `1` by `−|λ_N|_v^{−s/2} ℓ_v` lies on
`ℓ_v = 0`, and its compressed Gram matrices tend to the original ones. -/
theorem placePolarIndex_eq_negIndex_of_subBoost {K : posUnits → ℂ} (hK : IsHermKernel K)
    (lam : ℕ → posUnits)
    (hlam : Tendsto (fun N => (v ((lam N : ℚˣ) : ℚ)) ^ (-(s / 2))) atTop (𝓝 0))
    (hgrow : ∀ u : posUnits, Tendsto (fun N => K (lam N * u) *
      (((v ((lam N : ℚˣ) : ℚ)) ^ (-(s / 2)) : ℝ) : ℂ)) atTop (𝓝 0)) :
    placePolarIndex v s K = negIndex K := by
  classical
  refine le_antisymm (placePolarIndex_le_negIndex K) (negIndex_le_iff.mpr fun n F => ?_)
  set μ : ℕ → ℝ := fun N => (v ((lam N : ℚˣ) : ℚ)) ^ (-(s / 2))
  set ρ : Fin n → ℝ := fun i => (v ((F i : ℚˣ) : ℚ)) ^ (-(s / 2))
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
  have hroot : ∀ i, (v (((lam N * F i : posUnits) : ℚˣ) : ℚ)) ^ (-(s / 2)) = μ N * ρ i :=
    fun i => by
      rw [show (((lam N * F i : posUnits) : ℚˣ) : ℚ) = ((lam N : ℚˣ) : ℚ) * ((F i : ℚˣ) : ℚ) from
        rfl, map_mul]
      exact Real.mul_rpow (v.nonneg _) (v.nonneg _)
  have hV : ∀ a, L' a ∈ LinearMap.ker (placeMass v s (Fam N)) := fun a => by
    rw [LinearMap.mem_ker]
    simp only [L', placeMass, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp,
      Function.comp_apply, Matrix.mulVecLin_apply, Fin.sum_univ_succ, Fam, Fin.cons_zero,
      Fin.cons_succ, hroot, Matrix.mulVec, dotProduct, L, Matrix.of_apply, Fin.cases_zero,
      Fin.cases_succ, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, if_true,
      OneMemClass.coe_one, Units.val_one, map_one, Real.one_rpow, Complex.ofReal_one, mul_one]
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
    _ ≤ (negIndexOn (gram K (Fam N)) (LinearMap.ker (placeMass v s (Fam N))) : ℕ∞) :=
        Nat.cast_le.mpr (h2 ▸ h1)
    _ ≤ placePolarIndex v s K := negIndexOn_le_placePolarIndex K _

/-- **Sub-boost data cost exactly one square more**: `κ(K(|a|) + |a|_v^{−s/2}ψ(b)) = κ(K) + 1`. -/
theorem negIndex_glueAt_eq_of_subBoost (hS : IsGluingSuccessor v s ψ) (hs : 0 < s)
    (hv : ∃ u : ℚ, 1 < v u) {K : posUnits → ℂ} (hK : IsHermKernel K) (lam : ℕ → posUnits)
    (hlam : Tendsto (fun N => (v ((lam N : ℚˣ) : ℚ)) ^ (-(s / 2))) atTop (𝓝 0))
    (hgrow : ∀ u : posUnits, Tendsto (fun N => K (lam N * u) *
      (((v ((lam N : ℚˣ) : ℚ)) ^ (-(s / 2)) : ℝ) : ℂ)) atTop (𝓝 0)) :
    negIndex (glueAt v s ψ K) = negIndex K + 1 := by
  rw [negIndex_glueAt_eq hS hs hv hK,
    placePolarIndex_eq_negIndex_of_subBoost hK lam hlam hgrow]


/-! ### Gluing successors -/

theorem isGluingSuccessor_negAbsRat {c : ℝ} (hc : 0 < c) :
    IsGluingSuccessor Rat.AbsoluteValue.real 1 fun m => (c : ℂ) * negAbsRat m where
  conformal := isConformal_negAbsRat c
  herm := isHermKernel_ofReal_mul isHermKernel_negAbsRat c
  polar := fun x w hw => hermQuad_gram_ofReal_mul_nonneg hc.le x w
    (hermQuad_gram_negAbsRat_nonneg x w hw)
  neg_one := by simp [negAbsRat, absRat]; exact hc

theorem isGluingSuccessor_negUltra (p : ℕ) [Fact p.Prime] {c : ℝ} (hc : 0 < c) :
    IsGluingSuccessor (Rat.AbsoluteValue.padic p) 1
      fun m => (c : ℂ) * negUltra (Rat.AbsoluteValue.padic p) m where
  conformal := isConformal_negUltra _ c
  herm := isHermKernel_ofReal_mul (isHermKernel_negUltra _) c
  polar := fun x w hw => hermQuad_gram_ofReal_mul_nonneg hc.le x w
    (hermQuad_gram_negUltra_nonneg (isUltra_padic p) x w hw)
  neg_one := by simp [negUltra]; exact hc

/-! ### Weil's correlation glued at a prime -/

section Padic

variable (p : ℕ) [hp : Fact p.Prime]

/-- The positive slope `1/p`. -/
def pInvPos : posUnits :=
  ⟨Units.mk0 ((p : ℚ)⁻¹) (inv_ne_zero (by exact_mod_cast hp.out.ne_zero)), by
    show (0 : ℚ) < (p : ℚ)⁻¹; exact inv_pos.mpr (by exact_mod_cast hp.out.pos)⟩

theorem pInvPos_pow_val (N : ℕ) : ((((pInvPos p ^ N : posUnits) : ℚˣ) : ℚ)) = ((p : ℚ)⁻¹) ^ N := by
  simp [pInvPos]

theorem padic_pInvPos_pow (N : ℕ) :
    Rat.AbsoluteValue.padic p ((((pInvPos p ^ N : posUnits) : ℚˣ) : ℚ)) = (p : ℝ) ^ N := by
  rw [pInvPos_pow_val, map_pow, map_inv₀, Rat.AbsoluteValue.padic_eq_padicNorm,
    padicNorm.padicNorm_p_of_prime]
  push_cast
  rw [inv_inv]

theorem tendsto_padic_pInvPos_rpow :
    Tendsto (fun N : ℕ => (Rat.AbsoluteValue.padic p ((((pInvPos p ^ N : posUnits) : ℚˣ) : ℚ))) ^
      (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have e : ∀ N : ℕ, (Rat.AbsoluteValue.padic p ((((pInvPos p ^ N : posUnits) : ℚˣ) : ℚ))) ^
      (-(1 / 2 : ℝ)) = ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ N := fun N => by
    rw [padic_pInvPos_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm,
      Real.rpow_mul (by positivity), Real.rpow_natCast]
  simp_rw [e]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
    (Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num))

variable {Z : ZeroConfig} {f : ℝ → ℝ}

/-- **Orbit kernels grow slower than the `p`-adic boost** when every zero has `Re ρ < 1`:
`K(p^{−N} u) p^{−N/2} → 0`, since `u^{1/2−ρ}` at `u = p^{−N}` has modulus `p^{N(Re ρ − 1/2)}`. -/
theorem orbitCorr_subBoost_padic (hZ : TemperedConfig Z)
    (hf : f ∈ ArithmeticCastelnuovoSeveri.realTests) (hlt : ∀ ρ : Z.carrier, (ρ : ℂ).re < 1)
    (u : posUnits) :
    Tendsto (fun N : ℕ => orbitCorr Z f (pInvPos p ^ N * u) *
      ((((Rat.AbsoluteValue.padic p ((((pInvPos p ^ N : posUnits) : ℚˣ) : ℚ))) ^
        (-(1 / 2 : ℝ))) : ℝ) : ℂ)) atTop (𝓝 0) := by
  have hsum : Summable fun ρ : Z.carrier => ‖orbitWeight Z f ρ‖ :=
    ArithmeticCastelnuovoSeveri.summable_norm_Wsummand _ hZ (cx_contDiff hf.1)
      (cx_hasCompactSupport hf.2) (cx_contDiff hf.1) (cx_hasCompactSupport hf.2)
  set a : ℝ := Real.log (((u : ℚˣ) : ℚ) : ℝ)
  have hu : (0 : ℝ) < (((u : ℚˣ) : ℚ) : ℝ) := posUnits_val_pos u
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.out.one_lt)
  set F : ℕ → Z.carrier → ℂ := fun N ρ =>
    cexp (-((-((N : ℝ) * Real.log p) + a : ℝ) : ℂ) * ((ρ : ℂ) - 1 / 2)) * orbitWeight Z f ρ *
      ((Real.exp (-((N : ℝ) * Real.log p) / 2) : ℝ) : ℂ)
  have hterm : ∀ N, orbitCorr Z f (pInvPos p ^ N * u) *
      ((((Rat.AbsoluteValue.padic p ((((pInvPos p ^ N : posUnits) : ℚˣ) : ℚ))) ^
        (-(1 / 2 : ℝ))) : ℝ) : ℂ) = ∑' ρ, F N ρ := by
    intro N
    have hlog : Real.log (((((pInvPos p ^ N * u : posUnits) : ℚˣ) : ℚ) : ℝ)) =
        -((N : ℝ) * Real.log p) + a := by
      have : ((((pInvPos p ^ N * u : posUnits) : ℚˣ) : ℚ) : ℝ) =
          ((p : ℝ)⁻¹) ^ N * (((u : ℚˣ) : ℚ) : ℝ) := by
        rw [show (((pInvPos p ^ N * u : posUnits) : ℚˣ) : ℚ) =
          (((pInvPos p ^ N : posUnits) : ℚˣ) : ℚ) * (((u : ℚˣ) : ℚ)) by simp, pInvPos_pow_val]
        push_cast; rfl
      rw [this, Real.log_mul (by positivity) hu.ne', Real.log_pow, Real.log_inv]
      ring
    have hpow : (Rat.AbsoluteValue.padic p ((((pInvPos p ^ N : posUnits) : ℚˣ) : ℚ))) ^
        (-(1 / 2 : ℝ)) = Real.exp (-((N : ℝ) * Real.log p) / 2) := by
      rw [padic_pInvPos_pow, Real.rpow_def_of_pos (by positivity), Real.log_pow]
      congr 1; ring
    rw [orbitCorr_eq_tsum, hlog, hpow, ← tsum_mul_right]
  have hnorm : ∀ N ρ, ‖F N ρ‖ =
      Real.exp (-((N : ℝ) * Real.log p) * (1 - (ρ : ℂ).re) - a * ((ρ : ℂ).re - 1 / 2)) *
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
  have hbound : ∀ N ρ, ‖F N ρ‖ ≤ Real.exp (|a| / 2) * ‖orbitWeight Z f ρ‖ := by
    intro N ρ
    rw [hnorm]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have h0 := (Z.strip ρ ρ.2).1
    have h1 := (Z.strip ρ ρ.2).2
    have hN : 0 ≤ (N : ℝ) * Real.log p := by positivity
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
    have h0 := hlt ρ
    have : Tendsto (fun N : ℕ => -((N : ℝ) * Real.log p) * (1 - (ρ : ℂ).re) -
        a * ((ρ : ℂ).re - 1 / 2)) atTop atBot := by
      refine tendsto_atBot_add_const_right _ _ ?_
      have : Tendsto (fun N : ℕ => (N : ℝ) * (Real.log p * (1 - (ρ : ℂ).re))) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const (mul_pos hlogp (by linarith))
      refine (tendsto_neg_atTop_atBot.comp this).congr fun N => ?_
      simp only [Function.comp_apply]; ring
    simpa using (Real.tendsto_exp_atBot.comp this).mul_const ‖orbitWeight Z f ρ‖
  simp_rw [hterm]
  have := tendsto_tsum_of_dominated_convergence (hsum.mul_left (Real.exp (|a| / 2)))
    hlim (Eventually.of_forall hbound)
  simpa using this

/-- **The `p`-adic state of a zero configuration counts its zeros**: for a tempered configuration
with every zero in `Re ρ < 1`, `κ(K_f(|a|) − c|a|_p^{−1/2}|b|_p) = #{zeros right of the line seen by
f} + 1`. -/
theorem negIndex_glueAt_padic_orbitCorr (hZ : TemperedConfig Z)
    (hf : f ∈ ArithmeticCastelnuovoSeveri.realTests) (hlt : ∀ ρ : Z.carrier, (ρ : ℂ).re < 1)
    {c : ℝ} (hc : 0 < c) :
    negIndex (glueAt (Rat.AbsoluteValue.padic p) 1
      (fun m => (c : ℂ) * negUltra (Rat.AbsoluteValue.padic p) m) (orbitCorr Z f)) =
        (seenRightZeros Z f).encard + 1 := by
  have hK : IsHermKernel (orbitCorr Z f) := (isHermKernel_orbitKernel Z f).comp _
  have h := negIndex_glueAt_eq_of_subBoost (isGluingSuccessor_negUltra p hc) one_pos
    ⟨_, one_lt_padic_inv p⟩ hK (fun N => pInvPos p ^ N)
    (by simpa using tendsto_padic_pInvPos_rpow p)
    (fun u => by simpa using orbitCorr_subBoost_padic p hZ hf hlt u)
  rw [h, orbitCorr, negIndex_comp_of_surjective _ _ posUnitsToHecke_surjective,
    negIndex_orbitKernel Z hZ hf]

/-- **Weil's correlation glued at a prime**: `ratCorr(|a|) − c|a|_p^{−1/2}|b|_p`. -/
def weilPadicState (c : ℝ) : AffineGroupQ → ℂ :=
  glueAt (Rat.AbsoluteValue.padic p) 1 (fun m => (c : ℂ) * negUltra (Rat.AbsoluteValue.padic p) m)
    ratCorr

/-- **Every prime glues Weil's correlation at full index**: `κ = κ(K_ζ) + 1`. -/
theorem negIndex_weilPadicState_eq {c : ℝ} (hc : 0 < c) :
    negIndex (weilPadicState p c) = negIndex zetaKernel + 1 := by
  rw [weilPadicState, ratCorr_eq_orbitCorr,
    negIndex_glueAt_padic_orbitCorr p temperedConfig_zetaZeroConfig cubicSpline_mem_realTests
      (fun ρ => ρ.2.2.2) hc, zetaKernel,
    negIndex_orbitKernel _ temperedConfig_zetaZeroConfig cubicSpline_mem_realTests]

/-- In terms of the zeros: `κ = #{zeros right of the critical line} + 1` at every prime. -/
theorem negIndex_weilPadicState_eq_rightZeros {c : ℝ} (hc : 0 < c) :
    negIndex (weilPadicState p c) =
      (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard + 1 := by
  rw [negIndex_weilPadicState_eq p hc, negIndex_zetaKernel]

/-- **The `p`-adic state of `L(s, χ)` counts its zeros**: for a primitive character `χ` modulo
`q > 1` and every prime `p`, `κ(K_χ(|a|) − c|a|_p^{−1/2}|b|_p) = #{zeros of L(s, χ) right of the
critical line} + 1`. -/
theorem negIndex_glueAt_padic_dirichlet {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 1 < q) (hprim : χ.IsPrimitive) {c : ℝ} (hc : 0 < c) :
    negIndex (glueAt (Rat.AbsoluteValue.padic p) 1
      (fun m => (c : ℂ) * negUltra (Rat.AbsoluteValue.padic p) m)
      (orbitCorr (ThmE.LZeros (ThmE.LSeam_of hq hprim)) cubicSpline)) =
      {ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier | 1 / 2 < ρ.re}.encard + 1 := by
  rw [negIndex_glueAt_padic_orbitCorr p (SquareRootThreshold.temperedConfig_LZeros hq hprim)
    cubicSpline_mem_realTests (fun ρ => ρ.2.2.2) hc, seenRightZeros_cubicSpline]

end Padic

end GaloisForLFunctions.AdelicKreinGeometry
