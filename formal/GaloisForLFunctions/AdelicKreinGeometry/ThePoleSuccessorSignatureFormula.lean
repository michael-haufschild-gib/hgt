import GaloisForLFunctions.AdelicKreinGeometry.TheHeckeBoostAndTheConformalSuccessorAreOneState
import GaloisForLFunctions.AdelicKreinGeometry.MixingKillsNegativeSquares

/-!
# The signature formula of a pole–successor state

For a conformal successor `ψ` of exponent `s > 0` at a nontrivial place `v`, the pole–successor
state `Φ = (boost pair) + |a|_v^{−s/2} ψ(b)` has

  `κ(Φ) = κ₀(ψ) + 1`,

the polar index of the successor plus one square, the pole (`negIndex_poleSuccessor_eq`).

* **Upper bound** (`negIndex_poleSuccessor_le`): on the hyperplane `X = 0` of the boost coordinate
  the Gram form is the polar form of `ψ` at the weights `w_g|a_g|_v^{−s/2}`.
* **Lower bound** (`add_one_le_negIndex_poleSuccessor`): a polar negative subspace of `ψ` on
  translations and the boost pair on the dilations `u^N, u^{N+1}` decouple as `N → ∞`. After
  compression to the polar subspace the cross terms are `|u|_v^{−(N+e)s/2}` times constants, and
  lower semicontinuity of the index keeps both blocks.

This is the separable signature formula `κ = Σ κ₀ + ε` for one local constituent glued to the pole,
with `ε = 1` exactly: the pole always costs its square. For `ψ = −c|b|_v` (`κ₀ = 0`) it is the
pole–successor law; for `ψ = c|b|`, `c > 0` (`κ₀ = ∞`), the state has infinite index.
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate Matrix
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ} {s : ℝ} {ψ : Multiplicative K → ℂ}

theorem poleSuccessor_inv_mul (hψ : IsConformal v s ψ) (g h : AffineGroupOf K) :
    poleSuccessor v s ψ (g⁻¹ * h) =
      ((slopePow v s h / slopePow v s g + slopePow v s g / slopePow v s h : ℝ) : ℂ) +
      (((slopePow v s g * slopePow v s h)⁻¹ : ℝ) : ℂ) *
        ψ (Multiplicative.ofAdd (shiftOf h - shiftOf g)) := by
  rw [poleSuccessor, conformalInduction_inv_mul hψ, slopePow_inv_mul, inv_div]

/-- The pole–successor state of a Hermitian successor is Hermitian. -/
theorem isHermKernel_poleSuccessor (hψ : IsConformal v s ψ) (hk : IsHermKernel ψ) :
    IsHermKernel (poleSuccessor v s ψ) := fun g => by
  have h := poleSuccessor_inv_mul hψ g 1
  rw [mul_one] at h
  rw [h, slopePow_one, shiftOf_one, zero_sub, ofAdd_neg, hk]
  simp only [poleSuccessor, conformalInduction, map_add, map_mul, Complex.conj_ofReal, mul_one,
    div_one, one_div]
  push_cast
  ring

theorem slopePow_mul (v : AbsoluteValue K ℝ) (s : ℝ) (g h : AffineGroupOf K) :
    slopePow v s (g * h) = slopePow v s g * slopePow v s h := by
  rw [slopePow, slopePow, slopePow, slopeOf_mul, map_mul, Real.mul_rpow (v.nonneg _) (v.nonneg _)]

theorem slopePow_pow (v : AbsoluteValue K ℝ) (s : ℝ) (g : AffineGroupOf K) (n : ℕ) :
    slopePow v s (g ^ n) = slopePow v s g ^ n := by
  induction n with
  | zero => simp [slopePow_one]
  | succ n ih => rw [pow_succ, slopePow_mul, ih, pow_succ]

/-- The boost coordinate `X = Σ w_g |a_g|_v^{−s/2}`. -/
def boostMass (v : AbsoluteValue K ℝ) (s : ℝ) {n : ℕ} (g : Fin n → AffineGroupOf K) :
    (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun w := ∑ a, boostWeights v s g w a
  map_add' w w' := by simp only [boostWeights, Pi.add_apply, add_div, sum_add_distrib]
  map_smul' t w := by
    simp only [boostWeights, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_div_assoc, mul_sum]

/-- The weights `w_g |a_g|_v^{−s/2}` as a linear map. -/
def boostWeightsLin (v : AbsoluteValue K ℝ) (s : ℝ) {n : ℕ} (g : Fin n → AffineGroupOf K) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun := boostWeights v s g
  map_add' w w' := funext fun a => by simp [boostWeights, add_div]
  map_smul' t w := funext fun a => by simp [boostWeights, mul_div_assoc]

/-! ### The upper bound -/

/-- **Upper bound**: `κ(Φ) ≤ κ₀(ψ) + 1`. -/
theorem negIndex_poleSuccessor_le (hψ : IsConformal v s ψ) :
    negIndex (poleSuccessor v s ψ) ≤ polarIndex ψ + 1 := by
  refine negIndex_le_iff.mpr fun n g => ?_
  have h1 := hermNegIndex_le_negIndexOn_ker_add_one (gram (poleSuccessor v s ψ) g) (boostMass v s g)
  obtain ⟨W, hWV, hWr, hW⟩ :=
    exists_negIndexOn (gram (poleSuccessor v s ψ) g) (LinearMap.ker (boostMass v s g))
  set bW := Module.finBasis ℂ W
  set L : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    boostWeightsLin v s g ∘ₗ W.subtype ∘ₗ bW.equivFun.symm.toLinearMap
  -- the weights of a vector of `W` have total mass `X = 0`
  have hX : ∀ a, ∑ i, boostWeights v s g (bW.equivFun.symm a : Fin n → ℂ) i = 0 := fun a =>
    LinearMap.mem_ker.mp (hWV (bW.equivFun.symm a).2)
  have hL : ∀ a, L a ∈ LinearMap.ker (totalMass (Fin n)) := fun a =>
    LinearMap.mem_ker.mpr (hX a)
  have hneg : ∀ a, a ≠ 0 → hermQuad (gram ψ (shifts g)) (L a) < 0 := fun a ha => by
    have hw0 : (bW.equivFun.symm a : Fin n → ℂ) ≠ 0 := fun h =>
      ha (bW.equivFun.symm.injective (Subtype.ext (by rw [h, map_zero]; rfl)))
    have hpos := hW _ (bW.equivFun.symm a).2 hw0
    rw [hermQuad_neg] at hpos
    have hq := hermQuad_gram_poleSuccessor hψ g (bW.equivFun.symm a : Fin n → ℂ)
    rw [hX a] at hq
    simp only [map_zero, zero_mul, mul_zero, add_zero, Complex.zero_re, zero_add] at hq
    change hermQuad (gram ψ (shifts g)) (boostWeights v s g (bW.equivFun.symm a : Fin n → ℂ)) < 0
    linarith
  have h2 := card_le_negIndexOn_of_forall_neg (gram ψ (shifts g)) _ L hL hneg
  rw [Fintype.card_fin, hWr] at h2
  calc (hermNegIndex (gram (poleSuccessor v s ψ) g) : ℕ∞)
      ≤ ((negIndexOn (gram (poleSuccessor v s ψ) g) (LinearMap.ker (boostMass v s g)) + 1 : ℕ) :
          ℕ∞) := Nat.cast_le.mpr h1
    _ ≤ polarIndex ψ + 1 := by
        push_cast
        exact add_le_add ((Nat.cast_le.mpr h2).trans (negIndexOn_le_polarIndex ψ _)) le_rfl

/-! ### The lower bound -/

/-- On translations the boost weights are the weights and the shifts are the points. -/
theorem hermQuad_gram_poleSuccessor_translations (hψ : IsConformal v s ψ) {m : ℕ}
    (x : Fin m → Multiplicative K) (c : Fin m → ℂ) (hc : ∑ i, c i = 0) :
    hermQuad (gram (poleSuccessor v s ψ) fun i => translationOf (Multiplicative.toAdd (x i))) c =
      hermQuad (gram ψ x) c := by
  rw [hermQuad_gram_poleSuccessor hψ]
  have hw : boostWeights v s (fun i => translationOf (Multiplicative.toAdd (x i))) c = c :=
    funext fun i => by simp [boostWeights, slopePow_translation]
  have hsh : shifts (fun i => translationOf (Multiplicative.toAdd (x i))) = x :=
    funext fun i => by simp [shifts, shiftOf_translationOf]
  rw [hw, hsh]
  simp [slopePow_translation, hc]

/-- **Lower bound**: every polar negative subspace of `ψ` survives next to the pole's square. -/
theorem add_one_le_negIndex_poleSuccessor (hs : 0 < s) (hv : ∃ u : K, 1 < v u)
    (hψ : IsConformal v s ψ) (hk : IsHermKernel ψ) {m : ℕ} (x : Fin m → Multiplicative K) :
    (negIndexOn (gram ψ x) (LinearMap.ker (totalMass (Fin m))) : ℕ∞) + 1 ≤
      negIndex (poleSuccessor v s ψ) := by
  classical
  obtain ⟨W, hWV, hWr, hW⟩ := exists_negIndexOn (gram ψ x) (LinearMap.ker (totalMass (Fin m)))
  set r := Module.finrank ℂ W
  set bW := Module.finBasis ℂ W
  set BW : Matrix (Fin m) (Fin r) ℂ := Matrix.of fun i k => (bW k : Fin m → ℂ) i
  have hBW : ∀ k, ∑ i, BW i k = 0 := fun k => LinearMap.mem_ker.mp (hWV (bW k).2)
  set Φ := poleSuccessor v s ψ
  set τ : Fin m → AffineGroupOf K := fun i => translationOf (Multiplicative.toAdd (x i))
  obtain ⟨u, hu⟩ := hv
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu; linarith
  set uU : Kˣ := Units.mk0 u hu0
  set t := slopePow v s (dilationOf uU)
  have ht : 1 < t := by
    simp only [t, slopePow, slopeOf_dilationOf, uU, Units.val_mk0]
    exact Real.one_lt_rpow hu (by positivity)
  -- the dilations `u^N, u^{N+1}`
  set P : ℕ → Fin 2 → AffineGroupOf K := fun N e => dilationOf (uU ^ (N + (e : ℕ)))
  have hPslope : ∀ N e, slopePow v s (P N e) = t ^ (N + (e : ℕ)) := fun N e => by
    simp only [P, map_pow, slopePow_pow, t]
  have hPshift : ∀ N e, shiftOf (P N e) = 0 := fun N e => shiftOf_dilationOf _
  have hPinv : ∀ N e e', (P N e)⁻¹ * P N e' = (P 0 e)⁻¹ * P 0 e' := fun N e e' => by
    simp only [P, pow_add, map_mul]
    group
  -- the Gram matrix of `τ ⊔ P N` in block form
  set C : ℕ → Matrix (Fin m) (Fin 2) ℂ := fun N => Matrix.of fun i e => Φ ((τ i)⁻¹ * P N e)
  set C' : ℕ → Matrix (Fin 2) (Fin m) ℂ := fun N => Matrix.of fun e i => Φ ((P N e)⁻¹ * τ i)
  set A := gram Φ τ
  set D := gram Φ (P 0)
  have hblock : ∀ N, gram Φ (Sum.elim τ (P N)) = Matrix.fromBlocks A (C N) (C' N) D := by
    intro N
    ext p q
    rcases p with i | e <;> rcases q with j | e'
    · rfl
    · rfl
    · rfl
    · simp only [gram, Sum.elim_inr, Matrix.fromBlocks_apply₂₂, D, hPinv]
  set S : Matrix (Fin m ⊕ Fin 2) (Fin r ⊕ Fin 2) ℂ := Matrix.fromBlocks BW 0 0 1
  set H : ℕ → Matrix (Fin r ⊕ Fin 2) (Fin r ⊕ Fin 2) ℂ := fun N =>
    Sᴴ * gram Φ (Sum.elim τ (P N)) * S
  have hH : ∀ N, H N = Matrix.fromBlocks (BWᴴ * A * BW) (BWᴴ * C N) (C' N * BW) D := by
    intro N
    simp only [H, hblock, S, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_one, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
  set H₀ := Matrix.fromBlocks (BWᴴ * A * BW) 0 0 D
  -- the cross blocks vanish in the limit
  have hcross : ∀ k e, Tendsto (fun N => (BWᴴ * C N) k e) atTop (𝓝 0) := by
    intro k e
    have hent : ∀ N, (BWᴴ * C N) k e = (((t ^ (N + (e : ℕ)))⁻¹ : ℝ) : ℂ) *
        ∑ i, conj (BW i k) * ψ (Multiplicative.ofAdd (-(Multiplicative.toAdd (x i)))) := by
      intro N
      have hterm : ∀ i, Φ ((τ i)⁻¹ * P N e) =
          ((t ^ (N + (e : ℕ)) / 1 + 1 / t ^ (N + (e : ℕ)) : ℝ) : ℂ) +
          (((1 * t ^ (N + (e : ℕ)))⁻¹ : ℝ) : ℂ) *
            ψ (Multiplicative.ofAdd (-(Multiplicative.toAdd (x i)))) := fun i => by
        simp only [Φ, poleSuccessor_inv_mul hψ, hPslope, hPshift, τ, slopePow_translation,
          shiftOf_translationOf, zero_sub]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, C, Matrix.of_apply,
        Complex.star_def, hterm, mul_add, sum_add_distrib]
      have h0 : ∑ i, conj (BW i k) * ((t ^ (N + (e : ℕ)) / 1 + 1 / t ^ (N + (e : ℕ)) : ℝ) : ℂ)
          = 0 := by
        rw [← sum_mul, ← map_sum, hBW k, map_zero, zero_mul]
      rw [h0, zero_add, mul_sum]
      refine sum_congr rfl fun i _ => ?_
      push_cast
      ring
    simp_rw [hent]
    have hlim : Tendsto (fun N : ℕ => ((t ^ (N + (e : ℕ)))⁻¹ : ℝ)) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop_atTop_of_one_lt ht).comp
        (tendsto_add_atTop_nat _))
    simpa using (Complex.continuous_ofReal.tendsto 0 |>.comp hlim).mul_const
      (∑ i, conj (BW i k) * ψ (Multiplicative.ofAdd (-(Multiplicative.toAdd (x i)))))
  have hcross' : ∀ e k, Tendsto (fun N => (C' N * BW) e k) atTop (𝓝 0) := by
    intro e k
    have hent : ∀ N, (C' N * BW) e k = (((t ^ (N + (e : ℕ)))⁻¹ : ℝ) : ℂ) *
        ∑ i, ψ (Multiplicative.ofAdd (Multiplicative.toAdd (x i))) * BW i k := by
      intro N
      have hterm : ∀ i, Φ ((P N e)⁻¹ * τ i) =
          ((1 / t ^ (N + (e : ℕ)) + t ^ (N + (e : ℕ)) / 1 : ℝ) : ℂ) +
          (((t ^ (N + (e : ℕ)) * 1)⁻¹ : ℝ) : ℂ) *
            ψ (Multiplicative.ofAdd (Multiplicative.toAdd (x i))) := fun i => by
        simp only [Φ, poleSuccessor_inv_mul hψ, hPslope, hPshift, τ, slopePow_translation,
          shiftOf_translationOf, sub_zero]
      simp only [Matrix.mul_apply, C', Matrix.of_apply, hterm, add_mul, sum_add_distrib]
      have h0 : ∑ i, ((1 / t ^ (N + (e : ℕ)) + t ^ (N + (e : ℕ)) / 1 : ℝ) : ℂ) * BW i k = 0 := by
        rw [← mul_sum, hBW k, mul_zero]
      rw [h0, zero_add, mul_sum]
      refine sum_congr rfl fun i _ => ?_
      push_cast
      ring
    simp_rw [hent]
    have hlim : Tendsto (fun N : ℕ => ((t ^ (N + (e : ℕ)))⁻¹ : ℝ)) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop_atTop_of_one_lt ht).comp
        (tendsto_add_atTop_nat _))
    simpa using (Complex.continuous_ofReal.tendsto 0 |>.comp hlim).mul_const
      (∑ i, ψ (Multiplicative.ofAdd (Multiplicative.toAdd (x i))) * BW i k)
  have hconv : ∀ p q, Tendsto (fun N => H N p q) atTop (𝓝 (H₀ p q)) := by
    intro p q
    simp only [hH]
    rcases p with k | e <;> rcases q with k' | e'
    · exact tendsto_const_nhds
    · simpa [H₀] using hcross k e'
    · simpa [H₀] using hcross' e k'
    · exact tendsto_const_nhds
  -- the limit carries `r + 1` negative squares
  have hΦ : IsHermKernel Φ := isHermKernel_poleSuccessor hψ hk
  have hH₀ : H₀.IsHermitian := by
    refine Matrix.IsHermitian.fromBlocks ?_ (by simp) (gram_isHermitian hΦ _)
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
      congrArg (fun M => BWᴴ * M * BW) (gram_isHermitian hΦ τ)
  have hP : r ≤ hermNegIndex (BWᴴ * A * BW) := by
    have h := card_le_hermNegIndex_of_forall_neg (BWᴴ * A * BW) LinearMap.id fun a ha => by
      rw [LinearMap.id_apply, HTGeometry.hermQuad_rect_conjugate]
      have hmem : BW.mulVec a = (bW.equivFun.symm a : Fin m → ℂ) := by
        ext i
        simp only [Matrix.mulVec, dotProduct, BW, Matrix.of_apply, Module.Basis.equivFun_symm_apply,
          Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact sum_congr rfl fun k _ => mul_comm _ _
      have hc0 : (bW.equivFun.symm a : Fin m → ℂ) ≠ 0 := fun h =>
        ha (bW.equivFun.symm.injective (Subtype.ext (by rw [h, map_zero]; rfl)))
      rw [hmem, hermQuad_gram_poleSuccessor_translations hψ x _
        (LinearMap.mem_ker.mp (hWV (bW.equivFun.symm a).2))]
      have := hW _ (bW.equivFun.symm a).2 hc0
      rw [hermQuad_neg] at this
      linarith
    simpa using h
  have hD : 1 ≤ hermNegIndex D := by
    have hval : ∀ e e' : Fin 2, D e e' =
        ((t ^ (e' : ℕ) / t ^ (e : ℕ) + t ^ (e : ℕ) / t ^ (e' : ℕ) : ℝ) : ℂ) := by
      intro e e'
      simp only [D, gram, Φ, poleSuccessor_inv_mul hψ, hPslope, hPshift, sub_self, zero_add]
      rw [hψ.apply_zero hs ⟨u, hu⟩, mul_zero, add_zero]
    have hneg : hermQuad D ![1, -1] < 0 := by
      have htp : 0 < t := by linarith
      have hpair : 2 < t + t⁻¹ := by
        have e : t + t⁻¹ - 2 = (t - 1) ^ 2 / t := by field_simp; ring
        have : 0 < (t - 1) ^ 2 / t := div_pos (by nlinarith) htp
        linarith
      simp only [hermQuad, dotProduct, Matrix.mulVec, Fin.sum_univ_two, hval, Pi.star_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
        div_one, one_div]
      simp only [star_one, star_neg, mul_one, mul_neg, neg_mul, one_mul, Complex.add_re,
        Complex.neg_re, Complex.ofReal_re]
      simp only [div_self htp.ne']
      norm_num
      linarith
    exact (one_le_negIndexOn (V := ⊤) Submodule.mem_top hneg).trans (negIndexOn_le_hermNegIndex _ _)
  have hlimit : r + 1 ≤ hermNegIndex H₀ :=
    (add_le_add hP hD).trans (hermNegIndex_add_le_fromBlocks _ _)
  obtain ⟨N, hN⟩ := (eventually_le_hermNegIndex hH₀ hconv).exists
  -- the compression never raises the index
  have hcomp : hermNegIndex (H N) ≤ hermNegIndex (gram Φ (Sum.elim τ (P N))) :=
    hermNegIndex_le_of_hermQuad_eq _ _ (Matrix.mulVecLin S) fun a => by
      rw [Matrix.mulVecLin_apply, ← HTGeometry.hermQuad_rect_conjugate]
  have hfin := hermNegIndex_gram_le_negIndex Φ (Sum.elim τ (P N))
  have hfinal : r + 1 ≤ hermNegIndex (gram Φ (Sum.elim τ (P N))) := (hlimit.trans hN).trans hcomp
  calc (negIndexOn (gram ψ x) (LinearMap.ker (totalMass (Fin m))) : ℕ∞) + 1
      = ((r + 1 : ℕ) : ℕ∞) := by push_cast; rw [hWr]
    _ ≤ negIndex Φ := (Nat.cast_le.mpr hfinal).trans hfin

/-- **The signature formula**: `κ(Φ) = κ₀(ψ) + 1`. -/
theorem negIndex_poleSuccessor_eq (hs : 0 < s) (hv : ∃ u : K, 1 < v u) (hψ : IsConformal v s ψ)
    (hk : IsHermKernel ψ) : negIndex (poleSuccessor v s ψ) = polarIndex ψ + 1 := by
  refine le_antisymm (negIndex_poleSuccessor_le hψ) ?_
  rcases eq_or_ne (negIndex (poleSuccessor v s ψ)) ⊤ with htop | htop
  · rw [htop]; exact le_top
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp htop
  -- every polar family fits below `M − 1`
  have hfam : ∀ (m : ℕ) (x : Fin m → Multiplicative K),
      negIndexOn (gram ψ x) (LinearMap.ker (totalMass (Fin m))) + 1 ≤ M := fun m x => by
    have h := add_one_le_negIndex_poleSuccessor hs hv hψ hk x
    rw [← hM] at h
    exact_mod_cast h
  have h1 : 1 ≤ M := by have := hfam 0 (fun i => i.elim0); omega
  have hall : ∀ (m : ℕ) (x : Fin m → Multiplicative K),
      (negIndexOn (gram ψ x) (LinearMap.ker (totalMass (Fin m))) : ℕ∞) ≤ ((M - 1 : ℕ) : ℕ∞) :=
    fun m x => Nat.cast_le.mpr (by have := hfam m x; omega)
  calc polarIndex ψ + 1 ≤ ((M - 1 : ℕ) : ℕ∞) + 1 := add_le_add (iSup₂_le hall) le_rfl
    _ = negIndex (poleSuccessor v s ψ) := by
        rw [← hM]; norm_cast; omega

/-! ### The real place: the trichotomy -/

/-- `c|b|`, `c > 0`, is negative definite on every polar hyperplane: `κ₀ = ∞`. -/
theorem polarIndex_mul_absRat {c : ℝ} (hc : 0 < c) :
    polarIndex (fun m => (c : ℂ) * absRat m) = ⊤ := by
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  set x : Fin (n + 1) → Multiplicative ℚ := fun a => Multiplicative.ofAdd (a : ℚ)
  have hx : Function.Injective x := fun a b h => by
    have := congrArg Multiplicative.toAdd h
    simp only [x, toAdd_ofAdd] at this
    exact Fin.ext (by exact_mod_cast this)
  have e : gram (fun m => (c : ℂ) * absRat m) x = (c : ℂ) • gram absRat x := by
    ext a b; simp [gram]
  have hpos : IsPosDefOn (-gram (fun m => (c : ℂ) * absRat m) x)
      (LinearMap.ker (totalMass (Fin (n + 1)))) := by
    intro w hw hw0
    rw [hermQuad_neg, e, hermQuad_smul]
    have := hermQuad_gram_absRat_neg hx (c := w) hw hw0
    nlinarith
  have h := le_csSup (negIndexOn_bddAbove _ _) ⟨_, le_rfl, rfl, hpos⟩
  rw [finrank_ker_totalMass] at h
  exact (Nat.cast_le.mpr h).trans (negIndexOn_le_polarIndex _ x)

/-- **The trichotomy at the real place**: `|a|^{1/2} + |a|^{−1/2} − c|a|^{−1/2}|b|` has index `1` for
`c ≥ 0` and `∞` for `c < 0`. -/
theorem negIndex_poleSuccessor_mul_negAbsRat (c : ℝ) :
    negIndex (poleSuccessor Rat.AbsoluteValue.real 1 fun m => (c : ℂ) * negAbsRat m) =
      if 0 ≤ c then 1 else ⊤ := by
  split_ifs with hc
  · exact negIndex_poleSuccessorState hc
  · have hk : IsHermKernel fun m => (c : ℂ) * negAbsRat m := fun m => by
      show (c : ℂ) * negAbsRat m⁻¹ = conj ((c : ℂ) * negAbsRat m)
      rw [isHermKernel_negAbsRat m, map_mul, Complex.conj_ofReal]
    have e : (fun m => (c : ℂ) * negAbsRat m) = fun m => ((-c : ℝ) : ℂ) * absRat m := by
      funext m; simp [negAbsRat]
    rw [negIndex_poleSuccessor_eq one_pos exists_one_lt_real (isConformal_negAbsRat c) hk, e,
      polarIndex_mul_absRat (by linarith), top_add]

end GaloisForLFunctions.AdelicKreinGeometry
