import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticHodgeIndexSignatureLaw
import GaloisForLFunctions.SquareRootThreshold.ZetaSmallApertureHeightWindowPositivity
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection

/-!
# The Pontryagin law of a tempered configuration

A zero configuration is *tempered* when `Σ_ρ m_ρ/(1 + |γ_ρ|²) < ∞`; the nontrivial zeros of `ζ`
form one. Its Weil form `W(f, g) = Σ_ρ m_ρ h_f(γ_ρ) conj h_g(γ̄_ρ)` converges absolutely on
compactly supported `C²` tests (`summable_Wsummand`), and its negative squares on finite families
of tests are counted by the zeros right of the critical line:

* *Upper bound* (`negIndex_zeroGram_le_of_tempered`): at most `#{Re ρ > ½}`, in `ℕ∞`.
* *Attainment* (`exists_zeroGram_negIndex_ge_of_tempered`): exactly that many when they are
  finitely many. Each such `ρ` has a **dual test** `b_ρ` with `h_{b_ρ}(γ_σ) = h_{b_ρ}(γ̄_σ) = δ_{ρσ}`
  (interpolation at the off-line points, `exists_dual_tests`). The combination
  `Σ_ρ conj(y_ρ) (b_ρ + ω_ρ b_ρ(· − L))` with the phase `ω_ρ = −e^{−i Im ρ · L}` has transform
  `conj(y_ρ)(1 − e^{±δ_ρ L})` at `γ_ρ, γ̄_ρ` (`δ_ρ = Re ρ − ½`), so the pair `ρ, 1 − ρ̄` contributes
  `2 m_ρ |y_ρ|² (1 − e^{δ_ρ L})(1 − e^{−δ_ρ L}) ≤ −2 m_ρ |y_ρ|² (δ_ρ L − 1)`. On the line the
  phases have modulus one, so the on-line zeros contribute at most `4|y|² A` with
  `A = Σ_τ m_τ Σ_ρ |h_{b_ρ}(γ_τ)|²`, independently of `L`. Once `δ_ρ L ≥ 4A + 2` the form is
  `≤ −|y|²`: negative definite on an `#{Re ρ > ½}`-dimensional space.

The nontrivial zeros of `ζ` are tempered (`temperedConfig_zetaZeroConfig`) and their zero-side
Gram matrix is the Weil Gram matrix of the explicit formula (`weilGram_eq_zeroGram`). By the
signature law the excess positive squares of the scaling surface are these negative squares; the
attainment above needs the zeros right of the line to be finitely many, which is not known for `ζ`.
-/

open Complex Matrix Finset
open scoped ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig
  exists_radius_of_hasCompactSupport)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### Absolute convergence on tempered configurations -/

/-- A compactly supported `C²` test has `‖h_f(z)‖ ≤ C/(1 + |Re z|)²` on the strip `|Im z| ≤ ½`. -/
theorem exists_paperFT_decay {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ C, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖paperFT f z‖ ≤ C / (1 + |z.re|) ^ 2 := by
  obtain ⟨A, hA0, hA⟩ := exists_radius_of_hasCompactSupport hfc
  have hsupp : ∀ u, f u ≠ 0 → |u| ≤ A := fun u hu => by
    by_contra h
    exact hu (hA u (not_le.mp h))
  set K := 4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)
  have hK : 0 ≤ K := mul_nonneg (by norm_num) (add_nonneg
    (MeasureTheory.integral_nonneg fun _ => norm_nonneg _)
    (MeasureTheory.integral_nonneg fun _ => norm_nonneg _))
  refine ⟨Real.exp A * K, mul_nonneg (Real.exp_pos _).le hK, fun z hz => ?_⟩
  have he : Real.exp (|z.im| * A) ≤ Real.exp A :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hz) hA0])
  exact (RHTower.norm_paperFT_le_decay hf hsupp z).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he hK) (by positivity))

/-- The ordinates `γ_ρ` of a configuration lie in the strip `|Im γ| ≤ ½`. -/
theorem abs_im_gammaOf_le (Z : ZeroConfig) (τ : Z.carrier) : |(gammaOf τ).im| ≤ 1 / 2 := by
  have hstrip := Z.strip τ.1 τ.2
  have hγ : (gammaOf τ).im = 1 / 2 - (τ : ℂ).re := by simp [gammaOf]
  rw [hγ, abs_le]
  constructor <;> linarith [hstrip.1, hstrip.2]

/-- The weighted products `m_τ ‖h_f(γ_τ)‖ ‖h_g(w_τ)‖` are summable on a tempered configuration,
for any points `w_τ` of the strip `|Im w| ≤ ½`. -/
theorem summable_mult_norm_mul (Z : ZeroConfig) (hZ : TemperedConfig Z) {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (w : Z.carrier → ℂ) (hw : ∀ τ, |(w τ).im| ≤ 1 / 2) :
    Summable fun τ : Z.carrier =>
      (Z.mult τ : ℝ) * ‖paperFT f (gammaOf τ)‖ * ‖paperFT g (w τ)‖ := by
  obtain ⟨Cf, hCf, hf'⟩ := exists_paperFT_decay hf hfc
  obtain ⟨Cg, hCg, hg'⟩ := exists_paperFT_decay hg hgc
  refine Summable.of_nonneg_of_le (fun τ => by positivity) (fun τ => ?_)
    (hZ.mul_left (4 / 3 * Cf * Cg))
  have him := abs_im_gammaOf_le Z τ
  have hN : 0 < 1 + Complex.normSq (gammaOf τ) := by
    have := Complex.normSq_nonneg (gammaOf τ)
    linarith
  have hden : 1 / (1 + |(gammaOf τ).re|) ^ 2 ≤ (4 / 3) / (1 + Complex.normSq (gammaOf τ)) := by
    rw [Complex.normSq_apply, div_le_div_iff₀ (by positivity)
      (by nlinarith [mul_self_nonneg (gammaOf τ).re, mul_self_nonneg (gammaOf τ).im])]
    have h1 : (gammaOf τ).im * (gammaOf τ).im ≤ 1 / 4 := by nlinarith [abs_le.mp him]
    nlinarith [abs_nonneg (gammaOf τ).re, sq_abs (gammaOf τ).re]
  have hA : ‖paperFT f (gammaOf τ)‖ ≤ Cf * ((4 / 3) / (1 + Complex.normSq (gammaOf τ))) := by
    refine (hf' _ him).trans ?_
    rw [div_eq_mul_one_div Cf]
    exact mul_le_mul_of_nonneg_left hden hCf
  have hB : ‖paperFT g (w τ)‖ ≤ Cg :=
    (hg' _ (hw τ)).trans (div_le_self hCg (one_le_pow₀ (by linarith [abs_nonneg (w τ).re])))
  have hm : (0 : ℝ) ≤ Z.mult τ := Nat.cast_nonneg _
  calc (Z.mult τ : ℝ) * ‖paperFT f (gammaOf τ)‖ * ‖paperFT g (w τ)‖
      ≤ (Z.mult τ : ℝ) * (Cf * ((4 / 3) / (1 + Complex.normSq (gammaOf τ)))) * Cg :=
        mul_le_mul (mul_le_mul_of_nonneg_left hA hm) hB (norm_nonneg _)
          (mul_nonneg hm (mul_nonneg hCf (div_nonneg (by norm_num) hN.le)))
    _ = 4 / 3 * Cf * Cg * ((Z.mult τ : ℝ) / (1 + Complex.normSq (gammaOf τ))) := by ring

/-- The Weil summands of compactly supported `C²` tests are absolutely summable on a tempered
configuration. -/
theorem summable_norm_Wsummand (Z : ZeroConfig) (hZ : TemperedConfig Z) {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) : Summable fun τ : Z.carrier => ‖Z.Wsummand f g τ‖ := by
  refine (summable_mult_norm_mul Z hZ hf hfc hg hgc (fun τ => conj (gammaOf τ)) fun τ => ?_).congr
    fun τ => ?_
  · rw [Complex.conj_im, abs_neg]
    exact abs_im_gammaOf_le Z τ
  · rw [ZeroConfig.Wsummand, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_conj]

theorem summable_Wsummand (Z : ZeroConfig) (hZ : TemperedConfig Z) {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) : Summable fun τ : Z.carrier => Z.Wsummand f g τ :=
  (summable_norm_Wsummand Z hZ hf hfc hg hgc).of_norm

theorem summable_re_Wsummand (Z : ZeroConfig) (hZ : TemperedConfig Z) {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) : Summable fun τ : Z.carrier => (Z.Wsummand f g τ).re :=
  Summable.of_norm_bounded (summable_norm_Wsummand Z hZ hf hfc hg hgc) fun _ =>
    (Real.norm_eq_abs _).trans_le (Complex.abs_re_le_norm _)

/-- On a tempered configuration the Gram form is Weil's form of the conjugate-weighted
combination. -/
theorem hermQuad_zeroGram_of_tempered (Z : ZeroConfig) (hZ : TemperedConfig Z) {ι : Type*}
    [Fintype ι] (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) (x : ι → ℂ) :
    hermQuad (zeroGram Z f) x = (Z.W (∑ i, conj (x i) • f i) (∑ i, conj (x i) • f i)).re := by
  set T : Z.carrier → ι → ι → ℂ := fun ρ i j => conj (x i) * (Z.Wsummand (f i) (f j) ρ * x j)
    with hT
  have hs : ∀ i j, Summable fun ρ => T ρ i j := fun i j =>
    ((summable_Wsummand Z hZ (hf i) (hfc i) (hf j) (hfc j)).mul_right (x j)).mul_left (conj (x i))
  have hR : Z.W (∑ i, conj (x i) • f i) (∑ i, conj (x i) • f i) = ∑' ρ, ∑ i, ∑ j, T ρ i j := by
    rw [ZeroConfig.W]
    refine tsum_congr fun ρ => ?_
    simp only [ZeroConfig.Wsummand, paperFT_sum_smul f (fun i => (hf i).continuous) hfc, hT]
    rw [map_sum, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul, conj_conj]
    ring
  have hL : star x ⬝ᵥ (zeroGram Z f *ᵥ x) = ∑ i, ∑ j, ∑' ρ, T ρ i j := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Complex.star_def, zeroGram, ZeroConfig.W,
      Finset.mul_sum, hT]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← tsum_mul_right, ← tsum_mul_left]
  rw [hermQuad, hL, hR, Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hs i j]
  congr 1
  exact Finset.sum_congr rfl fun i _ => (Summable.tsum_finsetSum fun j _ => hs i j).symm

/-! ### The upper bound -/

/-- **Upper bound.** On a tempered configuration the Weil form has at most `#{Re ρ > ½}` negative
squares on any finite family of compactly supported `C²` tests. -/
theorem negIndex_zeroGram_le_of_tempered (Z : ZeroConfig) (hZ : TemperedConfig Z) {ι : Type*}
    [Fintype ι] (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) :
    (hermNegIndex (zeroGram Z f) : ℕ∞) ≤ (rightZeros Z).encard := by
  rcases (rightZeros Z).finite_or_infinite with hR | hR
  · haveI := hR.fintype
    rw [hR.encard_eq_coe_toFinset_card, Set.Finite.card_toFinset]
    refine ENat.coe_le_coe.mpr (negIndex_le_card_of_nonneg_on_ker _
      (fun ρ : rightZeros Z => evalFunctional f (gammaOf ρ)) fun x hx => ?_)
    have hFv : ∀ ρ ∈ Z.carrier, 1 / 2 < ρ.re →
        paperFT (∑ i, conj (x i) • f i) (gammaOf ρ) = 0 := by
      intro ρ hρ hre
      have := hx ⟨ρ, hρ, hre⟩
      rw [evalFunctional_eq f (fun i => (hf i).continuous) hfc] at this
      simpa using this
    have hFd := contDiff_sum_smul f hf fun i => conj (x i)
    have hFc := hasCompactSupport_sum_smul f hfc fun i => conj (x i)
    rw [hermQuad_zeroGram_of_tempered Z hZ f hf hfc, ZeroConfig.W,
      Complex.re_tsum (summable_Wsummand Z hZ hFd hFc hFd hFc)]
    exact tsum_nonneg fun ρ => re_Wsummand_nonneg Z hFv ρ
  · rw [hR.encard_eq]
    exact le_top

/-! ### Dual tests and translated pairs -/

/-- Interpolation of transforms at finitely many distinct points, indexed by any finite type. -/
theorem exists_test_interpolating_fintype {κ : Type*} [Fintype κ] (z : κ → ℂ)
    (hz : Function.Injective z) (b : κ → ℂ) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ ∀ k, paperFT f (z k) = b k := by
  classical
  obtain ⟨f, hf, hfc, hv⟩ := exists_test_interpolating (z ∘ (Fintype.equivFin κ).symm)
    (hz.comp (Fintype.equivFin κ).symm.injective) (b ∘ (Fintype.equivFin κ).symm)
  exact ⟨f, hf, hfc, fun k => by simpa using hv (Fintype.equivFin κ k)⟩

/-- **Dual tests.** For finitely many points `ρ` right of the line there are compactly supported
`C²` tests with `h_{b_ρ}(γ_σ) = h_{b_ρ}(γ̄_σ) = δ_{ρσ}`. -/
theorem exists_dual_tests {R : Finset ℂ} (hR : ∀ ρ ∈ R, 1 / 2 < ρ.re) :
    ∃ b : R → ℝ → ℂ, (∀ ρ, ContDiff ℝ 2 (b ρ)) ∧ (∀ ρ, HasCompactSupport (b ρ)) ∧
      (∀ ρ σ : R, paperFT (b ρ) (gammaOf σ) = if σ = ρ then 1 else 0) ∧
      (∀ ρ σ : R, paperFT (b ρ) (conj (gammaOf σ)) = if σ = ρ then 1 else 0) := by
  classical
  set z : R ⊕ R → ℂ := Sum.elim (fun σ => gammaOf σ) (fun σ => conj (gammaOf σ))
  have him : ∀ ρ : ℂ, (gammaOf ρ).im = 1 / 2 - ρ.re := fun ρ => by simp [gammaOf]
  have hz : Function.Injective z := by
    rintro (σ | σ) (σ' | σ') h <;> simp only [z, Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (Subtype.ext (gammaOf_injective h))
    · have := congrArg Complex.im h
      rw [Complex.conj_im, him, him] at this
      linarith [hR _ σ.2, hR _ σ'.2]
    · have := congrArg Complex.im h
      rw [Complex.conj_im, him, him] at this
      linarith [hR _ σ.2, hR _ σ'.2]
    · have := congrArg conj h
      simp only [conj_conj] at this
      exact congrArg Sum.inr (Subtype.ext (gammaOf_injective this))
  choose b hb hbc hbv using fun ρ : R => exists_test_interpolating_fintype z hz
    (Sum.elim (fun σ => if σ = ρ then 1 else 0) (fun σ => if σ = ρ then 1 else 0))
  exact ⟨b, hb, hbc, fun ρ σ => hbv ρ (Sum.inl σ), fun ρ σ => hbv ρ (Sum.inr σ)⟩

/-- The phased translate `u ↦ ω b(u − L)`. -/
def phasedTranslate (b : ℝ → ℂ) (ω : ℂ) (L : ℝ) : ℝ → ℂ := fun u => ω * b (u - L)

/-- **Translation**: `h_{ω b(· − L)}(z) = ω e^{izL} h_b(z)`. -/
theorem paperFT_phasedTranslate (b : ℝ → ℂ) (ω : ℂ) (L : ℝ) (z : ℂ) :
    paperFT (phasedTranslate b ω L) z = ω * cexp (I * z * L) * paperFT b z := by
  set G : ℝ → ℂ := fun v => ω * (b v * cexp (I * z * v) * cexp (I * z * L))
  have h1 : (fun u => phasedTranslate b ω L u * cexp (I * z * u)) = fun u => G (u - L) := by
    funext u
    simp only [phasedTranslate, G]
    rw [mul_assoc ω, mul_assoc (b (u - L)), ← Complex.exp_add]
    congr 3
    push_cast
    ring
  rw [paperFT, h1, MeasureTheory.integral_sub_right_eq_self]
  simp only [G]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const, paperFT]
  ring

/-- The doubled family `b_ρ, ω_ρ b_ρ(· − L)`. -/
def pairFamily {R : Type*} (b : R → ℝ → ℂ) (ω : R → ℂ) (L : ℝ) (p : R × Fin 2) : ℝ → ℂ :=
  if p.2 = 0 then b p.1 else phasedTranslate (b p.1) (ω p.1) L

theorem pairFamily_contDiff {R : Type*} {b : R → ℝ → ℂ} (hb : ∀ ρ, ContDiff ℝ 2 (b ρ))
    (ω : R → ℂ) (L : ℝ) (p : R × Fin 2) : ContDiff ℝ 2 (pairFamily b ω L p) := by
  unfold pairFamily phasedTranslate
  split_ifs
  · exact hb _
  · exact contDiff_const.mul ((hb _).comp (contDiff_id.sub contDiff_const))

theorem pairFamily_hasCompactSupport {R : Type*} {b : R → ℝ → ℂ}
    (hbc : ∀ ρ, HasCompactSupport (b ρ)) (ω : R → ℂ) (L : ℝ) (p : R × Fin 2) :
    HasCompactSupport (pairFamily b ω L p) := by
  unfold pairFamily phasedTranslate
  split_ifs
  · exact hbc _
  · exact ((hbc p.1).comp_homeomorph (Homeomorph.subRight L)).mul_left (f := fun _ => ω p.1)

/-- The transform of the combination `Σ_ρ conj(y_ρ) (b_ρ + ω_ρ b_ρ(· − L))`. -/
theorem paperFT_pairComb {R : Type*} [Fintype R] {b : R → ℝ → ℂ} (hb : ∀ ρ, ContDiff ℝ 2 (b ρ))
    (hbc : ∀ ρ, HasCompactSupport (b ρ)) (ω : R → ℂ) (L : ℝ) (y : R → ℂ) (z : ℂ) :
    paperFT (∑ p : R × Fin 2, conj (y p.1) • pairFamily b ω L p) z =
      ∑ ρ, conj (y ρ) * (1 + ω ρ * cexp (I * z * L)) * paperFT (b ρ) z := by
  rw [paperFT_sum_smul _ (fun p => (pairFamily_contDiff hb ω L p).continuous)
    (pairFamily_hasCompactSupport hbc ω L), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have h0 : pairFamily b ω L (ρ, 0) = b ρ := if_pos rfl
  have h1 : pairFamily b ω L (ρ, 1) = phasedTranslate (b ρ) (ω ρ) L := if_neg (by simp)
  rw [Fin.sum_univ_two, h0, h1, paperFT_phasedTranslate]
  ring

/-- At a point where the dual tests read off `σ`, the combination reads off `y_σ`. -/
theorem paperFT_pairComb_of_dual {R : Type*} [Fintype R] [DecidableEq R] {b : R → ℝ → ℂ}
    (hb : ∀ ρ, ContDiff ℝ 2 (b ρ)) (hbc : ∀ ρ, HasCompactSupport (b ρ)) (ω : R → ℂ) (L : ℝ)
    (y : R → ℂ) {z : ℂ} {σ : R} (hz : ∀ ρ, paperFT (b ρ) z = if σ = ρ then 1 else 0) :
    paperFT (∑ p : R × Fin 2, conj (y p.1) • pairFamily b ω L p) z =
      conj (y σ) * (1 + ω σ * cexp (I * z * L)) := by
  rw [paperFT_pairComb hb hbc, Finset.sum_eq_single σ]
  · rw [hz, if_pos rfl, mul_one]
  · intro ρ _ hρ
    rw [hz, if_neg (Ne.symm hρ), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ σ) h

/-- The phase `ω = −e^{−i Im ρ · L}` of a zero `ρ`. -/
def phase (L : ℝ) (ρ : ℂ) : ℂ := -cexp (-(I * ρ.im * L))

theorem norm_phase (L : ℝ) (ρ : ℂ) : ‖phase L ρ‖ = 1 := by
  rw [phase, norm_neg, Complex.norm_exp]
  simp

theorem gammaOf_eq (ρ : ℂ) : gammaOf ρ = (ρ.im : ℂ) - I * ((ρ.re - 1 / 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [gammaOf]

/-- The phase turns `e^{iγ_ρ L}` into `−e^{(Re ρ − ½)L}`. -/
theorem phase_mul_cexp_gammaOf (L : ℝ) (ρ : ℂ) :
    phase L ρ * cexp (I * gammaOf ρ * L) = -((Real.exp ((ρ.re - 1 / 2) * L) : ℝ) : ℂ) := by
  rw [phase, neg_mul, ← Complex.exp_add, Complex.ofReal_exp]
  congr 2
  rw [gammaOf_eq]
  push_cast
  linear_combination (-(((ρ.re : ℂ) - 1 / 2) * L)) * I_sq

/-- The phase turns `e^{iγ̄_ρ L}` into `−e^{−(Re ρ − ½)L}`. -/
theorem phase_mul_cexp_conj_gammaOf (L : ℝ) (ρ : ℂ) :
    phase L ρ * cexp (I * conj (gammaOf ρ) * L) =
      -((Real.exp (-((ρ.re - 1 / 2) * L)) : ℝ) : ℂ) := by
  rw [phase, neg_mul, ← Complex.exp_add, Complex.ofReal_exp]
  congr 2
  rw [gammaOf_eq, map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
  push_cast
  linear_combination (((ρ.re : ℂ) - 1 / 2) * L) * I_sq

/-- A test whose transform is `conj(u)(1 − a)` at `γ_ρ` and `conj(u)(1 − a')` at `γ̄_ρ` has the
real Weil summand `m_ρ |u|² (1 − a)(1 − a')` at `ρ`. -/
theorem Wsummand_eq_of_values (Z : ZeroConfig) (F : ℝ → ℂ) (ρ u : ℂ) (a a' : ℝ)
    (h1 : paperFT F (gammaOf ρ) = conj u * (1 - (a : ℂ)))
    (h2 : paperFT F (conj (gammaOf ρ)) = conj u * (1 - (a' : ℂ))) :
    Z.Wsummand F F ρ = ((Z.mult ρ * ‖u‖ ^ 2 * ((1 - a) * (1 - a')) : ℝ) : ℂ) := by
  rw [ZeroConfig.Wsummand, h1, h2, map_mul, Complex.conj_conj, map_sub, map_one,
    Complex.conj_ofReal]
  have hu : conj u * u = (‖u‖ : ℂ) ^ 2 := Complex.conj_mul' u
  push_cast
  linear_combination ((Z.mult ρ : ℂ) * (1 - (a : ℂ)) * (1 - (a' : ℂ))) * hu

/-- The Weil summand at the reflected zero is the conjugate. -/
theorem Wsummand_reflect (Z : ZeroConfig) (F : ℝ → ℂ) {σ : ℂ} (hσ : σ ∈ Z.carrier) :
    Z.Wsummand F F (reflect σ) = conj (Z.Wsummand F F σ) := by
  simp only [ZeroConfig.Wsummand, gammaOf_reflect, Z.mult_reflect σ hσ, conj_conj, map_mul,
    map_natCast]
  ring

/-- **On-line bound.** On the line the phases have modulus one, and a zero `τ` contributes at most
`4 |y|² m_τ Σ_ρ |h_{b_ρ}(γ_τ)|²`. -/
theorem re_Wsummand_pairComb_le_of_onLine (Z : ZeroConfig) {R : Type*} [Fintype R]
    {b : R → ℝ → ℂ} (hb : ∀ ρ, ContDiff ℝ 2 (b ρ)) (hbc : ∀ ρ, HasCompactSupport (b ρ))
    (r : R → ℂ) (L : ℝ) (y : R → ℂ) {τ : ℂ} (hτ : τ.re = 1 / 2) :
    (Z.Wsummand (∑ p : R × Fin 2, conj (y p.1) • pairFamily b (fun ρ => phase L (r ρ)) L p)
      (∑ p : R × Fin 2, conj (y p.1) • pairFamily b (fun ρ => phase L (r ρ)) L p) τ).re ≤
      4 * (∑ ρ, ‖y ρ‖ ^ 2) * ∑ ρ, (Z.mult τ : ℝ) * ‖paperFT (b ρ) (gammaOf τ)‖ ^ 2 := by
  set F := ∑ p : R × Fin 2, conj (y p.1) • pairFamily b (fun ρ => phase L (r ρ)) L p with hF
  have hγim : (gammaOf τ).im = 0 := by simp [gammaOf, hτ]
  have hγ : conj (gammaOf τ) = gammaOf τ := Complex.conj_eq_iff_im.mpr hγim
  have hre : (Z.Wsummand F F τ).re = (Z.mult τ : ℝ) * ‖paperFT F (gammaOf τ)‖ ^ 2 := by
    rw [ZeroConfig.Wsummand, hγ, mul_assoc, Complex.mul_conj, ← Complex.ofReal_natCast,
      ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hE : ‖cexp (I * gammaOf τ * L)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, hγim]
  have hph : ∀ ρ, ‖1 + phase L (r ρ) * cexp (I * gammaOf τ * L)‖ ≤ 2 := fun ρ => by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul, norm_phase, hE]
    norm_num
  have hnorm : ‖paperFT F (gammaOf τ)‖ ≤ ∑ ρ, ‖y ρ‖ * (2 * ‖paperFT (b ρ) (gammaOf τ)‖) := by
    rw [hF, paperFT_pairComb hb hbc]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_conj]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hph ρ) (norm_nonneg _))
      (norm_nonneg _)).trans_eq (by ring)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun ρ => ‖y ρ‖)
    (fun ρ => 2 * ‖paperFT (b ρ) (gammaOf τ)‖)
  have h4 : ∑ ρ, (2 * ‖paperFT (b ρ) (gammaOf τ)‖) ^ 2 =
      4 * ∑ ρ, ‖paperFT (b ρ) (gammaOf τ)‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ρ _ => by ring
  have hsq : ‖paperFT F (gammaOf τ)‖ ^ 2 ≤
      4 * (∑ ρ, ‖y ρ‖ ^ 2) * ∑ ρ, ‖paperFT (b ρ) (gammaOf τ)‖ ^ 2 := by
    calc ‖paperFT F (gammaOf τ)‖ ^ 2
        ≤ (∑ ρ, ‖y ρ‖ * (2 * ‖paperFT (b ρ) (gammaOf τ)‖)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ ≤ (∑ ρ, ‖y ρ‖ ^ 2) * ∑ ρ, (2 * ‖paperFT (b ρ) (gammaOf τ)‖) ^ 2 := hcs
      _ = _ := by rw [h4]; ring
  rw [hre, ← Finset.mul_sum]
  have hm : (0 : ℝ) ≤ Z.mult τ := Nat.cast_nonneg _
  calc (Z.mult τ : ℝ) * ‖paperFT F (gammaOf τ)‖ ^ 2
      ≤ (Z.mult τ : ℝ) * (4 * (∑ ρ, ‖y ρ‖ ^ 2) * ∑ ρ, ‖paperFT (b ρ) (gammaOf τ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hm
    _ = _ := by ring

/-! ### Attainment -/

/-- **Negativity of the translated pairs.** With dual tests `b_ρ` for the zeros `R` right of the
line, the on-line mass `A`, and an aperture with `(Re ρ − ½) L ≥ 4A + 2`, the Weil form of
`Σ_ρ conj(y_ρ)(b_ρ + ω_ρ b_ρ(· − L))` is at most `−Σ_ρ |y_ρ|²`. -/
theorem re_W_pairComb_le (Z : ZeroConfig) (hZ : TemperedConfig Z) {R : Finset ℂ}
    (hRm : ∀ ρ : R, (ρ : ℂ) ∈ Z.carrier ∧ 1 / 2 < (ρ : ℂ).re)
    (hRall : ∀ τ ∈ Z.carrier, 1 / 2 < τ.re → τ ∈ R)
    {b : R → ℝ → ℂ} (hb : ∀ ρ, ContDiff ℝ 2 (b ρ)) (hbc : ∀ ρ, HasCompactSupport (b ρ))
    (hb1 : ∀ ρ σ : R, paperFT (b ρ) (gammaOf σ) = if σ = ρ then 1 else 0)
    (hb2 : ∀ ρ σ : R, paperFT (b ρ) (conj (gammaOf σ)) = if σ = ρ then 1 else 0)
    {L : ℝ} (hL : ∀ ρ : R, 4 * (∑' τ : Z.carrier, ∑ ρ, (Z.mult τ : ℝ) *
      ‖paperFT (b ρ) (gammaOf τ)‖ ^ 2) + 2 ≤ ((ρ : ℂ).re - 1 / 2) * L)
    (y : R → ℂ) :
    (Z.W (∑ p : R × Fin 2, conj (y p.1) • pairFamily b (fun ρ => phase L ρ) L p)
      (∑ p : R × Fin 2, conj (y p.1) • pairFamily b (fun ρ => phase L ρ) L p)).re ≤
      -∑ ρ, ‖y ρ‖ ^ 2 := by
  classical
  set F := ∑ p : R × Fin 2, conj (y p.1) • pairFamily b (fun ρ => phase L ρ) L p with hF
  have hFd : ContDiff ℝ 2 F := contDiff_sum_smul _ (pairFamily_contDiff hb _ L) _
  have hFc : HasCompactSupport F := hasCompactSupport_sum_smul _ (pairFamily_hasCompactSupport hbc _ L) _
  set S : Z.carrier → ℝ := fun τ => ∑ ρ, (Z.mult τ : ℝ) * ‖paperFT (b ρ) (gammaOf τ)‖ ^ 2 with hSdef
  have hS : Summable S := summable_sum fun ρ _ => (summable_mult_norm_mul Z hZ (hb ρ) (hbc ρ)
    (hb ρ) (hbc ρ) (fun τ => gammaOf τ) (abs_im_gammaOf_le Z)).congr fun τ => by ring
  set A := ∑' τ, S τ with hAdef
  have hA0 : 0 ≤ A := tsum_nonneg fun τ => Finset.sum_nonneg fun ρ _ => by positivity
  set Y := ∑ ρ, ‖y ρ‖ ^ 2 with hYdef
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun ρ _ => by positivity
  set δ : R → ℝ := fun ρ => (ρ : ℂ).re - 1 / 2 with hδdef
  set v : R → ℝ := fun ρ => (Z.mult ρ : ℝ) * ‖y ρ‖ ^ 2 *
    ((1 - Real.exp (δ ρ * L)) * (1 - Real.exp (-(δ ρ * L)))) with hvdef
  -- the summand at a zero right of the line
  have hright : ∀ ρ : R, Z.Wsummand F F ρ = (v ρ : ℂ) := fun ρ => by
    refine Wsummand_eq_of_values Z F ρ (y ρ) _ _ ?_ ?_
    · rw [hF, paperFT_pairComb_of_dual hb hbc _ L y fun σ => hb1 σ ρ, phase_mul_cexp_gammaOf,
        ← sub_eq_add_neg]
    · rw [hF, paperFT_pairComb_of_dual hb hbc _ L y fun σ => hb2 σ ρ,
        phase_mul_cexp_conj_gammaOf, ← sub_eq_add_neg]
  -- each right zero pays at least `4A + 1` per unit of `|y_ρ|²`
  have hv : ∀ ρ : R, v ρ ≤ ‖y ρ‖ ^ 2 * (-4 * A - 1) := fun ρ => by
    have ha := Real.add_one_le_exp (δ ρ * L)
    have haa : Real.exp (δ ρ * L) * Real.exp (-(δ ρ * L)) = 1 := by
      rw [← Real.exp_add]; simp
    have ha' := Real.exp_pos (-(δ ρ * L))
    have hLρ : 4 * A + 2 ≤ δ ρ * L := hL ρ
    have hP : (1 - Real.exp (δ ρ * L)) * (1 - Real.exp (-(δ ρ * L))) ≤ -4 * A - 1 := by
      nlinarith
    have hP0 : (1 - Real.exp (δ ρ * L)) * (1 - Real.exp (-(δ ρ * L))) ≤ 0 := by linarith
    have hm : (1 : ℝ) ≤ Z.mult ρ := by exact_mod_cast Z.one_le_mult _ (hRm ρ).1
    have hmP : (Z.mult ρ : ℝ) * ((1 - Real.exp (δ ρ * L)) * (1 - Real.exp (-(δ ρ * L)))) ≤
        -4 * A - 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hm) (neg_nonneg.mpr hP0)]
    calc v ρ = ‖y ρ‖ ^ 2 * ((Z.mult ρ : ℝ) *
          ((1 - Real.exp (δ ρ * L)) * (1 - Real.exp (-(δ ρ * L))))) := by
          simp only [hvdef]; ring
      _ ≤ ‖y ρ‖ ^ 2 * (-4 * A - 1) := mul_le_mul_of_nonneg_left hmP (by positivity)
  have hv0 : ∀ ρ : R, v ρ ≤ 0 := fun ρ =>
    (hv ρ).trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith))
  -- the off-line ledger: the right zeros, as points of the carrier
  set ι : R → Z.carrier := fun ρ => ⟨ρ, (hRm ρ).1⟩ with hιdef
  set E : Z.carrier → ℝ := fun τ => ∑ ρ, if τ = ι ρ then v ρ else 0 with hEdef
  have hE0 : ∀ τ : Z.carrier, (τ : ℂ).re ≤ 1 / 2 → E τ = 0 := fun τ hτ =>
    Finset.sum_eq_zero fun ρ _ => if_neg fun h => by
      have : (τ : ℂ) = ρ := congrArg Subtype.val h
      linarith [(hRm ρ).2, congrArg Complex.re this]
  have hpt : ∀ τ : Z.carrier, (Z.Wsummand F F τ).re ≤ 4 * Y * S τ + E τ := by
    intro τ
    have hSτ : 0 ≤ 4 * Y * S τ :=
      mul_nonneg (mul_nonneg (by norm_num) hY0) (Finset.sum_nonneg fun ρ _ => by positivity)
    rcases lt_trichotomy (τ : ℂ).re (1 / 2) with hlt | heq | hgt
    · -- left of the line: the conjugate of the summand at the reflected right zero
      have hre : 1 / 2 < (reflect (τ : ℂ)).re := by
        simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
        linarith
      have hrefl : reflect (τ : ℂ) ∈ R := hRall _ (Z.reflect_mem _ τ.2) hre
      have hrr : reflect (reflect (τ : ℂ)) = τ := by simp [reflect]
      have h1 := Wsummand_reflect Z F (Z.reflect_mem _ τ.2)
      rw [hrr] at h1
      have h2 : Z.Wsummand F F (reflect (τ : ℂ)) = (v ⟨reflect τ, hrefl⟩ : ℂ) :=
        hright ⟨reflect τ, hrefl⟩
      rw [h1, Complex.conj_re, h2, Complex.ofReal_re, hE0 τ hlt.le]
      linarith [hv0 ⟨reflect τ, hrefl⟩]
    · rw [hE0 τ heq.le, add_zero]
      exact re_Wsummand_pairComb_le_of_onLine Z hb hbc (fun ρ => ρ) L y heq
    · set ρ₀ : R := ⟨τ, hRall _ τ.2 hgt⟩
      have hEτ : E τ = v ρ₀ := by
        simp only [hEdef]
        rw [Finset.sum_eq_single (f := fun ρ => if τ = ι ρ then v ρ else 0) ρ₀
          (fun ρ _ hρ => if_neg fun (h : τ = ι ρ) => hρ (Subtype.ext (congrArg Subtype.val h).symm))
          (fun h => absurd (Finset.mem_univ _) h), if_pos (Subtype.ext rfl)]
      have h2 : Z.Wsummand F F τ = (v ρ₀ : ℂ) := hright ρ₀
      rw [h2, Complex.ofReal_re, hEτ]
      linarith
  have hEs : ∀ ρ : R, HasSum (fun τ : Z.carrier => if τ = ι ρ then v ρ else 0) (v ρ) :=
    fun ρ => hasSum_ite_eq (ι ρ) (v ρ)
  have hEsum : HasSum E (∑ ρ, v ρ) := hasSum_sum fun ρ _ => hEs ρ
  have hYv : ∑ ρ, v ρ ≤ Y * (-4 * A - 1) := by
    rw [hYdef, Finset.sum_mul]
    exact Finset.sum_le_sum fun ρ _ => hv ρ
  rw [ZeroConfig.W, Complex.re_tsum (summable_Wsummand Z hZ hFd hFc hFd hFc)]
  calc ∑' τ : Z.carrier, (Z.Wsummand F F τ).re ≤ ∑' τ, (4 * Y * S τ + E τ) :=
        Summable.tsum_le_tsum hpt (summable_re_Wsummand Z hZ hFd hFc hFd hFc)
          ((hS.mul_left _).add hEsum.summable)
    _ = 4 * Y * A + ∑ ρ, v ρ := by
        rw [Summable.tsum_add (hS.mul_left _) hEsum.summable, tsum_mul_left, hEsum.tsum_eq]
    _ ≤ 4 * Y * A + Y * (-4 * A - 1) := by linarith
    _ = -Y := by ring

/-- **Attainment.** A tempered configuration with finitely many zeros right of the critical line
has a family of compactly supported `C²` tests, two per such zero, on which its Weil form has at
least that many negative squares. -/
theorem exists_zeroGram_negIndex_ge_of_tempered (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hR : (rightZeros Z).Finite) :
    ∃ f : hR.toFinset × Fin 2 → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧
      (∀ i, HasCompactSupport (f i)) ∧ hR.toFinset.card ≤ hermNegIndex (zeroGram Z f) := by
  classical
  set R := hR.toFinset with hRdef
  have hRm : ∀ ρ : R, (ρ : ℂ) ∈ Z.carrier ∧ 1 / 2 < (ρ : ℂ).re := fun ρ => by
    have := (Set.Finite.mem_toFinset hR).mp ρ.2
    simpa [rightZeros] using this
  have hRall : ∀ τ ∈ Z.carrier, 1 / 2 < τ.re → τ ∈ R := fun τ hτ hre =>
    (Set.Finite.mem_toFinset hR).mpr ⟨hτ, hre⟩
  obtain ⟨b, hb, hbc, hb1, hb2⟩ := exists_dual_tests (R := R) fun ρ hρ => (hRm ⟨ρ, hρ⟩).2
  -- the on-line mass of the dual tests, and an aperture beyond it
  set A := ∑' τ : Z.carrier, ∑ ρ, (Z.mult τ : ℝ) * ‖paperFT (b ρ) (gammaOf τ)‖ ^ 2 with hAdef
  have hA0 : 0 ≤ A := tsum_nonneg fun τ => Finset.sum_nonneg fun ρ _ => by positivity
  have hδ : ∀ ρ : R, 0 < (ρ : ℂ).re - 1 / 2 := fun ρ => by linarith [(hRm ρ).2]
  set L : ℝ := ∑ ρ : R, (4 * A + 2) / ((ρ : ℂ).re - 1 / 2) with hLdef
  have hL : ∀ ρ : R, 4 * A + 2 ≤ ((ρ : ℂ).re - 1 / 2) * L := fun ρ => by
    have h := Finset.single_le_sum (f := fun σ : R => (4 * A + 2) / ((σ : ℂ).re - 1 / 2))
      (fun σ _ => div_nonneg (by linarith) (hδ σ).le) (Finset.mem_univ ρ)
    calc 4 * A + 2 = ((ρ : ℂ).re - 1 / 2) * ((4 * A + 2) / ((ρ : ℂ).re - 1 / 2)) := by
          rw [mul_div_assoc', mul_div_cancel_left₀ _ (hδ ρ).ne']
      _ ≤ ((ρ : ℂ).re - 1 / 2) * L := mul_le_mul_of_nonneg_left h (hδ ρ).le
  refine ⟨pairFamily b (fun ρ => phase L ρ) L, pairFamily_contDiff hb _ L,
    pairFamily_hasCompactSupport hbc _ L, ?_⟩
  -- negative definiteness on the diagonal embedding `y ↦ (y_ρ, y_ρ)`
  set Φ : (R → ℂ) →ₗ[ℂ] (R × Fin 2 → ℂ) := LinearMap.funLeft ℂ ℂ Prod.fst with hΦdef
  have hΦ : Function.Injective Φ :=
    LinearMap.funLeft_injective_of_surjective ℂ ℂ Prod.fst fun ρ => ⟨(ρ, 0), rfl⟩
  have hpd : IsPosDefOn (-(zeroGram Z (pairFamily b (fun ρ => phase L ρ) L)))
      (LinearMap.range Φ) := by
    intro x hx hx0
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    have hy : y ≠ 0 := fun h => hx0 (by rw [h, map_zero])
    obtain ⟨ρ, hρ⟩ := Function.ne_iff.mp hy
    have hYpos : 0 < ∑ σ, ‖y σ‖ ^ 2 :=
      lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun σ => ‖y σ‖ ^ 2)
        (fun σ _ => by positivity) (Finset.mem_univ ρ))
    rw [hermQuad_neg, hermQuad_zeroGram_of_tempered Z hZ _ (pairFamily_contDiff hb _ L)
      (pairFamily_hasCompactSupport hbc _ L)]
    simp only [hΦdef, LinearMap.funLeft_apply]
    linarith [re_W_pairComb_le Z hZ hRm hRall hb hbc hb1 hb2 hL y]
  have h1 := finrank_le_posIndex hpd
  rw [LinearMap.finrank_range_of_inj hΦ, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe] at h1
  rw [hermNegIndex]
  exact h1

/-- **The Pontryagin law of a tempered configuration.** If finitely many zeros lie right of the
critical line, the largest number of negative squares of the Weil form on a finite family of
compactly supported `C²` tests is their number. -/
theorem pontryagin_law_of_tempered (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hR : (rightZeros Z).Finite) :
    (∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) → (∀ i, HasCompactSupport (f i)) →
      hermNegIndex (zeroGram Z f) ≤ hR.toFinset.card) ∧
    ∃ f : hR.toFinset × Fin 2 → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧
      (∀ i, HasCompactSupport (f i)) ∧ hermNegIndex (zeroGram Z f) = hR.toFinset.card := by
  have hle : ∀ {ι : Type} [Fintype ι] (f : ι → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) →
      (∀ i, HasCompactSupport (f i)) → hermNegIndex (zeroGram Z f) ≤ hR.toFinset.card := by
    intro ι _ f hf hfc
    have h := negIndex_zeroGram_le_of_tempered Z hZ f hf hfc
    rw [hR.encard_eq_coe_toFinset_card] at h
    exact_mod_cast h
  obtain ⟨f, hf, hfc, hge⟩ := exists_zeroGram_negIndex_ge_of_tempered Z hZ hR
  exact ⟨fun n g hg hgc => hle g hg hgc, f, hf, hfc, le_antisymm (hle f hf hfc) hge⟩

/-! ### The zeros of `ζ` -/

/-- For `ζ` the zero-side Gram matrix is the Weil Gram matrix of the explicit formula. -/
theorem weilGram_eq_zeroGram {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfc : ∀ i, HasCompactSupport (f i)) :
    weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f = zeroGram zetaZeroConfig f :=
  Matrix.ext fun i j =>
    (RHTower.zeta_W_eq_weilFullFunctional_mixed (hf i) (hfc i) (hf j) (hfc j)).symm

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
