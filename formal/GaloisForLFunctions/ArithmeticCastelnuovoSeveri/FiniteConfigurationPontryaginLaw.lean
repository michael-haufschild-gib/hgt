import Zeta23.Defs
import GaloisForLFunctions.HTGeometry.HermitianInertia
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The exact Pontryagin law of a finite zero configuration

For a zero configuration `Z` (a reflection-symmetric multiset of points of the strip) Weil's form is
`W_Z(f, g) = Σ_ρ m_ρ h_f(γ_ρ) conj h_g(γ̄_ρ)`, `γ_ρ = (ρ − ½)/i`. On the scaling surface its
negative squares are the excess positive squares of the intersection form (the signature law). For
a **finite** configuration they are counted exactly (`negIndex_zeroGram_le`,
`exists_zeroGram_negIndex_eq`):

    max over finite test families of #negative squares of W_Z = #{ρ ∈ Z : Re ρ > ½}.

* *Upper bound.* On combinations whose transforms vanish at the zeros right of the line every
  summand is `≥ 0` (on-line zeros give `m|h(γ)|²`, an off-line pair has the factor
  `h(γ_ρ)`, `Re ρ > ½`, in both of its terms), and a negative definite subspace meets that
  common kernel only in `0` (`negIndex_le_card_of_nonneg_on_ker`).
* *Attainment.* By **interpolation** (`exists_test_interpolating`) there are smooth compactly
  supported tests with prescribed transforms at finitely many points: translates `φ(· − jτ)` of a
  small bump have transforms `h_φ(z) e^{izjτ}`, with `h_φ(z) ≠ 0` once the support is short and a
  Vandermonde matrix in `e^{izτ}` that is invertible for small `τ`. Choosing `h_{f_ρ} = 1` at
  `γ_ρ`, `−1` at `γ̄_ρ` and `0` at every other zero makes the Gram matrix of `(f_ρ)_{Re ρ > ½}`
  diagonal with entries `−2 m_ρ`.

This is the finite-rank Krein–Langer law of the Weil form: the Hodge defect of a finite
configuration is exactly its number of zeros right of the critical line, multiplicities not counted.
-/

open Complex Matrix Finset
open scoped ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### Hermitian index calculus -/

section Index

variable {ι : Type*} [Fintype ι]

/-- `hermQuad` scales by `|c|²`. -/
theorem hermQuad_smul (H : Matrix ι ι ℂ) (c : ℂ) (x : ι → ℂ) :
    hermQuad H (c • x) = Complex.normSq c * hermQuad H x := by
  simp only [hermQuad, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  rw [← mul_assoc, Complex.star_def, Complex.mul_conj, Complex.re_ofReal_mul]

/-- A form with nonnegative quadratic values has no negative square. -/
theorem negIndex_eq_zero_of_hermQuad_nonneg {H : Matrix ι ι ℂ} (h : ∀ x, 0 ≤ hermQuad H x) :
    hermNegIndex H = 0 := by
  obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-H)
  rw [hermNegIndex, ← hrank, Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
  intro x hx
  by_contra hx0
  have := hW x hx hx0
  rw [hermQuad_neg] at this
  linarith [h x]

/-- A form with no negative square has nonnegative quadratic values. -/
theorem hermQuad_nonneg_of_negIndex_eq_zero {H : Matrix ι ι ℂ} (h : hermNegIndex H = 0)
    (x : ι → ℂ) : 0 ≤ hermQuad H x := by
  by_contra hneg
  push Not at hneg
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [hermQuad] at hneg
  have hpd : IsPosDefOn (-H) (Submodule.span ℂ {x}) := by
    intro y hy hy0
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hc : c ≠ 0 := by rintro rfl; simp at hy0
    rw [hermQuad_neg, hermQuad_smul]
    have : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc
    nlinarith
  have := finrank_le_posIndex hpd
  rw [finrank_span_singleton hx0] at this
  rw [hermNegIndex] at h
  omega

/-- **The abstract Pontryagin lemma.** If the form is nonnegative on the common kernel of `P`
linear functionals, it has at most `P` negative squares. -/
theorem negIndex_le_card_of_nonneg_on_ker {κ : Type*} [Fintype κ] (H : Matrix ι ι ℂ)
    (φ : κ → (ι → ℂ) →ₗ[ℂ] ℂ) (h : ∀ x, (∀ k, φ k x = 0) → 0 ≤ hermQuad H x) :
    hermNegIndex H ≤ Fintype.card κ := by
  obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-H)
  rw [hermNegIndex, ← hrank]
  set T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ) := LinearMap.pi φ
  have hker : LinearMap.ker (T.domRestrict W) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hy
    by_contra hy0
    have hyv : (y : ι → ℂ) ≠ 0 := fun h0 => hy0 (Subtype.ext h0)
    have hpos := hW _ y.2 hyv
    have hzero : ∀ k, φ k y = 0 := fun k => by
      have := congrFun hy k
      simpa [T] using this
    have := h y hzero
    rw [hermQuad_neg] at hpos
    linarith
  have hinj : Function.Injective (T.domRestrict W) := LinearMap.ker_eq_bot.mp hker
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fintype_fun_eq_card] at this

end Index

/-! ### Linear combinations of tests -/

section Combinations

variable {ι : Type*} [Fintype ι]

theorem contDiff_sum_smul (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (c : ι → ℂ) :
    ContDiff ℝ 2 (∑ i, c i • f i) := by
  have he : (∑ i, c i • f i) = fun x => ∑ i, c i • f i x := by
    funext x; simp
  rw [he]
  exact ContDiff.sum (fun i _ => (hf i).const_smul (c i))

theorem hasCompactSupport_sum_smul (f : ι → ℝ → ℂ) (hfc : ∀ i, HasCompactSupport (f i))
    (c : ι → ℂ) : HasCompactSupport (∑ i, c i • f i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using (HasCompactSupport.zero : HasCompactSupport (0 : ℝ → ℂ))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hfc a).smul_left.add ih

/-- The transform is linear on finite combinations of compactly supported continuous tests. -/
theorem paperFT_sum_smul (f : ι → ℝ → ℂ) (hf : ∀ i, Continuous (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) (c : ι → ℂ) (z : ℂ) :
    paperFT (∑ i, c i • f i) z = ∑ i, c i * paperFT (f i) z := by
  have hint : ∀ i, MeasureTheory.Integrable (fun u => f i u * Complex.exp (I * z * u)) := fun i =>
    ((hf i).mul (by fun_prop)).integrable_of_hasCompactSupport (hfc i).mul_right
  simp only [paperFT, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum _ fun i _ => (hint i).const_mul (c i) |>.congr
    (Filter.Eventually.of_forall fun u => by ring)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← MeasureTheory.integral_const_mul]
  congr 1; funext u; ring

/-- The transform at `z` of a conjugate-weighted combination, as a linear functional of the
weights: `x ↦ Σ_i x_i conj h_{f_i}(z)`. -/
def evalFunctional (f : ι → ℝ → ℂ) (z : ℂ) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun x := ∑ i, x i * conj (paperFT (f i) z)
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_assoc]

theorem evalFunctional_eq (f : ι → ℝ → ℂ) (hf : ∀ i, Continuous (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) (z : ℂ) (x : ι → ℂ) :
    evalFunctional f z x = conj (paperFT (∑ i, conj (x i) • f i) z) := by
  rw [paperFT_sum_smul f hf hfc, map_sum]
  simp [evalFunctional, mul_comm]

end Combinations

/-- `γ` of the reflected zero is the conjugate of `γ`. -/
theorem gammaOf_reflect (ρ : ℂ) : gammaOf (reflect ρ) = conj (gammaOf ρ) := by
  simp only [gammaOf, reflect, map_div₀, map_sub, Complex.conj_I, map_one, map_ofNat]
  field_simp
  ring

theorem gammaOf_injective : Function.Injective gammaOf := by
  intro a b h
  simp only [gammaOf] at h
  have := (div_left_inj' Complex.I_ne_zero).mp h
  linear_combination this

/-- The zero summand of `W_Z(F, F)` has nonnegative real part once `h_F` vanishes at the zeros of
`Z` right of the line. -/
theorem re_Wsummand_nonneg (Z : ZeroConfig) {F : ℝ → ℂ}
    (hF : ∀ ρ ∈ Z.carrier, 1 / 2 < ρ.re → paperFT F (gammaOf ρ) = 0) (ρ : Z.carrier) :
    0 ≤ (Z.Wsummand F F ρ).re := by
  obtain ⟨ρ, hρ⟩ := ρ
  simp only [ZeroConfig.Wsummand]
  rcases lt_trichotomy ρ.re (1 / 2) with hlt | heq | hgt
  · have hr := Z.reflect_mem ρ hρ
    have hre : 1 / 2 < (reflect ρ).re := by simp [reflect]; linarith
    have h0 := hF _ hr hre
    rw [gammaOf_reflect] at h0
    simp [h0]
  · have hγ : conj (gammaOf ρ) = gammaOf ρ := by
      rw [Complex.conj_eq_iff_im]
      simp [gammaOf, Complex.div_I, heq]
    rw [hγ, mul_assoc, Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
  · simp [hF ρ hρ hgt]

/-! ### Interpolation of transforms -/

/-- The small bump `φ_δ`: `1` on `[−δ/2, δ/2]`, supported in `(−δ, δ)`. -/
def smallBump (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, by linarith, by linarith⟩

/-- The translated complex test `u ↦ φ_δ(u − t)`. -/
def bumpTest (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : ℝ → ℂ := fun u => ((smallBump δ hδ (u - t) : ℝ) : ℂ)

theorem bumpTest_contDiff {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : ContDiff ℝ 2 (bumpTest δ hδ t) :=
  Complex.ofRealCLM.contDiff.comp ((smallBump δ hδ).contDiff.comp (contDiff_id.sub contDiff_const))

theorem bumpTest_hasCompactSupport {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    HasCompactSupport (bumpTest δ hδ t) :=
  (((smallBump δ hδ).hasCompactSupport.comp_homeomorph (Homeomorph.subRight t))).comp_left
    Complex.ofReal_zero

/-- **Translation**: `h_{φ(· − t)}(z) = e^{izt} h_φ(z)`. -/
theorem paperFT_bumpTest {δ : ℝ} (hδ : 0 < δ) (t : ℝ) (z : ℂ) :
    paperFT (bumpTest δ hδ t) z = cexp (I * z * t) * paperFT (bumpTest δ hδ 0) z := by
  set G : ℝ → ℂ := fun v => ((smallBump δ hδ v : ℝ) : ℂ) * cexp (I * z * v) * cexp (I * z * t)
  have h1 : (fun u => bumpTest δ hδ t u * cexp (I * z * u)) = fun u => G (u - t) := by
    funext u
    simp only [bumpTest, G]
    conv_rhs => rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [paperFT, h1, MeasureTheory.integral_sub_right_eq_self, paperFT]
  simp only [G, bumpTest, sub_zero]
  rw [MeasureTheory.integral_mul_const, mul_comm]

/-- **A short bump has nonvanishing transform**: `h_φ(z) ≠ 0` when `|z| δ ≤ 1/4`. -/
theorem paperFT_bumpTest_zero_ne_zero {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : ‖z‖ * δ ≤ 1 / 4) :
    paperFT (bumpTest δ hδ 0) z ≠ 0 := by
  set φ := smallBump δ hδ
  have hφc : Continuous fun u => ((φ u : ℝ) : ℂ) := Complex.continuous_ofReal.comp φ.continuous
  have hcs : HasCompactSupport fun u => ((φ u : ℝ) : ℂ) := φ.hasCompactSupport.comp_left
    Complex.ofReal_zero
  have hint1 : MeasureTheory.Integrable fun u => ((φ u : ℝ) : ℂ) * cexp (I * z * u) :=
    (hφc.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
  have hint2 : MeasureTheory.Integrable fun u => ((φ u : ℝ) : ℂ) :=
    hφc.integrable_of_hasCompactSupport hcs
  have hpos : 0 < ∫ u, φ u := φ.integral_pos
  -- `‖h_φ(z) − ∫ φ‖ ≤ (1/2) ∫ φ`
  have hdiff : paperFT (bumpTest δ hδ 0) z - ((∫ u, φ u : ℝ) : ℂ)
      = ∫ u, ((φ u : ℝ) : ℂ) * (cexp (I * z * u) - 1) := by
    have e1 : paperFT (bumpTest δ hδ 0) z = ∫ u, ((φ u : ℝ) : ℂ) * cexp (I * z * u) := by
      simp only [paperFT, bumpTest, sub_zero, φ]
    rw [e1, ← integral_complex_ofReal, ← MeasureTheory.integral_sub hint1 hint2]
    congr 1; funext u; ring
  have hbound : ∀ u, ‖((φ u : ℝ) : ℂ) * (cexp (I * z * u) - 1)‖ ≤ φ u / 2 := by
    intro u
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg φ.nonneg]
    by_cases hu : |u| < δ
    · have hw : ‖I * z * u‖ ≤ 1 / 4 := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        nlinarith [norm_nonneg z, abs_nonneg u]
      have := Complex.norm_exp_sub_one_le (le_trans hw (by norm_num))
      nlinarith [φ.nonneg (x := u)]
    · push Not at hu
      rw [φ.zero_of_le_dist (by simpa [φ, smallBump, Real.dist_eq] using hu)]
      simp
  have hnorm : ‖paperFT (bumpTest δ hδ 0) z - ((∫ u, φ u : ℝ) : ℂ)‖ ≤ (∫ u, φ u) / 2 := by
    rw [hdiff]
    refine (MeasureTheory.norm_integral_le_of_norm_le (φ.integrable.div_const 2)
      (Filter.Eventually.of_forall hbound)).trans_eq ?_
    rw [MeasureTheory.integral_div]
  intro h0
  rw [h0, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at hnorm
  linarith

/-- **Interpolation of transforms.** For finitely many distinct points `z_k` and arbitrary values
`b_k` there is a smooth compactly supported test with `h_f(z_k) = b_k`. -/
theorem exists_test_interpolating {n : ℕ} (z : Fin n → ℂ) (hz : Function.Injective z)
    (b : Fin n → ℂ) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ ∀ k, paperFT f (z k) = b k := by
  -- a bump short enough that its transform vanishes at no `z_k`
  set δ : ℝ := 1 / (4 * (1 + ∑ k, ‖z k‖))
  have hS : 0 ≤ ∑ k, ‖z k‖ := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hδ : 0 < δ := by positivity
  have hzδ : ∀ k, ‖z k‖ * δ ≤ 1 / 4 := by
    intro k
    have hk : ‖z k‖ ≤ ∑ k, ‖z k‖ :=
      Finset.single_le_sum (fun k _ => norm_nonneg (z k)) (Finset.mem_univ k)
    simp only [δ]
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set h : Fin n → ℂ := fun k => paperFT (bumpTest δ hδ 0) (z k)
  have hh : ∀ k, h k ≠ 0 := fun k => paperFT_bumpTest_zero_ne_zero hδ (hzδ k)
  -- a step short enough that `e^{i z_k τ}` are distinct
  set D : ℝ := 1 + ∑ k, ∑ l, ‖z k - z l‖
  have hD0 : 0 ≤ ∑ k, ∑ l, ‖z k - z l‖ :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => norm_nonneg _
  set τ : ℝ := 1 / D
  have hτ : 0 < τ := by positivity
  set w : Fin n → ℂ := fun k => cexp (I * z k * τ)
  have hw : Function.Injective w := by
    intro k l hkl
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp hkl
    have hkl' : (z k - z l) * τ = 2 * Real.pi * m := by
      have := congrArg (fun x => x / I) hm
      field_simp at this
      linear_combination this
    have hle : ‖z k - z l‖ ≤ ∑ k, ∑ l, ‖z k - z l‖ :=
      (Finset.single_le_sum (f := fun l => ‖z k - z l‖) (fun l _ => norm_nonneg _)
        (Finset.mem_univ l)).trans (Finset.single_le_sum (f := fun k => ∑ l, ‖z k - z l‖)
          (fun k _ => Finset.sum_nonneg fun l _ => norm_nonneg _) (Finset.mem_univ k))
    have hsmall : ‖(z k - z l) * τ‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
      simp only [τ, D]
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith
    have hm0 : m = 0 := by
      by_contra hm0
      rw [hkl', norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
        Complex.norm_intCast] at hsmall
      have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm0
      have : (2 : ℝ) * Real.pi * 1 ≤ 2 * Real.pi * |(m : ℝ)| := by
        gcongr
      have := Real.pi_gt_three
      norm_num at hsmall
      nlinarith
    rw [hm0] at hkl'
    simp only [Int.cast_zero, mul_zero] at hkl'
    have := mul_eq_zero.mp hkl'
    rcases this with h0 | h0
    · exact hz (sub_eq_zero.mp h0)
    · exact absurd h0 (Complex.ofReal_ne_zero.mpr hτ.ne')
  -- the evaluation matrix `M_{kj} = h_k w_k^j` is invertible
  set M : Matrix (Fin n) (Fin n) ℂ := diagonal h * vandermonde w
  have hdet : IsUnit M.det := by
    rw [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_vandermonde]
    refine (Ne.isUnit (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => hh k) ?_))
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    exact sub_ne_zero.mpr fun he => by
      have := hw he
      simp only [Finset.mem_Ioi] at hj
      exact (ne_of_gt hj) this
  set a : Fin n → ℂ := M⁻¹ *ᵥ b
  refine ⟨∑ j, a j • bumpTest δ hδ ((j : ℕ) * τ),
    contDiff_sum_smul _ (fun j => bumpTest_contDiff hδ _) a,
    hasCompactSupport_sum_smul _ (fun j => bumpTest_hasCompactSupport hδ _) a, fun k => ?_⟩
  rw [paperFT_sum_smul _ (fun j => (bumpTest_contDiff hδ _).continuous)
    (fun j => bumpTest_hasCompactSupport hδ _)]
  have hMa : M *ᵥ a = b := by
    simp only [a, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hentry : ∀ j, a j * paperFT (bumpTest δ hδ ((j : ℕ) * τ)) (z k) = M k j * a j := by
    intro j
    rw [paperFT_bumpTest]
    simp only [M, Matrix.mul_apply, Matrix.diagonal_apply, vandermonde_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, w, h, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl fun j _ => hentry j]
  have := congrFun hMa k
  rwa [Matrix.mulVec, dotProduct] at this

theorem reflect_reflect (ρ : ℂ) : reflect (reflect ρ) = ρ := by
  simp [reflect]

theorem re_reflect (ρ : ℂ) : (reflect ρ).re = 1 - ρ.re := by simp [reflect]

/-- The interpolation target of a zero `ρ` right of the line: `1` at `ρ`, `−1` at `1 − ρ̄`. -/
def pairTarget (ρ τ : ℂ) : ℂ := (if τ = ρ then 1 else 0) - (if τ = reflect ρ then 1 else 0)

/-! ### The finite law -/

section Finite

variable (Z : ZeroConfig) (hfin : Z.carrier.Finite)

/-- The Gram matrix `W_Z(f_i, f_j)` of a finite test family on the zero side. -/
def zeroGram {ι : Type*} (f : ι → ℝ → ℂ) : Matrix ι ι ℂ := fun i j => Z.W (f i) (f j)

/-- The zeros right of the critical line. -/
def rightZeros : Set ℂ := {ρ ∈ Z.carrier | 1 / 2 < ρ.re}

include hfin

theorem rightZeros_finite : (rightZeros Z).Finite := hfin.subset fun _ h => h.1

/-- For a finite configuration the Gram form is Weil's form of the conjugate-weighted combination. -/
theorem hermQuad_zeroGram {ι : Type*} [Fintype ι] (f : ι → ℝ → ℂ) (hf : ∀ i, Continuous (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) (x : ι → ℂ) :
    hermQuad (zeroGram Z f) x = (Z.W (∑ i, conj (x i) • f i) (∑ i, conj (x i) • f i)).re := by
  haveI : Fintype Z.carrier := hfin.fintype
  set m : Z.carrier → ℂ := fun ρ => (Z.mult ρ : ℂ)
  set hh : ι → Z.carrier → ℂ := fun i ρ => paperFT (f i) (gammaOf ρ)
  set hh' : ι → Z.carrier → ℂ := fun j ρ => paperFT (f j) (conj (gammaOf ρ))
  set T : Z.carrier → ι → ι → ℂ := fun ρ i j => conj (x i) * (m ρ * hh i ρ * conj (hh' j ρ) * x j)
  have hG : ∀ i j, zeroGram Z f i j = ∑ ρ, m ρ * hh i ρ * conj (hh' j ρ) := fun i j => by
    simp only [zeroGram, ZeroConfig.W, tsum_fintype, ZeroConfig.Wsummand, m, hh, hh']
  have hR : Z.W (∑ i, conj (x i) • f i) (∑ i, conj (x i) • f i)
      = ∑ ρ, ∑ i, ∑ j, T ρ i j := by
    simp only [ZeroConfig.W, tsum_fintype, ZeroConfig.Wsummand, paperFT_sum_smul f hf hfc]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [map_sum, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [T, m, hh, hh', map_mul, conj_conj]
    ring
  have hL : star x ⬝ᵥ (zeroGram Z f *ᵥ x) = ∑ i, ∑ j, ∑ ρ, T ρ i j := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Complex.star_def, hG, Finset.mul_sum,
      Finset.sum_mul, T]
  rw [hermQuad, hL, hR]
  congr 1
  calc ∑ i, ∑ j, ∑ ρ, T ρ i j = ∑ i, ∑ ρ, ∑ j, T ρ i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ ρ, ∑ i, ∑ j, T ρ i j := Finset.sum_comm

/-- **Upper bound.** On every finite family of continuous compactly supported tests the Weil form
of a finite configuration has at most `#{Re ρ > ½}` negative squares. -/
theorem negIndex_zeroGram_le {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ → ℂ)
    (hf : ∀ i, Continuous (f i)) (hfc : ∀ i, HasCompactSupport (f i)) :
    hermNegIndex (zeroGram Z f) ≤ (rightZeros_finite Z hfin).toFinset.card := by
  haveI : Fintype (rightZeros Z) := (rightZeros_finite Z hfin).fintype
  rw [Set.Finite.card_toFinset]
  refine negIndex_le_card_of_nonneg_on_ker _ (fun ρ : rightZeros Z => evalFunctional f (gammaOf ρ))
    fun x hx => ?_
  haveI : Fintype Z.carrier := hfin.fintype
  rw [hermQuad_zeroGram Z hfin f hf hfc, ZeroConfig.W, tsum_fintype, Complex.re_sum]
  refine Finset.sum_nonneg fun ρ _ => re_Wsummand_nonneg Z (fun σ hσ hre => ?_) ρ
  have := hx ⟨σ, hσ, hre⟩
  rw [evalFunctional_eq f hf hfc] at this
  simpa using this

/-- On a finite configuration Weil's form is a finite sum over the carrier. -/
theorem W_eq_sum (f g : ℝ → ℂ) :
    Z.W f g = ∑ τ ∈ hfin.toFinset, (Z.mult τ : ℂ) * paperFT f (gammaOf τ) *
      conj (paperFT g (conj (gammaOf τ))) := by
  haveI : Fintype Z.carrier := hfin.fintype
  rw [ZeroConfig.W, tsum_fintype]
  exact (Finset.sum_subtype hfin.toFinset (fun x => Set.Finite.mem_toFinset hfin)
    (fun τ => (Z.mult τ : ℂ) * paperFT f (gammaOf τ) * conj (paperFT g (conj (gammaOf τ))))).symm

/-- **Attainment.** A finite configuration admits a family of smooth compactly supported tests,
one per zero right of the line, whose Weil Gram matrix is `diag(−2 m_ρ)`: the Weil form has exactly
`#{Re ρ > ½}` negative squares on it. -/
theorem exists_zeroGram_negIndex_eq :
    ∃ f : (rightZeros_finite Z hfin).toFinset → ℝ → ℂ, (∀ ρ, ContDiff ℝ 2 (f ρ)) ∧
      (∀ ρ, HasCompactSupport (f ρ)) ∧
        hermNegIndex (zeroGram Z f) = (rightZeros_finite Z hfin).toFinset.card := by
  classical
  set C := hfin.toFinset
  set R := (rightZeros_finite Z hfin).toFinset
  set e := C.equivFin
  set z : Fin C.card → ℂ := fun k => gammaOf (e.symm k : ℂ)
  have hz : Function.Injective z := fun k l h =>
    e.symm.injective (Subtype.ext (gammaOf_injective h))
  have hex := fun ρ : R => exists_test_interpolating z hz (fun k => pairTarget ρ (e.symm k : ℂ))
  choose f hf hfc hfv using hex
  have hval : ∀ (ρ : R) τ, τ ∈ Z.carrier → paperFT (f ρ) (gammaOf τ) = pairTarget ρ τ := by
    intro ρ τ hτ
    have hτC : τ ∈ C := (Set.Finite.mem_toFinset hfin).mpr hτ
    have := hfv ρ (e ⟨τ, hτC⟩)
    simpa [z] using this
  have hR : ∀ ρ : R, (ρ : ℂ) ∈ Z.carrier ∧ 1 / 2 < (ρ : ℂ).re := fun ρ => by
    have := (Set.Finite.mem_toFinset (rightZeros_finite Z hfin)).mp ρ.2
    simpa [rightZeros] using this
  -- the Gram matrix is diagonal with entries `−2 m_ρ`
  have hgram : zeroGram Z f = diagonal fun ρ : R => ((-2 * (Z.mult ρ : ℝ) : ℝ) : ℂ) := by
    refine Matrix.ext fun ρ σ => ?_
    rw [Matrix.diagonal_apply]
    show Z.W (f ρ) (f σ) = _
    obtain ⟨hρC, hρre⟩ := hR ρ
    obtain ⟨hσC, hσre⟩ := hR σ
    have hρr : reflect (ρ : ℂ) ≠ ρ := fun h => by
      have := congrArg Complex.re h; rw [re_reflect] at this; linarith
    have hrefC : reflect (ρ : ℂ) ∈ Z.carrier := Z.reflect_mem _ hρC
    rw [W_eq_sum Z hfin]
    -- evaluate both transforms on the carrier
    have hsum : ∀ τ ∈ C, (Z.mult τ : ℂ) * paperFT (f ρ) (gammaOf τ) *
        conj (paperFT (f σ) (conj (gammaOf τ)))
          = (Z.mult τ : ℂ) * pairTarget ρ τ * conj (pairTarget σ (reflect τ)) := by
      intro τ hτ
      have hτ' : τ ∈ Z.carrier := (Set.Finite.mem_toFinset hfin).mp hτ
      rw [hval ρ τ hτ', ← gammaOf_reflect, hval σ _ (Z.reflect_mem τ hτ')]
    rw [Finset.sum_congr rfl hsum]
    -- only `τ = ρ` and `τ = reflect (ρ : ℂ)` contribute
    have hsub : ({(ρ : ℂ), reflect (ρ : ℂ)} : Finset ℂ) ⊆ C := by
      intro τ hτ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hτ
      rcases hτ with rfl | rfl <;> exact (Set.Finite.mem_toFinset hfin).mpr ‹_›
    have hzero : ∀ τ ∈ C, τ ∉ ({(ρ : ℂ), reflect (ρ : ℂ)} : Finset ℂ) →
        (Z.mult τ : ℂ) * pairTarget ρ τ * conj (pairTarget σ (reflect τ)) = 0 := by
      intro τ _ hτ
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hτ
      simp [pairTarget, hτ.1, hτ.2]
    rw [← Finset.sum_subset hsub hzero, Finset.sum_pair (Ne.symm hρr)]
    have hm : Z.mult (reflect (ρ : ℂ)) = Z.mult ρ := Z.mult_reflect _ hρC
    have h1 : reflect (ρ : ℂ) ≠ σ := fun h => by
      have := congrArg Complex.re h; rw [re_reflect] at this; linarith
    have h2 : (ρ : ℂ) ≠ reflect σ := fun h => by
      have := congrArg Complex.re h; rw [re_reflect] at this; linarith
    have hρρ : pairTarget ρ ρ = 1 := by simp [pairTarget, Ne.symm hρr]
    have hρref : pairTarget ρ (reflect (ρ : ℂ)) = -1 := by simp [pairTarget, hρr]
    rw [hρρ, hρref, reflect_reflect]
    by_cases hρσ : ρ = σ
    · subst hρσ
      simp only [hρref, hρρ, map_neg, map_one, hm]
      push_cast; ring
    · have hne : (ρ : ℂ) ≠ σ := fun h => hρσ (Subtype.ext h)
      have hneref : reflect (ρ : ℂ) ≠ reflect σ := fun h => hne (by
        rw [← reflect_reflect (ρ : ℂ), ← reflect_reflect (σ : ℂ)]; exact congrArg reflect h)
      have e1 : pairTarget σ (reflect (ρ : ℂ)) = 0 := by simp [pairTarget, h1, hneref]
      have e2 : pairTarget σ ρ = 0 := by simp [pairTarget, hne, h2]
      rw [e1, e2, if_neg hρσ]
      simp
  refine ⟨f, hf, hfc, ?_⟩
  rw [hgram, negIndex_diagonal]
  have : ({ρ | -2 * (Z.mult ρ : ℝ) < 0} : Finset R) = Finset.univ := by
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    have := Z.one_le_mult _ (hR ρ).1
    have : (1 : ℝ) ≤ Z.mult ρ := by exact_mod_cast this
    linarith
  rw [this, Finset.card_univ, Fintype.card_coe]

/-- **The exact Pontryagin law of a finite configuration.** The largest number of negative squares
of the Weil form of a finite zero configuration on a finite family of tests is the number of its
zeros right of the critical line. -/
theorem pontryagin_law_finite :
    (∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, Continuous (f i)) → (∀ i, HasCompactSupport (f i)) →
      hermNegIndex (zeroGram Z f) ≤ (rightZeros_finite Z hfin).toFinset.card) ∧
    ∃ f : (rightZeros_finite Z hfin).toFinset → ℝ → ℂ, (∀ ρ, ContDiff ℝ 2 (f ρ)) ∧
      (∀ ρ, HasCompactSupport (f ρ)) ∧
        hermNegIndex (zeroGram Z f) = (rightZeros_finite Z hfin).toFinset.card :=
  ⟨fun _ f hf hfc => negIndex_zeroGram_le Z hfin f hf hfc, exists_zeroGram_negIndex_eq Z hfin⟩

end Finite

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
