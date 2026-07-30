import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardHardyContraction
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Non-diagonal Hardy nonexpansiveness of the Xi Ward transport

The Schwarz-paired Xi phase is not only pointwise contractive.  On every finite packet in the
right half-plane, its Pick defect is positive semidefinite.  The proof starts from an exact
rank-one-plus-Cauchy factorization for one Cayley divisor factor, closes positivity under finite
products, and passes to the unconditional Xi product by entrywise matrix convergence.

The actual source transport is `V = 1 - phase`.  Affine Schur closure then proves that `V / 2`
is a contractive Hardy multiplier.  Equivalently, its unnormalized multiplier satisfies the
four-unit nonexpansiveness law

`4 G - diag(V) G diag(V)ᴴ ⪰ 0`

for every finite right-half-plane packet and every nonnegative real aperture.  No RH hypothesis,
zero-location hypothesis, finite truncation hypothesis, or unproved analytic input occurs.
-/

open Complex Set Matrix MeasureTheory Filter
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Hardy Cauchy Gram sampled on a finite right-half-plane packet. -/
def rightHalfPlaneHardyCauchyGram {n : ℕ} (w : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => 1 / (w i + star (w j))

theorem rightHalfPlaneHardyCauchyGram_hermitian {n : ℕ} (w : Fin n → ℂ) :
    (rightHalfPlaneHardyCauchyGram w).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, rightHalfPlaneHardyCauchyGram, add_comm]

theorem integral_cauchyFeaturePair
    {a : ℂ} (ha : 0 < a.re) :
    ∫ t : ℝ in Set.Ioi 0, Complex.exp (-a * (t : ℂ)) = 1 / a := by
  rw [integral_exp_mul_complex_Ioi (a := -a) (by simpa using ha) 0]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, neg_div]
  ring

def rightHalfPlaneCauchyPacketFeature {n : ℕ}
    (w : Fin n → ℂ) (x : Fin n → ℂ) (t : ℝ) : ℂ :=
  ∑ j, Complex.exp (-(star (w j)) * (t : ℂ)) * x j

def rightHalfPlaneCauchyQuadraticIntegrand {n : ℕ}
    (w : Fin n → ℂ) (x : Fin n → ℂ) (t : ℝ) : ℂ :=
  ∑ i, ∑ j,
    star (x i) *
      Complex.exp (-(w i + star (w j)) * (t : ℂ)) *
        x j

theorem rightHalfPlaneCauchyQuadraticIntegrand_eq_normSq
    {n : ℕ} (w : Fin n → ℂ) (x : Fin n → ℂ) (t : ℝ) :
    rightHalfPlaneCauchyQuadraticIntegrand w x t =
      (Complex.normSq (rightHalfPlaneCauchyPacketFeature w x t) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [rightHalfPlaneCauchyPacketFeature, rightHalfPlaneCauchyQuadraticIntegrand,
    map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_mul, RCLike.star_def]
  rw [← Complex.exp_conj]
  have hexp :
      Complex.exp
          (star (-(star (w j)) * (t : ℂ))) *
        Complex.exp (-(star (w i)) * (t : ℂ)) =
      Complex.exp
        (-(w j + star (w i)) * (t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    simp
    ring
  calc
    star (x j) *
          Complex.exp (-(w j + star (w i)) * (t : ℂ)) *
        x i =
      star (x j) *
          (Complex.exp (star (-(star (w j)) * (t : ℂ))) *
            Complex.exp (-(star (w i)) * (t : ℂ))) *
        x i := by rw [hexp]
    _ = Complex.exp (star (-(star (w j)) * (t : ℂ))) *
          star (x j) *
            (Complex.exp (-(star (w i)) * (t : ℂ)) * x i) := by
      ring

theorem integrableOn_rightHalfPlaneCauchyQuadraticTerm
    {n : ℕ} {w : Fin n → ℂ} (hw : ∀ i, 0 < (w i).re)
    (x : Fin n → ℂ) (i j : Fin n) :
    IntegrableOn
      (fun t : ℝ =>
        star (x i) *
          Complex.exp (-(w i + star (w j)) * (t : ℂ)) *
            x j)
      (Set.Ioi 0) := by
  have hrate : (-(w i + star (w j))).re < 0 := by
    simp only [neg_re, add_re, RCLike.star_def, Complex.conj_re]
    linarith [hw i, hw j]
  exact ((integrableOn_exp_mul_complex_Ioi hrate 0).const_mul
    (star (x i))).mul_const (x j)

theorem integrableOn_rightHalfPlaneCauchyQuadraticIntegrand
    {n : ℕ} {w : Fin n → ℂ} (hw : ∀ i, 0 < (w i).re)
    (x : Fin n → ℂ) :
    IntegrableOn (rightHalfPlaneCauchyQuadraticIntegrand w x) (Set.Ioi 0) := by
  unfold rightHalfPlaneCauchyQuadraticIntegrand
  apply integrable_finsetSum Finset.univ
  intro i hi
  apply integrable_finsetSum Finset.univ
  intro j hj
  exact integrableOn_rightHalfPlaneCauchyQuadraticTerm hw x i j

theorem integral_rightHalfPlaneCauchyQuadraticIntegrand_eq
    {n : ℕ} {w : Fin n → ℂ} (hw : ∀ i, 0 < (w i).re)
    (x : Fin n → ℂ) :
    (∫ t : ℝ in Set.Ioi 0, rightHalfPlaneCauchyQuadraticIntegrand w x t) =
      star x ⬝ᵥ (rightHalfPlaneHardyCauchyGram w *ᵥ x) := by
  have hterm (i j : Fin n) :
      IntegrableOn
        (fun t : ℝ =>
          star (x i) *
            Complex.exp (-(w i + star (w j)) * (t : ℂ)) *
              x j)
        (Set.Ioi 0) :=
    integrableOn_rightHalfPlaneCauchyQuadraticTerm hw x i j
  have hrow (i : Fin n) :
      IntegrableOn
        (fun t : ℝ => ∑ j,
          star (x i) *
            Complex.exp (-(w i + star (w j)) * (t : ℂ)) *
              x j)
        (Set.Ioi 0) :=
    integrable_finsetSum Finset.univ (fun j _ => hterm i j)
  simp only [rightHalfPlaneCauchyQuadraticIntegrand, dotProduct, mulVec,
    rightHalfPlaneHardyCauchyGram, div_eq_mul_inv, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => hrow i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum Finset.univ (fun j _ => hterm i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_mul_const, integral_const_mul,
    integral_cauchyFeaturePair (by
      simp only [add_re, RCLike.star_def, Complex.conj_re]
      linarith [hw i, hw j])]
  simp only [Pi.star_apply, one_mul, div_eq_mul_inv]
  ring

/-- The right-half-plane Hardy Cauchy kernel is positive semidefinite on every finite packet. -/
theorem rightHalfPlaneHardyCauchyGram_posSemidef
    {n : ℕ} {w : Fin n → ℂ} (hw : ∀ i, 0 < (w i).re) :
    (rightHalfPlaneHardyCauchyGram w).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (rightHalfPlaneHardyCauchyGram_hermitian w)
  intro x
  rw [← integral_rightHalfPlaneCauchyQuadraticIntegrand_eq hw x]
  have hfun :
      rightHalfPlaneCauchyQuadraticIntegrand w x =
        fun t : ℝ =>
          (Complex.normSq (rightHalfPlaneCauchyPacketFeature w x t) : ℂ) := by
    funext t
    exact rightHalfPlaneCauchyQuadraticIntegrand_eq_normSq w x t
  rw [hfun, integral_complex_ofReal]
  rw [Complex.nonneg_iff]
  constructor
  · simp only [ofReal_re]
    exact integral_nonneg
      (fun t => Complex.normSq_nonneg
        (rightHalfPlaneCauchyPacketFeature w x t))
  · simp only [ofReal_im]

def xiWardCayleyPickDefect {n : ℕ}
    (w : Fin n → ℂ) (lam : ℂ) (alpha : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    (1 -
      xiWardHalfPlaneCayleyFactor lam (w i) alpha *
        star (xiWardHalfPlaneCayleyFactor lam (w j) alpha)) /
      (w i + star (w j))

def xiWardCayleyResolventColumn {n : ℕ}
    (w : Fin n → ℂ) (lam : ℂ) (alpha : ℝ) :
    Matrix (Fin n) Unit ℂ :=
  fun i _ => (w i + lam + (alpha : ℂ))⁻¹

def xiWardCayleyResolventDiagonal {n : ℕ}
    (w : Fin n → ℂ) (lam : ℂ) (alpha : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal
    (fun i => (w i + lam + (alpha : ℂ))⁻¹)

theorem xiWardCayleyResolventColumn_gram_apply
    {n : ℕ} (w : Fin n → ℂ) (lam : ℂ) (alpha : ℝ)
    (i j : Fin n) :
    (xiWardCayleyResolventColumn w lam alpha *
        (xiWardCayleyResolventColumn w lam alpha)ᴴ) i j =
      (w i + lam + (alpha : ℂ))⁻¹ *
        star ((w j + lam + (alpha : ℂ))⁻¹) := by
  simp [xiWardCayleyResolventColumn, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

theorem xiWardCayleyResolventDiagonal_cauchy_apply
    {n : ℕ} (w : Fin n → ℂ) (lam : ℂ) (alpha : ℝ)
    (i j : Fin n) :
    (xiWardCayleyResolventDiagonal w lam alpha *
        rightHalfPlaneHardyCauchyGram w *
          (xiWardCayleyResolventDiagonal w lam alpha)ᴴ) i j =
      (w i + lam + (alpha : ℂ))⁻¹ *
        (1 / (w i + star (w j))) *
          star ((w j + lam + (alpha : ℂ))⁻¹) := by
  have hstar :
      (xiWardCayleyResolventDiagonal w lam alpha)ᴴ =
        Matrix.diagonal
          (fun j => star ((w j + lam + (alpha : ℂ))⁻¹)) := by
    ext k l
    by_cases hkl : k = l
    · subst l
      simp [xiWardCayleyResolventDiagonal, Matrix.conjTranspose_apply]
    · have hlk : l ≠ k := Ne.symm hkl
      simp [xiWardCayleyResolventDiagonal, Matrix.conjTranspose_apply,
        hkl, hlk]
  rw [hstar, Matrix.mul_diagonal]
  rw [show
    (xiWardCayleyResolventDiagonal w lam alpha * rightHalfPlaneHardyCauchyGram w) i j =
      (w i + lam + (alpha : ℂ))⁻¹ * rightHalfPlaneHardyCauchyGram w i j by
        rw [xiWardCayleyResolventDiagonal, Matrix.diagonal_mul]]
  rfl

theorem xiWardCayleyPick_scalar_factorization
    {wi wj lam : ℂ} {alpha : ℝ}
    (hwi : wi + lam + (alpha : ℂ) ≠ 0)
    (hwj : wj + star lam + (alpha : ℂ) ≠ 0)
    (hwij : wi + wj ≠ 0) :
    (1 -
        ((wi + lam - (alpha : ℂ)) /
          (wi + lam + (alpha : ℂ))) *
        ((wj + star lam - (alpha : ℂ)) /
          (wj + star lam + (alpha : ℂ)))) /
        (wi + wj) =
      ((2 * alpha : ℝ) : ℂ) *
          (wi + lam + (alpha : ℂ))⁻¹ *
            star ((star wj + lam + (alpha : ℂ))⁻¹) +
        ((4 * alpha * lam.re : ℝ) : ℂ) *
          (wi + lam + (alpha : ℂ))⁻¹ *
            (1 / (wi + wj)) *
              star ((star wj + lam + (alpha : ℂ))⁻¹) := by
  have hstarInv :
      star ((star wj + lam + (alpha : ℂ))⁻¹) =
        (wj + star lam + (alpha : ℂ))⁻¹ := by
    simp
  rw [hstarInv]
  have hreal :
      (lam.re : ℂ) = (lam + star lam) / 2 := by
    apply Complex.ext <;> simp
  field_simp [hwi, hwj, hwij]
  push_cast
  rw [hreal]
  ring

/-- Exact non-diagonal Pick factorization for one Xi Cayley divisor factor. -/
theorem xiWardCayleyPickDefect_factorization
    {n : ℕ} {w : Fin n → ℂ} {lam : ℂ} {alpha : ℝ}
    (hw : ∀ i, 0 < (w i).re) (hlam : 0 < lam.re)
    (ha : 0 ≤ alpha) :
    xiWardCayleyPickDefect w lam alpha =
      (2 * alpha : ℝ) •
        (xiWardCayleyResolventColumn w lam alpha *
          (xiWardCayleyResolventColumn w lam alpha)ᴴ) +
      (4 * alpha * lam.re : ℝ) •
        (xiWardCayleyResolventDiagonal w lam alpha *
          rightHalfPlaneHardyCauchyGram w *
            (xiWardCayleyResolventDiagonal w lam alpha)ᴴ) := by
  ext i j
  have hwi : w i + lam + (alpha : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [add_re, ofReal_re, zero_re] at hre
    linarith [hw i]
  have hwj :
      star (w j + lam + (alpha : ℂ)) ≠ 0 :=
    map_ne_zero (starRingEnd ℂ) |>.mpr (by
      intro h
      have hre := congrArg Complex.re h
      simp only [add_re, ofReal_re, zero_re] at hre
      linarith [hw j])
  have hwij : w i + star (w j) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [add_re, RCLike.star_def, Complex.conj_re, zero_re] at hre
    linarith [hw i, hw j]
  have hwj' :
      star (w j) + star lam + (alpha : ℂ) ≠ 0 := by
    simpa only [map_add, RCLike.star_def, Complex.conj_ofReal] using hwj
  have hwj'' :
      (alpha : ℂ) + star (w j) + star lam ≠ 0 := by
    simpa only [add_comm, add_left_comm, add_assoc] using hwj'
  have hstarFactor :
      star (xiWardHalfPlaneCayleyFactor lam (w j) alpha) =
        (star (w j) + star lam - (alpha : ℂ)) /
          (star (w j) + star lam + (alpha : ℂ)) := by
    change
      (starRingEnd ℂ) ((w j + lam - (alpha : ℂ)) /
        (w j + lam + (alpha : ℂ))) = _
    rw [map_div₀]
    simp only [map_sub, map_add, RCLike.star_def,
      Complex.conj_ofReal]
  change
    (1 -
        xiWardHalfPlaneCayleyFactor lam (w i) alpha *
          star (xiWardHalfPlaneCayleyFactor lam (w j) alpha)) /
        (w i + star (w j)) =
      ((2 * alpha : ℝ) : ℂ) *
          (xiWardCayleyResolventColumn w lam alpha *
            (xiWardCayleyResolventColumn w lam alpha)ᴴ) i j +
        ((4 * alpha * lam.re : ℝ) : ℂ) *
          (xiWardCayleyResolventDiagonal w lam alpha *
            rightHalfPlaneHardyCauchyGram w *
              (xiWardCayleyResolventDiagonal w lam alpha)ᴴ) i j
  rw [xiWardCayleyResolventColumn_gram_apply,
    xiWardCayleyResolventDiagonal_cauchy_apply]
  rw [hstarFactor]
  simpa [xiWardHalfPlaneCayleyFactor, mul_assoc] using
    (xiWardCayleyPick_scalar_factorization hwi hwj' hwij)

theorem xiWardCayleyPickDefect_posSemidef
    {n : ℕ} {w : Fin n → ℂ} {lam : ℂ} {alpha : ℝ}
    (hw : ∀ i, 0 < (w i).re) (hlam : 0 < lam.re)
    (ha : 0 ≤ alpha) :
    (xiWardCayleyPickDefect w lam alpha).PosSemidef := by
  rw [xiWardCayleyPickDefect_factorization hw hlam ha]
  apply Matrix.PosSemidef.add
  · apply Matrix.PosSemidef.smul
      (Matrix.posSemidef_self_mul_conjTranspose
        (xiWardCayleyResolventColumn w lam alpha))
    linarith
  · apply Matrix.PosSemidef.smul
      ((rightHalfPlaneHardyCauchyGram_posSemidef hw).mul_mul_conjTranspose_same
        (xiWardCayleyResolventDiagonal w lam alpha))
    positivity

def rightHalfPlanePickDefect {n : ℕ}
    (w : Fin n → ℂ) (f : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (1 - f i * star (f j)) / (w i + star (w j))

def pickValueDiagonal {n : ℕ} (f : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal f

theorem pickValueDiagonal_congruence_apply
    {n : ℕ} (f : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) :
    (pickValueDiagonal f * M * (pickValueDiagonal f)ᴴ) i j =
      f i * M i j * star (f j) := by
  have hstar :
      (pickValueDiagonal f)ᴴ =
        Matrix.diagonal (fun j => star (f j)) := by
    ext k l
    by_cases hkl : k = l
    · subst l
      simp [pickValueDiagonal, Matrix.conjTranspose_apply]
    · have hlk : l ≠ k := Ne.symm hkl
      simp [pickValueDiagonal, Matrix.conjTranspose_apply, hkl, hlk]
  rw [hstar, Matrix.mul_diagonal]
  rw [show (pickValueDiagonal f * M) i j = f i * M i j by
    rw [pickValueDiagonal, Matrix.diagonal_mul]]

/-- Product law for Pick defects; second summand is a diagonal congruence. -/
theorem rightHalfPlanePickDefect_mul
    {n : ℕ} (w : Fin n → ℂ) (f g : Fin n → ℂ) :
    rightHalfPlanePickDefect w (f * g) =
      rightHalfPlanePickDefect w f +
        pickValueDiagonal f *
          rightHalfPlanePickDefect w g *
            (pickValueDiagonal f)ᴴ := by
  ext i j
  simp only [Matrix.add_apply]
  rw [pickValueDiagonal_congruence_apply]
  simp only [rightHalfPlanePickDefect, Pi.mul_apply,
    star_mul]
  simp only [div_eq_mul_inv]
  ring

theorem rightHalfPlanePickDefect_mul_posSemidef
    {n : ℕ} {w : Fin n → ℂ} {f g : Fin n → ℂ}
    (hf : (rightHalfPlanePickDefect w f).PosSemidef)
    (hg : (rightHalfPlanePickDefect w g).PosSemidef) :
    (rightHalfPlanePickDefect w (f * g)).PosSemidef := by
  rw [rightHalfPlanePickDefect_mul]
  exact hf.add
    (hg.mul_mul_conjTranspose_same (pickValueDiagonal f))

theorem rightHalfPlanePickDefect_one_posSemidef
    {n : ℕ} (w : Fin n → ℂ) :
    (rightHalfPlanePickDefect w 1).PosSemidef := by
  have hzero :
      rightHalfPlanePickDefect w 1 =
        (0 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    simp [rightHalfPlanePickDefect]
  rw [hzero]
  exact Matrix.PosSemidef.zero

theorem rightHalfPlanePickDefect_finsetProd_posSemidef
    {n : ℕ} {κ : Type*} [DecidableEq κ]
    (w : Fin n → ℂ) (S : Finset κ) (f : κ → Fin n → ℂ)
    (hf : ∀ q ∈ S,
      (rightHalfPlanePickDefect w (f q)).PosSemidef) :
    (rightHalfPlanePickDefect w
      (fun i => ∏ q ∈ S, f q i)).PosSemidef := by
  induction S using Finset.induction_on with
  | empty =>
      simpa using! rightHalfPlanePickDefect_one_posSemidef w
  | @insert q S hq ih =>
      have hqpsd :
          (rightHalfPlanePickDefect w (f q)).PosSemidef :=
        hf q (Finset.mem_insert_self q S)
      have hSpsd :
          (rightHalfPlanePickDefect w
            (fun i => ∏ k ∈ S, f k i)).PosSemidef :=
        ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
      have hfun :
          (fun i => ∏ k ∈ insert q S, f k i) =
            f q * (fun i => ∏ k ∈ S, f k i) := by
        funext i
        simp only [Pi.mul_apply, Finset.prod_insert hq]
      rw [hfun]
      exact rightHalfPlanePickDefect_mul_posSemidef hqpsd hSpsd

theorem rightHalfPlanePickDefect_cayley_posSemidef
    {n : ℕ} {w : Fin n → ℂ} {lam : ℂ} {alpha : ℝ}
    (hw : ∀ i, 0 < (w i).re) (hlam : 0 < lam.re)
    (ha : 0 ≤ alpha) :
    (rightHalfPlanePickDefect w
      (fun i => xiWardHalfPlaneCayleyFactor lam (w i) alpha)).PosSemidef := by
  simpa only [rightHalfPlanePickDefect, xiWardCayleyPickDefect] using!
    (xiWardCayleyPickDefect_posSemidef hw hlam ha)

theorem Matrix.PosSemidef.of_tendsto_complex
    {α n : Type*} [Fintype n] {l : Filter α} [l.NeBot]
    {A : α → Matrix n n ℂ} {M : Matrix n n ℂ}
    (hA : ∀ᶠ a in l, (A a).PosSemidef)
    (hlim : Tendsto A l (nhds M)) :
    M.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.IsHermitian]
    have hc : Continuous
        (fun N : Matrix n n ℂ => N.conjTranspose) := by
      fun_prop
    have hleft :
        Tendsto (fun a => (A a).conjTranspose) l
          (nhds M.conjTranspose) :=
      hc.continuousAt.tendsto.comp hlim
    have hright :
        Tendsto (fun a => (A a).conjTranspose) l (nhds M) := by
      apply hlim.congr'
      filter_upwards [hA] with a ha
      exact ha.isHermitian.eq.symm
    exact tendsto_nhds_unique hleft hright
  · intro x
    have hc : Continuous (fun N : Matrix n n ℂ =>
        dotProduct (star x) (N.mulVec x)) := by
      fun_prop
    have hq := hc.continuousAt.tendsto.comp hlim
    apply isClosed_Ici.mem_of_tendsto hq
    filter_upwards [hA] with a ha
    exact (Matrix.posSemidef_iff_dotProduct_mulVec.mp ha).2 x

theorem tendsto_rightHalfPlanePickDefect
    {n : ℕ} {α : Type*} {l : Filter α}
    (w : Fin n → ℂ) (f : α → Fin n → ℂ) (g : Fin n → ℂ)
    (hf : ∀ i, Tendsto (fun a => f a i) l (nhds (g i))) :
    Tendsto (fun a => rightHalfPlanePickDefect w (f a)) l
      (nhds (rightHalfPlanePickDefect w g)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hij :
      Tendsto (fun a => (f a i, f a j)) l
        (nhds (g i, g j)) :=
    (hf i).prodMk_nhds (hf j)
  let entry : ℂ × ℂ → ℂ :=
    fun p => (1 - p.1 * star p.2) / (w i + star (w j))
  have hentry : Continuous entry := by
    dsimp [entry]
    fun_prop
  simpa only [rightHalfPlanePickDefect, entry] using!
    hentry.continuousAt.tendsto.comp hij

theorem rightHalfPlanePickDefect_schwarzPair_posSemidef
    {n : ℕ} {w : Fin n → ℂ}
    (hw : ∀ i, 0 < (w i).re) (q : XiRightUpperZeroCopy)
    {alpha : ℝ} (ha : 0 ≤ alpha) :
    (rightHalfPlanePickDefect w
      (fun i => xiWardSchwarzPairCayleyFactor q (w i) alpha)).PosSemidef := by
  have hupper :
      (rightHalfPlanePickDefect w
        (fun i => xiWardCayleyFactor q.1 (w i) alpha)).PosSemidef := by
    simpa only [xiWardCayleyFactor] using!
      (rightHalfPlanePickDefect_cayley_posSemidef
        hw q.1.2 ha)
  have hlower :
      (rightHalfPlanePickDefect w
        (fun i => xiWardCayleyFactor
          (xiRightZeroCopyConjEquiv q.1) (w i) alpha)).PosSemidef := by
    simpa only [xiWardCayleyFactor] using!
      (rightHalfPlanePickDefect_cayley_posSemidef
        hw (xiRightZeroCopyConjEquiv q.1).2 ha)
  simpa only [xiWardSchwarzPairCayleyFactor, Pi.mul_apply] using!
    rightHalfPlanePickDefect_mul_posSemidef hupper hlower

theorem rightHalfPlanePickDefect_finiteXiProduct_posSemidef
    {n : ℕ} {w : Fin n → ℂ}
    (hw : ∀ i, 0 < (w i).re)
    (S : Finset XiRightUpperZeroCopy)
    {alpha : ℝ} (ha : 0 ≤ alpha) :
    (rightHalfPlanePickDefect w
      (fun i => ∏ q ∈ S,
        xiWardSchwarzPairCayleyFactor q (w i) alpha)).PosSemidef := by
  apply rightHalfPlanePickDefect_finsetProd_posSemidef
  intro q hq
  exact rightHalfPlanePickDefect_schwarzPair_posSemidef hw q ha

/-- Infinite Schwarz-paired Xi phase is a contractive Hardy multiplier. -/
theorem xiWardPhasePickDefect_posSemidef
    {n : ℕ} {w : Fin n → ℂ}
    (hw : ∀ i, 0 < (w i).re)
    {alpha : ℝ} (ha : 0 ≤ alpha) :
    (rightHalfPlanePickDefect w
      (fun i => xiRightWardBoundarySourcePhaseCrossRatio
        (I * w i) (alpha : ℂ))).PosSemidef := by
  apply Matrix.PosSemidef.of_tendsto_complex
    (l := (SummationFilter.unconditional
      XiRightUpperZeroCopy).filter)
    (A := fun S : Finset XiRightUpperZeroCopy =>
      rightHalfPlanePickDefect w
        (fun i => ∏ q ∈ S,
          xiWardSchwarzPairCayleyFactor q (w i) alpha))
  · exact Filter.Eventually.of_forall fun S =>
      rightHalfPlanePickDefect_finiteXiProduct_posSemidef
        hw S ha
  · apply tendsto_rightHalfPlanePickDefect
    intro i
    have hprod :=
      xiRightWardBoundarySourcePhaseCrossRatio_hasProd_cayley
        (hw i) ha
    rw [HasProd] at hprod
    exact hprod

theorem rightHalfPlanePickDefect_oneSubHalf
    {n : ℕ} (w : Fin n → ℂ) (f : Fin n → ℂ) :
    rightHalfPlanePickDefect w
        (fun i => (1 - f i) / 2) =
      (1 / 2 : ℝ) • rightHalfPlanePickDefect w f +
        (1 / 4 : ℝ) •
          (pickValueDiagonal (1 + f) *
            rightHalfPlaneHardyCauchyGram w *
              (pickValueDiagonal (1 + f))ᴴ) := by
  ext i j
  let H : Matrix (Fin n) (Fin n) ℂ :=
    pickValueDiagonal (1 + f) *
      rightHalfPlaneHardyCauchyGram w *
        (pickValueDiagonal (1 + f))ᴴ
  change
    rightHalfPlanePickDefect w
        (fun i => (1 - f i) / 2) i j =
      (((1 / 2 : ℝ) : ℂ) *
          rightHalfPlanePickDefect w f i j) +
        (((1 / 4 : ℝ) : ℂ) * H i j)
  have hH :
      H i j =
        (1 + f) i * rightHalfPlaneHardyCauchyGram w i j * star ((1 + f) j) := by
    exact pickValueDiagonal_congruence_apply (1 + f)
      (rightHalfPlaneHardyCauchyGram w) i j
  rw [hH]
  simp only [rightHalfPlanePickDefect, rightHalfPlaneHardyCauchyGram,
    Pi.one_apply, Pi.add_apply]
  have hstarHalf :
      star ((1 - f j) / (2 : ℂ)) =
        (1 - star (f j)) / 2 := by
    change (starRingEnd ℂ) ((1 - f j) / (2 : ℂ)) = _
    rw [map_div₀, map_sub]
    simp only [map_one, map_ofNat, starRingEnd_apply]
  have hstarAdd :
      star (1 + f j) = 1 + star (f j) := by
    simp
  rw [hstarHalf, hstarAdd]
  push_cast
  simp only [div_eq_mul_inv]
  ring

theorem rightHalfPlanePickDefect_oneSubHalf_posSemidef
    {n : ℕ} {w : Fin n → ℂ} {f : Fin n → ℂ}
    (hw : ∀ i, 0 < (w i).re)
    (hf : (rightHalfPlanePickDefect w f).PosSemidef) :
    (rightHalfPlanePickDefect w
      (fun i => (1 - f i) / 2)).PosSemidef := by
  rw [rightHalfPlanePickDefect_oneSubHalf]
  apply Matrix.PosSemidef.add
  · exact hf.smul (by norm_num)
  · exact ((rightHalfPlaneHardyCauchyGram_posSemidef hw).mul_mul_conjTranspose_same
      (pickValueDiagonal (1 + f))).smul (by norm_num)

theorem rightHalfPlanePickDefect_eq_cauchy_sub_congruence
    {n : ℕ} (w : Fin n → ℂ) (f : Fin n → ℂ) :
    rightHalfPlanePickDefect w f =
      rightHalfPlaneHardyCauchyGram w -
        pickValueDiagonal f *
          rightHalfPlaneHardyCauchyGram w *
            (pickValueDiagonal f)ᴴ := by
  ext i j
  simp only [Matrix.sub_apply]
  rw [pickValueDiagonal_congruence_apply]
  simp only [rightHalfPlanePickDefect, rightHalfPlaneHardyCauchyGram]
  simp only [div_eq_mul_inv]
  ring

/-- Finite-packet multiplier values of actual Xi Ward transport normalized by source radius two. -/
def xiWardNormalizedTransportMultiplier {n : ℕ}
    (w : Fin n → ℂ) (alpha : ℝ) : Fin n → ℂ :=
  fun i =>
    mobiusGammaXiAntiCausalWardTransportV
      (w i) (alpha : ℂ) / 2

def xiWardTransportMultiplier {n : ℕ}
    (w : Fin n → ℂ) (alpha : ℝ) : Fin n → ℂ :=
  fun i =>
    mobiusGammaXiAntiCausalWardTransportV
      (w i) (alpha : ℂ)

theorem xiWardNormalizedTransportMultiplier_eq
    {n : ℕ} {w : Fin n → ℂ} (hw : ∀ i, 0 < (w i).re)
    (alpha : ℝ) :
    xiWardNormalizedTransportMultiplier w alpha =
      fun i =>
        (1 -
          xiRightWardBoundarySourcePhaseCrossRatio
            (I * w i) (alpha : ℂ)) / 2 := by
  funext i
  rw [xiWardNormalizedTransportMultiplier,
    mobiusGammaXiAntiCausalWardTransportV_eq_one_sub_phase
      (hw i)]

theorem xiWardNormalizedTransportMultiplier_eq_half
    {n : ℕ} (w : Fin n → ℂ) (alpha : ℝ) :
    xiWardNormalizedTransportMultiplier w alpha =
      fun i => xiWardTransportMultiplier w alpha i / 2 :=
  rfl

/-- Actual Xi Ward transport divided by two is nonexpansive on every finite Hardy packet. -/
theorem xiWardNormalizedTransport_nonexpansive
    {n : ℕ} {w : Fin n → ℂ}
    (hw : ∀ i, 0 < (w i).re)
    {alpha : ℝ} (ha : 0 ≤ alpha) :
    (rightHalfPlaneHardyCauchyGram w -
      pickValueDiagonal
          (xiWardNormalizedTransportMultiplier w alpha) *
        rightHalfPlaneHardyCauchyGram w *
          (pickValueDiagonal
            (xiWardNormalizedTransportMultiplier w alpha))ᴴ).PosSemidef := by
  rw [← rightHalfPlanePickDefect_eq_cauchy_sub_congruence]
  rw [xiWardNormalizedTransportMultiplier_eq hw alpha]
  exact rightHalfPlanePickDefect_oneSubHalf_posSemidef hw
    (xiWardPhasePickDefect_posSemidef hw ha)

/-- Four-unit form of nonexpansiveness for unnormalized actual transport `V`. -/
theorem xiWardTransport_fourUnit_nonexpansive
    {n : ℕ} {w : Fin n → ℂ}
    (hw : ∀ i, 0 < (w i).re)
    {alpha : ℝ} (ha : 0 ≤ alpha) :
    ((4 : ℝ) • rightHalfPlaneHardyCauchyGram w -
      pickValueDiagonal (xiWardTransportMultiplier w alpha) *
        rightHalfPlaneHardyCauchyGram w *
          (pickValueDiagonal
            (xiWardTransportMultiplier w alpha))ᴴ).PosSemidef := by
  have h :=
    (xiWardNormalizedTransport_nonexpansive hw ha).smul
      (show (0 : ℝ) ≤ 4 by norm_num)
  have heq :
      (4 : ℝ) •
          (rightHalfPlaneHardyCauchyGram w -
            pickValueDiagonal
                (xiWardNormalizedTransportMultiplier w alpha) *
              rightHalfPlaneHardyCauchyGram w *
                (pickValueDiagonal
                  (xiWardNormalizedTransportMultiplier w alpha))ᴴ) =
        (4 : ℝ) • rightHalfPlaneHardyCauchyGram w -
          pickValueDiagonal (xiWardTransportMultiplier w alpha) *
            rightHalfPlaneHardyCauchyGram w *
              (pickValueDiagonal
                (xiWardTransportMultiplier w alpha))ᴴ := by
    ext i j
    let H : Matrix (Fin n) (Fin n) ℂ :=
      pickValueDiagonal
          (xiWardNormalizedTransportMultiplier w alpha) *
        rightHalfPlaneHardyCauchyGram w *
          (pickValueDiagonal
            (xiWardNormalizedTransportMultiplier w alpha))ᴴ
    let K : Matrix (Fin n) (Fin n) ℂ :=
      pickValueDiagonal (xiWardTransportMultiplier w alpha) *
        rightHalfPlaneHardyCauchyGram w *
          (pickValueDiagonal
            (xiWardTransportMultiplier w alpha))ᴴ
    change
      (4 : ℂ) * (rightHalfPlaneHardyCauchyGram w i j - H i j) =
        (4 : ℂ) * rightHalfPlaneHardyCauchyGram w i j - K i j
    have hH :
        H i j =
          xiWardNormalizedTransportMultiplier w alpha i *
            rightHalfPlaneHardyCauchyGram w i j *
              star
                (xiWardNormalizedTransportMultiplier w alpha j) := by
      exact pickValueDiagonal_congruence_apply _ _ i j
    have hK :
        K i j =
          xiWardTransportMultiplier w alpha i *
            rightHalfPlaneHardyCauchyGram w i j *
              star (xiWardTransportMultiplier w alpha j) := by
      exact pickValueDiagonal_congruence_apply _ _ i j
    rw [hH, hK]
    simp only [xiWardNormalizedTransportMultiplier_eq_half]
    have hstarHalf :
        star
            (xiWardTransportMultiplier w alpha j / (2 : ℂ)) =
          star (xiWardTransportMultiplier w alpha j) / 2 := by
      change
        (starRingEnd ℂ)
            (xiWardTransportMultiplier w alpha j / (2 : ℂ)) = _
      rw [map_div₀, starRingEnd_apply]
      simp only [map_ofNat]
    rw [hstarHalf]
    ring
  rw [← heq]
  exact h

end

end RHTower
