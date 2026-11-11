import GaloisForLFunctions.FamilyContinuationTheory.TheBudgetInTheTwistExponent
import GaloisForLFunctions.FamilyContinuationTheory.UniformSubpolynomialBoundsForDirichletTwists
import GaloisForLFunctions.FamilyContinuationTheory.TheSignalOfTheZetaKernelIsAMoebiusSum
import GaloisForLFunctions.RHTower.DirichletCharacterQuadraticJacobiIdentity
import GaloisForLFunctions.RHTower.Sieve.PrimeWindow
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The shortest family with a generic mean square

Let `n ≥ 2` and let a ring carry the `n`-th roots of unity, with residue symbol `(m / u)_n` of
order `n`. A twist `u` decomposes into an `n`-th-power-free core `u₀` and an `n`-th-power radical
`a^n`; on the `n`-th-power radical `(m / a^n)_n = 1_{gcd(m, a) = 1}`, while on `u₀` the symbol is a
primitive character `χ_{u₀}`. This module establishes the exact closed-form answer to how short a
twist family of norm up to `Z^θ` can be and still carry a generic mean square `O_ε(Z^{θ + 1 + ε})`
of smoothed Möbius sums of length `Z`:

1. **Exact prime-avoidance amplification and subpolynomial Euler factors**
   (`twistedMoebiusSum_eq_sub_insert`, `twistedMoebiusSum_insert_eq_tsum`,
   `norm_twistedMoebiusSum_le_of_base_le`, `exists_eulerProd_primeFactors_le_rpow`). Removing a
   prime `p` multiplies the Dirichlet series of `μ · χ` by `(1 − χ(p) p^{-s})⁻¹`, giving the
   exact two-term identity `M_∅(Z) = M_{p}(Z) − χ(p) M_{p}(Z / p)` and the convergent geometric
   series `M_{p}(Z) = ∑_{k ≥ 0} χ(p)^k M_∅(Z / p^k)`.
2. **One-step prime-window exponent drop** (`exists_signal_drop_of_primeWindow_meanSquare`). Any
   generic mean square over prime twists `p ∈ (M, Q M]` at scale `M ≍ Z^{θ/n}` lowers a signal
   exponent `β ≥ 1/2` to `max(1/2 + (1 − 1/n)θ/2, β(1 − θ/n)) + ε`. Applied directly at
   `β = Θ + δ`, this forces `Θ ≤ min(1, 1/2 + (1 − 1/n)θ/2)` in a single step.
3. **Exact minimum of the principal `n`-th-power subfamily** (`principalTwistGenericSet_poleKernel`,
   `principalTwistGenericSet_gaussianKernel`, `isLeast_principalTwistGeneric_poleKernel`,
   `isLeast_principalTwistGeneric_gaussianKernel`,
   `principalTwistThreshold_eq_zero_iff_riemannHypothesis`). For both the pole kernel and the
   Gaussian kernel and every `n ≥ 2`, the set of `θ ≥ 0` with generic mean square is the closed ray
   `[n/(n − 1) · (2 Θ_ζ − 1), ∞)`, attaining its exact minimum
   `θ_min = n/(n − 1) · (2 Θ_ζ − 1)`, which vanishes if and only if `RiemannHypothesis` holds.
4. **Sharp non-cancellative / operator-norm barrier** (`positiveSquarefreeTwistGenericSet_eq`,
   `isLeast_positiveSquarefreeTwistGeneric`). Replacing `μ(m)` by `μ(m)²` destroys sign
   cancellation and shifts the exact minimum unconditionally to `n/(n − 1)` (`= 2` for `n = 2`,
   `6/5` for `n = 6`), proving that every `θ < n/(n − 1)` requires genuine Möbius sign cancellation
   across `m`.
5. **Full Jacobi quadratic twist family (`n = 2`)** (`zetaZeroAbscissa_and_jacobiPrimChar_le_of_jacobiTwistGeneric`,
   `forall_jacobiTwistGeneric_iff_quadraticGRH`, `sInf_jacobiTwistGeneric_eq_zero_iff_quadraticGRH`).
   Over all odd moduli `1 ≤ u ≤ Z^θ` weighted by the Jacobi symbol `(m / u)`, a generic mean square
   at `θ > 0` forces both `ζ` and every odd squarefree primitive quadratic `L(s, χ_{u₀})` to be
   zero-free right of `min(1, 1/2 + θ/4)`. Combined with the conductor-uniform subpolynomial lower
   bound of `UniformSubpolynomialBoundsForDirichletTwists`, generic mean square holds down to
   `θ → 0⁺` (and at `θ = 0`) if and only if GRH holds for `ζ` and all odd primitive real Dirichlet
   characters.
-/

noncomputable section

open Complex MeasureTheory Filter Set Finset
open scoped Topology

namespace GaloisForLFunctions.FamilyContinuationTheory

open GaloisForLFunctions.FamilyContinuationTheory.Budget

/-! ### Smooth Mellin cutoffs and explicit Gaussian signal -/

/-- A vertical-line weight `W` on `Re s = 2` that is continuous and `O((1 + y²)⁻¹)`. -/
structure IsSmoothCutoff (W : ℂ → ℂ) : Prop where
  continuous_linePoint : Continuous fun y : ℝ => W (linePoint y)
  exists_norm_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, ‖W (linePoint y)‖ ≤ C * (1 + y ^ 2)⁻¹

theorem isSmoothCutoff_poleKernel (c : ℝ) : IsSmoothCutoff (poleKernel c) where
  continuous_linePoint := continuous_poleKernel_linePoint c
  exists_norm_le := ⟨Real.exp ((2 - c) ^ 2), (Real.exp_pos _).le, norm_poleKernel_linePoint_le c⟩

theorem norm_gaussianKernel_linePoint_le (c : ℝ) (y : ℝ) :
    ‖gaussianKernel c (linePoint y)‖ ≤ Real.exp ((2 - c) ^ 2) * (1 + y ^ 2)⁻¹ := by
  have hexp : Real.exp (-(y ^ 2)) ≤ (1 + y ^ 2)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (y ^ 2)])
  unfold gaussianKernel
  rw [norm_cexp_sub_sq, linePoint_re, linePoint_im, neg_sq, sub_eq_add_neg, Real.exp_add]
  exact mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le

theorem isSmoothCutoff_gaussianKernel (c : ℝ) : IsSmoothCutoff (gaussianKernel c) where
  continuous_linePoint := by
    unfold gaussianKernel
    have := continuous_linePoint
    fun_prop
  exists_norm_le :=
    ⟨Real.exp ((2 - c) ^ 2), (Real.exp_pos _).le, norm_gaussianKernel_linePoint_le c⟩

theorem exists_norm_signal_two_le {W : ℂ → ℂ} (hW : IsSmoothCutoff W) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 0 < X → ‖signal W 2 X‖ ≤ C * X ^ 2 := by
  obtain ⟨C₀, hC₀, hbound⟩ := hW.exists_norm_le
  refine ⟨(C₀ + 1) / 2, by positivity, fun X hX => ?_⟩
  rw [signal_two_eq_integral, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hpoint : ∀ y : ℝ, ‖(X : ℂ) ^ linePoint y • W (linePoint y)‖ ≤
      X ^ 2 * (C₀ + 1) * (1 + y ^ 2)⁻¹ := by
    intro y
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hX, linePoint_re, Real.rpow_two]
    calc X ^ 2 * ‖W (linePoint y)‖
        ≤ X ^ 2 * (C₀ * (1 + y ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (hbound y) (by positivity)
      _ ≤ X ^ 2 * ((C₀ + 1) * (1 + y ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity)
      _ = X ^ 2 * (C₀ + 1) * (1 + y ^ 2)⁻¹ := by ring
  have hdom : Integrable fun y : ℝ => X ^ 2 * (C₀ + 1) * (1 + y ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul _
  have hint : ‖∫ y : ℝ, (X : ℂ) ^ linePoint y • W (linePoint y)‖ ≤
      X ^ 2 * (C₀ + 1) * Real.pi := by
    calc ‖∫ y : ℝ, (X : ℂ) ^ linePoint y • W (linePoint y)‖
        ≤ ∫ y : ℝ, ‖(X : ℂ) ^ linePoint y • W (linePoint y)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ y : ℝ, X ^ 2 * (C₀ + 1) * (1 + y ^ 2)⁻¹ :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hdom
            (Eventually.of_forall hpoint)
      _ = X ^ 2 * (C₀ + 1) * Real.pi := by
          rw [integral_const_mul, integral_univ_inv_one_add_sq]
  calc 1 / (2 * Real.pi) * ‖∫ y : ℝ, (X : ℂ) ^ linePoint y • W (linePoint y)‖
      ≤ 1 / (2 * Real.pi) * (X ^ 2 * (C₀ + 1) * Real.pi) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = (C₀ + 1) / 2 * X ^ 2 := by
        have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
        field_simp

/-- **Explicit log-Gaussian cutoff formula.** For every real `c` and `X > 0`, the inverse Mellin
signal of `gaussianKernel c` is the strictly positive real log-Gaussian
`X^c / (2 √π) · exp(-(log X)² / 4)`. -/
theorem signal_gaussianKernel_eq (c : ℝ) {X : ℝ} (hX : 0 < X) :
    signal (gaussianKernel c) 2 X =
      (((X ^ c / (2 * Real.sqrt Real.pi) * Real.exp (-(Real.log X ^ 2 / 4))) : ℝ) : ℂ) := by
  rw [signal_two_eq_integral]
  set L : ℂ := (Real.log X : ℂ)
  set c_lin : ℂ := -(L + 2 * (2 - (c : ℂ))) * I
  set d_const : ℂ := 2 * L + (2 - (c : ℂ)) ^ 2
  have hfun : (fun y : ℝ => (X : ℂ) ^ linePoint y • gaussianKernel c (linePoint y)) =
      fun y : ℝ => cexp ((-1 : ℂ) * (y : ℂ) ^ 2 + c_lin * (y : ℂ) + d_const) := by
    funext y
    rw [smul_eq_mul, cpow_def_of_ne_zero (ofReal_ne_zero.mpr hX.ne'), ← Complex.ofReal_log hX.le]
    unfold gaussianKernel linePoint
    rw [← Complex.exp_add]
    congr 1
    simp only [L, c_lin, d_const]
    ring_nf
    rw [I_sq]
    ring
  rw [hfun, _root_.integral_cexp_quadratic (show (-1 : ℂ).re < 0 by simp) c_lin d_const]
  have hpi : ((Real.pi : ℂ) / -(-1 : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [neg_neg, div_one, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow Real.pi_pos.le, Real.sqrt_eq_rpow]
  have hexp_arg : d_const - c_lin ^ 2 / (4 * (-1 : ℂ)) =
      (((c * Real.log X - Real.log X ^ 2 / 4) : ℝ) : ℂ) := by
    simp only [L, c_lin, d_const]
    ring_nf
    rw [I_sq]
    push_cast
    ring
  rw [hpi, hexp_arg, ← Complex.ofReal_exp]
  rw [Complex.real_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  have hrpow : X ^ c * Real.exp (-(Real.log X ^ 2 / 4)) =
      Real.exp (c * Real.log X - Real.log X ^ 2 / 4) := by
    rw [Real.rpow_def_of_pos hX, ← Real.exp_add]
    ring_nf
  rw [← hrpow]
  have hsqrt_ne : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpi_eq : Real.pi = Real.sqrt Real.pi * Real.sqrt Real.pi :=
    (Real.mul_self_sqrt Real.pi_pos.le).symm
  calc 1 / (2 * Real.pi) * (Real.sqrt Real.pi * (X ^ c * Real.exp (-(Real.log X ^ 2 / 4))))
      = 1 / (2 * (Real.sqrt Real.pi * Real.sqrt Real.pi)) *
          (Real.sqrt Real.pi * (X ^ c * Real.exp (-(Real.log X ^ 2 / 4)))) := by
          nth_rw 1 [hpi_eq]
    _ = X ^ c / (2 * Real.sqrt Real.pi) * Real.exp (-(Real.log X ^ 2 / 4)) := by
          field_simp

/-! ### Twisted Möbius sums avoiding a finite set of primes -/

/-- Coefficient `1_{(m, ∏_{p ∈ S} p) = 1} μ(m) χ(m)` of a twisted Möbius sum avoiding `S`. -/
def primeAvoidCoeff (χ : ℕ → ℂ) (S : Finset ℕ) (m : ℕ) : ℂ :=
  if ∀ p ∈ S, ¬ p ∣ m then (ArithmeticFunction.moebius m : ℂ) * χ m else 0

/-- Smoothed twisted Möbius sum `∑_{(m, S) = 1} μ(m) χ(m) signal(W, 2, Z/m)`. -/
def twistedMoebiusSum (W : ℂ → ℂ) (χ : ℕ → ℂ) (S : Finset ℕ) (Z : ℝ) : ℂ :=
  ∑' m : ℕ, primeAvoidCoeff χ S m * signal W 2 (Z / m)

@[simp]
theorem primeAvoidCoeff_zero (χ : ℕ → ℂ) (S : Finset ℕ) : primeAvoidCoeff χ S 0 = 0 := by
  simp [primeAvoidCoeff]

@[simp]
theorem primeAvoidCoeff_empty (χ : ℕ → ℂ) (m : ℕ) :
    primeAvoidCoeff χ ∅ m = (ArithmeticFunction.moebius m : ℂ) * χ m := by
  simp [primeAvoidCoeff]

theorem norm_moebius_complex_le_one (m : ℕ) : ‖(ArithmeticFunction.moebius m : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one : |ArithmeticFunction.moebius m| ≤ 1)

theorem norm_primeAvoidCoeff_le_one {χ : ℕ → ℂ} (hχ : ∀ m : ℕ, ‖χ m‖ ≤ 1) (S : Finset ℕ)
    (m : ℕ) : ‖primeAvoidCoeff χ S m‖ ≤ 1 := by
  unfold primeAvoidCoeff
  split_ifs
  · rw [norm_mul]
    exact mul_le_one₀ (norm_moebius_complex_le_one m) (norm_nonneg _) (hχ m)
  · simp

/-- General Mellin–LSeries termwise integration on `Re s = 2`. -/
theorem signal_eq_tsum_of_LSeries {K W : ℂ → ℂ} (hW : IsSmoothCutoff W) {f : ℕ → ℂ}
    (hf0 : f 0 = 0) (hfnorm : ∀ m : ℕ, ‖f m‖ ≤ 1)
    (hsum : ∀ y : ℝ, LSeriesSummable f (linePoint y))
    (hK : ∀ y : ℝ, K (linePoint y) = W (linePoint y) * LSeries f (linePoint y))
    {Z : ℝ} (hZ : 0 < Z) :
    signal K 2 Z = ∑' m : ℕ, f m * signal W 2 (Z / m) := by
  obtain ⟨C₀, hC₀, hWbound⟩ := hW.exists_norm_le
  set term : ℕ → ℝ → ℂ := fun m y =>
    f m * (((Z / m : ℝ) : ℂ) ^ linePoint y • W (linePoint y))
  have hterm_norm : ∀ m : ℕ, ∀ y : ℝ,
      ‖term m y‖ ≤ Z ^ 2 * (C₀ + 1) * (1 / (m : ℝ) ^ 2) * (1 + y ^ 2)⁻¹ := by
    intro m y
    rcases eq_or_ne m 0 with rfl | hm
    · simp [term, hf0]
    have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
    have hpow : ‖((Z / m : ℝ) : ℂ) ^ linePoint y‖ = Z ^ 2 * (1 / (m : ℝ) ^ 2) := by
      rw [norm_cpow_eq_rpow_re_of_pos (div_pos hZ hmpos), linePoint_re, Real.rpow_two, div_pow]
      ring
    simp only [term, norm_mul, norm_smul, hpow]
    have hW' : ‖W (linePoint y)‖ ≤ (C₀ + 1) * (1 + y ^ 2)⁻¹ :=
      (hWbound y).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    calc ‖f m‖ * (Z ^ 2 * (1 / (m : ℝ) ^ 2) * ‖W (linePoint y)‖)
        ≤ 1 * (Z ^ 2 * (1 / (m : ℝ) ^ 2) * ((C₀ + 1) * (1 + y ^ 2)⁻¹)) :=
          mul_le_mul (hfnorm m) (mul_le_mul_of_nonneg_left hW' (by positivity))
            (by positivity) zero_le_one
      _ = Z ^ 2 * (C₀ + 1) * (1 / (m : ℝ) ^ 2) * (1 + y ^ 2)⁻¹ := by ring
  have hcont : ∀ m : ℕ, Continuous (term m) := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · have : term 0 = fun _ => 0 := by funext y; simp [term, hf0]
      rw [this]; exact continuous_const
    have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
    have hbase : ((Z / m : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (div_pos hZ hmpos).ne'
    exact continuous_const.mul ((continuous_linePoint.const_cpow (Or.inl hbase)).smul
      hW.continuous_linePoint)
  have hint : ∀ m : ℕ, Integrable (term m) := fun m =>
    (integrable_inv_one_add_sq.const_mul _).mono' (hcont m).aestronglyMeasurable
      (Eventually.of_forall (hterm_norm m))
  have hsumm_int : Summable fun m : ℕ => ∫ y : ℝ, ‖term m y‖ := by
    have hb : ∀ m : ℕ, ∫ y : ℝ, ‖term m y‖ ≤
        Z ^ 2 * (C₀ + 1) * Real.pi * (1 / (m : ℝ) ^ 2) := by
      intro m
      have hdom : Integrable fun y : ℝ =>
          Z ^ 2 * (C₀ + 1) * (1 / (m : ℝ) ^ 2) * (1 + y ^ 2)⁻¹ :=
        integrable_inv_one_add_sq.const_mul _
      have h := integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        hdom (Eventually.of_forall (hterm_norm m))
      rw [integral_const_mul, integral_univ_inv_one_add_sq] at h
      linarith
    exact Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hb
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _)
  have hpoint : (fun y : ℝ => ∑' m : ℕ, term m y) =
      fun y : ℝ => (Z : ℂ) ^ linePoint y • K (linePoint y) := by
    funext y
    have hL := (hsum y).LSeriesHasSum
    have hfun : (fun m : ℕ => (Z : ℂ) ^ linePoint y * W (linePoint y) *
        LSeries.term f (linePoint y) m) = fun m : ℕ => term m y := by
      funext m
      rcases eq_or_ne m 0 with rfl | hm
      · simp [term, hf0, LSeries.term_def]
      · rw [LSeries.term_def, if_neg hm]
        simp only [term, smul_eq_mul, ofReal_div_natCast_cpow hZ.le hm]
        have hne : (m : ℂ) ^ linePoint y ≠ 0 := by
          rw [Ne, cpow_eq_zero_iff]
          exact fun h => (Nat.cast_ne_zero.mpr hm) h.1
        field_simp
    rw [hK y, smul_eq_mul, ← mul_assoc]
    exact (hfun ▸ hL.mul_left _).tsum_eq
  have hswap := integral_tsum_of_summable_integral_norm hint hsumm_int
  rw [hpoint] at hswap
  rw [signal_two_eq_integral, ← hswap, ← tsum_const_smul'']
  refine tsum_congr fun m => ?_
  rw [signal_two_eq_integral]
  simp only [term]
  rw [integral_const_mul]
  exact (mul_smul_comm _ _ _).symm

theorem signal_zetaKernel_eq_twistedMoebiusSum (c : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    signal (zetaKernel c) 2 Z = twistedMoebiusSum (poleKernel c) (fun _ => 1) ∅ Z := by
  rw [signal_zetaKernel_eq_tsum c hZ]
  unfold twistedMoebiusSum
  refine tsum_congr fun m => ?_
  simp

theorem signal_zetaGaussianKernel_eq_twistedMoebiusSum (c : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    signal (zetaGaussianKernel c) 2 Z =
      twistedMoebiusSum (gaussianKernel c) (fun _ => 1) ∅ Z := by
  have h := signal_eq_tsum_of_LSeries (K := zetaGaussianKernel c) (W := gaussianKernel c)
    (isSmoothCutoff_gaussianKernel c) (f := fun m => (ArithmeticFunction.moebius m : ℂ))
    (by simp) norm_moebius_complex_le_one
    (fun y => ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by rw [linePoint_re]; norm_num))
    (fun y => by
      have hre : 1 < (linePoint y).re := by rw [linePoint_re]; norm_num
      have hs1 : linePoint y ≠ 1 := fun h => by rw [h] at hre; norm_num at hre
      have hL := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hre
      rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hre] at hL
      have hinv : LSeries (fun m : ℕ => (ArithmeticFunction.moebius m : ℂ)) (linePoint y) =
          (riemannZeta (linePoint y))⁻¹ := eq_inv_of_mul_eq_one_right hL
      unfold zetaGaussianKernel gaussianKernel
      rw [RHTower.zetaEntire_eq hs1, hinv]
      have hsub : linePoint y - 1 ≠ 0 := sub_ne_zero.mpr hs1
      field_simp) hZ
  rw [h]
  unfold twistedMoebiusSum
  refine tsum_congr fun m => ?_
  simp

theorem signal_dirichletGaussianKernel_eq_twistedMoebiusSum {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (c : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    signal (dirichletGaussianKernel χ c) 2 Z =
      twistedMoebiusSum (gaussianKernel c) (fun m => χ m) ∅ Z := by
  set f : ℕ → ℂ := fun m => (ArithmeticFunction.moebius m : ℂ) * χ m
  have hf_eq : f = (fun m : ℕ => χ m) * (fun m : ℕ => (ArithmeticFunction.moebius m : ℂ)) := by
    funext m; simp [f, mul_comm]
  have h := signal_eq_tsum_of_LSeries (K := dirichletGaussianKernel χ c) (W := gaussianKernel c)
    (isSmoothCutoff_gaussianKernel c) (f := f) (by simp [f])
    (fun m => by
      simp only [f, norm_mul]
      exact mul_le_one₀ (norm_moebius_complex_le_one m) (norm_nonneg _)
        (RHTower.norm_dirichletCharacter_le_one χ m))
    (fun y => by
      rw [hf_eq]
      exact DirichletCharacter.LSeriesSummable_mul χ
        (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by rw [linePoint_re]; norm_num)))
    (fun y => by
      have hre : 1 < (linePoint y).re := by rw [linePoint_re]; norm_num
      have hmul := DirichletCharacter.LSeries.mul_mu_eq_one χ hre
      rw [← DirichletCharacter.LFunction_eq_LSeries χ hre, ← hf_eq] at hmul
      have hinv : LSeries f (linePoint y) = (DirichletCharacter.LFunction χ (linePoint y))⁻¹ :=
        eq_inv_of_mul_eq_one_right hmul
      unfold dirichletGaussianKernel gaussianKernel
      rw [hinv, div_eq_mul_inv]) hZ
  rw [h]
  unfold twistedMoebiusSum
  refine tsum_congr fun m => ?_
  simp [f]

/-! ### Absolute summability, exact prime split, and geometric-series amplification -/

theorem summable_norm_twistedMoebiusTerm {W : ℂ → ℂ} (hW : IsSmoothCutoff W)
    {χ : ℕ → ℂ} (hχ : ∀ m : ℕ, ‖χ m‖ ≤ 1) (S : Finset ℕ) {Z : ℝ} (hZ : 0 < Z) :
    Summable fun m : ℕ => ‖primeAvoidCoeff χ S m * signal W 2 (Z / m)‖ := by
  obtain ⟨C, hC, hsig⟩ := exists_norm_signal_two_le hW
  have hle : ∀ m : ℕ, ‖primeAvoidCoeff χ S m * signal W 2 (Z / m)‖ ≤
      C * Z ^ 2 * (1 / (m : ℝ) ^ 2) := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
    rw [norm_mul]
    calc ‖primeAvoidCoeff χ S m‖ * ‖signal W 2 (Z / m)‖
        ≤ 1 * (C * (Z / m) ^ 2) :=
          mul_le_mul (norm_primeAvoidCoeff_le_one hχ S m) (hsig _ (div_pos hZ hmpos))
            (norm_nonneg _) zero_le_one
      _ = C * Z ^ 2 * (1 / (m : ℝ) ^ 2) := by rw [div_pow]; ring
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _)

theorem exists_norm_twistedMoebiusSum_le_sq {W : ℂ → ℂ} (hW : IsSmoothCutoff W) :
    ∃ C_sum : ℝ, 0 < C_sum ∧ ∀ (χ : ℕ → ℂ), (∀ m : ℕ, ‖χ m‖ ≤ 1) →
      ∀ (S : Finset ℕ) (Z : ℝ), 0 < Z → ‖twistedMoebiusSum W χ S Z‖ ≤ C_sum * Z ^ 2 := by
  obtain ⟨C, hC, hsig⟩ := exists_norm_signal_two_le hW
  have hzeta2_summ : Summable fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ (2 : ℕ) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  set S₂ : ℝ := ∑' m : ℕ, (1 : ℝ) / (m : ℝ) ^ (2 : ℕ)
  have hS₂_nn : 0 ≤ S₂ := tsum_nonneg fun _ => by positivity
  refine ⟨C * (S₂ + 1), by positivity, fun χ hχ S Z hZ => ?_⟩
  have hnorm_summ := summable_norm_twistedMoebiusTerm hW hχ S hZ
  have hle : ∀ m : ℕ, ‖primeAvoidCoeff χ S m * signal W 2 (Z / m)‖ ≤
      C * Z ^ 2 * (1 / (m : ℝ) ^ (2 : ℕ)) := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
    rw [norm_mul]
    calc ‖primeAvoidCoeff χ S m‖ * ‖signal W 2 (Z / m)‖
        ≤ 1 * (C * (Z / m) ^ 2) :=
          mul_le_mul (norm_primeAvoidCoeff_le_one hχ S m) (hsig _ (div_pos hZ hmpos))
            (norm_nonneg _) zero_le_one
      _ = C * Z ^ 2 * (1 / (m : ℝ) ^ (2 : ℕ)) := by rw [div_pow]; ring
  calc ‖twistedMoebiusSum W χ S Z‖
      ≤ ∑' m : ℕ, ‖primeAvoidCoeff χ S m * signal W 2 (Z / m)‖ :=
        norm_tsum_le_tsum_norm hnorm_summ
    _ ≤ ∑' m : ℕ, C * Z ^ 2 * (1 / (m : ℝ) ^ (2 : ℕ)) :=
        hnorm_summ.tsum_le_tsum hle (hzeta2_summ.mul_left _)
    _ = C * Z ^ 2 * S₂ := tsum_mul_left
    _ ≤ C * (S₂ + 1) * Z ^ 2 := by nlinarith [hC.le, sq_nonneg Z]

/-- **Exact two-term prime split.** Removing a prime `p ∉ S` from a twisted Möbius sum splits into
`M_S(Z) = M_{insert p S}(Z) − χ(p) M_{insert p S}(Z / p)`. -/
theorem twistedMoebiusSum_eq_sub_insert {W : ℂ → ℂ} (hW : IsSmoothCutoff W)
    {χ : ℕ → ℂ} (hχ : ∀ m : ℕ, ‖χ m‖ ≤ 1) {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    {p : ℕ} (hp : p.Prime) (hpS : p ∉ S)
    (hχ_mul : ∀ k : ℕ, ¬ p ∣ k → χ (p * k) = χ p * χ k) {Z : ℝ} (hZ : 0 < Z) :
    twistedMoebiusSum W χ S Z =
      twistedMoebiusSum W χ (insert p S) Z -
        χ p * twistedMoebiusSum W χ (insert p S) (Z / p) := by
  set f : ℕ → ℂ := fun m => primeAvoidCoeff χ S m * signal W 2 (Z / m)
  set g₁ : ℕ → ℂ := fun m => primeAvoidCoeff χ (insert p S) m * signal W 2 (Z / m)
  set g₂ : ℕ → ℂ := fun m => if p ∣ m then f m else 0
  have hf_summ : Summable f := (summable_norm_twistedMoebiusTerm hW hχ S hZ).of_norm
  have hg₁_summ : Summable g₁ := (summable_norm_twistedMoebiusTerm hW hχ (insert p S) hZ).of_norm
  have hg₂_summ : Summable g₂ := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      (summable_norm_twistedMoebiusTerm hW hχ S hZ))
    simp only [g₂]
    split_ifs
    · rfl
    · simp only [norm_zero]
      exact norm_nonneg _
  have hpoint : ∀ m : ℕ, f m = g₁ m + g₂ m := by
    intro m
    by_cases hpm : p ∣ m
    · have hnot : ¬ ∀ q ∈ insert p S, ¬ q ∣ m := fun h => h p (Finset.mem_insert_self p S) hpm
      simp only [f, g₁, g₂, primeAvoidCoeff, if_pos hpm, if_neg hnot, zero_mul, zero_add]
    · have heq : (∀ q ∈ insert p S, ¬ q ∣ m) ↔ (∀ q ∈ S, ¬ q ∣ m) := by
        rw [Finset.forall_mem_insert]
        exact ⟨fun h => h.2, fun h => ⟨hpm, h⟩⟩
      simp only [f, g₁, g₂, primeAvoidCoeff, if_neg hpm, heq, add_zero]
  have hsplit : twistedMoebiusSum W χ S Z = twistedMoebiusSum W χ (insert p S) Z + ∑' m : ℕ, g₂ m := by
    change ∑' m : ℕ, f m = (∑' m : ℕ, g₁ m) + ∑' m : ℕ, g₂ m
    rw [show f = fun m => g₁ m + g₂ m from funext hpoint, hg₁_summ.tsum_add hg₂_summ]
  have hinj : Function.Injective (fun k : ℕ => p * k) := mul_right_injective₀ hp.ne_zero
  have hg₂_tsum : (∑' m : ℕ, g₂ m) = ∑' k : ℕ, g₂ (p * k) := by
    symm
    refine hinj.tsum_eq fun m hm => ?_
    simp only [g₂]
    rw [if_neg]
    rintro ⟨k, rfl⟩
    exact hm ⟨k, rfl⟩
  have hpk_term : ∀ k : ℕ, g₂ (p * k) =
      -(χ p * (primeAvoidCoeff χ (insert p S) k * signal W 2 ((Z / p) / k))) := by
    intro k
    have hdiv : p ∣ p * k := dvd_mul_right p k
    simp only [g₂, if_pos hdiv, f]
    have hZpk : Z / ((p * k : ℕ) : ℝ) = (Z / p) / (k : ℝ) := by push_cast; rw [div_div]
    rw [hZpk]
    by_cases hpk : p ∣ k
    · have hnsq : ¬ Squarefree (p * k) := by
        intro hsq
        rcases hpk with ⟨r, rfl⟩
        have hunit := hsq p (by refine ⟨r, ?_⟩; ring)
        rw [Nat.isUnit_iff] at hunit
        exact hp.ne_one hunit
      have hμ0 : ArithmeticFunction.moebius (p * k) = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq
      have hnot : ¬ ∀ q ∈ insert p S, ¬ q ∣ k := fun h => h p (Finset.mem_insert_self p S) hpk
      rw [primeAvoidCoeff, primeAvoidCoeff, if_neg hnot]
      simp [hμ0]
    · have hcop : Nat.Coprime p k := hp.coprime_iff_not_dvd.mpr hpk
      have hS_iff : (∀ q ∈ S, ¬ q ∣ p * k) ↔ (∀ q ∈ insert p S, ¬ q ∣ k) := by
        rw [Finset.forall_mem_insert]
        refine ⟨fun h => ⟨hpk, fun q hq hqk => h q hq (dvd_mul_of_dvd_right hqk p)⟩,
          fun ⟨_, h⟩ q hq hqpk => ?_⟩
        have hqp : q ≠ p := fun hEq => hpS (hEq ▸ hq)
        rcases (hS q hq).dvd_mul.mp hqpk with h1 | h2
        · exact hqp (((Nat.dvd_prime hp).mp h1).resolve_left (hS q hq).ne_one)
        · exact h q hq h2
      have hμ : (ArithmeticFunction.moebius (p * k) : ℂ) = -(ArithmeticFunction.moebius k : ℂ) := by
        have hm := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
        rw [hm, ArithmeticFunction.moebius_apply_prime hp]
        push_cast
        ring
      by_cases hkS : ∀ q ∈ insert p S, ¬ q ∣ k
      · have hpkS : ∀ q ∈ S, ¬ q ∣ p * k := hS_iff.mpr hkS
        simp only [primeAvoidCoeff, if_pos hpkS, if_pos hkS, hμ, hχ_mul k hpk]
        ring
      · have hpkS : ¬ ∀ q ∈ S, ¬ q ∣ p * k := fun h => hkS (hS_iff.mp h)
        rw [primeAvoidCoeff, if_neg hpkS, primeAvoidCoeff, if_neg hkS]
        simp
  rw [hsplit, hg₂_tsum, show (fun k : ℕ => g₂ (p * k)) = _ from funext hpk_term,
    tsum_neg, tsum_mul_left]
  rfl

/-- **Exact geometric-series amplification.** Avoiding a prime `p ∉ S` expands into the convergent
geometric series `M_{insert p S}(Z) = ∑'_{k ≥ 0} χ(p)^k M_S(Z / p^k)`. -/
theorem hasSum_twistedMoebiusSum_insert {W : ℂ → ℂ} (hW : IsSmoothCutoff W)
    {χ : ℕ → ℂ} (hχ : ∀ m : ℕ, ‖χ m‖ ≤ 1) {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    {p : ℕ} (hp : p.Prime) (hpS : p ∉ S)
    (hχ_mul : ∀ k : ℕ, ¬ p ∣ k → χ (p * k) = χ p * χ k) {Z : ℝ} (hZ : 0 < Z) :
    HasSum (fun k : ℕ => χ p ^ k * twistedMoebiusSum W χ S (Z / (p : ℝ) ^ k))
      (twistedMoebiusSum W χ (insert p S) Z) := by
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hp_ge2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  -- Finite telescoping identity for all `K : ℕ`.
  have htel : ∀ K : ℕ, twistedMoebiusSum W χ (insert p S) Z =
      (∑ k ∈ Finset.range K, χ p ^ k * twistedMoebiusSum W χ S (Z / (p : ℝ) ^ k)) +
        χ p ^ K * twistedMoebiusSum W χ (insert p S) (Z / (p : ℝ) ^ K) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      have hZK : 0 < Z / (p : ℝ) ^ K := div_pos hZ (pow_pos hp_pos K)
      have hstep := twistedMoebiusSum_eq_sub_insert hW hχ hS hp hpS hχ_mul hZK
      have hdiv : Z / (p : ℝ) ^ K / (p : ℝ) = Z / (p : ℝ) ^ (K + 1) := by
        rw [div_div, ← pow_succ]
      rw [hdiv] at hstep
      have hins : twistedMoebiusSum W χ (insert p S) (Z / (p : ℝ) ^ K) =
          twistedMoebiusSum W χ S (Z / (p : ℝ) ^ K) +
            χ p * twistedMoebiusSum W χ (insert p S) (Z / (p : ℝ) ^ (K + 1)) := by
        linear_combination -hstep
      rw [ih, hins, Finset.sum_range_succ, pow_succ]
      ring
  obtain ⟨C_sum, hC_sum, hbound⟩ := exists_norm_twistedMoebiusSum_le_sq hW
  have hr_lt : (1 : ℝ) / (p : ℝ) ^ (2 : ℕ) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  have hr_nn : 0 ≤ (1 : ℝ) / (p : ℝ) ^ (2 : ℕ) := by positivity
  -- Norm summability of the geometric-series terms.
  have hnorm_summ : Summable fun k : ℕ =>
      ‖χ p ^ k * twistedMoebiusSum W χ S (Z / (p : ℝ) ^ k)‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one hr_nn hr_lt).mul_left (C_sum * Z ^ 2))
    rw [norm_mul, norm_pow]
    have h1 : ‖χ p‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) (hχ p)
    have h2 := hbound χ hχ S (Z / (p : ℝ) ^ k) (div_pos hZ (pow_pos hp_pos k))
    calc ‖χ p‖ ^ k * ‖twistedMoebiusSum W χ S (Z / (p : ℝ) ^ k)‖
        ≤ 1 * (C_sum * (Z / (p : ℝ) ^ k) ^ 2) :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = C_sum * Z ^ 2 * ((1 / (p : ℝ) ^ (2 : ℕ)) ^ k) := by
          rw [div_pow, one_div_pow, ← pow_mul, mul_comm k 2, pow_mul]
          ring
  -- Remainder tends to `0`.
  have hrem : Tendsto (fun K : ℕ =>
      ‖χ p ^ K * twistedMoebiusSum W χ (insert p S) (Z / (p : ℝ) ^ K)‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => norm_nonneg _) (fun K => ?_)
      (by
        rw [← mul_zero (C_sum * Z ^ 2)]
        exact (tendsto_pow_atTop_nhds_zero_of_lt_one hr_nn hr_lt).const_mul _)
    rw [norm_mul, norm_pow]
    have h1 : ‖χ p‖ ^ K ≤ 1 := pow_le_one₀ (norm_nonneg _) (hχ p)
    have h2 := hbound χ hχ (insert p S) (Z / (p : ℝ) ^ K) (div_pos hZ (pow_pos hp_pos K))
    calc ‖χ p‖ ^ K * ‖twistedMoebiusSum W χ (insert p S) (Z / (p : ℝ) ^ K)‖
        ≤ 1 * (C_sum * (Z / (p : ℝ) ^ K) ^ 2) :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = C_sum * Z ^ 2 * ((1 / (p : ℝ) ^ (2 : ℕ)) ^ K) := by
          rw [div_pow, one_div_pow, ← pow_mul, mul_comm K 2, pow_mul]
          ring
  rw [hasSum_iff_tendsto_nat_of_summable_norm hnorm_summ, tendsto_iff_norm_sub_tendsto_zero]
  have hdiff : ∀ K : ℕ, ‖(∑ k ∈ Finset.range K,
      χ p ^ k * twistedMoebiusSum W χ S (Z / (p : ℝ) ^ k)) -
      twistedMoebiusSum W χ (insert p S) Z‖ =
      ‖χ p ^ K * twistedMoebiusSum W χ (insert p S) (Z / (p : ℝ) ^ K)‖ := fun K => by
    rw [show (∑ k ∈ Finset.range K,
        χ p ^ k * twistedMoebiusSum W χ S (Z / (p : ℝ) ^ k)) -
        twistedMoebiusSum W χ (insert p S) Z =
        -(χ p ^ K * twistedMoebiusSum W χ (insert p S) (Z / (p : ℝ) ^ K)) by
      linear_combination -(htel K), norm_neg]
  simp_rw [hdiff]
  exact hrem

theorem twistedMoebiusSum_insert_eq_tsum {W : ℂ → ℂ} (hW : IsSmoothCutoff W)
    {χ : ℕ → ℂ} (hχ : ∀ m : ℕ, ‖χ m‖ ≤ 1) {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    {p : ℕ} (hp : p.Prime) (hpS : p ∉ S)
    (hχ_mul : ∀ k : ℕ, ¬ p ∣ k → χ (p * k) = χ p * χ k) {Z : ℝ} (hZ : 0 < Z) :
    twistedMoebiusSum W χ (insert p S) Z =
      ∑' k : ℕ, χ p ^ k * twistedMoebiusSum W χ S (Z / (p : ℝ) ^ k) :=
  (hasSum_twistedMoebiusSum_insert hW hχ hS hp hpS hχ_mul hZ).tsum_eq.symm

/-- **Finite-prime-avoidance Euler-factor bound.** A global bound `‖M_∅(X)‖ ≤ C X^b` (`b > 0`)
propagates to `‖M_S(Z)‖ ≤ C (∏_{p ∈ S} (1 − p^{-b})⁻¹) Z^b` for every finite prime set `S`. -/
theorem norm_twistedMoebiusSum_le_of_base_le {W : ℂ → ℂ} (hW : IsSmoothCutoff W)
    {χ : ℕ → ℂ} (hχ : ∀ m : ℕ, ‖χ m‖ ≤ 1)
    (hχ_mul : ∀ p : ℕ, p.Prime → ∀ k : ℕ, ¬ p ∣ k → χ (p * k) = χ p * χ k)
    {b C : ℝ} (hb : 0 < b) (_hC : 0 ≤ C)
    (hbase : ∀ X : ℝ, 0 < X → ‖twistedMoebiusSum W χ ∅ X‖ ≤ C * X ^ b)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {Z : ℝ} (hZ : 0 < Z) :
    ‖twistedMoebiusSum W χ S Z‖ ≤ C * (∏ p ∈ S, (1 - (p : ℝ) ^ (-b))⁻¹) * Z ^ b := by
  induction S using Finset.induction_on generalizing Z with
  | empty =>
    simpa using hbase Z hZ
  | @insert p S hpS ih =>
    have hp : p.Prime := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
    have hp_gt1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hr_pos : 0 < (p : ℝ) ^ (-b) := Real.rpow_pos_of_pos hp_pos _
    have hr_lt1 : (p : ℝ) ^ (-b) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp_gt1 (by linarith)
    set P_S : ℝ := ∏ q ∈ S, (1 - (q : ℝ) ^ (-b))⁻¹
    have hPS_nn : 0 ≤ P_S := Finset.prod_nonneg fun q hq => by
      have hq1 : (1 : ℝ) < q := by exact_mod_cast (hS' q hq).one_lt
      have hqr : (q : ℝ) ^ (-b) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
      exact inv_nonneg.mpr (by linarith)
    have hhas := hasSum_twistedMoebiusSum_insert hW hχ hS' hp hpS (hχ_mul p hp) hZ
    rw [← hhas.tsum_eq, Finset.prod_insert hpS]
    have hgeom : Summable fun k : ℕ => ((p : ℝ) ^ (-b)) ^ k :=
      summable_geometric_of_lt_one hr_pos.le hr_lt1
    have hterm : ∀ k : ℕ, ‖χ p ^ k * twistedMoebiusSum W χ S (Z / (p : ℝ) ^ k)‖ ≤
        C * P_S * Z ^ b * (((p : ℝ) ^ (-b)) ^ k) := by
      intro k
      rw [norm_mul, norm_pow]
      have h1 : ‖χ p‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) (hχ p)
      have h2 := ih hS' (div_pos hZ (pow_pos hp_pos k))
      have hpow_eq : (Z / (p : ℝ) ^ k) ^ b = Z ^ b * (((p : ℝ) ^ (-b)) ^ k) := by
        rw [Real.div_rpow hZ.le (pow_pos hp_pos k).le, div_eq_mul_inv,
          ← Real.rpow_natCast (p : ℝ) k, ← Real.rpow_mul hp_pos.le,
          ← Real.rpow_neg hp_pos.le, ← Real.rpow_natCast ((p : ℝ) ^ (-b)) k,
          ← Real.rpow_mul hp_pos.le]
        congr 2
        ring
      calc ‖χ p‖ ^ k * ‖twistedMoebiusSum W χ S (Z / (p : ℝ) ^ k)‖
          ≤ 1 * (C * P_S * (Z / (p : ℝ) ^ k) ^ b) :=
            mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = C * P_S * Z ^ b * (((p : ℝ) ^ (-b)) ^ k) := by rw [hpow_eq]; ring
    have hnorm_summ : Summable fun k : ℕ =>
        ‖χ p ^ k * twistedMoebiusSum W χ S (Z / (p : ℝ) ^ k)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hgeom.mul_left _)
    calc ‖∑' k : ℕ, χ p ^ k * twistedMoebiusSum W χ S (Z / (p : ℝ) ^ k)‖
        ≤ ∑' k : ℕ, ‖χ p ^ k * twistedMoebiusSum W χ S (Z / (p : ℝ) ^ k)‖ :=
          norm_tsum_le_tsum_norm hnorm_summ
      _ ≤ ∑' k : ℕ, C * P_S * Z ^ b * (((p : ℝ) ^ (-b)) ^ k) :=
          hnorm_summ.tsum_le_tsum hterm (hgeom.mul_left _)
      _ = C * P_S * Z ^ b * (1 - (p : ℝ) ^ (-b))⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hr_pos.le hr_lt1]
      _ = C * ((1 - (p : ℝ) ^ (-b))⁻¹ * P_S) * Z ^ b := by ring

theorem inv_one_sub_prime_rpow_neg_le_four {p : ℕ} (hp : p.Prime) {b : ℝ} (hb : (1 : ℝ) / 2 ≤ b) :
    (1 - (p : ℝ) ^ (-b))⁻¹ ≤ 4 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hsqrt : (4 : ℝ) / 3 ≤ (2 : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hpb : (4 : ℝ) / 3 ≤ (p : ℝ) ^ b := by
    calc (4 : ℝ) / 3 ≤ (2 : ℝ) ^ ((1 : ℝ) / 2) := hsqrt
      _ ≤ (p : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by norm_num) hp2 (by norm_num)
      _ ≤ (p : ℝ) ^ b := Real.rpow_le_rpow_of_exponent_le (by linarith) hb
  have hp_neg : (p : ℝ) ^ (-b) ≤ 3 / 4 := by
    rw [Real.rpow_neg (by linarith)]
    calc ((p : ℝ) ^ b)⁻¹ ≤ ((4 : ℝ) / 3)⁻¹ := inv_anti₀ (by norm_num) hpb
      _ = 3 / 4 := by norm_num
  calc (1 - (p : ℝ) ^ (-b))⁻¹ ≤ ((1 : ℝ) - 3 / 4)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    _ = 4 := by norm_num

/-- **Subpolynomial Euler-factor bound.** For every `η > 0`, there is `C_η ≥ 1` such that for all
`b ≥ 1/2` and all `a ≥ 1`, `∏_{p | a} (1 − p^{-b})⁻¹ ≤ C_η a^η`. -/
theorem exists_eulerProd_primeFactors_le_rpow {η : ℝ} (hη : 0 < η) :
    ∃ C_η : ℝ, 1 ≤ C_η ∧ ∀ b : ℝ, (1 : ℝ) / 2 ≤ b → ∀ a : ℕ, 1 ≤ a →
      (∏ p ∈ a.primeFactors, (1 - (p : ℝ) ^ (-b))⁻¹) ≤ C_η * (a : ℝ) ^ η := by
  set P₀ : ℕ := ⌈(4 : ℝ) ^ (1 / η)⌉₊
  refine ⟨(4 : ℝ) ^ P₀, one_le_pow₀ (by norm_num), fun b hb a ha => ?_⟩
  have hterm : ∀ p ∈ a.primeFactors,
      (1 - (p : ℝ) ^ (-b))⁻¹ ≤ (if p < P₀ then (4 : ℝ) else 1) * (p : ℝ) ^ η := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have h4 := inv_one_sub_prime_rpow_neg_le_four hprime hb
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hprime.pos
    split_ifs with hlt
    · have hpη : (1 : ℝ) ≤ (p : ℝ) ^ η := Real.one_le_rpow hp1 hη.le
      nlinarith
    · rw [one_mul]
      have hge : (4 : ℝ) ^ (1 / η) ≤ p := (Nat.le_ceil _).trans (by exact_mod_cast not_lt.mp hlt)
      calc (1 - (p : ℝ) ^ (-b))⁻¹ ≤ 4 := h4
        _ = ((4 : ℝ) ^ (1 / η)) ^ η := by
            rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hη.ne', Real.rpow_one]
        _ ≤ (p : ℝ) ^ η := Real.rpow_le_rpow (by positivity) hge hη.le
  have hsmall : (∏ p ∈ a.primeFactors, if p < P₀ then (4 : ℝ) else 1) ≤ (4 : ℝ) ^ P₀ := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    have hsub : a.primeFactors.filter (fun p => p < P₀) ⊆ Finset.range P₀ := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    exact pow_le_pow_right₀ (by norm_num) (Finset.card_le_card hsub |>.trans (by simp))
  have hrad_dvd : (∏ p ∈ a.primeFactors, p) ∣ a := Nat.prod_primeFactors_dvd a
  have hrad_le : ((∏ p ∈ a.primeFactors, p : ℕ) : ℝ) ≤ a := by
    exact_mod_cast Nat.le_of_dvd ha hrad_dvd
  have hrad_pow : (∏ p ∈ a.primeFactors, (p : ℝ) ^ η) ≤ (a : ℝ) ^ η := by
    have hprod_rpow : (∏ p ∈ a.primeFactors, (p : ℝ) ^ η) =
        ((∏ p ∈ a.primeFactors, p : ℕ) : ℝ) ^ η := by
      push_cast
      induction a.primeFactors using Finset.induction_on with
      | empty => simp [Real.one_rpow]
      | @insert q s hqs ih =>
        rw [Finset.prod_insert hqs, Finset.prod_insert hqs,
          Real.mul_rpow (by positivity) (Finset.prod_nonneg fun _ _ => by positivity), ih]
    rw [hprod_rpow]
    exact Real.rpow_le_rpow (by positivity) hrad_le hη.le
  calc ∏ p ∈ a.primeFactors, (1 - (p : ℝ) ^ (-b))⁻¹
      ≤ ∏ p ∈ a.primeFactors, ((if p < P₀ then (4 : ℝ) else 1) * (p : ℝ) ^ η) :=
        Finset.prod_le_prod (fun p hp => by
          have hq1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
          have hqr : (p : ℝ) ^ (-b) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
          exact inv_nonneg.mpr (by linarith)) hterm
    _ = (∏ p ∈ a.primeFactors, if p < P₀ then (4 : ℝ) else 1) *
          (∏ p ∈ a.primeFactors, (p : ℝ) ^ η) := Finset.prod_mul_distrib
    _ ≤ (4 : ℝ) ^ P₀ * (a : ℝ) ^ η :=
        mul_le_mul hsmall hrad_pow
          (Finset.prod_nonneg fun _ _ => by positivity) (by positivity)

/-! ### One-step prime-window exponent drop and zero-abscissa bound -/

/-- **One-step prime-window exponent drop.** If a prime-avoiding family `M_{p}(Z)` has generic mean
square `O_ε(Z^{θ + 1 + ε})` over primes `p ∈ (M, Q M]` with `u_scale · (Q M)^n ≤ Z^θ`, then any
global signal bound `‖M_∅(X)‖ ≤ C_β X^β` (`β ≥ 1/2`) drops to every
`b' > max(positiveFormBoundary n θ, β (1 − θ/n))`. -/
theorem exists_signal_drop_of_primeWindow_meanSquare {W : ℂ → ℂ} (hW : IsSmoothCutoff W)
    {χ : ℕ → ℂ} (hχ : ∀ m : ℕ, ‖χ m‖ ≤ 1)
    (hχ_mul : ∀ p : ℕ, p.Prime → ∀ k : ℕ, ¬ p ∣ k → χ (p * k) = χ p * χ k)
    {n u_scale : ℕ} (hn : 2 ≤ n) (hu_scale : 1 ≤ u_scale)
    {θ : ℝ} (hθ : 0 < θ) (hθ_lt : θ < (n : ℝ) / ((n : ℝ) - 1))
    (hmean : ∀ ε : ℝ, 0 < ε → ∃ K Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ M Q : ℕ, u_scale + 3 ≤ M → 1 ≤ Q →
        (u_scale : ℝ) * ((Q * M : ℕ) : ℝ) ^ n ≤ Z ^ θ →
          (∑ p ∈ RHTower.Sieve.bigPrimeSet M (Q * M), ‖twistedMoebiusSum W χ {p} Z‖ ^ 2) ≤
            K * Z ^ (θ + 1 + ε))
    {β C_β : ℝ} (hβ : (1 : ℝ) / 2 ≤ β) (hC_β : 0 < C_β)
    (hbase : ∀ X : ℝ, 0 < X → ‖twistedMoebiusSum W χ ∅ X‖ ≤ C_β * X ^ β)
    {b' : ℝ} (hb' : max (positiveFormBoundary n θ) (β * (1 - θ / n)) < b') :
    ∃ K' Z₁ : ℝ, 1 ≤ Z₁ ∧ ∀ Z : ℝ, Z₁ ≤ Z → ‖twistedMoebiusSum W χ ∅ Z‖ ≤ K' * Z ^ b' := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := by linarith
  set α : ℝ := θ / n
  have hα_pos : 0 < α := div_pos hθ hn_pos
  have hα_lt1 : α < 1 := by
    have h1 : θ * ((n : ℝ) - 1) < n := (lt_div_iff₀ (by linarith)).mp hθ_lt
    simp only [α]
    rw [div_lt_one hn_pos]
    nlinarith
  set ε : ℝ := (b' - max (positiveFormBoundary n θ) (β * (1 - α))) / 2
  have hε : 0 < ε := by simp only [ε, α]; linarith
  obtain ⟨K, Z₀, hZ₀, hK⟩ := hmean ε hε
  set Q : ℕ := ⌈Real.exp (2 * RHTower.Sieve.mertensFirstConst + 1)⌉₊ + 1
  have hQ1 : 1 ≤ Q := by omega
  have hQ_log : 1 ≤ Real.log Q - 2 * RHTower.Sieve.mertensFirstConst := by
    have hexp_le : Real.exp (2 * RHTower.Sieve.mertensFirstConst + 1) ≤ (Q : ℝ) := by
      simp only [Q]
      push_cast
      linarith [Nat.le_ceil (Real.exp (2 * RHTower.Sieve.mertensFirstConst + 1))]
    have hlog := Real.log_le_log (Real.exp_pos _) hexp_le
    rw [Real.log_exp] at hlog
    linarith
  have hus_pos : (0 : ℝ) < u_scale := by exact_mod_cast hu_scale
  set R_sc : ℝ := ((Q + 1 : ℕ) : ℝ) * (u_scale : ℝ) ^ (1 / (n : ℝ))
  have hR_ge2 : 2 ≤ R_sc := by
    have h1 : (2 : ℝ) ≤ ((Q + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ Q + 1)
    have h2 : (1 : ℝ) ≤ (u_scale : ℝ) ^ (1 / (n : ℝ)) :=
      Real.one_le_rpow (by exact_mod_cast hu_scale) (by positivity)
    nlinarith
  have hR_pos : 0 < R_sc := by linarith
  -- Choose `Z₁` large enough so `Z^α / R_sc ≥ u_scale + 4` and `log Z ≤ Z^ε`.
  have hlim_pow : Tendsto (fun Z : ℝ => Z ^ α / R_sc) atTop atTop :=
    (tendsto_rpow_atTop hα_pos).atTop_div_const hR_pos
  have hlim_log : Tendsto (fun Z : ℝ => Real.log Z / Z ^ ε) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hε).tendsto_div_nhds_zero
  have hev1 : ∀ᶠ Z : ℝ in atTop, ((u_scale + 4 : ℕ) : ℝ) ≤ Z ^ α / R_sc :=
    hlim_pow.eventually_ge_atTop _
  have hev2 : ∀ᶠ Z : ℝ in atTop, Real.log Z / Z ^ ε < 1 :=
    hlim_log.eventually (gt_mem_nhds one_pos)
  obtain ⟨Z₁_raw, hZ₁_raw⟩ := eventually_atTop.mp (hev1.and (hev2.and (eventually_ge_atTop (max Z₀ 3))))
  set Z₁ : ℝ := max 3 Z₁_raw
  set K_sq : ℝ := 4 * R_sc * max K 1 + 32 * C_β ^ 2 * (2 * R_sc) ^ (2 * β)
  have hK_sq_pos : 0 < K_sq := by positivity
  refine ⟨Real.sqrt K_sq, Z₁, le_trans (by norm_num) (le_max_left 3 Z₁_raw), fun Z hZ => ?_⟩
  obtain ⟨hM_big, hlog_lt, hZZ₀3⟩ := hZ₁_raw Z ((le_max_right 3 Z₁_raw).trans hZ)
  have hZ3 : 3 ≤ Z := (le_max_right Z₀ 3).trans hZZ₀3
  have hZZ₀ : Z₀ ≤ Z := (le_max_left Z₀ 3).trans hZZ₀3
  have hZ1 : 1 ≤ Z := by linarith
  have hZ_pos : 0 < Z := by linarith
  have hlogZ : Real.log Z ≤ Z ^ ε :=
    (div_lt_one (Real.rpow_pos_of_pos hZ_pos ε)).mp hlog_lt |>.le
  set M : ℕ := ⌊Z ^ α / R_sc⌋₊
  have hM_ge : u_scale + 4 ≤ M := Nat.le_floor hM_big
  have hM_u3 : u_scale + 3 ≤ M := by omega
  have hM3 : 3 ≤ M := by omega
  have hM_upper : (M : ℝ) ≤ Z ^ α / R_sc := Nat.floor_le (by positivity)
  have hM_lower : Z ^ α / (2 * R_sc) ≤ (M : ℝ) := by
    have hlt : Z ^ α / R_sc < (M : ℝ) + 1 := Nat.lt_floor_add_one (Z ^ α / R_sc)
    have h4 : (4 : ℝ) ≤ Z ^ α / R_sc := by
      have : (4 : ℝ) ≤ ((u_scale + 4 : ℕ) : ℝ) := by exact_mod_cast (by omega : 4 ≤ u_scale + 4)
      linarith
    have hdiv2 : Z ^ α / (2 * R_sc) = (Z ^ α / R_sc) / 2 := by ring
    linarith
  have hM_le_Z : (M : ℝ) ≤ Z := by
    calc (M : ℝ) ≤ Z ^ α / R_sc := hM_upper
      _ ≤ Z ^ α / 1 := div_le_div_of_nonneg_left (by positivity) one_pos (by linarith)
      _ = Z ^ α := div_one _
      _ ≤ Z ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hZ1 hα_lt1.le
      _ = Z := Real.rpow_one Z
  -- Twist budget check: `u_scale * (Q * M)^n ≤ Z^θ`.
  have hQM_le : (u_scale : ℝ) * ((Q * M : ℕ) : ℝ) ^ n ≤ Z ^ θ := by
    have hQM : ((Q * M : ℕ) : ℝ) ≤ Z ^ α / (u_scale : ℝ) ^ (1 / (n : ℝ)) := by
      push_cast
      have hQ_le : (Q : ℝ) ≤ ((Q + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_succ Q)
      calc (Q : ℝ) * (M : ℝ)
          ≤ ((Q + 1 : ℕ) : ℝ) * (Z ^ α / R_sc) :=
            mul_le_mul hQ_le hM_upper (by positivity) (by positivity)
        _ = Z ^ α / (u_scale : ℝ) ^ (1 / (n : ℝ)) := by
            simp only [R_sc]
            have hQ1_ne : ((Q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
            field_simp
    have hpow := pow_le_pow_left₀ (by positivity) hQM n
    rw [div_pow, ← Real.rpow_natCast ((u_scale : ℝ) ^ (1 / (n : ℝ))) n,
      ← Real.rpow_mul hus_pos.le, one_div_mul_cancel hn_pos.ne', Real.rpow_one,
      ← Real.rpow_natCast (Z ^ α) n, ← Real.rpow_mul hZ_pos.le] at hpow
    have hαn : α * (n : ℝ) = θ := div_mul_cancel₀ θ hn_pos.ne'
    rw [hαn] at hpow
    rw [mul_comm]
    exact (le_div_iff₀ hus_pos).mp hpow
  -- Prime count lower bound in `(M, Q * M]`.
  set P := RHTower.Sieve.bigPrimeSet M (Q * M)
  have hlogM_pos : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hlogM_le : Real.log M ≤ Z ^ ε :=
    (Real.log_le_log (by positivity) hM_le_Z).trans hlogZ
  have hcard_ge : Z ^ (α - ε) / (2 * R_sc) ≤ (P.card : ℝ) := by
    have hc := RHTower.Sieve.card_bigPrimeSet_ratio_ge hM3 hQ1
    have h1 : (M : ℝ) / Real.log M ≤ (P.card : ℝ) := by
      calc (M : ℝ) / Real.log M = 1 * (M : ℝ) / Real.log M := by ring
        _ ≤ (Real.log Q - 2 * RHTower.Sieve.mertensFirstConst) * (M : ℝ) / Real.log M :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hQ_log (by positivity)) hlogM_pos.le
        _ ≤ (P.card : ℝ) := hc
    have h2 : Z ^ (α - ε) / (2 * R_sc) ≤ (M : ℝ) / Real.log M := by
      rw [Real.rpow_sub hZ_pos]
      calc Z ^ α / Z ^ ε / (2 * R_sc)
          = (Z ^ α / (2 * R_sc)) / Z ^ ε := by ring
        _ ≤ (M : ℝ) / Real.log M :=
            div_le_div₀ (by positivity) hM_lower hlogM_pos hlogM_le
    exact h2.trans h1
  have hcard_pos : 0 < (P.card : ℝ) := lt_of_lt_of_le (by positivity) hcard_ge
  -- Pointwise squared bound for each prime `p ∈ P`.
  have hp_sq : ∀ p ∈ P, ‖twistedMoebiusSum W χ ∅ Z‖ ^ 2 ≤
      2 * ‖twistedMoebiusSum W χ {p} Z‖ ^ 2 + 32 * C_β ^ 2 * (Z / (M : ℝ)) ^ (2 * β) := by
    intro p hpP
    have hp_mem := Finset.mem_filter.mp hpP
    have hp_prime : p.Prime := hp_mem.2
    have hp_gtM : (M : ℝ) ≤ p := by
      have := (Finset.mem_Icc.mp hp_mem.1).1
      exact_mod_cast (by omega : M ≤ p)
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp_prime.pos
    have hsplit := twistedMoebiusSum_eq_sub_insert hW hχ (fun _ hq => by simp at hq) hp_prime
      (Finset.not_mem_empty p) (hχ_mul p hp_prime) hZ_pos
    simp only [Finset.insert_empty_eq] at hsplit
    have htail_bd := norm_twistedMoebiusSum_le_of_base_le hW hχ hχ_mul
      (by linarith : 0 < β) hC_β.le hbase (S := {p}) (by simp [hp_prime]) (div_pos hZ_pos hp_pos)
    rw [Finset.prod_singleton] at htail_bd
    have h4 := inv_one_sub_prime_rpow_neg_le_four hp_prime hβ
    have hZp_le : (Z / (p : ℝ)) ^ β ≤ (Z / (M : ℝ)) ^ β :=
      Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_left hZ_pos.le (by positivity) hp_gtM) (by linarith)
    have htail2 : ‖χ p * twistedMoebiusSum W χ {p} (Z / p)‖ ≤
        4 * C_β * (Z / (M : ℝ)) ^ β := by
      rw [norm_mul]
      calc ‖χ p‖ * ‖twistedMoebiusSum W χ {p} (Z / p)‖
          ≤ 1 * (C_β * (1 - (p : ℝ) ^ (-β))⁻¹ * (Z / (p : ℝ)) ^ β) :=
            mul_le_mul (hχ p) htail_bd (norm_nonneg _) zero_le_one
        _ ≤ 1 * (C_β * 4 * (Z / (M : ℝ)) ^ β) := by
            rw [one_mul, one_mul]
            exact mul_le_mul (mul_le_mul_of_nonneg_left h4 hC_β.le) hZp_le
              (by positivity) (by positivity)
        _ = 4 * C_β * (Z / (M : ℝ)) ^ β := by ring
    have htri : ‖twistedMoebiusSum W χ ∅ Z‖ ≤
        ‖twistedMoebiusSum W χ {p} Z‖ + 4 * C_β * (Z / (M : ℝ)) ^ β := by
      rw [hsplit]
      exact (norm_sub_le _ _).trans (add_le_add_right htail2 _)
    have hsq_ineq : ∀ x y : ℝ, (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := fun x y => by
      nlinarith [sq_nonneg (x - y)]
    calc ‖twistedMoebiusSum W χ ∅ Z‖ ^ 2
        ≤ (‖twistedMoebiusSum W χ {p} Z‖ + 4 * C_β * (Z / (M : ℝ)) ^ β) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ ≤ 2 * ‖twistedMoebiusSum W χ {p} Z‖ ^ 2 +
            2 * (4 * C_β * (Z / (M : ℝ)) ^ β) ^ 2 := hsq_ineq _ _
      _ = 2 * ‖twistedMoebiusSum W χ {p} Z‖ ^ 2 +
            32 * C_β ^ 2 * (Z / (M : ℝ)) ^ (2 * β) := by
          rw [mul_pow, ← Real.rpow_natCast ((Z / (M : ℝ)) ^ β) 2,
            ← Real.rpow_mul (by positivity)]
          push_cast
          ring
  -- Average over `p ∈ P`.
  have hsum_P := Finset.sum_le_sum hp_sq
  simp only [Finset.sum_const, Finset.sum_add_distrib, ← Finset.mul_sum, nsmul_eq_mul] at hsum_P
  have hmean_Z := hK Z hZZ₀ M Q hM_u3 hQ1 hQM_le
  have hterm1 : 2 * (∑ p ∈ P, ‖twistedMoebiusSum W χ {p} Z‖ ^ 2) / (P.card : ℝ) ≤
      4 * R_sc * max K 1 * Z ^ (2 * b') := by
    have hK_le : K ≤ max K 1 := le_max_left K 1
    have hK1_pos : (0 : ℝ) < max K 1 := lt_of_lt_of_le one_pos (le_max_right K 1)
    have hnum_le : 2 * (∑ p ∈ P, ‖twistedMoebiusSum W χ {p} Z‖ ^ 2) ≤
        2 * (max K 1 * Z ^ (θ + 1 + ε)) := by
      refine mul_le_mul_of_nonneg_left (hmean_Z.trans ?_) (by norm_num)
      exact mul_le_mul_of_nonneg_right hK_le (by positivity)
    have hexp_le : θ + 1 + ε - (α - ε) ≤ 2 * b' := by
      have hpfb : 2 * positiveFormBoundary n θ = 1 + (1 - 1 / (n : ℝ)) * θ := by
        unfold positiveFormBoundary; field_simp
      have hα_eq : θ - α = (1 - 1 / (n : ℝ)) * θ := by simp only [α]; ring
      have hmax1 : positiveFormBoundary n θ ≤ max (positiveFormBoundary n θ) (β * (1 - α)) :=
        le_max_left _ _
      simp only [ε]
      linarith
    calc 2 * (∑ p ∈ P, ‖twistedMoebiusSum W χ {p} Z‖ ^ 2) / (P.card : ℝ)
        ≤ 2 * (max K 1 * Z ^ (θ + 1 + ε)) / (Z ^ (α - ε) / (2 * R_sc)) :=
          div_le_div₀ (by positivity) hnum_le (by positivity) hcard_ge
      _ = 4 * R_sc * max K 1 * (Z ^ (θ + 1 + ε) / Z ^ (α - ε)) := by ring
      _ = 4 * R_sc * max K 1 * Z ^ (θ + 1 + ε - (α - ε)) := by
          rw [← Real.rpow_sub hZ_pos]
      _ ≤ 4 * R_sc * max K 1 * Z ^ (2 * b') :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ1 hexp_le) (by positivity)
  have hterm2 : 32 * C_β ^ 2 * (Z / (M : ℝ)) ^ (2 * β) ≤
      32 * C_β ^ 2 * (2 * R_sc) ^ (2 * β) * Z ^ (2 * b') := by
    have hZM : Z / (M : ℝ) ≤ 2 * R_sc * Z ^ (1 - α) := by
      calc Z / (M : ℝ) ≤ Z / (Z ^ α / (2 * R_sc)) :=
            div_le_div_of_nonneg_left hZ_pos.le (by positivity) hM_lower
        _ = 2 * R_sc * (Z / Z ^ α) := by rw [div_div_eq_mul_div]; ring
        _ = 2 * R_sc * Z ^ (1 - α) := by
            conv_lhs => rw [← Real.rpow_one Z]
            rw [← Real.rpow_sub hZ_pos]
    have hpow : (Z / (M : ℝ)) ^ (2 * β) ≤ (2 * R_sc) ^ (2 * β) * Z ^ (2 * β * (1 - α)) := by
      calc (Z / (M : ℝ)) ^ (2 * β)
          ≤ (2 * R_sc * Z ^ (1 - α)) ^ (2 * β) :=
            Real.rpow_le_rpow (by positivity) hZM (by linarith)
        _ = (2 * R_sc) ^ (2 * β) * Z ^ (2 * β * (1 - α)) := by
            rw [Real.mul_rpow (by positivity) (by positivity),
              ← Real.rpow_mul hZ_pos.le, mul_comm (1 - α) (2 * β)]
    have hexp_le : 2 * β * (1 - α) ≤ 2 * b' := by
      have hmax2 : β * (1 - α) ≤ max (positiveFormBoundary n θ) (β * (1 - α)) := le_max_right _ _
      linarith
    calc 32 * C_β ^ 2 * (Z / (M : ℝ)) ^ (2 * β)
        ≤ 32 * C_β ^ 2 * ((2 * R_sc) ^ (2 * β) * Z ^ (2 * β * (1 - α))) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 32 * C_β ^ 2 * (2 * R_sc) ^ (2 * β) * Z ^ (2 * β * (1 - α)) := by ring
      _ ≤ 32 * C_β ^ 2 * (2 * R_sc) ^ (2 * β) * Z ^ (2 * b') :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ1 hexp_le) (by positivity)
  have hsq_final : ‖twistedMoebiusSum W χ ∅ Z‖ ^ 2 ≤ K_sq * Z ^ (2 * b') := by
    have hdiv : ‖twistedMoebiusSum W χ ∅ Z‖ ^ 2 ≤
        2 * (∑ p ∈ P, ‖twistedMoebiusSum W χ {p} Z‖ ^ 2) / (P.card : ℝ) +
          32 * C_β ^ 2 * (Z / (M : ℝ)) ^ (2 * β) := by
      rw [← le_div_iff₀' hcard_pos] at hsum_P
      have hsimp : (2 * ∑ p ∈ P, ‖twistedMoebiusSum W χ {p} Z‖ ^ 2 +
          (P.card : ℝ) * (32 * C_β ^ 2 * (Z / (M : ℝ)) ^ (2 * β))) / (P.card : ℝ) =
          2 * (∑ p ∈ P, ‖twistedMoebiusSum W χ {p} Z‖ ^ 2) / (P.card : ℝ) +
            32 * C_β ^ 2 * (Z / (M : ℝ)) ^ (2 * β) := by
        rw [add_div, mul_div_cancel_left₀ _ hcard_pos.ne']
      rwa [hsimp] at hsum_P
    calc ‖twistedMoebiusSum W χ ∅ Z‖ ^ 2
        ≤ 4 * R_sc * max K 1 * Z ^ (2 * b') +
            32 * C_β ^ 2 * (2 * R_sc) ^ (2 * β) * Z ^ (2 * b') :=
          hdiv.trans (add_le_add hterm1 hterm2)
      _ = K_sq * Z ^ (2 * b') := by simp only [K_sq]; ring
  have hsqrt := Real.sqrt_le_sqrt hsq_final
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hK_sq_pos.le,
    show Z ^ (2 * b') = (Z ^ b') ^ 2 by
      rw [← Real.rpow_natCast (Z ^ b') 2, ← Real.rpow_mul hZ_pos.le]; push_cast; ring,
    Real.sqrt_sq (by positivity)] at hsqrt
  exact hsqrt

/-- **One-step zero-abscissa theorem.** Any generic prime-window mean square at `θ > 0` forces an
abstract abscissa `Θ ∈ [1/2, 1]` satisfying the upper/lower signal laws to obey
`Θ ≤ min(1, positiveFormBoundary n θ)` immediately. -/
theorem abscissa_le_positiveFormBoundary_of_primeWindow_meanSquare
    {W : ℂ → ℂ} (hW : IsSmoothCutoff W)
    {χ : ℕ → ℂ} (hχ : ∀ m : ℕ, ‖χ m‖ ≤ 1)
    (hχ_mul : ∀ p : ℕ, p.Prime → ∀ k : ℕ, ¬ p ∣ k → χ (p * k) = χ p * χ k)
    {n u_scale : ℕ} (hn : 2 ≤ n) (hu_scale : 1 ≤ u_scale)
    {Θ : ℝ} (hΘ_half : (1 : ℝ) / 2 ≤ Θ) (hΘ_one : Θ ≤ 1)
    (hupper : ∀ β : ℝ, Θ < β → β < Θ + 1 → β ≤ 2 →
      ∃ C_β : ℝ, 0 < C_β ∧ ∀ X : ℝ, 0 < X → ‖twistedMoebiusSum W χ ∅ X‖ ≤ C_β * X ^ β)
    (hlower : ∀ b K Z₁ : ℝ, b < Θ → 1 ≤ Z₁ →
      (∀ Z : ℝ, Z₁ ≤ Z → ‖twistedMoebiusSum W χ ∅ Z‖ ≤ K * Z ^ b) → False)
    {θ : ℝ} (hθ : 0 < θ)
    (hmean : ∀ ε : ℝ, 0 < ε → ∃ K Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ M Q : ℕ, u_scale + 3 ≤ M → 1 ≤ Q →
        (u_scale : ℝ) * ((Q * M : ℕ) : ℝ) ^ n ≤ Z ^ θ →
          (∑ p ∈ RHTower.Sieve.bigPrimeSet M (Q * M), ‖twistedMoebiusSum W χ {p} Z‖ ^ 2) ≤
            K * Z ^ (θ + 1 + ε)) :
    Θ ≤ min 1 (positiveFormBoundary n θ) := by
  refine le_min hΘ_one ?_
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rcases le_or_gt ((n : ℝ) / ((n : ℝ) - 1)) θ with hbig | hlt
  · have h1 : 1 ≤ positiveFormBoundary n θ := by
      have h0 : positiveFormBoundary n ((n : ℝ) / ((n : ℝ) - 1)) = 1 := by
        unfold positiveFormBoundary
        have hne1 : (n : ℝ) - 1 ≠ 0 := by linarith
        have hne2 : (n : ℝ) ≠ 0 := by linarith
        field_simp
        ring
      rw [← h0]
      exact (positiveFormBoundary_strictMono (by linarith : (1 : ℝ) < n)).monotone hbig
    exact hΘ_one.trans h1
  · by_contra hcon
    rw [not_le] at hcon
    have hα_pos : 0 < θ / (n : ℝ) := div_pos hθ (by linarith)
    have hα_lt1 : θ / (n : ℝ) < 1 := by
      have h1 : θ * ((n : ℝ) - 1) < n := (lt_div_iff₀ (by linarith)).mp hlt
      rw [div_lt_one (by linarith)]
      nlinarith
    have hΘ_shrink : Θ * (1 - θ / (n : ℝ)) < Θ := by nlinarith
    set M_bd : ℝ := max (positiveFormBoundary n θ) (Θ * (1 - θ / (n : ℝ)))
    have hM_lt : M_bd < Θ := max_lt hcon hΘ_shrink
    set gap : ℝ := Θ - M_bd
    have hgap : 0 < gap := sub_pos.mpr hM_lt
    set δ : ℝ := min (1 / 2) (gap / 4)
    have hδ_pos : 0 < δ := lt_min (by norm_num) (by positivity)
    have hδ_lt1 : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
    have hδ_gap : δ ≤ gap / 4 := min_le_right _ _
    set β : ℝ := Θ + δ
    obtain ⟨C_β, hC_β, hbase⟩ := hupper β (by simp [β]; linarith) (by simp [β]; linarith)
      (by simp [β]; linarith [min_le_left (1 / 2) (gap / 4)])
    set b' : ℝ := Θ - gap / 2
    have hb'_gt : max (positiveFormBoundary n θ) (β * (1 - θ / (n : ℝ))) < b' := by
      refine max_lt ?_ ?_
      · have : positiveFormBoundary n θ ≤ M_bd := le_max_left _ _
        simp only [b', gap]; linarith
      · have h1 : Θ * (1 - θ / (n : ℝ)) ≤ M_bd := le_max_right _ _
        have h2 : β * (1 - θ / (n : ℝ)) = Θ * (1 - θ / (n : ℝ)) + δ * (1 - θ / (n : ℝ)) := by
          simp only [β]; ring
        have h3 : δ * (1 - θ / (n : ℝ)) ≤ δ := by nlinarith
        simp only [b', gap]; linarith
    obtain ⟨K', Z₁, hZ₁, hK'⟩ := exists_signal_drop_of_primeWindow_meanSquare hW hχ hχ_mul
      hn hu_scale hθ hlt hmean (by simp [β]; linarith) hC_β hbase hb'_gt
    exact hlower b' K' Z₁ (by simp [b']; linarith) hZ₁ hK'

/-! ### Exact minimum of the principal `n`-th-power twist subfamily -/

/-- A twist mean square `F θ Z` is of the generic size at exponent `θ` if
`F θ Z = O_ε(Z^{θ + 1 + ε})` for every `ε > 0`. -/
def IsGenericMeanSquare (F : ℝ → ℝ → ℝ) (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → F θ Z ≤ K * Z ^ (θ + 1 + ε)

/-- Mean square of `W`-smoothed Möbius sums over the principal `n`-th-power twists `a^n ≤ Z^θ`. -/
def principalTwistMeanSquare (W : ℂ → ℂ) (n : ℕ) (θ Z : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 ⌊Z ^ (θ / n)⌋₊,
    ‖twistedMoebiusSum W (fun _ => 1) a.primeFactors Z‖ ^ 2

theorem riemannHypothesis_iff_zetaZeroAbscissa_eq_half :
    RiemannHypothesis ↔ RHTower.zetaZeroAbscissa = 1 / 2 := by
  constructor
  · intro hRH
    have hXi := RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mp hRH
    have hzf := (RHTower.suzukiZetaZeroFreeRightOf_iff_xiZeroHalfPlaneBound le_rfl).mpr hXi
    apply le_antisymm _ RHTower.half_le_zetaZeroAbscissa
    by_contra hgt
    rw [not_le] at hgt
    obtain ⟨ρ, hzero, hre⟩ := RHTower.exists_zetaZero_lt_re hgt
    have hρ1 : ρ ≠ 1 := fun h1 => riemannZeta_one_ne_zero (h1 ▸ hzero)
    exact hzf ρ (by linarith) hρ1 hzero
  · intro hEq
    refine RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr ?_
    refine (RHTower.suzukiZetaZeroFreeRightOf_iff_xiZeroHalfPlaneBound le_rfl).mp ?_
    intro s hs _
    exact RHTower.riemannZeta_ne_zero_of_zetaZeroAbscissa_lt (by linarith)

/-- General closed-form characterization of `principalTwistMeanSquare W n` for any smooth cutoff
`W` whose `S = ∅` sum reads an abscissa `Θ ∈ [1/2, 1]`. -/
theorem principalTwistGenericSet_eq_of_abscissa {W : ℂ → ℂ} (hW : IsSmoothCutoff W)
    {n : ℕ} (hn : 2 ≤ n) {Θ : ℝ} (hΘ_half : (1 : ℝ) / 2 ≤ Θ) (hΘ_one : Θ ≤ 1)
    (hupper : ∀ β : ℝ, Θ < β → β < Θ + 1 → β ≤ 2 →
      ∃ C_β : ℝ, 0 < C_β ∧ ∀ X : ℝ, 0 < X → ‖twistedMoebiusSum W (fun _ => 1) ∅ X‖ ≤ C_β * X ^ β)
    (hlower : ∀ b K Z₁ : ℝ, b < Θ → 1 ≤ Z₁ →
      (∀ Z : ℝ, Z₁ ≤ Z → ‖twistedMoebiusSum W (fun _ => 1) ∅ Z‖ ≤ K * Z ^ b) → False) :
    {θ : ℝ | 0 ≤ θ ∧ IsGenericMeanSquare (principalTwistMeanSquare W n) θ} =
      Set.Ici (positiveFormTheta n Θ) := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := by linarith
  ext θ
  simp only [Set.mem_setOf_eq, Set.mem_Ici]
  constructor
  · rintro ⟨hθ0, hgen⟩
    rcases eq_or_lt_of_le hθ0 with rfl | hθ_pos
    · -- At `θ = 0`, the single term `a = 1` forces `Θ = 1/2`, so `positiveFormTheta n Θ = 0`.
      have hΘ_eq : Θ = 1 / 2 := by
        apply le_antisymm _ hΘ_half
        by_contra hgt
        rw [not_le] at hgt
        set b : ℝ := (1 / 2 + Θ) / 2
        have hb_gt : 1 / 2 < b := by simp [b]; linarith
        have hb_lt : b < Θ := by simp [b]; linarith
        obtain ⟨K, Z₀, hZ₀, hK⟩ := hgen (2 * b - 1) (by linarith)
        have hbd : ∀ Z : ℝ, Z₀ ≤ Z →
            ‖twistedMoebiusSum W (fun _ => 1) ∅ Z‖ ≤ Real.sqrt (max K 0) * Z ^ b := by
          intro Z hZ
          have hZ1 : 1 ≤ Z := hZ₀.trans hZ
          have hZ_pos : 0 < Z := by linarith
          have h1_mem : (1 : ℕ) ∈ Finset.Icc 1 ⌊Z ^ ((0 : ℝ) / n)⌋₊ := by
            rw [zero_div, Real.rpow_zero]
            simp
          have hterm_le : ‖twistedMoebiusSum W (fun _ => 1) ∅ Z‖ ^ 2 ≤
              principalTwistMeanSquare W n 0 Z := by
            unfold principalTwistMeanSquare
            have := Finset.single_le_sum (f := fun a : ℕ =>
              ‖twistedMoebiusSum W (fun _ => 1) a.primeFactors Z‖ ^ 2)
              (fun _ _ => sq_nonneg _) h1_mem
            simp at this
            exact this
          have hsq : ‖twistedMoebiusSum W (fun _ => 1) ∅ Z‖ ^ 2 ≤
              max K 0 * (Z ^ b) ^ 2 := by
            calc ‖twistedMoebiusSum W (fun _ => 1) ∅ Z‖ ^ 2
                ≤ K * Z ^ ((0 : ℝ) + 1 + (2 * b - 1)) := hterm_le.trans (hK Z hZ)
              _ ≤ max K 0 * Z ^ (2 * b) := by
                  rw [show (0 : ℝ) + 1 + (2 * b - 1) = 2 * b by ring]
                  exact mul_le_mul_of_nonneg_right (le_max_left K 0) (by positivity)
              _ = max K 0 * (Z ^ b) ^ 2 := by
                  rw [← Real.rpow_natCast (Z ^ b) 2, ← Real.rpow_mul hZ_pos.le]
                  push_cast; ring
          have hs := Real.sqrt_le_sqrt hsq
          rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (le_max_right K 0),
            Real.sqrt_sq (by positivity)] at hs
        exact hlower b (Real.sqrt (max K 0)) Z₀ hb_lt hZ₀ hbd
      rw [hΘ_eq]
      unfold positiveFormTheta
      norm_num
    · -- At `θ > 0`, prime-window amplification forces `Θ ≤ positiveFormBoundary n θ`.
      have hmean_primes : ∀ ε : ℝ, 0 < ε → ∃ K Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
          ∀ M Q : ℕ, 1 + 3 ≤ M → 1 ≤ Q →
            ((1 : ℕ) : ℝ) * ((Q * M : ℕ) : ℝ) ^ n ≤ Z ^ θ →
              (∑ p ∈ RHTower.Sieve.bigPrimeSet M (Q * M),
                ‖twistedMoebiusSum W (fun _ => 1) {p} Z‖ ^ 2) ≤ K * Z ^ (θ + 1 + ε) := by
        intro ε hε
        obtain ⟨K, Z₀, hZ₀, hK⟩ := hgen ε hε
        refine ⟨K, Z₀, hZ₀, fun Z hZ M Q hM hQ hQM => ?_⟩
        have hZ1 : 1 ≤ Z := hZ₀.trans hZ
        have hQM_le_floor : Q * M ≤ ⌊Z ^ (θ / n)⌋₊ := by
          refine Nat.le_floor ?_
          have h1 : (((Q * M : ℕ) : ℝ) ^ n) ^ (1 / (n : ℝ)) ≤ (Z ^ θ) ^ (1 / (n : ℝ)) :=
            Real.rpow_le_rpow (by positivity) (by push_cast at hQM; linarith) (by positivity)
          rw [← Real.rpow_natCast ((Q * M : ℕ) : ℝ) n, ← Real.rpow_mul (by positivity),
            mul_one_div_cancel hn_pos.ne', Real.rpow_one, ← Real.rpow_mul (by linarith),
            mul_one_div] at h1
          exact h1
        have hsub : RHTower.Sieve.bigPrimeSet M (Q * M) ⊆ Finset.Icc 1 ⌊Z ^ (θ / n)⌋₊ := by
          intro p hp
          obtain ⟨hIcc, _⟩ := Finset.mem_filter.mp hp
          obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hIcc
          exact Finset.mem_Icc.mpr ⟨by omega, hhi.trans hQM_le_floor⟩
        have hsum_eq : (∑ p ∈ RHTower.Sieve.bigPrimeSet M (Q * M),
            ‖twistedMoebiusSum W (fun _ => 1) {p} Z‖ ^ 2) =
            ∑ p ∈ RHTower.Sieve.bigPrimeSet M (Q * M),
              ‖twistedMoebiusSum W (fun _ => 1) p.primeFactors Z‖ ^ 2 := by
          refine Finset.sum_congr rfl fun p hp => ?_
          have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
          rw [hp_prime.primeFactors]
        rw [hsum_eq]
        exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _).trans
          (hK Z hZ)
      have hΘ_le := abscissa_le_positiveFormBoundary_of_primeWindow_meanSquare hW
        (fun _ => by simp) (fun _ _ _ _ => by simp) hn le_rfl hΘ_half hΘ_one hupper hlower
        hθ_pos hmean_primes
      have hΘ_pfb : Θ ≤ positiveFormBoundary n θ := hΘ_le.trans (min_le_right _ _)
      have hmono := (positiveFormTheta_strictMono (by linarith : (1 : ℝ) < n)).monotone hΘ_pfb
      rwa [positiveFormTheta_positiveFormBoundary hn_pos.ne' (by linarith)] at hmono
  · -- Sufficiency: `θ ≥ positiveFormTheta n Θ` gives `IsGenericMeanSquare`.
    intro hθ_ge
    have hθ0 : 0 ≤ θ := by
      have h0 : 0 ≤ positiveFormTheta n Θ := by
        unfold positiveFormTheta
        exact mul_nonneg (div_nonneg (by positivity) (by linarith)) (by linarith)
      linarith
    refine ⟨hθ0, fun ε hε => ?_⟩
    set δ : ℝ := min (1 / 2) (ε / 6)
    have hδ_pos : 0 < δ := lt_min (by norm_num) (by positivity)
    have hδ_lt1 : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
    have hδ_le : δ ≤ ε / 6 := min_le_right _ _
    set η : ℝ := ε / (4 * (θ + 1))
    have hη_pos : 0 < η := div_pos hε (by positivity)
    set b : ℝ := Θ + δ
    obtain ⟨C_b, hC_b, hbase⟩ := hupper b (by simp [b]; linarith) (by simp [b]; linarith)
      (by simp [b]; linarith [min_le_left ((1 : ℝ) / 2) (ε / 6)])
    obtain ⟨C_η, hC_η, heuler⟩ := exists_eulerProd_primeFactors_le_rpow hη_pos
    refine ⟨(C_b * C_η) ^ 2, 1, le_rfl, fun Z hZ => ?_⟩
    have hZ_pos : 0 < Z := by linarith
    have hexp_budget : θ / n + 2 * Θ ≤ θ + 1 := by
      have hpft : 2 * (n : ℝ) / ((n : ℝ) - 1) * (Θ - 1 / 2) ≤ θ := hθ_ge
      have hmul : 2 * (n : ℝ) * (Θ - 1 / 2) ≤ θ * ((n : ℝ) - 1) := by
        rwa [div_mul_eq_mul_div, div_le_iff₀ (by linarith)] at hpft
      rw [show θ / (n : ℝ) + 2 * Θ = (θ + 2 * n * Θ) / n by field_simp, div_le_iff₀ hn_pos]
      nlinarith
    have hterm_le : ∀ a ∈ Finset.Icc 1 ⌊Z ^ (θ / n)⌋₊,
        ‖twistedMoebiusSum W (fun _ => 1) a.primeFactors Z‖ ^ 2 ≤
          (C_b * C_η) ^ 2 * Z ^ (2 * b + 2 * θ * η) := by
      intro a ha
      obtain ⟨ha1, ha_hi⟩ := Finset.mem_Icc.mp ha
      have ha_le_Zθ : (a : ℝ) ≤ Z ^ θ := by
        have h1 : (a : ℝ) ≤ Z ^ (θ / n) := (Nat.le_floor_iff (by positivity)).mp ha_hi
        calc (a : ℝ) ≤ Z ^ (θ / n) := h1
          _ ≤ Z ^ θ := Real.rpow_le_rpow_of_exponent_le hZ
              (div_le_self hθ0 (by linarith))
      have haη : (a : ℝ) ^ η ≤ Z ^ (θ * η) := by
        calc (a : ℝ) ^ η ≤ (Z ^ θ) ^ η := Real.rpow_le_rpow (by positivity) ha_le_Zθ hη_pos.le
          _ = Z ^ (θ * η) := (Real.rpow_mul hZ_pos.le θ η).symm
      have h1 := norm_twistedMoebiusSum_le_of_base_le hW (fun _ => by simp)
        (fun _ _ _ _ => by simp) (by simp [b]; linarith) hC_b.le hbase
        (fun p hp => Nat.prime_of_mem_primeFactors hp) hZ_pos
      have h2 := heuler b (by simp [b]; linarith) a ha1
      have hnorm : ‖twistedMoebiusSum W (fun _ => 1) a.primeFactors Z‖ ≤
          C_b * C_η * Z ^ (b + θ * η) := by
        calc ‖twistedMoebiusSum W (fun _ => 1) a.primeFactors Z‖
            ≤ C_b * (∏ p ∈ a.primeFactors, (1 - (p : ℝ) ^ (-b))⁻¹) * Z ^ b := h1
          _ ≤ C_b * (C_η * (a : ℝ) ^ η) * Z ^ b :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hC_b.le) (by positivity)
          _ ≤ C_b * (C_η * Z ^ (θ * η)) * Z ^ b :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left haη (by positivity)) (by positivity)
          _ = C_b * C_η * Z ^ (b + θ * η) := by
              rw [Real.rpow_add hZ_pos]; ring
      calc ‖twistedMoebiusSum W (fun _ => 1) a.primeFactors Z‖ ^ 2
          ≤ (C_b * C_η * Z ^ (b + θ * η)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        _ = (C_b * C_η) ^ 2 * Z ^ (2 * b + 2 * θ * η) := by
            rw [mul_pow, ← Real.rpow_natCast (Z ^ (b + θ * η)) 2, ← Real.rpow_mul hZ_pos.le]
            push_cast; ring
    have hcard : ((Finset.Icc 1 ⌊Z ^ (θ / n)⌋₊).card : ℝ) ≤ Z ^ (θ / n) := by
      rw [Nat.card_Icc, Nat.add_sub_cancel]
      exact Nat.floor_le (by positivity)
    have hexp_total : θ / n + (2 * b + 2 * θ * η) ≤ θ + 1 + ε := by
      have h2θη : 2 * θ * η ≤ ε / 2 := by
        simp only [η]
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      simp only [b]
      linarith
    calc principalTwistMeanSquare W n θ Z
        ≤ ∑ _a ∈ Finset.Icc 1 ⌊Z ^ (θ / n)⌋₊, (C_b * C_η) ^ 2 * Z ^ (2 * b + 2 * θ * η) :=
          Finset.sum_le_sum hterm_le
      _ = ((Finset.Icc 1 ⌊Z ^ (θ / n)⌋₊).card : ℝ) *
            ((C_b * C_η) ^ 2 * Z ^ (2 * b + 2 * θ * η)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Z ^ (θ / n) * ((C_b * C_η) ^ 2 * Z ^ (2 * b + 2 * θ * η)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (C_b * C_η) ^ 2 * Z ^ (θ / n + (2 * b + 2 * θ * η)) := by
          rw [← mul_assoc, mul_comm (Z ^ (θ / n)) _, mul_assoc, ← Real.rpow_add hZ_pos]
      _ ≤ (C_b * C_η) ^ 2 * Z ^ (θ + 1 + ε) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexp_total) (by positivity)

/-- **Closed-form generic twist set for the pole kernel.** -/
theorem principalTwistGenericSet_poleKernel (c : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    {θ : ℝ | 0 ≤ θ ∧ IsGenericMeanSquare (principalTwistMeanSquare (poleKernel c) n) θ} =
      Set.Ici ((n : ℝ) / ((n : ℝ) - 1) * (2 * RHTower.zetaZeroAbscissa - 1)) := by
  have heq : positiveFormTheta n RHTower.zetaZeroAbscissa =
      (n : ℝ) / ((n : ℝ) - 1) * (2 * RHTower.zetaZeroAbscissa - 1) := by
    unfold positiveFormTheta; ring
  rw [← heq]
  refine principalTwistGenericSet_eq_of_abscissa (isSmoothCutoff_poleKernel c) hn
    RHTower.half_le_zetaZeroAbscissa RHTower.zetaZeroAbscissa_le_one
    (fun β h1 h2 h3 => ?_) (fun b K Z₁ hb hZ₁ hK => ?_)
  · obtain ⟨C, hC, hbd⟩ := exists_signal_zetaKernel_le_of_zeroFree_strip
      RHTower.half_le_zetaZeroAbscissa RHTower.zetaZeroAbscissa_le_one
      (fun _ hz => RHTower.riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hz) c h1 h2 h3
    exact ⟨C, hC, fun X hX => by rw [← signal_zetaKernel_eq_twistedMoebiusSum c hX]; exact hbd X hX⟩
  · obtain ⟨ρ, hzero, hre⟩ := RHTower.exists_zetaZero_lt_re hb
    have hρ1 : ρ ≠ 1 := fun h1 => riemannZeta_one_ne_zero (h1 ▸ hzero)
    exact riemannZeta_ne_zero_of_signal_le (c := c) (b := b) (K := K) (Z₀ := Z₁)
      (hb.trans_le RHTower.zetaZeroAbscissa_le_one) (by linarith)
      (fun Z hZ => by rw [signal_zetaKernel_eq_twistedMoebiusSum c (by linarith)]; exact hK Z hZ)
      ρ hre hρ1 hzero

/-- **Closed-form generic twist set for the pole-free Gaussian kernel.** -/
theorem principalTwistGenericSet_gaussianKernel (c : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    {θ : ℝ | 0 ≤ θ ∧ IsGenericMeanSquare (principalTwistMeanSquare (gaussianKernel c) n) θ} =
      Set.Ici ((n : ℝ) / ((n : ℝ) - 1) * (2 * RHTower.zetaZeroAbscissa - 1)) := by
  have heq : positiveFormTheta n RHTower.zetaZeroAbscissa =
      (n : ℝ) / ((n : ℝ) - 1) * (2 * RHTower.zetaZeroAbscissa - 1) := by
    unfold positiveFormTheta; ring
  rw [← heq]
  refine principalTwistGenericSet_eq_of_abscissa (isSmoothCutoff_gaussianKernel c) hn
    RHTower.half_le_zetaZeroAbscissa RHTower.zetaZeroAbscissa_le_one
    (fun β h1 h2 h3 => ?_) (fun b K Z₁ hb hZ₁ hK => ?_)
  · obtain ⟨C, hC, hbd⟩ := exists_signal_zetaGaussianKernel_le_of_zeroFree
      RHTower.half_le_zetaZeroAbscissa RHTower.zetaZeroAbscissa_le_one
      (fun _ hz => RHTower.riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hz) c h1 h2 h3
    exact ⟨C, hC, fun X hX => by
      rw [← signal_zetaGaussianKernel_eq_twistedMoebiusSum c hX]; exact hbd X hX⟩
  · obtain ⟨ρ, hzero, hre⟩ := RHTower.exists_zetaZero_lt_re hb
    have hρ1 : ρ ≠ 1 := fun h1 => riemannZeta_one_ne_zero (h1 ▸ hzero)
    exact riemannZeta_ne_zero_of_signal_zetaGaussianKernel_le (c := c) (b := b) (K := K) (Z₀ := Z₁)
      (hb.trans_le RHTower.zetaZeroAbscissa_le_one) (by linarith)
      (fun Z hZ => by
        rw [signal_zetaGaussianKernel_eq_twistedMoebiusSum c (by linarith)]; exact hK Z hZ)
      ρ hre hρ1 hzero

/-- **Exact least exponent `θ_min` for the pole kernel.** -/
theorem isLeast_principalTwistGeneric_poleKernel (c : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    IsLeast {θ : ℝ | 0 ≤ θ ∧ IsGenericMeanSquare (principalTwistMeanSquare (poleKernel c) n) θ}
      ((n : ℝ) / ((n : ℝ) - 1) * (2 * RHTower.zetaZeroAbscissa - 1)) := by
  rw [principalTwistGenericSet_poleKernel c hn]
  exact isLeast_Ici

/-- **Exact least exponent `θ_min` for the Gaussian kernel.** -/
theorem isLeast_principalTwistGeneric_gaussianKernel (c : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    IsLeast {θ : ℝ | 0 ≤ θ ∧ IsGenericMeanSquare (principalTwistMeanSquare (gaussianKernel c) n) θ}
      ((n : ℝ) / ((n : ℝ) - 1) * (2 * RHTower.zetaZeroAbscissa - 1)) := by
  rw [principalTwistGenericSet_gaussianKernel c hn]
  exact isLeast_Ici

/-- **Riemann Hypothesis biconditional for the principal twist threshold.** -/
theorem principalTwistThreshold_eq_zero_iff_riemannHypothesis {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) / ((n : ℝ) - 1) * (2 * RHTower.zetaZeroAbscissa - 1) = 0 ↔ RiemannHypothesis := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (n : ℝ) / ((n : ℝ) - 1) := div_pos (by linarith) (by linarith)
  rw [mul_eq_zero, or_iff_right hpos.ne', riemannHypothesis_iff_zetaZeroAbscissa_eq_half]
  constructor <;> intro h <;> linarith

/-! ### Sharp non-cancellative / operator-norm barrier `n / (n − 1)` -/

/-- Positive-weight squarefree twist sum replacing `μ(m)` by `μ(m)²`. -/
def positiveSquarefreeTwistSum (c : ℝ) (S : Finset ℕ) (Z : ℝ) : ℂ :=
  ∑' m : ℕ, (if ∀ p ∈ S, ¬ p ∣ m then ((ArithmeticFunction.moebius m : ℂ) ^ 2) else 0) *
    signal (gaussianKernel c) 2 (Z / m)

/-- Mean square of positive-weight squarefree sums over principal `n`-th-power twists `a^n ≤ Z^θ`. -/
def positiveSquarefreeTwistMeanSquare (c : ℝ) (n : ℕ) (θ Z : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 ⌊Z ^ (θ / n)⌋₊, ‖positiveSquarefreeTwistSum c a.primeFactors Z‖ ^ 2

theorem card_filter_dvd_Icc_le_div {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun m => k ∣ m)).card ≤ N / k := by
  have hinj : Set.InjOn (fun m : ℕ => m / k) ↑((Finset.Icc 1 N).filter (fun m => k ∣ m)) := by
    intro x hx y hy hxy
    have hkx : k ∣ x := (Finset.mem_filter.mp hx).2
    have hky : k ∣ y := (Finset.mem_filter.mp hy).2
    rw [← Nat.mul_div_cancel' hkx, ← Nat.mul_div_cancel' hky, hxy]
  have hmaps : Set.MapsTo (fun m : ℕ => m / k)
      ↑((Finset.Icc 1 N).filter (fun m => k ∣ m)) ↑(Finset.Icc 1 (N / k)) := by
    intro m hm
    obtain ⟨hIcc, hkm⟩ := Finset.mem_filter.mp hm
    obtain ⟨h1, hN⟩ := Finset.mem_Icc.mp hIcc
    rcases hkm with ⟨q, rfl⟩
    have hq_pos : 1 ≤ q := by
      rcases eq_or_ne q 0 with rfl | hq
      · simp at h1
      · omega
    exact Finset.mem_Icc.mpr ⟨by rw [Nat.mul_div_cancel_left q hk]; exact hq_pos,
      by rw [← Nat.mul_div_cancel_left q hk]; exact Nat.div_le_div_right hN⟩
  calc ((Finset.Icc 1 N).filter (fun m => k ∣ m)).card
      ≤ (Finset.Icc 1 (N / k)).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = N / k := by simp

theorem card_squarefree_window_avoiding_prime_ge {N p : ℕ} (hN : 36 ≤ N)
    (hp : 19 ≤ p ∨ p = 1) :
    (N : ℝ) / 12 ≤
      (((Finset.Icc (N / 9 + 1) N).filter (fun m => Squarefree m ∧ (p = 1 ∨ ¬ p ∣ m))).card : ℝ) := by
  -- Every non-squarefree `m ∈ Icc 1 N` is divisible by `d²` for some `d ∈ Icc 2 N`.
  have hnsq_sub : (Finset.Icc (N / 9 + 1) N).filter (fun m => ¬ Squarefree m) ⊆
      (Finset.Icc 2 N).biUnion (fun d => (Finset.Icc 1 N).filter (fun m => d ^ 2 ∣ m)) := by
    intro m hm
    obtain ⟨hIcc, hnsq⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hIcc
    have hm1 : 1 ≤ m := by omega
    rw [Squarefree, not_forall] at hnsq
    obtain ⟨d, hd⟩ := hnsq
    rw [not_imp] at hd
    obtain ⟨hdd, hnu⟩ := hd
    have hd_ge2 : 2 ≤ d := by
      rcases d with _ | _ | d
      · simp at hdd; omega
      · exact (hnu isUnit_one).elim
      · omega
    have hd_leN : d ≤ N := by
      have hd_dvd : d ∣ m := dvd_of_mul_left_dvd hdd
      exact (Nat.le_of_dvd (by omega) hd_dvd).trans hm_hi
    refine Finset.mem_biUnion.mpr ⟨d, Finset.mem_Icc.mpr ⟨hd_ge2, hd_leN⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm1, hm_hi⟩, by rwa [sq]⟩
  have hnsq_card : (((Finset.Icc (N / 9 + 1) N).filter (fun m => ¬ Squarefree m)).card : ℝ) ≤
      (25 : ℝ) / 36 * N := by
    have h1 : ((Finset.Icc (N / 9 + 1) N).filter (fun m => ¬ Squarefree m)).card ≤
        ∑ d ∈ Finset.Icc 2 N, ((Finset.Icc 1 N).filter (fun m => d ^ 2 ∣ m)).card :=
      (Finset.card_le_card hnsq_sub).trans Finset.card_biUnion_le
    have h2 : ∀ d ∈ Finset.Icc 2 N,
        (((Finset.Icc 1 N).filter (fun m => d ^ 2 ∣ m)).card : ℝ) ≤ (N : ℝ) / (d : ℝ) ^ 2 := by
      intro d hd
      have hd2 : 2 ≤ d := (Finset.mem_Icc.mp hd).1
      have hc := card_filter_dvd_Icc_le_div (show 0 < d ^ 2 by positivity) N
      calc (((Finset.Icc 1 N).filter (fun m => d ^ 2 ∣ m)).card : ℝ)
          ≤ ((N / d ^ 2 : ℕ) : ℝ) := by exact_mod_cast hc
        _ ≤ (N : ℝ) / ((d ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
        _ = (N : ℝ) / (d : ℝ) ^ 2 := by push_cast; rfl
    have hsum_inv : (∑ d ∈ Finset.Icc 2 N, (1 : ℝ) / (d : ℝ) ^ 2) ≤ 25 / 36 := by
      have hsplit2 : Finset.Icc 2 N = insert 2 (insert 3 (Finset.Icc 4 N)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsplit2, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
      have htel_le : (∑ d ∈ Finset.Icc 4 N, (1 : ℝ) / (d : ℝ) ^ 2) ≤ 1 / 3 := by
        have hle_t : ∀ d ∈ Finset.Icc 4 N, (1 : ℝ) / (d : ℝ) ^ 2 ≤
            1 / ((d : ℝ) - 1) - 1 / (d : ℝ) := by
          intro d hd
          have hd4 : (4 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
          have hpos1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
          have hpos2 : (0 : ℝ) < d := by linarith
          rw [div_sub_div _ _ hpos1.ne' hpos2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have htel' : (∑ d ∈ Finset.Icc 4 N, (1 / ((d : ℝ) - 1) - 1 / (d : ℝ))) =
            1 / 3 - 1 / (N : ℝ) := by
          have hind : ∀ M : ℕ, 3 ≤ M →
              (∑ d ∈ Finset.Ico 4 (M + 1), (1 / ((d : ℝ) - 1) - 1 / (d : ℝ))) =
                1 / 3 - 1 / (M : ℝ) := by
            intro M hM3
            induction M, hM3 using Nat.le_induction with
            | base => simp
            | succ k hk ih =>
              rw [Finset.sum_Ico_succ_top (by omega), ih]
              push_cast; ring
          exact hind N (by omega)
        exact (Finset.sum_le_sum hle_t).trans (by rw [htel']; linarith [show (0 : ℝ) ≤ 1 / N by positivity])
      norm_num
      linarith
    calc (((Finset.Icc (N / 9 + 1) N).filter (fun m => ¬ Squarefree m)).card : ℝ)
        ≤ ((∑ d ∈ Finset.Icc 2 N, ((Finset.Icc 1 N).filter (fun m => d ^ 2 ∣ m)).card : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ = ∑ d ∈ Finset.Icc 2 N, (((Finset.Icc 1 N).filter (fun m => d ^ 2 ∣ m)).card : ℝ) := by
          push_cast; rfl
      _ ≤ ∑ d ∈ Finset.Icc 2 N, (N : ℝ) / (d : ℝ) ^ 2 := Finset.sum_le_sum h2
      _ = (N : ℝ) * ∑ d ∈ Finset.Icc 2 N, (1 : ℝ) / (d : ℝ) ^ 2 := by
          simp_rw [div_eq_mul_one_div, ← Finset.mul_sum]
      _ ≤ (N : ℝ) * (25 / 36) := mul_le_mul_of_nonneg_left hsum_inv (by positivity)
      _ = 25 / 36 * (N : ℝ) := by ring
  have hp_card : (((Finset.Icc (N / 9 + 1) N).filter (fun m => ¬ (p = 1 ∨ ¬ p ∣ m))).card : ℝ) ≤
      (2 : ℝ) / 36 * N := by
    rcases hp with hp19 | rfl
    · have hsub_p : (Finset.Icc (N / 9 + 1) N).filter (fun m => ¬ (p = 1 ∨ ¬ p ∣ m)) ⊆
          (Finset.Icc 1 N).filter (fun m => p ∣ m) := by
        intro m hm
        obtain ⟨hIcc, hnot⟩ := Finset.mem_filter.mp hm
        push_neg at hnot
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hIcc).2⟩, hnot.2⟩
      calc (((Finset.Icc (N / 9 + 1) N).filter (fun m => ¬ (p = 1 ∨ ¬ p ∣ m))).card : ℝ)
          ≤ (((Finset.Icc 1 N).filter (fun m => p ∣ m)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub_p
        _ ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast card_filter_dvd_Icc_le_div (by omega) N
        _ ≤ (N : ℝ) / (p : ℝ) := Nat.cast_div_le
        _ ≤ (N : ℝ) / 19 := div_le_div_of_nonneg_left (by positivity) (by norm_num)
            (by exact_mod_cast hp19)
        _ ≤ 2 / 36 * (N : ℝ) := by linarith [show (0 : ℝ) ≤ N by positivity]
    · simp
      positivity
  set J := Finset.Icc (N / 9 + 1) N
  have hJ_card : (31 : ℝ) / 36 * N ≤ (J.card : ℝ) := by
    have hcard_nat : N - N / 9 ≤ J.card := by simp [J]
    have hdiv9 : 9 * (N / 9) ≤ N := Nat.mul_div_le N 9
    have h1 : (8 : ℝ) / 9 * N - 1 ≤ ((N - N / 9 : ℕ) : ℝ) := by
      have hle : N / 9 ≤ N := Nat.div_le_self N 9
      rw [Nat.cast_sub hle]
      have hcast : (9 : ℝ) * ((N / 9 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdiv9
      linarith
    have hNR : (36 : ℝ) ≤ N := by exact_mod_cast hN
    have h2 : ((N - N / 9 : ℕ) : ℝ) ≤ (J.card : ℝ) := by exact_mod_cast hcard_nat
    linarith
  have hcover : J ⊆ J.filter (fun m => Squarefree m ∧ (p = 1 ∨ ¬ p ∣ m)) ∪
      (J.filter (fun m => ¬ Squarefree m) ∪ J.filter (fun m => ¬ (p = 1 ∨ ¬ p ∣ m))) := by
    intro m hm
    by_cases h1 : Squarefree m
    · by_cases h2 : p = 1 ∨ ¬ p ∣ m
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hm, h1, h2⟩)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hm, h2⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hm, h1⟩))
  have hcard_union : J.card ≤ (J.filter (fun m => Squarefree m ∧ (p = 1 ∨ ¬ p ∣ m))).card +
      (J.filter (fun m => ¬ Squarefree m)).card +
      (J.filter (fun m => ¬ (p = 1 ∨ ¬ p ∣ m))).card := by
    have hu1 := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    have hu2 := Finset.card_union_le (J.filter (fun m => ¬ Squarefree m))
      (J.filter (fun m => ¬ (p = 1 ∨ ¬ p ∣ m)))
    omega
  have hcard_real : (J.card : ℝ) ≤
      ((J.filter (fun m => Squarefree m ∧ (p = 1 ∨ ¬ p ∣ m))).card : ℝ) +
      ((J.filter (fun m => ¬ Squarefree m)).card : ℝ) +
      ((J.filter (fun m => ¬ (p = 1 ∨ ¬ p ∣ m))).card : ℝ) := by exact_mod_cast hcard_union
  linarith

theorem positiveSquarefreeTwistSum_ge_linear (c : ℝ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ Z : ℝ, 72 ≤ Z → ∀ p : ℕ, (19 ≤ p ∧ p.Prime) ∨ p = 1 →
      γ * Z ≤ ‖positiveSquarefreeTwistSum c p.primeFactors Z‖ := by
  set w_min : ℝ := min 1 ((9 : ℝ) ^ c) / (2 * Real.sqrt Real.pi) * Real.exp (-(9 / 4))
  have hw_min : 0 < w_min := by
    have : 0 < min 1 ((9 : ℝ) ^ c) := lt_min one_pos (Real.rpow_pos_of_pos (by norm_num) c)
    positivity
  refine ⟨w_min / 24, by positivity, fun Z hZ p hp => ?_⟩
  set N : ℕ := ⌊Z⌋₊
  have hN36 : 36 ≤ N := Nat.le_floor (by linarith)
  have hZ_half : Z / 2 ≤ (N : ℝ) := by
    have := Nat.lt_floor_add_one Z
    linarith
  have hN_le_Z : (N : ℝ) ≤ Z := Nat.floor_le (by linarith)
  -- Express `positiveSquarefreeTwistSum` as the cast of a nonnegative real `tsum`.
  set f_real : ℕ → ℝ := fun m =>
    if m ≠ 0 ∧ Squarefree m ∧ ∀ q ∈ p.primeFactors, ¬ q ∣ m then
      (Z / m) ^ c / (2 * Real.sqrt Real.pi) * Real.exp (-(Real.log (Z / m) ^ 2 / 4))
    else 0
  have hf_nn : ∀ m : ℕ, 0 ≤ f_real m := by
    intro m
    simp only [f_real]
    split_ifs with hm
    · have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm.1)
      have hZm : 0 < Z / m := div_pos (by linarith) hm_pos
      exact mul_nonneg (div_nonneg (Real.rpow_nonneg hZm.le c) (by positivity))
        (Real.exp_pos _).le
    · rfl
  have hf_eq : ∀ m : ℕ,
      (if ∀ q ∈ p.primeFactors, ¬ q ∣ m then ((ArithmeticFunction.moebius m : ℂ) ^ 2) else 0) *
        signal (gaussianKernel c) 2 (Z / m) = ((f_real m : ℝ) : ℂ) := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm0
    · simp [f_real]
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
    rw [signal_gaussianKernel_eq c (div_pos (by linarith) hm_pos)]
    by_cases hsq : Squarefree m
    · have hμ_sq : (ArithmeticFunction.moebius m : ℂ) ^ 2 = 1 := by
        have hne : ArithmeticFunction.moebius m ≠ 0 :=
          ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsq
        have habs : |ArithmeticFunction.moebius m| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
        have h1 : ArithmeticFunction.moebius m = 1 ∨ ArithmeticFunction.moebius m = -1 := by omega
        rcases h1 with h | h <;> simp [h]
      by_cases hdiv : ∀ q ∈ p.primeFactors, ¬ q ∣ m
      · simp [f_real, hm0, hsq, hdiv, hμ_sq]
      · simp [f_real, hm0, hsq, hdiv]
    · have hμ0 : ArithmeticFunction.moebius m = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
      simp [f_real, hsq, hμ0]
  have hf_summ : Summable f_real := by
    obtain ⟨C, _, hsig⟩ := exists_norm_signal_two_le (isSmoothCutoff_gaussianKernel c)
    refine Summable.of_nonneg_of_le hf_nn (fun m => ?_)
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left (C * Z ^ 2))
    have h1 := congrArg Complex.norm (hf_eq m)
    rw [Complex.norm_real, Real.norm_of_nonneg (hf_nn m)] at h1
    rw [← h1]
    rcases eq_or_ne m 0 with rfl | hm0
    · simp
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
    rw [norm_mul]
    have hcoeff : ‖if ∀ q ∈ p.primeFactors, ¬ q ∣ m then
        ((ArithmeticFunction.moebius m : ℂ) ^ 2) else 0‖ ≤ 1 := by
      split_ifs
      · rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (norm_moebius_complex_le_one m)
      · simp
    calc ‖if ∀ q ∈ p.primeFactors, ¬ q ∣ m then ((ArithmeticFunction.moebius m : ℂ) ^ 2) else 0‖ *
          ‖signal (gaussianKernel c) 2 (Z / m)‖
        ≤ 1 * (C * (Z / m) ^ 2) :=
          mul_le_mul hcoeff (hsig _ (div_pos (by linarith) hm_pos)) (norm_nonneg _) zero_le_one
      _ = C * Z ^ 2 * (1 / (m : ℝ) ^ (2 : ℕ)) := by rw [div_pow]; ring
  have htsum_eq : positiveSquarefreeTwistSum c p.primeFactors Z =
      (((∑' m : ℕ, f_real m) : ℝ) : ℂ) := by
    unfold positiveSquarefreeTwistSum
    simp_rw [hf_eq, Complex.ofReal_tsum]
  rw [htsum_eq, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg hf_nn)]
  set S_win := (Finset.Icc (N / 9 + 1) N).filter (fun m => Squarefree m ∧ (p = 1 ∨ ¬ p ∣ m))
  have hcard_S := card_squarefree_window_avoiding_prime_ge hN36
    (hp.elim (fun h => Or.inl h.1) Or.inr)
  have hterm_win : ∀ m ∈ S_win, w_min ≤ f_real m := by
    intro m hm
    obtain ⟨hIcc, hsq, hp_div⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hIcc
    have hm0 : m ≠ 0 := by omega
    have hpf : ∀ q ∈ p.primeFactors, ¬ q ∣ m := by
      rcases hp with ⟨_, hp_prime⟩ | rfl
      · rw [hp_prime.primeFactors]
        simp [hp_div.resolve_left (by omega)]
      · simp
    simp only [f_real, if_pos ⟨hm0, hsq, hpf⟩]
    have hm_pos : (0 : ℝ) < m := by positivity
    have hX_ge1 : 1 ≤ Z / m := (le_div_iff₀ hm_pos).mpr ((by exact_mod_cast hm_hi).trans hN_le_Z)
    have hX_le9 : Z / m ≤ 9 := by
      rw [div_le_iff₀ hm_pos]
      have h9 : N < 9 * m := by
        have := Nat.div_lt_iff_lt_mul (by norm_num : 0 < 9) |>.mp (by omega : N / 9 < m)
        omega
      have h9R : (N : ℝ) + 1 ≤ 9 * (m : ℝ) := by exact_mod_cast h9
      have := Nat.lt_floor_add_one Z
      linarith
    have hlog_nn : 0 ≤ Real.log (Z / m) := Real.log_nonneg hX_ge1
    have hlog_le3 : Real.log (Z / m) ≤ 3 := by
      calc Real.log (Z / m) ≤ Real.log 9 := Real.log_le_log (by positivity) hX_le9
        _ ≤ Real.log (Real.exp 3) := Real.log_le_log (by norm_num) (by
            have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
            have h8 : (8 : ℝ) ≤ Real.exp 3 := by
              rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
              nlinarith
            have h27 : (9 : ℝ) ≤ Real.exp 3 := by
              have he1 := Real.exp_one_gt_d9
              rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
              nlinarith
            exact h27)
        _ = 3 := Real.log_exp 3
    have hexp_ge : Real.exp (-(9 / 4)) ≤ Real.exp (-(Real.log (Z / m) ^ 2 / 4)) := by
      refine Real.exp_le_exp.mpr ?_
      have hsq_le : Real.log (Z / m) ^ 2 ≤ 9 := by nlinarith
      linarith
    have hrpow_ge : min 1 ((9 : ℝ) ^ c) ≤ (Z / m) ^ c := by
      rcases le_or_gt 0 c with hc | hc
      · calc min 1 ((9 : ℝ) ^ c) ≤ 1 := min_le_left _ _
          _ = (1 : ℝ) ^ c := (Real.one_rpow c).symm
          _ ≤ (Z / m) ^ c := Real.rpow_le_rpow zero_le_one hX_ge1 hc
      · have hneg : 0 ≤ -c := by linarith
        calc min 1 ((9 : ℝ) ^ c) ≤ (9 : ℝ) ^ c := min_le_right _ _
          _ = ((9 : ℝ) ^ (-c))⁻¹ := by rw [Real.rpow_neg (by norm_num), inv_inv]
          _ ≤ ((Z / m) ^ (-c))⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _)
              (Real.rpow_le_rpow (by positivity) hX_le9 hneg)
          _ = (Z / m) ^ c := by rw [Real.rpow_neg (by positivity), inv_inv]
    exact mul_le_mul (div_le_div_of_nonneg_right hrpow_ge (by positivity)) hexp_ge
      (Real.exp_pos _).le (by positivity)
  calc w_min / 24 * Z
      ≤ w_min * ((N : ℝ) / 12) := by linarith
    _ ≤ w_min * (S_win.card : ℝ) := mul_le_mul_of_nonneg_left hcard_S hw_min.le
    _ = ∑ _m ∈ S_win, w_min := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ m ∈ S_win, f_real m := Finset.sum_le_sum hterm_win
    _ ≤ ∑' m : ℕ, f_real m := hf_summ.sum_le_tsum S_win (fun m _ => hf_nn m)

/-- **Sharp positive-weight / operator-norm barrier (lower bound).** Without sign cancellation
(`μ(m) ↦ μ(m)²`), every `0 ≤ θ < n / (n − 1)` fails to have a generic mean square. -/
theorem not_isGenericMeanSquare_positiveSquarefreeTwist_of_lt (c : ℝ) {n : ℕ} (hn : 2 ≤ n)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < (n : ℝ) / ((n : ℝ) - 1)) :
    ¬ IsGenericMeanSquare (positiveSquarefreeTwistMeanSquare c n) θ := by
  intro hgen
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := by linarith
  obtain ⟨γ, hγ, hlin⟩ := positiveSquarefreeTwistSum_ge_linear c
  rcases eq_or_lt_of_le hθ0 with rfl | hθ_pos
  · -- At `θ = 0`, the single term `a = 1` has norm squared `≥ γ² Z²`, exceeding `K Z^{3/2}`.
    obtain ⟨K, Z₀, hZ₀, hK⟩ := hgen (1 / 2) (by norm_num)
    have hlim : Tendsto (fun Z : ℝ => Z ^ ((1 : ℝ) / 2)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num)
    obtain ⟨Z₁, hZ₁⟩ := eventually_atTop.mp
      (hlim.eventually_gt_atTop (max 1 (max K 0 / γ ^ 2)))
    set Z : ℝ := max 72 (max Z₀ Z₁)
    have hZ72 : 72 ≤ Z := le_max_left _ _
    have hZZ₀ : Z₀ ≤ Z := (le_max_left Z₀ Z₁).trans (le_max_right _ _)
    have hZZ₁ : Z₁ ≤ Z := (le_max_right Z₀ Z₁).trans (le_max_right _ _)
    have hZ_pos : 0 < Z := by linarith
    have h1_mem : (1 : ℕ) ∈ Finset.Icc 1 ⌊Z ^ ((0 : ℝ) / n)⌋₊ := by
      rw [zero_div, Real.rpow_zero]; simp
    have hlow : (γ * Z) ^ 2 ≤ positiveSquarefreeTwistMeanSquare c n 0 Z := by
      have hterm := hlin Z hZ72 1 (Or.inr rfl)
      have hsq : (γ * Z) ^ 2 ≤ ‖positiveSquarefreeTwistSum c (1 : ℕ).primeFactors Z‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) hterm 2
      exact hsq.trans (Finset.single_le_sum (fun _ _ => sq_nonneg _) h1_mem)
    have hup : positiveSquarefreeTwistMeanSquare c n 0 Z ≤ max K 0 * Z ^ ((3 : ℝ) / 2) := by
      calc positiveSquarefreeTwistMeanSquare c n 0 Z
          ≤ K * Z ^ ((0 : ℝ) + 1 + 1 / 2) := hK Z hZZ₀
        _ ≤ max K 0 * Z ^ ((3 : ℝ) / 2) := by
            rw [show (0 : ℝ) + 1 + 1 / 2 = 3 / 2 by ring]
            exact mul_le_mul_of_nonneg_right (le_max_left K 0) (by positivity)
    have hZ_gt := (le_max_right 1 (max K 0 / γ ^ 2)).trans_lt (hZ₁ Z hZZ₁)
    have hmul_gt : max K 0 < γ ^ 2 * Z ^ ((1 : ℝ) / 2) := by
      rwa [div_lt_iff₀ (by positivity), mul_comm] at hZ_gt
    have hZ2 : Z ^ (2 : ℕ) = Z ^ ((1 : ℝ) / 2) * Z ^ ((3 : ℝ) / 2) := by
      rw [← Real.rpow_add hZ_pos, show (1 : ℝ) / 2 + 3 / 2 = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    have hstrict : max K 0 * Z ^ ((3 : ℝ) / 2) < (γ * Z) ^ 2 := by
      rw [mul_pow, hZ2, ← mul_assoc]
      exact mul_lt_mul_of_pos_right hmul_gt (by positivity)
    linarith
  · -- For `0 < θ < n / (n − 1)`, prime twists `p ∈ (M, Q M]` give `≫ Z^{2 + θ/n − ε} > Z^{θ + 1 + ε}`.
    set α : ℝ := θ / n
    have hα_pos : 0 < α := div_pos hθ_pos hn_pos
    have hgap : 0 < 1 + α - θ := by
      have h1 : θ * ((n : ℝ) - 1) < n := (lt_div_iff₀ (by linarith)).mp hθ
      simp only [α]
      rw [show 1 + θ / n - θ = (n - θ * (n - 1)) / n by field_simp; ring]
      exact div_pos (by linarith) hn_pos
    set ε : ℝ := (1 + α - θ) / 3
    have hε : 0 < ε := by simp only [ε]; linarith
    obtain ⟨K, Z₀, hZ₀, hK⟩ := hgen ε hε
    set Q : ℕ := ⌈Real.exp (2 * RHTower.Sieve.mertensFirstConst + 1)⌉₊ + 1
    have hQ1 : 1 ≤ Q := by omega
    have hQ_log : 1 ≤ Real.log Q - 2 * RHTower.Sieve.mertensFirstConst := by
      have hexp_le : Real.exp (2 * RHTower.Sieve.mertensFirstConst + 1) ≤ (Q : ℝ) := by
        push_cast
        linarith [Nat.le_ceil (Real.exp (2 * RHTower.Sieve.mertensFirstConst + 1))]
      have hlog := Real.log_le_log (Real.exp_pos _) hexp_le
      rw [Real.log_exp] at hlog
      linarith
    set R_sc : ℝ := ((Q + 1 : ℕ) : ℝ)
    have hR_pos : 0 < R_sc := by positivity
    have hα_lt1 : α < 1 := by
      have h1 : θ * ((n : ℝ) - 1) < n := (lt_div_iff₀ (by linarith)).mp hθ
      simp only [α]; rw [div_lt_one hn_pos]; nlinarith
    have hlim1 : Tendsto (fun Z : ℝ => Z ^ α / R_sc) atTop atTop :=
      (tendsto_rpow_atTop hα_pos).atTop_div_const hR_pos
    have hlim2 : Tendsto (fun Z : ℝ => Real.log Z / Z ^ ε) atTop (𝓝 0) :=
      (Real.isLittleO_log_rpow_atTop hε).tendsto_div_nhds_zero
    have hlim3 : Tendsto (fun Z : ℝ => Z ^ ε) atTop atTop := tendsto_rpow_atTop hε
    obtain ⟨Z₁, hZ₁⟩ := eventually_atTop.mp
      ((hlim1.eventually_ge_atTop 20).and
        ((hlim2.eventually (gt_mem_nhds one_pos)).and
          (hlim3.eventually_gt_atTop (2 * R_sc * max K 1 / γ ^ 2))))
    set Z : ℝ := max 72 (max Z₀ Z₁)
    have hZ72 : 72 ≤ Z := le_max_left _ _
    have hZZ₀ : Z₀ ≤ Z := (le_max_left Z₀ Z₁).trans (le_max_right _ _)
    have hZZ₁ : Z₁ ≤ Z := (le_max_right Z₀ Z₁).trans (le_max_right _ _)
    obtain ⟨hM20, hlog_lt, hZε_gt⟩ := hZ₁ Z hZZ₁
    have hZ1 : 1 ≤ Z := by linarith
    have hZ_pos : 0 < Z := by linarith
    set M : ℕ := ⌊Z ^ α / R_sc⌋₊
    have hM19 : 19 ≤ M := by have := Nat.le_floor hM20; omega
    have hM_upper : (M : ℝ) ≤ Z ^ α / R_sc := Nat.floor_le (by positivity)
    have hM_lower : Z ^ α / (2 * R_sc) ≤ (M : ℝ) := by
      have := Nat.lt_floor_add_one (Z ^ α / R_sc)
      linarith
    have hM_le_Z : (M : ℝ) ≤ Z := by
      have hR1 : 1 ≤ R_sc := by simp only [R_sc]; exact_mod_cast (by omega : 1 ≤ Q + 1)
      calc (M : ℝ) ≤ Z ^ α / R_sc := hM_upper
        _ ≤ Z ^ α / 1 := div_le_div_of_nonneg_left (by positivity) one_pos hR1
        _ = Z ^ α := div_one _
        _ ≤ Z ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hZ1 hα_lt1.le
        _ = Z := Real.rpow_one Z
    have hQM_floor : Q * M ≤ ⌊Z ^ (θ / n)⌋₊ := by
      refine Nat.le_floor ?_
      have hQ_le : (Q : ℝ) ≤ R_sc := by simp only [R_sc]; exact_mod_cast (Nat.le_succ Q)
      calc ((Q * M : ℕ) : ℝ) = (Q : ℝ) * (M : ℝ) := by push_cast; rfl
        _ ≤ R_sc * (Z ^ α / R_sc) := mul_le_mul hQ_le hM_upper (by positivity) hR_pos.le
        _ = Z ^ (θ / n) := mul_div_cancel₀ _ hR_pos.ne'
    set P := RHTower.Sieve.bigPrimeSet M (Q * M)
    have hsub : P ⊆ Finset.Icc 1 ⌊Z ^ (θ / n)⌋₊ := by
      intro p hp
      obtain ⟨hIcc, _⟩ := Finset.mem_filter.mp hp
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hIcc
      exact Finset.mem_Icc.mpr ⟨by omega, hhi.trans hQM_floor⟩
    have hlogM_pos : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
    have hlogM_le : Real.log M ≤ Z ^ ε :=
      (Real.log_le_log (by positivity) hM_le_Z).trans
        ((div_lt_one (Real.rpow_pos_of_pos hZ_pos ε)).mp hlog_lt).le
    have hcard_ge : Z ^ (α - ε) / (2 * R_sc) ≤ (P.card : ℝ) := by
      have hc := RHTower.Sieve.card_bigPrimeSet_ratio_ge (by omega : 3 ≤ M) hQ1
      have h1 : (M : ℝ) / Real.log M ≤ (P.card : ℝ) := by
        calc (M : ℝ) / Real.log M = 1 * (M : ℝ) / Real.log M := by ring
          _ ≤ (Real.log Q - 2 * RHTower.Sieve.mertensFirstConst) * (M : ℝ) / Real.log M :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right hQ_log (by positivity)) hlogM_pos.le
          _ ≤ (P.card : ℝ) := hc
      have h2 : Z ^ (α - ε) / (2 * R_sc) ≤ (M : ℝ) / Real.log M := by
        rw [Real.rpow_sub hZ_pos]
        calc Z ^ α / Z ^ ε / (2 * R_sc) = (Z ^ α / (2 * R_sc)) / Z ^ ε := by ring
          _ ≤ (M : ℝ) / Real.log M := div_le_div₀ (by positivity) hM_lower hlogM_pos hlogM_le
      exact h2.trans h1
    have hp_term : ∀ p ∈ P, (γ * Z) ^ 2 ≤ ‖positiveSquarefreeTwistSum c p.primeFactors Z‖ ^ 2 := by
      intro p hp
      obtain ⟨hIcc, hp_pr⟩ := Finset.mem_filter.mp hp
      have hp19 : 19 ≤ p := by have := (Finset.mem_Icc.mp hIcc).1; omega
      exact pow_le_pow_left₀ (by positivity) (hlin Z hZ72 p (Or.inl ⟨hp19, hp_pr⟩)) 2
    have hlow : γ ^ 2 / (2 * R_sc) * Z ^ (2 + α - ε) ≤
        positiveSquarefreeTwistMeanSquare c n θ Z := by
      have hexp_eq : Z ^ (α - ε) * Z ^ (2 : ℕ) = Z ^ (2 + α - ε) := by
        rw [← Real.rpow_natCast Z 2, ← Real.rpow_add hZ_pos]
        congr 1; push_cast; ring
      calc γ ^ 2 / (2 * R_sc) * Z ^ (2 + α - ε)
          = (Z ^ (α - ε) / (2 * R_sc)) * (γ * Z) ^ 2 := by rw [ ← hexp_eq]; ring
        _ ≤ (P.card : ℝ) * (γ * Z) ^ 2 := mul_le_mul_of_nonneg_right hcard_ge (by positivity)
        _ = ∑ _p ∈ P, (γ * Z) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ p ∈ P, ‖positiveSquarefreeTwistSum c p.primeFactors Z‖ ^ 2 :=
            Finset.sum_le_sum hp_term
        _ ≤ positiveSquarefreeTwistMeanSquare c n θ Z :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
    have hup : positiveSquarefreeTwistMeanSquare c n θ Z ≤ max K 1 * Z ^ (θ + 1 + ε) :=
      (hK Z hZZ₀).trans (mul_le_mul_of_nonneg_right (le_max_left K 1) (by positivity))
    have hexp_split : 2 + α - ε = (θ + 1 + ε) + ε := by simp only [ε]; ring
    have hstrict : max K 1 * Z ^ (θ + 1 + ε) < γ ^ 2 / (2 * R_sc) * Z ^ (2 + α - ε) := by
      rw [hexp_split, Real.rpow_add hZ_pos, ← mul_assoc, mul_comm (γ ^ 2 / (2 * R_sc)),
        mul_assoc, mul_comm (Z ^ (θ + 1 + ε))]
      have hcoef : max K 1 < γ ^ 2 / (2 * R_sc) * Z ^ ε := by
        rwa [div_lt_iff₀ (by positivity), mul_comm (Z ^ ε), ← mul_div_assoc',
          lt_div_iff₀ (by positivity)] at hZε_gt
      exact mul_lt_mul_of_pos_right hcoef (by positivity)
    linarith

/-- **Matching upper bound above `n / (n − 1)`.** For every `θ ≥ n / (n − 1)`, the positive-weight
squarefree twist family has a generic mean square unconditionally. -/
theorem isGenericMeanSquare_positiveSquarefreeTwist_of_ge (c : ℝ) {n : ℕ} (hn : 2 ≤ n)
    {θ : ℝ} (hθ : (n : ℝ) / ((n : ℝ) - 1) ≤ θ) :
    IsGenericMeanSquare (positiveSquarefreeTwistMeanSquare c n) θ := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := by linarith
  have hθ0 : 0 ≤ θ := le_trans (div_nonneg (by linarith) (by linarith)) hθ
  intro ε hε
  set δ : ℝ := ε / 4
  have hδ : 0 < δ := by positivity
  set C_ker : ℝ := Real.exp ((c - 1 - δ) ^ 2) / (2 * Real.sqrt Real.pi)
  have hC_ker : 0 < C_ker := by positivity
  have hker_bd : ∀ X : ℝ, 0 < X → ‖signal (gaussianKernel c) 2 X‖ ≤ C_ker * X ^ (1 + δ) := by
    intro X hX
    rw [signal_gaussianKernel_eq c hX, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    set u : ℝ := Real.log X
    have hquad : c * u - u ^ 2 / 4 ≤ (1 + δ) * u + (c - 1 - δ) ^ 2 := by
      nlinarith [sq_nonneg (u / 2 - (c - 1 - δ))]
    have hexp : X ^ c * Real.exp (-(u ^ 2 / 4)) ≤
        Real.exp ((c - 1 - δ) ^ 2) * X ^ (1 + δ) := by
      rw [Real.rpow_def_of_pos hX, Real.rpow_def_of_pos hX, ← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by simp only [u]; linarith)
    calc X ^ c / (2 * Real.sqrt Real.pi) * Real.exp (-(u ^ 2 / 4))
        = (X ^ c * Real.exp (-(u ^ 2 / 4))) / (2 * Real.sqrt Real.pi) := by ring
      _ ≤ (Real.exp ((c - 1 - δ) ^ 2) * X ^ (1 + δ)) / (2 * Real.sqrt Real.pi) :=
          div_le_div_of_nonneg_right hexp (by positivity)
      _ = C_ker * X ^ (1 + δ) := by simp only [C_ker]; ring
  have hzeta_summ : Summable fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ (1 + δ) := by
    simpa [one_div] using Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 1 + δ)
  set S_δ : ℝ := ∑' m : ℕ, (1 : ℝ) / (m : ℝ) ^ (1 + δ)
  have hS_δ : 0 ≤ S_δ := tsum_nonneg fun _ => by positivity
  set C_tot : ℝ := C_ker * (S_δ + 1)
  have hC_tot : 0 < C_tot := by positivity
  refine ⟨C_tot ^ 2, 1, le_rfl, fun Z hZ => ?_⟩
  have hZ_pos : 0 < Z := by linarith
  have hsum_le : ∀ S : Finset ℕ, ‖positiveSquarefreeTwistSum c S Z‖ ≤ C_tot * Z ^ (1 + δ) := by
    intro S
    have hterm_le : ∀ m : ℕ,
        ‖(if ∀ p ∈ S, ¬ p ∣ m then ((ArithmeticFunction.moebius m : ℂ) ^ 2) else 0) *
          signal (gaussianKernel c) 2 (Z / m)‖ ≤
          C_ker * Z ^ (1 + δ) * ((1 : ℝ) / (m : ℝ) ^ (1 + δ)) := by
      intro m
      rcases eq_or_ne m 0 with rfl | hm0
      · simp [Real.zero_rpow (by linarith : 1 + δ ≠ 0)]
      have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
      rw [norm_mul]
      have hcoeff : ‖if ∀ p ∈ S, ¬ p ∣ m then
          ((ArithmeticFunction.moebius m : ℂ) ^ 2) else 0‖ ≤ 1 := by
        split_ifs
        · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_moebius_complex_le_one m)
        · simp
      calc ‖if ∀ p ∈ S, ¬ p ∣ m then ((ArithmeticFunction.moebius m : ℂ) ^ 2) else 0‖ *
            ‖signal (gaussianKernel c) 2 (Z / m)‖
          ≤ 1 * (C_ker * (Z / m) ^ (1 + δ)) :=
            mul_le_mul hcoeff (hker_bd _ (div_pos hZ_pos hm_pos)) (norm_nonneg _) zero_le_one
        _ = C_ker * Z ^ (1 + δ) * ((1 : ℝ) / (m : ℝ) ^ (1 + δ)) := by
            rw [Real.div_rpow hZ_pos.le hm_pos.le]; ring
    have hnorm_summ : Summable fun m : ℕ =>
        ‖(if ∀ p ∈ S, ¬ p ∣ m then ((ArithmeticFunction.moebius m : ℂ) ^ 2) else 0) *
          signal (gaussianKernel c) 2 (Z / m)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le (hzeta_summ.mul_left _)
    calc ‖positiveSquarefreeTwistSum c S Z‖
        ≤ ∑' m : ℕ, ‖(if ∀ p ∈ S, ¬ p ∣ m then ((ArithmeticFunction.moebius m : ℂ) ^ 2) else 0) *
            signal (gaussianKernel c) 2 (Z / m)‖ := norm_tsum_le_tsum_norm hnorm_summ
      _ ≤ ∑' m : ℕ, C_ker * Z ^ (1 + δ) * ((1 : ℝ) / (m : ℝ) ^ (1 + δ)) :=
          hnorm_summ.tsum_le_tsum hterm_le (hzeta_summ.mul_left _)
      _ = C_ker * Z ^ (1 + δ) * S_δ := tsum_mul_left
      _ ≤ C_tot * Z ^ (1 + δ) := by simp only [C_tot]; nlinarith [Real.rpow_pos_of_pos hZ_pos (1 + δ)]
  have hcard : ((Finset.Icc 1 ⌊Z ^ (θ / n)⌋₊).card : ℝ) ≤ Z ^ (θ / n) := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
    exact Nat.floor_le (by positivity)
  have hexp_le : θ / n + (2 + 2 * δ) ≤ θ + 1 + ε := by
    have h1 : (n : ℝ) ≤ θ * ((n : ℝ) - 1) := (div_le_iff₀ (by linarith)).mp hθ
    have h2 : θ / n + 2 ≤ θ + 1 := by
      rw [div_add_iff hn_pos.ne']
      nlinarith
    simp only [δ]
    linarith
  calc positiveSquarefreeTwistMeanSquare c n θ Z
      ≤ ∑ _a ∈ Finset.Icc 1 ⌊Z ^ (θ / n)⌋₊, (C_tot * Z ^ (1 + δ)) ^ 2 :=
        Finset.sum_le_sum fun a _ => pow_le_pow_left₀ (norm_nonneg _) (hsum_le a.primeFactors) 2
    _ = ((Finset.Icc 1 ⌊Z ^ (θ / n)⌋₊).card : ℝ) *
          (C_tot ^ 2 * Z ^ (2 + 2 * δ)) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_pow, ← Real.rpow_natCast (Z ^ (1 + δ)) 2,
          ← Real.rpow_mul hZ_pos.le]
        push_cast; ring_nf
    _ ≤ Z ^ (θ / n) * (C_tot ^ 2 * Z ^ (2 + 2 * δ)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = C_tot ^ 2 * Z ^ (θ / n + (2 + 2 * δ)) := by rw [Real.rpow_add hZ_pos]; ring
    _ ≤ C_tot ^ 2 * Z ^ (θ + 1 + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexp_le) (by positivity)

/-- **Exact closed-form generic set for positive squarefree weights (`μ(m)²`).** -/
theorem positiveSquarefreeTwistGenericSet_eq (c : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    {θ : ℝ | 0 ≤ θ ∧ IsGenericMeanSquare (positiveSquarefreeTwistMeanSquare c n) θ} =
      Set.Ici ((n : ℝ) / ((n : ℝ) - 1)) := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  ext θ
  simp only [Set.mem_setOf_eq, Set.mem_Ici]
  constructor
  · rintro ⟨hθ0, hgen⟩
    by_contra hlt
    exact not_isGenericMeanSquare_positiveSquarefreeTwist_of_lt c hn hθ0 (not_le.mp hlt) hgen
  · intro hge
    exact ⟨le_trans (div_nonneg (by linarith) (by linarith)) hge,
      isGenericMeanSquare_positiveSquarefreeTwist_of_ge c hn hge⟩

/-- **Exact unconditional minimum `n / (n − 1)` without sign cancellation.** -/
theorem isLeast_positiveSquarefreeTwistGeneric (c : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    IsLeast {θ : ℝ | 0 ≤ θ ∧ IsGenericMeanSquare (positiveSquarefreeTwistMeanSquare c n) θ}
      ((n : ℝ) / ((n : ℝ) - 1)) := by
  rw [positiveSquarefreeTwistGenericSet_eq c hn]
  exact isLeast_Ici

/-! ### Full Jacobi quadratic twist family (`n = 2`) -/

/-- Smoothed Möbius sum twisted by the Jacobi residue symbol `(m / u)`. -/
def jacobiTwistSum (c : ℝ) (u : ℕ) (Z : ℝ) : ℂ :=
  ∑' m : ℕ, (ArithmeticFunction.moebius m : ℂ) * (jacobiSym (m : ℤ) u : ℂ) *
    signal (gaussianKernel c) 2 (Z / m)

/-- Full quadratic twist mean square over all odd integers `1 ≤ u ≤ Z^θ`. -/
def jacobiTwistMeanSquare (c : ℝ) (θ Z : ℝ) : ℝ :=
  ∑ u ∈ (Finset.Icc 1 ⌊Z ^ θ⌋₊).filter Odd, ‖jacobiTwistSum c u Z‖ ^ 2

/-- Certified odd-prime family of the prime factors of an odd integer `u₀`. -/
def oddSquarefreeFamily (u₀ : ℕ) (hodd : Odd u₀) :
    RHTower.OddPrimeFamily {p // p ∈ u₀.primeFactors} where
  prime i := ⟨i.1, Nat.prime_of_mem_primeFactors i.2, fun h2 => by
    have hdvd : 2 ∣ u₀ := h2 ▸ Nat.dvd_of_mem_primeFactors i.2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)⟩
  pairwise_ne _ _ hij := Subtype.val_injective.ne hij

theorem oddSquarefreeFamily_modulus {u₀ : ℕ} (hodd : Odd u₀) (hsq : Squarefree u₀) :
    (oddSquarefreeFamily u₀ hodd).modulus = u₀ := by
  have hu₀_ne : u₀ ≠ 0 := by rintro rfl; simp at hodd
  unfold RHTower.OddPrimeFamily.modulus oddSquarefreeFamily
  change (∏ i : {p // p ∈ u₀.primeFactors}, i.1) = u₀
  rw [Finset.prod_coe_sort u₀.primeFactors id]
  conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hu₀_ne]
  rw [Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hle1 : u₀.factorization p ≤ 1 := hsq.natFactorization_le_one p
  have hge1 : 1 ≤ u₀.factorization p :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (Nat.support_factorization u₀ ▸ hp))
  have heq1 : u₀.factorization p = 1 := le_antisymm hle1 hge1
  simp [heq1]

/-- Primitive real Dirichlet character modulo `u₀` realizing `m ↦ jacobiSym m u₀` for odd
squarefree `u₀`. -/
def jacobiPrimChar (u₀ : ℕ) (hodd : Odd u₀) (hsq : Squarefree u₀) : DirichletCharacter ℂ u₀ :=
  DirichletCharacter.changeLevel (dvd_of_eq (oddSquarefreeFamily_modulus hodd hsq))
    (RHTower.OddPrimeFamily.quadraticDirichletCharacter (oddSquarefreeFamily u₀ hodd))

theorem jacobiPrimChar_isPrimitive {u₀ : ℕ} (hodd : Odd u₀) (hsq : Squarefree u₀) :
    (jacobiPrimChar u₀ hodd hsq).IsPrimitive := by
  unfold jacobiPrimChar
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_changeLevel]
  exact (RHTower.OddPrimeFamily.quadraticDirichletCharacter_isPrimitive
    (oddSquarefreeFamily u₀ hodd)).trans (oddSquarefreeFamily_modulus hodd hsq)

theorem jacobiPrimChar_ne_one {u₀ : ℕ} (hgt : 1 < u₀) (hodd : Odd u₀) (hsq : Squarefree u₀) :
    jacobiPrimChar u₀ hodd hsq ≠ 1 := by
  haveI : NeZero u₀ := ⟨by omega⟩
  intro h1
  have hc1 : (jacobiPrimChar u₀ hodd hsq).conductor = 1 :=
    DirichletCharacter.eq_one_iff_conductor_eq_one.mp h1
  have hcu₀ : (jacobiPrimChar u₀ hodd hsq).conductor = u₀ := jacobiPrimChar_isPrimitive hodd hsq
  omega

theorem jacobiPrimChar_intCast_eq_jacobi {u₀ : ℕ} (hodd : Odd u₀) (hsq : Squarefree u₀) (z : ℤ) :
    jacobiPrimChar u₀ hodd hsq (z : ZMod u₀) = (jacobiSym z u₀ : ℂ) := by
  have hu₀_ne : u₀ ≠ 0 := by rintro rfl; simp at hodd
  haveI : NeZero u₀ := ⟨hu₀_ne⟩
  set P := oddSquarefreeFamily u₀ hodd
  have hmod : P.modulus = u₀ := oddSquarefreeFamily_modulus hodd hsq
  unfold jacobiPrimChar
  by_cases hz : IsCoprime z (u₀ : ℤ)
  · rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' _ (dvd_of_eq hmod) hz,
      RHTower.OddPrimeFamily.quadraticDirichletCharacter_intCast_eq_jacobi P z, hmod]
  · have hnonunit : ¬ IsUnit ((z : ℤ) : ZMod u₀) := by
      rw [ZMod.coe_int_isUnit_iff_isCoprime]
      exact fun h => hz h.symm
    have hgcd_ne : z.gcd u₀ ≠ 1 := fun hg => hz (Int.isCoprime_iff_gcd_eq_one.mpr hg)
    rw [MulChar.map_nonunit _ hnonunit, jacobiSym.eq_zero_iff.mpr ⟨hu₀_ne, hgcd_ne⟩]
    simp

/-- On `u = u₀ a²` (`u₀, a` odd), the Jacobi twist sum is the `a.primeFactors`-avoiding twisted
Möbius sum of `m ↦ jacobiSym m u₀`. -/
theorem jacobiTwistSum_mul_sq_eq (c : ℝ) {u₀ a : ℕ} (hu₀ : Odd u₀) (ha : Odd a) (Z : ℝ) :
    jacobiTwistSum c (u₀ * a ^ 2) Z =
      twistedMoebiusSum (gaussianKernel c) (fun m => (jacobiSym (m : ℤ) u₀ : ℂ))
        a.primeFactors Z := by
  have hu₀_ne : u₀ ≠ 0 := by rintro rfl; simp at hu₀
  have ha_ne : a ≠ 0 := by rintro rfl; simp at ha
  unfold jacobiTwistSum twistedMoebiusSum
  refine tsum_congr fun m => ?_
  congr 1
  rw [jacobiSym.mul_right' (m : ℤ) hu₀_ne (pow_ne_zero 2 ha_ne), jacobiSym.pow_right]
  by_cases hdiv : ∀ p ∈ a.primeFactors, ¬ p ∣ m
  · have hcop : m.gcd a = 1 := by
      by_contra hne
      set p := (m.gcd a).minFac
      have hp_pr : p.Prime := Nat.minFac_prime hne
      have hp_dvd_g : p ∣ m.gcd a := Nat.minFac_dvd (m.gcd a)
      have hp_mem : p ∈ a.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp_pr, hp_dvd_g.trans (Nat.gcd_dvd_right m a), ha_ne⟩
      exact hdiv p hp_mem (hp_dvd_g.trans (Nat.gcd_dvd_left m a))
    have hgcd_int : (m : ℤ).gcd a = 1 := by simpa [Int.gcd_natCast_natCast] using hcop
    rw [jacobiSym.sq_one hgcd_int, mul_one, primeAvoidCoeff, if_pos hdiv]
  · push_neg at hdiv
    obtain ⟨p, hp_mem, hpm⟩ := hdiv
    have hp_pr : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hpa : p ∣ a := Nat.dvd_of_mem_primeFactors hp_mem
    have hgcd_ne : (m : ℤ).gcd a ≠ 1 := by
      rw [Int.gcd_natCast_natCast]
      intro hg1
      exact hp_pr.not_dvd_one (hg1 ▸ Nat.dvd_gcd hpm hpa)
    have hj0 : jacobiSym (m : ℤ) a = 0 := jacobiSym.eq_zero_iff.mpr ⟨ha_ne, hgcd_ne⟩
    have hnot : ¬ ∀ q ∈ a.primeFactors, ¬ q ∣ m := by push_neg; exact ⟨p, hp_mem, hpm⟩
    simp [hj0, primeAvoidCoeff, if_neg hnot]

/-- **Zero-free half-plane theorem for the full Jacobi twist family (`n = 2`).** If
`jacobiTwistMeanSquare c` is generic at `θ > 0`, then both `ζ` and every odd squarefree primitive
quadratic `L(s, χ_{u₀})` (`u₀ > 1`) have zero abscissa at most `min(1, 1/2 + θ/4)`. -/
theorem zetaZeroAbscissa_and_jacobiPrimChar_le_of_jacobiTwistGeneric (c : ℝ) {θ : ℝ}
    (hθ : 0 < θ) (hgen : IsGenericMeanSquare (jacobiTwistMeanSquare c) θ) :
    RHTower.zetaZeroAbscissa ≤ min 1 (positiveFormBoundary 2 θ) ∧
      ∀ (u₀ : ℕ) (hgt : 1 < u₀) (hodd : Odd u₀) (hsq : Squarefree u₀),
        @RHTower.zeroAbscissa u₀ ⟨by omega⟩ (jacobiPrimChar u₀ hodd hsq) ≤
          min 1 (positiveFormBoundary 2 θ) := by
  constructor
  · -- Principal square subfamily `u = p²` (`u₀ = 1`).
    have hmean_ζ : ∀ ε : ℝ, 0 < ε → ∃ K Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
        ∀ M Q : ℕ, 1 + 3 ≤ M → 1 ≤ Q →
          (1 : ℝ) * ((Q * M : ℕ) : ℝ) ^ (2 : ℕ) ≤ Z ^ θ →
            (∑ p ∈ RHTower.Sieve.bigPrimeSet M (Q * M),
              ‖twistedMoebiusSum (gaussianKernel c) (fun _ => 1) {p} Z‖ ^ 2) ≤
              K * Z ^ (θ + 1 + ε) := by
      intro ε hε
      obtain ⟨K, Z₀, hZ₀, hK⟩ := hgen ε hε
      refine ⟨K, Z₀, hZ₀, fun Z hZ M Q hM hQ hQM => ?_⟩
      set P := RHTower.Sieve.bigPrimeSet M (Q * M)
      have hinj : Set.InjOn (fun p : ℕ => p ^ 2) ↑P := by
        intro x _ y _ hxy
        exact Nat.pow_left_injective (by norm_num) hxy
      have hmaps : Set.MapsTo (fun p : ℕ => p ^ 2) ↑P ↑((Finset.Icc 1 ⌊Z ^ θ⌋₊).filter Odd) := by
        intro p hp
        obtain ⟨hIcc, hp_pr⟩ := Finset.mem_filter.mp hp
        obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hIcc
        have hp_odd : Odd p := hp_pr.odd_of_ne_two (by omega)
        have hp2_le : p ^ 2 ≤ ⌊Z ^ θ⌋₊ := by
          refine Nat.le_floor ?_
          have h1 : ((p ^ 2 : ℕ) : ℝ) ≤ ((Q * M : ℕ) : ℝ) ^ (2 : ℕ) := by
            push_cast; exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hhi) 2
          linarith
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by positivity, hp2_le⟩, hp_odd.pow⟩
      have hterm_eq : ∀ p ∈ P,
          ‖twistedMoebiusSum (gaussianKernel c) (fun _ => 1) {p} Z‖ ^ 2 =
            ‖jacobiTwistSum c (p ^ 2) Z‖ ^ 2 := by
        intro p hp
        obtain ⟨hIcc, hp_pr⟩ := Finset.mem_filter.mp hp
        have hp_odd : Odd p := hp_pr.odd_of_ne_two (by omega)
        have h1 := jacobiTwistSum_mul_sq_eq c odd_one hp_odd Z
        simp only [one_mul, jacobiSym.one_right, Int.cast_one, hp_pr.primeFactors] at h1
        rw [h1]
      calc ∑ p ∈ P, ‖twistedMoebiusSum (gaussianKernel c) (fun _ => 1) {p} Z‖ ^ 2
          = ∑ p ∈ P, ‖jacobiTwistSum c (p ^ 2) Z‖ ^ 2 := Finset.sum_congr rfl hterm_eq
        _ = ∑ u ∈ P.image (fun p => p ^ 2), ‖jacobiTwistSum c u Z‖ ^ 2 :=
            (Finset.sum_image fun x hx y hy hxy => hinj hx hy hxy).symm
        _ ≤ jacobiTwistMeanSquare c θ Z :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.image_subset_iff.mpr fun p hp => hmaps hp) (fun _ _ _ => sq_nonneg _)
        _ ≤ K * Z ^ (θ + 1 + ε) := hK Z hZ
    exact abscissa_le_positiveFormBoundary_of_primeWindow_meanSquare
      (isSmoothCutoff_gaussianKernel c) (fun _ => by simp) (fun _ _ _ _ => by simp)
      (by norm_num) le_rfl RHTower.half_le_zetaZeroAbscissa RHTower.zetaZeroAbscissa_le_one
      (fun β h1 h2 h3 => by
        obtain ⟨C, hC, hbd⟩ := exists_signal_zetaGaussianKernel_le_of_zeroFree
          RHTower.half_le_zetaZeroAbscissa RHTower.zetaZeroAbscissa_le_one
          (fun _ hz => RHTower.riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hz) c h1 h2 h3
        exact ⟨C, hC, fun X hX => by
          rw [← signal_zetaGaussianKernel_eq_twistedMoebiusSum c hX]; exact hbd X hX⟩)
      (fun b K Z₁ hb hZ₁ hK => by
        obtain ⟨ρ, hzero, hre⟩ := RHTower.exists_zetaZero_lt_re hb
        have hρ1 : ρ ≠ 1 := fun h1 => riemannZeta_one_ne_zero (h1 ▸ hzero)
        exact riemannZeta_ne_zero_of_signal_zetaGaussianKernel_le (c := c) (b := b) (K := K)
          (Z₀ := Z₁) (hb.trans_le RHTower.zetaZeroAbscissa_le_one) (by linarith)
          (fun Z hZ => by
            rw [signal_zetaGaussianKernel_eq_twistedMoebiusSum c (by linarith)]; exact hK Z hZ)
          ρ hre hρ1 hzero)
      hθ hmean_ζ
  · -- Fixed-core square subfamily `u = u₀ p²` (`u₀ > 1` odd squarefree).
    intro u₀ hgt hodd hsq
    letI : NeZero u₀ := ⟨by omega⟩
    set χ₀ := jacobiPrimChar u₀ hodd hsq
    have hprim : χ₀.IsPrimitive := jacobiPrimChar_isPrimitive hodd hsq
    have hne1 : χ₀ ≠ 1 := jacobiPrimChar_ne_one hgt hodd hsq
    have hχ_eq : (fun m : ℕ => (jacobiSym (m : ℤ) u₀ : ℂ)) = fun m : ℕ => χ₀ m := by
      funext m
      simpa using (jacobiPrimChar_intCast_eq_jacobi hodd hsq (m : ℤ)).symm
    have hmean_χ : ∀ ε : ℝ, 0 < ε → ∃ K Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
        ∀ M Q : ℕ, u₀ + 3 ≤ M → 1 ≤ Q →
          (u₀ : ℝ) * ((Q * M : ℕ) : ℝ) ^ (2 : ℕ) ≤ Z ^ θ →
            (∑ p ∈ RHTower.Sieve.bigPrimeSet M (Q * M),
              ‖twistedMoebiusSum (gaussianKernel c) (fun m => χ₀ m) {p} Z‖ ^ 2) ≤
              K * Z ^ (θ + 1 + ε) := by
      intro ε hε
      obtain ⟨K, Z₀, hZ₀, hK⟩ := hgen ε hε
      refine ⟨K, Z₀, hZ₀, fun Z hZ M Q hM hQ hQM => ?_⟩
      set P := RHTower.Sieve.bigPrimeSet M (Q * M)
      have hinj : Set.InjOn (fun p : ℕ => u₀ * p ^ 2) ↑P := by
        intro x _ y _ hxy
        exact Nat.pow_left_injective (by norm_num) (Nat.eq_of_mul_eq_mul_left (by omega) hxy)
      have hmaps : Set.MapsTo (fun p : ℕ => u₀ * p ^ 2) ↑P
          ↑((Finset.Icc 1 ⌊Z ^ θ⌋₊).filter Odd) := by
        intro p hp
        obtain ⟨hIcc, hp_pr⟩ := Finset.mem_filter.mp hp
        obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hIcc
        have hp_odd : Odd p := hp_pr.odd_of_ne_two (by omega)
        have hu_le : u₀ * p ^ 2 ≤ ⌊Z ^ θ⌋₊ := by
          refine Nat.le_floor ?_
          have h1 : ((u₀ * p ^ 2 : ℕ) : ℝ) ≤ (u₀ : ℝ) * ((Q * M : ℕ) : ℝ) ^ (2 : ℕ) := by
            push_cast
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hhi) 2) (by positivity)
          linarith
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨by positivity, hu_le⟩, hodd.mul hp_odd.pow⟩
      have hterm_eq : ∀ p ∈ P,
          ‖twistedMoebiusSum (gaussianKernel c) (fun m => χ₀ m) {p} Z‖ ^ 2 =
            ‖jacobiTwistSum c (u₀ * p ^ 2) Z‖ ^ 2 := by
        intro p hp
        obtain ⟨hIcc, hp_pr⟩ := Finset.mem_filter.mp hp
        have hp_odd : Odd p := hp_pr.odd_of_ne_two (by omega)
        have h1 := jacobiTwistSum_mul_sq_eq c hodd hp_odd Z
        rw [hχ_eq, hp_pr.primeFactors] at h1
        rw [h1]
      calc ∑ p ∈ P, ‖twistedMoebiusSum (gaussianKernel c) (fun m => χ₀ m) {p} Z‖ ^ 2
          = ∑ p ∈ P, ‖jacobiTwistSum c (u₀ * p ^ 2) Z‖ ^ 2 := Finset.sum_congr rfl hterm_eq
        _ = ∑ u ∈ P.image (fun p => u₀ * p ^ 2), ‖jacobiTwistSum c u Z‖ ^ 2 :=
            (Finset.sum_image fun x hx y hy hxy => hinj hx hy hxy).symm
        _ ≤ jacobiTwistMeanSquare c θ Z :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.image_subset_iff.mpr fun p hp => hmaps hp) (fun _ _ _ => sq_nonneg _)
        _ ≤ K * Z ^ (θ + 1 + ε) := hK Z hZ
    exact abscissa_le_positiveFormBoundary_of_primeWindow_meanSquare
      (isSmoothCutoff_gaussianKernel c)
      (fun m => RHTower.norm_dirichletCharacter_le_one χ₀ m)
      (fun p _ k _ => by push_cast; exact map_mul χ₀ p k)
      (by norm_num) (by omega)
      (RHTower.half_le_zeroAbscissa hne1 hprim) (RHTower.zeroAbscissa_le_one hne1 hprim)
      (fun β h1 h2 h3 => by
        obtain ⟨C_sig, hC_sig, hbd⟩ := exists_uniform_signal_dirichletGaussianKernel_le c
          (by linarith : 0 < β - RHTower.zeroAbscissa χ₀)
          (by linarith : β - RHTower.zeroAbscissa χ₀ < 1) one_pos
        refine ⟨C_sig * (u₀ : ℝ) ^ (1 : ℝ), by positivity, fun X hX => ?_⟩
        rw [← signal_dirichletGaussianKernel_eq_twistedMoebiusSum χ₀ c hX]
        exact hbd u₀ χ₀ hne1 hprim β (by linarith) h3 X hX)
      (fun b K Z₁ hb hZ₁ hK => by
        obtain ⟨ρ, hzero, hre⟩ := RHTower.exists_zero_lt_re hne1 hprim hb
        exact LFunction_ne_zero_of_signal_dirichletGaussianKernel_le hne1 (c := c) (b := b)
          (K := K) (Z₀ := Z₁) (hb.trans_le (RHTower.zeroAbscissa_le_one hne1 hprim))
          (by linarith) (fun Z hZ => by
            rw [signal_dirichletGaussianKernel_eq_twistedMoebiusSum χ₀ c (by linarith)]
            exact hK Z hZ) ρ hre hzero)
      hθ hmean_χ

/-- **Sufficiency of quadratic GRH for the full Jacobi twist family.** If `RiemannHypothesis` holds
and every odd squarefree `u₀ > 1` has `zeroAbscissa (jacobiPrimChar u₀) = 1/2`, then
`jacobiTwistMeanSquare c` is generic for every `θ ≥ 0`. -/
theorem isGenericMeanSquare_jacobiTwist_of_quadraticGRH (c : ℝ)
    (hRH : RiemannHypothesis)
    (hGRH : ∀ (u₀ : ℕ) (hgt : 1 < u₀) (hodd : Odd u₀) (hsq : Squarefree u₀),
      @RHTower.zeroAbscissa u₀ ⟨by omega⟩ (jacobiPrimChar u₀ hodd hsq) = 1 / 2)
    {θ : ℝ} (hθ0 : 0 ≤ θ) :
    IsGenericMeanSquare (jacobiTwistMeanSquare c) θ := by
  intro ε hε
  set δ : ℝ := min (1 / 2) (ε / 6)
  have hδ_pos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ_lt1 : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hδ_le : δ ≤ ε / 6 := min_le_right _ _
  set η : ℝ := ε / (8 * (θ + 1))
  have hη_pos : 0 < η := div_pos hε (by positivity)
  set b : ℝ := 1 / 2 + δ
  have hb_le2 : b ≤ 2 := by simp [b]; linarith [min_le_left (1 / 2) (ε / 6)]
  have hΘ_ζ : RHTower.zetaZeroAbscissa = 1 / 2 :=
    riemannHypothesis_iff_zetaZeroAbscissa_eq_half.mp hRH
  obtain ⟨C_ζ, hC_ζ, hbd_ζ⟩ := exists_signal_zetaGaussianKernel_le_of_zeroFree
    RHTower.half_le_zetaZeroAbscissa RHTower.zetaZeroAbscissa_le_one
    (fun _ hz => RHTower.riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hz) c
    (by simp [b, hΘ_ζ]; linarith) (by simp [b, hΘ_ζ]; linarith) hb_le2
  obtain ⟨C_dir, hC_dir, hbd_dir⟩ :=
    exists_uniform_signal_dirichletGaussianKernel_le c hδ_pos hδ_lt1 hη_pos
  obtain ⟨C_η, hC_η, heuler⟩ := exists_eulerProd_primeFactors_le_rpow hη_pos
  set C_all : ℝ := max C_ζ C_dir * C_η
  have hC_all : 0 < C_all := by positivity
  refine ⟨C_all ^ 2, 1, le_rfl, fun Z hZ => ?_⟩
  have hZ_pos : 0 < Z := by linarith
  have hterm_le : ∀ u ∈ (Finset.Icc 1 ⌊Z ^ θ⌋₊).filter Odd,
      ‖jacobiTwistSum c u Z‖ ^ 2 ≤ C_all ^ 2 * Z ^ (2 * b + 4 * θ * η) := by
    intro u hu
    obtain ⟨hIcc, hu_odd⟩ := Finset.mem_filter.mp hu
    obtain ⟨hu1, hu_hi⟩ := Finset.mem_Icc.mp hIcc
    obtain ⟨u₀, a, hu₀_pos, ha_pos, ha2_mul, hu₀_sq⟩ :=
      (Nat.sq_mul_squarefree_of_pos (by omega : 0 < u)).elim fun u₀ h1 =>
        h1.elim fun a h2 => ⟨u₀, a, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2⟩
    have hu_eq : u = u₀ * a ^ 2 := by rw [← ha2_mul, mul_comm]
    have hu₀_odd : Odd u₀ := hu_odd.of_dvd_nat ⟨a ^ 2, hu_eq⟩
    have ha_odd : Odd a := by
      have ha2_odd : Odd (a ^ 2) := hu_odd.of_dvd_nat ⟨u₀, by rw [hu_eq, mul_comm]⟩
      by_contra hnot
      have hev : Even a := Nat.not_odd_iff_even.mp hnot
      exact (Nat.not_even_iff_odd.mpr ha2_odd) (hev.pow_of_ne_zero (by norm_num))
    have hu_le_Zθ : (u : ℝ) ≤ Z ^ θ := (Nat.le_floor_iff (by positivity)).mp hu_hi
    have hu₀_le_Zθ : (u₀ : ℝ) ≤ Z ^ θ := by
      have : u₀ ≤ u := by rw [hu_eq]; exact Nat.le_mul_of_pos_right _ (by positivity)
      exact (by exact_mod_cast this : (u₀ : ℝ) ≤ u).trans hu_le_Zθ
    have ha_le_Zθ : (a : ℝ) ≤ Z ^ θ := by
      have : a ≤ u := by
        calc a ≤ a ^ 2 := by nlinarith
          _ ≤ u₀ * a ^ 2 := Nat.le_mul_of_pos_left _ hu₀_pos
          _ = u := hu_eq.symm
      exact (by exact_mod_cast this : (a : ℝ) ≤ u).trans hu_le_Zθ
    have hu₀η : (u₀ : ℝ) ^ η ≤ Z ^ (θ * η) :=
      (Real.rpow_le_rpow (by positivity) hu₀_le_Zθ hη_pos.le).trans_eq (Real.rpow_mul hZ_pos.le θ η).symm
    have haη : (a : ℝ) ^ η ≤ Z ^ (θ * η) :=
      (Real.rpow_le_rpow (by positivity) ha_le_Zθ hη_pos.le).trans_eq (Real.rpow_mul hZ_pos.le θ η).symm
    have hbase_u₀ : ∀ X : ℝ, 0 < X →
        ‖twistedMoebiusSum (gaussianKernel c) (fun m => (jacobiSym (m : ℤ) u₀ : ℂ)) ∅ X‖ ≤
          (max C_ζ C_dir * (u₀ : ℝ) ^ η) * X ^ b := by
      rcases eq_or_lt_of_le (show 1 ≤ u₀ by omega) with rfl | hgt
      · intro X hX
        simp only [jacobiSym.one_right, Int.cast_one, Nat.cast_one, Real.one_rpow, mul_one]
        rw [← signal_zetaGaussianKernel_eq_twistedMoebiusSum c hX]
        exact (hbd_ζ X hX).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      · intro X hX
        letI : NeZero u₀ := ⟨by omega⟩
        set χ₀ := jacobiPrimChar u₀ hu₀_odd hu₀_sq
        have hprim : χ₀.IsPrimitive := jacobiPrimChar_isPrimitive hu₀_odd hu₀_sq
        have hne1 : χ₀ ≠ 1 := jacobiPrimChar_ne_one hgt hu₀_odd hu₀_sq
        have hχ_eq : (fun m : ℕ => (jacobiSym (m : ℤ) u₀ : ℂ)) = fun m : ℕ => χ₀ m := by
          funext m; simpa using (jacobiPrimChar_intCast_eq_jacobi hu₀_odd hu₀_sq (m : ℤ)).symm
        rw [hχ_eq, ← signal_dirichletGaussianKernel_eq_twistedMoebiusSum χ₀ c hX]
        have hΘ_u₀ := hGRH u₀ hgt hu₀_odd hu₀_sq
        exact (hbd_dir u₀ χ₀ hne1 hprim b (by simp [b, hΘ_u₀]) hb_le2 X hX).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (by positivity))
    have hnorm_u : ‖jacobiTwistSum c u Z‖ ≤ C_all * Z ^ (b + 2 * θ * η) := by
      rw [hu_eq, jacobiTwistSum_mul_sq_eq c hu₀_odd ha_odd Z]
      have h1 := norm_twistedMoebiusSum_le_of_base_le (isSmoothCutoff_gaussianKernel c)
        (fun m => by
          rcases jacobiSym.trichotomy (m : ℤ) u₀ with h | h | h <;> simp [h])
        (fun p _ k _ => by push_cast; rw [jacobiSym.mul_left]; push_cast; rfl)
        (by simp [b]; linarith) (by positivity) hbase_u₀
        (fun p hp => Nat.prime_of_mem_primeFactors hp) hZ_pos
      have h2 := heuler b (by simp [b]; linarith) a ha_pos
      calc ‖twistedMoebiusSum (gaussianKernel c) (fun m => (jacobiSym (m : ℤ) u₀ : ℂ))
              a.primeFactors Z‖
          ≤ max C_ζ C_dir * (u₀ : ℝ) ^ η *
              (∏ p ∈ a.primeFactors, (1 - (p : ℝ) ^ (-b))⁻¹) * Z ^ b := h1
        _ ≤ max C_ζ C_dir * Z ^ (θ * η) * (C_η * Z ^ (θ * η)) * Z ^ b := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul (mul_le_mul_of_nonneg_left hu₀η (by positivity))
              ((h2.trans (mul_le_mul_of_nonneg_left haη (by positivity))))
              (Finset.prod_nonneg fun p hp => by
                have hq1 : (1 : ℝ) < p :=
                  by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
                have hqr : (p : ℝ) ^ (-b) < 1 :=
                  Real.rpow_lt_one_of_one_lt_of_neg hq1 (by simp [b]; linarith)
                exact inv_nonneg.mpr (by linarith))
              (by positivity)
        _ = C_all * Z ^ (b + 2 * θ * η) := by
            simp only [C_all]
            rw [Real.rpow_add hZ_pos, show 2 * θ * η = θ * η + θ * η by ring,
              Real.rpow_add hZ_pos]
            ring
    calc ‖jacobiTwistSum c u Z‖ ^ 2
        ≤ (C_all * Z ^ (b + 2 * θ * η)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm_u 2
      _ = C_all ^ 2 * Z ^ (2 * b + 4 * θ * η) := by
          rw [mul_pow, ← Real.rpow_natCast (Z ^ (b + 2 * θ * η)) 2, ← Real.rpow_mul hZ_pos.le]
          push_cast; ring
  have hcard : (((Finset.Icc 1 ⌊Z ^ θ⌋₊).filter Odd).card : ℝ) ≤ Z ^ θ := by
    calc (((Finset.Icc 1 ⌊Z ^ θ⌋₊).filter Odd).card : ℝ)
        ≤ ((Finset.Icc 1 ⌊Z ^ θ⌋₊).card : ℝ) :=
          by exact_mod_cast Finset.card_filter_le _ _
      _ ≤ Z ^ θ := by rw [Nat.card_Icc, Nat.add_sub_cancel]; exact Nat.floor_le (by positivity)
  have hexp_total : θ + (2 * b + 4 * θ * η) ≤ θ + 1 + ε := by
    have h4θη : 4 * θ * η ≤ ε / 2 := by
      simp only [η]
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    simp only [b]
    linarith
  calc jacobiTwistMeanSquare c θ Z
      ≤ ∑ _u ∈ (Finset.Icc 1 ⌊Z ^ θ⌋₊).filter Odd, C_all ^ 2 * Z ^ (2 * b + 4 * θ * η) :=
        Finset.sum_le_sum hterm_le
    _ = (((Finset.Icc 1 ⌊Z ^ θ⌋₊).filter Odd).card : ℝ) *
          (C_all ^ 2 * Z ^ (2 * b + 4 * θ * η)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Z ^ θ * (C_all ^ 2 * Z ^ (2 * b + 4 * θ * η)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = C_all ^ 2 * Z ^ (θ + (2 * b + 4 * θ * η)) := by rw [Real.rpow_add hZ_pos]; ring
    _ ≤ C_all ^ 2 * Z ^ (θ + 1 + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexp_total) (by positivity)

/-- **Quadratic GRH biconditional for all `θ ≥ 0`.** The full Jacobi twist mean square is generic
for every `θ ≥ 0` if and only if GRH holds for `ζ` and all odd primitive real Dirichlet
characters. -/
theorem forall_jacobiTwistGeneric_iff_quadraticGRH (c : ℝ) :
    (∀ θ : ℝ, 0 ≤ θ → IsGenericMeanSquare (jacobiTwistMeanSquare c) θ) ↔
      (RiemannHypothesis ∧
        ∀ (u₀ : ℕ) (hgt : 1 < u₀) (hodd : Odd u₀) (hsq : Squarefree u₀),
          @RHTower.zeroAbscissa u₀ ⟨by omega⟩ (jacobiPrimChar u₀ hodd hsq) = 1 / 2) := by
  constructor
  · intro hall
    have hboth : RHTower.zetaZeroAbscissa = 1 / 2 ∧
        ∀ (u₀ : ℕ) (hgt : 1 < u₀) (hodd : Odd u₀) (hsq : Squarefree u₀),
          @RHTower.zeroAbscissa u₀ ⟨by omega⟩ (jacobiPrimChar u₀ hodd hsq) = 1 / 2 := by
      constructor
      · apply le_antisymm _ RHTower.half_le_zetaZeroAbscissa
        refine le_of_forall_pos_le_add fun ε hε => ?_
        have h := (zetaZeroAbscissa_and_jacobiPrimChar_le_of_jacobiTwistGeneric c
          (by positivity : 0 < 4 * ε) (hall (4 * ε) (by positivity))).1
        have hpfb : positiveFormBoundary 2 (4 * ε) = 1 / 2 + ε := by
          unfold positiveFormBoundary; norm_num; ring
        exact (h.trans (min_le_right _ _)).trans_eq hpfb
      · intro u₀ hgt hodd hsq
        letI : NeZero u₀ := ⟨by omega⟩
        apply le_antisymm _ (RHTower.half_le_zeroAbscissa
          (jacobiPrimChar_ne_one hgt hodd hsq) (jacobiPrimChar_isPrimitive hodd hsq))
        refine le_of_forall_pos_le_add fun ε hε => ?_
        have h := (zetaZeroAbscissa_and_jacobiPrimChar_le_of_jacobiTwistGeneric c
          (by positivity : 0 < 4 * ε) (hall (4 * ε) (by positivity))).2 u₀ hgt hodd hsq
        have hpfb : positiveFormBoundary 2 (4 * ε) = 1 / 2 + ε := by
          unfold positiveFormBoundary; norm_num; ring
        exact (h.trans (min_le_right _ _)).trans_eq hpfb
    exact ⟨riemannHypothesis_iff_zetaZeroAbscissa_eq_half.mpr hboth.1, hboth.2⟩
  · rintro ⟨hRH, hGRH⟩ θ hθ0
    exact isGenericMeanSquare_jacobiTwist_of_quadraticGRH c hRH hGRH hθ0

/-- **Infimum-zero biconditional for the full Jacobi twist family.** Arbitrarily short positive
twist exponents `θ → 0⁺` have generic mean square if and only if GRH holds for `ζ` and all odd
primitive real Dirichlet characters. -/
theorem sInf_jacobiTwistGeneric_eq_zero_iff_quadraticGRH (c : ℝ) :
    ((∃ θ : ℝ, 0 < θ ∧ IsGenericMeanSquare (jacobiTwistMeanSquare c) θ) ∧
      sInf {θ : ℝ | 0 < θ ∧ IsGenericMeanSquare (jacobiTwistMeanSquare c) θ} = 0) ↔
      (RiemannHypothesis ∧
        ∀ (u₀ : ℕ) (hgt : 1 < u₀) (hodd : Odd u₀) (hsq : Squarefree u₀),
          @RHTower.zeroAbscissa u₀ ⟨by omega⟩ (jacobiPrimChar u₀ hodd hsq) = 1 / 2) := by
  set S : Set ℝ := {θ : ℝ | 0 < θ ∧ IsGenericMeanSquare (jacobiTwistMeanSquare c) θ}
  constructor
  · rintro ⟨hne, hinf⟩
    have hboth : RHTower.zetaZeroAbscissa = 1 / 2 ∧
        ∀ (u₀ : ℕ) (hgt : 1 < u₀) (hodd : Odd u₀) (hsq : Squarefree u₀),
          @RHTower.zeroAbscissa u₀ ⟨by omega⟩ (jacobiPrimChar u₀ hodd hsq) = 1 / 2 := by
      constructor
      · apply le_antisymm _ RHTower.half_le_zetaZeroAbscissa
        refine le_of_forall_pos_le_add fun ε hε => ?_
        obtain ⟨θ, ⟨hθ_pos, hgen⟩, hθ_lt⟩ :=
          exists_lt_of_csInf_lt hne (by rw [hinf]; positivity : sInf S < 4 * ε)
        have h := (zetaZeroAbscissa_and_jacobiPrimChar_le_of_jacobiTwistGeneric c hθ_pos hgen).1
        have hpfb : positiveFormBoundary 2 θ ≤ 1 / 2 + ε := by
          unfold positiveFormBoundary; norm_num; linarith
        exact (h.trans (min_le_right _ _)).trans hpfb
      · intro u₀ hgt hodd hsq
        letI : NeZero u₀ := ⟨by omega⟩
        apply le_antisymm _ (RHTower.half_le_zeroAbscissa
          (jacobiPrimChar_ne_one hgt hodd hsq) (jacobiPrimChar_isPrimitive hodd hsq))
        refine le_of_forall_pos_le_add fun ε hε => ?_
        obtain ⟨θ, ⟨hθ_pos, hgen⟩, hθ_lt⟩ :=
          exists_lt_of_csInf_lt hne (by rw [hinf]; positivity : sInf S < 4 * ε)
        have h := (zetaZeroAbscissa_and_jacobiPrimChar_le_of_jacobiTwistGeneric c hθ_pos hgen).2
          u₀ hgt hodd hsq
        have hpfb : positiveFormBoundary 2 θ ≤ 1 / 2 + ε := by
          unfold positiveFormBoundary; norm_num; linarith
        exact (h.trans (min_le_right _ _)).trans hpfb
    exact ⟨riemannHypothesis_iff_zetaZeroAbscissa_eq_half.mpr hboth.1, hboth.2⟩
  · rintro ⟨hRH, hGRH⟩
    have hmem : ∀ θ : ℝ, 0 < θ → θ ∈ S := fun θ hθ =>
      ⟨hθ, isGenericMeanSquare_jacobiTwist_of_quadraticGRH c hRH hGRH hθ.le⟩
    refine ⟨⟨1, hmem 1 one_pos⟩, le_antisymm ?_ ?_⟩
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      rw [zero_add]
      exact csInf_le ⟨0, fun x hx => hx.1.le⟩ (hmem ε hε)
    · exact le_csInf ⟨1, hmem 1 one_pos⟩ fun x hx => hx.1.le

end GaloisForLFunctions.FamilyContinuationTheory