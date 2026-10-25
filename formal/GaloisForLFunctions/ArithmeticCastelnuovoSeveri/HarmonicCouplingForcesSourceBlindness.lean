import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MaximalBlindIdealOfTheMeyerSource
import GaloisForLFunctions.HTGeometry.CosinePolynomialPurchaseCap
import GaloisForLFunctions.HTGeometry.FrullaniIntegral
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic
import GaloisForLFunctions.RHTower.VonMangoldtThreeFourOneSeries
import GaloisForLFunctions.RHTower.ZetaResidueFactorDerivative
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegion
import GaloisForLFunctions.RHTower.WeilFullConeRiemannKernelRigidity

/-!
# Harmonic phase coupling and the invariants that force source blindness

Single-channel correspondence-stable positivity on the Meyer source space is
algebraically exhausted by `meyerTraceBoundedIdeal`. Escaping single-channel
blindness requires coupling multiple dilated harmonic channels through the
multiplicative group law `n^{-i k ω} = (n^{-i ω})^k` of the Dirichlet basis.

This module establishes the exact mechanism and sharp invariant structure of
that exit:

1. **Harmonic coupling degree ladder and strict Fejér barrier**:
   - Degree `K = 1` satisfies `a 1 ≤ a 0` for every nonnegative cosine polynomial,
     so two-channel coupling cannot weight an aligned zero strictly above a simple pole.
   - Folded Fejér autocorrelation `fejerAutoCoeff M b` produces nonnegative
     coefficients with `0 ≤ cosinePolynomial (fejerAutoCoeff M b) M θ`, crossing
     `a 0 < a 1` at minimum degree `M = 2` (`(6, 8, 2)`).
   - Every nonzero nonnegative cosine polynomial of any degree `K ≥ 1` obeys the
     strict universal Fejér barrier `a 1 < 2 * a 0`.

2. **All-aperture coupled Weil explicit-formula ceiling**:
   Modulating any nonnegative compactly supported `C²` real profile `f` at
   arbitrary support aperture along `±m ω` makes both the coupled prime sum and
   the coupled critical-line zero sum nonnegative simultaneously, bounding the
   coupled off-line zero sum solely by the pole and archimedean terms.

3. **Universal quantized divisor-order forcing law and Meyer-source exclusion**:
   Harmonic positivity on `σ > 1`, `a 0 < a 1`, simple pole multiplicity
   `μ_pole 0 ≤ 1`, harmonic pole isolation `μ_pole (k * t) = 0`, and integer
   divisor quantization `μ_zero t : ℕ` force `μ_zero t = 0`. Instantiated on `ζ`
   without circular boundary nonvanishing inputs, this excludes boundary zeros
   and, together with derivative growth, excludes `XiDivisorSupport` from both
   reflected de la Vallée Poussin collars inside the open strip.

4. **Sharpness countermodels**:
   - Dropping pole simplicity (`μ_pole 0 = 2`): an explicit Beurling system with
     nonnegative prime density `2 e^t (1 - cos(t0 t)) / t ≥ 0`, exact Euler–Frullani
     representation, and full harmonic positivity at all degrees `K` carries
     zeros `1 ± i t0` on `Re s = 1` that survive every degree `K` by `a 1 < 2 * a 0`.
   - Dropping harmonic pole isolation (`μ_pole (2 t) = 1`): a periodic Euler
     ratio with positive odd-harmonic prime weights and simple pole `μ_pole 0 = 1`
     carries a zero at `1 + i π / ℓ` saturating `a 1 ≤ a 0 + a 2`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped Real ComplexConjugate
open Zeta23

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. Harmonic coupling degree ladder and strict Fejér barrier -/

/-- At coupling degree `K = 1`, nonnegativity of `a 0 + a 1 cos θ` at `θ = π`
forces `a 1 ≤ a 0`: two-channel coupling cannot exceed a simple pole weight. -/
theorem degree_one_cosinePolynomial_le_const {a : ℕ → ℝ}
    (hP : ∀ θ : ℝ, 0 ≤ HTGeometry.cosinePolynomial a 1 θ) :
    a 1 ≤ a 0 := by
  have hpi := hP Real.pi
  unfold HTGeometry.cosinePolynomial at hpi
  rw [Finset.sum_range_succ, Finset.sum_range_one] at hpi
  simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one,
    Nat.cast_one, one_mul, Real.cos_pi, mul_neg] at hpi
  linarith only [hpi]

/-- Symmetric natural distance `|j - k|` on `ℕ`. -/
def natDist (j k : ℕ) : ℕ := (j - k) + (k - j)

/-- Folded Fejér autocorrelation coefficients of a finite profile `b` of degree `M`. -/
def fejerAutoCoeff (M : ℕ) (b : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
    (fun p => natDist p.1 p.2 = m), b p.1 * b p.2

theorem fejerAutoCoeff_nonneg (M : ℕ) {b : ℕ → ℝ}
    (hb : ∀ j ≤ M, 0 ≤ b j) (m : ℕ) :
    0 ≤ fejerAutoCoeff M b m := by
  unfold fejerAutoCoeff
  refine Finset.sum_nonneg fun p hp => ?_
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
  exact mul_nonneg (hb p.1 (by omega)) (hb p.2 (by omega))

private theorem cos_natDist_mul (j k : ℕ) (θ : ℝ) :
    Real.cos ((natDist j k : ℝ) * θ) =
      Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ) +
        Real.sin ((j : ℝ) * θ) * Real.sin ((k : ℝ) * θ) := by
  rw [ ← Real.cos_sub]
  rcases le_total k j with h | h
  · have hd : natDist j k = j - k := by unfold natDist; omega
    rw [hd, Nat.cast_sub h, sub_mul]
  · have hd : natDist j k = k - j := by unfold natDist; omega
    rw [hd, Nat.cast_sub h, ← Real.cos_neg]
    congr 1
    ring

/-- The cosine polynomial of `fejerAutoCoeff M b` is a sum of two real squares,
hence globally nonnegative for every real profile `b`. -/
theorem cosinePolynomial_fejerAutoCoeff (M : ℕ) (b : ℕ → ℝ) (θ : ℝ) :
    HTGeometry.cosinePolynomial (fejerAutoCoeff M b) M θ =
      (∑ j ∈ Finset.range (M + 1), b j * Real.cos ((j : ℝ) * θ)) ^ 2 +
        (∑ j ∈ Finset.range (M + 1), b j * Real.sin ((j : ℝ) * θ)) ^ 2 := by
  let S := Finset.range (M + 1) ×ˢ Finset.range (M + 1)
  have hmaps : (S : Set (ℕ × ℕ)).MapsTo (fun p => natDist p.1 p.2) (Finset.range (M + 1)) := by
    intro p hp
    simp only [S, Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at hp ⊢
    unfold natDist
    omega
  unfold HTGeometry.cosinePolynomial fejerAutoCoeff
  have hfib : (∑ k ∈ Finset.range (M + 1),
      (∑ p ∈ S.filter (fun p => natDist p.1 p.2 = k), b p.1 * b p.2) *
        Real.cos ((k : ℝ) * θ)) =
      ∑ p ∈ S, b p.1 * b p.2 * Real.cos ((natDist p.1 p.2 : ℝ) * θ) := by
    calc
      _ = ∑ k ∈ Finset.range (M + 1),
            ∑ p ∈ S.filter (fun p => natDist p.1 p.2 = k),
              b p.1 * b p.2 * Real.cos ((natDist p.1 p.2 : ℝ) * θ) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [(Finset.mem_filter.mp hp).2]
      _ = _ := Finset.sum_fiberwise_of_maps_to hmaps _
  rw [hfib]
  simp only [S, Finset.sum_product, cos_natDist_mul]
  simp only [sq, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem cosinePolynomial_fejerAutoCoeff_nonneg (M : ℕ) (b : ℕ → ℝ) (θ : ℝ) :
    0 ≤ HTGeometry.cosinePolynomial (fejerAutoCoeff M b) M θ := by
  rw [cosinePolynomial_fejerAutoCoeff]
  positivity

/-- Standard three-point profile `(1, 2, 1)` generating `(6, 8, 2)` at degree `M = 2`. -/
def fejerProfile2 : ℕ → ℝ
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0

theorem fejerProfile2_nonneg (j : ℕ) : 0 ≤ fejerProfile2 j := by
  match j with
  | 0 => norm_num [fejerProfile2]
  | 1 => norm_num [fejerProfile2]
  | 2 => norm_num [fejerProfile2]
  | _ + 3 => norm_num [fejerProfile2]

theorem fejerAutoCoeff_two_zero : fejerAutoCoeff 2 fejerProfile2 0 = 6 := by
  simp only [fejerAutoCoeff, natDist, fejerProfile2, Finset.sum_filter, Finset.sum_product,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem fejerAutoCoeff_two_one : fejerAutoCoeff 2 fejerProfile2 1 = 8 := by
  simp only [fejerAutoCoeff, natDist, fejerProfile2, Finset.sum_filter, Finset.sum_product,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem fejerAutoCoeff_two_two : fejerAutoCoeff 2 fejerProfile2 2 = 2 := by
  simp only [fejerAutoCoeff, natDist, fejerProfile2, Finset.sum_filter, Finset.sum_product,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- Degree `M = 2` crosses the simple-pole threshold `a 0 < a 1` constructively
with nonnegative coefficients and a globally nonnegative cosine polynomial. -/
theorem fejerAutoCoeff_two_const_lt_first :
    fejerAutoCoeff 2 fejerProfile2 0 < fejerAutoCoeff 2 fejerProfile2 1 := by
  rw [fejerAutoCoeff_two_zero, fejerAutoCoeff_two_one]
  norm_num

/-- Strict universal Fejér barrier: every nonnegative cosine polynomial of degree
`K ≥ 1` with `0 < a 0` satisfies the strict inequality `a 1 < 2 * a 0`. -/
theorem cosinePolynomial_purchase_ratio_lt_two {a : ℕ → ℝ} {K : ℕ} (hK : 1 ≤ K)
    (hP : ∀ θ : ℝ, 0 ≤ HTGeometry.cosinePolynomial a K θ) (ha0 : 0 < a 0) :
    a 1 < 2 * a 0 := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hex_pos : ∃ c ∈ Ioo (0 : ℝ) (2 * Real.pi), 0 < HTGeometry.cosinePolynomial a K c := by
    by_contra hall
    push Not at hall
    have heq_oo : EqOn (HTGeometry.cosinePolynomial a K) 0 (Ioo (0 : ℝ) (2 * Real.pi)) :=
      fun c hc => le_antisymm (hall c hc) (hP c)
    have heq_cc : EqOn (HTGeometry.cosinePolynomial a K) 0 (Icc (0 : ℝ) (2 * Real.pi)) := by
      rw [← closure_Ioo (ne_of_lt h2pi)]
      exact heq_oo.closure (HTGeometry.continuous_cosinePolynomial a K) continuous_const
    have hint0 : ∫ θ in (0 : ℝ)..(2 * Real.pi), HTGeometry.cosinePolynomial a K θ = 0 := by
      have hcongr : ∫ θ in (0 : ℝ)..(2 * Real.pi), HTGeometry.cosinePolynomial a K θ =
          ∫ _ in (0 : ℝ)..(2 * Real.pi), (0 : ℝ) := by
        refine intervalIntegral.integral_congr fun θ hθ => ?_
        rw [uIcc_of_le h2pi.le] at hθ
        exact heq_cc hθ
      rw [hcongr, intervalIntegral.integral_zero]
    rw [HTGeometry.integral_cosinePolynomial] at hint0
    nlinarith only [hint0, Real.pi_pos, ha0]
  obtain ⟨c, hc, hPc⟩ := hex_pos
  have h1cos_pos : 0 < 1 - Real.cos c := by
    have hsin : 0 < Real.sin (c / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith only [hc.1]) (by linarith only [hc.2])
    have hcos_eq : 1 - Real.cos c = 2 * Real.sin (c / 2) ^ 2 := by
      have hc2 : c = 2 * (c / 2) := by ring
      nth_rw 1 [hc2]
      rw [Real.cos_two_mul, ← Real.sin_sq_add_cos_sq (c / 2)]
      ring
    rw [hcos_eq]
    positivity
  let g : ℝ → ℝ := fun θ => (1 - Real.cos θ) * HTGeometry.cosinePolynomial a K θ
  have hgc : Continuous g :=
    (continuous_const.sub Real.continuous_cos).mul (HTGeometry.continuous_cosinePolynomial a K)
  have hpos_int : 0 < ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ := by
    have h0 := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt h2pi
      continuousOn_const hgc.continuousOn
      (fun θ _ => mul_nonneg (by linarith [Real.cos_le_one θ]) (hP θ))
      ⟨c, Ioo_subset_Icc_self hc, mul_pos h1cos_pos hPc⟩
    simpa only [intervalIntegral.integral_zero] using h0
  have hsplit : ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ =
      (∫ θ in (0 : ℝ)..(2 * Real.pi), HTGeometry.cosinePolynomial a K θ) -
        ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ * HTGeometry.cosinePolynomial a K θ := by
    have hi1 : IntervalIntegrable (HTGeometry.cosinePolynomial a K) volume 0 (2 * Real.pi) :=
      (HTGeometry.continuous_cosinePolynomial a K).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun θ => Real.cos θ * HTGeometry.cosinePolynomial a K θ)
        volume 0 (2 * Real.pi) :=
      (Real.continuous_cos.mul (HTGeometry.continuous_cosinePolynomial a K)).intervalIntegrable _ _
    rw [← intervalIntegral.integral_sub hi1 hi2]
    congr 1
    funext θ
    dsimp only [g]
    ring
  rw [hsplit, HTGeometry.integral_cosinePolynomial,
    HTGeometry.integral_cos_mul_cosinePolynomial a hK] at hpos_int
  nlinarith only [hpos_int, Real.pi_pos]

/-! ### 2. All-aperture harmonic-coupled Weil explicit-formula ceiling -/

/-- Frequency-modulated complexification `f(t) e^{i s t}` of a real profile. -/
def modCx (s : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℂ := cx f t * Complex.exp (I * (s : ℂ) * (t : ℂ))

theorem modCx_contDiff {s : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (modCx s f) :=
  (cx_contDiff hf).mul ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp)

theorem modCx_hasCompactSupport {s : ℝ} {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (modCx s f) :=
  (cx_hasCompactSupport hfc).mul_right

theorem weilTest_cx_eq_ofReal (f : ℝ → ℝ) (u : ℝ) :
    EF.weilTest (cx f) (cx f) u = ((∫ t : ℝ, f t * f (t - u) : ℝ) : ℂ) := by
  rw [_root_.RHTower.WeilSpectral.weilTest_apply, ← integral_complex_ofReal]
  congr 1
  funext t
  simp only [cx, Complex.conj_ofReal, Complex.ofReal_mul]

theorem weilTest_cx_re_nonneg {f : ℝ → ℝ} (hf_pos : ∀ t : ℝ, 0 ≤ f t) (u : ℝ) :
    0 ≤ (EF.weilTest (cx f) (cx f) u).re := by
  rw [weilTest_cx_eq_ofReal, Complex.ofReal_re]
  exact integral_nonneg fun t => mul_nonneg (hf_pos t) (hf_pos (t - u))

theorem weilTest_cx_im_eq_zero (f : ℝ → ℝ) (u : ℝ) :
    (EF.weilTest (cx f) (cx f) u).im = 0 := by
  rw [weilTest_cx_eq_ofReal, Complex.ofReal_im]

private theorem weilTest_modCx (s : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    EF.weilTest (modCx s f) (modCx s f) u =
      Complex.exp (I * (s : ℂ) * (u : ℂ)) * EF.weilTest (cx f) (cx f) u := by
  rw [_root_.RHTower.WeilSpectral.weilTest_apply, _root_.RHTower.WeilSpectral.weilTest_apply,
    ← integral_const_mul]
  congr 1
  funext t
  simp only [modCx]
  rw [map_mul, ← Complex.exp_conj]
  have hc : conj (I * (s : ℂ) * ((t - u : ℝ) : ℂ)) = -(I * (s : ℂ) * ((t - u : ℝ) : ℂ)) := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hc]
  have he : Complex.exp (I * (s : ℂ) * (t : ℂ)) *
      Complex.exp (-(I * (s : ℂ) * ((t - u : ℝ) : ℂ))) =
      Complex.exp (I * (s : ℂ) * (u : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (cx f t * conj (cx f (t - u))) * he

private theorem weilTest_modCx_pair (s : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    ((1 / 2 : ℝ) : ℂ) *
      (EF.weilTest (modCx s f) (modCx s f) u + EF.weilTest (modCx (-s) f) (modCx (-s) f) u) =
      (Real.cos (s * u) : ℂ) * EF.weilTest (cx f) (cx f) u := by
  rw [weilTest_modCx, weilTest_modCx]
  have hcos : ((1 / 2 : ℝ) : ℂ) *
      (Complex.exp (I * (s : ℂ) * (u : ℂ)) + Complex.exp (I * ((-s : ℝ) : ℂ) * (u : ℂ))) =
      (Real.cos (s * u) : ℂ) := by
    rw [Complex.ofReal_cos, show ((s * u : ℝ) : ℂ) = (s : ℂ) * (u : ℂ) by push_cast; ring,
      Complex.cos]
    have h1 : I * (s : ℂ) * (u : ℂ) = (s : ℂ) * (u : ℂ) * I := by ring
    have h2 : I * ((-s : ℝ) : ℂ) * (u : ℂ) = -((s : ℂ) * (u : ℂ) * I) := by push_cast; ring
    rw [h1, h2]
    push_cast
    ring
  calc
    ((1 / 2 : ℝ) : ℂ) * (Complex.exp (I * (s : ℂ) * u) * EF.weilTest (cx f) (cx f) u +
        Complex.exp (I * ((-s : ℝ) : ℂ) * u) * EF.weilTest (cx f) (cx f) u)
      = (((1 / 2 : ℝ) : ℂ) *
          (Complex.exp (I * (s : ℂ) * u) + Complex.exp (I * ((-s : ℝ) : ℂ) * u))) *
          EF.weilTest (cx f) (cx f) u := by ring
    _ = (Real.cos (s * u) : ℂ) * EF.weilTest (cx f) (cx f) u := by rw [hcos]

/-- Coupled autocorrelation kernel formed from harmonics `±m ω` (`0 ≤ m ≤ M`). -/
def harmonicCoupledKernel (M : ℕ) (c : ℕ → ℝ) (ω : ℝ) (f : ℝ → ℝ) : ℝ → ℂ :=
  ∑ m ∈ Finset.range (M + 1),
    ((c m / 2 : ℝ) : ℂ) •
      (EF.weilTest (modCx ((m : ℝ) * ω) f) (modCx ((m : ℝ) * ω) f) +
        EF.weilTest (modCx (-((m : ℝ) * ω)) f) (modCx (-((m : ℝ) * ω)) f))

/-- Pointwise factorization of the coupled autocorrelation kernel into the cosine
polynomial times the unmodulated real autocorrelation. -/
theorem harmonicCoupledKernel_apply (M : ℕ) (c : ℕ → ℝ) (ω : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    harmonicCoupledKernel M c ω f u =
      (HTGeometry.cosinePolynomial c M (ω * u) : ℂ) * EF.weilTest (cx f) (cx f) u := by
  unfold harmonicCoupledKernel HTGeometry.cosinePolynomial
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hsplit : ((c m / 2 : ℝ) : ℂ) = (c m : ℂ) * ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have hmul : (m : ℝ) * ω * u = (m : ℝ) * (ω * u) := by ring
  rw [hsplit, mul_assoc, weilTest_modCx_pair, hmul, ← mul_assoc]

theorem harmonicCoupledKernel_hasCompactSupport (M : ℕ) (c : ℕ → ℝ) (ω : ℝ)
    {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (harmonicCoupledKernel M c ω f) := by
  unfold harmonicCoupledKernel
  refine HasCompactSupport.finset_sum _ fun m _ => ?_
  have hp := modCx_hasCompactSupport (s := (m : ℝ) * ω) hfc
  have hm := modCx_hasCompactSupport (s := -((m : ℝ) * ω)) hfc
  exact ((EF.weilTest_hasCompactSupport hp hp).add
    (EF.weilTest_hasCompactSupport hm hm)).smul_left

/-- Harmonic-coupled zero-side Weil sum across harmonics `±m ω`. -/
def harmonicCoupledZeroSide (M : ℕ) (c : ℕ → ℝ) (ω : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (M + 1), (c m / 2) *
    ((zetaZeroConfig.W (modCx ((m : ℝ) * ω) f) (modCx ((m : ℝ) * ω) f)).re +
      (zetaZeroConfig.W (modCx (-((m : ℝ) * ω)) f) (modCx (-((m : ℝ) * ω)) f)).re)

/-- Harmonic-coupled pole and archimedean gamma functional. -/
def harmonicCoupledPoleGamma (M : ℕ) (c : ℕ → ℝ) (ω : ℝ) (f : ℝ → ℝ) : ℝ :=
  (paperFT (harmonicCoupledKernel M c ω f) (I / 2) +
    paperFT (harmonicCoupledKernel M c ω f) (-I / 2) +
    (1 / (2 * Real.pi) : ℂ) *
      ∫ r : ℝ, paperFT (harmonicCoupledKernel M c ω f) r * (EF.gammaBracket r : ℂ)).re

/-- Harmonic-coupled prime-power sum at arbitrary support aperture. -/
def harmonicCoupledPrimeSum (M : ℕ) (c : ℕ → ℝ) (ω : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∑' n : ℕ,
    ((if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0 : ℝ) : ℂ) *
      (harmonicCoupledKernel M c ω f (Real.log n) +
        harmonicCoupledKernel M c ω f (-Real.log n))).re

/-- Explicit formula for the harmonic-coupled zero sum. -/
theorem harmonicCoupledZeroSide_eq_poleGamma_sub_primes (M : ℕ) (c : ℕ → ℝ) (ω : ℝ)
    {f : ℝ → ℝ} (hf : f ∈ realTests) :
    harmonicCoupledZeroSide M c ω f =
      harmonicCoupledPoleGamma M c ω f - harmonicCoupledPrimeSum M c ω f := by
  let lam : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ)
  have hadm (s : ℝ) : _root_.RHTower.WeilSpectral.Admissible
      (EF.weilTest (modCx s f) (modCx s f)) :=
    _root_.RHTower.OddResolvent.admissible_weilTest_mixed
      (modCx_contDiff hf.1) (modCx_hasCompactSupport hf.2)
      (modCx_contDiff hf.1) (modCx_hasCompactSupport hf.2)
  have hW_eq : harmonicCoupledZeroSide M c ω f =
      (_root_.RHTower.weilFullFunctional lam (harmonicCoupledKernel M c ω f)).re := by
    unfold harmonicCoupledZeroSide harmonicCoupledKernel
    rw [_root_.RHTower.WeilSpectral.weilFullFunctional_sum lam (Finset.range (M + 1)) fun m _ =>
      ((hadm ((m : ℝ) * ω)).add (hadm (-((m : ℝ) * ω)))).smul _]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [_root_.RHTower.WeilSpectral.weilFullFunctional_smul,
      _root_.RHTower.WeilSpectral.weilFullFunctional_add lam
        (hadm ((m : ℝ) * ω)) (hadm (-((m : ℝ) * ω))),
      ← _root_.RHTower.zeta_W_eq_weilFullFunctional
        (modCx_contDiff hf.1) (modCx_hasCompactSupport hf.2),
      ← _root_.RHTower.zeta_W_eq_weilFullFunctional
        (modCx_contDiff hf.1) (modCx_hasCompactSupport hf.2),
      Complex.re_ofReal_mul, Complex.add_re]
  rw [hW_eq]
  unfold _root_.RHTower.weilFullFunctional harmonicCoupledPoleGamma harmonicCoupledPrimeSum
  dsimp only [lam]
  have hrearrange :
      paperFT (harmonicCoupledKernel M c ω f) (I / 2) +
        paperFT (harmonicCoupledKernel M c ω f) (-I / 2) -
        (∑' n : ℕ,
          ((if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0 : ℝ) : ℂ) *
            (harmonicCoupledKernel M c ω f (Real.log n) +
              harmonicCoupledKernel M c ω f (-Real.log n))) +
        (1 / (2 * Real.pi) : ℂ) *
          ∫ r : ℝ, paperFT (harmonicCoupledKernel M c ω f) r * (EF.gammaBracket r : ℂ) =
      (paperFT (harmonicCoupledKernel M c ω f) (I / 2) +
        paperFT (harmonicCoupledKernel M c ω f) (-I / 2) +
        (1 / (2 * Real.pi) : ℂ) *
          ∫ r : ℝ, paperFT (harmonicCoupledKernel M c ω f) r * (EF.gammaBracket r : ℂ)) -
        ∑' n : ℕ,
          ((if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0 : ℝ) : ℂ) *
            (harmonicCoupledKernel M c ω f (Real.log n) +
              harmonicCoupledKernel M c ω f (-Real.log n)) := by ring
  rw [hrearrange, Complex.sub_re]

/-- All-aperture prime-sum positivity: for any nonnegative `f ∈ realTests` at any
support radius and any nonnegative cosine polynomial, the coupled prime sum is
nonnegative. No narrow-support restriction `r ≤ 3 / 10` is needed. -/
theorem harmonicCoupledPrimeSum_nonneg (M : ℕ) {c : ℕ → ℝ} (ω : ℝ) {f : ℝ → ℝ}
    (hf : f ∈ realTests) (hf_pos : ∀ t : ℝ, 0 ≤ f t)
    (hP : ∀ θ : ℝ, 0 ≤ HTGeometry.cosinePolynomial c M θ) :
    0 ≤ harmonicCoupledPrimeSum M c ω f := by
  unfold harmonicCoupledPrimeSum
  have hsum := _root_.RHTower.summable_primeAtoms
    (fun n => if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0)
    (harmonicCoupledKernel_hasCompactSupport M c ω hf.2)
  rw [Complex.re_tsum hsum]
  refine tsum_nonneg fun n => ?_
  rw [Complex.re_ofReal_mul]
  have ha : 0 ≤ (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0) := by
    split_ifs with h2
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    · exact le_rfl
  refine mul_nonneg ha ?_
  rw [Complex.add_re, harmonicCoupledKernel_apply, harmonicCoupledKernel_apply,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  exact add_nonneg (mul_nonneg (hP _) (weilTest_cx_re_nonneg hf_pos _))
    (mul_nonneg (hP _) (weilTest_cx_re_nonneg hf_pos _))

/-- Summability of the Weil zero series for any compactly supported `C²` test. -/
theorem summable_Wsummand_zetaZeroConfig {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    Summable (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand g g ρ) := by
  let k := EF.weilTest g g
  obtain ⟨hs, -⟩ := WeilEF.EF_lit_zetaZeroConfig k
    (EF.weilTest_contDiff hg hg.continuous hgc) (EF.weilTest_hasCompactSupport hgc hgc)
  have hfac := EF.paperFT_weilTest hg.continuous hg.continuous hgc hgc
  refine hs.congr fun ρ => ?_
  simp only [ZeroConfig.Wsummand, k, hfac, mul_assoc]

/-- Off-line component of the harmonic-coupled zero sum. -/
def harmonicCoupledOffLineZeroSide (M : ℕ) (c : ℕ → ℝ) (ω : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (M + 1), (c m / 2) *
    ((∑' ρ : {ρ : zetaZeroConfig.carrier | (ρ : ℂ).re ≠ 1 / 2},
        (zetaZeroConfig.Wsummand (modCx ((m : ℝ) * ω) f) (modCx ((m : ℝ) * ω) f) ρ.1).re) +
     (∑' ρ : {ρ : zetaZeroConfig.carrier | (ρ : ℂ).re ≠ 1 / 2},
        (zetaZeroConfig.Wsummand (modCx (-((m : ℝ) * ω)) f) (modCx (-((m : ℝ) * ω)) f) ρ.1).re))

/-- All-aperture off-line zero ceiling: when `f ≥ 0`, `cosinePolynomial c M ≥ 0`,
and `c m ≥ 0` (e.g. `c = fejerAutoCoeff M b` for `b ≥ 0`), both primes and all
critical-line zeros have nonnegative coupled weight, so the off-line zero sum is
bounded unconditionally by `harmonicCoupledPoleGamma M c ω f` at every aperture. -/
theorem harmonicCoupledOffLineZeroSide_le_poleGamma (M : ℕ) {c : ℕ → ℝ} (ω : ℝ) {f : ℝ → ℝ}
    (hf : f ∈ realTests) (hf_pos : ∀ t : ℝ, 0 ≤ f t)
    (hc_pos : ∀ m ≤ M, 0 ≤ c m)
    (hP : ∀ θ : ℝ, 0 ≤ HTGeometry.cosinePolynomial c M θ) :
    harmonicCoupledOffLineZeroSide M c ω f ≤ harmonicCoupledPoleGamma M c ω f := by
  have hoff_le_full : harmonicCoupledOffLineZeroSide M c ω f ≤
      harmonicCoupledZeroSide M c ω f := by
    unfold harmonicCoupledOffLineZeroSide harmonicCoupledZeroSide
    refine Finset.sum_le_sum fun m hm => ?_
    have hm_le : m ≤ M := by rw [Finset.mem_range] at hm; omega
    have hcm : 0 ≤ c m / 2 := div_nonneg (hc_pos m hm_le) (by norm_num)
    have hsingle (s : ℝ) :
        (∑' ρ : {ρ : zetaZeroConfig.carrier | (ρ : ℂ).re ≠ 1 / 2},
          (zetaZeroConfig.Wsummand (modCx s f) (modCx s f) ρ.1).re) ≤
        (zetaZeroConfig.W (modCx s f) (modCx s f)).re := by
      let S : Set zetaZeroConfig.carrier := {ρ | (ρ : ℂ).re = 1 / 2}
      have hsum_c := summable_Wsummand_zetaZeroConfig
        (modCx_contDiff hf.1) (modCx_hasCompactSupport hf.2)
      have hsum_r : Summable (fun ρ : zetaZeroConfig.carrier =>
          (zetaZeroConfig.Wsummand (modCx s f) (modCx s f) ρ).re) :=
        Complex.reCLM.summable hsum_c
      rw [ZeroConfig.W, Complex.re_tsum hsum_c,
        ← hsum_r.tsum_subtype_add_tsum_subtype_compl S]
      have hon_nonneg : 0 ≤ ∑' ρ : S,
          (zetaZeroConfig.Wsummand (modCx s f) (modCx s f) ρ.1).re :=
        tsum_nonneg fun ρ =>
          SquareRootThreshold.re_Wsummand_nonneg_of_onLine zetaZeroConfig _ ρ.2
      change (∑' ρ : Sᶜ, (zetaZeroConfig.Wsummand (modCx s f) (modCx s f) ρ.1).re) ≤ _
      linarith only [hon_nonneg]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (hsingle ((m : ℝ) * ω)) (hsingle (-((m : ℝ) * ω)))) hcm
  have hfull_le : harmonicCoupledZeroSide M c ω f ≤ harmonicCoupledPoleGamma M c ω f := by
    rw [harmonicCoupledZeroSide_eq_poleGamma_sub_primes M c ω hf]
    linarith only [harmonicCoupledPrimeSum_nonneg M ω hf hf_pos hP]
  exact hoff_le_full.trans hfull_le

/-! ### 3. Universal quantized divisor-order forcing law and Meyer-source exclusion -/

private theorem sum_range_succ_eq_zero_add_Icc {K : ℕ} (g : ℕ → ℝ) :
    ∑ k ∈ Finset.range (K + 1), g k = g 0 + ∑ k ∈ Finset.Icc 1 K, g k := by
  induction K with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, add_assoc]
    congr 1
    have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hIcc, Finset.sum_insert (by simp), add_comm]

/-- Abstract harmonic divisor-order bound: any real logarithmic-derivative family
`L σ u` satisfying harmonic positivity for `1 < σ` and boundary order limits
`(σ - 1) * L σ u → μ_pole u - μ_zero u` as `σ → 1⁺` satisfies the weighted
divisor inequality across all harmonics `1 ≤ k ≤ K`. -/
theorem harmonic_divisor_order_le {K : ℕ} {a : ℕ → ℝ}
    {L : ℝ → ℝ → ℝ} {μ_pole μ_zero : ℝ → ℝ}
    (hpos : ∀ {σ : ℝ}, 1 < σ → ∀ t : ℝ,
      0 ≤ ∑ k ∈ Finset.range (K + 1), a k * L σ ((k : ℝ) * t))
    (hlim : ∀ u : ℝ,
      Tendsto (fun σ : ℝ => (σ - 1) * L σ u) (𝓝[>] 1) (𝓝 (μ_pole u - μ_zero u)))
    (hzero0 : μ_zero 0 = 0) (t : ℝ) :
    ∑ k ∈ Finset.Icc 1 K, a k * μ_zero ((k : ℝ) * t) ≤
      a 0 * μ_pole 0 + ∑ k ∈ Finset.Icc 1 K, a k * μ_pole ((k : ℝ) * t) := by
  have htend : Tendsto
      (fun σ : ℝ => ∑ k ∈ Finset.range (K + 1), a k * ((σ - 1) * L σ ((k : ℝ) * t)))
      (𝓝[>] 1)
      (𝓝 (∑ k ∈ Finset.range (K + 1), a k * (μ_pole ((k : ℝ) * t) - μ_zero ((k : ℝ) * t)))) :=
    tendsto_finset_sum _ fun k _ => (hlim ((k : ℝ) * t)).const_mul (a k)
  have hev : ∀ᶠ σ : ℝ in 𝓝[>] 1,
      0 ≤ ∑ k ∈ Finset.range (K + 1), a k * ((σ - 1) * L σ ((k : ℝ) * t)) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ1 : 0 ≤ σ - 1 := sub_nonneg.mpr (le_of_lt hσ)
    have hmul := mul_nonneg hσ1 (hpos hσ t)
    rwa [Finset.mul_sum, Finset.sum_congr rfl (fun k _ => by ring)] at hmul
  haveI : NeBot (𝓝[>] (1 : ℝ)) := nhdsGT_neBot 1
  have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.range (K + 1),
      a k * (μ_pole ((k : ℝ) * t) - μ_zero ((k : ℝ) * t)) :=
    ge_of_tendsto htend hev
  rw [sum_range_succ_eq_zero_add_Icc] at hsum_nonneg
  simp only [Nat.cast_zero, zero_mul, hzero0, sub_zero, mul_sub,
    Finset.sum_sub_distrib] at hsum_nonneg
  linarith only [hsum_nonneg]

/-- Universal quantized zero-order vanishing law: when `μ_pole, μ_zero : ℝ → ℕ`
are integer divisor multiplicities, `0 ≤ a 0 < a 1`, the origin pole is at most
simple (`μ_pole 0 ≤ 1`), and harmonics `1 ≤ k ≤ K` carry no poles (`μ_pole (k * t) = 0`),
integer quantization forces `μ_zero t = 0`. -/
theorem harmonic_quantized_zero_vanishing {K : ℕ} {a : ℕ → ℝ}
    {L : ℝ → ℝ → ℝ} {μ_pole μ_zero : ℝ → ℕ}
    (hK : 1 ≤ K)
    (ha0 : 0 ≤ a 0)
    (ha_pos : ∀ k ∈ Finset.Icc 1 K, 0 ≤ a k)
    (ha_strict : a 0 < a 1)
    (hpos : ∀ {σ : ℝ}, 1 < σ → ∀ t : ℝ,
      0 ≤ ∑ k ∈ Finset.range (K + 1), a k * L σ ((k : ℝ) * t))
    (hlim : ∀ u : ℝ,
      Tendsto (fun σ : ℝ => (σ - 1) * L σ u) (𝓝[>] 1)
        (𝓝 ((μ_pole u : ℝ) - (μ_zero u : ℝ))))
    (hpole_simple : μ_pole 0 ≤ 1)
    (hzero0 : μ_zero 0 = 0)
    {t : ℝ} (hpole_isol : ∀ k ∈ Finset.Icc 1 K, μ_pole ((k : ℝ) * t) = 0) :
    μ_zero t = 0 := by
  have hbound := harmonic_divisor_order_le hpos hlim
    (by simp only [hzero0, Nat.cast_zero]) t
  have hpole_sum : (∑ k ∈ Finset.Icc 1 K, a k * (μ_pole ((k : ℝ) * t) : ℝ)) = 0 :=
    Finset.sum_eq_zero fun k hk => by rw [hpole_isol k hk, Nat.cast_zero, mul_zero]
  have hpole0 : a 0 * (μ_pole 0 : ℝ) ≤ a 0 := by
    have hp1 : (μ_pole 0 : ℝ) ≤ 1 := by exact_mod_cast hpole_simple
    nlinarith only [ha0, hp1]
  have h1mem : 1 ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨le_rfl, hK⟩
  have hsingle : a 1 * (μ_zero t : ℝ) ≤
      ∑ k ∈ Finset.Icc 1 K, a k * (μ_zero ((k : ℝ) * t) : ℝ) := by
    have h1eq : a 1 * (μ_zero ((1 : ℕ) * t) : ℝ) = a 1 * (μ_zero t : ℝ) := by
      simp only [Nat.cast_one, one_mul]
    rw [← h1eq]
    exact Finset.single_le_sum
      (fun k hk => mul_nonneg (ha_pos k hk) (Nat.cast_nonneg _)) h1mem
  by_contra hne
  have hm1 : (1 : ℝ) ≤ (μ_zero t : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  nlinarith only [hbound, hpole_sum, hpole0, hsingle, hm1, ha0, ha_strict]

/-- Real part of `-ζ'/ζ(σ + i u)`. -/
def zetaRealLogDeriv (σ u : ℝ) : ℝ :=
  (-deriv riemannZeta ((σ : ℂ) + (u : ℂ) * I) /
    riemannZeta ((σ : ℂ) + (u : ℂ) * I)).re

/-- Boundary pole multiplicity of `ζ` along `Re s = 1`. -/
def zetaBoundaryPoleOrder (u : ℝ) : ℕ :=
  if u = 0 then 1 else 0

/-- Boundary analytic vanishing order of `ζ` along `Re s = 1`. -/
def zetaBoundaryZeroOrder (u : ℝ) : ℕ :=
  if u = 0 then 0 else analyticOrderNatAt riemannZeta (1 + (u : ℂ) * I)

/-- Harmonic positivity of `-Re (ζ'/ζ)` on `σ > 1` for every nonnegative cosine
polynomial `P`, proved from `Λ(n) ≥ 0` on the Dirichlet series. -/
theorem zetaRealLogDeriv_harmonic_nonneg {K : ℕ} {a : ℕ → ℝ}
    (hP : ∀ θ : ℝ, 0 ≤ HTGeometry.cosinePolynomial a K θ)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ ∑ k ∈ Finset.range (K + 1), a k * zetaRealLogDeriv σ ((k : ℝ) * t) := by
  have hs_re (u : ℝ) : (((σ : ℂ) + (u : ℂ) * I)).re = σ := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hterm_eq (k : ℕ) : a k * zetaRealLogDeriv σ ((k : ℝ) * t) =
      ∑' n : ℕ, a k * (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I) n).re := by
    unfold zetaRealLogDeriv
    have hre : 1 < (((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I)).re := by
      rw [hs_re]; exact hσ
    have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
    have hneg : -deriv riemannZeta ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I) =
        LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I) := by
      rw [hL, neg_div]
    have hs := ArithmeticFunction.LSeriesSummable_vonMangoldt hre
    have hsr : Summable (fun n : ℕ =>
        (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I) n).re) :=
      Complex.reCLM.summable hs
    rw [hneg, LSeries, Complex.re_tsum hs, ← hsr.tsum_mul_left]
  simp_rw [hterm_eq]
  have hsum_k (k : ℕ) : Summable (fun n : ℕ =>
      a k * (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I) n).re) := by
    refine (Complex.reCLM.summable (ArithmeticFunction.LSeriesSummable_vonMangoldt ?_)).mul_left _
    rw [hs_re]; exact hσ
  rw [← Summable.tsum_finsetSum (fun k _ => hsum_k k)]
  refine tsum_nonneg fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · have hpoint : ∑ k ∈ Finset.range (K + 1),
        a k * (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I) n).re =
        (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) *
          HTGeometry.cosinePolynomial a K (t * Real.log n) := by
      unfold HTGeometry.cosinePolynomial
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [_root_.RHTower.re_lseries_term_vonMangoldt hn σ ((k : ℝ) * t)]
      have hang : (k : ℝ) * t * Real.log n = (k : ℝ) * (t * Real.log n) := by ring
      rw [hang]
      ring
    rw [hpoint]
    exact mul_nonneg
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_pos_of_pos (by exact_mod_cast hn) _).le)
      (hP (t * Real.log n))

/-- Boundary order limit of `-Re (ζ'/ζ)` along `σ → 1⁺`, established from the
residue at `s = 1` and local Weierstrass factorization on `{1}ᶜ` using only
`ζ(2) ≠ 0` in the Euler half-plane `σ > 1`. -/
theorem tendsto_zetaRealLogDeriv_boundary (u : ℝ) :
    Tendsto (fun σ : ℝ => (σ - 1) * zetaRealLogDeriv σ u) (𝓝[>] 1)
      (𝓝 ((zetaBoundaryPoleOrder u : ℝ) - (zetaBoundaryZeroOrder u : ℝ))) := by
  by_cases hu : u = 0
  · subst hu
    simp only [zetaBoundaryPoleOrder, zetaBoundaryZeroOrder, ↓reduceIte,
      Nat.cast_one, Nat.cast_zero, sub_zero]
    have hcomp := _root_.RHTower.neg_logDeriv_zeta_residue.comp
      _root_.RHTower.tendsto_ofReal_nhdsWithin_ne_one
    have hre := (Complex.continuous_re.tendsto (1 : ℂ)).comp hcomp
    simp only [Complex.one_re] at hre
    refine hre.congr fun σ => ?_
    simp only [Function.comp_apply, zetaRealLogDeriv, Complex.ofReal_zero, zero_mul, add_zero]
    have hsub : ((σ : ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hsub, Complex.re_ofReal_mul]
  · simp only [zetaBoundaryPoleOrder, zetaBoundaryZeroOrder, hu, ↓reduceIte,
      Nat.cast_zero, zero_sub]
    let ρ : ℂ := 1 + (u : ℂ) * I
    have hρ1 : ρ ≠ 1 := by
      intro h
      have him := congrArg Complex.im h
      simp only [ρ, Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add] at him
      exact hu him
    let U : Set ℂ := {(1 : ℂ)}ᶜ
    have hU_conn : IsConnected U :=
      isConnected_compl_singleton_of_one_lt_rank
        (by rw [Complex.rank_real_complex]; norm_num) 1
    have hana_on : AnalyticOnNhd ℂ riemannZeta U :=
      fun z hz => HTGeometry.analyticAt_riemannZeta hz
    have h2mem : (2 : ℂ) ∈ U := by simp [U]
    have h2_ord : analyticOrderAt riemannZeta 2 ≠ ⊤ := by
      rw [(HTGeometry.analyticAt_riemannZeta h2mem).analyticOrderAt_eq_zero.mpr
        (riemannZeta_ne_zero_of_one_lt_re (by norm_num))]
      exact ENat.zero_ne_top
    have hρ_ord : analyticOrderAt riemannZeta ρ ≠ ⊤ :=
      (hana_on.exists_analyticOrderAt_ne_top_iff_forall hU_conn).mp
        ⟨⟨2, h2mem⟩, h2_ord⟩ ⟨ρ, hρ1⟩
    obtain ⟨g, hg, hg0, hfac⟩ :=
      (HTGeometry.analyticAt_riemannZeta hρ1).analyticOrderAt_ne_top.mp hρ_ord
    have hres := (_root_.RHTower.logDeriv_residue_of_factorization hg hg0 hfac).neg
    have hpath : Tendsto (fun σ : ℝ => (σ : ℂ) + (u : ℂ) * I) (𝓝[>] 1) (𝓝[≠] ρ) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hc : Continuous (fun σ : ℝ => (σ : ℂ) + (u : ℂ) * I) :=
          Complex.continuous_ofReal.add continuous_const
        simpa only [ρ, Complex.ofReal_one] using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with σ hσ
        intro heq
        have hre := congrArg Complex.re heq
        simp only [ρ, Complex.add_re, Complex.ofReal_re, Complex.one_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
          add_zero] at hre
        exact (ne_of_gt hσ) hre
    have hre := (Complex.continuous_re.tendsto
      (-(analyticOrderNatAt riemannZeta ρ : ℂ))).comp (hres.comp hpath)
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    refine hre.congr fun σ => ?_
    simp only [Function.comp_apply, zetaRealLogDeriv]
    have hdiff : ((σ : ℂ) + (u : ℂ) * I) - ρ = ((σ - 1 : ℝ) : ℂ) := by
      dsimp only [ρ]; push_cast; ring
    have hld : -(((σ : ℂ) + (u : ℂ) * I - ρ) * logDeriv riemannZeta ((σ : ℂ) + (u : ℂ) * I)) =
        ((σ - 1 : ℝ) : ℂ) *
          (-deriv riemannZeta ((σ : ℂ) + (u : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (u : ℂ) * I)) := by
      rw [hdiff, logDeriv_apply]
      ring
    rw [hld, Complex.re_ofReal_mul]

/-- Non-circular boundary vanishing order theorem for `ζ`: instantiating
`harmonic_quantized_zero_vanishing` with `fejerAutoCoeff 2 fejerProfile2`
forces `zetaBoundaryZeroOrder t = 0` at every height `t`. -/
theorem zetaBoundaryZeroOrder_eq_zero (t : ℝ) :
    zetaBoundaryZeroOrder t = 0 := by
  by_cases ht : t = 0
  · simp [zetaBoundaryZeroOrder, ht]
  · refine harmonic_quantized_zero_vanishing
      (K := 2) (a := fejerAutoCoeff 2 fejerProfile2)
      (by norm_num)
      (fejerAutoCoeff_nonneg 2 (fun j _ => fejerProfile2_nonneg j) 0)
      (fun k _ => fejerAutoCoeff_nonneg 2 (fun j _ => fejerProfile2_nonneg j) k)
      fejerAutoCoeff_two_const_lt_first
      (fun hσ u => zetaRealLogDeriv_harmonic_nonneg
        (cosinePolynomial_fejerAutoCoeff_nonneg 2 fejerProfile2) hσ u)
      tendsto_zetaRealLogDeriv_boundary
      (by simp [zetaBoundaryPoleOrder])
      (by simp [zetaBoundaryZeroOrder])
      (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    simp [zetaBoundaryPoleOrder, mul_ne_zero hk0 ht]

/-- Boundary nonvanishing of `ζ` on `Re s = 1` (`t ≠ 0`) derived directly from
the quantized harmonic forcing law. -/
theorem riemannZeta_boundary_ne_zero_from_harmonic_forcing {t : ℝ} (ht : t ≠ 0) :
    riemannZeta (1 + (t : ℂ) * I) ≠ 0 := by
  have hz := zetaBoundaryZeroOrder_eq_zero t
  simp only [zetaBoundaryZeroOrder, ht, ↓reduceIte] at hz
  let ρ : ℂ := 1 + (t : ℂ) * I
  have hρ1 : ρ ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp only [ρ, Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add] at him
    exact ht him
  let U : Set ℂ := {(1 : ℂ)}ᶜ
  have hU_conn : IsConnected U :=
    isConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num) 1
  have hana_on : AnalyticOnNhd ℂ riemannZeta U :=
    fun z hz => HTGeometry.analyticAt_riemannZeta hz
  have h2mem : (2 : ℂ) ∈ U := by simp [U]
  have h2_ord : analyticOrderAt riemannZeta 2 ≠ ⊤ := by
    rw [(HTGeometry.analyticAt_riemannZeta h2mem).analyticOrderAt_eq_zero.mpr
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num))]
    exact ENat.zero_ne_top
  have hρ_ord : analyticOrderAt riemannZeta ρ ≠ ⊤ :=
    (hana_on.exists_analyticOrderAt_ne_top_iff_forall hU_conn).mp
      ⟨⟨2, h2mem⟩, h2_ord⟩ ⟨ρ, hρ1⟩
  obtain ⟨g, -, hg0, hfac⟩ :=
    (HTGeometry.analyticAt_riemannZeta hρ1).analyticOrderAt_ne_top.mp hρ_ord
  have hval := hfac.eq_of_nhds
  change riemannZeta ρ = (ρ - ρ) ^ analyticOrderNatAt riemannZeta ρ • g ρ at hval
  rw [hz, pow_zero, one_smul] at hval
  rwa [hval]

/-- The symmetric two-sided harmonic zero-free collar inside the critical strip. -/
def harmonicZeroFreeCollar : Set ℂ :=
  {z : ℂ | 9 ≤ |z.im| ∧
    (1 - _root_.RHTower.zetaZeroFreeC / Real.log |z.im| ^ (9 : ℕ) < z.re ∨
      z.re < _root_.RHTower.zetaZeroFreeC / Real.log |z.im| ^ (9 : ℕ))}

/-- Non-vacuity: at every height `|t| ≥ 9`, `harmonicZeroFreeCollar` contains
points strictly inside the open critical strip `0 < Re z < 1` off `Re z = 1 / 2`. -/
theorem harmonicZeroFreeCollar_nonempty_in_strip {t : ℝ} (ht : 9 ≤ |t|) :
    ∃ z ∈ harmonicZeroFreeCollar,
      0 < z.re ∧ z.re < 1 ∧ z.re ≠ 1 / 2 ∧ z.im = t := by
  have hlog_pos : 0 < Real.log |t| := Real.log_pos (by linarith only [ht])
  have hlog_ge_one : 1 ≤ Real.log |t| := by
    have he := _root_.RHTower.exp_two_lt_eight
    have he1 : Real.exp 1 < Real.exp 2 := Real.exp_lt_exp.mpr (by norm_num)
    have hlt : Real.exp 1 < |t| := by linarith only [ht, he, he1]
    have h := Real.log_lt_log (Real.exp_pos 1) hlt
    rwa [Real.log_exp] at h
  have hpow_ge : 1 ≤ Real.log |t| ^ (9 : ℕ) := one_le_pow₀ hlog_ge_one
  have hc_pos : 0 < _root_.RHTower.zetaZeroFreeC / Real.log |t| ^ (9 : ℕ) :=
    div_pos _root_.RHTower.zetaZeroFreeC_pos (by positivity)
  have hc_le : _root_.RHTower.zetaZeroFreeC / Real.log |t| ^ (9 : ℕ) ≤ 1 / 2 := by
    calc _root_.RHTower.zetaZeroFreeC / Real.log |t| ^ (9 : ℕ)
        ≤ _root_.RHTower.zetaZeroFreeC / 1 :=
          div_le_div_of_nonneg_left _root_.RHTower.zetaZeroFreeC_pos.le zero_lt_one hpow_ge
      _ = _root_.RHTower.zetaZeroFreeC := div_one _
      _ ≤ 1 / 2 := _root_.RHTower.zetaZeroFreeC_le_half
  let w : ℝ := _root_.RHTower.zetaZeroFreeC / Real.log |t| ^ (9 : ℕ)
  let z : ℂ := ((1 - w / 2 : ℝ) : ℂ) + (t : ℂ) * I
  have hz_re : z.re = 1 - w / 2 := by
    simp [z, Complex.add_re, Complex.mul_re]
  have hz_im : z.im = t := by
    simp [z, Complex.add_im, Complex.mul_im]
  refine ⟨z, ?_, ?_, ?_, ?_, hz_im⟩
  · refine ⟨by rwa [hz_im], Or.inl ?_⟩
    rw [hz_im, hz_re]
    dsimp only [w] at hc_pos ⊢
    linarith only [hc_pos]
  · rw [hz_re]; dsimp only [w] at hc_le; linarith only [hc_le]
  · rw [hz_re]; dsimp only [w] at hc_pos; linarith only [hc_pos]
  · rw [hz_re]; dsimp only [w] at hc_le; intro heq; linarith only [hc_le, heq]

/-- Harmonic phase coupling excludes the actual Meyer-source spectral support
`XiDivisorSupport` from both boundary lines `Re z = 0, 1` and from both reflected
de la Vallée Poussin collars inside `0 < Re z < 1`. -/
theorem xiDivisorSupport_disjoint_boundary_and_harmonicCollar (rho : _root_.RHTower.XiDivisorSupport) :
    (rho : ℂ).re ≠ 0 ∧ (rho : ℂ).re ≠ 1 ∧ (rho : ℂ) ∉ harmonicZeroFreeCollar := by
  have hstrip := _root_.RHTower.xi_divisor_support_re_mem_open_unit rho
  have hxi0 := _root_.RHTower.xi_eq_zero_of_mem_divisor_support rho
  refine ⟨ne_of_gt hstrip.1, ne_of_lt hstrip.2, ?_⟩
  rintro ⟨ht, hright | hleft⟩
  · have hrho_ne1 : (rho : ℂ) ≠ 1 := fun h => by
      rw [h, Complex.one_re] at hstrip; exact lt_irrefl 1 hstrip.2
    have hζ0 : riemannZeta (rho : ℂ) = 0 :=
      (_root_.RHTower.xi_eq_zero_iff hstrip.1 hrho_ne1).mp hxi0
    have hdecomp : (((rho : ℂ).re : ℂ) + ((rho : ℂ).im : ℂ) * I) = (rho : ℂ) :=
      Complex.re_add_im (rho : ℂ)
    rw [← hdecomp] at hζ0
    exact _root_.RHTower.riemannZeta_ne_zero_of_re_gt_one_sub ht hright hζ0
  · let w : ℂ := 1 - (rho : ℂ)
    have hw_xi : _root_.RHTower.xi w = 0 := by
      dsimp only [w]; rw [_root_.RHTower.xi_one_sub, hxi0]
    have hw_re : w.re = 1 - (rho : ℂ).re := by simp [w]
    have hw_im : w.im = -(rho : ℂ).im := by simp [w]
    have hw_ne1 : w ≠ 1 := fun h => by
      have hr := congrArg Complex.re h
      rw [hw_re, Complex.one_re] at hr
      linarith only [hstrip.1, hr]
    have hζw : riemannZeta w = 0 :=
      (_root_.RHTower.xi_eq_zero_iff (by linarith only [hw_re, hstrip.2]) hw_ne1).mp hw_xi
    have hdecomp : ((w.re : ℂ) + (w.im : ℂ) * I) = w := Complex.re_add_im w
    rw [← hdecomp] at hζw
    have hwt : 9 ≤ |w.im| := by rwa [hw_im, abs_neg]
    have hw_col : 1 - _root_.RHTower.zetaZeroFreeC / Real.log |w.im| ^ (9 : ℕ) < w.re := by
      rw [hw_im, abs_neg, hw_re]
      linarith only [hleft]
    exact _root_.RHTower.riemannZeta_ne_zero_of_re_gt_one_sub hwt hw_col hζw

/-! ### 4. Sharpness Countermodel 1: Double-pole Beurling system (`μ_pole 0 = 2`) -/

/-- Explicit meromorphic zeta function with a double pole at `s = 1`, no other
poles, and genuine boundary zeros at `1 ± i t0`. -/
def doublePoleZeta (t0 : ℝ) (s : ℂ) : ℂ :=
  ((s - 1) ^ 2 + (t0 : ℂ) ^ 2) / (s - 1) ^ 2

/-- Nonnegative Beurling prime density `2 e^t (1 - cos(t0 t)) / t ≥ 0` on `(0, ∞)`. -/
def doublePolePrimeDensity (t0 : ℝ) (t : ℝ) : ℝ :=
  2 * Real.exp t * (1 - Real.cos (t0 * t)) / t

theorem doublePolePrimeDensity_nonneg (t0 : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ doublePolePrimeDensity t0 t := by
  unfold doublePolePrimeDensity
  exact div_nonneg
    (mul_nonneg (by positivity) (by linarith [Real.cos_le_one (t0 * t)])) ht

theorem doublePoleZeta_boundary_zero_pos (t0 : ℝ) :
    doublePoleZeta t0 (1 + (t0 : ℂ) * I) = 0 := by
  unfold doublePoleZeta
  have hnum : ((1 + (t0 : ℂ) * I - 1) ^ 2 + (t0 : ℂ) ^ 2) = 0 := by
    calc ((1 + (t0 : ℂ) * I - 1) ^ 2 + (t0 : ℂ) ^ 2)
        = (t0 : ℂ) ^ 2 * (I ^ 2 + 1) := by ring
      _ = 0 := by rw [Complex.I_sq]; ring
  rw [hnum, zero_div]

theorem doublePoleZeta_boundary_zero_neg (t0 : ℝ) :
    doublePoleZeta t0 (1 - (t0 : ℂ) * I) = 0 := by
  unfold doublePoleZeta
  have hnum : ((1 - (t0 : ℂ) * I - 1) ^ 2 + (t0 : ℂ) ^ 2) = 0 := by
    calc ((1 - (t0 : ℂ) * I - 1) ^ 2 + (t0 : ℂ) ^ 2)
        = (t0 : ℂ) ^ 2 * (I ^ 2 + 1) := by ring
      _ = 0 := by rw [Complex.I_sq]; ring
  rw [hnum, zero_div]

theorem differentiableAt_doublePoleZeta (t0 : ℝ) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (doublePoleZeta t0) s := by
  unfold doublePoleZeta
  exact (((differentiableAt_id.sub_const 1).pow 2).add
    (differentiableAt_const _)).div ((differentiableAt_id.sub_const 1).pow 2)
    (pow_ne_zero 2 (sub_ne_zero.mpr hs))

/-- Exact Euler–Frullani representation on `1 < Re s`: `doublePoleZeta t0 s` is
the exponential of the Laplace transform of the nonnegative prime density
`doublePolePrimeDensity t0`. -/
theorem cexp_integral_doublePolePrimeDensity_eq (t0 : ℝ) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (∫ t in Ioi (0 : ℝ),
      Complex.exp (-(s * (t : ℂ))) * (doublePolePrimeDensity t0 t : ℂ)) =
      doublePoleZeta t0 s := by
  let z0 : ℂ := s - 1
  let z1 : ℂ := s - 1 - (t0 : ℂ) * I
  let z2 : ℂ := s - 1 + (t0 : ℂ) * I
  have hz0 : 0 < z0.re := by simp only [z0, Complex.sub_re, Complex.one_re]; linarith only [hs]
  have hz1 : 0 < z1.re := by
    simp only [z1, Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
    linarith only [hs]
  have hz2 : 0 < z2.re := by
    simp only [z2, Complex.add_re, Complex.sub_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
      sub_zero, add_zero]
    linarith only [hs]
  have hpoint (t : ℝ) :
      Complex.exp (-(s * (t : ℂ))) * (doublePolePrimeDensity t0 t : ℂ) =
        (Complex.exp (-(z0 * t)) - Complex.exp (-(z1 * t))) / t +
          (Complex.exp (-(z0 * t)) - Complex.exp (-(z2 * t))) / t := by
    unfold doublePolePrimeDensity
    push_cast
    rw [Complex.ofReal_exp, Complex.ofReal_cos,
      show ((t0 * t : ℝ) : ℂ) = (t0 : ℂ) * (t : ℂ) by push_cast; ring,
      Complex.cos]
    have he0 : Complex.exp (-(s * (t : ℂ))) * Complex.exp (t : ℂ) = Complex.exp (-(z0 * t)) := by
      rw [← Complex.exp_add]; congr 1; dsimp only [z0]; ring
    have he1 : Complex.exp (-(z0 * t)) * Complex.exp ((t0 : ℂ) * (t : ℂ) * I) =
        Complex.exp (-(z1 * t)) := by
      rw [← Complex.exp_add]; congr 1; dsimp only [z0, z1]; ring
    have he2 : Complex.exp (-(z0 * t)) * Complex.exp (-((t0 : ℂ) * (t : ℂ) * I)) =
        Complex.exp (-(z2 * t)) := by
      rw [← Complex.exp_add]; congr 1; dsimp only [z0, z2]; ring
    rw [mul_div_assoc, ← add_div]
    congr 1
    calc
      Complex.exp (-(s * t)) * (2 * Complex.exp t *
          (1 - (Complex.exp ((t0 : ℂ) * t * I) + Complex.exp (-((t0 : ℂ) * t * I))) / 2))
        = (Complex.exp (-(s * t)) * Complex.exp t) *
            (2 - (Complex.exp ((t0 : ℂ) * t * I) + Complex.exp (-((t0 : ℂ) * t * I)))) := by ring
      _ = Complex.exp (-(z0 * t)) *
            (2 - (Complex.exp ((t0 : ℂ) * t * I) + Complex.exp (-((t0 : ℂ) * t * I)))) := by
          rw [he0]
      _ = 2 * Complex.exp (-(z0 * t)) -
            Complex.exp (-(z0 * t)) * Complex.exp ((t0 : ℂ) * t * I) -
            Complex.exp (-(z0 * t)) * Complex.exp (-((t0 : ℂ) * t * I)) := by ring
      _ = (Complex.exp (-(z0 * t)) - Complex.exp (-(z1 * t))) +
            (Complex.exp (-(z0 * t)) - Complex.exp (-(z2 * t))) := by
          rw [he1, he2]; ring
  simp_rw [hpoint]
  have hz0_ne : z0 ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz0; exact lt_irrefl 0 hz0
  have hz1_ne : z1 ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz1; exact lt_irrefl 0 hz1
  have hz2_ne : z2 ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz2; exact lt_irrefl 0 hz2
  rw [integral_add (HTGeometry.integrableOn_frullani hz0 hz1)
    (HTGeometry.integrableOn_frullani hz0 hz2),
    HTGeometry.integral_frullani hz0 hz1, HTGeometry.integral_frullani hz0 hz2,
    Complex.exp_add, Complex.exp_sub, Complex.exp_sub,
    Complex.exp_log hz0_ne, Complex.exp_log hz1_ne, Complex.exp_log hz2_ne]
  unfold doublePoleZeta
  dsimp only [z0, z1, z2] at hz0_ne ⊢
  field_simp [hz0_ne]
  calc ((s - 1 - (t0 : ℂ) * I) * (s - 1 + (t0 : ℂ) * I))
      = (s - 1) ^ 2 - (t0 : ℂ) ^ 2 * I ^ 2 := by ring
    _ = (s - 1) ^ 2 + (t0 : ℂ) ^ 2 := by rw [Complex.I_sq]; ring

/-- Negative logarithmic derivative of `doublePoleZeta t0`. -/
def doublePoleNegLogDeriv (t0 : ℝ) (s : ℂ) : ℂ :=
  2 / (s - 1) - 1 / (s - 1 - (t0 : ℂ) * I) - 1 / (s - 1 + (t0 : ℂ) * I)

/-- Away from its pole `1` and boundary zeros `1 ± i t0`, `-Z_2'/Z_2` equals
`doublePoleNegLogDeriv t0`. -/
theorem neg_logDeriv_doublePoleZeta_eq (t0 : ℝ) {s : ℂ}
    (hs1 : s ≠ 1) (hsp : s ≠ 1 + (t0 : ℂ) * I) (hsm : s ≠ 1 - (t0 : ℂ) * I) :
    -deriv (doublePoleZeta t0) s / doublePoleZeta t0 s = doublePoleNegLogDeriv t0 s := by
  have hz0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hzp : s - 1 - (t0 : ℂ) * I ≠ 0 := fun h => hsp (by linear_combination h)
  have hzm : s - 1 + (t0 : ℂ) * I ≠ 0 := fun h => hsm (by linear_combination h)
  have hnum_fac : (s - 1) ^ 2 + (t0 : ℂ) ^ 2 =
      (s - 1 - (t0 : ℂ) * I) * (s - 1 + (t0 : ℂ) * I) := by
    calc (s - 1) ^ 2 + (t0 : ℂ) ^ 2
        = (s - 1) ^ 2 - (t0 : ℂ) ^ 2 * I ^ 2 := by rw [Complex.I_sq]; ring
      _ = (s - 1 - (t0 : ℂ) * I) * (s - 1 + (t0 : ℂ) * I) := by ring
  have hd_sub : HasDerivAt (fun z : ℂ => (z - 1) ^ 2) (2 * (s - 1) * 1) s :=
    ((hasDerivAt_id s).sub_const 1).pow 2
  have hd : HasDerivAt (doublePoleZeta t0)
      (((2 * (s - 1) * 1 + 0) * (s - 1) ^ 2 -
        ((s - 1) ^ 2 + (t0 : ℂ) ^ 2) * (2 * (s - 1) * 1)) /
        ((s - 1) ^ 2) ^ 2) s := by
    unfold doublePoleZeta
    exact (hd_sub.add (hasDerivAt_const s ((t0 : ℂ) ^ 2))).div hd_sub (pow_ne_zero 2 hz0)
  rw [hd.deriv]
  unfold doublePoleZeta doublePoleNegLogDeriv
  rw [hnum_fac]
  field_simp [hz0, hzp, hzm]
  calc -((2 * (s - 1) * (s - 1) ^ 2 -
        (s - 1 - (t0 : ℂ) * I) * (s - 1 + (t0 : ℂ) * I) * (2 * (s - 1))))
      = 2 * (s - 1) * ((s - 1 - (t0 : ℂ) * I) * (s - 1 + (t0 : ℂ) * I) - (s - 1) ^ 2) := by ring
    _ = 2 * (s - 1) * ((s - 1) ^ 2 + (t0 : ℂ) ^ 2 - (s - 1) ^ 2) := by rw [← hnum_fac]
    _ = 2 * (s - 1 - (t0 : ℂ) * I) * (s - 1 + (t0 : ℂ) * I) -
          (s - 1) * (s - 1 + (t0 : ℂ) * I) - (s - 1) * (s - 1 - (t0 : ℂ) * I) := by
        calc 2 * (s - 1) * ((s - 1) ^ 2 + (t0 : ℂ) ^ 2 - (s - 1) ^ 2)
            = 2 * (s - 1) * (t0 : ℂ) ^ 2 := by ring
          _ = 2 * (s - 1) * ((s - 1 - (t0 : ℂ) * I) * (s - 1 + (t0 : ℂ) * I) - (s - 1) ^ 2) := by
              rw [← hnum_fac]; ring
          _ = _ := by ring

/-- Laplace representation of `doublePoleNegLogDeriv` against the nonnegative
weight `2 e^t (1 - cos(t0 t)) ≥ 0` on `1 < Re s`. -/
theorem doublePoleNegLogDeriv_eq_integral (t0 : ℝ) {s : ℂ} (hs : 1 < s.re) :
    doublePoleNegLogDeriv t0 s =
      ∫ t in Ioi (0 : ℝ),
        Complex.exp (-(s * (t : ℂ))) * ((2 * Real.exp t * (1 - Real.cos (t0 * t)) : ℝ) : ℂ) := by
  let z0 : ℂ := s - 1
  let z1 : ℂ := s - 1 - (t0 : ℂ) * I
  let z2 : ℂ := s - 1 + (t0 : ℂ) * I
  have hz0 : 0 < z0.re := by simp only [z0, Complex.sub_re, Complex.one_re]; linarith only [hs]
  have hz1 : 0 < z1.re := by
    simp only [z1, Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
    linarith only [hs]
  have hz2 : 0 < z2.re := by
    simp only [z2, Complex.add_re, Complex.sub_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
      sub_zero, add_zero]
    linarith only [hs]
  have hpoint (t : ℝ) :
      Complex.exp (-(s * (t : ℂ))) * ((2 * Real.exp t * (1 - Real.cos (t0 * t)) : ℝ) : ℂ) =
        ((2 : ℂ) * Complex.exp (-(z0 * t)) - Complex.exp (-(z1 * t))) -
          Complex.exp (-(z2 * t)) := by
    push_cast
    rw [Complex.ofReal_exp, Complex.ofReal_cos,
      show ((t0 * t : ℝ) : ℂ) = (t0 : ℂ) * (t : ℂ) by push_cast; ring, Complex.cos]
    have he0 : Complex.exp (-(s * (t : ℂ))) * Complex.exp (t : ℂ) = Complex.exp (-(z0 * t)) := by
      rw [← Complex.exp_add]; congr 1; dsimp only [z0]; ring
    have he1 : Complex.exp (-(z0 * t)) * Complex.exp ((t0 : ℂ) * (t : ℂ) * I) =
        Complex.exp (-(z1 * t)) := by
      rw [← Complex.exp_add]; congr 1; dsimp only [z0, z1]; ring
    have he2 : Complex.exp (-(z0 * t)) * Complex.exp (-((t0 : ℂ) * (t : ℂ) * I)) =
        Complex.exp (-(z2 * t)) := by
      rw [← Complex.exp_add]; congr 1; dsimp only [z0, z2]; ring
    calc
      Complex.exp (-(s * t)) * (2 * Complex.exp t *
          (1 - (Complex.exp ((t0 : ℂ) * t * I) + Complex.exp (-((t0 : ℂ) * t * I))) / 2))
        = (Complex.exp (-(s * t)) * Complex.exp t) *
            (2 - (Complex.exp ((t0 : ℂ) * t * I) + Complex.exp (-((t0 : ℂ) * t * I)))) := by ring
      _ = Complex.exp (-(z0 * t)) *
            (2 - (Complex.exp ((t0 : ℂ) * t * I) + Complex.exp (-((t0 : ℂ) * t * I)))) := by
          rw [he0]
      _ = 2 * Complex.exp (-(z0 * t)) -
            Complex.exp (-(z0 * t)) * Complex.exp ((t0 : ℂ) * t * I) -
            Complex.exp (-(z0 * t)) * Complex.exp (-((t0 : ℂ) * t * I)) := by ring
      _ = ((2 : ℂ) * Complex.exp (-(z0 * t)) - Complex.exp (-(z1 * t))) -
            Complex.exp (-(z2 * t)) := by
          rw [he1, he2]
  simp_rw [hpoint]
  rw [integral_sub (((HTGeometry.integrableOn_cexp_neg_mul hz0).const_mul 2).sub
      (HTGeometry.integrableOn_cexp_neg_mul hz1))
      (HTGeometry.integrableOn_cexp_neg_mul hz2),
    integral_sub ((HTGeometry.integrableOn_cexp_neg_mul hz0).const_mul 2)
      (HTGeometry.integrableOn_cexp_neg_mul hz1),
    integral_const_mul, HTGeometry.integral_cexp_neg_mul hz0,
    HTGeometry.integral_cexp_neg_mul hz1, HTGeometry.integral_cexp_neg_mul hz2]
  unfold doublePoleNegLogDeriv
  dsimp only [z0, z1, z2]
  ring

/-- Harmonic positivity holds for `doublePoleNegLogDeriv` across ALL degrees `K`
and ALL nonnegative cosine polynomials `P`. -/
theorem doublePole_harmonic_nonneg (t0 : ℝ) {K : ℕ} {a : ℕ → ℝ}
    (hP : ∀ θ : ℝ, 0 ≤ HTGeometry.cosinePolynomial a K θ)
    {σ : ℝ} (hσ : 1 < σ) (u : ℝ) :
    0 ≤ ∑ k ∈ Finset.range (K + 1),
      a k * (doublePoleNegLogDeriv t0 ((σ : ℂ) + (((k : ℝ) * u : ℝ) : ℂ) * I)).re := by
  have hint_w : IntegrableOn
      (fun t : ℝ => Real.exp (-((σ - 1) * t)) * (2 * (1 - Real.cos (t0 * t)))) (Ioi (0 : ℝ)) := by
    have hdom : IntegrableOn (fun t : ℝ => 4 * Real.exp (-(σ - 1) * t)) (Ioi (0 : ℝ)) :=
      (exp_neg_integrableOn_Ioi 0 (sub_pos.mpr hσ)).const_mul 4
    refine hdom.mono' ?_ ?_
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (continuous_const.mul (continuous_const.sub
          (Real.continuous_cos.comp (continuous_const.mul continuous_id))))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
      have hc1 : -1 ≤ Real.cos (t0 * t) := Real.neg_one_le_cos _
      have hc2 : Real.cos (t0 * t) ≤ 1 := Real.cos_le_one _
      have hw0 : 0 ≤ 2 * (1 - Real.cos (t0 * t)) := by linarith only [hc2]
      have hw4 : 2 * (1 - Real.cos (t0 * t)) ≤ 4 := by linarith only [hc1]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hw0),
        show -(σ - 1) * t = -((σ - 1) * t) by ring]
      nlinarith only [hw4, Real.exp_pos (-((σ - 1) * t))]
  have hterm (k : ℕ) :
      a k * (doublePoleNegLogDeriv t0 ((σ : ℂ) + (((k : ℝ) * u : ℝ) : ℂ) * I)).re =
        ∫ t in Ioi (0 : ℝ), a k *
          (Real.exp (-((σ - 1) * t)) * (2 * (1 - Real.cos (t0 * t))) *
            Real.cos ((k : ℝ) * (u * t))) := by
    have hs : 1 < (((σ : ℂ) + (((k : ℝ) * u : ℝ) : ℂ) * I)).re := by
      simp [Complex.add_re, Complex.mul_re, hσ]
    rw [doublePoleNegLogDeriv_eq_integral t0 hs]
    let g_c : ℝ → ℂ := fun t =>
      Complex.exp (-((((σ : ℂ) + (((k : ℝ) * u : ℝ) : ℂ) * I)) * (t : ℂ))) *
        ((2 * Real.exp t * (1 - Real.cos (t0 * t)) : ℝ) : ℂ)
    have hint_c : IntegrableOn g_c (Ioi (0 : ℝ)) := by
      refine (hint_w.mono' ?_ ?_)
      · dsimp only [g_c]; fun_prop
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
        dsimp only [g_c]
        rw [norm_mul, HTGeometry.norm_cexp_neg_mul_ofReal, Complex.norm_real,
          Real.norm_eq_abs]
        have hre : (((σ : ℂ) + (((k : ℝ) * u : ℝ) : ℂ) * I)).re = σ := by
          simp [Complex.add_re, Complex.mul_re]
        have hw0 : 0 ≤ 2 * Real.exp t * (1 - Real.cos (t0 * t)) :=
          mul_nonneg (by positivity) (by linarith [Real.cos_le_one (t0 * t)])
        rw [hre, abs_of_nonneg hw0]
        have hexp : Real.exp (-(σ * t)) * (2 * Real.exp t * (1 - Real.cos (t0 * t))) =
            Real.exp (-((σ - 1) * t)) * (2 * (1 - Real.cos (t0 * t))) := by
          calc Real.exp (-(σ * t)) * (2 * Real.exp t * (1 - Real.cos (t0 * t)))
              = (Real.exp (-(σ * t)) * Real.exp t) * (2 * (1 - Real.cos (t0 * t))) := by ring
            _ = Real.exp (-((σ - 1) * t)) * (2 * (1 - Real.cos (t0 * t))) := by
                rw [← Real.exp_add]; congr 1; ring
        rw [hexp]
    change a k * (∫ t in Ioi (0 : ℝ), g_c t).re = _
    rw [integral_re hint_c, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    dsimp only [g_c]
    rw [Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.ofReal_re,
      Complex.exp_re]
    have hre : (-(((σ : ℂ) + (((k : ℝ) * u : ℝ) : ℂ) * I) * (t : ℂ))).re = -(σ * t) := by
      simp [Complex.mul_re, Complex.add_re]
    have him : (-(((σ : ℂ) + (((k : ℝ) * u : ℝ) : ℂ) * I) * (t : ℂ))).im = -((k : ℝ) * (u * t)) := by
      simp [Complex.mul_im, Complex.add_im, Complex.mul_re, Complex.add_re]
      ring
    rw [hre, him, Real.cos_neg]
    have hexp : Real.exp (-(σ * t)) * (2 * Real.exp t * (1 - Real.cos (t0 * t))) =
        Real.exp (-((σ - 1) * t)) * (2 * (1 - Real.cos (t0 * t))) := by
      calc Real.exp (-(σ * t)) * (2 * Real.exp t * (1 - Real.cos (t0 * t)))
          = (Real.exp (-(σ * t)) * Real.exp t) * (2 * (1 - Real.cos (t0 * t))) := by ring
        _ = Real.exp (-((σ - 1) * t)) * (2 * (1 - Real.cos (t0 * t))) := by
            rw [← Real.exp_add]; congr 1; ring
    linear_combination a k * Real.cos ((k : ℝ) * (u * t)) * hexp
  have hint_k (k : ℕ) : IntegrableOn
      (fun t : ℝ => a k * (Real.exp (-((σ - 1) * t)) * (2 * (1 - Real.cos (t0 * t))) *
        Real.cos ((k : ℝ) * (u * t)))) (Ioi (0 : ℝ)) := by
    refine ((hint_w.mono' ?_ ?_).const_mul (a k))
    · exact (hint_w.aestronglyMeasurable.mul
        (Real.continuous_cos.comp (continuous_const.mul (continuous_const.mul continuous_id))).aestronglyMeasurable)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith [Real.cos_le_one (t0 * t)]))]
      exact mul_le_of_le_one_right
        (mul_nonneg (Real.exp_pos _).le (by linarith [Real.cos_le_one (t0 * t)]))
        (Real.abs_cos_le_one _)
  simp_rw [hterm]
  rw [← MeasureTheory.integral_finsetSum _ (fun k _ => hint_k k)]
  refine setIntegral_nonneg measurableSet_Ioi fun t _ => ?_
  have hsum_eq : ∑ k ∈ Finset.range (K + 1),
      a k * (Real.exp (-((σ - 1) * t)) * (2 * (1 - Real.cos (t0 * t))) *
        Real.cos ((k : ℝ) * (u * t))) =
      Real.exp (-((σ - 1) * t)) * (2 * (1 - Real.cos (t0 * t))) *
        HTGeometry.cosinePolynomial a K (u * t) := by
    unfold HTGeometry.cosinePolynomial
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hsum_eq]
  exact mul_nonneg
    (mul_nonneg (Real.exp_pos _).le (by linarith [Real.cos_le_one (t0 * t)]))
    (hP (u * t))

/-- Double-pole residue `+2` at `u = 0` (`μ_pole 0 = 2`). -/
theorem tendsto_doublePole_origin {t0 : ℝ} (ht0 : t0 ≠ 0) :
    Tendsto (fun σ : ℝ => (σ - 1) * (doublePoleNegLogDeriv t0 (σ : ℂ)).re)
      (𝓝[>] 1) (𝓝 2) := by
  have hz1 : ((1 : ℂ) - 1 - (t0 : ℂ) * I) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact ht0 him
  have hz2 : ((1 : ℂ) - 1 + (t0 : ℂ) * I) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact ht0 him
  let rem : ℝ → ℂ := fun σ =>
    1 / ((σ : ℂ) - 1 - (t0 : ℂ) * I) + 1 / ((σ : ℂ) - 1 + (t0 : ℂ) * I)
  have hrem_cont : ContinuousAt rem 1 := by
    dsimp only [rem]
    refine (continuousAt_const.div ?_ hz1).add (continuousAt_const.div ?_ hz2)
    · exact (Complex.continuous_ofReal.sub continuous_const).sub continuous_const |>.continuousAt
    · exact (Complex.continuous_ofReal.sub continuous_const).add continuous_const |>.continuousAt
  have hsub0 : Tendsto (fun σ : ℝ => ((σ - 1 : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 0) := by
    have hc : Continuous (fun σ : ℝ => ((σ - 1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)
    simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun σ : ℝ => (2 : ℂ) - ((σ - 1 : ℝ) : ℂ) * rem σ)
      (𝓝[>] 1) (𝓝 2) := by
    simpa using tendsto_const_nhds.sub (hsub0.mul (hrem_cont.tendsto.mono_left nhdsWithin_le_nhds))
  have hre := (Complex.continuous_re.tendsto (2 : ℂ)).comp hprod
  simp only [Complex.ofNat_re] at hre
  refine hre.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hne : ((σ : ℂ) - 1) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith only [hσ, hr]
  simp only [Function.comp_apply]
  have hident : ((σ - 1 : ℝ) : ℂ) * doublePoleNegLogDeriv t0 (σ : ℂ) =
      (2 : ℂ) - ((σ - 1 : ℝ) : ℂ) * rem σ := by
    unfold doublePoleNegLogDeriv
    dsimp only [rem]
    have hs : ((σ - 1 : ℝ) : ℂ) = (σ : ℂ) - 1 := by push_cast; ring
    rw [hs]
    field_simp [hne]
    ring
  rw [← hident, Complex.re_ofReal_mul]

/-- Simple boundary zero residue `-1` at `u = t0` (`μ_zero t0 = 1`), and strict
satisfaction `a 1 * 1 < a 0 * 2` of the harmonic order inequality for EVERY degree
`K ≥ 1` and EVERY nonzero nonnegative cosine polynomial `P`. -/
theorem doublePole_boundary_zero_survives_all_degrees {t0 : ℝ} (ht0 : t0 ≠ 0)
    {K : ℕ} (hK : 1 ≤ K) {a : ℕ → ℝ}
    (hP : ∀ θ : ℝ, 0 ≤ HTGeometry.cosinePolynomial a K θ) (ha0 : 0 < a 0) :
    doublePoleZeta t0 (1 + (t0 : ℂ) * I) = 0 ∧
      Tendsto (fun σ : ℝ =>
        (σ - 1) * (doublePoleNegLogDeriv t0 ((σ : ℂ) + (t0 : ℂ) * I)).re)
        (𝓝[>] 1) (𝓝 (-1)) ∧
      a 1 * (1 : ℝ) < a 0 * (2 : ℝ) := by
  refine ⟨doublePoleZeta_boundary_zero_pos t0, ?_, ?_⟩
  · have hz0 : ((1 : ℂ) + (t0 : ℂ) * I - 1) ≠ 0 := by
      intro h; have him := congrArg Complex.im h; simp at him; exact ht0 him
    have hz2 : ((1 : ℂ) + (t0 : ℂ) * I - 1 + (t0 : ℂ) * I) ≠ 0 := by
      intro h; have him := congrArg Complex.im h; simp at him; linarith only [ht0, him]
    let rem : ℝ → ℂ := fun σ =>
      2 / ((σ : ℂ) + (t0 : ℂ) * I - 1) -
        1 / ((σ : ℂ) + (t0 : ℂ) * I - 1 + (t0 : ℂ) * I)
    have hrem_cont : ContinuousAt rem 1 := by
      dsimp only [rem]
      refine (continuousAt_const.div ?_ hz0).sub (continuousAt_const.div ?_ hz2)
      · exact ((Complex.continuous_ofReal.add continuous_const).sub continuous_const).continuousAt
      · exact (((Complex.continuous_ofReal.add continuous_const).sub continuous_const).add
          continuous_const).continuousAt
    have hsub0 : Tendsto (fun σ : ℝ => ((σ - 1 : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 0) := by
      have hc : Continuous (fun σ : ℝ => ((σ - 1 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    have hprod : Tendsto (fun σ : ℝ => (-1 : ℂ) + ((σ - 1 : ℝ) : ℂ) * rem σ)
        (𝓝[>] 1) (𝓝 (-1)) := by
      simpa using tendsto_const_nhds.add (hsub0.mul (hrem_cont.tendsto.mono_left nhdsWithin_le_nhds))
    have hre := (Complex.continuous_re.tendsto (-1 : ℂ)).comp hprod
    simp only [Complex.neg_re, Complex.one_re] at hre
    refine hre.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hne : ((σ : ℂ) + (t0 : ℂ) * I - 1 - (t0 : ℂ) * I) ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp at hr
      linarith only [hσ, hr]
    simp only [Function.comp_apply]
    have hident : ((σ - 1 : ℝ) : ℂ) * doublePoleNegLogDeriv t0 ((σ : ℂ) + (t0 : ℂ) * I) =
        (-1 : ℂ) + ((σ - 1 : ℝ) : ℂ) * rem σ := by
      unfold doublePoleNegLogDeriv
      dsimp only [rem]
      have hs : ((σ : ℂ) + (t0 : ℂ) * I - 1 - (t0 : ℂ) * I) = ((σ - 1 : ℝ) : ℂ) := by
        push_cast; ring
      have hs0 : ((σ - 1 : ℝ) : ℂ) ≠ 0 := by rwa [← hs]
      rw [hs]
      field_simp [hs0]
      ring
    rw [← hident, Complex.re_ofReal_mul]
  · linarith only [cosinePolynomial_purchase_ratio_lt_two hK hP ha0]

/-! ### 5. Sharpness Countermodel 2: Periodic-pole lattice system (`μ_pole (2 t) = 1`) -/

/-- Periodic Euler ratio with a simple pole at `s = 1`, a periodic simple pole at
`s = 1 + 2 i π / ℓ`, and a genuine boundary zero at `s = 1 + i π / ℓ`. -/
def periodicPoleZeta (ℓ : ℝ) (s : ℂ) : ℂ :=
  (1 + Complex.exp (-((s - 1) * (ℓ : ℂ)))) /
    (1 - Complex.exp (-((s - 1) * (ℓ : ℂ))))

/-- Negative logarithmic derivative of `periodicPoleZeta ℓ`. -/
def periodicPoleNegLogDeriv (ℓ : ℝ) (s : ℂ) : ℂ :=
  2 * (ℓ : ℂ) * Complex.exp (-((s - 1) * (ℓ : ℂ))) /
    (1 - Complex.exp (-((s - 1) * (ℓ : ℂ))) ^ 2)

/-- On `1 < Re s`, `-Z_per'/Z_per` equals `periodicPoleNegLogDeriv ℓ`. -/
theorem neg_logDeriv_periodicPoleZeta_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : 1 < s.re) :
    -deriv (periodicPoleZeta ℓ) s / periodicPoleZeta ℓ s = periodicPoleNegLogDeriv ℓ s := by
  let q : ℂ := Complex.exp (-((s - 1) * (ℓ : ℂ)))
  have hq_norm : ‖q‖ < 1 := by
    dsimp only [q]
    rw [Complex.norm_exp]
    have hre : (-((s - 1) * (ℓ : ℂ))).re = -((s.re - 1) * ℓ) := by
      simp [Complex.mul_re, Complex.sub_re]
    rw [hre, Real.exp_lt_one_iff]
    nlinarith only [hs, hℓ]
  have h1mq : 1 - q ≠ 0 := fun h => by
    have heq : q = 1 := by linear_combination -h
    rw [heq, norm_one] at hq_norm
    exact lt_irrefl 1 hq_norm
  have h1pq : 1 + q ≠ 0 := fun h => by
    have heq : q = -1 := by linear_combination h
    rw [heq, norm_neg, norm_one] at hq_norm
    exact lt_irrefl 1 hq_norm
  have h1mq2 : 1 - q ^ 2 ≠ 0 := by
    have hfac : 1 - q ^ 2 = (1 - q) * (1 + q) := by ring
    rw [hfac]
    exact mul_ne_zero h1mq h1pq
  have hd_q : HasDerivAt (fun z : ℂ => Complex.exp (-((z - 1) * (ℓ : ℂ))))
      (q * (-(1 * (ℓ : ℂ)))) s :=
    ((((hasDerivAt_id s).sub_const 1).mul_const (ℓ : ℂ)).neg).cexp
  have hd : HasDerivAt (periodicPoleZeta ℓ)
      (((0 + q * (-(1 * (ℓ : ℂ)))) * (1 - q) -
        (1 + q) * (0 - q * (-(1 * (ℓ : ℂ))))) / (1 - q) ^ 2) s := by
    unfold periodicPoleZeta
    exact ((hasDerivAt_const s (1 : ℂ)).add hd_q).div
      ((hasDerivAt_const s (1 : ℂ)).sub hd_q) h1mq
  rw [hd.deriv]
  unfold periodicPoleZeta periodicPoleNegLogDeriv
  change -(((0 + q * (-(1 * (ℓ : ℂ)))) * (1 - q) -
      (1 + q) * (0 - q * (-(1 * (ℓ : ℂ))))) / (1 - q) ^ 2) / ((1 + q) / (1 - q)) =
    2 * (ℓ : ℂ) * q / (1 - q ^ 2)
  field_simp [h1mq, h1pq, h1mq2]
  ring

theorem periodicPoleZeta_boundary_zero {ℓ : ℝ} (hℓ : 0 < ℓ) :
    periodicPoleZeta ℓ (1 + ((Real.pi / ℓ : ℝ) : ℂ) * I) = 0 := by
  unfold periodicPoleZeta
  have hℓc : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hℓ)
  have harg : -((1 + ((Real.pi / ℓ : ℝ) : ℂ) * I - 1) * (ℓ : ℂ)) = -(Real.pi * I) := by
    push_cast
    field_simp [hℓc]
    ring
  rw [harg, Complex.exp_neg_pi_mul_I, add_neg_cancel, zero_div]

/-- Odd-harmonic geometric series expansion of `periodicPoleNegLogDeriv` on `1 < Re s`
with positive prime weights `2 ℓ > 0`. -/
theorem periodicPoleNegLogDeriv_eq_tsum {ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : 1 < s.re) :
    periodicPoleNegLogDeriv ℓ s =
      ∑' n : ℕ, (2 * (ℓ : ℂ)) *
        Complex.exp (-((((2 * n + 1 : ℕ) : ℝ) * ℓ : ℂ) * (s - 1))) := by
  let q : ℂ := Complex.exp (-((s - 1) * (ℓ : ℂ)))
  have hq_norm : ‖q‖ < 1 := by
    dsimp only [q]
    rw [Complex.norm_exp]
    have hre : (-((s - 1) * (ℓ : ℂ))).re = -((s.re - 1) * ℓ) := by
      simp [Complex.mul_re, Complex.sub_re]
    rw [hre, Real.exp_lt_one_iff]
    nlinarith only [hs, hℓ]
  have hq2_norm : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    nlinarith only [hq_norm, norm_nonneg q]
  unfold periodicPoleNegLogDeriv
  change 2 * (ℓ : ℂ) * q / (1 - q ^ 2) = _
  rw [div_eq_mul_inv, ← tsum_geometric_of_norm_lt_one hq2_norm, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hpow : q * (q ^ 2) ^ n = Complex.exp (-((((2 * n + 1 : ℕ) : ℝ) * ℓ : ℂ) * (s - 1))) := by
    dsimp only [q]
    rw [← pow_mul, ← pow_succ', ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [mul_assoc, hpow]

/-- Harmonic positivity holds for `periodicPoleNegLogDeriv` across ALL degrees `K`
and ALL nonnegative cosine polynomials `P`. -/
theorem periodicPole_harmonic_nonneg {ℓ : ℝ} (hℓ : 0 < ℓ) {K : ℕ} {a : ℕ → ℝ}
    (hP : ∀ θ : ℝ, 0 ≤ HTGeometry.cosinePolynomial a K θ)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ ∑ k ∈ Finset.range (K + 1),
      a k * (periodicPoleNegLogDeriv ℓ ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I)).re := by
  let r : ℝ := Real.exp (-((σ - 1) * ℓ))
  have hr_lt : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith only [hσ, hℓ])
  have hr2_lt : |r ^ 2| < 1 := by
    rw [abs_of_pos (by positivity)]
    nlinarith only [hr_lt, Real.exp_pos (-((σ - 1) * ℓ))]
  have hdom : Summable (fun n : ℕ => (2 * ℓ * r) * (r ^ 2) ^ n) :=
    (summable_geometric_of_abs_lt_one hr2_lt).mul_left _
  have hterm_eq (k : ℕ) :
      a k * (periodicPoleNegLogDeriv ℓ ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I)).re =
        ∑' n : ℕ, a k * (2 * ℓ * Real.exp (-(((2 * n + 1 : ℕ) : ℝ) * ℓ * (σ - 1))) *
          Real.cos ((k : ℝ) * (((2 * n + 1 : ℕ) : ℝ) * ℓ * t))) := by
    have hs : 1 < (((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I)).re := by
      simp [Complex.add_re, Complex.mul_re, hσ]
    rw [periodicPoleNegLogDeriv_eq_tsum hℓ hs]
    let f_c : ℕ → ℂ := fun n => (2 * (ℓ : ℂ)) *
      Complex.exp (-((((2 * n + 1 : ℕ) : ℝ) * ℓ : ℂ) *
        (((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I) - 1)))
    have hsum_c : Summable f_c := by
      refine hdom.of_norm_bounded fun n => ?_
      dsimp only [f_c]
      rw [norm_mul, Complex.norm_exp]
      have h2l : ‖(2 * (ℓ : ℂ))‖ = 2 * ℓ := by
        rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓ]
      have hre : (-((((2 * n + 1 : ℕ) : ℝ) * ℓ : ℂ) *
          (((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I) - 1))).re =
          -(((2 * n + 1 : ℕ) : ℝ) * ℓ * (σ - 1)) := by
        simp [Complex.mul_re, Complex.sub_re, Complex.add_re]
      have hexp : Real.exp (-(((2 * n + 1 : ℕ) : ℝ) * ℓ * (σ - 1))) = r * (r ^ 2) ^ n := by
        dsimp only [r]
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [h2l, hre, hexp]
      linarith only
    have hsum_r : Summable (fun n : ℕ => (f_c n).re) := Complex.reCLM.summable hsum_c
    change a k * (∑' n : ℕ, f_c n).re = _
    rw [Complex.re_tsum hsum_c, ← hsum_r.tsum_mul_left]
    refine tsum_congr fun n => ?_
    congr 1
    dsimp only [f_c]
    have h2l_im : (2 * (ℓ : ℂ)).im = 0 := by simp
    have h2l_re : (2 * (ℓ : ℂ)).re = 2 * ℓ := by simp
    rw [Complex.mul_re, h2l_im, zero_mul, sub_zero, h2l_re, Complex.exp_re]
    have hre : (-((((2 * n + 1 : ℕ) : ℝ) * ℓ : ℂ) *
        (((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I) - 1))).re =
        -(((2 * n + 1 : ℕ) : ℝ) * ℓ * (σ - 1)) := by
      simp [Complex.mul_re, Complex.sub_re, Complex.add_re]
    have him : (-((((2 * n + 1 : ℕ) : ℝ) * ℓ : ℂ) *
        (((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I) - 1))).im =
        -((k : ℝ) * (((2 * n + 1 : ℕ) : ℝ) * ℓ * t)) := by
      simp [Complex.mul_im, Complex.sub_im, Complex.add_im, Complex.mul_re,
        Complex.sub_re, Complex.add_re]
      ring
    rw [hre, him, Real.cos_neg, mul_assoc]
  have hsum_k (k : ℕ) : Summable (fun n : ℕ =>
      a k * (2 * ℓ * Real.exp (-(((2 * n + 1 : ℕ) : ℝ) * ℓ * (σ - 1))) *
        Real.cos ((k : ℝ) * (((2 * n + 1 : ℕ) : ℝ) * ℓ * t)))) := by
    refine (hdom.of_norm_bounded fun n => ?_).mul_left (a k)
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_pos (mul_pos (by linarith only [hℓ]) (Real.exp_pos _))]
    have hexp : Real.exp (-(((2 * n + 1 : ℕ) : ℝ) * ℓ * (σ - 1))) = r * (r ^ 2) ^ n := by
      dsimp only [r]
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1; push_cast; ring
    rw [hexp]
    exact le_trans (mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _))
      (by linarith only)
  simp_rw [hterm_eq]
  rw [← Summable.tsum_finsetSum (fun k _ => hsum_k k)]
  refine tsum_nonneg fun n => ?_
  have hpoint : ∑ k ∈ Finset.range (K + 1),
      a k * (2 * ℓ * Real.exp (-(((2 * n + 1 : ℕ) : ℝ) * ℓ * (σ - 1))) *
        Real.cos ((k : ℝ) * (((2 * n + 1 : ℕ) : ℝ) * ℓ * t))) =
      2 * ℓ * Real.exp (-(((2 * n + 1 : ℕ) : ℝ) * ℓ * (σ - 1))) *
        HTGeometry.cosinePolynomial a K (((2 * n + 1 : ℕ) : ℝ) * ℓ * t) := by
    unfold HTGeometry.cosinePolynomial
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hpoint]
  exact mul_nonneg (by positivity) (hP _)

/-- Simple-pole residue `+1` at `u = 0` (`μ_pole 0 = 1`) for `periodicPoleNegLogDeriv`. -/
theorem tendsto_periodicPole_origin {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Tendsto (fun σ : ℝ => (σ - 1) * (periodicPoleNegLogDeriv ℓ (σ : ℂ)).re)
      (𝓝[>] 1) (𝓝 1) := by
  let g : ℝ → ℝ := fun x => 1 - Real.exp (-2 * x)
  have hg0 : g 0 = 0 := by simp [g]
  have hderiv : HasDerivAt g 2 0 := by
    have h1 : HasDerivAt (fun x : ℝ => -2 * x) (-2 * 1) 0 := (hasDerivAt_id (0 : ℝ)).const_mul (-2)
    have h2 := h1.exp.const_sub 1
    simpa only [g, mul_zero, Real.exp_zero, mul_one, zero_sub, neg_neg] using h2
  have hslope : Tendsto (fun x : ℝ => (1 - Real.exp (-2 * x)) / x) (𝓝[≠] 0) (𝓝 2) := by
    refine (hasDerivAt_iff_tendsto_slope.mp hderiv).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x _
    rw [slope_def_field, hg0, sub_zero, sub_zero]
  have hinv : Tendsto (fun x : ℝ => x / (1 - Real.exp (-2 * x))) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    have h := hslope.inv₀ (by norm_num : (2 : ℝ) ≠ 0)
    simpa only [inv_div, one_div] using h
  have hx_tend : Tendsto (fun σ : ℝ => (σ - 1) * ℓ) (𝓝[>] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous (fun σ : ℝ => (σ - 1) * ℓ) :=
        (continuous_id.sub continuous_const).mul continuous_const
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact ne_of_gt (mul_pos (sub_pos.mpr hσ) hℓ)
  have hexp_tend : Tendsto (fun σ : ℝ => 2 * Real.exp (-((σ - 1) * ℓ))) (𝓝[>] 1) (𝓝 2) := by
    have hc : Continuous (fun σ : ℝ => 2 * Real.exp (-((σ - 1) * ℓ))) :=
      continuous_const.mul (Real.continuous_exp.comp ((continuous_id.sub continuous_const).mul
        continuous_const).neg)
    simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun σ : ℝ =>
      (2 * Real.exp (-((σ - 1) * ℓ))) * (((σ - 1) * ℓ) / (1 - Real.exp (-2 * ((σ - 1) * ℓ)))))
      (𝓝[>] 1) (𝓝 1) := by
    simpa using hexp_tend.mul (hinv.comp hx_tend)
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hx_pos : 0 < (σ - 1) * ℓ := mul_pos (sub_pos.mpr hσ) hℓ
  have hden_pos : 0 < 1 - Real.exp (-2 * ((σ - 1) * ℓ)) := by
    have hexp_lt : Real.exp (-2 * ((σ - 1) * ℓ)) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith only [hx_pos])
    linarith only [hexp_lt]
  have hval : periodicPoleNegLogDeriv ℓ (σ : ℂ) =
      ((2 * ℓ * Real.exp (-((σ - 1) * ℓ)) /
        (1 - Real.exp (-2 * ((σ - 1) * ℓ))) : ℝ) : ℂ) := by
    unfold periodicPoleNegLogDeriv
    have h1 : -(((σ : ℂ) - 1) * (ℓ : ℂ)) = ((-((σ - 1) * ℓ) : ℝ) : ℂ) := by push_cast; ring
    rw [h1, ← Complex.ofReal_exp, ← sq, ← Real.exp_nat_mul]
    push_cast
    congr 2
    ring
  rw [hval, Complex.ofReal_re]
  field_simp [ne_of_gt hden_pos]
  ring

/-- Sharpness of harmonic pole isolation: `periodicPoleZeta ℓ` has positive
odd-harmonic prime weights, a simple pole `μ_pole 0 = 1`, a periodic simple pole
`μ_pole (2 π / ℓ) = 1` at the second harmonic, and a surviving boundary zero at
`s = 1 + i π / ℓ` (`μ_zero (π / ℓ) = 1`). -/
theorem periodicPole_boundary_zero_survives_with_second_harmonic_pole {ℓ : ℝ} (hℓ : 0 < ℓ) :
    periodicPoleZeta ℓ (1 + ((Real.pi / ℓ : ℝ) : ℂ) * I) = 0 ∧
      Tendsto (fun σ : ℝ => (σ - 1) * (periodicPoleNegLogDeriv ℓ (σ : ℂ)).re)
        (𝓝[>] 1) (𝓝 1) ∧
      Tendsto (fun σ : ℝ =>
        (σ - 1) * (periodicPoleNegLogDeriv ℓ
          ((σ : ℂ) + ((Real.pi / ℓ : ℝ) : ℂ) * I)).re)
        (𝓝[>] 1) (𝓝 (-1)) ∧
      Tendsto (fun σ : ℝ =>
        (σ - 1) * (periodicPoleNegLogDeriv ℓ
          ((σ : ℂ) + ((2 * (Real.pi / ℓ) : ℝ) : ℂ) * I)).re)
        (𝓝[>] 1) (𝓝 1) := by
  have hℓc : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hℓ)
  have hshift_one (σ : ℝ) :
      periodicPoleNegLogDeriv ℓ ((σ : ℂ) + ((Real.pi / ℓ : ℝ) : ℂ) * I) =
        -periodicPoleNegLogDeriv ℓ (σ : ℂ) := by
    unfold periodicPoleNegLogDeriv
    have hexp : Complex.exp (-((((σ : ℂ) + ((Real.pi / ℓ : ℝ) : ℂ) * I) - 1) * (ℓ : ℂ))) =
        -Complex.exp (-(((σ : ℂ) - 1) * (ℓ : ℂ))) := by
      have harg : -((((σ : ℂ) + ((Real.pi / ℓ : ℝ) : ℂ) * I) - 1) * (ℓ : ℂ)) =
          -(((σ : ℂ) - 1) * (ℓ : ℂ)) + (-(Real.pi * I)) := by
        push_cast; field_simp [hℓc]; ring
      rw [harg, Complex.exp_add, Complex.exp_neg_pi_mul_I, mul_neg_one]
    rw [hexp, neg_sq]
    ring
  have hshift_two (σ : ℝ) :
      periodicPoleNegLogDeriv ℓ ((σ : ℂ) + ((2 * (Real.pi / ℓ) : ℝ) : ℂ) * I) =
        periodicPoleNegLogDeriv ℓ (σ : ℂ) := by
    unfold periodicPoleNegLogDeriv
    have hexp : Complex.exp (-((((σ : ℂ) + ((2 * (Real.pi / ℓ) : ℝ) : ℂ) * I) - 1) * (ℓ : ℂ))) =
        Complex.exp (-(((σ : ℂ) - 1) * (ℓ : ℂ))) := by
      have harg : -((((σ : ℂ) + ((2 * (Real.pi / ℓ) : ℝ) : ℂ) * I) - 1) * (ℓ : ℂ)) =
          -(((σ : ℂ) - 1) * (ℓ : ℂ)) + ((-(Real.pi * I)) + (-(Real.pi * I))) := by
        push_cast; field_simp [hℓc]; ring
      rw [harg, Complex.exp_add, Complex.exp_add, Complex.exp_neg_pi_mul_I]
      ring
    rw [hexp]
  refine ⟨periodicPoleZeta_boundary_zero hℓ, tendsto_periodicPole_origin hℓ, ?_, ?_⟩
  · refine (tendsto_periodicPole_origin hℓ).neg.congr fun σ => ?_
    rw [hshift_one σ, Complex.neg_re]
    ring
  · refine (tendsto_periodicPole_origin hℓ).congr fun σ => ?_
    rw [hshift_two σ]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
