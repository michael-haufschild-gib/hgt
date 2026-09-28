import GaloisForLFunctions.HTGeometry.GaussianSchwartz
import GaloisForLFunctions.HTGeometry.ConstitutivePositiveEvenLaplaceEscape
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Positive even Schwartz sources and the bilateral Laplace reporter

For a real source `f` the bilateral Laplace transform is `𝓛_z f = ∫ e^{zx} f(x) dx`.  This
module builds the positive even Gaussian packets

* `g(x) = π^{-1/2} e^{-x²}` with `𝓛_z g = e^{z²/4}`,
* `g_R(x) = g(x - R) + g(x + R)` with `𝓛_z g_R = e^{z²/4}(e^{zR} + e^{-zR})`,

proves the Schwartz translation estimate `p_{k,n}(f(· - R)) ≤ (1 + |R|)^k · C_{k,n}(f)`, and
derives the remote-packet escape: the positive even sources `q_N = e^{-|Re z| R_N} g_{R_N}` tend
to zero in the Schwartz topology while `𝓛_z q_N → e^{z²/4} ≠ 0`.  Consequently evaluation of the
bilateral Laplace transform at any `z` with `Re z ≠ 0` is discontinuous on the Schwartz sources
with entire Laplace transform.

The explicit two-shell source `cosh(2A) g_x + cosh(A) g_{2x}` with `x = π/|τ|`, `A = a x` is a
strictly positive even Schwartz function whose Laplace transform vanishes on the quartet
`±(a ± iτ)`.
-/

open Complex MeasureTheory Filter Topology
open scoped SchwartzMap

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PositiveEvenLaplaceEscape

/-! ## The bilateral Laplace transform -/

/-- The bilateral Laplace transform `𝓛_z f = ∫ e^{zx} f(x) dx` of a real source. -/
def bilateralLaplace (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, cexp (z * x) * (f x : ℂ)

/-- A real source has an entire bilateral Laplace transform when every exponential moment
converges absolutely. -/
def HasEntireLaplace (f : ℝ → ℝ) : Prop :=
  ∀ z : ℂ, Integrable (fun x : ℝ => cexp (z * x) * (f x : ℂ))

theorem hasEntireLaplace_zero : HasEntireLaplace (fun _ => 0) := fun z => by
  simp only [Complex.ofReal_zero, mul_zero]
  exact integrable_zero _ _ _

theorem HasEntireLaplace.add {f g : ℝ → ℝ} (hf : HasEntireLaplace f) (hg : HasEntireLaplace g) :
    HasEntireLaplace (fun x => f x + g x) := fun z =>
  ((hf z).add (hg z)).congr (Eventually.of_forall fun x => by
    simp only [Pi.add_apply, Complex.ofReal_add, mul_add])

theorem HasEntireLaplace.const_mul {f : ℝ → ℝ} (c : ℝ) (hf : HasEntireLaplace f) :
    HasEntireLaplace (fun x => c * f x) := fun z =>
  ((hf z).const_mul (c : ℂ)).congr (Eventually.of_forall fun x => by
    simp only [Complex.ofReal_mul]; ring)

theorem HasEntireLaplace.comp_sub {f : ℝ → ℝ} (hf : HasEntireLaplace f) (R : ℝ) :
    HasEntireLaplace (fun x => f (x - R)) := fun z =>
  (((hf z).comp_sub_right R).const_mul (cexp (z * R))).congr (Eventually.of_forall fun x => by
    simp only
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring)

theorem bilateralLaplace_zero (z : ℂ) : bilateralLaplace (fun _ => 0) z = 0 := by
  simp [bilateralLaplace]

theorem bilateralLaplace_add {f g : ℝ → ℝ} (hf : HasEntireLaplace f) (hg : HasEntireLaplace g)
    (z : ℂ) :
    bilateralLaplace (fun x => f x + g x) z = bilateralLaplace f z + bilateralLaplace g z := by
  unfold bilateralLaplace
  rw [← integral_add (hf z) (hg z)]
  congr 1
  funext x
  push_cast
  ring

theorem bilateralLaplace_const_mul (f : ℝ → ℝ) (c : ℝ) (z : ℂ) :
    bilateralLaplace (fun x => c * f x) z = c * bilateralLaplace f z := by
  unfold bilateralLaplace
  rw [← integral_const_mul]
  congr 1
  funext x
  push_cast
  ring

/-- Translation multiplies the bilateral Laplace transform by `e^{zR}`. -/
theorem bilateralLaplace_comp_sub (f : ℝ → ℝ) (R : ℝ) (z : ℂ) :
    bilateralLaplace (fun x => f (x - R)) z = cexp (z * R) * bilateralLaplace f z := by
  unfold bilateralLaplace
  rw [← integral_const_mul,
    ← integral_sub_right_eq_self (fun x : ℝ => cexp (z * R) * (cexp (z * x) * (f x : ℂ))) R]
  congr 1
  funext x
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- An even source has an even bilateral Laplace transform. -/
theorem bilateralLaplace_neg_of_even {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) (z : ℂ) :
    bilateralLaplace f (-z) = bilateralLaplace f z := by
  unfold bilateralLaplace
  conv_rhs => rw [← integral_neg_eq_self]
  congr 1
  funext x
  rw [hf]
  push_cast
  ring_nf

/-- A real source has a conjugation-symmetric bilateral Laplace transform. -/
theorem bilateralLaplace_conj (f : ℝ → ℝ) (z : ℂ) :
    bilateralLaplace f (starRingEnd ℂ z) = starRingEnd ℂ (bilateralLaplace f z) := by
  unfold bilateralLaplace
  rw [← integral_conj]
  congr 1
  funext x
  rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]

/-- The functional-equation quartet: a real even source vanishing at `z` also vanishes at
`-z`, `z̄` and `-z̄`. -/
theorem bilateralLaplace_quartet {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) {z : ℂ}
    (hz : bilateralLaplace f z = 0) :
    bilateralLaplace f z = 0 ∧ bilateralLaplace f (-z) = 0 ∧
      bilateralLaplace f (starRingEnd ℂ z) = 0 ∧
      bilateralLaplace f (-starRingEnd ℂ z) = 0 := by
  have hc : bilateralLaplace f (starRingEnd ℂ z) = 0 := by
    rw [bilateralLaplace_conj, hz, map_zero]
  exact ⟨hz, by rw [bilateralLaplace_neg_of_even hf, hz], hc,
    by rw [bilateralLaplace_neg_of_even hf, hc]⟩

/-- Zeros of a real even source are invariant under `z ↦ -z` and `z ↦ z̄`, so it suffices to
test the point `|Re z| + i |Im z|`. -/
theorem bilateralLaplace_eq_zero_iff_abs {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) (z : ℂ) :
    bilateralLaplace f z = 0 ↔
      bilateralLaplace f (((|z.re| : ℝ) : ℂ) + ((|z.im| : ℝ) : ℂ) * I) = 0 := by
  have hneg : ∀ w, bilateralLaplace f (-w) = 0 ↔ bilateralLaplace f w = 0 := fun w => by
    rw [bilateralLaplace_neg_of_even hf]
  have hconj : ∀ w, bilateralLaplace f (starRingEnd ℂ w) = 0 ↔ bilateralLaplace f w = 0 :=
    fun w => by rw [bilateralLaplace_conj, map_eq_zero]
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
  rcases le_total 0 z.re with hre | hre <;> rcases le_total 0 z.im with him | him
  · rw [abs_of_nonneg hre, abs_of_nonneg him, ← hz]
  · rw [abs_of_nonneg hre, abs_of_nonpos him, ← hconj]
    congr! 2
    apply Complex.ext <;> simp
  · rw [abs_of_nonpos hre, abs_of_nonneg him, ← hneg, ← hconj]
    congr! 2
    apply Complex.ext <;> simp
  · rw [abs_of_nonpos hre, abs_of_nonpos him, ← hneg]
    congr! 2
    apply Complex.ext <;> simp

/-! ## The Gaussian packet -/

/-- The positive Gaussian packet `g(x) = π^{-1/2} e^{-x²}` as a real Schwartz function. -/
def gaussianPacket : 𝓢(ℝ, ℝ) :=
  (Real.sqrt Real.pi)⁻¹ • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (ContinuousLinearEquiv.unitsEquivAut ℝ
      (Units.mk0 (Real.sqrt Real.pi)⁻¹ (by positivity))) gaussianSchwartzReal

theorem gaussianPacket_apply (x : ℝ) :
    gaussianPacket x = (Real.sqrt Real.pi)⁻¹ * Real.exp (-x ^ 2) := by
  have hpi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hs : Real.sqrt Real.pi ≠ 0 := by positivity
  simp only [gaussianPacket, smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.unitsEquivAut_apply, Units.val_mk0, gaussianSchwartzReal_apply,
    gaussReal, smul_eq_mul]
  congr 2
  field_simp
  rw [hpi]
  ring

theorem gaussianPacket_pos (x : ℝ) : 0 < gaussianPacket x := by
  rw [gaussianPacket_apply]
  positivity

theorem gaussianPacket_neg (x : ℝ) : gaussianPacket (-x) = gaussianPacket x := by
  simp only [gaussianPacket_apply, neg_sq]

theorem gaussianPacket_integrand (z : ℂ) (x : ℝ) :
    cexp (z * x) * (gaussianPacket x : ℂ) =
      ((Real.sqrt Real.pi)⁻¹ : ℂ) * cexp (-1 * (x : ℂ) ^ 2 + z * x + 0) := by
  rw [gaussianPacket_apply]
  push_cast
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

/-- The Gaussian packet has an entire bilateral Laplace transform. -/
theorem hasEntireLaplace_gaussianPacket : HasEntireLaplace gaussianPacket := fun z => by
  have h := (integrable_cexp_quadratic (b := 1) (by simp) z 0).const_mul
    ((Real.sqrt Real.pi)⁻¹ : ℂ)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only
  rw [gaussianPacket_integrand]

/-- `(EA.4)`  The Laplace transform of the Gaussian packet is `G(z) = e^{z²/4}`. -/
theorem bilateralLaplace_gaussianPacket (z : ℂ) :
    bilateralLaplace gaussianPacket z = cexp (z ^ 2 / 4) := by
  unfold bilateralLaplace
  simp_rw [gaussianPacket_integrand]
  rw [integral_const_mul, integral_cexp_quadratic (b := -1) (by simp) z 0]
  have hsq : ((Real.pi : ℂ) / -(-1 : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    rw [neg_neg, div_one, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
    push_cast
    rfl
  have hs : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [hsq, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  congr 1
  ring

/-- The packet translated to `R`. -/
def shiftedPacket (R : ℝ) : 𝓢(ℝ, ℝ) := SchwartzMap.compSubConstCLM ℝ R gaussianPacket

theorem shiftedPacket_apply (R x : ℝ) : shiftedPacket R x = gaussianPacket (x - R) := rfl

/-- The symmetric two-bump packet `g_R(x) = g(x - R) + g(x + R)`. -/
def evenPacket (R : ℝ) : 𝓢(ℝ, ℝ) := shiftedPacket R + shiftedPacket (-R)

theorem evenPacket_apply (R x : ℝ) :
    evenPacket R x = gaussianPacket (x - R) + gaussianPacket (x + R) := by
  simp [evenPacket, shiftedPacket_apply, sub_neg_eq_add]

theorem evenPacket_pos (R x : ℝ) : 0 < evenPacket R x := by
  rw [evenPacket_apply]
  exact add_pos (gaussianPacket_pos _) (gaussianPacket_pos _)

theorem evenPacket_neg (R x : ℝ) : evenPacket R (-x) = evenPacket R x := by
  rw [evenPacket_apply, evenPacket_apply, ← gaussianPacket_neg (-x - R),
    ← gaussianPacket_neg (-x + R)]
  ring_nf

theorem evenPacket_neg_center (R : ℝ) : evenPacket (-R) = evenPacket R := by
  ext x
  rw [evenPacket_apply, evenPacket_apply, sub_neg_eq_add, ← sub_eq_add_neg]
  ring

theorem hasEntireLaplace_evenPacket (R : ℝ) : HasEntireLaplace (evenPacket R) := by
  have h := (hasEntireLaplace_gaussianPacket.comp_sub R).add
    (hasEntireLaplace_gaussianPacket.comp_sub (-R))
  intro z
  refine (h z).congr (Eventually.of_forall fun x => ?_)
  simp only [evenPacket, add_apply, shiftedPacket_apply]

/-- `(EA.4)`  `𝓛_z g_R = e^{z²/4}(e^{zR} + e^{-zR}) = 2 G(z) cosh(zR)`. -/
theorem bilateralLaplace_evenPacket (R : ℝ) (z : ℂ) :
    bilateralLaplace (evenPacket R) z =
      cexp (z ^ 2 / 4) * (cexp (z * R) + cexp (-(z * R))) := by
  have h := bilateralLaplace_add (hasEntireLaplace_gaussianPacket.comp_sub R)
    (hasEntireLaplace_gaussianPacket.comp_sub (-R)) z
  have he : (fun x => evenPacket R x) =
      fun x => gaussianPacket (x - R) + gaussianPacket (x - -R) := by
    funext x
    simp only [evenPacket, add_apply, shiftedPacket_apply]
  rw [show bilateralLaplace (evenPacket R) z = bilateralLaplace (fun x => evenPacket R x) z
    from rfl, he, h, bilateralLaplace_comp_sub, bilateralLaplace_comp_sub,
    bilateralLaplace_gaussianPacket]
  push_cast
  ring_nf

theorem bilateralLaplace_evenPacket_eq_cosh (R : ℝ) (z : ℂ) :
    bilateralLaplace (evenPacket R) z = 2 * cexp (z ^ 2 / 4) * Complex.cosh (z * R) := by
  rw [bilateralLaplace_evenPacket, Complex.cosh]
  ring

/-! ## Linear structure on Schwartz sources -/

theorem HasEntireLaplace.schwartz_add {f g : 𝓢(ℝ, ℝ)} (hf : HasEntireLaplace f)
    (hg : HasEntireLaplace g) : HasEntireLaplace ⇑(f + g) :=
  hf.add hg

theorem HasEntireLaplace.schwartz_smul {f : 𝓢(ℝ, ℝ)} (c : ℝ) (hf : HasEntireLaplace f) :
    HasEntireLaplace ⇑(c • f) :=
  hf.const_mul c

theorem bilateralLaplace_schwartz_add {f g : 𝓢(ℝ, ℝ)} (hf : HasEntireLaplace f)
    (hg : HasEntireLaplace g) (z : ℂ) :
    bilateralLaplace ⇑(f + g) z = bilateralLaplace f z + bilateralLaplace g z :=
  bilateralLaplace_add hf hg z

theorem bilateralLaplace_schwartz_smul (f : 𝓢(ℝ, ℝ)) (c : ℝ) (z : ℂ) :
    bilateralLaplace ⇑(c • f) z = c * bilateralLaplace f z :=
  bilateralLaplace_const_mul f c z

/-- The Schwartz sources with entire bilateral Laplace transform. -/
def entireLaplaceSubmodule : Submodule ℝ 𝓢(ℝ, ℝ) where
  carrier := {f | HasEntireLaplace f}
  add_mem' hf hg := HasEntireLaplace.schwartz_add hf hg
  zero_mem' := hasEntireLaplace_zero
  smul_mem' c _ hf := HasEntireLaplace.schwartz_smul c hf

/-! ## The Schwartz translation estimate -/

/-- The seminorm constant `C_{k,n}(f) = 2^k max_{(i,j) ≤ (k,n)} p_{i,j}(f)`. -/
def translationConstant (k n : ℕ) (f : 𝓢(ℝ, ℝ)) : ℝ :=
  2 ^ k * ((Finset.Iic (k, n)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) f

theorem translationConstant_nonneg (k n : ℕ) (f : 𝓢(ℝ, ℝ)) :
    0 ≤ translationConstant k n f :=
  mul_nonneg (by positivity) (apply_nonneg _ _)

/-- `(EA.13)`  The translation estimate `p_{k,n}(f(· - R)) ≤ (1 + |R|)^k C_{k,n}(f)`. -/
theorem seminorm_compSubConst_le (f : 𝓢(ℝ, ℝ)) (R : ℝ) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (SchwartzMap.compSubConstCLM ℝ R f) ≤
      (1 + |R|) ^ k * translationConstant k n f := by
  refine SchwartzMap.seminorm_le_bound ℝ k n _
    (mul_nonneg (by positivity) (translationConstant_nonneg k n f)) fun x => ?_
  have hD : iteratedFDeriv ℝ n (SchwartzMap.compSubConstCLM ℝ R f) x =
      iteratedFDeriv ℝ n f (x - R) :=
    iteratedFDeriv_comp_sub (f := ⇑f) n R x
  rw [hD]
  have hx : ‖x‖ ≤ (1 + |R|) * (1 + ‖x - R‖) := by
    have h : ‖x‖ ≤ ‖x - R‖ + |R| := by
      calc ‖x‖ = ‖(x - R) + R‖ := by ring_nf
        _ ≤ ‖x - R‖ + ‖R‖ := norm_add_le _ _
        _ = ‖x - R‖ + |R| := by rw [Real.norm_eq_abs R]
    nlinarith [norm_nonneg (x - R), abs_nonneg R]
  have h2 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, n)) le_rfl le_rfl f
    (x - R)
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f (x - R)‖
      ≤ ((1 + |R|) * (1 + ‖x - R‖)) ^ k * ‖iteratedFDeriv ℝ n f (x - R)‖ := by gcongr
    _ = (1 + |R|) ^ k * ((1 + ‖x - R‖) ^ k * ‖iteratedFDeriv ℝ n f (x - R)‖) := by
      rw [mul_pow, mul_assoc]
    _ ≤ (1 + |R|) ^ k * translationConstant k n f := by
      gcongr
      exact h2

/-- `(EA.13)`  `p_{k,n}(g_R) ≤ 2 (1 + |R|)^k C_{k,n}(g)`. -/
theorem seminorm_evenPacket_le (R : ℝ) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (evenPacket R) ≤
      2 * ((1 + |R|) ^ k * translationConstant k n gaussianPacket) := by
  have h1 := seminorm_compSubConst_le gaussianPacket R k n
  have h2 := seminorm_compSubConst_le gaussianPacket (-R) k n
  rw [abs_neg] at h2
  calc SchwartzMap.seminorm ℝ k n (evenPacket R)
      ≤ SchwartzMap.seminorm ℝ k n (shiftedPacket R) +
          SchwartzMap.seminorm ℝ k n (shiftedPacket (-R)) := map_add_le_add _ _ _
    _ ≤ _ := by
      unfold shiftedPacket
      linarith

/-- Polynomial growth is beaten by exponential decay: `(1 + R)^k e^{-bR} → 0`. -/
theorem tendsto_one_add_pow_mul_exp_neg {b : ℝ} (hb : 0 < b) (k : ℕ) :
    Tendsto (fun R : ℝ => (1 + R) ^ k * Real.exp (-b * R)) atTop (𝓝 0) := by
  have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) b hb).comp
    (tendsto_atTop_add_const_left atTop 1 tendsto_id)).const_mul (Real.exp b)
  rw [mul_zero] at h
  refine h.congr fun R => ?_
  simp only [Function.comp_apply, id, Real.rpow_natCast]
  rw [show -b * (1 + R) = -b + -b * R by ring, Real.exp_add,
    show Real.exp b * ((1 + R) ^ k * (Real.exp (-b) * Real.exp (-b * R))) =
      (Real.exp b * Real.exp (-b)) * ((1 + R) ^ k * Real.exp (-b * R)) by ring,
    ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-! ## Remote-packet escape -/

/-- Remote periods: a sequence `R_N → ∞` with `e^{iτR_N} = 1`. -/
theorem exists_remote_periods (τ : ℝ) :
    ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧ (∀ N, 0 ≤ R N) ∧
      ∀ N, cexp (((τ * R N : ℝ) : ℂ) * I) = 1 := by
  by_cases hτ : τ = 0
  · refine ⟨fun N => N, tendsto_natCast_atTop_atTop, fun N => N.cast_nonneg, fun N => ?_⟩
    simp [hτ]
  · refine ⟨fun N => 2 * Real.pi * N / |τ|, ?_, fun N => by positivity, fun N => ?_⟩
    · have h : Tendsto (fun N : ℕ => (N : ℝ) * (2 * Real.pi / |τ|)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
      exact h.congr fun N => by ring
    · rcases lt_or_gt_of_ne hτ with h | h
      · rw [abs_of_neg h]
        have hr : τ * (2 * Real.pi * N / -τ) = -(2 * Real.pi * N) := by
          field_simp
        rw [hr, show ((-(2 * Real.pi * N) : ℝ) : ℂ) * I =
          ((-(N : ℤ) : ℤ) : ℂ) * (2 * Real.pi * I) by push_cast; ring,
          Complex.exp_int_mul_two_pi_mul_I]
      · rw [abs_of_pos h]
        have hr : τ * (2 * Real.pi * N / τ) = 2 * Real.pi * N := by
          field_simp
        rw [hr, show ((2 * Real.pi * N : ℝ) : ℂ) * I = (N : ℂ) * (2 * Real.pi * I) by
          push_cast; ring, Complex.exp_nat_mul_two_pi_mul_I]

/-- On a period `e^{i Im(z) R} = 1`, the exponentials `e^{±zR}` are real. -/
theorem cexp_mul_of_period {z : ℂ} {R : ℝ} (hR : cexp (((z.im * R : ℝ) : ℂ) * I) = 1) :
    cexp (z * R) = (Real.exp (z.re * R) : ℂ) ∧
      cexp (-(z * R)) = (Real.exp (-(z.re * R)) : ℂ) := by
  have hz : z * R = ((z.re * R : ℝ) : ℂ) + ((z.im * R : ℝ) : ℂ) * I := by
    conv_lhs => rw [← Complex.re_add_im z]
    push_cast
    ring
  have h1 : cexp (z * R) = (Real.exp (z.re * R) : ℂ) := by
    rw [hz, Complex.exp_add, hR, mul_one, Complex.ofReal_exp]
  refine ⟨h1, ?_⟩
  rw [Complex.exp_neg, h1, ← Complex.ofReal_inv, ← Real.exp_neg]

theorem exp_neg_abs_mul_add_exp (a R : ℝ) :
    Real.exp (-|a| * R) * (Real.exp (a * R) + Real.exp (-(a * R))) =
      1 + Real.exp (-2 * |a| * R) := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h, mul_add, ← Real.exp_add, ← Real.exp_add,
      show -a * R + a * R = 0 by ring, Real.exp_zero, show -a * R + -(a * R) = -2 * a * R by ring]
  · rw [abs_of_nonpos h, mul_add, ← Real.exp_add, ← Real.exp_add,
      show - -a * R + -(a * R) = 0 by ring, Real.exp_zero,
      show - -a * R + a * R = -2 * -a * R by ring, add_comm]

/-- The normalized remote packet `q = e^{-|Re z| R} g_R`. -/
def remotePacket (b R : ℝ) : 𝓢(ℝ, ℝ) := Real.exp (-b * R) • evenPacket R

theorem remotePacket_apply (b R x : ℝ) :
    remotePacket b R x = Real.exp (-b * R) * evenPacket R x := rfl

theorem remotePacket_pos (b R x : ℝ) : 0 < remotePacket b R x := by
  rw [remotePacket_apply]
  exact mul_pos (Real.exp_pos _) (evenPacket_pos _ _)

theorem remotePacket_neg (b R x : ℝ) : remotePacket b R (-x) = remotePacket b R x := by
  rw [remotePacket_apply, remotePacket_apply, evenPacket_neg]

theorem hasEntireLaplace_remotePacket (b R : ℝ) : HasEntireLaplace (remotePacket b R) :=
  (hasEntireLaplace_evenPacket R).const_mul _

/-- `(EA.14)`  On a period, `𝓛_z q = G(z)(1 + e^{-2|Re z| R})`. -/
theorem bilateralLaplace_remotePacket {z : ℂ} {R : ℝ}
    (hR : cexp (((z.im * R : ℝ) : ℂ) * I) = 1) :
    bilateralLaplace (remotePacket |z.re| R) z =
      cexp (z ^ 2 / 4) * (1 + (Real.exp (-2 * |z.re| * R) : ℂ)) := by
  rw [remotePacket, bilateralLaplace_schwartz_smul, bilateralLaplace_evenPacket]
  obtain ⟨h1, h2⟩ := cexp_mul_of_period hR
  rw [h1, h2]
  have hk : (Real.exp (-|z.re| * R) : ℂ) *
      ((Real.exp (z.re * R) : ℂ) + (Real.exp (-(z.re * R)) : ℂ)) =
        1 + (Real.exp (-2 * |z.re| * R) : ℂ) := by
    exact_mod_cast exp_neg_abs_mul_add_exp z.re R
  rw [← hk]
  ring

/-- The Schwartz seminorms of the remote packet decay: `p_{k,n}(q) ≤ 2 C (1+R)^k e^{-bR}`. -/
theorem seminorm_remotePacket_le (b : ℝ) {R : ℝ} (hR : 0 ≤ R) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (remotePacket b R) ≤
      2 * translationConstant k n gaussianPacket * ((1 + R) ^ k * Real.exp (-b * R)) := by
  rw [remotePacket, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-b * R) * SchwartzMap.seminorm ℝ k n (evenPacket R)
      ≤ Real.exp (-b * R) * (2 * ((1 + |R|) ^ k * translationConstant k n gaussianPacket)) := by
        gcongr
        exact seminorm_evenPacket_le R k n
    _ = _ := by
      rw [abs_of_nonneg hR]
      ring

/-- Remote packets on remote periods tend to zero in the Schwartz topology. -/
theorem tendsto_remotePacket_zero {b : ℝ} (hb : 0 < b) {R : ℕ → ℝ}
    (hRlim : Tendsto R atTop atTop) (hR0 : ∀ N, 0 ≤ R N) :
    Tendsto (fun N => remotePacket b (R N)) atTop (𝓝 0) := by
  rw [(schwartz_withSeminorms ℝ ℝ ℝ).tendsto_nhds _ 0]
  rintro ⟨k, n⟩ ε hε
  simp only [sub_zero, SchwartzMap.schwartzSeminormFamily_apply]
  have hlim : Tendsto (fun N => 2 * translationConstant k n gaussianPacket *
      ((1 + R N) ^ k * Real.exp (-b * R N))) atTop (𝓝 0) := by
    have h := ((tendsto_one_add_pow_mul_exp_neg hb k).comp hRlim).const_mul
      (2 * translationConstant k n gaussianPacket)
    rw [mul_zero] at h
    exact h
  filter_upwards [hlim.eventually (Iio_mem_nhds hε)] with N hN
  exact lt_of_le_of_lt (seminorm_remotePacket_le b (hR0 N) k n) hN

/-- `(EA.11)`  **Remote-packet escape.**  For `Re z ≠ 0` there are strictly positive even Schwartz
sources with entire Laplace transform that tend to zero in the Schwartz topology while their
Laplace values at `z` tend to `G(z) = e^{z²/4} ≠ 0`. -/
theorem remotePacketEscape {z : ℂ} (hz : z.re ≠ 0) :
    ∃ q : ℕ → 𝓢(ℝ, ℝ), (∀ N x, 0 < q N x) ∧ (∀ N x, q N (-x) = q N x) ∧
      (∀ N, HasEntireLaplace (q N)) ∧ Tendsto q atTop (𝓝 0) ∧
      Tendsto (fun N => bilateralLaplace (q N) z) atTop (𝓝 (cexp (z ^ 2 / 4))) := by
  obtain ⟨R, hRlim, hR0, hRper⟩ := exists_remote_periods z.im
  have hb : 0 < |z.re| := abs_pos.mpr hz
  refine ⟨fun N => remotePacket |z.re| (R N), fun N x => remotePacket_pos _ _ x,
    fun N x => remotePacket_neg _ _ x, fun N => hasEntireLaplace_remotePacket _ _,
    tendsto_remotePacket_zero hb hRlim hR0, ?_⟩
  have hexp : Tendsto (fun N => Real.exp (-2 * |z.re| * R N)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hRlim.const_mul_atTop_of_neg (by linarith))
  have hexpC : Tendsto (fun N => (Real.exp (-2 * |z.re| * R N) : ℂ)) atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp hexp
    rw [Complex.ofReal_zero] at h
    exact h
  have h := (tendsto_const_nhds (x := cexp (z ^ 2 / 4))).mul
    ((tendsto_const_nhds (x := (1 : ℂ))).add hexpC)
  rw [add_zero, mul_one] at h
  exact h.congr fun N => (bilateralLaplace_remotePacket (hRper N)).symm

/-- **The Laplace reporter is Schwartz-discontinuous.**  For `Re z ≠ 0`, evaluation of the
bilateral Laplace transform at `z` on the Schwartz sources with entire Laplace transform is not
continuous at the origin for the inherited Schwartz topology. -/
theorem not_continuousAt_bilateralLaplace {z : ℂ} (hz : z.re ≠ 0) :
    ¬ ContinuousAt (fun f : entireLaplaceSubmodule => bilateralLaplace f z) 0 := by
  intro hc
  obtain ⟨q, -, -, hent, hq0, hqL⟩ := remotePacketEscape hz
  let q' : ℕ → entireLaplaceSubmodule := fun N => ⟨q N, hent N⟩
  have hq' : Tendsto q' atTop (𝓝 0) := tendsto_subtype_rng.mpr hq0
  have h1 := hc.tendsto.comp hq'
  have h0 : bilateralLaplace ((0 : entireLaplaceSubmodule) : 𝓢(ℝ, ℝ)) z = 0 :=
    bilateralLaplace_zero z
  rw [h0] at h1
  exact Complex.exp_ne_zero _ (tendsto_nhds_unique hqL h1)

/-- **No continuous extension.**  For `Re z ≠ 0` no function on Schwartz space that is continuous
at the origin agrees with `𝓛_z` on the sources with entire Laplace transform. -/
theorem not_exists_continuous_extension {z : ℂ} (hz : z.re ≠ 0) :
    ¬ ∃ L : 𝓢(ℝ, ℝ) → ℂ, ContinuousAt L 0 ∧
      ∀ f : 𝓢(ℝ, ℝ), HasEntireLaplace f → L f = bilateralLaplace f z := by
  rintro ⟨L, hc, hL⟩
  obtain ⟨q, -, -, hent, hq0, hqL⟩ := remotePacketEscape hz
  have h1 := hc.tendsto.comp hq0
  have h0 : L 0 = 0 := by
    rw [hL 0 hasEntireLaplace_zero]
    exact bilateralLaplace_zero z
  rw [h0] at h1
  have h2 : Tendsto (fun N => bilateralLaplace (q N) z) atTop (𝓝 0) :=
    h1.congr fun N => hL (q N) (hent N)
  exact Complex.exp_ne_zero _ (tendsto_nhds_unique hqL h2)

/-! ## The explicit positive two-shell source -/

/-- `(EA.7)–(EA.9)`  The positive two-shell source `cosh(2A) g_x + cosh(A) g_{2x}` with
`x = π/|τ|` and `A = a x`: the Gaussian smoothing of the atomic measure
`cosh(2A)(δ_x + δ_{-x}) + cosh(A)(δ_{2x} + δ_{-2x})`. -/
def twoShellSource (a τ : ℝ) : 𝓢(ℝ, ℝ) :=
  Real.cosh (2 * (a * (Real.pi / |τ|))) • evenPacket (Real.pi / |τ|) +
    Real.cosh (a * (Real.pi / |τ|)) • evenPacket (2 * (Real.pi / |τ|))

theorem twoShellSource_apply (a τ x : ℝ) :
    twoShellSource a τ x =
      Real.cosh (2 * (a * (Real.pi / |τ|))) * evenPacket (Real.pi / |τ|) x +
        Real.cosh (a * (Real.pi / |τ|)) * evenPacket (2 * (Real.pi / |τ|)) x := rfl

theorem twoShellSource_pos (a τ x : ℝ) : 0 < twoShellSource a τ x := by
  rw [twoShellSource_apply]
  exact add_pos (mul_pos (Real.cosh_pos _) (evenPacket_pos _ _))
    (mul_pos (Real.cosh_pos _) (evenPacket_pos _ _))

theorem twoShellSource_neg (a τ x : ℝ) : twoShellSource a τ (-x) = twoShellSource a τ x := by
  rw [twoShellSource_apply, twoShellSource_apply, evenPacket_neg, evenPacket_neg]

theorem twoShellSource_abs (a τ : ℝ) : twoShellSource |a| τ = twoShellSource a τ := by
  ext x
  rw [twoShellSource_apply, twoShellSource_apply]
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, neg_mul, mul_neg, Real.cosh_neg, Real.cosh_neg]

theorem hasEntireLaplace_twoShellSource (a τ : ℝ) : HasEntireLaplace (twoShellSource a τ) :=
  HasEntireLaplace.schwartz_add ((hasEntireLaplace_evenPacket _).schwartz_smul _)
    ((hasEntireLaplace_evenPacket _).schwartz_smul _)

/-- `(EA.8)–(EA.9)`  `𝓛_w f = 2 G(w) (cosh(2A) cosh(wx) + cosh(A) cosh(2wx))`. -/
theorem bilateralLaplace_twoShellSource (a τ : ℝ) (w : ℂ) :
    bilateralLaplace (twoShellSource a τ) w =
      2 * cexp (w ^ 2 / 4) * positiveEvenTwoShellLaplace (a * (Real.pi / |τ|))
        (w * ((Real.pi / |τ| : ℝ) : ℂ)) := by
  rw [twoShellSource, bilateralLaplace_schwartz_add ((hasEntireLaplace_evenPacket _).schwartz_smul _)
    ((hasEntireLaplace_evenPacket _).schwartz_smul _), bilateralLaplace_schwartz_smul,
    bilateralLaplace_schwartz_smul, bilateralLaplace_evenPacket_eq_cosh,
    bilateralLaplace_evenPacket_eq_cosh, positiveEvenTwoShellLaplace]
  push_cast
  ring_nf

/-- `(EA.8)`, `(EA.10)`  **Explicit off-axis zero quartet.**  For `τ ≠ 0` the strictly positive
even two-shell Schwartz source vanishes under the bilateral Laplace transform at `a + iτ`, and
hence on the whole quartet `±(a ± iτ)`. -/
theorem bilateralLaplace_twoShellSource_eq_zero (a : ℝ) {τ : ℝ} (hτ : τ ≠ 0) :
    bilateralLaplace (twoShellSource a τ) ((a : ℂ) + (τ : ℂ) * I) = 0 := by
  have key : ∀ b t : ℝ, 0 < t →
      bilateralLaplace (twoShellSource b t) ((b : ℂ) + (t : ℂ) * I) = 0 := by
    intro b t ht
    rw [bilateralLaplace_twoShellSource, abs_of_pos ht]
    have harg : ((b : ℂ) + (t : ℂ) * I) * ((Real.pi / t : ℝ) : ℂ) =
        ((b * (Real.pi / t) : ℝ) : ℂ) + (Real.pi : ℂ) * I := by
      have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
      push_cast
      field_simp
    rw [harg, positiveEvenTwoShellLaplace_offAxis_zero, mul_zero]
  rw [bilateralLaplace_eq_zero_iff_abs (twoShellSource_neg a τ)]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
    Complex.mul_im, zero_add]
  rw [← twoShellSource_abs a τ, show twoShellSource |a| τ = twoShellSource |a| |τ| by
    unfold twoShellSource; rw [abs_abs]]
  exact key |a| |τ| (abs_pos.mpr hτ)

/-- The explicit source vanishes on the full functional-equation quartet. -/
theorem twoShellSource_quartet (a : ℝ) {τ : ℝ} (hτ : τ ≠ 0) :
    let z : ℂ := (a : ℂ) + (τ : ℂ) * I
    bilateralLaplace (twoShellSource a τ) z = 0 ∧
      bilateralLaplace (twoShellSource a τ) (-z) = 0 ∧
      bilateralLaplace (twoShellSource a τ) (starRingEnd ℂ z) = 0 ∧
      bilateralLaplace (twoShellSource a τ) (-starRingEnd ℂ z) = 0 :=
  bilateralLaplace_quartet (twoShellSource_neg a τ)
    (bilateralLaplace_twoShellSource_eq_zero a hτ)

end GaloisForLFunctions.HTGeometry.PositiveEvenLaplaceEscape
