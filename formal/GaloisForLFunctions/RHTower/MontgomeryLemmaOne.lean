import GaloisForLFunctions.RHTower.MontgomeryKernelPerron
import GaloisForLFunctions.RHTower.ZetaLogDerivZeroDistance

/-!
# Montgomery's lemma as an exact identity

With `a = 3/2 + it`, `b = −1/2 + it` and the Montgomery kernel `K_t(s) = x^{s}(−2)/((s−a)(s−b))`
on `Re s = 2`, the Perron integral `(1/2π)∫ (−ζ'/ζ) K_t` is evaluated twice: on the Dirichlet side
(`MontgomeryKernelPerron`) and on the Mittag-Leffler side, where `−ζ'/ζ` is the pole at `1`, a
constant, the digamma series of `Γ_ℝ'/Γ_ℝ`, and the paired partial fraction over the zeros of `ξ`.
Every term is a rational function against the kernel and is integrated by the two- and three-pole
Perron windows; the interchange of sum and integral is dominated by `(1+(τ−t)²)^{−3/4}`-type
majorants centred at the height `t`.  The kernel-pole residues re-sum, through the paired partial
fraction of `ξ'/ξ` at `a` and at `b` (both are non-zeros of `ξ`, the latter by the functional
equation), to `x^{a} ξ'/ξ(a)` and `x^{b} ξ'/ξ(b)`.  The result is

`Σ_ρ 2x^{ρ}/((ρ−a)(ρ−b)) = −Σ_{n≤x} Λ(n)((x/n)^a − (x/n)^b) + ((x−x^a)/(1−a) − (x−x^b)/(1−b))
  + c₁(x^a − x^b) − 2 Σ_{k≥0} x^{−2(k+1)}/((2(k+1)+a)(2(k+1)+b))
  + ½ x^a S(a) − ½ x^b S(b) − x^a ξ'/ξ(a) + x^b ξ'/ξ(b)`,

`S(s) = Σ_{k≥0} (1/(k+2) − 2/(s+2(k+1)))`, `c₁ = ½ − ½ log π − ½ γ`, absolutely convergent on the
zero side (`2x^{ρ}/((ρ−a)(ρ−b)) = −2x^{ρ}/(1 − (ρ − s₀)²)`, `s₀ = ½ + it`).
-/

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-! ## Pole arithmetic -/

theorem montgomeryPoleUp_ne_one (t : ℝ) : montgomeryPoleUp t ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [montgomeryPoleUp_re] at this
  norm_num at this

theorem montgomeryPoleDown_ne_one (t : ℝ) : montgomeryPoleDown t ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [montgomeryPoleDown_re] at this
  norm_num at this

theorem xiZeroCopy_ne_montgomeryPoleUp (q : XiZeroCopy) (t : ℝ) :
    (q.1 : ℂ) ≠ montgomeryPoleUp t := by
  intro h
  have := congrArg Complex.re h
  rw [montgomeryPoleUp_re] at this
  have := xiZeroCopy_re_lt_one q
  linarith

theorem xiZeroCopy_ne_montgomeryPoleDown (q : XiZeroCopy) (t : ℝ) :
    (q.1 : ℂ) ≠ montgomeryPoleDown t := by
  intro h
  have := congrArg Complex.re h
  rw [montgomeryPoleDown_re] at this
  have := xiZeroCopy_re_pos q
  linarith

/-- The trivial-zero pole `c_k = −2(k+1)`. -/
def trivialPole (k : ℕ) : ℂ := -(2 * ((k : ℂ) + 1))

theorem trivialPole_re (k : ℕ) : (trivialPole k).re = -(2 * ((k : ℝ) + 1)) := by
  simp [trivialPole]

theorem trivialPole_re_lt (k : ℕ) : (trivialPole k).re < 2 := by
  rw [trivialPole_re]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith

theorem trivialPole_ne_montgomeryPoleUp (k : ℕ) (t : ℝ) : trivialPole k ≠ montgomeryPoleUp t := by
  intro h
  have := congrArg Complex.re h
  rw [trivialPole_re, montgomeryPoleUp_re] at this
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem trivialPole_ne_montgomeryPoleDown (k : ℕ) (t : ℝ) :
    trivialPole k ≠ montgomeryPoleDown t := by
  intro h
  have := congrArg Complex.re h
  rw [trivialPole_re, montgomeryPoleDown_re] at this
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem lineTwo_sub_trivialPole (k : ℕ) (τ : ℝ) :
    lineTwo τ - trivialPole k = lineTwo τ + 2 * ((k : ℂ) + 1) := by
  unfold trivialPole; ring

theorem xi_montgomeryPoleUp_ne_zero (t : ℝ) : xi (montgomeryPoleUp t) ≠ 0 :=
  xi_ne_zero_of_one_le_re (by rw [montgomeryPoleUp_re]; norm_num)

theorem xi_montgomeryPoleDown_ne_zero (t : ℝ) : xi (montgomeryPoleDown t) ≠ 0 := by
  rw [← xi_one_sub]
  apply xi_ne_zero_of_one_le_re
  simp only [Complex.sub_re, Complex.one_re, montgomeryPoleDown_re]
  norm_num

/-! ## The kernel bound, centred at the height `t` -/

theorem lineTwo_sub_montgomeryPoleUp_eq (t τ : ℝ) :
    lineTwo τ - montgomeryPoleUp t = ((1 / 2 : ℝ) : ℂ) + ((τ - t : ℝ) : ℂ) * I := by
  apply Complex.ext <;> norm_num [lineTwo, montgomeryPoleUp]

theorem lineTwo_sub_montgomeryPoleDown_eq (t τ : ℝ) :
    lineTwo τ - montgomeryPoleDown t = ((5 / 2 : ℝ) : ℂ) + ((τ - t : ℝ) : ℂ) * I := by
  apply Complex.ext <;> norm_num [lineTwo, montgomeryPoleDown]

/-- `‖K_t(2+iτ)‖ ≤ 8x²/(1+(τ−t)²)`. -/
theorem norm_montgomeryLineKernel_le {x : ℝ} (hx : 0 < x) (t τ : ℝ) :
    ‖montgomeryLineKernel x t τ‖ ≤ 8 * x ^ 2 / (1 + (τ - t) ^ 2) := by
  unfold montgomeryLineKernel
  rw [norm_mul, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, lineTwo_re,
    lineTwo_sub_montgomeryPoleUp_eq, lineTwo_sub_montgomeryPoleDown_eq, Complex.norm_add_mul_I,
    Complex.norm_add_mul_I, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hu : (0 : ℝ) ≤ (τ - t) ^ 2 := sq_nonneg _
  have h1 : Real.sqrt ((1 / 2 : ℝ) ^ 2 + (τ - t) ^ 2) * Real.sqrt ((5 / 2 : ℝ) ^ 2 + (τ - t) ^ 2)
      ≥ (1 + (τ - t) ^ 2) / 4 := by
    have hA : Real.sqrt ((1 / 2 : ℝ) ^ 2 + (τ - t) ^ 2) ≥ Real.sqrt ((1 + (τ - t) ^ 2) / 4) := by
      apply Real.sqrt_le_sqrt; nlinarith
    have hB : Real.sqrt ((5 / 2 : ℝ) ^ 2 + (τ - t) ^ 2) ≥ Real.sqrt ((1 + (τ - t) ^ 2) / 4) := by
      apply Real.sqrt_le_sqrt; nlinarith
    have hC : Real.sqrt ((1 + (τ - t) ^ 2) / 4) * Real.sqrt ((1 + (τ - t) ^ 2) / 4)
        = (1 + (τ - t) ^ 2) / 4 := Real.mul_self_sqrt (by positivity)
    calc Real.sqrt ((1 / 2 : ℝ) ^ 2 + (τ - t) ^ 2) * Real.sqrt ((5 / 2 : ℝ) ^ 2 + (τ - t) ^ 2)
        ≥ Real.sqrt ((1 + (τ - t) ^ 2) / 4) * Real.sqrt ((1 + (τ - t) ^ 2) / 4) := by
          gcongr
      _ = (1 + (τ - t) ^ 2) / 4 := hC
  have hpos : 0 < (1 + (τ - t) ^ 2) / 4 := by positivity
  have hnorm2 : ‖(-2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm2]
  calc 2 * (x ^ 2 / (Real.sqrt ((1 / 2 : ℝ) ^ 2 + (τ - t) ^ 2) *
        Real.sqrt ((5 / 2 : ℝ) ^ 2 + (τ - t) ^ 2)))
      ≤ 2 * (x ^ 2 / ((1 + (τ - t) ^ 2) / 4)) := by gcongr
    _ = 8 * x ^ 2 / (1 + (τ - t) ^ 2) := by rw [div_div_eq_mul_div]; ring

/-! ## The two Mittag-Leffler families against the kernel -/

/-- The `k`-th digamma term times the Montgomery kernel. -/
def mkTerm (x t : ℝ) (k : ℕ) (τ : ℝ) : ℂ :=
  (1 / ((k : ℂ) + 2) - 2 / (lineTwo τ + 2 * ((k : ℂ) + 1))) * montgomeryLineKernel x t τ

/-- The zero term times the Montgomery kernel. -/
def mzTerm (x t : ℝ) (q : XiZeroCopy) (τ : ℝ) : ℂ :=
  (((q.1 : ℂ) - 1 / 2)⁻¹ + (lineTwo τ - (q.1 : ℂ))⁻¹) * montgomeryLineKernel x t τ

theorem continuous_montgomeryLineKernel {x : ℝ} (hx : 0 < x) (t : ℝ) :
    Continuous (montgomeryLineKernel x t) := by
  unfold montgomeryLineKernel
  have hsa : ∀ τ : ℝ, lineTwo τ - montgomeryPoleUp t ≠ 0 :=
    lineTwo_sub_ne_zero (montgomeryPoleUp_re_lt t)
  have hsb : ∀ τ : ℝ, lineTwo τ - montgomeryPoleDown t ≠ 0 :=
    lineTwo_sub_ne_zero (montgomeryPoleDown_re_lt t)
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  apply Continuous.mul continuous_const
  apply Continuous.div
  · exact continuous_const.cpow (by unfold lineTwo; fun_prop) (fun τ => Or.inl (by rw [Complex.ofReal_re]; exact hx))
  · exact ((by unfold lineTwo; fun_prop : Continuous fun τ : ℝ => lineTwo τ - montgomeryPoleUp t).mul
      (by unfold lineTwo; fun_prop))
  · intro τ
    exact mul_ne_zero (hsa τ) (hsb τ)

/-- The kernel divided by a further pole left of the line is integrable. -/
theorem integrable_montgomeryLineKernel_div {x : ℝ} (hx : 0 < x) (t : ℝ) {c : ℂ} (hc : c.re < 2) :
    Integrable (fun τ : ℝ => montgomeryLineKernel x t τ / (lineTwo τ - c)) := by
  have hA : Integrable (fun τ : ℝ => (x : ℂ) ^ lineTwo τ /
      ((lineTwo τ - c) * (lineTwo τ - montgomeryPoleUp t))) :=
    integrable_cpow_div_twoPole (σ := 2) hc (montgomeryPoleUp_re_lt t) hx
  have hB : Integrable (fun τ : ℝ => (x : ℂ) ^ lineTwo τ /
      ((lineTwo τ - c) * (lineTwo τ - montgomeryPoleDown t))) :=
    integrable_cpow_div_twoPole (σ := 2) hc (montgomeryPoleDown_re_lt t) hx
  refine (hA.sub hB).neg.congr (Filter.Eventually.of_forall fun τ => ?_)
  simp only [Pi.neg_apply, Pi.sub_apply]
  unfold montgomeryLineKernel
  have h1 := lineTwo_sub_ne_zero (montgomeryPoleUp_re_lt t) τ
  have h3 := lineTwo_sub_ne_zero hc τ
  have hab := montgomeryPoleUp_sub_down t
  have hab' : lineTwo τ - montgomeryPoleDown t = lineTwo τ - montgomeryPoleUp t + 2 := by
    rw [← hab]; ring
  have h2 : lineTwo τ - montgomeryPoleUp t + 2 ≠ 0 := by
    rw [← hab']; exact lineTwo_sub_ne_zero (montgomeryPoleDown_re_lt t) τ
  rw [hab']
  field_simp
  ring

theorem continuous_mkTerm {x : ℝ} (hx : 0 < x) (t : ℝ) (k : ℕ) : Continuous (mkTerm x t k) := by
  unfold mkTerm
  refine Continuous.mul ?_ (continuous_montgomeryLineKernel hx t)
  refine continuous_const.sub (continuous_const.div ?_ (lineTwo_add_ne_zero k))
  unfold lineTwo; fun_prop

theorem continuous_mzTerm {x : ℝ} (hx : 0 < x) (t : ℝ) (q : XiZeroCopy) :
    Continuous (mzTerm x t q) := by
  unfold mzTerm
  refine Continuous.mul ?_ (continuous_montgomeryLineKernel hx t)
  refine continuous_const.add (Continuous.inv₀ ?_ (lineTwo_sub_ne_zero (by
    have := xiZeroCopy_re_lt_one q; linarith)))
  unfold lineTwo; fun_prop

/-- Square roots are subadditive, in the form needed for the centred majorant. -/
theorem sqrt_abs_le_sqrt_abs_add (t τ : ℝ) :
    Real.sqrt |τ| ≤ Real.sqrt |τ - t| + Real.sqrt |t| := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 : |τ| ≤ |τ - t| + |t| := by
    calc |τ| = |(τ - t) + t| := by ring_nf
      _ ≤ |τ - t| + |t| := abs_add_le _ _
  nlinarith [Real.sq_sqrt (abs_nonneg (τ - t)), Real.sq_sqrt (abs_nonneg t),
    Real.sqrt_nonneg |τ - t|, Real.sqrt_nonneg |t|]

/-- The digamma-term majorant, centred at `t`. -/
def mkMajorant (t : ℝ) (τ : ℝ) : ℝ :=
  (1 + (τ - t) ^ 2) ^ (-(3 / 4 : ℝ)) + Real.sqrt |t| * (1 + (τ - t) ^ 2)⁻¹

theorem integrable_mkMajorant (t : ℝ) : Integrable (mkMajorant t) := by
  unfold mkMajorant
  refine (integrable_one_add_sq_rpow_neg_three_quarters.comp_sub_right t).add ?_
  exact (integrable_inv_one_add_sq.comp_sub_right t).const_mul _

theorem mkMajorant_nonneg (t τ : ℝ) : 0 ≤ mkMajorant t τ := by
  unfold mkMajorant; positivity

/-- The total mass of the centred digamma majorant. -/
def mkMajorantMass (t : ℝ) : ℝ := ∫ τ : ℝ, mkMajorant t τ

theorem norm_mkTerm_le {x : ℝ} (hx : 0 < x) (t : ℝ) (k : ℕ) (τ : ℝ) :
    ‖mkTerm x t k τ‖ ≤ (4 * x ^ 2 / (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) * mkMajorant t τ := by
  unfold mkTerm
  rw [norm_mul]
  have h1 := norm_kFactor_le k τ
  have h2 := norm_montgomeryLineKernel_le hx t τ
  have hk : 0 < ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2) := by positivity
  have hsq := sqrt_abs_le_sqrt_abs_add t τ
  have hq : Real.sqrt |τ - t| ≤ (1 + (τ - t) ^ 2) ^ (1 / 4 : ℝ) := sqrt_abs_le_rpow_quarter (τ - t)
  have hden : 0 < 1 + (τ - t) ^ 2 := by positivity
  have hrpow : (1 + (τ - t) ^ 2) ^ (1 / 4 : ℝ) / (1 + (τ - t) ^ 2)
      = (1 + (τ - t) ^ 2) ^ (-(3 / 4 : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hden]; norm_num
  calc ‖1 / ((k : ℂ) + 2) - 2 / (lineTwo τ + 2 * ((k : ℂ) + 1))‖ * ‖montgomeryLineKernel x t τ‖
      ≤ (Real.sqrt |τ| / (2 * ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) *
          (8 * x ^ 2 / (1 + (τ - t) ^ 2)) := by gcongr
    _ ≤ (((1 + (τ - t) ^ 2) ^ (1 / 4 : ℝ) + Real.sqrt |t|) /
          (2 * ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) * (8 * x ^ 2 / (1 + (τ - t) ^ 2)) := by
        gcongr
        linarith
    _ = (4 * x ^ 2 / (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) *
          ((1 + (τ - t) ^ 2) ^ (1 / 4 : ℝ) / (1 + (τ - t) ^ 2) +
            Real.sqrt |t| * (1 + (τ - t) ^ 2)⁻¹) := by
        field_simp
        ring
    _ = _ := by rw [hrpow]; rfl

theorem integrable_mkTerm {x : ℝ} (hx : 0 < x) (t : ℝ) (k : ℕ) : Integrable (mkTerm x t k) :=
  ((integrable_mkMajorant t).const_mul _).mono' (continuous_mkTerm hx t k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ => norm_mkTerm_le hx t k τ)

theorem integral_norm_mkTerm_le {x : ℝ} (hx : 0 < x) (t : ℝ) (k : ℕ) :
    ∫ τ : ℝ, ‖mkTerm x t k τ‖ ≤
      (4 * x ^ 2 / (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) * mkMajorantMass t := by
  unfold mkMajorantMass
  rw [← integral_const_mul]
  exact integral_mono (integrable_mkTerm hx t k).norm ((integrable_mkMajorant t).const_mul _)
    (norm_mkTerm_le hx t k)

theorem summable_integral_norm_mkTerm {x : ℝ} (hx : 0 < x) (t : ℝ) :
    Summable (fun k : ℕ => ∫ τ : ℝ, ‖mkTerm x t k τ‖) := by
  have hb : Summable (fun k : ℕ =>
      (4 * x ^ 2 * (1 / (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2)))) * mkMajorantMass t) :=
    (summable_inv_mul_sqrt_shift.mul_left (4 * x ^ 2)).mul_right _
  refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun τ => norm_nonneg _)
    (fun k => (integral_norm_mkTerm_le hx t k).trans (le_of_eq ?_)) hb
  ring

/-- Zero terms, centred majorant: `‖mzTerm‖ ≤ C_t x² ‖ρ−½‖⁻¹ (1+|γ−t|)^{−1/2} ((1+(τ−t)²)^{−3/4} + (1+(τ−γ)²)^{−3/4})`. -/
theorem norm_mzTerm_le_majorant {x : ℝ} (hx : 0 < x) (t : ℝ) (q : XiZeroCopy) (τ : ℝ) :
    ‖mzTerm x t q τ‖ ≤ (64 * Real.sqrt 2 * x ^ 2 * (1 + |t|) /
        (‖(q.1 : ℂ) - 1 / 2‖ * (1 + |((q.1 : ℂ)).im - t|) ^ (1 / 2 : ℝ))) *
      ((1 + (τ - t) ^ 2) ^ (-(3 / 4 : ℝ)) + (1 + (τ - ((q.1 : ℂ)).im) ^ 2) ^ (-(3 / 4 : ℝ))) := by
  unfold mzTerm
  rw [norm_mul]
  have h1 := norm_zFactor_le q τ
  have h2 := norm_montgomeryLineKernel_le hx t τ
  have hqn : 0 < ‖(q.1 : ℂ) - 1 / 2‖ := norm_pos_iff.mpr (xiZeroCopy_sub_half_ne_zero q)
  set γ : ℝ := ((q.1 : ℂ)).im with hγ
  -- `(1+|τ|) ≤ (1+|t|)(1+|τ−t|)` and `(1+|τ−t|)/(1+(τ−t)²) ≤ 2/(1+|τ−t|)`
  have hA : 1 + |τ| ≤ (1 + |t|) * (1 + |τ - t|) := by
    have : |τ| ≤ |τ - t| + |t| := by
      calc |τ| = |(τ - t) + t| := by ring_nf
        _ ≤ |τ - t| + |t| := abs_add_le _ _
    nlinarith [abs_nonneg t, abs_nonneg (τ - t)]
  have hB : (1 + |τ - t|) / (1 + (τ - t) ^ 2) ≤ 2 / (1 + |τ - t|) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_abs (τ - t), abs_nonneg (τ - t), sq_nonneg (1 - |τ - t|)]
  have hC := two_centre_majorant (γ - t) (τ - t)
  rw [show τ - t - (γ - t) = τ - γ by ring] at hC
  have hstep : ‖((q.1 : ℂ) - 1 / 2)⁻¹ + (lineTwo τ - (q.1 : ℂ))⁻¹‖ * ‖montgomeryLineKernel x t τ‖
      ≤ (4 * (1 + |τ|) / (‖(q.1 : ℂ) - 1 / 2‖ * (1 + |τ - γ|))) * (8 * x ^ 2 / (1 + (τ - t) ^ 2)) := by
    gcongr
  refine hstep.trans ?_
  have hD : (4 * (1 + |τ|) / (‖(q.1 : ℂ) - 1 / 2‖ * (1 + |τ - γ|))) * (8 * x ^ 2 / (1 + (τ - t) ^ 2))
      ≤ (32 * x ^ 2 * (1 + |t|) / ‖(q.1 : ℂ) - 1 / 2‖) *
          ((1 + |τ - t|) / (1 + (τ - t) ^ 2) * (1 / (1 + |τ - γ|))) := by
    have : (4 * (1 + |τ|) / (‖(q.1 : ℂ) - 1 / 2‖ * (1 + |τ - γ|))) * (8 * x ^ 2 / (1 + (τ - t) ^ 2))
        = (32 * x ^ 2 / ‖(q.1 : ℂ) - 1 / 2‖) *
          ((1 + |τ|) / (1 + (τ - t) ^ 2) * (1 / (1 + |τ - γ|))) := by
      field_simp
      ring
    rw [this]
    have hE : (1 + |τ|) / (1 + (τ - t) ^ 2) ≤ (1 + |t|) * ((1 + |τ - t|) / (1 + (τ - t) ^ 2)) := by
      rw [← mul_div_assoc]
      gcongr
    calc (32 * x ^ 2 / ‖(q.1 : ℂ) - 1 / 2‖) * ((1 + |τ|) / (1 + (τ - t) ^ 2) * (1 / (1 + |τ - γ|)))
        ≤ (32 * x ^ 2 / ‖(q.1 : ℂ) - 1 / 2‖) *
            ((1 + |t|) * ((1 + |τ - t|) / (1 + (τ - t) ^ 2)) * (1 / (1 + |τ - γ|))) := by
          gcongr
      _ = _ := by ring
  refine hD.trans ?_
  have hF : (1 + |τ - t|) / (1 + (τ - t) ^ 2) * (1 / (1 + |τ - γ|))
      ≤ 2 * (1 / ((1 + |τ - γ|) * (1 + |τ - t|))) := by
    calc (1 + |τ - t|) / (1 + (τ - t) ^ 2) * (1 / (1 + |τ - γ|))
        ≤ 2 / (1 + |τ - t|) * (1 / (1 + |τ - γ|)) := by gcongr
      _ = 2 * (1 / ((1 + |τ - γ|) * (1 + |τ - t|))) := by
          field_simp
  calc (32 * x ^ 2 * (1 + |t|) / ‖(q.1 : ℂ) - 1 / 2‖) *
        ((1 + |τ - t|) / (1 + (τ - t) ^ 2) * (1 / (1 + |τ - γ|)))
      ≤ (32 * x ^ 2 * (1 + |t|) / ‖(q.1 : ℂ) - 1 / 2‖) *
        (2 * (Real.sqrt 2 * (1 + |γ - t|) ^ (-(1 / 2 : ℝ)) *
          ((1 + (τ - t) ^ 2) ^ (-(3 / 4 : ℝ)) + (1 + (τ - γ) ^ 2) ^ (-(3 / 4 : ℝ))))) :=
        mul_le_mul_of_nonneg_left (hF.trans (mul_le_mul_of_nonneg_left hC (by norm_num)))
          (by positivity)
    _ = _ := by
        rw [Real.rpow_neg (by positivity)]
        field_simp
        ring

theorem integrable_mzTerm {x : ℝ} (hx : 0 < x) (t : ℝ) (q : XiZeroCopy) :
    Integrable (mzTerm x t q) :=
  (((integrable_one_add_sq_rpow_neg_three_quarters.comp_sub_right t).add
    (integrable_one_add_sq_rpow_neg_three_quarters.comp_sub_right ((q.1 : ℂ)).im)).const_mul _).mono'
    (continuous_mzTerm hx t q).aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ => norm_mzTerm_le_majorant hx t q τ)

theorem integral_norm_mzTerm_le {x : ℝ} (hx : 0 < x) (t : ℝ) (q : XiZeroCopy) :
    ∫ τ : ℝ, ‖mzTerm x t q τ‖ ≤
      (128 * Real.sqrt 2 * x ^ 2 * (1 + |t|) * majorantMass) *
        (1 / (‖(q.1 : ℂ) - 1 / 2‖ * (1 + |((q.1 : ℂ)).im - t|) ^ (1 / 2 : ℝ))) := by
  have hint : Integrable (fun τ : ℝ => (1 + (τ - t) ^ 2) ^ (-(3 / 4 : ℝ)) +
      (1 + (τ - ((q.1 : ℂ)).im) ^ 2) ^ (-(3 / 4 : ℝ))) :=
    (integrable_one_add_sq_rpow_neg_three_quarters.comp_sub_right t).add
      (integrable_one_add_sq_rpow_neg_three_quarters.comp_sub_right _)
  have hmass : ∫ τ : ℝ, ((1 + (τ - t) ^ 2) ^ (-(3 / 4 : ℝ)) +
      (1 + (τ - ((q.1 : ℂ)).im) ^ 2) ^ (-(3 / 4 : ℝ))) = 2 * majorantMass := by
    rw [integral_add (integrable_one_add_sq_rpow_neg_three_quarters.comp_sub_right t)
      (integrable_one_add_sq_rpow_neg_three_quarters.comp_sub_right _),
      integral_sub_right_eq_self (fun τ : ℝ => (1 + τ ^ 2) ^ (-(3 / 4 : ℝ))) t,
      integral_sub_right_eq_self (fun τ : ℝ => (1 + τ ^ 2) ^ (-(3 / 4 : ℝ))) _]
    unfold majorantMass
    ring
  calc ∫ τ : ℝ, ‖mzTerm x t q τ‖
      ≤ ∫ τ : ℝ, (64 * Real.sqrt 2 * x ^ 2 * (1 + |t|) /
          (‖(q.1 : ℂ) - 1 / 2‖ * (1 + |((q.1 : ℂ)).im - t|) ^ (1 / 2 : ℝ))) *
          ((1 + (τ - t) ^ 2) ^ (-(3 / 4 : ℝ)) + (1 + (τ - ((q.1 : ℂ)).im) ^ 2) ^ (-(3 / 4 : ℝ))) :=
        integral_mono (integrable_mzTerm hx t q).norm (hint.const_mul _)
          (norm_mzTerm_le_majorant hx t q)
    _ = _ := by
        rw [integral_const_mul, hmass]
        field_simp
        ring

/-- `(1+|γ−t|)^{−1/2} ≤ (1+|t|)^{1/2} ‖ρ−½‖^{−1/2}`. -/
theorem inv_sqrt_shift_le (t : ℝ) (q : XiZeroCopy) :
    1 / (‖(q.1 : ℂ) - 1 / 2‖ * (1 + |((q.1 : ℂ)).im - t|) ^ (1 / 2 : ℝ))
      ≤ Real.sqrt (1 + |t|) * (1 / (‖(q.1 : ℂ) - 1 / 2‖ * Real.sqrt ‖(q.1 : ℂ) - 1 / 2‖)) := by
  have hqn : 0 < ‖(q.1 : ℂ) - 1 / 2‖ := norm_pos_iff.mpr (xiZeroCopy_sub_half_ne_zero q)
  set γ : ℝ := ((q.1 : ℂ)).im with hγ
  -- `‖ρ−½‖ ≤ (1+|t|)(1+|γ−t|)`
  have him : |γ| ≤ ‖(q.1 : ℂ) - 1 / 2‖ := by
    have : ((q.1 : ℂ) - 1 / 2).im = γ := by simp [hγ]
    rw [← this]; exact Complex.abs_im_le_norm _
  have hre : |((q.1 : ℂ) - 1 / 2).re| ≤ 1 / 2 := by
    have h0 := xiZeroCopy_re_pos q
    have h1 := xiZeroCopy_re_lt_one q
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re, Complex.one_im]
    rw [abs_le]; constructor <;> norm_num <;> linarith
  have hn1 : ‖(q.1 : ℂ) - 1 / 2‖ ≤ 1 + |γ| := by
    have hbound := Complex.norm_le_abs_re_add_abs_im ((q.1 : ℂ) - 1 / 2)
    have : ((q.1 : ℂ) - 1 / 2).im = γ := by simp [hγ]
    rw [this] at hbound
    linarith
  have hn2 : 1 + |γ| ≤ (1 + |t|) * (1 + |γ - t|) := by
    have : |γ| ≤ |γ - t| + |t| := by
      calc |γ| = |(γ - t) + t| := by ring_nf
        _ ≤ |γ - t| + |t| := abs_add_le _ _
    nlinarith [abs_nonneg t, abs_nonneg (γ - t)]
  have hkey : ‖(q.1 : ℂ) - 1 / 2‖ ≤ (1 + |t|) * (1 + |γ - t|) := hn1.trans hn2
  have hsq : Real.sqrt ‖(q.1 : ℂ) - 1 / 2‖ ≤ Real.sqrt (1 + |t|) * (1 + |γ - t|) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) hkey (by norm_num)
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  calc ‖(q.1 : ℂ) - 1 / 2‖ * Real.sqrt ‖(q.1 : ℂ) - 1 / 2‖
      ≤ ‖(q.1 : ℂ) - 1 / 2‖ * (Real.sqrt (1 + |t|) * (1 + |γ - t|) ^ (1 / 2 : ℝ)) := by
        gcongr
    _ = Real.sqrt (1 + |t|) * (‖(q.1 : ℂ) - 1 / 2‖ * (1 + |γ - t|) ^ (1 / 2 : ℝ)) := by ring

theorem summable_integral_norm_mzTerm {x : ℝ} (hx : 0 < x) (t : ℝ) :
    Summable (fun q : XiZeroCopy => ∫ τ : ℝ, ‖mzTerm x t q τ‖) := by
  have hnorm : ∀ q : XiZeroCopy, ‖xiSpectralPoint q‖ = ‖(q.1 : ℂ) - 1 / 2‖ := by
    intro q
    rw [xiSpectralPoint, norm_mul, norm_neg, Complex.norm_I, mul_one]
  have hb : Summable (fun q : XiZeroCopy =>
      (128 * Real.sqrt 2 * x ^ 2 * (1 + |t|) * majorantMass * Real.sqrt (1 + |t|)) *
        (1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖))) :=
    xiSpectralPoint_inv_three_halves_summable.mul_left _
  refine Summable.of_nonneg_of_le (fun q => integral_nonneg fun τ => norm_nonneg _)
    (fun q => (integral_norm_mzTerm_le hx t q).trans ?_) hb
  rw [hnorm]
  have hC : 0 ≤ 128 * Real.sqrt 2 * x ^ 2 * (1 + |t|) * majorantMass := by
    have : 0 ≤ majorantMass := integral_nonneg fun τ => by positivity
    positivity
  calc (128 * Real.sqrt 2 * x ^ 2 * (1 + |t|) * majorantMass) *
        (1 / (‖(q.1 : ℂ) - 1 / 2‖ * (1 + |((q.1 : ℂ)).im - t|) ^ (1 / 2 : ℝ)))
      ≤ (128 * Real.sqrt 2 * x ^ 2 * (1 + |t|) * majorantMass) *
        (Real.sqrt (1 + |t|) * (1 / (‖(q.1 : ℂ) - 1 / 2‖ * Real.sqrt ‖(q.1 : ℂ) - 1 / 2‖))) :=
        mul_le_mul_of_nonneg_left (inv_sqrt_shift_le t q) hC
    _ = _ := by ring

/-! ## Termwise integrals -/

theorem integral_mkTerm {x : ℝ} (hx : 1 < x) (t : ℝ) (k : ℕ) :
    (1 / (2 * Real.pi) : ℝ) • ∫ τ : ℝ, mkTerm x t k τ =
      (1 / ((k : ℂ) + 2)) * (-((x : ℂ) ^ montgomeryPoleUp t - (x : ℂ) ^ montgomeryPoleDown t)) -
        2 * (-(((x : ℂ) ^ trivialPole k - (x : ℂ) ^ montgomeryPoleUp t) /
            (trivialPole k - montgomeryPoleUp t) -
          ((x : ℂ) ^ trivialPole k - (x : ℂ) ^ montgomeryPoleDown t) /
            (trivialPole k - montgomeryPoleDown t))) := by
  have hx0 : 0 < x := by linarith
  have hsplit : ∀ τ : ℝ, mkTerm x t k τ = (1 / ((k : ℂ) + 2)) * montgomeryLineKernel x t τ -
      2 * (montgomeryLineKernel x t τ / (lineTwo τ - trivialPole k)) := by
    intro τ
    unfold mkTerm
    rw [lineTwo_sub_trivialPole]
    have h := lineTwo_add_ne_zero k τ
    field_simp
  simp_rw [hsplit]
  have hI1 := (integrable_montgomeryLineKernel hx0 t).const_mul (1 / ((k : ℂ) + 2))
  have hI2 : Integrable (fun τ : ℝ => montgomeryLineKernel x t τ / (lineTwo τ - trivialPole k)) :=
    integrable_montgomeryLineKernel_div hx0 t (trivialPole_re_lt k)
  rw [integral_sub hI1 (hI2.const_mul 2), integral_const_mul, integral_const_mul, smul_sub,
    ← mul_smul_comm, ← mul_smul_comm, perron_montgomery_basic hx t,
    perron_montgomery_threePole hx t (trivialPole_re_lt k) (trivialPole_ne_montgomeryPoleUp k t)
      (trivialPole_ne_montgomeryPoleDown k t)]

theorem integral_mzTerm {x : ℝ} (hx : 1 < x) (t : ℝ) (q : XiZeroCopy) :
    (1 / (2 * Real.pi) : ℝ) • ∫ τ : ℝ, mzTerm x t q τ =
      ((q.1 : ℂ) - 1 / 2)⁻¹ * (-((x : ℂ) ^ montgomeryPoleUp t - (x : ℂ) ^ montgomeryPoleDown t)) +
        (-(((x : ℂ) ^ (q.1 : ℂ) - (x : ℂ) ^ montgomeryPoleUp t) / ((q.1 : ℂ) - montgomeryPoleUp t) -
          ((x : ℂ) ^ (q.1 : ℂ) - (x : ℂ) ^ montgomeryPoleDown t) /
            ((q.1 : ℂ) - montgomeryPoleDown t))) := by
  have hx0 : 0 < x := by linarith
  have hre : ((q.1 : ℂ)).re < 2 := by have := xiZeroCopy_re_lt_one q; linarith
  have hsplit : ∀ τ : ℝ, mzTerm x t q τ = ((q.1 : ℂ) - 1 / 2)⁻¹ * montgomeryLineKernel x t τ +
      montgomeryLineKernel x t τ / (lineTwo τ - (q.1 : ℂ)) := by
    intro τ
    unfold mzTerm
    have h := lineTwo_sub_ne_zero hre τ
    field_simp
  simp_rw [hsplit]
  have hI1 := (integrable_montgomeryLineKernel hx0 t).const_mul (((q.1 : ℂ) - 1 / 2)⁻¹)
  have hI2 : Integrable (fun τ : ℝ => montgomeryLineKernel x t τ / (lineTwo τ - (q.1 : ℂ))) :=
    integrable_montgomeryLineKernel_div hx0 t hre
  rw [integral_add hI1 hI2, integral_const_mul, smul_add, ← mul_smul_comm,
    perron_montgomery_basic hx t,
    perron_montgomery_threePole hx t hre (xiZeroCopy_ne_montgomeryPoleUp q t)
      (xiZeroCopy_ne_montgomeryPoleDown q t)]

/-! ## The Mittag-Leffler side -/

/-- **The Mittag-Leffler side** of the Montgomery Perron integral. -/
theorem montgomery_mittagLeffler_side {x : ℝ} (hx : 1 < x) (t : ℝ) :
    (1 / (2 * Real.pi) : ℝ) • ∫ τ : ℝ, LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) (lineTwo τ) *
        montgomeryLineKernel x t τ
      = (-(((x : ℂ) - (x : ℂ) ^ montgomeryPoleUp t) / (1 - montgomeryPoleUp t) -
            ((x : ℂ) - (x : ℂ) ^ montgomeryPoleDown t) / (1 - montgomeryPoleDown t))) +
        ((1 : ℂ) / 2 - (Real.log Real.pi : ℂ) / 2 - (Real.eulerMascheroniConstant : ℂ) / 2) *
          (-((x : ℂ) ^ montgomeryPoleUp t - (x : ℂ) ^ montgomeryPoleDown t)) +
        (1 / 2 : ℂ) * (∑' k : ℕ, (1 / (2 * Real.pi) : ℝ) • ∫ τ : ℝ, mkTerm x t k τ) -
        ∑' q : XiZeroCopy, (1 / (2 * Real.pi) : ℝ) • ∫ τ : ℝ, mzTerm x t q τ := by
  have hx0 : 0 < x := by linarith
  set c₁ : ℂ := (1 : ℂ) / 2 - (Real.log Real.pi : ℂ) / 2 - (Real.eulerMascheroniConstant : ℂ) / 2
    with hc₁
  have hpt : ∀ τ : ℝ, LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) (lineTwo τ) *
      montgomeryLineKernel x t τ =
      (montgomeryLineKernel x t τ / (lineTwo τ - 1) + c₁ * montgomeryLineKernel x t τ) +
        (1 / 2 : ℂ) * (∑' k : ℕ, mkTerm x t k τ) - ∑' q : XiZeroCopy, mzTerm x t q τ := by
    intro τ
    rw [lseries_vonMangoldt_lineTwo τ]
    unfold mkTerm mzTerm
    rw [tsum_mul_right, tsum_mul_right]
    have h1 := lineTwo_sub_one_ne_zero τ
    field_simp
    ring
  simp_rw [hpt]
  have hA1 : Integrable (fun τ : ℝ => montgomeryLineKernel x t τ / (lineTwo τ - 1)) :=
    integrable_montgomeryLineKernel_div hx0 t (by norm_num : (1 : ℂ).re < 2)
  have hA2 := (integrable_montgomeryLineKernel hx0 t).const_mul c₁
  have hTk : Integrable (fun τ : ℝ => ∑' k : ℕ, mkTerm x t k τ) :=
    integrable_tsum_of_summable_integral_norm' (fun k => (continuous_mkTerm hx0 t k).measurable)
      (integrable_mkTerm hx0 t) (summable_integral_norm_mkTerm hx0 t)
  have hTq : Integrable (fun τ : ℝ => ∑' q : XiZeroCopy, mzTerm x t q τ) :=
    integrable_tsum_of_summable_integral_norm' (fun q => (continuous_mzTerm hx0 t q).measurable)
      (integrable_mzTerm hx0 t) (summable_integral_norm_mzTerm hx0 t)
  have hS1 : Integrable (fun τ : ℝ => montgomeryLineKernel x t τ / (lineTwo τ - 1) +
      c₁ * montgomeryLineKernel x t τ) := hA1.add hA2
  have hS2 : Integrable (fun τ : ℝ => montgomeryLineKernel x t τ / (lineTwo τ - 1) +
      c₁ * montgomeryLineKernel x t τ + (1 / 2 : ℂ) * ∑' k : ℕ, mkTerm x t k τ) :=
    hS1.add (hTk.const_mul _)
  rw [integral_sub hS2 hTq, integral_add hS1 (hTk.const_mul _), integral_add hA1 hA2,
    integral_const_mul, integral_const_mul,
    ← integral_tsum_of_summable_integral_norm (integrable_mkTerm hx0 t)
      (summable_integral_norm_mkTerm hx0 t),
    ← integral_tsum_of_summable_integral_norm (integrable_mzTerm hx0 t)
      (summable_integral_norm_mzTerm hx0 t)]
  rw [smul_sub, smul_add, smul_add, ← mul_smul_comm, ← mul_smul_comm,
    perron_montgomery_threePole hx t (by norm_num : (1 : ℂ).re < 2)
      (montgomeryPoleUp_ne_one t).symm (montgomeryPoleDown_ne_one t).symm,
    perron_montgomery_basic hx t, smul_tsum_eq, smul_tsum_eq, Complex.cpow_one]


/-! ## Assembly -/

/-- The zero-side summand `2x^{ρ}/((ρ−a)(ρ−b))`. -/
def montgomeryZeroTerm (x t : ℝ) (q : XiZeroCopy) : ℂ :=
  2 * (x : ℂ) ^ (q.1 : ℂ) / (((q.1 : ℂ) - montgomeryPoleUp t) * ((q.1 : ℂ) - montgomeryPoleDown t))

/-- The trivial-zero summand `x^{c_k}/((c_k−a)(c_k−b))`, `c_k = −2(k+1)`. -/
def montgomeryTrivialTerm (x t : ℝ) (k : ℕ) : ℂ :=
  (x : ℂ) ^ trivialPole k /
    ((trivialPole k - montgomeryPoleUp t) * (trivialPole k - montgomeryPoleDown t))

/-- The shifted digamma summand `1/(k+2) − 2/(s + 2(k+1))`. -/
def digammaShiftTerm (s : ℂ) (k : ℕ) : ℂ := 1 / ((k : ℂ) + 2) - 2 / (s + 2 * ((k : ℂ) + 1))

theorem norm_cpow_xiZeroCopy_le {x : ℝ} (hx : 1 ≤ x) (q : XiZeroCopy) :
    ‖(x : ℂ) ^ (q.1 : ℂ)‖ ≤ x := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  calc x ^ ((q.1 : ℂ)).re ≤ x ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx (xiZeroCopy_re_lt_one q).le
    _ = x := Real.rpow_one x

/-- `‖ρ(1−ρ)‖ ≤ 16(1+t²)‖(ρ−a)(ρ−b)‖`: the Montgomery denominators dominate the genus kernel. -/
theorem norm_mul_one_sub_le_montgomery (t : ℝ) (q : XiZeroCopy) :
    ‖(q.1 : ℂ) * (1 - (q.1 : ℂ))‖ ≤ 16 * (1 + t ^ 2) *
      ‖((q.1 : ℂ) - montgomeryPoleUp t) * ((q.1 : ℂ) - montgomeryPoleDown t)‖ := by
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  set γ : ℝ := ((q.1 : ℂ)).im with hγ
  -- upper bound for the genus denominator
  have hA : ‖(q.1 : ℂ)‖ ≤ 1 + |γ| := by
    have := Complex.norm_le_abs_re_add_abs_im (q.1 : ℂ)
    have hre : |((q.1 : ℂ)).re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    linarith
  have hB : ‖1 - (q.1 : ℂ)‖ ≤ 1 + |γ| := by
    have := Complex.norm_le_abs_re_add_abs_im (1 - (q.1 : ℂ))
    have hre : |(1 - (q.1 : ℂ)).re| ≤ 1 := by
      simp only [Complex.sub_re, Complex.one_re]; rw [abs_le]; constructor <;> linarith
    have him : |(1 - (q.1 : ℂ)).im| = |γ| := by simp [hγ]
    rw [him] at this
    linarith
  have hAB : ‖(q.1 : ℂ) * (1 - (q.1 : ℂ))‖ ≤ 4 * (1 + t ^ 2) * (1 + (γ - t) ^ 2) := by
    rw [norm_mul]
    calc ‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ ≤ (1 + |γ|) * (1 + |γ|) := by gcongr
      _ ≤ 2 * (1 + γ ^ 2) := by nlinarith [abs_nonneg γ, sq_abs γ, sq_nonneg (1 - |γ|)]
      _ ≤ 4 * (1 + t ^ 2) * (1 + (γ - t) ^ 2) := by
          nlinarith [sq_nonneg (2 * t - γ), sq_nonneg (t * (γ - t))]
  -- lower bound for the Montgomery denominators
  have e1 : ‖(q.1 : ℂ) - montgomeryPoleUp t‖
      = Real.sqrt ((((q.1 : ℂ)).re - 3 / 2) ^ 2 + (γ - t) ^ 2) := by
    have : (q.1 : ℂ) - montgomeryPoleUp t
        = ((((q.1 : ℂ)).re - 3 / 2 : ℝ) : ℂ) + ((γ - t : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [montgomeryPoleUp, hγ]
    rw [this, Complex.norm_add_mul_I]
  have e2 : ‖(q.1 : ℂ) - montgomeryPoleDown t‖
      = Real.sqrt ((((q.1 : ℂ)).re + 1 / 2) ^ 2 + (γ - t) ^ 2) := by
    have : (q.1 : ℂ) - montgomeryPoleDown t
        = ((((q.1 : ℂ)).re + 1 / 2 : ℝ) : ℂ) + ((γ - t : ℝ) : ℂ) * I := by
      apply Complex.ext <;> norm_num [montgomeryPoleDown, hγ]
    rw [this, Complex.norm_add_mul_I]
  have hden : (1 + (γ - t) ^ 2) / 4
      ≤ ‖((q.1 : ℂ) - montgomeryPoleUp t) * ((q.1 : ℂ) - montgomeryPoleDown t)‖ := by
    rw [norm_mul, e1, e2]
    have hq1 : (1 / 4 : ℝ) + (γ - t) ^ 2 ≤ (((q.1 : ℂ)).re - 3 / 2) ^ 2 + (γ - t) ^ 2 := by
      nlinarith
    have hq2 : (1 / 4 : ℝ) + (γ - t) ^ 2 ≤ (((q.1 : ℂ)).re + 1 / 2) ^ 2 + (γ - t) ^ 2 := by
      nlinarith
    have hsq : Real.sqrt ((1 / 4 : ℝ) + (γ - t) ^ 2) * Real.sqrt ((1 / 4 : ℝ) + (γ - t) ^ 2)
        = (1 / 4 : ℝ) + (γ - t) ^ 2 := Real.mul_self_sqrt (by positivity)
    calc (1 + (γ - t) ^ 2) / 4 ≤ (1 / 4 : ℝ) + (γ - t) ^ 2 := by nlinarith
      _ = Real.sqrt ((1 / 4 : ℝ) + (γ - t) ^ 2) * Real.sqrt ((1 / 4 : ℝ) + (γ - t) ^ 2) := hsq.symm
      _ ≤ Real.sqrt ((((q.1 : ℂ)).re - 3 / 2) ^ 2 + (γ - t) ^ 2) *
          Real.sqrt ((((q.1 : ℂ)).re + 1 / 2) ^ 2 + (γ - t) ^ 2) :=
          mul_le_mul (Real.sqrt_le_sqrt hq1) (Real.sqrt_le_sqrt hq2) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
  calc ‖(q.1 : ℂ) * (1 - (q.1 : ℂ))‖ ≤ 4 * (1 + t ^ 2) * (1 + (γ - t) ^ 2) := hAB
    _ = 16 * (1 + t ^ 2) * ((1 + (γ - t) ^ 2) / 4) := by ring
    _ ≤ _ := by gcongr

theorem summable_montgomeryZeroTerm {x : ℝ} (hx : 1 ≤ x) (t : ℝ) :
    Summable (montgomeryZeroTerm x t) := by
  refine Summable.of_norm_bounded
    (g := fun q : XiZeroCopy => (32 * x * (1 + t ^ 2)) * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)
    (summable_inv_mul_one_sub.norm.mul_left _) fun q => ?_
  have hD : 0 < ‖((q.1 : ℂ) - montgomeryPoleUp t) * ((q.1 : ℂ) - montgomeryPoleDown t)‖ :=
    norm_pos_iff.mpr (mul_ne_zero (sub_ne_zero.mpr (xiZeroCopy_ne_montgomeryPoleUp q t))
      (sub_ne_zero.mpr (xiZeroCopy_ne_montgomeryPoleDown q t)))
  have hG : 0 < ‖(q.1 : ℂ) * (1 - (q.1 : ℂ))‖ :=
    norm_pos_iff.mpr (mul_ne_zero (xiZeroCopy_ne_zero q) (xiZeroCopy_one_sub_ne_zero q))
  have hkey := norm_mul_one_sub_le_montgomery t q
  unfold montgomeryZeroTerm
  rw [norm_div, norm_mul, norm_div, norm_one, show ‖(2 : ℂ)‖ = 2 by norm_num]
  rw [div_le_iff₀ hD]
  have hx' := norm_cpow_xiZeroCopy_le hx q
  calc 2 * ‖(x : ℂ) ^ (q.1 : ℂ)‖ ≤ 2 * x := by gcongr
    _ = (32 * x * (1 + t ^ 2)) * (1 / ‖(q.1 : ℂ) * (1 - (q.1 : ℂ))‖) *
          (16 * (1 + t ^ 2))⁻¹ * ‖(q.1 : ℂ) * (1 - (q.1 : ℂ))‖ := by
        field_simp
        ring
    _ ≤ (32 * x * (1 + t ^ 2)) * (1 / ‖(q.1 : ℂ) * (1 - (q.1 : ℂ))‖) *
          ((16 * (1 + t ^ 2))⁻¹ * (16 * (1 + t ^ 2) *
            ‖((q.1 : ℂ) - montgomeryPoleUp t) * ((q.1 : ℂ) - montgomeryPoleDown t)‖)) := by
        rw [mul_assoc (32 * x * (1 + t ^ 2) * (1 / ‖(q.1 : ℂ) * (1 - (q.1 : ℂ))‖))]
        gcongr
    _ = _ := by
        field_simp

theorem norm_montgomeryTrivialTerm_le {x : ℝ} (hx : 1 < x) (t : ℝ) (k : ℕ) :
    ‖montgomeryTrivialTerm x t k‖ ≤ ((x ^ 2)⁻¹) ^ k := by
  have hx0 : 0 < x := by linarith
  unfold montgomeryTrivialTerm
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, trivialPole_re]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  -- numerator `x^{−2(k+1)} ≤ x^{−2k}`
  have hnum : x ^ (-(2 * ((k : ℝ) + 1))) ≤ ((x ^ 2)⁻¹) ^ k := by
    have hcast : (2 * ((k : ℝ) + 1)) = ((2 * (k + 1) : ℕ) : ℝ) := by push_cast; ring
    rw [Real.rpow_neg hx0.le, hcast, Real.rpow_natCast, pow_mul, ← inv_pow, pow_succ]
    have hle : (x ^ 2)⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; nlinarith
    calc ((x ^ 2)⁻¹) ^ k * (x ^ 2)⁻¹ ≤ ((x ^ 2)⁻¹) ^ k * 1 := by gcongr
      _ = _ := mul_one _
  -- denominator `≥ 1`
  have hd1 : 1 ≤ ‖trivialPole k - montgomeryPoleUp t‖ := by
    have := Complex.abs_re_le_norm (trivialPole k - montgomeryPoleUp t)
    rw [Complex.sub_re, trivialPole_re, montgomeryPoleUp_re] at this
    rw [abs_le] at this
    linarith [this.1]
  have hd2 : 1 ≤ ‖trivialPole k - montgomeryPoleDown t‖ := by
    have := Complex.abs_re_le_norm (trivialPole k - montgomeryPoleDown t)
    rw [Complex.sub_re, trivialPole_re, montgomeryPoleDown_re] at this
    rw [abs_le] at this
    linarith [this.1]
  calc x ^ (-(2 * ((k : ℝ) + 1))) / (‖trivialPole k - montgomeryPoleUp t‖ *
        ‖trivialPole k - montgomeryPoleDown t‖)
      ≤ x ^ (-(2 * ((k : ℝ) + 1))) / 1 := by
        gcongr
        exact one_le_mul_of_one_le_of_one_le hd1 hd2
    _ ≤ _ := by rw [div_one]; exact hnum

theorem summable_montgomeryTrivialTerm {x : ℝ} (hx : 1 < x) (t : ℝ) :
    Summable (montgomeryTrivialTerm x t) := by
  have hr : (x ^ 2)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]; right; nlinarith
  exact Summable.of_norm_bounded (summable_geometric_of_lt_one (by positivity) hr)
    (norm_montgomeryTrivialTerm_le hx t)

theorem norm_digammaShiftTerm_le {s : ℂ} (hs : -1 / 2 ≤ s.re) (k : ℕ) :
    ‖digammaShiftTerm s k‖ ≤ ‖s - 2‖ * (1 / ((k : ℝ) + 1) ^ 2) := by
  unfold digammaShiftTerm
  have hk2 : ((k : ℂ) + 2) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (k + 1))
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hre : ((k : ℝ) + 1) ≤ (s + 2 * ((k : ℂ) + 1)).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.one_re]
    norm_num
    linarith
  have hs0 : s + 2 * ((k : ℂ) + 1) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [Complex.zero_re] at this
    linarith
  have hid : 1 / ((k : ℂ) + 2) - 2 / (s + 2 * ((k : ℂ) + 1))
      = (s - 2) / (((k : ℂ) + 2) * (s + 2 * ((k : ℂ) + 1))) := by
    field_simp
    ring
  rw [hid, norm_div, norm_mul]
  have hn1 : ((k : ℝ) + 1) ≤ ‖(k : ℂ) + 2‖ := by
    have : ‖(k : ℂ) + 2‖ = (k : ℝ) + 2 := by
      rw [show (k : ℂ) + 2 = ((k + 2 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast; ring
    rw [this]; linarith
  have hn2 : ((k : ℝ) + 1) ≤ ‖s + 2 * ((k : ℂ) + 1)‖ :=
    hre.trans (Complex.re_le_norm _)
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  calc ‖s - 2‖ / (‖(k : ℂ) + 2‖ * ‖s + 2 * ((k : ℂ) + 1)‖)
      ≤ ‖s - 2‖ / (((k : ℝ) + 1) * ((k : ℝ) + 1)) := by
        gcongr
    _ = ‖s - 2‖ * (1 / ((k : ℝ) + 1) ^ 2) := by
        field_simp

theorem summable_digammaShiftTerm {s : ℂ} (hs : -1 / 2 ≤ s.re) :
    Summable (digammaShiftTerm s) := by
  have hb : Summable (fun k : ℕ => ‖s - 2‖ * (1 / ((k : ℝ) + 1) ^ 2)) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
    refine (h.mul_left ‖s - 2‖).congr fun k => ?_
    push_cast
    ring
  exact Summable.of_norm_bounded hb (norm_digammaShiftTerm_le hs)

/-- The `q`-th Mittag-Leffler value, rearranged: `−Z_q − x^a P_a(ρ) + x^b P_b(ρ)`. -/
theorem integral_mzTerm_eq {x : ℝ} (hx : 1 < x) (t : ℝ) (q : XiZeroCopy) :
    (1 / (2 * Real.pi) : ℝ) • ∫ τ : ℝ, mzTerm x t q τ =
      -montgomeryZeroTerm x t q
        - (x : ℂ) ^ montgomeryPoleUp t * (((q.1 : ℂ) - 1 / 2)⁻¹ + (montgomeryPoleUp t - (q.1 : ℂ))⁻¹)
        + (x : ℂ) ^ montgomeryPoleDown t *
          (((q.1 : ℂ) - 1 / 2)⁻¹ + (montgomeryPoleDown t - (q.1 : ℂ))⁻¹) := by
  rw [integral_mzTerm hx t q]
  unfold montgomeryZeroTerm
  have h1 := xiZeroCopy_sub_half_ne_zero q
  have h2 : (q.1 : ℂ) - montgomeryPoleUp t ≠ 0 := sub_ne_zero.mpr (xiZeroCopy_ne_montgomeryPoleUp q t)
  have h3 : (q.1 : ℂ) - montgomeryPoleDown t ≠ 0 :=
    sub_ne_zero.mpr (xiZeroCopy_ne_montgomeryPoleDown q t)
  have h2' : montgomeryPoleUp t - (q.1 : ℂ) ≠ 0 := fun h => h2 (by rw [← neg_sub, h, neg_zero])
  have h3' : montgomeryPoleDown t - (q.1 : ℂ) ≠ 0 := fun h => h3 (by rw [← neg_sub, h, neg_zero])
  have hab := montgomeryPoleUp_sub_down t
  have hab' : (q.1 : ℂ) - montgomeryPoleDown t = (q.1 : ℂ) - montgomeryPoleUp t + 2 := by
    rw [← hab]; ring
  have hab'' : montgomeryPoleDown t - (q.1 : ℂ) = -((q.1 : ℂ) - montgomeryPoleUp t + 2) := by
    rw [← hab']; ring
  have hup : montgomeryPoleUp t - (q.1 : ℂ) = -((q.1 : ℂ) - montgomeryPoleUp t) := by ring
  rw [hab', hab'', hup]
  have h4 : (q.1 : ℂ) - montgomeryPoleUp t + 2 ≠ 0 := by rw [← hab']; exact h3
  field_simp
  ring

/-- The `k`-th Mittag-Leffler value, rearranged: `4 T_k − x^a d_k(a) + x^b d_k(b)`. -/
theorem integral_mkTerm_eq {x : ℝ} (hx : 1 < x) (t : ℝ) (k : ℕ) :
    (1 / (2 * Real.pi) : ℝ) • ∫ τ : ℝ, mkTerm x t k τ =
      4 * montgomeryTrivialTerm x t k
        - (x : ℂ) ^ montgomeryPoleUp t * digammaShiftTerm (montgomeryPoleUp t) k
        + (x : ℂ) ^ montgomeryPoleDown t * digammaShiftTerm (montgomeryPoleDown t) k := by
  rw [integral_mkTerm hx t k]
  unfold montgomeryTrivialTerm digammaShiftTerm
  have hk2 : ((k : ℂ) + 2) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (k + 1))
  have h2 : trivialPole k - montgomeryPoleUp t ≠ 0 :=
    sub_ne_zero.mpr (trivialPole_ne_montgomeryPoleUp k t)
  have h3 : trivialPole k - montgomeryPoleDown t ≠ 0 :=
    sub_ne_zero.mpr (trivialPole_ne_montgomeryPoleDown k t)
  have hca : montgomeryPoleUp t + 2 * ((k : ℂ) + 1) = -(trivialPole k - montgomeryPoleUp t) := by
    unfold trivialPole; ring
  have hcb : montgomeryPoleDown t + 2 * ((k : ℂ) + 1) = -(trivialPole k - montgomeryPoleDown t) := by
    unfold trivialPole; ring
  have hab := montgomeryPoleUp_sub_down t
  have hab' : trivialPole k - montgomeryPoleDown t = trivialPole k - montgomeryPoleUp t + 2 := by
    rw [← hab]; ring
  rw [hca, hcb, hab']
  have h4 : trivialPole k - montgomeryPoleUp t + 2 ≠ 0 := by rw [← hab']; exact h3
  field_simp
  ring

theorem tsum_integral_mzTerm {x : ℝ} (hx : 1 < x) (t : ℝ) :
    ∑' q : XiZeroCopy, (1 / (2 * Real.pi) : ℝ) • ∫ τ : ℝ, mzTerm x t q τ =
      -(∑' q : XiZeroCopy, montgomeryZeroTerm x t q)
        - (x : ℂ) ^ montgomeryPoleUp t * logDeriv xi (montgomeryPoleUp t)
        + (x : ℂ) ^ montgomeryPoleDown t * logDeriv xi (montgomeryPoleDown t) := by
  simp_rw [integral_mzTerm_eq hx t]
  have hZ := summable_montgomeryZeroTerm hx.le t
  have hPa := summable_partialFractionTerm (xi_montgomeryPoleUp_ne_zero t)
  have hPb := summable_partialFractionTerm (xi_montgomeryPoleDown_ne_zero t)
  rw [Summable.tsum_add ((hZ.neg).sub (hPa.mul_left _)) (hPb.mul_left _),
    Summable.tsum_sub hZ.neg (hPa.mul_left _), tsum_neg, tsum_mul_left, tsum_mul_left,
    ← logDeriv_xi_eq_partialFraction (xi_montgomeryPoleUp_ne_zero t),
    ← logDeriv_xi_eq_partialFraction (xi_montgomeryPoleDown_ne_zero t)]

theorem tsum_integral_mkTerm {x : ℝ} (hx : 1 < x) (t : ℝ) :
    ∑' k : ℕ, (1 / (2 * Real.pi) : ℝ) • ∫ τ : ℝ, mkTerm x t k τ =
      4 * (∑' k : ℕ, montgomeryTrivialTerm x t k)
        - (x : ℂ) ^ montgomeryPoleUp t * (∑' k : ℕ, digammaShiftTerm (montgomeryPoleUp t) k)
        + (x : ℂ) ^ montgomeryPoleDown t * (∑' k : ℕ, digammaShiftTerm (montgomeryPoleDown t) k) := by
  simp_rw [integral_mkTerm_eq hx t]
  have hT := summable_montgomeryTrivialTerm hx t
  have hDa := summable_digammaShiftTerm (s := montgomeryPoleUp t) (by rw [montgomeryPoleUp_re]; norm_num)
  have hDb := summable_digammaShiftTerm (s := montgomeryPoleDown t)
    (by rw [montgomeryPoleDown_re])
  rw [Summable.tsum_add ((hT.mul_left 4).sub (hDa.mul_left _)) (hDb.mul_left _),
    Summable.tsum_sub (hT.mul_left 4) (hDa.mul_left _), tsum_mul_left, tsum_mul_left, tsum_mul_left]

/-- **Montgomery's lemma, exact form.**  For `x > 1` and every height `t`, with `a = 3/2 + it`,
`b = −1/2 + it`, `c_k = −2(k+1)`, `S(s) = Σ_k (1/(k+2) − 2/(s+2(k+1)))` and
`c₁ = ½ − ½ log π − ½ γ`:

`Σ_ρ 2x^{ρ}/((ρ−a)(ρ−b)) = −Σ_{n≤x} Λ(n)((x/n)^a − (x/n)^b) + ((x−x^a)/(1−a) − (x−x^b)/(1−b))
  + c₁(x^a − x^b) − 2Σ_k x^{c_k}/((c_k−a)(c_k−b)) + ½x^a S(a) − ½x^b S(b) − x^a ξ'/ξ(a) + x^b ξ'/ξ(b)`.

The zero sum is absolutely convergent; every zero of `ξ` counted with multiplicity. -/
theorem montgomery_lemma_one {x : ℝ} (hx : 1 < x) (t : ℝ) :
    ∑' q : XiZeroCopy, montgomeryZeroTerm x t q =
      -(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((vonMangoldt n : ℝ) : ℂ) *
          (((x / n : ℝ) : ℂ) ^ montgomeryPoleUp t - ((x / n : ℝ) : ℂ) ^ montgomeryPoleDown t))
        + (((x : ℂ) - (x : ℂ) ^ montgomeryPoleUp t) / (1 - montgomeryPoleUp t) -
            ((x : ℂ) - (x : ℂ) ^ montgomeryPoleDown t) / (1 - montgomeryPoleDown t))
        + ((1 : ℂ) / 2 - (Real.log Real.pi : ℂ) / 2 - (Real.eulerMascheroniConstant : ℂ) / 2) *
            ((x : ℂ) ^ montgomeryPoleUp t - (x : ℂ) ^ montgomeryPoleDown t)
        - 2 * (∑' k : ℕ, montgomeryTrivialTerm x t k)
        + (1 / 2 : ℂ) * (x : ℂ) ^ montgomeryPoleUp t *
            (∑' k : ℕ, digammaShiftTerm (montgomeryPoleUp t) k)
        - (1 / 2 : ℂ) * (x : ℂ) ^ montgomeryPoleDown t *
            (∑' k : ℕ, digammaShiftTerm (montgomeryPoleDown t) k)
        - (x : ℂ) ^ montgomeryPoleUp t * logDeriv xi (montgomeryPoleUp t)
        + (x : ℂ) ^ montgomeryPoleDown t * logDeriv xi (montgomeryPoleDown t) := by
  have hD := montgomery_dirichlet_side hx t
  have hM := montgomery_mittagLeffler_side hx t
  rw [tsum_integral_mkTerm hx t, tsum_integral_mzTerm hx t] at hM
  have hkey := hD.symm.trans hM
  linear_combination -hkey

end

end RHTower
