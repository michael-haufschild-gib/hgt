import GaloisForLFunctions.RHTower.DeckPoincareFourier
import GaloisForLFunctions.RHTower.KuznetsovKernelIntegral

/-!
# The rows of the Poincaré pairing in Kuznetsov's coordinates

The conjugate Selberg profile `h̄_{s,ν}(w) = conj((Im w)^s e(νw)) = (Im w)^{s̄} e(−ν w̄)` with a cusp
vector `w` of frequency `−ν` gives the deck Poincaré series `P(·| h̄_{s,ν}, w)`, the conjugate of
`U_{𝔟n}(·, s)`.  For a row `(c, d)` with `c ≠ 0` of `M = (a b; c d)` and `x = yξ − d/c`,

`Im(M(x+iy)) = 1/(c² y (1+ξ²))`, `conj(M(x+iy)) = a/c − 1/(c² y (ξ − i))`,

and the term of the Fourier coefficient of `P(·| h̄_{s₂,ν}, w)` at the frequency `μ`, weighted by the
conjugate profile of `U_{𝔞m}(·, s₁)` and the invariant measure, is

`y^{s̄₁−2} e^{−2πμy} · y · coeffTerm(yξ − d/c) = ⟨v, ρ(M)⁻¹w⟩ e((μd − νa)/c) (c²)^{−s̄₂}
  K(s̄₁, s̄₂; μ, ν, c²)(y, ξ)`

with Kuznetsov's kernel `K` (`kuzKernel`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set EisensteinSeries Complex
open scoped MatrixGroups InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-! ## The conjugate profile -/

/-- **The conjugate Selberg profile** `conj((Im w)^s e(νw))`. -/
def conjProfile (s : ℂ) (ν : ℝ) (w : ℍ) : ℂ := conj (poincProfile s ν w)

theorem norm_conjProfile (s : ℂ) (ν : ℝ) (w : ℍ) : ‖conjProfile s ν w‖ = ‖poincProfile s ν w‖ :=
  Complex.norm_conj _

theorem continuous_conjProfile (s : ℂ) (ν : ℝ) : Continuous (conjProfile s ν) :=
  Complex.continuous_conj.comp (continuous_poincProfile s ν)

theorem conjProfile_apply (s : ℂ) (ν : ℝ) (u : ℍ) :
    conjProfile s ν u = ((u.im : ℝ) : ℂ) ^ (conj s) *
      cexp (-(2 * Real.pi * Complex.I * ν * conj (u : ℂ))) := by
  have harg : ((u.im : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg u.im_pos.le]
    exact Real.pi_pos.ne
  have h1 : conj (((u.im : ℝ) : ℂ) ^ s) = ((u.im : ℝ) : ℂ) ^ (conj s) := by
    rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]
  rw [conjProfile, poincProfile, map_mul, ← Complex.exp_conj, h1]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

theorem cuspCompatible_conjProfile (s : ℂ) {ν : ℝ} {w : DeckSpace N} (hw : IsCuspEigen (-ν) w) :
    CuspCompatible (conjProfile s ν) w := fun n u => by
  have hinv : (deckRho N (ModularGroup.T ^ n)).symm w =
      cexp (2 * Real.pi * Complex.I * ν * n) • w := by
    refine symm_eq_of_apply_eq ?_
    rw [map_smul, deckRho_T_zpow_eigen hw, smul_smul, ← Complex.exp_add]
    push_cast
    rw [show 2 * (Real.pi : ℂ) * Complex.I * ν * n + 2 * Real.pi * Complex.I * -ν * n = 0 by ring,
      Complex.exp_zero, one_smul]
  rw [hinv, conjProfile, conjProfile, poincProfile_T_zpow, map_mul, ← Complex.exp_conj, smul_smul]
  congr 1
  rw [mul_comm, ← mul_assoc, ← Complex.exp_add]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_intCast]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ν * n + 2 * Real.pi * -Complex.I * ν * n = 0 by ring,
    Complex.exp_zero, one_mul]

theorem summable_norm_conjProfile {s : ℂ} (hs : 1 < s.re) {ν : ℝ} (hν : 0 ≤ ν) (z : ℍ) :
    Summable fun p : gammaSet 1 1 0 => ‖conjProfile s ν (gammaSetMatrix p • z)‖ := by
  simp_rw [norm_conjProfile]
  exact summable_norm_poincProfile hs hν z

theorem continuous_tsum_norm_conjProfile {s : ℂ} (hs : 1 < s.re) {ν : ℝ} (hν : 0 ≤ ν) :
    Continuous fun z : ℍ => ∑' p : gammaSet 1 1 0, ‖conjProfile s ν (gammaSetMatrix p • z)‖ := by
  simp_rw [norm_conjProfile]
  exact continuous_tsum_norm_poincProfile hs hν

theorem continuous_poincSeries_conjProfile {s : ℂ} (hs : 1 < s.re) {ν : ℝ} (hν : 0 ≤ ν)
    (w : DeckSpace N) : Continuous (poincSeries (conjProfile s ν) w) :=
  continuous_tsum_of_rowHeight_bound
    (fun p => ((continuous_conjProfile s ν).comp (continuous_modular_smul _)).smul continuous_const)
    hs (norm_nonneg w) fun p z => by
      rw [norm_poincTerm, mul_comm, norm_conjProfile]
      exact mul_le_mul_of_nonneg_left (norm_poincProfile_le hν _) (norm_nonneg _)

theorem memLp_poincSeries_conjProfile {s : ℂ} (hs : 1 < s.re) {ν : ℝ} (hν : 0 < ν)
    (w : DeckSpace N) : MemLp (poincSeries (conjProfile s ν) w) 2 cellMeasure := by
  refine ((memLp_tsum_norm_poincProfile hs hν).const_mul ‖w‖).of_le
    (continuous_poincSeries_conjProfile hs hν.le w).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  have hsum := summable_norm_conjProfile hs hν.le z
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _)
    (tsum_nonneg fun _ => norm_nonneg _))]
  calc ‖poincSeries (conjProfile s ν) w z‖ ≤ ∑' p, ‖poincTerm (conjProfile s ν) w p z‖ :=
        norm_tsum_le_tsum_norm (hsum.mul_right ‖w‖ |>.congr fun p =>
          (norm_poincTerm _ w p z).symm)
    _ = ‖w‖ * ∑' p : gammaSet 1 1 0, ‖poincProfile s ν (gammaSetMatrix p • z)‖ := by
        simp_rw [norm_poincTerm, norm_conjProfile]
        rw [tsum_mul_right, mul_comm]

/-! ## Möbius coordinates of a row -/

theorem det_gammaSetMatrix (p : gammaSet 1 1 0) :
    (gammaSetMatrix p 0 0 : ℂ) * (p.1 1 : ℂ) - (gammaSetMatrix p 0 1 : ℂ) * (p.1 0 : ℂ) = 1 := by
  have h := (gammaSetMatrix p).det_coe
  rw [Matrix.det_fin_two, gammaSetMatrix_apply_one_zero, gammaSetMatrix_apply_one_one] at h
  exact_mod_cast h

theorem coe_gammaSetMatrix_smul (p : gammaSet 1 1 0) (z : ℍ) :
    ((gammaSetMatrix p • z : ℍ) : ℂ) =
      ((gammaSetMatrix p 0 0 : ℂ) * z + (gammaSetMatrix p 0 1 : ℂ)) /
        ((p.1 0 : ℂ) * z + (p.1 1 : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, gammaSetMatrix_apply_one_zero,
    gammaSetMatrix_apply_one_one]
  simp

/-- The row point `x = yξ − d/c` at height `y`. -/
def rowPoint (p : gammaSet 1 1 0) {y : ℝ} (hy : 0 < y) (ξ : ℝ) : ℍ :=
  hLine hy (y * ξ - (p.1 1 : ℝ) / (p.1 0 : ℝ))

theorem denom_rowPoint {p : gammaSet 1 1 0} (hc : p.1 0 ≠ 0) {y : ℝ} (hy : 0 < y) (ξ : ℝ) :
    (p.1 0 : ℂ) * (rowPoint p hy ξ : ℂ) + (p.1 1 : ℂ) = (p.1 0 : ℂ) * y * (ξ + Complex.I) := by
  have hc' : (p.1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [rowPoint, coe_hLine]
  push_cast
  field_simp
  ring

theorem im_gammaSetMatrix_smul_rowPoint {p : gammaSet 1 1 0} (hc : p.1 0 ≠ 0) {y : ℝ} (hy : 0 < y)
    (ξ : ℝ) :
    (gammaSetMatrix p • rowPoint p hy ξ).im = ((p.1 0 : ℝ) ^ 2 * y * (1 + ξ ^ 2))⁻¹ := by
  rw [im_gammaSetMatrix_smul, denom_rowPoint hc hy, rowPoint, hLine_im]
  have hc' : (p.1 0 : ℝ) ≠ 0 := by exact_mod_cast hc
  rw [show ((p.1 0 : ℤ) : ℂ) * (y : ℂ) * ((ξ : ℂ) + Complex.I) =
      (((p.1 0 : ℝ) * y : ℝ) : ℂ) * ((ξ : ℂ) + Complex.I) by push_cast; ring,
    Complex.normSq_mul, Complex.normSq_ofReal]
  rw [show Complex.normSq ((ξ : ℂ) + Complex.I) = 1 + ξ ^ 2 by
    rw [Complex.normSq_apply]; simp; ring]
  field_simp

theorem conj_gammaSetMatrix_smul_rowPoint {p : gammaSet 1 1 0} (hc : p.1 0 ≠ 0) {y : ℝ}
    (hy : 0 < y) (ξ : ℝ) :
    conj ((gammaSetMatrix p • rowPoint p hy ξ : ℍ) : ℂ) =
      (gammaSetMatrix p 0 0 : ℂ) / (p.1 0 : ℂ) -
        1 / ((p.1 0 : ℂ) ^ 2 * y * (ξ - Complex.I)) := by
  have hc' : (p.1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hξ : (ξ : ℂ) + Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have hdet := det_gammaSetMatrix p
  have hz : (rowPoint p hy ξ : ℂ) = y * (ξ + Complex.I) - (p.1 1 : ℂ) / (p.1 0 : ℂ) := by
    rw [rowPoint, coe_hLine]; push_cast; ring
  have hnum : (gammaSetMatrix p 0 0 : ℂ) * (rowPoint p hy ξ : ℂ) + (gammaSetMatrix p 0 1 : ℂ) =
      (gammaSetMatrix p 0 0 : ℂ) * y * (ξ + Complex.I) - 1 / (p.1 0 : ℂ) := by
    rw [hz]
    field_simp
    linear_combination -hdet
  have hM : ((gammaSetMatrix p • rowPoint p hy ξ : ℍ) : ℂ) =
      (gammaSetMatrix p 0 0 : ℂ) / (p.1 0 : ℂ) - 1 / ((p.1 0 : ℂ) ^ 2 * y * (ξ + Complex.I)) := by
    rw [coe_gammaSetMatrix_smul, denom_rowPoint hc hy, hnum]
    field_simp
  rw [hM]
  simp only [map_sub, map_div₀, map_one, map_mul, map_pow, map_intCast, Complex.conj_ofReal,
    map_add, Complex.conj_I]
  ring

/-! ## The row term as Kuznetsov's kernel -/

/-- The row weight `⟨v, ρ(M)⁻¹w⟩ e((μd − νa)/c)` of `M = (a b; c d)`. -/
def rowWeight (μ ν : ℝ) (v w : DeckSpace N) (p : gammaSet 1 1 0) : ℂ :=
  ⟪v, (deckRho N (gammaSetMatrix p)).symm w⟫_ℂ *
    cexp (2 * Real.pi * Complex.I *
      ((μ * (p.1 1 : ℂ) - ν * (gammaSetMatrix p 0 0 : ℂ)) / (p.1 0 : ℂ)))

theorem norm_rowWeight_le (μ ν : ℝ) (v w : DeckSpace N) (p : gammaSet 1 1 0) :
    ‖rowWeight μ ν v w p‖ ≤ ‖v‖ * ‖w‖ := by
  rw [rowWeight, norm_mul]
  have he : ‖cexp (2 * Real.pi * Complex.I *
      ((μ * (p.1 1 : ℂ) - ν * (gammaSetMatrix p 0 0 : ℂ)) / (p.1 0 : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    have : (2 * Real.pi * Complex.I *
        ((μ * (p.1 1 : ℂ) - ν * (gammaSetMatrix p 0 0 : ℂ)) / (p.1 0 : ℂ))).re = 0 := by
      rw [show (2 * Real.pi * Complex.I *
          ((μ * (p.1 1 : ℂ) - ν * (gammaSetMatrix p 0 0 : ℂ)) / (p.1 0 : ℂ))) =
          (((2 * Real.pi * ((μ * (p.1 1 : ℝ) - ν * (gammaSetMatrix p 0 0 : ℝ)) / (p.1 0 : ℝ)) : ℝ)
            : ℂ) * Complex.I) by push_cast; ring]
      simp
    rw [this, Real.exp_zero]
  rw [he, mul_one]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [LinearIsometryEquiv.norm_map]

theorem ofReal_inv_cpow {r : ℝ} (hr : 0 < r) (s : ℂ) :
    ((r⁻¹ : ℝ) : ℂ) ^ s = (r : ℂ) ^ (-s) := by
  have harg : (r : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_pos.ne
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg]

/-- **The row term in Kuznetsov's coordinates.** -/
theorem coeffTerm_rowPoint_eq_kuzKernel {μ ν : ℝ} (hμ : 0 < μ) (s₁ s₂ : ℂ) (v w : DeckSpace N)
    {p : gammaSet 1 1 0} (hc : p.1 0 ≠ 0) {y : ℝ} (hy : 0 < y) (ξ : ℝ) :
    ((y ^ 2)⁻¹ : ℝ) • ((y : ℂ) ^ (conj s₁) * (Real.exp (-(2 * Real.pi * μ * y)) : ℂ) *
      ((y : ℂ) * coeffTerm μ v (conjProfile s₂ ν) w hy p
        (y * ξ - (p.1 1 : ℝ) / (p.1 0 : ℝ)))) =
      rowWeight μ ν v w p * (((p.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-conj s₂) *
        Kuznetsov.kuzKernel (conj s₁) (conj s₂) μ ν ((p.1 0 : ℝ) ^ 2) (y, ξ) := by
  have hc' : (p.1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
  have hcr : (p.1 0 : ℝ) ≠ 0 := by exact_mod_cast hc
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hξ1 : (1 : ℂ) + Complex.I * ξ ≠ 0 := Kuznetsov.one_add_I_mul_ne_zero ξ
  have hξI : (ξ : ℂ) - Complex.I = -Complex.I * (1 + Complex.I * ξ) := by
    ring_nf; rw [Complex.I_sq]; ring
  have hξ0 : 0 < 1 + ξ ^ 2 := by positivity
  have hc2 : 0 < (p.1 0 : ℝ) ^ 2 := by positivity
  -- the profile at the row point
  have hrow : coeffTerm μ v (conjProfile s₂ ν) w hy p (y * ξ - (p.1 1 : ℝ) / (p.1 0 : ℝ)) =
      cexp (-(2 * Real.pi * Complex.I * μ * ((y * ξ - (p.1 1 : ℝ) / (p.1 0 : ℝ) : ℝ) : ℂ))) *
        ((((p.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-conj s₂) * (y : ℂ) ^ (-conj s₂) *
          (((1 + ξ ^ 2 : ℝ)) : ℂ) ^ (-conj s₂) *
          cexp (-(2 * Real.pi * Complex.I * ν * ((gammaSetMatrix p 0 0 : ℂ) / (p.1 0 : ℂ) -
            1 / ((p.1 0 : ℂ) ^ 2 * y * (ξ - Complex.I))))) *
          ⟪v, (deckRho N (gammaSetMatrix p)).symm w⟫_ℂ) := by
    rw [coeffTerm, cuspChar, poincTerm, inner_smul_right]
    change _ * (conjProfile s₂ ν (gammaSetMatrix p • rowPoint p hy ξ) * _) = _
    rw [conjProfile_apply, im_gammaSetMatrix_smul_rowPoint hc hy,
      conj_gammaSetMatrix_smul_rowPoint hc hy, ofReal_inv_cpow (by positivity),
      Complex.ofReal_mul ((p.1 0 : ℝ) ^ 2 * y), Complex.mul_cpow_ofReal_nonneg (by positivity) hξ0.le,
      Complex.ofReal_mul ((p.1 0 : ℝ) ^ 2), Complex.mul_cpow_ofReal_nonneg hc2.le hy.le]
  -- the power of `y`
  have hpow : (y : ℂ) ^ (conj s₁ - conj s₂ - 1) =
      (y : ℂ) ^ (conj s₁) * (y : ℂ) ^ (-conj s₂) * (y : ℂ)⁻¹ := by
    rw [sub_eq_add_neg, sub_eq_add_neg, Complex.cpow_add _ _ hy', Complex.cpow_add _ _ hy',
      Complex.cpow_neg_one]
  -- the exponent
  have hexp : cexp (-(Kuznetsov.kuzRate μ ξ * y) -
      (Kuznetsov.kuzParam μ ν ((p.1 0 : ℝ) ^ 2) : ℂ) / (Kuznetsov.kuzRate μ ξ * y)) =
      cexp (-(2 * Real.pi * Complex.I * μ * ((y * ξ - (p.1 1 : ℝ) / (p.1 0 : ℝ) : ℝ) : ℂ))) *
        cexp (-(2 * Real.pi * Complex.I * ν * ((gammaSetMatrix p 0 0 : ℂ) / (p.1 0 : ℂ) -
          1 / ((p.1 0 : ℂ) ^ 2 * y * (ξ - Complex.I))))) *
        cexp ((-(2 * Real.pi * μ * y) : ℝ) : ℂ) /
        cexp (2 * Real.pi * Complex.I *
          ((μ * (p.1 1 : ℂ) - ν * (gammaSetMatrix p 0 0 : ℂ)) / (p.1 0 : ℂ))) := by
    rw [eq_div_iff (Complex.exp_ne_zero _), ← Complex.exp_add, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    rw [hξI, Kuznetsov.kuzRate, Kuznetsov.kuzParam]
    push_cast
    field_simp
    ring
  rw [Kuznetsov.kuzKernel, Kuznetsov.invGaussKernel, hexp, hpow, hrow, rowWeight,
    Complex.real_smul, ← Complex.ofReal_exp]
  push_cast
  field_simp

/-! ## The fixed-height row integral -/

/-- **The row integral at height `y`** in Kuznetsov's coordinates `x = yξ − d/c`. -/
theorem integral_coeffTerm_conjProfile {μ ν : ℝ} (hμ : 0 < μ) (s₁ s₂ : ℂ) (v w : DeckSpace N)
    {p : gammaSet 1 1 0} (hc : p.1 0 ≠ 0) {y : ℝ} (hy : 0 < y) :
    ((y ^ 2)⁻¹ : ℝ) • ((y : ℂ) ^ (conj s₁) * (Real.exp (-(2 * Real.pi * μ * y)) : ℂ) *
      ∫ x, coeffTerm μ v (conjProfile s₂ ν) w hy p x) =
      rowWeight μ ν v w p * (((p.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-conj s₂) *
        ∫ ξ, Kuznetsov.kuzKernel (conj s₁) (conj s₂) μ ν ((p.1 0 : ℝ) ^ 2) (y, ξ) := by
  set f := coeffTerm μ v (conjProfile s₂ ν) w hy p
  set e : ℝ := (p.1 1 : ℝ) / (p.1 0 : ℝ)
  have h1 : ∫ x, f x = (y : ℂ) * ∫ ξ, f (y * ξ - e) := by
    rw [← integral_sub_right_eq_self f e]
    have h := Measure.integral_comp_mul_left (fun x => f (x - e)) y
    rw [abs_inv, abs_of_pos hy] at h
    rw [h, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hy.ne',
      Complex.ofReal_one, one_mul]
  rw [h1, ← integral_const_mul, ← integral_const_mul, ← integral_smul, ← integral_const_mul]
  congr 1
  funext ξ
  exact coeffTerm_rowPoint_eq_kuzKernel (ν := ν) hμ s₁ s₂ v w hc hy ξ

/-! ## The diagonal term vanishes -/

theorem isCuspEigen_add_neg_one {ν : ℝ} {w : DeckSpace N} (hw : IsCuspEigen ν w) :
    IsCuspEigen ν (w + (deckRho N (-1)).symm w) := by
  have hcomm : deckRho N ModularGroup.T ((deckRho N (-1)).symm w) =
      (deckRho N (-1)).symm (deckRho N ModularGroup.T w) := by
    rw [← deckRho_inv, ← deckRho_mul, ← deckRho_mul,
      ((Commute.neg_one_right ModularGroup.T).inv_right).eq]
  unfold IsCuspEigen at hw ⊢
  rw [map_add, hcomm, hw, map_smul, smul_add]

theorem inner_cuspEigen_mul_eq_zero {μ ν : ℝ} {v u : DeckSpace N} (hv : IsCuspEigen μ v)
    (hu : IsCuspEigen (-ν) u) :
    (1 - cexp (-(2 * Real.pi * Complex.I * (μ + ν)))) * ⟪v, u⟫_ℂ = 0 := by
  have h := (deckRho N ModularGroup.T).inner_map_map v u
  rw [hv, hu, inner_smul_left, inner_smul_right, ← Complex.exp_conj, ← mul_assoc,
    ← Complex.exp_add] at h
  have he : conj (2 * Real.pi * Complex.I * μ) + 2 * Real.pi * Complex.I * ((-ν : ℝ) : ℂ) =
      -(2 * Real.pi * Complex.I * (μ + ν)) := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  rw [he] at h
  linear_combination -h

theorem diagonal_conjProfile_eq_zero {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (s : ℂ)
    {v w : DeckSpace N} (hv : IsCuspEigen μ v) (hw : IsCuspEigen (-ν) w) {y : ℝ} (hy : 0 < y) :
    (∫ x in Ico (0 : ℝ) 1, cuspChar μ x * conjProfile s ν (hLine hy x)) *
      ⟪v, w + (deckRho N (-1)).symm w⟫_ℂ = 0 := by
  set c : ℂ := -(2 * Real.pi * Complex.I * (μ + ν))
  have hc : c ≠ 0 := by
    have : (μ + ν : ℂ) ≠ 0 := by exact_mod_cast (by linarith : μ + ν ≠ 0)
    simp only [c, neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
      (by exact_mod_cast Real.pi_pos.ne')) Complex.I_ne_zero) this
  have hpt : ∀ x : ℝ, cuspChar μ x * conjProfile s ν (hLine hy x) =
      (y : ℂ) ^ (conj s) * cexp (-(2 * Real.pi * ν * y : ℝ)) * cexp (c * x) := fun x => by
    rw [cuspChar, conjProfile_apply, hLine_im, coe_hLine, mul_left_comm, ← Complex.exp_add,
      mul_assoc ((y : ℂ) ^ (conj s)), ← Complex.exp_add]
    congr 2
    simp only [c, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le
    zero_le_one, integral_exp_mul_complex hc]
  have h0 := inner_cuspEigen_mul_eq_zero hv (isCuspEigen_add_neg_one hw)
  push_cast
  rw [mul_one, mul_zero, Complex.exp_zero]
  have : (cexp c - 1) * ⟪v, w + (deckRho N (-1)).symm w⟫_ℂ = 0 := by
    linear_combination -h0
  rw [mul_div_assoc', div_mul_eq_mul_div, mul_assoc, this, mul_zero, zero_div]

end

end GaloisForLFunctions.RHTower.DeckPointPair
