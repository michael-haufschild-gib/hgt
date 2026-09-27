import GaloisForLFunctions.RHTower.ThetaSieveBidirectionalCuspVariation
import Mathlib.NumberTheory.EulerProduct.Basic
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier
import Mathlib.Analysis.Complex.RemovableSingularity


/-!
# Finite theta Euler stages have a zero port and a growing-order pole port

For a finite set of primes `P`, the literal finite Euler theta source
`S_P = ∑_{n ≥ 1, all prime factors in P} a_n` has, for `Re w > -1/2`,
`L_P(w) = ∫ e^{wx} S_P(x) dx = G(w) Z_P(w + 1/2)`, `Z_P(s) = ∏_{p∈P} (1 - p^{-s})⁻¹`.

* Right critical port: `L_P(1/2) = 0`, `L_P'(1/2) = Z_P(1)/2`, `∏(1 - 1/p) L_P'(1/2) = 1/2`.
* Left reflected port: `s^{|P|} L_P(-1/2 + s) → -1/∏ log p` as `s ↓ 0`; `L_∅(-1/2) = -1`.
* The completed source has both reflected charges `1/2`.
* A meromorphic scalar making `R · L_P` holomorphic and nonzero at both ports has a simple pole at
  `+1/2` and a zero of exact order `|P|` at `-1/2`; this order is unbounded along any exhaustion.
-/

open MeasureTheory Set Filter Topology Complex

namespace RHTower

/-- The finite Euler theta source `S_P = ∑_{n ≥ 1, all prime factors in P} a_n`. -/
noncomputable def thetaEulerStageSource (P : Finset ℕ) (x : ℝ) : ℝ :=
  ∑' n : Nat.factoredNumbers P, thetaCuspSourceTerm x n

/-- The finite Euler product `Z_P(s) = ∏_{p∈P} (1 - p^{-s})⁻¹`. -/
noncomputable def thetaEulerStageZeta (P : Finset ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ P, (1 - (p : ℂ) ^ (-s))⁻¹

private theorem natCast_cpow_mul_coprime (s : ℂ) {m n : ℕ} (_ : m.Coprime n) :
    ((m * n : ℕ) : ℂ) ^ (-s) = (m : ℂ) ^ (-s) * (n : ℂ) ^ (-s) := by
  push_cast
  exact Complex.natCast_mul_natCast_cpow m n (-s)

private theorem norm_natCast_prime_pow_cpow {p : ℕ} (hp : p.Prime) (s : ℂ) (e : ℕ) :
    ‖(((p ^ e : ℕ) : ℂ) ^ (-s))‖ = ((p : ℝ) ^ (-s.re)) ^ e := by
  rw [Complex.norm_natCast_cpow_of_pos (pow_pos hp.pos e)]
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  simp only [neg_re]
  ring_nf

private theorem prime_pow_cpow_eq (p e : ℕ) (s : ℂ) :
    (((p ^ e : ℕ) : ℂ) ^ (-s)) = ((p : ℂ) ^ (-s)) ^ e := by
  rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

/-- The factored-number Dirichlet series of a finite prime set is its Euler product. -/
theorem hasSum_factoredNumbers_cpow (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {s : ℂ}
    (hs : 0 < s.re) :
    (Summable fun m : Nat.factoredNumbers P => ‖((m : ℕ) : ℂ) ^ (-s)‖) ∧
      HasSum (fun m : Nat.factoredNumbers P => ((m : ℕ) : ℂ) ^ (-s)) (thetaEulerStageZeta P s) := by
  have hlt : ∀ {p : ℕ}, p.Prime → (p : ℝ) ^ (-s.re) < 1 := fun hp =>
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  obtain ⟨hsum, hhas⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n : ℕ => ((n : ℕ) : ℂ) ^ (-s)) (by simp)
    (fun hmn => natCast_cpow_mul_coprime s hmn)
    (fun hp => by
      simp_rw [norm_natCast_prime_pow_cpow hp]
      exact summable_geometric_of_lt_one (by positivity) (hlt hp)) P
  refine ⟨hsum, ?_⟩
  have heq : (∏ p ∈ P with Nat.Prime p, ∑' (n : ℕ), (((p ^ n : ℕ) : ℂ) ^ (-s))) =
      thetaEulerStageZeta P s := by
    rw [Finset.filter_true_of_mem hP, thetaEulerStageZeta]
    apply Finset.prod_congr rfl
    intro p hp
    simp_rw [prime_pow_cpow_eq]
    rw [tsum_geometric_of_norm_lt_one]
    rw [Complex.norm_natCast_cpow_of_pos (hP p hp).pos]
    simpa using hlt (hP p hp)
  rw [heq] at hhas
  exact hhas


/-- Weighted absolute mass of an atom: `∫ e^{σx} |a_n(x)| dx = n^{-(σ+1/2)} ∫ e^{σx} |h(x)| dx`. -/
theorem integral_exp_mul_abs_thetaCuspSourceTerm (σ : ℝ) {n : ℕ} (hn : 0 < n) :
    (∫ x : ℝ, Real.exp (σ * x) * |thetaCuspSourceTerm x n|) =
      (n : ℝ) ^ (-(σ + 1 / 2)) * ∫ x : ℝ, Real.exp (σ * x) * |thetaCuspSourceTerm x 1| := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hform : ∀ x, |thetaCuspSourceTerm x n| =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * |thetaCuspSourceTerm (x - -Real.log n) 1| := by
    intro x
    rw [sub_neg_eq_add, ← abs_of_pos (Real.rpow_pos_of_pos hnR (-(1 / 2 : ℝ))), ← abs_mul,
      rpow_neg_half_mul_thetaCuspSourceTerm_add_log hn x 1, mul_one]
  simp_rw [hform]
  simp_rw [show ∀ x : ℝ, Real.exp (σ * x) * ((n : ℝ) ^ (-(1 / 2 : ℝ)) *
      |thetaCuspSourceTerm (x - -Real.log n) 1|) =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.exp (σ * x) * |thetaCuspSourceTerm (x - -Real.log n) 1|)
      from fun x => by ring]
  rw [integral_const_mul, integral_exp_mul_comp_sub σ (-Real.log n)
    (fun y => |thetaCuspSourceTerm y 1|), ← mul_assoc]
  congr 1
  rw [Real.rpow_def_of_pos hnR, Real.rpow_def_of_pos hnR, ← Real.exp_add]
  ring_nf

/-- **Finite Euler stage Mellin law (1).**  For `Re w > -1/2`,
`L_P(w) = G(w) Z_P(w + 1/2)`. -/
theorem integral_cexp_mul_thetaEulerStageSource (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (w : ℂ) (hw : -(1 / 2) < w.re) :
    Integrable (fun x : ℝ => Complex.exp (w * x) * (thetaEulerStageSource P x : ℂ)) ∧
      (∫ x : ℝ, Complex.exp (w * x) * (thetaEulerStageSource P x : ℂ)) =
        thetaAtomMellinFactor w * thetaEulerStageZeta P (w + 1 / 2) := by
  set F : Nat.factoredNumbers P → ℝ → ℂ := fun n x =>
    Complex.exp (w * x) * (thetaCuspSourceTerm x (n : ℕ) : ℂ)
  have hpos : ∀ n : Nat.factoredNumbers P, 0 < (n : ℕ) := fun n =>
    Nat.pos_of_ne_zero (Nat.mem_factoredNumbers.mp n.2).1
  have hint : ∀ n, Integrable (F n) := fun n =>
    integrable_cexp_mul_thetaCuspSourceTerm w (by linarith) n (hpos n)
  set C := ∫ x : ℝ, Real.exp (w.re * x) * |thetaCuspSourceTerm x 1|
  have hnorm : ∀ n : Nat.factoredNumbers P, (∫ x, ‖F n x‖) = ((n : ℕ) : ℝ) ^ (-(w.re + 1 / 2)) * C := by
    intro n
    rw [← integral_exp_mul_abs_thetaCuspSourceTerm w.re (hpos n)]
    apply integral_congr_ae
    filter_upwards with x
    simp only [F, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hre : 0 < ((w.re + 1 / 2 : ℝ) : ℂ).re := by simp; linarith
  have hsumnorm : Summable fun n : Nat.factoredNumbers P => ∫ x, ‖F n x‖ := by
    have h := (hasSum_factoredNumbers_cpow P hP hre).1
    simp_rw [hnorm]
    refine (h.mul_right C).congr (fun n => ?_)
    rw [Complex.norm_natCast_cpow_of_pos (hpos n)]
    simp
  have hre' : 0 < (w + 1 / 2).re := by simp; linarith
  have hsum := hasSum_integral_of_summable_integral_norm hint hsumnorm
  have htsum : ∀ x : ℝ, (∑' n, F n x) =
      Complex.exp (w * x) * (thetaEulerStageSource P x : ℂ) := by
    intro x
    simp only [F, thetaEulerStageSource]
    rw [Complex.ofReal_tsum, tsum_mul_left]
  have hvalue : HasSum (fun n : Nat.factoredNumbers P => ∫ x, F n x)
      (thetaAtomMellinFactor w * thetaEulerStageZeta P (w + 1 / 2)) := by
    have h := ((hasSum_factoredNumbers_cpow P hP hre').2).mul_left (thetaAtomMellinFactor w)
    refine h.congr_fun (fun n => ?_)
    simp only [F]
    rw [integral_cexp_mul_thetaCuspSourceTerm w (by linarith) n (hpos n)]
    ring
  refine ⟨?_, ?_⟩
  · have h := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm hint hsumnorm
    simpa only [htsum] using h
  · rw [← hvalue.tsum_eq, hsum.tsum_eq]
    apply integral_congr_ae
    filter_upwards with x
    exact (htsum x).symm


/-! ## The two ports -/

/-- The finite Euler stage transform `L_P(w) = ∫ e^{wx} S_P(x) dx`. -/
noncomputable def thetaEulerStageLaplace (P : Finset ℕ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (w * x) * (thetaEulerStageSource P x : ℂ)

/-- The nonvanishing Gamma factor `A(w) = Γ(w/2 + 5/4) π^{-(w/2+1/4)}`, `G(w) = (w - 1/2) A(w)`. -/
noncomputable def thetaAtomGammaFactorC (w : ℂ) : ℂ :=
  Complex.Gamma (w / 2 + 5 / 4) * (1 / (Real.pi : ℂ)) ^ (w / 2 + 1 / 4)

theorem thetaAtomMellinFactor_eq (w : ℂ) :
    thetaAtomMellinFactor w = (w - 1 / 2) * thetaAtomGammaFactorC w := by
  unfold thetaAtomMellinFactor thetaAtomGammaFactorC
  ring

theorem differentiableAt_thetaAtomGammaFactorC {w : ℂ} (hw : -(5 / 2) < w.re) :
    DifferentiableAt ℂ thetaAtomGammaFactorC w := by
  unfold thetaAtomGammaFactorC
  apply DifferentiableAt.mul
  · have hΓ : DifferentiableAt ℂ Complex.Gamma (w / 2 + 5 / 4) := by
      apply Complex.differentiableAt_Gamma
      intro m hm
      have := congrArg Complex.re hm
      simp at this
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact hΓ.comp w (by fun_prop)
  · exact DifferentiableAt.const_cpow (by fun_prop)
      (Or.inl (one_div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))

theorem analyticAt_thetaAtomGammaFactorC {w : ℂ} (hw : -(5 / 2) < w.re) :
    AnalyticAt ℂ thetaAtomGammaFactorC w := by
  apply DifferentiableOn.analyticAt (s := {z : ℂ | -(5 / 2) < z.re})
  · intro z hz
    exact (differentiableAt_thetaAtomGammaFactorC hz).differentiableWithinAt
  · exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw

theorem analyticAt_thetaAtomMellinFactor {w : ℂ} (hw : -(5 / 2) < w.re) :
    AnalyticAt ℂ thetaAtomMellinFactor w := by
  have h : thetaAtomMellinFactor = fun z => (z - 1 / 2) * thetaAtomGammaFactorC z := by
    funext z
    exact thetaAtomMellinFactor_eq z
  rw [h]
  exact (analyticAt_id.sub analyticAt_const).mul (analyticAt_thetaAtomGammaFactorC hw)

/-- `A(1/2) = Γ(3/2) π^{-1/2} = 1/2`. -/
theorem thetaAtomGammaFactorC_half : thetaAtomGammaFactorC (1 / 2) = 1 / 2 := by
  unfold thetaAtomGammaFactorC
  rw [show (1 / 2 : ℂ) / 2 + 5 / 4 = 1 / 2 + 1 by norm_num,
    Complex.Gamma_add_one _ (by norm_num), Complex.Gamma_one_half_eq,
    show (1 / 2 : ℂ) / 2 + 1 / 4 = 1 / 2 by norm_num]
  have hπ : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hinv : (1 / (Real.pi : ℂ)) = ((1 / Real.pi : ℝ) : ℂ) := by push_cast; rfl
  rw [hinv, mul_assoc, mul_comm ((Real.pi : ℂ) ^ (1 / 2 : ℂ)),
    ← Complex.mul_cpow_ofReal_nonneg (by positivity) hπ,
    show ((1 / Real.pi : ℝ) : ℂ) * (Real.pi : ℂ) = ((1 / Real.pi * Real.pi : ℝ) : ℂ) by push_cast; ring,
    one_div_mul_cancel Real.pi_ne_zero]
  simp

/-- `G(-1/2) = -Γ(1) = -1`. -/
theorem thetaAtomMellinFactor_neg_half : thetaAtomMellinFactor (-(1 / 2)) = -1 := by
  unfold thetaAtomMellinFactor
  rw [show (-(1 / 2) : ℂ) / 2 + 5 / 4 = 1 by norm_num, Complex.Gamma_one,
    show (-(1 / 2) : ℂ) / 2 + 1 / 4 = 0 by norm_num, Complex.cpow_zero]
  norm_num

theorem one_sub_natCast_cpow_neg_ne_zero {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    1 - (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  have hnorm := congrArg norm h1
  rw [Complex.norm_natCast_cpow_of_pos (by omega), norm_one] at hnorm
  have hpR : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have := Real.rpow_lt_one_of_one_lt_of_neg hpR (show (-s).re < 0 by simp; linarith)
  linarith

theorem differentiableAt_thetaEulerStageZeta (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ (thetaEulerStageZeta P) s := by
  have h : thetaEulerStageZeta P = ∏ p ∈ P, fun s : ℂ => (1 - (p : ℂ) ^ (-s))⁻¹ := by
    funext s
    simp [thetaEulerStageZeta, Finset.prod_apply]
  rw [h]
  apply DifferentiableAt.finsetProd
  intro p hp
  have hf : DifferentiableAt ℂ (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) s :=
    (differentiableAt_const _).sub (DifferentiableAt.const_cpow (by fun_prop)
      (Or.inl (by exact_mod_cast (hP p hp).ne_zero)))
  exact hf.inv (one_sub_natCast_cpow_neg_ne_zero (hP p hp).two_le hs)

theorem thetaEulerStageLaplace_eq (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {w : ℂ}
    (hw : -(1 / 2) < w.re) :
    thetaEulerStageLaplace P w = thetaAtomMellinFactor w * thetaEulerStageZeta P (w + 1 / 2) :=
  (integral_cexp_mul_thetaEulerStageSource P hP w hw).2

/-- **Right critical port (2).**  `L_P(1/2) = 0`. -/
theorem thetaEulerStageLaplace_half (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    thetaEulerStageLaplace P (1 / 2) = 0 := by
  rw [thetaEulerStageLaplace_eq P hP (by norm_num), thetaAtomMellinFactor_eq]
  ring

/-- **Right critical port (2).**  `L_P'(1/2) = (1/2) Z_P(1)`. -/
theorem hasDerivAt_thetaEulerStageLaplace_half (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    HasDerivAt (thetaEulerStageLaplace P) ((1 / 2) * thetaEulerStageZeta P 1) (1 / 2) := by
  have hev : thetaEulerStageLaplace P =ᶠ[𝓝 (1 / 2)]
      fun w => ((w - 1 / 2) * thetaAtomGammaFactorC w) * thetaEulerStageZeta P (w + 1 / 2) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show -(1 / 2 : ℝ) < (1 / 2 : ℂ).re by norm_num)] with w hw
    rw [thetaEulerStageLaplace_eq P hP hw, thetaAtomMellinFactor_eq]
  have hA := (differentiableAt_thetaAtomGammaFactorC (w := 1 / 2) (by norm_num)).hasDerivAt
  have hG := ((hasDerivAt_id (1 / 2 : ℂ)).sub_const (1 / 2)).mul hA
  have hZ := ((differentiableAt_thetaEulerStageZeta P hP (s := 1 / 2 + 1 / 2)
    (by norm_num)).hasDerivAt).comp_add_const (1 / 2 : ℂ) (1 / 2)
  have h := hG.mul hZ
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [id, sub_self, zero_mul, add_zero, one_mul, thetaAtomGammaFactorC_half]
  norm_num

/-- **Normalized first jet (2).**  `∏_{p∈P} (1 - 1/p) L_P'(1/2) = 1/2`. -/
theorem prod_one_sub_inv_mul_thetaEulerStage_jet (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, (1 - 1 / (p : ℂ))) * ((1 / 2) * thetaEulerStageZeta P 1) = 1 / 2 := by
  have hZ : (∏ p ∈ P, (1 - 1 / (p : ℂ))) * thetaEulerStageZeta P 1 = 1 := by
    rw [thetaEulerStageZeta, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    rw [Complex.cpow_neg_one, one_div]
    have hne : 1 - (p : ℂ)⁻¹ ≠ 0 := by
      intro h
      rw [sub_eq_zero, eq_comm, inv_eq_one] at h
      exact (hP p hp).one_lt.ne' (by exact_mod_cast h)
    exact mul_inv_cancel₀ hne
  linear_combination (1 / 2 : ℂ) * hZ


/-! ## The left reflected port -/

private theorem hasDerivAt_one_sub_natCast_cpow_neg {p : ℕ} (hp : 0 < p) (a z : ℂ) :
    HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-(z + a)))
      ((p : ℂ) ^ (-(z + a)) * (Real.log p : ℂ)) z := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have h := ((hasDerivAt_id z).add_const a).neg.const_cpow (c := (p : ℂ)) (Or.inl hp')
  have h2 := h.const_sub 1
  refine h2.congr_deriv ?_
  rw [Complex.natCast_log]
  simp

/-- Each Euler factor has the slope `(1 - p^{-t})/t → log p` at the left port. -/
private theorem tendsto_mul_inv_one_sub_natCast_cpow {p : ℕ} (hp : p.Prime) :
    Tendsto (fun t : ℝ => (t : ℂ) * (1 - (p : ℂ) ^ (-(t : ℂ)))⁻¹) (𝓝[>] 0)
      (𝓝 ((Real.log p : ℂ))⁻¹) := by
  have hd := (hasDerivAt_one_sub_natCast_cpow_neg hp.pos 0 ((0 : ℝ) : ℂ)).comp_ofReal
  have hslope := hd.tendsto_slope_zero_right
  have hlog : (Real.log p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  simp only [Complex.ofReal_zero, zero_add, add_zero, neg_zero, Complex.cpow_zero, one_mul,
    sub_self, sub_zero] at hslope
  have hinv := hslope.inv₀ hlog
  refine hinv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  rw [Complex.real_smul, mul_inv, Complex.ofReal_inv, inv_inv]

/-- **Left reflected port (3).**  For nonempty `P`,
`lim_{s↓0} s^{|P|} L_P(-1/2 + s) = -1 / ∏_{p∈P} log p`. -/
theorem tendsto_pow_mul_thetaEulerStageLaplace_left (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ P.card * thetaEulerStageLaplace P (-(1 / 2) + t)) (𝓝[>] 0)
      (𝓝 (-(∏ p ∈ P, (Real.log p : ℂ))⁻¹)) := by
  have hG : Tendsto (fun t : ℝ => thetaAtomMellinFactor (-(1 / 2) + t)) (𝓝[>] 0)
      (𝓝 (-1)) := by
    rw [← thetaAtomMellinFactor_neg_half]
    have hc := (analyticAt_thetaAtomMellinFactor (w := -(1 / 2)) (by norm_num)).continuousAt
    have hlin : Tendsto (fun t : ℝ => -(1 / 2 : ℂ) + t) (𝓝[>] 0) (𝓝 (-(1 / 2))) := by
      have : Continuous (fun t : ℝ => -(1 / 2 : ℂ) + t) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    exact hc.tendsto.comp hlin
  have hprod := tendsto_finsetProd P fun p hp => tendsto_mul_inv_one_sub_natCast_cpow (hP p hp)
  have h := hG.mul hprod
  rw [neg_one_mul] at h
  rw [← Finset.prod_inv_distrib]
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [thetaEulerStageLaplace_eq P hP (by simp; linarith [show (0 : ℝ) < t from ht]),
    thetaEulerStageZeta, Finset.prod_mul_distrib, Finset.prod_const,
    show -(1 / 2 : ℂ) + t + 1 / 2 = t by ring]
  ring

theorem thetaEulerStageSource_empty (x : ℝ) :
    thetaEulerStageSource ∅ x = thetaCuspSourceTerm x 1 := by
  rw [thetaEulerStageSource, tsum_subtype, Nat.factoredNumbers_empty, tsum_eq_single 1]
  · simp
  · intro n hn
    simp [hn]

/-- **Left port of the empty stage (3).**  `L_∅(-1/2) = -1`. -/
theorem thetaEulerStageLaplace_empty_neg_half : thetaEulerStageLaplace ∅ (-(1 / 2)) = -1 := by
  unfold thetaEulerStageLaplace
  simp_rw [thetaEulerStageSource_empty]
  rw [integral_cexp_mul_thetaSeedAtom _ (by norm_num), thetaAtomMellinFactor_neg_half]

/-- **Completed source (4).**  Both reflected critical charges equal `1/2`. -/
theorem integral_exp_neg_half_mul_thetaCuspFullSource_eq_half :
    (∫ x : ℝ, Real.exp ((-(1 / 2) : ℝ) * x) * thetaCuspFullSource x) = 1 / 2 := by
  calc
    (∫ x : ℝ, Real.exp ((-(1 / 2) : ℝ) * x) * thetaCuspFullSource x) =
        ∫ x : ℝ, (fun y : ℝ => Real.exp ((1 / 2 : ℝ) * y) * thetaCuspFullSource y) (-x) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [thetaCuspFullSource_neg]
      ring_nf
    _ = ∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * thetaCuspFullSource x :=
      integral_neg_eq_self (fun y : ℝ => Real.exp ((1 / 2 : ℝ) * y) * thetaCuspFullSource y) volume
    _ = 1 / 2 := integral_exp_half_mul_thetaCuspFullSource_eq_half

/-! ## Divisor price of a scalar renormalization -/

/-- The meromorphic continuation `G(w) Z_P(w + 1/2)` of the finite Euler stage transform. -/
noncomputable def thetaEulerStageLaplaceExt (P : Finset ℕ) (w : ℂ) : ℂ :=
  thetaAtomMellinFactor w * thetaEulerStageZeta P (w + 1 / 2)

theorem thetaEulerStageLaplace_eq_ext (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {w : ℂ}
    (hw : -(1 / 2) < w.re) : thetaEulerStageLaplace P w = thetaEulerStageLaplaceExt P w :=
  thetaEulerStageLaplace_eq P hP hw

private theorem analyticAt_zeta_shift (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {w : ℂ}
    (hw : -(1 / 2) < w.re) : AnalyticAt ℂ (fun z => thetaEulerStageZeta P (z + 1 / 2)) w := by
  apply DifferentiableOn.analyticAt (s := {z : ℂ | -(1 / 2) < z.re})
  · intro z hz
    exact ((differentiableAt_thetaEulerStageZeta P hP (s := z + 1 / 2)
      (by simp; linarith [show -(1 / 2) < z.re from hz])).comp z
        (differentiableAt_id.add_const _)).differentiableWithinAt
  · exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw

theorem thetaEulerStageZeta_ne_zero (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {s : ℂ}
    (hs : 0 < s.re) : thetaEulerStageZeta P s ≠ 0 := by
  rw [thetaEulerStageZeta, Finset.prod_ne_zero_iff]
  intro p hp
  exact inv_ne_zero (one_sub_natCast_cpow_neg_ne_zero (hP p hp).two_le hs)

/-- The right port is a simple zero of the continued transform. -/
theorem meromorphicOrderAt_thetaEulerStageLaplaceExt_half (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    meromorphicOrderAt (thetaEulerStageLaplaceExt P) (1 / 2) = 1 := by
  have hA := analyticAt_thetaAtomGammaFactorC (w := 1 / 2) (by norm_num)
  have hZ := analyticAt_zeta_shift P hP (w := 1 / 2) (by norm_num)
  have hG := analyticAt_thetaAtomMellinFactor (w := 1 / 2) (by norm_num)
  have hmer : MeromorphicAt (thetaEulerStageLaplaceExt P) (1 / 2) :=
    (hG.mul hZ).meromorphicAt
  have := (meromorphicOrderAt_eq_int_iff hmer (n := 1)).mpr
    ⟨fun z => thetaAtomGammaFactorC z * thetaEulerStageZeta P (z + 1 / 2), hA.mul hZ, ?_, ?_⟩
  · exact_mod_cast this
  · show thetaAtomGammaFactorC (1 / 2) * thetaEulerStageZeta P (1 / 2 + 1 / 2) ≠ 0
    rw [thetaAtomGammaFactorC_half]
    exact mul_ne_zero (by norm_num) (thetaEulerStageZeta_ne_zero P hP (by norm_num))
  · filter_upwards with z
    rw [thetaEulerStageLaplaceExt, thetaAtomMellinFactor_eq, zpow_one, smul_eq_mul]
    ring


/-- The shifted Euler factor `f_p(z) = 1 - p^{-(z+1/2)}`, simple zero at `-1/2`. -/
private noncomputable def eulerFactorShift (p : ℕ) (z : ℂ) : ℂ := 1 - (p : ℂ) ^ (-(z + 1 / 2))

private theorem eulerFactorShift_neg_half (p : ℕ) : eulerFactorShift p (-(1 / 2)) = 0 := by
  simp [eulerFactorShift]

private theorem differentiable_eulerFactorShift {p : ℕ} (hp : 0 < p) :
    Differentiable ℂ (eulerFactorShift p) := fun z =>
  (hasDerivAt_one_sub_natCast_cpow_neg hp (1 / 2) z).differentiableAt

private theorem analyticAt_dslope_eulerFactorShift {p : ℕ} (hp : 0 < p) (z : ℂ) :
    AnalyticAt ℂ (dslope (eulerFactorShift p) (-(1 / 2))) z := by
  have hd : DifferentiableOn ℂ (dslope (eulerFactorShift p) (-(1 / 2))) Set.univ :=
    (Complex.differentiableOn_dslope Filter.univ_mem).mpr
      (differentiable_eulerFactorShift hp).differentiableOn
  exact hd.analyticAt Filter.univ_mem

private theorem dslope_eulerFactorShift_same {p : ℕ} (hp : p.Prime) :
    dslope (eulerFactorShift p) (-(1 / 2)) (-(1 / 2)) = (Real.log p : ℂ) := by
  have h := hasDerivAt_one_sub_natCast_cpow_neg hp.pos (1 / 2) (-(1 / 2))
  rw [dslope_same, show eulerFactorShift p = fun z => 1 - (p : ℂ) ^ (-(z + 1 / 2)) from rfl,
    h.deriv]
  simp

private theorem eulerFactorShift_eq_mul_dslope (p : ℕ) (z : ℂ) :
    eulerFactorShift p z = (z + 1 / 2) * dslope (eulerFactorShift p) (-(1 / 2)) z := by
  have h := sub_smul_dslope (eulerFactorShift p) (-(1 / 2)) z
  rw [eulerFactorShift_neg_half, sub_zero, smul_eq_mul, sub_neg_eq_add] at h
  exact h.symm

private theorem thetaEulerStageLaplaceExt_eq_prod (P : Finset ℕ) (z : ℂ) :
    thetaEulerStageLaplaceExt P z =
      thetaAtomMellinFactor z * ∏ p ∈ P, (eulerFactorShift p z)⁻¹ := by
  rfl

theorem meromorphicAt_thetaEulerStageLaplaceExt_neg_half (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) : MeromorphicAt (thetaEulerStageLaplaceExt P) (-(1 / 2)) := by
  have hG := analyticAt_thetaAtomMellinFactor (w := -(1 / 2)) (by norm_num)
  have hprod : MeromorphicAt (∏ p ∈ P, fun z => (eulerFactorShift p z)⁻¹) (-(1 / 2)) :=
    MeromorphicAt.prod fun p hp =>
      ((differentiable_eulerFactorShift (hP p hp).pos).analyticAt _).meromorphicAt.inv
  have heq : thetaEulerStageLaplaceExt P =
      thetaAtomMellinFactor * ∏ p ∈ P, fun z => (eulerFactorShift p z)⁻¹ := by
    funext z
    simp [thetaEulerStageLaplaceExt_eq_prod, Finset.prod_apply]
  rw [heq]
  exact hG.meromorphicAt.mul hprod

/-- The left reflected port is a pole of exact order `|P|` of the continued transform. -/
theorem meromorphicOrderAt_thetaEulerStageLaplaceExt_neg_half (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    meromorphicOrderAt (thetaEulerStageLaplaceExt P) (-(1 / 2)) = -(P.card : ℤ) := by
  have hG := analyticAt_thetaAtomMellinFactor (w := -(1 / 2)) (by norm_num)
  have hmer := meromorphicAt_thetaEulerStageLaplaceExt_neg_half P hP
  have hφ : ∀ p ∈ P, AnalyticAt ℂ (fun z => (dslope (eulerFactorShift p) (-(1 / 2)) z)⁻¹)
      (-(1 / 2)) := fun p hp =>
    (analyticAt_dslope_eulerFactorShift (hP p hp).pos _).inv (by
      rw [dslope_eulerFactorShift_same (hP p hp)]
      exact Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast (hP p hp).one_lt)).ne')
  have hg : AnalyticAt ℂ (fun z => thetaAtomMellinFactor z *
      ∏ p ∈ P, (dslope (eulerFactorShift p) (-(1 / 2)) z)⁻¹) (-(1 / 2)) := by
    apply hG.mul
    have heq : (fun z => ∏ p ∈ P, (dslope (eulerFactorShift p) (-(1 / 2)) z)⁻¹) =
        ∏ p ∈ P, fun z => (dslope (eulerFactorShift p) (-(1 / 2)) z)⁻¹ := by
      funext z
      simp [Finset.prod_apply]
    rw [heq]
    exact Finset.analyticAt_prod P hφ
  have := (meromorphicOrderAt_eq_int_iff hmer (n := -(P.card : ℤ))).mpr
    ⟨_, hg, ?_, ?_⟩
  · exact this
  · show thetaAtomMellinFactor (-(1 / 2)) *
        ∏ p ∈ P, (dslope (eulerFactorShift p) (-(1 / 2)) (-(1 / 2)))⁻¹ ≠ 0
    rw [thetaAtomMellinFactor_neg_half, Finset.prod_congr rfl
      (fun p hp => by rw [dslope_eulerFactorShift_same (hP p hp)])]
    refine mul_ne_zero (by norm_num) (Finset.prod_ne_zero_iff.mpr fun p hp => inv_ne_zero ?_)
    exact Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast (hP p hp).one_lt)).ne'
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z + 1 / 2 ≠ 0 := by
      intro h
      apply hz
      simp only [Set.mem_singleton_iff]
      linear_combination h
    rw [thetaEulerStageLaplaceExt_eq_prod, smul_eq_mul, sub_neg_eq_add, zpow_neg, zpow_natCast]
    simp_rw [eulerFactorShift_eq_mul_dslope _ z, mul_inv, Finset.prod_mul_distrib,
      Finset.prod_const]
    ring

private theorem withTop_eq_of_add_eq_zero {a : WithTop ℤ} {m : ℤ} (h : a + (m : WithTop ℤ) = 0) :
    a = ((-m : ℤ) : WithTop ℤ) := by
  induction a using WithTop.recTopCoe with
  | top => simp at h
  | coe n =>
    have : n + m = 0 := by exact_mod_cast h
    congr 1
    omega

/-- **Divisor price of scalar renormalization.**  If a meromorphic scalar `R` makes `R · L_P`
holomorphic and nonzero at both ports, then `R` has a simple pole at `+1/2` and a zero of exact
order `|P|` at `-1/2`. -/
theorem thetaEulerStage_divisor_price (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (R : ℂ → ℂ)
    (hR₁ : MeromorphicAt R (1 / 2)) (hR₂ : MeromorphicAt R (-(1 / 2)))
    (h₁ : ∃ g : ℂ → ℂ, AnalyticAt ℂ g (1 / 2) ∧ g (1 / 2) ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] (1 / 2), R z * thetaEulerStageLaplaceExt P z = g z)
    (h₂ : ∃ g : ℂ → ℂ, AnalyticAt ℂ g (-(1 / 2)) ∧ g (-(1 / 2)) ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] (-(1 / 2)), R z * thetaEulerStageLaplaceExt P z = g z) :
    meromorphicOrderAt R (1 / 2) = -1 ∧ meromorphicOrderAt R (-(1 / 2)) = P.card := by
  have hE₁ : MeromorphicAt (thetaEulerStageLaplaceExt P) (1 / 2) :=
    ((analyticAt_thetaAtomMellinFactor (w := 1 / 2) (by norm_num)).mul
      (analyticAt_zeta_shift P hP (w := 1 / 2) (by norm_num))).meromorphicAt
  have hE₂ := meromorphicAt_thetaEulerStageLaplaceExt_neg_half P hP
  have horder : ∀ x : ℂ, MeromorphicAt R x → MeromorphicAt (thetaEulerStageLaplaceExt P) x →
      (∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧ g x ≠ 0 ∧
        ∀ᶠ z in 𝓝[≠] x, R z * thetaEulerStageLaplaceExt P z = g z) →
      meromorphicOrderAt R x + meromorphicOrderAt (thetaEulerStageLaplaceExt P) x = 0 := by
    intro x hR hE ⟨g, hga, hg0, hgeq⟩
    rw [← meromorphicOrderAt_mul hR hE]
    have := (meromorphicOrderAt_eq_int_iff (hR.mul hE) (n := 0)).mpr ⟨g, hga, hg0, by
      filter_upwards [hgeq] with z hz
      simp [hz]⟩
    exact_mod_cast this
  constructor
  · have h := horder _ hR₁ hE₁ h₁
    rw [meromorphicOrderAt_thetaEulerStageLaplaceExt_half P hP] at h
    have := withTop_eq_of_add_eq_zero (m := 1) (by exact_mod_cast h)
    exact_mod_cast this
  · have h := horder _ hR₂ hE₂ h₂
    rw [meromorphicOrderAt_thetaEulerStageLaplaceExt_neg_half P hP] at h
    have := withTop_eq_of_add_eq_zero (m := -(P.card : ℤ)) (by exact_mod_cast h)
    simpa using this

/-- The required left zero order grows without bound along every exhaustion of the primes. -/
theorem PrimeExhaustion.tendsto_card {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S) :
    Tendsto (fun j => (S j).card) atTop atTop := by
  rw [tendsto_atTop]
  intro N
  obtain ⟨M, hM⟩ : ∃ M, N ≤ ((Finset.range M).filter Nat.Prime).card := by
    refine ⟨Nat.nth Nat.Prime N + 1, ?_⟩
    have : ((Finset.range (Nat.nth Nat.Prime N + 1)).filter Nat.Prime) =
        Nat.primesBelow (Nat.nth Nat.Prime N + 1) := rfl
    rw [this, Nat.primesBelow_card_eq_primeCounting']
    calc N = Nat.primeCounting' (Nat.nth Nat.Prime N) := (Nat.primeCounting'_nth_eq N).symm
      _ ≤ Nat.primeCounting' (Nat.nth Nat.Prime N + 1) :=
        Nat.monotone_primeCounting' (Nat.le_succ _)
  have hev : ∀ᶠ j in atTop, ∀ p ∈ (Finset.range M).filter Nat.Prime, p ∈ S j := by
    rw [Filter.eventually_all_finset]
    intro p hp
    exact hS.eventually_mem p (Finset.mem_filter.mp hp).2
  filter_upwards [hev] with j hj
  exact hM.trans (Finset.card_le_card hj)

end RHTower
