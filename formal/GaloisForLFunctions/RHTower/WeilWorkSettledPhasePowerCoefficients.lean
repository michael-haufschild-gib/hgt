import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticForwardCoefficients

/-!
# Literal complex powers of a full-positive source

The absolutely convergent original logarithm fixes the branch. Its Dirichlet
exponential obeys an exact logarithmic convolution for every complex power.
-/

open Complex Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower.WeilWorkSettledPhase

/-- Dirichlet coefficients of the complex power fixed by the original logarithm. -/
def powerCoeff (lam : ℕ → ℝ) (z : ℂ) : ℕ → ℂ :=
  dirichletExp (z • logZetaCoeff (fun n => if 2 ≤ n then lam n else 0))

@[simp] theorem powerCoeff_zero (lam : ℕ → ℝ) (z : ℂ) : powerCoeff lam z 0 = 0 :=
  dirichletExp_zero

@[simp] theorem powerCoeff_one (lam : ℕ → ℝ) (z : ℂ) : powerCoeff lam z 1 = 1 := by
  apply dirichletExp_one <;> simp [logZetaCoeff]

/-- The literal power series converges absolutely on the original half-plane. -/
theorem powerCoeff_LSeries {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (z : ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (powerCoeff lam z) s ∧
      LSeries (powerCoeff lam z) s = cexp
        (z * LSeries (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0)) s) := by
  have hH := WeilSpectral.herglotzWeilPositive_of_weilPositiveFull hW
  have hf : LSeriesSummable (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0)) s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      ((abscissaOfAbsConv_logZetaCoeff_le hH.summable).trans_lt (by exact_mod_cast hs))
  simpa only [powerCoeff, LSeries_smul] using
    LSeries_dirichletExp (by simp [logZetaCoeff]) (by simp [logZetaCoeff]) (hf.smul z)

/-- Logarithmic differentiation preserves the full signed arithmetic source. -/
theorem powerCoeff_log_convolution {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (z : ℂ) (n : ℕ) :
    z * LSeries.convolution (WeilHerglotz.lamC lam) (powerCoeff lam z) n =
      (Real.log n : ℂ) * powerCoeff lam z n := by
  have hH := WeilSpectral.herglotzWeilPositive_of_weilPositiveFull hW
  have ha : LSeries.abscissaOfAbsConv (powerCoeff lam z) ≤ 1 := by
    have h := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
      (fun y hy => (powerCoeff_LSeries hW z (s := y) (by simpa using hy)).1)
    exact_mod_cast h
  have hlog : LSeries.abscissaOfAbsConv (LSeries.logMul (powerCoeff lam z)) < ⊤ := by
    rw [LSeries.abscissaOfAbsConv_logMul]
    exact ha.trans_lt (EReal.coe_lt_top 1)
  have hconv : LSeries.abscissaOfAbsConv
      (z • LSeries.convolution (WeilHerglotz.lamC lam) (powerCoeff lam z)) < ⊤ := by
    have hLam : LSeriesSummable (WeilHerglotz.lamC lam) 2 :=
      WeilHerglotz.summable_term_lamC hW (by norm_num)
    have h := (hLam.convolution (powerCoeff_LSeries hW z (s := 2) (by norm_num)).1).smul z
    exact h.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)
  have hid : (fun x : ℝ => LSeries
      (z • LSeries.convolution (WeilHerglotz.lamC lam) (powerCoeff lam z)) x) =ᶠ[atTop]
      fun x => LSeries (LSeries.logMul (powerCoeff lam z)) x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx' : 1 < (x : ℂ).re := by simpa using hx
    have hd := ((hasDerivAt_LSeries_logZetaCoeff hH.summable (by simp) hx').const_mul z).cexp
    have heq : LSeries (powerCoeff lam z) =ᶠ[nhds (x : ℂ)]
        fun s => cexp (z * LSeries (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0)) s) := by
      filter_upwards [isOpen_lt continuous_const continuous_re |>.mem_nhds hx'] with s hs
      exact (powerCoeff_LSeries hW z hs).2
    have hd' := hd.congr_of_eventuallyEq heq
    have hd'' := LSeries_hasDerivAt (s := (x : ℂ))
      (ha.trans_lt (by exact_mod_cast hx'))
    have hv := hd'.unique hd''
    rw [LSeries_smul, LSeries_convolution' (WeilHerglotz.summable_term_lamC hW hx')
      (powerCoeff_LSeries hW z hx').1, (powerCoeff_LSeries hW z hx').2]
    have hh := neg_injective (by simpa only [mul_neg] using hv)
    change z * (LSeries (fun n => ((if 2 ≤ n then lam n else 0 : ℝ) : ℂ)) x *
      cexp (z * LSeries (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0)) x)) = _
    rw [← hh]
    ring
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h := LSeries.eq_of_LSeries_eventually_eq hconv hlog hid hn.ne'
    simpa only [Pi.smul_apply, smul_eq_mul, LSeries.logMul, ← Complex.ofReal_natCast,
      Complex.ofReal_log (Nat.cast_nonneg n)] using h

end RHTower.WeilWorkSettledPhase
