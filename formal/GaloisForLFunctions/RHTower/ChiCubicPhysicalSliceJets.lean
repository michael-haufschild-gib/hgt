import GaloisForLFunctions.RHTower.ChiCubicPhysicalAmplitudeBudgets
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# All physical slice jets at the actual moving edge scale

The full normalized slice's already-proved derivative mass controls each
pointwise jet by the fundamental theorem of calculus from outside its
support. Exact dilation and the literal logarithmic slice identity then
pay EVERY physical derivative by H^(-n)/log N for EVERY admissible edge
width H. No derivative budget is assumed.

These are inputs to normal transport for the complete cubic exterior.
They do not by themselves prove its signed arithmetic cancellation.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace RHTower.BAGTrace

private theorem slice_jet_off (n : ℕ)
    (δ : {r : ℝ // r ∈ Ioo (0 : ℝ) (1/2)})
    (h : {r : ℝ // r ∈ Icc (0 : ℝ) 1}) {x : ℝ} (hx : x ∉ Icc (1 : ℝ) 2) :
    iteratedDeriv n (bagCubicNormalizedSlice δ.1 h.1) x = 0 := by
  have heq : bagCubicNormalizedSlice δ.1 h.1 =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy
    exact (bagCubicNormalizedSlice_properties δ h).2 y hy
  rw [heq.iteratedDeriv_eq]
  simp only [iteratedDeriv_const, ite_self]

/-- The actual moving slice has pointwise jets at the exact edge scale.
The constants are independent of BOTH cutoff width and logarithmic parameter. -/
theorem bagCubicNormalizedSlice_uniform_jets (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : {r : ℝ // r ∈ Ioo (0 : ℝ) (1/2)},
      ∀ h : {r : ℝ // r ∈ Icc (0 : ℝ) 1}, ∀ x : ℝ,
        ‖iteratedDeriv n (bagCubicNormalizedSlice δ.1 h.1) x‖ ≤ C / δ.1^n := by
  obtain ⟨C,hC,hb⟩ := bagCubicNormalizedSlice_derivative_budgets (n+1)
  refine ⟨C,hC,fun δ h x => ?_⟩
  by_cases hx : x ∈ Icc (1 : ℝ) 2
  · let f := bagCubicNormalizedSlice δ.1 h.1
    have hf : ContDiff ℝ ∞ f := (bagCubicNormalizedSlice_properties δ h).1
    have hd (t : ℝ) : HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n+1) f t) t := by
      simpa only [iteratedDeriv_succ] using
        (hf.differentiable_iteratedDeriv n (by
          exact_mod_cast (show (n : ℕ∞) < ⊤ from WithTop.coe_lt_top n)) t).hasDerivAt
    have hc : Continuous (iteratedDeriv (n+1) f) :=
      hf.continuous_iteratedDeriv (n+1) (by
        exact_mod_cast (le_top : ((n+1 : ℕ) : ℕ∞) ≤ ⊤))
    have hzero : iteratedDeriv n f 0 = 0 := slice_jet_off n δ h (by norm_num)
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hd t) (hc.intervalIntegrable 0 x)
    rw [hzero, sub_zero] at he
    calc
      _ = ‖∫ t in (0 : ℝ)..x, iteratedDeriv (n+1) f t‖ := congrArg norm he.symm
      _ ≤ ∫ t in (0 : ℝ)..x, ‖iteratedDeriv (n+1) f t‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith [hx.1])
      _ = ∫ t in Ioc (0 : ℝ) x, ‖iteratedDeriv (n+1) f t‖ :=
        intervalIntegral.integral_of_le (by linarith [hx.1])
      _ ≤ ∫ t : ℝ, ‖iteratedDeriv (n+1) f t‖ :=
        setIntegral_le_integral (hb δ h).1 (Eventually.of_forall (fun t => norm_nonneg _))
      _ ≤ C / δ.1^n := by simpa only [Nat.add_sub_cancel] using (hb δ h).2
  · rw [slice_jet_off n δ h hx, norm_zero]
    exact div_nonneg hC.le (pow_nonneg δ.2.1.le _)

/-- Every physical derivative is paid by the ACTUAL absolute edge width H,
including all logarithmic factors. No uniform-jet premise is assumed. -/
theorem bagCubicControlledSlice_uniform_jets (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : {r : ℝ // Real.exp 1 ≤ r},
      ∀ H : {r : ℝ // r ∈ Ioo (0 : ℝ) (N.1/2)}, ∀ x : ℝ,
        ‖iteratedDeriv n (bagCubicMellinSliceValue N.1
          (bagCubicControlledBandCutoff N.1 H.1) 0) x‖ ≤
            C / (Real.log N.1 * H.1^n) := by
  obtain ⟨C,hC,hb⟩ := bagCubicNormalizedSlice_uniform_jets n
  refine ⟨C,hC,fun N H x => ?_⟩
  have hN1 : 1 < N.1 := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) N.2
  have hN0 : 0 < N.1 := lt_trans zero_lt_one hN1
  have hL : 0 < Real.log N.1 := Real.log_pos hN1
  have hL1 : 1 ≤ Real.log N.1 := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) N.2
  let δ : {r : ℝ // r ∈ Ioo (0 : ℝ) (1/2)} :=
    ⟨H.1/N.1,div_pos H.2.1 hN0,(div_lt_iff₀ hN0).mpr (by linarith only [H.2.2])⟩
  let h : {r : ℝ // r ∈ Icc (0 : ℝ) 1} :=
    ⟨1/Real.log N.1,div_nonneg zero_le_one hL.le,(div_le_iff₀ hL).mpr (by simpa using hL1)⟩
  let F := bagCubicNormalizedSlice δ.1 h.1
  have hf : ContDiff ℝ (n : ℕ) F :=
    (bagCubicNormalizedSlice_properties δ h).1.of_le (by
      exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have heq : bagCubicMellinSliceValue N.1 (bagCubicControlledBandCutoff N.1 H.1) 0 =
      fun y : ℝ => F ((1/N.1)*y)/(Real.log N.1 : ℂ) := by
    funext y
    have he := bagCubicNormalizedSlice_eq_actual ⟨N.1,hN1⟩ H (y/N.1)
    rw [show N.1*(y/N.1)=y by field_simp] at he
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hL.ne')).mpr
    simpa only [F, δ, h, one_div, div_eq_mul_inv, mul_one, one_mul, mul_comm] using he
  rw [heq, iteratedDeriv_div_const, iteratedDeriv_comp_const_smul hf]
  simp only [norm_div, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (div_nonneg zero_le_one hN0.le) n),
    Complex.norm_of_nonneg hL.le]
  calc
    _ ≤ ((1/N.1)^n * (C / δ.1^n)) / Real.log N.1 := by
      gcongr
      exact hb δ h ((1/N.1)*x)
    _ = C / (Real.log N.1 * H.1^n) := by
      dsimp only [δ]
      rw [div_pow, div_pow, one_pow]
      field_simp

end RHTower.BAGTrace
