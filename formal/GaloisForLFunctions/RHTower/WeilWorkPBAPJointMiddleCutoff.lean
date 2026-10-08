import GaloisForLFunctions.RHTower.WeilWorkPBAPJointGrowingOrder
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointFixedCutoff
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointLogQuadrature

/-!
# The actual middle-frequency cutoff discrepancy

The growing-order schedule pays Abel variation for the fixed auxiliary
cutoff. Exact phase conjugacy handles both signs of the frequency. The
continuous Fourier term is exponentially small above the middle threshold.
Thus the literal complex grid-minus-integral error has a source-independent
majorant, and its exact hyperbolic pole factor costs o(L) when c log 2 < 1.

All interval, derivative and frequency budgets are discharged for the
actual width. This closes the middle band of MC6, not its all-frequency
energy certificate or full PBAP.
-/

open Real Set Filter Topology MeasureTheory
noncomputable section
namespace RHTower.WeilWorkPBAP

private theorem middle_weight_cost {N W C G H n : ℝ}
    (hN : 0 < N) (hW : 0 < W) (hW1 : W ≤ 1) (hC : 0 < C)
    (hG : 0 < G) (hH0 : 0 ≤ H) (hn : N/2 ≤ n) (hH : H ≤ G*N*W) :
    H*(H*((C/W+C)/n^2)+C/n) ≤ C*G*(8*G+2)*W := by
  have hn0 : 0 < n := (by positivity : (0:ℝ) < N/2).trans_le hn
  have hcoeff : C/W+C ≤ 2*C/W := by
    have hh : C ≤ C/W := (le_div_iff₀ hW).mpr (by nlinarith)
    calc
      _ ≤ C/W+C/W := add_le_add le_rfl hh
      _ = _ := by ring
  have hterm : H*((C/W+C)/n^2) ≤ 8*C*G/N := by
    calc
      _ ≤ (G*N*W)*((2*C/W)/(N/2)^2) := by gcongr
      _ = _ := by field_simp; ring
  have hend : C/n ≤ 2*C/N := by
    calc
      _ ≤ C/(N/2) := div_le_div_of_nonneg_left hC.le (by positivity) hn
      _ = _ := by ring
  calc
    _ ≤ (G*N*W)*(8*C*G/N+2*C/N) := by gcongr
    _ = _ := by field_simp

/-- The fixed cutoff pays its own Abel variation, uniformly on the actual growing middle band. -/
theorem eventually_jointFixedCutoff_middle_cpow :
    ∃ C > 0, ∀ (b c : ℝ), 0 < b → 0 < c →
      ∀ᶠ L : ℝ in atTop,
        let W := jointUniformWidth b L
        let n := ⌊exp L*exp (-2*W)⌋₊
        let m := ⌈exp L*exp (2*W)⌉₊+1
        ∀ t : ℝ, exp L/sqrt L ≤ t → t ≤ exp ((c*log (log L)+1)*L) →
          ‖∑ j ∈ Finset.Ico n m,
            ((jointFixedCutoff L W (log j-L)/(j:ℝ):ℝ):ℂ)*
              (j:ℂ)^(-(Complex.I*(t:ℂ)))‖ ≤
            C*W*exp (-((log L)^(1-c*log 2)/16)) := by
  obtain ⟨C, hC, hcut⟩ := jointFixedCutoff_uniform_bounds
  let G : ℝ := 4*exp 1+3
  have hG : 0 < G := by dsimp only [G]; positivity
  refine ⟨512*C*G*(8*G+2), by positivity, ?_⟩
  intro b c hb hc
  filter_upwards [eventually_jointUniformOrder_window hb hc,
    eventually_jointUniformOrder_saving hc,
    eventually_jointUniformWidth_grid_geometry hb,
    eventually_jointUniformWidth_grid_bounds hb,
    eventually_gt_atTop (1:ℝ)] with L hw hs hg hbds hL
  dsimp only
  intro t ht htop
  let W := jointUniformWidth b L
  let n := ⌊exp L*exp (-2*W)⌋₊
  let m := ⌈exp L*exp (2*W)⌉₊+1
  let H : ℝ := ((m-n:ℕ):ℝ)
  have hW : 0 < W := hbds.2.1
  have hW1 : W ≤ 1 := hbds.2.2.1.trans (by norm_num)
  have hn : 1 ≤ n := (by norm_num : (1:ℕ) ≤ 2).trans hg.1
  have hL0 : 0 < L := by linarith
  have ht0 : 0 < t := (div_pos (exp_pos L) (sqrt_pos.mpr hL0)).trans_le ht
  obtain ⟨k, hk, hkK, hsmall, hlarge⟩ := hw t ht htop
  have hU : 0 ≤ log L/2 := div_nonneg (log_nonneg hL.le) (by norm_num)
  have h := joint_log_short_phase_weighted (jointFixedCutoff L W) L t ht0 k n m
    hk hn hg.2.2.2.1 hg.2.2.2.2.1 (log L/2) hU hsmall hlarge
    ((jointFixedCutoff_contDiff L W).differentiable (by simp)) hC.le (by positivity)
    (fun y => (hcut L W hW hW1 y).1) (fun y => (hcut L W hW hW1 y).2.1)
  have hcost := middle_weight_cost (exp_pos L) hW hW1 hC hG
    (show 0 ≤ H from Nat.cast_nonneg _) hg.2.1 hg.2.2.2.2.2.2
  calc
    _ ≤ 512*H*exp (-(log L/2)/(2:ℝ)^k)*(H*((C/W+C)/(n:ℝ)^2)+C/(n:ℝ)) := h
    _ = 512*exp (-(log L/2)/(2:ℝ)^k)*
        (H*(H*((C/W+C)/(n:ℝ)^2)+C/(n:ℝ))) := by ring
    _ ≤ 512*exp (-((log L)^(1-c*log 2)/16))*(C*G*(8*G+2)*W) := by
      gcongr
      exact exp_le_exp.mp (hs k hkK)
    _ = _ := by ring

/-- The middle-band saving pays the growing logarithmic width coefficient. -/
theorem tendsto_jointUniformOrder_loglog_cost {c : ℝ} (hc : c*log 2 < 1) :
    Tendsto (fun L : ℝ => log (log L)*exp (-((log L)^(1-c*log 2)/16)))
      atTop (𝓝 0) := by
  let d : ℝ := 1-c*log 2
  have hd : 0 < d := by dsimp only [d]; linarith
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1/d) (1/16)
    (by norm_num)).comp ((tendsto_rpow_atTop hd).comp tendsto_log_atTop)
  have hmajor : Tendsto (fun L : ℝ => log L*exp (-((log L)^d/16))) atTop (𝓝 0) := by
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with L hL
    have hl : 0 ≤ log L := log_nonneg hL.le
    dsimp only [Function.comp_def]
    rw [← Real.rpow_mul hl, mul_one_div_cancel hd.ne', Real.rpow_one]
    congr 2
    ring
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [(tendsto_log_atTop.comp tendsto_log_atTop).eventually_ge_atTop (0:ℝ)]
      with L hL
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with L hL
    exact mul_le_mul_of_nonneg_right (log_le_self (log_nonneg hL)) (exp_pos _).le

/-- After the pole exponential is restored, the actual middle loss is still sublinear in L. -/
theorem tendsto_jointUniformWidth_middle_cost (b : ℝ) {c : ℝ} (hc : c*log 2 < 1) :
    Tendsto (fun L : ℝ => exp (L/2)*jointUniformWidth b L*
      exp (-((log L)^(1-c*log 2)/16))/L) atTop (𝓝 0) := by
  have ht := (tendsto_jointUniformOrder_loglog_cost hc).const_mul b
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  have he : exp (L/2)*exp (-L/2) = 1 := by
    rw [← exp_add, show L/2+ -L/2 = 0 by ring, exp_zero]
  unfold jointUniformWidth
  calc
    _ = b*log (log L)*exp (-((log L)^(1-c*log 2)/16)) := by ring
    _ = _ := by
      rw [show exp (L/2)*(b*L*log (log L)*exp (-L/2))*
          exp (-((log L)^(1-c*log 2)/16))/L =
          b*log (log L)*exp (-((log L)^(1-c*log 2)/16))*
            (exp (L/2)*exp (-L/2))*(L/L) by ring]
      rw [he, div_self hL.ne', mul_one, mul_one]

private theorem log_grid_phase_norm (w : ℕ → ℝ) (L t : ℝ) {n m : ℕ} (hn : 1 ≤ n) :
    ‖∑ j ∈ Finset.Ico n m, (w j:ℂ)*
      Complex.exp (((t*(log j-L):ℝ):ℂ)*Complex.I)‖ =
      ‖∑ j ∈ Finset.Ico n m, (w j:ℂ)*(j:ℂ)^(-(Complex.I*(t:ℂ)))‖ := by
  have hphase (j : ℕ) (hj : 1 ≤ j) :
      Complex.exp (((t*(log j-L):ℝ):ℂ)*Complex.I) =
        Complex.exp (((-t*L:ℝ):ℂ)*Complex.I)*
          (starRingEnd ℂ) ((j:ℂ)^(-(Complex.I*(t:ℂ)))) := by
    rw [Sieve.natCast_cpow_neg_I_mul t j hj, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Sieve.logPhase]
    have hpi : ((Real.pi:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp
    ring
  have heq : (∑ j ∈ Finset.Ico n m, (w j:ℂ)*
      Complex.exp (((t*(log j-L):ℝ):ℂ)*Complex.I)) =
      Complex.exp (((-t*L:ℝ):ℂ)*Complex.I)*
        (starRingEnd ℂ) (∑ j ∈ Finset.Ico n m, (w j:ℂ)*(j:ℂ)^(-(Complex.I*(t:ℂ)))) := by
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_mul, Complex.conj_ofReal, hphase j (hn.trans (Finset.mem_Ico.mp hj).1)]
    ring
  rw [heq, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, RCLike.norm_conj]

/-- The literal complex quadrature sum on the padded logarithmic cutoff interval. -/
def jointCutoffGridFourier (L W t : ℝ) : ℂ :=
  ∑ j ∈ Finset.Ico ⌊exp L*exp (-2*W)⌋₊ (⌈exp L*exp (2*W)⌉₊+1),
    ((jointFixedCutoff L W (log j-L)/(j:ℝ):ℝ):ℂ)*
      Complex.exp (((t*(log j-L):ℝ):ℂ)*Complex.I)

theorem jointCutoffGridFourier_neg (L W t : ℝ) :
    jointCutoffGridFourier L W (-t) = (starRingEnd ℂ) (jointCutoffGridFourier L W t) := by
  unfold jointCutoffGridFourier
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem norm_jointCutoffGridFourier_abs (L W t : ℝ) :
    ‖jointCutoffGridFourier L W |t|‖ = ‖jointCutoffGridFourier L W t‖ := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), jointCutoffGridFourier_neg, RCLike.norm_conj]

/-- Both frequency signs obey the source-independent middle-band cutoff bound. -/
theorem eventually_jointCutoffGridFourier_middle :
    ∃ C > 0, ∀ (b c : ℝ), 0 < b → 0 < c →
      ∀ᶠ L : ℝ in atTop, ∀ t : ℝ, exp L/sqrt L ≤ |t| →
        |t| ≤ exp ((c*log (log L)+1)*L) →
          ‖jointCutoffGridFourier L (jointUniformWidth b L) t‖ ≤
            C*jointUniformWidth b L*exp (-((log L)^(1-c*log 2)/16)) := by
  obtain ⟨C, hC, hbound⟩ := eventually_jointFixedCutoff_middle_cpow
  refine ⟨C, hC, ?_⟩
  intro b c hb hc
  filter_upwards [hbound b c hb hc, eventually_jointUniformWidth_grid_geometry hb] with L h hg
  intro t ht htop
  rw [← norm_jointCutoffGridFourier_abs]
  unfold jointCutoffGridFourier
  rw [log_grid_phase_norm _ L |t| ((by norm_num : (1:ℕ) ≤ 2).trans hg.1)]
  exact h |t| ht htop

/-- Above the middle threshold, the actual continuous Fourier term is exponentially small. -/
theorem eventually_jointFixedCutoff_fourier_middle :
    ∃ C > 0, ∀ b : ℝ, 0 < b → ∀ᶠ L : ℝ in atTop, ∀ t : ℝ,
      exp L/sqrt L ≤ |t| →
        ‖∫ y : ℝ, (jointFixedCutoff L (jointUniformWidth b L) y:ℂ)*
          Complex.exp (((t*y:ℝ):ℂ)*Complex.I)‖ ≤ C*exp (-L) := by
  obtain ⟨C, hC, hfour⟩ := jointFixedCutoff_fourier_decay
  refine ⟨C, hC, ?_⟩
  intro b hb
  have hbl := ((tendsto_log_atTop.comp tendsto_log_atTop).const_mul_atTop hb).eventually_ge_atTop (1:ℝ)
  filter_upwards [hbl, eventually_jointUniformWidth_grid_bounds hb,
    eventually_gt_atTop (1:ℝ)] with L hbl hbds hL
  change 1 ≤ b*log (log L) at hbl
  intro t ht
  let W := jointUniformWidth b L
  have hW : 0 < W := hbds.2.1
  have hW1 : W ≤ 1 := hbds.2.2.1.trans (by norm_num)
  have hL0 : 0 < L := by linarith
  have hWN : L ≤ W*exp L := by
    rw [mul_comm W, jointUniformWidth_grid_scale]
    have he : 1 ≤ exp (L/2) := one_le_exp_iff.mpr (by positivity)
    calc
      L ≤ (b*log (log L))*L := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hbl hL0.le
      _ ≤ (b*log (log L))*L*exp (L/2) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by ring
  have ht2 : (exp L)^2 ≤ L*t^2 := by
    have hs := (sq_le_sq₀ (by positivity : 0 ≤ exp L/sqrt L) (abs_nonneg t)).mpr ht
    rw [div_pow, sq_sqrt hL0.le, sq_abs] at hs
    have h := (div_le_iff₀ hL0).mp hs
    nlinarith
  have hbase : exp L ≤ W*t^2 := by
    apply (mul_le_mul_iff_of_pos_left (exp_pos L)).mp
    calc
      exp L*exp L = (exp L)^2 := by ring
      _ ≤ L*t^2 := ht2
      _ ≤ (W*exp L)*t^2 := mul_le_mul_of_nonneg_right hWN (sq_nonneg t)
      _ = _ := by ring
  have hf := (le_div_iff₀ hW).mp (hfour L W hW hW1 t)
  have hn : ‖∫ y : ℝ, (jointFixedCutoff L W y:ℂ)*
      Complex.exp (((t*y:ℝ):ℂ)*Complex.I)‖*exp L ≤ C := by
    calc
      _ ≤ ‖∫ y : ℝ, (jointFixedCutoff L W y:ℂ)*
          Complex.exp (((t*y:ℝ):ℂ)*Complex.I)‖*(W*t^2) :=
        mul_le_mul_of_nonneg_left hbase (norm_nonneg _)
      _ ≤ C := by nlinarith only [hf]
  calc
    _ ≤ C/exp L := (le_div_iff₀ (exp_pos L)).mpr hn
    _ = C*exp (-L) := by rw [exp_neg]; ring

/-- The literal integer-grid error against the full complex Fourier integral. -/
def jointCutoffFourierError (L W t : ℝ) : ℂ :=
  jointCutoffGridFourier L W t -
    ∫ y : ℝ, (jointFixedCutoff L W y:ℂ)*Complex.exp (((t*y:ℝ):ℂ)*Complex.I)

/-- The entire complex middle-band discrepancy has a paid, source-independent majorant. -/
theorem eventually_jointCutoffFourierError_middle :
    ∃ C > 0, ∀ (b c : ℝ), 0 < b → 0 < c →
      ∀ᶠ L : ℝ in atTop, ∀ t : ℝ, exp L/sqrt L ≤ |t| →
        |t| ≤ exp ((c*log (log L)+1)*L) →
          ‖jointCutoffFourierError L (jointUniformWidth b L) t‖ ≤
            C*(jointUniformWidth b L*exp (-((log L)^(1-c*log 2)/16))+exp (-L)) := by
  obtain ⟨C₁, hC₁, hgrid⟩ := eventually_jointCutoffGridFourier_middle
  obtain ⟨C₂, hC₂, hfour⟩ := eventually_jointFixedCutoff_fourier_middle
  refine ⟨C₁+C₂, by positivity, ?_⟩
  intro b c hb hc
  filter_upwards [hgrid b c hb hc, hfour b hb,
    eventually_jointUniformWidth_grid_bounds hb] with L hg hf hbds
  intro t ht htop
  have hW : 0 < jointUniformWidth b L := hbds.2.1
  calc
    _ ≤ ‖jointCutoffGridFourier L (jointUniformWidth b L) t‖+
        ‖∫ y : ℝ, (jointFixedCutoff L (jointUniformWidth b L) y:ℂ)*
          Complex.exp (((t*y:ℝ):ℂ)*Complex.I)‖ := norm_sub_le _ _
    _ ≤ C₁*jointUniformWidth b L*exp (-((log L)^(1-c*log 2)/16))+C₂*exp (-L) :=
      add_le_add (hg t ht htop) (hf t ht)
    _ ≤ (C₁+C₂)*jointUniformWidth b L*exp (-((log L)^(1-c*log 2)/16))+
        (C₁+C₂)*exp (-L) := by gcongr <;> linarith
    _ = _ := by ring

/-- The middle error majorant, after restoring the pole factor, is sublinear. -/
theorem tendsto_jointCutoff_middle_error_scale (b : ℝ) {c : ℝ} (hc : c*log 2 < 1) :
    Tendsto (fun L : ℝ => exp (L/2)*
      (jointUniformWidth b L*exp (-((log L)^(1-c*log 2)/16))+exp (-L))/L)
      atTop (𝓝 0) := by
  have htail : Tendsto (fun L : ℝ => exp (-L/2)/L) atTop (𝓝 0) := by
    have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-1) (1/2) (by norm_num)
    convert ht using 1
    funext L
    rw [Real.rpow_neg_one, show -(1/2:ℝ)*L = -L/2 by ring]
    ring
  have ht := (tendsto_jointUniformWidth_middle_cost b hc).add htail
  simp only [add_zero] at ht
  convert ht using 1
  funext L
  have he : exp (L/2)*exp (-L) = exp (-L/2) := by
    rw [← exp_add]
    congr 1
    ring
  rw [mul_add, add_div, he]
  ring

/-- The exact hyperbolic pole factor preserves the sublinear middle error. -/
theorem tendsto_jointCutoff_middle_pole_scale {b c : ℝ} (hb : 0 < b) (hc : c*log 2 < 1) :
    Tendsto (fun L : ℝ => 2*cosh (L/2)*
      (jointUniformWidth b L*exp (-((log L)^(1-c*log 2)/16))+exp (-L))/L)
      atTop (𝓝 0) := by
  have hmajor := (tendsto_jointCutoff_middle_error_scale b hc).const_mul 2
  simp only [mul_zero] at hmajor
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [eventually_jointUniformWidth_grid_bounds hb,
      eventually_gt_atTop (0:ℝ)] with L hw hL
    have hW := hw.2.1
    have hp := cosh_pos (L/2)
    positivity
  · filter_upwards [eventually_jointUniformWidth_grid_bounds hb,
      eventually_gt_atTop (0:ℝ)] with L hw hL
    have hW := hw.2.1
    have hh : cosh (L/2) ≤ exp (L/2) := by
      rw [Real.cosh_eq]
      have he : exp (-(L/2)) ≤ exp (L/2) := exp_le_exp.mpr (by linarith)
      linarith
    calc
      _ ≤ 2*exp (L/2)*
          (jointUniformWidth b L*exp (-((log L)^(1-c*log 2)/16))+exp (-L))/L := by gcongr
      _ = _ := by ring

/-- A paid sublinear loss for the literal middle-band discrepancy, including both poles. -/
theorem exists_jointCutoff_middle_loss {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (heta : c*log 2 < 1) :
    ∃ r : ℝ → ℝ, Tendsto (fun L => r L/L) atTop (𝓝 0) ∧
      ∀ᶠ L : ℝ in atTop, 0 ≤ r L ∧ ∀ t : ℝ, exp L/sqrt L ≤ |t| →
        |t| ≤ exp ((c*log (log L)+1)*L) →
          2*cosh (L/2)*‖jointCutoffFourierError L (jointUniformWidth b L) t‖ ≤ r L := by
  obtain ⟨C, hC, herror⟩ := eventually_jointCutoffFourierError_middle
  let r : ℝ → ℝ := fun L => C*(2*cosh (L/2)*
    (jointUniformWidth b L*exp (-((log L)^(1-c*log 2)/16))+exp (-L)))
  refine ⟨r, ?_, ?_⟩
  · have ht := (tendsto_jointCutoff_middle_pole_scale hb heta).const_mul C
    simpa only [r, mul_div_assoc, mul_zero] using ht
  · filter_upwards [herror b c hb hc, eventually_jointUniformWidth_grid_bounds hb] with L he hw
    have hW := hw.2.1
    have hp := cosh_pos (L/2)
    refine ⟨by dsimp only [r]; positivity, ?_⟩
    intro t ht htop
    exact (mul_le_mul_of_nonneg_left (he t ht htop) (by positivity)).trans_eq (by dsimp only [r]; ring)

end RHTower.WeilWorkPBAP
