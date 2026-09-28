import GaloisForLFunctions.RHTower.ThetaPrimeMomentPorts
import GaloisForLFunctions.RHTower.XiWallLogDerivativeCones

/-!
# Positive prime packets at the theta port

For probability weights `v_j ≥ 0` on positive scales `p_j` with reference log scale `L`, the
packet multiplier `A(w) = 1 - Σ_j v_j p_j^{-1/2} cosh(w log p_j)` and its real clock-gauge port
`E = X/2 + A X' + μ A' X / L` form an anti-reflected channel `E + E# = X`. On the wall
`w = 1/2 + iβ` the defect is `2|X|² Re[z - (Pz + μQ)/2 - (N₁z - μN₂)/2]` with explicit
positive- and reverse-frequency packet sums.

The source cones of `z = X'/X` at `1/2 + ih` and phase steering give a uniform threshold: if
`2 Re z_h < c Im z_h`, every packet with large reference scale, relative log width `≤ ε`, and
characteristic amplitude `|B(h)| ≥ c` has a negative modulus defect in the open physical strip for
**every** real gauge. Consequences: one-prime failure uniform in the gauge (20)–(24), the
phase-aperture classification, log-narrow packets (27)–(28), and the coherence threshold with its
forced logarithmic spread (30)–(32).
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-! ## Wall calculus of one prime -/

/-- `‖e^{ix} - e^{iy}‖ ≤ |x - y|`. -/
theorem norm_cexp_mul_I_sub_le (x y : ℝ) : ‖cexp (x * I) - cexp (y * I)‖ ≤ |x - y| := by
  have h : cexp (x * I) - cexp (y * I) = cexp (y * I) * (cexp (I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; push_cast; ring_nf
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y)

/-- The exact wall value of `A_p'`: `A_p'(1/2 + iβ) = -log p [p^{iβ} - p^{-1} p^{-iβ}]/2`. -/
theorem primeDeletionSymbolDeriv_wall {p : ℝ} (hp : 0 < p) (β : ℝ) :
    primeDeletionSymbolDeriv p (1 / 2 + β * I) =
      -(Real.log p * (cexp (Real.log p * β * I) - p⁻¹ * cexp (-(Real.log p * β * I))) / 2) := by
  have hr : p ^ (-(1 / 2 : ℝ)) = Real.exp (-(Real.log p / 2)) := by
    rw [Real.rpow_def_of_pos hp]; ring_nf
  have hr1 : ((p ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (Real.log p * (1 / 2 : ℂ)) = 1 := by
    rw [show (Real.log p : ℂ) * (1 / 2 : ℂ) = ((Real.log p / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp, ← Complex.ofReal_mul, hr, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, Complex.ofReal_one]
  have hr2 : ((p ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (-(Real.log p * (1 / 2 : ℂ))) = (p⁻¹ : ℝ) := by
    rw [show -((Real.log p : ℂ) * (1 / 2 : ℂ)) = ((-(Real.log p / 2) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp, ← Complex.ofReal_mul, hr, ← Real.exp_add,
      show -(Real.log p / 2) + -(Real.log p / 2) = -Real.log p by ring, Real.exp_neg,
      Real.exp_log hp]
  rw [primeDeletionSymbolDeriv, Complex.sinh, show (Real.log p : ℂ) * (1 / 2 + β * I) =
    Real.log p * (1 / 2 : ℂ) + Real.log p * β * I by ring, Complex.exp_add, neg_add,
    Complex.exp_add]
  push_cast at hr1 hr2 ⊢
  linear_combination (-(Real.log p * cexp (Real.log p * β * I)) / 2) * hr1 +
    ((Real.log p * cexp (-(Real.log p * β * I))) / 2) * hr2

/-! ## Positive prime packets -/

variable {ι : Type*}

/-- The packet multiplier `A(w) = 1 - Σ_j v_j p_j^{-1/2} cosh(w log p_j)`. -/
def packetSymbol (s : Finset ι) (v p : ι → ℝ) (w : ℂ) : ℂ :=
  1 - ∑ j ∈ s, (v j : ℂ) * (1 - primeDeletionSymbol (p j) w)

/-- Its derivative. -/
def packetSymbolDeriv (s : Finset ι) (v p : ι → ℝ) (w : ℂ) : ℂ :=
  ∑ j ∈ s, (v j : ℂ) * primeDeletionSymbolDeriv (p j) w

theorem hasDerivAt_packetSymbol (s : Finset ι) (v p : ι → ℝ) (w : ℂ) :
    HasDerivAt (packetSymbol s v p) (packetSymbolDeriv s v p w) w := by
  have h := (HasDerivAt.fun_sum (u := s) fun j _ =>
    ((hasDerivAt_primeDeletionSymbol (p j) w).const_sub 1).const_mul (v j : ℂ)).const_sub 1
  refine h.congr_deriv ?_
  simp only [packetSymbolDeriv, mul_neg, Finset.sum_neg_distrib, neg_neg]

theorem halfPortReflect_packetSymbol (s : Finset ι) (v p : ι → ℝ) (w : ℂ) :
    halfPortReflect (packetSymbol s v p) w = packetSymbol s v p w := by
  have h := fun j => halfPortReflect_primeDeletionSymbol (p j) w
  simp only [halfPortReflect] at h ⊢
  simp only [packetSymbol, map_sub, map_one, map_sum, map_mul, Complex.conj_ofReal, h]

theorem halfPortReflect_packetSymbolDeriv (s : Finset ι) (v p : ι → ℝ) (w : ℂ) :
    halfPortReflect (packetSymbolDeriv s v p) w = -packetSymbolDeriv s v p w := by
  have h := fun j => halfPortReflect_primeDeletionSymbolDeriv (p j) w
  simp only [halfPortReflect] at h ⊢
  simp only [packetSymbolDeriv, map_sum, map_mul, Complex.conj_ofReal, h, mul_neg,
    Finset.sum_neg_distrib]

/-- **(26).** The packet port with real clock gauge `μ` and reference scale `L`:
`E = X/2 + A X' + μ A' X / L`. -/
def packetGaugePort (s : Finset ι) (v p : ι → ℝ) (L μ : ℝ) (w : ℂ) : ℂ :=
  thetaSymmetrizedPort w / 2 + packetSymbol s v p w * deriv thetaSymmetrizedPort w +
    ((μ / L : ℝ) : ℂ) * packetSymbolDeriv s v p w * thetaSymmetrizedPort w

/-- The packet ports are anti-reflected channels: `E + E# = X`. -/
theorem packetGaugePort_add_reflect (s : Finset ι) (v p : ι → ℝ) (L μ : ℝ) (w : ℂ) :
    packetGaugePort s v p L μ w + halfPortReflect (packetGaugePort s v p L μ) w =
      thetaSymmetrizedPort w := by
  have h1 := halfPortReflect_thetaSymmetrizedPort w
  have h2 := halfPortReflect_deriv_thetaSymmetrizedPort w
  have h3 := halfPortReflect_packetSymbol s v p w
  have h4 := halfPortReflect_packetSymbolDeriv s v p w
  simp only [halfPortReflect, packetGaugePort] at h1 h2 h3 h4 ⊢
  rw [map_add, map_add, map_div₀, map_mul, map_mul, map_mul, h1, h2, h3, h4, Complex.conj_ofReal,
    map_ofNat]
  ring

/-- A single prime is the one-point packet. -/
theorem packetGaugePort_unit (q μ : ℝ) :
    packetGaugePort (Finset.univ : Finset Unit) (fun _ => 1) (fun _ => q) (Real.log q) μ =
      primeGaugePort q μ := by
  funext w
  simp [packetGaugePort, primeGaugePort, packetSymbol, packetSymbolDeriv]

theorem continuous_packetGaugePort (s : Finset ι) (v p : ι → ℝ) (L μ : ℝ) :
    Continuous (packetGaugePort s v p L μ) := by
  have hA : Continuous (packetSymbol s v p) :=
    continuous_iff_continuousAt.mpr fun w => (hasDerivAt_packetSymbol s v p w).continuousAt
  have hA' : Continuous (packetSymbolDeriv s v p) := by
    unfold packetSymbolDeriv
    refine continuous_finsetSum _ fun j _ => continuous_const.mul ?_
    exact continuous_iff_continuousAt.mpr fun w =>
      (hasDerivAt_primeDeletionSymbolDeriv (p j) w).continuousAt
  unfold packetGaugePort
  exact ((differentiable_thetaSymmetrizedPort.continuous.div_const 2).add
    (hA.mul differentiable_deriv_thetaSymmetrizedPort.continuous)).add
    ((continuous_const.mul hA').mul differentiable_thetaSymmetrizedPort.continuous)

theorem continuous_portImbalance {E : ℂ → ℂ} (hE : Continuous E) :
    Continuous (portImbalance E) := by
  unfold portImbalance halfPortReflect
  have : Continuous fun w => E (-(starRingEnd ℂ) w) := hE.comp Complex.continuous_conj.neg
  exact (hE.norm.pow 2).sub ((Complex.continuous_conj.comp this).norm.pow 2)

/-- A negative defect at a wall point moves into the open physical strip. -/
theorem exists_interior_of_wall_neg {E : ℂ → ℂ} (hE : Continuous E) {β : ℝ}
    (hneg : portImbalance E (1 / 2 + β * I) < 0) :
    ∃ w : ℂ, 0 < w.re ∧ w.re < 1 / 2 ∧ portImbalance E w < 0 := by
  have hc : Continuous fun t : ℝ => portImbalance E ((t : ℂ) + β * I) :=
    (continuous_portImbalance hE).comp (by fun_prop)
  have h0 : portImbalance E (((1 / 2 : ℝ) : ℂ) + β * I) < 0 := by simpa using hneg
  have hev := (hc.tendsto (1 / 2)).eventually (gt_mem_nhds h0)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hm : 0 < min (ε / 2) (1 / 4) := lt_min (by linarith) (by norm_num)
  have hm1 := min_le_left (ε / 2) (1 / 4)
  have hm2 := min_le_right (ε / 2) (1 / 4)
  refine ⟨((1 / 2 - min (ε / 2) (1 / 4) : ℝ) : ℂ) + β * I, ?_, ?_, ?_⟩
  · simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]; linarith
  · simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]; linarith
  · refine hball ?_
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith

/-- Strict (or weak) order in the open strip passes to the wall. -/
theorem portImbalance_wall_nonneg {E : ℂ → ℂ} (hE : Continuous E)
    (hord : ∀ w : ℂ, 0 < w.re → w.re < 1 / 2 → 0 ≤ portImbalance E w) (β : ℝ) :
    0 ≤ portImbalance E (1 / 2 + β * I) := by
  by_contra h
  obtain ⟨w, h1, h2, h3⟩ := exists_interior_of_wall_neg hE (not_le.mp h)
  exact (hord w h1 h2).not_gt h3

/-- **(15) for packets.** Away from the zeros of `X`, `D = 2|X|² Re[A z + (μ/L) A']`. -/
theorem packetGaugePort_imbalance_eq (s : Finset ι) (v p : ι → ℝ) (L μ : ℝ) {w : ℂ}
    (hX : thetaSymmetrizedPort w ≠ 0) :
    portImbalance (packetGaugePort s v p L μ) w = 2 * ‖thetaSymmetrizedPort w‖ ^ 2 *
      (packetSymbol s v p w * thetaPortLogDeriv w +
        ((μ / L : ℝ) : ℂ) * packetSymbolDeriv s v p w).re := by
  rw [portImbalance_eq_re_div (packetGaugePort_add_reflect s v p L μ) hX]
  congr 3
  rw [packetGaugePort, thetaPortLogDeriv]
  field_simp
  ring

/-- **The packet wall expansion.** At `w = 1/2 + iβ`, with `L_j = log p_j`,
`A z + (μ/L) A' = z - (P z + μ Q)/2 - (N₁ z - μ N₂)/2` where
`P = Σ v_j p_j^{iβ}`, `Q = Σ v_j (L_j/L) p_j^{iβ}`, `N₁ = Σ v_j p_j^{-1} p_j^{-iβ}`,
`N₂ = Σ v_j p_j^{-1} (L_j/L) p_j^{-iβ}`. -/
theorem packetSymbol_wall (s : Finset ι) (v p : ι → ℝ) (L μ β : ℝ) (hp : ∀ j ∈ s, 0 < p j)
    (z : ℂ) :
    packetSymbol s v p (1 / 2 + β * I) * z +
        ((μ / L : ℝ) : ℂ) * packetSymbolDeriv s v p (1 / 2 + β * I) =
      z - ((∑ j ∈ s, (v j : ℂ) * cexp (Real.log (p j) * β * I)) * z +
          μ * ∑ j ∈ s, (v j : ℂ) * ((Real.log (p j) / L : ℝ) : ℂ) *
            cexp (Real.log (p j) * β * I)) / 2 -
        ((∑ j ∈ s, (v j : ℂ) * (((p j)⁻¹ : ℝ) : ℂ) * cexp (-(Real.log (p j) * β * I))) * z -
          μ * ∑ j ∈ s, (v j : ℂ) * (((p j)⁻¹ : ℝ) : ℂ) * ((Real.log (p j) / L : ℝ) : ℂ) *
            cexp (-(Real.log (p j) * β * I))) / 2 := by
  have eL : packetSymbol s v p (1 / 2 + β * I) * z +
      ((μ / L : ℝ) : ℂ) * packetSymbolDeriv s v p (1 / 2 + β * I) =
        z - ∑ j ∈ s, ((v j : ℂ) * (1 - primeDeletionSymbol (p j) (1 / 2 + β * I)) * z -
          ((μ / L : ℝ) : ℂ) * ((v j : ℂ) * primeDeletionSymbolDeriv (p j) (1 / 2 + β * I))) := by
    rw [packetSymbol, packetSymbolDeriv, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum]
    ring
  rw [eL]
  have eR : ∀ a b c d : ι → ℂ, z - ((∑ j ∈ s, a j) * z + μ * ∑ j ∈ s, b j) / 2 -
      ((∑ j ∈ s, c j) * z - μ * ∑ j ∈ s, d j) / 2 =
        z - ∑ j ∈ s, ((a j * z + μ * b j) / 2 + (c j * z - μ * d j) / 2) := by
    intro a b c d
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul,
      ← Finset.mul_sum]
    ring
  rw [eR]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [primeDeletionSymbol_wall (hp j hj), primeDeletionSymbolDeriv_wall (hp j hj)]
  push_cast
  rcases eq_or_ne (L : ℂ) 0 with h0 | h0
  · simp [h0]; ring
  · field_simp
    ring

/-! ## Packet estimates -/

/-- The packet characteristic function `B(β) = Σ_j v_j e^{i(L_j - L)β}` (29). -/
def packetPhase (s : Finset ι) (v p : ι → ℝ) (L β : ℝ) : ℂ :=
  ∑ j ∈ s, (v j : ℂ) * cexp (((Real.log (p j) - L) * β : ℝ) * I)

theorem norm_packetPhase_le_one {s : Finset ι} {v : ι → ℝ} (hv : ∀ j ∈ s, 0 ≤ v j)
    (hs : ∑ j ∈ s, v j = 1) (p : ι → ℝ) (L β : ℝ) : ‖packetPhase s v p L β‖ ≤ 1 := by
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  rw [← hs]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (hv j hj)]

/-- **Phase steering.** `|B(β) - B(β')| ≤ δ |β - β'|` when all log scales lie within `δ` of `L`. -/
theorem norm_packetPhase_sub_le {s : Finset ι} {v : ι → ℝ} (hv : ∀ j ∈ s, 0 ≤ v j)
    (hs : ∑ j ∈ s, v j = 1) {p : ι → ℝ} {L δ : ℝ} (hδ : ∀ j ∈ s, |Real.log (p j) - L| ≤ δ)
    (β β' : ℝ) :
    ‖packetPhase s v p L β - packetPhase s v p L β'‖ ≤ δ * |β - β'| := by
  rw [packetPhase, packetPhase, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j ∈ s, ‖(v j : ℂ) * cexp (((Real.log (p j) - L) * β : ℝ) * I) -
        (v j : ℂ) * cexp (((Real.log (p j) - L) * β' : ℝ) * I)‖
      ≤ ∑ j ∈ s, v j * (δ * |β - β'|) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hv j hj)]
        refine mul_le_mul_of_nonneg_left ?_ (hv j hj)
        refine (norm_cexp_mul_I_sub_le _ _).trans ?_
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_right (hδ j hj) (abs_nonneg _)
    _ = δ * |β - β'| := by rw [← Finset.sum_mul, hs, one_mul]

theorem sum_mul_cexp_log_eq (s : Finset ι) (a : ι → ℂ) (p : ι → ℝ) (L β : ℝ) :
    ∑ j ∈ s, a j * cexp (Real.log (p j) * β * I) =
      cexp ((L * β : ℝ) * I) * ∑ j ∈ s, a j * cexp (((Real.log (p j) - L) * β : ℝ) * I) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast; ring

theorem packet_positive_sum_eq (s : Finset ι) (v p : ι → ℝ) (L β : ℝ) :
    ∑ j ∈ s, (v j : ℂ) * cexp (Real.log (p j) * β * I) =
      cexp ((L * β : ℝ) * I) * packetPhase s v p L β := by
  rw [packetPhase, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast; ring

theorem norm_cexp_log_mul_I (q β : ℝ) : ‖cexp (Real.log q * β * I)‖ = 1 := by
  rw [show (Real.log q : ℂ) * β * I = ((Real.log q * β : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_cexp_neg_log_mul_I (q β : ℝ) : ‖cexp (-(Real.log q * β * I))‖ = 1 := by
  rw [show -((Real.log q : ℂ) * β * I) = ((-(Real.log q * β) : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The derivative-weighted packet differs from the plain one by at most `δ/L`. -/
theorem norm_scale_weighted_sub_le {s : Finset ι} {v : ι → ℝ} (hv : ∀ j ∈ s, 0 ≤ v j)
    (hs : ∑ j ∈ s, v j = 1) {p : ι → ℝ} {L δ : ℝ} (hL : 0 < L)
    (hδ : ∀ j ∈ s, |Real.log (p j) - L| ≤ δ) (u : ι → ℂ) (hu : ∀ j ∈ s, ‖u j‖ ≤ 1) :
    ‖∑ j ∈ s, (v j : ℂ) * ((Real.log (p j) / L : ℝ) : ℂ) * u j - ∑ j ∈ s, (v j : ℂ) * u j‖ ≤
      δ / L := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ j ∈ s, v j * (δ / L) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [show (v j : ℂ) * ((Real.log (p j) / L : ℝ) : ℂ) * u j - (v j : ℂ) * u j =
            ((v j * ((Real.log (p j) - L) / L) : ℝ) : ℂ) * u j by push_cast; field_simp]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hv j hj),
          abs_div, abs_of_pos hL]
        have h1 : |Real.log (p j) - L| / L ≤ δ / L := div_le_div_of_nonneg_right (hδ j hj) hL.le
        have h2 : 0 ≤ |Real.log (p j) - L| / L := by positivity
        calc v j * (|Real.log (p j) - L| / L) * ‖u j‖ ≤ v j * (|Real.log (p j) - L| / L) * 1 :=
              mul_le_mul_of_nonneg_left (hu j hj) (mul_nonneg (hv j hj) h2)
          _ ≤ v j * (δ / L) := by rw [mul_one]; exact mul_le_mul_of_nonneg_left h1 (hv j hj)
    _ = δ / L := by rw [← Finset.sum_mul, hs, one_mul]

/-- The reverse-frequency packets are exponentially small in the scale. -/
theorem norm_packet_negative_sum_le {s : Finset ι} {v : ι → ℝ} (hv : ∀ j ∈ s, 0 ≤ v j)
    (hs : ∑ j ∈ s, v j = 1) {p : ι → ℝ} (hp : ∀ j ∈ s, 0 < p j) {L δ : ℝ}
    (hδ : ∀ j ∈ s, |Real.log (p j) - L| ≤ δ) (a : ι → ℝ) {C : ℝ} (ha : ∀ j ∈ s, |a j| ≤ C)
    (β : ℝ) :
    ‖∑ j ∈ s, (v j : ℂ) * (((p j)⁻¹ : ℝ) : ℂ) * (a j : ℂ) * cexp (-(Real.log (p j) * β * I))‖ ≤
      Real.exp (-(L - δ)) * C := by
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ j ∈ s, v j * (Real.exp (-(L - δ)) * C) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [norm_mul, norm_mul, norm_mul, norm_cexp_neg_log_mul_I, mul_one, Complex.norm_real,
          Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hv j hj),
          Real.norm_of_nonneg (inv_nonneg.mpr (hp j hj).le), Real.norm_eq_abs, mul_assoc]
        refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ (ha j hj) (abs_nonneg _)
          (Real.exp_pos _).le) (hv j hj)
        rw [← Real.exp_log (hp j hj), ← Real.exp_neg]
        exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hδ j hj)).1])
    _ = Real.exp (-(L - δ)) * C := by rw [← Finset.sum_mul, hs, one_mul]

/-- **The deterministic wall-defect bound.** If `P₀(z_h + μ)` is positive real and all packet
errors are at most `η`, then
`Re[z - (Pz + μQ)/2 - (N₁z - μN₂)/2] ≤ Re z_h + η - (c/2 - η)|z_h + μ| + η(4|z_h| + 2η + 1)/2`. -/
theorem wall_re_le {z zh P P₀ Q N₁ N₂ : ℂ} {μ η c : ℝ} (hη : 0 ≤ η) (hP₀ : ‖P₀‖ ≤ 1)
    (hc : c ≤ ‖P₀‖) (hph : (P₀ * (zh + μ)).re = ‖P₀‖ * ‖zh + μ‖) (hz : ‖z - zh‖ ≤ η)
    (hP : ‖P - P₀‖ ≤ η) (hQ : ‖Q - P₀‖ ≤ η) (hN₁ : ‖N₁‖ ≤ η) (hN₂ : ‖N₂‖ ≤ η) :
    (z - (P * z + μ * Q) / 2 - (N₁ * z - μ * N₂) / 2).re ≤
      zh.re + η - (c / 2 - η) * ‖zh + μ‖ + η * (4 * ‖zh‖ + 2 * η + 1) / 2 := by
  set m := ‖zh + (μ : ℂ)‖ with hmdef
  have hm : 0 ≤ m := norm_nonneg _
  have hμ : ‖(μ : ℂ)‖ ≤ m + ‖zh‖ := by
    calc ‖(μ : ℂ)‖ = ‖(zh + μ) - zh‖ := by ring_nf
      _ ≤ m + ‖zh‖ := norm_sub_le _ _
  have hzn : ‖z‖ ≤ ‖zh‖ + η := by
    calc ‖z‖ = ‖zh + (z - zh)‖ := by ring_nf
      _ ≤ ‖zh‖ + ‖z - zh‖ := norm_add_le _ _
      _ ≤ ‖zh‖ + η := by linarith
  have hE : ‖(P - P₀) * z + P₀ * (z - zh) + μ * (Q - P₀)‖ ≤
      η * (‖zh‖ + η) + η + (m + ‖zh‖) * η := by
    refine (norm_add₃_le).trans ?_
    rw [norm_mul, norm_mul, norm_mul]
    have h1 := mul_le_mul hP hzn (norm_nonneg _) hη
    have h2 := mul_le_mul hP₀ hz (norm_nonneg _) zero_le_one
    have h3 := mul_le_mul hμ hQ (norm_nonneg _) (by positivity)
    linarith
  have hN : ‖N₁ * z - μ * N₂‖ ≤ η * (‖zh‖ + η) + (m + ‖zh‖) * η := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 := mul_le_mul hN₁ hzn (norm_nonneg _) hη
    have h3 := mul_le_mul hμ hN₂ (norm_nonneg _) (by positivity)
    linarith
  have hsplit : z - (P * z + μ * Q) / 2 - (N₁ * z - μ * N₂) / 2 = z - P₀ * (zh + μ) / 2 -
      ((P - P₀) * z + P₀ * (z - zh) + μ * (Q - P₀)) / 2 - (N₁ * z - μ * N₂) / 2 := by ring
  rw [hsplit]
  generalize ((P - P₀) * z + P₀ * (z - zh) + μ * (Q - P₀)) = E at hE ⊢
  generalize (N₁ * z - μ * N₂) = N at hN ⊢
  simp only [Complex.sub_re, Complex.div_ofNat_re]
  have hre1 : z.re ≤ zh.re + η := by
    have := (abs_le.mp (Complex.abs_re_le_norm (z - zh))).2
    rw [Complex.sub_re] at this; linarith
  have hre2 := (abs_le.mp (Complex.abs_re_le_norm E)).1
  have hre3 := (abs_le.mp (Complex.abs_re_le_norm N)).1
  have hcm := mul_le_mul_of_nonneg_right hc hm
  rw [hph]
  linarith

/-- Every target phase is reached on the wall within `π/L` of any height. -/
theorem exists_wall_phase {L : ℝ} (hL : 0 < L) (h θ : ℝ) :
    ∃ β : ℝ, |β - h| ≤ Real.pi / L ∧ cexp ((L * β : ℝ) * I) = cexp (θ * I) := by
  set k := round ((L * h - θ) / (2 * Real.pi))
  have hk := abs_sub_round ((L * h - θ) / (2 * Real.pi))
  have hπ := Real.pi_pos
  refine ⟨h + (θ + 2 * Real.pi * k - L * h) / L, ?_, ?_⟩
  · rw [add_sub_cancel_left, abs_div, abs_of_pos hL]
    refine div_le_div_of_nonneg_right ?_ hL.le
    have : θ + 2 * Real.pi * k - L * h =
        -(2 * Real.pi) * ((L * h - θ) / (2 * Real.pi) - k) := by
      field_simp; ring
    rw [this, abs_mul, abs_neg, abs_of_pos (by positivity)]
    nlinarith
  · have : ((L * (h + (θ + 2 * Real.pi * k - L * h) / L) : ℝ) : ℂ) * I =
        θ * I + (k : ℂ) * (2 * Real.pi * I) := by
      rw [show L * (h + (θ + 2 * Real.pi * k - L * h) / L) = θ + 2 * Real.pi * k by
        field_simp; ring]
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem continuousAt_thetaPortLogDeriv {w : ℂ} (hX : thetaSymmetrizedPort w ≠ 0) :
    ContinuousAt thetaPortLogDeriv w :=
  differentiable_deriv_thetaSymmetrizedPort.continuous.continuousAt.div
    differentiable_thetaSymmetrizedPort.continuous.continuousAt hX

/-- Continuity of `z = X'/X` along the wall. -/
theorem exists_wall_logDeriv_near (h : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ β : ℝ, |β - h| < r →
      ‖thetaPortLogDeriv (1 / 2 + β * I) - thetaPortLogDeriv (1 / 2 + h * I)‖ < η := by
  have hf : ContinuousAt (fun β : ℝ => (1 / 2 : ℂ) + β * I) h := by fun_prop
  have hc : ContinuousAt (fun β : ℝ => thetaPortLogDeriv (1 / 2 + β * I)) h :=
    ContinuousAt.comp (g := thetaPortLogDeriv) (f := fun β : ℝ => (1 / 2 : ℂ) + β * I) (x := h)
      (continuousAt_thetaPortLogDeriv (thetaSymmetrizedPort_wall_ne_zero h)) hf
  obtain ⟨r, hr, H⟩ := Metric.continuousAt_iff.mp hc η hη
  exact ⟨r, hr, fun β hβ => by
    have := H (x := β) (by rwa [Real.dist_eq])
    rwa [dist_eq_norm] at this⟩

/-! ## The uniform coherence threshold -/

/-- **The coherence threshold (30), uniform in the gauge.** Let `z_h = X'/X(1/2 + ih)` have
`Im z_h > 0` and let `2 Re z_h < c Im z_h`. There are `ε > 0` and `L₀` such that every positive
normalized packet with reference scale `L ≥ L₀`, all log scales within `εL` of `L`, and
`|B(h)| ≥ c` has, for **every** real gauge `μ`, a point of the open strip `0 < Re w < 1/2` with
negative modulus defect. -/
theorem exists_packet_wall_threshold {h c : ℝ} (hc0 : 0 < c)
    (hb : 0 < (thetaPortLogDeriv (1 / 2 + h * I)).im)
    (hc : 2 * (thetaPortLogDeriv (1 / 2 + h * I)).re < c * (thetaPortLogDeriv (1 / 2 + h * I)).im) :
    ∃ ε > 0, ∃ L₀ > 0, ∀ (s : Finset ι) (v p : ι → ℝ) (L μ : ℝ), (∀ j ∈ s, 0 ≤ v j) →
      ∑ j ∈ s, v j = 1 → (∀ j ∈ s, 0 < p j) → L₀ ≤ L →
      (∀ j ∈ s, |Real.log (p j) - L| ≤ ε * L) → c ≤ ‖packetPhase s v p L h‖ →
      ∃ w : ℂ, 0 < w.re ∧ w.re < 1 / 2 ∧ portImbalance (packetGaugePort s v p L μ) w < 0 := by
  have hzr := fun (η : ℝ) (hη : 0 < η) => exists_wall_logDeriv_near h hη
  generalize thetaPortLogDeriv (1 / 2 + h * I) = zh at hb hc hzr
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = zh.im + 3 + 2 * ‖zh‖ := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  have hgap : 0 < c * zh.im / 2 - zh.re := by linarith
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min (min 1 (c / 2)) ((c * zh.im / 2 - zh.re) / (2 * K)) :=
    ⟨_, rfl⟩
  have hη0 : 0 < η := hηdef ▸ lt_min (lt_min one_pos (by linarith)) (by positivity)
  have hη1 : η ≤ 1 := hηdef ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hηc : η ≤ c / 2 := hηdef ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hηK : η * K ≤ (c * zh.im / 2 - zh.re) / 2 := by
    have := min_le_right (min 1 (c / 2)) ((c * zh.im / 2 - zh.re) / (2 * K))
    rw [← hηdef] at this
    calc η * K ≤ (c * zh.im / 2 - zh.re) / (2 * K) * K := mul_le_mul_of_nonneg_right this hK0.le
      _ = _ := by field_simp
  obtain ⟨r, hr, hzr⟩ := hzr η hη0
  have hπ := Real.pi_pos
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (1 / 2) (η / (1 + Real.pi)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := hεdef ▸ lt_min (by norm_num) (by positivity)
  have hε2 : ε ≤ 1 / 2 := hεdef ▸ min_le_left _ _
  have hεη : ε * (1 + Real.pi) ≤ η := by
    have := min_le_right (1 / 2) (η / (1 + Real.pi))
    rw [← hεdef] at this
    calc ε * (1 + Real.pi) ≤ η / (1 + Real.pi) * (1 + Real.pi) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = η := by field_simp
  refine ⟨ε, hε0, max (max 1 (2 * Real.pi / r)) (2 * Real.log (2 / η)),
    lt_max_of_lt_left (lt_max_of_lt_left one_pos), ?_⟩
  intro s v p L μ hv hs hp hL0 hδ hB
  have hL1 : 1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL0)
  have hL : 0 < L := by linarith
  have hLr : 2 * Real.pi / r ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL0)
  have hLη : 2 * Real.log (2 / η) ≤ L := (le_max_right _ _).trans hL0
  obtain ⟨β, hβ, hphase⟩ := exists_wall_phase hL h (-(packetPhase s v p L h * (zh + μ)).arg)
  have hβr : |β - h| < r := by
    have h2 : 2 * Real.pi ≤ L * r := by
      have := (div_le_iff₀ hr).mp hLr; linarith
    have : Real.pi / L ≤ r / 2 := by
      rw [div_le_div_iff₀ hL (by norm_num)]; linarith
    linarith
  have hX := thetaSymmetrizedPort_wall_ne_zero β
  have hz : ‖thetaPortLogDeriv (1 / 2 + β * I) - zh‖ ≤ η := (hzr β hβr).le
  -- the phase-rotated characteristic value
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : ℂ,
      P₀ = cexp ((-(packetPhase s v p L h * (zh + μ)).arg : ℝ) * I) * packetPhase s v p L h :=
    ⟨_, rfl⟩
  have hP₀n : ‖P₀‖ = ‖packetPhase s v p L h‖ := by
    rw [hP₀, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hph : (P₀ * (zh + μ)).re = ‖P₀‖ * ‖zh + μ‖ := by
    generalize packetPhase s v p L h = B at hP₀ hP₀n
    have hu := Complex.norm_mul_exp_arg_mul_I (B * (zh + μ))
    have : P₀ * (zh + μ) = ((‖B * (zh + μ)‖ : ℝ) : ℂ) := by
      calc P₀ * (zh + μ) = cexp ((-(B * (zh + μ)).arg : ℝ) * I) * (B * (zh + μ)) := by
            rw [hP₀]; ring
        _ = cexp ((-(B * (zh + μ)).arg : ℝ) * I) *
            ((‖B * (zh + μ)‖ : ℂ) * cexp ((B * (zh + μ)).arg * I)) := by rw [hu]
        _ = (‖B * (zh + μ)‖ : ℂ) *
            cexp (((-(B * (zh + μ)).arg : ℝ) : ℂ) * I + ((B * (zh + μ)).arg : ℂ) * I) := by
          rw [Complex.exp_add]; ring
        _ = _ := by
          rw [show ((-(B * (zh + μ)).arg : ℝ) : ℂ) * I + ((B * (zh + μ)).arg : ℂ) * I = 0 by
            push_cast; ring, Complex.exp_zero, mul_one]
    rw [this, Complex.ofReal_re, norm_mul, hP₀n]
  -- the wall packet sums
  have hPP₀' : ‖∑ j ∈ s, (v j : ℂ) * cexp (Real.log (p j) * β * I) - P₀‖ ≤ ε * Real.pi := by
    rw [packet_positive_sum_eq, hphase, hP₀, ← mul_sub, norm_mul,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    refine (norm_packetPhase_sub_le hv hs hδ β h).trans ?_
    calc ε * L * |β - h| ≤ ε * L * (Real.pi / L) :=
          mul_le_mul_of_nonneg_left hβ (by positivity)
      _ = ε * Real.pi := by field_simp
  have hPP₀ : ‖∑ j ∈ s, (v j : ℂ) * cexp (Real.log (p j) * β * I) - P₀‖ ≤ η := by
    have := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one :
      Real.pi ≤ 1 + Real.pi) hε0.le
    linarith
  have hQP := norm_scale_weighted_sub_le hv hs hL hδ (fun j => cexp (Real.log (p j) * β * I))
    (fun j _ => (norm_cexp_log_mul_I _ _).le)
  rw [mul_div_assoc, div_self hL.ne', mul_one] at hQP
  have hQP₀ : ‖∑ j ∈ s, (v j : ℂ) * ((Real.log (p j) / L : ℝ) : ℂ) *
      cexp (Real.log (p j) * β * I) - P₀‖ ≤ η := by
    refine (norm_sub_le_norm_sub_add_norm_sub _
      (∑ j ∈ s, (v j : ℂ) * cexp (Real.log (p j) * β * I)) _).trans ?_
    linarith
  have hexp : Real.exp (-(L - ε * L)) ≤ η / 2 := by
    have hεL := mul_le_mul_of_nonneg_right hε2 hL.le
    have h1 : -(L - ε * L) ≤ -Real.log (2 / η) := by linarith
    calc Real.exp (-(L - ε * L)) ≤ Real.exp (-Real.log (2 / η)) := Real.exp_le_exp.mpr h1
      _ = η / 2 := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have hN₁ : ‖∑ j ∈ s, (v j : ℂ) * (((p j)⁻¹ : ℝ) : ℂ) *
      cexp (-(Real.log (p j) * β * I))‖ ≤ η := by
    have := norm_packet_negative_sum_le hv hs hp hδ (fun _ => 1) (C := 1)
      (fun _ _ => by norm_num) β
    simp only [Complex.ofReal_one, mul_one] at this
    linarith
  have hN₂ : ‖∑ j ∈ s, (v j : ℂ) * (((p j)⁻¹ : ℝ) : ℂ) * ((Real.log (p j) / L : ℝ) : ℂ) *
      cexp (-(Real.log (p j) * β * I))‖ ≤ η := by
    have hC : ∀ j ∈ s, |Real.log (p j) / L| ≤ 3 / 2 := by
      intro j hj
      have := abs_le.mp (hδ j hj)
      have hεL := mul_le_mul_of_nonneg_right hε2 hL.le
      rw [abs_div, abs_of_pos hL, div_le_iff₀ hL, abs_le]
      constructor <;> linarith
    have := norm_packet_negative_sum_le hv hs hp hδ (fun j => Real.log (p j) / L) hC β
    have h1 := mul_le_mul_of_nonneg_right hexp (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith
  have hre := wall_re_le hη0.le (hP₀n ▸ norm_packetPhase_le_one hv hs p L h) (hP₀n ▸ hB) hph hz
    hPP₀ hQP₀ hN₁ hN₂
  have hm : zh.im ≤ ‖zh + μ‖ := by
    have := Complex.abs_im_le_norm (zh + μ)
    rw [Complex.add_im, Complex.ofReal_im, add_zero] at this
    exact (le_abs_self _).trans this
  have h1 : (c / 2 - η) * zh.im ≤ (c / 2 - η) * ‖zh + μ‖ :=
    mul_le_mul_of_nonneg_left hm (by linarith)
  have h2 : η * η ≤ η := by nlinarith
  have h3 : 0 ≤ η * ‖zh‖ := mul_nonneg hη0.le (norm_nonneg _)
  rw [hK] at hηK
  have hXn : 0 < ‖thetaSymmetrizedPort (1 / 2 + β * I)‖ := norm_pos_iff.mpr hX
  have hDneg : portImbalance (packetGaugePort s v p L μ) (1 / 2 + β * I) < 0 := by
    rw [packetGaugePort_imbalance_eq s v p L μ hX, packetSymbol_wall s v p L μ β hp]
    exact mul_neg_of_pos_of_neg (by positivity) (hre.trans_lt (by linarith))
  exact exists_interior_of_wall_neg (continuous_packetGaugePort s v p L μ) hDneg

/-! ## One prime -/

/-- Rotating by `e^{-i arg z}` makes `z` positive real. -/
theorem cexp_neg_arg_mul_I_mul_self (z : ℂ) : cexp ((-z.arg : ℝ) * I) * z = (‖z‖ : ℂ) := by
  have hu := Complex.norm_mul_exp_arg_mul_I z
  calc cexp ((-z.arg : ℝ) * I) * z = cexp ((-z.arg : ℝ) * I) * ((‖z‖ : ℂ) * cexp (z.arg * I)) := by
        rw [hu]
    _ = ‖z‖ := by
        rw [mul_left_comm, ← Complex.exp_add, show ((-z.arg : ℝ) : ℂ) * I + (z.arg : ℂ) * I = 0 by
          push_cast; ring, Complex.exp_zero, mul_one]

/-- **(24).** One prime threshold works for every real gauge coefficient at once: for all
`p ≥ P₀` and all `μ ∈ ℝ`, the port `E_{p,μ}` has a negative modulus defect in `0 < Re w < 1/2`. -/
theorem exists_primeGaugePort_threshold :
    ∃ P₀ : ℝ, ∀ p : ℝ, P₀ ≤ p → ∀ μ : ℝ,
      ∃ w : ℂ, 0 < w.re ∧ w.re < 1 / 2 ∧ portImbalance (primeGaugePort p μ) w < 0 := by
  obtain ⟨h1, h2⟩ := thetaPortLogDeriv_cone_two
  obtain ⟨ε, hε, L₀, hL₀, H⟩ := exists_packet_wall_threshold (ι := Unit) (h := 2) (c := 1)
    one_pos (by linarith) (by linarith)
  refine ⟨Real.exp L₀, fun p hp μ => ?_⟩
  have hp0 : 0 < p := (Real.exp_pos _).trans_le hp
  have hlog : L₀ ≤ Real.log p := (Real.le_log_iff_exp_le hp0).mpr hp
  have := H Finset.univ (fun _ => 1) (fun _ => p) (Real.log p) μ (fun _ _ => zero_le_one)
    (by simp) (fun _ _ => hp0) hlog
    (fun _ _ => by simpa using mul_nonneg hε.le (hL₀.le.trans hlog)) (by simp [packetPhase])
  rwa [packetGaugePort_unit] at this

/-- **(21)–(22) conclusion.** Deletion-after-clock `E_p^cov` has a negative modulus defect in the
open physical strip for every sufficiently large `p`. -/
theorem exists_primeCovariantPort_threshold :
    ∃ P₀ : ℝ, ∀ p : ℝ, P₀ ≤ p →
      ∃ w : ℂ, 0 < w.re ∧ w.re < 1 / 2 ∧ portImbalance (primeCovariantPort p) w < 0 := by
  obtain ⟨P₀, H⟩ := exists_primeGaugePort_threshold
  exact ⟨P₀, fun p hp => H p hp 0⟩

/-- Clock-after-deletion `E_p = X/2 + (A_p X)'` fails in the same way. -/
theorem exists_primeMomentPort_threshold :
    ∃ P₀ : ℝ, ∀ p : ℝ, P₀ ≤ p →
      ∃ w : ℂ, 0 < w.re ∧ w.re < 1 / 2 ∧ portImbalance (primeMomentPort p) w < 0 := by
  obtain ⟨P₀, H⟩ := exists_primeGaugePort_threshold
  exact ⟨P₀, fun p hp => H p hp (Real.log p)⟩

/-- **(20).** At a phase-steered wall point, the prime wall symbol is exactly
`1 - [e^{iθ} + p^{-1} e^{-iθ}]/2`. -/
theorem primeDeletionSymbol_wall_of_phase {p β θ : ℝ} (hp : 0 < p)
    (h : cexp ((Real.log p * β : ℝ) * I) = cexp (θ * I)) :
    primeDeletionSymbol p (1 / 2 + β * I) = 1 - (cexp (θ * I) + p⁻¹ * cexp (-(θ * I))) / 2 := by
  have h' : cexp (Real.log p * β * I) = cexp (θ * I) := by rw [← h]; push_cast; ring_nf
  rw [primeDeletionSymbol_wall hp, Complex.exp_neg, h', ← Complex.exp_neg]

theorem thetaPortLogDeriv_two_re_sub_half_norm_neg :
    (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).re -
      ‖thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)‖ / 2 < 0 := by
  obtain ⟨h1, h2⟩ := thetaPortLogDeriv_two_aperture
  obtain ⟨h3, h4⟩ := thetaPortLogDeriv_cone_two
  have hz : 0 < ‖thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)‖ :=
    h3.trans_le ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  rw [div_lt_iff₀ hz] at h1
  nlinarith

/-- **(21).** Steer `β_p → 2` so that `p^{iβ_p} = e^{iθ_*}` with `e^{iθ_*} z₀ = |z₀|`. Then
`Re[A_p(1/2 + iβ_p) z(1/2 + iβ_p)] → Re z₀ - |z₀|/2 < 0`. -/
theorem exists_prime_wall_steering :
    ∃ β : ℝ → ℝ, (∀ p : ℝ, 1 < p → |β p - 2| ≤ Real.pi / Real.log p ∧
        cexp ((Real.log p * β p : ℝ) * I) =
          cexp ((-(thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).arg : ℝ) * I)) ∧
      Tendsto (fun p => (primeDeletionSymbol p (1 / 2 + β p * I) *
        thetaPortLogDeriv (1 / 2 + β p * I)).re) atTop
        (𝓝 ((thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).re -
          ‖thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)‖ / 2)) ∧
      (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).re -
          ‖thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)‖ / 2 < 0 := by
  refine ?_
  have hex : ∀ p : ℝ, ∃ b : ℝ, 1 < p → |b - 2| ≤ Real.pi / Real.log p ∧
      cexp ((Real.log p * b : ℝ) * I) =
        cexp ((-(thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).arg : ℝ) * I) := by
    intro p
    by_cases hp : 1 < p
    · obtain ⟨b, hb1, hb2⟩ := exists_wall_phase (Real.log_pos hp) 2
        (-(thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).arg)
      exact ⟨b, fun _ => ⟨hb1, hb2⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose β hβ using hex
  refine ⟨β, hβ, ?_, thetaPortLogDeriv_two_re_sub_half_norm_neg⟩
  generalize hz₀ : thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I) = z₀ at hβ
  have hβlim : Tendsto β atTop (𝓝 2) := by
    have hπL : Tendsto (fun p => Real.pi / Real.log p) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    refine tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hπL)
    filter_upwards [eventually_gt_atTop 1] with p hp
    exact (hβ p hp).1
  have hz : Tendsto (fun p => thetaPortLogDeriv (1 / 2 + β p * I)) atTop (𝓝 z₀) := by
    have hf : ContinuousAt (fun b : ℝ => (1 / 2 : ℂ) + b * I) 2 := by fun_prop
    have hc := ContinuousAt.comp (g := thetaPortLogDeriv) (f := fun b : ℝ => (1 / 2 : ℂ) + b * I)
      (x := 2) (continuousAt_thetaPortLogDeriv (thetaSymmetrizedPort_wall_ne_zero 2)) hf
    rw [← hz₀]
    exact hc.tendsto.comp hβlim
  have hA : Tendsto (fun p => primeDeletionSymbol p (1 / 2 + β p * I)) atTop
      (𝓝 (1 - cexp ((-z₀.arg : ℝ) * I) / 2)) := by
    have hinv : Tendsto (fun p : ℝ => ((p⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
      rw [← Complex.ofReal_zero]
      exact (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    have := (tendsto_const_nhds (x := (1 : ℂ))).sub (((tendsto_const_nhds
      (x := cexp ((-z₀.arg : ℝ) * I))).add (hinv.mul (tendsto_const_nhds
        (x := cexp (-((-z₀.arg : ℝ) * I)))))).div_const 2)
    rw [zero_mul, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with p hp
    rw [primeDeletionSymbol_wall_of_phase (by linarith) (hβ p hp).2]
  have hval : ((1 - cexp ((-z₀.arg : ℝ) * I) / 2) * z₀).re = z₀.re - ‖z₀‖ / 2 := by
    have hrot := cexp_neg_arg_mul_I_mul_self z₀
    rw [sub_mul, one_mul, div_mul_eq_mul_div, hrot, Complex.sub_re, Complex.div_ofNat_re,
      Complex.ofReal_re]
  rw [← hval]
  exact (Complex.continuous_re.tendsto _).comp (hA.mul hz)

/-! ## The phase-aperture classification -/

/-- **Phase-aperture classification.** Let ports `E_n` with `E_n + E_n# = X` have (weak) order
in the open strip for all large `n`, and wall expansions
`(E_n - X/2)/X = (1 - c e^{iΛ_n β}) z(1/2 + iβ) + o(1)` uniformly for `|β - h| ≤ r`, with a
freely sweeping phase `Λ_n → ∞`. Then `Re z_h ≥ c |z_h|`. -/
theorem strip_order_forces_phase_aperture {h c r : ℝ} (hr : 0 < r) {E : ℕ → ℂ → ℂ} {Λ : ℕ → ℝ}
    (hΛ : Tendsto Λ atTop atTop) (hE : ∀ n, Continuous (E n))
    (hrefl : ∀ n w, E n w + halfPortReflect (E n) w = thetaSymmetrizedPort w)
    (hexp : ∀ η > 0, ∀ᶠ n in atTop, ∀ β : ℝ, |β - h| ≤ r →
      ‖(E n (1 / 2 + β * I) - thetaSymmetrizedPort (1 / 2 + β * I) / 2) /
          thetaSymmetrizedPort (1 / 2 + β * I) -
        (1 - c * cexp ((Λ n * β : ℝ) * I)) * thetaPortLogDeriv (1 / 2 + β * I)‖ ≤ η)
    (hord : ∀ᶠ n in atTop, ∀ w : ℂ, 0 < w.re → w.re < 1 / 2 → 0 ≤ portImbalance (E n) w) :
    c * ‖thetaPortLogDeriv (1 / 2 + h * I)‖ ≤ (thetaPortLogDeriv (1 / 2 + h * I)).re := by
  have hzr := fun (η : ℝ) (hη : 0 < η) => exists_wall_logDeriv_near h hη
  generalize thetaPortLogDeriv (1 / 2 + h * I) = zh at hzr ⊢
  refine le_of_forall_pos_lt_add fun η hη => ?_
  have hK : 0 < 3 + |c| := by positivity
  set η' := η / (3 + |c|) with hη'
  have hη'0 : 0 < η' := div_pos hη hK
  obtain ⟨r', hr', hzr⟩ := hzr η' hη'0
  have hπ := Real.pi_pos
  have hmin : 0 < min r r' := lt_min hr hr'
  obtain ⟨n, hn1, hn2, hn3⟩ := ((hexp η' hη'0).and (hord.and
    (hΛ.eventually (eventually_gt_atTop (Real.pi / min r r'))))).exists
  have hΛ0 : 0 < Λ n := (div_pos hπ hmin).trans hn3
  obtain ⟨β, hβ, hphase⟩ := exists_wall_phase hΛ0 h (-zh.arg)
  have hβ' : |β - h| < min r r' := by
    refine hβ.trans_lt ?_
    rw [div_lt_iff₀ hΛ0]
    rw [div_lt_iff₀ hmin] at hn3
    linarith
  have hX := thetaSymmetrizedPort_wall_ne_zero β
  have hwall := portImbalance_wall_nonneg (hE n) hn2 β
  rw [portImbalance_eq_re_div (hrefl n) hX] at hwall
  have hXn : 0 < ‖thetaSymmetrizedPort (1 / 2 + β * I)‖ := norm_pos_iff.mpr hX
  have hW : 0 ≤ ((E n (1 / 2 + β * I) - thetaSymmetrizedPort (1 / 2 + β * I) / 2) /
      thetaSymmetrizedPort (1 / 2 + β * I)).re := by
    by_contra hneg
    push Not at hneg
    have : 2 * ‖thetaSymmetrizedPort (1 / 2 + β * I)‖ ^ 2 * _ < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hneg
    linarith
  have hT := hn1 β (hβ'.le.trans (min_le_left _ _))
  rw [hphase] at hT
  generalize (E n (1 / 2 + β * I) - thetaSymmetrizedPort (1 / 2 + β * I) / 2) /
    thetaSymmetrizedPort (1 / 2 + β * I) = W at hW hT
  have hz := (hzr β (hβ'.trans_le (min_le_right _ _))).le
  generalize thetaPortLogDeriv (1 / 2 + β * I) = z at hz hT
  have hrot := cexp_neg_arg_mul_I_mul_self zh
  have hsplit : (1 - c * cexp ((-zh.arg : ℝ) * I)) * z = zh - c * (‖zh‖ : ℂ) +
      (1 - c * cexp ((-zh.arg : ℝ) * I)) * (z - zh) := by
    rw [← hrot]; ring
  have hfac : ‖1 - c * cexp ((-zh.arg : ℝ) * I)‖ ≤ 1 + |c| := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  have herr : ‖(1 - c * cexp ((-zh.arg : ℝ) * I)) * (z - zh)‖ ≤ (1 + |c|) * η' := by
    rw [norm_mul]; exact mul_le_mul hfac hz (norm_nonneg _) (by positivity)
  have h1 := (abs_le.mp (Complex.abs_re_le_norm (W - (1 - c * cexp ((-zh.arg : ℝ) * I)) * z))).2
  have h2 := (abs_le.mp (Complex.abs_re_le_norm ((1 - c * cexp ((-zh.arg : ℝ) * I)) * (z - zh)))).2
  rw [hsplit] at hT h1
  generalize (1 - c * cexp ((-zh.arg : ℝ) * I)) * (z - zh) = D at hT h1 h2 herr
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at h1
  have hη'e : (3 + |c|) * η' = η := by rw [hη']; field_simp
  have habs := abs_nonneg c
  nlinarith

/-- At `w₀ = 1/2 + 2i`, strip order with a cofinal wall multiplier `1 - c e^{iLβ} + o(1)` forces
`c < 4/√137`; the prime deletion coefficient `c = 1/2` is excluded. -/
theorem phase_aperture_lt_of_strip_order {c r : ℝ} (hr : 0 < r) {E : ℕ → ℂ → ℂ} {Λ : ℕ → ℝ}
    (hΛ : Tendsto Λ atTop atTop) (hE : ∀ n, Continuous (E n))
    (hrefl : ∀ n w, E n w + halfPortReflect (E n) w = thetaSymmetrizedPort w)
    (hexp : ∀ η > 0, ∀ᶠ n in atTop, ∀ β : ℝ, |β - 2| ≤ r →
      ‖(E n (1 / 2 + β * I) - thetaSymmetrizedPort (1 / 2 + β * I) / 2) /
          thetaSymmetrizedPort (1 / 2 + β * I) -
        (1 - c * cexp ((Λ n * β : ℝ) * I)) * thetaPortLogDeriv (1 / 2 + β * I)‖ ≤ η)
    (hord : ∀ᶠ n in atTop, ∀ w : ℂ, 0 < w.re → w.re < 1 / 2 → 0 ≤ portImbalance (E n) w) :
    c < 4 / Real.sqrt 137 := by
  have H := strip_order_forces_phase_aperture (h := 2) hr hΛ hE hrefl hexp hord
  obtain ⟨h1, _⟩ := thetaPortLogDeriv_two_aperture
  obtain ⟨h3, _⟩ := thetaPortLogDeriv_cone_two
  have hz : 0 < ‖thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)‖ :=
    h3.trans_le ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  rw [div_lt_iff₀ hz] at h1
  by_contra hc
  push Not at hc
  nlinarith [mul_le_mul_of_nonneg_right hc hz.le]

/-! ## Positive phase sums -/

/-- `Re Σ v_j e^{iθ_j} ≥ cos Δ` for normalized positive weights and `|θ_j| ≤ Δ ≤ π`. -/
theorem cos_le_re_phase_sum {s : Finset ι} {v θ : ι → ℝ} (hv : ∀ j ∈ s, 0 ≤ v j)
    (hs : ∑ j ∈ s, v j = 1) {Δ : ℝ} (hΔ : Δ ≤ Real.pi) (hθ : ∀ j ∈ s, |θ j| ≤ Δ) :
    Real.cos Δ ≤ (∑ j ∈ s, (v j : ℂ) * cexp (θ j * I)).re := by
  rw [Complex.re_sum]
  calc Real.cos Δ = ∑ j ∈ s, v j * Real.cos Δ := by rw [← Finset.sum_mul, hs, one_mul]
    _ ≤ ∑ j ∈ s, ((v j : ℂ) * cexp (θ j * I)).re := by
      refine Finset.sum_le_sum fun j hj => ?_
      rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, ← Real.cos_abs (θ j)]
      exact mul_le_mul_of_nonneg_left
        (Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hΔ (hθ j hj)) (hv j hj)

/-- **Minimum-width geometry.** For `0 < Δ < π/2`, positive normalized weights on phases in
`[-Δ, Δ]` satisfy `|Σ v_j e^{iθ_j}| = cos Δ` exactly when all weight sits at the two endpoints
with equal endpoint masses. -/
theorem norm_phase_sum_eq_cos_iff {s : Finset ι} {v θ : ι → ℝ} (hv : ∀ j ∈ s, 0 ≤ v j)
    (hs : ∑ j ∈ s, v j = 1) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ < Real.pi / 2)
    (hθ : ∀ j ∈ s, |θ j| ≤ Δ) :
    ‖∑ j ∈ s, (v j : ℂ) * cexp (θ j * I)‖ = Real.cos Δ ↔
      (∀ j ∈ s, 0 < v j → |θ j| = Δ) ∧
        ∑ j ∈ s with θ j = Δ, v j = ∑ j ∈ s with θ j = -Δ, v j := by
  have hπ := Real.pi_pos
  have hΔπ : Δ ≤ Real.pi := by linarith
  set B := ∑ j ∈ s, (v j : ℂ) * cexp (θ j * I) with hB
  have hre : B.re = ∑ j ∈ s, v j * Real.cos (θ j) := by
    rw [hB, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have him : B.im = ∑ j ∈ s, v j * Real.sin (θ j) := by
    rw [hB, Complex.im_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  -- on endpoint-supported weights, `Re B = cos Δ` and `Im B = sin Δ (w₊ - w₋)`
  have hend : (∀ j ∈ s, 0 < v j → |θ j| = Δ) → B.re = Real.cos Δ ∧
      B.im = Real.sin Δ * (∑ j ∈ s with θ j = Δ, v j - ∑ j ∈ s with θ j = -Δ, v j) := by
    intro H
    have hsupp : ∀ j ∈ s, v j = 0 ∨ θ j = Δ ∨ θ j = -Δ := by
      intro j hj
      rcases (hv j hj).lt_or_eq with h | h
      · have := H j hj h
        rcases abs_eq hΔ0.le |>.mp this with h' | h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
      · exact Or.inl h.symm
    constructor
    · rw [hre]
      calc ∑ j ∈ s, v j * Real.cos (θ j) = ∑ j ∈ s, v j * Real.cos Δ := by
            refine Finset.sum_congr rfl fun j hj => ?_
            rcases hsupp j hj with h | h | h
            · rw [h, zero_mul, zero_mul]
            · rw [h]
            · rw [h, Real.cos_neg]
        _ = Real.cos Δ := by rw [← Finset.sum_mul, hs, one_mul]
    · rw [him, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hne : Δ ≠ -Δ := by linarith
      rcases hsupp j hj with h | h | h
      · simp [h]
      · rw [if_pos h, if_neg (h ▸ hne), h]; ring
      · rw [if_neg (by rw [h]; exact fun h' => hne (by linarith)), if_pos h, h, Real.sin_neg]; ring
  have hsin : 0 < Real.sin Δ := Real.sin_pos_of_pos_of_lt_pi hΔ0 (by linarith)
  have hcos : 0 ≤ Real.cos Δ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, hΔ.le⟩
  constructor
  · intro hBn
    have hlow := cos_le_re_phase_sum hv hs hΔπ hθ
    rw [← hB] at hlow
    have hup : B.re ≤ ‖B‖ := (le_abs_self _).trans (Complex.abs_re_le_norm B)
    have hReq : B.re = Real.cos Δ := by linarith
    have hsupp : ∀ j ∈ s, 0 < v j → |θ j| = Δ := by
      have hsum : ∑ j ∈ s, v j * (Real.cos (θ j) - Real.cos Δ) = 0 := by
        rw [Finset.sum_congr rfl fun j _ => mul_sub (v j) _ _, Finset.sum_sub_distrib, ← hre,
          ← Finset.sum_mul, hs, one_mul, hReq, sub_self]
      have hnn : ∀ j ∈ s, 0 ≤ v j * (Real.cos (θ j) - Real.cos Δ) := by
        intro j hj
        refine mul_nonneg (hv j hj) (sub_nonneg.mpr ?_)
        rw [← Real.cos_abs (θ j)]
        exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hΔπ (hθ j hj)
      intro j hj hvj
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum j hj
      have hc : Real.cos |θ j| = Real.cos Δ := by
        rw [Real.cos_abs]
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h hvj.ne'
        · linarith
      exact Real.injOn_cos ⟨abs_nonneg _, (hθ j hj).trans hΔπ⟩ ⟨hΔ0.le, hΔπ⟩ hc
    refine ⟨hsupp, ?_⟩
    obtain ⟨_, hIm⟩ := hend hsupp
    have hIm0 : B.im = 0 := by
      have hn : ‖B‖ ^ 2 = B.re ^ 2 + B.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      rw [hBn, hReq] at hn
      nlinarith
    rw [hIm0] at hIm
    have := mul_eq_zero.mp hIm.symm
    rcases this with h | h
    · exact absurd h hsin.ne'
    · linarith
  · rintro ⟨hsupp, hw⟩
    obtain ⟨hRe, hIm⟩ := hend hsupp
    rw [hw, sub_self, mul_zero] at hIm
    have : B = (Real.cos Δ : ℂ) := Complex.ext (by rw [hRe, Complex.ofReal_re])
      (by rw [hIm, Complex.ofReal_im])
    rw [this, Complex.norm_real, Real.norm_of_nonneg hcos]

/-- For packets: `Re B(β) ≥ cos(βδ)` when all log scales lie within `δ` of `L` and `βδ ≤ π`. -/
theorem cos_le_re_packetPhase {s : Finset ι} {v : ι → ℝ} (hv : ∀ j ∈ s, 0 ≤ v j)
    (hs : ∑ j ∈ s, v j = 1) {p : ι → ℝ} {L δ β : ℝ} (hδ : ∀ j ∈ s, |Real.log (p j) - L| ≤ δ)
    (hβ : 0 ≤ β) (hπ : β * δ ≤ Real.pi) :
    Real.cos (β * δ) ≤ (packetPhase s v p L β).re :=
  cos_le_re_phase_sum hv hs hπ fun j hj => by
    rw [abs_mul, abs_of_nonneg hβ, mul_comm]
    exact mul_le_mul_of_nonneg_left (hδ j hj) hβ

theorem packetPhase_zero (s : Finset ι) (v p : ι → ℝ) (L : ℝ) :
    packetPhase s v p L 0 = ∑ j ∈ s, (v j : ℂ) := by
  simp [packetPhase]

theorem width_nonneg {s : Finset ι} {v : ι → ℝ} (hs : ∑ j ∈ s, v j = 1) {p : ι → ℝ} {L δ : ℝ}
    (hδ : ∀ j ∈ s, |Real.log (p j) - L| ≤ δ) : 0 ≤ δ := by
  obtain ⟨j, hj⟩ := Finset.nonempty_of_sum_ne_zero (hs ▸ one_ne_zero : ∑ j ∈ s, v j ≠ 0)
  exact (abs_nonneg _).trans (hδ j hj)

/-! ## Packet sequences -/

section Sequences

variable {s : ℕ → Finset ι} {v p : ℕ → ι → ℝ} {L δ : ℕ → ℝ}

/-- **(30), sequence form.** For packets with `δ_R/L_R → 0` and `L_R → ∞`, eventually every
packet with `|B_R(h)| ≥ c` has a negative strip defect for every real gauge. -/
theorem eventually_packet_threshold {h c : ℝ} (hc0 : 0 < c)
    (hb : 0 < (thetaPortLogDeriv (1 / 2 + h * I)).im)
    (hc : 2 * (thetaPortLogDeriv (1 / 2 + h * I)).re < c * (thetaPortLogDeriv (1 / 2 + h * I)).im)
    (hv : ∀ R, ∀ j ∈ s R, 0 ≤ v R j) (hs : ∀ R, ∑ j ∈ s R, v R j = 1)
    (hp : ∀ R, ∀ j ∈ s R, 0 < p R j) (hδ : ∀ R, ∀ j ∈ s R, |Real.log (p R j) - L R| ≤ δ R)
    (hδL : Tendsto (fun R => δ R / L R) atTop (𝓝 0)) (hL : Tendsto L atTop atTop) :
    ∀ᶠ R in atTop, c ≤ ‖packetPhase (s R) (v R) (p R) (L R) h‖ → ∀ μ : ℝ,
      ∃ w : ℂ, 0 < w.re ∧ w.re < 1 / 2 ∧
        portImbalance (packetGaugePort (s R) (v R) (p R) (L R) μ) w < 0 := by
  obtain ⟨ε, hε, L₀, hL₀, H⟩ := exists_packet_wall_threshold (ι := ι) hc0 hb hc
  filter_upwards [hL.eventually (eventually_ge_atTop L₀), hδL.eventually (eventually_lt_nhds hε)]
    with R hR1 hR2 hB μ
  have hLR : 0 < L R := hL₀.trans_le hR1
  rw [div_lt_iff₀ hLR] at hR2
  exact H (s R) (v R) (p R) (L R) μ (hv R) (hs R) (hp R) hR1
    (fun j hj => (hδ R j hj).trans hR2.le) hB

/-- **(27).** For `δ_R → 0` and `L_R → ∞`, both wall packets are `1 + o(1)` uniformly for
`|β - 2| ≤ π/L_R`. -/
theorem eventually_packetPhase_near_one (hv : ∀ R, ∀ j ∈ s R, 0 ≤ v R j)
    (hs : ∀ R, ∑ j ∈ s R, v R j = 1) (hδ : ∀ R, ∀ j ∈ s R, |Real.log (p R j) - L R| ≤ δ R)
    (hδ0 : Tendsto δ atTop (𝓝 0)) (hL : Tendsto L atTop atTop) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ R in atTop, ∀ β : ℝ, |β - 2| ≤ Real.pi / L R →
      ‖packetPhase (s R) (v R) (p R) (L R) β - 1‖ ≤ η ∧
      ‖∑ j ∈ s R, (v R j : ℂ) * ((Real.log (p R j) / L R : ℝ) : ℂ) *
          cexp (((Real.log (p R j) - L R) * β : ℝ) * I) - 1‖ ≤ η := by
  filter_upwards [hL.eventually (eventually_ge_atTop (Real.pi + 1)),
    hδ0.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < η / 4))] with R hR1 hR2 β hβ
  have hπ := Real.pi_pos
  have hLR : 0 < L R := by linarith
  have hδ0' := width_nonneg (hs R) (hδ R)
  have hβ3 : |β| ≤ 3 := by
    have h1 : Real.pi / L R ≤ 1 := (div_le_one hLR).mpr (by linarith)
    have h2 := abs_sub_abs_le_abs_sub β 2
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h2
    linarith
  have hB : ‖packetPhase (s R) (v R) (p R) (L R) β - 1‖ ≤ 3 * δ R := by
    have := norm_packetPhase_sub_le (hv R) (hs R) (hδ R) β 0
    rw [packetPhase_zero, ← Complex.ofReal_sum, hs R, Complex.ofReal_one, sub_zero] at this
    nlinarith
  refine ⟨by linarith, ?_⟩
  have hQ := norm_scale_weighted_sub_le (hv R) (hs R) hLR (hδ R)
    (fun j => cexp (((Real.log (p R j) - L R) * β : ℝ) * I))
    (fun j _ => (Complex.norm_exp_ofReal_mul_I _).le)
  have hL1 : δ R / L R ≤ δ R := div_le_self hδ0' (by linarith)
  calc _ = ‖(∑ j ∈ s R, (v R j : ℂ) * ((Real.log (p R j) / L R : ℝ) : ℂ) *
          cexp (((Real.log (p R j) - L R) * β : ℝ) * I) -
        ∑ j ∈ s R, (v R j : ℂ) * cexp (((Real.log (p R j) - L R) * β : ℝ) * I)) +
        (packetPhase (s R) (v R) (p R) (L R) β - 1)‖ := by congr 1; rw [packetPhase]; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ η := by linarith

/-- **(28).** For `δ_R → 0` and `L_R → ∞`, the wall expression `A z + (μ/L_R) A'` differs from
`z - e^{iL_Rβ}(z + μ)/2` by at most `η(1 + |μ|)`, uniformly in the real gauge `μ` and in
`|β - 2| ≤ π/L_R`. -/
theorem eventually_lognarrow_wall_approx (hv : ∀ R, ∀ j ∈ s R, 0 ≤ v R j)
    (hs : ∀ R, ∑ j ∈ s R, v R j = 1) (hp : ∀ R, ∀ j ∈ s R, 0 < p R j)
    (hδ : ∀ R, ∀ j ∈ s R, |Real.log (p R j) - L R| ≤ δ R) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hL : Tendsto L atTop atTop) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ R in atTop, ∀ β : ℝ, |β - 2| ≤ Real.pi / L R → ∀ μ : ℝ,
      ‖(packetSymbol (s R) (v R) (p R) (1 / 2 + β * I) * thetaPortLogDeriv (1 / 2 + β * I) +
          ((μ / L R : ℝ) : ℂ) * packetSymbolDeriv (s R) (v R) (p R) (1 / 2 + β * I)) -
        (thetaPortLogDeriv (1 / 2 + β * I) - cexp ((L R * β : ℝ) * I) *
          (thetaPortLogDeriv (1 / 2 + β * I) + μ) / 2)‖ ≤ η * (1 + |μ|) := by
  obtain ⟨r, hr, hzr⟩ := exists_wall_logDeriv_near 2 one_pos
  set M := ‖thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)‖ + 1 with hM
  have hM0 : 0 < M := by positivity
  set η' := η / (M + 1) with hη'
  have hη'0 : 0 < η' := by positivity
  have hη'M : η' * M ≤ η := by
    rw [hη', div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  have hη'η : η' ≤ η := by
    rw [hη', div_le_iff₀ (by linarith)]; nlinarith
  have hLδ : Tendsto (fun R => L R - δ R) atTop atTop :=
    (hL.atTop_add hδ0.neg).congr fun R => (sub_eq_add_neg _ _).symm
  have hexp : Tendsto (fun R => Real.exp (-(L R - δ R))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hLδ
  have hπ := Real.pi_pos
  filter_upwards [eventually_packetPhase_near_one hv hs hδ hδ0 hL hη'0,
    hL.eventually (eventually_ge_atTop (2 * Real.pi / r + 1)),
    hL.eventually (eventually_ge_atTop 1),
    hδ0.eventually (eventually_le_nhds one_pos),
    hexp.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < η' / 2))]
    with R hB hLr hL1 hδ1 hex β hβ μ
  have hLR : 0 < L R := by linarith
  obtain ⟨hB1, hB2⟩ := hB β hβ
  have hβr : |β - 2| < r := by
    refine hβ.trans_lt ?_
    rw [div_lt_iff₀ hLR]
    have : 2 * Real.pi / r < L R := by linarith
    rw [div_lt_iff₀ hr] at this
    linarith
  have hzM : ‖thetaPortLogDeriv (1 / 2 + β * I)‖ ≤ M := by
    have := hzr β hβr
    have h2 := norm_sub_norm_le (thetaPortLogDeriv (1 / 2 + β * I))
      (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I))
    rw [hM]; linarith
  rw [packetSymbol_wall (s R) (v R) (p R) (L R) μ β (hp R)]
  generalize thetaPortLogDeriv (1 / 2 + β * I) = z at hzM ⊢
  rw [sum_mul_cexp_log_eq (s R) (fun j => (v R j : ℂ)), sum_mul_cexp_log_eq (s R)
    (fun j => (v R j : ℂ) * ((Real.log (p R j) / L R : ℝ) : ℂ))]
  set e := cexp ((L R * β : ℝ) * I) with he
  have hen : ‖e‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hδ0' := width_nonneg (hs R) (hδ R)
  have hN₁ := norm_packet_negative_sum_le (hv R) (hs R) (hp R) (hδ R) (fun _ => 1) (C := 1)
    (fun _ _ => by norm_num) β
  simp only [Complex.ofReal_one, mul_one] at hN₁
  have hC : ∀ j ∈ s R, |Real.log (p R j) / L R| ≤ 2 := by
    intro j hj
    have := abs_le.mp (hδ R j hj)
    rw [abs_div, abs_of_pos hLR, div_le_iff₀ hLR, abs_le]
    constructor <;> nlinarith
  have hN₂ := norm_packet_negative_sum_le (hv R) (hs R) (hp R) (hδ R)
    (fun j => Real.log (p R j) / L R) hC β
  rw [packetPhase] at hB1
  generalize ∑ j ∈ s R, (v R j : ℂ) * cexp (((Real.log (p R j) - L R) * β : ℝ) * I) = B at hB1 ⊢
  generalize ∑ j ∈ s R, (v R j : ℂ) * ((Real.log (p R j) / L R : ℝ) : ℂ) *
    cexp (((Real.log (p R j) - L R) * β : ℝ) * I) = Q at hB2 ⊢
  generalize ∑ j ∈ s R, (v R j : ℂ) * (((p R j)⁻¹ : ℝ) : ℂ) *
    cexp (-(Real.log (p R j) * β * I)) = N₁ at hN₁ ⊢
  generalize ∑ j ∈ s R, (v R j : ℂ) * (((p R j)⁻¹ : ℝ) : ℂ) * ((Real.log (p R j) / L R : ℝ) : ℂ) *
    cexp (-(Real.log (p R j) * β * I)) = N₂ at hN₂ ⊢
  have hid : z - (e * B * z + μ * (e * Q)) / 2 - (N₁ * z - μ * N₂) / 2 - (z - e * (z + μ) / 2) =
      -(e * (B - 1) * z + μ * (e * (Q - 1))) / 2 - (N₁ * z - μ * N₂) / 2 := by ring
  rw [hid]
  have hμ : ‖(μ : ℂ)‖ = |μ| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hN₁' : ‖N₁‖ ≤ η' / 2 := by linarith
  have hN₂' : ‖N₂‖ ≤ η' := by linarith
  calc ‖-(e * (B - 1) * z + μ * (e * (Q - 1))) / 2 - (N₁ * z - μ * N₂) / 2‖
      ≤ (‖B - 1‖ * ‖z‖ + |μ| * ‖Q - 1‖ + ‖N₁‖ * ‖z‖ + |μ| * ‖N₂‖) / 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_div, norm_div, norm_neg, Complex.norm_ofNat]
        have h1 := norm_add_le (e * (B - 1) * z) (μ * (e * (Q - 1)))
        have h2 := norm_sub_le (N₁ * z) (μ * N₂)
        simp only [norm_mul, hen, one_mul, hμ] at h1 h2
        linarith
    _ ≤ (η' * M + |μ| * η' + η' / 2 * M + |μ| * η') / 2 := by
        have := abs_nonneg μ
        have h1 := mul_le_mul hB1 hzM (norm_nonneg _) hη'0.le
        have h2 := mul_le_mul_of_nonneg_left hB2 this
        have h3 := mul_le_mul hN₁' hzM (norm_nonneg _) (by positivity)
        have h4 := mul_le_mul_of_nonneg_left hN₂' this
        linarith
    _ ≤ η * (1 + |μ|) := by
        have := abs_nonneg μ
        nlinarith

/-- **Log-narrow packets inherit the obstruction.** If `δ_R → 0` and `L_R → ∞`, then for all
large `R` and **every** real gauge the packet port has a negative strip defect. -/
theorem eventually_lognarrow_packet_defect (hv : ∀ R, ∀ j ∈ s R, 0 ≤ v R j)
    (hs : ∀ R, ∑ j ∈ s R, v R j = 1) (hp : ∀ R, ∀ j ∈ s R, 0 < p R j)
    (hδ : ∀ R, ∀ j ∈ s R, |Real.log (p R j) - L R| ≤ δ R) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hL : Tendsto L atTop atTop) :
    ∀ᶠ R in atTop, ∀ μ : ℝ, ∃ w : ℂ, 0 < w.re ∧ w.re < 1 / 2 ∧
      portImbalance (packetGaugePort (s R) (v R) (p R) (L R) μ) w < 0 := by
  obtain ⟨h1, h2⟩ := thetaPortLogDeriv_cone_two
  have H := eventually_packet_threshold (h := 2) (c := 3 / 4) (by norm_num) (by linarith)
    (by linarith) hv hs hp hδ (hδ0.div_atTop hL) hL
  filter_upwards [H, hδ0.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 8))]
    with R hR hR8
  refine hR ?_
  have := norm_packetPhase_sub_le (hv R) (hs R) (hδ R) 2 0
  rw [packetPhase_zero, ← Complex.ofReal_sum, hs R, Complex.ofReal_one, sub_zero,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] at this
  have h3 := norm_sub_norm_le (1 : ℂ) (packetPhase (s R) (v R) (p R) (L R) 2)
  rw [norm_one, norm_sub_rev] at h3
  linarith

theorem thetaPortLogDeriv_two_threshold_lt :
    2 * (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).re / (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).im <
      8 / 11 := by
  obtain ⟨h1, h2⟩ := thetaPortLogDeriv_cone_two
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-- **(30)** at height `2`: every `c > 2a₀/b₀` is a coherence threshold. -/
theorem eventually_packet_coherence_defect (hv : ∀ R, ∀ j ∈ s R, 0 ≤ v R j)
    (hs : ∀ R, ∑ j ∈ s R, v R j = 1) (hp : ∀ R, ∀ j ∈ s R, 0 < p R j)
    (hδ : ∀ R, ∀ j ∈ s R, |Real.log (p R j) - L R| ≤ δ R)
    (hδL : Tendsto (fun R => δ R / L R) atTop (𝓝 0)) (hL : Tendsto L atTop atTop) {c : ℝ}
    (hc : 2 * (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).re /
      (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).im < c) :
    ∀ᶠ R in atTop, c ≤ ‖packetPhase (s R) (v R) (p R) (L R) 2‖ → ∀ μ : ℝ,
      ∃ w : ℂ, 0 < w.re ∧ w.re < 1 / 2 ∧
        portImbalance (packetGaugePort (s R) (v R) (p R) (L R) μ) w < 0 := by
  obtain ⟨h1, h2⟩ := thetaPortLogDeriv_cone_two
  have hb : 0 < (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).im := by linarith
  have hc0 : 0 < c := lt_of_le_of_lt (by positivity) hc
  rw [div_lt_iff₀ hb] at hc
  exact eventually_packet_threshold hc0 hb (by linarith) hv hs hp hδ hδL hL

/-- **(31).** Cofinal strip order forces `limsup |B_R(2)| ≤ 2a₀/b₀ < 8/11`: every `c > 2a₀/b₀`
eventually bounds `|B_R(2)|`. -/
theorem eventually_norm_packetPhase_lt_of_order (hv : ∀ R, ∀ j ∈ s R, 0 ≤ v R j)
    (hs : ∀ R, ∑ j ∈ s R, v R j = 1) (hp : ∀ R, ∀ j ∈ s R, 0 < p R j)
    (hδ : ∀ R, ∀ j ∈ s R, |Real.log (p R j) - L R| ≤ δ R)
    (hδL : Tendsto (fun R => δ R / L R) atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hord : ∀ᶠ R in atTop, ∃ μ : ℝ, ∀ w : ℂ, 0 < w.re → w.re < 1 / 2 →
      0 ≤ portImbalance (packetGaugePort (s R) (v R) (p R) (L R) μ) w) {c : ℝ}
    (hc : 2 * (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).re /
      (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).im < c) :
    ∀ᶠ R in atTop, ‖packetPhase (s R) (v R) (p R) (L R) 2‖ < c := by
  filter_upwards [eventually_packet_coherence_defect hv hs hp hδ hδL hL hc, hord]
    with R hR ⟨μ, hμ⟩
  by_contra hlt
  obtain ⟨w, hw1, hw2, hw3⟩ := hR (not_lt.mp hlt) μ
  exact (hμ w hw1 hw2).not_gt hw3

/-- **(32).** Cofinal strip order forces the log spread: for every `c ∈ (2a₀/b₀, 1]`,
eventually `2δ_R ≥ arccos c`. -/
theorem eventually_arccos_le_width_of_order (hv : ∀ R, ∀ j ∈ s R, 0 ≤ v R j)
    (hs : ∀ R, ∑ j ∈ s R, v R j = 1) (hp : ∀ R, ∀ j ∈ s R, 0 < p R j)
    (hδ : ∀ R, ∀ j ∈ s R, |Real.log (p R j) - L R| ≤ δ R)
    (hδL : Tendsto (fun R => δ R / L R) atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hord : ∀ᶠ R in atTop, ∃ μ : ℝ, ∀ w : ℂ, 0 < w.re → w.re < 1 / 2 →
      0 ≤ portImbalance (packetGaugePort (s R) (v R) (p R) (L R) μ) w) {c : ℝ}
    (hc : 2 * (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).re /
      (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).im < c) (hc1 : c ≤ 1) :
    ∀ᶠ R in atTop, Real.arccos c ≤ 2 * δ R := by
  obtain ⟨h1, h2⟩ := thetaPortLogDeriv_cone_two
  have hc0 : 0 < c := lt_of_le_of_lt (div_nonneg (by linarith) (by linarith)) hc
  filter_upwards [eventually_norm_packetPhase_lt_of_order hv hs hp hδ hδL hL hord hc] with R hR
  by_contra hlt
  push Not at hlt
  have hδ0 := width_nonneg (hs R) (hδ R)
  have hπ : 2 * δ R ≤ Real.pi := hlt.le.trans (Real.arccos_le_pi c)
  have hcos := cos_le_re_packetPhase (hv R) (hs R) (hδ R) (β := 2) (by norm_num) hπ
  have hlt' := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (Real.arccos_le_pi c) hlt
  rw [Real.cos_arccos (by linarith) hc1] at hlt'
  have hre := (le_abs_self _).trans (Complex.abs_re_le_norm (packetPhase (s R) (v R) (p R) (L R) 2))
  linarith

/-- **(32), liminf form.** `liminf 2δ_R ≥ arccos(2a₀/b₀)`. -/
theorem eventually_width_ge_of_order (hv : ∀ R, ∀ j ∈ s R, 0 ≤ v R j)
    (hs : ∀ R, ∑ j ∈ s R, v R j = 1) (hp : ∀ R, ∀ j ∈ s R, 0 < p R j)
    (hδ : ∀ R, ∀ j ∈ s R, |Real.log (p R j) - L R| ≤ δ R)
    (hδL : Tendsto (fun R => δ R / L R) atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hord : ∀ᶠ R in atTop, ∃ μ : ℝ, ∀ w : ℂ, 0 < w.re → w.re < 1 / 2 →
      0 ≤ portImbalance (packetGaugePort (s R) (v R) (p R) (L R) μ) w) {θ : ℝ}
    (hθ : θ < Real.arccos (2 * (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).re /
      (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).im)) :
    ∀ᶠ R in atTop, θ ≤ 2 * δ R := by
  set x₀ := 2 * (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).re /
    (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).im
  have hx₀ : x₀ < 1 := thetaPortLogDeriv_two_threshold_lt.trans (by norm_num)
  have hev : ∀ᶠ x in 𝓝[>] x₀, θ < Real.arccos x ∧ x < 1 :=
    ((Real.continuous_arccos.tendsto x₀).eventually (lt_mem_nhds hθ)).and
      (eventually_lt_nhds hx₀) |>.filter_mono nhdsWithin_le_nhds
  obtain ⟨c, ⟨hc1, hc2⟩, hc3⟩ := (hev.and self_mem_nhdsWithin).exists
  filter_upwards [eventually_arccos_le_width_of_order hv hs hp hδ hδL hL hord hc3 hc2.le]
    with R hR
  linarith

theorem arccos_eight_elevenths_lt :
    Real.arccos (8 / 11) < Real.arccos (2 * (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).re /
      (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).im) := by
  obtain ⟨h1, h2⟩ := thetaPortLogDeriv_cone_two
  exact Real.arccos_lt_arccos (by
    have : 0 ≤ 2 * (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).re /
      (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).im := div_nonneg (by linarith) (by linarith)
    linarith) thetaPortLogDeriv_two_threshold_lt (by norm_num)

/-- **(32), explicit.** Cofinal strip order forces `2δ_R > arccos(8/11)` eventually; in
particular `max_j p_{R,j} / min_j p_{R,j} ↛ 1`. -/
theorem eventually_width_gt_arccos_of_order (hv : ∀ R, ∀ j ∈ s R, 0 ≤ v R j)
    (hs : ∀ R, ∑ j ∈ s R, v R j = 1) (hp : ∀ R, ∀ j ∈ s R, 0 < p R j)
    (hδ : ∀ R, ∀ j ∈ s R, |Real.log (p R j) - L R| ≤ δ R)
    (hδL : Tendsto (fun R => δ R / L R) atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hord : ∀ᶠ R in atTop, ∃ μ : ℝ, ∀ w : ℂ, 0 < w.re → w.re < 1 / 2 →
      0 ≤ portImbalance (packetGaugePort (s R) (v R) (p R) (L R) μ) w) :
    ∀ᶠ R in atTop, Real.arccos (8 / 11) < 2 * δ R := by
  have h := arccos_eight_elevenths_lt
  filter_upwards [eventually_width_ge_of_order hv hs hp hδ hδL hL hord
    (θ := (Real.arccos (8 / 11) + Real.arccos (2 * (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).re /
      (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).im)) / 2) (by linarith)] with R hR
  linarith

end Sequences

end

end RHTower
