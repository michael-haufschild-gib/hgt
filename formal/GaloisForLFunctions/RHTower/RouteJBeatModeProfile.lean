import GaloisForLFunctions.RHTower.LegendreLaplaceHeine
import GaloisForLFunctions.RHTower.SemilocalDiagonalLegendre

/-!
# Route J: the beat-mode (fixed-`δ`) profile of the critical residual

For a fixed rapidity `δ = log(p₂/p₁) > 0` put `σ = 1/cosh δ`, `τ = tanh δ` and `φ = arccos σ`
(so `cos φ = σ`, `sin φ = τ`).  The Route J critical residual jet at the cosine mode is the exact
Legendre combination `residualJetOf_cosineMode_eq_legendre`

`J_k(δ) = σ^{1/2} [ r_{2k} r_{2k+1} (P_{4k+4} − P_{4k}) − 2 r_{2k+1}² (P_{4k+4} − P_{4k+2})
              − 2 r_{2k+2}² (P_{4k+6} − P_{4k+4}) + r_{2k+2} r_{2k+3} (P_{4k+8} − P_{4k+4}) ](σ)`.

Laplace–Heine asymptotics `legendre_laplaceHeine` of `P_{4k+j}(σ)`, the Wallis limit
`√(4k) C_{4k} → 1/√π`, the radius asymptotics `r_{2k+a} ∼ 2k` and the trigonometric identity
`−cos(χ−4φ) + 2cos(χ−2φ) − 2cos(χ+2φ) + cos(χ+4φ) = 8 sin 2φ sin²φ sin χ` give the **beat-mode law**

`J_k(δ) / k^{3/2} − 32 √(2/π) σ^{3/2} τ^{5/2} sin((4k + 9/2) φ − π/4) → 0`.

The residual oscillates with the beat frequency `4φ = 4 arccos(sech δ)` per unit of `k`, at amplitude
`32 √(2/π) σ^{3/2} τ^{5/2} k^{3/2}`: the fixed-`δ` counterpart of the scaling profile `Φ`.
-/

open Filter Topology Finset
open scoped Real

namespace RHTower
namespace RouteJBeatMode

open LegendreBoost RouteJProfile CosineModeResponse

/-! ## The beat angle -/

/-- `φ(δ) = arccos(1/cosh δ)`. -/
noncomputable def beatAngle (δ : ℝ) : ℝ := Real.arccos (1 / Real.cosh δ)

theorem sech_pos' (δ : ℝ) : 0 < 1 / Real.cosh δ := by
  have := Real.cosh_pos δ
  positivity

theorem sech_le_one' (δ : ℝ) : 1 / Real.cosh δ ≤ 1 := by
  rw [div_le_one (Real.cosh_pos δ)]
  exact Real.one_le_cosh δ

theorem cos_beatAngle (δ : ℝ) : Real.cos (beatAngle δ) = 1 / Real.cosh δ :=
  Real.cos_arccos (by linarith [sech_pos' δ]) (sech_le_one' δ)

theorem tanh_pos' {δ : ℝ} (hδ : 0 < δ) : 0 < Real.tanh δ := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hδ) (Real.cosh_pos δ)

theorem sin_beatAngle {δ : ℝ} (hδ : 0 ≤ δ) : Real.sin (beatAngle δ) = Real.tanh δ := by
  unfold beatAngle
  rw [Real.sin_arccos, Real.tanh_eq_sinh_div_cosh]
  have hc := Real.cosh_pos δ
  have hs := Real.sinh_nonneg_iff.mpr hδ
  have hsq := Real.cosh_sq δ
  have : 1 - (1 / Real.cosh δ) ^ 2 = (Real.sinh δ / Real.cosh δ) ^ 2 := by
    field_simp
    linear_combination hsq
  rw [this, Real.sqrt_sq (div_nonneg hs hc.le)]

theorem beatAngle_pos {δ : ℝ} (hδ : 0 < δ) : 0 < beatAngle δ := by
  unfold beatAngle
  rw [Real.arccos_pos, div_lt_one (Real.cosh_pos δ)]
  exact Real.one_lt_cosh.mpr hδ.ne'

theorem beatAngle_lt_pi (δ : ℝ) : beatAngle δ < π := by
  unfold beatAngle
  rw [Real.arccos_lt_pi]
  linarith [sech_pos' δ]

theorem sin_beatAngle_pos {δ : ℝ} (hδ : 0 < δ) : 0 < Real.sin (beatAngle δ) :=
  Real.sin_pos_of_pos_of_lt_pi (beatAngle_pos hδ) (beatAngle_lt_pi δ)

/-! ## Sequences -/

/-- The Laplace–Heine phase `θ_{k,j} = (4k + j + ½) φ − π/4`. -/
noncomputable def beatPhase (δ : ℝ) (k j : ℕ) : ℝ :=
  (((4 * k + j : ℕ) : ℝ) + 1 / 2) * beatAngle δ - π / 4

/-- `(2 sin φ)^{-1/2}`. -/
noncomputable def beatSfac (δ : ℝ) : ℝ := (2 * Real.sin (beatAngle δ)) ^ (-(1 / 2 : ℝ))

/-- `P_{4k+j}(σ)`. -/
noncomputable def beatLegendre (δ : ℝ) (k j : ℕ) : ℝ := legendre (4 * k + j) (1 / Real.cosh δ)

/-- The uniform-`C_{4k}` Laplace–Heine model `2 C_{4k} (2 sin φ)^{-1/2} cos θ_{k,j}`. -/
noncomputable def beatModel (δ : ℝ) (k j : ℕ) : ℝ :=
  2 * cb (4 * k) * beatSfac δ * Real.cos (beatPhase δ k j)

/-- The Wallis sequence `√k C_{4k}`. -/
noncomputable def wallisSeq (k : ℕ) : ℝ := Real.sqrt k * cb (4 * k)

/-- `√k (P_{4k+j} − model)`. -/
noncomputable def beatEmod (δ : ℝ) (k j : ℕ) : ℝ :=
  Real.sqrt k * (beatLegendre δ k j - beatModel δ k j)

/-- `√k · model`. -/
noncomputable def beatDmod (δ : ℝ) (k j : ℕ) : ℝ := Real.sqrt k * beatModel δ k j

/-- `r_{2k+a} r_{2k+b} / k²`. -/
noncomputable def beatQuot (k a b : ℕ) : ℝ :=
  semilocalArchimedeanJacobiCoefficient (2 * k + a) *
    semilocalArchimedeanJacobiCoefficient (2 * k + b) / (k : ℝ) ^ 2

/-- The beat-mode amplitude `32 √(2/π) σ^{3/2} τ^{5/2}`. -/
noncomputable def beatModeAmplitude (δ : ℝ) : ℝ :=
  32 * Real.sqrt (2 / π) * (1 / Real.cosh δ) ^ (3 / 2 : ℝ) * Real.tanh δ ^ (5 / 2 : ℝ)

/-! ## Wallis and ratio limits -/

theorem tendsto_wallisSeq : Tendsto wallisSeq atTop (𝓝 (1 / (2 * Real.sqrt π))) := by
  have h4 : Tendsto (fun k : ℕ => 4 * k) atTop atTop :=
    tendsto_id.const_mul_atTop' (by norm_num)
  have h := (GaloisForLFunctions.HTGeometry.tendsto_sqrtNat_mul_normalizedCentralBinom.comp h4).const_mul
    (1 / 2 : ℝ)
  have hlim : (1 / 2 : ℝ) * (1 / Real.sqrt π) = 1 / (2 * Real.sqrt π) := by ring
  rw [hlim] at h
  refine h.congr' (Eventually.of_forall fun k => ?_)
  show (1 / 2 : ℝ) * (Real.sqrt ((4 * k : ℕ) : ℝ) * cb (4 * k)) = wallisSeq k
  unfold wallisSeq
  rw [show ((4 * k : ℕ) : ℝ) = 4 * (k : ℝ) by push_cast; ring, Real.sqrt_mul (by norm_num),
    show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  ring

theorem abs_wallisSeq_le (k : ℕ) : |wallisSeq k| ≤ 1 := by
  unfold wallisSeq
  have hcb := cb_le_inv_sqrt (4 * k)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hpos : 0 < Real.sqrt (2 * ((4 * k : ℕ) : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (cb_pos _).le)]
  calc Real.sqrt k * cb (4 * k) ≤ Real.sqrt k * (1 / Real.sqrt (2 * ((4 * k : ℕ) : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hcb (Real.sqrt_nonneg _)
    _ = Real.sqrt k / Real.sqrt (2 * ((4 * k : ℕ) : ℝ) + 1) := by ring
    _ ≤ 1 := by
        rw [div_le_one hpos]
        apply Real.sqrt_le_sqrt
        push_cast
        linarith

theorem tendsto_cb_ratio_four (j : ℕ) :
    Tendsto (fun k : ℕ => cb (4 * k + j) / cb (4 * k)) atTop (𝓝 1) := by
  induction j with
  | zero =>
    have : (fun k : ℕ => cb (4 * k + 0) / cb (4 * k)) = fun _ => 1 := by
      funext k
      rw [Nat.add_zero, div_self (cb_pos _).ne']
    rw [this]
    exact tendsto_const_nhds
  | succ j ih =>
    have hN : Tendsto (fun k : ℕ => ((4 * k + j : ℕ) : ℝ)) atTop atTop := by
      have := ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop'
        (by norm_num : (0 : ℝ) < 4)).atTop_add (tendsto_const_nhds (x := (j : ℝ)))
      refine this.congr' (Eventually.of_forall fun k => ?_)
      push_cast
      ring
    have hρ : Tendsto (fun k : ℕ => (2 * ((4 * k + j : ℕ) : ℝ) + 1) /
        (2 * (((4 * k + j : ℕ) : ℝ) + 1))) atTop (𝓝 1) := by
      have hden : Tendsto (fun k : ℕ => 2 * (((4 * k + j : ℕ) : ℝ) + 1)) atTop atTop :=
        (hN.atTop_add tendsto_const_nhds).const_mul_atTop' (by norm_num)
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_inv_atTop_zero.comp hden)
      rw [sub_zero] at this
      refine this.congr' (Eventually.of_forall fun k => ?_)
      simp only [Function.comp]
      have : (0 : ℝ) < 2 * (((4 * k + j : ℕ) : ℝ) + 1) := by positivity
      field_simp
      ring
    have hfun : (fun k : ℕ => cb (4 * k + (j + 1)) / cb (4 * k)) =
        fun k => cb (4 * k + j) / cb (4 * k) *
          ((2 * ((4 * k + j : ℕ) : ℝ) + 1) / (2 * (((4 * k + j : ℕ) : ℝ) + 1))) := by
      funext k
      rw [show 4 * k + (j + 1) = 4 * k + j + 1 by ring, cb_succ]
      have := (cb_pos (4 * k)).ne'
      field_simp
    rw [hfun]
    simpa using ih.mul hρ

/-! ## Laplace–Heine input -/

theorem tendsto_sqrt_mul_beatErr {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    Tendsto (fun k : ℕ => Real.sqrt k *
      (beatLegendre δ k j - 2 * cb (4 * k + j) * beatSfac δ * Real.cos (beatPhase δ k j)))
      atTop (𝓝 0) := by
  have hφ0 := beatAngle_pos hδ
  have hφπ := beatAngle_lt_pi δ
  have hs := sin_beatAngle_pos hδ
  have hlim : Tendsto (fun k : ℕ => (100 / Real.sin (beatAngle δ)) * Real.sqrt (1 / (k : ℝ)))
      atTop (𝓝 0) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).sqrt
    rw [Real.sqrt_zero] at this
    simpa using this.const_mul (100 / Real.sin (beatAngle δ))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hN : 8 ≤ 4 * k + j := by omega
  have hLH := legendre_laplaceHeine hφ0 hφπ hN
  rw [cos_beatAngle] at hLH
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  unfold beatLegendre beatSfac beatPhase
  have hNpos : (0 : ℝ) < ((4 * k + j : ℕ) : ℝ) := by positivity
  calc Real.sqrt k * |legendre (4 * k + j) (1 / Real.cosh δ) -
        2 * cb (4 * k + j) * (2 * Real.sin (beatAngle δ)) ^ (-(1 / 2 : ℝ)) *
          Real.cos ((((4 * k + j : ℕ) : ℝ) + 1 / 2) * beatAngle δ - π / 4)|
      ≤ Real.sqrt k * (400 / (Real.sin (beatAngle δ) * ((4 * k + j : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hLH (Real.sqrt_nonneg _)
    _ = (100 / Real.sin (beatAngle δ)) * (4 * Real.sqrt k / ((4 * k + j : ℕ) : ℝ)) := by
        rw [div_mul_div_comm, mul_div_assoc']
        congr 1
        ring
    _ ≤ (100 / Real.sin (beatAngle δ)) * (4 * Real.sqrt k / (4 * (k : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        push_cast
        linarith
    _ = (100 / Real.sin (beatAngle δ)) * Real.sqrt (1 / (k : ℝ)) := by
        congr 1
        rw [one_div, Real.sqrt_inv]
        have hsq := Real.mul_self_sqrt hk0.le
        have hs0 : Real.sqrt k ≠ 0 := (Real.sqrt_pos.mpr hk0).ne'
        field_simp
        linear_combination hsq

theorem tendsto_beatEmod {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    Tendsto (fun k : ℕ => beatEmod δ k j) atTop (𝓝 0) := by
  have h1 := tendsto_sqrt_mul_beatErr hδ j
  have h2 : Tendsto (fun k : ℕ => wallisSeq k * (cb (4 * k + j) / cb (4 * k) - 1)) atTop (𝓝 0) := by
    have := tendsto_wallisSeq.mul ((tendsto_cb_ratio_four j).sub_const 1)
    simpa using this
  have hb : IsBoundedUnder (· ≤ ·) atTop
      ((fun x => ‖x‖) ∘ fun k : ℕ => 2 * beatSfac δ * Real.cos (beatPhase δ k j)) :=
    isBoundedUnder_of ⟨2 * |beatSfac δ|, fun k => by
      simp only [Function.comp, Real.norm_eq_abs, abs_mul, abs_two]
      have := Real.abs_cos_le_one (beatPhase δ k j)
      nlinarith [abs_nonneg (beatSfac δ)]⟩
  have h3 := h2.zero_mul_isBoundedUnder_le hb
  have := h1.add h3
  rw [add_zero] at this
  refine this.congr' (Eventually.of_forall fun k => ?_)
  simp only [beatEmod, beatModel, wallisSeq]
  have hcb := (cb_pos (4 * k)).ne'
  field_simp
  ring

theorem abs_beatDmod_sub_le (δ : ℝ) (k a b : ℕ) :
    |beatDmod δ k a - beatDmod δ k b| ≤ 4 * |beatSfac δ| := by
  have h : beatDmod δ k a - beatDmod δ k b =
      2 * beatSfac δ * wallisSeq k * (Real.cos (beatPhase δ k a) - Real.cos (beatPhase δ k b)) := by
    simp only [beatDmod, beatModel, wallisSeq]
    ring
  rw [h, abs_mul, abs_mul, abs_mul, abs_two]
  have h1 := abs_wallisSeq_le k
  have h2 : |Real.cos (beatPhase δ k a) - Real.cos (beatPhase δ k b)| ≤ 2 :=
    abs_le.mpr ⟨by linarith [Real.cos_le_one (beatPhase δ k b), Real.neg_one_le_cos (beatPhase δ k a)],
      by linarith [Real.cos_le_one (beatPhase δ k a), Real.neg_one_le_cos (beatPhase δ k b)]⟩
  calc 2 * |beatSfac δ| * |wallisSeq k| * |Real.cos (beatPhase δ k a) - Real.cos (beatPhase δ k b)|
      ≤ 2 * |beatSfac δ| * 1 * |Real.cos (beatPhase δ k a) - Real.cos (beatPhase δ k b)| := by
        gcongr
    _ ≤ 2 * |beatSfac δ| * 1 * 2 := by gcongr
    _ = 4 * |beatSfac δ| := by ring

/-! ## Radius asymptotics -/

theorem tendsto_r_div_nat (a : ℕ) :
    Tendsto (fun k : ℕ => semilocalArchimedeanJacobiCoefficient (2 * k + a) / (k : ℝ)) atTop (𝓝 2) := by
  have hinv : Tendsto (fun k : ℕ => 1 / (k : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hlim := ((tendsto_const_nhds (x := (2 : ℝ))).add (hinv.const_mul ((a : ℝ) + 1 / 2))).mul
    ((tendsto_const_nhds (x := (2 : ℝ))).add (hinv.const_mul ((a : ℝ) + 1))) |>.sqrt
  have h4 : Real.sqrt ((2 + ((a : ℝ) + 1 / 2) * 0) * (2 + ((a : ℝ) + 1) * 0)) = 2 := by
    rw [show (2 + ((a : ℝ) + 1 / 2) * 0) * (2 + ((a : ℝ) + 1) * 0) = 2 ^ 2 by ring]
    exact Real.sqrt_sq (by norm_num)
  rw [h4] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hr := semilocalArchimedeanJacobiCoefficient_sq (2 * k + a)
  have hr0 := (semilocalArchimedeanJacobiCoefficient_pos (2 * k + a)).le
  have hid : (2 + ((a : ℝ) + 1 / 2) * (1 / (k : ℝ))) * (2 + ((a : ℝ) + 1) * (1 / (k : ℝ))) =
      (((2 * k + a : ℕ) : ℝ) + 1 / 2) * (((2 * k + a : ℕ) : ℝ) + 1) / (k : ℝ) ^ 2 := by
    push_cast
    field_simp
    ring
  rw [hid, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hk0.le, ← hr, Real.sqrt_sq hr0]

theorem tendsto_beatQuot (a b : ℕ) : Tendsto (fun k : ℕ => beatQuot k a b) atTop (𝓝 4) := by
  have := (tendsto_r_div_nat a).mul (tendsto_r_div_nat b)
  rw [show (2 : ℝ) * 2 = 4 by norm_num] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold beatQuot
  field_simp

/-! ## The trigonometric beat identity -/

theorem beat_trig_identity (χ φ : ℝ) :
    -Real.cos (χ - 4 * φ) + 2 * Real.cos (χ - 2 * φ) - 2 * Real.cos (χ + 2 * φ) +
      Real.cos (χ + 4 * φ) = 8 * Real.sin (2 * φ) * Real.sin φ ^ 2 * Real.sin χ := by
  have h4c : Real.cos (4 * φ) = 2 * Real.cos (2 * φ) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]
    ring_nf
  have h4s : Real.sin (4 * φ) = 2 * Real.sin (2 * φ) * Real.cos (2 * φ) := by
    rw [← Real.sin_two_mul]
    ring_nf
  rw [Real.cos_sub, Real.cos_sub, Real.cos_add, Real.cos_add, h4c, h4s, Real.cos_two_mul,
    Real.sin_two_mul]
  linear_combination (-16 * Real.sin φ * Real.cos φ * Real.sin χ) * Real.sin_sq_add_cos_sq φ

theorem beatPhase_trig (δ : ℝ) (k : ℕ) :
    -Real.cos (beatPhase δ k 0) + 2 * Real.cos (beatPhase δ k 2) - 2 * Real.cos (beatPhase δ k 6) +
      Real.cos (beatPhase δ k 8) =
      8 * Real.sin (2 * beatAngle δ) * Real.sin (beatAngle δ) ^ 2 * Real.sin (beatPhase δ k 4) := by
  have h0 : beatPhase δ k 0 = beatPhase δ k 4 - 4 * beatAngle δ := by unfold beatPhase; push_cast; ring
  have h2 : beatPhase δ k 2 = beatPhase δ k 4 - 2 * beatAngle δ := by unfold beatPhase; push_cast; ring
  have h6 : beatPhase δ k 6 = beatPhase δ k 4 + 2 * beatAngle δ := by unfold beatPhase; push_cast; ring
  have h8 : beatPhase δ k 8 = beatPhase δ k 4 + 4 * beatAngle δ := by unfold beatPhase; push_cast; ring
  rw [h0, h2, h6, h8]
  exact beat_trig_identity _ _

/-! ## The amplitude -/

theorem beat_rpow_three_half {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hx (by norm_num), Real.rpow_one,
    Real.sqrt_eq_rpow]

theorem beat_rpow_five_half {x : ℝ} (hx : 0 ≤ x) : x ^ (5 / 2 : ℝ) = x ^ 2 * Real.sqrt x := by
  rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add' hx (by norm_num), Real.rpow_two,
    Real.sqrt_eq_rpow]

theorem beat_rpow_neg_half {x : ℝ} (hx : 0 ≤ x) : x ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt x := by
  rw [Real.rpow_neg hx, Real.sqrt_eq_rpow]
  exact (one_div _).symm

theorem beatAmplitude_eq {δ : ℝ} (hδ : 0 < δ) :
    beatModeAmplitude δ = Real.cosh δ ^ (-(1 / 2 : ℝ)) *
      (64 * beatSfac δ * Real.sin (2 * beatAngle δ) * Real.sin (beatAngle δ) ^ 2) *
        (1 / (2 * Real.sqrt π)) := by
  unfold beatModeAmplitude beatSfac
  rw [Real.sin_two_mul, sin_beatAngle hδ.le, cos_beatAngle]
  have hc := Real.cosh_pos δ
  have hτ := tanh_pos' hδ
  rw [beat_rpow_three_half (sech_pos' δ).le, beat_rpow_five_half hτ.le, beat_rpow_neg_half hc.le,
    beat_rpow_neg_half (by positivity : (0 : ℝ) ≤ 2 * Real.tanh δ),
    Real.sqrt_div' 2 Real.pi_pos.le, Real.sqrt_div' 1 hc.le, Real.sqrt_one,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have h2 : Real.sqrt 2 = 2 / Real.sqrt 2 := by
    have := Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have h2p : 0 < Real.sqrt 2 := by positivity
    field_simp
    linear_combination this
  set u := Real.sqrt (Real.tanh δ) with hu
  set v := Real.sqrt (Real.cosh δ) with hv
  have hu0 : 0 < u := Real.sqrt_pos.mpr hτ
  have hv0 : 0 < v := Real.sqrt_pos.mpr hc
  have hτu : Real.tanh δ = u ^ 2 := (Real.sq_sqrt hτ.le).symm
  have hcv : Real.cosh δ = v ^ 2 := (Real.sq_sqrt hc.le).symm
  rw [hτu, hcv]
  have h2p : 0 < Real.sqrt 2 := by positivity
  conv_lhs => rw [h2]
  field_simp
  ring

/-! ## The beat-mode law -/

/-- The remainder that tends to zero. -/
noncomputable def beatRemainder (δ : ℝ) (k : ℕ) : ℝ :=
  beatQuot k 0 1 * (beatEmod δ k 4 - beatEmod δ k 0) -
      2 * (beatQuot k 1 1 * (beatEmod δ k 4 - beatEmod δ k 2)) -
      2 * (beatQuot k 2 2 * (beatEmod δ k 6 - beatEmod δ k 4)) +
      beatQuot k 2 3 * (beatEmod δ k 8 - beatEmod δ k 4) +
    (beatQuot k 0 1 - 4) * (beatDmod δ k 4 - beatDmod δ k 0) -
      2 * ((beatQuot k 1 1 - 4) * (beatDmod δ k 4 - beatDmod δ k 2)) -
      2 * ((beatQuot k 2 2 - 4) * (beatDmod δ k 6 - beatDmod δ k 4)) +
      (beatQuot k 2 3 - 4) * (beatDmod δ k 8 - beatDmod δ k 4) +
    (64 * beatSfac δ * Real.sin (2 * beatAngle δ) * Real.sin (beatAngle δ) ^ 2) *
      (wallisSeq k - 1 / (2 * Real.sqrt π)) * Real.sin (beatPhase δ k 4)

theorem tendsto_beatRemainder {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k : ℕ => beatRemainder δ k) atTop (𝓝 0) := by
  have hE := tendsto_beatEmod hδ
  have hq := tendsto_beatQuot
  have hD : ∀ a b : ℕ, IsBoundedUnder (· ≤ ·) atTop
      ((fun x => ‖x‖) ∘ fun k : ℕ => beatDmod δ k a - beatDmod δ k b) := fun a b =>
    isBoundedUnder_of ⟨4 * |beatSfac δ|, fun k => by
      simpa [Function.comp, Real.norm_eq_abs] using abs_beatDmod_sub_le δ k a b⟩
  have hS : IsBoundedUnder (· ≤ ·) atTop
      ((fun x => ‖x‖) ∘ fun k : ℕ => Real.sin (beatPhase δ k 4)) :=
    isBoundedUnder_of ⟨1, fun k => by
      simpa [Function.comp, Real.norm_eq_abs] using Real.abs_sin_le_one (beatPhase δ k 4)⟩
  have hq0 : ∀ a b : ℕ, Tendsto (fun k : ℕ => beatQuot k a b - 4) atTop (𝓝 0) := fun a b => by
    have := (hq a b).sub_const 4
    rwa [sub_self] at this
  have hW : Tendsto (fun k : ℕ => (64 * beatSfac δ * Real.sin (2 * beatAngle δ) *
      Real.sin (beatAngle δ) ^ 2) * (wallisSeq k - 1 / (2 * Real.sqrt π))) atTop (𝓝 0) := by
    have := (tendsto_wallisSeq.sub_const (1 / (2 * Real.sqrt π))).const_mul
      (64 * beatSfac δ * Real.sin (2 * beatAngle δ) * Real.sin (beatAngle δ) ^ 2)
    rwa [sub_self, mul_zero] at this
  have t1 := (hq 0 1).mul ((hE 4).sub (hE 0))
  have t2 := (hq 1 1).mul ((hE 4).sub (hE 2))
  have t3 := (hq 2 2).mul ((hE 6).sub (hE 4))
  have t4 := (hq 2 3).mul ((hE 8).sub (hE 4))
  have u1 := (hq0 0 1).zero_mul_isBoundedUnder_le (hD 4 0)
  have u2 := (hq0 1 1).zero_mul_isBoundedUnder_le (hD 4 2)
  have u3 := (hq0 2 2).zero_mul_isBoundedUnder_le (hD 6 4)
  have u4 := (hq0 2 3).zero_mul_isBoundedUnder_le (hD 8 4)
  have w1 := hW.zero_mul_isBoundedUnder_le hS
  have := (((((((t1.sub (t2.const_mul 2)).sub (t3.const_mul 2)).add t4).add u1).sub
    (u2.const_mul 2)).sub (u3.const_mul 2)).add u4).add w1
  simpa only [beatRemainder, sub_self, mul_zero, sub_zero, add_zero, zero_add] using this

theorem beatRemainder_identity {δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : 1 ≤ k) :
    residualJetOf (cosineModeDeterminantJet δ) k / (k : ℝ) ^ (3 / 2 : ℝ) -
        beatModeAmplitude δ * Real.sin ((4 * (k : ℝ) + 9 / 2) * beatAngle δ - π / 4) =
      Real.cosh δ ^ (-(1 / 2 : ℝ)) * beatRemainder δ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk32 : (k : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt k ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hk0.le]
    norm_num
  have hχ : (4 * (k : ℝ) + 9 / 2) * beatAngle δ - π / 4 = beatPhase δ k 4 := by
    unfold beatPhase
    push_cast
    ring
  have htrig := beatPhase_trig δ k
  have hc0 : Real.cos (beatPhase δ k 0) = 2 * Real.cos (beatPhase δ k 2) -
      2 * Real.cos (beatPhase δ k 6) + Real.cos (beatPhase δ k 8) -
      8 * Real.sin (2 * beatAngle δ) * Real.sin (beatAngle δ) ^ 2 * Real.sin (beatPhase δ k 4) := by
    linarith
  rw [hχ, beatAmplitude_eq hδ, residualJetOf_cosineMode_eq_legendre, hk32]
  simp only [beatRemainder, beatQuot, beatEmod, beatDmod, beatModel, beatLegendre, wallisSeq,
    Nat.add_zero]
  rw [hc0]
  set t := Real.sqrt k with ht
  have ht0 : t ≠ 0 := (Real.sqrt_pos.mpr hk0).ne'
  have hkt : (k : ℝ) = t ^ 2 := (Real.sq_sqrt hk0.le).symm
  rw [hkt]
  have hcb := (cb_pos (4 * k)).ne'
  have hπ : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp
  ring

/-- **The beat-mode law of the Route J residual.**  For every fixed rapidity `δ > 0`, with
`σ = 1/cosh δ`, `τ = tanh δ`, `φ = arccos σ`,

`J_k(δ) / k^{3/2} − 32 √(2/π) σ^{3/2} τ^{5/2} sin((4k + 9/2) φ − π/4) → 0`  as `k → ∞`. -/
theorem tendsto_beatMode_profile {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k : ℕ => residualJetOf (cosineModeDeterminantJet δ) k / (k : ℝ) ^ (3 / 2 : ℝ) -
      32 * Real.sqrt (2 / π) * (1 / Real.cosh δ) ^ (3 / 2 : ℝ) * Real.tanh δ ^ (5 / 2 : ℝ) *
        Real.sin ((4 * (k : ℝ) + 9 / 2) * Real.arccos (1 / Real.cosh δ) - π / 4)) atTop (𝓝 0) := by
  have hmain := (tendsto_beatRemainder hδ).const_mul (Real.cosh δ ^ (-(1 / 2 : ℝ)))
  rw [mul_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  rw [← beatRemainder_identity hδ hk]
  rfl

end RouteJBeatMode
end RHTower
