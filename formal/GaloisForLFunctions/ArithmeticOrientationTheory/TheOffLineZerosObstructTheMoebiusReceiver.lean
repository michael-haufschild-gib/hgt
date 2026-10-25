import GaloisForLFunctions.ArithmeticOrientationTheory.UnpayabilityIsLocatedOnTheBohrPolydisk
import GaloisForLFunctions.TransHorizonIncidenceMechanics.APaidReceiverContinuesTheDirichletSeriesAcrossItsAbscissa
import GaloisForLFunctions.BezoutValuationIncidence.PowerDampedPronicMultiplicativityAndRoutePMBridge
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLineContinuity

/-!
# The off-line zeros obstruct the Möbius receiver

Let `0 < ε < ½` and `μ_ε(d) = μ(d) d^{−ε}` (`pmPowerDampedRealWeight`).  If a critical Wiener
kernel `k` repairs `μ_ε`, the Dirichlet series of `c = k ⋆ μ_ε` is `K(s)/ζ(s + ε)` beyond its
abscissa `1 − ε`, and a paid receiver continues `ζ(s)(C(s) − m)` holomorphically to `Re s > ½`
(`exists_holomorphic_continuation`, Trans-Horizon Incidence Mechanics).  Clearing the pole of
`ζ(s + ε)` with the residue unit `(w − 1)ζ(w)` and propagating the identity from the real segment
`(1 − ε, 1)` across the strip, a zero `ρ` of `ζ` with `½ + ε < Re ρ < 1` forces

    ζ(ρ − ε) · K(ρ − ε) = 0        (`riemannZeta_mul_lSeries_eq_zero_of_repairs`).

At `k = δ₁` this is the zero translation of the power-damped Möbius criterion.  For a general
kernel it says where the obstruction sits:

* **Off-line zeros are obstruction points** (`mem_obstructionHull_moebius_of_zero`): if
  `ζ(ρ) = 0`, `½ + ε < Re ρ < 1` and `ζ(ρ − ε) ≠ 0`, the half-plane point `ρ − ε` lies in the
  obstruction hull of `μ_ε`; every repairing kernel vanishes there.  So `μ_ε` is unpaid, and the
  translated zero is an invariant of its unit orbit (`obstructionHull_unit`).

The index object of the field thus reads the off-line zeros of `ζ` on the actual Möbius source,
one obstruction point per zero.
-/

open Finset ArithmeticFunction LSeries Complex Filter Topology
open scoped LSeries.notation ArithmeticFunction.Moebius

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open TransHorizonIncidenceMechanics WienerAlgebraAt BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ### Dirichlet series of real kernels -/

/-- The complex coefficients of a real kernel. -/
def cplx (f : ℕ → ℝ) : ℕ → ℂ := fun n => (f n : ℂ)

theorem norm_term_cplx (f : ℕ → ℝ) (θ : ℝ) (n : ℕ) :
    ‖term (cplx f) θ n‖ = if n = 0 then 0 else |f n| / (n : ℝ) ^ θ := by
  rw [norm_term_eq, cplx, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]

theorem lSeriesSummable_cplx_iff {f : ℕ → ℝ} {θ : ℝ} (hθ : 0 < θ) :
    LSeriesSummable (cplx f) θ ↔ Summable fun n : ℕ => |f n| * (n : ℝ) ^ (-θ) := by
  rw [← summable_norm_term_iff]
  refine summable_congr fun n => ?_
  rw [norm_term_cplx]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow (neg_ne_zero.2 hθ.ne')]
  · rw [if_neg hn, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

theorem cplx_dirichletConv (a b : ℕ → ℝ) :
    cplx (RHTower.dirichletConv a b) = cplx a ⍟ cplx b := by
  funext n
  rw [LSeries.convolution_def]
  show ((RHTower.dirichletConv a b n : ℝ) : ℂ) =
    ∑ p ∈ n.divisorsAntidiagonal, (a p.1 : ℂ) * (b p.2 : ℂ)
  rw [Nat.sum_divisorsAntidiagonal (fun i j => (a i : ℂ) * (b j : ℂ)), RHTower.dirichletConv,
    Complex.ofReal_sum]
  exact sum_congr rfl fun i _ => Complex.ofReal_mul _ _

/-- The weighted absolute summability of a convolution. -/
theorem summable_abs_dirichletConv_rpow {a b : ℕ → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (ha : Summable fun n : ℕ => |a n| * (n : ℝ) ^ (-θ))
    (hb : Summable fun n : ℕ => |b n| * (n : ℝ) ^ (-θ)) :
    Summable fun n : ℕ => |RHTower.dirichletConv a b n| * (n : ℝ) ^ (-θ) := by
  rw [← lSeriesSummable_cplx_iff hθ, cplx_dirichletConv]
  exact ((lSeriesSummable_cplx_iff hθ).2 ha).convolution ((lSeriesSummable_cplx_iff hθ).2 hb)

/-- A real Dirichlet series at a real point, as a complex L-series. -/
theorem ofReal_tsum_rpow (f : ℕ → ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ((∑' d : ℕ, f d * (d : ℝ) ^ (-σ) : ℝ) : ℂ) = LSeries (cplx f) σ := by
  unfold LSeries
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun d => ?_
  rcases eq_or_ne d 0 with rfl | hd
  · simp [Real.zero_rpow (neg_ne_zero.2 hσ.ne')]
  · rw [term_of_ne_zero hd, cplx, Real.rpow_neg (Nat.cast_nonneg d), ← div_eq_mul_inv,
      Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg d), Complex.ofReal_natCast]

/-- The damped Möbius series is the shifted reciprocal of `ζ`. -/
theorem lSeries_moebius_damped {ε : ℝ} {s : ℂ} (hs : 1 < s.re + ε) :
    LSeries (cplx (pmPowerDampedRealWeight ε)) s = (riemannZeta (s + ε))⁻¹ := by
  have hre : 1 < (s + ε).re := by simpa using hs
  have h1 : LSeries (cplx (pmPowerDampedRealWeight ε)) s = LSeries ↗μ (s + ε) := by
    unfold LSeries
    refine tsum_congr fun d => ?_
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    · rw [term_of_ne_zero hd, term_of_ne_zero hd, cplx, pmPowerDampedRealWeight, moebiusReal]
      have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
      rw [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg d), Complex.ofReal_natCast,
        Complex.cpow_add _ _ hd', Complex.ofReal_neg, Complex.cpow_neg]
      have h1 : (d : ℂ) ^ (s : ℂ) ≠ 0 := by
        rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hd' h.1
      have h2 : (d : ℂ) ^ ((ε : ℝ) : ℂ) ≠ 0 := by
        rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hd' h.1
      push_cast
      field_simp
  rw [h1, ← LSeries_zeta_eq_riemannZeta hre]
  exact eq_inv_of_mul_eq_one_right (LSeries_zeta_mul_Lseries_moebius hre)

/-! ### The kernel continuation identity -/

section Kernel

variable {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {k : ℕ → ℝ} (hk : CriticalWiener k)
include hε hε2 hk

theorem summable_kernel_rpow {θ : ℝ} (hθ : 1 / 2 ≤ θ) :
    Summable fun n : ℕ => |k n| * (n : ℝ) ^ (-θ) :=
  hk.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    fun n => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rcases eq_or_ne θ 0 with rfl | hθ0
        · linarith
        · simp [Real.zero_rpow (neg_ne_zero.2 hθ0)]
      · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast hn) (by linarith)) (abs_nonneg _)

omit hε hε2 hk in
theorem summable_moebius_rpow {θ : ℝ} (hθ : 1 - ε < θ) :
    Summable fun n : ℕ => |pmPowerDampedRealWeight ε n| * (n : ℝ) ^ (-θ) := by
  refine (Real.summable_nat_rpow.mpr (by linarith : -(θ + ε) < -1)).of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pmPowerDampedRealWeight, moebiusReal, ArithmeticFunction.map_zero]
    simp only [Int.cast_zero, zero_mul, abs_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg 0) _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [pmPowerDampedRealWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg hn0.le _), mul_assoc,
    ← Real.rpow_add hn0, show -ε + -θ = -(θ + ε) by ring]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hn0.le _) (by
    unfold moebiusReal
    have := ArithmeticFunction.abs_moebius_le_one (n := n)
    exact_mod_cast this)

theorem summable_repaired_rpow {θ : ℝ} (hθ : 1 - ε < θ) :
    Summable fun n : ℕ =>
      |RHTower.dirichletConv k (pmPowerDampedRealWeight ε) n| * (n : ℝ) ^ (-θ) :=
  summable_abs_dirichletConv_rpow (by linarith) (summable_kernel_rpow hε hε2 hk (by linarith))
    (summable_moebius_rpow hθ)

/-- Beyond the abscissa the repaired series is `K(s)/ζ(s + ε)`. -/
theorem lSeries_repaired {σ : ℝ} (hσ : 1 - ε < σ) :
    LSeries (cplx (RHTower.dirichletConv k (pmPowerDampedRealWeight ε))) σ =
      LSeries (cplx k) σ * (riemannZeta ((σ : ℂ) + ε))⁻¹ := by
  rw [cplx_dirichletConv, LSeries_convolution'
    ((lSeriesSummable_cplx_iff (by linarith)).2 (summable_kernel_rpow hε hε2 hk (by linarith)))
    ((lSeriesSummable_cplx_iff (by linarith)).2 (summable_moebius_rpow hσ)),
    lSeries_moebius_damped (by simp; linarith)]

omit hε hε2 in
/-- The kernel series is holomorphic on `Re s > ½`. -/
theorem analyticOnNhd_lSeries_kernel :
    AnalyticOnNhd ℂ (LSeries (cplx k)) {s : ℂ | 1 / 2 < s.re} := by
  refine (LSeries_analyticOnNhd (cplx k)).mono fun s hs => ?_
  have hsum : LSeriesSummable (cplx k) ((1 / 2 : ℝ) : ℂ) := by
    rw [lSeriesSummable_cplx_iff (by norm_num)]; exact hk
  have := LSeriesSummable.abscissaOfAbsConv_le hsum
  simp only [Set.mem_setOf_eq] at hs ⊢
  calc abscissaOfAbsConv (cplx k) ≤ ((1 / 2 : ℝ) : ℂ).re := by simpa using this
    _ < s.re := by simpa using hs

end Kernel

/-- The actual Mellin pairing satisfies the identity obtained by clearing shifted zeta poles. -/
theorem complexMellinPairing_cleared_identity_of_repairs
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {k : ℕ → ℝ} (hk : CriticalWiener k)
    (hB : ReceiverBounded (RHTower.dirichletConv k (pmPowerDampedRealWeight ε))) :
    ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      RHTower.zetaResidueUnit (s + ε) *
        complexMellinPairing (weightCenteredPrefix
          (RHTower.dirichletConv k (pmPowerDampedRealWeight ε))
          (∑' d : ℕ, RHTower.dirichletConv k (pmPowerDampedRealWeight ε) d / d)) s =
        (s + ε - 1) * riemannZeta s * LSeries (cplx k) s -
          ((∑' d : ℕ, RHTower.dirichletConv k (pmPowerDampedRealWeight ε) d / d : ℝ) : ℂ) *
            riemannZeta s * RHTower.zetaResidueUnit (s + ε) := by
  set c := RHTower.dirichletConv k (pmPowerDampedRealWeight ε)
  obtain ⟨E, hE⟩ := hB
  let Φ := complexMellinPairing (weightCenteredPrefix c (∑' d : ℕ, c d / d))
  have hΦ : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_complexMellinPairing (weightCenteredPrefix_zero _ _) (fun T => hE T)
  have hΦσ (σ : ℝ) (hσ : 1 - ε < σ) (hσ1 : σ < 1) :
      Φ σ = riemannZeta σ *
        (((∑' d : ℕ, c d * (d : ℝ) ^ (-σ)) - ∑' d : ℕ, c d / d : ℝ) : ℂ) :=
    complexMellinPairing_eq_zeta_mul (θ := (1 - ε + σ) / 2)
      (by linarith only [hε2, hσ]) (by linarith only [hσ]) hσ1
      (summable_repaired_rpow hε hε2 hk (by linarith only [hσ]))
  set m : ℂ := ((∑' d : ℕ, c d / d : ℝ) : ℂ)
  set U : Set ℂ := {s | 1 / 2 < s.re ∧ s.re < 1}
  -- both sides of the cleared identity are holomorphic on the strip
  have hUopen : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hΦa : AnalyticOnNhd ℂ Φ {s : ℂ | 1 / 2 < s.re} := hΦ.analyticOnNhd hUopen
  have hZ : ∀ s : ℂ, AnalyticAt ℂ (fun z : ℂ => RHTower.zetaResidueUnit (z + ε)) s := fun s =>
    (RHTower.analyticAt_zetaResidueUnit (s + ε)).comp (f := fun w : ℂ => w + (ε : ℂ))
      (analyticAt_id.add analyticAt_const)
  have hζ : ∀ s ∈ U, AnalyticAt ℂ riemannZeta s := fun s hs =>
    RHTower.Sieve.analyticAt_riemannZeta_of_ne_one fun h => by
      have := congrArg Complex.re h; simp at this; linarith [hs.2]
  have hL : AnalyticOnNhd ℂ (fun s => RHTower.zetaResidueUnit (s + ε) * Φ s) U :=
    fun s hs => (hZ s).mul (hΦa s hs.1)
  have hR : AnalyticOnNhd ℂ (fun s => (s + ε - 1) * riemannZeta s * LSeries (cplx k) s -
      m * riemannZeta s * RHTower.zetaResidueUnit (s + ε)) U := fun s hs =>
    ((((analyticAt_id.add analyticAt_const).sub analyticAt_const).mul (hζ s hs)).mul
      (analyticOnNhd_lSeries_kernel hk s hs.1)).sub
      ((analyticAt_const.mul (hζ s hs)).mul (hZ s))
  -- they agree on the real segment `(1 − ε, 1)`
  have hreal : ∀ σ : ℝ, 1 - ε < σ → σ < 1 →
      RHTower.zetaResidueUnit ((σ : ℂ) + ε) * Φ σ =
        ((σ : ℂ) + ε - 1) * riemannZeta σ * LSeries (cplx k) σ -
          m * riemannZeta σ * RHTower.zetaResidueUnit ((σ : ℂ) + ε) := by
    intro σ hσ hσ1
    have hne : (σ : ℂ) + ε ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hζε : riemannZeta ((σ : ℂ) + ε) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
    rw [RHTower.zetaResidueUnit, Function.update_of_ne hne, hΦσ σ hσ hσ1, Complex.ofReal_sub,
      ofReal_tsum_rpow _ (by linarith), lSeries_repaired hε hε2 hk hσ]
    field_simp
    ring
  -- propagate across the strip from the real point `1 − ε/2`
  set r : ℂ := ((1 - ε / 2 : ℝ) : ℂ)
  have hrU : r ∈ U := by simp only [U, Set.mem_setOf_eq, r, Complex.ofReal_re]; constructor <;> linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] r, RHTower.zetaResidueUnit (z + ε) * Φ z =
      (z + ε - 1) * riemannZeta z * LSeries (cplx k) z -
        m * riemannZeta z * RHTower.zetaResidueUnit (z + ε) := by
    rw [Filter.frequently_iff]
    intro V hV
    obtain ⟨r0, hr0, hball⟩ := Metric.mem_nhdsWithin_iff.1 hV
    set η := min (r0 / 2) (ε / 4)
    have hη : 0 < η := lt_min (by linarith) (by linarith)
    refine ⟨((1 - ε / 2 + η : ℝ) : ℂ), hball ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        show 1 - ε / 2 + η - (1 - ε / 2) = η by ring, abs_of_pos hη]
      exact (min_le_left _ _).trans_lt (by linarith)
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, r]
      intro h
      have := Complex.ofReal_injective h
      linarith
    · exact hreal _ (by linarith) (by linarith [min_le_right (r0 / 2) (ε / 4)])
  have heq := hL.eqOn_of_preconnected_of_frequently_eq hR
    ((convex_halfSpace_re_gt (1 / 2)).inter (convex_halfSpace_re_lt 1)).isPreconnected hrU hfreq
  exact fun s hs hs1 => heq ⟨hs, hs1⟩


/-- A paid repaired receiver supplies an analytic factor in the cleared identity. -/
theorem exists_cleared_continuation_of_repairs
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {k : ℕ → ℝ} (hk : CriticalWiener k)
    (hB : ReceiverBounded (RHTower.dirichletConv k (pmPowerDampedRealWeight ε))) :
    ∃ Φ : ℂ → ℂ,
      AnalyticOnNhd ℂ Φ {s : ℂ | 1 / 2 < s.re} ∧
      ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
        RHTower.zetaResidueUnit (s + ε) * Φ s =
          (s + ε - 1) * riemannZeta s * LSeries (cplx k) s -
            ((∑' d : ℕ, RHTower.dirichletConv k (pmPowerDampedRealWeight ε) d / d : ℝ) : ℂ) *
              riemannZeta s * RHTower.zetaResidueUnit (s + ε) := by
  obtain ⟨E, hE⟩ := hB
  exact ⟨_, (differentiableOn_complexMellinPairing (weightCenteredPrefix_zero _ _)
    (fun T => hE T)).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re),
    complexMellinPairing_cleared_identity_of_repairs hε hε2 hk ⟨E, hE⟩⟩


/-- Evaluating the cleared continuation recovers the translated-zero vanishing identity. -/
theorem riemannZeta_mul_lSeries_eq_zero_of_repairs
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {k : ℕ → ℝ} (hk : CriticalWiener k)
    (hB : ReceiverBounded (RHTower.dirichletConv k (pmPowerDampedRealWeight ε))) {ρ : ℂ}
    (hρ : 1 / 2 + ε < ρ.re) (hρ1 : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    riemannZeta (ρ - ε) * LSeries (cplx k) (ρ - ε) = 0 := by
  obtain ⟨Φ, _, hclear⟩ := exists_cleared_continuation_of_repairs hε hε2 hk hB
  have h := hclear (ρ - ε) (by simp only [sub_re, ofReal_re]; linarith)
    (by simp only [sub_re, ofReal_re]; linarith)
  simp only [sub_add_cancel] at h
  have hρne : ρ ≠ 1 := fun h' => by rw [h'] at hρ1; simp at hρ1
  have hZρ : RHTower.zetaResidueUnit ρ = 0 := by
    rw [RHTower.zetaResidueUnit, Function.update_of_ne hρne, hz, mul_zero]
  rw [hZρ] at h
  have h2 : (ρ - 1) * (riemannZeta (ρ - ε) * LSeries (cplx k) (ρ - ε)) = 0 := by
    linear_combination -h
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hρne)


/-! ### Obstruction points of the Möbius receiver -/

theorem summable_abs_moebius_div {ε : ℝ} (hε : 0 < ε) :
    Summable fun d : ℕ => |pmPowerDampedRealWeight ε d / d| := by
  refine (Real.summable_nat_rpow.mpr (by linarith : -(1 + ε) < -1)).of_nonneg_of_le
    (fun _ => abs_nonneg _) fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [Nat.cast_zero, div_zero, abs_zero]
    exact Real.rpow_nonneg le_rfl _
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [pmPowerDampedRealWeight, abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg hd0.le _),
    Nat.abs_cast, mul_div_assoc, show (d : ℝ) ^ (-ε) / d = (d : ℝ) ^ (-(1 + ε)) by
      rw [Real.rpow_neg hd0.le, Real.rpow_neg hd0.le, Real.rpow_add hd0, Real.rpow_one]; field_simp]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hd0.le _) (by
    unfold moebiusReal
    have := ArithmeticFunction.abs_moebius_le_one (n := d)
    exact_mod_cast this)

/-- The Dirichlet series of an element of `𝒲_{1/2}` is the combination of those of its parts. -/
theorem lSeries_toFn_eq (k : WienerAlgebraAt (1 / 2)) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    LSeries (⇑k.toFn) s = LSeries (cplx (rePart k)) s + I * LSeries (cplx (imPart k)) s := by
  have hr : LSeriesSummable (cplx (rePart k)) s :=
    ((lSeriesSummable_cplx_iff (by norm_num)).2 (criticalWiener_rePart k)).of_re_le_re
      (by simpa using hs)
  have hi : LSeriesSummable (cplx (imPart k)) s :=
    ((lSeriesSummable_cplx_iff (by norm_num)).2 (criticalWiener_imPart k)).of_re_le_re
      (by simpa using hs)
  rw [← LSeries_smul, ← LSeries_add hr (hi.smul I)]
  congr 1
  funext n
  simp only [cplx, rePart, imPart, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact (Complex.re_add_im (k.toFn n)).symm.trans (by ring)

/-- **The off-line zeros are obstruction points of the Möbius receiver**: if `ζ(ρ) = 0` with
`½ + ε < Re ρ < 1` and `ζ(ρ − ε) ≠ 0`, the half-plane point `ρ − ε` lies in the obstruction hull
of `μ_ε`. -/
theorem mem_obstructionHull_moebius_of_zero {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {ρ : ℂ}
    (hρ : 1 / 2 + ε < ρ.re) (hρ1 : ρ.re < 1) (hz : riemannZeta ρ = 0)
    (hz' : riemannZeta (ρ - ε) ≠ 0) :
    halfPlanePoint (1 / 2) (ρ - ε) (by simp; linarith) ∈
      obstructionHull (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε) := by
  intro k hk
  rw [mem_paidIdeal] at hk
  have hs : (1 / 2 : ℝ) ≤ (ρ - ε).re := by simp; linarith
  rw [bohrEval_halfPlanePoint, lSeries_toFn_eq k hs]
  have h1 := riemannZeta_mul_lSeries_eq_zero_of_repairs hε hε2 (criticalWiener_rePart k) hk.1 hρ
    hρ1 hz
  have h2 := riemannZeta_mul_lSeries_eq_zero_of_repairs hε hε2 (criticalWiener_imPart k) hk.2 hρ
    hρ1 hz
  rw [(mul_eq_zero.1 h1).resolve_left hz', (mul_eq_zero.1 h2).resolve_left hz', mul_zero, add_zero]

/-- An off-line zero with a nonvanishing translate leaves the Möbius receiver unpaid. -/
theorem not_receiverBounded_moebius_of_zero {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {ρ : ℂ}
    (hρ : 1 / 2 + ε < ρ.re) (hρ1 : ρ.re < 1) (hz : riemannZeta ρ = 0)
    (hz' : riemannZeta (ρ - ε) ≠ 0) : ¬ ReceiverBounded (pmPowerDampedRealWeight ε) :=
  (obstructionHull_nonempty_iff _ _).1 ⟨_, mem_obstructionHull_moebius_of_zero hε hε2 hρ hρ1 hz hz'⟩

end

end GaloisForLFunctions.ArithmeticOrientationTheory

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.complexMellinPairing_cleared_identity_of_repairs
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.riemannZeta_mul_lSeries_eq_zero_of_repairs
