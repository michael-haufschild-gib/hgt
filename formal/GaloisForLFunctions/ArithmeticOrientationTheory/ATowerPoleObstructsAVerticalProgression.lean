import GaloisForLFunctions.ArithmeticOrientationTheory.TheOffLineZerosObstructTheMoebiusReceiver
import GaloisForLFunctions.ArithmeticOrientationTheory.TheEvenFlipOfTheMoebiusReceiverKeepsItsObstructions

/-!
# A tower pole obstructs a vertical progression

Twist the smooth power by the inverse tower of `a` at the prime `2`:

  `c_a = (Σ_j a^j δ_{2^j}) ⋆ d^{−ε}`,  `c_a(2^j m) = Σ_{i ≤ j} a^i (2^{j−i} m)^{−ε}`,

with `0 < ε < ½` and `2^{1−ε} < a < 2` (`towerTwistedPower`).  Its mean is summable (`a < 2`), and
its Dirichlet series `ζ(s + ε)/(1 − a 2^{−s})` has, besides the pole at `1 − ε`, simple poles on the
whole vertical progression `2^{−s} = 1/a`, at `Re s = log₂ a ∈ (1 − ε, 1)`.

A paid receiver continues `ζ(s)(C(s) − m)` across the strip (`exists_holomorphic_continuation`).
Clearing the tower pole and the pole of `ζ(s + ε)` and propagating from the real segment, a
repairing kernel must vanish at every point of the progression where `ζ` does not
(`lSeries_eq_zero_of_repairs_towerTwisted`): `ζ(s)K(s)·(s + ε − 1)ζ(s + ε) = 0` there, and
`ζ(s + ε) ≠ 0` because `Re(s + ε) > 1`.  So every such half-plane point is an obstruction point
(`mem_obstructionHull_towerTwisted`).
-/

open Finset ArithmeticFunction LSeries Complex Filter Topology

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open TransHorizonIncidenceMechanics WienerAlgebraAt

noncomputable section
set_option autoImplicit false

/-! ### The weight -/

/-- The smooth power twisted by the inverse tower of `a` at `2`. -/
def towerTwistedPower (ε a : ℝ) : ℕ → ℝ :=
  RHTower.dirichletConv (localFactorInverse 2 a) (dampedSignWeight unitSign ε)

theorem summable_localFactorInverse_rpow {a θ : ℝ} (ha : 0 ≤ a) (h : a * (2 : ℝ) ^ (-θ) < 1) :
    Summable fun n : ℕ => |localFactorInverse 2 a n| * (n : ℝ) ^ (-θ) := by
  rw [← (Nat.pow_right_injective le_rfl).summable_iff fun n hn => by
    have hnot : ∀ k, n ≠ 2 ^ k := fun k h' => hn ⟨k, h'.symm⟩
    rw [localFactorInverse_eq_zero a hnot, abs_zero, zero_mul]]
  have hcomp : ((fun n : ℕ => |localFactorInverse 2 a n| * (n : ℝ) ^ (-θ)) ∘ fun k : ℕ => 2 ^ k) =
      fun k => (a * (2 : ℝ) ^ (-θ)) ^ k := by
    funext k
    simp only [Function.comp_apply]
    rw [localFactorInverse_pow one_lt_two, abs_pow, abs_of_nonneg ha, mul_pow, Nat.cast_pow,
      Nat.cast_ofNat, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul zero_le_two, ← Real.rpow_mul zero_le_two, mul_comm (k : ℝ)]
  rw [hcomp]
  exact summable_geometric_of_lt_one (by positivity) h

theorem summable_unitSign_rpow {ε θ : ℝ} (hε : 0 < ε) (h : 1 < θ + ε) :
    Summable fun n : ℕ => |dampedSignWeight unitSign ε n| * (n : ℝ) ^ (-θ) := by
  refine (Real.summable_nat_rpow.mpr (by linarith : -(θ + ε) < -1)).of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [dampedSignWeight, unitSign, one_mul, Nat.cast_zero,
      Real.zero_rpow (neg_ne_zero.2 hε.ne'), abs_zero, zero_mul]
    exact Real.rpow_nonneg le_rfl _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [dampedSignWeight, unitSign, one_mul, abs_of_nonneg (Real.rpow_nonneg hn0.le _),
    ← Real.rpow_add hn0, show -ε + -θ = -(θ + ε) by ring]

theorem summable_towerTwisted_rpow {ε a θ : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (hθ : 0 < θ)
    (h : a * (2 : ℝ) ^ (-θ) < 1) (hθε : 1 < θ + ε) :
    Summable fun n : ℕ => |towerTwistedPower ε a n| * (n : ℝ) ^ (-θ) :=
  summable_abs_dirichletConv_rpow hθ (summable_localFactorInverse_rpow ha h)
    (summable_unitSign_rpow hε hθε)

theorem summable_abs_towerTwisted_div {ε a : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (ha2 : a < 2) :
    Summable fun d : ℕ => |towerTwistedPower ε a d / d| :=
  (summable_towerTwisted_rpow hε ha one_pos (by rw [Real.rpow_neg_one]; linarith)
    (by linarith)).congr fun d => by
      rw [abs_div, Nat.abs_cast, Real.rpow_neg_one, div_eq_mul_inv]

/-! ### Dirichlet series -/

theorem lSeries_unitSign {ε : ℝ} {w : ℂ} (hw : 1 < w.re + ε) :
    LSeries (cplx (dampedSignWeight unitSign ε)) w = riemannZeta (w + ε) := by
  have hre : 1 < (w + ε).re := by simpa using hw
  rw [← LSeries_zeta_eq_riemannZeta hre]
  unfold LSeries
  refine tsum_congr fun d => ?_
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  rw [term_of_ne_zero hd, term_of_ne_zero hd, cplx, dampedSignWeight, unitSign, one_mul,
    Complex.ofReal_cpow (Nat.cast_nonneg d), Complex.ofReal_natCast, Complex.cpow_add _ _ hd']
  simp only [ArithmeticFunction.zeta_apply, hd, if_false,
    Nat.cast_one]
  have h1 : (d : ℂ) ^ w ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hd' h.1
  have h2 : (d : ℂ) ^ ((ε : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hd' h.1
  rw [Complex.ofReal_neg, Complex.cpow_neg]
  field_simp

theorem lSeries_localFactorKernel_two (b : ℝ) (w : ℂ) :
    LSeries (cplx (localFactorKernel 2 b)) w = 1 - b * (2 : ℂ) ^ (-w) := by
  unfold LSeries
  rw [tsum_eq_sum (s := {1, 2}) fun m hm => ?_, sum_pair (by norm_num)]
  · rw [term_of_ne_zero one_ne_zero, term_of_ne_zero two_ne_zero]
    simp [cplx, localFactorKernel, Complex.cpow_neg]
    ring
  · simp only [mem_insert, mem_singleton, not_or] at hm
    rcases eq_or_ne m 0 with rfl | hm0
    · simp
    rw [term_of_ne_zero hm0]
    simp [cplx, localFactorKernel, hm.1, hm.2]

theorem lSeriesSummable_localFactorKernel_two (b : ℝ) (w : ℂ) :
    LSeriesSummable (cplx (localFactorKernel 2 b)) w := by
  refine summable_of_ne_finset_zero (s := {1, 2}) fun m hm => ?_
  simp only [mem_insert, mem_singleton, not_or] at hm
  rcases eq_or_ne m 0 with rfl | hm0
  · simp
  rw [term_of_ne_zero hm0]
  simp [cplx, localFactorKernel, hm.1, hm.2]

/-- `L(Σ a^j δ_{2^j}, w) · (1 − a 2^{−w}) = 1` beyond the abscissa. -/
theorem lSeries_localFactorInverse_mul {a : ℝ} (ha : 0 ≤ a) {σ : ℝ} (hσ : 0 < σ)
    (h : a * (2 : ℝ) ^ (-σ) < 1) :
    LSeries (cplx (localFactorInverse 2 a)) σ * (1 - a * (2 : ℂ) ^ (-(σ : ℂ))) = 1 := by
  have hsum := (lSeriesSummable_cplx_iff hσ).2 (summable_localFactorInverse_rpow ha h)
  rw [← lSeries_localFactorKernel_two, mul_comm, ← LSeries_convolution'
    (lSeriesSummable_localFactorKernel_two a σ) hsum, ← cplx_dirichletConv]
  rw [LSeries_congr (g := fun n => if n = 1 then (1 : ℂ) else 0) (fun {n} hn => by
    rw [cplx, dirichletConv_localFactor_inverse Nat.prime_two a hn, unitKernel]
    split_ifs <;> simp)]
  unfold LSeries
  rw [tsum_eq_single 1 fun m hm => by simp [term_def, hm]]
  simp

theorem logb_bounds {ε a : ℝ} (ha1 : (2 : ℝ) ^ (1 - ε) < a) (ha2 : a < 2) :
    1 - ε < Real.logb 2 a ∧ Real.logb 2 a < 1 := by
  have ha0 : 0 < a := lt_trans (Real.rpow_pos_of_pos two_pos _) ha1
  refine ⟨(Real.lt_logb_iff_rpow_lt one_lt_two ha0).2 ha1, ?_⟩
  rw [Real.logb_lt_iff_lt_rpow one_lt_two ha0, Real.rpow_one]
  exact ha2

/-- On the progression `a 2^{−s} = 1`, `Re s = log₂ a`. -/
theorem re_eq_logb_of_tower {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : (a : ℂ) * (2 : ℂ) ^ (-s) = 1) :
    s.re = Real.logb 2 a := by
  have hn := congrArg norm hs
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, norm_one] at hn
  have h2 : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos (two_pos : (0 : ℝ) < 2) (-s)
    simpa using this
  rw [h2] at hn
  have h3 : (2 : ℝ) ^ s.re = a := by
    rw [Real.rpow_neg zero_le_two] at hn
    have hpos : (0 : ℝ) < (2 : ℝ) ^ s.re := Real.rpow_pos_of_pos two_pos _
    field_simp at hn
    linarith
  rw [← h3, Real.logb_rpow two_pos (by norm_num)]

/-! ### Repairing kernels vanish on the progression -/

/-- **A repairing kernel vanishes on the tower progression**: if `k ⋆ c_a` is paid and
`a 2^{−s} = 1` with `ζ(s) ≠ 0`, then `K(s) = 0`. -/
theorem lSeries_eq_zero_of_repairs_towerTwisted {ε a : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (ha1 : (2 : ℝ) ^ (1 - ε) < a) (ha2 : a < 2) {k : ℕ → ℝ} (hk : CriticalWiener k)
    (hB : ReceiverBounded (RHTower.dirichletConv k (towerTwistedPower ε a))) {s : ℂ}
    (hs : (a : ℂ) * (2 : ℂ) ^ (-s) = 1) (hz : riemannZeta s ≠ 0) :
    LSeries (cplx k) s = 0 := by
  have ha0 : 0 < a := lt_trans (Real.rpow_pos_of_pos two_pos _) ha1
  obtain ⟨hσa, hσa1⟩ := logb_bounds ha1 ha2
  set σa := Real.logb 2 a
  have hres : s.re = σa := re_eq_logb_of_tower ha0 hs
  -- abscissa of the tower: `a 2^{−θ} < 1` for `θ > log₂ a`
  have htower : ∀ θ : ℝ, σa < θ → a * (2 : ℝ) ^ (-θ) < 1 := fun θ hθ => by
    have h1 : (2 : ℝ) ^ (-θ) < (2 : ℝ) ^ (-σa) :=
      Real.rpow_lt_rpow_of_exponent_lt one_lt_two (by linarith)
    have h2 : a * (2 : ℝ) ^ (-σa) = 1 := by
      rw [Real.rpow_neg zero_le_two, Real.rpow_logb two_pos (by norm_num) ha0]
      exact mul_inv_cancel₀ ha0.ne'
    nlinarith
  set c := RHTower.dirichletConv k (towerTwistedPower ε a)
  obtain ⟨E, hE⟩ := hB
  have hcθ : ∀ θ : ℝ, σa < θ → Summable fun d : ℕ => |c d| * (d : ℝ) ^ (-θ) := fun θ hθ =>
    summable_abs_dirichletConv_rpow (by linarith)
      (summable_kernel_rpow hε hε2 hk (by linarith))
      (summable_towerTwisted_rpow hε ha0.le (by linarith) (htower θ hθ) (by linarith))
  obtain ⟨Φ, hΦ, hΦσ⟩ := exists_holomorphic_continuation (a := σa) (by linarith) hcθ hE
  set m : ℂ := ((∑' d : ℕ, c d / d : ℝ) : ℂ)
  set U : Set ℂ := {z | 1 / 2 < z.re ∧ z.re < 1}
  have hUopen : IsOpen {z : ℂ | 1 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hΦa : AnalyticOnNhd ℂ Φ {z : ℂ | 1 / 2 < z.re} := hΦ.analyticOnNhd hUopen
  have hZ : ∀ z : ℂ, AnalyticAt ℂ (fun w : ℂ => RHTower.zetaResidueUnit (w + ε)) z := fun z =>
    (RHTower.analyticAt_zetaResidueUnit (z + ε)).comp (f := fun w : ℂ => w + (ε : ℂ))
      (analyticAt_id.add analyticAt_const)
  have hζ : ∀ z ∈ U, AnalyticAt ℂ riemannZeta z := fun z hz' =>
    RHTower.Sieve.analyticAt_riemannZeta_of_ne_one fun h => by
      have := congrArg Complex.re h; simp at this; linarith [hz'.2]
  have h2c : ∀ z : ℂ, AnalyticAt ℂ (fun w : ℂ => (2 : ℂ) ^ (-w)) z := fun z =>
    analyticAt_const.cpow analyticAt_id.neg (by rw [Complex.mem_slitPlane_iff]; left; norm_num)
  have hL : AnalyticOnNhd ℂ (fun z => (1 - (a : ℂ) * (2 : ℂ) ^ (-z)) * (z + ε - 1) * Φ z) U :=
    fun z hz' => ((analyticAt_const.sub (analyticAt_const.mul (h2c z))).mul
      ((analyticAt_id.add analyticAt_const).sub analyticAt_const)).mul (hΦa z hz'.1)
  have hR : AnalyticOnNhd ℂ (fun z => riemannZeta z * (LSeries (cplx k) z *
      RHTower.zetaResidueUnit (z + ε) - m * (1 - (a : ℂ) * (2 : ℂ) ^ (-z)) * (z + ε - 1))) U :=
    fun z hz' => (hζ z hz').mul (((analyticOnNhd_lSeries_kernel hk z hz'.1).mul (hZ z)).sub
      ((analyticAt_const.mul (analyticAt_const.sub (analyticAt_const.mul (h2c z)))).mul
        ((analyticAt_id.add analyticAt_const).sub analyticAt_const)))
  -- the two sides agree on the real segment `(log₂ a, 1)`
  have hreal : ∀ σ : ℝ, σa < σ → σ < 1 →
      (1 - (a : ℂ) * (2 : ℂ) ^ (-(σ : ℂ))) * ((σ : ℂ) + ε - 1) * Φ σ =
        riemannZeta σ * (LSeries (cplx k) σ * RHTower.zetaResidueUnit ((σ : ℂ) + ε) -
          m * (1 - (a : ℂ) * (2 : ℂ) ^ (-(σ : ℂ))) * ((σ : ℂ) + ε - 1)) := by
    intro σ hσ hσ1
    have hσ0 : 0 < σ := by linarith
    have hne : (σ : ℂ) + ε ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hkσ := (lSeriesSummable_cplx_iff hσ0).2 (summable_kernel_rpow hε hε2 hk (by linarith))
    have hcaσ := (lSeriesSummable_cplx_iff hσ0).2
      (summable_towerTwisted_rpow hε ha0.le hσ0 (htower σ hσ) (by linarith))
    have hlfi := (lSeriesSummable_cplx_iff hσ0).2 (summable_localFactorInverse_rpow ha0.le
      (htower σ hσ))
    have hun := (lSeriesSummable_cplx_iff hσ0).2 (summable_unitSign_rpow hε (by linarith))
    have hC : LSeries (cplx c) σ = LSeries (cplx k) σ *
        (LSeries (cplx (localFactorInverse 2 a)) σ * riemannZeta ((σ : ℂ) + ε)) := by
      rw [cplx_dirichletConv, LSeries_convolution' hkσ hcaσ, towerTwistedPower,
        cplx_dirichletConv, LSeries_convolution' hlfi hun,
        lSeries_unitSign (by simp; linarith)]
    have hinv := lSeries_localFactorInverse_mul ha0.le hσ0 (htower σ hσ)
    rw [RHTower.zetaResidueUnit, Function.update_of_ne hne, hΦσ σ hσ hσ1, Complex.ofReal_sub,
      ofReal_tsum_rpow _ hσ0, hC]
    linear_combination (riemannZeta σ * LSeries (cplx k) σ * ((σ : ℂ) + ε - 1) *
      riemannZeta ((σ : ℂ) + ε)) * hinv
  -- propagate across the strip from a real point of `(log₂ a, 1)`
  set r : ℂ := (((σa + 1) / 2 : ℝ) : ℂ)
  have hrU : r ∈ U := by
    simp only [U, Set.mem_setOf_eq, r, Complex.ofReal_re]; constructor <;> linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] r, (1 - (a : ℂ) * (2 : ℂ) ^ (-z)) * (z + ε - 1) * Φ z =
      riemannZeta z * (LSeries (cplx k) z * RHTower.zetaResidueUnit (z + ε) -
        m * (1 - (a : ℂ) * (2 : ℂ) ^ (-z)) * (z + ε - 1)) := by
    rw [Filter.frequently_iff]
    intro V hV
    obtain ⟨r0, hr0, hball⟩ := Metric.mem_nhdsWithin_iff.1 hV
    set η := min (r0 / 2) ((1 - σa) / 4)
    have hη : 0 < η := lt_min (by linarith) (by linarith)
    refine ⟨(((σa + 1) / 2 + η : ℝ) : ℂ), hball ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        show (σa + 1) / 2 + η - (σa + 1) / 2 = η by ring, abs_of_pos hη]
      exact (min_le_left _ _).trans_lt (by linarith)
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, r]
      intro h
      have := Complex.ofReal_injective h
      linarith
    · exact hreal _ (by linarith) (by linarith [min_le_right (r0 / 2) ((1 - σa) / 4)])
  have heq := hL.eqOn_of_preconnected_of_frequently_eq hR
    ((convex_halfSpace_re_gt (1 / 2)).inter (convex_halfSpace_re_lt 1)).isPreconnected hrU hfreq
  have hsU : s ∈ U := by
    simp only [U, Set.mem_setOf_eq]; constructor <;> linarith
  have h := heq hsU
  simp only at h
  rw [hs, sub_self, zero_mul, zero_mul, mul_zero, zero_mul, sub_zero] at h
  have hne : s + ε ≠ 1 := fun h' => by
    have := congrArg Complex.re h'; simp at this; linarith
  have hζε : riemannZeta (s + ε) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  rw [RHTower.zetaResidueUnit, Function.update_of_ne hne] at h
  have h0 := h.symm
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact absurd h1 hz
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact h2
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (sub_eq_zero.1 h3) hne
  · exact absurd h3 hζε

/-- **The progression is in the hull**: every point `s` with `a 2^{−s} = 1` and `ζ(s) ≠ 0` is an
obstruction point of `c_a`. -/
theorem mem_obstructionHull_towerTwisted {ε a : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (ha1 : (2 : ℝ) ^ (1 - ε) < a) (ha2 : a < 2) {s : ℂ} (hs : (a : ℂ) * (2 : ℂ) ^ (-s) = 1)
    (hz : riemannZeta s ≠ 0) (hre : (1 / 2 : ℝ) ≤ s.re) :
    halfPlanePoint (1 / 2) s hre ∈ obstructionHull (towerTwistedPower ε a)
      (summable_abs_towerTwisted_div hε (lt_trans (Real.rpow_pos_of_pos two_pos _) ha1).le ha2) := by
  intro k hk
  rw [mem_paidIdeal] at hk
  rw [bohrEval_halfPlanePoint, lSeries_toFn_eq k hre,
    lSeries_eq_zero_of_repairs_towerTwisted hε hε2 ha1 ha2 (criticalWiener_rePart k) hk.1 hs hz,
    lSeries_eq_zero_of_repairs_towerTwisted hε hε2 ha1 ha2 (criticalWiener_imPart k) hk.2 hs hz,
    mul_zero, add_zero]

end

end GaloisForLFunctions.ArithmeticOrientationTheory
