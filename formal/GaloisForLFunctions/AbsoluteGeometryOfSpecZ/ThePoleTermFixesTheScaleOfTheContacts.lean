import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.LengtheningTheTreeOfTwoRaisesThePairingBelowTheSquareOfTwo
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectIsCyclic

/-!
# The pole term fixes the scale of the contacts

Multiply all contacts of the square by one factor: the contacts `(1 + ε)Λ + δ` with
`Σ |δ(n)| n^{-1/2} < ∞`, on the comb of the integers with the counterterm `log(n/2π) + c`. For
`ε = 0` the pair `(δ, c)` is not refuted exactly when the constant is at least the supremum of
the symbol of `δ`. For `ε ≠ 0` no constant helps.

* **A pair of bumps at the distance `T`** (`paperFT_bumpPair`, `Wsummand_bumpPair`): for
  `f_T = g + s·g(· − T)`, `s = ±1`, each summand of the sum over the zeros is that of `g` times
  `2 + s(e^{iγT} + e^{−iγT})`.
* **The zeros are of smaller order than the pole** (`tendsto_abs_zeroSum_bumpPair`):
  `|Z(f_T)| e^{−T/2} → 0`, because every zero has `|Im γ| < ½`; dominated convergence over the
  zeros.
* **The degrees** (`integral_bumpPair_mul_exp`): `d₁(f_T) d₂(f_T) = d₁(g) d₂(g)(1 + s e^{−T/2})
  (1 + s e^{T/2})`, of the order `e^{T/2}` with the sign `s`.
* **Every other scale fails** (`exists_packet_scaled_neg`, `not_combBezoutScaled`): for `ε ≠ 0`,
  summable `δ` and every `c`, a pair of bumps with `s` the sign of `ε` has a negative
  functional, without hypothesis.

So the pole plane fixes the total size of the contacts, as the symbol fixes their distribution up
to the constant: the trees of all primes cannot be rescaled by a common factor. The mechanism is
the prime number theorem in the form `|Im γ| < ½`.
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt Real

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

variable {g : ℝ → ℝ} {δ : ℕ → ℝ}

/-! ### A pair of bumps at a distance -/

/-- The pair of bumps `g + s·g(· − T)`. -/
def bumpPair (g : ℝ → ℝ) (s T : ℝ) : ℝ → ℝ := fun u => g u + s * g (u - T)

theorem contDiff_bumpPair (hg : ContDiff ℝ 2 g) (s T : ℝ) : ContDiff ℝ 2 (bumpPair g s T) :=
  hg.add (contDiff_const.mul (hg.comp (contDiff_id.sub contDiff_const)))

theorem hasCompactSupport_bumpPair (hgc : HasCompactSupport g) (s T : ℝ) :
    HasCompactSupport (bumpPair g s T) :=
  hgc.add ((hgc.comp_homeomorph (Homeomorph.subRight T)).mul_left (f := fun _ => s))

/-- The transform of a pair of bumps. -/
theorem paperFT_bumpPair (hg : Continuous g) (hgc : HasCompactSupport g) (s T : ℝ) (z : ℂ) :
    paperFT (fun u => (bumpPair g s T u : ℂ)) z =
      paperFT (fun u => (g u : ℂ)) z * (1 + s * Complex.exp (Complex.I * z * T)) := by
  have hG : Continuous fun u => (g u : ℂ) := Complex.continuous_ofReal.comp hg
  have hGc : HasCompactSupport fun u => (g u : ℂ) := hasCompactSupport_ofReal_packet hgc
  have hG' : Continuous fun u => ((g (u - T) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hg.comp (continuous_id.sub continuous_const))
  have hGc' : HasCompactSupport fun u => ((g (u - T) : ℝ) : ℂ) :=
    hasCompactSupport_ofReal_packet (hgc.comp_homeomorph (Homeomorph.subRight T))
  have h1 : Integrable fun u : ℝ => (g u : ℂ) * Complex.exp (Complex.I * z * u) :=
    (hG.mul (by fun_prop)).integrable_of_hasCompactSupport hGc.mul_right
  have h2 : Integrable fun u : ℝ => ((g (u - T) : ℝ) : ℂ) * Complex.exp (Complex.I * z * u) :=
    (hG'.mul (by fun_prop)).integrable_of_hasCompactSupport hGc'.mul_right
  have htr : (∫ u : ℝ, ((g (u - T) : ℝ) : ℂ) * Complex.exp (Complex.I * z * u)) =
      Complex.exp (Complex.I * z * T) * ∫ u : ℝ, (g u : ℂ) * Complex.exp (Complex.I * z * u) :=
    ArithmeticCastelnuovoSeveri.paperFT_translate T (fun u => (g u : ℂ)) z
  have e : (fun u : ℝ => ((bumpPair g s T u : ℝ) : ℂ) * Complex.exp (Complex.I * z * u)) =
      fun u => (g u : ℂ) * Complex.exp (Complex.I * z * u) +
        (s : ℂ) * (((g (u - T) : ℝ) : ℂ) * Complex.exp (Complex.I * z * u)) := by
    funext u
    simp only [bumpPair]
    push_cast
    ring
  unfold paperFT
  rw [e, integral_add h1 (h2.const_mul _), integral_const_mul, htr]
  ring

/-- **The summand of a zero on a pair of bumps**: that of one bump times
`2 + s(e^{iγT} + e^{−iγT})`. -/
theorem Wsummand_bumpPair (hg : Continuous g) (hgc : HasCompactSupport g) {s : ℝ}
    (hs : s * s = 1) (T : ℝ) (ρ : ℂ) :
    zetaZeroConfig.Wsummand (fun u => (bumpPair g s T u : ℂ))
        (fun u => (bumpPair g s T u : ℂ)) ρ =
      zetaZeroConfig.Wsummand (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) ρ *
        (2 + s * (Complex.exp (Complex.I * gammaOf ρ * T) +
          Complex.exp (-(Complex.I * gammaOf ρ * T)))) := by
  have hss : (s : ℂ) * (s : ℂ) = 1 := by exact_mod_cast hs
  have hxy : Complex.exp (Complex.I * gammaOf ρ * T) *
      Complex.exp (-(Complex.I * gammaOf ρ * T)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hconj : (starRingEnd ℂ) (Complex.exp (Complex.I * (starRingEnd ℂ) (gammaOf ρ) * T)) =
      Complex.exp (-(Complex.I * gammaOf ρ * T)) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
    ring
  unfold ZeroConfig.Wsummand
  rw [paperFT_bumpPair hg hgc, paperFT_bumpPair hg hgc, map_mul, map_add, map_one, map_mul,
    Complex.conj_ofReal, hconj]
  linear_combination
    ((zetaZeroConfig.mult ρ : ℂ) * paperFT (fun u => (g u : ℂ)) (gammaOf ρ) *
      (starRingEnd ℂ) (paperFT (fun u => (g u : ℂ)) ((starRingEnd ℂ) (gammaOf ρ))) *
      Complex.exp (Complex.I * gammaOf ρ * T) * Complex.exp (-(Complex.I * gammaOf ρ * T))) * hss +
    ((zetaZeroConfig.mult ρ : ℂ) * paperFT (fun u => (g u : ℂ)) (gammaOf ρ) *
      (starRingEnd ℂ) (paperFT (fun u => (g u : ℂ)) ((starRingEnd ℂ) (gammaOf ρ)))) * hxy

theorem abs_eq_one_of_mul_self {s : ℝ} (hs : s * s = 1) : |s| = 1 := by
  have h : |s| * |s| = 1 := by rw [← abs_mul, hs, abs_one]
  nlinarith [abs_nonneg s]

/-- The factor of a zero is at most `2 + 2 e^{|Im γ| T}`. -/
theorem norm_Wsummand_bumpPair_le (hg : Continuous g) (hgc : HasCompactSupport g) {s : ℝ}
    (hs : s * s = 1) {T : ℝ} (hT : 0 ≤ T) (ρ : ℂ) :
    ‖zetaZeroConfig.Wsummand (fun u => (bumpPair g s T u : ℂ))
        (fun u => (bumpPair g s T u : ℂ)) ρ‖ ≤
      ‖zetaZeroConfig.Wsummand (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) ρ‖ *
        (2 + 2 * Real.exp (|(gammaOf ρ).im| * T)) := by
  rw [Wsummand_bumpPair hg hgc hs, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hsn : ‖(s : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_eq_one_of_mul_self hs]
  have hx : ‖Complex.exp (Complex.I * gammaOf ρ * T)‖ ≤ Real.exp (|(gammaOf ρ).im| * T) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have hre : (Complex.I * gammaOf ρ * (T : ℂ)).re = -((gammaOf ρ).im * T) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have := mul_nonneg (show 0 ≤ |(gammaOf ρ).im| + (gammaOf ρ).im by
      linarith [neg_abs_le (gammaOf ρ).im]) hT
    linarith
  have hy : ‖Complex.exp (-(Complex.I * gammaOf ρ * T))‖ ≤ Real.exp (|(gammaOf ρ).im| * T) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have hre : (-(Complex.I * gammaOf ρ * (T : ℂ))).re = (gammaOf ρ).im * T := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have := mul_nonneg (show 0 ≤ |(gammaOf ρ).im| - (gammaOf ρ).im by
      linarith [le_abs_self (gammaOf ρ).im]) hT
    linarith
  calc ‖(2 : ℂ) + s * (Complex.exp (Complex.I * gammaOf ρ * T) +
          Complex.exp (-(Complex.I * gammaOf ρ * T)))‖
      ≤ ‖(2 : ℂ)‖ + ‖(s : ℂ) * (Complex.exp (Complex.I * gammaOf ρ * T) +
          Complex.exp (-(Complex.I * gammaOf ρ * T)))‖ := norm_add_le _ _
    _ = 2 + ‖Complex.exp (Complex.I * gammaOf ρ * T) +
          Complex.exp (-(Complex.I * gammaOf ρ * T))‖ := by
        rw [norm_mul, hsn, one_mul, Complex.norm_two]
    _ ≤ 2 + (‖Complex.exp (Complex.I * gammaOf ρ * T)‖ +
          ‖Complex.exp (-(Complex.I * gammaOf ρ * T))‖) := by
        linarith [norm_add_le (Complex.exp (Complex.I * gammaOf ρ * T))
          (Complex.exp (-(Complex.I * gammaOf ρ * T)))]
    _ ≤ 2 + 2 * Real.exp (|(gammaOf ρ).im| * T) := by linarith

/-! ### The zeros are of smaller order than the pole -/

theorem tendsto_exp_neg_mul {c : ℝ} (hc : 0 < c) :
    Tendsto (fun T : ℝ => Real.exp (-(c * T))) atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)

/-- **The sum over the zeros of a pair of bumps is `o(e^{T/2})`.** -/
theorem tendsto_abs_zeroSum_bumpPair (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {s : ℝ}
    (hs : s * s = 1) :
    Tendsto (fun T : ℝ => |zeroSum (bumpPair g s T)| * Real.exp (-(T / 2))) atTop (𝓝 0) := by
  have hGd := contDiff_ofReal_packet hg
  have hGc := hasCompactSupport_ofReal_packet hgc
  have htemp := SquareRootThreshold.temperedConfig_zetaZeroConfig
  have hsumW := ArithmeticCastelnuovoSeveri.summable_norm_Wsummand zetaZeroConfig htemp hGd hGc
    hGd hGc
  have him : ∀ ρ : zetaZeroConfig.carrier, |(gammaOf (ρ : ℂ)).im| < 1 / 2 := fun ρ => by
    have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
    exact WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩
  have hkey : ∀ (a T : ℝ), (2 + 2 * Real.exp (a * T)) * Real.exp (-(T / 2)) =
      2 * Real.exp (-(1 / 2 * T)) + 2 * Real.exp (-((1 / 2 - a) * T)) := by
    intro a T
    have e1 : -(T / 2) = -(1 / 2 * T) := by ring
    have e2 : a * T + -(T / 2) = -((1 / 2 - a) * T) := by ring
    rw [add_mul, mul_assoc, ← Real.exp_add, e2, e1]
  -- dominated convergence over the zeros
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (T : ℝ) (ρ : zetaZeroConfig.carrier) =>
      ‖zetaZeroConfig.Wsummand (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) ρ‖ *
        ((2 + 2 * Real.exp (|(gammaOf (ρ : ℂ)).im| * T)) * Real.exp (-(T / 2))))
    (g := fun _ => (0 : ℝ))
    (bound := fun ρ => 4 * ‖zetaZeroConfig.Wsummand (fun u => (g u : ℂ))
      (fun u => (g u : ℂ)) ρ‖)
    (hsumW.mul_left 4)
    (fun ρ => by
      have h1 := (tendsto_exp_neg_mul (show (0 : ℝ) < 1 / 2 by norm_num)).const_mul 2
      have h2 := (tendsto_exp_neg_mul (show (0 : ℝ) < 1 / 2 - |(gammaOf (ρ : ℂ)).im| by
        linarith [him ρ])).const_mul 2
      have h3 := (h1.add h2).const_mul
        ‖zetaZeroConfig.Wsummand (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) ρ‖
      simp only [mul_zero, add_zero] at h3
      exact h3.congr fun T => by rw [hkey])
    (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT ρ
      have ha := (him ρ).le
      have h1 : Real.exp (-(1 / 2 * T)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have h2 : Real.exp (-((1 / 2 - |(gammaOf (ρ : ℂ)).im|) * T)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hkey, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      linarith)
  rw [tsum_zero] at hT
  refine squeeze_zero' (Eventually.of_forall fun T => by positivity) ?_ hT
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT0
  have hFd := contDiff_ofReal_packet (contDiff_bumpPair hg s T)
  have hFc := hasCompactSupport_ofReal_packet (hasCompactSupport_bumpPair hgc s T)
  have hsumF := ArithmeticCastelnuovoSeveri.summable_norm_Wsummand zetaZeroConfig htemp hFd hFc
    hFd hFc
  have hle : ∀ ρ : zetaZeroConfig.carrier,
      ‖zetaZeroConfig.Wsummand (fun u => (bumpPair g s T u : ℂ))
        (fun u => (bumpPair g s T u : ℂ)) ρ‖ ≤
      ‖zetaZeroConfig.Wsummand (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) ρ‖ *
        (2 + 2 * Real.exp (|(gammaOf (ρ : ℂ)).im| * T)) := fun ρ =>
    norm_Wsummand_bumpPair_le hg.continuous hgc hs hT0 ρ
  have hsumB : Summable fun ρ : zetaZeroConfig.carrier =>
      ‖zetaZeroConfig.Wsummand (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) ρ‖ *
        (2 + 2 * Real.exp (|(gammaOf (ρ : ℂ)).im| * T)) := by
    refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_)
      (hsumW.mul_right (2 + 2 * Real.exp (1 / 2 * T)))
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have : Real.exp (|(gammaOf (ρ : ℂ)).im| * T) ≤ Real.exp (1 / 2 * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (him ρ).le hT0)
    linarith
  have h1 : |zeroSum (bumpPair g s T)| ≤
      ∑' ρ : zetaZeroConfig.carrier,
        ‖zetaZeroConfig.Wsummand (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) ρ‖ *
          (2 + 2 * Real.exp (|(gammaOf (ρ : ℂ)).im| * T)) := by
    calc |zeroSum (bumpPair g s T)|
        ≤ ‖zetaZeroConfig.W (fun u => (bumpPair g s T u : ℂ))
            (fun u => (bumpPair g s T u : ℂ))‖ := Complex.abs_re_le_norm _
      _ ≤ ∑' ρ : zetaZeroConfig.carrier,
            ‖zetaZeroConfig.Wsummand (fun u => (bumpPair g s T u : ℂ))
              (fun u => (bumpPair g s T u : ℂ)) ρ‖ := norm_tsum_le_tsum_norm hsumF
      _ ≤ _ := Summable.tsum_le_tsum hle hsumF hsumB
  calc |zeroSum (bumpPair g s T)| * Real.exp (-(T / 2))
      ≤ (∑' ρ : zetaZeroConfig.carrier,
          ‖zetaZeroConfig.Wsummand (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) ρ‖ *
            (2 + 2 * Real.exp (|(gammaOf (ρ : ℂ)).im| * T))) * Real.exp (-(T / 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = ∑' ρ : zetaZeroConfig.carrier,
          ‖zetaZeroConfig.Wsummand (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) ρ‖ *
            ((2 + 2 * Real.exp (|(gammaOf (ρ : ℂ)).im| * T)) * Real.exp (-(T / 2))) := by
        rw [← tsum_mul_right]
        exact tsum_congr fun ρ => mul_assoc _ _ _

/-! ### The degrees and the archimedean energy of a pair of bumps -/

/-- The exponential moments of a pair of bumps. -/
theorem integral_bumpPair_mul_exp (hg : Continuous g) (hgc : HasCompactSupport g) (s T σ : ℝ) :
    ∫ u, bumpPair g s T u * Real.exp (σ * u) =
      (∫ u, g u * Real.exp (σ * u)) * (1 + s * Real.exp (σ * T)) := by
  have h1 : Integrable fun u : ℝ => g u * Real.exp (σ * u) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  have h2 : Integrable fun u : ℝ => g (u - T) * Real.exp (σ * u) :=
    ((hg.comp (continuous_id.sub continuous_const)).mul
      (by fun_prop)).integrable_of_hasCompactSupport
      (hgc.comp_homeomorph (Homeomorph.subRight T)).mul_right
  have htr : (∫ u : ℝ, g (u - T) * Real.exp (σ * u)) =
      Real.exp (σ * T) * ∫ u : ℝ, g u * Real.exp (σ * u) := by
    have e : (fun u : ℝ => g (u - T) * Real.exp (σ * u)) =
        fun u => Real.exp (σ * T) * (fun v : ℝ => g v * Real.exp (σ * v)) (u - T) := by
      funext u
      show g (u - T) * Real.exp (σ * u) =
        Real.exp (σ * T) * (g (u - T) * Real.exp (σ * (u - T)))
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    rw [e, integral_const_mul, integral_sub_right_eq_self (fun v : ℝ => g v * Real.exp (σ * v)) T]
  have e : (fun u : ℝ => bumpPair g s T u * Real.exp (σ * u)) =
      fun u => g u * Real.exp (σ * u) + s * (g (u - T) * Real.exp (σ * u)) := by
    funext u
    simp only [bumpPair]
    ring
  rw [e, integral_add h1 (h2.const_mul _), integral_const_mul, htr]
  ring

/-- A compactly supported packet has a vanishing autocorrelation at `log n` for large `n`. -/
theorem exists_packetAutocorr_log_eq_zero {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    ∃ Q : ℕ, ∀ n : ℕ, Q < n → packetAutocorr f (Real.log n) = 0 := by
  obtain ⟨A, hA⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  have hsupp : ∀ u, f u ≠ 0 → |u| ≤ A := fun u hu => by
    have := hA (subset_tsupport _ hu)
    rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  have hlen : ∀ u, u ≤ -|A| - 1 ∨ (-|A| - 1) + (2 * |A| + 2) ≤ u → f u = 0 := by
    intro u hu
    by_contra h0
    have h := abs_le.mp (hsupp u h0)
    have hAA := le_abs_self A
    rcases hu with h' | h' <;> linarith [h.1, h.2]
  refine ⟨⌈Real.exp (2 * |A| + 2)⌉₊, fun n hn => packetAutocorr_eq_zero_of_length hlen ?_⟩
  have h1 : Real.exp (2 * |A| + 2) < n := Nat.lt_of_ceil_lt hn
  rw [← Real.log_exp (2 * |A| + 2)]
  exact Real.log_le_log (Real.exp_pos _) h1.le

/-- **The archimedean part of a pair of bumps without the pole is bounded** by the archimedean
energy of one bump. -/
theorem abs_weilArchRe_bumpPair_sub_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {s : ℝ}
    (hs : s * s = 1) (T : ℝ) :
    |_root_.RHTower.WeilOneSided.weilArchRe
          (EF.weilTest (fun u => (bumpPair g s T u : ℂ)) (fun u => (bumpPair g s T u : ℂ))) -
        2 * ((∫ u, bumpPair g s T u * Real.exp (-u / 2)) *
          ∫ u, bumpPair g s T u * Real.exp (u / 2))| ≤
      1 / (2 * π) * ∫ τ : ℝ, 4 * ‖‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π))‖ := by
  have hf := contDiff_bumpPair hg s T
  have hfc := hasCompactSupport_bumpPair hgc s T
  have hFd := contDiff_ofReal_packet hf
  obtain ⟨a, hfs⟩ := exists_tsupport_ofReal_subset_Icc hfc
  obtain ⟨ag, hgs⟩ := exists_tsupport_ofReal_subset_Icc hgc
  obtain ⟨Q, hQ⟩ := exists_packetAutocorr_log_eq_zero hfc
  have hW0 := re_weilFullFunctional_packet_of_weight (fun _ => (0 : ℝ)) (bumpPair g s T) hQ
  simp only [zero_div, zero_mul, Finset.sum_const_zero, mul_zero, sub_zero] at hW0
  have hsym := re_weilFullFunctional_eq_pole_add_symbol (fun _ => (0 : ℝ)) hFd hfs
  have hpole := weilPoleTerm_packet hf.continuous hfc
  have hS0 : ∀ ξ : ℝ, _root_.RHTower.weilAtomSymbol (fun _ => (0 : ℝ))
      ⌊Real.exp (2 * a)⌋₊ ξ = _root_.RHTower.archimedeanWeilSymbol ξ := fun ξ => by
    simp [_root_.RHTower.weilAtomSymbol]
  simp only [hS0] at hsym
  rw [← hW0, hsym, hpole, add_sub_cancel_left, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * π))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hbound : Integrable fun τ : ℝ => 4 * ‖‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
      _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π))‖ :=
    (_root_.RHTower.integrable_normSq_paperFT_mul_arch (contDiff_ofReal_packet hg)
      hgs).norm.const_mul 4
  have hsn : ‖(s : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_eq_one_of_mul_self hs]
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hbound (Eventually.of_forall fun τ => ?_)
  have hfac : ‖(1 : ℂ) + s * Complex.exp (Complex.I * τ * T)‖ ≤ 2 := by
    have h1 : ‖Complex.exp (Complex.I * (τ : ℂ) * (T : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : (Complex.I * (τ : ℂ) * (T : ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre, Real.exp_zero]
    calc ‖(1 : ℂ) + s * Complex.exp (Complex.I * τ * T)‖
        ≤ ‖(1 : ℂ)‖ + ‖(s : ℂ) * Complex.exp (Complex.I * τ * T)‖ := norm_add_le _ _
      _ = 2 := by
          rw [norm_mul, hsn, h1, norm_one]
          norm_num
  have hsq : ‖paperFT (fun u => (bumpPair g s T u : ℂ)) τ‖ ^ 2 ≤
      4 * ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 := by
    rw [paperFT_bumpPair hg.continuous hgc, norm_mul, mul_pow]
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hfac 2
    nlinarith [sq_nonneg ‖paperFT (fun u => (g u : ℂ)) τ‖]
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (sq_nonneg _),
    ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hsq (norm_nonneg _)

/-! ### Every other scale of the contacts fails -/

/-- The pole term of a pair of bumps: of the order `e^{T/2}`, with the sign `s`. -/
theorem pole_bumpPair (hg : Continuous g) (hgc : HasCompactSupport g) {s : ℝ} (hs : s * s = 1)
    (T : ℝ) :
    2 * ((∫ u, bumpPair g s T u * Real.exp (-u / 2)) *
        ∫ u, bumpPair g s T u * Real.exp (u / 2)) =
      2 * ((∫ u, g u * Real.exp (-(1 / 2) * u)) * ∫ u, g u * Real.exp (1 / 2 * u)) *
        (2 + s * (Real.exp (1 / 2 * T) + Real.exp (-(1 / 2 * T)))) := by
  have e1 : (fun u : ℝ => bumpPair g s T u * Real.exp (-u / 2)) =
      fun u => bumpPair g s T u * Real.exp (-(1 / 2) * u) := by
    funext u
    congr 2
    ring
  have e2 : (fun u : ℝ => bumpPair g s T u * Real.exp (u / 2)) =
      fun u => bumpPair g s T u * Real.exp (1 / 2 * u) := by
    funext u
    congr 2
    ring
  have hEm : Real.exp (-(1 / 2) * T) = Real.exp (-(1 / 2 * T)) := by
    congr 1
    ring
  have hEE : Real.exp (-(1 / 2 * T)) * Real.exp (1 / 2 * T) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [e1, e2, integral_bumpPair_mul_exp hg hgc, integral_bumpPair_mul_exp hg hgc, hEm]
  linear_combination
    (2 * (∫ u, g u * Real.exp (-(1 / 2) * u)) * (∫ u, g u * Real.exp (1 / 2 * u)) *
      Real.exp (-(1 / 2 * T)) * Real.exp (1 / 2 * T)) * hs +
    (2 * (∫ u, g u * Real.exp (-(1 / 2) * u)) * (∫ u, g u * Real.exp (1 / 2 * u))) * hEE

/-- The mass of a pair of bumps is at most four times the mass of one. -/
theorem integral_bumpPair_sq_le (hg : Continuous g) (hgc : HasCompactSupport g) {s : ℝ}
    (hs : s * s = 1) (T : ℝ) : ∫ u, bumpPair g s T u ^ 2 ≤ 4 * ∫ u, g u ^ 2 := by
  have hgsq : Integrable fun u => g u ^ 2 := by
    refine ((hg.mul hg).integrable_of_hasCompactSupport hgc.mul_right).congr
      (Eventually.of_forall fun u => ?_)
    show g u * g u = g u ^ 2
    ring
  have hshift : Integrable fun u => g (u - T) ^ 2 := hgsq.comp_sub_right T
  have hfc := hasCompactSupport_bumpPair hgc s T
  have hfcont : Continuous (bumpPair g s T) :=
    hg.add (continuous_const.mul (hg.comp (continuous_id.sub continuous_const)))
  have hfsq : Integrable fun u => bumpPair g s T u ^ 2 := by
    refine ((hfcont.mul hfcont).integrable_of_hasCompactSupport hfc.mul_right).congr
      (Eventually.of_forall fun u => ?_)
    show bumpPair g s T u * bumpPair g s T u = bumpPair g s T u ^ 2
    ring
  have hle : ∫ u, bumpPair g s T u ^ 2 ≤ ∫ u, (2 * g u ^ 2 + 2 * g (u - T) ^ 2) := by
    refine integral_mono hfsq ((hgsq.const_mul 2).add (hshift.const_mul 2)) fun u => ?_
    show bumpPair g s T u ^ 2 ≤ 2 * g u ^ 2 + 2 * g (u - T) ^ 2
    have e : bumpPair g s T u ^ 2 = 2 * g u ^ 2 + 2 * g (u - T) ^ 2 -
        (g u - s * g (u - T)) ^ 2 + 2 * (s * s - 1) * g (u - T) ^ 2 := by
      simp only [bumpPair]
      ring
    rw [e, hs]
    linarith [sq_nonneg (g u - s * g (u - T))]
  rw [integral_add (hgsq.const_mul 2) (hshift.const_mul 2), integral_const_mul,
    integral_const_mul, integral_sub_right_eq_self (fun u => g u ^ 2) T] at hle
  linarith

/-- A summable deviation of the contacts is bounded by the mass. -/
theorem abs_sum_deviation_le (hsum : Summable fun n => |δ n| / Real.sqrt n) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (Q : ℕ) :
    |∑ k ∈ Icc 2 Q, δ k / Real.sqrt k * packetAutocorr f (Real.log k)| ≤
      (∑' n : ℕ, |δ n| / Real.sqrt n) * ∫ u, f u ^ 2 := by
  have hmass0 : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun u => sq_nonneg _
  calc |∑ k ∈ Icc 2 Q, δ k / Real.sqrt k * packetAutocorr f (Real.log k)|
      ≤ ∑ k ∈ Icc 2 Q, |δ k / Real.sqrt k * packetAutocorr f (Real.log k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Icc 2 Q, |δ k| / Real.sqrt k * ∫ u, f u ^ 2 :=
        Finset.sum_le_sum fun k _ => by
          rw [abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
          exact mul_le_mul_of_nonneg_left
            (SelectiveArithmetic.abs_packetAutocorr_le hf hfc _) (by positivity)
    _ = (∑ k ∈ Icc 2 Q, |δ k| / Real.sqrt k) * ∫ u, f u ^ 2 := by rw [Finset.sum_mul]
    _ ≤ (∑' n : ℕ, |δ n| / Real.sqrt n) * ∫ u, f u ^ 2 :=
        mul_le_mul_of_nonneg_right (hsum.sum_le_tsum _ fun k _ => by positivity) hmass0

/-- **The functional of scaled contacts on a packet**: the zero sum, the archimedean part with
the pole, and the deviation. -/
theorem re_weilFullFunctional_scaled_eq (ε : ℝ) (δ : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {Q : ℕ}
    (hQ : ∀ n : ℕ, Q < n → packetAutocorr f (Real.log n) = 0) :
    (_root_.RHTower.weilFullFunctional (fun n => (1 + ε) * (Λ n : ℝ) + δ n)
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
      (1 + ε) * zeroSum f -
        ε * _root_.RHTower.WeilOneSided.weilArchRe
          (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) -
        2 * ∑ k ∈ Icc 2 Q, δ k / Real.sqrt k * packetAutocorr f (Real.log k) := by
  have hW := re_weilFullFunctional_packet_of_weight (fun n => (1 + ε) * (Λ n : ℝ) + δ n) f hQ
  have hΛ := re_weilFullFunctional_packet_of_weight (fun n => (Λ n : ℝ)) f hQ
  have hz := zeroSum_eq_weilFullFunctional hf hfc
  have hsplit : ∑ k ∈ Icc 2 Q, ((1 + ε) * (Λ k : ℝ) + δ k) / Real.sqrt k *
        packetAutocorr f (Real.log k) =
      (1 + ε) * ∑ k ∈ Icc 2 Q, (Λ k : ℝ) / Real.sqrt k * packetAutocorr f (Real.log k) +
        ∑ k ∈ Icc 2 Q, δ k / Real.sqrt k * packetAutocorr f (Real.log k) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hW, hsplit, hz, hΛ]
  ring

/-- A bump with positive degrees. -/
theorem exists_bump_pos_degrees : ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
    0 < (∫ u, g u * Real.exp (-(1 / 2) * u)) ∧ 0 < ∫ u, g u * Real.exp (1 / 2 * u) := by
  have hδ : (0 : ℝ) < 1 / 2 := by norm_num
  have hg : ContDiff ℝ 2 (SelectiveArithmetic.cutoff 1 (1 / 2)) :=
    (SelectiveArithmetic.contDiff_cutoff _ _).of_le (by norm_num)
  have hgc : HasCompactSupport (SelectiveArithmetic.cutoff 1 (1 / 2)) :=
    SelectiveArithmetic.hasCompactSupport_cutoff hδ
  have hgsq : Integrable fun u => SelectiveArithmetic.cutoff 1 (1 / 2) u ^ 2 := by
    refine ((hg.continuous.mul hg.continuous).integrable_of_hasCompactSupport
      hgc.mul_right).congr (Eventually.of_forall fun u => ?_)
    show SelectiveArithmetic.cutoff 1 (1 / 2) u * SelectiveArithmetic.cutoff 1 (1 / 2) u =
      SelectiveArithmetic.cutoff 1 (1 / 2) u ^ 2
    ring
  have hM1 : 1 ≤ ∫ u, SelectiveArithmetic.cutoff 1 (1 / 2) u ^ 2 := by
    have h := SelectiveArithmetic.le_packetAutocorr_cutoff_zero (show (0 : ℝ) < 1 by norm_num)
    have e : packetAutocorr (SelectiveArithmetic.cutoff 1 (1 / 2)) 0 =
        ∫ u, SelectiveArithmetic.cutoff 1 (1 / 2) u ^ 2 := by
      rw [packetAutocorr]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      show SelectiveArithmetic.cutoff 1 (1 / 2) u *
          SelectiveArithmetic.cutoff 1 (1 / 2) (u + 0) =
        SelectiveArithmetic.cutoff 1 (1 / 2) u ^ 2
      rw [add_zero, sq]
    rwa [e] at h
  -- both degrees are at least `e^{−1/2}`
  have hdeg : ∀ σ : ℝ, |σ| ≤ 1 / 2 →
      Real.exp (-(1 / 2)) ≤ ∫ u, SelectiveArithmetic.cutoff 1 (1 / 2) u * Real.exp (σ * u) := by
    intro σ hσ
    have hint : Integrable fun u : ℝ =>
        SelectiveArithmetic.cutoff 1 (1 / 2) u * Real.exp (σ * u) :=
      (hg.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
    have hmono : ∫ u, Real.exp (-(1 / 2)) * SelectiveArithmetic.cutoff 1 (1 / 2) u ^ 2 ≤
        ∫ u, SelectiveArithmetic.cutoff 1 (1 / 2) u * Real.exp (σ * u) := by
      refine integral_mono (hgsq.const_mul _) hint fun u => ?_
      show Real.exp (-(1 / 2)) * SelectiveArithmetic.cutoff 1 (1 / 2) u ^ 2 ≤
        SelectiveArithmetic.cutoff 1 (1 / 2) u * Real.exp (σ * u)
      have h0 := SelectiveArithmetic.cutoff_nonneg 1 (1 / 2) u
      have h1 := SelectiveArithmetic.cutoff_le_one 1 (1 / 2) u
      by_cases hz : SelectiveArithmetic.cutoff 1 (1 / 2) u = 0
      · rw [hz]
        simp
      · have hu : |u| < 1 := lt_of_not_ge fun h => hz (SelectiveArithmetic.cutoff_eq_zero hδ h)
        have hσu : -(1 / 2) ≤ σ * u := by
          have h2 : |σ * u| ≤ 1 / 2 := by
            rw [abs_mul]
            calc |σ| * |u| ≤ 1 / 2 * 1 := mul_le_mul hσ hu.le (abs_nonneg _) (by norm_num)
              _ = 1 / 2 := by norm_num
          linarith [(abs_le.mp h2).1]
        have he : Real.exp (-(1 / 2)) ≤ Real.exp (σ * u) := Real.exp_le_exp.mpr hσu
        have hsq : SelectiveArithmetic.cutoff 1 (1 / 2) u ^ 2 ≤
            SelectiveArithmetic.cutoff 1 (1 / 2) u := by
          rw [sq]
          exact mul_le_of_le_one_left h0 h1
        calc Real.exp (-(1 / 2)) * SelectiveArithmetic.cutoff 1 (1 / 2) u ^ 2
            ≤ Real.exp (-(1 / 2)) * SelectiveArithmetic.cutoff 1 (1 / 2) u :=
              mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
          _ ≤ Real.exp (σ * u) * SelectiveArithmetic.cutoff 1 (1 / 2) u :=
              mul_le_mul_of_nonneg_right he h0
          _ = SelectiveArithmetic.cutoff 1 (1 / 2) u * Real.exp (σ * u) := mul_comm _ _
    rw [integral_const_mul] at hmono
    have hpos := Real.exp_pos (-(1 / 2))
    calc Real.exp (-(1 / 2)) = Real.exp (-(1 / 2)) * 1 := (mul_one _).symm
      _ ≤ Real.exp (-(1 / 2)) * ∫ u, SelectiveArithmetic.cutoff 1 (1 / 2) u ^ 2 :=
          mul_le_mul_of_nonneg_left hM1 hpos.le
      _ ≤ _ := hmono
  exact ⟨_, hg, hgc,
    lt_of_lt_of_le (Real.exp_pos _) (hdeg _ (by rw [abs_neg]; norm_num)),
    lt_of_lt_of_le (Real.exp_pos _) (hdeg _ (by norm_num))⟩

/-- The pole term against the zero sum, the archimedean energy and the deviation. -/
theorem scaled_neg_of_bounds {ε s D E Em Z A P Carch Sδ Mδ Mf M c : ℝ} (hss : ε * s = |ε|)
    (hD : 0 < D) (hE : 0 < E) (hEm : 0 ≤ Em) (hP : P = 2 * D * (2 + s * (E + Em)))
    (hA : |A - P| ≤ Carch) (hZ : |1 + ε| * |Z| ≤ |ε| * D / 2 * E)
    (hK : 4 * |ε| * D + |ε| * Carch + (2 * Mδ + |c|) * (4 * M) ≤ |ε| * D / 2 * E)
    (hS : |Sδ| ≤ Mδ * Mf) (hMf0 : 0 ≤ Mf) (hMf : Mf ≤ 4 * M) (hMδ : 0 ≤ Mδ) (hε : ε ≠ 0) :
    (1 + ε) * Z - ε * A - 2 * Sδ + c * Mf < 0 := by
  have hεpos : 0 < |ε| := abs_pos.mpr hε
  have h1 : (1 + ε) * Z ≤ |ε| * D / 2 * E := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact hZ
  have hεA : -(ε * A) ≤ -(ε * P) + |ε| * Carch := by
    have h := abs_le.mp (show |ε * (A - P)| ≤ |ε| * Carch by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hA (abs_nonneg _))
    have e : ε * (A - P) = ε * A - ε * P := by ring
    linarith [h.1]
  have hεP : ε * P = 4 * ε * D + 2 * |ε| * D * (E + Em) := by
    rw [hP]
    linear_combination (2 * D * (E + Em)) * hss
  have hfour : -(4 * ε * D) ≤ 4 * |ε| * D := by
    have := mul_nonneg (show 0 ≤ |ε| + ε by linarith [neg_abs_le ε]) hD.le
    linarith
  have hEmD : 0 ≤ 2 * |ε| * D * Em := by positivity
  have hS' : -(2 * Sδ) ≤ 2 * (Mδ * Mf) := by linarith [(abs_le.mp hS).1]
  have hc : c * Mf ≤ |c| * Mf := mul_le_mul_of_nonneg_right (le_abs_self c) hMf0
  have hM : (2 * Mδ + |c|) * Mf ≤ (2 * Mδ + |c|) * (4 * M) :=
    mul_le_mul_of_nonneg_left hMf (by positivity)
  have hDE : 0 < |ε| * D * E := by positivity
  linarith

/-- **With the contacts `(1 + ε)Λ + δ`, `ε ≠ 0`, no constant helps.** For every `c` some packet
has `Re W_{(1+ε)Λ+δ}(f ⋆ f̃) + c ∫f² < 0`. -/
theorem exists_packet_scaled_neg (hsum : Summable fun n => |δ n| / Real.sqrt n) {ε : ℝ}
    (hε : ε ≠ 0) (c : ℝ) :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧
      (_root_.RHTower.weilFullFunctional (fun n => (1 + ε) * (Λ n : ℝ) + δ n)
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re + c * ∫ u, f u ^ 2 < 0 := by
  obtain ⟨g, hg, hgc, hD₁0, hD₂0⟩ := exists_bump_pos_degrees
  have hD := mul_pos hD₁0 hD₂0
  -- the sign of the pair
  obtain ⟨s, hs, hεs⟩ : ∃ s : ℝ, s * s = 1 ∧ ε * s = |ε| := by
    rcases lt_or_gt_of_ne hε with h | h
    · exact ⟨-1, by norm_num, by rw [abs_of_neg h]; ring⟩
    · exact ⟨1, by norm_num, by rw [abs_of_pos h]; ring⟩
  have hεpos : 0 < |ε| := abs_pos.mpr hε
  -- the constant that the pole term has to beat
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 4 * |ε| *
      ((∫ u, g u * Real.exp (-(1 / 2) * u)) * ∫ u, g u * Real.exp (1 / 2 * u)) +
      |ε| * (1 / (2 * π) * ∫ τ : ℝ, 4 * ‖‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π))‖) +
      (2 * (∑' n : ℕ, |δ n| / Real.sqrt n) + |c|) * (4 * ∫ u, g u ^ 2) := ⟨_, rfl⟩
  have hη : 0 < |ε| *
      ((∫ u, g u * Real.exp (-(1 / 2) * u)) * ∫ u, g u * Real.exp (1 / 2 * u)) / 2 := by
    positivity
  have hZ := (tendsto_abs_zeroSum_bumpPair hg hgc hs).const_mul |1 + ε|
  rw [mul_zero] at hZ
  have hKt : Tendsto (fun T : ℝ => K * Real.exp (-(1 / 2 * T))) atTop (𝓝 0) := by
    have h := (tendsto_exp_neg_mul (show (0 : ℝ) < 1 / 2 by norm_num)).const_mul K
    rwa [mul_zero] at h
  obtain ⟨T, ⟨hZT, hKT⟩, -⟩ := ((hZ.eventually (gt_mem_nhds hη)).and
    (hKt.eventually (gt_mem_nhds hη))).and (eventually_ge_atTop (0 : ℝ)) |>.exists
  have hE0 : 0 < Real.exp (1 / 2 * T) := Real.exp_pos _
  have hEinv : Real.exp (-(1 / 2 * T)) * Real.exp (1 / 2 * T) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hEinv' : Real.exp (-(T / 2)) * Real.exp (1 / 2 * T) = 1 := by
    rw [show -(T / 2) = -(1 / 2 * T) by ring]
    exact hEinv
  -- the packet
  have hf := contDiff_bumpPair hg s T
  have hfc := hasCompactSupport_bumpPair hgc s T
  refine ⟨bumpPair g s T, hf, hfc, ?_⟩
  obtain ⟨Q, hQ⟩ := exists_packetAutocorr_log_eq_zero hfc
  rw [re_weilFullFunctional_scaled_eq ε δ hf hfc hQ]
  refine scaled_neg_of_bounds hεs hD hE0 (Real.exp_pos _).le
    (pole_bumpPair hg.continuous hgc hs T) (abs_weilArchRe_bumpPair_sub_le hg hgc hs T) ?_ ?_
    (abs_sum_deviation_le hsum hf.continuous hfc Q) (integral_nonneg fun u => sq_nonneg _)
    (integral_bumpPair_sq_le hg.continuous hgc hs T) (tsum_nonneg fun n => by positivity) hε
  · have h1 := mul_le_mul_of_nonneg_right hZT.le hE0.le
    rwa [mul_assoc, mul_assoc, hEinv', mul_one] at h1
  · have h1 := mul_le_mul_of_nonneg_right hKT.le hE0.le
    rw [mul_assoc, hEinv, mul_one] at h1
    rw [hK] at h1
    exact h1

/-- Bézout on the comb of the integers with the contacts `(1 + ε)Λ + δ` and the counterterm
`log(n/2π) + c`. -/
def CombBezoutScaled (ε : ℝ) (δ : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f → ∀ K : ℕ, 1 ≤ K →
    (∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) →
    ∀ l : ℝ, Tendsto (fun N : ℕ => degreeForm f (3 * K) N -
        c * ∑ n ∈ Ioc N (N + 3 * K * N), degreeSample f N n ^ 2 / n +
        2 * weightedContact (fun n => (1 + ε) * (Λ n : ℝ) + δ n) f (3 * K) N) atTop (𝓝 l) →
      l ≤ 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2))

/-- **A common factor on the contacts is refuted for every constant.** For `ε ≠ 0`, summable `δ`
and every `c`, Bézout fails, without hypothesis. -/
theorem not_combBezoutScaled (hsum : Summable fun n => |δ n| / Real.sqrt n) {ε : ℝ}
    (hε : ε ≠ 0) (c : ℝ) : ¬ CombBezoutScaled ε δ c := by
  intro h
  obtain ⟨g, hg, hgc, hneg⟩ := exists_packet_scaled_neg hsum hε c
  obtain ⟨t, K, hK, hsupp⟩ := exists_translate_window hgc
  have hg' : ContDiff ℝ 2 fun u => g (u - t) := hg.comp (contDiff_id.sub contDiff_const)
  have hgc' : HasCompactSupport fun u => g (u - t) :=
    hgc.comp_homeomorph (Homeomorph.subRight t)
  have hlim := (tendsto_degreeForm_add_weightedContact
    (fun n => (1 + ε) * (Λ n : ℝ) + δ n) hg' hgc' hK hsupp).sub
    ((tendsto_degreeMass hg'.continuous hK hsupp).const_mul c)
  have hle := h _ hg' hgc' K hK hsupp _ (hlim.congr fun N => by ring)
  rw [weilTest_packet_translate g t, integral_sub_right_eq_self (fun u => g u ^ 2) t] at hle
  linarith

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
