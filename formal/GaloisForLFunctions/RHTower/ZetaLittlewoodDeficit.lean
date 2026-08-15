import GaloisForLFunctions.RHTower.RealTwistDeficitTransfer
import GaloisForLFunctions.RHTower.Sieve.ZetaShiftedLineRate

/-!
# The unconditional Littlewood deficit on the shifted line

Littlewood's rate, transported to the abscissa `1 + 1/log x`, is uniform over the whole
polynomial frequency horizon `1 ≤ |τ| ≤ x^B`:

```text
|ζ(1 + 1/log x + iτ)| ≤ C_B log x / log log x,
```

so the one-line deficit of `log|ζ|` below its trivial scale is at least

```text
log log x - log |ζ(1 + 1/log x + iτ)| ≥ log log log x - O_B(1).
```

Three regimes are combined: the compact frequency range, where the harmonic truncation suffices;
the range where the Littlewood scale `L = log(τ/2π)` is below `√log x`, where the numerator is
small; and the range where it is above, where the denominator is large.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The frequency threshold past which the Littlewood order conditions hold. -/
def littlewoodFreqThreshold : ℝ :=
  max (16 * Real.pi)
    (max (2 * Real.pi * Real.exp (Sieve.orderThreshold 2))
      (2 * Real.pi * Real.exp 2211904))

theorem littlewoodFreqThreshold_pos : 0 < littlewoodFreqThreshold := by
  have hπ := Real.pi_pos
  refine lt_of_lt_of_le (by positivity : (0:ℝ) < 16 * Real.pi) ?_
  exact le_max_left _ _

theorem sixteen_pi_le_littlewoodFreqThreshold : 16 * Real.pi ≤ littlewoodFreqThreshold :=
  le_max_left _ _

/-- Past the threshold, the Littlewood scale is large. -/
theorem littlewoodScale_ge {t : ℝ} (ht : littlewoodFreqThreshold ≤ t) :
    (2211904 : ℝ) ≤ Real.log (t / (2 * Real.pi)) := by
  have hπ := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hle : 2 * Real.pi * Real.exp 2211904 ≤ t :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have hquot : Real.exp 2211904 ≤ t / (2 * Real.pi) := by
    rw [le_div_iff₀ h2π]
    linarith
  have h := Real.log_le_log (Real.exp_pos 2211904) hquot
  rwa [Real.log_exp] at h

theorem orderThreshold_le_of_ge {t : ℝ} (ht : littlewoodFreqThreshold ≤ t) :
    Sieve.orderThreshold 2 ≤ Real.log (t / (2 * Real.pi)) := by
  have hπ := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hle : 2 * Real.pi * Real.exp (Sieve.orderThreshold 2) ≤ t :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have hquot : Real.exp (Sieve.orderThreshold 2) ≤ t / (2 * Real.pi) := by
    rw [le_div_iff₀ h2π]
    linarith
  have h := Real.log_le_log (Real.exp_pos _) hquot
  rwa [Real.log_exp] at h

/-- Past the threshold the order lower bound clears `4/3` with room to spare. -/
theorem orderLowerBound_ge_of_ge {t : ℝ} (ht : littlewoodFreqThreshold ≤ t) :
    5 / 3 ≤ Sieve.orderLowerBound (Real.log (t / (2 * Real.pi))) := by
  have hL := littlewoodScale_ge ht
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : (32 : ℝ) ≤ Real.log (t / (2 * Real.pi)) / 69122 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hlog : 5 * Real.log 2 ≤ Real.log (Real.log (t / (2 * Real.pi)) / 69122) := by
    have h32 : Real.log 32 ≤ Real.log (Real.log (t / (2 * Real.pi)) / 69122) :=
      Real.log_le_log (by norm_num) hratio
    have hval : Real.log 32 = 5 * Real.log 2 := by
      rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    linarith [h32, hval.le, hval.ge]
  rw [Sieve.orderLowerBound, le_div_iff₀ (by positivity)]
  linarith

/-- **The shifted line bound at every admissible frequency past the threshold.** -/
theorem norm_riemannZeta_shifted_le_of_ge {t δ : ℝ} (ht : littlewoodFreqThreshold ≤ t)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ‖riemannZeta (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ))‖
      ≤ 33 + 2 * Real.log (t / (2 * Real.pi))
          / (Sieve.orderLowerBound (Real.log (t / (2 * Real.pi))) - 4 / 3) := by
  refine Sieve.norm_riemannZeta_shifted_line_rate ?_ (orderThreshold_le_of_ge ht) ?_ hδ0 hδ1
  · exact le_trans sixteen_pi_le_littlewoodFreqThreshold ht
  · have := orderLowerBound_ge_of_ge ht
    linarith

/-- **The harmonic bound on the compact frequency range.** -/
theorem norm_riemannZeta_shifted_le_harmonic {t δ : ℝ} (ht : 1 ≤ |t|) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) :
    ‖riemannZeta (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ ≤ 4 + |t| := by
  obtain ⟨w, hwdef⟩ : ∃ w : ℂ, w = ((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ) := ⟨_, rfl⟩
  have hwre : w.re = 1 + δ := by
    rw [hwdef]; simp
  have hwim : w.im = t := by
    rw [hwdef]; simp
  have hre : (1 : ℝ) ≤ w.re := by
    rw [hwre]; linarith
  have him : (1 : ℝ) ≤ |w.im| := by
    rw [hwim]; exact ht
  have hbase := Sieve.norm_riemannZeta_ge_one_le hre him (N := 1) le_rfl
  have hnormw : ‖w‖ ≤ 2 + |t| := by
    rw [hwdef]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖((1 + δ : ℝ) : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have h2 : ‖Complex.I * (t : ℂ)‖ = |t| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    linarith [h1, h2.le, h2.ge]
  rw [← hwdef]
  simp only [Nat.cast_one, Real.log_one, div_one] at hbase
  linarith

/-- The conjugate frequency has the same modulus. -/
theorem norm_riemannZeta_shifted_neg (δ t : ℝ) :
    ‖riemannZeta (((1 + δ : ℝ) : ℂ) + Complex.I * ((-t : ℝ) : ℂ))‖
      = ‖riemannZeta (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ := by
  have hconj : ((1 + δ : ℝ) : ℂ) + Complex.I * ((-t : ℝ) : ℂ)
      = (starRingEnd ℂ) (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ)) := by
    rw [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
    push_cast
    ring
  rw [hconj, riemannZeta_conj, RCLike.norm_conj]

/-! ## The uniform horizon bound -/

/-- The threshold past which the horizon bound holds, stated for `log x`. -/
def zetaHorizonLogThreshold : ℝ :=
  Real.exp (max 4 (4 * Real.log 69122 + 16 * Real.log 2))

theorem log_le_half {v : ℝ} (hv : 0 < v) : Real.log v ≤ v / 2 := by
  have hw : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv.le
  have hwpos : (0 : ℝ) < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hlog : Real.log v = 2 * Real.log (Real.sqrt v) := by
    rw [Real.log_sqrt hv.le]
    ring
  have hstep : Real.log (Real.sqrt v) ≤ Real.sqrt v - 1 := Real.log_le_sub_one_of_pos hwpos
  nlinarith [hlog.le, hlog.ge, hstep, sq_nonneg (Real.sqrt v - 2), hw]

theorem log_le_sqrt {u : ℝ} (hu : 0 < u) : Real.log u ≤ Real.sqrt u := by
  have hs : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hlog : Real.log u = 2 * Real.log (Real.sqrt u) := by
    rw [Real.log_sqrt hu.le]
    ring
  have h := log_le_half hs
  linarith [hlog.le, hlog.ge, h]

theorem one_le_div_log {l : ℝ} (hl : 4 ≤ l) : 1 ≤ l / Real.log l := by
  have hl0 : (0 : ℝ) < l := by linarith
  have hloglpos : (0 : ℝ) < Real.log l := Real.log_pos (by linarith)
  rw [le_div_iff₀ hloglpos]
  have h := Real.log_le_sub_one_of_pos hl0
  linarith

theorem sqrt_le_div_log {l : ℝ} (hl : 4 ≤ l) : Real.sqrt l ≤ l / Real.log l := by
  have hl0 : (0 : ℝ) < l := by linarith
  have hloglpos : (0 : ℝ) < Real.log l := Real.log_pos (by linarith)
  have hsq : Real.sqrt l * Real.sqrt l = l := Real.mul_self_sqrt hl0.le
  have hlogle := log_le_sqrt hl0
  rw [le_div_iff₀ hloglpos]
  nlinarith [hlogle, hsq, Real.sqrt_nonneg l]

/-- Small Littlewood scale: the numerator carries the bound. -/
theorem littlewood_small_scale_le {l L oLB : ℝ} (hl : 4 ≤ l) (hL0 : 0 < L)
    (hLsmall : L ≤ Real.sqrt l) (hoLB : 5 / 3 ≤ oLB) :
    33 + 2 * L / (oLB - 4 / 3) ≤ 39 * (l / Real.log l) := by
  have hoLBpos : (0 : ℝ) < oLB - 4 / 3 := by linarith
  have hdiv : 2 * L / (oLB - 4 / 3) ≤ 6 * Real.sqrt l := by
    rw [div_le_iff₀ hoLBpos]
    nlinarith [hLsmall, hL0, hoLB, Real.sqrt_nonneg l]
  have hsqrt := sqrt_le_div_log hl
  have hone := one_le_div_log hl
  nlinarith [hdiv, hsqrt, hone]

/-- Large Littlewood scale: the denominator carries the bound. -/
theorem littlewood_large_scale_le {B l L : ℝ} (hB : 0 < B) (hl : 4 ≤ l)
    (hthr : 4 * Real.log 69122 + 16 * Real.log 2 ≤ Real.log l) (hL0 : 0 < L)
    (hLle : L ≤ B * l) (hlogL : Real.log l / 2 ≤ Real.log L) :
    33 + 2 * L / (Sieve.orderLowerBound L - 4 / 3)
      ≤ (33 + 24 * B * Real.log 2) * (l / Real.log l) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl0 : (0 : ℝ) < l := by linarith
  have hloglpos : (0 : ℝ) < Real.log l := Real.log_pos (by linarith)
  have hsplit : Sieve.orderLowerBound L = (Real.log L - Real.log 69122) / (3 * Real.log 2) := by
    rw [Sieve.orderLowerBound, Real.log_div (ne_of_gt hL0) (by norm_num)]
  have hden : Real.log l / (12 * Real.log 2) ≤ Sieve.orderLowerBound L - 4 / 3 := by
    rw [hsplit, le_sub_iff_add_le, div_add' _ _ _ (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hlogL, hthr, hlog2, hloglpos]
  have hdenpos : (0 : ℝ) < Real.log l / (12 * Real.log 2) := by positivity
  have hoLBpos : (0 : ℝ) < Sieve.orderLowerBound L - 4 / 3 := by linarith
  have hone := one_le_div_log hl
  have hdiv : 2 * L / (Sieve.orderLowerBound L - 4 / 3)
      ≤ 24 * B * Real.log 2 * (l / Real.log l) := by
    rw [div_le_iff₀ hoLBpos]
    have hprod : 24 * B * Real.log 2 * (l / Real.log l) * (Real.log l / (12 * Real.log 2))
        = 2 * (B * l) := by
      field_simp
      ring
    have hcoefnn : (0 : ℝ) ≤ 24 * B * Real.log 2 * (l / Real.log l) := by positivity
    nlinarith [hLle, hden, hprod.le, hprod.ge, hcoefnn]
  nlinarith [hdiv, hone, hB, hlog2]

/-- **The uniform Littlewood bound across the polynomial frequency horizon.** -/
theorem norm_riemannZeta_horizon_le {B x τ : ℝ} (hB : 0 < B)
    (hx : zetaHorizonLogThreshold ≤ Real.log x) (hx0 : 0 < x)
    (hτ : 1 ≤ |τ|) (hτB : |τ| ≤ x ^ B) :
    ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (τ : ℂ))‖
      ≤ (37 + littlewoodFreqThreshold + 24 * B * Real.log 2)
          * (Real.log x / Real.log (Real.log x)) := by
  have hπ := Real.pi_pos
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨l, hldef⟩ : ∃ l : ℝ, l = Real.log x := ⟨_, rfl⟩
  rw [← hldef] at hx
  have hexp4 : (4 : ℝ) < Real.exp 4 := by
    have h := Real.add_one_le_exp (4 : ℝ)
    linarith
  have hmax4 : (4 : ℝ) ≤ max 4 (4 * Real.log 69122 + 16 * Real.log 2) := le_max_left _ _
  have hexpmono : Real.exp 4 ≤ Real.exp (max 4 (4 * Real.log 69122 + 16 * Real.log 2)) :=
    Real.exp_le_exp.mpr hmax4
  have h4 : (4 : ℝ) ≤ l := by
    have : Real.exp (max 4 (4 * Real.log 69122 + 16 * Real.log 2)) ≤ l := by
      rw [zetaHorizonLogThreshold] at hx
      exact hx
    linarith
  have hthr : 4 * Real.log 69122 + 16 * Real.log 2 ≤ Real.log l := by
    have hle : Real.exp (max 4 (4 * Real.log 69122 + 16 * Real.log 2)) ≤ l := by
      rw [zetaHorizonLogThreshold] at hx
      exact hx
    have hlog := Real.log_le_log (Real.exp_pos _) hle
    rw [Real.log_exp] at hlog
    exact le_trans (le_max_right _ _) hlog
  have hl0 : (0 : ℝ) < l := by linarith
  have hloglpos : (0 : ℝ) < Real.log l := Real.log_pos (by linarith)
  have hratio1 : (1 : ℝ) ≤ l / Real.log l := by
    rw [le_div_iff₀ hloglpos]
    have h := Real.log_le_sub_one_of_pos hl0
    linarith
  have hδ0 : (0 : ℝ) ≤ 1 / l := by positivity
  have hδ1 : 1 / l ≤ 1 := by
    rw [div_le_one hl0]
    linarith
  have hcoef : (0 : ℝ) < 37 + littlewoodFreqThreshold + 24 * B * Real.log 2 := by
    have := littlewoodFreqThreshold_pos
    positivity
  -- reduce to a positive frequency
  have habs : ‖riemannZeta (((1 + 1 / l : ℝ) : ℂ) + Complex.I * (τ : ℂ))‖
      = ‖riemannZeta (((1 + 1 / l : ℝ) : ℂ) + Complex.I * ((|τ| : ℝ) : ℂ))‖ := by
    rcases abs_cases τ with ⟨heq, _⟩ | ⟨heq, _⟩
    · rw [heq]
    · rw [heq, norm_riemannZeta_shifted_neg]
  rw [← hldef, habs]
  rcases le_or_gt (|τ|) littlewoodFreqThreshold with hsmall | hbig
  · -- the compact range
    have hharm := norm_riemannZeta_shifted_le_harmonic (t := |τ|) (δ := 1 / l)
      (by rw [abs_of_nonneg (abs_nonneg τ)]; exact hτ) hδ0 hδ1
    rw [abs_of_nonneg (abs_nonneg τ)] at hharm
    have hstep : (4 : ℝ) + |τ| ≤ 4 + littlewoodFreqThreshold := by linarith
    have hfinal : (4 : ℝ) + littlewoodFreqThreshold
        ≤ (37 + littlewoodFreqThreshold + 24 * B * Real.log 2) * (l / Real.log l) := by
      have hcoefle : (4 : ℝ) + littlewoodFreqThreshold
          ≤ 37 + littlewoodFreqThreshold + 24 * B * Real.log 2 := by
        have : (0 : ℝ) < 24 * B * Real.log 2 := by positivity
        linarith
      nlinarith [hratio1, hcoefle, hcoef]
    linarith
  · -- the Littlewood range
    have hτpos : (0 : ℝ) < |τ| := lt_of_lt_of_le (by linarith [littlewoodFreqThreshold_pos]) hbig.le
    have hthrle : littlewoodFreqThreshold ≤ |τ| := hbig.le
    have hmain := norm_riemannZeta_shifted_le_of_ge (t := |τ|) (δ := 1 / l) hthrle hδ0 hδ1
    obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (|τ| / (2 * Real.pi)) := ⟨_, rfl⟩
    rw [← hLdef] at hmain
    have hLbig : (2211904 : ℝ) ≤ L := by
      rw [hLdef]
      exact littlewoodScale_ge hthrle
    have hL0 : (0 : ℝ) < L := by linarith
    have hoLB : 5 / 3 ≤ Sieve.orderLowerBound L := by
      rw [hLdef]
      exact orderLowerBound_ge_of_ge hthrle
    have hoLBpos : (0 : ℝ) < Sieve.orderLowerBound L - 4 / 3 := by linarith
    -- the Littlewood scale is at most `B l`
    have hLle : L ≤ B * l := by
      have hlogτ : Real.log (|τ|) ≤ B * l := by
        have h := Real.log_le_log hτpos hτB
        rw [Real.log_rpow hx0, ← hldef] at h
        exact h
      have hLsplit : L = Real.log (|τ|) - Real.log (2 * Real.pi) := by
        rw [hLdef, Real.log_div (ne_of_gt hτpos) (by positivity)]
      have hlogπ : 0 ≤ Real.log (2 * Real.pi) := by
        refine Real.log_nonneg ?_
        nlinarith [Real.pi_gt_three]
      linarith [hLsplit.le, hLsplit.ge]
    rcases le_or_gt L (Real.sqrt l) with hLsmall | hLlarge
    · -- small Littlewood scale: the numerator is small
      have hsmallbound := littlewood_small_scale_le h4 hL0 hLsmall hoLB
      have hcoefle : (39 : ℝ) ≤ 37 + littlewoodFreqThreshold + 24 * B * Real.log 2 := by
        have h1 : (16 : ℝ) * Real.pi ≤ littlewoodFreqThreshold :=
          sixteen_pi_le_littlewoodFreqThreshold
        have h2 : (0 : ℝ) < 24 * B * Real.log 2 := by positivity
        nlinarith [Real.pi_gt_three]
      have hratio0 : (0 : ℝ) ≤ l / Real.log l := by positivity
      nlinarith [hmain, hsmallbound, hcoefle, hratio0]
    · -- large Littlewood scale: the denominator is large
      have hlogL : Real.log l / 2 ≤ Real.log L := by
        have h := Real.log_le_log (Real.sqrt_pos.mpr hl0) hLlarge.le
        have hval : Real.log (Real.sqrt l) = Real.log l / 2 := Real.log_sqrt hl0.le
        linarith [h, hval.le, hval.ge]
      have hlargebound := littlewood_large_scale_le hB h4 hthr hL0 hLle hlogL
      have hcoefle : (33 : ℝ) + 24 * B * Real.log 2
          ≤ 37 + littlewoodFreqThreshold + 24 * B * Real.log 2 := by
        have := littlewoodFreqThreshold_pos
        linarith
      have hratio0 : (0 : ℝ) ≤ l / Real.log l := by positivity
      nlinarith [hmain, hlargebound, hcoefle, hratio0]

/-- **(Z2c)–(Z2d) The unconditional Littlewood deficit.**  Uniformly across the polynomial
frequency horizon, the shifted one-line deficit of `log|ζ|` below `log log x` is at least
`log log log x` up to an absolute constant. -/
theorem zetaLineDeficit_ge {B x τ : ℝ} (hB : 0 < B)
    (hx : zetaHorizonLogThreshold ≤ Real.log x) (hx0 : 0 < x)
    (hτ : 1 ≤ |τ|) (hτB : |τ| ≤ x ^ B) :
    Real.log (Real.log (Real.log x))
        - Real.log (37 + littlewoodFreqThreshold + 24 * B * Real.log 2)
      ≤ zetaLineDeficit τ x := by
  have hπ := Real.pi_pos
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hexp4 : (4 : ℝ) < Real.exp 4 := by
    have h := Real.add_one_le_exp (4 : ℝ)
    linarith
  have hmax4 : (4 : ℝ) ≤ max 4 (4 * Real.log 69122 + 16 * Real.log 2) := le_max_left _ _
  have h4 : (4 : ℝ) ≤ Real.log x := by
    have hle : Real.exp (max 4 (4 * Real.log 69122 + 16 * Real.log 2)) ≤ Real.log x := by
      rw [zetaHorizonLogThreshold] at hx
      exact hx
    have := Real.exp_le_exp.mpr hmax4
    linarith
  have hl0 : (0 : ℝ) < Real.log x := by linarith
  have hloglpos : (0 : ℝ) < Real.log (Real.log x) := Real.log_pos (by linarith)
  have hcoef : (0 : ℝ) < 37 + littlewoodFreqThreshold + 24 * B * Real.log 2 := by
    have := littlewoodFreqThreshold_pos
    positivity
  have hbound := norm_riemannZeta_horizon_le hB hx hx0 hτ hτB
  have hpoint : zetaLinePoint (1 + 1 / Real.log x) τ
      = ((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (τ : ℂ) := by
    rw [zetaLinePoint]
    push_cast
    ring
  rw [zetaLineDeficit, hpoint]
  have hratio1 := one_le_div_log h4
  have hprod1 : (1 : ℝ)
      ≤ (37 + littlewoodFreqThreshold + 24 * B * Real.log 2)
        * (Real.log x / Real.log (Real.log x)) := by
    nlinarith [hratio1, hcoef, littlewoodFreqThreshold_pos]
  have hlogle : Real.log ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (τ : ℂ))‖
      ≤ Real.log ((37 + littlewoodFreqThreshold + 24 * B * Real.log 2)
          * (Real.log x / Real.log (Real.log x))) := by
    rcases le_or_gt ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (τ : ℂ))‖ 0
      with hzero | hpos
    · have heq : ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (τ : ℂ))‖ = 0 :=
        le_antisymm hzero (norm_nonneg _)
      rw [heq, Real.log_zero]
      exact Real.log_nonneg hprod1
    · exact Real.log_le_log hpos hbound
  have hlogval : Real.log ((37 + littlewoodFreqThreshold + 24 * B * Real.log 2)
      * (Real.log x / Real.log (Real.log x)))
      = Real.log (37 + littlewoodFreqThreshold + 24 * B * Real.log 2)
        + Real.log (Real.log x) - Real.log (Real.log (Real.log x)) := by
    rw [Real.log_mul (ne_of_gt hcoef) (by positivity),
      Real.log_div (ne_of_gt hl0) (ne_of_gt hloglpos)]
    ring
  rw [hlogval] at hlogle
  linarith

/-- **The unconditional real-twist gap.**  For every real prime sequence in the closed unit disc,
the pretentious distance to an archimedean character at any frequency of the polynomial horizon is
at least a quarter of the Littlewood deficit `log log log x - O_B(1)`. -/
theorem quarter_littlewoodDeficit_le_pretentiousDistSq {r : ℕ → ℝ} (hr : ∀ n, |r n| ≤ 1)
    {B x α : ℝ} (hB : 0 < B) (hx : zetaHorizonLogThreshold ≤ Real.log x) (hx0 : 0 < x)
    (hα : 1 ≤ |2 * α|) (hαB : |2 * α| ≤ x ^ B) :
    (Real.log (Real.log (Real.log x))
        - Real.log (37 + littlewoodFreqThreshold + 24 * B * Real.log 2)
        - zetaDeficitConst) / 4
      ≤ pretentiousDistSq (fun n => (r n : ℂ)) (primeChar α) x := by
  have hexp4 : (4 : ℝ) < Real.exp 4 := by
    have h := Real.add_one_le_exp (4 : ℝ)
    linarith
  have hmax4 : (4 : ℝ) ≤ max 4 (4 * Real.log 69122 + 16 * Real.log 2) := le_max_left _ _
  have hle : Real.exp (max 4 (4 * Real.log 69122 + 16 * Real.log 2)) ≤ Real.log x := by
    rw [zetaHorizonLogThreshold] at hx
    exact hx
  have hexpmono := Real.exp_le_exp.mpr hmax4
  have h4 : (4 : ℝ) ≤ Real.log x := by linarith
  have hxexp : Real.exp 2 ≤ x := by
    have hlog : Real.log (Real.exp 2) ≤ Real.log x := by
      rw [Real.log_exp]
      linarith
    have h := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log (Real.exp_pos 2), Real.exp_log hx0] at h
  have hdeficit := zetaLineDeficit_ge (B := B) (x := x) (τ := 2 * α) hB hx hx0 hα hαB
  have htransfer := quarter_zetaLineDeficit_le_pretentiousDistSq (r := r) hr (α := α) (x := x)
    hxexp
  have hmono : (Real.log (Real.log (Real.log x))
      - Real.log (37 + littlewoodFreqThreshold + 24 * B * Real.log 2) - zetaDeficitConst) / 4
      ≤ (zetaLineDeficit (2 * α) x - zetaDeficitConst) / 4 := by
    have hnum : Real.log (Real.log (Real.log x))
        - Real.log (37 + littlewoodFreqThreshold + 24 * B * Real.log 2) - zetaDeficitConst
        ≤ zetaLineDeficit (2 * α) x - zetaDeficitConst := by linarith
    exact div_le_div_of_nonneg_right hnum (by norm_num : (0:ℝ) ≤ 4)

end

end RHTower
