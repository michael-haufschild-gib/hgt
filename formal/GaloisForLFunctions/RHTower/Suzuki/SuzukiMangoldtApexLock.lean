import GaloisForLFunctions.RHTower.Suzuki.SuzukiMangoldtLogHaarTransport

/-!
# Mangoldt atoms lock to unique Suzuki apices

The bi-causal transport cannot be completed at the turning seam by assigning each atom a
positive-volume subset of its pointwise value-dominating superlevel.  At width `log 2` and aperture
`log (2n) / 2`, the actual Mangoldt node `2 log n` is the unique positive-lag maximizer of the
positive archimedean sample channel.  Its dominating superlevel is therefore null, whereas every
prime-power atom has positive mass.

The positive survivor is an exact source-specific apex rigidity law.  It forces any future seam
transport to group apex atoms with flank atoms before enforcing capacity one.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- Fixed small-lag part of Suzuki's positive rectangular sample channel. -/
def suzukiRectangularFixedArchChannel (L t : ℝ) : ℝ :=
  Real.exp (t / 4) * (2 * max 0 (L - t / 2))

/-- Moving large-lag part of Suzuki's positive rectangular sample channel. -/
def suzukiRectangularMovingArchChannel (L a t : ℝ) : ℝ :=
  Real.exp (t / 4) * max 0 (L - |t / 2 - (2 * a - L)|)

/-- Lag at the geometric center of the moving rectangular tent. -/
def suzukiRectangularMovingApex (L a : ℝ) : ℝ := 4 * a - 2 * L

/-- On the positive axis, the sample channel splits into fixed and moving pieces. -/
theorem suzukiRectangularPositiveArchSampleChannel_eq_fixed_add_moving
    {L a t : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) (ht : 0 ≤ t) :
    suzukiRectangularPositiveArchSampleChannel L a t =
      suzukiRectangularFixedArchChannel L t +
        suzukiRectangularMovingArchChannel L a t := by
  rw [suzukiRectangularPositiveArchSampleChannel,
    rectangularTwoEdgeAutocorrelation_eq_fixed_add_moving_tent hL ha (by positivity)]
  rw [suzukiRectangularFixedArchChannel, suzukiRectangularMovingArchChannel]
  ring

/-- For width below two, the exponentially tilted fixed tent strictly decreases away from zero. -/
theorem suzukiRectangularFixedArchChannel_lt_zeroLag
    {L t : ℝ} (hL : 0 < L) (hL2 : L < 2) (ht : 0 < t) :
    suzukiRectangularFixedArchChannel L t < 2 * L := by
  rw [suzukiRectangularFixedArchChannel]
  by_cases hheight : 0 < L - t / 2
  · rw [max_eq_right hheight.le]
    have hlinear : L - t / 2 < L * (1 - t / 4) := by
      nlinarith
    have hexp : 1 - t / 4 < Real.exp (-(t / 4)) :=
      Real.one_sub_lt_exp_neg (by linarith)
    have hscaled : L - t / 2 < L * Real.exp (-(t / 4)) :=
      hlinear.trans (mul_lt_mul_of_pos_left hexp hL)
    have hcore : Real.exp (t / 4) * (L - t / 2) < L := by
      calc
        Real.exp (t / 4) * (L - t / 2) <
            Real.exp (t / 4) * (L * Real.exp (-(t / 4))) :=
          mul_lt_mul_of_pos_left hscaled (Real.exp_pos _)
        _ = L := by
          rw [show Real.exp (t / 4) * (L * Real.exp (-(t / 4))) =
              L * (Real.exp (t / 4) * Real.exp (-(t / 4))) by ring,
            ← Real.exp_add]
          simp
    nlinarith
  · rw [max_eq_left (le_of_not_gt hheight)]
    nlinarith

/-- Exact height of the moving channel at its geometric apex. -/
theorem suzukiRectangularMovingArchChannel_at_apex
    {L a : ℝ} (hL : 0 ≤ L) :
    suzukiRectangularMovingArchChannel L a (suzukiRectangularMovingApex L a) =
      Real.exp (suzukiRectangularMovingApex L a / 4) * L := by
  rw [suzukiRectangularMovingArchChannel, suzukiRectangularMovingApex]
  have hcenter : (4 * a - 2 * L) / 2 - (2 * a - L) = 0 := by ring
  rw [hcenter, abs_zero, sub_zero, max_eq_right hL]

/-- Below width two, exponential tilt preserves a unique strict maximum of the moving tent. -/
theorem suzukiRectangularMovingArchChannel_lt_apex
    {L a t : ℝ} (hL : 0 < L) (hL2 : L < 2)
    (hne : t ≠ suzukiRectangularMovingApex L a) :
    suzukiRectangularMovingArchChannel L a t <
      suzukiRectangularMovingArchChannel L a (suzukiRectangularMovingApex L a) := by
  rcases lt_or_gt_of_ne hne with hleft | hright
  · have hheight : max 0 (L - |t / 2 - (2 * a - L)|) ≤ L := by
      apply max_le hL.le
      linarith [abs_nonneg (t / 2 - (2 * a - L))]
    rw [suzukiRectangularMovingArchChannel,
      suzukiRectangularMovingArchChannel_at_apex hL.le]
    calc
      Real.exp (t / 4) * max 0 (L - |t / 2 - (2 * a - L)|) ≤
          Real.exp (t / 4) * L :=
        mul_le_mul_of_nonneg_left hheight (Real.exp_pos _).le
      _ < Real.exp (suzukiRectangularMovingApex L a / 4) * L := by
        apply mul_lt_mul_of_pos_right _ hL
        rw [Real.exp_lt_exp]
        linarith
  · have harg : 0 ≤ t / 2 - (2 * a - L) := by
      rw [suzukiRectangularMovingApex] at hright
      linarith
    have hheightEq : L - (t / 2 - (2 * a - L)) =
        L - (t - suzukiRectangularMovingApex L a) / 2 := by
      rw [suzukiRectangularMovingApex]
      ring
    rw [suzukiRectangularMovingArchChannel, abs_of_nonneg harg, hheightEq]
    by_cases hheight : 0 < L - (t - suzukiRectangularMovingApex L a) / 2
    · rw [max_eq_right hheight.le]
      have hdelta : 0 < (t - suzukiRectangularMovingApex L a) / 4 := by linarith
      have hlinear : L - (t - suzukiRectangularMovingApex L a) / 2 <
          L * (1 - (t - suzukiRectangularMovingApex L a) / 4) := by
        nlinarith
      have hexp : 1 - (t - suzukiRectangularMovingApex L a) / 4 <
          Real.exp (-((t - suzukiRectangularMovingApex L a) / 4)) :=
        Real.one_sub_lt_exp_neg hdelta.ne'
      have hscaled : L - (t - suzukiRectangularMovingApex L a) / 2 <
          L * Real.exp (-((t - suzukiRectangularMovingApex L a) / 4)) :=
        hlinear.trans (mul_lt_mul_of_pos_left hexp hL)
      have hcore : Real.exp ((t - suzukiRectangularMovingApex L a) / 4) *
          (L - (t - suzukiRectangularMovingApex L a) / 2) < L := by
        calc
          _ < Real.exp ((t - suzukiRectangularMovingApex L a) / 4) *
                (L * Real.exp (-((t - suzukiRectangularMovingApex L a) / 4))) :=
            mul_lt_mul_of_pos_left hscaled (Real.exp_pos _)
          _ = L := by
            rw [show Real.exp ((t - suzukiRectangularMovingApex L a) / 4) *
                  (L * Real.exp (-((t - suzukiRectangularMovingApex L a) / 4))) =
                L * (Real.exp ((t - suzukiRectangularMovingApex L a) / 4) *
                  Real.exp (-((t - suzukiRectangularMovingApex L a) / 4))) by ring,
              ← Real.exp_add]
            simp
      have hexpSplit : Real.exp (t / 4) =
          Real.exp (suzukiRectangularMovingApex L a / 4) *
            Real.exp ((t - suzukiRectangularMovingApex L a) / 4) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexpSplit, suzukiRectangularMovingArchChannel_at_apex hL.le]
      calc
        _ = Real.exp (suzukiRectangularMovingApex L a / 4) *
            (Real.exp ((t - suzukiRectangularMovingApex L a) / 4) *
              (L - (t - suzukiRectangularMovingApex L a) / 2)) := by ring
        _ < Real.exp (suzukiRectangularMovingApex L a / 4) * L :=
          mul_lt_mul_of_pos_left hcore (Real.exp_pos _)
    · rw [max_eq_left (le_of_not_gt hheight),
        suzukiRectangularMovingArchChannel_at_apex hL.le]
      simpa using mul_pos (Real.exp_pos (suzukiRectangularMovingApex L a / 4)) hL

/-- At a separated aperture, the full positive channel takes the moving-apex value. -/
theorem suzukiRectangularPositiveArchSampleChannel_at_movingApex
    {L a : ℝ} (hL : 0 < L) (ha : 3 * L / 2 ≤ a) :
    suzukiRectangularPositiveArchSampleChannel L a
        (suzukiRectangularMovingApex L a) =
      Real.exp (suzukiRectangularMovingApex L a / 4) * L := by
  have hLa : L ≤ a := by linarith
  have hapex0 : 0 ≤ suzukiRectangularMovingApex L a := by
    rw [suzukiRectangularMovingApex]
    linarith
  rw [suzukiRectangularPositiveArchSampleChannel_eq_fixed_add_moving hL.le hLa hapex0,
    suzukiRectangularFixedArchChannel, suzukiRectangularMovingArchChannel_at_apex hL.le]
  have hfixed : L - suzukiRectangularMovingApex L a / 2 ≤ 0 := by
    rw [suzukiRectangularMovingApex]
    linarith
  rw [max_eq_left hfixed]
  ring

/-- If the moving support is separated from the fixed support and its apex is at least as high,
the full Suzuki sample channel has no other positive-lag maximizer. -/
theorem suzukiRectangularPositiveArchSampleChannel_lt_movingApex
    {L a t : ℝ} (hL : 0 < L) (hL2 : L < 2)
    (ha : 3 * L / 2 ≤ a) (hheight : Real.log 2 ≤ a - L / 2)
    (ht : 0 < t) (hne : t ≠ suzukiRectangularMovingApex L a) :
    suzukiRectangularPositiveArchSampleChannel L a t <
      suzukiRectangularPositiveArchSampleChannel L a
        (suzukiRectangularMovingApex L a) := by
  have hLa : L ≤ a := by linarith
  have hdecomp := suzukiRectangularPositiveArchSampleChannel_eq_fixed_add_moving
    hL.le hLa ht.le
  have hapex := suzukiRectangularPositiveArchSampleChannel_at_movingApex hL ha
  have hexpTwo : 2 ≤ Real.exp (suzukiRectangularMovingApex L a / 4) := by
    rw [suzukiRectangularMovingApex]
    have := (Real.exp_le_exp.mpr hheight)
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at this
    rw [show (4 * a - 2 * L) / 4 = a - L / 2 by ring]
    exact this
  have hfixedBound : 2 * L ≤
      Real.exp (suzukiRectangularMovingApex L a / 4) * L :=
    mul_le_mul_of_nonneg_right hexpTwo hL.le
  by_cases htSmall : t < 2 * L
  · have harg : t / 2 - (2 * a - L) ≤ 0 := by linarith
    have habs : L ≤ |t / 2 - (2 * a - L)| := by
      rw [abs_of_nonpos harg]
      linarith
    have hmoving : suzukiRectangularMovingArchChannel L a t = 0 := by
      rw [suzukiRectangularMovingArchChannel, max_eq_left (by linarith)]
      ring
    rw [hdecomp, hmoving, add_zero, hapex]
    exact (suzukiRectangularFixedArchChannel_lt_zeroLag hL hL2 ht).trans_le hfixedBound
  · have hfixed : suzukiRectangularFixedArchChannel L t = 0 := by
      rw [suzukiRectangularFixedArchChannel, max_eq_left (by linarith)]
      ring
    rw [hdecomp, hfixed, zero_add, hapex,
      ← suzukiRectangularMovingArchChannel_at_apex hL.le]
    exact suzukiRectangularMovingArchChannel_lt_apex hL hL2 hne

/-- Unique-maximizer form of the separated moving-apex theorem. -/
theorem suzukiRectangularPositiveArchSampleChannel_apex_le_iff
    {L a t : ℝ} (hL : 0 < L) (hL2 : L < 2)
    (ha : 3 * L / 2 ≤ a) (hheight : Real.log 2 ≤ a - L / 2)
    (ht : 0 < t) :
    suzukiRectangularPositiveArchSampleChannel L a
        (suzukiRectangularMovingApex L a) ≤
        suzukiRectangularPositiveArchSampleChannel L a t ↔
      t = suzukiRectangularMovingApex L a := by
  constructor
  · intro hle
    by_contra hne
    exact (not_lt_of_ge hle)
      (suzukiRectangularPositiveArchSampleChannel_lt_movingApex
        hL hL2 ha hheight ht hne)
  · rintro rfl
    exact le_rfl

/-- Aperture which aligns the moving apex with the Mangoldt node `2 log n` at width `log 2`. -/
def suzukiMangoldtApexAperture (n : ℕ) : ℝ :=
  Real.log (2 * (n : ℝ)) / 2

/-- The aperture `log(2n)/2` locks the moving apex exactly to the source node `2 log n`. -/
theorem suzukiMangoldtApex_node_eq_apex
    {n : ℕ} (hn : 0 < n) :
    mangoldtLogHaarNode n =
      suzukiRectangularMovingApex (Real.log 2) (suzukiMangoldtApexAperture n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mangoldtLogHaarNode, suzukiRectangularMovingApex, suzukiMangoldtApexAperture,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR.ne']
  ring

/-- At every source index at least four, its node is the unique positive-lag maximizer of the
width-`log 2`, aperture-`log(2n)/2` Suzuki channel. -/
theorem suzukiMangoldtApex_unique_positiveLag_maximizer
    {n : ℕ} (hn : 4 ≤ n) {t : ℝ} (ht : 0 < t) :
    suzukiRectangularPositiveArchSampleChannel (Real.log 2)
        (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) ≤
        suzukiRectangularPositiveArchSampleChannel (Real.log 2)
          (suzukiMangoldtApexAperture n) t ↔
      t = mangoldtLogHaarNode n := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwoTwo : Real.log 2 < 2 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnR
  have hlogFour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hlogn : 2 * Real.log 2 ≤ Real.log (n : ℝ) := by
    rw [← hlogFour]
    exact Real.log_le_log (by norm_num) hnR
  have hlogMul : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log n :=
    Real.log_mul (by norm_num) hnPos.ne'
  have ha : 3 * Real.log 2 / 2 ≤ suzukiMangoldtApexAperture n := by
    rw [suzukiMangoldtApexAperture, hlogMul]
    linarith
  have hheight : Real.log 2 ≤ suzukiMangoldtApexAperture n - Real.log 2 / 2 := by
    rw [suzukiMangoldtApexAperture, hlogMul]
    linarith
  have hnode := suzukiMangoldtApex_node_eq_apex (show 0 < n by omega)
  rw [hnode]
  exact suzukiRectangularPositiveArchSampleChannel_apex_le_iff
    hlogTwo hlogTwoTwo ha hheight ht

/-- Any pointwise value-dominating target for a Mangoldt-aligned apex is Lebesgue null. -/
theorem volume_suzukiMangoldtApex_pointwiseDominatingSet_eq_zero
    {n : ℕ} (hn : 4 ≤ n) {S : Set ℝ}
    (hSpos : S ⊆ Set.Ioi 0)
    (hdom : ∀ t ∈ S,
      suzukiRectangularPositiveArchSampleChannel (Real.log 2)
          (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) ≤
        suzukiRectangularPositiveArchSampleChannel (Real.log 2)
          (suzukiMangoldtApexAperture n) t) :
    volume S = 0 := by
  apply measure_mono_null (t := {mangoldtLogHaarNode n})
  · intro t ht
    rw [Set.mem_singleton_iff]
    exact (suzukiMangoldtApex_unique_positiveLag_maximizer hn (hSpos ht)).mp (hdom t ht)
  · exact measure_singleton _

/-- A positive von-Mangoldt coefficient gives a strictly positive log-Haar atom. -/
theorem mangoldtLogHaarAtomMass_pos_of_vonMangoldt_pos
    {n : ℕ} (hn : 0 < n) (hΛ : 0 < ArithmeticFunction.vonMangoldt n) :
    0 < mangoldtLogHaarAtomMass n := by
  rw [mangoldtLogHaarAtomMass]
  positivity

/-- Exact no-go: a positive Mangoldt apex atom cannot be assigned a same-mass cell contained in
its pointwise value-dominating positive-lag superlevel. -/
theorem no_suzukiMangoldtApex_positiveVolume_pointwiseDominatingCell
    {n : ℕ} (hn : 4 ≤ n) (hΛ : 0 < ArithmeticFunction.vonMangoldt n) :
    ¬ ∃ S : Set ℝ,
      volume S = ENNReal.ofReal (mangoldtLogHaarAtomMass n) ∧
      S ⊆ Set.Ioi 0 ∧
      ∀ t ∈ S,
        suzukiRectangularPositiveArchSampleChannel (Real.log 2)
            (suzukiMangoldtApexAperture n) (mangoldtLogHaarNode n) ≤
          suzukiRectangularPositiveArchSampleChannel (Real.log 2)
            (suzukiMangoldtApexAperture n) t := by
  rintro ⟨S, hvolume, hSpos, hdom⟩
  have hzero := volume_suzukiMangoldtApex_pointwiseDominatingSet_eq_zero hn hSpos hdom
  have hmass : 0 < mangoldtLogHaarAtomMass n :=
    mangoldtLogHaarAtomMass_pos_of_vonMangoldt_pos (by omega) hΛ
  have hne : ENNReal.ofReal (mangoldtLogHaarAtomMass n) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hmass
  apply hne
  rw [← hvolume, hzero]

/-- Powers of two give a cofinal symbolic family of actual positive source atoms locked at unique
Suzuki apices. -/
theorem no_suzukiMangoldtApex_cell_at_two_pow
    {k : ℕ} (hk : 2 ≤ k) :
    ¬ ∃ S : Set ℝ,
      volume S = ENNReal.ofReal (mangoldtLogHaarAtomMass (2 ^ k)) ∧
      S ⊆ Set.Ioi 0 ∧
      ∀ t ∈ S,
        suzukiRectangularPositiveArchSampleChannel (Real.log 2)
            (suzukiMangoldtApexAperture (2 ^ k)) (mangoldtLogHaarNode (2 ^ k)) ≤
          suzukiRectangularPositiveArchSampleChannel (Real.log 2)
            (suzukiMangoldtApexAperture (2 ^ k)) t := by
  apply no_suzukiMangoldtApex_positiveVolume_pointwiseDominatingCell
  · simpa [show (4 : ℕ) = 2 ^ 2 by norm_num] using
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) hk)
  · rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact Real.log_pos (by norm_num)

end RHTower
