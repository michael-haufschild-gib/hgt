import GaloisForLFunctions.HTGeometry.TitchmarshCircleChain
import GaloisForLFunctions.RHTower.TitchmarshZetaInputs
import GaloisForLFunctions.U0.U0KummerBranch

noncomputable section

/-!
# Titchmarsh's shrinking zero-gap theorem for the Riemann zeta function

This is a formalization of Titchmarsh, *The Theory of the Riemann Zeta-function*, Theorem 9.12:
every sufficiently high ordinate `T` has a zeta zero within `A / log log log T`.

The proof is unconditional.  Assuming a zero-free horizontal strip, simply connectedness supplies
one global holomorphic branch of `log ζ`.  Borel--Carathéodory and Hadamard three-circles propagate
the bounded branch at `2+iT` to `-1/2+iT`.  The propagated upper bound contradicts the exact
functional-equation lower bound in `titchmarsh_terminal_zeta_lower`.
-/

open Complex Set Metric Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The open horizontal strip of half-width `h` about height `T`. -/
def titchmarshHorizontalStrip (T h : ℝ) : Set ℂ :=
  {z : ℂ | |z.im - T| < h}

theorem isOpen_titchmarshHorizontalStrip (T h : ℝ) :
    IsOpen (titchmarshHorizontalStrip T h) := by
  unfold titchmarshHorizontalStrip
  apply isOpen_lt
  · fun_prop
  · fun_prop

theorem convex_titchmarshHorizontalStrip (T h : ℝ) :
    Convex ℝ (titchmarshHorizontalStrip T h) := by
  have hlinim : IsLinearMap ℝ (fun z : ℂ => z.im) :=
    ⟨fun x y => by simp, fun c x => by simp⟩
  have hlower : Convex ℝ {z : ℂ | T - h < z.im} := convex_halfSpace_gt hlinim _
  have hupper : Convex ℝ {z : ℂ | z.im < T + h} := convex_halfSpace_lt hlinim _
  have hsplit : titchmarshHorizontalStrip T h =
      {z : ℂ | T - h < z.im} ∩ {z : ℂ | z.im < T + h} := by
    ext z
    simp only [titchmarshHorizontalStrip, mem_setOf_eq, mem_inter_iff, abs_lt]
    constructor <;> intro hz <;> constructor <;> linarith [hz.1, hz.2]
  rw [hsplit]
  exact hlower.inter hupper

/-- The centre of the `v`-th overlapping circle. -/
def titchmarshCircleCenter (T h : ℝ) (v : ℕ) : ℂ :=
  ((2 - (v : ℝ) * h / 8 : ℝ) : ℂ) + (T : ℂ) * I

@[simp] theorem titchmarshCircleCenter_re (T h : ℝ) (v : ℕ) :
    (titchmarshCircleCenter T h v).re = 2 - (v : ℝ) * h / 8 := by
  simp [titchmarshCircleCenter]

@[simp] theorem titchmarshCircleCenter_im (T h : ℝ) (v : ℕ) :
    (titchmarshCircleCenter T h v).im = T := by
  simp [titchmarshCircleCenter]

theorem titchmarshCircleCenter_succ_sub (T h : ℝ) (v : ℕ) :
    titchmarshCircleCenter T h (v + 1) - titchmarshCircleCenter T h v = -(h / 8 : ℝ) := by
  apply Complex.ext <;> simp [titchmarshCircleCenter]
  ring

/-- A zero-free horizontal strip has one holomorphic logarithm of `ζ`, normalized to the principal
logarithm at `2+iT`. -/
theorem exists_normalized_analyticLog_riemannZeta_on_horizontalStrip
    {T h : ℝ} (hh : 0 < h) (hT : h < T)
    (hzero : ∀ z ∈ titchmarshHorizontalStrip T h, riemannZeta z ≠ 0) :
    ∃ L : ℂ → ℂ,
      AnalyticOnNhd ℂ L (titchmarshHorizontalStrip T h) ∧
      (∀ z ∈ titchmarshHorizontalStrip T h, Complex.exp (L z) = riemannZeta z) ∧
      L (titchmarshCircleCenter T h 0) =
        Complex.log (riemannZeta (titchmarshCircleCenter T h 0)) := by
  let U := titchmarshHorizontalStrip T h
  have hUo : IsOpen U := isOpen_titchmarshHorizontalStrip T h
  have hcU : titchmarshCircleCenter T h 0 ∈ U := by
    dsimp only [U, titchmarshHorizontalStrip]
    simp [hh]
  have hUne : U.Nonempty := ⟨_, hcU⟩
  have hUsc : IsSimplyConnected U := by
    letI : ContractibleSpace U := (convex_titchmarshHorizontalStrip T h).contractibleSpace hUne
    exact SimplyConnectedSpace.ofContractible _
  have hne1 : ∀ z ∈ U, z ≠ 1 := by
    intro z hz hzone
    change |z.im - T| < h at hz
    have him : z.im = 0 := by rw [hzone]; simp
    have hT0 : 0 < T := hh.trans hT
    rw [him, zero_sub, abs_neg, abs_of_pos hT0] at hz
    linarith
  have hzetaDiff : DifferentiableOn ℂ riemannZeta U := by
    intro z hz
    exact (differentiableAt_riemannZeta (hne1 z hz)).differentiableWithinAt
  have hzetaAn : AnalyticOnNhd ℂ riemannZeta U := hzetaDiff.analyticOnNhd hUo
  have hzeroImage : (0 : ℂ) ∉ riemannZeta '' U := by
    rintro ⟨z, hz, hval⟩
    exact hzero z hz hval
  obtain ⟨L₀, hL₀cont, hL₀exp⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp hUsc hUo hzetaAn.continuousOn hzeroImage
  let c := titchmarshCircleCenter T h 0
  have hzc : riemannZeta c ≠ 0 := hzero c hcU
  let d : ℂ := Complex.log (riemannZeta c) - L₀ c
  have hdexp : Complex.exp d = 1 := by
    dsimp only [d]
    rw [Complex.exp_sub, Complex.exp_log hzc]
    have hbase : Complex.exp (L₀ c) = riemannZeta c := hL₀exp hcU
    rw [hbase, div_self hzc]
  let L : ℂ → ℂ := fun z => L₀ z + d
  have hLcont : ContinuousOn L U := hL₀cont.add continuousOn_const
  have hLexp : ∀ z ∈ U, Complex.exp (L z) = riemannZeta z := by
    intro z hz
    change Complex.exp (L₀ z + d) = riemannZeta z
    rw [Complex.exp_add, hdexp, mul_one]
    exact hL₀exp hz
  have hLan : AnalyticOnNhd ℂ L U :=
    U0KummerBranch.analyticOnNhd_of_continuousOn_exp_eq hUo hLcont hzetaAn hLexp
  refine ⟨L, hLan, hLexp, ?_⟩
  dsimp only [L, d, c]
  ring

/-- Logarithmic real-part cap used on every propagation circle. -/
def titchmarshLogCap (T : ℝ) : ℝ :=
  Real.log (20 * Real.exp 4 * (2 + T) ^ 2)

/-- Preliminary Borel--Carathéodory bound. -/
def titchmarshCrudeLogBound (A : ℝ) : ℕ → ℝ
  | 0 => 4 * A + 50
  | n + 1 => 4 * A + 5 * titchmarshCrudeLogBound A n

/-- Hadamard-refined bound after repeated square-root interpolation. -/
def titchmarshRefinedLogBound (A : ℝ) : ℕ → ℝ
  | 0 => 60 ^ (1 / 2 : ℝ) * (titchmarshCrudeLogBound A 0) ^ (1 / 2 : ℝ)
  | n + 1 =>
      (titchmarshRefinedLogBound A n) ^ (1 / 2 : ℝ) *
        (titchmarshCrudeLogBound A (n + 1)) ^ (1 / 2 : ℝ)

theorem titchmarshLogCap_pos {T : ℝ} (hT : 0 ≤ T) : 0 < titchmarshLogCap T := by
  apply Real.log_pos
  have he : 1 ≤ Real.exp 4 := Real.one_le_exp (by norm_num)
  have hs : 1 ≤ (2 + T) ^ 2 := by nlinarith [sq_nonneg (2 + T)]
  nlinarith

theorem titchmarshCrudeLogBound_pos {A : ℝ} (hA : 0 < A) :
    ∀ n, 0 < titchmarshCrudeLogBound A n := by
  intro n
  induction n with
  | zero => simp [titchmarshCrudeLogBound]; linarith
  | succ n hn => simp [titchmarshCrudeLogBound]; linarith

theorem titchmarshRefinedLogBound_pos {A : ℝ} (hA : 0 < A) :
    ∀ n, 0 < titchmarshRefinedLogBound A n := by
  intro n
  induction n with
  | zero =>
      simp only [titchmarshRefinedLogBound]
      exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
        (Real.rpow_pos_of_pos (titchmarshCrudeLogBound_pos hA 0) _)
  | succ n hn =>
      simp only [titchmarshRefinedLogBound]
      exact mul_pos (Real.rpow_pos_of_pos hn _)
        (Real.rpow_pos_of_pos (titchmarshCrudeLogBound_pos hA (n + 1)) _)

/-- Number of circle shifts needed to move the centre from `Re s = 2` to `Re s ≤ -1/2`. -/
def titchmarshCircleCount (h : ℝ) : ℕ := ⌈20 / h⌉₊

theorem titchmarshCircleCount_lower {h : ℝ} :
    20 / h ≤ (titchmarshCircleCount h : ℝ) := by
  exact Nat.le_ceil _

theorem titchmarshCircleCount_upper {h : ℝ} (hh : 0 < h) :
    (titchmarshCircleCount h : ℝ) < 20 / h + 1 := by
  exact Nat.ceil_lt_add_one (by positivity)

theorem titchmarsh_final_center_re_le {h : ℝ} (hh : 0 < h) :
    (titchmarshCircleCenter 0 h (titchmarshCircleCount h)).re ≤ -1 / 2 := by
  rw [titchmarshCircleCenter_re]
  have hn := titchmarshCircleCount_lower (h := h)
  have h20 : 20 ≤ (titchmarshCircleCount h : ℝ) * h := by
    calc
      20 = (20 / h) * h := by field_simp
      _ ≤ (titchmarshCircleCount h : ℝ) * h := mul_le_mul_of_nonneg_right hn hh.le
  linarith

theorem titchmarsh_final_center_re_gt {h : ℝ} (hh : 0 < h) :
    -1 / 2 - h / 8 <
      (titchmarshCircleCenter 0 h (titchmarshCircleCount h)).re := by
  rw [titchmarshCircleCenter_re]
  have hn := titchmarshCircleCount_upper hh
  have hmul : (titchmarshCircleCount h : ℝ) * h < 20 + h := by
    calc
      (titchmarshCircleCount h : ℝ) * h < (20 / h + 1) * h :=
        mul_lt_mul_of_pos_right hn hh
      _ = 20 + h := by field_simp
  nlinarith

theorem titchmarsh_circle_ball_subset_horizontalStrip
    {T h : ℝ} (hh : 0 < h) (v : ℕ) :
    ball (titchmarshCircleCenter T h v) (3 * h / 4) ⊆
      titchmarshHorizontalStrip T h := by
  intro z hz
  rw [mem_ball_iff_norm] at hz
  have him := Complex.abs_im_le_norm (z - titchmarshCircleCenter T h v)
  have himeq : (z - titchmarshCircleCenter T h v).im = z.im - T := by simp
  rw [himeq] at him
  exact lt_of_le_of_lt him (lt_of_lt_of_le hz (by linarith))

/-- Uniform real and imaginary bounds on every circle used before the terminal index. -/
theorem titchmarsh_circle_ball_geometry
    {T h : ℝ} (hh : 0 < h) (hhsmall : h ≤ 1 / 2) (hT : 3 ≤ T)
    {v : ℕ} (hv : v ≤ titchmarshCircleCount h)
    {z : ℂ} (hz : z ∈ ball (titchmarshCircleCenter T h v) (3 * h / 4)) :
    -1 ≤ z.re ∧ z.re ≤ 5 / 2 ∧ 2 ≤ |z.im| := by
  rw [mem_ball_iff_norm] at hz
  have hre := Complex.abs_re_le_norm (z - titchmarshCircleCenter T h v)
  have him := Complex.abs_im_le_norm (z - titchmarshCircleCenter T h v)
  have hcre : (titchmarshCircleCenter T h v).re = 2 - (v : ℝ) * h / 8 := by simp
  have hcim : (titchmarshCircleCenter T h v).im = T := by simp
  rw [Complex.sub_re, hcre] at hre
  rw [Complex.sub_im, hcim] at him
  have hvcast : (v : ℝ) ≤ titchmarshCircleCount h := by exact_mod_cast hv
  have hn := titchmarshCircleCount_upper hh
  have hvupper : (v : ℝ) < 20 / h + 1 := hvcast.trans_lt hn
  have hvmul : (v : ℝ) * h < 20 + h := by
    calc
      (v : ℝ) * h < (20 / h + 1) * h := mul_lt_mul_of_pos_right hvupper hh
      _ = 20 + h := by field_simp
  have hcenterLower : -1 / 2 - h / 8 < 2 - (v : ℝ) * h / 8 := by nlinarith
  have hcenterUpper : 2 - (v : ℝ) * h / 8 ≤ 2 := by
    have hvh : 0 ≤ (v : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
    linarith
  have hzreLower : -1 ≤ z.re := by
    have := (abs_lt.mp (hre.trans_lt hz)).1
    nlinarith
  have hzreUpper : z.re ≤ 5 / 2 := by
    have := (abs_lt.mp (hre.trans_lt hz)).2
    nlinarith
  have hzim : 2 ≤ z.im := by
    have := (abs_lt.mp (him.trans_lt hz)).1
    nlinarith
  exact ⟨hzreLower, hzreUpper, hzim.trans (le_abs_self _)⟩

/-- The real part of any normalized analytic logarithm is capped by `titchmarshLogCap` on every
propagation ball. -/
theorem analyticLog_riemannZeta_re_le_titchmarshLogCap
    {T h : ℝ} (hh : 0 < h) (hhsmall : h ≤ 1 / 2) (hT : 3 ≤ T)
    {L : ℂ → ℂ}
    (hLexp : ∀ z ∈ titchmarshHorizontalStrip T h,
      Complex.exp (L z) = riemannZeta z)
    {v : ℕ} (hv : v ≤ titchmarshCircleCount h)
    {z : ℂ} (hz : z ∈ ball (titchmarshCircleCenter T h v) (3 * h / 4)) :
    (L z).re ≤ titchmarshLogCap T := by
  have hzstrip := titchmarsh_circle_ball_subset_horizontalStrip hh v hz
  obtain ⟨hzreLow, hzreHigh, hzimLow⟩ :=
    titchmarsh_circle_ball_geometry hh hhsmall hT hv hz
  have hzeta := norm_riemannZeta_le_titchmarsh_strip hzreLow hzreHigh hzimLow
  have him := Complex.abs_im_le_norm (z - titchmarshCircleCenter T h v)
  have himeq : (z - titchmarshCircleCenter T h v).im = z.im - T := by simp
  rw [himeq] at him
  have hdist : ‖z - titchmarshCircleCenter T h v‖ < 3 * h / 4 := by
    rw [mem_ball_iff_norm] at hz
    exact hz
  have himabs : |z.im - T| < 3 * h / 4 := him.trans_lt hdist
  have hzimPos : 0 < z.im := by
    have := (abs_lt.mp himabs).1
    nlinarith
  have hzimUpper : |z.im| ≤ T + 1 := by
    rw [abs_of_pos hzimPos]
    have := (abs_lt.mp himabs).2
    linarith
  have hfactor : 1 + |z.im| ≤ 2 + T := by linarith
  have hfactor0 : 0 ≤ 1 + |z.im| := by positivity
  have hfactorT0 : 0 ≤ 2 + T := by linarith
  have hzeta' : ‖riemannZeta z‖ ≤ 20 * Real.exp 4 * (2 + T) ^ 2 := by
    have hrepr : ((z.re : ℂ) + (z.im : ℂ) * I) = z := by
      apply Complex.ext <;> simp
    rw [hrepr] at hzeta
    calc
      ‖riemannZeta z‖ ≤ 20 * Real.exp 4 * (1 + |z.im|) ^ 2 := hzeta
      _ ≤ 20 * Real.exp 4 * (2 + T) ^ 2 := by
        gcongr
  have hexpnorm : Real.exp (L z).re = ‖riemannZeta z‖ := by
    rw [← hLexp z hzstrip, Complex.norm_exp]
  rw [titchmarshLogCap, ← Real.log_exp (L z).re]
  rw [hexpnorm]
  exact Real.log_le_log (by rw [← hexpnorm]; positivity) hzeta'

/-- The first inner circle stays in the absolutely convergent half-plane, so the normalized branch
has an absolute bound independent of both `T` and the strip width. -/
theorem analyticLog_riemannZeta_base_inner_le_sixty
    {T h : ℝ} (hh : 0 < h) (hhsmall : h ≤ 1 / 2) (_hT : 3 ≤ T)
    {L : ℂ → ℂ}
    (hLan : AnalyticOnNhd ℂ L (titchmarshHorizontalStrip T h))
    (hLexp : ∀ z ∈ titchmarshHorizontalStrip T h,
      Complex.exp (L z) = riemannZeta z)
    (hLc : L (titchmarshCircleCenter T h 0) =
      Complex.log (riemannZeta (titchmarshCircleCenter T h 0))) :
    ∀ z : ℂ, ‖z - titchmarshCircleCenter T h 0‖ = h / 8 → ‖L z‖ ≤ 60 := by
  let c := titchmarshCircleCenter T h 0
  have hc : ‖L c‖ ≤ 10 := by
    rw [hLc]
    simpa [c, titchmarshCircleCenter] using norm_log_riemannZeta_two_add_I_mul_le_ten T
  have hsmall : 0 < h / 4 := by positivity
  have hballSub : ball c (3 * (h / 4) / 4) ⊆ titchmarshHorizontalStrip T h := by
    intro z hz
    apply titchmarsh_circle_ball_subset_horizontalStrip hh 0
    rw [mem_ball_iff_norm] at hz ⊢
    linarith
  have hLdiff : DifferentiableOn ℂ L (ball c (3 * (h / 4) / 4)) := by
    intro z hz
    exact ((hLan z (hballSub hz)).differentiableAt).differentiableWithinAt
  have hre : ∀ z ∈ ball c (3 * (h / 4) / 4), (L z).re ≤ 2 := by
    intro z hz
    have hzstrip := hballSub hz
    have hdist : ‖z - c‖ < 3 * (h / 4) / 4 := by
      rw [mem_ball_iff_norm] at hz
      exact hz
    have hreal := Complex.abs_re_le_norm (z - c)
    have hcre : c.re = 2 := by simp [c]
    rw [Complex.sub_re, hcre] at hreal
    have hzre : 3 / 2 < z.re := by
      have := (abs_lt.mp (hreal.trans_lt hdist)).1
      nlinarith
    have hzeta := Sieve.norm_riemannZeta_le (s := z) (by linarith)
    have hden : 1 / 2 < z.re - 1 := by linarith
    have hden0 : 0 < z.re - 1 := by linarith
    have hinv : 1 / (z.re - 1) < 2 := by
      rw [div_lt_iff₀ hden0]
      nlinarith
    have hzetaThree : ‖riemannZeta z‖ ≤ 3 := hzeta.trans (by linarith)
    have hexpnorm : Real.exp (L z).re = ‖riemannZeta z‖ := by
      rw [← hLexp z hzstrip, Complex.norm_exp]
    rw [← Real.log_exp (L z).re, hexpnorm]
    have hlog := Real.log_le_log (by rw [← hexpnorm]; positivity) hzetaThree
    have hlogThree : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      norm_num at this ⊢
      exact this
    exact hlog.trans hlogThree
  intro z hz
  change ‖z - c‖ = h / 8 at hz
  have htarget : ‖z - c‖ ≤ (h / 4) / 2 := by
    rw [hz]
    ring_nf
    exact le_rfl
  have hmain := norm_le_titchmarsh_borel (g := L) (c := c) (A := 2) (h := h / 4)
    (by norm_num) hsmall hLdiff hre hc (z := z) htarget
  norm_num at hmain ⊢
  linarith

/-- A zero-free strip forces the terminal logarithm below the finite Hadamard recursion. -/
theorem exists_analyticLog_terminal_le_refined_of_zeroFree
    {T h : ℝ} (hh : 0 < h) (hhsmall : h ≤ 1 / 2) (hT : 3 ≤ T)
    (hzero : ∀ z ∈ titchmarshHorizontalStrip T h, riemannZeta z ≠ 0) :
    ∃ L : ℂ → ℂ,
      AnalyticOnNhd ℂ L (titchmarshHorizontalStrip T h) ∧
      (∀ z ∈ titchmarshHorizontalStrip T h, Complex.exp (L z) = riemannZeta z) ∧
      ‖L (smoothAFEZetaLeftLinePt T)‖ ≤
        titchmarshRefinedLogBound (titchmarshLogCap T) (titchmarshCircleCount h) := by
  obtain ⟨L, hLan, hLexp, hLc⟩ :=
    exists_normalized_analyticLog_riemannZeta_on_horizontalStrip hh (by linarith) hzero
  let A := titchmarshLogCap T
  let n := titchmarshCircleCount h
  have hA : 0 < A := titchmarshLogCap_pos (by linarith)
  have hdiff : ∀ v : ℕ, v ≤ n →
      DifferentiableOn ℂ L (ball (titchmarshCircleCenter T h v) (3 * h / 4)) := by
    intro v hv z hz
    have hzstrip := titchmarsh_circle_ball_subset_horizontalStrip hh v hz
    exact ((hLan z hzstrip).differentiableAt).differentiableWithinAt
  have hre : ∀ v : ℕ, v ≤ n →
      ∀ z ∈ ball (titchmarshCircleCenter T h v) (3 * h / 4), (L z).re ≤ A := by
    intro v hv z hz
    exact analyticLog_riemannZeta_re_le_titchmarshLogCap hh hhsmall hT hLexp hv hz
  have hc0 : ‖L (titchmarshCircleCenter T h 0)‖ ≤ 10 := by
    rw [hLc]
    simpa [titchmarshCircleCenter] using norm_log_riemannZeta_two_add_I_mul_le_ten T
  have hcenterSuccMem : ∀ v : ℕ,
      titchmarshCircleCenter T h (v + 1) ∈
        closedBall (titchmarshCircleCenter T h v) (h / 2) := by
    intro v
    rw [mem_closedBall_iff_norm, titchmarshCircleCenter_succ_sub]
    simp [abs_of_pos hh]
    linarith
  have hinnerSuccMem : ∀ v : ℕ, ∀ z : ℂ,
      ‖z - titchmarshCircleCenter T h (v + 1)‖ = h / 8 →
        z ∈ closedBall (titchmarshCircleCenter T h v) (h / 4) := by
    intro v z hz
    rw [mem_closedBall_iff_norm]
    have hsplit : z - titchmarshCircleCenter T h v =
        (z - titchmarshCircleCenter T h (v + 1)) +
          (titchmarshCircleCenter T h (v + 1) - titchmarshCircleCenter T h v) := by ring
    rw [hsplit]
    calc
      ‖(z - titchmarshCircleCenter T h (v + 1)) +
          (titchmarshCircleCenter T h (v + 1) - titchmarshCircleCenter T h v)‖
          ≤ ‖z - titchmarshCircleCenter T h (v + 1)‖ +
            ‖titchmarshCircleCenter T h (v + 1) - titchmarshCircleCenter T h v‖ :=
        norm_add_le _ _
      _ = h / 8 + h / 8 := by
        rw [hz, titchmarshCircleCenter_succ_sub]
        simp [abs_of_pos hh]
      _ = h / 4 := by ring
  have hcrude : ∀ v : ℕ, v ≤ n →
      ∀ z ∈ closedBall (titchmarshCircleCenter T h v) (h / 2),
        ‖L z‖ ≤ titchmarshCrudeLogBound A v := by
    intro v
    induction v with
    | zero =>
        intro _ z hz
        rw [mem_closedBall_iff_norm] at hz
        have hmain := norm_le_titchmarsh_borel hA hh (hdiff 0 (Nat.zero_le _))
          (hre 0 (Nat.zero_le _)) hc0 hz
        norm_num at hmain
        simpa [titchmarshCrudeLogBound] using hmain
    | succ v ih =>
        intro hvn z hz
        have hvn' : v ≤ n := (Nat.le_succ v).trans hvn
        have hc := ih hvn' _ (hcenterSuccMem v)
        rw [mem_closedBall_iff_norm] at hz
        have hmain := norm_le_titchmarsh_borel hA hh (hdiff (v + 1) hvn)
          (hre (v + 1) hvn) hc hz
        simpa [titchmarshCrudeLogBound] using hmain
  have hbaseInner : ∀ z : ℂ,
      ‖z - titchmarshCircleCenter T h 0‖ = h / 8 → ‖L z‖ ≤ 60 :=
    analyticLog_riemannZeta_base_inner_le_sixty hh hhsmall hT hLan hLexp hLc
  have hrefined : ∀ v : ℕ, v ≤ n →
      ∀ z ∈ closedBall (titchmarshCircleCenter T h v) (h / 4),
        ‖L z‖ ≤ titchmarshRefinedLogBound A v := by
    intro v
    induction v with
    | zero =>
        intro _
        have hmain := norm_le_titchmarsh_circle_step_closedBall hA hh
          (hdiff 0 (Nat.zero_le _)) (hre 0 (Nat.zero_le _)) hc0 hbaseInner
        norm_num at hmain
        simpa [titchmarshRefinedLogBound, titchmarshCrudeLogBound] using hmain
    | succ v ih =>
        intro hvn
        have hvn' : v ≤ n := (Nat.le_succ v).trans hvn
        have hc : ‖L (titchmarshCircleCenter T h (v + 1))‖ ≤
            titchmarshCrudeLogBound A v :=
          hcrude v hvn' _ (hcenterSuccMem v)
        have hinner : ∀ z : ℂ,
            ‖z - titchmarshCircleCenter T h (v + 1)‖ = h / 8 →
              ‖L z‖ ≤ titchmarshRefinedLogBound A v := by
          intro z hz
          exact ih hvn' z (hinnerSuccMem v z hz)
        have hmain := norm_le_titchmarsh_circle_step_closedBall hA hh
          (hdiff (v + 1) hvn) (hre (v + 1) hvn) hc hinner
        simpa [titchmarshRefinedLogBound, titchmarshCrudeLogBound] using hmain
  have hterminalMem : smoothAFEZetaLeftLinePt T ∈
      closedBall (titchmarshCircleCenter T h n) (h / 4) := by
    rw [mem_closedBall_iff_norm]
    have hcle : (titchmarshCircleCenter T h n).re ≤ -1 / 2 := by
      dsimp only [n]
      simpa using titchmarsh_final_center_re_le hh
    have hcgt : -1 / 2 - h / 8 < (titchmarshCircleCenter T h n).re := by
      dsimp only [n]
      simpa using titchmarsh_final_center_re_gt hh
    have hdiffpoint : smoothAFEZetaLeftLinePt T - titchmarshCircleCenter T h n =
        (((-1 / 2 - (titchmarshCircleCenter T h n).re : ℝ)) : ℂ) := by
      apply Complex.ext
      · simp [smoothAFEZetaLeftLinePt]
      · simp [smoothAFEZetaLeftLinePt]
    rw [hdiffpoint, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ -1 / 2 - (titchmarshCircleCenter T h n).re)]
    linarith
  refine ⟨L, hLan, hLexp, ?_⟩
  exact hrefined n le_rfl _ hterminalMem

/-- Elementary majorant for the preliminary Borel--Carathéodory recursion. -/
def titchmarshCrudeMajorant (A : ℝ) (n : ℕ) : ℝ :=
  6 ^ (n + 1) * (A + 10)

/-- Weight of the initial circle after `n` repeated geometric-mean improvements. -/
def titchmarshRefinedWeight (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (n + 1)

theorem titchmarshCrudeLogBound_le_majorant {A : ℝ} (hA : 0 ≤ A) :
    ∀ n : ℕ, titchmarshCrudeLogBound A n ≤ titchmarshCrudeMajorant A n := by
  intro n
  induction n with
  | zero =>
      simp [titchmarshCrudeLogBound, titchmarshCrudeMajorant]
      linarith
  | succ n hn =>
      have hp : (1 : ℝ) ≤ 6 ^ (n + 1) := one_le_pow₀ (by norm_num)
      have hp6 : (6 : ℝ) ≤ 6 ^ (n + 1) := by
        rw [pow_succ]
        have := one_le_pow₀ (n := n) (by norm_num : (1 : ℝ) ≤ 6)
        nlinarith
      have hAten : 0 ≤ A + 10 := by linarith
      have hAge : 4 * A ≤ titchmarshCrudeMajorant A n := by
        calc
          4 * A ≤ 6 * (A + 10) := by linarith
          _ ≤ 6 ^ (n + 1) * (A + 10) :=
            mul_le_mul_of_nonneg_right hp6 hAten
          _ = titchmarshCrudeMajorant A n := rfl
      rw [titchmarshCrudeLogBound]
      calc
        4 * A + 5 * titchmarshCrudeLogBound A n
            ≤ 4 * A + 5 * titchmarshCrudeMajorant A n := by linarith
        _ ≤ 6 * titchmarshCrudeMajorant A n := by linarith
        _ = titchmarshCrudeMajorant A (n + 1) := by
          simp [titchmarshCrudeMajorant, pow_succ]
          ring

theorem titchmarshCrudeMajorant_pos {A : ℝ} (hA : 0 ≤ A) (n : ℕ) :
    0 < titchmarshCrudeMajorant A n := by
  unfold titchmarshCrudeMajorant
  positivity

theorem titchmarshCrudeMajorant_mono {A : ℝ} (hA : 0 ≤ A) (n : ℕ) :
    titchmarshCrudeMajorant A n ≤ titchmarshCrudeMajorant A (n + 1) := by
  have hpos := titchmarshCrudeMajorant_pos hA n
  have heq : titchmarshCrudeMajorant A (n + 1) =
      6 * titchmarshCrudeMajorant A n := by
    simp [titchmarshCrudeMajorant, pow_succ]
    ring
  rw [heq]
  linarith

@[simp] theorem titchmarshRefinedWeight_zero : titchmarshRefinedWeight 0 = 1 / 2 := by
  norm_num [titchmarshRefinedWeight]

theorem titchmarshRefinedWeight_succ (n : ℕ) :
    titchmarshRefinedWeight (n + 1) = titchmarshRefinedWeight n / 2 := by
  simp [titchmarshRefinedWeight, pow_succ]
  ring

theorem titchmarshRefinedWeight_nonneg (n : ℕ) :
    0 ≤ titchmarshRefinedWeight n := by
  unfold titchmarshRefinedWeight
  positivity

theorem titchmarshRefinedWeight_le_one (n : ℕ) :
    titchmarshRefinedWeight n ≤ 1 := by
  unfold titchmarshRefinedWeight
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- Logarithmic solution of the repeated Hadamard geometric-mean recursion. -/
theorem log_titchmarshRefinedLogBound_le
    {A : ℝ} (hA : 0 < A) (n : ℕ) :
    Real.log (titchmarshRefinedLogBound A n) ≤
      titchmarshRefinedWeight n * Real.log 60 +
        (1 - titchmarshRefinedWeight n) *
          Real.log (titchmarshCrudeMajorant A n) := by
  have hA0 : 0 ≤ A := hA.le
  induction n with
  | zero =>
      have hD : 0 < titchmarshCrudeLogBound A 0 :=
        titchmarshCrudeLogBound_pos hA 0
      have hB : 0 < titchmarshCrudeMajorant A 0 :=
        titchmarshCrudeMajorant_pos hA0 0
      have hDB : titchmarshCrudeLogBound A 0 ≤ titchmarshCrudeMajorant A 0 :=
        titchmarshCrudeLogBound_le_majorant hA0 0
      rw [titchmarshRefinedLogBound,
        Real.log_mul (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 60) _).ne'
          (Real.rpow_pos_of_pos hD _).ne',
        Real.log_rpow (by norm_num : (0 : ℝ) < 60), Real.log_rpow hD]
      rw [titchmarshRefinedWeight_zero]
      have hlogDB : Real.log (titchmarshCrudeLogBound A 0) ≤
          Real.log (titchmarshCrudeMajorant A 0) := Real.log_le_log hD hDB
      norm_num
      linarith
  | succ n ih =>
      have hK : 0 < titchmarshRefinedLogBound A n :=
        titchmarshRefinedLogBound_pos hA n
      have hD : 0 < titchmarshCrudeLogBound A (n + 1) :=
        titchmarshCrudeLogBound_pos hA (n + 1)
      have hB : 0 < titchmarshCrudeMajorant A (n + 1) :=
        titchmarshCrudeMajorant_pos hA0 (n + 1)
      have hDB : titchmarshCrudeLogBound A (n + 1) ≤
          titchmarshCrudeMajorant A (n + 1) :=
        titchmarshCrudeLogBound_le_majorant hA0 (n + 1)
      have hBB : titchmarshCrudeMajorant A n ≤
          titchmarshCrudeMajorant A (n + 1) :=
        titchmarshCrudeMajorant_mono hA0 n
      have hlogDB : Real.log (titchmarshCrudeLogBound A (n + 1)) ≤
          Real.log (titchmarshCrudeMajorant A (n + 1)) := Real.log_le_log hD hDB
      have hlogBB : Real.log (titchmarshCrudeMajorant A n) ≤
          Real.log (titchmarshCrudeMajorant A (n + 1)) :=
        Real.log_le_log (titchmarshCrudeMajorant_pos hA0 n) hBB
      rw [titchmarshRefinedLogBound,
        Real.log_mul (Real.rpow_pos_of_pos hK _).ne'
          (Real.rpow_pos_of_pos hD _).ne',
        Real.log_rpow hK, Real.log_rpow hD,
        titchmarshRefinedWeight_succ]
      have hq0 := titchmarshRefinedWeight_nonneg n
      have hq1 := titchmarshRefinedWeight_le_one n
      norm_num
      nlinarith

/-- At the terminal point the functional equation forces every logarithm of zeta to have size at
least one half of `log T`.  The explicit threshold only absorbs the harmless Archimedean constants
in `titchmarsh_terminal_zeta_lower`. -/
theorem half_log_le_norm_analyticLog_terminal
    {T : ℝ} (hT : 25000000 ≤ T) {L : ℂ → ℂ}
    (hLexp : Complex.exp (L (smoothAFEZetaLeftLinePt T)) =
      riemannZeta (smoothAFEZetaLeftLinePt T)) :
    (1 / 2 : ℝ) * Real.log T ≤ ‖L (smoothAFEZetaLeftLinePt T)‖ := by
  let s := smoothAFEZetaLeftLinePt T
  have hTpos : 0 < T := by linarith
  have hTabs : |T| = T := abs_of_pos hTpos
  have hterminal := titchmarsh_terminal_zeta_lower (t := T) (by rw [hTabs]; linarith)
  rw [hTabs] at hterminal
  have hsNorm : T ≤ ‖s‖ := by
    have him := Complex.abs_im_le_norm s
    simpa [s, hTabs] using him
  have hpi : 2 * Real.pi ≤ 8 := by
    linarith [Real.pi_lt_four]
  have hratio : T / 8 ≤ ‖s‖ / (2 * Real.pi) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8)
      (mul_pos (by norm_num) Real.pi_pos)).2
    calc
      T * (2 * Real.pi) ≤ T * 8 := mul_le_mul_of_nonneg_left hpi hTpos.le
      _ ≤ ‖s‖ * 8 := mul_le_mul_of_nonneg_right hsNorm (by norm_num)
  have hratioPow : (T / 8) ^ 4 ≤ (‖s‖ / (2 * Real.pi)) ^ 4 := by
    gcongr
  have hlogpos : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogle : Real.log T ≤ T := by
    have := Real.log_le_sub_one_of_pos hTpos
    linarith
  have hsecond : 1 / (6048 * T) ≤
      (1 / 2 : ℝ) ^ 3 / (756 * Real.log T) := by
    have hinv : 1 / T ≤ 1 / Real.log T := one_div_le_one_div_of_le hlogpos hlogle
    calc
      1 / (6048 * T) = (1 / 6048 : ℝ) * (1 / T) := by field_simp
      _ ≤ (1 / 6048 : ℝ) * (1 / Real.log T) := by gcongr
      _ = (1 / 2 : ℝ) ^ 3 / (756 * Real.log T) := by
        field_simp
        norm_num
  have hsimple : T ^ 2 ≤ (T / 8) ^ 4 * (1 / (6048 * T)) := by
    have hconst : (24772608 : ℝ) ≤ T := by linarith
    field_simp
    nlinarith [sq_nonneg T]
  have hproduct : (T / 8) ^ 4 * (1 / (6048 * T)) ≤
      (‖s‖ / (2 * Real.pi)) ^ 4 *
        ((1 / 2 : ℝ) ^ 3 / (756 * Real.log T)) := by
    exact mul_le_mul hratioPow hsecond (by positivity) (by positivity)
  have hzetaLower : T ^ 2 ≤ ‖riemannZeta s‖ ^ 4 := by
    calc
      T ^ 2 ≤ (T / 8) ^ 4 * (1 / (6048 * T)) := hsimple
      _ ≤ (‖s‖ / (2 * Real.pi)) ^ 4 *
          ((1 / 2 : ℝ) ^ 3 / (756 * Real.log T)) := hproduct
      _ ≤ ‖riemannZeta s‖ ^ 4 := by simpa [s] using hterminal
  have hexpNorm : ‖riemannZeta s‖ = Real.exp (L s).re := by
    rw [← hLexp]
    exact Complex.norm_exp _
  have hzetaUpper : ‖riemannZeta s‖ ≤ Real.exp ‖L s‖ := by
    rw [hexpNorm]
    exact Real.exp_le_exp.mpr (Complex.re_le_norm _)
  have hpowUpper : ‖riemannZeta s‖ ^ 4 ≤ (Real.exp ‖L s‖) ^ 4 := by
    gcongr
  have hcombined : T ^ 2 ≤ Real.exp (4 * ‖L s‖) := by
    calc
      T ^ 2 ≤ ‖riemannZeta s‖ ^ 4 := hzetaLower
      _ ≤ (Real.exp ‖L s‖) ^ 4 := hpowUpper
      _ = Real.exp (4 * ‖L s‖) := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hlog := Real.log_le_log (sq_pos_of_pos hTpos) hcombined
  rw [Real.log_pow, Real.log_exp] at hlog
  norm_num at hlog
  simpa [s] using (show (1 / 2 : ℝ) * Real.log T ≤ ‖L s‖ by linarith)

/-- A circle count below `log x / 50` leaves a polynomially large fraction of the initial
Hadamard weight. -/
theorem titchmarshRefinedWeight_lower_of_count
    {x : ℝ} (hx : 1 ≤ x) {n : ℕ}
    (hn : (n : ℝ) < Real.log x / 50 + 1) :
    Real.exp (-2) * x ^ (-1 / 50 : ℝ) ≤ titchmarshRefinedWeight n := by
  have hxpos : 0 < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hn' : ((n + 1 : ℕ) : ℝ) ≤ Real.log x / 50 + 2 := by
    norm_num
    linarith
  have hpow : (1 / 2 : ℝ) ^ (Real.log x / 50 + 2) ≤
      (1 / 2 : ℝ) ^ ((n + 1 : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hn'
  rw [Real.rpow_natCast] at hpow
  have hlogtwo : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hloghalf : -1 ≤ Real.log (1 / 2 : ℝ) := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    linarith
  have hu : 0 ≤ Real.log x / 50 + 2 := by positivity
  have hbase : Real.exp (-(Real.log x / 50 + 2)) ≤
      (1 / 2 : ℝ) ^ (Real.log x / 50 + 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hloghalf hu
    linarith
  have heq : Real.exp (-(Real.log x / 50 + 2)) =
      Real.exp (-2) * x ^ (-1 / 50 : ℝ) := by
    rw [Real.rpow_def_of_pos hxpos, ← Real.exp_add]
    congr 1
    ring
  rw [← heq]
  exact hbase.trans hpow

/-- The surviving Hadamard weight eventually beats every logarithmic loss in the circle chain. -/
theorem eventually_titchmarshRefinedWeight_mul_sub_gt :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ,
      (n : ℝ) < Real.log x / 50 + 1 →
        Real.log x + 100 < titchmarshRefinedWeight n * (x - 100) := by
  let c : ℝ := Real.exp (-2) / 8
  have hc : 0 < c := by dsimp only [c]; positivity
  have hr : (0 : ℝ) < 49 / 50 := by norm_num
  have hlog : ∀ᶠ x : ℝ in atTop, Real.log x ≤ c * x ^ (49 / 50 : ℝ) := by
    have hlo := (isLittleO_log_rpow_atTop hr).def hc
    filter_upwards [hlo, eventually_ge_atTop (1 : ℝ)] with x hxlog hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hx),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hxlog
    exact hxlog
  have hconst : ∀ᶠ x : ℝ in atTop, 100 < c * x ^ (49 / 50 : ℝ) := by
    have ht : Tendsto (fun x : ℝ => c * x ^ (49 / 50 : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hc (tendsto_rpow_atTop hr)
    exact ht.eventually_gt_atTop 100
  filter_upwards [hlog, hconst, eventually_ge_atTop (200 : ℝ)] with x hxlog hxconst hx n hn
  have hxone : 1 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hq := titchmarshRefinedWeight_lower_of_count hxone hn
  have hq0 := titchmarshRefinedWeight_nonneg n
  have hxsub : x / 2 ≤ x - 100 := by linarith
  have hpowSplit : x ^ (-1 / 50 : ℝ) * x = x ^ (49 / 50 : ℝ) := by
    nth_rewrite 2 [← Real.rpow_one x]
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  have hlower : Real.exp (-2) / 2 * x ^ (49 / 50 : ℝ) ≤
      titchmarshRefinedWeight n * (x - 100) := by
    calc
      Real.exp (-2) / 2 * x ^ (49 / 50 : ℝ) =
          (Real.exp (-2) * x ^ (-1 / 50 : ℝ)) * (x / 2) := by
            rw [show (Real.exp (-2) * x ^ (-1 / 50 : ℝ)) * (x / 2) =
              Real.exp (-2) / 2 * (x ^ (-1 / 50 : ℝ) * x) by ring,
              hpowSplit]
      _ ≤ titchmarshRefinedWeight n * (x / 2) := by gcongr
      _ ≤ titchmarshRefinedWeight n * (x - 100) := by gcongr
  have hupper : Real.log x + 100 <
      Real.exp (-2) / 2 * x ^ (49 / 50 : ℝ) := by
    dsimp only [c] at hxlog hxconst
    nlinarith [Real.rpow_nonneg hxpos.le (49 / 50 : ℝ), Real.exp_pos (-2)]
  exact hupper.trans_le hlower

theorem titchmarshLogCap_add_ten_le_six_log
    {T : ℝ} (hT : 2 ≤ T) (hlogT : 10 ≤ Real.log T) :
    titchmarshLogCap T + 10 ≤ 6 * Real.log T := by
  have hTpos : 0 < T := by linarith
  have hTtwoPos : 0 < 2 + T := by linarith
  have htwoTpos : 0 < 2 * T := by positivity
  have hTtwo : 2 + T ≤ 2 * T := by linarith
  have hlogTtwo : Real.log (2 + T) ≤ Real.log (2 * T) :=
    Real.log_le_log hTtwoPos hTtwo
  have hlogtwo : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hlogtwenty : Real.log 20 ≤ 19 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 20)
    norm_num at this ⊢
    exact this
  have hcap : titchmarshLogCap T =
      Real.log 20 + 4 + 2 * Real.log (2 + T) := by
    rw [titchmarshLogCap,
      Real.log_mul (mul_ne_zero (by norm_num) (Real.exp_ne_zero 4))
        (pow_ne_zero 2 hTtwoPos.ne'),
      Real.log_mul (by norm_num : (20 : ℝ) ≠ 0) (Real.exp_ne_zero 4),
      Real.log_exp, Real.log_pow]
    norm_num
  have hsplit : Real.log (2 * T) = Real.log 2 + Real.log T := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hTpos.ne']
  rw [hsplit] at hlogTtwo
  rw [hcap]
  linarith

/-- The crude majorant has logarithm `log log T + O(log log log T)` at the Titchmarsh circle
count.  Both sides are kept explicit for the final contradiction. -/
theorem log_titchmarshCrudeMajorant_bounds
    {T : ℝ} (hT : 2 ≤ T) (hlogT : 10 ≤ Real.log T)
    {n : ℕ} (hn : (n : ℝ) < Real.log (Real.log (Real.log T)) / 50 + 1)
    (htriple : 0 ≤ Real.log (Real.log (Real.log T))) :
    Real.log (Real.log T) ≤
        Real.log (titchmarshCrudeMajorant (titchmarshLogCap T) n) ∧
      Real.log (titchmarshCrudeMajorant (titchmarshLogCap T) n) ≤
        Real.log (Real.log T) + Real.log (Real.log (Real.log T)) + 20 := by
  have hTpos : 0 < T := by linarith
  have hlogTpos : 0 < Real.log T := by linarith
  have hA : 0 < titchmarshLogCap T := titchmarshLogCap_pos (by linarith)
  have hfac : (1 : ℝ) ≤ 20 * Real.exp 4 := by
    have he : (1 : ℝ) ≤ Real.exp 4 := Real.one_le_exp (by norm_num)
    nlinarith
  have hTsq : T ≤ (2 + T) ^ 2 := by nlinarith [sq_nonneg (2 + T)]
  have hTM : T ≤ 20 * Real.exp 4 * (2 + T) ^ 2 := by
    calc
      T ≤ (2 + T) ^ 2 := hTsq
      _ ≤ (20 * Real.exp 4) * (2 + T) ^ 2 := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hfac (sq_nonneg (2 + T))
  have hlogTA : Real.log T ≤ titchmarshLogCap T := by
    unfold titchmarshLogCap
    exact Real.log_le_log hTpos hTM
  have hp : (1 : ℝ) ≤ 6 ^ (n + 1) := one_le_pow₀ (by norm_num)
  have hAB : titchmarshLogCap T ≤
      titchmarshCrudeMajorant (titchmarshLogCap T) n := by
    calc
      titchmarshLogCap T ≤ titchmarshLogCap T + 10 := by linarith
      _ ≤ 6 ^ (n + 1) * (titchmarshLogCap T + 10) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hp
          (show 0 ≤ titchmarshLogCap T + 10 by linarith)
      _ = titchmarshCrudeMajorant (titchmarshLogCap T) n := rfl
  have hlogLower : Real.log (Real.log T) ≤
      Real.log (titchmarshCrudeMajorant (titchmarshLogCap T) n) := by
    exact Real.log_le_log hlogTpos (hlogTA.trans hAB)
  have hcapUpper := titchmarshLogCap_add_ten_le_six_log hT hlogT
  have hcapTenPos : 0 < titchmarshLogCap T + 10 := by linarith
  have hsixLogPos : 0 < 6 * Real.log T := by positivity
  have hlogCapUpper : Real.log (titchmarshLogCap T + 10) ≤
      Real.log 6 + Real.log (Real.log T) := by
    calc
      Real.log (titchmarshLogCap T + 10) ≤ Real.log (6 * Real.log T) :=
        Real.log_le_log hcapTenPos hcapUpper
      _ = Real.log 6 + Real.log (Real.log T) := by
        rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hlogTpos.ne']
  have hlogSix : Real.log 6 ≤ 5 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
    norm_num at this ⊢
    exact this
  have hn' : ((n + 1 : ℕ) : ℝ) <
      Real.log (Real.log (Real.log T)) / 50 + 2 := by
    norm_num
    linarith
  have hterm : ((n + 1 : ℕ) : ℝ) * Real.log 6 ≤
      Real.log (Real.log (Real.log T)) + 10 := by
    have hlogSix0 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    have hmul := mul_le_mul hn'.le hlogSix hlogSix0
      (by positivity : (0 : ℝ) ≤ Real.log (Real.log (Real.log T)) / 50 + 2)
    nlinarith
  have hmajorantLog :
      Real.log (titchmarshCrudeMajorant (titchmarshLogCap T) n) =
        ((n + 1 : ℕ) : ℝ) * Real.log 6 +
          Real.log (titchmarshLogCap T + 10) := by
    rw [titchmarshCrudeMajorant,
      Real.log_mul (pow_ne_zero _ (by norm_num : (6 : ℝ) ≠ 0)) hcapTenPos.ne',
      Real.log_pow]
  constructor
  · exact hlogLower
  · rw [hmajorantLog]
    linarith

/-- Explicit width used in the formal Titchmarsh theorem. -/
def titchmarshZeroGapWidth (T : ℝ) : ℝ :=
  1000 / Real.log (Real.log (Real.log T))

/-- Titchmarsh, Theorem 9.12, with an explicit absolute constant: every sufficiently high
ordinate is within `1000 / log log log T` of the ordinate of a Riemann-zeta zero. -/
theorem eventually_exists_riemannZeta_zero_titchmarsh :
    ∀ᶠ T : ℝ in atTop, ∃ ρ : ℂ,
      riemannZeta ρ = 0 ∧ |ρ.im - T| < titchmarshZeroGapWidth T := by
  have hL1 : Tendsto (fun T : ℝ => Real.log T) atTop atTop := Real.tendsto_log_atTop
  have hL2 : Tendsto (fun T : ℝ => Real.log (Real.log T)) atTop atTop :=
    Real.tendsto_log_atTop.comp hL1
  have hL3 : Tendsto (fun T : ℝ => Real.log (Real.log (Real.log T))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL2
  have hweight := hL2.eventually eventually_titchmarshRefinedWeight_mul_sub_gt
  filter_upwards [eventually_ge_atTop (25000000 : ℝ), hL1.eventually_ge_atTop 10,
    hL2.eventually_ge_atTop 10, hL3.eventually_ge_atTop 2000, hweight] with
      T hT hlogT hloglogT hlogloglogT hweightT
  let L₁ := Real.log T
  let L₂ := Real.log L₁
  let L₃ := Real.log L₂
  let h := titchmarshZeroGapWidth T
  let n := titchmarshCircleCount h
  let A := titchmarshLogCap T
  let B := titchmarshCrudeMajorant A n
  let q := titchmarshRefinedWeight n
  let K := titchmarshRefinedLogBound A n
  have hTtwo : 2 ≤ T := by linarith
  have hL1ten : 10 ≤ L₁ := by simpa [L₁] using hlogT
  have hL1pos : 0 < L₁ := by linarith
  have hL2ten : 10 ≤ L₂ := by simpa [L₂, L₁] using hloglogT
  have hL2pos : 0 < L₂ := by linarith
  have hL3large : 2000 ≤ L₃ := by simpa [L₃, L₂, L₁] using hlogloglogT
  have hL3pos : 0 < L₃ := by linarith
  have hh : 0 < h := by
    dsimp only [h, titchmarshZeroGapWidth]
    positivity
  have hhsmall : h ≤ 1 / 2 := by
    dsimp only [h, titchmarshZeroGapWidth]
    rw [div_le_iff₀ hL3pos]
    dsimp only [L₃, L₂, L₁] at hL3large ⊢
    linarith
  have hwidth : 20 / h = L₃ / 50 := by
    dsimp only [h, titchmarshZeroGapWidth, L₃, L₂, L₁]
    field_simp
    ring
  have hn : (n : ℝ) < L₃ / 50 + 1 := by
    have hnraw := titchmarshCircleCount_upper (h := h) hh
    rw [hwidth] at hnraw
    simpa only [n] using hnraw
  have hweightPoint : L₃ + 100 < q * (L₂ - 100) := by
    have hw := hweightT n
    have hn' : (n : ℝ) < Real.log L₂ / 50 + 1 := by
      simpa only [L₃] using hn
    have := hw hn'
    simpa only [L₃, q] using this
  by_cases hex : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ |ρ.im - T| < h
  · simpa only [h] using hex
  · exfalso
    have hzero : ∀ z ∈ titchmarshHorizontalStrip T h, riemannZeta z ≠ 0 := by
      intro z hz hzeta
      exact hex ⟨z, hzeta, hz⟩
    obtain ⟨L, hLan, hLexp, hterminalUpper⟩ :=
      exists_analyticLog_terminal_le_refined_of_zeroFree hh hhsmall (by linarith) hzero
    have hterminalMem : smoothAFEZetaLeftLinePt T ∈ titchmarshHorizontalStrip T h := by
      simp [titchmarshHorizontalStrip, hh]
    have hterminalLower := half_log_le_norm_analyticLog_terminal hT
      (hLexp (smoothAFEZetaLeftLinePt T) hterminalMem)
    have hAK : ‖L (smoothAFEZetaLeftLinePt T)‖ ≤ K := by
      simpa only [K, A, n] using hterminalUpper
    have hhalfPos : 0 < (1 / 2 : ℝ) * L₁ := by positivity
    have hKpos : 0 < K := by
      exact titchmarshRefinedLogBound_pos (titchmarshLogCap_pos (by linarith)) n
    have hlogTerminal : Real.log ((1 / 2 : ℝ) * L₁) ≤ Real.log K := by
      apply Real.log_le_log hhalfPos
      calc
        (1 / 2 : ℝ) * L₁ ≤ ‖L (smoothAFEZetaLeftLinePt T)‖ := by
          simpa only [L₁] using hterminalLower
        _ ≤ K := hAK
    have hlogtwo : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at this ⊢
      exact this
    have hloghalf : -1 ≤ Real.log (1 / 2 : ℝ) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
      linarith
    rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) hL1pos.ne'] at hlogTerminal
    have hKLower : L₂ - 1 ≤ Real.log K := by
      dsimp only [L₂]
      linarith
    have hApos : 0 < A := titchmarshLogCap_pos (by linarith)
    have hlogRec : Real.log K ≤
        q * Real.log 60 + (1 - q) * Real.log B := by
      simpa only [K, A, n, q, B] using log_titchmarshRefinedLogBound_le hApos n
    have hBbounds := log_titchmarshCrudeMajorant_bounds hTtwo hL1ten
      (n := n) (by simpa only [L₃, L₂, L₁] using hn) (by linarith : 0 ≤ L₃)
    have hBLower : L₂ ≤ Real.log B := by
      simpa only [B, A, L₂, L₁] using hBbounds.1
    have hBUpper : Real.log B ≤ L₂ + L₃ + 20 := by
      simpa only [B, A, L₂, L₃, L₁] using hBbounds.2
    have hlogSixty : Real.log 60 ≤ 59 := by
      have hs := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 60)
      norm_num at hs ⊢
      exact hs
    have hq0 : 0 ≤ q := titchmarshRefinedWeight_nonneg n
    have hqdiff : q * (L₂ - 100) ≤ q * (Real.log B - Real.log 60) := by
      gcongr
      linarith
    have hrewrite : q * Real.log 60 + (1 - q) * Real.log B =
        Real.log B - q * (Real.log B - Real.log 60) := by ring
    rw [hrewrite] at hlogRec
    have hKUpper : Real.log K ≤ Real.log B - q * (L₂ - 100) := by linarith
    have hKStrict : Real.log K < L₂ - 80 := by linarith
    linarith

/-- Classical existential-constant form of Titchmarsh's Theorem 9.12. -/
theorem titchmarsh_exists_zero_near_height :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∃ ρ : ℂ,
      riemannZeta ρ = 0 ∧
        |ρ.im - T| < C / Real.log (Real.log (Real.log T)) := by
  refine ⟨1000, by norm_num, ?_⟩
  simpa only [titchmarshZeroGapWidth] using eventually_exists_riemannZeta_zero_titchmarsh

end RHTower
