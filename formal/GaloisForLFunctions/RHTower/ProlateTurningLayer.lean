import GaloisForLFunctions.RHTower.ProlateAllowedEnergy
import GaloisForLFunctions.RHTower.ProlateSeparationTunneling

/-!
# Clock-free propagation across the prolate turning layer

The scaled state energy `Phi² + (Phi'/c)²` can grow backward through the allowed region at rate
at most `exp(c · distance)`.  Applying this only on the width-`1/c` Airy layer costs the fixed
factor `exp(1)`.  Combined with the monotone allowed energy, this propagates the sharp tunneling
amplitude through the whole oscillatory interval without changing its exponential clock.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Set MeasureTheory

open _root_.RHTower

/-- Scaled first-order state energy at the turning layer. -/
def prolateTurningEnergy (c : ℝ) (Φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  Φ y ^ (2 : ℕ) + (deriv Φ y / c) ^ (2 : ℕ)

theorem prolateTurningEnergy_nonneg (c : ℝ) (Φ : ℝ → ℝ) (y : ℝ) :
    0 ≤ prolateTurningEnergy c Φ y := by
  rw [prolateTurningEnergy]
  positivity

theorem hasDerivAt_prolateTurningEnergy
    {c y : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) :
    HasDerivAt (prolateTurningEnergy c Φ)
      (2 * Φ y * deriv Φ y +
        2 * (deriv Φ y / c) * (deriv (deriv Φ) y / c)) y := by
  have hΦ1 : HasDerivAt Φ (deriv Φ y) y :=
    ((contDiff_infty_iff_deriv.mp hsm).1 y).hasDerivAt
  have hΦ2 : HasDerivAt (deriv Φ) (deriv (deriv Φ) y) y :=
    ((contDiff_infty_iff_deriv.mp
      (contDiff_infty_iff_deriv.mp hsm).2).1 y).hasDerivAt
  have hsum := (hΦ1.pow 2).add ((hΦ2.div_const c).pow 2)
  have hfun : Φ ^ (2 : ℕ) + (fun t => deriv Φ t / c) ^ (2 : ℕ) = prolateTurningEnergy c Φ := by
    funext t
    rfl
  rw [hfun] at hsum
  refine hsum.congr_deriv ?_
  norm_num

/-- Radial ODE form of the scaled-state derivative. -/
theorem hasDerivAt_prolateTurningEnergy_radial
    {c s y : ℝ} (hc : c ≠ 0) {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ x = -(s * c ^ (2 : ℕ)) * Φ x)
    (hy : y ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (prolateTurningEnergy c Φ)
      (2 * (1 - prolateAllowedPotential s y) * Φ y * deriv Φ y +
        (4 * y / (c ^ (2 : ℕ) * (1 - y ^ (2 : ℕ)))) * deriv Φ y ^ (2 : ℕ)) y := by
  have hp : 1 - y ^ (2 : ℕ) ≠ 0 := by nlinarith [hy.1, hy.2]
  have heigy := heig y ⟨hy.1.le, hy.2.le⟩
  have hsecond : deriv (deriv Φ) y =
      (2 * y / (1 - y ^ (2 : ℕ))) * deriv Φ y -
        c ^ (2 : ℕ) * prolateAllowedPotential s y * Φ y := by
    rw [prolateSLAction] at heigy
    rw [prolateAllowedPotential]
    field_simp [hp]
    nlinarith [heigy]
  have hE := hasDerivAt_prolateTurningEnergy (c := c) (y := y) hsm
  refine hE.congr_deriv ?_
  rw [hsecond]
  field_simp [hc]
  ring

/-- Backward logarithmic growth of the scaled state is at most `c` throughout the positive
allowed region. -/
theorem neg_c_mul_turningEnergy_le_deriv
    {c s y : ℝ} (hc : 0 < c) (hs1 : s ≤ 1) (hy0 : 0 ≤ y)
    (hy1 : y < 1) (hturn : y ^ (2 : ℕ) ≤ s) {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ x = -(s * c ^ (2 : ℕ)) * Φ x) :
    -(c * prolateTurningEnergy c Φ y) ≤
      deriv (prolateTurningEnergy c Φ) y := by
  have hy : y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hy1⟩
  have hderiv := hasDerivAt_prolateTurningEnergy_radial hc.ne' hsm heig hy
  rw [hderiv.deriv]
  have hp : 0 < 1 - y ^ (2 : ℕ) := by nlinarith
  have hq0 : 0 ≤ prolateAllowedPotential s y := by
    rw [prolateAllowedPotential]
    exact div_nonneg (sub_nonneg.2 hturn) hp.le
  have hq1 : prolateAllowedPotential s y ≤ 1 := by
    rw [prolateAllowedPotential]
    exact (div_le_one hp).2 (by linarith)
  have hA0 : 0 ≤ 1 - prolateAllowedPotential s y := sub_nonneg.2 hq1
  have hA1 : 1 - prolateAllowedPotential s y ≤ 1 := by linarith
  have hpositive : 0 ≤
      (4 * y / (c ^ (2 : ℕ) * (1 - y ^ (2 : ℕ)))) * deriv Φ y ^ (2 : ℕ) := by
    positivity
  have hyoung : -(c * prolateTurningEnergy c Φ y) ≤
      2 * Φ y * deriv Φ y := by
    have hsquare := sq_nonneg (c * Φ y + deriv Φ y)
    rw [prolateTurningEnergy]
    have hrewrite :
        c * (Φ y ^ (2 : ℕ) + (deriv Φ y / c) ^ (2 : ℕ)) =
          (c ^ (2 : ℕ) * Φ y ^ (2 : ℕ) + deriv Φ y ^ (2 : ℕ)) / c := by
      field_simp
    rw [hrewrite]
    calc
      -((c ^ (2 : ℕ) * Φ y ^ (2 : ℕ) + deriv Φ y ^ (2 : ℕ)) / c) =
          (-(c ^ (2 : ℕ) * Φ y ^ (2 : ℕ) + deriv Φ y ^ (2 : ℕ))) / c := by ring
      _ ≤ 2 * Φ y * deriv Φ y := by
        rw [div_le_iff₀ hc]
        nlinarith
  have hcross : -(c * prolateTurningEnergy c Φ y) ≤
      2 * (1 - prolateAllowedPotential s y) * Φ y * deriv Φ y := by
    by_cases hsign : 0 ≤ Φ y * deriv Φ y
    · have hM0 := prolateTurningEnergy_nonneg c Φ y
      have : 0 ≤ 2 * (1 - prolateAllowedPotential s y) *
          Φ y * deriv Φ y := by nlinarith [mul_nonneg hA0 hsign]
      nlinarith
    · have hsign' : Φ y * deriv Φ y ≤ 0 := le_of_not_ge hsign
      have hmul := mul_le_mul_of_nonpos_right hA1 hsign'
      nlinarith [hyoung]
  nlinarith

/-- The exponentially weighted state energy is monotone toward the turning point. -/
theorem monotoneOn_turningEnergy_mul_exp
    {c s a b : ℝ} (hc : 0 < c) (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hb1 : b < 1) (hturn : b ^ (2 : ℕ) ≤ s) (hs1 : s ≤ 1)
    {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ x = -(s * c ^ (2 : ℕ)) * Φ x) :
    MonotoneOn (fun y => prolateTurningEnergy c Φ y * Real.exp (c * y)) (Icc a b) := by
  have hEderiv : ∀ y ∈ Icc a b,
      HasDerivAt (prolateTurningEnergy c Φ)
        (deriv (prolateTurningEnergy c Φ) y) y := by
    intro y hy
    have h := hasDerivAt_prolateTurningEnergy_radial hc.ne' hsm heig
      ⟨lt_of_lt_of_le (by norm_num) (ha0.trans hy.1), lt_of_le_of_lt hy.2 hb1⟩
    exact h.congr_deriv h.deriv.symm
  have hweighted : ∀ y ∈ Icc a b,
      HasDerivAt (fun t => prolateTurningEnergy c Φ t * Real.exp (c * t))
        (Real.exp (c * y) *
          (deriv (prolateTurningEnergy c Φ) y +
            c * prolateTurningEnergy c Φ y)) y := by
    intro y hy
    have hexp := ((hasDerivAt_id y).const_mul c).exp
    have hmul := (hEderiv y hy).mul hexp
    exact hmul.congr_deriv (by
      simp only [id_eq, mul_one]
      ring)
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (fun y hy => (hweighted y hy).continuousAt.continuousWithinAt) ?_ ?_
  · rw [interior_Icc]
    intro y hy
    exact (hweighted y ⟨hy.1.le, hy.2.le⟩).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    rw [(hweighted y ⟨hy.1.le, hy.2.le⟩).deriv]
    exact mul_nonneg (Real.exp_pos _).le (by
      have hlow := neg_c_mul_turningEnergy_le_deriv hc hs1
        (ha0.trans hy.1.le) (hy.2.trans hb1)
        ((sq_le_sq₀ (ha0.trans hy.1.le) (ha0.trans hab)).2 hy.2.le |>.trans hturn)
        hsm heig
      linarith)

/-- Backward propagation estimate for the scaled state. -/
theorem turningEnergy_le_mul_exp_distance
    {c s x z : ℝ} (hc : 0 < c) (hx0 : 0 ≤ x) (hxz : x ≤ z)
    (hz1 : z < 1) (hzturn : z ^ (2 : ℕ) ≤ s) (hs1 : s ≤ 1)
    {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y) :
    prolateTurningEnergy c Φ x ≤
      prolateTurningEnergy c Φ z * Real.exp (c * (z - x)) := by
  have hmono := monotoneOn_turningEnergy_mul_exp hc hx0 hxz hz1 hzturn hs1 hsm heig
  have hraw := hmono (left_mem_Icc.2 hxz) (right_mem_Icc.2 hxz) hxz
  have hexppos : 0 < Real.exp (c * x) := Real.exp_pos _
  change prolateTurningEnergy c Φ x * Real.exp (c * x) ≤
    prolateTurningEnergy c Φ z * Real.exp (c * z) at hraw
  have hfactor : Real.exp (c * z) =
      Real.exp (c * x) * Real.exp (c * (z - x)) := by
    rw [← Real.exp_add]
    congr 2
    ring
  rw [hfactor] at hraw
  have hcanceled : Real.exp (c * x) * prolateTurningEnergy c Φ x ≤
      Real.exp (c * x) *
        (prolateTurningEnergy c Φ z * Real.exp (c * (z - x))) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hraw
  nlinarith

/-- Endpoint-normalized radial modes are positive from their positive turning point to the
singular endpoint. -/
theorem prolate_pos_on_right_of_radial_turning
    {c s : ℝ} {Φ : ℝ → ℝ} (hs0 : 0 ≤ s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) :
    ∀ y ∈ Icc (Real.sqrt s) 1, 0 < Φ y := by
  have hsqrt0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt s ^ (2 : ℕ) = s := Real.sq_sqrt hs0
  apply prolate_pos_on_right_forbidden_region hsm heig hΦ1 hsqrt0
  intro y hy
  have hy0 : 0 ≤ y := hsqrt0.trans hy.1
  have hsq : Real.sqrt s ^ (2 : ℕ) ≤ y ^ (2 : ℕ) :=
    (sq_le_sq₀ hsqrt0 hy0).2 hy.1
  nlinarith [sq_nonneg c]

/-- Endpoint comparison supplies the radial-barrier bound at every positive point of a zero-free
forbidden interval. -/
theorem prolateLogDeriv_le_radialBarrier_of_endpoint_normalized
    {c s a : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 ≤ s) (hs1 : s < 1) (hcs : 4 ≤ c * s)
    (ha0 : 0 < a) (ha1 : a < 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) (hpos : ∀ y ∈ Icc a 1, 0 < Φ y) :
    prolateLogDeriv Φ a ≤ prolateRadialBarrier c s a := by
  let l : Filter ℝ := nhdsWithin 1 (Iio 1)
  have hab : ∀ᶠ b : ℝ in l, a ≤ b :=
    mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds ha1)
  have hb1 : ∀ᶠ b : ℝ in l, b < 1 := self_mem_nhdsWithin
  have hinit := eventually_prolateLogDeriv_le_radialBarrier_at_one hc hs0 hs1 hsm hΦ1
  obtain ⟨b, habb, hb, hterminal⟩ := (hab.and (hb1.and hinit)).exists
  exact prolateLogDeriv_le_radialBarrier hc hs0 hs1 hcs hsm heig
    habb ha0 hb (fun y hy => hpos y ⟨hy.1, hy.2.trans hb.le⟩) hterminal
    a ⟨le_rfl, habb⟩

/-- At the radial turning point the derivative is controlled by the turning amplitude at the
natural first-order scale `c * sqrt s`. -/
theorem abs_deriv_prolate_turningPoint_le
    {c s : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 < s) (hs1 : s < 1) (hcs : 4 ≤ c * s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) :
    |deriv Φ (Real.sqrt s)| ≤
      c * Real.sqrt s * Φ (Real.sqrt s) := by
  have hsqrt0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hsqrt1 : Real.sqrt s < 1 := by
    nlinarith [Real.sq_sqrt hs0.le, Real.sqrt_nonneg s]
  have hsqrtSq : Real.sqrt s ^ (2 : ℕ) = s := Real.sq_sqrt hs0.le
  have hpos := prolate_pos_on_right_of_radial_turning hs0.le hsm heig hΦ1
  have hQ : ∀ y ∈ Icc (Real.sqrt s) 1,
      0 ≤ -(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ) := by
    intro y hy
    have hy0 : 0 ≤ y := hsqrt0.le.trans hy.1
    have hsq : Real.sqrt s ^ (2 : ℕ) ≤ y ^ (2 : ℕ) :=
      (sq_le_sq₀ hsqrt0.le hy0).2 hy.1
    nlinarith [sq_nonneg c]
  have hlog := prolateLogDeriv_le_radialBarrier_of_endpoint_normalized
    hc hs0.le hs1 hcs hsqrt0 hsqrt1 hsm heig hΦ1 hpos
  have hsqrtOne : 0 < Real.sqrt (1 - s) := Real.sqrt_pos.2 (by linarith)
  have hbarrier : prolateRadialBarrier c s (Real.sqrt s) = c * Real.sqrt s := by
    rw [prolateRadialBarrier, hsqrtSq]
    field_simp [hsqrtOne.ne']
  rw [hbarrier, prolateLogDeriv, ← neg_div] at hlog
  have hderiv : deriv Φ (Real.sqrt s) ≤ 0 :=
    deriv_nonpos_of_turning hsm heig (by linarith)
      (fun y hy => (hpos y hy).le) hQ ⟨le_rfl, hsqrt1⟩
  rw [abs_of_nonpos hderiv]
  exact (div_le_iff₀ (hpos _ (left_mem_Icc.2 hsqrt1.le))).mp hlog

/-- The scaled first-order energy at the turning point is at most twice the squared turning
amplitude. -/
theorem prolateTurningEnergy_turningPoint_le_two_sq
    {c s : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 < s) (hs1 : s < 1) (hcs : 4 ≤ c * s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) :
    prolateTurningEnergy c Φ (Real.sqrt s) ≤
      2 * Φ (Real.sqrt s) ^ (2 : ℕ) := by
  have hsqrt0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hsqrt1 : Real.sqrt s < 1 := by
    nlinarith [Real.sq_sqrt hs0.le, Real.sqrt_nonneg s]
  have hsqrtle : Real.sqrt s ≤ 1 := hsqrt1.le
  have hA := prolate_pos_on_right_of_radial_turning hs0.le hsm heig hΦ1
    _ (left_mem_Icc.2 hsqrt1.le)
  have habs := abs_deriv_prolate_turningPoint_le hc hs0 hs1 hcs hsm heig hΦ1
  have hfactor : 0 ≤ c * (1 - Real.sqrt s) * Φ (Real.sqrt s) :=
    mul_nonneg (mul_nonneg hc.le (sub_nonneg.2 hsqrtle)) hA.le
  have hdivabs : |deriv Φ (Real.sqrt s) / c| ≤ Φ (Real.sqrt s) := by
    rw [abs_div, abs_of_pos hc, div_le_iff₀ hc]
    nlinarith
  have hsq : (deriv Φ (Real.sqrt s) / c) ^ (2 : ℕ) ≤
      Φ (Real.sqrt s) ^ (2 : ℕ) := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (deriv Φ (Real.sqrt s) / c)) hA.le).2 hdivabs
  rw [prolateTurningEnergy]
  nlinarith

/-- Match point one inverse-bandwidth inside the positive turning point. -/
def prolateMatchPoint (c s : ℝ) : ℝ := Real.sqrt s - 1 / c

/-- At the match point, the allowed potential retains at least the scale `sqrt s / c`. -/
theorem sqrt_div_le_prolateAllowedPotential_matchPoint
    {c s : ℝ} (hc : 0 < c) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hscale : 1 ≤ c * Real.sqrt s) :
    Real.sqrt s / c ≤ prolateAllowedPotential s (prolateMatchPoint c s) := by
  let r : ℝ := Real.sqrt s
  let z : ℝ := prolateMatchPoint c s
  have hr0 : 0 < r := by exact Real.sqrt_pos.2 hs0
  have hrsq : r ^ (2 : ℕ) = s := by exact Real.sq_sqrt hs0.le
  have hr1 : r ≤ 1 := by nlinarith
  have hinv : 1 / c ≤ r := by
    rw [div_le_iff₀ hc]
    nlinarith
  have hzdef : z = r - 1 / c := rfl
  have hz0 : 0 ≤ z := by rw [hzdef]; linarith
  have hzr : z < r := by
    rw [hzdef]
    have : 0 < 1 / c := one_div_pos.mpr hc
    linarith
  have hz1 : z < 1 := hzr.trans_le hr1
  have hden : 0 < 1 - z ^ (2 : ℕ) := by nlinarith
  have hnum0 : 0 ≤ s - z ^ (2 : ℕ) := by nlinarith
  have hfactor : s - z ^ (2 : ℕ) = (1 / c) * (r + z) := by
    rw [← hrsq, hzdef]
    field_simp [hc.ne']
    ring
  have hnum : r / c ≤ s - z ^ (2 : ℕ) := by
    rw [hfactor]
    calc
      r / c = (1 / c) * r := by ring
      _ ≤ (1 / c) * (r + z) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hz0) (one_div_nonneg.mpr hc.le)
  rw [prolateAllowedPotential]
  refine hnum.trans ?_
  rw [le_div_iff₀ hden]
  nlinarith [mul_nonneg hnum0 (sq_nonneg z)]

/-- Allowed energy is dominated by `c²` times scaled state energy whenever `s ≤ 1`. -/
theorem prolateAllowedEnergy_le_c_sq_mul_turningEnergy
    {c s y : ℝ} (hc : c ≠ 0) (hs1 : s ≤ 1) (hy0 : 0 ≤ y) (hy1 : y < 1)
    {Φ : ℝ → ℝ} :
    prolateAllowedEnergy c s Φ y ≤ c ^ (2 : ℕ) * prolateTurningEnergy c Φ y := by
  have hp : 0 < 1 - y ^ (2 : ℕ) := by nlinarith
  have hq1 : prolateAllowedPotential s y ≤ 1 := by
    rw [prolateAllowedPotential]
    exact (div_le_one hp).2 (by linarith)
  have hterm : c ^ (2 : ℕ) * prolateAllowedPotential s y * Φ y ^ (2 : ℕ) ≤
      c ^ (2 : ℕ) * Φ y ^ (2 : ℕ) := by
    simpa only [mul_assoc, one_mul] using mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hq1 (sq_nonneg (Φ y))) (sq_nonneg c)
  rw [prolateAllowedEnergy, prolateTurningEnergy]
  field_simp [hc]
  nlinarith

/-- Crossing the inverse-bandwidth turning layer costs at most the fixed factor `exp 1`. -/
theorem prolateTurningEnergy_matchPoint_le
    {c s : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 < s) (hs1 : s < 1) (hcs : 4 ≤ c * s)
    (hscale : 1 ≤ c * Real.sqrt s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) :
    prolateTurningEnergy c Φ (prolateMatchPoint c s) ≤
      2 * Real.exp 1 * Φ (Real.sqrt s) ^ (2 : ℕ) := by
  have hsqrt0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hsqrt1 : Real.sqrt s < 1 := by
    nlinarith [Real.sq_sqrt hs0.le, Real.sqrt_nonneg s]
  have hsqrtSq : Real.sqrt s ^ (2 : ℕ) = s := Real.sq_sqrt hs0.le
  have hinv : 1 / c ≤ Real.sqrt s := by
    rw [div_le_iff₀ hc]
    nlinarith
  have hz0 : 0 ≤ prolateMatchPoint c s := by
    rw [prolateMatchPoint]
    linarith
  have hzturn : prolateMatchPoint c s ≤ Real.sqrt s := by
    rw [prolateMatchPoint]
    have : 0 ≤ 1 / c := one_div_nonneg.mpr hc.le
    linarith
  have hprop := turningEnergy_le_mul_exp_distance hc hz0 hzturn hsqrt1
    (by rw [hsqrtSq]) hs1.le hsm heig
  have hexp : Real.exp (c * (Real.sqrt s - prolateMatchPoint c s)) = Real.exp 1 := by
    congr 1
    rw [prolateMatchPoint]
    field_simp [hc.ne']
    ring
  rw [hexp] at hprop
  calc
    prolateTurningEnergy c Φ (prolateMatchPoint c s) ≤
        prolateTurningEnergy c Φ (Real.sqrt s) * Real.exp 1 := hprop
    _ ≤ (2 * Φ (Real.sqrt s) ^ (2 : ℕ)) * Real.exp 1 :=
      mul_le_mul_of_nonneg_right
        (prolateTurningEnergy_turningPoint_le_two_sq hc hs0 hs1 hcs hsm heig hΦ1)
        (Real.exp_pos 1).le
    _ = 2 * Real.exp 1 * Φ (Real.sqrt s) ^ (2 : ℕ) := by ring

/-- Every point before the match point is controlled by match-point state energy with only the
polynomial factor `c / sqrt s`. -/
theorem prolate_value_sq_le_matchPoint_energy
    {c s x : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hscale : 1 ≤ c * Real.sqrt s)
    (hx0 : 0 ≤ x) (hxz : x ≤ prolateMatchPoint c s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y) :
    Φ x ^ (2 : ℕ) ≤ (c / Real.sqrt s) *
      prolateTurningEnergy c Φ (prolateMatchPoint c s) := by
  let r : ℝ := Real.sqrt s
  let z : ℝ := prolateMatchPoint c s
  have hr0 : 0 < r := Real.sqrt_pos.2 hs0
  have hrsq : r ^ (2 : ℕ) = s := Real.sq_sqrt hs0.le
  have hr1 : r ≤ 1 := by nlinarith
  have hinv : 1 / c ≤ r := by
    rw [div_le_iff₀ hc]
    nlinarith
  have hzdef : z = r - 1 / c := rfl
  have hz0 : 0 ≤ z := by rw [hzdef]; linarith
  have hzr : z < r := by
    rw [hzdef]
    have : 0 < 1 / c := one_div_pos.mpr hc
    linarith
  have hz1 : z < 1 := hzr.trans_le hr1
  have hzturn : z ^ (2 : ℕ) < s := by nlinarith
  have hqpos : 0 < prolateAllowedPotential s z :=
    prolateAllowedPotential_pos ⟨by linarith, hz1⟩ hzturn
  have hamp := c_sq_mul_value_sq_le_allowedEnergyRatio hx0 hxz hz1 hzturn hs1 hsm heig
  rw [prolateAllowedEnergyRatio] at hamp
  have hamp' : c ^ (2 : ℕ) * Φ x ^ (2 : ℕ) * prolateAllowedPotential s z ≤
      prolateAllowedEnergy c s Φ z := (le_div_iff₀ hqpos).mp hamp
  have hqlo : r / c ≤ prolateAllowedPotential s z := by
    exact sqrt_div_le_prolateAllowedPotential_matchPoint hc hs0 hs1 hscale
  have hleft : c ^ (2 : ℕ) * Φ x ^ (2 : ℕ) * (r / c) ≤
      c ^ (2 : ℕ) * Φ x ^ (2 : ℕ) * prolateAllowedPotential s z :=
    mul_le_mul_of_nonneg_left hqlo
      (mul_nonneg (sq_nonneg c) (sq_nonneg (Φ x)))
  have henergy : prolateAllowedEnergy c s Φ z ≤
      c ^ (2 : ℕ) * prolateTurningEnergy c Φ z :=
    prolateAllowedEnergy_le_c_sq_mul_turningEnergy hc.ne' hs1 hz0 hz1
  have hchain : c ^ (2 : ℕ) * Φ x ^ (2 : ℕ) * (r / c) ≤
      c ^ (2 : ℕ) * prolateTurningEnergy c Φ z := hleft.trans (hamp'.trans henergy)
  have hnormalized : c * (Φ x ^ (2 : ℕ) * r) ≤
      c * (c * prolateTurningEnergy c Φ z) := by
    convert hchain using 1 <;> field_simp [hc.ne']
  have hcancel : Φ x ^ (2 : ℕ) * r ≤ c * prolateTurningEnergy c Φ z :=
    le_of_mul_le_mul_left hnormalized hc
  change Φ x ^ (2 : ℕ) ≤ (c / r) * prolateTurningEnergy c Φ z
  rw [show (c / r) * prolateTurningEnergy c Φ z =
      (c * prolateTurningEnergy c Φ z) / r by ring]
  exact (le_div_iff₀ hr0).2 hcancel

/-- Uniform squared-amplitude envelope on the positive aperture.  The turning action remains
untouched; only the polynomial prefactor `c / sqrt s` is paid. -/
theorem prolate_value_sq_le_turning_envelope
    {c s x : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 < s) (hs1 : s < 1) (hcs : 4 ≤ c * s)
    (hscale : 1 ≤ c * Real.sqrt s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    Φ x ^ (2 : ℕ) ≤ 2 * Real.exp 1 * (c / Real.sqrt s) *
      Φ (Real.sqrt s) ^ (2 : ℕ) := by
  let r : ℝ := Real.sqrt s
  let z : ℝ := prolateMatchPoint c s
  have hr0 : 0 < r := Real.sqrt_pos.2 hs0
  have hrsq : r ^ (2 : ℕ) = s := Real.sq_sqrt hs0.le
  have hr1 : r < 1 := by nlinarith
  have hinv : 1 / c ≤ r := by
    rw [div_le_iff₀ hc]
    nlinarith
  have hzdef : z = r - 1 / c := rfl
  have hz0 : 0 ≤ z := by rw [hzdef]; linarith
  have hzr : z ≤ r := by
    rw [hzdef]
    have : 0 ≤ 1 / c := one_div_nonneg.mpr hc.le
    linarith
  have hrr : r * r ≤ 1 := by nlinarith
  have hrc : r ≤ c := by
    have hrInv : r ≤ 1 / r := (le_div_iff₀ hr0).2 hrr
    have hinvC : 1 / r ≤ c := by
      rw [div_le_iff₀ hr0]
      simpa only [one_mul, mul_comm] using hscale
    exact hrInv.trans hinvC
  have hcoef : 1 ≤ c / r := (le_div_iff₀ hr0).2 (by simpa using hrc)
  have hboost : 2 * Real.exp 1 * Φ r ^ (2 : ℕ) ≤
      2 * Real.exp 1 * (c / r) * Φ r ^ (2 : ℕ) := by
    have hbase : 0 ≤ 2 * Real.exp 1 * Φ r ^ (2 : ℕ) := by positivity
    calc
      2 * Real.exp 1 * Φ r ^ (2 : ℕ) = 1 * (2 * Real.exp 1 * Φ r ^ (2 : ℕ)) := by ring
      _ ≤ (c / r) * (2 * Real.exp 1 * Φ r ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_right hcoef hbase
      _ = 2 * Real.exp 1 * (c / r) * Φ r ^ (2 : ℕ) := by ring
  by_cases hxz : x ≤ z
  · have hvalue := prolate_value_sq_le_matchPoint_energy hc hs0 hs1.le hscale
      hx.1 hxz hsm heig
    have hmatch := prolateTurningEnergy_matchPoint_le hc hs0 hs1 hcs hscale
      hsm heig hΦ1
    have hscaled := mul_le_mul_of_nonneg_left hmatch
      (div_nonneg hc.le hr0.le)
    exact hvalue.trans (by
      change (c / r) * prolateTurningEnergy c Φ z ≤
        2 * Real.exp 1 * (c / r) * Φ r ^ (2 : ℕ)
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hscaled)
  · have hzx : z ≤ x := le_of_not_ge hxz
    by_cases hxr : x ≤ r
    · have hstate : Φ x ^ (2 : ℕ) ≤ prolateTurningEnergy c Φ x := by
        rw [prolateTurningEnergy]
        nlinarith [sq_nonneg (deriv Φ x / c)]
      have hprop := turningEnergy_le_mul_exp_distance hc hx.1 hxr hr1
        (by rw [hrsq]) hs1.le hsm heig
      have hdist : c * (r - x) ≤ 1 := by
        have hraw : r - x ≤ 1 / c := by rw [hzdef] at hzx; linarith
        calc
          c * (r - x) ≤ c * (1 / c) := mul_le_mul_of_nonneg_left hraw hc.le
          _ = 1 := by field_simp [hc.ne']
      have hexp : Real.exp (c * (r - x)) ≤ Real.exp 1 :=
        Real.exp_le_exp.mpr hdist
      have hprop' : prolateTurningEnergy c Φ x ≤
          prolateTurningEnergy c Φ r * Real.exp 1 :=
        hprop.trans (mul_le_mul_of_nonneg_left hexp
          (prolateTurningEnergy_nonneg c Φ r))
      have hturn := prolateTurningEnergy_turningPoint_le_two_sq
        hc hs0 hs1 hcs hsm heig hΦ1
      have hturn' : prolateTurningEnergy c Φ r * Real.exp 1 ≤
          2 * Real.exp 1 * Φ r ^ (2 : ℕ) := by
        have := mul_le_mul_of_nonneg_right hturn (Real.exp_pos 1).le
        simpa only [mul_assoc, mul_comm, mul_left_comm] using this
      exact hstate.trans (hprop'.trans (hturn'.trans hboost))
    · have hrx : r ≤ x := le_of_not_ge hxr
      have hpos := prolate_pos_on_right_of_radial_turning hs0.le hsm heig hΦ1
      have hQ : ∀ y ∈ Icc r 1,
          0 ≤ -(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ) := by
        intro y hy
        have hy0 : 0 ≤ y := hr0.le.trans hy.1
        have hsq : r ^ (2 : ℕ) ≤ y ^ (2 : ℕ) := (sq_le_sq₀ hr0.le hy0).2 hy.1
        nlinarith [sq_nonneg c]
      have hanti := antitoneOn_of_turning hsm heig (by linarith)
        (fun y hy => (hpos y hy).le) hQ
      have hvalue : Φ x ≤ Φ r :=
        hanti (left_mem_Icc.2 hr1.le) ⟨hrx, hx.2⟩ hrx
      have hsq : Φ x ^ (2 : ℕ) ≤ Φ r ^ (2 : ℕ) :=
        pow_le_pow_left₀ (hpos x ⟨hrx, hx.2⟩).le hvalue 2
      exact hsq.trans ((by
        have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
        have hA2 : 0 ≤ Φ r ^ (2 : ℕ) := sq_nonneg _
        nlinarith [mul_nonneg (sub_nonneg.2 he) hA2]) :
          Φ r ^ (2 : ℕ) ≤ 2 * Real.exp 1 * Φ r ^ (2 : ℕ)) |>.trans hboost

/-- The full aperture mass is controlled by the turning amplitude with the same exponential
clock and only a polynomial prefactor. -/
theorem integral_sq_le_turning_amplitude_envelope
    {c s : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 < s) (hs1 : s < 1) (hcs : 4 ≤ c * s)
    (hscale : 1 ≤ c * Real.sqrt s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) (heven : Function.Even Φ) :
    (∫ y in (-1 : ℝ)..1, Φ y ^ (2 : ℕ)) ≤
      4 * Real.exp 1 * (c / Real.sqrt s) * Φ (Real.sqrt s) ^ (2 : ℕ) := by
  let C : ℝ := 2 * Real.exp 1 * (c / Real.sqrt s) * Φ (Real.sqrt s) ^ (2 : ℕ)
  have hint : IntervalIntegrable (fun y : ℝ => Φ y ^ (2 : ℕ)) volume (-1) 1 :=
    (hsm.continuous.pow 2).intervalIntegrable (-1) 1
  have hpoint : ∀ y ∈ Icc (-1 : ℝ) 1, Φ y ^ (2 : ℕ) ≤ C := by
    intro y hy
    have habs : |y| ∈ Icc (0 : ℝ) 1 := by
      exact ⟨abs_nonneg y, (abs_le).2 ⟨by linarith [hy.1], hy.2⟩⟩
    have henv := prolate_value_sq_le_turning_envelope
      hc hs0 hs1 hcs hscale hsm heig hΦ1 habs
    have heq : Φ |y| = Φ y := by
      by_cases hy0 : 0 ≤ y
      · rw [abs_of_nonneg hy0]
      · rw [abs_of_neg (lt_of_not_ge hy0)]
        exact heven y
    change Φ y ^ (2 : ℕ) ≤ C
    rw [← heq]
    exact henv
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1)
    hint intervalIntegrable_const hpoint
  calc
    (∫ y in (-1 : ℝ)..1, Φ y ^ (2 : ℕ)) ≤ ∫ _y in (-1 : ℝ)..1, C := hmono
    _ = 4 * Real.exp 1 * (c / Real.sqrt s) * Φ (Real.sqrt s) ^ (2 : ℕ) := by
      simp only [intervalIntegral.integral_const, sub_neg_eq_add]
      dsimp only [C]
      ring

/-- **Clock-preserving aperture bound.**  Endpoint normalization and the radial barrier give an
explicit `exp (2c(1-s))` upper bound for total aperture mass. -/
theorem integral_sq_le_exp_twice_turning_action
    {c s : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 < s) (hs1 : s < 1) (hcs : 4 ≤ c * s)
    (hscale : 1 ≤ c * Real.sqrt s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) (heven : Function.Even Φ) :
    (∫ y in (-1 : ℝ)..1, Φ y ^ (2 : ℕ)) ≤
      4 * Real.exp 1 * (c / Real.sqrt s) * Real.exp (2 * c * (1 - s)) := by
  have hmass := integral_sq_le_turning_amplitude_envelope
    hc hs0 hs1 hcs hscale hsm heig hΦ1 heven
  have hturn := prolateTurningPoint_mul_exp_neg_action_le_one
    hc hs0 hs1 hcs hsm heig hΦ1
  let T : ℝ := c * (1 - s)
  have hcancel : Real.exp (-T) * Real.exp T = 1 := by
    rw [← Real.exp_add]
    simp
  have hAle : Φ (Real.sqrt s) ≤ Real.exp T := by
    calc
      Φ (Real.sqrt s) =
          (Φ (Real.sqrt s) * Real.exp (-T)) * Real.exp T := by
        rw [mul_assoc, hcancel, mul_one]
      _ ≤ 1 * Real.exp T :=
        mul_le_mul_of_nonneg_right hturn (Real.exp_pos T).le
      _ = Real.exp T := one_mul _
  have hApos := prolate_pos_on_right_of_radial_turning hs0.le hsm heig hΦ1
    _ (left_mem_Icc.2 (by
      nlinarith [Real.sq_sqrt hs0.le, Real.sqrt_nonneg s]))
  have hsq : Φ (Real.sqrt s) ^ (2 : ℕ) ≤ Real.exp (2 * c * (1 - s)) := by
    have hpow := pow_le_pow_left₀ hApos.le hAle 2
    calc
      Φ (Real.sqrt s) ^ (2 : ℕ) ≤ Real.exp T ^ (2 : ℕ) := hpow
      _ = Real.exp (2 * c * (1 - s)) := by
        rw [pow_two, ← Real.exp_add]
        dsimp only [T]
        congr 1
        ring
  exact hmass.trans (mul_le_mul_of_nonneg_left hsq (by positivity))

/-- Scalar extraction of a leakage lower bound from exact exterior/interior mass balance. -/
theorem leakage_lower_of_radial_mass_bounds
    {c s inside outside value leakage : ℝ}
    (hc : 0 < c) (hs0 : 0 < s)
    (hout : 1 / (32 * c ^ (2 : ℕ)) ≤ outside)
    (hvalue : 1 / 2 ≤ value ^ (2 : ℕ)) (hleakage : 0 ≤ leakage)
    (hinside : inside ≤
      4 * Real.exp 1 * (c / Real.sqrt s) * Real.exp (2 * c * (1 - s)))
    (hmass : outside = inside * leakage / value ^ (2 : ℕ)) :
    (Real.sqrt s / (256 * Real.exp 1 * c ^ (3 : ℕ))) *
        Real.exp (-(2 * c * (1 - s))) ≤ leakage := by
  let U : ℝ := 4 * Real.exp 1 * (c / Real.sqrt s) * Real.exp (2 * c * (1 - s))
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hv : 0 < value ^ (2 : ℕ) := lt_of_lt_of_le (by norm_num) hvalue
  have hv0 : value ≠ 0 := by
    intro h
    subst value
    norm_num at hvalue
  have heq : outside * value ^ (2 : ℕ) = inside * leakage := by
    rw [hmass]
    field_simp [hv0]
  have hbase : 1 / (64 * c ^ (2 : ℕ)) ≤ outside * value ^ (2 : ℕ) := by
    have hout0 : 0 ≤ outside :=
      (by positivity : 0 ≤ 1 / (32 * c ^ (2 : ℕ))).trans hout
    have hmul := mul_le_mul hout hvalue (by norm_num : (0 : ℝ) ≤ 1 / 2) hout0
    calc
      1 / (64 * c ^ (2 : ℕ)) = (1 / (32 * c ^ (2 : ℕ))) * (1 / 2) := by
        field_simp [hc.ne']
        ring
      _ ≤ outside * value ^ (2 : ℕ) := hmul
  have hscaled : inside * leakage ≤ U * leakage :=
    mul_le_mul_of_nonneg_right hinside hleakage
  have hU : 0 < U := by
    dsimp only [U]
    positivity
  have hratio : (1 / (64 * c ^ (2 : ℕ))) / U ≤ leakage :=
    (div_le_iff₀ hU).2 (hbase.trans (heq.le.trans (by
      simpa only [mul_comm] using hscaled)))
  have hid : (1 / (64 * c ^ (2 : ℕ))) / U =
      (Real.sqrt s / (256 * Real.exp 1 * c ^ (3 : ℕ))) *
        Real.exp (-(2 * c * (1 - s))) := by
    dsimp only [U]
    rw [Real.exp_neg]
    field_simp [hc.ne', hr.ne', (Real.exp_pos (2 * c * (1 - s))).ne']
    ring
  rw [← hid]
  exact hratio

/-- Scalar high-separation extraction.  A bounded aperture mass and the endpoint collar force a
polynomial leakage floor. -/
theorem leakage_lower_of_high_separation_mass_bounds
    {c inside outside value leakage : ℝ}
    (hc : 0 < c)
    (hout : 1 / (8 * c ^ (2 : ℕ)) ≤ outside)
    (hvalue : 1 / 2 ≤ value ^ (2 : ℕ)) (hleakage : 0 ≤ leakage)
    (hinside : inside ≤ 2)
    (hmass : outside = inside * leakage / value ^ (2 : ℕ)) :
    1 / (32 * c ^ (2 : ℕ)) ≤ leakage := by
  have hv : 0 < value ^ (2 : ℕ) := lt_of_lt_of_le (by norm_num) hvalue
  have hv0 : value ≠ 0 := by
    intro h
    subst value
    norm_num at hvalue
  have heq : outside * value ^ (2 : ℕ) = inside * leakage := by
    rw [hmass]
    field_simp [hv0]
  have hbase : 1 / (16 * c ^ (2 : ℕ)) ≤ outside * value ^ (2 : ℕ) := by
    have hout0 : 0 ≤ outside :=
      (by positivity : 0 ≤ 1 / (8 * c ^ (2 : ℕ))).trans hout
    have hmul := mul_le_mul hout hvalue (by norm_num : (0 : ℝ) ≤ 1 / 2) hout0
    calc
      1 / (16 * c ^ (2 : ℕ)) = (1 / (8 * c ^ (2 : ℕ))) * (1 / 2) := by
        field_simp [hc.ne']
        ring
      _ ≤ outside * value ^ (2 : ℕ) := hmul
  have hscaled : inside * leakage ≤ 2 * leakage :=
    mul_le_mul_of_nonneg_right hinside hleakage
  have htwice : 1 / (16 * c ^ (2 : ℕ)) ≤ 2 * leakage :=
    hbase.trans (heq.le.trans hscaled)
  rw [div_le_iff₀ (by positivity : 0 < 16 * c ^ (2 : ℕ))] at htwice
  rw [div_le_iff₀ (by positivity : 0 < 32 * c ^ (2 : ℕ))]
  nlinarith

/-- A fixed positive separation threshold turns the clock-preserving radial lower bound into the
strict Gaussian clock gain required by the separation principle. -/
theorem eventually_exp_clock_gain_le_radial_polynomial_lower
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℝ in Filter.atTop,
      Real.exp (-((4 * Real.pi - 2 * Real.pi * ε) * a ^ (2 : ℕ))) ≤
        (Real.sqrt ε /
          (256 * Real.exp 1 * (2 * Real.pi * a ^ (2 : ℕ)) ^ (3 : ℕ))) *
          Real.exp (-(2 * (2 * Real.pi * a ^ (2 : ℕ)) * (1 - ε))) := by
  let C : ℝ := 256 * Real.exp 1 * (2 * Real.pi) ^ (3 : ℕ) / Real.sqrt ε
  have hgain : 0 < 2 * Real.pi * ε := by positivity
  have hclock := eventually_const_mul_pow_mul_exp_neg_lt_exp_clock_gain
    C (2 * Real.pi * ε) 6 (δ := 2 * Real.pi * ε) hgain
  filter_upwards [hclock, Filter.eventually_gt_atTop (0 : ℝ)] with a ha ha0
  have hfac : C * a ^ (6 : ℕ) * Real.exp (-((2 * Real.pi * ε) * a ^ (2 : ℕ))) ≤ 1 := by
    have hone : Real.exp (-(((2 * Real.pi * ε) - (2 * Real.pi * ε)) * a ^ (2 : ℕ))) = 1 := by
      ring_nf
      simp
    rw [hone] at ha
    exact ha.le
  let K : ℝ :=
    256 * Real.exp 1 * (2 * Real.pi * a ^ (2 : ℕ)) ^ (3 : ℕ) / Real.sqrt ε
  let L : ℝ :=
    (Real.sqrt ε / (256 * Real.exp 1 * (2 * Real.pi * a ^ (2 : ℕ)) ^ (3 : ℕ))) *
      Real.exp (-(2 * (2 * Real.pi * a ^ (2 : ℕ)) * (1 - ε)))
  have hsqrt : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hK : K = C * a ^ (6 : ℕ) := by
    dsimp only [K, C]
    field_simp [hsqrt.ne', Real.pi_ne_zero]
  let P : ℝ := Real.sqrt ε /
    (256 * Real.exp 1 * (2 * Real.pi * a ^ (2 : ℕ)) ^ (3 : ℕ))
  let E₀ : ℝ := Real.exp (-(2 * (2 * Real.pi * a ^ (2 : ℕ)) * (1 - ε)))
  let E₁ : ℝ := Real.exp (-((2 * Real.pi * ε) * a ^ (2 : ℕ)))
  have hcoef : P * K = 1 := by
    dsimp only [P, K]
    field_simp [hsqrt.ne', Real.pi_ne_zero, ha0.ne']
  have hexp : E₀ * E₁ =
      Real.exp (-((4 * Real.pi - 2 * Real.pi * ε) * a ^ (2 : ℕ))) := by
    dsimp only [E₀, E₁]
    rw [← Real.exp_add]
    congr 1
    ring
  have hdecompRev : L * (K * E₁) =
      Real.exp (-((4 * Real.pi - 2 * Real.pi * ε) * a ^ (2 : ℕ))) := by
    change (P * E₀) * (K * E₁) = _
    calc
      (P * E₀) * (K * E₁) = (P * K) * (E₀ * E₁) := by ring
      _ = Real.exp (-((4 * Real.pi - 2 * Real.pi * ε) * a ^ (2 : ℕ))) := by
        rw [hcoef, hexp, one_mul]
  have hdecomp := hdecompRev.symm
  have hL0 : 0 ≤ L := by
    dsimp only [L]
    positivity
  rw [hdecomp]
  have hfac' : K * E₁ ≤ 1 := by
    rw [hK]
    dsimp only [E₁]
    exact hfac
  change L * (K * E₁) ≤ L
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hfac' hL0

/-- The same strict Gaussian clock is eventually below the polynomial high-separation leakage
floor. -/
theorem eventually_exp_clock_gain_le_one_div_radial_sq
    {ε : ℝ} (_hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ a : ℝ in Filter.atTop,
      Real.exp (-((4 * Real.pi - 2 * Real.pi * ε) * a ^ (2 : ℕ))) ≤
        1 / (32 * (2 * Real.pi * a ^ (2 : ℕ)) ^ (2 : ℕ)) := by
  let α : ℝ := 4 * Real.pi - 2 * Real.pi * ε
  have hα : 0 < α := by
    dsimp only [α]
    have hpi := Real.pi_pos
    nlinarith
  have hsmall := eventually_const_mul_pow_mul_exp_neg_lt_exp_clock_gain
    (32 * (2 * Real.pi) ^ (2 : ℕ)) α 4 hα
  filter_upwards [hsmall, Filter.eventually_gt_atTop (0 : ℝ)] with a ha ha0
  have hden : 0 < 32 * (2 * Real.pi * a ^ (2 : ℕ)) ^ (2 : ℕ) := by positivity
  rw [show α - α = 0 by ring, zero_mul, neg_zero, Real.exp_zero] at ha
  rw [le_div_iff₀ hden]
  have heq :
      Real.exp (-(α * a ^ (2 : ℕ))) * (32 * (2 * Real.pi * a ^ (2 : ℕ)) ^ (2 : ℕ)) =
        32 * (2 * Real.pi) ^ (2 : ℕ) * a ^ (4 : ℕ) * Real.exp (-(α * a ^ (2 : ℕ))) := by ring
  rw [show 4 * Real.pi - 2 * Real.pi * ε = α by rfl, heq]
  exact ha.le

end GaloisForLFunctions.RHTower

end
