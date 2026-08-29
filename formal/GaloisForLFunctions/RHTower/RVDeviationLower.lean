import GaloisForLFunctions.RHTower.SteinhausThreeWaySplit
import GaloisForLFunctions.RHTower.RVSteinhausModel
import GaloisForLFunctions.RHTower.SteinhausCumulantDeriv

/-!
# The large-deviation lower bound

The card's `(5)`, lower half.  The three-way split is instantiated at three tilts
`λ' < λ < λ''` whose cumulant derivatives are `q + δ/4`, `q + δ/2`, `q + 3δ/4`; strict convexity
turns those into the two chord conditions, so both outer pieces are exponentially smaller than the
whole and the band retains at least half the mass.
-/

open MeasureTheory Filter Topology HTGeometry

namespace RHTower

local instance phaseCirclePositiveLower : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable section

/-- The prime average of the tilted cumulant, as an exponent of the Laplace product. -/
theorem prod_steinhausLaplace_eq_exp {α : ℝ} {L : ℝ → ℝ} {lam X : ℝ} :
    ∏ i : ↥(rvPrimeFinset X),
        steinhausLaplace (lam * rvPrimeCount X * rvWeightFun α L X i)
      = Real.exp (primeCountSum
          (fun t => steinhausLogLaplace (lam * rvNormReal α L X t)) 0 X) := by
  rw [← sum_steinhausLogLaplace_rvWeightFun (α := α) (L := L) (lam := lam) (X := X),
    Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [steinhausLogLaplace, Real.exp_log (steinhausLaplace_pos _)]

/-- **The band bound for the model.** -/
theorem le_rvDeviationProb {α : ℝ} {L : ℝ → ℝ} {lamL lam lamU X q δ : ℝ}
    (hsl : lamL ≤ lam) (hlu : lam ≤ lamU) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ) :
    Real.exp (-(lam * rvPrimeCount X * (q + δ)))
        * (Real.exp (primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t)) 0 X)
          - Real.exp ((lam - lamL) * rvPrimeCount X * q)
            * Real.exp (primeCountSum
              (fun t => steinhausLogLaplace (lamL * rvNormReal α L X t)) 0 X)
          - Real.exp ((lam - lamU) * rvPrimeCount X * (q + δ))
            * Real.exp (primeCountSum
              (fun t => steinhausLogLaplace (lamU * rvNormReal α L X t)) 0 X))
      ≤ rvDeviationProb α L X q := by
  have hd0 : (0 : ℝ) ≤ rvPrimeCount X := Nat.cast_nonneg _
  have hst : lamL * rvPrimeCount X ≤ lam * rvPrimeCount X :=
    mul_le_mul_of_nonneg_right hsl hd0
  have htu : lam * rvPrimeCount X ≤ lamU * rvPrimeCount X :=
    mul_le_mul_of_nonneg_right hlu hd0
  have ht : (0 : ℝ) ≤ lam * rvPrimeCount X := mul_nonneg hlam hd0
  have hband := le_meas_band (rvWeightFun α L X) (q := q) (δ := δ) hst htu ht hδ
  have hnorm := meas_proj_le_meas_norm (rvWeightFun α L X) q
  have htoReal := ENNReal.toReal_le_toReal
    (measure_ne_top (Measure.pi fun _ : ↥(rvPrimeFinset X) => AddCircle.haarAddCircle) _)
    (measure_ne_top (Measure.pi fun _ : ↥(rvPrimeFinset X) => AddCircle.haarAddCircle) _) |>.2
    hnorm
  have hchain : Real.exp (-(lam * rvPrimeCount X * (q + δ)))
      * ((∏ i : ↥(rvPrimeFinset X),
            steinhausLaplace (lam * rvPrimeCount X * rvWeightFun α L X i))
        - Real.exp ((lam * rvPrimeCount X - lamL * rvPrimeCount X) * q)
          * ∏ i : ↥(rvPrimeFinset X),
              steinhausLaplace (lamL * rvPrimeCount X * rvWeightFun α L X i)
        - Real.exp ((lam * rvPrimeCount X - lamU * rvPrimeCount X) * (q + δ))
          * ∏ i : ↥(rvPrimeFinset X),
              steinhausLaplace (lamU * rvPrimeCount X * rvWeightFun α L X i))
      ≤ rvDeviationProb α L X q := by
    rw [rvDeviationProb]
    exact le_trans hband htoReal
  have hs1 : (lam * rvPrimeCount X - lamL * rvPrimeCount X) * q
      = (lam - lamL) * rvPrimeCount X * q := by ring
  have hs2 : (lam * rvPrimeCount X - lamU * rvPrimeCount X) * (q + δ)
      = (lam - lamU) * rvPrimeCount X * (q + δ) := by ring
  rw [hs1, hs2, prod_steinhausLaplace_eq_exp, prod_steinhausLaplace_eq_exp,
    prod_steinhausLaplace_eq_exp] at hchain
  exact hchain


/-- **The large-deviation lower bound**, the lower half of the card's `(5)`. -/
theorem eventually_le_log_rvDeviationProb {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : ℝ → ℝ}
    (hL : IsSlowlyVarying L) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in atTop,
      -(rvRate α q) - ε ≤ Real.log (rvDeviationProb α L X q) / rvPrimeCount X := by
  -- the reference tilt
  set δ₀ : ℝ := (1 - q) / 2 with hδ₀def
  have hδ₀ : 0 < δ₀ := by rw [hδ₀def]; linarith
  obtain ⟨lam₀, hlam₀0, hlam₀⟩ := exists_rvCumulantDeriv_eq (α := α) hα1
    (q := q + δ₀ / 2) (by linarith) (by rw [hδ₀def]; linarith)
  set δ : ℝ := min δ₀ (ε / (2 * (lam₀ + 1))) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀ (by positivity)
  have hδle : δ ≤ δ₀ := min_le_left _ _
  have hδeps : δ ≤ ε / (2 * (lam₀ + 1)) := min_le_right _ _
  have hq34 : q + 3 * δ / 4 < 1 := by
    have : δ ≤ (1 - q) / 2 := le_trans hδle (le_of_eq hδ₀def)
    linarith
  obtain ⟨lamL, hlamL0, hlamL⟩ := exists_rvCumulantDeriv_eq (α := α) hα1
    (q := q + δ / 4) (by linarith) (by linarith)
  obtain ⟨lam, hlam0, hlamv⟩ := exists_rvCumulantDeriv_eq (α := α) hα1
    (q := q + δ / 2) (by linarith) (by linarith)
  obtain ⟨lamU, hlamU0, hlamU⟩ := exists_rvCumulantDeriv_eq (α := α) hα1
    (q := q + 3 * δ / 4) (by linarith) (by linarith)
  have hmono := strictMono_rvCumulantDeriv (α := α) hα1
  have hLlt : lamL < lam := by
    by_contra hcon
    rw [not_lt] at hcon
    have := hmono.le_iff_le.2 hcon
    rw [hlamL, hlamv] at this
    linarith
  have hltU : lam < lamU := by
    by_contra hcon
    rw [not_lt] at hcon
    have := hmono.le_iff_le.2 hcon
    rw [hlamU, hlamv] at this
    linarith
  have hlamle : lam ≤ lam₀ := by
    by_contra hcon
    rw [not_le] at hcon
    have hstrict := hmono hcon
    rw [hlam₀, hlamv] at hstrict
    linarith [hδle]
  -- the two chord conditions
  have hconv := strictConvexOn_rvCumulant (α := α) hα1
  have hchordL : (lam - lamL) * q + rvCumulant α lamL - rvCumulant α lam < 0 := by
    have hslope := hconv.deriv_lt_slope (Set.mem_univ lamL) (Set.mem_univ lam) hLlt
      ((differentiable_rvCumulant hα1) lamL)
    rw [deriv_rvCumulant hα1, hlamL, slope_def_field] at hslope
    have hpos : 0 < lam - lamL := by linarith
    rw [lt_div_iff₀ hpos] at hslope
    nlinarith only [hslope, hδpos, hpos]
  have hchordU : (lam - lamU) * (q + δ) + rvCumulant α lamU - rvCumulant α lam < 0 := by
    have hslope := hconv.slope_lt_deriv (Set.mem_univ lam) (Set.mem_univ lamU) hltU
      ((differentiable_rvCumulant hα1) lamU)
    rw [deriv_rvCumulant hα1, hlamU, slope_def_field] at hslope
    have hpos : 0 < lamU - lam := by linarith
    rw [div_lt_iff₀ hpos] at hslope
    nlinarith only [hslope, hδpos, hpos]
  set E₁ : ℝ := (lam - lamL) * q + rvCumulant α lamL - rvCumulant α lam with hE₁
  set E₂ : ℝ := (lam - lamU) * (q + δ) + rvCumulant α lamU - rvCumulant α lam with hE₂
  -- the value at the chosen tilt
  have hvalue : -(lam * (q + δ)) + rvCumulant α lam ≥ -(rvRate α q) - ε / 2 := by
    have hle := le_rvRate hα1 hq1 hlam0.le
    have hδbound : lam * δ ≤ ε / 2 := by
      have h1 : lam * δ ≤ lam₀ * δ := mul_le_mul_of_nonneg_right hlamle hδpos.le
      have h2 : lam₀ * (ε / (2 * (lam₀ + 1))) ≤ ε / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith only [hlam₀0, hε]
      have h3 : lam₀ * δ ≤ lam₀ * (ε / (2 * (lam₀ + 1))) :=
        mul_le_mul_of_nonneg_left hδeps hlam₀0.le
      linarith
    nlinarith only [hle, hδbound]
  -- eventual control
  have hE₁neg : E₁ < 0 := hchordL
  have hE₂neg : E₂ < 0 := hchordU
  set η : ℝ := min (ε / 8) (min (-E₁) (-E₂) / 8) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by
    have : 0 < min (-E₁) (-E₂) := lt_min (by linarith) (by linarith)
    linarith)
  have hηε : η ≤ ε / 8 := min_le_left _ _
  have hηE : η ≤ min (-E₁) (-E₂) / 8 := min_le_right _ _
  have hcumL := (tendsto_rvCumulantAverage hα0 hα1 hL hlamL0.le).eventually
    (eventually_lt_nhds (show rvCumulant α lamL < rvCumulant α lamL + η by linarith))
  have hcumM := (tendsto_rvCumulantAverage hα0 hα1 hL hlam0.le).eventually
    (eventually_gt_nhds (show rvCumulant α lam - η < rvCumulant α lam by linarith))
  have hcumU := (tendsto_rvCumulantAverage hα0 hα1 hL hlamU0.le).eventually
    (eventually_lt_nhds (show rvCumulant α lamU < rvCumulant α lamU + η by linarith))
  have hexp1 : ∀ᶠ X in atTop, Real.exp (rvPrimeCount X * (E₁ / 2)) ≤ 1 / 4 := by
    have hlim : Tendsto (fun X : ℝ => Real.exp (rvPrimeCount X * (E₁ / 2))) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      have hneg : E₁ / 2 < 0 := by linarith
      simpa [mul_comm] using tendsto_rvPrimeCount_atTop.atTop_mul_const_of_neg hneg
    exact hlim.eventually_le_const (by norm_num)
  have hexp2 : ∀ᶠ X in atTop, Real.exp (rvPrimeCount X * (E₂ / 2)) ≤ 1 / 4 := by
    have hlim : Tendsto (fun X : ℝ => Real.exp (rvPrimeCount X * (E₂ / 2))) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      have hneg : E₂ / 2 < 0 := by linarith
      simpa [mul_comm] using tendsto_rvPrimeCount_atTop.atTop_mul_const_of_neg hneg
    exact hlim.eventually_le_const (by norm_num)
  have hlog2 : ∀ᶠ X in atTop, Real.log 2 / rvPrimeCount X ≤ 3 * ε / 8 := by
    have hlim : Tendsto (fun X : ℝ => Real.log 2 / rvPrimeCount X) atTop (𝓝 0) :=
      tendsto_rvPrimeCount_atTop.const_div_atTop _
    exact hlim.eventually_le_const (by linarith)
  have hWpos : ∀ᶠ X in atTop, rvWeightSum α L X ≠ 0 := by
    have hα' : (0 : ℝ) < 1 - α := by linarith
    have hlim := (tendsto_rvWeightSum hα0 hα1 hL).eventually_const_lt
      (show (0 : ℝ) < 1 / (1 - α) by positivity)
    filter_upwards [hlim, eventually_gt_atTop (1 : ℝ)] with X hX hX1
    have hX0 : (0 : ℝ) < X := lt_trans one_pos hX1
    have hLX : 0 < L X := hL.pos _ hX0
    have hXpow : (0 : ℝ) < X ^ (1 - α) := Real.rpow_pos_of_pos hX0 _
    have hden : (0 : ℝ) < X ^ (1 - α) * L X := mul_pos hXpow hLX
    rw [lt_div_iff₀ hden, zero_mul] at hX
    exact hX.ne'
  filter_upwards [hcumL, hcumM, hcumU, hexp1, hexp2, hlog2, hWpos,
    tendsto_rvPrimeCount_atTop.eventually_gt_atTop 0] with
    X hXL hXM hXU hX1 hX2 hXlog hXW hXd
  set d : ℝ := rvPrimeCount X with hd
  set A : ℝ := primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t)) 0 X with hA
  set A' : ℝ := primeCountSum (fun t => steinhausLogLaplace (lamL * rvNormReal α L X t)) 0 X
    with hA'
  set A'' : ℝ := primeCountSum (fun t => steinhausLogLaplace (lamU * rvNormReal α L X t)) 0 X
    with hA''
  have hAvg : rvCumulantAverage α L lam X = A / d := rfl
  have hAvgL : rvCumulantAverage α L lamL X = A' / d := rfl
  have hAvgU : rvCumulantAverage α L lamU X = A'' / d := rfl
  rw [hAvg] at hXM
  rw [hAvgL] at hXL
  rw [hAvgU] at hXU
  rw [div_lt_iff₀ hXd] at hXL hXU
  rw [lt_div_iff₀ hXd] at hXM
  -- the two outer terms
  have hu₁ : (lam - lamL) * d * q + A' - A ≤ d * (E₁ / 2) := by
    have hmin : min (-E₁) (-E₂) ≤ -E₁ := min_le_left _ _
    have hηb : η ≤ (-E₁) / 8 := by linarith [hηE, hmin]
    have hkey : A' - A ≤ d * (rvCumulant α lamL - rvCumulant α lam) + 2 * (d * η) := by
      nlinarith only [hXL, hXM, hXd]
    have hE : (lam - lamL) * d * q = d * ((lam - lamL) * q) := by ring
    rw [hE]
    have hcomb : d * ((lam - lamL) * q) + (d * (rvCumulant α lamL - rvCumulant α lam)
        + 2 * (d * η)) = d * (E₁ + 2 * η) := by rw [hE₁]; ring
    have hfinal : d * (E₁ + 2 * η) ≤ d * (E₁ / 2) := by
      refine mul_le_mul_of_nonneg_left ?_ hXd.le
      linarith [hηb]
    linarith [hkey, hcomb.le, hcomb.ge, hfinal]
  have hu₂ : (lam - lamU) * d * (q + δ) + A'' - A ≤ d * (E₂ / 2) := by
    have hmin : min (-E₁) (-E₂) ≤ -E₂ := min_le_right _ _
    have hηb : η ≤ (-E₂) / 8 := by linarith [hηE, hmin]
    have hkey : A'' - A ≤ d * (rvCumulant α lamU - rvCumulant α lam) + 2 * (d * η) := by
      nlinarith only [hXU, hXM, hXd]
    have hE : (lam - lamU) * d * (q + δ) = d * ((lam - lamU) * (q + δ)) := by ring
    rw [hE]
    have hcomb : d * ((lam - lamU) * (q + δ)) + (d * (rvCumulant α lamU - rvCumulant α lam)
        + 2 * (d * η)) = d * (E₂ + 2 * η) := by rw [hE₂]; ring
    have hfinal : d * (E₂ + 2 * η) ≤ d * (E₂ / 2) := by
      refine mul_le_mul_of_nonneg_left ?_ hXd.le
      linarith [hηb]
    linarith [hkey, hcomb.le, hcomb.ge, hfinal]
  -- the band bound
  have hband := le_rvDeviationProb (α := α) (L := L) (lamL := lamL) (lam := lam) (lamU := lamU)
    (X := X) (q := q) (δ := δ) hLlt.le hltU.le hlam0.le hδpos.le
  have hterm1 : Real.exp ((lam - lamL) * d * q) * Real.exp A' ≤ (1 / 4) * Real.exp A := by
    rw [← Real.exp_add]
    have hle : (lam - lamL) * d * q + A' ≤ d * (E₁ / 2) + A := by linarith [hu₁]
    calc Real.exp ((lam - lamL) * d * q + A') ≤ Real.exp (d * (E₁ / 2) + A) :=
          Real.exp_le_exp.2 hle
      _ = Real.exp (d * (E₁ / 2)) * Real.exp A := Real.exp_add _ _
      _ ≤ (1 / 4) * Real.exp A :=
          mul_le_mul_of_nonneg_right hX1 (Real.exp_pos _).le
  have hterm2 : Real.exp ((lam - lamU) * d * (q + δ)) * Real.exp A'' ≤ (1 / 4) * Real.exp A := by
    rw [← Real.exp_add]
    have hle : (lam - lamU) * d * (q + δ) + A'' ≤ d * (E₂ / 2) + A := by linarith [hu₂]
    calc Real.exp ((lam - lamU) * d * (q + δ) + A'') ≤ Real.exp (d * (E₂ / 2) + A) :=
          Real.exp_le_exp.2 hle
      _ = Real.exp (d * (E₂ / 2)) * Real.exp A := Real.exp_add _ _
      _ ≤ (1 / 4) * Real.exp A :=
          mul_le_mul_of_nonneg_right hX2 (Real.exp_pos _).le
  have hlowP : Real.exp (-(lam * d * (q + δ))) * ((1 / 2) * Real.exp A)
      ≤ rvDeviationProb α L X q := by
    refine le_trans ?_ hband
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    linarith [hterm1, hterm2]
  have hPpos : 0 < rvDeviationProb α L X q := rvDeviationProb_pos hq1 hXW
  have hlogP : -(lam * d * (q + δ)) + A - Real.log 2
      ≤ Real.log (rvDeviationProb α L X q) := by
    have hposlow : (0 : ℝ) < Real.exp (-(lam * d * (q + δ))) * ((1 / 2) * Real.exp A) := by
      positivity
    have hlogle := Real.log_le_log hposlow hlowP
    have hid : Real.log (Real.exp (-(lam * d * (q + δ))) * ((1 / 2) * Real.exp A))
        = -(lam * d * (q + δ)) + A - Real.log 2 := by
      rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp,
        Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
      rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.log_inv]
      ring
    linarith [hlogle, hid.le, hid.ge]
  rw [le_div_iff₀ hXd]
  have hAlow : d * (rvCumulant α lam - η) < A := by linarith [hXM]
  have hvalue' : -(lam * (q + δ)) + rvCumulant α lam ≥ -(rvRate α q) - ε / 2 := hvalue
  have hlogd : Real.log 2 ≤ 3 * ε / 8 * d := by
    rw [div_le_iff₀ hXd] at hXlog
    linarith [hXlog]
  have hscale : (-(rvRate α q) - ε) * d ≤ -(lam * d * (q + δ)) + A - Real.log 2 := by
    have hstep : (-(rvRate α q) - ε / 2 - η) * d ≤ (-(lam * (q + δ)) + rvCumulant α lam - η) * d :=
      mul_le_mul_of_nonneg_right (by linarith [hvalue']) hXd.le
    have hid : (-(lam * (q + δ)) + rvCumulant α lam - η) * d
        = -(lam * d * (q + δ)) + d * (rvCumulant α lam - η) := by ring
    have hεη : (-(rvRate α q) - ε) * d + Real.log 2
        ≤ (-(rvRate α q) - ε / 2 - η) * d := by
      have hgap : (-(rvRate α q) - ε / 2 - η) * d - (-(rvRate α q) - ε) * d
          = (ε / 2 - η) * d := by ring
      have hεη2 : 3 * ε / 8 ≤ ε / 2 - η := by linarith [hηε]
      have : 3 * ε / 8 * d ≤ (ε / 2 - η) * d := mul_le_mul_of_nonneg_right hεη2 hXd.le
      linarith [hgap.le, hgap.ge, hlogd]
    linarith [hstep, hid.le, hid.ge, hAlow, hεη]
  linarith [hlogP, hscale]


/-- **The card's `(5)`.**  The event exponent of the regular-variation Steinhaus model. -/
theorem tendsto_log_rvDeviationProb {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : ℝ → ℝ}
    (hL : IsSlowlyVarying L) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (fun X : ℝ => Real.log (rvDeviationProb α L X q) / rvPrimeCount X) atTop
      (𝓝 (-(rvRate α q))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hlow := eventually_le_log_rvDeviationProb hα0 hα1 hL hq0 hq1
    (show (0 : ℝ) < ε / 2 by linarith)
  have hup := eventually_log_rvDeviationProb_le hα0 hα1 hL hq0 hq1
    (show (0 : ℝ) < ε / 2 by linarith)
  filter_upwards [hlow, hup] with X hXlow hXup
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end

end RHTower
