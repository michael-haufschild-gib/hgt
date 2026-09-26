import GaloisForLFunctions.RHTower.XiZeroFreeRegionDiscSeamContraction
import GaloisForLFunctions.RHTower.Sieve.InghamDetectorDensity

/-!
# The adjoint seam contracts on almost every right disc

Let `D_n` be the closed disc of radius `1/10` centred at `17/20 + i n`.  Every `D_n` lies in the
strip `3/4 ≤ Re s ≤ 19/20`, strictly right of the critical line.  When `xi` has no zero in `D_n`, the
adjoint Hankel seam of the `xi` boundary phase on `D_n` is a strict contraction
(`xiDisc_adjointSeam_lt_one_of_ne_zero`).

`card_badDensityDiscs_le` bounds the exceptional discs by the corpus zero-density estimate
(`Sieve.exists_eventually_zetaLittlewoodZeroCountAbove_sevenTenths_le_routeTExponent`).  The number
of `n ≤ X` for which `D_n` contains a zero of `xi` is at most `K (X + 3)^θ`, with the density
exponent `θ < 7/10`.  So the seam contraction of the Riemann-hypothesis criterion
`riemannHypothesis_iff_forall_xiRightDisc_adjointSeam_lt_one` holds unconditionally for all but
`O(X^{7/10})` of the first `X` discs.  Distinct discs are separated by more than their diameter, so
each zero lies in at most one of them.
-/

noncomputable section

open Complex Metric Filter

namespace RHTower

/-- The centre `17/20 + i n` of the `n`-th comparison disc. -/
def densityDiscCenter (n : ℕ) : ℂ := ((17 / 20 : ℝ) : ℂ) + ((n : ℝ) : ℂ) * I

theorem densityDiscCenter_re (n : ℕ) : (densityDiscCenter n).re = 17 / 20 := by
  simp [densityDiscCenter]

theorem densityDiscCenter_im (n : ℕ) : (densityDiscCenter n).im = n := by
  simp [densityDiscCenter]

/-- The exceptional heights `n ≤ X`: those whose disc contains a zero of `xi`. -/
def badDensityDiscs (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter
    (fun n => ∃ z ∈ closedBall (densityDiscCenter n) (1 / 10), xi z = 0)

theorem mem_badDensityDiscs {X n : ℕ} :
    n ∈ badDensityDiscs X ↔
      n ∈ Finset.Icc 1 X ∧ ∃ z ∈ closedBall (densityDiscCenter n) (1 / 10), xi z = 0 := by
  classical
  unfold badDensityDiscs
  rw [Finset.mem_filter]

theorem re_im_of_mem_densityDisc {n : ℕ} {z : ℂ}
    (hz : z ∈ closedBall (densityDiscCenter n) (1 / 10)) :
    3 / 4 ≤ z.re ∧ z.re ≤ 19 / 20 ∧ (n : ℝ) - 1 / 10 ≤ z.im ∧ z.im ≤ (n : ℝ) + 1 / 10 := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have h1 : |(z - densityDiscCenter n).re| ≤ ‖z - densityDiscCenter n‖ :=
    Complex.abs_re_le_norm _
  have h2 : |(z - densityDiscCenter n).im| ≤ ‖z - densityDiscCenter n‖ :=
    Complex.abs_im_le_norm _
  rw [Complex.sub_re, densityDiscCenter_re] at h1
  rw [Complex.sub_im, densityDiscCenter_im] at h2
  have a1 := abs_le.mp (le_trans h1 hz)
  have a2 := abs_le.mp (le_trans h2 hz)
  refine ⟨by linarith [a1.1], by linarith [a1.2], by linarith [a2.1], by linarith [a2.2]⟩

/-- Off the exceptional set the seam contracts. -/
theorem densityDisc_adjointSeam_lt_one {n : ℕ}
    (hn : ∀ z ∈ closedBall (densityDiscCenter n) (1 / 10), xi z ≠ 0) :
    ∃ hne : ∀ ζ ∈ sphere (densityDiscCenter n) (1 / 10), xi ζ ≠ 0,
      ‖(xiDiscDatum (densityDiscCenter n) (1 / 10) (by norm_num)
        hne).circlePhase.datum.adjointHankelSeam‖ < 1 :=
  ⟨fun ζ hζ => hn ζ (sphere_subset_closedBall hζ),
    xiDisc_adjointSeam_lt_one_of_ne_zero _ _ _ _ hn⟩

/-- The comparison discs lie strictly right of the critical line. -/
theorem densityDisc_right {n : ℕ} :
    ∀ z ∈ closedBall (densityDiscCenter n) (1 / 10), 1 / 2 < z.re := fun z hz => by
  have := (re_im_of_mem_densityDisc hz).1
  linarith

/-- **Few exceptional discs.**  With the zero-density exponent `θ < 7/10`, eventually at most
`K (X + 3)^θ` of the first `X` comparison discs contain a zero of `xi`. -/
theorem card_badDensityDiscs_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ X : ℕ in atTop,
      ((badDensityDiscs X).card : ℝ) ≤
        K * ((X + 3 : ℕ) : ℝ) ^ Sieve.inghamFixedGabrielRouteTExponent := by
  classical
  obtain ⟨K, hK, hev⟩ := Sieve.exists_eventually_zetaLittlewoodZeroCountAbove_sevenTenths_le_routeTExponent
  refine ⟨K, hK, ?_⟩
  filter_upwards [(tendsto_add_atTop_nat 3).eventually hev] with X hX
  set T : ℝ := ((X + 3 : ℕ) : ℝ) - 2 with hT
  have hTX : T = (X : ℝ) + 1 := by rw [hT]; push_cast; ring
  set Zall := Sieve.zetaResidueUnitClosedRectangleZeros
    ((Sieve.inghamFixedGabrielSigma : ℂ) + ((-T : ℝ) : ℂ) * I) ((4 : ℝ) + (T : ℂ) * I) with hZall
  set Z := Zall.filter (fun w => (7 / 10 : ℝ) ≤ w.re) with hZ
  -- choose a zero in each exceptional disc
  have hchoose : ∀ n ∈ badDensityDiscs X,
      ∃ z ∈ closedBall (densityDiscCenter n) (1 / 10), xi z = 0 :=
    fun n hn => (mem_badDensityDiscs.mp hn).2
  choose! w hwball hwzero using hchoose
  have hmaps : ∀ n ∈ badDensityDiscs X, w n ∈ Z := by
    intro n hn
    have hnI := (mem_badDensityDiscs.mp hn).1
    rw [Finset.mem_Icc] at hnI
    obtain ⟨hr1, hr2, hi1, hi2⟩ := re_im_of_mem_densityDisc (hwball n hn)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnI.1
    have hnX : (n : ℝ) ≤ X := by exact_mod_cast hnI.2
    have hre0 : 0 < (w n).re := by linarith
    have hne1 : w n ≠ 1 := by
      intro h; rw [h, Complex.one_re] at hr2; linarith
    have hzeta : riemannZeta (w n) = 0 := (xi_eq_zero_iff hre0 hne1).mp (hwzero n hn)
    have hunit : zetaResidueUnit (w n) = 0 := by
      rw [zetaResidueUnit, Function.update_of_ne hne1, hzeta, mul_zero]
    rw [hZ, Finset.mem_filter, hZall, Sieve.mem_zetaResidueUnitClosedRectangleZeros]
    refine ⟨⟨?_, hunit⟩, by linarith⟩
    rw [Complex.mem_reProdIm]
    have hsig : Sieve.inghamFixedGabrielSigma = 699 / 1000 := rfl
    constructor
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
      rw [Set.uIcc_of_le (by rw [hsig]; norm_num)]
      exact ⟨by rw [hsig]; linarith, by linarith⟩
    · simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, zero_add, add_zero]
      rw [Set.uIcc_of_le (by rw [hTX]; linarith)]
      exact ⟨by rw [hTX]; linarith, by rw [hTX]; linarith⟩
  have hinj : Set.InjOn w (badDensityDiscs X : Set ℕ) := by
    intro n hn m hm hnm
    obtain ⟨-, -, hn1, hn2⟩ := re_im_of_mem_densityDisc (hwball n hn)
    obtain ⟨-, -, hm1, hm2⟩ := re_im_of_mem_densityDisc (hwball m hm)
    rw [hnm] at hn1 hn2
    have h1 : ((n : ℝ) - m) < 1 := by linarith
    have h2 : ((m : ℝ) - n) < 1 := by linarith
    have h3 : (n : ℤ) - m < 1 := by exact_mod_cast h1
    have h4 : (m : ℤ) - n < 1 := by exact_mod_cast h2
    omega
  have hcard : (badDensityDiscs X).card ≤ Z.card :=
    Finset.card_le_card_of_injOn w hmaps hinj
  have hsum : (Z.card : ℝ) ≤ Sieve.zetaLittlewoodZeroCountAbove Sieve.inghamFixedGabrielSigma 4
      T (7 / 10) := by
    unfold Sieve.zetaLittlewoodZeroCountAbove
    rw [← hZall, ← hZ, Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun v hv => ?_
    rw [hZ, Finset.mem_filter, hZall, Sieve.mem_zetaResidueUnitClosedRectangleZeros] at hv
    have hv0 : zetaResidueUnit v = 0 := hv.1.2
    have hord0 : analyticOrderAt zetaResidueUnit v ≠ 0 := by
      rw [ne_eq, (analyticAt_zetaResidueUnit v).analyticOrderAt_eq_zero]
      exact fun h => h hv0
    have hordtop := Sieve.zetaResidueUnit_order_ne_top v
    have h1 : 1 ≤ (analyticOrderAt zetaResidueUnit v).toNat := by
      rw [Nat.one_le_iff_ne_zero, ne_eq, ENat.toNat_eq_zero]
      push Not
      exact ⟨hord0, hordtop⟩
    push_cast
    exact_mod_cast h1
  calc ((badDensityDiscs X).card : ℝ) ≤ Z.card := by exact_mod_cast hcard
    _ ≤ _ := hsum
    _ ≤ _ := hX

end RHTower
