import GaloisForLFunctions.RHTower.XiRightDiscSeamContractionDensity
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorZeroDensityLinearExponent

/-!
# Seam contraction on almost every right disc, uniformly in the abscissa

For `0 < r < 1/2` and an abscissa `σ₀` with `7/10 + r ≤ σ₀` and `σ₀ + r < 1`, let `D_n(σ₀, r)` be
the closed disc of radius `r` centred at `σ₀ + i n`.  On a zero-free disc the adjoint Hankel seam of
the `xi` boundary phase is a strict contraction (`xiDisc_adjointSeam_lt_one_of_ne_zero`).
`card_badUniformDiscs_le` bounds the exceptional heights, with one constant uniform in `σ₀` and
`r`: the number of `n ≤ X` whose disc contains a zero of `xi` is at most
`K (1 + log X)^{14} (1 + X^{(16/5)(1 − σ₀ + r)} (1 + log X)² + (1 + log X)²)`.  This is `o(X)`
because `(16/5)(1 − σ₀ + r) ≤ (16/5)(3/10) < 1`.  The input is the corpus uniform zero-density
estimate `Sieve.exists_eventually_zetaLittlewoodZeroCountAbove_le_linearExponent`.  Discs at
distinct integer heights are separated by more than their diameter, so each zero lies in at most
one of them.
-/

noncomputable section

open Complex Metric Filter

namespace RHTower

/-- The centre `σ₀ + i n`. -/
def uniformDiscCenter (σ₀ : ℝ) (n : ℕ) : ℂ := (σ₀ : ℂ) + ((n : ℝ) : ℂ) * I

/-- Exceptional heights `n ≤ X`: the disc of radius `r` at `σ₀ + i n` contains a zero of `xi`. -/
def badUniformDiscs (σ₀ r : ℝ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter
    (fun n => ∃ z ∈ closedBall (uniformDiscCenter σ₀ n) r, xi z = 0)

theorem mem_badUniformDiscs {σ₀ r : ℝ} {X n : ℕ} :
    n ∈ badUniformDiscs σ₀ r X ↔
      n ∈ Finset.Icc 1 X ∧ ∃ z ∈ closedBall (uniformDiscCenter σ₀ n) r, xi z = 0 := by
  classical
  unfold badUniformDiscs
  rw [Finset.mem_filter]

theorem re_im_of_mem_uniformDisc {σ₀ r : ℝ} {n : ℕ} {z : ℂ}
    (hz : z ∈ closedBall (uniformDiscCenter σ₀ n) r) :
    σ₀ - r ≤ z.re ∧ z.re ≤ σ₀ + r ∧ (n : ℝ) - r ≤ z.im ∧ z.im ≤ (n : ℝ) + r := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have h1 : |(z - uniformDiscCenter σ₀ n).re| ≤ ‖z - uniformDiscCenter σ₀ n‖ :=
    Complex.abs_re_le_norm _
  have h2 : |(z - uniformDiscCenter σ₀ n).im| ≤ ‖z - uniformDiscCenter σ₀ n‖ :=
    Complex.abs_im_le_norm _
  have hre : (uniformDiscCenter σ₀ n).re = σ₀ := by simp [uniformDiscCenter]
  have him : (uniformDiscCenter σ₀ n).im = n := by simp [uniformDiscCenter]
  rw [Complex.sub_re, hre] at h1
  rw [Complex.sub_im, him] at h2
  have a1 := abs_le.mp (le_trans h1 hz)
  have a2 := abs_le.mp (le_trans h2 hz)
  exact ⟨by linarith [a1.1], by linarith [a1.2], by linarith [a2.1], by linarith [a2.2]⟩

/-- **Uniform density of exceptional discs.** -/
theorem card_badUniformDiscs_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ X : ℕ in atTop, ∀ {σ₀ r : ℝ}, 0 < r → r < 1 / 2 →
      7 / 10 + r ≤ σ₀ → σ₀ + r < 1 →
      ((badUniformDiscs σ₀ r X).card : ℝ) ≤
        K * (1 + Real.log ((X + 3 : ℕ) : ℝ)) ^ (14 : ℕ) *
          (1 + ((X + 3 : ℕ) : ℝ) ^ ((16 / 5 : ℝ) * (1 - (σ₀ - r))) *
              (1 + Real.log ((X + 3 : ℕ) : ℝ)) ^ (2 : ℕ) +
            (1 + Real.log ((X + 3 : ℕ) : ℝ)) ^ (2 : ℕ)) := by
  classical
  obtain ⟨K, hK, hev⟩ := Sieve.exists_eventually_zetaLittlewoodZeroCountAbove_le_linearExponent
  refine ⟨K, hK, ?_⟩
  filter_upwards [(tendsto_add_atTop_nat 3).eventually hev] with X hX
  intro σ₀ r hr0 hrhalf hσlow hσhigh
  set sig : ℝ := σ₀ - r with hsig
  have hsig0 : 7 / 10 ≤ sig := by rw [hsig]; linarith
  have hsig1 : sig < 1 := by rw [hsig]; linarith
  have hbound := hX (sigma := sig) hsig0 hsig1
  set T : ℝ := ((X + 3 : ℕ) : ℝ) - 2 with hT
  have hTX : T = (X : ℝ) + 1 := by rw [hT]; push_cast; ring
  set Zall := Sieve.zetaResidueUnitClosedRectangleZeros
    ((Sieve.inghamUniformGabrielCenter sig : ℂ) + ((-T : ℝ) : ℂ) * I) ((4 : ℝ) + (T : ℂ) * I)
    with hZall
  set Z := Zall.filter (fun w => sig ≤ w.re) with hZ
  have hchoose : ∀ n ∈ badUniformDiscs σ₀ r X,
      ∃ z ∈ closedBall (uniformDiscCenter σ₀ n) r, xi z = 0 :=
    fun n hn => (mem_badUniformDiscs.mp hn).2
  choose! w hwball hwzero using hchoose
  have hcenter : Sieve.inghamUniformGabrielCenter sig ≤ sig := by
    unfold Sieve.inghamUniformGabrielCenter; linarith
  have hmaps : ∀ n ∈ badUniformDiscs σ₀ r X, w n ∈ Z := by
    intro n hn
    have hnI := (mem_badUniformDiscs.mp hn).1
    rw [Finset.mem_Icc] at hnI
    obtain ⟨hr1, hr2, hi1, hi2⟩ := re_im_of_mem_uniformDisc (hwball n hn)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnI.1
    have hnX : (n : ℝ) ≤ X := by exact_mod_cast hnI.2
    have hre0 : 0 < (w n).re := by linarith
    have hne1 : w n ≠ 1 := by
      intro h; rw [h, Complex.one_re] at hr2; linarith
    have hzeta : riemannZeta (w n) = 0 := (xi_eq_zero_iff hre0 hne1).mp (hwzero n hn)
    have hunit : zetaResidueUnit (w n) = 0 := by
      rw [zetaResidueUnit, Function.update_of_ne hne1, hzeta, mul_zero]
    rw [hZ, Finset.mem_filter, hZall, Sieve.mem_zetaResidueUnitClosedRectangleZeros]
    refine ⟨⟨?_, hunit⟩, by rw [hsig]; linarith⟩
    rw [Complex.mem_reProdIm]
    constructor
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
      rw [Set.uIcc_of_le (by linarith)]
      exact ⟨by linarith, by linarith⟩
    · simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, zero_add, add_zero]
      rw [Set.uIcc_of_le (by rw [hTX]; linarith)]
      exact ⟨by rw [hTX]; linarith, by rw [hTX]; linarith⟩
  have hinj : Set.InjOn w (badUniformDiscs σ₀ r X : Set ℕ) := by
    intro n hn m hm hnm
    obtain ⟨-, -, hn1, hn2⟩ := re_im_of_mem_uniformDisc (hwball n hn)
    obtain ⟨-, -, hm1, hm2⟩ := re_im_of_mem_uniformDisc (hwball m hm)
    rw [hnm] at hn1 hn2
    have h1 : ((n : ℝ) - m) < 1 := by linarith
    have h2 : ((m : ℝ) - n) < 1 := by linarith
    have h3 : (n : ℤ) - m < 1 := by exact_mod_cast h1
    have h4 : (m : ℤ) - n < 1 := by exact_mod_cast h2
    omega
  have hcard : (badUniformDiscs σ₀ r X).card ≤ Z.card :=
    Finset.card_le_card_of_injOn w hmaps hinj
  have hsum : (Z.card : ℝ) ≤ Sieve.zetaLittlewoodZeroCountAbove
      (Sieve.inghamUniformGabrielCenter sig) 4 T sig := by
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
  calc ((badUniformDiscs σ₀ r X).card : ℝ) ≤ Z.card := by exact_mod_cast hcard
    _ ≤ _ := hsum
    _ ≤ _ := hbound

/-- Off the exceptional set the seam contracts. -/
theorem uniformDisc_adjointSeam_lt_one {σ₀ r : ℝ} (hr : 0 < r) {n : ℕ}
    (hn : ∀ z ∈ closedBall (uniformDiscCenter σ₀ n) r, xi z ≠ 0) :
    ∃ hne : ∀ ζ ∈ sphere (uniformDiscCenter σ₀ n) r, xi ζ ≠ 0,
      ‖(xiDiscDatum (uniformDiscCenter σ₀ n) r hr hne).circlePhase.datum.adjointHankelSeam‖
        < 1 :=
  ⟨fun ζ hζ => hn ζ (sphere_subset_closedBall hζ),
    xiDisc_adjointSeam_lt_one_of_ne_zero _ _ _ _ hn⟩

end RHTower
