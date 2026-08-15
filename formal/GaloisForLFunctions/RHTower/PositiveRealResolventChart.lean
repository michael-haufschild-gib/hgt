import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.InfiniteSum.Order
import GaloisForLFunctions.HTGeometry.CaratheodoryCoefficient
import GaloisForLFunctions.HTGeometry.PowerSequenceLimitOne

/-!
# The positive-real resolvent and its disk chart

A divisor whose points all lie to the right of `-c` has a resolvent with strictly positive real
part on the half-plane `Re Y > -c`: every summand `1/(Y + ζ)` has real part
`(Re Y + Re ζ)/|Y + ζ|²`.

The Möbius chart `Φ(z) = (y(1+z) + 2cz)/(1-z)` carries the unit disk onto that half-plane, sends
`0` to `y` and `-1` to `-c`, so the composed function has positive real part on the disk and
Carathéodory's coefficient inequality applies to it.  A simple pole at `a` becomes an ordinary
disk pole whose Julia-normalized residue is the invariant trace of the physical residue.
-/

open Complex

noncomputable section

namespace RHTower

/-- A point of positive real part has an inverse of positive real part. -/
theorem re_inv_pos (w : ℂ) (hw : 0 < w.re) : 0 < (w⁻¹).re := by
  have hne : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  rw [Complex.inv_re]
  exact div_pos hw (Complex.normSq_pos.2 hne)

/-- **(PCR.2) The resolvent of a right divisor is positive-real.** -/
theorem re_tsum_inv_pos {ι : Type*} [Nonempty ι] (ζ : ι → ℂ) (Y : ℂ) (c : ℝ)
    (hc : ∀ q, c < (ζ q).re) (hY : -c < Y.re)
    (hsum : Summable fun q => (Y + ζ q)⁻¹) :
    0 < (∑' q, (Y + ζ q)⁻¹).re := by
  have hpos : ∀ q, 0 < ((Y + ζ q)⁻¹).re := by
    intro q
    refine re_inv_pos _ ?_
    rw [Complex.add_re]
    have := hc q
    linarith
  have hre : (∑' q, (Y + ζ q)⁻¹).re = ∑' q, ((Y + ζ q)⁻¹).re :=
    Complex.reCLM.map_tsum hsum
  rw [hre]
  have hsumre : Summable fun q => ((Y + ζ q)⁻¹).re :=
    (Complex.hasSum_re hsum.hasSum).summable
  exact hsumre.tsum_pos (fun q => (hpos q).le) (Classical.arbitrary ι) (hpos _)

/-! ## The disk chart -/

/-- The Möbius chart of the half-plane `Re Y > -c` centred at `y`. -/
def diskChart (c y : ℝ) (z : ℂ) : ℂ := ((y : ℂ) * (1 + z) + 2 * (c : ℂ) * z) / (1 - z)

/-- Its inverse. -/
def diskChartInv (c y : ℝ) (Y : ℂ) : ℂ := (Y - (y : ℂ)) / (Y + (y : ℂ) + 2 * (c : ℂ))

theorem diskChart_zero (c y : ℝ) : diskChart c y 0 = (y : ℂ) := by
  rw [diskChart]
  norm_num

theorem diskChart_add_c (c y : ℝ) {z : ℂ} (hz : z ≠ 1) :
    diskChart c y z + (c : ℂ) = ((y : ℂ) + (c : ℂ)) * (1 + z) / (1 - z) := by
  have hne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  rw [diskChart]
  field_simp
  ring

theorem diskChart_sub_center (c y : ℝ) {z : ℂ} (hz : z ≠ 1) :
    diskChart c y z - (y : ℂ) = 2 * ((y : ℂ) + (c : ℂ)) * z / (1 - z) := by
  have hne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  rw [diskChart]
  field_simp
  ring

/-- The Cayley transform has positive real part on the disk. -/
theorem re_one_add_div_one_sub {z : ℂ} (hz : ‖z‖ < 1) :
    ((1 + z) / (1 - z)).re = (1 - ‖z‖ ^ 2) / ‖1 - z‖ ^ 2 := by
  have hne : (1 : ℂ) - z ≠ 0 := by
    intro h
    have : z = 1 := by linear_combination -h
    rw [this] at hz
    simp at hz
  have hcc : (1 - z) * (starRingEnd ℂ) (1 - z) = ((‖(1 : ℂ) - z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hconjne : (starRingEnd ℂ) (1 - z) ≠ 0 := by
    rw [starRingEnd_apply]
    exact star_ne_zero.2 hne
  have hkey : (1 + z) / (1 - z)
      = (1 + z) * (starRingEnd ℂ) (1 - z) / ((‖(1 : ℂ) - z‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hcc]
    field_simp
  rw [hkey, Complex.div_ofReal_re]
  · congr 1
    have hconj : (starRingEnd ℂ) (1 - z) = 1 - (starRingEnd ℂ) z := by
      rw [map_sub, map_one]
    rw [hconj]
    have hexp : (1 + z) * (1 - (starRingEnd ℂ) z)
        = 1 + (z - (starRingEnd ℂ) z) - z * (starRingEnd ℂ) z := by ring
    have h1 : (z - (starRingEnd ℂ) z).re = 0 := by
      simp [Complex.sub_re, Complex.conj_re]
    have h2 : (z * (starRingEnd ℂ) z).re = ‖z‖ ^ 2 := by
      rw [Complex.mul_conj, Complex.ofReal_re]
      exact Complex.normSq_eq_norm_sq z
    rw [hexp, Complex.sub_re, Complex.add_re, Complex.one_re, h1, h2]
    ring

/-- **(PCR.3) The chart maps the disk into the half-plane.** -/
theorem re_diskChart_gt (c y : ℝ) (hyc : 0 < y + c) {z : ℂ} (hz : ‖z‖ < 1) :
    -c < (diskChart c y z).re := by
  have hne : z ≠ 1 := by
    intro h
    rw [h] at hz
    simp at hz
  have hsub : (1 : ℂ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hchart := diskChart_add_c c y hne
  have hfac : ((y : ℂ) + (c : ℂ)) * (1 + z) / (1 - z)
      = ((y + c : ℝ) : ℂ) * ((1 + z) / (1 - z)) := by
    push_cast
    ring
  rw [hfac] at hchart
  have hre : (diskChart c y z + (c : ℂ)).re = (y + c) * ((1 - ‖z‖ ^ 2) / ‖1 - z‖ ^ 2) := by
    rw [hchart, Complex.re_ofReal_mul, re_one_add_div_one_sub hz]
  have hpos : 0 < (y + c) * ((1 - ‖z‖ ^ 2) / ‖1 - z‖ ^ 2) := by
    refine mul_pos hyc (div_pos ?_ ?_)
    · nlinarith [norm_nonneg z]
    · have : ‖(1 : ℂ) - z‖ ≠ 0 := norm_ne_zero_iff.2 hsub
      positivity
  rw [Complex.add_re, Complex.ofReal_re] at hre
  linarith [hre ▸ hpos]

/-! ## The disk image of a simple pole -/

/-- **(PCR.10) A simple pole becomes an ordinary disk pole.** -/
theorem pole_diskChart (c y a ρ : ℝ) {z : ℂ} (hz : z ≠ 1)
    (hd : (y : ℂ) + (a : ℂ) + 2 * (c : ℂ) ≠ 0) :
    (ρ : ℂ) / (diskChart c y z - (a : ℂ))
      = (ρ : ℂ) * (1 - z) /
        (((y : ℂ) + (a : ℂ) + 2 * (c : ℂ)) *
          (z - ((a : ℂ) - (y : ℂ)) / ((y : ℂ) + (a : ℂ) + 2 * (c : ℂ)))) := by
  have hne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  have hden : diskChart c y z - (a : ℂ)
      = (((y : ℂ) + (a : ℂ) + 2 * (c : ℂ)) *
          (z - ((a : ℂ) - (y : ℂ)) / ((y : ℂ) + (a : ℂ) + 2 * (c : ℂ)))) / (1 - z) := by
    rw [diskChart]
    field_simp
    ring
  rw [hden]
  field_simp

/-- **(PCR.13) The Julia-normalized residue.** -/
theorem julia_residue (c y a ρ : ℝ) (hd : y + a + 2 * c ≠ 0) (hac : a + c ≠ 0) :
    (2 * ρ * (y + c) / (y + a + 2 * c) ^ 2) / (2 * (a + c) / (y + a + 2 * c))
      = ρ * (y + c) / ((a + c) * (y + a + 2 * c)) := by
  field_simp

/-! ## Ordinary versus Julia-normalized residues -/

/-- **(PCR.14) The ordinary disk residue is asymptotically blind.**  It is bounded by `2ρ/y`, so it
vanishes as the centre recedes even when the physical residue does not. -/
theorem diskResidue_le (c y a ρ : ℝ) (hc : 0 < c) (ha : 0 ≤ a) (hρ : 0 ≤ ρ) (hy : 0 < y) :
    2 * ρ * (y + c) / (y + a + 2 * c) ^ 2 ≤ 2 * ρ / y := by
  have hden : 0 < (y + a + 2 * c) ^ 2 := by positivity
  rw [div_le_div_iff₀ hden hy]
  have hkey : 0 ≤ (y + a + 2 * c) ^ 2 - y * (y + c) := by nlinarith [ha, hc.le, hy.le]
  nlinarith [mul_nonneg hρ hkey]

/-- **(PCR.15) The Julia-normalized residue is comparable to the physical residue.**  Up to the
absolute factor two it equals `ρ/(a+c)` for every centre beyond the pole. -/
theorem juliaResidue_comparable (c y a ρ : ℝ) (hc : 0 < c) (ha : 0 ≤ a) (hρ : 0 ≤ ρ)
    (hy : a + 2 * c ≤ y) :
    ρ / (a + c) / 2 ≤ ρ * (y + c) / ((a + c) * (y + a + 2 * c))
      ∧ ρ * (y + c) / ((a + c) * (y + a + 2 * c)) ≤ ρ / (a + c) := by
  have hac : 0 < a + c := by linarith
  have hypos : 0 < y := by linarith
  have hd : 0 < y + a + 2 * c := by linarith
  constructor
  · rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hρ hac.le) (by linarith : (0 : ℝ) ≤ y - a)]
  · rw [div_le_div_iff₀ (by positivity) hac]
    nlinarith [mul_nonneg (mul_nonneg hρ hac.le) hac.le]

/-- **(PCR.16)/(PCR.17) The two vanishing targets agree.**  The total Julia-normalized boundary
mass is comparable, with absolute constants, to the total physical residue weighted by `1/(a+c)`. -/
theorem sum_juliaResidue_comparable {ι : Type*} [Fintype ι] (c y : ℝ) (ρ a : ι → ℝ)
    (hc : 0 < c) (ha : ∀ i, 0 ≤ a i) (hρ : ∀ i, 0 ≤ ρ i) (hy : ∀ i, a i + 2 * c ≤ y) :
    (∑ i, ρ i / (a i + c)) / 2 ≤ ∑ i, ρ i * (y + c) / ((a i + c) * (y + a i + 2 * c))
      ∧ ∑ i, ρ i * (y + c) / ((a i + c) * (y + a i + 2 * c)) ≤ ∑ i, ρ i / (a i + c) := by
  constructor
  · have hdiv : (∑ i, ρ i / (a i + c)) / 2 = ∑ i, ρ i / (a i + c) / 2 := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv, div_eq_mul_inv]
    rw [hdiv]
    refine Finset.sum_le_sum fun i _ => ?_
    exact (juliaResidue_comparable c y (a i) (ρ i) hc (ha i) (hρ i) (hy i)).1
  · refine Finset.sum_le_sum fun i _ => ?_
    exact (juliaResidue_comparable c y (a i) (ρ i) hc (ha i) (hρ i) (hy i)).2

/-! ## The Carathéodory reserve hierarchy -/

/-- **(PCR.18) The disk coefficient of one pole in reserve form.** -/
theorem reserve_term (c y a ρ : ℝ) (m : ℕ) (hm : 1 ≤ m) (hd : y + a + 2 * c ≠ 0)
    (hya : y - a ≠ 0) :
    2 * ρ * (y + c) / ((y + a + 2 * c) ^ 2 * ((a - y) / (y + a + 2 * c)) ^ (2 * m))
      = 2 * (y + c) * (ρ * (y + a + 2 * c) ^ (2 * m - 2) / (y - a) ^ (2 * m)) := by
  have heven : ((a - y) / (y + a + 2 * c)) ^ (2 * m)
      = (y - a) ^ (2 * m) / (y + a + 2 * c) ^ (2 * m) := by
    rw [div_pow]
    congr 1
    have hneg : a - y = -(y - a) := by ring
    rw [hneg, neg_pow]
    have hpar : (-1 : ℝ) ^ (2 * m) = 1 := by
      rw [pow_mul]
      norm_num
    rw [hpar, one_mul]
  have hsplit : (y + a + 2 * c) ^ (2 * m) = (y + a + 2 * c) ^ 2 * (y + a + 2 * c) ^ (2 * m - 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hd2 : (y + a + 2 * c) ^ 2 ≠ 0 := pow_ne_zero 2 hd
  have hdm : (y + a + 2 * c) ^ (2 * m - 2) ≠ 0 := pow_ne_zero _ hd
  have hyam : (y - a) ^ (2 * m) ≠ 0 := pow_ne_zero _ hya
  rw [heven, hsplit]
  field_simp

/-- **(PCR.19) The reserve hierarchy.**  Every odd Carathéodory coefficient bounds a positive
combination of the Padé residues. -/
theorem caratheodory_reserve {ι : Type*} [Fintype ι] (c y : ℝ) (ρ a : ι → ℝ) (m : ℕ)
    (hm : 1 ≤ m) (hd : ∀ i, y + a i + 2 * c ≠ 0) (hlt : ∀ i, a i < y) (G0 : ℝ)
    (hcara : ∑ i, 2 * ρ i * (y + c)
        / ((y + a i + 2 * c) ^ 2 * ((a i - y) / (y + a i + 2 * c)) ^ (2 * m)) ≤ 2 * G0) :
    (y + c) * ∑ i, ρ i * (y + a i + 2 * c) ^ (2 * m - 2) / (y - a i) ^ (2 * m) ≤ G0 := by
  have hterm : ∀ i : ι, 2 * ρ i * (y + c)
      / ((y + a i + 2 * c) ^ 2 * ((a i - y) / (y + a i + 2 * c)) ^ (2 * m))
      = 2 * (y + c) * (ρ i * (y + a i + 2 * c) ^ (2 * m - 2) / (y - a i) ^ (2 * m)) := by
    intro i
    exact reserve_term c y (a i) (ρ i) m hm (hd i) (by
      have := hlt i
      intro hcon
      linarith [sub_eq_zero.1 hcon])
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum] at hcara
  linarith

/-- **(PCR.20) The exact reserve balance.**  Every Padé atom to the right of `-c` must be paid for
by Padé mass to the left of `-c`. -/
theorem caratheodory_reserve_balance {ι : Type*} [Fintype ι] (c y : ℝ) (ρ a : ι → ℝ)
    (hlt : ∀ i, a i < y)
    (hres : (y + c) * ∑ i, ρ i / (y - a i) ^ 2 ≤ ∑ i, ρ i / (y - a i)) :
    ∑ i, ρ i * (a i + c) / (y - a i) ^ 2 ≤ 0 := by
  have hterm : ∀ i : ι, ρ i * (a i + c) / (y - a i) ^ 2
      = (y + c) * (ρ i / (y - a i) ^ 2) - ρ i / (y - a i) := by
    intro i
    have hne : y - a i ≠ 0 := by
      have := hlt i
      intro hcon
      linarith [sub_eq_zero.1 hcon]
    field_simp
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith

/-! ## The half-plane derivative bound -/

open GaloisForLFunctions.HTGeometry

/-- The first Cauchy coefficient is the derivative at the centre. -/
theorem cauchyCoeff_one_eq_deriv (f : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall 0 R)) :
    cauchyCoeff f R 1 = deriv f 0 := by
  obtain ⟨Rn, hRn⟩ : ∃ Rn : NNReal, (Rn : ℝ) = R := ⟨⟨R, hR.le⟩, rfl⟩
  have hRpos : 0 < Rn := by
    rw [← NNReal.coe_pos, hRn]
    exact hR
  have hf' : DifferentiableOn ℂ f (Metric.closedBall 0 (Rn : ℝ)) := by rw [hRn]; exact hf
  have hball := hf'.hasFPowerSeriesOnBall hRpos
  have hderiv := hball.hasFPowerSeriesAt.deriv
  rw [cauchyCoeff, ← hRn]
  exact hderiv.symm

theorem hasDerivAt_diskChart (c y : ℝ) :
    HasDerivAt (diskChart c y) (2 * ((y : ℂ) + (c : ℂ))) 0 := by
  have hnum : HasDerivAt (fun z : ℂ => (y : ℂ) * (1 + z) + 2 * (c : ℂ) * z)
      ((y : ℂ) + 2 * (c : ℂ)) 0 := by
    have h1 : HasDerivAt (fun z : ℂ => (y : ℂ) * (1 + z)) (y : ℂ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_add (1 : ℂ)).const_mul (y : ℂ)
    have h2 : HasDerivAt (fun z : ℂ => 2 * (c : ℂ) * z) (2 * (c : ℂ)) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (2 * (c : ℂ))
    have h3 : HasDerivAt (fun z : ℂ => (y : ℂ) * (1 + z) + 2 * (c : ℂ) * z)
        ((y : ℂ) + 2 * (c : ℂ)) 0 := h1.add h2
    exact h3
  have hden : HasDerivAt (fun z : ℂ => 1 - z) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_sub 1
  have hne : (1 : ℂ) - (0 : ℂ) ≠ 0 := by norm_num
  have h := hnum.div hden hne
  have hval : (((y : ℂ) + 2 * (c : ℂ)) * (1 - 0)
      - ((y : ℂ) * (1 + 0) + 2 * (c : ℂ) * 0) * (-1)) / (1 - 0) ^ 2
      = 2 * ((y : ℂ) + (c : ℂ)) := by
    ring
  rw [hval] at h
  exact h

/-- **The Cauchy coefficients are the Taylor coefficients.** -/
theorem cauchyCoeff_eq_iteratedDeriv (f : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall 0 R)) (n : ℕ) :
    cauchyCoeff f R n = iteratedDeriv n f 0 / n.factorial := by
  obtain ⟨Rn, hRn⟩ : ∃ Rn : NNReal, (Rn : ℝ) = R := ⟨⟨R, hR.le⟩, rfl⟩
  have hRpos : 0 < Rn := by rw [← NNReal.coe_pos, hRn]; exact hR
  have hf' : DifferentiableOn ℂ f (Metric.closedBall 0 (Rn : ℝ)) := by rw [hRn]; exact hf
  have hball := hf'.hasFPowerSeriesOnBall hRpos
  have hat := hball.hasFPowerSeriesAt
  have hat2 := hat.analyticAt.hasFPowerSeriesAt
  have heq := hat.eq_formalMultilinearSeries hat2
  rw [cauchyCoeff, ← hRn, heq, FormalMultilinearSeries.ofScalars_apply_eq]
  simp

set_option maxHeartbeats 1000000 in
/-- **(PCR.5) The half-plane coefficient bound.**  A function with nonnegative real part on the
half-plane `Re Y > -c` has every Taylor coefficient of its disk chart bounded by `2 Re G(y)`. -/
theorem caratheodory_halfplane_coeff (c y : ℝ) (hyc : 0 < y + c) (G : ℂ → ℂ)
    (hG : ∀ Y : ℂ, -c < Y.re → DifferentiableAt ℂ G Y)
    (hre : ∀ Y : ℂ, -c < Y.re → 0 ≤ (G Y).re) {n : ℕ} (hn : 1 ≤ n) :
    ‖iteratedDeriv n (fun z => G (diskChart c y z)) 0‖ / n.factorial
      ≤ 2 * (G (y : ℂ)).re := by
  have hyre : -c < ((y : ℂ)).re := by
    rw [Complex.ofReal_re]
    linarith
  have hzero : diskChart c y 0 = (y : ℂ) := diskChart_zero c y
  have hdiffAll : ∀ z : ℂ, ‖z‖ < 1 → DifferentiableAt ℂ (fun w => G (diskChart c y w)) z := by
    intro z hzlt
    have hne : (1 : ℂ) - z ≠ 0 := by
      intro h
      have : z = 1 := by linear_combination -h
      rw [this] at hzlt
      simp at hzlt
    have hchart : DifferentiableAt ℂ (diskChart c y) z := by
      refine DifferentiableAt.div ?_ ?_ hne
      · exact (((differentiableAt_id).const_add 1).const_mul _).add
          ((differentiableAt_id).const_mul _)
      · exact (differentiableAt_const 1).sub differentiableAt_id
    exact (hG _ (re_diskChart_gt c y hyc hzlt)).comp z hchart
  have hchain : ∀ R : ℝ, 0 < R → R < 1 →
      ‖iteratedDeriv n (fun z => G (diskChart c y z)) 0‖ / n.factorial * R ^ n
        ≤ 2 * (G (y : ℂ)).re := by
    intro R hR hR1
    have hDon : DifferentiableOn ℂ (fun w => G (diskChart c y w)) (Metric.closedBall 0 R) := by
      intro z hz
      refine (hdiffAll z ?_).differentiableWithinAt
      have := Metric.mem_closedBall.1 hz
      rw [dist_zero_right] at this
      exact lt_of_le_of_lt this hR1
    have hDCC : DiffContOnCl ℂ (fun w => G (diskChart c y w)) (Metric.ball 0 R) := by
      constructor
      · intro z hz
        refine (hdiffAll z ?_).differentiableWithinAt
        have := Metric.mem_ball.1 hz
        rw [dist_zero_right] at this
        exact lt_trans this hR1
      · intro z hz
        refine (hdiffAll z ?_).continuousAt.continuousWithinAt
        have := Metric.mem_closedBall.1 (Metric.closure_ball_subset_closedBall hz)
        rw [dist_zero_right] at this
        exact lt_of_le_of_lt this hR1
    have hpos : ∀ z ∈ Metric.sphere (0 : ℂ) R, 0 ≤ ((fun w => G (diskChart c y w)) z).re := by
      intro z hz
      have hzn : ‖z‖ = R := by
        have := Metric.mem_sphere.1 hz
        rwa [dist_zero_right] at this
      exact hre _ (re_diskChart_gt c y hyc (by rw [hzn]; exact hR1))
    have hcara := norm_cauchyCoeff_mul_pow_le (fun w => G (diskChart c y w)) hR hDCC hpos hn
    have hcoeff := cauchyCoeff_eq_iteratedDeriv (fun w => G (diskChart c y w)) hR hDon n
    rw [hcoeff, hzero] at hcara
    have hnormdiv : ‖iteratedDeriv n (fun z => G (diskChart c y z)) 0 / (n.factorial : ℂ)‖
        = ‖iteratedDeriv n (fun z => G (diskChart c y z)) 0‖ / n.factorial := by
      rw [norm_div, Complex.norm_natCast]
    rw [hnormdiv] at hcara
    exact hcara
  obtain ⟨A, hA⟩ : ∃ A : ℝ,
      A = ‖iteratedDeriv n (fun z => G (diskChart c y z)) 0‖ / n.factorial := ⟨_, rfl⟩
  have hlim : Filter.Tendsto (fun R : ℝ => A * R ^ n) (nhdsWithin 1 (Set.Iio 1)) (nhds A) := by
    have h : Filter.Tendsto (fun R : ℝ => A * R ^ n) (nhds 1) (nhds (A * 1 ^ n)) :=
      tendsto_const_nhds.mul ((continuous_pow n).tendsto 1)
    rw [one_pow, mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ R in nhdsWithin (1 : ℝ) (Set.Iio 1), A * R ^ n ≤ 2 * (G (y : ℂ)).re := by
    have h0 : ∀ᶠ R in nhdsWithin (1 : ℝ) (Set.Iio 1), (0 : ℝ) < R :=
      nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [self_mem_nhdsWithin, h0] with R hR1 hR0
    rw [hA]
    exact hchain R hR0 hR1
  rw [← hA]
  exact le_of_tendsto hlim hev

/-- **(PCR.20) The half-plane derivative bound.**  `(y+c)·|G'(y)| ≤ Re G(y)` at every real centre
`y > -c`. -/
theorem caratheodory_halfplane_deriv (c y : ℝ) (hyc : 0 < y + c) (G : ℂ → ℂ)
    (hG : ∀ Y : ℂ, -c < Y.re → DifferentiableAt ℂ G Y)
    (hre : ∀ Y : ℂ, -c < Y.re → 0 ≤ (G Y).re) :
    (y + c) * ‖deriv G (y : ℂ)‖ ≤ (G (y : ℂ)).re := by
  have hyre : -c < ((y : ℂ)).re := by
    rw [Complex.ofReal_re]
    linarith
  have hzero : diskChart c y 0 = (y : ℂ) := diskChart_zero c y
  have hbase := caratheodory_halfplane_coeff c y hyc G hG hre (n := 1) (le_refl 1)
  have hd : iteratedDeriv 1 (fun w => G (diskChart c y w)) 0
      = deriv G (y : ℂ) * (2 * ((y : ℂ) + (c : ℂ))) := by
    rw [iteratedDeriv_one]
    have hc := hasDerivAt_diskChart c y
    have hGd : HasDerivAt G (deriv G (y : ℂ)) (diskChart c y 0) := by
      rw [hzero]
      exact (hG _ hyre).hasDerivAt
    exact (hGd.comp 0 hc).deriv
  rw [hd] at hbase
  have hnorm : ‖deriv G (y : ℂ) * (2 * ((y : ℂ) + (c : ℂ)))‖
      = ‖deriv G (y : ℂ)‖ * (2 * (y + c)) := by
    rw [norm_mul]
    congr 1
    have hcast : (2 : ℂ) * ((y : ℂ) + (c : ℂ)) = ((2 * (y + c) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [hnorm] at hbase
  simp only [Nat.factorial_one, Nat.cast_one, div_one] at hbase
  linarith

/-- The iterated derivatives of a simple pole. -/
theorem iteratedDeriv_inv_sub (w : ℂ) (k : ℕ) :
    ∀ z : ℂ, z - w ≠ 0 →
      iteratedDeriv k (fun u => (u - w)⁻¹) z = (-1) ^ k * k.factorial / (z - w) ^ (k + 1) := by
  induction k with
  | zero =>
      intro z hz
      simp
  | succ k ih =>
      intro z hz
      have hopen : IsOpen {u : ℂ | u - w ≠ 0} :=
        isOpen_compl_singleton.preimage (continuous_id.sub continuous_const)
      have hmem : z ∈ {u : ℂ | u - w ≠ 0} := hz
      have hev : (fun u : ℂ => iteratedDeriv k (fun v => (v - w)⁻¹) u)
          =ᶠ[nhds z] fun u : ℂ => (-1) ^ k * k.factorial / (u - w) ^ (k + 1) := by
        filter_upwards [hopen.mem_nhds hmem] with u hu
        exact ih u hu
      rw [iteratedDeriv_succ, hev.deriv_eq]
      have hbase : HasDerivAt (fun u : ℂ => u - w) 1 z := (hasDerivAt_id z).sub_const w
      have hpow : HasDerivAt (fun u : ℂ => (u - w) ^ (k + 1))
          (((k : ℂ) + 1) * (z - w) ^ k) z := by
        have h : HasDerivAt (fun u : ℂ => (u - w) ^ (k + 1))
            (((k + 1 : ℕ) : ℂ) * (z - w) ^ (k + 1 - 1) * 1) z := hbase.pow (k + 1)
        simpa using h
      have hne : (z - w) ^ (k + 1) ≠ 0 := pow_ne_zero _ hz
      have hinv : HasDerivAt (fun u : ℂ => ((u - w) ^ (k + 1))⁻¹)
          (-(((k : ℂ) + 1) * (z - w) ^ k) / ((z - w) ^ (k + 1)) ^ 2) z := hpow.inv hne
      have hd : HasDerivAt (fun u : ℂ => (-1 : ℂ) ^ k * (k.factorial : ℂ) / (u - w) ^ (k + 1))
          ((-1 : ℂ) ^ k * (k.factorial : ℂ) *
            (-(((k : ℂ) + 1) * (z - w) ^ k) / ((z - w) ^ (k + 1)) ^ 2)) z := by
        have h := hinv.const_mul ((-1 : ℂ) ^ k * (k.factorial : ℂ))
        simpa [div_eq_mul_inv] using h
      rw [hd.deriv]
      have hzk : (z - w) ^ (k + 1 + 1) ≠ 0 := pow_ne_zero _ hz
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring

/-- **(PCR.18) The disk Taylor coefficients of one pole.** -/
theorem iteratedDeriv_pole_expansion (ρ d w : ℂ) (hd : d ≠ 0) (hw : w ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    iteratedDeriv k (fun z => ρ * (1 - z) / (d * (z - w))) 0
      = ρ * (1 - w) / d * ((-1) ^ k * k.factorial / (0 - w) ^ (k + 1)) := by
  have hopen : IsOpen {u : ℂ | u - w ≠ 0} :=
    isOpen_compl_singleton.preimage (continuous_id.sub continuous_const)
  have hzero : (0 : ℂ) - w ≠ 0 := by
    intro h
    exact hw (by linear_combination -h)
  have hmem : (0 : ℂ) ∈ {u : ℂ | u - w ≠ 0} := hzero
  have hev : (fun z : ℂ => ρ * (1 - z) / (d * (z - w)))
      =ᶠ[nhds 0] fun z : ℂ => (-(ρ / d)) + (ρ * (1 - w) / d) * (z - w)⁻¹ := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hzw : z - w ≠ 0 := hz
    field_simp
    ring
  have hcd : ContDiffAt ℂ (k : ℕ∞) (fun z : ℂ => (z - w)⁻¹) 0 := by
    refine ContDiffAt.inv ?_ hzero
    exact contDiffAt_id.sub contDiffAt_const
  rw [Filter.EventuallyEq.iteratedDeriv_eq k hev, iteratedDeriv_const_add (by omega) _,
    iteratedDeriv_const_mul _ hcd, iteratedDeriv_inv_sub w k 0 hzero]

/-- **(PCR.20) The Padé reserve balance from the literal source.**  Matching the resolvent and its
derivative at the centre turns the half-plane derivative bound into the exact reserve balance. -/
theorem pade_reserve_balance {ι : Type*} [Fintype ι] (c y : ℝ) (hyc : 0 < y + c)
    (ρ a : ι → ℝ) (hlt : ∀ i, a i < y) (hρ : ∀ i, 0 ≤ ρ i)
    (G : ℂ → ℂ) (hG : ∀ Y : ℂ, -c < Y.re → DifferentiableAt ℂ G Y)
    (hre : ∀ Y : ℂ, -c < Y.re → 0 ≤ (G Y).re)
    (hmatch0 : (G (y : ℂ)).re = ∑ i, ρ i / (y - a i))
    (hmatch1 : deriv G (y : ℂ) = ((-∑ i, ρ i / (y - a i) ^ 2 : ℝ) : ℂ)) :
    ∑ i, ρ i * (a i + c) / (y - a i) ^ 2 ≤ 0 := by
  have hnn : 0 ≤ ∑ i, ρ i / (y - a i) ^ 2 := by
    refine Finset.sum_nonneg fun i _ => ?_
    have hne : y - a i ≠ 0 := by
      have := hlt i
      intro hcon
      linarith [sub_eq_zero.1 hcon]
    have hsq : 0 < (y - a i) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
    exact div_nonneg (hρ i) hsq.le
  have hnorm : ‖deriv G (y : ℂ)‖ = ∑ i, ρ i / (y - a i) ^ 2 := by
    rw [hmatch1, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hnn]
  have hbound := caratheodory_halfplane_deriv c y hyc G hG hre
  rw [hnorm, hmatch0] at hbound
  exact caratheodory_reserve_balance c y ρ a hlt hbound

set_option maxHeartbeats 1000000 in
/-- **(PCR.19) The reserve hierarchy from the literal source.**  Once the `(2m-1)`-st Taylor
coefficient of the chart-composed resolvent is identified with the pole expansion, the
Carathéodory bound is exactly the reserve inequality. -/
theorem caratheodory_reserve_hierarchy {ι : Type*} [Fintype ι] (c y : ℝ) (hyc : 0 < y + c)
    (ρ a : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hlt : ∀ i, a i < y)
    (G : ℂ → ℂ) (hG : ∀ Y : ℂ, -c < Y.re → DifferentiableAt ℂ G Y)
    (hre : ∀ Y : ℂ, -c < Y.re → 0 ≤ (G Y).re) (m : ℕ) (hm : 1 ≤ m)
    (hmatch : iteratedDeriv (2 * m - 1) (fun z => G (diskChart c y z)) 0
        / (((2 * m - 1).factorial : ℕ) : ℂ)
      = -(((2 * (y + c) *
            ∑ i, ρ i * (y + a i + 2 * c) ^ (2 * m - 2) / (y - a i) ^ (2 * m)) : ℝ) : ℂ)) :
    (y + c) * ∑ i, ρ i * (y + a i + 2 * c) ^ (2 * m - 2) / (y - a i) ^ (2 * m)
      ≤ (G (y : ℂ)).re := by
  have hnn : 0 ≤ ∑ i, ρ i * (y + a i + 2 * c) ^ (2 * m - 2) / (y - a i) ^ (2 * m) := by
    refine Finset.sum_nonneg fun i _ => ?_
    have hne : y - a i ≠ 0 := by
      have := hlt i
      intro hcon
      linarith [sub_eq_zero.1 hcon]
    have hevenTop : 0 ≤ (y + a i + 2 * c) ^ (2 * m - 2) := by
      have hidx : 2 * m - 2 = 2 * (m - 1) := by omega
      rw [hidx, pow_mul]
      positivity
    have hevenBot : 0 < (y - a i) ^ (2 * m) := by
      rw [pow_mul]
      have : (0 : ℝ) < (y - a i) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
      positivity
    exact div_nonneg (mul_nonneg (hρ i) hevenTop) hevenBot.le
  have hbignn : (0 : ℝ) ≤ 2 * (y + c) *
      ∑ i, ρ i * (y + a i + 2 * c) ^ (2 * m - 2) / (y - a i) ^ (2 * m) := by
    have : (0 : ℝ) ≤ 2 * (y + c) := by linarith
    exact mul_nonneg this hnn
  have hcoeff := caratheodory_halfplane_coeff c y hyc G hG hre (n := 2 * m - 1) (by omega)
  have hnorm : ‖iteratedDeriv (2 * m - 1) (fun z => G (diskChart c y z)) 0‖
      / ((2 * m - 1).factorial : ℝ)
      = 2 * (y + c) * ∑ i, ρ i * (y + a i + 2 * c) ^ (2 * m - 2) / (y - a i) ^ (2 * m) := by
    have h := congrArg norm hmatch
    rw [norm_div, Complex.norm_natCast, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hbignn] at h
    exact h
  rw [hnorm] at hcoeff
  linarith

/-! ## Finite-jet blindness -/

theorem inv_one_sub_le_exp {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    (1 - t)⁻¹ ≤ Real.exp (2 * t) := by
  have hpos : (0 : ℝ) < 1 - t := by linarith
  have hexp : 1 + 2 * t ≤ Real.exp (2 * t) := by
    have := Real.add_one_le_exp (2 * t)
    linarith
  have hmul : 1 ≤ (1 - t) * Real.exp (2 * t) := by nlinarith [hexp, ht0, ht, hpos]
  rw [inv_eq_one_div, div_le_iff₀ hpos]
  linarith [hmul]

theorem sum_inv_one_sub_pow_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (M : ℕ) :
    ∑ k ∈ Finset.range (M + 1), ((1 - t)⁻¹) ^ (k + 1)
      ≤ ((M : ℝ) + 1) * Real.exp (2 * ((M : ℝ) + 1) * t) := by
  have hpos : (0 : ℝ) < 1 - t := by linarith
  have hterm : ∀ k ∈ Finset.range (M + 1),
      ((1 - t)⁻¹) ^ (k + 1) ≤ Real.exp (2 * ((M : ℝ) + 1) * t) := by
    intro k hk
    have hkM : (k : ℝ) + 1 ≤ (M : ℝ) + 1 := by
      have := Finset.mem_range.1 hk
      have hk' : (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 this
      linarith
    calc ((1 - t)⁻¹) ^ (k + 1) ≤ (Real.exp (2 * t)) ^ (k + 1) :=
          pow_le_pow_left₀ (by positivity) (inv_one_sub_le_exp ht0 ht) _
      _ = Real.exp (((k : ℝ) + 1) * (2 * t)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
      _ ≤ Real.exp (2 * ((M : ℝ) + 1) * t) := by
          refine Real.exp_le_exp.2 ?_
          nlinarith [ht0, hkM]
  calc ∑ k ∈ Finset.range (M + 1), ((1 - t)⁻¹) ^ (k + 1)
      ≤ ∑ _k ∈ Finset.range (M + 1), Real.exp (2 * ((M : ℝ) + 1) * t) :=
        Finset.sum_le_sum hterm
    _ = ((M : ℝ) + 1) * Real.exp (2 * ((M : ℝ) + 1) * t) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- **(PCR.22)-(PCR.23) The finite jet of one bounded atom.**  The whole head of length `M+1` of
the matched jet is bounded by `(2ρ/y)(M+1)exp(2(M+1)t)` with `t = 2(a+c)/(y+a+2c)`. -/
theorem finiteJet_bound (c y a ρ : ℝ) (hc : 0 < c) (ha : 0 ≤ a) (hρ : 0 ≤ ρ) (hy : 0 < y)
    (ht : 2 * (a + c) / (y + a + 2 * c) ≤ 1 / 2) (M : ℕ) :
    ∑ k ∈ Finset.range (M + 1),
        2 * ρ * (y + c) / (y + a + 2 * c) ^ 2 *
          ((1 - 2 * (a + c) / (y + a + 2 * c))⁻¹) ^ (k + 1)
      ≤ 2 * ρ / y * (((M : ℝ) + 1) *
          Real.exp (2 * ((M : ℝ) + 1) * (2 * (a + c) / (y + a + 2 * c)))) := by
  have hd : 0 < y + a + 2 * c := by linarith
  have ht0 : 0 ≤ 2 * (a + c) / (y + a + 2 * c) := by positivity
  have hsum := sum_inv_one_sub_pow_le ht0 ht M
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range (M + 1),
      ((1 - 2 * (a + c) / (y + a + 2 * c))⁻¹) ^ (k + 1) := by
    refine Finset.sum_nonneg fun k _ => ?_
    have : (0 : ℝ) < 1 - 2 * (a + c) / (y + a + 2 * c) := by linarith
    positivity
  have hcoef := diskResidue_le c y a ρ hc ha hρ hy
  have hcoef0 : 0 ≤ 2 * ρ * (y + c) / (y + a + 2 * c) ^ 2 := by positivity
  rw [← Finset.mul_sum]
  calc 2 * ρ * (y + c) / (y + a + 2 * c) ^ 2 *
        ∑ k ∈ Finset.range (M + 1), ((1 - 2 * (a + c) / (y + a + 2 * c))⁻¹) ^ (k + 1)
      ≤ 2 * ρ / y *
        ∑ k ∈ Finset.range (M + 1), ((1 - 2 * (a + c) / (y + a + 2 * c))⁻¹) ^ (k + 1) :=
        mul_le_mul_of_nonneg_right hcoef hsum0
    _ ≤ 2 * ρ / y * (((M : ℝ) + 1) *
          Real.exp (2 * ((M : ℝ) + 1) * (2 * (a + c) / (y + a + 2 * c)))) := by
        refine mul_le_mul_of_nonneg_left hsum ?_
        positivity

open Filter in
/-- **(PCR.23) The whole finite jet of a bounded atom vanishes.**  When the head length is small
compared with the centre, the entire matched jet of one fixed physical residue tends to zero. -/
theorem tendsto_finiteJet_zero (c a ρ : ℝ) (hc : 0 < c) (ha : 0 ≤ a)
    {y : ℕ → ℝ} {M : ℕ → ℕ} (hy : ∀ j, 0 < y j)
    (hMy : Tendsto (fun j => ((M j : ℝ) + 1) / y j) atTop (nhds 0)) :
    Tendsto (fun j => 2 * ρ / y j * (((M j : ℝ) + 1) *
        Real.exp (2 * ((M j : ℝ) + 1) * (2 * (a + c) / (y j + a + 2 * c))))) atTop (nhds 0) := by
  have hfront : Tendsto (fun j => 2 * ρ * (((M j : ℝ) + 1) / y j)) atTop (nhds 0) := by
    have h := hMy.const_mul (2 * ρ)
    simpa using h
  have hexpArg : Tendsto
      (fun j => 2 * ((M j : ℝ) + 1) * (2 * (a + c) / (y j + a + 2 * c))) atTop (nhds 0) := by
    have hub : Tendsto (fun j => 4 * (a + c) * (((M j : ℝ) + 1) / y j)) atTop (nhds 0) := by
      have h := hMy.const_mul (4 * (a + c))
      simpa using h
    refine squeeze_zero (fun j => ?_) (fun j => ?_) hub
    · have hd : 0 < y j + a + 2 * c := by have := hy j; linarith
      have hM : (0 : ℝ) ≤ (M j : ℝ) + 1 := by positivity
      positivity
    · have hyj := hy j
      have hd : 0 < y j + a + 2 * c := by linarith
      have hM : (0 : ℝ) ≤ (M j : ℝ) + 1 := by positivity
      have hac : (0 : ℝ) ≤ a + c := by linarith
      calc 2 * ((M j : ℝ) + 1) * (2 * (a + c) / (y j + a + 2 * c))
          = 4 * (a + c) * ((M j : ℝ) + 1) / (y j + a + 2 * c) := by ring
        _ ≤ 4 * (a + c) * ((M j : ℝ) + 1) / y j := by
            refine div_le_div_of_nonneg_left ?_ hyj ?_
            · positivity
            · linarith
        _ = 4 * (a + c) * (((M j : ℝ) + 1) / y j) := by ring
  have hexp : Tendsto
      (fun j => Real.exp (2 * ((M j : ℝ) + 1) * (2 * (a + c) / (y j + a + 2 * c))))
      atTop (nhds 1) := by
    have h : Tendsto
        (fun j => Real.exp (2 * ((M j : ℝ) + 1) * (2 * (a + c) / (y j + a + 2 * c))))
        atTop (nhds (Real.exp 0)) := (Real.continuous_exp.tendsto 0).comp hexpArg
    rwa [Real.exp_zero] at h
  have hprod := hfront.mul hexp
  rw [zero_mul] at hprod
  refine hprod.congr fun j => ?_
  ring

/-! ## The depletion kernel ratio -/

/-- **(PCR.29) The exact kernel-ratio defect.**  The ratio of two coefficient kernels differs from
one by `2(b-a)(y+c)` over a product of two linear factors, hence by `O(1/y)` for bounded poles. -/
theorem kernel_ratio_sub_one (c y a b : ℝ) (hay : a - y ≠ 0) (hb : y + b + 2 * c ≠ 0) :
    ((b - y) * (y + a + 2 * c)) / ((a - y) * (y + b + 2 * c)) - 1
      = 2 * (b - a) * (y + c) / ((a - y) * (y + b + 2 * c)) := by
  field_simp
  ring

theorem abs_kernel_ratio_sub_one_le {a b y c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ y / 8)
    (hy : 8 * (|a| + |b| + 1) ≤ y) :
    |((b - y) * (y + a + 2 * c)) / ((a - y) * (y + b + 2 * c)) - 1| ≤ 16 * |b - a| / y := by
  have habs : |a| ≤ y / 8 := by
    have h1 : (0 : ℝ) ≤ |b| := abs_nonneg b
    linarith
  have hbbs : |b| ≤ y / 8 := by
    have h1 : (0 : ℝ) ≤ |a| := abs_nonneg a
    linarith
  have hypos : (0 : ℝ) < y := by
    have h1 : (0 : ℝ) ≤ |a| := abs_nonneg a
    have h2 : (0 : ℝ) ≤ |b| := abs_nonneg b
    linarith
  have hale : a ≤ y / 8 := le_trans (le_abs_self a) habs
  have hbge : -(y / 8) ≤ b := by
    have := neg_abs_le b
    linarith
  have hya : (0 : ℝ) < y - a := by linarith
  have hyb : (0 : ℝ) < y + b + 2 * c := by linarith
  have hay : a - y ≠ 0 := by intro h; linarith [sub_eq_zero.1 h]
  have hb : y + b + 2 * c ≠ 0 := ne_of_gt hyb
  rw [kernel_ratio_sub_one c y a b hay hb, abs_div]
  have hnum : |2 * (b - a) * (y + c)| = 2 * |b - a| * (y + c) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ y + c)]
  have hden : |(a - y) * (y + b + 2 * c)| = (y - a) * (y + b + 2 * c) := by
    rw [abs_mul, abs_of_neg (by linarith : a - y < 0), abs_of_pos hyb]
    ring
  rw [hnum, hden]
  have hdenpos : (0 : ℝ) < (y - a) * (y + b + 2 * c) := mul_pos hya hyb
  rw [div_le_div_iff₀ hdenpos hypos]
  have hba : (0 : ℝ) ≤ |b - a| := abs_nonneg _
  have h1 : 7 * y / 8 ≤ y - a := by linarith
  have h2 : 7 * y / 8 ≤ y + b + 2 * c := by linarith
  have h3 : y + c ≤ 9 * y / 8 := by linarith
  have hprod : (7 * y / 8) * (7 * y / 8) ≤ (y - a) * (y + b + 2 * c) :=
    mul_le_mul h1 h2 (by positivity) (by linarith)
  have hcore : 2 * (y + c) * y ≤ 16 * ((y - a) * (y + b + 2 * c)) := by
    nlinarith [hprod, h3, hypos]
  nlinarith [mul_le_mul_of_nonneg_left hcore hba]

open Filter in
/-- **(PCR.28) The depletion kernel ratio tends to one.**  For bounded poles, a depletion parameter
small compared with the centre, and a head length small compared with the centre, the matched-jet
kernels of two poles become indistinguishable. -/
theorem tendsto_kernelRatio_one (a b : ℝ) {y c : ℕ → ℝ} {k : ℕ → ℕ}
    (hy : Tendsto y atTop atTop) (hc0 : ∀ j, 0 ≤ c j)
    (hcy : Tendsto (fun j => c j / y j) atTop (nhds 0))
    (hky : Tendsto (fun j => ((k j : ℝ) + 1) / y j) atTop (nhds 0)) :
    Tendsto (fun j =>
        (((b - y j) * (y j + a + 2 * c j)) / ((a - y j) * (y j + b + 2 * c j))) ^ (k j + 1))
      atTop (nhds 1) := by
  have hevY : ∀ᶠ j in atTop, 8 * (|a| + |b| + 1) ≤ y j := hy.eventually_ge_atTop _
  have hevC : ∀ᶠ j in atTop, c j ≤ y j / 8 := by
    have hpos : ∀ᶠ j in atTop, (0 : ℝ) < y j := hy.eventually_gt_atTop 0
    have hsmall : ∀ᶠ j in atTop, c j / y j < 1 / 8 :=
      hcy.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
    filter_upwards [hpos, hsmall] with j hj hs
    rw [div_lt_iff₀ hj] at hs
    linarith
  have hbound : ∀ᶠ j in atTop,
      |((b - y j) * (y j + a + 2 * c j)) / ((a - y j) * (y j + b + 2 * c j)) - 1|
        ≤ 16 * |b - a| / y j := by
    filter_upwards [hevY, hevC] with j hj hjc
    exact abs_kernel_ratio_sub_one_le (hc0 j) hjc hj
  have hbig : Tendsto (fun j => 16 * |b - a| / y j) atTop (nhds 0) := by
    have h := hy.inv_tendsto_atTop
    have h2 := h.const_mul (16 * |b - a|)
    simpa [div_eq_mul_inv] using h2
  have hr1 : Tendsto (fun j =>
      ((b - y j) * (y j + a + 2 * c j)) / ((a - y j) * (y j + b + 2 * c j))) atTop (nhds 1) := by
    rw [← sub_zero (1 : ℝ)]
    refine tendsto_sub_nhds_zero_iff.1 ?_
    refine squeeze_zero_norm' ?_ hbig
    filter_upwards [hbound] with j hj
    simpa [Real.norm_eq_abs] using hj
  have hmr : Tendsto (fun j => ((k j + 1 : ℕ) : ℝ) *
      (((b - y j) * (y j + a + 2 * c j)) / ((a - y j) * (y j + b + 2 * c j)) - 1))
      atTop (nhds 0) := by
    have hcast : ∀ j : ℕ, ((k j + 1 : ℕ) : ℝ) = (k j : ℝ) + 1 := by
      intro j
      push_cast
      ring
    simp only [hcast]
    have hub : Tendsto (fun j => 16 * |b - a| * (((k j : ℝ) + 1) / y j)) atTop (nhds 0) := by
      have h := hky.const_mul (16 * |b - a|)
      simpa using h
    refine squeeze_zero_norm' ?_ hub
    filter_upwards [hbound] with j hj
    have hk0 : (0 : ℝ) ≤ (k j : ℝ) + 1 := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk0]
    calc ((k j : ℝ) + 1) *
          |((b - y j) * (y j + a + 2 * c j)) / ((a - y j) * (y j + b + 2 * c j)) - 1|
        ≤ ((k j : ℝ) + 1) * (16 * |b - a| / y j) := mul_le_mul_of_nonneg_left hj hk0
      _ = 16 * |b - a| * (((k j : ℝ) + 1) / y j) := by ring
  exact tendsto_pow_of_tendsto_one hr1 hmr

end RHTower

end
