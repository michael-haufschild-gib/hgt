import GaloisForLFunctions.HTGeometry.IndexedBlaschkeMultiplier
import GaloisForLFunctions.Bottcher.DiskSchwarzPick
import Mathlib.Analysis.Calculus.DSlope

open Complex Filter Topology Metric Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A disk Blaschke factor maps two strict disk points to a strict disk point. -/
theorem norm_blaschkeFactor_lt_one {a z : ℂ}
    (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖blaschkeFactor a z‖ < 1 := by
  have hden : 1 - (starRingEnd ℂ) a * z ≠ 0 :=
    blaschkeFactor_den_ne_zero ha hz.le
  rw [blaschkeFactor, norm_div, div_lt_one (norm_pos_iff.mpr hden)]
  have ha' : 0 < 1 - (a.re ^ 2 + a.im ^ 2) := by
    nlinarith [Complex.sq_norm a, Complex.normSq_apply a, norm_nonneg a]
  have hz' : 0 < 1 - (z.re ^ 2 + z.im ^ 2) := by
    nlinarith [Complex.sq_norm z, Complex.normSq_apply z, norm_nonneg z]
  have hsq : ‖z - a‖ ^ 2 < ‖1 - (starRingEnd ℂ) a * z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im]
    nlinarith [mul_pos ha' hz']
  nlinarith [norm_nonneg (z - a), norm_nonneg (1 - (starRingEnd ℂ) a * z)]

/-- Inverse source automorphism for the disk Blaschke coordinate based at `a`. -/
def diskBlaschkeInverse (a η : ℂ) : ℂ :=
  (a + η) / (1 + (starRingEnd ℂ) a * η)

theorem norm_diskBlaschkeInverse_lt_one {a η : ℂ}
    (ha : ‖a‖ < 1) (hη : ‖η‖ < 1) :
    ‖diskBlaschkeInverse a η‖ < 1 := by
  have hden := Bottcher.one_add_conj_mul_ne_zero_of_norm_lt_one ha hη
  have hid := Bottcher.one_sub_norm_sq_mobius (a := a) (η := η) hden
  have hnum : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖η‖ ^ 2) := by
    apply mul_pos <;> nlinarith [norm_nonneg a, norm_nonneg η]
  have hdenpos : 0 < ‖1 + (starRingEnd ℂ) a * η‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hden) 2
  have : 0 < 1 - ‖diskBlaschkeInverse a η‖ ^ 2 := by
    change 0 < 1 - ‖(a + η) / (1 + (starRingEnd ℂ) a * η)‖ ^ 2
    rw [hid]
    exact div_pos hnum hdenpos
  nlinarith [norm_nonneg (diskBlaschkeInverse a η)]

theorem differentiableOn_diskBlaschkeInverse {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (diskBlaschkeInverse a) (ball 0 1) := by
  intro η hη
  have hη' : ‖η‖ < 1 := by simpa [mem_ball, dist_zero_right] using hη
  have hden := Bottcher.one_add_conj_mul_ne_zero_of_norm_lt_one ha hη'
  apply DifferentiableAt.differentiableWithinAt
  unfold diskBlaschkeInverse
  fun_prop (disch := exact hden)

/-- Schwarz--Pick division estimate at one zero of a bounded analytic disk multiplier. -/
theorem DiskMultiplier.norm_fn_le_bd_mul_norm_blaschkeFactor
    (φ : DiskMultiplier) {a : ℂ} (ha : ‖a‖ < 1) (hzero : φ.fn a = 0)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖φ.fn z‖ ≤ φ.bd * ‖blaschkeFactor a z‖ := by
  by_cases hbd0 : φ.bd = 0
  · have hzmem : z ∈ ball (0 : ℂ) 1 := by simpa [mem_ball, dist_zero_right]
    have hφz : φ.fn z = 0 := norm_eq_zero.mp (by
      apply le_antisymm
      · simpa [hbd0] using φ.bd_le z hzmem
      · exact norm_nonneg _)
    simp [hφz, hbd0]
  have hbdpos : 0 < φ.bd := lt_of_le_of_ne φ.bd_nonneg (Ne.symm hbd0)
  let T : ℂ → ℂ := diskBlaschkeInverse a
  let g : ℂ → ℂ := fun η => φ.fn (T η) / (φ.bd : ℂ)
  have hTdisk : ∀ η ∈ ball (0 : ℂ) 1, T η ∈ ball (0 : ℂ) 1 := by
    intro η hη
    rw [mem_ball, dist_zero_right] at hη ⊢
    exact norm_diskBlaschkeInverse_lt_one ha hη
  have hgdiff : DifferentiableOn ℂ g (ball 0 1) := by
    intro η hη
    have hTη := hTdisk η hη
    have hφat := (φ.diff (T η) hTη).differentiableAt
      (isOpen_ball.mem_nhds hTη)
    have hTat := (differentiableOn_diskBlaschkeInverse ha η hη).differentiableAt
      (isOpen_ball.mem_nhds hη)
    exact (hφat.comp η hTat).div_const (φ.bd : ℂ) |>.differentiableWithinAt
  have hgbd : ∀ η ∈ ball (0 : ℂ) 1, ‖g η‖ ≤ 1 := by
    intro η hη
    have hφ := φ.bd_le (T η) (hTdisk η hη)
    dsimp [g]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hbdpos, div_le_one hbdpos]
    exact hφ
  have hT0 : T 0 = a := by simp [T, diskBlaschkeInverse]
  have hg0 : g 0 = 0 := by simp [g, hT0, hzero]
  let η : ℂ := blaschkeFactor a z
  have hη : ‖η‖ < 1 := norm_blaschkeFactor_lt_one ha hz
  have hηmem : η ∈ ball (0 : ℂ) 1 := by simpa [mem_ball, dist_zero_right]
  have hschwarz := Bottcher.blaschke_lift_norm_le_dist_div
    (g := g) (c := 0) (z := η) (R := 1) zero_lt_one hgdiff hgbd
    (by simp [hg0]) hηmem
  have hden : 1 - (starRingEnd ℂ) a * z ≠ 0 :=
    blaschkeFactor_den_ne_zero ha hz.le
  have hTη : T η = z := by
    simpa [T, η, diskBlaschkeInverse, blaschkeFactor] using
      Bottcher.mobius_of_blaschke (a := a) (w := z) ha hden
  rw [hg0] at hschwarz
  simp only [sub_zero, map_zero, zero_mul, sub_zero, div_one, dist_zero_right] at hschwarz
  dsimp [g] at hschwarz
  rw [hTη, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hbdpos] at hschwarz
  have hmul := (div_le_iff₀ hbdpos).mp hschwarz
  simpa [η, mul_comm] using hmul

/-- Analytic quotient after removing one normalized Blaschke zero. -/
def DiskMultiplier.removeNormalizedBlaschkeZeroFn
    (φ : DiskMultiplier) (a z : ℂ) : ℂ :=
  if a = 0 then dslope φ.fn a z
  else -a / (‖a‖ : ℂ) * (1 - (starRingEnd ℂ) a * z) * dslope φ.fn a z

theorem DiskMultiplier.normalizedBlaschkeFactor_mul_removeNormalizedBlaschkeZeroFn
    (φ : DiskMultiplier) {a : ℂ} (ha : ‖a‖ < 1) (hzero : φ.fn a = 0)
    {z : ℂ} (hz : ‖z‖ < 1) :
    normalizedBlaschkeFactor a z * φ.removeNormalizedBlaschkeZeroFn a z = φ.fn z := by
  by_cases ha0 : a = 0
  · subst a
    rw [normalizedBlaschkeFactor, if_pos rfl,
      DiskMultiplier.removeNormalizedBlaschkeZeroFn, if_pos rfl]
    by_cases hz0 : z = 0
    · subst z
      simp [hzero]
    · rw [dslope_of_ne _ hz0, slope_def_field]
      rw [hzero, sub_zero]
      field_simp [hz0]
      ring
  · rw [normalizedBlaschkeFactor, if_neg ha0,
      DiskMultiplier.removeNormalizedBlaschkeZeroFn, if_neg ha0, blaschkeFactor]
    have hnorm : (‖a‖ : ℂ) ≠ 0 := by
      exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha0)
    by_cases hza : z = a
    · subst z
      simp [hzero]
    · have hden : 1 - (starRingEnd ℂ) a * z ≠ 0 :=
        blaschkeFactor_den_ne_zero ha hz.le
      have hden' : 1 - z * (starRingEnd ℂ) a ≠ 0 := by
        simpa [mul_comm] using hden
      rw [dslope_of_ne _ hza, slope_def_field, hzero, sub_zero]
      field_simp [ha0, hnorm, hden, hden', sub_ne_zero.mpr hza]

theorem norm_normalizedBlaschkeFactor_eq_norm_blaschkeFactor
    (a z : ℂ) :
    ‖normalizedBlaschkeFactor a z‖ = ‖blaschkeFactor a z‖ := by
  by_cases ha0 : a = 0
  · subst a
    simp [normalizedBlaschkeFactor, blaschkeFactor]
  rw [normalizedBlaschkeFactor, if_neg ha0, norm_mul, norm_neg, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a),
    div_self (norm_ne_zero_iff.mpr ha0), one_mul]

theorem DiskMultiplier.differentiableOn_removeNormalizedBlaschkeZeroFn
    (φ : DiskMultiplier) {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (φ.removeNormalizedBlaschkeZeroFn a) (ball 0 1) := by
  have haMem : a ∈ ball (0 : ℂ) 1 := by simpa [mem_ball, dist_zero_right]
  have hds : DifferentiableOn ℂ (dslope φ.fn a) (ball 0 1) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds haMem)).mpr φ.diff
  by_cases ha0 : a = 0
  · subst a
    rw [show φ.removeNormalizedBlaschkeZeroFn 0 = dslope φ.fn 0 by
      funext z
      simp [DiskMultiplier.removeNormalizedBlaschkeZeroFn]]
    exact hds
  · rw [show φ.removeNormalizedBlaschkeZeroFn a = fun z =>
        -a / (‖a‖ : ℂ) * (1 - (starRingEnd ℂ) a * z) * dslope φ.fn a z by
      funext z
      simp only [DiskMultiplier.removeNormalizedBlaschkeZeroFn, if_neg ha0]]
    exact ((differentiableOn_const (-a / (‖a‖ : ℂ))).mul
      ((differentiableOn_const 1).sub
        ((differentiableOn_const ((starRingEnd ℂ) a)).mul differentiableOn_id))).mul hds

theorem DiskMultiplier.norm_removeNormalizedBlaschkeZeroFn_le_bd
    (φ : DiskMultiplier) {a : ℂ} (ha : ‖a‖ < 1) (hzero : φ.fn a = 0)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖φ.removeNormalizedBlaschkeZeroFn a z‖ ≤ φ.bd := by
  have haMem : a ∈ ball (0 : ℂ) 1 := by simpa [mem_ball, dist_zero_right]
  have hdiff := φ.differentiableOn_removeNormalizedBlaschkeZeroFn ha
  by_cases hza : z = a
  · subst z
    have htend : Tendsto (fun w => ‖φ.removeNormalizedBlaschkeZeroFn a w‖)
        (𝓝[≠] a) (𝓝 ‖φ.removeNormalizedBlaschkeZeroFn a a‖) :=
      ((hdiff a haMem).differentiableAt (isOpen_ball.mem_nhds haMem)).continuousAt.norm.tendsto.mono_left
        inf_le_left
    apply le_of_tendsto htend
    have hball : ∀ᶠ w in 𝓝[≠] a, w ∈ ball (0 : ℂ) 1 :=
      Filter.Eventually.filter_mono inf_le_left (isOpen_ball.mem_nhds haMem)
    filter_upwards [hball, self_mem_nhdsWithin] with w hw hwa
    have hwlt : ‖w‖ < 1 := by simpa [mem_ball, dist_zero_right] using hw
    have hBne : normalizedBlaschkeFactor a w ≠ 0 := by
      rw [ne_eq, normalizedBlaschkeFactor_eq_zero_iff ha hwlt.le]
      exact hwa
    have hBpos : 0 < ‖normalizedBlaschkeFactor a w‖ := norm_pos_iff.mpr hBne
    apply (mul_le_mul_iff_of_pos_left hBpos).mp
    calc
      ‖normalizedBlaschkeFactor a w‖ *
          ‖φ.removeNormalizedBlaschkeZeroFn a w‖ = ‖φ.fn w‖ := by
        rw [← norm_mul,
          φ.normalizedBlaschkeFactor_mul_removeNormalizedBlaschkeZeroFn ha hzero hwlt]
      _ ≤ φ.bd * ‖blaschkeFactor a w‖ :=
        φ.norm_fn_le_bd_mul_norm_blaschkeFactor ha hzero hwlt
      _ = ‖normalizedBlaschkeFactor a w‖ * φ.bd := by
        rw [norm_normalizedBlaschkeFactor_eq_norm_blaschkeFactor]
        ring
  · have hBne : normalizedBlaschkeFactor a z ≠ 0 := by
      rw [ne_eq, normalizedBlaschkeFactor_eq_zero_iff ha hz.le]
      exact hza
    have hBpos : 0 < ‖normalizedBlaschkeFactor a z‖ := norm_pos_iff.mpr hBne
    apply (mul_le_mul_iff_of_pos_left hBpos).mp
    calc
      ‖normalizedBlaschkeFactor a z‖ *
          ‖φ.removeNormalizedBlaschkeZeroFn a z‖ = ‖φ.fn z‖ := by
        rw [← norm_mul,
          φ.normalizedBlaschkeFactor_mul_removeNormalizedBlaschkeZeroFn ha hzero hz]
      _ ≤ φ.bd * ‖blaschkeFactor a z‖ :=
        φ.norm_fn_le_bd_mul_norm_blaschkeFactor ha hzero hz
      _ = ‖normalizedBlaschkeFactor a z‖ * φ.bd := by
        rw [norm_normalizedBlaschkeFactor_eq_norm_blaschkeFactor]
        ring

/-- Remove one prescribed zero by its normalized Blaschke factor without increasing the bound. -/
def DiskMultiplier.removeNormalizedBlaschkeZero
    (φ : DiskMultiplier) (a : ℂ) (ha : ‖a‖ < 1) (hzero : φ.fn a = 0) :
    DiskMultiplier where
  fn := φ.removeNormalizedBlaschkeZeroFn a
  diff := φ.differentiableOn_removeNormalizedBlaschkeZeroFn ha
  bd := φ.bd
  bd_nonneg := φ.bd_nonneg
  bd_le := fun z hz => φ.norm_removeNormalizedBlaschkeZeroFn_le_bd ha hzero
    (by simpa [mem_ball, dist_zero_right] using hz)

theorem DiskMultiplier.removeNormalizedBlaschkeZero_fn
    (φ : DiskMultiplier) (a : ℂ) (ha : ‖a‖ < 1) (hzero : φ.fn a = 0) (z : ℂ) :
    (φ.removeNormalizedBlaschkeZero a ha hzero).fn z =
      φ.removeNormalizedBlaschkeZeroFn a z := rfl

/-- Exact one-zero Blaschke factorization on the open disk. -/
theorem DiskMultiplier.normalizedBlaschkeFactor_mul_removeNormalizedBlaschkeZero
    (φ : DiskMultiplier) {a : ℂ} (ha : ‖a‖ < 1) (hzero : φ.fn a = 0)
    {z : ℂ} (hz : ‖z‖ < 1) :
    normalizedBlaschkeFactor a z *
        (φ.removeNormalizedBlaschkeZero a ha hzero).fn z = φ.fn z :=
  φ.normalizedBlaschkeFactor_mul_removeNormalizedBlaschkeZeroFn ha hzero hz

end

end GaloisForLFunctions.HTGeometry
