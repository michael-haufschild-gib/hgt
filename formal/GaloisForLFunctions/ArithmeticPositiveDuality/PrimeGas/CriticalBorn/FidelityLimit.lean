import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.ElementaryWave
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.FidelityMass

/-! # Reflected elementary heat states become orthogonal away from isometric composition -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter Real
open scoped Topology

private def overlapMass (a x : ℝ) := (powerMass 0 x)^2 / (powerMass a x * powerMass (-a) x)

private theorem even_overlap (a x : ℝ) : overlapMass (-a) x = overlapMass a x := by
  simp only [overlapMass,neg_neg,mul_comm]

private theorem abs_overlap (s : ℂ) (x : ℝ) :
    reflectedFidelity s x = overlapMass |1-2*s.re| x := by
  rw [reflectedFidelity_eq]
  by_cases h : 0≤1-2*s.re
  · rw [abs_of_nonneg h,overlapMass]
  · rw [abs_of_neg (lt_of_not_ge h),even_overlap,overlapMass]

private theorem scaled_overlap {d : ℝ} (hd : 0<d) (hd' : d<1) :
    Tendsto (fun x => overlapMass d x*x^d / ((log (log x))^2*log x)) atTop (𝓝 (d/primeTotal (-d))) := by
  have ht := primeTotal_pos (neg_lt_zero.mpr hd)
  have h := ((harmonic_mass_ratio.pow 2).const_mul d).div
    ((powerMass_asymptotic hd hd').mul (powerMass_limit (neg_lt_zero.mpr hd))) (by simpa only [one_mul] using ht.ne')
  simp only [one_pow,mul_one,one_mul] at h
  apply h.congr'
  filter_upwards [tendsto_log_atTop.eventually_gt_atTop 1,eventually_gt_atTop (1:ℝ)] with x hl hx
  change d*(powerMass 0 x/log (log x))^2 /
    ((powerMass d x*(d*log x)/x^d)*powerMass (-d) x) = _
  simp only [overlapMass]
  field_simp [hd.ne',(log_pos hl).ne',(log_pos hx).ne',(rpow_pos_of_pos (one_pos.trans hx) d).ne',
    (powerMass_pos d x).ne',(powerMass_pos (-d) x).ne']

/-- The exact decay rate in the open strip recovers the distance from
the composition line and the convergent prime sum on the reflected side. -/
theorem reflectedFidelity_asymptotic (s : ℂ) (hd : 0 < |1-2*s.re|) (hd' : |1-2*s.re| < 1) :
    Tendsto (fun x => reflectedFidelity s x*x ^ |1-2*s.re| / ((log (log x))^2*log x))
      atTop (𝓝 (|1-2*s.re| / primeTotal (-|1-2*s.re|))) := by
  simpa only [abs_overlap] using scaled_overlap hd hd'

private theorem small_overlap_vanishes {b : ℝ} (hb : 0<b) (hb' : b<1) :
    Tendsto (overlapMass b) atTop (𝓝 0) := by
  have lim := (scaled_overlap hb hb').mul (log_prefactor_vanishes hb)
  rw [mul_zero] at lim
  apply lim.congr'
  filter_upwards [tendsto_log_atTop.eventually_gt_atTop 1,eventually_gt_atTop (1:ℝ)] with x hl hx
  field_simp [(log_pos hl).ne',(log_pos hx).ne',(rpow_pos_of_pos (one_pos.trans hx) b).ne']

private theorem positive_overlap_vanishes {d : ℝ} (hd : 0<d) : Tendsto (overlapMass d) atTop (𝓝 0) := by
  let b := min d (1/2)
  have hb : 0<b := lt_min hd (by norm_num)
  have hb' : b<1 := (min_le_right _ _).trans_lt (by norm_num)
  have ht := (powerMass_limit (neg_lt_zero.mpr hb)).div (powerMass_limit (neg_lt_zero.mpr hd))
    (primeTotal_pos (neg_lt_zero.mpr hd)).ne'
  have upper := (small_overlap_vanishes hb hb').mul ht
  rw [zero_mul] at upper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds upper
  · exact Eventually.of_forall fun x => div_nonneg (sq_nonneg _)
      (mul_pos (powerMass_pos d x) (powerMass_pos (-d) x)).le
  · apply Eventually.of_forall
    intro x
    change overlapMass d x ≤ overlapMass b x * (powerMass (-b) x / powerMass (-d) x)
    calc
      overlapMass d x ≤ (powerMass 0 x)^2/(powerMass b x * powerMass (-d) x) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos (powerMass_pos b x) (powerMass_pos _ x))
          (mul_le_mul_of_nonneg_right (powerMass_index_mono (min_le_left _ _) x) (powerMass_pos _ x).le)
      _ = _ := by
        simp only [overlapMass]
        field_simp [(powerMass_pos b x).ne',(powerMass_pos (-b) x).ne',(powerMass_pos (-d) x).ne']

/-- The two normalized quantum states coincide on the isometry line and
have vanishing transition probability at every other fixed real part. -/
theorem reflectedFidelity_limit (s : ℂ) : Tendsto (reflectedFidelity s) atTop
    (𝓝 (if s.re=1/2 then 1 else 0)) := by
  by_cases eq : s.re=1/2
  · rw [if_pos eq]
    apply tendsto_const_nhds.congr
    intro x
    rw [reflectedFidelity_eq,eq,show (1:ℝ)-2*(1/2)=0 by norm_num,neg_zero,sq,div_self
      (mul_ne_zero (powerMass_pos 0 x).ne' (powerMass_pos 0 x).ne')]
  · rw [if_neg eq]
    have nz : 1-2*s.re ≠ 0 := fun h => eq (by linarith only [h])
    exact (positive_overlap_vanishes (abs_pos.mpr nz)).congr (fun x => (abs_overlap s x).symm)

theorem fidelity_one_iff_split (s : ℂ) : Tendsto (reflectedFidelity s) atTop (𝓝 1) ↔
    ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  rw [split_isometric_iff]
  have lim := reflectedFidelity_limit s
  constructor
  · intro h
    by_contra off
    rw [if_neg off] at lim
    exact zero_ne_one (tendsto_nhds_unique lim h)
  · intro eq
    simpa only [if_pos eq] using lim

/-- RH asks whether the normalized reflected heat states avoid
asymptotic orthogonality at every open-strip partition zero. -/
theorem rh_iff_reflected_nonorthogonality : RiemannHypothesis ↔
    ∀ s : OpenStrip, riemannZeta s.val=0 → ¬ Tendsto (reflectedFidelity s.val) atTop (𝓝 0) := by
  rw [rh_iff_unit_clock]
  constructor
  · intro h s hz vanish
    have one := (fidelity_one_iff_split s.val).mpr
      ((elementary_haar_iff_split s.val one_ne_zero).mp (h s hz))
    exact zero_ne_one (tendsto_nhds_unique vanish one)
  · intro h s hz
    apply (haar_iff_half _ one_ne_zero).mpr
    by_contra off
    exact h s hz (by simpa only [if_neg off] using reflectedFidelity_limit s.val)

#print axioms reflectedFidelity_asymptotic
#print axioms reflectedFidelity_limit
#print axioms fidelity_one_iff_split
#print axioms rh_iff_reflected_nonorthogonality

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
