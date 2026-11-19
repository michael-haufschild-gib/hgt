import GaloisForLFunctions.RHTower.WeilConeSingularDeficitEnvelope
import GaloisForLFunctions.RHTower.XiHorizontalSlopeNearOne

/-!
# Counting the divisor of ξ by tangent disks

The disk estimate in Broucke–Révész, Proposition 4.1 (arXiv:2611.03356),
uses the real part of a resolvent at a point to the right of the disk.
For the completed zeta function the exterior zeros have positive weights.
This gives a finite-height estimate which also records the excess from zeros
strictly inside the tangent disk. All counts include multiplicities.
-/

noncomputable section
open Complex RHTower RHTower.WeilSpectral
namespace GaloisForLFunctions.ZeroConfigurationGeometry.Landau

/-- Multiplicity copies in the closed disk with centre `b + it` and radius `r`. -/
def diskCopies (b t r : ℝ) : Finset XiZeroCopy := by
  classical
  exact ((finite_xiZeroCopy_band t (abs_nonneg r)).toFinset).filter fun q =>
    (b - (q.1 : ℂ).re)^2 + (t - (q.1 : ℂ).im)^2 ≤ r^2

theorem mem_diskCopies {b t r : ℝ} {q : XiZeroCopy} :
    q ∈ diskCopies b t r ↔
      (b - (q.1 : ℂ).re)^2 + (t - (q.1 : ℂ).im)^2 ≤ r^2 := by
  classical
  simp only [diskCopies, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    and_iff_right_iff_imp]
  intro h
  exact sq_le_sq.mp (by nlinarith only [h, sq_nonneg (b - (q.1 : ℂ).re)])

/-- Exact signed gain of one zero over the unit cost in the tangent disk. -/
theorem tangent_excess {σ : ℝ} (hσ : 1 ≤ σ) (t r : ℝ) (q : XiZeroCopy) :
    2*r*copyPoisson σ t q - 1 =
      (r^2 - ((σ-r-(q.1 : ℂ).re)^2 + (t-(q.1 : ℂ).im)^2)) /
        ((σ-(q.1 : ℂ).re)^2 + (t-(q.1 : ℂ).im)^2) := by
  have hp : 0 < σ - (q.1 : ℂ).re := sub_pos.mpr ((xiZeroCopy_re_lt_one q).trans_le hσ)
  unfold copyPoisson
  have hd : 0 < (σ-(q.1 : ℂ).re)^2 + (t-(q.1 : ℂ).im)^2 := by positivity
  field_simp [hd.ne']
  ring

/-- A closed disk tangent at the observation point is exactly a Poisson superlevel set. -/
theorem mem_tangent_iff {σ : ℝ} (hσ : 1 ≤ σ) (t r : ℝ) (q : XiZeroCopy) :
    q ∈ diskCopies (σ-r) t r ↔ 1 ≤ 2*r*copyPoisson σ t q := by
  have hp : 0 < σ - (q.1 : ℂ).re := sub_pos.mpr ((xiZeroCopy_re_lt_one q).trans_le hσ)
  have hd : 0 < (σ-(q.1 : ℂ).re)^2 + (t-(q.1 : ℂ).im)^2 := by positivity
  rw [mem_diskCopies, ← sub_nonneg (b := 1), tangent_excess hσ,
    le_div_iff₀ hd, zero_mul, sub_nonneg]

private theorem partial_mass_le {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (S : Finset XiZeroCopy) :
    ∑ q ∈ S, copyPoisson σ t q ≤ (logDeriv xi ((σ : ℂ) + t*I)).re := by
  rw [re_logDeriv_xi_eq_tsum_copyPoisson hσ]
  exact (summable_copyPoisson hσ t).sum_le_tsum S fun q _ => (copyPoisson_pos hσ.le t q).le

/-- Interior gain and all exterior Poisson mass account for the entire slack
in the multiplicity bound. -/
theorem tangent_count_remainder {σ : ℝ} (hσ : 1 < σ) (t r : ℝ) :
    let S := diskCopies (σ-r) t r
    2*r*(logDeriv xi ((σ : ℂ) + t*I)).re - S.card =
      (∑ q ∈ S, (2*r*copyPoisson σ t q - 1)) +
        2*r*(∑' q : ((S : Set XiZeroCopy)ᶜ : Set XiZeroCopy), copyPoisson σ t q) := by
  intro S
  rw [re_logDeriv_xi_eq_tsum_copyPoisson hσ,
    ← (summable_copyPoisson hσ t).sum_add_tsum_compl (s := S), Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  simp only [Finset.sum_const, nsmul_one]
  ring

/-- Evaluate at distance `h ≥ r` to the right of the centre. The larger tangent
disk with diameter `h+r` covers the original disk. -/
theorem disk_count_le_resolvent {b t r h : ℝ} (hr : 0 ≤ r) (hrh : r ≤ h)
    (hs : 1 < b+h) :
    ((diskCopies b t r).card : ℝ) ≤ (h+r)*(logDeriv xi (((b+h : ℝ) : ℂ) + t*I)).re := by
  have hpt (q : XiZeroCopy) (hq : q ∈ diskCopies b t r) :
      1 ≤ (h+r)*copyPoisson (b+h) t q := by
    have hd := mem_diskCopies.mp hq
    have hx : b - (q.1 : ℂ).re ≤ r := by
      have hsq : (b - (q.1 : ℂ).re)^2 ≤ r^2 := by linarith only [hd, sq_nonneg (t - (q.1 : ℂ).im)]
      exact (le_abs_self _).trans ((sq_le_sq.mp hsq).trans_eq (abs_of_nonneg hr))
    have hd' : q ∈ diskCopies (b+h-(h+r)/2) t ((h+r)/2) := by
      rw [mem_diskCopies]
      nlinarith only [hd, mul_nonneg (sub_nonneg.mpr hrh) (sub_nonneg.mpr hx)]
    have hm := (mem_tangent_iff hs.le t ((h+r)/2) q).mp hd'
    linarith only [hm]
  calc ((diskCopies b t r).card : ℝ) = ∑ _q ∈ diskCopies b t r, (1 : ℝ) := by simp
    _ ≤ ∑ q ∈ diskCopies b t r, (h+r)*copyPoisson (b+h) t q := Finset.sum_le_sum hpt
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (partial_mass_le hs t _) (by linarith)

/-- Explicit count of zeros within radius `r` of the one-line. The evaluation
offset `h` is free and can be optimized for each radius and height. -/
theorem one_line_disk_count {t r h : ℝ} (ht : 200 ≤ t) (hr : 0 ≤ r) (hh : 0 < h)
    (hrh : r ≤ h) (hfar : 1+h ≤ t/32) :
    ((diskCopies 1 t r).card : ℝ) ≤
      (h+r)*(1/h + (Real.log (t/(2*Real.pi))/2 + 3)) := by
  have hσ : 1 < 1+h := by linarith
  have he := RHTower.DeBruijn.norm_logDeriv_xi_sub_horizontalSlope_le_near hσ hfar ht
  have hbound := (Complex.re_le_norm _).trans he
  rw [Complex.sub_re, horizontalSlope_re] at hbound
  refine (disk_count_le_resolvent hr hrh hσ).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
  rw [show 1+h-1 = h by ring] at hbound
  linarith only [hbound]

/-- On the tangent scale the additive pole cost is two at every height. -/
theorem one_line_disk_count_at_radius {t r : ℝ} (ht : 200 ≤ t) (hr : 0 < r) (hr1 : r ≤ 1) :
    ((diskCopies 1 t r).card : ℝ) ≤ 2 + r*(Real.log (t/(2*Real.pi)) + 6) := by
  refine (one_line_disk_count ht hr.le hr le_rfl (by linarith)).trans_eq ?_
  field_simp [hr.ne']
  ring

/-- At radius `u²/L`, where `L` is the smooth slope plus three, the
optimizing offset is `u/L`. The pole cost tends to one as the radius shrinks. -/
theorem one_line_disk_count_optimized {t u : ℝ} (ht : 200 ≤ t) (hu : 0 < u)
    (hu1 : u ≤ 1) :
    let L := Real.log (t/(2*Real.pi))/2 + 3
    ((diskCopies 1 t (u^2/L)).card : ℝ) ≤ (1+u)^2 := by
  intro L
  have hlog : 0 ≤ Real.log (t/(2*Real.pi)) :=
    Real.log_nonneg ((one_le_div₀ (by positivity)).mpr (by linarith [Real.pi_lt_four]))
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hp : 0 < L := zero_lt_one.trans_le hL
  have hsmall : u/L ≤ 1 := (div_le_one hp).mpr (hu1.trans hL)
  refine (one_line_disk_count ht (div_nonneg (sq_nonneg u) hp.le) (div_pos hu hp)
    (div_le_div_of_nonneg_right (by nlinarith only [mul_nonneg hu.le (sub_nonneg.mpr hu1)]) hp.le)
    (by linarith)).trans_eq ?_
  change (u/L+u^2/L)*(1/(u/L)+L) = (1+u)^2
  field_simp [hp.ne', hu.ne']

/-- Below the radius `(√2-1)²/L`, the disk contains at most one zero,
counted with multiplicity. -/
theorem one_line_disk_at_most_one {t u : ℝ} (ht : 200 ≤ t) (hu : 0 < u)
    (hsmall : u < Real.sqrt 2 - 1) :
    (diskCopies 1 t (u^2/(Real.log (t/(2*Real.pi))/2 + 3))).card ≤ 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hu1 : u ≤ 1 := by nlinarith only [hs, hsmall]
  have hstrict : (1 + u)^2 < 2 := by
    calc (1 + u)^2 < (Real.sqrt 2)^2 := by
           apply sq_lt_sq'
           · linarith [Real.sqrt_nonneg 2]
           · linarith
         _ = 2 := hs
  have hcard := (one_line_disk_count_optimized ht hu hu1).trans_lt hstrict
  exact Nat.le_of_lt_succ (by exact_mod_cast hcard)

#print axioms mem_diskCopies
#print axioms tangent_excess
#print axioms mem_tangent_iff
#print axioms tangent_count_remainder
#print axioms disk_count_le_resolvent
#print axioms one_line_disk_count
#print axioms one_line_disk_count_at_radius
#print axioms one_line_disk_count_optimized
#print axioms one_line_disk_at_most_one
end GaloisForLFunctions.ZeroConfigurationGeometry.Landau
