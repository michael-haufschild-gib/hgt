import GaloisForLFunctions.RHTower.SuzukiSafeShiftTransverseChargeBudget
import GaloisForLFunctions.HTGeometry.PairwiseVarianceIdentity

/-!
# A zero-charge anchor pays the cofinite transverse charge

One shifted Xi atom with vanishing transverse charge makes the whole response tail coercive.  Its
pairs with the other atoms are extracted from the nonnegative pairwise dispersion; each such pair
pays the transverse charge of its partner, because the charge-to-mass ratio is dominated by the
squared atom norm — which vanishes cofinitely — while the response slope gap tends to the anchor's
own fixed positive slope.  Hence there is a finite head outside which the complete charge is
covered by the Hilbert dispersion.
-/

open Filter

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The charge-to-mass ratio is dominated by the squared atom norm: the strict sector
`im² < re²` costs nothing beyond one factor. -/
theorem chargeDensity_div_mass_le_normSq {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    xiShiftedTransverseChargeDensity y q / xiShiftedResponseMass y q
      ≤ ‖xiShiftedReciprocalSquare y q‖ ^ 2 := by
  set z := xiShiftedReciprocalSquare y q with hz
  have hre : 0 < z.re := by
    simpa only [hz, xiShiftedResponseMass] using xiShiftedResponseMass_pos hy q
  have hsector : z.im ^ 2 < z.re ^ 2 := by
    simpa only [hz] using xiShiftedReciprocalSquare_im_sq_lt_re_sq hy q
  have hnorm : ‖z‖ ^ 2 = Complex.normSq z := by
    rw [Complex.sq_norm]
  have hval : xiShiftedTransverseChargeDensity y q / xiShiftedResponseMass y q
      = z.im ^ 2 * Complex.normSq z / z.re ^ 2 := by
    rw [xiShiftedTransverseChargeDensity, xiShiftedResponseMass, ← hz, div_div]
    ring_nf
  rw [hval, hnorm, div_le_iff₀ (by positivity)]
  have hns : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
  nlinarith [hsector, hns]

/-- **`(SR-64.10)`: one anchored pair pays one atom's charge.** -/
theorem anchor_pair_pays_charge {y : ℝ} (hy : 0 < y) {r q : XiZeroCopy} {A : ℝ} (hA : 0 ≤ A)
    (hslope : xiShiftedResponseSlope y q < xiShiftedResponseSlope y r / 2)
    (hsmall : A * ‖xiShiftedReciprocalSquare y q‖ ^ 2
      < xiShiftedResponseMass y r * xiShiftedResponseSlope y r ^ 2 / 4) :
    A * xiShiftedTransverseChargeDensity y q
      < xiShiftedResponseMass y q * xiShiftedResponseMass y r
        * (xiShiftedResponseSlope y q - xiShiftedResponseSlope y r) ^ 2 := by
  have hmq : 0 < xiShiftedResponseMass y q := xiShiftedResponseMass_pos hy q
  have hmr : 0 < xiShiftedResponseMass y r := xiShiftedResponseMass_pos hy r
  have hsq : 0 < xiShiftedResponseSlope y q := xiShiftedResponseSlope_pos hy q
  have hsr : 0 < xiShiftedResponseSlope y r := xiShiftedResponseSlope_pos hy r
  have hgap : xiShiftedResponseSlope y r / 2
      < xiShiftedResponseSlope y r - xiShiftedResponseSlope y q := by
    linarith
  have hgapsq : xiShiftedResponseSlope y r ^ 2 / 4
      < (xiShiftedResponseSlope y q - xiShiftedResponseSlope y r) ^ 2 := by
    nlinarith [hgap, hsr, hsq]
  have hratio : xiShiftedTransverseChargeDensity y q / xiShiftedResponseMass y q
      ≤ ‖xiShiftedReciprocalSquare y q‖ ^ 2 := chargeDensity_div_mass_le_normSq hy q
  have hcharge : A * xiShiftedTransverseChargeDensity y q
      ≤ A * ‖xiShiftedReciprocalSquare y q‖ ^ 2 * xiShiftedResponseMass y q := by
    have hstep : xiShiftedTransverseChargeDensity y q
        ≤ ‖xiShiftedReciprocalSquare y q‖ ^ 2 * xiShiftedResponseMass y q := by
      rw [div_le_iff₀ hmq] at hratio
      exact hratio
    nlinarith [hstep, hA, hmq]
  have hkey : A * ‖xiShiftedReciprocalSquare y q‖ ^ 2 * xiShiftedResponseMass y q
      < xiShiftedResponseMass y q * xiShiftedResponseMass y r
        * (xiShiftedResponseSlope y q - xiShiftedResponseSlope y r) ^ 2 := by
    have hstep : xiShiftedResponseMass y r * xiShiftedResponseSlope y r ^ 2 / 4
        < xiShiftedResponseMass y r
          * (xiShiftedResponseSlope y q - xiShiftedResponseSlope y r) ^ 2 := by
      nlinarith [hgapsq, hmr]
    nlinarith [hsmall, hstep, hmq]
  linarith

/-- **`(SR-64.1)`: the anchored cofinite payment.**  Outside a finite head, the complete shifted
transverse charge is covered by the Hilbert response dispersion. -/
theorem exists_finset_anchor_payment {y : ℝ} (hy : 0 < y) (r : XiZeroCopy) :
    ∃ F : Finset XiZeroCopy, r ∈ F ∧
      (∑' q : ({q : XiZeroCopy | q ∉ F} : Set XiZeroCopy),
          (∑' i : XiZeroCopy, xiShiftedResponseMass y i)
            * xiShiftedTransverseChargeDensity y (q : XiZeroCopy))
        ≤ xiShiftedResponseHilbertDispersion y := by
  classical
  set A : ℝ := ∑' i : XiZeroCopy, xiShiftedResponseMass y i with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact tsum_nonneg fun i => (xiShiftedResponseMass_pos hy i).le
  have hsr : 0 < xiShiftedResponseSlope y r := xiShiftedResponseSlope_pos hy r
  have hmr : 0 < xiShiftedResponseMass y r := xiShiftedResponseMass_pos hy r
  -- the two cofinite smallness conditions
  have hslope : ∀ᶠ q : XiZeroCopy in cofinite,
      xiShiftedResponseSlope y q < xiShiftedResponseSlope y r / 2 :=
    (tendsto_xiShiftedResponseSlope_cofinite_zero hy).eventually_lt_const (by linarith)
  have hnormzero : Tendsto (fun q : XiZeroCopy => A * ‖xiShiftedReciprocalSquare y q‖ ^ 2)
      cofinite (nhds 0) := by
    have hnorm : Tendsto (fun q : XiZeroCopy => ‖xiShiftedReciprocalSquare y q‖)
        cofinite (nhds 0) := by
      simpa using (summable_xiShiftedReciprocalSquare_pow hy.le 0).tendsto_cofinite_zero.norm
    have hsq : Tendsto (fun q : XiZeroCopy => ‖xiShiftedReciprocalSquare y q‖ ^ 2)
        cofinite (nhds 0) := by
      simpa using hnorm.pow 2
    have := hsq.const_mul A
    simpa using this
  have hsmall : ∀ᶠ q : XiZeroCopy in cofinite,
      A * ‖xiShiftedReciprocalSquare y q‖ ^ 2
        < xiShiftedResponseMass y r * xiShiftedResponseSlope y r ^ 2 / 4 :=
    hnormzero.eventually_lt_const (by positivity)
  have hfin : {q : XiZeroCopy | ¬ (xiShiftedResponseSlope y q
      < xiShiftedResponseSlope y r / 2 ∧ A * ‖xiShiftedReciprocalSquare y q‖ ^ 2
        < xiShiftedResponseMass y r * xiShiftedResponseSlope y r ^ 2 / 4)}.Finite :=
    Filter.eventually_cofinite.mp (hslope.and hsmall)
  refine ⟨insert r hfin.toFinset, Finset.mem_insert_self _ _, ?_⟩
  set F : Finset XiZeroCopy := insert r hfin.toFinset with hFdef
  set S : Set XiZeroCopy := {q : XiZeroCopy | q ∉ F} with hSdef
  have hrS : r ∉ S := by
    rw [hSdef]
    simp [hFdef]
  have hpay : ∀ q : S,
      A * xiShiftedTransverseChargeDensity y (q : XiZeroCopy)
        ≤ xiShiftedResponseMass y (q : XiZeroCopy) * xiShiftedResponseMass y r
          * (xiShiftedResponseSlope y (q : XiZeroCopy) - xiShiftedResponseSlope y r) ^ 2 := by
    intro q
    have hq : (q : XiZeroCopy) ∉ F := q.2
    have hq0 : (q : XiZeroCopy) ∉ hfin.toFinset := fun h => hq (by
      rw [hFdef]
      exact Finset.mem_insert_of_mem h)
    have hmem : (q : XiZeroCopy) ∈ {x | xiShiftedResponseSlope y x
        < xiShiftedResponseSlope y r / 2 ∧ A * ‖xiShiftedReciprocalSquare y x‖ ^ 2
        < xiShiftedResponseMass y r * xiShiftedResponseSlope y r ^ 2 / 4} := by
      by_contra hcon
      exact hq0 (hfin.mem_toFinset.mpr hcon)
    exact le_of_lt (anchor_pair_pays_charge hy hA0 hmem.1 hmem.2)
  -- summability on the tail
  have hsumcharge : Summable fun q : S =>
      A * xiShiftedTransverseChargeDensity y (q : XiZeroCopy) :=
    ((summable_xiShiftedTransverseChargeDensity hy).subtype S).mul_left A
  have hsumpair : Summable fun q : S =>
      xiShiftedResponseMass y (q : XiZeroCopy) * xiShiftedResponseMass y r
        * (xiShiftedResponseSlope y (q : XiZeroCopy) - xiShiftedResponseSlope y r) ^ 2 := by
    have hglobal : Summable fun q : XiZeroCopy =>
        xiShiftedResponseMass y q * xiShiftedResponseMass y r
          * (xiShiftedResponseSlope y q - xiShiftedResponseSlope y r) ^ 2 := by
      have hexp : ∀ q : XiZeroCopy,
          xiShiftedResponseMass y q * xiShiftedResponseMass y r
            * (xiShiftedResponseSlope y q - xiShiftedResponseSlope y r) ^ 2
            = xiShiftedResponseMass y r *
              (xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ 2
                - 2 * xiShiftedResponseSlope y r
                  * (xiShiftedResponseMass y q * xiShiftedResponseSlope y q)
                + xiShiftedResponseSlope y r ^ 2 * xiShiftedResponseMass y q) := by
        intro q
        ring
      refine (Summable.congr ?_ fun q => (hexp q).symm)
      exact (((summable_xiShiftedResponseMass_mul_slope_sq hy).sub
        ((summable_xiShiftedResponseMass_mul_slope hy).mul_left
          (2 * xiShiftedResponseSlope y r))).add
        ((summable_xiShiftedResponseMass hy.le).mul_left
          (xiShiftedResponseSlope y r ^ 2))).mul_left _
    exact hglobal.subtype S
  have hcompare := Summable.tsum_le_tsum hpay hsumcharge hsumpair
  have hanchor := tsum_anchor_pairs_le (a := xiShiftedResponseMass y)
    (τ := xiShiftedResponseSlope y) (summable_xiShiftedResponseMass hy.le)
    (summable_xiShiftedResponseMass_mul_slope hy)
    (summable_xiShiftedResponseMass_mul_slope_sq hy)
    (fun i => (xiShiftedResponseMass_pos hy i).le) r hrS hsumpair
  have hH : xiShiftedResponseHilbertDispersion y
      = (∑' i : XiZeroCopy, xiShiftedResponseMass y i)
          * (∑' i : XiZeroCopy, xiShiftedResponseMass y i * xiShiftedResponseSlope y i ^ 2)
        - (∑' i : XiZeroCopy, xiShiftedResponseMass y i * xiShiftedResponseSlope y i) ^ 2 := by
    rw [xiShiftedResponseHilbertDispersion, tsum_xiShiftedResponseMass_eq_moment_re hy.le,
      tsum_xiShiftedResponseMass_mul_slope_eq_moment_re hy]
  rw [hH]
  refine le_trans (le_of_eq ?_) (le_trans hcompare hanchor)
  refine tsum_congr fun q => rfl

/-- **`(SR-64.12)`: a charge-free head closes the minor.**  If the finite head produced by the
anchored payment carries no transverse charge, the complete charge is covered and the safe-shift
Hankel minor is nonnegative. -/
theorem transverseCharge_le_dispersion_of_chargeFree_head {y : ℝ} (hy : 0 < y)
    {F : Finset XiZeroCopy}
    (hpay : (∑' q : ({q : XiZeroCopy | q ∉ F} : Set XiZeroCopy),
        (∑' i : XiZeroCopy, xiShiftedResponseMass y i)
          * xiShiftedTransverseChargeDensity y (q : XiZeroCopy))
      ≤ xiShiftedResponseHilbertDispersion y)
    (hzero : ∀ q ∈ F, xiShiftedTransverseChargeDensity y q = 0) :
    xiShiftedTransverseCharge y ≤ xiShiftedResponseHilbertDispersion y := by
  classical
  set A : ℝ := ∑' i : XiZeroCopy, xiShiftedResponseMass y i with hAdef
  have hsum := summable_xiShiftedTransverseChargeDensity hy
  have hsplit := hsum.sum_add_tsum_compl (s := F)
  have hheadzero : (∑ q ∈ F, xiShiftedTransverseChargeDensity y q) = 0 :=
    Finset.sum_eq_zero hzero
  rw [hheadzero, zero_add] at hsplit
  have hcompl : (↑F : Set XiZeroCopy)ᶜ = {q : XiZeroCopy | q ∉ F} := by
    ext q
    simp
  have htotal : (∑' q : XiZeroCopy, xiShiftedTransverseChargeDensity y q)
      = ∑' q : ({q : XiZeroCopy | q ∉ F} : Set XiZeroCopy),
          xiShiftedTransverseChargeDensity y (q : XiZeroCopy) := by
    rw [← hsplit, hcompl]
  have hcharge : xiShiftedTransverseCharge y
      = ∑' q : ({q : XiZeroCopy | q ∉ F} : Set XiZeroCopy),
          A * xiShiftedTransverseChargeDensity y (q : XiZeroCopy) := by
    rw [xiShiftedTransverseCharge, ← tsum_xiShiftedResponseMass_eq_moment_re hy.le, ← hAdef,
      htotal, tsum_mul_left]
  rw [hcharge]
  exact hpay

end

end RHTower
