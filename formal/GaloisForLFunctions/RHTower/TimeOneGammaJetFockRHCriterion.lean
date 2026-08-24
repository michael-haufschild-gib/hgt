import GaloisForLFunctions.RHTower.MeixnerRootPrimeLaplaceValueFrame
import GaloisForLFunctions.RHTower.MertensGradedCoronaPolarTower
import GaloisForLFunctions.RHTower.FactorialFockPoleDivergence
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence
import GaloisForLFunctions.RHTower.CentralReciprocalMoments

/-!
# Time-one Gamma prime-seam factorial-jet criterion

At time one, the Meixner weight moves the degree-one prime transform's Mertens pole to the
boundary of its convergence half-plane.  The reflected seam cancels exactly on the critical line.
Off the line, one translate reaches that boundary while the other stays regular, leaving residue
`±√2`.  This genuine boundary obstruction and the general factorial-Fock extension theorem give
the exact finite-jet boundedness criterion and its equivalent Xi-divisor formulation of RH.

The proof uses the original absolutely convergent prime transform along the inward real ray.  No
meromorphic-continuation assumption is needed.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The exact time-one weighted prime transform on the positive real axis. -/
theorem primeSeamTransform_one_ofReal_eq_timeOnePrimeLaplace {s : ℝ} (hs : 0 < s) :
    primeSeamTransform 1 (s : ℂ) =
      (timeOnePrimeLaplace (gradeSource 0) s : ℝ) := by
  rw [primeSeamTransform, timeOnePrimeLaplace]
  rw [show (∑' n : ℕ,
      meixnerShape 1 n * ((n : ℝ) * mertensPrimeWeight n) * gradeSource 0 n *
        (n : ℝ) ^ (-s)) =
      ∑' p : Nat.Primes,
        meixnerShape 1 (p : ℕ) * (((p : ℕ) : ℝ) * mertensPrimeWeight (p : ℕ)) *
          gradeSource 0 (p : ℕ) * (((p : ℕ) : ℝ) ^ (-s)) by
    classical
    let i : Nat.Primes → ℕ := fun p => (p : ℕ)
    have hi : Function.Injective i := Subtype.coe_injective
    have hsupp : Function.support (fun n : ℕ =>
        meixnerShape 1 n * ((n : ℝ) * mertensPrimeWeight n) * gradeSource 0 n *
          (n : ℝ) ^ (-s)) ⊆ Set.range i := by
      intro n hn
      by_contra hmem
      have hnp : ¬ n.Prime := fun hp => hmem ⟨⟨n, hp⟩, rfl⟩
      apply hn
      simp [mertensPrimeWeight, hnp]
    exact (hi.tsum_eq hsupp).symm]
  let q : Nat.Primes → ℝ := fun p =>
    meixnerShape 1 (p : ℕ) * (((p : ℕ) : ℝ) * mertensPrimeWeight (p : ℕ)) *
      gradeSource 0 (p : ℕ) * (((p : ℕ) : ℝ) ^ (-s))
  have hall : Summable (fun n : ℕ =>
      meixnerShape 1 n * ((n : ℝ) * mertensPrimeWeight n) * gradeSource 0 n *
        (n : ℝ) ^ (-s)) := by
    have h := (summable_timeOneCorrection_primeLogPowWeight 0 hs).mul_left (Real.sqrt 2)
    exact h.congr (fun n => by
      rw [timeOnePrimeLaplace_term, abelWeighted_gradeSource])
  have hsum : Summable q := hall.comp_injective
    (i := fun p : Nat.Primes => (p : ℕ)) Subtype.coe_injective
  calc
    ∑' p : Nat.Primes, (meixnerPrimeWeight 1 (p : ℕ) : ℂ) *
          (Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-((s : ℝ) : ℂ)) =
        ∑' p : Nat.Primes, ((q p : ℝ) : ℂ) := by
      apply tsum_congr
      intro p
      have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
      dsimp [q]
      rw [meixnerPrimeWeight, meixnerShape, mertensPrimeWeight, if_pos p.2,
        gradeSource, pow_zero]
      simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
      rw [Complex.ofReal_cpow hp0.le]
      push_cast
      field_simp [Nat.cast_ne_zero.mpr p.2.ne_zero]
    _ = ((∑' p : Nat.Primes, q p : ℝ) : ℂ) := by
      exact ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).map_tsum hsum).symm

/-- Complex form of the reflected-transform identity on its full convergence half-plane. -/
theorem meixnerPrimeSeamValue_eq_reflected_transform_complex
    {theta : ℝ} (htheta : 0 ≤ theta) {rho z : ℂ}
    (hleft : 1 < theta + (z + rho).re)
    (hright : 1 < theta + (z + 1 - (starRingEnd ℂ) rho).re) :
    meixnerPrimeSeamValue theta rho z =
      primeSeamTransform theta (z + rho) -
        primeSeamTransform theta (z + 1 - (starRingEnd ℂ) rho) := by
  have hs1 : Summable (meixnerPrimeSeamSummand theta (z + rho)) :=
    summable_meixnerPrimeSeamSummand htheta hleft
  have hs2 : Summable
      (meixnerPrimeSeamSummand theta (z + 1 - (starRingEnd ℂ) rho)) :=
    summable_meixnerPrimeSeamSummand htheta hright
  rw [meixnerPrimeSeamValue, LSeries_meixnerPrimeSeamCoeff_eq_tsum_primes,
    primeSeamTransform, primeSeamTransform]
  change (∑' p : Nat.Primes, meixnerPrimeSeamCoeff theta rho (p : ℕ) /
      ((p : ℕ) : ℂ) ^ z) =
    (∑' p : Nat.Primes, meixnerPrimeSeamSummand theta (z + rho) p) -
      ∑' p : Nat.Primes,
        meixnerPrimeSeamSummand theta (z + 1 - (starRingEnd ℂ) rho) p
  rw [← hs1.tsum_sub hs2]
  apply tsum_congr
  intro p
  simpa only [LSeries.term_of_ne_zero p.2.ne_zero] using
    LSeries_term_meixnerPrimeSeamCoeff_prime theta rho z p

/-- Left edge of the common time-one convergence half-plane. -/
def timeOneGammaSeamBoundary (rho : ℂ) : ℝ :=
  max (-rho.re) (rho.re - 1)

/-- Common convergence half-plane of both reflected time-one translates. -/
def timeOneGammaSeamDomain (rho : ℂ) : Set ℂ :=
  {z | timeOneGammaSeamBoundary rho < z.re}

/-- Actual time-one Gamma--Meixner reflected prime seam. -/
def timeOneGammaPrimeSeam (rho z : ℂ) : ℂ :=
  meixnerPrimeSeamValue 1 rho z

theorem isPreconnected_timeOneGammaSeamDomain (rho : ℂ) :
    IsPreconnected (timeOneGammaSeamDomain rho) := by
  exact (convex_halfSpace_re_gt (timeOneGammaSeamBoundary rho)).isPreconnected

theorem analyticOnNhd_timeOneGammaPrimeSeam (rho : ℂ) :
    AnalyticOnNhd ℂ (timeOneGammaPrimeSeam rho) (timeOneGammaSeamDomain rho) := by
  intro z hz
  change timeOneGammaSeamBoundary rho < z.re at hz
  let c : ℝ := (timeOneGammaSeamBoundary rho + z.re) / 2
  have hbc : timeOneGammaSeamBoundary rho < c := by
    dsimp [c]
    linarith
  have hcz : c < z.re := by
    dsimp [c]
    linarith
  have hleft0 : 0 < c + rho.re := by
    have hb := le_max_left (-rho.re) (rho.re - 1)
    dsimp [timeOneGammaSeamBoundary] at hbc
    linarith
  have hright0 : 0 < c + 1 - rho.re := by
    have hb := le_max_right (-rho.re) (rho.re - 1)
    dsimp [timeOneGammaSeamBoundary] at hbc
    linarith
  have hsum : LSeriesSummable (meixnerPrimeSeamCoeff 1 rho) (c : ℂ) := by
    apply lSeriesSummable_meixnerPrimeSeamCoeff (theta := 1) (rho := rho) (z := (c : ℂ))
      (by norm_num)
    · simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    · simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.one_re,
        Complex.conj_re]
      linarith
  have hab : LSeries.abscissaOfAbsConv (meixnerPrimeSeamCoeff 1 rho) < (z.re : EReal) :=
    lt_of_le_of_lt hsum.abscissaOfAbsConv_le (by exact_mod_cast hcz)
  exact LSeries_analyticOnNhd (meixnerPrimeSeamCoeff 1 rho) z hab

theorem timeOneGammaPrimeSeam_eq_reflected_transform
    {rho z : ℂ} (hz : z ∈ timeOneGammaSeamDomain rho) :
    timeOneGammaPrimeSeam rho z =
      primeSeamTransform 1 (z + rho) -
        primeSeamTransform 1 (z + 1 - (starRingEnd ℂ) rho) := by
  apply meixnerPrimeSeamValue_eq_reflected_transform_complex (by norm_num)
  · have hb := le_max_left (-rho.re) (rho.re - 1)
    simp only [timeOneGammaSeamDomain, Set.mem_setOf_eq] at hz
    dsimp [timeOneGammaSeamBoundary] at hz
    simp only [Complex.add_re]
    linarith
  · have hb := le_max_right (-rho.re) (rho.re - 1)
    simp only [timeOneGammaSeamDomain, Set.mem_setOf_eq] at hz
    dsimp [timeOneGammaSeamBoundary] at hz
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.conj_re]
    linarith

theorem timeOneGammaPrimeSeam_eq_zero_of_re_eq_half
    {rho : ℂ} (hrho : rho.re = 1 / 2) :
    timeOneGammaPrimeSeam rho = 0 := by
  funext z
  rw [timeOneGammaPrimeSeam, meixnerPrimeSeamValue]
  have hcoeff : meixnerPrimeSeamCoeff 1 rho = 0 := by
    funext n
    rw [meixnerPrimeSeamCoeff]
    by_cases hn : n.Prime
    · rw [dif_pos hn]
      have hreflect : rho = 1 - (starRingEnd ℂ) rho := by
        apply Complex.ext
        · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
          linarith
        · simp
      have hconj : (starRingEnd ℂ) rho = 1 - rho := by
        calc
          (starRingEnd ℂ) rho = (starRingEnd ℂ) (1 - (starRingEnd ℂ) rho) :=
            congrArg (starRingEnd ℂ) hreflect
          _ = 1 - rho := by simp
      have hcharge : orbitwiseNatPrimeSeamCharge n rho = 0 := by
        rw [orbitwiseNatPrimeSeamCharge, orbitwiseScaleSeamCharge, hconj, sub_self,
          mul_zero]
      rw [hcharge, map_zero, mul_zero]
      rfl
    · rw [dif_neg hn]
      rfl
  rw [hcoeff]
  change LSeries (0 : ℕ → ℂ) z = (0 : ℂ)
  rw [LSeries]
  have hterm : (fun n : ℕ => LSeries.term (0 : ℕ → ℂ) z n) = 0 := by
    funext n
    simp [LSeries.term]
  rw [hterm]
  exact tsum_zero

theorem tendsto_mul_shifted_timeOnePrimeLaplace {d : ℝ} (hd : 0 < d) :
    Tendsto (fun s : ℝ => s * timeOnePrimeLaplace (gradeSource 0) (d + s))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have harg : Tendsto (fun s : ℝ => d + s) (nhdsWithin 0 (Set.Ioi 0)) (nhds d) := by
    have h : ContinuousAt (fun s : ℝ => d + s) 0 := by fun_prop
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have hvalue : Tendsto
      (fun s : ℝ => timeOnePrimeLaplace (gradeSource 0) (d + s))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (timeOnePrimeLaplace (gradeSource 0) d)) :=
    (hasDerivAt_timeOnePrimeLaplace_gradeSource 0 hd).continuousAt.tendsto.comp harg
  have hzero : Tendsto (fun s : ℝ => s) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  simpa using hzero.mul hvalue

/-- On the right of the critical line, reflected translate carries residue `-√2`. -/
theorem tendsto_timeOneGammaPrimeSeam_right_residue
    {rho : ℂ} (hrho : 1 / 2 < rho.re) :
    Tendsto (fun s : ℝ =>
        (s : ℂ) * timeOneGammaPrimeSeam rho
          ((starRingEnd ℂ) rho - 1 + (s : ℂ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(Real.sqrt 2 : ℂ))) := by
  let d : ℝ := 2 * rho.re - 1
  have hd : 0 < d := by dsimp [d]; linarith
  have hshift := tendsto_mul_shifted_timeOnePrimeLaplace hd
  have hres : Tendsto (fun s : ℝ => s * timeOnePrimeLaplace (gradeSource 0) s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt 2)) := by
    simpa using tendsto_gradedTimeOnePrimeLaplace 0
  have hdiff : Tendsto (fun s : ℝ =>
      s * timeOnePrimeLaplace (gradeSource 0) (d + s) -
        s * timeOnePrimeLaplace (gradeSource 0) s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-Real.sqrt 2)) := by
    simpa using hshift.sub hres
  have hc : Tendsto (fun s : ℝ =>
      ((s * timeOnePrimeLaplace (gradeSource 0) (d + s) -
        s * timeOnePrimeLaplace (gradeSource 0) s : ℝ) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((-Real.sqrt 2 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto (-Real.sqrt 2)).comp hdiff
  have hlim : ((-Real.sqrt 2 : ℝ) : ℂ) = -(Real.sqrt 2 : ℂ) := by simp
  rw [hlim] at hc
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hspos : 0 < s := hs
  have hboundary : timeOneGammaSeamBoundary rho = rho.re - 1 := by
    rw [timeOneGammaSeamBoundary, max_eq_right]
    linarith
  have hz : (starRingEnd ℂ) rho - 1 + (s : ℂ) ∈ timeOneGammaSeamDomain rho := by
    rw [timeOneGammaSeamDomain, Set.mem_setOf_eq, hboundary]
    simp only [Complex.add_re, Complex.sub_re, Complex.conj_re, Complex.one_re,
      Complex.ofReal_re]
    linarith
  have hleft : (starRingEnd ℂ) rho - 1 + (s : ℂ) + rho = ((d + s : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.sub_re, Complex.conj_re, Complex.one_re,
        Complex.ofReal_re]
      dsimp [d]
      ring
    · simp
  have hright : (starRingEnd ℂ) rho - 1 + (s : ℂ) + 1 -
      (starRingEnd ℂ) rho = (s : ℂ) := by ring
  rw [timeOneGammaPrimeSeam_eq_reflected_transform hz, hleft, hright,
    primeSeamTransform_one_ofReal_eq_timeOnePrimeLaplace (by linarith),
    primeSeamTransform_one_ofReal_eq_timeOnePrimeLaplace hspos]
  push_cast
  ring

/-- On the left of the critical line, direct translate carries residue `+√2`. -/
theorem tendsto_timeOneGammaPrimeSeam_left_residue
    {rho : ℂ} (hrho : rho.re < 1 / 2) :
    Tendsto (fun s : ℝ =>
        (s : ℂ) * timeOneGammaPrimeSeam rho (-rho + (s : ℂ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt 2 : ℂ)) := by
  let d : ℝ := 1 - 2 * rho.re
  have hd : 0 < d := by dsimp [d]; linarith
  have hshift := tendsto_mul_shifted_timeOnePrimeLaplace hd
  have hres : Tendsto (fun s : ℝ => s * timeOnePrimeLaplace (gradeSource 0) s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt 2)) := by
    simpa using tendsto_gradedTimeOnePrimeLaplace 0
  have hdiff : Tendsto (fun s : ℝ =>
      s * timeOnePrimeLaplace (gradeSource 0) s -
        s * timeOnePrimeLaplace (gradeSource 0) (d + s))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt 2)) := by
    simpa using hres.sub hshift
  have hc : Tendsto (fun s : ℝ =>
      ((s * timeOnePrimeLaplace (gradeSource 0) s -
        s * timeOnePrimeLaplace (gradeSource 0) (d + s) : ℝ) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((Real.sqrt 2 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto (Real.sqrt 2)).comp hdiff
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hspos : 0 < s := hs
  have hboundary : timeOneGammaSeamBoundary rho = -rho.re := by
    rw [timeOneGammaSeamBoundary, max_eq_left]
    linarith
  have hz : -rho + (s : ℂ) ∈ timeOneGammaSeamDomain rho := by
    rw [timeOneGammaSeamDomain, Set.mem_setOf_eq, hboundary]
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
    linarith
  have hleft : -rho + (s : ℂ) + rho = (s : ℂ) := by ring
  have hright : -rho + (s : ℂ) + 1 - (starRingEnd ℂ) rho =
      ((d + s : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.one_re,
        Complex.conj_re, Complex.ofReal_re]
      dsimp [d]
      ring
    · simp
  rw [timeOneGammaPrimeSeam_eq_reflected_transform hz, hleft, hright,
    primeSeamTransform_one_ofReal_eq_timeOnePrimeLaplace hspos,
    primeSeamTransform_one_ofReal_eq_timeOnePrimeLaplace (by linarith)]
  push_cast
  ring

/-- Nonzero normalized residue on an inward real ray forbids analytic boundary element. -/
theorem noExtensionAt_of_right_ray_residue
    {Phi : ℂ → ℂ} {Omega : Set ℂ} {b L : ℂ}
    (hmem : ∀ s : ℝ, 0 < s → b + (s : ℂ) ∈ Omega)
    (hlim : Tendsto (fun s : ℝ => (s : ℂ) * Phi (b + (s : ℂ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L))
    (hL : L ≠ 0) :
    NoExtensionAt Phi Omega b := by
  rintro ⟨U, g, hUopen, hbU, hgan, hgeq⟩
  have hpath : Tendsto (fun s : ℝ => b + (s : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds b) := by
    have h : ContinuousAt (fun s : ℝ => b + (s : ℂ)) 0 := by fun_prop
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have hg : Tendsto (fun s : ℝ => g (b + (s : ℂ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (g b)) :=
    (hgan b hbU).continuousAt.tendsto.comp hpath
  have hs : Tendsto (fun s : ℝ => (s : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    exact (Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hzero : Tendsto (fun s : ℝ => (s : ℂ) * g (b + (s : ℂ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hs.mul hg
  have hU : ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0), b + (s : ℂ) ∈ U :=
    hpath.eventually (hUopen.mem_nhds hbU)
  have heq : (fun s : ℝ => (s : ℂ) * g (b + (s : ℂ))) =ᶠ[
      nhdsWithin 0 (Set.Ioi 0)]
      fun s : ℝ => (s : ℂ) * Phi (b + (s : ℂ)) := by
    filter_upwards [hU, self_mem_nhdsWithin] with s hsU hspos
    rw [hgeq (b + (s : ℂ)) ⟨hsU, hmem s hspos⟩]
  have hzero' : Tendsto (fun s : ℝ => (s : ℂ) * Phi (b + (s : ℂ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := hzero.congr' heq
  exact hL (tendsto_nhds_unique hlim hzero')

theorem timeOneGammaPrimeSeam_noExtensionAt_of_re_gt_half
    {rho : ℂ} (hrho : 1 / 2 < rho.re) :
    NoExtensionAt (timeOneGammaPrimeSeam rho) (timeOneGammaSeamDomain rho)
      ((starRingEnd ℂ) rho - 1) := by
  apply noExtensionAt_of_right_ray_residue
  · intro s hs
    have hboundary : timeOneGammaSeamBoundary rho = rho.re - 1 := by
      rw [timeOneGammaSeamBoundary, max_eq_right]
      linarith
    rw [timeOneGammaSeamDomain, Set.mem_setOf_eq, hboundary]
    simp only [Complex.add_re, Complex.sub_re, Complex.conj_re, Complex.one_re,
      Complex.ofReal_re]
    linarith
  · exact tendsto_timeOneGammaPrimeSeam_right_residue hrho
  · simp only [neg_ne_zero]
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)

theorem timeOneGammaPrimeSeam_noExtensionAt_of_re_lt_half
    {rho : ℂ} (hrho : rho.re < 1 / 2) :
    NoExtensionAt (timeOneGammaPrimeSeam rho) (timeOneGammaSeamDomain rho) (-rho) := by
  apply noExtensionAt_of_right_ray_residue
  · intro s hs
    have hboundary : timeOneGammaSeamBoundary rho = -rho.re := by
      rw [timeOneGammaSeamBoundary, max_eq_left]
      linarith
    rw [timeOneGammaSeamDomain, Set.mem_setOf_eq, hboundary]
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
    linarith
  · exact tendsto_timeOneGammaPrimeSeam_left_residue hrho
  · exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)

/-- Uniform boundedness of all finite factorial raw-jet energies at one real base point. -/
def TimeOneGammaJetFockBounded (rho : ℂ) (x0 : ℝ) : Prop :=
  ∃ C : ℝ, ∀ N : ℕ,
    ∑ n ∈ Finset.range N,
      ‖iteratedDeriv n (timeOneGammaPrimeSeam rho) (x0 : ℂ)‖ ^ 2 / n.factorial ≤ C

theorem ofReal_mem_timeOneGammaSeamDomain
    {rho : ℂ} (hrho : 0 < rho.re ∧ rho.re < 1) {x0 : ℝ} (hx0 : 1 < x0) :
    (x0 : ℂ) ∈ timeOneGammaSeamDomain rho := by
  have hb : timeOneGammaSeamBoundary rho < 0 := by
    rw [timeOneGammaSeamBoundary, max_lt_iff]
    constructor <;> linarith
  rw [timeOneGammaSeamDomain, Set.mem_setOf_eq, Complex.ofReal_re]
  linarith

/-- Exact time-one Gamma factorial-jet dichotomy, equation (14). -/
theorem timeOneGammaJetFockBounded_iff_re_eq_half
    {rho : ℂ} (hrho : 0 < rho.re ∧ rho.re < 1) {x0 : ℝ} (hx0 : 1 < x0) :
    TimeOneGammaJetFockBounded rho x0 ↔ rho.re = 1 / 2 := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨N, hN⟩ := exists_rawJetFactorialFockPartialEnergy_gt_of_noExtensionAt
        (analyticOnNhd_timeOneGammaPrimeSeam rho)
        (isPreconnected_timeOneGammaSeamDomain rho)
        (ofReal_mem_timeOneGammaSeamDomain hrho hx0)
        (timeOneGammaPrimeSeam_noExtensionAt_of_re_lt_half hlt) C
      exact (not_lt_of_ge (hC N)) hN
    · obtain ⟨N, hN⟩ := exists_rawJetFactorialFockPartialEnergy_gt_of_noExtensionAt
        (analyticOnNhd_timeOneGammaPrimeSeam rho)
        (isPreconnected_timeOneGammaSeamDomain rho)
        (ofReal_mem_timeOneGammaSeamDomain hrho hx0)
        (timeOneGammaPrimeSeam_noExtensionAt_of_re_gt_half hgt) C
      exact (not_lt_of_ge (hC N)) hN
  · intro hline
    refine ⟨0, fun N => ?_⟩
    rw [timeOneGammaPrimeSeam_eq_zero_of_re_eq_half hline]
    simp

/-- Explicit off-line cofinal divergence at every safe base point. -/
theorem exists_timeOneGammaJetFockEnergy_gt_of_re_ne_half
    {rho : ℂ} (hrho : 0 < rho.re ∧ rho.re < 1) (hoff : rho.re ≠ 1 / 2)
    {x0 C : ℝ} (hx0 : 1 < x0) :
    ∃ N : ℕ, C < ∑ n ∈ Finset.range N,
      ‖iteratedDeriv n (timeOneGammaPrimeSeam rho) (x0 : ℂ)‖ ^ 2 / n.factorial := by
  rcases lt_or_gt_of_ne hoff with hlt | hgt
  · exact exists_rawJetFactorialFockPartialEnergy_gt_of_noExtensionAt
      (analyticOnNhd_timeOneGammaPrimeSeam rho)
      (isPreconnected_timeOneGammaSeamDomain rho)
      (ofReal_mem_timeOneGammaSeamDomain hrho hx0)
      (timeOneGammaPrimeSeam_noExtensionAt_of_re_lt_half hlt) C
  · exact exists_rawJetFactorialFockPartialEnergy_gt_of_noExtensionAt
      (analyticOnNhd_timeOneGammaPrimeSeam rho)
      (isPreconnected_timeOneGammaSeamDomain rho)
      (ofReal_mem_timeOneGammaSeamDomain hrho hx0)
      (timeOneGammaPrimeSeam_noExtensionAt_of_re_gt_half hgt) C

/-- Every open-strip reflected seam is an honest vector in time-one Meixner Hilbert space. -/
theorem summable_timeOneMeixnerSeamEnergy_of_openStrip
    {rho : ℂ} (hrho : 0 < rho.re ∧ rho.re < 1) :
    Summable (meixnerSeamEnergy 1 rho) := by
  rw [summable_meixnerSeamEnergy_iff (by norm_num : (0 : ℝ) < 1)]
  right
  rw [abs_lt]
  constructor <;> linarith

/-- Analytic seam is source-value transform of its actual time-one Hilbert vector. -/
theorem inner_timeOneMeixnerSeam_eq_timeOneGammaPrimeSeam
    {rho : ℂ} (hrho : 0 < rho.re ∧ rho.re < 1) {x : ℝ} (hx : 1 / 2 < x) :
    inner ℂ
        (meixnerPrimeSeam 1 rho (summable_timeOneMeixnerSeamEnergy_of_openStrip hrho))
        (meixnerPrimeLaplaceFeature 1 x (by norm_num) hx) =
      timeOneGammaPrimeSeam rho x := by
  exact inner_meixnerPrimeSeam_meixnerPrimeLaplaceFeature
    (theta := 1) (by norm_num) rho
      (summable_timeOneMeixnerSeamEnergy_of_openStrip hrho) hx

/-- Exact RH consumer, equation (17), at any one fixed safe real base point. -/
theorem riemannHypothesis_iff_forall_xiDivisor_timeOneGammaJetFockBounded
    {x0 : ℝ} (hx0 : 1 < x0) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport, TimeOneGammaJetFockBounded (rho : ℂ) x0 := by
  constructor
  · intro hRH rho
    rw [timeOneGammaJetFockBounded_iff_re_eq_half
      (xi_divisor_support_re_mem_open_unit rho) hx0]
    exact (riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH) (rho : ℂ)
      (xi_eq_zero_of_mem_divisor_support rho)
  · intro hbound
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro z hz
    let rho : XiDivisorSupport := ⟨z, mem_xi_divisor_support_of_eq_zero hz⟩
    exact (timeOneGammaJetFockBounded_iff_re_eq_half
      (xi_divisor_support_re_mem_open_unit rho) hx0).mp (hbound rho)

end

end RHTower
