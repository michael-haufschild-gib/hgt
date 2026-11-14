import GaloisForLFunctions.ConjugateDiagonalGeometry.GaussianZeroCopies
import GaloisForLFunctions.ConjugateDiagonalGeometry.GaussianCompensationKernel
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.QuasiRiemannHypothesis

/-!
# Local off-line compensation for a large critical multiplicity

A critical atom contributes its full multiplicity to a centered Gaussian.
Negative contributions must lie off the critical line. The Gaussian tail is
controlled by the actual Lorentzian zero mass, leaving finitely many nearby
copies at a definite horizontal depth.
-/

open Complex Filter Topology Set
noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open RiemannGaussian _root_.RHTower
open GaloisForLFunctions.ConjugateDiagonalGeometry
open GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

/-- The exact finite compensation inequality at a critical zero. All copies
on the right are actual zeta zeros with their analytic multiplicities. -/
theorem exists_gaussian_compensating_copies (ρ : NontrivialZetaZero)
    (hρ : ρ.1.re = 1 / 2) {ε R : ℝ} (hε : 1 ≤ ε) (hR : 0 < R) :
    ∃ F : Finset (NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity),
      (∀ q ∈ F, |q.1.1.im - ρ.1.im| ≤ R ∧
        Real.pi / (4 * ε * R) ≤ |q.1.1.re - 1 / 2|) ∧
      (analyticZetaZeroMultiplicity ρ : ℝ) ≤
        canonicalZetaGaussianZeroSum ε ρ.1.im + Real.exp (9 * ε / 64) * F.card +
          (2 * Real.exp (9 * ε / 64) * Real.exp (-(ε * R ^ 2 / 2))) * lorentzMass ρ.1.im := by
  classical
  have hε0 : 0 < ε := by linarith only [hε]
  let g (q : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity) : ℝ :=
    offAxisSingleContribution ε ρ.1.im q.1.1.im (1 / 2 - q.1.1.re)
  let w (q : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity) : ℝ :=
    1 / (1 + (ρ.1.im - q.1.1.im) ^ 2)
  let A : ℝ := Real.exp (9 * ε / 64)
  let κ : ℝ := 2 * A * Real.exp (-(ε * R ^ 2 / 2))
  have hA : 0 < A := Real.exp_pos _
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hw0 (q) : 0 ≤ w q := by dsimp [w]; positivity
  have hsum : HasSum g (canonicalZetaGaussianZeroSum ε ρ.1.im) := by
    simpa only [g, gaussianZeroSummand_re, Complex.ofReal_re] using
      Complex.hasSum_re (representsCanonicalZetaGaussianZeroSum_unconditional ε ρ.1.im hε0)
  have hw : Summable w := summable_gaussianZeroLorentz ρ.1.im
  let target : Finset (NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity) :=
    ({ρ} : Finset NontrivialZetaZero).sigma
      (fun σ => (Finset.univ : Finset (Fin (analyticZetaZeroMultiplicity σ))))
  have htarget : target.card = analyticZetaZeroMultiplicity ρ := by simp [target]
  have hcenter (q) (hq : q ∈ target) : g q = 1 := by
    have hqρ : q.1 = ρ := Finset.mem_singleton.mp (Finset.mem_sigma.mp hq).1
    simp only [g, hqρ, hρ, offAxisSingleContribution, sub_self, zero_pow (by decide : 2 ≠ 0),
      mul_zero, sub_zero, Real.exp_zero, Real.cos_zero, mul_one]
  have hfinite := finite_gaussianZeroCopies_near ρ.1.im hR.le
  let bad := hfinite.toFinset.filter (fun q => g q < 0)
  have hbad (q) : q ∈ bad ↔ |q.1.1.im - ρ.1.im| ≤ R ∧ g q < 0 := by
    simp only [bad, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have henv (q) : |g q| ≤ A * Real.exp (-ε * (q.1.1.im - ρ.1.im) ^ 2) := by
    have hs := riemannZeta_zero_mem_quasiRH_strip q.1.zero_lt_re q.1.2.1
    have hd : |1 / 2 - q.1.1.re| ≤ 3 / 8 :=
      abs_le.mpr ⟨by linarith only [hs.2], by linarith only [hs.1]⟩
    exact abs_gaussianContribution_le_strip_envelope hε0.le hd ρ.1.im q.1.1.im
  have hglobal (q) : |g q| ≤ A := by
    have he : Real.exp (-ε * (q.1.1.im - ρ.1.im) ^ 2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hm := mul_nonneg hε0.le (sq_nonneg (q.1.1.im - ρ.1.im))
      nlinarith only [hm]
    exact (henv q).trans (mul_le_of_le_one_right hA.le he)
  have htail (q) (hq : R ≤ |q.1.1.im - ρ.1.im|) : -κ * w q ≤ g q := by
    have he := gaussian_lorentz_tail_le hε hR.le hq
    have hb := (henv q).trans (mul_le_mul_of_nonneg_left he hA.le)
    have heq : A * ((2 * Real.exp (-(ε * R ^ 2 / 2))) /
        (1 + (q.1.1.im - ρ.1.im) ^ 2)) = κ * w q := by
      dsimp [κ, w]
      rw [sq_sub_comm ρ.1.im q.1.1.im]
      ring
    rw [heq] at hb
    simpa only [neg_mul] using (abs_le.mp hb).1
  have hpoint (q) : (if q ∈ target then (1 : ℝ) else 0) ≤
      g q + A * (if q ∈ bad then (1 : ℝ) else 0) + κ * w q := by
    have htw : 0 ≤ κ * w q := mul_nonneg hκ (hw0 q)
    by_cases ht : q ∈ target
    · rw [if_pos ht, hcenter q ht]
      split_ifs <;> nlinarith only [hA, htw]
    · rw [if_neg ht]
      by_cases hb : q ∈ bad
      · rw [if_pos hb, mul_one]
        have hg := (abs_le.mp (hglobal q)).1
        linarith only [hg, htw]
      · rw [if_neg hb, mul_zero, add_zero]
        by_cases hn : |q.1.1.im - ρ.1.im| ≤ R
        · have hg : 0 ≤ g q := le_of_not_gt (fun hneg => hb ((hbad q).mpr ⟨hn, hneg⟩))
          exact add_nonneg hg htw
        · have hg := htail q (le_of_lt (lt_of_not_ge hn))
          linarith only [hg]
  have hc := finite_gaussian_compensation_count target bad hsum.summable hw hpoint
  rw [htarget, hsum.tsum_eq, tsum_gaussianZeroLorentz] at hc
  refine ⟨bad, ?_, hc⟩
  intro q hq
  obtain ⟨hn, hneg⟩ := (hbad q).mp hq
  refine ⟨hn, ?_⟩
  have hd := gaussian_negative_depth_ge hε0 hR hn hneg
  simpa only [abs_sub_comm (1 / 2 : ℝ) q.1.1.re] using hd

/-- Every critical zero with multiplicity at least `c log T`, at sufficiently
large positive height, forces a logarithmic number of nearby off-line copies
at a horizontal depth bounded below solely in terms of `c`. -/
theorem exists_local_offLine_compensation {c : ℝ} (hc : 0 < c) :
    ∃ R d κ T₀ : ℝ, 0 < R ∧ 0 < d ∧ 0 < κ ∧ 8 ≤ T₀ ∧
      ∀ ρ : NontrivialZetaZero, ρ.1.re = 1 / 2 → T₀ ≤ ρ.1.im →
        c * Real.log ρ.1.im ≤ (analyticZetaZeroMultiplicity ρ : ℝ) →
        ∃ F : Finset (NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity),
          (∀ q ∈ F, |q.1.1.im - ρ.1.im| ≤ R ∧ d ≤ |q.1.1.re - 1 / 2|) ∧
          κ * Real.log ρ.1.im ≤ F.card := by
  let h : ℝ := min 1 (c * Real.sqrt Real.pi)
  have hh : 0 < h := lt_min (by norm_num) (mul_pos hc (Real.sqrt_pos.mpr Real.pi_pos))
  have hh1 : h ≤ 1 := min_le_left _ _
  have hhc : h ≤ c * Real.sqrt Real.pi := min_le_right _ _
  let ε : ℝ := 1 / h ^ 2
  have hε0 : 0 < ε := by dsimp [ε]; positivity
  have hε : 1 ≤ ε := by
    apply (le_div_iff₀ (by positivity : 0 < h ^ 2)).mpr
    have hs := pow_le_pow_left₀ hh.le hh1 2
    simpa using hs
  let A : ℝ := Real.exp (9 / (64 * h ^ 2))
  have hA : 0 < A := Real.exp_pos _
  have hAeq : Real.exp (9 * ε / 64) = A := by
    dsimp [ε, A]
    congr 1
    ring
  let C : ℝ := 8 * (|xiLineTwoLogDerivConstant| + 2)
  have hC : 0 < C := by dsimp [C]; positivity
  let R : ℝ := 1 + 2 * Real.pi * h ^ 2 / 3 +
    h * Real.sqrt (2 * Real.log (1 + 16 * A * C / c))
  have hR : 0 < R := by dsimp [R]; positivity
  let d : ℝ := Real.pi / (4 * ε * R)
  have hd : 0 < d := by dsimp [d]; positivity
  let κ : ℝ := c / (4 * A)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  let tail : ℝ := 2 * A * Real.exp (-(ε * R ^ 2 / 2))
  have htail0 : 0 ≤ tail := by dsimp [tail]; positivity
  have htailC : tail * C ≤ c / 8 := by
    have he : ε * R ^ 2 / 2 = R ^ 2 / (2 * h ^ 2) := by dsimp [ε]; ring
    dsimp only [tail]
    rw [he]
    exact gaussian_explicit_radius_tail hh hA hC hc
  have hmass : Real.sqrt (Real.pi / ε) = h * Real.sqrt Real.pi := by
    have he : Real.pi / ε = Real.pi * h ^ 2 := by dsimp [ε]; field_simp [hh.ne']
    rw [he, Real.sqrt_mul Real.pi_nonneg, Real.sqrt_sq_eq_abs, abs_of_pos hh]
    ring
  have hmain : Real.sqrt (Real.pi / ε) / (2 * Real.pi) ≤ c / 2 := by
    rw [hmass]
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    have hm := mul_le_mul_of_nonneg_right hhc (Real.sqrt_nonneg Real.pi)
    have he : c * Real.sqrt Real.pi * Real.sqrt Real.pi = c * Real.pi := by
      rw [mul_assoc, ← pow_two, Real.sq_sqrt Real.pi_nonneg]
    rw [he] at hm
    nlinarith only [hm]
  have hlim := tendsto_canonicalZetaGaussianZeroSum_log_normalized hε0
  have he := hlim.eventually (Iio_mem_nhds (show
      Real.sqrt (Real.pi / ε) / (2 * Real.pi) <
        Real.sqrt (Real.pi / ε) / (2 * Real.pi) + c / 8 by linarith only [hc]))
  obtain ⟨U, hU⟩ := eventually_atTop.mp (eventually_comap.mp he)
  refine ⟨R, d, κ, max 8 U, hR, hd, hκ, le_max_left _ _, ?_⟩
  intro ρ hρ hheight hmult
  have ht8 : 8 ≤ ρ.1.im := (le_max_left _ _).trans hheight
  have ht0 : 0 < ρ.1.im := by linarith only [ht8]
  have hlog : 0 < Real.log ρ.1.im := Real.log_pos (by linarith only [ht8])
  have hq := hU ρ.1.im ((le_max_right _ _).trans hheight) ρ.1.im (abs_of_pos ht0)
  rw [abs_of_pos ht0] at hq
  have hQ : canonicalZetaGaussianZeroSum ε ρ.1.im ≤ (5 * c / 8) * Real.log ρ.1.im := by
    apply (div_le_iff₀ hlog).mp
    exact hq.le.trans (by linarith only [hmain])
  have hM : lorentzMass ρ.1.im ≤ C * Real.log ρ.1.im := by
    have hh := gaussianZeroLorentz_le_log ht8
    rw [tsum_gaussianZeroLorentz] at hh
    exact hh
  have htail : tail * lorentzMass ρ.1.im ≤ (c / 8) * Real.log ρ.1.im := by
    calc tail * lorentzMass ρ.1.im ≤ tail * (C * Real.log ρ.1.im) :=
        mul_le_mul_of_nonneg_left hM htail0
      _ = (tail * C) * Real.log ρ.1.im := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right htailC hlog.le
  obtain ⟨F, hF, hb⟩ := exists_gaussian_compensating_copies ρ hρ hε hR
  rw [hAeq] at hb
  change (analyticZetaZeroMultiplicity ρ : ℝ) ≤
    canonicalZetaGaussianZeroSum ε ρ.1.im + A * F.card + tail * lorentzMass ρ.1.im at hb
  have hnegative : (c / 4) * Real.log ρ.1.im ≤ A * F.card := by
    nlinarith only [hmult, hQ, htail, hb]
  refine ⟨F, hF, ?_⟩
  have hcount : ((c / 4) * Real.log ρ.1.im) / A ≤ F.card :=
    (div_le_iff₀ hA).mpr (by simpa only [mul_comm] using hnegative)
  convert hcount using 1
  dsimp [κ]
  ring

end GaloisForLFunctions.SquareRootThreshold

#print axioms GaloisForLFunctions.SquareRootThreshold.exists_gaussian_compensating_copies
#print axioms GaloisForLFunctions.SquareRootThreshold.exists_local_offLine_compensation
