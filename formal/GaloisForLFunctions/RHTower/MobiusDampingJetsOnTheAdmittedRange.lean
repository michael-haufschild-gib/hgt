import GaloisForLFunctions.RHTower.TheDampedMoebiusMellinQuotientIsHardyRightOfTheZeroAbscissa
import Mathlib.Analysis.Complex.Liouville
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusMellin
import GaloisForLFunctions.RHTower.MellinHardyClasses
import GaloisForLFunctions.HTGeometry.FourierUniquenessL1
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# Uniform Mellin bounds for the damping jets

Cauchy's estimate for the regular reciprocal of zeta retains its subpolynomial
vertical bound at every derivative order. On a closed damping range strictly
above the zero width, the pole-cleared Mellin jets therefore have one common
square-integrable vertical majorant, with factorial dependence on the order.
-/

open Complex Set Filter Topology MeasureTheory Metric
open GaloisForLFunctions.HTGeometry

noncomputable section
set_option autoImplicit false

namespace RHTower

open Sieve

/-- The reciprocal is holomorphic throughout the open zero-free half-plane. -/
theorem differentiableOn_invZeta_abscissa :
    DifferentiableOn ℂ invZeta {w : ℂ | zetaZeroAbscissa < w.re} := by
  intro w hw
  exact (differentiableAt_invZeta (zetaResidueUnit_ne_zero_of_zeroFree
    (fun z hz => riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hz) hw)).differentiableWithinAt

/-- Every reciprocal-zeta jet is holomorphic in the same half-plane. -/
theorem differentiableOn_iteratedDeriv_invZeta_abscissa (k : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv k invZeta)
      {w : ℂ | zetaZeroAbscissa < w.re} := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using differentiableOn_invZeta_abscissa
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv (isOpen_lt continuous_const Complex.continuous_re)

/-- One vertical majorant controls every reciprocal-zeta jet, uniformly to the
right of any fixed line strictly beyond the zero abscissa. -/
theorem exists_uniform_invZeta_jet_bound {a : ℝ}
    (ha : zetaZeroAbscissa < 1 / 2 + a) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ (k : ℕ) (w : ℂ),
      1 / 2 + a ≤ w.re →
      ‖iteratedDeriv k invZeta w‖ ≤
        ((k.factorial : ℝ) * C / r ^ k) * (2 + |w.im|) ^ ((1 : ℝ) / 8) := by
  let r : ℝ := min ((1 / 2 + a - zetaZeroAbscissa) / 2) 1
  have hr : 0 < r := lt_min (by linarith) zero_lt_one
  have hr1 : r ≤ 1 := min_le_right _ _
  have hrmargin : r ≤ (1 / 2 + a - zetaZeroAbscissa) / 2 := min_le_left _ _
  have hb : zetaZeroAbscissa < 1 / 2 + (a - r) := by linarith
  obtain ⟨B, hB, hbound⟩ := exists_norm_invZeta_le_of_zetaZeroAbscissa_lt hb
  refine ⟨r, B * 2 ^ ((1 : ℝ) / 8), hr, by positivity, fun k w hw => ?_⟩
  have hsub : closedBall w r ⊆ {z : ℂ | zetaZeroAbscissa < z.re} := by
    intro z hz
    have hnorm : ‖z - w‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have hre := (abs_le.mp ((Complex.abs_re_le_norm (z - w)).trans hnorm)).1
    simp only [Complex.sub_re] at hre
    change zetaZeroAbscissa < z.re
    linarith
  have hdc : DiffContOnCl ℂ invZeta (ball w r) :=
    differentiableOn_invZeta_abscissa.diffContOnCl_ball hsub
  have hcircle : ∀ z ∈ sphere w r, ‖invZeta z‖ ≤
      B * 2 ^ ((1 : ℝ) / 8) * (2 + |w.im|) ^ ((1 : ℝ) / 8) := by
    intro z hz
    have hnorm : ‖z - w‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hz
    have hre := (abs_le.mp ((Complex.abs_re_le_norm (z - w)).trans_eq hnorm)).1
    simp only [Complex.sub_re] at hre
    have him : |z.im - w.im| ≤ r := by
      simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (z - w)).trans_eq hnorm
    have hzre : 1 / 2 + (a - r) ≤ z.re := by linarith
    have habs : |z.im| ≤ |w.im| + r := by
      have htri := abs_add_le (z.im - w.im) w.im
      rw [sub_add_cancel] at htri
      linarith
    calc ‖invZeta z‖ ≤ B * (2 + |z.im|) ^ ((1 : ℝ) / 8) := hbound z hzre
      _ ≤ B * (2 * (2 + |w.im|)) ^ ((1 : ℝ) / 8) := by
        apply mul_le_mul_of_nonneg_left _ hB
        exact Real.rpow_le_rpow (by positivity)
          (by nlinarith [abs_nonneg w.im]) (by norm_num)
      _ = B * 2 ^ ((1 : ℝ) / 8) * (2 + |w.im|) ^ ((1 : ℝ) / 8) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
        ring
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr hdc hcircle
  calc ‖iteratedDeriv k invZeta w‖ ≤
      (k.factorial : ℝ) *
        (B * 2 ^ ((1 : ℝ) / 8) * (2 + |w.im|) ^ ((1 : ℝ) / 8)) / r ^ k := hc
    _ = ((k.factorial : ℝ) * (B * 2 ^ ((1 : ℝ) / 8)) / r ^ k) *
        (2 + |w.im|) ^ ((1 : ℝ) / 8) := by ring

/-- The Mellin multiplier of the `k`th damping derivative of the Fermi source. -/
def mobiusDampingJetQuotient (k : ℕ) (ε : ℝ) (s : ℂ) : ℂ :=
  etaSlope s * zetaResidueUnit s * iteratedDeriv k invZeta (s + (ε : ℂ)) / s

@[simp] theorem mobiusDampingJetQuotient_zero (ε : ℝ) :
    mobiusDampingJetQuotient 0 ε = etaZetaQuotient ε := by
  funext s
  simp only [mobiusDampingJetQuotient, iteratedDeriv_zero, etaZetaQuotient]

/-- The pole-cleared damping jets are holomorphic on the closed critical
half-plane whenever the damping lies strictly above the zero width. -/
theorem differentiableAt_mobiusDampingJetQuotient (k : ℕ) {ε : ℝ}
    (hε : zetaZeroAbscissa < 1 / 2 + ε) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    DifferentiableAt ℂ (mobiusDampingJetQuotient k ε) s := by
  have hmem : s + (ε : ℂ) ∈ {w : ℂ | zetaZeroAbscissa < w.re} := by
    simp only [mem_setOf_eq, add_re, ofReal_re]
    linarith
  have hd := (differentiableOn_iteratedDeriv_invZeta_abscissa k).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)
  have hs0 : s ≠ 0 := by
    intro hz
    rw [hz, zero_re] at hs
    linarith
  exact ((differentiable_etaSlope_mul_zetaResidueUnit s).mul
    (hd.comp s (differentiableAt_id.add_const _))).div differentiableAt_id hs0

/-- Damping differentiation costs factorials and powers of the distance to the
admission boundary, but does not worsen vertical decay. -/
theorem exists_uniform_mobiusDampingJetQuotient_bound {a : ℝ}
    (ha : zetaZeroAbscissa < 1 / 2 + a) :
    ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧ ∀ (k : ℕ) (ε : ℝ), a ≤ ε →
      ∀ s : ℂ, 1 / 2 ≤ s.re →
        ‖mobiusDampingJetQuotient k ε s‖ ≤
          (K * (k.factorial : ℝ) / r ^ k) * (1 + |s.im|) ^ (-(9 / 16 : ℝ)) := by
  obtain ⟨r, C, hr, hC, hI⟩ := exists_uniform_invZeta_jet_bound ha
  obtain ⟨A, hA, hE⟩ := exists_norm_etaSlope_mul_zetaResidueUnit_le
  refine ⟨r, 4 * A * C * 2 ^ ((1 : ℝ) / 8), hr, by positivity,
    fun k ε hε s hs => ?_⟩
  let B : ℝ := (k.factorial : ℝ) * C / r ^ k
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hu : (0 : ℝ) < 1 + |s.im| := by positivity
  have hsn : 0 < ‖s‖ := by
    have := one_add_abs_im_le_four_mul_norm hs
    linarith [abs_nonneg s.im]
  have harg : 1 / 2 + a ≤ (s + (ε : ℂ)).re := by
    simp only [add_re, ofReal_re]
    linarith
  have hi : ‖iteratedDeriv k invZeta (s + (ε : ℂ))‖ ≤
      B * 2 ^ ((1 : ℝ) / 8) * (1 + |s.im|) ^ ((1 : ℝ) / 8) := by
    have h := hI k (s + (ε : ℂ)) harg
    simp only [add_im, ofReal_im, add_zero] at h
    refine h.trans ?_
    rw [mul_assoc, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hu.le]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg s.im])
        (by norm_num)) hB
  have hinv : ‖s‖⁻¹ ≤ 4 * (1 + |s.im|)⁻¹ := by
    have h := inv_anti₀ (by positivity : (0 : ℝ) < (1 + |s.im|) / 4)
      (by linarith [one_add_abs_im_le_four_mul_norm hs] : (1 + |s.im|) / 4 ≤ ‖s‖)
    rwa [inv_div, div_eq_mul_inv] at h
  rw [mobiusDampingJetQuotient, norm_div, norm_mul, div_eq_mul_inv]
  calc ‖etaSlope s * zetaResidueUnit s‖ *
        ‖iteratedDeriv k invZeta (s + (ε : ℂ))‖ * ‖s‖⁻¹
      ≤ (A * (1 + |s.im|) ^ ((5 : ℝ) / 16)) *
          (B * 2 ^ ((1 : ℝ) / 8) * (1 + |s.im|) ^ ((1 : ℝ) / 8)) *
          (4 * (1 + |s.im|)⁻¹) :=
        mul_le_mul (mul_le_mul (hE s hs) hi (norm_nonneg _) (by positivity)) hinv
          (by positivity) (by positivity)
    _ = (4 * A * B * 2 ^ ((1 : ℝ) / 8)) *
        ((1 + |s.im|) ^ ((5 : ℝ) / 16) *
          (1 + |s.im|) ^ ((1 : ℝ) / 8) * (1 + |s.im|)⁻¹) := by ring
    _ = (4 * A * B * 2 ^ ((1 : ℝ) / 8)) *
        (1 + |s.im|) ^ (-(9 / 16 : ℝ)) := by
      congr 1
      rw [← Real.rpow_add hu, ← Real.rpow_neg_one, ← Real.rpow_add hu]
      norm_num
    _ = ((4 * A * C * 2 ^ ((1 : ℝ) / 8)) * (k.factorial : ℝ) / r ^ k) *
        (1 + |s.im|) ^ (-(9 / 16 : ℝ)) := by dsimp [B]; ring

/-- A single factorial Hardy budget controls all jets on a closed interior damping range. -/
theorem exists_uniform_mobiusDampingJetQuotient_hardy {a : ℝ}
    (ha : zetaZeroAbscissa < 1 / 2 + a) :
    ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧ ∀ (k : ℕ) (ε : ℝ), a ≤ ε →
      IsHalfPlaneHardy (fun w => mobiusDampingJetQuotient k ε (w + 1 / 2))
        (∫ ξ : ℝ, ‖hardyLineMajorant (K * (k.factorial : ℝ) / r ^ k) ξ‖ ^ (2 : ℕ)) := by
  obtain ⟨r, K, hr, hK, hb⟩ := exists_uniform_mobiusDampingJetQuotient_bound ha
  refine ⟨r, K, hr, hK, fun k ε haε => ?_⟩
  have hε : zetaZeroAbscissa < 1 / 2 + ε := by linarith
  let B : ℝ := K * (k.factorial : ℝ) / r ^ k
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hline : ∀ σ : ℝ, 0 ≤ σ → ∀ ξ : ℝ,
      ‖mobiusDampingJetQuotient k ε (rayLine σ ξ + 1 / 2)‖ ≤
        ‖hardyLineMajorant B ξ‖ := by
    intro σ hσ ξ
    have hre : 1 / 2 ≤ (rayLine σ ξ + 1 / 2).re := by
      simp only [add_re, rayLine_re]
      norm_num
      linarith
    have him : (rayLine σ ξ + 1 / 2).im = 2 * Real.pi * ξ := by simp [rayLine]
    have h := hb k ε haε _ hre
    rw [him] at h
    refine h.trans ?_
    have hm : ‖hardyLineMajorant B ξ‖ = B * (1 + |ξ|) ^ (-(9 / 16 : ℝ)) :=
      Real.norm_of_nonneg (mul_nonneg hB (Real.rpow_nonneg (by positivity) _))
    rw [hm]
    change B * (1 + |2 * Real.pi * ξ|) ^ (-(9 / 16 : ℝ)) ≤ _
    apply mul_le_mul_of_nonneg_left _ hB
    have hbase : 1 + |ξ| ≤ 1 + |2 * Real.pi * ξ| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      nlinarith [abs_nonneg ξ, Real.pi_gt_three]
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |2 * Real.pi * ξ|),
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |ξ|)]
    exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_le_rpow (by positivity) hbase (by norm_num))
  have hcont : ∀ σ : ℝ, 0 ≤ σ →
      Continuous (fun ξ : ℝ => mobiusDampingJetQuotient k ε (rayLine σ ξ + 1 / 2)) := by
    intro σ hσ
    apply continuous_iff_continuousAt.mpr
    intro ξ
    have hre : 1 / 2 ≤ (rayLine σ ξ + 1 / 2).re := by
      simp only [add_re, rayLine_re]
      norm_num
      linarith
    have hc : Continuous (fun y : ℝ => rayLine σ y + 1 / 2) := by
      unfold rayLine
      fun_prop
    show ContinuousAt (mobiusDampingJetQuotient k ε ∘
      fun y : ℝ => rayLine σ y + 1 / 2) ξ
    exact ContinuousAt.comp (f := fun y : ℝ => rayLine σ y + 1 / 2) (x := ξ)
      (differentiableAt_mobiusDampingJetQuotient k hε hre).continuousAt hc.continuousAt
  refine ⟨?_, fun σ hσ => ?_, fun σ hσ => ?_⟩
  · intro w hw
    change 0 < w.re at hw
    have hre : 1 / 2 ≤ (w + 1 / 2).re := by
      simp only [add_re]
      norm_num
      linarith
    exact ((differentiableAt_mobiusDampingJetQuotient k hε hre).comp w
      (differentiableAt_id.add_const _)).differentiableWithinAt
  · exact (memLp_two_hardyLineMajorant B).of_le (hcont σ hσ.le).aestronglyMeasurable
      (Eventually.of_forall (hline σ hσ.le))
  · refine integral_mono_of_nonneg (Eventually.of_forall fun ξ => by positivity)
      (integrable_sq_hardyLineMajorant B) (Eventually.of_forall fun ξ => ?_)
    exact pow_le_pow_left₀ (norm_nonneg _) (hline σ hσ.le ξ) 2

/-- Every damping jet belongs to the same critical Mellin Hardy class. -/
theorem isMellinTailHardy_mobiusDampingJetQuotient (k : ℕ) {ε : ℝ}
    (hε : zetaZeroAbscissa < 1 / 2 + ε) :
    IsMellinTailHardy 1 (mobiusDampingJetQuotient k ε) := by
  obtain ⟨r, K, _, _, hb⟩ := exists_uniform_mobiusDampingJetQuotient_hardy hε
  refine ⟨∫ ξ : ℝ, ‖hardyLineMajorant (K * (k.factorial : ℝ) / r ^ k) ξ‖ ^ (2 : ℕ), ?_⟩
  simpa only [ofReal_one, Complex.one_cpow, one_mul] using hb k ε le_rfl

end RHTower

/-!
# Identifying a Hardy datum with its arithmetic source

Agreement on one absolutely convergent vertical line identifies an explicit
source with the Paley–Wiener datum. The identification retains the Hardy mass
bound; it does not assume square-integrability of the explicit source.
-/

open Complex Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped FourierTransform

noncomputable section
set_option autoImplicit false

namespace RHTower

/-- The mass bound in the Hardy definition also bounds its boundary datum. -/
theorem integral_norm_sq_hardyDatum_le {F : ℂ → ℂ} {M : ℝ}
    (hF : IsHalfPlaneHardy F M) :
    (∫ x in Ioi (0 : ℝ), ‖hardyDatum F hF x‖ ^ (2 : ℕ)) ≤ M := by
  apply le_of_tendsto (tendsto_integral_norm_sq_laplaceRay_line (memLp_two_hardyDatum hF))
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  calc (∫ ξ : ℝ, ‖laplaceRay (hardyDatum F hF) (rayLine σ ξ)‖ ^ (2 : ℕ)) =
      ∫ ξ : ℝ, ‖F (rayLine σ ξ)‖ ^ (2 : ℕ) := by
        apply integral_congr_ae
        filter_upwards with ξ
        rw [isHalfPlaneHardy_eq_laplaceRay hF (by simpa using hσ)]
    _ ≤ M := hF.bound σ hσ

/-- One weighted `L¹` line suffices to identify a source with a Hardy datum. -/
theorem ae_eq_hardyDatum_of_laplaceRay_line {F : ℂ → ℂ} {M τ : ℝ}
    (hF : IsHalfPlaneHardy F M) (hτ : 0 < τ) {φ : ℝ → ℂ}
    (hi : ∀ ξ : ℝ, IntegrableOn (fun x => φ x * expRay (rayLine τ ξ) x) (Ioi 0))
    (heq : ∀ ξ : ℝ, laplaceRay φ (rayLine τ ξ) = F (rayLine τ ξ)) :
    φ =ᵐ[volume.restrict (Ioi 0)] hardyDatum F hF := by
  let d := hardyDatum F hF
  have hd : MemLp d 2 (volume.restrict (Ioi 0)) := memLp_two_hardyDatum hF
  have hdamp : rayDamp (φ - d) τ = rayDamp φ τ - rayDamp d τ := by
    funext x
    simp only [rayDamp, Pi.sub_apply, indicator_apply, sub_mul]
    split_ifs <;> simp
  have hφ : Integrable (rayDamp φ τ) := by
    rw [rayDamp, integrable_indicator_iff measurableSet_Ioi]
    simpa [rayLine] using hi 0
  have hdiff : Integrable (rayDamp (φ - d) τ) := by
    rw [hdamp]
    exact hφ.sub (integrable_rayDamp hd hτ)
  have hfour : ∀ ξ : ℝ, 𝓕 (rayDamp (φ - d) τ) ξ = 0 := by
    intro ξ
    rw [fourierIntegral_rayDamp]
    have hsub : laplaceRay (φ - d) (rayLine τ ξ) =
        laplaceRay φ (rayLine τ ξ) - laplaceRay d (rayLine τ ξ) := by
      simp only [laplaceRay, Pi.sub_apply, sub_mul]
      exact integral_sub (hi ξ) (integrableOn_laplaceRay hd (by simpa using hτ))
    rw [hsub, heq ξ, isHalfPlaneHardy_eq_laplaceRay hF (by simpa using hτ)]
    exact sub_self _
  have hae := HTGeometry.ae_eq_zero_of_fourierIntegral_eq_zero hdiff hfour
  refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
  filter_upwards [hae] with x hx hx0
  simp only [rayDamp, indicator_of_mem hx0, Pi.sub_apply, Pi.zero_apply] at hx
  exact sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_right (Complex.exp_ne_zero _))

/-- Source identification transfers both membership and the original Hardy budget. -/
theorem memLp_and_mass_le_of_laplaceRay_line {F : ℂ → ℂ} {M τ : ℝ}
    (hF : IsHalfPlaneHardy F M) (hτ : 0 < τ) {φ : ℝ → ℂ}
    (hi : ∀ ξ : ℝ, IntegrableOn (fun x => φ x * expRay (rayLine τ ξ) x) (Ioi 0))
    (heq : ∀ ξ : ℝ, laplaceRay φ (rayLine τ ξ) = F (rayLine τ ξ)) :
    MemLp φ 2 (volume.restrict (Ioi 0)) ∧
      (∫ x in Ioi (0 : ℝ), ‖φ x‖ ^ (2 : ℕ)) ≤ M := by
  have hae := ae_eq_hardyDatum_of_laplaceRay_line hF hτ hi heq
  refine ⟨(memLp_two_hardyDatum hF).ae_eq hae.symm, ?_⟩
  calc (∫ x in Ioi (0 : ℝ), ‖φ x‖ ^ (2 : ℕ)) =
      ∫ x in Ioi (0 : ℝ), ‖hardyDatum F hF x‖ ^ (2 : ℕ) := by
        exact integral_congr_ae (hae.mono fun x hx => by simp only [hx])
    _ ≤ M := integral_norm_sq_hardyDatum_le hF

/-- The head chart converts the usual Mellin integrand into a Laplace integrand. -/
theorem logChartHead_one_mul_expRay (f : ℝ → ℂ) (s : ℂ) (x : ℝ) :
    (Real.exp (-x)) • (((Real.exp (-x) : ℝ) : ℂ) ^ (s - 1) * f (Real.exp (-x))) =
      logChartHead 1 f x * expRay (s - 1 / 2) x := by
  simp only [logChartHead, Real.sqrt_one, one_mul, expRay, Complex.real_smul]
  rw [GaloisForLFunctions.cpow_ofReal_exp, Complex.ofReal_exp,
    Complex.ofReal_exp]
  have he : Complex.exp ((-x : ℝ) : ℂ) * Complex.exp (((-x : ℝ) : ℂ) * (s - 1)) =
      Complex.exp (((-x / 2 : ℝ) : ℂ)) * Complex.exp (-((s - 1 / 2) * (x : ℂ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (f (Real.exp (-x))) * he

/-- Absolute Mellin convergence supplies the weighted `L¹` line used for uniqueness. -/
theorem integrableOn_logChartHead_mul_expRay {f : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f s) :
    IntegrableOn (fun x => logChartHead 1 f x * expRay (s - 1 / 2) x) (Ioi 0) := by
  have hh : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * f t) (Ioo 0 1) :=
    hf.mono_set Ioo_subset_Ioi_self
  have ht := (integrableOn_Ioo_expScaleNeg one_pos _).mp hh
  simp only [one_mul] at ht
  exact ht.congr_fun (fun x _ => logChartHead_one_mul_expRay f s x) measurableSet_Ioi

/-- Square-integrability transfers back through the head chart. -/
theorem memLp_of_memLp_logChartHead_one {f : ℝ → ℂ} (hm : Measurable f)
    (hsupp : ∀ t : ℝ, 1 < t → f t = 0)
    (hf : MemLp (logChartHead 1 f) 2 (volume.restrict (Ioi 0))) :
    MemLp f 2 (volume.restrict (Ioi 0)) := by
  rw [memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable]
  have hh : IntegrableOn (fun t => ‖f t‖ ^ (2 : ℕ)) (Ioo 0 1) := by
    apply (integrableOn_Ioo_expScaleNeg one_pos _).mpr
    have hi : IntegrableOn (fun x => ‖logChartHead 1 f x‖ ^ (2 : ℕ)) (Ioi 0) :=
      (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
    refine hi.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simpa only [smul_eq_mul] using norm_sq_logChartHead zero_le_one f x
  have hh' : IntegrableOn (fun t => ‖f t‖ ^ (2 : ℕ)) (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hh
  have ht : IntegrableOn (fun t => ‖f t‖ ^ (2 : ℕ)) (Ioi 1) := by
    refine integrableOn_zero.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp [hsupp t ht]
  change IntegrableOn _ (Ioi (0 : ℝ))
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact hh'.union ht

/-- A compactly supported source inherits the Hardy bound from one Mellin line. -/
theorem memLp_and_head_mass_le_of_mellin_line {f : ℝ → ℂ} (hm : Measurable f)
    (hsupp : ∀ t : ℝ, 1 < t → f t = 0) {F : ℂ → ℂ} {M τ : ℝ}
    (hF : IsHalfPlaneHardy (fun w => F (w + 1 / 2)) M) (hτ : 0 < τ)
    (hi : ∀ ξ : ℝ, MellinConvergent f (rayLine τ ξ + 1 / 2))
    (heq : ∀ ξ : ℝ, mellin f (rayLine τ ξ + 1 / 2) = F (rayLine τ ξ + 1 / 2)) :
    MemLp f 2 (volume.restrict (Ioi 0)) ∧
      (∫ t in Ioo (0 : ℝ) 1, ‖f t‖ ^ (2 : ℕ)) ≤ M := by
  have hi' : ∀ ξ : ℝ, IntegrableOn
      (fun x => logChartHead 1 f x * expRay (rayLine τ ξ) x) (Ioi 0) := by
    intro ξ
    simpa only [add_sub_cancel_right] using integrableOn_logChartHead_mul_expRay (hi ξ)
  have heq' : ∀ ξ : ℝ, laplaceRay (logChartHead 1 f) (rayLine τ ξ) =
      F (rayLine τ ξ + 1 / 2) := by
    intro ξ
    have h := heq ξ
    rwa [pm_mellin_eq_head_laplace hsupp, add_sub_cancel_right] at h
  obtain ⟨hlp, hmass⟩ := memLp_and_mass_le_of_laplaceRay_line hF hτ hi' heq'
  refine ⟨memLp_of_memLp_logChartHead_one hm hsupp hlp, ?_⟩
  rwa [integral_norm_sq_logChartHead one_pos f] at hmass

/-- For a source supported below one, its full square mass is its head mass. -/
theorem integral_norm_sq_Ioi_eq_head {f : ℝ → ℂ}
    (hsupp : ∀ t : ℝ, 1 < t → f t = 0) :
    (∫ t in Ioi (0 : ℝ), ‖f t‖ ^ (2 : ℕ)) =
      ∫ t in Ioo (0 : ℝ) 1, ‖f t‖ ^ (2 : ℕ) := by
  calc (∫ t in Ioi (0 : ℝ), ‖f t‖ ^ (2 : ℕ)) =
      ∫ t in Ioc (0 : ℝ) 1, ‖f t‖ ^ (2 : ℕ) := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
        intro t ht
        have ht1 : 1 < t := by
          have hn := ht.2
          simp only [mem_Ioc, not_and, not_le] at hn
          exact hn ht.1
        simp [hsupp t ht1]
    _ = _ := integral_Ioc_eq_integral_Ioo

/-- The same identification gives the full positive-ray mass budget. -/
theorem memLp_and_mass_le_of_mellin_line {f : ℝ → ℂ} (hm : Measurable f)
    (hsupp : ∀ t : ℝ, 1 < t → f t = 0) {F : ℂ → ℂ} {M τ : ℝ}
    (hF : IsHalfPlaneHardy (fun w => F (w + 1 / 2)) M) (hτ : 0 < τ)
    (hi : ∀ ξ : ℝ, MellinConvergent f (rayLine τ ξ + 1 / 2))
    (heq : ∀ ξ : ℝ, mellin f (rayLine τ ξ + 1 / 2) = F (rayLine τ ξ + 1 / 2)) :
    MemLp f 2 (volume.restrict (Ioi 0)) ∧
      (∫ t in Ioi (0 : ℝ), ‖f t‖ ^ (2 : ℕ)) ≤ M := by
  rw [integral_norm_sq_Ioi_eq_head hsupp]
  exact memLp_and_head_mass_le_of_mellin_line hm hsupp hF hτ hi heq

end RHTower

/-!
# Literal arithmetic sources for the damping jets

The coefficients are `(-log n)^k μ(n)n^(-ε)`. Absolute Mellin interchange
identifies their pointwise finite Fermi source with the reciprocal-zeta jet.
Hardy identification then controls the source itself throughout the open
admission range, with one factorial budget on every closed interior range.
-/

open Complex Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section
set_option autoImplicit false

namespace RHTower

open Sieve

/-- Signed logarithmic coefficients of the `k`th damping derivative. -/
def mobiusDampingJetCoeff (k : ℕ) (ε : ℝ) : ℕ → ℂ :=
  (-1 : ℂ) ^ k • LSeries.logMul^[k] (pmPowerDampedMobiusCoeff ε)

theorem mobiusDampingJetCoeff_eq (k : ℕ) (ε : ℝ) (n : ℕ) :
    mobiusDampingJetCoeff k ε n =
      ((-Real.log n : ℝ) : ℂ) ^ k * pmPowerDampedMobiusCoeff ε n := by
  have hlog : ∀ j : ℕ, (LSeries.logMul^[j] (pmPowerDampedMobiusCoeff ε)) n =
      (Complex.log n) ^ j * pmPowerDampedMobiusCoeff ε n := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', LSeries.logMul, ih, pow_succ]
      ring
  rw [mobiusDampingJetCoeff, Pi.smul_apply, smul_eq_mul, hlog,
    ← mul_assoc, ← mul_pow]
  congr 2
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  simp

@[simp] theorem mobiusDampingJetCoeff_zero (k : ℕ) (ε : ℝ) :
    mobiusDampingJetCoeff k ε 0 = 0 := by
  rw [mobiusDampingJetCoeff_eq, pmPowerDampedMobiusCoeff_zero, mul_zero]

@[simp] theorem mobiusDampingJetCoeff_order_zero (ε : ℝ) :
    mobiusDampingJetCoeff 0 ε = pmPowerDampedMobiusCoeff ε := by
  simp [mobiusDampingJetCoeff]

/-- The real arithmetic row underlying the complex Mellin coefficients. -/
def mobiusDampingJetRealCoeff (k : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  (-Real.log n) ^ k * (pmPowerDampedMobiusCoeff ε n).re

theorem mobiusDampingJetCoeff_ofReal (k : ℕ) (ε : ℝ) (n : ℕ) :
    mobiusDampingJetCoeff k ε n = (mobiusDampingJetRealCoeff k ε n : ℂ) := by
  -- Take the real part of the real-valued coefficient before splitting the casts.
  rw [mobiusDampingJetCoeff_eq, mobiusDampingJetRealCoeff, pmPowerDampedMobiusCoeff,
    Complex.ofReal_re]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]

theorem abscissaOfAbsConv_pmPowerDampedMobiusCoeff_le (ε : ℝ) :
    LSeries.abscissaOfAbsConv (pmPowerDampedMobiusCoeff ε) ≤ ((1 - ε : ℝ) : EReal) := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact pmPowerDampedMobiusCoeff_lSeriesSummable ε (by simp only [ofReal_re]; linarith)

theorem mobiusDampingJetCoeff_lSeriesSummable (k : ℕ) (ε : ℝ) {s : ℂ}
    (hs : 1 < s.re + ε) : LSeriesSummable (mobiusDampingJetCoeff k ε) s := by
  have ha : LSeries.abscissaOfAbsConv (pmPowerDampedMobiusCoeff ε) < s.re :=
    (abscissaOfAbsConv_pmPowerDampedMobiusCoeff_le ε).trans_lt
      (by exact_mod_cast (show 1 - ε < s.re by linarith))
  have hi : LSeriesSummable (LSeries.logMul^[k] (pmPowerDampedMobiusCoeff ε)) s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using ha)
  exact hi.smul _

/-- Positive damping makes the exact arithmetic mean absolutely convergent at every order. -/
theorem summable_mobiusDampingJetCoeff_div (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => mobiusDampingJetCoeff k ε n / (n : ℂ)) := by
  have h := mobiusDampingJetCoeff_lSeriesSummable k ε
    (s := 1) (by simp only [one_re]; linarith)
  change Summable (LSeries.term (mobiusDampingJetCoeff k ε) 1) at h
  apply h.congr
  intro n
  by_cases hn : n = 0
  · simp only [hn, LSeries.term_zero, Nat.cast_zero, div_zero]
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_one]

theorem summable_mobiusDampingJetRealCoeff_div (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => mobiusDampingJetRealCoeff k ε n / (n : ℝ)) := by
  apply Complex.summable_ofReal.mp
  simpa only [mobiusDampingJetCoeff_ofReal, Complex.ofReal_div, Complex.ofReal_natCast]
    using summable_mobiusDampingJetCoeff_div k hε

/-- The coefficient jet differentiates only the shifted reciprocal, not the Fermi factor. -/
theorem mobiusDampingJetCoeff_lSeries (k : ℕ) (ε : ℝ) {s : ℂ}
    (hs : 1 < s.re + ε) :
    LSeries (mobiusDampingJetCoeff k ε) s = iteratedDeriv k invZeta (s + (ε : ℂ)) := by
  have ha : LSeries.abscissaOfAbsConv (pmPowerDampedMobiusCoeff ε) < s.re :=
    (abscissaOfAbsConv_pmPowerDampedMobiusCoeff_le ε).trans_lt
      (by exact_mod_cast (show 1 - ε < s.re by linarith))
  have heq : LSeries (pmPowerDampedMobiusCoeff ε) =ᶠ[𝓝 s]
      fun z => invZeta (z + (ε : ℂ)) := by
    filter_upwards [(isOpen_lt continuous_const
      (Complex.continuous_re.add continuous_const)).mem_nhds hs] with z hz
    change 1 < z.re + ε at hz
    rw [pmPowerDampedMobiusCoeff_lSeries ε hz, invZeta_eq_inv]
    · exact one_div _
    · intro h
      have hh := congrArg Complex.re h
      simp only [add_re, ofReal_re, one_re] at hh
      linarith
  rw [mobiusDampingJetCoeff, LSeries_smul, ← LSeries_iteratedDeriv k ha,
    heq.iteratedDeriv_eq k, iteratedDeriv_comp_add_const]

/-- The literal finite-at-positive-scale Fermi source of a damping jet. -/
def mobiusDampingJetSource (k : ℕ) (ε : ℝ) (t : ℝ) : ℂ :=
  -pmWeightedDilationSource (mobiusDampingJetCoeff k ε) (fermiNymanGen 1) t

theorem measurable_mobiusDampingJetSource (k : ℕ) (ε : ℝ) :
    Measurable (mobiusDampingJetSource k ε) := by
  apply Measurable.neg
  exact Measurable.tsum fun n => measurable_const.mul
    ((measurable_fermiNymanGen 1).comp (measurable_const.mul measurable_id))

theorem mobiusDampingJetSource_eq_zero_of_one_lt (k : ℕ) (ε : ℝ) {t : ℝ}
    (ht : 1 < t) : mobiusDampingJetSource k ε t = 0 := by
  rw [mobiusDampingJetSource, pmWeightedDilationSource]
  suffices (∑' n : ℕ, mobiusDampingJetCoeff k ε n * fermiNymanGen 1 ((n : ℝ) * t)) = 0 by
    rw [this, neg_zero]
  calc
    _ = ∑' _ : ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        rw [fermiNymanGen_eq_zero_of_inv_lt one_pos (by
          simpa using ht.trans_le (le_mul_of_one_le_left (by linarith : 0 ≤ t) hn1)), mul_zero]
    _ = 0 := tsum_zero

theorem mobiusDampingJetSource_order_zero (ε : ℝ) {t : ℝ} (ht : 0 < t) :
    mobiusDampingJetSource 0 ε t = pmPowerDampedFermiSource ε t := by
  rw [mobiusDampingJetSource, mobiusDampingJetCoeff_order_zero,
    pmPowerDampedFermiSource_eq_dilation ε ht]

/-- Exact finite-source formula; no summation or differentiation is implicit here. -/
theorem mobiusDampingJetSource_eq_sum (k : ℕ) (ε : ℝ) {t : ℝ} (ht : 0 < t) :
    mobiusDampingJetSource k ε t = -∑ n ∈ Finset.range (⌊1 / t⌋₊ + 1),
      mobiusDampingJetCoeff k ε n * fermiNymanGen 1 ((n : ℝ) * t) := by
  rw [mobiusDampingJetSource, pmWeightedDilationSource_eq_sum _ _ ⌊1 / t⌋₊
    (θ := 1) ht (fun x hx => fermiNymanGen_eq_zero_of_inv_lt one_pos (by simpa using hx))
    ((div_lt_iff₀ ht).mp (Nat.lt_floor_add_one (1 / t)))]

private theorem mellinConvergent_fermi_one {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (fermiNymanGen 1) s := by
  have h1 := GaloisForLFunctions.NymanMellin.mellinConvergent_nymanGen hs0 hs1 one_pos
  have h2 := GaloisForLFunctions.NymanMellin.mellinConvergent_nymanGen hs0 hs1
    (by norm_num : (0 : ℝ) < 2 * 1)
  change MellinConvergent (fun t => GaloisForLFunctions.NymanMellin.nymanGen 1 t -
    2 * GaloisForLFunctions.NymanMellin.nymanGen (2 * 1) t) s
  simpa only [smul_eq_mul] using (hasMellin_sub h1 (h2.const_smul (2 : ℂ))).1

/-- Mellin transformation of the literal arithmetic jet on its absolute-convergence strip. -/
theorem hasMellin_mobiusDampingJetSource (k : ℕ) (ε : ℝ) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsε : 1 < s.re + ε) :
    HasMellin (mobiusDampingJetSource k ε) s (mobiusDampingJetQuotient k ε s) := by
  have h := pmWeightedDilationSource_hasMellin (mobiusDampingJetCoeff k ε)
    (fermiNymanGen 1) (mobiusDampingJetCoeff_zero k ε)
    (mobiusDampingJetCoeff_lSeriesSummable k ε hsε) (mellinConvergent_fermi_one hs0 hs1)
  have hn := hasMellin_const_smul h.1 (-1 : ℂ)
  have hsne : s ≠ 1 := by intro h; rw [h, one_re] at hs1; linarith
  have hvalue : -mellin (pmWeightedDilationSource (mobiusDampingJetCoeff k ε)
      (fermiNymanGen 1)) s = mobiusDampingJetQuotient k ε s := by
    rw [h.2, mobiusDampingJetCoeff_lSeries k ε hsε,
      mellin_fermiNymanGen hs0 hs1 one_pos, mobiusDampingJetQuotient,
      etaSlope_mul_zetaResidueUnit hsne]
    simp only [ofReal_one, Complex.one_cpow, one_mul]
    ring
  simp only [smul_eq_mul, neg_one_mul, hvalue] at hn
  exact hn

/-- The Hardy estimate controls the literal source, uniformly at every jet order. -/
theorem exists_uniform_mobiusDampingJetSource_budget {a : ℝ}
    (ha : zetaZeroAbscissa < 1 / 2 + a) :
    ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧ ∀ (k : ℕ) (ε : ℝ), a ≤ ε →
      MemLp (mobiusDampingJetSource k ε) 2 (volume.restrict (Ioi 0)) ∧
        (∫ t in Ioi (0 : ℝ), ‖mobiusDampingJetSource k ε t‖ ^ (2 : ℕ)) ≤
          ∫ ξ : ℝ, ‖hardyLineMajorant (K * (k.factorial : ℝ) / r ^ k) ξ‖ ^ (2 : ℕ) := by
  obtain ⟨r, K, hr, hK, hH⟩ := exists_uniform_mobiusDampingJetQuotient_hardy ha
  refine ⟨r, K, hr, hK, fun k ε haε => ?_⟩
  have hε : 0 < ε := by linarith [half_le_zetaZeroAbscissa]
  let τ : ℝ := (max 0 (1 / 2 - ε) + 1 / 2) / 2
  have hτ0 : 0 < τ := by
    dsimp [τ]
    linarith [le_max_left 0 (1 / 2 - ε)]
  have hτ1 : τ < 1 / 2 := by
    have hmax : max 0 (1 / 2 - ε) < 1 / 2 := max_lt (by norm_num) (by linarith)
    dsimp [τ]
    linarith
  have hτε : 1 / 2 < τ + ε := by
    dsimp [τ]
    linarith [le_max_right 0 (1 / 2 - ε)]
  apply memLp_and_mass_le_of_mellin_line (measurable_mobiusDampingJetSource k ε)
    (fun t ht => mobiusDampingJetSource_eq_zero_of_one_lt k ε ht) (hH k ε haε) hτ0
  · intro ξ
    apply (hasMellin_mobiusDampingJetSource k ε ?_ ?_ ?_).1
    all_goals simp only [add_re, rayLine_re]; norm_num; linarith
  · intro ξ
    apply (hasMellin_mobiusDampingJetSource k ε ?_ ?_ ?_).2
    all_goals simp only [add_re, rayLine_re]; norm_num; linarith

theorem integral_sq_hardyLineMajorant (K : ℝ) :
    (∫ ξ : ℝ, ‖hardyLineMajorant K ξ‖ ^ (2 : ℕ)) =
      K ^ 2 * ∫ ξ : ℝ, ‖hardyLineMajorant 1 ξ‖ ^ (2 : ℕ) := by
  simp only [hardyLineMajorant, one_mul, Real.norm_eq_abs, sq_abs, mul_pow]
  exact integral_const_mul _ _

/-- A common factorial square-mass budget for the physical arithmetic jets. -/
theorem exists_uniform_mobiusDampingJetSource_factorial_budget {a : ℝ}
    (ha : zetaZeroAbscissa < 1 / 2 + a) :
    ∃ r B : ℝ, 0 < r ∧ 0 ≤ B ∧ ∀ (k : ℕ) (ε : ℝ), a ≤ ε →
      MemLp (mobiusDampingJetSource k ε) 2 (volume.restrict (Ioi 0)) ∧
        (∫ t in Ioi (0 : ℝ), ‖mobiusDampingJetSource k ε t‖ ^ (2 : ℕ)) ≤
          B * ((k.factorial : ℝ) / r ^ k) ^ 2 := by
  obtain ⟨r, K, hr, _, hb⟩ := exists_uniform_mobiusDampingJetSource_budget ha
  have hI : 0 ≤ ∫ ξ : ℝ, ‖hardyLineMajorant 1 ξ‖ ^ (2 : ℕ) :=
    integral_nonneg fun _ => sq_nonneg _
  refine ⟨r, K ^ 2 * ∫ ξ : ℝ, ‖hardyLineMajorant 1 ξ‖ ^ (2 : ℕ), hr,
    mul_nonneg (sq_nonneg K) hI, fun k ε haε => ?_⟩
  refine ⟨(hb k ε haε).1, (hb k ε haε).2.trans_eq ?_⟩
  rw [integral_sq_hardyLineMajorant]
  ring

/-- Every literal logarithmic damping jet is admitted strictly above the zero width. -/
theorem memLp_mobiusDampingJetSource (k : ℕ) {ε : ℝ}
    (hε : zetaZeroAbscissa < 1 / 2 + ε) :
    MemLp (mobiusDampingJetSource k ε) 2 (volume.restrict (Ioi 0)) := by
  obtain ⟨_, _, _, _, hb⟩ := exists_uniform_mobiusDampingJetSource_budget hε
  exact (hb k ε le_rfl).1

end RHTower

