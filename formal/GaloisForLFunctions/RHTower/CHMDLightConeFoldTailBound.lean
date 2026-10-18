import GaloisForLFunctions.RHTower.CHMDMobiusFoldedTransportOfKleinGordonPrimeWave
import GaloisForLFunctions.RHTower.CHMDLightConeBesselZeroAndIntegrationByParts
import GaloisForLFunctions.RHTower.BesselJOneRecurrence
import GaloisForLFunctions.RHTower.Sieve.DirichletTruncationError

/-!
# Quantitative light-cone decay of the Möbius fold

The normalized order-one Bessel kernel has modulus at most one on the forward
light cone. Spatial decay of the d'Alembert kernel and its first two derivatives
therefore gives a folded-source bound with rapidity cost
`(1 + |y|) (1 + y²) exp(π |y|)`. The constant is independent of rapidity and
spatial shift. No cancellation between Möbius coefficients is used.
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace RHTower.CHMDChebyshevTransport

open CHMDLightCone CHMDStage22 CHMDLightConeBesselZero GaloisForLFunctions.HTGeometry

private theorem besselJ_one_eq_integral_besselJ1 (x : ℝ) :
    besselJ 1 x = GaloisForLFunctions.RHTower.besselJ1 x := by
  have hzero : besselJ 0 = GaloisForLFunctions.RHTower.besselJ0 := by
    funext u
    rw [besselJ_zero_eq_integral, GaloisForLFunctions.RHTower.besselJ0_eq_two_div_pi_mul]
  have hd := hasDerivAt_besselJ_zero x
  rw [hzero] at hd
  have heq := hd.unique (GaloisForLFunctions.RHTower.hasDerivAt_besselJ0 x)
  dsimp [GaloisForLFunctions.RHTower.besselJ1]
  linarith

/-- The normalized order-one Bessel kernel is bounded by one for nonnegative arguments. -/
theorem abs_lightConeBesselReal_nonneg_le_one {w : ℝ} (hw : 0 ≤ w) :
    |lightConeBesselReal w| ≤ 1 := by
  by_cases hw0 : w = 0
  · subst w
    simp [lightConeBesselReal_zero]
  have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hxpos : 0 < Real.sqrt w := Real.sqrt_pos.mpr hwpos
  have heq : besselJ 1 (Real.sqrt w) =
      Real.sqrt w / 2 * lightConeBesselReal w := by
    have hc := congr_arg Complex.re (besselJ_one_eq (Real.sqrt w))
    simpa [← ofReal_lightConeBesselReal, ← Complex.ofReal_pow, Real.sq_sqrt hw] using hc
  have h := GaloisForLFunctions.RHTower.abs_besselJ1_le (Real.sqrt w)
  rw [← besselJ_one_eq_integral_besselJ1, heq, abs_mul,
    abs_of_pos (div_pos hxpos (by norm_num)), abs_of_pos hxpos] at h
  by_contra hbad
  have hpos := mul_pos (div_pos hxpos (by norm_num : (0 : ℝ) < 2))
    (sub_pos.mpr (lt_of_not_ge hbad))
  nlinarith

/-- Rapidity cost of the forward light-cone transport of an exponentially decaying spatial jet. -/
def foldRapidityEnvelope (y : ℝ) : ℝ :=
  (1 + |y|) * (1 + y ^ 2) * Real.exp (π * |y|)

theorem foldRapidityEnvelope_nonneg (y : ℝ) : 0 ≤ foldRapidityEnvelope y := by
  unfold foldRapidityEnvelope
  positivity

private theorem abs_lightCone_pair_sub_integral_le {G : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hG : ∀ v, |G v| ≤ C * (1 + |v|) * Real.exp (-(π * |v|))) (y s : ℝ) :
    |G (s + y) + G (s - y) -
      y ^ 2 / 2 * ∫ t in (-1 : ℝ)..1,
        lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
          (G (s + y * t) + G (s - y * t))| ≤
      2 * C * foldRapidityEnvelope y * Real.exp (-((π - 1) * |s|)) := by
  let K := C * (1 + |y|) * Real.exp (π * |y|) * Real.exp (-((π - 1) * |s|))
  have hpair : ∀ t : ℝ, |t| ≤ 1 → |G (s + y * t) + G (s - y * t)| ≤ 2 * K := by
    intro t ht
    have hyt : |y * t| ≤ |y| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg y) ht
    have hyt' : |-(y * t)| ≤ |y| := by rwa [abs_neg]
    have h1 := shift_decay_le hC hG y hyt s
    have h2 := shift_decay_le hC hG y hyt' s
    rw [← sub_eq_add_neg] at h2
    exact (abs_add_le _ _).trans (by change _ ≤ 2 * K; change _ ≤ K at h1 h2; linarith)
  have htail : |∫ t in (-1 : ℝ)..1,
      lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
        (G (s + y * t) + G (s - y * t))| ≤ 4 * K := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1 : ℝ)) (b := 1) (C := 2 * K)
      (f := fun t => lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
        (G (s + y * t) + G (s - y * t))) fun t ht => by
          have hta := mem_uIoc_neg_one_one_abs_le ht
          have ht2 : 0 ≤ 1 - t ^ 2 := by
            obtain ⟨hlo, hhi⟩ := abs_le.mp hta
            nlinarith
          have hB := abs_lightConeBesselReal_nonneg_le_one
            (mul_nonneg (by positivity : 0 ≤ 2 * y ^ 2) ht2)
          rw [Real.norm_eq_abs, abs_mul]
          calc |lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2))| *
                |G (s + y * t) + G (s - y * t)| ≤ 1 * (2 * K) :=
              mul_le_mul hB (hpair t hta) (abs_nonneg _) zero_le_one
            _ = 2 * K := one_mul _
    rw [Real.norm_eq_abs] at h
    norm_num at h
    linarith
  have hp : |G (s + y) + G (s - y)| ≤ 2 * K := by
    simpa using hpair 1 (by norm_num)
  calc
    _ ≤ |G (s + y) + G (s - y)| +
        |y ^ 2 / 2 * ∫ t in (-1 : ℝ)..1,
          lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
            (G (s + y * t) + G (s - y * t))| := abs_sub _ _
    _ ≤ 2 * K + y ^ 2 / 2 * (4 * K) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ y ^ 2 / 2)]
      exact add_le_add hp (mul_le_mul_of_nonneg_left htail (by positivity))
    _ = _ := by dsimp [K, foldRapidityEnvelope]; ring

/-- The conjugated spatial Laplacian has exponential rapidity cost and summable spatial decay. -/
theorem exists_abs_conjugatedLaplacian_le_rapidity_envelope :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y s : ℝ, 0 ≤ s →
      |conjugatedLaplacian y s| ≤
        C * foldRapidityEnvelope y * Real.exp (-((π - 1 / 2) * s)) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_abs_dAlembertDeriv_le
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_abs_dAlembertDeriv2_le
  refine ⟨2 * C₂ + 2 * C₁ + 4, by positivity, fun y s hs => ?_⟩
  have h0 : |chmdPrimeKernel y s| ≤
      16 * foldRapidityEnvelope y * Real.exp (-((π - 1) * s)) := by
    have h := abs_lightCone_pair_sub_integral_le (C := 8) (by norm_num)
      (G := dAlembertReal) (fun v => by
        rw [abs_of_pos (dAlembertReal_pos v)]
        exact dAlembertReal_le v) y s
    rw [chmdPrimeKernel_eq_pair_sub_tail, lightConeTail]
    simpa only [abs_of_nonneg hs, show (2 : ℝ) * 8 = 16 by norm_num] using h
  have h1 : |kernelDeriv y s| ≤
      2 * C₁ * foldRapidityEnvelope y * Real.exp (-((π - 1) * s)) := by
    simpa [kernelDeriv, abs_of_nonneg hs] using
      abs_lightCone_pair_sub_integral_le hC₁0 hC₁ y s
  have h2 : |kernelDeriv2 y s| ≤
      2 * C₂ * foldRapidityEnvelope y * Real.exp (-((π - 1) * s)) := by
    simpa [kernelDeriv2, abs_of_nonneg hs] using
      abs_lightCone_pair_sub_integral_le hC₂0 hC₂ y s
  have hexp : Real.exp (-((π - 1 / 2) * s)) =
      Real.exp (-(s / 2)) * Real.exp (-((π - 1) * s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [conjugatedLaplacian, abs_mul, abs_of_pos (Real.exp_pos _), hexp]
  calc
    _ ≤ Real.exp (-(s / 2)) *
        (|kernelDeriv2 y s| + |kernelDeriv y s| + |chmdPrimeKernel y s| / 4) := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      refine (abs_add_le _ _).trans ?_
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      linarith [abs_sub (kernelDeriv2 y s) (kernelDeriv y s)]
    _ ≤ Real.exp (-(s / 2)) *
        ((2 * C₂ * foldRapidityEnvelope y * Real.exp (-((π - 1) * s))) +
          (2 * C₁ * foldRapidityEnvelope y * Real.exp (-((π - 1) * s))) +
          (16 * foldRapidityEnvelope y * Real.exp (-((π - 1) * s))) / 4) := by
      gcongr
    _ = _ := by ring

/-- A single fold has summable spatial decay with polynomial times exponential rapidity cost. -/
theorem exists_abs_mobiusFold_le_rapidity_envelope :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y v : ℝ, 0 ≤ v →
      |mobiusFold y v| ≤
        C * foldRapidityEnvelope y * Real.exp (-((π - 1 / 2) * v)) := by
  obtain ⟨D, hD0, hD⟩ := exists_abs_conjugatedLaplacian_le_rapidity_envelope
  refine ⟨sourceBound * D * (π - 3 / 2)⁻¹, by
    exact mul_nonneg (mul_nonneg sourceBound_nonneg hD0)
      (inv_nonneg.mpr pi_sub_three_half_pos.le), fun y v hv => ?_⟩
  let C := D * foldRapidityEnvelope y
  have hC : ∀ s : ℝ, 0 ≤ s → |conjugatedLaplacian y s| ≤
      C * Real.exp (-((π - 1 / 2) * s)) := hD y
  rw [mobiusFold_eq_setIntegral]
  have hdom : IntegrableOn
      (fun s : ℝ => sourceBound * Real.exp (-v) * C * Real.exp (-((π - 3 / 2) * s)))
      (Ioi v) := by
    have h : IntegrableOn (fun s : ℝ => sourceBound * Real.exp (-v) * C *
        Real.exp (-(π - 3 / 2) * s)) (Ioi v) :=
      (exp_neg_integrableOn_Ioi v pi_sub_three_half_pos).const_mul _
    refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp only [neg_mul]
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi v))
    (f := fun s => ccmPrimeDeficitDilationSource (s - v) * conjugatedLaplacian y s) hdom
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => by
      have hsl : v < s := hs
      have hs0 : 0 ≤ s := hv.trans hsl.le
      rw [Real.norm_eq_abs, abs_mul]
      calc |ccmPrimeDeficitDilationSource (s - v)| * |conjugatedLaplacian y s|
          ≤ sourceBound * Real.exp (s - v) *
              (C * Real.exp (-((π - 1 / 2) * s))) :=
            mul_le_mul (abs_ccmPrimeDeficitDilationSource_le (sub_nonneg.mpr hsl.le))
              (hC s hs0) (abs_nonneg _) (mul_nonneg sourceBound_nonneg (Real.exp_pos _).le)
        _ = sourceBound * Real.exp (-v) * C * Real.exp (-((π - 3 / 2) * s)) := by
          rw [Real.exp_sub, show sourceBound * (Real.exp s / Real.exp v) *
              (C * Real.exp (-((π - 1 / 2) * s))) = sourceBound * (Real.exp v)⁻¹ * C *
              (Real.exp s * Real.exp (-((π - 1 / 2) * s))) by ring,
            ← Real.exp_add, Real.exp_neg]
          congr 2
          ring))
  rw [Real.norm_eq_abs, integral_const_mul, integral_Ioi_exp_neg_mul' pi_sub_three_half_pos] at h
  refine h.trans (le_of_eq ?_)
  rw [show sourceBound * Real.exp (-v) * C *
      ((π - 3 / 2)⁻¹ * Real.exp (-((π - 3 / 2) * v))) =
      sourceBound * C * (π - 3 / 2)⁻¹ *
        (Real.exp (-v) * Real.exp (-((π - 3 / 2) * v))) by ring,
    ← Real.exp_add]
  have hexp : -v + -((π - 3 / 2) * v) = -((π - 1 / 2) * v) := by ring
  rw [hexp]
  dsimp [C]
  ring

/-- The complete absolute fold tail has an explicit joint cutoff and rapidity bound. -/
theorem exists_tsum_abs_mobiusFold_tail_le_rapidity_envelope :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : ℝ) (N : ℕ), 1 ≤ N →
      (∑' j : ℕ, |mobiusFold y (Real.log ((j + N + 1 : ℕ) : ℝ))|) ≤
        C * foldRapidityEnvelope y * (N : ℝ) ^ (-(π - 3 / 2)) := by
  obtain ⟨D, hD0, hD⟩ := exists_abs_mobiusFold_le_rapidity_envelope
  refine ⟨D / (π - 3 / 2), div_nonneg hD0 pi_sub_three_half_pos.le, fun y N hN => ?_⟩
  let p : ℝ := π - 1 / 2
  have hp : 1 < p := by dsimp [p]; linarith [Real.pi_gt_three]
  have hs : Summable (fun j : ℕ => ((j + N + 1 : ℕ) : ℝ) ^ (-p)) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (N + 1)).2
        (Real.summable_nat_rpow.mpr (by linarith : -p < -1))
  have hmajor := hs.mul_left (D * foldRapidityEnvelope y)
  have hpoint : ∀ j : ℕ, |mobiusFold y (Real.log ((j + N + 1 : ℕ) : ℝ))| ≤
      D * foldRapidityEnvelope y * ((j + N + 1 : ℕ) : ℝ) ^ (-p) := by
    intro j
    have hn : (1 : ℝ) ≤ ((j + N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j + N + 1)
    have hn0 : (0 : ℝ) < ((j + N + 1 : ℕ) : ℝ) := by linarith
    have h := hD y (Real.log ((j + N + 1 : ℕ) : ℝ)) (Real.log_nonneg hn)
    have he : Real.exp (-(p * Real.log ((j + N + 1 : ℕ) : ℝ))) =
        ((j + N + 1 : ℕ) : ℝ) ^ (-p) := by
      rw [Real.rpow_def_of_pos hn0]
      congr 1
      push_cast
      ring
    change _ ≤ D * foldRapidityEnvelope y * Real.exp (-(p * Real.log ((j + N + 1 : ℕ) : ℝ))) at h
    rw [he] at h
    exact h
  have hsum := hmajor.of_nonneg_of_le (fun j => abs_nonneg _) hpoint
  calc
    _ ≤ ∑' j : ℕ, D * foldRapidityEnvelope y * ((j + N + 1 : ℕ) : ℝ) ^ (-p) :=
      Summable.tsum_le_tsum hpoint hsum hmajor
    _ = D * foldRapidityEnvelope y * ∑' j : ℕ, ((j + N + 1 : ℕ) : ℝ) ^ (-p) :=
      tsum_mul_left
    _ ≤ D * foldRapidityEnvelope y * ((N : ℝ) ^ (1 - p) / (p - 1)) :=
      mul_le_mul_of_nonneg_left (Sieve.tsum_tail_rpow_neg_le hp hN)
        (mul_nonneg hD0 (foldRapidityEnvelope_nonneg y))
    _ = _ := by
      rw [show 1 - p = -(π - 3 / 2) by dsimp [p]; ring,
        show p - 1 = π - 3 / 2 by dsimp [p]; ring]
      ring

end RHTower.CHMDChebyshevTransport

end
