import GaloisForLFunctions.RHTower.CriticalDiscEulerOrbitDensity
import GaloisForLFunctions.RHTower.TraceHankelAnalyticInstability
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Odd-to-even normalized trace germs

The normalized trace-moment passage is the divided difference `dslope` at the
functional-equation centre.  This file records the exact odd/even algebra and
the Schwarz-lemma estimate which makes division continuous only after passing
from a larger disc to a strictly smaller one.
-/

noncomputable section

namespace RHTower

open Complex Set Metric ComplexConjugate

/-- Normalized division of a centred odd trace germ. -/
def normalizedTraceMomentGerm (T : ℂ → ℂ) : ℂ → ℂ :=
  fun z ↦ -dslope T 0 z

/-- The canonical odd preimage of an even trace-moment germ. -/
def oddTracePreimage (g : ℂ → ℂ) : ℂ → ℂ :=
  fun z ↦ -z * g z

theorem dslope_odd_even
    (T : ℂ → ℂ) (hodd : ∀ z, T (-z) = -T z) (h0 : T 0 = 0) :
    ∀ z, dslope T 0 (-z) = dslope T 0 z := by
  intro z
  by_cases hz : z = 0
  · subst z
    simp
  · have hnz : -z ≠ 0 := neg_ne_zero.mpr hz
    rw [dslope_of_ne _ hnz, dslope_of_ne _ hz,
      slope_def_module, slope_def_module, h0, hodd]
    simp [smul_eq_mul]

theorem normalizedTraceMomentGerm_even
    (T : ℂ → ℂ) (hodd : ∀ z, T (-z) = -T z) (h0 : T 0 = 0) :
    ∀ z, normalizedTraceMomentGerm T (-z) = normalizedTraceMomentGerm T z := by
  intro z
  rw [normalizedTraceMomentGerm, normalizedTraceMomentGerm,
    dslope_odd_even T hodd h0]

theorem oddTracePreimage_odd
    (g : ℂ → ℂ) (heven : ∀ z, g (-z) = g z) :
    ∀ z, oddTracePreimage g (-z) = -oddTracePreimage g z := by
  intro z
  simp [oddTracePreimage, heven]

theorem oddTracePreimage_schwarz
    (g : ℂ → ℂ) (hschwarz : ∀ z, conj (g (conj z)) = g z) :
    ∀ z, conj (oddTracePreimage g (conj z)) = oddTracePreimage g z := by
  intro z
  simp [oddTracePreimage, map_mul, hschwarz]

/-- Divided difference is a left inverse to multiplication by the centred
coordinate, including at the centre where it reads the derivative. -/
theorem dslope_mul_self
    (g : ℂ → ℂ) (hg : DifferentiableAt ℂ g 0) :
    ∀ z, dslope (fun z ↦ z * g z) 0 z = g z := by
  intro z
  by_cases hz : z = 0
  · subst z
    rw [dslope_same]
    change deriv (id * g) 0 = g 0
    simpa using ((hasDerivAt_id (0 : ℂ)).mul hg.hasDerivAt).deriv
  · rw [dslope_of_ne _ hz, slope_def_module]
    simp [hz, smul_eq_mul]

/-- Exact inverse identity for the normalized odd-to-even passage. -/
theorem normalizedTraceMomentGerm_oddTracePreimage
    (g : ℂ → ℂ) (hg : DifferentiableAt ℂ g 0) :
    normalizedTraceMomentGerm (oddTracePreimage g) = g := by
  funext z
  unfold normalizedTraceMomentGerm oddTracePreimage
  by_cases hz : z = 0
  · subst z
    rw [dslope_same]
    rw [show (fun z : ℂ => -z * g z) = (-id) * g by rfl]
    have hder := ((hasDerivAt_id (0 : ℂ)).neg.mul hg.hasDerivAt).deriv
    simpa using congrArg Neg.neg hder
  · rw [dslope_of_ne _ hz, slope_def_module]
    simp [hz, smul_eq_mul]

/-- The larger-disc/smaller-disc bound governing normalized division.  A
uniform error `R₂` on a disc of radius `R₁` becomes at most `R₂/R₁`
after division by the centred coordinate, uniformly throughout that disc. -/
theorem norm_normalizedTraceMomentGerm_le_div_of_mapsTo_ball
    {T : ℂ → ℂ} {R₁ R₂ : ℝ}
    (hT : DifferentiableOn ℂ T (ball 0 R₁))
    (hmaps : MapsTo T (ball 0 R₁) (closedBall (T 0) R₂))
    {z : ℂ} (hz : z ∈ ball 0 R₁) :
    ‖normalizedTraceMomentGerm T z‖ ≤ R₂ / R₁ := by
  rw [normalizedTraceMomentGerm, norm_neg]
  exact norm_dslope_le_div_of_mapsTo_ball hT hmaps hz

/-- Analyticity at the centre survives normalized division. -/
theorem analyticAt_normalizedTraceMomentGerm
    {T : ℂ → ℂ} (hT : AnalyticAt ℂ T 0) :
    AnalyticAt ℂ (normalizedTraceMomentGerm T) 0 := by
  rcases hT with ⟨p, hp⟩
  have hs := hp.has_fpower_series_dslope_fslope
  have hneg : HasFPowerSeriesAt
      ((-1 : ℂ) • dslope T 0) ((-1 : ℂ) • p.fslope) 0 :=
    hs.const_smul
  exact ⟨-p.fslope, by
    change HasFPowerSeriesAt (-dslope T 0) (-p.fslope) 0
    simpa only [neg_smul, one_smul] using hneg⟩

/-!
## Exact Euler-orbit to trace-moment coupling

The centered rotation identifies even Schwarz moment germs with FE-odd Schwarz trace germs on the
critical disc.  Combining that identification with the genuine Euler-unit orbit theorem and the
analytic trace-Hankel perturbation gives the missing capstone: arbitrarily close moment germs that
fail Hankel positivity still come from targets in the closed finite Euler-unit orbit.
-/

/-- Convert a centered even moment germ into the FE-odd trace germ on the critical coordinate. -/
def evenMomentToCriticalTrace (g : ℂ → ℂ) : ℂ → ℂ :=
  fun s ↦ -(s - 1 / 2) * g (-Complex.I * (s - 1 / 2))

/-- Rotate a critical-coordinate trace back to the centered spectral coordinate. -/
def criticalTraceToCenteredOdd (T : ℂ → ℂ) : ℂ → ℂ :=
  fun z ↦ -Complex.I * T (1 / 2 + Complex.I * z)

theorem evenMomentToCriticalTrace_antireflection
    (g : ℂ → ℂ) (heven : ∀ z, g (-z) = g z) :
    ∀ s, evenMomentToCriticalTrace g (1 - s) = -evenMomentToCriticalTrace g s := by
  intro s
  simp only [evenMomentToCriticalTrace]
  have harg : -Complex.I * (1 - s - 1 / 2) =
      -(-Complex.I * (s - 1 / 2)) := by ring
  rw [harg, heven]
  ring

theorem evenMomentToCriticalTrace_schwarz
    (g : ℂ → ℂ) (heven : ∀ z, g (-z) = g z)
    (hschwarz : ∀ z, g (conj z) = conj (g z)) :
    ∀ s, evenMomentToCriticalTrace g (conj s) =
      conj (evenMomentToCriticalTrace g s) := by
  intro s
  simp only [evenMomentToCriticalTrace, map_mul, map_neg]
  have htwo : conj (2 : ℂ) = 2 := map_ofNat (starRingEnd ℂ) 2
  have hhalf : conj (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, htwo]
  have harg : -Complex.I * (conj s - 1 / 2) =
      -(conj (-Complex.I * (s - 1 / 2))) := by
    rw [map_mul, map_neg, conj_I, map_sub, hhalf]
    ring
  rw [harg, heven, hschwarz]
  rw [map_sub, hhalf]

theorem criticalTraceToCenteredOdd_evenMomentToCriticalTrace
    (g : ℂ → ℂ) :
    criticalTraceToCenteredOdd (evenMomentToCriticalTrace g) = oddTracePreimage g := by
  funext z
  simp only [criticalTraceToCenteredOdd, evenMomentToCriticalTrace, oddTracePreimage]
  have hrot : -Complex.I * (Complex.I * z) = z := by
    rw [← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]
  rw [show 1 / 2 + Complex.I * z - 1 / 2 = Complex.I * z by ring, hrot]
  rw [← mul_assoc, mul_neg, hrot]

/-- Normalized division exactly recovers the original even moment germ. -/
theorem normalizedTraceMomentGerm_criticalTraceToCenteredOdd_evenMomentToCriticalTrace
    (g : ℂ → ℂ) (hg : DifferentiableAt ℂ g 0) :
    normalizedTraceMomentGerm
        (criticalTraceToCenteredOdd (evenMomentToCriticalTrace g)) = g := by
  rw [criticalTraceToCenteredOdd_evenMomentToCriticalTrace]
  exact normalizedTraceMomentGerm_oddTracePreimage g hg

theorem diffContOnCl_evenMomentToCriticalTrace
    (g : ℂ → ℂ) {r : ℝ} (hg : DiffContOnCl ℂ g (ball 0 r)) :
    DiffContOnCl ℂ (evenMomentToCriticalTrace g) (ball (1 / 2 : ℂ) r) := by
  let phi : ℂ → ℂ := fun s ↦ -Complex.I * (s - 1 / 2)
  have hphiDiff : Differentiable ℂ phi := by
    dsimp [phi]
    fun_prop
  have hphi : DiffContOnCl ℂ phi (ball (1 / 2 : ℂ) r) :=
    hphiDiff.diffContOnCl
  have hmap : MapsTo phi (ball (1 / 2 : ℂ) r) (ball 0 r) := by
    intro s hs
    rw [mem_ball, dist_zero_right]
    dsimp [phi]
    rw [norm_mul, norm_neg, norm_I, one_mul]
    simpa [mem_ball, dist_eq_norm] using hs
  have hgcomp : DiffContOnCl ℂ (g ∘ phi) (ball (1 / 2 : ℂ) r) :=
    hg.comp hphi hmap
  have hscalar : DiffContOnCl ℂ (fun s : ℂ ↦ -(s - 1 / 2))
      (ball (1 / 2 : ℂ) r) := by
    apply Differentiable.diffContOnCl
    fun_prop
  have hprod := hscalar.smul hgcomp
  change DiffContOnCl ℂ
    (fun s : ℂ ↦ -(s - 1 / 2) * g (-Complex.I * (s - 1 / 2)))
      (ball (1 / 2 : ℂ) r)
  simpa only [phi, Function.comp_def, smul_eq_mul] using hprod

/-- Every analytic even Schwarz moment germ is the normalized trace of a critical-disc target in
the closure of the genuine local Euler-unit group, after any finite prime deletion. -/
theorem evenMomentGerm_realEulerOrbitClosure_and_normalizedTrace
    (g : ℂ → ℂ) {r₀ r₁ epsilon : ℝ}
    (hr₀ : 0 ≤ r₀) (hr01 : r₀ < r₁) (hr1 : r₁ < 1 / 2)
    (hepsilon : 0 < epsilon)
    (hg : DiffContOnCl ℂ g (ball 0 r₁))
    (heven : ∀ z, g (-z) = g z)
    (hschwarz : ∀ z, g (conj z) = conj (g z))
    (S : Finset Nat.Primes) :
    criticalDiscRestriction (evenMomentToCriticalTrace g) r₀
        ((diffContOnCl_evenMomentToCriticalTrace g hg).continuousOn_ball.mono
          (Metric.closedBall_subset_closedBall hr01.le)) ∈
      (criticalDiscRealEulerIncrementGroup r₀ S epsilon).topologicalClosure ∧
    normalizedTraceMomentGerm
        (criticalTraceToCenteredOdd (evenMomentToCriticalTrace g)) = g := by
  have htrace := diffContOnCl_evenMomentToCriticalTrace g hg
  have hmem := criticalDisc_analytic_odd_schwarz_mem_realEulerIncrementGroup_closure
    (evenMomentToCriticalTrace g) hr₀ hr01 hr1 hepsilon htrace
    (fun z hz ↦ evenMomentToCriticalTrace_antireflection g heven z)
    (evenMomentToCriticalTrace_schwarz g heven hschwarz) S
  have hr₁pos : 0 < r₁ := lt_of_le_of_lt hr₀ hr01
  have hg0 : DifferentiableAt ℂ g 0 :=
    hg.differentiableAt isOpen_ball (by simpa [mem_ball] using hr₁pos)
  exact ⟨hmem,
    normalizedTraceMomentGerm_criticalTraceToCenteredOdd_evenMomentToCriticalTrace g hg0⟩

theorem diffContOnCl_remoteEvenPerturbation
    {f : ℂ → ℂ} {r : ℝ} (hf : DiffContOnCl ℂ f (ball 0 r)) (N : ℕ) :
    DiffContOnCl ℂ (remoteEvenPerturbation f N) (ball 0 r) := by
  have hpoly : DiffContOnCl ℂ
      (fun z : ℂ ↦ (analyticTraceMoments f (2 * N) + 1 : ℝ) * z ^ (4 * N))
      (ball 0 r) := by
    apply Differentiable.diffContOnCl
    fun_prop
  change DiffContOnCl ℂ
    (f - fun z : ℂ ↦ (analyticTraceMoments f (2 * N) + 1 : ℝ) * z ^ (4 * N))
    (ball 0 r)
  exact hf.sub hpoly

/-- Every compact-open neighborhood of an even Schwarz trace-moment target contains a normalized
moment germ which fails trace-Hankel positivity and whose critical trace lies in the closure of the
genuine finite Euler-unit orbit. -/
theorem exists_close_realEulerOrbit_normalizedTraceHankel_failure
    {f : ℂ → ℂ} {r₀ r₁ B closeEpsilon orbitEpsilon : ℝ}
    (hr₀ : 0 ≤ r₀) (hr₀1 : r₀ < 1) (hr01 : r₀ < r₁)
    (hf : DiffContOnCl ℂ f (ball 0 r₁))
    (hB : ∀ z ∈ sphere (0 : ℂ) r₁, ‖f z‖ ≤ B)
    (hB0 : 0 ≤ B) (hclose : 0 < closeEpsilon)
    (horbit : 0 < orbitEpsilon)
    (heven : ∀ z, f (-z) = f z)
    (hschwarz : ∀ z, conj (f (conj z)) = f z)
    (S : Finset Nat.Primes) (hr1 : r₁ < 1 / 2) :
    ∃ g : ℂ → ℂ,
      ∃ hg : DiffContOnCl ℂ g (ball 0 r₁),
        (∀ z ∈ closedBall (0 : ℂ) r₀, ‖g z - f z‖ < closeEpsilon) ∧
        ¬ AnalyticTraceHankelNonnegative g ∧
        criticalDiscRestriction (evenMomentToCriticalTrace g) r₀
            ((diffContOnCl_evenMomentToCriticalTrace g hg).continuousOn_ball.mono
                (Metric.closedBall_subset_closedBall hr01.le)) ∈
          (criticalDiscRealEulerIncrementGroup r₀ S orbitEpsilon).topologicalClosure ∧
        normalizedTraceMomentGerm
            (criticalTraceToCenteredOdd (evenMomentToCriticalTrace g)) = g := by
  obtain ⟨N, hcloseN⟩ := eventually_remoteEvenPerturbation_uniformly_close
    hr₀ hr₀1 hr01 hf hB hB0 hclose
  let g := remoteEvenPerturbation f N
  have hr₁pos : 0 < r₁ := lt_of_le_of_lt hr₀ hr01
  have hfat : AnalyticAt ℂ f 0 :=
    (hf.differentiableOn.analyticOnNhd isOpen_ball) 0
      (by simpa [mem_ball] using hr₁pos)
  have hgdiff := diffContOnCl_remoteEvenPerturbation hf N
  have hgeven := remoteEvenPerturbation_even heven N
  have hgschwarz : ∀ z, g (conj z) = conj (g z) := by
    intro z
    have h := remoteEvenPerturbation_schwarz hschwarz N z
    change remoteEvenPerturbation f N (conj z) =
      conj (remoteEvenPerturbation f N z)
    rw [← h]
    simp
  have hcap := evenMomentGerm_realEulerOrbitClosure_and_normalizedTrace
    g hr₀ hr01 hr1 horbit hgdiff hgeven hgschwarz S
  refine ⟨g, hgdiff, ?_, remoteEvenPerturbation_not_traceHankel hfat N, hcap.1, hcap.2⟩
  exact hcloseN

end RHTower
