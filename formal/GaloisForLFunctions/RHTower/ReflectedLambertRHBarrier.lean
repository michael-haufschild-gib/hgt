import GaloisForLFunctions.RHTower.CriticalDiscReflectedLambertUniversality
import GaloisForLFunctions.RHTower.CriticalTraceMomentGerm
import GaloisForLFunctions.RHTower.PrimeArchThetaAllOrderCumulant

/-!
# Reflected-Lambert universality and the local-germ RH barrier

This capstone transports the universal reflected-Lambert orbit law through
the exact odd-to-even normalized trace map, specializes it to every cofinite
prime-logarithm spectrum, and joins it to the source-side Hankel criterion
equivalent to the Riemann hypothesis.
-/

noncomputable section

namespace RHTower

open Complex Set Metric ComplexConjugate

/-! ## Abstract spectral transport to moment germs -/

/-- Every analytic even Schwarz-real moment germ is the exact normalized
trace of a target in the closed genuine-increment orbit of any positive
strongly sector-Blaschke-complete spectrum. -/
theorem evenMomentGerm_frequencyOrbitClosure_and_normalizedTrace
    {ι : Type*} (lambda : ι → ℝ)
    (hpositive : ∀ i, 0 < lambda i)
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hcomplete : StrongSectorBlaschkeComplete lambda R₀)
    (g : ℂ → ℂ) {r₀ r₁ epsilon : ℝ}
    (hr₀ : 0 ≤ r₀) (hr01 : r₀ < r₁) (hr1 : r₁ < 1 / 2)
    (hepsilon : 0 < epsilon)
    (hg : DiffContOnCl ℂ g (ball 0 r₁))
    (heven : ∀ z, g (-z) = g z)
    (hschwarz : ∀ z, g (conj z) = conj (g z)) :
    criticalDiscRestriction (evenMomentToCriticalTrace g) r₀
        ((diffContOnCl_evenMomentToCriticalTrace g hg).continuousOn_ball.mono
          (Metric.closedBall_subset_closedBall hr01.le)) ∈
      (criticalDiscSafeRealFrequencyIncrementGroup
        r₀ lambda epsilon).topologicalClosure ∧
    normalizedTraceMomentGerm
        (criticalTraceToCenteredOdd (evenMomentToCriticalTrace g)) = g := by
  have htrace := diffContOnCl_evenMomentToCriticalTrace g hg
  have hmem :=
    criticalDisc_analytic_odd_schwarz_mem_safeFrequencyIncrementGroup_closure
      lambda hpositive hR₀ hcomplete
      (evenMomentToCriticalTrace g) hr₀ hr01 hr1 hepsilon htrace
      (fun z _ ↦ evenMomentToCriticalTrace_antireflection g heven z)
      (evenMomentToCriticalTrace_schwarz g heven hschwarz)
  have hr₁pos : 0 < r₁ := lt_of_le_of_lt hr₀ hr01
  have hg0 : DifferentiableAt ℂ g 0 :=
    hg.differentiableAt isOpen_ball
      (by simpa [mem_ball] using hr₁pos)
  exact ⟨hmem,
    normalizedTraceMomentGerm_criticalTraceToCenteredOdd_evenMomentToCriticalTrace
      g hg0⟩

/-- Every compact-disc neighbourhood contains an exact normalized moment
germ failing a finite Hankel-square test, while its trace target still lies
in the closed genuine-increment orbit. -/
theorem exists_close_frequencyOrbit_normalizedTraceHankel_failure
    {ι : Type*} (lambda : ι → ℝ)
    (hpositive : ∀ i, 0 < lambda i)
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hcomplete : StrongSectorBlaschkeComplete lambda R₀)
    {f : ℂ → ℂ} {r₀ r₁ B closeEpsilon orbitEpsilon : ℝ}
    (hr₀ : 0 ≤ r₀) (hr₀1 : r₀ < 1) (hr01 : r₀ < r₁)
    (hf : DiffContOnCl ℂ f (ball 0 r₁))
    (hB : ∀ z ∈ sphere (0 : ℂ) r₁, ‖f z‖ ≤ B)
    (hB0 : 0 ≤ B) (hclose : 0 < closeEpsilon)
    (horbit : 0 < orbitEpsilon)
    (heven : ∀ z, f (-z) = f z)
    (hschwarz : ∀ z, conj (f (conj z)) = f z)
    (hr1 : r₁ < 1 / 2) :
    ∃ g : ℂ → ℂ,
      ∃ hg : DiffContOnCl ℂ g (ball 0 r₁),
        (∀ z ∈ closedBall (0 : ℂ) r₀,
          ‖g z - f z‖ < closeEpsilon) ∧
        ¬ AnalyticTraceHankelNonnegative g ∧
        criticalDiscRestriction (evenMomentToCriticalTrace g) r₀
            ((diffContOnCl_evenMomentToCriticalTrace g hg).continuousOn_ball.mono
              (Metric.closedBall_subset_closedBall hr01.le)) ∈
          (criticalDiscSafeRealFrequencyIncrementGroup
            r₀ lambda orbitEpsilon).topologicalClosure ∧
        normalizedTraceMomentGerm
            (criticalTraceToCenteredOdd (evenMomentToCriticalTrace g)) = g := by
  obtain ⟨N, hcloseN⟩ :=
    eventually_remoteEvenPerturbation_uniformly_close
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
  have hcap :=
    evenMomentGerm_frequencyOrbitClosure_and_normalizedTrace
      lambda hpositive hR₀ hcomplete
      g hr₀ hr01 hr1 horbit hgdiff hgeven hgschwarz
  refine ⟨g, hgdiff, hcloseN,
    remoteEvenPerturbation_not_traceHankel hfat N, hcap.1, hcap.2⟩

/-! ## Exact cofinite-prime specialization -/

/-- After deleting any finite prime set, every analytic even Schwarz-real
moment germ is an exact normalized trace of a target in the cofinite
prime-logarithm increment-orbit closure. -/
theorem evenMomentGerm_cofinitePrimeLogOrbitClosure_and_normalizedTrace
    (S : Finset Nat.Primes)
    (g : ℂ → ℂ) {r₀ r₁ epsilon : ℝ}
    (hr₀ : 0 ≤ r₀) (hr01 : r₀ < r₁) (hr1 : r₁ < 1 / 2)
    (hepsilon : 0 < epsilon)
    (hg : DiffContOnCl ℂ g (ball 0 r₁))
    (heven : ∀ z, g (-z) = g z)
    (hschwarz : ∀ z, g (conj z) = conj (g z)) :
    criticalDiscRestriction (evenMomentToCriticalTrace g) r₀
        ((diffContOnCl_evenMomentToCriticalTrace g hg).continuousOn_ball.mono
          (Metric.closedBall_subset_closedBall hr01.le)) ∈
      (criticalDiscSafeRealFrequencyIncrementGroup
        r₀ (cofinitePrimeLog S) epsilon).topologicalClosure ∧
    normalizedTraceMomentGerm
        (criticalTraceToCenteredOdd (evenMomentToCriticalTrace g)) = g := by
  exact evenMomentGerm_frequencyOrbitClosure_and_normalizedTrace
    (cofinitePrimeLog S) (cofinitePrimeLog_positive S)
    (R₀ := 1) (by norm_num)
    (cofinitePrimeLog_strongSectorBlaschkeComplete' S 1 (by norm_num))
    g hr₀ hr01 hr1 hepsilon hg heven hschwarz

/-- No continuous Hausdorff-valued reader invariant under the genuine local
increment group can classify analytic trace-Hankel positivity. -/
theorem no_continuous_frequencyInvariant_traceHankel_classifier
    {ι : Type*} (lambda : ι → ℝ)
    (hpositive : ∀ i, 0 < lambda i)
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hcomplete : StrongSectorBlaschkeComplete lambda R₀)
    {r₀ r₁ epsilon : ℝ}
    (hr₀ : 0 ≤ r₀) (hr01 : r₀ < r₁) (hr1 : r₁ < 1 / 2)
    (hepsilon : 0 < epsilon)
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : C(CriticalClosedDisc r₀, ℂ) → Y) (hA : Continuous A)
    (hinvariant : ∀ x g,
      g ∈ criticalDiscSafeRealFrequencyIncrementGroup r₀ lambda epsilon →
      A (x + g) = A x)
    (hclassifies : ∀ (g : ℂ → ℂ)
      (hg : DiffContOnCl ℂ g (ball 0 r₁)),
      (∀ z, g (-z) = g z) →
      (∀ z, g (conj z) = conj (g z)) →
      (A (criticalDiscRestriction (evenMomentToCriticalTrace g) r₀
          ((diffContOnCl_evenMomentToCriticalTrace g hg).continuousOn_ball.mono
            (Metric.closedBall_subset_closedBall hr01.le))) = A 0 ↔
        AnalyticTraceHankelNonnegative g)) :
    False := by
  let g : ℂ → ℂ :=
    remoteEvenPerturbation (fun _ : ℂ ↦ (0 : ℂ)) 0
  have hzeroDiff :
      DiffContOnCl ℂ (fun _ : ℂ ↦ (0 : ℂ)) (ball 0 r₁) := by
    exact differentiable_const 0 |>.diffContOnCl
  have hg : DiffContOnCl ℂ g (ball 0 r₁) :=
    diffContOnCl_remoteEvenPerturbation hzeroDiff 0
  have hgeven : ∀ z, g (-z) = g z :=
    remoteEvenPerturbation_even (fun z ↦ by simp) 0
  have hgschwarz : ∀ z, g (conj z) = conj (g z) := by
    intro z
    have h := remoteEvenPerturbation_schwarz (f := fun _ ↦ 0)
      (fun z ↦ by simp) 0 z
    have h' := congrArg conj h
    simpa [g] using h'
  have heq :
      A (criticalDiscRestriction (evenMomentToCriticalTrace g) r₀
        ((diffContOnCl_evenMomentToCriticalTrace g hg).continuousOn_ball.mono
          (Metric.closedBall_subset_closedBall hr01.le))) = A 0 := by
    exact criticalDisc_continuous_safeFrequencyIncrementInvariant_eq_base
      lambda hpositive hR₀ hcomplete A hA hinvariant
      (evenMomentToCriticalTrace g)
      hr₀ hr01 hr1 hepsilon
      (diffContOnCl_evenMomentToCriticalTrace g hg)
      (fun z _ ↦ evenMomentToCriticalTrace_antireflection g hgeven z)
      (evenMomentToCriticalTrace_schwarz g hgeven hgschwarz)
  have hpositiveG : AnalyticTraceHankelNonnegative g :=
    (hclassifies g hg hgeven hgschwarz).mp heq
  exact (remoteEvenPerturbation_not_traceHankel
    (f := fun _ : ℂ ↦ 0) analyticAt_const 0) hpositiveG

end RHTower
