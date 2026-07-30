import GaloisForLFunctions.RHTower.CriticalDiscSchwarzCompleteness

/-!
# Cofinite Euler tangents test continuous semilocal connection readers

The actual FE-paired Euler-unit tangents remain complete after deleting any finite set of primes.
This file turns that density theorem into operator-facing interfaces.

First, derivatives and mixed derivatives of norm-differentiable compact-operator families are
compact.  Second, a continuous real-linear reader which kills all retained Euler tangents kills
every analytic FE-odd Schwarz-real germ on a smaller critical disc.  The same propagation holds
for compactness and for polarized bilinear readers.

Thus a Calkin-valued semilocal connection need only be checked on finite prime-tangent pairs.  If
those pair values arise as mixed derivatives of a finite completed quasi-inner family, their
compactness is automatic and density propagates it to the full analytic source fibre.

No Xi divisor point, zero-location statement, RH-equivalent positivity, or limiting measure is
used.  The source-side RH application still requires the exact value relation identifying the
semilocal normal-curvature coboundary with such a polarized connection reader.
-/

namespace RHTower

noncomputable section

open Complex Metric Set ComplexConjugate

/-! ## Compactness is stable under norm derivatives -/

/-- The norm derivative of an everywhere compact operator family is compact. -/
theorem isCompactOperator_deriv_of_compact_operator_family
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (F : ℝ → (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hF : ∀ t : ℝ, IsCompactOperator (F t))
    (hderiv : HasDerivAt F T 0) :
    IsCompactOperator T := by
  apply isClosed_setOf_isCompactOperator.mem_of_tendsto hderiv.tendsto_slope
  filter_upwards with t
  exact (hF t).sub (hF 0) |>.smul (t - 0)⁻¹

/-- An iterated mixed derivative of an everywhere compact two-parameter operator family is
compact.  The statement is deliberately ordered: `d₂F s` is the derivative in the second
parameter at zero, and `T` is its derivative in the first parameter at zero. -/
theorem isCompactOperator_mixedDeriv_of_compact_operator_family
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (F : ℝ → ℝ → (H →L[ℂ] H)) (d₂F : ℝ → (H →L[ℂ] H))
    (T : H →L[ℂ] H)
    (hF : ∀ s t : ℝ, IsCompactOperator (F s t))
    (hinner : ∀ s : ℝ, HasDerivAt (F s) (d₂F s) 0)
    (houter : HasDerivAt d₂F T 0) :
    IsCompactOperator T := by
  apply isCompactOperator_deriv_of_compact_operator_family d₂F T
  · intro s
    exact isCompactOperator_deriv_of_compact_operator_family
      (F s) (d₂F s) (hF s) (hinner s)
  · exact houter

/-! ## Cofinite generator tests for continuous readers -/

/-- Every continuous real-linear reader annihilating the cofinite paired Euler tangents also
annihilates every analytic FE-odd Schwarz-real germ on the smaller critical disc.  The target is
an arbitrary real normed space, so the theorem is not restricted to scalar detectors. -/
theorem criticalDisc_connectionReader_eq_zero_of_primeEulerTangent_annihilation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r₀ r₁ : ℝ} (S : Finset Nat.Primes)
    (L : C(CriticalClosedDisc r₀, ℂ) →L[ℝ] E)
    (hL : ∀ p : {p : Nat.Primes // p ∉ S},
      L (compactPrimeEulerUnitFETangent
        (criticalDiscCoordinate r₀) (criticalDiscReflection r₀)
        (p : Nat.Primes)) = 0)
    (f : ℂ → ℂ)
    (hr₀ : 0 ≤ r₀) (hr01 : r₀ < r₁) (hr1 : r₁ < 1 / 2)
    (hf : DiffContOnCl ℂ f (ball (1 / 2 : ℂ) r₁))
    (hodd : ∀ z ∈ closedBall (1 / 2 : ℂ) r₀, f (1 - z) = -f z)
    (hschwarz : ∀ z : ℂ, f (conj z) = conj (f z)) :
    L (criticalDiscRestriction f r₀
      (hf.continuousOn_ball.mono (Metric.closedBall_subset_closedBall hr01.le))) = 0 := by
  let V : Set C(CriticalClosedDisc r₀, ℂ) :=
    Set.range fun p : {p : Nat.Primes // p ∉ S} =>
      compactPrimeEulerUnitFETangent
        (criticalDiscCoordinate r₀) (criticalDiscReflection r₀)
        (p : Nat.Primes)
  have hspan : Submodule.span ℝ V ≤ L.ker := by
    rw [Submodule.span_le]
    rintro g ⟨p, rfl⟩
    exact hL p
  have hclosure : (Submodule.span ℝ V).topologicalClosure ≤ L.ker :=
    Submodule.topologicalClosure_minimal _ hspan (ContinuousLinearMap.isClosed_ker L)
  exact hclosure
    (criticalDisc_analytic_odd_schwarz_mem_realClosedSpan_compl_finset
      f hr₀ hr01 hr1 hf hodd hschwarz S)

/-- Operator-valued form of the generator test: compactness on the cofinite paired Euler
tangents propagates to every analytic FE-odd Schwarz-real germ.  This is the quotient-free Calkin
interface used by semilocal connection problems. -/
theorem criticalDisc_connectionReader_isCompact_of_primeEulerTangent_compactness
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {r₀ r₁ : ℝ} (S : Finset Nat.Primes)
    (L : C(CriticalClosedDisc r₀, ℂ) →L[ℝ] (H →L[ℂ] H))
    (hL : ∀ p : {p : Nat.Primes // p ∉ S},
      IsCompactOperator
        (L (compactPrimeEulerUnitFETangent
          (criticalDiscCoordinate r₀) (criticalDiscReflection r₀)
          (p : Nat.Primes))))
    (f : ℂ → ℂ)
    (hr₀ : 0 ≤ r₀) (hr01 : r₀ < r₁) (hr1 : r₁ < 1 / 2)
    (hf : DiffContOnCl ℂ f (ball (1 / 2 : ℂ) r₁))
    (hodd : ∀ z ∈ closedBall (1 / 2 : ℂ) r₀, f (1 - z) = -f z)
    (hschwarz : ∀ z : ℂ, f (conj z) = conj (f z)) :
    IsCompactOperator
      (L (criticalDiscRestriction f r₀
        (hf.continuousOn_ball.mono (Metric.closedBall_subset_closedBall hr01.le)))) := by
  let V : Set C(CriticalClosedDisc r₀, ℂ) :=
    Set.range fun p : {p : Nat.Primes // p ∉ S} =>
      compactPrimeEulerUnitFETangent
        (criticalDiscCoordinate r₀) (criticalDiscReflection r₀)
        (p : Nat.Primes)
  have hspan : ∀ x ∈ Submodule.span ℝ V, IsCompactOperator (L x) := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => IsCompactOperator (L x))
      ?_ ?_ ?_ ?_ hx
    · rintro x ⟨p, rfl⟩
      exact hL p
    · simpa using! (isCompactOperator_zero : IsCompactOperator (0 : H →L[ℂ] H))
    · intro x y hx hy hcx hcy
      simpa using! hcx.add hcy
    · intro c x hx hcx
      simpa using! hcx.smul c
  have hclosed : IsClosed {x : C(CriticalClosedDisc r₀, ℂ) |
      IsCompactOperator (L x)} := by
    exact isClosed_setOf_isCompactOperator.preimage L.continuous
  exact (closure_minimal hspan hclosed)
    (criticalDisc_analytic_odd_schwarz_mem_realClosedSpan_compl_finset
      f hr₀ hr01 hr1 hf hodd hschwarz S)

/-! ## Polarized connection readers -/

/-- If a continuous real-bilinear reader vanishes on every retained prime-tangent pair, it
vanishes on every pair of analytic FE-odd Schwarz-real germs. -/
theorem criticalDisc_polarizedConnectionReader_eq_zero_of_primeEulerTangent_pairs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r₀ r₁ : ℝ} (S : Finset Nat.Primes)
    (B : C(CriticalClosedDisc r₀, ℂ) →L[ℝ]
      C(CriticalClosedDisc r₀, ℂ) →L[ℝ] E)
    (hB : ∀ p q : {p : Nat.Primes // p ∉ S},
      B (compactPrimeEulerUnitFETangent
          (criticalDiscCoordinate r₀) (criticalDiscReflection r₀)
          (p : Nat.Primes))
        (compactPrimeEulerUnitFETangent
          (criticalDiscCoordinate r₀) (criticalDiscReflection r₀)
          (q : Nat.Primes)) = 0)
    (f g : ℂ → ℂ)
    (hr₀ : 0 ≤ r₀) (hr01 : r₀ < r₁) (hr1 : r₁ < 1 / 2)
    (hf : DiffContOnCl ℂ f (ball (1 / 2 : ℂ) r₁))
    (hodd_f : ∀ z ∈ closedBall (1 / 2 : ℂ) r₀, f (1 - z) = -f z)
    (hschwarz_f : ∀ z : ℂ, f (conj z) = conj (f z))
    (hg : DiffContOnCl ℂ g (ball (1 / 2 : ℂ) r₁))
    (hodd_g : ∀ z ∈ closedBall (1 / 2 : ℂ) r₀, g (1 - z) = -g z)
    (hschwarz_g : ∀ z : ℂ, g (conj z) = conj (g z)) :
    B (criticalDiscRestriction f r₀
        (hf.continuousOn_ball.mono (Metric.closedBall_subset_closedBall hr01.le)))
      (criticalDiscRestriction g r₀
        (hg.continuousOn_ball.mono (Metric.closedBall_subset_closedBall hr01.le))) = 0 := by
  let tf : C(CriticalClosedDisc r₀, ℂ) :=
    criticalDiscRestriction f r₀
      (hf.continuousOn_ball.mono (Metric.closedBall_subset_closedBall hr01.le))
  have hfirst (q : {p : Nat.Primes // p ∉ S}) :
      B tf (compactPrimeEulerUnitFETangent
        (criticalDiscCoordinate r₀) (criticalDiscReflection r₀)
        (q : Nat.Primes)) = 0 := by
    exact criticalDisc_connectionReader_eq_zero_of_primeEulerTangent_annihilation
      S (B.flip (compactPrimeEulerUnitFETangent
        (criticalDiscCoordinate r₀) (criticalDiscReflection r₀)
        (q : Nat.Primes))) (fun p => hB p q)
      f hr₀ hr01 hr1 hf hodd_f hschwarz_f
  exact criticalDisc_connectionReader_eq_zero_of_primeEulerTangent_annihilation
    S (B tf) hfirst g hr₀ hr01 hr1 hg hodd_g hschwarz_g

/-- Compactness form of the polarized generator test.  A continuous real-bilinear operator
reader whose values on all retained prime-tangent pairs are compact has compact value on every
pair of analytic FE-odd Schwarz-real germs. -/
theorem criticalDisc_polarizedConnection_isCompact_of_primeEulerTangent_pairs
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {r₀ r₁ : ℝ} (S : Finset Nat.Primes)
    (B : C(CriticalClosedDisc r₀, ℂ) →L[ℝ]
      C(CriticalClosedDisc r₀, ℂ) →L[ℝ] (H →L[ℂ] H))
    (hB : ∀ p q : {p : Nat.Primes // p ∉ S},
      IsCompactOperator
        (B (compactPrimeEulerUnitFETangent
            (criticalDiscCoordinate r₀) (criticalDiscReflection r₀)
            (p : Nat.Primes))
          (compactPrimeEulerUnitFETangent
            (criticalDiscCoordinate r₀) (criticalDiscReflection r₀)
            (q : Nat.Primes))))
    (f g : ℂ → ℂ)
    (hr₀ : 0 ≤ r₀) (hr01 : r₀ < r₁) (hr1 : r₁ < 1 / 2)
    (hf : DiffContOnCl ℂ f (ball (1 / 2 : ℂ) r₁))
    (hodd_f : ∀ z ∈ closedBall (1 / 2 : ℂ) r₀, f (1 - z) = -f z)
    (hschwarz_f : ∀ z : ℂ, f (conj z) = conj (f z))
    (hg : DiffContOnCl ℂ g (ball (1 / 2 : ℂ) r₁))
    (hodd_g : ∀ z ∈ closedBall (1 / 2 : ℂ) r₀, g (1 - z) = -g z)
    (hschwarz_g : ∀ z : ℂ, g (conj z) = conj (g z)) :
    IsCompactOperator
      (B (criticalDiscRestriction f r₀
          (hf.continuousOn_ball.mono (Metric.closedBall_subset_closedBall hr01.le)))
        (criticalDiscRestriction g r₀
          (hg.continuousOn_ball.mono (Metric.closedBall_subset_closedBall hr01.le)))) := by
  let tf : C(CriticalClosedDisc r₀, ℂ) :=
    criticalDiscRestriction f r₀
      (hf.continuousOn_ball.mono (Metric.closedBall_subset_closedBall hr01.le))
  have hfirst (q : {p : Nat.Primes // p ∉ S}) :
      IsCompactOperator
        (B tf (compactPrimeEulerUnitFETangent
          (criticalDiscCoordinate r₀) (criticalDiscReflection r₀)
          (q : Nat.Primes))) := by
    exact criticalDisc_connectionReader_isCompact_of_primeEulerTangent_compactness
      S (B.flip (compactPrimeEulerUnitFETangent
        (criticalDiscCoordinate r₀) (criticalDiscReflection r₀)
        (q : Nat.Primes))) (fun p => hB p q)
      f hr₀ hr01 hr1 hf hodd_f hschwarz_f
  exact criticalDisc_connectionReader_isCompact_of_primeEulerTangent_compactness
    S (B tf) hfirst g hr₀ hr01 hr1 hg hodd_g hschwarz_g

end

end RHTower
