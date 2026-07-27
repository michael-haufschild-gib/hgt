import GaloisForLFunctions.RHTower.FrequencySectorBlaschkeCompleteness
import GaloisForLFunctions.RHTower.CompactCarrierFECompleteness

/-!
# Compact-carrier completeness for abstract Lambert frequencies

For every strongly sector-Blaschke-complete real frequency family, the
corresponding derivative-Lambert kernels have dense polynomial span on every
compact carrier contained in a positive real strip.  Functional-equation
pairing then gives dense span in the anti-invariant sector.

The theorem is independent of primes and Euler products.  Prime logarithms
enter only as a later arithmetic example of the frequency hypothesis.
-/

noncomputable section

namespace RHTower

open Complex Metric Set

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Derivative-Lambert tangent at an arbitrary positive real frequency. -/
def compactFrequencyLambertTangent
    (s : C(K, ℂ)) (lambda : ℝ) : C(K, ℂ) :=
  (lambda : ℂ) • compactLambertKernel s lambda

/-- Functional-equation-paired derivative-Lambert tangent. -/
def compactFrequencyLambertFETangent
    (s : C(K, ℂ)) (tau : C(K, K)) (lambda : ℝ) : C(K, ℂ) :=
  compactFrequencyLambertTangent s lambda -
    (compactFrequencyLambertTangent s lambda).comp tau

@[simp]
theorem compactFrequencyLambertFETangent_apply
    (s : C(K, ℂ)) (tau : C(K, K)) (lambda : ℝ) (k : K) :
    compactFrequencyLambertFETangent s tau lambda k =
      compactFrequencyLambertTangent s lambda k -
        compactFrequencyLambertTangent s lambda (tau k) := rfl

/-- Annihilating a nonzero-frequency tangent kills the corresponding value
of the compact-carrier Lambert transform. -/
theorem compactCarrierLambertTransform_frequency_eq_zero_of_annihilates
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ))
    {lambda : ℝ} (hlambda : lambda ≠ 0)
    (hann : L (compactFrequencyLambertTangent s lambda) = 0) :
    compactCarrierLambertTransform L s lambda = 0 := by
  unfold compactCarrierLambertTransform
  have hscaled :
      (lambda : ℂ) * L (compactLambertKernel s lambda) = 0 := by
    simpa [compactFrequencyLambertTangent] using hann
  exact (mul_eq_zero.mp hscaled).resolve_left
    (by exact_mod_cast hlambda)

/-- Once the Lambert transform vanishes on a positive ray, compact-carrier
Lambert--Möbius inversion makes the Fourier--Borel transform vanish
identically. -/
theorem compactFourierBorel_eq_zero_of_Lambert_zero_on_ray
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ))
    {n : ℕ} {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (hsector : UniformSectorCarrierPositive s n R₀)
    (hHray : ∀ x : ℝ, R₀ + 1 ≤ x →
      compactCarrierLambertTransform L s x = 0) :
    ∀ z : ℂ, compactFourierBorel L s z = 0 := by
  apply entire_eq_zero_of_lambert_ray_zero
    (compactFourierBorel L s) (R₀ + 1)
    (compactFourierBorel_analyticOnNhd L s)
  intro x hx
  let R : ℝ := x - 1
  have hRR₀ : R₀ ≤ R := by
    dsimp [R]
    linarith
  obtain ⟨d, hd, hpos⟩ := hsector R hRR₀
  have hbase : ∀ k : K, d ≤ ((x : ℂ) * s k).re := by
    intro k
    have hk := hpos 0 (by simp) k
    simpa [R] using hk
  let r : ℝ := Real.exp (-d)
  have hr0 : 0 ≤ r := Real.exp_nonneg _
  have hr1 : r < 1 := by
    simpa [r] using
      (Real.exp_lt_one_iff.mpr (show -d < 0 by linarith))
  have hdecay : ∀ m : ℕ+,
      ‖compactFourierBorel L s ((m : ℂ) * x)‖ ≤
        ‖L‖ * r ^ (m : ℕ) := by
    intro m
    have hmpos : (0 : ℝ) < (m : ℕ) := by
      exact_mod_cast m.prop
    have hmre : ∀ k : K,
        (m : ℝ) * d ≤ (((m : ℂ) * (x : ℂ)) * s k).re := by
      intro k
      have hk := hbase k
      have hmxcast : (m : ℂ) * (x : ℂ) =
          (((m : ℝ) * x : ℝ) : ℂ) := by
        norm_cast
      calc
        (m : ℝ) * d ≤ (m : ℝ) * (((x : ℂ) * s k).re) :=
          mul_le_mul_of_nonneg_left hk hmpos.le
        _ = (((m : ℂ) * (x : ℂ)) * s k).re := by
          rw [hmxcast]
          simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
          ring
    have htest := norm_compactExponentialTest_le_exp_neg_of_re s
      ((m : ℂ) * (x : ℂ)) ((m : ℝ) * d) hmre
    have hL := L.le_opNorm
      (compactExponentialTest s ((m : ℂ) * (x : ℂ)))
    calc
      ‖compactFourierBorel L s ((m : ℂ) * x)‖
          ≤ ‖L‖ *
              ‖compactExponentialTest s ((m : ℂ) * (x : ℂ))‖ := by
            simpa [compactFourierBorel] using hL
      _ ≤ ‖L‖ * Real.exp (-((m : ℝ) * d)) := by
            gcongr
      _ = ‖L‖ * r ^ (m : ℕ) := by
        congr 1
        rw [show -((m : ℝ) * d) = (m : ℕ) * (-d) by ring,
          Real.exp_nat_mul]
  have hzero : ∀ m : ℕ+,
      positiveLambertDerivative (compactFourierBorel L s)
        ((m : ℂ) * (x : ℂ)) = 0 := by
    intro m
    have hmone : (1 : ℝ) ≤ (m : ℕ) := by
      exact_mod_cast m.prop
    have hxpos : 0 < x := by
      linarith
    have hmx : R₀ + 1 ≤ (m : ℝ) * x := by
      nlinarith
    have htransform : compactCarrierLambertTransform L s
        ((m : ℂ) * (x : ℂ)) = 0 := by
      simpa using hHray ((m : ℝ) * x) hmx
    have hmre : ∀ k : K,
        (m : ℝ) * d ≤ (((m : ℂ) * (x : ℂ)) * s k).re := by
      intro k
      have hk := hbase k
      have hmxcast : (m : ℂ) * (x : ℂ) =
          (((m : ℝ) * x : ℝ) : ℂ) := by
        norm_cast
      calc
        (m : ℝ) * d ≤ (m : ℝ) * (((x : ℂ) * s k).re) :=
          mul_le_mul_of_nonneg_left hk
            (by exact_mod_cast m.prop.le)
        _ = (((m : ℂ) * (x : ℂ)) * s k).re := by
          rw [hmxcast]
          simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
          ring
    have hq : ‖compactExponentialTest s
        ((m : ℂ) * (x : ℂ))‖ < 1 :=
      norm_compactExponentialTest_lt_one_of_re_pos
        s _ ((m : ℝ) * d)
        (mul_pos (by exact_mod_cast m.prop) hd) hmre
    rw [positiveLambertDerivative_compactFourierBorel L s _ hq]
    exact htransform
  exact ⟨‖L‖, r, norm_nonneg L, hr0, hr1, hdecay, hzero⟩

/-- Strong sector-Blaschke completeness plus annihilation of every abstract
frequency tangent forces the compact Fourier--Borel transform to vanish. -/
theorem compactFourierBorel_eq_zero_of_frequencyTangent_annihilation
    {ι : Type*} (lambda : ι → ℝ)
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ))
    {n : ℕ} (hn : n ≠ 0) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (hcomplete : SectorBlaschkeComplete lambda n R₀)
    (hsector : UniformSectorCarrierPositive s n R₀)
    (hann : ∀ i : ι,
      L (compactFrequencyLambertTangent s (lambda i)) = 0) :
    ∀ z : ℂ, compactFourierBorel L s z = 0 := by
  have hHray : ∀ x : ℝ, R₀ + 1 ≤ x →
      compactCarrierLambertTransform L s x = 0 := by
    apply frequency_zero_uniqueness_on_ray hn R₀ hcomplete
    · exact compactCarrierLambert_sector_analytic L s hsector
    · exact compactCarrierLambert_sector_bounded L s hsector
    · intro i hi
      apply compactCarrierLambertTransform_frequency_eq_zero_of_annihilates
        L s
      · linarith
      · exact hann i
  exact compactFourierBorel_eq_zero_of_Lambert_zero_on_ray
    L s hR₀ hsector hHray

/-- Carrier-independent frequency completeness on a positive real
rectangle. -/
theorem compactFourierBorel_eq_zero_of_strongFrequencyTangent_annihilation
    {ι : Type*} (lambda : ι → ℝ)
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ))
    (delta M R₀ : ℝ) (hdelta : 0 < delta) (hR₀ : 0 < R₀)
    (hre : ∀ k : K, delta ≤ (s k).re)
    (him : ∀ k : K, |(s k).im| ≤ M)
    (hcomplete : StrongSectorBlaschkeComplete lambda R₀)
    (hann : ∀ i : ι,
      L (compactFrequencyLambertTangent s (lambda i)) = 0) :
    ∀ z : ℂ, compactFourierBorel L s z = 0 := by
  obtain ⟨n, hn, hsector⟩ :=
    exists_uniformSectorCarrierPositive
      s delta M R₀ hdelta hR₀ hre him
  exact compactFourierBorel_eq_zero_of_frequencyTangent_annihilation
    lambda L s hn hR₀.le (hcomplete n hn) hsector hann

/-- Every coordinate monomial belongs to the closed span of a strongly
Blaschke-complete derivative-Lambert family. -/
theorem coordinate_pow_mem_closedSpan_frequencyLambertTangents
    {ι : Type*} (lambda : ι → ℝ)
    (s : C(K, ℂ)) (delta M R₀ : ℝ)
    (hdelta : 0 < delta) (hR₀ : 0 < R₀)
    (hre : ∀ k : K, delta ≤ (s k).re)
    (him : ∀ k : K, |(s k).im| ≤ M)
    (hcomplete : StrongSectorBlaschkeComplete lambda R₀)
    (N : ℕ) :
    s ^ N ∈
      (Submodule.span ℂ
        (Set.range fun i : ι ↦
          compactFrequencyLambertTangent s (lambda i))).topologicalClosure := by
  let v : ι → C(K, ℂ) :=
    fun i ↦ compactFrequencyLambertTangent s (lambda i)
  apply mem_topologicalClosure_span_of_forall_dual v (s ^ N)
  intro L hLv
  have hF :=
    compactFourierBorel_eq_zero_of_strongFrequencyTangent_annihilation
      lambda L s delta M R₀ hdelta hR₀ hre him hcomplete hLv
  exact map_coordinate_pow_eq_zero_of_fourierBorel_zero L s hF N

/-- Every anti-invariant coordinate monomial belongs to the closed span of
the paired abstract frequency tangents. -/
theorem odd_coordinate_pow_mem_closedSpan_frequencyLambertFETangents
    {ι : Type*} (lambda : ι → ℝ)
    (s : C(K, ℂ)) (tau : C(K, K))
    (delta M R₀ : ℝ)
    (hdelta : 0 < delta) (hR₀ : 0 < R₀)
    (hre : ∀ k : K, delta ≤ (s k).re)
    (him : ∀ k : K, |(s k).im| ≤ M)
    (hcomplete : StrongSectorBlaschkeComplete lambda R₀)
    (N : ℕ) :
    s ^ N - (s ^ N).comp tau ∈
      (Submodule.span ℂ
        (Set.range fun i : ι ↦
          compactFrequencyLambertFETangent
            s tau (lambda i))).topologicalClosure := by
  let v : ι → C(K, ℂ) :=
    fun i ↦ compactFrequencyLambertFETangent s tau (lambda i)
  apply mem_topologicalClosure_span_of_forall_dual v
    (s ^ N - (s ^ N).comp tau)
  intro L hLv
  let P : C(K, ℂ) →L[ℂ] C(K, ℂ) :=
    ContinuousLinearMap.id ℂ C(K, ℂ) -
      ContinuousMap.compCLM ℂ ℂ tau
  let Lodd : C(K, ℂ) →L[ℂ] ℂ := L.comp P
  have hann : ∀ i : ι,
      Lodd (compactFrequencyLambertTangent s (lambda i)) = 0 := by
    intro i
    have hv := hLv i
    simpa [v, Lodd, P, compactFrequencyLambertFETangent] using hv
  have hF :=
    compactFourierBorel_eq_zero_of_strongFrequencyTangent_annihilation
      lambda Lodd s delta M R₀ hdelta hR₀ hre him hcomplete hann
  have hmono :=
    map_coordinate_pow_eq_zero_of_fourierBorel_zero Lodd s hF N
  simpa [Lodd, P] using hmono

/-- Literal reflection form of abstract frequency completeness. -/
theorem fe_odd_coordinate_pow_mem_closedSpan_frequencyLambert
    {ι : Type*} (lambda : ι → ℝ)
    (s : C(K, ℂ)) (tau : C(K, K))
    (hreflect : ∀ k : K, s (tau k) = 1 - s k)
    (delta M R₀ : ℝ)
    (hdelta : 0 < delta) (hR₀ : 0 < R₀)
    (hre : ∀ k : K, delta ≤ (s k).re)
    (him : ∀ k : K, |(s k).im| ≤ M)
    (hcomplete : StrongSectorBlaschkeComplete lambda R₀)
    (N : ℕ) :
    s ^ N - (1 - s) ^ N ∈
      (Submodule.span ℂ
        (Set.range fun i : ι ↦
          compactFrequencyLambertFETangent
            s tau (lambda i))).topologicalClosure := by
  have h :=
    odd_coordinate_pow_mem_closedSpan_frequencyLambertFETangents
      lambda s tau delta M R₀ hdelta hR₀ hre him hcomplete N
  convert h using 1
  ext k
  simp [hreflect]

/-- Every oddified scalar polynomial belongs to the paired abstract
frequency-tangent closed span. -/
theorem fe_odd_polynomial_mem_closedSpan_frequencyLambert
    {ι : Type*} (lambda : ι → ℝ)
    (s : C(K, ℂ)) (tau : C(K, K))
    (hreflect : ∀ k : K, s (tau k) = 1 - s k)
    (delta M R₀ : ℝ)
    (hdelta : 0 < delta) (hR₀ : 0 < R₀)
    (hre : ∀ k : K, delta ≤ (s k).re)
    (him : ∀ k : K, |(s k).im| ≤ M)
    (hcomplete : StrongSectorBlaschkeComplete lambda R₀)
    (P : Polynomial ℂ) :
    compactPolynomialEval s P - compactPolynomialEval (1 - s) P ∈
      (Submodule.span ℂ
        (Set.range fun i : ι ↦
          compactFrequencyLambertFETangent
            s tau (lambda i))).topologicalClosure := by
  rw [compactPolynomialEval, compactPolynomialEval,
    ← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro n hn
  rw [← smul_sub]
  exact Submodule.smul_mem _ _
    (fe_odd_coordinate_pow_mem_closedSpan_frequencyLambert
      lambda s tau hreflect delta M R₀ hdelta hR₀
      hre him hcomplete n)

end RHTower
