import GaloisForLFunctions.RHTower.CompactCarrierWedgeGeometry
import GaloisForLFunctions.RHTower.DenseSpanDuality

/-!
# Polynomial detection from compact Fourier--Borel vanishing

If a compact Fourier--Borel transform vanishes identically, its functional
annihilates every polynomial in the carrier coordinate.  The proof is
constructive: first-order exponential difference quotients converge uniformly
to `-s`; their powers are finite linear combinations of exponentials, so no
higher Banach derivative formula is required.
-/

noncomputable section

namespace RHTower

open Complex Set Filter Topology

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Difference quotient of the compact exponential test at zero. -/
def compactExponentialSlope (s : C(K, ℂ)) (t : ℂ) : C(K, ℂ) :=
  t⁻¹ • (compactExponentialTest s t - compactExponentialTest s 0)

/-- The exponential difference quotient converges in the carrier sup norm to
the negative coordinate. -/
theorem compactExponentialSlope_tendsto (s : C(K, ℂ)) :
    Tendsto (compactExponentialSlope s) (nhdsWithin 0 ({0} : Set ℂ)ᶜ)
      (nhds (-s)) := by
  simpa [compactExponentialSlope] using
    (compactExponentialTest_hasDerivAt_zero s).tendsto_slope_zero

/-- If a functional kills every compact exponential, it kills every power of
the exponential difference quotient away from zero. -/
theorem map_compactExponentialSlope_pow_eq_zero
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ))
    (hkill : ∀ z : ℂ, L (compactExponentialTest s z) = 0)
    (N : ℕ) {t : ℂ} (ht : t ≠ 0) :
    L ((compactExponentialSlope s t) ^ N) = 0 := by
  let q : C(K, ℂ) := compactExponentialTest s t
  have hq0 : compactExponentialTest s 0 = 1 := by
    ext k
    simp
  have hqpow : ∀ m : ℕ, L (q ^ m) = 0 := by
    intro m
    rw [compactExponentialTest_pow]
    exact hkill ((m : ℂ) * t)
  have hsubpow : L ((q - 1) ^ N) = 0 := by
    rw [sub_pow, map_sum]
    apply Finset.sum_eq_zero
    intro m hm
    let c : ℂ := ((-1 : ℂ) ^ (m + N)) * (N.choose m : ℂ)
    have hterm :
        ((-1 : C(K, ℂ)) ^ (m + N) * q ^ m *
            (1 : C(K, ℂ)) ^ (N - m) * (N.choose m : C(K, ℂ))) =
          c • q ^ m := by
      ext k
      simp [c, mul_assoc, mul_comm, mul_left_comm]
    rw [hterm, map_smul, hqpow, smul_zero]
  have hslope : compactExponentialSlope s t = t⁻¹ • (q - 1) := by
    simp [compactExponentialSlope, q, hq0]
  rw [hslope, smul_pow, map_smul, hsubpow, smul_zero]

/-- Fourier--Borel vanishing forces annihilation of every monomial in the
compact carrier coordinate. -/
theorem map_coordinate_pow_eq_zero_of_fourierBorel_zero
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ))
    (hF : ∀ z : ℂ, compactFourierBorel L s z = 0) (N : ℕ) :
    L (s ^ N) = 0 := by
  have hkill : ∀ z : ℂ, L (compactExponentialTest s z) = 0 := by
    intro z
    simpa [compactFourierBorel] using hF z
  have hslope := compactExponentialSlope_tendsto s
  have hpow : Tendsto (fun t => (compactExponentialSlope s t) ^ N)
      (nhdsWithin 0 ({0} : Set ℂ)ᶜ) (nhds ((-s) ^ N)) := hslope.pow N
  have hLlim : Tendsto (fun t => L ((compactExponentialSlope s t) ^ N))
      (nhdsWithin 0 ({0} : Set ℂ)ᶜ) (nhds (L ((-s) ^ N))) :=
    (L.continuous.tendsto ((-s) ^ N)).comp hpow
  have heq : (fun t => L ((compactExponentialSlope s t) ^ N)) =ᶠ[
      nhdsWithin 0 ({0} : Set ℂ)ᶜ] (fun _ => 0) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact map_compactExponentialSlope_pow_eq_zero L s hkill N (by simpa using ht)
  have hzeroLim : Tendsto (fun t => L ((compactExponentialSlope s t) ^ N))
      (nhdsWithin 0 ({0} : Set ℂ)ᶜ) (nhds 0) :=
    tendsto_const_nhds.congr' heq.symm
  have hneg : L ((-s) ^ N) = 0 := tendsto_nhds_unique hLlim hzeroLim
  have hpowneg : (-s) ^ N = ((-1 : ℂ) ^ N) • s ^ N := by
    ext k
    simp only [ContinuousMap.neg_apply, ContinuousMap.pow_apply, ContinuousMap.smul_apply]
    rw [neg_pow]
    simp
  rw [hpowneg, map_smul] at hneg
  have hc : (-1 : ℂ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
  change ((-1 : ℂ) ^ N) * L (s ^ N) = 0 at hneg
  exact (mul_eq_zero.mp hneg).resolve_left hc

/-- Under the right-rectangle carrier bounds, every coordinate monomial lies
in the closed span of the cofinite actual Euler-unit tangents. -/
theorem coordinate_pow_mem_closedSpan_primeEulerTangents
    (s : C(K, ℂ)) (δ M R₀ : ℝ)
    (hδ : 0 < δ) (hM : 0 ≤ M) (hR₀ : 0 < R₀)
    (hre : ∀ k : K, δ ≤ (s k).re)
    (him : ∀ k : K, |(s k).im| ≤ M)
    (N : ℕ) :
    s ^ N ∈ (Submodule.span ℂ
      (Set.range fun p : {p : Nat.Primes // R₀ + 1 < Real.log (p : ℝ)} =>
        compactPrimeEulerUnitTangent s (p : Nat.Primes))).topologicalClosure := by
  let v : {p : Nat.Primes // R₀ + 1 < Real.log (p : ℝ)} → C(K, ℂ) :=
    fun p => compactPrimeEulerUnitTangent s (p : Nat.Primes)
  apply mem_topologicalClosure_span_of_forall_dual v (s ^ N)
  intro L hLv
  have hann : ∀ p : Nat.Primes, R₀ + 1 < Real.log (p : ℝ) →
      L (compactPrimeEulerUnitTangent s (p : ℕ)) = 0 := by
    intro p hp
    exact hLv ⟨p, hp⟩
  have hF := compactFourierBorel_eq_zero_of_tangent_annihilation_rightRectangle
    L s δ M R₀ hδ hM hR₀ hre him hann
  exact map_coordinate_pow_eq_zero_of_fourierBorel_zero L s hF N

/-- Deleting an arbitrary finite prime set does not change polynomial
completeness on a right-half-plane compact carrier. -/
theorem coordinate_pow_mem_closedSpan_primeEulerTangents_compl_finset
    (s : C(K, ℂ)) (δ M : ℝ)
    (hδ : 0 < δ) (hM : 0 ≤ M)
    (hre : ∀ k : K, δ ≤ (s k).re)
    (him : ∀ k : K, |(s k).im| ≤ M)
    (S : Finset Nat.Primes) (N : ℕ) :
    s ^ N ∈ (Submodule.span ℂ
      (Set.range fun p : {p : Nat.Primes // p ∉ S} =>
        compactPrimeEulerUnitTangent s (p : Nat.Primes))).topologicalClosure := by
  let B : ℝ := ∑ p ∈ S, Real.log (p : ℝ)
  let R₀ : ℝ := 1 + B
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hR₀ : 0 < R₀ := by dsimp [R₀]; linarith
  have htail := coordinate_pow_mem_closedSpan_primeEulerTangents
    s δ M R₀ hδ hM hR₀ hre him N
  apply (Submodule.topologicalClosure_mono ?_) htail
  apply Submodule.span_mono
  rintro x ⟨p, rfl⟩
  have hpnot : (p : Nat.Primes) ∉ S := by
    intro hpS
    have hlognonneg : ∀ q ∈ S, 0 ≤ Real.log ((q : Nat.Primes) : ℝ) := by
      intro q hq
      apply Real.log_nonneg
      exact_mod_cast q.prop.one_lt.le
    have hle : Real.log ((p : Nat.Primes) : ℝ) ≤ B := by
      dsimp [B]
      exact Finset.single_le_sum hlognonneg hpS
    have hp := p.prop
    dsimp [R₀] at hp
    linarith
  exact ⟨⟨(p : Nat.Primes), hpnot⟩, rfl⟩

end RHTower
