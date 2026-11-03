import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheSecondOrderTermOfEveryPeriodicTwist

/-!
# The second-order term is the Dirichlet series of the spectrum

The second-order term of a window twisted by a mean-zero `M`-periodic weight `χ` is
`(βA_φ/(K∫φ²))` times the spectral sum `Σ_{0<k<M} |χ̂(k)|² (ζ(s, k/M) + ζ(s, 1 − k/M))`, `s = β + 1`
(`periodicTwist_layer_criticalCurve_of_regularTail`). The Hurwitz sums are sums over the residue
classes `k + Mℤ`, and the power `|χ̂(j)|²` is `M`-periodic and reflection symmetric, so the spectral
sum is a Dirichlet series:

* **The counting reading** (`twistSpectralSum_eq_dirichlet`):

  `Σ_{0<k<M} |χ̂(k)|² (ζ(s, k/M) + ζ(s, 1 − k/M)) = 2 M^s Σ_{j≥1} |χ̂(j)|² j^{−s}`,

  the integers counted with weight their spectral power. For a Ramanujan sum `c_m` the power is
  the indicator of `(j, m) = 1`, and the series is `2m^s Σ_{(j,m)=1} j^{−s} = 2ζ(s) J_s(m)`
  (ADT `zetaSum_mul_jordanTotient_eq`): the count of `ℙ^{s−1}(ℤ/m)`.
* **The second-order term in counting form** (`periodicTwist_layer_criticalCurve_dirichlet`).
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ h : ℝ → ℝ} {A : ℝ}

/-- The Fourier coefficients of a twist are `M`-periodic. -/
theorem twistCoeff_add_mul (χ : ℕ → ℝ) {M : ℕ} (hM : 0 < M) (r q : ℕ) :
    twistCoeff χ M (r + M * q) = twistCoeff χ M r := by
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold twistCoeff
  refine sum_congr rfl fun n _ => ?_
  have e : 2 * (Real.pi : ℂ) * Complex.I * (((r + M * q : ℕ) : ℂ) * n / M) =
      2 * Real.pi * Complex.I * ((r : ℂ) * n / M) + ((q * n : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; field_simp
  rw [e, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem twistPower_mod (χ : ℕ → ℝ) {M : ℕ} (hM : 0 < M) (j : ℕ) :
    twistPower χ M j = twistPower χ M (j % M) := by
  unfold twistPower
  conv_lhs => rw [← Nat.mod_add_div j M, twistCoeff_add_mul χ hM]

/-- **Reflection**: for a real twist `S_{M−k} = conj S_k`, so `|χ̂(M − k)| = |χ̂(k)|`. -/
theorem twistPower_reflect (χ : ℕ → ℝ) {M k : ℕ} (hM : 0 < M) (hkM : k ≤ M) :
    twistPower χ M (M - k) = twistPower χ M k := by
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hc : twistCoeff χ M (M - k) = conj (twistCoeff χ M k) := by
    unfold twistCoeff
    rw [map_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    have e : 2 * (Real.pi : ℂ) * Complex.I * (((M - k : ℕ) : ℂ) * n / M) =
        (starRingEnd ℂ) (2 * Real.pi * Complex.I * ((k : ℂ) * n / M)) +
          (n : ℂ) * (2 * Real.pi * Complex.I) := by
      simp only [map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
      push_cast [Nat.cast_sub hkM]
      field_simp
      ring
    rw [e, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  unfold twistPower
  rw [hc, Complex.norm_conj]

/-- A Hurwitz sum at a rational shift is a sum over a residue class:
`ζ(s, r/M) = M^s Σ_{n ≥ 0} (r + Mn)^{−s}`. -/
theorem hurwitzSum_div_eq (s : ℝ) {M : ℕ} (hM : 0 < M) (r : ℕ) :
    hurwitzSum s ((r : ℝ) / M) = (M : ℝ) ^ s * ∑' n : ℕ, (((r + M * n : ℕ) : ℝ)) ^ (-s) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  unfold hurwitzSum
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have e : (n : ℝ) + r / M = ((r + M * n : ℕ) : ℝ) / M := by
    push_cast; field_simp; ring
  rw [e, Real.div_rpow (Nat.cast_nonneg _) hM0.le, Real.rpow_neg hM0.le, div_inv_eq_mul, mul_comm]

/-- **The counting reading of the second-order term**: the spectral sum of a twist is the
Dirichlet series of its power spectrum,
`Σ_{0<k<M} |χ̂(k)|² (ζ(s, k/M) + ζ(s, 1 − k/M)) = 2 M^s Σ_j |χ̂(j)|² j^{−s}`. -/
theorem twistSpectralSum_eq_dirichlet {s : ℝ} (hs : 1 < s) {χ : ℕ → ℝ} {M : ℕ}
    (hχ : MeanZeroTwist χ M) :
    twistSpectralSum s χ M = 2 * (M : ℝ) ^ s * ∑' j : ℕ, twistPower χ M j * (j : ℝ) ^ (-s) := by
  have hM := hχ.pos
  haveI : NeZero M := ⟨hM.ne'⟩
  set g : ℕ → ℝ := fun j => (j : ℝ) ^ (-s) with hg
  have hgs : Summable g := Real.summable_nat_rpow.mpr (by linarith)
  set B := ∑ r ∈ range M, twistPower χ M r with hB
  have hPb : ∀ j, twistPower χ M j ≤ B := fun j => by
    rw [twistPower_mod χ hM j]
    exact single_le_sum (fun r _ => twistPower_nonneg χ M r) (mem_range.mpr (Nat.mod_lt _ hM))
  have hF : Summable fun j => twistPower χ M j * g j :=
    (hgs.mul_left B).of_nonneg_of_le
      (fun j => mul_nonneg (twistPower_nonneg _ _ _) (by positivity))
      (fun j => mul_le_mul_of_nonneg_right (hPb j) (by positivity))
  have hP0 : twistPower χ M 0 = 0 := by
    unfold twistPower; rw [twistCoeff_zero hχ, norm_zero]; simp
  -- the residue classes
  have hres : ∑' j, twistPower χ M j * g j =
      ∑ r ∈ Ico 1 M, twistPower χ M r * ∑' n : ℕ, g (r + M * n) := by
    rw [Nat.sumByResidueClasses hF M, sum_zmod_eq_sum_range M]
    have hterm : ∀ r ∈ range M, ∑' n, twistPower χ M ((r : ZMod M).val + M * n) *
        g ((r : ZMod M).val + M * n) = twistPower χ M r * ∑' n : ℕ, g (r + M * n) := by
      intro r hr
      have hrM := mem_range.mp hr
      rw [ZMod.val_natCast_of_lt hrM, ← tsum_mul_left]
      refine tsum_congr fun n => ?_
      rw [twistPower_mod χ hM (r + M * n), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrM]
    rw [sum_congr rfl hterm, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hM, hP0, zero_mul,
      zero_add]
  -- the Hurwitz sums
  have hhur : ∀ k ∈ Ico 1 M, hurwitzSum s ((k : ℝ) / M) + hurwitzSum s (1 - (k : ℝ) / M) =
      (M : ℝ) ^ s * (∑' n : ℕ, g (k + M * n) + ∑' n : ℕ, g ((M - k) + M * n)) := by
    intro k hk
    have hkM : k ≤ M := (mem_Ico.mp hk).2.le
    have e : 1 - (k : ℝ) / M = ((M - k : ℕ) : ℝ) / M := by
      have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      push_cast [Nat.cast_sub hkM]; field_simp
    rw [e, hurwitzSum_div_eq s hM, hurwitzSum_div_eq s hM, mul_add]
  have hrefl : ∑ k ∈ Ico 1 M, twistPower χ M k * ∑' n : ℕ, g ((M - k) + M * n) =
      ∑ k ∈ Ico 1 M, twistPower χ M k * ∑' n : ℕ, g (k + M * n) := by
    refine Finset.sum_nbij' (fun k => M - k) (fun k => M - k) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [mem_Ico] at ha ⊢; omega
    · intro a ha; simp only [mem_Ico] at ha ⊢; omega
    · intro a ha; simp only [mem_Ico] at ha; omega
    · intro a ha; simp only [mem_Ico] at ha; omega
    · intro a ha
      have haM : a ≤ M := (mem_Ico.mp ha).2.le
      rw [twistPower_reflect χ hM haM]
  unfold twistSpectralSum
  rw [hres, sum_congr rfl fun k hk => by rw [hhur k hk]]
  have e2 : ∀ k ∈ Ico 1 M, twistPower χ M k * ((M : ℝ) ^ s * (∑' n : ℕ, g (k + M * n) +
      ∑' n : ℕ, g ((M - k) + M * n))) = (M : ℝ) ^ s * (twistPower χ M k * ∑' n : ℕ, g (k + M * n)) +
        (M : ℝ) ^ s * (twistPower χ M k * ∑' n : ℕ, g ((M - k) + M * n)) := fun k _ => by ring
  rw [sum_congr rfl e2, sum_add_distrib, ← mul_sum, ← mul_sum, hrefl]
  ring

/-- **The second-order term in counting form.** For every profile with a regular spectral tail
`x^β T(x) → A_φ` and every mean-zero `M`-periodic twist: along `c^{β+1}/log N → K`,
`c⁻¹⟨W x, x⟩/∫g² → (2βA_φ M^{β+1}/(K∫φ²)) Σ_{j≥1} |χ̂(j)|² j^{−(β+1)} ‖H‖²_{−(β+1)}`. -/
theorem periodicTwist_layer_criticalCurve_dirichlet (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β Aφ : ℝ} (hβ : 0 < β)
    (hT : Tendsto (fun x => x ^ β * ArithmeticDegenerationTheory.spectralTail φ x) atTop (𝓝 Aφ))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    {χ : ℕ → ℝ} {M : ℕ} (hχ : MeanZeroTwist χ M) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h χ N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop
      (𝓝 (β * Aφ / (K * ∫ u, φ u ^ 2) *
        (2 * (M : ℝ) ^ (β + 1) * ∑' j : ℕ, twistPower χ M j * (j : ℝ) ^ (-(β + 1))) *
        ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2)) := by
  rw [← twistSpectralSum_eq_dirichlet (by linarith) hχ]
  exact periodicTwist_layer_criticalCurve_of_regularTail hφ hφsupp hφ2 hq hCφ hdecay hβ hT hh hA
    hsupp hc1 hK hcrit hχ

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
