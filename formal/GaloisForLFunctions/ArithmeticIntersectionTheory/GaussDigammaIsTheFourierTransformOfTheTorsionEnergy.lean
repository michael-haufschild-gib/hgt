import GaloisForLFunctions.ArithmeticIntersectionTheory.TheProjectionFormulaAndTheRegulatorAnomaly
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheArchimedeanGermSurvivesOnItsPolarHyperplane
import GaloisForLFunctions.RHTower.RingRecursionWitness

/-!
# Gauss's digamma theorem is the Fourier transform of the torsion energy

On the cycle `μ_N` of `N`-th roots of unity the rotations act, and the torsion energy
`k_r(1, ζ^a) = −log |1 − r ζ^a|` is diagonalized by the characters `a ↦ cos(2π a k/N)`. Its Fourier
coefficients are the **archimedean lattice germ** `G_s(z) = Σ_{m ≥ 0} s^m/(m + z)` of RBG at the
rational points `z = k/N`, `s = r^N` (`hasSum_torsionFourier`):

    Σ_{a < N} −log |1 − r ζ_N^a| cos(2πak/N) = ½ (r^k G_{r^N}(k/N) + r^{N−k} G_{r^N}((N−k)/N)).

Expanding `−log |1 − w| = Σ_j Re(w^j)/j`, the rotation characters select the frequencies `j ≡ ±k mod N`,
and the progression `j = mN + k` is the shifted lattice `k/N + ℕ` scaled by `N`.

At `r → 1` the germ is renormalized by `log(1/(1 − r^N))`, while the diagonal point `a = 0` carries
`log(1/(1 − r))`. Their difference is the regulator anomaly `log N` of `[N]`, and the limit is **Gauss's
digamma theorem** (`gauss_digamma_theorem`): for `0 < k < N`,

    Σ_{0 < a < N} log |1 − ζ_N^a| cos(2πak/N) = log N + γ + ½ (ψ(k/N) + ψ(1 − k/N)).

So the archimedean local factor of the explicit formula, through its digamma function at rational
points, and the torsion of the characteristic circle are Fourier dual; the `log N` of Gauss's formula
is the anomaly of the Hecke correspondence `[N]`.
-/

noncomputable section

open Finset Filter Topology Complex
open scoped Real

namespace GaloisForLFunctions.ArithmeticIntersectionTheory

open ArithmeticEffectivityTheory RenormalizedBiarithmeticGeometry

/-- The angle `θ_a = 2πa/N` of the root `ζ_N^a`. -/
def rootAngle (N a : ℕ) : ℝ := 2 * π * a / N

/-- The root of unity `ζ_N^a = e^{iθ_a}`. -/
def rootPoint (N a : ℕ) : ℂ := exp ((rootAngle N a : ℂ) * I)

/-- The `k`-th Fourier coefficient of the regularized torsion energy on `μ_N`. -/
def torsionFourier (r : ℝ) (N k : ℕ) : ℝ :=
  ∑ a ∈ range N, -Real.log ‖1 - (r : ℂ) * rootPoint N a‖ * Real.cos (k * rootAngle N a)

theorem norm_rootPoint (N a : ℕ) : ‖rootPoint N a‖ = 1 := by
  rw [rootPoint, Complex.norm_exp_ofReal_mul_I]

theorem re_rootPoint_pow (N a j : ℕ) : ((rootPoint N a) ^ j).re = Real.cos (j * rootAngle N a) := by
  rw [rootPoint, ← Complex.exp_nat_mul, ← mul_assoc, ← ofReal_natCast, ← ofReal_mul,
    exp_ofReal_mul_I_re]

/-- `Σ_{a < N} cos(m θ_a) = N [N ∣ m]`. -/
theorem sum_cos_rootAngle {N : ℕ} (hN : 0 < N) (m : ℕ) :
    ∑ a ∈ range N, Real.cos (m * rootAngle N a) = if N ∣ m then (N : ℝ) else 0 := by
  have h := congrArg Complex.re (RHTower.sum_rootsOfUnity_pow hN m)
  rw [re_sum] at h
  have hterm : ∀ a ∈ range N, (exp (((2 * π * m * a / N : ℝ) : ℂ) * I)).re =
      Real.cos (m * rootAngle N a) := by
    intro a _
    rw [exp_ofReal_mul_I_re, rootAngle]
    congr 1
    ring
  rw [sum_congr rfl hterm] at h
  rw [h]
  split_ifs <;> simp

/-- `2 cos(jθ) cos(kθ) = cos((j + k)θ) + cos((j + N − k)θ)` on `μ_N`. -/
theorem two_cos_mul_cos_rootAngle {N k : ℕ} (hk : k ≤ N) (a j : ℕ) :
    2 * (Real.cos (j * rootAngle N a) * Real.cos (k * rootAngle N a)) =
      Real.cos (((j + k : ℕ) : ℝ) * rootAngle N a) +
        Real.cos (((j + (N - k) : ℕ) : ℝ) * rootAngle N a) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [rootAngle]; ring
  have hshift : ((j + (N - k) : ℕ) : ℝ) * rootAngle N a =
      (j * rootAngle N a - k * rootAngle N a) + a * (2 * π) := by
    rw [rootAngle, Nat.cast_add, Nat.cast_sub hk]
    field_simp
    ring
  rw [hshift, Real.cos_add_nat_mul_two_pi, Nat.cast_add, add_mul, Real.cos_add, Real.cos_sub]
  ring

/-- The Fourier coefficient of a frequency `j`: `Σ_a cos(jθ_a) cos(kθ_a) = (N/2)([N ∣ j+k] + [N ∣ j+N−k])`. -/
theorem sum_cos_mul_cos_rootAngle {N k : ℕ} (hN : 0 < N) (hk : k ≤ N) (j : ℕ) :
    ∑ a ∈ range N, Real.cos (j * rootAngle N a) * Real.cos (k * rootAngle N a) =
      (N : ℝ) / 2 * ((if N ∣ j + k then 1 else 0) + (if N ∣ j + (N - k) then 1 else 0)) := by
  have h : ∀ a ∈ range N, Real.cos (j * rootAngle N a) * Real.cos (k * rootAngle N a) =
      (Real.cos (((j + k : ℕ) : ℝ) * rootAngle N a) +
        Real.cos (((j + (N - k) : ℕ) : ℝ) * rootAngle N a)) / 2 := by
    intro a _
    rw [← two_cos_mul_cos_rootAngle hk]
    ring
  rw [sum_congr rfl h, ← sum_div, sum_add_distrib, sum_cos_rootAngle hN, sum_cos_rootAngle hN]
  split_ifs <;> ring

/-- Frequencies in a residue class: `Σ_{j ≡ c (N)} r^j/j` over the progression `j = mN + c`. -/
theorem hasSum_progression {N c : ℕ} (hN : 0 < N) (hc : 0 < c) (hcN : c < N) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun j : ℕ => r ^ j / j * (if N ∣ j + (N - c) then 1 else 0))
      (r ^ c / N * latticeGerm (r ^ N) ((c : ℝ) / N)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set g : ℕ → ℕ := fun m => m * N + c
  have hg : Function.Injective g := fun m m' h => by
    simp only [g] at h
    exact Nat.eq_of_mul_eq_mul_right hN (by omega)
  have hsupp : ∀ j ∉ Set.range g, r ^ j / j * (if N ∣ j + (N - c) then 1 else 0) = 0 := by
    intro j hj
    rw [if_neg, mul_zero]
    rintro ⟨d, hd⟩
    apply hj
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · simp at hd; omega
      · omega⟩
    refine ⟨d', ?_⟩
    simp only [g]
    have : N * (d' + 1) = d' * N + N := by ring
    omega
  rw [← hg.hasSum_iff hsupp]
  have hterm : ∀ m : ℕ, (fun j : ℕ => r ^ j / j * (if N ∣ j + (N - c) then 1 else 0)) (g m) =
      r ^ c / N * ((r ^ N) ^ m / ((m : ℝ) + c / N)) := by
    intro m
    have hdvd : N ∣ m * N + c + (N - c) := ⟨m + 1, by
      have := Nat.sub_add_cancel hcN.le
      rw [add_assoc, Nat.add_sub_of_le hcN.le]; ring⟩
    simp only [g, if_pos hdvd, mul_one]
    push_cast
    rw [← pow_mul, pow_add, mul_comm N m]
    field_simp
  simp only [Function.comp_def, hterm]
  exact (hasSum_latticeGerm (pow_nonneg hr0 N) (pow_lt_one₀ hr0 hr1 hN.ne')
    (by positivity)).mul_left _

/-- **The Fourier coefficients of the torsion energy are lattice germs.** For `0 < k < N`,
`Σ_a −log|1 − r ζ_N^a| cos(2πak/N) = ½(r^k G_{r^N}(k/N) + r^{N−k} G_{r^N}((N−k)/N))`. -/
theorem torsionFourier_eq {N k : ℕ} (hk : 0 < k) (hkN : k < N) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) :
    torsionFourier r N k = (r ^ k * latticeGerm (r ^ N) ((k : ℝ) / N) +
      r ^ (N - k) * latticeGerm (r ^ N) (((N - k : ℕ) : ℝ) / N)) / 2 := by
  have hN : 0 < N := hk.trans hkN
  -- expand each logarithm into its Fourier series
  have hser : HasSum (fun j : ℕ => r ^ j / j *
      ∑ a ∈ range N, Real.cos (j * rootAngle N a) * Real.cos (k * rootAngle N a))
      (torsionFourier r N k) := by
    have h := hasSum_sum (s := range N) fun a _ =>
      (hasSum_neg_log_norm_one_sub hr0 hr1 (norm_rootPoint N a).le).mul_right
        (Real.cos (k * rootAngle N a))
    simp only [re_rootPoint_pow] at h
    have e : (fun j : ℕ => r ^ j / j *
        ∑ a ∈ range N, Real.cos (j * rootAngle N a) * Real.cos (k * rootAngle N a)) =
        fun j : ℕ => ∑ a ∈ range N,
          r ^ j / (j : ℝ) * Real.cos ((j : ℝ) * rootAngle N a) * Real.cos (k * rootAngle N a) := by
      funext j; rw [mul_sum]; exact sum_congr rfl fun a _ => by ring
    rw [e]
    exact h
  simp only [sum_cos_mul_cos_rootAngle hN hkN.le] at hser
  -- the two residue classes `j ≡ k` and `j ≡ −k`
  have h1 := hasSum_progression hN hk hkN hr0 hr1
  have h2 := hasSum_progression (c := N - k) hN (by omega) (by omega) hr0 hr1
  rw [Nat.sub_sub_self hkN.le] at h2
  have hsum := (h1.add h2).mul_left ((N : ℝ) / 2)
  have e : (fun j : ℕ => r ^ j / j * ((N : ℝ) / 2 *
      ((if N ∣ j + k then 1 else 0) + (if N ∣ j + (N - k) then 1 else 0)))) =
      fun j => (N : ℝ) / 2 * (r ^ j / j * (if N ∣ j + (N - k) then 1 else 0) +
        r ^ j / j * (if N ∣ j + k then 1 else 0)) := by
    funext j; ring
  rw [e] at hser
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [hser.unique hsum]
  field_simp

/-! ### The limit: Gauss's digamma theorem -/

theorem norm_one_sub_rootPoint_ne_zero {N a : ℕ} (ha : 0 < a) (haN : a < N) :
    ‖1 - rootPoint N a‖ ≠ 0 := by
  have hN : 0 < N := ha.trans haN
  rw [norm_ne_zero_iff, sub_ne_zero]
  intro h
  have hζ := Complex.isPrimitiveRoot_exp N hN.ne'
  have hpow : rootPoint N a = exp (2 * π * I / N) ^ a := by
    rw [rootPoint, ← Complex.exp_nat_mul, rootAngle]
    congr 1; push_cast; ring
  rw [hpow] at h
  exact absurd (Nat.le_of_dvd ha ((hζ.pow_eq_one_iff_dvd a).mp h.symm)) (not_le.mpr haN)

/-- `(1 − r^m) log(1 − r) → 0` as `r → 1⁻`. -/
theorem tendsto_one_sub_pow_mul_log (m : ℕ) :
    Tendsto (fun r : ℝ => (1 - r ^ m) * Real.log (1 - r)) (𝓝[<] 1) (𝓝 0) := by
  have hc : Continuous (fun r : ℝ => (1 - r) * Real.log (1 - r)) :=
    Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
  have hxlog : Tendsto (fun r : ℝ => (1 - r) * Real.log (1 - r)) (𝓝[<] 1) (𝓝 0) := by
    have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
    simpa using this
  have hgeom : Tendsto (fun r : ℝ => ∑ i ∈ range m, r ^ i) (𝓝[<] 1) (𝓝 (m : ℝ)) := by
    have := ((by fun_prop : Continuous fun r : ℝ => ∑ i ∈ range m, r ^ i).tendsto 1)
    simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h := hgeom.mul hxlog
  rw [mul_zero] at h
  refine h.congr fun r => ?_
  have := geom_sum_mul r m
  rw [show 1 - r ^ m = (∑ i ∈ range m, r ^ i) * (1 - r) by linarith]
  ring

/-- **Gauss's digamma theorem** as the renormalized Fourier transform of the torsion energy: for
`0 < k < N`, `Σ_{0 < a < N} log |1 − ζ_N^a| cos(2πak/N) = log N + γ + ½(ψ(k/N) + ψ((N − k)/N))`. -/
theorem gauss_digamma_theorem {N k : ℕ} (hk : 0 < k) (hkN : k < N) :
    ∑ a ∈ Ico 1 N, Real.log ‖1 - rootPoint N a‖ * Real.cos (k * rootAngle N a) =
      Real.log N + Real.eulerMascheroniConstant +
        ((Complex.digamma (Complex.ofReal ((k : ℝ) / N))).re +
          (Complex.digamma (Complex.ofReal (((N - k : ℕ) : ℝ) / N))).re) / 2 := by
  have hN : 0 < N := hk.trans hkN
  have hz1 : (0 : ℝ) < (k : ℝ) / N := by positivity
  have hz2 : (0 : ℝ) < ((N - k : ℕ) : ℝ) / N := by
    have : 0 < N - k := by omega
    positivity
  set F : ℝ → ℝ := fun r => ∑ a ∈ Ico 1 N,
    -Real.log ‖1 - (r : ℂ) * rootPoint N a‖ * Real.cos (k * rootAngle N a)
  -- the nondiagonal points are continuous at `r = 1`
  have hF : Tendsto F (𝓝[<] 1) (𝓝 (∑ a ∈ Ico 1 N,
      -Real.log ‖1 - rootPoint N a‖ * Real.cos (k * rootAngle N a))) := by
    refine (tendsto_finsetSum _ fun a ha => ?_).mono_left nhdsWithin_le_nhds
    obtain ⟨ha1, haN⟩ := mem_Ico.mp ha
    have hne : ‖1 - ((1 : ℝ) : ℂ) * rootPoint N a‖ ≠ 0 := by
      rw [ofReal_one, one_mul]; exact norm_one_sub_rootPoint_ne_zero ha1 haN
    have h1 : ContinuousAt (fun r : ℝ => ‖1 - (r : ℂ) * rootPoint N a‖) 1 := by fun_prop
    have hc : ContinuousAt (fun r : ℝ =>
        -Real.log ‖1 - (r : ℂ) * rootPoint N a‖ * Real.cos (k * rootAngle N a)) 1 :=
      (h1.log hne).neg.mul continuousAt_const
    simpa using hc.tendsto
  -- on `r < 1`, `F` is the Fourier coefficient minus the diagonal point
  have hFeq : ∀ r ∈ Set.Ioo (0 : ℝ) 1, F r =
      (r ^ k * (latticeGerm (r ^ N) ((k : ℝ) / N) + Real.log (1 - r ^ N)) +
        r ^ (N - k) * (latticeGerm (r ^ N) (((N - k : ℕ) : ℝ) / N) + Real.log (1 - r ^ N))) / 2
      - (r ^ k + r ^ (N - k)) / 2 * (Real.log (1 - r ^ N) - Real.log (1 - r))
      + (1 - (r ^ k + r ^ (N - k)) / 2) * Real.log (1 - r) := by
    intro r hr
    have hsplit : torsionFourier r N k = -Real.log (1 - r) + F r := by
      rw [torsionFourier, range_eq_Ico, sum_eq_sum_Ico_succ_bot hN]
      simp only [rootPoint, rootAngle, Nat.cast_zero, mul_zero, zero_div, ofReal_zero, zero_mul,
        Complex.exp_zero, mul_one, Real.cos_zero]
      rw [show ‖1 - (r : ℂ)‖ = 1 - r by
        rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_of_nonneg (by linarith [hr.2])]]
      rfl
    have := torsionFourier_eq hk hkN hr.1.le hr.2
    linarith
  have hlim1 := tendsto_latticeGerm_add_log hz1
  have hlim2 := tendsto_latticeGerm_add_log hz2
  have hpowN : Tendsto (fun r : ℝ => r ^ N) (𝓝[<] 1) (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_pow N : Continuous fun r : ℝ => r ^ N).tendsto 1).mono_left
        (nhdsWithin_le_nhds (s := Set.Iio 1))
      simpa using this
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
      exact pow_lt_one₀ hr.1.le hr.2 hN.ne'
  have hpk : ∀ m : ℕ, Tendsto (fun r : ℝ => r ^ m) (𝓝[<] 1) (𝓝 1) := fun m => by
    simpa using ((continuous_pow m : Continuous fun r : ℝ => r ^ m).tendsto 1).mono_left
      (nhdsWithin_le_nhds (s := Set.Iio 1))
  have hG := (((hpk k).mul (hlim1.comp hpowN)).add ((hpk (N - k)).mul (hlim2.comp hpowN))).div_const 2
  have hA := ((hpk k).add (hpk (N - k))).div_const 2 |>.mul (tendsto_log_one_sub_pow_sub_log_one_sub hN)
  have hB := (tendsto_one_sub_pow_mul_log k).add (tendsto_one_sub_pow_mul_log (N - k))
  have hlim := (hG.sub hA).add (hB.div_const 2)
  have hFlim : Tendsto F (𝓝[<] 1) (𝓝 ((1 * latticeGermLimit ((k : ℝ) / N) +
      1 * latticeGermLimit (((N - k : ℕ) : ℝ) / N)) / 2 - (1 + 1) / 2 * Real.log N + (0 + 0) / 2)) := by
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    rw [hFeq r hr]
    simp only [Function.comp_def]
    ring
  have huniq := tendsto_nhds_unique hF hFlim
  rw [latticeGermLimit_eq hz1, latticeGermLimit_eq hz2] at huniq
  have hneg : ∑ a ∈ Ico 1 N, Real.log ‖1 - rootPoint N a‖ * Real.cos (k * rootAngle N a) =
      -∑ a ∈ Ico 1 N, -Real.log ‖1 - rootPoint N a‖ * Real.cos (k * rootAngle N a) := by
    rw [← sum_neg_distrib]; refine sum_congr rfl fun a _ => ?_; ring
  rw [hneg, huniq]
  ring

end GaloisForLFunctions.ArithmeticIntersectionTheory
