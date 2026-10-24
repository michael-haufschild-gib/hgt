import GaloisForLFunctions.BezoutValuationIncidence.KernelMeanAtCompositeModuliAndTheAllRowsLaws
import GaloisForLFunctions.RHTower.EulerDeletionRemainderMobiusInversion
import GaloisForLFunctions.RHTower.SquarefreeCountingAsymptotic

/-!
# The Möbius row inverts the cross-scale kernel

Both kernels of the cross-scale dual norm are sums over multiples:
`𝔅(d, n)/n² = Σ_j Φ_d(jn)/(jn)²` and `𝔅₃(d, n)/n³ = Σ_j (2Ψ_d - Φ_d)(jn)/(jn)³`. Since `μ ⋆ 1 = δ`,
the full Möbius row collapses each of them to its value at `1`:

`Σ_n μ(n) 𝔅(d, n)/n² = Φ_d(1)`,  `Σ_n μ(n) 𝔅₃(d, n)/n³ = 2Ψ_d(1) - Φ_d(1)`,

so the kernel statistic of the untruncated Möbius row is explicit at every modulus,

`Σ_n μ(n) ℓ_d(n) = 2Ψ_d(1) - (6/π²) m_d = (d - 1)(d - 3)/4 - (6/π²) m_d`

(`hasSum_moebius_mul_kernelTerm`). The arithmetic in the statistics of Möbius windows lies entirely
in the window cutoffs: over a cover of `ℕ` by windows they add up to this explicit value.
-/

open Finset ArithmeticFunction RHTower
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- The term of the kernel statistic, `ℓ_d(n) = (𝔅(d, n) - m_d)/n² + 𝔅₃(d, n)/n³`. -/
def kernelTerm (d n : ℕ) : ℝ :=
  (bernoulliKernel d n - kernelMean d) / (n : ℝ) ^ 2 + cubicKernel d n / (n : ℝ) ^ 3

/-- `Λ_d(c') = Σ_{n ≤ N} c'(n) ℓ_d(n)`. -/
theorem kernelStatisticAll_eq_sum_kernelTerm (N : ℕ) (c' : ℕ → ℝ) (d : ℕ) :
    kernelStatisticAll N c' d = ∑ n ∈ Icc 1 N, c' n * kernelTerm d n := by
  unfold kernelStatisticAll kernelTerm
  exact sum_congr rfl fun n _ => by ring

/-- **Möbius inversion over multiples**, real form: for `Σ_{p,n} |g(pn)| < ∞`,
`Σ_p μ(p) Σ_n g(pn) = g(1)`, the row sums being summable. -/
theorem hasSum_moebius_mul_tsum_mul (g : ℕ → ℝ)
    (hg : Summable (fun x : ℕ+ × ℕ+ => |g ((x.1 : ℕ) * x.2)|)) :
    HasSum (fun p : ℕ+ => (μ (p : ℕ) : ℝ) * ∑' n : ℕ+, g ((p : ℕ) * n)) (g 1) := by
  have hw : Summable (fun x : ℕ+ × ℕ+ => (μ (x.1 : ℕ) : ℝ) * g ((x.1 : ℕ) * x.2)) := by
    refine Summable.of_norm_bounded hg fun x => ?_
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_of_le_one_left (abs_nonneg _) ?_
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hrows : Summable (fun p : ℕ+ => (μ (p : ℕ) : ℝ) * ∑' n : ℕ+, g ((p : ℕ) * n)) :=
    hw.prod.congr fun p => by simp only; exact tsum_mul_left
  have h := RHTower.DeletionMixedRefinement.moebius_multiples_inversion (fun N => (g N : ℂ))
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hg)
  have hcast : ((∑' p : ℕ+, (μ (p : ℕ) : ℝ) * ∑' n : ℕ+, g ((p : ℕ) * n) : ℝ) : ℂ) =
      ∑' p : ℕ+, (μ (p : ℕ) : ℂ) * ∑' n : ℕ+, (g ((p : ℕ) * n) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun p => ?_
    rw [Complex.ofReal_mul, Complex.ofReal_tsum]
    push_cast
    rfl
  have hval : ∑' p : ℕ+, (μ (p : ℕ) : ℝ) * ∑' n : ℕ+, g ((p : ℕ) * n) = g 1 := by
    exact_mod_cast hcast.trans h
  rw [← hval]
  exact hrows.hasSum

/-- Pair summability for a function bounded by `C/N²` on `N ≥ 1`. -/
theorem summable_abs_mul_pnat_of_le {g : ℕ → ℝ} {C : ℝ}
    (hg : ∀ N : ℕ, 1 ≤ N → |g N| ≤ C / (N : ℝ) ^ 2) :
    Summable (fun x : ℕ+ × ℕ+ => |g ((x.1 : ℕ) * x.2)|) := by
  have hs : Summable (fun p : ℕ+ => 1 / ((p : ℕ) : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective PNat.coe_injective
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun x => ?_)
    ((hs.mul_of_nonneg hs (fun _ => by positivity) (fun _ => by positivity)).mul_left C)
  have h1 : 1 ≤ (x.1 : ℕ) * x.2 :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero x.1.ne_zero x.2.ne_zero)
  refine (hg _ h1).trans (le_of_eq ?_)
  push_cast
  field_simp

/-- A sum over the multiples `pn`, `n ∈ ℕ+`, from a `HasSum` over `j : ℕ` at `(j + 1) p`. -/
theorem tsum_pnat_mul_eq {F : ℕ → ℝ} {p : ℕ+} {a : ℝ}
    (h : HasSum (fun j : ℕ => F ((j + 1) * p)) a) : ∑' n : ℕ+, F ((p : ℕ) * n) = a := by
  rw [tsum_pnat_eq_tsum_succ (f := fun n => F ((p : ℕ) * n))]
  have e : (fun j : ℕ => F ((p : ℕ) * (j + 1))) = fun j : ℕ => F ((j + 1) * p) :=
    funext fun j => by rw [mul_comm]
  rw [e]
  exact h.tsum_eq

/-- `Σ_n μ(n) 𝔅(d, n)/n² = Φ_d(1)`. -/
theorem hasSum_moebius_mul_bernoulliKernel {d : ℕ} (hd : 0 < d) :
    HasSum (fun p : ℕ+ => (μ (p : ℕ) : ℝ) * (bernoulliKernel d p / ((p : ℕ) : ℝ) ^ 2))
      (residuePotential d 1) := by
  set g : ℕ → ℝ := fun N => residuePotential d N / (N : ℝ) ^ 2
  have hrow : ∀ p : ℕ+, bernoulliKernel d p / ((p : ℕ) : ℝ) ^ 2 = ∑' n : ℕ+, g ((p : ℕ) * n) := by
    intro p
    refine (tsum_pnat_mul_eq ?_).symm
    have hp : ((p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast p.ne_zero
    have e : (fun j : ℕ => g ((j + 1) * p)) = fun j : ℕ =>
        residuePotential d ((j + 1) * p) / ((j : ℝ) + 1) ^ 2 / ((p : ℕ) : ℝ) ^ 2 :=
      funext fun j => by simp only [g]; push_cast; field_simp
    rw [e]
    exact (hasSum_bernoulliKernel hd p).div_const _
  have hg : ∀ N : ℕ, 1 ≤ N → |g N| ≤ (d : ℝ) ^ 2 / 8 / (N : ℝ) ^ 2 := fun N _ => by
    simp only [g]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) ^ 2)]
    exact div_le_div_of_nonneg_right (abs_residuePotential_le hd N) (by positivity)
  have h := hasSum_moebius_mul_tsum_mul g (summable_abs_mul_pnat_of_le hg)
  simp only [g, Nat.cast_one, one_pow, div_one] at h
  rw [funext fun p : ℕ+ => congrArg (fun x => (μ (p : ℕ) : ℝ) * x) (hrow p)]
  exact h

/-- `Σ_n μ(n) 𝔅₃(d, n)/n³ = 2Ψ_d(1) - Φ_d(1)`. -/
theorem hasSum_moebius_mul_cubicKernel {d : ℕ} (hd : 0 < d) :
    HasSum (fun p : ℕ+ => (μ (p : ℕ) : ℝ) * (cubicKernel d p / ((p : ℕ) : ℝ) ^ 3))
      (2 * cubicPotential d 1 - residuePotential d 1) := by
  set g : ℕ → ℝ := fun N => (2 * cubicPotential d N - residuePotential d N) / (N : ℝ) ^ 3
  have hrow : ∀ p : ℕ+, cubicKernel d p / ((p : ℕ) : ℝ) ^ 3 = ∑' n : ℕ+, g ((p : ℕ) * n) := by
    intro p
    refine (tsum_pnat_mul_eq ?_).symm
    have hp : ((p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast p.ne_zero
    have e : (fun j : ℕ => g ((j + 1) * p)) = fun j : ℕ =>
        (2 * cubicPotential d ((j + 1) * p) - residuePotential d ((j + 1) * p)) /
          ((j : ℝ) + 1) ^ 3 / ((p : ℕ) : ℝ) ^ 3 :=
      funext fun j => by simp only [g]; push_cast; field_simp
    rw [e]
    exact (hasSum_cubicKernel hd p).div_const _
  have hg : ∀ N : ℕ, 1 ≤ N → |g N| ≤ (d : ℝ) ^ 3 / 2 / (N : ℝ) ^ 2 := fun N hN => by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    simp only [g]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) ^ 3)]
    calc |2 * cubicPotential d N - residuePotential d N| / (N : ℝ) ^ 3
        ≤ (d : ℝ) ^ 3 / 2 / (N : ℝ) ^ 3 :=
          div_le_div_of_nonneg_right (abs_two_mul_cubicPotential_sub_le hd N) (by positivity)
      _ ≤ (d : ℝ) ^ 3 / 2 / (N : ℝ) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (pow_le_pow_right₀ hN1 (by norm_num))
  have h := hasSum_moebius_mul_tsum_mul g (summable_abs_mul_pnat_of_le hg)
  simp only [g, Nat.cast_one, one_pow, div_one] at h
  rw [funext fun p : ℕ+ => congrArg (fun x => (μ (p : ℕ) : ℝ) * x) (hrow p)]
  exact h

/-- `Σ_n μ(n)/n² = 6/π²`, over `ℕ+`. -/
theorem hasSum_pnat_moebius_div_sq :
    HasSum (fun p : ℕ+ => (μ (p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2) (6 / Real.pi ^ 2) := by
  have h := RHTower.hasSum_moebius_div_sq
  rw [← Function.Injective.hasSum_iff PNat.coe_injective] at h
  · exact h
  · intro n hn
    have : n = 0 := by
      by_contra h0
      exact hn ⟨⟨n, Nat.pos_of_ne_zero h0⟩, rfl⟩
    simp [this]

/-- **The Möbius row inverts the cross-scale kernel.** At every modulus `d ≥ 1`,
`Σ_n μ(n) ℓ_d(n) = 2Ψ_d(1) - (6/π²) m_d`. -/
theorem hasSum_moebius_mul_kernelTerm {d : ℕ} (hd : 0 < d) :
    HasSum (fun p : ℕ+ => (μ (p : ℕ) : ℝ) * kernelTerm d p)
      (2 * cubicPotential d 1 - 6 / Real.pi ^ 2 * kernelMean d) := by
  have h := ((hasSum_moebius_mul_bernoulliKernel hd).sub
    (hasSum_pnat_moebius_div_sq.mul_right (kernelMean d))).add (hasSum_moebius_mul_cubicKernel hd)
  have e : (fun p : ℕ+ => (μ (p : ℕ) : ℝ) * kernelTerm d p) = fun p : ℕ+ =>
      (μ (p : ℕ) : ℝ) * (bernoulliKernel d p / ((p : ℕ) : ℝ) ^ 2) -
        (μ (p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2 * kernelMean d +
      (μ (p : ℕ) : ℝ) * (cubicKernel d p / ((p : ℕ) : ℝ) ^ 3) :=
    funext fun p => by unfold kernelTerm; ring
  rw [e, show 2 * cubicPotential d 1 - 6 / Real.pi ^ 2 * kernelMean d =
    residuePotential d 1 - 6 / Real.pi ^ 2 * kernelMean d +
      (2 * cubicPotential d 1 - residuePotential d 1) by ring]
  exact h

/-- `2Ψ_d(1) = (d - 1)(d - 3)/4`. -/
theorem two_mul_cubicPotential_one {d : ℕ} (hd : 0 < d) :
    2 * cubicPotential d 1 = ((d : ℝ) - 1) * ((d : ℝ) - 3) / 4 := by
  unfold cubicPotential
  rcases Nat.lt_or_ge d 2 with h | h
  · obtain rfl : d = 1 := by omega
    norm_num
  · rw [Nat.mod_eq_of_lt (by omega : 1 < d)]
    push_cast
    ring

end

end GaloisForLFunctions.BezoutValuationIncidence
