import GaloisForLFunctions.RHTower.VonMangoldtMinusOneAbscissa
import GaloisForLFunctions.RHTower.LiouvilleExponentialSumRH

/-!
# Abscissae of convergence of the signed arithmetic Dirichlet series

For a real sequence `f` with partial sums `S(N) = Σ_{n ≤ N} f(n)`,

  `S(N) = O(N^{½+δ})` for every `δ > 0`  ⟺  `Σ f(n) n^{-σ}` converges for every real `σ > ½`

(`forall_halfPower_bound_iff_forall_converges`): Abel summation against polynomially bounded
partial sums one way, Kronecker's lemma the other.  With the corpus Mertens and Liouville summatory
equivalences this gives

* RH ⟺ `Σ μ(n) n^{-σ}` converges for every `σ > ½` (`riemannHypothesis_iff_moebius_converges`);
* RH ⟺ `Σ λ(n) n^{-σ}` converges for every `σ > ½` (`riemannHypothesis_iff_liouville_converges`);

alongside RH ⟺ `Σ (Λ(n) − 1) n^{-σ}` converges for every `σ > ½`
(`riemannHypothesis_iff_vonMangoldtMinusOne_converges`).  The nonnegative sequences `Λ`, `Λ/log`
and `1_{prime}` have abscissa of convergence `1` unconditionally
(`summable_of_dirichletConvergesAt_of_nonneg`).  So exactly the signed, pole-free sequences carry
the zeros in their abscissa of convergence.
-/

open Filter Topology

namespace RHTower

noncomputable section

theorem sum_range_succ_eq_sourcePartialSum (f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, f (n + 1) = sourcePartialSum f N := by
  induction N with
  | zero => simp [sourcePartialSum]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, sourcePartialSum, sourcePartialSum,
      Finset.sum_Icc_succ_top (by omega)]

/-- **Kronecker's lemma.**  If `Σ g(n) (n+1)^{-σ}` converges at a real `σ > 0`, then
`|Σ_{n<N} g(n)| ≤ C N^σ`. -/
theorem exists_abs_sum_range_le_of_converges (g : ℕ → ℝ) {σ : ℝ} (hσ : 0 < σ)
    (hconv : ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N,
      ((g n : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(σ : ℂ))) atTop (𝓝 L)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |∑ n ∈ Finset.range N, g n| ≤ C * (N : ℝ) ^ σ := by
  obtain ⟨L, hL⟩ := hconv
  obtain ⟨M, hM⟩ := (isBounded_iff_forall_norm_le).1 hL.cauchySeq.isBounded_range
  set c : ℕ → ℝ := fun n => g n * ((n : ℝ) + 1) ^ (-σ) with hc
  have hterm : ∀ n, ((g n : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(σ : ℂ)) = ((c n : ℝ) : ℂ) := by
    intro n
    rw [hc, Complex.ofReal_mul, Complex.ofReal_cpow (by positivity), Complex.ofReal_neg]
  have hB : ∀ k, |∑ j ∈ Finset.range k, c j| ≤ M := by
    intro k
    have h := hM _ (Set.mem_range_self k)
    simp only [hterm] at h
    rwa [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs] at h
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hB 0)
  refine ⟨2 * M, by positivity, fun N => ?_⟩
  set w : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ σ with hw
  have hw0 : ∀ i, 0 ≤ w i := fun i => by positivity
  have hwmono : ∀ i, w i ≤ w (i + 1) := fun i => by
    simp only [hw]
    exact Real.rpow_le_rpow (by positivity) (by push_cast; linarith) hσ.le
  have hwc : ∀ n, w n * c n = g n := by
    intro n
    simp only [hw, hc]
    rw [mul_left_comm, ← Real.rpow_add (by positivity), add_neg_cancel, Real.rpow_zero, mul_one]
  have habel := abs_sum_mul_le_of_bounded_partial_mono N hB hw0 hwmono
  simp only [hwc] at habel
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp only [Finset.range_zero, Finset.sum_empty, abs_zero, Nat.cast_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg le_rfl σ)
  · have hwN : w (N - 1) = (N : ℝ) ^ σ := by
      simp only [hw]
      rw [Nat.cast_sub hNpos, Nat.cast_one, sub_add_cancel]
    rwa [hwN] at habel

/-- **Half-power partial sums are the abscissa `½`.** -/
theorem forall_halfPower_bound_iff_forall_converges (f : ℕ → ℝ) :
    (∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
        |sourcePartialSum f N| ≤ C * ((N : ℝ) + 1) ^ (1 / 2 + δ)) ↔
      ∀ σ : ℝ, 1 / 2 < σ → ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N,
        ((f (n + 1) : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(σ : ℂ))) atTop (𝓝 L) := by
  constructor
  · intro h σ hσ
    set δ : ℝ := (σ - 1 / 2) / 2 with hδ
    obtain ⟨C, hC0, hC⟩ := h δ (by rw [hδ]; linarith)
    refine GaloisForLFunctions.RHTower.tendsto_dirichlet_partialSum_of_poly_bounded
      (α := 1 / 2 + δ) hC0 (by rw [hδ]; linarith) (fun N => ?_)
      (by rw [Complex.ofReal_re, hδ]; linarith)
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
      sum_range_succ_eq_sourcePartialSum]
    exact hC N
  · intro h δ hδ
    obtain ⟨C, hC0, hC⟩ := exists_abs_sum_range_le_of_converges (fun n => f (n + 1))
      (by linarith : (0 : ℝ) < 1 / 2 + δ) (h (1 / 2 + δ) (by linarith))
    refine ⟨C, hC0, fun N => ?_⟩
    rw [← sum_range_succ_eq_sourcePartialSum]
    refine (hC N).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)

/-- **RH as the abscissa of `Σ μ(n) n^{-s}`.** -/
theorem riemannHypothesis_iff_moebius_converges :
    RiemannHypothesis ↔ ∀ σ : ℝ, 1 / 2 < σ → ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N,
      ((moebiusR (n + 1) : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(σ : ℂ))) atTop (𝓝 L) := by
  rw [← mobiusMertensAllStrictHalfPowerBound_iff_riemannHypothesis,
    ← forall_halfPower_bound_iff_forall_converges]
  unfold MobiusMertensAllStrictHalfPowerBound
  simp only [norm_mobiusMertensPartialSum_eq]

/-- **RH as the abscissa of `Σ λ(n) n^{-s}`.** -/
theorem riemannHypothesis_iff_liouville_converges :
    RiemannHypothesis ↔ ∀ σ : ℝ, 1 / 2 < σ → ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N,
      ((liouvilleR (n + 1) : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(σ : ℂ))) atTop (𝓝 L) := by
  rw [riemannHypothesis_iff_forall_liouvilleSummatory_le,
    forall_halfPower_bound_iff_forall_converges]

end

end RHTower
