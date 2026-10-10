import GaloisForLFunctions.RHTower.CCMGeneralizedVonKoch
import GaloisForLFunctions.RHTower.DirichletPolyBoundedAbel
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# The abscissa of convergence of `Σ (Λ(n) − 1) n^{-s}` is the zero-free abscissa

`Σ Λ(n) n^{-s}` and `Σ n^{-s}` both have abscissa of convergence `1`: their coefficients are
nonnegative.  Their difference `Σ (Λ(n) − 1) n^{-s} = −ζ'/ζ(s) − ζ(s)` has the pole at `s = 1`
removed, and its convergence measures the zeros exactly:

  `ξ` has no zero with `Re ρ > ½ + α`  ⟺  `Σ (Λ(n) − 1) n^{-σ}` converges for every real `σ > ½ + α`

(`xiZeroHalfPlaneBound_iff_vonMangoldtMinusOne_converges`, any `α ≥ 0`).  At `α = 0`:
RH ⟺ the series converges at every `σ > ½` (`riemannHypothesis_iff_vonMangoldtMinusOne_converges`).

The partial sums are `ψ(N) − N`.  If `ξ` has no zeros right of `½ + α`, the generalized von Koch theorem
gives `ψ(N) − N = O(N^{½+α+ε})`.  Abel summation against polynomially bounded partial sums then
gives convergence.  Conversely, convergence at `σ` keeps the partial sums of
`(Λ(n) − 1) n^{-σ}` bounded.  Abel summation against the increasing weights `n^σ` gives
`ψ(N) − N = O(N^σ)` (Kronecker), and the converse von Koch theorem places the zeros.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The coefficients `Λ(n+1) − 1`, indexed from `0`. -/
def vonMangoldtMinusOne (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt (n + 1) - 1

theorem sum_range_vonMangoldtMinusOne (N : ℕ) :
    ∑ n ∈ Finset.range N, vonMangoldtMinusOne n =
      (∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt k : ℝ)) - N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega), vonMangoldtMinusOne]
    push_cast
    ring

/-- **Abel's inequality for increasing weights.** -/
theorem abs_sum_mul_le_of_bounded_partial_mono {g w : ℕ → ℝ} {B : ℝ} (n : ℕ)
    (hB : ∀ k, |∑ j ∈ Finset.range k, g j| ≤ B) (hw0 : ∀ i, 0 ≤ w i)
    (hwmono : ∀ i, w i ≤ w (i + 1)) :
    |∑ i ∈ Finset.range n, w i * g i| ≤ 2 * B * w (n - 1) := by
  have hBnn : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hparts := Finset.sum_range_by_parts w g n
  simp only [smul_eq_mul] at hparts
  rw [hparts]
  have hhead : |w (n - 1) * ∑ i ∈ Finset.range n, g i| ≤ w (n - 1) * B := by
    rw [abs_mul, abs_of_nonneg (hw0 (n - 1))]
    exact mul_le_mul_of_nonneg_left (hB n) (hw0 (n - 1))
  have htel : ∑ i ∈ Finset.range (n - 1), (w (i + 1) - w i) = w (n - 1) - w 0 :=
    Finset.sum_range_sub w (n - 1)
  have htail : |∑ i ∈ Finset.range (n - 1),
      (w (i + 1) - w i) * ∑ j ∈ Finset.range (i + 1), g j| ≤ B * (w (n - 1) - w 0) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [← htel, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (hwmono i)), mul_comm]
    exact mul_le_mul_of_nonneg_right (hB (i + 1)) (sub_nonneg.2 (hwmono i))
  have := abs_sub _ _ |>.trans (add_le_add hhead htail)
  nlinarith [hw0 0, hw0 (n - 1)]

/-- **Kronecker.**  If `Σ (Λ(n) − 1) n^{-σ}` converges at a real `σ > 0`, then
`|ψ(N) − N| ≤ C N^σ`. -/
theorem exists_abs_sum_vonMangoldtMinusOne_le_of_converges {σ : ℝ} (hσ : 0 < σ)
    (hconv : ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N,
      ((vonMangoldtMinusOne n : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(σ : ℂ))) atTop (𝓝 L)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |∑ n ∈ Finset.range N, vonMangoldtMinusOne n| ≤ C * (N : ℝ) ^ σ := by
  obtain ⟨L, hL⟩ := hconv
  obtain ⟨M, hM⟩ := (isBounded_iff_forall_norm_le).1 hL.cauchySeq.isBounded_range
  set g : ℕ → ℝ := fun n => vonMangoldtMinusOne n * ((n : ℝ) + 1) ^ (-σ) with hg
  have hterm : ∀ n, ((vonMangoldtMinusOne n : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(σ : ℂ)) =
      ((g n : ℝ) : ℂ) := by
    intro n
    rw [hg, Complex.ofReal_mul, Complex.ofReal_cpow (by positivity), Complex.ofReal_neg]
  have hB : ∀ k, |∑ j ∈ Finset.range k, g j| ≤ M := by
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
  have hwg : ∀ n, w n * g n = vonMangoldtMinusOne n := by
    intro n
    simp only [hw, hg]
    rw [mul_left_comm, ← Real.rpow_add (by positivity), add_neg_cancel, Real.rpow_zero, mul_one]
  have habel := abs_sum_mul_le_of_bounded_partial_mono N hB hw0 hwmono
  simp only [hwg] at habel
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp only [Finset.range_zero, Finset.sum_empty, abs_zero, Nat.cast_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg le_rfl σ)
  · have hwN : w (N - 1) = (N : ℝ) ^ σ := by
      simp only [hw]
      rw [Nat.cast_sub hNpos, Nat.cast_one, sub_add_cancel]
    rwa [hwN] at habel

/-- Convergence of `Σ (Λ(n) − 1) n^{-σ}` for all `σ > ½ + α` gives the Chebyshev error spectrum. -/
theorem chebyshevErrorPowerSpectrum_of_vonMangoldtMinusOne_converges {α : ℝ} (hα : 0 ≤ α)
    (h : ∀ σ : ℝ, 1 / 2 + α < σ → ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N,
      ((vonMangoldtMinusOne n : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(σ : ℂ))) atTop (𝓝 L)) :
    ChebyshevErrorPowerSpectrum α := by
  intro ε hε
  set σ : ℝ := 1 / 2 + α + ε with hσdef
  have hσ : 0 < σ := by positivity
  obtain ⟨C, hC0, hC⟩ := exists_abs_sum_vonMangoldtMinusOne_le_of_converges hσ (h σ (by linarith))
  refine ⟨C + 1, by positivity, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  rw [criticalMellinError_vonMangoldt_eq_chebyshevPsiReal_sub]
  have hflle : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0.le
  have hfllt : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
  have hpsi : chebyshevPsiReal x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) := by
    rw [chebyshevPsiReal_eq_sum_range, sum_range_succ_vonMangoldt_eq_sum_Icc]
  have hb := hC ⌊x⌋₊
  rw [sum_range_vonMangoldtMinusOne] at hb
  have hmono : ((⌊x⌋₊ : ℕ) : ℝ) ^ σ ≤ x ^ σ := Real.rpow_le_rpow (by positivity) hflle hσ.le
  have hone : (1 : ℝ) ≤ x ^ σ := Real.one_le_rpow hx hσ.le
  have htri : |chebyshevPsiReal x - x| ≤
      |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ)) - ((⌊x⌋₊ : ℕ) : ℝ)| +
        |((⌊x⌋₊ : ℕ) : ℝ) - x| := by
    rw [hpsi]
    exact abs_sub_le _ _ _
  have hgap : |((⌊x⌋₊ : ℕ) : ℝ) - x| ≤ 1 := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hmono hC0]

/-- A Chebyshev error spectrum at width `α` gives convergence of `Σ (Λ(n) − 1) n^{-σ}` for
every `σ > ½ + α`. -/
theorem vonMangoldtMinusOne_converges_of_chebyshevErrorPowerSpectrum {α : ℝ} (hα : 0 ≤ α)
    (hspec : ChebyshevErrorPowerSpectrum α) {σ : ℝ} (hσ : 1 / 2 + α < σ) :
    ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N,
      ((vonMangoldtMinusOne n : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(σ : ℂ))) atTop (𝓝 L) := by
  set ε : ℝ := (σ - (1 / 2 + α)) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨C, hC0, hC⟩ := hspec ε hε
  set β : ℝ := 1 / 2 + α + ε with hβ
  have hβ0 : 0 ≤ β := by positivity
  refine GaloisForLFunctions.RHTower.tendsto_dirichlet_partialSum_of_poly_bounded hC0 hβ0
    (fun N => ?_) (by rw [Complex.ofReal_re, hβ, hεdef]; linarith)
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs, sum_range_vonMangoldtMinusOne]
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp only [CharP.cast_eq_zero, zero_add, Real.one_rpow, mul_one]
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (1 : ℕ) > 0), Finset.sum_empty, sub_zero,
      abs_zero]
    exact hC0
  · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
    have h := hC N hN1
    rw [criticalMellinError_vonMangoldt_eq_chebyshevPsiReal_sub, chebyshevPsiReal_eq_sum_range,
      Nat.floor_natCast, sum_range_succ_vonMangoldt_eq_sum_Icc] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    exact Real.rpow_le_rpow (by positivity) (by linarith) hβ0

/-- **Zero-free half-planes are abscissae of convergence.**  For `α ≥ 0`, every zero of `ξ` has
`Re ρ ≤ ½ + α` iff `Σ (Λ(n) − 1) n^{-σ}` converges for every real `σ > ½ + α`. -/
theorem xiZeroHalfPlaneBound_iff_vonMangoldtMinusOne_converges {α : ℝ} (hα : 0 ≤ α) :
    XiZeroHalfPlaneBound α ↔ ∀ σ : ℝ, 1 / 2 + α < σ → ∃ L : ℂ, Tendsto (fun N =>
      ∑ n ∈ Finset.range N,
        ((vonMangoldtMinusOne n : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(σ : ℂ))) atTop (𝓝 L) :=
  ⟨fun hXi _ hσ => vonMangoldtMinusOne_converges_of_chebyshevErrorPowerSpectrum hα
      (chebyshevErrorPowerSpectrum_of_xiZeroHalfPlaneBound hα hXi) hσ,
    fun h => xiZeroHalfPlaneBound_of_chebyshevErrorPowerSpectrum hα
      (chebyshevErrorPowerSpectrum_of_vonMangoldtMinusOne_converges hα h)⟩

theorem riemannHypothesis_iff_xiZeroHalfPlaneBound_zero :
    RiemannHypothesis ↔ XiZeroHalfPlaneBound 0 := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  constructor
  · intro h ρ hρ
    rw [h ρ hρ]; norm_num
  · intro h ρ hρ
    have h1 := h ρ hρ
    have h2 := h (1 - ρ) (by rw [xi_one_sub]; exact hρ)
    rw [Complex.sub_re, Complex.one_re] at h2
    linarith

/-- **RH as an abscissa of convergence.**  RH holds iff `Σ (Λ(n) − 1) n^{-σ}` converges for every
real `σ > ½`. -/
theorem riemannHypothesis_iff_vonMangoldtMinusOne_converges :
    RiemannHypothesis ↔ ∀ σ : ℝ, 1 / 2 < σ → ∃ L : ℂ, Tendsto (fun N =>
      ∑ n ∈ Finset.range N,
        ((vonMangoldtMinusOne n : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(σ : ℂ))) atTop (𝓝 L) := by
  rw [riemannHypothesis_iff_xiZeroHalfPlaneBound_zero,
    xiZeroHalfPlaneBound_iff_vonMangoldtMinusOne_converges le_rfl]
  simp only [add_zero]

end

end RHTower
