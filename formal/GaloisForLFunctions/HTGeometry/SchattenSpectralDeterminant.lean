/-
# The regularized determinant of order `p` on an `ℓ^p` spectrum

On the spectral side a Schatten-`p` datum is an `ℓ^p` family of eigenvalues.  Its power traces
converge from exponent `p` upwards, so the order-`p` regularized exponent

```text
  ∑_{n ≥ p} zⁿ tr(Aⁿ) / n
```

converges on a disc, and its negative exponential is the order-`p` regularized determinant there.
By construction the determinant depends only on the traces from `p` upwards -- it *forgets* the
first `p − 1` of them -- and on a finite spectrum it is the finite-rank order-`p` determinant.

Main results:
* `IsSchattenSpectrum`, `exists_bound_of_isSchattenSpectrum` — the datum and its sup bound.
* `schattenTracePower`, `norm_schattenTracePower_le` — the power traces and their geometric bound.
* `schattenDetExp`, `schattenDet` — **the order-`p` regularized determinant on the disc**.
* `schattenDet_congr` — **it forgets the traces below `p`**.
* `schattenDet_eq_finiteDetOrder` — **it extends the finite-rank order-`p` determinant**.
* `tendsto_schattenDet_of_tendsto_tracePower` — **it is continuous in the power traces**.
-/
import GaloisForLFunctions.HTGeometry.FiniteRegularizedDeterminantOrder
import Mathlib.Analysis.Normed.Group.Tannery

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

/-- An `ℓ^p` spectrum: the spectral-side Schatten-`p` datum of a compact operator. -/
def IsSchattenSpectrum (p : ℕ) (lam : ι → ℂ) : Prop := Summable fun i => ‖lam i‖ ^ p

/-- **An `ℓ^p` spectrum is bounded.** -/
theorem exists_bound_of_isSchattenSpectrum {p : ℕ} (_hp : 0 < p) {lam : ι → ℂ}
    (h : IsSchattenSpectrum p lam) : ∃ B : ℝ, 1 ≤ B ∧ ∀ i, ‖lam i‖ ≤ B := by
  classical
  have hcof : ∀ᶠ i in cofinite, ‖lam i‖ ^ p < 1 :=
    h.tendsto_cofinite_zero.eventually_lt_const (by norm_num)
  have hfin : {i | ¬ ‖lam i‖ ^ p < 1}.Finite := Filter.eventually_cofinite.mp hcof
  refine ⟨1 + ∑ i ∈ hfin.toFinset, ‖lam i‖, ?_, fun i => ?_⟩
  · have : 0 ≤ ∑ i ∈ hfin.toFinset, ‖lam i‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    linarith
  · by_cases hi : ‖lam i‖ ^ p < 1
    · have hlt : ‖lam i‖ < 1 := by
        by_contra hcon
        rw [not_lt] at hcon
        exact absurd (one_le_pow₀ hcon) (not_le.mpr hi)
      have : 0 ≤ ∑ j ∈ hfin.toFinset, ‖lam j‖ :=
        Finset.sum_nonneg fun j _ => norm_nonneg _
      linarith
    · have hmem : i ∈ hfin.toFinset := by
        simpa using hi
      have hle : ‖lam i‖ ≤ ∑ j ∈ hfin.toFinset, ‖lam j‖ :=
        Finset.single_le_sum (fun j _ => norm_nonneg (lam j)) hmem
      linarith

/-- Above the Schatten exponent every power of an `ℓ^p` spectrum is summable. -/
theorem summable_normPow_of_le {p n : ℕ} (_hp : 0 < p) (hpn : p ≤ n) {lam : ι → ℂ}
    (h : IsSchattenSpectrum p lam) : Summable fun i => ‖lam i‖ ^ n := by
  refine Summable.of_norm_bounded_eventually h ?_
  have hcof : ∀ᶠ i in cofinite, ‖lam i‖ ^ p < 1 :=
    h.tendsto_cofinite_zero.eventually_lt_const (by norm_num)
  filter_upwards [hcof] with i hi
  have hlt : ‖lam i‖ ≤ 1 := by
    by_contra hcon
    rw [not_le] at hcon
    exact absurd (one_le_pow₀ hcon.le) (not_le.mpr hi)
  have := pow_le_pow_of_le_one (norm_nonneg (lam i)) hlt hpn
  simpa [abs_of_nonneg (pow_nonneg (norm_nonneg (lam i)) n)] using this

theorem summable_pow_of_le {p n : ℕ} (hp : 0 < p) (hpn : p ≤ n) {lam : ι → ℂ}
    (h : IsSchattenSpectrum p lam) : Summable fun i => (lam i) ^ n := by
  refine Summable.of_norm ?_
  simpa [norm_pow] using summable_normPow_of_le hp hpn h

/-- The `n`-th power trace of a spectrum. -/
def schattenTracePower (lam : ι → ℂ) (n : ℕ) : ℂ := ∑' i, (lam i) ^ n

/-- **The geometric bound on the power traces.** -/
theorem norm_schattenTracePower_le {p k : ℕ} (hp : 0 < p) {lam : ι → ℂ}
    (h : IsSchattenSpectrum p lam) {B : ℝ} (hB1 : 1 ≤ B) (hB : ∀ i, ‖lam i‖ ≤ B) :
    ‖schattenTracePower lam (k + p)‖ ≤ B ^ k * ∑' i, ‖lam i‖ ^ p := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hsum : Summable fun i => ‖(lam i) ^ (k + p)‖ := by
    simpa [norm_pow] using summable_normPow_of_le hp (Nat.le_add_left p k) h
  have hstep : ∀ i, ‖(lam i) ^ (k + p)‖ ≤ B ^ k * ‖lam i‖ ^ p := by
    intro i
    rw [norm_pow, pow_add]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hB i) k)
      (pow_nonneg (norm_nonneg _) p)
  calc ‖schattenTracePower lam (k + p)‖ ≤ ∑' i, ‖(lam i) ^ (k + p)‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' i, B ^ k * ‖lam i‖ ^ p := by
        exact Summable.tsum_le_tsum hstep hsum (h.mul_left _)
    _ = B ^ k * ∑' i, ‖lam i‖ ^ p := tsum_mul_left

/-- The order-`p` regularized exponent of a spectrum. -/
def schattenDetExp (p : ℕ) (lam : ι → ℂ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, z ^ (k + p) / ((k + p : ℕ) : ℂ) * schattenTracePower lam (k + p)

/-- The regularized exponent converges inside the reciprocal spectral radius. -/
theorem summable_schattenDetExp {p : ℕ} (hp : 0 < p) {lam : ι → ℂ}
    (h : IsSchattenSpectrum p lam) {B : ℝ} (hB1 : 1 ≤ B) (hB : ∀ i, ‖lam i‖ ≤ B)
    {z : ℂ} (hz : ‖z‖ * B < 1) :
    Summable fun k : ℕ => z ^ (k + p) / ((k + p : ℕ) : ℂ) * schattenTracePower lam (k + p) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  set S : ℝ := ∑' i, ‖lam i‖ ^ p with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun i => pow_nonneg (norm_nonneg _) p
  have hzB0 : 0 ≤ ‖z‖ * B := mul_nonneg (norm_nonneg z) hB0
  refine Summable.of_norm_bounded (g := fun k : ℕ => (S * ‖z‖ ^ p) * (‖z‖ * B) ^ k) ?_ ?_
  · exact ((summable_geometric_of_lt_one hzB0 hz).mul_left _)
  · intro k
    have hden : (1 : ℝ) ≤ ‖((k + p : ℕ) : ℂ)‖ := by
      rw [Complex.norm_natCast]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
    have htr := norm_schattenTracePower_le (k := k) hp h hB1 hB
    have hnum : ‖z ^ (k + p) / ((k + p : ℕ) : ℂ) * schattenTracePower lam (k + p)‖
        ≤ ‖z‖ ^ (k + p) * (B ^ k * S) := by
      rw [norm_mul, norm_div, norm_pow]
      refine mul_le_mul ?_ htr (norm_nonneg _) (by positivity)
      rw [div_le_iff₀ (by linarith : (0:ℝ) < ‖((k + p : ℕ) : ℂ)‖)]
      nlinarith [pow_nonneg (norm_nonneg z) (k + p)]
    refine le_trans hnum (le_of_eq ?_)
    rw [pow_add, mul_pow]
    ring

/-- **The order-`p` regularized determinant of a spectrum.** -/
def schattenDet (p : ℕ) (lam : ι → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (- schattenDetExp p lam z)

/-- **The determinant forgets every trace below the Schatten exponent.** -/
theorem schattenDet_congr {p : ℕ} {lam mu : ι → ℂ}
    (h : ∀ n, p ≤ n → schattenTracePower lam n = schattenTracePower mu n) (z : ℂ) :
    schattenDet p lam z = schattenDet p mu z := by
  have hexp : schattenDetExp p lam z = schattenDetExp p mu z := by
    refine tsum_congr fun k => ?_
    rw [h (k + p) (Nat.le_add_left p k)]
  rw [schattenDet, schattenDet, hexp]

/-- Every family on a finite index set is an `ℓ^p` spectrum. -/
theorem isSchattenSpectrum_of_finite [Finite ι] (p : ℕ) (lam : ι → ℂ) :
    IsSchattenSpectrum p lam := Summable.of_finite

/-- The power traces of a finite spectrum are the matrix power traces of its diagonal. -/
theorem schattenTracePower_diagonal {n : ℕ} (lam : Fin n → ℂ) (m : ℕ) :
    ((Matrix.diagonal lam) ^ m).trace = schattenTracePower lam m := by
  rw [Matrix.diagonal_pow, Matrix.trace_diagonal, schattenTracePower, tsum_fintype]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- **The order-`p` regularized determinant of a finite spectrum is the finite-rank order-`p`
determinant of its diagonal.** -/
theorem schattenDet_eq_finiteDetOrder {p n : ℕ} (hp : 0 < p) (lam : Fin n → ℂ) {z : ℂ}
    (hz : ‖z‖ * Real.sqrt (matHSNormSq (Matrix.diagonal lam)) < 1) :
    schattenDet p lam z = finiteDetOrder (p - 1) (-(Matrix.diagonal lam)) z := by
  have hg : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos hp
  have hmain := exp_neg_traceSeries_eq_finiteDetOrder_neg (p - 1) (Matrix.diagonal lam) hz
  rw [hg] at hmain
  have hterm : ∀ k : ℕ, z ^ (k + p) / ((k + p : ℕ) : ℂ) * schattenTracePower lam (k + p)
      = z ^ (k + p) / ((k + p : ℕ) : ℂ) * ((Matrix.diagonal lam) ^ (k + p)).trace := by
    intro k
    rw [schattenTracePower_diagonal]
  rw [← hmain, schattenDet, schattenDetExp, tsum_congr hterm]

/-- **Continuity of the order-`p` determinant in the power traces.**  Along any filter on which the
power traces converge under a common geometric bound, the determinants converge. -/
theorem tendsto_schattenDet_of_tendsto_tracePower {p : ℕ} (hp : 0 < p)
    {L : Type*} {l : Filter L} {lam : L → ι → ℂ} {mu : ι → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B) (_hS0 : 0 ≤ S)
    (hbound : ∀ (a : L) (k : ℕ), ‖schattenTracePower (lam a) (k + p)‖ ≤ S * B ^ k)
    (hconv : ∀ k : ℕ, Filter.Tendsto (fun a => schattenTracePower (lam a) (k + p)) l
      (nhds (schattenTracePower mu (k + p))))
    {z : ℂ} (hz : ‖z‖ * B < 1) :
    Filter.Tendsto (fun a => schattenDet p (lam a) z) l (nhds (schattenDet p mu z)) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hzB0 : 0 ≤ ‖z‖ * B := mul_nonneg (norm_nonneg z) hB0
  have hdom : Summable fun k : ℕ => (S * ‖z‖ ^ p) * (‖z‖ * B) ^ k :=
    (summable_geometric_of_lt_one hzB0 hz).mul_left _
  have hbnd : ∀ (a : L) (k : ℕ),
      ‖z ^ (k + p) / ((k + p : ℕ) : ℂ) * schattenTracePower (lam a) (k + p)‖
        ≤ (S * ‖z‖ ^ p) * (‖z‖ * B) ^ k := by
    intro a k
    have hden : (1 : ℝ) ≤ ‖((k + p : ℕ) : ℂ)‖ := by
      rw [Complex.norm_natCast]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
    have hnum : ‖z ^ (k + p) / ((k + p : ℕ) : ℂ) * schattenTracePower (lam a) (k + p)‖
        ≤ ‖z‖ ^ (k + p) * (S * B ^ k) := by
      rw [norm_mul, norm_div, norm_pow]
      refine mul_le_mul ?_ (hbound a k) (norm_nonneg _) (by positivity)
      rw [div_le_iff₀ (by linarith : (0:ℝ) < ‖((k + p : ℕ) : ℂ)‖)]
      nlinarith [pow_nonneg (norm_nonneg z) (k + p)]
    refine le_trans hnum (le_of_eq ?_)
    rw [pow_add, mul_pow]
    ring
  have hexp : Filter.Tendsto (fun a => schattenDetExp p (lam a) z) l
      (nhds (schattenDetExp p mu z)) := by
    simp only [schattenDetExp]
    exact tendsto_tsum_of_dominated_convergence hdom (fun k => (hconv k).const_mul _)
      (Filter.Eventually.of_forall fun a k => hbnd a k)
  exact (Complex.continuous_exp.continuousAt).tendsto.comp hexp.neg

end

end GaloisForLFunctions.HTGeometry
