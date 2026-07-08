/-
# The infinite (countable-rank) Hilbert–Schmidt diagonal determinant

The finite diagonal operator `diagMul g` (supported on a `Finset`) realized each finite Euler product as a
Fredholm determinant.  This file removes the finite-rank restriction: a diagonal operator `diagMul g` with
countably many nonzero entries `g i` is Hilbert–Schmidt precisely when its energies are summable,
`∑ᵢ ‖g i‖² < ∞`, and then its regularized determinant `det₂(1 − z·diagMul g)` has a closed-form resolvent
trace given by the *convergent series* over all diagonal entries,

  `resolventTrace (diagMul g) z = ∑ᵢ z·(g i)²/(1 − z·g i)`   (on `|z|·‖diagMul g‖_HS < 1`),

so that (with `logDeriv_fredholmDet`) `logDeriv det₂(1 − z·diagMul g) = −∑ᵢ z·(g i)²/(1 − z·g i)`.

This is the substrate an infinite realization consumes: the archimedean factor `1/Γ` and the full Euler
product are both countable diagonal operators of exactly this shape (`∑ 1/n² < ∞`), lying past finite rank.
The double series over `(n, i)` — power index and diagonal index — is summed by absolute convergence
(dominated by `‖z‖^{n+1}·‖K‖_HS^n·‖g i‖²`, a geometric–times–summable bound) and Tonelli's theorem for
`tsum` (`Summable.tsum_comm`).

Main results:
* `isHS_diagMul_infinite` — `∑ᵢ ‖g i‖² < ∞ ⟹ diagMul g` is Hilbert–Schmidt.
* `hsNormSq_diagMul_infinite` — `‖diagMul g‖_HS² = ∑ᵢ ‖g i‖²`.
* `norm_le_hsNorm_diagMul_infinite` — each entry is bounded by the HS norm, `‖g i‖ ≤ ‖diagMul g‖_HS`.
* `resolventTrace_diagMul_infinite` — the countable resolvent trace `∑ᵢ z·(g i)²/(1 − z·g i)`.
* `logDeriv_fredholmDet_diagMul_infinite` — the Plemelj identity for the infinite diagonal operator.
-/
import GaloisForLFunctions.FredholmDeterminantExamples

open scoped BigOperators

namespace HilbertSchmidt

variable {ι : Type*} [DecidableEq ι]

/-- A diagonal operator with summable energies `∑ᵢ ‖g i‖² < ∞` is Hilbert–Schmidt: its kernel is supported
on the diagonal, an injective copy of the index set, so the two-dimensional energy sum collapses to the
one-dimensional summable series. -/
theorem isHS_diagMul_infinite (g : ι → ℂ) (hs : Summable (fun i => ‖g i‖ ^ 2)) :
    IsHS (diagMul g) := by
  have hinj : Function.Injective (fun i : ι => (i, i)) := fun a b h => (Prod.ext_iff.mp h).1
  have hzero : ∀ p ∉ Set.range (fun i : ι => (i, i)), ‖diagMul g p‖ ^ 2 = 0 := by
    intro p hp
    have hpp : p.1 ≠ p.2 := fun h => hp ⟨p.1, by rw [Prod.ext_iff]; exact ⟨rfl, h⟩⟩
    simp [diagMul, hpp]
  rw [IsHS, ← hinj.summable_iff hzero]
  have hcomp : ((fun p : ι × ι => ‖diagMul g p‖ ^ 2) ∘ (fun i : ι => (i, i)))
      = fun i => ‖g i‖ ^ 2 := by funext i; simp [Function.comp, diagMul]
  rw [hcomp]; exact hs

/-- The Hilbert–Schmidt norm squared of a countable diagonal operator is the sum of its entry energies,
`‖diagMul g‖_HS² = ∑ᵢ ‖g i‖²` (the diagonal support collapses the `ι × ι` energy sum). -/
theorem hsNormSq_diagMul_infinite (g : ι → ℂ) :
    hsNormSq (diagMul g) = ∑' i, ‖g i‖ ^ 2 := by
  have hinj : Function.Injective (fun i : ι => (i, i)) := fun a b h => (Prod.ext_iff.mp h).1
  have hsupp : Function.support (fun p : ι × ι => ‖diagMul g p‖ ^ 2)
      ⊆ Set.range (fun i : ι => (i, i)) := by
    intro p hp; rw [Function.mem_support] at hp
    have hpp : p.1 = p.2 := by by_contra hne; exact hp (by simp [diagMul, hne])
    exact ⟨p.1, by rw [Prod.ext_iff]; exact ⟨rfl, hpp⟩⟩
  rw [hsNormSq, ← Function.Injective.tsum_eq hinj hsupp]
  apply tsum_congr; intro i; simp [diagMul]

/-- Every diagonal entry is bounded by the Hilbert–Schmidt norm: `‖g i‖ ≤ ‖diagMul g‖_HS`, since `‖g i‖²`
is a single term of the summable energy series `∑ⱼ ‖g j‖²`. -/
theorem norm_le_hsNorm_diagMul_infinite (g : ι → ℂ) (hs : Summable (fun i => ‖g i‖ ^ 2)) (i : ι) :
    ‖g i‖ ≤ hsNorm (diagMul g) := by
  rw [hsNorm, hsNormSq_diagMul_infinite g,
    show ‖g i‖ = Real.sqrt (‖g i‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
  exact Real.sqrt_le_sqrt (Summable.le_tsum hs i (fun j _ => sq_nonneg _))

/-- **The resolvent trace of a countable diagonal Hilbert–Schmidt operator** is the convergent series over
all diagonal entries, `resolventTrace (diagMul g) z = ∑ᵢ z·(g i)²/(1 − z·g i)`, on the disk
`|z|·‖diagMul g‖_HS < 1`.  The double series over the power index `n` and the diagonal index `i` is summed
by absolute convergence — each entry `‖z‖^{n+1}·‖g i‖^{n+2}` is dominated by `‖z‖^{n+1}·M^n·‖g i‖²`
(`M = ‖diagMul g‖_HS`), a geometric-in-`n` times summable-in-`i` bound — and Tonelli's theorem for `tsum`
lets the sums be exchanged; the inner geometric series in `n` sums to `z·(g i)²/(1 − z·g i)`. -/
theorem resolventTrace_diagMul_infinite (g : ι → ℂ) (hs : Summable (fun i => ‖g i‖ ^ 2))
    (r : ℝ) (hr : r * hsNorm (diagMul g) < 1) (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) :
    resolventTrace (diagMul g) z = ∑' i, z * g i ^ 2 / (1 - z * g i) := by
  set M := hsNorm (diagMul g) with hM
  have hM0 : 0 ≤ M := hsNorm_nonneg _
  have hzr : ‖z‖ < r := by rwa [mem_ball_zero_iff] at hz
  have hzM : ‖z‖ * M < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hzr.le hM0) hr
  have hgle : ∀ i, ‖g i‖ ≤ M := fun i => norm_le_hsNorm_diagMul_infinite g hs i
  have hzgi : ∀ i, ‖z * g i‖ < 1 := fun i => by
    rw [norm_mul]; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hgle i) (norm_nonneg z)) hzM
  have hpow : ∀ (n : ℕ) (i : ι), ‖g i‖ ^ (n + 2) ≤ M ^ n * ‖g i‖ ^ 2 := by
    intro n i; rw [pow_add]; gcongr; exact hgle i
  have hbound_i : ∀ (n : ℕ) (i : ι),
      ‖z‖ ^ (n + 1) * ‖g i‖ ^ (n + 2) ≤ ‖z‖ ^ (n + 1) * M ^ n * ‖g i‖ ^ 2 := by
    intro n i
    calc ‖z‖ ^ (n + 1) * ‖g i‖ ^ (n + 2)
        ≤ ‖z‖ ^ (n + 1) * (M ^ n * ‖g i‖ ^ 2) := mul_le_mul_of_nonneg_left (hpow n i) (by positivity)
      _ = ‖z‖ ^ (n + 1) * M ^ n * ‖g i‖ ^ 2 := by ring
  have hsum_i : ∀ n : ℕ, Summable (fun i => ‖z‖ ^ (n + 1) * ‖g i‖ ^ (n + 2)) := fun n =>
    Summable.of_nonneg_of_le (fun i => by positivity) (fun i => hbound_i n i)
      (hs.mul_left (‖z‖ ^ (n + 1) * M ^ n))
  have hgeom : Summable (fun n : ℕ => ‖z‖ ^ (n + 1) * M ^ n) := by
    have heq : (fun n : ℕ => ‖z‖ ^ (n + 1) * M ^ n) = fun n => ‖z‖ * (‖z‖ * M) ^ n := by
      funext n; rw [mul_pow]; ring
    rw [heq]; exact (summable_geometric_of_lt_one (by positivity) hzM).mul_left _
  have hnorm_summable : Summable (fun p : ℕ × ι => ‖z‖ ^ (p.1 + 1) * ‖g p.2‖ ^ (p.1 + 2)) := by
    rw [summable_prod_of_nonneg (fun p => by positivity)]
    refine ⟨hsum_i, ?_⟩
    apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (hgeom.mul_right (∑' i, ‖g i‖ ^ 2))
    conv_rhs => rw [← tsum_mul_left]
    exact Summable.tsum_mono (hsum_i n) (hs.mul_left _) (fun i => hbound_i n i)
  have huncurry :
      Summable (Function.uncurry (fun (n : ℕ) (i : ι) => z ^ (n + 1) * g i ^ (n + 2))) := by
    apply Summable.of_norm
    have heq :
        (fun p : ℕ × ι => ‖Function.uncurry (fun (n : ℕ) (i : ι) => z ^ (n + 1) * g i ^ (n + 2)) p‖)
          = fun p : ℕ × ι => ‖z‖ ^ (p.1 + 1) * ‖g p.2‖ ^ (p.1 + 2) := by
      funext p; simp [Function.uncurry, norm_pow]
    rw [heq]; exact hnorm_summable
  rw [resolventTrace]
  have hstep : ∀ n : ℕ, z ^ (n + 1) * (∑' i, hsPow (diagMul g) (n + 1) (i, i))
      = ∑' i, z ^ (n + 1) * g i ^ (n + 2) := by
    intro n
    rw [hsPow_diagMul, ← tsum_mul_left]
    apply tsum_congr; intro i; simp [diagMul]
  rw [tsum_congr hstep, ← Summable.tsum_comm huncurry]
  apply tsum_congr; intro i
  exact tsum_geom_resolvent z (g i) (hzgi i)

/-- **The Plemelj identity for the infinite (countable-rank) diagonal operator:**
`logDeriv det₂(1 − z·diagMul g) = −∑ᵢ z·(g i)²/(1 − z·g i)`, the negative of the countable resolvent
trace, for any summable-energy diagonal `g` and `z` on the disk `|z|·‖diagMul g‖_HS < 1`.  This is
`logDeriv Λ = −tr` at the level of an operator with infinitely many eigenvalues — past finite rank. -/
theorem logDeriv_fredholmDet_diagMul_infinite (g : ι → ℂ) (hs : Summable (fun i => ‖g i‖ ^ 2))
    (r : ℝ) (hr : r * hsNorm (diagMul g) < 1) (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) :
    logDeriv (fun w => fredholmDet (diagMul g) w) z = -∑' i, z * g i ^ 2 / (1 - z * g i) := by
  rw [logDeriv_fredholmDet (isHS_diagMul_infinite g hs) r hr z hz,
    resolventTrace_diagMul_infinite g hs r hr z hz]

end HilbertSchmidt
