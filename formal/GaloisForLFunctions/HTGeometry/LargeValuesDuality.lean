import Mathlib
import GaloisForLFunctions.HTGeometry.SeparatedOffDiagonalBound
import GaloisForLFunctions.HTGeometry.DifferenceEnergyBound

/-!
# The duality step of a large-values inequality

Gallagher's route to a large-values bound differentiates, and pays `log N`.  The duality route does
not.  Writing `b_r = ∑_n a_n M(r,n)` for the sampled values of a Dirichlet polynomial,

```text
∑_r |b_r|²  =  ∑_n a_n · ( ∑_r conj(b_r) M(r,n) )
            ≤  (∑_n |a_n|²)^{1/2} · (∑_n |∑_r conj(b_r) M(r,n)|²)^{1/2}
```

by Cauchy–Schwarz, and the dual sum expands into a diagonal term plus the sampling off-diagonal
handled by `SeparatedOffDiagonalBound`.  Squaring and cancelling one factor of `∑_r|b_r|²` gives

```text
∑_r |b_r|²  ≤  (diagonal + off-diagonal) · ∑_n |a_n|² ,
```

with no derivative anywhere.  This module proves the duality step itself; the two structural inputs —
the exponential-sum bound feeding the off-diagonal and the row-sum bound of the sampling set — enter
downstream as explicit hypotheses.
-/

open Finset

namespace GaloisForLFunctions

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The duality step.**  If the sampled values are `b r = ∑ n, a n * M r n` and the dual sum is
bounded by `C` times the sampled energy, then the sampled energy is at most `C` times the coefficient
energy.  Cauchy–Schwarz, then cancel one factor. -/
theorem sampled_energy_le_of_dual_bound {M : ι → κ → ℂ} {a : κ → ℂ} {b : ι → ℂ} {C : ℝ}
    (hb : ∀ r, b r = ∑ n, a n * M r n) (hC : 0 ≤ C)
    (hdual : ∑ n, ‖∑ r, (starRingEnd ℂ) (b r) * M r n‖ ^ 2
      ≤ C * ∑ r, ‖b r‖ ^ 2) :
    ∑ r, ‖b r‖ ^ 2 ≤ C * ∑ n, ‖a n‖ ^ 2 := by
  classical
  set E : ℝ := ∑ r, ‖b r‖ ^ 2 with hE
  set A : ℝ := ∑ n, ‖a n‖ ^ 2 with hA
  have hEnn : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hAnn : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- the pairing identity
  have hconj : ∀ z : ℂ, (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hpair : (E : ℂ) = ∑ n, a n * ∑ r, (starRingEnd ℂ) (b r) * M r n := by
    have hswap : ∑ n, a n * ∑ r, (starRingEnd ℂ) (b r) * M r n
        = ∑ r, (starRingEnd ℂ) (b r) * ∑ n, a n * M r n := by
      calc ∑ n, a n * ∑ r, (starRingEnd ℂ) (b r) * M r n
          = ∑ n, ∑ r, a n * ((starRingEnd ℂ) (b r) * M r n) := by
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [Finset.mul_sum]
        _ = ∑ r, ∑ n, a n * ((starRingEnd ℂ) (b r) * M r n) := Finset.sum_comm
        _ = ∑ r, (starRingEnd ℂ) (b r) * ∑ n, a n * M r n := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun n _ => ?_
            ring
    rw [hswap]
    have : ∀ r : ι, (starRingEnd ℂ) (b r) * ∑ n, a n * M r n
        = ((‖b r‖ ^ 2 : ℝ) : ℂ) := by
      intro r
      rw [← hb r, hconj]
    rw [Finset.sum_congr rfl fun r _ => this r, hE]
    push_cast
    rfl
  -- Cauchy–Schwarz on the pairing
  have hcs : E ^ 2 ≤ A * (∑ n, ‖∑ r, (starRingEnd ℂ) (b r) * M r n‖ ^ 2) := by
    have habs : E = ‖(E : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hEnn]
    have hle : ‖(E : ℂ)‖ ≤ ∑ n, ‖a n‖ * ‖∑ r, (starRingEnd ℂ) (b r) * M r n‖ := by
      rw [hpair]
      refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
      exact Finset.sum_congr rfl fun n _ => norm_mul _ _
    have hcs' : (∑ n, ‖a n‖ * ‖∑ r, (starRingEnd ℂ) (b r) * M r n‖) ^ 2
        ≤ A * ∑ n, ‖∑ r, (starRingEnd ℂ) (b r) * M r n‖ ^ 2 := by
      simpa [hA] using
        Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset κ)
          (fun n => ‖a n‖) (fun n => ‖∑ r, (starRingEnd ℂ) (b r) * M r n‖)
    have hEle : E ≤ ∑ n, ‖a n‖ * ‖∑ r, (starRingEnd ℂ) (b r) * M r n‖ := habs ▸ hle
    have hnn : 0 ≤ ∑ n, ‖a n‖ * ‖∑ r, (starRingEnd ℂ) (b r) * M r n‖ :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith [hEle, hnn, hcs']
  -- combine with the dual bound and cancel
  rcases eq_or_lt_of_le hEnn with hzero | hpos
  · rw [← hzero]; positivity
  · have h1 : E ^ 2 ≤ A * (C * E) := le_trans hcs (by nlinarith [hdual, hAnn])
    nlinarith [h1, hpos]


/-! ### The dual sum expands into the sampling Gram -/

/-- **Expansion of the dual sum.**  The dual energy is the sampling Gram form: diagonal plus
off-diagonal, with entries the correlation sums `∑ₙ M(r,n)·conj M(s,n)`. -/
theorem dual_sum_expand {M : ι → κ → ℂ} (c : ι → ℂ) :
    ∑ n, ‖∑ r, c r * M r n‖ ^ 2
      = ∑ r, ∑ s, (c r * (starRingEnd ℂ) (c s) *
          ∑ n, M r n * (starRingEnd ℂ) (M s n)).re := by
  classical
  have hstep : ∀ n : κ, ‖∑ r, c r * M r n‖ ^ 2
      = ∑ r, ∑ s, (c r * (starRingEnd ℂ) (c s) * (M r n * (starRingEnd ℂ) (M s n))).re := by
    intro n
    have hz : ‖∑ r, c r * M r n‖ ^ 2
        = ((∑ r, c r * M r n) * (starRingEnd ℂ) (∑ r, c r * M r n)).re := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      norm_cast
    rw [hz, map_sum, Finset.sum_mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    rw [map_mul]
    ring
  rw [Finset.sum_congr rfl fun n _ => hstep n]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Complex.re_sum, ← Finset.mul_sum]

omit [Fintype ι] in
/-- Each Gram entry is dominated by the moduli times the correlation bound. -/
theorem gram_entry_le {M : ι → κ → ℂ} (c : ι → ℂ) (r s : ι) {G : ℝ}
    (hG : ‖∑ n, M r n * (starRingEnd ℂ) (M s n)‖ ≤ G) :
    (c r * (starRingEnd ℂ) (c s) * ∑ n, M r n * (starRingEnd ℂ) (M s n)).re
      ≤ ‖c r‖ * ‖c s‖ * G := by
  have h1 := Complex.re_le_norm
    (c r * (starRingEnd ℂ) (c s) * ∑ n, M r n * (starRingEnd ℂ) (M s n))
  have h2 : ‖c r * (starRingEnd ℂ) (c s) * ∑ n, M r n * (starRingEnd ℂ) (M s n)‖
      = ‖c r‖ * ‖c s‖ * ‖∑ n, M r n * (starRingEnd ℂ) (M s n)‖ := by
    rw [norm_mul, norm_mul, RCLike.norm_conj]
  refine le_trans h1 (le_trans (le_of_eq h2) ?_)
  exact mul_le_mul_of_nonneg_left hG (by positivity)



/-! ### The assembled large-values bound -/

/-- **The large-values inequality by duality.**  If the sampled values are `b r = ∑ₙ aₙ M(r,n)`, the
diagonal correlation is at most `D`, the off-diagonal correlations are at most `M₀` times the
reciprocal separation, and the sampling row sums are at most `H`, then

```text
∑ᵣ ‖b r‖²  ≤  (D + M₀·H) · ∑ₙ ‖aₙ‖² .
```

No derivative of the polynomial appears, so no factor `log N` is paid; the only logarithm is the one
inside `H`, which for a `δ`-separated sampling set is `O(log R / δ)`. -/
theorem sampled_energy_le_of_correlation_bounds [DecidableEq ι]
    {M : ι → κ → ℂ} {a : κ → ℂ} {b : ι → ℂ} {t : ι → ℝ} {D M₀ H : ℝ}
    (hb : ∀ r, b r = ∑ n, a n * M r n) (hD : 0 ≤ D) (hM₀ : 0 ≤ M₀) (hH : 0 ≤ H)
    (hdiag : ∀ r, ‖∑ n, M r n * (starRingEnd ℂ) (M r n)‖ ≤ D)
    (hoff : ∀ r s, r ≠ s → ‖∑ n, M r n * (starRingEnd ℂ) (M s n)‖ ≤ M₀ * sepKernel t r s)
    (hrow : ∀ r, ∑ s, sepKernel t r s ≤ H) :
    ∑ r, ‖b r‖ ^ 2 ≤ (D + M₀ * H) * ∑ n, ‖a n‖ ^ 2 := by
  classical
  refine sampled_energy_le_of_dual_bound hb (by positivity) ?_
  set c : ι → ℂ := fun r => (starRingEnd ℂ) (b r) with hc
  have hcn : ∀ r, ‖c r‖ = ‖b r‖ := fun r => by rw [hc]; exact RCLike.norm_conj _
  rw [dual_sum_expand (M := M) c]
  -- termwise domination
  have hterm : ∀ r s : ι,
      (c r * (starRingEnd ℂ) (c s) * ∑ n, M r n * (starRingEnd ℂ) (M s n)).re
        ≤ (if r = s then D * ‖b r‖ ^ 2 else 0)
          + M₀ * (‖b r‖ * ‖b s‖ * sepKernel t r s) := by
    intro r s
    by_cases hrs : r = s
    · subst hrs
      have hker : sepKernel t r r = 0 := by unfold sepKernel; simp
      have hbound := gram_entry_le (M := M) c r r (hdiag r)
      rw [hcn r] at hbound
      rw [if_pos rfl, hker]
      simp only [mul_zero]
      nlinarith [hbound]
    · have hbound := gram_entry_le (M := M) c r s (hoff r s hrs)
      rw [if_neg hrs]
      have hker : 0 ≤ sepKernel t r s := sepKernel_nonneg t r s
      calc (c r * (starRingEnd ℂ) (c s) * ∑ n, M r n * (starRingEnd ℂ) (M s n)).re
          ≤ ‖c r‖ * ‖c s‖ * (M₀ * sepKernel t r s) := hbound
        _ = 0 + M₀ * (‖b r‖ * ‖b s‖ * sepKernel t r s) := by
            rw [hcn r, hcn s]; ring
  have hsum : ∑ r, ∑ s, (c r * (starRingEnd ℂ) (c s) *
        ∑ n, M r n * (starRingEnd ℂ) (M s n)).re
      ≤ ∑ r, ∑ s, ((if r = s then D * ‖b r‖ ^ 2 else 0)
          + M₀ * (‖b r‖ * ‖b s‖ * sepKernel t r s)) :=
    Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => hterm r s
  have hdiagSum : ∑ r, ∑ s, (if r = s then D * ‖b r‖ ^ 2 else 0)
      = D * ∑ r, ‖b r‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp
  have hoffSum : ∑ r, ∑ s, M₀ * (‖b r‖ * ‖b s‖ * sepKernel t r s)
      ≤ M₀ * (H * ∑ r, ‖b r‖ ^ 2) := by
    have hbase := sampling_offDiagonal_le (t := t) (b := fun r => ‖b r‖) hrow
    have habs : ∀ r, |‖b r‖| = ‖b r‖ := fun r => abs_of_nonneg (norm_nonneg _)
    simp only [habs] at hbase
    calc ∑ r, ∑ s, M₀ * (‖b r‖ * ‖b s‖ * sepKernel t r s)
        = M₀ * ∑ r, ∑ s, ‖b r‖ * ‖b s‖ * sepKernel t r s := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.mul_sum]
      _ ≤ M₀ * (H * ∑ r, ‖b r‖ ^ 2) := mul_le_mul_of_nonneg_left hbase hM₀
  have hsplit : ∑ r, ∑ s, ((if r = s then D * ‖b r‖ ^ 2 else 0)
        + M₀ * (‖b r‖ * ‖b s‖ * sepKernel t r s))
      = (∑ r, ∑ s, (if r = s then D * ‖b r‖ ^ 2 else 0))
        + ∑ r, ∑ s, M₀ * (‖b r‖ * ‖b s‖ * sepKernel t r s) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_add_distrib]
  rw [hsplit, hdiagSum] at hsum
  nlinarith [hsum, hoffSum]



/-! ### The dual bound through the additive energy

The row-sum route bounds the off-diagonal by `sup × count`.  Routing it instead through the
difference multiset replaces that by `√(additive energy) × ‖correlation‖_{ℓ²}`, which for an
unstructured sampling set is smaller by a *power* of the count, not a logarithm. -/

/-- **The dual sum through the additive energy.**  With bounded sampled values, correlations
controlled by a function of the difference, and the difference multiset carrying energy `E`, the dual
energy is at most `B²·√E·‖f‖_{ℓ²}`. -/
theorem dual_sum_le_via_energy {Dt : Type*} [DecidableEq Dt]
    {M : ι → κ → ℂ} {c : ι → ℂ} {B : ℝ} {d : ι → ι → Dt} {f : Dt → ℝ} {S : Finset Dt}
    (hB : ∀ r, ‖c r‖ ≤ B) (hB0 : 0 ≤ B) (hf : ∀ x, 0 ≤ f x)
    (hmem : ∀ p : ι × ι, d p.1 p.2 ∈ S)
    (hcorr : ∀ r s, ‖∑ n, M r n * (starRingEnd ℂ) (M s n)‖ ≤ f (d r s)) :
    ∑ n, ‖∑ r, c r * M r n‖ ^ 2
      ≤ B ^ 2 * (Real.sqrt (∑ x ∈ S, (diffMult d x : ℝ) ^ 2)
          * Real.sqrt (∑ x ∈ S, f x ^ 2)) := by
  classical
  rw [dual_sum_expand (M := M) c]
  -- each Gram entry is at most the weights times the correlation bound
  have hentry : ∀ p : ι × ι,
      (c p.1 * (starRingEnd ℂ) (c p.2) * ∑ n, M p.1 n * (starRingEnd ℂ) (M p.2 n)).re
        ≤ ‖c p.1‖ * ‖c p.2‖ * f (d p.1 p.2) :=
    fun p => gram_entry_le (M := M) c p.1 p.2 (hcorr p.1 p.2)
  have hflat : ∑ r, ∑ s, (c r * (starRingEnd ℂ) (c s) *
        ∑ n, M r n * (starRingEnd ℂ) (M s n)).re
      = ∑ p : ι × ι, (c p.1 * (starRingEnd ℂ) (c p.2) *
        ∑ n, M p.1 n * (starRingEnd ℂ) (M p.2 n)).re := by
    rw [← Finset.sum_product', Finset.univ_product_univ]
  rw [hflat]
  have habs : ∀ r, |‖c r‖| = ‖c r‖ := fun r => abs_of_nonneg (norm_nonneg _)
  calc ∑ p : ι × ι, (c p.1 * (starRingEnd ℂ) (c p.2) *
          ∑ n, M p.1 n * (starRingEnd ℂ) (M p.2 n)).re
      ≤ ∑ p : ι × ι, ‖c p.1‖ * ‖c p.2‖ * f (d p.1 p.2) :=
        Finset.sum_le_sum fun p _ => hentry p
    _ = ∑ p : ι × ι, |‖c p.1‖| * |‖c p.2‖| * f (d p.1 p.2) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [habs p.1, habs p.2]
    _ ≤ B ^ 2 * ∑ p : ι × ι, f (d p.1 p.2) :=
        weighted_pairs_le_of_bounded (b := fun r => ‖c r‖) d f
          (fun r => by rw [habs r]; exact hB r) hB0 hf
    _ ≤ B ^ 2 * (Real.sqrt (∑ x ∈ S, (diffMult d x : ℝ) ^ 2)
          * Real.sqrt (∑ x ∈ S, f x ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (sum_pairs_le_sqrt_energy d f S hmem) (by positivity)


end GaloisForLFunctions
