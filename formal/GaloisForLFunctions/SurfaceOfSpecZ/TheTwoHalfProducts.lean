import GaloisForLFunctions.SurfaceOfSpecZ.TheFrobeniusZonotopeSurface
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheWeilPrimeKernelIsARenormalizedTorsionEnergy

/-!
# The two half-products: where the off-diagonal of Weil's form lives

`Spec ℤ ×_{𝔽₁} Spec ℤ` is not constructed, but the two products in which one or both factors are
replaced by the `𝔽₁`-model `ℙ¹_{𝔽₁}` exist:

* `ℙ¹_{𝔽₁} ×_{𝔽₁} ℙ¹_{𝔽₁} = ℙ¹ × ℙ¹`, with the power-map graphs `Γ_n`, meeting in `m + n` points
  (`TheFrobeniusZonotopeSurface`);
* `Spec ℤ ×_{𝔽₁} ℙ¹_{𝔽₁} = ℙ¹_ℤ`, the arithmetic surface on which the Galois orbits `O_n` of the
  primitive roots of unity (the `𝔽₁`-points) meet over the primes, `I(m, mt) = φ(m) Λ(t)`
  (`ArithmeticEffectivityTheory.orbitIntersection_hecke`).

Place atoms at `log m` and `log n`, `m ≠ n`. Weil's distribution between them is the pole term minus
the archimedean Lévy density minus the prime kernel (`weilDeltaKernel`). Define the intersection of the
Frobenius graphs of `Spec ℤ` as the bidegree pairing minus Weil's defect,
`Γ_m · Γ_n = (m + n) − √(mn) W(m, n)` (`frobeniusIntersection`), as on `C × C`. Then
(`frobeniusIntersection_eq`)

  `Γ_m · Γ_n = min(m, n) / (1 − (min/max)²) + G(m, n) · I(m, n)`,

with `G(m, n) = gcd/φ(gcd)`: the archimedean place contributes one `𝔽₁`-cusp with its tower of even
jets, `min · (1 + r^{−2} + r^{−4} + ⋯)`, `r = max/min` (the cusp is the term `min(m, n)` of the zonotope
surface, the jets are the trivial zeros), and the primes contribute the gcd-twisted intersection of
torsion orbits on `ℙ¹_ℤ`. Every local index is nonnegative, so distinct Frobenius graphs meet at least
in the cusp, `Γ_m · Γ_n ≥ min(m, n)` (`min_le_frobeniusIntersection`), while on `ℙ¹ × ℙ¹` they meet in
`min(m, n)(r + 1)`.

So the whole off-diagonal of Weil's form is assembled from the two existing half-products; what no
half-product supplies is the diagonal, the self-intersection `Γ_n² = n(2 − 2g)` with `g = ∞`, which
must be renormalized, and the sign of Weil's form lives in that renormalization.

**The toy door.** On the zonotope surface the defect is exactly quadratic and integral, so the count
door of `CountingHolography.TheTateLimitOfACount` opens with the count itself
(`zonotope_tateLimit`).
-/

open Finset Filter Topology
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticEffectivityTheory

/-- Weil's distribution between atoms at `log m` and `log n`, `m ≠ n`: pole minus archimedean Lévy
density minus prime kernel. -/
def weilDeltaKernel (m n : ℕ) : ℝ :=
  2 * Real.cosh ((Real.log m - Real.log n) / 2) -
    RHTower.archLevyDensity |Real.log m - Real.log n| - weilPrimeKernel m n

/-- The intersection of the Frobenius graphs `Γ_m, Γ_n` of `Spec ℤ`: bidegree pairing minus Weil's
defect. -/
def frobeniusIntersection (m n : ℕ) : ℝ := (m + n) - Real.sqrt ((m : ℝ) * n) * weilDeltaKernel m n

/-- The pole term is the bidegree pairing: `√(mn) · 2 cosh((log m − log n)/2) = m + n`. -/
theorem sqrt_mul_two_cosh {m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    Real.sqrt (m * n) * (2 * Real.cosh ((Real.log m - Real.log n) / 2)) = m + n := by
  have hx : ∀ y : ℝ, 0 < y → Real.exp (Real.log y / 2) = Real.sqrt y := fun y hy => by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy]; ring_nf
  rw [Real.cosh_eq, show (Real.log m - Real.log n) / 2 = Real.log (m / n) / 2 by
      rw [Real.log_div hm.ne' hn.ne'], show -(Real.log (m / n) / 2) = Real.log (n / m) / 2 by
      rw [Real.log_div hm.ne' hn.ne', Real.log_div hn.ne' hm.ne']; ring,
    hx _ (div_pos hm hn), hx _ (div_pos hn hm)]
  rw [show 2 * ((Real.sqrt (m / n) + Real.sqrt (n / m)) / 2) =
      Real.sqrt (m / n) + Real.sqrt (n / m) by ring, mul_add,
    ← Real.sqrt_mul (mul_pos hm hn).le, ← Real.sqrt_mul (mul_pos hm hn).le,
    show m * n * (m / n) = m * m by field_simp, show m * n * (n / m) = n * n by field_simp,
    Real.sqrt_mul_self hm.le, Real.sqrt_mul_self hn.le]

/-- `e^{−2|log m − log n|} = (min/max)²`. -/
theorem exp_neg_two_abs_log_sub {m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    Real.exp (-(2 * |Real.log m - Real.log n|)) = (min m n / max m n) ^ 2 := by
  have hsq : ∀ y : ℝ, 0 < y → Real.exp (2 * Real.log y) = y ^ 2 := fun y hy => by
    rw [two_mul, Real.exp_add, Real.exp_log hy, sq]
  rcases le_total m n with h | h
  · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith [Real.log_le_log hm h]),
      show -(2 * -(Real.log m - Real.log n)) = 2 * Real.log (m / n) by
        rw [Real.log_div hm.ne' hn.ne']; ring, hsq _ (div_pos hm hn)]
  · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith [Real.log_le_log hn h]),
      show -(2 * (Real.log m - Real.log n)) = 2 * Real.log (n / m) by
        rw [Real.log_div hn.ne' hm.ne']; ring, hsq _ (div_pos hn hm)]

/-- The archimedean term is the cusp with its jets: `√(mn) · ω(|log m − log n|) = min/(1 − (min/max)²)`. -/
theorem sqrt_mul_archLevyDensity {m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    Real.sqrt (m * n) * RHTower.archLevyDensity |Real.log m - Real.log n| =
      min m n / (1 - (min m n / max m n) ^ 2) := by
  unfold RHTower.archLevyDensity
  rw [show -2 * |Real.log m - Real.log n| = -(2 * |Real.log m - Real.log n|) by ring,
    exp_neg_two_abs_log_sub hm hn, ← mul_div_assoc, min_eq_sqrt_mul_exp hm hn]

/-- The prime term is the gcd-twisted intersection of torsion orbits on `ℙ¹_ℤ`. -/
theorem sqrt_mul_weilPrimeKernel {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    Real.sqrt ((m : ℝ) * n) * weilPrimeKernel m n = gcdTwist m n * orbitIntersection m n := by
  have hpos : ∀ a b : ℕ, 0 < a → 0 < b → (0 : ℝ) < Real.sqrt ((a : ℝ) * b) := fun a b ha hb =>
    Real.sqrt_pos.mpr (by positivity)
  by_cases h1 : m ∣ n
  · obtain ⟨t, rfl⟩ := h1
    have ht : 1 < t := by
      rcases Nat.lt_or_ge t 2 with h | h
      · interval_cases t
        · simp at hn
        · simp at hmn
      · omega
    have hk := gcdTwist_mul_orbitIntersection_hecke hm ht
    have hwk : weilPrimeKernel m (m * t) = Λ t / Real.sqrt t := by
      rw [weilPrimeKernel, if_pos ⟨dvd_mul_right m t, hmn⟩, Nat.mul_div_cancel_left t hm]
    rw [hwk, ← hk, mul_div_cancel₀ _ (hpos _ _ hm hn).ne']
  · by_cases h2 : n ∣ m
    · obtain ⟨t, rfl⟩ := h2
      have ht : 1 < t := by
        rcases Nat.lt_or_ge t 2 with h | h
        · interval_cases t
          · simp at hm
          · simp at hmn
        · omega
      have hk := gcdTwist_mul_orbitIntersection_hecke hn ht
      have hwk : weilPrimeKernel (n * t) n = Λ t / Real.sqrt t := by
        rw [weilPrimeKernel, if_neg (fun h => h1 h.1), if_pos ⟨dvd_mul_right n t, Ne.symm hmn⟩,
          Nat.mul_div_cancel_left t hn]
      rw [hwk, ← hk, gcdTwist_comm, orbitIntersection_comm, mul_comm ((n * t : ℕ) : ℝ),
        mul_div_cancel₀ _ (hpos _ _ hn hm).ne']
    · have hw : weilPrimeKernel m n = 0 := by
        rw [weilPrimeKernel, if_neg (fun h => h1 h.1), if_neg (fun h => h2 h.1)]
      rw [hw, orbitIntersection_eq hm hn hmn, if_neg h2, if_neg h1]
      ring

/-- **The two half-products.** Distinct Frobenius graphs of `Spec ℤ` meet in one `𝔽₁`-cusp with its
tower of even jets (the archimedean place) plus the gcd-twisted torsion intersection on `ℙ¹_ℤ` (the
primes). -/
theorem frobeniusIntersection_eq {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    frobeniusIntersection m n =
      min (m : ℝ) n / (1 - (min (m : ℝ) n / max (m : ℝ) n) ^ 2) +
        gcdTwist m n * orbitIntersection m n := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc := sqrt_mul_two_cosh hm' hn'
  have ha := sqrt_mul_archLevyDensity hm' hn'
  have hp := sqrt_mul_weilPrimeKernel hm hn hmn
  rw [frobeniusIntersection, weilDeltaKernel, mul_sub, mul_sub, hc, ha, hp]
  ring

/-- `0 ≤ I(m, n)`: torsion orbits meet nonnegatively. -/
theorem orbitIntersection_nonneg_of_ne {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    0 ≤ orbitIntersection m n := by
  rw [orbitIntersection_eq hm hn hmn]
  split_ifs <;> first
    | exact mul_nonneg (Nat.cast_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
    | exact le_rfl

/-- **Distinct Frobenius graphs of `Spec ℤ` meet at least in the `𝔽₁`-cusp.** -/
theorem min_le_frobeniusIntersection {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    min (m : ℝ) n ≤ frobeniusIntersection m n := by
  rw [frobeniusIntersection_eq hm hn hmn]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmn' : (m : ℝ) ≠ n := by exact_mod_cast hmn
  have hmin : 0 < min (m : ℝ) n := lt_min hm' hn'
  have hlt : min (m : ℝ) n < max (m : ℝ) n := min_lt_max.mpr hmn'
  have hr0 : 0 ≤ (min (m : ℝ) n / max (m : ℝ) n) ^ 2 := sq_nonneg _
  have hr1 : (min (m : ℝ) n / max (m : ℝ) n) ^ 2 < 1 := by
    rw [div_pow, div_lt_one (by nlinarith)]
    exact pow_lt_pow_left₀ hlt hmin.le two_ne_zero
  have hjet : min (m : ℝ) n ≤ min (m : ℝ) n / (1 - (min (m : ℝ) n / max (m : ℝ) n) ^ 2) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [mul_nonneg hmin.le hr0]
  have htw : 0 ≤ gcdTwist m n * orbitIntersection m n := by
    refine mul_nonneg ?_ (orbitIntersection_nonneg_of_ne hm hn hmn)
    rw [gcdTwist_eq]; positivity
  linarith

/-! ### The toy door -/

/-- **The count door of the zonotope surface.** The cusp form is an `ℕ`-valued count that is exactly
quadratic along integer rays, so its Tate limit is itself: half the Castelnuovo–Severi defect. -/
theorem zonotope_tateLimit (S : Finset ℕ) (a : ℕ → ℤ) :
    ∃ K : (ℕ → ℤ) → ℕ, Tendsto (fun m : ℕ => (K (m • a) : ℝ) / (m : ℝ) ^ 2) atTop
      (𝓝 ((zonotopeDefect S a : ℝ) / 2)) := by
  refine ⟨fun b => (cuspForm S b).toNat, ?_⟩
  have hq : ∀ m : ℕ, ((cuspForm S (m • a)).toNat : ℝ) = (m : ℝ) ^ 2 * cuspForm S a := by
    intro m
    have hc : cuspForm S (m • a) = (m : ℤ) ^ 2 * cuspForm S a := by
      unfold cuspForm
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      simp only [Pi.smul_apply, nsmul_eq_mul]
      ring
    rw [show ((cuspForm S (m • a)).toNat : ℝ) = ((cuspForm S (m • a) : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg (cuspForm_nonneg S _), hc]
    push_cast
    ring
  have hd : (zonotopeDefect S a : ℝ) / 2 = cuspForm S a := by
    rw [zonotopeDefect, torusForm_eq]; push_cast; ring
  rw [hd]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm' : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  rw [hq, mul_div_cancel_left₀ _ hm'.ne']

end GaloisForLFunctions.SurfaceOfSpecZ

#print axioms GaloisForLFunctions.SurfaceOfSpecZ.frobeniusIntersection_eq
#print axioms GaloisForLFunctions.SurfaceOfSpecZ.min_le_frobeniusIntersection
#print axioms GaloisForLFunctions.SurfaceOfSpecZ.zonotope_tateLimit
