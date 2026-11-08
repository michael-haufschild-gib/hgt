import GaloisForLFunctions.SurfaceOfSpecZ.ThePointCountOfSpecZ

/-!
# The torsion energy against the jets

`ArithmeticEffectivityTheory` writes Weil's prime kernel as minus the Abel limit of the gcd-twisted
torsion energy `T_r(m, n)/√(mn)` of `ℙ¹_ℤ`, a positive kernel for every `r < 1`. The rest of Weil's
off-diagonal kernel is the **archimedean compensation**: the pole plane minus the archimedean Lévy
density (`archCompensation`). So, off the diagonal (`tendsto_compensation_add_twistedEnergy`),

  `W(m, n) = lim_{r → 1} ( C_∞(m, n) + T̃_r(m, n) )`,   `Σ x_m x_n T̃_r(m, n) ≥ 0`
  (`sum_sum_twistedEnergy_nonneg`):

Weil's form is the archimedean compensation plus a limit of positive torsion energies, up to the
renormalization of the diagonal. In the Frobenius normalization the compensation is the pole plane
minus the archimedean place, `√(mn) C_∞(m, n) = (m + n) − min/(1 − (min/max)²)`
(`sqrt_mul_archCompensation`): the bidegree pairing minus one `𝔽₁`-cusp and its tower of even jets.
It is positive for distant orders and negative for close ones: `√2 C_∞(1, 2) = 5/3`,
`√6 C_∞(2, 3) = 7/5`, `√20 C_∞(4, 5) = −19/9` (`archCompensation_one_two`,
`archCompensation_two_three`, `archCompensation_four_five`).

This is the precise content of the Gamma/pole compensation asked for by the renormalized torsion forms
at the critical weight: it is `C_∞`, it is not an Arakelov metric on `ℙ¹_ℤ`
(`not_exists_arakelov_frobeniusIntersection`), and its negative part is the archimedean place.
-/

open Finset Filter Topology
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticEffectivityTheory

/-- The archimedean compensation: pole term minus archimedean Lévy density. -/
def archCompensation (m n : ℕ) : ℝ :=
  2 * Real.cosh ((Real.log m - Real.log n) / 2) - RHTower.archLevyDensity |Real.log m - Real.log n|

theorem weilDeltaKernel_eq (m n : ℕ) :
    weilDeltaKernel m n = archCompensation m n - weilPrimeKernel m n := by
  rw [weilDeltaKernel, archCompensation]

/-- **Weil's kernel is the compensation plus the Abel limit of the torsion energy.** -/
theorem tendsto_compensation_add_twistedEnergy {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    Tendsto (fun r : ℝ => archCompensation m n + twistedEnergy r m n) (𝓝 1)
      (𝓝 (weilDeltaKernel m n)) := by
  rw [weilDeltaKernel_eq, sub_eq_add_neg]
  exact tendsto_const_nhds.add (tendsto_twistedEnergy_of_ne hm hn hmn)

/-- **The twisted torsion energy is a positive kernel** for `0 ≤ r < 1`. -/
theorem sum_sum_twistedEnergy_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {S : Finset ℕ}
    (hS : ∀ n ∈ S, 0 < n) (x : ℕ → ℝ) :
    0 ≤ ∑ m ∈ S, ∑ n ∈ S, x m * x n * twistedEnergy r m n := by
  have h := sum_sum_gcdTwist_torsionEnergy_nonneg hr0 hr1 hS (fun k => x k / Real.sqrt k)
  refine le_of_le_of_eq h (sum_congr rfl fun m hm => sum_congr rfl fun n hn => ?_)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hS m hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hS n hn
  rw [twistedEnergy, Real.sqrt_mul hm'.le]
  field_simp

/-- **The compensation in the Frobenius normalization**: the pole plane minus the archimedean place. -/
theorem sqrt_mul_archCompensation {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Real.sqrt ((m : ℝ) * n) * archCompensation m n =
      (m + n) - min (m : ℝ) n / (1 - (min (m : ℝ) n / max (m : ℝ) n) ^ 2) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [archCompensation, mul_sub, sqrt_mul_two_cosh hm' hn', sqrt_mul_archLevyDensity hm' hn']

theorem archCompensation_one_two :
    Real.sqrt ((1 : ℕ) * (2 : ℕ) : ℝ) * archCompensation 1 2 = 5 / 3 := by
  have h := sqrt_mul_archCompensation (m := 1) (n := 2) one_pos two_pos
  push_cast at h ⊢
  rw [h]; norm_num [min_def, max_def]

theorem archCompensation_two_three :
    Real.sqrt ((2 : ℕ) * (3 : ℕ) : ℝ) * archCompensation 2 3 = 7 / 5 := by
  have h := sqrt_mul_archCompensation (m := 2) (n := 3) two_pos (by norm_num)
  push_cast at h ⊢
  rw [h]; norm_num [min_def, max_def]

theorem archCompensation_four_five :
    Real.sqrt ((4 : ℕ) * (5 : ℕ) : ℝ) * archCompensation 4 5 = -19 / 9 := by
  have h := sqrt_mul_archCompensation (m := 4) (n := 5) (by norm_num) (by norm_num)
  push_cast at h ⊢
  rw [h]; norm_num [min_def, max_def]

end GaloisForLFunctions.SurfaceOfSpecZ
