import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarParitySourceProfile

/-!
# Two-ended rank of the actual prime–Gamma pole source

The two reflected physical source profiles have independent logarithmic endpoint
coefficients. Every nonzero real combination diverges, with one sign, at one of
the two aperture endpoints. In particular, bounded arithmetic corrections cannot
cancel both boundary channels. This does not determine a constrained ground state.
-/

open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace RHTower

/-- Real even/odd coordinates of the two physical source profiles. -/
def ccmPolarSourceParityCombination (a : SuzukiPositiveAperture) (c d x : ℝ) : ℝ :=
  c * (ccmPolarParityBoundaryProfile a 1 x).re +
    d * (ccmPolarParityBoundaryProfile a (-1) x).re

theorem ccmPolarSourceParityCombination_reflect (a : SuzukiPositiveAperture) (c d x : ℝ) :
    ccmPolarSourceParityCombination a c d (-x) =
      ccmPolarSourceParityCombination a c (-d) x := by
  unfold ccmPolarSourceParityCombination ccmPolarParityBoundaryProfile
  simp only [neg_neg, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, one_mul, neg_one_mul]
  ring

private theorem sourceCombination_right_of_pos (a : SuzukiPositiveAperture) (c d : ℝ)
    (hk : 0 < c * (Real.exp (a.1 / 2) + Real.exp (-a.1 / 2)) +
      d * (Real.exp (a.1 / 2) - Real.exp (-a.1 / 2))) :
    Tendsto (ccmPolarSourceParityCombination a c d) (𝓝[<] a.1) atTop := by
  let M := Real.exp (a.1 / 2) *
    (2 * (Chebyshev.psi (Real.exp (2 * a.1)) + Real.exp (2 * a.1) +
      (Real.log 4 + 5)) + Real.log 2)
  let k : ℝ → ℝ := fun x =>
    c * (Real.exp (x / 2) + Real.exp (-x / 2)) +
      d * (Real.exp (x / 2) - Real.exp (-x / 2))
  have hkc : Continuous k := by dsimp [k]; fun_prop
  have hkt : Tendsto k (𝓝[<] a.1)
      (𝓝 (c * (Real.exp (a.1 / 2) + Real.exp (-a.1 / 2)) +
        d * (Real.exp (a.1 / 2) - Real.exp (-a.1 / 2)))) :=
    hkc.tendsto a.1 |>.mono_left nhdsWithin_le_nhds
  have hp := Filter.Tendsto.pos_mul_atTop hk hkt
    (tendsto_ccmGammaPolarBoundary_right a)
  have hbase := tendsto_atTop_add_const_right _ (-((|c| + |d|) * M)) hp
  apply tendsto_atTop_mono' _ _ hbase
  filter_upwards [Ioo_mem_nhdsLT (show -a.1 < a.1 by linarith [a.property])]
    with x hx
  have h1 := abs_ccmPolarParityArithmeticRemainder_le a (Or.inl rfl) hx
  have h2 := abs_ccmPolarParityArithmeticRemainder_le a (Or.inr rfl) hx
  have hr : |c * ccmPolarParityArithmeticRemainder a 1 x +
      d * ccmPolarParityArithmeticRemainder a (-1) x| ≤ (|c| + |d|) * M := by
    calc
      _ ≤ |c * ccmPolarParityArithmeticRemainder a 1 x| +
          |d * ccmPolarParityArithmeticRemainder a (-1) x| := abs_add_le _ _
      _ = |c| * |ccmPolarParityArithmeticRemainder a 1 x| +
          |d| * |ccmPolarParityArithmeticRemainder a (-1) x| := by rw [abs_mul, abs_mul]
      _ ≤ |c| * M + |d| * M := add_le_add
        (mul_le_mul_of_nonneg_left h1 (abs_nonneg c))
        (mul_le_mul_of_nonneg_left h2 (abs_nonneg d))
      _ = _ := by ring
  rw [ccmPolarSourceParityCombination,
    ccmPolarParityBoundaryProfile_re_decomposition,
    ccmPolarParityBoundaryProfile_re_decomposition]
  dsimp [k]
  have hh := (abs_le.mp hr).2
  linarith

/-- Every nonzero real pair has a divergent physical source channel at an endpoint. -/
theorem ccmPolarSourceParityCombination_endpoint_rank (a : SuzukiPositiveAperture)
    (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0) :
    Tendsto (ccmPolarSourceParityCombination a c d) (𝓝[<] a.1) atTop ∨
    Tendsto (fun x => -ccmPolarSourceParityCombination a c d x) (𝓝[<] a.1) atTop ∨
    Tendsto (fun x => ccmPolarSourceParityCombination a c d (-x)) (𝓝[<] a.1) atTop ∨
    Tendsto (fun x => -ccmPolarSourceParityCombination a c d (-x)) (𝓝[<] a.1) atTop := by
  let E := Real.exp (a.1 / 2)
  let F := Real.exp (-a.1 / 2)
  have hE : 0 < E := Real.exp_pos _
  have hF : 0 < F := Real.exp_pos _
  have hEF : F < E := Real.exp_lt_exp.mpr (by linarith [a.property])
  let kp := c * (E + F) + d * (E - F)
  let km := c * (E + F) - d * (E - F)
  have hnonzero : kp ≠ 0 ∨ km ≠ 0 := by
    by_contra h
    push Not at h
    have hcprod : c * (E + F) = 0 := by dsimp [kp, km] at h; linarith
    have hc : c = 0 := (mul_eq_zero.mp hcprod).resolve_right (by linarith)
    have hdprod : d * (E - F) = 0 := by dsimp [kp] at h; rw [hc] at h; linarith
    have hd : d = 0 := (mul_eq_zero.mp hdprod).resolve_right (by linarith)
    exact hcd.elim (fun h => h hc) (fun h => h hd)
  rcases hnonzero with hplus | hminus
  · rcases lt_or_gt_of_ne hplus with hlt | hgt
    · right; left
      have ht := sourceCombination_right_of_pos a (-c) (-d) (by dsimp [kp, E, F] at hlt ⊢; linarith)
      have heq : ccmPolarSourceParityCombination a (-c) (-d) =
          fun x => -ccmPolarSourceParityCombination a c d x := by
        funext x
        unfold ccmPolarSourceParityCombination
        ring
      simpa only [heq] using ht
    · left
      exact sourceCombination_right_of_pos a c d (by simpa [kp, E, F] using hgt)
  · rcases lt_or_gt_of_ne hminus with hlt | hgt
    · right; right; right
      have ht := sourceCombination_right_of_pos a (-c) d (by dsimp [km, E, F] at hlt ⊢; linarith)
      have heq : ccmPolarSourceParityCombination a (-c) d =
          fun x => -ccmPolarSourceParityCombination a c d (-x) := by
        funext x
        rw [ccmPolarSourceParityCombination_reflect]
        unfold ccmPolarSourceParityCombination
        ring
      simpa only [heq] using ht
    · right; right; left
      have ht := sourceCombination_right_of_pos a c (-d) (by simpa [km, E, F] using hgt)
      simpa only [ccmPolarSourceParityCombination_reflect] using ht

end RHTower
