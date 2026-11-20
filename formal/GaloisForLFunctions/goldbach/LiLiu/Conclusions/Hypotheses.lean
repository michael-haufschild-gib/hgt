import GaloisForLFunctions.goldbach.LiLiu.Boundary.HardyOperator
import GaloisForLFunctions.goldbach.LiLiu.Spectral.QuaternionProduct
import GaloisForLFunctions.goldbach.LiLiu.Spectral.SpectralScales

/-! # The target-dependent Li–Liu hypotheses -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open Filter
open scoped Topology
noncomputable section

theorem leftEdge_bounds {N : ℕ} (h : 10 < Real.log N) : 0 < leftEdge N ∧ leftEdge N < 1/8 := by
  have hb : 8 < Real.log N := (by norm_num : (8:ℝ)<10).trans h
  have hp : 0 < Real.log N := (by norm_num : (0:ℝ)<8).trans hb
  exact ⟨one_div_pos.mpr hp,one_div_lt_one_div_of_lt (by norm_num) hb⟩

/-- The two edges are distinct at every sufficiently large target. -/
theorem eventually_large_strip : ∀ᶠ N : ℕ in atTop, 4 ≤ N ∧ 10 < Real.log N :=
  (eventually_ge_atTop 4).and ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 10)

/-- The quaternionic function of the Hardy integral operator at the specified modulus. -/
def arithmeticSpectralProduct (N : ℕ) (hN : 4 ≤ N) (hg : modulusGRH N) (hl : 10 < Real.log N) : ℍ → ℍ :=
  match N with
  | 0 => by omega
  | 1 => by omega
  | k+2 => quaternionSpectralProduct
      (hardyOperator (n := k+1) hN hg (leftEdge_bounds hl).1 (leftEdge_bounds hl).2.le) (spectralScale (k+2))

def eventualEvenGRH : Prop := ∀ᶠ N : ℕ in atTop, Even N → modulusGRH N

def admissibleWidth (h : ℕ → ℝ) : Prop :=
  (∀ N, 0 < h N) ∧ Tendsto h atTop atTop ∧ ∀ᶠ N : ℕ in atTop, exclusionWidth h N ≤ 1/4

/-- Hypothesis S(h) excludes zeros in the prescribed open half-space at every large even GRH target. -/
def hypothesisS (h : ℕ → ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, Even N → ∀ (hN : 4 ≤ N) (hg : modulusGRH N) (hl : 10 < Real.log N) (q : ℍ),
    1-exclusionWidth h N < q.re → arithmeticSpectralProduct N hN hg hl q ≠ 0

/-- Hypothesis R places every quaternionic zero of the same arithmetic product on Re q=1/2. -/
def hypothesisR : Prop :=
  ∀ᶠ N : ℕ in atTop, Even N → ∀ (hN : 4 ≤ N) (hg : modulusGRH N) (hl : 10 < Real.log N) (q : ℍ),
    arithmeticSpectralProduct N hN hg hl q = 0 → q.re=1/2

theorem hypothesisS_of_R {h : ℕ → ℝ} (hh : admissibleWidth h) (hr : hypothesisR) : hypothesisS h := by
  filter_upwards [hh.2.2,hr] with N hw hcrit he hN hg hl q hq hz
  have h := hcrit he hN hg hl q hz
  linarith only [h,hq,hw]

#print axioms hypothesisS_of_R
end
end GaloisForLFunctions.Goldbach.LiLiu
