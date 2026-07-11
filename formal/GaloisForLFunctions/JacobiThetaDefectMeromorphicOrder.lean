import GaloisForLFunctions.MeromorphicPoleOrbitBoundary
import GaloisForLFunctions.JacobiThetaDefectPrincipalPart
import Mathlib.Analysis.Meromorphic.TrailingCoefficient

/-!
# Exact meromorphic orders of the translated theta defect

The normalized residue limits of the translated theta logarithmic-derivative defect are converted
into Lean's native `meromorphicOrderAt` language.  Both pole lattices have exact order `-1`, and
the exact theta zero classification proves that there are no other poles.
-/

open Complex Set Filter
open scoped Topology

namespace GaloisForLFunctions

noncomputable section

/-- A meromorphic function whose product with `z-p` tends to a nonzero finite limit has a simple
pole at `p`. -/
theorem meromorphicOrderAt_eq_neg_one_of_tendsto_mul_sub
    {f : ℂ → ℂ} {p c : ℂ} (hf : MeromorphicAt f p) (hc : c ≠ 0)
    (hlim : Tendsto (fun z : ℂ => (z - p) * f z) (𝓝[≠] p) (𝓝 c)) :
    meromorphicOrderAt f p = ((-1 : ℤ) : WithTop ℤ) := by
  have hlin : MeromorphicAt (fun z : ℂ => z - p) p := by fun_prop
  have hprod : MeromorphicAt (fun z : ℂ => (z - p) * f z) p := hlin.mul hf
  have hzero : meromorphicOrderAt (fun z : ℂ => (z - p) * f z) p = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hprod).1 ⟨c, hc, hlim⟩
  change meromorphicOrderAt ((fun z : ℂ => z - p) * f) p = 0 at hzero
  rw [meromorphicOrderAt_mul hlin hf, meromorphicOrderAt_id_sub_const] at hzero
  have hfinite : meromorphicOrderAt f p ≠ ⊤ := by
    intro htop
    rw [htop] at hzero
    simp at hzero
  lift meromorphicOrderAt f p to ℤ using hfinite with n hn
  have hzero' : (1 : ℤ) + n = 0 := by exact_mod_cast hzero
  have hnneg : n = -1 := by omega
  simp [hnneg]

theorem meromorphicAt_thetaLogDeriv {τ z : ℂ} (hτ : 0 < τ.im) :
    MeromorphicAt (thetaLogDeriv · τ) z := by
  rw [show (thetaLogDeriv · τ) =
      (jacobiTheta₂' · τ) / (jacobiTheta₂ · τ) by funext w; rfl]
  exact ((jacobiTheta₂'_analyticOnNhd_fst τ hτ) z (mem_univ z)).meromorphicAt.div
    ((jacobiTheta₂_analyticOnNhd_fst τ hτ) z (mem_univ z)).meromorphicAt

theorem meromorphicAt_thetaLogDerivDefect {τ h z : ℂ} (hτ : 0 < τ.im) :
    MeromorphicAt (thetaLogDerivDefect h · τ) z := by
  have hbase := meromorphicAt_thetaLogDeriv (z := z) hτ
  have hshiftBase := meromorphicAt_thetaLogDeriv (z := z + h) hτ
  have hinner : AnalyticAt ℂ (fun w : ℂ => w + h) z := by fun_prop
  have hshift : MeromorphicAt (fun w : ℂ => thetaLogDeriv (w + h) τ) z := by
    change MeromorphicAt ((thetaLogDeriv · τ) ∘ fun w : ℂ => w + h) z
    exact MeromorphicAt.comp_analyticAt (x := z) (f := fun w => thetaLogDeriv w τ)
      (g := fun w : ℂ => w + h) hshiftBase hinner
  simpa [thetaLogDerivDefect] using hshift.fun_sub hbase

/-- The base half-period lattice is an exact simple-pole orbit of the theta defect. -/
theorem meromorphicOrderAt_thetaLogDerivDefect_base
    {τ h : ℂ} (hτ : 0 < τ.im) (hh : ThetaNonlatticeShift τ h) (m n : ℤ) :
    let p := thetaHalfPeriod τ + m + n * τ
    meromorphicOrderAt (thetaLogDerivDefect h · τ) p = ((-1 : ℤ) : WithTop ℤ) := by
  dsimp only
  let p := thetaHalfPeriod τ + m + n * τ
  apply meromorphicOrderAt_eq_neg_one_of_tendsto_mul_sub (c := -1)
    (meromorphicAt_thetaLogDerivDefect (z := p) hτ) (by norm_num)
  simpa [p] using tendsto_thetaLogDerivDefect_normalized_base hτ hh m n

/-- The lattice translated by `-h` is the second exact simple-pole orbit of the theta defect. -/
theorem meromorphicOrderAt_thetaLogDerivDefect_shifted
    {τ h : ℂ} (hτ : 0 < τ.im) (hh : ThetaNonlatticeShift τ h) (m n : ℤ) :
    let p := thetaHalfPeriod τ + m + n * τ - h
    meromorphicOrderAt (thetaLogDerivDefect h · τ) p = ((-1 : ℤ) : WithTop ℤ) := by
  dsimp only
  let p := thetaHalfPeriod τ + m + n * τ - h
  apply meromorphicOrderAt_eq_neg_one_of_tendsto_mul_sub (c := 1)
    (meromorphicAt_thetaLogDerivDefect (z := p) hτ) (by norm_num)
  simpa [p] using tendsto_thetaLogDerivDefect_normalized_shifted hτ hh m n

theorem analyticAt_thetaLogDeriv_of_ne_zero {τ z : ℂ} (hτ : 0 < τ.im)
    (hz : jacobiTheta₂ z τ ≠ 0) :
    AnalyticAt ℂ (thetaLogDeriv · τ) z := by
  rw [show (thetaLogDeriv · τ) =
      (jacobiTheta₂' · τ) / (jacobiTheta₂ · τ) by funext w; rfl]
  exact ((jacobiTheta₂'_analyticOnNhd_fst τ hτ) z (mem_univ z)).div
    ((jacobiTheta₂_analyticOnNhd_fst τ hτ) z (mem_univ z)) hz

/-- **Exact pole classification.** For a nonlattice shift, the theta defect has precisely the two
simple-pole lattice orbits already detected by the normalized residue limits. -/
theorem thetaLogDerivDefect_pole_iff
    {τ h z : ℂ} (hτ : 0 < τ.im) (hh : ThetaNonlatticeShift τ h) :
    meromorphicOrderAt (thetaLogDerivDefect h · τ) z < 0 ↔
      (∃ m n : ℤ, z = thetaHalfPeriod τ + m + n * τ) ∨
        ∃ m n : ℤ, z = thetaHalfPeriod τ + m + n * τ - h := by
  constructor
  · intro hpole
    by_contra hzclasses
    push Not at hzclasses
    have hz0 : jacobiTheta₂ z τ ≠ 0 := by
      intro hzero
      obtain ⟨m, n, hmn⟩ :=
        (jacobiTheta₂_eq_zero_iff_thetaHalfPeriod_add_lattice hτ).mp hzero
      exact hzclasses.1 m n hmn
    have hzh0 : jacobiTheta₂ (z + h) τ ≠ 0 := by
      intro hzero
      obtain ⟨m, n, hmn⟩ :=
        (jacobiTheta₂_eq_zero_iff_thetaHalfPeriod_add_lattice hτ).mp hzero
      apply hzclasses.2 m n
      linear_combination hmn
    have hbaseAn := analyticAt_thetaLogDeriv_of_ne_zero hτ hz0
    have hshiftBase := analyticAt_thetaLogDeriv_of_ne_zero hτ hzh0
    have hinner : AnalyticAt ℂ (fun w : ℂ => w + h) z := by fun_prop
    have hshiftAn : AnalyticAt ℂ (fun w : ℂ => thetaLogDeriv (w + h) τ) z := by
      change AnalyticAt ℂ ((fun w => thetaLogDeriv w τ) ∘ fun w : ℂ => w + h) z
      exact AnalyticAt.comp (x := z) (g := fun w => thetaLogDeriv w τ)
        (f := fun w : ℂ => w + h) hshiftBase hinner
    have hdefAn : AnalyticAt ℂ (thetaLogDerivDefect h · τ) z := by
      simpa [thetaLogDerivDefect] using hshiftAn.sub hbaseAn
    exact (not_lt_of_ge hdefAn.meromorphicOrderAt_nonneg) hpole
  · rintro (⟨m, n, rfl⟩ | ⟨m, n, rfl⟩)
    · rw [meromorphicOrderAt_thetaLogDerivDefect_base hτ hh m n]
      exact_mod_cast (show (-1 : ℤ) < 0 by omega)
    · rw [meromorphicOrderAt_thetaLogDerivDefect_shifted hτ hh m n]
      exact_mod_cast (show (-1 : ℤ) < 0 by omega)

end

end GaloisForLFunctions
