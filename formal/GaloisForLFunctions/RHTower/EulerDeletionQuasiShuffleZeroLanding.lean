import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleConvergence
import GaloisForLFunctions.RHTower.DirichletUniformAbel
import GaloisForLFunctions.RHTower.DirichletLSeriesBridge
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# Euler-deletion zero landing

The conditionally convergent Euler-deletion path is holomorphic on `Re s > 0`.  Its exact finite
dilation identity identifies it on `Re s > 1` with

```text
(1 - p * p^(-s)) * zeta(s).
```

After clearing the removable pole at one, analytic uniqueness propagates this identity throughout
the positive half-plane.  Consequently every positive-real-part zeta zero closes every deletion
path at level one.

This is deliberately only a level-one landing theorem.  Equal closed endpoints do not determine
chronological second levels; no quasi-shuffle refinement coherence follows from this file.
-/

noncomputable section

open Filter Topology Set

namespace RHTower

/-- Ordinary finite Dirichlet prefixes converge to zeta in the absolute half-plane. -/
theorem tendsto_zetaDirichletPrefix {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N => zetaDirichletPrefix N s) atTop (nhds (riemannZeta s)) := by
  have hhas : HasSum (LSeries.term (1 : ℕ → ℂ) s) (riemannZeta s) :=
    LSeriesHasSum_one hs
  have hshift : HasSum (fun n => LSeries.term (1 : ℕ → ℂ) s (n + 1))
      (riemannZeta s) := by
    have := (hasSum_nat_add_iff' 1).mpr hhas
    simpa [LSeries.term_zero] using this
  refine hshift.tendsto_sum_nat.congr fun N => ?_
  rw [zetaDirichletPrefix, sum_Icc_eq_sum_range_succ]
  apply Finset.sum_congr rfl
  intro n hn
  simpa using
    (GaloisForLFunctions.RHTower.term_succ_eq (1 : ℕ → ℂ) s n)

/-- Abel convergence packaged in the corpus's ordinary Dirichlet-series API. -/
theorem eulerDeletionDirichlet_convergesAt {q : ℕ} {s : ℂ} (hs : 0 < s.re) :
    GaloisForLFunctions.RHTower.DirichletConvergesAt
      (eulerDeletionDirichletCoefficient q) s := by
  simpa [GaloisForLFunctions.RHTower.DirichletConvergesAt,
    GaloisForLFunctions.RHTower.dirichletPartialSum] using
      (tendsto_eulerDeletionDirichletCoefficient (q := q) hs)

/-- The zero-indexed conditional prefix is the one-indexed deletion prefix. -/
theorem dirichletPartialSum_eulerDeletion_eq_prefix (q N : ℕ) (s : ℂ) :
    GaloisForLFunctions.RHTower.dirichletPartialSum
        (eulerDeletionDirichletCoefficient q) N s =
      eulerDeletionDirichletPrefix (q + 1) N s := by
  rw [GaloisForLFunctions.RHTower.dirichletPartialSum,
    eulerDeletionDirichletPrefix, sum_Icc_eq_sum_range_succ]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [eulerDeletionDirichletCoefficient]
  congr 2
  norm_num

/-- Far-right value of the deletion sum, derived from the finite dilation identity. -/
theorem dirichletSum_eulerDeletion_eq_factor_zeta
    (q : ℕ) {s : ℂ} (hs : 1 < s.re) :
    GaloisForLFunctions.RHTower.dirichletSum
        (eulerDeletionDirichletCoefficient q) s =
      (1 - complexEulerDilationFactor (q + 1) s) * riemannZeta s := by
  let p := q + 1
  have hp : 0 < p := by omega
  have hconv := eulerDeletionDirichlet_convergesAt (q := q) (s := s) (by linarith)
  have hleft := GaloisForLFunctions.RHTower.tendsto_dirichletSum hconv
  have hraw := tendsto_zetaDirichletPrefix hs
  have hdiv : Tendsto (fun N => zetaDirichletPrefix (N / p) s) atTop
      (nhds (riemannZeta s)) :=
    hraw.comp (Nat.tendsto_div_const_atTop hp.ne')
  have hright : Tendsto
      (fun N => zetaDirichletPrefix N s -
        complexEulerDilationFactor p s * zetaDirichletPrefix (N / p) s)
      atTop
      (nhds (riemannZeta s - complexEulerDilationFactor p s * riemannZeta s)) :=
    hraw.sub (tendsto_const_nhds.mul hdiv)
  have hsame : Tendsto
      (fun N => GaloisForLFunctions.RHTower.dirichletPartialSum
        (eulerDeletionDirichletCoefficient q) N s)
      atTop
      (nhds (riemannZeta s - complexEulerDilationFactor p s * riemannZeta s)) := by
    refine hright.congr fun N => ?_
    rw [dirichletPartialSum_eulerDeletion_eq_prefix]
    exact (eulerDeletionDirichletPrefix_eq_dilation p N hp s).symm
  have heq := tendsto_nhds_unique hleft hsame
  change _ = (1 - complexEulerDilationFactor p s) * riemannZeta s
  rw [heq]
  ring

/-- Conditional Euler-deletion sum selected by ordinary chronological cutoffs. -/
noncomputable def eulerDeletionDirichletSum (q : ℕ) (s : ℂ) : ℂ :=
  GaloisForLFunctions.RHTower.dirichletSum (eulerDeletionDirichletCoefficient q) s

/-- The complex dilation factor is entire in the exponent. -/
theorem differentiable_complexEulerDilationFactor (p : ℕ) (hp : 0 < p) :
    Differentiable ℂ (complexEulerDilationFactor p) := by
  have hpC : (((p : ℝ) : ℂ)) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (by exact_mod_cast hp.ne')
  unfold complexEulerDilationFactor
  exact (differentiable_const (p : ℂ)).mul
    (differentiable_neg.const_cpow (Or.inl hpC))

/-- The conditional deletion sum is holomorphic throughout the positive half-plane. -/
theorem differentiableOn_eulerDeletionDirichletSum (q : ℕ) :
    DifferentiableOn ℂ (eulerDeletionDirichletSum q) {s : ℂ | 0 < s.re} := by
  intro s hs
  change 0 < s.re at hs
  let s₀ : ℂ := (s.re / 2 : ℝ)
  have hs₀ : 0 < s₀.re := by
    simp [s₀]
    linarith
  have hconv := eulerDeletionDirichlet_convergesAt (q := q) (s := s₀) hs₀
  have hdiff := GaloisForLFunctions.RHTower.differentiableOn_dirichletSum hconv
  have hmem : s ∈ {z : ℂ | s₀.re < z.re} := by
    change s₀.re < s.re
    simp [s₀]
    linarith
  have hopen : IsOpen {z : ℂ | s₀.re < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hat := hdiff.differentiableAt (hopen.mem_nhds hmem)
  change DifferentiableWithinAt ℂ
    (GaloisForLFunctions.RHTower.dirichletSum (eulerDeletionDirichletCoefficient q))
    {z : ℂ | 0 < z.re} s
  exact hat.differentiableWithinAt

/-- Pole-cleared deletion identity on `Re s > 0`, obtained by analytic uniqueness. -/
theorem poleCleared_eulerDeletionDirichletSum_eq
    (q : ℕ) {s : ℂ} (hs : 0 < s.re) :
    (s - 1) * eulerDeletionDirichletSum q s =
      (1 - complexEulerDilationFactor (q + 1) s) * zetaResidueUnit s := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUpre : IsPreconnected U :=
    (convex_halfSpace_gt ⟨Complex.add_re, fun c z => Complex.smul_re c z⟩ 0).isPreconnected
  let F : ℂ → ℂ := fun z => (z - 1) * eulerDeletionDirichletSum q z
  let G : ℂ → ℂ := fun z =>
    (1 - complexEulerDilationFactor (q + 1) z) * zetaResidueUnit z
  have hFdiff : DifferentiableOn ℂ F U := by
    exact ((differentiable_id.sub_const (1 : ℂ)).differentiableOn.mul
      (differentiableOn_eulerDeletionDirichletSum q))
  have hGdiff : DifferentiableOn ℂ G U := by
    have hfactor : Differentiable ℂ (complexEulerDilationFactor (q + 1)) :=
      differentiable_complexEulerDilationFactor (q + 1) (by omega)
    have hleft : Differentiable ℂ (fun z => 1 - complexEulerDilationFactor (q + 1) z) :=
      (differentiable_const 1).sub hfactor
    have hzeta : Differentiable ℂ zetaResidueUnit :=
      fun z => (analyticAt_zetaResidueUnit z).differentiableAt
    have hprod := hleft.mul hzeta
    intro z hz
    exact (hprod z).differentiableWithinAt
  have hFana : AnalyticOnNhd ℂ F U := hFdiff.analyticOnNhd hUopen
  have hGana : AnalyticOnNhd ℂ G U := hGdiff.analyticOnNhd hUopen
  have htwoU : (2 : ℂ) ∈ U := by norm_num [U]
  have hevent : F =ᶠ[nhds (2 : ℂ)] G := by
    have hVopen : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have htwoV : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
    filter_upwards [hVopen.mem_nhds htwoV] with z hz
    have hz1 : 1 < z.re := hz
    have hzne : z ≠ 1 := by
      intro h
      rw [h] at hz1
      norm_num at hz1
    change (z - 1) * eulerDeletionDirichletSum q z =
      (1 - complexEulerDilationFactor (q + 1) z) * zetaResidueUnit z
    rw [eulerDeletionDirichletSum,
      dirichletSum_eulerDeletion_eq_factor_zeta q hz1]
    rw [(zetaResidueUnit_eventuallyEq hzne).eq_of_nhds]
    ring
  have heq := hFana.eqOn_of_preconnected_of_eventuallyEq hGana hUpre htwoU hevent
  have hsU : s ∈ U := hs
  simpa [F, G] using heq hsU

/-- Every positive-half-plane zeta zero closes every Euler-deletion path at level one. -/
theorem eulerDeletionDirichletSum_eq_zero_of_riemannZeta_eq_zero
    (q : ℕ) {rho : ℂ} (hrhoRe : 0 < rho.re)
    (hrho1 : rho ≠ 1) (hzeta : riemannZeta rho = 0) :
    eulerDeletionDirichletSum q rho = 0 := by
  have hpc := poleCleared_eulerDeletionDirichletSum_eq q hrhoRe
  rw [(zetaResidueUnit_eventuallyEq hrho1).eq_of_nhds, hzeta, mul_zero, mul_zero] at hpc
  exact (mul_eq_zero.mp hpc).resolve_left (sub_ne_zero.mpr hrho1)

end RHTower
