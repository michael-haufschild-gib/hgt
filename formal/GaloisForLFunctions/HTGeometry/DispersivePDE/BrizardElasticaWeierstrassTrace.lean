import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAlgebra
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Tactic

/-!
# Pole-free periodic Weierstrass traces for arXiv:2607.21750

Mathlib's analytic `PeriodPair.weierstrassP` has poles on its period lattice.  The paper evaluates
`wp` on a half-period-shifted line.  For every period pair, this module proves that the whole real
line `x * omega₁ + omega₂ / 2` avoids the lattice.  It therefore yields a globally differentiable,
one-periodic real-parameter solution of the scaled Weierstrass equation and an actual analytic path
on the associated short Weierstrass curve.
-/

open PeriodPair

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def halfShiftArgument (L : PeriodPair) (x : ℝ) : ℂ :=
  (x : ℂ) * L.ω₁ + L.ω₂ / 2

/-- A real line shifted by half the second period never meets the period lattice. -/
theorem halfShiftArgument_not_mem_lattice (L : PeriodPair) (x : ℝ) :
    halfShiftArgument L x ∉ L.lattice := by
  intro hmem
  obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp hmem
  have hcoeff := LinearIndependent.pair_iff.mp L.indep
    ((m : ℝ) - x) ((n : ℝ) - 1 / 2) (by
      simp only [Complex.real_smul]
      push_cast
      rw [halfShiftArgument] at hmn
      linear_combination hmn)
  have hnreal : (n : ℝ) = 1 / 2 := by linarith [hcoeff.2]
  have hnreal2 : (2 : ℝ) * (n : ℝ) = 1 := by linarith [hnreal]
  have hnint : (2 * n : ℤ) = 1 := by exact_mod_cast hnreal2
  omega

noncomputable def halfShiftWeierstrass (L : PeriodPair) (x : ℝ) : ℂ :=
  L.weierstrassP (halfShiftArgument L x)

noncomputable def halfShiftWeierstrassPrime (L : PeriodPair) (x : ℝ) : ℂ :=
  L.ω₁ * L.derivWeierstrassP (halfShiftArgument L x)

/-- The half-shifted trace has an actual derivative at every real parameter. -/
theorem hasDerivAt_halfShiftWeierstrass (L : PeriodPair) (x : ℝ) :
    HasDerivAt (halfShiftWeierstrass L) (halfShiftWeierstrassPrime L x) x := by
  have houter : HasDerivAt L.weierstrassP
      (L.derivWeierstrassP (halfShiftArgument L x)) (halfShiftArgument L x) := by
    have hda := (L.analyticOnNhd_weierstrassP _
      (halfShiftArgument_not_mem_lattice L x)).differentiableAt.hasDerivAt
    rwa [congrFun L.deriv_weierstrassP (halfShiftArgument L x)] at hda
  have hpath : HasDerivAt (halfShiftArgument L) L.ω₁ x := by
    have hbase : HasDerivAt (fun y : ℝ => (y : ℂ) * L.ω₁) L.ω₁ x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).mul_const L.ω₁
    have hsum : HasDerivAt (fun y : ℝ => (y : ℂ) * L.ω₁ + L.ω₂ / 2) L.ω₁ x :=
      hbase.add_const (L.ω₂ / 2)
    exact hsum
  have h := houter.scomp x hpath
  change HasDerivAt (fun y : ℝ => L.weierstrassP (halfShiftArgument L y))
    (L.ω₁ * L.derivWeierstrassP (halfShiftArgument L x)) x
  simpa only [Function.comp_def, smul_eq_mul] using h

/-- Paper equation (72) along the pole-free trace, including the chain-rule scale `omega₁²`. -/
theorem halfShiftWeierstrass_equation (L : PeriodPair) (x : ℝ) :
    halfShiftWeierstrassPrime L x ^ (2 : ℕ) =
      L.ω₁ ^ (2 : ℕ) *
        (4 * halfShiftWeierstrass L x ^ (3 : ℕ) -
          L.g₂ * halfShiftWeierstrass L x - L.g₃) := by
  have h := L.derivWeierstrassP_sq (halfShiftArgument L x)
    (halfShiftArgument_not_mem_lattice L x)
  rw [halfShiftWeierstrassPrime, halfShiftWeierstrass]
  rw [mul_pow, h]

/-- The trace is periodic with unit period in its normalized real coordinate. -/
theorem halfShiftWeierstrass_periodic (L : PeriodPair) :
    Function.Periodic (halfShiftWeierstrass L) 1 := by
  intro x
  have harg : halfShiftArgument L (x + 1) = halfShiftArgument L x + L.ω₁ := by
    rw [halfShiftArgument, halfShiftArgument]
    push_cast
    ring
  rw [halfShiftWeierstrass, halfShiftWeierstrass, harg]
  simpa using L.weierstrassP_add_coe (halfShiftArgument L x)
    ⟨L.ω₁, L.ω₁_mem_lattice⟩

/-- Short Weierstrass model attached to an analytic period pair. -/
noncomputable def analyticWeierstrassCurve (L : PeriodPair) : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -L.g₂ / 4
  a₆ := -L.g₃ / 4

/-- The analytic trace and its normalized derivative give a point on the curve for every real `x`. -/
theorem halfShiftWeierstrass_on_curve (L : PeriodPair) (x : ℝ) :
    (analyticWeierstrassCurve L).toAffine.Equation
      (halfShiftWeierstrass L x)
      (halfShiftWeierstrassPrime L x / (2 * L.ω₁)) := by
  have hω : L.ω₁ ≠ 0 := by
    intro hzero
    have h := L.indep.ne_zero 0
    simp [hzero] at h
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [analyticWeierstrassCurve]
  have heq := halfShiftWeierstrass_equation L x
  field_simp
  rw [heq]
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
