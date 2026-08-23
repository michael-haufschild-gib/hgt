import GaloisForLFunctions.HTGeometry.DispersivePDE.NLSSolitons
import GaloisForLFunctions.HTGeometry.FDNLS.Symmetries

/-!
# Closed fractional discrete NLS applications

An explicit one-site soliton on a three-site quasi-Riesz lattice, its focusing/defocusing stagger,
and closed applications of corpus power/Hamiltonian conservation.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE

open GaloisForLFunctions.HTGeometry.FDNLS

noncomputable def singleSiteFDNLS (t : ℝ) (n : Fin 3) : ℂ :=
  if n = 0 then brightPhase t else 0

theorem singleSiteFDNLS_solves :
    IsLatticeNLSSolution 0 1 (quasiRieszKernel 1) singleSiteFDNLS := by
  intro t n
  by_cases hn : n = 0
  · subst n
    change HasDerivAt (fun s : ℝ => brightPhase s)
      (-Complex.I * latticeNLSField 0 1 (quasiRieszKernel 1) (singleSiteFDNLS t) 0) t
    apply (hasDerivAt_brightPhase t).congr_deriv
    simp [latticeNLSField, singleSiteFDNLS, norm_brightPhase]
    ring
  · change HasDerivAt (fun s : ℝ => singleSiteFDNLS s n)
      (-Complex.I * latticeNLSField 0 1 (quasiRieszKernel 1) (singleSiteFDNLS t) n) t
    simpa [singleSiteFDNLS, hn, latticeNLSField] using hasDerivAt_const t (0 : ℂ)

theorem singleSiteFDNLS_power_exact (t : ℝ) : latticePower (singleSiteFDNLS t) = 1 := by
  simp [latticePower, singleSiteFDNLS, norm_brightPhase, Fin.sum_univ_succ]

theorem singleSiteFDNLS_conserved (t₁ t₂ : ℝ) :
    latticePower (singleSiteFDNLS t₁) = latticePower (singleSiteFDNLS t₂)
      ∧ latticeHamiltonian 0 1 (quasiRieszKernel 1) (singleSiteFDNLS t₁)
        = latticeHamiltonian 0 1 (quasiRieszKernel 1) (singleSiteFDNLS t₂) :=
  quasiRiesz_conserved singleSiteFDNLS_solves t₁ t₂

noncomputable def singleSiteFDNLSDefocusing : ℝ → Fin 3 → ℂ :=
  stagger 0 Real.pi staggerSign singleSiteFDNLS

theorem singleSiteFDNLSDefocusing_solves :
    IsLatticeNLSSolution 0 (-1) (quasiRieszKernel 1) singleSiteFDNLSDefocusing := by
  exact (quasiRiesz_stagger_solution_iff (C := 0) (σ := -1) singleSiteFDNLS).2
    singleSiteFDNLS_solves

theorem singleSiteFDNLSDefocusing_conserved (t₁ t₂ : ℝ) :
    latticePower (singleSiteFDNLSDefocusing t₁) = latticePower (singleSiteFDNLSDefocusing t₂)
      ∧ latticeHamiltonian 0 (-1) (quasiRieszKernel 1) (singleSiteFDNLSDefocusing t₁)
        = latticeHamiltonian 0 (-1) (quasiRieszKernel 1) (singleSiteFDNLSDefocusing t₂) :=
  quasiRiesz_conserved singleSiteFDNLSDefocusing_solves t₁ t₂

theorem singleSiteFDNLSDefocusing_power_exact (t : ℝ) :
    latticePower (singleSiteFDNLSDefocusing t) = 1 := by
  rw [singleSiteFDNLSDefocusing, latticePower]
  have hnorm : ∀ n : Fin 3,
      ‖stagger 0 Real.pi staggerSign singleSiteFDNLS t n‖ = ‖singleSiteFDNLS t n‖ :=
    fun n => norm_stagger staggerSign_mul_self singleSiteFDNLS t n
  simp_rw [hnorm]
  exact singleSiteFDNLS_power_exact t

end GaloisForLFunctions.HTGeometry.DispersivePDE
