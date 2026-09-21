import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiCarrierRealNodeDensityNoGo
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianZetaGeometry

/-!
# Global removable representative at real Xi carrier nodes

The literal Suzuki real-axis carrier density has a removable discontinuity at
some real spectral Xi nodes.  A separate one-point patch does not provide one
representative for a global Hardy/Fredholm argument.  This module patches the
countable set of all such real node coordinates simultaneously.

The resulting density is measurable and equal to the literal density almost
everywhere.  At each real spectral Xi node it is continuous: its value is
zero and it is pointwise squeezed between zero and the literal density, whose
punctured limit is zero.  Thus the a.e. `L²` representative and the required
nodewise endpoint regularity can be fixed at once.  This resolves only that
representative issue; it provides no unbounded-width or global positivity
law.
-/

open Filter MeasureTheory Set Topology

namespace RiemannGaussian

noncomputable section

/-- Real observation coordinates occupied by a nontrivial zeta zero with real
rotated spectral coordinate. -/
def suzukiXiRealSpectralNodeSet : Set ℝ :=
  {x | ∃ rho : NontrivialZetaZero,
    (zetaSpectralCoordinate rho.1).im = 0 ∧
      x = (zetaSpectralCoordinate rho.1).re}

/-- The simultaneous removable-patch locus is countable. -/
theorem countable_suzukiXiRealSpectralNodeSet :
    suzukiXiRealSpectralNodeSet.Countable := by
  apply Set.Countable.mono ?_ (Set.countable_range fun rho : NontrivialZetaZero =>
    (zetaSpectralCoordinate rho.1).re)
  rintro x ⟨rho, hreal, hx⟩
  exact ⟨rho, hx.symm⟩

/-- The source-defined carrier representative obtained by setting every real
spectral node to its removable value zero. -/
noncomputable def suzukiXiRealAxisCarrierDensityGlobalRemovablePatch (x : ℝ) : ℝ := by
  classical
  exact if x ∈ suzukiXiRealSpectralNodeSet then 0 else
    suzukiXiRealAxisCarrierDensity x

/-- The global representative changes the literal carrier density only on a
Lebesgue-null countable set. -/
theorem ae_eq_suzukiXiRealAxisCarrierDensityGlobalRemovablePatch :
    suzukiXiRealAxisCarrierDensityGlobalRemovablePatch =ᵐ[volume]
      suzukiXiRealAxisCarrierDensity := by
  have hcompl : ∀ᵐ x : ℝ ∂volume, x ∈ suzukiXiRealSpectralNodeSetᶜ :=
    MeasureTheory.compl_mem_ae_iff.mpr
      (countable_suzukiXiRealSpectralNodeSet.measure_zero volume)
  filter_upwards [hcompl] with x hx
  have hnot : x ∉ suzukiXiRealSpectralNodeSet := by
    simpa only [Set.mem_compl_iff] using hx
  simp [suzukiXiRealAxisCarrierDensityGlobalRemovablePatch, hnot]

/-- The global representative is Borel measurable. -/
theorem measurable_suzukiXiRealAxisCarrierDensityGlobalRemovablePatch :
    Measurable suzukiXiRealAxisCarrierDensityGlobalRemovablePatch := by
  unfold suzukiXiRealAxisCarrierDensityGlobalRemovablePatch
  exact Measurable.ite countable_suzukiXiRealSpectralNodeSet.measurableSet
    measurable_const measurable_suzukiXiRealAxisCarrierDensity

/-- The global patch inherits the literal punctured zero limit at every real
spectral Xi node. -/
theorem tendsto_suzukiXiRealAxisCarrierDensityGlobalRemovablePatch_at_real_spectral_zero
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0) :
    Tendsto suzukiXiRealAxisCarrierDensityGlobalRemovablePatch
      (𝓝[≠] (zetaSpectralCoordinate rho.1).re) (𝓝 0) := by
  apply squeeze_zero' (g := suzukiXiRealAxisCarrierDensity)
  · exact Eventually.of_forall fun x => by
      unfold suzukiXiRealAxisCarrierDensityGlobalRemovablePatch
      split
      · norm_num
      · rw [suzukiXiRealAxisCarrierDensity_eq_arithmetic]
        exact suzukiXiRealAxisArithmeticCarrierDensity_nonneg x
  · exact Eventually.of_forall fun x => by
      unfold suzukiXiRealAxisCarrierDensityGlobalRemovablePatch
      split
      · rw [suzukiXiRealAxisCarrierDensity_eq_arithmetic]
        exact suzukiXiRealAxisArithmeticCarrierDensity_nonneg x
      · exact le_rfl
  · exact tendsto_suzukiXiRealAxisCarrierDensity_at_real_spectral_zero rho hrho

/-- One a.e.-equal, measurable representative is continuous at every real
spectral Xi node. -/
theorem continuousAt_suzukiXiRealAxisCarrierDensityGlobalRemovablePatch_at_real_spectral_zero
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0) :
    ContinuousAt suzukiXiRealAxisCarrierDensityGlobalRemovablePatch
      (zetaSpectralCoordinate rho.1).re := by
  rw [continuousAt_iff_punctured_nhds]
  have hnode : (zetaSpectralCoordinate rho.1).re ∈ suzukiXiRealSpectralNodeSet :=
    ⟨rho, hrho, rfl⟩
  have hvalue : suzukiXiRealAxisCarrierDensityGlobalRemovablePatch
      (zetaSpectralCoordinate rho.1).re = 0 := by
    classical
    unfold suzukiXiRealAxisCarrierDensityGlobalRemovablePatch
    exact if_pos hnode
  rw [hvalue]
  exact tendsto_suzukiXiRealAxisCarrierDensityGlobalRemovablePatch_at_real_spectral_zero rho hrho

end

end RiemannGaussian
