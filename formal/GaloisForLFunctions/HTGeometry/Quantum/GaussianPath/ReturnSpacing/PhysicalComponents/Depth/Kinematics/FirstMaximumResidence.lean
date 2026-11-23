import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.Kinematics.MaximumResidence
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.CrossingWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # Maximum-length empty residence at the first sufficiently deep return -/
open MeasureTheory Filter Finset Set Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
open EmptyVisitFlux SharpOccupation
noncomputable section

/-- From the first near-Hilbert crossing, every sufficiently accurate first
empty return lies in an outer component of exactly the maximum possible
duration. Its midpoint is a coincidence of the extreme eigenphases. -/
theorem gaussian_first_maximum_residence :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let w := fun i => -H.2.isHermitian.eigenvalues i/(2*π)
      let W := univ.sup' univ_nonempty w-univ.inf' univ_nonempty w
      ∃ σ>0, orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        ∃ p q, w p=univ.sup' univ_nonempty w ∧ w q=univ.inf' univ_nonempty w ∧
          ∀ ρ∈Ioo (0:ℝ) (9/80), let r := physicalArc ρ
            ∃ η∈Ioc (0:ℝ) ρ, ∀ δ∈Ioc (0:ℝ) η, let v := PrecisionReturns.firstVisit H σ 0 δ
              ∃ c, σ<c-r/W ∧ |v-c| * W≤physicalArc δ ∧ flow w c p=flow w c q ∧
                Icc (c-r/W) (c+r/W) ⊆ visitSet H 0 ρ ∧
                ∀ a≤c-r/W, ∀ b≥c+r/W, Icc a b ⊆ visitSet H 0 ρ → a=c-r/W ∧ b=c+r/W := by
  filter_upwards [gaussian_first_crossing_flux,gaussian_path_all_prefixes_maximally_projective] with ω hc hi
  filter_upwards [hc] with k hk
  intro N H P w W
  obtain ⟨σ,hσ,he,hb,_⟩ := hk
  obtain ⟨p,_,hp⟩ := exists_mem_eq_sup' univ_nonempty w
  obtain ⟨q,_,hq⟩ := exists_mem_eq_inf' univ_nonempty w
  have hbnd (i) : w q≤w i ∧ w i≤w p := by
    rw [←hp,←hq]
    exact ⟨inf'_le w (mem_univ i),le_sup' w (mem_univ i)⟩
  have hinj : Function.Injective w := by
    intro i j h
    apply (hi k).injective
    change -H.2.isHermitian.eigenvalues i/(2*π)= -H.2.isHermitian.eigenvalues j/(2*π) at h
    exact neg_inj.mp ((div_left_inj' (by positivity : (2:ℝ)*π≠0)).mp h)
  have hext : w q<w p := by
    by_contra! h
    have hall (i) : w i=w q := le_antisymm ((hbnd i).2.trans h) (hbnd i).1
    obtain ⟨i,j,hij⟩ := exists_pair_ne (Fin N→Bool)
    exact hij (hinj ((hall i).trans (hall j).symm))
  have hW : W=w p-w q := congrArg₂ (·-·) hp hq
  have hpos : 0<W := by rw [hW]; exact sub_pos.mpr hext
  refine ⟨σ,hσ,he,hb,p,q,hp.symm,hq.symm,?_⟩
  intro ρ hρ r
  have hsqrt : (9/80:ℝ)<sqrt 2 := by nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2]
  have hsmall := hρ.2.trans hsqrt
  obtain ⟨hr,her⟩ := physicalArc_spec hρ.1 hsmall
  obtain ⟨d,hd,halign⟩ := deep_visit_alignment w hinj p q hext hbnd hr.1
  have hd' : d∈Icc (0:ℝ) (1/2) := ⟨hd.1.le,hd.2.trans hr.2.le⟩
  let η := zeroGateArcTolerance d
  have hη : η∈Ioc (0:ℝ) ρ := by
    have hz := strictMonoOn_zeroGateArcTolerance (show (0:ℝ)∈Icc 0 (1/2:ℝ) by constructor <;> norm_num) hd' hd.1
    have hle := strictMonoOn_zeroGateArcTolerance.monotoneOn hd' (Ioo_subset_Icc_self hr) hd.2
    exact ⟨by simpa only [η,zeroGateArcTolerance,mul_zero,zero_div,sin_zero] using hz,hle.trans_eq her⟩
  refine ⟨η,hη,?_⟩
  intro δ hδ v
  have hδs := (hδ.2.trans hη.2).trans_lt hsmall
  obtain ⟨hx,hex⟩ := physicalArc_spec hδ.1 hδs
  have hxd : physicalArc δ≤d := by
    by_contra! h
    have hh := strictMonoOn_zeroGateArcTolerance hd' (Ioo_subset_Icc_self hx) h
    exact hh.not_ge (hex.trans_le hδ.2)
  obtain ⟨hσv,hv⟩ := (PrecisionReturns.firstVisit_isLeast H σ 0 hδ.1).1
  obtain ⟨c,hc',hpq,hbox⟩ := halign (physicalArc δ) ⟨hx.1.le,hxd⟩ v ((physical_visit H hδ.1 hδs v).mpr hv)
  have hh := maximum_residence_of_alignment w p q hr.1 hr.2 hext hbox
  rw [←hW] at hh hc'
  have hvisit : Icc (c-r/W) (c+r/W) ⊆ visitSet H 0 ρ :=
    fun s hs => (physical_visit H hρ.1 hsmall s).mp (hh.1 s hs)
  have hno : σ∉visitSet H 0 ρ := by
    rintro ⟨z,hz,C,hC,hfit⟩
    have hp' : HasProjectiveCircuitApproximation N ρ P (unitaryEvolution H.val σ) :=
      ⟨z,hz,C,hC.trans (Nat.zero_le _),hfit⟩
    have hle : orbitCircuitDistance H P σ≤ρ := (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp hp'
    exact hρ.2.not_ge (he.symm.trans_le hle)
  have hvc := (le_div_iff₀ hpos).mpr (hc'.trans (hxd.trans hd.2))
  have hfinal : σ<c-r/W := by
    by_contra! h
    exact hno (hvisit ⟨h,by linarith only [(abs_le.mp hvc).2,hσv]⟩)
  refine ⟨c,hfinal,hc',hpq,hvisit,?_⟩
  exact fun a ha b hb' hs => hh.2 a ha b hb' fun s ht => (physical_visit H hρ.1 hsmall s).mpr (hs ht)

#print axioms gaussian_first_maximum_residence
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
