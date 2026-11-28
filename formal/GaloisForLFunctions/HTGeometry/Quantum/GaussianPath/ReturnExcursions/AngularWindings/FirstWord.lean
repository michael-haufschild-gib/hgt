import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.FirstWait
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.EndpointWord
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons.WindowLaw

/-! # One extremal integer at the first short-circuit visit after the original crossing -/

open Set Finset MeasureTheory Real
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings
open PrescribedTimes ShortWindows SharpOccupation SpectralJets
open SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics
open SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
open SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
noncomputable section

/-- One net circuit and one extremal integer determine every relative phase
winding at the actual first visit. The rounded words use only the spectrum,
circuit, and integer. The original crossing affects only the index window. -/
theorem gaussian_first_wait_word :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k s : ℕ,
      let K := k+3
      let X := prefixPoint k ω
      let P := nearHilbertContinuousCircuitBudget K
      let σ := crossingOrigin (k+1) P (9/80) X
      let Δ := crossingWait (k+1) P s X
      let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian K) X
      let A (i : Level k) := -E i/(2*π)
      let l := topLevel k
      let u : Level k := 0
      let G := A u-A l
      let x := physicalArc (7/20)
      0<G ∧ ∃ W ∈ atMostQuarterCircuitNet K s, ∃ N : ℤ,
        let b := lineTurns k W.val X
        let y := targetWord A b l u N
        (∀ T U : ℝ, Δ∈Icc T U →
          (N:ℝ)∈Icc ((σ+T)*G-(b u-b l)-x) ((σ+U)*G-(b u-b l)+x)) ∧
        (∀ i, |y i-(⌊y i+1/2⌋:ℝ)|≤x) ∧
        ∃ p : ℝ, ∀ i, |(σ+Δ)*A i-(b i+(⌊y i+1/2⌋:ℝ))-p|≤x/2 := by
  filter_upwards [gaussian_first_wait_winding,gaussian_path_all_prefixes_maximally_projective] with ω hw hω k s
  intro K X P σ Δ E A l u G x
  have hi := (hω k).injective
  obtain ⟨e,he⟩ := physical_sorted_order k ω hi
  have hinj : Function.Injective E := by
    intro i j hij
    apply e.symm.injective
    apply hi
    rwa [he,he,e.apply_symm_apply,e.apply_symm_apply]
  have hmon : Monotone E := monotone_sortedTuple _
  have hstrict := lt_of_le_of_ne (hmon (top_pos k).le) (hinj.ne (top_pos k).ne)
  have hg : A l<A u := div_lt_div_of_pos_right (neg_lt_neg hstrict) two_pi_pos
  have hext (i : Level k) : A i∈Icc (A l) (A u) := by
    have htop : i≤l := by change i.val≤2^(k+3)-1; have := i.isLt; omega
    exact ⟨div_le_div_of_nonneg_right (neg_le_neg (hmon htop)) two_pi_pos.le,
      div_le_div_of_nonneg_right (neg_le_neg (hmon (Fin.zero_le i))) two_pi_pos.le⟩
  obtain ⟨W,hW,m,⟨p,hp⟩,_,_⟩ := hw k s
  let b := lineTurns k W.val X
  have hfit (i : Level k) : |(σ+Δ)*A i-(b i+(m i:ℝ))-p|≤x/2 := by
    rw [show (σ+Δ)*A i-(b i+(m i:ℝ))-p=Δ*A i-(b i-σ*A i+(m i:ℝ))-p by ring]
    exact hp i
  have hx : x<1/2 := (physicalArc_spec (by norm_num : (0:ℝ)<7/20)
    (((by norm_num : (7/20:ℝ)<1)).trans_le (one_le_sqrt.mpr (by norm_num)))).1.2
  let N := m u-m l
  let y := targetWord A b l u N
  obtain ⟨hN,hword⟩ := endpoint_word A b m l u (σ+Δ) p x hg hext hfit
  have hround (i : Level k) : ⌊y i+1/2⌋=m i-m l :=
    endpoint_word_round A b m l u (σ+Δ) p x hx hg hext hfit i
  refine ⟨sub_pos.mpr hg,W,hW,N,?_,?_,?_⟩
  · intro T U ht
    obtain ⟨hlo,hhi⟩ := abs_le.mp hN
    have hl := mul_le_mul_of_nonneg_right (add_le_add_left ht.1 σ) (sub_nonneg.mpr hg.le)
    have hu := mul_le_mul_of_nonneg_right (add_le_add_left ht.2 σ) (sub_nonneg.mpr hg.le)
    change (σ+T)*G-(b u-b l)-x≤(N:ℝ) ∧ (N:ℝ)≤(σ+U)*G-(b u-b l)+x
    dsimp only [G,N] at *
    constructor <;> linarith only [hlo,hhi,hl,hu]
  · intro i
    rw [hround]
    exact hword i
  · refine ⟨p+(m l:ℝ),?_⟩
    intro i
    rw [hround,Int.cast_sub]
    convert hfit i using 2
    ring

#print axioms gaussian_first_wait_word
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings
