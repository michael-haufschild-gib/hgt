import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MomentResponse.MomentLoss
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MovingTrace.TunableWindows

/-! # Physical tests at a prescribed heat moment -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Finset Set

/-- Simultaneous open tests on a relative partition and a real moment admit a conserving rank-one realization. -/
theorem physical_moment_probe (q : GibbsExponent) {z : ℂ} (hz : 0 < z.re) (b : SpectralBand 1)
    {A D : ℝ} (ha : A < ‖relativePartition b z‖) (hd : momentLoss q b < D) :
    ∃ c ∈ physicalSpectra 1, A < ‖relativePartition c z‖ ∧ momentLoss q c < D := by
  let U := {c : SpectralBand 1 | A < ‖relativePartition c z‖ ∧ momentLoss q c < D}
  have ho : IsOpen U := (isOpen_lt continuous_const (continuous_relativePartition_spectrum hz 1).norm).inter
    (isOpen_lt (continuous_relativeReading (powerResponse q) 1) continuous_const)
  have hb : b ∈ closure (physicalSpectra 1) := by rw [closure_rank_one_spectra]; exact mem_univ _
  obtain ⟨c,hin,hphys⟩ := mem_closure_iff.mp hb U ho (show b ∈ U from ⟨ha,hd⟩)
  exact ⟨c,hphys,hin⟩

/-- Ground attenuation at scale (1+q)S gives a fixed fraction of t/S at moment cost strictly below 1/S. -/
theorem ground_moment_probe (q : GibbsExponent) {σ t S : ℝ} (hs : 0 < σ) (ht : 1 ≤ t) (hS : t ≤ S) :
    ∃ c ∈ physicalSpectra 1, (shortChordFactor σ/(2*(1+q.val)))*(t/S) < ‖relativePartition c (⟨σ,t⟩:ℂ)‖ ∧
      momentLoss q c < 1/S := by
  let R := (1+q.val)*S
  have ht' := zero_lt_one.trans_le ht
  have hSp := ht'.trans_le hS
  have hqpos : 0 < q.val := q.property
  have hscale := add_pos zero_lt_one hqpos
  have hr : S ≤ R := le_mul_of_one_le_left hSp.le (le_add_of_nonneg_right hqpos.le)
  have hRp := hSp.trans_le hr
  let u : Ioc (0:ℝ) 1 := ⟨Real.exp (-(shortStep/R)),Real.exp_pos _,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_pos shortStep_pos hRp).le)⟩
  obtain ⟨b,_,he⟩ := exists_ground_attenuation 0 u
  have hq := he (z := (q.val:ℂ)) q.property
  rw [relativePartition_real b q,← Complex.ofReal_cpow u.property.1.le,← Complex.ofReal_one,← Complex.ofReal_sub] at hq
  have hD : momentLoss q b = 1-Real.exp (-(shortStep/R)*q.val) := by
    rw [Real.exp_mul]
    exact Complex.ofReal_inj.mp hq
  apply physical_moment_probe q (z := ⟨σ,t⟩) hs b
  · rw [he hs]
    have hh := short_chord_lower hs.le ht'.le (ht.trans (hS.trans hr)) (hS.trans hr)
    have hlt := mul_lt_mul_of_pos_right (half_lt_self (shortChordFactor_pos σ)) (div_pos ht' hRp)
    exact (show shortChordFactor σ/(2*(1+q.val))*(t/S) = shortChordFactor σ/2*(t/R) by
      simp only [R,div_eq_mul_inv,mul_inv_rev]; ring).trans_lt (hlt.trans_le hh)
  · rw [hD]
    have hd : shortStep*q.val < 1+q.val :=
      (mul_le_of_le_one_left q.property.le ((min_le_left _ _).trans (by norm_num : (1/4:ℝ)≤1))).trans_lt (lt_one_add _)
    have hb : shortStep/R*q.val < 1/S := by
      calc
        _ = (shortStep*q.val)/R := by ring
        _ < (1+q.val)/R := div_lt_div_of_pos_right hd hRp
        _ = 1/S := by dsimp only [R]; field_simp [hscale.ne']
    linarith only [Real.add_one_le_exp (-(shortStep/R)*q.val),hb]

/-- A coherent subset of any admissible tail block retains a quarter of its total chord length. Its entire prefix stays fixed. -/
theorem coherent_tail_profile {z : ℂ} (N : ℕ) (F : Finset ℕ) (hF : ∀ k ∈ F, N ≤ k) (x : ℕ → ℝ)
    (hx : ∀ k ∈ F, x k ∈ Icc (occupationWeight (k+1)) (occupationWeight k)) :
    ∃ b : SpectralBand 1, (∀ k < N, (b k).val = occupationWeight k) ∧
      (∑ k ∈ F, ‖(occupationWeight k:ℂ)^z-(x k:ℂ)^z‖) ≤ 4*‖relativePartition b z‖ := by
  obtain ⟨S,hS,hv⟩ := exists_complex_subset F (fun k => (occupationWeight k:ℂ)^z-(x k:ℂ)^z)
  refine ⟨finiteProfile S x (fun k hk => hx k (hS hk)),?_,?_⟩
  · intro k hk
    have hnot : k ∉ S := fun h => hk.not_ge (hF k (hS h))
    simp only [finiteProfile,dif_neg hnot,hotEdge]
  · rwa [finiteProfile_partition]

#print axioms ground_moment_probe
#print axioms coherent_tail_profile

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
