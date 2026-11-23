import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InterlacingConverse.PrescribedModes
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InterlacingConverse.BandPlacement

/-! # The full interlacing band is the physical closure at missing dimension one -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set

/-- Every strictly interlacing finite prescription is realized at its exact indices in the physical closure. -/
theorem realize_strict_prefix {m : ℕ} (x : Fin m → ℝ)
    (hx : ∀ j, occupationWeight (j.val+1) < x j ∧ x j < occupationWeight j.val) :
    ∃ b ∈ closure (physicalSpectra 1), ∀ j : Fin m, (b j.val).val = x j := by
  obtain ⟨v,hv,he⟩ := exists_prescribed_line x hx
  have hn := norm_ne_zero_iff.mp (hv.trans_ne one_ne_zero)
  obtain ⟨b,hb,hd⟩ := spectral_limit_of_square_limit (line_square_mem_physical_closure hn)
  refine ⟨b,hb,fun j => ?_⟩
  obtain ⟨y,hy,heig⟩ := he j
  exact line_gap_index v hd (hx j) hy heig

private theorem strict_profile_mem (b : SpectralBand 1)
    (hb : ∀ k, occupationWeight (k+1) < (b k).val ∧ (b k).val < occupationWeight k) :
    b ∈ closure (physicalSpectra 1) := by
  choose c hc he using fun m => realize_strict_prefix (fun j : Fin m => (b j.val).val) (fun j => hb j.val)
  apply isClosed_closure.mem_of_tendsto (f := c) (b := atTop) _ (Eventually.of_forall hc)
  apply tendsto_pi_nhds.mpr
  intro k
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop k] with m hm
  exact Subtype.ext (he m ⟨k,hm⟩).symm

private def midpoint (k : ℕ) := (occupationWeight (k+1)+occupationWeight k)/2

private theorem midpoint_strict (k : ℕ) : occupationWeight (k+1) < midpoint k ∧ midpoint k < occupationWeight k := by
  have he := occupationWeight_strictAnti (Nat.lt_succ_self k)
  dsimp only [midpoint]
  constructor <;> linarith only [he]

private def interiorWeight (b : SpectralBand 1) (n k : ℕ) :=
  (1-occupationWeight n)*(b k).val + occupationWeight n * midpoint k

private theorem interiorWeight_strict (b : SpectralBand 1) (n k : ℕ) :
    occupationWeight (k+1) < interiorWeight b n k ∧ interiorWeight b n k < occupationWeight k := by
  let t := occupationWeight n
  have ht : 0 < t := occupationWeight_pos _
  have hu : 0 ≤ 1-t := sub_nonneg.mpr (occupation_in_unit n).2
  have he (u : ℝ) : (1-t)*u+t*u = u := by ring
  constructor
  · exact (he _).symm.trans_lt (add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left (b k).property.1 hu)
      (mul_lt_mul_of_pos_left (midpoint_strict k).1 ht))
  · exact (add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left (b k).property.2 hu)
      (mul_lt_mul_of_pos_left (midpoint_strict k).2 ht)).trans_eq (he _)

/-- One omitted direction suffices for coordinatewise approximation of every allowed spectrum, including simultaneous endpoint choices. -/
theorem closure_rank_one_spectra : closure (physicalSpectra 1) = univ := by
  apply eq_univ_of_forall
  intro b
  let c (n : ℕ) : SpectralBand 1 := fun k => ⟨interiorWeight b n k,(interiorWeight_strict b n k).1.le,
    (interiorWeight_strict b n k).2.le⟩
  have hc (n : ℕ) := strict_profile_mem (c n) (interiorWeight_strict b n)
  apply isClosed_closure.mem_of_tendsto (f := c) (b := atTop) _ (Eventually.of_forall hc)
  apply tendsto_pi_nhds.mpr
  intro k
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun n => (1-occupationWeight n)*(b k).val+occupationWeight n*midpoint k) atTop (𝓝 (b k).val)
  simpa only [sub_zero,one_mul,zero_mul,add_zero] using
    ((occupationWeight_tendsto.const_sub 1).mul_const (b k).val).add (occupationWeight_tendsto.mul_const (midpoint k))

#print axioms realize_strict_prefix
#print axioms closure_rank_one_spectra

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
