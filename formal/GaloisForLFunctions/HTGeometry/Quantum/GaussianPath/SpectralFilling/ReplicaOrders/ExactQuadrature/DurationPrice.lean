import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.Diameter
import GaloisForLFunctions.RHTower.Sieve.SeparatedCount

/-! # Bandwidth lower bound for exact positive spectral quadrature -/
open Finset Real
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
noncomputable section
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

/-- Exact orthogonality separates every pair of energies after scaling
by the record duration. Counting those separated energies charges the
full number of resolved levels against bandwidth times duration. -/
theorem duration_price (E : I → ℝ) (p t : J → ℝ) (hp : ∀ j, 0≤p j) (hm : ∑ j, p j=1)
    {a b u v : ℝ} (hab : a≤b) (huv : u≤v) (hr : ∀ j, t j∈Set.Icc a b)
    (hE : ∀ i, E i∈Set.Icc u v)
    (hg : ∀ i k, i≠k → ∑ j, (p j:ℂ)*wave (E i-E k) (t j)=0) :
    π*((Fintype.card I:ℝ)-1) ≤ (b-a)*(v-u) := by
  have hT := sub_nonneg.mpr hab
  let F (i : I) := (b-a)*E i
  have hsep (i k : I) (hne : i≠k) : π≤|F i-F k| := by
    have hdiff : E i≠E k := by
      intro he
      have hh := hg i k hne
      rw [he,sub_self] at hh
      simp only [wave,zero_mul,Complex.ofReal_zero,Complex.exp_zero,mul_one,←Complex.ofReal_sum,hm,
        Complex.ofReal_one,one_ne_zero] at hh
    rw [show F i-F k=(b-a)*(E i-E k) by dsimp only [F]; ring,abs_mul,abs_of_nonneg hT]
    rcases lt_or_gt_of_ne hdiff with h|h
    · rw [abs_of_neg (sub_neg.mpr h),neg_sub,mul_comm]
      exact half_period_floor p t hp hm (sub_pos.mpr h) hr (hg k i hne.symm)
    · rw [abs_of_pos (sub_pos.mpr h),mul_comm]
      exact half_period_floor p t hp hm (sub_pos.mpr h) hr (hg i k hne)
  have hcount := RHTower.Sieve.card_le_of_separated (s:=univ) (u:=F) (c:=(b-a)*u)
    pi_pos (mul_nonneg hT (sub_nonneg.mpr huv)) (fun i _ k _ => hsep i k) (fun i _ =>
      ⟨mul_le_mul_of_nonneg_left (hE i).1 hT,(mul_le_mul_of_nonneg_left (hE i).2 hT).trans_eq (by ring)⟩)
  rw [card_univ] at hcount
  have h := mul_le_mul_of_nonneg_right hcount pi_pos.le
  rw [add_mul,div_mul_cancel₀ _ pi_ne_zero,one_mul] at h
  linarith only [h]

#print axioms duration_price
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
