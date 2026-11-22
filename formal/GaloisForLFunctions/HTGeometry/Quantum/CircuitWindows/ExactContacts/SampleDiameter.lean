import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.ConsecutiveSamples
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.PhasePolynomial
import GaloisForLFunctions.HTGeometry.SubwindingChordComparison

/-! # A lower bound on the amplitude in every short interval -/
open Real Set
namespace GaloisForLFunctions.HTGeometry.ExactContacts
noncomputable section

private theorem norm_phase (w t : ℝ) : ‖energyPhase w t‖ = 1 := by
  simp [energyPhase,Complex.norm_exp]

private theorem phase_shift (w a h : ℝ) (q : ℕ) :
    energyPhase w (a+(q:ℝ)*h) = energyPhase w a*(energyPhase w h)^q := by
  simp only [energyPhase,←Complex.exp_nat_mul,←Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem chord_floor (a b h : ℝ) (hh : 0≤h) (hs : |a-b| * h≤π) :
    (|a-b|/(π/2))*h ≤ ‖energyPhase a h-energyPhase b h‖ := by
  have hr : 2*π-π=π := by ring
  have he (w : ℝ) : energyPhase w h=Complex.exp (-((w*h:ℝ):ℂ)*Complex.I) := by
    unfold energyPhase
    congr 1
    push_cast
    ring
  have hd : |a*h-b*h|=|a-b| * h := by rw [←sub_mul,abs_mul,abs_of_nonneg hh]
  have hc := abs_sub_le_chord pi_pos (by linarith only [pi_pos] : π<2*π)
    (show |a*h-b*h|≤2*π-π by rwa [hd,hr])
  rw [hr,sin_pi_div_two,mul_one,hd] at hc
  rw [he,he,div_mul_eq_mul_div,(div_le_iff₀ (half_pos pi_pos)),mul_comm _ (π/2)]
  exact hc

variable {I : Type*} [DecidableEq I]

/-- For any nonzero coefficient the neighboring frequencies give a
positive amplitude floor proportional to h to the number of competitors.
The starting time is unrestricted. -/
theorem exponential_sample_floor (J : Finset I) (c : I → ℂ) (w : I → ℝ)
    {i : I} (hi : i∈J) (hc : c i≠0) (hw : Set.InjOn w J) :
    ∃ κ H : ℝ, 0<κ ∧ 0<H ∧ ∀ (a h δ : ℝ), 0≤h → h≤H →
      (∀ q < J.card, ‖RHTower.expSum_exponentialSumMeanSquareLower J c w (a+(q:ℝ)*h)‖ ≤ δ) →
      κ*h^(J.card-1) ≤ δ := by
  let S := J.erase i
  let g (l : I) := |w i-w l|/(π/2)
  let R := 1+∑ l ∈ J, |w i-w l|
  have hR : 0<R := by dsimp only [R]; positivity
  have hg (l : I) (hl : l∈S) : 0<g l := by
    have hne := Finset.mem_erase.mp hl
    exact div_pos (abs_pos.mpr (sub_ne_zero.mpr fun he => hne.1 ((hw hi hne.2 he).symm))) (half_pos pi_pos)
  let B := ‖c i‖*∏ l ∈ S, g l
  have hB : 0<B := mul_pos (norm_pos_iff.mpr hc) (Finset.prod_pos hg)
  refine ⟨B/2^(J.card-1),π/R,div_pos hB (by positivity),div_pos pi_pos hR,?_⟩
  intro a h δ h0 hh hδ
  have hd (l : I) (hl : l∈S) : g l*h ≤ ‖energyPhase (w i) h-energyPhase (w l) h‖ := by
    have hle : |w i-w l|≤R := by
      have hsum := Finset.single_le_sum (f:=fun j => |w i-w j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_of_mem_erase hl)
      dsimp [R]
      linarith only [hsum]
    apply chord_floor _ _ _ h0
    exact (mul_le_mul_of_nonneg_right hle h0).trans (by simpa only [mul_comm R h] using (le_div_iff₀ hR).mp hh)
  have hprod := Finset.prod_le_prod (fun l hl => mul_nonneg (hg l hl).le h0) hd
  have hn := consecutive_sample_bound J (fun l => c l*energyPhase (w l) a) (fun l => energyPhase (w l) h) hi
    (fun l => (norm_phase (w l) h).le) (δ:=δ) (fun q hq => by
      have hsample := hδ q hq
      change ‖∑ l ∈ J, c l*energyPhase (w l) (a+(q:ℝ)*h)‖ ≤ δ at hsample
      simpa only [phase_shift,←mul_assoc] using hsample)
  rw [norm_mul,norm_phase,mul_one] at hn
  rw [Finset.prod_mul_distrib,Finset.prod_const,show S.card=J.card-1 from Finset.card_erase_of_mem hi] at hprod
  rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : (0:ℝ)<2^(J.card-1)),mul_comm δ]
  exact (show B*h^(J.card-1) = ‖c i‖*((∏ l ∈ S, g l)*h^(J.card-1)) by dsimp only [B]; ring).trans_le
    ((mul_le_mul_of_nonneg_left hprod (norm_nonneg _)).trans hn)

#print axioms exponential_sample_floor
end
end GaloisForLFunctions.HTGeometry.ExactContacts
