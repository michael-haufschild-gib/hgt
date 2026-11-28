import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass.Bins
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass.Scale
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.DenseResonances.Band

/-! # Phase-uniform positive resonant mass for bounded spectra -/

open Finset Filter
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass
noncomputable section

/-- All midpoint phases are allowed. Only the total absolute minor weight
at a tenth-error fit enters the positive real lower bound. -/
theorem positive_band (C M : ℝ) (hM : 0≤M) :
    ∀ᶠ n : ℕ in atTop, ∀ {I : Type} [Fintype I] [DecidableEq I], Fintype.card I=4*n →
      ∀ (E : I → ℝ) (A w : ℝ), 0≤A → A≤C*(4*n) → (∀ i, |E i|≤A) →
      0≤w → w≤2*(11/10:ℝ)^(4*n) →
      let F := (univ : Finset I).powersetCard (2*n)
      let B : ℝ := (4*n).choose (2*n)
      ∀ a : Finset I → ℂ, (∀ S∈F, ‖a S‖≤1) → B*(199/200)^(2*n)≤∑ S ∈ F, ‖a S‖ →
        M*B^2*(9/10)^(4*n)<positiveWindow F a (fun S => ∑ i ∈ S, E i) n w := by
  filter_upwards [positive_mass_price C M hM] with n hn
  intro I _ _ hd E A w hA hAC hE hw hw' F B a ha hmass
  let q := 2*n
  let b := (⌊w*(2*(q:ℝ)*A)⌋₊+1:ℕ)
  have ht := positive_bin_bound F a (fun S => ∑ i ∈ S, E i) n (-(q*A)) (q*A) w hw
    (fun _ hS => subset_mem_band E hE hS) ha
  have hc : (F.card:ℝ)=B := by simp only [F,B,card_powersetCard,card_univ,hd]
  rw [hc,hd,show (q:ℝ)*A- -(q*A)=2*q*A by ring] at ht
  have hm := pow_le_pow_left₀ (show 0≤B*(199/200:ℝ)^(2*n) by dsimp only [B]; positivity) hmass 2
  rw [mul_pow,←pow_mul,show 2*n*2=4*n by omega] at hm
  exact hn b _ (Nat.cast_nonneg _) (bin_cap hA hAC hw hw') (hm.trans ht)

#print axioms positive_band
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass
