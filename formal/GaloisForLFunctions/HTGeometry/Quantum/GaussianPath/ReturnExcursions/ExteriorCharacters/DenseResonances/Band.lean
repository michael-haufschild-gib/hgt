import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.DenseResonances.Detuning
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.DenseResonances.Scale

/-! # Compulsory dense resonances for spectra of polynomial width -/

open Finset Filter
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances
noncomputable section

/-- Number of inverse-width bins for half the levels of a linear-width
band, at widths up to twice the specified horizon. -/
theorem bin_cap {n : ℕ} {w A C : ℝ} (hA : 0≤A) (hAC : A≤C*(4*n))
    (hw : 0≤w) (hw' : w≤2*(11/10:ℝ)^(4*n)) :
    ((⌊w*(2*(2*n:ℕ)*A)⌋₊+1:ℕ):ℝ)≤1+2*C*(4*n)^2*(11/10:ℝ)^(4*n) := by
  have hfloor : ((⌊w*(2*(2*n:ℕ)*A)⌋₊:ℕ):ℝ)≤w*(2*(2*n:ℕ)*A) :=
    Nat.floor_le (by positivity)
  have hprod := mul_le_mul hw' hAC hA (by positivity)
  have hm := mul_le_mul_of_nonneg_left hprod (show 0≤4*(n:ℝ) by positivity)
  push_cast at hfloor ⊢
  nlinarith only [hm,hfloor]

/-- Every spectrum of dimension $D=4n$ in a linear-width band has more
than any fixed multiple of the target number of broad-support pairs at
the resolution of the original elapsed window. -/
theorem band_resonances (C M : ℝ) (hM : 0≤M) :
    ∀ᶠ n : ℕ in atTop, ∀ {I : Type} [Fintype I] [DecidableEq I], Fintype.card I=4*n →
    ∀ (E : I → ℝ) (A w : ℝ), 0≤A → A≤C*(4*n) → (∀ i, |E i|≤A) →
    0≤w → w≤2*(11/10:ℝ)^(4*n) →
    let F := (univ : Finset I).powersetCard (2*n)
    let x (S : Finset I) := ∑ i ∈ S, E i
    M*((4*n).choose (2*n):ℝ)^2*(9/10)^(4*n) <
      (pairCount F n (fun S T => |w*(x S-x T)|≤1):ℝ) := by
  filter_upwards [many_collisions C M hM] with n hscale
  intro I _ _ hd E A w hA hAC hE hw hw' F x
  let b := (⌊w*(2*(2*n:ℕ)*A)⌋₊+1:ℕ)
  have h := subset_sum_count E A n (2*n) w hw hE
  rw [hd] at h
  exact hscale _ b (Nat.cast_nonneg _) (bin_cap hA hAC hw hw') h

#print axioms band_resonances
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances
