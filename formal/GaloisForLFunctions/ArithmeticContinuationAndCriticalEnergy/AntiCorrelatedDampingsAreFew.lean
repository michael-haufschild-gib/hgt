import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.RelativeStabilityOfTheTangentFamily
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.ThePronicDilationContractionAndItsThreshold

/-!
# Anti-correlated dampings are few

The damping autocorrelation is the Gram kernel of one family of vectors, so it inherits every
constraint a Gram matrix carries.  The sharpest elementary one bounds how many vectors can be
pairwise obtuse: if `m` unit vectors are pairwise at correlation at most `−δ`, then

`0 ≤ ‖Σ v_i‖² ≤ m − m(m−1) δ`,  hence  `m ≤ 1 + 1/δ`.

Transported to the tangent family this says: at most `1 + 1/δ` dampings can be pairwise
`δ`-anti-correlated relative to their sizes (`card_le_of_pairwise_anticorrelated`).  The obstruction
to backward continuation — negative autocorrelation — therefore cannot persist across many dampings:
strong anti-correlation is a *finite* phenomenon in the damping parameter, with an explicit bound
depending only on the strength.

Combined with the averaged criterion, where only the damping average of the relative loss has to be
bounded, this constrains the obstruction to a set of dampings whose size is controlled by how
strongly the tangents are anti-aligned.
-/

open Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The Gram expansion of a finite sum of rows -/

theorem pronicNorm_sum_sq {T : ℕ} (s : Finset ℝ) (u : ℝ → ℕ → ℝ) :
    pronicNorm T (fun n => ∑ η ∈ s, u η n) ^ 2 =
      ∑ η ∈ s, ∑ ε ∈ s, pronicPairing T (u η) (u ε) := by
  rw [pronicNorm_sq]
  have hcell : ∀ n ∈ Finset.Icc 1 T,
      (∑ η ∈ s, u η n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
        ∑ η ∈ s, ∑ ε ∈ s, u η n * u ε n / ((n : ℝ) * ((n : ℝ) + 1)) := by
    intro n _
    rw [sq, Finset.sum_mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun η _ => by rw [Finset.sum_div]
  rw [Finset.sum_congr rfl hcell, Finset.sum_comm]
  refine Finset.sum_congr rfl fun η _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ε _ => by rw [pronicPairing]

theorem pronicPairing_div {T : ℕ} (u v : ℕ → ℝ) {a b : ℝ} :
    pronicPairing T (fun n => u n / a) (fun n => v n / b) =
      pronicPairing T u v / (a * b) := by
  unfold pronicPairing
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun n _ => by ring

/-! ## §2. Pairwise anti-correlated dampings are few -/

/-- **At most `1 + 1/δ` dampings are pairwise `δ`-anti-correlated.**  The tangents form a Gram
family, and pairwise obtuse families are finite. -/
theorem card_le_of_pairwise_anticorrelated {T : ℕ} {δ : ℝ} (hδ : 0 < δ) (s : Finset ℝ)
    (hpos : ∀ η ∈ s, 0 < pronicNorm T (dampedChebyshevError η))
    (hanti : ∀ η ∈ s, ∀ ε ∈ s, η ≠ ε →
      tangentCorrelation T η ε ≤
        -δ * (pronicNorm T (dampedChebyshevError η) *
          pronicNorm T (dampedChebyshevError ε))) :
    (s.card : ℝ) ≤ 1 + 1 / δ := by
  classical
  set u : ℝ → ℕ → ℝ := fun η n =>
    dampedChebyshevError η n / pronicNorm T (dampedChebyshevError η) with hu
  -- the normalised tangents have unit energy and pairwise correlation at most `−δ`
  have hdiag : ∀ η ∈ s, pronicPairing T (u η) (u η) = 1 := by
    intro η hη
    have hn := hpos η hη
    rw [hu, pronicPairing_div, ← tangentCorrelation, tangentCorrelation_self]
    field_simp
  have hoff : ∀ η ∈ s, ∀ ε ∈ s, η ≠ ε → pronicPairing T (u η) (u ε) ≤ -δ := by
    intro η hη ε hε hne
    have hnη := hpos η hη
    have hnε := hpos ε hε
    have hprod : 0 < pronicNorm T (dampedChebyshevError η) *
        pronicNorm T (dampedChebyshevError ε) := mul_pos hnη hnε
    rw [hu, pronicPairing_div, ← tangentCorrelation, div_le_iff₀ hprod]
    have h := hanti η hη ε hε hne
    linarith
  -- the Gram expansion of the sum of the normalised tangents
  have hexp := pronicNorm_sum_sq (T := T) s u
  have hnonneg : 0 ≤ pronicNorm T (fun n => ∑ η ∈ s, u η n) ^ 2 := sq_nonneg _
  have hsplit : (∑ η ∈ s, ∑ ε ∈ s, pronicPairing T (u η) (u ε)) ≤
      (s.card : ℝ) - δ * ((s.card : ℝ) * ((s.card : ℝ) - 1)) := by
    have hrow : ∀ η ∈ s, (∑ ε ∈ s, pronicPairing T (u η) (u ε)) ≤
        1 - δ * ((s.card : ℝ) - 1) := by
      intro η hη
      have hdecomp : (∑ ε ∈ s, pronicPairing T (u η) (u ε)) =
          pronicPairing T (u η) (u η) +
            ∑ ε ∈ s.erase η, pronicPairing T (u η) (u ε) := by
        rw [← Finset.add_sum_erase s _ hη]
      rw [hdecomp, hdiag η hη]
      have hbound : (∑ ε ∈ s.erase η, pronicPairing T (u η) (u ε)) ≤
          ∑ _ε ∈ s.erase η, (-δ) := by
        refine Finset.sum_le_sum fun ε hε => ?_
        exact hoff η hη ε (Finset.mem_of_mem_erase hε) (Ne.symm (Finset.ne_of_mem_erase hε))
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hη] at hbound
      have hcard : ((s.card - 1 : ℕ) : ℝ) = (s.card : ℝ) - 1 := by
        have h1 : 1 ≤ s.card := Finset.card_pos.mpr ⟨η, hη⟩
        push_cast [h1]
        ring
      rw [hcard] at hbound
      linarith
    have hsum := Finset.sum_le_sum hrow
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    calc (∑ η ∈ s, ∑ ε ∈ s, pronicPairing T (u η) (u ε))
        ≤ (s.card : ℝ) * (1 - δ * ((s.card : ℝ) - 1)) := hsum
      _ = (s.card : ℝ) - δ * ((s.card : ℝ) * ((s.card : ℝ) - 1)) := by ring
  rw [hexp] at hnonneg
  have hcard0 : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos'
  · rw [h0]
    push_cast
    have : 0 < 1 / δ := by positivity
    linarith
  · have hc1 : (1 : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hpos'
    have hkey : δ * ((s.card : ℝ) * ((s.card : ℝ) - 1)) ≤ (s.card : ℝ) := by linarith
    have hm0 : (0 : ℝ) < (s.card : ℝ) := by linarith
    have hstep : δ * ((s.card : ℝ) - 1) ≤ 1 := by nlinarith [hkey, hm0]
    have hfinal : (s.card : ℝ) - 1 ≤ 1 / δ := by
      rw [le_div_iff₀ hδ]
      linarith
    linarith

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
