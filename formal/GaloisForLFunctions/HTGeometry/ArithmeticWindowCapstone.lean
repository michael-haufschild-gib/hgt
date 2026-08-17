import GaloisForLFunctions.HTGeometry.PeriodicTentPacket
import GaloisForLFunctions.HTGeometry.SpectralFormConjugateBound

/-!
# The arithmetic moving-window law

The frequency a packet mode carries along an algebraic spectrum is the distinguished embedding of an
integer spectral form.  Liouville separation therefore bounds every nonconstant mode away from zero,
uniformly in the mode, by `(2dNR)^{-(n-1)}`; and that uniform separation is exactly the hypothesis
the moving-window estimate consumes.

The result is a moving-window law with no genericity and no first-hit argument: once the Fejér order
and the window length pass two explicit thresholds, *every* window of that length spends at least
half the cube's Haar measure of its length inside the cube.
-/

open Real NumberField MeasureTheory

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Capstone

variable {K : Type*} [Field K] [NumberField K] {d : ℕ}

theorem mem_diagPairs_of_eq {N : ℕ} {pq : ℕ × ℕ}
    (hmem : pq ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1)) (heq : pq.1 = pq.2) :
    pq ∈ diagPairs N := by
  rw [Finset.mem_product] at hmem
  rw [diagPairs, Finset.mem_image]
  refine ⟨pq.1, hmem.1, ?_⟩
  ext
  · rfl
  · exact heq

/-- **The mode frequency is an embedded spectral form.** -/
theorem packetFreq_eq_embedding (E : Fin (d + 1) → 𝓞 K) (σ₀ : K →+* ℂ) (ω : Fin d → ℝ)
    (hω : ∀ j, ((ω j : ℝ) : ℂ) = σ₀ ((E j.succ : 𝓞 K) : K) - σ₀ ((E 0 : 𝓞 K) : K))
    (k : Fin d → ℕ × ℕ) :
    ((packetFreq ω k : ℝ) : ℂ)
      = σ₀ ((spectralForm E (fun j => ((k j).1 : ℤ) - ((k j).2 : ℤ)) : 𝓞 K) : K) := by
  classical
  rw [embedding_spectralForm, packetFreq]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hω j]

/-- **The uniform separation of the nonconstant modes.**  Every mode outside the diagonal carries a
frequency at least `(2dNR)^{-(n-1)}` in modulus. -/
theorem inv_pow_le_abs_packetFreq (E : Fin (d + 1) → 𝓞 K) (σ₀ : K →+* ℂ) (ω : Fin d → ℝ)
    (hω : ∀ j, ((ω j : ℝ) : ℂ) = σ₀ ((E j.succ : 𝓞 K) : K) - σ₀ ((E 0 : 𝓞 K) : K))
    {N : ℕ} {R : ℝ} (hR : ∀ (τ : K →+* ℂ) (i : Fin (d + 1)), ‖τ ((E i : 𝓞 K) : K)‖ ≤ R)
    (hpos : 0 < 2 * (d : ℝ) * (N : ℝ) * R)
    (hindep : ∀ m : Fin d → ℤ, m ≠ 0 → spectralForm E m ≠ 0)
    {k : Fin d → ℕ × ℕ}
    (hk : k ∈ (Fintype.piFinset fun _ : Fin d => Finset.range (N + 1) ×ˢ Finset.range (N + 1))
      \ Fintype.piFinset (fun _ : Fin d => diagPairs N)) :
    ((2 * (d : ℝ) * (N : ℝ) * R) ^ (Fintype.card (K →+* ℂ) - 1))⁻¹ ≤ |packetFreq ω k| := by
  classical
  rw [Finset.mem_sdiff] at hk
  obtain ⟨hk1, hk2⟩ := hk
  have hmem : ∀ j, k j ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1) :=
    fun j => Fintype.mem_piFinset.mp hk1 j
  -- coefficient bound
  have hkN : ∀ j, |(((((k j).1 : ℤ) - ((k j).2 : ℤ)) : ℤ) : ℝ)| ≤ (N : ℝ) := by
    intro j
    have h := hmem j
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at h
    have h1 : ((k j).1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp h.1
    have h2 : ((k j).2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp h.2
    have h1' : (0 : ℝ) ≤ ((k j).1 : ℝ) := by positivity
    have h2' : (0 : ℝ) ≤ ((k j).2 : ℝ) := by positivity
    push_cast
    rw [abs_le]
    constructor <;> linarith
  -- nonvanishing
  have hne : spectralForm E (fun j => ((k j).1 : ℤ) - ((k j).2 : ℤ)) ≠ 0 := by
    refine hindep _ ?_
    intro hzero
    refine hk2 (Fintype.mem_piFinset.mpr fun j => ?_)
    have hj : ((k j).1 : ℤ) - ((k j).2 : ℤ) = 0 := congrFun hzero j
    exact mem_diagPairs_of_eq (hmem j) (by omega)
  have hbound := inv_pow_le_norm_embedding_spectralForm E
    (fun j => ((k j).1 : ℤ) - ((k j).2 : ℤ)) hkN hR hpos hne σ₀
  have hfreq : |packetFreq ω k|
      = ‖σ₀ ((spectralForm E (fun j => ((k j).1 : ℤ) - ((k j).2 : ℤ)) : 𝓞 K) : K)‖ := by
    rw [← packetFreq_eq_embedding E σ₀ ω hω k, Complex.norm_real, Real.norm_eq_abs]
  rw [hfreq]
  exact hbound

/-- **Theorem A.**  On an algebraic spectrum with all conjugates below `R` and no integer relation
among the anchored gaps, every moving window whose length passes the displayed threshold spends at
least half the cube's Haar measure of its length inside the cube. -/
theorem half_mul_le_measureReal_cubeVisit_of_algebraic (E : Fin (d + 1) → 𝓞 K) (σ₀ : K →+* ℂ)
    (ω : Fin d → ℝ)
    (hω : ∀ j, ((ω j : ℝ) : ℂ) = σ₀ ((E j.succ : 𝓞 K) : K) - σ₀ ((E 0 : 𝓞 K) : K))
    {N : ℕ} {R ρ T : ℝ} (hρ : 0 < ρ) (hρπ : ρ ≤ π) (c : Fin d → ℝ)
    (hR : ∀ (τ : K →+* ℂ) (i : Fin (d + 1)), ‖τ ((E i : 𝓞 K) : K)‖ ≤ R)
    (hpos : 0 < 2 * (d : ℝ) * (N : ℝ) * R)
    (hindep : ∀ m : Fin d → ℤ, m ≠ 0 → spectralForm E m ≠ 0)
    (hT : 0 < T) (u : ℝ)
    (hNbig : 8 * π * (d : ℝ) ≤ ρ * (ρ / (2 * π)) ^ d * Real.sqrt ((N : ℝ) + 1))
    (hTbig : 8 * ((N : ℝ) + 1) ^ d
      ≤ T * ((2 * (d : ℝ) * (N : ℝ) * R) ^ (Fintype.card (K →+* ℂ) - 1))⁻¹) :
    ((ρ / (2 * π)) ^ d / 2) * T
      ≤ (volume (cubeVisit ρ c ω ∩ Set.Ioc u (u + T))).toReal := by
  have hβpos : (0 : ℝ) < ((2 * (d : ℝ) * (N : ℝ) * R) ^ (Fintype.card (K →+* ℂ) - 1))⁻¹ := by
    positivity
  exact half_mul_le_measureReal_cubeVisit N hρ hρπ c ω hβpos hT u
    (fun k hk => inv_pow_le_abs_packetFreq E σ₀ ω hω hR hpos hindep hk) hNbig hTbig

end Capstone

end

end GaloisForLFunctions.HTGeometry
