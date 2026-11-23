import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockStability.CalibratedSampling

/-! # Recovery from noisy data with independently corrupted samples -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

private theorem exists_clean_index (bad : Finset ℕ) {k : ℕ} (hk : bad.card ≤ k) (m : ℕ) :
    ∃ j ≤ k, m+j ∉ bad := by
  by_contra! h
  have hi : Function.Injective (fun j : ℕ => m+j) := fun _ _ he => Nat.add_left_cancel he
  have hs : (Finset.range (k+1)).image (fun j => m+j) ⊆ bad := by
    intro a ha
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ha
    exact h j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hi,Finset.card_range] at hc
  omega

/-- A candidate agrees with the recorded clock and with its trusted complex readings in a finite window. -/
def fitsReadings {l u : ℝ} {r : ℕ} (p : ClockState l u r) (clock : ℝ) (y : ℕ → ℂ)
    (start last : ℕ) (bad : Finset ℕ) (η : ℝ) : Prop :=
  |p.1.val-clock| ≤ η ∧ ∀ n, start ≤ n → n ≤ last → n ∉ bad →
    ‖clockReading p.1.val p.2 n - y n‖ ≤ η

/-- Two candidates may discard different observations. Uniform error control survives k discarded readings per candidate. -/
theorem noisy_clock_stability (r : ℕ) (l u : ℝ) (f : SpectralResponse) {ε : ℝ} (hε : 0 < ε)
    (start k : ℕ) :
    ∃ N : ℕ, ∀ (p q : ClockState l u r) (clock : ℝ) (y : ℕ → ℂ) (B C : Finset ℕ),
      B.card ≤ k → C.card ≤ k →
      fitsReadings p clock y start (start+N+2*k) B (occupationWeight N/2) →
      fitsReadings q clock y start (start+N+2*k) C (occupationWeight N/2) →
      detectorError f p.2.val q.2.val < ε := by
  obtain ⟨N,hN⟩ := finite_clock_stability r l u f hε start (2*k)
  refine ⟨N,fun p q clock y B C hB hC hp hq => ?_⟩
  apply hN p q
  · have ht := abs_sub_le p.1.val clock q.1.val
    rw [abs_sub_comm clock q.1.val] at ht
    linarith only [ht,hp.1,hq.1]
  · intro m hm
    have hcard : (B ∪ C).card ≤ 2*k :=
      (Finset.card_union_le _ _).trans (by omega)
    obtain ⟨j,hj,hclean⟩ := exists_clean_index (B ∪ C) hcard (start+m)
    let n := start+m+j
    have hlow : start ≤ n := by dsimp [n]; omega
    have hhigh : n ≤ start+N+2*k := by dsimp [n]; omega
    have hp' := hp.2 n hlow hhigh (fun h => hclean (Finset.mem_union_left _ h))
    have hq' := hq.2 n hlow hhigh (fun h => hclean (Finset.mem_union_right _ h))
    refine ⟨j,hj,?_⟩
    have ht := dist_triangle (clockReading p.1.val p.2 n) (y n) (clockReading q.1.val q.2 n)
    rw [dist_comm (y n) (clockReading q.1.val q.2 n)] at ht
    simp only [dist_eq_norm] at ht
    change ‖clockReading p.1.val p.2 n - clockReading q.1.val q.2 n‖ ≤ _
    linarith only [ht,hp',hq']

#print axioms noisy_clock_stability

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
