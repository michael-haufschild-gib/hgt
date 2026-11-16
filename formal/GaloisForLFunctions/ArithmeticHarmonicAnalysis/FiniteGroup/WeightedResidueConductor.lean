import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.WeightedResidueGaps

/-!
# The conductor bound from complete residue weights

A missing integer lies at least one full modulus below the weight in
its residue class. Uniform upper bounds for the weights therefore give
conductor bounds. The last possible gap occurs exactly when some weight
attains the upper bound.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {N : ℕ} (hN : 0 < N) (D : Fin N → ℕ)
    (hresidue : ∀ i j, D i % N = D j % N → i = j)

include hN hresidue in
private theorem residue_exists (m : ℕ) : ∃ i : Fin N, D i % N = m % N := by
  let ρ : Fin N → Fin N := fun i => ⟨D i % N, Nat.mod_lt _ hN⟩
  have hρ : Function.Injective ρ := fun i j h => hresidue i j (congrArg Fin.val h)
  obtain ⟨i, hi⟩ := (Finite.surjective_of_injective hρ) ⟨m % N, Nat.mod_lt _ hN⟩
  exact ⟨i, congrArg Fin.val hi⟩

include hresidue in
/-- An integer is missing exactly when it precedes the weight representing its residue class. -/
theorem weightedResidueGap_iff_lt_weight (m : ℕ) (i : Fin N)
    (hi : D i % N = m % N) :
    (¬ ∃ j : Fin N, ∃ k : ℕ, N * k + D j = m) ↔ m < D i := by
  constructor
  · intro h
    by_contra hlt
    have hle : D i ≤ m := Nat.le_of_not_gt hlt
    have hdiv : D i / N ≤ m / N := Nat.div_le_div_right hle
    apply h
    refine ⟨i, m / N - D i / N, ?_⟩
    calc
      N * (m / N - D i / N) + D i =
          N * (m / N - D i / N) + (N * (D i / N) + D i % N) := by rw [Nat.div_add_mod]
      _ = N * ((m / N - D i / N) + D i / N) + D i % N := by ring
      _ = N * (m / N) + m % N := by rw [Nat.sub_add_cancel hdiv, hi]
      _ = m := Nat.div_add_mod _ _
  · rintro hlt ⟨j, k, hj⟩
    have hmod := congrArg (fun t => t % N) hj
    rw [Nat.mul_add_mod_self_left] at hmod
    have heq := hresidue j i (hmod.trans hi.symm)
    subst j
    have hle : D i ≤ N * k + D i := Nat.le_add_left _ _
    omega

include hN in
private theorem gap_step (m : ℕ) (i : Fin N) (hi : D i % N = m % N)
    (hm : m < D i) : m + N ≤ D i := by
  have hd := Nat.div_add_mod (D i) N
  have hmd := Nat.div_add_mod m N
  have hmul : N * (m / N) < N * (D i / N) := by omega
  have hdiv := (Nat.mul_lt_mul_left hN).mp hmul
  have hstep := Nat.mul_le_mul_left N (Nat.succ_le_of_lt hdiv)
  change N * (m / N + 1) ≤ N * (D i / N) at hstep
  rw [Nat.mul_add, Nat.mul_one] at hstep
  omega

include hN hresidue in
/-- Weights bounded by `B+N-1` leave no gaps at or above `B`. -/
theorem weightedResidueGap_lt_bound (B : ℕ) (hD : ∀ i, D i ≤ B + N - 1)
    (m : WeightedResidueGaps D) : m.val < B := by
  obtain ⟨i, hi⟩ := residue_exists hN D hresidue m.val
  have hlt := (weightedResidueGap_iff_lt_weight D hresidue m.val i hi).mp m.property
  have hstep := gap_step hN D m.val i hi hlt
  have hbound := hD i
  omega

include hN hresidue in
/-- The final possible gap occurs exactly when a residue weight attains the conductor upper bound. -/
theorem weightedResidue_last_gap_iff (B : ℕ) (hB : 0 < B)
    (hD : ∀ i, D i ≤ B + N - 1) :
    (¬ ∃ i : Fin N, ∃ k : ℕ, N * k + D i = B - 1) ↔
      ∃ i : Fin N, D i = B + N - 1 := by
  constructor
  · intro hgap
    obtain ⟨i, hi⟩ := residue_exists hN D hresidue (B - 1)
    have hlt := (weightedResidueGap_iff_lt_weight D hresidue (B - 1) i hi).mp hgap
    have hstep := gap_step hN D (B - 1) i hi hlt
    have hbound := hD i
    exact ⟨i, by omega⟩
  · rintro ⟨i, hi⟩
    have hmod : D i % N = (B - 1) % N := by
      rw [hi, show B + N - 1 = N * 1 + (B - 1) by omega,
        Nat.mul_add_mod_self_left]
    apply (weightedResidueGap_iff_lt_weight D hresidue (B - 1) i hmod).mpr
    omega

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
