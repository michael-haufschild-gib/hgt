import GaloisForLFunctions.HTGeometry.TorsionLanguageUniversalPhase
import GaloisForLFunctions.HTGeometry.PolynomialPatternSurvivors

/-!
# Geometric valuation of translated ADE patterns

For an exact geometric Taylor log-magnitude plus a convergent remainder, every translated bounded
ADE pattern splits into its exponentially scaled finite pattern value and a remainder converging
to the common degree times the limiting correction.
-/

namespace GaloisForLFunctions

open Filter Finset PowerSeries Topology

noncomputable section

/-- The finite geometric value of a bounded multiplicity pattern. -/
def geometricPatternValue {M D : ℕ} (lam : ℝ)
    (p : Fin M → Fin (D + 1)) : ℝ :=
  ∑ r, (p r : ℝ) * lam ^ (r : ℕ)

/-- The subleading valuation correction carried by a translated bounded pattern. -/
def geometricPatternRemainder {M D : ℕ} (c : ℕ → ℝ) (q K : ℕ)
    (p : Fin M → Fin (D + 1)) : ℝ :=
  ∑ r, (p r : ℝ) * c (windowShift q K (r : ℕ))

/-- Exact valuation splitting for one translated bounded pattern. -/
theorem atomValuation_shiftedAtomPatternKey_geometric
    {M D : ℕ} (A lam : ℝ) (c : ℕ → ℝ) (q K : ℕ)
    (p : Fin M → Fin (D + 1)) :
    atomValuation (fun i => A * lam ^ i + c i)
        (shiftedAtomPatternKey q K p) =
      A * lam ^ (q - K) * geometricPatternValue lam p +
        geometricPatternRemainder c q K p := by
  classical
  rw [atomValuation, shiftedAtomPatternKey_eq_sum,
    ← Finsupp.sum_finsetSum_index (s := Finset.univ)
      (g := fun r : Fin M =>
        Finsupp.single (windowShift q K (r : ℕ)) (p r : ℕ))
      (h := fun i k => (k : ℝ) * (A * lam ^ i + c i))]
  · calc
      (∑ r : Fin M,
          (Finsupp.single (windowShift q K (r : ℕ)) (p r : ℕ)).sum
            (fun i k => (k : ℝ) * (A * lam ^ i + c i))) =
          ∑ r : Fin M, (p r : ℝ) *
            (A * lam ^ (windowShift q K (r : ℕ)) +
              c (windowShift q K (r : ℕ))) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finsupp.sum_single_index]
        simp
      _ = A * lam ^ (q - K) * geometricPatternValue lam p +
          geometricPatternRemainder c q K p := by
        rw [geometricPatternValue, geometricPatternRemainder,
          Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r hr
        rw [windowShift, pow_add]
        ring
  · intro i
    simp
  · intro i a b
    push_cast
    ring

/-- Every fixed degree-`D` pattern has the same limiting subleading correction `D * c0`. -/
theorem tendsto_geometricPatternRemainder
    {M D : ℕ} {c : ℕ → ℝ} {c0 : ℝ}
    (hc : Tendsto c atTop (𝓝 c0)) (K : ℕ)
    (p : Fin M → Fin (D + 1))
    (hcount : (∑ r, (p r : ℕ)) = D) :
    Tendsto (fun q => geometricPatternRemainder c q K p)
      atTop (𝓝 (D * c0)) := by
  have hterm : ∀ r : Fin M,
      Tendsto (fun q => (p r : ℝ) * c (windowShift q K (r : ℕ)))
        atTop (𝓝 ((p r : ℝ) * c0)) := by
    intro r
    exact tendsto_const_nhds.mul
      (hc.comp ((tendsto_add_atTop_nat (r : ℕ)).comp (tendsto_sub_atTop_nat K)))
  have hsum := tendsto_finsetSum Finset.univ (fun r _ => hterm r)
  have hcountReal : ∑ r, (p r : ℝ) = (D : ℝ) := by
    exact_mod_cast hcount
  have hlimit : ∑ r, (p r : ℝ) * c0 = (D : ℝ) * c0 := by
    rw [← Finset.sum_mul, hcountReal]
  rw [← hlimit]
  simpa only [geometricPatternRemainder] using hsum

/-- The least geometric value among a finite pattern family, with value zero for the empty
family. -/
noncomputable def geometricPatternMinimum
    {M D : ℕ} (lam : ℝ) (S : Finset (Fin M → Fin (D + 1))) : ℝ :=
  if hS : S.Nonempty then
    (S.image (geometricPatternValue lam)).min' (hS.image _)
  else 0

/-- The locked geometric face consists of the surviving patterns with least geometric value. -/
def geometricPatternFace
    {M D : ℕ} (lam : ℝ) (S : Finset (Fin M → Fin (D + 1))) :
    Finset (Fin M → Fin (D + 1)) :=
  S.filter fun p => geometricPatternValue lam p = geometricPatternMinimum lam S

theorem mem_geometricPatternFace_iff
    {M D : ℕ} {lam : ℝ} {S : Finset (Fin M → Fin (D + 1))}
    {p : Fin M → Fin (D + 1)} :
    p ∈ geometricPatternFace lam S ↔
      p ∈ S ∧ geometricPatternValue lam p = geometricPatternMinimum lam S := by
  simp [geometricPatternFace]

/-- A nonempty finite survivor family has a nonempty least-value face. -/
theorem geometricPatternFace_nonempty
    {M D : ℕ} (lam : ℝ) (S : Finset (Fin M → Fin (D + 1)))
    (hS : S.Nonempty) :
    (geometricPatternFace lam S).Nonempty := by
  classical
  let V := S.image (geometricPatternValue lam)
  have hV : V.Nonempty := hS.image _
  have hminmem : V.min' hV ∈ V := Finset.min'_mem V hV
  obtain ⟨p, hpS, hpmin⟩ := Finset.mem_image.mp hminmem
  refine ⟨p, (mem_geometricPatternFace_iff).mpr ⟨hpS, ?_⟩⟩
  simp only [geometricPatternMinimum, hS, ↓reduceDIte]
  exact hpmin

/-- The minimum is no larger than the value of any surviving pattern. -/
theorem geometricPatternMinimum_le
    {M D : ℕ} (lam : ℝ) (S : Finset (Fin M → Fin (D + 1)))
    (hS : S.Nonempty) {p : Fin M → Fin (D + 1)} (hp : p ∈ S) :
    geometricPatternMinimum lam S ≤ geometricPatternValue lam p := by
  classical
  simp only [geometricPatternMinimum, hS, ↓reduceDIte]
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

/-- Patterns outside the least-value face are separated from it by one uniform positive gap. -/
theorem exists_pos_geometricPatternFace_gap
    {M D : ℕ} (lam : ℝ) (S : Finset (Fin M → Fin (D + 1)))
    (hS : S.Nonempty) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ p ∈ S \ geometricPatternFace lam S,
        geometricPatternMinimum lam S + delta ≤ geometricPatternValue lam p := by
  classical
  let C := S \ geometricPatternFace lam S
  by_cases hC : C.Nonempty
  · let gaps := C.image fun p =>
      geometricPatternValue lam p - geometricPatternMinimum lam S
    have hgaps : gaps.Nonempty := hC.image _
    let delta := gaps.min' hgaps
    have hdeltaMem : delta ∈ gaps := Finset.min'_mem gaps hgaps
    have hdelta : 0 < delta := by
      obtain ⟨p, hpC, hpdelta⟩ := Finset.mem_image.mp hdeltaMem
      rw [← hpdelta]
      have hpS : p ∈ S := Finset.mem_sdiff.mp hpC |>.1
      have hpNot : p ∉ geometricPatternFace lam S := Finset.mem_sdiff.mp hpC |>.2
      have hle := geometricPatternMinimum_le lam S hS hpS
      have hne : geometricPatternValue lam p ≠ geometricPatternMinimum lam S := by
        intro heq
        exact hpNot ((mem_geometricPatternFace_iff).mpr ⟨hpS, heq⟩)
      have hlt : geometricPatternMinimum lam S < geometricPatternValue lam p :=
        lt_of_le_of_ne hle hne.symm
      linarith
    refine ⟨delta, hdelta, ?_⟩
    intro p hp
    have hgapMem : geometricPatternValue lam p - geometricPatternMinimum lam S ∈ gaps :=
      Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have hle := Finset.min'_le gaps _ hgapMem
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro p hp
    exact (hC ⟨p, hp⟩).elim

end

end GaloisForLFunctions
