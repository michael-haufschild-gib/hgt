import GaloisForLFunctions.BezoutValuationIncidence.CofinalMobiusJointMagnitudeLaw

/-!
# Magnitude observables and source-gradient lower bounds

The joint magnitude law transfers to every fixed real-valued observable:
all sampled magnitude vectors eventually lie in a finite alphabet. Applied
to adjacent squared differences, this determines the magnitude-gradient
mean and gives an unconditional lower bound for the literal signed-source
gradient energy. No signed Möbius correlation assumption is used.
-/

open Filter Topology Finset
open scoped BigOperators Classical

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false
variable {m : ℕ}

private theorem source_magnitude_finite (K N n : ℕ+)
    (hhi : (n : ℕ) ≤ ((K : ℕ) + 1) * (N : ℕ)) :
    ∃ a : Fin ((K : ℕ) + 1), |sieveSeq N moebiusReal n| = ((a : ℕ) : ℝ) := by
  have he := abs_sieveSeq_moebius_eq_bandMagnitude N n
  by_cases hn : (n : ℕ) = 1
  · have hK := K.pos
    exact ⟨⟨1, by omega⟩, by simpa only [if_pos hn, Nat.cast_one] using he⟩
  rw [if_neg hn] at he
  have hq : ((n : ℕ) - 1) / (N : ℕ) < (K : ℕ) + 1 := by
    apply (Nat.div_lt_iff_lt_mul N.pos).mpr
    have hn0 := n.pos
    omega
  obtain ⟨a, ha⟩ := moebiusBandMagnitude_mem_finite (((n : ℕ) - 1) / (N : ℕ)) n
  have hlt : (a : ℕ) < (K : ℕ) + 1 := by
    have := a.isLt
    omega
  exact ⟨⟨a, hlt⟩, he.trans ha⟩

private theorem shifted_source_magnitude_finite (K : ℕ+) (t : Set.Icc (0 : ℝ) 1)
    (h : Fin m → ℕ) {N n : ℕ} (hN : 1 ≤ N) (hH : (∑ i, h i) ≤ N)
    (hn : n ∈ Icc 1 ⌊((K : ℝ) + (t : ℝ)) * N⌋₊) (i : Fin m) :
    ∃ a : Fin ((K : ℕ) + 2), |sieveSeq N moebiusReal (n + h i)| = ((a : ℕ) : ℝ) := by
  have hi : h i ≤ N := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)).trans hH
  have hfloor : ⌊((K : ℝ) + (t : ℝ)) * N⌋₊ ≤ ((K : ℕ) + 1) * N := by
    apply Nat.floor_le_of_le
    push_cast
    have ht := t.property.2
    have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  obtain ⟨hn0, hnhi⟩ := mem_Icc.mp hn
  have hbound : n + h i ≤ (((K : ℕ) + 1) + 1) * N := by nlinarith
  exact source_magnitude_finite ⟨(K : ℕ) + 1, by omega⟩ ⟨N, by omega⟩
    ⟨n + h i, by omega⟩ hbound

/-- Explicit raw mean of any fixed function of the joint magnitude vector. -/
def cofinalMobiusMagnitudeObservableMass (K : ℕ+) (t : Set.Icc (0 : ℝ) 1)
    (h : Fin m → ℕ) (Φ : (Fin m → ℝ) → ℝ) : ℝ :=
  ∑ a : Fin m → Fin ((K : ℕ) + 2),
    Φ (fun i => ((a i : ℕ) : ℝ)) * cofinalMobiusJointMagnitudeMass K t h (fun i => ((a i : ℕ) : ℝ))

/-- Finite magnitude support transfers the joint law to every real-valued observable. -/
theorem tendsto_moebiusMagnitudeObservableMean (K : ℕ+) (t : Set.Icc (0 : ℝ) 1)
    (h : Fin m → ℕ) (Φ : (Fin m → ℝ) → ℝ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 ⌊((K : ℝ) + (t : ℝ)) * N⌋₊,
        Φ (fun i => |sieveSeq N moebiusReal (n + h i)|)) / N)
      atTop (𝓝 (cofinalMobiusMagnitudeObservableMass K t h Φ)) := by
  have hlim := tendsto_finsetSum (univ : Finset (Fin m → Fin ((K : ℕ) + 2)))
    (fun a _ => (tendsto_moebiusSourceMagnitudePatternCount K t h (fun i => ((a i : ℕ) : ℝ))).const_mul
      (Φ (fun i => ((a i : ℕ) : ℝ))))
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (∑ i, h i)] with N hN hH
  let M : ℕ := ⌊((K : ℝ) + (t : ℝ)) * N⌋₊
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 M) :
      Φ (fun i => |sieveSeq N moebiusReal (n + h i)|) =
        ∑ a : Fin m → Fin ((K : ℕ) + 2), Φ (fun i => ((a i : ℕ) : ℝ)) *
          (if ∀ i, |sieveSeq N moebiusReal (n + h i)| = ((a i : ℕ) : ℝ) then 1 else 0) := by
    choose b hb using shifted_source_magnitude_finite K t h hN hH hn
    have he (a : Fin m → Fin ((K : ℕ) + 2)) :
        (∀ i, |sieveSeq N moebiusReal (n + h i)| = ((a i : ℕ) : ℝ)) ↔ b = a := by
      constructor
      · intro ha
        funext i
        apply Fin.ext
        exact_mod_cast (hb i).symm.trans (ha i)
      · rintro rfl
        exact hb
    simp only [he, mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq]
    exact congrArg Φ (funext hb)
  symm
  calc
    _ = (∑ n ∈ Icc 1 M, ∑ a : Fin m → Fin ((K : ℕ) + 2),
        Φ (fun i => ((a i : ℕ) : ℝ)) *
          (if ∀ i, |sieveSeq N moebiusReal (n + h i)| = ((a i : ℕ) : ℝ) then 1 else 0)) / N := by
      congr 1
      exact sum_congr rfl hpoint
    _ = _ := by
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.mul_sum, Finset.sum_boole]
      simp only [moebiusSourceMagnitudePatternCount, mul_div_assoc]
      congr 4

/-- Limiting squared magnitude-gradient mean for the literal truncated source. -/
def cofinalMobiusMagnitudeGradientMass (K : ℕ+) (t : Set.Icc (0 : ℝ) 1) : ℝ :=
  cofinalMobiusMagnitudeObservableMass K t (fun i : Fin 2 => i.val)
    (fun x => (x 1 - x 0) ^ 2)

/-- The joint law computes the magnitude-gradient mean without a signed correlation premise. -/
theorem tendsto_moebiusMagnitudeGradientMean (K : ℕ+) (t : Set.Icc (0 : ℝ) 1) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 ⌊((K : ℝ) + (t : ℝ)) * N⌋₊,
        (|sieveSeq N moebiusReal (n + 1)| - |sieveSeq N moebiusReal n|) ^ 2) / N)
      atTop (𝓝 (cofinalMobiusMagnitudeGradientMass K t)) := by
  exact tendsto_moebiusMagnitudeObservableMean K t (fun i : Fin 2 => i.val)
    (fun x => (x 1 - x 0) ^ 2)

/-- The explicit magnitude law yields an eventual lower bound for actual signed-source gradient energy. -/
theorem eventually_moebiusGradientMean_ge_magnitudeMass (K : ℕ+)
    (t : Set.Icc (0 : ℝ) 1) (ε : Set.Ioi (0 : ℝ)) :
    ∀ᶠ N : ℕ in atTop, cofinalMobiusMagnitudeGradientMass K t - (ε : ℝ) ≤
      (∑ n ∈ Icc 1 ⌊((K : ℝ) + (t : ℝ)) * N⌋₊,
        (sieveSeq N moebiusReal (n + 1) - sieveSeq N moebiusReal n) ^ 2) / N := by
  have he := (tendsto_moebiusMagnitudeGradientMean K t).eventually
    (lt_mem_nhds (sub_lt_self _ ε.property))
  filter_upwards [he] with N hmean
  apply hmean.le.trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply Finset.sum_le_sum
  intro n _
  let u := sieveSeq N moebiusReal n
  let v := sieveSeq N moebiusReal (n + 1)
  have huv : u * v ≤ |u| * |v| := by rw [← abs_mul]; exact le_abs_self _
  have hu := sq_abs u
  have hv := sq_abs v
  change (|v| - |u|) ^ 2 ≤ (v - u) ^ 2
  nlinarith

end
end GaloisForLFunctions.BezoutValuationIncidence
