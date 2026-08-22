import GaloisForLFunctions.HTGeometry.KleinbockMargulis.TheoremA

/-!
# Finite-order compression of all-order nondegeneracy

For a map with finite-dimensional output, it is enough to know that every
nonzero covector is detected by some positive-order jet. Compactness of the
unit covector sphere then gives one finite jet order detecting all covectors.
This closes the uniformity bridge between analytic all-order escape and the
finite-order nondegeneracy used by Kleinbock--Margulis.
-/

open Set Metric
open scoped Topology BigOperators

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {d n : ℕ}

/-- Pointwise separation of every nonzero covector by some positive-order
jet compresses, in finite output dimension, to one uniform finite order. -/
theorem exists_finiteOrder_nondegAt_of_all_covectors_separated
    {F : (Fin d → ℝ) → (Fin n → ℝ)} {x₀ : Fin d → ℝ}
    (hsep : ∀ w : Fin n → ℝ, w ≠ 0 →
      ∃ j : ℕ, 1 ≤ j ∧ ∃ m : Fin j → (Fin d → ℝ),
        ∑ i, w i * (iteratedFDeriv ℝ j F x₀ m) i ≠ 0) :
    ∃ l : ℕ, 1 ≤ l ∧ NondegAt l F x₀ := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, le_rfl, ?_⟩
    intro w _hw
    exact Subsingleton.elim w 0
  haveI : NeZero n := ⟨by omega⟩
  have hlocal : ∀ w ∈ sphere (0 : Fin n → ℝ) 1,
      ∃ (N : Set (Fin n → ℝ)) (j : ℕ)
          (m : Fin j → (Fin d → ℝ)),
        N ∈ 𝓝 w ∧ 1 ≤ j ∧
          ∀ w' ∈ N,
            ∑ i, w' i * (iteratedFDeriv ℝ j F x₀ m) i ≠ 0 := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro h
      rw [mem_sphere_zero_iff_norm, h, norm_zero] at hw
      exact zero_ne_one hw
    obtain ⟨j, hj, m, hwm⟩ := hsep w hw0
    let S : (Fin n → ℝ) → ℝ :=
      fun w' => ∑ i, w' i * (iteratedFDeriv ℝ j F x₀ m) i
    have hScont : Continuous S := by
      exact continuous_finsetSum _ fun i _ =>
        (continuous_apply i).mul continuous_const
    refine ⟨{w' | S w' ≠ 0}, j, m, ?_, hj, ?_⟩
    · exact hScont.continuousAt.eventually_ne hwm
    · intro w' hw'
      exact hw'
  choose! Nf jf mf hNf hjf hne using hlocal
  obtain ⟨t, hts, hcover⟩ :=
    (isCompact_sphere (0 : Fin n → ℝ) 1).elim_nhds_subcover
      Nf fun w hw => hNf w hw
  have hu₁ :
      (Pi.single (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n) (1 : ℝ))
        ∈ sphere (0 : Fin n → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm]
    exact norm_single_eq_one _
  obtain ⟨w₁, hw₁t, -⟩ := Set.mem_iUnion₂.mp (hcover hu₁)
  have ht : t.Nonempty := ⟨w₁, hw₁t⟩
  let l : ℕ := t.sup' ht jf
  have hl : 1 ≤ l :=
    (hjf w₁ (hts w₁ hw₁t)).trans (Finset.le_sup' jf hw₁t)
  refine ⟨l, hl, ?_⟩
  intro w hvanish
  by_contra hw0
  have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  let u : Fin n → ℝ := ‖w‖⁻¹ • w
  have huS : u ∈ sphere (0 : Fin n → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm]
    change ‖‖w‖⁻¹ • w‖ = 1
    rw [norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (ne_of_gt hwnorm)]
  obtain ⟨a, hat, hua⟩ := Set.mem_iUnion₂.mp (hcover huS)
  have hjle : jf a ≤ l := Finset.le_sup' jf hat
  have hz := hvanish (jf a) (hjf a (hts a hat)) hjle (mf a)
  have huzero :
      ∑ i, u i * (iteratedFDeriv ℝ (jf a) F x₀ (mf a)) i = 0 := by
    change ∑ i, (‖w‖⁻¹ * w i) *
      (iteratedFDeriv ℝ (jf a) F x₀ (mf a)) i = 0
    simp only [mul_assoc]
    rw [← Finset.mul_sum, hz, mul_zero]
  exact (hne a (hts a hat) u hua) huzero

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
