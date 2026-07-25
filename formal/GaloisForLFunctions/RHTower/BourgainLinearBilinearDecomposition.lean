/-
# Pointwise linear-to-bilinear decomposition

This is the finite rearrangement inequality behind Bourgain's
bilinear-to-linear induction.  Either all terms except a largest one are
smaller by a factor `K`, in which case the whole sum is controlled by one
diagonal twelfth power, or a second large term supplies a bilinear
sixth-power product.  The resulting coefficient `K^18` is the power appearing
in Bourgain's equation (2.25).

The present theorem sums over all distinct pairs.  The interval-separation
refinement is a subsequent combinatorial layer.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace RHTower

noncomputable section

set_option maxHeartbeats 800000 in
/-- Pointwise diagonal/bilinear decomposition for a finite complex sum. -/
theorem norm_fintypeSum_pow_twelve_le_diagonal_add_bilinear
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → ℂ) :
    ‖∑ i : ι, z i‖ ^ (12 : ℕ) ≤
      (2 : ℝ) ^ (12 : ℕ) * ∑ i : ι, ‖z i‖ ^ (12 : ℕ) +
        (Fintype.card ι : ℝ) ^ (18 : ℕ) *
          ∑ i : ι, ∑ j ∈ (Finset.univ : Finset ι).filter (fun j => j ≠ i),
            ‖z i‖ ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ) := by
  classical
  by_cases hι : Nonempty ι
  · letI : Nonempty ι := hι
    obtain ⟨i₀, hi₀mem, hi₀max⟩ :=
      Finset.exists_max_image (Finset.univ : Finset ι)
        (fun i => ‖z i‖) Finset.univ_nonempty
    let A : ℝ := ‖z i₀‖
    let K : ℝ := Fintype.card ι
    let E : Finset ι := (Finset.univ : Finset ι).erase i₀
    have hA : 0 ≤ A := by
      dsimp [A]
      positivity
    have hK : 0 < K := by
      dsimp [K]
      exact_mod_cast Fintype.card_pos
    have hmax (i : ι) : ‖z i‖ ≤ A := by
      exact hi₀max i (Finset.mem_univ i)
    have hsumNorm :
        ‖∑ i : ι, z i‖ ≤ ∑ i : ι, ‖z i‖ :=
      norm_sum_le _ _
    have hsumMax :
        (∑ i : ι, ‖z i‖) ≤ K * A := by
      calc
        (∑ i : ι, ‖z i‖) ≤ ∑ _i : ι, A :=
          Finset.sum_le_sum fun i _ => hmax i
        _ = K * A := by
          simp [K, nsmul_eq_mul]
    by_cases hlarge :
        ∃ j ∈ E, A ≤ K * ‖z j‖
    · obtain ⟨j, hjE, hjlarge⟩ := hlarge
      have hji₀ : j ≠ i₀ := (Finset.mem_erase.mp hjE).1
      have hpowNorm :
          ‖∑ i : ι, z i‖ ^ (12 : ℕ) ≤
            (K * A) ^ (12 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg _)
          (hsumNorm.trans hsumMax) 12
      have hlargePow :
          A ^ (6 : ℕ) ≤ (K * ‖z j‖) ^ (6 : ℕ) :=
        pow_le_pow_left₀ hA hjlarge 6
      have hpairLe :
          A ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ) ≤
            ∑ i : ι,
              ∑ j ∈ (Finset.univ : Finset ι).filter (fun j => j ≠ i),
                ‖z i‖ ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ) := by
        have hinner :
            A ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ) ≤
              ∑ k ∈ (Finset.univ : Finset ι).filter (fun k => k ≠ i₀),
                ‖z i₀‖ ^ (6 : ℕ) * ‖z k‖ ^ (6 : ℕ) := by
          simpa [A] using
            (Finset.single_le_sum
              (s := (Finset.univ : Finset ι).filter (fun k => k ≠ i₀))
              (f := fun k =>
                ‖z i₀‖ ^ (6 : ℕ) * ‖z k‖ ^ (6 : ℕ))
              (fun k hk => by positivity)
              (show j ∈
                (Finset.univ : Finset ι).filter (fun k => k ≠ i₀) by
                  simp [hji₀]))
        have houter :
            (∑ k ∈ (Finset.univ : Finset ι).filter (fun k => k ≠ i₀),
                ‖z i₀‖ ^ (6 : ℕ) * ‖z k‖ ^ (6 : ℕ)) ≤
              ∑ i : ι,
                ∑ k ∈ (Finset.univ : Finset ι).filter (fun k => k ≠ i),
                  ‖z i‖ ^ (6 : ℕ) * ‖z k‖ ^ (6 : ℕ) := by
          exact Finset.single_le_sum
            (s := (Finset.univ : Finset ι))
            (f := fun i =>
              ∑ k ∈ (Finset.univ : Finset ι).filter (fun k => k ≠ i),
                ‖z i‖ ^ (6 : ℕ) * ‖z k‖ ^ (6 : ℕ))
            (fun i hi => Finset.sum_nonneg fun k hk => by positivity)
            (Finset.mem_univ i₀)
        simpa [A] using hinner.trans houter
      have hKnonneg : 0 ≤ K := hK.le
      have hbilinear :
          (K * A) ^ (12 : ℕ) ≤
            K ^ (18 : ℕ) *
              (A ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ)) := by
        calc
          (K * A) ^ (12 : ℕ) =
              K ^ (12 : ℕ) *
                (A ^ (6 : ℕ) * A ^ (6 : ℕ)) := by ring
          _ ≤ K ^ (12 : ℕ) *
                (A ^ (6 : ℕ) * (K * ‖z j‖) ^ (6 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hlargePow (by positivity))
              (by positivity)
          _ = K ^ (18 : ℕ) *
                (A ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ)) := by ring
      calc
        ‖∑ i : ι, z i‖ ^ (12 : ℕ) ≤ (K * A) ^ (12 : ℕ) :=
          hpowNorm
        _ ≤ K ^ (18 : ℕ) *
            (A ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ)) := hbilinear
        _ ≤ K ^ (18 : ℕ) *
            (∑ i : ι,
              ∑ j ∈ (Finset.univ : Finset ι).filter (fun j => j ≠ i),
                ‖z i‖ ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ)) :=
          mul_le_mul_of_nonneg_left hpairLe (by positivity)
        _ ≤ (2 : ℝ) ^ (12 : ℕ) *
              ∑ i : ι, ‖z i‖ ^ (12 : ℕ) +
            K ^ (18 : ℕ) *
              ∑ i : ι,
                ∑ j ∈ (Finset.univ : Finset ι).filter (fun j => j ≠ i),
                  ‖z i‖ ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ) := by
          have hdiagNonneg :
              0 ≤ (2 : ℝ) ^ (12 : ℕ) *
                ∑ i : ι, ‖z i‖ ^ (12 : ℕ) := by
            exact mul_nonneg (by positivity)
              (Finset.sum_nonneg fun i hi => by positivity)
          linarith
        _ = (2 : ℝ) ^ (12 : ℕ) *
              ∑ i : ι, ‖z i‖ ^ (12 : ℕ) +
            (Fintype.card ι : ℝ) ^ (18 : ℕ) *
              ∑ i : ι,
                ∑ j ∈ (Finset.univ : Finset ι).filter (fun j => j ≠ i),
                  ‖z i‖ ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ) := by rfl
    · have hsmall (j : ι) (hj : j ∈ E) :
          K * ‖z j‖ ≤ A := by
        exact le_of_not_ge fun h => hlarge ⟨j, hj, h⟩
      have hcardE : (E.card : ℝ) ≤ K := by
        dsimp [K]
        exact_mod_cast Finset.card_le_univ E
      have hsumE :
          (∑ j ∈ E, ‖z j‖) ≤ A := by
        have hscaled :
            K * (∑ j ∈ E, ‖z j‖) ≤ K * A := by
          calc
            K * (∑ j ∈ E, ‖z j‖) =
                ∑ j ∈ E, K * ‖z j‖ := by
              rw [Finset.mul_sum]
            _ ≤ ∑ _j ∈ E, A :=
              Finset.sum_le_sum fun j hj => hsmall j hj
            _ = (E.card : ℝ) * A := by
              simp [nsmul_eq_mul]
            _ ≤ K * A :=
              mul_le_mul_of_nonneg_right hcardE hA
        nlinarith
      have hsumSplit :
          (∑ i : ι, ‖z i‖) =
            A + ∑ j ∈ E, ‖z j‖ := by
        rw [add_comm]
        simp [A, E]
      have hsumTwoA :
          (∑ i : ι, ‖z i‖) ≤ 2 * A := by
        rw [hsumSplit]
        linarith
      have hpowNorm :
          ‖∑ i : ι, z i‖ ^ (12 : ℕ) ≤
            (2 * A) ^ (12 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg _)
          (hsumNorm.trans hsumTwoA) 12
      have hdiag :
          A ^ (12 : ℕ) ≤ ∑ i : ι, ‖z i‖ ^ (12 : ℕ) := by
        simpa [A] using
          (Finset.single_le_sum
            (s := (Finset.univ : Finset ι))
            (f := fun i => ‖z i‖ ^ (12 : ℕ))
            (fun i hi => by positivity)
            (Finset.mem_univ i₀))
      calc
        ‖∑ i : ι, z i‖ ^ (12 : ℕ) ≤
            (2 * A) ^ (12 : ℕ) := hpowNorm
        _ = (2 : ℝ) ^ (12 : ℕ) * A ^ (12 : ℕ) := by
          rw [mul_pow]
        _ ≤ (2 : ℝ) ^ (12 : ℕ) *
            ∑ i : ι, ‖z i‖ ^ (12 : ℕ) :=
          mul_le_mul_of_nonneg_left hdiag (by positivity)
        _ ≤ (2 : ℝ) ^ (12 : ℕ) *
              ∑ i : ι, ‖z i‖ ^ (12 : ℕ) +
            (Fintype.card ι : ℝ) ^ (18 : ℕ) *
              ∑ i : ι,
                ∑ j ∈ (Finset.univ : Finset ι).filter (fun j => j ≠ i),
                  ‖z i‖ ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ) := by
          have hcrossNonneg :
              0 ≤ (Fintype.card ι : ℝ) ^ (18 : ℕ) *
                ∑ i : ι,
                  ∑ j ∈ (Finset.univ : Finset ι).filter (fun j => j ≠ i),
                    ‖z i‖ ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ) := by
            apply mul_nonneg (by positivity)
            exact Finset.sum_nonneg fun i hi =>
              Finset.sum_nonneg fun j hj => by positivity
          linarith
  · haveI : IsEmpty ι := not_nonempty_iff.mp hι
    simp

/-- Finset form of the pointwise diagonal/bilinear decomposition. -/
theorem norm_finsetSum_pow_twelve_le_diagonal_add_bilinear
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (z : ι → ℂ) :
    ‖∑ i ∈ s, z i‖ ^ (12 : ℕ) ≤
      (2 : ℝ) ^ (12 : ℕ) * ∑ i ∈ s, ‖z i‖ ^ (12 : ℕ) +
        (s.card : ℝ) ^ (18 : ℕ) *
          ∑ i ∈ s, ∑ j ∈ s.filter (fun j => j ≠ i),
            ‖z i‖ ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ) := by
  classical
  let z' : {i // i ∈ s} → ℂ := fun i => z i
  have h :=
    norm_fintypeSum_pow_twelve_le_diagonal_add_bilinear z'
  have hsum :
      (∑ i : {i // i ∈ s}, z' i) = ∑ i ∈ s, z i := by
    exact Finset.sum_attach s z
  have hdiag :
      (∑ i : {i // i ∈ s}, ‖z' i‖ ^ (12 : ℕ)) =
        ∑ i ∈ s, ‖z i‖ ^ (12 : ℕ) := by
    exact Finset.sum_attach s (fun i => ‖z i‖ ^ (12 : ℕ))
  have hinner (i : {i // i ∈ s}) :
      (∑ j ∈ (Finset.univ : Finset {i // i ∈ s}).filter (fun j => j ≠ i),
          ‖z' i‖ ^ (6 : ℕ) * ‖z' j‖ ^ (6 : ℕ)) =
        ∑ j ∈ s.filter (fun j => j ≠ i.1),
          ‖z i.1‖ ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ) := by
    apply Finset.sum_bij (fun j _ => j.1)
    · intro j hj
      have hjne := (Finset.mem_filter.mp hj).2
      simp only [Finset.mem_filter]
      exact ⟨j.2, fun hval => hjne (Subtype.ext hval)⟩
    · intro j₁ hj₁ j₂ hj₂ heq
      exact Subtype.ext heq
    · intro j hj
      refine ⟨⟨j, (Finset.mem_filter.mp hj).1⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro heq
      exact (Finset.mem_filter.mp hj).2 (congrArg Subtype.val heq)
    · intro j hj
      rfl
  have hpair :
      (∑ i : {i // i ∈ s},
          ∑ j ∈ (Finset.univ : Finset {i // i ∈ s}).filter (fun j => j ≠ i),
            ‖z' i‖ ^ (6 : ℕ) * ‖z' j‖ ^ (6 : ℕ)) =
        ∑ i ∈ s, ∑ j ∈ s.filter (fun j => j ≠ i),
          ‖z i‖ ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ) := by
    calc
      _ = ∑ i : {i // i ∈ s},
          ∑ j ∈ s.filter (fun j => j ≠ i.1),
            ‖z i.1‖ ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ) := by
        apply Fintype.sum_congr
        exact hinner
      _ = _ := by
        simpa using
          Finset.sum_attach s (fun i =>
            ∑ j ∈ s.filter (fun j => j ≠ i),
              ‖z i‖ ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ))
  rw [hsum, hdiag, hpair] at h
  simpa [z'] using h

end

end RHTower
