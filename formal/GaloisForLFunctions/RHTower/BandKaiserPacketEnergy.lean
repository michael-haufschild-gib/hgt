import GaloisForLFunctions.RHTower.BandKaiserPacketConditioning
import GaloisForLFunctions.HTGeometry.HalfLineSteinRobertson

/-!
# Uniform energy lower bounds for conditioned Kaiser packet spans

The packet-reading matrix has a positive diagonal of size at least `T_c(0)/2` and exponentially
small off-diagonal entries.  A maximal-coefficient argument therefore gives a quantitative lower
bound for every vector in a fixed finite packet span.  Integral Cauchy--Schwarz then converts one
large reading into physical `L²` energy.
-/

open MeasureTheory Set intervalIntegral
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Conditioned Kaiser combination on the explicit angular grid. -/
def kaiserGridCombination {m : ℕ} (c : ℝ) (b : Fin m → ℝ) : ℝ → ℝ :=
  kaiserCosCombination c (kaiserPacketFrequency c) b

/-- A row of the packet-reading matrix applied to the coefficient vector. -/
def kaiserPacketRow {m : ℕ} (c : ℝ) (b : Fin m → ℝ) (i : Fin m) : ℝ :=
  ∑ j, b j * kaiserPacketReading c (kaiserPacketAngularFrequency c i)
    (kaiserPacketAngularFrequency c j)

theorem exists_max_abs_kaiserPacketCoefficient {m : ℕ} (hm : 0 < m) (b : Fin m → ℝ) :
    ∃ i : Fin m, ∀ j : Fin m, |b j| ≤ |b i| := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin m))
    (fun j => |b j|) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

theorem sum_sq_kaiserPacketCoefficient_le {m : ℕ} (b : Fin m → ℝ) (i : Fin m)
    (hi : ∀ j, |b j| ≤ |b i|) :
    (∑ j, b j ^ 2) ≤ (m : ℝ) * |b i| ^ 2 := by
  calc
    (∑ j, b j ^ 2) = ∑ j, |b j| ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact (sq_abs (b j)).symm
    _ ≤ ∑ _j : Fin m, |b i| ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (abs_nonneg _) (hi j) 2
    _ = (m : ℝ) * |b i| ^ 2 := by simp [Fintype.card_fin]

/-- Diagonal dominance of a fixed packet row at an index of maximal coefficient magnitude. -/
theorem abs_kaiserPacketRow_ge {m : ℕ} {c : ℝ}
    (hc : 1 ≤ c) (hscale : 8 * (m : ℝ) ^ 2 ≤ Real.sqrt c)
    (hsmall : 32 * (m : ℝ) * Real.exp (-(Real.sqrt c / 2)) ≤ 1)
    (b : Fin m → ℝ) (i : Fin m) (hi : ∀ j, |b j| ≤ |b i|) :
    |b i| * kaiserAngularTransform c 0 / 4 ≤ |kaiserPacketRow c b i| := by
  let T : ℝ := kaiserAngularTransform c 0
  let D : ℝ := kaiserPacketReading c (kaiserPacketAngularFrequency c i)
    (kaiserPacketAngularFrequency c i)
  let E : ℝ := ∑ j ∈ (Finset.univ : Finset (Fin m)).erase i,
    b j * kaiserPacketReading c (kaiserPacketAngularFrequency c i)
      (kaiserPacketAngularFrequency c j)
  have hcpos : 0 < c := one_pos.trans_le hc
  have hTpos : 0 < T := by
    exact kaiserAngularTransform_zero_pos hcpos
  have hD : T / 2 ≤ D := by
    exact kaiserPacketReading_diagonal_ge hc hscale i
  have hD0 : 0 ≤ D := le_trans (div_nonneg hTpos.le (by norm_num)) hD
  have hdiag : |b i| * T / 2 ≤ |b i * D| := by
    rw [abs_mul, abs_of_nonneg hD0]
    exact div_le_iff₀ (by norm_num : (0 : ℝ) < 2) |>.2
      (by nlinarith [mul_le_mul_of_nonneg_left hD (abs_nonneg (b i))])
  have hoff : |E| ≤
      (m : ℝ) * (|b i| *
        (8 * Real.exp (-(Real.sqrt c / 2)) * T)) := by
    calc
      |E| ≤ ∑ j ∈ (Finset.univ : Finset (Fin m)).erase i,
          |b j * kaiserPacketReading c (kaiserPacketAngularFrequency c i)
            (kaiserPacketAngularFrequency c j)| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ (Finset.univ : Finset (Fin m)).erase i,
          |b i| * (8 * Real.exp (-(Real.sqrt c / 2)) * T) := by
        apply Finset.sum_le_sum
        intro j hj
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        rw [abs_mul]
        exact mul_le_mul (hi j)
          (abs_kaiserPacketReading_offDiagonal_le hc hscale hji.symm)
          (abs_nonneg _) (by positivity)
      _ = (((Finset.univ : Finset (Fin m)).erase i).card : ℝ) *
          (|b i| * (8 * Real.exp (-(Real.sqrt c / 2)) * T)) := by
        simp
      _ ≤ (m : ℝ) * (|b i| *
          (8 * Real.exp (-(Real.sqrt c / 2)) * T)) := by
        apply mul_le_mul_of_nonneg_right
        · have hcard :
            ((Finset.univ : Finset (Fin m)).erase i).card ≤
              (Finset.univ : Finset (Fin m)).card := Finset.card_erase_le
          simp only [Finset.card_univ, Fintype.card_fin] at hcard
          exact_mod_cast hcard
        · positivity
  have hoffSmall : |E| ≤ |b i| * T / 4 := by
    refine hoff.trans ?_
    calc
      (m : ℝ) * (|b i| * (8 * Real.exp (-(Real.sqrt c / 2)) * T)) =
          (32 * (m : ℝ) * Real.exp (-(Real.sqrt c / 2))) * (|b i| * T / 4) := by
        ring
      _ ≤ 1 * (|b i| * T / 4) :=
        mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = |b i| * T / 4 := one_mul _
  have hsplit : b i * D + E = kaiserPacketRow c b i := by
    change b i * kaiserPacketReading c (kaiserPacketAngularFrequency c i)
        (kaiserPacketAngularFrequency c i) +
      (∑ j ∈ (Finset.univ : Finset (Fin m)).erase i,
        b j * kaiserPacketReading c (kaiserPacketAngularFrequency c i)
          (kaiserPacketAngularFrequency c j)) =
      ∑ j, b j * kaiserPacketReading c (kaiserPacketAngularFrequency c i)
        (kaiserPacketAngularFrequency c j)
    exact Finset.add_sum_erase (Finset.univ : Finset (Fin m))
      (fun j => b j * kaiserPacketReading c (kaiserPacketAngularFrequency c i)
        (kaiserPacketAngularFrequency c j)) (Finset.mem_univ i)
  have htriangle : |b i * D| - |E| ≤ |kaiserPacketRow c b i| := by
    calc
      |b i * D| - |E| = |b i * D| - |-E| := by rw [abs_neg]
      _ ≤ |b i * D - -E| := abs_sub_abs_le_abs_sub _ _
      _ = |kaiserPacketRow c b i| := by rw [sub_neg_eq_add, hsplit]
  change |b i| * T / 4 ≤ _
  linarith

end GaloisForLFunctions.RHTower

end
