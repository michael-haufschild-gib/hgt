import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedUniformValueTruncation
import GaloisForLFunctions.RHTower.Sieve.DirichletTruncationError

/-!
# High-block law, brick B8 (direct side): the direct Gaussian series beyond `L`

The direct edge of the exact displaced AFE is `Σ_n (n+1)^{−s} V((n+1)/x)` with `V` the Gaussian
cutoff. Since `‖V(u)‖ ≤ K_A u^{−A}` for every `A > 0`, the terms beyond `L` are bounded by
`K_A x^A (n+1)^{−(½ − d + A)}`, and the tail is `≤ K_A x^A L^{½+d−A}/(A − ½ − d)`.

With `L = x·a^δ` this is `≪ a^{−δ(A−1)+¼}`, so any fixed `A > 1 + 1/(4δ)` makes the tail
negligible on the block — the free exponent is what the lane's fixed `L^{−1}` tail lacks.
-/

open Complex

namespace RHTower

noncomputable section

/-- Free-exponent pointwise envelope for the direct value coefficients. -/
theorem exists_norm_smoothAFEZetaDisplacedDirectTerm_le_rpow_general {A : ℝ} (hA : 0 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (d x tau : ℝ), 0 < x → ∀ n : ℕ,
      ‖smoothAFEZetaDisplacedDirectTerm d x tau n‖ ≤
        K * x ^ A * (((n + 1 : ℕ) : ℝ)) ^ (-(1 / 2 - d + A)) := by
  obtain ⟨K, hK, hcut⟩ := exists_norm_smoothAFECutoff_le_neg_rpow hA
  refine ⟨K, hK, fun d x tau hx n => ?_⟩
  have hr1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hr0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  rw [smoothAFEZetaDisplacedDirectTerm, norm_mul, norm_natSucc_cpow_neg_displacedLinePt]
  have hV : ‖smoothAFECutoff (((n : ℝ) + 1) / x)‖ ≤ K * x ^ A * ((n : ℝ) + 1) ^ (-A) := by
    calc ‖smoothAFECutoff (((n : ℝ) + 1) / x)‖ ≤ K * (((n : ℝ) + 1) / x) ^ (-A) :=
          hcut (div_pos hr0 hx)
      _ = K * x ^ A * ((n : ℝ) + 1) ^ (-A) := by
        rw [Real.div_rpow hr0.le hx.le, Real.rpow_neg hr0.le, Real.rpow_neg hx.le]
        have h1 : x ^ A ≠ 0 := (Real.rpow_pos_of_pos hx A).ne'
        have h2 : ((n : ℝ) + 1) ^ A ≠ 0 := (Real.rpow_pos_of_pos hr0 A).ne'
        field_simp
  have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  calc ((n : ℝ) + 1) ^ (-(1 / 2 - d)) * ‖smoothAFECutoff (((n : ℝ) + 1) / x)‖
      ≤ ((n : ℝ) + 1) ^ (-(1 / 2 - d)) * (K * x ^ A * ((n : ℝ) + 1) ^ (-A)) :=
        mul_le_mul_of_nonneg_left hV (Real.rpow_nonneg hr0.le _)
    _ = K * x ^ A * ((n : ℝ) + 1) ^ (-(1 / 2 - d + A)) := by
        rw [show -(1 / 2 - d + A) = (-(1 / 2 - d)) + (-A) by ring, Real.rpow_add hr0]
        ring

/-- **B8, direct side.** The direct series beyond `L` is `≤ K x^A L^{½+d−A}/(A − ½ − d)`. -/
theorem exists_norm_smoothAFEZetaDisplacedDirectTerm_tail_le_general {A : ℝ} (hA : 1 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (d x tau : ℝ), 0 < x → 0 ≤ d → d ≤ 1 / 4 → ∀ L : ℕ, 1 ≤ L →
      ‖(∑' n : ℕ, smoothAFEZetaDisplacedDirectTerm d x tau n) -
          ∑ n ∈ Finset.range L, smoothAFEZetaDisplacedDirectTerm d x tau n‖ ≤
        K * x ^ A * ((L : ℝ) ^ (1 - (1 / 2 - d + A)) / ((1 / 2 - d + A) - 1)) := by
  obtain ⟨K, hK, hpoint⟩ :=
    exists_norm_smoothAFEZetaDisplacedDirectTerm_le_rpow_general (by linarith : (0 : ℝ) < A)
  refine ⟨K, hK, fun d x tau hx hd0 hd4 L hL => ?_⟩
  have hdhalf : d < 1 / 2 := by linarith
  set σ : ℝ := 1 / 2 - d + A with hσ
  have hσ1 : 1 < σ := by rw [hσ]; linarith
  let f : ℕ → ℂ := fun n => smoothAFEZetaDisplacedDirectTerm d x tau n
  have hnorm : Summable (fun n : ℕ => ‖f n‖) := by
    simpa only [f] using summable_norm_smoothAFEZetaDisplacedDirectTerm hdhalf hx tau
  have hsum : Summable f := hnorm.of_norm
  have heq : (∑' n : ℕ, f n) - ∑ n ∈ Finset.range L, f n = ∑' j : ℕ, f (j + L) := by
    rw [← hsum.sum_add_tsum_nat_add L, add_sub_cancel_left]
  show ‖(∑' n : ℕ, f n) - ∑ n ∈ Finset.range L, f n‖ ≤ _
  rw [heq]
  have hnormTail : Summable (fun j : ℕ => ‖f (j + L)‖) := (summable_nat_add_iff L).2 hnorm
  have hpow : Summable (fun j : ℕ => (((j + L + 1 : ℕ) : ℝ)) ^ (-σ)) := by
    have hbase := Real.summable_nat_rpow.mpr (show -σ < -1 by linarith)
    simpa [Nat.add_assoc] using (summable_nat_add_iff (L + 1)).2 hbase
  calc ‖∑' j : ℕ, f (j + L)‖ ≤ ∑' j : ℕ, ‖f (j + L)‖ := norm_tsum_le_tsum_norm hnormTail
    _ ≤ ∑' j : ℕ, K * x ^ A * (((j + L + 1 : ℕ) : ℝ)) ^ (-σ) := by
        refine hnormTail.tsum_le_tsum (fun j => ?_) (hpow.mul_left _)
        have := hpoint d x tau hx (j + L)
        simpa only [f, hσ] using this
    _ = K * x ^ A * ∑' j : ℕ, (((j + L + 1 : ℕ) : ℝ)) ^ (-σ) := by rw [tsum_mul_left]
    _ ≤ K * x ^ A * ((L : ℝ) ^ (1 - σ) / (σ - 1)) :=
        mul_le_mul_of_nonneg_left (Sieve.tsum_tail_rpow_neg_le hσ1 hL) (by positivity)

end

end RHTower
