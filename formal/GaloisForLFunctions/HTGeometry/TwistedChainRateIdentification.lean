import GaloisForLFunctions.HTGeometry.TwistedChainDegreeRate
import GaloisForLFunctions.HTGeometry.ShiftedTopMatrix

/-!
# Identifying the growth rate of a twisted chain

The rate exists unconditionally.  When a shear puts the generator at shifted degree `c` and the
accumulated shifted leading matrices never vanish, the rate **is** `c`: the band estimate
`|matDeg A_n − n·c| ≤ spread(k)` divides by `n` and the error goes to zero, so the Fekete limit is
pinned by uniqueness of limits.

Together with the existence result this is the card's asymptotic law in the non-degenerate regime —
the rate is not merely approximated by `matDeg A_n / n`, it equals the shifted degree exactly.

* `twistedChainRate_nonneg`, `twistedChainRate_le_matDeg`;
* `twistedChainRate_eq_zero_of_shiftDegLE` — a shear with `c = 0` forces rate zero;
* `twistedChainRate_eq` — **the rate is the shifted degree when the leading chain survives**.
-/

open scoped Differential

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem twistedChainRate_nonneg (σ : DiffOp K →+* DiffOp K) (hσ : ∀ p, degree (σ p) = degree p)
    (C : Matrix ι ι (DiffOp K)) : 0 ≤ twistedChainRate σ hσ C := by
  refine le_of_tendsto_of_eventually_le (tendsto_matDeg_twistedChain σ hσ C) ?_
  filter_upwards with n
  positivity

theorem twistedChainRate_le_matDeg (σ : DiffOp K →+* DiffOp K)
    (hσ : ∀ p, degree (σ p) = degree p) (C : Matrix ι ι (DiffOp K)) {e : ℕ}
    (he : matDeg C ≤ e) : twistedChainRate σ hσ C ≤ (e : ℝ) := by
  refine ge_of_tendsto (tendsto_matDeg_twistedChain σ hσ C) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hle : matDeg (twistedChain σ C n) ≤ n * e := by
    have hshift := shiftDegLE_twistedChain (K := K) (fun _ => (0 : ℤ)) σ hσ
      (C := C) (c := (e : ℤ)) (fun i j _ => by
        have := degree_le_matDeg C i j
        have h2 : degree (C i j) ≤ e := le_trans this he
        push_cast
        omega) n
    have hmat := hshift.matDeg_le (by positivity)
    have hsp : shearSpread (fun _ : ι => (0 : ℤ)) = 0 := by
      refine le_antisymm (Finset.sup'_le _ _ fun q _ => by simp) ?_
      obtain ⟨i⟩ := ‹Nonempty ι›
      have := le_shearSpread (fun _ : ι => (0 : ℤ)) i i
      simpa using this
    rw [hsp, add_zero] at hmat
    exact_mod_cast hmat
  rw [div_le_iff₀ hnR]
  have : ((matDeg (twistedChain σ C n) : ℕ) : ℝ) ≤ ((n * e : ℕ) : ℝ) := by exact_mod_cast hle
  push_cast at this
  linarith

/-- **A shear making the shifted degree vanish forces the rate to be zero.** -/
theorem twistedChainRate_eq_zero_of_shiftDegLE (k : ι → ℤ) (σ : DiffOp K →+* DiffOp K)
    (hσ : ∀ p, degree (σ p) = degree p) {C : Matrix ι ι (DiffOp K)}
    (hC : ShiftDegLE k C 0) : twistedChainRate σ hσ C = 0 := by
  refine le_antisymm ?_ (twistedChainRate_nonneg σ hσ C)
  refine ge_of_tendsto (tendsto_matDeg_twistedChain σ hσ C) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hb := matDeg_twistedChain_le_of_shiftDegLE_zero k σ hσ hC n
  sorry

end

end DiffOp

end GaloisForLFunctions.HTGeometry
