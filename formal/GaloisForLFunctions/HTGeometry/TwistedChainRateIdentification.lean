import GaloisForLFunctions.HTGeometry.TwistedChainDegreeRate
import GaloisForLFunctions.HTGeometry.ShiftedTopMatrix
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Identifying the growth rate of a twisted chain

The rate exists unconditionally.  When a shear puts the generator at shifted degree `c` and the
accumulated shifted leading matrices never vanish, the rate **is** `c`: the band estimate
`|matDeg A_n − n·c| ≤ spread(k)` divided by `n` has error going to zero, so the Fekete limit is
pinned by uniqueness of limits.

So in the non-degenerate regime the rate is not merely approximated by `matDeg A_n / n` — it equals
the shifted degree exactly, and the bounded phase is the case `c = 0`.

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

omit [Nonempty ι] in
theorem twistedChainRate_nonneg (σ : DiffOp K →+* DiffOp K) (hσ : ∀ p, degree (σ p) = degree p)
    (C : Matrix ι ι (DiffOp K)) : 0 ≤ twistedChainRate σ hσ C := by
  refine ge_of_tendsto (tendsto_matDeg_twistedChain σ hσ C) ?_
  filter_upwards with n
  positivity

omit [DecidableEq ι] in
theorem shearSpread_zero_fun : shearSpread (fun _ : ι => (0 : ℤ)) = 0 := by
  refine le_antisymm (Finset.sup'_le _ _ fun q _ => by simp) ?_
  obtain ⟨i⟩ := ‹Nonempty ι›
  have := le_shearSpread (fun _ : ι => (0 : ℤ)) i i
  simpa using this

theorem twistedChainRate_le_matDeg (σ : DiffOp K →+* DiffOp K)
    (hσ : ∀ p, degree (σ p) = degree p) (C : Matrix ι ι (DiffOp K)) {e : ℕ}
    (he : matDeg C ≤ e) : twistedChainRate σ hσ C ≤ (e : ℝ) := by
  refine le_of_tendsto (tendsto_matDeg_twistedChain σ hσ C) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hshift := shiftDegLE_twistedChain (K := K) (fun _ => (0 : ℤ)) σ hσ
    (C := C) (c := (e : ℤ)) (fun i j _ => by
      have h1 := degree_le_matDeg C i j
      have h2 : degree (C i j) ≤ e := le_trans h1 he
      push_cast
      omega) n
  have hmat := hshift.matDeg_le (by positivity)
  rw [shearSpread_zero_fun, add_zero] at hmat
  have hcast : ((matDeg (twistedChain σ C n) : ℕ) : ℝ) ≤ (n : ℝ) * (e : ℝ) := by
    have : ((matDeg (twistedChain σ C n) : ℕ) : ℤ) ≤ (n : ℤ) * (e : ℤ) := by exact_mod_cast hmat
    exact_mod_cast this
  rw [div_le_iff₀ hnR]
  linarith

/-- **A shear making the shifted degree vanish forces the rate to be zero.** -/
theorem twistedChainRate_eq_zero_of_shiftDegLE (k : ι → ℤ) (σ : DiffOp K →+* DiffOp K)
    (hσ : ∀ p, degree (σ p) = degree p) {C : Matrix ι ι (DiffOp K)}
    (hC : ShiftDegLE k C 0) : twistedChainRate σ hσ C = 0 := by
  refine le_antisymm ?_ (twistedChainRate_nonneg σ hσ C)
  have h1 := tendsto_matDeg_twistedChain σ hσ C
  have h2 : Tendsto (fun n : ℕ => ((shearSpread k : ℤ) : ℝ) / n) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  refine le_of_tendsto_of_tendsto' h1 h2 fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hb := matDeg_twistedChain_le_of_shiftDegLE_zero k σ hσ hC n
    have hcast : ((matDeg (twistedChain σ C n) : ℕ) : ℝ) ≤ ((shearSpread k : ℤ) : ℝ) := by
      exact_mod_cast hb
    gcongr

/-- **The rate is the shifted degree when the accumulated leading chain survives.** -/
theorem twistedChainRate_eq (k : ι → ℤ) (σ : DiffOp K →+* DiffOp K) (τ : K →+* K)
    (hσ : ∀ p, degree (σ p) = degree p)
    (hcoeff : ∀ (p : DiffOp K) (n : ℕ), coeff (σ p) n = τ (coeff p n))
    {C : Matrix ι ι (DiffOp K)} {c : ℤ} (hc : 0 ≤ c) (hC : ShiftDegLE k C c)
    (hne : ∀ n, chainProdK (twistedFamily τ (shiftTopMatrix k C c)) n ≠ 0) :
    twistedChainRate σ hσ C = (c : ℝ) := by
  refine tendsto_nhds_unique (tendsto_matDeg_twistedChain σ hσ C) ?_
  have hband : ∀ n : ℕ,
      |(matDeg (twistedChain σ C n) : ℤ) - (n : ℤ) * c| ≤ shearSpread k :=
    matDeg_twistedChain_sub_le k σ τ hσ hcoeff hc hC hne
  have hsp : Tendsto (fun n : ℕ => ((shearSpread k : ℤ) : ℝ) / n) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hlow : Tendsto (fun n : ℕ => (c : ℝ) - ((shearSpread k : ℤ) : ℝ) / n) atTop
      (nhds (c : ℝ)) := by
    have h := (tendsto_const_nhds (X := ℝ) (x := (c : ℝ)) (f := atTop (α := ℕ))).sub hsp
    simpa using h
  have hhigh : Tendsto (fun n : ℕ => (c : ℝ) + ((shearSpread k : ℤ) : ℝ) / n) atTop
      (nhds (c : ℝ)) := by
    have h := (tendsto_const_nhds (X := ℝ) (x := (c : ℝ)) (f := atTop (α := ℕ))).add hsp
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hb := (abs_le.mp (hband n)).1
    have hbR : -(((shearSpread k : ℤ) : ℝ))
        ≤ ((matDeg (twistedChain σ C n) : ℕ) : ℝ) - (n : ℝ) * (c : ℝ) := by
      exact_mod_cast hb
    rw [le_div_iff₀ hnR]
    field_simp
    linarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hb := (abs_le.mp (hband n)).2
    have hbR : ((matDeg (twistedChain σ C n) : ℕ) : ℝ) - (n : ℝ) * (c : ℝ)
        ≤ ((shearSpread k : ℤ) : ℝ) := by
      exact_mod_cast hb
    rw [div_le_iff₀ hnR]
    field_simp
    linarith

end

end DiffOp

end GaloisForLFunctions.HTGeometry
