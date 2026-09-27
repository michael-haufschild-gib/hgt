import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.RHTower.XiResolventMassBudget

/-!
# Arbitrarily many actual critical-line nodes for Gaussian polynomial sampling

Hardy's unconditional real zeros supply distinct positive squared nodes of every
finite cardinality. The nodes are actual divisor copies, with no placement
assumption and no numerical zero certification.
-/

open Complex Set
noncomputable section

namespace RHTower

/-- Positive real zeros of the actual centered Xi function form an infinite set. -/
theorem infinite_positive_real_XiC_zeros :
    {x : ℝ | 0 < x ∧ XiC (x : ℂ) = 0}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨T, hT⟩
  obtain ⟨x, hx, hzero⟩ := exists_Xi_zero_gt (max T 0)
  have hx0 : 0 < x := (le_max_right T 0).trans_lt hx
  have hXi : XiC (x : ℂ) = 0 := by rw [XiC_ofReal, hzero]; simp
  exact (not_le_of_gt ((le_max_left T 0).trans_lt hx)) (hT ⟨hx0, hXi⟩)

/-- Every finite polynomial dimension has a separated family of actual positive real Xi nodes. -/
theorem exists_xiCriticalGaussian_nodes (N : ℕ) :
    ∃ (γ : Fin N → ℝ) (q : Fin N → XiZeroCopy),
      Function.Injective (fun i => (γ i : ℂ) ^ 2) ∧
      (∀ i, 0 < γ i ∧ xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      (∀ i, (32 : ℝ) < γ i ^ 2) := by
  classical
  let S : Set ℝ := {x : ℝ | 0 < x ∧ XiC (x : ℂ) = 0}
  let e : ℕ ↪ S := infinite_positive_real_XiC_zeros.natEmbedding S
  let γ : Fin N → ℝ := fun i => (e (i : ℕ)).val
  have hγpos (i : Fin N) : 0 < γ i := (e (i : ℕ)).property.1
  have hzero (i : Fin N) : XiC (γ i : ℂ) = 0 := (e (i : ℕ)).property.2
  choose q hq using fun i => (XiC_eq_zero_iff_exists_xiZeroCopy (γ i)).mp (hzero i)
  refine ⟨γ, q, ?_, fun i => ⟨hγpos i, hq i⟩, ?_⟩
  · intro i j hij
    change (γ i : ℂ) ^ 2 = (γ j : ℂ) ^ 2 at hij
    have hs : γ i ^ 2 = γ j ^ 2 := by
      exact_mod_cast hij
    have heq : γ i = γ j := (sq_eq_sq₀ (hγpos i).le (hγpos j).le).mp hs
    exact Fin.ext (e.injective (Subtype.ext heq))
  · intro i
    have h := xiSpectral_re_sq_gt_thirtytwo (q i)
    simpa only [hq i, Complex.ofReal_re] using h

end RHTower
