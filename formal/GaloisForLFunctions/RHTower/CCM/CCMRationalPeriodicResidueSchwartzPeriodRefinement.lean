import GaloisForLFunctions.RHTower.CCM.CCMRationalPeriodicResidueSchwartzStrongLogDecay
import GaloisForLFunctions.RHTower.CCM.CCMRationalFiniteBruhatPeriodicWeights

/-!
# Common-period refinement of residue-Schwartz traces

A residue-Schwartz trace of period `M` can be represented at every multiple
`M * K` by repeating its residue family `K` times.  The represented logarithmic
trace is unchanged, while the sum of any residue statistic is multiplied by
`K`.  In particular, after refinement the total Fourier zero mode acquires the
same factor as the period.  This is the exact compatibility needed to add
adelic tensor packets without losing endpoint cancellations between summands.
-/

noncomputable section

open scoped FourierTransform SchwartzMap BigOperators

namespace GaloisForLFunctions
namespace RHTower

/-- Pulling a function back along the integer residue map gives a sequence of
period `M`. -/
theorem ccmRationalPeriodicResidue_comp_periodic
    {Y : Type*} (M : ℕ) [NeZero M] (w : Fin M → Y) :
    Function.Periodic
      (fun n : ℤ => w (ccmRationalPeriodicResidue M n)) (M : ℤ) := by
  intro n
  apply congrArg w
  apply Fin.ext
  simp [ccmRationalPeriodicResidue, Int.divModEquiv, Int.natMod]

/-- Repeat an `M`-residue Schwartz family at period `M * K`. -/
def ccmRationalPeriodicResidueSchwartzRefinement
    (M K : ℕ) [NeZero M] [NeZero K]
    (g : Fin M → CCMRationalArchimedeanSchwartz) :
    Fin (M * K) → CCMRationalArchimedeanSchwartz :=
  fun r => g (ccmRationalPeriodicResidue M (r.val : ℤ))

/-- Product coordinates ordered so the second coordinate is the residue
modulo `M`. -/
def ccmRationalPeriodicResidueRefinementEquiv (M K : ℕ) :
    Fin K × Fin M ≃ Fin (M * K) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm K M))

@[simp]
theorem ccmRationalPeriodicResidueSchwartzRefinement_equiv_apply
    (M K : ℕ) [NeZero M] [NeZero K]
    (g : Fin M → CCMRationalArchimedeanSchwartz)
    (p : Fin K × Fin M) :
    ccmRationalPeriodicResidueSchwartzRefinement M K g
        (ccmRationalPeriodicResidueRefinementEquiv M K p) =
      g p.2 := by
  unfold ccmRationalPeriodicResidueSchwartzRefinement
    ccmRationalPeriodicResidueRefinementEquiv
  congr 1
  have hval :
      ((finProdFinEquiv.trans
        (finCongr (Nat.mul_comm K M))) p).val =
        p.2.val + M * p.1.val := rfl
  apply Fin.ext
  rw [show (((finProdFinEquiv.trans
      (finCongr (Nat.mul_comm K M))) p).val : ℤ) =
      (p.2.val + M * p.1.val : ℕ) by rw [hval]]
  have hpnonneg : (0 : ℤ) ≤ (p.2.val : ℤ) := by positivity
  have hplt : (p.2.val : ℤ) < (M : ℤ) := by
    exact_mod_cast p.2.isLt
  simp [ccmRationalPeriodicResidue, Int.divModEquiv, Int.natMod,
    Int.emod_eq_of_lt hpnonneg hplt]

/-- Refinement preserves the residue selected by every integer. -/
@[simp]
theorem ccmRationalPeriodicResidueSchwartzRefinement_residue
    (M K : ℕ) [NeZero M] [NeZero K]
    (g : Fin M → CCMRationalArchimedeanSchwartz) (n : ℤ) :
    ccmRationalPeriodicResidueSchwartzRefinement M K g
        (ccmRationalPeriodicResidue (M * K) n) =
      g (ccmRationalPeriodicResidue M n) := by
  unfold ccmRationalPeriodicResidueSchwartzRefinement
  congr 1
  let F : ℤ → Fin M := fun z => ccmRationalPeriodicResidue M z
  have hF : Function.Periodic F (M : ℤ) :=
    ccmRationalPeriodicResidue_comp_periodic M id
  have hprod : Function.Periodic F ((M * K : ℕ) : ℤ) := by
    rw [Nat.cast_mul]
    simpa [nsmul_eq_mul, mul_comm] using hF.nsmul K
  let p : ℤ × Fin (M * K) := Int.divModEquiv (M * K) n
  have hn : n = p.1 * ((M * K : ℕ) : ℤ) + (p.2 : ℤ) := by
    change n = (Int.divModEquiv (M * K) n).1 *
      ((M * K : ℕ) : ℤ) + ((Int.divModEquiv (M * K) n).2 : ℤ)
    exact (Int.divModEquiv (M * K)).symm_apply_apply n |>.symm
  have hp : F n = F (p.2 : ℤ) := by
    rw [hn, add_comm]
    exact hprod.int_mul p.1 (p.2 : ℤ)
  exact hp.symm

/-- Every residue statistic is repeated exactly `K` times by refinement. -/
theorem sum_ccmRationalPeriodicResidueSchwartzRefinement
    {A : Type*} [AddCommMonoid A]
    (M K : ℕ) [NeZero M] [NeZero K]
    (g : Fin M → CCMRationalArchimedeanSchwartz)
    (h : CCMRationalArchimedeanSchwartz → A) :
    ∑ s : Fin (M * K),
        h (ccmRationalPeriodicResidueSchwartzRefinement M K g s) =
      K • ∑ r : Fin M, h (g r) := by
  calc
    (∑ s : Fin (M * K),
        h (ccmRationalPeriodicResidueSchwartzRefinement M K g s)) =
        ∑ p : Fin K × Fin M,
          h (ccmRationalPeriodicResidueSchwartzRefinement M K g
            (ccmRationalPeriodicResidueRefinementEquiv M K p)) :=
      ((ccmRationalPeriodicResidueRefinementEquiv M K).sum_comp
        (fun s => h
          (ccmRationalPeriodicResidueSchwartzRefinement M K g s))).symm
    _ = ∑ p : Fin K × Fin M, h (g p.2) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [ccmRationalPeriodicResidueSchwartzRefinement_equiv_apply]
    _ = K • ∑ r : Fin M, h (g r) := by
      rw [Fintype.sum_prod_type]
      simp

/-- A residue-Schwartz trace is the integer lattice sum obtained by selecting
the Schwartz function belonging to the current residue. -/
theorem ccmRationalPeriodicResidueSchwartzLogTrace_apply
    (M : ℕ) [NeZero M]
    (g : Fin M → CCMRationalArchimedeanSchwartz) (t : ℝ) :
    ccmRationalPeriodicResidueSchwartzLogTrace M g t =
      ∑' n : ℤ, g (ccmRationalPeriodicResidue M n)
        (Real.exp t * (n : ℝ)) := by
  rw [ccmRationalPeriodicResidueSchwartzLogTrace]
  rw [Finset.sum_apply]
  change (∑ r : Fin M, ccmRationalPeriodicWeightedTrace M
      (ccmRationalPeriodicDeltaWeight M r) (g r) (Real.exp t)) = _
  simp_rw [ccmRationalPeriodicWeightedTrace]
  change (∑ r : Fin M, ∑' n : ℤ,
      ccmRationalPeriodicDeltaWeight M r
          (ccmRationalPeriodicResidue M n) *
        g r (Real.exp t * (n : ℝ))) = _
  have hs : ∀ r : Fin M, Summable (fun n : ℤ =>
      ccmRationalPeriodicDeltaWeight M r
          (ccmRationalPeriodicResidue M n) *
        g r (Real.exp t * (n : ℝ))) := by
    intro r
    exact ccmRationalPeriodicWeightedTrace_summable M
      (ccmRationalPeriodicDeltaWeight M r) (g r)
      (Real.exp_ne_zero t)
  rw [← Summable.tsum_finsetSum (fun r _ => hs r)]
  apply tsum_congr
  intro n
  simp [ccmRationalPeriodicDeltaWeight]

/-- Period refinement changes the presentation but not the represented
logarithmic trace. -/
theorem ccmRationalPeriodicResidueSchwartzLogTrace_refinement
    (M K : ℕ) [NeZero M] [NeZero K]
    (g : Fin M → CCMRationalArchimedeanSchwartz) :
    ccmRationalPeriodicResidueSchwartzLogTrace (M * K)
        (ccmRationalPeriodicResidueSchwartzRefinement M K g) =
      ccmRationalPeriodicResidueSchwartzLogTrace M g := by
  funext t
  rw [ccmRationalPeriodicResidueSchwartzLogTrace_apply,
    ccmRationalPeriodicResidueSchwartzLogTrace_apply]
  apply tsum_congr
  intro n
  rw [ccmRationalPeriodicResidueSchwartzRefinement_residue]

/-- The same refinement with the new factor written on the left of the
period.  This orientation lets two packets refine directly to `M * K` without
transporting one family across an equality of `Fin` types. -/
def ccmRationalPeriodicResidueSchwartzLeftRefinement
    (M K : ℕ) [NeZero M] [NeZero K]
    (g : Fin M → CCMRationalArchimedeanSchwartz) :
    Fin (K * M) → CCMRationalArchimedeanSchwartz :=
  fun r => g (ccmRationalPeriodicResidue M (r.val : ℤ))

/-- Left refinement preserves the residue selected by every integer. -/
@[simp]
theorem ccmRationalPeriodicResidueSchwartzLeftRefinement_residue
    (M K : ℕ) [NeZero M] [NeZero K]
    (g : Fin M → CCMRationalArchimedeanSchwartz) (n : ℤ) :
    ccmRationalPeriodicResidueSchwartzLeftRefinement M K g
        (ccmRationalPeriodicResidue (K * M) n) =
      g (ccmRationalPeriodicResidue M n) := by
  unfold ccmRationalPeriodicResidueSchwartzLeftRefinement
  congr 1
  let F : ℤ → Fin M := fun z => ccmRationalPeriodicResidue M z
  have hF : Function.Periodic F (M : ℤ) :=
    ccmRationalPeriodicResidue_comp_periodic M id
  have hprod : Function.Periodic F ((K * M : ℕ) : ℤ) := by
    rw [Nat.cast_mul]
    simpa [nsmul_eq_mul] using hF.nsmul K
  let p : ℤ × Fin (K * M) := Int.divModEquiv (K * M) n
  have hn : n = p.1 * ((K * M : ℕ) : ℤ) + (p.2 : ℤ) := by
    change n = (Int.divModEquiv (K * M) n).1 *
      ((K * M : ℕ) : ℤ) + ((Int.divModEquiv (K * M) n).2 : ℤ)
    exact (Int.divModEquiv (K * M)).symm_apply_apply n |>.symm
  have hp : F n = F (p.2 : ℤ) := by
    rw [hn, add_comm]
    exact hprod.int_mul p.1 (p.2 : ℤ)
  exact hp.symm

/-- Left refinement also repeats every residue statistic exactly `K` times. -/
theorem sum_ccmRationalPeriodicResidueSchwartzLeftRefinement
    {A : Type*} [AddCommMonoid A]
    (M K : ℕ) [NeZero M] [NeZero K]
    (g : Fin M → CCMRationalArchimedeanSchwartz)
    (h : CCMRationalArchimedeanSchwartz → A) :
    ∑ s : Fin (K * M),
        h (ccmRationalPeriodicResidueSchwartzLeftRefinement M K g s) =
      K • ∑ r : Fin M, h (g r) := by
  calc
    (∑ s : Fin (K * M),
        h (ccmRationalPeriodicResidueSchwartzLeftRefinement M K g s)) =
        ∑ p : Fin K × Fin M,
          h (ccmRationalPeriodicResidueSchwartzLeftRefinement M K g
            (finProdFinEquiv p)) :=
      (finProdFinEquiv.sum_comp
        (fun s => h
          (ccmRationalPeriodicResidueSchwartzLeftRefinement M K g s))).symm
    _ = ∑ p : Fin K × Fin M, h (g p.2) := by
      apply Finset.sum_congr rfl
      intro p hp
      unfold ccmRationalPeriodicResidueSchwartzLeftRefinement
      apply congrArg h
      apply congrArg g
      apply Fin.ext
      have hpnonneg : (0 : ℤ) ≤ (p.2.val : ℤ) := by positivity
      have hplt : (p.2.val : ℤ) < (M : ℤ) := by
        exact_mod_cast p.2.isLt
      simp [ccmRationalPeriodicResidue, Int.divModEquiv, Int.natMod,
        finProdFinEquiv, Int.emod_eq_of_lt hpnonneg hplt]
    _ = K • ∑ r : Fin M, h (g r) := by
      rw [Fintype.sum_prod_type]
      simp

/-- Left period refinement also leaves the represented trace unchanged. -/
theorem ccmRationalPeriodicResidueSchwartzLogTrace_leftRefinement
    (M K : ℕ) [NeZero M] [NeZero K]
    (g : Fin M → CCMRationalArchimedeanSchwartz) :
    ccmRationalPeriodicResidueSchwartzLogTrace (K * M)
        (ccmRationalPeriodicResidueSchwartzLeftRefinement M K g) =
      ccmRationalPeriodicResidueSchwartzLogTrace M g := by
  funext t
  rw [ccmRationalPeriodicResidueSchwartzLogTrace_apply,
    ccmRationalPeriodicResidueSchwartzLogTrace_apply]
  apply tsum_congr
  intro n
  rw [ccmRationalPeriodicResidueSchwartzLeftRefinement_residue]

end RHTower
end GaloisForLFunctions
