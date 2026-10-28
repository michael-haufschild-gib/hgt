import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogarithmicStepProfiles
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogarithmicCellSourceTransfer

/-!
# Realization of the complete cell profiles

The monotone-floor profile is exactly the finite logarithmic-cell section after
translation to the source window. This identifies its jumps and moments with the
same vectors whose complete prime pairings are computed by cell subdivision.
-/

noncomputable section
open MeasureTheory Set
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open HTGeometry BiarithmeticGaugeGeometry

theorem mem_logCell_of_ge (R : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : ℝ} (hu : -R ≤ u) :
    u ∈ Ico (logEndpoint R N (logCellIndex R N u))
      (logEndpoint R N (logCellIndex R N u + 1)) := by
  refine ⟨(logCellPoint_bounds R hN hu).1, ?_⟩
  have hn : N ≤ ⌊Real.exp (u + Real.log N + R)⌋₊ :=
    (_root_.RHTower.log_le_iff_le_floor hN _).mp (by linarith)
  have hi : logCellIndex R N u = ⌊Real.exp (u + Real.log N + R)⌋₊ := max_eq_left hn
  have hhi := Real.log_lt_log (Real.exp_pos (u + Real.log N + R))
    (Nat.lt_floor_add_one (Real.exp (u + Real.log N + R)))
  rw [Real.log_exp] at hhi
  simp only [logEndpoint, hi, Nat.cast_add, Nat.cast_one]
  linarith only [hhi]

theorem logCellIndex_eq_of_mem (R : ℝ) {N a : ℕ} (hN : 1 ≤ N) (ha : N ≤ a)
    {u : ℝ} (hu : u ∈ Ico (logEndpoint R N a) (logEndpoint R N (a + 1))) :
    logCellIndex R N u = a := by
  have he := logStep_eq_sample (f := fun x => x) R hN ha hu
  simp only [logStep, logCellPoint, logSamples, max_eq_left ha] at he
  have hl : Real.log (logCellIndex R N u) = Real.log a := by linarith only [he]
  have hi0 : (0 : ℝ) < logCellIndex R N u := by
    exact_mod_cast hN.trans (logCellIndex_ge R N u)
  have ha0 : (0 : ℝ) < a := by exact_mod_cast hN.trans ha
  have hexp := congrArg Real.exp hl
  rw [Real.exp_log hi0, Real.exp_log ha0] at hexp
  exact_mod_cast hexp

/-- Exact finite section identity, including both support endpoints. -/
theorem logStep_eq_indicator_sum {f : ℝ → ℝ} (R : ℝ) {N B : ℕ}
    (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) (u : ℝ) :
    logStep f R N u = ∑ a ∈ Finset.Icc N (N * B),
      (Ico (logEndpoint R N a) (logEndpoint R N (a + 1))).indicator
        (fun _ => logSamples f R N a) u := by
  classical
  by_cases hu : u < -R
  · rw [logStep_eq_zero_outside R hN hB hs (Or.inl hu.le)]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    apply indicator_of_notMem
    intro hmem
    have haN := (Finset.mem_Icc.mp ha).1
    have hlo := Real.log_le_log (by exact_mod_cast hN : (0 : ℝ) < N)
      (by exact_mod_cast haN : (N : ℝ) ≤ a)
    dsimp only [logEndpoint] at hmem
    linarith only [hu, hmem.1, hlo]
  · let a := logCellIndex R N u
    have haN : N ≤ a := logCellIndex_ge R N u
    have hmem : u ∈ Ico (logEndpoint R N a) (logEndpoint R N (a + 1)) :=
      mem_logCell_of_ge R hN (le_of_not_gt hu)
    rw [logStep_eq_sample R hN haN hmem]
    by_cases haX : a ≤ N * B
    · symm
      apply (Finset.sum_eq_single a ?_ ?_).trans (indicator_of_mem hmem _)
      · intro b hb hba
        apply indicator_of_notMem
        intro hcell
        exact hba (logCellIndex_eq_of_mem R hN (Finset.mem_Icc.mp hb).1 hcell).symm
      · intro hnot
        exact False.elim (hnot (Finset.mem_Icc.mpr ⟨haN, haX⟩))
    · rw [logSamples_eq_zero_above R hN hB
        (fun x hx => hs x (Or.inr hx.le)) a (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro b hb
      apply indicator_of_notMem
      intro hcell
      have he : a = b := logCellIndex_eq_of_mem R hN (Finset.mem_Icc.mp hb).1 hcell
      exact haX (he.trans_le (Finset.mem_Icc.mp hb).2)

theorem cellAtom_coeFn (n : ℕ) :
    (cellAtom n : ℝ → ℂ) =ᵐ[halfLineMeasure]
      (Ico (Real.log n) (Real.log ((n + 1 : ℕ) : ℝ))).indicator (fun _ => (1 : ℂ)) := by
  by_cases hn : 0 < n
  · rw [cellAtom, dif_pos hn]
    have hp : Real.sqrt (logCellWidth n) * logCellWidth n ^ (-(1 / 2 : ℝ)) = 1 := by
      simpa only [div_one, Real.one_rpow] using
        sqrt_div_mul_rpow (logCellWidth_pos (by omega : 1 ≤ n)) (by norm_num : (0 : ℝ) < 1)
    filter_upwards [Lp.coeFn_smul (Real.sqrt (logCellWidth n) : ℂ) (logCellVec (n.toPNat hn)),
      logCellVec_coeFn (n.toPNat hn)] with x hsm hv
    rw [hsm, Pi.smul_apply, smul_eq_mul, hv]
    simp only [logCellSet, coe_toPNat, Nat.cast_add, Nat.cast_one]
    by_cases hx : x ∈ Ico (Real.log n) (Real.log ((n : ℝ) + 1))
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      change (Real.sqrt (logCellWidth n) : ℂ) *
        (logCellWidth n ^ (-(1 / 2 : ℝ)) : ℝ) = 1
      rw [← Complex.ofReal_mul, hp, Complex.ofReal_one]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
  · have hn0 : n = 0 := by omega
    subst n
    simp only [cellAtom, dif_neg (by omega : ¬0 < 0), Nat.cast_zero,
      zero_add, Nat.cast_one, Real.log_zero, Real.log_one, Ico_self, indicator_empty]
    exact Lp.coeFn_zero _ _ _

/-- The Hilbert-space section and the monotone-floor profile are the same source. -/
theorem cellSection_logSamples_coeFn {f : ℝ → ℝ} (R : ℝ) {N B : ℕ}
    (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    (cellSection (logSamples f R N) N (N * B) : ℝ → ℂ) =ᵐ[halfLineMeasure]
      fun x => (logStep f R N (x - Real.log N - R) : ℂ) := by
  have hsum := coeFn_finset_sum_smul (Finset.Icc N (N * B))
    (fun a => (logSamples f R N a : ℂ)) cellAtom
  have hatom : ∀ᵐ x ∂halfLineMeasure, ∀ a : ℕ,
      (cellAtom a : ℝ → ℂ) x =
        (Ico (Real.log a) (Real.log ((a + 1 : ℕ) : ℝ))).indicator (fun _ => (1 : ℂ)) x :=
    ae_all_iff.mpr cellAtom_coeFn
  unfold cellSection
  filter_upwards [hsum, hatom] with x hx ha
  rw [hx, logStep_eq_indicator_sum R hN hB hs (x - Real.log N - R), Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [ha a]
  have hshift : x - Real.log N - R ∈ Ico (logEndpoint R N a) (logEndpoint R N (a + 1)) ↔
      x ∈ Ico (Real.log a) (Real.log ((a + 1 : ℕ) : ℝ)) := by
    simp only [mem_Ico, logEndpoint]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  by_cases hmem : x ∈ Ico (Real.log a) (Real.log ((a + 1 : ℕ) : ℝ))
  · rw [indicator_of_mem hmem, indicator_of_mem (hshift.mpr hmem), mul_one]
  · rw [indicator_of_notMem hmem, indicator_of_notMem (fun h => hmem (hshift.mp h)),
      mul_zero, Complex.ofReal_zero]

/-- Zero extension identifies the actual complete section on the whole real line. -/
theorem halfLineExtend_cellSection_logSamples {f : ℝ → ℝ} (R : ℝ) {N B : ℕ}
    (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    (halfLineExtend (cellSection (logSamples f R N) N (N * B)) : ℝ → ℂ) =ᵐ[volume]
      fun x => (logStep f R N (x - Real.log N - R) : ℂ) := by
  refine (halfLineExtend_coeFn _).trans
    ((indicator_ae_eq_of_halfLine (cellSection_logSamples_coeFn R hN hB hs)).trans ?_)
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ Ici (0 : ℝ)
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx]
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1)
      (by exact_mod_cast hN : (1 : ℝ) ≤ N)
    rw [Real.log_one] at hlog
    have hx0 : x < 0 := lt_of_not_ge hx
    change (0 : ℂ) = (logStep f R N (x - Real.log N - R) : ℂ)
    rw [logStep_eq_zero_outside R hN hB hs (u := x - Real.log N - R)
      (Or.inl (by linarith only [hx0, hlog])),
      Complex.ofReal_zero]

/-- Synthesis of a finite source family commutes with taking its actual cell section. -/
theorem cellSection_logSamples_sum {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ)
    (c : ι → ℝ) (R : ℝ) (N X : ℕ) :
    cellSection (logSamples (fun u => ∑ i, c i * f i u) R N) N X =
      ∑ i, (c i : ℂ) • cellSection (logSamples (f i) R N) N X := by
  simp only [cellSection, logSamples, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

#print axioms logStep_eq_indicator_sum
#print axioms halfLineExtend_cellSection_logSamples
#print axioms cellSection_logSamples_sum

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
