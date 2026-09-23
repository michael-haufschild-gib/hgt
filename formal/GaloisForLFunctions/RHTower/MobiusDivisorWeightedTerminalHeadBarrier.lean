import GaloisForLFunctions.RHTower.WeightedScalarMergeAmplitude
import GaloisForLFunctions.RHTower.MobiusDivisorSqrtGrowthEscape
import GaloisForLFunctions.RHTower.MobiusDivisorTerminalCoreExistence
import GaloisForLFunctions.RHTower.MobiusDivisorTransverseDissipationTrap
import GaloisForLFunctions.RHTower.MobiusDivisorTerminalBudgetRecovery

/-!
# Sharp weighted terminal head barrier for the actual divisor source

The positive scalar amplitude law transports through every literal terminal
prime insertion. Together with unconditional square-root source escape on
fixed grids, it excludes uniform complete monotone orders from small-head,
bounded-quotient terminal cores. The existing arithmetic small-core construction
provides such noncompletable cores arbitrarily far out, with arbitrarily
small quadratic successor envelope.

This excludes completion through those cores. It leaves the fixed-positive-
weight complete-path candidate from the initial source open.
-/

noncomputable section
open Finset
namespace RHTower

/-- A complete finite order of literal unprocessed prime insertions, each decreasing
retained energy with the specified fixed head weight. -/
def MobiusDivisorWeightedCompletion (α : ℝ) (M : ℕ) (P : Finset ℕ) : Prop :=
  ∃ (N : ℕ) (Q : ℕ → Finset ℕ), Q 0=P ∧ Q N=mobiusDivisorSelectionPrimes M ∧
    ∀ k<N,∃ p  ∈  mobiusDivisorSelectionPrimes M \ Q k,
      Q (k+1)=insert p (Q k) ∧
      mobiusDivisorWeightedHeadEnergy α M (Q (k+1)) ≤ mobiusDivisorWeightedHeadEnergy α M (Q k)

/-- In the terminal phase, weighted descent is exactly the one-leaf scalar inequality. -/
theorem mobiusDivisorWeightedHeadEnergy_terminal_step_iff (α : ℝ) (M : ℕ) (P : Finset ℕ)
    (hterminal : mobiusDivisorSmallSelectionPrimes M  ⊆  P)
    {p : ℕ} (hp : p  ∈  mobiusDivisorSelectionPrimes M \ P) :
    (mobiusDivisorWeightedHeadEnergy α M (insert p P) ≤ mobiusDivisorWeightedHeadEnergy α M P) ↔
      α*(mobiusDivisorSelectionFibre M P ∅+mobiusDivisorSelectionFibre M P {p})^(2 : ℕ) ≤ 
        α*(mobiusDivisorSelectionFibre M P ∅)^(2 : ℕ)+(mobiusDivisorSelectionFibre M P {p})^(2 : ℕ) := by
  have hE := mobiusDivisorSelectionEnergy_union_terminal M P {p} hterminal
  have hH := mobiusDivisorSelectionHead_union_terminal M P {p} hterminal
  simp only [union_singleton,sum_singleton,scalarSubsetMergeEnergy] at hE hH
  have hsum := sum_erase_add (mobiusDivisorSelectionPrimes M \ P)
    (fun q => (mobiusDivisorSelectionFibre M P {q})^(2 : ℕ)) hp
  rw [← sdiff_singleton_eq_erase] at hsum
  unfold mobiusDivisorWeightedHeadEnergy mobiusDivisorNonemptyEnergy
  rw [hE,hH,mobiusDivisorSelectionEnergy_terminal M P hterminal]
  constructor <;> intro hh <;> nlinarith only [hsum,hh]

private theorem singleton_abs_bound (M J : ℕ) (P : Finset ℕ) {p : ℕ}
    (hp : p.Prime) (hquot : M/p ≤ J) :
    |mobiusDivisorSelectionFibre M P {p}|  ≤  (3/5:ℝ)*J*Real.sqrt M := by
  have hs := (single_le_sum (fun R (_ : R  ∈  ((mobiusDivisorSelectionPrimes M).erase p).powerset) =>
    abs_nonneg (mobiusDivisorSelectionFibre M P (insert p R)))
      (mem_powerset.mpr (empty_subset _))).trans
        (sum_abs_mobiusDivisorPrimeFibre_le_quotient M P hp)
  simp only [insert_empty_eq] at hs
  have hq : ((M/p:ℕ):ℝ) ≤ J := by exact_mod_cast hquot
  nlinarith only [hs,mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ) ≤ (3/5)*Real.sqrt M)]

/-- Every fixed-positive-weight complete terminal order obeys the sharp scalar head ceiling,
with the literal quotient bound on its leaves. -/
theorem abs_sum_mobiusDivisorDilationChannel_le_of_weighted_terminal_completion
    {α : ℝ} (hα : 0<α) (M J : ℕ) (P : Finset ℕ)
    (hterminal : mobiusDivisorSmallSelectionPrimes M  ⊆  P)
    (hfront : ∀ p  ∈  mobiusDivisorSelectionPrimes M \ P,M/p ≤ J)
    (hcomplete : MobiusDivisorWeightedCompletion α M P) :
    |∑ d  ∈  Icc 1 M,mobiusDivisorDilationChannel M d|  ≤ 
      max |mobiusDivisorSelectionFibre M P ∅| (((1+α)/(2*α))*((3/5:ℝ)*J*Real.sqrt M)) := by
  obtain ⟨N,Q,hQ0,hQN,hstep⟩ := hcomplete
  have hsub : ∀ k ≤ N,P ⊆ Q k := by
    intro k hk
    induction k with
    | zero => rw [hQ0]
    | succ k ih =>
      obtain ⟨p,hp,hQ,_⟩ := hstep k (by omega)
      rw [hQ]
      exact (ih (by omega)).trans (subset_insert _ _)
  have hbound : ∀ k ≤ N,|mobiusDivisorSelectionFibre M (Q k) ∅|  ≤ 
      max |mobiusDivisorSelectionFibre M P ∅| (((1+α)/(2*α))*((3/5:ℝ)*J*Real.sqrt M)) := by
    intro k hk
    induction k with
    | zero => rw [hQ0]; exact le_max_left _ _
    | succ k ih =>
      obtain ⟨p,hp,hQ,hdescent⟩ := hstep k (by omega)
      have ht : mobiusDivisorSmallSelectionPrimes M ⊆ Q k := hterminal.trans (hsub k (by omega))
      have hpfree : p ∈ mobiusDivisorSelectionPrimes M \ P :=
        mem_sdiff.mpr ⟨(mem_sdiff.mp hp).1,fun hn => (mem_sdiff.mp hp).2 ((hsub k (by omega)) hn)⟩
      have hleaf := singleton_abs_bound M J (Q k)
        (mem_filter.mp (mem_sdiff.mp hp).1).2 (hfront p hpfree)
      rw [hQ] at hdescent
      have hscalar := (mobiusDivisorWeightedHeadEnergy_terminal_step_iff α M (Q k) ht hp).mp hdescent
      have hb := abs_weightedScalarMerge_le hα hscalar
      have hhead : mobiusDivisorSelectionFibre M (insert p (Q k)) ∅=
          mobiusDivisorSelectionFibre M (Q k) ∅+mobiusDivisorSelectionFibre M (Q k) {p} := by
        rw [mobiusDivisorSelectionFibre_insert]
        simp
      rw [← hhead,← hQ] at hb
      exact hb.trans (max_le (ih (by omega))
        ((mul_le_mul_of_nonneg_left hleaf (by positivity)).trans (le_max_right _ _)))
  have hfinal := hbound N le_rfl
  rw [hQN,mobiusDivisorSelectionFibre_of_all_source_primes_processed M
    (mobiusDivisorSelectionPrimes M) ∅ (Subset.rfl),if_pos rfl] at hfinal
  exact hfinal

/-- A square-root-sized terminal head can complete monotonically only when the final
signed source has the same growth scale. -/
theorem abs_sum_mobiusDivisorDilationChannel_le_sqrt_of_weighted_terminal_completion
    {α : ℝ} (hα : 0<α) (M J : ℕ) (P : Finset ℕ) (C : ℝ)
    (hterminal : mobiusDivisorSmallSelectionPrimes M ⊆ P)
    (hfront : ∀ p ∈ mobiusDivisorSelectionPrimes M \ P,M/p ≤ J)
    (hhead : |mobiusDivisorSelectionFibre M P ∅| ≤ C*Real.sqrt M)
    (hcomplete : MobiusDivisorWeightedCompletion α M P) :
    |∑ d ∈ Icc 1 M,mobiusDivisorDilationChannel M d| ≤
      max C (((1+α)/(2*α))*((3/5:ℝ)*J))*Real.sqrt M := by
  apply (abs_sum_mobiusDivisorDilationChannel_le_of_weighted_terminal_completion
    hα M J P hterminal hfront hcomplete).trans
  apply max_le
  · exact hhead.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  · calc
      _ = (((1+α)/(2*α))*((3/5:ℝ)*J))*Real.sqrt M := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)

/-- On arbitrarily large cutoffs of every fixed grid, every completable terminal core
with bounded remaining quotients must have a head larger than any prescribed square-root envelope. -/
theorem exists_weighted_terminal_head_escape_on_grid
    {c : ℕ} (hc : 0<c) {α : ℝ} (hα : 0<α) (C : ℝ) (J N₀ : ℕ) :
    ∃ N : ℕ,N₀ ≤ N ∧ ∀ P : Finset ℕ,
      mobiusDivisorSmallSelectionPrimes (c*N) ⊆ P →
      (∀ p ∈ mobiusDivisorSelectionPrimes (c*N) \ P,(c*N)/p ≤ J) →
      MobiusDivisorWeightedCompletion α (c*N) P →
      C*Real.sqrt (c*N:ℕ) < |mobiusDivisorSelectionFibre (c*N) P ∅| := by
  obtain ⟨N,hN,hgt⟩ := exists_sum_mobiusDivisorDilationChannel_grid_gt_sqrt_after hc
    (max C (((1+α)/(2*α))*((3/5:ℝ)*J))) N₀
  refine ⟨N,hN,?_⟩
  intro P hterminal hfront hcomplete
  by_contra hn
  have hb := abs_sum_mobiusDivisorDilationChannel_le_sqrt_of_weighted_terminal_completion
    hα (c*N) J P C hterminal hfront (le_of_not_gt hn) hcomplete
  exact (not_lt_of_ge hb) hgt

/-- No fixed positive weight gives complete monotone orders through uniformly small-head,
bounded-quotient terminal cores, even eventually on one fixed positive integer grid. -/
theorem not_exists_uniform_weighted_small_terminal_completion :
    ¬ ∃ (c : ℕ) (α C : ℝ) (J N₀ : ℕ),0<c ∧ 0<α ∧ ∀ N : ℕ,N₀ ≤ N →
      ∃ P : Finset ℕ,mobiusDivisorSmallSelectionPrimes (c*N) ⊆ P ∧
        (∀ p ∈ mobiusDivisorSelectionPrimes (c*N) \ P,(c*N)/p ≤ J) ∧
        |mobiusDivisorSelectionFibre (c*N) P ∅| ≤ C*Real.sqrt (c*N:ℕ) ∧
        MobiusDivisorWeightedCompletion α (c*N) P := by
  rintro ⟨c,α,C,J,N₀,hc,hα,hall⟩
  obtain ⟨N,hN,he⟩ := exists_weighted_terminal_head_escape_on_grid hc hα C J N₀
  obtain ⟨P,hterminal,hfront,hhead,hcomplete⟩ := hall N hN
  exact (not_lt_of_ge hhead) (he P hterminal hfront hcomplete)

/-- The previously constructed actual small terminal cores exist arbitrarily far out
where their complete fixed-positive-weight monotone continuation is impossible. -/
theorem exists_mobiusDivisorSmallTerminalCore_without_weighted_completion :
    ∃ b : ℕ,8 ≤ b ∧ ∀ α ε : ℝ,0<α → 0<ε → ∀ N₀ : ℕ,
      ∃ N : ℕ,N₀ ≤ N ∧
        let M := 7*(b+1)*(4*N)
        let A := GaloisForLFunctions.HTGeometry.primesInIoc (b*(4*N)) ((b+1)*(4*N))
        let B := mobiusDivisorActiveLatePrimes M
        ∃ P ⊆ mobiusDivisorSelectionPrimes M,
          mobiusDivisorSelectionPrimes M \ (A ∪ B) ⊆ P ∧
          mobiusDivisorSmallSelectionPrimes M ⊆ P ∧
          |mobiusDivisorSelectionFibre M P ∅| ≤ 5*Real.sqrt M ∧
          mobiusDivisorSuccessorEnvelope M P ≤ ε*(M:ℝ)^(2 : ℕ) ∧
          ¬ MobiusDivisorWeightedCompletion α M P := by
  obtain ⟨b,hb,hcores⟩ := exists_mobiusDivisorSmallTerminalCore
  refine ⟨b,hb,?_⟩
  intro α ε hα hε N₀
  obtain ⟨L,hL⟩ := Filter.eventually_atTop.mp (hcores ε hε)
  have hc : 0<7*(b+1)*4 := by positivity
  obtain ⟨N,hN,hescape⟩ := exists_weighted_terminal_head_escape_on_grid hc hα 5 7 (max L (max N₀ 1))
  have hNL : L ≤ N := (le_max_left _ _).trans hN
  have hNN₀ : N₀ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN1 : 1 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨P,hP,hcover,hterminal,hhead,henv⟩ := hL N hNL
  have hM : 7*(b+1)*4*N=7*(b+1)*(4*N) := by ring
  rw [hM] at hescape
  refine ⟨N,hNN₀,P,hP,hcover,hterminal,hhead,henv,?_⟩
  intro hcomplete
  have hfront : ∀ p ∈ mobiusDivisorSelectionPrimes (7*(b+1)*(4*N)) \ P,
      (7*(b+1)*(4*N))/p ≤ 7 := by
    intro p hp
    obtain ⟨hpM,hpP⟩ := mem_sdiff.mp hp
    have hpU : p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (b*(4*N)) ((b+1)*(4*N)) ∪
        mobiusDivisorActiveLatePrimes (7*(b+1)*(4*N)) := by
      by_contra hn
      exact hpP (hcover (mem_sdiff.mpr ⟨hpM,hn⟩))
    have hpprime := (mem_filter.mp hpM).2
    have h8 : 7*(b+1)*(4*N)<8*p := by
      rcases mem_union.mp hpU with hpa|hpb
      · obtain ⟨_,hlo,_⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hpa
        nlinarith
      · obtain ⟨_,_,h2p⟩ := mem_mobiusDivisorActiveLatePrimes hpb
        omega
    have hd := (Nat.div_lt_iff_lt_mul hpprime.pos).mpr (show 7*(b+1)*(4*N)<8*p from h8)
    omega
  exact (not_lt_of_ge hhead) (hescape P hterminal hfront hcomplete)

end RHTower
