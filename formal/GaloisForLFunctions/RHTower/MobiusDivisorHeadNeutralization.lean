import GaloisForLFunctions.RHTower.MobiusDivisorNonemptyEnergy
import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeInterleavingCapacity

/-!
# Source-derived head neutralization by late primes

A finite mass cover can be selected with overshoot bounded by one weight and
paid for by the selected weight squares. Applied to isolated late primes, it
releases the entire initial head square without exceeding the initial energy
at any intermediate subset. Actual late-prime mass eventually covers the
unprocessed source head, giving an unconditional initial balancing block.
-/
noncomputable section
open Finset Filter Topology
namespace RHTower

/-- A bounded positive mass cover has a subset whose overshoot is paid for by its selected squares. -/
theorem exists_mass_cover_with_square_reserve {α : Type*} [DecidableEq α]
    (U : Finset α) (w : α → ℝ) (a : ℝ) (ha : 0 ≤ a) :
    ∀ h : ℝ,0 ≤ h → (∀ p ∈ U,0 ≤ w p ∧ w p ≤ a) → h ≤ ∑ p ∈ U,w p →
      ∃ L ⊆ U,0 ≤ (∑ p ∈ L,w p)-h ∧ (∑ p ∈ L,w p)-h ≤ a ∧
        ((∑ p ∈ L,w p)-h)^(2 : ℕ) ≤ ∑ p ∈ L,(w p)^(2 : ℕ) := by
  induction U using Finset.induction_on with
  | empty =>
    intro h hh hw hcover
    simp only [sum_empty] at hcover
    have he : h=0 := le_antisymm hcover hh
    subst h
    exact ⟨∅,by simp,by simp,by simpa using ha,by simp⟩
  | @insert p U hpU ih =>
    intro h hh hw hcover
    have hp := hw p (mem_insert_self p U)
    by_cases hwp : h ≤ w p
    · refine ⟨{p},singleton_subset_iff.mpr (mem_insert_self p U),?_⟩
      simp only [sum_singleton]
      refine ⟨by linarith,by linarith,?_⟩
      have hprod := mul_nonneg hh (show 0 ≤ 2*w p-h by linarith)
      nlinarith only [hprod]
    · have htarget : 0 ≤ h-w p := by linarith
      have hwU : ∀ q ∈ U,0 ≤ w q ∧ w q ≤ a := fun q hq => hw q (mem_insert_of_mem hq)
      have htarget_cover : h-w p ≤ ∑ q ∈ U,w q := by
        rw [sum_insert hpU] at hcover
        linarith only [hcover]
      obtain ⟨L,hLU,h0,h1,hsq⟩ := ih (h-w p) htarget hwU htarget_cover
      have hpL : p ∉ L := fun h => hpU (hLU h)
      refine ⟨insert p L,insert_subset_insert p hLU,?_⟩
      simp only [sum_insert hpL]
      have he : w p+(∑ q ∈ L,w q)-h=(∑ q ∈ L,w q)-(h-w p) := by ring
      rw [he]
      exact ⟨h0,h1,hsq.trans (le_add_of_nonneg_left (sq_nonneg (w p)))⟩

/-- Every first quotient block retains its literal square-root mass and first divisor defect. -/
theorem divisorUnsignedDilationChannel_eq_first_block {M d : ℕ}
    (hd : 1 ≤ d) (hdM : d<M) (hMd : M ≤ 2*d) :
    divisorUnsignedDilationChannel M d =
      (Real.sqrt M-Real.sqrt d)*primeFreeDivisorDefect 1 := by
  have hdiv (k : ℕ) (hk : k ∈ Icc d (M-1)) : k/d=1 := by
    obtain ⟨hdk,hkM⟩ := mem_Icc.mp hk
    have hlo : 1 ≤ k/d := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using hdk)
    have hhi : k/d<2 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    omega
  unfold divisorUnsignedDilationChannel
  calc
    _ = ∑ k ∈ Icc d (M-1),(Real.sqrt (k+1:ℕ)-Real.sqrt k)*primeFreeDivisorDefect 1 :=
      sum_congr rfl (fun k hk => by rw [hdiv k hk])
    _ = _ := by
      rw [← sum_mul,sum_sqrt_succ_sub_sqrt_Icc_general (by omega : d ≤ M-1),
        show M-1+1=M by omega]

/-- Each late coefficient has at most a square-root-sized mass, unconditionally. -/
theorem divisorUnsignedDilationChannel_late_le_sqrt {M d : ℕ}
    (hd : 1 ≤ d) (hdM : d<M) (hMd : M ≤ 2*d) :
    divisorUnsignedDilationChannel M d ≤ Real.sqrt M := by
  have hD : primeFreeDivisorDefect 1 ≤ 1 := by
    norm_num [primeFreeDivisorDefect]
    linarith [eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion]
  have hgap : 0 ≤ Real.sqrt M-Real.sqrt d :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast hdM.le))
  rw [divisorUnsignedDilationChannel_eq_first_block hd hdM hMd]
  have h := mul_le_mul_of_nonneg_left hD hgap
  nlinarith only [h,Real.sqrt_nonneg (d:ℝ)]

/-- A covered nonnegative head can be neutralized while releasing its whole square and controlling every intermediate subset. -/
theorem exists_mobiusDivisorLatePrime_head_neutralization (M : ℕ) (P U : Finset ℕ)
    (hU : ∀ p ∈ U,p.Prime ∧ p<M ∧ M≤2*p) (hfree : ∀ p ∈ U,p ∉ P)
    (hh : 0 ≤ mobiusDivisorSelectionFibre M P ∅)
    (hcover : mobiusDivisorSelectionFibre M P ∅ ≤ ∑ p ∈ U,divisorUnsignedDilationChannel M p) :
    ∃ L ⊆ U,
      (-Real.sqrt M ≤ mobiusDivisorSelectionFibre M (P ∪ L) ∅ ∧
        mobiusDivisorSelectionFibre M (P ∪ L) ∅ ≤ 0) ∧
      (mobiusDivisorSelectionFibre M (P ∪ L) ∅)^(2 : ℕ) ≤ M ∧
      mobiusDivisorSelectionEnergy M (P ∪ L) ≤ mobiusDivisorNonemptyEnergy M P ∧
      ∀ R ⊆ L,mobiusDivisorSelectionEnergy M (P ∪ R) ≤ mobiusDivisorSelectionEnergy M P := by
  obtain ⟨L,hLU,h0,h1,hsq⟩ := exists_mass_cover_with_square_reserve U
    (divisorUnsignedDilationChannel M) (Real.sqrt M) (Real.sqrt_nonneg _)
    (mobiusDivisorSelectionFibre M P ∅) hh
    (fun p hp => ⟨divisorUnsignedDilationChannel_nonneg M p,
      divisorUnsignedDilationChannel_late_le_sqrt (hU p hp).1.pos (hU p hp).2.1 (hU p hp).2.2⟩) hcover
  have hL : ∀ p ∈ L,p.Prime ∧ p<M ∧ M≤2*p := fun p hp => hU p (hLU hp)
  have hf : ∀ p ∈ L,p ∉ P := fun p hp => hfree p (hLU hp)
  have hc (p : ℕ) (hp : p ∈ L) : mobiusDivisorDilationChannel M p =
      -divisorUnsignedDilationChannel M p := by
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
      ArithmeticFunction.moebius_apply_prime (hL p hp).1]
    push_cast
    ring
  have hsum : (∑ p ∈ L,mobiusDivisorDilationChannel M p) =
      -(∑ p ∈ L,divisorUnsignedDilationChannel M p) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl hc
  have hsquares : (∑ p ∈ L,(mobiusDivisorDilationChannel M p)^(2 : ℕ)) =
      ∑ p ∈ L,(divisorUnsignedDilationChannel M p)^(2 : ℕ) := by
    apply sum_congr rfl
    intro p hp
    rw [hc p hp,neg_sq]
  have hhead := mobiusDivisorSelectionHead_union_late_primes M P L hL hf
  rw [hsum] at hhead
  have hrange : -Real.sqrt M ≤ mobiusDivisorSelectionFibre M (P ∪ L) ∅ ∧
      mobiusDivisorSelectionFibre M (P ∪ L) ∅ ≤ 0 := by
    constructor <;> linarith only [hhead,h0,h1]
  have hHsq : (mobiusDivisorSelectionFibre M (P ∪ L) ∅)^(2 : ℕ) ≤ M := by
    have hprod := mul_nonneg (show 0 ≤ Real.sqrt M+mobiusDivisorSelectionFibre M (P ∪ L) ∅ by linarith only [hrange.1])
      (show 0 ≤ Real.sqrt M-mobiusDivisorSelectionFibre M (P ∪ L) ∅ by linarith [Real.sqrt_nonneg (M:ℝ),hrange.2])
    nlinarith only [hprod,Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) M)]
  have hV := mobiusDivisorNonemptyEnergy_union_late_primes M P L hL hf
  rw [hsquares] at hV
  have henergy : mobiusDivisorSelectionEnergy M (P ∪ L) ≤ mobiusDivisorNonemptyEnergy M P := by
    unfold mobiusDivisorNonemptyEnergy at hV
    rw [hhead] at hV
    unfold mobiusDivisorNonemptyEnergy
    nlinarith only [hV,hsq]
  have hstart : mobiusDivisorNonemptyEnergy M P ≤ mobiusDivisorSelectionEnergy M P := by
    unfold mobiusDivisorNonemptyEnergy
    exact sub_le_self _ (sq_nonneg _)
  refine ⟨L,hLU,hrange,hHsq,henergy,?_⟩
  exact (mobiusDivisorSelectionEnergy_late_block_ceiling_iff M P L
    (mobiusDivisorSelectionEnergy M P) hL hf).mpr ⟨le_rfl,henergy.trans hstart⟩

/-- The unprocessed empty-cofactor head is exactly the unsigned unit channel. -/
theorem mobiusDivisorSelectionHead_empty_eq_unit_channel (M : ℕ) :
    mobiusDivisorSelectionFibre M ∅ ∅=divisorUnsignedDilationChannel M 1 := by
  rw [mobiusDivisorSelectionFibre_eq_sum_Icc]
  by_cases hM : M=0
  · subst M
    simp [divisorUnsignedDilationChannel]
  have hM1 : 1 ≤ M := by omega
  rw [sum_eq_single 1]
  · simp [mobiusDivisorDilationChannel_eq_moebius_unsigned]
  · intro d hd hd1
    have hd0 : d ≠ 0 := by have := (mem_Icc.mp hd).1; omega
    simp [Nat.primeFactors_eq_empty,hd0,hd1]
  · simp [hM1]

/-- The original retained head has nonnegative orientation at every cutoff. -/
theorem mobiusDivisorSelectionHead_empty_nonneg (M : ℕ) :
    0 ≤ mobiusDivisorSelectionFibre M ∅ ∅ := by
  rw [mobiusDivisorSelectionHead_empty_eq_unit_channel]
  exact divisorUnsignedDilationChannel_nonneg M 1

/-- The original diagonal supplies a uniform linear budget for its initial head. -/
theorem mobiusDivisorSelectionHead_empty_le_linear (M : ℕ) :
    mobiusDivisorSelectionFibre M ∅ ∅ ≤ 27*M := by
  have hsq := sum_mobiusDivisorSelectionFibre_sq_le_energy M ∅ {∅}
  simp only [sum_singleton] at hsq
  have hQ := sum_mobiusDivisorDilationChannel_sq_le_quadratic M
  rw [← mobiusDivisorSelectionEnergy_empty] at hQ
  have hn := Nat.cast_nonneg (α := ℝ) M
  nlinarith only [hsq,hQ,hn]

/-- Actual late-prime mass eventually covers the original head, with no signed-sum or endpoint hypothesis. -/
theorem eventually_mobiusDivisorLatePrimeMass_covers_initial_head :
    ∀ᶠ N : ℕ in atTop,mobiusDivisorSelectionFibre (4*N) ∅ ∅ ≤ mobiusDivisorLatePrimeMass (4*N) := by
  have hT := tendsto_mobiusDivisorLatePrimeMass_div_atTop.eventually_gt_atTop 27
  filter_upwards [hT,eventually_ge_atTop (1:ℕ)] with N hT hN
  have hmass := (lt_div_iff₀ (show (0:ℝ)<4*N by positivity)).mp hT
  have hh := mobiusDivisorSelectionHead_empty_le_linear (4*N)
  push_cast at hh
  linarith only [hh,hmass]

/-- An unconditional initial late-prime block has a square-root-sized head and releases the original head energy at every sufficiently large cutoff in the cofinal family. -/
theorem eventually_exists_mobiusDivisorInitialHeadNeutralization :
    ∀ᶠ N : ℕ in atTop,∃ L ⊆ mobiusDivisorActiveLatePrimes (4*N),
      (-Real.sqrt (4*N:ℕ) ≤ mobiusDivisorSelectionFibre (4*N) L ∅ ∧
        mobiusDivisorSelectionFibre (4*N) L ∅ ≤ 0) ∧
      (mobiusDivisorSelectionFibre (4*N) L ∅)^(2 : ℕ) ≤ (4*N:ℕ) ∧
      mobiusDivisorSelectionEnergy (4*N) L ≤ mobiusDivisorNonemptyEnergy (4*N) ∅ ∧
      ∀ R ⊆ L,mobiusDivisorSelectionEnergy (4*N) R ≤ mobiusDivisorSelectionEnergy (4*N) ∅ := by
  filter_upwards [eventually_mobiusDivisorLatePrimeMass_covers_initial_head] with N hcover
  rw [← sum_mobiusDivisorActiveLatePrimes] at hcover
  have h := exists_mobiusDivisorLatePrime_head_neutralization (4*N) ∅
    (mobiusDivisorActiveLatePrimes (4*N)) (fun _ hp => mem_mobiusDivisorActiveLatePrimes hp)
    (by simp) (mobiusDivisorSelectionHead_empty_nonneg _) hcover
  simpa only [empty_union] using h
end RHTower
