import GaloisForLFunctions.RHTower.MobiusDivisorTerminalCoreExistence
import GaloisForLFunctions.RHTower.MobiusDivisorPaidCutoffInterval

/-!
# Prime-exhaustive geometric clock checkpoints

Actual signed terminal windows yield a universal bound of `200*M^2` for
the full logarithmically weighted clock energy. Prime density absorbs the
logarithmic weight; no constant depends on the processed core cardinality.

Choose checkpoints with `M(n+1)=8*M(n)`. Every next core contains every prime
active at the previous checkpoint, so the cores are nested and exhaust all
primes. The same bound holds at every checkpoint, with bound `201*L^2` on
its original fourth-root cutoff collar. No energy or cancellation premise
is assumed by either public construction.

The estimate is at the current checkpoint. It does not control the previous
cutoff after its primes are completely processed, or the gaps between the
collars. A paid continuation through those original cutoffs remains missing;
this theorem does not establish bounded completed critical action.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology
namespace RHTower

private lemma clock_le_log_energy (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorFiniteClockEnergy 1 M P ≤
      (1+Real.log M)*mobiusDivisorSelectionEnergy M P := by
  rw [mobiusDivisorSelectionEnergy_eq_inclusive_squarefree,mul_sum]
  apply sum_le_sum
  intro r hr
  have hr' := mem_Icc.mp (mem_filter.mp hr).1
  have hlog : 1+Real.log (r:ℝ) ≤ 1+Real.log (M:ℝ) :=
    add_le_add le_rfl (Real.log_le_log (by exact_mod_cast hr'.1) (by exact_mod_cast hr'.2))
  have h := mul_le_mul_of_nonneg_right hlog
    (show 0 ≤ (r:ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^2 by positivity)
  simpa only [mul_assoc] using h

private lemma eventually_log_prime_count :
    ∀ᶠ M : ℕ in atTop, (1+Real.log M)*(Nat.primeCounting M:ℝ) ≤ 4*M := by
  have ht := tendsto_primeCounting_nat_ratio.eventually
    (eventually_lt_nhds (by norm_num : (1:ℝ)<2))
  have hl := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [ht,hl,eventually_ge_atTop (1:ℕ)] with M h hlog hM
  change 1 ≤ Real.log (M:ℝ) at hlog
  have hm : (0:ℝ)<M := by exact_mod_cast hM
  have hh : (Nat.primeCounting M:ℝ)*Real.log M < 2*M := by
    apply (div_lt_iff₀ hm).mp
    simpa only [div_div_eq_mul_div] using h
  have hn : (0:ℝ) ≤ Nat.primeCounting M := by positivity
  nlinarith only [hh,mul_nonneg hn (sub_nonneg.mpr hlog)]

private lemma eventually_terminal_clock_bound :
    ∀ᶠ M : ℕ in atTop, ∀ P : Finset ℕ,
      mobiusDivisorSmallSelectionPrimes M ⊆ P →
      (∀ p ∈ mobiusDivisorSelectionPrimes M \ P,M/p ≤ 7) →
      |mobiusDivisorSelectionFibre M P ∅| ≤ 5*Real.sqrt M →
      mobiusDivisorFiniteClockEnergy 1 M P ≤ 200*(M:ℝ)^2 := by
  filter_upwards [eventually_log_prime_count,eventually_ge_atTop (1:ℕ)] with M hc hM
  intro P hterminal hfront hhead
  have hb := mobiusDivisorSuccessorEnvelope_le_terminal_density M 7 P 5
    (by norm_num) hterminal hfront hhead
  have he := ((mobiusDivisorSuccessorEnvelope_le_iff _ _ _).mp hb).1
  have hw : 0 ≤ 1+Real.log (M:ℝ) := by positivity
  have hh := (clock_le_log_energy M P).trans (mul_le_mul_of_nonneg_left he hw)
  have hlog : 1+Real.log (M:ℝ) ≤ M := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ)<M by exact_mod_cast hM)
    linarith
  have h1 := mul_le_mul_of_nonneg_right hlog (show 0 ≤ (M:ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_right hc (show 0 ≤ (M:ℝ) by positivity)
  norm_num at hh
  nlinarith only [hh,h1,h2,sq_nonneg (M:ℝ)]

/-- Actual signed source windows produce a uniformly bounded full clock
energy while processing every prime up to their lower boundary. The bound
and eventual threshold are independent of the size of any inherited core
below that boundary. -/
theorem eventually_exists_mobiusDivisorTerminalClockBudget :
    ∃ b : ℕ, 8 ≤ b ∧ ∀ᶠ N : ℕ in atTop,
      let M := 7*(b+1)*(4*N)
      ∃ P : Finset ℕ, P ⊆ mobiusDivisorSelectionPrimes M ∧
        mobiusDivisorSelectionPrimes (4*b*N+1) ⊆ P ∧
        mobiusDivisorFiniteClockEnergy 1 M P ≤ 200*(M:ℝ)^2 ∧
        ∀ L : ℕ, M ≤ L → (L:ℝ)-M ≤ Real.sqrt (Real.sqrt M) →
          mobiusDivisorFiniteClockEnergy 1 L P ≤ 201*(L:ℝ)^2 := by
  obtain ⟨b,hb,hcores⟩ := exists_mobiusDivisorSmallTerminalCore
  have hclock : Tendsto (fun N : ℕ => 7*(b+1)*(4*N)) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro N
    change N ≤ 7*(b+1)*(4*N)
    nlinarith
  have hW := hclock.eventually eventually_terminal_clock_bound
  have hT := hclock.eventually
    (eventually_mobiusDivisorFiniteClockEnergy_fourth_root_transport 200 1
      (by norm_num) (by norm_num))
  refine ⟨b,hb,?_⟩
  filter_upwards [hcores 1 (by norm_num),hW,hT,eventually_ge_atTop (1:ℕ)] with N hQ hw ht hN
  let M := 7*(b+1)*(4*N)
  obtain ⟨P,hP,hcover,hterminal,hhead,_⟩ := hQ
  have hfront : ∀ p ∈ mobiusDivisorSelectionPrimes M \ P,M/p ≤ 7 := by
    intro p hp
    obtain ⟨hpM,hpP⟩ := mem_sdiff.mp hp
    have hpU : p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (b*(4*N)) ((b+1)*(4*N)) ∪
        mobiusDivisorActiveLatePrimes M := by
      by_contra hn
      exact hpP (hcover (mem_sdiff.mpr ⟨hpM,hn⟩))
    have hpprime := (mem_filter.mp hpM).2
    have h8 : M < 8*p := by
      rcases mem_union.mp hpU with hpa|hpb
      · obtain ⟨_,hlo,_⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hpa
        dsimp [M]
        nlinarith
      · obtain ⟨_,_,h2p⟩ := mem_mobiusDivisorActiveLatePrimes hpb
        omega
    have hd := (Nat.div_lt_iff_lt_mul hpprime.pos).mpr h8
    omega
  have hbound := hw P hterminal hfront hhead
  refine ⟨P,hP,?_,hbound,?_⟩
  · intro p hp
    obtain ⟨hpr,hprime⟩ := mem_filter.mp hp
    have hpB : p ≤ 4*b*N := by have := mem_range.mp hpr; omega
    apply hcover
    apply Finset.mem_sdiff.mpr
    constructor
    · apply mem_filter.mpr
      refine ⟨mem_range.mpr ?_,hprime⟩
      nlinarith
    · intro h
      rcases mem_union.mp h with hpa|hpb
      · have := (GaloisForLFunctions.HTGeometry.mem_primesInIoc hpa).2.1
        nlinarith
      · have := (mem_mobiusDivisorActiveLatePrimes hpb).2.2
        nlinarith
  · intro L hML hgap
    have hlog := Real.log_natCast_nonneg M
    have hWlog : mobiusDivisorFiniteClockEnergy 1 M P ≤
        200*(M:ℝ)^2*(1+Real.log M) := by
      nlinarith only [hbound,mul_nonneg (sq_nonneg (M:ℝ)) hlog]
    have htrans := ht P hWlog L hML hgap
    have hsq : (M:ℝ)^2 ≤ (L:ℝ)^2 := by
      gcongr
    nlinarith only [htrans,hbound,hsq]

/-- A nested, prime-exhaustive family of actual cores has one full weighted
energy bound at geometric clock checkpoints and on their fourth-root collars.
Every checkpoint's active primes are all processed at the next checkpoint.
This does not bound the energy at the earlier cutoff after that processing,
nor the intervals between the collars. -/
theorem exists_mobiusDivisorExhaustiveClockCheckpoints :
    ∃ M : ℕ → ℕ, ∃ P : ℕ → Finset ℕ,
      0 < M 0 ∧ (∀ n,M (n+1)=8*M n) ∧ StrictMono M ∧
      (∀ n,P n ⊆ mobiusDivisorSelectionPrimes (M n)) ∧
      (∀ n,mobiusDivisorSelectionPrimes (M n) ⊆ P (n+1)) ∧
      Monotone P ∧ (∀ p : ℕ,p.Prime → ∀ᶠ n : ℕ in atTop,p ∈ P n) ∧
      (∀ n,mobiusDivisorFiniteClockEnergy 1 (M n) (P n) ≤ 200*(M n:ℝ)^2) ∧
      ∀ n L : ℕ,M n ≤ L → (L:ℝ)-M n ≤ Real.sqrt (Real.sqrt (M n)) →
        mobiusDivisorFiniteClockEnergy 1 L (P n) ≤ 201*(L:ℝ)^2 := by
  obtain ⟨b,hb,hcores⟩ := eventually_exists_mobiusDivisorTerminalClockBudget
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.mp hcores
  let N := fun n : ℕ => (T+1)*8^n
  let M := fun n : ℕ => 7*(b+1)*(4*N n)
  have hN (n : ℕ) : T ≤ N n := by
    have hp : 1 ≤ (8:ℕ)^n := Nat.one_le_pow n 8 (by omega)
    dsimp [N]
    nlinarith
  have hall (n : ℕ) := hT (N n) (hN n)
  choose P hsub hcover henergy hcollar using hall
  have hpos (n : ℕ) : 0 < M n := by dsimp [M,N]; positivity
  have hstep (n : ℕ) : M (n+1)=8*M n := by dsimp [M,N]; rw [pow_succ]; ring
  have hmono : StrictMono M := strictMono_nat_of_lt_succ (fun n => by rw [hstep]; nlinarith [hpos n])
  have hprev (n : ℕ) : mobiusDivisorSelectionPrimes (M n) ⊆ P (n+1) := by
    intro p hp
    apply hcover (n+1)
    obtain ⟨hpr,hprime⟩ := mem_filter.mp hp
    refine mem_filter.mpr ⟨mem_range.mpr ?_,hprime⟩
    have hpM := mem_range.mp hpr
    have hclock : M n ≤ 4*b*N (n+1)+1 := by
      dsimp [M,N]
      rw [pow_succ]
      nlinarith [Nat.zero_le ((T+1)*8^n)]
    exact hpM.trans_le hclock
  have hPmono : Monotone P := monotone_nat_of_le_succ (fun n => (hsub n).trans (hprev n))
  refine ⟨M,P,hpos 0,hstep,hmono,hsub,hprev,hPmono,?_,henergy,hcollar⟩
  intro p hp
  have hg := hmono.tendsto_atTop.eventually_ge_atTop (8*(p+1))
  filter_upwards [hg,eventually_ge_atTop (1:ℕ)] with n hn hn1
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  rw [hstep] at hn
  apply hprev k
  exact mem_filter.mpr ⟨mem_range.mpr (by omega),hp⟩

end RHTower
