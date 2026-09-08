import GaloisForLFunctions.RHTower.MobiusDivisorCoareaHeadTransport
import GaloisForLFunctions.RHTower.MobiusDivisorUniformSuccessorTransport
import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeCompensation

/-!
# Unbounded coarea head slope after the first prime

After processing prime two, the head contains only original indices one
and two, so its absolute mass is at most `(6/5) sqrt M`. Every late prime
remains an isolated pure negative cell and contributes its complete
absolute mass to nonempty conditional energy.

On the cofinal grid `M = 4N`, the actual coarea head slope is consequently
at least the late-prime mass minus `4 sqrt M`. The corpus prime-window
mass theorem then gives `g(4N,{2})/(4N) → +∞` unconditionally. In
combination with invariant late-prime slope transport, this identifies
a positive growth direction that isolated late-prime processing cannot
reverse. No numerical estimate or hypothesis on zeta zeros is used.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology
namespace RHTower

private lemma channel_bound (M d : ℕ) :
    |mobiusDivisorDilationChannel M d| ≤ (3/5:ℝ)*Real.sqrt M := by
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,abs_mul,
    abs_of_nonneg (divisorUnsignedDilationChannel_nonneg M d)]
  have hm : |(ArithmeticFunction.moebius d:ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
  calc
    _ ≤ 1*divisorUnsignedDilationChannel M d :=
      mul_le_mul_of_nonneg_right hm (divisorUnsignedDilationChannel_nonneg M d)
    _ ≤ _ := by simpa using divisorUnsignedDilationChannel_le_three_fifths_sqrt M d

/-- Processing prime two collects at most two uniformly bounded original source amplitudes. -/
theorem mobiusDivisorFibreAbsoluteMass_two_head_le (M : ℕ) :
    mobiusDivisorFibreAbsoluteMass M {2} ∅ ≤ (6/5:ℝ)*Real.sqrt M := by
  let I := (mobiusDivisorSelectionIndices M).filter (fun d => d.primeFactors \ {2} = ∅)
  have hsub : I ⊆ ({1,2}:Finset ℕ) := by
    intro d hd
    obtain ⟨hd,he⟩ := mem_filter.mp hd
    have hs := (mem_filter.mp hd).2
    have hf : d.primeFactors ⊆ {2} := sdiff_eq_empty_iff_subset.mp he
    rcases subset_singleton_iff.mp hf with hz | hz
    · have hd1 : d=1 := by rw [← Nat.prod_primeFactors_of_squarefree hs,hz]; simp
      simp [hd1]
    · have hd2 : d=2 := by rw [← Nat.prod_primeFactors_of_squarefree hs,hz]; simp
      simp [hd2]
  have he : mobiusDivisorFibreAbsoluteMass M {2} ∅ =
      ∑ d ∈ I,|mobiusDivisorDilationChannel M d| := by
    simp [mobiusDivisorFibreAbsoluteMass,subsetLabelFibre,I,sum_filter]
  rw [he]
  calc
    _ ≤ ∑ d ∈ ({1,2}:Finset ℕ),|mobiusDivisorDilationChannel M d| :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
    _ ≤ ∑ _d ∈ ({1,2}:Finset ℕ),(3/5:ℝ)*Real.sqrt M :=
      sum_le_sum (fun d _ => channel_bound M d)
    _ = _ := by norm_num; ring

/-- Every late-prime source mass survives in nonempty coarea after processing prime two. -/
theorem mobiusDivisorNonemptyCoarea_two_ge_lateMass (N : ℕ) :
    mobiusDivisorLatePrimeMass (4*N) ≤ mobiusDivisorNonemptyCoarea (4*N) {2} := by
  let L := GaloisForLFunctions.HTGeometry.primesInIoc ((4*N)/2) (4*N)
  let t := fun R => (mobiusDivisorSelectionFibre (4*N) {2} R)^2 /
    mobiusDivisorFibreAbsoluteMass (4*N) {2} R
  have hprime (p : ℕ) (hp : p ∈ L) : p.Prime ∧ p<4*N ∧ 4*N≤2*p ∧ p ∉ ({2}:Finset ℕ) := by
    obtain ⟨hpr,hlo,hhi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
    have hne : p≠4*N := by
      intro he
      have hd : 2 ∣ p := by rw [he]; omega
      have hp2 : 2=p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpr).mp hd
      omega
    refine ⟨hpr,by omega,by omega,?_⟩
    simp only [mem_singleton]
    omega
  have hsub : L.image (fun p => ({p}:Finset ℕ)) ⊆
      (mobiusDivisorSelectionPrimes (4*N)).powerset.erase ∅ := by
    intro R hR
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hR
    have h := hprime p hp
    have hpU : p ∈ mobiusDivisorSelectionPrimes (4*N) :=
      mem_filter.mpr ⟨mem_range.mpr h.2.1,h.1⟩
    simp [hpU]
  have hterm (p : ℕ) (hp : p ∈ L) : t {p} = divisorUnsignedDilationChannel (4*N) p := by
    have h := hprime p hp
    dsimp [t]
    rw [mobiusDivisorSelectionFibre_late_prime h.1 h.2.1 h.2.2.1 {2} {p}
      h.2.2.2 (mem_singleton_self p),
      mobiusDivisorFibreAbsoluteMass_late_prime h.1 h.2.1 h.2.2.1 {2} {p}
        h.2.2.2 (mem_singleton_self p)]
    simp only [if_true]
    have hc : |mobiusDivisorDilationChannel (4*N) p| = divisorUnsignedDilationChannel (4*N) p := by
      simp [mobiusDivisorDilationChannel_eq_moebius_unsigned,
        ArithmeticFunction.moebius_apply_prime h.1,
        abs_of_nonneg (divisorUnsignedDilationChannel_nonneg (4*N) p)]
    rw [← hc]
    by_cases hz : mobiusDivisorDilationChannel (4*N) p=0
    · simp [hz]
    · apply (div_eq_iff (abs_ne_zero.mpr hz)).mpr
      nlinarith only [sq_abs (mobiusDivisorDilationChannel (4*N) p)]
  change (∑ p ∈ L,divisorUnsignedDilationChannel (4*N) p) ≤
    ∑ R ∈ (mobiusDivisorSelectionPrimes (4*N)).powerset.erase ∅,t R
  calc
    _ = ∑ p ∈ L,t {p} := sum_congr rfl (fun p hp => (hterm p hp).symm)
    _ = ∑ R ∈ L.image (fun p => ({p}:Finset ℕ)),t R := by
      rw [sum_image (by intro a _ b _ he; simpa using he)]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun R _ _ =>
      div_nonneg (sq_nonneg _) (mobiusDivisorFibreAbsoluteMass_nonneg (4*N) {2} R))

/-- The actual initial coarea head slope retains all late-prime mass up to a square-root loss. -/
theorem mobiusDivisorCoareaHeadSlope_two_ge_lateMass (N : ℕ) :
    mobiusDivisorLatePrimeMass (4*N)-4*Real.sqrt (4*N:ℕ) ≤
      mobiusDivisorCoareaHeadSlope (4*N) {2} := by
  have hK := mobiusDivisorNonemptyCoarea_two_ge_lateMass N
  have ha := mobiusDivisorFibreAbsoluteMass_two_head_le (4*N)
  have hf := (le_abs_self (mobiusDivisorSelectionFibre (4*N) {2} ∅)).trans
    (abs_mobiusDivisorSelectionFibre_le_absoluteMass (4*N) {2} ∅)
  unfold mobiusDivisorCoareaHeadSlope
  nlinarith [Real.sqrt_nonneg (4*N:ℕ)]

/-- After prime two, the coarea head slope grows faster than the linear source scale. -/
theorem tendsto_mobiusDivisorCoareaHeadSlope_two_div_atTop :
    Tendsto (fun N : ℕ => mobiusDivisorCoareaHeadSlope (4*N) {2}/(4*(N:ℝ))) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  have hlarge := tendsto_atTop.mp tendsto_mobiusDivisorLatePrimeMass_div_atTop (b+4)
  filter_upwards [hlarge,eventually_ge_atTop (1:ℕ)] with N hT hN
  have hn : (0:ℝ)<4*N := by positivity
  have hroot : Real.sqrt (4*N:ℕ) ≤ 4*(N:ℝ) := by
    have hs := Real.sqrt_le_self_iff.mpr (Or.inr
      (show (1:ℝ)≤(4*N:ℕ) by exact_mod_cast (show 1≤4*N by omega)))
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hs
  have hg := mobiusDivisorCoareaHeadSlope_two_ge_lateMass N
  have hbound : mobiusDivisorLatePrimeMass (4*N)-4*(4*(N:ℝ)) ≤
      mobiusDivisorCoareaHeadSlope (4*N) {2} := by linarith only [hg,hroot]
  have hd := div_le_div_of_nonneg_right hbound hn.le
  rw [sub_div,mul_div_cancel_right₀ (4:ℝ) hn.ne'] at hd
  linarith only [hT,hd]

end RHTower
