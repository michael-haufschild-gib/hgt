import GaloisForLFunctions.RHTower.MobiusDivisorPrescribedClockBlock
import GaloisForLFunctions.RHTower.WoldBooleanAcceleratedType

/-!
# Source depth required to repay an inherited clock debt

Every nonempty even processed prime core has arbitrarily distant omitted
primes with positive logarithmic clock debt. The debt persists when the
repayment cutoff advances arbitrarily from the current cutoff.

The preserved-sample law bounds the payment obtainable from all helper
primes with a given child-quotient ceiling. Prime density then forces that
ceiling to grow at least logarithmically. Removing redundant helpers gives
an actual fresh prime with the required depth, uniformly over adaptive
helper sets, their cardinalities, and all later repayment cutoffs.

This is a source obstruction to bounded-quotient repayment. It neither
constructs an exhaustive schedule nor bounds the completed critical action.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private lemma eventually_prime_clock_count :
    ∀ᶠ M : ℕ in atTop,
      (1+(Nat.primeCounting M:ℝ))*Real.log M ≤ 2*(M:ℝ) := by
  have hlog : Tendsto (fun M : ℕ => Real.log (M:ℝ)/(M:ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun M : ℕ =>
      (1+(Nat.primeCounting M:ℝ))*Real.log M/(M:ℝ)) atTop (𝓝 1) := by
    have hh := hlog.add tendsto_primeCounting_nat_ratio
    simp only [zero_add] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (2:ℕ)] with M hM
    have hm : (1:ℝ)<M := by exact_mod_cast (show 1<M by omega)
    have hl := (Real.log_pos hm).ne'
    field_simp
  filter_upwards [ht.eventually (eventually_lt_nhds (show (1:ℝ)<2 by norm_num)),
    eventually_ge_atTop (1:ℕ)] with M h hM
  exact ((div_lt_iff₀ (show (0:ℝ)<M by exact_mod_cast hM)).mp h).le

private lemma current_clock_debt (P : Finset ℕ) (hP : P.Nonempty)
    (hprime : ∀p∈P,p.Prime) (heven : Even P.card) (B : ℕ) :
    ∃ r : ℕ, r.Prime ∧ B<r ∧ r∉P ∧
      (∑' n,mobiusDivisorFixedCoreBlockMass P n) <
        ∑' n,mobiusDivisorFixedCoreBlockMass (insert r P) n := by
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.mp
    (eventually_mobiusDivisorPrimeReleaseCoefficient_oriented_pos P hP hprime)
  obtain ⟨r,hrge,hr⟩ := Nat.exists_infinite_primes (T+B+P.sup id+1)
  have hrP : r∉P := by
    intro h
    have hh : r≤P.sup id := Finset.le_sup (f:=id) h
    omega
  have hs := hT r (by omega) hr hrP
  rw [pow_succ,heven.neg_one_pow] at hs
  refine ⟨r,hr,by omega,hrP,?_⟩
  linarith


/-- Over every nonempty even prime core there are arbitrarily distant omitted
primes whose debt persists from the current clock to every later cutoff.
Any net repayment at that later cutoff requires logarithmic child depth,
uniformly over all adaptive helper sets and changing quotient thresholds. -/
theorem exists_mobiusDivisorAdvancingClockDebt_log_depth
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀p∈P,p.Prime)
    (heven : Even P.card) (B : ℕ) :
    ∃ r : ℕ, r.Prime ∧ B<r ∧ r∉P ∧ ∃ δ η : ℝ, 0<δ ∧ 0<η ∧
      ∀ᶠ M : ℕ in atTop, ∀ L : ℕ, M≤L →
        δ*(1+Real.log L) ≤
          mobiusDivisorFiniteClockEnergy 1 L (insert r P)/(L:ℝ)^2-
            mobiusDivisorFiniteClockEnergy 1 M P/(M:ℝ)^2 ∧
        ∀ (S : Finset ℕ) (K : ℕ),
          (∀q∈S,q.Prime ∧ L/q≤K) →
          mobiusDivisorFiniteClockEnergy 1 L ((insert r P)∪S)/(L:ℝ)^2 ≤
            mobiusDivisorFiniteClockEnergy 1 M P/(M:ℝ)^2 →
          η*Real.log L ≤ (K:ℝ) := by
  obtain ⟨r,hr,hrB,hrP,hgap⟩ := current_clock_debt P hP hprime heven B
  let Q := insert r P
  have hQ : ∀q∈Q,q.Prime := by simpa [Q] using And.intro hr hprime
  let a := ∑' n,mobiusDivisorFixedCoreBlockMass P n
  let b := ∑' n,mobiusDivisorFixedCoreBlockMass Q n
  have ha : 0≤a := tsum_nonneg (mobiusDivisorFixedCoreBlockMass_nonneg P hprime)
  have hg : 0<b-a := sub_pos.mpr hgap
  let δ := (b-a)/4
  let C : ℝ := ((3/5:ℝ)*2^(Q.card-1))^2
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hC : 0<C := by dsimp [C]; positivity
  let η := δ/(2*C)
  have hη : 0<η := by dsimp [η]; positivity
  have hupper := (tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log P hprime).eventually
    (eventually_lt_nhds (show a<a+δ by linarith))
  have hlower := (tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log Q hQ).eventually
    (eventually_gt_nhds (show b-δ<b by linarith))
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp
    (hupper.and (hlower.and (eventually_prime_clock_count.and (eventually_ge_atTop (2:ℕ)))))
  refine ⟨r,hr,hrB,hrP,δ,η,hδ,hη,Filter.eventually_atTop.mpr ⟨N,?_⟩⟩
  intro M hNM L hML
  have hM := hN M hNM
  have hL := hN L (hNM.trans hML)
  have hMp : (0:ℝ)<M := by exact_mod_cast (show 0<M by have := hM.2.2.2; omega)
  have hLp : (0:ℝ)<L := by exact_mod_cast (show 0<L by have := hL.2.2.2; omega)
  have hlogM : 0≤Real.log (M:ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1≤M by have := hM.2.2.2; omega))
  have hlogL : 0≤Real.log (L:ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1≤L by have := hL.2.2.2; omega))
  have huM : 0<1+Real.log (M:ℝ) := by linarith
  have huL : 0<1+Real.log (L:ℝ) := by linarith
  have hUP : mobiusDivisorFiniteClockEnergy 1 M P/(M:ℝ)^2 < (a+δ)*(1+Real.log M) := by
    apply (div_lt_iff₀ huM).mp
    simpa only [div_div] using hM.1
  have hLO : (b-δ)*(1+Real.log L) < mobiusDivisorFiniteClockEnergy 1 L Q/(L:ℝ)^2 := by
    apply (lt_div_iff₀ huL).mp
    simpa only [div_div] using hL.2.1
  have hmono : (a+δ)*(1+Real.log M) ≤ (a+δ)*(1+Real.log L) :=
    mul_le_mul_of_nonneg_left
      (by have := Real.log_le_log hMp (show (M:ℝ)≤L by exact_mod_cast hML); linarith)
      (by linarith)
  have hcoeff : a+δ+δ ≤ b-δ := by dsimp [δ]; linarith only [hg]
  have hprod := mul_le_mul_of_nonneg_right hcoeff huL.le
  have hd : δ*(1+Real.log L) ≤ mobiusDivisorFiniteClockEnergy 1 L Q/(L:ℝ)^2-
      mobiusDivisorFiniteClockEnergy 1 M P/(M:ℝ)^2 := by
    nlinarith only [hUP,hLO,hmono,hprod]
  refine ⟨hd,?_⟩
  intro S K hS hpaid
  have hcap := mobiusDivisorFiniteClockEnergy_current_quotient_payment_le Q hQ L K
    (by have := hL.2.2.2; omega) S hS
  change _ ≤ C*L*(1+Real.log L)*(K:ℝ)*(1+Nat.primeCounting L) at hcap
  have hx : δ*(1+Real.log L) ≤
      (mobiusDivisorFiniteClockEnergy 1 L Q-mobiusDivisorFiniteClockEnergy 1 L (Q∪S))/(L:ℝ)^2 := by
    rw [sub_div]
    linarith only [hd,hpaid]
  have hfinite := (le_div_iff₀ (sq_pos_of_pos hLp)).mp hx
  have hmain : δ*(L:ℝ) ≤ C*(K:ℝ)*(1+Nat.primeCounting L) := by
    apply (mul_le_mul_iff_left₀ (mul_pos hLp huL)).mp
    nlinarith only [hfinite,hcap]
  have hl := mul_le_mul_of_nonneg_right hmain hlogL
  have hc := mul_le_mul_of_nonneg_left hL.2.2.1
    (mul_nonneg hC.le (Nat.cast_nonneg (α:=ℝ) K))
  have hdiv : δ*Real.log L ≤ 2*C*(K:ℝ) := by
    apply (mul_le_mul_iff_left₀ hLp).mp
    nlinarith only [hl,hc]
  dsimp [η]
  have heq : δ/(2*C)*Real.log L=(δ*Real.log L)/(2*C) := by ring
  rw [heq]
  exact (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hC)).mpr (by nlinarith only [hdiv])

/-- Every adaptive net repayment, at the current or any later clock, uses a
fresh source prime outside the inherited core and prescribed insertion whose
actual child quotient is at least a fixed multiple of the logarithmic clock. -/
theorem exists_mobiusDivisorAdvancingClockDebt_requires_deep_prime
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀p∈P,p.Prime)
    (heven : Even P.card) (B : ℕ) :
    ∃ r : ℕ, r.Prime ∧ B<r ∧ r∉P ∧ ∃ η : ℝ, 0<η ∧
      ∀ᶠ M : ℕ in atTop, ∀ L : ℕ, M≤L → ∀ S : Finset ℕ,
        (∀q∈S,q.Prime) →
        mobiusDivisorFiniteClockEnergy 1 L ((insert r P)∪S)/(L:ℝ)^2 ≤
          mobiusDivisorFiniteClockEnergy 1 M P/(M:ℝ)^2 →
        ∃ q∈S, q∉insert r P ∧ η*Real.log L ≤ (L/q:ℕ) := by
  obtain ⟨r,hr,hrB,hrP,δ,η,hδ,hη,hall⟩ :=
    exists_mobiusDivisorAdvancingClockDebt_log_depth P hP hprime heven B
  refine ⟨r,hr,hrB,hrP,η,hη,?_⟩
  filter_upwards [hall,eventually_ge_atTop (2:ℕ)] with M hM hM2
  intro L hML S hS hpaid
  let A := S\insert r P
  let K := A.sup (fun q => L/q)
  have heq : (insert r P)∪A=(insert r P)∪S := by
    ext q
    dsimp only [A]
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto
  have hA : ∀q∈A,q.Prime ∧ L/q≤K := by
    intro q hq
    exact ⟨hS q (mem_sdiff.mp hq).1,Finset.le_sup (f:=fun q => L/q) hq⟩
  have hK := (hM L hML).2 A K hA (by simpa only [heq] using hpaid)
  have hpositive : 0<η*Real.log (L:ℝ) := mul_pos hη (Real.log_pos (by
    exact_mod_cast (show 1<L by omega)))
  have hne : A.Nonempty := by
    by_contra hn
    have hzero : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have : K=0 := by simp [K,hzero]
    rw [this,Nat.cast_zero] at hK
    exact (not_le_of_gt hpositive) hK
  obtain ⟨q,hq,hqK⟩ := Finset.exists_mem_eq_sup A hne (fun q => L/q)
  refine ⟨q,(mem_sdiff.mp hq).1,(mem_sdiff.mp hq).2,?_⟩
  change A.sup (fun q => L/q)=L/q at hqK
  change η*Real.log L≤((A.sup (fun q : ℕ => L/q):ℕ):ℝ) at hK
  simpa only [hqK] using hK


end RHTower
