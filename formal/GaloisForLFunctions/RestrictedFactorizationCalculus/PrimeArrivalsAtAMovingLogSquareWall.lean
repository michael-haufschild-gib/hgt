import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePrimeReadingsBeyondTheHyperbola
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimesRoundAnOscillatingDensity

/-!
# Prime arrivals in the variation of signed quotient heads

Each ordinary prime above the final wall enters the increasing head
once. A simultaneous sieve jump can erase at most one such observation.
At unchanged walls changing proper powers costs only their signed action
on the smaller common head.
-/
noncomputable section
open Finset Filter ArithmeticFunction RHTower.CoprimeMobius
open GaloisForLFunctions.BezoutValuationIncidence
open scoped Classical
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev headAt (a : ArithmeticFunction ℝ) (y t : ℕ) :=
  quotientReading (roughFloorCoefficient y a) t

private theorem coefficient_at_an_arriving_prime (y : ℕ) (a : ArithmeticFunction ℝ)
    (unit : a 1=0) {p : ℕ} (pr : p.Prime) :
    roughFloorCoefficient y a p=a p := by
  rw [roughFloorCoefficient,ArithmeticFunction.mul_apply]
  have unitMu : roughMobiusWeight y 1=1 := by
    simp [roughMobiusWeight,roughRestriction_apply,isFree_one]
  rw [sum_eq_single (1,p)]
  · simp [unitMu]
  · rintro ⟨d,q⟩ h diff
    obtain ⟨fac,_⟩ := Nat.mem_divisorsAntidiagonal.mp h
    change d*q=p at fac
    have dvd : q ∣ p := fac ▸ dvd_mul_left q d
    rcases (Nat.dvd_prime pr).mp dvd with one | pval
    · simp [one,unit]
    · subst q
      have d1 : d=1 := Nat.eq_of_mul_eq_mul_right pr.pos (by simpa only [one_mul] using fac : d*p=1*p)
      exact (diff (by simp [d1])).elim
  · intro bad
    exact (bad (Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.one_mul _,pr.ne_zero⟩)).elim

private theorem add_one_coefficient (a : ArithmeticFunction ℝ) (y i : ℕ) :
    headAt a y (i+1)=headAt a y i+roughFloorCoefficient y a (i+1) := by
  unfold headAt quotientReading
  rw [sum_Icc_succ_top (Nat.succ_pos _)]

private theorem shifted_range (g : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range n,g (i+1))=∑ q ∈ Ioc 0 n,g q := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ,sum_Ioc_succ_top (Nat.zero_le _),ih]

/-- The prime mass beyond the last sieve is paid either by path
variation, by a simultaneous sieve jump, or by a genuine weight edit.
The signed price of all proper-power edits uses only a weaker strip. -/
theorem prime_arrivals_force_head_variation {s : ℝ} (strip : RHTower.zetaZeroAbscissa<s)
    (upper : s ≤ 1) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ N : ℕ,∀ Y : ℕ → ℕ,Monotone Y →
      ∀ a : ℕ → ArithmeticFunction ℝ,(∀ i,a i 1=0) →
      (∀ i p,p.Prime → a i p=roughOrdinaryPrimeWeight (Y i) p) →
      ∀ B : ℝ,0 ≤ B → (∀ q,¬q.Prime → (∑ i ∈ range N,|a (i+1) q-a i q|) ≤ B*vonMangoldt q) →
      Chebyshev.theta N-Chebyshev.theta (min (Y N) N) ≤
        (∑ i ∈ range N,|headAt (a (i+1)) (Y (i+1)) (i+1)-headAt (a i) (Y i) i|)+
        ((Y N:ℝ)-Y 0)*Real.log N+K*B*deletionPrice s (Y N)*(N:ℝ)^s := by
  obtain ⟨K,k0,cap⟩ := signed_price_of_all_proper_power_edits strip upper
  refine ⟨K,k0,fun N Y mono a unit ordinary B bp variation => ?_⟩
  let b := fun i => if Y (i+1)=Y i then a (i+1) else a i
  let P := fun i => headAt (a i) (Y i) i
  let D := fun i => |headAt (b i) (Y i) i-headAt (a i) (Y i) i|
  let g := fun p : ℕ => if p.Prime ∧ Y N<p then Real.log p else 0
  have fixed (i p : ℕ) (_ : i<N) (hp : p.Prime) : b i p=a i p := by
    dsimp only [b]
    split
    · rename_i eq
      rw [ordinary _ _ hp,ordinary _ _ hp,eq]
    · rfl
  have changes (q : ℕ) : (∑ i ∈ range N,|b i q-a i q|) ≤ B*vonMangoldt q := by
    by_cases pr : q.Prime
    · apply le_trans _ (mul_nonneg bp vonMangoldt_nonneg)
      exact (sum_eq_zero (fun i hi => by rw [fixed i q (mem_range.mp hi) pr,sub_self,abs_zero])).le
    · apply le_trans _ (variation q pr)
      apply sum_le_sum
      intro i _
      dsimp only [b]
      split
      · exact le_rfl
      · rw [sub_self,abs_zero]; exact abs_nonneg _
  have totalEdits := cap N (Y N) N Y id (fun _ h => mono h.le) (fun _ h => h.le) a b B bp fixed changes
  have step (i : ℕ) (hi : i ∈ range N) : g (i+1) ≤
      |P (i+1)-P i|+((Y (i+1):ℝ)-Y i)*Real.log N+D i := by
    let p := i+1
    have pN : p ≤ N := mem_range.mp hi
    have wall := mono (Nat.le_succ i)
    have z := mul_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr wall)) (Real.log_natCast_nonneg N)
    by_cases marked : p.Prime ∧ Y N<p
    · change (if p.Prime ∧ Y N<p then Real.log p else 0) ≤ _
      rw [if_pos marked]
      by_cases eq : Y (i+1)=Y i
      · have high := (mono pN).trans_lt marked.2
        have primeValue : a (i+1) p=Real.log p := by
          rw [ordinary _ _ marked.1]
          change (if p.Prime ∧ Y (i+1)<p then Real.log p else 0)=_
          exact if_pos ⟨marked.1,high⟩
        have arriving := add_one_coefficient (a (i+1)) (Y (i+1)) i
        rw [coefficient_at_an_arriving_prime _ _ (unit _) marked.1,primeValue,eq] at arriving
        have adj : P (i+1)-P i=(headAt (b i) (Y i) i-headAt (a i) (Y i) i)+Real.log p := by
          change headAt (a (i+1)) (Y (i+1)) (i+1)-headAt (a i) (Y i) i=_
          rw [eq,arriving]; simp only [b,if_pos eq]; ring
        have tri := abs_sub (P (i+1)-P i) (headAt (b i) (Y i) i-headAt (a i) (Y i) i)
        rw [show P (i+1)-P i-(headAt (b i) (Y i) i-headAt (a i) (Y i) i)=Real.log p by rw [adj]; ring,
          abs_of_nonneg (Real.log_natCast_nonneg _)] at tri
        dsimp only [D]
        linarith only [tri,z]
      · have inc : (Y i:ℝ)+1 ≤ Y (i+1) := by exact_mod_cast (show Y i+1 ≤ Y (i+1) from lt_of_le_of_ne wall (Ne.symm eq))
        have log := Real.log_le_log (Nat.cast_pos.mpr (Nat.succ_pos i)) (Nat.cast_le.mpr pN)
        have cost := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ (Y (i+1):ℝ)-Y i by linarith only [inc]) (Real.log_natCast_nonneg N)
        exact log.trans (by linarith only [cost,abs_nonneg (P (i+1)-P i),show 0 ≤ D i from abs_nonneg _])
    · change (if p.Prime ∧ Y N<p then Real.log p else 0) ≤ _
      rw [if_neg marked]
      exact add_nonneg (add_nonneg (abs_nonneg _) z) (abs_nonneg _)
  have summed := sum_le_sum step
  rw [sum_add_distrib,sum_add_distrib,←sum_mul,sum_range_sub] at summed
  have θ : (∑ i ∈ range N,g (i+1))=Chebyshev.theta N-Chebyshev.theta (min (Y N) N) := by
    rw [GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimeEdits.theta_sub_theta (min_le_right ..)]
    rw [shifted_range]
    have split : Ioc (min (Y N) N) N=(Ioc 0 N).filter (Y N<·) := by
      ext p; simp only [mem_Ioc,mem_filter]; omega
    rw [split,sum_filter]
    apply sum_congr rfl
    intro p _
    by_cases pr : p.Prime <;> by_cases high : Y N<p <;> simp [g,pr,high]
  rw [←θ]
  exact summed.trans (by linarith only [totalEdits])

#print axioms prime_arrivals_force_head_variation
end GaloisForLFunctions.RestrictedFactorizationCalculus
