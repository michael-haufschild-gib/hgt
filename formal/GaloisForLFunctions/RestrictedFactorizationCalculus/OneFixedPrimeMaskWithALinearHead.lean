import GaloisForLFunctions.RestrictedFactorizationCalculus.TheCenteredReadingBelowTheHyperbola
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimesRoundAnOscillatingDensity
import GaloisForLFunctions.RHTower.RobinLcmCriterion

/-!
# A fixed prime reading attaining the full head exponent

A single mask of ordinary primes can have an inverse-coefficient head of
linear size cofinally. Successive prime octaves lie above the current
sieve while all previously marked octaves lie below it.
-/

noncomputable section
open Filter Finset ArithmeticFunction RHTower.CoprimeMobius
open scoped Classical Topology
open GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

def markedOrdinaryPrimeWeight (A : Set ℕ) : ArithmeticFunction ℝ :=
  ⟨fun q => if q.Prime ∧ q ∈ A then Real.log q else 0,by simp⟩

theorem marked_weight_dominated (A : Set ℕ) (n : ℕ) :
    |markedOrdinaryPrimeWeight A n| ≤ vonMangoldt n := by
  change |if n.Prime ∧ n ∈ A then Real.log n else 0| ≤ _
  split
  · rename_i h
    rw [vonMangoldt_apply_prime h.1,abs_of_nonneg (Real.log_natCast_nonneg _)]
  · rw [abs_zero]; exact vonMangoldt_nonneg

private theorem one_window_head (y T : ℕ) (A : Set ℕ) (room : y ≤ T/2)
    (window : ∀ q,q ≤ T → y<q → (q ∈ A ↔ T/2<q)) :
    quotientReading (roughFloorCoefficient y (roughRestriction y (markedOrdinaryPrimeWeight A))) T=
      Chebyshev.theta T-Chebyshev.theta (T/2:ℕ) := by
  let a := roughRestriction y (markedOrdinaryPrimeWeight A)
  change quotientReading (roughFloorCoefficient y a) T=_
  rw [coefficient_head_as_quotient_sum,GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimeEdits.theta_sub_theta (Nat.div_le_self ..)]
  have seteq : Ioc (T/2) T=(Icc 1 T).filter (T/2<·) := by
    ext d
    simp only [mem_filter,mem_Icc,mem_Ioc]
    omega
  rw [seteq,sum_filter]
  apply sum_congr rfl
  intro q hq
  have pos := (mem_Icc.mp hq).1
  have atMost := (mem_Icc.mp hq).2
  have value : a q=if q.Prime ∧ T/2<q then Real.log q else 0 := by
    rw [show a=roughRestriction y (markedOrdinaryPrimeWeight A) from rfl,roughRestriction_apply]
    change (if IsFree (RoughReading.banned y) q then (if q.Prime ∧ q ∈ A then Real.log q else 0) else 0)=_
    by_cases pr : q.Prime
    · have free : IsFree (RoughReading.banned y) q ↔ y<q := by
        simpa only [RoughReading.banned,Set.mem_setOf_eq,not_le] using isFree_prime (RoughReading.banned y) pr
      by_cases high : y<q
      · simp [free,pr,high,window q atMost high]
      · have cheap := (not_lt.mp high).trans room
        simp [free,pr,high,cheap.not_gt]
    · simp [pr]
  rw [value]
  by_cases high : T/2<q
  · have divone : T/q=1 := by
      apply le_antisymm
      · apply Nat.le_of_lt_succ
        apply (Nat.div_lt_iff_lt_mul pos).mpr
        omega
      · apply (Nat.le_div_iff_mul_le pos).mpr
        simpa using atMost
    simp [high,divone,coprimeMoebiusSum,coprimeMoebiusIndicator]
  · simp [high]

/-- For every diverging sieve below half the head, one fixed prime
selection isolates the highest prime octave on an infinite sequence. -/
theorem one_prime_mask_with_exact_octave_heads (Y T : ℕ → ℕ) (top : Tendsto Y atTop atTop)
    (space : ∀ᶠ X : ℕ in atTop,Y X<T X/2) :
    ∃ (A : Set ℕ) (x : ℕ → ℕ),StrictMono x ∧ StrictMono (fun j => T (x j)) ∧
      ∀ j,quotientReading (roughFloorCoefficient (Y (x j))
        (roughRestriction (Y (x j)) (markedOrdinaryPrimeWeight A))) (T (x j))=
        Chebyshev.theta (T (x j))-Chebyshev.theta (T (x j)/2:ℕ) := by
  have choose (k : ℕ) : ∃ n,k<n ∧ T k ≤ Y n ∧ Y n<T n/2 :=
    ((eventually_gt_atTop k).and ((top.eventually_ge_atTop (T k)).and space)).exists
  choose next step using choose
  let x : ℕ → ℕ := Nat.rec (next 0) (fun _ k => next k)
  have seq (j : ℕ) : x (j+1)=next (x j) := rfl
  have strict : StrictMono x := strictMono_nat_of_lt_succ (fun j => (step (x j)).1)
  let t := fun j => T (x j)
  let y := fun j => Y (x j)
  have gap (j : ℕ) : t j ≤ y (j+1) := (step (x j)).2.1
  have low (j : ℕ) : y j<t j/2 := by
    cases j with
    | zero => exact (step 0).2.2
    | succ j => exact (step (x j)).2.2
  have tr : StrictMono t := strictMono_nat_of_lt_succ (fun j =>
    ((gap j).trans_lt (low (j+1))).trans_le (Nat.div_le_self ..))
  let A : Set ℕ := {q | ∃ j,t j/2<q ∧ q ≤ t j}
  refine ⟨A,x,strict,tr,fun j => one_window_head (y j) (t j) A (low j).le ?_⟩
  intro q qt qy
  constructor
  · rintro ⟨k,above,below⟩
    rcases lt_trichotomy k j with earlier | rfl | later
    · obtain ⟨h,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
      exact (qy.not_ge (below.trans ((tr.monotone (Nat.le_of_lt_succ earlier)).trans (gap h)))).elim
    · exact above
    · obtain ⟨h,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
      exact (above.not_ge (qt.trans ((tr.monotone (Nat.le_of_lt_succ later)).trans ((gap h).trans (low (h+1)).le)))).elim
  · exact fun high => ⟨j,high,qt⟩

private theorem terminal_octave_limit :
    Tendsto (fun n : ℕ => (Chebyshev.theta n-Chebyshev.theta (n/2:ℕ))/(n:ℝ)) atTop (𝓝 (1/2)) := by
  have top : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have halfTop : Tendsto (fun n : ℕ => n/2) atTop atTop := tendsto_atTop.mpr
    (fun k => (eventually_ge_atTop (2*k)).mono (fun n h => by omega))
  have inv := tendsto_inv_atTop_zero.comp top
  have ratio : Tendsto (fun n : ℕ => ((n/2:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 (1/2)) := by
    have lower := (tendsto_const_nhds (x := (1/2:ℝ))).sub inv
    rw [sub_zero] at lower
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lower tendsto_const_nhds
    all_goals
      filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
      have np : 0<(n:ℝ) := Nat.cast_pos.mpr hn
      have lo : (n:ℝ) ≤ 2*((n/2:ℕ):ℝ)+1 := by exact_mod_cast (show n ≤ 2*(n/2)+1 by omega)
      have hi : 2*((n/2:ℕ):ℝ) ≤ n := by exact_mod_cast (show 2*(n/2) ≤ n by omega)
    · apply (le_div_iff₀ np).mpr
      change (1/2-(n:ℝ)⁻¹)*(n:ℝ) ≤ _
      rw [sub_mul,inv_mul_cancel₀ np.ne']; linarith only [lo]
    · exact (div_le_iff₀ np).mpr (by linarith only [hi])
  have main := RHTower.tendsto_theta_div_self.comp top
  have dif := main.sub ((main.comp halfTop).mul ratio)
  rw [one_mul,show (1:ℝ)-1/2=1/2 by norm_num] at dif
  apply dif.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
  let h := n/2
  have hp : (0:ℝ)<(h:ℝ) := Nat.cast_pos.mpr (show 0<n/2 by omega)
  change Chebyshev.theta n/(n:ℝ)-Chebyshev.theta h/(h:ℝ)*((h:ℝ)/(n:ℝ))=_
  field_simp [hp.ne']; ring

/-- One fixed ordinary-prime mask has normalized signed head tending
to one half along a cofinal sequence. No sublinear head budget can
hold for every fixed prime selection at these cutoffs. -/
theorem one_fixed_prime_mask_with_linear_head (Y T : ℕ → ℕ) (top : Tendsto Y atTop atTop)
    (space : ∀ᶠ X : ℕ in atTop,Y X<T X/2) :
    ∃ (A : Set ℕ) (x : ℕ → ℕ),StrictMono x ∧
      Tendsto (fun j => quotientReading (roughFloorCoefficient (Y (x j))
        (roughRestriction (Y (x j)) (markedOrdinaryPrimeWeight A))) (T (x j))/(T (x j):ℝ)) atTop (𝓝 (1/2)) := by
  obtain ⟨A,x,hx,ht,heads⟩ := one_prime_mask_with_exact_octave_heads Y T top space
  refine ⟨A,x,hx,(terminal_octave_limit.comp ht.tendsto_atTop).congr (fun j => ?_)⟩
  simp only [Function.comp_apply,heads]

#print axioms one_prime_mask_with_exact_octave_heads
#print axioms one_fixed_prime_mask_with_linear_head
end GaloisForLFunctions.RestrictedFactorizationCalculus
