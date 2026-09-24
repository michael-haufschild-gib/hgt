import GaloisForLFunctions.RHTower.MobiusDivisorShellAnchorDebt

/-!
# Cardinality barrier for moving old-core compensation

Every old processed prime can at most double the global square-root head
amplitude. On a fresh dyadic shell, the child arguments stay below two,
so all old-prime corrections vanish there and the shell's negative
one-prime mass is unchanged. Consequently a moving old core with
`480 * 2^card(Q) ≤ card(shell)` cannot pay the physical inverse-cube debt.
This is a necessary lower bound on compensation complexity, not a schedule.
-/

noncomputable section
open Finset Set Filter Topology MeasureTheory
namespace RHTower

theorem anchor_head_card_bound (Q : Finset ℕ) (hQ : ∀q∈Q,q.Prime) (x : ℝ) :
    |mobiusDivisorContinuousHead Q x| ≤
      ((3/5:ℝ)*2^Q.card)*Real.sqrt x := by
  induction Q using Finset.induction_on generalizing x with
  | empty =>
    simpa [mobiusDivisorContinuousHead,
      abs_of_nonneg (divisorContinuousUnitHead_nonneg x)] using
      divisorContinuousUnitHead_le_sqrt x
  | @insert p P hpP ih =>
    have hp : p.Prime := hQ p (mem_insert_self p P)
    have hP : ∀q∈P,q.Prime := fun q hq => hQ q (mem_insert_of_mem hq)
    by_cases hx : x ≤ 0
    · rw [mobiusDivisorContinuousHead_eq_zero (insert p P) (by linarith)]
      simp [Real.sqrt_eq_zero_of_nonpos hx]
    have hx0 : 0 ≤ x := (lt_of_not_ge hx).le
    have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
    have hroot : Real.sqrt p*Real.sqrt (x/p)=Real.sqrt x := by
      rw [Real.sqrt_div hx0]
      field_simp [(Real.sqrt_pos.mpr hp0).ne']
    have ha := ih hP x
    have hb := ih hP (x/p)
    rw [mobiusDivisorContinuousHead_insert P hP hp hpP]
    calc
      |mobiusDivisorContinuousHead P x-
          Real.sqrt p*mobiusDivisorContinuousHead P (x/p)| ≤
        |mobiusDivisorContinuousHead P x|+
          Real.sqrt p*|mobiusDivisorContinuousHead P (x/p)| := by
          simpa [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)] using
            (abs_sub (mobiusDivisorContinuousHead P x)
              (Real.sqrt p*mobiusDivisorContinuousHead P (x/p)))
      _ ≤ ((3/5:ℝ)*2^P.card)*Real.sqrt x +
          Real.sqrt p*(((3/5:ℝ)*2^P.card)*Real.sqrt (x/p)) := by
            exact add_le_add ha (mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _))
      _ = ((3/5:ℝ)*2^(insert p P).card)*Real.sqrt x := by
            rw [card_insert_of_notMem hpP,pow_succ,← hroot]
            ring

private theorem anchor_head_unit_below_two (Q : Finset ℕ)
    (hQ : ∀q∈Q,q.Prime) {y : ℝ} (hy : y ≤ 2) :
    mobiusDivisorContinuousHead Q y = divisorContinuousUnitHead y := by
  induction Q using Finset.induction_on generalizing y with
  | empty => simp [mobiusDivisorContinuousHead]
  | @insert p P hpP ih =>
    have hp : p.Prime := hQ p (mem_insert_self p P)
    have hP : ∀q∈P,q.Prime := fun q hq => hQ q (mem_insert_of_mem hq)
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    rw [mobiusDivisorContinuousHead_insert P hP hp hpP]
    rw [mobiusDivisorContinuousHead_eq_zero P
      ((div_le_one (by exact_mod_cast hp.pos)).mpr (by linarith))]
    simpa using ih hP hy

/-- A moving old core with fewer than logarithmically many primes cannot
    cancel a dense dyadic shell at the physical head scale. -/
theorem shell_head_card_barrier (Q : Finset ℕ) (hQ : ∀q∈Q,q.Prime)
    (N : ℕ) (hN : 1 ≤ N)
    (hdis : Disjoint Q (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)))
    {x : ℝ} (hxl : (7/2:ℝ)*N ≤ x) (hxu : x ≤ (15/4:ℝ)*N) :
    mobiusDivisorContinuousHead
      (Q ∪ GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) x ≤
    (2*((3/5:ℝ)*2^Q.card)-
      ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)/200)*
        Real.sqrt N := by
  let P := GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)
  have hprime : ∀p∈P,p.Prime := fun p hp =>
    (GaloisForLFunctions.HTGeometry.mem_primesInIoc hp).1
  have hpair : ∀p∈P,∀r∈P,x ≤ (p:ℝ)*r := by
    intro p hp r hr
    have hpl := (GaloisForLFunctions.HTGeometry.mem_primesInIoc hp).2.1
    have hrl := (GaloisForLFunctions.HTGeometry.mem_primesInIoc hr).2.1
    have hp2 : (2:ℝ)*N ≤ p := by exact_mod_cast hpl.le
    have hr2 : (2:ℝ)*N ≤ r := by exact_mod_cast hrl.le
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
    have hm := mul_le_mul hp2 hr2 (by positivity) (by positivity)
    nlinarith only [hm,hxu,hN1]
  have hunit : ∀p∈P,mobiusDivisorContinuousHead Q (x/p) =
      divisorContinuousUnitHead (x/p) := by
    intro p hp
    have hp0 : (0:ℝ)<p := by exact_mod_cast (hprime p hp).pos
    have hpl := (GaloisForLFunctions.HTGeometry.mem_primesInIoc hp).2.1
    have hplR : (2:ℝ)*N < p := by exact_mod_cast hpl
    exact anchor_head_unit_below_two Q hQ
      ((div_le_iff₀ hp0).mpr (by linarith))
  have hsum : (P.card:ℝ)*Real.sqrt N/200 ≤
      ∑p∈P,Real.sqrt p*mobiusDivisorContinuousHead Q (x/p) := by
    calc
      _ = ∑_p∈P,Real.sqrt N/200 := by
        simp only [sum_const,nsmul_eq_mul]
        ring
      _ ≤ _ := sum_le_sum (fun p hp => by
        rw [hunit p hp]
        exact anchor_shell_term_floor hN hp hxl hxu)
  have hx0 : 0 ≤ x := by
    have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    linarith
  have hroot : Real.sqrt x ≤ 2*Real.sqrt N := by
    have hxSq := Real.sq_sqrt hx0
    have hNSq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    nlinarith [Real.sqrt_nonneg x,Real.sqrt_nonneg (N:ℝ)]
  have hC : 0 ≤ (3/5:ℝ)*2^Q.card := by positivity
  have hCroot := mul_le_mul_of_nonneg_left hroot hC
  have hbase := (le_abs_self (mobiusDivisorContinuousHead Q x)).trans
    (anchor_head_card_bound Q hQ x)
  have heq := head_shell_over_base Q P hQ hprime hdis hpair
  rw [heq]
  dsimp only [P] at hsum ⊢
  nlinarith only [hsum,hbase,hCroot]

theorem shell_dilationMean_card_barrier (Q : Finset ℕ) (hQ : ∀q∈Q,q.Prime)
    (N : ℕ) (hN : 1 ≤ N)
    (hdis : Disjoint Q (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)))
    (hcard : 480*2^Q.card ≤
      ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)) :
    ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)^2 /
      (40960000*(N:ℝ)) ≤
    mobiusDivisorDilationMean
      (Q ∪ GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) 1 := by
  apply anchor_shell_mean_lower_of_head Q N hN
  intro x hxl hxu
  have h := shell_head_card_barrier Q hQ N hN hdis hxl hxu
  have hs : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  nlinarith only [h,hcard,hs,mul_nonneg
    (show (0:ℝ) ≤
      ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)-
      480*2^Q.card by linarith) hs]

end RHTower
