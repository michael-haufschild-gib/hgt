import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Ranks.Observable

/-! # The first squarefree excitation exchanges one occupied and one empty mode -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks.Squarefree

open Finset

variable {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ}

abbrev Sector (I : Type*) [Fintype I] (m : ℕ) := State (fun _ : I => 1) m

def occupied (x : Sector I m) := univ.filter fun i => count x i = 1

theorem count_occupied (x : Sector I m) (i : I) : count x i = if i ∈ occupied x then 1 else 0 := by
  have hc : count x i ≤ 1 := count_cap x i
  simp only [occupied,mem_filter,mem_univ,true_and]
  split <;> omega

theorem card_occupied (x : Sector I m) : (occupied x).card = m := by
  apply Eq.trans _ (count_sum x)
  simp_rw [count_occupied x]
  simp

def fill (T : Finset I) (hT : T.card = m) : Sector I m :=
  ⟨fun i => ⟨if i ∈ T then 1 else 0, by
      change (if i ∈ T then 1 else 0) < 2
      split <;> omega⟩, by
    change (∑ i, if i ∈ T then 1 else 0) = m
    simpa [sum_boole] using hT⟩

theorem occupied_fill (T : Finset I) (hT : T.card = m) : occupied (fill T hT) = T := by
  ext i
  simp only [occupied,mem_filter,mem_univ,true_and]
  change (if i ∈ T then 1 else 0 : ℕ) = 1 ↔ _
  by_cases h : i ∈ T <;> simp [h]

theorem occupied_injective : Function.Injective (occupied (I := I) (m := m)) := by
  intro x y h
  exact state_ext fun i => by rw [count_occupied x,count_occupied y,h]

def cost (e : I → ℝ) (x : Sector I m) := ∑ i ∈ occupied x, e i

theorem cost_fill (e : I → ℝ) (T : Finset I) (hT : T.card = m) :
    cost e (fill T hT) = ∑ i ∈ T, e i := by rw [cost,occupied_fill]

omit [Fintype I] in
/-- An exchange of d particles costs at least d times the gap across the filling boundary. -/
private theorem exchange_bound (e : I → ℝ) (T U : Finset I) (hc : U.card = T.card)
    (a b : ℝ) (hin : ∀ i ∈ T, e i ≤ a) (hout : ∀ i ∉ T, b ≤ e i) :
    ((U \ T).card : ℝ)*(b-a) ≤ (∑ i ∈ U, e i)-(∑ i ∈ T, e i) := by
  let C := T ∩ U
  have tu : T \ C = T \ U := by ext i; simp [C]
  have ut : U \ C = U \ T := by ext i; simp [C]
  have st := sum_sdiff (f := e) (show C ⊆ T from inter_subset_left)
  have su := sum_sdiff (f := e) (show C ⊆ U from inter_subset_right)
  rw [tu] at st
  rw [ut] at su
  have added := sum_le_sum (s := U \ T) (fun i hi => hout i (mem_sdiff.mp hi).2)
  have lost := sum_le_sum (s := T \ U) (fun i hi => hin i (mem_sdiff.mp hi).1)
  simp only [sum_const,nsmul_eq_mul,← card_sdiff_comm hc] at lost
  simp only [sum_const,nsmul_eq_mul] at added
  rw [mul_sub]
  linarith only [st,su,added,lost]

/-- Filling a lower set and exchanging its last mode for the first available mode
give the two lowest energies at fixed particle number. -/
theorem first_exchange (e : I → ℝ) (T : Finset I) (hT : T.card = m) (p q : I)
    (hp : p ∈ T) (hq : q ∉ T) (hlt : e p < e q)
    (hin : ∀ i ∈ T, e i ≤ e p) (hout : ∀ i ∉ T, e q ≤ e i) :
    ∃ u v : Sector I m, FirstTwo (cost e) u v ∧ cost e v-cost e u = e q-e p := by
  let V := insert q (T.erase p)
  have hvq : q ∉ T.erase p := fun h => hq (mem_of_mem_erase h)
  have hv : V.card = m := by
    rw [show V = insert q (T.erase p) from rfl,card_insert_of_notMem hvq,card_erase_of_mem hp,← hT]
    have := card_pos.mpr ⟨p,hp⟩
    omega
  have delta : cost e (fill V hv)-cost e (fill T hT) = e q-e p := by
    rw [cost_fill,cost_fill,show V = insert q (T.erase p) from rfl,sum_insert hvq]
    linarith only [sum_erase_add T e hp]
  have inc : cost e (fill T hT) < cost e (fill V hv) := by linarith only [delta,hlt]
  refine ⟨fill T hT,fill V hv,⟨fun he => inc.ne (congrArg (cost e) he),inc.le,?_⟩,delta⟩
  intro x hx
  have hc := (card_occupied x).trans hT.symm
  have hne : occupied x ≠ T := fun h => hx (occupied_injective (h.trans (occupied_fill T hT).symm))
  have hpos : 0 < ((occupied x) \ T).card := card_pos.mpr
    (sdiff_nonempty.mpr fun hs => hne (eq_of_subset_of_card_le hs hc.ge))
  have h₁ : (1:ℝ) ≤ (((occupied x) \ T).card : ℝ) := by exact_mod_cast hpos
  have bound := exchange_bound e T (occupied x) hc _ _ hin hout
  have gap := mul_le_mul_of_nonneg_right h₁ (sub_nonneg.mpr hlt.le)
  rw [cost_fill] at delta
  change cost e (fill V hv) ≤ ∑ i ∈ occupied x, e i
  rw [cost_fill]
  linarith only [delta,bound,gap,cost_fill e T hT]

/-- Squarefree shell energy is the sum of the logarithms of its occupied primes. -/
theorem prime_cost {S : Finset Nat.Primes} (x : Sector S m) : energy (level x) = cost primeEnergy x := by
  let y : Boson S m := ⟨fun i => ⟨count x i, Nat.lt_succ_of_le
      ((count_interval x i).2.trans (show min m 1 ≤ m from min_le_left _ _))⟩,count_sum x⟩
  rw [show level x = level y from rfl,energy_eq_read]
  change (∑ i, (count x i : ℝ)*primeEnergy i) = _
  simp_rw [count_occupied x]
  simp only [apply_ite Nat.cast,Nat.cast_zero,Nat.cast_one,ite_mul,one_mul,zero_mul,
    sum_ite_mem,univ_inter,cost]

#print axioms first_exchange
#print axioms prime_cost

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks.Squarefree
