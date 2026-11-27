import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.FirstParticle
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Paired
import GaloisForLFunctions.HTGeometry.ThermodynamicAffinityHolonomy

/-! # Two ranked probabilities as an observable of a finite Gibbs law -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks

open Real _root_.HTGeometry

/-- The runner-up counts different states with equal probabilities as different entries. -/
def second {X : Type*} (P : X → ℝ) := sSup {z | ∃ i j, i ≠ j ∧ min (P i) (P j) = z}

def logOdds {X : Type*} (P : X → ℝ) := log (sSup (Set.range P) / second P)

theorem logOdds_at {X : Type*} (P : X → ℝ) (u v : X) (huv : u ≠ v)
    (hu : ∀ x, P x ≤ P u) (hv : ∀ x, x ≠ u → P x ≤ P v) :
    logOdds P = log (P u / P v) := by
  have h₁ : IsGreatest (Set.range P) (P u) := ⟨⟨u,rfl⟩,fun _ ⟨x,h⟩ => h ▸ hu x⟩
  have h₂ : IsGreatest {z | ∃ i j, i ≠ j ∧ min (P i) (P j) = z} (P v) := by
    refine ⟨⟨u,v,huv,min_eq_right (hu v)⟩,?_⟩
    rintro _ ⟨i,j,hij,rfl⟩
    by_cases hi : i = u
    · subst i; exact (min_le_right _ _).trans (hv j hij.symm)
    · exact (min_le_left _ _).trans (hv i hi)
  rw [logOdds, second, h₁.csSup_eq, h₂.csSup_eq]

/-- Two distinct states sorted first and second by energy. -/
def FirstTwo {X : Type*} (E : X → ℝ) (u v : X) : Prop :=
  u ≠ v ∧ E u ≤ E v ∧ ∀ x, x ≠ u → E v ≤ E x

theorem FirstTwo.lowest {X : Type*} {E : X → ℝ} {u v : X} (h : FirstTwo E u v) (x : X) : E u ≤ E x := by
  by_cases hx : x = u
  · rw [hx]
  · exact h.2.1.trans (h.2.2 x hx)

private theorem gibbs_rank {X : Type*} [Fintype X] (E : X → ℝ) (t : ℝ) (u v : X)
    (h : FirstTwo (fun x => t*E x) u v) :
    logOdds (finiteGibbsStateWeight t E) = t*(E v-E u) := by
  letI : Nonempty X := ⟨u⟩
  have anti {a b : X} (hab : t*E a ≤ t*E b) : finiteGibbsStateWeight t E b ≤ finiteGibbsStateWeight t E a :=
    div_le_div_of_nonneg_right (exp_le_exp.mpr (by linarith only [hab] : -t*E b ≤ -t*E a))
      (finiteGibbsPartition_pos t E).le
  rw [logOdds_at _ u v h.1 (fun x => anti (h.lowest x)) (fun x hx => anti (h.2.2 x hx)),
    GaloisForLFunctions.HTGeometry.finiteGibbsStateWeight_ratio, log_exp]

theorem positive_odds {X : Type*} [Fintype X] {E : X → ℝ} {u v : X} (h : FirstTwo E u v)
    {t : ℝ} (ht : 0 ≤ t) : logOdds (finiteGibbsStateWeight t E) = t*(E v-E u) :=
  gibbs_rank E t u v ⟨h.1,mul_le_mul_of_nonneg_left h.2.1 ht,
    fun x hx => mul_le_mul_of_nonneg_left (h.2.2 x hx) ht⟩

theorem negative_odds {X : Type*} [Fintype X] {E : X → ℝ} {u v : X} (h : FirstTwo (fun x => -E x) u v)
    {t : ℝ} (ht : t ≤ 0) : logOdds (finiteGibbsStateWeight t E) = t*(E v-E u) :=
  gibbs_rank E t u v ⟨h.1,mul_le_mul_of_nonpos_left (neg_le_neg_iff.mp h.2.1) ht,
    fun x hx => mul_le_mul_of_nonpos_left (neg_le_neg_iff.mp (h.2.2 x hx)) ht⟩

/-- The signed difference of log odds is exactly linear through zero, including the completely tied law. -/
theorem odds_contrast {X : Type*} [Fintype X] {E : X → ℝ} {l q u r : X}
    (low : FirstTwo E l q) (high : FirstTwo (fun x => -E x) u r) (t : ℝ) :
    logOdds (finiteGibbsStateWeight t E) - logOdds (finiteGibbsStateWeight (-t) E) =
      t*((E q-E l)-(E u-E r)) := by
  rcases le_total 0 t with h | h
  · rw [positive_odds low h, negative_odds high (neg_nonpos.mpr h)]; ring
  · rw [negative_odds high h, positive_odds low (neg_nonneg.mpr h)]; ring

theorem firstTwo_boson {I : Type*} [Fintype I] [DecidableEq I] (n : ℕ) (e : I → ℝ) (l q : I)
    (hlq : e l < e q) (hrest : ∀ i, i ≠ l → i ≠ q → e q < e i) :
    FirstTwo (read e) (pure (n+1) l) (firstExcitation n l q) := by
  have gap := first_gap n l q e
  have hlt : read e (pure (n+1) l) < read e (firstExcitation n l q) := by linarith only [gap,hlq]
  refine ⟨fun h => hlt.ne (congrArg (read e) h), hlt.le, ?_⟩
  intro x hu
  by_cases hv : x = firstExcitation n l q
  · rw [hv]
  · linarith only [gap, above_first_gap n e l q hlq hrest x hu hv]

/-- Log odds of the actual outgoing probabilities of a fixed-count sector. -/
def measuredOdds (S : Finset Nat.Primes) (c : S → ℕ) (m : ℕ) (s : ℂ) :=
  logOdds (fun x : State c m => outgoingShare s x)

theorem measuredOdds_eq (S : Finset Nat.Primes) (c : S → ℕ) (m : ℕ) (s : ℂ) :
    measuredOdds S c m s = logOdds (finiteGibbsStateWeight (2*s.re-1) (fun x : State c m => energy (level x))) := by
  exact congrArg logOdds (funext (outgoing_gibbs s))

#print axioms logOdds_at
#print axioms odds_contrast
#print axioms firstTwo_boson
#print axioms measuredOdds_eq

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks
