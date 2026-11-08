import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.PrimeStarCompensation
import GaloisForLFunctions.RHTower.Sieve.PrimeLogPowerTail

/-!
# The sharp logarithmic prime-star compensation boundary

The original tame prime diagonal augmented by `(log p)^α` admits finite
central compensation precisely for `α>2`. Prime-density summability gives
sufficiency; the logarithmic-square obstruction gives necessity. The exact
least payment realizes the positive completion, while every smaller exponent
has explicit finite negative probes for every central budget.
-/

noncomputable section
open Filter
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open ArithmeticIntersectionTheory RenormalizedArithmeticPotentialTheory

/-- A logarithmic diagonal correction of the original tame prime diagonal. -/
def primeStarLogDiagonal (α : ℝ) (p : Nat.Primes) : ℝ :=
  tameDifferent p+(Real.log p)^α

theorem primeStarLogDiagonal_pos (α : ℝ) (p : Nat.Primes) :
    0 < primeStarLogDiagonal α p :=
  add_pos_of_nonneg_of_pos (tameDifferent_nonneg _)
    (Real.rpow_pos_of_pos (Real.log_pos (by exact_mod_cast p.property.one_lt)) _)

/-- Every logarithmic exponent above two gives summable central compensation. -/
theorem summable_primeStar_log_payment (α : ℝ) (hα : 2 < α) :
    Summable (fun p=>(primeStarCoupling p)^2/primeStarLogDiagonal α p) := by
  have hs:=RHTower.Sieve.summable_primes_one_div_mul_log_rpow (by linarith : 0 < α-2)
  apply hs.of_nonneg_of_le
  · intro p
    exact div_nonneg (sq_nonneg _) (primeStarLogDiagonal_pos α p).le
  · intro p
    have hp : (0:ℝ)<p := by exact_mod_cast p.property.pos
    have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast p.property.one_lt)
    have he : (Real.log p)^α=(Real.log p)^2*(Real.log p)^(α-2) := by
      calc (Real.log p)^α=(Real.log p)^((2:ℝ)+(α-2)) := by congr 1; ring
           _ = _ := by rw [Real.rpow_add hl]; norm_num
    rw [primeStar_payment_density]
    calc (Real.log p)^2/((p:ℝ)*primeStarLogDiagonal α p) ≤
          (Real.log p)^2/((p:ℝ)*(Real.log p)^α) :=
        div_le_div_of_nonneg_left (sq_nonneg _)
          (mul_pos hp (Real.rpow_pos_of_pos hl _))
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (tameDifferent_nonneg _)) hp.le)
         _ = 1/((p:ℝ)*(Real.log p)^(α-2)) := by
          rw [he]
          field_simp [hp.ne',hl.ne',(Real.rpow_pos_of_pos hl (α-2)).ne']

/-- At or below logarithmic exponent two, the exact prime-star payment diverges. -/
theorem not_summable_primeStar_log_payment (α : ℝ) (hα : α≤2) :
    ¬Summable (fun p=>(primeStarCoupling p)^2/primeStarLogDiagonal α p) := by
  apply not_summable_primeStar_of_log_square_bound _ (primeStarLogDiagonal_pos α) 2
  have hpco : Tendsto (fun p : Nat.Primes=>(p:ℕ)) cofinite atTop := by
    rw [←Nat.cofinite_eq_atTop]
    exact (Subtype.val_injective : Function.Injective (fun p : Nat.Primes=>(p:ℕ))).tendsto_cofinite
  have hl:=Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hpco)
  filter_upwards [hl.eventually_ge_atTop 1] with p hp1
  simp only [Function.comp_apply] at hp1
  have hr : (Real.log p)^α≤(Real.log p)^2 := by
    have h:=Real.rpow_le_rpow_of_exponent_le hp1 hα
    norm_num at h ⊢
    exact h
  have hd:=tameDifferent_le_log p.property.pos
  dsimp only [primeStarLogDiagonal]
  nlinarith only [hr,hd,hp1,sq_nonneg (Real.log p-1)]

/-- The sharp logarithmic compensation boundary is exponent two. -/
theorem primeStar_log_payment_summable_iff (α : ℝ) :
    Summable (fun p=>(primeStarCoupling p)^2/primeStarLogDiagonal α p) ↔ 2 < α := by
  constructor
  · intro hs
    by_contra h
    exact not_summable_primeStar_log_payment α (le_of_not_gt h) hs
  · exact summable_primeStar_log_payment α

/-- Finite positive completion for logarithmic leaf growth exists exactly above exponent two. -/
theorem primeStar_log_completion_iff (α : ℝ) :
    (∃a,∀S t x,0≤primeStarEnergy S a (primeStarLogDiagonal α) t x) ↔ 2 < α := by
  constructor
  · rintro ⟨a,ha⟩
    exact (primeStar_log_payment_summable_iff α).mp
      ((primeStar_all_nonneg_iff a _ (primeStarLogDiagonal_pos α)).mp ha).1
  · intro hα
    exact ⟨_,primeStar_minimal_completion _ (primeStarLogDiagonal_pos α)
      (summable_primeStar_log_payment α hα)⟩

/-- The exact least payment realizes the positive logarithmic completion. -/
theorem primeStar_log_minimal_completion (α : ℝ) (hα : 2 < α) :
    ∀S t x,0≤primeStarEnergy S
      (∑'p,(primeStarCoupling p)^2/primeStarLogDiagonal α p)
      (primeStarLogDiagonal α) t x :=
  primeStar_minimal_completion _ (primeStarLogDiagonal_pos α)
    (summable_primeStar_log_payment α hα)

/-- Every finite central budget has an explicit negative probe at or below exponent two. -/
theorem primeStar_log_negative (α : ℝ) (hα : α≤2) (a : ℝ) :
    ∃S,primeStarEnergy S a (primeStarLogDiagonal α) 1
      (fun p=>primeStarCoupling p/primeStarLogDiagonal α p)<0 :=
  primeStar_negative_of_not_summable a _ (primeStarLogDiagonal_pos α)
    (not_summable_primeStar_log_payment α hα)

#print axioms summable_primeStar_log_payment
#print axioms not_summable_primeStar_log_payment
#print axioms primeStar_log_payment_summable_iff
#print axioms primeStar_log_completion_iff
#print axioms primeStar_log_minimal_completion
#print axioms primeStar_log_negative
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
