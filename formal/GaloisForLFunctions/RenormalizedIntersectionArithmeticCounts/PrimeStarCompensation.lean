import GaloisForLFunctions.HeightHomotopyArithmeticCounts.TorsionPrimePairKernel
import GaloisForLFunctions.RHTower.ZetaFisherVariance
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Sharp diagonal compensation of the arithmetic prime star

The spacing-limit torsion kernel on conductor one and prime conductors has
couplings `−log(p)/√p` and no interaction between distinct prime leaves.
After diagonal correction, positivity on every finite prime set is equivalent
to positive leaf diagonals and a summable Schur payment covered by the central
diagonal. The square completion gives the exact least payment and explicit
negative probes when it fails.

For corrected diagonal `d(p)+p^δ`, a finite payment exists exactly when `δ>0`.
More generally, any eventual `O((log p)^2)` leaf diagonal fails. These are
statements about the actual prime-star restriction; composite interactions and
nonlocal corrections are separate questions.
-/

noncomputable section
open Finset Filter Topology
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

open ArithmeticEffectivityTheory ArithmeticIntersectionTheory HeightHomotopyArithmeticCounts

/-- The torsion coupling between conductor one and a prime. -/
def primeStarCoupling (p : Nat.Primes) : ℝ := Real.log p / Real.sqrt p

/-- The corrected prime-star energy, with central payment `a` and leaf diagonals `D`. -/
def primeStarEnergy (S : Finset Nat.Primes) (a : ℝ) (D : Nat.Primes → ℝ)
    (t : ℝ) (x : Nat.Primes → ℝ) : ℝ :=
  a*t^2 + ∑ p∈S, (D p*(x p)^2-2*t*primeStarCoupling p*x p)

/-- The exact central payment required by a finite set of prime conductors. -/
def primeStarPayment (S : Finset Nat.Primes) (D : Nat.Primes → ℝ) : ℝ :=
  ∑ p∈S, (primeStarCoupling p)^2/D p

/-- The central-prime row is the von Mangoldt coupling of the original spacing kernel. -/
theorem primeStar_kernel_one (p : Nat.Primes) :
    spacingLimitKernel 1 p = -primeStarCoupling p := by
  have hn : (1:ℕ)≠p.val := p.property.ne_one.symm
  change spacingLimitKernel 1 p.val = _
  rw [spacingLimitKernel,if_neg hn,add_zero,weilPrimeKernel,
    if_pos ⟨one_dvd p.val,hn⟩,Nat.div_one,
    ArithmeticFunction.vonMangoldt_apply_prime p.property]
  rfl

/-- Distinct prime leaves have no interaction in the original torsion kernel. -/
theorem primeStar_kernel_offDiagonal (p q : Nat.Primes) (hpq : p≠q) :
    spacingLimitKernel p q=0 := by
  have hne : p.val≠q.val := fun h => hpq (Subtype.ext h)
  have hnd : ¬p.val∣q.val := by
    intro h
    rcases (Nat.dvd_prime q.property).mp h with h|h
    · exact p.property.ne_one h
    · exact hne h
  have hdn : ¬q.val∣p.val := by
    intro h
    rcases (Nat.dvd_prime p.property).mp h with h|h
    · exact q.property.ne_one h
    · exact hne h.symm
  change spacingLimitKernel p.val q.val=0
  simp only [spacingLimitKernel,if_neg hne,weilPrimeKernel,
    hnd,hdn,false_and,ite_false,neg_zero,zero_add]

/-- Completing squares identifies both the payment and its minimizing probe. -/
theorem primeStar_complete_square (S : Finset Nat.Primes) (a : ℝ)
    (D : Nat.Primes → ℝ) (hD : ∀p∈S,0<D p) (t : ℝ) (x : Nat.Primes → ℝ) :
    primeStarEnergy S a D t x =
      (a-primeStarPayment S D)*t^2+
      ∑ p∈S,D p*(x p-t*primeStarCoupling p/D p)^2 := by
  have he (p) (hp:p∈S) :
      D p*(x p)^2-2*t*primeStarCoupling p*x p =
      D p*(x p-t*primeStarCoupling p/D p)^2-
        (primeStarCoupling p)^2/D p*t^2 := by
    field_simp [ne_of_gt (hD p hp)]
    ring
  unfold primeStarEnergy primeStarPayment
  rw [sum_congr rfl he,sum_sub_distrib,←sum_mul]
  ring

/-- A finite star is positive exactly when its central payment covers the sharp budget. -/
theorem primeStar_nonneg_iff (S : Finset Nat.Primes) (a : ℝ)
    (D : Nat.Primes → ℝ) (hD : ∀p∈S,0<D p) :
    (∀t x,0≤primeStarEnergy S a D t x) ↔ primeStarPayment S D≤a := by
  constructor
  · intro h
    have he:=h 1 (fun p=>primeStarCoupling p/D p)
    rw [primeStar_complete_square S a D hD] at he
    simp only [one_mul,sub_self,zero_pow (by omega : (2:ℕ)≠0),mul_zero,sum_const_zero,
      one_pow,mul_one,add_zero] at he
    exact sub_nonneg.mp he
  · intro ha t x
    rw [primeStar_complete_square S a D hD]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg _))
      (sum_nonneg fun p hp=>mul_nonneg (hD p hp).le (sq_nonneg _))

/-- An insufficient central budget has an explicit negative finite arithmetic probe. -/
theorem primeStar_minimizer (S : Finset Nat.Primes) (a : ℝ)
    (D : Nat.Primes → ℝ) (hD : ∀p∈S,0<D p) :
    primeStarEnergy S a D 1 (fun p=>primeStarCoupling p/D p)=a-primeStarPayment S D := by
  rw [primeStar_complete_square S a D hD]
  simp only [one_mul,sub_self,zero_pow (by omega : (2:ℕ)≠0),mul_zero,sum_const_zero,
    one_pow,mul_one,add_zero]

/-- The completed-star energy is exactly the original torsion matrix with diagonal corrections. -/
theorem primeStarEnergy_eq_torsion (S : Finset Nat.Primes) (a : ℝ)
    (D : Nat.Primes → ℝ) (t : ℝ) (x : Nat.Primes → ℝ) :
    primeStarEnergy S a D t x =
      t^2*(spacingLimitKernel 1 1+a) +
      (∑p∈S,∑q∈S,x p*x q*(spacingLimitKernel p q+
        if p=q then D p-tameDifferent p else 0)) +
      ∑p∈S,t*x p*(spacingLimitKernel 1 p+spacingLimitKernel p 1) := by
  classical
  have hrow (p) (hp:p∈S) :
      (∑q∈S,x p*x q*(spacingLimitKernel p q+
        if p=q then D p-tameDifferent p else 0))=D p*(x p)^2 := by
    rw [sum_eq_single p]
    · rw [if_pos rfl,spacingLimitKernel_self]
      ring
    · intro q hq hqp
      rw [if_neg hqp.symm,primeStar_kernel_offDiagonal p q hqp.symm]
      ring
    · exact fun hn=>(hn hp).elim
  have hcross (p : Nat.Primes) :
      t*x p*(spacingLimitKernel 1 p+spacingLimitKernel p 1)=
        -(2*t*primeStarCoupling p*x p) := by
    rw [spacingLimitKernel_comm p.val 1,primeStar_kernel_one]
    ring
  rw [sum_congr rfl hrow]
  simp_rw [hcross]
  have h11 : spacingLimitKernel 1 1=0 := by
    rw [spacingLimitKernel_self]
    simp only [tameDifferent,Nat.primeFactors_one,sum_empty]
  rw [h11,zero_add,primeStarEnergy,sum_sub_distrib,sum_neg_distrib]
  ring

/-- Positivity on every finite prime star is equivalent to a finite total payment. -/
theorem primeStar_all_nonneg_iff (a : ℝ) (D : Nat.Primes → ℝ)
    (hD : ∀p,0<D p) :
    (∀S t x,0≤primeStarEnergy S a D t x) ↔
      Summable (fun p=>(primeStarCoupling p)^2/D p) ∧
      (∑'p,(primeStarCoupling p)^2/D p)≤a := by
  have hn : 0≤(fun p=>(primeStarCoupling p)^2/D p) :=
    fun p=>div_nonneg (sq_nonneg _) (hD p).le
  constructor
  · intro h
    have hb (S) : primeStarPayment S D≤a :=
      (primeStar_nonneg_iff S a D (fun p _=>hD p)).mp (h S)
    exact ⟨summable_of_sum_le hn hb,Real.tsum_le_of_sum_le hn hb⟩
  · rintro ⟨hs,ha⟩ S
    apply (primeStar_nonneg_iff S a D (fun p _=>hD p)).mpr
    exact (Summable.sum_le_tsum S (fun p _=>hn p) hs).trans ha

/-- Every original prime coupling is strictly positive. -/
theorem primeStarCoupling_pos (p : Nat.Primes) : 0<primeStarCoupling p := by
  exact div_pos (Real.log_pos (by exact_mod_cast p.property.one_lt))
    (Real.sqrt_pos.mpr (by exact_mod_cast p.property.pos))

/-- Positivity itself forces every leaf diagonal to be strictly positive. -/
theorem primeStar_diagonal_pos_of_nonneg (a : ℝ) (D : Nat.Primes → ℝ)
    (h : ∀S t x,0≤primeStarEnergy S a D t x) (p : Nat.Primes) : 0<D p := by
  have hn:=h {p} 0 (fun _=>1)
  simp only [primeStarEnergy,sum_singleton,zero_pow (by omega : (2:ℕ)≠0),
    mul_zero,zero_add,one_pow,mul_one,zero_mul,sub_zero] at hn
  by_contra hnp
  have hz : D p=0 := le_antisymm (le_of_not_gt hnp) hn
  have hc : 2*primeStarCoupling p≠0 := mul_ne_zero two_ne_zero (primeStarCoupling_pos p).ne'
  have he:=h {p} 1 (fun _=>(a+1)/(2*primeStarCoupling p))
  simp only [primeStarEnergy,sum_singleton,hz,zero_mul,one_pow,mul_one,sub_eq_add_neg,
    zero_add] at he
  have hh : 2*primeStarCoupling p*((a+1)/(2*primeStarCoupling p))=a+1 :=
    mul_div_cancel₀ (a+1) hc
  linarith only [he,hh]

/-- The unrestricted classification includes strict leaf positivity as a conclusion. -/
theorem primeStar_complete_classification (a : ℝ) (D : Nat.Primes → ℝ) :
    (∀S t x,0≤primeStarEnergy S a D t x) ↔
      (∀p,0<D p) ∧ Summable (fun p=>(primeStarCoupling p)^2/D p) ∧
        (∑'p,(primeStarCoupling p)^2/D p)≤a := by
  constructor
  · intro h
    have hd:=primeStar_diagonal_pos_of_nonneg a D h
    exact ⟨hd,(primeStar_all_nonneg_iff a D hd).mp h⟩
  · rintro ⟨hd,hs,ha⟩
    exact (primeStar_all_nonneg_iff a D hd).mpr ⟨hs,ha⟩

/-- Summable compensation gives a positive completion at the exact minimal central payment. -/
theorem primeStar_minimal_completion (D : Nat.Primes → ℝ) (hD : ∀p,0<D p)
    (hs : Summable (fun p=>(primeStarCoupling p)^2/D p)) :
    ∀S t x,0≤primeStarEnergy S (∑'p,(primeStarCoupling p)^2/D p) D t x :=
  (primeStar_all_nonneg_iff _ D hD).mpr ⟨hs,le_rfl⟩

/-- If the payment diverges, every central budget admits an explicit negative finite probe. -/
theorem primeStar_negative_of_not_summable (a : ℝ) (D : Nat.Primes → ℝ)
    (hD : ∀p,0<D p) (hs : ¬Summable (fun p=>(primeStarCoupling p)^2/D p)) :
    ∃S,primeStarEnergy S a D 1 (fun p=>primeStarCoupling p/D p)<0 := by
  have hex : ∃S, a<primeStarPayment S D := by
    by_contra h
    have hb : ∀S,primeStarPayment S D≤a := by
      simpa only [not_exists,not_lt] using h
    exact hs (summable_of_sum_le (fun p=>div_nonneg (sq_nonneg _) (hD p).le) hb)
  obtain ⟨S,hS⟩:=hex
  refine ⟨S,?_⟩
  rw [primeStar_minimizer S a D (fun p _=>hD p)]
  exact sub_neg.mpr hS

open ArithmeticIntersectionTheory RenormalizedArithmeticPotentialTheory

/-- Adding a conductor power to the original tame prime diagonal. -/
def primeStarPowerDiagonal (δ : ℝ) (p : Nat.Primes) : ℝ :=
  tameDifferent p+(p:ℝ)^δ

theorem primeStarPowerDiagonal_pos (δ : ℝ) (p : Nat.Primes) :
    0<primeStarPowerDiagonal δ p :=
  add_pos_of_nonneg_of_pos (tameDifferent_nonneg _)
    (Real.rpow_pos_of_pos (by exact_mod_cast p.property.pos) _)

/-- The payment density retains the original logarithmic prime coupling. -/
theorem primeStar_payment_density (D : Nat.Primes → ℝ) (p : Nat.Primes) :
    (primeStarCoupling p)^2/D p=(Real.log p)^2/((p:ℝ)*D p) := by
  unfold primeStarCoupling
  rw [div_pow,Real.sq_sqrt (show (0:ℝ)≤p by positivity),div_div]

/-- Every positive power makes the entire prime-star compensation summable. -/
theorem summable_primeStar_power_payment (δ : ℝ) (hδ : 0<δ) :
    Summable (fun p=>(primeStarCoupling p)^2/primeStarPowerDiagonal δ p) := by
  have hs : Summable (fun p : Nat.Primes=>(Real.log p)^2*(p:ℝ)^(-(1+δ))) :=
    (RHTower.summable_log_natCast_pow_mul_rpow_neg 2 (by linarith : 1<1+δ)).comp_injective
      (Subtype.val_injective : Function.Injective (fun p : Nat.Primes=>(p:ℕ)))
  apply hs.of_nonneg_of_le
  · intro p
    exact div_nonneg (sq_nonneg _) (primeStarPowerDiagonal_pos δ p).le
  · intro p
    have hp : (0:ℝ)<p := by exact_mod_cast p.property.pos
    rw [primeStar_payment_density]
    calc (Real.log p)^2/((p:ℝ)*primeStarPowerDiagonal δ p) ≤
          (Real.log p)^2/((p:ℝ)*(p:ℝ)^δ) :=
            div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hp (Real.rpow_pos_of_pos hp _))
              (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (tameDifferent_nonneg _)) hp.le)
         _ = (Real.log p)^2*(p:ℝ)^(-(1+δ)) := by
          have he : (p:ℝ)*(p:ℝ)^δ=(p:ℝ)^(1+δ) := by
            rw [Real.rpow_add hp,Real.rpow_one]
          rw [he,div_eq_mul_inv,←Real.rpow_neg hp.le]

/-- At nonpositive power, the payment dominates the divergent reciprocal-prime series. -/
theorem not_summable_primeStar_power_payment (δ : ℝ) (hδ : δ≤0) :
    ¬Summable (fun p=>(primeStarCoupling p)^2/primeStarPowerDiagonal δ p) := by
  intro hs
  apply Nat.Primes.not_summable_one_div
  apply hs.of_norm_bounded_eventually
  have hpco : Tendsto (fun p : Nat.Primes=>(p:ℕ)) cofinite atTop := by
    rw [←Nat.cofinite_eq_atTop]
    exact (Subtype.val_injective : Function.Injective (fun p : Nat.Primes=>(p:ℕ))).tendsto_cofinite
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hpco)
  filter_upwards [hl.eventually_ge_atTop 2] with p hp2
  simp only [Function.comp_apply] at hp2
  have hp : (0:ℝ)<p := by exact_mod_cast p.property.pos
  have hpow : (p:ℝ)^δ≤1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast p.property.one_lt.le) hδ
  have hd : primeStarPowerDiagonal δ p≤(Real.log p)^2 := by
    have hb:=tameDifferent_le_log p.property.pos
    dsimp only [primeStarPowerDiagonal]
    nlinarith only [hb,hpow,hp2,sq_nonneg (Real.log p-2)]
  rw [Real.norm_of_nonneg (div_nonneg zero_le_one hp.le),primeStar_payment_density]
  apply (div_le_div_iff₀ hp (mul_pos hp (primeStarPowerDiagonal_pos δ p))).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hd hp.le]

/-- Even logarithmic-square leaf growth cannot be compensated by a finite central payment. -/
theorem not_summable_primeStar_of_log_square_bound
    (D : Nat.Primes → ℝ) (hD : ∀p,0<D p) (C : ℝ)
    (hb : ∀ᶠp : Nat.Primes in cofinite,D p≤C*(Real.log p)^2) :
    ¬Summable (fun p=>(primeStarCoupling p)^2/D p) := by
  intro hs
  apply Nat.Primes.not_summable_one_div
  apply (hs.mul_left C).of_norm_bounded_eventually
  filter_upwards [hb] with p hpD
  have hp : (0:ℝ)<p := by exact_mod_cast p.property.pos
  rw [Real.norm_of_nonneg (div_nonneg zero_le_one hp.le),primeStar_payment_density,
    ←mul_div_assoc]
  apply (div_le_div_iff₀ hp (mul_pos hp (hD p))).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hpD hp.le]

/-- Logarithmic-square diagonal compensation leaves explicit negative finite prime probes. -/
theorem primeStar_negative_of_log_square_bound
    (a : ℝ) (D : Nat.Primes → ℝ) (hD : ∀p,0<D p) (C : ℝ)
    (hb : ∀ᶠp : Nat.Primes in cofinite,D p≤C*(Real.log p)^2) :
    ∃S,primeStarEnergy S a D 1 (fun p=>primeStarCoupling p/D p)<0 :=
  primeStar_negative_of_not_summable a D hD
    (not_summable_primeStar_of_log_square_bound D hD C hb)

/-- Positive conductor power is exactly the boundary for finite central compensation. -/
theorem primeStar_power_payment_summable_iff (δ : ℝ) :
    Summable (fun p=>(primeStarCoupling p)^2/primeStarPowerDiagonal δ p) ↔ 0<δ := by
  constructor
  · intro h
    by_contra hn
    exact not_summable_primeStar_power_payment δ (le_of_not_gt hn) h
  · exact summable_primeStar_power_payment δ

/-- A positive completion on every finite prime star exists exactly above critical weight. -/
theorem primeStar_power_completion_iff (δ : ℝ) :
    (∃a,∀S t x,0≤primeStarEnergy S a (primeStarPowerDiagonal δ) t x) ↔ 0<δ := by
  constructor
  · rintro ⟨a,ha⟩
    exact (primeStar_power_payment_summable_iff δ).mp
      ((primeStar_all_nonneg_iff a _ (primeStarPowerDiagonal_pos δ)).mp ha).1
  · intro hδ
    exact ⟨_,primeStar_minimal_completion _ (primeStarPowerDiagonal_pos δ)
      (summable_primeStar_power_payment δ hδ)⟩

#print axioms primeStar_kernel_one
#print axioms primeStar_kernel_offDiagonal
#print axioms primeStar_complete_square
#print axioms primeStar_nonneg_iff
#print axioms primeStar_minimizer
#print axioms primeStarEnergy_eq_torsion
#print axioms primeStar_complete_classification
#print axioms primeStar_all_nonneg_iff
#print axioms primeStar_minimal_completion
#print axioms primeStar_negative_of_not_summable
#print axioms summable_primeStar_power_payment
#print axioms not_summable_primeStar_power_payment
#print axioms primeStar_power_payment_summable_iff
#print axioms primeStar_power_completion_iff
#print axioms primeStar_negative_of_log_square_bound
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
