import GaloisForLFunctions.BezoutValuationIncidence.CoprimeMobiusSignAndEvenDilationMeans
import GaloisForLFunctions.RHTower.SquarefreeDiscrepancyMellin

/-!
# Effective square-root error after prime deletion

The squarefree prime-deletion recurrence is a dilation equation.
On discrepancies bounded at square-root scale its inverse has norm
at most 1/(1−1/√p). The resulting Euler product gives an explicit
uniform bound for every positive modulus and every real cutoff.
-/
noncomputable section
open Finset Filter
open scoped Topology ArithmeticFunction.Moebius
open _root_.RHTower.Sieve (squarefreeDensity)
namespace GaloisForLFunctions.BezoutValuationIncidence

def coprimeCountError (Q : ℕ) (x : ℝ) :=
  coprimeSquarefreeCount Q ⌊x⌋₊ - coprimeSquarefreeDensity Q*x

/-- Inverting a prime step on square-root size errors costs this factor. -/
def squareRootDeletionFactor (p : ℕ) := (1-(Real.sqrt p)⁻¹)⁻¹

private theorem prime_inv_sqrt {p : ℕ} (hp : p.Prime) : (Real.sqrt p)⁻¹<1 := by
  apply inv_lt_one_of_one_lt₀
  exact (Real.lt_sqrt zero_le_one).mpr (by rw [one_pow]; exact_mod_cast hp.one_lt)

private theorem one_le_cost {p : ℕ} (hp : p.Prime) : 1 ≤ squareRootDeletionFactor p := by
  unfold squareRootDeletionFactor
  rw [one_le_inv₀ (sub_pos.mpr (prime_inv_sqrt hp))]
  exact sub_le_self _ (inv_nonneg.mpr (Real.sqrt_nonneg _))

private theorem small_cut {Q : ℕ} (hQ : Q≠0) {x : ℝ} (hx : 0≤x) (hsmall : x<1) :
    |coprimeCountError Q x|≤Real.sqrt x := by
  have hc := tendsto_coprimeSquarefreeMean_positive_modulus ⟨Q,Nat.pos_of_ne_zero hQ⟩
  have hD : |coprimeSquarefreeDensity Q|≤1 :=
    le_of_tendsto hc.abs (.of_forall (abs_coprimeSquarefreeMean_le_one Q))
  rw [coprimeCountError,Nat.floor_eq_zero.mpr hsmall]
  simp only [coprimeSquarefreeCount,Icc_eq_empty_of_lt (Nat.zero_lt_one),sum_empty,
    zero_sub,abs_neg,abs_mul,abs_of_nonneg hx]
  have hroot := Real.sqrt_le_one.mpr hsmall.le
  have hxroot : x≤Real.sqrt x := by
    nlinarith only [Real.sq_sqrt hx,mul_nonneg (Real.sqrt_nonneg x) (sub_nonneg.mpr hroot)]
  exact (mul_le_mul_of_nonneg_right hD hx).trans (by rwa [one_mul])

private theorem error_relation {p Q : ℕ} (hp : p.Prime) (hPQ : ¬p∣Q) (hQ : Q≠0) (x : ℝ) :
    coprimeCountError Q x=coprimeCountError (p*Q) x+coprimeCountError (p*Q) (x/p) := by
  simp only [coprimeCountError,Nat.floor_div_natCast,coprimeSquarefreeDensity_prime_mul hp hPQ hQ]
  rw [coprimeSquarefreeCount_prime_relation hp hPQ]
  have hpR : (0:ℝ)<p := Nat.cast_pos.mpr hp.pos
  field_simp [hpR.ne',(by positivity : (p:ℝ)+1≠0)]
  <;> ring

/-- Deleting p multiplies the previous discrepancy envelope by
1/(1−1/√p). This bound treats the fractional cutoff exactly. -/
theorem squarefree_count_deletion_envelope {p Q : ℕ} (hp : p.Prime) (hPQ : ¬p∣Q)
    (hQ : Q≠0) {K : ℝ} (hK : 1≤K) (hprev : ∀ x:ℝ,0≤x → |coprimeCountError Q x|≤K*Real.sqrt x) :
    ∀ x:ℝ,0≤x → |coprimeCountError (p*Q) x|≤K*squareRootDeletionFactor p*Real.sqrt x := by
  let b := (Real.sqrt p)⁻¹
  have hpR : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
  have hb : b<1 := prime_inv_sqrt hp
  have hd := one_le_cost hp
  have hC : 1 ≤ K*squareRootDeletionFactor p := by
    nlinarith only [hK,hd,mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hd)]
  have price : K+K*squareRootDeletionFactor p*b=K*squareRootDeletionFactor p := by
    change K+K*(1-b)⁻¹*b=K*(1-b)⁻¹
    field_simp [(sub_pos.mpr hb).ne'];ring
  have law (N : ℕ) : ∀ x:ℝ,⌊x⌋₊=N → 0≤x →
      |coprimeCountError (p*Q) x|≤K*squareRootDeletionFactor p*Real.sqrt x := by
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro x he hx
      rcases lt_or_ge x 1 with hsmall|hbig
      · exact (small_cut (mul_ne_zero hp.ne_zero hQ) hx hsmall).trans
          (le_mul_of_one_le_left (Real.sqrt_nonneg _) hC)
      have hN : 1≤N := he ▸ (Nat.one_le_floor_iff x).mpr hbig
      have hf : ⌊x/(p:ℝ)⌋₊<N := by rw [Nat.floor_div_natCast,he]; exact Nat.div_lt_self hN hp.one_lt
      have H := ih _ hf (x/p) rfl (div_nonneg hx hpR.le)
      have hr := error_relation hp hPQ hQ x
      rw [show coprimeCountError (p*Q) x=coprimeCountError Q x-coprimeCountError (p*Q) (x/p) by linarith only [hr]]
      apply (abs_sub _ _).trans ((add_le_add (hprev x hx) H).trans_eq ?_)
      rw [Real.sqrt_div hx,div_eq_mul_inv]
      change K*Real.sqrt x+K*squareRootDeletionFactor p*(Real.sqrt x*b) = _
      linear_combination Real.sqrt x*price
  exact fun x hx => law _ x rfl hx

private theorem unit_envelope (x : ℝ) (hx : 0≤x) :
    |coprimeCountError 1 x|≤4*Real.sqrt x := by
  rcases lt_or_ge x 1 with hh|hh
  · exact (small_cut one_ne_zero hx hh).trans (by nlinarith only [Real.sqrt_nonneg x])
  simpa [coprimeCountError,coprimeSquarefreeCount,coprimeSquarefreeIndicator,coprimeSquarefreeDensity_one,
    _root_.RHTower.SquarefreeDiscrepancy.error,_root_.RHTower.SquarefreeDiscrepancy.count] using
    _root_.RHTower.SquarefreeDiscrepancy.abs_error_le hh

/-- The real-cutoff squarefree count with any squarefree forbidden
modulus Q has a square-root remainder priced by its individual primes. -/
theorem squarefree_count_euler_envelope (Q : ℕ) : Squarefree Q → ∀ x:ℝ,0≤x →
    |coprimeCountError Q x|≤(4*∏ p∈Q.primeFactors,squareRootDeletionFactor p)*Real.sqrt x := by
  induction Q using Nat.strong_induction_on with
  | _ L ih =>
    intro hsq x hx
    by_cases hOne : L=1
    · subst L;simpa using unit_envelope x hx
    let p := L.minFac
    let R := L/p
    have hp : p.Prime := Nat.minFac_prime hOne
    have hdiv : p∣L := Nat.minFac_dvd L
    have hfac : p*R=L := Nat.mul_div_cancel' hdiv
    have hcop : p.Coprime R := Nat.coprime_of_squarefree_mul (by simpa only [hfac] using hsq)
    have hnd : ¬p∣R := hp.coprime_iff_not_dvd.mp hcop
    have hR := Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hdiv) hsq
    have hlt : R<L := Nat.div_lt_self (Nat.pos_of_ne_zero hsq.ne_zero) hp.one_lt
    have hnot : p∉R.primeFactors := fun h => hnd (Nat.mem_primeFactors.mp h).2.1
    have hset : L.primeFactors=insert p R.primeFactors := by
      rw [←hfac,Nat.primeFactors_mul hp.ne_zero hR.ne_zero,hp.primeFactors];simp <;> rfl
    have hprod : 1≤∏ q∈R.primeFactors,squareRootDeletionFactor q :=
      Finset.one_le_prod fun q hq => one_le_cost (Nat.mem_primeFactors.mp hq).1
    have hb := squarefree_count_deletion_envelope hp hnd hR.ne_zero
      (K:=4*∏ q∈R.primeFactors,squareRootDeletionFactor q) (by linarith only [hprod])
      (fun t ht => ih R hlt hR t ht) x hx
    rw [hfac] at hb
    rw [hset,prod_insert hnot]
    convert hb using 1 <;> ring

/-- Repeated prime factors of the forbidden modulus incur no further
cost. The same product bounds every positive modulus. -/
theorem coprime_squarefree_count_error {Q : ℕ} (hQ : Q≠0) {x : ℝ} (hx : 0≤x) :
    |coprimeCountError Q x|≤(4*∏ p∈Q.primeFactors,squareRootDeletionFactor p)*Real.sqrt x := by
  have hR : primeRadical Q≠0 := (show 0<primeRadical Q from
    prod_pos fun p hp => (Nat.mem_primeFactors.mp hp).1.pos).ne'
  have hcount : coprimeSquarefreeCount (primeRadical Q) ⌊x⌋₊=coprimeSquarefreeCount Q ⌊x⌋₊ := by
    refine sum_congr rfl fun n hn => ?_
    have hn0 := (Nat.pos_of_ne_zero (by have := (mem_Icc.mp hn).1;omega):0<n)
    have hc : Nat.Coprime (primeRadical Q) n ↔ Nat.Coprime Q n := by
      rw [←Nat.disjoint_primeFactors hR hn0.ne',←Nat.disjoint_primeFactors hQ hn0.ne']
      simp only [primeRadical,Nat.primeFactors_prod_primeFactors]
    simp only [coprimeSquarefreeIndicator,hc]
  have hb := squarefree_count_euler_envelope (primeRadical Q) (squarefree_primeRadical Q hQ) x hx
  simp only [coprimeCountError] at hb
  rw [hcount] at hb
  simpa only [coprimeCountError,coprimeSquarefreeDensity,primeRadical,Nat.primeFactors_prod_primeFactors] using hb

end GaloisForLFunctions.BezoutValuationIncidence
