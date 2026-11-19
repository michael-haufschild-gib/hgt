import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheTotientTermInTheReflectedCompositePrice

/-!
# The remaining factors of opposite primitive integers

Delete ordinary primes above the cutoff only when the cofactor is at least
two. Subtracting the full primitive log price then pairs the two remaining
integer factors across the common midpoint. Above twice the square root
at most one ordinary prime is deleted at either endpoint.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def selectedPrimes (Q x : ℕ) : Finset ℕ :=
  x.primeFactors.filter (fun p => Q < p ∧ 2*p ≤ x)

/-- Integer factor left after deleting the selected proper prime divisors once each. -/
def remainingMidpointFactor (Q x : ℕ) : ℕ := x / ∏ p ∈ selectedPrimes Q x,p

/-- The large proper prime leaves exactly its original cofactor at the
square-root cutoff, including products at the upper interval endpoint. -/
theorem remaining_factor_at_large_prime {n Q a p : ℕ} (hp : p.Prime) (ha : 2 ≤ a)
    (hx : a*p ≤ 4*n) (hQ : ⌊2*Real.sqrt n⌋₊ ≤ Q) (hpQ : Q < p) :
    remainingMidpointFactor Q (a*p) = a := by
  have haQ : a ≤ Q := by
    by_contra! h
    have ha' := (Nat.floor_lt (by positivity : 0 ≤ 2*Real.sqrt n)).mp (hQ.trans_lt h)
    have hp' := (Nat.floor_lt (by positivity : 0 ≤ 2*Real.sqrt n)).mp (hQ.trans_lt hpQ)
    have hh := (mul_le_mul_of_nonneg_left hp'.le (by positivity : (0:ℝ) ≤ 2*Real.sqrt n)).trans_lt
      (mul_lt_mul_of_pos_right ha' (Nat.cast_pos.mpr hp.pos))
    have hcap : (a:ℝ)*p ≤ 4*n := by exact_mod_cast hx
    nlinarith only [hh,hcap,Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n)]
  have hs : selectedPrimes Q (a*p)={p} := by
    ext d
    simp only [selectedPrimes,mem_filter,Nat.mem_primeFactors,mem_singleton]
    constructor
    · rintro ⟨⟨hd,hdvd,_⟩,hQd,_⟩
      rcases hd.dvd_mul.mp hdvd with hda | hdp
      · exact False.elim (hQd.not_ge ((Nat.le_of_dvd (by omega) hda).trans haQ))
      · exact ((Nat.dvd_prime hp).mp hdp).resolve_left hd.ne_one
    · intro he
      subst d
      exact ⟨⟨hp,dvd_mul_left p a,Nat.mul_ne_zero (by omega) hp.ne_zero⟩,
        hpQ,Nat.mul_le_mul_right p ha⟩
  rw [remainingMidpointFactor,hs,prod_singleton,Nat.mul_div_cancel _ hp.pos]

private theorem remaining_factor_log (Q : ℕ) {x : ℕ} (hx : 0 < x) :
    0 < remainingMidpointFactor Q x ∧ Real.log (remainingMidpointFactor Q x) =
      Real.log x-∑ p ∈ selectedPrimes Q x,Real.log p := by
  let S := selectedPrimes Q x
  have hd := (prod_dvd_prod_of_subset S x.primeFactors id (filter_subset _ _)).trans (Nat.prod_primeFactors_dvd x)
  have hp (p : ℕ) (h : p ∈ S) : 0 < p := (Nat.prime_of_mem_primeFactors (mem_filter.mp h).1).pos
  have hprod : 0 < ∏ p ∈ S,p := Finset.prod_pos hp
  have hrem : 0 < remainingMidpointFactor Q x := Nat.div_pos (Nat.le_of_dvd hx hd) hprod
  refine ⟨hrem,?_⟩
  have eqn : remainingMidpointFactor Q x * (∏ p ∈ S,p) = x := Nat.div_mul_cancel hd
  have hh := congrArg (fun m : ℕ => Real.log (m:ℝ)) eqn
  change Real.log ((remainingMidpointFactor Q x * (∏ p ∈ S,p) : ℕ):ℝ)=Real.log x at hh
  rw [Nat.cast_mul,Real.log_mul (Nat.cast_ne_zero.mpr hrem.ne') (Nat.cast_ne_zero.mpr hprod.ne'),
    Nat.cast_prod,Real.log_prod (fun p h => Nat.cast_ne_zero.mpr (hp p h).ne')] at hh
  linarith only [hh]

private def properPrimePriceAt (S : Finset ℕ) (n x : ℕ) : ℝ :=
  ∑ p ∈ S,if p ∣ x then (if n.Coprime x ∧ 2*p ≤ x then Real.log p else 0) else 0

private theorem proper_prime_prefix (S : Finset ℕ) (hS : ∀ p ∈ S,p.Prime) (n T : ℕ) :
    (∑ x ∈ Icc 1 T,properPrimePriceAt S n x) = ∑ p ∈ S,Real.log p*(if n.Coprime p then
      (((Icc 2 (T/p)).filter (n.Coprime ·)).card:ℝ) else 0) := by
  simp only [properPrimePriceAt]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hpr
  have hp := (hS p hpr).pos
  have hm (j : ℕ) : 2*p ≤ p*j ↔ 2 ≤ j := by
    rw [Nat.mul_comm 2 p]
    exact ⟨fun h => Nat.le_of_mul_le_mul_left h hp,Nat.mul_le_mul_left p⟩
  rw [←sum_filter,_root_.RHTower.Sieve.sum_filter_dvd_eq_sum_scaled hp]
  simp only [Nat.coprime_mul_iff_right,hm]
  by_cases hc : n.Coprime p
  · simp only [and_iff_right hc,if_pos hc]
    have hset : (Icc 1 (T/p)).filter (fun j => n.Coprime j ∧ 2 ≤ j) =
        (Icc 2 (T/p)).filter (n.Coprime ·) := by
      ext j
      simp only [mem_filter,mem_Icc]
      exact ⟨fun h => ⟨⟨h.2.2,h.1.2⟩,h.2.1⟩,
        fun h => ⟨⟨(by decide : 1 ≤ 2).trans h.1.1,h.1.2⟩,h.2,h.1.1⟩⟩
    rw [←sum_filter,hset,sum_const,nsmul_eq_mul,mul_comm]
  · simp [hc]

private theorem price_of_selected_factors (n Q : ℕ) :
    let S := (Ioc Q (4*n)).filter Nat.Prime
    largePrimeCofactorPrice n Q = (∑ x ∈ Ioc (3*n) (4*n),properPrimePriceAt S n x) -
      (∑ x ∈ Ioc (2*n) (3*n),properPrimePriceAt S n x) := by
  let S := (Ioc Q (4*n)).filter Nat.Prime
  let f := properPrimePriceAt S n
  have interval (u v : ℕ) (huv : u ≤ v) : (∑ x ∈ Ioc u v,f x) =
      (∑ x ∈ Icc 1 v,f x)-(∑ x ∈ Icc 1 u,f x) := by
    have hi (j : ℕ) : Icc 1 j = Ioc 0 j := by ext x; simp only [mem_Icc,mem_Ioc]; omega
    simp only [hi]
    linarith only [sum_Ioc_consecutive f (Nat.zero_le u) huv]
  change (∑ p ∈ S,Real.log p*properCofactorMidpoint n p) = _
  change _ = (∑ x ∈ Ioc (3*n) (4*n),f x)-(∑ x ∈ Ioc (2*n) (3*n),f x)
  rw [interval _ _ (by omega),interval _ _ (by omega)]
  have hS (p : ℕ) (hp : p ∈ S) := (mem_filter.mp hp).2
  simp only [f,proper_prime_prefix S hS,←sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  let A (j : ℕ) : ℝ := (((Icc 2 (j*n/p)).filter (n.Coprime ·)).card:ℝ)
  unfold properCofactorMidpoint
  split_ifs
  · change Real.log p*(A 4-2*A 3+A 2)=
      (Real.log p*A 4-Real.log p*A 3)-(Real.log p*A 3-Real.log p*A 2)
    ring
  · ring

private theorem price_at_primitive {n Q x : ℕ} (hx : 0 < x) (hcap : x ≤ 4*n) :
    properPrimePriceAt ((Ioc Q (4*n)).filter Nat.Prime) n x -
      (if n.Coprime x then Real.log x else 0) =
      -(if n.Coprime x then Real.log (remainingMidpointFactor Q x) else 0) := by
  by_cases hc : n.Coprime x
  · have he : ((Ioc Q (4*n)).filter Nat.Prime).filter (fun p => p ∣ x ∧ 2*p ≤ x) = selectedPrimes Q x := by
      ext p
      simp only [selectedPrimes,mem_filter,mem_Ioc,Nat.mem_primeFactors]
      constructor
      · rintro ⟨⟨⟨hQ,_⟩,hp⟩,hd,hp2⟩
        exact ⟨⟨hp,hd,hx.ne'⟩,hQ,hp2⟩
      · rintro ⟨⟨hp,hd,_⟩,hQ,hp2⟩
        exact ⟨⟨⟨hQ,(Nat.le_of_dvd hx hd).trans hcap⟩,hp⟩,hd,hp2⟩
    have hlog := (remaining_factor_log Q hx).2
    simp only [properPrimePriceAt,and_iff_right hc,if_pos hc]
    rw [show (∑ p ∈ (Ioc Q (4*n)).filter Nat.Prime,if p ∣ x then (if 2*p ≤ x then Real.log p else 0) else 0) =
      ∑ p ∈ selectedPrimes Q x,Real.log p by simp only [←he,sum_filter,ite_and]]
    linarith only [hlog]
  · simp [properPrimePriceAt,hc]

private theorem reflected_coprime {n x y : ℕ} (hs : x+y=6*n) : n.Coprime x ↔ n.Coprime y := by
  have transfer (a b : ℕ) (h : a+b=6*n) : n.gcd a ∣ n.gcd b := by
    have hd := Nat.gcd_dvd_left n a
    apply Nat.dvd_gcd hd
    rw [show b=6*n-a by omega]
    exact Nat.dvd_sub (hd.trans (dvd_mul_left n 6)) (Nat.gcd_dvd_right n a)
  have eqg := Nat.dvd_antisymm (transfer x y hs) (transfer y x (by omega))
  change n.gcd x=1 ↔ n.gcd y=1
  rw [eqg]

/-- Log ratio of the remaining left and right factors at the primitive
integer pairs reflected about 3n. -/
def oppositeFactorPrice (n Q : ℕ) : ℝ :=
  ∑ x ∈ (Ioo (3*n) (4*n)).filter (n.Coprime ·),
    Real.log ((remainingMidpointFactor Q (6*n-x):ℝ)/remainingMidpointFactor Q x)

/-- Centering the true large-factor price leaves the signed log ratio of
the two remaining integer factors, paired at every primitive midpoint. -/
theorem centered_price_of_opposite_factors {n : ℕ} (hn : 1 < n) (Q : ℕ) :
    largePrimeCofactorPrice n Q-reflectedCoprimePrice n = oppositeFactorPrice n Q := by
  unfold oppositeFactorPrice
  let S := (Ioc Q (4*n)).filter Nat.Prime
  let f (x : ℕ) := if n.Coprime x then Real.log (x:ℝ) else 0
  let r (x : ℕ) := if n.Coprime x then Real.log (remainingMidpointFactor Q x) else 0
  have hpref (T : ℕ) : (∑ x ∈ Ioc 0 T,f x)=∑ x ∈ (Icc 1 T).filter (n.Coprime ·),Real.log x := by
    rw [sum_filter,show Icc 1 T=Ioc 0 T by ext x; simp only [mem_Icc,mem_Ioc]; omega]
  have center : reflectedCoprimePrice n=(∑ x ∈ Ioc (3*n) (4*n),f x)-(∑ x ∈ Ioc (2*n) (3*n),f x) := by
    change (∑ x ∈ (Icc 1 (4*n)).filter (n.Coprime ·),Real.log x) -
      2*(∑ x ∈ (Icc 1 (3*n)).filter (n.Coprime ·),Real.log x) +
      (∑ x ∈ (Icc 1 (2*n)).filter (n.Coprime ·),Real.log x) = _
    simp only [←hpref]
    linarith only [sum_Ioc_consecutive f (Nat.zero_le (3*n)) (show 3*n ≤ 4*n by omega),
      sum_Ioc_consecutive f (Nat.zero_le (2*n)) (show 2*n ≤ 3*n by omega)]
  have inter (u v : ℕ) (hv : v ≤ 4*n) : (∑ x ∈ Ioc u v,properPrimePriceAt S n x) -
      (∑ x ∈ Ioc u v,f x) = -(∑ x ∈ Ioc u v,r x) := by
    rw [←sum_sub_distrib,←sum_neg_distrib]
    exact sum_congr rfl fun x h => price_at_primitive (lt_of_le_of_lt (Nat.zero_le u) (mem_Ioc.mp h).1) ((mem_Ioc.mp h).2.trans hv)
  have hcut (u v : ℕ) (huv : u < v) (he : r v=0) : (∑ x ∈ Ioc u v,r x) = ∑ x ∈ Ioo u v,r x := by
    have heq : Ioc u v=insert v (Ioo u v) := by ext x; simp only [mem_Ioc,mem_Ioo,mem_insert]; omega
    rw [heq,sum_insert (by simp),he,zero_add]
  have hend (k : ℕ) : r (k*n)=0 := by
    have hc : ¬n.Coprime (k*n) := by
      intro h
      have hd := Nat.dvd_gcd (dvd_refl n) (dvd_mul_left n k)
      rw [show n.gcd (k*n)=1 from h] at hd
      exact hn.ne' (Nat.dvd_one.mp hd)
    simp only [r,if_neg hc]
  have hre : (∑ y ∈ Ioo (2*n) (3*n),r y) = ∑ x ∈ Ioo (3*n) (4*n),r (6*n-x) := by
    apply sum_nbij' (fun y => 6*n-y) (fun x => 6*n-x)
    · intro y h; simp only [mem_Ioo] at h ⊢; omega
    · intro x h; simp only [mem_Ioo] at h ⊢; omega
    · intro y h; simp only [mem_Ioo] at h; omega
    · intro x h; simp only [mem_Ioo] at h; omega
    · intro y h; simp only [mem_Ioo] at h; rw [show 6*n-(6*n-y)=y by omega]
  rw [price_of_selected_factors,center]
  change ((∑ x ∈ Ioc (3*n) (4*n),properPrimePriceAt S n x) - _) - _ = _
  have hj := inter (3*n) (4*n) le_rfl
  have hk := inter (2*n) (3*n) (by omega)
  have heq : ((∑ x ∈ Ioc (3*n) (4*n),properPrimePriceAt S n x)-(∑ x ∈ Ioc (2*n) (3*n),properPrimePriceAt S n x)) -
      ((∑ x ∈ Ioc (3*n) (4*n),f x)-(∑ x ∈ Ioc (2*n) (3*n),f x)) =
      (∑ y ∈ Ioc (2*n) (3*n),r y)-(∑ x ∈ Ioc (3*n) (4*n),r x) := by linarith only [hj,hk]
  rw [heq,hcut _ _ (by omega) (hend 3),hcut _ _ (by omega) (hend 4),hre,←sum_sub_distrib,sum_filter]
  apply sum_congr rfl
  intro x h
  obtain ⟨hl,hu⟩ := mem_Ioo.mp h
  have hy : 0 < 6*n-x := by omega
  have hc := reflected_coprime (n:=n) (x:=6*n-x) (y:=x) (by omega)
  rw [Real.log_div (Nat.cast_ne_zero.mpr (remaining_factor_log Q hy).1.ne')
    (Nat.cast_ne_zero.mpr (remaining_factor_log Q (by omega : 0 < x)).1.ne')]
  simp only [r,hc]
  split_ifs <;> simp

/-- The opposite residual factors give the prime midpoint up to the
small Mangoldt mass and the proper-power mass at the common cutoff. -/
theorem opposite_factor_midpoint_error {n Q : ℕ} (hn : 1 < n) (hQ : Q ≤ 2*n) :
    |oppositeFactorPrice n Q-primeMidpointPrice n| ≤
      (7*(Q:ℝ)+(Chebyshev.psi (4*n:ℕ)-Chebyshev.theta (4*n:ℕ)))*squarefreeDivisorMass n := by
  let S := (Ioc Q (4*n)).filter (fun q => ¬q.Prime)
  have hS : S ⊆ (Ioc 0 (4*n)).filter (fun q => ¬q.Prime) := by
    intro q h
    obtain ⟨hi,hp⟩ := mem_filter.mp h
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hi
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.zero_le Q).trans_lt hl,hu⟩,hp⟩
  rw [←centered_price_of_opposite_factors hn,large_prime_cofactor_price_exact (by omega) hQ,abs_neg,add_mul]
  exact (abs_add_le _ _).trans (add_le_add (abs_small_midpoint_factor_price (by omega) Q)
    (midpoint_selected_proper_power_price (by omega) S hS))

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
