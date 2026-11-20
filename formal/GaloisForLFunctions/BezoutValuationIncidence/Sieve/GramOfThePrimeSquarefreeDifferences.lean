import GaloisForLFunctions.BezoutValuationIncidence.CoprimeMobiusSignAndEvenDilationMeans
import GaloisForLFunctions.RHTower.Sieve.SquarefreeIndicator
import GaloisForLFunctions.RHTower.Sieve.ElementaryHarmonicBounds

/-!
# Gram matrix of density-canceling squarefree rows

The difference of a squarefree Dirichlet section and its prime
dilation has coefficients v_p(n)=μ²(n)−p 1_{p∣n} μ²(n/p). Although
each row has mean zero, two distinct prime rows have positive
limiting correlation. Their entire Gram matrix is a positive
diagonal plus one outer product. This evaluates the quadratic Gram
expansion used by Gabet, Ferreira Da Costa and Lee in Proposition 2.4
for the arithmetic differences produced by Abel summation.
-/

noncomputable section
open Finset Filter
open scoped ArithmeticFunction.Moebius Topology
open _root_.RHTower.Sieve (squarefreeDensity moebius_sq_eq_indicator)
open GaloisForLFunctions.TransHorizonIncidenceMechanics (sum_Icc_filter_dvd_eq_sum_Icc_div)
namespace GaloisForLFunctions.BezoutValuationIncidence

private def atom (n : ℕ) : ℝ := ((μ n:ℤ):ℝ)^2
private theorem atom_sq (n : ℕ) : atom n*atom n=atom n := by
  rw [atom,moebius_sq_eq_indicator];split <;>simp
private theorem coprime_atom_sq (Q n : ℕ) :
    coprimeSquarefreeIndicator Q n ^ 2=coprimeSquarefreeIndicator Q n := by
  unfold coprimeSquarefreeIndicator
  split_ifs <;> (try simp only [moebius_sq_eq_indicator]) <;> (try split_ifs) <;> simp

/-- Coefficient on the multiples of d of the d-dilated squarefree row. -/
def dilatedSquarefreeAtom (d n : ℕ) : ℝ := if d∣n then atom (n/d) else 0

/-- The coefficient of the difference that cancels the natural density at p. -/
def primeSquarefreeDifference (p n : ℕ) := dilatedSquarefreeAtom 1 n-(p:ℝ)*dilatedSquarefreeAtom p n

private theorem product_atom (a b n : ℕ) :
    atom (a*n)*atom (b*n)=atom a*atom b*coprimeSquarefreeIndicator (a*b) n := by
  have h := congrArg (fun u : ℝ => u^2) (moebius_dilation_pair_eq_coprimeSquarefreeIndicator a b n)
  simpa only [atom,mul_pow,coprime_atom_sq] using h

private theorem prefix_dilated {a b : ℕ} (ha : 0<a) (hb : 0<b) (hab : a.Coprime b) (N : ℕ) :
    (∑ n∈Icc 1 N,dilatedSquarefreeAtom a n*dilatedSquarefreeAtom b n)=
      atom a*atom b*coprimeSquarefreeCount (a*b) (N/(a*b)) := by
  classical
  have hf (n : ℕ) : dilatedSquarefreeAtom a n*dilatedSquarefreeAtom b n =
      if a*b∣n then atom (n/a)*atom (n/b) else 0 := by
    by_cases h1 : a∣n
    · by_cases h2 : b∣n
      · simp [dilatedSquarefreeAtom,h1,h2,hab.mul_dvd_of_dvd_of_dvd h1 h2]
      · have hne : ¬a*b∣n := fun h => h2 ((dvd_mul_left b a).trans h)
        simp [dilatedSquarefreeAtom,h2,hne]
    · have hne : ¬a*b∣n := fun h => h1 ((dvd_mul_right a b).trans h)
      simp [dilatedSquarefreeAtom,h1,hne]
  simp_rw [hf]
  rw [←sum_filter,sum_Icc_filter_dvd_eq_sum_Icc_div (Nat.mul_pos ha hb)]
  unfold coprimeSquarefreeCount
  rw [Finset.mul_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [show a*b*n=a*(b*n) by ring,Nat.mul_div_cancel_left _ ha,
    show a*(b*n)=b*(a*n) by ring,Nat.mul_div_cancel_left _ hb,mul_comm (atom (b*n)),product_atom]

private theorem prefix_square {a : ℕ} (ha : 0<a) (N : ℕ) :
    (∑ n∈Icc 1 N,dilatedSquarefreeAtom a n*dilatedSquarefreeAtom a n)=
      coprimeSquarefreeCount 1 (N/a) := by
  have h (n : ℕ) : dilatedSquarefreeAtom a n*dilatedSquarefreeAtom a n =
      if a∣n then atom (n/a) else 0 := by
    unfold dilatedSquarefreeAtom;split_ifs <;> simp [atom_sq]
  simp_rw [h]
  rw [←sum_filter,sum_Icc_filter_dvd_eq_sum_Icc_div ha]
  simp only [Nat.mul_div_cancel_left _ ha,coprimeSquarefreeCount,coprimeSquarefreeIndicator,
    Nat.coprime_one_left_eq_true,if_true,atom]

private theorem mean_scaled {d Q : ℕ} (hd : 0<d) (hQ : 0<Q) :
    Tendsto (fun x : ℝ => coprimeSquarefreeCount Q (⌊x⌋₊/d)/x) atTop
      (𝓝 (coprimeSquarefreeDensity Q/d)) := by
  have hp : 0<(d:ℝ) := Nat.cast_pos.mpr hd
  have h := (tendsto_coprimeSquarefreeMean_positive_modulus ⟨Q,hQ⟩).comp
    (show Tendsto (fun x : ℝ => x/d) atTop atTop by
      simpa only [div_eq_mul_inv,id_eq] using tendsto_id.atTop_mul_const (inv_pos.mpr hp))
  apply (h.div_const (d:ℝ)).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  dsimp only [Function.comp_apply,coprimeSquarefreeMean]
  rw [Nat.floor_div_natCast,div_div,div_mul_cancel₀ _ hp.ne',PNat.mk_coe]

private def scalarMean (a b : ℕ → ℝ) (x : ℝ) := (∑ n∈Icc 1 ⌊x⌋₊,a n*b n)/x

private theorem mean_distinct {a b : ℕ} (ha : 0<a) (hb : 0<b) (hc : a.Coprime b) :
    Tendsto (scalarMean (dilatedSquarefreeAtom a) (dilatedSquarefreeAtom b)) atTop
      (𝓝 (atom a*atom b*(coprimeSquarefreeDensity (a*b)/(a*b:ℕ)))) := by
  have h := (mean_scaled (d:=a*b) (Q:=a*b) (Nat.mul_pos ha hb) (Nat.mul_pos ha hb)).const_mul
    (atom a*atom b)
  show Tendsto (fun x => scalarMean (dilatedSquarefreeAtom a) (dilatedSquarefreeAtom b) x) _ _
  simpa only [scalarMean,prefix_dilated ha hb hc,mul_div_assoc] using h

private theorem mean_same {a : ℕ} (ha : 0<a) :
    Tendsto (scalarMean (dilatedSquarefreeAtom a) (dilatedSquarefreeAtom a)) atTop
      (𝓝 (squarefreeDensity/a)) := by
  show Tendsto (fun x => scalarMean (dilatedSquarefreeAtom a) (dilatedSquarefreeAtom a) x) _ _
  simpa only [scalarMean,prefix_square ha,coprimeSquarefreeDensity_one] using
    mean_scaled (d:=a) (Q:=1) ha Nat.zero_lt_one

private theorem density_prime (p : ℕ) (hp : p.Prime) :
    coprimeSquarefreeDensity p=(p:ℝ)/((p:ℝ)+1)*squarefreeDensity := by
  simpa only [mul_one,coprimeSquarefreeDensity_one] using
    coprimeSquarefreeDensity_prime_mul (Q:=1) hp (by simpa using hp.not_dvd_one) one_ne_zero

private theorem mean_prime_unit {p : ℕ} (hp : p.Prime) :
    Tendsto (scalarMean (dilatedSquarefreeAtom p) (dilatedSquarefreeAtom 1)) atTop
      (𝓝 (squarefreeDensity/(p+1:ℝ))) := by
  have h := mean_distinct hp.pos Nat.zero_lt_one (Nat.coprime_one_right p)
  simp only [atom,ArithmeticFunction.moebius_apply_prime hp,ArithmeticFunction.moebius_apply_one,
    Int.cast_neg,Int.cast_one,neg_one_sq,one_pow,one_mul,mul_one,density_prime p hp] at h
  convert h using 2
  have hpR : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
  field_simp [hpR.ne',(by positivity : (p:ℝ)+1≠0)] <;> ring

private theorem scalarMean_comm (a b : ℕ → ℝ) : scalarMean a b=scalarMean b a := by
  funext x;unfold scalarMean;congr 1;exact sum_congr rfl fun n _ => mul_comm _ _

private theorem expand_reading (p q : ℕ) (x : ℝ) :
    scalarMean (primeSquarefreeDifference p) (primeSquarefreeDifference q) x =
      scalarMean (dilatedSquarefreeAtom 1) (dilatedSquarefreeAtom 1) x -
      (p:ℝ)*scalarMean (dilatedSquarefreeAtom p) (dilatedSquarefreeAtom 1) x -
      (q:ℝ)*scalarMean (dilatedSquarefreeAtom 1) (dilatedSquarefreeAtom q) x +
      (p:ℝ)*q*scalarMean (dilatedSquarefreeAtom p) (dilatedSquarefreeAtom q) x := by
  simp only [scalarMean,primeSquarefreeDifference]
  simp_rw [show ∀ a b c d P Q:ℝ,(a-P*b)*(c-Q*d)=a*c-P*(b*c)-Q*(a*d)+(P*Q)*(b*d) by intros;ring]
  simp only [sum_add_distrib,sum_sub_distrib,←Finset.mul_sum,sub_div,add_div,mul_div_assoc]

/-- The full natural-density Gram between distinct primes is a rank-one
kernel, even though both arithmetic rows have mean zero. -/
theorem prime_squarefree_cross_mean {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q) :
    Tendsto (fun x : ℝ => (∑ n∈Icc 1 ⌊x⌋₊,primeSquarefreeDifference p n*primeSquarefreeDifference q n)/x)
      atTop (𝓝 (squarefreeDensity/(((p:ℝ)+1)*(q+1:ℝ)))) := by
  have h₁ := mean_same (a:=1) Nat.zero_lt_one
  rw [Nat.cast_one,div_one] at h₁
  have hp₁ := mean_prime_unit hp
  have hq₁ := mean_prime_unit hq
  rw [scalarMean_comm] at hq₁
  have hc := hp.coprime_iff_not_dvd.mpr (fun h => hne ((Nat.dvd_prime hq).mp h |>.resolve_left hp.ne_one))
  have h := mean_distinct hp.pos hq.pos hc
  have hb : coprimeSquarefreeDensity (p*q)=(p:ℝ)/(p+1:ℝ)*((q:ℝ)/(q+1:ℝ)*squarefreeDensity) := by
    rw [coprimeSquarefreeDensity_prime_mul hp (hp.coprime_iff_not_dvd.mp hc) hq.ne_zero,density_prime q hq]
  simp only [atom,ArithmeticFunction.moebius_apply_prime hp,ArithmeticFunction.moebius_apply_prime hq,
    Int.cast_neg,Int.cast_one,neg_one_sq,one_mul,hb,Nat.cast_mul] at h
  have H := ((h₁.sub (hp₁.const_mul (p:ℝ))).sub (hq₁.const_mul (q:ℝ))).add (h.const_mul ((p:ℝ)*q))
  have hpR : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
  have hqR : 0<(q:ℝ) := Nat.cast_pos.mpr hq.pos
  have he : squarefreeDensity-p*(squarefreeDensity/(p+1:ℝ))-q*(squarefreeDensity/(q+1:ℝ))+
      (p:ℝ)*q*((p:ℝ)/(p+1:ℝ)*((q:ℝ)/(q+1:ℝ)*squarefreeDensity)/(p*q:ℝ)) =
        squarefreeDensity/((p+1:ℝ)*(q+1:ℝ)) := by
    field_simp [hpR.ne',hqR.ne',(by positivity : (p:ℝ)+1≠0),(by positivity : (q:ℝ)+1≠0)] <;> ring
  rw [he] at H
  exact H.congr' (.of_forall fun x => (expand_reading p q x).symm)

/-- The diagonal retains the contribution of the p²-divisible sites.
At large p its mean square grows linearly in the prime. -/
theorem prime_squarefree_self_mean {p : ℕ} (hp : p.Prime) :
    Tendsto (fun x : ℝ => (∑ n∈Icc 1 ⌊x⌋₊,primeSquarefreeDifference p n^2)/x)
      atTop (𝓝 (squarefreeDensity*((p:ℝ)^2+1)/((p:ℝ)+1))) := by
  have h₁ := mean_same (a:=1) Nat.zero_lt_one
  rw [Nat.cast_one,div_one] at h₁
  have h2 := mean_prime_unit hp
  have h3 := h2
  rw [scalarMean_comm] at h3
  have h4 := mean_same hp.pos
  have H := ((h₁.sub (h2.const_mul (p:ℝ))).sub (h3.const_mul (p:ℝ))).add (h4.const_mul ((p:ℝ)*p))
  have hpR : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
  have he : squarefreeDensity-p*(squarefreeDensity/(p+1:ℝ))-p*(squarefreeDensity/(p+1:ℝ))+
      (p:ℝ)*p*(squarefreeDensity/p) = squarefreeDensity*((p:ℝ)^2+1)/(p+1:ℝ) := by
    field_simp [hpR.ne',(by positivity : (p:ℝ)+1≠0)] <;> ring
  rw [he] at H
  apply H.congr'
  exact .of_forall fun x => (expand_reading p p x).symm.trans (by simp only [scalarMean,pow_two])


/-- Residual diagonal after subtracting the common rank-one component. -/
def primeDifferenceVariance (p : ℕ) : ℝ :=
  squarefreeDensity*(p:ℝ)*((p:ℝ)^2+p+1)/((p:ℝ)+1)^2

private theorem gram_entry {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    Tendsto (scalarMean (primeSquarefreeDifference p) (primeSquarefreeDifference q)) atTop
      (𝓝 (squarefreeDensity/((p+1:ℝ)*(q+1:ℝ))+(if p=q then primeDifferenceVariance p else 0))) := by
  by_cases h : p=q
  · subst q
    rw [if_pos rfl]
    have hh := prime_squarefree_self_mean hp
    have hv : squarefreeDensity/(((p:ℝ)+1)*((p:ℝ)+1)) + primeDifferenceVariance p =
        squarefreeDensity*((p:ℝ)^2+1)/((p:ℝ)+1) := by
      unfold primeDifferenceVariance
      have h1 : (p:ℝ)+1 ≠ 0 := by positivity
      field_simp
      ring
    rw [hv]
    refine hh.congr' (.of_forall fun x => ?_)
    simp only [scalarMean, pow_two]
  · rw [if_neg h,add_zero];exact prime_squarefree_cross_mean hp hq h

private theorem gram_sum (P : Finset ℕ) (w : ℕ → ℝ) :
    (∑ p∈P, ∑ q∈P, w p*w q*(squarefreeDensity/((p+1:ℝ)*(q+1:ℝ))+
      if p=q then primeDifferenceVariance p else 0)) =
        squarefreeDensity*(∑ p∈P,w p/(p+1:ℝ))^2+∑ p∈P,w p^2*primeDifferenceVariance p := by
  have hentry (p q : ℕ) :
      w p*w q*(squarefreeDensity/((p+1:ℝ)*(q+1:ℝ))+
        if p=q then primeDifferenceVariance p else 0) =
      squarefreeDensity*((w p/(p+1:ℝ))*(w q/(q+1:ℝ)))+
        (if q=p then w p^2*primeDifferenceVariance p else 0) := by
    by_cases hh : p=q
    · subst q;rw [if_pos rfl,if_pos rfl,div_mul_div_comm];ring
    · simp only [if_neg hh,if_neg (Ne.symm hh),add_zero,mul_zero];rw [div_mul_div_comm];ring
  simp_rw [hentry,Finset.sum_add_distrib,sum_ite_eq']
  congr 1
  · rw [sq,Finset.sum_mul_sum,Finset.mul_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
  · exact sum_congr rfl fun p hp => if_pos hp

/-- The Gram law for every finite signed combination of prime rows.
Its sole cross-prime cost is the square of one explicit linear statistic. -/
theorem prime_squarefree_portfolio_mean (P : Finset ℕ) (hP : ∀ p∈P,p.Prime) (w : ℕ → ℝ) :
    Tendsto (fun x : ℝ => (∑ n∈Icc 1 ⌊x⌋₊,(∑ p∈P,w p*primeSquarefreeDifference p n)^2)/x)
      atTop (𝓝 (squarefreeDensity*(∑ p∈P,w p/(p+1:ℝ))^2+∑ p∈P,w p^2*primeDifferenceVariance p)) := by
  have hh := tendsto_finsetSum P (fun p hp => tendsto_finsetSum P (fun q hq =>
    (gram_entry (hP p hp) (hP q hq)).const_mul (w p*w q)))
  rw [gram_sum] at hh
  apply hh.congr'
  refine .of_forall fun x => ?_
  simp only [scalarMean,←mul_div_assoc,←Finset.sum_div,Finset.mul_sum]
  congr 1
  calc
    _ = ∑ n∈Icc 1 ⌊x⌋₊,∑ p∈P,∑ q∈P,w p*w q*(primeSquarefreeDifference p n*primeSquarefreeDifference q n) := by
      exact (sum_congr rfl fun p _ => Finset.sum_comm).trans Finset.sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro n _
      rw [pow_two,Finset.sum_mul]
      apply sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
      exact sum_congr rfl fun q _ => by ring


/-- Limiting mean-square norm for the prime differences. -/
def primeDifferenceEnergy (P : Finset ℕ) (w : ℕ → ℝ) :=
  squarefreeDensity*(∑ p∈P,w p/(p+1:ℝ))^2 + ∑ p∈P,w p^2*primeDifferenceVariance p

private def localEnergy (w : ℕ → ℝ) (p : ℕ) := (p:ℝ)*w p/(p+1:ℝ)

private theorem prime_cost_identity (P : Finset ℕ) (w : ℕ → ℝ) :
    squarefreeDensity*(∑ p∈P,(p:ℝ)*w p^2)-primeDifferenceEnergy P w =
      squarefreeDensity*((∑ p∈P,(localEnergy w p)^2)-(∑ p∈P,w p/(p+1:ℝ))^2) := by
  have h (p : ℕ) : squarefreeDensity*((p:ℝ)*w p^2)-w p^2*primeDifferenceVariance p=
      squarefreeDensity*(localEnergy w p)^2 := by
    unfold primeDifferenceVariance localEnergy
    field_simp [(by positivity : (p:ℝ)+1≠0)] <;> ring
  have hh := sum_congr (s₁:=P) rfl (fun p _ => h p)
  rw [sum_sub_distrib,←mul_sum,←mul_sum] at hh
  unfold primeDifferenceEnergy
  linear_combination hh

private theorem prime_reciprocal_squares (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) :
    (∑ p∈P,(p:ℝ)⁻¹^2)≤1/2 := by
  have hsum := _root_.RHTower.Sieve.sum_inv_sq_odd_le (s:=P.erase 2) (by
    intro p h
    obtain ⟨hne,hpP⟩ := mem_erase.mp h
    have hprime := hp p hpP
    exact ⟨(show 3≤p by have := hprime.two_le;omega),
      fun hd => hne (((Nat.dvd_prime hprime).mp hd).resolve_left (by norm_num) |>.symm)⟩)
  simp only [one_div,inv_pow] at hsum
  by_cases ht : 2∈P
  · rw [←sum_erase_add _ _ ht]
    norm_num only [Nat.cast_ofNat,inv_pow] at *
    linarith only [hsum]
  · rw [erase_eq_of_notMem ht] at hsum
    simpa only [inv_pow] using hsum.trans (by norm_num : (4:ℝ)⁻¹≤1/2)

/-- Sharp weighted loss of squared norm. Equality is attained by
w(p)=(p+1)/p², simultaneously at every finite set of primes. -/
theorem prime_difference_energy_loss (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) (w : ℕ → ℝ) :
    squarefreeDensity*(1-∑ p∈P,(p:ℝ)⁻¹^2)*(∑ p∈P,((p:ℝ)*w p/(p+1:ℝ))^2) ≤
      squarefreeDensity*(∑ p∈P,(p:ℝ)*w p^2)-primeDifferenceEnergy P w := by
  have hd : 0 ≤ squarefreeDensity := by rw [_root_.RHTower.Sieve.squarefreeDensity_eq];positivity
  have H := Finset.sum_mul_sq_le_sq_mul_sq P (fun p:ℕ => (p:ℝ)⁻¹) (localEnergy w)
  have hsum : (∑ p∈P,(p:ℝ)⁻¹*localEnergy w p)=∑ p∈P,w p/(p+1:ℝ) := by
    refine sum_congr rfl fun p hpP => ?_
    unfold localEnergy
    field_simp [Nat.cast_ne_zero.mpr (hp p hpP).ne_zero]
  rw [hsum] at H
  rw [prime_cost_identity,mul_assoc]
  exact mul_le_mul_of_nonneg_left (by dsimp only [localEnergy] at *;linarith only [H]) hd

theorem prime_difference_loss_attained (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) :
    let w := fun p:ℕ => ((p:ℝ)+1)/p^2
    squarefreeDensity*(∑ p∈P,(p:ℝ)*w p^2)-primeDifferenceEnergy P w =
      squarefreeDensity*(1-∑ p∈P,(p:ℝ)⁻¹^2)*(∑ p∈P,((p:ℝ)*w p/(p+1:ℝ))^2) := by
  dsimp only
  rw [prime_cost_identity]
  have he (p:ℕ) (hpP : p∈P) : localEnergy (fun p:ℕ => ((p:ℝ)+1)/p^2) p=(p:ℝ)⁻¹ := by
    unfold localEnergy
    field_simp [Nat.cast_ne_zero.mpr (hp p hpP).ne_zero,(by positivity : (p:ℝ)+1≠0)]
  have hv (p:ℕ) (_ : p∈P) : ((p:ℝ)+1)/p^2/(p+1:ℝ)=(p:ℝ)⁻¹^2 := by
    rw [inv_pow];field_simp [(by positivity : (p:ℝ)+1≠0)]
  have hl : ∀ p ∈ P, localEnergy (fun p:ℕ => ((p:ℝ)+1)/p^2) p ^ 2 = (p:ℝ)⁻¹^2 :=
    fun p hp => by rw [he p hp]
  have hr : ∀ p ∈ P, ((p:ℝ) * (((p:ℝ)+1)/(p:ℝ)^2) / ((p:ℝ)+1))^2 = (p:ℝ)⁻¹^2 :=
    fun p hp => by rw [← he p hp]; rfl
  rw [sum_congr rfl hl,sum_congr rfl hv,sum_congr rfl hr]
  ring

/-- Uniform Riesz bounds for the infinite family of rows normalized
by √p, expressed without denominators in the coefficients. -/
theorem prime_difference_riesz_bounds (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) (w : ℕ → ℝ) :
    (7/9:ℝ)*squarefreeDensity*(∑ p∈P,(p:ℝ)*w p^2) ≤ primeDifferenceEnergy P w ∧
      primeDifferenceEnergy P w ≤ squarefreeDensity*(∑ p∈P,(p:ℝ)*w p^2) := by
  have hd : 0 ≤ squarefreeDensity := by rw [_root_.RHTower.Sieve.squarefreeDensity_eq];positivity
  constructor
  · have h (p:ℕ) (hpP:p∈P) : (7/9:ℝ)*squarefreeDensity*((p:ℝ)*w p^2)≤w p^2*primeDifferenceVariance p := by
      have h2 : (2:ℝ)≤p := by exact_mod_cast (hp p hpP).two_le
      have he : (7/9:ℝ)≤((p:ℝ)^2+p+1)/(p+1:ℝ)^2 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith only [mul_nonneg (sub_nonneg.mpr h2) (by linarith only [h2] : 0≤2*(p:ℝ)-1)]
      have h' := mul_le_mul_of_nonneg_right he (show 0 ≤ squarefreeDensity*p*w p^2 by positivity)
      unfold primeDifferenceVariance
      exact ((by ring : (7/9:ℝ)*squarefreeDensity*((p:ℝ)*w p^2) =
        (7/9:ℝ)*(squarefreeDensity*p*w p^2)).trans_le h').trans_eq (by ring)
    have hh := sum_le_sum h
    rw [←mul_sum] at hh
    exact hh.trans (le_add_of_nonneg_left (mul_nonneg hd (sq_nonneg _)))
  · have hh := prime_difference_energy_loss P hp w
    have hr := prime_reciprocal_squares P hp
    have hn : 0≤1-∑ p∈P,(p:ℝ)⁻¹^2 := by linarith
    have hs : 0 ≤ ∑ p∈P,((p:ℝ)*w p/(p+1:ℝ))^2 := sum_nonneg fun p _ => sq_nonneg _
    linarith only [hh,mul_nonneg (mul_nonneg hd hn) hs]


end GaloisForLFunctions.BezoutValuationIncidence
