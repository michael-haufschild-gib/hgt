import GaloisForLFunctions.RHTower.Sieve.PrimeCosineSum
import GaloisForLFunctions.RHTower.SquarefreeCriticalNormalCone

/-!
# Uniform finite Euler comparison across the one-line

For every bounded real logarithmic displacement, the ORIGINAL finite Euler
product is uniformly comparable with inverse zeta at `1+1/log N+i*tau`.
The frequency is unrestricted, including frequencies depending on N.

Both real logarithms reduce to the same finite prime cosine sum. The actual
prime tail at the right abscissa, Mertens' head shift, and a summable complex
logarithm remainder bound their difference. This supplies uniform arithmetic
control for mixed Mellin transfer; it does not exchange a growing source
limit with the actual moving physical integral.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RHTower.BAGTrace
open Sieve

private def primeTailConstant : ℝ :=
  2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2

private theorem logN_ge {N : ℕ} (hN : 3 ≤ N) : 1 ≤ Real.log N := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hexp : Real.exp 1 ≤ (N : ℝ) := by linarith [Real.exp_one_lt_d9]
  have h := Real.log_le_log (Real.exp_pos 1) hexp
  simpa using h

private theorem cosine_zeta_comparison {N : ℕ} (hN : 3 ≤ N) (t : ℝ) :
    |Real.log ‖riemannZeta (((1+1/Real.log N : ℝ) : ℂ)+(t : ℂ)*Complex.I)‖ -
      ∑ p ∈ Nat.primesLE N, Real.cos (t*Real.log p)/(p : ℝ)| ≤
        Real.pi^2/6 + primeTailConstant + (1+Real.log 4) := by
  have hL := logN_ge hN
  have hL0 : 0 < Real.log N := by linarith
  let σ : ℝ := 1+1/Real.log N
  have hσ : 1 < σ := by
    have : 0 < 1/Real.log N := by positivity
    dsimp [σ]; linarith
  have hz := abs_log_norm_riemannZeta_sub_tsum_re_le
    (s := (σ : ℂ)+(t : ℂ)*Complex.I) (by simpa using hσ)
  have hsquare : (∑' p : Nat.Primes, ‖((p : ℕ) : ℂ)^(-((σ : ℂ)+(t : ℂ)*Complex.I))‖^2)
      ≤ Real.pi^2/6 := by
    rw [tsum_norm_sq_eq]
    simpa using (tsum_prime_rpow_le hσ.le)
  have hz' := hz.trans hsquare
  have hsplit := tsum_re_prime_cpow_split (z := N) (t := t) hσ
  have htail := abs_tsum_prime_tail_re_le (z := N) (t := t) hσ
  have htailC := tsum_primeTailTerm_le hN
  have hshift := abs_sum_weight_shift_le (z := N) (by omega) hσ.le
    (w := fun p => Real.cos (t*Real.log p)) (fun p => Real.abs_cos_le_one _)
  have hident : (∑ p ∈ Nat.primesLE N, Real.cos (t*Real.log p)/(p : ℝ)) =
      (∑ p ∈ Nat.primesLE N,(p : ℝ)^(-σ)*Real.cos (t*Real.log p))+
      ∑ p ∈ Nat.primesLE N,Real.cos (t*Real.log p)*(1/(p : ℝ)-(p : ℝ)^(-σ)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hshiftC : (σ-1)*(Real.log N+Real.log 4) ≤ 1+Real.log 4 := by
    have he : (σ-1)*(Real.log N+Real.log 4)=1+Real.log 4/Real.log N := by
      dsimp [σ]; field_simp; ring
    rw [he]
    have hdiv : Real.log 4/Real.log N ≤ Real.log 4 := by
      rw [div_le_iff₀ hL0]
      nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
    linarith
  change |_ - _| ≤ _
  rw [hident]
  have hzbound := abs_le.mp hz'
  have htbound := abs_le.mp htail
  have hsbound := abs_le.mp hshift
  change _ ≤ primeTailConstant at htailC
  change _ ≤ ∑' p, primeTailTerm N σ p at htail
  apply abs_le.mpr
  constructor <;> linarith

private def q (a t : ℝ) (N p : ℕ) : ℂ :=
  Complex.exp ((-1-(a/Real.log N : ℝ)-(t : ℂ)*Complex.I)*(Real.log p : ℂ))

private theorem q_cpow (a t : ℝ) (N : ℕ) {p : ℕ} (hp : 0<p) :
    q a t N p=(p : ℂ)^(-1-(a/Real.log N : ℝ)-(t : ℂ)*Complex.I) := by
  rw [q,Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hp.ne')]
  have hpR : (0 : ℝ)<p := by exact_mod_cast hp
  rw [show (p : ℂ)=((p : ℝ) : ℂ) by simp,← Complex.ofReal_log hpR.le]
  congr 1
  ring

private theorem q_norm (a t : ℝ) (N : ℕ) {p : ℕ} (hp : 2≤p) :
    ‖q a t N p‖=radialNome (-a/(2*Real.log N)) p := by
  rw [q,Complex.norm_exp,radialNome_eq_exp hp]
  congr 1
  simp only [Complex.mul_re,Complex.sub_re,Complex.neg_re,Complex.I_re,Complex.I_im,
    Complex.one_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  ring

private theorem exp_difference (x : ℝ) : |Real.exp x-1| ≤ |x| * Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 1
  have h' : ‖Complex.exp (x : ℂ)-1‖ ≤ |x| * Real.exp |x| := by simpa using h
  have he : Complex.exp (x : ℂ)-1=((Real.exp x-1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub,Complex.ofReal_exp,Complex.ofReal_one]
  rw [he,Complex.norm_real,Real.norm_eq_abs] at h'
  exact h'

private theorem q_shift {A a : ℝ} (hA : |a| ≤ A) {N p : ℕ}
    (hN : 3≤N) (hp : 2≤p) (hpN : p≤N) (t : ℝ) :
    ‖q a t N p-q 0 t N p‖ ≤
      A*Real.exp A/Real.log N*(Real.log p/(p : ℝ)) := by
  have hL := logN_ge hN
  have hL0 : 0<Real.log N := by linarith
  have hp0 : (0 : ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have hlp : 0≤Real.log p := Real.log_nonneg (by exact_mod_cast (show 1≤p by omega))
  have hlogle : Real.log p≤Real.log N := Real.log_le_log hp0 (by exact_mod_cast hpN)
  have hA0 : 0≤A := (abs_nonneg a).trans hA
  let x : ℝ := -a/Real.log N*Real.log p
  have hx : |x|=|a|/Real.log N*Real.log p := by
    simp [x,abs_mul,abs_div,abs_of_pos hL0,abs_of_nonneg hlp]
  have hxA : |x|≤A := by
    rw [hx]
    calc |a|/Real.log N*Real.log p ≤ A/Real.log N*Real.log p := by gcongr
         _ ≤ A/Real.log N*Real.log N := by gcongr
         _ = A := by field_simp
  have he : q a t N p=q 0 t N p*(Real.exp x : ℂ) := by
    rw [q,q,Complex.ofReal_exp,← Complex.exp_add]
    congr 1
    dsimp [x]
    push_cast
    ring
  have hq0 : ‖q 0 t N p‖=1/(p : ℝ) := by
    rw [q_norm _ _ _ hp]
    simp only [neg_zero,zero_div,radialNome_zero hp,one_div]
  rw [he,show q 0 t N p*(Real.exp x : ℂ)-q 0 t N p =
    q 0 t N p*((Real.exp x : ℂ)-1) by ring,norm_mul,hq0]
  have hexp : ‖(Real.exp x : ℂ)-1‖ ≤ A/Real.log N*Real.log p*Real.exp A := by
    have hh := exp_difference x
    calc ‖(Real.exp x : ℂ)-1‖ = |Real.exp x-1| := by norm_cast
         _ ≤ (|a|/Real.log N*Real.log p)*Real.exp |x| := by simpa only [hx] using hh
         _ ≤ (A/Real.log N*Real.log p)*Real.exp A := by gcongr
  calc 1/(p : ℝ)*‖(Real.exp x : ℂ)-1‖ ≤
      1/(p : ℝ)*(A/Real.log N*Real.log p*Real.exp A) := by gcongr
       _ = _ := by ring

private theorem q_zero_re (N : ℕ) {p : ℕ} (hp : 0<p) (t : ℝ) :
    (q 0 t N p).re=Real.cos (t*Real.log p)/(p : ℝ) := by
  rw [q_cpow _ _ _ hp]
  simp only [zero_div,Complex.ofReal_zero,sub_zero]
  rw [show (-1-(t : ℂ)*Complex.I)= -((1 : ℝ)+(t : ℂ)*Complex.I) by push_cast; ring,
    re_natCast_cpow_neg hp]
  simp only [Real.rpow_neg_one,inv_mul_eq_div]

private def remainderTotal : ℝ := ∑' n : ℕ,(n : ℝ)^(-(3/2) : ℝ)

private theorem remainder_summable : Summable (fun n : ℕ => (n : ℝ)^(-(3/2) : ℝ)) := by
  rw [Real.summable_nat_rpow]
  norm_num

private theorem log_error {w : ℂ} (hw : ‖w‖≤3/4) :
    |Real.log ‖1-w‖+w.re| ≤ 2*‖w‖^2 := by
  have h := norm_neg_log_one_sub_sub_self_le (show ‖w‖<1 by linarith)
  have hden : 0<1-‖w‖ := by linarith
  have hinv : (1-‖w‖)⁻¹ ≤ (4 : ℝ) := by
    rw [inv_le_comm₀ hden (by norm_num)]
    linarith
  have hreal := Complex.abs_re_le_norm (-Complex.log (1-w)-w)
  simp only [Complex.sub_re,Complex.neg_re,Complex.log_re] at hreal
  have hsign : |-Real.log ‖1-w‖-w.re|=|Real.log ‖1-w‖+w.re| := by
    rw [show -Real.log ‖1-w‖-w.re= -(Real.log ‖1-w‖+w.re) by ring,abs_neg]
  rw [hsign] at hreal
  nlinarith [mul_le_mul_of_nonneg_left hinv (sq_nonneg ‖w‖)]

private theorem q_nonzero (a t : ℝ) (N : ℕ) {p : ℕ} (hp : 2≤p)
    (ha : |a/(2*Real.log N)|≤1/8) : 1-q a t N p ≠ 0 := by
  have hnorm : ‖q a t N p‖≤3/4 := by
    rw [q_norm _ _ _ hp]
    apply radialNome_le hp
    simpa only [neg_div,abs_neg] using ha
  intro he
  have heq := sub_eq_zero.mp he
  rw [← heq,norm_one] at hnorm
  norm_num at hnorm

private theorem log_product_comparison {A a : ℝ} (hA : |a|≤A) {N : ℕ}
    (hN : 3≤N) (ha : |a/(2*Real.log N)|≤1/8) (t : ℝ) :
    |Real.log ‖∏ p ∈ Nat.primesLE N,(1-q a t N p)‖+
      ∑ p ∈ Nat.primesLE N,Real.cos (t*Real.log p)/(p : ℝ)| ≤
        2*remainderTotal+A*Real.exp A*(1+Real.log 4) := by
  have hL := logN_ge hN
  have hL0 : 0<Real.log N := by linarith
  have hA0 : 0≤A := (abs_nonneg a).trans hA
  have hl : Real.log ‖∏ p ∈ Nat.primesLE N,(1-q a t N p)‖=
      ∑ p ∈ Nat.primesLE N,Real.log ‖1-q a t N p‖ := by
    rw [norm_prod]
    apply Real.log_prod
    intro p hp
    exact norm_ne_zero_iff.mpr (q_nonzero a t N (Nat.mem_primesLE.mp hp).2.two_le ha)
  have hrem : |∑ p ∈ Nat.primesLE N,(Real.log ‖1-q a t N p‖+(q a t N p).re)|
      ≤ 2*remainderTotal := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc (∑ p ∈ Nat.primesLE N,|Real.log ‖1-q a t N p‖+(q a t N p).re|) ≤
        ∑ p ∈ Nat.primesLE N,2*(p : ℝ)^(-(3/2) : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          have hp2 := (Nat.mem_primesLE.mp hp).2.two_le
          have hn := q_norm a t N hp2
          have hr : |-a/(2*Real.log N)|≤1/8 := by simpa only [neg_div,abs_neg] using ha
          have hq : ‖q a t N p‖≤3/4 := by rw [hn]; exact radialNome_le hp2 hr
          have hsq : ‖q a t N p‖^2≤(p : ℝ)^(-(3/2) : ℝ) := by
            rw [hn]; exact sq_radialNome_le hp2 hr
          exact (log_error hq).trans (mul_le_mul_of_nonneg_left hsq (by norm_num))
         _ ≤ 2*remainderTotal := by
           rw [← Finset.mul_sum]
           apply mul_le_mul_of_nonneg_left _ (by norm_num)
           exact remainder_summable.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hshift : |∑ p ∈ Nat.primesLE N,((q a t N p).re-(q 0 t N p).re)| ≤
      A*Real.exp A*(1+Real.log 4) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc (∑ p ∈ Nat.primesLE N,|(q a t N p).re-(q 0 t N p).re|) ≤
        ∑ p ∈ Nat.primesLE N,A*Real.exp A/Real.log N*(Real.log p/(p : ℝ)) := by
          apply Finset.sum_le_sum
          intro p hp
          have hpp := Nat.mem_primesLE.mp hp
          exact (Complex.abs_re_le_norm (q a t N p-q 0 t N p)).trans
            (q_shift hA hN hpp.2.two_le hpp.1 t)
         _ ≤ A*Real.exp A/Real.log N*(Real.log N+Real.log 4) := by
           rw [← Finset.mul_sum]
           exact mul_le_mul_of_nonneg_left (mertensFirst_upper (by omega)) (by positivity)
         _ ≤ A*Real.exp A*(1+Real.log 4) := by
           have he : A*Real.exp A/Real.log N*(Real.log N+Real.log 4) =
               A*Real.exp A*(1+Real.log 4/Real.log N) := by field_simp
           rw [he]
           gcongr
           rw [div_le_iff₀ hL0]
           nlinarith [Real.log_nonneg (show (1 : ℝ)≤4 by norm_num)]
  have hzero : (∑ p ∈ Nat.primesLE N,(q 0 t N p).re)=
      ∑ p ∈ Nat.primesLE N,Real.cos (t*Real.log p)/(p : ℝ) := by
    exact Finset.sum_congr rfl fun p hp => q_zero_re N (Nat.mem_primesLE.mp hp).2.pos t
  rw [Finset.sum_add_distrib] at hrem
  rw [Finset.sum_sub_distrib,hzero] at hshift
  rw [hl]
  have hr := abs_le.mp hrem
  have hs := abs_le.mp hshift
  apply abs_le.mpr
  constructor <;> linarith

/-- Original finite Euler products are uniformly comparable with inverse zeta
at the standard right abscissa. The frequency is completely unrestricted,
and the finite product may lie on either side of the one-line. -/
theorem criticalFiniteEulerProduct_zeta_comparison (A : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop, ∀ a : ℝ, |a|≤|A| → ∀ t : ℝ,
      Real.exp (-C) ≤
        ‖∏ p ∈ Nat.primesLE N,(1-(p : ℂ)^(-1-(a/Real.log N : ℝ)-(t : ℂ)*Complex.I))‖ *
        ‖riemannZeta (((1+1/Real.log N : ℝ) : ℂ)+(t : ℂ)*Complex.I)‖ ∧
      ‖∏ p ∈ Nat.primesLE N,(1-(p : ℂ)^(-1-(a/Real.log N : ℝ)-(t : ℂ)*Complex.I))‖ *
        ‖riemannZeta (((1+1/Real.log N : ℝ) : ℂ)+(t : ℂ)*Complex.I)‖ ≤ Real.exp C := by
  let B : ℝ := 2*remainderTotal+|A| *Real.exp |A| *(1+Real.log 4)+
    (Real.pi^2/6+primeTailConstant+(1+Real.log 4))
  refine ⟨|B|+1,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop 3,eventually_abs_drift_le (|A|/2)] with N hN hNA
  intro a ha t
  have hL := logN_ge hN
  have hL0 : 0<Real.log N := by linarith
  have hadrift : |a/(2*Real.log N)|≤1/8 := by
    have he : |(|A|/2)/Real.log N|=|A|/(2*Real.log N) := by
      rw [abs_div,abs_of_pos hL0,abs_div,abs_abs,abs_of_pos (show (0 : ℝ)<2 by norm_num)]
      ring
    rw [he] at hNA
    rw [abs_div,abs_of_pos (show 0<2*Real.log N by positivity)]
    exact (div_le_div_of_nonneg_right ha (by positivity)).trans hNA
  let Q : ℂ := ∏ p ∈ Nat.primesLE N,(1-q a t N p)
  let Z : ℂ := riemannZeta (((1+1/Real.log N : ℝ) : ℂ)+(t : ℂ)*Complex.I)
  have hQ : Q≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact q_nonzero a t N (Nat.mem_primesLE.mp hp).2.two_le hadrift
  have hZ : Z≠0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    have : 0<1/Real.log N := by positivity
    simp only [Complex.add_re,Complex.mul_re,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero]
    linarith
  have hprod := log_product_comparison ha hN hadrift t
  have hzeta := cosine_zeta_comparison hN t
  have hh : |Real.log ‖Q‖+Real.log ‖Z‖|≤B := by
    have h1 := abs_le.mp hprod
    have h2 := abs_le.mp hzeta
    apply abs_le.mpr
    constructor <;> dsimp [Q,Z,B] at * <;> linarith
  have hsum := abs_le.mp (hh.trans (le_trans (le_abs_self B) (by linarith : |B|≤|B|+1)))
  have hval : Real.exp (Real.log ‖Q‖+Real.log ‖Z‖)=‖Q‖*‖Z‖ := by
    rw [Real.exp_add,Real.exp_log (norm_pos_iff.mpr hQ),Real.exp_log (norm_pos_iff.mpr hZ)]
  have hlow := Real.exp_le_exp.mpr hsum.1
  have hupp := Real.exp_le_exp.mpr hsum.2
  rw [hval] at hlow hupp
  have hQeq : Q=∏ p ∈ Nat.primesLE N,
      (1-(p : ℂ)^(-1-(a/Real.log N : ℝ)-(t : ℂ)*Complex.I)) := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [q_cpow _ _ _ (Nat.mem_primesLE.mp hp).2.pos]
  rw [hQeq] at hlow hupp
  exact ⟨hlow,hupp⟩

end RHTower.BAGTrace
