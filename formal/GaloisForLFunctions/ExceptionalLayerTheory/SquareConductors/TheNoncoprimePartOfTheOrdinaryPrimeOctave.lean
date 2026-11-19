import GaloisForLFunctions.ExceptionalLayerTheory.CancellationOnRepeatedPrimeFactors
import GaloisForLFunctions.RHTower.Sieve.SelbergInversion
import GaloisForLFunctions.RHTower.BurnolAlternatingHarmonic
import GaloisForLFunctions.HTGeometry.HarmonicLogWindow
import GaloisForLFunctions.RHTower.Sieve.SquarefreeCount
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# The noncoprime part of the ordinary-prime octave

Two distinct integers in a common sharp octave cannot share a prime if
either is itself prime. The centered prime pair weight on every noncoprime
pair therefore equals the ordinary harmonic weight. Möbius inversion gives
its entire contribution, retaining both floors in each divisor row.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Reciprocal mass on a sharp integer interval. -/
def octaveIntervalHarmonic (lo hi : ℕ) : ℝ := ∑ d ∈ Ioc lo hi, (d:ℝ)⁻¹

/-- Ordinary primes centered against the unit density. -/
def centeredOrdinaryPrimeWeight (d : ℕ) : ℝ := (if d.Prime then Real.log d else 0)-1

private theorem no_proper_multiple_in_octave {M d e : ℕ} (hd : d∈Ioc M (2*M))
    (he : e∈Ioc M (2*M)) (hne : d≠e) : ¬ d∣e := by
  obtain ⟨hd0,_⟩ := mem_Ioc.mp hd
  obtain ⟨he0,he2⟩ := mem_Ioc.mp he
  rintro ⟨k,rfl⟩
  have hk : 2≤k := by
    rcases k with _|k
    · simp only [Nat.mul_zero] at he0; omega
    rcases k with _|k
    · exact False.elim (hne (Nat.mul_one d).symm)
    · omega
  have h := Nat.mul_le_mul_left d hk
  rw [Nat.mul_comm d 2] at h
  omega

theorem centered_ordinary_weights_of_shared_divisor {M d e : ℕ}
    (hd : d∈Ioc M (2*M)) (he : e∈Ioc M (2*M)) (hne : d≠e) (hc : ¬d.Coprime e) :
    centeredOrdinaryPrimeWeight d*centeredOrdinaryPrimeWeight e=1 := by
  have hp : ¬d.Prime := fun h => hc (h.coprime_iff_not_dvd.mpr (no_proper_multiple_in_octave hd he hne))
  have hq : ¬e.Prime := fun h => hc ((h.coprime_iff_not_dvd.mpr (no_proper_multiple_in_octave he hd hne.symm)).symm)
  simp [centeredOrdinaryPrimeWeight,hp,hq]

/-- Both orders of every distinct noncoprime pair are included. -/
def noncoprimeOrdinaryOctave (M : ℕ) : ℝ :=
  ∑ d ∈ Ioc M (2*M), ∑ e ∈ Ioc M (2*M),
    if d≠e ∧ ¬d.Coprime e then (centeredOrdinaryPrimeWeight d*centeredOrdinaryPrimeWeight e)*
      ((d:ℝ)⁻¹*(e:ℝ)⁻¹) else 0

private theorem common_divisor_indicator {M d e : ℕ} (hd : d∈Ioc M (2*M)) (he : e∈Ioc M (2*M)) :
    (∑ h ∈ Icc 1 (2*M), if h∣d ∧ h∣e then (moebius h:ℝ) else 0) =
      if d.Coprime e then 1 else 0 := by
  have hd0 : 0<d := (Nat.zero_le _).trans_lt (mem_Ioc.mp hd).1
  have he0 : 0<e := (Nat.zero_le _).trans_lt (mem_Ioc.mp he).1
  have hset : (Icc 1 (2*M)).filter (fun h => h∣d ∧ h∣e) = (d.gcd e).divisors := by
    ext h
    simp only [mem_filter,mem_Icc,Nat.mem_divisors]
    exact ⟨fun h => ⟨Nat.dvd_gcd h.2.1 h.2.2,(Nat.gcd_pos_of_pos_right d he0).ne'⟩,
      fun h => ⟨⟨Nat.pos_of_dvd_of_pos (h.1.trans (Nat.gcd_dvd_left _ _)) hd0,
        (Nat.le_of_dvd hd0 (h.1.trans (Nat.gcd_dvd_left _ _))).trans (mem_Ioc.mp hd).2⟩,
        h.1.trans (Nat.gcd_dvd_left _ _),h.1.trans (Nat.gcd_dvd_right _ _)⟩⟩
  rw [←sum_filter,hset,_root_.RHTower.Sieve.sum_divisors_moebius_real]

private theorem octave_multiples_row {h : ℕ} (hh : 0<h) (M : ℕ) :
    (∑ d ∈ Ioc M (2*M), if h∣d then (d:ℝ)⁻¹ else 0) =
      (h:ℝ)⁻¹*octaveIntervalHarmonic (M/h) (2*M/h) := by
  rw [←sum_filter,sum_divisible_Ioc hh,octaveIntervalHarmonic,mul_sum]
  apply sum_congr rfl
  intro d _
  simp only [Nat.cast_mul,mul_inv_rev,mul_comm]

/-- Exact common-divisor correction to the centered ordinary-prime
second moment, at every pair of original octave endpoints. -/
theorem noncoprime_ordinary_octave_exact {M : ℕ} (hM : 0<M) :
    noncoprimeOrdinaryOctave M = (octaveIntervalHarmonic M (2*M))^2 -
      (∑ d ∈ Ioc M (2*M), ((d:ℝ)⁻¹)^2) -
      ∑ h ∈ Icc 1 (2*M), (moebius h:ℝ)*
        ((h:ℝ)⁻¹*octaveIntervalHarmonic (M/h) (2*M/h))^2 := by
  let S := Ioc M (2*M)
  let T := Icc 1 (2*M)
  let w (d : ℕ) := (d:ℝ)⁻¹
  let f (h d : ℕ) := if h∣d then w d else 0
  have row (d : ℕ) (hd : d∈S) (e : ℕ) (he : e∈S) :
      (if d≠e ∧ ¬d.Coprime e then (centeredOrdinaryPrimeWeight d*centeredOrdinaryPrimeWeight e)*
        (w d*w e) else 0) =
      w d*w e - (if e=d then w d^2 else 0) -
        ∑ h ∈ T,(moebius h:ℝ)*f h d*f h e := by
    have hterm (h : ℕ) : (moebius h:ℝ)*f h d*f h e =
        (if h∣d ∧ h∣e then (moebius h:ℝ) else 0)*(w d*w e) := by
      by_cases hd' : h∣d <;> by_cases he' : h∣e <;> simp [f,hd',he',mul_assoc]
    rw [sum_congr rfl (fun h _ => hterm h),←sum_mul,common_divisor_indicator hd he]
    by_cases hde : d=e
    · subst e
      have hdc : ¬d.Coprime d := by
        change d.gcd d≠1
        rw [Nat.gcd_self]
        have := (mem_Ioc.mp hd).1
        omega
      simp [hdc,sq]
    · by_cases hc : d.Coprime e
      · rw [if_pos hc,if_neg (Ne.symm hde),if_neg (fun t => t.2 hc)]
        ring
      · rw [if_neg hc,if_neg (Ne.symm hde),if_pos ⟨hde,hc⟩,centered_ordinary_weights_of_shared_divisor hd he hde hc]
        ring
  have hgroup : (∑ d ∈ S, ∑ e ∈ S, ∑ h ∈ T,(moebius h:ℝ)*f h d*f h e) =
      ∑ h ∈ T,(moebius h:ℝ)*(∑ d ∈ S,f h d)^2 := by
    calc _ = ∑ d ∈ S, ∑ h ∈ T, ∑ e ∈ S, (moebius h:ℝ)*f h d*f h e :=
           sum_congr rfl fun d _ => sum_comm
         _ = _ := by
           rw [sum_comm]
           apply sum_congr rfl
           intro h _
           simp_rw [←mul_sum]
           rw [←sum_mul,←mul_sum,sq,mul_assoc]
  have hfull : (∑ d ∈ S, ∑ e ∈ S, w d*w e) = (octaveIntervalHarmonic M (2*M))^2 := by
    simp_rw [←mul_sum]
    rw [←sum_mul,sq]
    rfl
  have hdiag (d : ℕ) (hd : d∈S) : (∑ e ∈ S, if e=d then w d^2 else 0)=w d^2 := by simp [hd]
  unfold noncoprimeOrdinaryOctave
  rw [sum_congr rfl (fun d hd => sum_congr rfl (row d hd))]
  simp only [sum_sub_distrib]
  rw [hfull,sum_congr rfl hdiag,hgroup]
  congr 1
  apply sum_congr rfl
  intro h hh
  rw [show (∑ d ∈ S,f h d)=(h:ℝ)⁻¹*octaveIntervalHarmonic (M/h) (2*M/h) from
    octave_multiples_row (mem_Icc.mp hh).1 M]

private theorem interval_harmonic_half (n : ℕ) :
    octaveIntervalHarmonic (n/2) n = _root_.RHTower.burnolAlternatingHarmonic n := by
  let m := n/2
  have hm : n=2*m ∨ n=2*m+1 := by dsimp only [m]; omega
  change octaveIntervalHarmonic m n=_
  rcases hm with hh|hh
  · rw [hh,octaveIntervalHarmonic,_root_.HTGeometry.sum_Ioc_inv_eq_harmonic_sub (by omega),
      _root_.RHTower.burnolAlternatingHarmonic_two_mul]
  · rw [hh,octaveIntervalHarmonic,_root_.HTGeometry.sum_Ioc_inv_eq_harmonic_sub (by omega)]
    have hnext : _root_.RHTower.burnolAlternatingHarmonic (2*m+1) =
        _root_.RHTower.burnolAlternatingHarmonic (2*m)+1/((2*m:ℕ)+1:ℝ) := by
      rw [_root_.RHTower.burnolAlternatingHarmonic,_root_.RHTower.burnolAlternatingHarmonic,
        Finset.sum_range_succ,pow_mul]
      norm_num
    rw [hnext,_root_.RHTower.burnolAlternatingHarmonic_two_mul,harmonic_succ]
    push_cast
    ring

/-- Both divided endpoints give one alternating harmonic partial sum.
Its parity gives the sign of the terminal correction. -/
theorem octave_harmonic_divisor_row (M h : ℕ) :
    octaveIntervalHarmonic (M/h) (2*M/h) = Real.log 2 -
      (-1:ℝ)^(2*M/h)*_root_.RHTower.burnolAltTail (2*M/h) := by
  have hf : (2*M/h)/2=M/h := by
    rw [Nat.div_div_eq_div_mul,Nat.mul_comm h 2,←Nat.div_div_eq_div_mul,
      Nat.mul_div_cancel_left _ (by decide : 0<2)]
  rw [←hf,interval_harmonic_half,_root_.RHTower.burnolAlternatingHarmonic_eq]

private theorem harmonic_row_error {M h : ℕ} (hM : 0<M) (hh : 0<h) :
    |octaveIntervalHarmonic (M/h) (2*M/h)-Real.log 2|≤(h:ℝ)/(2*M) := by
  let t := 2*M/h
  have hterr := _root_.RHTower.abs_burnolAltTail_sub_le t
  have hpos : 0<(t:ℝ)+1 := by positivity
  have hrem : 1/(2*((t:ℝ)+1)*((t:ℝ)+2)) ≤ 1/(2*((t:ℝ)+1)) :=
    one_div_le_one_div_of_le (by positivity) (le_mul_of_one_le_right (by positivity) (by linarith only [hpos]))
  have ht : |_root_.RHTower.burnolAltTail t|≤1/((t:ℝ)+1) := by
    rcases abs_le.mp hterr with ⟨hlo,hhi⟩
    have he : 1/(2*((t:ℝ)+1)) + 1/(2*((t:ℝ)+1)) = 1/((t:ℝ)+1) := by field_simp [hpos.ne']; ring
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi,hrem,he,one_div_pos.mpr hpos]
  rw [octave_harmonic_divisor_row,sub_sub_cancel_left,abs_neg,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
  apply ht.trans
  apply (div_le_div_iff₀ hpos (by positivity : 0<2*(M:ℝ))).mpr
  rw [one_mul]
  exact_mod_cast (show 2*M≤h*(t+1) from (Nat.lt_mul_div_succ (2*M) hh).le)


private theorem octave_harmonic_square_error {M h : ℕ} (hM : 0<M) (hh : h∈Icc 1 (2*M)) :
    |(octaveIntervalHarmonic (M/h) (2*M/h))^2-(Real.log 2)^2|≤3*((h:ℝ)/(2*M)) := by
  let L := octaveIntervalHarmonic (M/h) (2*M/h)
  have he := harmonic_row_error hM (mem_Icc.mp hh).1
  change |L-Real.log 2|≤_ at he
  have hratio : (h:ℝ)/(2*M)≤1 := (div_le_one (by positivity)).mpr (by exact_mod_cast (mem_Icc.mp hh).2)
  have hL : 0≤L := sum_nonneg (fun d _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  have hl := Real.log_nonneg (by norm_num : (1:ℝ)≤2)
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hplus : |L+Real.log 2|≤3 := by
    rw [abs_of_nonneg (add_nonneg hL hl)]
    linarith only [(le_abs_self (L-Real.log 2)).trans he,hratio,hlog]
  change |L^2-(Real.log 2)^2|≤_
  rw [sq_sub_sq,abs_mul]
  exact mul_le_mul hplus he (abs_nonneg _) (by norm_num)

private theorem octave_reciprocal_diagonal {M : ℕ} (hM : 0<M) :
    (∑ d ∈ Ioc M (2*M), ((d:ℝ)⁻¹)^2) ≤ (M:ℝ)⁻¹ := by
  have h0 : 0<(M:ℝ) := Nat.cast_pos.mpr hM
  have h := sum_le_sum (s := Ioc M (2*M)) (fun d hd => pow_le_pow_left₀
    (inv_nonneg.mpr (Nat.cast_nonneg d : 0≤(d:ℝ)))
    (inv_anti₀ h0 (Nat.cast_le.mpr (mem_Ioc.mp hd).1.le)) 2)
  rw [sum_const,nsmul_eq_mul,Nat.card_Ioc,show 2*M-M=M by omega] at h
  exact h.trans_eq (by field_simp [h0.ne'])

/-- Quantitative separation of the noncoprime main term. The entire
error at one terminal costs at most a harmonic sum divided by M. -/
theorem noncoprime_ordinary_octave_density_error {M : ℕ} (hM : 0<M) :
    |noncoprimeOrdinaryOctave M -
      (1-∑ h ∈ Icc 1 (2*M), (moebius h:ℝ)*((h:ℝ)⁻¹)^2)*(Real.log 2)^2| ≤
      (M:ℝ)⁻¹ + 3/(2*M)*(1+∑ h ∈ Icc 1 (2*M),(h:ℝ)⁻¹) := by
  let T := Icc 1 (2*M)
  let w (h : ℕ) := (moebius h:ℝ)*((h:ℝ)⁻¹)^2
  let L (h : ℕ) := octaveIntervalHarmonic (M/h) (2*M/h)
  let l := Real.log 2
  let D := ∑ d ∈ Ioc M (2*M), ((d:ℝ)⁻¹)^2
  have ht (h : ℕ) (hh : h∈T) :
      |w h*(L h^2-l^2)| ≤ 3/(2*M)*(h:ℝ)⁻¹ := by
    have hp : (0:ℝ)<h := Nat.cast_pos.mpr (mem_Icc.mp hh).1
    have hm : |(moebius h:ℝ)|≤1 := by exact_mod_cast (abs_moebius_le_one (n := h))
    dsimp only [w]; rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg ((h:ℝ)⁻¹))]
    have hw := mul_le_of_le_one_left (sq_nonneg ((h:ℝ)⁻¹)) hm
    apply (mul_le_mul hw (octave_harmonic_square_error hM hh) (abs_nonneg _) (sq_nonneg _)).trans_eq
    field_simp [hp.ne']
  have hsum := (abs_sum_le_sum_abs _ _).trans (sum_le_sum ht)
  rw [←mul_sum] at hsum
  have hdiag : |D|≤(M:ℝ)⁻¹ := by
    rw [abs_of_nonneg (show 0≤D from sum_nonneg (fun _ _ => sq_nonneg _))]
    exact octave_reciprocal_diagonal hM
  have h1 := octave_harmonic_square_error hM (h := 1) (mem_Icc.mpr ⟨le_rfl,by omega⟩)
  simp only [Nat.div_one,Nat.cast_one] at h1
  have eqn : noncoprimeOrdinaryOctave M-(1-∑ h ∈ T,w h)*l^2 =
      ((octaveIntervalHarmonic M (2*M))^2-l^2)-D-∑ h ∈ T,w h*(L h^2-l^2) := by
    rw [noncoprime_ordinary_octave_exact hM,sub_mul,one_mul,sum_mul]
    simp_rw [mul_sub]
    rw [sum_sub_distrib]
    have hs : (∑ h ∈ Icc 1 (2*M), (moebius h:ℝ)*((h:ℝ)⁻¹*octaveIntervalHarmonic (M/h) (2*M/h))^2) =
        ∑ h ∈ T,w h*L h^2 := sum_congr rfl fun h _ => by dsimp only [w,L]; ring
    rw [hs]; ring
  rw [eqn]
  change _ ≤ (M:ℝ)⁻¹+3/(2*M)*(1+∑ h ∈ T,(h:ℝ)⁻¹)
  apply ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add h1 hdiag)) hsum)).trans_eq
  ring

/-- Density of noncoprime pairs multiplied by the two reciprocal octave masses. -/
def noncoprimeOctaveMainTerm : ℝ := (1-6/Real.pi^2)*(Real.log 2)^2

theorem noncoprime_octave_main_term_pos : 0<noncoprimeOctaveMainTerm := by
  have hpi : (3:ℝ)^2<Real.pi^2 := pow_lt_pow_left₀ Real.pi_gt_three (by norm_num) (by decide)
  exact mul_pos (sub_pos.mpr ((div_lt_one (sq_pos_of_pos Real.pi_pos)).mpr
    (by linarith only [hpi]))) (sq_pos_of_pos (Real.log_pos (by norm_num)))

/-- The secondary term has a fixed positive coefficient at every terminal. -/
theorem noncoprime_ordinary_octave_constant {M : ℕ} (hM : 0<M) :
    |noncoprimeOrdinaryOctave M-noncoprimeOctaveMainTerm|≤
      5*(1+Real.log (2*M))/(M:ℝ) := by
  let S := ∑ h ∈ Icc 1 (2*M),(moebius h:ℝ)*((h:ℝ)⁻¹)^2
  let F := (1-S)*(Real.log 2)^2
  let H := ∑ h ∈ Icc 1 (2*M),(h:ℝ)⁻¹
  have hm : 0<(M:ℝ) := Nat.cast_pos.mpr hM
  have h2m : 1≤2*M := by omega
  have htr := _root_.RHTower.Sieve.abs_sum_Icc_moebius_div_sq_sub_le h2m
  rw [_root_.RHTower.Sieve.squarefreeDensity_eq] at htr
  have htr' : |S-6/Real.pi^2|≤1/(2*(M:ℝ)) := by
    simpa only [S,div_eq_mul_inv,inv_pow,Nat.cast_mul,Nat.cast_ofNat] using htr
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hl0 := Real.log_nonneg (by norm_num : (1:ℝ)≤2)
  have hlsq : (Real.log 2)^2≤1 := calc
    _ ≤ (1:ℝ)^2 := pow_le_pow_left₀ hl0 (by linarith only [hl]) _
    _ = _ := one_pow _
  have hcorr : |F-noncoprimeOctaveMainTerm|≤1/(2*(M:ℝ)) := by
    rw [show F-noncoprimeOctaveMainTerm=-(S-6/Real.pi^2)*(Real.log 2)^2 by
      dsimp only [F,noncoprimeOctaveMainTerm]; ring,abs_mul,abs_neg,abs_of_nonneg (sq_nonneg (Real.log 2))]
    exact (mul_le_of_le_one_right (abs_nonneg _) hlsq).trans htr'
  have hH : H≤1+Real.log (2*M) := by
    simpa only [H,one_div,Nat.cast_mul,Nat.cast_ofNat] using _root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log (2*M)
  have hh := noncoprime_ordinary_octave_density_error hM
  change |noncoprimeOrdinaryOctave M-F|≤(M:ℝ)⁻¹+3/(2*M)*(1+H) at hh
  have hlg := Real.log_nonneg (show (1:ℝ)≤2*M by exact_mod_cast h2m)
  calc |noncoprimeOrdinaryOctave M-noncoprimeOctaveMainTerm| =
         |(noncoprimeOrdinaryOctave M-F)+(F-noncoprimeOctaveMainTerm)| := by congr 1; ring
       _ ≤ _ := abs_add_le _ _
       _ ≤ _ := add_le_add hh hcorr
       _ ≤ (M:ℝ)⁻¹+3/(2*M)*(1+(1+Real.log (2*M)))+1/(2*M) := by gcongr
       _ = (1+(3/2)*(2+Real.log (2*M))+1/2)/(M:ℝ) := by field_simp [hm.ne']; ring
       _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hlg]) hm.le

/-- Any selection of actual octave terminals has the same linear main
term with a log-squared total error, uniformly in the choice of terminals. -/
theorem noncoprime_ordinary_octave_fragments {N : ℕ} (S : Finset ℕ) (hS : S ⊆ Icc 1 N) :
    |(∑ M ∈ S,noncoprimeOrdinaryOctave M)-(S.card:ℝ)*noncoprimeOctaveMainTerm|≤
      5*(1+Real.log (2*N))^2 := by
  rcases Nat.eq_zero_or_pos N with rfl|hn
  · have hse : S=∅ := eq_empty_of_forall_notMem fun n hn => by have := mem_Icc.mp (hS hn); omega
    simp [hse]
  let A := 1+Real.log (2*N)
  have h2n : 1≤2*N := by omega
  have ha : 0≤A := by dsimp only [A]; linarith only [Real.log_nonneg (show (1:ℝ)≤2*N by exact_mod_cast h2n)]
  have hH : (∑ M ∈ S,(M:ℝ)⁻¹) ≤ A := by
    apply (sum_le_sum_of_subset_of_nonneg hS (fun m _ _ => inv_nonneg.mpr (Nat.cast_nonneg m))).trans
    have h := _root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log N
    have hl := Real.log_le_log (Nat.cast_pos.mpr hn : (0:ℝ)<N)
      (show (N:ℝ)≤2*N by linarith only [(Nat.cast_nonneg N : (0:ℝ)≤N)])
    dsimp only [A]; simp only [one_div] at h
    linarith only [h,hl]
  have term (m : ℕ) (hm : m∈S) :
      |noncoprimeOrdinaryOctave m-noncoprimeOctaveMainTerm|≤(5*A)*(m:ℝ)⁻¹ := by
    obtain ⟨hm1,hmN⟩ := mem_Icc.mp (hS hm)
    apply (noncoprime_ordinary_octave_constant hm1).trans
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Nat.cast_nonneg _))
    dsimp only [A]; gcongr
  have hh := (abs_sum_le_sum_abs _ _).trans (sum_le_sum term)
  rw [sum_sub_distrib,sum_const,nsmul_eq_mul,←mul_sum] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left hH (mul_nonneg (by norm_num) ha)).trans_eq (by ring))

#print axioms noncoprime_ordinary_octave_fragments
#print axioms noncoprime_octave_main_term_pos



#print axioms noncoprime_ordinary_octave_density_error

#print axioms octave_harmonic_divisor_row
#print axioms centered_ordinary_weights_of_shared_divisor
#print axioms noncoprime_ordinary_octave_exact
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
