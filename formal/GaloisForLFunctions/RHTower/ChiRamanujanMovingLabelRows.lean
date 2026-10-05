import GaloisForLFunctions.RHTower.ChiRamanujanMovingResponseWindow
import GaloisForLFunctions.RHTower.ChiRamanujanMaskedMellinSource
import GaloisForLFunctions.RHTower.ChiRamanujanCriticalMellinDeformation
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
/-!
# Actual growing Mellin response rows and collisions

All four original distinguished-label responses have explicit prime-window
limits. Their exact rational profiles meet the two continuity conditions of
the moving-window theorem. The additional collision weight is -z log z at
z=1/p, continuous and zero at the limiting slice. The same theorem therefore
makes every actual pair and triple collision negligible at logarithmic scale.
-/

open scoped BigOperators Topology
open Filter MeasureTheory
noncomputable section
namespace RHTower.BAGTrace

private def responseF (a b : ℂ) : ℂ := (a+b-a^2-b^2)/(a*b)
private def responseG (a b : ℂ) : ℂ := a+b-1-b/a-a/b+b^2/a+a^2/b
private def responseBase (z a b : ℂ) : ℂ :=
  1+(z*responseF a b+z^2*(a+b-2))/(1-z)^2
private def responseFirstNumerator (z a b : ℂ) : ℂ :=
  ((a+b-1)+z*((a+b)*responseF a b-a*b-1)+
    z^2*(a*b-a-b+a^2+b^2))/(a*(1-z)^2)
private def responseThirdNumerator (z a b : ℂ) : ℂ :=
  (a*b-a-b+z*(2*(a+b)-a*b-1)-z^2*a*b)/(a*b*(1-z)^3)
private def responsePairNumerator (z a b : ℂ) : ℂ :=
  (a^2+b^2+a*b-a-b+z*(a*b*(2-responseF a b-a-b)-(a+b)*responseG a b)+
    z^2*a*b*responseG a b)/(a*b*(1-z)^2)
private def responseNumerator (k : Fin 4) (z a b : ℂ) : ℂ :=
  if k=0 then responseFirstNumerator z a b else
  if k=1 then responseFirstNumerator z b a else
  if k=2 then responseThirdNumerator z a b else responsePairNumerator z a b
private def responseRational (k : Fin 4) (z a b : ℂ) : ℂ :=
  responseNumerator k z a b/responseBase z a b
private def responseProfile (k : Fin 4) (u v : ℂ) (zt : ℝ × ℝ) : ℂ :=
  responseRational k zt.1 (Complex.exp (-u*(zt.2 : ℂ))) (Complex.exp (-v*(zt.2 : ℂ)))

private theorem responseBase_zero (a b : ℂ) : responseBase 0 a b = 1 := by
  simp [responseBase]

private theorem responseBase_balanced (z : ℂ) : responseBase z 1 1 = 1 := by
  norm_num [responseBase,responseF]

private theorem continuousAt_responseBase {z a b : ℂ}
    (hz : 1-z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    ContinuousAt (fun w : ℂ × ℂ × ℂ => responseBase w.1 w.2.1 w.2.2) (z,a,b) := by
  unfold responseBase responseF
  fun_prop (disch := simp [hz,ha,hb])

private theorem continuousAt_responseNumerator (k : Fin 4) {z a b : ℂ}
    (hz : 1-z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    ContinuousAt (fun w : ℂ × ℂ × ℂ => responseNumerator k w.1 w.2.1 w.2.2) (z,a,b) := by
  fin_cases k <;>
    simp [responseNumerator,responseFirstNumerator,responseThirdNumerator,
      responsePairNumerator,responseF,responseG] <;>
    fun_prop (disch := simp [hz,ha,hb])

private theorem continuousAt_responseRational (k : Fin 4) {z a b : ℂ}
    (hz : 1-z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hH : responseBase z a b ≠ 0) :
    ContinuousAt (fun w : ℂ × ℂ × ℂ => responseRational k w.1 w.2.1 w.2.2) (z,a,b) :=
  (continuousAt_responseNumerator k hz ha hb).div (continuousAt_responseBase hz ha hb) hH

private theorem continuousAt_responseProfile (k : Fin 4) (u v : ℂ) {z t : ℝ}
    (hz : 1-(z : ℂ) ≠ 0)
    (hH : responseBase z (Complex.exp (-u*(t : ℂ))) (Complex.exp (-v*(t : ℂ))) ≠ 0) :
    ContinuousAt (responseProfile k u v) (z,t) := by
  have hm : ContinuousAt (fun zt : ℝ × ℝ => ((zt.1 : ℂ),
      Complex.exp (-u*(zt.2 : ℂ)),Complex.exp (-v*(zt.2 : ℂ)))) (z,t) := by fun_prop
  have h := (continuousAt_responseRational k hz (Complex.exp_ne_zero _)
    (Complex.exp_ne_zero _) hH).tendsto.comp hm.tendsto
  exact h

private theorem responseProfile_slice (k : Fin 4) (u v : ℂ) (t : ℝ) :
    ContinuousAt (responseProfile k u v) (0,t) := by
  apply continuousAt_responseProfile
  · norm_num
  · simp [responseBase_zero]

private theorem responseProfile_prime_head (k : Fin 4) (u v : ℂ) (n : ℕ) (hn : n.Prime) :
    ContinuousAt (responseProfile k u v) ((n : ℝ)⁻¹,0) := by
  apply continuousAt_responseProfile
  · have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn.one_lt
    have hi : (n : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hn1
    exact_mod_cast (sub_pos.mpr hi).ne'
  · simp [responseBase_balanced]

private def responseLocalNumerator (k : Fin 4) (z x y : ℂ) : ℂ :=
  if k=0 then x⁻¹*weightedConeEulerMinusOne z x y else
  if k=1 then y⁻¹*weightedConeEulerMinusOne z x y else
  if k=2 then weightedConeEuler z x y 1 else x⁻¹*y⁻¹*weightedConeEulerMinusTwo z x y

private theorem minusOne_swap (z x y : ℂ) (hz : 1-z ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0) (hx1 : 1-x ≠ 0) (hy1 : 1-y ≠ 0) :
    weightedConeEulerMinusOne z x y = weightedConeEulerMinusOne z y x := by
  unfold weightedConeEulerMinusOne weightedEuler
  field_simp
  ring

private theorem responseBase_eq (z a b : ℂ) (hz : z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : 1-z ≠ 0) (hx : 1-z*a ≠ 0) (hy : 1-z*b ≠ 0) :
    responseBase z a b = (1-z*a)*(1-z*b)*weightedEuler z (z*a) (z*b) := by
  have h := weightedEuler_normalized_deformation z a b hz ha hb h1 hx hy
  rw [h]
  unfold responseBase responseF
  ring

private theorem responseNumerator_eq (k : Fin 4) (z a b : ℂ)
    (hz : z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : 1-z ≠ 0) (hx : 1-z*a ≠ 0) (hy : 1-z*b ≠ 0) :
    responseNumerator k z a b = (1-z*a)*(1-z*b)*responseLocalNumerator k z (z*a) (z*b) := by
  fin_cases k
  · simp [responseNumerator,responseLocalNumerator]
    have h := weightedFirst_normalized_deformation z a b hz ha hb h1 hx hy
    unfold responseFirstNumerator responseF
    convert h.symm using 1 <;> ring
  · simp [responseNumerator,responseLocalNumerator]
    have h := weightedFirst_normalized_deformation z b a hz hb ha h1 hy hx
    rw [minusOne_swap z (z*b) (z*a) h1 (mul_ne_zero hz hb) (mul_ne_zero hz ha) hy hx] at h
    unfold responseFirstNumerator responseF
    convert h.symm using 1 <;> ring
  · simp [responseNumerator,responseLocalNumerator]
    have h := weightedThird_normalized_deformation z a b hz ha hb h1 hx hy
    exact h.symm
  · simp [responseNumerator,responseLocalNumerator]
    have h := weightedPair_normalized_deformation z a b hz ha hb h1 hx hy
    dsimp only at h
    unfold responsePairNumerator responseF responseG
    convert h.symm using 1
    ring

private theorem responseRational_eq (k : Fin 4) (z a b : ℂ)
    (hz : z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : 1-z ≠ 0) (hx : 1-z*a ≠ 0) (hy : 1-z*b ≠ 0) :
    responseRational k z a b =
      responseLocalNumerator k z (z*a) (z*b)/weightedEuler z (z*a) (z*b) := by
  rw [responseRational,responseNumerator_eq k z a b hz ha hb h1 hx hy,
    responseBase_eq z a b hz ha hb h1 hx hy]
  exact mul_div_mul_left _ _ (mul_ne_zero hx hy)

/-- The four actual distinguished-label responses; index3 is the allowed first/second coincidence. -/
def criticalMellinResponse (k : Fin 4) (p : Nat.Primes) (s t : ℂ) : ℂ :=
  if k=0 then criticalFirstMellinResponse p s t else
  if k=1 then criticalSecondMellinResponse p s t else
  if k=2 then criticalThirdMellinResponse p s t else criticalPairMellinResponse p s t

private theorem responseActual_local (k : Fin 4) (p : Nat.Primes) (s t : ℂ) :
    criticalMellinResponse k p s t =
      responseLocalNumerator k (cubicPrimeBase p 1) (cubicPrimeBase p s) (cubicPrimeBase p t)/
        weightedEuler (cubicPrimeBase p 1) (cubicPrimeBase p s) (cubicPrimeBase p t) := by
  fin_cases k <;> simp [criticalMellinResponse,responseLocalNumerator,
    criticalFirstMellinResponse,criticalSecondMellinResponse,criticalThirdMellinResponse,
    criticalPairMellinResponse,criticalLocalMellinBase]

private theorem moving_base_eq (p : Nat.Primes) (u : ℂ) (L : ℝ) :
    cubicPrimeBase p (1+u/(L : ℂ)) =
      (((p : ℝ)⁻¹ : ℝ) : ℂ)*Complex.exp (-u*((Real.log (p : ℝ)/L : ℝ) : ℂ)) := by
  have h := criticalPrimeMellinRatio_logScale p u L
  rw [criticalPrimeMellinRatio] at h
  have he := (div_eq_iff (cubicPrimeBase_ne_zero p 1)).mp h
  simpa [cubicPrimeBase,Complex.cpow_neg_one,mul_comm] using he

private theorem base_complement_nonzero (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    1-cubicPrimeBase p s ≠ 0 := by
  have h : ‖cubicPrimeBase p s‖ < 1 := by
    rw [norm_cubicPrimeBase]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.property.one_lt) (neg_neg_of_pos hs)
  intro he
  rw [← sub_eq_zero.mp he,norm_one] at h
  exact (lt_irrefl _ h)

private theorem responseActual_eq_profile (k : Fin 4) (p : Nat.Primes) (u v : ℂ) (N : ℕ)
    (hu : 0 < (1+u/(Real.log N : ℂ)).re) (hv : 0 < (1+v/(Real.log N : ℂ)).re) :
    criticalMellinResponse k p (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ)) =
      responseProfile k u v ((p : ℝ)⁻¹,Real.log (p : ℝ)/Real.log N) := by
  have hbase : cubicPrimeBase p 1 = (((p : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp [cubicPrimeBase,Complex.cpow_neg_one]
  have hz : (((p : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (inv_ne_zero (by exact_mod_cast p.property.ne_zero))
  have h1 : 1-(((p : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have hi : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀
      (by exact_mod_cast p.property.one_lt)
    exact_mod_cast (sub_pos.mpr hi).ne' 
  have hx := base_complement_nonzero p hu
  have hy := base_complement_nonzero p hv
  rw [moving_base_eq] at hx hy
  rw [responseActual_local,hbase,moving_base_eq,moving_base_eq]
  exact (responseRational_eq k (((p : ℝ)⁻¹ : ℝ) : ℂ)
    (Complex.exp (-u*((Real.log (p : ℝ)/Real.log N : ℝ) : ℂ)))
    (Complex.exp (-v*((Real.log (p : ℝ)/Real.log N : ℝ) : ℂ)))
    hz (Complex.exp_ne_zero _) (Complex.exp_ne_zero _) h1 hx hy).symm

/-- The four limiting response profiles, including the coincident first/second label. -/
def criticalMellinResponseLeading (k : Fin 4) (u v : ℂ) (t : ℝ) : ℂ :=
  if k=0 then 1+Complex.exp ((u-v)*(t : ℂ))-Complex.exp (u*(t : ℂ)) else
  if k=1 then 1+Complex.exp ((v-u)*(t : ℂ))-Complex.exp (v*(t : ℂ)) else
  if k=2 then 1-Complex.exp (u*(t : ℂ))-Complex.exp (v*(t : ℂ)) else
    1+Complex.exp ((u-v)*(t : ℂ))+Complex.exp ((v-u)*(t : ℂ))-
      Complex.exp (u*(t : ℂ))-Complex.exp (v*(t : ℂ))

private theorem responseProfile_zero (k : Fin 4) (u v : ℂ) (t : ℝ) :
    responseProfile k u v (0,t) = criticalMellinResponseLeading k u v t := by
  have hu : Complex.exp (u*(t : ℂ)) = (Complex.exp (-u*(t : ℂ)))⁻¹ := by
    rw [← Complex.exp_neg]
    congr 1
    ring
  have hv : Complex.exp (v*(t : ℂ)) = (Complex.exp (-v*(t : ℂ)))⁻¹ := by
    rw [← Complex.exp_neg]
    congr 1
    ring
  have huv : Complex.exp ((u-v)*(t : ℂ)) =
      Complex.exp (-v*(t : ℂ))/Complex.exp (-u*(t : ℂ)) := by
    rw [← Complex.exp_sub]
    congr 1
    ring
  have hvu : Complex.exp ((v-u)*(t : ℂ)) =
      Complex.exp (-u*(t : ℂ))/Complex.exp (-v*(t : ℂ)) := by
    rw [← Complex.exp_sub]
    congr 1
    ring
  simp only [responseProfile,responseRational,Complex.ofReal_zero,responseBase_zero,div_one,
    criticalMellinResponseLeading,hu,hv,huv,hvu]
  have ha := Complex.exp_ne_zero (-u*(t : ℂ))
  have hb := Complex.exp_ne_zero (-v*(t : ℂ))
  fin_cases k <;>
    simp [responseNumerator,responseFirstNumerator,responseThirdNumerator,responsePairNumerator] <;>
    field_simp <;> ring

private theorem response_moving_positive (u : ℂ) :
    ∀ᶠ N : ℕ in atTop, 0 < (1+u/(Real.log N : ℂ)).re := by
  have hd : Tendsto (fun N : ℕ => u/(Real.log N : ℂ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using criticalLogScaleInv_tendsto_zero.const_mul u
  have h := (Complex.continuous_re.tendsto _).comp
    ((tendsto_const_nhds (x := (1 : ℂ))).add hd)
  exact h.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < (1+(0 : ℂ)).re))

private theorem prime_sum (N : ℕ) (f : ℕ → ℂ) :
    (∑ p : Sieve.primeSubtypeLE N,f p.val.val) = ∑ n ∈ Nat.primesLE N,f n := by
  calc (∑ p : Sieve.primeSubtypeLE N,f p.val.val) =
      ∑ p ∈ Sieve.primeSubtypeLE N,f p.val :=
        Finset.sum_coe_sort (Sieve.primeSubtypeLE N) (fun p : Nat.Primes => f p.val)
    _ = _ := Finset.sum_subtype_of_mem f (fun n hn => Nat.prime_of_mem_primesLE hn)

/-- The actual growing distinguished-label row, without logarithmic normalization. -/
def criticalMellinResponseRow (k : Fin 4) (u v : ℂ) (N : ℕ) : ℂ :=
  ∑ p : Sieve.primeSubtypeLE N, (criticalPrimeLabelWeight p : ℂ)*
    criticalMellinResponse k p (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ))

private theorem response_row_eq_window (k : Fin 4) (u v : ℂ) (N : ℕ)
    (hu : 0 < (1+u/(Real.log N : ℂ)).re) (hv : 0 < (1+v/(Real.log N : ℂ)).re) :
    criticalMellinResponseRow k u v N =
      ∑ n ∈ Finset.Icc 0 N,responseProfile k u v ((n : ℝ)⁻¹,Real.log n/Real.log N)*
        (mertensPrimeWeight n : ℂ) := by
  unfold criticalMellinResponseRow
  simp_rw [responseActual_eq_profile k _ u v N hu hv]
  have h := prime_sum N (fun n : ℕ => ((Real.log n/(n : ℝ) : ℝ) : ℂ)*
    responseProfile k u v ((n : ℝ)⁻¹,Real.log n/Real.log N))
  rw [show (∑ p : Sieve.primeSubtypeLE N, (criticalPrimeLabelWeight p : ℂ)*
    responseProfile k u v (((p : Nat.Primes) : ℝ)⁻¹,
      Real.log ((p : Nat.Primes) : ℝ)/Real.log N)) =
      ∑ n ∈ Nat.primesLE N, ((Real.log n/(n : ℝ) : ℝ) : ℂ)*
        responseProfile k u v ((n : ℝ)⁻¹,Real.log n/Real.log N) from h]
  rw [show Nat.primesLE N = (Finset.Icc 0 N).filter Nat.Prime by
    ext n; simp [Finset.mem_filter,Finset.mem_Icc,Nat.mem_primesLE]]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n.Prime
  · simp [mertensPrimeWeight,hn,mul_comm]
  · simp [mertensPrimeWeight,hn]

/-- Every actual distinguished-label row has its full logarithmic growing-window limit. -/
theorem criticalMellinResponseRow_tendsto (k : Fin 4) (u v : ℂ) :
    Tendsto (fun N : ℕ => criticalMellinResponseRow k u v N/(Real.log N : ℂ))
      atTop (𝓝 (∫ t in (0 : ℝ)..1,criticalMellinResponseLeading k u v t)) := by
  have h := criticalMovingResponseWindow_tendsto (responseProfile k u v)
    (fun t _ => responseProfile_slice k u v t) (responseProfile_prime_head k u v)
  simp_rw [responseProfile_zero] at h
  apply h.congr'
  filter_upwards [response_moving_positive u,response_moving_positive v] with N hu hv
  rw [response_row_eq_window k u v N hu hv]

private def collisionWeight (z : ℝ) : ℂ := ((-(z*Real.log z) : ℝ) : ℂ)

private theorem collisionWeight_continuous : Continuous collisionWeight :=
  Complex.continuous_ofReal.comp Real.continuous_mul_log.neg

private theorem collisionWeight_zero : collisionWeight 0 = 0 := by simp [collisionWeight]

private theorem collisionWeight_prime (p : Nat.Primes) :
    collisionWeight ((p : ℝ)⁻¹) = (criticalPrimeLabelWeight p : ℂ) := by
  unfold collisionWeight criticalPrimeLabelWeight
  rw [Real.log_inv]
  congr 1
  ring

private def collisionProfile (k : Fin 4) (u v : ℂ) (zt : ℝ × ℝ) : ℂ :=
  let w := collisionWeight zt.1
  let a := responseProfile 0 u v zt
  let b := responseProfile 1 u v zt
  let c := responseProfile 2 u v zt
  let d := responseProfile 3 u v zt
  if k=0 then w*(d-a*b) else
  if k=1 then w*b*c else
  if k=2 then w*a*c else w^2*c*(2*a*b-d)

private theorem collisionProfile_continuousAt (k : Fin 4) (u v : ℂ) {zt : ℝ × ℝ}
    (hR : ∀ j : Fin 4, ContinuousAt (responseProfile j u v) zt) :
    ContinuousAt (collisionProfile k u v) zt := by
  have hw : ContinuousAt (fun zt : ℝ × ℝ => collisionWeight zt.1) zt :=
    collisionWeight_continuous.continuousAt.comp continuousAt_fst
  fin_cases k
  · exact hw.mul ((hR 3).sub ((hR 0).mul (hR 1)))
  · exact (hw.mul (hR 1)).mul (hR 2)
  · exact (hw.mul (hR 0)).mul (hR 2)
  · exact ((hw.pow 2).mul (hR 2)).mul
      (((continuousAt_const.mul (hR 0)).mul (hR 1)).sub (hR 3))

private theorem collisionProfile_zero (k : Fin 4) (u v : ℂ) (t : ℝ) :
    collisionProfile k u v (0,t) = 0 := by
  fin_cases k <;> simp [collisionProfile,collisionWeight_zero]

/-- The four exact collision sums from the unrestricted masked response expansion. -/
def criticalMellinCollisionMoment (k : Fin 4) (u v : ℂ) (N : ℕ) : ℂ :=
  ∑ p : Sieve.primeSubtypeLE N,
    let w : ℂ := criticalPrimeLabelWeight p
    let a := criticalMellinResponse 0 p (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ))
    let b := criticalMellinResponse 1 p (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ))
    let c := criticalMellinResponse 2 p (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ))
    let d := criticalMellinResponse 3 p (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ))
    if k=0 then w^2*(d-a*b) else
    if k=1 then w^2*b*c else
    if k=2 then w^2*a*c else w^3*c*(2*a*b-d)

private theorem profile_prime_sum (R : ℝ × ℝ → ℂ) (N : ℕ) :
    (∑ p : Sieve.primeSubtypeLE N,
      R (((p : Nat.Primes) : ℝ)⁻¹,Real.log ((p : Nat.Primes) : ℝ)/Real.log N)*
        (criticalPrimeLabelWeight p : ℂ)) =
    ∑ n ∈ Finset.Icc 0 N,R ((n : ℝ)⁻¹,Real.log n/Real.log N)*(mertensPrimeWeight n : ℂ) := by
  have h := prime_sum N (fun n : ℕ => R ((n : ℝ)⁻¹,Real.log n/Real.log N)*
    ((Real.log n/(n : ℝ) : ℝ) : ℂ))
  calc _ = ∑ n ∈ Nat.primesLE N,R ((n : ℝ)⁻¹,Real.log n/Real.log N)*
      ((Real.log n/(n : ℝ) : ℝ) : ℂ) := h
    _ = _ := by
      rw [show Nat.primesLE N = (Finset.Icc 0 N).filter Nat.Prime by
        ext n; simp [Finset.mem_filter,Finset.mem_Icc,Nat.mem_primesLE]]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : n.Prime <;> simp [mertensPrimeWeight,hn]

private theorem collision_moment_eq_window (k : Fin 4) (u v : ℂ) (N : ℕ)
    (hu : 0 < (1+u/(Real.log N : ℂ)).re) (hv : 0 < (1+v/(Real.log N : ℂ)).re) :
    criticalMellinCollisionMoment k u v N =
      ∑ n ∈ Finset.Icc 0 N,collisionProfile k u v ((n : ℝ)⁻¹,Real.log n/Real.log N)*
        (mertensPrimeWeight n : ℂ) := by
  rw [← profile_prime_sum]
  unfold criticalMellinCollisionMoment
  apply Finset.sum_congr rfl
  intro p _
  dsimp only
  simp_rw [responseActual_eq_profile _ p u v N hu hv]
  fin_cases k <;> simp [collisionProfile,collisionWeight_prime] <;> ring

/-- Every exact pair/triple collision sum is negligible even at one logarithmic scale. -/
theorem criticalMellinCollisionMoment_tendsto (k : Fin 4) (u v : ℂ) :
    Tendsto (fun N : ℕ => criticalMellinCollisionMoment k u v N/(Real.log N : ℂ))
      atTop (𝓝 0) := by
  have h := criticalMovingResponseWindow_tendsto (collisionProfile k u v)
    (fun t _ => collisionProfile_continuousAt k u v (fun j => responseProfile_slice j u v t))
    (fun n hn => collisionProfile_continuousAt k u v
      (fun j => responseProfile_prime_head j u v n hn))
  simp only [collisionProfile_zero,intervalIntegral.integral_zero] at h
  apply h.congr'
  filter_upwards [response_moving_positive u,response_moving_positive v] with N hu hv
  rw [collision_moment_eq_window k u v N hu hv]

end RHTower.BAGTrace
