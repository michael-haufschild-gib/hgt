import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFixedPrimeCutAfterSummingConductors

/-!
# The first prime moment seen by the integrated conductor spline

Interchanging the moving interval and the spectral weight, as in the
discrepancy argument of El Kaouni (arXiv:2610.42022, §3.4), rewrites the
whole conductor tail as one dilation average of the first prime moment.
The original spline has zero mean, so the continuous quadratic prime
background cancels exactly before any estimate.
-/

noncomputable section
open Finset MeasureTheory Complex
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.ConductorMoment

/-- Density for the dilation average of a first moment. -/
def density (t : ℝ) : ℂ := squarePrimeWeight t/(t:ℂ)^2

private theorem density_integrable : IntegrableOn density (Set.Ioi 0) := by
  simpa only [MellinConvergent,show (-1:ℂ)-1=-(2:ℂ) by norm_num,Complex.cpow_neg,
    Complex.cpow_two,smul_eq_mul,density,div_eq_mul_inv,mul_comm] using
    mellinConvergent_squarePrimeWeight (-1)

/-- The first moment of a finite row, with the endpoint counted in full. -/
def firstMoment (F : Finset ℕ) (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ p ∈ F, if (p : ℝ) ≤ x then (p:ℂ)*a p else 0

/-- Dilation observation at terminal scale X. -/
def reading (X : ℝ) (M : ℝ → ℂ) : ℂ := ∫ t in Set.Ioi (0:ℝ), density t*M (X*t)

private theorem term_integrable {X : ℝ} (hX : 0 < X) (p : ℕ) (a : ℕ → ℂ) :
    IntegrableOn (fun t : ℝ => density t*(if (p : ℝ) ≤ X*t then (p:ℂ)*a p else 0)) (Set.Ioi 0) := by
  have hi := (density_integrable.mul_const ((p:ℂ)*a p)).indicator
    (measurableSet_Ici (a := (p:ℝ)/X))
  refine hi.congr_fun (fun t _ => ?_) measurableSet_Ioi
  by_cases he : (p:ℝ)/X ≤ t
  · rw [Set.indicator_of_mem (show t ∈ Set.Ici ((p:ℝ)/X) from he), if_pos (by
      simpa only [mul_comm t X] using (div_le_iff₀ hX).mp he)]
  · rw [Set.indicator_of_notMem (show t ∉ Set.Ici ((p:ℝ)/X) from he), if_neg (by
      intro h; exact he ((div_le_iff₀ hX).mpr (by simpa only [mul_comm t X] using h))),mul_zero]

private theorem firstMoment_integrable {X : ℝ} (hX : 0 < X) (F : Finset ℕ) (a : ℕ → ℂ) :
    IntegrableOn (fun t => density t * firstMoment F a (X*t)) (Set.Ioi 0) := by
  simpa only [firstMoment,Finset.mul_sum] using
    (integrable_finsetSum F (fun p _ => term_integrable hX p a))

/-- Exact interchange of a sharp finite row with the signed spline. No
discrepancy or total variation estimate enters. -/
theorem finite_spline_reading {X : ℝ} (hX : 0 < X) (F : Finset ℕ) (hF : ∀ p ∈ F, 0 < p)
    (a : ℕ → ℂ) :
    (X:ℂ)*∑ p ∈ F, a p*squarePrefixPrimeWeight ((p:ℝ)/X) = reading X (firstMoment F a) := by
  rw [reading,Finset.mul_sum]
  simp only [firstMoment, Finset.mul_sum]
  rw [integral_finsetSum F (fun p _ => term_integrable hX p a)]
  apply sum_congr rfl
  intro p hp
  have hv : 0 < (p:ℝ)/X := div_pos (Nat.cast_pos.mpr (hF p hp)) hX
  rw [squarePrefixPrimeWeight_tail hv]
  have hpt (t : ℝ) :
      density t*(if (p:ℝ) ≤ X*t then (p:ℂ)*a p else 0) =
      (Set.Ici ((p:ℝ)/X)).indicator (fun t => ((p:ℂ)*a p)*density t) t := by
    by_cases he : (p:ℝ)/X ≤ t
    · rw [Set.indicator_of_mem he,if_pos (by simpa only [mul_comm t X] using (div_le_iff₀ hX).mp he),mul_comm]
    · rw [Set.indicator_of_notMem he,if_neg (by intro h; exact he ((div_le_iff₀ hX).mpr
        (by simpa only [mul_comm t X] using h))),mul_zero]
  simp_rw [hpt]
  rw [integral_indicator measurableSet_Ici,Measure.restrict_restrict_of_subset
    (show Set.Ici ((p:ℝ)/X) ⊆ Set.Ioi 0 from fun _ ht => hv.trans_le ht),integral_const_mul,
    Complex.ofReal_div,Complex.ofReal_natCast]
  change _ = ((p:ℂ)*a p)*∫ t in Set.Ici ((p:ℝ)/X), squarePrimeWeight t/(t:ℂ)^2
  field_simp [Complex.ofReal_ne_zero.mpr hX.ne'] <;> ring

/-- Every quadratic background has zero reading. Its signed contributions
cancel over the complete support of the original conductor spline. -/
theorem quadratic_background (A : ℂ) (X : ℝ) :
    reading X (fun x => A*(x:ℂ)^2) = 0 := by
  have he (t : ℝ) (ht : t ∈ Set.Ioi (0:ℝ)) :
      density t*(A*((X*t:ℝ):ℂ)^2) = (A*(X:ℂ)^2)*squarePrimeWeight t := by
    rw [density,Complex.ofReal_mul,mul_pow]
    field_simp [Complex.ofReal_ne_zero.mpr (show 0 < t from ht).ne'] <;> ring
  rw [reading,setIntegral_congr_fun measurableSet_Ioi he,integral_const_mul,squarePrimeWeight_mean_zero,mul_zero]

private theorem integrable_background (A : ℂ) (X : ℝ) :
    IntegrableOn (fun t : ℝ => density t*(A*((X*t:ℝ):ℂ)^2)) (Set.Ioi 0) := by
  have hs : IntegrableOn squarePrimeWeight (Set.Ioi 0) := by
    simpa only [MellinConvergent,sub_self,Complex.cpow_zero,one_smul] using mellinConvergent_squarePrimeWeight 1
  refine (hs.const_mul (A*(X:ℂ)^2)).congr_fun (fun t ht => ?_) measurableSet_Ioi
  rw [density,Complex.ofReal_mul,mul_pow]
  field_simp [Complex.ofReal_ne_zero.mpr (show 0 < t from ht).ne'] <;> ring

/-- Subtraction of the continuum first moment can be performed inside the
actual measurement, at every terminal scale. -/
theorem finite_spline_centered {X : ℝ} (hX : 0 < X) (F : Finset ℕ) (hF : ∀ p ∈ F, 0 < p)
    (a : ℕ → ℂ) (A : ℂ) :
    (X:ℂ)*∑ p ∈ F, a p*squarePrefixPrimeWeight ((p:ℝ)/X) =
      reading X (fun x => firstMoment F a x-A*(x:ℂ)^2) := by
  rw [finite_spline_reading hX F hF,reading,reading]
  simp only [mul_sub]
  rw [integral_sub (firstMoment_integrable hX F a) (integrable_background A X)]
  change _ = _ - reading X (fun x => A*(x:ℂ)^2)
  rw [quadratic_background, sub_zero]

/-- The literal centered conductor tail is a quadratic-background-free
reading of primes strictly above the cutoff, plus its fixed low-prime
counterterm. -/
theorem centered_tail_reading {N : ℕ} (hN : 0 < N) (K : ℕ) (A : ℂ) :
    let H := ⌊((N:ℝ)/squareConductorBVWindow.lower)^2⌋₊
    centeredFixedPrimeTail N K =
      reading ((N:ℝ)^2) (fun x => firstMoment ((ordinaryPrimeLags H).filter (K < ·))
        (fun p => (Real.log p:ℂ)) x - A*(x:ℂ)^2) +
      ((innerPrimeSlope*((K:ℝ)*(K+1)/2):ℝ):ℂ) := by
  intro H
  have hp : ∀ p ∈ (ordinaryPrimeLags H).filter (K < ·), 0 < p := by
    intro p h
    exact (mem_filter.mp (mem_filter.mp h).1).2.pos
  simpa only [centeredFixedPrimeTail,H,Complex.ofReal_pow,Complex.ofReal_natCast] using
    congrArg (· + ((innerPrimeSlope*((K:ℝ)*(K+1)/2):ℝ):ℂ))
      (finite_spline_centered (X := (N:ℝ)^2) (by positivity) _ hp (fun p => (Real.log p:ℂ)) A)

/-- The untruncated first ordinary-prime moment. -/
def primeMoment (x : ℝ) : ℂ :=
  ∑ p ∈ ordinaryPrimeLags ⌊x⌋₊, (p:ℂ)*(Real.log p:ℂ)

private theorem moment_eq {H : ℕ} {x : ℝ} (hx : 0 ≤ x) (hH : ⌊x⌋₊ ≤ H) :
    firstMoment (ordinaryPrimeLags H) (fun p => (Real.log p:ℂ)) x = primeMoment x := by
  rw [firstMoment, ← sum_filter,primeMoment]
  congr 1
  ext p
  simp only [ordinaryPrimeLags,mem_filter,mem_Icc,Nat.le_floor_iff hx]
  constructor
  · rintro ⟨⟨⟨ha,_⟩,hp⟩,h⟩; exact ⟨⟨ha,h⟩,hp⟩
  · rintro ⟨⟨ha,h⟩,hp⟩; exact ⟨⟨⟨ha,((Nat.le_floor_iff hx).mpr h).trans hH⟩,hp⟩,h⟩

private theorem support_below_terminal {N : ℕ} {t : ℝ}
    (ht : t ≤ Real.exp (8+Real.log 4)) :
    (N:ℝ)^2*t ≤ ((N:ℝ)/squareConductorBVWindow.lower)^2 := by
  have hlog : Real.log 4 ≤ 4-1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h16 := ht.trans (Real.exp_le_exp.mpr (by linarith only [hlog] : 8+Real.log 4 ≤ 16))
  have hs : squareConductorBVWindow.lower^2 = Real.exp (-16) := by
    change Real.exp (-8)^2=_
    rw [sq, ← Real.exp_add]; norm_num
  rw [div_pow,le_div_iff₀ (sq_pos_of_pos squareConductorBVWindow.lower_pos),hs, mul_assoc]
  have ht1 : t*Real.exp (-16) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv,div_le_one (Real.exp_pos _)]
    exact h16
  exact mul_le_of_le_one_right (sq_nonneg _) ht1

private theorem complete_reading {N : ℕ} (A : ℂ) :
    let H := ⌊((N:ℝ)/squareConductorBVWindow.lower)^2⌋₊
    reading ((N:ℝ)^2) (fun x => firstMoment (ordinaryPrimeLags H) (fun p => (Real.log p:ℂ)) x-A*(x:ℂ)^2) =
    reading ((N:ℝ)^2) (fun x => primeMoment x-A*(x:ℂ)^2) := by
  intro H
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  by_cases hs : t ∈ Set.Icc (Real.exp (-8)) (Real.exp (8+Real.log 4))
  · rw [moment_eq (mul_nonneg (sq_nonneg _) (show 0 < t from ht).le)
      (Nat.floor_mono (support_below_terminal hs.2))]
  · simp only [density,squarePrimeWeight_zero_outside ht hs,zero_div,zero_mul]

/-- Exact first-moment error formula with the quadratic main term removed.
Only the discrete error at K remains outside the integral. -/
theorem centered_tail_first_moment {N K : ℕ} (hN : 0 < N)
    (hK : (K:ℝ) ≤ Real.exp (-8)*(N:ℝ)^2) (A : ℂ) :
    centeredFixedPrimeTail N K =
      reading ((N:ℝ)^2) (fun x => primeMoment x-A*(x:ℂ)^2) -
        (innerPrimeSlope:ℂ)*(primeMoment K - (K:ℂ)*(K+1)/2) := by
  let H := ⌊((N:ℝ)/squareConductorBVWindow.lower)^2⌋₊
  let f := fun p : ℕ => (Real.log p:ℂ)*squarePrefixPrimeWeight ((p:ℝ)/(N:ℝ)^2)
  have hKH : K ≤ H := by
    apply Nat.le_floor
    have he : Real.exp (-8) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    refine hK.trans ((mul_le_of_le_one_left (sq_nonneg _) he).trans ?_)
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (le_div_self (Nat.cast_nonneg _)
      squareConductorBVWindow.lower_pos he) 2
  have hset : (ordinaryPrimeLags H).filter (fun k => ¬K < k) = ordinaryPrimeLags K := by
    ext k
    simp only [ordinaryPrimeLags,mem_filter,mem_Icc,not_lt]
    omega
  have hsplit := sum_filter_add_sum_filter_not (ordinaryPrimeLags H) (K < ·) f
  rw [hset] at hsplit
  have hfull := finite_spline_centered (X := (N:ℝ)^2) (by positivity) (ordinaryPrimeLags H)
    (fun p hp => (mem_filter.mp hp).2.pos) (fun p => (Real.log p:ℂ)) A
  rw [complete_reading A] at hfull
  simp only [Complex.ofReal_pow,Complex.ofReal_natCast] at hfull
  change (N:ℂ)^2*(∑ p ∈ ordinaryPrimeLags H, f p) = _ at hfull
  rw [← hsplit,mul_add] at hfull
  have hlo := fixed_inner_prime_price hN hK
  change (N:ℂ)^2*(∑ p ∈ ordinaryPrimeLags K, f p) = _ at hlo
  rw [hlo] at hfull
  change (N:ℂ)^2*(∑ p ∈ (ordinaryPrimeLags H).filter (K < ·), f p) + _ = _
  simp only [primeMoment,Nat.floor_natCast,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_ofNat,Complex.ofReal_natCast]
  linear_combination hfull

/-- Each multiplicative power is read at its exact Mellin frequency.
This includes complex oscillations with arbitrary real frequency. -/
theorem power_reading (s : ℂ) {X : ℝ} (hX : 0 < X) :
    reading X (fun x => (x:ℂ)^s) = (X:ℂ)^s * mellin squarePrimeWeight (s-1) := by
  rw [reading,mellin, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht' : 0 < t := ht
  have htz := Complex.ofReal_ne_zero.mpr ht'.ne'
  rw [density,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hX.le ht'.le s, smul_eq_mul,
    show s-1-1=s+(-(2:ℂ)) by ring, Complex.cpow_add htz,Complex.cpow_neg,
    Complex.cpow_two]
  ring

#print axioms finite_spline_reading
#print axioms quadratic_background
#print axioms finite_spline_centered
#print axioms centered_tail_reading
#print axioms centered_tail_first_moment
#print axioms power_reading
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.ConductorMoment
