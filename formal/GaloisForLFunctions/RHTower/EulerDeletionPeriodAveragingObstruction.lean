import GaloisForLFunctions.RHTower.EulerDeletionMobiusPeriodCovariance
import GaloisForLFunctions.RHTower.PrimeCountShell
import GaloisForLFunctions.RHTower.Sieve.ShortIntervalThetaEveryWindow

/-!
# Isolated prime variance and the failure of uniform period averaging

Every prime above half the channel cutoff is orthogonal to all other primitive
channels. Its positive covariance cannot be cancelled by the remaining signs.
-/
noncomputable section
set_option autoImplicit false
open Filter Topology ArithmeticFunction
open scoped BigOperators
namespace RHTower.DeletionPeriodGrowth
open DeletionPeriodCovariance

private def mu (m : ℕ) : ℝ := ((moebius m : ℤ) : ℝ)

/-- Complete unweighted period variance of the actual Möbius primitive. -/
def variance (N : ℕ) : ℝ := periodCovariance (Finset.Icc 1 N) mu

/-- Prime channels with no distinct positive multiple inside the cutoff. -/
def upperPrimes (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ N < 2*p)

/-- Exact remaining covariance after removing only those isolated prime channels. -/
def remainingVariance (N : ℕ) : ℝ :=
  periodCovariance (Finset.Icc 1 N) (fun m => if m ∈ upperPrimes N then 0 else mu m)

private theorem upperPrime_coprime {N p m : ℕ} (hp : p ∈ upperPrimes N)
    (hm : m ∈ Finset.Icc 1 N) (hne : m ≠ p) : p.Coprime m := by
  obtain ⟨_,hpPrime,hpN⟩ := Finset.mem_filter.mp hp
  apply hpPrime.coprime_iff_not_dvd.mpr
  intro hpm
  exact hne (Nat.eq_of_dvd_of_lt_two_mul (by have hm1 := (Finset.mem_Icc.mp hm).1; omega : m ≠ 0) hpm
    ((Finset.mem_Icc.mp hm).2.trans_lt hpN))

/-- The residual coefficient vector still has nonnegative complete covariance. -/
theorem remainingVariance_nonneg (N : ℕ) : 0 ≤ remainingVariance N := by
  apply periodCovariance_nonneg (P := N.factorial)
    (hpos := fun m hm => (Finset.mem_Icc.mp hm).1)
    (hP0 := Nat.factorial_pos N)
  intro m hm
  exact Nat.dvd_factorial (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2

/-- Exact orthogonal projection onto the isolated prime channels. Both signs and the
complete nonnegative covariance of the remaining coefficients are retained. -/
theorem variance_eq_upperPrime_diagonal_add_remaining (N : ℕ) :
    variance N = (∑ p ∈ upperPrimes N, ((p : ℝ)^2-1)/(12*(p : ℝ)^2))+
      remainingVariance N := by
  let v (m : ℕ) : ℝ := if m ∈ upperPrimes N then 0 else mu m
  let d (m : ℕ) : ℝ := ((m : ℝ)^2-1)/(m : ℝ)^2
  have he (m : ℕ) (hm : m ∈ Finset.Icc 1 N) (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      mu m*mu n*((Nat.gcd m n : ℝ)^2-1)/((m : ℝ)*(n : ℝ)) =
        (if m=n ∧ m ∈ upperPrimes N then d m else 0)+
          v m*v n*((Nat.gcd m n : ℝ)^2-1)/((m : ℝ)*(n : ℝ)) := by
    by_cases hmU : m ∈ upperPrimes N
    · by_cases hmn : m=n
      · subst n
        have hp := (Finset.mem_filter.mp hmU).2.1
        have hmu : mu m = -1 := by simp [mu,moebius_apply_prime hp]
        simp [hmU,v,d,hmu,pow_two]
      · have hc := upperPrime_coprime hmU hn (Ne.symm hmn)
        simp [hmn,hmU,hc.gcd_eq_one,v]
    · by_cases hnU : n ∈ upperPrimes N
      · have hmn : m ≠ n := by intro h; exact hmU (h ▸ hnU)
        have hc := upperPrime_coprime hnU hm hmn
        rw [Nat.gcd_comm, hc.gcd_eq_one]
        simp [hmU,hnU,v]
      · simp [hmU,hnU,v]
  have hd : (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
      if m=n ∧ m ∈ upperPrimes N then d m else 0) = ∑ p ∈ upperPrimes N, d p := by
    have hinner (m : ℕ) (hm : m ∈ Finset.Icc 1 N) :
        (∑ n ∈ Finset.Icc 1 N, if m=n ∧ m ∈ upperPrimes N then d m else 0) =
          if m ∈ upperPrimes N then d m else 0 := by
      by_cases hU : m ∈ upperPrimes N <;> simp [hU,hm]
    rw [Finset.sum_congr rfl hinner]
    have hsub : upperPrimes N ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
    have h := Finset.sum_subset hsub (f := fun m => if m ∈ upperPrimes N then d m else 0)
      (fun m hm hU => by simp [hU])
    exact h.symm.trans (Finset.sum_congr rfl (fun m hm => by simp [hm]))
  unfold variance periodCovariance
  rw [Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (he m hm))]
  simp_rw [Finset.sum_add_distrib]
  rw [mul_add,hd]
  have hdiag : (1/12 : ℝ)*(∑ p ∈ upperPrimes N, d p) =
      ∑ p ∈ upperPrimes N, ((p : ℝ)^2-1)/(12*(p : ℝ)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp [d]
    ring
  rw [hdiag]
  rfl

/-- Every isolated prime contributes at least one sixteenth to the full period variance. -/
theorem upperPrime_card_le_variance (N : ℕ) :
    ((upperPrimes N).card : ℝ)/16 ≤ variance N := by
  have hd (p : ℕ) (hp : p ∈ upperPrimes N) :
      (1/16 : ℝ) ≤ ((p : ℝ)^2-1)/(12*(p : ℝ)^2) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg ((p : ℝ)-2)]
  calc ((upperPrimes N).card : ℝ)/16 = ∑ p ∈ upperPrimes N, (1/16 : ℝ) := by simp; ring
       _ ≤ ∑ p ∈ upperPrimes N, ((p : ℝ)^2-1)/(12*(p : ℝ)^2) := Finset.sum_le_sum hd
       _ ≤ variance N := by
         rw [variance_eq_upperPrime_diagonal_add_remaining]
         linarith [remainingVariance_nonneg N]

private theorem upperPrime_card_eq_shell (N : ℕ) :
    (upperPrimes N).card = primeShellCard ((N : ℝ)/2) (N : ℝ) := by
  unfold primeShellCard
  rw [Nat.floor_natCast]
  apply congrArg Finset.card
  ext p
  simp only [upperPrimes, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hp1,hpN⟩,hp,hhalf⟩
    refine ⟨⟨?_,hpN⟩,hp⟩
    rw [Nat.floor_lt (by positivity)]
    have h : (N : ℝ) < 2*(p : ℝ) := by exact_mod_cast hhalf
    linarith
  · rintro ⟨⟨hfloor,hpN⟩,hp⟩
    have hhalf : (N : ℝ)/2 < (p : ℝ) := (Nat.floor_lt (by positivity)).mp hfloor
    refine ⟨⟨hp.pos,hpN⟩,hp,?_⟩
    exact_mod_cast (show (N : ℝ) < 2*(p : ℝ) by linarith)

private theorem rpow_three_quarters_eventually_le :
    ∀ᶠ N : ℕ in atTop, (N : ℝ)^((3 : ℝ)/4) ≤ (N : ℝ)/4 := by
  have hlim := (tendsto_rpow_neg_atTop (y := (1 : ℝ)/4) (by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have he := hlim.eventually (eventually_lt_nhds (show (0 : ℝ) < 1/4 by norm_num))
  filter_upwards [he,eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hp : (N : ℝ)^((3 : ℝ)/4) = (N : ℝ)*(N : ℝ)^(-((1 : ℝ)/4)) := by
    calc _ = (N : ℝ)^((1 : ℝ)+-((1 : ℝ)/4)) := by congr 1; norm_num
         _ = _ := by rw [Real.rpow_add hN0,Real.rpow_one]
  rw [hp]
  change (N : ℝ)^(-((1 : ℝ)/4)) < 1/4 at hN
  calc _ ≤ (N : ℝ)*(1/4) := mul_le_mul_of_nonneg_left hN.le hN0.le
       _ = _ := by ring

/-- Unconditional macroscopic lower bound for the complete uniform period variance. -/
theorem variance_eventually_lower :
    ∀ᶠ N : ℕ in atTop, (N : ℝ)/(524288*Real.log (N : ℝ)) ≤ variance N := by
  obtain ⟨X,hX,hwin⟩ := Sieve.exists_theta_window_lower (α := (3 : ℝ)/4) (by norm_num) (by norm_num)
  have hx := ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const
    (show (0 : ℝ) < 2 by norm_num)).eventually_ge_atTop X
  filter_upwards [hx,rpow_three_quarters_eventually_le,eventually_ge_atTop 4]
    with N hNX hpow hN4
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hw := hwin ((N : ℝ)/2) ((N : ℝ)/2) hNX (by positivity)
  rw [show (N : ℝ)/2+(N : ℝ)/2=(N : ℝ) by ring] at hw
  have hmass : (N : ℝ)/32768 ≤ Chebyshev.theta (N : ℝ)-Chebyshev.theta ((N : ℝ)/2) := by
    linarith
  have hcount := (primeShellCard_bounds (a := (N : ℝ)/2) (b := (N : ℝ))
    (by linarith) (by linarith)).1
  have hc : (N : ℝ)/(32768*Real.log (N : ℝ)) ≤ ((upperPrimes N).card : ℝ) := by
    calc _ = ((N : ℝ)/32768)/Real.log (N : ℝ) := by ring
         _ ≤ (Chebyshev.theta (N : ℝ)-Chebyshev.theta ((N : ℝ)/2))/Real.log (N : ℝ) :=
           div_le_div_of_nonneg_right hmass hlog.le
         _ ≤ (primeShellCard ((N : ℝ)/2) (N : ℝ) : ℝ) := hcount
         _ = _ := by rw [upperPrime_card_eq_shell]
  calc _ = ((N : ℝ)/(32768*Real.log (N : ℝ)))/16 := by ring
       _ ≤ ((upperPrimes N).card : ℝ)/16 := div_le_div_of_nonneg_right hc (by norm_num)
       _ ≤ variance N := upperPrime_card_le_variance N

/-- The exact mean of the uncentered square over one complete factorial period. -/
def periodAverage (N : ℕ) : ℝ :=
  (∑ k ∈ Finset.range N.factorial, ‖DeletionMobiusPrimitive.primitive N k‖^2)/(N.factorial : ℝ)

/-- Literal complete-period average, with the scalar mean and full covariance separated. -/
theorem periodAverage_eq (N : ℕ) :
    periodAverage N = ((Sieve.mertensM N-deningerHarmonicPartial N)/2)^2+variance N := by
  rw [periodAverage,mobius_primitive_factorial_energy]
  have hP : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  change (N.factorial : ℝ)*(((Sieve.mertensM N-deningerHarmonicPartial N)/2)^2+variance N)/
    (N.factorial : ℝ) = _
  field_simp

/-- The uncentered mean retains the entire nonnegative variance. -/
theorem variance_le_periodAverage (N : ℕ) : variance N ≤ periodAverage N := by
  rw [periodAverage_eq]
  nlinarith [sq_nonneg ((Sieve.mertensM N-deningerHarmonicPartial N)/2)]

private theorem variance_nonneg (N : ℕ) : 0 ≤ variance N :=
  (by positivity : (0 : ℝ) ≤ ((upperPrimes N).card : ℝ)/16).trans (upperPrime_card_le_variance N)

private theorem log_tendsto : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem nat_div_log_pow_tendsto (p : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ)/Real.log (N : ℝ)^p) atTop atTop := by
  have h0 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 p one_ne_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall : Tendsto (fun N : ℕ => Real.log (N : ℝ)^p/(N : ℝ)) atTop (𝓝 0) := by
    apply h0.congr
    intro N
    dsimp
    ring
  have hpos : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ)^p/(N : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
    exact div_pos (pow_pos (Real.log_pos hN1) p) (by linarith)
  have hwithin := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hsmall hpos
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  apply hinv.congr
  intro N
  change (Real.log (N : ℝ)^p/(N : ℝ))⁻¹ = _
  rw [inv_div]

/-- Uniform period variance grows beyond every fixed logarithmic power, without any zero hypothesis. -/
theorem variance_div_log_pow_tendsto (q : ℕ) :
    Tendsto (fun N : ℕ => variance N/Real.log (N : ℝ)^q) atTop atTop := by
  have hlower := (nat_div_log_pow_tendsto (q+1)).atTop_div_const
    (show (0 : ℝ) < 524288 by norm_num)
  apply tendsto_atTop_mono' atTop _ hlower
  filter_upwards [variance_eventually_lower,log_tendsto.eventually_ge_atTop 1] with N hN hlog
  calc ((N : ℝ)/Real.log (N : ℝ)^(q+1))/524288 =
         ((N : ℝ)/(524288*Real.log (N : ℝ)))/Real.log (N : ℝ)^q := by
         rw [pow_succ]
         ring
       _ ≤ _ := div_le_div_of_nonneg_right hN (pow_nonneg (by linarith) q)

/-- Even cofinal polynomial-log upper returns of the complete uniform variance are impossible. -/
theorem not_cofinally_log_bounded_variance :
    ¬ ∃ q : ℕ, ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ variance N ≤ B*Real.log (N : ℝ)^q := by
  rintro ⟨q,B,h⟩
  have he := (variance_div_log_pow_tendsto q).eventually_gt_atTop B
  obtain ⟨K,hK⟩ := eventually_atTop.mp (he.and (log_tendsto.eventually_ge_atTop 1))
  obtain ⟨N,hKN,hN⟩ := h K
  have hs := hK N hKN
  have hu : variance N/Real.log (N : ℝ)^q ≤ B :=
    (div_le_iff₀ (pow_pos (by linarith : 0 < Real.log (N : ℝ)) q)).mpr hN
  exact (not_le.mpr hs.1) hu

/-- The literal full-period uncentered average also cannot supply the EDQ logarithmic ceiling. -/
theorem not_cofinally_log_bounded_periodAverage :
    ¬ ∃ q : ℕ, ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ periodAverage N ≤ B*Real.log (N : ℝ)^q := by
  rintro ⟨q,B,h⟩
  apply not_cofinally_log_bounded_variance
  refine ⟨q,B,?_⟩
  intro K
  obtain ⟨N,hKN,hN⟩ := h K
  exact ⟨N,hKN,(variance_le_periodAverage N).trans hN⟩

private theorem modular_norm_div_tendsto_of_lower {G : ℕ → ℝ} (hG : ∀ N, 0 ≤ G N)
    (hbound : ∀ᶠ N : ℕ in atTop, (N : ℝ)/(524288*Real.log (N : ℝ)) ≤ G N) :
    Tendsto (fun N : ℕ => ‖bdMobiusModularApproximantVec N‖^2/G N) atTop (𝓝 0) := by
  have hlim := (DeletionMobiusGlobal.modular_norm_log_pow_div_tendsto_zero 1).const_mul 524288
  simp only [pow_one,mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · exact Eventually.of_forall (fun N => div_nonneg (sq_nonneg _) (hG N))
  · filter_upwards [hbound,eventually_ge_atTop 2] with N hN hN2
    have hN1 : (1 : ℝ) < N := by exact_mod_cast hN2
    have hN0 : (0 : ℝ) < N := by linarith
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
    have hden : 0 < (524288 : ℝ)*Real.log (N : ℝ) := by positivity
    have hGN : 0 < G N := (div_pos hN0 hden).trans_le hN
    have hmul := (div_le_iff₀ hden).mp hN
    calc ‖bdMobiusModularApproximantVec N‖^2/G N ≤
           (524288*‖bdMobiusModularApproximantVec N‖^2*Real.log (N : ℝ))/(N : ℝ) := by
           apply (div_le_div_iff₀ hGN hN0).mpr
           nlinarith [mul_le_mul_of_nonneg_left hmul (sq_nonneg ‖bdMobiusModularApproximantVec N‖)]
         _ = _ := by ring

/-- The actual carrier energy is asymptotically negligible compared with its uniform period variance. -/
theorem modular_norm_sq_div_variance_tendsto_zero :
    Tendsto (fun N : ℕ => ‖bdMobiusModularApproximantVec N‖^2/variance N) atTop (𝓝 0) :=
  modular_norm_div_tendsto_of_lower variance_nonneg variance_eventually_lower

/-- Uniform complete-period averaging and the actual weighted carrier are not asymptotically comparable. -/
theorem modular_norm_sq_div_periodAverage_tendsto_zero :
    Tendsto (fun N : ℕ => ‖bdMobiusModularApproximantVec N‖^2/periodAverage N) atTop (𝓝 0) :=
  modular_norm_div_tendsto_of_lower (fun N => (variance_nonneg N).trans (variance_le_periodAverage N))
    (variance_eventually_lower.mono (fun N hN => hN.trans (variance_le_periodAverage N)))

end RHTower.DeletionPeriodGrowth
end
