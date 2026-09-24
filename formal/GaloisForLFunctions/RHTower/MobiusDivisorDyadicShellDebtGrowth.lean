import GaloisForLFunctions.RHTower.MobiusDivisorDilationMeanRenewal
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount

/-!
# Dyadic prime-shell growth of the physical fixed-core debt

For the processed core consisting of primes in `(2N, 3N]`, the continuous
head has an exact one-prime expansion throughout a macroscopic interval near
`4N`: products of two shell primes are too large to contribute. Each
one-prime term has the same negative sign and a uniform square-root floor.
The physical inverse-cube mean therefore grows at least like the square of
the window's prime count divided by `N`. The squarefree density factor stays
above half its unprocessed value, so the normalized fixed-core debt diverges.

This is a changing-core obstruction to a uniform fixed-core debt budget. It
does not exclude compensation by smaller processed primes at finite cutoff.
-/

noncomputable section
open Finset Set Filter Topology MeasureTheory
namespace RHTower

private theorem head_eq_unit_below_core (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {x : ℝ} (hx : ∀ p ∈ P, x ≤ p) :
    mobiusDivisorContinuousHead P x = divisorContinuousUnitHead x := by
  induction P using Finset.induction_on with
  | empty => simp [mobiusDivisorContinuousHead]
  | @insert p P hpP ih =>
    have hp : p.Prime := hP p (mem_insert_self p P)
    have hPP : ∀ q ∈ P, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    rw [mobiusDivisorContinuousHead_insert P hPP hp hpP]
    rw [mobiusDivisorContinuousHead_eq_zero P ((div_le_one (by exact_mod_cast hp.pos)).mpr
      (hx p (mem_insert_self p P)))]
    simpa using ih hPP (fun q hq => hx q (mem_insert_of_mem hq))

private theorem head_eq_unit_sub_prime_shell (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {x : ℝ}
    (hpair : ∀ p ∈ P, ∀ q ∈ P, x ≤ (p:ℝ)*q) :
    mobiusDivisorContinuousHead P x = divisorContinuousUnitHead x -
      ∑ p ∈ P, Real.sqrt p * divisorContinuousUnitHead (x/p) := by
  induction P using Finset.induction_on with
  | empty => simp [mobiusDivisorContinuousHead]
  | @insert p P hpP ih =>
    have hp : p.Prime := hP p (mem_insert_self p P)
    have hPP : ∀ q ∈ P, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    have hbelow : mobiusDivisorContinuousHead P (x/p) =
        divisorContinuousUnitHead (x/p) := by
      apply head_eq_unit_below_core P hPP
      intro q hq
      exact (div_le_iff₀ (by exact_mod_cast hp.pos)).mpr
        (hpair q (mem_insert_of_mem hq) p (mem_insert_self p P))
    rw [mobiusDivisorContinuousHead_insert P hPP hp hpP,
      ih hPP (fun q hq r hr => hpair q (mem_insert_of_mem hq) r (mem_insert_of_mem hr)),
      hbelow, sum_insert hpP]
    ring

private theorem first_defect_floor : (1/10:ℝ) ≤ primeFreeDivisorDefect 1 := by
  have h := (harmonic_mascheroni_half_bounds (n := 4) (by norm_num)).2
  norm_num [harmonic, Finset.sum_range_succ, Real.log_four_eq] at h
  norm_num [primeFreeDivisorDefect]
  linarith [Real.log_two_lt_d9]

private theorem shell_term_floor {N p : ℕ} (hN : 1 ≤ N)
    (hp : p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N))
    {x : ℝ} (hxl : (7/2:ℝ)*N ≤ x) (hxu : x ≤ (15/4:ℝ)*N) :
    Real.sqrt N/200 ≤ Real.sqrt p * divisorContinuousUnitHead (x/p) := by
  obtain ⟨hprime,hpl,hpu⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hp0 : (0:ℝ) < p := by exact_mod_cast hprime.pos
  have hplR : (2:ℝ)*N < p := by exact_mod_cast hpl
  have hpuR : (p:ℝ) ≤ 3*N := by exact_mod_cast hpu
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x/p := (le_div_iff₀ hp0).mpr (by linarith)
  have hx2 : x/p ≤ 2 := (div_le_iff₀ hp0).mpr (by linarith)
  have hfirst : divisorContinuousUnitHead (x/p) =
      (Real.sqrt (x/p)-1)*primeFreeDivisorDefect 1 := by
    rw [divisorContinuousUnitHead_between (k := 1) le_rfl (by simpa using hx1)
      (by simpa using hx2)]
    simp [divisorUnsignedDilationChannel]
  have hroot : Real.sqrt p*(Real.sqrt (x/p)-1) = Real.sqrt x-Real.sqrt p := by
    rw [Real.sqrt_div hx0]
    have hs : Real.sqrt (p:ℝ) ≠ 0 := (Real.sqrt_pos.mpr hp0).ne'
    field_simp
  have hrootp : Real.sqrt p ≤ (7/4:ℝ)*Real.sqrt N := by
    have hpSq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p)
    have hNSq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    nlinarith [Real.sqrt_nonneg (p:ℝ), Real.sqrt_nonneg (N:ℝ)]
  have hrootx : (9/5:ℝ)*Real.sqrt N ≤ Real.sqrt x := by
    have hxSq := Real.sq_sqrt hx0
    have hNSq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (N:ℝ)]
  have hgap : Real.sqrt N/20 ≤ Real.sqrt x-Real.sqrt p := by linarith
  have h1 := mul_le_mul_of_nonneg_right first_defect_floor
    (show 0 ≤ Real.sqrt N/20 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hgap
    (show 0 ≤ primeFreeDivisorDefect 1 by linarith [first_defect_floor])
  rw [hfirst]
  calc
    Real.sqrt N/200 ≤ primeFreeDivisorDefect 1 * (Real.sqrt x-Real.sqrt p) := by
      nlinarith only [h1,h2]
    _ = Real.sqrt p * ((Real.sqrt (x/p)-1)*primeFreeDivisorDefect 1) := by
      rw [← hroot]
      ring

private theorem shell_head_floor (N : ℕ) (hN : 1 ≤ N)
    {x : ℝ} (hxl : (7/2:ℝ)*N ≤ x) (hxu : x ≤ (15/4:ℝ)*N) :
    mobiusDivisorContinuousHead
        (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) x ≤
      (6/5:ℝ)*Real.sqrt N -
        ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)*
          Real.sqrt N/200 := by
  let P := GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)
  have hprime : ∀ p ∈ P, p.Prime := fun p hp =>
    (GaloisForLFunctions.HTGeometry.mem_primesInIoc hp).1
  have hpair : ∀ p ∈ P, ∀ q ∈ P, x ≤ (p:ℝ)*q := by
    intro p hp q hq
    have hp2 := (GaloisForLFunctions.HTGeometry.mem_primesInIoc hp).2.1
    have hq2 := (GaloisForLFunctions.HTGeometry.mem_primesInIoc hq).2.1
    have hpr : (2:ℝ)*N ≤ p := by exact_mod_cast hp2.le
    have hqr : (2:ℝ)*N ≤ q := by exact_mod_cast hq2.le
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
    have hmul : ((2:ℝ)*N)*((2:ℝ)*N) ≤ (p:ℝ)*q :=
      mul_le_mul hpr hqr (by positivity) (by positivity)
    nlinarith [hmul]
  rw [head_eq_unit_sub_prime_shell P hprime hpair]
  have hsum : (P.card:ℝ)*Real.sqrt N/200 ≤
      ∑ p ∈ P, Real.sqrt p*divisorContinuousUnitHead (x/p) := by
    calc
      _ = ∑ _p ∈ P, Real.sqrt N/200 := by
        simp only [sum_const, nsmul_eq_mul]
        ring
      _ ≤ _ := sum_le_sum (fun p hp => shell_term_floor hN hp hxl hxu)
  have hx0 : 0 ≤ x := by
    have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
    linarith
  have hroot : Real.sqrt x ≤ 2*Real.sqrt N := by
    have hxSq := Real.sq_sqrt hx0
    have hNSq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (N:ℝ)]
  have hu := divisorContinuousUnitHead_le_sqrt x
  dsimp only [P] at hsum ⊢
  linarith only [hsum, hroot, hu]

private theorem shell_head_negative (N : ℕ) (hN : 1 ≤ N)
    (hcard : 480 ≤ (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card)
    {x : ℝ} (hxl : (7/2:ℝ)*N ≤ x) (hxu : x ≤ (15/4:ℝ)*N) :
    mobiusDivisorContinuousHead
        (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) x ≤
      -((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)*
        Real.sqrt N/400 := by
  have h := shell_head_floor N hN hxl hxu
  have hk : (480:ℝ) ≤
      (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card := by
    exact_mod_cast hcard
  have hs : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  nlinarith only [h,hk,hs, mul_nonneg (show (0:ℝ) ≤
    ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)-480 by linarith) hs]

private theorem shell_mean_lower_raw (N : ℕ) (hN : 1 ≤ N)
    (hcard : 480 ≤ (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card) :
    (((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)*
        Real.sqrt N/400)^2 / (4*(N:ℝ))^3 * ((N:ℝ)/4) ≤
      mobiusDivisorDilationMean
        (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) 1 := by
  let P := GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)
  let a : ℝ := (7/2:ℝ)*N
  let b : ℝ := (15/4:ℝ)*N
  let C : ℝ := ((P.card:ℝ)*Real.sqrt N/400)^2 / (4*(N:ℝ))^3
  let f : ℝ → ℝ := fun x => (mobiusDivisorContinuousHead P x)^2/x^3
  have hNr : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hab : a ≤ b := by dsimp [a,b]; linarith
  have ha1 : 1 < a := by dsimp [a]; linarith
  have hset : Ioc a b ⊆ Ioi (1:ℝ) := by
    intro x hx
    exact ha1.trans hx.1
  have hint : IntegrableOn f (Ioi (1:ℝ)) := by
    simpa only [f, one_mul, pow_two] using
      integrable_mobiusDivisorDilationMean_kernel P
        (by norm_num : (0:ℝ)<1)
  have hpt : ∀ x ∈ Ioc a b, C ≤ f x := by
    intro x hx
    have hxl : (7/2:ℝ)*N ≤ x := by exact hx.1.le
    have hxu : x ≤ (15/4:ℝ)*N := hx.2
    have hhead := shell_head_negative N hN hcard hxl hxu
    have hx0 : 0 < x := lt_trans zero_lt_one (ha1.trans hx.1)
    have hx4 : x ≤ 4*(N:ℝ) := by linarith
    have hden : x^3 ≤ (4*(N:ℝ))^3 := pow_le_pow_left₀ hx0.le hx4 3
    have hsq : ((P.card:ℝ)*Real.sqrt N/400)^2 ≤
        (mobiusDivisorContinuousHead P x)^2 := by
      have hK : 0 ≤ (P.card:ℝ)*Real.sqrt N/400 := by positivity
      have hh : (P.card:ℝ)*Real.sqrt N/400 ≤
          -mobiusDivisorContinuousHead P x := by
        dsimp only [P] at hhead ⊢
        linarith only [hhead]
      have hpow := pow_le_pow_left₀ hK hh 2
      nlinarith only [hpow]
    have hmul : ((P.card:ℝ)*Real.sqrt N/400)^2*x^3 ≤
        (mobiusDivisorContinuousHead P x)^2*(4*(N:ℝ))^3 :=
      mul_le_mul hsq hden (by positivity) (by positivity)
    exact (div_le_div_iff₀ (by positivity : 0 < (4*(N:ℝ))^3)
      (pow_pos hx0 3)).mpr hmul
  have hmono : C*(b-a) ≤ ∫ x in Ioc a b, f x := by
    have hconst : IntegrableOn (fun _ : ℝ => C) (Ioc a b) :=
      integrableOn_const measure_Ioc_lt_top.ne
    have hm := setIntegral_mono_on hconst
      (hint.mono_set hset) measurableSet_Ioc hpt
    have hvol : (volume : Measure ℝ).real (Ioc a b) = b-a := by
      simp [MeasureTheory.measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal, sub_nonneg.mpr hab]
    simpa only [setIntegral_const, smul_eq_mul, hvol, mul_comm] using hm
  have hmass : (∫ x in Ioc a b, f x) ≤ ∫ x in Ioi (1:ℝ), f x := by
    refine setIntegral_mono_set hint ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact div_nonneg (sq_nonneg _) (pow_nonneg (le_trans zero_le_one hx.le) 3)
    · exact Filter.Eventually.of_forall (fun x hx => hset hx)
  have hlen : b-a=(N:ℝ)/4 := by dsimp [a,b]; ring
  rw [hlen] at hmono
  change C*((N:ℝ)/4) ≤ _ at hmono
  exact hmono.trans (by simpa [mobiusDivisorDilationMean, f, one_mul,
    pow_two] using hmass)

private theorem shell_mean_lower (N : ℕ) (hN : 1 ≤ N)
    (hcard : 480 ≤ (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card) :
    ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)^2 /
      (40960000*(N:ℝ)) ≤
    mobiusDivisorDilationMean
      (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) 1 := by
  have h := shell_mean_lower_raw N hN hcard
  have hN0 : (N:ℝ) ≠ 0 := by exact_mod_cast (show N≠0 by omega)
  have heq :
      (((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)*
          Real.sqrt N/400)^2 / (4*(N:ℝ))^3 * ((N:ℝ)/4) =
        ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)^2 /
          (40960000*(N:ℝ)) := by
    rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)]
    field_simp [hN0]
    ring
  rwa [heq] at h

private theorem prod_one_sub_ge_one_sub_sum (S : Finset ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ p ∈ S, 0 ≤ a p) (ha1 : ∀ p ∈ S, a p ≤ 1) :
    1 - ∑ p ∈ S, a p ≤ ∏ p ∈ S, (1-a p) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hpS ih =>
    have ha0p := ha0 p (mem_insert_self p S)
    have ha1p := ha1 p (mem_insert_self p S)
    have ha0S : ∀ q ∈ S, 0 ≤ a q := fun q hq => ha0 q (mem_insert_of_mem hq)
    have ha1S : ∀ q ∈ S, a q ≤ 1 := fun q hq => ha1 q (mem_insert_of_mem hq)
    have hsum : 0 ≤ ∑ q ∈ S, a q := sum_nonneg ha0S
    have hm := mul_le_mul_of_nonneg_left (ih ha0S ha1S) (by linarith : 0 ≤ 1-a p)
    rw [sum_insert hpS, prod_insert hpS]
    nlinarith only [hm, mul_nonneg ha0p hsum]

private theorem shell_density_lower (N : ℕ) (hN : 1 ≤ N) :
    (1/2:ℝ) ≤ ∏ p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N),
      (p:ℝ)/(p+1) := by
  let P := GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)
  have hcard : P.card ≤ N := by
    calc
      P.card ≤ (Finset.Ioc (2*N) (3*N)).card := by
        exact card_le_card (Finset.filter_subset _ _)
      _ = N := by simp; omega
  have hcardR : (P.card:ℝ) ≤ N := by exact_mod_cast hcard
  let a : ℕ → ℝ := fun p => 1/((p:ℝ)+1)
  have ha0 : ∀ p ∈ P, 0 ≤ a p := by intro p hp; positivity
  have ha1 : ∀ p ∈ P, a p ≤ 1 := by
    intro p hp
    dsimp [a]
    have hp0 : (0:ℝ) ≤ p := by positivity
    exact (div_le_iff₀ (by positivity : (0:ℝ) < p+1)).mpr (by linarith)
  have hsum : (∑ p ∈ P, a p) ≤ (P.card:ℝ)/(2*(N:ℝ)+1) := by
    calc
      _ ≤ ∑ _p ∈ P, (1:ℝ)/(2*(N:ℝ)+1) := by
        apply sum_le_sum
        intro p hp
        have hpl := (GaloisForLFunctions.HTGeometry.mem_primesInIoc hp).2.1
        have hpR : (2:ℝ)*N ≤ p := by exact_mod_cast hpl.le
        exact (one_div_le_one_div_of_le (by positivity : (0:ℝ)<2*(N:ℝ)+1)
          (by linarith : 2*(N:ℝ)+1 ≤ (p:ℝ)+1))
      _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring
  have hsumHalf : (∑ p ∈ P, a p) ≤ (1/2:ℝ) := by
    apply hsum.trans
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*(N:ℝ)+1)).mpr
    linarith
  have hprod := prod_one_sub_ge_one_sub_sum P a ha0 ha1
  have heq : (∏ p ∈ P, (1-a p)) = ∏ p ∈ P, (p:ℝ)/(p+1) := by
    apply prod_congr rfl
    intro p hp
    dsimp [a]
    have hd : (p:ℝ)+1 ≠ 0 := by positivity
    field_simp
    ring
  rw [heq] at hprod
  dsimp only [P] at hprod ⊢
  linarith only [hprod, hsumHalf]

private theorem eventually_shell_card_lower :
    ∀ᶠ N : ℕ in atTop,
      ((3/2:ℝ)-1)/2 * (((2*N:ℕ):ℝ)/Real.log (2*N:ℕ)) ≤
        ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ) := by
  have hcast : Tendsto (fun N : ℕ => 2*(N:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hcount := hcast.eventually
    (GaloisForLFunctions.HTGeometry.eventually_primeCount_window_ge
      (K := (3:ℝ)/2) (by norm_num))
  filter_upwards [hcount, eventually_ge_atTop (1:ℕ)] with N hc hN
  have harg : (3/2:ℝ)*(2*(N:ℝ))=(3*N:ℕ) := by push_cast; ring
  have htwo : 2*(N:ℝ)=((2*N:ℕ):ℝ) := by push_cast; rfl
  rw [harg, htwo, Nat.floor_natCast, Nat.floor_natCast] at hc
  have hcard := GaloisForLFunctions.HTGeometry.card_primesInIoc
    (show 2*N ≤ 3*N by omega)
  rw [← hcard] at hc
  exact hc

private theorem sqrt_log_double_tendsto :
    Tendsto (fun N : ℕ => Real.sqrt N/(320*Real.log (2*(N:ℝ)))) atTop atTop := by
  have hzero : Tendsto (fun x : ℝ => Real.log x/Real.sqrt x) atTop (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := 1/2) (by norm_num)).tendsto_div_nhds_zero
  have hwithin : Tendsto (fun x : ℝ => Real.log x/Real.sqrt x) atTop
      (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hzero
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (Real.sqrt_pos.mpr (by linarith))
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  have hr : Tendsto (fun x : ℝ => Real.sqrt x/Real.log x) atTop atTop := by
    exact hinv.congr (fun x => by
      change (Real.log x/Real.sqrt x)⁻¹=Real.sqrt x/Real.log x
      rw [inv_div])
  have hcast : Tendsto (fun N : ℕ => 2*(N:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have h := (hr.comp hcast).const_mul_atTop
    (show (0:ℝ)<1/(320*Real.sqrt 2) by positivity)
  convert h using 1
  funext N
  simp only [Function.comp_def, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  field_simp

theorem tendsto_shell_card_div_sqrt :
    Tendsto (fun N : ℕ =>
      ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)/
        Real.sqrt N) atTop atTop := by
  have hbound : ∀ᶠ N : ℕ in atTop,
      Real.sqrt N/(320*Real.log (2*(N:ℝ))) ≤
        ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)/
          Real.sqrt N := by
    filter_upwards [eventually_shell_card_lower, eventually_ge_atTop (1:ℕ)]
      with N hc hN
    have hNr : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
    have hroot : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
    have hlog : 0 < Real.log (2*(N:ℝ)) := Real.log_pos (by nlinarith [hN1])
    have hraw : ((3/2:ℝ)-1)/2 * (((2*N:ℕ):ℝ)/Real.log (2*N:ℕ)) =
        (N:ℝ)/(2*Real.log (2*(N:ℝ))) := by
      push_cast
      ring
    rw [hraw] at hc
    have hc' : (N:ℝ) ≤ (2*Real.log (2*(N:ℝ)))*
        ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ) := by
      simpa only [mul_comm] using
        (div_le_iff₀ (by positivity : 0 < 2*Real.log (2*(N:ℝ)))).mp hc
    have hlarge : (2*Real.log (2*(N:ℝ)))*
        ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ) ≤
        (320*Real.log (2*(N:ℝ)))*
        ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ) := by
      apply mul_le_mul_of_nonneg_right (by linarith [hlog]) (Nat.cast_nonneg _)
    have hdiv : (N:ℝ)/(320*Real.log (2*(N:ℝ))) ≤
        ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ) :=
      (div_le_iff₀ (by positivity : 0 < 320*Real.log (2*(N:ℝ)))).mpr
        (by simpa only [mul_comm] using hc'.trans hlarge)
    apply (le_div_iff₀ hroot).mpr
    calc
      (Real.sqrt N/(320*Real.log (2*(N:ℝ))))*Real.sqrt N =
          (Real.sqrt N)^2/(320*Real.log (2*(N:ℝ))) := by ring
      _ = (N:ℝ)/(320*Real.log (2*(N:ℝ))) := by
        rw [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)]
      _ ≤ _ := hdiv
  exact tendsto_atTop_mono' _ hbound sqrt_log_double_tendsto

theorem tendsto_shell_mobiusDivisorDilationMean_atTop :
    Tendsto (fun N : ℕ => mobiusDivisorDilationMean
      (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) 1) atTop atTop := by
  let k : ℕ → ℝ := fun N =>
    ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)
  have hcardTop : Tendsto (fun N : ℕ => k N/Real.sqrt N) atTop atTop :=
    tendsto_shell_card_div_sqrt
  have hpow : Tendsto (fun x : ℝ => x^2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)
  have hscaled : Tendsto (fun N : ℕ => (k N/Real.sqrt N)^2/40960000)
      atTop atTop :=
    (hpow.comp hcardTop).atTop_div_const (by norm_num : (0:ℝ)<40960000)
  have hbound : ∀ᶠ N : ℕ in atTop,
      (k N/Real.sqrt N)^2/40960000 ≤
        mobiusDivisorDilationMean
          (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) 1 := by
    filter_upwards [hcardTop.eventually_ge_atTop 480,
      eventually_ge_atTop (1:ℕ)] with N hk hN
    have hNr : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
    have hroot : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
    have hroot1 : 1 ≤ Real.sqrt N := by
      have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N),
        Real.sqrt_nonneg (N:ℝ)]
    have hk' : (480:ℝ) ≤ k N := by
      have hmul := (le_div_iff₀ hroot).mp hk
      nlinarith [hmul]
    have hcard : 480 ≤
        (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card := by
      change (480:ℝ) ≤
        ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ) at hk'
      exact_mod_cast hk'
    have hlower := shell_mean_lower N hN hcard
    have hN0 : (N:ℝ) ≠ 0 := hNr.ne'
    have heq : (k N/Real.sqrt N)^2/40960000 =
        (k N)^2/(40960000*(N:ℝ)) := by
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)]
      field_simp [hN0]
    rw [heq]
    exact hlower
  exact tendsto_atTop_mono' _ hbound hscaled

theorem tendsto_shell_normalized_fixedCoreDebt_atTop :
    Tendsto (fun N : ℕ =>
      (Sieve.squarefreeDensity *
        ∏ p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N),
          (p:ℝ)/(p+1)) *
        mobiusDivisorDilationMean
          (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) 1)
      atTop atTop := by
  have hδ : 0 < Sieve.squarefreeDensity := by
    rw [Sieve.squarefreeDensity_eq]
    positivity
  have hmean := tendsto_shell_mobiusDivisorDilationMean_atTop
  have hbase : Tendsto (fun N : ℕ =>
      (Sieve.squarefreeDensity/2) * mobiusDivisorDilationMean
        (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) 1)
        atTop atTop := hmean.const_mul_atTop (by positivity)
  have hbound : ∀ᶠ N : ℕ in atTop,
      (Sieve.squarefreeDensity/2) * mobiusDivisorDilationMean
        (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) 1 ≤
      (Sieve.squarefreeDensity *
        ∏ p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N),
          (p:ℝ)/(p+1)) *
        mobiusDivisorDilationMean
          (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) 1 := by
    filter_upwards [hmean.eventually_ge_atTop 0,
      eventually_ge_atTop (1:ℕ)] with N hm hN
    have hp := shell_density_lower N hN
    have hprod := mul_le_mul_of_nonneg_left hp hδ.le
    have hmul := mul_le_mul_of_nonneg_right hprod hm
    nlinarith only [hmul]
  exact tendsto_atTop_mono' _ hbound hbase

end RHTower
