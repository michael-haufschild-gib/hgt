import GaloisForLFunctions.ExceptionalLayerTheory.ALocalPrimeWaveAtEveryRightZero
import GaloisForLFunctions.ExceptionalLayerTheory.PositiveWeightsForTheTwoSignsOfThePrimeError
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevCumulativeEnvelope

/-!
# Both signs of the prime error on every sufficiently large power interval

The wave at a single right zero supplies absolute mass on every large
interval. The positive alternating-divisor weights balance the two signs.
Together they test the ordinary prime count without a spectral gap.
-/

noncomputable section

open Finset Filter Topology Complex ArithmeticFunction

namespace GaloisForLFunctions.ExceptionalLayerTheory

private abbrev E (n : ℕ) : ℝ := Chebyshev.psi n - n

/-- Harmonic mass of one sign of the prime error between the square root and the cutoff. -/
def localPrimeSignMass (σ : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => Real.sqrt N < n), max (σ*E n) 0 / n

private theorem cut_kernel_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    (a : ArithmeticFunction ℝ) (w : ℝ → V) (hw : w 1 = 0) {x : ℝ} (hx : x ≤ 1) :
    arithmeticKernel a w x = 0 := by
  rcases hx.lt_or_eq with h | rfl
  · have hfl : ⌊x⌋₊ = 0 := by
      by_contra hne
      exact (not_le.mpr h) ((Nat.one_le_floor_iff x).mp (Nat.one_le_iff_ne_zero.mpr hne))
    simp [arithmeticKernel,hfl]
  · simp [arithmeticKernel,hw]

private theorem small_prime_mass {σ : ℝ} (hσ : |σ| = 1) (N : ℕ) :
    (∑ n ∈ Icc 1 N, max (σ*E n) 0 / n) ≤ localPrimeSignMass σ N + 5*Real.sqrt N := by
  let S := (Icc 1 N).filter (fun n : ℕ => ¬ Real.sqrt N < n)
  have hh : ∑ n ∈ S, max (σ*E n) 0 / n ≤ ∑ _n ∈ S, (5:ℝ) := by
    apply sum_le_sum
    intro n hn
    have hn1 := (mem_Icc.mp (mem_filter.mp hn).1).1
    have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn1
    have hE := RiemannGaussian.abs_chebyshevPsi_sub_self_le_five_mul_self_of_one_le hnR
    apply (div_le_iff₀ (zero_lt_one.trans_le hnR)).mpr
    apply max_le
    · apply (le_abs_self _).trans
      rw [abs_mul,hσ,one_mul]
      exact hE
    · positivity
  have hA : S ⊆ Icc 1 ⌊Real.sqrt N⌋₊ := by
    intro n hn
    obtain ⟨hn,hlo⟩ := mem_filter.mp hn
    exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1,(Nat.le_floor_iff (Real.sqrt_nonneg _)).mpr (not_lt.mp hlo)⟩
  have hcard : (S.card:ℝ) ≤ Real.sqrt N := by
    apply le_trans _ (Nat.floor_le (Real.sqrt_nonneg _))
    exact_mod_cast (show S.card ≤ ⌊Real.sqrt N⌋₊ by simpa using Finset.card_le_card hA)
  have hsmall : (∑ n ∈ S, max (σ*E n) 0 / n) ≤ 5*Real.sqrt N := by
    apply hh.trans
    simp only [sum_const,nsmul_eq_mul]
    linarith only [hcard]
  rw [← sum_filter_add_sum_filter_not (Icc 1 N) (fun n : ℕ => Real.sqrt N < n)]
  exact add_le_add le_rfl hsmall

private theorem absolute_sign_split (ε t : ℝ) (hε : |ε|=1) :
    |t| = 2*max (ε*t) 0 - ε*t := by
  have he : |ε*t| = |t| := by rw [abs_mul,hε,one_mul]
  rw [← he]
  rcases le_total 0 (ε*t) with h | h
  · rw [abs_of_nonneg h,max_eq_left h]; ring
  · rw [abs_of_nonpos h,max_eq_right h]; ring

/-- Quantitative localization at an arbitrary right zero, uniform in the choice of sign. -/
theorem exists_right_zero_prime_mass_bound {ρ : ℂ} (hhalf : 1/2 < ρ.re) (hone : ρ.re < 1)
    (hz : riemannZeta ρ = 0) : ∃ D K : ℝ, 0 < D ∧ 0 < K ∧ ∀ N : ℕ, 1 ≤ N → ∀ σ : ℝ, |σ| = 1 →
      D*(N:ℝ)^ρ.re ≤ K*(Real.sqrt N + localPrimeSignMass σ N) := by
  obtain ⟨k,d,C,hd,hC,hinc,hwave⟩ := exists_alternating_prime_kernel_at_zero hhalf hone hz
  let H := arithmeticKernel alternatingDivisorCoeff (centeredDirichletTest k ρ)
  let G := arithmeticKernel alternatingPrimeExcess (centeredDirichletTest k ρ)
  have hH {y : ℝ} (hy : y ≤ 1) : H y = 0 :=
    cut_kernel_zero _ _ (by simp [centeredDirichletTest]) hy
  let B := 2*(75+2*|Real.eulerMascheroniConstant|)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let P := C+6*C*(10+B)
  let Q := 12*C
  let K := 1+max P Q
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hK : 0 < K := by dsimp only [K]; linarith only [hQ,le_max_right P Q]
  refine ⟨‖d‖,K,norm_pos_iff.mpr hd,hK,fun N hN σ hσ => ?_⟩
  let S := Icc 1 N
  let w := primeMeanWeight N
  let J := fun n : ℕ => H ((N:ℝ)/n)-H ((N:ℝ)/(n+1))
  have hrow : G N = ∑ n ∈ S, E n • J n := by
    change arithmeticKernel (alternatingDivisorCoeff * (vonMangoldt-(zeta : ArithmeticFunction ℝ))) _ _ = _
    rw [mul_comm,arithmeticKernel_mul]
    change arithmeticKernel (vonMangoldt-(zeta : ArithmeticFunction ℝ)) H (N:ℝ) = _
    rw [arithmeticKernel_eq_prefix_differences _ H (fun _ hy => hH hy)]
    simp only [sum_vonMangoldt_sub_zeta,J,S,E]
  have hw (n : ℕ) (hn : n ∈ S) : 0 ≤ w n ∧ w n ≤ 1/n ∧ ‖J n‖ ≤ 6*C*w n := by
    obtain ⟨hn1,hnN⟩ := mem_Icc.mp hn
    have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn1
    rcases hnN.lt_or_eq with h | rfl
    · have hNpos : 0 < (N:ℝ) := by exact_mod_cast hN
      have hx : 1 ≤ (N:ℝ)/(n+1) := (one_le_div (by positivity)).mpr (by exact_mod_cast h)
      have hy : (N:ℝ)/(n+1) ≤ (N:ℝ)/n := div_le_div_of_nonneg_left hNpos.le hn0 (by linarith)
      have hbounds := primeMeanWeight_bounds hn1 h
      have hlow := (primeMeanKernel_increment_bounds hx hy).1
      have hj := hinc _ _ hx hy
      refine ⟨(by positivity : (0:ℝ) ≤ (1/(n+1:ℝ))/6).trans hbounds.1,
        hbounds.2.trans (mul_le_of_le_one_left (by positivity) (by norm_num)),?_⟩
      apply hj.trans
      change _ ≤ 6*C*(primeMeanKernel ((N:ℝ)/n)-primeMeanKernel ((N:ℝ)/(n+1)))
      nlinarith only [mul_le_mul_of_nonneg_left hlow hC]
    · have hle : (n:ℝ)/(n+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      have hw0 : w n = 0 := by
        change primeMeanWeight n n = 0
        rw [primeMeanWeight,div_self hn0.ne']
        rw [primeMeanKernel_eq_zero le_rfl,primeMeanKernel_eq_zero hle,sub_self]
      rw [hw0]
      dsimp only [J]
      rw [div_self hn0.ne',hH le_rfl,hH hle,sub_self,norm_zero,mul_zero]
      exact ⟨le_rfl,by positivity,le_rfl⟩
  have hG : ‖G N‖ ≤ (6*C)* ∑ n ∈ S, |E n| * w n := by
    rw [hrow,mul_sum]
    apply (norm_sum_le _ _).trans
    refine sum_le_sum fun n hn => ?_
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hw n hn).2.2 (abs_nonneg _)).trans_eq (by ring)
  let U := ∑ n ∈ S, max (σ*E n) 0*w n
  let T := ∑ n ∈ S, E n*w n
  have hsplit : (∑ n ∈ S, |E n| * w n) = 2*U - σ*T := by
    dsimp only [U,T]
    rw [mul_sum,mul_sum,← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [absolute_sign_split σ _ hσ]
    ring
  have hT : |T| ≤ B*Real.sqrt N := abs_primeMeanWeight_sum_le N
  have hminus : -(σ*T) ≤ B*Real.sqrt N := by
    apply (neg_le_abs _).trans
    rwa [abs_mul,hσ,one_mul]
  have hU : U ≤ localPrimeSignMass σ N + 5*Real.sqrt N := by
    apply le_trans _ (small_prime_mass hσ N)
    exact sum_le_sum fun n hn => by
      simpa only [div_eq_mul_inv,one_mul] using
        mul_le_mul_of_nonneg_left (hw n hn).2.1 (le_max_right (σ*E n) 0)
  rw [hsplit] at hG
  have hG' : ‖G N‖ ≤ 6*C*(2*(localPrimeSignMass σ N + 5*Real.sqrt N)+B*Real.sqrt N) :=
    hG.trans (mul_le_mul_of_nonneg_left (by linarith only [hU,hminus]) (by positivity))
  have hNr : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  have ha := hwave N hNr
  have hv : ‖d‖*(N:ℝ)^ρ.re ≤ ‖G N‖+C*Real.sqrt N := by
    have htri := norm_le_norm_add_norm_sub' (((N:ℝ):ℂ)^ρ*d) (G N)
    rw [norm_sub_rev] at htri
    apply le_trans _ (add_le_add le_rfl ha)
    simpa only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hNr),mul_comm ‖d‖] using htri
  have hpos : 0 ≤ localPrimeSignMass σ N := sum_nonneg fun n _ => div_nonneg (le_max_right _ _) (Nat.cast_nonneg _)
  calc
    _ ≤ 6*C*(2*(localPrimeSignMass σ N + 5*Real.sqrt N)+B*Real.sqrt N)+C*Real.sqrt N :=
      hv.trans (add_le_add hG' le_rfl)
    _ = P*Real.sqrt N + Q*localPrimeSignMass σ N := by dsimp only [P,Q]; ring
    _ ≤ K*Real.sqrt N + K*localPrimeSignMass σ N := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith only [le_max_left P Q]) (Real.sqrt_nonneg _)
      · exact mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith only [le_max_right P Q]) hpos
    _ = _ := (mul_add _ _ _).symm

private theorem eventually_power_lt {b β K c : ℝ} (hb : b < β) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, K*(N:ℝ)^b < c*(N:ℝ)^β := by
  have hlim : Tendsto (fun n : ℕ => K*(n:ℝ)^(-(β-b))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (sub_pos.mpr hb)).comp tendsto_natCast_atTop_atTop).const_mul K
  filter_upwards [hlim.eventually_lt_const hc,eventually_ge_atTop 1] with N hN hn
  have hp : 0 < (N:ℝ) := by exact_mod_cast hn
  calc
    _ = (K*(N:ℝ)^(-(β-b)))*(N:ℝ)^β := by rw [mul_assoc,← Real.rpow_add hp,show -(β-b)+β=b by ring]
    _ < _ := mul_lt_mul_of_pos_right hN (Real.rpow_pos_of_pos hp _)

/-- Both signs have mass of the power of the zero on every sufficiently large interval
from the square root to the cutoff. The sign may vary with the cutoff. -/
theorem both_prime_sign_masses_at_every_large_cutoff {ρ : ℂ} (hhalf : 1/2 < ρ.re)
    (hone : ρ.re < 1) (hz : riemannZeta ρ = 0) : ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop, ∀ σ : ℝ, |σ|=1 → c*(N:ℝ)^ρ.re ≤ localPrimeSignMass σ N := by
  obtain ⟨D,K,hD,hK,hm⟩ := exists_right_zero_prime_mass_bound hhalf hone hz
  refine ⟨D/(2*K),by positivity,?_⟩
  filter_upwards [eventually_power_lt (K := K) hhalf (half_pos hD),eventually_ge_atTop 1] with N h hn
  intro σ hσ
  have hi := hm N hn σ hσ
  rw [Real.sqrt_eq_rpow] at hi
  calc
    _ = ((D/2)*(N:ℝ)^ρ.re)/K := by ring
    _ ≤ _ := (div_le_iff₀ hK).mpr (by linarith only [h,hi])

private theorem local_mass_le_of_pointwise {b C σ : ℝ} (hb : 1/2≤b) (hC : 0≤C)
    {N : ℕ} (hN : 1≤N) (h : ∀ n ∈ Icc 1 N, Real.sqrt N<n → σ*E n≤C*(n:ℝ)^b) :
    localPrimeSignMass σ N≤(2*C)*(N:ℝ)^b := by
  have hpos := sub_nonneg.mpr hb
  let S := Icc 1 N
  let T := S.filter (fun n : ℕ => Real.sqrt N < n)
  have hsub : T ⊆ S := filter_subset _ _
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast hN
  let A := C*(N:ℝ)^(b-1/2)
  have hA : 0 ≤ A := mul_nonneg hC (Real.rpow_nonneg hN0.le _)
  have hw (n : ℕ) (ht : n ∈ T) : max (σ*E n) 0 / n ≤ A*(n:ℝ)^(-(1/2:ℝ)) := by
    have hn := hsub ht
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have hn0 := zero_lt_one.trans_le hn1
    have hac := max_le (h n hn (mem_filter.mp ht).2) (mul_nonneg hC (Real.rpow_nonneg hn0.le b))
    apply (div_le_div_of_nonneg_right hac hn0.le).trans
    calc
      _ = (C*(n:ℝ)^(b-1/2))*(n:ℝ)^(-(1/2:ℝ)) := by
        rw [mul_div_assoc,← Real.rpow_sub_one hn0.ne',mul_assoc,← Real.rpow_add hn0,
          show b-1/2+(-(1/2:ℝ))=b-1 by ring]
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn0.le
        (by exact_mod_cast (mem_Icc.mp hn).2) hpos) hC) (Real.rpow_nonneg hn0.le _)
  calc
    _ ≤ ∑ n ∈ T, A*(n:ℝ)^(-(1/2:ℝ)) := sum_le_sum fun n hn => hw n hn
    _ ≤ ∑ n ∈ S, A*(n:ℝ)^(-(1/2:ℝ)) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    _ ≤ A*(2*Real.sqrt N) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (_root_.RHTower.sum_rpow_neg_half_le N) hA
    _ = _ := by
      rw [Real.sqrt_eq_rpow]
      calc
        _ = (2*C)*((N:ℝ)^(b-1/2)*(N:ℝ)^(1/2:ℝ)) := by dsimp only [A]; ring
        _ = _ := by rw [← Real.rpow_add hN0,show b-1/2+1/2=b by ring]

private theorem mass_bound_above_zero_abscissa {b : ℝ} (hb : _root_.RHTower.zeroReSup < b) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ σ : ℝ, |σ|=1 → localPrimeSignMass σ N ≤ K*(N:ℝ)^b := by
  obtain ⟨C,hC,hψ⟩ := _root_.RHTower.exists_abs_chebyshevPsi_sub_le_rpow hb
  refine ⟨2*C,fun N hN σ hσ => local_mass_le_of_pointwise
    (_root_.RHTower.half_le_zeroReSup.trans hb.le) hC hN (fun n hn _ => ?_)⟩
  apply (le_abs_self _).trans
  rw [abs_mul,hσ,one_mul]
  exact hψ n (by exact_mod_cast (mem_Icc.mp hn).1)

/-- Every right zero forces a point of each sign at its exact power on
each sufficiently large interval between the square root and the cutoff. -/
theorem both_prime_error_peaks_at_every_large_cutoff {ρ : ℂ} (hhalf : 1/2<ρ.re)
    (hone : ρ.re<1) (hz : riemannZeta ρ=0) : ∃ c : ℝ, 0<c ∧
      ∀ᶠ N : ℕ in atTop, ∀ σ : ℝ, |σ|=1 → ∃ n ∈ Icc 1 N, Real.sqrt N<n ∧
        c*(n:ℝ)^ρ.re<σ*(Chebyshev.psi n-n) := by
  obtain ⟨c,hc,h⟩ := both_prime_sign_masses_at_every_large_cutoff hhalf hone hz
  refine ⟨c/4,by positivity,?_⟩
  filter_upwards [h,eventually_ge_atTop 1] with N hN hn
  intro σ hσ
  by_contra! hu
  have hl := (hN σ hσ).trans (local_mass_le_of_pointwise hhalf.le (by positivity : 0≤c/4) hn hu)
  have hp : 0<c*(N:ℝ)^ρ.re := mul_pos hc (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)
  linarith only [hl,hp]


/-- RH is equivalent to finding one sign of small harmonic mass on arbitrarily distant
square-root intervals for each exponent above one half. -/
theorem riemannHypothesis_iff_cofinal_one_signed_prime_means :
    RiemannHypothesis ↔ ∀ b : ℝ, 1/2 < b → b < 1 → ∃ K : ℝ,
      ∃ᶠ N : ℕ in atTop, ∃ σ : ℝ, |σ|=1 ∧ localPrimeSignMass σ N ≤ K*(N:ℝ)^b := by
  constructor
  · intro hRH b hb _
    have hsup := _root_.RHTower.zeroReSup_le_of_forall_re_le fun q =>
      (_root_.RHTower.xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q).le
    obtain ⟨K,hK⟩ := mass_bound_above_zero_abscissa (hsup.trans_lt hb)
    refine ⟨K,Eventually.frequently ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact ⟨1,abs_one,hK N hN 1 abs_one⟩
  · intro h
    apply _root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mpr
    intro ρ hhalf hone hz
    obtain ⟨b,hb,hbρ⟩ := exists_between hhalf
    obtain ⟨K,hK⟩ := h b hb (hbρ.trans hone)
    obtain ⟨c,hc,hcN⟩ := both_prime_sign_masses_at_every_large_cutoff hhalf hone hz
    obtain ⟨N,⟨σ,hσ,hupper⟩,hlow,hlt⟩ :=
      (hK.and_eventually (hcN.and (eventually_power_lt (K := K) hbρ hc))).exists
    exact (not_lt_of_ge ((hlow σ hσ).trans hupper)) hlt


end GaloisForLFunctions.ExceptionalLayerTheory
