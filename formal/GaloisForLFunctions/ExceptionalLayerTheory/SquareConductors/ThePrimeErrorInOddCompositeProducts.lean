import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheOddDivisorLogarithmOnEveryProductInterval
import GaloisForLFunctions.ExceptionalLayerTheory.EveryRightZeroForcesBothSignsOfThePrimeError
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheSeventeenNinthsConductorPrefix
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.SingleQuartetSecularAndWallRigidity

/-!
# The prime error in odd composite products

At the square-root cutoff an eligible divisor is a unique large prime.
The signed prime error agrees to square-root precision with a finite
baseline minus a positive sum supported entirely on odd composites.
-/

noncomputable section
open Finset Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Large-prime mass on odd composites through an integer horizon. -/
def oddCompositePrimeMass (H : ℕ) : ℝ :=
  ∑ u ∈ (Ioc 0 H).filter Odd, if u.Prime then 0 else eligibleDivisorLog H.sqrt u

/-- Corrected odd factorial baseline. The omitted Mangoldt terms are
small primes or proper powers, so their prime bases are all small. -/
def oddCompositeBaseline (H : ℕ) : ℝ :=
  (∑ u ∈ (Ioc 0 H).filter Odd, Real.log u) - (H:ℝ)/2*oddExcludedDivisorDensity H.sqrt H +
    (∑ d ∈ (Ioc 0 H).filter (fun d => ¬(d.Prime ∧ max 4 H.sqrt<d)), vonMangoldt d) - H

private theorem singleton_and_omitted (P H : ℕ) :
    (∑ u ∈ (Ioc 0 H).filter Odd, if u.Prime ∧ max 4 P<u then Real.log u else 0) +
    (∑ d ∈ (Ioc 0 H).filter (fun d => ¬(d.Prime ∧ max 4 P<d)), vonMangoldt d) = Chebyshev.psi H := by
  classical
  let S := Ioc 0 H
  let good (p : ℕ) := p.Prime ∧ max 4 P<p
  have he : (S.filter Odd).filter good = S.filter good := by
    ext p
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨hp,_⟩,hg⟩; exact ⟨hp,hg⟩
    · rintro ⟨hp,hg⟩
      obtain ⟨hpr,hP⟩ := hg
      have h4 := (le_max_left 4 P).trans_lt hP
      exact ⟨⟨hp,hpr.odd_of_ne_two (by omega)⟩,hpr,hP⟩
  have hsum : (∑ u ∈ S.filter Odd, if good u then Real.log u else 0) =
      ∑ p ∈ S.filter good, vonMangoldt p := by
    rw [←sum_filter,he]
    exact sum_congr rfl (fun p hp => (vonMangoldt_apply_prime (mem_filter.mp hp).2.1).symm)
  change (∑ u ∈ S.filter Odd, if good u then _ else 0) + _ = _
  rw [hsum,Chebyshev.psi,Nat.floor_natCast]
  exact sum_filter_add_sum_filter_not S good vonMangoldt

/-- A uniform square-root comparison on all integer terminals. -/
theorem odd_composite_baseline_prime_error :
    ∃ A : ℝ, 0≤A ∧ ∀ {H : ℕ}, 0<H →
      |(oddCompositeBaseline H-oddCompositePrimeMass H)-(Chebyshev.psi H-H)| ≤ A*Real.sqrt H := by
  classical
  obtain ⟨C,hC,h⟩ := odd_signed_product_prefix
  refine ⟨28+C,by positivity,fun {H} hH => ?_⟩
  let P := H.sqrt
  let U := (Ioc 0 H).filter Odd
  let Λ₀ (u : ℕ) : ℝ := if u.Prime ∧ max 4 P<u then Real.log u else 0
  have hm : (∑ u ∈ U, firstPrimeProductCoefficient P u) = -oddCompositePrimeMass H := by
    unfold oddCompositePrimeMass
    rw [←sum_neg_distrib]
    apply sum_congr rfl
    intro u hu
    rw [odd_product_is_negative_composite_mass P (mem_filter.mp hu).2]
    by_cases hp : u.Prime <;> simp only [hp,if_false,if_true,neg_zero,P,eligibleDivisorLog]
  have hs := h P H H le_rfl
  change |(∑ u ∈ U, (firstPrimeProductCoefficient P u-Λ₀ u+Real.log u))-_| ≤ _ at hs
  rw [sum_add_distrib,sum_sub_distrib,hm] at hs
  have hψ := singleton_and_omitted P H
  change (∑ u ∈ U, Λ₀ u)+_=Chebyshev.psi H at hψ
  have hbase : (oddCompositeBaseline H-oddCompositePrimeMass H)-(Chebyshev.psi H-H) =
      (-oddCompositePrimeMass H-(∑ u ∈ U, Λ₀ u)+(∑ u ∈ U, Real.log u)) -
        (H:ℝ)/2*oddExcludedDivisorDensity P H := by
    rw [←hψ,oddCompositeBaseline]
    dsimp only [U,P]
    ring
  rw [hbase]
  have h1 : 1≤Real.sqrt H := Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr hH)
  have hmax : ((max 4 P:ℕ):ℝ)≤4*Real.sqrt H := by
    rw [Nat.cast_max,Nat.cast_ofNat]
    exact max_le (by linarith only [h1]) (Real.nat_sqrt_le_real_sqrt.trans (by linarith only [h1]))
  exact hs.trans (by linarith only [hmax])

private theorem power_gap_on_square_window {b β A c : ℝ} (hb : b<β) (hc : 0<c) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, Real.sqrt N<n → A*(n:ℝ)^b<c*(n:ℝ)^β := by
  have hlim : Tendsto (fun n : ℕ => A*(n:ℝ)^(-(β-b))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (sub_pos.mpr hb)).comp tendsto_natCast_atTop_atTop).const_mul A
  obtain ⟨k,hk⟩ := eventually_atTop.mp (hlim.eventually_lt_const hc)
  filter_upwards [eventually_ge_atTop (k^2)] with N hN
  intro n hn
  have hNk : (k:ℝ)≤Real.sqrt N := Real.le_sqrt_of_sq_le (by exact_mod_cast hN)
  have hn0 := (Real.sqrt_nonneg (N:ℝ)).trans_lt hn
  have hkn : k≤n := by exact_mod_cast (hNk.trans hn.le)
  calc _ = (A*(n:ℝ)^(-(β-b)))*(n:ℝ)^β := by
         rw [mul_assoc,← Real.rpow_add hn0,show -(β-b)+β=b by ring]
       _ < _ := mul_lt_mul_of_pos_right (hk n hkn) (Real.rpow_pos_of_pos hn0 _)

/-- Every actual right zero forces both signs of the positive composite
count relative to its arithmetic baseline on each sufficiently late window. -/
theorem odd_composite_surpluses_at_right_zero {ρ : ℂ} (hhalf : 1/2<ρ.re)
    (hone : ρ.re<1) (hz : riemannZeta ρ=0) : ∃ c : ℝ, 0<c ∧
    ∀ᶠ N : ℕ in atTop, ∀ σ : ℝ, |σ|=1 → ∃ n ∈ Icc 1 N, Real.sqrt N<n ∧
      c*(n:ℝ)^ρ.re < σ*(oddCompositePrimeMass n-oddCompositeBaseline n) := by
  obtain ⟨c,hc,hlate⟩ := both_prime_error_peaks_at_every_large_cutoff hhalf hone hz
  obtain ⟨A,hA,herr⟩ := odd_composite_baseline_prime_error
  refine ⟨c/2,half_pos hc,?_⟩
  filter_upwards [hlate,power_gap_on_square_window (A := A) hhalf (half_pos hc)] with N hN hsmall
  intro σ hσ
  obtain ⟨n,hn,hhi,hp⟩ := hN (-σ) (by rwa [abs_neg])
  have hb := hsmall n hhi
  rw [←Real.sqrt_eq_rpow] at hb
  have he := herr (mem_Icc.mp hn).1
  have he' : |σ*((oddCompositeBaseline n-oddCompositePrimeMass n)-(Chebyshev.psi n-n))| ≤ A*Real.sqrt n := by
    rw [abs_mul,hσ,one_mul]; exact he
  exact ⟨n,hn,hhi,by linarith only [hp,hb,(abs_le.mp he').2]⟩

/-- A lower estimate on the positive composite sum on arbitrarily late
square-root windows, uniform over all endpoints of each chosen window. -/
def compositeLowerOnCofinalWindows (b : ℝ) : Prop :=
  ∃ A : ℝ, ∃ᶠ N : ℕ in atTop, ∀ n ∈ Icc 1 N, Real.sqrt N<n →
    oddCompositeBaseline n-oddCompositePrimeMass n ≤ A*(n:ℝ)^b

private theorem width_of_composite_lower {b : ℝ} (hb : 1/2≤b) (h : compositeLowerOnCofinalWindows b) :
    _root_.RHTower.zetaZeroAbscissa ≤ b := by
  obtain ⟨A,hA⟩ := h
  refine csSup_le _root_.RHTower.zetaZeroReSet_nonempty fun x hx => ?_
  obtain ⟨ρ,hz,rfl⟩ := hx
  by_contra! hr
  have hone : ρ.re<1 := lt_of_not_ge (fun hh => riemannZeta_ne_zero_of_one_le_re hh hz)
  obtain ⟨c,hc,hpeak⟩ := odd_composite_surpluses_at_right_zero (hb.trans_lt hr) hone hz
  obtain ⟨N,hup,hp,hgap⟩ := (hA.and_eventually (hpeak.and (power_gap_on_square_window (A := A) hr hc))).exists
  obtain ⟨n,hn,hhi,hnp⟩ := hp (-1) (by norm_num)
  have hg := hgap n hhi
  have hu := hup n hn hhi
  linarith only [hnp,hg,hu]

/-- A five-sixths lower error for positive odd composites on cofinal
windows implies the absolute eleven-thirds estimate on every conductor prefix. -/
theorem eleven_thirds_of_cofinal_composite_lower (h : compositeLowerOnCofinalWindows (5/6)) :
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, |seventeenNinthsConductorPrefix N| ≤ C*(N:ℝ)^(11/3:ℝ) :=
  five_sixths_iff_seventeenNinthsConductorPrefix.mp (width_of_composite_lower (by norm_num) h)

/-- The square-root-plus lower criterion on odd composites characterizes RH.
Only one sequence of late windows is required for each exponent. -/
theorem riemannHypothesis_iff_cofinal_odd_composite_lower :
    RiemannHypothesis ↔ ∀ b : ℝ, 1/2<b → b<1 → compositeLowerOnCofinalWindows b := by
  constructor
  · intro hrh b hb _
    have hsup := _root_.RHTower.zeroReSup_le_of_forall_re_le fun q =>
      (_root_.RHTower.xiZeroCopy_re_eq_half_of_riemannHypothesis hrh q).le
    obtain ⟨K,hK,hψ⟩ := _root_.RHTower.exists_abs_chebyshevPsi_sub_le_rpow (hsup.trans_lt hb)
    obtain ⟨A,hA,he⟩ := odd_composite_baseline_prime_error
    refine ⟨K+A,Eventually.frequently (Eventually.of_forall (fun N n hn _ => ?_))⟩
    have hn1 := (mem_Icc.mp hn).1
    have hnR : (1:ℝ)≤n := Nat.one_le_cast.mpr hn1
    have hroot : Real.sqrt n≤(n:ℝ)^b := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hnR hb.le
    have h₁ := (le_abs_self _).trans (hψ n hnR)
    have h₂ := ((abs_le.mp (he hn1)).2).trans (mul_le_mul_of_nonneg_left hroot hA)
    linarith only [h₁,h₂]
  · intro h
    apply _root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mpr
    intro ρ hhalf hone hz
    obtain ⟨b,hb,hbρ⟩ := exists_between hhalf
    exact hbρ.not_ge ((_root_.RHTower.re_le_zetaZeroAbscissa hz).trans
      (width_of_composite_lower hb.le (h b hb (hbρ.trans hone))))

open GaloisForLFunctions.ExclusionOfTheCriticalState in
/-- An actual right zero generates the lone quartet precisely when the
positive odd-composite count follows its single prime wave at square-root
precision times the squared logarithm. -/
theorem single_quartet_iff_odd_composite_wave {ρ : ℂ} (hr : 1/2<ρ.re)
    (hz : ρ∈Zeta23.zetaZeroConfig.carrier) :
    HasSingleOffLineQuartet ρ ↔ ∃ K : ℝ, ∀ x : ℝ, 16≤x →
      |oddCompositeBaseline ⌊x⌋₊-oddCompositePrimeMass ⌊x⌋₊ +
        2*(quartetCopyMult ρ:ℝ)*((x:ℂ)^ρ/ρ).re| ≤ K*Real.sqrt x*Real.log x^2 := by
  rw [hasSingleOffLineQuartet_iff_chebyshevPsi_singleWave hr hz]
  obtain ⟨A,hA,h⟩ := odd_composite_baseline_prime_error
  let D (x : ℝ) := oddCompositeBaseline ⌊x⌋₊-oddCompositePrimeMass ⌊x⌋₊
  let E (x : ℝ) := Chebyshev.psi x-x
  have he (x : ℝ) (hx : 16≤x) : |D x-E x|≤(A+1)*Real.sqrt x*Real.log x^2 := by
    have h1 : 1≤x := by linarith only [hx]
    have hx0 := zero_lt_one.trans_le h1
    have hj : 0<⌊x⌋₊ := by exact Nat.le_floor (by simpa only [Nat.cast_one] using h1)
    have hlo := Nat.floor_le hx0.le
    have hhi := Nat.lt_floor_add_one x
    have hb := h hj
    have hs := Real.sqrt_le_sqrt hlo
    have hs1 := Real.one_le_sqrt.mpr h1
    have hl : 1≤Real.log x := (Real.le_log_iff_exp_le hx0).mpr (by linarith only [Real.exp_one_lt_three,hx])
    have heq : D x-E x = ((oddCompositeBaseline ⌊x⌋₊-oddCompositePrimeMass ⌊x⌋₊)-
        (Chebyshev.psi ⌊x⌋₊-⌊x⌋₊)) + (x-⌊x⌋₊) := by
      dsimp only [D,E]
      rw [Chebyshev.psi_eq_psi_coe_floor x]; ring
    rw [heq]
    apply (abs_add_le _ _).trans
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    apply le_trans (b := (A+1)*Real.sqrt x)
    · linarith only [hb,mul_le_mul_of_nonneg_left hs hA,hs1,hhi]
    · exact le_mul_of_one_le_right (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (one_le_pow₀ hl)
  have transfer {v t w₀ K x : ℝ} (ht : |v-t|≤(A+1)*Real.sqrt x*Real.log x^2)
      (hw : |t+w₀|≤K*Real.sqrt x*Real.log x^2) :
      |v+w₀|≤(K+A+1)*Real.sqrt x*Real.log x^2 := by
    rw [show v+w₀=(v-t)+(t+w₀) by ring]
    exact (abs_add_le _ _).trans ((add_le_add ht hw).trans_eq (by ring))
  constructor
  · rintro ⟨K,hK⟩
    exact ⟨K+A+1,fun x hx => transfer (he x hx) (hK x hx)⟩
  · rintro ⟨K,hK⟩
    refine ⟨K+A+1,fun x hx => ?_⟩
    have hd : |E x-D x|≤_ := (abs_sub_comm (E x) (D x)).le.trans (he x hx)
    exact transfer hd (hK x hx)

#print axioms single_quartet_iff_odd_composite_wave
#print axioms riemannHypothesis_iff_cofinal_odd_composite_lower
#print axioms eleven_thirds_of_cofinal_composite_lower
#print axioms odd_composite_surpluses_at_right_zero
#print axioms odd_composite_baseline_prime_error
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
