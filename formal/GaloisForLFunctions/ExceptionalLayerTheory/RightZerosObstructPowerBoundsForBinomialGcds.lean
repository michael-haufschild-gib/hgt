import GaloisForLFunctions.ExceptionalLayerTheory.TheDirichletSeriesOfDyadicBinomialPrimeCounts
import GaloisForLFunctions.ExceptionalLayerTheory.PairedCofactorBoundsForOrdinaryPrimeCounts
import GaloisForLFunctions.RHTower.ZetaLittlewoodDeficit

/-!
# Right zeros obstruct power bounds for binomial gcds

A linear main term contributes a constant multiple of zeta to the
Dirichlet series. At a right zero it leaves the residue of the logarithmic
derivative unchanged. Sampling at multiples of a fixed width loses at most
the width times a logarithm.
-/

noncomputable section

open Complex Finset Filter Topology

namespace GaloisForLFunctions.ExceptionalLayerTheory

private def primeSymbolRemainder (q : ℕ) (A : ℝ) (s : ℂ) : ℂ :=
  (-deriv riemannZeta s / riemannZeta s)*lastQuotientClassSymbol q s - A*riemannZeta s

private theorem symbol_vanishes_of_mass_bound (q : ℕ) [NeZero q] (hq : 2 ≤ q)
    {A b K : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hbound : ∀ N : ℕ, 1 ≤ N → |lastClassPrimeMass q N - A*N| ≤ K*(N:ℝ)^b)
    {ρ : ℂ} (hρ : b < ρ.re) (hz : riemannZeta ρ = 0) : lastQuotientClassSymbol q ρ = 0 := by
  let c := fun n : ℕ => if n = 0 then (0:ℂ) else ((lastClassPrimeCoeff q n - A : ℝ) : ℂ)
  have hc0 : c 0 = 0 := by simp [c]
  have hK : 0 ≤ K := by simpa using (abs_nonneg _).trans (hbound 1 le_rfl)
  have hreal (x : ℝ) (hx : 1 ≤ x) : ‖∑ n ∈ Icc 1 ⌊x⌋₊, c n‖ ≤ K*x^b := by
    let M := ⌊x⌋₊
    have he : (∑ n ∈ Icc 1 M, c n) = ((lastClassPrimeMass q M - A*M : ℝ) : ℂ) := by
      calc
        _ = ∑ n ∈ Icc 1 M, ((lastClassPrimeCoeff q n - A : ℝ) : ℂ) :=
          sum_congr rfl fun n hn => if_neg (Nat.ne_of_gt (mem_Icc.mp hn).1)
        _ = _ := by
          rw [← Complex.ofReal_sum,sum_sub_distrib,lastClassPrimeMass_eq_prefix q hq]
          simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel,mul_comm A]
    rw [he,Complex.norm_real,Real.norm_eq_abs]
    exact (hbound M ((Nat.one_le_floor_iff x).mpr hx)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (zero_le_one.trans hx)) hb) hK)
  let D := {s : ℂ | b < s.re}
  let G := HeckeLFunctions.growthCont c b
  have hopen : IsOpen D := isOpen_lt continuous_const Complex.continuous_re
  have hG : DifferentiableOn ℂ G D := HeckeLFunctions.differentiableOn_growthCont hc0 hb hreal
  let F := primeSymbolRemainder q A - G
  have hmero : MeromorphicOn F D := by
    apply MeromorphicOn.sub _ (hG.analyticOnNhd hopen).meromorphicOn
    intro s _
    have hZ := RHTower.meromorphicAt_riemannZeta_everywhere s
    have hA : MeromorphicAt (fun _ : ℂ => (A:ℂ)) s := analyticAt_const.meromorphicAt
    exact ((hZ.deriv.neg.div hZ).mul
      ((differentiable_lastQuotientClassSymbol q).analyticAt s).meromorphicAt).sub
      (hA.mul hZ)
  have h2 : meromorphicOrderAt F (2:ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hnb : {s : ℂ | 1 < s.re} ∈ 𝓝 (2:ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [nhdsWithin_le_nhds hnb] with s hs
    obtain ⟨hf,he⟩ := lastClassPrimeCoeff_series q hs
    let f := fun n => (lastClassPrimeCoeff q n : ℂ)
    have hd {n : ℕ} (hn : n ≠ 0) : c n = (f - (A:ℂ) • (1 : ℕ → ℂ)) n := by
      simp [c,hn,f]
    have ha := (LSeriesSummable_one_iff.mpr hs).smul (A:ℂ)
    have hc := (LSeriesSummable_congr s hd).mpr (hf.sub ha)
    apply sub_eq_zero.mpr
    change primeSymbolRemainder q A s = HeckeLFunctions.growthCont c b s
    rw [HeckeLFunctions.growthCont_eq_LSeries hc0 hb hreal (hb1.trans hs) hc,LSeries_congr hd s,
      LSeries_sub hf ha,LSeries_smul,LSeries_one_eq_riemannZeta hs]
    exact congrArg (· - (A:ℂ)*riemannZeta s) he.symm
  have htop : meromorphicOrderAt F ρ = ⊤ := by
    by_contra h
    exact (hmero.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_halfSpace_re_gt b).isPreconnected hρ
      (show b < (2:ℂ).re by simpa using hb1.trans (by norm_num : (1:ℝ)<2)) h) h2
  have hgerm : primeSymbolRemainder q A =ᶠ[𝓝[≠] ρ] G :=
    (meromorphicOrderAt_eq_top_iff.mp htop).mono fun _ e => sub_eq_zero.mp e
  have hlin : Tendsto (fun s : ℂ => s-ρ) (𝓝[≠] ρ) (𝓝 0) :=
    ((continuous_id.sub continuous_const).tendsto' ρ 0 (sub_self ρ)).mono_left nhdsWithin_le_nhds
  have hGlim := (hG.differentiableAt (hopen.mem_nhds hρ)).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := ({ρ}ᶜ : Set ℂ)))
  have hzero : Tendsto (fun s : ℂ => (s-ρ)*primeSymbolRemainder q A s) (𝓝[≠] ρ) (𝓝 0) := by
    apply (tendsto_congr' (hgerm.mono fun s hs => congrArg ((s-ρ)*·) hs)).mpr
    simpa only [zero_mul] using hlin.mul hGlim
  obtain ⟨m,hm,hres⟩ := RHTower.neg_logDeriv_zeta_zero_residue hz
  have hDlim := (differentiable_lastQuotientClassSymbol q ρ).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := ({ρ}ᶜ : Set ℂ)))
  have hZlim := (differentiableAt_riemannZeta (RHTower.riemannZeta_zero_ne_one hz)).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := ({ρ}ᶜ : Set ℂ)))
  have hlim : Tendsto (fun s : ℂ => (s-ρ)*primeSymbolRemainder q A s) (𝓝[≠] ρ)
      (𝓝 (-(m:ℂ)*lastQuotientClassSymbol q ρ)) := by
    convert (hres.mul hDlim).sub ((hlin.mul_const (A:ℂ)).mul hZlim) using 1
    · funext s
      unfold primeSymbolRemainder
      ring
    · simp
  exact (mul_eq_zero.mp (tendsto_nhds_unique hlim hzero)).resolve_left
    (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega : m ≠ 0)))

private theorem mass_bound_of_gcd_bound (j : ℕ) {b A K : ℝ} (hb : 1/2 ≤ b)
    (hg : ∀ N : ℕ, |Real.log (dyadicBinomialGcd j N) - A*(2^(j+1)*N : ℕ)| ≤
      K*(max 1 (2^(j+1)*N : ℕ) : ℕ)^b) :
    ∃ T : ℝ, ∀ X : ℕ, 1 ≤ X →
      |lastClassPrimeMass (2^(j+1)) X - A*X| ≤ T*(X:ℝ)^b := by
  let q := 2^(j+1)
  have hq : 2 ≤ q := by have := Nat.lt_two_pow_self (n := j+1); dsimp only [q]; omega
  obtain ⟨C,hC⟩ := exists_uniform_dyadicBinomialGcd_log_error
  refine ⟨2*q + |C| + |K| + |A| * q,fun X hX => ?_⟩
  let N := X/q
  let Y := q*N
  have hXY : Y ≤ X := Nat.mul_div_le X q
  have hgap : X-Y ≤ q := by
    have h := Nat.mod_add_div X q
    have hr := Nat.mod_lt X (by omega : 0 < q)
    change X - q*(X/q) ≤ q
    omega
  have hx : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hroot : Real.sqrt X ≤ (X:ℝ)^b := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx hb
  have hpow : 1 ≤ (X:ℝ)^b := Real.one_le_rpow hx (by linarith only [hb])
  have hl : Real.log ((X:ℝ)+1) ≤ 2*(X:ℝ)^b := calc
    _ ≤ Real.sqrt ((X:ℝ)+1) := RHTower.log_le_sqrt (by positivity)
    _ ≤ Real.sqrt (4*(X:ℝ)) := Real.sqrt_le_sqrt (by linarith only [hx])
    _ = 2*Real.sqrt X := by rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]; norm_num
    _ ≤ _ := by linarith only [hroot]
  have h₁ := (lastClassPrimeMass_cutoff_gap hq hXY).trans (mul_le_mul
    (show ((X-Y:ℕ):ℝ) ≤ q by exact_mod_cast hgap) hl (Real.log_nonneg (by linarith only [hx]))
    (Nat.cast_nonneg q))
  have h₂ : |lastClassPrimeMass q Y - Real.log (dyadicBinomialGcd j N)| ≤ |C| * (X:ℝ)^b := by
    change |lastClassPrimeMass (2^(j+1)) (2^(j+1)*N) - _| ≤ _
    rw [abs_sub_comm,lastClassPrimeMass_at_dyadic]
    exact (hC j N).trans (mul_le_mul (le_abs_self _) ((Real.sqrt_le_sqrt
      (show (Y:ℝ) ≤ X by exact_mod_cast hXY)).trans hroot) (Real.sqrt_nonneg _) (abs_nonneg _))
  have h₃ := (hg N).trans (mul_le_mul (le_abs_self K)
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (show ((max 1 Y : ℕ):ℝ) ≤ X by
      exact_mod_cast max_le hX hXY) (by linarith only [hb])) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (abs_nonneg K))
  have h₄ : |A*(Y:ℝ)-A*X| ≤ (|A| * q)*(X:ℝ)^b := by
    rw [← mul_sub,abs_mul,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hXY))]
    have hr : (X:ℝ) - Y ≤ q := by
      apply sub_le_iff_le_add.mpr
      exact_mod_cast (show X ≤ q+Y by omega)
    exact (mul_le_mul_of_nonneg_left hr (abs_nonneg _)).trans
      (le_mul_of_one_le_right (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) hpow)
  have ht := (abs_sub_le (lastClassPrimeMass q X) (lastClassPrimeMass q Y) (A*X)).trans
    (add_le_add h₁ ((abs_sub_le _ (Real.log (dyadicBinomialGcd j N)) _).trans
    (add_le_add h₂ ((abs_sub_le _ (A*Y) _).trans (add_le_add h₃ h₄)))))
  exact ht.trans_eq (by ring)

/-- At every right zero, all sufficiently deep fixed gcd families fail every
linear approximation with a power saving below the real part of that zero. -/
theorem right_zero_obstructs_dyadicBinomialGcd_bounds {ρ : ℂ} (hhalf : 1/2 < ρ.re)
    (hz : riemannZeta ρ = 0) :
    ∀ᶠ j : ℕ in atTop, ∀ b : ℝ, 1/2 ≤ b → b < ρ.re → b < 1 → ∀ A K : ℝ,
      ∃ N : ℕ, K*(max 1 (2^(j+1)*N : ℕ) : ℕ)^b <
        |Real.log (dyadicBinomialGcd j N) - A*(2^(j+1)*N : ℕ)| := by
  filter_upwards [eventually_dyadicQuotientSymbol_ne_zero (by linarith only [hhalf] : 0 < ρ.re)]
    with j hj
  intro b hb hbρ hb1 A K
  by_contra! hn
  obtain ⟨T,ht⟩ := mass_bound_of_gcd_bound j hb hn
  have hq : 2 ≤ 2^(j+1) := by have := Nat.lt_two_pow_self (n := j+1); omega
  exact hj (symbol_vanishes_of_mass_bound _ hq (by linarith only [hb]) hb1 ht hbρ hz)

/-- Cofinal fixed depths with square-root-accuracy linear main terms would force RH. -/
theorem riemannHypothesis_of_cofinal_dyadicBinomialGcd_bounds
    (h : ∀ b : ℝ, 1/2 < b → b < 1 → ∃ᶠ j : ℕ in atTop, ∃ A K : ℝ, ∀ N : ℕ,
      |Real.log (dyadicBinomialGcd j N) - A*(2^(j+1)*N : ℕ)| ≤
        K*(max 1 (2^(j+1)*N : ℕ) : ℕ)^b) : RiemannHypothesis := by
  apply RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mpr
  intro ρ hlo hhi hz
  obtain ⟨b,hb,hbρ⟩ := exists_between hlo
  obtain ⟨j,⟨A,K,hg⟩,hj⟩ := ((h b hb (hbρ.trans hhi)).and_eventually
    (right_zero_obstructs_dyadicBinomialGcd_bounds hlo hz)).exists
  obtain ⟨N,hN⟩ := hj b hb.le hbρ (hbρ.trans hhi) A K
  exact (hg N).not_gt hN

#print axioms right_zero_obstructs_dyadicBinomialGcd_bounds
#print axioms riemannHypothesis_of_cofinal_dyadicBinomialGcd_bounds

end GaloisForLFunctions.ExceptionalLayerTheory
