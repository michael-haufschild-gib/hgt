import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.GaussianFiniteFilters

/-!
# Gaussian-damped natural-cone moments detect zero width

Finite positive-clock products isolate an actual zero below height `n^4`.
Their `exp(K n^6)` cost is beaten by seventh-power target amplification,
while Gaussian damping suppresses the remaining tail at eighth-power scale.
Thus bounded radially shifted moments exclude every zero beyond that rate.
-/

open Complex Finset Filter Topology
open Zeta23
open GaloisForLFunctions.SquareRootThreshold
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary

/-- A uniformly bounded clock filter preserves the Gaussian tail after positive-clock amplification. -/
lemma norm_gaussian_filtered_tail_le {τ σ a b T A : ℝ}
    (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hT : 0 ≤ T) (hA : 0 ≤ A) (P : zetaZeroConfig.carrier → ℂ)
    (hP : ∀ ρ, ‖P ρ‖ ≤ A) (m : ℕ) :
    ‖∑' ρ : zetaZeroConfig.carrier, if T < |(ρ:ℂ).im| then
      gaussianMixedResidue τ a b ρ*P ρ*shiftedClock σ a ρ^m else 0‖ ≤
      (A*Real.exp (a*(m:ℝ)/2+τ/4-τ*T^2))*(∑' ρ : zetaZeroConfig.carrier, ‖mixedResidue a b ρ‖) := by
  classical
  let K := A*Real.exp (a*(m:ℝ)/2+τ/4-τ*T^2)
  have hK : 0 ≤ K := mul_nonneg hA (Real.exp_pos _).le
  let f (ρ : zetaZeroConfig.carrier) := if T < |(ρ:ℂ).im| then
    gaussianMixedResidue τ a b ρ*P ρ*shiftedClock σ a ρ^m else 0
  have hbound (ρ : zetaZeroConfig.carrier) : ‖f ρ‖ ≤ K*‖mixedResidue a b ρ‖ := by
    dsimp only [f]
    split_ifs with hγ
    · rw [norm_mul,norm_mul,norm_pow]
      have hd := gaussianMixedResidue_tail_pointwise (a := a) (b := b) hτ hT ρ hγ.le
      have hU := pow_le_pow_left₀ (norm_nonneg _) (norm_shiftedClock_le hσ ha ρ) m
      calc
        _ ≤ (Real.exp (τ/4-τ*T^2)*‖mixedResidue a b ρ‖)*A*(Real.exp (a/2))^m :=
          mul_le_mul (mul_le_mul hd (hP ρ) (norm_nonneg _) (by positivity)) hU
            (pow_nonneg (norm_nonneg _) m) (by positivity)
        _ = K*‖mixedResidue a b ρ‖ := by
          rw [← Real.exp_nat_mul]
          dsimp only [K]
          have he : Real.exp (τ/4-τ*T^2)*Real.exp ((m:ℝ)*(a/2)) =
              Real.exp (a*(m:ℝ)/2+τ/4-τ*T^2) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc
            _ = A*(Real.exp (τ/4-τ*T^2)*Real.exp ((m:ℝ)*(a/2)))*‖mixedResidue a b ρ‖ := by ring
            _ = _ := by rw [he]
    · rw [norm_zero]
      exact mul_nonneg hK (norm_nonneg _)
  have hs := (summable_norm_mixedResidue ha hb).mul_left K
  have hnorm : Summable (fun ρ => ‖f ρ‖) := hs.of_nonneg_of_le (fun ρ => norm_nonneg _) hbound
  calc
    ‖∑' ρ, f ρ‖ ≤ ∑' ρ, ‖f ρ‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' ρ, K*‖mixedResidue a b ρ‖ := hnorm.tsum_le_tsum hbound hs
    _ = K*(∑' ρ, ‖mixedResidue a b ρ‖) := by rw [tsum_mul_left]

/-- A filter that kills the finite head bounds its surviving atom by the full sum and tail. -/
lemma norm_filtered_target_le (d P U : zetaZeroConfig.carrier → ℂ)
    (ρ₀ : zetaZeroConfig.carrier) (m : ℕ) {T : ℝ}
    (hs : Summable (fun ρ => d ρ*P ρ*U ρ^m))
    (htarget : |(ρ₀:ℂ).im| ≤ T) (hP₀ : P ρ₀=1)
    (hhead : ∀ ρ : zetaZeroConfig.carrier, ρ ≠ ρ₀ → |(ρ:ℂ).im| ≤ T → P ρ=0) :
    ‖d ρ₀*U ρ₀^m‖ ≤ ‖∑' ρ, d ρ*P ρ*U ρ^m‖+
      ‖∑' ρ : zetaZeroConfig.carrier, if T < |(ρ:ℂ).im| then d ρ*P ρ*U ρ^m else 0‖ := by
  classical
  let f (ρ : zetaZeroConfig.carrier) := d ρ*P ρ*U ρ^m
  let tail (ρ : zetaZeroConfig.carrier) := if T < |(ρ:ℂ).im| then f ρ else 0
  have ht : Summable tail := by
    apply Summable.of_norm
    refine hs.norm.of_nonneg_of_le (fun ρ => norm_nonneg _) fun ρ => ?_
    dsimp only [tail]
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (f ρ)
  have hpoint (ρ : zetaZeroConfig.carrier) :
      f ρ-tail ρ=if ρ=ρ₀ then d ρ₀*U ρ₀^m else 0 := by
    by_cases hρ : ρ=ρ₀
    · subst ρ
      simp only [tail,if_neg (not_lt.mpr htarget),f,hP₀,mul_one,sub_zero,ite_true]
    · by_cases hγ : T < |(ρ:ℂ).im|
      · simp only [tail,if_pos hγ,sub_self,if_neg hρ]
      · have hz := hhead ρ hρ (le_of_not_gt hγ)
        simp only [tail,if_neg hγ,f,hz,mul_zero,zero_mul,sub_self,if_neg hρ]
  have he : (∑' ρ, f ρ)-(∑' ρ, tail ρ)=d ρ₀*U ρ₀^m := by
    rw [← hs.tsum_sub ht,tsum_congr hpoint,tsum_ite_eq]
  rw [← he]
  exact norm_sub_le _ _

/-- Bounded Gaussian-damped moments on one positive two-prime cone exclude every
actual zero to the right of the allowed exponential growth rate. -/
theorem zeroOffset_re_le_of_bounded_gaussian_moments {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {τ σ M : ℝ}
    (hτ : 0 < τ) (hσ : 0 ≤ σ)
    (hM : ∀ m l : ℕ, ‖∑' ρ : zetaZeroConfig.carrier,
      gaussianMixedResidue τ (Real.log p) (Real.log q) ρ*
        shiftedClock σ (Real.log p) ρ^m*shiftedClock σ (Real.log q) ρ^l‖ ≤ M) :
    ∀ ρ : zetaZeroConfig.carrier, (zeroOffset ρ).re ≤ σ := by
  classical
  intro ρ₀
  by_contra hnot
  have hδ : σ < (zeroOffset ρ₀).re := lt_of_not_ge hnot
  let a := Real.log p
  let b := Real.log q
  have ha : 0 < a := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hb : 0 < b := Real.log_pos (by exact_mod_cast hq.one_lt)
  let d := gaussianMixedResidue τ a b
  let U := shiftedClock σ a
  let g := a*((zeroOffset ρ₀).re-σ)
  have hg : 0 < g := mul_pos ha (sub_pos.mpr hδ)
  have hd : d ρ₀ ≠ 0 := gaussianMixedResidue_ne_zero τ ha hb ρ₀ (hσ.trans_lt hδ)
  have hs (m l : ℕ) : Summable (fun ρ => d ρ*U ρ^m*shiftedClock σ b ρ^l) :=
    summable_shifted_gaussian_moment hτ.le hσ ha.le hb.le m l
  obtain ⟨K,R,hK,hR,hγR,hfilter⟩ := exists_actual_clock_filters hp hq hpq hσ ρ₀
  let L := Real.exp (τ/4)*(∑' ρ : zetaZeroConfig.carrier, ‖mixedResidue a b ρ‖)
  have hestimate (n : ℕ) (hn : R ≤ (n:ℝ)) :
      ‖d ρ₀‖ ≤ M*Real.exp (K*(n:ℝ)^6-g*(n:ℝ)^7)+
        L*Real.exp (K*(n:ℝ)^6+(a/2-g)*(n:ℝ)^7-τ*(n:ℝ)^8) := by
    obtain ⟨P,hP₀,hhead,hP,hcontrol⟩ := hfilter n hn
    have hn1 : 1 ≤ (n:ℝ) := hR.trans hn
    have hn0 : 0 ≤ (n:ℝ) := zero_le_one.trans hn1
    have htarget : |(ρ₀:ℂ).im| ≤ (n:ℝ)^4 :=
      (hγR.trans hn).trans (le_self_pow₀ hn1 (by norm_num))
    have hctrl := hcontrol d M hs hM (n^7) 0
    simp only [pow_zero,mul_one] at hctrl
    have hsplit := norm_filtered_target_le d P U ρ₀ (n^7) hctrl.1 htarget hP₀ hhead
    have htail := norm_gaussian_filtered_tail_le hτ.le hσ ha.le hb.le
      (pow_nonneg hn0 4) (Real.exp_pos (K*(n:ℝ)^6)).le P hP (n^7)
    have htailEq :
        (Real.exp (K*(n:ℝ)^6)*Real.exp (a*((n^7:ℕ):ℝ)/2+τ/4-τ*((n:ℝ)^4)^2))*
          (∑' ρ : zetaZeroConfig.carrier, ‖mixedResidue a b ρ‖) =
        L*Real.exp (K*(n:ℝ)^6+(a/2)*(n:ℝ)^7-τ*(n:ℝ)^8) := by
      have he : Real.exp (K*(n:ℝ)^6)*Real.exp (a*((n^7:ℕ):ℝ)/2+τ/4-τ*((n:ℝ)^4)^2) =
          Real.exp (τ/4)*Real.exp (K*(n:ℝ)^6+(a/2)*(n:ℝ)^7-τ*(n:ℝ)^8) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [he]
      dsimp only [L]
      ring
    rw [htailEq] at htail
    have hterm : ‖d ρ₀*U ρ₀^(n^7)‖=‖d ρ₀‖*Real.exp (g*(n:ℝ)^7) := by
      rw [norm_mul,norm_pow,norm_shiftedClock,← Real.exp_nat_mul]
      congr 1
      congr 1
      dsimp only [g]
      push_cast
      ring
    rw [hterm] at hsplit
    have hmain : ‖d ρ₀‖*Real.exp (g*(n:ℝ)^7) ≤ M*Real.exp (K*(n:ℝ)^6)+
        L*Real.exp (K*(n:ℝ)^6+(a/2)*(n:ℝ)^7-τ*(n:ℝ)^8) :=
      hsplit.trans (add_le_add hctrl.2 htail)
    calc
      ‖d ρ₀‖ ≤ (M*Real.exp (K*(n:ℝ)^6)+
          L*Real.exp (K*(n:ℝ)^6+(a/2)*(n:ℝ)^7-τ*(n:ℝ)^8))/Real.exp (g*(n:ℝ)^7) :=
        (le_div_iff₀ (Real.exp_pos _)).mpr hmain
      _ = _ := by
        simp only [add_div,mul_div_assoc,← Real.exp_sub]
        rw [show K*(n:ℝ)^6+(a/2)*(n:ℝ)^7-τ*(n:ℝ)^8-g*(n:ℝ)^7 =
          K*(n:ℝ)^6+(a/2-g)*(n:ℝ)^7-τ*(n:ℝ)^8 by ring]
  have hcast : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlim₁ : Tendsto (fun n : ℕ => M*Real.exp (K*(n:ℝ)^6-g*(n:ℝ)^7)) atTop (nhds 0) := by
    simpa only [Function.comp_def,mul_zero] using ((tendsto_exp_six_sub_seven K hg).comp hcast).const_mul M
  have hlim₂ : Tendsto (fun n : ℕ =>
      L*Real.exp (K*(n:ℝ)^6+(a/2-g)*(n:ℝ)^7-τ*(n:ℝ)^8)) atTop (nhds 0) := by
    simpa only [Function.comp_def,mul_zero] using ((tendsto_exp_six_seven_sub_eight K (a/2-g) hτ).comp hcast).const_mul L
  have hlim := hlim₁.add hlim₂
  have hbound : ∀ᶠ n : ℕ in atTop, ‖d ρ₀‖ ≤
      M*Real.exp (K*(n:ℝ)^6-g*(n:ℝ)^7)+
        L*Real.exp (K*(n:ℝ)^6+(a/2-g)*(n:ℝ)^7-τ*(n:ℝ)^8) := by
    filter_upwards [hcast.eventually (eventually_ge_atTop R)] with n hn
    exact hestimate n hn
  have hz : ‖d ρ₀‖ ≤ 0 := by simpa only [zero_add] using ge_of_tendsto hlim hbound
  exact (norm_pos_iff.mpr hd).not_ge hz

/-- Gaussian-damped positive two-prime moments read the actual zero width,
including an unattained boundary. -/
theorem zetaZeroWidth_le_iff_bounded_gaussian_moments {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {τ σ : ℝ}
    (hτ : 0 < τ) (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ ∃ M : ℝ, ∀ m l : ℕ,
      ‖∑' ρ : zetaZeroConfig.carrier, gaussianMixedResidue τ (Real.log p) (Real.log q) ρ*
        shiftedClock σ (Real.log p) ρ^m*shiftedClock σ (Real.log q) ρ^l‖ ≤ M := by
  have ha : 0 ≤ Real.log p := (Real.log_pos (by exact_mod_cast hp.one_lt)).le
  have hb : 0 ≤ Real.log q := (Real.log_pos (by exact_mod_cast hq.one_lt)).le
  constructor
  · intro hwidth
    let d := gaussianMixedResidue τ (Real.log p) (Real.log q)
    have hd := summable_norm_gaussianMixedResidue hτ.le ha hb
    have hclock (a : ℝ) (ha : 0 ≤ a) (ρ : zetaZeroConfig.carrier) :
        ‖shiftedClock σ a ρ‖ ≤ 1 := by
      rw [norm_shiftedClock]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ha
        (sub_nonpos.mpr ((zeroOffset_re_le_width ρ).trans hwidth)))
    refine ⟨∑' ρ : zetaZeroConfig.carrier, ‖d ρ‖,?_⟩
    intro m l
    have hs := summable_shifted_gaussian_moment hτ.le hσ ha hb m l
    calc
      _ ≤ ∑' ρ : zetaZeroConfig.carrier,
          ‖d ρ*shiftedClock σ (Real.log p) ρ^m*shiftedClock σ (Real.log q) ρ^l‖ :=
        norm_tsum_le_tsum_norm hs.norm
      _ ≤ ∑' ρ : zetaZeroConfig.carrier, ‖d ρ‖ := by
        apply hs.norm.tsum_le_tsum _ hd
        intro ρ
        rw [norm_mul,norm_mul,norm_pow,norm_pow]
        have hA : ‖shiftedClock σ (Real.log p) ρ‖^m ≤ 1 := by
          simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (hclock _ ha ρ) m
        have hB : ‖shiftedClock σ (Real.log q) ρ‖^l ≤ 1 := by
          simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (hclock _ hb ρ) l
        calc
          _ ≤ ‖d ρ‖*1*1 := mul_le_mul
            (mul_le_mul_of_nonneg_left hA (norm_nonneg _)) hB
            (pow_nonneg (norm_nonneg _) l) (by positivity)
          _ = _ := by rw [mul_one,mul_one]
  · rintro ⟨M,hM⟩
    apply (zetaZeroWidth_le_iff_re_le hσ).mpr
    intro ρ hρ
    have hh := zeroOffset_re_le_of_bounded_gaussian_moments hp hq hpq hτ hσ hM ⟨ρ,hρ⟩
    rw [zeroOffset_re] at hh
    linarith only [hh]

#print axioms norm_gaussian_filtered_tail_le
#print axioms zetaZeroWidth_le_iff_bounded_gaussian_moments
#print axioms zeroOffset_re_le_of_bounded_gaussian_moments
#print axioms norm_filtered_target_le
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
