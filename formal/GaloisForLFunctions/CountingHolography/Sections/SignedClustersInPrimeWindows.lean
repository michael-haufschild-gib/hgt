import GaloisForLFunctions.CountingHolography.Sections.PrimeTraceWindows
import GaloisForLFunctions.SurfaceOfSpecZ.AlmostAllPrimesAndTheStepanovBoundary

/-!
# Signed clusters of rational sections

Anchor a positive mass at conductor one and distribute positive net mass
among conductors in a power window. Bound both the anchor and the total
variation by a fixed multiple of the smaller mass. All these signed
clusters have positive degree on the same arbitrarily late prime windows. The original contact generator is then a small section on each ray.
-/

noncomputable section

namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology ArithmeticScatteringHolography ArithmeticCastelnuovoSeveri
open RenormalizedIntersectionTheory

private def pairing {N : ℕ} (a b : Fin N → ℤ) : ℝ :=
  ∑ i, (a i : ℝ) * ∑ j, (b j : ℝ) * (atomGram N i j).re

private theorem probe_eq_pairing {N : ℕ} (a : Fin N → ℤ) :
    integerProbe N a = pairing a a := by
  rw [integerProbe_eq_sum, pairing]
  simp only [mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

private theorem pairing_comm {N : ℕ} (a b : Fin N → ℤ) : pairing a b = pairing b a := by
  unfold pairing
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
  have hc : starRingEnd ℂ (atomGram N i j) = atomGram N j i :=
    congr_fun (congr_fun (atomGram_isHermitian N) j) i
  have hr : (atomGram N i j).re = (atomGram N j i).re := by simpa using congr_arg Complex.re hc
  rw [hr]
  ring

private theorem pairing_add_left {N : ℕ} (a b d : Fin N → ℤ) :
    pairing (a+b) d = pairing a d + pairing b d := by
  simp only [pairing, Pi.add_apply, Int.cast_add, add_mul, sum_add_distrib]

private theorem pairing_anchor {N : ℕ} (c : ℤ) (b : Fin (N+1) → ℤ) :
    pairing (Pi.single 0 c) b =
      (c : ℝ) * ∑ j, (b j : ℝ) * (splineSeries (Real.log ((j : ℝ)+1))).re := by
  rw [pairing]
  simp only [Pi.single_apply, Int.cast_ite, Int.cast_zero, ite_mul, zero_mul,
    sum_ite_eq', mem_univ, if_true]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  have hc : starRingEnd ℂ (atomGram (N+1) j 0) = atomGram (N+1) 0 j :=
    congr_fun (congr_fun (atomGram_isHermitian (N+1)) 0) j
  have hr : (atomGram (N+1) j 0).re = (atomGram (N+1) 0 j).re := by
    simpa using congr_arg Complex.re hc
  rw [← hr, atomGram_eq_splineSeries]
  simp

private theorem anchored_probe {N : ℕ} (c : ℤ) (b : Fin (N+1) → ℤ) :
    integerProbe (N+1) (Pi.single 0 c + b) =
      (c : ℝ)^2 * (splineSeries 0).re +
      (c : ℝ) * (∑ j, (b j : ℝ) * (2 * (splineSeries (Real.log ((j : ℝ)+1))).re)) +
      pairing b b := by
  let e : Fin (N+1) → ℤ := Pi.single 0 c
  have hsum : pairing e e = (c : ℝ)^2 * (splineSeries 0).re := by
    rw [pairing_anchor]
    simp [e, Pi.single_apply, ite_mul, pow_two, mul_assoc]
  have hcross : (∑ j, (b j : ℝ) * (2*(splineSeries (Real.log ((j : ℝ)+1))).re)) =
      2 * ∑ j, (b j : ℝ) * (splineSeries (Real.log ((j : ℝ)+1))).re := by
    rw [mul_sum]
    exact sum_congr rfl fun _ _ => by ring
  change integerProbe (N+1) (e+b) = _
  rw [probe_eq_pairing, pairing_add_left, pairing_comm e (e+b), pairing_add_left,
    pairing_comm b (e+b), pairing_add_left, pairing_comm b e, hsum, hcross, pairing_anchor]
  ring

private theorem abs_weighted_sum {ι : Type*} [Fintype ι] (b : ι → ℤ) (f : ι → ℝ) {E : ℝ}
    (h : ∀ i, b i ≠ 0 → |f i| ≤ E) :
    |∑ i, (b i : ℝ) * f i| ≤ (∑ i, |(b i : ℝ)|) * E := by
  apply (abs_sum_le_sum_abs _ _).trans
  rw [sum_mul]
  refine sum_le_sum fun i _ => ?_
  by_cases hi : b i = 0
  · simp [hi]
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h i hi) (abs_nonneg _)

/-- Dyadic conductor ratios have uniformly bounded spline correlation. -/
private theorem exists_dyadic_gram_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (p x y : ℝ), 0 < p → p ≤ x → x ≤ 2*p → p ≤ y → y ≤ 2*p →
      |(splineSeries (Real.log x - Real.log y)).re| ≤ D := by
  have hc : Continuous fun t : ℝ => |(splineSeries t).re| :=
    (Complex.continuous_re.comp continuous_splineSeries).abs
  obtain ⟨D,hD⟩ := (isCompact_Icc (a := -Real.log 2) (b := Real.log 2)).bddAbove_image hc.continuousOn
  refine ⟨|D|,abs_nonneg _,fun p x y hp hx hx' hy hy' => ?_⟩
  have hlow (z : ℝ) (hz : p ≤ z) := Real.log_le_log hp hz
  have hupp (z : ℝ) (hz : p ≤ z) (hz' : z ≤ 2*p) :
      Real.log z ≤ Real.log 2 + Real.log p := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hp.ne']
    exact Real.log_le_log (hp.trans_le hz) hz'
  apply (le_trans ?_ (le_abs_self D))
  apply hD
  exact ⟨_,⟨by linarith only [hlow x hx, hupp y hy hy'], by linarith only [hlow y hy, hupp x hx hx']⟩,rfl⟩

private theorem positive_degree_sections {N : ℕ} (a : Fin N → ℤ) (hq : 0 < integerProbe N a) :
    (∀ᶠ m : ℕ in atTop, 1 ∈ smallSections (generator (m • a) : ℝ) (radius (m • a))) ∧
      Tendsto (fun m : ℕ => (splineCount (m • a) : ℝ) / (m : ℝ)^2) atTop
        (𝓝 (integerProbe N a)) := by
  constructor
  · filter_upwards [eventually_log_generator_lt_radius hq] with m hfit
    have hdq : 0 < generator (m • a) := contactGenerator_pos _ _ _
    have hd : 0 < (generator (m • a) : ℝ) := by exact_mod_cast hdq
    apply (mem_smallSections hd 1).mpr
    simpa only [Int.cast_one, mul_one, abs_of_pos hd] using (Real.log_le_iff_le_exp hd).mp hfit.le
  · have ht := splineCount_tateLimit a
    rw [max_eq_left hq.le] at ht
    exact ht

/-- The cross term pays for the anchor diagonal and for every pair inside the cluster. -/
private theorem positive_mass_estimate {c M V K D R s t y z : ℝ}
    (hc : 0 < c) (hm : 0 < M) (hv : 0 ≤ V) (hk : 0 ≤ K) (hd : 0 ≤ D) (hr : 0 ≤ R)
    (hsize : max c V ≤ K * min c M) (hpeak : D*K^2 + K*|s| + K*R < t)
    (hcross : -(V*R) ≤ y - M*t) (hself : |z| ≤ V*(V*D)) :
    0 < c^2*s + c*y + z := by
  have hvc : V ≤ K*c := (le_max_right _ _).trans
    (hsize.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hk))
  have hmass := hsize.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hk)
  have hvm : V ≤ K*M := (le_max_right _ _).trans hmass
  have hcm : c ≤ K*M := (le_max_left _ _).trans hmass
  have hcost := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hvm hr) hc.le
  have hquad := mul_le_mul_of_nonneg_right (mul_le_mul hvc hvm hv (mul_nonneg hk hc.le)) hd
  have hdiag := mul_le_mul_of_nonneg_left (neg_le_abs s) (sq_nonneg c)
  have hanchor := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcm hc.le) (abs_nonneg s)
  linarith only [mul_lt_mul_of_pos_left hpeak (mul_pos hc hm),
    mul_le_mul_of_nonneg_left hcross hc.le, hcost, hquad, hdiag, hanchor, (abs_le.mp hself).1]

private theorem cluster_positive_at_peak {β K D R : ℝ} {p : ℕ} (hp : p.Prime)
    (hβ : β < 1) (hK : 0 ≤ K) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hgram : ∀ p x y : ℝ, 0 < p → p ≤ x → x ≤ 2*p → p ≤ y → y ≤ 2*p →
      |(splineSeries (Real.log x - Real.log y)).re| ≤ D)
    (hpeak : D*K^2 + K*|(splineSeries 0).re| + K*R < 2*(splineSeries (Real.log p)).re)
    (hflat : ∀ x : ℝ, p ≤ x → x ≤ p + (p : ℝ)^β →
      |2*(splineSeries (Real.log x)).re - 2*(splineSeries (Real.log p)).re| ≤ R)
    {N : ℕ} (c : ℤ) (b : Fin (N+1) → ℤ) (hc : 0 < c) (hm : 0 < ∑ i, (b i : ℝ))
    (hv : max (c : ℝ) (∑ i, |(b i : ℝ)|) ≤ K * min (c : ℝ) (∑ i, (b i : ℝ)))
    (hwin : ∀ i, b i ≠ 0 → (p : ℝ) ≤ (i : ℝ)+1 ∧ (i : ℝ)+1 ≤ p + (p : ℝ)^β) :
    0 < integerProbe (N+1) (Pi.single 0 c + b) := by
  let M := ∑ i, (b i : ℝ)
  let V := ∑ i, |(b i : ℝ)|
  let T := fun x : ℝ => 2 * (splineSeries (Real.log x)).re
  have hc' : 0 < (c : ℝ) := by exact_mod_cast hc
  change 0 < M at hm
  change max (c : ℝ) V ≤ K * min (c : ℝ) M at hv
  have hV : 0 ≤ V := sum_nonneg fun _ _ => abs_nonneg _
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have h2 : (p : ℝ) + (p : ℝ)^β ≤ 2*p := by
    have he := Real.rpow_le_rpow_of_exponent_le hp1 hβ.le
    rw [Real.rpow_one] at he
    linarith only [he]
  have hinner (i : Fin (N+1)) (hi : b i ≠ 0) :
      |∑ j, (b j : ℝ) * (atomGram (N+1) i j).re| ≤ V*D := by
    apply abs_weighted_sum
    intro j hj
    rw [atomGram_eq_splineSeries]
    obtain ⟨hlo,hup⟩ := hwin i hi
    obtain ⟨hlo',hup'⟩ := hwin j hj
    exact hgram p _ _ (zero_lt_one.trans_le hp1) hlo (hup.trans h2) hlo' (hup'.trans h2)
  have hself : |pairing b b| ≤ V*(V*D) := abs_weighted_sum b _ hinner
  have hdiff := abs_weighted_sum b (fun i => T ((i : ℝ)+1) - T p)
    (fun i hi => hflat _ (hwin i hi).1 (hwin i hi).2)
  simp only [mul_sub, sum_sub_distrib, ← sum_mul] at hdiff
  have hcross := (abs_le.mp hdiff).1
  change - (V*R) ≤ (∑ i, (b i : ℝ) * T ((i : ℝ)+1)) - M*T p at hcross
  rw [anchored_probe]
  exact positive_mass_estimate (t := T p) hc' hm hV hK hD hR hv hpeak hcross hself

private theorem anchored_ne_zero {N p : ℕ} (hp : p.Prime) {c : ℤ} (hc : 0 < c)
    {b : Fin (N+1) → ℤ} (hlo : ∀ i, b i ≠ 0 → (p : ℝ) ≤ (i : ℝ)+1) :
    Pi.single 0 c + b ≠ 0 := by
  have hb : b 0 = 0 := by
    by_contra hn
    have hh : (p : ℝ) ≤ 1 := by simpa using hlo 0 hn
    exact hp.one_lt.not_ge (by exact_mod_cast hh)
  intro hz
  have hh := congrFun hz 0
  simp [hb, hc.ne'] at hh

/-- In arbitrarily late prime windows the generator itself is small on
every signed cluster whose anchor and total variation are bounded by a
fixed multiple of both positive masses. Its ordinary
section count realizes the full signed Weil degree in the Tate limit. -/
theorem prime_windows_of_signed_cluster_sections {β K : ℝ} (hβ : β < 1) (hK : 0 ≤ K) (P : ℕ) :
    ∃ p ≥ P, p.Prime ∧ ∀ (N : ℕ) (c : ℤ) (b : Fin (N+1) → ℤ), 0 < c →
      0 < (∑ i, (b i : ℝ)) →
      max (c : ℝ) (∑ i, |(b i : ℝ)|) ≤ K * min (c : ℝ) (∑ i, (b i : ℝ)) →
      (∀ i, b i ≠ 0 → (p : ℝ) ≤ (i : ℝ)+1 ∧ (i : ℝ)+1 ≤ p + (p : ℝ)^β) →
      let a := Pi.single 0 c + b
      (∀ᶠ m : ℕ in atTop, 1 ∈ smallSections (generator (m • a) : ℝ) (radius (m • a))) ∧
        Tendsto (fun m : ℕ => (splineCount (m • a) : ℝ) / (m : ℝ)^2) atTop
          (𝓝 (integerProbe (N+1) a)) := by
  by_cases hRH : RiemannHypothesis
  · obtain ⟨p,hP,hp⟩ := Nat.exists_infinite_primes P
    refine ⟨p,hP,hp,fun N c b hc _ _ hwin => positive_degree_sections _ ?_⟩
    exact integerProbe_pos_of_rh hRH
      (anchored_ne_zero hp hc (b := b) (fun i hi => (hwin i hi).1))
  obtain ⟨D,hD,hgram⟩ := exists_dyadic_gram_bound
  obtain ⟨p,hP,hp,R,hR,hpeak,hflat⟩ := primeTrace_dominates_window_oscillation hRH hβ
    (D*K^2 + K*|(splineSeries 0).re|) hK P
  refine ⟨p,hP,hp,fun N c b hc hm hv hwin => positive_degree_sections _ ?_⟩
  exact cluster_positive_at_peak hp hβ hK hD hR hgram hpeak hflat c b hc hm hv hwin

/-- Beyond the short-interval prime number theorem threshold, a single
multiplicity tail serves a whole run of at least `p^β / (4 log p)`
consecutive primes beyond the centre. -/
theorem prime_windows_of_many_simultaneous_sections {β : ℝ} (hlo : 7 / 12 < β)
    (hβ : β < 1) (P : ℕ) :
    ∃ p ≥ P, p.Prime ∧
      let W := _root_.RHTower.Sieve.windowPrimes (p : ℝ) (p + (p : ℝ)^β)
      (p : ℝ)^β / (4 * Real.log p) ≤ W.card ∧
        ∀ᶠ m : ℕ in atTop, ∀ q ∈ W,
          Real.log (contactModulus (m • primePair q)) < radius (m • primePair q) := by
  have hθ := (SurfaceOfSpecZ.tendsto_theta_short_window_div_seven_twelfths hlo hβ).comp
    tendsto_natCast_atTop_atTop
  obtain ⟨P₀,h₀⟩ := eventually_atTop.mp
    (hθ.eventually_const_lt (by norm_num : (1 : ℝ)/2 < 1))
  obtain ⟨p,hPP,hp,hfit⟩ := prime_windows_of_simultaneous_modulus_fit hβ (max P P₀)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hw := Real.rpow_pos_of_pos hp0 β
  let W := _root_.RHTower.Sieve.windowPrimes (p : ℝ) (p + (p : ℝ)^β)
  have hmem {q : ℕ} (h : q ∈ W) : p < q ∧ (q : ℝ) ≤ p + (p : ℝ)^β := by
    obtain ⟨hq,_⟩ := _root_.RHTower.Sieve.mem_windowPrimes.mp h
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hq
    exact ⟨by simpa only [Nat.floor_natCast] using hl,
      (Nat.le_floor_iff (add_nonneg hp0.le hw.le)).mp hu⟩
  refine ⟨p,(le_max_left _ _).trans hPP,hp,?_,?_⟩
  · have hl := h₀ p ((le_max_right _ _).trans hPP)
    change 1 / 2 < (Chebyshev.theta (p + (p : ℝ)^β) - Chebyshev.theta p) / (p : ℝ)^β at hl
    have hm : 1 / 2 * (p : ℝ)^β < ∑ q ∈ W, Real.log q := by
      rw [_root_.RHTower.Sieve.theta_sub_eq_sum_Ioc (le_add_of_nonneg_right hw.le)] at hl
      exact (lt_div_iff₀ hw).mp hl
    have he := Real.rpow_le_rpow_of_exponent_le hp1.le hβ.le
    rw [Real.rpow_one] at he
    have hu : ∑ q ∈ W, Real.log q ≤ W.card * (2 * Real.log p) := by
      calc _ ≤ ∑ _ ∈ W, 2 * Real.log p := by
             refine sum_le_sum fun q hq => ?_
             have hq0 : (0 : ℝ) < q := by exact_mod_cast hp.pos.trans (hmem hq).1
             have hqle : (q : ℝ) ≤ 2*p := by linarith only [(hmem hq).2, he]
             have hlog := Real.log_le_log hq0 hqle
             rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hp0.ne'] at hlog
             linarith only [hlog, Real.log_le_log (by norm_num : (0 : ℝ) < 2) hp2]
           _ = _ := by simp only [sum_const, nsmul_eq_mul]
    apply (div_le_iff₀ (mul_pos (by norm_num) (Real.log_pos hp1))).mpr
    linarith only [hm, hu]
  · exact hfit.mono fun m hm q hq => hm q (hmem hq).1.le (hmem hq).2

#print axioms prime_windows_of_many_simultaneous_sections
#print axioms prime_windows_of_signed_cluster_sections

end GaloisForLFunctions.CountingHolography.Sections
