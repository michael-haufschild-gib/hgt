import GaloisForLFunctions.HTGeometry.FactorialModulusProfile
import GaloisForLFunctions.HTGeometry.MaximumTermCentralIndex

/-!
# The factorial profile has order one and exponential type one

An entire function whose Taylor coefficient magnitudes are `1/n!` has `‖f z‖ ≤ exp ‖z‖`, and on
every large circle it comes within `exp (−ε r)` of that bound: splitting the exponential series at
`2 e r` shows that one Cauchy coefficient estimate would otherwise cap the whole series.

Both the exponential and its phase-randomized companion therefore have order one and exponential
type one, as the card's item 4 asserts.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem summable_factorialProfile_term (r : ℝ) :
    Summable (fun n : ℕ => r ^ n / (n.factorial : ℝ)) := by
  exact NormedSpace.expSeries_div_summable r

theorem tsum_factorialProfile_term (r : ℝ) :
    ∑' n : ℕ, r ^ n / (n.factorial : ℝ) = Real.exp r := by
  have h1 : Real.exp = NormedSpace.exp := Real.exp_eq_exp_ℝ
  have h2 : (NormedSpace.exp : ℝ → ℝ) = fun x : ℝ => ∑' n : ℕ, x ^ n / (n.factorial : ℝ) :=
    NormedSpace.exp_eq_tsum_div
  rw [h1, h2]

/-- **Type at most one.**  A function whose Taylor moduli are `1/n!` is dominated by `exp ‖z‖`. -/
theorem norm_le_exp_of_factorial_moduli {f : ℂ → ℂ} {c : ℕ → ℂ}
    (hsum : ∀ z : ℂ, f z = ∑' n : ℕ, c n * z ^ n)
    (hnorm : ∀ n, ‖c n‖ = 1 / (n.factorial : ℝ)) (z : ℂ) :
    ‖f z‖ ≤ Real.exp ‖z‖ := by
  have hsummable : Summable (fun n : ℕ => ‖c n * z ^ n‖) := by
    have hEq : (fun n : ℕ => ‖c n * z ^ n‖) = fun n : ℕ => ‖z‖ ^ n / (n.factorial : ℝ) := by
      funext n
      rw [norm_mul, hnorm n, norm_pow]
      ring
    rw [hEq]
    exact summable_factorialProfile_term ‖z‖
  have hbound := norm_tsum_le_tsum_norm hsummable
  rw [hsum z]
  refine le_trans hbound ?_
  have hEq : (fun n : ℕ => ‖c n * z ^ n‖) = fun n : ℕ => ‖z‖ ^ n / (n.factorial : ℝ) := by
    funext n
    rw [norm_mul, hnorm n, norm_pow]
    ring
  rw [hEq, tsum_factorialProfile_term]

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

/-- The elementary factorial bound `m ! ≥ (m/e)^m`, in the form `r^m/m! ≤ (e r/m)^m`. -/
theorem pow_div_factorial_le (m : ℕ) : ((m : ℝ) ^ m) / (m.factorial : ℝ) ≤ Real.exp m := by
  have hsum := Real.sum_le_exp_of_nonneg (x := (m : ℝ)) (by positivity) (m + 1)
  have hmem : ((m : ℝ) ^ m) / (m.factorial : ℝ)
      ≤ ∑ i ∈ Finset.range (m + 1), ((m : ℝ) ^ i) / (i.factorial : ℝ) := by
    refine Finset.single_le_sum (f := fun i : ℕ => ((m : ℝ) ^ i) / (i.factorial : ℝ)) ?_ ?_
    · intro i _
      positivity
    · exact Finset.self_mem_range_succ m
  exact le_trans hmem hsum

/-- Terms of the exponential series beyond `2 e r` are dominated by a geometric series. -/
theorem term_le_geometric {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 2 * Real.exp 1 * r ≤ m) :
    r ^ m / (m.factorial : ℝ) ≤ (1 / 2 : ℝ) ^ m := by
  have hm0 : 0 < (m : ℝ) := lt_of_lt_of_le (by positivity) hm
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by positivity
  have hbound : ((m : ℝ) ^ m) / (m.factorial : ℝ) ≤ Real.exp m := pow_div_factorial_le m
  have hexpm : Real.exp (m : ℝ) = Real.exp 1 ^ m := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have h1 : ((m : ℝ) ^ m) ≤ Real.exp (m : ℝ) * (m.factorial : ℝ) := by
    have h2 := (div_le_iff₀ hfac).mp hbound
    linarith
  have hkey : r ^ m / (m.factorial : ℝ) ≤ (Real.exp 1 * r / m) ^ m := by
    rw [div_pow, mul_pow, div_le_div_iff₀ hfac (by positivity)]
    calc r ^ m * (m : ℝ) ^ m
        ≤ r ^ m * (Real.exp (m : ℝ) * (m.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.exp 1 ^ m * r ^ m * (m.factorial : ℝ) := by rw [hexpm]; ring
  refine le_trans hkey ?_
  have hratio : Real.exp 1 * r / (m : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hm0 (by norm_num)]
    linarith
  have hnn : 0 ≤ Real.exp 1 * r / (m : ℝ) := by positivity
  exact pow_le_pow_left₀ hnn hratio m

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

theorem summable_shifted_factorial (r : ℝ) (K : ℕ) :
    Summable (fun n : ℕ => r ^ (n + K) / ((n + K).factorial : ℝ)) :=
  (summable_factorialProfile_term r).comp_injective (add_left_injective K)

/-- The exponential series beyond `2 e r` contributes at most one. -/
theorem tail_le_one {r : ℝ} (hr : 0 < r) {K : ℕ} (hK : 2 * Real.exp 1 * r ≤ (K : ℝ))
    (hK1 : 1 ≤ K) :
    ∑' n : ℕ, r ^ (n + K) / ((n + K).factorial : ℝ) ≤ 1 := by
  have hle : ∀ n : ℕ, r ^ (n + K) / ((n + K).factorial : ℝ) ≤ (1 / 2 : ℝ) ^ (n + K) := by
    intro n
    refine term_le_geometric hr ?_
    have hmono : (K : ℝ) ≤ ((n + K : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left K n
    linarith
  have hgeo : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + K)) := by
    have := (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1:ℝ)/2 < 1))
    simpa [pow_add] using this.mul_right ((1 / 2 : ℝ) ^ K)
  have hsum : ∑' n : ℕ, r ^ (n + K) / ((n + K).factorial : ℝ)
      ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + K) :=
    Summable.tsum_le_tsum hle (summable_shifted_factorial r K) hgeo
  refine le_trans hsum ?_
  have hval : ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + K) = (1 / 2 : ℝ) ^ K * 2 := by
    have : ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + K) = ((1:ℝ)/2) ^ K * ∑' n : ℕ, (1 / 2 : ℝ) ^ n := by
      rw [← tsum_mul_left]
      congr 1
      funext n
      rw [pow_add]
      ring
    rw [this, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  rw [hval]
  have hpow : (1 / 2 : ℝ) ^ K ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ K ≤ (1 / 2 : ℝ) ^ (1 : ℕ) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hK1
      _ = 1 / 2 := by norm_num
  linarith

/-- **Type at least one.**  A function whose Taylor moduli are `1/n!` exceeds `exp ((1−ε) r)`
somewhere on every large circle. -/
theorem exists_sphere_norm_ge_of_factorial_moduli {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnorm : ∀ n : ℕ, ‖iteratedDeriv n f 0 / (n.factorial : ℂ)‖ = 1 / (n.factorial : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, ∃ z ∈ Metric.sphere (0 : ℂ) r,
      Real.exp ((1 - ε) * r) ≤ ‖f z‖ := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (2 * (4 * Real.exp 1 + 4) / ε ^ (2 : ℕ) + 1)] with r hr1 hrbig
  by_contra hcon
  push Not at hcon
  have hr : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
  set C : ℝ := Real.exp ((1 - ε) * r) with hC
  have hsphere : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖f z‖ ≤ C := by
    intro z hz
    exact le_of_lt (hcon z hz)
  have hcoeff : ∀ n : ℕ, r ^ n / (n.factorial : ℝ) ≤ C := by
    intro n
    have h := taylorCoeff_norm_mul_pow_le hf hr hsphere n
    rw [hnorm n] at h
    calc r ^ n / (n.factorial : ℝ) = 1 / (n.factorial : ℝ) * r ^ n := by ring
      _ ≤ C := h
  -- split the exponential series
  set K : ℕ := ⌈2 * Real.exp 1 * r⌉₊ + 1 with hKdef
  have hKge : 2 * Real.exp 1 * r ≤ (K : ℝ) := by
    have := Nat.le_ceil (2 * Real.exp 1 * r)
    rw [hKdef]
    push_cast
    linarith
  have hK1 : 1 ≤ K := by omega
  have hKle : (K : ℝ) ≤ 2 * Real.exp 1 * r + 2 := by
    have hceil := Nat.ceil_lt_add_one (le_of_lt (by positivity : (0:ℝ) < 2 * Real.exp 1 * r))
    rw [hKdef]
    push_cast
    linarith
  have hsplit : (∑ n ∈ Finset.range K, r ^ n / (n.factorial : ℝ))
      + ∑' n : ℕ, r ^ (n + K) / ((n + K).factorial : ℝ) = Real.exp r := by
    rw [← tsum_factorialProfile_term r]
    exact Summable.sum_add_tsum_nat_add K (summable_factorialProfile_term r)
  have htail : ∑' n : ℕ, r ^ (n + K) / ((n + K).factorial : ℝ) ≤ 1 := tail_le_one hr hKge hK1
  have hfin : (∑ n ∈ Finset.range K, r ^ n / (n.factorial : ℝ)) ≤ (K : ℝ) * C := by
    calc (∑ n ∈ Finset.range K, r ^ n / (n.factorial : ℝ))
        ≤ ∑ _n ∈ Finset.range K, C := Finset.sum_le_sum fun n _ => hcoeff n
      _ = (K : ℝ) * C := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the growth contradiction
  have hexp : Real.exp r ≤ (K : ℝ) * C + 1 := by linarith [hsplit, htail, hfin]
  have hCval : C = Real.exp r * Real.exp (-(ε * r)) := by
    rw [hC, ← Real.exp_add]
    ring_nf
  have hquad : 1 + ε * r + (ε * r) ^ (2 : ℕ) / 2 ≤ Real.exp (ε * r) := by
    have h := Real.sum_le_exp_of_nonneg (x := ε * r) (by positivity) 3
    have hsum : ∑ i ∈ Finset.range 3, (ε * r) ^ i / (i.factorial : ℝ)
        = 1 + ε * r + (ε * r) ^ (2 : ℕ) / 2 := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [hsum] at h
    exact h
  have hexppos : (0 : ℝ) < Real.exp r := Real.exp_pos r
  have hkey : Real.exp (ε * r) ≤ (K : ℝ) + Real.exp (-(r)) * Real.exp (ε * r) := by
    have hmul := mul_le_mul_of_nonneg_right hexp (le_of_lt (Real.exp_pos (ε * r - r)))
    rw [hCval] at hmul
    have hexpid : Real.exp r * Real.exp (-(ε * r)) * Real.exp (ε * r - r) = Real.exp (-(0:ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      ring_nf
    have hexpid2 : Real.exp r * Real.exp (ε * r - r) = Real.exp (ε * r) := by
      rw [← Real.exp_add]
      ring_nf
    have hexpid3 : Real.exp (ε * r - r) = Real.exp (-(r)) * Real.exp (ε * r) := by
      rw [← Real.exp_add]
      ring_nf
    calc Real.exp (ε * r) = Real.exp r * Real.exp (ε * r - r) := hexpid2.symm
      _ ≤ ((K : ℝ) * (Real.exp r * Real.exp (-(ε * r))) + 1) * Real.exp (ε * r - r) := hmul
      _ = (K : ℝ) * (Real.exp r * Real.exp (-(ε * r)) * Real.exp (ε * r - r))
            + Real.exp (ε * r - r) := by ring
      _ = (K : ℝ) * 1 + Real.exp (-(r)) * Real.exp (ε * r) := by
            rw [hexpid, hexpid3]
            norm_num
      _ = (K : ℝ) + Real.exp (-(r)) * Real.exp (ε * r) := by ring
  have hsmall : Real.exp (-(r)) ≤ 1 / 2 := by
    have h1 : Real.exp (-(1:ℝ)) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      nlinarith [Real.exp_one_gt_d9]
    refine le_trans ?_ h1
    exact Real.exp_le_exp.mpr (by linarith)
  have hhalf : Real.exp (ε * r) / 2 ≤ (K : ℝ) := by
    nlinarith [Real.exp_pos (ε * r), hkey, hsmall]
  have hquadbig : 2 * (4 * Real.exp 1 + 4) / ε ^ (2 : ℕ) + 1 ≤ r := hrbig
  have hεr : 0 < ε * r := by positivity
  have h1 : Real.exp (ε * r) ≤ 4 * Real.exp 1 * r + 4 := by linarith [hhalf, hKle]
  have h2 : (ε * r) ^ (2 : ℕ) / 2 ≤ Real.exp (ε * r) := by nlinarith [hquad, hεr]
  have h3 : (ε * r) ^ (2 : ℕ) / 2 ≤ (4 * Real.exp 1 + 4) * r := by nlinarith [h1, h2, hr1]
  have h4 : ε ^ (2 : ℕ) * r / 2 ≤ 4 * Real.exp 1 + 4 := by nlinarith [h3, hr]
  have h5 : r ≤ 2 * (4 * Real.exp 1 + 4) / ε ^ (2 : ℕ) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [h4]
  linarith [hrbig, h5]

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

theorem norm_cexp_le_exp_norm (z : ℂ) : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr (le_trans (Complex.re_le_norm z) (le_refl _))

theorem iteratedDeriv_cexp_norm (n : ℕ) :
    ‖iteratedDeriv n Complex.exp 0 / (n.factorial : ℂ)‖ = 1 / (n.factorial : ℝ) := by
  have hiter : iteratedDeriv n Complex.exp = Complex.exp := by
    induction n with
    | zero => simp [iteratedDeriv_zero]
    | succ k ih => rw [iteratedDeriv_succ, ih, Complex.deriv_exp]
  rw [hiter, Complex.exp_zero, norm_div, norm_one]
  simp

theorem iteratedDeriv_factorialProfileHT_norm (n : ℕ) :
    ‖iteratedDeriv n factorialProfileHT 0 / (n.factorial : ℂ)‖ = 1 / (n.factorial : ℝ) := by
  have h := norm_taylorPS_factorialProfileHT n
  rwa [GaloisForLFunctions.coeff_taylorPS] at h

theorem differentiable_factorialProfileHT : Differentiable ℂ factorialProfileHT := by
  have h := contDiff_modulusProfileFunction (ρ := factorialProfile) factorialProfile_bounded
  exact h.differentiable (by simp)

theorem factorialProfileHT_eq_tsum (z : ℂ) :
    factorialProfileHT z = ∑' n : ℕ, phaseSeq_modulusPhaseSequence factorialProfile n * z ^ n := by
  rw [factorialProfileHT, modulusProfileFunction,
    FormalMultilinearSeries.ofScalars_sum_eq]
  simp [smul_eq_mul]

/-- **Card 16, Theorem 2, item 4.**  Both realizations of the factorial profile have order one and
exponential type one: each is dominated by `exp ‖z‖`, and on every large circle each exceeds
`exp ((1 − ε) r)` somewhere. -/
theorem factorialProfile_order_one_type_one :
    (∀ z : ℂ, ‖Complex.exp z‖ ≤ Real.exp ‖z‖)
      ∧ (∀ z : ℂ, ‖factorialProfileHT z‖ ≤ Real.exp ‖z‖)
      ∧ (∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in atTop, ∃ z ∈ Metric.sphere (0 : ℂ) r,
          Real.exp ((1 - ε) * r) ≤ ‖Complex.exp z‖)
      ∧ (∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in atTop, ∃ z ∈ Metric.sphere (0 : ℂ) r,
          Real.exp ((1 - ε) * r) ≤ ‖factorialProfileHT z‖) := by
  refine ⟨norm_cexp_le_exp_norm, ?_, ?_, ?_⟩
  · intro z
    refine norm_le_exp_of_factorial_moduli (c := phaseSeq_modulusPhaseSequence factorialProfile)
      factorialProfileHT_eq_tsum ?_ z
    intro n
    rw [norm_phaseSeq, factorialProfile, abs_of_pos (by positivity)]
  · intro ε hε
    exact exists_sphere_norm_ge_of_factorial_moduli Complex.differentiable_exp
      iteratedDeriv_cexp_norm hε
  · intro ε hε
    exact exists_sphere_norm_ge_of_factorial_moduli differentiable_factorialProfileHT
      iteratedDeriv_factorialProfileHT_norm hε

end

end GaloisForLFunctions.HTGeometry
