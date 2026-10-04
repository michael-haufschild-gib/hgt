import GaloisForLFunctions.RHTower.PoleVanishingWeilPrimeTwoEntry
import GaloisForLFunctions.RHTower.PoleFreePrimeTranslationResonance
import GaloisForLFunctions.RHTower.SelbergTruncatedVonMangoldtKreinCompletion
import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic
import Mathlib.NumberTheory.AbelSummation

/-!
# The free-lag scalar trace certificate fails at large aperture

At aperture `a` let `N = ⌊e^{2a}⌋` and let

`S_a(ξ) = W(ξ) - 2 Σ_{2 ≤ n ≤ N} Λ(n) n^{-1/2} (cos(2π log n ξ) - cos(4π a ξ))`

be the all-prime symbol with the free-lag correction.  On the pole-vanishing subspace the actual
restricted Weil form is `∫ S_a(ξ) |û(ξ)|² dξ`: the correction term pairs with the autocorrelation
at the full lag `2a`, which vanishes on the aperture.  Every pole-vanishing aperture vector obeys
`|f̂(ξ)|² ≤ R_a(ξ) ‖f‖²` with the optimal two-pole residual
`R_a(ξ) = 2a - C(a,ω)²/(a + sinh a) - S(a,ω)²/(sinh a - a)`, `ω = 2πξ`, and this bound is attained.
Hence `Q(u) ≥ (α - ∫ (α - S_a)₊ R_a) ‖f‖²` for every level `α`: this is the scalar trace
certificate.

**Obstruction.**  There are `κ > 0` and `a₀` such that for every `a ≥ a₀` and every `α > 0`
the certificate value is `≤ -κ e^a / a`, and the same bound holds for every valid certificate
built from a symbol deficit and a pointwise Fourier density bound.

**Mechanism.**  With `M₀, M₁, M₂` the prime moments `Σ Λ(n) n^{-1/2} (2a - log n)^k`:
Chebyshev's bound and Abel summation give `M₀ ≤ 2C e^a`, `C = log 4 + 4`; the layer-cake identity
`M₂ = 2 ∫₀^{2a} (2a - s) M₀(s/2) ds` gives `M₂ ≤ 16C (e^a - 1 - a)`; the prime number theorem gives
`M₁ ≥ e^a/4`.  Taylor's bound for the cosine then gives
`S_a(t/(4πa)) ≤ W(1) - (t sin t / a) M₁ + t² M₂/(4a²)` on the four bands
`|t| ∈ [π/6, 5π/6] ∪ [13π/6, 17π/6]`, where `t sin t ≥ π/12`.  The exact cancellation
`C² + S² = 16 (cos² sinh²(a/2) + sin² cosh²(a/2))/(1 + 4ω²)` gives `R_a ≥ 2a - 64`, so the bands
carry residual mass at least `7/6`.
-/

open MeasureTheory Set Filter Topology
open scoped FourierTransform

noncomputable section

namespace RHTower.FreeLagTrace

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## Chebyshev moments of the prime weights -/

/-- Mathlib's Chebyshev constant: `ψ(x) ≤ (log 4 + 4) x` for `x ≥ 0`. -/
def chebyshevConst : ℝ := Real.log 4 + 4

theorem chebyshevConst_pos : 0 < chebyshevConst := by
  unfold chebyshevConst
  have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  linarith

/-- The native prime cutoff `⌊e^{2a}⌋`. -/
def primeCutoff (a : ℝ) : ℕ := ⌊Real.exp (2 * a)⌋₊

/-- `M₀(a) = Σ_{2 ≤ n ≤ e^{2a}} Λ(n) n^{-1/2}`. -/
def primeMass (a : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 (primeCutoff a), Λ n / Real.sqrt n

/-- `M₂(a) = Σ_{2 ≤ n ≤ e^{2a}} Λ(n) n^{-1/2} (2a - log n)²`. -/
def primeSecondMoment (a : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 (primeCutoff a), Λ n / Real.sqrt n * (2 * a - Real.log n) ^ 2

private theorem weight_nonneg (n : ℕ) : 0 ≤ Λ n / Real.sqrt n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

theorem primeMass_nonneg (a : ℝ) : 0 ≤ primeMass a :=
  Finset.sum_nonneg fun n _ => weight_nonneg n

private theorem rpow_neg_half_eq (k : ℕ) : (k : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt k)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg k)]

/-- **Abel summation for `Λ(n)/√n`.** -/
theorem sum_vonMangoldt_div_sqrt_eq (x : ℝ) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Λ n / Real.sqrt n =
      x ^ (-(1 / 2 : ℝ)) * Chebyshev.psi x +
        (1 / 2) * ∫ t in Ioc 1 x, t ^ (-(1 / 2 : ℝ) - 1) * Chebyshev.psi t := by
  have hf_diff : ∀ t ∈ Icc (1 : ℝ) x,
      DifferentiableAt ℝ (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) t := fun t ht =>
    Real.differentiableAt_rpow_const_of_ne _ (by linarith [ht.1] : t ≠ 0)
  have hderiv : deriv (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) =
      fun t : ℝ => -(1 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ) - 1) := Real.deriv_rpow_const' _
  have hf_int : IntegrableOn (deriv fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Icc 1 x) := by
    rw [hderiv]
    refine (ContinuousOn.mul continuousOn_const ?_).integrableOn_Icc
    intro t ht
    exact (Real.continuousAt_rpow_const t _ (Or.inl (by linarith [ht.1] : t ≠ 0))).continuousWithinAt
  have habel := sum_mul_eq_sub_integral_mul₀ (fun n => Λ n) (by simp) x hf_diff hf_int
  have hL : ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, (k : ℝ) ^ (-(1 / 2 : ℝ)) * Λ k =
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Λ n / Real.sqrt n :=
    Finset.sum_congr rfl fun k _ => by rw [rpow_neg_half_eq, div_eq_mul_inv, mul_comm]
  have hI : (∫ t in Ioc 1 x, deriv (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) t *
        ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (fun n => Λ n) k) =
      -(1 / 2 : ℝ) * ∫ t in Ioc 1 x, t ^ (-(1 / 2 : ℝ) - 1) * Chebyshev.psi t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    simp only [hderiv, ← Chebyshev.psi_eq_sum_Icc]
    ring
  rw [hL, ← Chebyshev.psi_eq_sum_Icc, hI] at habel
  rw [habel]
  ring

/-- **Chebyshev in square-root form.**  `Σ_{2 ≤ n ≤ x} Λ(n)/√n ≤ 2C √x` for `x ≥ 1`. -/
theorem sum_vonMangoldt_div_sqrt_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, Λ n / Real.sqrt n ≤ 2 * chebyshevConst * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hsub : ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, Λ n / Real.sqrt n =
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Λ n / Real.sqrt n := by
    refine Finset.sum_subset (fun n hn => ?_) (fun n hn hn' => ?_)
    · rw [Finset.mem_Icc] at hn ⊢
      omega
    · rw [Finset.mem_Icc] at hn hn'
      have : n = 0 ∨ n = 1 := by omega
      rcases this with rfl | rfl <;> simp
  rw [hsub, sum_vonMangoldt_div_sqrt_eq x]
  have hpsi : ∀ t, 0 ≤ t → Chebyshev.psi t ≤ chebyshevConst * t := fun t ht =>
    Chebyshev.psi_le_const_mul_self ht
  have hfirst : x ^ (-(1 / 2 : ℝ)) * Chebyshev.psi x ≤ chebyshevConst * Real.sqrt x := by
    have hnn : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
    have e : x ^ (-(1 / 2 : ℝ)) * x = Real.sqrt x := by
      rw [← Real.rpow_add_one hx0.ne', Real.sqrt_eq_rpow]
      norm_num
    calc x ^ (-(1 / 2 : ℝ)) * Chebyshev.psi x ≤ x ^ (-(1 / 2 : ℝ)) * (chebyshevConst * x) :=
          mul_le_mul_of_nonneg_left (hpsi x hx0.le) hnn
      _ = chebyshevConst * Real.sqrt x := by rw [← e]; ring
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Icc 1 x) := fun t ht =>
    (Real.continuousAt_rpow_const t _ (Or.inl (by linarith [ht.1] : t ≠ 0))).continuousWithinAt
  have hcont' : ContinuousOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ) - 1)) (Icc 1 x) := fun t ht =>
    (Real.continuousAt_rpow_const t _ (Or.inl (by linarith [ht.1] : t ≠ 0))).continuousWithinAt
  have hint_g : IntegrableOn (fun t : ℝ => chebyshevConst * t ^ (-(1 / 2 : ℝ))) (Ioc 1 x) :=
    ((continuousOn_const.mul hcont).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hint_f : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ) - 1) * Chebyshev.psi t) (Ioc 1 x) := by
    refine Integrable.mono' (g := fun _ => chebyshevConst * x) (integrableOn_const (by simp))
      ((hcont'.aestronglyMeasurable measurableSet_Icc).mono_set Ioc_subset_Icc_self |>.mul
        Chebyshev.psi_mono.measurable.aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have h1 : t ^ (-(1 / 2 : ℝ) - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ht.1.le (by norm_num)
    have hrnn : 0 ≤ t ^ (-(1 / 2 : ℝ) - 1) := Real.rpow_nonneg ht0.le _
    have h3 : Chebyshev.psi t ≤ chebyshevConst * x :=
      (Chebyshev.psi_mono ht.2).trans (hpsi x hx0.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hrnn (Chebyshev.psi_nonneg t))]
    calc t ^ (-(1 / 2 : ℝ) - 1) * Chebyshev.psi t ≤ 1 * Chebyshev.psi t :=
          mul_le_mul_of_nonneg_right h1 (Chebyshev.psi_nonneg t)
      _ ≤ chebyshevConst * x := by rw [one_mul]; exact h3
  have hint : ∫ t in Ioc 1 x, t ^ (-(1 / 2 : ℝ) - 1) * Chebyshev.psi t ≤
      ∫ t in Ioc 1 x, chebyshevConst * t ^ (-(1 / 2 : ℝ)) := by
    refine setIntegral_mono_on hint_f hint_g measurableSet_Ioc fun t ht => ?_
    have ht0 : 0 < t := by linarith [ht.1]
    have hrnn : 0 ≤ t ^ (-(1 / 2 : ℝ) - 1) := Real.rpow_nonneg ht0.le _
    have e : t ^ (-(1 / 2 : ℝ) - 1) * t = t ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add_one ht0.ne']
      ring_nf
    calc t ^ (-(1 / 2 : ℝ) - 1) * Chebyshev.psi t ≤
          t ^ (-(1 / 2 : ℝ) - 1) * (chebyshevConst * t) :=
          mul_le_mul_of_nonneg_left (hpsi t ht0.le) hrnn
      _ = chebyshevConst * t ^ (-(1 / 2 : ℝ)) := by rw [← e]; ring
  have heval : ∫ t in Ioc 1 x, chebyshevConst * t ^ (-(1 / 2 : ℝ)) =
      chebyshevConst * (2 * Real.sqrt x - 2) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hx,
      integral_rpow (Or.inl (by norm_num)), Real.sqrt_eq_rpow, Real.one_rpow]
    congr 1
    norm_num
    ring
  have hC := chebyshevConst_pos
  nlinarith [hint, heval, hfirst]

/-- **`M₀(a) ≤ 2C e^a`** for `a ≥ 0`. -/
theorem primeMass_le {a : ℝ} (ha : 0 ≤ a) : primeMass a ≤ 2 * chebyshevConst * Real.exp a := by
  have hx : 1 ≤ Real.exp (2 * a) := Real.one_le_exp (by linarith)
  have h := sum_vonMangoldt_div_sqrt_le hx
  have hs : Real.sqrt (Real.exp (2 * a)) = Real.exp a := by
    rw [show 2 * a = a + a by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos a).le]
  rwa [hs] at h

/-- The partial prime mass `Σ_{2 ≤ n ≤ e^s} Λ(n)/√n`, i.e. `M₀(s/2)`. -/
private theorem primeMass_half (s : ℝ) :
    primeMass (s / 2) = ∑ n ∈ Finset.Icc 2 ⌊Real.exp s⌋₊, Λ n / Real.sqrt n := by
  simp only [primeMass, primeCutoff, show 2 * (s / 2) = s by ring]

private theorem log_le_of_mem_cutoff {a : ℝ} {n : ℕ} (hn : n ∈ Finset.Icc 2 (primeCutoff a)) :
    Real.log n ≤ 2 * a :=
  log_le_two_mul_of_mem hn

private theorem log_pos_of_mem {a : ℝ} {n : ℕ} (hn : n ∈ Finset.Icc 2 (primeCutoff a)) :
    0 < Real.log n := by
  rw [Finset.mem_Icc] at hn
  exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))

/-- One layer of the layer-cake identity: `(2a - log n)² = ∫₀^{2a} 2(2a - s) 1[log n ≤ s] ds`. -/
private theorem layer_integral {a L : ℝ} (hL : 0 ≤ L) (hLa : L ≤ 2 * a) :
    ∫ s in (0 : ℝ)..(2 * a), (Ici L).indicator (fun s => 2 * (2 * a - s)) s = (2 * a - L) ^ 2 := by
  have h0 : (0 : ℝ) ≤ 2 * a := hL.trans hLa
  rw [intervalIntegral.integral_of_le h0, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  have hset : (Ici L ∩ Ioc 0 (2 * a) : Set ℝ) =ᵐ[volume] (Ioc L (2 * a) : Set ℝ) := by
    rcases hL.eq_or_lt with hL0 | hL0
    · subst hL0
      have : Ici (0 : ℝ) ∩ Ioc 0 (2 * a) = Ioc 0 (2 * a) := by
        ext s; simp only [mem_inter_iff, mem_Ici, mem_Ioc]; constructor
        · rintro ⟨_, h⟩; exact h
        · rintro h; exact ⟨h.1.le, h⟩
      rw [this]
    · have : Ici L ∩ Ioc 0 (2 * a) = Icc L (2 * a) := by
        ext s; simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]; constructor
        · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, hL0.trans_le h1, h2⟩
      rw [this]
      exact Ioc_ae_eq_Icc.symm
  rw [setIntegral_congr_set hset, ← intervalIntegral.integral_of_le hLa]
  have hd : ∀ s ∈ uIcc L (2 * a), HasDerivAt (fun s => -(2 * a - s) ^ 2) (2 * (2 * a - s)) s := by
    intro s _
    have := ((hasDerivAt_id' s).const_sub (2 * a)).pow 2
    convert! this.neg using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun s : ℝ => 2 * (2 * a - s)).intervalIntegrable _ _)]
  ring

/-- **Layer-cake identity.**  `M₂(a) = 2 ∫₀^{2a} (2a - s) M₀(s/2) ds`. -/
theorem primeSecondMoment_eq_layerCake {a : ℝ} (ha : 0 ≤ a) :
    primeSecondMoment a = ∫ s in (0 : ℝ)..(2 * a), 2 * (2 * a - s) * primeMass (s / 2) := by
  have hcut : ∀ s ∈ Icc (0 : ℝ) (2 * a), 2 * (2 * a - s) * primeMass (s / 2) =
      ∑ n ∈ Finset.Icc 2 (primeCutoff a), Λ n / Real.sqrt n *
        (Ici (Real.log n)).indicator (fun s => 2 * (2 * a - s)) s := by
    intro s hs
    rw [primeMass_half, Finset.mul_sum]
    have hsub : Finset.Icc 2 ⌊Real.exp s⌋₊ ⊆ Finset.Icc 2 (primeCutoff a) := by
      apply Finset.Icc_subset_Icc le_rfl
      exact Nat.floor_le_floor (Real.exp_le_exp.mpr hs.2)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun n hn => ?_
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hle : Real.log n ≤ s := by
        have h1 : (n : ℝ) ≤ Real.exp s :=
          (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le (Real.exp_pos s).le)
        calc Real.log n ≤ Real.log (Real.exp s) := Real.log_le_log hnpos h1
          _ = s := Real.log_exp s
      rw [indicator_of_mem (show s ∈ Ici (Real.log n) from hle)]
      ring
    · intro n hn hn'
      have hnot : ¬ Real.log n ≤ s := by
        intro hle
        apply hn'
        rw [Finset.mem_Icc] at hn ⊢
        refine ⟨hn.1, Nat.le_floor ?_⟩
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hnpos).symm
          _ ≤ Real.exp s := Real.exp_le_exp.mpr hle
      rw [indicator_of_notMem (show s ∉ Ici (Real.log n) from hnot), mul_zero]
  have h0 : (0 : ℝ) ≤ 2 * a := by linarith
  have hEq : ∫ s in (0 : ℝ)..(2 * a), 2 * (2 * a - s) * primeMass (s / 2) =
      ∫ s in (0 : ℝ)..(2 * a), ∑ n ∈ Finset.Icc 2 (primeCutoff a), Λ n / Real.sqrt n *
        (Ici (Real.log n)).indicator (fun s => 2 * (2 * a - s)) s :=
    intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le h0] at hs
      exact hcut s hs
  rw [hEq, intervalIntegral.integral_finsetSum]
  · unfold primeSecondMoment
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [intervalIntegral.integral_const_mul,
      layer_integral (log_pos_of_mem hn).le (log_le_of_mem_cutoff hn)]
  · intro n _
    refine IntervalIntegrable.const_mul ?_ _
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le h0).mpr ?_
    refine ((by fun_prop : Continuous fun s : ℝ => 2 * (2 * a - s)).integrableOn_Icc
      (a := 0) (b := 2 * a)).mono_set Ioc_subset_Icc_self |>.indicator measurableSet_Ici

/-- **`M₂(a) ≤ 16C (e^a - 1 - a) ≤ 16C e^a`.** -/
theorem primeSecondMoment_le {a : ℝ} (ha : 0 ≤ a) :
    primeSecondMoment a ≤ 16 * chebyshevConst * (Real.exp a - 1 - a) := by
  have h0 : (0 : ℝ) ≤ 2 * a := by linarith
  rw [primeSecondMoment_eq_layerCake ha]
  have hmono : ∫ s in (0 : ℝ)..(2 * a), 2 * (2 * a - s) * primeMass (s / 2) ≤
      ∫ s in (0 : ℝ)..(2 * a), 4 * chebyshevConst * ((2 * a - s) * Real.exp (s / 2)) := by
    refine intervalIntegral.integral_mono_on h0 ?_ ?_ fun s hs => ?_
    · have hm : Monotone fun s : ℝ => primeMass (s / 2) := by
        intro s t hst
        simp only [primeMass_half]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => weight_nonneg n
        exact Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor (Real.exp_le_exp.mpr hst))
      exact (hm.intervalIntegrable (μ := volume) (a := 0) (b := 2 * a)).continuousOn_mul
        (by fun_prop : Continuous fun s : ℝ => 2 * (2 * a - s)).continuousOn
    · exact (by fun_prop : Continuous fun s : ℝ =>
        4 * chebyshevConst * ((2 * a - s) * Real.exp (s / 2))).intervalIntegrable _ _
    · have hs0 : 0 ≤ s / 2 := by linarith [hs.1]
      have hM := primeMass_le hs0
      have hw : 0 ≤ 2 * (2 * a - s) := by linarith [hs.2]
      calc 2 * (2 * a - s) * primeMass (s / 2) ≤
            2 * (2 * a - s) * (2 * chebyshevConst * Real.exp (s / 2)) :=
            mul_le_mul_of_nonneg_left hM hw
        _ = 4 * chebyshevConst * ((2 * a - s) * Real.exp (s / 2)) := by ring
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul]
  have hd : ∀ s ∈ uIcc 0 (2 * a), HasDerivAt
      (fun s => 2 * (2 * a - s) * Real.exp (s / 2) + 4 * Real.exp (s / 2))
      ((2 * a - s) * Real.exp (s / 2)) s := by
    intro s _
    have he : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (s / 2) * (1 / 2)) s :=
      ((hasDerivAt_id s).div_const 2).exp.congr_deriv (by simp)
    have := ((((hasDerivAt_id' s).const_sub (2 * a)).const_mul 2).mul he).add (he.const_mul 4)
    convert! this using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun s : ℝ => (2 * a - s) * Real.exp (s / 2)).intervalIntegrable _ _)]
  simp only [sub_self, mul_zero, zero_mul, zero_add, zero_div, Real.exp_zero, sub_zero,
    show 2 * a / 2 = a by ring]
  ring

/-! ## Taylor's bound for the cosine -/

/-- `cos(t - h) - cos t ≥ h sin t - h²/2`. -/
theorem cos_sub_sub_cos_ge (t h : ℝ) :
    h * Real.sin t - h ^ 2 / 2 ≤ Real.cos (t - h) - Real.cos t := by
  set φ : ℝ → ℝ := fun h => Real.cos (t - h) - Real.cos t - h * Real.sin t + h ^ 2 / 2 with hφ
  have hd : ∀ h, HasDerivAt φ (Real.sin (t - h) - Real.sin t + h) h := by
    intro h
    have h1 := (Real.hasDerivAt_cos (t - h)).comp h ((hasDerivAt_id' h).const_sub t)
    have h2 := ((hasDerivAt_id' h).mul_const (Real.sin t))
    have h3 := ((hasDerivAt_id' h).pow 2).div_const 2
    convert! ((h1.sub_const (Real.cos t)).sub h2).add h3 using 1
    ring
  have hcont : Continuous φ := continuous_iff_continuousAt.mpr fun h => (hd h).continuousAt
  have hdiff : Differentiable ℝ φ := fun h => (hd h).differentiableAt
  have hφ0 : φ 0 = 0 := by simp [hφ]
  have hlip (h : ℝ) : |Real.sin (t - h) - Real.sin t| ≤ |h| := by
    simpa [abs_neg] using Real.abs_sin_sub_sin_le (t - h) t
  have hpos : 0 ≤ φ h := by
    rcases le_total 0 h with hh | hh
    · have hm : MonotoneOn φ (Ici 0) :=
        monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont.continuousOn hdiff.differentiableOn
          fun x hx => by
            rw [interior_Ici, mem_Ioi] at hx
            rw [(hd x).deriv]
            have := (abs_le.mp (hlip x)).1
            rw [abs_of_pos hx] at this
            linarith
      simpa [hφ0] using hm self_mem_Ici (show h ∈ Ici 0 from hh) hh
    · have hm : AntitoneOn φ (Iic 0) :=
        antitoneOn_of_deriv_nonpos (convex_Iic 0) hcont.continuousOn hdiff.differentiableOn
          fun x hx => by
            rw [interior_Iic, mem_Iio] at hx
            rw [(hd x).deriv]
            have := (abs_le.mp (hlip x)).2
            rw [abs_of_neg hx] at this
            linarith
      simpa [hφ0] using hm (show h ∈ Iic 0 from hh) self_mem_Iic hh
  simp only [hφ] at hpos
  linarith

/-! ## The optimal two-pole residual -/

/-- The optimal residual `R(a,ω) = 2a - C²/(a + sinh a) - S²/(sinh a - a)`. -/
def optimalResidual (a ω : ℝ) : ℝ :=
  2 * a - poleCosCoshIntegral a ω ^ 2 / (a + Real.sinh a) -
    poleSinSinhIntegral a ω ^ 2 / (Real.sinh a - a)

theorem sinh_sub_self_pos {a : ℝ} (ha : 0 < a) : 0 < Real.sinh a - a := by
  have := Real.self_lt_sinh_iff.mpr ha
  linarith

theorem self_add_sinh_pos {a : ℝ} (ha : 0 < a) : 0 < a + Real.sinh a := by
  have := Real.sinh_pos_iff.mpr ha
  linarith

/-- The optimal residual is the closed residual at the optimal parameters. -/
theorem optimalResidual_eq_closedForm {a : ℝ} (ha : 0 < a) (ω : ℝ) :
    optimalResidual a ω = poleResidualClosedForm a ω
      (poleCosCoshIntegral a ω / (a + Real.sinh a))
      (poleSinSinhIntegral a ω / (Real.sinh a - a)) := by
  have h1 := (self_add_sinh_pos ha).ne'
  have h2 := (sinh_sub_self_pos ha).ne'
  unfold optimalResidual poleResidualClosedForm
  field_simp
  ring

/-- The optimal residual is the minimum of the closed residual over the pole parameters. -/
theorem optimalResidual_le_closedForm {a : ℝ} (ha : 0 < a) (ω p q : ℝ) :
    optimalResidual a ω ≤ poleResidualClosedForm a ω p q := by
  have h1 := self_add_sinh_pos ha
  have h2 := sinh_sub_self_pos ha
  set C := poleCosCoshIntegral a ω
  set S := poleSinSinhIntegral a ω
  have e : poleResidualClosedForm a ω p q - optimalResidual a ω =
      (a + Real.sinh a) * (p - C / (a + Real.sinh a)) ^ 2 +
        (Real.sinh a - a) * (q - S / (Real.sinh a - a)) ^ 2 := by
    unfold poleResidualClosedForm optimalResidual
    field_simp
    ring
  have : 0 ≤ poleResidualClosedForm a ω p q - optimalResidual a ω := by
    rw [e]; positivity
  linarith

/-- **Exact cancellation.**
`C² + S² = 16 (cos(aω)² sinh(a/2)² + sin(aω)² cosh(a/2)²)/(1 + 4ω²)`. -/
theorem poleCosCosh_sq_add_poleSinSinh_sq (a ω : ℝ) :
    poleCosCoshIntegral a ω ^ 2 + poleSinSinhIntegral a ω ^ 2 =
      16 * (Real.cos (ω * a) ^ 2 * Real.sinh (a / 2) ^ 2 +
        Real.sin (ω * a) ^ 2 * Real.cosh (a / 2) ^ 2) / (1 + 4 * ω ^ 2) := by
  have hd : (1 + 4 * ω ^ 2) ≠ 0 := by positivity
  unfold poleCosCoshIntegral poleSinSinhIntegral
  field_simp
  ring

/-- `C² + S² ≤ 16 e^a` for `a ≥ 0`. -/
theorem poleCosCosh_sq_add_poleSinSinh_sq_le {a : ℝ} (ha : 0 ≤ a) (ω : ℝ) :
    poleCosCoshIntegral a ω ^ 2 + poleSinSinhIntegral a ω ^ 2 ≤ 16 * Real.exp a := by
  rw [poleCosCosh_sq_add_poleSinSinh_sq]
  have hd : 1 ≤ 1 + 4 * ω ^ 2 := by nlinarith [sq_nonneg ω]
  have hsh : Real.sinh (a / 2) ^ 2 ≤ Real.cosh (a / 2) ^ 2 := by
    have := Real.cosh_sq (a / 2); nlinarith [sq_nonneg (Real.sinh (a / 2))]
  have hch : Real.cosh (a / 2) ^ 2 ≤ Real.exp a := by
    have hc : Real.cosh (a / 2) ≤ Real.exp (a / 2) := by
      rw [Real.cosh_eq]
      have : Real.exp (-(a / 2)) ≤ Real.exp (a / 2) := Real.exp_le_exp.mpr (by linarith)
      linarith
    have he : Real.exp (a / 2) ^ 2 = Real.exp a := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [← he]
    exact pow_le_pow_left₀ (Real.cosh_pos _).le hc 2
  have hnum : Real.cos (ω * a) ^ 2 * Real.sinh (a / 2) ^ 2 +
      Real.sin (ω * a) ^ 2 * Real.cosh (a / 2) ^ 2 ≤ Real.exp a := by
    have hcs := Real.cos_sq_add_sin_sq (ω * a)
    nlinarith [sq_nonneg (Real.cos (ω * a)), sq_nonneg (Real.sin (ω * a))]
  have hnn : 0 ≤ Real.cos (ω * a) ^ 2 * Real.sinh (a / 2) ^ 2 +
      Real.sin (ω * a) ^ 2 * Real.cosh (a / 2) ^ 2 := by positivity
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-! ## The free-lag all-prime symbol -/

/-- `S_a(ξ) = W(ξ) - 2 Σ_{2 ≤ n ≤ e^{2a}} Λ(n) n^{-1/2} (cos(2π log n ξ) - cos(2π (2a) ξ))`. -/
def freeLagSymbol (a ξ : ℝ) : ℝ :=
  archimedeanWeilSymbol ξ - 2 * ∑ n ∈ Finset.Icc 2 (primeCutoff a),
    Λ n / Real.sqrt n *
      (Real.cos (2 * Real.pi * Real.log n * ξ) - Real.cos (2 * Real.pi * (2 * a) * ξ))

/-- The free-lag symbol is the finite-atom symbol plus the null full-lag correction. -/
theorem freeLagSymbol_eq_weilAtomSymbol (a ξ : ℝ) :
    freeLagSymbol a ξ = weilAtomSymbol (fun n => Λ n) (primeCutoff a) ξ +
      2 * primeMass a * Real.cos (2 * Real.pi * (2 * a) * ξ) := by
  have h : 2 * ∑ n ∈ Finset.Icc 2 (primeCutoff a), Λ n / Real.sqrt n *
      (Real.cos (2 * Real.pi * Real.log n * ξ) - Real.cos (2 * Real.pi * (2 * a) * ξ)) =
      ∑ n ∈ Finset.Icc 2 (primeCutoff a), Λ n * (1 / Real.sqrt n) *
        (2 * Real.cos (2 * Real.pi * Real.log n * ξ)) -
      2 * primeMass a * Real.cos (2 * Real.pi * (2 * a) * ξ) := by
    unfold primeMass
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  unfold freeLagSymbol weilAtomSymbol
  rw [h]
  ring

/-- At apertures with the single prime `2` the free-lag symbol is the prime-two symbol: the
coefficient `2 Λ(2)/√2 = √2 log 2`. -/
theorem freeLagSymbol_eq_primeTwoShiftSymbol {a : ℝ} (h : primeCutoff a = 2) (ξ : ℝ) :
    freeLagSymbol a ξ = primeTwoShiftSymbol a ξ := by
  have hΛ : Λ 2 = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have hs : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 := by
    rw [div_eq_iff (Real.sqrt_pos.mpr (by norm_num)).ne', Real.mul_self_sqrt (by norm_num)]
  have key : ∀ X : ℝ, 2 * (Real.log 2 / Real.sqrt 2 * X) = Real.sqrt 2 * Real.log 2 * X := by
    intro X
    rw [show Real.sqrt 2 * Real.log 2 * X = 2 / Real.sqrt 2 * Real.log 2 * X by rw [hs]]
    ring
  unfold freeLagSymbol primeTwoShiftSymbol
  rw [h, Finset.Icc_self, Finset.sum_singleton, hΛ]
  simp only [Nat.cast_ofNat]
  rw [key]

private theorem integrable_weilAtomSymbol_mul (a : SuzukiPositiveAperture) (lam : ℕ → ℝ) (N : ℕ)
    (u : CCMArchimedeanFormDomain a) :
    Integrable (fun ξ : ℝ => weilAtomSymbol lam N ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) := by
  have hW : Integrable (fun ξ : ℝ => archimedeanWeilSymbol ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) := by
    simpa [archimedeanWeilSymbol] using integrable_two_gammaHardyPhaseRate_mul_norm_sq u.1
  have hC : Integrable (fun ξ : ℝ => ∑ n ∈ Finset.Icc 2 N, lam n * (1 / Real.sqrt n) *
      (2 * Real.cos (2 * Real.pi * Real.log n * ξ)) * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) := by
    refine integrable_finsetSum _ fun n _ => ?_
    refine ((integrable_cos_mul_norm_sq_ccmFormDomain a u (Real.log n)).const_mul
      (lam n * (1 / Real.sqrt n) * 2)).congr (Eventually.of_forall fun ξ => ?_)
    simp only
    ring
  refine (hW.sub hC).congr (Eventually.of_forall fun ξ => ?_)
  simp only [Pi.sub_apply, weilAtomSymbol, sub_mul, Finset.sum_mul]

theorem integrable_freeLagSymbol_mul (a : SuzukiPositiveAperture) (b : ℝ)
    (u : CCMArchimedeanFormDomain a) :
    Integrable (fun ξ : ℝ => freeLagSymbol b ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) := by
  refine ((integrable_weilAtomSymbol_mul a (fun n => Λ n) (primeCutoff b) u).add
    ((integrable_cos_mul_norm_sq_ccmFormDomain a u (2 * b)).const_mul (2 * primeMass b))).congr
    (Eventually.of_forall fun ξ => ?_)
  simp only [Pi.add_apply, freeLagSymbol_eq_weilAtomSymbol]
  ring

/-- **The free-lag symbol represents the actual form.**  On the pole-vanishing subspace the
restricted Weil form at aperture `a` is `∫ S_a(ξ) |û(ξ)|² dξ`. -/
theorem ccmRestrictedWeilSourceQuadratic_eq_integral_freeLagSymbol (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u) :
    ccmRestrictedWeilSourceQuadratic a u =
      ∫ ξ : ℝ, freeLagSymbol a.1 ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 := by
  rw [← ccmRestrictedWeilSourceQuadraticWith_eq a (fun n => Λ n) (N := primeCutoff a.1) le_rfl
      (fun _ _ _ => rfl) u,
    ccmRestrictedWeilSourceQuadraticWith_eq_integral_symbol a _ _ u hu]
  have hzero : ∫ ξ : ℝ, Real.cos (2 * Real.pi * (2 * a.1) * ξ) * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 = 0 := by
    rw [← re_inner_logTranslation_eq_integral_cos a u (2 * a.1),
      inner_logTranslationCLM_two_aperture_eq_zero, Complex.zero_re]
  have h1 := integrable_weilAtomSymbol_mul a (fun n => Λ n) (primeCutoff a.1) u
  have h2 := (integrable_cos_mul_norm_sq_ccmFormDomain a u (2 * a.1)).const_mul (2 * primeMass a.1)
  have hfun : (fun ξ : ℝ => freeLagSymbol a.1 ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) =
      fun ξ => weilAtomSymbol (fun n => Λ n) (primeCutoff a.1) ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 +
        2 * primeMass a.1 * (Real.cos (2 * Real.pi * (2 * a.1) * ξ) * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) := by
    funext ξ
    rw [freeLagSymbol_eq_weilAtomSymbol]
    ring
  rw [hfun, integral_add h1 h2, integral_const_mul, hzero, mul_zero, add_zero]

/-! ## Elementary bounds on the symbol -/

theorem continuous_archimedeanWeilSymbol : Continuous archimedeanWeilSymbol := by
  unfold archimedeanWeilSymbol
  exact continuous_const.mul (continuous_gammaHardyPhaseRate.comp (continuous_const.mul continuous_id))

theorem continuous_freeLagSymbol (a : ℝ) : Continuous (freeLagSymbol a) := by
  unfold freeLagSymbol
  refine continuous_archimedeanWeilSymbol.sub (continuous_const.mul ?_)
  exact continuous_finsetSum _ fun n _ => continuous_const.mul (by fun_prop)

/-- `S_a ≥ W - 4 M₀(a)`. -/
theorem archimedeanWeilSymbol_sub_le_freeLagSymbol (a ξ : ℝ) :
    archimedeanWeilSymbol ξ - 4 * primeMass a ≤ freeLagSymbol a ξ := by
  have h : ∑ n ∈ Finset.Icc 2 (primeCutoff a), Λ n / Real.sqrt n *
      (Real.cos (2 * Real.pi * Real.log n * ξ) - Real.cos (2 * Real.pi * (2 * a) * ξ)) ≤
      2 * primeMass a := by
    unfold primeMass
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    have h1 := Real.cos_le_one (2 * Real.pi * Real.log n * ξ)
    have h2 := Real.neg_one_le_cos (2 * Real.pi * (2 * a) * ξ)
    have hw := weight_nonneg n
    nlinarith
  unfold freeLagSymbol
  linarith

/-- The archimedean symbol diverges: it exceeds every level outside a compact interval. -/
theorem exists_archimedeanWeilSymbol_ge (B : ℝ) :
    ∃ X : ℝ, 0 ≤ X ∧ ∀ ξ : ℝ, X ≤ |ξ| → B ≤ archimedeanWeilSymbol ξ := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    (gammaHardyPhaseRate_tendsto_atTop.eventually (eventually_ge_atTop (B / 2)))
  refine ⟨max T 0 / (2 * Real.pi), by positivity, fun ξ hξ => ?_⟩
  have hX : archimedeanWeilSymbol (max T 0 / (2 * Real.pi)) = 2 * gammaHardyPhaseRate (max T 0) := by
    unfold archimedeanWeilSymbol
    rw [mul_div_cancel₀ _ (by positivity)]
  have h1 := hT (max T 0) (le_max_left _ _)
  have hmono := archimedeanWeilSymbol_mono (ξ := max T 0 / (2 * Real.pi)) (ζ := ξ)
    (by rw [abs_of_nonneg (by positivity)]; exact hξ)
  linarith

theorem optimalResidual_nonneg {a : ℝ} (ha : 0 < a) (ω : ℝ) : 0 ≤ optimalResidual a ω := by
  rw [optimalResidual_eq_closedForm ha, ← integral_poleResidual_eq_closedForm]
  exact intervalIntegral.integral_nonneg (by linarith) fun x _ => by positivity

theorem continuous_optimalResidual (a : ℝ) : Continuous (optimalResidual a) := by
  unfold optimalResidual poleCosCoshIntegral poleSinSinhIntegral
  fun_prop (disch := (intros; positivity))

/-- **The Fourier density bound.**  Every pole-vanishing aperture vector satisfies
`|f̂(ξ)|² ≤ R_a(2πξ) ‖f‖²`. -/
theorem norm_fourier_sq_le_optimalResidual (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a)
    (hplus : inner ℂ (ccmPolarL2Vector a (1 / 2)) f.1 = 0)
    (hminus : inner ℂ (ccmPolarL2Vector a (-1 / 2)) f.1 = 0) (ξ : ℝ) :
    ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ^ 2 ≤ optimalResidual a.1 (2 * Real.pi * ξ) * ‖f‖ ^ 2 := by
  have h := norm_fourier_le_poleResidual a f hplus hminus ξ
    (poleCosCoshIntegral a.1 (2 * Real.pi * ξ) / (a.1 + Real.sinh a.1))
    (poleSinSinhIntegral a.1 (2 * Real.pi * ξ) / (Real.sinh a.1 - a.1))
  rw [optimalResidual_eq_closedForm a.2, ← norm_sq_poleResidualL2_eq_closedForm, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-! ## The scalar trace certificate -/

/-- The trace defect `∫ (α - S_a)₊ R_a`. -/
def traceDefect (a α : ℝ) : ℝ :=
  ∫ ξ : ℝ, max (α - freeLagSymbol a ξ) 0 * optimalResidual a (2 * Real.pi * ξ)

/-- The scalar trace certificate `α - ∫ (α - S_a)₊ R_a` at level `α`. -/
def traceCertificate (a α : ℝ) : ℝ := α - traceDefect a α

/-- The defect density is integrable: it vanishes once `W ≥ α + 4M₀`. -/
theorem integrable_traceDefect (a α : ℝ) :
    Integrable (fun ξ : ℝ => max (α - freeLagSymbol a ξ) 0 * optimalResidual a (2 * Real.pi * ξ)) := by
  obtain ⟨X, -, hX⟩ := exists_archimedeanWeilSymbol_ge (α + 4 * primeMass a)
  have hcont : Continuous (fun ξ : ℝ =>
      max (α - freeLagSymbol a ξ) 0 * optimalResidual a (2 * Real.pi * ξ)) :=
    ((continuous_const.sub (continuous_freeLagSymbol a)).max continuous_const).mul
      ((continuous_optimalResidual a).comp (continuous_const.mul continuous_id))
  have heq : (fun ξ : ℝ => max (α - freeLagSymbol a ξ) 0 * optimalResidual a (2 * Real.pi * ξ)) =
      (Icc (-X) X).indicator
        (fun ξ : ℝ => max (α - freeLagSymbol a ξ) 0 * optimalResidual a (2 * Real.pi * ξ)) := by
    funext ξ
    by_cases hξ : ξ ∈ Icc (-X) X
    · rw [indicator_of_mem hξ]
    · rw [indicator_of_notMem hξ]
      have hbig : X ≤ |ξ| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hξ
        rcases hξ with h | h
        · exact le_abs.mpr (Or.inr (by linarith))
        · exact le_abs.mpr (Or.inl h.le)
      have := hX ξ hbig
      have := archimedeanWeilSymbol_sub_le_freeLagSymbol a ξ
      rw [max_eq_right (by linarith), zero_mul]
  rw [heq]
  exact (hcont.integrableOn_Icc).integrable_indicator measurableSet_Icc

theorem traceDefect_nonneg {a : ℝ} (ha : 0 < a) (α : ℝ) : 0 ≤ traceDefect a α :=
  integral_nonneg fun _ => mul_nonneg (le_max_right _ _) (optimalResidual_nonneg ha _)

/-- **Validity of the certificate.**  For every level `α` and every pole-vanishing form-domain
vector, `Q(u) ≥ (α - ∫ (α - S_a)₊ R_a) ‖f‖²`. -/
theorem traceCertificate_mul_le (a : SuzukiPositiveAperture) (α : ℝ)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u) :
    traceCertificate a.1 α * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u := by
  set f := ccmArchimedeanFormToAperture a u with hfdef
  have hplus : inner ℂ (ccmPolarL2Vector a (1 / 2)) f.1 = 0 := hu.1
  have hminus : inner ℂ (ccmPolarL2Vector a (-1 / 2)) f.1 = 0 := hu.2
  set φ : ℝ → ℝ := fun ξ => ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 with hφ
  set m : ℝ → ℝ := fun ξ => max (α - freeLagSymbol a.1 ξ) 0 with hm
  set R : ℝ → ℝ := fun ξ => optimalResidual a.1 (2 * Real.pi * ξ) with hR
  have hφint : Integrable φ := integrable_norm_sq_ccmFormDomain a u
  have hφnn : ∀ ξ, 0 ≤ φ ξ := fun ξ => by positivity
  have hm_cont : Continuous m :=
    (continuous_const.sub (continuous_freeLagSymbol a.1)).max continuous_const
  have hm_bdd : ∀ ξ, ‖m ξ‖ ≤ max (α - (archimedeanWeilSymbol 0 - 4 * primeMass a.1)) 0 := by
    intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    refine max_le_max ?_ le_rfl
    have h0 := archimedeanWeilSymbol_mono (ξ := 0) (ζ := ξ) (by simp)
    have := archimedeanWeilSymbol_sub_le_freeLagSymbol a.1 ξ
    linarith
  have hmφ : Integrable (fun ξ => m ξ * φ ξ) :=
    hφint.bdd_mul hm_cont.aestronglyMeasurable (Eventually.of_forall hm_bdd)
  have hSφ : Integrable (fun ξ => freeLagSymbol a.1 ξ * φ ξ) := integrable_freeLagSymbol_mul a a.1 u
  have hmR : Integrable (fun ξ => m ξ * R ξ) := integrable_traceDefect a.1 α
  -- the symbol dominates `α - m`
  have hstep1 : ∫ ξ, (α * φ ξ - m ξ * φ ξ) ≤ ∫ ξ, freeLagSymbol a.1 ξ * φ ξ := by
    refine integral_mono ((hφint.const_mul α).sub hmφ) hSφ fun ξ => ?_
    have : α - m ξ ≤ freeLagSymbol a.1 ξ := by
      simp only [hm]
      have := le_max_left (α - freeLagSymbol a.1 ξ) 0
      linarith
    have := mul_le_mul_of_nonneg_right this (hφnn ξ)
    simp only
    linarith
  -- the density bound
  have hstep2 : ∫ ξ, m ξ * φ ξ ≤ ∫ ξ, m ξ * R ξ * ‖f‖ ^ 2 := by
    refine integral_mono_ae hmφ (hmR.mul_const _) ?_
    filter_upwards [ccmFormDomain_ae_eq_fourier a u] with ξ hξ
    have hb := norm_fourier_sq_le_optimalResidual a f hplus hminus ξ
    have hφξ : φ ξ = ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ^ 2 := by simp only [hφ, hξ, hfdef]
    rw [mul_assoc, hφξ]
    exact mul_le_mul_of_nonneg_left hb (le_max_right _ _)
  have hnorm : ∫ ξ, φ ξ = ‖f‖ ^ 2 := integral_norm_sq_ccmFormDomain a u
  rw [ccmRestrictedWeilSourceQuadratic_eq_integral_freeLagSymbol a u hu]
  rw [integral_sub (hφint.const_mul α) hmφ, integral_const_mul, hnorm] at hstep1
  rw [integral_mul_const] at hstep2
  unfold traceCertificate traceDefect
  change (α - ∫ ξ, m ξ * R ξ) * ‖f‖ ^ 2 ≤ _
  nlinarith [hstep1, hstep2]

/-! ## The negative bands -/

/-- The four observation bands `|t| ∈ [π/6, 5π/6] ∪ [13π/6, 17π/6]`. -/
def IsNegativeBand (t : ℝ) : Prop :=
  (Real.pi / 6 ≤ |t| ∧ |t| ≤ 5 * Real.pi / 6) ∨ (13 * Real.pi / 6 ≤ |t| ∧ |t| ≤ 17 * Real.pi / 6)

private theorem half_le_sin {t : ℝ} (h1 : Real.pi / 6 ≤ t) (h2 : t ≤ 5 * Real.pi / 6) :
    1 / 2 ≤ Real.sin t := by
  have hpi := Real.pi_pos
  rcases le_total t (Real.pi / 2) with h | h
  · rw [← Real.sin_pi_div_six]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h h1
  · rw [← Real.sin_pi_sub, ← Real.sin_pi_div_six]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

/-- On the bands `t sin t ≥ π/12` and `|t| ≤ 17π/6`. -/
theorem isNegativeBand_mul_sin {t : ℝ} (ht : IsNegativeBand t) :
    Real.pi / 12 ≤ t * Real.sin t ∧ |t| ≤ 17 * Real.pi / 6 := by
  have hpi := Real.pi_pos
  have heven : t * Real.sin t = |t| * Real.sin |t| := by
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, Real.sin_neg]; ring
  rw [heven]
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨?_, by linarith⟩
    have hs := half_le_sin h1 h2
    nlinarith
  · refine ⟨?_, h2⟩
    have hs : 1 / 2 ≤ Real.sin |t| := by
      have := half_le_sin (t := |t| - 2 * Real.pi) (by linarith) (by linarith)
      rwa [Real.sin_sub_two_pi] at this
    nlinarith

/-- **Taylor bound for the symbol.**
`S_a(ξ) ≤ W(ξ) - 4πξ sin(4πaξ) M₁(a) + 4π²ξ² M₂(a)`. -/
theorem freeLagSymbol_le_taylor (a ξ : ℝ) :
    freeLagSymbol a ξ ≤ archimedeanWeilSymbol ξ -
      4 * Real.pi * ξ * Real.sin (2 * Real.pi * (2 * a) * ξ) * primeHinge a +
        4 * Real.pi ^ 2 * ξ ^ 2 * primeSecondMoment a := by
  set t := 2 * Real.pi * (2 * a) * ξ
  have hterm : ∀ n ∈ Finset.Icc 2 (primeCutoff a),
      Λ n / Real.sqrt n * ((2 * Real.pi * (2 * a - Real.log n) * ξ) * Real.sin t -
        (2 * Real.pi * (2 * a - Real.log n) * ξ) ^ 2 / 2) ≤
      Λ n / Real.sqrt n *
        (Real.cos (2 * Real.pi * Real.log n * ξ) - Real.cos t) := by
    intro n _
    refine mul_le_mul_of_nonneg_left ?_ (weight_nonneg n)
    have h := cos_sub_sub_cos_ge t (2 * Real.pi * (2 * a - Real.log n) * ξ)
    have he : t - 2 * Real.pi * (2 * a - Real.log n) * ξ = 2 * Real.pi * Real.log n * ξ := by
      simp only [t]; ring
    rwa [he] at h
  have hsum := Finset.sum_le_sum hterm
  have hrw : ∑ n ∈ Finset.Icc 2 (primeCutoff a), Λ n / Real.sqrt n *
      ((2 * Real.pi * (2 * a - Real.log n) * ξ) * Real.sin t -
        (2 * Real.pi * (2 * a - Real.log n) * ξ) ^ 2 / 2) =
      2 * Real.pi * ξ * Real.sin t * primeHinge a - 2 * Real.pi ^ 2 * ξ ^ 2 * primeSecondMoment a := by
    unfold primeHinge primeSecondMoment primeCutoff
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hrw] at hsum
  unfold freeLagSymbol
  linarith

/-- **The symbol is uniformly negative of order `e^a/a` on the bands.**  There is `a₁ ≥ 1`
with `S_a(ξ) ≤ -(π/96) e^a/a` whenever `a ≥ a₁` and `4πaξ` lies in a band. -/
theorem exists_freeLagSymbol_le_on_band :
    ∃ a₁ : ℝ, 1 ≤ a₁ ∧ ∀ a, a₁ ≤ a → ∀ ξ, IsNegativeBand (4 * Real.pi * a * ξ) →
      freeLagSymbol a ξ ≤ -(Real.pi / 96) * (Real.exp a / a) := by
  obtain ⟨A₀, hA₀⟩ := exists_primeHinge_ge
  have hpi := Real.pi_pos
  have hC := chebyshevConst_pos
  set W1 := archimedeanWeilSymbol 1
  have hev : ∀ᶠ a : ℝ in atTop, W1 + 324 * chebyshevConst * (Real.exp a / a) / a ≤
      Real.pi / 96 * (Real.exp a / a) := by
    have hlim : Tendsto (fun a : ℝ => Real.exp a / a) atTop atTop := by
      simpa using Real.tendsto_exp_div_pow_atTop 1
    filter_upwards [hlim.eventually_ge_atTop (192 * |W1| / Real.pi),
      eventually_ge_atTop (324 * 192 * chebyshevConst / Real.pi), eventually_gt_atTop (0 : ℝ)]
      with a h1 h2 h3
    have hE : 0 ≤ Real.exp a / a := (div_pos (Real.exp_pos a) h3).le
    have h1' : 192 * |W1| ≤ (Real.exp a / a) * Real.pi := (div_le_iff₀ hpi).mp h1
    have h2' : 324 * 192 * chebyshevConst ≤ a * Real.pi := (div_le_iff₀ hpi).mp h2
    have hW : W1 ≤ Real.pi / 192 * (Real.exp a / a) := by linarith [le_abs_self W1]
    have hq : 324 * chebyshevConst * (Real.exp a / a) / a ≤ Real.pi / 192 * (Real.exp a / a) := by
      rw [div_le_iff₀ h3]
      nlinarith [mul_le_mul_of_nonneg_right h2' hE]
    linarith
  obtain ⟨a₂, ha₂⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max (max a₂ A₀) 1, le_max_right _ _, fun a ha ξ hξ => ?_⟩
  have ha1 : 1 ≤ a := (le_max_right _ _).trans ha
  have ha0 : 0 < a := by linarith
  have hM1 := hA₀ a ((le_max_right _ _).trans ((le_max_left _ _).trans ha))
  have hM2 := primeSecondMoment_le ha0.le
  have hbound := ha₂ a ((le_max_left _ _).trans ((le_max_left _ _).trans ha))
  obtain ⟨hts, htT⟩ := isNegativeBand_mul_sin hξ
  set t := 4 * Real.pi * a * ξ with htdef
  have hξt : ξ = t / (4 * Real.pi * a) := by rw [htdef]; field_simp
  have hξ1 : |ξ| ≤ 1 := by
    rw [hξt, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi * a), div_le_one (by positivity)]
    nlinarith
  have hW : archimedeanWeilSymbol ξ ≤ W1 := archimedeanWeilSymbol_mono (by simpa using hξ1)
  have htaylor := freeLagSymbol_le_taylor a ξ
  have harg : 2 * Real.pi * (2 * a) * ξ = t := by rw [htdef]; ring
  rw [harg] at htaylor
  have hlin : 4 * Real.pi * ξ * Real.sin t * primeHinge a = t * Real.sin t / a * primeHinge a := by
    rw [hξt]; field_simp
  have hquad : 4 * Real.pi ^ 2 * ξ ^ 2 * primeSecondMoment a =
      t ^ 2 / (4 * a ^ 2) * primeSecondMoment a := by
    rw [hξt]; field_simp
  rw [hlin, hquad] at htaylor
  have hE : 0 < Real.exp a := Real.exp_pos a
  -- the linear term
  have hL : Real.pi / 48 * (Real.exp a / a) ≤ t * Real.sin t / a * primeHinge a := by
    have h1 : Real.pi / 12 / a ≤ t * Real.sin t / a := div_le_div_of_nonneg_right hts ha0.le
    have h2 : 0 ≤ Real.pi / 12 / a := by positivity
    calc Real.pi / 48 * (Real.exp a / a) = Real.pi / 12 / a * (Real.exp a / 4) := by ring
      _ ≤ t * Real.sin t / a * primeHinge a := mul_le_mul h1 hM1 (by positivity) (h2.trans h1)
  -- the quadratic term
  have hQ : t ^ 2 / (4 * a ^ 2) * primeSecondMoment a ≤
      324 * chebyshevConst * (Real.exp a / a) / a := by
    have ht2 : t ^ 2 ≤ 81 := by
      have hpi' := Real.pi_lt_d2
      have : |t| ≤ 9 := by linarith
      nlinarith [abs_nonneg t, sq_abs t]
    have hM2' : primeSecondMoment a ≤ 16 * chebyshevConst * Real.exp a := by
      have : Real.exp a - 1 - a ≤ Real.exp a := by linarith
      nlinarith
    have hM2nn : 0 ≤ primeSecondMoment a := by
      unfold primeSecondMoment
      exact Finset.sum_nonneg fun n _ => mul_nonneg (weight_nonneg n) (sq_nonneg _)
    have hfac : 0 ≤ t ^ 2 / (4 * a ^ 2) := by positivity
    calc t ^ 2 / (4 * a ^ 2) * primeSecondMoment a ≤ 81 / (4 * a ^ 2) * (16 * chebyshevConst * Real.exp a) :=
          mul_le_mul (div_le_div_of_nonneg_right ht2 (by positivity)) hM2' hM2nn (by positivity)
      _ = 324 * chebyshevConst * (Real.exp a / a) / a := by field_simp; ring
  linarith

/-- The residual is `≥ 2a - 64` at every frequency once `a ≥ 7`. -/
theorem optimalResidual_ge {a : ℝ} (ha : 7 ≤ a) (ω : ℝ) : 2 * a - 64 ≤ optimalResidual a ω := by
  have ha0 : 0 < a := by linarith
  have hs := sinh_sub_self_pos ha0
  have hq := Real.quadratic_le_exp_of_nonneg ha0.le
  have hexp : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hsinh : Real.exp a / 4 ≤ Real.sinh a - a := by
    rw [Real.sinh_eq]; nlinarith
  have hCS := poleCosCosh_sq_add_poleSinSinh_sq_le ha0.le ω
  set C := poleCosCoshIntegral a ω
  set S := poleSinSinhIntegral a ω
  have h1 : C ^ 2 / (a + Real.sinh a) ≤ C ^ 2 / (Real.sinh a - a) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hs (by linarith)
  have h2 : (C ^ 2 + S ^ 2) / (Real.sinh a - a) ≤ 64 := by
    rw [div_le_iff₀ hs]; nlinarith [Real.exp_pos a]
  have h3 : C ^ 2 / (Real.sinh a - a) + S ^ 2 / (Real.sinh a - a) = (C ^ 2 + S ^ 2) / (Real.sinh a - a) := by
    rw [add_div]
  unfold optimalResidual
  linarith

/-- The four `ξ`-bands at aperture `a`, as intervals. -/
private theorem band_intervals {a ξ : ℝ} (ha : 0 < a)
    (hξ : ξ ∈ Icc (-(17 / (24 * a))) (-(13 / (24 * a))) ∪ Icc (-(5 / (24 * a))) (-(1 / (24 * a))) ∪
      Icc (1 / (24 * a)) (5 / (24 * a)) ∪ Icc (13 / (24 * a)) (17 / (24 * a))) :
    IsNegativeBand (4 * Real.pi * a * ξ) := by
  have hpi := Real.pi_pos
  have key : ∀ c : ℝ, 4 * Real.pi * a * (c / (24 * a)) = c * Real.pi / 6 := fun c => by
    field_simp; ring
  simp only [mem_union, mem_Icc] at hξ
  unfold IsNegativeBand
  rcases hξ with ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · have l := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 * Real.pi * a)
    have r := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * Real.pi * a)
    rw [mul_neg, key] at l r
    right
    rw [abs_of_neg (by linarith)]
    constructor <;> linarith
  · have l := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 * Real.pi * a)
    have r := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * Real.pi * a)
    rw [mul_neg, key] at l r
    left
    rw [abs_of_neg (by linarith)]
    constructor <;> linarith
  · have l := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 * Real.pi * a)
    have r := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * Real.pi * a)
    rw [key] at l r
    left
    rw [abs_of_pos (by linarith)]
    constructor <;> linarith
  · have l := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 * Real.pi * a)
    have r := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * Real.pi * a)
    rw [key] at l r
    right
    rw [abs_of_pos (by linarith)]
    constructor <;> linarith

/-- **Band mass.**  A nonnegative integrable density that is `≥ (α + K)(2a - 64)` on the bands
forces `α - ∫ F ≤ -K` once `a ≥ 256`: the four bands have `ξ`-length `2/(3a)` and the residual
mass on them is at least `7/6`. -/
theorem sub_integral_le_of_band {a α K : ℝ} (ha : 256 ≤ a) (hα : 0 < α) (hK : 0 ≤ K)
    {F : ℝ → ℝ} (hF : Integrable F) (hF0 : ∀ ξ, 0 ≤ F ξ)
    (hband : ∀ ξ, IsNegativeBand (4 * Real.pi * a * ξ) → (α + K) * (2 * a - 64) ≤ F ξ) :
    α - ∫ ξ, F ξ ≤ -K := by
  have ha0 : 0 < a := by linarith
  set c := (α + K) * (2 * a - 64) with hc
  have hc0 : 0 ≤ c := by rw [hc]; nlinarith
  set J₁ := Icc (-(17 / (24 * a))) (-(13 / (24 * a)))
  set J₂ := Icc (-(5 / (24 * a))) (-(1 / (24 * a)))
  set J₃ := Icc (1 / (24 * a)) (5 / (24 * a))
  set J₄ := Icc (13 / (24 * a)) (17 / (24 * a))
  have hinv : ∀ p q : ℝ, p < q → p / (24 * a) < q / (24 * a) := fun p q h =>
    div_lt_div_of_pos_right h (by positivity)
  have hd12 : Disjoint J₁ J₂ := by
    refine Set.disjoint_left.mpr fun x hx1 hx2 => ?_
    have := hinv 5 13 (by norm_num)
    linarith [hx1.2, hx2.1]
  have hd123 : Disjoint (J₁ ∪ J₂) J₃ := by
    refine Set.disjoint_left.mpr fun x hx hx3 => ?_
    have := hinv 1 1 |> fun _ => (by positivity : (0 : ℝ) < 1 / (24 * a))
    rcases hx with hx | hx
    · have := hinv 13 17 (by norm_num); linarith [hx.2, hx3.1, (by positivity : (0 : ℝ) < 13 / (24 * a))]
    · linarith [hx.2, hx3.1, (by positivity : (0 : ℝ) < 1 / (24 * a))]
  have hd1234 : Disjoint (J₁ ∪ J₂ ∪ J₃) J₄ := by
    refine Set.disjoint_left.mpr fun x hx hx4 => ?_
    have h513 := hinv 5 13 (by norm_num)
    rcases hx with (hx | hx) | hx
    · linarith [hx.2, hx4.1, (by positivity : (0 : ℝ) < 13 / (24 * a))]
    · linarith [hx.2, hx4.1, (by positivity : (0 : ℝ) < 1 / (24 * a)),
        (by positivity : (0 : ℝ) < 13 / (24 * a))]
    · linarith [hx.2, hx4.1]
  have hJ : ∀ J : Set ℝ, J ⊆ J₁ ∪ J₂ ∪ J₃ ∪ J₄ → ∀ p q : ℝ, J = Icc p q → p ≤ q →
      c * (q - p) ≤ ∫ ξ in J, F ξ := by
    intro J hJsub p q hJ hpq
    have hconst : ∫ ξ in J, c = c * (q - p) := by
      rw [setIntegral_const, hJ, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_comm]
    rw [← hconst]
    refine setIntegral_mono_on (integrableOn_const (by rw [hJ, Real.volume_Icc]; simp))
      hF.integrableOn (by rw [hJ]; exact measurableSet_Icc) fun ξ hξ => ?_
    exact hband ξ (band_intervals ha0 (hJsub hξ))
  have hsub1 : J₁ ⊆ J₁ ∪ J₂ ∪ J₃ ∪ J₄ := fun x hx => Or.inl (Or.inl (Or.inl hx))
  have hsub2 : J₂ ⊆ J₁ ∪ J₂ ∪ J₃ ∪ J₄ := fun x hx => Or.inl (Or.inl (Or.inr hx))
  have hsub3 : J₃ ⊆ J₁ ∪ J₂ ∪ J₃ ∪ J₄ := fun x hx => Or.inl (Or.inr hx)
  have hsub4 : J₄ ⊆ J₁ ∪ J₂ ∪ J₃ ∪ J₄ := fun x hx => Or.inr hx
  have hle : ∀ p q : ℝ, p < q → p / (24 * a) ≤ q / (24 * a) := fun p q h => (hinv p q h).le
  have i1 := hJ J₁ hsub1 _ _ rfl (by have := hle 13 17 (by norm_num); linarith)
  have i2 := hJ J₂ hsub2 _ _ rfl (by have := hle 1 5 (by norm_num); linarith)
  have i3 := hJ J₃ hsub3 _ _ rfl (hle 1 5 (by norm_num))
  have i4 := hJ J₄ hsub4 _ _ rfl (hle 13 17 (by norm_num))
  have hunion : ∫ ξ in J₁ ∪ J₂ ∪ J₃ ∪ J₄, F ξ =
      (∫ ξ in J₁, F ξ) + (∫ ξ in J₂, F ξ) + (∫ ξ in J₃, F ξ) + ∫ ξ in J₄, F ξ := by
    rw [setIntegral_union hd1234 measurableSet_Icc hF.integrableOn hF.integrableOn,
      setIntegral_union hd123 measurableSet_Icc hF.integrableOn hF.integrableOn,
      setIntegral_union hd12 measurableSet_Icc hF.integrableOn hF.integrableOn]
  have htot : ∫ ξ in J₁ ∪ J₂ ∪ J₃ ∪ J₄, F ξ ≤ ∫ ξ, F ξ :=
    setIntegral_le_integral hF (Eventually.of_forall hF0)
  have hlen : c * (4 / (6 * a)) =
      c * (-(13 / (24 * a)) - -(17 / (24 * a))) + c * (-(1 / (24 * a)) - -(5 / (24 * a))) +
        c * (5 / (24 * a) - 1 / (24 * a)) + c * (17 / (24 * a) - 13 / (24 * a)) := by
    field_simp; ring
  have hmass : 7 / 6 * (α + K) ≤ c * (4 / (6 * a)) := by
    rw [hc, show (α + K) * (2 * a - 64) * (4 / (6 * a)) = (α + K) * ((2 * a - 64) * 4 / (6 * a)) by ring]
    have : 7 / 6 ≤ (2 * a - 64) * 4 / (6 * a) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    nlinarith
  linarith

/-! ## The obstruction -/

/-- **The free-lag scalar trace certificate fails at large aperture.**  There are `κ > 0` and
`a₀ > 0` such that for every aperture `a ≥ a₀` and every positive level `α`,
`α - ∫ (α - S_a)₊ R_a ≤ -κ e^a / a`. -/
theorem exists_traceCertificate_le :
    ∃ κ : ℝ, 0 < κ ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a, a₀ ≤ a → ∀ α, 0 < α →
      traceCertificate a α ≤ -κ * (Real.exp a / a) := by
  obtain ⟨a₁, -, hband⟩ := exists_freeLagSymbol_le_on_band
  refine ⟨Real.pi / 96, by positivity, max a₁ 256, by positivity, fun a ha α hα => ?_⟩
  have ha256 : 256 ≤ a := (le_max_right _ _).trans ha
  have ha0 : 0 < a := by linarith
  have hK : 0 ≤ Real.pi / 96 * (Real.exp a / a) := by positivity
  have h := sub_integral_le_of_band ha256 hα hK (integrable_traceDefect a α)
    (fun ξ => mul_nonneg (le_max_right _ _) (optimalResidual_nonneg ha0 _)) (fun ξ hξ => by
      have hS := hband a ((le_max_left _ _).trans ha) ξ hξ
      have hR := optimalResidual_ge (by linarith : (7 : ℝ) ≤ a) (2 * Real.pi * ξ)
      have hm : α + Real.pi / 96 * (Real.exp a / a) ≤ max (α - freeLagSymbol a ξ) 0 :=
        le_trans (by linarith) (le_max_left _ _)
      exact mul_le_mul hm hR (by linarith) (le_max_right _ _))
  unfold traceCertificate traceDefect
  linarith

/-- In particular the certificate is strictly negative at every large aperture and level. -/
theorem traceCertificate_neg_eventually :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a, a₀ ≤ a → ∀ α, 0 < α → traceCertificate a α < 0 := by
  obtain ⟨κ, hκ, a₀, ha₀, h⟩ := exists_traceCertificate_le
  refine ⟨a₀, ha₀, fun a ha α hα => (h a ha α hα).trans_lt ?_⟩
  have : 0 < Real.exp a / a := div_pos (Real.exp_pos a) (ha₀.trans_le ha)
  nlinarith

/-! ## Sharpness of the residual bound -/

theorem indicatorCutoff_planeWaveL2 (a : SuzukiPositiveAperture) (ξ : ℝ) :
    indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1) (planeWaveL2 a ξ) =
      planeWaveL2 a ξ := by
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1)
      (planeWaveL2 a ξ), planeWaveL2_coeFn a ξ] with x hcut hvec
  rw [hcut]
  by_cases hx : x ∈ centralInterval a.1
  · simp [hx]
  · rw [Set.indicator_of_notMem hx, hvec, Set.indicator_of_notMem hx]

/-- The aperture plane wave as a vector of the aperture space. -/
def planeWaveApertureVector (a : SuzukiPositiveAperture) (ξ : ℝ) : suzukiApertureHilbert a :=
  ⟨planeWaveL2 a ξ, by
    rw [suzukiApertureHilbert, physicalForbidden, LinearMap.mem_range]
    exact ⟨planeWaveL2 a ξ, indicatorCutoff_planeWaveL2 a ξ⟩⟩

/-- `⟨e^{s x}, e_ξ⟩` on the aperture is `∫_{-a}^{a} exp((s + 2πiξ) x) dx`. -/
theorem inner_ccmPolarL2Vector_planeWaveL2 (a : SuzukiPositiveAperture) (s ξ : ℝ) :
    inner ℂ (ccmPolarL2Vector a s) (planeWaveL2 a ξ) =
      ∫ x in (-a.1)..a.1, Complex.exp (((s : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * x) := by
  rw [MeasureTheory.L2.inner_def]
  have hae : (fun x : ℝ => inner ℂ ((ccmPolarL2Vector a s : ℝ → ℂ) x) ((planeWaveL2 a ξ : ℝ → ℂ) x))
      =ᵐ[volume] (centralInterval a.1).indicator (fun x : ℝ =>
        Complex.exp (((s : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * x)) := by
    filter_upwards [ccmPolarL2Vector_coeFn a s, planeWaveL2_coeFn a ξ] with x h1 h2
    rw [h1, h2]
    by_cases hx : x ∈ centralInterval a.1
    · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx, RCLike.inner_apply]
      unfold ccmPolarProfile planeWaveProfile
      rw [Complex.conj_ofReal, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx, inner_zero_left]
  rw [integral_congr_ae hae, integral_indicator (measurableSet_centralInterval a.1), centralInterval,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [a.property])]

/-- `⟨e^{± x/2}, e_ξ⟩ = C ± i S`. -/
theorem inner_ccmPolarL2Vector_planeWaveL2_eq {a : SuzukiPositiveAperture} {s : ℝ}
    (hs : s = 1 / 2 ∨ s = -1 / 2) (ξ : ℝ) :
    inner ℂ (ccmPolarL2Vector a s) (planeWaveL2 a ξ) =
      ((poleCosCoshIntegral a.1 (2 * Real.pi * ξ) : ℝ) : ℂ) +
        ((2 * s * poleSinSinhIntegral a.1 (2 * Real.pi * ξ) : ℝ) : ℂ) * Complex.I := by
  set ω := 2 * Real.pi * ξ
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hz : (s : ℂ) + (ω : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hs0 this
  have hd : (1 + 4 * ω ^ 2) ≠ 0 := by positivity
  rw [inner_ccmPolarL2Vector_planeWaveL2, integral_exp_mul_complex hz, eq_comm, eq_div_iff hz]
  set A := a.1
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.sub_re, Complex.exp_re, Complex.add_im, Complex.mul_im]
    simp only [mul_zero, sub_zero, add_zero, mul_one, zero_add, Real.cos_neg, mul_neg]
    unfold poleCosCoshIntegral poleSinSinhIntegral
    rw [Real.sinh_eq, Real.cosh_eq]
    rcases hs with rfl | rfl
    · have e1 : (1 / 2 : ℝ) * A = A / 2 := by ring
      simp only [e1]
      field_simp
      ring
    · have e1 : (-1 / 2 : ℝ) * A = -(A / 2) := by ring
      simp only [e1, neg_neg]
      field_simp
      ring
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.sub_im, Complex.exp_im, Complex.add_im, Complex.mul_im]
    simp only [mul_zero, sub_zero, add_zero, mul_one, zero_add, Real.sin_neg, mul_neg]
    unfold poleCosCoshIntegral poleSinSinhIntegral
    rw [Real.sinh_eq, Real.cosh_eq]
    rcases hs with rfl | rfl
    · have e1 : (1 / 2 : ℝ) * A = A / 2 := by ring
      simp only [e1]
      field_simp
      ring
    · have e1 : (-1 / 2 : ℝ) * A = -(A / 2) := by ring
      simp only [e1, neg_neg]
      field_simp
      ring

/-- The optimal pole parameters `p* = C/(a + sinh a)`, `q* = S/(sinh a - a)`. -/
def optimalCosParameter (a ω : ℝ) : ℝ := poleCosCoshIntegral a ω / (a + Real.sinh a)

def optimalSinParameter (a ω : ℝ) : ℝ := poleSinSinhIntegral a ω / (Real.sinh a - a)

/-- The optimal residual vector `e_ξ - p* cosh(x/2) - i q* sinh(x/2)` in the aperture space. -/
def optimalResidualVector (a : SuzukiPositiveAperture) (ξ : ℝ) : suzukiApertureHilbert a :=
  planeWaveApertureVector a ξ -
    (((optimalCosParameter a.1 (2 * Real.pi * ξ) : ℂ) +
        (optimalSinParameter a.1 (2 * Real.pi * ξ) : ℂ) * Complex.I) / 2) •
      ccmPolarApertureVector a (1 / 2) -
    (((optimalCosParameter a.1 (2 * Real.pi * ξ) : ℂ) -
        (optimalSinParameter a.1 (2 * Real.pi * ξ) : ℂ) * Complex.I) / 2) •
      ccmPolarApertureVector a (-1 / 2)

theorem optimalResidualVector_coe (a : SuzukiPositiveAperture) (ξ : ℝ) :
    (optimalResidualVector a ξ : SoninL2) = poleResidualL2 a ξ
      (optimalCosParameter a.1 (2 * Real.pi * ξ)) (optimalSinParameter a.1 (2 * Real.pi * ξ)) :=
  rfl

private theorem inner_ccmPolarL2Vector_eq_integral (a : SuzukiPositiveAperture) (s t : ℝ) :
    inner ℂ (ccmPolarL2Vector a s) (ccmPolarL2Vector a t) =
      ((∫ x in (-a.1)..a.1, Real.exp ((s + t) * x) : ℝ) : ℂ) := by
  rw [MeasureTheory.L2.inner_def, ← intervalIntegral.integral_ofReal]
  have hae : (fun x : ℝ => inner ℂ ((ccmPolarL2Vector a s : ℝ → ℂ) x)
      ((ccmPolarL2Vector a t : ℝ → ℂ) x)) =ᵐ[volume]
      (centralInterval a.1).indicator (fun x : ℝ => ((Real.exp ((s + t) * x) : ℝ) : ℂ)) := by
    filter_upwards [ccmPolarL2Vector_coeFn a s, ccmPolarL2Vector_coeFn a t] with x h1 h2
    rw [h1, h2]
    by_cases hx : x ∈ centralInterval a.1
    · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx, RCLike.inner_apply]
      unfold ccmPolarProfile
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx, inner_zero_left]
  rw [integral_congr_ae hae, integral_indicator (measurableSet_centralInterval a.1), centralInterval,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [a.property])]

private theorem inner_polar_self (a : SuzukiPositiveAperture) {s : ℝ} (hs : s = 1 / 2 ∨ s = -1 / 2) :
    inner ℂ (ccmPolarL2Vector a s) (ccmPolarL2Vector a s) = ((2 * Real.sinh a.1 : ℝ) : ℂ) := by
  rw [inner_ccmPolarL2Vector_eq_integral]
  congr 1
  rw [Real.sinh_eq]
  rcases hs with rfl | rfl
  · have e : ∀ x : ℝ, (1 / 2 + 1 / 2) * x = x := fun x => by ring
    simp only [e, integral_exp]
    ring
  · have e : ∀ x : ℝ, (-1 / 2 + -1 / 2) * x = -x := fun x => by ring
    simp only [e]
    rw [intervalIntegral.integral_comp_neg (fun x => Real.exp x), neg_neg, integral_exp]
    ring

private theorem inner_polar_opposite (a : SuzukiPositiveAperture) (s : ℝ) :
    inner ℂ (ccmPolarL2Vector a s) (ccmPolarL2Vector a (-s)) = ((2 * a.1 : ℝ) : ℂ) := by
  rw [inner_ccmPolarL2Vector_eq_integral]
  congr 1
  simp only [add_neg_cancel, zero_mul, Real.exp_zero, intervalIntegral.integral_const, smul_eq_mul,
    mul_one]
  ring

/-- The optimal residual vector is pole-vanishing. -/
theorem inner_optimalResidualVector_eq_zero (a : SuzukiPositiveAperture) {s : ℝ}
    (hs : s = 1 / 2 ∨ s = -1 / 2) (ξ : ℝ) :
    inner ℂ (ccmPolarL2Vector a s) (optimalResidualVector a ξ : SoninL2) = 0 := by
  have ha := a.2
  have h1 := (self_add_sinh_pos ha).ne'
  have h2 := (sinh_sub_self_pos ha).ne'
  rw [optimalResidualVector_coe]
  unfold poleResidualL2 optimalCosParameter optimalSinParameter
  rw [inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right,
    inner_ccmPolarL2Vector_planeWaveL2_eq hs]
  rcases hs with rfl | rfl
  · rw [inner_polar_self a (Or.inl rfl),
      show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, inner_polar_opposite a (1 / 2)]
    apply Complex.ext <;>
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.div_ofNat_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im,
        Complex.div_ofNat_im, Complex.zero_re, Complex.zero_im] <;>
      field_simp <;> ring
  · rw [inner_polar_self a (Or.inr rfl),
      show (1 / 2 : ℝ) = -(-1 / 2) by norm_num, inner_polar_opposite a (-1 / 2)]
    apply Complex.ext <;>
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.div_ofNat_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im,
        Complex.div_ofNat_im, Complex.zero_re, Complex.zero_im] <;>
      field_simp <;> ring

theorem norm_optimalResidualVector_sq (a : SuzukiPositiveAperture) (ξ : ℝ) :
    ‖optimalResidualVector a ξ‖ ^ 2 = optimalResidual a.1 (2 * Real.pi * ξ) := by
  rw [optimalResidual_eq_closedForm a.2, ← norm_sq_poleResidualL2_eq_closedForm]
  rfl

/-- **The residual bound is attained**: `f̂(ξ) = R_a(2πξ)` and `‖f‖² = R_a(2πξ)` for the optimal
residual vector. -/
theorem fourier_optimalResidualVector (a : SuzukiPositiveAperture) (ξ : ℝ) :
    𝓕 ((optimalResidualVector a ξ : SoninL2) : ℝ → ℂ) ξ =
      ((optimalResidual a.1 (2 * Real.pi * ξ) : ℝ) : ℂ) := by
  rw [fourier_eq_inner_planeWaveL2 a (optimalResidualVector a ξ) ξ]
  set r := optimalResidualVector a ξ
  have hdecomp : planeWaveL2 a ξ = (r : SoninL2) +
      (((optimalCosParameter a.1 (2 * Real.pi * ξ) : ℂ) +
        (optimalSinParameter a.1 (2 * Real.pi * ξ) : ℂ) * Complex.I) / 2) • ccmPolarL2Vector a (1 / 2) +
      (((optimalCosParameter a.1 (2 * Real.pi * ξ) : ℂ) -
        (optimalSinParameter a.1 (2 * Real.pi * ξ) : ℂ) * Complex.I) / 2) • ccmPolarL2Vector a (-1 / 2) := by
    rw [optimalResidualVector_coe]
    unfold poleResidualL2
    abel
  rw [hdecomp, inner_add_left, inner_add_left, inner_smul_left, inner_smul_left,
    inner_optimalResidualVector_eq_zero a (Or.inl rfl), inner_optimalResidualVector_eq_zero a (Or.inr rfl),
    mul_zero, mul_zero, add_zero, add_zero, inner_self_eq_norm_sq_to_K]
  have hn : ‖(r : SoninL2)‖ = ‖r‖ := rfl
  rw [hn, ← norm_optimalResidualVector_sq a ξ]
  push_cast
  rfl

/-- **Every valid Fourier density bound dominates the optimal residual.**  If
`|f̂(ξ)|² ≤ R ‖f‖²` for every pole-vanishing aperture vector, then `R_a(2πξ) ≤ R` whenever
`R_a(2πξ) > 0`. -/
theorem optimalResidual_le_of_density_bound (a : SuzukiPositiveAperture) (ξ R : ℝ)
    (hR : ∀ f : suzukiApertureHilbert a, inner ℂ (ccmPolarL2Vector a (1 / 2)) f.1 = 0 →
      inner ℂ (ccmPolarL2Vector a (-1 / 2)) f.1 = 0 → ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ^ 2 ≤ R * ‖f‖ ^ 2)
    (hpos : 0 < optimalResidual a.1 (2 * Real.pi * ξ)) :
    optimalResidual a.1 (2 * Real.pi * ξ) ≤ R := by
  have h := hR (optimalResidualVector a ξ) (inner_optimalResidualVector_eq_zero a (Or.inl rfl) ξ)
    (inner_optimalResidualVector_eq_zero a (Or.inr rfl) ξ)
  rw [fourier_optimalResidualVector, norm_optimalResidualVector_sq, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hpos, sq] at h
  exact le_of_mul_le_mul_right h hpos

/-- **The obstruction for every valid scalar certificate.**  Let `G ≥ 0` be any symbol deficit
(`S_a ≥ α - G`) and `R` any pointwise Fourier density bound valid on the pole-vanishing subspace,
with `G R` integrable.  Then for `a ≥ a₀` and `α > 0`, the certificate value `α - ∫ G R` is at most
`-κ e^a / a`.  Finite shell certificates are the case of step functions `G`, `R`. -/
theorem exists_certificate_le :
    ∃ κ : ℝ, 0 < κ ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : SuzukiPositiveAperture, a₀ ≤ a.1 →
      ∀ α : ℝ, 0 < α → ∀ G R : ℝ → ℝ, (∀ ξ, 0 ≤ G ξ) →
        (∀ ξ, α - G ξ ≤ freeLagSymbol a.1 ξ) →
        (∀ f : suzukiApertureHilbert a, inner ℂ (ccmPolarL2Vector a (1 / 2)) f.1 = 0 →
          inner ℂ (ccmPolarL2Vector a (-1 / 2)) f.1 = 0 →
            ∀ ξ, ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ^ 2 ≤ R ξ * ‖f‖ ^ 2) →
        Integrable (fun ξ => G ξ * R ξ) →
          α - ∫ ξ, G ξ * R ξ ≤ -(Real.pi / 96) * (Real.exp a.1 / a.1) := by
  obtain ⟨a₁, -, hband⟩ := exists_freeLagSymbol_le_on_band
  refine ⟨Real.pi / 96, by positivity, max a₁ 256, by positivity,
    fun a ha α hα G R hG hGS hRvalid hint => ?_⟩
  have ha256 : 256 ≤ a.1 := (le_max_right _ _).trans ha
  have hRlow : ∀ ξ, 2 * a.1 - 64 ≤ R ξ := fun ξ => by
    have h7 := optimalResidual_ge (by linarith : (7 : ℝ) ≤ a.1) (2 * Real.pi * ξ)
    exact h7.trans (optimalResidual_le_of_density_bound a ξ (R ξ)
      (fun f hp hm => hRvalid f hp hm ξ) (by linarith))
  have hK : 0 ≤ Real.pi / 96 * (Real.exp a.1 / a.1) := by
    have := a.2; positivity
  have h := sub_integral_le_of_band ha256 hα hK hint
    (fun ξ => mul_nonneg (hG ξ) (by linarith [hRlow ξ])) (fun ξ hξ => by
      have hS := hband a.1 ((le_max_left _ _).trans ha) ξ hξ
      have hGξ : α + Real.pi / 96 * (Real.exp a.1 / a.1) ≤ G ξ := by
        have := hGS ξ; linarith
      exact mul_le_mul hGξ (hRlow ξ) (by linarith) (hG ξ))
  linarith

end RHTower.FreeLagTrace
