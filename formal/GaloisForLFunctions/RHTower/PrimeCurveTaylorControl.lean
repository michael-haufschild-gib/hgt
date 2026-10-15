import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Basic
import GaloisForLFunctions.RHTower.PrimeCurveFiniteSmoothModels
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.ContDiff.RCLike


/-!
# Taylor control on the actual prime curve

The real prime vector and its finite truncations tend to zero in ell².
The omitted primes contribute o(N^(-sigma)) after truncation at N. A
C^(k+1) function vanishing on the actual curve therefore has a truncated
radial Taylor polynomial which is o(N^(-sigma)) whenever N < 2^(k+1).

These are dependencies for the actual-curve vacuum regularity obstruction.
They do not prove that obstruction, analytic continuation, or a zero-free strip.
-/

open Set Filter Topology
open scoped ContDiff

namespace RHTower.PrimeCurveTaylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem iteratedDeriv_radial {f : E → ℝ} {U : Set E} {n j : ℕ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ n f U) (v : E) (t : ℝ)
    (ht : t • v ∈ U) (hj : j ≤ n) :
    iteratedDeriv j (fun u : ℝ => f (u • v)) t =
      (iteratedFDeriv ℝ j f (t • v)) (fun _ : Fin j => v) := by
  let g : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ v
  have htg : g t ∈ U := ht
  have hopen : IsOpen (g ⁻¹' U) := hU.preimage g.continuous
  have h := g.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hopen.uniqueDiffOn
    htg (by exact_mod_cast hj : (j : ℕ∞ω) ≤ n)
  rw [iteratedFDerivWithin_of_isOpen j hopen htg,
    iteratedFDerivWithin_of_isOpen j hU htg] at h
  have h' := congrArg (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℝ) ℝ =>
    A (fun _ => 1)) h
  simpa only [iteratedDeriv_eq_iteratedFDeriv, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    g, ContinuousLinearMap.toSpanSingleton_apply, one_smul, Function.comp_def] using h'

theorem radial_taylor_bound {f : E → ℝ} {n : ℕ} {r C : ℝ} {x : E}
    (hf : ContDiffOn ℝ (n + 1) f (Metric.ball 0 r)) (hx : ‖x‖ < r)
    (hC : ∀ y ∈ Metric.ball (0 : E) r, ‖iteratedFDeriv ℝ (n + 1) f y‖ ≤ C) :
    ‖f x - ∑ j ∈ Finset.range (n + 1),
      (j.factorial : ℝ)⁻¹ * (iteratedFDeriv ℝ j f 0) (fun _ : Fin j => x)‖ ≤
        C * ‖x‖ ^ (n + 1) / (n.factorial : ℝ) := by
  have hs : MapsTo (fun t : ℝ => t • x) (Icc 0 1) (Metric.ball (0 : E) r) := by
    intro t ht
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg x) ht.2).trans_lt hx
  have hg : ContDiffOn ℝ (n + 1) (fun t : ℝ => f (t • x)) (Icc 0 1) :=
    hf.comp (contDiff_id.smul contDiff_const).contDiffOn hs
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (j : ℕ) (hj : j ≤ n + 1) :
      iteratedDerivWithin j (fun t : ℝ => f (t • x)) (Icc 0 1) t =
        (iteratedFDeriv ℝ j f (t • x)) (fun _ : Fin j => x) := by
    have hloc : ContDiffAt ℝ j (fun t : ℝ => f (t • x)) t := by
      apply ContDiffAt.fun_comp t _ (contDiffAt_id.smul contDiffAt_const)
      exact (hf.of_le (by exact_mod_cast hj)).contDiffAt (Metric.isOpen_ball.mem_nhds (hs ht))
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num)) hloc ht]
    exact iteratedDeriv_radial Metric.isOpen_ball hf x t (hs ht) hj
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖iteratedDerivWithin (n + 1) (fun t : ℝ => f (t • x)) (Icc 0 1) t‖ ≤
        C * ‖x‖ ^ (n + 1) := by
    rw [hd t ht (n + 1) le_rfl]
    calc
      ‖(iteratedFDeriv ℝ (n + 1) f (t • x)) (fun _ : Fin (n + 1) => x)‖
          ≤ ‖iteratedFDeriv ℝ (n + 1) f (t • x)‖ * ‖x‖ ^ (n + 1) := by
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
          (iteratedFDeriv ℝ (n + 1) f (t • x)).le_opNorm (fun _ => x)
      _ ≤ C * ‖x‖ ^ (n + 1) := mul_le_mul_of_nonneg_right (hC _ (hs ht)) (by positivity)
  have hpoly : taylorWithinEval (fun t : ℝ => f (t • x)) n (Icc 0 1) 0 1 =
      ∑ j ∈ Finset.range (n + 1),
        (j.factorial : ℝ)⁻¹ * (iteratedFDeriv ℝ j f 0) (fun _ : Fin j => x) := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hd 0 (by norm_num) j (Nat.le_of_lt (Finset.mem_range.mp hj))]
    simp only [sub_zero, one_pow, mul_one, zero_smul, smul_eq_mul]
  have h := taylor_mean_remainder_bound (a := 0) (b := 1) (x := 1)
    (C := C * ‖x‖ ^ (n + 1)) (by norm_num) hg (by norm_num) hb
  simpa only [one_smul, hpoly, sub_zero, one_pow, mul_one] using h

theorem exists_local_radial_taylor_bound {f : E → ℝ} {U : Set E} {n : ℕ}
    (hU : IsOpen U) (h0 : (0 : E) ∈ U) (hf : ContDiffOn ℝ (n + 1) f U) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖x‖ < r →
      ‖f x - ∑ j ∈ Finset.range (n + 1),
        (j.factorial : ℝ)⁻¹ * (iteratedFDeriv ℝ j f 0) (fun _ : Fin j => x)‖ ≤
          C * ‖x‖ ^ (n + 1) / (n.factorial : ℝ) := by
  let C : ℝ := ‖iteratedFDerivWithin ℝ (n + 1) f U 0‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hc : ContinuousAt (iteratedFDerivWithin ℝ (n + 1) f U) 0 :=
    (hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_rfl) hU.uniqueDiffOn 0 h0).continuousAt
      (hU.mem_nhds h0)
  have hev : ∀ᶠ y : E in 𝓝 0, y ∈ U ∧ ‖iteratedFDerivWithin ℝ (n + 1) f U y‖ < C := by
    filter_upwards [hU.mem_nhds h0,
      hc.norm.eventually (eventually_lt_nhds (lt_add_one ‖iteratedFDerivWithin ℝ (n + 1) f U 0‖))]
      with y hy hb
    exact ⟨hy, hb⟩
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp hev
  have hsub : Metric.ball (0 : E) r ⊆ U := fun y hy => (hb hy).1
  refine ⟨r, hr, C, hC, fun x hx => radial_taylor_bound (hf.mono hsub) hx ?_⟩
  intro y hy
  rw [← iteratedFDerivWithin_of_isOpen (n + 1) hU (hsub hy)]
  exact (hb hy).2.le

theorem radial_taylor_isBigO {f : E → ℝ} {U : Set E} {n : ℕ}
    (hU : IsOpen U) (h0 : (0 : E) ∈ U) (hf : ContDiffOn ℝ (n + 1) f U) :
    (fun x : E => f x - ∑ j ∈ Finset.range (n + 1),
      (j.factorial : ℝ)⁻¹ * (iteratedFDeriv ℝ j f 0) (fun _ : Fin j => x))
      =O[𝓝 0] (fun x : E => ‖x‖ ^ (n + 1)) := by
  obtain ⟨r, hr, C, _, hb⟩ := exists_local_radial_taylor_bound hU h0 hf
  apply Asymptotics.IsBigO.of_bound (C / (n.factorial : ℝ))
  filter_upwards [Metric.ball_mem_nhds (0 : E) hr] with x hx
  have hx' : ‖x‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  have h := hb x hx'
  rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) _)]
  convert h using 1
  ring

end RHTower.PrimeCurveTaylor


open Filter Set Topology

namespace RHTower.PrimeCurveModel

def finitePrimeSet (N : ℕ) : Finset Nat.Primes :=
  (Finset.range (N + 1)).subtype Nat.Prime

@[simp] theorem mem_finitePrimeSet (N : ℕ) (p : Nat.Primes) :
    p ∈ finitePrimeSet N ↔ p.val ≤ N := by
  simpa only [finitePrimeSet, Finset.mem_range, Nat.lt_succ_iff] using!
    (Finset.mem_subtype (p := Nat.Prime) (s := Finset.range (N + 1)) (a := p))

noncomputable def primeTruncation (N : ℕ) (σ : ℝ) : PrimeHilbert :=
  ∑ p ∈ finitePrimeSet N, lp.single 2 p ((p.val : ℝ) ^ (-σ))

theorem primeTruncation_apply (N : ℕ) (σ : ℝ) (p : Nat.Primes) :
    primeTruncation N σ p = if p.val ≤ N then (p.val : ℝ) ^ (-σ) else 0 := by
  classical
  simp only [primeTruncation, lp.coeFn_sum, Finset.sum_apply, lp.single_apply,
    Finset.sum_pi_single, mem_finitePrimeSet]

theorem primeCurve_sub_truncation_apply (N : ℕ) (σ : ℝ) (hσ : 1 / 2 < σ) (p : Nat.Primes) :
    (primeCurve σ hσ - primeTruncation N σ) p =
      if p.val ≤ N then 0 else (p.val : ℝ) ^ (-σ) := by
  simp only [lp.coeFn_sub, Pi.sub_apply, primeCurve_apply, primeTruncation_apply]
  split_ifs <;> simp

theorem rpow_tail_majorant {b p σ : ℝ} (hb : 0 < b) (hbp : b ≤ p) (hσ : 1 ≤ σ) :
    p ^ (-σ) ≤ b ^ (1 - σ) * p ^ (-1 : ℝ) := by
  have hp : 0 < p := hb.trans_le hbp
  calc
    p ^ (-σ) = p ^ (1 - σ) * p ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hp]
      congr 1
      ring
    _ ≤ b ^ (1 - σ) * p ^ (-1 : ℝ) :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hb hbp (by linarith)) (Real.rpow_nonneg hp.le _)

theorem norm_primeCurve_sub_truncation_le (N : ℕ) {σ : ℝ} (hσ : 1 ≤ σ) :
    ‖primeCurve σ (by linarith) - primeTruncation N σ‖ ≤
      (N + 1 : ℕ) ^ (1 - σ) * ‖primeCurve 1 (by norm_num)‖ := by
  have hN : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hnorm : ‖primeCurve σ (by linarith) - primeTruncation N σ‖ ≤
      ‖(((N + 1 : ℕ) : ℝ) ^ (1 - σ)) • primeCurve 1 (by norm_num)‖ := by
    apply lp.norm_mono (by norm_num)
    intro p
    change ‖(primeCurve σ _ - primeTruncation N σ) p‖ ≤
      ‖(((N + 1 : ℕ) : ℝ) ^ (1 - σ)) * (p.val : ℝ) ^ (-1 : ℝ)‖
    rw [primeCurve_sub_truncation_apply]
    split_ifs with hpN
    · simp only [norm_zero]
      exact norm_nonneg _
    · rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p.val) _),
        Real.norm_of_nonneg (by positivity)]
      exact rpow_tail_majorant hN (by exact_mod_cast (Nat.lt_of_not_ge hpN)) hσ
  simpa only [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hN.le _)] using hnorm

theorem norm_primeCurve_le {σ : ℝ} (hσ : 1 ≤ σ) :
    ‖primeCurve σ (by linarith)‖ ≤ (2 : ℝ) ^ (1 - σ) * ‖primeCurve 1 (by norm_num)‖ := by
  have hnorm : ‖primeCurve σ (by linarith)‖ ≤
      ‖((2 : ℝ) ^ (1 - σ)) • primeCurve 1 (by norm_num)‖ := by
    apply lp.norm_mono (by norm_num)
    intro p
    change ‖(p.val : ℝ) ^ (-σ)‖ ≤ ‖(2 : ℝ) ^ (1 - σ) * (p.val : ℝ) ^ (-1 : ℝ)‖
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p.val) _),
      Real.norm_of_nonneg (by positivity)]
    exact rpow_tail_majorant (by norm_num) (by exact_mod_cast p.property.two_le) hσ
  simpa only [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]
    using hnorm

theorem norm_primeTruncation_le (N : ℕ) {σ : ℝ} (hσ : 1 / 2 < σ) :
    ‖primeTruncation N σ‖ ≤ ‖primeCurve σ hσ‖ := by
  apply lp.norm_mono (by norm_num)
  intro p
  rw [primeTruncation_apply, primeCurve_apply]
  split_ifs
  · exact le_rfl
  · simp only [norm_zero]
    exact norm_nonneg _

noncomputable def farPrimeCurve (σ : ℝ) : PrimeHilbert :=
  if hσ : 1 / 2 < σ then primeCurve σ hσ else 0

theorem farPrimeCurve_eq {σ : ℝ} (hσ : 1 / 2 < σ) : farPrimeCurve σ = primeCurve σ hσ := by
  simp only [farPrimeCurve, dif_pos hσ]

theorem farPrimeCurve_tendsto_zero : Tendsto farPrimeCurve atTop (𝓝 0) := by
  have hpow : Tendsto (fun σ : ℝ => (2 : ℝ) ^ (1 - σ)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)).inv_tendsto_atTop
    simpa only [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
      div_eq_mul_inv, mul_zero, Pi.inv_apply] using h.const_mul 2
  apply squeeze_zero_norm' (a := fun σ : ℝ => (2 : ℝ) ^ (1 - σ) * ‖primeCurve 1 (by norm_num)‖)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with σ hσ
    rw [farPrimeCurve_eq (by linarith : 1 / 2 < σ)]
    exact norm_primeCurve_le hσ
  · simpa only [zero_mul] using hpow.mul_const ‖primeCurve 1 (by norm_num)‖

theorem primeTruncation_tendsto_zero (N : ℕ) : Tendsto (primeTruncation N) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun σ : ℝ => ‖farPrimeCurve σ‖)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with σ hσ
    rw [farPrimeCurve_eq (by linarith : 1 / 2 < σ)]
    exact norm_primeTruncation_le N (by linarith)
  · simpa only [norm_zero] using farPrimeCurve_tendsto_zero.norm

theorem rpow_one_sub {b : ℝ} (hb : 0 < b) (σ : ℝ) : b ^ (1 - σ) = b * b ^ (-σ) := by
  rw [sub_eq_add_neg, Real.rpow_add hb, Real.rpow_one]

theorem farPrimeCurve_isBigO :
    farPrimeCurve =O[atTop] (fun σ : ℝ => (2 : ℝ) ^ (-σ)) := by
  apply Asymptotics.IsBigO.of_bound (2 * ‖primeCurve 1 (by norm_num)‖)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with σ hσ
  rw [farPrimeCurve_eq (by linarith : 1 / 2 < σ),
    Real.norm_of_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]
  have h := norm_primeCurve_le hσ
  rw [rpow_one_sub (by norm_num : (0 : ℝ) < 2)] at h
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

theorem primeTruncation_isBigO (N : ℕ) :
    primeTruncation N =O[atTop] (fun σ : ℝ => (2 : ℝ) ^ (-σ)) := by
  apply Asymptotics.IsBigO.of_bound (2 * ‖primeCurve 1 (by norm_num)‖)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with σ hσ
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]
  have h := (norm_primeTruncation_le N (by linarith : 1 / 2 < σ)).trans (norm_primeCurve_le hσ)
  rw [rpow_one_sub (by norm_num : (0 : ℝ) < 2)] at h
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

theorem primeCurve_truncation_error_isBigO (N : ℕ) :
    (fun σ : ℝ => farPrimeCurve σ - primeTruncation N σ) =O[atTop]
      (fun σ : ℝ => ((N + 1 : ℕ) : ℝ) ^ (-σ)) := by
  apply Asymptotics.IsBigO.of_bound (((N + 1 : ℕ) : ℝ) * ‖primeCurve 1 (by norm_num)‖)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with σ hσ
  rw [farPrimeCurve_eq (by linarith : 1 / 2 < σ),
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (N + 1 : ℕ)) _)]
  have h := norm_primeCurve_sub_truncation_le N hσ
  rw [rpow_one_sub (by positivity : (0 : ℝ) < (N + 1 : ℕ))] at h
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

theorem faster_rpow_isLittleO {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (fun σ : ℝ => b ^ (-σ)) =o[atTop] (fun σ : ℝ => a ^ (-σ)) := by
  have hb : 0 < b := ha.trans hab
  apply (Asymptotics.isLittleO_iff_tendsto (fun σ hz =>
    False.elim ((Real.rpow_pos_of_pos ha (-σ)).ne' hz))).mpr
  have hratio (σ : ℝ) : b ^ (-σ) / a ^ (-σ) = (a / b) ^ σ := by
    rw [Real.rpow_neg hb.le, Real.rpow_neg ha.le, Real.div_rpow ha.le hb.le]
    simp only [div_eq_mul_inv, inv_inv, mul_comm]
  simp_rw [hratio]
  exact tendsto_rpow_atTop_of_base_lt_one (a / b)
    (by linarith [div_pos ha hb]) ((div_lt_one hb).mpr hab)

theorem primeCurve_truncation_error_isLittleO {N : ℕ} (hN : 1 ≤ N) :
    (fun σ : ℝ => farPrimeCurve σ - primeTruncation N σ) =o[atTop]
      (fun σ : ℝ => (N : ℝ) ^ (-σ)) :=
  (primeCurve_truncation_error_isBigO N).trans_isLittleO
    (faster_rpow_isLittleO (by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN))
      (by exact_mod_cast Nat.lt_succ_self N))

end RHTower.PrimeCurveModel

namespace RHTower.PrimeCurveModel


theorem vanishing_curve_truncation_isLittleO {f : PrimeHilbert → ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hf : ContDiffAt ℝ 1 f 0)
    (hv : ∀ᶠ σ : ℝ in atTop, f (farPrimeCurve σ) = 0) :
    (fun σ : ℝ => f (primeTruncation N σ)) =o[atTop]
      (fun σ : ℝ => (N : ℝ) ^ (-σ)) := by
  have h := hf.hasStrictFDerivAt (by norm_num) |>.isBigO_sub.comp_tendsto
    (farPrimeCurve_tendsto_zero.prodMk_nhds (primeTruncation_tendsto_zero N))
  have he := (h.trans_isLittleO (primeCurve_truncation_error_isLittleO hN)).neg_left
  apply he.congr' _ (Filter.EventuallyEq.refl _ _)
  filter_upwards [hv] with σ hσ
  simp only [Function.comp_def, hσ, zero_sub, neg_neg]

theorem truncated_radial_taylor_error_isBigO {f : PrimeHilbert → ℝ} {U : Set PrimeHilbert}
    {k : ℕ} (hU : IsOpen U) (h0 : (0 : PrimeHilbert) ∈ U)
    (hf : ContDiffOn ℝ (k + 1) f U) (N : ℕ) :
    (fun σ : ℝ => f (primeTruncation N σ) - ∑ j ∈ Finset.range (k + 1),
      (j.factorial : ℝ)⁻¹ * (iteratedFDeriv ℝ j f 0)
        (fun _ : Fin j => primeTruncation N σ)) =O[atTop]
      (fun σ : ℝ => ((2 : ℝ) ^ (k + 1 : ℕ)) ^ (-σ)) := by
  have ht := (RHTower.PrimeCurveTaylor.radial_taylor_isBigO hU h0 hf).comp_tendsto
    (primeTruncation_tendsto_zero N)
  have hn := (primeTruncation_isBigO N).norm_left.pow (k + 1)
  have hr (σ : ℝ) : ((2 : ℝ) ^ (-σ)) ^ (k + 1) =
      ((2 : ℝ) ^ (k + 1 : ℕ)) ^ (-σ) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-σ)), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_natCast (2 : ℝ), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
  simpa only [Function.comp_def, hr] using ht.trans hn

theorem truncated_radial_taylor_isLittleO {f : PrimeHilbert → ℝ} {U : Set PrimeHilbert}
    {k N : ℕ} (hU : IsOpen U) (h0 : (0 : PrimeHilbert) ∈ U)
    (hf : ContDiffOn ℝ (k + 1) f U) (hN : 1 ≤ N) (hNk : N < 2 ^ (k + 1))
    (hv : ∀ᶠ σ : ℝ in atTop, f (farPrimeCurve σ) = 0) :
    (fun σ : ℝ => ∑ j ∈ Finset.range (k + 1),
      (j.factorial : ℝ)⁻¹ * (iteratedFDeriv ℝ j f 0)
        (fun _ : Fin j => primeTruncation N σ)) =o[atTop]
      (fun σ : ℝ => (N : ℝ) ^ (-σ)) := by
  have hfirst := vanishing_curve_truncation_isLittleO hN
    ((hf.of_le (by exact_mod_cast Nat.succ_pos k)).contDiffAt (hU.mem_nhds h0)) hv
  have herr := (truncated_radial_taylor_error_isBigO hU h0 hf N).trans_isLittleO
    (faster_rpow_isLittleO (a := (N : ℝ)) (by exact_mod_cast (Nat.zero_lt_of_lt hN))
      (by exact_mod_cast hNk))
  simpa only [sub_sub_cancel] using hfirst.sub herr

end RHTower.PrimeCurveModel
