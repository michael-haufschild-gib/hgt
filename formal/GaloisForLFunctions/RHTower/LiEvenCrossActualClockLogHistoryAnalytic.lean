import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPrimitive
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Real
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockHistoryBarrier
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Analytic.Order
import Mathlib.Topology.Instances.Real.Lemmas
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockDerivative

/-!
Entire continuation of the actual undamped logarithmic clock history.
The complete multiplicity-copy Taylor series has a uniform factorial majorant.
Its true complex derivative identifies the canonical real primitive at every
real clock. The full positive source moment gives exact origin order two;
analytic isolation then gives finite positive zero order and compact zero sets.
-/

open Complex Set Filter
open scoped BigOperators Topology
namespace RHTower
noncomputable section
local notation "D" => liEvenCrossActualClockLogHistory

private def hgt_lhc_frequency (q : XiZeroCopy) : ℂ := (xiSpectralPoint q)⁻¹

private def hgt_lhc_atom (z : ℂ) (p : XiZeroCopy × ℕ) : ℂ :=
  (-1:ℂ)^p.2 * (z*hgt_lhc_frequency p.1)^(2*(p.2+1)) /
    (((2*(p.2+1):ℕ):ℂ)*((2*(p.2+1)).factorial:ℂ))

private def hgt_lhc_complex (z : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, ∑' j : ℕ, hgt_lhc_atom z (q,j)

private theorem hgt_lhc_mass_summable :
    Summable (fun q : XiZeroCopy => ‖hgt_lhc_frequency q‖^2) := by
  simpa only [hgt_lhc_frequency, norm_inv, one_div, inv_pow]
    using xiSpectralPoint_inv_sq_summable

private theorem hgt_lhc_frequency_bound (q : XiZeroCopy) :
    ‖hgt_lhc_frequency q‖ ≤ 1 := by
  have h := norm_xiZeroCopyReciprocalSquare_lt_one_div_oneHundredFifty q
  have heq : ‖xiZeroCopyReciprocalSquare q‖ = ‖hgt_lhc_frequency q‖^2 := by
    simp [xiZeroCopyReciprocalSquare, hgt_lhc_frequency, norm_pow]
  rw [heq] at h
  nlinarith [norm_nonneg (hgt_lhc_frequency q)]

private theorem hgt_lhc_mass_eq :
    (∑' q : XiZeroCopy, ‖hgt_lhc_frequency q‖^2) = xiShiftAbsoluteMass 0 := by
  simp [xiShiftAbsoluteMass, hgt_lhc_frequency, xiZeroCopyReciprocalSquare, norm_pow]

private theorem hgt_lhc_degree_injective :
    Function.Injective (fun j : ℕ => 2*(j+1)) := by
  intro a b h
  change 2*(a+1) = 2*(b+1) at h
  omega

private theorem hgt_lhc_scalar_summable (R : ℝ) :
    Summable (fun j : ℕ => R^(2*(j+1))/((2*(j+1)).factorial:ℝ)) := by
  exact (Real.summable_pow_div_factorial R).comp_injective hgt_lhc_degree_injective

private theorem hgt_lhc_scalar_sum_le {R : ℝ} (hR : 0 ≤ R) :
    (∑' j : ℕ, R^(2*(j+1))/((2*(j+1)).factorial:ℝ)) ≤ Real.exp R := by
  have he : HasSum (fun n : ℕ => R^n/(n.factorial:ℝ)) (Real.exp R) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp R
  rw [← he.tsum_eq]
  exact Summable.tsum_le_tsum_of_inj (fun j : ℕ => 2*(j+1))
    hgt_lhc_degree_injective (fun n _ => by positivity) (fun j => le_rfl)
    (hgt_lhc_scalar_summable R) he.summable

private theorem hgt_lhc_majorant_summable {R : ℝ} (hR : 0 ≤ R) :
    Summable (fun p : XiZeroCopy × ℕ =>
      ‖hgt_lhc_frequency p.1‖^2 *
        (R^(2*(p.2+1))/((2*(p.2+1)).factorial:ℝ))) := by
  apply (summable_prod_of_nonneg (fun p => by positivity)).2
  constructor
  · intro q
    change Summable (fun j : ℕ => ‖hgt_lhc_frequency q‖^2 *
      (R^(2*(j+1))/((2*(j+1)).factorial:ℝ)))
    exact (hgt_lhc_scalar_summable R).mul_left (‖hgt_lhc_frequency q‖^2)
  · simp_rw [tsum_mul_left]
    exact hgt_lhc_mass_summable.mul_right _

private theorem hgt_lhc_atom_bound {R : ℝ} (hR : 0 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) (p : XiZeroCopy × ℕ) :
    ‖hgt_lhc_atom z p‖ ≤ ‖hgt_lhc_frequency p.1‖^2 *
      (R^(2*(p.2+1))/((2*(p.2+1)).factorial:ℝ)) := by
  have hf : ‖hgt_lhc_frequency p.1‖^(2*(p.2+1)) ≤ ‖hgt_lhc_frequency p.1‖^2 :=
    pow_le_pow_of_le_one (norm_nonneg _) (hgt_lhc_frequency_bound p.1) (by omega)
  have hzpow := pow_le_pow_left₀ (norm_nonneg z) hz (2*(p.2+1))
  have hn : (1:ℝ) ≤ (2*(p.2+1):ℕ) := by exact_mod_cast (show 1 ≤ 2*(p.2+1) by omega)
  have hnorm : ‖hgt_lhc_atom z p‖ =
      ‖z‖^(2*(p.2+1))*‖hgt_lhc_frequency p.1‖^(2*(p.2+1)) /
        (((2*(p.2+1):ℕ):ℝ)*((2*(p.2+1)).factorial:ℝ)) := by
    simp only [hgt_lhc_atom, norm_div, norm_mul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul, Complex.norm_natCast, mul_pow]
  rw [hnorm]
  calc
    _ ≤ R^(2*(p.2+1))*‖hgt_lhc_frequency p.1‖^2 /
        (((2*(p.2+1):ℕ):ℝ)*((2*(p.2+1)).factorial:ℝ)) :=
      div_le_div_of_nonneg_right (mul_le_mul hzpow hf (by positivity) (by positivity))
        (by positivity)
    _ ≤ R^(2*(p.2+1))*‖hgt_lhc_frequency p.1‖^2 /
        ((1:ℝ)*((2*(p.2+1)).factorial:ℝ)) := by
      gcongr
    _ = _ := by ring

private theorem hgt_lhc_norm_summable (z : ℂ) :
    Summable (fun p : XiZeroCopy × ℕ => ‖hgt_lhc_atom z p‖) := by
  exact Summable.of_nonneg_of_le (fun p => norm_nonneg _)
    (hgt_lhc_atom_bound (norm_nonneg z) le_rfl)
    (hgt_lhc_majorant_summable (norm_nonneg z))

private theorem hgt_lhc_norm_sum_le {R : ℝ} (hR : 0 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    (∑' p : XiZeroCopy × ℕ, ‖hgt_lhc_atom z p‖) ≤ xiShiftAbsoluteMass 0*Real.exp R := by
  have hs := hgt_lhc_majorant_summable hR
  calc
    _ ≤ ∑' p : XiZeroCopy × ℕ, ‖hgt_lhc_frequency p.1‖^2 *
        (R^(2*(p.2+1))/((2*(p.2+1)).factorial:ℝ)) :=
      (hgt_lhc_norm_summable z).tsum_le_tsum (hgt_lhc_atom_bound hR hz) hs
    _ = (∑' q : XiZeroCopy, ‖hgt_lhc_frequency q‖^2) *
        (∑' j : ℕ, R^(2*(j+1))/((2*(j+1)).factorial:ℝ)) := by
      rw [hs.tsum_prod]
      simp_rw [tsum_mul_left]
      rw [tsum_mul_right]
    _ ≤ (∑' q : XiZeroCopy, ‖hgt_lhc_frequency q‖^2)*Real.exp R :=
      mul_le_mul_of_nonneg_left (hgt_lhc_scalar_sum_le hR) (tsum_nonneg (fun q => by positivity))
    _ = _ := by rw [hgt_lhc_mass_eq]

private theorem hgt_lhc_pair_sum (z : ℂ) :
    (∑' p : XiZeroCopy × ℕ, hgt_lhc_atom z p) = hgt_lhc_complex z := by
  exact (hgt_lhc_norm_summable z).of_norm.tsum_prod

private theorem hgt_lhc_analytic (z : ℂ) : AnalyticAt ℂ hgt_lhc_complex z := by
  let R := ‖z‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hz : z ∈ Metric.ball (0:ℂ) R := by simp [R]
  have hd : DifferentiableOn ℂ (fun y : ℂ => ∑' p : XiZeroCopy × ℕ, hgt_lhc_atom y p)
      (Metric.ball 0 R) := by
    apply Complex.differentiableOn_tsum_of_summable_norm (hgt_lhc_majorant_summable hR)
    · intro p
      dsimp [hgt_lhc_atom]
      fun_prop
    · exact Metric.isOpen_ball
    · intro p y hy
      exact hgt_lhc_atom_bound hR ((by simpa using hy : ‖y‖ < R).le) p
  have he : (fun y : ℂ => ∑' p : XiZeroCopy × ℕ, hgt_lhc_atom y p) = hgt_lhc_complex :=
    funext hgt_lhc_pair_sum
  rw [he] at hd
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds hz)

private def hgt_lhd_atom (w z : ℂ) (j : ℕ) : ℂ :=
  (-1:ℂ)^j * (z*w)^(2*(j+1)) /
    (((2*(j+1):ℕ):ℂ)*((2*(j+1)).factorial:ℂ))

private def hgt_lhd_datom (w z : ℂ) (j : ℕ) : ℂ :=
  (-1:ℂ)^j * w * (z*w)^(2*j+1) / ((2*(j+1)).factorial:ℂ)

private theorem hgt_lhd_cosine_hasSum (v : ℂ) :
    HasSum (fun j : ℕ => (-1:ℂ)^j*v^(2*(j+1))/((2*(j+1)).factorial:ℂ))
      (1-Complex.cos v) := by
  have hh : HasSum
      (fun j : ℕ => (-1:ℂ)^(j+1)*v^(2*(j+1))/((2*(j+1)).factorial:ℂ))
      (Complex.cos v-1) := by
    simpa using (hasSum_nat_add_iff'
      (f:=fun j : ℕ => (-1:ℂ)^j*v^(2*j)/((2*j).factorial:ℂ)) 1).mpr
      (Complex.hasSum_cos v)
  convert! hh.neg using 1
  · ext j
    rw [pow_succ]
    ring
  · ring

private theorem hgt_lhd_atom_hasDerivAt (w z : ℂ) (j : ℕ) :
    HasDerivAt (fun y : ℂ => hgt_lhd_atom w y j) (hgt_lhd_datom w z j) z := by
  have hn : (((2*(j+1):ℕ):ℂ)) ≠ 0 := by
    exact_mod_cast (show (2*(j+1):ℕ) ≠ 0 by omega)
  have hf : ((2*(j+1)).factorial:ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (2*(j+1))).ne'
  have hd := ((((hasDerivAt_id z).mul_const w).pow (2*(j+1))).const_mul
    ((-1:ℂ)^j)).div_const (((2*(j+1):ℕ):ℂ)*((2*(j+1)).factorial:ℂ))
  convert! hd using 1
  dsimp [hgt_lhd_datom]
  rw [show 2*(j+1)-1=2*j+1 by omega]
  field_simp

private theorem hgt_lhd_datom_mul (w z : ℂ) (j : ℕ) :
    hgt_lhd_datom w z j*z =
      (-1:ℂ)^j*(z*w)^(2*(j+1))/((2*(j+1)).factorial:ℂ) := by
  unfold hgt_lhd_datom
  rw [div_mul_eq_mul_div, show 2*(j+1)=2*j+1+1 by omega, pow_succ]
  ring

private theorem hgt_lhd_atom_hasDerivAt_zero (w : ℂ) (j : ℕ) :
    HasDerivAt (fun y : ℂ => hgt_lhd_atom w y j) 0 0 := by
  simpa [hgt_lhd_datom, zero_pow (by omega : 2*j+1≠0)]
    using hgt_lhd_atom_hasDerivAt w 0 j

private theorem hgt_lha_derivative_hasSum (z : ℂ) :
    HasSum (fun p : XiZeroCopy × ℕ =>
      hgt_lhd_datom (hgt_lhc_frequency p.1) z p.2) (deriv hgt_lhc_complex z) := by
  let R := ‖z‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hz : z ∈ Metric.ball (0:ℂ) R := by simp [R]
  have hd := Complex.hasSum_deriv_of_summable_norm
    (F:=fun p : XiZeroCopy × ℕ => fun y : ℂ => hgt_lhc_atom y p)
    (hgt_lhc_majorant_summable hR)
    (fun p => by dsimp [hgt_lhc_atom]; fun_prop)
    Metric.isOpen_ball
    (fun p y hy => hgt_lhc_atom_bound hR
      ((by simpa using hy : ‖y‖ < R).le) p) hz
  have he : (fun y : ℂ => ∑' p : XiZeroCopy × ℕ, hgt_lhc_atom y p) = hgt_lhc_complex :=
    funext hgt_lhc_pair_sum
  rw [he] at hd
  apply hd.congr_fun
  intro p
  exact (hgt_lhd_atom_hasDerivAt (hgt_lhc_frequency p.1) z p.2).deriv.symm

private theorem hgt_lha_cosine_hasSum (z : ℂ) :
    HasSum (fun q : XiZeroCopy => 1-Complex.cos (z*hgt_lhc_frequency q))
      (deriv hgt_lhc_complex z*z) := by
  have hm := (hgt_lha_derivative_hasSum z).mul_right z
  apply hm.prod_fiberwise
  intro q
  apply (hgt_lhd_cosine_hasSum (z*hgt_lhc_frequency q)).congr_fun
  intro j
  exact hgt_lhd_datom_mul (hgt_lhc_frequency q) z j

private theorem hgt_lha_cosine_norm_summable (z : ℂ) :
    Summable (fun q : XiZeroCopy => ‖1-Complex.cos (z*hgt_lhc_frequency q)‖) :=
  (hgt_lha_cosine_hasSum z).summable.norm

private theorem hgt_lha_deriv_zero : deriv hgt_lhc_complex 0 = 0 := by
  have hh := (hgt_lha_derivative_hasSum 0).tsum_eq.symm
  simpa [hgt_lhd_datom] using hh

private theorem hgt_lha_hasDerivAt (z : ℂ) :
    HasDerivAt hgt_lhc_complex
      ((∑' q : XiZeroCopy, (1-Complex.cos (z*hgt_lhc_frequency q)))/z) z := by
  have hd := (hgt_lhc_analytic z).differentiableAt.hasDerivAt
  apply hd.congr_deriv
  by_cases hz : z=0
  · subst z
    simp [hgt_lha_deriv_zero]
  · exact (eq_div_iff hz).2 (hgt_lha_cosine_hasSum z).tsum_eq.symm

private theorem hgt_lhr_density_cast (t : ℝ) :
    ((∑' q : XiZeroCopy, (1-Complex.cos ((t:ℂ)*(xiSpectralPoint q)⁻¹)))/(t:ℂ)) =
      (liEvenCrossActualClockLogHistoryDensity t:ℂ) := by
  unfold liEvenCrossActualClockLogHistoryDensity
  rw [Complex.ofReal_div, liEvenCrossActualClockPrimitive_ofReal_eq_tsum_cosine]
  rfl

private theorem hgt_lhr_canonical (f : ℂ → ℂ) (hzero : f 0 = 0)
    (hderiv : ∀ t : ℝ, HasDerivAt f
      (liEvenCrossActualClockLogHistoryDensity t:ℂ) (t:ℂ)) (t : ℝ) :
    f (t:ℂ) = (liEvenCrossActualClockLogHistory t:ℂ) := by
  have hd (s : ℝ) : HasDerivAt
      (fun u : ℝ => f (u:ℂ)-(liEvenCrossActualClockLogHistory u:ℂ)) 0 s := by
    simpa only [sub_self, Pi.sub_apply] using! (hderiv s).comp_ofReal.sub
      (hasDerivAt_liEvenCrossActualClockLogHistory s).ofReal_comp
  have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simpa [hzero, liEvenCrossActualClockLogHistory_origin.2, sub_eq_zero] using he

private theorem hgt_lhr_real_analytic (f : ℂ → ℂ)
    (hf : ∀ z : ℂ, AnalyticAt ℂ f z) (t : ℝ) :
    AnalyticAt ℝ (fun u : ℝ => (f (u:ℂ)).re) t := by
  have hc : AnalyticAt ℝ f (t:ℂ) := (hf (t:ℂ)).restrictScalars
  have ha : AnalyticAt ℝ (fun u : ℝ => f (u:ℂ)) t :=
    hc.comp (f:=fun u : ℝ => (u:ℂ)) (Complex.ofRealCLM.analyticAt t)
  exact (Complex.reCLM.analyticAt (f (t:ℂ))).comp (f:=fun u : ℝ => f (u:ℂ)) ha

private theorem hgt_lhz_order_ne_top (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, AnalyticAt ℝ f x) {a : ℝ} (ha : f a ≠ 0) (t : ℝ) :
    analyticOrderAt f t ≠ ⊤ := by
  intro ht
  have he := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero t hf).mp ht
  exact ha (by rw [he]; rfl)

private theorem hgt_lhz_zero_factor (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, AnalyticAt ℝ f x) {a : ℝ} (ha : f a ≠ 0)
    (t : ℝ) (ht : f t = 0) :
    analyticOrderAt f t ≠ ⊤ ∧ 0 < analyticOrderNatAt f t ∧
      ∃ u : ℝ → ℝ, AnalyticAt ℝ u t ∧ u t ≠ 0 ∧
        ∀ᶠ s in 𝓝 t, f s = (s-t)^analyticOrderNatAt f t * u s := by
  have hn := hgt_lhz_order_ne_top f hf ha t
  obtain ⟨u, hu, hu0, he⟩ := (hf t).analyticOrderAt_ne_top.mp hn
  have hp : 0 < analyticOrderNatAt f t := by
    by_contra h
    have hk : analyticOrderNatAt f t = 0 := by omega
    have hh := he.self_of_nhds
    simp only [hk, pow_zero, one_smul, ht] at hh
    exact hu0 hh.symm
  refine ⟨hn, hp, u, hu, hu0, ?_⟩
  simpa only [smul_eq_mul] using! he

private theorem hgt_lhz_finite_zeros (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, AnalyticAt ℝ f x) {c : ℝ} (hc : f c ≠ 0) (a b : ℝ) :
    {t : ℝ | t ∈ Icc a b ∧ f t = 0}.Finite := by
  have hu : AnalyticOnNhd ℝ f univ := fun x _ => hf x
  have hh : f ⁻¹' {0}ᶜ ∈ codiscrete ℝ := hu.preimage_zero_mem_codiscrete hc
  have hi : f ⁻¹' {0}ᶜ ∈ codiscreteWithin (Icc a b) :=
    Filter.codiscreteWithin_mono (subset_univ (Icc a b)) hh
  have hfin := isCompact_Icc.finite_sdiff_of_mem_codiscreteWithin hi
  simpa only [sdiff_eq, preimage_compl, compl_compl, inter_def, mem_Icc,
    mem_preimage, mem_singleton_iff] using hfin

local notation "P" => liEvenCrossActualClockPrimitive
local notation "F" => liEvenCrossActualClockResponse

private theorem hgt_lho_primitive_eq : P = fun t : ℝ => t*deriv D t := by
  funext t
  rw [(hasDerivAt_liEvenCrossActualClockLogHistory t).deriv]
  unfold liEvenCrossActualClockLogHistoryDensity
  by_cases ht : t=0
  · subst t
    simp [liEvenCrossActualClockPrimitive_origin_even.1]
  · field_simp

private theorem hgt_lho_response_deriv_zero : deriv F 0 = normalizedPrimeArchMoment 0 := by
  rw [(hasDerivAt_liEvenCrossActualClockResponse 0).deriv,
    liEvenCrossActualClockDerivative_eq_tsum_cos]
  have h := tsum_xiZeroCopyReciprocalSquare_pow 0
  rw [← ofReal_normalizedPrimeArchMoment_eq_xiCentralReciprocalMoment] at h
  have hr := congrArg Complex.re h
  simpa [xiZeroCopyReciprocalSquare] using hr

private theorem hgt_lho_order_mul_deriv (f : ℝ → ℝ)
    (hf : AnalyticAt ℝ f 0) (hz : f 0 = 0) :
    analyticOrderAt (fun t : ℝ => t*deriv f t) 0 = analyticOrderAt f 0 := by
  calc
    _ = analyticOrderAt ((id : ℝ → ℝ)*deriv f) 0 := rfl
    _ = analyticOrderAt (id : ℝ → ℝ) 0 + analyticOrderAt (deriv f) 0 :=
      analyticOrderAt_mul analyticAt_id hf.deriv
    _ = analyticOrderAt (deriv f) 0 + 1 := by rw [analyticOrderAt_id, add_comm]
    _ = analyticOrderAt f 0 := by simpa [hz] using hf.analyticOrderAt_deriv_add_one

private theorem hgt_lho_origin_order (hD : AnalyticAt ℝ D 0) :
    analyticOrderNatAt D 0 = 2 := by
  have hP : AnalyticAt ℝ P 0 := by
    rw [hgt_lho_primitive_eq]
    exact analyticAt_id.mul hD.deriv
  have hPF : deriv P = F := funext fun t => (hasDerivAt_liEvenCrossActualClockPrimitive t).deriv
  have hF : AnalyticAt ℝ F 0 := by rw [← hPF]; exact hP.deriv
  have hF0 : F 0 = 0 := by simp [liEvenCrossActualClockResponse]
  have hF1 : deriv F 0 ≠ 0 := by
    rw [hgt_lho_response_deriv_zero]
    exact normalizedPrimeArchMoment_zero_pos.ne'
  have hFO : analyticOrderAt F 0 = 1 :=
    hF.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hF0 hF1
  have hPO : analyticOrderAt P 0 = 2 := by
    have hh : analyticOrderAt P 0 = (1+1:ℕ∞) := by
      simpa only [hPF, liEvenCrossActualClockPrimitive_origin_even.1, sub_zero, hFO]
        using! hP.analyticOrderAt_deriv_add_one.symm
    exact hh.trans (by norm_num)
  have hPD : analyticOrderAt P 0 = analyticOrderAt D 0 := by
    rw [hgt_lho_primitive_eq]
    exact hgt_lho_order_mul_deriv D hD liEvenCrossActualClockLogHistory_origin.2
  have hDO : analyticOrderAt D 0 = 2 := hPD.symm.trans hPO
  simp [analyticOrderNatAt, hDO]

private theorem hgt_lho_one_pos : 0 < D 1 := by
  have hm := xiShiftAbsoluteMass_pos 0
  have h := (liEvenCrossActualClockLogHistory_local_corridor
    (t:=1) (by norm_num) (by norm_num)).2.2
  exact lt_of_lt_of_le (by positivity) h

local notation "w" => (fun q : XiZeroCopy => (xiSpectralPoint q)⁻¹)
local notation "Amass" => xiShiftAbsoluteMass 0
local notation "Atom" => (fun (z : ℂ) (p : XiZeroCopy × ℕ) =>
  (-1:ℂ)^(Prod.snd p) * (z*w (Prod.fst p))^(2*(Prod.snd p+1)) /
    (((2*(Prod.snd p+1):ℕ):ℂ)*(Nat.factorial (2*(Prod.snd p+1)):ℂ)))

def liEvenCrossActualClockLogHistoryComplex (z : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, ∑' j : ℕ, Atom z (q,j)
local notation "Dc" => liEvenCrossActualClockLogHistoryComplex

theorem summable_norm_liEvenCrossActualClockLogHistoryTaylor (z : ℂ) :
  Summable (fun p : XiZeroCopy × ℕ => ‖Atom z p‖) := by
  exact hgt_lhc_norm_summable z

theorem liEvenCrossActualClockLogHistoryTaylor_norm_le
    {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) :
  (∑' p : XiZeroCopy × ℕ, ‖Atom z p‖) ≤ Amass*Real.exp R := by
  exact hgt_lhc_norm_sum_le hR hz

theorem analyticAt_liEvenCrossActualClockLogHistoryComplex (z : ℂ) :
  AnalyticAt ℂ Dc z := by
  exact hgt_lhc_analytic z

theorem hasDerivAt_liEvenCrossActualClockLogHistoryComplex (z : ℂ) :
  HasDerivAt Dc
    ((∑' q : XiZeroCopy, (1-Complex.cos (z*w q)))/z) z := by
  exact hgt_lha_hasDerivAt z

theorem liEvenCrossActualClockLogHistoryComplex_ofReal (t : ℝ) :
  Dc (t:ℂ) = (D t:ℂ) := by
  have hz : hgt_lhc_complex 0 = 0 := by
    simp [hgt_lhc_complex, hgt_lhc_atom]
  have hd (s : ℝ) : HasDerivAt hgt_lhc_complex
      (liEvenCrossActualClockLogHistoryDensity s:ℂ) (s:ℂ) := by
    rw [← hgt_lhr_density_cast s]
    exact hgt_lha_hasDerivAt (s:ℂ)
  exact hgt_lhr_canonical hgt_lhc_complex hz hd t

theorem analyticAt_liEvenCrossActualClockLogHistory (t : ℝ) :
  AnalyticAt ℝ D t := by
  have ha := hgt_lhr_real_analytic Dc analyticAt_liEvenCrossActualClockLogHistoryComplex t
  have he : (fun u : ℝ => (Dc (u:ℂ)).re) = D := by
    funext u
    rw [liEvenCrossActualClockLogHistoryComplex_ofReal]
    rfl
  rw [he] at ha
  exact ha

theorem liEvenCrossActualClockLogHistory_origin_order :
  analyticOrderNatAt D 0 = 2 := by
  exact hgt_lho_origin_order (analyticAt_liEvenCrossActualClockLogHistory 0)

theorem liEvenCrossActualClockLogHistory_zero_factor (t : ℝ) (hz : D t = 0) :
  analyticOrderAt D t ≠ ⊤ ∧ 0 < analyticOrderNatAt D t ∧
    ∃ u : ℝ→ℝ, AnalyticAt ℝ u t ∧ u t ≠ 0 ∧
      ∀ᶠ s in 𝓝 t, D s = (s-t)^analyticOrderNatAt D t * u s := by
  exact hgt_lhz_zero_factor D analyticAt_liEvenCrossActualClockLogHistory
    hgt_lho_one_pos.ne' t hz

theorem finite_liEvenCrossActualClockLogHistory_zeros (a b : ℝ) :
  {t : ℝ | t ∈ Icc a b ∧ D t = 0}.Finite := by
  exact hgt_lhz_finite_zeros D analyticAt_liEvenCrossActualClockLogHistory
    hgt_lho_one_pos.ne' a b

end
end RHTower
