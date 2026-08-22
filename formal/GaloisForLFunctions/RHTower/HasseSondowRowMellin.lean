import GaloisForLFunctions.RHTower.SalemFermiModeIntegral
import GaloisForLFunctions.HTGeometry.ConstitutiveHassePacketFormation
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# The Hasse–Sondow row as a Mellin transform

Each finite-difference row of the Hasse–Sondow global series is, after multiplication by the gamma
factor, the Mellin transform of one elementary positive kernel.  The row therefore obeys the exact
majorant `|Γ(s) h_n(s)| ≤ Γ(σ) h_n(σ)`, and summing the geometric depth weights recovers the
Dirichlet eta function on the whole right half-plane.
-/

open MeasureTheory Set Complex

namespace RHTower

noncomputable section

/-- The depth-`n` Hasse–Sondow finite-difference row (PFM.1). -/
def hasseRow (s : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (n.choose k : ℂ) * ((k : ℂ) + 1) ^ (-s)

/-- The positive kernel of the depth-`n` row. -/
def hasseKernel (n : ℕ) (t : ℝ) : ℝ := Real.exp (-t) * (1 - Real.exp (-t)) ^ n

theorem hasseKernel_nonneg (n : ℕ) {t : ℝ} (ht : 0 < t) : 0 ≤ hasseKernel n t := by
  have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 : (0 : ℝ) ≤ 1 - Real.exp (-t) := by linarith
  exact mul_nonneg (Real.exp_pos _).le (pow_nonneg h2 n)

/-- The kernel is the finite alternating sum of pure exponentials. -/
theorem hasseKernel_eq_sum (n : ℕ) (t : ℝ) :
    hasseKernel n t
      = ∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.exp (-(((k : ℝ) + 1) * t)) := by
  rw [hasseKernel, ← GaloisForLFunctions.HTGeometry.hasseFiniteDifference_packet
    (Real.exp (-t)) n, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show -(((k : ℝ) + 1) * t) = -t + (k : ℝ) * -t by ring, Real.exp_add,
    ← Real.exp_nat_mul]
  ring

private theorem mellin_exp_neg_mul {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    mellin (fun t : ℝ => ((Real.exp (-(a * t)) : ℝ) : ℂ)) s
      = ((a : ℂ)) ^ (-s) * Complex.Gamma s := by
  have hbase : mellin (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) s = Complex.Gamma s := by
    rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral_eq_mellin]
  have h := mellin_comp_mul_left (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) s ha
  simp only [smul_eq_mul] at h
  rw [show (fun t : ℝ => ((Real.exp (-(a * t)) : ℝ) : ℂ))
      = fun t : ℝ => ((Real.exp (-(a * t)) : ℝ) : ℂ) from rfl]
  rw [show (fun t : ℝ => ((Real.exp (-(a * t)) : ℝ) : ℂ))
      = (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) ∘ (fun t : ℝ => a * t) by
    funext t
    rfl]
  rw [show ((fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) ∘ (fun t : ℝ => a * t))
      = fun t : ℝ => ((Real.exp (-(a * t)) : ℝ) : ℂ) from rfl]
  rw [h, hbase]

theorem integrableOn_mellin_exp_neg_mul {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • ((Real.exp (-(a * t)) : ℝ) : ℂ))
      (Ioi 0) := by
  have hconv : MellinConvergent (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) s := by
    rw [MellinConvergent]
    have := Complex.GammaIntegral_convergent hs
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [smul_eq_mul]
    rw [Complex.ofReal_exp]
    ring
  exact (MellinConvergent.comp_mul_left
    (f := fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) (s := s) ha).2 hconv

/-- **(PFM.2).**  The gamma-normalized row is the Mellin transform of its positive kernel. -/
theorem mellin_hasseKernel {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    mellin (fun t : ℝ => ((hasseKernel n t : ℝ) : ℂ)) s = Complex.Gamma s * hasseRow s n := by
  have hsum : (fun t : ℝ => ((hasseKernel n t : ℝ) : ℂ))
      = fun t : ℝ => ∑ k ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ k * (n.choose k : ℂ)) * ((Real.exp (-(((k : ℝ) + 1) * t)) : ℝ) : ℂ) := by
    funext t
    rw [hasseKernel_eq_sum]
    push_cast
    rfl
  rw [mellin]
  rw [show (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) • ((hasseKernel n t : ℝ) : ℂ))
      = ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) •
        ∑ k ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ k * (n.choose k : ℂ)) *
            ((Real.exp (-(((k : ℝ) + 1) * t)) : ℝ) : ℂ) from
    setIntegral_congr_fun measurableSet_Ioi fun t ht => by
      congr 1
      rw [hasseKernel_eq_sum]
      push_cast
      rfl]
  have hint : ∀ k ∈ Finset.range (n + 1),
      IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) •
        (((-1 : ℂ) ^ k * (n.choose k : ℂ)) *
          ((Real.exp (-(((k : ℝ) + 1) * t)) : ℝ) : ℂ))) (Ioi 0) := by
    intro k _
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hc : IntegrableOn (fun t : ℝ => ((-1 : ℂ) ^ k * (n.choose k : ℂ)) *
        ((t : ℂ) ^ (s - 1) • ((Real.exp (-(((k : ℝ) + 1) * t)) : ℝ) : ℂ))) (Ioi 0) :=
      (integrableOn_mellin_exp_neg_mul hs hpos).const_mul _
    refine IntegrableOn.congr_fun hc (fun t ht => ?_) measurableSet_Ioi
    simp only [smul_eq_mul]
    ring
  rw [show (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) •
      ∑ k ∈ Finset.range (n + 1),
        ((-1 : ℂ) ^ k * (n.choose k : ℂ)) * ((Real.exp (-(((k : ℝ) + 1) * t)) : ℝ) : ℂ))
      = ∑ k ∈ Finset.range (n + 1), ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) •
        (((-1 : ℂ) ^ k * (n.choose k : ℂ)) *
          ((Real.exp (-(((k : ℝ) + 1) * t)) : ℝ) : ℂ)) by
    rw [← integral_finsetSum _ hint]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [Finset.smul_sum]]
  rw [hasseRow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hmel : ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) •
      (((-1 : ℂ) ^ k * (n.choose k : ℂ)) *
        ((Real.exp (-(((k : ℝ) + 1) * t)) : ℝ) : ℂ))
      = ((-1 : ℂ) ^ k * (n.choose k : ℂ)) *
        mellin (fun t : ℝ => ((Real.exp (-(((k : ℝ) + 1) * t)) : ℝ) : ℂ)) s := by
    rw [mellin, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [smul_eq_mul]
    ring
  rw [hmel, mellin_exp_neg_mul hs hpos]
  push_cast
  ring

/-! ## The real row and its majorant -/

theorem cpow_ofReal_sub_one {t : ℝ} (ht : 0 ≤ t) (σ : ℝ) :
    (t : ℂ) ^ ((σ : ℂ) - 1) = ((t ^ (σ - 1) : ℝ) : ℂ) := by
  rw [show ((σ : ℂ) - 1) = (((σ - 1 : ℝ)) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow ht]

/-- The row at a real exponent. -/
def hasseRowReal (σ : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ) * ((k : ℝ) + 1) ^ (-σ)

theorem hasseRow_ofReal (σ : ℝ) (n : ℕ) :
    hasseRow ((σ : ℝ) : ℂ) n = ((hasseRowReal σ n : ℝ) : ℂ) := by
  rw [hasseRow, hasseRowReal]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [show ((k : ℂ) + 1) = ((((k : ℝ) + 1 : ℝ)) : ℂ) by push_cast; ring,
    show (-(σ : ℂ)) = (((-σ : ℝ)) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity)]

theorem integrableOn_mellin_hasseKernel {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • ((hasseKernel n t : ℝ) : ℂ)) (Ioi 0) := by
  have hint : ∀ k ∈ Finset.range (n + 1),
      IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) •
        (((-1 : ℂ) ^ k * (n.choose k : ℂ)) *
          ((Real.exp (-(((k : ℝ) + 1) * t)) : ℝ) : ℂ))) (Ioi 0) := by
    intro k _
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hc : IntegrableOn (fun t : ℝ => ((-1 : ℂ) ^ k * (n.choose k : ℂ)) *
        ((t : ℂ) ^ (s - 1) • ((Real.exp (-(((k : ℝ) + 1) * t)) : ℝ) : ℂ))) (Ioi 0) :=
      (integrableOn_mellin_exp_neg_mul hs hpos).const_mul _
    refine IntegrableOn.congr_fun hc (fun t ht => ?_) measurableSet_Ioi
    simp only [smul_eq_mul]
    ring
  have hfs := integrable_finsetSum (Finset.range (n + 1)) hint
  refine IntegrableOn.congr_fun hfs (fun t ht => ?_) measurableSet_Ioi
  show (∑ k ∈ Finset.range (n + 1), (t : ℂ) ^ (s - 1) •
      (((-1 : ℂ) ^ k * (n.choose k : ℂ)) * ((Real.exp (-(((k : ℝ) + 1) * t)) : ℝ) : ℂ)))
    = (t : ℂ) ^ (s - 1) • ((hasseKernel n t : ℝ) : ℂ)
  rw [← Finset.smul_sum]
  congr 1
  rw [hasseKernel_eq_sum]
  push_cast
  rfl

theorem integrableOn_rpow_mul_hasseKernel {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * hasseKernel n t) (Ioi 0) := by
  have hre : (0 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have hbase := integrableOn_mellin_hasseKernel hre n
  have hcast : IntegrableOn
      (fun t : ℝ => ((t ^ (σ - 1) * hasseKernel n t : ℝ) : ℂ)) (Ioi 0) := by
    refine hbase.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (0 : ℝ) < t := ht
    show (t : ℂ) ^ ((σ : ℂ) - 1) • ((hasseKernel n t : ℝ) : ℂ)
      = ((t ^ (σ - 1) * hasseKernel n t : ℝ) : ℂ)
    rw [smul_eq_mul, cpow_ofReal_sub_one ht0.le, ← Complex.ofReal_mul]
  have hre := hcast.re
  exact hre.congr (Filter.Eventually.of_forall fun t => by simp)

/-- **(PFM.2) in real form.**  The gamma-normalized real row is the positive Mellin integral. -/
theorem gamma_mul_hasseRowReal {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    Real.Gamma σ * hasseRowReal σ n = ∫ t : ℝ in Ioi 0, t ^ (σ - 1) * hasseKernel n t := by
  have hre : (0 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have h := mellin_hasseKernel hre n
  rw [hasseRow_ofReal, Complex.Gamma_ofReal, mellin] at h
  have hcast : (∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((σ : ℂ) - 1) • ((hasseKernel n t : ℝ) : ℂ))
      = ((∫ t : ℝ in Ioi 0, t ^ (σ - 1) * hasseKernel n t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    show (t : ℂ) ^ ((σ : ℂ) - 1) • ((hasseKernel n t : ℝ) : ℂ)
      = ((t ^ (σ - 1) * hasseKernel n t : ℝ) : ℂ)
    rw [smul_eq_mul, cpow_ofReal_sub_one ht0.le, ← Complex.ofReal_mul]
  rw [hcast] at h
  exact_mod_cast h.symm

/-- **(PFM.4).**  The complex row is dominated by its real profile. -/
theorem norm_gamma_mul_hasseRow_le {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖Complex.Gamma s * hasseRow s n‖ ≤ Real.Gamma s.re * hasseRowReal s.re n := by
  rw [← mellin_hasseKernel hs n, mellin, gamma_mul_hasseRowReal hs n]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine le_of_eq (setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (hasseKernel_nonneg n ht0)]
  congr 2

/-! ## Summation over the depth tower -/

theorem mellinConvergent_salemFermiKernel {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent salemFermiKernel s :=
  mellinConvergent_of_isBigO_rpow_exp (a := 1) (b := 0) one_pos
    salemFermiKernel_locallyIntegrableOn salemFermiKernel_isBigO_exp_neg
    salemFermiKernel_isBigO_one_at_zero hs

theorem integrableOn_rpow_mul_fermi {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => t ^ (s.re - 1) * (Real.exp t + 1)⁻¹) (Ioi 0) := by
  have h := (mellinConvergent_salemFermiKernel hs).norm
  refine IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (0 : ℝ) < t := ht
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, norm_salemFermiKernel]
  congr 1

/-- **(PFM.3).**  The geometrically weighted depth tower sums to the Dirichlet eta function. -/
theorem hasSum_hasseRow_eq_eta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    HasSum (fun n : ℕ => (((1 / 2 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hasseRow s n)
      ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) := by
  have hGamma : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hFint : ∀ n : ℕ, IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) •
        (((1 / 2 : ℝ) ^ (n + 1) * hasseKernel n t : ℝ) : ℂ)) (Ioi 0) := by
    intro n
    have hc : IntegrableOn (fun t : ℝ => (((1 / 2 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
        ((t : ℂ) ^ (s - 1) • ((hasseKernel n t : ℝ) : ℂ))) (Ioi 0) :=
      (integrableOn_mellin_hasseKernel hs n).const_mul _
    refine IntegrableOn.congr_fun hc (fun t ht => ?_) measurableSet_Ioi
    show (((1 / 2 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
        ((t : ℂ) ^ (s - 1) • ((hasseKernel n t : ℝ) : ℂ))
      = (t : ℂ) ^ (s - 1) • (((1 / 2 : ℝ) ^ (n + 1) * hasseKernel n t : ℝ) : ℂ)
    push_cast
    simp only [smul_eq_mul]
    ring
  have hbound : ∀ n : ℕ, ∀ᵐ t : ℝ ∂(volume.restrict (Ioi 0)),
      ‖(t : ℂ) ^ (s - 1) • (((1 / 2 : ℝ) ^ (n + 1) * hasseKernel n t : ℝ) : ℂ)‖
        ≤ t ^ (s.re - 1) * ((1 / 2 : ℝ) ^ (n + 1) * hasseKernel n t) := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by
        have := hasseKernel_nonneg n ht0
        positivity)]
    rw [Complex.sub_re, Complex.one_re]
  have hjoint : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * hasseKernel n t) (Real.exp t + 1)⁻¹ := by
    intro t ht0
    have h := GaloisForLFunctions.HTGeometry.hasSum_hassePacketJointAtom ht0
    rw [GaloisForLFunctions.HTGeometry.hassePacketScale_eq_fermiKernel] at h
    have hfun : GaloisForLFunctions.HTGeometry.hassePacketJointAtom t
        = fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * hasseKernel n t := by
      funext n
      simp only [GaloisForLFunctions.HTGeometry.hassePacketJointAtom, hasseKernel]
      ring
    rw [hfun] at h
    exact h
  have hsumbound : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi 0)),
      Summable fun n : ℕ => t ^ (s.re - 1) * ((1 / 2 : ℝ) ^ (n + 1) * hasseKernel n t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact ((hjoint t ht).summable).mul_left _
  have hdomint : Integrable
      (fun t : ℝ => ∑' n : ℕ, t ^ (s.re - 1) * ((1 / 2 : ℝ) ^ (n + 1) * hasseKernel n t))
      (volume.restrict (Ioi 0)) := by
    refine IntegrableOn.congr_fun (integrableOn_rpow_mul_fermi hs) (fun t ht => ?_)
      measurableSet_Ioi
    have ht0 : (0 : ℝ) < t := ht
    exact (((hjoint t ht0).mul_left (t ^ (s.re - 1))).tsum_eq).symm
  have hker : ∀ t : ℝ, salemFermiKernel t = (((Real.exp t + 1)⁻¹ : ℝ) : ℂ) := by
    intro t
    rw [salemFermiKernel, ← Complex.ofReal_inv]
  have hlim : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi 0)),
      HasSum (fun n : ℕ => (t : ℂ) ^ (s - 1) •
          (((1 / 2 : ℝ) ^ (n + 1) * hasseKernel n t : ℝ) : ℂ))
        ((t : ℂ) ^ (s - 1) • salemFermiKernel t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have hC : HasSum (fun n : ℕ => (((1 / 2 : ℝ) ^ (n + 1) * hasseKernel n t : ℝ) : ℂ))
        (((Real.exp t + 1)⁻¹ : ℝ) : ℂ) := Complex.ofRealCLM.hasSum (hjoint t ht0)
    rw [hker t]
    exact hC.const_smul ((t : ℂ) ^ (s - 1))
  have hHS := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi 0))
    (fun n t => t ^ (s.re - 1) * ((1 / 2 : ℝ) ^ (n + 1) * hasseKernel n t))
    (fun n => (hFint n).aestronglyMeasurable) hbound hsumbound hdomint hlim
  have hleft : ∀ n : ℕ,
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) •
        (((1 / 2 : ℝ) ^ (n + 1) * hasseKernel n t : ℝ) : ℂ))
      = (((1 / 2 : ℝ) ^ (n + 1) : ℝ) : ℂ) * (Complex.Gamma s * hasseRow s n) := by
    intro n
    rw [← mellin_hasseKernel hs n, mellin, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    push_cast
    simp only [smul_eq_mul]
    ring
  have hright : (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) • salemFermiKernel t)
      = Complex.Gamma s * ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) := by
    rw [← mellin, mellin_salemFermiKernel_eq_closedForm hs hs1]
    ring
  rw [hright] at hHS
  simp only [hleft] at hHS
  have hfinal := hHS.mul_left (Complex.Gamma s)⁻¹
  have hgoal : ((Complex.Gamma s)⁻¹ * (Complex.Gamma s * ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s)))
      = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
    rw [← mul_assoc, inv_mul_cancel₀ hGamma, one_mul]
  rw [hgoal] at hfinal
  have heq : ∀ n : ℕ, (Complex.Gamma s)⁻¹ * ((((1 / 2 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
      (Complex.Gamma s * hasseRow s n))
      = (((1 / 2 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hasseRow s n := by
    intro n
    rw [← mul_assoc, mul_comm ((Complex.Gamma s)⁻¹), mul_assoc, ← mul_assoc (Complex.Gamma s)⁻¹,
      inv_mul_cancel₀ hGamma, one_mul]
  simpa only [heq] using hfinal

/-- **(PFM.11).**  Every nontrivial zeta zero gives an unconditional vanishing relation between the
Hasse rows. -/
theorem hasSum_hasseRow_eq_zero_of_zetaZero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ ≠ 1)
    (hz : riemannZeta ρ = 0) :
    HasSum (fun n : ℕ => (((1 / 2 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hasseRow ρ n) 0 := by
  have h := hasSum_hasseRow_eq_eta h0 h1
  rwa [hz, mul_zero] at h

end

end RHTower
