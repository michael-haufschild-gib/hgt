import GaloisForLFunctions.RHTower.PutnamPeriodization

/-!
# The Fourier coefficients of the periodisation

The Fourier coefficients of a periodisation are the samples of the Fourier transform of the
original kernel.  For Putnam's kernel this says

`∫_0^{2π/d} D_a(x) e^{-idnx} dx  =  - ζ(½+i(a+dn)) / (½+i(a+dn))`,

so the whole vertical progression of zeta values is recorded in one periodic function.
-/

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

theorem iUnion_Ioc_period {P : ℝ} (hP : 0 < P) :
    (⋃ k : ℤ, Ioc ((k : ℝ) * P) (((k : ℝ) + 1) * P)) = univ := by
  ext y
  simp only [mem_iUnion, mem_Ioc, mem_univ, iff_true]
  refine ⟨⌈y / P⌉ - 1, ?_, ?_⟩
  · push_cast
    have h1 : (y / P) ≤ (⌈y / P⌉ : ℝ) := Int.le_ceil _
    have h2 : ((⌈y / P⌉ : ℝ) - 1) < y / P := by
      have := Int.ceil_lt_add_one (y / P)
      linarith
    calc ((⌈y / P⌉ : ℝ) - 1) * P < (y / P) * P := by
          exact mul_lt_mul_of_pos_right h2 hP
      _ = y := by field_simp
  · push_cast
    have h1 : (y / P) ≤ (⌈y / P⌉ : ℝ) := Int.le_ceil _
    calc y = (y / P) * P := by field_simp
      _ ≤ (⌈y / P⌉ : ℝ) * P := mul_le_mul_of_nonneg_right h1 hP.le
      _ = ((⌈y / P⌉ : ℝ) - 1 + 1) * P := by ring

theorem pairwise_disjoint_Ioc_period {P : ℝ} (hP : 0 < P) :
    Pairwise (Function.onFun Disjoint
      (fun k : ℤ => Ioc ((k : ℝ) * P) (((k : ℝ) + 1) * P))) := by
  intro k l hkl
  rcases lt_or_gt_of_ne hkl with h | h
  · refine Set.disjoint_left.mpr fun y hy hy' => ?_
    have hk1 : ((k : ℝ) + 1) ≤ (l : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h
    have h1 : y ≤ ((k : ℝ) + 1) * P := hy.2
    have h2 : (l : ℝ) * P < y := hy'.1
    nlinarith [hP]
  · refine Set.disjoint_left.mpr fun y hy hy' => ?_
    have hk1 : ((l : ℝ) + 1) ≤ (k : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h
    have h1 : y ≤ ((l : ℝ) + 1) * P := hy'.2
    have h2 : (k : ℝ) * P < y := hy.1
    nlinarith [hP]

/-- The lattice phase is trivial: `exp(-i d n k (2π/d)) = 1`. -/
theorem putnamTwist_shift {a d : ℝ} (hd : 0 < d) (n k : ℤ) (x : ℝ) :
    putnamTwist a (d * n) (x + (k : ℝ) * putnamPeriod d)
      = putnamKernel a (x + (k : ℝ) * putnamPeriod d) *
          Complex.exp (-((d * n : ℝ) : ℂ) * I * (x : ℂ)) := by
  rw [putnamTwist]
  congr 1
  have hkey : ((x + (k : ℝ) * putnamPeriod d : ℝ) : ℂ) = (x : ℂ) + (k : ℂ) * ((putnamPeriod d : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hkey, mul_add, Complex.exp_add]
  have hphase : -(((d * n : ℝ) : ℂ) * I) * ((k : ℂ) * ((putnamPeriod d : ℝ) : ℂ))
      = -(2 * Real.pi * ((n : ℝ) * (k : ℝ)) : ℝ) * I := by
    have hP : ((putnamPeriod d : ℝ) : ℂ) = 2 * (Real.pi : ℂ) / (d : ℂ) := by
      rw [putnamPeriod]
      push_cast
      ring
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd
    rw [hP]
    push_cast
    field_simp
  rw [hphase]
  have hone : Complex.exp (-((2 * Real.pi * ((n : ℝ) * (k : ℝ)) : ℝ) : ℂ) * I) = 1 := by
    have hrw : -((2 * Real.pi * ((n : ℝ) * (k : ℝ)) : ℝ) : ℂ) * I
        = ((-(n * k) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      push_cast
      ring
    rw [hrw]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [hone, mul_one]
  congr 1
  ring

theorem norm_putnamTwist (a ξ x : ℝ) : ‖putnamTwist a ξ x‖ = ‖putnamKernel a x‖ := by
  rw [putnamTwist, norm_mul, Complex.norm_exp]
  have hre : (-((ξ : ℂ) * I) * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  rw [hre, Real.exp_zero, mul_one]

/-- **The Fourier coefficients of the periodisation are the zeta values.** -/
theorem integral_putnamPeriodization_fourier {a d : ℝ} (hd : 0 < d) (n : ℤ) :
    (∫ x in Ioc (0 : ℝ) (putnamPeriod d),
        putnamPeriodization a d x * Complex.exp (-((d * n : ℝ) : ℂ) * I * (x : ℂ)))
      = -riemannZeta (1 / 2 + ((a + d * n : ℝ) : ℂ) * I)
          / (1 / 2 + ((a + d * n : ℝ) : ℂ) * I) := by
  classical
  set P : ℝ := putnamPeriod d with hPdef
  have hP : 0 < P := putnamPeriod_pos hd
  set g : ℤ → ℝ → ℂ := fun k x => putnamTwist a (d * n) (x + (k : ℝ) * P) with hgdef
  have hgnorm : ∀ (k : ℤ) (x : ℝ), x ∈ Ioc (0 : ℝ) P →
      ‖g k x‖ ≤ Real.exp (P / 2) * Real.exp (-(P / 2 * |(k : ℝ)|)) := by
    intro k x hx
    rw [hgdef]
    simp only
    rw [norm_putnamTwist]
    refine le_trans (norm_putnamKernel_le a _) ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hxb : |x| ≤ P := by
      rw [abs_of_pos hx.1]
      exact hx.2
    have habs : |(k : ℝ)| * P - P ≤ |x + (k : ℝ) * P| := by
      have h := abs_sub_abs_le_abs_sub ((k : ℝ) * P) (-x)
      rw [abs_neg, sub_neg_eq_add] at h
      have h2 : |(k : ℝ) * P| = |(k : ℝ)| * P := by rw [abs_mul, abs_of_pos hP]
      rw [h2] at h
      have h3 : |(k : ℝ) * P + x| = |x + (k : ℝ) * P| := by rw [add_comm]
      rw [h3] at h
      linarith [hxb]
    linarith
  have hfin : (volume (Ioc (0 : ℝ) P)) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hmeas : ∀ k : ℤ, AEStronglyMeasurable (g k) (volume.restrict (Ioc (0 : ℝ) P)) := by
    intro k
    exact ((measurable_putnamTwist a (d * n)).comp (by fun_prop)).aestronglyMeasurable
  have hint : ∀ k : ℤ, IntegrableOn (g k) (Ioc (0 : ℝ) P) := by
    intro k
    refine Integrable.mono' (g := fun _ : ℝ => Real.exp (P / 2) * Real.exp (-(P / 2 * |(k : ℝ)|)))
      ?_ (hmeas k) ?_
    · exact integrableOn_const hfin
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun x hx => ?_)
      exact hgnorm k x hx
  have hsum : Summable fun k : ℤ => ∫ x in Ioc (0 : ℝ) P, ‖g k x‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun x => norm_nonneg _)
      (fun k => ?_) (((summable_exp_neg_abs_int (r := P / 2) (by positivity)).mul_left
        (Real.exp (P / 2))).mul_left P)
    calc (∫ x in Ioc (0 : ℝ) P, ‖g k x‖)
        ≤ ∫ _x in Ioc (0 : ℝ) P, Real.exp (P / 2) * Real.exp (-(P / 2 * |(k : ℝ)|)) := by
          refine setIntegral_mono_on (hint k).norm (integrableOn_const hfin) measurableSet_Ioc ?_
          intro x hx
          exact hgnorm k x hx
      _ = P * (Real.exp (P / 2) * Real.exp (-(P / 2 * |(k : ℝ)|))) := by
          rw [setIntegral_const, Real.volume_real_Ioc_of_le hP.le, smul_eq_mul]
          ring
  have hhassum := hasSum_integral_of_summable_integral_norm hint hsum
  have hpoint : ∀ x : ℝ, putnamPeriodization a d x * Complex.exp (-((d * n : ℝ) : ℂ) * I * (x : ℂ))
      = ∑' k : ℤ, g k x := by
    intro x
    rw [putnamPeriodization, ← tsum_mul_right]
    refine tsum_congr fun k => ?_
    rw [hgdef]
    simp only
    rw [putnamTwist_shift hd n k x]
  rw [setIntegral_congr_fun measurableSet_Ioc (fun x _ => hpoint x)]
  rw [← hhassum.tsum_eq]
  have hshift : ∀ k : ℤ, (∫ x in Ioc (0 : ℝ) P, g k x)
      = ∫ y in Ioc ((k : ℝ) * P) (((k : ℝ) + 1) * P), putnamTwist a (d * n) y := by
    intro k
    have h1 : (∫ x in Ioc (0 : ℝ) P, g k x) = ∫ x in (0 : ℝ)..P, g k x := by
      rw [intervalIntegral.integral_of_le hP.le]
    have h2 : (∫ y in Ioc ((k : ℝ) * P) (((k : ℝ) + 1) * P), putnamTwist a (d * n) y)
        = ∫ y in ((k : ℝ) * P)..(((k : ℝ) + 1) * P), putnamTwist a (d * n) y := by
      rw [intervalIntegral.integral_of_le (by nlinarith [hP])]
    have h3 : (∫ x in (0 : ℝ)..P, putnamTwist a (d * n) (x + (k : ℝ) * P))
        = ∫ x in (0 + (k : ℝ) * P)..(P + (k : ℝ) * P), putnamTwist a (d * n) x :=
      intervalIntegral.integral_comp_add_right (putnamTwist a (d * n)) ((k : ℝ) * P)
    rw [h1, h2]
    have hgk : (∫ x in (0 : ℝ)..P, g k x)
        = ∫ x in (0 : ℝ)..P, putnamTwist a (d * n) (x + (k : ℝ) * P) := rfl
    rw [hgk, h3]
    congr 1 <;> ring
  rw [tsum_congr hshift]
  have hunion := iUnion_Ioc_period (P := P) hP
  have hdisj := pairwise_disjoint_Ioc_period (P := P) hP
  have hIU := MeasureTheory.integral_iUnion (μ := (volume : Measure ℝ))
    (f := putnamTwist a (d * n))
    (s := fun k : ℤ => Ioc ((k : ℝ) * P) (((k : ℝ) + 1) * P))
    (fun k => measurableSet_Ioc) hdisj
    (by rw [hunion, integrableOn_univ]; exact integrable_putnamTwist a (d * n))
  rw [hunion] at hIU
  rw [← hIU, MeasureTheory.setIntegral_univ]
  have hzeta := integral_putnamTwist a (d * n)
  rw [hzeta]

end RHTower

end
