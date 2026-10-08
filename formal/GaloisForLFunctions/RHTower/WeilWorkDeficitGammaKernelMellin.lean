import GaloisForLFunctions.RHTower.WeilWorkDeficitGammaKernelJets
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.MellinInversion

/-!
# Mellin integration and inversion of the actual reciprocal-Gamma kernel

Absolute admission is proved separately on each monomial piece. Their
Mellin integral is the literal rational symbol on the line of real part two.
The zeroth residue cancellation gives an integrable vertical bound, and
matching endpoint values give continuity. Mellin inversion then recovers
the actual piecewise kernel at every positive argument.

This does not yet prove the cosine-kernel/Xi-density inversion, the C23
resonance asymptotic, or the WP06 spectral-deficit bound.
-/

noncomputable section
open Complex MeasureTheory Set
open scoped BigOperators
namespace RHTower.WeilWorkDeficitGamma

/-- Literal piecewise kernel whose endpoint jets are already proved. -/
def kernel (N : ℕ) (x : ℝ) : ℂ :=
  if x ≤ 1 then kernelInner N x else kernelOuter N x

private theorem weighted_zpow (s : ℂ) (m : ℤ) {x : ℝ} (hx : 0 < x) :
    (x:ℂ)^(-s)*(x:ℂ)^m = (x:ℂ)^((m:ℂ)-s) := by
  rw [← Complex.cpow_intCast, ← Complex.cpow_add _ _ (by exact_mod_cast hx.ne')]
  congr 1
  ring

private theorem inner_factor (N : ℕ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (x:ℂ)^(-s)*kernelInner N x =
      -∑ j : Fin (N+3), residue N (Sum.inr j)*(x:ℂ)^(2*(j:ℂ)+2-s) := by
  simp only [kernelInner, mul_neg, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_left_comm, weighted_zpow s _ hx]
  congr 2
  push_cast
  ring

private theorem outer_factor (N : ℕ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (x:ℂ)^(-s)*kernelOuter N x =
      ∑ j : Fin (N+3), residue N (Sum.inl j)*(x:ℂ)^(-2*(j:ℂ)-3-s) := by
  simp only [kernelOuter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_left_comm, weighted_zpow s _ hx]
  congr 2
  push_cast
  ring

private theorem inner_power_integrable (s : ℂ) (hs : s.re < 3) (j : ℕ) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(2*(j:ℂ)+2-s)) (Ioc 0 1) := by
  apply (intervalIntegral.intervalIntegrable_cpow' ?_).1
  have hj : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
  norm_num
  linarith

private theorem outer_power_integrable (s : ℂ) (hs : -2 < s.re) (j : ℕ) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(-2*(j:ℂ)-3-s)) (Ioi 1) := by
  apply integrableOn_Ioi_cpow_of_lt ?_ zero_lt_one
  have hj : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
  norm_num
  linarith

private theorem inner_integrable (N : ℕ) (s : ℂ) (hs : s.re < 3) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(-s)*kernelInner N x) (Ioc 0 1) := by
  have h := (integrable_finsetSum Finset.univ (fun j _ =>
    (inner_power_integrable s hs (j : Fin (N+3))).const_mul (residue N (Sum.inr j)))).neg
  exact IntegrableOn.congr_fun h (fun x hx => (inner_factor N s hx.1).symm) measurableSet_Ioc

private theorem outer_integrable (N : ℕ) (s : ℂ) (hs : -2 < s.re) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(-s)*kernelOuter N x) (Ioi 1) := by
  have h := integrable_finsetSum Finset.univ (fun j _ =>
    (outer_power_integrable s hs (j : Fin (N+3))).const_mul (residue N (Sum.inl j)))
  exact IntegrableOn.congr_fun h (fun x hx => (outer_factor N s (zero_lt_one.trans hx)).symm)
    measurableSet_Ioi

private theorem kernel_left (N : ℕ) (s : ℂ) :
    EqOn (fun x : ℝ => (x:ℂ)^(-s)*kernelInner N x)
      (fun x => (x:ℂ)^(-s)*kernel N x) (Ioc 0 1) := by
  intro x hx
  simp [kernel, hx.2]

private theorem kernel_right (N : ℕ) (s : ℂ) :
    EqOn (fun x : ℝ => (x:ℂ)^(-s)*kernelOuter N x)
      (fun x => (x:ℂ)^(-s)*kernel N x) (Ioi 1) := by
  intro x hx
  simp [kernel, not_le.mpr (show 1 < x from hx)]

private theorem kernel_weighted_integrable (N : ℕ) (s : ℂ)
    (hl : -2 < s.re) (hr : s.re < 3) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(-s)*kernel N x) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0:ℝ) ≤ 1 by norm_num), integrableOn_union]
  exact ⟨(inner_integrable N s hr).congr_fun (kernel_left N s) measurableSet_Ioc,
    (outer_integrable N s hl).congr_fun (kernel_right N s) measurableSet_Ioi⟩

private theorem inner_power_integral (s : ℂ) (hs : s.re < 3) (j : ℕ) :
    (∫ x in Ioc (0:ℝ) 1, (x:ℂ)^(2*(j:ℂ)+2-s)) =
      1/(2*(j:ℂ)+3-s) := by
  have hr : -1 < (2*(j:ℂ)+2-s).re := by
    have hj : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
    norm_num
    linarith
  have hn : 2*(j:ℂ)+2-s+1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
    linarith
  rw [← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num),
    integral_cpow (Or.inl hr)]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, one_cpow, Complex.zero_cpow hn,
    sub_zero]
  congr 1
  ring

private theorem outer_power_integral (s : ℂ) (hs : -2 < s.re) (j : ℕ) :
    (∫ x in Ioi (1:ℝ), (x:ℂ)^(-2*(j:ℂ)-3-s)) =
      -1/(-2*(j:ℂ)-2-s) := by
  have hr : (-2*(j:ℂ)-3-s).re < -1 := by
    have hj : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
    norm_num
    linarith
  rw [integral_Ioi_cpow_of_lt hr zero_lt_one]
  simp only [Complex.ofReal_one, one_cpow]
  congr 1
  ring

private theorem inner_integral (N : ℕ) (s : ℂ) (hs : s.re < 3) :
    (∫ x in Ioc (0:ℝ) 1, (x:ℂ)^(-s)*kernelInner N x) =
      ∑ j : Fin (N+3), residue N (Sum.inr j)/(s-pole N (Sum.inr j)) := by
  rw [setIntegral_congr_fun measurableSet_Ioc (fun x hx => inner_factor N s hx.1),
    integral_neg, integral_finsetSum _ (fun (j : Fin (N+3)) _ =>
      (inner_power_integrable s hs j).const_mul (residue N (Sum.inr j))),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, inner_power_integral s hs]
  simp only [pole]
  rw [show 2*(j:ℂ)+3-s = -(s-(2*(j:ℂ)+3)) by ring, div_neg]
  ring

private theorem outer_integral (N : ℕ) (s : ℂ) (hs : -2 < s.re) :
    (∫ x in Ioi (1:ℝ), (x:ℂ)^(-s)*kernelOuter N x) =
      ∑ j : Fin (N+3), residue N (Sum.inl j)/(s-pole N (Sum.inl j)) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => outer_factor N s
    (zero_lt_one.trans hx)), integral_finsetSum _ (fun (j : Fin (N+3)) _ =>
      (outer_power_integrable s hs j).const_mul (residue N (Sum.inl j)))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, outer_power_integral s hs]
  simp only [pole]
  rw [show -2*(j:ℂ)-2-s = -(s-(-2*(j:ℂ)-2)) by ring, div_neg]
  ring

private theorem kernel_weighted_integral (N : ℕ) (s : ℂ)
    (hl : -2 < s.re) (hr : s.re < 3) :
    (∫ x in Ioi (0:ℝ), (x:ℂ)^(-s)*kernel N x) =
      ∑ i : PoleIndex N, residue N i/(s-pole N i) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0:ℝ) ≤ 1 by norm_num),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      ((inner_integrable N s hr).congr_fun (kernel_left N s) measurableSet_Ioc)
      ((outer_integrable N s hl).congr_fun (kernel_right N s) measurableSet_Ioi)]
  rw [← setIntegral_congr_fun measurableSet_Ioc (kernel_left N s),
    ← setIntegral_congr_fun measurableSet_Ioi (kernel_right N s),
    inner_integral N s hr, outer_integral N s hl, Fintype.sum_sum_type, add_comm]

/-- Absolute weighted admission on the complete pole-free strip. -/
theorem integrable_kernel_strip (N : ℕ)
    (s : {s : ℂ // -2 < s.re ∧ s.re < 3}) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(-(s:ℂ))*kernel N x) (Ioi 0) :=
  kernel_weighted_integrable N s s.property.1 s.property.2

/-- Actual weighted Mellin integral on the complete pole-free strip. -/
theorem kernel_mellin_strip (N : ℕ)
    (s : {s : ℂ // -2 < s.re ∧ s.re < 3}) :
    (∫ x in Ioi (0:ℝ), (x:ℂ)^(-(s:ℂ))*kernel N x) =
      (s:ℂ)*((s:ℂ)-1)/clearingProduct (N+3) s := by
  rw [kernel_weighted_integral N s s.property.1 s.property.2,
    rationalSymbol_strip]

/-- The actual kernel has zero total mass, permitting cosine subtraction. -/
theorem integral_kernel_zero (N : ℕ) :
    (∫ x in Ioi (0:ℝ), kernel N x) = 0 := by
  simpa using kernel_mellin_strip N ⟨0, by norm_num⟩

/-- The actual piecewise kernel is absolutely integrable. -/
theorem integrable_kernel (N : ℕ) : IntegrableOn (kernel N) (Ioi 0) := by
  simpa using kernel_weighted_integrable N 0 (by norm_num) (by norm_num)

/-- The actual line-two Mellin integral is absolutely admitted at every height. -/
theorem integrable_kernel_mellin_two (N : ℕ) (t : ℝ) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(-(2+(t:ℂ)*I))*kernel N x) (Ioi 0) :=
  kernel_weighted_integrable N _ (by norm_num) (by norm_num)

/-- Exact rational Mellin transform of the literal kernel on the inversion line. -/
theorem kernel_mellin_two (N : ℕ) (t : ℝ) :
    (∫ x in Ioi (0:ℝ), (x:ℂ)^(-(2+(t:ℂ)*I))*kernel N x) =
      (2+(t:ℂ)*I)*(1+(t:ℂ)*I)/clearingProduct (N+3) (2+(t:ℂ)*I) := by
  rw [kernel_weighted_integral N _ (by norm_num) (by norm_num), rationalSymbol_two]

/-- Continuity of the actual piecewise kernel includes its matching endpoint. -/
theorem continuous_kernel (N : ℕ) : Continuous (kernel N) := by
  have hi : Continuous (fun x : ℝ => kernelInner N x) := by
    unfold kernelInner
    apply Continuous.neg
    apply continuous_finsetSum
    intro j hj
    apply continuous_const.mul
    exact Complex.continuous_ofReal.zpow₀ _ (fun _ => Or.inr (by omega))
  have ho : ContinuousOn (fun x : ℝ => kernelOuter N x) (Ici 1) := by
    unfold kernelOuter
    apply continuousOn_finsetSum
    intro j hj
    apply continuousOn_const.mul
    apply Complex.continuous_ofReal.continuousOn.zpow₀
    intro x hx
    left
    exact_mod_cast (show x ≠ 0 by have : 1 ≤ x := hx; linarith)
  unfold kernel
  apply continuous_if
  · intro x hx
    have hx1 : x = 1 := by simpa only [show {x : ℝ | x ≤ 1} = Iic 1 by rfl,
      frontier_Iic, mem_singleton_iff] using hx
    subst x
    simpa only [iteratedDeriv_zero, Complex.ofReal_one] using
      (kernel_endpoint_match N ⟨0, by omega⟩).symm
  · exact hi.continuousOn
  · simpa only [show {x : ℝ | ¬x ≤ 1} = Ioi 1 by ext x; simp, closure_Ioi] using ho

private theorem line_den_norm (N : ℕ) (t : ℝ) (i : PoleIndex N) :
    Real.sqrt (1+t^2) ≤ ‖2+(t:ℂ)*I-pole N i‖ := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨norm_nonneg _, ?_⟩
  rw [Complex.sq_norm, Complex.normSq_apply]
  cases i with
  | inl j =>
    norm_num [pole]
    have hj : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
    nlinarith [sq_nonneg (j:ℝ)]
  | inr j =>
    norm_num [pole]
    have hj : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
    nlinarith [sq_nonneg (j:ℝ)]

private theorem line_base_norm (t : ℝ) :
    Real.sqrt (1+t^2) ≤ ‖2+(t:ℂ)*I‖ := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨norm_nonneg _, ?_⟩
  rw [Complex.sq_norm, Complex.normSq_apply]
  norm_num
  nlinarith

private theorem line_base_ne (t : ℝ) : 2+(t:ℂ)*I ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num at hr

private theorem line_pole_ne (N : ℕ) (t : ℝ) (i : PoleIndex N) :
    2+(t:ℂ)*I-pole N i ≠ 0 := by
  apply norm_pos_iff.mp
  exact lt_of_lt_of_le (Real.sqrt_pos.mpr (by positivity)) (line_den_norm N t i)

private theorem residue_sum_zero (N : ℕ) : ∑ i : PoleIndex N, residue N i = 0 := by
  simpa [boundaryJet] using boundaryJet_lower N ⟨0, by omega⟩

private theorem rational_decay (N : ℕ) (t : ℝ) :
    ‖(2+(t:ℂ)*I)*(1+(t:ℂ)*I)/clearingProduct (N+3) (2+(t:ℂ)*I)‖ ≤
      (∑ i : PoleIndex N, ‖residue N i*pole N i‖)*(1+t^2)⁻¹ := by
  let s : ℂ := 2+(t:ℂ)*I
  have hs : s ≠ 0 := line_base_ne t
  have hsplit : (∑ i : PoleIndex N, residue N i/(s-pole N i)) =
      ∑ i : PoleIndex N, (residue N i*pole N i)/(s*(s-pole N i)) := by
    calc
      _ = ∑ i : PoleIndex N, (residue N i/(s-pole N i)-residue N i/s) := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_div, residue_sum_zero, zero_div, sub_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        have hp := line_pole_ne N t i
        change s-pole N i ≠ 0 at hp
        field_simp [hs, hp]
        ring
  rw [rationalSymbol_two, hsplit]
  calc
    _ ≤ ∑ i : PoleIndex N, ‖residue N i*pole N i/(s*(s-pole N i))‖ := norm_sum_le _ _
    _ ≤ ∑ i : PoleIndex N, ‖residue N i*pole N i‖*(1+t^2)⁻¹ := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [norm_div, norm_mul]
      rw [← div_eq_mul_inv]
      have hd : 1+t^2 ≤ ‖s‖*‖s-pole N i‖ := by
        calc
          _ = Real.sqrt (1+t^2)*Real.sqrt (1+t^2) := (Real.mul_self_sqrt (by positivity)).symm
          _ ≤ _ := mul_le_mul (line_base_norm t) (line_den_norm N t i)
            (Real.sqrt_nonneg _) (norm_nonneg _)
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hd
    _ = _ := by rw [Finset.sum_mul]

/-- Absolute vertical admission follows from the actual zero residue sum. -/
theorem integrable_rational_two (N : ℕ) :
    Integrable (fun t : ℝ =>
      (2+(t:ℂ)*I)*(1+(t:ℂ)*I)/clearingProduct (N+3) (2+(t:ℂ)*I)) := by
  have he : (fun t : ℝ => (2+(t:ℂ)*I)*(1+(t:ℂ)*I)/clearingProduct (N+3) (2+(t:ℂ)*I)) =
      (fun t : ℝ => ∑ i : PoleIndex N, residue N i/(2+(t:ℂ)*I-pole N i)) := by
    funext t
    exact rationalSymbol_two N t
  have hc : Continuous (fun t : ℝ =>
      (2+(t:ℂ)*I)*(1+(t:ℂ)*I)/clearingProduct (N+3) (2+(t:ℂ)*I)) := by
    rw [he]
    apply continuous_finsetSum
    intro i hi
    exact Continuous.div₀ continuous_const (by fun_prop) (fun t => line_pole_ne N t i)
  refine (integrable_inv_one_add_sq.const_mul
    (∑ i : PoleIndex N, ‖residue N i*pole N i‖)).mono' hc.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (rational_decay N)

private theorem kernel_mellin_line (N : ℕ) (t : ℝ) :
    mellin (kernel N) (-1+(t:ℂ)*I) =
      (2-(t:ℂ)*I)*(1-(t:ℂ)*I)/clearingProduct (N+3) (2-(t:ℂ)*I) := by
  have h := kernel_mellin_two N (-t)
  simp only [Complex.ofReal_neg, neg_mul] at h
  rw [mellin]
  simp only [smul_eq_mul]
  convert h using 1
  · congr 1
    funext x
    congr 2
    ring
  · congr 2

private theorem kernel_mellin_convergent (N : ℕ) : MellinConvergent (kernel N) (-1) := by
  simpa only [MellinConvergent, smul_eq_mul, show (-1:ℂ)-1 = -(2:ℂ) by ring] using
    kernel_weighted_integrable N 2 (by norm_num) (by norm_num)

private theorem kernel_vertical_integrable (N : ℕ) :
    VerticalIntegrable (mellin (kernel N)) (-1) := by
  simp only [VerticalIntegrable, Complex.ofReal_neg, Complex.ofReal_one]
  simp_rw [kernel_mellin_line]
  simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using
    (integrable_rational_two N).comp_neg

/-- Inverse Mellin recovery of the literal kernel at every positive argument. -/
theorem kernel_mellin_inversion (N : ℕ) (x : Ioi (0:ℝ)) :
    mellinInv (-1) (fun s : ℂ =>
      (1-s)*(-s)/clearingProduct (N+3) (1-s)) x = kernel N x := by
  calc
    _ = mellinInv (-1) (mellin (kernel N)) x := by
      simp only [mellinInv, Complex.ofReal_neg, Complex.ofReal_one]
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by
        dsimp only
        rw [kernel_mellin_line]
        rw [show (1:ℂ)-(-1+(t:ℂ)*I) = 2-(t:ℂ)*I by ring,
          show -(-1+(t:ℂ)*I) = 1-(t:ℂ)*I by ring])
    _ = _ := by
      apply mellinInv_mellin_eq
      · exact x.property
      · simpa only [Complex.ofReal_neg, Complex.ofReal_one] using kernel_mellin_convergent N
      · exact kernel_vertical_integrable N
      · exact (continuous_kernel N).continuousAt

end RHTower.WeilWorkDeficitGamma
