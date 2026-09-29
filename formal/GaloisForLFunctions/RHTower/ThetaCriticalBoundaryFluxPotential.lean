import GaloisForLFunctions.RHTower.ThetaCriticalBoundaryMellinCharge

/-!
# Flux potentials of theta sources and the boundary charge at the cusp

For an index set `A ⊆ ℕ` the flux potential `H_A(x) = Σ_{n∈A} 2πn² e^{3x} e^{−πn² e^{2x}}` is
nonnegative, bounded by the all-integer potential `H ≤ 1/2`, differentiable with
`H_A' = −e^{x/2} S_A`, and equal to the right-tail critical mass `∫_x^∞ e^{t/2} S_A`.  At the
physical end `H_A → 0` for every `A`.  At the cusp `H_A → 0` whenever `Σ_{n∈A} 1/n < ∞`, while the
completed potential tends to `1/2`: completion changes the left boundary condition of the same
exact differential law.

For every sequence of index sets `A_j` with `Σ_{n∈A_j} 1/n < ∞` exhausting the positive integers
(in particular the finite-prime stages):

* the escaped charge `∫_{−∞}^{−R} e^{x/2}(k − S_{A_j}) → 1/2` for every `R`;
* for every bounded differentiable test `ψ` with integrable derivative, `ψ(−∞)` exists and
  `∫ ψ e^{x/2} S_{A_j} → ∫ ψ e^{x/2} k − ψ(−∞)/2`.

The proof integrates by parts against the potentials and passes to the limit by dominated
convergence, using `0 ≤ H_{A_j} ≤ H ≤ 1/2` and pointwise convergence `H_{A_j} → H`.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## Flux atoms -/

/-- The flux atom `2πn² e^{3x} e^{−πn² e^{2x}}`. -/
def thetaFluxTerm (x : ℝ) (n : ℕ) : ℝ :=
  2 * (Real.pi * (n : ℝ) ^ 2) * rateFlux (Real.pi * (n : ℝ) ^ 2) x

theorem thetaFluxTerm_nonneg (x : ℝ) (n : ℕ) : 0 ≤ thetaFluxTerm x n := by
  unfold thetaFluxTerm rateFlux; positivity

theorem thetaFluxTerm_zero (x : ℝ) : thetaFluxTerm x 0 = 0 := by simp [thetaFluxTerm]

/-- **Exact flux law for one atom.**  `(d/dx) [2πn² e^{3x} e^{−πn²e^{2x}}] = −e^{x/2} a_n(x)`. -/
theorem hasDerivAt_thetaFluxTerm (x : ℝ) (n : ℕ) :
    HasDerivAt (fun y => thetaFluxTerm y n)
      (-(Real.exp ((1 / 2 : ℝ) * x) * thetaCuspSourceTerm x n)) x := by
  have h := (hasDerivAt_rateFlux (Real.pi * (n : ℝ) ^ 2) x).const_mul (2 * (Real.pi * (n : ℝ) ^ 2))
  refine h.congr_deriv ?_
  rw [thetaCuspSourceTerm_eq_rateAtom, show (1 / 2 : ℝ) * x = x / 2 by ring, exp_half_mul_rateAtom]
  ring

/-- Scaling form of a flux atom: `n^{-1}` times the profile `2π t³ e^{−πt²}` at `t = n e^x`. -/
theorem thetaFluxTerm_eq_inv_mul {n : ℕ} (hn : 0 < n) (x : ℝ) :
    thetaFluxTerm x n = (n : ℝ)⁻¹ * (2 * Real.pi * ((n : ℝ) * Real.exp x) ^ 3 *
      Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ 2)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h3 : Real.exp x ^ 3 = Real.exp (3 * x) := by rw [← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp x ^ 2 = Real.exp (2 * x) := by rw [← Real.exp_nat_mul]; norm_num
  simp only [thetaFluxTerm, rateFlux, mul_pow, h3, h2]
  rw [show -Real.pi * ((n : ℝ) ^ 2 * Real.exp (2 * x)) = -(Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)) by
    ring]
  field_simp

theorem summable_thetaFluxTerm (x : ℝ) : Summable (thetaFluxTerm x) := by
  have hsigma : 0 < Real.pi * Real.exp (2 * x) := mul_pos Real.pi_pos (Real.exp_pos _)
  refine ((summable_pow_mul_exp_neg_nat_sq 2 hsigma).mul_left
    (2 * Real.pi * Real.exp (3 * x))).congr fun n => ?_
  simp only [thetaFluxTerm, rateFlux]
  rw [show -(Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)) = -(Real.pi * Real.exp (2 * x)) * (n : ℝ) ^ 2 by
    ring]
  ring

theorem tendsto_thetaFluxTerm_atTop (n : ℕ) :
    Tendsto (fun x => thetaFluxTerm x n) atTop (𝓝 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [thetaFluxTerm_zero]; exact tendsto_const_nhds
  · have hlam : 0 < Real.pi * (n : ℝ) ^ 2 := by positivity
    simpa only [thetaFluxTerm, mul_zero] using
      (tendsto_rateFlux_atTop hlam).const_mul (2 * (Real.pi * (n : ℝ) ^ 2))

/-- On the physical half-line each flux atom decreases. -/
theorem thetaFluxTerm_le_zero_of_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    thetaFluxTerm x n ≤ thetaFluxTerm 0 n := by
  have hanti : AntitoneOn (fun y => thetaFluxTerm y n) (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun y _ => (hasDerivAt_thetaFluxTerm y n).continuousAt.continuousWithinAt)
      (fun y _ => (hasDerivAt_thetaFluxTerm y n).differentiableAt.differentiableWithinAt)
      fun y hy => ?_
    rw [interior_Ici] at hy
    rw [(hasDerivAt_thetaFluxTerm y n).deriv, neg_nonpos]
    exact mul_nonneg (Real.exp_pos _).le (thetaCuspSourceTerm_nonneg_of_pos hy n)
  exact hanti self_mem_Ici hx hx

/-! ## Flux potentials of index sets -/

/-- The flux potential `H_A(x) = Σ_{n∈A} 2πn² e^{3x} e^{−πn² e^{2x}}`. -/
def indexFluxPotential (A : Set ℕ) (x : ℝ) : ℝ :=
  ∑' n : A, thetaFluxTerm x n

theorem indexFluxPotential_nonneg (A : Set ℕ) (x : ℝ) : 0 ≤ indexFluxPotential A x :=
  tsum_nonneg fun n => thetaFluxTerm_nonneg x n

theorem indexFluxPotential_le_univ (A : Set ℕ) (x : ℝ) :
    indexFluxPotential A x ≤ indexFluxPotential univ x := by
  rw [indexFluxPotential, indexFluxPotential, tsum_univ (f := fun n => thetaFluxTerm x n)]
  exact (summable_thetaFluxTerm x).tsum_subtype_le _ A fun n => thetaFluxTerm_nonneg x n

/-- **Termwise flux law.**  For every index set, `H_A' = −e^{x/2} S_A`. -/
theorem hasDerivAt_indexFluxPotential (A : Set ℕ) (x : ℝ) :
    HasDerivAt (indexFluxPotential A)
      (-(Real.exp ((1 / 2 : ℝ) * x) * indexThetaSource A x)) x := by
  set R : ℝ := |x| + 1
  have hmem : x ∈ Ioo (-R) R := ⟨by have := neg_abs_le x; linarith, by
    have := le_abs_self x; linarith⟩
  have hu : Summable (fun n : A => Real.exp (R / 2) * thetaCuspSourceMajorant R n) :=
    ((summable_thetaCuspSourceMajorant R).subtype A).mul_left _
  have h := hasDerivAt_tsum_of_isPreconnected (g := fun (n : A) y => thetaFluxTerm y n)
    (g' := fun (n : A) y => -(Real.exp ((1 / 2 : ℝ) * y) * thetaCuspSourceTerm y n)) hu isOpen_Ioo
    isPreconnected_Ioo (fun n y _ => hasDerivAt_thetaFluxTerm y n) (fun n y hy => ?_) hmem
    ((summable_thetaFluxTerm x).subtype A) hmem
  · refine h.congr_deriv ?_
    rw [tsum_neg, indexThetaSource, ← tsum_mul_left]
  · rw [norm_neg, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    exact mul_le_mul (Real.exp_le_exp.2 (by linarith [hy.2]))
      (abs_thetaCuspSourceTerm_le_majorant ⟨hy.1.le, hy.2.le⟩ n) (abs_nonneg _) (Real.exp_pos _).le

theorem continuous_indexFluxPotential (A : Set ℕ) : Continuous (indexFluxPotential A) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_indexFluxPotential A x).continuousAt

/-- `H_A → 0` at the physical end, for every index set. -/
theorem tendsto_indexFluxPotential_atTop (A : Set ℕ) :
    Tendsto (indexFluxPotential A) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (f := fun x (n : A) => thetaFluxTerm x n)
    (g := fun _ => (0 : ℝ)) (bound := fun n : A => thetaFluxTerm 0 n)
    ((summable_thetaFluxTerm 0).subtype A) (fun n => tendsto_thetaFluxTerm_atTop n)
    (by
      filter_upwards [eventually_ge_atTop 0] with x hx n
      rw [Real.norm_eq_abs, abs_of_nonneg (thetaFluxTerm_nonneg x n)]
      exact thetaFluxTerm_le_zero_of_nonneg hx n)
  show Tendsto (fun x => ∑' n : A, thetaFluxTerm x n) atTop (𝓝 0)
  simpa using h

/-! ## An integrable envelope on right half-lines -/

theorem tsum_abs_thetaCuspSourceTerm_le {R t : ℝ} (ht : -R ≤ t) :
    ∑' n, |thetaCuspSourceTerm t n| ≤
      thetaCuspFullSource t + (Icc (-R) R).indicator (fun _ => ∑' n, thetaCuspSourceMajorant R n) t := by
  rcases lt_or_ge 0 t with h0 | h0
  · have hind : 0 ≤ (Icc (-R) R).indicator (fun _ => ∑' n, thetaCuspSourceMajorant R n) t :=
      Set.indicator_nonneg (fun _ _ => tsum_nonneg (thetaCuspSourceMajorant_nonneg R)) t
    have heq : ∑' n, |thetaCuspSourceTerm t n| = thetaCuspFullSource t := by
      rw [thetaCuspFullSource]
      exact tsum_congr fun n => abs_of_nonneg (thetaCuspSourceTerm_nonneg_of_pos h0 n)
    linarith
  · have hmem : t ∈ Icc (-R) R := ⟨ht, by linarith⟩
    rw [Set.indicator_of_mem hmem]
    have := (summable_thetaCuspSourceTerm t).abs.tsum_le_tsum
      (fun n => abs_thetaCuspSourceTerm_le_majorant hmem n) (summable_thetaCuspSourceMajorant R)
    linarith [thetaCuspFullSource_pos_all t]

/-- The envelope `e^{t/2}(k(t) + 1_{[−R,R]}(t) Σ M_R)` dominating every index-set source on
`t ≥ −R`. -/
def thetaSourceEnvelope (R t : ℝ) : ℝ :=
  Real.exp ((1 / 2 : ℝ) * t) *
    (thetaCuspFullSource t + (Icc (-R) R).indicator (fun _ => ∑' n, thetaCuspSourceMajorant R n) t)

theorem integrable_thetaSourceEnvelope (R : ℝ) : Integrable (thetaSourceEnvelope R) := by
  have h1 : Integrable (fun t : ℝ => Real.exp ((1 / 2 : ℝ) * t) * thetaCuspFullSource t) :=
    integrable_exp_mul_thetaCuspFullSource_of_abs_lt_one (by norm_num [abs_of_pos])
  have h2 : Integrable (fun t : ℝ => Real.exp ((1 / 2 : ℝ) * t) *
      (Icc (-R) R).indicator (fun _ => ∑' n, thetaCuspSourceMajorant R n) t) := by
    have : IntegrableOn (fun t : ℝ => Real.exp ((1 / 2 : ℝ) * t) * ∑' n, thetaCuspSourceMajorant R n)
        (Icc (-R) R) := (by fun_prop : Continuous fun t : ℝ =>
          Real.exp ((1 / 2 : ℝ) * t) * ∑' n, thetaCuspSourceMajorant R n).integrableOn_Icc
    refine (this.integrable_indicator measurableSet_Icc).congr (ae_of_all _ fun t => ?_)
    by_cases ht : t ∈ Icc (-R) R <;> simp [ht]
  exact (h1.add h2).congr (ae_of_all _ fun t => by
    simp only [thetaSourceEnvelope, Pi.add_apply]; ring)

theorem abs_exp_half_mul_indexThetaSource_le (A : Set ℕ) {R t : ℝ} (ht : -R ≤ t) :
    |Real.exp ((1 / 2 : ℝ) * t) * indexThetaSource A t| ≤ thetaSourceEnvelope R t := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _), thetaSourceEnvelope]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  refine le_trans ?_ (tsum_abs_thetaCuspSourceTerm_le ht)
  have hs : Summable (fun n : A => ‖thetaCuspSourceTerm t (n : ℕ)‖) :=
    (summable_thetaCuspSourceTerm t).norm.subtype A
  have h1 : ‖indexThetaSource A t‖ ≤ ∑' n : A, ‖thetaCuspSourceTerm t (n : ℕ)‖ :=
    norm_tsum_le_tsum_norm hs
  have h2 : ∑' n : A, ‖thetaCuspSourceTerm t (n : ℕ)‖ ≤ ∑' n, ‖thetaCuspSourceTerm t n‖ :=
    (summable_thetaCuspSourceTerm t).norm.tsum_subtype_le (fun n => ‖thetaCuspSourceTerm t n‖) A
      fun n => norm_nonneg _
  simp only [Real.norm_eq_abs] at h1 h2
  exact h1.trans h2

theorem continuous_indexThetaSource (A : Set ℕ) : Continuous (indexThetaSource A) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  set R : ℝ := |x| + 1
  have hmem : x ∈ Ioo (-R) R := ⟨by have := neg_abs_le x; linarith, by
    have := le_abs_self x; linarith⟩
  have h := continuousOn_tsum (f := fun (n : A) y => thetaCuspSourceTerm y n)
    (s := Ioo (-R) R) (fun n => (continuous_thetaCuspSourceTerm n).continuousOn)
    ((summable_thetaCuspSourceMajorant R).subtype A)
    (fun n y hy => abs_thetaCuspSourceTerm_le_majorant ⟨hy.1.le, hy.2.le⟩ n)
  exact h.continuousAt (isOpen_Ioo.mem_nhds hmem)

theorem integrableOn_exp_half_mul_indexThetaSource_Ioi (A : Set ℕ) (a : ℝ) :
    IntegrableOn (fun t => Real.exp ((1 / 2 : ℝ) * t) * indexThetaSource A t) (Ioi a) := by
  refine ((integrable_thetaSourceEnvelope (-a)).integrableOn).mono'
    ((by fun_prop : Continuous fun t : ℝ => Real.exp ((1 / 2 : ℝ) * t)).mul
      (continuous_indexThetaSource A)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs]
  exact abs_exp_half_mul_indexThetaSource_le A (by simp only [neg_neg]; exact (mem_Ioi.1 ht).le)

/-- **The flux potential is the right-tail critical mass.**  `H_A(x) = ∫_x^∞ e^{t/2} S_A(t) dt`
for every index set. -/
theorem indexFluxPotential_eq_setIntegral (A : Set ℕ) (x : ℝ) :
    indexFluxPotential A x = ∫ t in Ioi x, Real.exp ((1 / 2 : ℝ) * t) * indexThetaSource A t := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (continuous_indexFluxPotential A).continuousWithinAt
    (fun y _ => hasDerivAt_indexFluxPotential A y)
    (integrableOn_exp_half_mul_indexThetaSource_Ioi A x).neg (tendsto_indexFluxPotential_atTop A)
  rw [integral_neg, zero_sub, neg_inj] at h
  exact h.symm

/-! ## Boundary values of the flux potentials -/

theorem tendsto_setIntegral_Ioi_atBot_real {g : ℝ → ℝ} (hg : Integrable g) :
    Tendsto (fun x => ∫ t in Ioi x, g t) atBot (𝓝 (∫ t, g t)) := by
  have h := tendsto_integral_filter_of_dominated_convergence (l := (atBot : Filter ℝ))
    (F := fun x t => (Ioi x).indicator g t) (f := g) (fun t => ‖g t‖)
    (Eventually.of_forall fun x => hg.aestronglyMeasurable.indicator measurableSet_Ioi)
    (Eventually.of_forall fun x => ae_of_all _ fun t => norm_indicator_le_norm_self _ _)
    hg.norm (ae_of_all _ fun t => tendsto_const_nhds.congr' (by
      filter_upwards [eventually_lt_atBot t] with x hx
      rw [Set.indicator_of_mem (mem_Ioi.2 hx)]))
  simpa only [integral_indicator measurableSet_Ioi] using h

theorem summable_rpow_neg_one_iff_inv {A : Set ℕ} :
    Summable (fun n : A => ((n : ℕ) : ℝ) ^ (-(1 / 2 + 1 / 2 : ℝ))) ↔
      Summable (fun n : A => ((n : ℕ) : ℝ)⁻¹) := by
  rw [show -(1 / 2 + 1 / 2 : ℝ) = -1 by norm_num]
  simp only [Real.rpow_neg_one]

/-- For an index set with `Σ_{n∈A} 1/n < ∞`, the critical moment of `S_A` is absolutely
defined and zero. -/
theorem integral_exp_half_mul_indexThetaSource {A : Set ℕ}
    (hA : Summable (fun n : A => ((n : ℕ) : ℝ)⁻¹)) :
    Integrable (fun x : ℝ => Real.exp ((1 / 2 : ℝ) * x) * indexThetaSource A x) ∧
    (∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * indexThetaSource A x) = 0 := by
  have h := integral_exp_mul_indexThetaSource (A := A) (a := 1 / 2) (by norm_num)
    (summable_rpow_neg_one_iff_inv.2 hA)
  refine ⟨h.1, ?_⟩
  rw [h.2]; ring

/-- **Both walls vanish at every admissible stage.**  If `Σ_{n∈A} 1/n < ∞` then `H_A → 0` at
the cusp as well. -/
theorem tendsto_indexFluxPotential_atBot_of_summable {A : Set ℕ}
    (hA : Summable (fun n : A => ((n : ℕ) : ℝ)⁻¹)) :
    Tendsto (indexFluxPotential A) atBot (𝓝 0) := by
  obtain ⟨hi, h0⟩ := integral_exp_half_mul_indexThetaSource hA
  have h := tendsto_setIntegral_Ioi_atBot_real hi
  rw [h0] at h
  exact h.congr fun x => (indexFluxPotential_eq_setIntegral A x).symm

/-- **The completed potential has left wall `1/2`.** -/
theorem tendsto_indexFluxPotential_univ_atBot :
    Tendsto (indexFluxPotential univ) atBot (𝓝 (1 / 2)) := by
  have hi : Integrable (fun x : ℝ => Real.exp ((1 / 2 : ℝ) * x) * indexThetaSource univ x) := by
    rw [← thetaCuspFullSource_eq_indexThetaSource]
    exact integrable_exp_mul_thetaCuspFullSource_of_abs_lt_one (by norm_num [abs_of_pos])
  have h := tendsto_setIntegral_Ioi_atBot_real hi
  rw [← thetaCuspFullSource_eq_indexThetaSource, integral_exp_half_mul_thetaCuspFullSource_eq_half,
    thetaCuspFullSource_eq_indexThetaSource] at h
  exact h.congr fun x => (indexFluxPotential_eq_setIntegral univ x).symm

theorem indexFluxPotential_univ_le_half (x : ℝ) : indexFluxPotential univ x ≤ 1 / 2 := by
  rw [indexFluxPotential_eq_setIntegral, ← thetaCuspFullSource_eq_indexThetaSource]
  exact (setIntegral_le_integral
    (integrable_exp_mul_thetaCuspFullSource_of_abs_lt_one
      (by norm_num [abs_of_pos] : |(1 / 2 : ℝ)| < 1))
    (ae_of_all _ fun t => mul_nonneg (Real.exp_pos _).le (thetaCuspFullSource_pos_all t).le)).trans_eq
    integral_exp_half_mul_thetaCuspFullSource_eq_half

theorem indexFluxPotential_le_half (A : Set ℕ) (x : ℝ) : indexFluxPotential A x ≤ 1 / 2 :=
  (indexFluxPotential_le_univ A x).trans (indexFluxPotential_univ_le_half x)

/-! ## Arbitrary exhaustions -/

theorem tendsto_tsum_subtype_of_exhaustion {f : ℕ → ℝ} (hf : Summable f) (hf0 : f 0 = 0)
    {A : ℕ → Set ℕ} (hA : ∀ n, 0 < n → ∀ᶠ j in atTop, n ∈ A j) :
    Tendsto (fun j => ∑' n : A j, f n) atTop (𝓝 (∑' n, f n)) := by
  simp_rw [tsum_subtype]
  refine tendsto_tsum_of_dominated_convergence (bound := fun n => ‖f n‖) hf.norm (fun n => ?_)
    (Eventually.of_forall fun j n => norm_indicator_le_norm_self _ _)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine tendsto_const_nhds.congr fun j => ?_
    by_cases h : 0 ∈ A j <;> simp [h, hf0]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hA n hn] with j hj
    rw [Set.indicator_of_mem hj]

theorem tendsto_indexThetaSource_of_exhaustion {A : ℕ → Set ℕ}
    (hA : ∀ n, 0 < n → ∀ᶠ j in atTop, n ∈ A j) (x : ℝ) :
    Tendsto (fun j => indexThetaSource (A j) x) atTop (𝓝 (thetaCuspFullSource x)) :=
  tendsto_tsum_subtype_of_exhaustion (summable_thetaCuspSourceTerm x) (thetaCuspSourceTerm_zero x) hA

theorem tendsto_indexFluxPotential_of_exhaustion {A : ℕ → Set ℕ}
    (hA : ∀ n, 0 < n → ∀ᶠ j in atTop, n ∈ A j) (x : ℝ) :
    Tendsto (fun j => indexFluxPotential (A j) x) atTop (𝓝 (indexFluxPotential univ x)) := by
  rw [indexFluxPotential, tsum_univ (f := fun n => thetaFluxTerm x n)]
  exact tendsto_tsum_subtype_of_exhaustion (summable_thetaFluxTerm x) (thetaFluxTerm_zero x) hA

/-- The residual critical moment is `1/2` at every admissible stage. -/
theorem integral_exp_half_mul_sub_indexThetaSource {A : Set ℕ}
    (hA : Summable (fun n : A => ((n : ℕ) : ℝ)⁻¹)) :
    (∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * (thetaCuspFullSource x - indexThetaSource A x)) =
      1 / 2 := by
  obtain ⟨hS, h0⟩ := integral_exp_half_mul_indexThetaSource hA
  simp_rw [mul_sub]
  rw [integral_sub (integrable_exp_mul_thetaCuspFullSource_of_abs_lt_one
    (by norm_num [abs_of_pos] : |(1 / 2 : ℝ)| < 1)) hS,
    integral_exp_half_mul_thetaCuspFullSource_eq_half, h0, sub_zero]

/-- The residual critical mass on every right half-line `x > −R` tends to zero along any
exhaustion. -/
theorem tendsto_setIntegral_Ioi_exp_half_mul_sub_indexThetaSource {A : ℕ → Set ℕ}
    (hA : ∀ n, 0 < n → ∀ᶠ j in atTop, n ∈ A j) (R : ℝ) :
    Tendsto (fun j => ∫ x in Ioi (-R), Real.exp ((1 / 2 : ℝ) * x) *
      (thetaCuspFullSource x - indexThetaSource (A j) x)) atTop (𝓝 0) := by
  have hk : IntegrableOn (fun x : ℝ => Real.exp ((1 / 2 : ℝ) * x) * thetaCuspFullSource x)
      (Ioi (-R)) := (integrable_exp_mul_thetaCuspFullSource_of_abs_lt_one
        (by norm_num [abs_of_pos] : |(1 / 2 : ℝ)| < 1)).integrableOn
  have hval : ∀ j, (∫ x in Ioi (-R), Real.exp ((1 / 2 : ℝ) * x) *
      (thetaCuspFullSource x - indexThetaSource (A j) x)) =
        indexFluxPotential univ (-R) - indexFluxPotential (A j) (-R) := fun j => by
    rw [indexFluxPotential_eq_setIntegral, indexFluxPotential_eq_setIntegral,
      ← thetaCuspFullSource_eq_indexThetaSource,
      ← integral_sub hk (integrableOn_exp_half_mul_indexThetaSource_Ioi _ _)]
    congr 1; funext x; ring
  simp_rw [hval]
  simpa using (tendsto_indexFluxPotential_of_exhaustion hA (-R)).const_sub
    (indexFluxPotential univ (-R))

/-- **(6) Escaped charge, for every admissible exhaustion.**  If `Σ_{n∈A_j} 1/n < ∞` and every
`n ≥ 1` eventually lies in `A_j`, then for every `R`,
`∫_{−∞}^{−R} e^{x/2}(k − S_{A_j}) → 1/2`. -/
theorem tendsto_setIntegral_Iio_exp_half_mul_sub_indexThetaSource {A : ℕ → Set ℕ}
    (hsum : ∀ j, Summable (fun n : A j => ((n : ℕ) : ℝ)⁻¹))
    (hA : ∀ n, 0 < n → ∀ᶠ j in atTop, n ∈ A j) (R : ℝ) :
    Tendsto (fun j => ∫ x in Iio (-R), Real.exp ((1 / 2 : ℝ) * x) *
      (thetaCuspFullSource x - indexThetaSource (A j) x)) atTop (𝓝 (1 / 2)) := by
  have hk : Integrable (fun x : ℝ => Real.exp ((1 / 2 : ℝ) * x) * thetaCuspFullSource x) :=
    integrable_exp_mul_thetaCuspFullSource_of_abs_lt_one (by norm_num [abs_of_pos])
  have hval : ∀ j, (∫ x in Iio (-R), Real.exp ((1 / 2 : ℝ) * x) *
      (thetaCuspFullSource x - indexThetaSource (A j) x)) =
        1 / 2 - indexFluxPotential univ (-R) + indexFluxPotential (A j) (-R) := fun j => by
    obtain ⟨hS, h0⟩ := integral_exp_half_mul_indexThetaSource (hsum j)
    have hint : Integrable (fun x : ℝ => Real.exp ((1 / 2 : ℝ) * x) *
        (thetaCuspFullSource x - indexThetaSource (A j) x)) :=
      (hk.sub hS).congr (ae_of_all _ fun x => by simp only [Pi.sub_apply]; ring)
    have hsplit := integral_add_compl (measurableSet_Ioi (a := -R)) hint
    rw [compl_Ioi, integral_Iic_eq_integral_Iio] at hsplit
    have htot : (∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) *
        (thetaCuspFullSource x - indexThetaSource (A j) x)) = 1 / 2 := by
      simp_rw [mul_sub]
      rw [integral_sub hk hS, integral_exp_half_mul_thetaCuspFullSource_eq_half, h0, sub_zero]
    have hright : (∫ x in Ioi (-R), Real.exp ((1 / 2 : ℝ) * x) *
        (thetaCuspFullSource x - indexThetaSource (A j) x)) =
          indexFluxPotential univ (-R) - indexFluxPotential (A j) (-R) := by
      rw [indexFluxPotential_eq_setIntegral, indexFluxPotential_eq_setIntegral,
        ← thetaCuspFullSource_eq_indexThetaSource, ← integral_sub hk.integrableOn
          (integrableOn_exp_half_mul_indexThetaSource_Ioi _ _)]
      congr 1; funext x; ring
    linarith
  simp_rw [hval]
  have h := ((tendsto_indexFluxPotential_of_exhaustion hA (-R)).const_add
    (1 / 2 - indexFluxPotential univ (-R)))
  simpa using h

/-! ## The boundary-sensitive test-space limit -/

/-- Integration by parts against a flux potential with values in `[0, 1/2]`. -/
theorem integral_mul_eq_integral_deriv_mul_indexFluxPotential {A : Set ℕ} {ψ ψ' : ℝ → ℂ}
    (hψ : ∀ x, HasDerivAt ψ (ψ' x) x) (hψ' : Integrable ψ') {C : ℝ} (hC : ∀ x, ‖ψ x‖ ≤ C)
    (hS : Integrable (fun x : ℝ => Real.exp ((1 / 2 : ℝ) * x) * indexThetaSource A x))
    {a' b' : ℂ} (hbot : Tendsto (fun x => ψ x * (indexFluxPotential A x : ℂ)) atBot (𝓝 a'))
    (htop : Tendsto (fun x => ψ x * (indexFluxPotential A x : ℂ)) atTop (𝓝 b')) :
    (∫ x : ℝ, ψ x * ((Real.exp ((1 / 2 : ℝ) * x) * indexThetaSource A x : ℝ) : ℂ)) =
      a' - b' + ∫ x : ℝ, ψ' x * (indexFluxPotential A x : ℂ) := by
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun x => (hψ x).continuousAt
  have hv : ∀ x, HasDerivAt (fun y => (indexFluxPotential A y : ℂ))
      (-((Real.exp ((1 / 2 : ℝ) * x) * indexThetaSource A x : ℝ) : ℂ)) x := fun x => by
    simpa using (hasDerivAt_indexFluxPotential A x).ofReal_comp
  have huv : Integrable (fun x => ψ x *
      -((Real.exp ((1 / 2 : ℝ) * x) * indexThetaSource A x : ℝ) : ℂ)) :=
    hS.ofReal.neg.bdd_mul hψc.aestronglyMeasurable (ae_of_all _ hC)
  have hu'v : Integrable (fun x => ψ' x * (indexFluxPotential A x : ℂ)) :=
    hψ'.mul_bdd (Complex.continuous_ofReal.comp (continuous_indexFluxPotential A)).aestronglyMeasurable
      (c := 1 / 2) (ae_of_all _ fun x => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (indexFluxPotential_nonneg A x)]
        exact indexFluxPotential_le_half A x)
  have h := integral_mul_deriv_eq_deriv_mul (u := ψ) (v := fun y => (indexFluxPotential A y : ℂ))
    (fun x _ => hψ x) (fun x _ => hv x) huv hu'v hbot htop
  simp only [mul_neg, integral_neg] at h
  linear_combination -h

theorem tendsto_mul_indexFluxPotential_of_tendsto_zero {A : Set ℕ} {ψ : ℝ → ℂ} {C : ℝ}
    (hC : ∀ x, ‖ψ x‖ ≤ C) {l : Filter ℝ} (hH : Tendsto (indexFluxPotential A) l (𝓝 0)) :
    Tendsto (fun x => ψ x * (indexFluxPotential A x : ℂ)) l (𝓝 0) := by
  refine squeeze_zero_norm (a := fun x => C * indexFluxPotential A x) (fun x => ?_) ?_
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (indexFluxPotential_nonneg A x)]
    exact mul_le_mul_of_nonneg_right (hC x) (indexFluxPotential_nonneg A x)
  · simpa using hH.const_mul C

/-- **(6a) Completed bulk plus a negative half-unit boundary functional.**  Let `A_j` be any
sequence of index sets with `Σ_{n∈A_j} 1/n < ∞` such that every `n ≥ 1` eventually lies in `A_j`.
For every bounded differentiable test `ψ` with integrable derivative, `ψ(−∞)` exists and
`∫ ψ e^{x/2} S_{A_j} → ∫ ψ e^{x/2} k − ψ(−∞)/2`. -/
theorem tendsto_integral_mul_exp_half_mul_indexThetaSource {A : ℕ → Set ℕ}
    (hsum : ∀ j, Summable (fun n : A j => ((n : ℕ) : ℝ)⁻¹))
    (hA : ∀ n, 0 < n → ∀ᶠ j in atTop, n ∈ A j) {ψ ψ' : ℝ → ℂ}
    (hψ : ∀ x, HasDerivAt ψ (ψ' x) x) (hψ' : Integrable ψ') {C : ℝ} (hC : ∀ x, ‖ψ x‖ ≤ C) :
    ∃ L : ℂ, Tendsto ψ atBot (𝓝 L) ∧
      Tendsto (fun j => ∫ x : ℝ, ψ x * ((Real.exp ((1 / 2 : ℝ) * x) * indexThetaSource (A j) x : ℝ) : ℂ))
        atTop (𝓝 ((∫ x : ℝ, ψ x * ((Real.exp ((1 / 2 : ℝ) * x) * thetaCuspFullSource x : ℝ) : ℂ)) -
          L / 2)) := by
  have hL := tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic (a := 0) (fun x _ => hψ x)
    hψ'.integrableOn
  set L := limUnder atBot ψ
  refine ⟨L, hL, ?_⟩
  have hk : Integrable (fun x : ℝ => Real.exp ((1 / 2 : ℝ) * x) * indexThetaSource univ x) := by
    rw [← thetaCuspFullSource_eq_indexThetaSource]
    exact integrable_exp_mul_thetaCuspFullSource_of_abs_lt_one (by norm_num [abs_of_pos])
  have hfull := integral_mul_eq_integral_deriv_mul_indexFluxPotential hψ hψ' hC hk
    (hL.mul ((Complex.continuous_ofReal.tendsto _).comp tendsto_indexFluxPotential_univ_atBot))
    (tendsto_mul_indexFluxPotential_of_tendsto_zero hC (tendsto_indexFluxPotential_atTop univ))
  rw [← thetaCuspFullSource_eq_indexThetaSource] at hfull
  have hstage : ∀ j, (∫ x : ℝ, ψ x *
      ((Real.exp ((1 / 2 : ℝ) * x) * indexThetaSource (A j) x : ℝ) : ℂ)) =
        ∫ x : ℝ, ψ' x * (indexFluxPotential (A j) x : ℂ) := fun j => by
    rw [integral_mul_eq_integral_deriv_mul_indexFluxPotential hψ hψ' hC
      (integral_exp_half_mul_indexThetaSource (hsum j)).1
      (tendsto_mul_indexFluxPotential_of_tendsto_zero hC
        (tendsto_indexFluxPotential_atBot_of_summable (hsum j)))
      (tendsto_mul_indexFluxPotential_of_tendsto_zero hC (tendsto_indexFluxPotential_atTop _))]
    ring
  simp_rw [hstage]
  have hlim : Tendsto (fun j => ∫ x : ℝ, ψ' x * (indexFluxPotential (A j) x : ℂ)) atTop
      (𝓝 (∫ x : ℝ, ψ' x * (indexFluxPotential univ x : ℂ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖ψ' x‖ * (1 / 2))
      (Eventually.of_forall fun j => hψ'.aestronglyMeasurable.mul
        (Complex.continuous_ofReal.comp (continuous_indexFluxPotential _)).aestronglyMeasurable)
      (Eventually.of_forall fun j => ae_of_all _ fun x => ?_) (hψ'.norm.mul_const _)
      (ae_of_all _ fun x => ((Complex.continuous_ofReal.tendsto _).comp
        (tendsto_indexFluxPotential_of_exhaustion hA x)).const_mul (ψ' x))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (indexFluxPotential_nonneg _ x)]
    exact mul_le_mul_of_nonneg_left (indexFluxPotential_le_half _ x) (norm_nonneg _)
  convert hlim using 2
  rw [hfull]
  push_cast
  ring

/-! ## Finite-prime stages -/

theorem summable_inv_smoothNumbers (N : ℕ) :
    Summable (fun n : (N + 1).smoothNumbers => ((n : ℕ) : ℝ)⁻¹) :=
  summable_rpow_neg_one_iff_inv.1 (summable_smoothNumbers_rpow_neg N (by norm_num))

theorem eventually_mem_smoothNumbers {n : ℕ} (hn : 0 < n) :
    ∀ᶠ N in atTop, n ∈ (N + 1).smoothNumbers := by
  filter_upwards [eventually_ge_atTop n] with N hN
  exact Nat.mem_smoothNumbers_of_lt hn (by omega)

/-- The finite-prime flux potential vanishes at both ends. -/
theorem tendsto_finitePrimeFluxPotential (N : ℕ) :
    Tendsto (indexFluxPotential (N + 1).smoothNumbers) atBot (𝓝 0) ∧
      Tendsto (indexFluxPotential (N + 1).smoothNumbers) atTop (𝓝 0) :=
  ⟨tendsto_indexFluxPotential_atBot_of_summable (summable_inv_smoothNumbers N),
    tendsto_indexFluxPotential_atTop _⟩

/-- **(6) for the finite-prime sources.** -/
theorem tendsto_setIntegral_Iio_exp_half_mul_sub_finitePrimeThetaCuspSource (R : ℝ) :
    Tendsto (fun N : ℕ => ∫ x in Iio (-R), Real.exp ((1 / 2 : ℝ) * x) *
      (thetaCuspFullSource x - finitePrimeThetaCuspSource N x)) atTop (𝓝 (1 / 2)) :=
  tendsto_setIntegral_Iio_exp_half_mul_sub_indexThetaSource summable_inv_smoothNumbers
    (fun _ hn => eventually_mem_smoothNumbers hn) R

/-- **(6a) for the finite-prime sources.** -/
theorem tendsto_integral_mul_exp_half_mul_finitePrimeThetaCuspSource {ψ ψ' : ℝ → ℂ}
    (hψ : ∀ x, HasDerivAt ψ (ψ' x) x) (hψ' : Integrable ψ') {C : ℝ} (hC : ∀ x, ‖ψ x‖ ≤ C) :
    ∃ L : ℂ, Tendsto ψ atBot (𝓝 L) ∧
      Tendsto (fun N : ℕ => ∫ x : ℝ, ψ x *
          ((Real.exp ((1 / 2 : ℝ) * x) * finitePrimeThetaCuspSource N x : ℝ) : ℂ))
        atTop (𝓝 ((∫ x : ℝ, ψ x * ((Real.exp ((1 / 2 : ℝ) * x) * thetaCuspFullSource x : ℝ) : ℂ)) -
          L / 2)) :=
  tendsto_integral_mul_exp_half_mul_indexThetaSource summable_inv_smoothNumbers
    (fun _ hn => eventually_mem_smoothNumbers hn) hψ hψ' hC

/-- The spectral tests `ψ_w(x) = e^{(w − 1/2)x}` of the Xi strip are unbounded at the cusp when
`Re w < 1/2`, so they lie outside the bounded test space of the boundary-charge limit. -/
theorem tendsto_norm_cexp_sub_half_mul_atBot {w : ℂ} (hw : w.re < 1 / 2) :
    Tendsto (fun x : ℝ => ‖Complex.exp ((w - 1 / 2) * x)‖) atBot atTop := by
  have h : Tendsto (fun x : ℝ => (w.re - 1 / 2) * x) atBot atTop :=
    tendsto_id.const_mul_atBot_of_neg (by linarith)
  refine (Real.tendsto_exp_atTop.comp h).congr fun x => ?_
  simp only [Function.comp, Complex.norm_exp, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  norm_num

end

end RHTower
