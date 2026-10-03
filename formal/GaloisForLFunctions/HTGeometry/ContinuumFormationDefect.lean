import GaloisForLFunctions.HTGeometry.CubicApertureGradedCarrier
import GaloisForLFunctions.HTGeometry.LaplaceAtomicRigidity
import GaloisForLFunctions.HTGeometry.BurnolHalfLineWeightedShift
import GaloisForLFunctions.HTGeometry.GramianInverseForm
import GaloisForLFunctions.HTGeometry.WeakSequentialCompactness
import GaloisForLFunctions.HTGeometry.ObserverHorizonStability

/-!
# Zero-distance / infinite-action formation defect

On the Burnol carrier `H_B = L²((0,∞), dr)` the cubic-gauged continuum synthesis
`(A₀ b)(r) = ∫ b(s) m(s) f_s(r) ds`, `f_s(r) = r e^{-sr}`, `m = √(h_x) d_c^{3/2} > 0`, is
`r ↦ r · L_b(r)` with `L_b` the Laplace transform of the integrable label density `b m`.

* **Theorem ZDIA-B (ZDIA.3)–(ZDIA.4).**  `A₀ b = ∑_{n ∈ F} c_n f_{log n}` forces `b = 0` and all `c_n = 0`
  (Laplace rigidity of an absolutely continuous density against finitely many atoms); no nonzero
  finite active Euler packet lies in `Ran A₀`.
* **Theorem OCSE-A / ZDIA-A.**  The columns `f_s` are total (Laplace uniqueness on `L¹`), so `A₀*` is
  injective and `A₀` has dense range; `A₀` is compact, injective and not surjective, and its inverse
  `G₀` is closed, densely defined and unbounded **(ZDIA.2)**; Euler packets are at distance zero
  from the range **(ZDIA.5)**.
* **Theorem ZDIA-C (ZDIA.6)–(ZDIA.8).**  For a compact `T` and `y ∉ Ran T`, every `T b_j → y` has
  `‖b_j‖ → ∞` (weak compactness), and the approximation action `L_ε(y) → ∞`.
* **(ZDIA.9)–(ZDIA.12).**  `C_ε = A_E* (A₀A₀* + ε)⁻¹ A_E` is positive, a product of Hilbert–Schmidt
  operators, `0 ≤ Tr C_ε ≤ ε⁻¹ ‖A_E‖²_HS ≤ ε⁻¹ B_base`, its entries are `⟪y_n, (K₀ + ε)⁻¹ y_m⟫`, and
  every active diagonal diverges (Tikhonov identity plus Theorem ZDIA-C).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance factTwoNeTopContinuumDefect : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-! ## Radial vectors and the gauge -/

theorem memLp_burnolRadial {s : ℝ} (hs : 0 < s) :
    MemLp (fun r => ((burnolRadial s r : ℝ) : ℂ)) 2 halfLineMeasure := by
  refine (memLp_two_iff_integrable_sq_norm (by unfold burnolRadial; fun_prop)).2 ?_
  have h := (integrableOn_Ici_iff_integrableOn_Ioi enorm_ne_top).2 (integrableOn_burnolRadial_sq hs)
  refine (h.congr_fun (fun r _ => ?_) measurableSet_Ici : IntegrableOn _ (Ici (0 : ℝ)) volume)
  simp [Complex.norm_real, sq_abs]

/-- The radial vector `f_s ∈ H_B`. -/
def radialLp {s : ℝ} (hs : 0 < s) : BurnolCarrier := (memLp_burnolRadial hs).toLp _

theorem radialLp_coeFn {s : ℝ} (hs : 0 < s) :
    (radialLp hs : ℝ → ℂ) =ᵐ[halfLineMeasure] fun r => ((burnolRadial s r : ℝ) : ℂ) :=
  (memLp_burnolRadial hs).coeFn_toLp

variable {x c : ℝ}

theorem cubicGaugeWeight_sq_le_exp (hx : 0 < x) (hc : 0 < c) {s : ℝ} (hs : 0 ≤ s) :
    cubicGaugeWeight x c s ^ 2 ≤ Real.exp (-(2 * Real.pi * x) * s) := by
  rw [cubicGaugeWeight_sq hc.le hs]
  have h1 : apertureDefect c s ^ 3 ≤ 1 :=
    pow_le_one₀ (apertureDefect_nonneg hc.le hs) (apertureDefect_le_one c s)
  have h2 : thetaDamping x s ≤ Real.exp (-(2 * Real.pi * x) * s) := by
    rw [thetaDamping, Real.exp_le_exp]
    have h3 : 2 * s ≤ Real.exp (2 * s) := by linarith [Real.add_one_le_exp (2 * s)]
    have h4 : 0 ≤ Real.pi * x * (Real.exp (2 * s) - 2 * s) :=
      mul_nonneg (mul_pos Real.pi_pos hx).le (by linarith)
    nlinarith
  calc _ ≤ thetaDamping x s * 1 := mul_le_mul_of_nonneg_left h1 (thetaDamping_pos x s).le
    _ ≤ _ := by rw [mul_one]; exact h2

theorem memLp_gauge (hx : 0 < x) (hc : 0 < c) :
    MemLp (fun s => ((cubicGaugeWeight x c s : ℝ) : ℂ)) 2 halfLineMeasure := by
  have hcont := continuous_cubicGaugeWeight x c
  refine (memLp_two_iff_integrable_sq_norm (by fun_prop)).2 ?_
  have hexp : Integrable (fun s => Real.exp (-(2 * Real.pi * x) * s)) halfLineMeasure := by
    exact (integrableOn_Ici_iff_integrableOn_Ioi enorm_ne_top).2
      (exp_neg_integrableOn_Ioi 0 (by positivity))
  refine hexp.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
  rw [Real.norm_of_nonneg (sq_nonneg _), Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact cubicGaugeWeight_sq_le_exp hx hc hs

/-! ## The continuum synthesis as a Laplace transform -/

/-- The label density `g_b = b m`. -/
def labelDensity (x c : ℝ) (b : BurnolCarrier) (s : ℝ) : ℂ := b s * ((cubicGaugeWeight x c s : ℝ) : ℂ)

theorem integrable_labelDensity (hx : 0 < x) (hc : 0 < c) (b : BurnolCarrier) :
    Integrable (labelDensity x c b) halfLineMeasure :=
  (Lp.memLp b).integrable_mul (memLp_gauge hx hc)

theorem integrableOn_labelDensity (hx : 0 < x) (hc : 0 < c) (b : BurnolCarrier) :
    IntegrableOn (labelDensity x c b) (Ioi 0) := by
  exact (show IntegrableOn (labelDensity x c b) (Ici 0) volume from
    integrable_labelDensity hx hc b).mono_set Ioi_subset_Ici_self

/-- The Laplace transform `L_b(r) = ∫ b(s) m(s) e^{-rs} ds`. -/
def labelLaplace (x c : ℝ) (b : BurnolCarrier) (r : ℝ) : ℂ :=
  ∫ s in Ioi 0, labelDensity x c b s * (Real.exp (-r * s) : ℂ)

/-- `A₀ b = r ↦ r L_b(r)`. -/
theorem continuumSynthesis_coeFn (hx : 0 < x) (hc : 0 < c) (b : BurnolCarrier) :
    (continuumSynthesis hx hc b : ℝ → ℂ) =ᵐ[halfLineMeasure]
      fun r => (r : ℂ) * labelLaplace x c b r := by
  filter_upwards [(continuumKernel hx hc).op_coeFn b] with r hr
  rw [continuumSynthesis, hr, SqIntKernel.apply, labelLaplace, ← integral_const_mul,
    integral_Ici_eq_integral_Ioi]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  change ((cubicGaugeWeight x c s * burnolRadial s r : ℝ) : ℂ) * b s = _
  rw [labelDensity, burnolRadial]
  push_cast
  rw [show -(↑s * ↑r) = (-↑r * ↑s : ℂ) by ring]
  ring

theorem continuousOn_labelLaplace (hx : 0 < x) (hc : 0 < c) (b : BurnolCarrier) :
    ContinuousOn (labelLaplace x c b) (Ici 0) := by
  have hg := integrableOn_labelDensity hx hc b
  refine continuousOn_of_dominated (bound := fun s => ‖labelDensity x c b s‖)
    (fun r _ => (hg.aestronglyMeasurable.mul (by fun_prop))) (fun r hr => ?_) hg.norm ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [Real.exp_le_one_iff]
    have hr' : (0 : ℝ) ≤ r := hr
    have hs' : (0 : ℝ) < s := hs
    nlinarith
  · exact Eventually.of_forall fun s => (by fun_prop : Continuous fun r : ℝ =>
      labelDensity x c b s * (Real.exp (-r * s) : ℂ)).continuousOn

/-! ## Theorem ZDIA-B -/

theorem log_injOn_atomLabel (F : Finset AtomLabel) :
    Set.InjOn (fun n : AtomLabel => Real.log (n : ℕ)) F := by
  intro n _ m _ h
  have hn : (0 : ℝ) < (n : ℕ) := by exact_mod_cast (show 0 < (n : ℕ) by have := n.2; omega)
  have hm : (0 : ℝ) < (m : ℕ) := by exact_mod_cast (show 0 < (m : ℕ) by have := m.2; omega)
  have := Real.log_injOn_pos (Set.mem_Ioi.2 hn) (Set.mem_Ioi.2 hm) h
  exact Subtype.ext (by exact_mod_cast this)

/-- **Theorem ZDIA-B, rigidity form.**  If the continuum synthesis of `b` equals a finite combination
of Euler columns `∑ c_n f_{log n}`, then `b = 0` and every `c_n = 0`. -/
theorem continuumSynthesis_eq_atoms (hx : 0 < x) (hc : 0 < c) (F : Finset AtomLabel)
    (w : AtomLabel → ℂ) (b : BurnolCarrier)
    (h : continuumSynthesis hx hc b = ∑ n ∈ F, w n • radialLp (log_pos_of_atomLabel n)) :
    b = 0 ∧ ∀ n ∈ F, w n = 0 := by
  -- pointwise identity `r L_b(r) = ∑ w_n r e^{-r log n}` almost everywhere
  have hsum := Lp.coeFn_finsetSum (μ := halfLineMeasure) F
    (fun n => w n • radialLp (log_pos_of_atomLabel n))
  have hterm : ∀ n ∈ F, (⇑(w n • radialLp (log_pos_of_atomLabel n)) : ℝ → ℂ) =ᵐ[halfLineMeasure]
      fun r => w n * ((burnolRadial (Real.log (n : ℕ)) r : ℝ) : ℂ) := by
    intro n _
    filter_upwards [Lp.coeFn_smul (w n) (radialLp (log_pos_of_atomLabel n)),
      radialLp_coeFn (log_pos_of_atomLabel n)] with r h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  have hterms : ∀ᵐ r ∂halfLineMeasure, ∀ n ∈ F,
      (⇑(w n • radialLp (log_pos_of_atomLabel n)) : ℝ → ℂ) r =
        w n * ((burnolRadial (Real.log (n : ℕ)) r : ℝ) : ℂ) :=
    (ae_ball_iff F.countable_toSet).2 fun n hn => hterm n hn
  have hae : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      labelLaplace x c b r = ∑ n ∈ F, w n * (Real.exp (-r * Real.log (n : ℕ)) : ℂ) := by
    have h1 : ∀ᵐ (r : ℝ) ∂halfLineMeasure, (r : ℂ) * labelLaplace x c b r =
        ∑ n ∈ F, w n * ((burnolRadial (Real.log (n : ℕ)) r : ℝ) : ℂ) := by
      filter_upwards [continuumSynthesis_coeFn hx hc b, hsum, hterms] with r e1 e2 e3
      rw [← e1, h, e2, Finset.sum_apply]
      exact Finset.sum_congr rfl e3
    have h2 : ∀ᵐ (r : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))), (r : ℂ) * labelLaplace x c b r =
        ∑ n ∈ F, w n * ((burnolRadial (Real.log (n : ℕ)) r : ℝ) : ℂ) :=
      ae_restrict_of_ae_restrict_of_subset Ioi_subset_Ici_self h1
    filter_upwards [h2, ae_restrict_mem measurableSet_Ioi] with r e hr
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hr)
    apply mul_left_cancel₀ hr0
    rw [e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [burnolRadial, show -(Real.log (n : ℕ) * r) = -r * Real.log (n : ℕ) by ring,
      Complex.ofReal_mul]
    ring
  -- continuity upgrades to every `r > 0`
  have heq : Set.EqOn (labelLaplace x c b)
      (fun r => ∑ n ∈ F, w n * (Real.exp (-r * Real.log (n : ℕ)) : ℂ)) (Ioi 0) :=
    Measure.eqOn_of_ae_eq hae ((continuousOn_labelLaplace hx hc b).mono Ioi_subset_Ici_self)
      (by fun_prop) (by rw [interior_Ioi, closure_Ioi]; exact Ioi_subset_Ici_self)
  have hrig := laplace_atomic_rigidity (integrableOn_labelDensity hx hc b) F
    (p := fun n : AtomLabel => Real.log (n : ℕ)) (fun n _ => log_pos_of_atomLabel n)
    (log_injOn_atomLabel F) w fun t ht => by
      have := heq ht
      simp only [labelLaplace] at this
      rw [this]
  refine ⟨?_, hrig.2⟩
  -- `b m = 0` and `m > 0` give `b = 0`
  have hb : (b : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] 0 := by
    filter_upwards [hrig.1, ae_restrict_mem measurableSet_Ioi] with s hs hpos
    have hm : ((cubicGaugeWeight x c s : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (cubicGaugeWeight_pos hc hpos).ne'
    have : b s * ((cubicGaugeWeight x c s : ℝ) : ℂ) = 0 := hs
    exact (mul_eq_zero.1 this).resolve_right hm
  refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
  change (b : ℝ → ℂ) =ᵐ[volume.restrict (Ici 0)] 0
  rw [← Measure.restrict_congr_set Ioi_ae_eq_Ici]
  exact hb

/-- **Theorem ZDIA-A, injectivity.** -/
theorem continuumSynthesis_injective (hx : 0 < x) (hc : 0 < c) :
    Function.Injective (continuumSynthesis hx hc) := by
  refine (injective_iff_map_eq_zero _).2 fun b hb => ?_
  exact (continuumSynthesis_eq_atoms hx hc ∅ (fun _ => 0) b (by rw [hb, Finset.sum_empty])).1

/-- The Euler column `y_n = a_n f_{log n}`. -/
def eulerColumn (x c : ℝ) (n : AtomLabel) : BurnolCarrier :=
  (atomicCoefficient x c n : ℂ) • radialLp (log_pos_of_atomLabel n)

/-- **Theorem ZDIA-B (ZDIA.3).**  A finite packet of active Euler columns `∑ z_n y_n` with some
`z_n ≠ 0` is not in the range of `A₀`. -/
theorem eulerPacket_not_mem_range (hx : 0 < x) (hc : 0 < c) (F : Finset AtomLabel)
    (hF : ∀ n ∈ F, 0 < ArithmeticFunction.vonMangoldt (n : ℕ)) (z : AtomLabel → ℂ)
    (hz : ∃ n ∈ F, z n ≠ 0) :
    ∑ n ∈ F, z n • eulerColumn x c n ∉ Set.range (continuumSynthesis hx hc) := by
  rintro ⟨b, hb⟩
  have hb' : continuumSynthesis hx hc b =
      ∑ n ∈ F, (z n * atomicCoefficient x c n) • radialLp (log_pos_of_atomLabel n) := by
    rw [hb]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [eulerColumn, smul_smul]
  obtain ⟨n, hn, hzn⟩ := hz
  have h := (continuumSynthesis_eq_atoms hx hc F _ b hb').2 n hn
  have ha : (atomicCoefficient x c n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (atomicCoefficient_pos hc (hF n hn)).ne'
  exact hzn ((mul_eq_zero.1 h).resolve_right ha)

/-! ## Totality of the radial columns and dense range -/

/-- The pairing `s ↦ ∫ f_s(r) q(r) dr`. -/
def radialPairing (q : BurnolCarrier) (s : ℝ) : ℂ :=
  ∫ r in Ioi 0, ((burnolRadial s r : ℝ) : ℂ) * q r

theorem inner_radialLp {s : ℝ} (hs : 0 < s) (q : BurnolCarrier) :
    ⟪radialLp hs, q⟫_ℂ = radialPairing q s := by
  rw [L2.inner_def, radialPairing, ← integral_Ici_eq_integral_Ioi]
  refine integral_congr_ae ?_
  filter_upwards [radialLp_coeFn hs] with r hr
  rw [hr, RCLike.inner_apply, Complex.conj_ofReal, mul_comm]

/-- **Theorem OCSE-A.**  If `q ∈ H_B` pairs to zero with almost every column `f_s`, `s > 0`, then
`q = 0`: `r e^{-r} q(r)` is integrable with vanishing Laplace transform. -/
theorem eq_zero_of_radialPairing_ae_eq_zero (q : BurnolCarrier)
    (h : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), radialPairing q s = 0) : q = 0 := by
  set g : ℝ → ℂ := fun r => ((burnolRadial 1 r : ℝ) : ℂ) * q r with hgdef
  have hg : IntegrableOn g (Ioi 0) := by
    have h1 := (memLp_burnolRadial one_pos).integrable_mul (Lp.memLp q)
    exact (show IntegrableOn g (Ici 0) volume from h1).mono_set Ioi_subset_Ici_self
  have hshift : ∀ t : ℝ, radialPairing q (t + 1) = ∫ r in Ioi 0, g r * (Real.exp (-t * r) : ℂ) := by
    intro t
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp only [hgdef, burnolRadial]
    rw [show -((t + 1) * r) = -(1 * r) + -t * r by ring, Real.exp_add]
    push_cast
    ring
  have h1 := (quasiMeasurePreserving_add_right_Ioi (h := 1) zero_le_one).ae h
  have hlap : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫ r in Ioi 0, g r * (Real.exp (-t * r) : ℂ) = 0 := by
    filter_upwards [h1] with t ht
    rw [← hshift]
    exact ht
  have hg0 := ae_eq_zero_of_laplace_ae_eq_zero hg hlap
  refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
  change (q : ℝ → ℂ) =ᵐ[volume.restrict (Ici 0)] 0
  rw [← Measure.restrict_congr_set Ioi_ae_eq_Ici]
  filter_upwards [hg0, ae_restrict_mem measurableSet_Ioi] with r hr hpos
  have hne : ((burnolRadial 1 r : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, burnolRadial]
    exact mul_ne_zero (ne_of_gt hpos) (Real.exp_pos _).ne'
  exact (mul_eq_zero.1 hr).resolve_left hne

variable (hx : 0 < x) (hc : 0 < c)
include hx hc

/-- The adjoint `A₀* q = s ↦ m(s) ∫ f_s q`. -/
theorem adjoint_continuumSynthesis_coeFn (q : BurnolCarrier) :
    (ContinuousLinearMap.adjoint (continuumSynthesis hx hc) q : ℝ → ℂ) =ᵐ[halfLineMeasure]
      fun s => ((cubicGaugeWeight x c s : ℝ) : ℂ) * radialPairing q s := by
  rw [continuumSynthesis, SqIntKernel.adjoint_op]
  filter_upwards [(continuumKernel hx hc).adjoint.op_coeFn q] with s hs
  rw [hs, SqIntKernel.apply, radialPairing, ← integral_const_mul, ← integral_Ici_eq_integral_Ioi]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  change conj (((cubicGaugeWeight x c s * burnolRadial s r : ℝ) : ℂ)) * q r = _
  rw [Complex.conj_ofReal]
  push_cast
  ring

/-- **Theorem OCSE-B (OCSE.2) / ZDIA-A, density.**  `A₀*` is injective, so `A₀` has dense range. -/
theorem denseRange_continuumSynthesis : DenseRange (continuumSynthesis hx hc) := by
  have hker : ∀ q : BurnolCarrier, ContinuousLinearMap.adjoint (continuumSynthesis hx hc) q = 0 →
      q = 0 := by
    intro q hq
    refine eq_zero_of_radialPairing_ae_eq_zero q ?_
    have h1 := adjoint_continuumSynthesis_coeFn hx hc q
    rw [hq] at h1
    have h2 : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        ((cubicGaugeWeight x c s : ℝ) : ℂ) * radialPairing q s = 0 := by
      have h3 := ae_restrict_of_ae_restrict_of_subset Ioi_subset_Ici_self
        (h1.symm.trans (Lp.coeFn_zero ℂ 2 halfLineMeasure))
      filter_upwards [h3] with s hs
      exact hs
    filter_upwards [h2, ae_restrict_mem measurableSet_Ioi] with s hs hpos
    have hm : ((cubicGaugeWeight x c s : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (cubicGaugeWeight_pos hc hpos).ne'
    exact (mul_eq_zero.1 hs).resolve_left hm
  have hperp : (LinearMap.range (continuumSynthesis hx hc : BurnolCarrier →ₗ[ℂ] BurnolCarrier))ᗮ = ⊥ := by
    rw [ContinuousLinearMap.orthogonal_range, eq_bot_iff]
    intro q hq
    exact (Submodule.mem_bot ℂ).2 (hker q hq)
  have hclos := Submodule.orthogonal_orthogonal_eq_closure
    (LinearMap.range (continuumSynthesis hx hc : BurnolCarrier →ₗ[ℂ] BurnolCarrier))
  rw [hperp, Submodule.bot_orthogonal_eq_top] at hclos
  have hd := (Submodule.dense_iff_topologicalClosure_eq_top).2 hclos.symm
  simpa [DenseRange, LinearMap.coe_range] using hd

/-- **(ZDIA.5)** Every vector, in particular every Euler packet, is at distance zero from the range. -/
theorem infDist_range_eq_zero (y : BurnolCarrier) :
    Metric.infDist y (Set.range (continuumSynthesis hx hc)) = 0 :=
  Metric.infDist_zero_of_mem_closure ((denseRange_continuumSynthesis hx hc).closure_eq ▸ mem_univ y)

omit hx hc in
theorem two_mem_active : 0 < ArithmeticFunction.vonMangoldt ((⟨2, le_rfl⟩ : AtomLabel) : ℕ) := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  exact Real.log_pos (by norm_num)

/-- **Theorem ZDIA-A, nonsurjectivity.**  The Euler column `y_2` is not in the range. -/
theorem not_surjective_continuumSynthesis : ¬ Function.Surjective (continuumSynthesis hx hc) := by
  intro hs
  have h := eulerPacket_not_mem_range hx hc {⟨2, le_rfl⟩} (by simpa using two_mem_active)
    (fun _ => 1) ⟨⟨2, le_rfl⟩, by simp, one_ne_zero⟩
  exact h (hs _)

/-- **Theorem ZDIA-A, compactness.** -/
theorem isCompactOperator_continuumSynthesis : IsCompactOperator (continuumSynthesis hx hc) :=
  (isHilbertSchmidt_continuumSynthesis hx hc).isCompactOperator

/-- **(ZDIA.2)** The continuum completion graph `G₀ = A₀⁻¹` with domain `Ran A₀`. -/
def continuumInverse : BurnolCarrier →ₗ.[ℂ] BurnolCarrier :=
  gramInverse (continuumSynthesis hx hc) (continuumSynthesis_injective hx hc)

/-- **(ZDIA.2)** `G₀` is closed, densely defined and unbounded. -/
theorem continuumInverse_closed_dense_unbounded :
    (continuumInverse hx hc).IsClosed ∧ Dense ((continuumInverse hx hc).domain : Set BurnolCarrier) ∧
      ¬ ∃ C : ℝ, ∀ y : (continuumInverse hx hc).domain,
        ‖continuumInverse hx hc y‖ ≤ C * ‖(y : BurnolCarrier)‖ := by
  have hinj := continuumSynthesis_injective hx hc
  refine ⟨?_, ?_, ?_⟩
  · -- the graph is the flipped graph of `A₀`
    have hg : ((continuumInverse hx hc).graph : Set (BurnolCarrier × BurnolCarrier)) =
        {p | continuumSynthesis hx hc p.2 = p.1} := by
      ext p
      simp only [SetLike.mem_coe, LinearPMap.mem_graph_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨y, hy1, hy2⟩
        rw [← hy2, ← hy1]
        exact apply_gramInverse hinj y
      · intro hp
        refine ⟨⟨p.1, (LinearMap.mem_range.2 ⟨p.2, hp⟩ :
          p.1 ∈ LinearMap.range (continuumSynthesis hx hc : BurnolCarrier →ₗ[ℂ] BurnolCarrier))⟩,
          rfl, ?_⟩
        apply hinj
        exact (apply_gramInverse hinj _).trans hp.symm
    rw [LinearPMap.IsClosed, hg]
    exact isClosed_eq ((continuumSynthesis hx hc).continuous.comp continuous_snd) continuous_fst
  · change Dense (Set.range (continuumSynthesis hx hc))
    exact denseRange_continuumSynthesis hx hc
  · rintro ⟨C, hC⟩
    -- `A₀` would be bounded below, so its range would be closed and dense
    have hbelow : ∀ b, ‖b‖ ≤ C * ‖continuumSynthesis hx hc b‖ := by
      intro b
      have h := hC ⟨continuumSynthesis hx hc b, mem_gramInverse_domain hinj b⟩
      have he : continuumInverse hx hc ⟨continuumSynthesis hx hc b, mem_gramInverse_domain hinj b⟩ = b :=
        hinj (apply_gramInverse hinj _)
      rwa [he] at h
    have hbelow' : ∀ b, ‖b‖ ≤ max C 0 * ‖continuumSynthesis hx hc b‖ := fun b =>
      (hbelow b).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have hanti : AntilipschitzWith (Real.toNNReal (max C 0)) (continuumSynthesis hx hc) := by
      refine AntilipschitzWith.of_le_mul_dist fun a b => ?_
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, Real.coe_toNNReal _ (le_max_right _ _)]
      exact hbelow' (a - b)
    have hclosed := hanti.isClosed_range (continuumSynthesis hx hc).uniformContinuous
    have huniv : Set.range (continuumSynthesis hx hc) = univ := by
      rw [← hclosed.closure_eq]
      exact (denseRange_continuumSynthesis hx hc).closure_range
    exact not_surjective_continuumSynthesis hx hc (Set.range_eq_univ.1 huniv)

omit hx hc

/-! ## Theorem ZDIA-C: infinite lift action -/

section LiftAction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [TopologicalSpace.SeparableSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Theorem ZDIA-C (ZDIA.6).**  For a compact `T` and `y ∉ Ran T`, every sequence with `T b_j → y`
has `‖b_j‖ → ∞`: a bounded subsequence would have a weak limit `w`, and compactness would give
`T w = y`. -/
theorem tendsto_norm_atTop_of_tendsto_not_mem_range {T : E →L[ℂ] F} (hT : IsCompactOperator T)
    {y : F} (hy : y ∉ Set.range T) {b : ℕ → E} (hb : Tendsto (fun j => T (b j)) atTop (𝓝 y)) :
    Tendsto (fun j => ‖b j‖) atTop atTop := by
  by_contra hne
  rw [tendsto_atTop] at hne
  push Not at hne
  obtain ⟨M, hM⟩ := hne
  obtain ⟨φ, hφ, hφM⟩ := Filter.extraction_of_frequently_atTop hM
  obtain ⟨w, ψ, hψ, hwM, hweak⟩ :=
    exists_weaklyConvergent_subseq_of_bounded (fun n => b (φ n)) M fun n => (hφM n).le
  have hM0 : 0 < M := lt_of_le_of_lt (norm_nonneg _) (hφM 0)
  set K : ℝ := 2 * M + 1 with hK
  have hK0 : 0 < K := by positivity
  set u : ℕ → E := fun n => b (φ (ψ n)) with hu
  have hx1 : ∀ n, ‖((K⁻¹ : ℝ) : ℂ) • (u n - w)‖ ≤ 1 := by
    intro n
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hK0).le]
    have h1 : ‖u n - w‖ ≤ 2 * M :=
      (norm_sub_le _ _).trans (by linarith [(hφM (ψ n)).le, hwM])
    rw [inv_mul_le_iff₀ hK0]
    linarith
  have hxw : ∀ z : E, Tendsto (fun n => ⟪z, ((K⁻¹ : ℝ) : ℂ) • (u n - w)⟫_ℂ) atTop (𝓝 0) := by
    intro z
    have h1 : Tendsto (fun n => ⟪u n - w, z⟫_ℂ) atTop (𝓝 0) := by
      have := (hweak z).sub_const ⟪w, z⟫_ℂ
      simpa [hu, inner_sub_left] using this
    have h2 := ((Complex.continuous_conj.tendsto 0).comp h1).const_mul ((K⁻¹ : ℝ) : ℂ)
    simp only [map_zero, mul_zero] at h2
    refine h2.congr fun n => ?_
    simp only [Function.comp_apply, inner_smul_right, inner_conj_symm]
  have hT0 := tendsto_norm_compact_of_weaklyNull T hT _ hx1 hxw
  have hTu : Tendsto (fun n => T (u n)) atTop (𝓝 (T w)) := by
    have h1 := hT0.const_smul ((K : ℝ) : ℂ)
    rw [smul_zero] at h1
    have h2 : (fun n => ((K : ℝ) : ℂ) • T (((K⁻¹ : ℝ) : ℂ) • (u n - w))) = fun n => T (u n) - T w := by
      funext n
      rw [map_smul, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hK0.ne', Complex.ofReal_one,
        one_smul, map_sub]
    rw [h2] at h1
    simpa using h1.add_const (T w)
  have hby : Tendsto (fun n => T (u n)) atTop (𝓝 y) := hb.comp (hφ.comp hψ).tendsto_atTop
  exact hy ⟨w, tendsto_nhds_unique hTu hby⟩

/-- **(ZDIA.7)** The approximation action `L_ε(y) = inf {‖b‖² : ‖T b - y‖ ≤ ε}`. -/
def liftAction (T : E →L[ℂ] F) (y : F) (ε : ℝ) : ℝ :=
  sInf {a : ℝ | ∃ b : E, ‖T b - y‖ ≤ ε ∧ a = ‖b‖ ^ 2}

omit [CompleteSpace E] [TopologicalSpace.SeparableSpace E] [CompleteSpace F] in
/-- **(ZDIA.7)** For dense range, every `ε > 0` admits approximating lifts, so `L_ε(y)` is a finite
infimum, and it is nonnegative. -/
theorem liftAction_spec {T : E →L[ℂ] F} (hd : DenseRange T) (y : F) {ε : ℝ} (hε : 0 < ε) :
    {a : ℝ | ∃ b : E, ‖T b - y‖ ≤ ε ∧ a = ‖b‖ ^ 2}.Nonempty ∧ 0 ≤ liftAction T y ε := by
  refine ⟨?_, Real.sInf_nonneg fun a ⟨b, _, hab⟩ => hab ▸ sq_nonneg _⟩
  obtain ⟨b, hb⟩ := hd.exists_dist_lt y hε
  exact ⟨_, b, by rw [← dist_eq_norm, dist_comm]; exact hb.le, rfl⟩

/-- **(ZDIA.8)** `L_ε(y) → ∞` as `ε ↓ 0` whenever `y ∉ Ran T`. -/
theorem tendsto_liftAction {T : E →L[ℂ] F} (hT : IsCompactOperator T) (hd : DenseRange T) {y : F}
    (hy : y ∉ Set.range T) : Tendsto (liftAction T y) (𝓝[>] 0) atTop := by
  rw [tendsto_atTop]
  intro M
  by_contra hne
  rw [Filter.not_eventually] at hne
  have hpick : ∀ j : ℕ, ∃ ε, 0 < ε ∧ ε < 1 / ((j : ℝ) + 1) ∧ liftAction T y ε < M := by
    intro j
    have hmem : Ioo (0 : ℝ) (1 / ((j : ℝ) + 1)) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
    obtain ⟨ε, hε1, hε2⟩ := (hne.and_eventually hmem).exists
    exact ⟨ε, hε2.1, hε2.2, lt_of_not_ge hε1⟩
  choose ε hε0 hε1 hεM using hpick
  have hb : ∀ j, ∃ b : E, ‖T b - y‖ ≤ ε j ∧ ‖b‖ ^ 2 < M := by
    intro j
    obtain ⟨a, ⟨b, hb1, rfl⟩, ha⟩ :=
      exists_lt_of_csInf_lt (liftAction_spec hd y (hε0 j)).1 (hεM j)
    exact ⟨b, hb1, ha⟩
  choose b hb1 hb2 using hb
  have hconv : Tendsto (fun j => T (b j)) atTop (𝓝 y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun j => norm_nonneg _) (fun j => (hb1 j).trans (hε1 j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hinf := tendsto_norm_atTop_of_tendsto_not_mem_range hT hy hconv
  obtain ⟨j, hj⟩ := (hinf.eventually_gt_atTop (Real.sqrt M)).exists
  have hle : ‖b j‖ ≤ Real.sqrt M := by
    have := Real.abs_le_sqrt (hb2 j).le
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  exact absurd hle (not_le.2 hj)

/-! ## Canonical nuclear regularization -/

omit [CompleteSpace F] in
theorem re_inner_self_complex (v : F) : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) v

omit [CompleteSpace F] in
theorem im_inner_self_complex (v : F) : (⟪v, v⟫_ℂ).im = 0 :=
  inner_self_im (𝕜 := ℂ) v

omit [TopologicalSpace.SeparableSpace E] [CompleteSpace E] in
/-- A positive compact operator plus a positive scalar is invertible. -/
theorem isUnit_add_smul_one_of_compact {K : F →L[ℂ] F} (hK : IsCompactOperator K)
    (hpos : ∀ v, 0 ≤ (⟪v, K v⟫_ℂ).re) {ε : ℝ} (hε : 0 < ε) : IsUnit (K + (ε : ℂ) • 1) := by
  have hε' : (-(ε : ℂ)) ≠ 0 := neg_ne_zero.2 (Complex.ofReal_ne_zero.2 hε.ne')
  have hno : ¬ Module.End.HasEigenvalue ((K : F →ₗ[ℂ] F)) (-(ε : ℂ)) := by
    intro h
    obtain ⟨v, hv, hvne⟩ := h.exists_hasEigenvector
    have hKv : K v = -(ε : ℂ) • v := by
      simpa [Module.End.mem_genEigenspace_one] using hv
    have h1 := hpos v
    rw [hKv, inner_smul_right, ← Complex.ofReal_neg, Complex.re_ofReal_mul,
      ← RCLike.re_to_complex, inner_self_eq_norm_sq] at h1
    have h3 : ‖v‖ ^ 2 ≤ 0 := by nlinarith
    exact hvne (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h3 (sq_nonneg _))))
  have hs : (-(ε : ℂ)) ∉ spectrum ℂ K :=
    fun h => hno ((hK.hasEigenvalue_iff_mem_spectrum hε').mpr h)
  have hu := (spectrum.notMem_iff.mp hs).neg
  simpa only [Algebra.algebraMap_eq_smul_one, neg_smul, neg_sub, sub_neg_eq_add] using hu

omit [TopologicalSpace.SeparableSpace E] [CompleteSpace E] [CompleteSpace F] in
/-- Coercivity of `K + ε`: `ε ‖(K + ε)⁻¹ y‖ ≤ ‖y‖`. -/
theorem norm_shiftedResolvent_le {K : F →L[ℂ] F} (hpos : ∀ v, 0 ≤ (⟪v, K v⟫_ℂ).re) {ε : ℝ}
    (hu : IsUnit (K + (ε : ℂ) • 1)) (y : F) :
    ε * ‖Ring.inverse (K + (ε : ℂ) • 1) y‖ ≤ ‖y‖ := by
  set u := Ring.inverse (K + (ε : ℂ) • 1) y with hudef
  have hKu : (K + (ε : ℂ) • 1) u = y := by
    change ((K + (ε : ℂ) • 1) * Ring.inverse (K + (ε : ℂ) • 1)) y = y
    rw [Ring.mul_inverse_cancel _ hu, one_apply_eq_self]
  have h1 : ε * ‖u‖ ^ 2 ≤ ‖u‖ * ‖y‖ := by
    have h2 : (⟪u, (K + (ε : ℂ) • 1) u⟫_ℂ).re = (⟪u, K u⟫_ℂ).re + ε * ‖u‖ ^ 2 := by
      rw [add_apply, inner_add_right, smul_apply, one_apply_eq_self, inner_smul_right,
        Complex.add_re, Complex.re_ofReal_mul, re_inner_self_complex]
    have h3 : (⟪u, (K + (ε : ℂ) • 1) u⟫_ℂ).re ≤ ‖u‖ * ‖y‖ := by
      rw [hKu]
      exact (Complex.re_le_norm _).trans (norm_inner_le_norm u y)
    linarith [hpos u]
  rcases eq_or_ne ‖u‖ 0 with h0 | h0
  · rw [h0, mul_zero]
    exact norm_nonneg _
  · have hpos' : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

omit [TopologicalSpace.SeparableSpace E] in
/-- **(ZDIA.12), Tikhonov form.**  With `K = T T*`, `u = (K + ε)⁻¹ y` and `b = T* u`,
`Re ⟪y, (K + ε)⁻¹ y⟫ = ‖b‖² + ε ‖u‖²` and `T b - y = -ε u`. -/
theorem tikhonov_identity (T : E →L[ℂ] F) {ε : ℝ}
    (hu : IsUnit (T ∘L ContinuousLinearMap.adjoint T + (ε : ℂ) • 1)) (y : F) :
    (⟪y, Ring.inverse (T ∘L ContinuousLinearMap.adjoint T + (ε : ℂ) • 1) y⟫_ℂ).re =
        ‖ContinuousLinearMap.adjoint T
            (Ring.inverse (T ∘L ContinuousLinearMap.adjoint T + (ε : ℂ) • 1) y)‖ ^ 2 +
          ε * ‖Ring.inverse (T ∘L ContinuousLinearMap.adjoint T + (ε : ℂ) • 1) y‖ ^ 2 ∧
      T (ContinuousLinearMap.adjoint T
          (Ring.inverse (T ∘L ContinuousLinearMap.adjoint T + (ε : ℂ) • 1) y)) - y =
        -((ε : ℂ) • Ring.inverse (T ∘L ContinuousLinearMap.adjoint T + (ε : ℂ) • 1) y) := by
  set R := Ring.inverse (T ∘L ContinuousLinearMap.adjoint T + (ε : ℂ) • 1) with hR
  set u := R y with hudef
  have hKu : T (ContinuousLinearMap.adjoint T u) + (ε : ℂ) • u = y := by
    have : ((T ∘L ContinuousLinearMap.adjoint T + (ε : ℂ) • 1) * R) y = y := by
      rw [hR, Ring.mul_inverse_cancel _ hu, one_apply_eq_self]
    simpa [mul_apply_eq_comp, ContinuousLinearMap.comp_apply, add_apply, smul_apply] using this
  refine ⟨?_, by rw [← hKu]; abel⟩
  have hb : ‖ContinuousLinearMap.adjoint T u‖ ^ 2 = (⟪u, T (ContinuousLinearMap.adjoint T u)⟫_ℂ).re := by
    rw [← ContinuousLinearMap.adjoint_inner_left T (ContinuousLinearMap.adjoint T u) u,
      ← RCLike.re_to_complex, inner_self_eq_norm_sq]
  calc (⟪y, u⟫_ℂ).re = (⟪u, y⟫_ℂ).re := by rw [← inner_conj_symm, Complex.conj_re]
    _ = (⟪u, T (ContinuousLinearMap.adjoint T u)⟫_ℂ).re + ε * ‖u‖ ^ 2 := by
        rw [← hKu, inner_add_right, inner_smul_right, Complex.add_re, Complex.re_ofReal_mul,
          re_inner_self_complex]
    _ = _ := by rw [hb]

omit [TopologicalSpace.SeparableSpace E] in
/-- The resolvent `(T T* + ε)⁻¹`, `ε ≥ 0`, is a positive operator:
`⟪R y, y⟫ = ‖T* R y‖² + ε ‖R y‖²`. -/
theorem isPositive_resolvent (T : E →L[ℂ] F) {ε : ℝ} (hε : 0 ≤ ε)
    (hu : IsUnit (T ∘L ContinuousLinearMap.adjoint T + (ε : ℂ) • 1)) :
    (Ring.inverse (T ∘L ContinuousLinearMap.adjoint T + (ε : ℂ) • 1)).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro y
  set u := Ring.inverse (T ∘L ContinuousLinearMap.adjoint T + (ε : ℂ) • 1) y with hudef
  have hKu : T (ContinuousLinearMap.adjoint T u) + (ε : ℂ) • u = y := by
    have h := (tikhonov_identity T hu y).2
    rw [← hudef] at h
    rw [← sub_eq_zero, show T (ContinuousLinearMap.adjoint T u) + (ε : ℂ) • u - y =
      (T (ContinuousLinearMap.adjoint T u) - y) + (ε : ℂ) • u by abel, h, neg_add_cancel]
  have hval : ⟪u, y⟫_ℂ = ⟪ContinuousLinearMap.adjoint T u, ContinuousLinearMap.adjoint T u⟫_ℂ +
      (ε : ℂ) * ⟪u, u⟫_ℂ := by
    rw [← hKu, inner_add_right, inner_smul_right,
      ← ContinuousLinearMap.adjoint_inner_left T (ContinuousLinearMap.adjoint T u) u]
  have him : (⟪u, y⟫_ℂ).im = 0 := by
    rw [hval, Complex.add_im, im_inner_self_complex, Complex.im_ofReal_mul, im_inner_self_complex,
      mul_zero, add_zero]
  have hre : 0 ≤ (⟪u, y⟫_ℂ).re := by
    rw [hval, Complex.add_re, Complex.re_ofReal_mul, re_inner_self_complex, re_inner_self_complex]
    positivity
  refine ⟨Complex.ext (by simp) (by simp [him]), ?_⟩
  rw [RCLike.re_to_complex]
  exact hre

/-- **(ZDIA.12)** For a compact `T` and `y ∉ Ran T`, `Re ⟪y, (T T* + ε)⁻¹ y⟫ → ∞` as `ε ↓ 0`. -/
theorem tendsto_resolventPairing {T : E →L[ℂ] F} (hT : IsCompactOperator T) {y : F}
    (hy : y ∉ Set.range T) :
    Tendsto (fun ε : ℝ =>
      (⟪y, Ring.inverse (T ∘L ContinuousLinearMap.adjoint T + (ε : ℂ) • 1) y⟫_ℂ).re)
      (𝓝[>] 0) atTop := by
  have hK : IsCompactOperator (T ∘L ContinuousLinearMap.adjoint T) :=
    hT.comp_clm (ContinuousLinearMap.adjoint T)
  have hpos : ∀ v, 0 ≤ (⟪v, (T ∘L ContinuousLinearMap.adjoint T) v⟫_ℂ).re := by
    intro v
    rw [ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.adjoint_inner_left T (ContinuousLinearMap.adjoint T v) v,
      ← RCLike.re_to_complex, inner_self_eq_norm_sq]
    positivity
  rw [tendsto_atTop]
  intro M
  by_contra hne
  rw [Filter.not_eventually] at hne
  have hpick : ∀ j : ℕ, ∃ ε, 0 < ε ∧ ε < 1 / ((j : ℝ) + 1) ∧
      (⟪y, Ring.inverse (T ∘L ContinuousLinearMap.adjoint T + (ε : ℂ) • 1) y⟫_ℂ).re < M := by
    intro j
    have hmem : Ioo (0 : ℝ) (1 / ((j : ℝ) + 1)) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
    obtain ⟨ε, hε1, hε2⟩ := (hne.and_eventually hmem).exists
    exact ⟨ε, hε2.1, hε2.2, lt_of_not_ge hε1⟩
  choose ε hε0 hε1 hεM using hpick
  set b : ℕ → E := fun j => ContinuousLinearMap.adjoint T
    (Ring.inverse (T ∘L ContinuousLinearMap.adjoint T + (ε j : ℂ) • 1) y) with hbdef
  have hspec := fun j => tikhonov_identity T (isUnit_add_smul_one_of_compact hK hpos (hε0 j)) y
  have hM0 : 0 ≤ M := by
    have := (hspec 0).1
    have h1 := hεM 0
    have h2 : 0 ≤ ‖b 0‖ ^ 2 + ε 0 * ‖Ring.inverse (T ∘L ContinuousLinearMap.adjoint T +
      (ε 0 : ℂ) • 1) y‖ ^ 2 := by have := hε0 0; positivity
    linarith
  have hbnd : ∀ j, ‖b j‖ ^ 2 ≤ M := by
    intro j
    have h1 := (hspec j).1
    have h2 := hεM j
    have : 0 ≤ ε j * ‖Ring.inverse (T ∘L ContinuousLinearMap.adjoint T + (ε j : ℂ) • 1) y‖ ^ 2 := by
      have := hε0 j; positivity
    linarith
  have hdist : ∀ j, ‖T (b j) - y‖ ^ 2 ≤ ε j * M := by
    intro j
    rw [(hspec j).2, norm_neg, norm_smul, Complex.norm_real, Real.norm_of_nonneg (hε0 j).le, mul_pow]
    have h1 := (hspec j).1
    have h2 := hεM j
    have h3 : 0 ≤ ‖b j‖ ^ 2 := sq_nonneg _
    nlinarith [hε0 j]
  have hconv : Tendsto (fun j => T (b j)) atTop (𝓝 y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : Tendsto (fun j : ℕ => Real.sqrt (1 / ((j : ℝ) + 1) * M)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const M).sqrt
      simpa using this
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hsq
    rw [← Real.sqrt_sq (norm_nonneg (T (b j) - y))]
    exact Real.sqrt_le_sqrt ((hdist j).trans (mul_le_mul_of_nonneg_right (hε1 j).le hM0))
  have hinf := tendsto_norm_atTop_of_tendsto_not_mem_range hT hy hconv
  obtain ⟨j, hj⟩ := (hinf.eventually_gt_atTop (Real.sqrt M)).exists
  have hle : ‖b j‖ ≤ Real.sqrt M := by
    have := Real.abs_le_sqrt (hbnd j)
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  exact absurd hle (not_le.2 hj)

end LiftAction

/-! ## The Euler specialization -/

include hx hc

/-- **(ZDIA.8)** Every nonzero finite active Euler packet has divergent approximation action. -/
theorem tendsto_liftAction_eulerPacket (F : Finset AtomLabel)
    (hF : ∀ n ∈ F, 0 < ArithmeticFunction.vonMangoldt (n : ℕ)) (z : AtomLabel → ℂ)
    (hz : ∃ n ∈ F, z n ≠ 0) :
    Tendsto (liftAction (continuumSynthesis hx hc) (∑ n ∈ F, z n • eulerColumn x c n)) (𝓝[>] 0)
      atTop :=
  tendsto_liftAction (isCompactOperator_continuumSynthesis hx hc)
    (denseRange_continuumSynthesis hx hc) (eulerPacket_not_mem_range hx hc F hF z hz)

omit hx hc

/-- The label basis vector `e_n ∈ ℓ²(n ≥ 2)`. -/
def labelBasisVec (n : AtomLabel) : Lp ℂ 2 (Measure.count : Measure AtomLabel) :=
  indicatorConstLp 2 (measurableSet_singleton n) (by rw [Measure.count_singleton]; exact ENNReal.one_ne_top)
    (1 : ℂ)

/-- The atomic synthesis sends `e_n` to the Euler column `y_n = a_n f_{log n}`. -/
theorem atomicSynthesis_labelBasisVec (hx : 0 ≤ x) (hc : 0 ≤ c) (n : AtomLabel) :
    atomicSynthesis hx hc (labelBasisVec n) = eulerColumn x c n := by
  refine Lp.ext ?_
  filter_upwards [(atomicKernel hx hc).op_coeFn (labelBasisVec n),
    Lp.coeFn_smul (atomicCoefficient x c n : ℂ) (radialLp (log_pos_of_atomLabel n)),
    radialLp_coeFn (log_pos_of_atomLabel n)] with r h1 h2 h3
  rw [atomicSynthesis, h1, eulerColumn, h2, Pi.smul_apply, h3, SqIntKernel.apply]
  have hcoe : (labelBasisVec n : AtomLabel → ℂ) =ᵐ[Measure.count] Set.indicator {n} fun _ => (1 : ℂ) :=
    indicatorConstLp_coeFn
  rw [integral_congr_ae (hcoe.mono fun m hm => by rw [hm])]
  simp_rw [← Set.indicator_mul_right]
  rw [integral_indicator (measurableSet_singleton n), integral_singleton, Measure.real,
    Measure.count_singleton, ENNReal.toReal_one, one_smul, mul_one, smul_eq_mul]
  change ((atomicCoefficient x c n * burnolRadial (Real.log (n : ℕ)) r : ℝ) : ℂ) = _
  push_cast
  ring

include hx hc

theorem isUnit_continuumCovariance_add {ε : ℝ} (hε : 0 < ε) :
    IsUnit (continuumSynthesis hx hc ∘L ContinuousLinearMap.adjoint (continuumSynthesis hx hc) +
      (ε : ℂ) • 1) := by
  refine isUnit_add_smul_one_of_compact ((isCompactOperator_continuumSynthesis hx hc).comp_clm _)
    (fun v => ?_) hε
  rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left, re_inner_self_complex]
  positivity

/-- **(ZDIA.9)** The nuclear lift-action family `C_ε = A_E* (K₀ + ε)⁻¹ A_E`, `K₀ = A₀ A₀*`. -/
def nuclearLiftAction (ε : ℝ) :
    Lp ℂ 2 (Measure.count : Measure AtomLabel) →L[ℂ] Lp ℂ 2 (Measure.count : Measure AtomLabel) :=
  ContinuousLinearMap.adjoint (atomicSynthesis hx.le hc.le) ∘L
    (Ring.inverse (continuumSynthesis hx hc ∘L ContinuousLinearMap.adjoint (continuumSynthesis hx hc) +
      (ε : ℂ) • 1) ∘L atomicSynthesis hx.le hc.le)

/-- **(ZDIA.11)** The entries of `C_ε` are `⟪y_n, (K₀ + ε)⁻¹ y_m⟫`: one continuum covariance for the
whole atomic family. -/
theorem inner_nuclearLiftAction (ε : ℝ) (n m : AtomLabel) :
    ⟪labelBasisVec n, nuclearLiftAction hx hc ε (labelBasisVec m)⟫_ℂ =
      ⟪eulerColumn x c n, Ring.inverse (continuumSynthesis hx hc ∘L
        ContinuousLinearMap.adjoint (continuumSynthesis hx hc) + (ε : ℂ) • 1) (eulerColumn x c m)⟫_ℂ := by
  rw [nuclearLiftAction, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.comp_apply, atomicSynthesis_labelBasisVec, atomicSynthesis_labelBasisVec]

/-- **(ZDIA.9)–(ZDIA.10)** `C_ε` is positive, a product of Hilbert–Schmidt operators (trace class),
and `0 ≤ Tr C_ε ≤ ε⁻¹ ‖A_E‖²_HS ≤ ε⁻¹ B_base`. -/
theorem nuclearLiftAction_spec {ε : ℝ} (hε : 0 < ε) :
    (nuclearLiftAction hx hc ε).IsPositive ∧
      nuclearLiftAction hx hc ε = ContinuousLinearMap.adjoint (atomicSynthesis hx.le hc.le) ∘L
        (Ring.inverse (continuumSynthesis hx hc ∘L ContinuousLinearMap.adjoint
          (continuumSynthesis hx hc) + (ε : ℂ) • 1) ∘L atomicSynthesis hx.le hc.le) ∧
      ContinuousLinearMap.IsHilbertSchmidt (ContinuousLinearMap.adjoint (atomicSynthesis hx.le hc.le)) ∧
      ContinuousLinearMap.IsHilbertSchmidt (Ring.inverse (continuumSynthesis hx hc ∘L
        ContinuousLinearMap.adjoint (continuumSynthesis hx hc) + (ε : ℂ) • 1) ∘L
          atomicSynthesis hx.le hc.le) ∧
      0 ≤ (ContinuousLinearMap.opTrace (nuclearLiftAction hx hc ε)).re ∧
      (ContinuousLinearMap.opTrace (nuclearLiftAction hx hc ε)).re ≤
        ε⁻¹ * ContinuousLinearMap.hsNormSq (atomicSynthesis hx.le hc.le) ∧
      ε⁻¹ * ContinuousLinearMap.hsNormSq (atomicSynthesis hx.le hc.le) ≤
        ε⁻¹ * RHTower.routePPrimitiveBaseCauchyCubicTraceBudget := by
  set A0 := continuumSynthesis hx hc
  set AE := atomicSynthesis hx.le hc.le
  have hu := isUnit_continuumCovariance_add hx hc hε
  set R := Ring.inverse (A0 ∘L ContinuousLinearMap.adjoint A0 + (ε : ℂ) • 1) with hR
  have hAE := isHilbertSchmidt_atomicSynthesis hx.le hc.le
  -- positivity of the resolvent
  have hRpos : R.IsPositive := isPositive_resolvent A0 hε.le hu
  have hpair : ∀ v, (⟪AE v, R (AE v)⟫_ℂ).re ≤ ε⁻¹ * ‖AE v‖ ^ 2 := by
    intro v
    have h1 := norm_shiftedResolvent_le (K := A0 ∘L ContinuousLinearMap.adjoint A0) (fun w => by
      rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left,
        re_inner_self_complex]
      positivity) hu (AE v)
    have h2 : (⟪AE v, R (AE v)⟫_ℂ).re ≤ ‖AE v‖ * ‖R (AE v)‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    have h3 : ‖R (AE v)‖ ≤ ‖AE v‖ / ε := by
      rw [le_div_iff₀ hε]
      linarith [mul_comm ε ‖R (AE v)‖]
    calc (⟪AE v, R (AE v)⟫_ℂ).re ≤ ‖AE v‖ * ‖R (AE v)‖ := h2
      _ ≤ ‖AE v‖ * (‖AE v‖ / ε) := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = ε⁻¹ * ‖AE v‖ ^ 2 := by field_simp
  have hsum : Summable fun i => ⟪ContinuousLinearMap.hsBasis ℂ (Lp ℂ 2 (Measure.count : Measure AtomLabel)) i,
      nuclearLiftAction hx hc ε (ContinuousLinearMap.hsBasis ℂ _ i)⟫_ℂ :=
    ContinuousLinearMap.summable_inner_diag_comp hAE.adjoint (hAE.comp_left R) _
  have hdiag : ∀ i, ⟪ContinuousLinearMap.hsBasis ℂ (Lp ℂ 2 (Measure.count : Measure AtomLabel)) i,
      nuclearLiftAction hx hc ε (ContinuousLinearMap.hsBasis ℂ _ i)⟫_ℂ =
        ⟪AE (ContinuousLinearMap.hsBasis ℂ _ i), R (AE (ContinuousLinearMap.hsBasis ℂ _ i))⟫_ℂ := fun i => by
    rw [nuclearLiftAction, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.comp_apply]
  refine ⟨hRpos.adjoint_conj AE, rfl, hAE.adjoint, hAE.comp_left R, ?_, ?_, ?_⟩
  · rw [ContinuousLinearMap.opTrace, Complex.re_tsum hsum]
    refine tsum_nonneg fun i => ?_
    rw [hdiag]
    have := hRpos.re_inner_nonneg_right (AE (ContinuousLinearMap.hsBasis ℂ _ i))
    rwa [RCLike.re_to_complex] at this
  · rw [ContinuousLinearMap.opTrace, Complex.re_tsum hsum, ContinuousLinearMap.hsNormSq,
      ← tsum_mul_left]
    refine (Complex.reCLM.summable hsum).tsum_le_tsum (fun i => ?_)
      ((show ContinuousLinearMap.IsHilbertSchmidt AE from hAE).mul_left ε⁻¹)
    rw [hdiag]
    exact hpair _
  · exact mul_le_mul_of_nonneg_left (hsNormSq_atomicSynthesis hx.le hc.le).2.1
      (inv_nonneg.2 hε.le)

/-- **(ZDIA.12)** Every active diagonal entry of the nuclear lift action diverges as `ε ↓ 0`. -/
theorem tendsto_nuclearLiftAction_diag (n : AtomLabel)
    (hn : 0 < ArithmeticFunction.vonMangoldt (n : ℕ)) :
    Tendsto (fun ε : ℝ => (⟪labelBasisVec n, nuclearLiftAction hx hc ε (labelBasisVec n)⟫_ℂ).re)
      (𝓝[>] 0) atTop := by
  simp_rw [inner_nuclearLiftAction]
  have hy := eulerPacket_not_mem_range hx hc {n} (by simpa using hn) (fun _ => 1)
    ⟨n, by simp, one_ne_zero⟩
  simp only [Finset.sum_singleton, one_smul] at hy
  exact tendsto_resolventPairing (isCompactOperator_continuumSynthesis hx hc) hy

end GaloisForLFunctions.HTGeometry
