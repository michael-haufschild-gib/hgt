import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-!
# Phase packets reflect the order of finite measures

For a finite phase packet `p_{t,z}(x) = Σ_j z_j e^{-i t_j x}` and a finite measure `ν` on `ℝ`,
the quadratic form `Q_ν(t,z) = Σ_{j,k} conj(z_j) z_k ν̂(t_k - t_j)` equals `∫ |p_{t,z}|² dν`.

The main theorem is order reflection: for finite measures `N` and `P`, `N ≤ P` holds exactly when
`∫ |p|² dN ≤ ∫ |p|² dP` for every phase packet, and packets with rational frequencies already
suffice.  The proof periodizes a compactly supported test on a circle of period `2πK`, approximates
its square root uniformly by trigonometric polynomials (Stone–Weierstrass on `AddCircle`), passes
from compactly supported to bounded continuous tests by cutoff, from bounded continuous tests to
closed sets by outer approximation, and to all Borel sets by inner regularity.

For a signed measure `η` with Jordan parts `η⁺, η⁻` this gives `η ≥ 0` iff every packet energy is
nonnegative, and the phase kernels `(η̂(t_k - t_j))_{j,k}` reconstruct `η`.
-/

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PhaseKernel

/-! ## Phase packets and the quadratic identity -/

/-- `(FKA.2)`  The finite phase packet `p_{t,z}(x) = Σ_j z_j e^{-i t_j x}`. -/
def phasePacket {m : ℕ} (t : Fin m → ℝ) (z : Fin m → ℂ) (x : ℝ) : ℂ :=
  ∑ j, z j * cexp (-((t j : ℂ) * x * I))

/-- A packet has rational phases when every frequency is rational. -/
def IsRationalPacket {m : ℕ} (t : Fin m → ℝ) : Prop := ∀ j, ∃ q : ℚ, t j = q

theorem continuous_phasePacket {m : ℕ} (t : Fin m → ℝ) (z : Fin m → ℂ) :
    Continuous (phasePacket t z) := by
  unfold phasePacket
  fun_prop

theorem norm_cexp_phase (s x : ℝ) : ‖cexp (-((s : ℂ) * x * I))‖ = 1 := by
  rw [show -((s : ℂ) * x * I) = ((-(s * x) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem norm_phasePacket_le {m : ℕ} (t : Fin m → ℝ) (z : Fin m → ℂ) (x : ℝ) :
    ‖phasePacket t z x‖ ≤ ∑ j, ‖z j‖ := by
  unfold phasePacket
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_cexp_phase, mul_one]

/-- `(FKA.1)`  The Fourier transform `ν̂(t) = ∫ e^{-itx} dν(x)` of a finite measure. -/
def fourierTransform (ν : Measure ℝ) (t : ℝ) : ℂ :=
  ∫ x, cexp (-((t : ℂ) * x * I)) ∂ν

/-- `(FKA.2)`  The packet quadratic form `Q_ν(t,z) = Σ_{j,k} conj(z_j) z_k ν̂(t_k - t_j)`. -/
def packetForm (ν : Measure ℝ) {m : ℕ} (t : Fin m → ℝ) (z : Fin m → ℂ) : ℂ :=
  ∑ j, ∑ k, conj (z j) * z k * fourierTransform ν (t k - t j)

/-- The packet energy `∫ |p_{t,z}|² dν`. -/
def packetEnergy (ν : Measure ℝ) {m : ℕ} (t : Fin m → ℝ) (z : Fin m → ℂ) : ℝ :=
  ∫ x, ‖phasePacket t z x‖ ^ 2 ∂ν

theorem integrable_of_continuous_bounded {ν : Measure ℝ} [IsFiniteMeasure ν] {E : Type*}
    [NormedAddCommGroup E] {f : ℝ → E} (hf : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable f ν :=
  (integrable_const C).mono' hf.aestronglyMeasurable (Eventually.of_forall hC)

theorem integrable_normSq_phasePacket (ν : Measure ℝ) [IsFiniteMeasure ν] {m : ℕ}
    (t : Fin m → ℝ) (z : Fin m → ℂ) : Integrable (fun x => ‖phasePacket t z x‖ ^ 2) ν := by
  refine integrable_of_continuous_bounded ((continuous_phasePacket t z).norm.pow 2)
    (C := (∑ j, ‖z j‖) ^ 2) fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_phasePacket_le t z x) 2

theorem packetEnergy_nonneg (ν : Measure ℝ) {m : ℕ} (t : Fin m → ℝ) (z : Fin m → ℂ) :
    0 ≤ packetEnergy ν t z :=
  integral_nonneg fun _ => by positivity

theorem normSq_phasePacket {m : ℕ} (t : Fin m → ℝ) (z : Fin m → ℂ) (x : ℝ) :
    ((‖phasePacket t z x‖ ^ 2 : ℝ) : ℂ) =
      ∑ j, ∑ k, conj (z j) * z k * cexp (-(((t k - t j : ℝ) : ℂ) * x * I)) := by
  push_cast
  rw [← Complex.conj_mul']
  unfold phasePacket
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, ← Complex.exp_conj]
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [show conj (z j) * cexp (-((t j : ℂ) * x * -I)) * (z k * cexp (-((t k : ℂ) * x * I))) =
      conj (z j) * z k * (cexp (-((t j : ℂ) * x * -I)) * cexp (-((t k : ℂ) * x * I))) by ring,
    ← Complex.exp_add]
  congr 2
  ring

/-- `(FKA.5)`  **Fourier quadratic identity.**  `Q_ν(t,z) = ∫ |p_{t,z}|² dν`. -/
theorem packetForm_eq_packetEnergy (ν : Measure ℝ) [IsFiniteMeasure ν] {m : ℕ}
    (t : Fin m → ℝ) (z : Fin m → ℂ) : packetForm ν t z = (packetEnergy ν t z : ℂ) := by
  have hint : ∀ s : ℝ, Integrable (fun x : ℝ => cexp (-((s : ℂ) * x * I))) ν := fun s =>
    integrable_of_continuous_bounded (by fun_prop) (C := 1) fun x => (norm_cexp_phase s x).le
  unfold packetEnergy
  rw [← integral_complex_ofReal]
  simp_rw [normSq_phasePacket]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    (hint (t k - t j)).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => (hint (t k - t j)).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]
  rfl

/-! ## Rational phase approximation of compactly supported tests -/

/-- A finite measure gives vanishing mass to the far tails `{n ≤ |x|}`. -/
theorem tendsto_measure_tail (ρ : Measure ℝ) [IsFiniteMeasure ρ] :
    Tendsto (fun n : ℕ => ρ {x : ℝ | (n : ℝ) ≤ |x|}) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := ρ) (s := fun n : ℕ => {x : ℝ | (n : ℝ) ≤ |x|})
    (fun n => (measurableSet_le measurable_const continuous_abs.measurable).nullMeasurableSet)
    (fun a b hab x hx => by
      simp only [mem_setOf_eq] at hx ⊢
      exact le_trans (by exact_mod_cast hab) hx) ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ n : ℕ, {x : ℝ | (n : ℝ) ≤ |x|}) = ∅ := by
    ext x
    simp only [mem_iInter, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall, not_le]
    exact exists_nat_gt |x|
  rw [hempty, measure_empty] at h
  exact h

/-- **Rational phase approximation.**  A continuous compactly supported test is approximated in
`L¹(ρ)` by phase packets with rational frequencies, uniformly bounded by `M + 1`. -/
theorem exists_rationalPacket_approx (ρ : Measure ℝ) [IsFiniteMeasure ρ] {φ : ℝ → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (m : ℕ) (t : Fin m → ℝ) (z : Fin m → ℂ), IsRationalPacket t ∧
      (∀ x, ‖phasePacket t z x‖ ≤ M + 1) ∧ ∫ x, ‖phasePacket t z x - φ x‖ ∂ρ < ε := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hs.isCompact.isBounded
  have hvan : ∀ x : ℝ, r < |x| → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have h := hr hmem
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h
      linarith
  have hε' : 0 < ε / (2 * (M + 1)) := by positivity
  have hsmall : ∀ᶠ n : ℕ in atTop,
      ρ {x : ℝ | (n : ℝ) ≤ |x|} < ENNReal.ofReal (ε / (2 * (M + 1))) :=
    (tendsto_measure_tail ρ).eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε'))
  obtain ⟨K, hKsmall, hK1, hKr⟩ := (hsmall.and ((eventually_ge_atTop 1).and
    (tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop r)))).exists
  have hK0 : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hpiK : (K : ℝ) ≤ Real.pi * K := by nlinarith [Real.two_le_pi]
  set L : ℝ := 2 * Real.pi * K with hLdef
  have hL : 0 < L := by positivity
  haveI : Fact (0 < L) := ⟨hL⟩
  set a : ℝ := -(Real.pi * K) with hadef
  have haL : a + L = Real.pi * K := by rw [hadef, hLdef]; ring
  have hφa : φ a = 0 := hvan a (by rw [hadef, abs_neg, abs_of_pos (by positivity)]; linarith)
  have hφaL : φ (a + L) = 0 := hvan (a + L) (by rw [haL, abs_of_pos (by positivity)]; linarith)
  let G : C(AddCircle L, ℂ) :=
    ⟨AddCircle.liftIco L a φ, AddCircle.liftIco_continuous (by rw [hφa, hφaL]) hφ.continuousOn⟩
  have hGM : ‖G‖ ≤ M := (G.norm_le hM0).mpr fun y => hM _
  have hGx : ∀ x ∈ Ico a (a + L), G (x : AddCircle L) = φ x := fun x hx =>
    AddCircle.liftIco_coe_apply hx
  set δ : ℝ := min 1 (ε / (2 * (ρ.real univ + 1))) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hmem : G ∈ closure (Submodule.span ℂ (range (fourier (T := L))) :
      Set C(AddCircle L, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    trivial
  obtain ⟨b, hbspan, hGb⟩ := Metric.mem_closure_iff.mp hmem δ hδpos
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hbspan
  let e := c.support.equivFin
  let t : Fin c.support.card → ℝ := fun j => -(((e.symm j : ℤ) : ℝ) / K)
  let z : Fin c.support.card → ℂ := fun j => c (e.symm j)
  have hb : ∀ x : ℝ, phasePacket t z x = b (x : AddCircle L) := by
    intro x
    rw [← hc]
    simp only [phasePacket, Finsupp.sum, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      fourier_coe_apply, smul_eq_mul, t, z]
    rw [← Finset.sum_coe_sort c.support]
    refine Fintype.sum_equiv e.symm _ _ fun j => ?_
    congr 2
    rw [hLdef]
    have hKc : (K : ℂ) ≠ 0 := by exact_mod_cast (show (K : ℝ) ≠ 0 by positivity)
    have hpic : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  have hbnorm : ‖b‖ ≤ M + δ := by
    calc ‖b‖ = ‖G + (b - G)‖ := by rw [add_sub_cancel]
      _ ≤ ‖G‖ + ‖b - G‖ := norm_add_le _ _
      _ ≤ M + δ := by
        rw [← dist_eq_norm, dist_comm]
        exact add_le_add hGM hGb.le
  have hbound : ∀ x, ‖phasePacket t z x‖ ≤ M + 1 := fun x => by
    rw [hb]
    exact (b.norm_coe_le_norm _).trans (hbnorm.trans (by linarith))
  refine ⟨c.support.card, t, z, fun j => ⟨-(((e.symm j : ℤ) : ℚ) / K), by
    simp only [t]; push_cast; ring⟩, hbound, ?_⟩
  set T : Set ℝ := {x : ℝ | (K : ℝ) ≤ |x|} with hTdef
  have hT : MeasurableSet T := measurableSet_le measurable_const continuous_abs.measurable
  have hpoint : ∀ x,
      ‖phasePacket t z x - φ x‖ ≤ δ + (M + 1) * T.indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ Ico a (a + L)
    · rw [hb, ← hGx x hx]
      have h1 : ‖b (x : AddCircle L) - G (x : AddCircle L)‖ ≤ δ := by
        rw [← ContinuousMap.sub_apply]
        refine ((b - G).norm_coe_le_norm _).trans ?_
        rw [← dist_eq_norm, dist_comm]
        exact hGb.le
      have h2 : 0 ≤ (M + 1) * T.indicator (fun _ => (1 : ℝ)) x :=
        mul_nonneg (by linarith) (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
      linarith
    · have hfar : Real.pi * K ≤ |x| := by
        rw [Set.mem_Ico, not_and_or, not_le, not_lt] at hx
        rcases hx with hx | hx
        · rw [hadef] at hx
          rw [abs_of_neg (by nlinarith [Real.pi_pos])]
          linarith
        · rw [haL] at hx
          rw [abs_of_pos (by nlinarith [Real.pi_pos])]
          exact hx
      have hxT : x ∈ T := by
        simp only [hTdef, mem_setOf_eq]
        linarith
      rw [hvan x (by linarith), sub_zero, Set.indicator_of_mem hxT, mul_one]
      linarith [hbound x]
  have hint1 : Integrable (fun x => ‖phasePacket t z x - φ x‖) ρ :=
    integrable_of_continuous_bounded ((continuous_phasePacket t z).sub hφ).norm
      (C := M + 1 + M) fun x => by
        rw [norm_norm]
        exact (norm_sub_le _ _).trans (add_le_add (hbound x) (hM x))
  have hint2 : Integrable (fun x => δ + (M + 1) * T.indicator (fun _ => (1 : ℝ)) x) ρ :=
    (integrable_const δ).add (((integrable_const (1 : ℝ)).indicator hT).const_mul _)
  have hTreal : ρ.real T < ε / (2 * (M + 1)) := by
    rw [measureReal_def]
    exact ENNReal.toReal_lt_of_lt_ofReal hKsmall
  have hδρ : δ * ρ.real univ < ε / 2 := by
    have h0 : 0 ≤ ρ.real univ := measureReal_nonneg
    calc δ * ρ.real univ ≤ ε / (2 * (ρ.real univ + 1)) * ρ.real univ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) h0
      _ < ε / 2 := by
        rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  calc ∫ x, ‖phasePacket t z x - φ x‖ ∂ρ
      ≤ ∫ x, (δ + (M + 1) * T.indicator (fun _ => (1 : ℝ)) x) ∂ρ :=
        integral_mono hint1 hint2 hpoint
    _ = δ * ρ.real univ + (M + 1) * ρ.real T := by
        rw [integral_add (integrable_const δ)
          (((integrable_const (1 : ℝ)).indicator hT).const_mul _), integral_const,
          integral_const_mul, integral_indicator_const _ hT, smul_eq_mul, smul_eq_mul, mul_one,
          mul_comm]
    _ < ε / 2 + (M + 1) * (ε / (2 * (M + 1))) := by
        have := mul_lt_mul_of_pos_left hTreal (show (0 : ℝ) < M + 1 by linarith)
        linarith
    _ = ε := by field_simp; ring

/-! ## Order reflection -/

section OrderReflection

variable {P N : Measure ℝ} [IsFiniteMeasure P] [IsFiniteMeasure N]

omit [IsFiniteMeasure N] in
theorem packetEnergy_mono (hle : N ≤ P) {m : ℕ} (t : Fin m → ℝ) (z : Fin m → ℂ) :
    packetEnergy N t z ≤ packetEnergy P t z :=
  integral_mono_measure hle (Eventually.of_forall fun _ => by positivity)
    (integrable_normSq_phasePacket P t z)

/-- Rational-packet domination passes to nonnegative compactly supported continuous tests. -/
theorem integral_le_of_rationalPacket
    (h : ∀ (m : ℕ) (t : Fin m → ℝ) (z : Fin m → ℂ), IsRationalPacket t →
      packetEnergy N t z ≤ packetEnergy P t z)
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hs : HasCompactSupport φ) (h0 : ∀ x, 0 ≤ φ x) :
    ∫ x, φ x ∂N ≤ ∫ x, φ x ∂P := by
  set ψ : ℝ → ℂ := fun x => ((Real.sqrt (φ x) : ℝ) : ℂ) with hψdef
  have hψc : Continuous ψ := Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp hφ)
  have hψs : HasCompactSupport ψ :=
    hs.comp_left (g := fun r : ℝ => ((Real.sqrt r : ℝ) : ℂ)) (by simp)
  obtain ⟨M, hM⟩ := hψc.bounded_above_of_compact_support hψs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hψsq : ∀ x, ‖ψ x‖ ^ 2 = φ x := fun x => by
    rw [hψdef, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (h0 x)]
  obtain ⟨C0, hC0⟩ := hφ.bounded_above_of_compact_support hs
  have hφi : ∀ (μ : Measure ℝ) [IsFiniteMeasure μ], Integrable φ μ := fun μ _ =>
    integrable_of_continuous_bounded hφ hC0
  set C : ℝ := 2 * M + 1 with hCdef
  have hC : 0 < C := by positivity
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨m, t, z, ht, hbd, happ⟩ :=
    exists_rationalPacket_approx (P + N) hψc hψs hM (ε := ε / C) (by positivity)
  have hdi : ∀ (μ : Measure ℝ) [IsFiniteMeasure μ],
      Integrable (fun x => ‖phasePacket t z x - ψ x‖) μ := fun μ _ =>
    integrable_of_continuous_bounded ((continuous_phasePacket t z).sub hψc).norm
      (C := M + 1 + M) fun x => by
        rw [norm_norm]
        exact (norm_sub_le _ _).trans (add_le_add (hbd x) (hM x))
  have hpt : ∀ x, |‖phasePacket t z x‖ ^ 2 - φ x| ≤ C * ‖phasePacket t z x - ψ x‖ := by
    intro x
    rw [← hψsq x, sq_sub_sq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖phasePacket t z x‖ +
      ‖ψ x‖), mul_comm]
    calc |‖phasePacket t z x‖ - ‖ψ x‖| * (‖phasePacket t z x‖ + ‖ψ x‖)
        ≤ ‖phasePacket t z x - ψ x‖ * (M + 1 + M) :=
          mul_le_mul (abs_norm_sub_norm_le _ _) (add_le_add (hbd x) (hM x)) (by positivity)
            (norm_nonneg _)
      _ = C * ‖phasePacket t z x - ψ x‖ := by rw [hCdef]; ring
  have hcmp : ∀ (μ : Measure ℝ) [IsFiniteMeasure μ],
      |packetEnergy μ t z - ∫ x, φ x ∂μ| ≤ C * ∫ x, ‖phasePacket t z x - ψ x‖ ∂μ := by
    intro μ _
    rw [packetEnergy, ← integral_sub (integrable_normSq_phasePacket μ t z) (hφi μ),
      ← integral_const_mul]
    exact abs_integral_le_integral_abs.trans (integral_mono
      ((integrable_normSq_phasePacket μ t z).sub (hφi μ)).abs ((hdi μ).const_mul C) hpt)
  have hsplit : ∫ x, ‖phasePacket t z x - ψ x‖ ∂(P + N) =
      ∫ x, ‖phasePacket t z x - ψ x‖ ∂P + ∫ x, ‖phasePacket t z x - ψ x‖ ∂N :=
    integral_add_measure (hdi P) (hdi N)
  have hEN := hcmp N
  have hEP := hcmp P
  have hE := h m t z ht
  have happ' : C * (∫ x, ‖phasePacket t z x - ψ x‖ ∂P + ∫ x, ‖phasePacket t z x - ψ x‖ ∂N) < ε := by
    rw [← hsplit]
    calc C * ∫ x, ‖phasePacket t z x - ψ x‖ ∂(P + N) < C * (ε / C) :=
          mul_lt_mul_of_pos_left happ hC
      _ = ε := by field_simp
  rw [abs_le] at hEN hEP
  nlinarith [hEN.1, hEN.2, hEP.1, hEP.2]

/-- The tent cutoff `max 0 (min 1 (R + 1 - |x|))`. -/
def tentCutoff (R x : ℝ) : ℝ := max 0 (min 1 (R + 1 - |x|))

theorem continuous_tentCutoff (R : ℝ) : Continuous (tentCutoff R) := by
  unfold tentCutoff
  fun_prop

theorem tentCutoff_nonneg (R x : ℝ) : 0 ≤ tentCutoff R x := le_max_left _ _

theorem tentCutoff_le_one (R x : ℝ) : tentCutoff R x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem tentCutoff_eq_one {R x : ℝ} (hx : |x| ≤ R) : tentCutoff R x = 1 := by
  unfold tentCutoff
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem tentCutoff_eq_zero {R x : ℝ} (hx : R + 1 < |x|) : tentCutoff R x = 0 := by
  unfold tentCutoff
  rw [min_eq_right (by linarith), max_eq_left (by linarith)]

/-- Rational-packet domination passes to nonnegative bounded continuous tests. -/
theorem integral_le_of_rationalPacket_bounded
    (h : ∀ (m : ℕ) (t : Fin m → ℝ) (z : Fin m → ℂ), IsRationalPacket t →
      packetEnergy N t z ≤ packetEnergy P t z)
    {f : ℝ → ℝ} (hf : Continuous f) {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) (h0 : ∀ x, 0 ≤ f x) :
    ∫ x, f x ∂N ≤ ∫ x, f x ∂P := by
  have hlim : ∀ (μ : Measure ℝ) [IsFiniteMeasure μ],
      Tendsto (fun n : ℕ => ∫ x, tentCutoff n x * f x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    intro μ _
    refine tendsto_integral_of_dominated_convergence (fun _ => B)
      (fun n => ((continuous_tentCutoff n).mul hf).aestronglyMeasurable) (integrable_const B)
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (tentCutoff_nonneg _ _)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (tentCutoff_le_one _ _)).trans (hB x)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop |x|)] with n hn
      rw [tentCutoff_eq_one hn, one_mul]
  refine le_of_tendsto_of_tendsto' (hlim N) (hlim P) fun n => ?_
  refine integral_le_of_rationalPacket h ((continuous_tentCutoff n).mul hf)
    (HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) ((n : ℝ) + 1)) fun x hx => ?_)
    fun x => mul_nonneg (tentCutoff_nonneg _ _) (h0 x)
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
  rw [tentCutoff_eq_zero hx, zero_mul]

/-- Rational-packet domination passes to closed sets. -/
theorem measure_le_of_rationalPacket_isClosed
    (h : ∀ (m : ℕ) (t : Fin m → ℝ) (z : Fin m → ℂ), IsRationalPacket t →
      packetEnergy N t z ≤ packetEnergy P t z)
    {F : Set ℝ} (hF : IsClosed F) : N F ≤ P F := by
  refine le_of_tendsto_of_tendsto' (HasOuterApproxClosed.tendsto_lintegral_apprSeq hF N)
    (HasOuterApproxClosed.tendsto_lintegral_apprSeq hF P) fun n => ?_
  set f := hF.apprSeq n
  have hfc : Continuous fun x => ((f x : ℝ≥0) : ℝ) := NNReal.continuous_coe.comp f.continuous
  have hfb : ∀ x, ‖((f x : ℝ≥0) : ℝ)‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, NNReal.abs_eq]
    exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hF n x
  rw [lintegral_coe_eq_integral _ (integrable_of_continuous_bounded hfc hfb),
    lintegral_coe_eq_integral _ (integrable_of_continuous_bounded hfc hfb)]
  exact ENNReal.ofReal_le_ofReal
    (integral_le_of_rationalPacket_bounded h hfc hfb fun x => (f x).2)

/-- **Order reflection by rational phase packets.** -/
theorem le_of_forall_rationalPacketEnergy_le
    (h : ∀ (m : ℕ) (t : Fin m → ℝ) (z : Fin m → ℂ), IsRationalPacket t →
      packetEnergy N t z ≤ packetEnergy P t z) : N ≤ P := by
  rw [Measure.le_iff]
  intro s hs
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨F, hFs, hF, hlt⟩ :=
    hs.exists_isClosed_lt_add (measure_ne_top N s) (ENNReal.coe_ne_zero.mpr hε.ne')
  calc N s ≤ N F + ε := hlt.le
    _ ≤ P F + ε := add_le_add (measure_le_of_rationalPacket_isClosed h hF) le_rfl
    _ ≤ P s + ε := add_le_add (measure_mono hFs) le_rfl

/-- `(FKA.6)`, measure form.  `N ≤ P` exactly when every phase packet has
`∫ |p|² dN ≤ ∫ |p|² dP`. -/
theorem le_iff_forall_packetEnergy_le :
    N ≤ P ↔ ∀ (m : ℕ) (t : Fin m → ℝ) (z : Fin m → ℂ), packetEnergy N t z ≤ packetEnergy P t z :=
  ⟨fun hle _ t z => packetEnergy_mono hle t z,
    fun h => le_of_forall_rationalPacketEnergy_le fun _ t z _ => h _ t z⟩

/-- `(FKA.13)`, measure form.  Rational phase packets already reflect the order. -/
theorem le_iff_forall_rationalPacketEnergy_le :
    N ≤ P ↔ ∀ (m : ℕ) (t : Fin m → ℝ) (z : Fin m → ℂ), IsRationalPacket t →
      packetEnergy N t z ≤ packetEnergy P t z :=
  ⟨fun hle _ t z _ => packetEnergy_mono hle t z, le_of_forall_rationalPacketEnergy_le⟩

/-- A formal difference of finite measures is nonnegative exactly when `N ≤ P`. -/
theorem toSignedMeasure_sub_nonneg_iff :
    0 ≤ P.toSignedMeasure - N.toSignedMeasure ↔ N ≤ P := by
  rw [VectorMeasure.le_iff, Measure.le_iff]
  refine forall_congr' fun s => imp_congr_right fun hs => ?_
  rw [sub_apply, Measure.toSignedMeasure_apply_measurable hs,
    Measure.toSignedMeasure_apply_measurable hs, zero_apply, sub_nonneg,
    measureReal_def, measureReal_def,
    ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]

end OrderReflection

/-! ## Signed measures -/

/-- The packet energy `Q_η(t,z) = ∫ |p_{t,z}|² dη` of a finite signed measure, computed on its
Jordan parts. -/
def signedPacketEnergy (η : SignedMeasure ℝ) {m : ℕ} (t : Fin m → ℝ) (z : Fin m → ℂ) : ℝ :=
  packetEnergy η.toJordanDecomposition.posPart t z -
    packetEnergy η.toJordanDecomposition.negPart t z

/-- The Fourier transform `η̂(t) = ∫ e^{-itx} dη(x)` of a finite signed measure. -/
def signedFourier (η : SignedMeasure ℝ) (t : ℝ) : ℂ :=
  fourierTransform η.toJordanDecomposition.posPart t -
    fourierTransform η.toJordanDecomposition.negPart t

/-- `(FKA.2)`  The signed packet quadratic form. -/
def signedPacketForm (η : SignedMeasure ℝ) {m : ℕ} (t : Fin m → ℝ) (z : Fin m → ℂ) : ℂ :=
  ∑ j, ∑ k, conj (z j) * z k * signedFourier η (t k - t j)

/-- `(FKA.7)`  The phase kernel matrix `K_η(t) = (η̂(t_k - t_j))_{j,k}`. -/
def kernelMatrix (η : SignedMeasure ℝ) {m : ℕ} (t : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  fun j k => signedFourier η (t k - t j)

theorem signedMeasure_eq_sub (η : SignedMeasure ℝ) :
    η = η.toJordanDecomposition.posPart.toSignedMeasure -
      η.toJordanDecomposition.negPart.toSignedMeasure :=
  (SignedMeasure.toSignedMeasure_toJordanDecomposition η).symm

/-- `(FKA.5)`, signed form: `Q_η(t,z) = ∫ |p_{t,z}|² dη`. -/
theorem signedPacketForm_eq (η : SignedMeasure ℝ) {m : ℕ} (t : Fin m → ℝ) (z : Fin m → ℂ) :
    signedPacketForm η t z = (signedPacketEnergy η t z : ℂ) := by
  have h1 := packetForm_eq_packetEnergy η.toJordanDecomposition.posPart t z
  have h2 := packetForm_eq_packetEnergy η.toJordanDecomposition.negPart t z
  unfold signedPacketForm signedPacketEnergy signedFourier
  unfold packetForm at h1 h2
  push_cast
  rw [← h1, ← h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- `(FKA.6)`  **Positivity reconstruction.**  A finite signed measure is nonnegative exactly
when every phase-packet quadratic form is nonnegative. -/
theorem nonneg_iff_forall_signedPacketEnergy_nonneg (η : SignedMeasure ℝ) :
    0 ≤ η ↔ ∀ (m : ℕ) (t : Fin m → ℝ) (z : Fin m → ℂ), 0 ≤ signedPacketEnergy η t z := by
  conv_lhs => rw [signedMeasure_eq_sub η]
  rw [toSignedMeasure_sub_nonneg_iff, le_iff_forall_packetEnergy_le]
  simp only [signedPacketEnergy, sub_nonneg]

/-- `(FKA.6)` with rational phases. -/
theorem nonneg_iff_forall_rational_signedPacketEnergy_nonneg (η : SignedMeasure ℝ) :
    0 ≤ η ↔ ∀ (m : ℕ) (t : Fin m → ℝ) (z : Fin m → ℂ), IsRationalPacket t →
      0 ≤ signedPacketEnergy η t z := by
  conv_lhs => rw [signedMeasure_eq_sub η]
  rw [toSignedMeasure_sub_nonneg_iff, le_iff_forall_rationalPacketEnergy_le]
  simp only [signedPacketEnergy, sub_nonneg]

/-- The Fourier transform of a finite measure is its characteristic function at `-t`. -/
theorem fourierTransform_eq_charFun (ν : Measure ℝ) (t : ℝ) :
    fourierTransform ν t = charFun ν (-t) := by
  rw [charFun_apply, fourierTransform]
  congr 1
  funext x
  congr 1
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

theorem fourierTransform_add_measure (ν ν' : Measure ℝ) [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (t : ℝ) : fourierTransform (ν + ν') t = fourierTransform ν t + fourierTransform ν' t := by
  have hint : ∀ (μ : Measure ℝ) [IsFiniteMeasure μ],
      Integrable (fun x : ℝ => cexp (-((t : ℂ) * x * I))) μ := fun μ _ =>
    integrable_of_continuous_bounded (by fun_prop) (C := 1) fun x => (norm_cexp_phase t x).le
  exact integral_add_measure (hint ν) (hint ν')

/-- `(FKA.7)`  **Kernel reconstruction.**  The phase kernel matrices determine a finite signed
measure; already the two-time packets `(0, t)` read off its Fourier transform. -/
theorem eq_of_kernelMatrix_eq {η η' : SignedMeasure ℝ}
    (h : ∀ (m : ℕ) (t : Fin m → ℝ), kernelMatrix η t = kernelMatrix η' t) : η = η' := by
  have hF : ∀ s, signedFourier η s = signedFourier η' s := fun s => by
    have := congrFun (congrFun (h 2 ![0, s]) 0) 1
    simpa [kernelMatrix] using this
  set P := η.toJordanDecomposition.posPart
  set N := η.toJordanDecomposition.negPart
  set P' := η'.toJordanDecomposition.posPart
  set N' := η'.toJordanDecomposition.negPart
  have hmeas : P + N' = P' + N := by
    refine Measure.ext_of_charFun (funext fun s => ?_)
    rw [← neg_neg s, ← fourierTransform_eq_charFun, ← fourierTransform_eq_charFun,
      fourierTransform_add_measure, fourierTransform_add_measure]
    have := hF (-s)
    unfold signedFourier at this
    linear_combination this
  rw [signedMeasure_eq_sub η, signedMeasure_eq_sub η', sub_eq_sub_iff_add_eq_add]
  ext i hi
  have hi' := congrArg (fun μ : Measure ℝ => (μ i).toReal) hmeas
  simp only [Measure.add_apply] at hi'
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hi'
  simp only [add_apply, Measure.toSignedMeasure_apply_measurable hi, measureReal_def]
  exact hi'

end GaloisForLFunctions.HTGeometry.PhaseKernel
