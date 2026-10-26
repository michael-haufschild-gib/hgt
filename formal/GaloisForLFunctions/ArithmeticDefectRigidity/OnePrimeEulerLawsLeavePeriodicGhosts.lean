import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# One-prime Euler laws leave periodic ghosts; two primes leave a constant

Work on the log scale with Lebesgue measure. Fix `κ > 0`, `τ > 0` and a measurable `g : ℝ → ℝ`.
The one-prime law is `g − e^{κτ} g(· − τ) ∈ L²` (`lawDefect`). Its anti-causal series
`S = Σ_{i≥0} e^{−κτ(i+1)} f(· + (i+1)τ)` has energy at most `(Σ e^{−κτ(i+1)})² ∫ f²`
(`lintegral_sq_antiCausalSum_ne_top`), and the ghost `e^{−κu}(g + S)` is a.e. `τ`-periodic
(`ae_periodic_logGhost`), with `g = e^{κu}·ghost − S` identically. So one law determines `g` modulo
`L²` only up to `e^{κu}` times a `τ`-periodic function.

Two laws with incommensurable periods `τ₂, τ₃` leave a constant
(`exists_lintegral_sub_const_mul_exp_ne_top`): the ghosts differ by an `L²(e^{2κu}du)` function; a
shift by `τ₂` turns this into a `τ₃`-periodic function of finite energy on a half-line, hence zero
(`ae_eq_zero_of_periodic`); a function with two incommensurable periods is a.e. constant by
ergodicity of the irrational rotation (`exists_ae_eq_const_of_two_periods`); the constants agree
because `e^{κu}` has infinite energy.
-/

open MeasureTheory Filter Topology Set

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-! ### Periods and the lift to the circle -/

theorem ae_comp_add_right {P : ℝ → Prop} (h : ∀ᵐ u : ℝ, P u) (c : ℝ) : ∀ᵐ u : ℝ, P (u + c) :=
  (measurePreserving_add_right volume c).quasiMeasurePreserving.ae h

/-- An a.e. period is an a.e. period for every integer multiple. -/
theorem ae_periodic_intMul {φ : ℝ → ℝ} {b : ℝ} (hb : ∀ᵐ u : ℝ, φ (u + b) = φ u) (k : ℤ) :
    ∀ᵐ u : ℝ, φ (u + k * b) = φ u := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    filter_upwards [ih, ae_comp_add_right hb ((k : ℤ) * b)] with u h1 h2
    rw [show u + ((k : ℤ) + 1 : ℤ) * b = u + (k : ℤ) * b + b by push_cast; ring, h2, h1]
  | pred k ih =>
    filter_upwards [ih, ae_comp_add_right hb ((-(k : ℤ) - 1 : ℤ) * b)] with u h1 h2
    rw [show u + (-(k : ℤ) - 1 : ℤ) * b + b = u + (-(k : ℤ) : ℤ) * b by push_cast; ring] at h2
    rw [← h2, h1]

theorem ae_periodic_of_ae_eq {φ ψ : ℝ → ℝ} (hφψ : φ =ᵐ[volume] ψ) {b : ℝ}
    (hb : ∀ᵐ u : ℝ, φ (u + b) = φ u) : ∀ᵐ u : ℝ, ψ (u + b) = ψ u := by
  filter_upwards [hφψ, ae_comp_add_right hφψ b, hb] with u h1 h2 h3
  rw [← h1, ← h2, h3]

/-- The lift of a function on `ℝ` to `AddCircle b` through the fundamental domain `(0, b]`. -/
def circleLift (b : ℝ) [Fact (0 < b)] (φ : ℝ → ℝ) (θ : AddCircle b) : ℝ :=
  φ (AddCircle.equivIoc b 0 θ)

section Circle

variable {b : ℝ} [hb : Fact (0 < b)]

theorem measurable_circleLift {φ : ℝ → ℝ} (hφ : Measurable φ) : Measurable (circleLift b φ) :=
  hφ.comp (measurable_subtype_coe.comp (AddCircle.measurableEquivIoc b 0).measurable)

/-- The lift agrees with the function off a null set when the function is a.e. `b`-periodic. -/
theorem circleLift_coe_ae {φ : ℝ → ℝ} (hper : ∀ᵐ u : ℝ, φ (u + b) = φ u) :
    ∀ᵐ u : ℝ, circleLift b φ (u : AddCircle b) = φ u := by
  have hall : ∀ᵐ u : ℝ, ∀ k : ℤ, φ (u + k * b) = φ u := ae_all_iff.mpr (ae_periodic_intMul hper)
  filter_upwards [hall] with u hu
  have hmem : toIocMod hb.out 0 u ∈ Ioc 0 (0 + b) := toIocMod_mem_Ioc hb.out 0 u
  have hco : (u : AddCircle b) = ((toIocMod hb.out 0 u : ℝ) : AddCircle b) := by
    have h : (u : AddCircle b) =
        ((toIocMod hb.out 0 u + toIocDiv hb.out 0 u • b : ℝ) : AddCircle b) := by
      rw [toIocMod_add_toIocDiv_zsmul]
    rw [h, AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, add_zero]
  have hm : toIocMod hb.out 0 u = u + ((-toIocDiv hb.out 0 u : ℤ) : ℝ) * b := by
    rw [← self_sub_toIocDiv_zsmul hb.out 0 u, zsmul_eq_mul]; push_cast; ring
  rw [circleLift, hco, AddCircle.equivIoc_coe_eq hmem]
  change φ (toIocMod hb.out 0 u) = φ u
  rw [hm]
  exact hu _

/-- A null set of the circle pulls back to a null set of the line. -/
theorem volume_preimage_coe_eq_zero {N : Set (AddCircle b)} (hN : volume N = 0) :
    volume (((↑) : ℝ → AddCircle b) ⁻¹' N) = 0 := by
  have hcover : ((↑) : ℝ → AddCircle b) ⁻¹' N =
      ⋃ k : ℤ, (((↑) : ℝ → AddCircle b) ⁻¹' N ∩ Ioc (0 + k • b) (0 + (k + 1) • b)) := by
    rw [← inter_iUnion, iUnion_Ioc_add_zsmul hb.out 0, inter_univ]
  rw [hcover]
  refine measure_iUnion_null fun k => ?_
  have hmp := AddCircle.measurePreserving_mk b (0 + k • b)
  have h0 := hmp.quasiMeasurePreserving.preimage_null hN
  rw [Measure.restrict_apply' measurableSet_Ioc] at h0
  convert h0 using 3
  rw [add_smul, one_smul, add_assoc]

/-- Transfer of a.e. statements from the circle to the line. -/
theorem ae_coe_of_ae {P : AddCircle b → Prop} (h : ∀ᵐ θ : AddCircle b, P θ) :
    ∀ᵐ u : ℝ, P (u : AddCircle b) :=
  volume_preimage_coe_eq_zero (ae_iff.mp h)

/-- Transfer of a.e. statements from the line to the circle, for measurable predicates. -/
theorem ae_of_ae_coe {S : Set (AddCircle b)} (hS : MeasurableSet S)
    (h : ∀ᵐ u : ℝ, (u : AddCircle b) ∈ S) : ∀ᵐ θ : AddCircle b, θ ∈ S := by
  rw [ae_iff] at h ⊢
  have hmp := AddCircle.measurePreserving_mk b 0
  change volume Sᶜ = 0
  rw [← hmp.measure_preimage hS.compl.nullMeasurableSet]
  exact le_antisymm ((Measure.restrict_apply_le _ _).trans h.le) bot_le

/-- Every window `(t, t + b]` carries the full circle energy of an a.e. `b`-periodic function. -/
theorem setLIntegral_Ioc_eq_circle {φ : ℝ → ℝ} (hper : ∀ᵐ u : ℝ, φ (u + b) = φ u) (t : ℝ) :
    ∫⁻ u in Ioc t (t + b), ENNReal.ofReal (φ u ^ 2) =
      ∫⁻ θ : AddCircle b, ENNReal.ofReal (circleLift b φ θ ^ 2) := by
  rw [← AddCircle.lintegral_preimage b t]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [circleLift_coe_ae hper] with u hu
  rw [hu]

/-- **A periodic function of finite energy on a half-line vanishes.** -/
theorem ae_eq_zero_of_periodic {φ : ℝ → ℝ} (hφ : Measurable φ)
    (hper : ∀ᵐ u : ℝ, φ (u + b) = φ u)
    (hfin : ∫⁻ u in Ioi 0, ENNReal.ofReal (φ u ^ 2) ≠ ⊤) : ∀ᵐ u : ℝ, φ u = 0 := by
  set J := ∫⁻ θ : AddCircle b, ENNReal.ofReal (circleLift b φ θ ^ 2) with hJ
  have hblock : ∀ M : ℕ, ∫⁻ u in Ioc 0 (M * b), ENNReal.ofReal (φ u ^ 2) = M * J := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      have hun : Ioc 0 (((M + 1 : ℕ) : ℝ) * b) = Ioc 0 (M * b) ∪ Ioc (M * b) (M * b + b) := by
        rw [Ioc_union_Ioc_eq_Ioc (mul_nonneg (Nat.cast_nonneg M) hb.out.le) (by linarith [hb.out])]
        push_cast; ring_nf
      rw [hun, lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl), ih,
        setLIntegral_Ioc_eq_circle hper]
      push_cast
      ring
  have hJ0 : J = 0 := by
    by_contra hne
    obtain ⟨M, hM⟩ := ENNReal.exists_nat_mul_gt hne hfin
    have hle : ∫⁻ u in Ioc 0 (M * b), ENNReal.ofReal (φ u ^ 2) ≤
        ∫⁻ u in Ioi 0, ENNReal.ofReal (φ u ^ 2) := lintegral_mono_set Ioc_subset_Ioi_self
    rw [hblock] at hle
    exact absurd (hM.trans_le hle) (lt_irrefl _)
  have hm : Measurable fun θ => ENNReal.ofReal (circleLift b φ θ ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_circleLift hφ).pow_const 2)
  have hz : ∀ᵐ θ : AddCircle b, circleLift b φ θ = 0 := by
    have h := (lintegral_eq_zero_iff hm).mp hJ0
    filter_upwards [h] with θ hθ
    simpa using hθ
  filter_upwards [ae_coe_of_ae hz, circleLift_coe_ae hper] with u h1 h2
  rw [← h2, h1]

/-- **Two incommensurable periods force a constant.** -/
theorem exists_ae_eq_const_of_two_periods {φ : ℝ → ℝ} (hφ : Measurable φ) {a : ℝ}
    (hord : addOrderOf (a : AddCircle b) = 0) (hpb : ∀ᵐ u : ℝ, φ (u + b) = φ u)
    (hpa : ∀ᵐ u : ℝ, φ (u + a) = φ u) : ∃ c : ℝ, ∀ᵐ u : ℝ, φ u = c := by
  set Φ := circleLift b φ
  have hΦ : Measurable Φ := measurable_circleLift hφ
  have hcoe := circleLift_coe_ae hpb
  have hline : ∀ᵐ u : ℝ, (u : AddCircle b) ∈ {θ | Φ (θ + a) = Φ θ} := by
    filter_upwards [hcoe, ae_comp_add_right hcoe a, hpa] with u h1 h2 h3
    change Φ ((u : AddCircle b) + (a : AddCircle b)) = Φ u
    rw [← AddCircle.coe_add]
    exact h2.trans (h3.trans h1.symm)
  have hmeas : MeasurableSet {θ : AddCircle b | Φ (θ + a) = Φ θ} :=
    measurableSet_eq_fun (hΦ.comp (measurable_add_const _)) hΦ
  have hinv : Φ ∘ (· + (a : AddCircle b)) =ᵐ[volume] Φ := ae_of_ae_coe hmeas hline
  obtain ⟨c, hc⟩ := (AddCircle.ergodic_add_right.mpr hord).ae_eq_const_of_ae_eq_comp_ae
    hΦ.aestronglyMeasurable hinv
  refine ⟨c, ?_⟩
  filter_upwards [ae_coe_of_ae hc, hcoe] with u h1 h2
  rw [← h2]; exact h1

end Circle

/-! ### The anti-causal series of a one-prime law -/

/-- `Σ aᵢ < ∞` and `Σ aᵢyᵢ² < ∞` give `Σ aᵢyᵢ` absolutely, by `|y| ≤ (1 + y²)/2`. -/
theorem summable_mul_of_summable_mul_sq {a y : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hA : Summable a)
    (hY : Summable fun i => a i * y i ^ 2) : Summable fun i => a i * y i := by
  refine Summable.of_norm_bounded ((hA.add hY).div_const 2) fun i => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha i)]
  have h1 : |y i| ≤ (1 + y i ^ 2) / 2 := by
    nlinarith [sq_nonneg (|y i| - 1), sq_abs (y i), abs_nonneg (y i)]
  calc a i * |y i| ≤ a i * ((1 + y i ^ 2) / 2) := mul_le_mul_of_nonneg_left h1 (ha i)
    _ = (a i + a i * y i ^ 2) / 2 := by ring

/-- Weighted Cauchy–Schwarz for series: `(Σ aᵢyᵢ)² ≤ (Σ aᵢ)(Σ aᵢyᵢ²)`. -/
theorem sq_tsum_mul_le {a y : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hA : Summable a)
    (hY : Summable fun i => a i * y i ^ 2) :
    (∑' i, a i * y i) ^ 2 ≤ (∑' i, a i) * ∑' i, a i * y i ^ 2 := by
  have hay := summable_mul_of_summable_mul_sq ha hA hY
  have hfin : ∀ N, (∑ i ∈ Finset.range N, a i * y i) ^ 2 ≤
      (∑ i ∈ Finset.range N, a i) * ∑ i ∈ Finset.range N, a i * y i ^ 2 := by
    intro N
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N) (fun i => Real.sqrt (a i))
      (fun i => Real.sqrt (a i) * y i)
    have e1 : ∀ i, Real.sqrt (a i) * (Real.sqrt (a i) * y i) = a i * y i := fun i => by
      rw [← mul_assoc, Real.mul_self_sqrt (ha i)]
    have e2 : ∀ i, Real.sqrt (a i) ^ 2 = a i := fun i => Real.sq_sqrt (ha i)
    have e3 : ∀ i, (Real.sqrt (a i) * y i) ^ 2 = a i * y i ^ 2 := fun i => by
      rw [mul_pow, Real.sq_sqrt (ha i)]
    simp only [e1, e2, e3] at h
    exact h
  exact le_of_tendsto_of_tendsto' (hay.hasSum.tendsto_sum_nat.pow 2)
    (hA.hasSum.tendsto_sum_nat.mul hY.hasSum.tendsto_sum_nat) hfin

/-- The geometric weights `e^{-κτ(i+1)}`. -/
def geomWeight (κ τ : ℝ) (i : ℕ) : ℝ := Real.exp (-(κ * τ * ((i : ℝ) + 1)))

theorem geomWeight_pos (κ τ : ℝ) (i : ℕ) : 0 < geomWeight κ τ i := Real.exp_pos _

theorem geomWeight_eq (κ τ : ℝ) (i : ℕ) :
    geomWeight κ τ i = Real.exp (-(κ * τ)) ^ (i + 1) := by
  rw [geomWeight, ← Real.exp_nat_mul]; push_cast; ring_nf

theorem summable_geomWeight {κ τ : ℝ} (hκτ : 0 < κ * τ) : Summable (geomWeight κ τ) := by
  rw [show geomWeight κ τ = fun i : ℕ => Real.exp (-(κ * τ)) ^ (i + 1) from
    funext (geomWeight_eq κ τ)]
  exact (summable_geometric_of_lt_one (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (by linarith))).comp_injective (add_left_injective 1)

/-- The anti-causal series `S(u) = Σ_{i≥0} e^{-κτ(i+1)} f(u + (i+1)τ)`. -/
def antiCausalSum (κ τ : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑' i : ℕ, geomWeight κ τ i * f (u + ((i : ℝ) + 1) * τ)

/-- The pointwise energy majorant `Σ_{i≥0} e^{-κτ(i+1)} f(u + (i+1)τ)²`. -/
def antiCausalMajorant (κ τ : ℝ) (f : ℝ → ℝ) (u : ℝ) : ENNReal :=
  ∑' i : ℕ, ENNReal.ofReal (geomWeight κ τ i * f (u + ((i : ℝ) + 1) * τ) ^ 2)

theorem measurable_antiCausalMajorant (κ τ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (antiCausalMajorant κ τ f) :=
  Measurable.tsum fun _ => ENNReal.measurable_ofReal.comp
    (measurable_const.mul ((hf.comp (measurable_add_const _)).pow_const 2))

theorem lintegral_antiCausalMajorant {κ τ : ℝ} (hκτ : 0 < κ * τ) {f : ℝ → ℝ}
    (hf : Measurable f) :
    ∫⁻ u, antiCausalMajorant κ τ f u =
      ENNReal.ofReal (∑' i, geomWeight κ τ i) * ∫⁻ u, ENNReal.ofReal (f u ^ 2) := by
  have hm : ∀ i : ℕ, Measurable fun u => ENNReal.ofReal (f (u + ((i : ℝ) + 1) * τ) ^ 2) :=
    fun i => ENNReal.measurable_ofReal.comp ((hf.comp (measurable_add_const _)).pow_const 2)
  have hm' : ∀ i : ℕ, Measurable fun u =>
      ENNReal.ofReal (geomWeight κ τ i * f (u + ((i : ℝ) + 1) * τ) ^ 2) :=
    fun i => ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((hf.comp (measurable_add_const _)).pow_const 2))
  simp only [antiCausalMajorant]
  rw [lintegral_tsum fun i => (hm' i).aemeasurable]
  have hterm : ∀ i : ℕ, ∫⁻ u, ENNReal.ofReal (geomWeight κ τ i * f (u + ((i : ℝ) + 1) * τ) ^ 2) =
      ENNReal.ofReal (geomWeight κ τ i) * ∫⁻ u, ENNReal.ofReal (f u ^ 2) := by
    intro i
    simp_rw [ENNReal.ofReal_mul (geomWeight_pos κ τ i).le]
    rw [lintegral_const_mul _ (hm i)]
    congr 1
    exact lintegral_add_right_eq_self (fun v => ENNReal.ofReal (f v ^ 2)) (((i : ℝ) + 1) * τ)
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_right, ENNReal.ofReal_tsum_of_nonneg (fun i => (geomWeight_pos κ τ i).le)
    (summable_geomWeight hκτ)]

/-- Pointwise: `S(u)² ≤ (Σ wᵢ) · majorant(u)`. -/
theorem ofReal_sq_antiCausalSum_le {κ τ : ℝ} (hκτ : 0 < κ * τ) (f : ℝ → ℝ) (u : ℝ) :
    ENNReal.ofReal (antiCausalSum κ τ f u ^ 2) ≤
      ENNReal.ofReal (∑' i, geomWeight κ τ i) * antiCausalMajorant κ τ f u := by
  have hW : 0 < ∑' i, geomWeight κ τ i :=
    (summable_geomWeight hκτ).tsum_pos (fun i => (geomWeight_pos κ τ i).le) 0 (geomWeight_pos κ τ 0)
  by_cases htop : antiCausalMajorant κ τ f u = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hW).ne']
    exact le_top
  · have hsum : Summable fun i => geomWeight κ τ i * f (u + ((i : ℝ) + 1) * τ) ^ 2 := by
      refine (ENNReal.summable_toReal htop).congr fun i => ?_
      rw [ENNReal.toReal_ofReal (mul_nonneg (geomWeight_pos κ τ i).le (sq_nonneg _))]
    have hmaj : antiCausalMajorant κ τ f u =
        ENNReal.ofReal (∑' i, geomWeight κ τ i * f (u + ((i : ℝ) + 1) * τ) ^ 2) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (geomWeight_pos κ τ i).le (sq_nonneg _))
        hsum).symm
    rw [hmaj, ← ENNReal.ofReal_mul hW.le]
    exact ENNReal.ofReal_le_ofReal (sq_tsum_mul_le (fun i => (geomWeight_pos κ τ i).le)
      (summable_geomWeight hκτ) hsum)

/-- **The anti-causal series has finite energy.** -/
theorem lintegral_sq_antiCausalSum_ne_top {κ τ : ℝ} (hκτ : 0 < κ * τ) {f : ℝ → ℝ}
    (hf : Measurable f) (hfin : ∫⁻ u, ENNReal.ofReal (f u ^ 2) ≠ ⊤) :
    ∫⁻ u, ENNReal.ofReal (antiCausalSum κ τ f u ^ 2) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (lintegral_mono fun u => ofReal_sq_antiCausalSum_le hκτ f u)
  rw [lintegral_const_mul _ (measurable_antiCausalMajorant κ τ hf),
    lintegral_antiCausalMajorant hκτ hf]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)

theorem ae_summable_antiCausal {κ τ : ℝ} (hκτ : 0 < κ * τ) {f : ℝ → ℝ} (hf : Measurable f)
    (hfin : ∫⁻ u, ENNReal.ofReal (f u ^ 2) ≠ ⊤) :
    ∀ᵐ u : ℝ, Summable fun i : ℕ => geomWeight κ τ i * f (u + ((i : ℝ) + 1) * τ) := by
  have hint : ∫⁻ u, antiCausalMajorant κ τ f u ≠ ⊤ := by
    rw [lintegral_antiCausalMajorant hκτ hf]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  filter_upwards [ae_lt_top' (measurable_antiCausalMajorant κ τ hf).aemeasurable hint] with u hu
  have hsum : Summable fun i => geomWeight κ τ i * f (u + ((i : ℝ) + 1) * τ) ^ 2 := by
    refine (ENNReal.summable_toReal hu.ne).congr fun i => ?_
    rw [ENNReal.toReal_ofReal (mul_nonneg (geomWeight_pos κ τ i).le (sq_nonneg _))]
  exact summable_mul_of_summable_mul_sq (fun i => (geomWeight_pos κ τ i).le)
    (summable_geomWeight hκτ) hsum

theorem measurable_antiCausalSum (κ τ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (antiCausalSum κ τ f) :=
  Measurable.tsum fun _ => measurable_const.mul (hf.comp (measurable_add_const _))

/-! ### The one-prime ghost -/

/-- The one-prime defect `g − e^{κτ} g(· − τ)`. -/
def lawDefect (κ τ : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ := g u - Real.exp (κ * τ) * g (u - τ)

/-- The one-prime ghost `e^{-κu}(g + S)`, `S` the anti-causal series of the defect. -/
def logGhost (κ τ : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  Real.exp (-(κ * u)) * (g u + antiCausalSum κ τ (lawDefect κ τ g) u)

/-- `g = e^{κu}·ghost − S` identically. -/
theorem eq_exp_mul_logGhost_sub (κ τ : ℝ) (g : ℝ → ℝ) (u : ℝ) :
    g u = Real.exp (κ * u) * logGhost κ τ g u - antiCausalSum κ τ (lawDefect κ τ g) u := by
  rw [logGhost, ← mul_assoc, ← Real.exp_add, show κ * u + -(κ * u) = 0 by ring, Real.exp_zero]
  ring

/-- **The ghost is `τ`-periodic wherever the anti-causal series converges.** -/
theorem logGhost_add_period (κ τ : ℝ) (g : ℝ → ℝ) {u : ℝ}
    (hs : Summable fun i : ℕ => geomWeight κ τ i * lawDefect κ τ g (u + ((i : ℝ) + 1) * τ)) :
    logGhost κ τ g (u + τ) = logGhost κ τ g u := by
  set S := antiCausalSum κ τ (lawDefect κ τ g)
  have hshift : S u = Real.exp (-(κ * τ)) * (lawDefect κ τ g (u + τ) + S (u + τ)) := by
    change antiCausalSum κ τ (lawDefect κ τ g) u = _
    rw [antiCausalSum, hs.tsum_eq_zero_add]
    have hF : ∀ i : ℕ, geomWeight κ τ (i + 1) * lawDefect κ τ g (u + (((i + 1 : ℕ) : ℝ) + 1) * τ) =
        Real.exp (-(κ * τ)) * (geomWeight κ τ i * lawDefect κ τ g ((u + τ) + ((i : ℝ) + 1) * τ)) := by
      intro i
      rw [geomWeight, geomWeight, ← mul_assoc, ← Real.exp_add]
      congr 2
      · push_cast; ring
      · push_cast; ring
    simp_rw [hF]
    rw [tsum_mul_left, geomWeight]
    change Real.exp (-(κ * τ * (((0 : ℕ) : ℝ) + 1))) *
        lawDefect κ τ g (u + (((0 : ℕ) : ℝ) + 1) * τ) +
      Real.exp (-(κ * τ)) * antiCausalSum κ τ (lawDefect κ τ g) (u + τ) = _
    simp only [Nat.cast_zero, zero_add, mul_one, one_mul]
    ring
  have hdef : lawDefect κ τ g (u + τ) = g (u + τ) - Real.exp (κ * τ) * g u := by
    rw [lawDefect, add_sub_cancel_right]
  have hEE : Real.exp (-(κ * τ)) * Real.exp (κ * τ) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hexp : Real.exp (-(κ * (u + τ))) = Real.exp (-(κ * u)) * Real.exp (-(κ * τ)) := by
    rw [← Real.exp_add]; ring_nf
  change Real.exp (-(κ * (u + τ))) * (g (u + τ) + S (u + τ)) =
    Real.exp (-(κ * u)) * (g u + S u)
  rw [hshift, hdef, hexp]
  linear_combination (Real.exp (-(κ * u)) * g u) * hEE

theorem ae_periodic_logGhost {κ τ : ℝ} (hκτ : 0 < κ * τ) {g : ℝ → ℝ}
    (hd : Measurable (lawDefect κ τ g))
    (hfin : ∫⁻ u, ENNReal.ofReal (lawDefect κ τ g u ^ 2) ≠ ⊤) :
    ∀ᵐ u : ℝ, logGhost κ τ g (u + τ) = logGhost κ τ g u := by
  filter_upwards [ae_summable_antiCausal hκτ hd hfin] with u hu
  exact logGhost_add_period κ τ g hu


theorem measurable_logGhost (κ τ : ℝ) {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (logGhost κ τ g) := by
  have hd : Measurable (lawDefect κ τ g) :=
    hg.sub (measurable_const.mul (hg.comp (measurable_sub_const τ)))
  exact (Real.measurable_exp.comp (measurable_id.const_mul κ).neg).mul
    (hg.add (measurable_antiCausalSum κ τ hd))

/-! ### Two laws leave a constant -/

theorem ofReal_sq_sub_le (x y : ℝ) :
    ENNReal.ofReal ((x - y) ^ 2) ≤ 2 * ENNReal.ofReal (x ^ 2) + 2 * ENNReal.ofReal (y ^ 2) := by
  have h : (x - y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by nlinarith [sq_nonneg (x + y)]
  calc ENNReal.ofReal ((x - y) ^ 2) ≤ ENNReal.ofReal (2 * x ^ 2 + 2 * y ^ 2) :=
        ENNReal.ofReal_le_ofReal h
    _ = 2 * ENNReal.ofReal (x ^ 2) + 2 * ENNReal.ofReal (y ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num)]
        simp

theorem one_le_exp_mul {κ u : ℝ} (hκ : 0 ≤ κ) (hu : 0 ≤ u) : 1 ≤ Real.exp (κ * u) :=
  Real.one_le_exp (mul_nonneg hκ hu)

/-- **Transfer of a period.** If `χ` is a.e. `τ`-periodic, `φ` a.e. `σ`-periodic, and
`e^{κu}(χ − φ)` has finite energy, then `τ` is also an a.e. period of `φ`. -/
theorem ae_periodic_of_weighted_difference {κ τ σ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ)
    [Fact (0 < σ)] {χ φ : ℝ → ℝ} (hχ : Measurable χ) (hφ : Measurable φ)
    (hχper : ∀ᵐ u : ℝ, χ (u + τ) = χ u) (hφper : ∀ᵐ u : ℝ, φ (u + σ) = φ u)
    (hfin : ∫⁻ u, ENNReal.ofReal ((Real.exp (κ * u) * (χ u - φ u)) ^ 2) ≠ ⊤) :
    ∀ᵐ u : ℝ, φ (u + τ) = φ u := by
  set W : ℝ → ENNReal := fun u => ENNReal.ofReal ((Real.exp (κ * u) * (χ u - φ u)) ^ 2) with hWdef
  have hWm : Measurable W := ENNReal.measurable_ofReal.comp
    (((Real.measurable_exp.comp (measurable_id.const_mul κ)).mul (hχ.sub hφ)).pow_const 2)
  set ψ : ℝ → ℝ := fun u => φ (u + τ) - φ u with hψdef
  have hψm : Measurable ψ := (hφ.comp (measurable_add_const τ)).sub hφ
  have hψper : ∀ᵐ u : ℝ, ψ (u + σ) = ψ u := by
    filter_upwards [hφper, ae_comp_add_right hφper τ] with u h1 h2
    simp only [hψdef]
    rw [show u + σ + τ = u + τ + σ by ring, h2, h1]
  have hpt : ∀ᵐ u : ℝ, u ∈ Ioi (0 : ℝ) →
      ENNReal.ofReal (ψ u ^ 2) ≤ 2 * W (u + τ) + 2 * W u := by
    filter_upwards [hχper] with u hu hu0
    have hu0' : (0 : ℝ) ≤ u := le_of_lt hu0
    have hψ : ψ u = -((χ (u + τ) - φ (u + τ)) - (χ u - φ u)) := by
      simp only [hψdef]; rw [hu]; ring
    rw [hψ, neg_sq]
    have hA : ENNReal.ofReal ((χ (u + τ) - φ (u + τ)) ^ 2) ≤ W (u + τ) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have he := one_le_exp_mul hκ.le (by linarith : (0 : ℝ) ≤ u + τ)
      rw [mul_pow]
      nlinarith [sq_nonneg (χ (u + τ) - φ (u + τ)), one_le_pow₀ (n := 2) he]
    have hB : ENNReal.ofReal ((χ u - φ u) ^ 2) ≤ W u := by
      refine ENNReal.ofReal_le_ofReal ?_
      have he := one_le_exp_mul hκ.le hu0'
      rw [mul_pow]
      nlinarith [sq_nonneg (χ u - φ u), one_le_pow₀ (n := 2) he]
    refine (ofReal_sq_sub_le _ _).trans ?_
    gcongr
  have hψfin : ∫⁻ u in Ioi 0, ENNReal.ofReal (ψ u ^ 2) ≠ ⊤ := by
    have h1 : ∫⁻ u in Ioi 0, ENNReal.ofReal (ψ u ^ 2) ≤
        ∫⁻ u in Ioi 0, (2 * W (u + τ) + 2 * W u) :=
      lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).mpr hpt)
    have h2 : ∫⁻ u in Ioi 0, (2 * W (u + τ) + 2 * W u) ≤ ∫⁻ u, (2 * W (u + τ) + 2 * W u) :=
      setLIntegral_le_lintegral _ _
    have hWτ : Measurable fun u => W (u + τ) := hWm.comp (measurable_add_const τ)
    have hWτ2 : Measurable fun u => 2 * W (u + τ) := hWτ.const_mul 2
    have h3 : ∫⁻ u, (2 * W (u + τ) + 2 * W u) = (2 * ∫⁻ u, W u) + 2 * ∫⁻ u, W u := by
      rw [lintegral_add_left hWτ2, lintegral_const_mul _ hWτ, lintegral_const_mul _ hWm]
      rw [lintegral_add_right_eq_self (μ := volume) W τ]
    have hfin' : ∫⁻ u, W u ≠ ⊤ := hfin
    refine ne_top_of_le_ne_top ?_ (h1.trans (h2.trans h3.le))
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) hfin',
      ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) hfin'⟩
  filter_upwards [ae_eq_zero_of_periodic hψm hψper hψfin] with u hu
  simp only [hψdef] at hu
  linarith

/-- **Two incommensurable one-prime laws leave a constant.** If `g − e^{κτ₂}g(· − τ₂)` and
`g − e^{κτ₃}g(· − τ₃)` have finite energy and `τ₂/τ₃` is irrational, then `g − c e^{κu}` has finite
energy for some constant `c`. -/
theorem exists_lintegral_sub_const_mul_exp_ne_top {κ : ℝ} (hκ : 0 < κ) {τ₂ τ₃ : ℝ}
    (hτ₂ : 0 < τ₂) (hτ₃ : 0 < τ₃) (h23 : addOrderOf (τ₂ : AddCircle τ₃) = 0)
    (h32 : addOrderOf (τ₃ : AddCircle τ₂) = 0) {g : ℝ → ℝ} (hg : Measurable g)
    (h2 : ∫⁻ u, ENNReal.ofReal (lawDefect κ τ₂ g u ^ 2) ≠ ⊤)
    (h3 : ∫⁻ u, ENNReal.ofReal (lawDefect κ τ₃ g u ^ 2) ≠ ⊤) :
    ∃ c : ℝ, ∫⁻ u, ENNReal.ofReal ((g u - c * Real.exp (κ * u)) ^ 2) ≠ ⊤ := by
  haveI : Fact (0 < τ₂) := ⟨hτ₂⟩
  haveI : Fact (0 < τ₃) := ⟨hτ₃⟩
  have hd : ∀ τ, Measurable (lawDefect κ τ g) := fun τ =>
    hg.sub (measurable_const.mul (hg.comp (measurable_sub_const τ)))
  set S₂ := antiCausalSum κ τ₂ (lawDefect κ τ₂ g) with hS₂def
  set S₃ := antiCausalSum κ τ₃ (lawDefect κ τ₃ g) with hS₃def
  set π₂ := logGhost κ τ₂ g with hπ₂def
  set π₃ := logGhost κ τ₃ g with hπ₃def
  have hS₂ : ∫⁻ u, ENNReal.ofReal (S₂ u ^ 2) ≠ ⊤ :=
    lintegral_sq_antiCausalSum_ne_top (mul_pos hκ hτ₂) (hd τ₂) h2
  have hS₃ : ∫⁻ u, ENNReal.ofReal (S₃ u ^ 2) ≠ ⊤ :=
    lintegral_sq_antiCausalSum_ne_top (mul_pos hκ hτ₃) (hd τ₃) h3
  have hmS₂ : Measurable S₂ := measurable_antiCausalSum κ τ₂ (hd τ₂)
  have hp₂ : ∀ᵐ u : ℝ, π₂ (u + τ₂) = π₂ u := ae_periodic_logGhost (mul_pos hκ hτ₂) (hd τ₂) h2
  have hp₃ : ∀ᵐ u : ℝ, π₃ (u + τ₃) = π₃ u := ae_periodic_logGhost (mul_pos hκ hτ₃) (hd τ₃) h3
  have hm₂ : Measurable π₂ := measurable_logGhost κ τ₂ hg
  have hm₃ : Measurable π₃ := measurable_logGhost κ τ₃ hg
  -- the two decompositions of `g`
  have hdiff : ∀ u, Real.exp (κ * u) * (π₂ u - π₃ u) = S₂ u - S₃ u := by
    intro u
    have e2 := eq_exp_mul_logGhost_sub κ τ₂ g u
    have e3 := eq_exp_mul_logGhost_sub κ τ₃ g u
    linear_combination e3 - e2
  have hW : ∫⁻ u, ENNReal.ofReal ((Real.exp (κ * u) * (π₂ u - π₃ u)) ^ 2) ≠ ⊤ := by
    simp_rw [hdiff]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun u => ofReal_sq_sub_le (S₂ u) (S₃ u))
    have hm2 : Measurable fun u => 2 * ENNReal.ofReal (S₂ u ^ 2) :=
      (ENNReal.measurable_ofReal.comp (hmS₂.pow_const 2)).const_mul 2
    rw [lintegral_add_left hm2, lintegral_const_mul' _ _ (by norm_num),
      lintegral_const_mul' _ _ (by norm_num)]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) hS₂,
      ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) hS₃⟩
  have hW' : ∫⁻ u, ENNReal.ofReal ((Real.exp (κ * u) * (π₃ u - π₂ u)) ^ 2) ≠ ⊤ := by
    simpa only [← neg_sub (π₂ _), mul_neg, neg_sq] using hW
  -- each ghost inherits the other period, hence is constant
  have hA₃ := ae_periodic_of_weighted_difference hκ hτ₂ hm₂ hm₃ hp₂ hp₃ hW
  have hA₂ := ae_periodic_of_weighted_difference hκ hτ₃ hm₃ hm₂ hp₃ hp₂ hW'
  obtain ⟨c₃, hc₃⟩ := exists_ae_eq_const_of_two_periods hm₃ h23 hp₃ hA₃
  obtain ⟨c₂, hc₂⟩ := exists_ae_eq_const_of_two_periods hm₂ h32 hp₂ hA₂
  -- the constants agree, since `e^{κu}` has infinite energy
  have hc : c₂ = c₃ := by
    by_contra hne
    have hsq : 0 < (c₂ - c₃) ^ 2 := by
      have : c₂ - c₃ ≠ 0 := sub_ne_zero.mpr hne
      positivity
    have hlow : ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((c₂ - c₃) ^ 2) ≤
        ∫⁻ u, ENNReal.ofReal ((Real.exp (κ * u) * (π₂ u - π₃ u)) ^ 2) := by
      refine le_trans ?_ (setLIntegral_le_lintegral (Ioi 0) _)
      refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).mpr ?_)
      filter_upwards [hc₂, hc₃] with u h2u h3u hu0
      rw [h2u, h3u]
      refine ENNReal.ofReal_le_ofReal ?_
      have he := one_le_exp_mul hκ.le (le_of_lt hu0)
      rw [mul_pow]
      nlinarith [one_le_pow₀ (n := 2) he]
    rw [setLIntegral_const, Real.volume_Ioi, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hsq).ne'] at hlow
    exact hW (top_le_iff.mp hlow)
  refine ⟨c₂, ?_⟩
  have hcongr : (fun u => ENNReal.ofReal ((g u - c₂ * Real.exp (κ * u)) ^ 2)) =ᵐ[volume]
      fun u => ENNReal.ofReal (S₂ u ^ 2) := by
    filter_upwards [hc₂] with u hu
    have e2 := eq_exp_mul_logGhost_sub κ τ₂ g u
    rw [e2, ← hπ₂def, hu]
    congr 1
    ring
  rw [lintegral_congr_ae hcongr]
  exact hS₂

end GaloisForLFunctions.ArithmeticDefectRigidity
