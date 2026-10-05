import GaloisForLFunctions.RHTower.ThetaQuantileHalfPowerThreshold
import GaloisForLFunctions.RHTower.ThetaQuotientEigenvalueSums

/-!
# Every Xi divisor mode is charged at the input port

At a zero `z` of `Ξ_C` the compact source inverse `B` has the divisor eigenvector `v_z` with
`B v_z = −z⁻¹ v_z` and `∫₀¹ v_z = √M`.  The source-normalized quotient mode
`f_z = v_z/√M − 1 ∈ H₀` satisfies

`D f_z = −z⁻¹ f_z`,   `β(f_z) = −z⁻¹ ≠ 0`,

so no divisor mode lies in the neutral-port subspace `ker β`, where the pencil `TD = A − bβ`
forces real eigenvalues.  The suppressed pencil `A f = λ T f` has only real eigenvalues and does
not contain any `f_z`.  Counting zeros with multiplicity, the largest total charge over `N`
divisor copies is `Σ |β(f_z)| = (1/(2π) + o(1))(log N)²`.
-/

open MeasureTheory Set Filter Topology Module
open scoped InnerProductSpace

namespace RHTower

noncomputable section

open HedenmalmThetaSource HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmPrimeTranslation
  GaloisForLFunctions.HTGeometry

local notation "ThetaL2" => Lp ℂ 2 unitIntervalMeasure

/-! ## The divisor eigenvectors -/

theorem xiC_eq_zero_of_XiC_eq_zero {z : ℂ} (hz : XiC z = 0) : xiC thetaSource z = 0 := by
  rw [xiC_thetaSource (abs_im_lt_one_of_XiC_eq_zero hz)]; exact hz

/-- The divisor eigenvector `v_z` of the source inverse (zero off the divisor). -/
def divisorVec (z : ℂ) : ThetaL2 :=
  if h : XiC z = 0 then
    thetaDivisorEigenvector z (abs_im_lt_one_of_XiC_eq_zero h) (xiC_eq_zero_of_XiC_eq_zero h)
  else 0

theorem divisorVec_of_zero {z : ℂ} (hz : XiC z = 0) :
    divisorVec z = thetaDivisorEigenvector z (abs_im_lt_one_of_XiC_eq_zero hz) (xiC_eq_zero_of_XiC_eq_zero hz) :=
  dif_pos hz

theorem thetaKernelOperator_divisorVec {z : ℂ} (hz : XiC z = 0) :
    thetaKernelOperator (divisorVec z) = (-z⁻¹) • divisorVec z := by
  rw [divisorVec_of_zero hz, thetaKernelOperator_eq_thetaCompactSourceInverse]
  exact thetaCompactSourceInverse_eigen z _ _

/-- **Source normalization**: `∫₀¹ v_z = √M`. -/
theorem inner_constMode_divisorVec {z : ℂ} (hz : XiC z = 0) :
    ⟪constMode, divisorVec z⟫_ℂ = (Real.sqrt thetaSource.mass : ℂ) := by
  have hz1 := abs_im_lt_one_of_XiC_eq_zero hz
  have hz0 := xiC_eq_zero_of_XiC_eq_zero hz
  rw [inner_constMode_eq_pinnedMean, pinnedMean, divisorVec_of_zero hz, thetaDivisorEigenvector]
  set v := thetaDivisorSourceVector z hz1 hz0
  have hae : (fun t => (quantileUnitary thetaSource v : ThetaL2) t) =ᵐ[unitIntervalMeasure]
      fun t => (fun x => (Real.sqrt thetaSource.mass : ℂ) * sourceModeF thetaSource z x /
        (thetaSource.k x : ℂ)) (thetaSource.quantileFun t) := by
    filter_upwards [quantileUnitary_ae thetaSource v, thetaDivisorSourceVector_quantile_ae z hz1 hz0] with t h1 h2
    rw [h1, h2]
  rw [integral_congr_ae hae, unitIntervalMeasure_eq]
  have hcont : Continuous fun x => (Real.sqrt thetaSource.mass : ℂ) * sourceModeF thetaSource z x /
      (thetaSource.k x : ℂ) := by
    refine (continuous_const.mul ?_).div (Complex.continuous_ofReal.comp thetaSource.continuous_k)
      fun x => by exact_mod_cast (thetaSource.pos_k x).ne'
    unfold sourceModeF
    exact continuous_const.mul (continuous_sourceModeU hz1)
  rw [integral_comp_quantile thetaSource _ hcont.aestronglyMeasurable]
  have hM := thetaSource.mass_pos
  have hpt : ∀ x, thetaSource.normalized x • ((Real.sqrt thetaSource.mass : ℂ) * sourceModeF thetaSource z x /
      (thetaSource.k x : ℂ)) = ((Real.sqrt thetaSource.mass / thetaSource.mass : ℝ) : ℂ) *
        sourceModeF thetaSource z x := by
    intro x
    have hk : (thetaSource.k x : ℂ) ≠ 0 := by exact_mod_cast (thetaSource.pos_k x).ne'
    have hm : (thetaSource.mass : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    rw [PositiveDensitySource.normalized, Complex.real_smul]
    push_cast
    field_simp
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
    integral_sourceModeF_thetaSource_eq_mass hz1 hz0]
  have hm : (thetaSource.mass : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  push_cast
  field_simp

/-! ## The source-normalized quotient modes -/

theorem XiC_eq_zero_ne_zero {z : ℂ} (hz : XiC z = 0) : z ≠ 0 := fun h => XiC_zero_ne (h ▸ hz)


/-- **The source-normalized quotient mode** `f_z = v_z/√M − 1`. -/
def portEigenmode (z : ℂ) : ThetaL2 := ((Real.sqrt thetaSource.mass : ℂ)⁻¹) • divisorVec z - constMode

theorem sqrt_mass_ne_zero : (Real.sqrt thetaSource.mass : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 thetaSource.mass_pos).ne'

theorem portEigenmode_mem {z : ℂ} (hz : XiC z = 0) : portEigenmode z ∈ meanZeroSpace := by
  rw [mem_meanZeroSpace_iff, portEigenmode, inner_sub_right, inner_smul_right, inner_constMode_divisorVec hz,
    inner_constMode_self, inv_mul_cancel₀ sqrt_mass_ne_zero, sub_self]

theorem thetaKernelOperator_constMode : thetaKernelOperator constMode = 0 :=
  thetaKernelOperator_unitFourierBasis_zero

/-- **`D f_z = −z⁻¹ f_z`.** -/
theorem thetaQuotientOperator_portEigenmode {z : ℂ} (hz : XiC z = 0) :
    thetaQuotientOperator (portEigenmode z) = (-z⁻¹) • portEigenmode z := by
  rw [thetaQuotientOperator_apply, portEigenmode, map_sub, map_smul, thetaKernelOperator_constMode, sub_zero,
    thetaKernelOperator_divisorVec hz, smul_smul, map_smul, meanZeroProj_apply, inner_constMode_divisorVec hz]
  have e1 : (Real.sqrt thetaSource.mass : ℂ)⁻¹ * -z⁻¹ * (Real.sqrt thetaSource.mass : ℂ) = -z⁻¹ := by
    rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ sqrt_mass_ne_zero, one_mul]
  have e2 : (Real.sqrt thetaSource.mass : ℂ)⁻¹ * -z⁻¹ = -z⁻¹ * (Real.sqrt thetaSource.mass : ℂ)⁻¹ :=
    mul_comm _ _
  rw [smul_sub, smul_smul, e1, smul_sub, smul_smul, e2]

/-- **The port charge** `β(f_z) = −z⁻¹`. -/
theorem onePortInput_portEigenmode {z : ℂ} (hz : XiC z = 0) : onePortInput (portEigenmode z) = -z⁻¹ := by
  rw [onePortInput_apply, portEigenmode, map_sub, map_smul, thetaKernelOperator_constMode, sub_zero,
    thetaKernelOperator_divisorVec hz, smul_smul, inner_smul_right, inner_constMode_divisorVec hz]
  rw [mul_comm _ (Real.sqrt thetaSource.mass : ℂ), ← mul_assoc, mul_inv_cancel₀ sqrt_mass_ne_zero, one_mul]


/-- **Every divisor mode is charged**: `β(f_z) ≠ 0`. -/
theorem onePortInput_portEigenmode_ne_zero {z : ℂ} (hz : XiC z = 0) : onePortInput (portEigenmode z) ≠ 0 := by
  rw [onePortInput_portEigenmode hz]
  exact neg_ne_zero.2 (inv_ne_zero (XiC_eq_zero_ne_zero hz))

theorem portEigenmode_ne_zero {z : ℂ} (hz : XiC z = 0) : portEigenmode z ≠ 0 := fun h => by
  have := onePortInput_portEigenmode_ne_zero hz
  rw [h, map_zero] at this
  exact this rfl

/-- **The suppressed pencil is self-adjoint**: `A f = λ T f` on `H₀ ∖ {0}` forces `λ ∈ ℝ`. -/
theorem im_eq_zero_of_onePortPrimitive_eq {f : ThetaL2} {μ : ℂ} (hf : f ∈ meanZeroSpace) (hne : f ≠ 0)
    (heq : onePortPrimitive f = μ • onePortMetric f) : μ.im = 0 := by
  have h1 : μ * (metricEnergy f : ℂ) = ⟪f, onePortPrimitive f⟫_ℂ := by
    rw [← inner_onePortMetric_of_mem hf, ← inner_smul_right, heq]
  have hA : (⟪f, onePortPrimitive f⟫_ℂ).im = 0 := by
    have hsym : ⟪onePortPrimitive f, f⟫_ℂ = ⟪f, onePortPrimitive f⟫_ℂ :=
      isSelfAdjoint_onePortPrimitive.isSymmetric f f
    rw [← inner_conj_symm] at hsym
    exact Complex.conj_eq_iff_im.1 hsym
  have him := congrArg Complex.im h1
  rw [hA, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add] at him
  rcases mul_eq_zero.1 him with h | h
  · exact h
  · exact absurd h (metricEnergy_pos hne).ne'

theorem onePortOutputVector_ne_zero : onePortOutputVector ≠ 0 := by
  have hpos : 0 < ‖outPortLp‖ := by
    refine norm_pos_iff.2 fun h0 => ?_
    have hae := MemLp.coeFn_toLp memLp_normalized
    rw [show memLp_normalized.toLp = outPortLp from rfl, h0] at hae
    have h0' := Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)
    have := hae.symm.trans h0'
    obtain ⟨x, hx⟩ := this.exists
    have hρ := thetaSource.normalized_pos x
    simp only [Pi.zero_apply] at hx
    exact hρ.ne' (by exact_mod_cast hx)
  obtain ⟨f, hf, hlt⟩ := exists_inner_onePortOutputVector_gt (c := 0) hpos
  intro hb
  rw [hb, inner_zero_left, norm_zero, zero_mul] at hlt
  exact lt_irrefl _ hlt

/-- **The divisor modes are not solutions of the suppressed pencil**: `A f_z ≠ −z⁻¹ T f_z`. -/
theorem onePortPrimitive_portEigenmode_ne {z : ℂ} (hz : XiC z = 0) :
    onePortPrimitive (portEigenmode z) ≠ (-z⁻¹) • onePortMetric (portEigenmode z) := by
  intro h
  have hp := onePortMetric_thetaQuotientOperator (portEigenmode_mem hz)
  rw [thetaQuotientOperator_portEigenmode hz, map_smul, onePortInput_portEigenmode hz, h] at hp
  have : (-z⁻¹) • onePortOutputVector = 0 := by
    have := congrArg (fun x => x - (-z⁻¹) • onePortMetric (portEigenmode z)) hp
    simp only [sub_self] at this
    rw [eq_comm, sub_sub_cancel_left, neg_eq_zero] at this
    exact this
  rcases smul_eq_zero.1 this with h1 | h1
  · exact XiC_eq_zero_ne_zero hz (by simpa using h1)
  · exact onePortOutputVector_ne_zero h1

/-! ## The charged-port sum over the divisor -/

theorem norm_onePortInput_portEigenmode {z : ℂ} (hz : XiC z = 0) :
    ‖onePortInput (portEigenmode z)‖ = ‖-z⁻¹‖ := by
  rw [onePortInput_portEigenmode hz]

/-- An admissible family of divisor copies: distinct zeros `z ∈ s`, each taken `m(z)` times, at most
its order, `N` copies in total. -/
def IsXiZeroFamily (s : Finset ℂ) (m : ℂ → ℕ) (N : ℕ) : Prop :=
  (∀ z ∈ s, XiC z = 0 ∧ (m z : ℕ∞) ≤ analyticOrderAt XiC z) ∧ ∑ z ∈ s, m z ≤ N

/-- **The charged-port sum** `Σ |β(f_z)|` over the first `N` divisor copies ordered by `|z|`: the
largest total charge of `N` copies counted with multiplicity. -/
def xiPortChargeSum (N : ℕ) : ℝ :=
  sSup {x | ∃ (s : Finset ℂ) (m : ℂ → ℕ), IsXiZeroFamily s m N ∧
    x = ∑ z ∈ s, (m z : ℝ) * ‖onePortInput (portEigenmode z)‖}

theorem neg_inv_neg_inv (z : ℂ) : -(-z⁻¹)⁻¹ = z := by rw [inv_neg, neg_neg, inv_inv]

theorem neg_inv_injective : Function.Injective (fun z : ℂ => -z⁻¹) := fun a b h => by
  have := congrArg (fun w : ℂ => -w⁻¹) h
  simpa only [neg_inv_neg_inv] using this

theorem sum_le_thetaQuotientEigenSum_of_isXiZeroFamily {s : Finset ℂ} {m : ℂ → ℕ} {N : ℕ}
    (h : IsXiZeroFamily s m N) :
    ∑ z ∈ s, (m z : ℝ) * ‖onePortInput (portEigenmode z)‖ ≤ thetaQuotientEigenSum N := by
  classical
  set s' := s.image fun z => -z⁻¹
  set m' : ℂ → ℕ := fun μ => m (-μ⁻¹)
  have hinj : Set.InjOn (fun z : ℂ => -z⁻¹) (s : Set ℂ) := fun a _ b _ hab => neg_inv_injective hab
  have hfam : IsThetaEigenFamily s' m' N := by
    refine ⟨fun μ hμ => ?_, ?_⟩
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hμ
      obtain ⟨hz0, hmz⟩ := h.1 z hz
      refine ⟨neg_ne_zero.2 (inv_ne_zero (XiC_eq_zero_ne_zero hz0)), ?_⟩
      obtain ⟨-, heq⟩ := finrank_maxGenEigenspace_thetaD_of_XiC_eq_zero hz0
      simp only [m', neg_inv_neg_inv]
      rw [← heq] at hmz
      exact_mod_cast hmz
    · rw [Finset.sum_image hinj]
      simpa only [m', neg_inv_neg_inv] using h.2
  refine le_trans (le_of_eq ?_) (le_thetaQuotientEigenSum hfam)
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun z hz => ?_
  simp only [m', neg_inv_neg_inv, norm_onePortInput_portEigenmode (h.1 z hz).1]

theorem xiPortChargeSum_set_bddAbove (N : ℕ) :
    BddAbove {x | ∃ (s : Finset ℂ) (m : ℂ → ℕ), IsXiZeroFamily s m N ∧
      x = ∑ z ∈ s, (m z : ℝ) * ‖onePortInput (portEigenmode z)‖} :=
  ⟨thetaQuotientEigenSum N, fun _ ⟨_, _, h, hx⟩ => hx ▸ sum_le_thetaQuotientEigenSum_of_isXiZeroFamily h⟩

theorem sum_le_xiPortChargeSum_of_isThetaEigenFamily {s : Finset ℂ} {m : ℂ → ℕ} {N : ℕ}
    (h : IsThetaEigenFamily s m N) : ∑ μ ∈ s, (m μ : ℝ) * ‖μ‖ ≤ xiPortChargeSum N := by
  classical
  set s₁ := s.filter fun μ => m μ ≠ 0
  have hzero : ∀ μ ∈ s₁, ∃ z, XiC z = 0 ∧ μ = -z⁻¹ := by
    intro μ hμ
    obtain ⟨hμs, hm⟩ := Finset.mem_filter.1 hμ
    obtain ⟨hμ0, hle⟩ := h.1 μ hμs
    have hne : thetaD.maxGenEigenspace μ ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hle
      exact hm (Nat.le_zero.1 hle)
    exact exists_XiC_zero_of_maxGenEigenspace_thetaD_ne_bot hμ0 hne
  set s₂ := s₁.image fun μ => -μ⁻¹
  set m₂ : ℂ → ℕ := fun z => m (-z⁻¹)
  have hinj : Set.InjOn (fun μ : ℂ => -μ⁻¹) (s₁ : Set ℂ) := fun a _ b _ hab => neg_inv_injective hab
  have hfam : IsXiZeroFamily s₂ m₂ N := by
    refine ⟨fun z hz => ?_, ?_⟩
    · obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.1 hz
      obtain ⟨z₀, hz₀, hμz⟩ := hzero μ hμ
      have hzz : -μ⁻¹ = z₀ := by rw [hμz, neg_inv_neg_inv]
      rw [hzz]
      refine ⟨hz₀, ?_⟩
      obtain ⟨-, heq⟩ := finrank_maxGenEigenspace_thetaD_of_XiC_eq_zero hz₀
      simp only [m₂, ← hzz, neg_inv_neg_inv]
      rw [hzz, ← heq, ← hμz]
      exact_mod_cast (h.1 μ (Finset.mem_filter.1 hμ).1).2
    · rw [Finset.sum_image hinj]
      simp only [m₂, neg_inv_neg_inv]
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun _ _ _ => Nat.zero_le _).trans h.2
  have hval : ∑ μ ∈ s, (m μ : ℝ) * ‖μ‖ = ∑ z ∈ s₂, (m₂ z : ℝ) * ‖onePortInput (portEigenmode z)‖ := by
    rw [Finset.sum_image hinj]
    rw [← Finset.sum_filter_add_sum_filter_not s (fun μ => m μ ≠ 0)]
    have hrest : ∑ μ ∈ s.filter (fun μ => ¬ m μ ≠ 0), (m μ : ℝ) * ‖μ‖ = 0 :=
      Finset.sum_eq_zero fun μ hμ => by
        have := (Finset.mem_filter.1 hμ).2
        push Not at this
        simp [this]
    rw [hrest, add_zero]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    obtain ⟨z₀, hz₀, hμz⟩ := hzero μ hμ
    simp only [m₂, neg_inv_neg_inv]
    rw [norm_onePortInput_portEigenmode (by rw [hμz, neg_inv_neg_inv]; exact hz₀), neg_inv_neg_inv]
  rw [hval]
  exact le_csSup (xiPortChargeSum_set_bddAbove N) ⟨s₂, m₂, hfam, rfl⟩

/-- The charged-port sum is the modulus-ordered eigenvalue sum of `D`. -/
theorem xiPortChargeSum_eq (N : ℕ) : xiPortChargeSum N = thetaQuotientEigenSum N := by
  apply le_antisymm
  · exact csSup_le ⟨0, ∅, fun _ => 0, ⟨by simp, by simp⟩, by simp⟩ fun _ ⟨_, _, h, hx⟩ =>
      hx ▸ sum_le_thetaQuotientEigenSum_of_isXiZeroFamily h
  · exact csSup_le (thetaQuotientEigenSum_set_nonempty N) fun _ ⟨_, _, h, hx⟩ =>
      hx ▸ sum_le_xiPortChargeSum_of_isThetaEigenFamily h

/-- **The charged-port law** `Σ_{first N copies} |β(f_z)| = (1/(2π) + o(1))(log N)²`. -/
theorem tendsto_xiPortChargeSum_div_log_sq :
    Tendsto (fun N : ℕ => xiPortChargeSum N / Real.log N ^ 2) atTop (𝓝 (1 / (2 * Real.pi))) := by
  simp_rw [xiPortChargeSum_eq]
  exact tendsto_thetaQuotientEigenSum_div_log_sq

end

end RHTower
