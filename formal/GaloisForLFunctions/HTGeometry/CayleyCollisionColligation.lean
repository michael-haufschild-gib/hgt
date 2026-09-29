import GaloisForLFunctions.HTGeometry.CayleyContrastLaw
import GaloisForLFunctions.HTGeometry.HistoryRecordOperator
import GaloisForLFunctions.HTGeometry.L2FourierMultiplier
import GaloisForLFunctions.HTGeometry.BoundedMultiplierHilbert

/-!
# The Cayley collision colligation of a clock-pair law

For a finite law `ν` on clock pairs carried by the open quadrant, let
`δ = (x - y)/(|x| + |y|)` be the Cayley contrast and `g = √(1 - δ²)` the coherence.  On
`L²(ν)` the multipliers

`S f = δ f`,  `E₀ f = g f`

form a conservative colligation `S*S + E₀*E₀ = 1` with `Sᴺ → 0` strongly, since `|δ| < 1`
almost everywhere.  With `Z_ν = ∫ δ²(1 - δ²)² dν > 0`, the oriented collision state
`Ω_ν = Z_ν^{-1/2} δ(1 - δ²)` is a unit vector, its exit vectors are
`e_n = E₀ Sⁿ Ω_ν = Z_ν^{-1/2} g δⁿ⁺¹(1 - δ²)`, and the dephased record `𝖳_ν = ⊕ₙ |e_n⟩⟨e_n|` is
positive with `tr 𝖳_ν = ‖𝖳_ν‖₁ = 1`, tail traces `‖Sⁿ Ω_ν‖²`, and `‖𝖳_ν‖ = ‖e_0‖² < 1`.  It is the
trace-norm history dephasing of the lifted pure state `|O Ω_ν⟩⟨O Ω_ν|`.

If `ν` is swap-symmetric, the swap `J f = f ∘ swap` reverses `Ω_ν` and `S`, fixes `E₀`, acts by
`(-1)ⁿ⁺¹` on `e_n`, fixes `𝖳_ν`, and multiplies the `(n, k)` block of `|O Ω_ν⟩⟨O Ω_ν|` by
`(-1)ⁿ⁺ᵏ`.
-/

open MeasureTheory Filter Topology Set ContinuousLinearMap
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local instance factOneLeTwoCollision : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-! ## Contraction multipliers -/

section Multiplier

variable {α : Type*} [MeasurableSpace α] (ν : Measure α)

theorem norm_sq_Lp_two_eq_integral (f : Lp ℂ 2 ν) : ‖f‖ ^ 2 = ∫ z, ‖(f : α → ℂ) z‖ ^ 2 ∂ν := by
  have h := @inner_self_eq_norm_sq ℂ _ _ _ _ f
  rw [← h, L2.inner_def]
  have hpt : ∀ z, ⟪(f : α → ℂ) z, (f : α → ℂ) z⟫_ℂ = ((‖(f : α → ℂ) z‖ ^ 2 : ℝ) : ℂ) :=
    fun z => by rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  simp_rw [hpt]
  rw [integral_complex_ofReal]
  simp

theorem norm_sq_L2_toLp {g : α → ℂ} (hg : MemLp g 2 ν) :
    ‖hg.toLp g‖ ^ 2 = ∫ z, ‖g z‖ ^ 2 ∂ν := by
  rw [norm_sq_Lp_two_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with z hz
  rw [hz]

omit [MeasurableSpace α] in
theorem norm_bound_ofReal {φ : α → ℝ} (hb : ∀ z, |φ z| ≤ 1) (z : α) : ‖((φ z : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hb z

/-- Multiplication by a real symbol bounded by one. -/
def contractionMul {φ : α → ℝ} (hφ : Measurable φ) (hb : ∀ z, |φ z| ≤ 1) :
    Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  lpBoundedMulCLM (p := 2) (μ := ν) (φ := fun z => ((φ z : ℝ) : ℂ))
    (Complex.measurable_ofReal.comp hφ) zero_le_one (norm_bound_ofReal hb)

theorem contractionMul_coeFn {φ : α → ℝ} (hφ : Measurable φ) (hb : ∀ z, |φ z| ≤ 1)
    (f : Lp ℂ 2 ν) :
    (contractionMul ν hφ hb f : α → ℂ) =ᵐ[ν] fun z => (φ z : ℂ) * (f : α → ℂ) z :=
  lpBoundedMulCLM_coeFn _ _ _ f

theorem adjoint_contractionMul {φ : α → ℝ} (hφ : Measurable φ) (hb : ∀ z, |φ z| ≤ 1) :
    adjoint (contractionMul ν hφ hb) = contractionMul ν hφ hb :=
  ((eq_adjoint_iff _ _).mpr fun f g =>
    lpBoundedMulCLM_inner_general _ _ _ (fun _ => Complex.conj_ofReal _) f g).symm

omit [MeasurableSpace α] in
theorem abs_mul_le_one {φ ψ : α → ℝ} (hb : ∀ z, |φ z| ≤ 1) (hc : ∀ z, |ψ z| ≤ 1) (z : α) :
    |φ z * ψ z| ≤ 1 := by
  rw [abs_mul]
  exact mul_le_one₀ (hb z) (abs_nonneg _) (hc z)

theorem contractionMul_comp {φ ψ : α → ℝ} (hφ : Measurable φ) (hb : ∀ z, |φ z| ≤ 1)
    (hψ : Measurable ψ) (hc : ∀ z, |ψ z| ≤ 1) :
    contractionMul ν hφ hb ∘L contractionMul ν hψ hc
      = contractionMul ν (hφ.mul hψ) (abs_mul_le_one hb hc) :=
  lpBoundedMulCLM_comp _ _ _ _ _ _ _ _ _
    (Eventually.of_forall fun z => by simp only [Pi.mul_apply, Complex.ofReal_mul])

theorem contractionMul_congr {φ ψ : α → ℝ} (hφ : Measurable φ) (hb : ∀ z, |φ z| ≤ 1)
    (hψ : Measurable ψ) (hc : ∀ z, |ψ z| ≤ 1) (h : ∀ᵐ z ∂ν, φ z = ψ z) :
    contractionMul ν hφ hb = contractionMul ν hψ hc :=
  lpBoundedMulCLM_congr _ _ _ _ _ _ (h.mono fun z hz => by simp only [hz])

omit [MeasurableSpace α] in
theorem abs_pow_le_one' {φ : α → ℝ} (hb : ∀ z, |φ z| ≤ 1) (n : ℕ) (z : α) : |φ z ^ n| ≤ 1 := by
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (hb z)

theorem contractionMul_pow {φ : α → ℝ} (hφ : Measurable φ) (hb : ∀ z, |φ z| ≤ 1) (n : ℕ) :
    contractionMul ν hφ hb ^ n = contractionMul ν (hφ.pow_const n) (abs_pow_le_one' hb n) := by
  induction n with
  | zero =>
    rw [pow_zero, contractionMul]
    refine (lpBoundedMulCLM_eq_id _ _ _ (Eventually.of_forall fun _ => by simp)).symm
  | succ n ih =>
    rw [pow_succ, ih, mul_def, contractionMul_comp]
    exact contractionMul_congr ν _ _ _ _
      (Eventually.of_forall fun z => by simp only [Pi.mul_apply]; ring)

/-- `(M_φ)ᴺ → 0` strongly when `|φ| < 1` almost everywhere. -/
theorem tendsto_contractionMul_pow_apply {φ : α → ℝ} (hφ : Measurable φ)
    (hb : ∀ z, |φ z| ≤ 1) (hlt : ∀ᵐ z ∂ν, |φ z| < 1) (f : Lp ℂ 2 ν) :
    Tendsto (fun N => (contractionMul ν hφ hb ^ N) f) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hrepr : ∀ N, ‖(contractionMul ν hφ hb ^ N) f‖ ^ 2
      = ∫ z, (φ z ^ 2) ^ N * ‖(f : α → ℂ) z‖ ^ 2 ∂ν := by
    intro N
    rw [contractionMul_pow, norm_sq_Lp_two_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [contractionMul_coeFn ν (hφ.pow_const N) (abs_pow_le_one' hb N) f] with z hz
    rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, ← pow_mul,
      ← pow_mul, mul_comm N 2]
  have hint : Integrable (fun z => ‖(f : α → ℂ) z‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hsq : Tendsto (fun N => ‖(contractionMul ν hφ hb ^ N) f‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [hrepr]
    have h := tendsto_integral_of_dominated_convergence (μ := ν)
      (F := fun N z => (φ z ^ 2) ^ N * ‖(f : α → ℂ) z‖ ^ 2) (f := fun _ => 0)
      (fun z => ‖(f : α → ℂ) z‖ ^ 2)
      (fun N => ((hφ.pow_const 2).pow_const N).aestronglyMeasurable.mul hint.1) hint
      (fun N => Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_of_le_one_left (sq_nonneg _)
          (pow_le_one₀ (sq_nonneg _) (by nlinarith [abs_le.mp (hb z), sq_abs (φ z)])))
      (by
        filter_upwards [hlt] with z hz
        have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg (φ z))
          ((sq_lt_one_iff_abs_lt_one _).mpr hz)
        simpa using h1.mul_const (‖(f : α → ℂ) z‖ ^ 2))
    simpa using h
  have h := hsq.sqrt
  simp only [Real.sqrt_zero] at h
  exact h.congr fun N => Real.sqrt_sq (norm_nonneg _)

end Multiplier

/-! ## The Cayley contrast and coherence symbols -/

/-- The Cayley contrast `δ = (x - y)/(|x| + |y|)`, bounded by one everywhere. -/
def pairContrast (z : ℝ × ℝ) : ℝ := (z.1 - z.2) / (|z.1| + |z.2|)

theorem measurable_pairContrast : Measurable pairContrast := by
  unfold pairContrast
  fun_prop

theorem abs_pairContrast_le_one (z : ℝ × ℝ) : |pairContrast z| ≤ 1 := by
  unfold pairContrast
  rcases (add_nonneg (abs_nonneg z.1) (abs_nonneg z.2)).eq_or_lt with h | h
  · rw [← h, div_zero, abs_zero]
    exact zero_le_one
  · rw [abs_div, abs_of_pos h, div_le_one h]
    exact abs_sub _ _

theorem pairContrast_of_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    pairContrast (x, y) = cayleyContrast x y := by
  rw [pairContrast, cayleyContrast, abs_of_pos hx, abs_of_pos hy]

theorem abs_pairContrast_lt_one {z : ℝ × ℝ} (hz : 0 < z.1 ∧ 0 < z.2) : |pairContrast z| < 1 := by
  have h := cayleyContrast_mem_Ioo hz.1 hz.2
  rw [← pairContrast_of_pos hz.1 hz.2] at h
  exact abs_lt.mpr h

theorem pairContrast_swap (z : ℝ × ℝ) : pairContrast z.swap = -pairContrast z := by
  rw [pairContrast, pairContrast, Prod.fst_swap, Prod.snd_swap, add_comm, ← neg_div, neg_sub]

theorem pairContrast_sq_le_one (z : ℝ × ℝ) : pairContrast z ^ 2 ≤ 1 := by
  have h := abs_pairContrast_le_one z
  nlinarith [abs_nonneg (pairContrast z), sq_abs (pairContrast z)]

/-- The coherence `g = √(1 - δ²)`. -/
def pairCoherence (z : ℝ × ℝ) : ℝ := Real.sqrt (1 - pairContrast z ^ 2)

theorem measurable_pairCoherence : Measurable pairCoherence := by
  unfold pairCoherence
  exact (measurable_const.sub (measurable_pairContrast.pow_const 2)).sqrt

theorem pairCoherence_nonneg (z : ℝ × ℝ) : 0 ≤ pairCoherence z := Real.sqrt_nonneg _

theorem pairCoherence_sq (z : ℝ × ℝ) : pairCoherence z ^ 2 = 1 - pairContrast z ^ 2 :=
  Real.sq_sqrt (by linarith [pairContrast_sq_le_one z])

theorem abs_pairCoherence_le_one (z : ℝ × ℝ) : |pairCoherence z| ≤ 1 := by
  rw [abs_of_nonneg (pairCoherence_nonneg z), pairCoherence, Real.sqrt_le_one]
  linarith [sq_nonneg (pairContrast z)]

theorem pairCoherence_swap (z : ℝ × ℝ) : pairCoherence z.swap = pairCoherence z := by
  rw [pairCoherence, pairCoherence, pairContrast_swap, neg_sq]

/-- The oriented profile `δ(1 - δ²)`. -/
def collisionProfile (z : ℝ × ℝ) : ℝ := pairContrast z * (1 - pairContrast z ^ 2)

theorem measurable_collisionProfile : Measurable collisionProfile := by
  unfold collisionProfile
  exact measurable_pairContrast.mul (measurable_const.sub (measurable_pairContrast.pow_const 2))

theorem abs_collisionProfile_le_one (z : ℝ × ℝ) : |collisionProfile z| ≤ 1 := by
  have h1 := abs_pairContrast_le_one z
  have h3 : 0 ≤ 1 - pairContrast z ^ 2 := by linarith [pairContrast_sq_le_one z]
  rw [collisionProfile, abs_mul, abs_of_nonneg h3]
  exact mul_le_one₀ h1 h3 (by linarith [sq_nonneg (pairContrast z)])

theorem collisionProfile_swap (z : ℝ × ℝ) : collisionProfile z.swap = -collisionProfile z := by
  rw [collisionProfile, collisionProfile, pairContrast_swap, neg_sq]
  ring

/-! ## The colligation of a pair law -/

section PairLaw

variable (ν : Measure (ℝ × ℝ))

/-- The survival operator `S = δ`. -/
def collisionSurvival : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  contractionMul ν measurable_pairContrast abs_pairContrast_le_one

/-- The exit operator `E₀ = √(1 - λ)`. -/
def collisionExit : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  contractionMul ν measurable_pairCoherence abs_pairCoherence_le_one

theorem adjoint_collisionSurvival : adjoint (collisionSurvival ν) = collisionSurvival ν :=
  adjoint_contractionMul ν _ _

theorem adjoint_collisionExit : adjoint (collisionExit ν) = collisionExit ν :=
  adjoint_contractionMul ν _ _

/-- **(CCRHD.6).**  `S*S + E₀*E₀ = 1`. -/
theorem collision_colligation :
    adjoint (collisionSurvival ν) ∘L collisionSurvival ν
      + adjoint (collisionExit ν) ∘L collisionExit ν = ContinuousLinearMap.id ℂ _ := by
  rw [adjoint_collisionSurvival, adjoint_collisionExit]
  ext1 f
  refine Lp.ext ?_
  have hS : ∀ g : Lp ℂ 2 ν, (collisionSurvival ν g : ℝ × ℝ → ℂ) =ᵐ[ν]
      fun z => (pairContrast z : ℂ) * (g : ℝ × ℝ → ℂ) z := fun g => contractionMul_coeFn ν _ _ g
  have hE : ∀ g : Lp ℂ 2 ν, (collisionExit ν g : ℝ × ℝ → ℂ) =ᵐ[ν]
      fun z => (pairCoherence z : ℂ) * (g : ℝ × ℝ → ℂ) z := fun g => contractionMul_coeFn ν _ _ g
  filter_upwards [Lp.coeFn_add (collisionSurvival ν (collisionSurvival ν f))
    (collisionExit ν (collisionExit ν f)), hS (collisionSurvival ν f), hS f,
    hE (collisionExit ν f), hE f] with z h1 h2 h3 h4 h5
  rw [add_apply, comp_apply, comp_apply, id_apply, h1, Pi.add_apply, h2, h3, h4, h5]
  have hsum : (pairContrast z : ℂ) * ((pairContrast z : ℂ) * (f : ℝ × ℝ → ℂ) z)
      + (pairCoherence z : ℂ) * ((pairCoherence z : ℂ) * (f : ℝ × ℝ → ℂ) z)
      = ((pairContrast z ^ 2 + pairCoherence z ^ 2 : ℝ) : ℂ) * (f : ℝ × ℝ → ℂ) z := by
    push_cast
    ring
  rw [hsum, pairCoherence_sq]
  simp

/-- The survival and exit operators commute. -/
theorem collisionSurvival_comp_collisionExit :
    collisionSurvival ν ∘L collisionExit ν = collisionExit ν ∘L collisionSurvival ν := by
  rw [collisionSurvival, collisionExit, contractionMul_comp, contractionMul_comp]
  exact contractionMul_congr ν _ _ _ _ (Eventually.of_forall fun z => mul_comm _ _)

theorem collisionSurvival_pow (n : ℕ) :
    collisionSurvival ν ^ n
      = contractionMul ν (measurable_pairContrast.pow_const n)
          (abs_pow_le_one' abs_pairContrast_le_one n) :=
  contractionMul_pow ν _ _ n

/-- **(CCRHD.6).**  `Sᴺ → 0` strongly for a law carried by the open quadrant. -/
theorem collision_stable (hν : ∀ᵐ z ∂ν, 0 < z.1 ∧ 0 < z.2) (f : Lp ℂ 2 ν) :
    Tendsto (fun N => (collisionSurvival ν ^ N) f) atTop (𝓝 0) :=
  tendsto_contractionMul_pow_apply ν _ _ (hν.mono fun _ hz => abs_pairContrast_lt_one hz) f

/-- The normalizer `Z_ν = ∫ δ²(1 - δ²)² dν`. -/
def collisionMass : ℝ := ∫ z, collisionProfile z ^ 2 ∂ν

theorem collisionMass_nonneg : 0 ≤ collisionMass ν :=
  integral_nonneg fun _ => sq_nonneg _

/-- The oriented collision amplitude `Z_ν^{-1/2} δ(1 - δ²)`. -/
def collisionAmplitude (z : ℝ × ℝ) : ℝ := (Real.sqrt (collisionMass ν))⁻¹ * collisionProfile z

theorem measurable_collisionAmplitude : Measurable (collisionAmplitude ν) :=
  measurable_const.mul measurable_collisionProfile

variable [IsFiniteMeasure ν]

theorem integrable_of_abs_le {f : ℝ × ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ z, |f z| ≤ C) :
    Integrable f ν :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hC z)

theorem memLp_collisionAmplitude : MemLp (fun z => (collisionAmplitude ν z : ℂ)) 2 ν :=
  MemLp.of_bound
    (Complex.measurable_ofReal.comp (measurable_collisionAmplitude ν)).aestronglyMeasurable
    (Real.sqrt (collisionMass ν))⁻¹ (Eventually.of_forall fun z => by
      rw [Complex.norm_real, Real.norm_eq_abs, collisionAmplitude, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
      exact mul_le_of_le_one_right (inv_nonneg.mpr (Real.sqrt_nonneg _))
        (abs_collisionProfile_le_one z))

/-- **(CCRHD.2).**  The oriented collision state `Ω_ν`. -/
def collisionState : Lp ℂ 2 ν := (memLp_collisionAmplitude ν).toLp _

theorem collisionState_coeFn :
    (collisionState ν : ℝ × ℝ → ℂ) =ᵐ[ν] fun z => (collisionAmplitude ν z : ℂ) :=
  (memLp_collisionAmplitude ν).coeFn_toLp

/-- `‖Sⁿ Ω_ν‖² = Z_ν⁻¹ ∫ λⁿ δ²(1 - δ²)² dν`. -/
theorem norm_collisionSurvival_pow_state_sq (n : ℕ) :
    ‖(collisionSurvival ν ^ n) (collisionState ν)‖ ^ 2
      = (collisionMass ν)⁻¹ * ∫ z, (pairContrast z ^ 2) ^ n * collisionProfile z ^ 2 ∂ν := by
  rw [collisionSurvival_pow, norm_sq_Lp_two_eq_integral, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [contractionMul_coeFn ν (measurable_pairContrast.pow_const n)
    (abs_pow_le_one' abs_pairContrast_le_one n) (collisionState ν),
    collisionState_coeFn ν] with z h1 h2
  rw [h1, h2, collisionAmplitude, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, sq_abs, sq_abs, mul_pow, inv_pow,
    Real.sq_sqrt (collisionMass_nonneg ν), ← pow_mul, ← pow_mul, mul_comm n 2]
  ring

/-- **Theorem CCRHD-A for `ν`.**  `‖Ω_ν‖ = 1` when `Z_ν > 0`. -/
theorem norm_collisionState (hZ : 0 < collisionMass ν) : ‖collisionState ν‖ = 1 := by
  have h := norm_collisionSurvival_pow_state_sq ν 0
  simp only [pow_zero, one_mul, one_def, id_apply] at h
  rw [← collisionMass, inv_mul_cancel₀ hZ.ne'] at h
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp (by rw [h, one_pow])

/-- **(CCRHD.9).**  The exit vectors `e_n = E₀ Sⁿ Ω_ν`. -/
def collisionExitVector (n : ℕ) : Lp ℂ 2 ν :=
  collisionExit ν ((collisionSurvival ν ^ n) (collisionState ν))

/-- **(CCRHD.17).**  `e_n = Z_ν^{-1/2} g δⁿ δ(1 - δ²)`. -/
theorem collisionExitVector_coeFn (n : ℕ) :
    (collisionExitVector ν n : ℝ × ℝ → ℂ) =ᵐ[ν]
      fun z => ((pairCoherence z * pairContrast z ^ n * collisionAmplitude ν z : ℝ) : ℂ) := by
  filter_upwards [contractionMul_coeFn ν measurable_pairCoherence abs_pairCoherence_le_one
    ((collisionSurvival ν ^ n) (collisionState ν)),
    (by rw [collisionSurvival_pow]; exact contractionMul_coeFn ν _ _ (collisionState ν) :
      (((collisionSurvival ν ^ n) (collisionState ν) : Lp ℂ 2 ν) : ℝ × ℝ → ℂ) =ᵐ[ν]
        fun z => ((pairContrast z ^ n : ℝ) : ℂ) * (collisionState ν : ℝ × ℝ → ℂ) z),
    collisionState_coeFn ν] with z h1 h2 h3
  rw [collisionExitVector, collisionExit, h1, h2, h3]
  push_cast
  ring

/-- The exit vectors commute with survival: `e_n = Sⁿ E₀ Ω_ν`. -/
theorem collisionExitVector_eq (n : ℕ) :
    collisionExitVector ν n = (collisionSurvival ν ^ n) (collisionExit ν (collisionState ν)) := by
  have hc : ∀ y, collisionSurvival ν (collisionExit ν y)
      = collisionExit ν (collisionSurvival ν y) :=
    fun y => by
      have := congrArg (fun A : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν => A y)
        (collisionSurvival_comp_collisionExit ν)
      simpa using this
  have h : ∀ y, collisionExit ν ((collisionSurvival ν ^ n) y)
      = (collisionSurvival ν ^ n) (collisionExit ν y) := by
    induction n with
    | zero => intro y; simp [one_def]
    | succ n ih =>
      intro y
      rw [pow_succ' (collisionSurvival ν) n, mul_def, comp_apply, comp_apply, ← hc, ih]
  exact h _

omit [IsFiniteMeasure ν] in
theorem norm_collisionSurvival_le_one : ‖collisionSurvival ν‖ ≤ 1 := by
  have h := norm_lpBoundedMulCLM_le (p := 2) (μ := ν) (φ := fun z => ((pairContrast z : ℝ) : ℂ))
    (Complex.measurable_ofReal.comp measurable_pairContrast) zero_le_one
    (norm_bound_ofReal abs_pairContrast_le_one)
  exact h

omit [IsFiniteMeasure ν] in
theorem norm_collisionSurvival_pow_apply_le (n : ℕ) (x : Lp ℂ 2 ν) :
    ‖(collisionSurvival ν ^ n) x‖ ≤ ‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_def, comp_apply]
    exact ((le_opNorm _ _).trans (mul_le_of_le_one_left (norm_nonneg _)
      (norm_collisionSurvival_le_one ν))).trans ih

/-- The exit masses decrease: `‖e_n‖ ≤ ‖e_0‖`. -/
theorem norm_collisionExitVector_le (n : ℕ) :
    ‖collisionExitVector ν n‖ ≤ ‖collisionExitVector ν 0‖ := by
  rw [collisionExitVector_eq, collisionExitVector_eq ν 0, pow_zero, one_def, id_apply]
  exact norm_collisionSurvival_pow_apply_le ν n _

variable (hν : ∀ᵐ z ∂ν, 0 < z.1 ∧ 0 < z.2)

include hν in
theorem hasSum_norm_collisionExitVector_sq :
    HasSum (fun n => ‖collisionExitVector ν n‖ ^ 2) (‖collisionState ν‖ ^ 2) :=
  hasSum_norm_exit_sq (collision_colligation ν) (collision_stable ν hν) _

include hν in
theorem summable_norm_collisionExitVector_sq :
    Summable fun n => ‖collisionExitVector ν n‖ ^ 2 :=
  (hasSum_norm_collisionExitVector_sq ν hν).summable

/-- **(CCRHD.12).**  The dephased collision record `𝖳_ν = ⊕ₙ |e_n⟩⟨e_n|`. -/
def collisionRecord : HistoryL2 (Lp ℂ 2 ν) →L[ℂ] HistoryL2 (Lp ℂ 2 ν) :=
  recordOp (collisionExitVector ν) (summable_norm_collisionExitVector_sq ν hν)

/-- The observability isometry `O` of the collision colligation. -/
def collisionObservability : Lp ℂ 2 ν →L[ℂ] HistoryL2 (Lp ℂ 2 ν) :=
  observability (collision_colligation ν) (collision_stable ν hν)

omit [IsFiniteMeasure ν] in
/-- **Theorem CCRHD-B.**  `O` is an isometry, `O*O = 1`. -/
theorem collisionObservability_isometry :
    (∀ f, ‖collisionObservability ν hν f‖ = ‖f‖) ∧
      adjoint (collisionObservability ν hν) ∘L collisionObservability ν hν = 1 :=
  ⟨norm_observability_apply _ _, adjoint_observability_comp _ _⟩

theorem collisionObservability_state (n : ℕ) :
    collisionObservability ν hν (collisionState ν) n = collisionExitVector ν n := rfl

/-- **(CCRHD.14).**  `𝖳_ν = D_hist(|O Ω_ν⟩⟨O Ω_ν|)`. -/
theorem collisionRecord_eq_historyDephased :
    collisionRecord ν hν = historyDephased (collisionObservability ν hν (collisionState ν)) :=
  recordOp_congr _ _ _ rfl

/-- **(CCRHD.14), dephasing limit.**  `∑_{n < N} P_n |O Ω_ν⟩⟨O Ω_ν| P_n → 𝖳_ν` in trace norm. -/
theorem tendsto_traceNorm_collisionRecord_sub :
    Tendsto (fun N => traceNorm (HistoryL2 (Lp ℂ 2 ν)) (collisionRecord ν hν -
      ∑ n ∈ Finset.range N, historyGrade n ∘L
        historyRankOne (collisionObservability ν hν (collisionState ν)) ∘L historyGrade n))
      atTop (𝓝 0) := by
  rw [collisionRecord_eq_historyDephased]
  exact tendsto_traceNorm_historyDephased_sub _

variable {ν} (hZ : 0 < collisionMass ν)

include hν hZ in
theorem tsum_norm_collisionExitVector_sq : ∑' n, ‖collisionExitVector ν n‖ ^ 2 = 1 := by
  rw [(hasSum_norm_collisionExitVector_sq ν hν).tsum_eq, norm_collisionState ν hZ, one_pow]

include hZ in
/-- **Theorem CCRHD-C for `ν`.**  `𝖳_ν ≥ 0`, `𝖳_ν ∈ S₁`, `tr 𝖳_ν = ‖𝖳_ν‖₁ = 1`. -/
theorem collisionRecord_nuclear :
    (collisionRecord ν hν).IsPositive ∧ MemSchattenClass 1 (collisionRecord ν hν) ∧
      adjoint (collisionRecord ν hν) = collisionRecord ν hν ∧
      opTrace (collisionRecord ν hν) = 1 ∧
      traceNorm (HistoryL2 (Lp ℂ 2 ν)) (collisionRecord ν hν) = 1 := by
  obtain ⟨hpos, hS1, htr⟩ := recordOp_traceClass (collisionExitVector ν)
    (summable_norm_collisionExitVector_sq ν hν)
  refine ⟨hpos, hS1, adjoint_recordOp _ _, ?_, ?_⟩
  · rw [collisionRecord, htr, tsum_norm_collisionExitVector_sq hν hZ, Complex.ofReal_one]
  · rw [collisionRecord, traceNorm_recordOp, tsum_norm_collisionExitVector_sq hν hZ]

/-- **(CCRHD.16) for `ν`.**  `tr((Q_N ⊗ 1) 𝖳_ν) = ‖Sᴺ Ω_ν‖²`. -/
theorem opTrace_historyTail_collisionRecord (N : ℕ) :
    opTrace (historyTailProjection N ∘L collisionRecord ν hν)
      = ((‖(collisionSurvival ν ^ N) (collisionState ν)‖ ^ 2 : ℝ) : ℂ) := by
  rw [collisionRecord, opTrace_historyTail_recordOp]
  exact congrArg (fun r : ℝ => (r : ℂ)) (hasSum_norm_exit_sq_tail (collision_colligation ν)
    (collision_stable ν hν) (collisionState ν) N).tsum_eq

/-- **Operator norm.**  `‖𝖳_ν‖ = ‖e_0‖²`. -/
theorem norm_collisionRecord : ‖collisionRecord ν hν‖ = ‖collisionExitVector ν 0‖ ^ 2 :=
  norm_recordOp _ _ (norm_collisionExitVector_le ν)

theorem norm_collisionExitVector_sq (n : ℕ) :
    ‖collisionExitVector ν n‖ ^ 2
      = ‖(collisionSurvival ν ^ n) (collisionState ν)‖ ^ 2
        - ‖(collisionSurvival ν ^ (n + 1)) (collisionState ν)‖ ^ 2 := by
  have h := norm_sq_add_norm_sq_of_colligation (collision_colligation ν)
    ((collisionSurvival ν ^ n) (collisionState ν))
  rw [pow_succ' (collisionSurvival ν) n, mul_def, comp_apply, collisionExitVector]
  linarith

include hZ in
/-- The first survival mass is positive: `‖S Ω_ν‖ > 0`. -/
theorem norm_collisionSurvival_state_pos :
    0 < ‖collisionSurvival ν (collisionState ν)‖ ^ 2 := by
  have h := norm_collisionSurvival_pow_state_sq ν 1
  rw [pow_one] at h
  rw [h]
  refine mul_pos (inv_pos.mpr hZ) ?_
  have hmeas : Measurable fun z => (pairContrast z ^ 2) ^ 1 * collisionProfile z ^ 2 :=
    ((measurable_pairContrast.pow_const 2).pow_const 1).mul
      (measurable_collisionProfile.pow_const 2)
  have hint : Integrable (fun z => (pairContrast z ^ 2) ^ 1 * collisionProfile z ^ 2) ν :=
    integrable_of_abs_le ν hmeas (C := 1) fun z => by
      rw [abs_of_nonneg (by positivity), pow_one]
      exact mul_le_one₀ (pairContrast_sq_le_one z) (sq_nonneg _)
        (by nlinarith [abs_collisionProfile_le_one z, sq_abs (collisionProfile z),
          abs_nonneg (collisionProfile z)])
  have hint0 : Integrable (fun z => collisionProfile z ^ 2) ν :=
    integrable_of_abs_le ν (measurable_collisionProfile.pow_const 2) (C := 1) fun z => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [abs_collisionProfile_le_one z, sq_abs (collisionProfile z),
        abs_nonneg (collisionProfile z)]
  rw [integral_pos_iff_support_of_nonneg (fun z => by positivity) hint]
  have hZ' := hZ
  rw [collisionMass, integral_pos_iff_support_of_nonneg (fun z => by positivity) hint0] at hZ'
  have hsupp : Function.support (fun z => collisionProfile z ^ 2)
      = Function.support (fun z => (pairContrast z ^ 2) ^ 1 * collisionProfile z ^ 2) := by
    ext z
    simp only [Function.mem_support, ne_eq, pow_one, mul_eq_zero, pow_eq_zero_iff,
      OfNat.ofNat_ne_zero, not_false_eq_true, not_or]
    constructor
    · intro h
      refine ⟨fun h0 => h ?_, h⟩
      rw [collisionProfile, h0, zero_mul]
    · exact fun h => h.2
  rwa [← hsupp]

include hZ in
/-- **(CCRHD.20) for `ν`.**  `‖𝖳_ν‖ = ‖e_0‖² < 1`. -/
theorem norm_collisionRecord_lt_one : ‖collisionRecord ν hν‖ < 1 := by
  rw [norm_collisionRecord, norm_collisionExitVector_sq, pow_zero, one_def, id_apply, zero_add,
    pow_one, norm_collisionState ν hZ, one_pow]
  linarith [norm_collisionSurvival_state_pos hZ]

end PairLaw

end GaloisForLFunctions.HTGeometry
