import GaloisForLFunctions.BlackHoleRingdown.TheCuspSpectrumIsDiscrete

/-!
# The kernel of the Weyl bound

Three tools for counting cusp forms from below.

* **Min–max for a diagonal operator** (`finrank_le_card_of_form_ge`). If a symmetric operator acts on a
  Hilbert basis by real eigenvalues `μ_i` and its quadratic form is at least `c‖f‖²` on a
  finite-dimensional subspace `V`, then at least `dim V` basis vectors have `μ_i ≥ c`.
* **Eigenvalue against mass** (`exists_kernelEigenvalue`). For a smooth profile `φ`, the point-pair
  operator acts on the basis vector of eigenvalue `λ` by a real number `κ`, and `λ |κ| ≤ ‖Dφ‖₁`, where
  `Dφ` is the radial Laplacian of the profile: `L_{Dφ} = -λ L_φ` on the eigenvector, and `‖L_{Dφ}‖ ≤ ‖Dφ‖₁`.
* **Narrow profiles** (`narrowProfile`). `φ_R(u) = β(u/R)` with a fixed bump `β`. Its mass is at least
  `πR/8` and the mass of its radial Laplacian is bounded independently of `R` (`narrow_mass_ge`,
  `exists_narrow_lap_mass_le`): the hyperbolic disc `u(i, w) ≤ r` has area between `πr/4` and `32πr`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped MatrixGroups UpperHalfPlane InnerProductSpace ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.DeckPointPair
  MaassFiniteDeckDirichlet SelbergMaassCongruenceTrace
open GaloisForLFunctions.HTGeometry (pairU)

namespace WeylBound

/-! ### Min–max -/

/-- **Min–max for a diagonal operator.** -/
theorem finrank_le_card_of_form_ge {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E)
    (hTs : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ) (μ : ι → ℝ)
    (hT : ∀ i, b i ∈ Module.End.eigenspace (T : E →ₗ[ℂ] E) (μ i : ℂ))
    {c : ℝ} (S : Finset ι) (hS : ∀ i, c ≤ μ i → i ∈ S) (V : Submodule ℂ E) [FiniteDimensional ℂ V]
    (hV : ∀ f ∈ V, c * ‖f‖ ^ 2 ≤ (⟪f, T f⟫_ℂ).re) : Module.finrank ℂ V ≤ S.card := by
  by_contra hlt
  push Not at hlt
  let L : V →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun f i => ⟪b i, (f : E)⟫_ℂ
      map_add' := fun f g => by
        funext i
        simp
      map_smul' := fun a f => by
        funext i
        simp }
  have hdim : Module.finrank ℂ (S → ℂ) < Module.finrank ℂ V := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
    exact hlt
  obtain ⟨f, hfker, hf0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt hdim)
  have hcoef : ∀ i ∈ S, ⟪b i, (f : E)⟫_ℂ = 0 := by
    intro i hi
    have h : L f = 0 := LinearMap.mem_ker.mp hfker
    exact congr_fun h ⟨i, hi⟩
  set x : E := (f : E) with hxdef
  have hconj : ∀ i, ⟪x, b i⟫_ℂ * ⟪b i, x⟫_ℂ = ((‖⟪b i, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [← inner_conj_symm, Complex.conj_mul', Complex.ofReal_pow]
  have hTx : ∀ i, ⟪x, b i⟫_ℂ * ⟪b i, T x⟫_ℂ = ((μ i * ‖⟪b i, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [← hTs, show T (b i) = (μ i : ℂ) • b i from Module.End.mem_eigenspace_iff.1 (hT i),
      inner_smul_left, Complex.conj_ofReal]
    have h := hconj i
    push_cast at h ⊢
    linear_combination (μ i : ℂ) * h
  have h1 : HasSum (fun i => ((‖⟪b i, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) ⟪x, x⟫_ℂ := by
    have h := (b.summable_inner_mul_inner x x).hasSum
    rw [b.tsum_inner_mul_inner] at h
    simpa only [hconj] using h
  have h2 : HasSum (fun i => ((μ i * ‖⟪b i, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) ⟪x, T x⟫_ℂ := by
    have h := (b.summable_inner_mul_inner x (T x)).hasSum
    rw [b.tsum_inner_mul_inner] at h
    simpa only [hTx] using h
  have h1r : HasSum (fun i => ‖⟪b i, x⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := by
    have h := Complex.reCLM.hasSum h1
    simp only [Complex.reCLM_apply, Complex.ofReal_re] at h
    have e : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
      have h := @inner_self_eq_norm_sq ℂ E _ _ _ x
      simpa using h
    rwa [e] at h
  have h2r : HasSum (fun i => μ i * ‖⟪b i, x⟫_ℂ‖ ^ 2) (⟪x, T x⟫_ℂ).re := by
    have h := Complex.reCLM.hasSum h2
    simpa only [Complex.reCLM_apply, Complex.ofReal_re] using h
  have h3 : HasSum (fun i => (c - μ i) * ‖⟪b i, x⟫_ℂ‖ ^ 2) (c * ‖x‖ ^ 2 - (⟪x, T x⟫_ℂ).re) := by
    have h := (h1r.mul_left c).sub h2r
    have e : (fun i => c * ‖⟪b i, x⟫_ℂ‖ ^ 2 - μ i * ‖⟪b i, x⟫_ℂ‖ ^ 2) =
        fun i => (c - μ i) * ‖⟪b i, x⟫_ℂ‖ ^ 2 := by
      funext i
      ring
    rwa [e] at h
  have hnonneg : ∀ i, 0 ≤ (c - μ i) * ‖⟪b i, x⟫_ℂ‖ ^ 2 := fun i => by
    by_cases hi : i ∈ S
    · rw [hcoef i hi, norm_zero]
      simp
    · have : μ i < c := lt_of_not_ge fun h => hi (hS i h)
      exact mul_nonneg (by linarith) (sq_nonneg _)
  obtain ⟨i₀, hi₀⟩ : ∃ i, ⟪b i, x⟫_ℂ ≠ 0 := by
    by_contra h
    push Not at h
    have hz : ‖x‖ ^ 2 = 0 := by
      have := h1r.tsum_eq
      rw [← this]
      simp [h]
    have hx0 : x = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
      exact norm_eq_zero.mp this
    exact hf0 (Subtype.ext hx0)
  have hi₀S : i₀ ∉ S := fun h => hi₀ (hcoef i₀ h)
  have hpos : 0 < (c - μ i₀) * ‖⟪b i₀, x⟫_ℂ‖ ^ 2 := by
    have : μ i₀ < c := lt_of_not_ge fun h => hi₀S (hS i₀ h)
    exact mul_pos (by linarith) (by positivity)
  have hsum_pos : 0 < c * ‖x‖ ^ 2 - (⟪x, T x⟫_ℂ).re := by
    exact lt_of_lt_of_le hpos (le_hasSum h3 i₀ fun j _ => hnonneg j)
  have := hV x f.2
  linarith

/-! ### The eigenvalue of a kernel on a basis vector -/

theorem norm_lap_op_le (P : SmoothProfile) (g : DeckL2 0) :
    ‖P.lap.op 0 g‖ ≤ (ppKernelMass (radialLap P.toFun)).toReal * ‖g‖ :=
  norm_ppLinear_le P.lap.differentiable.continuous P.lap.abs_le P.lap.radius_nonneg P.lap.support g

/-- **Eigenvalue against mass.** The kernel operator acts on each basis vector by a real `κ`, and
`λ |κ| ≤ ‖Dφ‖₁`. -/
theorem exists_kernelEigenvalue (P : SmoothProfile) (i : CuspEigenIndex 0) :
    ∃ κ : ℝ, (cuspEigenBasis 0 i : CuspidalL2 0) ∈
        Module.End.eigenspace (P.pp.cuspOp 0 : CuspidalL2 0 →ₗ[ℂ] CuspidalL2 0) (κ : ℂ) ∧
      i.1 * |κ| ≤ (ppKernelMass (radialLap P.toFun)).toReal := by
  have hq := one_quarter_le_cuspEigenBasis i
  set t := Real.sqrt (i.1 - 1 / 4)
  have ht : t ^ 2 = i.1 - 1 / 4 := Real.sq_sqrt (by linarith)
  set s : ℂ := 1 / 2 + (t : ℂ) * Complex.I
  have hs1 : s * (1 - s) = (i.1 : ℂ) := by
    have h : s * (1 - s) = 1 / 4 + ((t ^ 2 : ℝ) : ℂ) := by
      simp only [s]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [h, ht]
    push_cast
    ring
  obtain ⟨U, hU, hb⟩ := cuspEigenBasis_spec i
  have hmem : (cuspEigenBasis 0 i : CuspidalL2 0) ∈
      Module.End.eigenspace (P.pp.cuspOp 0 : CuspidalL2 0 →ₗ[ℂ] CuspidalL2 0)
        (selbergTransform P.toFun s) :=
    eigenClassSpace_le_eigenspace P hs1 ⟨U, hU, hb⟩
  have hne := (cuspEigenBasis 0).orthonormal.ne_zero i
  have hev : Module.End.HasEigenvalue (P.pp.cuspOp 0 : CuspidalL2 0 →ₗ[ℂ] CuspidalL2 0)
      (selbergTransform P.toFun s) := Module.End.hasEigenvalue_of_hasEigenvector ⟨hmem, hne⟩
  have hreal : ((selbergTransform P.toFun s).re : ℂ) = selbergTransform P.toFun s :=
    Complex.conj_eq_iff_re.1 ((P.pp.cuspOp_isSymmetric (N := 0)).conj_eigenvalue_eq_self hev)
  set κ := (selbergTransform P.toFun s).re
  have hK : (cuspEigenBasis 0 i : CuspidalL2 0) ∈
      Module.End.eigenspace (P.pp.cuspOp 0 : CuspidalL2 0 →ₗ[ℂ] CuspidalL2 0) (κ : ℂ) := by
    rw [hreal]
    exact hmem
  refine ⟨κ, hK, ?_⟩
  have hop : P.pp.op 0 (cuspEigenBasis 0 i : DeckL2 0) = (κ : ℂ) • (cuspEigenBasis 0 i : DeckL2 0) := by
    have h := congrArg Subtype.val (Module.End.mem_eigenspace_iff.1 hK)
    rw [← PairProfile.coe_cuspOp]
    exact h
  have hlap := P.lap_op_eigen hU
  rw [← hb, hop, smul_smul] at hlap
  have hnorm := norm_lap_op_le P (cuspEigenBasis 0 i : DeckL2 0)
  rw [hlap, norm_smul] at hnorm
  have h1 : ‖(cuspEigenBasis 0 i : DeckL2 0)‖ = 1 := by
    rw [← (cuspEigenBasis 0).orthonormal.1 i]
    rfl
  rw [h1, mul_one, mul_one, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ i.1)] at hnorm
  exact hnorm

/-! ### The area of a small hyperbolic disc -/

/-- The hyperbolic disc `u(i, w) ≤ r`. -/
def disc (r : ℝ) : Set ℍ := {w | pairU UpperHalfPlane.I w ≤ r}

theorem measurableSet_disc (r : ℝ) : MeasurableSet (disc r) :=
  measurableSet_le (continuous_pairU_right _).measurable measurable_const

theorem pairU_I_eq (w : ℍ) :
    pairU UpperHalfPlane.I w = ((w : ℂ).re ^ 2 + ((w : ℂ).im - 1) ^ 2) / (4 * w.im) := by
  unfold pairU
  rw [UpperHalfPlane.I_im, Complex.dist_eq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [UpperHalfPlane.coe_I, Complex.sub_re, Complex.I_re, Complex.sub_im, Complex.I_im]
  congr 1
  · ring
  · ring

/-- The hyperbolic density `1/y²`, as it appears in the volume. -/
theorem volume_le_of_im_ge {s : Set ℍ} (hs : ∀ w ∈ s, 1 / 2 ≤ w.im) :
    (volume : Measure ℍ) s ≤ 4 * volume (UpperHalfPlane.coe '' s) := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  calc ∫⁻ z : ℂ in UpperHalfPlane.coe '' s, ((1 / ‖z.im‖₊) ^ 2 : ℝ≥0)
      ≤ ∫⁻ z : ℂ in UpperHalfPlane.coe '' s, (4 : ℝ≥0∞) := by
        refine setLIntegral_mono measurable_const fun z hz => ?_
        obtain ⟨w, hw, rfl⟩ := hz
        have h1 : (1 / 2 : ℝ) ≤ (w : ℂ).im := hs w hw
        have h2 : ((1 / ‖(w : ℂ).im‖₊) ^ 2 : ℝ≥0) ≤ 4 := by
          rw [← NNReal.coe_le_coe]
          push_cast
          rw [Real.norm_eq_abs, abs_of_pos (by linarith), div_pow, one_pow, div_le_iff₀ (by positivity)]
          nlinarith
        exact_mod_cast h2
    _ = 4 * volume (UpperHalfPlane.coe '' s) := by rw [setLIntegral_const]

theorem volume_ge_of_im_le {s : Set ℍ} (hs : ∀ w ∈ s, w.im ≤ 2) :
    (1 / 4 : ℝ≥0∞) * volume (UpperHalfPlane.coe '' s) ≤ (volume : Measure ℍ) s := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  calc (1 / 4 : ℝ≥0∞) * volume (UpperHalfPlane.coe '' s) =
        ∫⁻ z : ℂ in UpperHalfPlane.coe '' s, (1 / 4 : ℝ≥0∞) := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ z : ℂ in UpperHalfPlane.coe '' s, ((1 / ‖z.im‖₊) ^ 2 : ℝ≥0) := by
        refine setLIntegral_mono (by fun_prop) fun z hz => ?_
        obtain ⟨w, hw, rfl⟩ := hz
        have h1 : (w : ℂ).im ≤ 2 := hs w hw
        have h0 : 0 < (w : ℂ).im := w.im_pos
        have h2 : (1 / 4 : ℝ≥0) ≤ ((1 / ‖(w : ℂ).im‖₊) ^ 2 : ℝ≥0) := by
          rw [← NNReal.coe_le_coe]
          push_cast
          rw [Real.norm_eq_abs, abs_of_pos h0, div_pow, one_pow, le_div_iff₀ (by positivity)]
          nlinarith
        have h3 : ((1 / 4 : ℝ≥0) : ℝ≥0∞) = (1 / 4 : ℝ≥0∞) := by
          rw [ENNReal.coe_div (by norm_num)]
          simp
        rw [← h3]
        exact_mod_cast h2

/-- **The disc has area at most `32πr`.** -/
theorem volume_disc_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 32) :
    (volume : Measure ℍ) (disc r) ≤ ENNReal.ofReal (32 * Real.pi * r) := by
  have hsub : (UpperHalfPlane.coe '' disc r) ⊆ Metric.closedBall (UpperHalfPlane.I : ℂ) (Real.sqrt (8 * r)) := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨h1, h2⟩ := CuspSpectrum.height_bounds hr hw
    have hu := hw
    change pairU UpperHalfPlane.I w ≤ r at hu
    rw [pairU_I_eq, div_le_iff₀ (by positivity)] at hu
    rw [Metric.mem_closedBall, Complex.dist_eq, ← Real.sqrt_sq (norm_nonneg _), ← Complex.normSq_eq_norm_sq]
    refine Real.sqrt_le_sqrt ?_
    rw [Complex.normSq_apply]
    simp only [UpperHalfPlane.coe_I, Complex.sub_re, Complex.I_re, Complex.sub_im, Complex.I_im]
    have hy : w.im ≤ 2 := by nlinarith
    change ((w : ℂ).re - 0) * ((w : ℂ).re - 0) + ((w : ℂ).im - 1) * ((w : ℂ).im - 1) ≤ 8 * r
    have : (w : ℂ).im = w.im := rfl
    nlinarith
  have hs : ∀ w ∈ disc r, 1 / 2 ≤ w.im := fun w hw => (CuspSpectrum.height_bounds hr hw).1.le
  calc (volume : Measure ℍ) (disc r) ≤ 4 * volume (UpperHalfPlane.coe '' disc r) := volume_le_of_im_ge hs
    _ ≤ 4 * volume (Metric.closedBall (UpperHalfPlane.I : ℂ) (Real.sqrt (8 * r))) := by
        gcongr
    _ = ENNReal.ofReal (32 * Real.pi * r) := by
        rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
          Real.sq_sqrt (by positivity), ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_ofNat 4,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-- **The disc has area at least `πr/4`.** -/
theorem volume_disc_ge {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 4) :
    ENNReal.ofReal (Real.pi * r / 4) ≤ (volume : Measure ℍ) (disc r) := by
  set B : Set ℍ := UpperHalfPlane.coe ⁻¹' Metric.closedBall (UpperHalfPlane.I : ℂ) (Real.sqrt r)
  have hsqrt : Real.sqrt r ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hr
  have hball : ∀ z ∈ Metric.closedBall (UpperHalfPlane.I : ℂ) (Real.sqrt r),
      1 / 2 ≤ z.im ∧ z.im ≤ 2 ∧ Complex.normSq (z - Complex.I) ≤ r := by
    intro z hz
    rw [Metric.mem_closedBall, Complex.dist_eq, UpperHalfPlane.coe_I] at hz
    have hn : Complex.normSq (z - Complex.I) ≤ r := by
      rw [Complex.normSq_eq_norm_sq]
      calc ‖z - Complex.I‖ ^ 2 ≤ Real.sqrt r ^ 2 := by gcongr
        _ = r := Real.sq_sqrt hr0
    have him : |z.im - 1| ≤ Real.sqrt r := by
      have := Complex.abs_im_le_norm (z - Complex.I)
      simp only [Complex.sub_im, Complex.I_im] at this
      linarith
    rw [abs_le] at him
    exact ⟨by linarith, by linarith, hn⟩
  have himage : (UpperHalfPlane.coe '' B) = Metric.closedBall (UpperHalfPlane.I : ℂ) (Real.sqrt r) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      have hpos : 0 < z.im := by linarith [(hball z hz).1]
      exact ⟨⟨z, hpos⟩, hz, rfl⟩
  have hBdisc : B ⊆ disc r := by
    intro w hw
    obtain ⟨h1, h2, h3⟩ := hball _ hw
    change pairU UpperHalfPlane.I w ≤ r
    rw [pairU_I_eq, div_le_iff₀ (by positivity)]
    rw [Complex.normSq_apply] at h3
    simp only [Complex.sub_re, Complex.I_re, Complex.sub_im, Complex.I_im] at h3
    have : (w : ℂ).im = w.im := rfl
    nlinarith
  have hs : ∀ w ∈ B, w.im ≤ 2 := fun w hw => (hball _ hw).2.1
  calc ENNReal.ofReal (Real.pi * r / 4)
      = (1 / 4 : ℝ≥0∞) * volume (Metric.closedBall (UpperHalfPlane.I : ℂ) (Real.sqrt r)) := by
        rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hr0,
          ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, ← ENNReal.ofReal_mul hr0,
          show (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4) by
            rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
    _ = (1 / 4 : ℝ≥0∞) * volume (UpperHalfPlane.coe '' B) := by rw [himage]
    _ ≤ volume B := volume_ge_of_im_le hs
    _ ≤ volume (disc r) := measure_mono hBdisc

/-! ### Narrow profiles -/

/-- The fixed bump: `1` on `[-½, ½]`, zero outside `[-1, 1]`. -/
def baseBump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

theorem contDiff_baseBump : ContDiff ℝ 3 baseBump := by
  simpa using baseBump.contDiff (n := 3)

theorem contDiff_baseBump_top : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) baseBump := baseBump.contDiff

theorem baseBump_eq_zero {v : ℝ} (hv : 1 < |v|) : baseBump v = 0 :=
  baseBump.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hv.le)

theorem baseBump_eq_one {v : ℝ} (hv : |v| ≤ 1 / 2) : baseBump v = 1 :=
  baseBump.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hv)

/-- **The narrow profile** `φ_R(u) = β(u/R)`. -/
def narrowProfile (R : ℝ) (hR : 0 < R) : SmoothProfile where
  toFun u := baseBump (u / R)
  radius := R
  radius_nonneg := hR.le
  contDiff := contDiff_baseBump.comp (contDiff_id.div_const R)
  support u hu := baseBump_eq_zero (by
    rw [abs_div, abs_of_pos hR, lt_div_iff₀ hR, one_mul]
    exact hu)

theorem narrow_toFun (R : ℝ) (hR : 0 < R) (u : ℝ) : (narrowProfile R hR).toFun u = baseBump (u / R) :=
  rfl

theorem narrow_nonneg (R : ℝ) (hR : 0 < R) (u : ℝ) : 0 ≤ (narrowProfile R hR).toFun u :=
  baseBump.nonneg

/-- **The mass of a narrow profile** is at least the area of the half disc. -/
theorem narrow_mass_ge {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1 / 2) :
    ENNReal.ofReal (Real.pi * R / 8) ≤ ppKernelMass (narrowProfile R hR).toFun := by
  have h1 : ENNReal.ofReal (Real.pi * R / 8) ≤ (volume : Measure ℍ) (disc (R / 2)) := by
    have := volume_disc_ge (r := R / 2) (by positivity) (by linarith)
    rwa [show Real.pi * (R / 2) / 4 = Real.pi * R / 8 by ring] at this
  refine h1.trans ?_
  unfold ppKernelMass
  rw [← lintegral_indicator_one (measurableSet_disc _)]
  refine lintegral_mono fun w => ?_
  by_cases hw : w ∈ disc (R / 2)
  · rw [Set.indicator_of_mem hw, Pi.one_apply]
    have hu0 : 0 ≤ pairU UpperHalfPlane.I w := by unfold pairU; positivity
    have hle : |pairU UpperHalfPlane.I w / R| ≤ 1 / 2 := by
      rw [abs_of_nonneg (by positivity), div_le_iff₀ hR]
      have := hw
      change pairU UpperHalfPlane.I w ≤ R / 2 at this
      linarith
    rw [narrow_toFun, baseBump_eq_one hle, abs_one, ENNReal.ofReal_one]
  · rw [Set.indicator_of_notMem hw]
    simp

/-- Bounds for the first two derivatives of the base bump. -/
theorem exists_baseBump_deriv_bounds :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ (∀ v, |deriv baseBump v| ≤ C₁) ∧
      (∀ v, |deriv (deriv baseBump) v| ≤ C₂) := by
  have hc1 : Continuous (deriv baseBump) := contDiff_baseBump.continuous_deriv (by norm_num)
  have hd : ContDiff ℝ 2 (deriv baseBump) :=
    (contDiff_infty_iff_deriv.mp contDiff_baseBump_top).2.of_le (by norm_cast)
  have hc2 : Continuous (deriv (deriv baseBump)) := hd.continuous_deriv (by norm_num)
  have hs1 : HasCompactSupport (deriv baseBump) := baseBump.hasCompactSupport.deriv
  obtain ⟨C₁, hC₁⟩ := hc1.bounded_above_of_compact_support hs1
  obtain ⟨C₂, hC₂⟩ := hc2.bounded_above_of_compact_support hs1.deriv
  exact ⟨C₁, C₂, le_trans (norm_nonneg _) (hC₁ 0), le_trans (norm_nonneg _) (hC₂ 0),
    fun v => hC₁ v, fun v => hC₂ v⟩

theorem deriv_narrow (R : ℝ) (hR : 0 < R) :
    deriv (narrowProfile R hR).toFun = fun u => deriv baseBump (u / R) / R := by
  funext u
  have hd : Differentiable ℝ baseBump := contDiff_baseBump.differentiable (by norm_num)
  have h := (hd (u / R)).hasDerivAt.comp u ((hasDerivAt_id' u).div_const R)
  rw [show (narrowProfile R hR).toFun = baseBump ∘ fun u => u / R from rfl, h.deriv]
  ring

theorem deriv_deriv_narrow (R : ℝ) (hR : 0 < R) :
    deriv (deriv (narrowProfile R hR).toFun) = fun u => deriv (deriv baseBump) (u / R) / R ^ 2 := by
  rw [deriv_narrow]
  funext u
  have hd2 : ContDiff ℝ 2 (deriv baseBump) :=
    (contDiff_infty_iff_deriv.mp contDiff_baseBump_top).2.of_le (by norm_cast)
  have hd : Differentiable ℝ (deriv baseBump) := hd2.differentiable (by norm_num)
  have h := ((hd (u / R)).hasDerivAt.comp u ((hasDerivAt_id' u).div_const R)).div_const R
  have e : (fun u => deriv baseBump (u / R) / R) = fun u => (deriv baseBump ∘ fun u => u / R) u / R :=
    rfl
  rw [e, h.deriv]
  ring

/-- **The radial Laplacian of a narrow profile has bounded mass**, independently of `R`. -/
theorem exists_narrow_lap_mass_le : ∃ A : ℝ, 0 ≤ A ∧ ∀ (R : ℝ) (hR : 0 < R), R ≤ 1 / 32 →
    (ppKernelMass (radialLap (narrowProfile R hR).toFun)).toReal ≤ A := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hb1, hb2⟩ := exists_baseBump_deriv_bounds
  refine ⟨32 * Real.pi * (2 * C₂ + 3 * C₁), by positivity, fun R hR hR32 => ?_⟩
  set P := narrowProfile R hR
  have hpt : ∀ w : ℍ, ENNReal.ofReal |radialLap P.toFun (pairU UpperHalfPlane.I w)| ≤
      (disc R).indicator (fun _ => ENNReal.ofReal ((2 * C₂ + 3 * C₁) / R)) w := by
    intro w
    set u := pairU UpperHalfPlane.I w
    have hu0 : 0 ≤ u := by unfold u pairU; positivity
    by_cases hw : w ∈ disc R
    · rw [Set.indicator_of_mem hw]
      refine ENNReal.ofReal_le_ofReal ?_
      have huR : u ≤ R := hw
      rw [radialLap, deriv_deriv_narrow, deriv_narrow]
      have e1 := hb1 (u / R)
      have e2 := hb2 (u / R)
      calc |u * (u + 1) * (deriv (deriv baseBump) (u / R) / R ^ 2) + (2 * u + 1) *
            (deriv baseBump (u / R) / R)|
          ≤ u * (u + 1) * (|deriv (deriv baseBump) (u / R)| / R ^ 2) +
              (2 * u + 1) * (|deriv baseBump (u / R)| / R) := by
            refine (abs_add_le _ _).trans (le_of_eq ?_)
            rw [abs_mul, abs_mul, abs_mul, abs_div, abs_div, abs_of_nonneg hu0,
              abs_of_nonneg (by linarith : (0 : ℝ) ≤ u + 1), abs_of_nonneg (by positivity : (0 : ℝ) ≤ R ^ 2),
              abs_of_pos hR, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * u + 1)]
        _ ≤ R * 2 * (C₂ / R ^ 2) + 3 * (C₁ / R) := by
            have hu1 : u * (u + 1) ≤ R * 2 := by nlinarith
            have hu2 : 2 * u + 1 ≤ 3 := by linarith
            exact add_le_add (mul_le_mul hu1 (div_le_div_of_nonneg_right e2 (by positivity))
              (by positivity) (by positivity))
              (mul_le_mul hu2 (div_le_div_of_nonneg_right e1 hR.le) (by positivity) (by norm_num))
        _ = (2 * C₂ + 3 * C₁) / R := by
            field_simp
    · rw [Set.indicator_of_notMem hw]
      have huR : R < u := lt_of_not_ge hw
      rw [P.radialLap_support u (by rwa [abs_of_nonneg hu0]), abs_zero, ENNReal.ofReal_zero]
  have hmass : ppKernelMass (radialLap P.toFun) ≤
      ENNReal.ofReal ((2 * C₂ + 3 * C₁) / R) * volume (disc R) := by
    unfold ppKernelMass
    calc ∫⁻ w, ENNReal.ofReal |radialLap P.toFun (pairU UpperHalfPlane.I w)|
        ≤ ∫⁻ w, (disc R).indicator (fun _ => ENNReal.ofReal ((2 * C₂ + 3 * C₁) / R)) w :=
          lintegral_mono hpt
      _ = ENNReal.ofReal ((2 * C₂ + 3 * C₁) / R) * volume (disc R) := by
          rw [lintegral_indicator_const (measurableSet_disc _)]
  have hvol := volume_disc_le hR.le hR32
  have hfin : ENNReal.ofReal ((2 * C₂ + 3 * C₁) / R) * volume (disc R) ≤
      ENNReal.ofReal (32 * Real.pi * (2 * C₂ + 3 * C₁)) := by
    calc ENNReal.ofReal ((2 * C₂ + 3 * C₁) / R) * volume (disc R)
        ≤ ENNReal.ofReal ((2 * C₂ + 3 * C₁) / R) * ENNReal.ofReal (32 * Real.pi * R) := by gcongr
      _ = ENNReal.ofReal (32 * Real.pi * (2 * C₂ + 3 * C₁)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  have h := hmass.trans hfin
  exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h)
    ENNReal.ofReal_ne_top).2 h |>.trans (le_of_eq (ENNReal.toReal_ofReal (by positivity)))

end WeylBound

end GaloisForLFunctions.BlackHoleRingdown
