import GaloisForLFunctions.ArithmeticPositiveDuality.ArchimedeanEigenvectorsAreInvisibleToTranslations
import GaloisForLFunctions.ArithmeticPositiveDuality.TheHilbertSpaceOfAPositiveDefiniteFunction
import GaloisForLFunctions.ArithmeticPositiveDuality.AnAtomicArchimedeanSpectrumBlindsTheSuccessor

/-!
# The successor sees only the continuous dilation spectrum

Let `φ` be positive definite on `Aff(ℚ)` with archimedean dilation part
`φ(x ↦ ux) = ∫ u^{ix} dν(x)` for `u > 0`, `ν` a finite measure on `ℝ`, and let `γ_1, …, γ_K` be
distinct reals.

**Theorem** (`successor_eq_blind_add_continuous`). There are a real `α` and a positive-definite
`ψ` on `Aff(ℚ)` with
* `φ(x ↦ x + b) = α + ψ(x ↦ x + b)` for every `b ≠ 0`,
* `ψ(x ↦ ux) = ∫ u^{ix} dν(x) − Σ_k ν{γ_k} u^{iγ_k}` for `u > 0`, so `ψ(1) = ν(ℝ) − Σ_k ν{γ_k}`.

**Corollary** (`norm_successor_sub_le`). `|φ(x ↦ x + b) − φ(x ↦ x + b')| ≤ 2(ν(ℝ) − Σ_k ν{γ_k})`
for `b, b' ≠ 0`: the successor oscillates by at most twice the dilation mass outside any finite
set of atoms. In particular an atomic `ν` forces a blind successor, and an absolutely continuous
`ν` can be seen (`successor_sees_autocorrelation`): the successor reads the continuous dilation
spectrum and nothing of the point spectrum.

Mechanism. In the GNS Hilbert space `(𝓗, π, ξ)` of `φ`, the two-prime box averages
`B_N = N⁻²Σ_{a,b<N} (2^a3^b)^{−iγ} π(x ↦ 2^a3^b x)ξ` have spectral transforms
`boxAvg(x − γ, N) → 1[x = γ]`, so they converge to an eigenvector `e_γ` of frequency `γ` with
`⟨ξ, e_γ⟩ = ‖e_γ‖² = ν{γ}` and `⟨e_γ, w⟩ = ⟨ξ, w⟩` for every eigenvector `w` of frequency `γ`.
The remainder `ζ = ξ − Σ_k e_{γ_k}` is orthogonal to these eigenspaces and has a continuous
dilation orbit, so translations do not mix it with the `e_{γ_k}`, and on the `e_{γ_k}` they act
by the blind constants (`ArchimedeanEigenvectorsAreInvisibleToTranslations`).
-/

open Complex MeasureTheory Filter Topology Finset
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

theorem continuous_archChar_left (u : ℚ) : Continuous fun x : ℝ => archChar x u := by
  unfold archChar; fun_prop

theorem inner_self_complex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E) :
    ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) :=
  Complex.ext (by simp [inner_self_eq_norm_sq (𝕜 := ℂ) x])
    (by simp [inner_self_im (𝕜 := ℂ) x])

/-- A vector state is positive definite. -/
theorem isPosDefOnGroup_vectorState {G E : Type*} [Group G] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (π : G →* (E ≃ₗᵢ[ℂ] E)) (ζ : E) :
    IsPosDefOnGroup fun g => ⟪ζ, π g ζ⟫_ℂ := by
  intro N x c
  refine ⟨‖∑ b, c b • π (x b) ζ‖ ^ 2, sq_nonneg _, ?_⟩
  have hinner : ∀ a b, ⟪ζ, π ((x a)⁻¹ * x b) ζ⟫_ℂ = ⟪π (x a) ζ, π (x b) ζ⟫_ℂ := by
    intro a b
    conv_rhs => rw [show x b = x a * ((x a)⁻¹ * x b) by group, map_mul,
      LinearIsometryEquiv.coe_mul, Function.comp_apply, LinearIsometryEquiv.inner_map_map]
  rw [← inner_self_complex, sum_inner]
  refine sum_congr rfl fun a _ => ?_
  beta_reduce
  rw [inner_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [inner_smul_left, inner_smul_right, hinner, Complex.star_def]
  ring

/-! ### Box kernels -/

theorem boxUnit_pos' (p : ℕ × ℕ) : 0 < ((boxUnit p.1 p.2 : ℚˣ) : ℚ) := boxUnit_pos _ _

/-- The kernel `x ↦ boxAvg(x − γ, N)` tends to the indicator of `γ`. -/
theorem tendsto_boxAvg_sub (γ x : ℝ) :
    Tendsto (fun N => boxAvg (x - γ) N) atTop (𝓝 (if x = γ then 1 else 0)) := by
  split_ifs with h
  · subst h
    simp only [sub_self]
    exact tendsto_const_nhds.congr' ((eventually_gt_atTop 0).mono fun N hN => (boxAvg_zero hN).symm)
  · exact tendsto_boxAvg (sub_ne_zero.mpr h)

theorem measurable_ind (γ : ℝ) : Measurable fun x : ℝ => if x = γ then (1 : ℂ) else 0 :=
  Measurable.ite (measurableSet_singleton γ) measurable_const measurable_const

theorem norm_ind_le (γ x : ℝ) : ‖(if x = γ then (1 : ℂ) else 0)‖ ≤ 1 := by
  split_ifs <;> simp

theorem integral_ind (ν : Measure ℝ) [IsFiniteMeasure ν] (γ : ℝ) :
    ∫ x, (if x = γ then (1 : ℂ) else 0) ∂ν = ν.real {γ} := by
  have h := integral_indicator_const (μ := ν) (1 : ℂ) (measurableSet_singleton γ)
  simp only [Set.indicator, Set.mem_singleton_iff, Complex.real_smul, mul_one] at h
  exact h

/-- Dominated convergence for bounded integrands against a finite measure. -/
theorem tendsto_integral_bdd (ν : Measure ℝ) [IsFiniteMeasure ν] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {G : ℕ → ℝ → E} {g : ℝ → E}
    (hG : ∀ N, AEStronglyMeasurable (G N) ν) {C : ℝ} (hC : ∀ N x, ‖G N x‖ ≤ C)
    (hlim : ∀ x, Tendsto (fun N => G N x) atTop (𝓝 (g x))) :
    Tendsto (fun N => ∫ x, G N x ∂ν) atTop (𝓝 (∫ x, g x ∂ν)) :=
  tendsto_integral_of_dominated_convergence (fun _ => C) hG (integrable_const C)
    (fun N => Eventually.of_forall (hC N)) (Eventually.of_forall hlim)

section Spectral

variable {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) {ν : Measure ℝ} [IsFiniteMeasure ν]

/-- The GNS triple of `φ`. -/
abbrev affRep := gnsRep (⟨φ, hφ⟩ : PosDefFn AffineGroupQ)
abbrev affVec : GNSHilbert (⟨φ, hφ⟩ : PosDefFn AffineGroupQ) := gnsCyclic _

theorem inner_affRep (g h : AffineGroupQ) :
    ⟪affRep hφ g (affVec hφ), affRep hφ h (affVec hφ)⟫_ℂ = φ (g⁻¹ * h) := by
  conv_lhs => rw [show h = g * (g⁻¹ * h) by group, rep_mul_apply]
  rw [LinearIsometryEquiv.inner_map_map]
  exact inner_gnsCyclic_gnsRep _ _

/-- A combination `Σ_i a_i π(x ↦ v_i x)ξ` of dilated cyclic vectors. -/
def dilVec {ι : Type*} (s : Finset ι) (v : ι → ℚˣ) (a : ι → ℂ) :
    GNSHilbert (⟨φ, hφ⟩ : PosDefFn AffineGroupQ) :=
  ∑ i ∈ s, a i • affRep hφ (dilation (v i)) (affVec hφ)

/-- Its spectral transform `x ↦ Σ_i a_i v_i^{ix}`. -/
def dilT {ι : Type*} (s : Finset ι) (v : ι → ℚˣ) (a : ι → ℂ) (x : ℝ) : ℂ :=
  ∑ i ∈ s, a i * archChar x (v i)

theorem continuous_dilT {ι : Type*} (s : Finset ι) (v : ι → ℚˣ) (a : ι → ℂ) :
    Continuous (dilT s v a) := by
  unfold dilT
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_archChar_left _)

theorem norm_dilT_le {ι : Type*} (s : Finset ι) (v : ι → ℚˣ) (a : ι → ℂ) (x : ℝ) :
    ‖dilT s v a x‖ ≤ ∑ i ∈ s, ‖a i‖ := by
  unfold dilT
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_archChar, mul_one]

variable (hν : ∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = ∫ x, archChar x u ∂ν)
include hφ hν

omit [IsFiniteMeasure ν] in
theorem inner_affRep_dilation {v w u : ℚˣ} (hv : 0 < (v : ℚ)) (hw : 0 < (w : ℚ)) (hu : 0 < (u : ℚ)) :
    ⟪affRep hφ (dilation v) (affVec hφ), affRep hφ (dilation u) (affRep hφ (dilation w) (affVec hφ))⟫_ℂ
      = ∫ x, conj (archChar x v) * archChar x w * archChar x u ∂ν := by
  rw [← rep_mul_apply, inner_affRep, ← map_inv, ← map_mul, ← map_mul,
    hν _ (by simp only [Units.val_mul, Units.val_inv_eq_inv_val]; positivity)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  rw [archChar_mul x (inv_pos.mpr hv) (mul_pos hu hw), archChar_mul x hu hw, archChar_inv x hv,
    Complex.star_def]
  ring

/-- **The spectral identity.** `⟨Σ a_i π_{v_i}ξ, π_u Σ b_j π_{w_j}ξ⟩ = ∫ conj(â) b̂ u^{ix} dν`. -/
theorem inner_dilVec {ι κ : Type*} (s : Finset ι) (t : Finset κ) {v : ι → ℚˣ} {w : κ → ℚˣ}
    (a : ι → ℂ) (b : κ → ℂ) (hv : ∀ i, 0 < (v i : ℚ)) (hw : ∀ j, 0 < (w j : ℚ)) {u : ℚˣ}
    (hu : 0 < (u : ℚ)) :
    ⟪dilVec hφ s v a, affRep hφ (dilation u) (dilVec hφ t w b)⟫_ℂ =
      ∫ x, conj (dilT s v a x) * dilT t w b x * archChar x u ∂ν := by
  have hint : ∀ i j, Integrable (fun x => conj (a i) * b j *
      (conj (archChar x (v i)) * archChar x (w j) * archChar x u)) ν := fun i j =>
    Integrable.of_bound ((continuous_const.mul (((Complex.continuous_conj.comp
      (continuous_archChar_left _)).mul (continuous_archChar_left _)).mul
      (continuous_archChar_left _))).aestronglyMeasurable) ‖conj (a i) * b j‖
      (Eventually.of_forall fun x => by
        simp only [norm_mul, Complex.norm_conj, norm_archChar, mul_one, le_refl])
  have hL : ⟪dilVec hφ s v a, affRep hφ (dilation u) (dilVec hφ t w b)⟫_ℂ =
      ∑ i ∈ s, ∑ j ∈ t, ∫ x, conj (a i) * b j *
        (conj (archChar x (v i)) * archChar x (w j) * archChar x u) ∂ν := by
    unfold dilVec
    rw [map_sum, sum_inner]
    refine sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, inner_sum, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [LinearIsometryEquiv.map_smul, inner_smul_right,
      inner_affRep_dilation hφ hν (hv i) (hw j) hu, integral_const_mul]
    ring
  rw [hL]
  calc ∑ i ∈ s, ∑ j ∈ t, ∫ x, conj (a i) * b j *
        (conj (archChar x (v i)) * archChar x (w j) * archChar x u) ∂ν
      = ∑ i ∈ s, ∫ x, ∑ j ∈ t, conj (a i) * b j *
        (conj (archChar x (v i)) * archChar x (w j) * archChar x u) ∂ν :=
        sum_congr rfl fun i _ => (integral_finsetSum _ fun j _ => hint i j).symm
    _ = ∫ x, ∑ i ∈ s, ∑ j ∈ t, conj (a i) * b j *
        (conj (archChar x (v i)) * archChar x (w j) * archChar x u) ∂ν :=
        (integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j).symm
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [dilT, map_sum, sum_mul]
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum, sum_mul]
        refine sum_congr rfl fun j _ => ?_
        rw [map_mul]
        ring

theorem inner_dilVec_one {ι κ : Type*} (s : Finset ι) (t : Finset κ) {v : ι → ℚˣ}
    {w : κ → ℚˣ} (a : ι → ℂ) (b : κ → ℂ) (hv : ∀ i, 0 < (v i : ℚ)) (hw : ∀ j, 0 < (w j : ℚ)) :
    ⟪dilVec hφ s v a, dilVec hφ t w b⟫_ℂ = ∫ x, conj (dilT s v a x) * dilT t w b x ∂ν := by
  have h := inner_dilVec hφ hν s t a b hv hw (u := 1) one_pos
  rw [map_one, rep_one_apply] at h
  rw [h]
  simp only [Units.val_one, archChar_one, mul_one]

/-- `‖Σ a_i π_{v_i}ξ‖² = ∫ |Σ a_i v_i^{ix}|² dν`. -/
theorem norm_sq_dilVec {ι : Type*} (s : Finset ι) {v : ι → ℚˣ} (a : ι → ℂ)
    (hv : ∀ i, 0 < (v i : ℚ)) :
    ‖dilVec hφ s v a‖ ^ 2 = ∫ x, ‖dilT s v a x‖ ^ 2 ∂ν := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_dilVec_one hφ hν s s a a hv hv]
  simp only [Complex.conj_mul', ← Complex.ofReal_pow, RCLike.re_to_complex]
  rw [integral_complex_ofReal, Complex.ofReal_re]

omit hν in
theorem dilVec_disjSum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (v : ι → ℚˣ) (w : κ → ℚˣ)
    (a : ι → ℂ) (b : κ → ℂ) :
    dilVec hφ (s.disjSum t) (Sum.elim v w) (Sum.elim a b) = dilVec hφ s v a + dilVec hφ t w b := by
  simp only [dilVec, sum_disjSum, Sum.elim_inl, Sum.elim_inr]

omit hν in
theorem dilVec_neg {ι : Type*} (s : Finset ι) (v : ι → ℚˣ) (a : ι → ℂ) :
    dilVec hφ s v (fun i => -a i) = -dilVec hφ s v a := by
  simp only [dilVec, neg_smul, sum_neg_distrib]

omit hφ hν in
theorem dilT_disjSum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (v : ι → ℚˣ) (w : κ → ℚˣ)
    (a : ι → ℂ) (b : κ → ℂ) (x : ℝ) :
    dilT (s.disjSum t) (Sum.elim v w) (Sum.elim a b) x = dilT s v a x + dilT t w b x := by
  simp only [dilT, sum_disjSum, Sum.elim_inl, Sum.elim_inr]

omit hφ hν in
theorem dilT_neg {ι : Type*} (s : Finset ι) (v : ι → ℚˣ) (a : ι → ℂ) (x : ℝ) :
    dilT s v (fun i => -a i) x = -dilT s v a x := by
  simp only [dilT, neg_mul, sum_neg_distrib]

/-- `‖X − Y‖² = ∫ |X̂ − Ŷ|² dν` for two dilation combinations. -/
theorem norm_sq_dilVec_sub {ι κ : Type*} (s : Finset ι) (t : Finset κ) {v : ι → ℚˣ}
    {w : κ → ℚˣ} (a : ι → ℂ) (b : κ → ℂ) (hv : ∀ i, 0 < (v i : ℚ)) (hw : ∀ j, 0 < (w j : ℚ)) :
    ‖dilVec hφ s v a - dilVec hφ t w b‖ ^ 2 = ∫ x, ‖dilT s v a x - dilT t w b x‖ ^ 2 ∂ν := by
  have h := norm_sq_dilVec hφ hν (s.disjSum t) (v := Sum.elim v w) (Sum.elim a fun j => -b j)
    (by rintro (i | j) <;> simp [hv, hw])
  rw [dilVec_disjSum, dilVec_neg, ← sub_eq_add_neg] at h
  simp only [dilT_disjSum, dilT_neg, ← sub_eq_add_neg] at h
  exact h

/-! ### Atoms as eigenvectors -/

omit hν in
/-- The cyclic vector is a one-term dilation combination. -/
theorem affVec_eq_dilVec :
    affVec hφ = dilVec hφ (univ : Finset Unit) (fun _ => 1) (fun _ => 1) := by
  rw [dilVec, univ_unique, sum_singleton, one_smul, map_one, rep_one_apply]

omit hφ hν in
theorem dilT_unit (x : ℝ) : dilT (univ : Finset Unit) (fun _ => (1 : ℚˣ)) (fun _ => 1) x = 1 := by
  simp [dilT, archChar_one]

omit hν in
/-- The box average `B_N = N⁻²Σ_{a,b<N} (2^a3^b)^{−iγ} π(x ↦ 2^a3^b x)ξ`. -/
def boxEigVec (γ : ℝ) (N : ℕ) : GNSHilbert (⟨φ, hφ⟩ : PosDefFn AffineGroupQ) :=
  dilVec hφ (range N ×ˢ range N) (fun p => boxUnit p.1 p.2)
    (fun p => (1 / (N : ℂ) ^ 2) * conj (archChar γ (boxUnit p.1 p.2)))

omit hφ hν in
theorem dilT_box (γ x : ℝ) (N : ℕ) :
    dilT (range N ×ˢ range N) (fun p => boxUnit p.1 p.2)
      (fun p => (1 / (N : ℂ) ^ 2) * conj (archChar γ (boxUnit p.1 p.2))) x = boxAvg (x - γ) N := by
  rw [dilT, sum_product, boxAvg_eq]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [archChar_sub, Complex.star_def]
  ring

omit hφ hν in
theorem continuous_boxAvg_sub (γ : ℝ) (N : ℕ) : Continuous fun x => boxAvg (x - γ) N :=
  (continuous_dilT _ _ _).congr fun x => dilT_box γ x N

omit hφ hν in
/-- The squared distance of the kernel to the indicator tends to zero in `L²(ν)`. -/
theorem tendsto_boxDefect (γ : ℝ) :
    Tendsto (fun N => ∫ x, ‖boxAvg (x - γ) N - (if x = γ then 1 else 0)‖ ^ 2 ∂ν) atTop (𝓝 0) := by
  have h := tendsto_integral_bdd ν (G := fun N x => ‖boxAvg (x - γ) N -
    (if x = γ then (1 : ℂ) else 0)‖ ^ 2) (g := fun _ => 0) (C := 4)
    (fun N => ((((continuous_boxAvg_sub γ N).measurable.sub (measurable_ind γ)).norm).pow_const
      2).aestronglyMeasurable)
    (fun N x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 : ‖boxAvg (x - γ) N - (if x = γ then (1 : ℂ) else 0)‖ ≤ 2 :=
        (norm_sub_le _ _).trans (by linarith [norm_boxAvg_le (x - γ) N, norm_ind_le γ x])
      nlinarith [norm_nonneg (boxAvg (x - γ) N - (if x = γ then (1 : ℂ) else 0))])
    (fun x => by
      have := ((tendsto_boxAvg_sub γ x).sub_const (if x = γ then (1 : ℂ) else 0)).norm.pow 2
      simpa using this)
  simpa using h

/-- Box averages are Cauchy. -/
theorem cauchySeq_boxEigVec (γ : ℝ) : CauchySeq (boxEigVec hφ γ) := by
  set ε : ℕ → ℝ := fun N => ∫ x, ‖boxAvg (x - γ) N - (if x = γ then 1 else 0)‖ ^ 2 ∂ν
  have hε := tendsto_boxDefect (ν := ν) γ
  have hint : ∀ N, Integrable (fun x => ‖boxAvg (x - γ) N - (if x = γ then (1 : ℂ) else 0)‖ ^ 2) ν :=
    fun N => Integrable.of_bound ((((continuous_boxAvg_sub γ N).measurable.sub
      (measurable_ind γ)).norm).pow_const 2).aestronglyMeasurable 4 (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h1 : ‖boxAvg (x - γ) N - (if x = γ then (1 : ℂ) else 0)‖ ≤ 2 :=
          (norm_sub_le _ _).trans (by linarith [norm_boxAvg_le (x - γ) N, norm_ind_le γ x])
        nlinarith [norm_nonneg (boxAvg (x - γ) N - (if x = γ then (1 : ℂ) else 0))])
  have hdist : ∀ N M, dist (boxEigVec hφ γ N) (boxEigVec hφ γ M) ^ 2 ≤ 2 * ε N + 2 * ε M := by
    intro N M
    rw [dist_eq_norm, boxEigVec, boxEigVec, norm_sq_dilVec_sub hφ hν _ _ _ _ boxUnit_pos' boxUnit_pos']
    simp only [dilT_box]
    rw [show 2 * ε N + 2 * ε M = ∫ x, (2 * ‖boxAvg (x - γ) N - (if x = γ then 1 else 0)‖ ^ 2 +
        2 * ‖boxAvg (x - γ) M - (if x = γ then 1 else 0)‖ ^ 2) ∂ν by
      rw [integral_add ((hint N).const_mul 2) ((hint M).const_mul 2), integral_const_mul,
        integral_const_mul]]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
      (((hint N).const_mul 2).add ((hint M).const_mul 2)) (Eventually.of_forall fun x => ?_)
    beta_reduce
    have h1 := norm_sub_le_norm_sub_add_norm_sub (boxAvg (x - γ) N) (if x = γ then (1 : ℂ) else 0)
      (boxAvg (x - γ) M)
    rw [norm_sub_rev (if x = γ then (1 : ℂ) else 0)] at h1
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖boxAvg (x - γ) N - (if x = γ then (1 : ℂ) else 0)‖ -
      ‖boxAvg (x - γ) M - (if x = γ then (1 : ℂ) else 0)‖)]
  rw [Metric.cauchySeq_iff']
  intro δ hδ
  obtain ⟨N, hN⟩ := (eventually_atTop.mp (hε.eventually (gt_mem_nhds (show (0 : ℝ) < δ ^ 2 / 4 by
    positivity))))
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hdist n N
  have h2 := hN n hn
  have h3 := hN N le_rfl
  have : dist (boxEigVec hφ γ n) (boxEigVec hφ γ N) ^ 2 < δ ^ 2 := by linarith
  exact (pow_lt_pow_iff_left₀ dist_nonneg hδ.le two_ne_zero).mp this

omit hν in
/-- The atom vector `e_γ = lim B_N`. -/
def atomVec (γ : ℝ) : GNSHilbert (⟨φ, hφ⟩ : PosDefFn AffineGroupQ) := limUnder atTop (boxEigVec hφ γ)

theorem tendsto_boxEigVec (γ : ℝ) : Tendsto (boxEigVec hφ γ) atTop (𝓝 (atomVec hφ γ)) :=
  (cauchySeq_boxEigVec hφ hν γ).tendsto_limUnder

/-- `⟨ξ, e_γ⟩ = ν{γ}`. -/
theorem inner_affVec_atomVec (γ : ℝ) : ⟪affVec hφ, atomVec hφ γ⟫_ℂ = ν.real {γ} := by
  have h1 : Tendsto (fun N => ⟪affVec hφ, boxEigVec hφ γ N⟫_ℂ) atTop (𝓝 ⟪affVec hφ, atomVec hφ γ⟫_ℂ) :=
    ((continuous_const.inner continuous_id : Continuous fun z :
      GNSHilbert (⟨φ, hφ⟩ : PosDefFn AffineGroupQ) => ⟪affVec hφ, z⟫_ℂ).tendsto _).comp
      (tendsto_boxEigVec hφ hν γ)
  have h2 : Tendsto (fun N => ⟪affVec hφ, boxEigVec hφ γ N⟫_ℂ) atTop (𝓝 (ν.real {γ} : ℂ)) := by
    have h := tendsto_integral_bdd ν (G := fun N x => boxAvg (x - γ) N)
      (g := fun x => if x = γ then (1 : ℂ) else 0) (C := 1)
      (fun N => (continuous_boxAvg_sub γ N).aestronglyMeasurable) (fun N x => norm_boxAvg_le _ _)
      (tendsto_boxAvg_sub γ)
    rw [integral_ind] at h
    refine h.congr fun N => ?_
    rw [affVec_eq_dilVec, boxEigVec, inner_dilVec_one hφ hν _ _ _ _ (fun _ => one_pos) boxUnit_pos']
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [dilT_unit, dilT_box, map_one, one_mul]
  exact tendsto_nhds_unique h1 h2

/-- `‖e_γ‖² = ν{γ}`. -/
theorem norm_sq_atomVec (γ : ℝ) : ‖atomVec hφ γ‖ ^ 2 = ν.real {γ} := by
  have h1 := ((continuous_norm.pow 2).tendsto _).comp (tendsto_boxEigVec hφ hν γ)
  have h2 : Tendsto (fun N => ‖boxEigVec hφ γ N‖ ^ 2) atTop (𝓝 (ν.real {γ})) := by
    have h := tendsto_integral_bdd ν (G := fun N x => ‖boxAvg (x - γ) N‖ ^ 2)
      (g := fun x => ‖(if x = γ then (1 : ℂ) else 0)‖ ^ 2) (C := 1)
      (fun N => ((continuous_boxAvg_sub γ N).norm.pow 2).aestronglyMeasurable)
      (fun N x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_one₀ (norm_nonneg _) (norm_boxAvg_le _ _))
      (fun x => ((tendsto_boxAvg_sub γ x).norm).pow 2)
    have hg : ∫ x, ‖(if x = γ then (1 : ℂ) else 0)‖ ^ 2 ∂ν = ν.real {γ} := by
      have h := integral_indicator_const (μ := ν) (1 : ℝ) (measurableSet_singleton γ)
      simp only [Set.indicator, Set.mem_singleton_iff, smul_eq_mul, mul_one] at h
      rw [← h]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      beta_reduce
      split_ifs <;> simp
    rw [hg] at h
    refine h.congr fun N => ?_
    rw [boxEigVec, norm_sq_dilVec hφ hν _ _ boxUnit_pos']
    simp only [dilT_box]
  exact tendsto_nhds_unique h1 h2

omit hν in
/-- Dilations of a combination: `π_u Σ a_i π_{v_i}ξ = Σ a_i π_{uv_i}ξ`. -/
theorem rep_dilation_dilVec {ι : Type*} (s : Finset ι) (v : ι → ℚˣ) (a : ι → ℂ) (u : ℚˣ) :
    affRep hφ (dilation u) (dilVec hφ s v a) = dilVec hφ s (fun i => u * v i) a := by
  simp only [dilVec, map_sum, LinearIsometryEquiv.map_smul, map_mul, LinearIsometryEquiv.coe_mul,
    Function.comp_apply]

/-- `e_γ` is an eigenvector of frequency `γ`. -/
theorem isArchEigen_atomVec (γ : ℝ) : IsArchEigen (affRep hφ) γ (atomVec hφ γ) := by
  intro u hu
  have hlim := ((affRep hφ (dilation u)).continuous.tendsto _).comp (tendsto_boxEigVec hφ hν γ)
  have hlim2 := (tendsto_boxEigVec hφ hν γ).const_smul (archChar γ u)
  have hsub := hlim.sub hlim2
  -- the defect tends to zero
  have h0 : Tendsto (fun N => affRep hφ (dilation u) (boxEigVec hφ γ N) -
      archChar γ u • boxEigVec hφ γ N) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hsq : Tendsto (fun N => ‖affRep hφ (dilation u) (boxEigVec hφ γ N) -
        archChar γ u • boxEigVec hφ γ N‖ ^ 2) atTop (𝓝 0) := by
      have h := tendsto_integral_bdd ν
        (G := fun N x => ‖(archChar x u - archChar γ u) * boxAvg (x - γ) N‖ ^ 2)
        (g := fun x => ‖(archChar x u - archChar γ u) * (if x = γ then (1 : ℂ) else 0)‖ ^ 2) (C := 4)
        (fun N => ((((continuous_archChar_left _).sub continuous_const).mul
          (continuous_boxAvg_sub γ N)).norm.pow 2).aestronglyMeasurable)
        (fun N x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul]
          have h1 : ‖archChar x u - archChar γ u‖ ≤ 2 := (norm_sub_le _ _).trans
            (by rw [norm_archChar, norm_archChar]; norm_num)
          have h2 := norm_boxAvg_le (x - γ) N
          have h3 : ‖archChar x u - archChar γ u‖ * ‖boxAvg (x - γ) N‖ ≤ 2 := by
            nlinarith [norm_nonneg (archChar x u - archChar γ u), norm_nonneg (boxAvg (x - γ) N)]
          nlinarith [mul_nonneg (norm_nonneg (archChar x u - archChar γ u))
            (norm_nonneg (boxAvg (x - γ) N))])
        (fun x => (((tendsto_boxAvg_sub γ x).const_mul _).norm).pow 2)
      have hg : ∫ x, ‖(archChar x u - archChar γ u) * (if x = γ then (1 : ℂ) else 0)‖ ^ 2 ∂ν = 0 := by
        rw [show (fun x => ‖(archChar x u - archChar γ u) * (if x = γ then (1 : ℂ) else 0)‖ ^ 2) =
            fun _ => (0 : ℝ) by
          funext x; split_ifs with hx <;> simp [hx]]
        simp
      rw [hg] at h
      refine h.congr fun N => ?_
      have key : ∀ x, dilT (range N ×ˢ range N) (fun p => u * boxUnit p.1 p.2)
          (fun p => (1 / (N : ℂ) ^ 2) * conj (archChar γ (boxUnit p.1 p.2))) x -
          dilT (range N ×ˢ range N) (fun p => boxUnit p.1 p.2)
          (fun p => archChar γ u * ((1 / (N : ℂ) ^ 2) * conj (archChar γ (boxUnit p.1 p.2)))) x =
          (archChar x u - archChar γ u) * boxAvg (x - γ) N := by
        intro x
        rw [← dilT_box γ x N, dilT, dilT, dilT, mul_sum, ← sum_sub_distrib]
        refine sum_congr rfl fun p _ => ?_
        simp only [Units.val_mul]
        rw [archChar_mul x hu (boxUnit_pos' p)]
        ring
      rw [boxEigVec, rep_dilation_dilVec, show archChar γ u • dilVec hφ (range N ×ˢ range N)
          (fun p => boxUnit p.1 p.2) (fun p => (1 / (N : ℂ) ^ 2) * conj (archChar γ (boxUnit p.1 p.2)))
          = dilVec hφ (range N ×ˢ range N) (fun p => boxUnit p.1 p.2)
            (fun p => archChar γ u * ((1 / (N : ℂ) ^ 2) * conj (archChar γ (boxUnit p.1 p.2)))) by
          simp only [dilVec, smul_sum, smul_smul],
        norm_sq_dilVec_sub hφ hν _ _ _ _ (fun p => by simpa using mul_pos hu (boxUnit_pos' p))
          boxUnit_pos']
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [key x]
    simpa [Real.sqrt_sq (norm_nonneg _)] using hsq.sqrt
  have := tendsto_nhds_unique hsub h0
  exact sub_eq_zero.mp this

/-- `⟨e_γ, w⟩ = ⟨ξ, w⟩` for every eigenvector `w` of frequency `γ`. -/
theorem inner_atomVec_eigen (γ : ℝ) {w : GNSHilbert (⟨φ, hφ⟩ : PosDefFn AffineGroupQ)}
    (hw : IsArchEigen (affRep hφ) γ w) : ⟪atomVec hφ γ, w⟫_ℂ = ⟪affVec hφ, w⟫_ℂ := by
  have h1 := ((continuous_id.inner continuous_const : Continuous fun z :
    GNSHilbert (⟨φ, hφ⟩ : PosDefFn AffineGroupQ) => ⟪z, w⟫_ℂ).tendsto _).comp (tendsto_boxEigVec hφ hν γ)
  have h2 : ∀ N, 0 < N → ⟪boxEigVec hφ γ N, w⟫_ℂ = ⟪affVec hφ, w⟫_ℂ := by
    intro N hN
    have hterm : ∀ p : ℕ × ℕ, ⟪affRep hφ (dilation (boxUnit p.1 p.2)) (affVec hφ), w⟫_ℂ =
        conj (archChar γ (boxUnit p.1 p.2)) * ⟪affVec hφ, w⟫_ℂ := by
      intro p
      have h := inner_rep_dilation (affRep hφ) (boxUnit p.1 p.2)⁻¹ (affVec hφ) w
      rw [inv_inv, hw _ (by simpa using boxUnit_pos' p), inner_smul_right] at h
      rw [← h, Units.val_inv_eq_inv_val, archChar_inv _ (boxUnit_pos' p), Complex.star_def]
    rw [boxEigVec, dilVec, sum_inner]
    simp only [inner_smul_left, hterm, map_mul, Complex.conj_conj, map_div₀, map_one, map_pow,
      Complex.conj_natCast]
    rw [sum_congr rfl fun p _ => by
      rw [show 1 / (N : ℂ) ^ 2 * archChar γ (boxUnit p.1 p.2) *
          (conj (archChar γ (boxUnit p.1 p.2)) * ⟪affVec hφ, w⟫_ℂ) =
          1 / (N : ℂ) ^ 2 * ⟪affVec hφ, w⟫_ℂ by
        rw [← mul_assoc, mul_assoc (1 / _), archChar_mul_conj, mul_one]],
      sum_const, card_product, card_range, nsmul_eq_mul]
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    push_cast
    field_simp
  have h3 : Tendsto (fun N => ⟪boxEigVec hφ γ N, w⟫_ℂ) atTop (𝓝 ⟪affVec hφ, w⟫_ℂ) :=
    tendsto_const_nhds.congr' ((eventually_gt_atTop 0).mono fun N hN => (h2 N hN).symm)
  exact tendsto_nhds_unique h1 h3

/-! ### The decomposition -/

theorem norm_sq_affVec : ‖affVec hφ‖ ^ 2 = ν.real Set.univ := by
  rw [affVec_eq_dilVec, norm_sq_dilVec hφ hν _ _ (fun _ => one_pos)]
  simp only [dilT_unit, norm_one, one_pow, integral_const, smul_eq_mul, mul_one]

omit [IsFiniteMeasure ν] in
theorem inner_affVec_rep_dilation {u : ℚˣ} (hu : 0 < (u : ℚ)) :
    ⟪affVec hφ, affRep hφ (dilation u) (affVec hφ)⟫_ℂ = ∫ x, archChar x u ∂ν := by
  rw [← hν u hu]
  exact inner_gnsCyclic_gnsRep _ _

variable {K : ℕ} (γ : Fin K → ℝ)

/-- The remainder `ζ = ξ − Σ_k e_{γ_k}`. -/
def remVec : GNSHilbert (⟨φ, hφ⟩ : PosDefFn AffineGroupQ) :=
  affVec hφ - ∑ k, atomVec hφ (γ k)

variable {γ} (hγ : Function.Injective γ)
include hγ

theorem inner_atomVec_atomVec {j k : Fin K} (hjk : j ≠ k) :
    ⟪atomVec hφ (γ j), atomVec hφ (γ k)⟫_ℂ = 0 := by
  have h := (isArchEigen_atomVec hφ hν (γ k)).inner_translation_eq_zero
    (isArchEigen_atomVec hφ hν (γ j)) (hγ.ne hjk.symm) 0
  rwa [rep_translation_zero] at h

theorem inner_remVec_eigen (k : Fin K) {w : GNSHilbert (⟨φ, hφ⟩ : PosDefFn AffineGroupQ)}
    (hw : IsArchEigen (affRep hφ) (γ k) w) : ⟪remVec hφ γ, w⟫_ℂ = 0 := by
  rw [remVec, inner_sub_left, sum_inner, sum_eq_single k, inner_atomVec_eigen hφ hν _ hw, sub_self]
  · intro j _ hjk
    have h := hw.inner_translation_eq_zero (isArchEigen_atomVec hφ hν (γ j)) (hγ.ne hjk.symm) 0
    rwa [rep_translation_zero] at h
  · intro h; exact absurd (mem_univ k) h

theorem inner_sum_atomVec_self :
    ⟪∑ k, atomVec hφ (γ k), ∑ k, atomVec hφ (γ k)⟫_ℂ = ∑ k, (ν.real {γ k} : ℂ) := by
  rw [sum_inner]
  refine sum_congr rfl fun j _ => ?_
  rw [inner_sum, sum_eq_single j (fun k _ hkj => inner_atomVec_atomVec hφ hν hγ hkj.symm)
    (fun h => absurd (mem_univ j) h), inner_self_complex, norm_sq_atomVec hφ hν]

/-- `‖ζ‖² = ν(ℝ) − Σ_k ν{γ_k}`. -/
theorem norm_sq_remVec : ‖remVec hφ γ‖ ^ 2 = ν.real Set.univ - ∑ k, ν.real {γ k} := by
  have h1 : ⟪affVec hφ, ∑ k, atomVec hφ (γ k)⟫_ℂ = ∑ k, (ν.real {γ k} : ℂ) := by
    rw [inner_sum]; exact sum_congr rfl fun k _ => inner_affVec_atomVec hφ hν _
  have h2 : ‖∑ k, atomVec hφ (γ k)‖ ^ 2 = ∑ k, ν.real {γ k} := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_sum_atomVec_self hφ hν hγ]
    simp
  rw [remVec, norm_sub_sq (𝕜 := ℂ), norm_sq_affVec hφ hν, h1, h2]
  simp only [RCLike.re_to_complex, Complex.re_sum, Complex.ofReal_re]
  ring

/-- `⟨ζ, π(x ↦ ux)ζ⟩ = ∫ u^{ix} dν − Σ_k ν{γ_k} u^{iγ_k}`. -/
theorem inner_remVec_dilation {u : ℚˣ} (hu : 0 < (u : ℚ)) :
    ⟪remVec hφ γ, affRep hφ (dilation u) (remVec hφ γ)⟫_ℂ =
      (∫ x, archChar x u ∂ν) - ∑ k, (ν.real {γ k} : ℂ) * archChar (γ k) u := by
  have he : ∀ k, affRep hφ (dilation u) (atomVec hφ (γ k)) = archChar (γ k) u • atomVec hφ (γ k) :=
    fun k => isArchEigen_atomVec hφ hν (γ k) u hu
  have hA : ⟪affVec hφ, affRep hφ (dilation u) (∑ k, atomVec hφ (γ k))⟫_ℂ =
      ∑ k, (ν.real {γ k} : ℂ) * archChar (γ k) u := by
    rw [map_sum, inner_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [he, inner_smul_right, inner_affVec_atomVec hφ hν, mul_comm]
  have hB : ⟪∑ k, atomVec hφ (γ k), affRep hφ (dilation u) (affVec hφ)⟫_ℂ =
      ∑ k, (ν.real {γ k} : ℂ) * archChar (γ k) u := by
    rw [sum_inner]
    refine sum_congr rfl fun k _ => ?_
    rw [inner_rep_dilation, isArchEigen_atomVec hφ hν (γ k) u⁻¹ (by simpa using hu),
      inner_smul_left, ← inner_conj_symm, inner_affVec_atomVec hφ hν, Complex.conj_ofReal,
      Units.val_inv_eq_inv_val, archChar_inv _ hu, Complex.star_def, Complex.conj_conj, mul_comm]
  have hC : ⟪∑ k, atomVec hφ (γ k), affRep hφ (dilation u) (∑ k, atomVec hφ (γ k))⟫_ℂ =
      ∑ k, (ν.real {γ k} : ℂ) * archChar (γ k) u := by
    rw [map_sum, sum_inner]
    refine sum_congr rfl fun j _ => ?_
    rw [inner_sum, sum_eq_single j (fun k _ hkj => by
        rw [he, inner_smul_right, inner_atomVec_atomVec hφ hν hγ hkj.symm, mul_zero])
      (fun h => absurd (mem_univ j) h), he, inner_smul_right, inner_self_complex,
      norm_sq_atomVec hφ hν, mul_comm]
  rw [remVec, map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
    inner_affVec_rep_dilation hφ hν hu, hA, hB, hC]
  ring

/-- The dilation orbit of `ζ` is continuous at `1`. -/
theorem tendsto_rep_remVec :
    Tendsto (fun j => affRep hφ (dilation (Units.mk0 (nearOne j) (nearOne_pos j).ne')⁻¹)
      (remVec hφ γ)) atTop (𝓝 (remVec hφ γ)) := by
  set u : ℕ → ℚˣ := fun j => (Units.mk0 (nearOne j) (nearOne_pos j).ne')⁻¹
  have hu : ∀ j, 0 < ((u j : ℚˣ) : ℚ) := fun j => by simpa [u] using nearOne_pos j
  have hchar : ∀ x : ℝ, Tendsto (fun j => archChar x (u j)) atTop (𝓝 1) := by
    intro x
    have h := (Complex.continuous_conj.tendsto 1).comp (tendsto_archChar_nearOne x)
    rw [map_one] at h
    refine h.congr fun j => ?_
    simp only [Function.comp_apply, u, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [archChar_inv _ (nearOne_pos j), Complex.star_def]
  have hint : Tendsto (fun j => ∫ x, archChar x (u j) ∂ν) atTop (𝓝 (∫ _, (1 : ℂ) ∂ν)) :=
    tendsto_integral_bdd ν (fun j => (continuous_archChar_left _).aestronglyMeasurable)
      (fun j x => (norm_archChar _ _).le) hchar
  have hsum : Tendsto (fun j => ∑ k, (ν.real {γ k} : ℂ) * archChar (γ k) (u j)) atTop
      (𝓝 (∑ k, (ν.real {γ k} : ℂ) * 1)) :=
    tendsto_finsetSum _ fun k _ => (hchar (γ k)).const_mul _
  have hin : Tendsto (fun j => ⟪remVec hφ γ, affRep hφ (dilation (u j)) (remVec hφ γ)⟫_ℂ) atTop
      (𝓝 (((ν.real Set.univ - ∑ k, ν.real {γ k} : ℝ)) : ℂ)) := by
    have h := hint.sub hsum
    simp only [integral_const, mul_one, Complex.real_smul] at h
    refine (h.congr fun j => (inner_remVec_dilation hφ hν hγ (hu j)).symm).trans ?_
    push_cast
    exact le_rfl
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun j => ‖affRep hφ (dilation (u j)) (remVec hφ γ) - remVec hφ γ‖ ^ 2)
      atTop (𝓝 0) := by
    have hre := (Complex.continuous_re.tendsto _).comp hin
    have hlim : Tendsto (fun j => 2 * ‖remVec hφ γ‖ ^ 2 - 2 *
        (⟪remVec hφ γ, affRep hφ (dilation (u j)) (remVec hφ γ)⟫_ℂ).re) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := 2 * ‖remVec hφ γ‖ ^ 2)).sub (hre.const_mul 2)
      simpa [norm_sq_remVec hφ hν hγ] using this
    refine hlim.congr fun j => ?_
    rw [norm_sub_sq (𝕜 := ℂ), LinearIsometryEquiv.norm_map, ← inner_conj_symm,
      RCLike.re_to_complex, Complex.conj_re]
    ring
  have h := hsq.sqrt
  simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at h
  exact h

/-- Translations do not mix `ζ` with the atoms. -/
theorem inner_remVec_translation_atomVec (k : Fin K) (b : ℚ) :
    ⟪remVec hφ γ, affRep hφ (translation b) (atomVec hφ (γ k))⟫_ℂ = 0 :=
  (isArchEigen_atomVec hφ hν (γ k)).inner_translation_eq_zero_of_continuous
    (fun _ hw => inner_remVec_eigen hφ hν hγ k hw) (tendsto_rep_remVec hφ hν hγ) b

/-- **The successor sees only the continuous dilation spectrum.** For `b ≠ 0`,
`φ(x ↦ x + b) = α + ⟨ζ, π(x ↦ x + b)ζ⟩` with `α` real and independent of `b`. -/
theorem successor_eq_blind_add_rem :
    ∃ α : ℝ, ∀ b : ℚ, b ≠ 0 →
      φ (translation b) = α + ⟪remVec hφ γ, affRep hφ (translation b) (remVec hφ γ)⟫_ℂ := by
  choose α hα using fun k => (isArchEigen_atomVec hφ hν (γ k)).inner_translation_eq
  refine ⟨∑ k, α k, fun b hb => ?_⟩
  set S := ∑ k, atomVec hφ (γ k)
  set ζ := remVec hφ γ
  have hξ : affVec hφ = S + ζ := by simp only [ζ, remVec, S, add_sub_cancel]
  have hSS : ⟪S, affRep hφ (translation b) S⟫_ℂ = ∑ k, (α k : ℂ) := by
    rw [map_sum, sum_inner]
    refine sum_congr rfl fun j _ => ?_
    rw [inner_sum, sum_eq_single j (fun k _ hkj =>
        (isArchEigen_atomVec hφ hν (γ k)).inner_translation_eq_zero
          (isArchEigen_atomVec hφ hν (γ j)) (hγ.ne hkj) b)
      (fun h => absurd (mem_univ j) h), hα j b hb]
  have hζS : ⟪ζ, affRep hφ (translation b) S⟫_ℂ = 0 := by
    rw [map_sum, inner_sum]
    exact sum_eq_zero fun k _ => inner_remVec_translation_atomVec hφ hν hγ k b
  have hSζ : ⟪S, affRep hφ (translation b) ζ⟫_ℂ = 0 := by
    rw [sum_inner]
    refine sum_eq_zero fun k _ => ?_
    rw [show b = -(-b) by ring, inner_rep_translation_neg, ← inner_conj_symm,
      inner_remVec_translation_atomVec hφ hν hγ k, map_zero]
  have hφτ : φ (translation b) =
      ⟪affVec hφ, affRep hφ (translation b) (affVec hφ)⟫_ℂ :=
    (inner_gnsCyclic_gnsRep (⟨φ, hφ⟩ : PosDefFn AffineGroupQ) (translation b)).symm
  rw [hφτ, hξ, map_add, inner_add_left, inner_add_right, inner_add_right, hSS, hζS, hSζ]
  push_cast
  ring

/-- **The successor oscillates by at most twice the non-atomic dilation mass.** -/
theorem norm_successor_sub_le {b b' : ℚ} (hb : b ≠ 0) (hb' : b' ≠ 0) :
    ‖φ (translation b) - φ (translation b')‖ ≤ 2 * (ν.real Set.univ - ∑ k, ν.real {γ k}) := by
  obtain ⟨α, hα⟩ := successor_eq_blind_add_rem hφ hν hγ
  rw [hα b hb, hα b' hb', add_sub_add_left_eq_sub, ← norm_sq_remVec hφ hν hγ]
  refine (norm_sub_le _ _).trans ?_
  have h : ∀ c : ℚ, ‖⟪remVec hφ γ, affRep hφ (translation c) (remVec hφ γ)⟫_ℂ‖ ≤
      ‖remVec hφ γ‖ ^ 2 := fun c => by
    refine (norm_inner_le_norm _ _).trans ?_
    rw [LinearIsometryEquiv.norm_map, sq]
  linarith [h b, h b']

/-- **Structure theorem.** The successor of `φ` is a blind constant plus the successor of a
positive-definite `ψ` whose dilation part is `ν` with the atoms `γ_k` removed. -/
theorem successor_eq_blind_add_continuous :
    ∃ (α : ℝ) (ψ : AffineGroupQ → ℂ), IsPosDefOnGroup ψ ∧
      ψ 1 = ((ν.real Set.univ - ∑ k, ν.real {γ k} : ℝ) : ℂ) ∧
      (∀ u : ℚˣ, 0 < (u : ℚ) →
        ψ (dilation u) = (∫ x, archChar x u ∂ν) - ∑ k, (ν.real {γ k} : ℂ) * archChar (γ k) u) ∧
      ∀ b : ℚ, b ≠ 0 → φ (translation b) = α + ψ (translation b) := by
  obtain ⟨α, hα⟩ := successor_eq_blind_add_rem hφ hν hγ
  refine ⟨α, fun g => ⟪remVec hφ γ, affRep hφ g (remVec hφ γ)⟫_ℂ,
    isPosDefOnGroup_vectorState _ _, ?_, fun u hu => inner_remVec_dilation hφ hν hγ hu, hα⟩
  show ⟪remVec hφ γ, affRep hφ 1 (remVec hφ γ)⟫_ℂ = _
  rw [map_one, LinearIsometryEquiv.coe_one, id, inner_self_complex, norm_sq_remVec hφ hν hγ]

end Spectral

end GaloisForLFunctions.ArithmeticPositiveDuality
