import GaloisForLFunctions.HTGeometry.SourceGramianSylvester
import GaloisForLFunctions.HTGeometry.ComplexJacobiFormula

/-!
# Positive Gram formation of a cyclic source and its withheld responses

For a cyclic source `(L, v)` the Gramian `G = ∫₀^∞ |x(t)⟩⟨x(t)| dt` is positive definite and is
the unique solution of `L G + G L = |v⟩⟨v|` `(SR.12)`: if `⟨z, G z⟩ = ∫ |⟨z, x(t)⟩|² = 0`, then
`z` is orthogonal to the orbit, which spans.

For a self-adjoint intervention `K` and small real `ε`, `L + εK` stays coercive and its Gramian
`G_ε` satisfies `Λ(G_ε - G) = -ε (K G_ε + G_ε K)` with `Λ X = L X + X L`.  The operator
`Ġ = ∫₀^∞ (|Y_K⟩⟨x| + |x⟩⟨Y_K|) dt` `(SR.13)` satisfies `Λ Ġ = -(K G + G K)` `(SR.14)` (weak
fundamental theorem of calculus on the half-line), and the inverse bound for `Λ` turns the two
identities into `d/dε G_ε |₀ = Ġ`.  Positivity of `G` makes `K ↦ K G + G K` invertible, so `Ġ`
reconstructs `K` `(SR.15)`; the inverse cost `C = G⁻¹` and `log det G` respond by
`Ċ = -C Ġ C` `(SR.16)` and `tr (C Ġ)` `(SR.17)`.
-/

open Filter Topology Set MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

attribute [local instance] operatorRatAlgebra

namespace CyclicSource

variable (σ : CyclicSource H)

/-! ### The source Gramian -/

/-- The source Gramian `G = ∫₀^∞ |x(t)⟩⟨x(t)| dt` `(SR.6)`. -/
def gram : H →L[ℂ] H := gramian σ.L σ.v

/-- **`(SR.12)`: the Lyapunov law** `L G + G L = |v⟩⟨v|`. -/
theorem lyapunov_gram :
    σ.L * σ.gram + σ.gram * σ.L = InnerProductSpace.rankOne ℂ σ.v σ.v := by
  obtain ⟨c, hc, hcoer⟩ := σ.exists_coercive
  exact lyapunov_gramian σ.isSelfAdjoint hc hcoer σ.v

/-- The Gramian is the unique solution of the Lyapunov equation. -/
theorem eq_gram_of_lyapunov {X : H →L[ℂ] H}
    (hX : σ.L * X + X * σ.L = InnerProductSpace.rankOne ℂ σ.v σ.v) : X = σ.gram := by
  obtain ⟨c, hc, hcoer⟩ := σ.exists_coercive
  exact eq_gramian_of_lyapunov σ.isSelfAdjoint hc hcoer σ.v hX

theorem isSelfAdjoint_gram : IsSelfAdjoint σ.gram := by
  obtain ⟨c, hc, hcoer⟩ := σ.exists_coercive
  exact isSelfAdjoint_gramian hc hcoer σ.v

theorem inner_gram (a b : H) :
    ⟪a, σ.gram b⟫_ℂ = ∫ t in Ioi (0 : ℝ), ⟪a, σ.x t⟫_ℂ * ⟪σ.x t, b⟫_ℂ := by
  obtain ⟨c, hc, hcoer⟩ := σ.exists_coercive
  exact inner_gramian hc hcoer σ.v a b

/-- **The Gramian is positive definite.** -/
theorem gram_pos {z : H} (hz : z ≠ 0) : 0 < RCLike.re ⟪z, σ.gram z⟫_ℂ := by
  obtain ⟨c, hc, hcoer⟩ := σ.exists_coercive
  rw [gram, inner_gramian_self hc hcoer, RCLike.re_to_complex, Complex.ofReal_re]
  have hex : ∃ t ∈ Ioo (0 : ℝ) 1, ⟪z, σ.x t⟫_ℂ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hle : Submodule.span ℂ (σ.x '' Ioo 0 1) ≤ (ℂ ∙ z)ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨t, ht, rfl⟩
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hcon t ht)
    rw [σ.span_orbit_Ioo one_pos] at hle
    have hzz :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle (Submodule.mem_top (x := z)))
    exact hz (inner_self_eq_zero.mp hzz)
  obtain ⟨t₀, ht₀, hne⟩ := hex
  set f : ℝ → ℝ := fun t => ‖⟪z, expNeg σ.L t σ.v⟫_ℂ‖ ^ 2
  have hfc : Continuous f :=
    ((continuous_const.inner (continuous_expNeg_apply σ.L σ.v)).norm).pow 2
  have hint : IntegrableOn f (Ioi 0) := by
    refine integrableOn_Ioi_of_exp_bound hfc (δ := 2 * c) (C := ‖z‖ ^ 2 * ‖σ.v‖ ^ 2)
      (by positivity) fun t ht => ?_
    have hx := norm_exp_neg_le σ.L hcoer ht.le σ.v
    have h1 : ‖⟪z, expNeg σ.L t σ.v⟫_ℂ‖ ≤ ‖z‖ * (Real.exp (-(c * t)) * ‖σ.v‖) :=
      (norm_inner_le_norm _ _).trans (by gcongr)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖⟪z, expNeg σ.L t σ.v⟫_ℂ‖ ^ 2 ≤ (‖z‖ * (Real.exp (-(c * t)) * ‖σ.v‖)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = ‖z‖ ^ 2 * ‖σ.v‖ ^ 2 * Real.exp (-(2 * c * t)) := by
          rw [show -(2 * c * t) = -(c * t) + -(c * t) by ring, Real.exp_add]
          ring
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun t => by simp only [Pi.zero_apply]; positivity) hint]
  refine (hfc.isOpen_support.inter isOpen_Ioi).measure_pos volume ⟨t₀, ?_, ht₀.1⟩
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)

/-- The Gramian is coercive. -/
theorem exists_gram_coercive : ∃ c > 0, ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, σ.gram y⟫_ℂ :=
  exists_coercive_of_pos σ.gram fun _ hx => σ.gram_pos hx

/-- The Gramian is invertible. -/
theorem isUnit_gram : IsUnit σ.gram := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  have hinj : Function.Injective σ.gram := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    by_contra hne
    have h := σ.gram_pos hne
    rw [hz, inner_zero_right, map_zero] at h
    exact lt_irrefl 0 h
  exact ⟨hinj, LinearMap.injective_iff_surjective (f := (σ.gram : H →ₗ[ℂ] H)).mp hinj⟩

/-- **The positive Sylvester equation** `K G + G K = B` has exactly one solution. -/
theorem existsUnique_gram_sylvester (B : H →L[ℂ] H) :
    ∃! K : H →L[ℂ] H, K * σ.gram + σ.gram * K = B := by
  obtain ⟨c, hc, hcoer⟩ := σ.exists_gram_coercive
  obtain ⟨X, hX, huniq⟩ := existsUnique_sylvester hc hcoer B
  refine ⟨X, ?_, fun Y hY => huniq Y ?_⟩
  · simp only
    rw [add_comm]
    exact hX
  · simp only at hY ⊢
    rw [add_comm]
    exact hY

theorem eq_zero_of_gram_sylvester {K : H →L[ℂ] H} (hK : K * σ.gram + σ.gram * K = 0) :
    K = 0 := by
  obtain ⟨c, hc, hcoer⟩ := σ.exists_gram_coercive
  exact eq_zero_of_sylvester hc hcoer (by rw [add_comm]; exact hK)

/-- The determinant of the Gramian is a positive real number. -/
theorem exists_det_gram_eq_pos :
    ∃ r : ℝ, 0 < r ∧ LinearMap.det (σ.gram : H →ₗ[ℂ] H) = r := by
  have hT : (σ.gram : H →ₗ[ℂ] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp σ.isSelfAdjoint_gram
  set n := Module.finrank ℂ H
  have hn : Module.finrank ℂ H = n := rfl
  refine ⟨∏ i, hT.eigenvalues hn i, Finset.prod_pos fun i _ => ?_, ?_⟩
  · set e := hT.eigenvectorBasis hn i
    have he : ‖e‖ = 1 := (hT.eigenvectorBasis hn).orthonormal.1 i
    have hne : e ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at he
      exact zero_ne_one he
    have hpos := σ.gram_pos hne
    have happ : σ.gram e = ((hT.eigenvalues hn i : ℝ) : ℂ) • e := hT.apply_eigenvectorBasis hn i
    rw [happ, inner_smul_right, inner_self_eq_norm_sq_to_K, he] at hpos
    simpa using hpos
  · rw [hT.det_eq_prod_eigenvalues hn, Complex.ofReal_prod]
    rfl

/-! ### Perturbed sources -/

variable {K : H →L[ℂ] H}

omit [FiniteDimensional ℂ H] in
theorem isSelfAdjoint_add_smul (hK : IsSelfAdjoint K) (ε : ℝ) :
    IsSelfAdjoint (σ.L + ε • K) := by
  have hεK : IsSelfAdjoint (ε • K) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hK ⊢
    intro x y
    simp only [ContinuousLinearMap.coe_coe, smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ),
      inner_smul_left, inner_smul_right, RCLike.conj_ofReal]
    rw [show ⟪K x, y⟫_ℂ = ⟪x, K y⟫_ℂ from hK x y]
  exact σ.isSelfAdjoint.add hεK

omit [FiniteDimensional ℂ H] in
/-- A small intervention keeps the generator coercive with half the constant. -/
theorem coercive_add_smul {c : ℝ} (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, σ.L y⟫_ℂ)
    {ε : ℝ} (hε : |ε| * ‖K‖ ≤ c / 2) (y : H) :
    c / 2 * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, (σ.L + ε • K) y⟫_ℂ := by
  have h1 : |RCLike.re ⟪y, (ε • K) y⟫_ℂ| ≤ |ε| * ‖K‖ * ‖y‖ ^ 2 := by
    calc |RCLike.re ⟪y, (ε • K) y⟫_ℂ| ≤ ‖⟪y, (ε • K) y⟫_ℂ‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖y‖ * ‖(ε • K) y‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (‖ε • K‖ * ‖y‖) := by gcongr; exact (ε • K).le_opNorm y
      _ = |ε| * ‖K‖ * ‖y‖ ^ 2 := by rw [norm_smul, Real.norm_eq_abs]; ring
  have h2 : |ε| * ‖K‖ * ‖y‖ ^ 2 ≤ c / 2 * ‖y‖ ^ 2 := mul_le_mul_of_nonneg_right hε (sq_nonneg _)
  rw [add_apply, inner_add_right, map_add]
  linarith [hcoer y, neg_abs_le (RCLike.re ⟪y, (ε • K) y⟫_ℂ)]

/-- The perturbed Gramian `G_{ε,K} = ∫₀^∞ |x_{ε,K}(t)⟩⟨x_{ε,K}(t)| dt`. -/
def perturbedGram (K : H →L[ℂ] H) (ε : ℝ) : H →L[ℂ] H := gramian (σ.L + ε • K) σ.v

omit [FiniteDimensional ℂ H] in
theorem perturbedGram_zero (K : H →L[ℂ] H) : σ.perturbedGram K 0 = σ.gram := by
  simp [perturbedGram, gram]

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
/-- Small interventions are eventually admissible. -/
theorem eventually_small (K : H →L[ℂ] H) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| * ‖K‖ ≤ c / 2 := by
  have hcont : Continuous fun ε : ℝ => |ε| * ‖K‖ := by fun_prop
  have h : Tendsto (fun ε : ℝ => |ε| * ‖K‖) (𝓝 0) (𝓝 0) := by
    simpa using hcont.tendsto (0 : ℝ)
  exact h.eventually (ge_mem_nhds (by positivity))

/-- The perturbed Lyapunov identity `Λ(G_ε - G) = -ε (K G_ε + G_ε K)`. -/
theorem lyapunov_perturbedGram_sub (hK : IsSelfAdjoint K) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, σ.L y⟫_ℂ) {ε : ℝ}
    (hε : |ε| * ‖K‖ ≤ c / 2) :
    σ.L * (σ.perturbedGram K ε - σ.gram) + (σ.perturbedGram K ε - σ.gram) * σ.L =
      -(ε • (K * σ.perturbedGram K ε + σ.perturbedGram K ε * K)) := by
  have hP := lyapunov_gramian (σ.isSelfAdjoint_add_smul hK ε) (by positivity : 0 < c / 2)
    (σ.coercive_add_smul hcoer hε) σ.v
  have h0 := σ.lyapunov_gram
  rw [← perturbedGram] at hP
  set Gε := σ.perturbedGram K ε
  rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm] at hP
  rw [mul_sub, sub_mul, smul_add]
  calc σ.L * Gε - σ.L * σ.gram + (Gε * σ.L - σ.gram * σ.L)
      = (σ.L * Gε + ε • (K * Gε) + (Gε * σ.L + ε • (Gε * K))) -
          (σ.L * σ.gram + σ.gram * σ.L) - (ε • (K * Gε) + ε • (Gε * K)) := by abel
    _ = -(ε • (K * Gε) + ε • (Gε * K)) := by rw [hP, h0, sub_self, zero_sub]

omit [FiniteDimensional ℂ H] in
/-- The perturbed Gramians are uniformly bounded. -/
theorem norm_perturbedGram_le {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, σ.L y⟫_ℂ) {ε : ℝ}
    (hε : |ε| * ‖K‖ ≤ c / 2) : ‖σ.perturbedGram K ε‖ ≤ ‖σ.v‖ ^ 2 / c := by
  have h := norm_gramian_le (by positivity : 0 < c / 2) (σ.coercive_add_smul hcoer hε) σ.v
  rw [show 2 * (c / 2) = c by ring] at h
  exact h

/-! ### Size of the first response -/

section ResponseBounds

variable {c : ℝ}

omit [FiniteDimensional ℂ H] in
/-- `‖Y_K(t)‖ ≤ t e^{-ct} ‖K‖ ‖v‖`. -/
theorem norm_response_le (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, σ.L y⟫_ℂ)
    (K : H →L[ℂ] H) {t : ℝ} (ht : 0 ≤ t) :
    ‖σ.response K t‖ ≤ t * Real.exp (-(c * t)) * (‖K‖ * ‖σ.v‖) := by
  have hb : ∀ s ∈ uIoc (0 : ℝ) t,
      ‖σ.S (t - s) (K (σ.x s))‖ ≤ Real.exp (-(c * t)) * (‖K‖ * ‖σ.v‖) := by
    intro s hs
    rw [uIoc_of_le ht] at hs
    have h1 : ‖σ.S (t - s) (K (σ.x s))‖ ≤ Real.exp (-(c * (t - s))) * ‖K (σ.x s)‖ :=
      norm_exp_neg_le σ.L hcoer (sub_nonneg.mpr hs.2) _
    have h2 : ‖σ.x s‖ ≤ Real.exp (-(c * s)) * ‖σ.v‖ := norm_exp_neg_le σ.L hcoer hs.1.le σ.v
    have h3 : ‖K (σ.x s)‖ ≤ ‖K‖ * (Real.exp (-(c * s)) * ‖σ.v‖) :=
      (K.le_opNorm _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    calc ‖σ.S (t - s) (K (σ.x s))‖
        ≤ Real.exp (-(c * (t - s))) * (‖K‖ * (Real.exp (-(c * s)) * ‖σ.v‖)) :=
          h1.trans (mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le)
      _ = Real.exp (-(c * t)) * (‖K‖ * ‖σ.v‖) := by
          rw [show -(c * t) = -(c * (t - s)) + -(c * s) by ring, Real.exp_add]
          ring
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg ht] at h
  rw [response, norm_neg]
  calc _ ≤ _ := h
    _ = t * Real.exp (-(c * t)) * (‖K‖ * ‖σ.v‖) := by ring

omit [FiniteDimensional ℂ H] in
theorem norm_response_le_exp (hc : 0 < c)
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, σ.L y⟫_ℂ) (K : H →L[ℂ] H) {t : ℝ}
    (ht : 0 ≤ t) : ‖σ.response K t‖ ≤ 2 / c * Real.exp (-(c / 2 * t)) * (‖K‖ * ‖σ.v‖) :=
  (σ.norm_response_le hcoer K ht).trans
    (mul_le_mul_of_nonneg_right (mul_exp_neg_le_two_div_exp_half hc t) (by positivity))

omit [FiniteDimensional ℂ H] in
theorem tendsto_response (hc : 0 < c)
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, σ.L y⟫_ℂ) (K : H →L[ℂ] H) :
    Tendsto (σ.response K) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun t : ℝ => 2 / c * Real.exp (-(c / 2 * t)) * (‖K‖ * ‖σ.v‖)) atTop
      (𝓝 0) := by
    have := ((Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop
      (by positivity : (0 : ℝ) < c / 2))).const_mul (2 / c)).mul_const (‖K‖ * ‖σ.v‖)
    simpa [Function.comp_def] using this
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact σ.norm_response_le_exp hc hcoer K ht

omit [FiniteDimensional ℂ H] in
theorem norm_response_mul_le (hc : 0 < c)
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, σ.L y⟫_ℂ) (K : H →L[ℂ] H) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖σ.response K t‖ * ‖σ.x t‖ ≤ 2 / c * (‖K‖ * ‖σ.v‖ ^ 2) * Real.exp (-(c / 2 * t)) := by
  have hY := σ.norm_response_le_exp hc hcoer K ht
  have hx : ‖σ.x t‖ ≤ ‖σ.v‖ := by
    have h : ‖σ.x t‖ ≤ Real.exp (-(c * t)) * ‖σ.v‖ := norm_exp_neg_le σ.L hcoer ht σ.v
    have he : Real.exp (-(c * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    nlinarith [norm_nonneg σ.v]
  calc ‖σ.response K t‖ * ‖σ.x t‖
      ≤ (2 / c * Real.exp (-(c / 2 * t)) * (‖K‖ * ‖σ.v‖)) * ‖σ.v‖ :=
        mul_le_mul hY hx (norm_nonneg _) (by positivity)
    _ = _ := by ring

end ResponseBounds

/-! ### The Gram response -/

/-- The Gram response `Ġ_K = ∫₀^∞ (|Y_K(t)⟩⟨x(t)| + |x(t)⟩⟨Y_K(t)|) dt` `(SR.13)`. -/
def gramDot (K : H →L[ℂ] H) : H →L[ℂ] H :=
  ∫ t in Ioi (0 : ℝ), (InnerProductSpace.rankOne ℂ (σ.response K t) (σ.x t) +
    InnerProductSpace.rankOne ℂ (σ.x t) (σ.response K t))

section GramDot

variable {c : ℝ}

theorem integrableOn_gramDotIntegrand (hc : 0 < c)
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, σ.L y⟫_ℂ) (K : H →L[ℂ] H) :
    IntegrableOn (fun t => InnerProductSpace.rankOne ℂ (σ.response K t) (σ.x t) +
      InnerProductSpace.rankOne ℂ (σ.x t) (σ.response K t)) (Ioi 0) := by
  have hcont := (continuous_rankOne_path (σ.continuous_response K) σ.continuous_x).add
    (continuous_rankOne_path σ.continuous_x (σ.continuous_response K))
  refine integrableOn_Ioi_of_exp_bound hcont (δ := c / 2)
    (C := 2 * (2 / c * (‖K‖ * ‖σ.v‖ ^ 2))) (by positivity) fun t ht => ?_
  have h := σ.norm_response_mul_le hc hcoer K ht.le
  calc _ ≤ ‖InnerProductSpace.rankOne ℂ (σ.response K t) (σ.x t)‖ +
        ‖InnerProductSpace.rankOne ℂ (σ.x t) (σ.response K t)‖ := norm_add_le _ _
    _ = 2 * (‖σ.response K t‖ * ‖σ.x t‖) := by
        rw [InnerProductSpace.norm_rankOne, InnerProductSpace.norm_rankOne]
        ring
    _ ≤ 2 * (2 / c * (‖K‖ * ‖σ.v‖ ^ 2) * Real.exp (-(c / 2 * t))) := by gcongr
    _ = _ := by ring

theorem integrableOn_responsePair (hc : 0 < c)
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, σ.L y⟫_ℂ) (K : H →L[ℂ] H) (a b : H) :
    IntegrableOn (fun t => ⟪a, σ.response K t⟫_ℂ * ⟪σ.x t, b⟫_ℂ +
      ⟪a, σ.x t⟫_ℂ * ⟪σ.response K t, b⟫_ℂ) (Ioi 0) := by
  have hY := σ.continuous_response K
  have hx := σ.continuous_x
  have hcont : Continuous fun t => ⟪a, σ.response K t⟫_ℂ * ⟪σ.x t, b⟫_ℂ +
      ⟪a, σ.x t⟫_ℂ * ⟪σ.response K t, b⟫_ℂ :=
    ((continuous_const.inner hY).mul (hx.inner continuous_const)).add
      ((continuous_const.inner hx).mul (hY.inner continuous_const))
  refine integrableOn_Ioi_of_exp_bound hcont (δ := c / 2)
    (C := 2 * (‖a‖ * ‖b‖) * (2 / c * (‖K‖ * ‖σ.v‖ ^ 2))) (by positivity) fun t ht => ?_
  have h := σ.norm_response_mul_le hc hcoer K ht.le
  set Y := σ.response K t
  set z := σ.x t
  have e1 : ‖⟪a, Y⟫_ℂ * ⟪z, b⟫_ℂ‖ ≤ ‖a‖ * ‖b‖ * (‖Y‖ * ‖z‖) := by
    rw [norm_mul]
    calc _ ≤ (‖a‖ * ‖Y‖) * (‖z‖ * ‖b‖) :=
          mul_le_mul (norm_inner_le_norm _ _) (norm_inner_le_norm _ _) (norm_nonneg _)
            (by positivity)
      _ = _ := by ring
  have e2 : ‖⟪a, z⟫_ℂ * ⟪Y, b⟫_ℂ‖ ≤ ‖a‖ * ‖b‖ * (‖Y‖ * ‖z‖) := by
    rw [norm_mul]
    calc _ ≤ (‖a‖ * ‖z‖) * (‖Y‖ * ‖b‖) :=
          mul_le_mul (norm_inner_le_norm _ _) (norm_inner_le_norm _ _) (norm_nonneg _)
            (by positivity)
      _ = _ := by ring
  calc _ ≤ ‖⟪a, Y⟫_ℂ * ⟪z, b⟫_ℂ‖ + ‖⟪a, z⟫_ℂ * ⟪Y, b⟫_ℂ‖ := norm_add_le _ _
    _ ≤ 2 * (‖a‖ * ‖b‖) * (‖Y‖ * ‖z‖) := by linarith
    _ ≤ 2 * (‖a‖ * ‖b‖) * (2 / c * (‖K‖ * ‖σ.v‖ ^ 2) * Real.exp (-(c / 2 * t))) := by gcongr
    _ = _ := by ring

/-- The weak form of the Gram response. -/
theorem inner_gramDot (hc : 0 < c)
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, σ.L y⟫_ℂ) (K : H →L[ℂ] H) (a b : H) :
    ⟪a, σ.gramDot K b⟫_ℂ = ∫ t in Ioi (0 : ℝ),
      (⟪a, σ.response K t⟫_ℂ * ⟪σ.x t, b⟫_ℂ + ⟪a, σ.x t⟫_ℂ * ⟪σ.response K t, b⟫_ℂ) := by
  set Φ : (H →L[ℂ] H) →L[ℂ] ℂ := (innerSL ℂ a).comp (ContinuousLinearMap.apply ℂ H b)
  have h := Φ.integral_comp_comm (σ.integrableOn_gramDotIntegrand hc hcoer K)
  change Φ (σ.gramDot K) = _
  rw [gramDot, ← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [Φ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    innerSL_apply_apply, add_apply, InnerProductSpace.rankOne_apply, inner_add_right,
    inner_smul_right]
  ring

end GramDot

/-- **`(SR.14)`: the forced Gram identity** `L Ġ_K + Ġ_K L = -(K G + G K)`. -/
theorem lyapunov_gramDot (hK : IsSelfAdjoint K) :
    σ.L * σ.gramDot K + σ.gramDot K * σ.L = -(K * σ.gram + σ.gram * K) := by
  obtain ⟨c, hc, hcoer⟩ := σ.exists_coercive
  have hs : ∀ x y : H, ⟪σ.L x, y⟫_ℂ = ⟪x, σ.L y⟫_ℂ := fun x y =>
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp σ.isSelfAdjoint x y
  have hk : ∀ x y : H, ⟪K x, y⟫_ℂ = ⟪x, K y⟫_ℂ := fun x y =>
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hK x y
  set g : H → H → ℝ → ℂ := fun a b t =>
    ⟪a, σ.response K t⟫_ℂ * ⟪σ.x t, b⟫_ℂ + ⟪a, σ.x t⟫_ℂ * ⟪σ.response K t, b⟫_ℂ with hg
  set h : H → H → ℝ → ℂ := fun a b t => ⟪a, σ.x t⟫_ℂ * ⟪σ.x t, b⟫_ℂ with hh
  ext b
  refine ext_inner_left ℂ fun a => ?_
  have hderiv : ∀ t, HasDerivAt (g a b)
      (-(g (σ.L a) b t + g a (σ.L b) t) - (h (K a) b t + h a (K b) t)) t := by
    intro t
    have hY := σ.hasDerivAt_response K t
    have hx := σ.hasDerivAt_x t
    have h1 := ((hasDerivAt_const t a).inner ℂ hY).mul (hx.inner ℂ (hasDerivAt_const t b))
    have h2 := ((hasDerivAt_const t a).inner ℂ hx).mul (hY.inner ℂ (hasDerivAt_const t b))
    refine (h1.add h2).congr_deriv ?_
    simp only [hg, hh, inner_zero_left, inner_zero_right, zero_add, add_zero, inner_sub_right,
      inner_sub_left, inner_neg_right, inner_neg_left]
    rw [← hs a (σ.response K t), ← hs a (σ.x t), hs (σ.x t) b, hs (σ.response K t) b,
      ← hk a (σ.x t), hk (σ.x t) b]
    ring
  have hgint : ∀ a b, IntegrableOn (g a b) (Ioi 0) := fun a b =>
    σ.integrableOn_responsePair hc hcoer K a b
  have hhint : ∀ a b, IntegrableOn (h a b) (Ioi 0) := fun a b =>
    integrableOn_orbit_mul hc hcoer a σ.v σ.v b
  have hlim : Tendsto (g a b) atTop (𝓝 0) := by
    have hY := σ.tendsto_response hc hcoer K
    have hx : Tendsto σ.x atTop (𝓝 0) := tendsto_expNeg_apply hc hcoer σ.v
    have hca : Continuous fun y : H => ⟪a, y⟫_ℂ := continuous_const.inner continuous_id
    have hcb : Continuous fun y : H => ⟪y, b⟫_ℂ := continuous_id.inner continuous_const
    have := ((hca.tendsto 0 |>.comp hY).mul (hcb.tendsto 0 |>.comp hx)).add
      ((hca.tendsto 0 |>.comp hx).mul (hcb.tendsto 0 |>.comp hY))
    simpa [hg, Function.comp_def] using this
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto (f := g a b) (a := 0) (m := 0)
    (hderiv 0).continuousAt.continuousWithinAt (fun t _ => hderiv t)
    (((hgint (σ.L a) b).add (hgint a (σ.L b))).neg.sub ((hhint (K a) b).add (hhint a (K b))))
    hlim
  have e1 : ∫ t in Ioi (0 : ℝ), g (σ.L a) b t = ⟪σ.L a, σ.gramDot K b⟫_ℂ :=
    (σ.inner_gramDot hc hcoer K _ _).symm
  have e2 : ∫ t in Ioi (0 : ℝ), g a (σ.L b) t = ⟪a, σ.gramDot K (σ.L b)⟫_ℂ :=
    (σ.inner_gramDot hc hcoer K _ _).symm
  have e3 : ∫ t in Ioi (0 : ℝ), h (K a) b t = ⟪K a, σ.gram b⟫_ℂ := (σ.inner_gram _ _).symm
  have e4 : ∫ t in Ioi (0 : ℝ), h a (K b) t = ⟪a, σ.gram (K b)⟫_ℂ := (σ.inner_gram _ _).symm
  have hg0 : g a b 0 = 0 := by simp [hg, σ.response_zero]
  rw [integral_sub (f := fun x => -(g (σ.L a) b x + g a (σ.L b) x))
    (g := fun x => h (K a) b x + h a (K b) x) ((hgint (σ.L a) b).add (hgint a (σ.L b))).neg
    ((hhint (K a) b).add (hhint a (K b))), integral_neg,
    integral_add (f := fun x => g (σ.L a) b x) (g := fun x => g a (σ.L b) x)
      (hgint (σ.L a) b) (hgint a (σ.L b)),
    integral_add (f := fun x => h (K a) b x) (g := fun x => h a (K b) x)
      (hhint (K a) b) (hhint a (K b)), e1, e2, e3, e4] at hftc
  rw [add_apply, mul_apply_eq_comp, mul_apply_eq_comp, inner_add_right, ← hs a, neg_apply,
    add_apply, mul_apply_eq_comp, mul_apply_eq_comp, inner_neg_right, inner_add_right, ← hk a]
  linear_combination -hftc + hg0

/-- **`(SR.13)`: the Gram response is the derivative of the perturbed Gramian**,
`d/dε G_{ε,K} |₀ = Ġ_K`. -/
theorem hasDerivAt_perturbedGram (hK : IsSelfAdjoint K) :
    HasDerivAt (σ.perturbedGram K) (σ.gramDot K) 0 := by
  obtain ⟨c, hc, hcoer⟩ := σ.exists_coercive
  obtain ⟨M, hM0, hM⟩ := exists_lyapunov_inverse_bound hc hcoer
  have hS := σ.lyapunov_gramDot hK
  set C₀ : ℝ := M * (2 * ‖K‖) * (M * (2 * ‖K‖ * (‖σ.v‖ ^ 2 / c)))
  have hbound : ∀ ε : ℝ, ε ≠ 0 → |ε| * ‖K‖ ≤ c / 2 →
      ‖ε⁻¹ • (σ.perturbedGram K ε - σ.gram) - σ.gramDot K‖ ≤ C₀ * |ε| := by
    intro ε hε0 hε
    have hR := σ.lyapunov_perturbedGram_sub hK hc hcoer hε
    have hGε := σ.norm_perturbedGram_le hc hcoer hε
    set Gε := σ.perturbedGram K ε
    set G := σ.gram
    set Ġ := σ.gramDot K
    have hsum : ∀ X : H →L[ℂ] H, ‖K * X + X * K‖ ≤ 2 * ‖K‖ * ‖X‖ := fun X =>
      ((norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))).trans_eq
        (by ring)
    have hdiff : ‖Gε - G‖ ≤ M * (|ε| * (2 * ‖K‖ * (‖σ.v‖ ^ 2 / c))) := by
      refine (hM _).trans (mul_le_mul_of_nonneg_left ?_ hM0)
      rw [hR, norm_neg, norm_smul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ((hsum Gε).trans ?_) (abs_nonneg _)
      gcongr
    have hD : σ.L * (ε⁻¹ • (Gε - G) - Ġ) + (ε⁻¹ • (Gε - G) - Ġ) * σ.L =
        -(K * (Gε - G) + (Gε - G) * K) := by
      have e1 : σ.L * (ε⁻¹ • (Gε - G) - Ġ) + (ε⁻¹ • (Gε - G) - Ġ) * σ.L =
          ε⁻¹ • (σ.L * (Gε - G) + (Gε - G) * σ.L) - (σ.L * Ġ + Ġ * σ.L) := by
        rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_add]
        abel
      rw [e1, hR, hS, smul_neg, smul_smul, inv_mul_cancel₀ hε0, one_smul]
      noncomm_ring
    calc ‖ε⁻¹ • (Gε - G) - Ġ‖ ≤ M * ‖K * (Gε - G) + (Gε - G) * K‖ := by
          have h := hM (ε⁻¹ • (Gε - G) - Ġ)
          rwa [hD, norm_neg] at h
      _ ≤ M * (2 * ‖K‖ * ‖Gε - G‖) := mul_le_mul_of_nonneg_left (hsum _) hM0
      _ ≤ M * (2 * ‖K‖ * (M * (|ε| * (2 * ‖K‖ * (‖σ.v‖ ^ 2 / c))))) := by gcongr
      _ = C₀ * |ε| := by ring
  rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun ε : ℝ => C₀ * |ε|) (𝓝[≠] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => C₀ * |ε|) (𝓝 0) (𝓝 (C₀ * |0|)) :=
      (continuous_const.mul continuous_abs).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [nhdsWithin_le_nhds (eventually_small K hc), self_mem_nhdsWithin]
    with ε hε hε0
  rw [zero_add, σ.perturbedGram_zero]
  exact hbound ε hε0 hε

/-! ### Reconstruction from the Gram response -/

/-- `(SR.15)`: the intervention solves the positive Sylvester equation
`K G + G K = B` with `B = -(L Ġ_K + Ġ_K L)`. -/
theorem gram_sylvester_gramDot (hK : IsSelfAdjoint K) :
    K * σ.gram + σ.gram * K = -(σ.L * σ.gramDot K + σ.gramDot K * σ.L) := by
  rw [σ.lyapunov_gramDot hK, neg_neg]

/-- `(SR.15)`: the measured Gram response determines the intervention uniquely. -/
theorem eq_of_gram_sylvester (hK : IsSelfAdjoint K) {X : H →L[ℂ] H}
    (hX : X * σ.gram + σ.gram * X = -(σ.L * σ.gramDot K + σ.gramDot K * σ.L)) : X = K := by
  obtain ⟨Y, -, huniq⟩ := σ.existsUnique_gram_sylvester
    (-(σ.L * σ.gramDot K + σ.gramDot K * σ.L))
  exact (huniq X hX).trans (huniq K (σ.gram_sylvester_gramDot hK)).symm

/-- **Gram reconstruction**: self-adjoint interventions with equal Gram responses are equal. -/
theorem gramDot_injective {K₁ K₂ : H →L[ℂ] H} (h₁ : IsSelfAdjoint K₁) (h₂ : IsSelfAdjoint K₂)
    (h : σ.gramDot K₁ = σ.gramDot K₂) : K₁ = K₂ :=
  σ.eq_of_gram_sylvester h₂ (h ▸ σ.gram_sylvester_gramDot h₁)

/-! ### Inverse-cost and determinant responses -/

/-- **`(SR.16)`: the inverse-cost response** `d/dε G_{ε,K}⁻¹ |₀ = -C Ġ_K C`, `C = G⁻¹`. -/
theorem hasDerivAt_inverseCost (hK : IsSelfAdjoint K) :
    HasDerivAt (fun ε => Ring.inverse (σ.perturbedGram K ε))
      (-(Ring.inverse σ.gram * σ.gramDot K * Ring.inverse σ.gram)) 0 := by
  obtain ⟨u, hu⟩ := σ.isUnit_gram
  have hinv : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (H →L[ℂ] H) ↑u⁻¹ ↑u⁻¹) (σ.perturbedGram K 0) := by
    rw [σ.perturbedGram_zero, ← hu]
    exact hasFDerivAt_ringInverse u
  have h := hinv.comp_hasDerivAt (0 : ℝ) (σ.hasDerivAt_perturbedGram hK)
  refine h.congr_deriv ?_
  rw [neg_apply, ContinuousLinearMap.mulLeftRight_apply, ← hu,
    Ring.inverse_unit]

/-- **`(SR.17)`: the determinant response** `d/dε log det G_{ε,K} |₀ = tr (C Ġ_K)`. -/
theorem hasDerivAt_logDet (hK : IsSelfAdjoint K) :
    HasDerivAt (fun ε => Complex.log (LinearMap.det (σ.perturbedGram K ε : H →ₗ[ℂ] H)))
      (LinearMap.trace ℂ H (Ring.inverse σ.gram * σ.gramDot K : H →L[ℂ] H)) 0 := by
  have hdet := hasDerivAt_det_operator (σ.hasDerivAt_perturbedGram hK)
    (by rw [σ.perturbedGram_zero]; exact σ.isUnit_gram)
  obtain ⟨r, hr, hdr⟩ := σ.exists_det_gram_eq_pos
  have hslit : LinearMap.det (σ.perturbedGram K 0 : H →ₗ[ℂ] H) ∈ Complex.slitPlane := by
    rw [σ.perturbedGram_zero, hdr]
    exact Complex.ofReal_mem_slitPlane.mpr hr
  refine (hdet.clog_real hslit).congr_deriv ?_
  rw [σ.perturbedGram_zero, hdr]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')

end CyclicSource

end GaloisForLFunctions.HTGeometry
