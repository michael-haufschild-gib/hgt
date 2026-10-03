import GaloisForLFunctions.RHTower.PhaseQuotientStationaryCompletionHomotopy

/-!
# Toeplitz phase form and the weak Haar phase average

The stationary Toeplitz lift `R = H† M_c H` of a contractive common-radial phase field is the
bounded operator of the phase form

`q(x, y) = ∫ ⟪F_x(z), c(z) F_y(z)⟫ dm(z)`,   `F_x(z) = ∑ z^n x_n`,

and it is the unique bounded operator whose history blocks are the Fourier coefficients
`E_n† R E_m = C_{m-n}` of the source density `c`.

The history gauge `(Γ_z x)_n = z^n x_n` is strongly continuous, so for every pair of history
vectors the phase function `z ↦ ⟪x, Γ_z† R Γ_z y⟫` is continuous and bounded.  Its Haar average
equals `⟪x, (I ⊗ C_0) y⟫` for all `x, y`: the weak phase average of the open Toeplitz history is
the diagonal constant-block lift of the zero Fourier coefficient.  The general mechanism is that a
bounded weakly integrable operator family has its weak integral determined by the integrals of its
matrix coefficients on a Hilbert basis.
-/

open Complex Set MeasureTheory Filter Topology
open scoped BigOperators InnerProductSpace ComplexOrder ENNReal

namespace RHTower

noncomputable section

open ContinuousLinearMap
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-! ## Weak integrals determined on a Hilbert basis -/

/-- A bounded family of functionals with integrable evaluations integrates to a bounded
functional; it is therefore determined by its integrals on a Hilbert basis. -/
theorem integral_apply_eq_of_hilbertBasis
    {ι Z E : Type*} [MeasurableSpace Z] {μ : Measure Z} [IsFiniteMeasure μ]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : HilbertBasis ι ℂ E) (f : Z → E →L[ℂ] ℂ) {K : ℝ}
    (hK : ∀ z, ‖f z‖ ≤ K) (hint : ∀ y, Integrable (fun z => f z y) μ)
    (g : E →L[ℂ] ℂ) (hb : ∀ j, ∫ z, f z (b j) ∂μ = g (b j)) (y : E) :
    ∫ z, f z y ∂μ = g y := by
  let φ : E →L[ℂ] ℂ := LinearMap.mkContinuous
    { toFun := fun y => ∫ z, f z y ∂μ
      map_add' := fun y y' => by
        simp only [map_add]
        exact integral_add (hint y) (hint y')
      map_smul' := fun c y => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
    (K * μ.real Set.univ) (fun y => by
      change ‖∫ z, f z y ∂μ‖ ≤ K * μ.real Set.univ * ‖y‖
      have h := norm_integral_le_of_norm_le_const (μ := μ) (C := K * ‖y‖)
        (f := fun z => f z y) (Eventually.of_forall fun z =>
          ((f z).le_opNorm y).trans (mul_le_mul_of_nonneg_right (hK z) (norm_nonneg y)))
      calc ‖∫ z, f z y ∂μ‖ ≤ K * ‖y‖ * μ.real Set.univ := h
        _ = K * μ.real Set.univ * ‖y‖ := by ring)
  have hφ : φ = g :=
    ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.2 b.dense_span)
      (by rintro _ ⟨j, rfl⟩; exact hb j)
  exact DFunLike.congr_fun hφ y

/-- Weak integrals of bounded operator families are determined on a Hilbert basis: if the matrix
coefficients `⟪b_i, T(z) b_j⟫` integrate to those of `B`, then `∫ ⟪x, T(z) y⟫ = ⟪x, B y⟫` for all
vectors `x, y`. -/
theorem integral_inner_eq_of_hilbertBasis
    {ι Z E : Type*} [MeasurableSpace Z] {μ : Measure Z} [IsFiniteMeasure μ]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : HilbertBasis ι ℂ E) (T : Z → E →L[ℂ] E) {C : ℝ}
    (hC : ∀ z, ‖T z‖ ≤ C)
    (hint : ∀ x y, Integrable (fun z => inner ℂ x (T z y)) μ)
    (B : E →L[ℂ] E)
    (hb : ∀ i j, ∫ z, inner ℂ (b i) (T z (b j)) ∂μ = inner ℂ (b i) (B (b j)))
    (x y : E) :
    ∫ z, inner ℂ x (T z y) ∂μ = inner ℂ x (B y) := by
  have hcol : ∀ j u, ∫ z, inner ℂ u (T z (b j)) ∂μ = inner ℂ u (B (b j)) := by
    intro j u
    have hconj : ∀ v, ∫ z, inner ℂ (T z (b j)) v ∂μ = inner ℂ (B (b j)) v := by
      intro v
      refine integral_apply_eq_of_hilbertBasis b (fun z => innerSL ℂ (T z (b j)))
        (K := C * ‖b j‖) ?_ ?_ (innerSL ℂ (B (b j))) ?_ v
      · intro z
        rw [innerSL_apply_norm]
        exact ((T z).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hC z) (norm_nonneg _))
      · intro w
        simp only [innerSL_apply_apply]
        refine (hint w (b j)).congr'
          (Complex.continuous_conj.comp_aestronglyMeasurable (hint w (b j)).1
            |>.congr (Eventually.of_forall fun z => ?_)) (Eventually.of_forall fun z => ?_)
        · exact inner_conj_symm _ _
        · rw [← inner_conj_symm (T z (b j)) w, RCLike.norm_conj]
      · intro i
        simp only [innerSL_apply_apply]
        rw [← inner_conj_symm (B (b j)), ← hb i j, ← integral_conj]
        exact integral_congr_ae (Eventually.of_forall fun z => (inner_conj_symm _ _).symm)
    rw [← inner_conj_symm u, ← hconj u, ← integral_conj]
    exact integral_congr_ae (Eventually.of_forall fun z => (inner_conj_symm _ _).symm)
  refine integral_apply_eq_of_hilbertBasis b (fun z => (innerSL ℂ x).comp (T z))
    (K := ‖x‖ * C) ?_ ?_ ((innerSL ℂ x).comp B) ?_ y
  · intro z
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [innerSL_apply_norm]
    exact mul_le_mul_of_nonneg_left (hC z) (norm_nonneg x)
  · intro w
    simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] using hint x w
  · intro j
    simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] using hcol j x

/-- A uniformly bounded operator family that is continuous on a Hilbert basis is strongly
continuous: the vectors on which it is continuous form a closed subspace containing the basis. -/
theorem continuous_apply_of_hilbertBasis
    {ι Z E F : Type*} [TopologicalSpace Z]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (b : HilbertBasis ι ℂ E) (T : Z → E →L[ℂ] F) {C : ℝ}
    (hC : ∀ z, ‖T z‖ ≤ C) (hb : ∀ i, Continuous fun z => T z (b i)) (x : E) :
    Continuous fun z => T z x := by
  let S : Submodule ℂ E :=
    { carrier := {x | Continuous fun z => T z x}
      add_mem' := fun {x y} hx hy => by
        have hx' : Continuous fun z => T z x := hx
        have hy' : Continuous fun z => T z y := hy
        change Continuous fun z => T z (x + y)
        simp only [map_add]
        exact hx'.add hy'
      zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]; exact continuous_const
      smul_mem' := fun c x hx => by
        have hx' : Continuous fun z => T z x := hx
        change Continuous fun z => T z (c • x)
        simp only [map_smul]
        exact hx'.const_smul c }
  have hC' : ∀ z, ‖T z‖ ≤ |C| + 1 := fun z => (hC z).trans (by linarith [le_abs_self C])
  have hpos : 0 < |C| + 1 := by positivity
  have hclosed : IsClosed (S : Set E) := by
    refine closure_subset_iff_isClosed.1 fun x hx => ?_
    change Continuous fun z => T z x
    refine continuous_iff_continuousAt.2 fun z₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx (ε / (3 * (|C| + 1))) (by positivity)
    have hyc : Continuous fun z => T z y := hy
    filter_upwards [Metric.tendsto_nhds.1 (hyc.tendsto z₀) (ε / 3) (by positivity)] with z hz
    have hxy' : ‖x - y‖ < ε / (3 * (|C| + 1)) := by rwa [← dist_eq_norm]
    have h1 : ‖T z (x - y)‖ < ε / 3 := by
      calc ‖T z (x - y)‖ ≤ (|C| + 1) * ‖x - y‖ :=
            ((T z).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC' z) (norm_nonneg _))
        _ < (|C| + 1) * (ε / (3 * (|C| + 1))) := mul_lt_mul_of_pos_left hxy' hpos
        _ = ε / 3 := by field_simp
    have h2 : ‖T z₀ (x - y)‖ < ε / 3 := by
      calc ‖T z₀ (x - y)‖ ≤ (|C| + 1) * ‖x - y‖ :=
            ((T z₀).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC' z₀) (norm_nonneg _))
        _ < (|C| + 1) * (ε / (3 * (|C| + 1))) := mul_lt_mul_of_pos_left hxy' hpos
        _ = ε / 3 := by field_simp
    rw [dist_eq_norm] at hz ⊢
    have hsplit : T z x - T z₀ x = T z (x - y) + (T z y - T z₀ y) - T z₀ (x - y) := by
      simp only [map_sub]; abel
    rw [hsplit]
    calc ‖T z (x - y) + (T z y - T z₀ y) - T z₀ (x - y)‖
        ≤ ‖T z (x - y)‖ + ‖T z y - T z₀ y‖ + ‖T z₀ (x - y)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by gcongr
      _ = ε := by ring
  have hspan : Submodule.span ℂ (Set.range b) ≤ S :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb i)
  have htop : (⊤ : Submodule ℂ E) ≤ S := by
    rw [← b.dense_span]
    exact Submodule.topologicalClosure_minimal _ hspan hclosed
  exact htop (Submodule.mem_top (x := x))

/-! ## The phase form of the Toeplitz lift -/

/-- The Toeplitz lift is the operator of the phase form: `⟪x, R y⟫ = ∫ ⟪(Hx)(z), c(z)(Hy)(z)⟫`. -/
theorem inner_commonRadialPhaseToeplitzLift
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (x y : PrimeHodgeHistoryHilbert) :
    inner ℂ x (commonRadialPhaseToeplitzLift a V y) =
      ∫ z, inner ℂ
        ((commonRadialHardySynthesis x : CommonRadialPhaseBoundary) z)
        (commonRadialPhaseSourceDensity a V z
          ((commonRadialHardySynthesis y : CommonRadialPhaseBoundary) z)) ∂unitCircleHaar := by
  change inner ℂ x (ContinuousLinearMap.adjoint commonRadialHardySynthesis
      (commonRadialPhaseMultiplication a V (commonRadialHardySynthesis y))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [commonRadialPhaseMultiplication_coeFn a V
    (commonRadialHardySynthesis y)] with z hz
  rw [hz]

/-- Hardy synthesis of a finitely supported history vector is the analytic polynomial
`F_x(z) = ∑ z^n x_{n,p} e_p`. -/
theorem commonRadialHardySynthesis_finsetSum_coeFn
    (s : Finset PrimeHodgeHistoryIndex) (c : PrimeHodgeHistoryIndex → ℂ) :
    ((commonRadialHardySynthesis
        (∑ i ∈ s, c i • HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex i) :
          CommonRadialPhaseBoundary) : CommonRadialPhase → CommonRadialPrimeSpace)
      =ᵐ[unitCircleHaar] fun z =>
        ∑ i ∈ s, (c i * fourier (i.1 : ℤ) z) • HilbertSchmidt.lpBasis Nat.Primes i.2 := by
  rw [map_sum]
  simp_rw [map_smul, commonRadialHardySynthesis_basis]
  have hsmul : ∀ i : PrimeHodgeHistoryIndex,
      ((c i • commonRadialHardyMode i : CommonRadialPhaseBoundary) :
          CommonRadialPhase → CommonRadialPrimeSpace) =ᵐ[unitCircleHaar]
        fun z => (c i * fourier (i.1 : ℤ) z) • HilbertSchmidt.lpBasis Nat.Primes i.2 := by
    rintro ⟨n, p⟩
    filter_upwards [Lp.coeFn_smul (c (n, p)) (commonRadialHardyMode (n, p)),
      commonRadialHardyMode_coeFn n p] with z h1 h2
    rw [h1, Pi.smul_apply, h2, smul_smul]
  filter_upwards [Lp.coeFn_finsetSum s (fun i => c i • commonRadialHardyMode i),
    ae_all_iff.2 hsmul] with z h1 h2
  rw [h1, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => h2 i

/-- On finitely supported history vectors the Toeplitz lift is the phase form
`q(x, y) = ∫ ⟪F_x(z), c(z) F_y(z)⟫ dm(z)` with `F_x(z) = ∑ z^n x_n`. -/
theorem inner_commonRadialPhaseToeplitzLift_finsetSum
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (s t : Finset PrimeHodgeHistoryIndex) (x y : PrimeHodgeHistoryIndex → ℂ) :
    inner ℂ (∑ i ∈ s, x i • HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex i)
        (commonRadialPhaseToeplitzLift a V
          (∑ j ∈ t, y j • HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex j)) =
      ∫ z, inner ℂ
        (∑ i ∈ s, (x i * fourier (i.1 : ℤ) z) • HilbertSchmidt.lpBasis Nat.Primes i.2)
        (commonRadialPhaseSourceDensity a V z
          (∑ j ∈ t, (y j * fourier (j.1 : ℤ) z) • HilbertSchmidt.lpBasis Nat.Primes j.2))
        ∂unitCircleHaar := by
  rw [inner_commonRadialPhaseToeplitzLift]
  apply integral_congr_ae
  filter_upwards [commonRadialHardySynthesis_finsetSum_coeFn s x,
    commonRadialHardySynthesis_finsetSum_coeFn t y] with z h1 h2
  rw [h1, h2]

/-- Uniqueness of the stationary lift: a bounded history operator with Fourier blocks
`E_n† R' E_m = C_{m-n}` is the Toeplitz lift. -/
theorem eq_commonRadialPhaseToeplitzLift_of_blocks
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (hR : ∀ (n m : ℕ) (p q : Nat.Primes),
      inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
          (R (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (m, q))) =
        inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
          (commonRadialPhaseFourierCoefficient a V ((m : ℤ) - (n : ℤ))
            (HilbertSchmidt.lpBasis Nat.Primes q))) :
    R = commonRadialPhaseToeplitzLift a V := by
  apply continuousLinearMap_eq_of_eq_on_hilbertBasis
    (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex)
  rintro ⟨m, q⟩
  apply (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex).repr.injective
  ext j
  rcases j with ⟨n, p⟩
  rw [(HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex).repr_apply_apply,
    (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex).repr_apply_apply, hR,
    inner_basis_commonRadialPhaseToeplitzLift_basis]

/-! ## Strong continuity of the history gauge and the weak phase average -/

theorem norm_commonRadialHistoryGaugeCLM_le (z : CommonRadialPhase) :
    ‖commonRadialHistoryGaugeCLM z‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _

theorem norm_commonRadialHistoryGaugeCLM_apply
    (z : CommonRadialPhase) (x : PrimeHodgeHistoryHilbert) :
    ‖commonRadialHistoryGaugeCLM z x‖ = ‖x‖ :=
  (commonRadialHistoryGauge z).norm_map x

/-- The history gauge `(Γ_z x)_n = z^n x_n` is strongly continuous in the phase. -/
theorem continuous_commonRadialHistoryGaugeCLM_apply (x : PrimeHodgeHistoryHilbert) :
    Continuous fun z => commonRadialHistoryGaugeCLM z x := by
  refine continuous_apply_of_hilbertBasis (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex)
    commonRadialHistoryGaugeCLM norm_commonRadialHistoryGaugeCLM_le ?_ x
  rintro ⟨n, p⟩
  simp_rw [commonRadialHistoryGaugeCLM_basis]
  exact (fourier (n : ℤ)).continuous.smul continuous_const

theorem norm_commonRadialHistoryGaugeConjugate_le
    (z : CommonRadialPhase)
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert) :
    ‖commonRadialHistoryGaugeConjugate z R‖ ≤ ‖R‖ := by
  have hΓ := norm_commonRadialHistoryGaugeCLM_le z
  have hΓ' : ‖ContinuousLinearMap.adjoint (commonRadialHistoryGaugeCLM z)‖ ≤ 1 := by
    rw [norm_adjoint_eq_norm]; exact hΓ
  calc ‖commonRadialHistoryGaugeConjugate z R‖
      ≤ ‖ContinuousLinearMap.adjoint (commonRadialHistoryGaugeCLM z)‖ *
          (‖R‖ * ‖commonRadialHistoryGaugeCLM z‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖R‖ * 1) := by gcongr
    _ = ‖R‖ := by ring

/-- Every matrix coefficient `z ↦ ⟪x, Γ_z† R Γ_z y⟫` is continuous in the phase. -/
theorem continuous_inner_commonRadialHistoryGaugeConjugate
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (x y : PrimeHodgeHistoryHilbert) :
    Continuous fun z => inner ℂ x (commonRadialHistoryGaugeConjugate z R y) := by
  have h : (fun z => inner ℂ x (commonRadialHistoryGaugeConjugate z R y)) =
      fun z => inner ℂ (commonRadialHistoryGaugeCLM z x)
        (R (commonRadialHistoryGaugeCLM z y)) := by
    funext z
    change inner ℂ x (ContinuousLinearMap.adjoint (commonRadialHistoryGaugeCLM z)
      (R (commonRadialHistoryGaugeCLM z y))) = _
    rw [ContinuousLinearMap.adjoint_inner_right]
  rw [h]
  exact (continuous_commonRadialHistoryGaugeCLM_apply x).inner
    (R.continuous.comp (continuous_commonRadialHistoryGaugeCLM_apply y))

/-- Every matrix coefficient of the gauge conjugate is Haar integrable. -/
theorem integrable_inner_commonRadialHistoryGaugeConjugate
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (x y : PrimeHodgeHistoryHilbert) :
    Integrable (fun z => inner ℂ x (commonRadialHistoryGaugeConjugate z R y))
      unitCircleHaar := by
  refine Integrable.of_bound
    (continuous_inner_commonRadialHistoryGaugeConjugate R x y).aestronglyMeasurable
    (‖x‖ * (‖R‖ * ‖y‖)) (Eventually.of_forall fun z => ?_)
  refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg x))
  exact ((commonRadialHistoryGaugeConjugate z R).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right (norm_commonRadialHistoryGaugeConjugate_le z R) (norm_nonneg y))

/-- Weak Haar phase average: for all history vectors `x, y`,
`∫ ⟪x, Γ_z† R Γ_z y⟫ dm(z) = ⟪x, (I ⊗ C_0) y⟫`. -/
theorem integral_inner_commonRadialHistoryGaugeConjugate_eq_quotient
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (x y : PrimeHodgeHistoryHilbert) :
    ∫ z, inner ℂ x (commonRadialHistoryGaugeConjugate z
        (commonRadialPhaseToeplitzLift a V) y) ∂unitCircleHaar =
      inner ℂ x (commonRadialPhaseQuotient a V y) := by
  refine integral_inner_eq_of_hilbertBasis (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex)
    (fun z => commonRadialHistoryGaugeConjugate z (commonRadialPhaseToeplitzLift a V))
    (fun z => norm_commonRadialHistoryGaugeConjugate_le z _)
    (integrable_inner_commonRadialHistoryGaugeConjugate _) _ ?_ x y
  rintro ⟨n, p⟩ ⟨m, q⟩
  exact integral_inner_basis_commonRadialHistoryGaugeConjugate_eq_quotient a V n m p q

/-- The weak phase average is a well-defined bounded operator: any bounded operator whose matrix
coefficients are the Haar averages of those of `Γ_z† R Γ_z` is `I ⊗ C_0`. -/
theorem eq_commonRadialPhaseQuotient_of_weakAverage
    (a : {d : ℝ // 0 < d}) (V : CommonRadialPhaseContractionField)
    (B : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (hB : ∀ x y, inner ℂ x (B y) = ∫ z, inner ℂ x (commonRadialHistoryGaugeConjugate z
        (commonRadialPhaseToeplitzLift a V) y) ∂unitCircleHaar) :
    B = commonRadialPhaseQuotient a V := by
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [hB, integral_inner_commonRadialHistoryGaugeConjugate_eq_quotient]

end
end RHTower
