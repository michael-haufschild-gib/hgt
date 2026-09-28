import GaloisForLFunctions.HTGeometry.BlockDiagonalSingularValues
import GaloisForLFunctions.HTGeometry.WeightedOrbitInductionGap

/-!
# Weighted orbit induction: the Schatten threshold and the weighted Gram

The singular values of the weighted induction `Ind_a(D) = ⊕ aᵢ Vᵢ D Uᵢ⁻¹` are the multiset union
of the rescaled singular values `|aᵢ| sₙ(D)`.  Consequently, for every exponent `p > 0` and a
nonzero `D` in the Schatten class `𝒮_p`,

* `memRectSchattenClass_weightedInduction_iff` `(WOI.8)` — `Ind_a(D) ∈ 𝒮_p` exactly when
  `a ∈ ℓ^p`;
* `tsum_rpow_rectApproxNumber_weightedInduction` `(WOI.9)` —
  `‖Ind_a(D)‖_{𝒮_p}^p = (∑ |aᵢ|^p) ‖D‖_{𝒮_p}^p`, and for `p = 1` the trace norm is
  `(∑ |aᵢ|) ‖D‖₁`.

The compactness threshold `(WOI.6)` is restated as the `c₀` condition
`aᵢ → 0` along the cofinite filter, and the positive Gram operator `(WOI.10)` inherits the same
compactness wall and has the `ℓ²` trace-class wall when `D` is Hilbert--Schmidt.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter RHTower MeasureTheory
open scoped ENNReal Topology InnerProductSpace

noncomputable section

/-! ## Summability through extended sums -/

theorem summable_iff_tsum_ofReal_ne_top {κ : Type*} {f : κ → ℝ} (hf : ∀ i, 0 ≤ f i) :
    Summable f ↔ ∑' i, ENNReal.ofReal (f i) ≠ ⊤ := by
  have hcoe : ∀ i, ((f i).toNNReal : ℝ) = f i := fun i => Real.coe_toNNReal _ (hf i)
  change Summable f ↔ ∑' i, ((f i).toNNReal : ℝ≥0∞) ≠ ⊤
  rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
  simp_rw [hcoe]

theorem tsum_toReal_ofReal_eq {κ : Type*} {f : κ → ℝ} (hf : ∀ i, 0 ≤ f i) :
    (∑' i, ENNReal.ofReal (f i)).toReal = ∑' i, f i := by
  rw [ENNReal.tsum_toReal_eq fun i => ENNReal.ofReal_ne_top]
  exact tsum_congr fun i => ENNReal.toReal_ofReal (hf i)

/-! ## The `c₀` form of the compactness threshold -/

section CZero

variable {I : Type} [Nonempty I] [DecidableEq I]

/-- The tail supremum vanishes exactly when the amplitudes tend to zero along the cofinite
filter, i.e. `a ∈ c₀(I)`. -/
theorem tailSup_eq_zero_iff_tendsto {a : I → ℂ} (hbdd : BddAbove (Set.range fun i => ‖a i‖)) :
    tailSup a = 0 ↔ Tendsto a cofinite (𝓝 0) := by
  rw [tailSup_eq_zero_iff hbdd, Metric.tendsto_nhds]
  refine forall_congr' fun ε => forall_congr' fun _ => ?_
  rw [Filter.eventually_cofinite]
  simp only [dist_zero_right, not_lt]

theorem tailSup_normSq_eq_zero_iff {a : I → ℂ} (hbdd : BddAbove (Set.range fun i => ‖a i‖)) :
    tailSup (fun i => ((‖a i‖ ^ 2 : ℝ) : ℂ)) = 0 ↔ tailSup a = 0 := by
  have hnorm : ∀ i, ‖((‖a i‖ ^ 2 : ℝ) : ℂ)‖ = ‖a i‖ ^ 2 := fun i => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [tailSup_eq_zero_iff_tendsto (bddAbove_normSq_amp hbdd), tailSup_eq_zero_iff_tendsto hbdd,
    tendsto_zero_iff_norm_tendsto_zero (f := fun i => ((‖a i‖ ^ 2 : ℝ) : ℂ)),
    tendsto_zero_iff_norm_tendsto_zero (f := a)]
  simp_rw [hnorm]
  constructor
  · intro h
    have := (Real.continuous_sqrt.tendsto 0).comp h
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  · intro h
    simpa using h.pow 2

end CZero

/-! ## The Schatten threshold -/

section Schatten

variable {I : Type} [Nonempty I] {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [Nonempty I] [CompleteSpace H] [CompleteSpace K] in
/-- The approximation numbers of one transported block are the rescaled local ones. -/
theorem rectApproxNumber_weightedBlock (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (i : I) (n : ℕ) :
    rectApproxNumber (weightedBlock a D U V i) n = ‖a i‖ * rectApproxNumber D n := by
  rw [weightedBlock, rectApproxNumber_smul_eq, orbitBlock, rectApproxNumber_unitary_conj]

omit [Nonempty I] [CompleteSpace H] [CompleteSpace K] in
theorem isCompactOperator_weightedBlock (a : I → ℂ) {D : H →L[ℂ] K} (hD : IsCompactOperator D)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K)) (i : I) :
    IsCompactOperator (weightedBlock a D U V i) := by
  have h : IsCompactOperator (orbitBlock D U V i) := by
    rw [orbitBlock]
    exact (hD.comp_clm ((U i).symm.toLinearIsometry.toContinuousLinearMap)).clm_comp
      ((V i).toLinearIsometry.toContinuousLinearMap)
  exact h.smul (a i)

/-- **Theorem 4.1, energy form.**  For a compact local operator and every exponent `p > 0`, the
`p`-energy of the singular values of the weighted induction factors as the `ℓ^p` energy of the
amplitudes times the `p`-energy of the local singular values, in `ℝ≥0∞`. -/
theorem tsum_ofReal_rpow_rectApproxNumber_weightedInduction [Countable I] (a : I → ℂ)
    (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (hD : IsCompactOperator D) {p : ℝ}
    (hp : 0 < p) :
    ∑' n, ENNReal.ofReal (rectApproxNumber (weightedInduction a D U V hbdd) n ^ p)
      = (∑' i, ENNReal.ofReal (‖a i‖ ^ p))
          * ∑' n, ENNReal.ofReal (rectApproxNumber D n ^ p) := by
  have h := tsum_ofReal_rpow_rectApproxNumber_rectangularBlockOperator
    (E := fun _ : I => H) (F := fun _ : I => K) (fun i => weightedBlock a D U V i)
    (mul_nonneg (ampSup_nonneg hbdd) (norm_nonneg D))
    (fun i => by
      rw [norm_weightedBlock]
      exact mul_le_mul_of_nonneg_right (le_ampSup hbdd i) (norm_nonneg D))
    (fun i => isCompactOperator_weightedBlock a hD U V i) hp
  refine h.trans ?_
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun i => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [rectApproxNumber_weightedBlock, Real.mul_rpow (norm_nonneg _) (rectApproxNumber_nonneg _ _),
    ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]

omit [Nonempty I] [CompleteSpace H] [CompleteSpace K] in
theorem tsum_ofReal_rpow_rectApproxNumber_pos {D : H →L[ℂ] K} (hD0 : D ≠ 0) {p : ℝ} :
    0 < ∑' n, ENNReal.ofReal (rectApproxNumber D n ^ p) := by
  have h0 : 0 < ENNReal.ofReal (rectApproxNumber D 0 ^ p) := by
    rw [ENNReal.ofReal_pos, rectApproxNumber_zero_eq_norm]
    exact Real.rpow_pos_of_pos (norm_pos_iff.mpr hD0) p
  exact lt_of_lt_of_le h0 (ENNReal.le_tsum 0)

/-- **Theorem 4.1, `(WOI.8)`.**  For a nonzero `D ∈ 𝒮_p` with `p > 0`, the weighted induction is
in `𝒮_p` exactly when the amplitudes are `p`-summable. -/
theorem memRectSchattenClass_weightedInduction_iff [Countable I] (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    {p : ℝ} (hp : 0 < p) (hDS : MemRectSchattenClass p D) (hD0 : D ≠ 0) :
    MemRectSchattenClass p (weightedInduction a D U V hbdd)
      ↔ Summable fun i => ‖a i‖ ^ p := by
  have hD : IsCompactOperator D := isCompactOperator_of_memRectSchattenClass hp hDS
  have hB : ∑' n, ENNReal.ofReal (rectApproxNumber D n ^ p) ≠ ⊤ :=
    (summable_iff_tsum_ofReal_ne_top fun n => Real.rpow_nonneg (rectApproxNumber_nonneg D n) p).mp
      hDS
  have hB0 := (tsum_ofReal_rpow_rectApproxNumber_pos hD0 (p := p)).ne'
  rw [MemRectSchattenClass,
    summable_iff_tsum_ofReal_ne_top fun n => Real.rpow_nonneg (rectApproxNumber_nonneg _ n) p,
    tsum_ofReal_rpow_rectApproxNumber_weightedInduction a D U V hbdd hD hp,
    summable_iff_tsum_ofReal_ne_top fun i => Real.rpow_nonneg (norm_nonneg _) p]
  constructor
  · intro h hA
    exact h (by rw [hA, ENNReal.top_mul hB0])
  · intro hA
    exact ENNReal.mul_ne_top hA hB

/-- `(WOI.8)` in `ℓ^p` form. -/
theorem memRectSchattenClass_weightedInduction_iff_memℓp [Countable I] (a : I → ℂ)
    (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) {p : ℝ} (hp : 0 < p)
    (hDS : MemRectSchattenClass p D) (hD0 : D ≠ 0) :
    MemRectSchattenClass p (weightedInduction a D U V hbdd) ↔ Memℓp a (ENNReal.ofReal p) := by
  rw [memRectSchattenClass_weightedInduction_iff a D U V hbdd hp hDS hD0,
    memℓp_gen_iff (by rw [ENNReal.toReal_ofReal hp.le]; exact hp), ENNReal.toReal_ofReal hp.le]

/-- **Theorem 4.1, `(WOI.9)`.**  For `D ∈ 𝒮_p` with `p > 0`,
`∑ₙ sₙ(Ind_a D)^p = (∑ᵢ |aᵢ|^p) ∑ₙ sₙ(D)^p`.  When `a ∉ ℓ^p` both sides are the zero value of a
divergent sum. -/
theorem tsum_rpow_rectApproxNumber_weightedInduction [Countable I] (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    {p : ℝ} (hp : 0 < p) (hDS : MemRectSchattenClass p D) :
    ∑' n, rectApproxNumber (weightedInduction a D U V hbdd) n ^ p
      = (∑' i, ‖a i‖ ^ p) * ∑' n, rectApproxNumber D n ^ p := by
  have hD : IsCompactOperator D := isCompactOperator_of_memRectSchattenClass hp hDS
  have h := congrArg ENNReal.toReal
    (tsum_ofReal_rpow_rectApproxNumber_weightedInduction a D U V hbdd hD hp)
  rwa [ENNReal.toReal_mul,
    tsum_toReal_ofReal_eq fun n => Real.rpow_nonneg (rectApproxNumber_nonneg _ n) p,
    tsum_toReal_ofReal_eq fun i => Real.rpow_nonneg (norm_nonneg _) p,
    tsum_toReal_ofReal_eq fun n => Real.rpow_nonneg (rectApproxNumber_nonneg _ n) p] at h

/-- `(WOI.9)` at `p = 1`: the trace norm of the weighted induction of a trace-class block is the
`ℓ¹` mass of the amplitudes times the local trace norm. -/
theorem rectTraceNorm_weightedInduction [Countable I] (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    (hDS : MemRectSchattenClass 1 D) :
    rectTraceNorm (lp (fun _ : I => H) 2) (lp (fun _ : I => K) 2)
        (weightedInduction a D U V hbdd)
      = (∑' i, ‖a i‖) * rectTraceNorm H K D := by
  have h := tsum_rpow_rectApproxNumber_weightedInduction a D U V hbdd one_pos hDS
  simp only [Real.rpow_one] at h
  exact h

/-- **Theorem 4.1, `p = 1`.**  Trace-class global admission is exactly an `ℓ¹` amplitude budget. -/
theorem memRectSchattenClass_one_weightedInduction_iff [Countable I] (a : I → ℂ)
    (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (hDS : MemRectSchattenClass 1 D)
    (hD0 : D ≠ 0) :
    MemRectSchattenClass 1 (weightedInduction a D U V hbdd) ↔ Summable fun i => ‖a i‖ := by
  rw [memRectSchattenClass_weightedInduction_iff a D U V hbdd one_pos hDS hD0]
  simp only [Real.rpow_one]

/-- **Theorem 3.1, `(WOI.6)` in `c₀` form.**  For a nonzero compact block, the weighted induction
is compact exactly when `aᵢ → 0` along the cofinite filter. -/
theorem isCompactOperator_weightedInduction_iff_tendsto [DecidableEq I] (a : I → ℂ)
    (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (hD : IsCompactOperator D) (hDne : D ≠ 0) :
    IsCompactOperator (weightedInduction a D U V hbdd) ↔ Tendsto a cofinite (𝓝 0) := by
  rw [isCompactOperator_weightedInduction_iff a D U V hbdd hD hDne,
    tailSup_eq_zero_iff_tendsto hbdd]

end Schatten

/-! ## The weighted Gram -/

section Gram

variable {I : Type} [Nonempty I] {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem adjoint_comp_self_ne_zero {D : H →L[ℂ] K} (hD0 : D ≠ 0) :
    ContinuousLinearMap.adjoint D ∘L D ≠ 0 := by
  intro h
  have hn := ContinuousLinearMap.norm_adjoint_comp_self D
  rw [h, norm_zero] at hn
  have hpos : 0 < ‖D‖ := norm_pos_iff.mpr hD0
  nlinarith

/-- **Section 5 (1).**  The positive Gram of the weighted induction of a nonzero compact block is
compact exactly when `(|aᵢ|²) ∈ c₀`, which is exactly `a ∈ c₀`: positivity does not repair
decay. -/
theorem isCompactOperator_gram_weightedInduction_iff [DecidableEq I] (a : I → ℂ)
    (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (hD : IsCompactOperator D) (hDne : D ≠ 0) :
    (IsCompactOperator (ContinuousLinearMap.adjoint (weightedInduction a D U V hbdd)
        ∘L weightedInduction a D U V hbdd)
      ↔ tailSup (fun i => ((‖a i‖ ^ 2 : ℝ) : ℂ)) = 0)
    ∧ (tailSup (fun i => ((‖a i‖ ^ 2 : ℝ) : ℂ)) = 0 ↔ tailSup a = 0)
    ∧ (tailSup a = 0 ↔ IsCompactOperator (weightedInduction a D U V hbdd)) := by
  refine ⟨?_, tailSup_normSq_eq_zero_iff hbdd,
    (isCompactOperator_weightedInduction_iff a D U V hbdd hD hDne).symm⟩
  rw [gram_weightedInduction]
  exact isCompactOperator_weightedInduction_iff _ _ U U _
    (hD.clm_comp (ContinuousLinearMap.adjoint D)) (adjoint_comp_self_ne_zero hDne)

/-- A Hilbert--Schmidt operator has trace-class Gram, with approximation numbers squared. -/
theorem memRectSchattenClass_one_adjoint_comp_self {D : H →L[ℂ] K}
    (hDS : MemRectSchattenClass 2 D) :
    MemRectSchattenClass 1 (ContinuousLinearMap.adjoint D ∘L D) := by
  have hD : IsCompactOperator D := isCompactOperator_of_memRectSchattenClass two_pos hDS
  unfold MemRectSchattenClass at hDS ⊢
  refine hDS.congr fun n => ?_
  rw [Real.rpow_one, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact rectApproxNumber_sq_eq_approxNumber_adjoint_comp_self D hD n

/-- **Section 5 (2).**  For a nonzero Hilbert--Schmidt block, the positive Gram of the weighted
induction is trace class exactly when `a ∈ ℓ²`. -/
theorem memRectSchattenClass_one_gram_weightedInduction_iff [Countable I] (a : I → ℂ)
    (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (hDS : MemRectSchattenClass 2 D)
    (hD0 : D ≠ 0) :
    MemRectSchattenClass 1 (ContinuousLinearMap.adjoint (weightedInduction a D U V hbdd)
        ∘L weightedInduction a D U V hbdd)
      ↔ Summable fun i => ‖a i‖ ^ 2 := by
  rw [gram_weightedInduction, memRectSchattenClass_weightedInduction_iff _ _ U U _ one_pos
    (memRectSchattenClass_one_adjoint_comp_self hDS) (adjoint_comp_self_ne_zero hD0)]
  have hnorm : ∀ i, ‖((‖a i‖ ^ 2 : ℝ) : ℂ)‖ ^ (1 : ℝ) = ‖a i‖ ^ 2 := fun i => by
    rw [Real.rpow_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp_rw [hnorm]

end Gram

end

end GaloisForLFunctions.HTGeometry
