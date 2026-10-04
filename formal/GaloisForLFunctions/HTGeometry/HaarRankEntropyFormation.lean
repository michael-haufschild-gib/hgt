import GaloisForLFunctions.HTGeometry.AtomlessPhaseFormation
import GaloisForLFunctions.HTGeometry.PrimeHodgeResidueClock
import GaloisForLFunctions.RHTower.ApproximationNumberLowerBound
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Exact rank, norm and entropy of the Haar phase formation

For an orthonormal family `(e_k)` the normalized orbit state `Q_N = N⁻¹ ∑_{k<N} |e_k⟩⟨e_k|` is
`N⁻¹` times the projection onto `span{e_0, …, e_{N-1}}`.  Its approximation numbers are `N⁻¹`
(`N` times) and then `0`, so

`rank Q_N = N`, `‖Q_N‖ = N⁻¹`, `‖Q_N‖₂ = N^{-1/2}`, `‖Q_N‖₁ = 1`, `S(Q_N) = log N`,

where `S(T) = ∑ₙ -sₙ log sₙ` over the approximation numbers (for a positive compact operator these
are its eigenvalues with multiplicity, so `S(T) = -tr T log T`).

**Haar model.**  On `L²(S¹)` with normalized Haar measure and `U f = z f`, the rank-one state
`ρ = |1⟩⟨1|` has orbit `αⁿ(ρ) = |eₙ⟩⟨eₙ|`, `eₙ(z) = z⁻ⁿ`, so `M_N(ρ) = Q_N` for this orthonormal
family.  The reflection `(J f)(z) = f(z̄)` satisfies `J U J⁻¹ = U*`, sends `eₙ` to `zⁿ`, and carries
`M_N(ρ)` to the positive-frequency state with the same rank, norms and entropy.  An isometric
common encoding preserves every approximation number, hence cannot repair the ideal mismatch.
-/

open MeasureTheory Filter Topology Set AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.ContinuousLinearMap

/-! ### Normalized orthonormal orbit states -/

section OrthonormalAverage

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **von Neumann entropy** `S(T) = ∑ₙ -sₙ log sₙ` over the approximation numbers. -/
def vonNeumannEntropy (T : H →L[ℂ] H) : ℝ := ∑' n, Real.negMulLog (RHTower.approxNumber T n)

/-- The normalized orbit state `Q_N = N⁻¹ ∑_{k<N} |e_k⟩⟨e_k|`. -/
def orthoAverage (e : ℕ → H) (N : ℕ) : H →L[ℂ] H :=
  (N : ℂ)⁻¹ • ∑ k ∈ Finset.range N, InnerProductSpace.rankOne ℂ (e k) (e k)

/-- The aperture `span{e_0, …, e_{N-1}}`. -/
def orthoSpan (e : ℕ → H) (N : ℕ) : Submodule ℂ H :=
  Submodule.span ℂ (Set.range fun k : Fin N => e k)

omit [CompleteSpace H] in
theorem orthoAverage_apply (e : ℕ → H) (N : ℕ) (x : H) :
    orthoAverage e N x = (N : ℂ)⁻¹ • ∑ k : Fin N, ⟪e k, x⟫_ℂ • e k := by
  simp only [orthoAverage, smul_apply, sum_apply, InnerProductSpace.rankOne_apply]
  rw [Finset.sum_range (fun k => ⟪e k, x⟫_ℂ • e k)]

variable {e : ℕ → H}

omit [CompleteSpace H] in
theorem orthonormal_fin {e : ℕ → H} (he : Orthonormal ℂ e) (N : ℕ) :
    Orthonormal ℂ (fun k : Fin N => e k) :=
  he.comp _ Fin.val_injective

omit [CompleteSpace H] in
theorem finrank_orthoSpan (he : Orthonormal ℂ e) (N : ℕ) :
    Module.finrank ℂ (orthoSpan e N) = N := by
  rw [orthoSpan, finrank_span_eq_card (orthonormal_fin he N).linearIndependent, Fintype.card_fin]

instance (e : ℕ → H) (N : ℕ) : FiniteDimensional ℂ (orthoSpan e N) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

omit [CompleteSpace H] in
theorem orthoAverage_mem (e : ℕ → H) (N : ℕ) (x : H) : orthoAverage e N x ∈ orthoSpan e N := by
  rw [orthoAverage_apply]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

omit [CompleteSpace H] in
/-- On the aperture `Q_N` acts as `N⁻¹`. -/
theorem orthoAverage_of_mem (he : Orthonormal ℂ e) (N : ℕ) {w : H} (hw : w ∈ orthoSpan e N) :
    orthoAverage e N w = (N : ℂ)⁻¹ • w := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw
  rw [orthoAverage_apply]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(orthonormal_fin he N).inner_right_fintype c k]

omit [CompleteSpace H] in
theorem norm_orthoAverage_apply_le (he : Orthonormal ℂ e) (N : ℕ) (x : H) :
    ‖orthoAverage e N x‖ ≤ (N : ℝ)⁻¹ * ‖x‖ := by
  rw [orthoAverage_apply, norm_smul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsq : ‖∑ k : Fin N, ⟪e k, x⟫_ℂ • e k‖ ^ 2 = ∑ k : Fin N, ‖⟪e k, x⟫_ℂ‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, (orthonormal_fin he N).inner_sum]
    simp only [Complex.conj_mul', map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [← Complex.ofReal_pow]
  have hbessel := (orthonormal_fin he N).sum_inner_products_le x (s := Finset.univ)
  have h2 : ‖∑ k : Fin N, ⟪e k, x⟫_ℂ • e k‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hsq]
    exact hbessel
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

omit [CompleteSpace H] in
theorem norm_orthoAverage (he : Orthonormal ℂ e) {N : ℕ} (hN : 0 < N) :
    ‖orthoAverage e N‖ = (N : ℝ)⁻¹ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (norm_orthoAverage_apply_le he N)) ?_
  have hmem : e 0 ∈ orthoSpan e N := Submodule.subset_span ⟨⟨0, hN⟩, rfl⟩
  have h := (orthoAverage e N).le_opNorm (e 0)
  rw [orthoAverage_of_mem he N hmem, norm_smul, he.1 0, mul_one, mul_one, norm_inv,
    Complex.norm_natCast] at h
  exact h

omit [CompleteSpace H] in
theorem hasRankLE_orthoAverage (he : Orthonormal ℂ e) (N : ℕ) :
    RHTower.HasRankLE (orthoAverage e N) N :=
  ⟨orthoSpan e N, inferInstance, (finrank_orthoSpan he N).le, orthoAverage_mem e N⟩

omit [CompleteSpace H] in
/-- The approximation numbers of `Q_N`: `N⁻¹` for `n < N`, then `0`. -/
theorem approxNumber_orthoAverage (he : Orthonormal ℂ e) {N : ℕ} (hN : 0 < N) (n : ℕ) :
    RHTower.approxNumber (orthoAverage e N) n = if n < N then (N : ℝ)⁻¹ else 0 := by
  split_ifs with hn
  · refine RHTower.approxNumber_eq_of_subspace_of_hasRankLE (orthoSpan e N)
      (by rw [finrank_orthoSpan he N]; omega) (fun w hw => ?_) 0 (RHTower.hasRankLE_zero n)
      (by rw [sub_zero, norm_orthoAverage he hN])
    rw [orthoAverage_of_mem he N hw, norm_smul, norm_inv, Complex.norm_natCast]
  · refine le_antisymm ?_ (RHTower.approxNumber_nonneg _ n)
    have h := RHTower.approxNumber_le (orthoAverage e N) n (orthoAverage e N)
      ((hasRankLE_orthoAverage he N).mono (not_lt.mp hn))
    rwa [sub_self, norm_zero] at h

omit [CompleteSpace H] in
theorem tsum_approxNumber_orthoAverage (he : Orthonormal ℂ e) {N : ℕ} (hN : 0 < N)
    (g : ℝ → ℝ) (hg : g 0 = 0) :
    ∑' n, g (RHTower.approxNumber (orthoAverage e N) n) = N * g (N : ℝ)⁻¹ := by
  rw [tsum_eq_sum (s := Finset.range N) fun n hn => by
    rw [approxNumber_orthoAverage he hN, if_neg (by simpa using hn), hg]]
  rw [Finset.sum_congr rfl fun n hn => by
    rw [approxNumber_orthoAverage he hN, if_pos (Finset.mem_range.mp hn)]]
  simp

omit [CompleteSpace H] in
theorem memSchattenClass_one_orthoAverage (he : Orthonormal ℂ e) (N : ℕ) :
    RHTower.MemSchattenClass 1 (orthoAverage e N) :=
  RHTower.memSchattenClass_of_hasRankLE one_pos (hasRankLE_orthoAverage he N)

omit [CompleteSpace H] in
/-- `‖Q_N‖₁ = 1`. -/
theorem traceNorm_orthoAverage (he : Orthonormal ℂ e) {N : ℕ} (hN : 0 < N) :
    RHTower.traceNorm H (orthoAverage e N) = 1 := by
  have h := tsum_approxNumber_orthoAverage he hN id rfl
  simp only [id] at h
  rw [RHTower.traceNorm, h]
  field_simp

/-- `‖Q_N‖₂² = N⁻¹`. -/
theorem hsNormSq_orthoAverage (he : Orthonormal ℂ e) {N : ℕ} (hN : 0 < N) :
    hsNormSq (orthoAverage e N) = (N : ℝ)⁻¹ := by
  rw [RHTower.hsNormSq_eq_tsum_approxNumber_sq
      (memSchattenClass_one_orthoAverage he N).one_isHilbertSchmidt,
    tsum_approxNumber_orthoAverage he hN (fun s => s ^ 2) (by norm_num)]
  have : (N : ℝ) ≠ 0 := by positivity
  field_simp

/-- `‖Q_N‖₂ = N^{-1/2}`. -/
theorem hsNorm_orthoAverage (he : Orthonormal ℂ e) {N : ℕ} (hN : 0 < N) :
    (orthoAverage e N).hsNorm = (Real.sqrt N)⁻¹ := by
  rw [ContinuousLinearMap.hsNorm, hsNormSq_orthoAverage he hN, Real.sqrt_inv]

omit [CompleteSpace H] in
/-- `S(Q_N) = log N`. -/
theorem vonNeumannEntropy_orthoAverage (he : Orthonormal ℂ e) {N : ℕ} (hN : 0 < N) :
    vonNeumannEntropy (orthoAverage e N) = Real.log N := by
  rw [vonNeumannEntropy, tsum_approxNumber_orthoAverage he hN Real.negMulLog Real.negMulLog_zero,
    Real.negMulLog, Real.log_inv]
  have : (N : ℝ) ≠ 0 := by positivity
  field_simp

omit [CompleteSpace H] in
/-- `rank Q_N = N`: its range is the whole aperture. -/
theorem finrank_range_orthoAverage (he : Orthonormal ℂ e) {N : ℕ} (hN : 0 < N) :
    Module.finrank ℂ (LinearMap.range (orthoAverage e N : H →ₗ[ℂ] H)) = N := by
  have hrange : LinearMap.range (orthoAverage e N : H →ₗ[ℂ] H) = orthoSpan e N := by
    refine le_antisymm ?_ fun w hw => ?_
    · rintro _ ⟨x, rfl⟩
      exact orthoAverage_mem e N x
    · refine ⟨(N : ℂ) • w, ?_⟩
      show orthoAverage e N ((N : ℂ) • w) = w
      rw [map_smul, orthoAverage_of_mem he N hw, smul_smul,
        mul_inv_cancel₀ (by exact_mod_cast hN.ne'), one_smul]
  rw [hrange, finrank_orthoSpan he N]

omit [CompleteSpace H] in
theorem isPositive_orthoAverage (e : ℕ → H) (N : ℕ) : (orthoAverage e N).IsPositive := by
  refine IsPositive.smul_of_nonneg ?_ ?_
  · induction N with
    | zero => simp [isPositive_zero]
    | succ N ih =>
        rw [Finset.sum_range_succ]
        exact ih.add (InnerProductSpace.isPositive_rankOne_self _)
  · rw [show ((N : ℂ))⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.zero_le_real.mpr (by positivity)

omit [CompleteSpace H] in
/-- The conjugation orbit of a rank-one projection: `αⁿ(|v⟩⟨v|) = |U*ⁿ v⟩⟨U*ⁿ v|`. -/
theorem hsConj_iterate_rankOne (U : H ≃ₗᵢ[ℂ] H) (v : H) (n : ℕ) :
    (hsConj U)^[n] (InnerProductSpace.rankOne ℂ v v) =
      InnerProductSpace.rankOne ℂ (U.symm^[n] v) (U.symm^[n] v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, hsConj_rankOne, Function.iterate_succ_apply']

omit [CompleteSpace H] in
/-- **Rank/entropy law.**  If the orbit vectors `U*ⁿ v`, `n < N`, are orthonormal, the formed state
of `|v⟩⟨v|` is `Q_N`: rank `N`, operator norm `N⁻¹`, Hilbert–Schmidt norm `N^{-1/2}`, trace norm
`1` and entropy `log N`. -/
theorem hsCesaro_rankOne_eq_orthoAverage (U : H ≃ₗᵢ[ℂ] H) (v : H) (N : ℕ) :
    hsCesaro U N (InnerProductSpace.rankOne ℂ v v) =
      orthoAverage (fun n => U.symm^[n] v) N := by
  rw [hsCesaro, orthoAverage]
  congr 1
  exact Finset.sum_congr rfl fun n _ => hsConj_iterate_rankOne U v n

end OrthonormalAverage

/-! ### Isometric encodings preserve the ideal mismatch -/

section Encoding

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A common isometric encoding `T ↦ V T V*` preserves the trace norm. -/
theorem traceNorm_isometric_conj {V : H →L[ℂ] K}
    (hV : ContinuousLinearMap.adjoint V ∘L V = ContinuousLinearMap.id ℂ H) (T : H →L[ℂ] H) :
    RHTower.traceNorm K (V ∘L T ∘L ContinuousLinearMap.adjoint V) = RHTower.traceNorm H T := by
  simp only [RHTower.traceNorm, approxNumber_isometric_conj hV]

/-- A common isometric encoding preserves the Hilbert–Schmidt norm. -/
theorem hsNorm_isometric_conj {V : H →L[ℂ] K}
    (hV : ContinuousLinearMap.adjoint V ∘L V = ContinuousLinearMap.id ℂ H) {T : H →L[ℂ] H}
    (hT : IsHilbertSchmidt T) :
    (V ∘L T ∘L ContinuousLinearMap.adjoint V).hsNorm = T.hsNorm := by
  have hHS : IsHilbertSchmidt (V ∘L T ∘L ContinuousLinearMap.adjoint V) :=
    (hT.comp_right _).comp_left _
  rw [ContinuousLinearMap.hsNorm, ContinuousLinearMap.hsNorm,
    RHTower.hsNormSq_eq_tsum_approxNumber_sq hHS,
    RHTower.hsNormSq_eq_tsum_approxNumber_sq hT]
  simp only [approxNumber_isometric_conj hV]

/-- **No common encoding repairs the ideal mismatch.**  After an isometric encoding the formed
packets of Theorem 4.2 still have constant trace norm `‖T‖₁ > 0` and vanishing Hilbert–Schmidt
norm. -/
theorem encoded_idealEscape {U : H ≃ₗᵢ[ℂ] H} (hU : HasNoEigenvectors U) {V : H →L[ℂ] K}
    (hV : ContinuousLinearMap.adjoint V ∘L V = ContinuousLinearMap.id ℂ H) {T : H →L[ℂ] H}
    (hT : RHTower.MemSchattenClass 1 T) (hpos : T.IsPositive) (hT0 : T ≠ 0) :
    (∀ N, 1 ≤ N → RHTower.traceNorm K
        (V ∘L hsCesaro U N T ∘L ContinuousLinearMap.adjoint V) = RHTower.traceNorm H T) ∧
      0 < RHTower.traceNorm H T ∧
      Tendsto (fun N => (V ∘L hsCesaro U N T ∘L ContinuousLinearMap.adjoint V).hsNorm) atTop
        (𝓝 0) := by
  obtain ⟨hN, hpos', hHS, -⟩ := positive_traceClass_idealEscape hU hT hpos hT0
  refine ⟨fun N hN1 => by rw [traceNorm_isometric_conj hV, (hN N hN1).2.2.2], hpos', ?_⟩
  refine hHS.congr fun N => ?_
  rw [hsNorm_isometric_conj hV (isHilbertSchmidt_hsCesaro U hT.one_isHilbertSchmidt N)]

end Encoding

/-! ### Conjugating a normalized orbit state -/

section Conjugation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem hsConj_add (U : H ≃ₗᵢ[ℂ] H) (A B : H →L[ℂ] H) :
    hsConj U (A + B) = hsConj U A + hsConj U B := by
  ext x
  simp

theorem hsConj_smul (U : H ≃ₗᵢ[ℂ] H) (c : ℂ) (A : H →L[ℂ] H) :
    hsConj U (c • A) = c • hsConj U A := by
  ext x
  simp

/-- Unitary conjugation transports a normalized orbit state along the unitary. -/
theorem hsConj_orthoAverage (W : H ≃ₗᵢ[ℂ] H) (e : ℕ → H) (N : ℕ) :
    hsConj W (orthoAverage e N) = orthoAverage (fun n => W.symm (e n)) N := by
  rw [orthoAverage, orthoAverage, hsConj_smul]
  congr 1
  induction N with
  | zero => ext x; simp [hsConj]
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hsConj_add, ih, hsConj_rankOne]

end Conjugation

/-! ### The Haar model -/

section Haar

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The circle coordinate `z` on `AddCircle T`. -/
def circlePhase : AddCircle T → ℂ := fun x => fourier 1 x

omit hT in
theorem norm_circlePhase (x : AddCircle T) : ‖circlePhase x‖ = 1 := by
  rw [circlePhase, fourier_apply]
  exact Circle.norm_coe _

/-- Normalized Haar measure on the circle has no atoms. -/
theorem haarAddCircle_singleton (x : AddCircle T) : (@haarAddCircle T hT) {x} = 0 := by
  have hvol : (volume : Measure (AddCircle T)) {x} = 0 := by
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
    calc (volume : Measure (AddCircle T)) {x}
        ≤ volume (Metric.closedBall x ((ε : ℝ) / 2)) :=
          measure_mono (Set.singleton_subset_iff.mpr (Metric.mem_closedBall_self (by positivity)))
      _ = ENNReal.ofReal (min T (2 * ((ε : ℝ) / 2))) := AddCircle.volume_closedBall T _
      _ ≤ ENNReal.ofReal (2 * ((ε : ℝ) / 2)) := ENNReal.ofReal_le_ofReal (min_le_right _ _)
      _ = 0 + ε := by rw [mul_div_cancel₀ _ two_ne_zero, ENNReal.ofReal_coe_nnreal, zero_add]
  rw [volume_eq_smul_haarAddCircle, Measure.smul_apply, smul_eq_mul] at hvol
  exact (mul_eq_zero.mp hvol).resolve_left (by simp [hT.out])

/-- The circle coordinate is an atomless unit phase for normalized Haar measure. -/
theorem isAtomlessPhase_circle : IsAtomlessPhase (@haarAddCircle T hT) circlePhase where
  measurable := (fourier 1).continuous.measurable
  norm_eq_one := norm_circlePhase
  noAtoms := ⟨fun c => by
    have hm : Measurable (circlePhase (T := T)) := (fourier 1).continuous.measurable
    rw [Measure.map_apply hm (measurableSet_singleton c)]
    have hsub : (circlePhase ⁻¹' {c} : Set (AddCircle T)).Subsingleton := fun x hx y hy => by
      have hxy : circlePhase x = circlePhase y :=
        (Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm
      simp only [circlePhase, fourier_one] at hxy
      exact injective_toCircle hT.out.ne' (Circle.coe_inj.mp hxy)
    rcases hsub.eq_empty_or_singleton with h | ⟨x, h⟩
    · rw [h, measure_empty]
    · rw [h, haarAddCircle_singleton]⟩

/-- The orbit vectors `eₙ(z) = z⁻ⁿ`. -/
def haarOrbitVector (n : ℕ) : Lp ℂ 2 (@haarAddCircle T hT) := fourierLp 2 (-(n : ℤ))

theorem orthonormal_haarOrbitVector : Orthonormal ℂ (haarOrbitVector (T := T)) :=
  orthonormal_fourier.comp _ fun a b h => by simpa using h

/-- `U* eₙ = eₙ₊₁`. -/
theorem phaseMulUnitary_symm_haarOrbitVector (n : ℕ) :
    (phaseMulUnitary (isAtomlessPhase_circle (T := T))).symm (haarOrbitVector n) =
      haarOrbitVector (n + 1) := by
  refine Lp.ext_iff.mpr ?_
  filter_upwards [unimodularMulUnitary_symm_coeFn (μ := haarAddCircle)
      (isAtomlessPhase_circle (T := T)).measurable (isAtomlessPhase_circle (T := T)).norm_eq_one
      (haarOrbitVector n),
    coeFn_fourierLp 2 (-(n : ℤ)), coeFn_fourierLp (T := T) 2 (-((n + 1 : ℕ) : ℤ))]
    with x h1 h2 h3
  rw [show ((phaseMulUnitary (isAtomlessPhase_circle (T := T))).symm (haarOrbitVector n) :
      AddCircle T → ℂ) x = conj (circlePhase x) * (haarOrbitVector n : AddCircle T → ℂ) x from h1,
    show (haarOrbitVector (T := T) (n + 1) : AddCircle T → ℂ) x = fourier (-((n + 1 : ℕ) : ℤ)) x
      from h3, show (haarOrbitVector (T := T) n : AddCircle T → ℂ) x = fourier (-(n : ℤ)) x
      from h2, circlePhase, ← fourier_neg, ← fourier_add]
  congr 2
  push_cast
  ring

theorem phaseMulUnitary_symm_iterate (n : ℕ) :
    (phaseMulUnitary (isAtomlessPhase_circle (T := T))).symm^[n] (haarOrbitVector 0) =
      haarOrbitVector n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, phaseMulUnitary_symm_haarOrbitVector]

/-- **Theorem 5.1, `(AIE.7)`–`(AIE.9)`: exact Haar calibration.**  For `U f = z f` on `L²(S¹)` and
`ρ = |1⟩⟨1|`: `αⁿ(ρ) = |eₙ⟩⟨eₙ|` with `(eₙ)` orthonormal, `M_N(ρ) = N⁻¹ P_N`, and
`rank M_N(ρ) = N`, `‖M_N(ρ)‖ = N⁻¹`, `‖M_N(ρ)‖₂ = N^{-1/2}`, `‖M_N(ρ)‖₁ = 1`,
`S(M_N(ρ)) = log N`. -/
theorem haar_rank_entropy_formation {N : ℕ} (hN : 0 < N) :
    (∀ n, (hsConj (phaseMulUnitary (isAtomlessPhase_circle (T := T))))^[n]
        (InnerProductSpace.rankOne ℂ (haarOrbitVector 0) (haarOrbitVector 0)) =
        InnerProductSpace.rankOne ℂ (haarOrbitVector n) (haarOrbitVector n)) ∧
      hsCesaro (phaseMulUnitary (isAtomlessPhase_circle (T := T))) N
        (InnerProductSpace.rankOne ℂ (haarOrbitVector 0) (haarOrbitVector 0)) =
        orthoAverage haarOrbitVector N ∧
      Module.finrank ℂ (LinearMap.range
        (orthoAverage (haarOrbitVector (T := T)) N).toLinearMap) = N ∧
      ‖orthoAverage (haarOrbitVector (T := T)) N‖ = (N : ℝ)⁻¹ ∧
      (orthoAverage (haarOrbitVector (T := T)) N).hsNorm = (Real.sqrt N)⁻¹ ∧
      RHTower.traceNorm _ (orthoAverage (haarOrbitVector (T := T)) N) = 1 ∧
      vonNeumannEntropy (orthoAverage (haarOrbitVector (T := T)) N) = Real.log N := by
  have he := orthonormal_haarOrbitVector (T := T)
  refine ⟨fun n => ?_, ?_, finrank_range_orthoAverage he hN, norm_orthoAverage he hN,
    hsNorm_orthoAverage he hN, traceNorm_orthoAverage he hN, vonNeumannEntropy_orthoAverage he hN⟩
  · rw [hsConj_iterate_rankOne, phaseMulUnitary_symm_iterate]
  · rw [hsCesaro_rankOne_eq_orthoAverage]
    congr 1
    funext n
    exact phaseMulUnitary_symm_iterate n

/-! ### The functional-equation reflection -/

/-- The reflection `(J f)(z) = f(z̄)`, i.e. composition with negation on `AddCircle T`. -/
def circleReflectionₗᵢ : Lp ℂ 2 (@haarAddCircle T hT) →ₗᵢ[ℂ] Lp ℂ 2 (@haarAddCircle T hT) :=
  Lp.compMeasurePreservingₗᵢ ℂ Neg.neg (Measure.measurePreserving_neg haarAddCircle)

theorem circleReflectionₗᵢ_coeFn (f : Lp ℂ 2 (@haarAddCircle T hT)) :
    (circleReflectionₗᵢ f : AddCircle T → ℂ) =ᵐ[haarAddCircle] fun x => f (-x) :=
  Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_neg haarAddCircle)

theorem circleReflectionₗᵢ_involutive (f : Lp ℂ 2 (@haarAddCircle T hT)) :
    circleReflectionₗᵢ (circleReflectionₗᵢ f) = f := by
  refine Lp.ext_iff.mpr ?_
  have hq := (Measure.measurePreserving_neg (@haarAddCircle T hT)).quasiMeasurePreserving
  filter_upwards [circleReflectionₗᵢ_coeFn (circleReflectionₗᵢ f),
    hq.ae_eq_comp (circleReflectionₗᵢ_coeFn f)] with x h1 h2
  rw [h1]
  simpa using h2

/-- The reflection as a unitary. -/
def circleReflection : Lp ℂ 2 (@haarAddCircle T hT) ≃ₗᵢ[ℂ] Lp ℂ 2 (@haarAddCircle T hT) :=
  LinearIsometryEquiv.ofSurjective circleReflectionₗᵢ fun f =>
    ⟨circleReflectionₗᵢ f, circleReflectionₗᵢ_involutive f⟩

theorem circleReflection_apply (f : Lp ℂ 2 (@haarAddCircle T hT)) :
    circleReflection f = circleReflectionₗᵢ f := rfl

theorem circleReflection_symm_apply (f : Lp ℂ 2 (@haarAddCircle T hT)) :
    circleReflection.symm f = circleReflection f := by
  apply circleReflection.injective
  rw [LinearIsometryEquiv.apply_symm_apply, circleReflection_apply, circleReflection_apply,
    circleReflectionₗᵢ_involutive]

omit hT in
theorem circlePhase_neg (x : AddCircle T) : circlePhase (-x) = conj (circlePhase x) := by
  rw [circlePhase, circlePhase, fourier_apply, smul_neg, fourier_neg']

/-- **`J U J⁻¹ = U*`.** -/
theorem circleReflection_conj_phase (f : Lp ℂ 2 (@haarAddCircle T hT)) :
    circleReflection (phaseMulUnitary isAtomlessPhase_circle (circleReflection f)) =
      (phaseMulUnitary (isAtomlessPhase_circle (T := T))).symm f := by
  refine Lp.ext_iff.mpr ?_
  have hq := (Measure.measurePreserving_neg (@haarAddCircle T hT)).quasiMeasurePreserving
  filter_upwards [circleReflectionₗᵢ_coeFn
      (phaseMulUnitary isAtomlessPhase_circle (circleReflection f)),
    hq.ae_eq_comp (unimodularMulUnitary_coeFn (μ := haarAddCircle)
      (isAtomlessPhase_circle (T := T)).measurable (isAtomlessPhase_circle (T := T)).norm_eq_one
      (circleReflection f)),
    hq.ae_eq_comp (hq.ae_eq_comp (circleReflectionₗᵢ_coeFn f)),
    unimodularMulUnitary_symm_coeFn (μ := haarAddCircle)
      (isAtomlessPhase_circle (T := T)).measurable (isAtomlessPhase_circle (T := T)).norm_eq_one f,
    hq.ae_eq_comp (circleReflectionₗᵢ_coeFn f)] with x h1 h2 h3 h4 h5
  rw [circleReflection_apply, h1]
  simp only [Function.comp_apply] at h2 h5
  rw [show (phaseMulUnitary isAtomlessPhase_circle (circleReflection f) : AddCircle T → ℂ) (-x) =
      circlePhase (-x) * (circleReflection f : AddCircle T → ℂ) (-x) from h2,
    show ((phaseMulUnitary (isAtomlessPhase_circle (T := T))).symm f : AddCircle T → ℂ) x =
      conj (circlePhase x) * f x from h4, circleReflection_apply, h5, neg_neg, circlePhase_neg]

/-- The reflection sends `eₙ(z) = z⁻ⁿ` to `zⁿ`. -/
theorem circleReflection_haarOrbitVector (n : ℕ) :
    circleReflection (haarOrbitVector (T := T) n) = fourierLp 2 (n : ℤ) := by
  refine Lp.ext_iff.mpr ?_
  filter_upwards [circleReflectionₗᵢ_coeFn (haarOrbitVector (T := T) n),
    (Measure.measurePreserving_neg (@haarAddCircle T hT)).quasiMeasurePreserving.ae_eq_comp
      (coeFn_fourierLp 2 (-(n : ℤ))), coeFn_fourierLp (T := T) 2 (n : ℤ)] with x h1 h2 h3
  rw [circleReflection_apply, h1, h3]
  simp only [Function.comp_apply] at h2
  rw [show (haarOrbitVector (T := T) n : AddCircle T → ℂ) (-x) = fourier (-(n : ℤ)) (-x) from h2,
    fourier_apply, fourier_apply, neg_smul_neg]

/-- **Section 6.**  The reflection carries `M_N(ρ)` to the positive-frequency state
`N⁻¹ ∑_{n<N} |zⁿ⟩⟨zⁿ|`, which has the same rank, norms and entropy. -/
theorem circleReflection_formation {N : ℕ} (hN : 0 < N) :
    hsConj circleReflection.symm (orthoAverage (haarOrbitVector (T := T)) N) =
        orthoAverage (fun n => fourierLp (T := T) 2 (n : ℤ)) N ∧
      Module.finrank ℂ (LinearMap.range
        (orthoAverage (fun n => fourierLp (T := T) 2 (n : ℤ)) N).toLinearMap) = N ∧
      ‖orthoAverage (fun n => fourierLp (T := T) 2 (n : ℤ)) N‖ = (N : ℝ)⁻¹ ∧
      (orthoAverage (fun n => fourierLp (T := T) 2 (n : ℤ)) N).hsNorm = (Real.sqrt N)⁻¹ ∧
      RHTower.traceNorm _ (orthoAverage (fun n => fourierLp (T := T) 2 (n : ℤ)) N) = 1 ∧
      vonNeumannEntropy (orthoAverage (fun n => fourierLp (T := T) 2 (n : ℤ)) N) = Real.log N := by
  have he : Orthonormal ℂ (fun n : ℕ => fourierLp (T := T) 2 (n : ℤ)) :=
    orthonormal_fourier.comp _ fun a b h => by simpa using h
  refine ⟨?_, finrank_range_orthoAverage he hN, norm_orthoAverage he hN,
    hsNorm_orthoAverage he hN, traceNorm_orthoAverage he hN, vonNeumannEntropy_orthoAverage he hN⟩
  rw [hsConj_orthoAverage]
  congr 1
  funext n
  rw [LinearIsometryEquiv.symm_symm, circleReflection_haarOrbitVector]

end Haar

/-- **Section 6.**  Replacing the phase by its conjugate keeps it an atomless unit phase. -/
theorem IsAtomlessPhase.conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {ζ : X → ℂ}
    (hζ : IsAtomlessPhase μ ζ) : IsAtomlessPhase μ (fun x => conj (ζ x)) where
  measurable := Complex.continuous_conj.measurable.comp hζ.measurable
  norm_eq_one x := by rw [Complex.norm_conj, hζ.norm_eq_one]
  noAtoms := ⟨fun c => by
    have hm : Measurable (fun x => conj (ζ x)) :=
      Complex.continuous_conj.measurable.comp hζ.measurable
    rw [Measure.map_apply hm (measurableSet_singleton c)]
    have : (fun x => conj (ζ x)) ⁻¹' {c} = ζ ⁻¹' {conj c} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro rfl
        simp
      · rintro h
        rw [h, Complex.conj_conj]
    rw [this, hζ.measure_preimage_singleton]⟩

/-! ### Predictions -/

section Predictions

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Rank/entropy prediction.**  If the orbit vectors `U*ⁿ v`, `n < N`, are orthonormal, the formed
state of `|v⟩⟨v|` has rank `N`, operator norm `N⁻¹`, Hilbert–Schmidt norm `N^{-1/2}`, trace norm
`1` and entropy `log N`. -/
theorem orthogonalOrbit_rank_entropy (U : H ≃ₗᵢ[ℂ] H) (v : H)
    (he : Orthonormal ℂ fun n => U.symm^[n] v) {N : ℕ} (hN : 0 < N) :
    Module.finrank ℂ (LinearMap.range
        (hsCesaro U N (InnerProductSpace.rankOne ℂ v v)).toLinearMap) = N ∧
      ‖hsCesaro U N (InnerProductSpace.rankOne ℂ v v)‖ = (N : ℝ)⁻¹ ∧
      (hsCesaro U N (InnerProductSpace.rankOne ℂ v v)).hsNorm = (Real.sqrt N)⁻¹ ∧
      RHTower.traceNorm H (hsCesaro U N (InnerProductSpace.rankOne ℂ v v)) = 1 ∧
      vonNeumannEntropy (hsCesaro U N (InnerProductSpace.rankOne ℂ v v)) = Real.log N := by
  rw [hsCesaro_rankOne_eq_orthoAverage]
  exact ⟨finrank_range_orthoAverage he hN, norm_orthoAverage he hN, hsNorm_orthoAverage he hN,
    traceNorm_orthoAverage he hN, vonNeumannEntropy_orthoAverage he hN⟩

/-- **Topology prediction.**  For a unitary without eigenvectors but with approximate
eigenvectors, some Hilbert–Schmidt operator is not a transgression `α(S) - S` of any
Hilbert–Schmidt `S`: there is no bounded global primitive on `S₂`. -/
theorem exists_hilbertSchmidt_not_transgression {U : H ≃ₗᵢ[ℂ] H} (hU : HasNoEigenvectors U)
    (hU' : HasApproxEigenvectors U) :
    ∃ T : H →L[ℂ] H, IsHilbertSchmidt T ∧
      ∀ S : H →L[ℂ] H, IsHilbertSchmidt S → hsConj U S - S ≠ T := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  have hne : Set.range (columnConj b U - 1 : lp (fun _ : w => H) 2 →L[ℂ] _) ≠ Set.univ := by
    intro h
    exact not_isClosed_range_columnTransgression b hU hU' (h ▸ isClosed_univ)
  obtain ⟨x, hx⟩ : ∃ x, x ∉ Set.range (columnConj b U - 1 : lp (fun _ : w => H) 2 →L[ℂ] _) := by
    by_contra hcon
    push Not at hcon
    exact hne (Set.eq_univ_of_forall hcon)
  refine ⟨columnOperator b x, isHilbertSchmidt_columnOperator b x, fun S hS hST => hx ?_⟩
  refine ⟨hsColumns b hS, ?_⟩
  rw [sub_apply, one_apply_eq_self, columnConj_hsColumns, ← hsColumns_columnOperator b x]
  apply lp.ext
  funext j
  simp only [lp.coeFn_sub, Pi.sub_apply, hsColumns_apply, ← hST, sub_apply]

end Predictions

end GaloisForLFunctions.HTGeometry
