import GaloisForLFunctions.HTGeometry.GeometricDecayFredholmDeterminant
import Mathlib.LinearAlgebra.PID
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# Traces and determinants of finite-rank operators

For a continuous operator `X` on a complex normed space, `finiteRankTrace X` and
`finiteRankDet X = det(1 − X)` are the trace and the determinant computed on the range of `X`.
When the range is finite dimensional they can be computed on any finite-dimensional subspace
containing it (`finiteRankTrace_eq_trace_restrict`, `finiteRankDet_eq_det_restrict`): the trace by
the trace of a restriction to a submodule containing the image, the determinant by the block
decomposition of the determinant along the range, whose quotient block is the identity.

Main results:
* `differentiable_det_one_sub_smul`, `eventually_det_one_sub_smul_eq_exp` — in finite dimension
  `z ↦ det(1 − z f)` is entire and equals `exp(−Σ_{n≥1} zⁿ tr(fⁿ)/n)` near `0`.
* `det_one_sub_eq_exp_of_norm_trace_pow_le` — the identity at `z = 1` when the traces of the
  powers decay geometrically.
* `det_one_sub_eq_mul_of_trace_pow_eq_add` — determinants multiply when traces of powers add.
* `norm_trace_restrictEnd_le` — `|tr(X|_W)| ≤ dim W · ‖X‖`: every eigenvalue is bounded by the
  operator norm.
* `finiteRankTrace_add_of_le`, `finiteRankTrace_sub_of_le`, `finiteRankTrace_conj`,
  `finiteRankDet_conj` — additivity and similarity invariance.
-/

open Module Filter Topology Metric

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FiniteRank

open GeomFredholm

/-! ## Determinant identities in finite dimension -/

section FiniteDim

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- `z ↦ det(1 − z f)` is entire: it is a polynomial in `z`. -/
theorem differentiable_det_one_sub_smul (f : Module.End ℂ V) :
    Differentiable ℂ fun z : ℂ => LinearMap.det (1 - z • f) := by
  set b := Module.finBasis ℂ V
  set M := LinearMap.toMatrix b b f
  have h : (fun z : ℂ => LinearMap.det (1 - z • f)) = fun z : ℂ =>
      ∑ σ : Equiv.Perm (Fin (finrank ℂ V)), (Equiv.Perm.sign σ : ℂ) *
        ∏ i, ((if σ i = i then (1 : ℂ) else 0) - z * M (σ i) i) := by
    funext z
    rw [← LinearMap.det_toMatrix b, map_sub, LinearMap.toMatrix_one, map_smul, Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
    simp [Matrix.one_apply, M]
  rw [h]
  fun_prop

/-- The traces of the powers of an endomorphism grow at most geometrically. -/
theorem exists_norm_trace_pow_le (f : Module.End ℂ V) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ‖LinearMap.trace ℂ V (f ^ n)‖ ≤ finrank ℂ V * B ^ n := by
  set b := Module.finBasis ℂ V
  set M := LinearMap.toMatrix b b f
  obtain ⟨U, T, hU1, hU2, hT, hMT⟩ := exists_schur_triangulation (finrank ℂ V) M
  refine ⟨Real.sqrt (matHSNormSq M), Real.sqrt_nonneg _, fun n => ?_⟩
  rw [LinearMap.trace_eq_matrix_trace ℂ b, ← LinearMap.toMatrix_pow,
    trace_pow_eq_sum_diag hU1 hU2 hT hMT n]
  calc ‖∑ i, T i i ^ n‖ ≤ ∑ i, ‖T i i ^ n‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (finrank ℂ V), Real.sqrt (matHSNormSq M) ^ n := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_diag_le_of_schur hU2 hMT i) n
    _ = finrank ℂ V * Real.sqrt (matHSNormSq M) ^ n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The trace series converges on the disc `‖z‖ B < 1` when the traces grow like `d Bⁿ`. -/
theorem summable_traceSeries_of_le {T : ℕ → ℂ} {d B : ℝ} (hB : 0 ≤ B)
    (hT : ∀ n, ‖T n‖ ≤ d * B ^ n) {z : ℂ} (hz : ‖z‖ * B < 1) :
    Summable fun n : ℕ => z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) * T (n + 1) := by
  have h0 : 0 ≤ ‖z‖ * B := mul_nonneg (norm_nonneg _) hB
  refine Summable.of_norm_bounded
    (((summable_geometric_of_lt_one h0 hz).mul_left (d * (‖z‖ * B)))) fun n => ?_
  rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
  have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  calc ‖z‖ ^ (n + 1) / ((n + 1 : ℕ) : ℝ) * ‖T (n + 1)‖ ≤ ‖z‖ ^ (n + 1) * (d * B ^ (n + 1)) :=
        mul_le_mul (div_le_self (by positivity) h1) (hT _) (norm_nonneg _) (by positivity)
    _ = d * (‖z‖ * B) * (‖z‖ * B) ^ n := by ring

/-- **Near `z = 0`, `det(1 − z f) = exp(−Σ_{n≥1} zⁿ tr(fⁿ)/n)`**, with a convergent series. -/
theorem eventually_det_one_sub_smul_eq_exp (f : Module.End ℂ V) :
    ∀ᶠ z in 𝓝 (0 : ℂ),
      Summable (fun n : ℕ =>
        z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) * LinearMap.trace ℂ V (f ^ (n + 1))) ∧
      LinearMap.det (1 - z • f) =
        Complex.exp (-traceSeries (fun n => LinearMap.trace ℂ V (f ^ n)) z) := by
  set b := Module.finBasis ℂ V
  set M := LinearMap.toMatrix b b f
  set H := Real.sqrt (matHSNormSq M)
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have htr : (fun n => LinearMap.trace ℂ V (f ^ n)) = fun n => (M ^ n).trace := by
    funext n
    rw [LinearMap.trace_eq_matrix_trace ℂ b, ← LinearMap.toMatrix_pow]
  obtain ⟨U, T, hU1, hU2, hT, hMT⟩ := exists_schur_triangulation (finrank ℂ V) M
  have hbound : ∀ n : ℕ, ‖(M ^ n).trace‖ ≤ finrank ℂ V * H ^ n := by
    intro n
    rw [trace_pow_eq_sum_diag hU1 hU2 hT hMT n]
    calc ‖∑ i, T i i ^ n‖ ≤ ∑ i, ‖T i i ^ n‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin (finrank ℂ V), H ^ n := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_diag_le_of_schur hU2 hMT i) n
      _ = finrank ℂ V * H ^ n := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hεpos : 0 < (H + 1)⁻¹ := by positivity
  filter_upwards [ball_mem_nhds (0 : ℂ) hεpos] with z hz
  have hzl : ‖z‖ < (H + 1)⁻¹ := mem_ball_zero_iff.mp hz
  have hzH : ‖z‖ * H < 1 := by
    calc ‖z‖ * H ≤ (H + 1)⁻¹ * H := mul_le_mul_of_nonneg_right hzl.le hH
      _ < 1 := by rw [inv_mul_lt_iff₀ (by positivity)]; linarith
  have hsum : Summable fun n : ℕ => z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) * (M ^ (n + 1)).trace :=
    summable_traceSeries_of_le hH hbound hzH
  refine ⟨hsum.congr fun n => by rw [congrFun htr (n + 1)], ?_⟩
  rw [htr]
  have hdetM : LinearMap.det (1 - z • f) = (1 - z • M).det := by
    rw [← LinearMap.det_toMatrix b, map_sub, LinearMap.toMatrix_one, map_smul]
  have h := exp_neg_traceSeries_eq_finiteDet2_neg M (z := z) hzH
  have hdet : finiteDet2 (-M) z = (1 - z • M).det * Complex.exp (z * M.trace) := by
    have e1 : (1 : Matrix (Fin (finrank ℂ V)) (Fin (finrank ℂ V)) ℂ) + z • -M = 1 - z • M := by
      rw [smul_neg, ← sub_eq_add_neg]
    have e2 : -(z * (-M).trace) = z * M.trace := by rw [Matrix.trace_neg, mul_neg, neg_neg]
    show (1 + z • -M).det * Complex.exp (-(z * (-M).trace)) = _
    rw [e1, e2]
  have hsplit : traceSeries (fun n => (M ^ n).trace) z =
      z * M.trace + ∑' k : ℕ, z ^ (k + 2) / ((k + 2 : ℕ) : ℂ) * (M ^ (k + 2)).trace := by
    unfold traceSeries
    rw [hsum.tsum_eq_zero_add]
    simp only [zero_add, pow_one, Nat.cast_one, div_one]
  rw [hdetM, hsplit, neg_add, Complex.exp_add, h, hdet, mul_comm (Complex.exp _), mul_assoc,
    ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]

/-- **`det(1 − f) = exp(−Σ_{n≥1} tr(fⁿ)/n)` when the traces of the powers decay geometrically.**
Both sides of the `z`-identity are holomorphic on a disc of radius `> 1`. -/
theorem det_one_sub_eq_exp_of_norm_trace_pow_le (f : Module.End ℂ V) {C c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c < 1) (hb : ∀ n : ℕ, ‖LinearMap.trace ℂ V (f ^ (n + 1))‖ ≤ C * c ^ (n + 1)) :
    LinearMap.det (1 - f) =
      Complex.exp (-traceSeries (fun n => LinearMap.trace ℂ V (f ^ n)) 1) := by
  set r : ℝ := 2 / (1 + c) with hr
  have hr1 : 1 < r := by rw [hr, lt_div_iff₀ (by linarith)]; linarith
  have hrc : r * c < 1 := by
    rw [hr, div_mul_eq_mul_div, div_lt_one (by linarith)]; linarith
  have hrc0 : 0 ≤ r * c := mul_nonneg (by linarith) hc0
  set U : Set ℂ := ball 0 r
  have hUo : IsOpen U := isOpen_ball
  have hC : ∀ n : ℕ, ‖LinearMap.trace ℂ V (f ^ (n + 1))‖ ≤ |C| * c ^ (n + 1) := fun n =>
    (hb n).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hc0 _))
  have hdiffS : DifferentiableOn ℂ (traceSeries (fun n => LinearMap.trace ℂ V (f ^ n))) U := by
    unfold traceSeries
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun n => |C| * (r * c) ^ (n + 1))
      ((summable_geometric_of_lt_one hrc0 hrc).mul_left (|C| * (r * c)) |>.congr fun n => by ring)
      (fun n => ?_) hUo (fun n z hz => ?_)
    · exact ((differentiableOn_id.pow _).div_const _).mul_const _
    · have hl : ‖z‖ ≤ r := (mem_ball_zero_iff.mp hz).le
      rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
      have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      calc ‖z‖ ^ (n + 1) / ((n + 1 : ℕ) : ℝ) * ‖LinearMap.trace ℂ V (f ^ (n + 1))‖
          ≤ r ^ (n + 1) * (|C| * c ^ (n + 1)) :=
            mul_le_mul ((div_le_self (by positivity) h1).trans
              (pow_le_pow_left₀ (norm_nonneg _) hl _)) (hC n) (norm_nonneg _) (by positivity)
        _ = |C| * (r * c) ^ (n + 1) := by ring
  have hg : DifferentiableOn ℂ
      (fun z => Complex.exp (-traceSeries (fun n => LinearMap.trace ℂ V (f ^ n)) z)) U :=
    hdiffS.neg.cexp
  have hf : DifferentiableOn ℂ (fun z : ℂ => LinearMap.det (1 - z • f)) U :=
    (differentiable_det_one_sub_smul f).differentiableOn
  have heq : (fun z : ℂ => LinearMap.det (1 - z • f)) =ᶠ[𝓝 0]
      fun z => Complex.exp (-traceSeries (fun n => LinearMap.trace ℂ V (f ^ n)) z) :=
    (eventually_det_one_sub_smul_eq_exp f).mono fun z hz => hz.2
  have h0U : (0 : ℂ) ∈ U := mem_ball_self (by linarith)
  have hEq := (hf.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hUo)
    (convex_ball 0 r).isPreconnected h0U heq
  have h1U : (1 : ℂ) ∈ U := mem_ball_zero_iff.mpr (by simpa using hr1)
  have := hEq h1U
  simpa using this

/-- **Determinants multiply when the traces of all powers add.**  The three polynomials
`det(1 − z ·)` agree near `0` through their trace series, hence everywhere. -/
theorem det_one_sub_eq_mul_of_trace_pow_eq_add {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [FiniteDimensional ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [FiniteDimensional ℂ V₂]
    (f : Module.End ℂ V) (g : Module.End ℂ V₁) (h : Module.End ℂ V₂)
    (htr : ∀ n : ℕ, LinearMap.trace ℂ V (f ^ (n + 1)) =
      LinearMap.trace ℂ V₁ (g ^ (n + 1)) + LinearMap.trace ℂ V₂ (h ^ (n + 1))) :
    LinearMap.det (1 - f) = LinearMap.det (1 - g) * LinearMap.det (1 - h) := by
  have hF : Differentiable ℂ fun z : ℂ =>
      LinearMap.det (1 - z • f) - LinearMap.det (1 - z • g) * LinearMap.det (1 - z • h) :=
    (differentiable_det_one_sub_smul f).sub
      ((differentiable_det_one_sub_smul g).mul (differentiable_det_one_sub_smul h))
  have hzero : (fun z : ℂ =>
      LinearMap.det (1 - z • f) - LinearMap.det (1 - z • g) * LinearMap.det (1 - z • h))
        =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [eventually_det_one_sub_smul_eq_exp f, eventually_det_one_sub_smul_eq_exp g,
      eventually_det_one_sub_smul_eq_exp h] with z hf hg hh
    rw [hf.2, hg.2, hh.2, ← Complex.exp_add, ← neg_add]
    have hadd : traceSeries (fun n => LinearMap.trace ℂ V (f ^ n)) z =
        traceSeries (fun n => LinearMap.trace ℂ V₁ (g ^ n)) z +
          traceSeries (fun n => LinearMap.trace ℂ V₂ (h ^ n)) z := by
      unfold traceSeries
      rw [← hg.1.tsum_add hh.1]
      exact tsum_congr fun n => by simp only [htr n, mul_add]
    rw [hadd, sub_self]
  have hEq := (hF.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_const) isPreconnected_univ (Set.mem_univ 0) hzero
  have := hEq (Set.mem_univ 1)
  simp only [one_smul] at this
  exact sub_eq_zero.mp this

end FiniteDim

/-! ## Operators of finite rank -/

section Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The restriction of a continuous operator to an invariant subspace. -/
def restrictEnd (X : E →L[ℂ] E) (W : Submodule ℂ E) (h : ∀ v ∈ W, X v ∈ W) :
    Module.End ℂ W :=
  (X : E →ₗ[ℂ] E).restrict h

@[simp] theorem coe_restrictEnd_apply (X : E →L[ℂ] E) (W : Submodule ℂ E)
    (h : ∀ v ∈ W, X v ∈ W) (v : W) : ((restrictEnd X W h v : W) : E) = X v := rfl

/-- The range of an operator, as a submodule. -/
abbrev opRange (X : E →L[ℂ] E) : Submodule ℂ E := LinearMap.range (X : E →ₗ[ℂ] E)

theorem mem_opRange (X : E →L[ℂ] E) (v : E) : X v ∈ opRange X := LinearMap.mem_range_self _ v

/-- The **trace of an operator computed on its range**. -/
def finiteRankTrace (X : E →L[ℂ] E) : ℂ :=
  LinearMap.trace ℂ (opRange X) (restrictEnd X (opRange X) fun v _ => mem_opRange X v)

/-- The **determinant `det(1 − X)` computed on the range of `X`**. -/
def finiteRankDet (X : E →L[ℂ] E) : ℂ :=
  LinearMap.det (1 - restrictEnd X (opRange X) fun v _ => mem_opRange X v)

theorem opRange_le (X : E →L[ℂ] E) {W : Submodule ℂ E} (hX : ∀ v, X v ∈ W) : opRange X ≤ W := by
  rintro _ ⟨v, rfl⟩; exact hX v

/-- **The trace on the range equals the trace on any finite-dimensional subspace containing the
range.** -/
theorem finiteRankTrace_eq_trace_restrict (X : E →L[ℂ] E) (W : Submodule ℂ E)
    [FiniteDimensional ℂ W] (hX : ∀ v, X v ∈ W) :
    finiteRankTrace X = LinearMap.trace ℂ W (restrictEnd X W fun v _ => hX v) := by
  have hle : opRange X ≤ W := opRange_le X hX
  set f := restrictEnd X W fun v _ => hX v
  set p : Submodule ℂ W := (opRange X).comap W.subtype
  have hfp : ∀ x, f x ∈ p := fun x => mem_opRange X x
  rw [← LinearMap.trace_restrict_eq_of_forall_mem p f hfp]
  set e := Submodule.comapSubtypeEquivOfLe hle
  rw [finiteRankTrace, ← LinearMap.trace_conj' (f.restrict fun x _ => hfp x) e]
  congr 1

/-- **`det(1 − X)` on the range equals the determinant on any finite-dimensional subspace
containing the range**: the quotient block of `1 − X` is the identity. -/
theorem finiteRankDet_eq_det_restrict (X : E →L[ℂ] E) (W : Submodule ℂ E)
    [FiniteDimensional ℂ W] (hX : ∀ v, X v ∈ W) :
    finiteRankDet X = LinearMap.det (1 - restrictEnd X W fun v _ => hX v) := by
  have hle : opRange X ≤ W := opRange_le X hX
  set f := restrictEnd X W fun v _ => hX v
  set p : Submodule ℂ W := (opRange X).comap W.subtype
  have hfp : ∀ x, f x ∈ p := fun x => mem_opRange X x
  have he : p ≤ p.comap (1 - f) := by
    intro x hx
    simp only [Submodule.mem_comap, LinearMap.sub_apply, Module.End.one_apply]
    exact p.sub_mem hx (hfp x)
  rw [LinearMap.det_eq_det_mul_det p (1 - f) he]
  have hq : p.mapQ p (1 - f) he = LinearMap.id := by
    refine Submodule.linearMap_qext p (LinearMap.ext fun x => ?_)
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.id_coe, id_eq, LinearMap.sub_apply, Module.End.one_apply]
    rw [Submodule.Quotient.eq]
    simpa using p.neg_mem (hfp x)
  rw [hq, LinearMap.det_id, mul_one]
  set e := Submodule.comapSubtypeEquivOfLe hle
  rw [finiteRankDet, ← LinearMap.det_conj ((1 - f).restrict he) e]
  congr 1

/-- **Additivity of the finite-rank trace.** -/
theorem finiteRankTrace_add_of_le (X Y : E →L[ℂ] E) (W : Submodule ℂ E) [FiniteDimensional ℂ W]
    (hX : ∀ v, X v ∈ W) (hY : ∀ v, Y v ∈ W) :
    finiteRankTrace (X + Y) = finiteRankTrace X + finiteRankTrace Y := by
  rw [finiteRankTrace_eq_trace_restrict X W hX, finiteRankTrace_eq_trace_restrict Y W hY,
    finiteRankTrace_eq_trace_restrict (X + Y) W (fun v => W.add_mem (hX v) (hY v)), ← map_add]
  congr 1

/-- **The finite-rank trace of a difference.** -/
theorem finiteRankTrace_sub_of_le (X Y : E →L[ℂ] E) (W : Submodule ℂ E) [FiniteDimensional ℂ W]
    (hX : ∀ v, X v ∈ W) (hY : ∀ v, Y v ∈ W) :
    finiteRankTrace (X - Y) = finiteRankTrace X - finiteRankTrace Y := by
  rw [finiteRankTrace_eq_trace_restrict X W hX, finiteRankTrace_eq_trace_restrict Y W hY,
    finiteRankTrace_eq_trace_restrict (X - Y) W (fun v => W.sub_mem (hX v) (hY v)), ← map_sub]
  congr 1

/-- **Every eigenvalue is bounded by the operator norm, so `|tr(X|_W)| ≤ dim W · ‖X‖`.** -/
theorem norm_trace_restrictEnd_le (X : E →L[ℂ] E) (W : Submodule ℂ E) [FiniteDimensional ℂ W]
    (h : ∀ v ∈ W, X v ∈ W) :
    ‖LinearMap.trace ℂ W (restrictEnd X W h)‖ ≤ finrank ℂ W * ‖X‖ := by
  set f := restrictEnd X W h
  set b := Module.finBasis ℂ W
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace_eq_sum_roots_charpoly,
    LinearMap.charpoly_toMatrix]
  have hroot : ∀ μ ∈ f.charpoly.roots, ‖μ‖ ≤ ‖X‖ := by
    intro μ hμ
    have hne : f.charpoly ≠ 0 := (LinearMap.charpoly_monic f).ne_zero
    have hr : f.charpoly.IsRoot μ := (Polynomial.mem_roots hne).mp hμ
    obtain ⟨v, hv⟩ :=
      ((Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr hr).exists_hasEigenvector
    have hv0 : (v : E) ≠ 0 := fun h0 => hv.2 (Subtype.ext h0)
    have hfv : X v = μ • (v : E) := congrArg Subtype.val hv.apply_eq_smul
    have hle : ‖μ‖ * ‖(v : E)‖ ≤ ‖X‖ * ‖(v : E)‖ := by
      rw [← norm_smul, ← hfv]; exact X.le_opNorm v
    exact le_of_mul_le_mul_right hle (norm_pos_iff.mpr hv0)
  have hcard : (f.charpoly.roots.map fun x => ‖x‖).card ≤ finrank ℂ W := by
    rw [Multiset.card_map, ← LinearMap.charpoly_natDegree f]
    exact Polynomial.card_roots' _
  calc ‖f.charpoly.roots.sum‖ ≤ (f.charpoly.roots.map fun x => ‖x‖).sum := norm_multiset_sum_le _
    _ ≤ (f.charpoly.roots.map fun x => ‖x‖).card • ‖X‖ :=
        Multiset.sum_le_card_nsmul _ _ fun x hx => by
          obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hx
          exact hroot μ hμ
    _ ≤ finrank ℂ W * ‖X‖ := by
        rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (norm_nonneg _)

/-- The finite-rank trace is bounded by the dimension of any finite-dimensional subspace containing
the range times the operator norm. -/
theorem norm_finiteRankTrace_le (X : E →L[ℂ] E) (W : Submodule ℂ E) [FiniteDimensional ℂ W]
    (hX : ∀ v, X v ∈ W) : ‖finiteRankTrace X‖ ≤ finrank ℂ W * ‖X‖ := by
  rw [finiteRankTrace_eq_trace_restrict X W hX]
  exact norm_trace_restrictEnd_le X W _

/-- **The finite-rank trace is invariant under similarity.** -/
theorem finiteRankTrace_conj (u : (E →L[ℂ] E)ˣ) (X : E →L[ℂ] E)
    [FiniteDimensional ℂ (opRange X)] :
    finiteRankTrace ((u : E →L[ℂ] E) * X * (↑(u⁻¹) : E →L[ℂ] E)) = finiteRankTrace X := by
  set U : E ≃L[ℂ] E := ContinuousLinearEquiv.ofUnit u
  set W : Submodule ℂ E := (opRange X).map (U.toLinearEquiv : E →ₗ[ℂ] E)
  haveI : FiniteDimensional ℂ W := inferInstance
  have hY : ∀ v, ((u : E →L[ℂ] E) * X * (↑(u⁻¹) : E →L[ℂ] E)) v ∈ W := fun v =>
    ⟨X ((↑(u⁻¹) : E →L[ℂ] E) v), mem_opRange X _, rfl⟩
  rw [finiteRankTrace_eq_trace_restrict _ W hY, finiteRankTrace,
    ← LinearMap.trace_conj' (restrictEnd X (opRange X) fun v _ => mem_opRange X v)
      (U.toLinearEquiv.submoduleMap (opRange X))]
  congr 1

/-- **`det(1 − X)` on the range is invariant under similarity.** -/
theorem finiteRankDet_conj (u : (E →L[ℂ] E)ˣ) (X : E →L[ℂ] E)
    [FiniteDimensional ℂ (opRange X)] :
    finiteRankDet ((u : E →L[ℂ] E) * X * (↑(u⁻¹) : E →L[ℂ] E)) = finiteRankDet X := by
  set U : E ≃L[ℂ] E := ContinuousLinearEquiv.ofUnit u
  set W : Submodule ℂ E := (opRange X).map (U.toLinearEquiv : E →ₗ[ℂ] E)
  haveI : FiniteDimensional ℂ W := inferInstance
  have hY : ∀ v, ((u : E →L[ℂ] E) * X * (↑(u⁻¹) : E →L[ℂ] E)) v ∈ W := fun v =>
    ⟨X ((↑(u⁻¹) : E →L[ℂ] E) v), mem_opRange X _, rfl⟩
  rw [finiteRankDet_eq_det_restrict _ W hY, finiteRankDet,
    ← LinearMap.det_conj (1 - restrictEnd X (opRange X) fun v _ => mem_opRange X v)
      (U.toLinearEquiv.submoduleMap (opRange X))]
  congr 1
  refine LinearMap.ext fun w => ?_
  obtain ⟨v, rfl⟩ := (U.toLinearEquiv.submoduleMap (opRange X)).surjective w
  have hu : ∀ v, (↑(u⁻¹) : E →L[ℂ] E) ((u : E →L[ℂ] E) v) = v := fun v => by
    show ((↑(u⁻¹) * ↑u : E →L[ℂ] E)) v = v
    rw [Units.inv_mul]; rfl
  have hU : ∀ v, (ContinuousLinearEquiv.ofUnit u) v = (u : E →L[ℂ] E) v := fun v => rfl
  apply Subtype.ext
  simp [restrictEnd, U, LinearEquiv.submoduleMap_apply, hu, hU]

end Operator

end GaloisForLFunctions.HTGeometry.FiniteRank
