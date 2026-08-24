import GaloisForLFunctions.HTGeometry.HalfLineExponentialGram
import GaloisForLFunctions.HTGeometry.FiniteRankCutoffWardTrace
import GaloisForLFunctions.RHTower.NuclearRankOneTrace

open Complex Filter Topology MeasureTheory Set
open scoped BigOperators InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

abbrev HalfLineLaplaceL2 := Lp ℂ 2 halfLineLaplaceMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Algebraic finite synthesis of a Hilbert-space vector family. -/
def finiteSynthesisLinear {ι : Type*} [Fintype ι] (v : ι → H) :
    EuclideanSpace ℂ ι →ₗ[ℂ] H where
  toFun c := ∑ i, c i • v i
  map_add' := by
    intro c d
    change (∑ i, (c i + d i) • v i) = _
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro z c
    change (∑ i, (z * c i) • v i) = z • ∑ i, c i • v i
    simp only [mul_smul, Finset.smul_sum]

/-- Continuous finite synthesis; continuity is automatic from finite-dimensional domain. -/
def finiteSynthesis {ι : Type*} [Fintype ι] (v : ι → H) :
    EuclideanSpace ℂ ι →L[ℂ] H :=
  LinearMap.toContinuousLinearMap (finiteSynthesisLinear v)

omit [CompleteSpace H] in
@[simp] theorem finiteSynthesis_apply {ι : Type*} [Fintype ι]
    (v : ι → H) (c : EuclideanSpace ℂ ι) :
    finiteSynthesis v c = ∑ i, c i • v i := rfl

/-- Coordinates of the adjoint finite synthesis are the Hilbert analysis coefficients. -/
theorem adjoint_finiteSynthesis_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → H) (x : H) (i : ι) :
    (finiteSynthesis v).adjoint x i = inner ℂ (v i) x := by
  have h := (finiteSynthesis v).adjoint_inner_right
    (EuclideanSpace.single i 1) x
  simpa [finiteSynthesis_apply, PiLp.inner_apply, RCLike.inner_apply] using h

/-- An injective bounded synthesis with finite-dimensional domain has surjective adjoint. -/
theorem adjoint_surjective_of_finiteDimensional_domain_injective
    {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    [CompleteSpace D] [FiniteDimensional ℂ D]
    (S : D →L[ℂ] H) (hS : Function.Injective S) :
    Function.Surjective S.adjoint := by
  have hGramInj : Function.Injective (S.adjoint.comp S) := by
    apply LinearMap.ker_eq_bot.mp
    rw [S.ker_adjoint_comp_self, LinearMap.ker_eq_bot.mpr hS]
  have hGramSurj : Function.Surjective (S.adjoint.comp S) :=
    LinearMap.surjective_of_injective hGramInj
  intro d
  obtain ⟨c, hc⟩ := hGramSurj d
  exact ⟨S c, hc⟩

/-- The positive Gram on the ambient Hilbert space has the synthesis range. -/
theorem range_comp_adjoint_eq_range_of_finiteDimensional_domain_injective
    {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    [CompleteSpace D] [FiniteDimensional ℂ D]
    (S : D →L[ℂ] H) (hS : Function.Injective S) :
    (S.comp S.adjoint).range = S.range := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact ⟨S.adjoint x, rfl⟩
  · rintro y ⟨d, rfl⟩
    obtain ⟨x, hx⟩ :=
      adjoint_surjective_of_finiteDimensional_domain_injective S hS d
    refine ⟨x, ?_⟩
    change S (S.adjoint x) = S d
    rw [hx]

/-- Exact range dimension of an injective finite synthesis Gram. -/
theorem finrank_range_comp_adjoint_of_finiteDimensional_domain_injective
    {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    [CompleteSpace D] [FiniteDimensional ℂ D]
    (S : D →L[ℂ] H) (hS : Function.Injective S) :
    Module.finrank ℂ (S.comp S.adjoint).range = Module.finrank ℂ D := by
  rw [range_comp_adjoint_eq_range_of_finiteDimensional_domain_injective S hS]
  have hrank := LinearMap.finrank_range_add_finrank_ker S.toLinearMap
  rw [LinearMap.ker_eq_bot.mpr hS] at hrank
  simpa using hrank

def finiteExponentialHankel {r : ℕ} (a : Fin r → ℝ) (ha : ∀ j, 0 < a j)
    (m : Fin r → ℕ) : HalfLineLaplaceL2 →L[ℂ] HalfLineLaplaceL2 :=
  finiteRankProbe (fun j => ((2 * m j : ℕ) : ℂ))
    (fun j => expFeature (a j) (ha j)) (fun j => expFeature (a j) (ha j))

/-- Square-root weighted exponential vector whose Gram square is the Hankel layer. -/
def weightedExpFeature {r : ℕ} (a : Fin r → ℝ) (ha : ∀ j, 0 < a j)
    (m : Fin r → ℕ) (j : Fin r) : HalfLineLaplaceL2 :=
  ((Real.sqrt (2 * (m j : ℝ)) : ℝ) : ℂ) • expFeature (a j) (ha j)

/-- Finite synthesis map for the weighted exponential packet. -/
def finiteExponentialSynthesis {r : ℕ} (a : Fin r → ℝ) (ha : ∀ j, 0 < a j)
    (m : Fin r → ℕ) : EuclideanSpace ℂ (Fin r) →L[ℂ] HalfLineLaplaceL2 :=
  finiteSynthesis (weightedExpFeature a ha m)

/-- The finite Laplace--Hankel operator is exactly an adjoint Gram square. -/
theorem finiteExponentialSynthesis_comp_adjoint {r : ℕ} (a : Fin r → ℝ)
    (ha : ∀ j, 0 < a j) (m : Fin r → ℕ) :
    (finiteExponentialSynthesis a ha m).comp
        (finiteExponentialSynthesis a ha m).adjoint = finiteExponentialHankel a ha m := by
  classical
  apply ContinuousLinearMap.ext
  intro f
  rw [ContinuousLinearMap.comp_apply, finiteExponentialSynthesis,
    finiteSynthesis_apply, finiteExponentialHankel, finiteRankProbe]
  simp only [adjoint_finiteSynthesis_apply, weightedExpFeature, inner_smul_left,
    Complex.conj_ofReal, _root_.sum_apply, smul_apply,
    InnerProductSpace.rankOne_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_smul, smul_smul]
  congr 1
  have hsqrtR : Real.sqrt (2 * (m j : ℝ)) * Real.sqrt (2 * (m j : ℝ)) =
      2 * (m j : ℝ) := by
    simpa [pow_two] using Real.sq_sqrt (by positivity : 0 ≤ 2 * (m j : ℝ))
  have hsqrtC :
      ((Real.sqrt (2 * (m j : ℝ)) : ℝ) : ℂ) *
          ((Real.sqrt (2 * (m j : ℝ)) : ℝ) : ℂ) =
        (2 : ℂ) * (m j : ℂ) := by
    exact_mod_cast hsqrtR
  calc
    ((Real.sqrt (2 * (m j : ℝ)) : ℝ) : ℂ) *
          inner ℂ (expFeature (a j) (ha j)) f *
          ((Real.sqrt (2 * (m j : ℝ)) : ℝ) : ℂ) =
        (((Real.sqrt (2 * (m j : ℝ)) : ℝ) : ℂ) *
          ((Real.sqrt (2 * (m j : ℝ)) : ℝ) : ℂ)) *
          inner ℂ (expFeature (a j) (ha j)) f := by ring
    _ = (2 : ℂ) * (m j : ℂ) * inner ℂ (expFeature (a j) (ha j)) f := by
      rw [hsqrtC]
    _ = ((2 * m j : ℕ) : ℂ) * inner ℂ (expFeature (a j) (ha j)) f := by
      push_cast
      rfl

theorem finiteExponentialHankel_isPositive {r : ℕ} (a : Fin r → ℝ)
    (ha : ∀ j, 0 < a j) (m : Fin r → ℕ) :
    (finiteExponentialHankel a ha m).IsPositive := by
  rw [← finiteExponentialSynthesis_comp_adjoint]
  have h := ContinuousLinearMap.isPositive_adjoint_comp_self
    (finiteExponentialSynthesis a ha m).adjoint
  simpa using h

/-- Positive multiplicity weights preserve independence of distinct exponential rates. -/
theorem linearIndependent_weightedExpFeature {r : ℕ} (a : Fin r → ℝ)
    (ha : ∀ j, 0 < a j) (m : Fin r → ℕ) (hm : ∀ j, 0 < m j)
    (hinj : Function.Injective a) :
    LinearIndependent ℂ (weightedExpFeature a ha m) := by
  let c : Fin r → ℂ := fun j => ((Real.sqrt (2 * (m j : ℝ)) : ℝ) : ℂ)
  have hc : ∀ j, c j ≠ 0 := by
    intro j
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt
      (Real.sqrt_pos.2 (mul_pos (by norm_num) (Nat.cast_pos.mpr (hm j)))))
  have hbase := linearIndependent_expFeature a ha hinj
  let u : Fin r → ℂˣ := fun j => Units.mk0 (c j) (hc j)
  have hscaled : LinearIndependent ℂ
      (fun j => c j • expFeature (a j) (ha j)) := by
    rw [show (fun j => c j • expFeature (a j) (ha j)) =
        u • (fun j => expFeature (a j) (ha j)) by
      funext j
      simp [u, Pi.smul_apply']]
    exact hbase.units_smul u
  change LinearIndependent ℂ
    (fun j => c j • expFeature (a j) (ha j))
  exact hscaled

theorem finiteExponentialSynthesis_injective {r : ℕ} (a : Fin r → ℝ)
    (ha : ∀ j, 0 < a j) (m : Fin r → ℕ) (hm : ∀ j, 0 < m j)
    (hinj : Function.Injective a) :
    Function.Injective (finiteExponentialSynthesis a ha m) := by
  intro c d hcd
  have hLI := linearIndependent_weightedExpFeature a ha m hm hinj
  rw [Fintype.linearIndependent_iff] at hLI
  have hzero : ∑ j, ((c - d) j) • weightedExpFeature a ha m j = 0 := by
    change finiteExponentialSynthesis a ha m (c - d) = 0
    rw [map_sub, hcd, sub_self]
  have hcoord := hLI (fun j => (c - d) j) hzero
  apply sub_eq_zero.mp
  ext j
  exact hcoord j

/-- Distinct positive rates give exactly one Hankel rank per rate. -/
theorem finrank_range_finiteExponentialHankel {r : ℕ} (a : Fin r → ℝ)
    (ha : ∀ j, 0 < a j) (m : Fin r → ℕ) (hm : ∀ j, 0 < m j)
    (hinj : Function.Injective a) :
    Module.finrank ℂ (finiteExponentialHankel a ha m).range = r := by
  rw [← finiteExponentialSynthesis_comp_adjoint]
  rw [finrank_range_comp_adjoint_of_finiteDimensional_domain_injective
    (finiteExponentialSynthesis a ha m)
    (finiteExponentialSynthesis_injective a ha m hm hinj)]
  simp

/-- The exact-rank exponential Hankel operator has rank at most its number of rates. -/
theorem finiteExponentialHankel_hasRankLE {r : ℕ} (a : Fin r → ℝ)
    (ha : ∀ j, 0 < a j) (m : Fin r → ℕ) (hm : ∀ j, 0 < m j)
    (hinj : Function.Injective a) :
    RHTower.HasRankLE (finiteExponentialHankel a ha m) r := by
  refine ⟨(finiteExponentialHankel a ha m).range, ?_, ?_, fun x => ⟨x, rfl⟩⟩
  · rw [← finiteExponentialSynthesis_comp_adjoint,
      range_comp_adjoint_eq_range_of_finiteDimensional_domain_injective
        (finiteExponentialSynthesis a ha m)
        (finiteExponentialSynthesis_injective a ha m hm hinj)]
    infer_instance
  · exact le_of_eq (finrank_range_finiteExponentialHankel a ha m hm hinj)

/-- Every distinct positive finite exponential packet is trace class. -/
theorem finiteExponentialHankel_memSchattenClass_one {r : ℕ} (a : Fin r → ℝ)
    (ha : ∀ j, 0 < a j) (m : Fin r → ℕ) (hm : ∀ j, 0 < m j)
    (hinj : Function.Injective a) :
    RHTower.MemSchattenClass 1 (finiteExponentialHankel a ha m) :=
  RHTower.memSchattenClass_of_hasRankLE one_pos
    (finiteExponentialHankel_hasRankLE a ha m hm hinj)

theorem opTrace_finiteExponentialHankel {r : ℕ} (a : Fin r → ℝ)
    (ha : ∀ j, 0 < a j) (m : Fin r → ℕ) :
    ContinuousLinearMap.opTrace (finiteExponentialHankel a ha m) =
      ∑ j, ((m j : ℕ) : ℂ) / (a j : ℂ) := by
  rw [finiteExponentialHankel]
  have htrace := opTrace_mul_finiteRankProbe_mul
    (H := HalfLineLaplaceL2)
    (ContinuousLinearMap.id ℂ HalfLineLaplaceL2)
    (ContinuousLinearMap.id ℂ HalfLineLaplaceL2)
    (fun j : Fin r => ((2 * m j : ℕ) : ℂ))
    (fun j => expFeature (a j) (ha j))
    (fun j => expFeature (a j) (ha j))
  have hop :
      (ContinuousLinearMap.id ℂ HalfLineLaplaceL2 *
          finiteRankProbe (fun j : Fin r => ((2 * m j : ℕ) : ℂ))
            (fun j => expFeature (a j) (ha j))
            (fun j => expFeature (a j) (ha j)) *
        ContinuousLinearMap.id ℂ HalfLineLaplaceL2) =
          finiteRankProbe (fun j : Fin r => ((2 * m j : ℕ) : ℂ))
            (fun j => expFeature (a j) (ha j))
            (fun j => expFeature (a j) (ha j)) := by
    ext x
    rfl
  rw [hop] at htrace
  rw [htrace]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [ContinuousLinearMap.id_apply]
  rw [inner_expFeature]
  push_cast
  field_simp [ne_of_gt (ha j)]
  ring

/-- Exact diagonal quadratic form of the finite exponential Hankel operator. -/
theorem inner_expFeature_finiteExponentialHankel {r : ℕ} (a : Fin r → ℝ)
    (ha : ∀ j, 0 < a j) (m : Fin r → ℕ) (j : Fin r) :
    inner ℂ (expFeature (a j) (ha j))
        (finiteExponentialHankel a ha m (expFeature (a j) (ha j))) =
      ∑ k, ((2 * m k : ℕ) : ℂ) /
        (((a j : ℂ) + (a k : ℂ)) ^ 2) := by
  rw [finiteExponentialHankel, finiteRankProbe, _root_.sum_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [smul_apply, InnerProductSpace.rankOne_apply, inner_smul_right]
  rw [inner_expFeature, inner_expFeature]
  rw [add_comm (a k : ℂ) (a j : ℂ)]
  simp only [div_eq_mul_inv]
  rw [← inv_pow]
  ring

/-- Real positive Cauchy-Gram form on one exponential test vector. -/
theorem re_inner_expFeature_finiteExponentialHankel {r : ℕ} (a : Fin r → ℝ)
    (ha : ∀ j, 0 < a j) (m : Fin r → ℕ) (j : Fin r) :
    (inner ℂ (expFeature (a j) (ha j))
        (finiteExponentialHankel a ha m (expFeature (a j) (ha j)))).re =
      ∑ k, (2 * (m k : ℝ)) / ((a j + a k) ^ 2) := by
  rw [inner_expFeature_finiteExponentialHankel]
  classical
  let s : Finset (Fin r) := Finset.univ
  change (∑ k ∈ s, ((2 * m k : ℕ) : ℂ) /
      (((a j : ℂ) + (a k : ℂ)) ^ 2)).re =
    ∑ k ∈ s, (2 * (m k : ℝ)) / ((a j + a k) ^ 2)
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk, Complex.add_re, ih]
      congr 1
      have hterm :
          (2 : ℂ) * (m k : ℂ) / (((a j : ℂ) + (a k : ℂ)) ^ 2) =
            (((2 * (m k : ℝ)) / ((a j + a k) ^ 2) : ℝ) : ℂ) := by
        push_cast
        rfl
      have hnat : ((2 * m k : ℕ) : ℂ) = (2 : ℂ) * (m k : ℂ) := by
        push_cast
        rfl
      rw [hnat]
      calc
        ((2 : ℂ) * (m k : ℂ) / (((a j : ℂ) + (a k : ℂ)) ^ 2)).re =
            ((((2 * (m k : ℝ)) / ((a j + a k) ^ 2) : ℝ) : ℂ)).re :=
          congrArg Complex.re hterm
        _ = (2 * (m k : ℝ)) / ((a j + a k) ^ 2) := Complex.ofReal_re _

/-- Exact squared norm of a half-line exponential feature. -/
theorem norm_sq_expFeature {a : ℝ} (ha : 0 < a) :
    ‖expFeature a ha‖ ^ 2 = 1 / (2 * a) := by
  have hinner := inner_expFeature ha ha
  have hc : ((a : ℂ) + (a : ℂ))⁻¹ = (((1 / (2 * a) : ℝ)) : ℂ) := by
    push_cast
    field_simp [ne_of_gt ha]
    ring
  rw [hc] at hinner
  calc
    ‖expFeature a ha‖ ^ 2 =
        (inner ℂ (expFeature a ha) (expFeature a ha)).re := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    _ = 1 / (2 * a) := by simpa using congrArg Complex.re hinner

omit [CompleteSpace H] in
/-- Every bounded operator's diagonal quadratic form is controlled by its operator norm. -/
theorem re_inner_apply_le_opNorm_mul_norm_sq (T : H →L[ℂ] H) (x : H) :
    (inner ℂ x (T x)).re ≤ ‖T‖ * ‖x‖ ^ 2 := by
  calc
    (inner ℂ x (T x)).re ≤ ‖inner ℂ x (T x)‖ := Complex.re_le_norm _
    _ ≤ ‖x‖ * ‖T x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖T‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg x)
    _ = ‖T‖ * ‖x‖ ^ 2 := by ring

/-- A rate-`a j` exponential detects the sharp single-layer norm floor `m j / a j`. -/
theorem multiplicity_div_rate_le_norm_finiteExponentialHankel {r : ℕ}
    (a : Fin r → ℝ) (ha : ∀ j, 0 < a j) (m : Fin r → ℕ) (j : Fin r) :
    (m j : ℝ) / a j ≤ ‖finiteExponentialHankel a ha m‖ := by
  let v := expFeature (a j) (ha j)
  have hlower :
      (2 * (m j : ℝ)) / ((a j + a j) ^ 2) ≤
        (inner ℂ v (finiteExponentialHankel a ha m v)).re := by
    rw [re_inner_expFeature_finiteExponentialHankel]
    have hnonneg : ∀ k : Fin r,
        0 ≤ (2 * (m k : ℝ)) / ((a j + a k) ^ 2) := by
      intro k
      exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (sq_nonneg _)
    exact Finset.single_le_sum
      (fun k _ => hnonneg k)
      (Finset.mem_univ j)
  have hupper :
      (inner ℂ v (finiteExponentialHankel a ha m v)).re ≤
        ‖finiteExponentialHankel a ha m‖ * ‖v‖ ^ 2 :=
    re_inner_apply_le_opNorm_mul_norm_sq _ _
  have hbound := hlower.trans hupper
  have hq : ‖v‖ ^ 2 = 1 / (2 * a j) := norm_sq_expFeature (ha j)
  have hfactor :
      (2 * (m j : ℝ)) / ((a j + a j) ^ 2) =
        ((m j : ℝ) / a j) * ‖v‖ ^ 2 := by
    rw [hq]
    field_simp [ne_of_gt (ha j)]
    ring
  rw [hfactor] at hbound
  have hqpos : 0 < ‖v‖ ^ 2 := by
    rw [hq]
    exact one_div_pos.mpr (mul_pos (by norm_num) (ha j))
  exact le_of_mul_le_mul_right hbound hqpos

end GaloisForLFunctions.HTGeometry
