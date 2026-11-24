import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedOriginTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RationalValueDenominators

/-! A section supported at one fibre point clears finitely many local
denominators while preserving their prescribed values there. -/

noncomputable section

open GlobalTheory.WH

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [IsAlgClosed k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}
  {ι : Type*} [Fintype ι]

omit [IsAlgClosed k] in
private theorem algHom_eq_of_coordinateValues {A : Type} [CommRing A] [Algebra k A]
    (f : MvPolynomial (Fin d) k ≃ₐ[k] A) (u v : A →ₐ[k] k)
    (h : ∀ j, u (f (MvPolynomial.X j)) = v (f (MvPolynomial.X j))) : u = v := by
  have hcomp : u.comp f.toAlgHom = v.comp f.toAlgHom := MvPolynomial.algHom_ext h
  apply AlgHom.ext
  intro a
  obtain ⟨b, rfl⟩ := f.surjective a
  exact AlgHom.congr_fun hcomp b

omit [IsAlgClosed k] [Fintype ι] in
/-- An origin fibre point restricts to evaluation at the origin on the
polynomial chart. -/
theorem originEval_comp_chart (h : IsPd k x) (e : OriginFibrePoint k E x) :
    e.1.comp (IsScalarTower.toAlgHom k (rA k x {0}) (integralClosure (rA k x {0}) E)) = originEval h := by
  let f := h.chartPolynomialEquiv 0
  let i : rA k x {0} →ₐ[k] rB k E x {0} :=
    IsScalarTower.toAlgHom k (rA k x {0}) (integralClosure (rA k x {0}) E)
  change e.1.comp i = originEval h
  apply algHom_eq_of_coordinateValues f
  intro j
  have hj : i (f (MvPolynomial.X j)) = ⟨_, tco_mem k E x j⟩ := by
    apply Subtype.ext
    change algebraMap F E (f (MvPolynomial.X j) : F) = _
    rw [h.chartPolynomialEquiv_X]
    simp [chartCoordinates]
  change e.1 (i (f (MvPolynomial.X j))) =
    MvPolynomial.aeval (fun _ : Fin d => (0 : k)) (f.symm (f (MvPolynomial.X j)))
  rw [hj, e.2 j, f.symm_apply_apply, MvPolynomial.aeval_X]

open Classical in
/-- Every finite family of rational functions regular at a fibre point
can be multiplied by a single normalized section to specialize only
at that point. -/
theorem IsFinCover.exists_fibreSupportedCoefficients (h : IsFinCover k E x)
    [IsReduced ((rB k E x {0}) ⧸ originIdeal k E x)]
    (e : OriginFibrePoint k E x) (g : ι → E) (γ : ι → k)
    (hg : ∀ j, Val (rB k E x {0}) e.1 (g j) (γ j)) :
    ∃ (a : rB k E x {0}) (u : ι → rB k E x {0}),
      e.1 a = 1 ∧ (∀ j, (u j : E) = (a : E) * g j) ∧
      ∀ e' : OriginFibrePoint k E x, ∀ j, e'.1 (u j) =
        if e' = e then γ j else 0 := by
  classical
  let B := rB k E x {0}
  choose b hb hbg hb0 hval using hg
  let D (j : ι) : B := ⟨b j, hb j⟩
  let N (j : ι) : B := ⟨b j * g j, hbg j⟩
  let D₀ := ∏ j, D j
  let N₀ (j : ι) := (∏ l ∈ Finset.univ.erase j, D l) * N j
  have hprod (j : ι) : (∏ l ∈ Finset.univ.erase j, D l) * D j = D₀ :=
    Finset.prod_erase_mul _ _ (Finset.mem_univ j)
  have hcoef (j : ι) : (N₀ j : E) = (D₀ : E) * g j := by
    change ((∏ l ∈ Finset.univ.erase j, D l : B) : E) * (b j * g j) = _
    rw [← mul_assoc, ← show ((∏ l ∈ Finset.univ.erase j, D l : B) : E) * b j =
      (D₀ : E) from congrArg Subtype.val (hprod j)]
  have hecoef (j : ι) : e.1 (N₀ j) = e.1 D₀ * γ j := by
    dsimp only [N₀]
    rw [map_mul, show e.1 (N j) = e.1 (D j) * γ j from hval j, ← mul_assoc,
      ← map_mul, hprod]
  have hd : e.1 D₀ ≠ 0 := by
    dsimp only [D₀]
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => hb0 j
  obtain ⟨χ, hχ⟩ := (trace_originFibre h).2.1 (fun e' => if e' = e then (1 : k) else 0)
  have hχ' (e' : OriginFibrePoint k E x) : e'.1 χ = if e' = e then 1 else 0 :=
    congrFun hχ e'
  let a₀ := algebraMap k B (e.1 D₀)⁻¹ * χ
  have ha₀ (e' : OriginFibrePoint k E x) :
      e'.1 a₀ = (e.1 D₀)⁻¹ * (if e' = e then 1 else 0) := by
    dsimp only [a₀]
    rw [map_mul, AlgHom.commutes, hχ']
    simp
  refine ⟨a₀ * D₀, fun j => a₀ * N₀ j, ?_, ?_, ?_⟩
  · rw [map_mul, ha₀, if_pos rfl, mul_one, inv_mul_cancel₀ hd]
  · intro j
    change (a₀ : E) * (N₀ j : E) = (a₀ : E) * (D₀ : E) * g j
    rw [hcoef, mul_assoc]
  · intro e' j
    rw [map_mul, ha₀]
    by_cases he : e' = e
    · subst e'
      simp only [if_true, mul_one]
      rw [hecoef, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
    · simp only [if_neg he, mul_zero, zero_mul]

open Classical in
/-- The trace of such a section specializes to its single supported
value at the origin. -/
theorem IsFinCover.residue_trace_fibreSupportedCoefficients (h : IsFinCover k E x)
    [IsReduced ((rB k E x {0}) ⧸ originIdeal k E x)]
    (e : OriginFibrePoint k E x) (ρ : F →ₗ[k] k) (hρ : IsRes x ρ)
    (u : rB k E x {0}) (a : k)
    (hu : ∀ e' : OriginFibrePoint k E x, e'.1 u = if e' = e then a else 0) :
    ρ (Algebra.trace F E u) = a := by
  classical
  rw [h.residue_trace_origin ρ hρ]
  exact (finsum_eq_single (fun e' : OriginFibrePoint k E x => e'.1 u) e
    (fun e' he' => (hu e').trans (if_neg he'))).trans ((hu e).trans (if_pos rfl))

omit [IsAlgClosed k] [Fintype ι] in
/-- The trace of an integral section has the value of its Laurent
constant coefficient at every point above the origin. -/
theorem IsFinCover.val_trace_origin (h : IsFinCover k E x)
    (e : OriginFibrePoint k E x) (ρ : F →ₗ[k] k) (hρ : IsRes x ρ)
    (u : rB k E x {0}) :
    Val (rB k E x {0}) e.1
      (algebraMap F E (Algebra.trace F E u)) (ρ (Algebra.trace F E u)) := by
  let A := rA k x {0}
  let B := integralClosure A E
  letI : IsIntegrallyClosed (MvPolynomial (Fin d) k) :=
    UpperTheory.Cb.isIntegrallyClosed_fin_polynomialRing k d
  letI : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv (h.pd.chartPolynomialEquiv 0).toRingEquiv
  letI : IsFractionRing A F := h.pd.isFractionRing_rA 0
  letI : Module.Finite F E := h.fin
  have hu : IsIntegral A (Algebra.trace F E (u : E)) :=
    Algebra.isIntegral_trace (L := F) u.2
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A)).mp hu
  change (a : F) = Algebra.trace F E (u : E) at ha
  rw [← ha]
  let b : B := algebraMap A B a
  have hb : e.1 b = ρ a :=
    (AlgHom.congr_fun (originEval_comp_chart h.pd e) a).trans
      (res_eq_originEval h.pd ρ hρ a).symm
  have hm : 1 * algebraMap F E (a : F) ∈ rB k E x {0} := by
    rw [one_mul]
    exact b.2
  refine ⟨1, one_mem _, hm, ?_, ?_⟩
  · exact (map_one e.1).trans_ne zero_ne_one.symm
  · have he : (⟨1 * algebraMap F E (a : F), hm⟩ : rB k E x {0}) = b :=
      Subtype.ext (one_mul _)
    rw [he, hb]
    change ρ (a : F) = e.1 (1 : rB k E x {0}) * ρ (a : F)
    rw [map_one, one_mul]

end GlobalTheory.PD
