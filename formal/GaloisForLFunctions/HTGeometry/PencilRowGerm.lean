import GaloisForLFunctions.HTGeometry.PencilRowCarrier
import GaloisForLFunctions.HTGeometry.PencilStanleyReisnerMatroid

/-!
# The operator row of a pencil orbit, in the meromorphic field

Reading the coordinate packet of a Stanley--Reisner Laurent family in the several-variable
meromorphic field turns the row sum into the germ of the operator applied to the source: the
derivation jets of a germ are the germs of the iterated directional derivatives, and the germ map is
additive and commutes with complex scalars.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Bottcher
open scoped Classical Differential

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### The germ of an entire function in the meromorphic field -/

/-- The germ of an entire function in the several-variable meromorphic field. -/
def entireGerm (f : E → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ) :
    meroFieldGen (Set.univ : Set E) :=
  algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E))
    (entireGermGen f hf)

theorem entireGerm_add (f g : E → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ) (hfg : AnalyticOnNhd ℂ (fun z => f z + g z) Set.univ) :
    entireGerm (fun z => f z + g z) hfg = entireGerm f hf + entireGerm g hg := by
  rw [entireGerm, entireGerm, entireGerm, ← map_add]
  exact congrArg (algebraMap (analyticSubringGen (Set.univ : Set E))
    (meroFieldGen (Set.univ : Set E))) (entireGermGen_add f g hf hg)

theorem entireGerm_zero (h : AnalyticOnNhd ℂ (fun _ : E => (0 : ℂ)) Set.univ) :
    entireGerm (fun _ : E => (0 : ℂ)) h = 0 := by
  rw [entireGerm, show entireGermGen (fun _ : E => (0 : ℂ)) h = 0 from
    (entireGermGen_eq_zero_iff _ h).mpr fun _ => rfl, map_zero]

theorem entireGerm_const_mul (a : ℂ) (f : E → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ)
    (haf : AnalyticOnNhd ℂ (fun z => a * f z) Set.univ) :
    entireGerm (fun z => a * f z) haf
      = algebraMap ℂ (meroFieldGen (Set.univ : Set E)) a * entireGerm f hf := by
  have hconst : algebraMap ℂ (meroFieldGen (Set.univ : Set E)) a
      = algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E))
        (constToAnalyticGen (Set.univ : Set E) a) := by
    rw [IsScalarTower.algebraMap_apply ℂ (analyticSubringGen (Set.univ : Set E))
      (meroFieldGen (Set.univ : Set E))]
    rfl
  rw [entireGerm, entireGerm, hconst, ← map_mul]
  refine congrArg (algebraMap (analyticSubringGen (Set.univ : Set E))
    (meroFieldGen (Set.univ : Set E))) ?_
  rw [← entireGermGen_const (E := E) a]
  exact entireGermGen_mul (fun _ => a) f analyticOnNhd_const hf

theorem entireGerm_congr (f g : E → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ) (h : f = g) : entireGerm f hf = entireGerm g hg := by
  subst h
  rfl

theorem entireGerm_finset_sum {κ : Type*} (s : Finset κ) (f : κ → E → ℂ)
    (hf : ∀ k, AnalyticOnNhd ℂ (f k) Set.univ)
    (hs : AnalyticOnNhd ℂ (fun z => ∑ k ∈ s, f k z) Set.univ) :
    entireGerm (fun z => ∑ k ∈ s, f k z) hs = ∑ k ∈ s, entireGerm (f k) (hf k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, entireGerm_congr (fun z => ∑ k ∈ (∅ : Finset κ), f k z)
        (fun _ : E => (0 : ℂ)) hs analyticOnNhd_const (by funext z; rw [Finset.sum_empty]),
        entireGerm_zero]
  | insert a s ha ih =>
      have hsum : AnalyticOnNhd ℂ (fun z => ∑ k ∈ s, f k z) Set.univ :=
        Finset.analyticOnNhd_fun_sum s fun k _ => hf k
      have hadd : AnalyticOnNhd ℂ (fun z => f a z + ∑ k ∈ s, f k z) Set.univ := (hf a).add hsum
      rw [entireGerm_congr (fun z => ∑ k ∈ insert a s, f k z)
          (fun z => f a z + ∑ k ∈ s, f k z) hs hadd (by funext z; rw [Finset.sum_insert ha]),
        entireGerm_add (f a) (fun z => ∑ k ∈ s, f k z) (hf a) hsum hadd, ih hsum,
        Finset.sum_insert ha]

/-! ### Analyticity of a carrier -/

variable {α : Type} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
theorem analyticOnNhd_seedCarrierPoly (ω : α → E) {G : E → ℂ}
    (hG : AnalyticOnNhd ℂ G Set.univ) (P : MvPolynomial α ℂ) :
    AnalyticOnNhd ℂ (seedCarrierPoly ω G P) Set.univ := by
  have hfun : seedCarrierPoly ω G P
      = fun z => ∑ e ∈ (differenceToTranslationHom P).support,
        MvPolynomial.coeff e (differenceToTranslationHom P) * G (z + translationAddHom ω e) := by
    funext z
    exact seedCarrierPoly_apply_translation ω G P z
  rw [hfun]
  refine Finset.analyticOnNhd_fun_sum _ fun e _ => ?_
  exact analyticOnNhd_const.mul (analyticOnNhd_comp_add_const G hG _)

/-! ### The derivation of a finite sum -/

omit [Fintype α] [DecidableEq α] in
theorem dirDerivFun_finset_sum (w : E) {κ : Type*} (s : Finset κ) {f : κ → E → ℂ}
    (hf : ∀ k ∈ s, Differentiable ℂ (f k)) :
    dirDerivFun w (fun z => ∑ k ∈ s, f k z) = fun z => ∑ k ∈ s, dirDerivFun w (f k) z := by
  funext z
  show fderiv ℂ (fun y => ∑ k ∈ s, f k y) z w = ∑ k ∈ s, dirDerivFun w (f k) z
  rw [fderiv_fun_sum (fun k hk => (hf k hk z))]
  exact sum_apply _ _ w

omit [Fintype α] [DecidableEq α] in
/-- **The iterated derivation of a finite sum.** -/
theorem dirDerivFun_iterate_finset_sum (w : E) (r : ℕ) {κ : Type*} (s : Finset κ)
    {f : κ → E → ℂ} (hf : ∀ k ∈ s, AnalyticOnNhd ℂ (f k) Set.univ) :
    (dirDerivFun w)^[r] (fun z => ∑ k ∈ s, f k z)
      = fun z => ∑ k ∈ s, ((dirDerivFun w)^[r] (f k)) z := by
  induction r generalizing f with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply,
        dirDerivFun_finset_sum w s (fun k hk => fun x => ((hf k hk) x (Set.mem_univ x)).differentiableAt),
        ih (fun k hk => analyticOnNhd_dirDerivFun w (hf k hk))]
      funext z
      exact Finset.sum_congr rfl fun k _ => by rw [Function.iterate_succ_apply]

/-! ### The row of a pencil orbit -/

variable {d : ℕ} {facets : Finset (Finset α)} {ι : Type} [Fintype ι]

omit [Fintype α] [DecidableEq α] in
theorem analyticOnNhd_opCarrier (w : Fin d → ℂ) (ω : α → (Fin d → ℂ))
    {F : (Fin d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F Set.univ) (n : ℕ) (Q : ℕ → MvPolynomial α ℂ) :
    AnalyticOnNhd ℂ (opCarrier w ω F n Q) Set.univ :=
  Finset.analyticOnNhd_fun_sum _ fun r _ =>
    analyticOnNhd_seedCarrierPoly ω (analyticOnNhd_dirDerivFun_iterate w hF r) (Q r)

omit [Fintype α] [DecidableEq α] in
theorem analyticOnNhd_opCarrier_sub (w : Fin d → ℂ) (ω : α → (Fin d → ℂ))
    {F : (Fin d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F Set.univ) (n : ℕ) (Q : ℕ → MvPolynomial α ℂ)
    (τ : Fin d → ℂ) :
    AnalyticOnNhd ℂ (fun z => opCarrier w ω F n Q (z - τ)) Set.univ := by
  have h := analyticOnNhd_comp_add_const (opCarrier w ω F n Q)
    (analyticOnNhd_opCarrier w ω hF n Q) (-τ)
  simpa only [← sub_eq_add_neg] using h

omit [Fintype ι] in
/-- The row coefficients above the operator degree vanish. -/
theorem coeff_stanleyReisnerLaurentRows_opPoly_eq_zero
    (dd : translationSubmonoid (Polynomial ℂ) α) (n : ℕ) (Q : ι → ℕ → MvPolynomial α ℂ)
    (i : ι) (A : facets) (g : α → ℤ) {r : ℕ} (hr : r ∉ Finset.range n) :
    Polynomial.coeff (stanleyReisnerLaurentRows dd facets
      (fun j => Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets)
        (opPoly n (Q j))) i A g) r = 0 := by
  classical
  have hrow : stanleyReisnerLaurentRows dd facets
      (fun j => Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets)
        (opPoly n (Q j))) i A
      = facetLaurentShift dd A.1 (differenceToTranslationHom
        (opPoly n (fun s => facetRestrict A.1 (Q i s)))) := by
    show facetLaurentShift dd A.1
      (stanleyReisnerFacetTranslationCoordinates facets
        (Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets) (opPoly n (Q i))) A) = _
    rw [stanleyReisnerFacetTranslationCoordinates_mk, facetRestrict_opPoly]
  rw [hrow, facetLaurentShift]
  by_cases hg : g ∈ Set.range (facetLaurentExponentShift dd A.1)
  · obtain ⟨e, rfl⟩ := hg
    rw [Finsupp.mapDomain_apply (facetLaurentExponentShift_injective dd A.1)]
    show Polynomial.coeff (MvPolynomial.coeff e (differenceToTranslationHom
      (opPoly n (fun s => facetRestrict A.1 (Q i s))))) r = 0
    rw [coeff_differenceToTranslationHom_opPoly, if_neg hr]
  · rw [Finsupp.mapDomain_notin_range _ _ hg, Polynomial.coeff_zero]

set_option maxHeartbeats 4000000 in
/-- **The operator row of a pencil orbit is the germ of the operator applied to the source.**
Summing the Stanley--Reisner Laurent rows of `∑_r δ^r Q_r` against the orbit of the facet sources
gives the germ of that operator applied to the sum of the facet sources, translated by the common
denominator. -/
theorem differentialOperatorRowApply_eq_entireGerm_opCarrier
    (w : Fin d → ℂ) (ω : α → (Fin d → ℂ)) (Y : facets → (Fin d → ℂ) → ℂ)
    (hYa : ∀ A, AnalyticOnNhd ℂ (Y A) Set.univ)
    (hYp : ∀ (A : facets), ∀ v ∉ A.1, ∀ z, Y A (z + ω v) = Y A z)
    (dd : translationSubmonoid (Polynomial ℂ) α)
    (n : ℕ) (Q : ι → ℕ → MvPolynomial α ℂ) (i : ι) :
    letI := meroFieldGenDirDifferential w (isOpen_univ (X := Fin d → ℂ))
      isPreconnected_univ_gen Set.univ_nonempty
    differentialOperatorRowApply
        (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows dd facets
          (fun j => Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets)
            (opPoly n (Q j)))))
        (fun q => entireGerm (fun z => Y q.1.1 (z + intTranslation ω q.1.2))
          (analyticOnNhd_comp_add_const _ (hYa q.1.1) _)) i
      = entireGerm
          (fun z => opCarrier w ω (fun y => ∑ A : facets, Y A y) n (Q i)
            (z - ∑ v, (translationDenominatorExponent dd v : ℤ) • ω v))
          (analyticOnNhd_opCarrier_sub w ω
            (Finset.analyticOnNhd_fun_sum _ fun A _ => hYa A) n (Q i) _) := by
  classical
  letI := meroFieldGenDirDifferential w (isOpen_univ (X := Fin d → ℂ))
    isPreconnected_univ_gen Set.univ_nonempty
  set Rows := stanleyReisnerLaurentRows dd facets
    (fun j => Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets)
      (opPoly n (Q j))) with hRowsdef
  set H : ℕ → facets → (Fin d → ℂ) → ℂ := fun r A => (dirDerivFun w)^[r] (Y A) with hHdef
  have hHa : ∀ r A, AnalyticOnNhd ℂ (H r A) Set.univ := fun r A =>
    analyticOnNhd_dirDerivFun_iterate w (hYa A) r
  have hHp : ∀ (r : ℕ) (A : facets), ∀ v ∉ A.1, ∀ z, H r A (z + ω v) = H r A z := by
    intro r A v hv z
    have hfun : (fun y => Y A (y + ω v)) = Y A := by funext y; exact hYp A v hv y
    have hiter := dirDerivFun_iterate_comp_add_const w (ω v) (Y A) r
    rw [hfun] at hiter
    exact (congrFun hiter z).symm
  set xq : FiniteFinsuppRowIndex Rows → meroFieldGen (Set.univ : Set (Fin d → ℂ)) :=
    fun q => entireGerm (fun z => Y q.1.1 (z + intTranslation ω q.1.2))
      (analyticOnNhd_comp_add_const _ (hYa q.1.1) _) with hxq
  have hjet : ∀ (q : FiniteFinsuppRowIndex Rows) (r : ℕ),
      differentialJet r (xq q)
        = entireGerm (fun z => H r q.1.1 (z + intTranslation ω q.1.2))
          (analyticOnNhd_comp_add_const _ (hHa r q.1.1) _) := by
    intro q r
    have hbeta : xq q = entireGerm (fun z => Y q.1.1 (z + intTranslation ω q.1.2))
        (analyticOnNhd_comp_add_const _ (hYa q.1.1) _) := rfl
    rw [hbeta, entireGerm, differentialJet_entireGermGen]
    exact entireGerm_congr _ _ _ _
      (dirDerivFun_iterate_comp_add_const w (intTranslation ω q.1.2) (Y q.1.1) r)
  have hrange : ∀ (A : facets) (g : α → ℤ), (Rows i A g).support ⊆ Finset.range n := by
    intro A g m hm
    by_contra hmr
    exact (Polynomial.mem_support_iff.mp hm)
      (coeff_stanleyReisnerLaurentRows_opPoly_eq_zero dd n Q i A g hmr)
  have hterm : ∀ q : FiniteFinsuppRowIndex Rows,
      differentialOperatorApply (finiteFinsuppOperatorRows Rows i q) (xq q)
        = ∑ r ∈ Finset.range n,
          algebraMap ℂ (meroFieldGen (Set.univ : Set (Fin d → ℂ)))
            (Polynomial.coeff (Rows i q.1.1 q.1.2) r) * differentialJet r (xq q) := by
    intro q
    show (Rows i q.1.1 q.1.2).sum
        (fun m c => algebraMap ℂ (meroFieldGen (Set.univ : Set (Fin d → ℂ))) c
          * differentialJet m (xq q)) = _
    rw [Polynomial.sum]
    exact Finset.sum_subset (hrange q.1.1 q.1.2) fun m _ hm => by
      rw [Polynomial.notMem_support_iff.mp hm, map_zero, zero_mul]
  have hqa : ∀ q : FiniteFinsuppRowIndex Rows,
      AnalyticOnNhd ℂ (fun z => ∑ r ∈ Finset.range n,
        Polynomial.coeff (Rows i q.1.1 q.1.2) r * H r q.1.1 (z + intTranslation ω q.1.2))
        Set.univ := fun q => Finset.analyticOnNhd_fun_sum _ fun r _ =>
          analyticOnNhd_const.mul (analyticOnNhd_comp_add_const _ (hHa r q.1.1) _)
  have hcomb : ∀ q : FiniteFinsuppRowIndex Rows,
      differentialOperatorApply (finiteFinsuppOperatorRows Rows i q) (xq q)
        = entireGerm (fun z => ∑ r ∈ Finset.range n,
            Polynomial.coeff (Rows i q.1.1 q.1.2) r * H r q.1.1 (z + intTranslation ω q.1.2))
          (hqa q) := by
    intro q
    rw [hterm q, entireGerm_finset_sum (Finset.range n)
      (fun r z => Polynomial.coeff (Rows i q.1.1 q.1.2) r
        * H r q.1.1 (z + intTranslation ω q.1.2))
      (fun r => analyticOnNhd_const.mul (analyticOnNhd_comp_add_const _ (hHa r q.1.1) _)) (hqa q)]
    exact Finset.sum_congr rfl fun r _ => by
      rw [hjet q r, entireGerm_const_mul]
  have hbig : AnalyticOnNhd ℂ (fun z => ∑ q : FiniteFinsuppRowIndex Rows,
      ∑ r ∈ Finset.range n,
        Polynomial.coeff (Rows i q.1.1 q.1.2) r * H r q.1.1 (z + intTranslation ω q.1.2))
      Set.univ := Finset.analyticOnNhd_fun_sum _ fun q _ => hqa q
  show ∑ q : FiniteFinsuppRowIndex Rows,
      differentialOperatorApply (finiteFinsuppOperatorRows Rows i q) (xq q) = _
  rw [Finset.sum_congr rfl (fun q (_ : q ∈ Finset.univ) => hcomb q),
    ← entireGerm_finset_sum Finset.univ _ hqa hbig]
  refine entireGerm_congr _ _ _ _ (funext fun z => ?_)
  rw [rowSum_eq_seedCarrier_sum ω H hHp dd n Q i z, opCarrier]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  exact (dirDerivFun_iterate_finset_sum w r Finset.univ fun A _ => hYa A).symm

end

end GaloisForLFunctions.HTGeometry
