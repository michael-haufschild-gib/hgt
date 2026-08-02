import GaloisForLFunctions.HTGeometry.QuasiAbelianPatternPacket
import GaloisForLFunctions.HTGeometry.ContinuousPolynomialDefect

/-!
# Coefficient-uniform Baire packets in one automorphic-factor space

All-order jet ampleness now supplies every analytic witness required by the countable decorated-
monomial determinant argument.  No defect locus, escaping section, or empty-interior certificate
is assumed: each is constructed from the actual fixed-factor jet map.
-/

open Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- All translated mixed jets used by one decorated pattern, observed continuously in the fixed
automorphic-factor section space. -/
def automorphicTranslationPatternObservationCLM
    {d : ℕ} {Gamma : AddSubgroup (Fin d → ℂ)}
    (psi : AutomorphicFactor d Gamma) {Lambda : Type u}
    (shift : Lambda → Fin d → ℂ)
    (p : FiniteMultivariateAffineJetPattern Lambda d)
    (base : MultivariateAffinePatternRow p → Fin d → ℂ) :
    psi.forms →L[ℂ]
      (MultivariateAffinePatternRow p × MultivariateAffinePatternJet p → ℂ) :=
  ContinuousLinearMap.pi fun x ↦
    (multiIndexJetEvalCLM
      (base x.1 + shift (p.frameCode x.2.1)) x.2.2.1).comp psi.forms.subtypeL

@[simp]
theorem automorphicTranslationPatternObservationCLM_apply
    {d : ℕ} {Gamma : AddSubgroup (Fin d → ℂ)}
    (psi : AutomorphicFactor d Gamma) {Lambda : Type u}
    (shift : Lambda → Fin d → ℂ)
    (p : FiniteMultivariateAffineJetPattern Lambda d)
    (base : MultivariateAffinePatternRow p → Fin d → ℂ)
    (f : psi.forms)
    (x : MultivariateAffinePatternRow p × MultivariateAffinePatternJet p) :
    automorphicTranslationPatternObservationCLM psi shift p base f x =
      multiIndexJetEvalCLM
        (base x.1 + shift (p.frameCode x.2.1)) x.2.2.1 f.1 :=
  rfl

/-- Polynomial determinant defect for one chosen sample base packet. -/
def automorphicTranslationPatternDefect
    {d : ℕ} {Gamma : AddSubgroup (Fin d → ℂ)}
    (psi : AutomorphicFactor d Gamma) {Lambda : Type u}
    (shift : Lambda → Fin d → ℂ)
    (p : FiniteMultivariateAffineJetPattern Lambda d)
    (base : MultivariateAffinePatternRow p → Fin d → ℂ) : Set psi.forms :=
  {f | MvPolynomial.eval
      (automorphicTranslationPatternObservationCLM psi shift p base f)
      (multivariateCoefficientPatternDeterminant
        base p.coordinateExponent p.jetExponent) = 0}

theorem automorphicTranslationPatternDefect_isClosed
    {d : ℕ} {Gamma : AddSubgroup (Fin d → ℂ)}
    (psi : AutomorphicFactor d Gamma) {Lambda : Type u}
    (shift : Lambda → Fin d → ℂ)
    (p : FiniteMultivariateAffineJetPattern Lambda d)
    (base : MultivariateAffinePatternRow p → Fin d → ℂ) :
    IsClosed (automorphicTranslationPatternDefect psi shift p base) :=
  isClosed_continuousLinearMap_mvPolynomial_zero
    (automorphicTranslationPatternObservationCLM psi shift p base)
    (multivariateCoefficientPatternDeterminant
      base p.coordinateExponent p.jetExponent)

/-- Actual escaping section and its quotient-distinct sample packet for one decorated pattern. -/
structure AutomorphicTranslationPatternWitness
    {d : ℕ} {Gamma : AddSubgroup (Fin d → ℂ)}
    (psi : AutomorphicFactor d Gamma) {Lambda : Type u}
    (shift : Lambda → Fin d → ℂ)
    (p : FiniteMultivariateAffineJetPattern Lambda d) where
  base : MultivariateAffinePatternRow p → Fin d → ℂ
  source : psi.forms
  sample_distinct : PairwiseDistinctModulo Gamma
    (fun q : MultivariateAffinePatternRow p × Fin p.frameCount ↦
      base q.1 + shift (p.frameCode q.2))
  escapes : MvPolynomial.eval
    (automorphicTranslationPatternObservationCLM psi shift p base source)
    (multivariateCoefficientPatternDeterminant
      base p.coordinateExponent p.jetExponent) ≠ 0
  nowhereDense : IsNowhereDense
    (automorphicTranslationPatternDefect psi shift p base)

/-- Fixed-factor all-order jet ampleness constructs an escaping determinant witness for every
finite decorated translation pattern. -/
theorem AutomorphicFactor.nonempty_translationPatternWitness
    {d : ℕ} (hd : 0 < d) {Gamma : AddSubgroup (Fin d → ℂ)}
    [DiscreteTopology Gamma] (psi : AutomorphicFactor d Gamma)
    {Lambda : Type u} (shift : Lambda → Fin d → ℂ)
    (hshift : PairwiseDistinctModulo Gamma shift)
    (hjet : AutomorphicFactor.JetAmpleEveryFiniteOrder.{0} psi)
    (p : FiniteMultivariateAffineJetPattern Lambda d) :
    Nonempty (AutomorphicTranslationPatternWitness psi shift p) := by
  classical
  have hselected : PairwiseDistinctModulo Gamma (fun i ↦ shift (p.frameCode i)) := by
    intro i j hij
    exact hshift (fun h ↦ hij (p.frameCode_injective h))
  obtain ⟨base, target, hfull, hnodes⟩ :=
    exists_fullRank_multivariateTranslatedMonomial_packet_distinctModulo
      hd Gamma (fun i ↦ shift (p.frameCode i)) hselected p.orders
      p.coordinateExponent p.jetExponent p.decoratedExponent_injective
  let packetPoint :
      MultivariateAffinePatternRow p × Fin p.frameCount → Fin d → ℂ :=
    fun q ↦ base q.1 + shift (p.frameCode q.2)
  let packetOrder :
      MultivariateAffinePatternRow p × Fin p.frameCount → ℕ :=
    fun q ↦ p.orders q.2 + 1
  let desired : FiniteJetPacketIndex d
      (MultivariateAffinePatternRow p × Fin p.frameCount) packetOrder → ℂ :=
    fun q ↦
      if ha : Finsupp.degree q.2.1 < p.orders q.1.2 then
        target q.1.1 ⟨q.1.2, ⟨q.2.1, ha⟩⟩
      else 0
  obtain ⟨source, hsource⟩ := hjet
    (MultivariateAffinePatternRow p × Fin p.frameCount)
    packetPoint packetOrder hnodes (fun q ↦ Nat.succ_pos _)
    desired
  have hobservation :
      automorphicTranslationPatternObservationCLM psi shift p base source =
        fun x ↦ target x.1 x.2 := by
    funext x
    let q : FiniteJetPacketIndex d
        (MultivariateAffinePatternRow p × Fin p.frameCount) packetOrder :=
      ⟨(x.1, x.2.1),
        ⟨x.2.2.1, lt_trans x.2.2.2 (Nat.lt_succ_self _)⟩⟩
    have hq := congrFun hsource q
    simpa [AutomorphicFactor.jetPacketLinearMap_apply, packetPoint, packetOrder,
      desired, q, x.2.2.2] using hq
  have hescapes : MvPolynomial.eval
      (automorphicTranslationPatternObservationCLM psi shift p base source)
      (multivariateCoefficientPatternDeterminant
        base p.coordinateExponent p.jetExponent) ≠ 0 := by
    rw [hobservation, eval_multivariateCoefficientPatternDeterminant]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hfull).ne_zero
  have hnowhere : IsNowhereDense
      (automorphicTranslationPatternDefect psi shift p base) := by
    change IsNowhereDense {f : psi.forms | MvPolynomial.eval
      (automorphicTranslationPatternObservationCLM psi shift p base f)
      (multivariateCoefficientPatternDeterminant
        base p.coordinateExponent p.jetExponent) = 0}
    exact isNowhereDense_continuousLinearMap_mvPolynomial_zero_of_witness
      (X := psi.forms)
      (σ := MultivariateAffinePatternRow p × MultivariateAffinePatternJet p)
      (automorphicTranslationPatternObservationCLM psi shift p base)
      (multivariateCoefficientPatternDeterminant
        base p.coordinateExponent p.jetExponent)
      source hescapes
  exact ⟨⟨base, source, hnodes, hescapes, hnowhere⟩⟩

/-- Canonical choice of the finite-pattern witness supplied by all-order jet ampleness. -/
noncomputable def AutomorphicFactor.translationPatternWitness
    {d : ℕ} (hd : 0 < d) {Gamma : AddSubgroup (Fin d → ℂ)}
    [DiscreteTopology Gamma] (psi : AutomorphicFactor d Gamma)
    {Lambda : Type u} (shift : Lambda → Fin d → ℂ)
    (hshift : PairwiseDistinctModulo Gamma shift)
    (hjet : AutomorphicFactor.JetAmpleEveryFiniteOrder.{0} psi)
    (p : FiniteMultivariateAffineJetPattern Lambda d) :
    AutomorphicTranslationPatternWitness psi shift p :=
  (psi.nonempty_translationPatternWitness hd shift hshift hjet p).some

/-- Sections simultaneously avoiding all coefficient-uniform decorated translation defects. -/
def automorphicTranslationPatternResidualSet
    {d : ℕ} {Gamma : AddSubgroup (Fin d → ℂ)}
    (psi : AutomorphicFactor d Gamma) {Lambda : Type u}
    (shift : Lambda → Fin d → ℂ)
    (witness : ∀ p : FiniteMultivariateAffineJetPattern Lambda d,
      AutomorphicTranslationPatternWitness psi shift p) : Set psi.forms :=
  {f | ∀ p, f ∉ automorphicTranslationPatternDefect psi shift p (witness p).base}

/-- Any supplied escaping witness for every finite pattern yields the dense residual avoidance
set.  Keeping this Baire assembly abstract prevents the witness choice from being unfolded during
the topological proof. -/
theorem automorphicTranslationPatternResidualSet_dense_residual_of_witness
    {d : ℕ} {Gamma : AddSubgroup (Fin d → ℂ)}
    (psi : AutomorphicFactor d Gamma) {Lambda : Type u} [Countable Lambda]
    (shift : Lambda → Fin d → ℂ)
    (witness : ∀ p : FiniteMultivariateAffineJetPattern Lambda d,
      AutomorphicTranslationPatternWitness psi shift p) :
    Dense (automorphicTranslationPatternResidualSet psi shift witness) ∧
      automorphicTranslationPatternResidualSet psi shift witness ∈ residual psi.forms := by
  let D : FiniteMultivariateAffineJetPattern Lambda d → Set psi.forms :=
    fun p ↦ automorphicTranslationPatternDefect psi shift p (witness p).base
  have hclosed : ∀ p, IsClosed (D p) := fun p ↦
    automorphicTranslationPatternDefect_isClosed psi shift p (witness p).base
  have hnowhere : ∀ p, IsNowhereDense (D p) := by
    intro p
    exact (witness p).nowhereDense
  have hset : automorphicTranslationPatternResidualSet psi shift witness =
      ⋂ p, (D p)ᶜ := by
    ext f
    simp [automorphicTranslationPatternResidualSet, D]
  change Dense (automorphicTranslationPatternResidualSet psi shift witness) ∧
    automorphicTranslationPatternResidualSet psi shift witness ∈ residual psi.forms
  rw [hset]
  exact ⟨dense_iInter_of_isOpen (fun p ↦ (hclosed p).isOpen_compl)
      (fun p ↦ interior_eq_empty_iff_dense_compl.mp
        ((hclosed p).isNowhereDense_iff.mp (hnowhere p))),
    countable_iInter_mem.mpr (fun p ↦ (hnowhere p).isMeagre)⟩

/-- **Fixed-factor coefficient-uniform Baire law.**  For a countable quotient-distinct translation
palette, all-order jet ampleness produces a dense residual set of sections avoiding every finite
decorated-monomial determinant defect. -/
theorem AutomorphicFactor.translationPatternResidualSet_dense_residual
    {d : ℕ} (hd : 0 < d) {Gamma : AddSubgroup (Fin d → ℂ)}
    [DiscreteTopology Gamma] (psi : AutomorphicFactor d Gamma)
    {Lambda : Type u} [Countable Lambda]
    (shift : Lambda → Fin d → ℂ)
    (hshift : PairwiseDistinctModulo Gamma shift)
    (hjet : AutomorphicFactor.JetAmpleEveryFiniteOrder.{0} psi) :
    let witness := fun p : FiniteMultivariateAffineJetPattern Lambda d ↦
      psi.translationPatternWitness hd shift hshift hjet p
    Dense (automorphicTranslationPatternResidualSet psi shift witness) ∧
      automorphicTranslationPatternResidualSet psi shift witness ∈ residual psi.forms := by
  exact automorphicTranslationPatternResidualSet_dense_residual_of_witness psi shift
    (fun p ↦ psi.translationPatternWitness hd shift hshift hjet p)

/-- Avoiding a pattern defect excludes every complex coefficient relation on its complete
decorated-monomial support. -/
theorem coefficients_eq_zero_of_mem_automorphicTranslationPatternResidualSet
    {d : ℕ} {Gamma : AddSubgroup (Fin d → ℂ)}
    {psi : AutomorphicFactor d Gamma} {Lambda : Type u}
    {shift : Lambda → Fin d → ℂ}
    {witness : ∀ p : FiniteMultivariateAffineJetPattern Lambda d,
      AutomorphicTranslationPatternWitness psi shift p}
    {f : psi.forms}
    (hf : f ∈ automorphicTranslationPatternResidualSet psi shift witness)
    (p : FiniteMultivariateAffineJetPattern Lambda d)
    (c : MultivariateAffinePatternRow p → ℂ)
    (hrelation : ∀ z : Fin d → ℂ,
      ∑ b, c b *
        (multivariateCoordinateMonomial (p.coordinateExponent b) z *
          (p.jetExponent b).prod (fun q e ↦
            multiIndexJetEvalCLM
              (z + shift (p.frameCode q.1)) q.2.1 f.1 ^ e)) = 0) :
    ∀ b, c b = 0 := by
  have hdet :
      (Matrix.of fun a b ↦
        multivariateCoordinateMonomial (p.coordinateExponent b) ((witness p).base a) *
          (p.jetExponent b).prod (fun q e ↦
            multiIndexJetEvalCLM
              ((witness p).base a + shift (p.frameCode q.1)) q.2.1 f.1 ^ e) :
        Matrix (MultivariateAffinePatternRow p)
          (MultivariateAffinePatternRow p) ℂ).det ≠ 0 := by
    have havoid := hf p
    rw [automorphicTranslationPatternDefect, Set.mem_setOf_eq,
      eval_multivariateCoefficientPatternDeterminant] at havoid
    exact havoid
  apply coefficients_eq_zero_of_fullRank_evaluation_packet
    (fun b z ↦
      multivariateCoordinateMonomial (p.coordinateExponent b) z *
        (p.jetExponent b).prod (fun q e ↦
          multiIndexJetEvalCLM (z + shift (p.frameCode q.1)) q.2.1 f.1 ^ e))
    (witness p).base
  · rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hdet
  · exact fun a ↦ hrelation ((witness p).base a)

end

end GaloisForLFunctions.HTGeometry
