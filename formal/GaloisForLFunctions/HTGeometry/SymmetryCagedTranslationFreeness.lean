import GaloisForLFunctions.HTGeometry.FixedDivisorTranslationFreeness
import GaloisForLFunctions.HTGeometry.SymmetricGaugeSpace
import GaloisForLFunctions.HTGeometry.SymmetricRowPacketAtlas

/-!
# Full complex translation freeness inside the symmetry cage

A gauged source `W·exp(g)` with `g` obeying the functional equation, Schwarz reality, and a
prescribed finite jet passport keeps the divisor of `W`, both symmetries, and the passport.  This
module runs the compact-patch codimension argument inside that constraint space: the symmetric
passport probe is still onto the jets at a node with a free symmetry orbit, so densely many
constrained gauges have full expanded-evaluation rank at every shift of a compact patch.

Baire over a compact exhaustion of the shift configuration space, and then over the countable set of
finite differential patterns, gives one dense residual set of constrained gauges whose entire
uncountable complex translation orbit is differentially algebraically independent.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology
open ClassicalAnalyticNevanlinnaCarrierFamily

noncomputable section

variable {row κ ι : Type} [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
  [Fintype ι] [DecidableEq ι]

/-- A row packet is admissible in the symmetry cage when its whole node family has a free symmetry
orbit off the origin, the divisor, and the passport set. -/
def symGoodPacket (W : ℂ → ℂ) (A : Finset ℂ) (packet : InjectiveProjectiveRowPacket row)
    (shift : InjectiveShiftConfiguration ι) : Prop :=
  shift.1 ∈ symGoodCombinedRowPacketAmbientSet W A packet

/-- One admissible packet witnesses full coefficient rank in the symmetry cage. -/
def symGaugeExpandedFullRankWitness (W : ℂ → ℂ) (A : Finset ℂ) (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (g : EntireGauge) (shift : InjectiveShiftConfiguration ι) : Prop :=
  ∃ packet : InjectiveProjectiveRowPacket row,
    symGoodPacket W A packet shift ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix degree
          (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
          (gaugeExpandedPacketValue W orders packet g shift)).mulVec

/-- A finite polynomial-coefficient relation on the jets of a caged gauged source. -/
def symGaugeExpandedPatternRelationHolds (W : ℂ → ℂ) (A : Finset ℂ) (degree : ℕ)
    (orders : ι → ℕ) (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (g : EntireGauge) (shift : InjectiveShiftConfiguration ι)
    (coeff : κ × Fin (degree + 1) → ℂ) : Prop :=
  ∀ packet : InjectiveProjectiveRowPacket row, symGoodPacket W A packet shift →
    ∀ r, ∑ col, coeff col *
      expandedDifferentialEvaluationMatrix degree
        (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
        (gaugeExpandedPacketValue W orders packet g shift) r col = 0

omit [DecidableEq row] [DecidableEq κ] [DecidableEq ι] in
theorem symGaugeExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness
    (W : ℂ → ℂ) (A : Finset ℂ) (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (g : EntireGauge) (shift : InjectiveShiftConfiguration ι)
    (hwitness : symGaugeExpandedFullRankWitness (row := row) (κ := κ) W A degree orders
      exponent g shift)
    (coeff : κ × Fin (degree + 1) → ℂ)
    (hrelation : symGaugeExpandedPatternRelationHolds (row := row) W A degree orders exponent g
      shift coeff) :
    ∀ col, coeff col = 0 := by
  obtain ⟨packet, hgood, hinjective⟩ := hwitness
  have hmul : (expandedDifferentialEvaluationMatrix degree
      (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
      (gaugeExpandedPacketValue W orders packet g shift)).mulVec coeff = 0 := by
    funext r
    simpa [Matrix.mulVec, dotProduct, mul_comm] using hrelation packet hgood r
  have hcoeff : coeff = 0 := hinjective (by simpa using hmul)
  intro col
  exact congrFun hcoeff col

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Set Topology
open ClassicalAnalyticNevanlinnaCarrierFamily

noncomputable section

variable {row κ ι : Type} [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
  [Fintype ι] [DecidableEq ι]

/-- **Compact-patch complete atlas inside the symmetry cage.** -/
theorem compact_injectiveShiftPatch_has_dense_completeAtlas_symGauge
    {A : Finset ℂ} {dep : ℂ → ℕ}
    (hA1 : ∀ a ∈ A, 1 - a ∈ A) (hdep1 : ∀ a ∈ A, dep (1 - a) = dep a)
    (hA2 : ∀ a ∈ A, (starRingEnd ℂ) a ∈ A) (hdep2 : ∀ a ∈ A, dep ((starRingEnd ℂ) a) = dep a)
    (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree < Fintype.card row)
    {W : ℂ → ℂ} (hWd : Differentiable ℂ W) (h0 : ∃ w, W w ≠ 0)
    (Kshift : Set (InjectiveShiftConfiguration ι)) (hKshift : IsCompact Kshift)
    (hdim : Module.finrank ℝ (ι → ℂ) <
      2 * (Fintype.card row - Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    ∃ G : Set ↥(symGaugeSet A dep), IsOpen G ∧ Dense G ∧
      ∀ g ∈ G, ∀ shift ∈ Kshift,
        symGaugeExpandedFullRankWitness (row := row) (κ := κ) W A degree orders exponent
          (g : EntireGauge) shift := by
  classical
  have hWa : AnalyticOnNhd ℂ W Set.univ := hWd.differentiableOn.analyticOnNhd isOpen_univ
  obtain ⟨n, packets, pieces, hcover, hpiecesCompact, hpiecesChart⟩ :=
    compact_injectiveShiftPatch_finite_symGoodCombinedRowPacket_refinement
      (row := row) (ι := ι) hWa hWd.continuous h0 A hKshift
  set m := ordersBound orders with hmdef
  set hm := le_ordersBound orders with hhm
  set D := Fintype.card ((row × ι) × Fin 4) * m with hDdef
  set pd : GaugeProbe (row × ι) m D := passportProbe (row × ι) A dep m 0 D with hpd
  set nodes : Fin n → (ι → ℂ) → row × ι → ℂ := fun j h x => (packets j).1 x.1 + h x.2 with hnodes
  set ambientPiece : Fin n → Set (ι → ℂ) := fun j => Subtype.val '' pieces j with hambient
  set family : Fin n → (↥(symGaugeSet A dep) × (ι → ℂ)) →
      row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ := fun j p =>
    gaugeExpandedActualJetFamily W m orders hm (nodes j) ((p.1 : EntireGauge), p.2) with hfamily
  set good : Fin n → Set ↥(symGaugeSet A dep) := fun j =>
    compactConfigurationAvoidance (family j)
      (expandedDifferentialEvaluationRankDefect degree
        (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent)
      (ambientPiece j) with hgooddef
  have hnodesSmooth : ∀ j, ContDiff ℝ ⊤ (nodes j) := by
    intro j
    rw [contDiff_pi]
    intro x
    exact contDiff_const.add (contDiff_apply ℝ ℂ x.2)
  have hfamilyCont : ∀ j, Continuous (family j) := by
    intro j
    exact (continuous_gaugeExpandedActualJetFamily hWd m orders hm
      (hnodesSmooth j).continuous).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hKj : ∀ j, IsCompact (ambientPiece j) := fun j =>
    (hpiecesCompact j).image continuous_subtype_val
  have hKjUj : ∀ j, ambientPiece j ⊆ symGoodCombinedRowPacketAmbientSet (ι := ι) W A (packets j) := by
    rintro j _ ⟨shiftCfg, hpiece, rfl⟩
    exact hpiecesChart j hpiece
  have hgood : ∀ j, Dense (good j) ∧ IsOpen (good j) := by
    intro j
    constructor
    · have hdense := compact_gaugeExpandedActualEvaluation_avoidance_dense_of_chart
        (row := row) (κ := κ) (ι := ι) (H := ι → ℂ)
        degree orders pd hm (packets j).1 (packets j).2 exponent hexponent hrows hWd
        (nodes j) (hnodesSmooth j)
        (symGoodCombinedRowPacketAmbientSet (ι := ι) W A (packets j)) (ambientPiece j)
        (symGoodCombinedRowPacketAmbientSet_isOpen (ι := ι) hWd.continuous A (packets j))
        (hKjUj j)
        (fun h hh => surjective_symProbe_jet (X := row × ι) (symPassportPoly A dep) m 0
          (orbitInjective_of_mem_symGood hh)
          (fun q => orbitNe_zero_of_mem_symGood hh q)
          (fun x => eval_symPassportPoly_ne_zero (notMem_passport_of_mem_symGood hh x)))
        (fun h hh x => sourceNe_zero_of_mem_symGood hh x)
        hdim (S := ↥(symGaugeSet A dep)) Subtype.val
        (symChart hA1 hdep1 hA2 hdep2 (row × ι) m 0 D)
        (fun g => continuous_symChart hA1 hdep1 hA2 hdep2 (row × ι) m 0 D g)
        (fun g => symChart_zero hA1 hdep1 hA2 hdep2 (row × ι) m 0 D g)
        (fun g c w => symChart_apply hA1 hdep1 hA2 hdep2 (row × ι) m 0 D g c w)
      exact hdense
    · exact compactConfigurationAvoidance_isOpen (family j) (hfamilyCont j) _
        (expandedDifferentialEvaluationRankDefect_isClosed degree
          (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent)
        (ambientPiece j) (hKj j)
  refine ⟨⋂ j, good j, isOpen_iInter_of_finite fun j => (hgood j).2,
    dense_iInter_of_finite_isOpen good (fun j => (hgood j).2) (fun j => (hgood j).1), ?_⟩
  intro g hg shift hshift
  obtain ⟨j, hjpiece⟩ := Set.mem_iUnion.mp (hcover hshift)
  refine ⟨packets j, hpiecesChart j hjpiece, ?_⟩
  have hjgood := Set.mem_iInter.mp hg j
  have havoid := hjgood shift.1 ⟨shift, hjpiece, rfl⟩
  have hinjective : Function.Injective
      (expandedDifferentialEvaluationMatrix degree
        (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent
        (family j (g, shift.1))).mulVec := by
    simpa only [mem_expandedDifferentialEvaluationRankDefect_iff, not_not] using havoid
  exact hinjective

/-- **All-shift full-rank law for one finite differential pattern, inside the symmetry cage.** -/
theorem global_injectiveShifts_symGaugeExpandedFullRankWitness_dense_residual
    {A : Finset ℂ} {dep : ℂ → ℕ}
    (hA1 : ∀ a ∈ A, 1 - a ∈ A) (hdep1 : ∀ a ∈ A, dep (1 - a) = dep a)
    (hA2 : ∀ a ∈ A, (starRingEnd ℂ) a ∈ A) (hdep2 : ∀ a ∈ A, dep ((starRingEnd ℂ) a) = dep a)
    (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree < Fintype.card row)
    {W : ℂ → ℂ} (hWd : Differentiable ℂ W) (h0 : ∃ w, W w ≠ 0)
    (hdim : Module.finrank ℝ (ι → ℂ) <
      2 * (Fintype.card row - Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    let good : Set ↥(symGaugeSet A dep) := {g |
      ∀ shift : InjectiveShiftConfiguration ι,
        symGaugeExpandedFullRankWitness (row := row) (κ := κ) W A degree orders exponent
          (g : EntireGauge) shift}
    Dense good ∧ good ∈ residual ↥(symGaugeSet A dep) := by
  dsimp only
  apply globalWitness_dense_residual_of_sigmaCompact
    (fun (g : ↥(symGaugeSet A dep)) (shift : InjectiveShiftConfiguration ι) =>
      symGaugeExpandedFullRankWitness (row := row) (κ := κ) W A degree orders exponent
        (g : EntireGauge) shift)
  intro Kshift hKshift
  exact compact_injectiveShiftPatch_has_dense_completeAtlas_symGauge hA1 hdep1 hA2 hdep2
    degree orders exponent hexponent hrows hWd h0 Kshift hKshift hdim

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Set Topology MvPolynomial
open ClassicalAnalyticNevanlinnaCarrierFamily

noncomputable section

/-! ### The passport survives the gauge -/

theorem eval_zero_jetShiftDeriv (P : MvPolynomial ℕ ℂ) :
    MvPolynomial.eval (fun _ => (0 : ℂ)) (jetShiftDeriv P) = 0 := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => rw [jetShiftDeriv_C, map_zero]
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ, add_zero]
  | mul_X P j hP =>
      rw [Derivation.leibniz, jetShiftDeriv_X]
      simp only [smul_eq_mul, map_add, map_mul, MvPolynomial.eval_X, hP]
      ring

theorem eval_zero_expJetPoly_succ (l : ℕ) :
    MvPolynomial.eval (fun _ => (0 : ℂ)) (expJetPoly (l + 1)) = 0 := by
  rw [expJetPoly_succ, map_add, eval_zero_jetShiftDeriv, map_mul, MvPolynomial.eval_X]
  ring

/-- **A gauge vanishing to order `d` keeps every jet of the source below order `d`.** -/
theorem iteratedDeriv_gaugeCarrier_eq_of_flat {W g : ℂ → ℂ} (hW : Differentiable ℂ W)
    (hg : Differentiable ℂ g) {a : ℂ} {d : ℕ} (hflat : ∀ k < d, iteratedDeriv k g a = 0)
    {j : ℕ} (hj : j < d) :
    iteratedDeriv j (fun w => W w * Complex.exp (g w)) a = iteratedDeriv j W a := by
  classical
  have hm : j < j + 1 := Nat.lt_succ_self j
  have hkey := iteratedDeriv_gaugeCarrier (m := j + 1) hW hg a ⟨j, hm⟩
  have hexp : ∀ l : Fin (j + 1),
      expJetMap (j + 1) (gaugeJetVec (j + 1) g a) l = if (l : ℕ) = 0 then 1 else 0 := by
    intro l
    rw [expJetMap]
    have h0 : jetExtend (j + 1) (gaugeJetVec (j + 1) g a) 0 = g a := by
      rw [jetExtend_gaugeJetVec g a (by omega), iteratedDeriv_zero]
    have hga : g a = 0 := by
      have := hflat 0 (by omega)
      rwa [iteratedDeriv_zero] at this
    have heval : MvPolynomial.eval (jetExtend (j + 1) (gaugeJetVec (j + 1) g a))
        (expJetPoly (l : ℕ))
        = MvPolynomial.eval (fun _ => (0 : ℂ)) (expJetPoly (l : ℕ)) := by
      refine eval_eq_of_mem_jetSub (expJetPoly_mem_jetSub (l : ℕ)) _ _ ?_
      intro k hk1 hk2
      rw [jetExtend_gaugeJetVec g a (lt_of_le_of_lt hk2 l.2)]
      exact hflat k (lt_of_le_of_lt hk2 (lt_of_lt_of_le l.2 (by omega)))
    rw [h0, hga, Complex.exp_zero, heval]
    rcases Nat.eq_zero_or_pos (l : ℕ) with hl | hl
    · rw [if_pos hl, hl, expJetPoly_zero, map_one, one_mul]
    · rw [if_neg (by omega)]
      obtain ⟨r, hr⟩ : ∃ r, (l : ℕ) = r + 1 := ⟨(l : ℕ) - 1, by omega⟩
      rw [hr, eval_zero_expJetPoly_succ, mul_zero]
  rw [Finset.sum_congr rfl (fun l _ => by rw [hexp l])] at hkey
  rw [hkey, Finset.sum_eq_single (⟨0, by omega⟩ : Fin (j + 1))]
  · have hcoef : leibnizJetMatrix (j + 1) (fun r => iteratedDeriv r W a) ⟨j, hm⟩
        (⟨0, by omega⟩ : Fin (j + 1)) = iteratedDeriv j W a := by
      rw [leibnizJetMatrix, leibnizJetCoeff, if_pos (Nat.zero_le _)]
      simp
    rw [hcoef]
    simp
  · intro b _ hb
    have hbne : (b : ℕ) ≠ 0 := fun hcon => hb (Fin.ext hcon)
    rw [if_neg hbne, mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ (⟨0, by omega⟩ : Fin (j + 1))) hcon

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Set Topology
open ClassicalAnalyticNevanlinnaCarrierFamily

noncomputable section

variable {A : Finset ℂ} {dep : ℂ → ℕ}

theorem allFinitePatterns_symGaugeExpandedFullRankWitness_dense_residual
    {Γ : Type} [Countable Γ]
    (hA1 : ∀ a ∈ A, 1 - a ∈ A) (hdep1 : ∀ a ∈ A, dep (1 - a) = dep a)
    (hA2 : ∀ a ∈ A, (starRingEnd ℂ) a ∈ A) (hdep2 : ∀ a ∈ A, dep ((starRingEnd ℂ) a) = dep a)
    {W : ℂ → ℂ} (hWd : Differentiable ℂ W) (h0 : ∃ w, W w ≠ 0) :
    let fullRank : Set ↥(symGaugeSet A dep) := {g |
      ∀ (p : FiniteDifferentialPattern Γ)
        (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
        symGaugeExpandedFullRankWitness (row := CarrierPatternRow p)
          (κ := CarrierPatternMonomial p) W A p.coefficientDegree p.orders
          (carrierPatternExponent p) (g : EntireGauge) shift}
    Dense fullRank ∧ fullRank ∈ residual ↥(symGaugeSet A dep) := by
  dsimp only
  let goodPattern : FiniteDifferentialPattern Γ → Set ↥(symGaugeSet A dep) := fun p =>
    {g | ∀ shift : InjectiveShiftConfiguration (CarrierPatternShift p),
      symGaugeExpandedFullRankWitness (row := CarrierPatternRow p)
        (κ := CarrierPatternMonomial p) W A p.coefficientDegree p.orders
        (carrierPatternExponent p) (g : EntireGauge) shift}
  have hgoodPattern : ∀ p : FiniteDifferentialPattern Γ,
      Dense (goodPattern p) ∧ goodPattern p ∈ residual ↥(symGaugeSet A dep) := by
    intro p
    exact global_injectiveShifts_symGaugeExpandedFullRankWitness_dense_residual
      (row := CarrierPatternRow p) (κ := CarrierPatternMonomial p) (ι := CarrierPatternShift p)
      hA1 hdep1 hA2 hdep2 p.coefficientDegree p.orders (carrierPatternExponent p)
      (carrierPatternExponent_injective p)
      (carrierPattern_rows_strictly_dominate_columns p) hWd h0
      (carrierPattern_shift_dimension_below_codimension p)
  have hresidual : (⋂ p, goodPattern p) ∈ residual ↥(symGaugeSet A dep) :=
    countable_iInter_mem.mpr fun p => (hgoodPattern p).2
  have heq : (⋂ p, goodPattern p) = {g : ↥(symGaugeSet A dep) |
      ∀ (p : FiniteDifferentialPattern Γ)
        (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
        symGaugeExpandedFullRankWitness (row := CarrierPatternRow p)
          (κ := CarrierPatternMonomial p) W A p.coefficientDegree p.orders
          (carrierPatternExponent p) (g : EntireGauge) shift} := by
    ext g
    simp only [Set.mem_iInter, goodPattern, Set.mem_setOf_eq]
  rw [heq] at hresidual
  exact ⟨dense_of_mem_residual hresidual, hresidual⟩

theorem allFinitePatterns_symGaugeExpandedRelationFree_dense_residual
    {Γ : Type} [Countable Γ]
    (hA1 : ∀ a ∈ A, 1 - a ∈ A) (hdep1 : ∀ a ∈ A, dep (1 - a) = dep a)
    (hA2 : ∀ a ∈ A, (starRingEnd ℂ) a ∈ A) (hdep2 : ∀ a ∈ A, dep ((starRingEnd ℂ) a) = dep a)
    {W : ℂ → ℂ} (hWd : Differentiable ℂ W) (h0 : ∃ w, W w ≠ 0) :
    let relationFree : Set ↥(symGaugeSet A dep) := {g |
      ∀ (p : FiniteDifferentialPattern Γ)
        (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
        (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
        symGaugeExpandedPatternRelationHolds (row := CarrierPatternRow p)
          W A p.coefficientDegree p.orders (carrierPatternExponent p) (g : EntireGauge)
          shift coeff →
        ∀ col, coeff col = 0}
    Dense relationFree ∧ relationFree ∈ residual ↥(symGaugeSet A dep) := by
  dsimp only
  let fullRank : Set ↥(symGaugeSet A dep) := {g |
    ∀ (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
      symGaugeExpandedFullRankWitness (row := CarrierPatternRow p)
        (κ := CarrierPatternMonomial p) W A p.coefficientDegree p.orders
        (carrierPatternExponent p) (g : EntireGauge) shift}
  let relationFree : Set ↥(symGaugeSet A dep) := {g |
    ∀ (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      symGaugeExpandedPatternRelationHolds (row := CarrierPatternRow p)
        W A p.coefficientDegree p.orders (carrierPatternExponent p) (g : EntireGauge)
        shift coeff →
      ∀ col, coeff col = 0}
  have hfull : Dense fullRank ∧ fullRank ∈ residual ↥(symGaugeSet A dep) := by
    simpa only [fullRank] using
      (allFinitePatterns_symGaugeExpandedFullRankWitness_dense_residual (Γ := Γ)
        hA1 hdep1 hA2 hdep2 hWd h0)
  have hsubset : fullRank ⊆ relationFree := by
    intro g hg p shift coeff hrelation
    exact symGaugeExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness
      W A p.coefficientDegree p.orders (carrierPatternExponent p) (g : EntireGauge) shift
      (hg p shift) coeff hrelation
  exact ⟨hfull.1.mono hsubset, Filter.mem_of_superset hfull.2 hsubset⟩

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Set Topology
open ClassicalAnalyticNevanlinnaCarrierFamily

noncomputable section

variable {A : Finset ℂ} {dep : ℂ → ℕ}

/-! ### Descent to differential-algebraic independence -/

/-- **No finite family of distinct complex translates of a caged relation-free gauged source
satisfies an algebraic differential relation over the rational functions.** -/
theorem not_familyDifferentiallyAlgebraicOn_symGaugeCarrier_of_relationFree
    (mm : ℕ) {W : ℂ → ℂ} (g : EntireGauge)
    (hfree : ∀ (p : FiniteDifferentialPattern ℕ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      symGaugeExpandedPatternRelationHolds (row := CarrierPatternRow p)
        W A p.coefficientDegree p.orders (carrierPatternExponent p) g shift coeff →
      ∀ col, coeff col = 0)
    (shift : InjectiveShiftConfiguration (Fin mm)) :
    ¬ FamilyDifferentiallyAlgebraicOn
      (fun i z => W (z + shift.1 i) * Complex.exp ((g : C(ℂ, ℂ)) (z + shift.1 i))) Set.univ := by
  intro hDA
  obtain ⟨nn, P, hPne, hPzero⟩ := hDA
  let shiftCode : Fin mm → ℕ := naturalFamilyShiftCode mm
  have hshiftCode : Function.Injective shiftCode := naturalFamilyShiftCode_injective mm
  let Q : MvPolynomial (Σ _ : Fin mm, Fin (nn + 1)) (Polynomial ℂ) :=
    renameToFamilyShiftJets mm nn (familyReshapeJet mm nn P)
  let p : FiniteDifferentialPattern ℕ := codedFamilyPatternOfRelation shiftCode hshiftCode P
  let shiftP : InjectiveShiftConfiguration (CarrierPatternShift p) := ⟨shift.1, shift.2⟩
  let patternCoeff : PatternRow p → ℂ :=
    polynomialPatternCoefficientVector shiftCode hshiftCode (familyOrders mm nn) Q
  let coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ :=
    fun col => patternCoeff (Fintype.equivFin (PatternShape p) col)
  have hrelation : symGaugeExpandedPatternRelationHolds (row := CarrierPatternRow p)
      W A p.coefficientDegree p.orders (carrierPatternExponent p) g shiftP coeff := by
    intro packet _ r
    let z : ℂ := packet.1 r
    let sigma := Σ i : CarrierPatternShift p, Fin (p.orders i)
    let y : CarrierPatternRow p × Fin (Fintype.card sigma) → ℂ :=
      gaugeExpandedPacketValue W p.orders packet g shiftP
    let x : sigma → ℂ := fun t =>
      familyJetVec (n := nn)
        (fun i w => W (w + shift.1 i) * Complex.exp ((g : C(ℂ, ℂ)) (w + shift.1 i)))
        z (Sum.inr (t.1, t.2))
    have hy : ∀ t : sigma, y (r, Fintype.equivFin sigma t) = x t := by
      intro t
      simpa [y, x, p, Q, shiftP, shiftCode, codedFamilyPatternOfRelation, familyOrders] using!
        (gaugeExpandedPacketValue_eq_familyJetVec packet g shift r
          (⟨t.1, t.2⟩ : Σ _ : Fin mm, Fin (nn + 1)))
    have hprod : ∀ a : CarrierPatternMonomial p,
        (carrierPatternExponent p a).prod (fun k e => y (r, k) ^ e)
          = (p.jetExponent a).prod (fun t e => x t ^ e) := by
      intro a
      rw [carrierPatternExponent, Finsupp.equivCongrLeft_apply, Finsupp.prod_equivMapDomain]
      apply Finsupp.prod_congr
      intro t _
      rw [hy t]
    have hsum : (∑ col, coeff col *
          expandedDifferentialEvaluationMatrix p.coefficientDegree
            (Fintype.card sigma) packet.1 (carrierPatternExponent p) y r col)
        = ∑ b : PatternRow p, patternCoeff b * z ^ patternDegree p b *
            (patternExponent p b).prod (fun t e => x t ^ e) := by
      apply Fintype.sum_equiv (Fintype.equivFin (PatternShape p))
      intro col
      rw [expandedDifferentialEvaluationMatrix_apply, hprod]
      simp [coeff, patternCoeff, patternDegree, patternExponent, z]
      ring
    rw [hsum]
    calc
      (∑ b : PatternRow p, patternCoeff b * z ^ patternDegree p b *
          (patternExponent p b).prod (fun t e => x t ^ e))
          = MvPolynomial.eval (Sum.elim (fun _ => z) fun q => x ⟨q.1, q.2⟩) P := by
        simpa [patternCoeff, p, Q] using!
          (codedFamilyPatternExpansion_eq_eval shiftCode hshiftCode P z x)
      _ = 0 := hPzero z (Set.mem_univ z)
  have hcoeffZero := hfree p shiftP coeff hrelation
  have hpatternZero : ∀ b : PatternRow p, patternCoeff b = 0 := by
    intro b
    have hz := hcoeffZero ((Fintype.equivFin (PatternShape p)).symm b)
    simpa [coeff] using hz
  have hP : P = 0 :=
    familyJetRelation_eq_zero_of_codedPatternCoefficients_zero shiftCode hshiftCode P
      (fun b => hpatternZero b)
  exact hPne hP

/-! ### The capstone -/

/-- **Symmetry-caged full complex translation freeness on a prescribed divisor.**  For a nonzero
entire `W` obeying the functional equation and Schwarz reality, a dense residual set of constrained
gauges makes every finite family of distinct complex translates of `W·exp(g)` differentially
algebraically independent over the rational functions, while `W·exp(g)` keeps the divisor of `W`,
both symmetries, and the prescribed finite jet passport. -/
theorem symmetryCaged_fullTranslationFreeness_denseResidual
    (hA1 : ∀ a ∈ A, 1 - a ∈ A) (hdep1 : ∀ a ∈ A, dep (1 - a) = dep a)
    (hA2 : ∀ a ∈ A, (starRingEnd ℂ) a ∈ A) (hdep2 : ∀ a ∈ A, dep ((starRingEnd ℂ) a) = dep a)
    {W : ℂ → ℂ} (hWd : Differentiable ℂ W) (h0 : ∃ w, W w ≠ 0)
    (hWsym : ∀ z, W (1 - z) = W z)
    (hWreal : ∀ z, W ((starRingEnd ℂ) z) = (starRingEnd ℂ) (W z)) :
    let universalPhase : Set ↥(symGaugeSet A dep) := {g |
      ∀ (p : FiniteDifferentialPattern ℕ)
        (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
        (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
        symGaugeExpandedPatternRelationHolds (row := CarrierPatternRow p)
          W A p.coefficientDegree p.orders (carrierPatternExponent p) (g : EntireGauge)
          shift coeff →
        ∀ col, coeff col = 0}
    Dense universalPhase ∧ universalPhase ∈ residual ↥(symGaugeSet A dep) ∧
      (∀ (g : ↥(symGaugeSet A dep)) (z : ℂ),
        analyticOrderAt (fun w => W w * Complex.exp (((g : EntireGauge) : C(ℂ, ℂ)) w)) z
          = analyticOrderAt W z) ∧
      (∀ (g : ↥(symGaugeSet A dep)) (z : ℂ),
        W (1 - z) * Complex.exp (((g : EntireGauge) : C(ℂ, ℂ)) (1 - z))
          = W z * Complex.exp (((g : EntireGauge) : C(ℂ, ℂ)) z)) ∧
      (∀ (g : ↥(symGaugeSet A dep)) (z : ℂ),
        W ((starRingEnd ℂ) z) * Complex.exp (((g : EntireGauge) : C(ℂ, ℂ)) ((starRingEnd ℂ) z))
          = (starRingEnd ℂ) (W z * Complex.exp (((g : EntireGauge) : C(ℂ, ℂ)) z))) ∧
      (∀ (g : ↥(symGaugeSet A dep)), ∀ a ∈ A, ∀ j < dep a,
        iteratedDeriv j (fun w => W w * Complex.exp (((g : EntireGauge) : C(ℂ, ℂ)) w)) a
          = iteratedDeriv j W a) ∧
      ∀ g ∈ universalPhase, ∀ (mm : ℕ) (shift : InjectiveShiftConfiguration (Fin mm)),
        ¬ FamilyDifferentiallyAlgebraicOn
          (fun i z => W (z + shift.1 i) *
            Complex.exp (((g : EntireGauge) : C(ℂ, ℂ)) (z + shift.1 i)))
          Set.univ := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (allFinitePatterns_symGaugeExpandedRelationFree_dense_residual (Γ := ℕ)
      hA1 hdep1 hA2 hdep2 hWd h0).1
  · exact (allFinitePatterns_symGaugeExpandedRelationFree_dense_residual (Γ := ℕ)
      hA1 hdep1 hA2 hdep2 hWd h0).2
  · intro g z
    exact analyticOrderAt_gaugeCarrier hWd (g : EntireGauge) z
  · intro g z
    rw [hWsym z, g.2.1 z]
  · intro g z
    rw [hWreal z, g.2.2.1 z, map_mul, ← Complex.exp_conj]
  · intro g a ha j hj
    exact iteratedDeriv_gaugeCarrier_eq_of_flat hWd (g : EntireGauge).2
      (fun k hk => g.2.2.2 a ha k hk) hj
  · intro g hg mm shift
    exact not_familyDifferentiallyAlgebraicOn_symGaugeCarrier_of_relationFree mm
      (g : EntireGauge) hg shift

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Set Topology
open ClassicalAnalyticNevanlinnaCarrierFamily

noncomputable section

variable {A : Finset ℂ} {dep : ℂ → ℕ}

/-- **Existence form of the symmetry-caged law.** -/
theorem exists_symGauge_fullTranslationFreeness
    (hA1 : ∀ a ∈ A, 1 - a ∈ A) (hdep1 : ∀ a ∈ A, dep (1 - a) = dep a)
    (hA2 : ∀ a ∈ A, (starRingEnd ℂ) a ∈ A) (hdep2 : ∀ a ∈ A, dep ((starRingEnd ℂ) a) = dep a)
    {W : ℂ → ℂ} (hWd : Differentiable ℂ W) (h0 : ∃ w, W w ≠ 0)
    (hWsym : ∀ z, W (1 - z) = W z)
    (hWreal : ∀ z, W ((starRingEnd ℂ) z) = (starRingEnd ℂ) (W z)) :
    ∃ g : EntireGauge,
      Differentiable ℂ (fun z => W z * Complex.exp ((g : C(ℂ, ℂ)) z)) ∧
      (∀ z, analyticOrderAt (fun w => W w * Complex.exp ((g : C(ℂ, ℂ)) w)) z
        = analyticOrderAt W z) ∧
      (∀ z, W (1 - z) * Complex.exp ((g : C(ℂ, ℂ)) (1 - z))
        = W z * Complex.exp ((g : C(ℂ, ℂ)) z)) ∧
      (∀ z, W ((starRingEnd ℂ) z) * Complex.exp ((g : C(ℂ, ℂ)) ((starRingEnd ℂ) z))
        = (starRingEnd ℂ) (W z * Complex.exp ((g : C(ℂ, ℂ)) z))) ∧
      (∀ a ∈ A, ∀ j < dep a,
        iteratedDeriv j (fun w => W w * Complex.exp ((g : C(ℂ, ℂ)) w)) a = iteratedDeriv j W a) ∧
      ∀ (mm : ℕ) (shift : InjectiveShiftConfiguration (Fin mm)),
        ¬ FamilyDifferentiallyAlgebraicOn
          (fun i z => W (z + shift.1 i) * Complex.exp ((g : C(ℂ, ℂ)) (z + shift.1 i)))
          Set.univ := by
  obtain ⟨hdense, _, horder, hsym, hreal, hpass, hfree⟩ :=
    symmetryCaged_fullTranslationFreeness_denseResidual hA1 hdep1 hA2 hdep2 hWd h0 hWsym hWreal
  obtain ⟨g, hg⟩ := hdense.nonempty
  exact ⟨(g : EntireGauge), hWd.mul (g : EntireGauge).2.cexp, horder g, hsym g, hreal g,
    hpass g, hfree g hg⟩

/-! ### A symmetric divisor on the critical line, and one off it -/

/-- A symmetric Schwarz-real entire source whose whole divisor lies on the critical line. -/
def critSymDivisor (t : ℝ) : ℂ → ℂ := fun z => ((z - 1 / 2) ^ 2 + ((t : ℂ)) ^ 2) ^ 2

/-- A symmetric Schwarz-real entire source whose whole divisor lies off the critical line. -/
def offSymDivisor (a : ℂ) : ℂ → ℂ := fun z =>
  (((z - 1 / 2) ^ 2 - a ^ 2) * ((z - 1 / 2) ^ 2 - ((starRingEnd ℂ) a) ^ 2)) ^ 2

theorem differentiable_critSymDivisor (t : ℝ) : Differentiable ℂ (critSymDivisor t) := by
  unfold critSymDivisor
  fun_prop

theorem differentiable_offSymDivisor (a : ℂ) : Differentiable ℂ (offSymDivisor a) := by
  unfold offSymDivisor
  fun_prop

theorem critSymDivisor_sym (t : ℝ) (z : ℂ) : critSymDivisor t (1 - z) = critSymDivisor t z := by
  unfold critSymDivisor
  ring_nf

theorem offSymDivisor_sym (a : ℂ) (z : ℂ) : offSymDivisor a (1 - z) = offSymDivisor a z := by
  unfold offSymDivisor
  ring_nf

theorem conj_half : (starRingEnd ℂ) ((1 : ℂ) / 2) = 1 / 2 := by
  rw [map_div₀, map_one]
  congr 1
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]

theorem critSymDivisor_real (t : ℝ) (z : ℂ) :
    critSymDivisor t ((starRingEnd ℂ) z) = (starRingEnd ℂ) (critSymDivisor t z) := by
  unfold critSymDivisor
  simp only [map_pow, map_add, map_sub, conj_half, Complex.conj_ofReal]

theorem offSymDivisor_real (a : ℂ) (z : ℂ) :
    offSymDivisor a ((starRingEnd ℂ) z) = (starRingEnd ℂ) (offSymDivisor a z) := by
  unfold offSymDivisor
  simp only [map_pow, map_mul, map_sub, conj_half, Complex.conj_conj]
  ring

theorem critSymDivisor_ne_zero {t : ℝ} (ht : t ≠ 0) : ∃ w, critSymDivisor t w ≠ 0 := by
  refine ⟨1 / 2, ?_⟩
  unfold critSymDivisor
  norm_num
  exact_mod_cast ht

theorem offSymDivisor_ne_zero {a : ℂ} (ha : a ≠ 0) : ∃ w, offSymDivisor a w ≠ 0 := by
  refine ⟨1 / 2, ?_⟩
  unfold offSymDivisor
  have hca : (starRingEnd ℂ) a ≠ 0 := by simpa using ha
  have h1 : ((1 / 2 : ℂ) - 1 / 2) ^ 2 - a ^ 2 = -(a ^ 2) := by ring
  have h2 : ((1 / 2 : ℂ) - 1 / 2) ^ 2 - ((starRingEnd ℂ) a) ^ 2
      = -(((starRingEnd ℂ) a) ^ 2) := by ring
  rw [h1, h2]
  exact pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 ha))
    (neg_ne_zero.mpr (pow_ne_zero 2 hca)))

/-- **Every zero of the critical source lies on the critical line.** -/
theorem critSymDivisor_zero_re {t : ℝ} {z : ℂ} (hz : critSymDivisor t z = 0) : z.re = 1 / 2 := by
  have hfac : ((z - 1 / 2) - Complex.I * (t : ℂ)) * ((z - 1 / 2) + Complex.I * (t : ℂ)) = 0 := by
    have h1 : ((z - 1 / 2) ^ 2 + ((t : ℂ)) ^ 2) = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
      exact this
    linear_combination h1 - (t : ℂ)^2 * Complex.I_sq
  rcases mul_eq_zero.mp hfac with h | h
  · have hval : z - 1 / 2 = Complex.I * (t : ℂ) := by linear_combination h
    have hre := congrArg Complex.re hval
    simp [Complex.sub_re, Complex.mul_re] at hre
    linarith
  · have hval : z - 1 / 2 = -(Complex.I * (t : ℂ)) := by linear_combination h
    have hre := congrArg Complex.re hval
    simp [Complex.sub_re, Complex.mul_re] at hre
    linarith

/-- **No zero of the off-critical source lies on the critical line.** -/
theorem offSymDivisor_zero_re {a : ℂ} (ha : a.re ≠ 0) {z : ℂ} (hz : offSymDivisor a z = 0) :
    z.re ≠ 1 / 2 := by
  have hprod : ((z - 1 / 2) ^ 2 - a ^ 2) * ((z - 1 / 2) ^ 2 - ((starRingEnd ℂ) a) ^ 2) = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
  have hsq : ∀ b : ℂ, b.re ≠ 0 → (z - 1 / 2) ^ 2 - b ^ 2 = 0 → z.re ≠ 1 / 2 := by
    intro b hb hfac hre
    have hzero : ((z - 1 / 2) - b) * ((z - 1 / 2) + b) = 0 := by linear_combination hfac
    have hhalfre : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
    have hreZ : (z - 1 / 2).re = 0 := by
      rw [Complex.sub_re, hhalfre, hre]
      norm_num
    rcases mul_eq_zero.mp hzero with h | h
    · have : b.re = 0 := by
        have hval : z - 1 / 2 = b := by linear_combination h
        rw [← hval]
        exact hreZ
      exact hb this
    · have : b.re = 0 := by
        have hval : z - 1 / 2 = -b := by linear_combination h
        have := congrArg Complex.re hval
        rw [hreZ] at this
        simp only [Complex.neg_re] at this
        linarith
      exact hb this
  have hca : ((starRingEnd ℂ) a).re = a.re := Complex.conj_re a
  rcases mul_eq_zero.mp hprod with h | h
  · exact hsq a ha h
  · exact hsq ((starRingEnd ℂ) a) (by rw [hca]; exact ha) h

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Set Topology
open ClassicalAnalyticNevanlinnaCarrierFamily

noncomputable section

/-- **Symmetry-caged critical-line blindness.**  A symmetric Schwarz-real source whose divisor lies
entirely on the critical line and one whose divisor lies entirely off it both carry free full
complex translation orbits, so the critical-line divisor predicate is invisible to the
differential-translation structure together with the two scalar symmetries. -/
theorem exists_pair_symmetryCaged_criticalLine_blindness
    {t : ℝ} (ht : t ≠ 0) {a : ℂ} (ha0 : a ≠ 0) (hare : a.re ≠ 0) :
    ∃ F₀ F₁ : ℂ → ℂ,
      Differentiable ℂ F₀ ∧ Differentiable ℂ F₁ ∧
      (∀ z, F₀ (1 - z) = F₀ z) ∧ (∀ z, F₁ (1 - z) = F₁ z) ∧
      (∀ z, F₀ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F₀ z)) ∧
      (∀ z, F₁ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F₁ z)) ∧
      (∀ z, analyticOrderAt F₀ z = analyticOrderAt (critSymDivisor t) z) ∧
      (∀ z, analyticOrderAt F₁ z = analyticOrderAt (offSymDivisor a) z) ∧
      (∀ z, F₀ z = 0 → z.re = 1 / 2) ∧ (∀ z, F₁ z = 0 → z.re ≠ 1 / 2) ∧
      (∀ (mm : ℕ) (shift : InjectiveShiftConfiguration (Fin mm)),
        ¬ FamilyDifferentiallyAlgebraicOn (fun i z => F₀ (z + shift.1 i)) Set.univ) ∧
      (∀ (mm : ℕ) (shift : InjectiveShiftConfiguration (Fin mm)),
        ¬ FamilyDifferentiallyAlgebraicOn (fun i z => F₁ (z + shift.1 i)) Set.univ) := by
  classical
  have hA1 : ∀ x ∈ (∅ : Finset ℂ), 1 - x ∈ (∅ : Finset ℂ) := by simp
  have hdep1 : ∀ x ∈ (∅ : Finset ℂ), (fun _ : ℂ => 0) (1 - x) = (fun _ : ℂ => 0) x := by simp
  have hA2 : ∀ x ∈ (∅ : Finset ℂ), (starRingEnd ℂ) x ∈ (∅ : Finset ℂ) := by simp
  have hdep2 : ∀ x ∈ (∅ : Finset ℂ),
      (fun _ : ℂ => 0) ((starRingEnd ℂ) x) = (fun _ : ℂ => 0) x := by simp
  obtain ⟨g₀, hd₀, ho₀, hs₀, hr₀, -, hf₀⟩ :=
    exists_symGauge_fullTranslationFreeness (A := (∅ : Finset ℂ)) (dep := fun _ => 0)
      hA1 hdep1 hA2 hdep2 (differentiable_critSymDivisor t) (critSymDivisor_ne_zero ht)
      (critSymDivisor_sym t) (critSymDivisor_real t)
  obtain ⟨g₁, hd₁, ho₁, hs₁, hr₁, -, hf₁⟩ :=
    exists_symGauge_fullTranslationFreeness (A := (∅ : Finset ℂ)) (dep := fun _ => 0)
      hA1 hdep1 hA2 hdep2 (differentiable_offSymDivisor a) (offSymDivisor_ne_zero ha0)
      (offSymDivisor_sym a) (offSymDivisor_real a)
  refine ⟨fun z => critSymDivisor t z * Complex.exp ((g₀ : C(ℂ, ℂ)) z),
    fun z => offSymDivisor a z * Complex.exp ((g₁ : C(ℂ, ℂ)) z),
    hd₀, hd₁, hs₀, hs₁, hr₀, hr₁, ho₀, ho₁, ?_, ?_, hf₀, hf₁⟩
  · intro z hz
    rcases mul_eq_zero.mp hz with h | h
    · exact critSymDivisor_zero_re h
    · exact absurd h (Complex.exp_ne_zero _)
  · intro z hz
    rcases mul_eq_zero.mp hz with h | h
    · exact offSymDivisor_zero_re hare h
    · exact absurd h (Complex.exp_ne_zero _)

end

end GaloisForLFunctions.HTGeometry
