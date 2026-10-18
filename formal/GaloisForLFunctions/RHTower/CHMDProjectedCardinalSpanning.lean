import GaloisForLFunctions.RHTower.CHMDEigenvectorCardinalReadoutAndFourTermNodalDecomposition
import GaloisForLFunctions.RHTower.CHMDFullSpectralNullspace

/-!
# Actual cardinal synthesis of the resolvent bound-state band

The mass components of every small translation of the real and imaginary Xi
cardinal packets detect each eigenspace in `(1/2,1)`. Their orthogonal spectral
projections span that finite-dimensional eigenspace, with a finite subfamily
already sufficient. Across the entire open band their closed span is exactly
the closed span of its eigenvectors. Global finite dimensionality is not assumed.
-/


open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace
noncomputable section


namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump CHMDTranslation

/-- Actual real and imaginary cardinal graph packets at every admissible small shift. -/
def translatedCardinalPackets : Set SourceGraph :=
  {q | ∃ a : ℂ, 0 < a.re ∧ XiC a = 0 ∧ ∃ t : ℝ,
    |t| ≤ CHMDThetaTranslate.radius ∧
      (q.val.fst =ᵐ[massMeasure]
        phiDoobInv (translate (fun x => (divisorCardinalSource a x).re) t) ∨
       q.val.fst =ᵐ[massMeasure]
        phiDoobInv (translate (fun x => (divisorCardinalSource a x).im) t))}

theorem fullSpectralNullspace_of_cardinal_pair_zero {p : SourceGraph}
    (hp : ∀ q ∈ translatedCardinalPackets, sourcePair p q = 0) :
    p ∈ fullSpectralNullspace := by
  have hshift {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0) {t : ℝ}
      (ht : |t| ≤ CHMDThetaTranslate.radius) : shiftedCosineReadout p a t = 0 := by
    obtain ⟨u, v, hus, hvs, hu, hv⟩ := exists_translatedCardinalFrame ha hz t ht
    have hr := hp u ⟨a, ha, hz, t, ht, Or.inl hus⟩
    have hi := hp v ⟨a, ha, hz, t, ht, Or.inr hvs⟩
    rw [hu] at hr
    rw [hv] at hi
    have hm := (cardinalOrbitMass_pos ha hz).ne'
    apply Complex.ext
    · exact (mul_eq_zero.mp hr).resolve_left hm
    · exact (mul_eq_zero.mp hi).resolve_left hm
  have hpos {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0) :
      graphFourierReadout p a = 0 ∧ graphFourierReadout p (-a) = 0 := by
    have hn : a ≠ 0 := by intro h; simp [h] at ha
    exact shiftedCosineReadout_separates p hn CHMDThetaTranslate.radius_pos
      (fun _ ht => hshift ha hz ht)
  intro a hz
  rcases lt_or_gt_of_ne (re_ne_zero_of_XiC_eq_zero hz) with hneg | hpos'
  · have hza : XiC (-a) = 0 := by rw [XiC_even, hz]
    have h := (hpos (a := -a) (by simpa using neg_pos.mpr hneg) hza).2
    simpa only [neg_neg] using h
  · exact (hpos hpos' hz).1

/-- Translated cardinal packets detect every eigenvector strictly between the threshold
and the ground eigenvalue. No finiteness of the total zero set is assumed. -/
theorem eigenvector_eq_zero_of_cardinal_orthogonal {μ : ℝ} (hμ : 1 / 2 < μ)
    (hμ1 : μ < 1) {w : MassSpace} (heig : resolvent w = μ • w)
    (hw : ∀ q ∈ translatedCardinalPackets, ⟪w, q.val.fst⟫_ℝ = 0) : w = 0 := by
  have hnull : rieszLift w ∈ fullSpectralNullspace :=
    fullSpectralNullspace_of_cardinal_pair_zero fun q hq => by
      rw [sourcePair_rieszLift_of_eigenvector heig, hw q hq, mul_zero]
  have hprim := primitiveGraph_rieszLift (inner_oneL_eq_zero_of_eigenvector hμ1.ne heig)
  have hcos : polarCosine (rieszLift w) = 0 := by
    rw [polarCosine_oneL]
    exact hprim
  have hnonneg : 0 ≤ sourceEnergy (rieszLift w) := by
    rw [full_nullspace_energy hnull, hcos]
    positivity
  have hlower : μ * ‖w‖ ^ 2 ≤ ⟪resolvent w, w⟫_ℝ := by
    rw [heig, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have henergy := sourceEnergy_rieszLift_le_of_lower_bound hμ hlower
  have hpos : 0 < μ * (2 * μ - 1) := mul_pos (by linarith) (by linarith)
  have hsq : ‖w‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖w‖]
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg w])

abbrev cardinalEigenspace (μ : ℝ) : Submodule ℝ MassSpace :=
  Module.End.eigenspace (resolvent : MassSpace →ₗ[ℝ] MassSpace) μ

instance cardinalEigenspace_complete (μ : ℝ) : CompleteSpace (cardinalEigenspace μ) :=
  (isClosed_eigenspace μ).completeSpace_coe

/-- Orthogonal spectral projection of an actual translated cardinal packet. -/
def cardinalEigenpacket (μ : ℝ) (q : translatedCardinalPackets) : cardinalEigenspace μ :=
  (cardinalEigenspace μ).orthogonalProjectionOnto q.val.val.fst

/-- Exact algebraic spanning of every finite-dimensional eigenspace in `(1/2,1)`. -/
theorem span_cardinalEigenpacket_eq_top {μ : ℝ} (hμ : 1 / 2 < μ) (hμ1 : μ < 1) :
    Submodule.span ℝ (Set.range (cardinalEigenpacket μ)) = ⊤ := by
  letI : FiniteDimensional ℝ (cardinalEigenspace μ) := finiteDimensional_eigenspace_above_half hμ
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro w hw
  apply Subtype.ext
  apply eigenvector_eq_zero_of_cardinal_orthogonal hμ hμ1
    (Module.End.mem_eigenspace_iff.mp w.property)
  intro q hq
  have h := (Submodule.mem_orthogonal' _ _).mp hw
    (cardinalEigenpacket μ ⟨q, hq⟩) (Submodule.subset_span ⟨⟨q, hq⟩, rfl⟩)
  simpa only [cardinalEigenpacket,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] using h

/-- The packet synthesis span has closed range in each actual bound-state eigenspace. -/
theorem isClosed_span_cardinalEigenpacket {μ : ℝ} (hμ : 1 / 2 < μ) (hμ1 : μ < 1) :
    IsClosed (Submodule.span ℝ (Set.range (cardinalEigenpacket μ)) : Set (cardinalEigenspace μ)) := by
  rw [span_cardinalEigenpacket_eq_top hμ hμ1]
  exact isClosed_univ

/-- Finitely many projected actual packets already synthesize the whole eigenspace. -/
theorem exists_finite_cardinalEigenpacket_span {μ : ℝ} (hμ : 1 / 2 < μ) (hμ1 : μ < 1) :
    ∃ s : Finset (cardinalEigenspace μ), (s : Set (cardinalEigenspace μ)) ⊆
      Set.range (cardinalEigenpacket μ) ∧ Submodule.span ℝ (s : Set (cardinalEigenspace μ)) = ⊤ := by
  letI : FiniteDimensional ℝ (cardinalEigenspace μ) := finiteDimensional_eigenspace_above_half hμ
  have hfg : (Submodule.span ℝ (Set.range (cardinalEigenpacket μ))).FG := by
    rw [span_cardinalEigenpacket_eq_top hμ hμ1]
    exact Module.Finite.fg_top
  obtain ⟨s, hs, heq⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (Set.range (cardinalEigenpacket μ))).mp hfg
  exact ⟨s, hs, heq.symm.trans (span_cardinalEigenpacket_eq_top hμ hμ1)⟩

/-- All actual projected cardinal packets across the open bound-state band. -/
def bandCardinalPackets : Set MassSpace :=
  {w | ∃ μ : ℝ, 1 / 2 < μ ∧ μ < 1 ∧ ∃ q : translatedCardinalPackets,
    (cardinalEigenpacket μ q : MassSpace) = w}

def openBoundStateEigenvectors : Set MassSpace :=
  {w | ∃ μ : ℝ, 1 / 2 < μ ∧ μ < 1 ∧ resolvent w = μ • w}

/-- Algebraic spanning holds simultaneously at every eigenvalue in the open band. -/
theorem span_bandCardinalPackets :
    Submodule.span ℝ bandCardinalPackets = Submodule.span ℝ openBoundStateEigenvectors := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro w ⟨μ, hμ, hμ1, q, rfl⟩
    exact Submodule.subset_span
      ⟨μ, hμ, hμ1, Module.End.mem_eigenspace_iff.mp (cardinalEigenpacket μ q).property⟩
  · apply Submodule.span_le.mpr
    rintro w ⟨μ, hμ, hμ1, heig⟩
    have hle : Submodule.span ℝ (Set.range (cardinalEigenpacket μ)) ≤
        (Submodule.span ℝ bandCardinalPackets).comap (cardinalEigenspace μ).subtype := by
      apply Submodule.span_le.mpr
      rintro v ⟨q, rfl⟩
      exact Submodule.subset_span ⟨μ, hμ, hμ1, q, rfl⟩
    rw [span_cardinalEigenpacket_eq_top hμ hμ1] at hle
    exact hle (show (⟨w, Module.End.mem_eigenspace_iff.mpr heig⟩ : cardinalEigenspace μ) ∈
      (⊤ : Submodule ℝ (cardinalEigenspace μ)) from trivial)

/-- The entire closed `(1/2,1)` bound-state sector, without a global finiteness premise. -/
def openBoundStateBand : Submodule ℝ MassSpace :=
  (Submodule.span ℝ openBoundStateEigenvectors).topologicalClosure

theorem closed_span_bandCardinalPackets :
    (Submodule.span ℝ bandCardinalPackets).topologicalClosure = openBoundStateBand := by
  rw [span_bandCardinalPackets]
  rfl

theorem isClosed_openBoundStateBand : IsClosed (openBoundStateBand : Set MassSpace) :=
  (Submodule.span ℝ openBoundStateEigenvectors).isClosed_topologicalClosure

end RHTower.CHMDPolar
