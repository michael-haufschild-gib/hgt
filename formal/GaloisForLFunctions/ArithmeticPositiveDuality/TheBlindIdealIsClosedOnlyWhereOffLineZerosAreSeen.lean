import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MaximalBlindIdealOfTheMeyerSource
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeyerNumericalRadicalAndMultiplicity
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrongLogOperatorContinuity

/-!
# The blind ideal is closed only where off-line zeros are seen

The maximal blind ideal of the Meyer source (`meyerTraceBoundedIdeal`) consists of the sources
whose Mellin transform vanishes at every off-line Xi zero; it is the largest sharp-stable
convolution ideal with nonnegative trace, and it is everything iff RH. Which topologies on the
source keep every critical jet continuous and make this ideal closed?

* **The natural Fréchet topology closes it** (`isClosed_meyerTraceBoundedIdeal`). In the weighted
  derivative topology of the source every Mellin evaluation is continuous, so the ideal is an
  intersection of closed hyperplanes, unconditionally; every critical jet stays continuous.
* **Critical data never close it** (`dense_meyerTraceBoundedIdeal_criticalJet`). In the
  critical-jet topology, the coarsest one making all jets at critical zeros continuous, the ideal
  is dense: critical single-jet sources lie in it and match any finitely many critical jets
  exactly. So it is closed there iff RH (`isClosed_criticalJet_iff`), and the same holds for every
  topology whose open sets are critical-jet open (`rh_of_isClosed_of_criticalJetTopology_le`).

So the exhaustion theorem becomes a limit statement exactly in a topology that already reads the
off-line zeros: closedness of the blind ideal is information about the off-line divisor, not about
the critical one. The natural topology is therefore not coarser than the critical-jet topology
unless RH holds (`not_criticalJetTopology_le_natural`).
-/

open Topology Set
open RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

open ArithmeticCastelnuovoSeveri

/-- Membership in the blind ideal is vanishing at every off-line Xi zero. -/
theorem mem_meyerTraceBoundedIdeal_iff (g : DeningerMeyerStrongLogTarget) :
    g ∈ meyerTraceBoundedIdeal ↔ ∀ rho : XiDivisorSupport, (rho : ℂ).re ≠ 1 / 2 →
      deningerMeyerStrongLogMellinLM (rho : ℂ) g = 0 :=
  meyerTraceOrbitBounded_iff_offLine_values_zero g

/-! ### The natural topology -/

section Natural

open scoped DeningerMeyerNaturalTopology

/-- **The natural Fréchet topology closes the blind ideal**, unconditionally. -/
theorem isClosed_meyerTraceBoundedIdeal :
    IsClosed (meyerTraceBoundedIdeal : Set DeningerMeyerStrongLogTarget) := by
  have e : (meyerTraceBoundedIdeal : Set DeningerMeyerStrongLogTarget) =
      ⋂ rho ∈ {rho : XiDivisorSupport | (rho : ℂ).re ≠ 1 / 2},
        (deningerMeyerStrongLogMellinLM (rho : ℂ)) ⁻¹' {0} := by
    ext g
    simp only [SetLike.mem_coe, mem_meyerTraceBoundedIdeal_iff, mem_iInter, mem_preimage,
      mem_singleton_iff, mem_setOf_eq]
  rw [e]
  exact isClosed_biInter fun rho _ =>
    isClosed_singleton.preimage (continuous_deningerMeyerStrongLogMellinLM (rho : ℂ))

/-- Every jet at every Xi zero is continuous in the natural topology. -/
theorem continuous_jet_natural (k : ℕ) (rho : XiDivisorSupport) :
    Continuous (deningerMeyerStrongLogMellinJetLM k (rho : ℂ)) :=
  deningerMeyerStrongLogMellinJetLM_continuous k rho

end Natural

/-! ### The critical-jet topology -/

/-- A critical jet slot: a critical Xi zero and a jet order below its multiplicity. -/
def CriticalJetSlot : Type :=
  Σ rho : {rho : XiDivisorSupport // (rho : ℂ).re = 1 / 2}, DeningerArithmeticJetIndex rho.1

/-- All critical jets of a source. -/
def criticalJetReading (g : DeningerMeyerStrongLogTarget) : CriticalJetSlot → ℂ :=
  fun q => deningerMeyerStrongLogMellinJetLM q.2.val (q.1.1 : ℂ) g

/-- The critical-jet topology: the coarsest topology making every critical jet continuous. -/
def criticalJetTopology : TopologicalSpace DeningerMeyerStrongLogTarget :=
  TopologicalSpace.induced criticalJetReading inferInstance

/-- **Critical interpolation inside the blind ideal.** Any finitely many critical jets of any
source are matched exactly by a source in the blind ideal. -/
theorem exists_mem_blind_eq_on (g : DeningerMeyerStrongLogTarget) (F : Finset CriticalJetSlot) :
    ∃ g' ∈ meyerTraceBoundedIdeal, ∀ q ∈ F, criticalJetReading g' q = criticalJetReading g q := by
  refine ⟨∑ q ∈ F, criticalJetReading g q • meyerSingleJetSource q.1.1 q.2,
    Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _
      (meyerSingleJetSource_traceOrbitBounded_of_critical q.1.1 q.1.2 q.2), fun q hq => ?_⟩
  simp only [criticalJetReading, map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single_of_mem q hq]
  · rw [meyerSingleJetSource_jet, if_pos ⟨rfl, rfl⟩, mul_one]
  · intro q' _ hne
    rw [meyerSingleJetSource_jet, if_neg, mul_zero]
    rintro ⟨h1, h2⟩
    apply hne
    obtain ⟨⟨rho, hrho⟩, i⟩ := q
    obtain ⟨⟨rho', hrho'⟩, i'⟩ := q'
    simp only at h1 h2
    subst h1
    have : i = i' := Fin.ext h2
    subst this
    rfl

/-- **The blind ideal is dense for the critical-jet topology.** -/
theorem dense_meyerTraceBoundedIdeal_criticalJet :
    @Dense DeningerMeyerStrongLogTarget criticalJetTopology
      (meyerTraceBoundedIdeal : Set DeningerMeyerStrongLogTarget) := by
  letI := criticalJetTopology
  rw [dense_iff_inter_open]
  rintro U hU ⟨g, hg⟩
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hV _ hg
  obtain ⟨g', hg', heq⟩ := exists_mem_blind_eq_on g I
  refine ⟨g', ?_, hg'⟩
  apply hsub
  intro q hq
  rw [heq q hq]
  exact (hu q hq).2

/-- **Closed for critical data iff RH.** -/
theorem isClosed_criticalJet_iff :
    @IsClosed DeningerMeyerStrongLogTarget criticalJetTopology
      (meyerTraceBoundedIdeal : Set DeningerMeyerStrongLogTarget) ↔ RiemannHypothesis := by
  rw [← meyerTraceBoundedIdeal_eq_top_iff]
  letI := criticalJetTopology
  constructor
  · intro hc
    have h := dense_meyerTraceBoundedIdeal_criticalJet.closure_eq
    rw [hc.closure_eq] at h
    exact Submodule.eq_top_iff'.mpr fun g => by
      have : g ∈ (meyerTraceBoundedIdeal : Set DeningerMeyerStrongLogTarget) := by
        rw [h]; exact mem_univ g
      exact this
  · intro htop
    rw [htop, Submodule.top_coe]
    exact isClosed_univ

/-- **No topology built from critical data closes the blind ideal unless RH.** If every open set
of `τ` is open for the critical-jet topology and the blind ideal is `τ`-closed, then RH. -/
theorem rh_of_isClosed_of_criticalJetTopology_le {τ : TopologicalSpace DeningerMeyerStrongLogTarget}
    (hτ : criticalJetTopology ≤ τ)
    (hc : @IsClosed DeningerMeyerStrongLogTarget τ
      (meyerTraceBoundedIdeal : Set DeningerMeyerStrongLogTarget)) : RiemannHypothesis :=
  isClosed_criticalJet_iff.mp (hc.mono hτ)

/-- The natural topology reads every critical jet: it is finer than the critical-jet topology. -/
theorem natural_le_criticalJetTopology :
    deningerMeyerStrongLogTopology ≤ criticalJetTopology := by
  rw [criticalJetTopology, ← continuous_iff_le_induced]
  exact continuous_pi fun q => continuous_jet_natural q.2.val q.1.1

/-- **The natural topology is not determined by critical data unless RH.** -/
theorem not_criticalJetTopology_le_natural (h : ¬ RiemannHypothesis) :
    ¬ criticalJetTopology ≤ deningerMeyerStrongLogTopology :=
  fun hle => h (rh_of_isClosed_of_criticalJetTopology_le hle isClosed_meyerTraceBoundedIdeal)

end GaloisForLFunctions.ArithmeticPositiveDuality
