import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticAntitoneCauchy

/-!
# Unconditional global Xi-jet interpolation

Arbitrary multiplicity-bounded Xi jet data are realized by an entire function.  The construction
is a compact-open Cauchy recursion:

1. exhaust the Xi divisor by finite geometric packets;
2. interpolate the next finite packet;
3. subtract an actual Xi coboundary so the new correction lies in a rapidly shrinking symmetric
   compact-open neighborhood;
4. take the complete compact-open limit.

Every correction keeps its full Xi-jet family, so the limit realizes all prescribed data.  This
proves the formerly conjectural infinite interpolation gate without a Mittag--Leffler axiom.
-/

open Complex Filter Function Set Topology
open scoped Pointwise Uniformity

namespace RHTower

noncomputable section

/- Compact convergence is translation-invariant on the entire source. -/
local instance deningerCompactOpenEntireIsUniformAddGroup :
    IsUniformAddGroup DeningerCompactOpenEntire := by
  letI : IsUniformAddGroup C(ℂ, ℂ) := by
    let phi :
        C(ℂ, ℂ) →+
          UniformOnFun ℂ ℂ
            {K : Set ℂ | IsCompact K} :=
      {
      toFun := ContinuousMap.toUniformOnFunIsCompact
      map_zero' := rfl
      map_add' _ _ := rfl }
    exact
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact
        |>.isUniformAddGroup phi
  exact
    isUniformEmbedding_subtype_val.isUniformAddGroup
      deningerCompactOpenEntireSubmodule.subtype.toAddMonoidHom

/--
Every full family of multiplicity-bounded Xi jets is realized by a compact-open entire source.
-/
theorem deningerCompactOpenAllJets_surjective :
    Function.Surjective deningerCompactOpenAllJets := by
  intro target
  obtain ⟨u, hu, huadd⟩ :=
    IsTopologicalAddGroup.exists_antitone_basis_nhds_zero
      DeningerCompactOpenEntire
  let v : ℕ → Set DeningerCompactOpenEntire :=
    fun n => u n ∩ -(u n)
  have hvnhds :
      ∀ n, v n ∈ 𝓝 (0 : DeningerCompactOpenEntire) := by
    intro n
    exact
      inter_mem (hu.mem n)
        (neg_mem_nhds_zero DeningerCompactOpenEntire
          (hu.mem n))
  let control : ℕ → ℕ :=
    fun n =>
      Classical.choose
        (exists_deningerCompactOpen_small_Xi_correction
          (hvnhds (n + 1)))
  have hcontrol :
      ∀ n F,
        (∀ (rho :
            ↥(deningerXiSupportClosedBallFinset
              (control n + 2)))
            (k : DeningerArithmeticJetIndex rho.1),
          deningerCompactOpenJet
              (xiSpectralPointSupport rho.1) k F = 0) →
          ∃ Q : DeningerCompactOpenEntire,
            F - deningerCompactOpenXiMul Q ∈
              v (n + 1) := by
    intro n
    exact
      Classical.choose_spec
        (exists_deningerCompactOpen_small_Xi_correction
          (hvnhds (n + 1)))
  let R : ℕ → ℕ :=
    fun n =>
      Nat.rec (control 0)
        (fun n previous =>
          max (previous + 1) (control (n + 1))) n
  have hcontrol_le :
      ∀ n, control n ≤ R n := by
    intro n
    cases n with
    | zero =>
        simp [R]
    | succ n =>
        simp only [R]
        exact le_max_right _ _
  have hRstep :
      ∀ n, R n + 1 ≤ R (n + 1) := by
    intro n
    simp only [R]
    exact le_max_left _ _
  have hNatR :
      ∀ n, n ≤ R n := by
    intro n
    induction n with
    | zero =>
        exact Nat.zero_le _
    | succ n ih =>
        exact (Nat.succ_le_succ ih).trans (hRstep n)
  have hRmono :
      Monotone R := by
    exact monotone_nat_of_le_succ fun n =>
      (Nat.le_succ (R n)).trans (hRstep n)
  let S : ℕ → Finset XiDivisorSupport :=
    fun n =>
      deningerXiSupportClosedBallFinset (R n + 2)
  have hSmono :
      Monotone S := by
    intro m n hmn
    apply deningerXiSupportClosedBallFinset_mono
    exact Nat.add_le_add_right (hRmono hmn) 2
  let Matches
      (n : ℕ) (F : DeningerCompactOpenEntire) : Prop :=
    ∀ (rho : ↥(S n))
      (k : DeningerArithmeticJetIndex rho.1),
      deningerCompactOpenJet
          (xiSpectralPointSupport rho.1) k F =
        target rho.1 k
  let initial :
      DeningerCompactOpenEntire :=
    deningerCompactOpenFiniteJetSection (S 0)
      (fun idx => target idx.1.1 idx.2)
  have hinitial :
      Matches 0 initial := by
    intro rho k
    let idx : DeningerArithmeticFiniteJetCoordinate (S 0) :=
      ⟨rho, k⟩
    have hcoord :=
      congrFun
        (deningerCompactOpenFiniteJets_section
          (S 0)
          (fun idx => target idx.1.1 idx.2)) idx
    exact hcoord
  have hexNext :
      ∀ n F, Matches n F →
        ∃ F' : DeningerCompactOpenEntire,
          Matches (n + 1) F' ∧
            F' - F ∈ v (n + 1) := by
    intro n F hF
    let desired :
        DeningerArithmeticFiniteJetValues (S (n + 1)) :=
      fun idx =>
        target idx.1.1 idx.2 -
          deningerCompactOpenJet
            (xiSpectralPointSupport idx.1.1)
            idx.2 F
    let P : DeningerCompactOpenEntire :=
      deningerCompactOpenFiniteJetSection
        (S (n + 1)) desired
    have hP :
        ∀ (rho : ↥(S (n + 1)))
          (k : DeningerArithmeticJetIndex rho.1),
          deningerCompactOpenJet
              (xiSpectralPointSupport rho.1) k P =
            target rho.1 k -
              deningerCompactOpenJet
                (xiSpectralPointSupport rho.1) k F := by
      intro rho k
      let idx :
          DeningerArithmeticFiniteJetCoordinate
            (S (n + 1)) :=
        ⟨rho, k⟩
      have hcoord :=
        congrFun
          (deningerCompactOpenFiniteJets_section
            (S (n + 1)) desired) idx
      exact hcoord
    have hPzero :
        ∀ (rho :
            ↥(deningerXiSupportClosedBallFinset
              (control n + 2)))
          (k : DeningerArithmeticJetIndex rho.1),
          deningerCompactOpenJet
              (xiSpectralPointSupport rho.1) k P = 0 := by
      intro rho k
      have hrhoCurrent :
          rho.1 ∈ S n := by
        apply
          (mem_deningerXiSupportClosedBallFinset
            (R n + 2) rho.1).2
        have hrho :=
          (mem_deningerXiSupportClosedBallFinset
            (control n + 2) rho.1).1 rho.2
        exact
          hrho.trans (by
            exact_mod_cast
              Nat.add_le_add_right (hcontrol_le n) 2)
      have hrhoNext :
          rho.1 ∈ S (n + 1) :=
        hSmono (Nat.le_succ n) hrhoCurrent
      have hPcoord :=
        hP ⟨rho.1, hrhoNext⟩ k
      have hFcoord :=
        hF ⟨rho.1, hrhoCurrent⟩ k
      rw [hPcoord, hFcoord, sub_self]
    obtain ⟨Q, hsmall⟩ :=
      hcontrol n P hPzero
    let C :=
      P - deningerCompactOpenXiMul Q
    have hCjets :
        deningerCompactOpenAllJets C =
          deningerCompactOpenAllJets P :=
      deningerCompactOpenAllJets_sub_XiMul P Q
    refine ⟨F + C, ?_, ?_⟩
    · intro rho k
      have hCcoord :=
        congrFun (congrFun hCjets rho.1) k
      have hPcoord :=
        hP rho k
      calc
        deningerCompactOpenJet
            (xiSpectralPointSupport rho.1) k
            (F + C) =
            deningerCompactOpenJet
                (xiSpectralPointSupport rho.1) k F +
              deningerCompactOpenJet
                (xiSpectralPointSupport rho.1) k C :=
          (deningerCompactOpenJet
            (xiSpectralPointSupport rho.1) k).map_add F C
        _ =
            deningerCompactOpenJet
                (xiSpectralPointSupport rho.1) k F +
              deningerCompactOpenJet
                (xiSpectralPointSupport rho.1) k P := by
          exact congrArg
            (deningerCompactOpenJet
              (xiSpectralPointSupport rho.1) k F + ·)
            hCcoord
        _ = target rho.1 k := by
          rw [hPcoord]
          ring
    · have hdiff :
          F + C - F = C := by
        abel
      rw [hdiff]
      exact hsmall
  let State (n : ℕ) :=
    {F : DeningerCompactOpenEntire // Matches n F}
  let start : State 0 :=
    ⟨initial, hinitial⟩
  let next :
      ∀ n, State n → State (n + 1) :=
    fun n x =>
      ⟨Classical.choose (hexNext n x.1 x.2),
        (Classical.choose_spec
          (hexNext n x.1 x.2)).1⟩
  have hnext :
      ∀ n (x : State n),
        (next n x).1 - x.1 ∈ v (n + 1) := by
    intro n x
    exact
      (Classical.choose_spec
        (hexNext n x.1 x.2)).2
  let states : (n : ℕ) → State n :=
    fun n =>
      Nat.rec start
        (fun n x => next n x) n
  let approximant : ℕ → DeningerCompactOpenEntire :=
    fun n => (states n).1
  have hstatesSucc :
      ∀ n, states (n + 1) =
        next n (states n) := by
    intro n
    rfl
  have happroximant :
      ∀ n, Matches n (approximant n) :=
    fun n => (states n).2
  have happroximantStep :
      ∀ n,
        approximant (n + 1) - approximant n ∈
          u (n + 1) ∩ -(u (n + 1)) := by
    intro n
    change
      (states (n + 1)).1 - (states n).1 ∈
        v (n + 1)
    rw [hstatesSucc]
    exact hnext n (states n)
  have hCauchy :
      CauchySeq approximant :=
    cauchySeq_of_antitone_add_basis_increments
      u hu huadd approximant happroximantStep
  obtain ⟨F, hF⟩ :=
    cauchySeq_tendsto_of_complete hCauchy
  refine ⟨F, ?_⟩
  have hObserved :
      Tendsto
        (fun n =>
          deningerCompactOpenAllJets
            (approximant n))
        atTop
        (𝓝 (deningerCompactOpenAllJets F)) :=
    (deningerCompactOpenAllJets.continuous.tendsto F).comp hF
  have hTarget :
      Tendsto
        (fun n =>
          deningerCompactOpenAllJets
            (approximant n))
        atTop (𝓝 target) := by
    rw [tendsto_pi_nhds]
    intro rho
    rw [tendsto_pi_nhds]
    intro k
    apply tendsto_const_nhds.congr'
    obtain ⟨N, hN⟩ :=
      deningerXiSupportClosedBallFinset_covers rho
    filter_upwards [eventually_ge_atTop N] with n hn
    have hrho :
        rho ∈ S n := by
      apply
        (mem_deningerXiSupportClosedBallFinset
          (R n + 2) rho).2
      have hnorm :
          ‖xiSpectralPointSupport rho‖ ≤ N :=
        (mem_deningerXiSupportClosedBallFinset
          N rho).1 hN
      exact
        hnorm.trans (by
          exact_mod_cast
            hn.trans (hNatR n) |>.trans
              (Nat.le_add_right (R n) 2))
    exact
      (happroximant n ⟨rho, hrho⟩ k).symm
  exact tendsto_nhds_unique hObserved hTarget

/-- The descended compact-open cohomology observation is surjective. -/
theorem deningerCompactOpenH1AllJets_surjective :
    Function.Surjective deningerCompactOpenH1AllJets := by
  intro target
  obtain ⟨F, hF⟩ :=
    deningerCompactOpenAllJets_surjective target
  refine
    ⟨deningerArithmeticCompactOpenH1Class F, ?_⟩
  simpa only [deningerCompactOpenH1AllJets_class] using hF

end

end RHTower
