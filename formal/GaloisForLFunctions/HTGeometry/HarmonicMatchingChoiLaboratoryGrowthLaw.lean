import GaloisForLFunctions.HTGeometry.ControlledPhaseChoiCutGap
import GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
import GaloisForLFunctions.HTGeometry.LiteralTwoQueryHaarBenchmark

open scoped BigOperators Matrix Kronecker
open Matrix

/-!
# Harmonic-matching Choi laboratory growth law

A fixed diagonal two-local Hamiltonian on disjoint qubit pairs carries reciprocal harmonic
couplings. Every laboratory shell activates a full block of controlled phases in the closed left
half-plane. A circuit with too few two-qubit gates leaves one active pair untouched, hence factors
across its endpoint cut; `ControlledPhaseChoiCutGap` then supplies a dimension-free operational
Choi-distance obstruction. The resulting lower bound is uniform over each complete time shell.
-/

namespace GaloisForLFunctions.HTGeometry.HarmonicMatchingChoiLaboratoryGrowthLaw

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.ControlledPhaseChoiCutGap
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
open GaloisForLFunctions.RHTower

theorem choiDist_reindexAlgEquiv {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Nonempty ι] [Nonempty κ]
    (e : ι ≃ κ) (U V : Matrix ι ι ℂ) :
    choiDist (Matrix.reindexAlgEquiv ℂ ℂ e U)
        (Matrix.reindexAlgEquiv ℂ ℂ e V) = choiDist U V := by
  have hι : 0 < Fintype.card ι := Fintype.card_pos
  have hκ : 0 < Fintype.card κ := Fintype.card_pos
  rw [choiDist_eq hκ, choiDist_eq hι]
  have htrace :
      Matrix.trace ((Matrix.reindexAlgEquiv ℂ ℂ e U)ᴴ *
          Matrix.reindexAlgEquiv ℂ ℂ e V) = Matrix.trace (Uᴴ * V) := by
    change Matrix.trace (star (Matrix.reindexAlgEquiv ℂ ℂ e U) *
      Matrix.reindexAlgEquiv ℂ ℂ e V) = Matrix.trace (star U * V)
    rw [← reindexAlgEquiv_star, ← map_mul, reindexAlgEquiv_trace]
  rw [htrace, Fintype.card_congr e]

theorem choiDist_ge_of_reindex_eq_kronecker_controlledPhase
    {ι γ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    (e : ι ≃ ControlledPhaseChoiCutGap.ProductIndex γ)
    (W U : Matrix ι ι ℂ)
    (A : Matrix Bool Bool ℂ)
    (B : Matrix (Bool × γ) (Bool × γ) ℂ)
    (z : ℂ) (r : Bool × γ → ℂ)
    (hWre : Matrix.reindexAlgEquiv ℂ ℂ e W = A ⊗ₖ B)
    (hUre : Matrix.reindexAlgEquiv ℂ ℂ e U =
      productControlledPhaseTarget z r)
    (hW : Wᴴ * W = 1)
    (hz : ‖z‖ = 1) (hre : z.re ≤ 0) (hr : ∀ y, ‖r y‖ = 1) :
    Real.sqrt ((1 : ℝ) / 8) ≤ choiDist W U := by
  have hWprod : (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = 1 := by
    rw [← hWre]
    change star (Matrix.reindexAlgEquiv ℂ ℂ e W) *
        Matrix.reindexAlgEquiv ℂ ℂ e W = 1
    rw [← reindexAlgEquiv_star, ← map_mul]
    have hWstar : star W * W = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using hW
    rw [hWstar, map_one]
  have hgap := choiDist_kronecker_productControlledPhaseTarget_ge
    A B z r hz hre hr hWprod
  rw [← hWre, ← hUre] at hgap
  rw [choiDist_reindexAlgEquiv e W U] at hgap
  exact hgap

theorem reindex_splitConfig_eq_kronecker_of_separates
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (Acut : Finset Q) (W : Matrix (Config Q) (Config Q) ℂ)
    (hsep : SeparatesAcross Acut W) :
    ∃ WA : Matrix (On Acut) (On Acut) ℂ,
      ∃ WB : Matrix (Off Acut) (Off Acut) ℂ,
        Matrix.reindexAlgEquiv ℂ ℂ (splitConfig Acut) W = WA ⊗ₖ WB := by
  rcases hsep with ⟨WA, WB, hsep⟩
  refine ⟨WA, WB, ?_⟩
  ext p q
  change W ((splitConfig Acut).symm p) ((splitConfig Acut).symm q) =
    WA p.1 q.1 * WB p.2 q.2
  rw [hsep]
  simp

section MatchingCut

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

def singletonPoint (q : Q) : {x : Q // x ∈ ({q} : Finset Q)} := ⟨q, by simp⟩

def onSingletonEquiv (q : Q) : On ({q} : Finset Q) ≃ Bool where
  toFun a := a (singletonPoint q)
  invFun b := fun _ => b
  left_inv a := by
    funext p
    have hp : p = singletonPoint q := by
      apply Subtype.ext
      exact Finset.mem_singleton.mp p.property
    rw [hp]
  right_inv _ := rfl

def offPoint {q₀ q₁ : Q} (hne : q₁ ≠ q₀) :
    {q : Q // q ∉ ({q₀} : Finset Q)} := ⟨q₁, by simpa⟩

abbrev PairCutRest {q₀ q₁ : Q} (hne : q₁ ≠ q₀) :=
  Off ({offPoint hne} : Finset {q : Q // q ∉ ({q₀} : Finset Q)})

def offMateEquiv {q₀ q₁ : Q} (hne : q₁ ≠ q₀) :
    Off ({q₀} : Finset Q) ≃ Bool × PairCutRest hne :=
  (splitConfig ({offPoint hne} :
      Finset {q : Q // q ∉ ({q₀} : Finset Q)})).trans
    ((onSingletonEquiv (offPoint hne)).prodCongr (Equiv.refl _))

def matchingCutEquiv {q₀ q₁ : Q} (hne : q₁ ≠ q₀) :
    Config Q ≃ ControlledPhaseChoiCutGap.ProductIndex (PairCutRest hne) :=
  (splitConfig ({q₀} : Finset Q)).trans
    ((onSingletonEquiv q₀).prodCongr (offMateEquiv hne))

theorem reindex_matchingCutEquiv_eq_kronecker_of_separates
    {q₀ q₁ : Q} (hne : q₁ ≠ q₀)
    (W : Matrix (Config Q) (Config Q) ℂ)
    (hsep : SeparatesAcross ({q₀} : Finset Q) W) :
    ∃ A : Matrix Bool Bool ℂ,
      ∃ B : Matrix (Bool × PairCutRest hne) (Bool × PairCutRest hne) ℂ,
        Matrix.reindexAlgEquiv ℂ ℂ (matchingCutEquiv hne) W = A ⊗ₖ B := by
  rcases hsep with ⟨WA, WB, hsep⟩
  let A := Matrix.reindexAlgEquiv ℂ ℂ (onSingletonEquiv q₀) WA
  let B := Matrix.reindexAlgEquiv ℂ ℂ (offMateEquiv hne) WB
  refine ⟨A, B, ?_⟩
  ext p q
  change W ((matchingCutEquiv hne).symm p) ((matchingCutEquiv hne).symm q) =
    WA ((onSingletonEquiv q₀).symm p.1) ((onSingletonEquiv q₀).symm q.1) *
      WB ((offMateEquiv hne).symm p.2) ((offMateEquiv hne).symm q.2)
  rw [hsep]
  simp [matchingCutEquiv]

omit [Fintype Q] in
@[simp] theorem matchingCutEquiv_symm_first
    {q₀ q₁ : Q} (hne : q₁ ≠ q₀)
    (a : Bool) (y : Bool × PairCutRest hne) :
    (matchingCutEquiv hne).symm (a, y) q₀ = a := by
  simp [matchingCutEquiv, onSingletonEquiv, singletonPoint, splitConfig]

omit [Fintype Q] in
@[simp] theorem matchingCutEquiv_symm_mate
    {q₀ q₁ : Q} (hne : q₁ ≠ q₀)
    (a : Bool) (y : Bool × PairCutRest hne) :
    (matchingCutEquiv hne).symm (a, y) q₁ = y.1 := by
  simp [matchingCutEquiv, offMateEquiv, onSingletonEquiv, offPoint,
    singletonPoint, splitConfig, hne]

omit [Fintype Q] in
theorem matchingCutEquiv_symm_outside_first
    {q₀ q₁ : Q} (hne : q₁ ≠ q₀)
    (a a' : Bool) (y : Bool × PairCutRest hne)
    {q : Q} (hq : q ≠ q₀) :
    (matchingCutEquiv hne).symm (a, y) q =
      (matchingCutEquiv hne).symm (a', y) q := by
  simp [matchingCutEquiv, splitConfig, hq]

end MatchingCut

section HarmonicMatching

open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

noncomputable def harmonicPairWeight {L : ℕ} (j : Fin L) : ℝ :=
  1 / ((j.val + 1 : ℕ) : ℝ)

noncomputable def harmonicPairTerm {L : ℕ}
    (x : Config (PairQubit L)) (j : Fin L) : ℝ :=
  if x (j, false) = true ∧ x (j, true) = true then harmonicPairWeight j else 0

noncomputable def harmonicMatchingEnergy {L : ℕ}
    (x : Config (PairQubit L)) : ℝ :=
  ∑ j : Fin L, harmonicPairTerm x j

noncomputable def harmonicRestEnergy {L : ℕ} (j : Fin L)
    (x : Config (PairQubit L)) : ℝ :=
  ∑ k ∈ (Finset.univ.erase j), harmonicPairTerm x k

theorem harmonicMatchingEnergy_eq_rest_add {L : ℕ} (j : Fin L)
    (x : Config (PairQubit L)) :
    harmonicMatchingEnergy x = harmonicRestEnergy j x + harmonicPairTerm x j := by
  unfold harmonicMatchingEnergy harmonicRestEnergy
  exact (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ j)).symm

theorem pair_true_ne_false {L : ℕ} (j : Fin L) :
    (j, true) ≠ (j, false) := by simp

theorem harmonicRestEnergy_matchingCutEquiv_symm_independent
    {L : ℕ} (j : Fin L) (a a' : Bool)
    (y : Bool × PairCutRest (pair_true_ne_false j)) :
    harmonicRestEnergy j
        ((matchingCutEquiv (pair_true_ne_false j)).symm (a, y)) =
      harmonicRestEnergy j
        ((matchingCutEquiv (pair_true_ne_false j)).symm (a', y)) := by
  unfold harmonicRestEnergy
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k ≠ j := Finset.ne_of_mem_erase hk
  have hkfalse : (k, false) ≠ (j, false) := by
    intro h
    exact hkj (congrArg Prod.fst h)
  have hktrue : (k, true) ≠ (j, false) := by
    intro h
    have hb := congrArg Prod.snd h
    simp at hb
  unfold harmonicPairTerm
  rw [matchingCutEquiv_symm_outside_first (pair_true_ne_false j) a a' y hkfalse,
    matchingCutEquiv_symm_outside_first (pair_true_ne_false j) a a' y hktrue]

theorem harmonicPairTerm_matchingCutEquiv_symm
    {L : ℕ} (j : Fin L) (a : Bool)
    (y : Bool × PairCutRest (pair_true_ne_false j)) :
    harmonicPairTerm ((matchingCutEquiv (pair_true_ne_false j)).symm (a, y)) j =
      if a && y.1 then harmonicPairWeight j else 0 := by
  unfold harmonicPairTerm
  simp

theorem harmonicMatchingEnergy_matchingCutEquiv_symm
    {L : ℕ} (j : Fin L) (a : Bool)
    (y : Bool × PairCutRest (pair_true_ne_false j)) :
    harmonicMatchingEnergy ((matchingCutEquiv (pair_true_ne_false j)).symm (a, y)) =
      harmonicRestEnergy j
          ((matchingCutEquiv (pair_true_ne_false j)).symm (false, y)) +
        if a && y.1 then harmonicPairWeight j else 0 := by
  rw [harmonicMatchingEnergy_eq_rest_add]
  rw [harmonicRestEnergy_matchingCutEquiv_symm_independent j a false y]
  rw [harmonicPairTerm_matchingCutEquiv_symm]

noncomputable def harmonicMatchingEvolution (L : ℕ) (t : ℝ) :
    Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ :=
  Matrix.diagonal fun x =>
    Complex.exp (-(Complex.I * (t * harmonicMatchingEnergy x)))

noncomputable def harmonicRestPhase {L : ℕ} (j : Fin L) (t : ℝ)
    (y : Bool × PairCutRest (pair_true_ne_false j)) : ℂ :=
  Complex.exp (-(Complex.I *
    (t * harmonicRestEnergy j
      ((matchingCutEquiv (pair_true_ne_false j)).symm (false, y)))))

noncomputable def harmonicSelectedPhase {L : ℕ} (j : Fin L) (t : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * (t * harmonicPairWeight j)))

theorem exp_harmonic_bool_split (R w t : ℝ) (b : Bool) :
    Complex.exp (-(Complex.I * (t * (R + if b then w else 0)))) =
      Complex.exp (-(Complex.I * (t * R))) *
        if b then Complex.exp (-(Complex.I * (t * w))) else 1 := by
  cases b
  · simp
  · simp only [if_true]
    rw [show -(Complex.I * ((t : ℂ) * ((R : ℂ) + (w : ℂ)))) =
        -(Complex.I * ((t : ℂ) * (R : ℂ))) +
          -(Complex.I * ((t : ℂ) * (w : ℂ))) by
      ring]
    rw [Complex.exp_add]

theorem reindex_harmonicMatchingEvolution_eq_productControlledPhaseTarget
    {L : ℕ} (j : Fin L) (t : ℝ)
    [DecidableEq (PairCutRest (pair_true_ne_false j))] :
    Matrix.reindexAlgEquiv ℂ ℂ (matchingCutEquiv (pair_true_ne_false j))
        (harmonicMatchingEvolution L t) =
      productControlledPhaseTarget (harmonicSelectedPhase j t)
        (harmonicRestPhase j t) := by
  classical
  ext p q
  by_cases hpq : p = q
  · subst q
    rcases p with ⟨a, y⟩
    change harmonicMatchingEvolution L t
        ((matchingCutEquiv (pair_true_ne_false j)).symm (a, y))
        ((matchingCutEquiv (pair_true_ne_false j)).symm (a, y)) =
      productControlledPhaseTarget (harmonicSelectedPhase j t)
        (harmonicRestPhase j t) (a, y) (a, y)
    simp only [harmonicMatchingEvolution, productControlledPhaseTarget,
      Matrix.diagonal_apply_eq]
    change Complex.exp (-(Complex.I *
        (t * harmonicMatchingEnergy
          ((matchingCutEquiv (pair_true_ne_false j)).symm (a, y))))) =
      harmonicRestPhase j t y *
        if a && y.1 then harmonicSelectedPhase j t else 1
    rw [harmonicMatchingEnergy_matchingCutEquiv_symm]
    unfold harmonicRestPhase harmonicSelectedPhase
    simpa only [Complex.ofReal_add, Complex.ofReal_zero] using
      (exp_harmonic_bool_split
        (harmonicRestEnergy j
          ((matchingCutEquiv (pair_true_ne_false j)).symm (false, y)))
        (harmonicPairWeight j) t (a && y.1))
  · have hinv :
        (matchingCutEquiv (pair_true_ne_false j)).symm p ≠
          (matchingCutEquiv (pair_true_ne_false j)).symm q := by
      exact (matchingCutEquiv (pair_true_ne_false j)).symm.injective.ne hpq
    simp [Matrix.reindex_apply, harmonicMatchingEvolution,
      productControlledPhaseTarget, hpq, hinv]

theorem harmonicRestPhase_norm {L : ℕ} (j : Fin L) (t : ℝ)
    (y : Bool × PairCutRest (pair_true_ne_false j)) :
    ‖harmonicRestPhase j t y‖ = 1 := by
  unfold harmonicRestPhase
  rw [show -(Complex.I *
      (t * harmonicRestEnergy j
        ((matchingCutEquiv (pair_true_ne_false j)).symm (false, y)))) =
      ((-(t * harmonicRestEnergy j
        ((matchingCutEquiv (pair_true_ne_false j)).symm (false, y))) : ℝ) : ℂ) *
        Complex.I by
    push_cast
    ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem harmonicSelectedPhase_norm {L : ℕ} (j : Fin L) (t : ℝ) :
    ‖harmonicSelectedPhase j t‖ = 1 := by
  unfold harmonicSelectedPhase
  rw [show -(Complex.I * (t * harmonicPairWeight j)) =
      ((-(t * harmonicPairWeight j) : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem harmonicSelectedPhase_re_nonpos {L : ℕ} (j : Fin L) (t : ℝ)
    (hlo : Real.pi / 2 ≤ t * harmonicPairWeight j)
    (hhi : t * harmonicPairWeight j ≤ Real.pi) :
    (harmonicSelectedPhase j t).re ≤ 0 := by
  unfold harmonicSelectedPhase
  rw [show -(Complex.I * (t * harmonicPairWeight j)) =
      ((-(t * harmonicPairWeight j) : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  exact Real.cos_nonpos_of_pi_div_two_le_of_le hlo
    (hhi.trans (by linarith [Real.pi_pos]))

theorem choiDist_circuit_harmonicMatchingEvolution_ge_of_separates
    {L : ℕ} (c : List (LocalGate (PairQubit L))) (j : Fin L) (t : ℝ)
    (hsep : SeparatesAcross ({(j, false)} : Finset (PairQubit L))
      (circuitMatrix c))
    (hlo : Real.pi / 2 ≤ t * harmonicPairWeight j)
    (hhi : t * harmonicPairWeight j ≤ Real.pi) :
    Real.sqrt ((1 : ℝ) / 8) ≤
      choiDist (circuitMatrix c) (harmonicMatchingEvolution L t) := by
  classical
  letI : DecidableEq (PairCutRest (pair_true_ne_false j)) := Classical.decEq _
  rcases reindex_matchingCutEquiv_eq_kronecker_of_separates
      (pair_true_ne_false j) (circuitMatrix c) hsep with ⟨A, B, hWre⟩
  apply choiDist_ge_of_reindex_eq_kronecker_controlledPhase
    (matchingCutEquiv (pair_true_ne_false j))
    (circuitMatrix c) (harmonicMatchingEvolution L t) A B
    (harmonicSelectedPhase j t) (harmonicRestPhase j t)
  · exact hWre
  · exact reindex_harmonicMatchingEvolution_eq_productControlledPhaseTarget j t
  · let W : Matrix.unitaryGroup (Config (PairQubit L)) ℂ :=
      ⟨circuitMatrix c, circuitMatrix_unitary c⟩
    simpa [W, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self W
  · exact harmonicSelectedPhase_norm j t
  · exact harmonicSelectedPhase_re_nonpos j t hlo hhi
  · exact harmonicRestPhase_norm j t

theorem harmonicMatching_twoGateCount_activeSet_lower
    {L : ℕ} (c : List (LocalGate (PairQubit L)))
    (S : Finset (Fin L)) (t : ℝ)
    (hactive : ∀ j ∈ S,
      Real.pi / 2 ≤ t * harmonicPairWeight j ∧
        t * harmonicPairWeight j ≤ Real.pi)
    (hclose : choiDist (circuitMatrix c) (harmonicMatchingEvolution L t) <
      Real.sqrt ((1 : ℝ) / 8)) :
    S.card ≤ 2 * twoGateCount c := by
  by_contra hnot
  have hcost : 2 * twoGateCount c < S.card := Nat.lt_of_not_ge hnot
  have htouched := circuitTouchedPairs_card_le c
  have hsmall : (circuitTouchedPairs c).card < S.card := lt_of_le_of_lt htouched hcost
  have hnsub : ¬S ⊆ circuitTouchedPairs c := by
    intro hsub
    exact (not_lt_of_ge (Finset.card_le_card hsub)) hsmall
  rcases Finset.not_subset.mp hnsub with ⟨j, hjS, hjnot⟩
  have hdisj : Disjoint ({j} : Finset (Fin L)) (circuitTouchedPairs c) := by
    simpa [Finset.disjoint_left] using hjnot
  have hsep := circuitMatrix_separates_firstEndpoints c ({j} : Finset (Fin L)) hdisj
  have hcut : firstEndpointSites ({j} : Finset (Fin L)) =
      ({(j, false)} : Finset (PairQubit L)) := by
    ext q
    rcases q with ⟨k, b⟩
    simp [firstEndpointSites, Prod.ext_iff]
  rw [hcut] at hsep
  have hgap := choiDist_circuit_harmonicMatchingEvolution_ge_of_separates
    c j t hsep (hactive j hjS).1 (hactive j hjS).2
  linarith

def harmonicBlockEmbedding {L K : ℕ} (hKL : 2 * K ≤ L) : Fin K → Fin L :=
  fun i => ⟨K + i.val, by omega⟩

theorem harmonicBlockEmbedding_injective {L K : ℕ} (hKL : 2 * K ≤ L) :
    Function.Injective (harmonicBlockEmbedding hKL) := by
  intro i j hij
  apply Fin.ext
  exact Nat.add_left_cancel (congrArg Fin.val hij)

def harmonicActiveBlock {L K : ℕ} (hKL : 2 * K ≤ L) : Finset (Fin L) :=
  Finset.univ.image (harmonicBlockEmbedding hKL)

theorem harmonicActiveBlock_card {L K : ℕ} (hKL : 2 * K ≤ L) :
    (harmonicActiveBlock hKL).card = K := by
  rw [harmonicActiveBlock, Finset.card_image_iff.mpr]
  · simp
  · exact (harmonicBlockEmbedding_injective hKL).injOn

theorem harmonicActiveBlock_index_bounds {L K : ℕ} (hKL : 2 * K ≤ L)
    {j : Fin L} (hj : j ∈ harmonicActiveBlock hKL) :
    K + 1 ≤ j.val + 1 ∧ j.val + 1 ≤ 2 * K := by
  rw [harmonicActiveBlock, Finset.mem_image] at hj
  rcases hj with ⟨i, _, rfl⟩
  dsimp [harmonicBlockEmbedding]
  constructor <;> omega

theorem harmonicActiveBlock_phase_bounds
    {L K : ℕ} (hKL : 2 * K ≤ L)
    {t : ℝ} (htlo : Real.pi * K ≤ t)
    (hthi : t < Real.pi * (K + 1))
    {j : Fin L} (hj : j ∈ harmonicActiveBlock hKL) :
    Real.pi / 2 ≤ t * harmonicPairWeight j ∧
      t * harmonicPairWeight j ≤ Real.pi := by
  have hb := harmonicActiveBlock_index_bounds hKL hj
  have hmposN : 0 < j.val + 1 := by omega
  have hmpos : (0 : ℝ) < (j.val + 1 : ℕ) := by exact_mod_cast hmposN
  have hmlo : ((K + 1 : ℕ) : ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) := by
    exact_mod_cast hb.1
  have hmhi : (((j.val + 1 : ℕ) : ℝ)) ≤ ((2 * K : ℕ) : ℝ) := by
    exact_mod_cast hb.2
  have htloR : Real.pi * (K : ℝ) ≤ t := by exact_mod_cast htlo
  have hthiR : t < Real.pi * ((K : ℝ) + 1) := by exact_mod_cast hthi
  have hdenLo : Real.pi * ((K : ℝ) + 1) ≤
      Real.pi * ((j.val + 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hb.1) Real.pi_pos.le
  have hdenHi : (Real.pi / 2) * ((j.val + 1 : ℕ) : ℝ) ≤
      Real.pi * (K : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hmhi (by positivity : 0 ≤ Real.pi / 2)
    norm_num [Nat.cast_mul] at hmul ⊢
    nlinarith
  unfold harmonicPairWeight
  rw [mul_one_div]
  constructor
  · rw [le_div_iff₀ hmpos]
    exact hdenHi.trans htloR
  · rw [div_le_iff₀ hmpos]
    exact (hthiR.trans_le hdenLo).le

theorem harmonicMatching_twoGateCount_shell_lower
    {L K : ℕ} (c : List (LocalGate (PairQubit L)))
    (hKL : 2 * K ≤ L) {t : ℝ}
    (htlo : Real.pi * K ≤ t) (hthi : t < Real.pi * (K + 1))
    (hclose : choiDist (circuitMatrix c) (harmonicMatchingEvolution L t) <
      Real.sqrt ((1 : ℝ) / 8)) :
    K ≤ 2 * twoGateCount c := by
  rw [← harmonicActiveBlock_card hKL]
  apply harmonicMatching_twoGateCount_activeSet_lower c (harmonicActiveBlock hKL) t
  · intro j hj
    exact harmonicActiveBlock_phase_bounds hKL htlo hthi hj
  · exact hclose

end HarmonicMatching

end GaloisForLFunctions.HTGeometry.HarmonicMatchingChoiLaboratoryGrowthLaw

