import GaloisForLFunctions.HTGeometry.GammaExteriorInverseBranches
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The Baire inverse-coding horizon of the Euler Gamma function

The common exterior inverse sheets of `Gamma` admit arbitrary countable itineraries.  For every
schedule of sufficiently late pole cutoffs, the finite nested inverse words converge.  Their
limit gives a topological embedding of the literal Baire space `ℕ → ℕ` into `ℂ`; the Euler Gamma
function removes the first symbol exactly.

Nothing in this file is an iterated-function-system hypothesis.  The branches, their common
domain, their factorial contractions, convergence for every Baire word, injectivity, continuity,
and continuity of the decoder are all proved for the Euler Gamma function.
-/

namespace GaloisForLFunctions

open Complex Filter Function Metric Set Topology
open scoped NNReal

noncomputable section

/-- The left shift on an infinite word or cutoff schedule. -/
def gammaCodeShift {α : Type*} (u : ℕ → α) : ℕ → α := fun k => u (k + 1)

@[simp]
theorem gammaCodeShift_apply {α : Type*} (u : ℕ → α) (k : ℕ) :
    gammaCodeShift u k = u (k + 1) := rfl

@[simp]
theorem gammaCodeShift_iterate_apply {α : Type*} (u : ℕ → α) (d k : ℕ) :
    (gammaCodeShift^[d]) u k = u (k + d) := by
  induction d generalizing k with
  | zero => simp
  | succ d ih =>
      rw [Function.iterate_succ_apply']
      simp only [gammaCodeShift_apply, ih]
      congr 1
      omega

/-- The pole label selected at clock depth `k`. -/
def gammaCodeLabel (N ω : ℕ → ℕ) (k : ℕ) : ℕ := N k + ω k

theorem gammaCodeLabel_late
    {N ω : ℕ → ℕ}
    (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) (k : ℕ) :
    gammaCommonInverseCollar.threshold ≤ gammaCodeLabel N ω k := by
  exact (hN k).trans (Nat.le_add_right (N k) (ω k))

theorem gammaCodeShift_schedule_late
    {N : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) (d : ℕ) :
    ∀ k, gammaCommonInverseCollar.threshold ≤ (gammaCodeShift^[d]) N k := by
  intro k
  simpa using hN (k + d)

/-- A finite nested inverse-Gamma word.  The first code symbol is the outermost sheet. -/
def gammaCodePrefix : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℂ → ℂ
  | _N, _ω, 0, y => y
  | N, ω, d + 1, y =>
      gammaExteriorInverseBranch (gammaCodeLabel N ω 0)
        (gammaCodePrefix (gammaCodeShift N) (gammaCodeShift ω) d y)

@[simp]
theorem gammaCodePrefix_zero (N ω : ℕ → ℕ) (y : ℂ) :
    gammaCodePrefix N ω 0 y = y := rfl

@[simp]
theorem gammaCodePrefix_succ (N ω : ℕ → ℕ) (d : ℕ) (y : ℂ) :
    gammaCodePrefix N ω (d + 1) y =
      gammaExteriorInverseBranch (gammaCodeLabel N ω 0)
        (gammaCodePrefix (gammaCodeShift N) (gammaCodeShift ω) d y) := rfl

/-- Every finite inverse word preserves the common exterior. -/
theorem gammaCodePrefix_mem
    {N ω : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k)
    {y : ℂ} (hy : y ∈ gammaExterior) :
    ∀ d, gammaCodePrefix N ω d y ∈ gammaExterior := by
  intro d
  induction d generalizing N ω with
  | zero => simpa
  | succ d ih =>
      rw [gammaCodePrefix_succ]
      apply gammaExteriorInverseBranch_mem (gammaCodeLabel_late hN 0)
      apply ih
      intro k
      simpa [gammaCodeShift] using hN (k + 1)

theorem gammaExteriorContraction_le_half
    {n : ℕ} (hn : gammaCommonInverseCollar.threshold ≤ n) :
    gammaExteriorContraction n ≤ (1 / 2 : ℝ≥0) := by
  rw [← NNReal.coe_le_coe, gammaExteriorContraction_eq]
  have hn5 : 5 ≤ n := gammaCommonInverseCollar_threshold_ge_five.trans hn
  have hfacNat : 4 ≤ n.factorial :=
    le_trans (by norm_num : 4 ≤ (5 : ℕ).factorial) (Nat.factorial_le hn5)
  have hfac : (4 : ℝ) ≤ n.factorial := by exact_mod_cast hfacNat
  have hfacpos : (0 : ℝ) < n.factorial := by positivity
  norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  apply (div_le_iff₀ hfacpos).2
  linarith

/-- A depth-`d` inverse word is at most `2⁻ᵈ`-Lipschitz on the common exterior. -/
theorem lipschitzOn_gammaCodePrefix
    {N ω : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) :
    ∀ d, LipschitzOnWith ((1 / 2 : ℝ≥0) ^ d)
      (gammaCodePrefix N ω d) gammaExterior := by
  intro d
  induction d generalizing N ω with
  | zero => simpa using! (LipschitzWith.id :
      LipschitzWith 1 (id : ℂ → ℂ)).lipschitzOnWith
  | succ d ih =>
      have hNshift : ∀ k, gammaCommonInverseCollar.threshold ≤ gammaCodeShift N k := by
        intro k
        simpa [gammaCodeShift] using hN (k + 1)
      have hinner := ih hNshift (ω := gammaCodeShift ω)
      have hmaps : MapsTo
          (gammaCodePrefix (gammaCodeShift N) (gammaCodeShift ω) d)
          gammaExterior gammaExterior := by
        intro y hy
        exact gammaCodePrefix_mem hNshift hy d
      have houter := lipschitzOn_gammaExteriorInverseBranch
        (n := gammaCodeLabel N ω 0) (gammaCodeLabel_late (ω := ω) hN 0)
      have hcomp := houter.comp hinner hmaps
      have hconst : gammaExteriorContraction (gammaCodeLabel N ω 0) *
          (1 / 2 : ℝ≥0) ^ d ≤ (1 / 2 : ℝ≥0) ^ (d + 1) := by
        rw [pow_succ]
        calc
          gammaExteriorContraction (gammaCodeLabel N ω 0) * (1 / 2 : ℝ≥0) ^ d
              ≤ (1 / 2 : ℝ≥0) * (1 / 2 : ℝ≥0) ^ d :=
            mul_le_mul_left (gammaExteriorContraction_le_half
              (gammaCodeLabel_late (ω := ω) hN 0)) _
          _ = (1 / 2 : ℝ≥0) ^ d * (1 / 2 : ℝ≥0) := mul_comm _ _
      simpa [gammaCodePrefix_succ] using! hcomp.weaken hconst

/-- Appending one sheet at the innermost end of a word. -/
theorem gammaCodePrefix_succ_right
    (N ω : ℕ → ℕ) (d : ℕ) (y : ℂ) :
    gammaCodePrefix N ω (d + 1) y =
      gammaCodePrefix N ω d
        (gammaExteriorInverseBranch (gammaCodeLabel N ω d) y) := by
  induction d generalizing N ω with
  | zero => simp
  | succ d ih =>
      rw [gammaCodePrefix_succ, gammaCodePrefix_succ]
      congr 1
      simpa [gammaCodeLabel, gammaCodeShift] using
        ih (gammaCodeShift N) (gammaCodeShift ω)

/-- Two outputs of one late sheet have diameter strictly less than `1/2`, independently of their
unbounded exterior inputs. -/
theorem dist_gammaExteriorInverseBranch_lt_half
    {n : ℕ} (hn : gammaCommonInverseCollar.threshold ≤ n)
    {x y : ℂ} (hx : x ∈ gammaExterior) (hy : y ∈ gammaExterior) :
    dist (gammaExteriorInverseBranch n x) (gammaExteriorInverseBranch n y) < 1 / 2 := by
  have hxn := gammaExteriorInverseBranch_mem_poleBall hn hx
  have hyn := gammaExteriorInverseBranch_mem_poleBall hn hy
  rw [Metric.mem_ball] at hxn hyn
  calc
    dist (gammaExteriorInverseBranch n x) (gammaExteriorInverseBranch n y)
        ≤ dist (gammaExteriorInverseBranch n x) (-(n : ℂ)) +
            dist (-(n : ℂ)) (gammaExteriorInverseBranch n y) := dist_triangle _ _ _
    _ < 1 / 4 + 1 / 4 := add_lt_add hxn (by simpa [dist_comm] using hyn)
    _ = 1 / 2 := by norm_num

/-- A fixed exterior basepoint for all finite words. -/
def gammaCodeBase : ℂ := 4

theorem gammaCodeBase_mem : gammaCodeBase ∈ gammaExterior := by
  norm_num [gammaCodeBase, gammaExterior]

/-- The depth-`d` approximation to an infinite inverse history. -/
def gammaCodeApprox (N ω : ℕ → ℕ) (d : ℕ) : ℂ :=
  gammaCodePrefix N ω d gammaCodeBase

theorem gammaCodeApprox_mem
    {N ω : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) (d : ℕ) :
    gammaCodeApprox N ω d ∈ gammaExterior :=
  gammaCodePrefix_mem hN gammaCodeBase_mem d

/-- Consecutive nontrivial approximants are geometrically close. -/
theorem dist_gammaCodeApprox_succ_succ_le
    {N ω : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) (d : ℕ) :
    dist (gammaCodeApprox N ω (d + 1)) (gammaCodeApprox N ω (d + 2)) ≤
      (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ d := by
  have hA : gammaCodeApprox N ω (d + 1) =
      gammaCodePrefix N ω d
        (gammaExteriorInverseBranch (gammaCodeLabel N ω d) gammaCodeBase) := by
    exact gammaCodePrefix_succ_right N ω d gammaCodeBase
  have hB : gammaCodeApprox N ω (d + 2) =
      gammaCodePrefix N ω d
        (gammaExteriorInverseBranch (gammaCodeLabel N ω d)
          (gammaExteriorInverseBranch (gammaCodeLabel N ω (d + 1)) gammaCodeBase)) := by
    rw [gammaCodeApprox, show d + 2 = (d + 1) + 1 by omega,
      gammaCodePrefix_succ_right N ω (d + 1),
      gammaCodePrefix_succ_right N ω d]
  rw [hA, hB]
  have hprefix := (lipschitzOn_gammaCodePrefix (ω := ω) hN d).dist_le_mul
  have hlabel := gammaCodeLabel_late (ω := ω) hN d
  have hbase1 : gammaExteriorInverseBranch (gammaCodeLabel N ω (d + 1)) gammaCodeBase ∈
      gammaExterior :=
    gammaExteriorInverseBranch_mem (gammaCodeLabel_late hN (d + 1)) gammaCodeBase_mem
  have hbase0 : gammaCodeBase ∈ gammaExterior := gammaCodeBase_mem
  have hx : gammaExteriorInverseBranch (gammaCodeLabel N ω d) gammaCodeBase ∈
      gammaExterior := gammaExteriorInverseBranch_mem hlabel hbase0
  have hy : gammaExteriorInverseBranch (gammaCodeLabel N ω d)
      (gammaExteriorInverseBranch (gammaCodeLabel N ω (d + 1)) gammaCodeBase) ∈
      gammaExterior := gammaExteriorInverseBranch_mem hlabel hbase1
  have hdiam := dist_gammaExteriorInverseBranch_lt_half hlabel hbase0 hbase1
  have hdist := hprefix _ hx _ hy
  calc
    dist (gammaCodePrefix N ω d
        (gammaExteriorInverseBranch (gammaCodeLabel N ω d) gammaCodeBase))
        (gammaCodePrefix N ω d
          (gammaExteriorInverseBranch (gammaCodeLabel N ω d)
            (gammaExteriorInverseBranch (gammaCodeLabel N ω (d + 1)) gammaCodeBase)))
        ≤ ((1 / 2 : ℝ≥0) ^ d : ℝ) *
            dist (gammaExteriorInverseBranch (gammaCodeLabel N ω d) gammaCodeBase)
              (gammaExteriorInverseBranch (gammaCodeLabel N ω d)
                (gammaExteriorInverseBranch (gammaCodeLabel N ω (d + 1)) gammaCodeBase)) := by
          simpa using hdist
    _ ≤ (1 / 2 : ℝ) ^ d * (1 / 2 : ℝ) := by
          simpa using mul_le_mul_of_nonneg_left hdiam.le
            (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ d)
    _ = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ d := by ring

theorem cauchySeq_gammaCodeApprox
    {N ω : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) :
    CauchySeq (gammaCodeApprox N ω) := by
  rw [← cauchySeq_shift 1]
  apply cauchySeq_of_le_geometric (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num)
  intro d
  simpa [Nat.add_assoc] using dist_gammaCodeApprox_succ_succ_le hN d

/-- The point of the Gamma horizon coded by the infinite Baire word `ω`. -/
def gammaBaireCode (N ω : ℕ → ℕ) : ℂ :=
  limUnder atTop (gammaCodeApprox N ω)

theorem gammaCodeApprox_tendsto
    {N ω : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) :
    Tendsto (gammaCodeApprox N ω) atTop (𝓝 (gammaBaireCode N ω)) :=
  (cauchySeq_gammaCodeApprox hN).tendsto_limUnder

theorem isClosed_gammaExterior : IsClosed gammaExterior := by
  change IsClosed (norm ⁻¹' Set.Ici (4 : ℝ))
  exact isClosed_Ici.preimage continuous_norm

/-- Every coded limit remains in the common exterior. -/
theorem gammaBaireCode_mem
    {N ω : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) :
    gammaBaireCode N ω ∈ gammaExterior := by
  apply isClosed_gammaExterior.mem_of_tendsto (gammaCodeApprox_tendsto hN)
  exact Eventually.of_forall (gammaCodeApprox_mem hN)

/-- Uniform tail estimate: after `d+1` symbols the remaining ambiguity is at most `2⁻ᵈ`. -/
theorem dist_gammaCodeApprox_succ_code_le
    {N ω : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) (d : ℕ) :
    dist (gammaCodeApprox N ω (d + 1)) (gammaBaireCode N ω) ≤
      (1 / 2 : ℝ) ^ d := by
  have hstep : ∀ k : ℕ,
      dist (gammaCodeApprox N ω (k + 1)) (gammaCodeApprox N ω (k + 1 + 1)) ≤
        (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k := by
    intro k
    simpa [Nat.add_assoc] using dist_gammaCodeApprox_succ_succ_le hN k
  have htend : Tendsto (fun k => gammaCodeApprox N ω (k + 1)) atTop
      (𝓝 (gammaBaireCode N ω)) :=
    (gammaCodeApprox_tendsto hN).comp (tendsto_add_atTop_nat 1)
  have htail := dist_le_of_le_geometric_of_tendsto
    (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) hstep htend d
  convert htail using 1 <;> ring

/-- A finite approximation depends only on its finite code prefix. -/
theorem gammaCodePrefix_congr
    {N ω ν : ℕ → ℕ} {d : ℕ}
    (hων : ∀ k < d, ω k = ν k) (y : ℂ) :
    gammaCodePrefix N ω d y = gammaCodePrefix N ν d y := by
  induction d generalizing N ω ν with
  | zero => simp
  | succ d ih =>
      rw [gammaCodePrefix_succ, gammaCodePrefix_succ]
      congr 1
      · exact congrArg (fun t => N 0 + t) (hων 0 (by omega))
      · apply ih
        intro k hk
        simpa [gammaCodeShift] using hων (k + 1) (by omega)

/-- The coding map is continuous for the ordinary product topology on Baire space. -/
theorem continuous_gammaBaireCode
    {N : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) :
    Continuous (gammaBaireCode N) := by
  letI : MetricSpace (ℕ → ℕ) := PiNat.metricSpaceNatNat
  rw [continuous_iff_continuousAt]
  intro ω
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (1 / 2 : ℝ) ^ d < ε / 2 :=
    exists_pow_lt_of_lt_one (by positivity) (by norm_num)
  refine ⟨(1 / 2 : ℝ) ^ (d + 1), by positivity, ?_⟩
  intro ν hdist
  have hcoords : ∀ k < d + 1, ν k = ω k := by
    intro k hk
    exact PiNat.apply_eq_of_dist_lt hdist (by omega)
  have happ : gammaCodeApprox N ν (d + 1) = gammaCodeApprox N ω (d + 1) := by
    exact gammaCodePrefix_congr hcoords gammaCodeBase
  have hνω := dist_gammaCodeApprox_succ_code_le hN d (ω := ν)
  have hω := dist_gammaCodeApprox_succ_code_le hN d (ω := ω)
  calc
    dist (gammaBaireCode N ν) (gammaBaireCode N ω)
        ≤ dist (gammaBaireCode N ν) (gammaCodeApprox N ν (d + 1)) +
            dist (gammaCodeApprox N ν (d + 1)) (gammaBaireCode N ω) :=
          dist_triangle _ _ _
    _ = dist (gammaCodeApprox N ν (d + 1)) (gammaBaireCode N ν) +
            dist (gammaCodeApprox N ω (d + 1)) (gammaBaireCode N ω) := by
          rw [dist_comm (gammaBaireCode N ν), happ]
    _ ≤ (1 / 2 : ℝ) ^ d + (1 / 2 : ℝ) ^ d := add_le_add hνω hω
    _ < ε := by linarith

/-- Removing the first inverse sheet commutes with the limit. -/
theorem gammaBaireCode_selfSimilarity
    {N ω : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) :
    gammaBaireCode N ω =
      gammaExteriorInverseBranch (gammaCodeLabel N ω 0)
        (gammaBaireCode (gammaCodeShift N) (gammaCodeShift ω)) := by
  have hNshift : ∀ k, gammaCommonInverseCollar.threshold ≤ gammaCodeShift N k := by
    intro k
    simpa [gammaCodeShift] using hN (k + 1)
  have hleft : Tendsto (fun d => gammaCodeApprox N ω (d + 1)) atTop
      (𝓝 (gammaBaireCode N ω)) :=
    (gammaCodeApprox_tendsto hN).comp (tendsto_add_atTop_nat 1)
  have hinner := gammaCodeApprox_tendsto (N := gammaCodeShift N)
    (ω := gammaCodeShift ω) hNshift
  have hwithin : Tendsto
      (gammaCodeApprox (gammaCodeShift N) (gammaCodeShift ω)) atTop
      (𝓝[gammaExterior] (gammaBaireCode (gammaCodeShift N) (gammaCodeShift ω))) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hinner, Eventually.of_forall (gammaCodeApprox_mem hNshift)⟩
  have hcontOn := (lipschitzOn_gammaExteriorInverseBranch
      (n := gammaCodeLabel N ω 0) (gammaCodeLabel_late (ω := ω) hN 0)).continuousOn
  have hcont := hcontOn _ (gammaBaireCode_mem (ω := gammaCodeShift ω) hNshift)
  have hright : Tendsto
      (fun d => gammaExteriorInverseBranch (gammaCodeLabel N ω 0)
        (gammaCodeApprox (gammaCodeShift N) (gammaCodeShift ω) d)) atTop
      (𝓝 (gammaExteriorInverseBranch (gammaCodeLabel N ω 0)
        (gammaBaireCode (gammaCodeShift N) (gammaCodeShift ω)))) :=
    hcont.tendsto.comp hwithin
  have heq : (fun d => gammaCodeApprox N ω (d + 1)) =
      (fun d => gammaExteriorInverseBranch (gammaCodeLabel N ω 0)
        (gammaCodeApprox (gammaCodeShift N) (gammaCodeShift ω) d)) := by
    funext d
    rfl
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

/-- On the coded horizon, `Gamma` is exactly the left shift. -/
theorem Gamma_gammaBaireCode
    {N ω : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) :
    Complex.Gamma (gammaBaireCode N ω) =
      gammaBaireCode (gammaCodeShift N) (gammaCodeShift ω) := by
  rw [gammaBaireCode_selfSimilarity hN]
  exact Gamma_gammaExteriorInverseBranch (gammaCodeLabel_late hN 0)
    (gammaBaireCode_mem (gammaCodeShift_schedule_late hN 1))

/-- Every finite Gamma iterate reads the corresponding tail of the code. -/
theorem Gamma_iterate_gammaBaireCode
    {N ω : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) (d : ℕ) :
    (Complex.Gamma^[d]) (gammaBaireCode N ω) =
      gammaBaireCode ((gammaCodeShift^[d]) N) ((gammaCodeShift^[d]) ω) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Function.iterate_succ_apply', ih]
      simpa only [Function.iterate_succ_apply'] using
        (Gamma_gammaBaireCode
          (N := (gammaCodeShift^[d]) N) (ω := (gammaCodeShift^[d]) ω)
          (gammaCodeShift_schedule_late hN d))

/-- A coded point lies in the pole disk selected by its first symbol. -/
theorem gammaBaireCode_mem_poleBall
    {N ω : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) :
    gammaBaireCode N ω ∈ Metric.ball (-(gammaCodeLabel N ω 0 : ℂ)) (1 / 4) := by
  rw [gammaBaireCode_selfSimilarity hN]
  exact gammaExteriorInverseBranch_mem_poleBall (gammaCodeLabel_late hN 0)
    (gammaBaireCode_mem (gammaCodeShift_schedule_late hN 1))

private theorem dist_neg_nat_ge_one {n m : ℕ} (hnm : n ≠ m) :
    (1 : ℝ) ≤ dist (-(n : ℂ)) (-(m : ℂ)) := by
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have hnm1 : n + 1 ≤ m := hlt
    rw [dist_eq_norm]
    have hnm1R : ((n + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hnm1
    have hltR : (n : ℝ) < m := by exact_mod_cast hlt
    have hnonneg : (0 : ℝ) ≤ (m : ℝ) - n := (sub_pos.mpr hltR).le
    have hone : (1 : ℝ) ≤ (m : ℝ) - n := by
      push_cast at hnm1R
      linarith
    have hcenter : (-(n : ℂ)) - -(m : ℂ) =
        (((m : ℝ) - (n : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcenter]
    exact hone.trans_eq (Complex.norm_of_nonneg hnonneg).symm
  · have hmn1 : m + 1 ≤ n := hgt
    rw [dist_eq_norm]
    have hmn1R : ((m + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hmn1
    have hgtR : (m : ℝ) < n := by exact_mod_cast hgt
    have hnonneg : (0 : ℝ) ≤ (n : ℝ) - m := (sub_pos.mpr hgtR).le
    have hone : (1 : ℝ) ≤ (n : ℝ) - m := by
      push_cast at hmn1R
      linarith
    have hcenter : (-(n : ℂ)) - -(m : ℂ) =
        -(((n : ℝ) - (m : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcenter, norm_neg]
    exact hone.trans_eq (Complex.norm_of_nonneg hnonneg).symm

/-- Distinct pole sheets are separated by more than `1/2`, not merely disjoint. -/
theorem half_lt_dist_gammaExteriorInverseBranch_of_ne
    {n m : ℕ} (hn : gammaCommonInverseCollar.threshold ≤ n)
    (hm : gammaCommonInverseCollar.threshold ≤ m) (hnm : n ≠ m)
    {x y : ℂ} (hx : x ∈ gammaExterior) (hy : y ∈ gammaExterior) :
    (1 / 2 : ℝ) <
      dist (gammaExteriorInverseBranch n x) (gammaExteriorInverseBranch m y) := by
  have hnx := gammaExteriorInverseBranch_mem_poleBall hn hx
  have hmy := gammaExteriorInverseBranch_mem_poleBall hm hy
  rw [Metric.mem_ball] at hnx hmy
  have hcenters := dist_neg_nat_ge_one hnm
  have hupper : dist (-(n : ℂ)) (-(m : ℂ)) <
      1 / 4 + dist (gammaExteriorInverseBranch n x)
        (gammaExteriorInverseBranch m y) + 1 / 4 := by
    calc
      dist (-(n : ℂ)) (-(m : ℂ))
          ≤ dist (-(n : ℂ)) (gammaExteriorInverseBranch n x) +
              dist (gammaExteriorInverseBranch n x) (-(m : ℂ)) := dist_triangle _ _ _
      _ ≤ dist (-(n : ℂ)) (gammaExteriorInverseBranch n x) +
              (dist (gammaExteriorInverseBranch n x) (gammaExteriorInverseBranch m y) +
                dist (gammaExteriorInverseBranch m y) (-(m : ℂ))) := by
            gcongr
            exact dist_triangle _ _ _
      _ < 1 / 4 + dist (gammaExteriorInverseBranch n x)
              (gammaExteriorInverseBranch m y) + 1 / 4 := by
            have hnx' : dist (-(n : ℂ)) (gammaExteriorInverseBranch n x) < 1 / 4 := by
              simpa [dist_comm] using hnx
            linarith
  linarith

/-- Distance below `1/2` between two coded points forces equality of their first symbols. -/
theorem gammaBaireCode_firstLabel_eq_of_dist_lt_half
    {N ω ν : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k)
    (hdist : dist (gammaBaireCode N ω) (gammaBaireCode N ν) < 1 / 2) :
    gammaCodeLabel N ω 0 = gammaCodeLabel N ν 0 := by
  by_contra hne
  rw [gammaBaireCode_selfSimilarity hN, gammaBaireCode_selfSimilarity hN] at hdist
  have hNshift : ∀ k, gammaCommonInverseCollar.threshold ≤ gammaCodeShift N k := by
    intro k
    simpa [gammaCodeShift] using hN (k + 1)
  have hsep := half_lt_dist_gammaExteriorInverseBranch_of_ne
    (gammaCodeLabel_late hN 0) (gammaCodeLabel_late hN 0) hne
    (x := gammaBaireCode (gammaCodeShift N) (gammaCodeShift ω))
    (y := gammaBaireCode (gammaCodeShift N) (gammaCodeShift ν))
    (gammaBaireCode_mem hNshift) (gammaBaireCode_mem hNshift)
  linarith

/-- The full Baire word is recovered uniquely from its complex horizon point. -/
theorem gammaBaireCode_injective
    {N : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) :
    Function.Injective (gammaBaireCode N) := by
  intro ω ν hcode
  funext k
  have hiter :
      (Complex.Gamma^[k]) (gammaBaireCode N ω) =
        (Complex.Gamma^[k]) (gammaBaireCode N ν) := congrArg _ hcode
  rw [Gamma_iterate_gammaBaireCode hN,
    Gamma_iterate_gammaBaireCode hN] at hiter
  have hdist : dist
      (gammaBaireCode ((gammaCodeShift^[k]) N) ((gammaCodeShift^[k]) ω))
      (gammaBaireCode ((gammaCodeShift^[k]) N) ((gammaCodeShift^[k]) ν)) < 1 / 2 := by
    rw [hiter]
    simp
  have hlabel := gammaBaireCode_firstLabel_eq_of_dist_lt_half
    (N := (gammaCodeShift^[k]) N) (ω := (gammaCodeShift^[k]) ω)
    (ν := (gammaCodeShift^[k]) ν) (gammaCodeShift_schedule_late hN k) hdist
  simp only [gammaCodeLabel, gammaCodeShift_iterate_apply, zero_add] at hlabel
  exact Nat.add_left_cancel hlabel

/-- No coded horizon point is a Gamma pole. -/
theorem gammaBaireCode_ne_neg_nat
    {N ω : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) (m : ℕ) :
    gammaBaireCode N ω ≠ -(m : ℂ) := by
  intro h
  have hGamma := Gamma_gammaBaireCode (N := N) (ω := ω) hN
  rw [h, Complex.Gamma_neg_nat_eq_zero] at hGamma
  exact gammaExterior_ne_zero
    (gammaBaireCode_mem (gammaCodeShift_schedule_late hN 1)) hGamma.symm

/-- Every finite Gamma iterate is continuous at every coded point, despite the poles elsewhere. -/
theorem continuousAt_Gamma_iterate_gammaBaireCode
    {N ω : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) :
    ∀ d, ContinuousAt (Complex.Gamma^[d]) (gammaBaireCode N ω) := by
  intro d
  induction d with
  | zero => simpa using (continuousAt_id : ContinuousAt (id : ℂ → ℂ) _)
  | succ d ih =>
      have hpoint := Gamma_iterate_gammaBaireCode (N := N) (ω := ω) hN d
      have hGamma : ContinuousAt Complex.Gamma
          (gammaBaireCode ((gammaCodeShift^[d]) N) ((gammaCodeShift^[d]) ω)) :=
        Complex.continuousAt_Gamma _ (gammaBaireCode_ne_neg_nat
          (gammaCodeShift_schedule_late hN d))
      have hGammaAt : ContinuousAt Complex.Gamma
          ((Complex.Gamma^[d]) (gammaBaireCode N ω)) := by
        rw [hpoint]
        exact hGamma
      have hcomp := hGammaAt.comp' ih
      simpa only [Function.iterate_succ'] using! hcomp

/-- If the `k`-th Gamma iterates of two coded points are closer than `1/2`, then their `k`-th
symbols agree. -/
theorem gammaBaireCode_coordinate_eq_of_iterate_dist_lt_half
    {N ω ν : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) {d : ℕ}
    (hdist : dist ((Complex.Gamma^[d]) (gammaBaireCode N ω))
      ((Complex.Gamma^[d]) (gammaBaireCode N ν)) < 1 / 2) :
    ω d = ν d := by
  rw [Gamma_iterate_gammaBaireCode hN, Gamma_iterate_gammaBaireCode hN] at hdist
  have hlabel := gammaBaireCode_firstLabel_eq_of_dist_lt_half
    (gammaCodeShift_schedule_late hN d) hdist
  simp only [gammaCodeLabel, gammaCodeShift_iterate_apply, zero_add] at hlabel
  exact Nat.add_left_cancel hlabel

/-- The actual subset of `ℂ` occupied by a scheduled Gamma Baire horizon. -/
abbrev gammaBaireCodeRange (N : ℕ → ℕ) : Type := Set.range (gammaBaireCode N)

/-- The coding map with codomain restricted to its actual horizon. -/
def gammaBaireCodeIntoRange (N : ℕ → ℕ) (ω : ℕ → ℕ) : gammaBaireCodeRange N :=
  ⟨gammaBaireCode N ω, ⟨ω, rfl⟩⟩

/-- The unique Baire word represented by a point of the coded horizon. -/
def gammaBaireDecode (N : ℕ → ℕ) (z : gammaBaireCodeRange N) : ℕ → ℕ :=
  Classical.choose z.property

theorem gammaBaireCode_decode (N : ℕ → ℕ) (z : gammaBaireCodeRange N) :
    gammaBaireCode N (gammaBaireDecode N z) = (z : ℂ) :=
  Classical.choose_spec z.property

theorem gammaBaireDecode_code
    {N : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) (ω : ℕ → ℕ) :
    gammaBaireDecode N (gammaBaireCodeIntoRange N ω) = ω := by
  apply gammaBaireCode_injective hN
  exact gammaBaireCode_decode N _

/-- The decoder is continuous on the actual complex horizon. -/
theorem continuous_gammaBaireDecode
    {N : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) :
    Continuous (gammaBaireDecode N) := by
  letI : MetricSpace (ℕ → ℕ) := PiNat.metricSpaceNatNat
  apply continuous_pi
  intro d
  rw [continuous_iff_continuousAt]
  intro z
  let ω := gammaBaireDecode N z
  have hz : gammaBaireCode N ω = (z : ℂ) := gammaBaireCode_decode N z
  have hiter : ContinuousAt (fun w : gammaBaireCodeRange N =>
      (Complex.Gamma^[d]) (w : ℂ)) z := by
    have h := continuousAt_Gamma_iterate_gammaBaireCode (N := N) (ω := ω) hN d
    rw [hz] at h
    exact h.comp' continuous_subtype_val.continuousAt
  have hnear : {w : gammaBaireCodeRange N |
      dist ((Complex.Gamma^[d]) (w : ℂ)) ((Complex.Gamma^[d]) (z : ℂ)) < 1 / 2} ∈ 𝓝 z :=
    (Metric.continuousAt_iff'.mp hiter) (1 / 2) (by norm_num)
  apply continuousAt_const.congr
  filter_upwards [hnear] with w hw
  have hwcode : gammaBaireCode N (gammaBaireDecode N w) = w :=
    gammaBaireCode_decode N w
  have hdist : dist
      ((Complex.Gamma^[d]) (gammaBaireCode N (gammaBaireDecode N w)))
      ((Complex.Gamma^[d]) (gammaBaireCode N ω)) < 1 / 2 := by
    rw [hwcode, hz]
    exact hw
  exact (gammaBaireCode_coordinate_eq_of_iterate_dist_lt_half hN hdist).symm

theorem continuous_gammaBaireCodeIntoRange
    {N : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) :
    Continuous (gammaBaireCodeIntoRange N) :=
  (continuous_gammaBaireCode hN).subtype_mk _

/-- **Unconditional Baire coding theorem for Gamma.**  Every sufficiently late cutoff schedule
produces a horizon homeomorphic to Baire space, and this homeomorphism is the actual inverse-sheet
limit in the complex plane. -/
def gammaBaireCodeHomeomorph
    (N : ℕ → ℕ) (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) :
    (ℕ → ℕ) ≃ₜ gammaBaireCodeRange N where
  toFun := gammaBaireCodeIntoRange N
  invFun := gammaBaireDecode N
  left_inv := gammaBaireDecode_code hN
  right_inv := by
    intro z
    apply Subtype.ext
    exact gammaBaireCode_decode N z
  continuous_toFun := continuous_gammaBaireCodeIntoRange hN
  continuous_invFun := continuous_gammaBaireDecode hN

end

end GaloisForLFunctions
