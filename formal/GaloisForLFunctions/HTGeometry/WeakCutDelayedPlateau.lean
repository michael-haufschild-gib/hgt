/-
# A weak cut delays the onset without touching the later plateau

The seed of the weak-cut theorem must factor across the cut, so it is a *product* cubic-phase seed;
the bipartite eighth-root transfer supplies a finite family of such seeds, one member of which is
collision-good at every shell direction.  Finitely many good sets therefore cover the weak-edge
sector, one member serves a positive-measure part of it, and the degenerate directions are null
inside that part.  At the resulting single pair the split synthesis cap survives the whole
prescribed delay, while the single-orbit plateau makes the evolution hard at every instant of
arbitrarily late windows and the projective recurrence returns it to the seed.

Main results:
* `regSplit`, `bipartiteFamily`, `registerSeed` — the bipartite reading of the register.
* `norm_pathHamiltonian_le_sqrt` — **the orbit speed of the path shell**.
* `subset_iUnion_cubicGood` — the finite product cubic family serves every direction.
* `exists_weakCut_fixed_pair` — one seed and one nondegenerate weak-cut direction.
* `exists_weakCut_delayed_plateau` — **Theorem C**.
-/
import GaloisForLFunctions.HTGeometry.BipartiteEighthRootTransfer
import GaloisForLFunctions.HTGeometry.PathShellProjectiveGenericity
import GaloisForLFunctions.HTGeometry.SingleOrbitPlateauWindow

open Finset MeasureTheory Matrix Filter Set Metric
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

set_option linter.unusedSectionVars false

section Register

variable {k a b : ℕ}

/-- A contiguous bipartition of the register. -/
def regSplit (hab : a + b = k + 3) :
    FiniteQubitConfiguration (Fin (k + 3)) ≃ (Fin a → Bool) × (Fin b → Bool) :=
  (Equiv.arrowCongr ((finCongr hab.symm).trans finSumFinEquiv.symm) (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) Bool)

theorem card_regSplit (hab : a + b = k + 3) :
    Fintype.card (FiniteQubitConfiguration (Fin (k + 3)))
      = Fintype.card (Fin a → Bool) * Fintype.card (Fin b → Bool) := by
  simp only [FiniteQubitConfiguration, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [← pow_add, hab]

/-- An orthonormal family of the register read on the bipartite factorization. -/
def bipartiteFamily (hab : a + b = k + 3)
    (e : FiniteQubitConfiguration (Fin (k + 3)) → FiniteQubitConfiguration (Fin (k + 3)) → ℂ) :
    FiniteQubitConfiguration (Fin (k + 3)) → ((Fin a → Bool) × (Fin b → Bool)) → ℂ :=
  fun j p => e j ((regSplit hab).symm p)

theorem sum_normSq_bipartiteFamily (hab : a + b = k + 3)
    {e : FiniteQubitConfiguration (Fin (k + 3)) → FiniteQubitConfiguration (Fin (k + 3)) → ℂ}
    (he : ∀ j, (∑ x, ‖e j x‖ ^ 2) = 1) (j : FiniteQubitConfiguration (Fin (k + 3))) :
    (∑ p, ‖bipartiteFamily hab e j p‖ ^ 2) = 1 := by
  rw [← he j]
  exact Equiv.sum_comp (regSplit hab).symm (fun x => ‖e j x‖ ^ 2)

/-- A bipartite state read on the register. -/
def registerSeed (hab : a + b = k + 3) (psi : ((Fin a → Bool) × (Fin b → Bool)) → ℂ) :
    FiniteQubitConfiguration (Fin (k + 3)) → ℂ :=
  fun x => psi (regSplit hab x)

theorem finiteComplexInner_bipartiteFamily (hab : a + b = k + 3)
    (e : FiniteQubitConfiguration (Fin (k + 3)) → FiniteQubitConfiguration (Fin (k + 3)) → ℂ)
    (psi : ((Fin a → Bool) × (Fin b → Bool)) → ℂ) (j : FiniteQubitConfiguration (Fin (k + 3))) :
    finiteComplexInner (bipartiteFamily hab e j) psi
      = finiteComplexInner (e j) (registerSeed hab psi) := by
  rw [finiteComplexInner, finiteComplexInner]
  refine (Equiv.sum_comp (regSplit hab)
    (fun p => (starRingEnd ℂ) (bipartiteFamily hab e j p) * psi p)).symm.trans ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [bipartiteFamily, registerSeed, Equiv.symm_apply_apply]

theorem sum_normSq_registerSeed (hab : a + b = k + 3)
    {psi : ((Fin a → Bool) × (Fin b → Bool)) → ℂ} (hpsi : (∑ p, ‖psi p‖ ^ 2) = 1) :
    (∑ x, ‖registerSeed hab psi x‖ ^ 2) = 1 := by
  rw [← hpsi]
  exact Equiv.sum_comp (regSplit hab) (fun p => ‖psi p‖ ^ 2)

end Register


section Selection

variable (k : ℕ) {a b : ℕ}

/-- The product cubic-phase seed of a coefficient pair, read on the register. -/
def cubicProductSeed (hab : a + b = k + 3)
    (c : (MonLe (Fin a) 3 → ZMod 8) × (MonLe (Fin b) 3 → ZMod 8)) :
    FiniteQubitConfiguration (Fin (k + 3)) → ℂ :=
  registerSeed hab (prodPhaseSeed (eighthPhase (prodPolyEval 3 c)))

theorem sum_normSq_cubicProductSeed (hab : a + b = k + 3)
    (c : (MonLe (Fin a) 3 → ZMod 8) × (MonLe (Fin b) 3 → ZMod 8)) :
    (∑ x, ‖cubicProductSeed k hab c x‖ ^ 2) = 1 :=
  sum_normSq_registerSeed hab (sum_normSq_prodPhaseSeed _)

theorem finiteComplexInner_cubicProductSeed (hab : a + b = k + 3)
    (c : (MonLe (Fin a) 3 → ZMod 8) × (MonLe (Fin b) 3 → ZMod 8)) :
    finiteComplexInner (cubicProductSeed k hab c) (cubicProductSeed k hab c) = 1 := by
  have hcast : finiteComplexInner (cubicProductSeed k hab c) (cubicProductSeed k hab c)
      = ((∑ x, ‖cubicProductSeed k hab c x‖ ^ 2 : ℝ) : ℂ) := by
    rw [finiteComplexInner, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Complex.normSq_eq_conj_mul_self, Complex.sq_norm]
  rw [hcast, sum_normSq_cubicProductSeed]
  norm_num

/-- The shell directions at which one product cubic seed has small collision. -/
def cubicGood (hab : a + b = k + 3)
    (c : (MonLe (Fin a) 3 → ZMod 8) × (MonLe (Fin b) 3 → ZMod 8)) :
    Set (sphere (0 : PathShell (k + 1)) 1) :=
  {v | (∑ j, ‖finiteComplexInner (pathEigenBasis k (v : PathShell (k + 1)) j)
        (cubicProductSeed k hab c)‖ ^ 4)
      ≤ 4 / ((Fintype.card (Fin a → Bool) : ℝ) * Fintype.card (Fin b → Bool))}

/-- **The finite product cubic family serves every shell direction.** -/
theorem subset_iUnion_cubicGood (hab : a + b = k + 3) :
    (Set.univ : Set (sphere (0 : PathShell (k + 1)) 1)) ⊆
      ⋃ c : (MonLe (Fin a) 3 → ZMod 8) × (MonLe (Fin b) 3 → ZMod 8), cubicGood k hab c := by
  intro v _
  obtain ⟨heb⟩ : Nonempty (IsOrthoEigenBasis (pathHamiltonian (v : PathShell (k + 1)))
      (pathEigenBasis k (v : PathShell (k + 1))) (pathEigenValues k (v : PathShell (k + 1)))) :=
    ⟨isOrthoEigenBasis_pathEigenBasis k _⟩
  have hunit : ∀ j, (∑ x, ‖pathEigenBasis k (v : PathShell (k + 1)) j x‖ ^ 2) = 1 := by
    intro j
    have h1 : finiteComplexInner (pathEigenBasis k (v : PathShell (k + 1)) j)
        (pathEigenBasis k (v : PathShell (k + 1)) j) = 1 := by
      rw [heb.orth j j, if_pos rfl]
    have hcast : finiteComplexInner (pathEigenBasis k (v : PathShell (k + 1)) j)
        (pathEigenBasis k (v : PathShell (k + 1)) j)
        = ((∑ x, ‖pathEigenBasis k (v : PathShell (k + 1)) j x‖ ^ 2 : ℝ) : ℂ) := by
      rw [finiteComplexInner, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Complex.normSq_eq_conj_mul_self, Complex.sq_norm]
    rw [hcast] at h1
    exact_mod_cast h1
  obtain ⟨c, hc⟩ := exists_prodPolyEval_collision_le_four_div (ιA := Fin a) (ιB := Fin b)
    (ι := FiniteQubitConfiguration (Fin (k + 3))) 3 (by norm_num)
    (bipartiteFamily hab (pathEigenBasis k (v : PathShell (k + 1))))
    (fun j => sum_normSq_bipartiteFamily hab hunit j) (card_regSplit hab)
  refine Set.mem_iUnion.mpr ⟨c, ?_⟩
  show (∑ j, ‖finiteComplexInner (pathEigenBasis k (v : PathShell (k + 1)) j)
      (cubicProductSeed k hab c)‖ ^ 4) ≤ _
  refine le_trans (le_of_eq ?_) hc
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cubicProductSeed, ← finiteComplexInner_bipartiteFamily]

/-- **One product cubic seed and one nondegenerate weak-cut direction.** -/
theorem exists_weakCut_fixed_pair (hab : a + b = k + 3) (e : Fin (k + 2))
    {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ∃ (c : (MonLe (Fin a) 3 → ZMod 8) × (MonLe (Fin b) 3 → ZMod 8))
      (v : sphere (0 : PathShell (k + 1)) 1),
      v ∈ edgeSmall e x ∧ v ∈ cubicGood k hab c ∧ v ∉ pathBadSphere k := by
  classical
  obtain ⟨C, c₁, hc₁, -, -, hlower⟩ := exists_edgeSmall_tail_bounds (n := k + 1) e
  have hUpos : 0 < pathShellProb (edgeSmall e x) :=
    lt_of_lt_of_le (by positivity) (hlower x hx0.le hx1)
  obtain ⟨c₀, hc₀⟩ := exists_pos_inter_of_cover
    (A := edgeSmall e x) (G := cubicGood k hab)
    (fun v _ => subset_iUnion_cubicGood k hab (Set.mem_univ v)) hUpos
  obtain ⟨v, hv, hvbad⟩ := exists_mem_notMem_pathBadSphere k hc₀
  exact ⟨c₀, v, hv.1, hv.2, hvbad⟩

end Selection


section Speed

variable {k : ℕ}

/-- **The orbit speed of the path shell.**  A unit shell direction generates an evolution of speed
at most the square root of the coefficient dimension. -/
theorem norm_pathHamiltonian_le_sqrt (v : sphere (0 : PathShell (k + 1)) 1) :
    ‖pathHamiltonian (v : PathShell (k + 1))‖
      ≤ Real.sqrt (Fintype.card (PathLabel (k + 1))) := by
  classical
  have hnorm : ‖(v : PathShell (k + 1))‖ = 1 := by
    have := v.2
    rw [mem_sphere_iff_norm, sub_zero] at this
    exact this
  have hsum : Real.sqrt (∑ l, (WithLp.ofLp (v : PathShell (k + 1)) l) ^ 2) = 1 := by
    have h1 : ‖(v : PathShell (k + 1))‖
        = Real.sqrt (∑ l, (WithLp.ofLp (v : PathShell (k + 1)) l) ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      refine congrArg Real.sqrt (Finset.sum_congr rfl fun l _ => ?_)
      rw [Real.norm_eq_abs, sq_abs]
    rw [← h1]
    exact hnorm
  rw [pathHamiltonian_eq_sum]
  refine le_trans (l2_opNorm_pauliCombination_le (pathWord (n := k + 1))
    (fun l => WithLp.ofLp (v : PathShell (k + 1)) l)) ?_
  rw [hsum, mul_one]

theorem sqrt_card_pathLabel_pos :
    0 < Real.sqrt (Fintype.card (PathLabel (k + 1))) := by
  refine Real.sqrt_pos.mpr ?_
  have : 0 < Fintype.card (PathLabel (k + 1)) := Fintype.card_pos
  exact_mod_cast this

end Speed


section Capstone

variable (k : ℕ) {a b : ℕ}

/-- **Theorem C: a weak cut delays the onset while the later plateau, the recurrence and the
locality are unaffected.**  One product cubic-phase seed and one unit shell direction can be fixed
together so that the split synthesis cap survives the whole prescribed delay, the evolution is hard
for the dictionary at *every* instant of arbitrarily late windows of length `W`, and the orbit
returns arbitrarily close to the seed after every time. -/
theorem exists_weakCut_delayed_plateau (hab : a + b = k + 3)
    {Γ : Type*}
    (act : Γ → EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (k + 3))) →
      EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (k + 3))))
    (chi : EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (k + 3))))
    {eta eps : ℝ} {S : ℕ} (hmargin : eta < eps) (edge : Fin (k + 2))
    (hcert : ∀ c : (MonLe (Fin a) 3 → ZMod 8) × (MonLe (Fin b) 3 → ZMod 8),
      ∀ u : PathShell (k + 1), ∀ s : ℝ, ∃ w : List Γ, w.length ≤ S ∧
        dist (orbitState (pathHamiltonianCut u edge) (eucVec (cubicProductSeed k hab c)) s)
          (wordAct act w chi) ≤ eta)
    {L : ℝ} (hL : (eps - eta) / 3 ≤ L)
    {epsn epsw : ℝ} (hepsn : 0 ≤ epsn) (hgap : epsn < epsw) (hepsw : epsw < 1)
    {r : ℕ} (hr : 1 ≤ r)
    (hscale : 16 * (4 / ((Fintype.card (Fin a → Bool) : ℝ) * Fintype.card (Fin b → Bool)))
      / (1 - epsw ^ 2) ^ 2 ≤ 1 / (2 * r))
    {C : Type} [Fintype C] [Nonempty C]
    (Z : C → (FiniteQubitConfiguration (Fin (k + 3)) → ℂ))
    (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1)
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcardC : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2)
    (W : ℝ)
    (hW : ((plateauGridCount W ((epsw - epsn) /
        Real.sqrt (Fintype.card (PathLabel (k + 1)))) : ℕ) : ℝ) *
      (2 : ℝ) ^ (-((r : ℝ) / 2)) < 1) :
    ∃ (c : (MonLe (Fin a) 3 → ZMod 8) × (MonLe (Fin b) 3 → ZMod 8))
      (v : sphere (0 : PathShell (k + 1)) 1),
      (∀ t : ℝ, 0 ≤ t → t ≤ L →
        approxComplexity act chi eps (orbitState (pathHamiltonian (v : PathShell (k + 1)))
          (eucVec (cubicProductSeed k hab c)) t) ≤ S)
      ∧ (∀ A : ℝ, ∃ t₀, A < t₀ ∧ ∀ u ∈ Set.Icc t₀ (t₀ + W),
          u ∉ metricEasySet (pathHamiltonian (v : PathShell (k + 1)))
            (cubicProductSeed k hab c) epsn Z)
      ∧ (∀ ρ : ℝ, 0 < ρ → ∀ A : ℝ, ∃ s' : ℝ, A < s' ∧ 1 - ρ ≤ ‖finiteComplexInner
          (unitaryEvolution (pathHamiltonian (v : PathShell (k + 1))) s' *ᵥ
            cubicProductSeed k hab c) (cubicProductSeed k hab c)‖) := by
  classical
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith) hL
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = (eps - eta) / (3 * L) := ⟨_, rfl⟩
  have hxpos : 0 < x := by
    rw [hxdef]
    exact div_pos (by linarith) (by linarith)
  have hx1 : x ≤ 1 := by
    rw [hxdef, div_le_one (by positivity)]
    linarith [(div_le_iff₀ (by norm_num : (0:ℝ) < 3)).mp hL]
  obtain ⟨c, v, hvU, hvgood, hvbad⟩ := exists_weakCut_fixed_pair k hab edge hxpos hx1
  refine ⟨c, v, ?_, ?_, ?_⟩
  · have hψ : ‖eucVec (cubicProductSeed k hab c)‖ = 1 :=
      norm_eucVec_eq_one (finiteComplexInner_cubicProductSeed k hab c)
    have hsub := edgeSmall_subset_delayEvent (eps := eps) act chi
      (eucVec (cubicProductSeed k hab c)) hψ edge (hcert c) hLpos
    rw [← hxdef] at hsub
    exact hsub hvU
  · intro A
    have heb := isOrthoEigenBasis_pathEigenBasis k (v : PathShell (k + 1))
    have hmax := maximallyProjectiveEnergy_pathEigenValues k hvbad
    have hcoll : occupationCollision (fun j =>
        ‖eigenCoords (pathEigenBasis k (v : PathShell (k + 1)))
          (cubicProductSeed k hab c) j‖ ^ 2)
        ≤ 4 / ((Fintype.card (Fin a → Bool) : ℝ) * Fintype.card (Fin b → Bool)) := by
      refine le_trans (le_of_eq ?_) hvgood
      rw [occupationCollision]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [eigenCoords, ← pow_mul]
    exact exists_late_hardWindow heb hmax (fun _ => false)
      (isSelfAdjoint_pathHamiltonian _) (finiteComplexInner_cubicProductSeed k hab c) hZ
      hepsn hgap hepsw sqrt_card_pathLabel_pos (norm_pathHamiltonian_le_sqrt v) hr hcoll
      hscale hM hcardC hs W hW A
  · intro ρ hρ A
    have heb := isOrthoEigenBasis_pathEigenBasis k (v : PathShell (k + 1))
    have hmax := maximallyProjectiveEnergy_pathEigenValues k hvbad
    exact exists_late_seed_recurrence heb hmax.injective hmax (fun _ => false)
      (cubicProductSeed k hab c) (finiteComplexInner_cubicProductSeed k hab c) hρ A

end Capstone

end GaloisForLFunctions.HTGeometry

end
