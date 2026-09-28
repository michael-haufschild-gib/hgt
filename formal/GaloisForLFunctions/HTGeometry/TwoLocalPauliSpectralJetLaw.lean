import GaloisForLFunctions.HTGeometry.TwoLocalCommonSpectralChartJetLaw
import GaloisForLFunctions.HTGeometry.PauliTwoLocalEmbedding
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Spectral jets in the full two-local Pauli family

The explicit star responses are genuine iterated Fréchet derivatives of the full
real weight-two Pauli coefficient family, not derivatives of an unrelated spectral
assignment. Every nonzero balanced real spectral covector is detected at the same
diagonal reference by a derivative of order at most `n + 1`.

The reference is a sum of onsite Z terms. Every matrix in the parameter family is
Hermitian, and the analytic spectral branches are real near the reference.
These are local finite-order certificates; no growing-replica, circuit-tube,
fibre-multiplicity, or first-return estimate is asserted here.
-/

open Filter Topology
open scoped BigOperators Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Recursive coordinate derivatives equal evaluation of the iterated Fréchet derivative. -/
theorem orderedStarCouplingDeriv_eq_iteratedFDeriv
    {I : Type*} [Fintype I] [DecidableEq I]
    (sites : List I) (f : (I → ℝ) → ℝ) (c : I → ℝ)
    (hf : ContDiffAt ℝ (sites.length : ℕ) f c) :
    orderedStarCouplingDeriv sites f c =
      iteratedFDeriv ℝ sites.length f c (fun j => Pi.single (sites.get j) 1) := by
  induction sites generalizing c with
  | nil => simp [orderedStarCouplingDeriv, iteratedFDeriv_zero_apply]
  | cons i sites ih =>
    let dirs : Fin sites.length → (I → ℝ) := fun j => Pi.single (sites.get j) 1
    have hft : ContDiffAt ℝ (sites.length : ℕ) f c := hf.of_le (by simp)
    have hnear := hft.eventually (by simp)
    have hline := hasDerivAt_update c i (c i)
    have heq :
        (fun t => orderedStarCouplingDeriv sites f (Function.update c i t)) =ᶠ[𝓝 (c i)]
          (fun t => iteratedFDeriv ℝ sites.length f (Function.update c i t) dirs) := by
      have ht := hline.continuousAt.tendsto.eventually (by simpa using hnear)
      filter_upwards [ht] with t ht
      exact ih _ ht
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ sites.length f) c :=
      hf.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self sites.length)
    have hdline := HasFDerivAt.comp_hasDerivAt (c i)
      (by simpa using hdiff.hasFDerivAt) hline
    have hev := HasFDerivAt.comp_hasDerivAt (c i)
      (ContinuousLinearMap.hasFDerivAt
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin sites.length => (I → ℝ)) ℝ dirs)) hdline
    change HasDerivAt (fun t => iteratedFDeriv ℝ sites.length f (Function.update c i t) dirs)
      (fderiv ℝ (iteratedFDeriv ℝ sites.length f) c (Pi.single i 1) dirs) (c i) at hev
    have hdirs : (fun j : Fin (i :: sites).length => Pi.single ((i :: sites).get j) (1 : ℝ)) =
        @Fin.cons sites.length (fun _ => I → ℝ) (Pi.single i 1) dirs := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [dirs]
    change deriv (fun t => orderedStarCouplingDeriv sites f (Function.update c i t)) (c i) = _
    rw [heq.deriv_eq, hev.deriv, hdirs]
    rfl

/-- Add the transverse parameter as the `none` coordinate. -/
def starOptionLift {I : Type*} (c : I → ℝ) (u : ℝ) : Option I → ℝ :=
  fun j => j.elim u c

@[simp] theorem starOptionLift_zero {I : Type*} : starOptionLift (0 : I → ℝ) 0 = 0 := by
  funext j
  cases j <;> rfl

private theorem starOptionLift_update_some {I : Type*} [DecidableEq I]
    (c : I → ℝ) (u t : ℝ) (i : I) :
    starOptionLift (Function.update c i t) u = Function.update (starOptionLift c u) (some i) t := by
  funext j
  cases j with
  | none => simp [starOptionLift]
  | some j => by_cases h : j = i <;> simp [starOptionLift, h]

private theorem starOptionLift_update_none {I : Type*} [DecidableEq I]
    (c : I → ℝ) (u t : ℝ) :
    starOptionLift c t = Function.update (starOptionLift c u) none t := by
  funext j
  cases j <;> simp [starOptionLift]

private theorem orderedStarCouplingDeriv_append {I : Type*} [DecidableEq I]
    (s t : List I) (f : (I → ℝ) → ℝ) :
    orderedStarCouplingDeriv (s ++ t) f =
      orderedStarCouplingDeriv s (orderedStarCouplingDeriv t f) := by
  induction s with
  | nil => rfl
  | cons i s ih => simp [orderedStarCouplingDeriv, ih]

private theorem orderedStarCouplingDeriv_some {I : Type*} [DecidableEq I]
    (s : List I) (f : (Option I → ℝ) → ℝ) (c : I → ℝ) (u : ℝ) :
    orderedStarCouplingDeriv s (fun c => f (starOptionLift c u)) c =
      orderedStarCouplingDeriv (s.map some) f (starOptionLift c u) := by
  induction s generalizing c with
  | nil => rfl
  | cons i s ih =>
    simp only [List.map_cons, orderedStarCouplingDeriv, starOptionLift, Option.elim_some]
    congr 1
    funext t
    simpa only [starOptionLift_update_some] using ih (Function.update c i t)

private theorem orderedStarCouplingDeriv_none_twice {I : Type*} [DecidableEq I]
    (f : (Option I → ℝ) → ℝ) (c : I → ℝ) (u : ℝ) :
    orderedStarCouplingDeriv [none, none] f (starOptionLift c u) =
      deriv (deriv (fun t => f (starOptionLift c t))) u := by
  simp only [orderedStarCouplingDeriv]
  simp_rw [← starOptionLift_update_none]
  rfl

/-- Coupling derivatives after two transverse derivatives form one ordered jet word. -/
theorem mixedStarSpectralDeriv_eq_iteratedFDeriv
    {I : Type*} [Fintype I] [DecidableEq I]
    (s : List I) (f : (Option I → ℝ) → ℝ) (c : I → ℝ) (u : ℝ)
    (hf : ContDiffAt ℝ ((s.length + 2 : ℕ) : ℕ) f (starOptionLift c u)) :
    orderedStarCouplingDeriv s
        (fun c => deriv (deriv (fun t => f (starOptionLift c t))) u) c =
      iteratedFDeriv ℝ (s.map some ++ [none, none]).length f (starOptionLift c u)
        (fun j => Pi.single ((s.map some ++ [none, none]).get j) 1) := by
  rw [← orderedStarCouplingDeriv_eq_iteratedFDeriv _ _ _ (by simpa using hf),
    orderedStarCouplingDeriv_append, ← orderedStarCouplingDeriv_some]
  congr 1
  funext c
  exact (orderedStarCouplingDeriv_none_twice f c u).symm

noncomputable local instance localJetBoolCubeFintype
    {I : Type*} [Fintype I] : Fintype (I → Bool) := Fintype.ofFinite _

/-- All real Pauli perturbations of weight at most two, about the common reference. -/
def commonReferencePauliMatrix (n : ℕ) (p : PauliBoundedLabel n 2 → ℝ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  commonReferenceSpectralMatrix n + ∑ P, (p P : ℂ) • finitePauliMatrix P.1

@[simp] theorem commonReferencePauliMatrix_zero (n : ℕ) :
    commonReferencePauliMatrix n 0 = commonReferenceSpectralMatrix n := by
  simp [commonReferencePauliMatrix]

/-- The fixed reference introduces only onsite terms, not a nonlocal offset. -/
theorem commonReferenceSpectralMatrix_eq_pauli (n : ℕ) :
    commonReferenceSpectralMatrix n =
      ∑ i : Fin n, (starJetReferenceField n i : ℂ) • finitePauliMatrix (pauliZLabel i) := by
  ext x y
  simp only [commonReferenceSpectralMatrix, Matrix.diagonal_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, finitePauliMatrix_pauliZLabel]
  by_cases h : x = y
  · subst y
    simp only [ite_true, starJetReferenceEnergy, Complex.ofReal_sum, Complex.ofReal_mul]
    apply Finset.sum_congr rfl
    intro i _
    cases hx : x i <;> simp [siteSign, zSign, hx]
  · simp [h]

theorem commonReferencePauliMatrix_isHermitian (n : ℕ) (p : PauliBoundedLabel n 2 → ℝ) :
    (commonReferencePauliMatrix n p).IsHermitian := by
  rw [commonReferencePauliMatrix, commonReferenceSpectralMatrix_eq_pauli]
  apply Matrix.IsHermitian.add
  · exact isSelfAdjoint_sum _ fun i _ =>
      (finitePauliMatrix_isHermitian (pauliZLabel i)).smul (by simp [IsSelfAdjoint])
  · exact isSelfAdjoint_sum _ fun P _ =>
      (finitePauliMatrix_isHermitian P.1).smul (by simp [IsSelfAdjoint])

theorem contDiff_commonReferencePauliMatrix (n : ℕ) :
    ContDiff ℝ ⊤ (commonReferencePauliMatrix n) := by
  unfold commonReferencePauliMatrix
  change ContDiff ℝ ⊤ (fun p : PauliBoundedLabel n 2 → ℝ =>
    commonReferenceSpectralMatrix n + ∑ P, Complex.ofRealCLM (p P) • finitePauliMatrix P.1)
  fun_prop

theorem commonReferencePauli_branch_real (n : ℕ) (x : Fin n → Bool) :
    ∀ᶠ p in 𝓝 (0 : PauliBoundedLabel n 2 → ℝ),
      (commonReferenceSpectralBranch n x (commonReferencePauliMatrix n p)).im = 0 := by
  have ht : Tendsto (commonReferencePauliMatrix n) (𝓝 0)
      (𝓝 (commonReferenceSpectralMatrix n)) := by
    simpa only [commonReferencePauliMatrix_zero] using!
      ((contDiff_commonReferencePauliMatrix n).continuous.continuousAt
        (x := (0 : PauliBoundedLabel n 2 → ℝ))).tendsto
  have hroot := ht.eventually (commonReferenceSpectralBranch_spec n x).2.2
  filter_upwards [hroot] with p hp
  change (Matrix.scalar _ (commonReferenceSpectralBranch n x
    (commonReferencePauliMatrix n p)) - commonReferencePauliMatrix n p).det = 0 at hp
  rw [← Matrix.eval_charpoly, (commonReferencePauliMatrix_isHermitian n p).charpoly_eq,
    Polynomial.eval_prod] at hp
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hp
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hp
  rw [sub_eq_zero.mp hj]
  simp

/-- Embed transverse X and longitudinal ZZ star directions in the full coefficient space. -/
def starPauliDirectionMap {n : ℕ} (i : Fin n) :
    (Option {j : Fin n // j ≠ i} → ℝ) →L[ℝ] (PauliBoundedLabel n 2 → ℝ) :=
  ContinuousLinearMap.pi fun P =>
    (if P.1 = pauliXLabel i then ContinuousLinearMap.proj none else 0) +
    ∑ j : {j : Fin n // j ≠ i},
      if P.1 = pauliZZLabel i j then ContinuousLinearMap.proj (some j) else 0

theorem starPauliDirectionMap_apply {n : ℕ} (i : Fin n)
    (q : Option {j : Fin n // j ≠ i} → ℝ) (P : PauliBoundedLabel n 2) :
    starPauliDirectionMap i q P =
      (if P.1 = pauliXLabel i then q none else 0) +
        ∑ j : {j : Fin n // j ≠ i}, if P.1 = pauliZZLabel i j then q (some j) else 0 := by
  simp only [starPauliDirectionMap, ContinuousLinearMap.pi_apply, _root_.add_apply,
    _root_.sum_apply]
  refine congrArg₂ (· + ·) ?_ ?_
  · split_ifs <;> rfl
  · apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> rfl

theorem commonReferencePauliMatrix_star_expansion {n : ℕ} (i : Fin n)
    (q : Option {j : Fin n // j ≠ i} → ℝ) :
    commonReferencePauliMatrix n (starPauliDirectionMap i q) =
      commonReferenceSpectralMatrix n + (q none : ℂ) • finitePauliMatrix (pauliXLabel i) +
        ∑ j : {j : Fin n // j ≠ i}, (q (some j) : ℂ) • finitePauliMatrix (pauliZZLabel i j) := by
  ext x y
  simp only [commonReferencePauliMatrix, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, starPauliDirectionMap_apply]
  push_cast
  simp only [apply_ite, Complex.ofReal_zero, add_mul, Finset.sum_add_distrib]
  rw [sum_ite_label_mul (by simpa using (pauliWeight_pauliXLabel i).le.trans (by norm_num : 1 ≤ 2))
      (q none : ℂ) (fun L => finitePauliMatrix L x y),
    sum_ite_family_mul (fun j : {j : Fin n // j ≠ i} => pauliZZLabel i j)
      (fun j => pauliWeight_pauliZZLabel_le i j)
      (fun j => (q (some j) : ℂ)) (fun L => finitePauliMatrix L x y)]
  exact (add_assoc _ _ _).symm

theorem commonReferenceStarMatrix_eq_pauli {n : ℕ} (i : Fin n)
    (c : {j : Fin n // j ≠ i} → ℝ) (u : ℝ) :
    commonReferenceStarMatrix i (c, u) =
      commonReferenceSpectralMatrix n + (u : ℂ) • finitePauliMatrix (pauliXLabel i) +
        ∑ j : {j : Fin n // j ≠ i}, (c j : ℂ) • finitePauliMatrix (pauliZZLabel i j) := by
  classical
  rw [← commonReferenceStarMatrix_zero i]
  ext x y
  obtain ⟨⟨b,z⟩, rfl⟩ := (edgeEquiv i).surjective x
  obtain ⟨⟨d,w⟩, rfl⟩ := (edgeEquiv i).surjective y
  have hZZ (j : {j : Fin n // j ≠ i}) :
      finitePauliMatrix (pauliZZLabel i j) (edgeEquiv i (b,z)) (edgeEquiv i (d,w)) =
        if edgeEquiv i (b,z) = edgeEquiv i (d,w) then
          zSign (edgeEquiv i (b,z) i) * zSign (edgeEquiv i (b,z) j) else 0 :=
    finitePauliMatrix_pauliZZLabel (Ne.symm j.property) _ _
  have htoggle_eq (b : Fin 2) :
      boolToggle (edgeEquiv i (b,z)) i =
        edgeEquiv i (finTwoEquiv.symm (!(finTwoEquiv b)), z) := by
    rw [edgeEquiv_apply, boolToggle_edgeState, edgeEquiv_apply, Equiv.apply_symm_apply]
  have henv (a : Bool) (j : {j : Fin n // j ≠ i}) : edgeState i z a j = z j :=
    edgeState_of_ne i z a j.property
  simp only [commonReferenceStarMatrix, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Prod.fst_zero, Prod.snd_zero, Complex.ofReal_zero,
    finitePauliMatrix_pauliXLabel, hZZ, htoggle_eq, (edgeEquiv i).injective.eq_iff]
  by_cases hzw : z = w
  · subst w
    -- Use a fixed entrywise simp set in all four blocks.
    fin_cases b <;> fin_cases d <;>
      simp only [blockSplitMatrix, splitBlock, twoLocalStarGap, ne_eq,
        mul_ite, mul_neg, mul_one, Complex.ofReal_add, Complex.ofReal_sum,
        Complex.ofReal_sub, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one,
        Matrix.blockDiagonal_apply_eq, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Pi.zero_apply, neg_zero, ite_self, Finset.sum_const_zero, add_zero,
        finTwoEquiv, Equiv.symm_mk, Equiv.coe_fn_mk, Fin.reduceBEq, BEq.rfl,
        Bool.not_false, Bool.not_true, cond_true, cond_false, Prod.mk.injEq,
        zero_ne_one, one_ne_zero, and_true, ↓reduceIte, mul_zero, zero_add,
        zSign, edgeEquiv_zero, edgeEquiv_one, edgeState_self, Bool.false_eq_true,
        henv, neg_neg]
    all_goals
      simp only [apply_ite, Complex.ofReal_neg,
        sub_eq_add_neg, neg_add_rev, ← Finset.sum_neg_distrib, neg_neg]
      ring
  · simp [blockSplitMatrix, Matrix.blockDiagonal_apply, hzw, Ne.symm hzw]

theorem commonReferencePauliMatrix_star {n : ℕ} (i : Fin n)
    (q : Option {j : Fin n // j ≠ i} → ℝ) :
    commonReferencePauliMatrix n (starPauliDirectionMap i q) =
      commonReferenceStarMatrix i ((fun j => q (some j)), q none) := by
  rw [commonReferencePauliMatrix_star_expansion, commonReferenceStarMatrix_eq_pauli]

/-- Real spectral action of the full Pauli family on its common local branch chart. -/
def commonReferencePauliAction {n : ℕ} (k : (Fin n → Bool) → ℝ)
    (p : PauliBoundedLabel n 2 → ℝ) : ℝ :=
  commonReferenceChartAction k (commonReferencePauliMatrix n p)

theorem contDiffAt_commonReferencePauliAction {n : ℕ} (k : (Fin n → Bool) → ℝ) :
    ContDiffAt ℝ ⊤ (commonReferencePauliAction k) 0 := by
  unfold commonReferencePauliAction commonReferenceChartAction
  apply ContDiffAt.sum
  intro x _
  apply contDiffAt_const.mul
  have hbranch : ContDiffAt ℝ ⊤ (commonReferenceSpectralBranch n x)
      (commonReferencePauliMatrix n 0) := by
    rw [commonReferencePauliMatrix_zero]
    exact ((commonReferenceSpectralBranch_spec n x).1.restrictScalars (𝕜 := ℝ)).contDiffAt
  exact Complex.reCLM.contDiff.contDiffAt.comp 0
    (hbranch.comp 0 (contDiff_commonReferencePauliMatrix n).contDiffAt)

private theorem iteratedFDeriv_comp_clm_at
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (f : F → ℝ) (x : E) (j : ℕ)
    (hf : ContDiffAt ℝ (j : ℕ) f (L x)) :
    iteratedFDeriv ℝ j (f ∘ L) x =
      (iteratedFDeriv ℝ j f (L x)).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨U, hUs, hU, hx⟩ := mem_nhds_iff.mp hs
  have hpre := hU.preimage L.continuous
  have hcomp := L.iteratedFDerivWithin_comp_right (hfs.mono hUs)
    hU.uniqueDiffOn hpre.uniqueDiffOn hx (le_refl (j : WithTop ℕ∞))
  rw [iteratedFDerivWithin_of_isOpen j hpre (show x ∈ L ⁻¹' U from hx),
    iteratedFDerivWithin_of_isOpen j hU hx] at hcomp
  exact hcomp

/-- One derivative per selected ZZ coupling, followed by two transverse X derivatives. -/
def starSpectralJetWord {n : ℕ} {i : Fin n}
    (S : Finset {j : Fin n // j ≠ i}) : List (Option {j : Fin n // j ≠ i}) :=
  S.toList.map some ++ [none, none]

/-- Exact transfer of the explicit star response to the full-family Fréchet jet. -/
theorem commonReferencePauliAction_star_jet {n : ℕ}
    (k : (Fin n → Bool) → ℝ) (i : Fin n) (S : Finset {j : Fin n // j ≠ i}) :
    iteratedFDeriv ℝ (starSpectralJetWord S).length (commonReferencePauliAction k) 0
        (fun j => starPauliDirectionMap i (Pi.single ((starSpectralJetWord S).get j) 1)) =
      orderedStarCouplingDeriv S.toList
        (fun c => deriv (deriv (commonReferenceRealStarAction k i c)) 0) 0 := by
  let g : (Option {j : Fin n // j ≠ i} → ℝ) → ℝ :=
    commonReferencePauliAction k ∘ starPauliDirectionMap i
  have hg : ContDiffAt ℝ ((S.toList.length + 2 : ℕ) : ℕ) g 0 := by
    have hb : ContDiffAt ℝ ((S.toList.length + 2 : ℕ) : ℕ)
        (commonReferencePauliAction k) (starPauliDirectionMap i 0) := by
      simpa using (contDiffAt_commonReferencePauliAction k).of_le
        (show ((S.toList.length + 2 : ℕ) : WithTop ℕ∞) ≤ ⊤ from le_top)
    exact hb.comp 0 (starPauliDirectionMap i).contDiff.contDiffAt
  have hmixed := mixedStarSpectralDeriv_eq_iteratedFDeriv S.toList g 0 0
    (by simpa only [starOptionLift_zero] using hg)
  have hc : ContDiffAt ℝ ((starSpectralJetWord S).length : ℕ)
      (commonReferencePauliAction k) (starPauliDirectionMap i 0) := by
    simpa using (contDiffAt_commonReferencePauliAction k).of_le
      (show ((starSpectralJetWord S).length : WithTop ℕ∞) ≤ ⊤ from le_top)
  have hcomp := iteratedFDeriv_comp_clm_at (starPauliDirectionMap i)
    (commonReferencePauliAction k) 0 (starSpectralJetWord S).length hc
  have hgeq : (fun c => deriv (deriv (fun t => g (starOptionLift c t))) 0) =
      (fun c => deriv (deriv (fun t => commonReferenceChartAction k
        (commonReferenceStarMatrix i (c,t)))) 0) := by
    funext c
    simp only [g, Function.comp_apply, commonReferencePauliAction,
      commonReferencePauliMatrix_star, starOptionLift, Option.elim_some, Option.elim_none]
  rw [hgeq, commonReferenceChartAction_star_jet] at hmixed
  have hcomp0 := congrArg
    (fun M => M (fun j => Pi.single ((starSpectralJetWord S).get j) (1 : ℝ))) hcomp
  simp only [map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply] at hcomp0
  exact hcomp0.symm.trans (by
    simpa only [g, starSpectralJetWord, starOptionLift_zero] using! hmixed.symm)

/-- Every balanced real spectral covector is detected by a genuine Fréchet derivative
of the full weight-two Pauli family, of total order at most `n+1`. -/
theorem balanced_real_character_fullPauli_jet_detection
    (n : ℕ) (k : (Fin n → Bool) → ℝ)
    (hbalance : ∑ x, k x = 0) (hk : k ≠ 0) :
    ∃ (i : Fin n) (S : Finset {j : Fin n // j ≠ i}),
      (starSpectralJetWord S).length ≤ n + 1 ∧
      Real.sqrt (∑ x, k x ^ (2 : ℕ)) ≤
        |iteratedFDeriv ℝ (starSpectralJetWord S).length (commonReferencePauliAction k) 0
          (fun j => starPauliDirectionMap i (Pi.single ((starSpectralJetWord S).get j) 1))| := by
  obtain ⟨i, S, horder, hbound⟩ :=
    balanced_real_character_commonBase_starJet_detection n k hbalance hk
  refine ⟨i, S, ?_, ?_⟩
  · simpa only [starSpectralJetWord, List.length_append, List.length_map,
      Finset.length_toList, List.length_cons, List.length_nil, Nat.reduceAdd] using horder
  · rw [commonReferencePauliAction_star_jet]
    exact hbound

end
end GaloisForLFunctions.HTGeometry
