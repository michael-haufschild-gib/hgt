import GaloisForLFunctions.HTGeometry.OnePowerCanonicalProductHypertranscendence
import GaloisForLFunctions.HTGeometry.GaugeReductionToMultiplicative

/-!
# Finite-jet indistinguishability

Every prescribed finite jet at the origin is realized both by a differentially algebraic germ and
by a hypertranscendental one: a polynomial realizes the jet, and adding the same polynomial
correction to an entire hypertranscendental function realizes it again without changing the
hypertranscendence.  Hence no finite-jet observer can decide hypertranscendence.
-/

open scoped Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open _root_.HTGeometry

noncomputable section

/-- The `j`-th jet coordinate at the origin. -/
def jetAtZero (j : ℕ) (f : ℂ → ℂ) : ℂ := iteratedDeriv j f 0

/-- The interpolating polynomial of a prescribed finite jet. -/
noncomputable def finiteJetPolynomial (r : ℕ) (c : ℕ → ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (r + 1), Polynomial.C (c k / (Nat.factorial k : ℂ)) * Polynomial.X ^ k

theorem iteratedDeriv_polynomial_eval_zero (Q : Polynomial ℂ) (j : ℕ) :
    iteratedDeriv j (fun z => Polynomial.eval z Q) 0
      = (Nat.factorial j : ℂ) * Q.coeff j := by
  rw [iteratedDeriv_polynomial_eval Q j 0, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self]

theorem jetAtZero_finiteJetPolynomial (r : ℕ) (c : ℕ → ℂ) {j : ℕ} (hj : j ≤ r) :
    jetAtZero j (fun z => Polynomial.eval z (finiteJetPolynomial r c)) = c j := by
  rw [jetAtZero, iteratedDeriv_polynomial_eval_zero]
  have hcoeff : (finiteJetPolynomial r c).coeff j = c j / (Nat.factorial j : ℂ) := by
    rw [finiteJetPolynomial, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro k _ hkj
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hkj), mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  rw [hcoeff]
  have hfac : (Nat.factorial j : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  field_simp

/-- An entire hypertranscendental witness. -/
noncomputable def entireHypertranscendentalWitness : ℂ → ℂ := powerCanonicalProduct 1

theorem hypertranscendental_entireHypertranscendentalWitness :
    Hypertranscendental entireHypertranscendentalWitness :=
  hypertranscendental_powerCanonicalProduct_one

theorem analyticOnNhd_entireHypertranscendentalWitness :
    AnalyticOnNhd ℂ entireHypertranscendentalWitness Set.univ :=
  analyticOnNhd_powerCanonicalProduct one_pos

theorem differentiable_entireHypertranscendentalWitness :
    Differentiable ℂ entireHypertranscendentalWitness := fun z =>
  (analyticOnNhd_entireHypertranscendentalWitness z (Set.mem_univ z)).differentiableAt

theorem differentiable_iteratedDeriv_witness (j : ℕ) :
    Differentiable ℂ (iteratedDeriv j entireHypertranscendentalWitness) :=
  differentiable_iteratedDeriv_of_entire analyticOnNhd_entireHypertranscendentalWitness j

/-- A function with a vanishing iterated derivative satisfies an algebraic differential
equation. -/
theorem differentiallyAlgebraic_of_iteratedDeriv_eq_zero {f : ℂ → ℂ} {m : ℕ}
    (h : ∀ z, iteratedDeriv m f z = 0) : DifferentiallyAlgebraic f := by
  refine ⟨m, MvPolynomial.X ⟨m + 1, by omega⟩, MvPolynomial.X_ne_zero _, fun z => ?_⟩
  rw [MvPolynomial.eval_X]
  have hval : (Fin.cons z (fun j : Fin (m + 1) => iteratedDeriv (j : ℕ) f z) :
      Fin (m + 2) → ℂ) ⟨m + 1, by omega⟩ = iteratedDeriv m f z := by
    rw [show (⟨m + 1, by omega⟩ : Fin (m + 2)) = Fin.succ ⟨m, by omega⟩ from rfl, Fin.cons_succ]
  rw [hval, h z]

theorem natDegree_finiteJetPolynomial_le (r : ℕ) (c : ℕ → ℂ) :
    (finiteJetPolynomial r c).natDegree ≤ r := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  rw [Polynomial.natDegree_X_pow]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)

theorem differentiallyAlgebraic_finiteJetPolynomial (r : ℕ) (c : ℕ → ℂ) :
    DifferentiallyAlgebraic (fun z => Polynomial.eval z (finiteJetPolynomial r c)) := by
  refine differentiallyAlgebraic_of_iteratedDeriv_eq_zero (m := r + 1) fun z => ?_
  rw [iteratedDeriv_polynomial_eval]
  rw [Polynomial.iterate_derivative_eq_zero
    (Nat.lt_succ_of_le (natDegree_finiteJetPolynomial_le r c))]
  simp

/-- **Theorem 4.1, exact finite-jet indistinguishability.**  Every prescribed finite jet at the
origin is realized both by a differentially algebraic function and by a hypertranscendental one. -/
theorem exists_finiteJet_da_and_ht (r : ℕ) (c : ℕ → ℂ) :
    ∃ p h : ℂ → ℂ,
      (∀ j ≤ r, jetAtZero j p = c j) ∧ (∀ j ≤ r, jetAtZero j h = c j) ∧
      DifferentiallyAlgebraic p ∧ Hypertranscendental h := by
  classical
  set W : ℂ → ℂ := entireHypertranscendentalWitness with hWdef
  set P : Polynomial ℂ := finiteJetPolynomial r c with hPdef
  set T : Polynomial ℂ := finiteJetPolynomial r (fun k => jetAtZero k W) with hTdef
  refine ⟨fun z => Polynomial.eval z P, fun z => W z + Polynomial.eval z (P - T), ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact jetAtZero_finiteJetPolynomial r c hj
  · intro j hj
    have hjet := iteratedDeriv_add_polynomial W differentiable_iteratedDeriv_witness (P - T) j 0
    have hpoly : Polynomial.eval 0 (Polynomial.derivative^[j] (P - T))
        = jetAtZero j (fun z => Polynomial.eval z (P - T)) := by
      rw [jetAtZero, iteratedDeriv_polynomial_eval]
    have hsplit : jetAtZero j (fun z => Polynomial.eval z (P - T))
        = jetAtZero j (fun z => Polynomial.eval z P)
          - jetAtZero j (fun z => Polynomial.eval z T) := by
      rw [jetAtZero, jetAtZero, jetAtZero, iteratedDeriv_polynomial_eval_zero,
        iteratedDeriv_polynomial_eval_zero, iteratedDeriv_polynomial_eval_zero,
        Polynomial.coeff_sub]
      ring
    rw [jetAtZero, hjet, hpoly, hsplit, jetAtZero_finiteJetPolynomial r c hj,
      jetAtZero_finiteJetPolynomial r (fun k => jetAtZero k W) hj]
    simp [jetAtZero]
  · exact differentiallyAlgebraic_finiteJetPolynomial r c
  · intro hDA
    exact hypertranscendental_entireHypertranscendentalWitness
      (differentiallyAlgebraic_add_polynomial differentiable_iteratedDeriv_witness (P - T) hDA)

/-! ## The finite-jet topology -/

/-- Germs at the origin, carrying the finite-jet topology below. -/
def JetSpace : Type := ℂ → ℂ

/-- The tautological map onto the finite-jet carrier. -/
def toJetSpace (f : ℂ → ℂ) : JetSpace := f

/-- The tautological map off the finite-jet carrier. -/
def ofJetSpace (f : JetSpace) : ℂ → ℂ := f

@[simp]
theorem ofJetSpace_toJetSpace (f : ℂ → ℂ) : ofJetSpace (toJetSpace f) = f := rfl

/-- The full jet of a germ at the origin. -/
def finiteJetVector (f : JetSpace) : ℕ → ℂ := fun j => jetAtZero j (ofJetSpace f)

/-- The finite-jet topology: the initial topology of the full jet map, equivalently of all the
finite jet maps `f ↦ (f 0, …, f^{(r)} 0)`. -/
instance : TopologicalSpace JetSpace := TopologicalSpace.induced finiteJetVector inferInstance

theorem continuous_jetVector : Continuous finiteJetVector := continuous_induced_dom

theorem continuous_jetAtZero (j : ℕ) :
    Continuous fun f : JetSpace => jetAtZero j (ofJetSpace f) :=
  (continuous_apply j).comp continuous_jetVector

theorem nhds_jetSpace (g : JetSpace) :
    nhds g = Filter.comap finiteJetVector (nhds (finiteJetVector g)) :=
  nhds_induced finiteJetVector g

/-- A property realizable on every exact finite jet fiber is dense in the finite-jet topology. -/
theorem exists_mem_of_mem_nhds {P : (ℂ → ℂ) → Prop}
    (hP : ∀ (r : ℕ) (c : ℕ → ℂ), ∃ f : ℂ → ℂ, (∀ j ≤ r, jetAtZero j f = c j) ∧ P f)
    (g : JetSpace) {s : Set JetSpace} (hs : s ∈ nhds g) :
    ∃ f ∈ s, P (ofJetSpace f) := by
  rw [nhds_jetSpace, Filter.mem_comap] at hs
  obtain ⟨t, ht, hts⟩ := hs
  rw [nhds_pi, Filter.mem_pi] at ht
  obtain ⟨I, hI, u, hu, hut⟩ := ht
  obtain ⟨r, hr⟩ := hI.bddAbove
  obtain ⟨f, hjf, hPf⟩ := hP r (finiteJetVector g)
  refine ⟨toJetSpace f, hts ?_, hPf⟩
  refine hut ?_
  intro i hi
  have hji : finiteJetVector (toJetSpace f) i = finiteJetVector g i := hjf i (hr hi)
  rw [hji]
  exact mem_of_mem_nhds (hu i)

/-- **Corollary 4.2, first half.**  The differentially algebraic germs are dense in the
finite-jet topology. -/
theorem dense_differentiallyAlgebraic :
    Dense {f : JetSpace | DifferentiallyAlgebraic (ofJetSpace f)} := by
  intro g
  rw [mem_closure_iff_nhds]
  intro t ht
  obtain ⟨f, hf, hPf⟩ :=
    exists_mem_of_mem_nhds (P := DifferentiallyAlgebraic)
      (fun r c => ⟨fun z => Polynomial.eval z (finiteJetPolynomial r c),
        fun j hj => jetAtZero_finiteJetPolynomial r c hj, differentiallyAlgebraic_finiteJetPolynomial r c⟩)
      g ht
  exact ⟨f, hf, hPf⟩

/-- **Corollary 4.2, second half.**  The hypertranscendental germs are dense in the finite-jet
topology. -/
theorem dense_hypertranscendental :
    Dense {f : JetSpace | Hypertranscendental (ofJetSpace f)} := by
  intro g
  rw [mem_closure_iff_nhds]
  intro t ht
  obtain ⟨f, hf, hPf⟩ :=
    exists_mem_of_mem_nhds (P := Hypertranscendental)
      (fun r c => by
        obtain ⟨p, h, -, hjh, -, hht⟩ := exists_finiteJet_da_and_ht r c
        exact ⟨h, hjh, hht⟩)
      g ht
  exact ⟨f, hf, hPf⟩

/-- Neither class has interior in the finite-jet topology. -/
theorem interior_differentiallyAlgebraic_eq_empty :
    interior {f : JetSpace | DifferentiallyAlgebraic (ofJetSpace f)} = ∅ := by
  rw [interior_eq_empty_iff_dense_compl]
  exact dense_hypertranscendental

theorem interior_hypertranscendental_eq_empty :
    interior {f : JetSpace | Hypertranscendental (ofJetSpace f)} = ∅ := by
  rw [interior_eq_empty_iff_dense_compl]
  have hcompl : {f : JetSpace | Hypertranscendental (ofJetSpace f)}ᶜ
      = {f : JetSpace | DifferentiallyAlgebraic (ofJetSpace f)} := by
    ext f
    simp [Hypertranscendental, not_not]
  rw [hcompl]
  exact dense_differentiallyAlgebraic

theorem exists_hypertranscendental_jetSpace :
    ∃ f : JetSpace, Hypertranscendental (ofJetSpace f) :=
  ⟨toJetSpace entireHypertranscendentalWitness,
    hypertranscendental_entireHypertranscendentalWitness⟩

theorem exists_differentiallyAlgebraic_jetSpace :
    ∃ f : JetSpace, DifferentiallyAlgebraic (ofJetSpace f) :=
  ⟨toJetSpace (fun z => Polynomial.eval z (finiteJetPolynomial 0 fun _ => 0)),
    differentiallyAlgebraic_finiteJetPolynomial 0 _⟩

/-- Neither class is closed in the finite-jet topology. -/
theorem not_isClosed_differentiallyAlgebraic :
    ¬ IsClosed {f : JetSpace | DifferentiallyAlgebraic (ofJetSpace f)} := by
  intro hclosed
  obtain ⟨f, hf⟩ := exists_hypertranscendental_jetSpace
  have huniv : {f : JetSpace | DifferentiallyAlgebraic (ofJetSpace f)} = Set.univ := by
    rw [← hclosed.closure_eq]
    exact dense_differentiallyAlgebraic.closure_eq
  have : f ∈ {f : JetSpace | DifferentiallyAlgebraic (ofJetSpace f)} := by
    rw [huniv]; trivial
  exact hf this

theorem not_isClosed_hypertranscendental :
    ¬ IsClosed {f : JetSpace | Hypertranscendental (ofJetSpace f)} := by
  intro hclosed
  obtain ⟨f, hf⟩ := exists_differentiallyAlgebraic_jetSpace
  have huniv : {f : JetSpace | Hypertranscendental (ofJetSpace f)} = Set.univ := by
    rw [← hclosed.closure_eq]
    exact dense_hypertranscendental.closure_eq
  have : f ∈ {f : JetSpace | Hypertranscendental (ofJetSpace f)} := by
    rw [huniv]; trivial
  exact this hf

/-- **Corollary 4.3, no continuous finite-precision classifier.**  No continuous map to a
Hausdorff space separates the differentially algebraic germs from the hypertranscendental ones. -/
theorem no_continuous_classifier {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (Φ : JetSpace → Y) (hΦ : Continuous Φ) {yDA yHT : Y} (hne : yDA ≠ yHT)
    (hDA : ∀ f : JetSpace, DifferentiallyAlgebraic (ofJetSpace f) → Φ f = yDA)
    (hHT : ∀ f : JetSpace, Hypertranscendental (ofJetSpace f) → Φ f = yHT) : False := by
  have hconst : Φ = fun _ => yDA :=
    hΦ.ext_on dense_differentiallyAlgebraic continuous_const fun f hf => hDA f hf
  obtain ⟨f, hf⟩ := exists_hypertranscendental_jetSpace
  have h1 : Φ f = yHT := hHT f hf
  rw [hconst] at h1
  exact hne h1

end

end GaloisForLFunctions.HTGeometry
