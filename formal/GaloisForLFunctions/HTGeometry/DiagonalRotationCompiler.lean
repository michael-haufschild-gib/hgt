/-
# The diagonal carrier is compiled by one rotation per generator

On the diagonal carrier of the path shell the Hamiltonian is a sum of commuting `Z` and `ZZ` words,
so its evolution is a product of `2n+3` diagonal rotations, one per generator.  Discretizing the
rotation angles into `m` equal steps gives a finite alphabet whose depth-`(2n+3)` words reproduce
every carrier endpoint at every time to within `(2n+3)·2π/m`.  The compiler certificate of the
codimension law is therefore a theorem, not a hypothesis: the alphabet is explicit, its size is
`(2n+3)m`, and the word length is `2n+3` for every carrier point and every time.

Main results:
* `diagSignOf`, `pathHamiltonian_embed_eq_diagonal_carrierEnergy` — the carrier Hamiltonian.
* `unitaryEvolution_diagonal` — its evolution.
* `diagAlphabetGate`, `diagAlphabetAct` — the finite alphabet of discretized diagonal rotations.
* `exists_diagonal_compiler` — **the compiler certificate**.
-/
import GaloisForLFunctions.HTGeometry.CoupledShortcutCollision
import GaloisForLFunctions.HTGeometry.PhaseGridApproximation
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

open Matrix Finset Metric _root_.HTGeometry
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-! ## The carrier Hamiltonian and its evolution -/

/-- The `±1` diagonal sign of a diagonal path label. -/
def diagSignOf (l : PathLabel n) (x : FiniteQubitConfiguration (Fin (n + 2))) : ℝ :=
  match l with
  | Sum.inl sq => zSetSign ({sq.1} : Finset (Fin (n + 2))) x
  | Sum.inr eab => zSetSign ({eab.1.castSucc, eab.1.succ} : Finset (Fin (n + 2))) x

theorem abs_diagSignOf (l : PathLabel n) (x : FiniteQubitConfiguration (Fin (n + 2))) :
    |diagSignOf l x| = 1 := by
  cases l with
  | inl sq => exact abs_zSetSign _ _
  | inr eab => exact abs_zSetSign _ _

theorem finitePauliMatrix_pathWord_of_isDiag {l : PathLabel n} (hl : IsDiagLabel l) :
    finitePauliMatrix (pathWord l)
      = Matrix.diagonal fun x => ((diagSignOf l x : ℝ) : ℂ) := by
  cases l with
  | inl sq =>
      have hq : sq.2 = 2 := hl
      obtain ⟨s, q⟩ := sq
      simp only at hq
      subst hq
      ext x y
      rw [show pathWord (Sum.inl (s, (2 : Fin 3))) = onsiteWord s 2 from rfl, onsiteWord_two,
        finitePauliMatrix_pauliZSetLabel, Matrix.diagonal_apply]
      by_cases h : x = y
      · subst h
        simp [diagSignOf]
      · simp [h]
  | inr eab =>
      have hab : eab.2 = (2, 2) := hl
      obtain ⟨e, ab⟩ := eab
      simp only at hab
      subst hab
      ext x y
      rw [show pathWord (Sum.inr (e, ((2 : Fin 3), (2 : Fin 3)))) = couplingWord e (2, 2) from rfl,
        couplingWord_zz, finitePauliMatrix_pauliZSetLabel, Matrix.diagonal_apply]
      by_cases h : x = y
      · subst h
        simp [diagSignOf]
      · simp [h]

/-- The classical energy of a carrier coefficient vector, in patch coordinates. -/
def carrierEnergy (v : EuclideanSpace ℝ (Fin (2 * n + 3)))
    (x : FiniteQubitConfiguration (Fin (n + 2))) : ℝ :=
  ∑ i : Fin (2 * n + 3), v i * diagSignOf (pathPatchEquiv n (Sum.inl i)) x

/-- **The carrier Hamiltonian is diagonal with the classical energies.** -/
theorem pathHamiltonian_embed_eq_diagonal_carrierEnergy
    (v : EuclideanSpace ℝ (Fin (2 * n + 3))) :
    pathHamiltonian (pathPatchIsometry n
        (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * n + 12))))))
      = Matrix.diagonal fun x => ((carrierEnergy v x : ℝ) : ℂ) := by
  classical
  obtain ⟨u, hudef⟩ : ∃ u : PathShell n, u = pathPatchIsometry n
    (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * n + 12))))) := ⟨_, rfl⟩
  rw [← hudef, pathHamiltonian_eq_sum]
  have hsum : ∑ l : PathLabel n, ((u l : ℝ) : ℂ) • finitePauliMatrix (pathWord l)
      = ∑ i : Fin (2 * n + 3),
          ((u (pathPatchEquiv n (Sum.inl i)) : ℝ) : ℂ) •
            finitePauliMatrix (pathWord (pathPatchEquiv n (Sum.inl i))) := by
    rw [← Equiv.sum_comp (pathPatchEquiv n)
      (fun l => ((u l : ℝ) : ℂ) • finitePauliMatrix (pathWord l)), Fintype.sum_sum_type]
    have hzero : ∀ j : Fin (10 * n + 12),
        ((u (pathPatchEquiv n (Sum.inr j)) : ℝ) : ℂ) •
          finitePauliMatrix (pathWord (pathPatchEquiv n (Sum.inr j))) = 0 := by
      intro j
      rw [hudef, pathPatchIsometry_embed_offDiag v (notDiag_pathPatchEquiv_inr j)]
      simp
    rw [Finset.sum_congr rfl (fun j _ => hzero j), Finset.sum_const_zero, add_zero]
  rw [hsum]
  have hterm : ∀ i : Fin (2 * n + 3),
      ((u (pathPatchEquiv n (Sum.inl i)) : ℝ) : ℂ) •
          finitePauliMatrix (pathWord (pathPatchEquiv n (Sum.inl i)))
        = Matrix.diagonal fun x =>
            ((v i * diagSignOf (pathPatchEquiv n (Sum.inl i)) x : ℝ) : ℂ) := by
    intro i
    rw [finitePauliMatrix_pathWord_of_isDiag (isDiag_pathPatchEquiv_inl i),
      show u (pathPatchEquiv n (Sum.inl i)) = v i by
        rw [hudef, ofLp_pathPatchIsometry_embed, Equiv.symm_apply_apply]
        rfl]
    ext x y
    by_cases h : x = y
    · subst h
      simp [Matrix.diagonal_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ h]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  ext x y
  by_cases h : x = y
  · subst h
    rw [Matrix.sum_apply, Matrix.diagonal_apply_eq, carrierEnergy, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.sum_apply, Matrix.diagonal_apply_ne _ h]
    exact Finset.sum_eq_zero fun i _ => by rw [Matrix.diagonal_apply_ne _ h]

variable {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]

/-- **The evolution of a diagonal Hamiltonian**, in phase form. -/
theorem unitaryEvolution_diagonal_phase (E : d → ℝ) (s : ℝ) :
    unitaryEvolution (Matrix.diagonal fun x => ((E x : ℝ) : ℂ)) s
      = Matrix.diagonal fun x => Complex.exp ((-(s * E x) : ℝ) * Complex.I) := by
  rw [unitaryEvolution_diagonal]
  congr 1
  funext x
  congr 1
  push_cast
  ring


/-! ## The discretized diagonal rotation alphabet -/

/-- The alphabet: a carrier generator together with a discretized rotation angle. -/
abbrev DiagAlphabet (n m : ℕ) : Type := Fin (2 * n + 3) × Fin m

/-- The gate matrix of one alphabet letter. -/
def diagAlphabetGate (n m : ℕ) (g : DiagAlphabet n m) :
    Matrix (FiniteQubitConfiguration (Fin (n + 2))) (FiniteQubitConfiguration (Fin (n + 2))) ℂ :=
  Matrix.diagonal fun x => Complex.exp
    ((-(gridAngle m g.2 * diagSignOf (pathPatchEquiv n (Sum.inl g.1)) x) : ℝ) * Complex.I)

/-- Its action on register states. -/
def diagAlphabetAct (n m : ℕ) :
    DiagAlphabet n m → EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2)))
      → EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))) :=
  fun g x => eucVec (diagAlphabetGate n m g *ᵥ WithLp.ofLp x)

theorem wordAct_diagAlphabetAct (m : ℕ)
    (psi : FiniteQubitConfiguration (Fin (n + 2)) → ℂ) :
    ∀ w : List (DiagAlphabet n m),
      wordAct (diagAlphabetAct n m) w (eucVec psi)
        = eucVec (((w.map (diagAlphabetGate n m)).prod) *ᵥ psi)
  | [] => by
      simp only [wordAct_nil, List.map_nil, List.prod_nil, Matrix.one_mulVec]
  | c :: w => by
      rw [wordAct_cons, wordAct_diagAlphabetAct m psi w, diagAlphabetAct]
      simp only [List.map_cons, List.prod_cons]
      rw [← Matrix.mulVec_mulVec]
      rfl

theorem prod_map_diagAlphabetGate (m : ℕ) :
    ∀ w : List (DiagAlphabet n m),
      (w.map (diagAlphabetGate n m)).prod
        = Matrix.diagonal fun x => (w.map fun g =>
            Complex.exp ((-(gridAngle m g.2
              * diagSignOf (pathPatchEquiv n (Sum.inl g.1)) x) : ℝ) * Complex.I)).prod
  | [] => by
      simp
  | c :: w => by
      rw [List.map_cons, List.prod_cons, prod_map_diagAlphabetGate m w, diagAlphabetGate,
        Matrix.diagonal_mul_diagonal]
      congr 1

/-! ## The compiler certificate -/

theorem norm_exp_ofReal_I (t : ℝ) : ‖Complex.exp ((t : ℝ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- **The compiler certificate at a fixed grid.**  Every carrier endpoint at every time is
reproduced by a word of `2n+3` discretized diagonal rotations, to within `(2n+3)·2π/m`. -/
theorem exists_diagAlphabet_word {m : ℕ} (hm : 0 < m)
    {psi : FiniteQubitConfiguration (Fin (n + 2)) → ℂ} (hpsi : ‖eucVec psi‖ = 1)
    (v : EuclideanSpace ℝ (Fin (2 * n + 3))) (s : ℝ) :
    ∃ w : List (DiagAlphabet n m), w.length = 2 * n + 3 ∧
      dist (orbitState (pathHamiltonian (pathPatchIsometry n
              (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * n + 12)))))))
              (eucVec psi) s)
           (wordAct (diagAlphabetAct n m) w (eucVec psi))
        ≤ ((2 * n + 3 : ℕ) : ℝ) * (2 * Real.pi / m) := by
  classical
  choose jj hjj using fun i : Fin (2 * n + 3) => exists_gridIndex hm (s * v i)
  refine ⟨List.ofFn fun i : Fin (2 * n + 3) => (i, jj i), by rw [List.length_ofFn], ?_⟩
  obtain ⟨w, hwdef⟩ : ∃ w : List (DiagAlphabet n m),
    w = List.ofFn fun i : Fin (2 * n + 3) => (i, jj i) := ⟨_, rfl⟩
  rw [← hwdef]
  -- both endpoints are diagonal actions on the uniform seed
  have hleft : orbitState (pathHamiltonian (pathPatchIsometry n
        (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * n + 12)))))))
        (eucVec psi) s
      = eucVec (fun x => Complex.exp ((-(s * carrierEnergy v x) : ℝ) * Complex.I)
          * psi x) := by
    show eucVec (unitaryEvolution (pathHamiltonian (pathPatchIsometry n
      (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * n + 12))))))) s *ᵥ
        psi) = _
    rw [pathHamiltonian_embed_eq_diagonal_carrierEnergy, unitaryEvolution_diagonal_phase]
    congr 1
    funext x
    rw [Matrix.mulVec_diagonal]
  have hright : wordAct (diagAlphabetAct n m) w (eucVec psi)
      = eucVec (fun x => (w.map fun g =>
          Complex.exp ((-(gridAngle m g.2
            * diagSignOf (pathPatchEquiv n (Sum.inl g.1)) x) : ℝ) * Complex.I)).prod
          * psi x) := by
    rw [wordAct_diagAlphabetAct, prod_map_diagAlphabetGate]
    congr 1
    funext x
    rw [Matrix.mulVec_diagonal]
  rw [hleft, hright, dist_eucVec]
  -- the uniform phase bound
  have hphase : ∀ x : FiniteQubitConfiguration (Fin (n + 2)),
      ‖Complex.exp ((-(s * carrierEnergy v x) : ℝ) * Complex.I)
        - (w.map fun g => Complex.exp ((-(gridAngle m g.2
            * diagSignOf (pathPatchEquiv n (Sum.inl g.1)) x) : ℝ) * Complex.I)).prod‖
      ≤ ((2 * n + 3 : ℕ) : ℝ) * (2 * Real.pi / m) := by
    intro x
    obtain ⟨A, hAdef⟩ : ∃ A : Fin (2 * n + 3) → ℂ, A = fun i =>
      Complex.exp ((-((s * v i) * diagSignOf (pathPatchEquiv n (Sum.inl i)) x) : ℝ)
        * Complex.I) := ⟨_, rfl⟩
    obtain ⟨B, hBdef⟩ : ∃ B : Fin (2 * n + 3) → ℂ, B = fun i =>
      Complex.exp ((-(gridAngle m (jj i)
        * diagSignOf (pathPatchEquiv n (Sum.inl i)) x) : ℝ) * Complex.I) := ⟨_, rfl⟩
    have hAprod : Complex.exp ((-(s * carrierEnergy v x) : ℝ) * Complex.I)
        = ((List.finRange (2 * n + 3)).map A).prod := by
      rw [← List.ofFn_eq_map, List.prod_ofFn, hAdef]
      have hsum : (-(s * carrierEnergy v x) : ℝ)
          = ∑ i : Fin (2 * n + 3),
              (-((s * v i) * diagSignOf (pathPatchEquiv n (Sum.inl i)) x)) := by
        rw [carrierEnergy, Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [← Complex.exp_sum]
      congr 1
      rw [hsum, Complex.ofReal_sum, Finset.sum_mul]
    have hBprod : (w.map fun g => Complex.exp ((-(gridAngle m g.2
          * diagSignOf (pathPatchEquiv n (Sum.inl g.1)) x) : ℝ) * Complex.I)).prod
        = ((List.finRange (2 * n + 3)).map B).prod := by
      rw [hwdef, List.map_ofFn, ← List.ofFn_eq_map, hBdef]
      rfl
    have hAnorm : ∀ i, ‖A i‖ = 1 := by
      intro i
      rw [hAdef]
      exact norm_exp_ofReal_I _
    have hBnorm : ∀ i, ‖B i‖ = 1 := by
      intro i
      rw [hBdef]
      exact norm_exp_ofReal_I _
    rw [hAprod, hBprod]
    refine le_trans (norm_prod_sub_prod_le (List.finRange (2 * n + 3)) A B hAnorm hBnorm) ?_
    have hterm : ∀ i : Fin (2 * n + 3), ‖A i - B i‖ ≤ 2 * Real.pi / m := by
      intro i
      rw [hAdef, hBdef]
      exact hjj i _ (abs_diagSignOf _ x)
    calc ((List.finRange (2 * n + 3)).map fun i => ‖A i - B i‖).sum
        = ∑ i : Fin (2 * n + 3), ‖A i - B i‖ := by
          rw [← List.ofFn_eq_map, List.sum_ofFn]
      _ ≤ ∑ _i : Fin (2 * n + 3), (2 * Real.pi / m) := Finset.sum_le_sum fun i _ => hterm i
      _ = ((2 * n + 3 : ℕ) : ℝ) * (2 * Real.pi / m) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- assemble
  have hbound : ∀ x : FiniteQubitConfiguration (Fin (n + 2)),
      ‖Complex.exp ((-(s * carrierEnergy v x) : ℝ) * Complex.I) * psi x
        - (w.map fun g => Complex.exp ((-(gridAngle m g.2
            * diagSignOf (pathPatchEquiv n (Sum.inl g.1)) x) : ℝ) * Complex.I)).prod
          * psi x‖ ^ (2 : ℕ)
      ≤ (((2 * n + 3 : ℕ) : ℝ) * (2 * Real.pi / m)) ^ (2 : ℕ) * ‖psi x‖ ^ (2 : ℕ) := by
    intro x
    rw [← sub_mul, norm_mul, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hnn : (0 : ℝ) ≤ ((2 * n + 3 : ℕ) : ℝ) * (2 * Real.pi / m) := by positivity
    exact pow_le_pow_left₀ (norm_nonneg _) (hphase x) 2
  have hsumseed : ∑ x : FiniteQubitConfiguration (Fin (n + 2)), ‖psi x‖ ^ (2 : ℕ) = 1 := by
    have := norm_eucVec psi
    rw [hpsi] at this
    have hnn : (0 : ℝ) ≤ ∑ x : FiniteQubitConfiguration (Fin (n + 2)),
        ‖psi x‖ ^ (2 : ℕ) := by positivity
    nlinarith [Real.sq_sqrt hnn, this]
  have hfinal : ∑ x : FiniteQubitConfiguration (Fin (n + 2)),
      ‖Complex.exp ((-(s * carrierEnergy v x) : ℝ) * Complex.I) * psi x
        - (w.map fun g => Complex.exp ((-(gridAngle m g.2
            * diagSignOf (pathPatchEquiv n (Sum.inl g.1)) x) : ℝ) * Complex.I)).prod
          * psi x‖ ^ (2 : ℕ)
      ≤ (((2 * n + 3 : ℕ) : ℝ) * (2 * Real.pi / m)) ^ (2 : ℕ) := by
    refine le_trans (Finset.sum_le_sum fun x _ => hbound x) (le_of_eq ?_)
    rw [← Finset.mul_sum, hsumseed, mul_one]
  have hnn : (0 : ℝ) ≤ ((2 * n + 3 : ℕ) : ℝ) * (2 * Real.pi / m) := by positivity
  rw [show ((2 * n + 3 : ℕ) : ℝ) * (2 * Real.pi / m)
      = Real.sqrt ((((2 * n + 3 : ℕ) : ℝ) * (2 * Real.pi / m)) ^ (2 : ℕ)) from
    (Real.sqrt_sq hnn).symm]
  exact Real.sqrt_le_sqrt hfinal


/-- **The compiler certificate.**  For every tolerance there is a finite alphabet of discretized
diagonal rotations whose depth-`(2n+3)` words reproduce every carrier endpoint at every time. -/
theorem exists_diagAlphabet_compiler (n : ℕ)
    {psi : FiniteQubitConfiguration (Fin (n + 2)) → ℂ} (hpsi : ‖eucVec psi‖ = 1)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ m : ℕ, 0 < m ∧ ∀ (v : EuclideanSpace ℝ (Fin (2 * n + 3))) (s : ℝ),
      ∃ w : List (DiagAlphabet n m), w.length ≤ 2 * n + 3 ∧
        dist (orbitState (pathHamiltonian (pathPatchIsometry n
                (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * n + 12)))))))
                (eucVec psi) s)
             (wordAct (diagAlphabetAct n m) w (eucVec psi)) ≤ eta := by
  classical
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈((2 * n + 3 : ℕ) : ℝ) * (2 * Real.pi) / eta⌉₊ + 1 := ⟨_, rfl⟩
  have hmpos : 0 < m := by
    rw [hmdef]
    omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hle : ((2 * n + 3 : ℕ) : ℝ) * (2 * Real.pi / m) ≤ eta := by
    rw [mul_div_assoc', div_le_iff₀ hmR]
    have hceil : ((2 * n + 3 : ℕ) : ℝ) * (2 * Real.pi) / eta
        ≤ (⌈((2 * n + 3 : ℕ) : ℝ) * (2 * Real.pi) / eta⌉₊ : ℝ) := Nat.le_ceil _
    have hmge : ((2 * n + 3 : ℕ) : ℝ) * (2 * Real.pi) / eta ≤ (m : ℝ) := by
      rw [hmdef]
      push_cast at hceil ⊢
      linarith [hceil]
    rw [div_le_iff₀ heta] at hmge
    linarith [hmge]
  refine ⟨m, hmpos, fun v s => ?_⟩
  obtain ⟨w, hwlen, hwdist⟩ := exists_diagAlphabet_word (n := n) hmpos hpsi v s
  exact ⟨w, le_of_eq hwlen, le_trans hwdist hle⟩

/-! ## Theorem C without the compiler hypothesis -/

variable {k : ℕ}

/-- **Theorem C on the tube, unconditionally.**  With the explicit alphabet of discretized diagonal
rotations, the compiler certificate is a theorem, so every Hamiltonian of the tube over the
separated diagonal patch incubates the uniform superposition through `L`, keeps its spectral
collision `O(1/D)`, and has every spatial bond strongly coupled -- with no hypothesis on any gate
alphabet. -/
theorem coupled_shortcut_tube_compiled
    {eps rho r L eta epsMinus : ℝ}
    (heps : 0 < eps) (hsmall : eps * 3 ^ ((k + 1) + 2) ≤ 2 / 3)
    (hrho0 : 0 ≤ rho) (hr0 : 0 ≤ r)
    (hrho : (2 * (((k + 1 : ℕ) : ℝ)) + 3) * rho
      ≤ eps / (4 * Real.sqrt ((2 * (k + 1) + 3 : ℕ) : ℝ)))
    (heta : 0 < eta) (hL : 0 ≤ L)
    (hgap : L * (Real.sqrt (Fintype.card (PathLabel (k + 1))) * r) ≤ epsMinus - eta)
    {ω : sphere (0 : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) 1}
    (hω : ω ∈ patchThickening (d := 10 * (k + 1) + 12)
      (sphericalCap (carrierPatchDir (k + 1) eps) rho) r) :
    ∃ m : ℕ, 0 < m ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ L →
        approxComplexity (diagAlphabetAct (k + 1) m) (eucVec (uniformSeed (k + 3))) epsMinus
          (orbitState (patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)))
            (eucVec (uniformSeed (k + 3))) t) ≤ 2 * (k + 1) + 3)
      ∧ (∀ ebasis lam, IsOrthoEigenBasis
            (patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))) ebasis lam →
          spectralCollision ebasis (uniformSeed (k + 3))
            ≤ ((Real.sqrt (2 ^ (k + 3)))⁻¹
                + 2 * (Real.sqrt (Fintype.card (PathLabel (k + 1))) * r)
                  / (eps / (2 * Real.sqrt ((2 * (k + 1) + 3 : ℕ) : ℝ)))) ^ (2 : ℕ))
      ∧ (∀ e : Fin (k + 2), (2 * Real.sqrt ((2 * (k + 1) + 3 : ℕ) : ℝ))⁻¹ - rho - r
          ≤ ‖edgePart (pathPatchIsometry (k + 1)
              (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))) e‖) := by
  classical
  obtain ⟨m, hmpos, hcompiler⟩ := exists_diagAlphabet_compiler (k + 1)
    (norm_eucVec_uniformSeed (k + 3)) heta
  refine ⟨m, hmpos, ?_⟩
  refine coupled_shortcut_tube (diagAlphabetAct (k + 1) m) (eucVec (uniformSeed (k + 3)))
    heps hsmall hrho0 hr0 hrho ?_ hL hgap hω
  rintro y ⟨v, -, rfl⟩ s
  exact hcompiler v s

end GaloisForLFunctions.HTGeometry

end
