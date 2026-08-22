import GaloisForLFunctions.HTGeometry.HaferkampFlattenedTerminalSignControl
import GaloisForLFunctions.HTGeometry.HaferkampFlattenedTerminalPhaseChart

/-!
# Explicit Pauli witnesses for computational-basis state directions

The nonzero Boolean configurations give a concrete real basis of the tangent
space of pure states at the computational zero: an all-`X` string reaches each
configuration and replacing one `X` by `Y` supplies its imaginary partner.
-/

open scoped BigOperators Matrix.Norms.Operator
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The all-false computational configuration. -/
def boolZeroConfiguration (n : ℕ) : Fin n → Bool := fun _ => false

/-- The nonzero Boolean configurations of an `n`-qubit register. -/
abbrev NonzeroBoolConfiguration (n : ℕ) :=
  {c : Fin n → Bool // c ≠ boolZeroConfiguration n}

/-- The computational-basis vector at a Boolean configuration. -/
def boolConfigBasis {n : ℕ} (c : Fin n → Bool) : (Fin n → Bool) → ℂ :=
  Pi.single c 1

theorem boolConfigBasis_apply {n : ℕ} (c x : Fin n → Bool) :
    boolConfigBasis c x = if x = c then 1 else 0 := by
  rw [boolConfigBasis, Pi.single_apply]

/-- Evaluating a matrix on the all-false computational state selects its zero
column. -/
theorem mulVec_boolZeroConfiguration {n : ℕ}
    (M : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    M *ᵥ boolConfigBasis (boolZeroConfiguration n) =
      fun x => M x (boolZeroConfiguration n) := by
  funext x
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (boolZeroConfiguration n)
    (fun b _ hb => by rw [boolConfigBasis_apply, if_neg hb, mul_zero])
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [boolConfigBasis_apply, if_pos rfl, mul_one]

/-- An `X` string whose support is exactly a target configuration. -/
def realStateWitnessLabel {n : ℕ} (c : Fin n → Bool) :
    Fin n → Option (Fin 3) :=
  fun i => if c i then some 0 else none

/-- A distinguished occupied site of a nonzero configuration. -/
noncomputable def imagStateWitnessSite {n : ℕ} (c : NonzeroBoolConfiguration n) : Fin n :=
  Classical.choose (Function.ne_iff.mp c.2)

theorem imagStateWitnessSite_true {n : ℕ} (c : NonzeroBoolConfiguration n) :
    c.1 (imagStateWitnessSite c) = true := by
  have h := Classical.choose_spec (Function.ne_iff.mp c.2)
  simpa [imagStateWitnessSite, boolZeroConfiguration] using h

/-- The imaginary partner replaces one occupied `X` factor by `Y`. -/
noncomputable def imagStateWitnessLabel {n : ℕ} (c : NonzeroBoolConfiguration n) :
    Fin n → Option (Fin 3) :=
  fun i => if i = imagStateWitnessSite c then some 1 else realStateWitnessLabel c.1 i

private theorem realStateWitness_entry {n : ℕ} (c x : Fin n → Bool) (i : Fin n) :
    boolPauliOptionEntry (realStateWitnessLabel c i)
        (x i, boolZeroConfiguration n i) = if x i = c i then 1 else 0 := by
  cases hc : c i <;> cases hx : x i <;>
    simp [realStateWitnessLabel, boolZeroConfiguration, hc,
      boolPauliOptionEntry, boolPauliOption, finiteQubitPauli, Matrix.one_apply]

theorem finitePauliMatrix_realStateWitnessLabel_apply {n : ℕ}
    (c x : Fin n → Bool) :
    finitePauliMatrix (realStateWitnessLabel c) x (boolZeroConfiguration n) =
      if x = c then 1 else 0 := by
  rw [show finitePauliMatrix (realStateWitnessLabel c) x (boolZeroConfiguration n) =
      ∏ i, boolPauliOptionEntry (realStateWitnessLabel c i)
        (x i, boolZeroConfiguration n i) from rfl]
  rw [Finset.prod_congr rfl (fun i _ => realStateWitness_entry c x i), Finset.prod_boole]
  by_cases h : x = c
  · rw [if_pos h, if_pos (fun i _ => congrFun h i)]
  · rw [if_neg h, if_neg (fun hh => h (funext fun i => hh i (Finset.mem_univ i)))]

theorem finitePauliMatrix_realStateWitnessLabel_mulVec_zero {n : ℕ}
    (c : Fin n → Bool) :
    finitePauliMatrix (realStateWitnessLabel c) *ᵥ boolConfigBasis (boolZeroConfiguration n) =
      boolConfigBasis c := by
  rw [mulVec_boolZeroConfiguration]
  funext x
  rw [finitePauliMatrix_realStateWitnessLabel_apply, boolConfigBasis_apply]

private theorem imagStateWitness_entry {n : ℕ}
    (c : NonzeroBoolConfiguration n) (x : Fin n → Bool) (i : Fin n) :
    boolPauliOptionEntry (imagStateWitnessLabel c i)
        (x i, boolZeroConfiguration n i) =
      if x i = c.1 i then (if i = imagStateWitnessSite c then Complex.I else 1) else 0 := by
  by_cases hi : i = imagStateWitnessSite c
  · subst i
    have hc := imagStateWitnessSite_true c
    cases hx : x (imagStateWitnessSite c) <;>
      simp [imagStateWitnessLabel, boolZeroConfiguration, hc,
        boolPauliOptionEntry, boolPauliOption, finiteQubitPauli]
  · rw [imagStateWitnessLabel, if_neg hi]
    rw [realStateWitness_entry]
    simp [hi]

theorem finitePauliMatrix_imagStateWitnessLabel_apply {n : ℕ}
    (c : NonzeroBoolConfiguration n) (x : Fin n → Bool) :
    finitePauliMatrix (imagStateWitnessLabel c) x (boolZeroConfiguration n) =
      if x = c.1 then Complex.I else 0 := by
  rw [show finitePauliMatrix (imagStateWitnessLabel c) x (boolZeroConfiguration n) =
      ∏ i, boolPauliOptionEntry (imagStateWitnessLabel c i)
        (x i, boolZeroConfiguration n i) from rfl]
  by_cases hxc : x = c.1
  · subst x
    rw [if_pos rfl]
    refine (Finset.prod_eq_single (imagStateWitnessSite c) ?_ ?_).trans ?_
    · intro i _ hi
      rw [imagStateWitness_entry]
      simp [hi]
    · intro h
      exact absurd (Finset.mem_univ (imagStateWitnessSite c)) h
    · rw [imagStateWitness_entry]
      simp
  · rw [if_neg hxc]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxc
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [imagStateWitness_entry]
    simp [hi]

theorem finitePauliMatrix_imagStateWitnessLabel_mulVec_zero {n : ℕ}
    (c : NonzeroBoolConfiguration n) :
    finitePauliMatrix (imagStateWitnessLabel c) *ᵥ boolConfigBasis (boolZeroConfiguration n) =
      Complex.I • boolConfigBasis c.1 := by
  rw [mulVec_boolZeroConfiguration]
  funext x
  rw [finitePauliMatrix_imagStateWitnessLabel_apply, Pi.smul_apply,
    boolConfigBasis_apply, smul_eq_mul]
  by_cases h : x = c.1 <;> simp [h]

/-- The Pauli labels providing both real directions of every nonzero
computational-basis state. -/
noncomputable def terminalStateWitnessLabel (n : ℕ) :
    NonzeroBoolConfiguration n ⊕ NonzeroBoolConfiguration n →
      Fin n → Option (Fin 3)
  | Sum.inl c => realStateWitnessLabel c.1
  | Sum.inr c => imagStateWitnessLabel c

/-- The corresponding state tangent directions: first imaginary basis vectors,
then their real partners. -/
def terminalStateWitnessFamily (n : ℕ) :
    NonzeroBoolConfiguration n ⊕ NonzeroBoolConfiguration n →
      ((Fin n → Bool) → ℂ)
  | Sum.inl c => Complex.I • boolConfigBasis c.1
  | Sum.inr c => (-1 : ℂ) • boolConfigBasis c.1

theorem terminalStateWitnessFamily_eq_terminalPauliAction {n : ℕ}
    (a : NonzeroBoolConfiguration n ⊕ NonzeroBoolConfiguration n) :
    terminalStateWitnessFamily n a =
      Complex.I • (finitePauliMatrix (terminalStateWitnessLabel n a) *ᵥ
        boolConfigBasis (boolZeroConfiguration n)) := by
  cases a with
  | inl c =>
      simp only [terminalStateWitnessFamily, terminalStateWitnessLabel]
      rw [finitePauliMatrix_realStateWitnessLabel_mulVec_zero]
  | inr c =>
      simp only [terminalStateWitnessFamily, terminalStateWitnessLabel]
      rw [finitePauliMatrix_imagStateWitnessLabel_mulVec_zero, smul_smul,
        Complex.I_mul_I]

private theorem sum_smul_boolConfigBasis_apply {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (e : ι → Fin n → Bool) (he : Function.Injective e)
    (g : ι → ℝ) (z : ℂ) (t : ι) :
    (∑ j : ι, g j • (z • boolConfigBasis (e j))) (e t) = (g t : ℂ) * z := by
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single t (fun b _ hb => by
    rw [Pi.smul_apply, Pi.smul_apply, boolConfigBasis_apply,
      if_neg (fun h => hb (he h.symm))]
    simp) (fun h => absurd (Finset.mem_univ t) h)]
  rw [Pi.smul_apply, Pi.smul_apply, boolConfigBasis_apply, if_pos rfl, smul_eq_mul,
    mul_one, Complex.real_smul]

/-- The `2(2^n-1)` terminal Pauli state directions are real-linearly
independent. -/
theorem linearIndependent_terminalStateWitnessFamily (n : ℕ) :
    LinearIndependent ℝ (terminalStateWitnessFamily n) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hval : ∀ c : NonzeroBoolConfiguration n,
      ((g (Sum.inl c) : ℂ)) * Complex.I + (g (Sum.inr c) : ℂ) * (-1) = 0 := by
    intro c
    have h := congrFun hg c.1
    rw [Fintype.sum_sum_type] at h
    have hinj : Function.Injective (fun c : NonzeroBoolConfiguration n => c.1) :=
      fun x y hxy => Subtype.ext hxy
    have h1 : (∑ c : NonzeroBoolConfiguration n,
        g (Sum.inl c) • terminalStateWitnessFamily n (Sum.inl c)) c.1
        = (g (Sum.inl c) : ℂ) * Complex.I := by
      have hsum := sum_smul_boolConfigBasis_apply
        (fun c : NonzeroBoolConfiguration n => c.1) hinj
        (fun c => g (Sum.inl c)) Complex.I c
      simpa [terminalStateWitnessFamily] using hsum
    have h2 : (∑ c : NonzeroBoolConfiguration n,
        g (Sum.inr c) • terminalStateWitnessFamily n (Sum.inr c)) c.1
        = (g (Sum.inr c) : ℂ) * (-1) := by
      have hsum := sum_smul_boolConfigBasis_apply
        (fun c : NonzeroBoolConfiguration n => c.1) hinj
        (fun c => g (Sum.inr c)) (-1) c
      simpa [terminalStateWitnessFamily] using hsum
    rw [Pi.add_apply, h1, h2] at h
    exact h
  intro a
  cases a with
  | inl c =>
      have h := congrArg Complex.im (hval c)
      simpa using h
  | inr c =>
      have h := congrArg Complex.re (hval c)
      exact neg_eq_zero.mp (by simpa using h)

theorem card_NonzeroBoolConfiguration (n : ℕ) :
    Fintype.card (NonzeroBoolConfiguration n) = 2 ^ n - 1 := by
  change Fintype.card {c : Fin n → Bool // ¬ c = boolZeroConfiguration n} = 2 ^ n - 1
  rw [Fintype.card_subtype_compl (fun c : Fin n → Bool => c = boolZeroConfiguration n),
    Fintype.card_subtype_eq]
  simp

theorem linearIndependent_terminalStatePauliActions (n : ℕ) :
    LinearIndependent ℝ (fun a : NonzeroBoolConfiguration n ⊕ NonzeroBoolConfiguration n =>
      Complex.I • (finitePauliMatrix (terminalStateWitnessLabel n a) *ᵥ
        boolConfigBasis (boolZeroConfiguration n))) := by
  rw [show (fun a : NonzeroBoolConfiguration n ⊕ NonzeroBoolConfiguration n =>
      Complex.I • (finitePauliMatrix (terminalStateWitnessLabel n a) *ᵥ
        boolConfigBasis (boolZeroConfiguration n))) = terminalStateWitnessFamily n by
      funext a
      exact (terminalStateWitnessFamily_eq_terminalPauliAction a).symm]
  exact linearIndependent_terminalStateWitnessFamily n

/-- Right action on a fixed state, viewed as a real continuous linear map of
the matrix argument. -/
noncomputable def matrixMulVecR {d : Type*} [Fintype d] [DecidableEq d]
    (ψ : d → ℂ) : Matrix d d ℂ →L[ℝ] (d → ℂ) :=
  (({ toFun := fun M => M *ᵥ ψ
      map_add' := fun M N => Matrix.add_mulVec M N ψ
      map_smul' := fun c M => Matrix.smul_mulVec c M ψ } :
      Matrix d d ℂ →ₗ[ℂ] (d → ℂ)).toContinuousLinearMap).restrictScalars ℝ

theorem matrixMulVecR_apply {d : Type*} [Fintype d] [DecidableEq d]
    (ψ : d → ℂ) (M : Matrix d d ℂ) : matrixMulVecR ψ M = M *ᵥ ψ := rfl

private theorem linearIndependent_real_smul_of_ne_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V] {ι : Type*}
    (v : ι → V) (hv : LinearIndependent ℝ v)
    (c : ι → ℝ) (hc : ∀ i, c i ≠ 0) :
    LinearIndependent ℝ (fun i => c i • v i) := by
  let u : ι → ℝˣ := fun i => Units.mk0 (c i) (hc i)
  rw [show (fun i => c i • v i) = u • v by
    funext i
    simp [u, Pi.smul_apply']]
  exact hv.units_smul u

namespace BackwardsLightCone

/-- The simultaneous terminal-phase chart acting on the computational zero
state. -/
def TerminalBlockPrefixAssembly.terminalPhaseStateChart
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    (Fin labels.length → ℝ) → ((Fin n → Bool) → ℂ) :=
  fun x => (assembly.terminalPhaseLiftedWord x).reverse.prod *ᵥ
    boolConfigBasis (boolZeroConfiguration n)

/-- The derivative of the terminal state chart is the matrix-chart derivative
followed by evaluation on the computational zero state. -/
theorem TerminalBlockPrefixAssembly.hasFDerivAt_terminalPhaseStateChart_zero
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    HasFDerivAt assembly.terminalPhaseStateChart
  ((matrixMulVecR (boolConfigBasis (boolZeroConfiguration n))).comp
        assembly.terminalPhaseTangentMap) 0 := by
  have hmatrix := assembly.hasFDerivAt_terminalPhaseContraction_zero
  have hstate : HasFDerivAt
      (matrixMulVecR (boolConfigBasis (boolZeroConfiguration n)))
      (matrixMulVecR (boolConfigBasis (boolZeroConfiguration n)))
      ((assembly.terminalPhaseLiftedWord 0).reverse.prod) :=
    (matrixMulVecR (boolConfigBasis (boolZeroConfiguration n))).hasFDerivAt
  have hcomp := HasFDerivAt.comp (f := fun x =>
      (assembly.terminalPhaseLiftedWord x).reverse.prod) (g := matrixMulVecR
        (boolConfigBasis (boolZeroConfiguration n))) 0 hstate hmatrix
  change HasFDerivAt (fun x => matrixMulVecR
    (boolConfigBasis (boolZeroConfiguration n))
    ((assembly.terminalPhaseLiftedWord x).reverse.prod)) _ 0
  exact hcomp

/-- After removing the assembled circuit unitary, each state-chart coordinate
tangent is its selected Pauli action, up to the certified terminal sign. -/
theorem TerminalBlockPrefixAssembly.terminalPhaseStateTangent_stripped
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels)
    (i : Fin labels.length) :
    Matrix.conjTranspose (assembly.liftedWord.reverse.prod :
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *ᵥ
      (((matrixMulVecR (boolConfigBasis (boolZeroConfiguration n))).comp
        assembly.terminalPhaseTangentMap) (Pi.single i 1)) =
      assembly.terminalCoefficient i •
        (Complex.I • (finitePauliMatrix (labels.get i) *ᵥ
          boolConfigBasis (boolZeroConfiguration n))) := by
  have hprefix :
      Matrix.conjTranspose
          (((assembly.liftedWord.take (assembly.terminalIndices i).1).reverse.prod :
            Matrix.unitaryGroup (Fin n → Bool) ℂ) :
            Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
        Matrix.conjTranspose (assembly.liftedWord.get (assembly.terminalIndices i) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
        finitePauliMatrix (Function.update (fun _ => none) root (some 2)) *
        (assembly.liftedWord.get (assembly.terminalIndices i) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
        (((assembly.liftedWord.take (assembly.terminalIndices i).1).reverse.prod :
          Matrix.unitaryGroup (Fin n → Bool) ℂ) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
        assembly.terminalCoefficient i • finitePauliMatrix (labels.get i) := by
    simpa [TerminalBlockPrefixAssembly.terminalPrefix] using
      assembly.terminalCoordinate_stripped i
  have hstrip := haferkampUnitaryListCoordinateOutput_strip assembly.liftedWord
    (assembly.terminalIndices i)
    (finitePauliMatrix (Function.update (fun _ => none) root (some 2)))
    (labels.get i) (assembly.terminalCoefficient i) hprefix
  have hsingle : assembly.terminalPhaseTangentMap (Pi.single i (1 : ℝ)) =
      Complex.I • haferkampUnitaryListCoordinateOutput assembly.liftedWord
        (assembly.terminalIndices i)
        (finitePauliMatrix (Function.update (fun _ => none) root (some 2))) := by
    simp [TerminalBlockPrefixAssembly.terminalPhaseTangentMap]
  change Matrix.conjTranspose (assembly.liftedWord.reverse.prod :
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *ᵥ
      (assembly.terminalPhaseTangentMap (Pi.single i 1) *ᵥ
        boolConfigBasis (boolZeroConfiguration n)) = _
  rw [hsingle, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    hstrip, Matrix.smul_mulVec, smul_smul, smul_smul, mul_comm]

/-- Independent Pauli actions on the computational zero state remain
independent as the terminal-state derivative coordinates of a BLC assembly. -/
theorem TerminalBlockPrefixAssembly.linearIndependent_terminalPhaseStateTangents
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels)
    (hlabels : LinearIndependent ℝ (fun i : Fin labels.length =>
      Complex.I • (finitePauliMatrix (labels.get i) *ᵥ
        boolConfigBasis (boolZeroConfiguration n))) ) :
    LinearIndependent ℝ (fun i =>
      ((matrixMulVecR (boolConfigBasis (boolZeroConfiguration n))).comp
        assembly.terminalPhaseTangentMap) (Pi.single i 1)) := by
  let c : Fin labels.length → ℝ := fun i =>
    if assembly.terminalCoefficient i = 1 then 1 else -1
  have hcoeff : ∀ i, (c i : ℂ) = assembly.terminalCoefficient i := by
    intro i
    rcases assembly.terminalCoefficient_eq_one_or_neg_one i with h | h
    · simp [c, h]
    · norm_num [c, h]
  have hc : ∀ i, c i ≠ 0 := by
    intro i
    dsimp [c]
    split <;> norm_num
  have hscaled : LinearIndependent ℝ (fun i : Fin labels.length =>
      c i • (Complex.I • (finitePauliMatrix (labels.get i) *ᵥ
        boolConfigBasis (boolZeroConfiguration n)))) :=
    linearIndependent_real_smul_of_ne_zero _ hlabels c hc
  let U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
    Matrix.conjTranspose (assembly.liftedWord.reverse.prod :
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
  let leftAction : ((Fin n → Bool) → ℂ) →ₗ[ℝ] ((Fin n → Bool) → ℂ) :=
    (Matrix.mulVecLin U).restrictScalars ℝ
  apply LinearIndependent.of_comp leftAction
  rw [show (leftAction ∘ fun i : Fin labels.length =>
      ((matrixMulVecR (boolConfigBasis (boolZeroConfiguration n))).comp
        assembly.terminalPhaseTangentMap) (Pi.single i 1)) =
      (fun i => c i • (Complex.I • (finitePauliMatrix (labels.get i) *ᵥ
        boolConfigBasis (boolZeroConfiguration n)))) by
      funext i
      change U *ᵥ (((matrixMulVecR (boolConfigBasis (boolZeroConfiguration n))).comp
        assembly.terminalPhaseTangentMap) (Pi.single i 1)) = _
      rw [show U = Matrix.conjTranspose (assembly.liftedWord.reverse.prod :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) by rfl,
        assembly.terminalPhaseStateTangent_stripped i, ← hcoeff i]
      ext x
      simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]]
  exact hscaled

/-- Independent terminal Pauli state actions force the corresponding lower
bound on the real range rank of the terminal-state tangent map. -/
theorem TerminalBlockPrefixAssembly.finrank_range_ge_terminalPhaseStateTangents
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels)
    (hlabels : LinearIndependent ℝ (fun i : Fin labels.length =>
      Complex.I • (finitePauliMatrix (labels.get i) *ᵥ
        boolConfigBasis (boolZeroConfiguration n))) ) :
    labels.length ≤ Module.finrank ℝ
      ((matrixMulVecR (boolConfigBasis (boolZeroConfiguration n))).comp
        assembly.terminalPhaseTangentMap).range := by
  let D := (matrixMulVecR (boolConfigBasis (boolZeroConfiguration n))).comp
    assembly.terminalPhaseTangentMap
  have htangents := assembly.linearIndependent_terminalPhaseStateTangents hlabels
  have hsingle (i : Fin labels.length) :
      D (Pi.single i 1) =
        ((matrixMulVecR (boolConfigBasis (boolZeroConfiguration n))).comp
          assembly.terminalPhaseTangentMap) (Pi.single i 1) := rfl
  have himages : LinearIndependent ℝ (fun i => D (Pi.single i 1)) := by
    simpa only [hsingle] using htangents
  let values : Fin labels.length → D.range :=
    fun i => ⟨D (Pi.single i 1), ⟨Pi.single i 1, rfl⟩⟩
  have hcomp : LinearIndependent ℝ (D.range.subtype ∘ values) := by
    simpa [values, Function.comp_def] using himages
  have hvalues : LinearIndependent ℝ values :=
    LinearIndependent.of_comp D.range.subtype hcomp
  change labels.length ≤ Module.finrank ℝ D.range
  calc
    labels.length = (Set.range values).finrank ℝ := by
      simpa using (linearIndependent_iff_card_eq_finrank_span.mp hvalues)
    _ = Module.finrank ℝ (Submodule.span ℝ (Set.range values)) := rfl
    _ ≤ Module.finrank ℝ D.range := Submodule.finrank_le _

/-- The actual Fréchet derivative of the terminal-state chart has the same
explicit rank lower bound. -/
theorem TerminalBlockPrefixAssembly.finrank_range_ge_terminalPhaseState_fderiv
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels)
    (hlabels : LinearIndependent ℝ (fun i : Fin labels.length =>
      Complex.I • (finitePauliMatrix (labels.get i) *ᵥ
        boolConfigBasis (boolZeroConfiguration n))) ) :
    labels.length ≤ Module.finrank ℝ
      (fderiv ℝ assembly.terminalPhaseStateChart 0).range := by
  have hderiv := assembly.hasFDerivAt_terminalPhaseStateChart_zero.fderiv
  rw [hderiv]
  exact assembly.finrank_range_ge_terminalPhaseStateTangents hlabels

end BackwardsLightCone

/-- The full explicit list of terminal-state Pauli labels, indexed by a finite
enumeration of the nonzero Boolean configurations and their `Y` partners. -/
noncomputable def terminalStateWitnessLabels (n : ℕ) :
    List (Fin n → Option (Fin 3)) :=
  List.ofFn (fun i : Fin (Fintype.card
      (NonzeroBoolConfiguration n ⊕ NonzeroBoolConfiguration n)) =>
    terminalStateWitnessLabel n ((Fintype.equivFin
      (NonzeroBoolConfiguration n ⊕ NonzeroBoolConfiguration n)).symm i))

theorem terminalStateWitnessLabels_length (n : ℕ) :
    (terminalStateWitnessLabels n).length =
      Fintype.card (NonzeroBoolConfiguration n ⊕ NonzeroBoolConfiguration n) := by
  simp [terminalStateWitnessLabels]

theorem terminalStateWitnessLabels_card (n : ℕ) :
    (terminalStateWitnessLabels n).length = 2 * (2 ^ n - 1) := by
  rw [terminalStateWitnessLabels_length, Fintype.card_sum,
    card_NonzeroBoolConfiguration]
  omega

theorem terminalStateWitnessLabel_ne_identity
    {n : ℕ} (a : NonzeroBoolConfiguration n ⊕ NonzeroBoolConfiguration n) :
    terminalStateWitnessLabel n a ≠ fun _ => none := by
  cases a with
  | inl c =>
      obtain ⟨i, hi⟩ := Function.ne_iff.mp c.2
      intro h
      have hval := congrFun h i
      simp [terminalStateWitnessLabel, realStateWitnessLabel,
        boolZeroConfiguration] at hval hi
      exact Bool.false_ne_true (hval.symm.trans hi)
  | inr c =>
      intro h
      have hval := congrFun h (imagStateWitnessSite c)
      simp [terminalStateWitnessLabel, imagStateWitnessLabel] at hval

theorem linearIndependent_terminalStateWitnessLabelActions (n : ℕ) :
    LinearIndependent ℝ (fun i : Fin (terminalStateWitnessLabels n).length =>
      Complex.I • (finitePauliMatrix ((terminalStateWitnessLabels n).get i) *ᵥ
        boolConfigBasis (boolZeroConfiguration n))) := by
  let ι := NonzeroBoolConfiguration n ⊕ NonzeroBoolConfiguration n
  let hlength : (terminalStateWitnessLabels n).length = Fintype.card ι :=
    terminalStateWitnessLabels_length n
  let cast : Fin (terminalStateWitnessLabels n).length → Fin (Fintype.card ι) :=
    fun i => Fin.cast hlength i
  let e : Fin (terminalStateWitnessLabels n).length → ι := fun i =>
    (Fintype.equivFin ι).symm (cast i)
  have hcast_inj : Function.Injective cast := Fin.cast_injective hlength
  have he_inj : Function.Injective e :=
    (Fintype.equivFin ι).symm.injective.comp hcast_inj
  have hget (i : Fin (terminalStateWitnessLabels n).length) :
      (terminalStateWitnessLabels n).get i = terminalStateWitnessLabel n (e i) := by
    change (List.ofFn (fun j : Fin (Fintype.card ι) =>
      terminalStateWitnessLabel n ((Fintype.equivFin ι).symm j))).get i = _
    rw [List.get_ofFn]
    rfl
  rw [show (fun i : Fin (terminalStateWitnessLabels n).length =>
      Complex.I • (finitePauliMatrix ((terminalStateWitnessLabels n).get i) *ᵥ
        boolConfigBasis (boolZeroConfiguration n))) =
      ((fun a : ι => Complex.I •
        (finitePauliMatrix (terminalStateWitnessLabel n a) *ᵥ
          boolConfigBasis (boolZeroConfiguration n))) ∘ e) by
      funext i
      rw [hget]
      rfl]
  exact (linearIndependent_terminalStatePauliActions n).comp e he_inj

namespace BackwardsLightCone

/-- Every backwards-light-cone architecture on at least two qubits admits a
terminal-phase state chart whose derivative has rank at least `T` throughout
the strict Appendix-C pre-saturation range. -/
theorem exists_terminalPhase_state_rank_witness
    {n T : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    (cone : BackwardsLightCone n edges root) (hn : 1 < n)
    (hT : T < 2 * 2 ^ n - 1) :
    ∃ labels : List (Fin n → Option (Fin 3)),
      ∃ assembly : TerminalBlockPrefixAssembly cone 1 labels,
        T ≤ Module.finrank ℝ
          (fderiv ℝ assembly.terminalPhaseStateChart 0).range := by
  let labels := terminalStateWitnessLabels n
  have hlabels_nonid : ∀ Q ∈ labels, Q ≠ fun _ => none := by
    intro Q hQ
    change Q ∈ terminalStateWitnessLabels n at hQ
    unfold terminalStateWitnessLabels at hQ
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hQ
    rw [← hi]
    exact terminalStateWitnessLabel_ne_identity _
  obtain ⟨assembly⟩ := nonempty_terminalBlockPrefixAssembly cone hn labels hlabels_nonid 1
    one_isFinitePauliClifford
  refine ⟨labels, assembly, ?_⟩
  have hlength : labels.length = 2 * (2 ^ n - 1) := by
    exact terminalStateWitnessLabels_card n
  have hTle : T ≤ labels.length := by
    rw [hlength]
    have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
    omega
  exact hTle.trans
    (assembly.finrank_range_ge_terminalPhaseState_fderiv
      (linearIndependent_terminalStateWitnessLabelActions n))

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
