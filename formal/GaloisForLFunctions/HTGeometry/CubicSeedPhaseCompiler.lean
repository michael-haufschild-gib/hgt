/-
# The cubic-phase seed is one gate per monomial

A cubic-phase seed is the uniform superposition modulated by the eighth-root character of a
multilinear polynomial of degree at most three.  Each monomial contributes one diagonal phase gate,
so the seed is prepared exactly -- not approximately -- by one gate per monomial, and the monomial
count is the cubic `1 + n + C(n,2) + C(n,3)`.  Adjoining those gates to the discretized diagonal
rotations compiles every carrier endpoint of every cubic seed at every time, from the *single*
reference state `|+>^{⊗n}`.

Main results:
* `charEight_add`, `charEight_sum` — the eighth-root character is additive-to-multiplicative.
* `monPhaseGate`, `registerCubicSeed_eq_mulVec` — **the seed is the monomial phase word**.
* `exists_cubicDiagAlphabet_compiler` — **the compiler certificate for every cubic seed**.
-/
import GaloisForLFunctions.HTGeometry.DiagonalRotationCompiler
import GaloisForLFunctions.HTGeometry.CapacityIncubationInstantiation

open Matrix Finset Metric MeasureTheory _root_.HTGeometry
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-! ## The eighth-root character -/

theorem zeta8_pow_congr {i j : ℕ} (h : i % 8 = j % 8) : zeta8 ^ i = zeta8 ^ j := by
  conv_lhs => rw [← Nat.div_add_mod i 8]
  conv_rhs => rw [← Nat.div_add_mod j 8]
  rw [pow_add, pow_add, pow_mul, pow_mul, zeta8_pow_eight, one_pow, one_pow, h]

theorem charEight_add (a b : ZMod 8) : charEight (a + b) = charEight a * charEight b := by
  rw [charEight, charEight, charEight, ← pow_add]
  refine zeta8_pow_congr ?_
  rw [ZMod.val_add]
  omega

theorem charEight_zero : charEight (0 : ZMod 8) = 1 := by
  rw [charEight]
  simp

theorem charEight_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 8) :
    charEight (∑ i ∈ s, f i) = ∏ i ∈ s, charEight (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [charEight_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, charEight_add, ih]

theorem norm_charEight (a : ZMod 8) : ‖charEight a‖ = 1 := by
  rw [charEight, norm_pow,
    Complex.norm_eq_one_of_pow_eq_one zeta8_pow_eight (by norm_num), one_pow]

/-! ## The monomial phase gates -/

variable {n : ℕ}

/-- The indicator of a monomial at a configuration. -/
def monIndicator (S : MonLe (Fin (n + 2)) 3) (x : FiniteQubitConfiguration (Fin (n + 2))) :
    ZMod 8 :=
  if ∀ i ∈ S.1, x i = true then (1 : ZMod 8) else 0

/-- The diagonal phase gate of one multilinear monomial. -/
def monPhaseGate (S : MonLe (Fin (n + 2)) 3) (t : ZMod 8) :
    Matrix (FiniteQubitConfiguration (Fin (n + 2))) (FiniteQubitConfiguration (Fin (n + 2))) ℂ :=
  Matrix.diagonal fun x => charEight (monIndicator S x * t)

theorem polyEval_eq_sum_monIndicator (c : MonLe (Fin (n + 2)) 3 → ZMod 8)
    (x : FiniteQubitConfiguration (Fin (n + 2))) :
    polyEval 3 c x = ∑ S : MonLe (Fin (n + 2)) 3, monIndicator S x * c S := by
  rw [polyEval]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [monIndicator]
  congr 1
  congr 1

/-- The list of all monomials of degree at most three. -/
def monList (n : ℕ) : List (MonLe (Fin (n + 2)) 3) :=
  (Finset.univ : Finset (MonLe (Fin (n + 2)) 3)).toList

theorem length_monList (n : ℕ) :
    (monList n).length = Fintype.card (MonLe (Fin (n + 2)) 3) := by
  rw [monList, Finset.length_toList, Finset.card_univ]

theorem prod_monPhaseGate (c : MonLe (Fin (n + 2)) 3 → ZMod 8) :
    (((monList n).map fun S => monPhaseGate S (c S)).prod)
      = Matrix.diagonal fun x => charEight (polyEval 3 c x) := by
  classical
  have hgen : ∀ L : List (MonLe (Fin (n + 2)) 3),
      ((L.map fun S => monPhaseGate S (c S)).prod)
        = Matrix.diagonal fun x => (L.map fun S => charEight (monIndicator S x * c S)).prod := by
    intro L
    induction L with
    | nil => simp
    | cons S L ih =>
        rw [List.map_cons, List.prod_cons, ih, monPhaseGate, Matrix.diagonal_mul_diagonal]
        congr 1
  rw [hgen]
  congr 1
  funext x
  rw [polyEval_eq_sum_monIndicator, charEight_sum]
  rw [monList, Finset.prod_map_toList]


/-! ## The cubic seed as a monomial word -/

theorem uniformSeed_eq_sqrt_weight (k : ℕ) (x : FiniteQubitConfiguration (Fin (k + 3))) :
    ((Real.sqrt (uniformPhaseWeights (FiniteQubitConfiguration (Fin (k + 3))) x) : ℝ) : ℂ)
      = uniformSeed (k + 3) x := by
  rw [uniformPhaseWeights, uniformSeed]
  congr 1
  rw [Real.sqrt_inv]
  congr 2
  simp

theorem charLift_single_eighthPhase (k : ℕ)
    (w : FiniteQubitConfiguration (Fin (k + 3)) → ZMod 8)
    (x : FiniteQubitConfiguration (Fin (k + 3))) :
    charLift (Pi.single x 1) (eighthPhase w) = charEight (w x) := by
  classical
  rw [charLift_eighthPhase]
  rw [Finset.prod_eq_single x]
  · rw [Pi.single_eq_same]
    norm_num
  · intro a _ hax
    rw [Pi.single_eq_of_ne hax]
    norm_num [charEight_zero]
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- **The cubic seed is one gate per monomial applied to the uniform superposition.** -/
theorem registerCubicSeed_eq_mulVec (k : ℕ) (c : MonLe (Fin (k + 3)) 3 → ZMod 8) :
    registerCubicSeed k c
      = (((monList (k + 1)).map fun S => monPhaseGate S (c S)).prod) *ᵥ uniformSeed (k + 3) := by
  funext x
  rw [prod_monPhaseGate, Matrix.mulVec_diagonal, registerCubicSeed, uniformPhaseSeed,
    torusReplicaPhaseOrbit, charLift_single_eighthPhase, uniformSeed_eq_sqrt_weight]
  ring

/-! ## The alphabet of the cubic compiler -/

/-- Monomial phase gates together with discretized diagonal rotations. -/
abbrev CubicDiagAlphabet (n m : ℕ) : Type :=
  (MonLe (Fin (n + 2)) 3 × ZMod 8) ⊕ DiagAlphabet n m

/-- The gate matrix of one letter. -/
def cubicDiagGate (n m : ℕ) :
    CubicDiagAlphabet n m →
      Matrix (FiniteQubitConfiguration (Fin (n + 2))) (FiniteQubitConfiguration (Fin (n + 2))) ℂ
  | Sum.inl St => monPhaseGate St.1 St.2
  | Sum.inr g => diagAlphabetGate n m g

/-- Its action on register states. -/
def cubicDiagAct (n m : ℕ) :
    CubicDiagAlphabet n m → EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2)))
      → EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))) :=
  fun g x => eucVec (cubicDiagGate n m g *ᵥ WithLp.ofLp x)

theorem wordAct_cubicDiagAct_inr (m : ℕ)
    (psi : FiniteQubitConfiguration (Fin (n + 2)) → ℂ) :
    ∀ w : List (DiagAlphabet n m),
      wordAct (cubicDiagAct n m) (w.map Sum.inr) (eucVec psi)
        = wordAct (diagAlphabetAct n m) w (eucVec psi)
  | [] => by simp
  | g :: w => by
      rw [List.map_cons, wordAct_cons, wordAct_cons, wordAct_cubicDiagAct_inr m psi w]
      rfl

theorem wordAct_cubicDiagAct_mulVec (m : ℕ)
    (psi : FiniteQubitConfiguration (Fin (n + 2)) → ℂ) :
    ∀ w : List (CubicDiagAlphabet n m),
      wordAct (cubicDiagAct n m) w (eucVec psi)
        = eucVec (((w.map (cubicDiagGate n m)).prod) *ᵥ psi)
  | [] => by
      simp only [wordAct_nil, List.map_nil, List.prod_nil, Matrix.one_mulVec]
  | g :: w => by
      rw [wordAct_cons, wordAct_cubicDiagAct_mulVec m psi w, cubicDiagAct]
      simp only [List.map_cons, List.prod_cons]
      rw [← Matrix.mulVec_mulVec]
      rfl

/-- **The compiler certificate for every cubic seed.**  From the single reference state
`|+>^{⊗n}`, one word of `card (MonLe) + (2n+3)` letters reproduces the carrier endpoint of every
cubic seed at every time. -/
theorem exists_cubicDiagAlphabet_compiler (k : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∃ m : ℕ, 0 < m ∧
      ∀ (c : MonLe (Fin (k + 3)) 3 → ZMod 8)
        (v : EuclideanSpace ℝ (Fin (2 * (k + 1) + 3))) (s : ℝ),
        ∃ w : List (CubicDiagAlphabet (k + 1) m),
          w.length ≤ Fintype.card (MonLe (Fin (k + 3)) 3) + (2 * (k + 1) + 3) ∧
          dist (orbitState (patchHamLM k (WithLp.toLp 2 (v,
                  (0 : EuclideanSpace ℝ (Fin (10 * (k + 1) + 12))))))
                  (eucVec (registerCubicSeed k c)) s)
               (wordAct (cubicDiagAct (k + 1) m) w (eucVec (uniformSeed (k + 3)))) ≤ eta := by
  classical
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ,
    m = ⌈((2 * (k + 1) + 3 : ℕ) : ℝ) * (2 * Real.pi) / eta⌉₊ + 1 := ⟨_, rfl⟩
  have hmpos : 0 < m := by
    rw [hmdef]
    omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hle : ((2 * (k + 1) + 3 : ℕ) : ℝ) * (2 * Real.pi / m) ≤ eta := by
    rw [mul_div_assoc', div_le_iff₀ hmR]
    have hceil : ((2 * (k + 1) + 3 : ℕ) : ℝ) * (2 * Real.pi) / eta
        ≤ (⌈((2 * (k + 1) + 3 : ℕ) : ℝ) * (2 * Real.pi) / eta⌉₊ : ℝ) := Nat.le_ceil _
    have hmge : ((2 * (k + 1) + 3 : ℕ) : ℝ) * (2 * Real.pi) / eta ≤ (m : ℝ) := by
      rw [hmdef]
      push_cast at hceil ⊢
      linarith [hceil]
    rw [div_le_iff₀ heta] at hmge
    linarith [hmge]
  refine ⟨m, hmpos, fun c v s => ?_⟩
  have hunit : ‖eucVec (registerCubicSeed k c)‖ = 1 :=
    norm_eucVec_eq_one (finiteComplexInner_registerCubicSeed c)
  obtain ⟨wr, hwrlen, hwrdist⟩ :=
    exists_diagAlphabet_word (n := k + 1) hmpos hunit v s
  obtain ⟨wmon, hwmondef⟩ : ∃ wmon : List (CubicDiagAlphabet (k + 1) m),
    wmon = (monList (k + 1)).map fun S => Sum.inl (S, c S) := ⟨_, rfl⟩
  refine ⟨(wr.map Sum.inr) ++ wmon, ?_, ?_⟩
  · rw [List.length_append, List.length_map, hwrlen, hwmondef, List.length_map,
      length_monList]
    have hcard : Fintype.card (MonLe (Fin (k + 1 + 2)) 3)
        = Fintype.card (MonLe (Fin (k + 3)) 3) := rfl
    omega
  · have hprep : wordAct (cubicDiagAct (k + 1) m) wmon (eucVec (uniformSeed (k + 3)))
        = eucVec (registerCubicSeed k c) := by
      rw [wordAct_cubicDiagAct_mulVec, hwmondef, List.map_map, registerCubicSeed_eq_mulVec]
      rfl
    have happ : wordAct (cubicDiagAct (k + 1) m) ((wr.map Sum.inr) ++ wmon)
          (eucVec (uniformSeed (k + 3)))
        = wordAct (cubicDiagAct (k + 1) m) (wr.map Sum.inr)
            (wordAct (cubicDiagAct (k + 1) m) wmon (eucVec (uniformSeed (k + 3)))) := by
      rw [wordAct, wordAct, wordAct, List.foldr_append]
    rw [happ, hprep, wordAct_cubicDiagAct_inr]
    exact le_trans hwrdist hle


/-! ## The incubation law without the compiler hypothesis -/

/-- **The capacity-compatible incubation law, unconditionally.**  With the explicit alphabet of
monomial phase gates and discretized diagonal rotations, the carrier compiler certificate is a
theorem, so the incubation conjunction holds with no hypothesis on any gate alphabet. -/
theorem exists_incubating_cubicSeed_compiled (k : ℕ)
    {ρ r L eta epsMinus : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L) (heta : 0 < eta)
    (hgap : L * (Real.sqrt (Fintype.card (PathLabel (k + 1))) * r) ≤ epsMinus - eta)
    {kap : ℝ} (hkap : 0 < kap)
    {epsn epsw : ℝ} (hepsn : 0 ≤ epsn) (hegap : epsn < epsw) (hepsw : epsw < 1)
    {rr : ℕ} (hrr : 1 ≤ rr)
    (hscale : 16 * ((2 + kap) / regDim k) / (1 - epsw ^ 2) ^ 2 ≤ 1 / (2 * rr))
    {C : Type} [Fintype C] [Nonempty C]
    (Z : C → (FiniteQubitConfiguration (Fin (k + 3)) → ℂ))
    (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1)
    {M : ℝ} (hM : 1 < M) {sc : ℕ} (hcardC : (Fintype.card C : ℝ) ≤ M ^ (sc + 1))
    (hs : ((sc : ℝ) + 1) * Real.log M ≤ ((rr : ℝ) / 2) * Real.log 2)
    (W : ℝ)
    (hW : ((plateauGridCount W ((epsw - epsn) /
        Real.sqrt (Fintype.card (PathLabel (k + 1)))) : ℕ) : ℝ) *
      (2 : ℝ) ^ (-((rr : ℝ) / 2)) < 1) :
    ∃ m : ℕ, 0 < m ∧
      ∃ c : MonLe (Fin (k + 3)) 3 → ZMod 8,
        (1 - 96 / (kap ^ 2 * regDim k)) *
            ((volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere).real
              (patchThickening (sphericalCap (uniformDir (2 * (k + 1) + 3)) ρ) r)
          ≤ (((volume : Measure (PatchSpace (2 * (k + 1) + 3)
              (10 * (k + 1) + 12))).toSphere).restrict
              (patchThickening (sphericalCap (uniformDir (2 * (k + 1) + 3)) ρ) r)).real
              (patchGood k kap c ∩ (patchToCoeff k ⁻¹' chainBadSphere k)ᶜ)
        ∧ ∀ ω ∈ patchThickening (sphericalCap (uniformDir (2 * (k + 1) + 3)) ρ) r,
            ω ∈ patchGood k kap c → ω ∉ patchToCoeff k ⁻¹' chainBadSphere k →
            (∀ t : ℝ, 0 ≤ t → t ≤ L →
                approxComplexity (cubicDiagAct (k + 1) m) (eucVec (uniformSeed (k + 3))) epsMinus
                  (orbitState (patchHamLM k
                      (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)))
                    (eucVec (registerCubicSeed k c)) t)
                ≤ Fintype.card (MonLe (Fin (k + 3)) 3) + (2 * (k + 1) + 3))
            ∧ MaximallyProjectiveEnergy (patchEigenValues k ω)
            ∧ phaseCollision (patchEigenBasis k ω) (eighthPhase (polyEval 3 c))
                ≤ (2 + kap) / regDim k
            ∧ (∀ A : ℝ, ∃ t₀, A < t₀ ∧ ∀ u ∈ Set.Icc t₀ (t₀ + W),
                u ∉ metricEasySet
                  (patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)))
                  (registerCubicSeed k c) epsn Z)
            ∧ (∀ ρ' : ℝ, 0 < ρ' → ∀ A : ℝ, ∃ s' : ℝ, A < s' ∧ 1 - ρ' ≤ ‖finiteComplexInner
                (unitaryEvolution
                    (patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))) s' *ᵥ
                  registerCubicSeed k c) (registerCubicSeed k c)‖)
            ∧ (∀ e : Fin (k + 2),
                (Real.sqrt ((2 * (k + 1) + 3 : ℕ) : ℝ))⁻¹ - ρ - r
                  ≤ ‖edgePart (pathPatchIsometry (k + 1)
                      (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))) e‖) := by
  obtain ⟨m, hmpos, hcomp⟩ := exists_cubicDiagAlphabet_compiler k heta
  refine ⟨m, hmpos, ?_⟩
  refine exists_incubating_cubicSeed k (cubicDiagAct (k + 1) m)
    (eucVec (uniformSeed (k + 3)))
    (B := Fintype.card (MonLe (Fin (k + 3)) 3) + (2 * (k + 1) + 3)) hρ hL ?_ hgap hkap
    hepsn hegap hepsw hrr hscale Z hZ hM hcardC hs W hW
  rintro c y ⟨v, -, rfl⟩ s
  exact hcomp c v s

end GaloisForLFunctions.HTGeometry

end
