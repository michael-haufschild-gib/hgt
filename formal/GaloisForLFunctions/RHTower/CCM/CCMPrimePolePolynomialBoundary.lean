import GaloisForLFunctions.RHTower.CCM.CCMPrimePoleCalkinBoundary
import Mathlib.Algebra.FreeAlgebra
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The joint polynomial boundary of finite CCM pole projections

Every finite family of positive CCM local scales admits a common weakly-null
unit sequence on which all of its pole-space projections converge strongly to
the identity.  Free-algebra induction upgrades this generator statement to
every noncommutative polynomial `Q`:

`Q(P₁, ..., P_d) vₙ - Q(1, ..., 1) vₙ → 0`.

The boundary value gives a lower bound for the essential norm of the evaluated
operator.  In particular, a polynomial that evaluates to a compact operator
must vanish at `(1, ..., 1)`.  Hence evaluation at that point descends to a
unique character of the polynomial algebra modulo the ideal of compact
evaluations, and every generator has character value one.
-/

open Filter Topology

noncomputable section

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Free noncommutative complex polynomials in generators indexed by `ι`. -/
abbrev OperatorPolynomial (ι : Type*) := FreeAlgebra ℂ ι

/-- Evaluate a free polynomial at a family of bounded operators. -/
def operatorPolynomialEval {ι : Type*} (T : ι → H →L[ℂ] H) :
    OperatorPolynomial ι →ₐ[ℂ] (H →L[ℂ] H) :=
  FreeAlgebra.lift ℂ T

/-- The scalar boundary evaluation sending every generator to one. -/
def operatorPolynomialBoundary {ι : Type*} :
    OperatorPolynomial ι →ₐ[ℂ] ℂ :=
  FreeAlgebra.lift ℂ (fun _ => 1)

/-- A common approximate fixed sequence for the generators is automatically an
approximate eigenvector sequence for every free noncommutative polynomial, with
eigenvalue obtained by sending every generator to one. -/
theorem tendsto_operatorPolynomialEval_apply_sub_boundary_smul
    {ι : Type*} (T : ι → H →L[ℂ] H) (f : ℕ → H)
    (hT : ∀ i, Tendsto (fun n => T i (f n) - f n) atTop (𝓝 0))
    (Q : OperatorPolynomial ι) :
    Tendsto (fun n => operatorPolynomialEval T Q (f n) -
      operatorPolynomialBoundary Q • f n) atTop (𝓝 0) := by
  induction Q using FreeAlgebra.induction with
  | grade0 c =>
      simp [operatorPolynomialEval, operatorPolynomialBoundary]
  | grade1 i =>
      simpa [operatorPolynomialEval, operatorPolynomialBoundary] using hT i
  | add A B hA hB =>
      have h := hA.add hB
      convert h using 1
      · funext n
        simp only [operatorPolynomialEval, operatorPolynomialBoundary, map_add,
          _root_.add_apply, add_smul]
        abel
      · simp
  | mul A B hA hB =>
      let EA : H →L[ℂ] H := operatorPolynomialEval T A
      let EB : H →L[ℂ] H := operatorPolynomialEval T B
      let a : ℂ := operatorPolynomialBoundary A
      let b : ℂ := operatorPolynomialBoundary B
      have hleft : Tendsto (fun n => EA (EB (f n) - b • f n)) atTop (𝓝 0) := by
        have hcont := EA.continuous.continuousAt.tendsto.comp hB
        simpa only [Function.comp_apply, map_zero] using! hcont
      have hright : Tendsto (fun n => b • (EA (f n) - a • f n)) atTop (𝓝 0) := by
        simpa [EA, a, b] using hA.const_smul b
      have hsum := hleft.add hright
      convert hsum using 1
      · funext n
        simp only [operatorPolynomialEval, operatorPolynomialBoundary, map_mul,
          mul_apply_eq_comp]
        dsimp only [EA, EB, a, b]
        rw [map_sub, map_smul]
        simp only [smul_sub, smul_smul]
        rw [mul_comm (operatorPolynomialBoundary B) (operatorPolynomialBoundary A)]
        abel
      · simp

/-- A weakly-null unit approximate eigenvector gives the modulus of its
approximate eigenvalue as a lower bound against every compact perturbation. -/
theorem norm_le_norm_sub_compact_of_weaklyNull_approx_eigenvector
    [CompleteSpace H] (T : H →L[ℂ] H) (f : ℕ → H) (c : ℂ)
    (hf_norm : ∀ n, ‖f n‖ = 1)
    (hf_weak : ∀ ℓ : H →L[ℂ] ℂ, Tendsto (fun n => ℓ (f n)) atTop (𝓝 0))
    (hT : Tendsto (fun n => ‖T (f n) - c • f n‖) atTop (𝓝 0))
    (K : H →L[ℂ] H) (hK : IsCompactOperator K) :
    ‖c‖ ≤ ‖T - K‖ := by
  have hf_bound : ∀ n, ‖f n‖ ≤ 1 := fun n => (hf_norm n).le
  have hTnorm : Tendsto (fun n => ‖T (f n)‖) atTop (𝓝 ‖c‖) :=
    tendsto_norm_of_norm_sub_tendsto_zero_of_norm_eq hT (fun n => by
      rw [norm_smul, hf_norm n, mul_one])
  have hKzero : Tendsto (fun n => ‖K (f n)‖) atTop (𝓝 0) :=
    IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weakly_null
      K hK f 1 hf_bound hf_weak
  have hupper : Tendsto (fun n => ‖T - K‖ + ‖K (f n)‖)
      atTop (𝓝 (‖T - K‖ + 0)) := tendsto_const_nhds.add hKzero
  have hle : ∀ n, ‖T (f n)‖ ≤ ‖T - K‖ + ‖K (f n)‖ := by
    intro n
    have hdecomp : T (f n) = (T - K) (f n) + K (f n) := by simp
    calc
      ‖T (f n)‖ = ‖(T - K) (f n) + K (f n)‖ := by rw [hdecomp]
      _ ≤ ‖(T - K) (f n)‖ + ‖K (f n)‖ := norm_add_le _ _
      _ ≤ (‖T - K‖ * ‖f n‖) + ‖K (f n)‖ := by
        gcongr
        exact (T - K).le_opNorm (f n)
      _ ≤ ‖T - K‖ + ‖K (f n)‖ := by
        have hm : ‖T - K‖ * ‖f n‖ ≤ ‖T - K‖ * 1 :=
          mul_le_mul_of_nonneg_left (hf_bound n) (norm_nonneg _)
        simpa using add_le_add_right hm ‖K (f n)‖
  have hlim := le_of_tendsto_of_tendsto hTnorm hupper (Eventually.of_forall hle)
  simpa using hlim

/-- Essential-norm form of the weakly-null approximate-eigenvector lower bound. -/
theorem norm_le_essentialNorm_of_weaklyNull_approx_eigenvector
    [CompleteSpace H] (T : H →L[ℂ] H) (f : ℕ → H) (c : ℂ)
    (hf_norm : ∀ n, ‖f n‖ = 1)
    (hf_weak : ∀ ℓ : H →L[ℂ] ℂ, Tendsto (fun n => ℓ (f n)) atTop (𝓝 0))
    (hT : Tendsto (fun n => ‖T (f n) - c • f n‖) atTop (𝓝 0)) :
    ‖c‖ ≤ essentialNorm T := by
  apply le_essentialNorm
  intro K hK
  exact norm_le_norm_sub_compact_of_weaklyNull_approx_eigenvector
    T f c hf_norm hf_weak hT K hK

/-- Free operator polynomials in a finite family of CCM pole projections. -/
abbrev CCMPrimePoleOperatorPolynomial (d : ℕ) := FreeAlgebra ℂ (Fin d)

/-- Evaluate a finite free polynomial at CCM pole-space projections. -/
def ccmPrimePoleOperatorPolynomialEval {d : ℕ}
    (L : Fin d → ℝ) (hL : ∀ i, 0 < L i) :
    CCMPrimePoleOperatorPolynomial d →ₐ[ℂ]
      (CCMPrimePoleHilbert →L[ℂ] CCMPrimePoleHilbert) :=
  operatorPolynomialEval fun i =>
    (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection

/-- Send every finite CCM pole-projection generator to the scalar one. -/
def ccmPrimePoleOperatorPolynomialBoundary {d : ℕ} :
    CCMPrimePoleOperatorPolynomial d →ₐ[ℂ] ℂ :=
  operatorPolynomialBoundary

/-- **Joint polynomial boundary sequence.** Every finite family of positive CCM
scales has one weakly-null unit sequence which simultaneously evaluates every
free noncommutative polynomial at the boundary point `(1, ..., 1)`. -/
theorem exists_fin_ccmPrimePole_operatorPolynomial_common_boundary_sequence
    {d : ℕ} (L : Fin d → ℝ) (hL : ∀ i, 0 < L i) :
    ∃ f : ℕ → CCMPrimePoleHilbert,
      (∀ n, ‖f n‖ = 1) ∧
      (∀ ℓ : CCMPrimePoleHilbert →L[ℂ] ℂ,
        Tendsto (fun n => ℓ (f n)) atTop (𝓝 0)) ∧
      ∀ Q : CCMPrimePoleOperatorPolynomial d,
        Tendsto (fun n => ccmPrimePoleOperatorPolynomialEval L hL Q (f n) -
          ccmPrimePoleOperatorPolynomialBoundary Q • f n) atTop (𝓝 0) := by
  obtain ⟨φ, _hφ, hnorm, hweak, hproj⟩ :=
    exists_fin_ccmPrimePole_projection_common_weaklyNull_sequence
      (by positivity : (0 : ℝ) < 1) L hL
  let f : ℕ → CCMPrimePoleHilbert := fun m =>
    ccmNormalizedPrimePoleVector 1 (by positivity) (φ m : ℤ)
  have hgen : ∀ i, Tendsto (fun m =>
      (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection (f m) - f m)
      atTop (𝓝 0) := by
    intro i
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [f] using hproj i
  refine ⟨f, ?_, ?_, fun Q => ?_⟩
  · simpa only [f] using hnorm
  · simpa only [f] using hweak
  · simpa [ccmPrimePoleOperatorPolynomialEval,
      ccmPrimePoleOperatorPolynomialBoundary] using
      tendsto_operatorPolynomialEval_apply_sub_boundary_smul
        (fun i => (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection)
        f hgen Q

/-- **Polynomial essential-boundary inequality.** Evaluation at the joint point
`(1, ..., 1)` is contractive for the essential operator norm. -/
theorem norm_ccmPrimePoleOperatorPolynomialBoundary_le_essentialNorm_eval
    {d : ℕ} (L : Fin d → ℝ) (hL : ∀ i, 0 < L i)
    (Q : CCMPrimePoleOperatorPolynomial d) :
    ‖ccmPrimePoleOperatorPolynomialBoundary Q‖ ≤
      essentialNorm (ccmPrimePoleOperatorPolynomialEval L hL Q) := by
  obtain ⟨f, hnorm, hweak, hpoly⟩ :=
    exists_fin_ccmPrimePole_operatorPolynomial_common_boundary_sequence L hL
  apply norm_le_essentialNorm_of_weaklyNull_approx_eigenvector
    (ccmPrimePoleOperatorPolynomialEval L hL Q) f
      (ccmPrimePoleOperatorPolynomialBoundary Q) hnorm hweak
  exact tendsto_zero_iff_norm_tendsto_zero.mp (hpoly Q)

/-- A compactly evaluated CCM pole polynomial vanishes at the joint boundary. -/
theorem ccmPrimePoleOperatorPolynomialBoundary_eq_zero_of_compact
    {d : ℕ} (L : Fin d → ℝ) (hL : ∀ i, 0 < L i)
    (Q : CCMPrimePoleOperatorPolynomial d)
    (hQ : IsCompactOperator (ccmPrimePoleOperatorPolynomialEval L hL Q)) :
    ccmPrimePoleOperatorPolynomialBoundary Q = 0 := by
  have hess : essentialNorm (ccmPrimePoleOperatorPolynomialEval L hL Q) = 0 := by
    apply le_antisymm
    · simpa using essentialNorm_le
        (ccmPrimePoleOperatorPolynomialEval L hL Q)
        (ccmPrimePoleOperatorPolynomialEval L hL Q) hQ
    · exact essentialNorm_nonneg _
  have hbound := norm_ccmPrimePoleOperatorPolynomialBoundary_le_essentialNorm_eval
    L hL Q
  rw [hess] at hbound
  exact norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))

/-- Compact equivalence of evaluated polynomials preserves their joint boundary value. -/
theorem ccmPrimePoleOperatorPolynomialBoundary_eq_of_compactDifference
    {d : ℕ} (L : Fin d → ℝ) (hL : ∀ i, 0 < L i)
    (Q R : CCMPrimePoleOperatorPolynomial d)
    (hQR : IsCompactOperator
      (ccmPrimePoleOperatorPolynomialEval L hL Q -
       ccmPrimePoleOperatorPolynomialEval L hL R)) :
    ccmPrimePoleOperatorPolynomialBoundary Q =
      ccmPrimePoleOperatorPolynomialBoundary R := by
  have hcompact : IsCompactOperator
      (ccmPrimePoleOperatorPolynomialEval L hL (Q - R)) := by
    simpa using hQR
  have hzero := ccmPrimePoleOperatorPolynomialBoundary_eq_zero_of_compact
    L hL (Q - R) hcompact
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- The two-sided ideal of free polynomials whose CCM pole evaluation is compact. -/
def ccmPrimePolePolynomialCompactIdeal
    {d : ℕ} (L : Fin d → ℝ) (hL : ∀ i, 0 < L i) :
    Ideal (CCMPrimePoleOperatorPolynomial d) where
  carrier := {Q | IsCompactOperator (ccmPrimePoleOperatorPolynomialEval L hL Q)}
  zero_mem' := by
    simpa using! (isCompactOperator_zero : IsCompactOperator
      (0 : CCMPrimePoleHilbert →L[ℂ] CCMPrimePoleHilbert))
  add_mem' := by
    intro Q R hQ hR
    simpa using! hQ.add hR
  smul_mem' := by
    intro Q R hR
    change IsCompactOperator
      (ccmPrimePoleOperatorPolynomialEval L hL (Q * R))
    rw [map_mul]
    exact hR.clm_comp (ccmPrimePoleOperatorPolynomialEval L hL Q)

instance ccmPrimePolePolynomialCompactIdeal_isTwoSided
    {d : ℕ} (L : Fin d → ℝ) (hL : ∀ i, 0 < L i) :
    (ccmPrimePolePolynomialCompactIdeal L hL).IsTwoSided where
  mul_mem_of_left {Q} R hQ := by
    change IsCompactOperator
      (ccmPrimePoleOperatorPolynomialEval L hL (Q * R))
    rw [map_mul]
    exact hQ.comp_clm (ccmPrimePoleOperatorPolynomialEval L hL R)

/-- The algebraic Calkin image of the finite CCM pole-projection polynomial algebra. -/
abbrev CCMPrimePolePolynomialCalkinAlgebra
    {d : ℕ} (L : Fin d → ℝ) (hL : ∀ i, 0 < L i) :=
  CCMPrimePoleOperatorPolynomial d ⧸ ccmPrimePolePolynomialCompactIdeal L hL

/-- **Joint Calkin boundary character.** Evaluation at `(1, ..., 1)` descends
through all compact polynomial relations. -/
def ccmPrimePolePolynomialCalkinCharacter
    {d : ℕ} (L : Fin d → ℝ) (hL : ∀ i, 0 < L i) :
    CCMPrimePolePolynomialCalkinAlgebra L hL →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ (ccmPrimePolePolynomialCompactIdeal L hL)
    ccmPrimePoleOperatorPolynomialBoundary
    (fun Q hQ => ccmPrimePoleOperatorPolynomialBoundary_eq_zero_of_compact
      L hL Q hQ)

@[simp]
theorem ccmPrimePolePolynomialCalkinCharacter_mk
    {d : ℕ} (L : Fin d → ℝ) (hL : ∀ i, 0 < L i)
    (Q : CCMPrimePoleOperatorPolynomial d) :
    ccmPrimePolePolynomialCalkinCharacter L hL
      (Ideal.Quotient.mk (ccmPrimePolePolynomialCompactIdeal L hL) Q) =
      ccmPrimePoleOperatorPolynomialBoundary Q := by
  simp [ccmPrimePolePolynomialCalkinCharacter]

/-- Every finite local projection has value one under the joint Calkin boundary character. -/
@[simp]
theorem ccmPrimePolePolynomialCalkinCharacter_generator
    {d : ℕ} (L : Fin d → ℝ) (hL : ∀ i, 0 < L i) (i : Fin d) :
    ccmPrimePolePolynomialCalkinCharacter L hL
      (Ideal.Quotient.mk (ccmPrimePolePolynomialCompactIdeal L hL)
        (FreeAlgebra.ι ℂ i)) = 1 := by
  rw [ccmPrimePolePolynomialCalkinCharacter_mk]
  simp [ccmPrimePoleOperatorPolynomialBoundary, operatorPolynomialBoundary]

/-- **Uniqueness of the joint boundary character.** It is the only complex
algebra character of the polynomial Calkin quotient that sends every local
projection generator to one. -/
theorem ccmPrimePolePolynomialCalkinCharacter_unique
    {d : ℕ} (L : Fin d → ℝ) (hL : ∀ i, 0 < L i)
    (χ : CCMPrimePolePolynomialCalkinAlgebra L hL →ₐ[ℂ] ℂ)
    (hχ : ∀ i : Fin d,
      χ (Ideal.Quotient.mk (ccmPrimePolePolynomialCompactIdeal L hL)
        (FreeAlgebra.ι ℂ i)) = 1) :
    χ = ccmPrimePolePolynomialCalkinCharacter L hL := by
  apply Ideal.Quotient.algHom_ext
  apply FreeAlgebra.hom_ext
  funext i
  change χ (Ideal.Quotient.mk (ccmPrimePolePolynomialCompactIdeal L hL)
      (FreeAlgebra.ι ℂ i)) =
    ccmPrimePolePolynomialCalkinCharacter L hL
      (Ideal.Quotient.mk (ccmPrimePolePolynomialCompactIdeal L hL)
        (FreeAlgebra.ι ℂ i))
  rw [hχ i, ccmPrimePolePolynomialCalkinCharacter_generator]

end RHTower
