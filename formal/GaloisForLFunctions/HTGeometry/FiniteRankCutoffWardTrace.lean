import GaloisForLFunctions.HTGeometry.PointedFisherCutoffWardTrace

/-!
# Finite-rank cutoff Ward transgression

The pointed Fisher cutoff Ward trace is the rank-two instance of a finite-packet law.  An arbitrary
finite sum of rank-one sources supplies all trace regularity needed to evaluate a bounded, possibly
noncompact cutoff edge.  The resulting signed pairing is exactly the packet evaluation of the
adjoint double-commutator curvature.
-/

open Complex
open scoped BigOperators InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open ContinuousLinearMap InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

/-- A finite-rank source packet `Σ i, c i • |x i⟩⟨y i|`. -/
noncomputable def finiteRankProbe
    (c : ι → ℂ) (x y : ι → H) : H →L[ℂ] H :=
  ∑ i, c i • rankOne ℂ (x i) (y i)

/-- Bounded multiplication transports a finite-rank packet by acting on its left vectors and by
the adjoint on its right vectors. -/
theorem mul_finiteRankProbe_mul
    (A B : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H) :
    A * finiteRankProbe c x y * B =
      finiteRankProbe c (fun i ↦ A (x i)) (fun i ↦ adjoint B (y i)) := by
  classical
  unfold finiteRankProbe
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ext z
  simp only [mul_apply, smul_apply, rankOne_apply, map_smul]
  rw [adjoint_inner_left]

/-- The adjoint of a finite-rank packet conjugates its coefficients and exchanges its two vector
families. -/
theorem adjoint_finiteRankProbe
    (c : ι → ℂ) (x y : ι → H) :
    adjoint (finiteRankProbe c x y) =
      finiteRankProbe (fun i ↦ (starRingEnd ℂ) (c i)) y x := by
  classical
  rw [finiteRankProbe, finiteRankProbe, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ContinuousLinearMap.adjoint.map_smulₛₗ, adjoint_rankOne]

/-- A real diagonal finite packet is self-adjoint.  This is the canonical hypothesis-free source
class for the one-way projection-boundary energy law. -/
theorem adjoint_finiteRankProbe_ofReal_self
    (r : ι → ℝ) (x : ι → H) :
    adjoint (finiteRankProbe (fun i ↦ (r i : ℂ)) x x) =
      finiteRankProbe (fun i ↦ (r i : ℂ)) x x := by
  simpa using adjoint_finiteRankProbe (fun i ↦ (r i : ℂ)) x x

omit [CompleteSpace H] in
/-- Finite-rank packets are additive in their coefficient family. -/
theorem finiteRankProbe_add_coeff
    (c d : ι → ℂ) (x y : ι → H) :
    finiteRankProbe (c + d) x y =
      finiteRankProbe c x y + finiteRankProbe d x y := by
  classical
  unfold finiteRankProbe
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Pi.add_apply, add_smul]

omit [CompleteSpace H] in
/-- Scaling packet coefficients scales the represented finite-rank operator. -/
theorem finiteRankProbe_smul_coeff
    (a : ℂ) (c : ι → ℂ) (x y : ι → H) :
    finiteRankProbe (a • c) x y = a • finiteRankProbe c x y := by
  classical
  unfold finiteRankProbe
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Pi.smul_apply]
  module

/-- Conjugating a finite-rank packet by a self-adjoint operator acts on both vector families. -/
theorem finiteRankProbe_conjugate_selfAdjoint
    (J : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H)
    (hJAdj : adjoint J = J) :
    J * finiteRankProbe c x y * J =
      finiteRankProbe c (fun i ↦ J (x i)) (fun i ↦ J (y i)) := by
  rw [mul_finiteRankProbe_mul, hJAdj]

/-- Every finite-rank source packet is Hilbert--Schmidt. -/
theorem finiteRankProbe_isHilbertSchmidt
    (c : ι → ℂ) (x y : ι → H) :
    IsHilbertSchmidt (finiteRankProbe c x y) := by
  classical
  unfold finiteRankProbe
  let s : Finset ι := Finset.univ
  change IsHilbertSchmidt (∑ i ∈ s, c i • rankOne ℂ (x i) (y i))
  induction s using Finset.induction_on with
  | empty => simpa using (isHilbertSchmidt_zero :
      IsHilbertSchmidt (0 : H →L[ℂ] H))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact ((isHilbertSchmidt_rankOne (x i) (y i)).smul (c i)).add ih

/-- The cutoff commutator of a finite-rank packet remains Hilbert--Schmidt. -/
theorem cutoffCommutator_finiteRankProbe_isHilbertSchmidt
    (e : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H) :
    IsHilbertSchmidt (cutoffCommutator e (finiteRankProbe c x y)) := by
  have hP := finiteRankProbe_isHilbertSchmidt c x y
  change IsHilbertSchmidt
    (finiteRankProbe c x y ∘L e - e ∘L finiteRankProbe c x y)
  exact (hP.comp_right e).sub (hP.comp_left e)

/-- Every bounded sandwich of a finite-rank source packet has a summable canonical trace
diagonal. -/
theorem summable_inner_diag_mul_finiteRankProbe_mul
    (A B : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H) :
    Summable (fun j ↦ inner ℂ (hsBasis ℂ H j)
      ((A * finiteRankProbe c x y * B) (hsBasis ℂ H j))) := by
  rw [mul_finiteRankProbe_mul]
  unfold finiteRankProbe
  have hEq : (fun j ↦ inner ℂ (hsBasis ℂ H j)
      ((∑ i, c i • rankOne ℂ (A (x i)) (adjoint B (y i))) (hsBasis ℂ H j))) =
      fun j ↦ ∑ i, c i * inner ℂ (hsBasis ℂ H j)
        (rankOne ℂ (A (x i)) (adjoint B (y i)) (hsBasis ℂ H j)) := by
    funext j
    rw [ContinuousLinearMap.sum_apply, inner_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_apply, inner_smul_right]
  rw [hEq]
  exact summable_sum (s := Finset.univ) (fun i hi ↦ by
      simpa only [smul_apply, inner_smul_right] using
        (summable_inner_diag_rankOne (A (x i))
          (adjoint B (y i))).mul_left (c i))

/-- **Finite-packet value law.**  A bounded operator may be evaluated against an arbitrary
finite-rank packet without a Hilbert--Schmidt premise on either bounded factor. -/
theorem opTrace_mul_finiteRankProbe_mul
    (A B : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H) :
    opTrace (A * finiteRankProbe c x y * B) =
      ∑ i, c i * inner ℂ (y i) (B (A (x i))) := by
  rw [mul_finiteRankProbe_mul]
  unfold finiteRankProbe
  classical
  let s : Finset ι := Finset.univ
  change opTrace (∑ i ∈ s, c i • rankOne ℂ (A (x i)) (adjoint B (y i))) =
    ∑ i ∈ s, c i * inner ℂ (y i) (B (A (x i)))
  induction s using Finset.induction_on with
  | empty => simp [opTrace]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        opTrace_add_of_summable_diag]
      · rw [opTrace_smul, opTrace_rankOne, adjoint_inner_left, ih]
      · simp_rw [smul_apply, inner_smul_right]
        exact (summable_inner_diag_rankOne (A (x i)) (adjoint B (y i))).mul_left (c i)
      · simpa only [ContinuousLinearMap.sum_apply, inner_sum] using
          (summable_sum (s := s) (fun j hj ↦ by
            simpa only [smul_apply, inner_smul_right] using
              (summable_inner_diag_rankOne (A (x j))
                (adjoint B (y j))).mul_left (c j)))

/-- **Finite-rank cyclicity.**  A bounded factor passes cyclically across an arbitrary finite-rank
packet, with no Hilbert--Schmidt hypothesis on the bounded factors. -/
theorem opTrace_mul_finiteRankProbe_mul_cyclic
    (A B : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H) :
    opTrace (A * finiteRankProbe c x y * B) =
      opTrace (finiteRankProbe c x y * B * A) := by
  rw [opTrace_mul_finiteRankProbe_mul,
    show finiteRankProbe c x y * B * A =
        1 * finiteRankProbe c x y * (B * A) by noncomm_ring,
    opTrace_mul_finiteRankProbe_mul]
  simp [ContinuousLinearMap.mul_apply]

/-- Signed cutoff pairing of a finite-rank source packet with a bounded channel. -/
noncomputable def finiteRankCutoffWardTrace
    (e T : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H) : ℂ :=
  opTrace (adjoint (cutoffCommutator e (finiteRankProbe c x y)) *
    cutoffCommutator e T)

omit [CompleteSpace H] in
/-- The pointed Fisher connection is exactly the symmetric two-term finite-rank packet. -/
theorem finiteRankProbe_finTwo_eq_pointedFisherConnection (psi chi : H) :
    finiteRankProbe (fun _ : Fin 2 ↦ ((Real.sqrt 2)⁻¹ : ℂ))
        (fun i ↦ if (i : ℕ) = 0 then chi else psi)
        (fun i ↦ if (i : ℕ) = 0 then psi else chi) =
      pointedFisherConnection psi chi := by
  rw [finiteRankProbe, Fin.sum_univ_two]
  simp only [Fin.isValue, Fin.val_zero, ↓reduceIte, Fin.val_one, one_ne_zero]
  rw [pointedFisherConnection]
  module

/-- The existing pointed Ward trace is the literal `Fin 2` specialization of the finite-packet
trace. -/
theorem finiteRankCutoffWardTrace_finTwo_eq_pointedCutoffWardTrace
    (e T : H →L[ℂ] H) (psi chi : H) :
    finiteRankCutoffWardTrace e T
        (fun _ : Fin 2 ↦ ((Real.sqrt 2)⁻¹ : ℂ))
        (fun i ↦ if (i : ℕ) = 0 then chi else psi)
        (fun i ↦ if (i : ℕ) = 0 then psi else chi) =
      pointedCutoffWardTrace e T psi chi := by
  unfold finiteRankCutoffWardTrace pointedCutoffWardTrace
  rw [finiteRankProbe_finTwo_eq_pointedFisherConnection]

/-! ## Hermitian polarization of finite-packet cutoff energy -/

/-- The two-source finite-rank Ward form.  Its two entries are finite packets, so it is a genuine
Hilbert--Schmidt pairing rather than merely a one-sided trace extension. -/
noncomputable def finiteRankCutoffWardForm
    {κ : Type*} [Fintype κ]
    (e : H →L[ℂ] H)
    (c : ι → ℂ) (x y : ι → H)
    (d : κ → ℂ) (u v : κ → H) : ℂ :=
  finiteRankCutoffWardTrace e (finiteRankProbe d u v) c x y

/-- The finite-packet Ward form is exactly the Hilbert--Schmidt pairing of the two cutoff
commutators. -/
theorem finiteRankCutoffWardForm_eq_hsInner
    {κ : Type*} [Fintype κ]
    (e : H →L[ℂ] H)
    (c : ι → ℂ) (x y : ι → H)
    (d : κ → ℂ) (u v : κ → H) :
    finiteRankCutoffWardForm e c x y d u v =
      hsInner (cutoffCommutator e (finiteRankProbe c x y))
        (cutoffCommutator e (finiteRankProbe d u v)) := by
  unfold finiteRankCutoffWardForm finiteRankCutoffWardTrace
  simpa only [ContinuousLinearMap.mul_def, adjoint_adjoint] using
    opTrace_comp_eq_hsInner
      (adjoint (cutoffCommutator e (finiteRankProbe c x y)))
      (cutoffCommutator e (finiteRankProbe d u v))

/-- **Ward polarization reflection.**  Exchanging the two finite source packets conjugates the
cutoff Ward value. -/
theorem finiteRankCutoffWardForm_conj_symm
    {κ : Type*} [Fintype κ]
    (e : H →L[ℂ] H)
    (c : ι → ℂ) (x y : ι → H)
    (d : κ → ℂ) (u v : κ → H) :
    finiteRankCutoffWardForm e c x y d u v =
      (starRingEnd ℂ) (finiteRankCutoffWardForm e d u v c x y) := by
  rw [finiteRankCutoffWardForm_eq_hsInner,
    finiteRankCutoffWardForm_eq_hsInner, hsInner_conj_symm]

/-- **Polarization recovers cutoff energy.**  On the diagonal, the signed finite-packet Ward form
is exactly the nonnegative Hilbert--Schmidt commutator energy. -/
theorem finiteRankCutoffWardForm_self_eq_hsNormSq
    (e : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H) :
    finiteRankCutoffWardForm e c x y c x y =
      (hsNormSq (cutoffCommutator e (finiteRankProbe c x y)) : ℂ) := by
  let K := cutoffCommutator e (finiteRankProbe c x y)
  have hK : IsHilbertSchmidt K :=
    cutoffCommutator_finiteRankProbe_isHilbertSchmidt e c x y
  rw [finiteRankCutoffWardForm_eq_hsInner]
  change hsInner K K = (hsNormSq K : ℂ)
  have hreal : (((hsInner K K).re : ℝ) : ℂ) = hsInner K K :=
    Complex.conj_eq_iff_re.mp (hsInner_conj_symm K K).symm
  calc
    hsInner K K = (((hsInner K K).re : ℝ) : ℂ) := hreal.symm
    _ = (hsNormSq K : ℂ) :=
      congrArg (fun r : ℝ ↦ (r : ℂ)) (hsInner_self_re hK)

/-- **Faithful Ward detector.**  The diagonal finite-packet Ward value vanishes exactly when its
cutoff commutator vanishes.  Thus Hilbert--Schmidt positive-definiteness upgrades Ward
nonnegativity to an exact proposition interface. -/
theorem finiteRankCutoffWardForm_self_eq_zero_iff
    (e : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H) :
    finiteRankCutoffWardForm e c x y c x y = 0 ↔
      cutoffCommutator e (finiteRankProbe c x y) = 0 := by
  rw [finiteRankCutoffWardForm_self_eq_hsNormSq, Complex.ofReal_eq_zero]
  exact hsNormSq_eq_zero_iff
    (cutoffCommutator_finiteRankProbe_isHilbertSchmidt e c x y)

/-- The faithful Ward detector vanishes exactly when the represented finite packet preserves the
cutoff decomposition. -/
theorem finiteRankCutoffWardForm_self_eq_zero_iff_commute
    (e : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H) :
    finiteRankCutoffWardForm e c x y c x y = 0 ↔
      finiteRankProbe c x y * e = e * finiteRankProbe c x y := by
  rw [finiteRankCutoffWardForm_self_eq_zero_iff]
  exact sub_eq_zero

/-- **Strict Ward detection.**  The real diagonal Ward value is positive exactly when the finite
packet crosses the cutoff. -/
theorem finiteRankCutoffWardForm_self_re_pos_iff_not_commute
    (e : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H) :
    0 < (finiteRankCutoffWardForm e c x y c x y).re ↔
      finiteRankProbe c x y * e ≠ e * finiteRankProbe c x y := by
  rw [finiteRankCutoffWardForm_self_eq_hsNormSq, Complex.ofReal_re]
  let K := cutoffCommutator e (finiteRankProbe c x y)
  have hK : IsHilbertSchmidt K :=
    cutoffCommutator_finiteRankProbe_isHilbertSchmidt e c x y
  constructor
  · intro hpos hcomm
    have hKzero : K = 0 := sub_eq_zero.mpr hcomm
    change 0 < hsNormSq K at hpos
    rw [hKzero, hsNormSq] at hpos
    simp at hpos
  · intro hcomm
    have hKne : K ≠ 0 := by
      intro hKzero
      exact hcomm (sub_eq_zero.mp hKzero)
    have hnormne : hsNormSq K ≠ 0 := by
      exact fun hzero => hKne ((hsNormSq_eq_zero_iff hK).mp hzero)
    exact lt_of_le_of_ne (hsNormSq_nonneg K) (Ne.symm hnormne)

/-- The diagonal finite-packet Ward value has nonnegative real part. -/
theorem finiteRankCutoffWardForm_self_re_nonneg
    (e : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H) :
    0 ≤ (finiteRankCutoffWardForm e c x y c x y).re := by
  rw [finiteRankCutoffWardForm_self_eq_hsNormSq, Complex.ofReal_re]
  exact hsNormSq_nonneg _

/-- **Pointed diagonal bridge.**  Evaluating a pointed Fisher source against itself as channel is
exactly its quadratic cutoff-commutator energy. -/
theorem pointedCutoffWardTrace_self_eq_hsNormSq
    (e : H →L[ℂ] H) (psi chi : H) :
    pointedCutoffWardTrace e (pointedFisherConnection psi chi) psi chi =
      (hsNormSq (cutoffCommutator e (pointedFisherConnection psi chi)) : ℂ) := by
  let c : Fin 2 → ℂ := fun _ ↦ ((Real.sqrt 2)⁻¹ : ℂ)
  let x : Fin 2 → H := fun i ↦ if (i : ℕ) = 0 then chi else psi
  let y : Fin 2 → H := fun i ↦ if (i : ℕ) = 0 then psi else chi
  have h := finiteRankCutoffWardForm_self_eq_hsNormSq e c x y
  rw [finiteRankCutoffWardForm, finiteRankProbe_finTwo_eq_pointedFisherConnection,
    finiteRankCutoffWardTrace_finTwo_eq_pointedCutoffWardTrace] at h
  exact h

/-- **Explicit phase-sensitive pointed Ward value.**  For an orthogonal state--tangent pair and an
orthogonal cutoff, the diagonal signed Ward trace is the established complex Fisher energy,
including the nonnegative phase defect that a real-overlap formula omits. -/
theorem pointedCutoffWardTrace_self_eq_phase
    (e : H →L[ℂ] H) (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (psi chi : H) (horth : inner ℂ psi chi = 0) :
    pointedCutoffWardTrace e (pointedFisherConnection psi chi) psi chi =
      (((‖chi‖ ^ 2 - ‖e chi‖ ^ 2) * ‖e psi‖ ^ 2 +
        (‖psi‖ ^ 2 - ‖e psi‖ ^ 2) * ‖e chi‖ ^ 2 -
        2 * ‖inner ℂ (e chi) (e psi)‖ ^ 2 +
        4 * (inner ℂ (e chi) (e psi)).im ^ 2 : ℝ) : ℂ) := by
  rw [pointedCutoffWardTrace_self_eq_hsNormSq,
    hsNormSq_pointedFisherConnection_cutoffCommutator_phase
      e he heAdj psi chi horth]

/-- Cauchy--Schwarz controls every polarized finite-packet Ward value by the two cutoff energies. -/
theorem norm_finiteRankCutoffWardForm_le
    {κ : Type*} [Fintype κ]
    (e : H →L[ℂ] H)
    (c : ι → ℂ) (x y : ι → H)
    (d : κ → ℂ) (u v : κ → H) :
    ‖finiteRankCutoffWardForm e c x y d u v‖ ≤
      hsNorm (cutoffCommutator e (finiteRankProbe c x y)) *
        hsNorm (cutoffCommutator e (finiteRankProbe d u v)) := by
  rw [finiteRankCutoffWardForm_eq_hsInner]
  exact norm_hsInner_le
    (cutoffCommutator_finiteRankProbe_isHilbertSchmidt e c x y)
    (cutoffCommutator_finiteRankProbe_isHilbertSchmidt e d u v)

/-- **Finite-rank cutoff Ward transgression.**  The signed boundary pairing is the trace of the
adjoint source packet against `[[T,e],e†]`. -/
theorem finiteRankCutoffWardTrace_eq_opTrace_adjointCurvature
    (e T : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H) :
    finiteRankCutoffWardTrace e T c x y =
      opTrace (adjoint (finiteRankProbe c x y) *
        cutoffWardAdjointCurvature e T) := by
  let P := finiteRankProbe c x y
  let Pstar := finiteRankProbe (fun i ↦ (starRingEnd ℂ) (c i)) y x
  let K := cutoffCommutator e T
  have hPstar : adjoint P = Pstar := adjoint_finiteRankProbe c x y
  have hAdj : adjoint (cutoffCommutator e P) =
      adjoint e * Pstar - Pstar * adjoint e := by
    rw [cutoffCommutator, map_sub, adjoint_comp, adjoint_comp, hPstar]
    rfl
  have hleft : (adjoint e * Pstar - Pstar * adjoint e) * K =
      adjoint e * Pstar * K - Pstar * adjoint e * K := by
    noncomm_ring
  have hright : Pstar * cutoffWardAdjointCurvature e T =
      Pstar * K * adjoint e - Pstar * adjoint e * K := by
    change Pstar * (K * adjoint e - adjoint e * K) =
      Pstar * K * adjoint e - Pstar * adjoint e * K
    noncomm_ring
  have hePK := summable_inner_diag_mul_finiteRankProbe_mul
    (adjoint e) K (fun i ↦ (starRingEnd ℂ) (c i)) y x
  have hPeK := summable_inner_diag_mul_finiteRankProbe_mul
    1 (adjoint e * K) (fun i ↦ (starRingEnd ℂ) (c i)) y x
  have hPKe := summable_inner_diag_mul_finiteRankProbe_mul
    1 (K * adjoint e) (fun i ↦ (starRingEnd ℂ) (c i)) y x
  dsimp only [finiteRankCutoffWardTrace]
  rw [hAdj, hleft, opTrace_sub_of_summable_diag]
  · rw [opTrace_mul_finiteRankProbe_mul_cyclic
        (adjoint e) K (fun i ↦ (starRingEnd ℂ) (c i)) y x]
    change opTrace (Pstar * K * adjoint e) - opTrace (Pstar * adjoint e * K) =
      opTrace (adjoint P * cutoffWardAdjointCurvature e T)
    rw [hPstar, hright, opTrace_sub_of_summable_diag]
    · simpa only [one_mul, mul_assoc] using hPKe
    · simpa only [one_mul, mul_assoc] using hPeK
  · exact hePK
  · simpa only [one_mul, mul_assoc] using hPeK

/-- **Finite-packet adjoint-curvature value relation.**  Every signed cutoff Ward trace is the
finite sum of packet matrix elements of `[[T,e],e†]`. -/
theorem finiteRankCutoffWardTrace_eq_adjointCurvature_values
    (e T : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H) :
    finiteRankCutoffWardTrace e T c x y =
      ∑ i, (starRingEnd ℂ) (c i) *
        inner ℂ (x i) (cutoffWardAdjointCurvature e T (y i)) := by
  rw [finiteRankCutoffWardTrace_eq_opTrace_adjointCurvature,
    adjoint_finiteRankProbe]
  simpa only [one_mul] using
    opTrace_mul_finiteRankProbe_mul
      (1 : H →L[ℂ] H) (cutoffWardAdjointCurvature e T)
        (fun i ↦ (starRingEnd ℂ) (c i)) y x

/-- For a self-adjoint cutoff, the finite packet evaluates the ordinary double commutator. -/
theorem finiteRankCutoffWardTrace_eq_curvature_values
    (e T : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H)
    (he : adjoint e = e) :
    finiteRankCutoffWardTrace e T c x y =
      ∑ i, (starRingEnd ℂ) (c i) *
        inner ℂ (x i) (cutoffWardCurvature e T (y i)) := by
  rw [finiteRankCutoffWardTrace_eq_adjointCurvature_values]
  congr 1
  funext i
  rw [cutoffWardAdjointCurvature, he]
  rfl

/-- Source-packet addition is visible exactly at the signed Ward value. -/
theorem finiteRankCutoffWardTrace_add_coeff
    (e T : H →L[ℂ] H) (c d : ι → ℂ) (x y : ι → H) :
    finiteRankCutoffWardTrace e T (c + d) x y =
      finiteRankCutoffWardTrace e T c x y +
        finiteRankCutoffWardTrace e T d x y := by
  simp only [finiteRankCutoffWardTrace_eq_adjointCurvature_values, Pi.add_apply, map_add,
    add_mul, Finset.sum_add_distrib]

/-- Scaling a source packet conjugate-scales its signed Ward value. -/
theorem finiteRankCutoffWardTrace_smul_coeff
    (e T : H →L[ℂ] H) (a : ℂ) (c : ι → ℂ) (x y : ι → H) :
    finiteRankCutoffWardTrace e T (a • c) x y =
      (starRingEnd ℂ) a * finiteRankCutoffWardTrace e T c x y := by
  simp only [finiteRankCutoffWardTrace_eq_adjointCurvature_values, Pi.smul_apply,
    smul_eq_mul, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Adjoint cutoff curvature is additive in the bounded channel. -/
theorem cutoffWardAdjointCurvature_add
    (e S T : H →L[ℂ] H) :
    cutoffWardAdjointCurvature e (S + T) =
      cutoffWardAdjointCurvature e S + cutoffWardAdjointCurvature e T := by
  change (((S + T) * e - e * (S + T)) * adjoint e -
      adjoint e * ((S + T) * e - e * (S + T))) =
    ((S * e - e * S) * adjoint e - adjoint e * (S * e - e * S)) +
      ((T * e - e * T) * adjoint e - adjoint e * (T * e - e * T))
  noncomm_ring

omit [CompleteSpace H] in
/-- Cutoff commutators are homogeneous in the bounded channel. -/
theorem cutoffCommutator_smul
    (e T : H →L[ℂ] H) (a : ℂ) :
    cutoffCommutator e (a • T) = a • cutoffCommutator e T := by
  ext z
  simp [cutoffCommutator]
  module

/-- Adjoint cutoff curvature is homogeneous in the bounded channel. -/
theorem cutoffWardAdjointCurvature_smul
    (e T : H →L[ℂ] H) (a : ℂ) :
    cutoffWardAdjointCurvature e (a • T) =
      a • cutoffWardAdjointCurvature e T := by
  rw [cutoffWardAdjointCurvature, cutoffCommutator_smul,
    cutoffCommutator_smul]
  rfl

/-- The finite-packet Ward value is additive in the bounded channel. -/
theorem finiteRankCutoffWardTrace_add_channel
    (e S T : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H) :
    finiteRankCutoffWardTrace e (S + T) c x y =
      finiteRankCutoffWardTrace e S c x y +
        finiteRankCutoffWardTrace e T c x y := by
  rw [finiteRankCutoffWardTrace_eq_adjointCurvature_values,
    finiteRankCutoffWardTrace_eq_adjointCurvature_values,
    finiteRankCutoffWardTrace_eq_adjointCurvature_values,
    cutoffWardAdjointCurvature_add]
  simp only [add_apply, inner_add_right, mul_add, Finset.sum_add_distrib]

/-- The finite-packet Ward value is homogeneous in the bounded channel. -/
theorem finiteRankCutoffWardTrace_smul_channel
    (e T : H →L[ℂ] H) (a : ℂ)
    (c : ι → ℂ) (x y : ι → H) :
    finiteRankCutoffWardTrace e (a • T) c x y =
      a * finiteRankCutoffWardTrace e T c x y := by
  rw [finiteRankCutoffWardTrace_eq_adjointCurvature_values,
    finiteRankCutoffWardTrace_eq_adjointCurvature_values,
    cutoffWardAdjointCurvature_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [smul_apply, inner_smul_right]
  ring

/-- Complementing the cutoff reverses both boundary commutators and preserves the finite-packet
Ward value. -/
theorem finiteRankCutoffWardTrace_one_sub
    (e T : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H) :
    finiteRankCutoffWardTrace (1 - e) T c x y =
      finiteRankCutoffWardTrace e T c x y := by
  unfold finiteRankCutoffWardTrace
  rw [cutoffCommutator_one_sub, cutoffCommutator_one_sub]
  apply congrArg opTrace
  rw [map_neg]
  noncomm_ring

/-- Simultaneous conjugation by a self-adjoint involution preserves every finite-packet Ward
value. -/
theorem finiteRankCutoffWardTrace_conjugate_involution
    (J e T : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H)
    (hJ : J * J = 1) (hJAdj : adjoint J = J) :
    finiteRankCutoffWardTrace (J * e * J) (J * T * J) c
        (fun i ↦ J (x i)) (fun i ↦ J (y i)) =
      finiteRankCutoffWardTrace e T c x y := by
  rw [finiteRankCutoffWardTrace_eq_adjointCurvature_values,
    finiteRankCutoffWardTrace_eq_adjointCurvature_values,
    cutoffWardAdjointCurvature_conjugate_involution J e T hJ hJAdj]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_conjugate_apply_involution J (cutoffWardAdjointCurvature e T) hJ hJAdj]

/-! ### Complete sesquilinear and reflection interfaces -/

/-- The finite-packet Ward form is additive in its first packet coefficients. -/
theorem finiteRankCutoffWardForm_add_left
    {κ : Type*} [Fintype κ]
    (e : H →L[ℂ] H)
    (c₁ c₂ : ι → ℂ) (x y : ι → H)
    (d : κ → ℂ) (u v : κ → H) :
    finiteRankCutoffWardForm e (c₁ + c₂) x y d u v =
      finiteRankCutoffWardForm e c₁ x y d u v +
        finiteRankCutoffWardForm e c₂ x y d u v := by
  exact finiteRankCutoffWardTrace_add_coeff e (finiteRankProbe d u v) c₁ c₂ x y

/-- The finite-packet Ward form is conjugate-homogeneous in its first packet. -/
theorem finiteRankCutoffWardForm_smul_left
    {κ : Type*} [Fintype κ]
    (e : H →L[ℂ] H) (a : ℂ)
    (c : ι → ℂ) (x y : ι → H)
    (d : κ → ℂ) (u v : κ → H) :
    finiteRankCutoffWardForm e (a • c) x y d u v =
      (starRingEnd ℂ) a * finiteRankCutoffWardForm e c x y d u v := by
  exact finiteRankCutoffWardTrace_smul_coeff e (finiteRankProbe d u v) a c x y

/-- The finite-packet Ward form is additive in its second packet coefficients. -/
theorem finiteRankCutoffWardForm_add_right
    {κ : Type*} [Fintype κ]
    (e : H →L[ℂ] H)
    (c : ι → ℂ) (x y : ι → H)
    (d₁ d₂ : κ → ℂ) (u v : κ → H) :
    finiteRankCutoffWardForm e c x y (d₁ + d₂) u v =
      finiteRankCutoffWardForm e c x y d₁ u v +
        finiteRankCutoffWardForm e c x y d₂ u v := by
  unfold finiteRankCutoffWardForm
  rw [finiteRankProbe_add_coeff, finiteRankCutoffWardTrace_add_channel]

/-- The finite-packet Ward form is homogeneous in its second packet. -/
theorem finiteRankCutoffWardForm_smul_right
    {κ : Type*} [Fintype κ]
    (e : H →L[ℂ] H) (a : ℂ)
    (c : ι → ℂ) (x y : ι → H)
    (d : κ → ℂ) (u v : κ → H) :
    finiteRankCutoffWardForm e c x y (a • d) u v =
      a * finiteRankCutoffWardForm e c x y d u v := by
  unfold finiteRankCutoffWardForm
  rw [finiteRankProbe_smul_coeff, finiteRankCutoffWardTrace_smul_channel]

/-- The finite-packet Ward form is invariant under cutoff complementation. -/
theorem finiteRankCutoffWardForm_one_sub
    {κ : Type*} [Fintype κ]
    (e : H →L[ℂ] H)
    (c : ι → ℂ) (x y : ι → H)
    (d : κ → ℂ) (u v : κ → H) :
    finiteRankCutoffWardForm (1 - e) c x y d u v =
      finiteRankCutoffWardForm e c x y d u v := by
  exact finiteRankCutoffWardTrace_one_sub e (finiteRankProbe d u v) c x y

/-- Simultaneous conjugation by a self-adjoint involution preserves the finite-packet Ward form. -/
theorem finiteRankCutoffWardForm_conjugate_involution
    {κ : Type*} [Fintype κ]
    (J e : H →L[ℂ] H)
    (c : ι → ℂ) (x y : ι → H)
    (d : κ → ℂ) (u v : κ → H)
    (hJ : J * J = 1) (hJAdj : adjoint J = J) :
    finiteRankCutoffWardForm (J * e * J) c
        (fun i ↦ J (x i)) (fun i ↦ J (y i)) d
        (fun i ↦ J (u i)) (fun i ↦ J (v i)) =
      finiteRankCutoffWardForm e c x y d u v := by
  unfold finiteRankCutoffWardForm
  rw [← finiteRankProbe_conjugate_selfAdjoint J d u v hJAdj]
  exact finiteRankCutoffWardTrace_conjugate_involution
    J e (finiteRankProbe d u v) c x y hJ hJAdj

end

end GaloisForLFunctions.HTGeometry
