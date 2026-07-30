import GaloisForLFunctions.HTGeometry.GammaPoleCovariantJetRealization
import GaloisForLFunctions.HTGeometry.GammaPoleMovingMaximalWeightReflection
import GaloisForLFunctions.HTGeometry.GammaPoleReciprocalBellGrading

/-!
# Weighted boundary values for dynamic Gamma polynomial jets

This file supplies the analytic associated-graded law behind moving Gamma
polynomial packets.  A polynomial evaluated on coordinates with prescribed
pole weights has a boundary value determined exactly by its maximal weighted
homogeneous component.  The law allows the coefficient homomorphism to move
as well, provided it converges pointwise.

For the factorially normalized Gamma chart, every covariant jet has its exact
top residue and every polynomial coefficient converges to its pole-center
value.  Hence the maximal weighted boundary of a running packet is precisely
the frozen top-residue evaluation; all Taylor corrections descend to lower
pole grades.
-/

open Complex Filter Topology Finset MvPolynomial

namespace GaloisForLFunctions

noncomputable section

/-- Polynomial evaluation is continuous when both coefficients and variables vary. -/
theorem tendsto_mvPolynomial_eval₂
    {ι R : Type*} [Fintype ι] [CommSemiring R]
    {l : Filter ℂ} {f : ℂ → R →+* ℂ} {f₀ : R →+* ℂ}
    {x : ι → ℂ → ℂ} {r : ι → ℂ}
    (hf : ∀ a, Tendsto (fun z => f z a) l (𝓝 (f₀ a)))
    (hx : ∀ i, Tendsto (x i) l (𝓝 (r i)))
    (P : MvPolynomial ι R) :
    Tendsto (fun z => MvPolynomial.eval₂ (f z) (fun i => x i z) P) l
      (𝓝 (MvPolynomial.eval₂ f₀ r P)) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hf a
  | add P Q hP hQ => simpa using hP.add hQ
  | mul_X P i hP => simpa using hP.mul (hx i)

/-- Weighted scaling decomposes evaluation into its homogeneous boundary layers. -/
theorem pow_weightedTotalDegree_mul_eval₂_eq_sum_weightedHomogeneousComponent
    {ι R : Type*} [Fintype ι] [CommSemiring R]
    (w : ι → ℕ) (P : MvPolynomial ι R) (f : R →+* ℂ)
    (x : ι → ℂ) (z : ℂ) :
    z ^ P.weightedTotalDegree w * MvPolynomial.eval₂ f x P =
      ∑ d ∈ Finset.range (P.weightedTotalDegree w + 1),
        z ^ (P.weightedTotalDegree w - d) *
          MvPolynomial.eval₂ f (fun i => z ^ w i * x i)
            (MvPolynomial.weightedHomogeneousComponent w d P) := by
  classical
  let W := P.weightedTotalDegree w
  have hsum := sum_weightedHomogeneousComponent_range w P
  calc
    z ^ P.weightedTotalDegree w * MvPolynomial.eval₂ f x P =
        z ^ W * MvPolynomial.eval₂ f x
          (∑ d ∈ Finset.range (W + 1),
            MvPolynomial.weightedHomogeneousComponent w d P) := by rw [hsum]
    _ = ∑ d ∈ Finset.range (W + 1),
          z ^ W * MvPolynomial.eval₂ f x
            (MvPolynomial.weightedHomogeneousComponent w d P) := by
      change z ^ W * (MvPolynomial.eval₂Hom f x)
          (∑ d ∈ Finset.range (W + 1),
            MvPolynomial.weightedHomogeneousComponent w d P) = _
      rw [map_sum, Finset.mul_sum]
      simp only [MvPolynomial.coe_eval₂Hom]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdW : d ≤ W := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
      have hscale := isWeightedHomogeneous_eval₂_scale
        (w := w)
        (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous d P)
        f x z
      calc
        z ^ P.weightedTotalDegree w * MvPolynomial.eval₂ f x
              (MvPolynomial.weightedHomogeneousComponent w d P) =
            z ^ (P.weightedTotalDegree w - d) *
              (z ^ d * MvPolynomial.eval₂ f x
              (MvPolynomial.weightedHomogeneousComponent w d P)) := by
          rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hdW]
        _ = z ^ (P.weightedTotalDegree w - d) * MvPolynomial.eval₂ f
              (fun i => z ^ w i * x i)
              (MvPolynomial.weightedHomogeneousComponent w d P) :=
          congrArg (fun y => z ^ (P.weightedTotalDegree w - d) * y) hscale.symm

/-- **Weighted boundary-value law.** If coordinate `i` has pole scale `w i`, then multiplying a
polynomial by its maximal weighted degree selects exactly its top weighted-homogeneous boundary
value, even while its coefficient homomorphism varies continuously. -/
theorem tendsto_pow_weightedTotalDegree_mul_eval₂
    {ι R : Type*} [Fintype ι] [CommSemiring R]
    (w : ι → ℕ) (P : MvPolynomial ι R)
    {f : ℂ → R →+* ℂ} {f₀ : R →+* ℂ}
    {a : ι → ℂ → ℂ} {r : ι → ℂ}
    (hf : ∀ c, Tendsto (fun z => f z c) (𝓝[≠] 0) (𝓝 (f₀ c)))
    (ha : ∀ i, Tendsto (fun z => z ^ w i * a i z) (𝓝[≠] 0) (𝓝 (r i))) :
    Tendsto
      (fun z => z ^ P.weightedTotalDegree w *
        MvPolynomial.eval₂ (f z) (fun i => a i z) P)
      (𝓝[≠] 0)
      (𝓝 (MvPolynomial.eval₂ f₀ r
        (MvPolynomial.weightedHomogeneousComponent w
          (P.weightedTotalDegree w) P))) := by
  classical
  let W := P.weightedTotalDegree w
  have hz : Tendsto (fun z : ℂ => z) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hterm : ∀ d ∈ Finset.range (W + 1),
      Tendsto
        (fun z => z ^ (W - d) *
          MvPolynomial.eval₂ (f z) (fun i => z ^ w i * a i z)
            (MvPolynomial.weightedHomogeneousComponent w d P))
        (𝓝[≠] 0)
        (𝓝 (if d = W then
          MvPolynomial.eval₂ f₀ r
            (MvPolynomial.weightedHomogeneousComponent w W P) else 0)) := by
    intro d hd
    have hpoly := tendsto_mvPolynomial_eval₂ hf ha
      (MvPolynomial.weightedHomogeneousComponent w d P)
    by_cases hdW : d = W
    · subst d
      simpa using hpoly
    · have hlt : d < W := lt_of_le_of_ne
          (Nat.le_of_lt_succ (Finset.mem_range.mp hd)) hdW
      have hpow : Tendsto (fun z : ℂ => z ^ (W - d)) (𝓝[≠] 0) (𝓝 0) := by
        simpa [zero_pow (Nat.sub_pos_of_lt hlt).ne'] using hz.pow (W - d)
      simpa [hdW] using hpow.mul hpoly
  have hsum := tendsto_finsetSum (s := Finset.range (W + 1))
    fun d hd => hterm d hd
  have hlimsum :
      (∑ d ∈ Finset.range (W + 1),
        (if d = W then MvPolynomial.eval₂ f₀ r
          (MvPolynomial.weightedHomogeneousComponent w W P) else 0)) =
        MvPolynomial.eval₂ f₀ r
          (MvPolynomial.weightedHomogeneousComponent w W P) := by
    rw [Finset.sum_eq_single W]
    · simp
    · intro d hd hne
      simp [hne]
    · simp
  rw [hlimsum] at hsum
  apply hsum.congr'
  exact Filter.Eventually.of_forall fun z =>
    (pow_weightedTotalDegree_mul_eval₂_eq_sum_weightedHomogeneousComponent
      w P (f z) (fun i => a i z) z).symm

/-- Exact top residue frame for the factorially normalized native Gamma jets. -/
def gammaPoleCovariantTopResidueValue (branch n : ℕ) : Fin (n + 1) → ℂ :=
  fun j => -(reciprocalGammaFactorialScale branch)⁻¹ ^ (j : ℕ) *
    ((-1 : ℂ) ^ (j : ℕ) * ((j : ℕ).factorial : ℂ))

/-- **Dynamic Gamma top-weight reflection.** The running covariant polynomial packet has the
same maximal weighted boundary value as its frozen top residue frame; coefficient polynomials
contribute only their value at the pole center. -/
theorem tendsto_pow_weightedTotalDegree_mul_gammaPoleCovariantPolynomialJetEval
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    Tendsto
      (fun x => x ^ P.weightedTotalDegree (bellJetWeight (n + 1)) *
        gammaPoleCovariantPolynomialJetEval branch n x P)
      (𝓝[≠] 0)
      (𝓝 (MvPolynomial.eval₂
        (Polynomial.evalRingHom (-(branch : ℂ)))
        (gammaPoleCovariantTopResidueValue branch n)
        (MvPolynomial.weightedHomogeneousComponent (bellJetWeight (n + 1))
          (P.weightedTotalDegree (bellJetWeight (n + 1))) P))) := by
  apply tendsto_pow_weightedTotalDegree_mul_eval₂
  · intro p
    have hcont : ContinuousAt
        (fun x : ℂ => p.eval
          (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  · intro j
    simpa [bellJetWeight, gammaPoleCovariantTopResidueValue] using
      tendsto_pow_succ_mul_gammaPoleCovariantJetValue branch (j : ℕ)

/-- Covariant Gamma packet with every polynomial coefficient frozen at the pole center. -/
def gammaPoleCenterFrozenCovariantPolynomialJetEval (branch n : ℕ) (x : ℂ) :
    MvPolynomial (Fin (n + 1)) (Polynomial ℂ) →+* ℂ :=
  MvPolynomial.eval₂Hom
    (Polynomial.evalRingHom (-(branch : ℂ)))
    (fun j => gammaPoleCovariantJetValue branch (j : ℕ) x)

/-- Center-frozen covariant packets remain meromorphic at the normalized pole. -/
theorem meromorphicAt_gammaPoleCenterFrozenCovariantPolynomialJetEval
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    MeromorphicAt
      (fun x => gammaPoleCenterFrozenCovariantPolynomialJetEval branch n x P) 0 := by
  induction P using MvPolynomial.induction_on with
  | C p =>
      have hconst : MeromorphicAt (fun _ : ℂ => p.eval (-(branch : ℂ))) 0 :=
        (analyticAt_const : AnalyticAt ℂ
          (fun _ : ℂ => p.eval (-(branch : ℂ))) 0).meromorphicAt
      exact hconst.congr (Filter.Eventually.of_forall fun x => by
        simp [gammaPoleCenterFrozenCovariantPolynomialJetEval])
  | add P Q hP hQ =>
      have h := hP.add hQ
      change MeromorphicAt
        (fun x =>
          gammaPoleCenterFrozenCovariantPolynomialJetEval branch n x P +
            gammaPoleCenterFrozenCovariantPolynomialJetEval branch n x Q) 0 at h
      simpa only [map_add] using h
  | mul_X P i hP =>
      have h := hP.mul (meromorphicAt_gammaPoleCovariantJetValue branch (i : ℕ))
      change MeromorphicAt
        (fun x =>
          gammaPoleCenterFrozenCovariantPolynomialJetEval branch n x P *
            gammaPoleCovariantJetValue branch (i : ℕ) x) 0 at h
      simpa [gammaPoleCenterFrozenCovariantPolynomialJetEval] using h

/-- The center-frozen packet has the same maximal weighted boundary as the running packet. -/
theorem tendsto_pow_weightedTotalDegree_mul_gammaPoleCenterFrozenCovariantPolynomialJetEval
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    Tendsto
      (fun x => x ^ P.weightedTotalDegree (bellJetWeight (n + 1)) *
        gammaPoleCenterFrozenCovariantPolynomialJetEval branch n x P)
      (𝓝[≠] 0)
      (𝓝 (MvPolynomial.eval₂
        (Polynomial.evalRingHom (-(branch : ℂ)))
        (gammaPoleCovariantTopResidueValue branch n)
        (MvPolynomial.weightedHomogeneousComponent (bellJetWeight (n + 1))
          (P.weightedTotalDegree (bellJetWeight (n + 1))) P))) := by
  apply tendsto_pow_weightedTotalDegree_mul_eval₂
  · intro p
    exact tendsto_const_nhds
  · intro j
    simpa [bellJetWeight, gammaPoleCovariantTopResidueValue] using
      tendsto_pow_succ_mul_gammaPoleCovariantJetValue branch (j : ℕ)

/-- **Running-to-frozen top-layer descent.** After maximal Bell-weight normalization, the
difference between running and center-frozen coefficient packets tends to zero. -/
theorem tendsto_pow_weightedTotalDegree_mul_gammaPoleCovariant_sub_centerFrozen
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    Tendsto
      (fun x => x ^ P.weightedTotalDegree (bellJetWeight (n + 1)) *
        (gammaPoleCovariantPolynomialJetEval branch n x P -
          gammaPoleCenterFrozenCovariantPolynomialJetEval branch n x P))
      (𝓝[≠] 0) (𝓝 0) := by
  have h :=
    (tendsto_pow_weightedTotalDegree_mul_gammaPoleCovariantPolynomialJetEval branch n P).sub
      (tendsto_pow_weightedTotalDegree_mul_gammaPoleCenterFrozenCovariantPolynomialJetEval
        branch n P)
  simpa only [sub_self] using h.congr'
    (Filter.Eventually.of_forall fun x => by ring)

/-- Running polynomial coefficients affect only orders strictly below the maximal Bell layer. -/
theorem neg_weightedTotalDegree_lt_meromorphicOrderAt_gammaPoleCovariant_sub_centerFrozen
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    ((-((P.weightedTotalDegree (bellJetWeight (n + 1)) : ℕ) : ℤ) : ℤ) : WithTop ℤ) <
      meromorphicOrderAt
        (fun x => gammaPoleCovariantPolynomialJetEval branch n x P -
          gammaPoleCenterFrozenCovariantPolynomialJetEval branch n x P) 0 := by
  apply neg_nat_lt_meromorphicOrderAt_of_tendsto_pow_mul_zero
    (P.weightedTotalDegree (bellJetWeight (n + 1)))
  · exact (meromorphicAt_gammaPoleCovariantPolynomialJetEval branch n P).sub
      (meromorphicAt_gammaPoleCenterFrozenCovariantPolynomialJetEval branch n P)
  · simpa using
      tendsto_pow_weightedTotalDegree_mul_gammaPoleCovariant_sub_centerFrozen branch n P

/-- The native Gamma packet differs from its center-frozen covariant model only below the maximal
Bell-weight pole layer. -/
theorem neg_weightedTotalDegree_lt_meromorphicOrderAt_gammaPolyJetEval_affine_sub_centerFrozen
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    ((-((P.weightedTotalDegree (bellJetWeight (n + 1)) : ℕ) : ℤ) : ℤ) : WithTop ℤ) <
      meromorphicOrderAt
        (fun x : ℂ => gammaPolyJetEval (n + 1)
            (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) P -
          gammaPoleCenterFrozenCovariantPolynomialJetEval branch n x P) 0 := by
  have hev :
      (fun x : ℂ => gammaPolyJetEval (n + 1)
          (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) P -
        gammaPoleCenterFrozenCovariantPolynomialJetEval branch n x P) =ᶠ[𝓝[≠] 0]
      (fun x => gammaPoleCovariantPolynomialJetEval branch n x P -
        gammaPoleCenterFrozenCovariantPolynomialJetEval branch n x P) :=
    (gammaPolyJetEval_affine_eventuallyEq_covariant branch n P).mono fun x hx =>
      congrArg (fun y => y - gammaPoleCenterFrozenCovariantPolynomialJetEval branch n x P) hx
  rw [meromorphicOrderAt_congr hev]
  exact neg_weightedTotalDegree_lt_meromorphicOrderAt_gammaPoleCovariant_sub_centerFrozen
    branch n P

/-- Every dynamic Gamma packet has pole order at least the negative maximal Bell weight. -/
theorem neg_weightedTotalDegree_le_meromorphicOrderAt_gammaPoleCovariantPolynomialJetEval
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    ((-((P.weightedTotalDegree (bellJetWeight (n + 1)) : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt
        (fun x => gammaPoleCovariantPolynomialJetEval branch n x P) 0 := by
  apply neg_nat_le_meromorphicOrderAt_of_tendsto_pow_mul
    (P.weightedTotalDegree (bellJetWeight (n + 1)))
    (meromorphicAt_gammaPoleCovariantPolynomialJetEval branch n P)
  simpa using
    tendsto_pow_weightedTotalDegree_mul_gammaPoleCovariantPolynomialJetEval branch n P

/-- Exact dynamic Gamma packet order is equivalent to noncancellation of its reflected top
weighted boundary value. -/
theorem meromorphicOrderAt_gammaPoleCovariantPolynomialJetEval_eq_iff
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    meromorphicOrderAt
        (fun x => gammaPoleCovariantPolynomialJetEval branch n x P) 0 =
        ((-((P.weightedTotalDegree (bellJetWeight (n + 1)) : ℕ) : ℤ) : ℤ) : WithTop ℤ) ↔
      MvPolynomial.eval₂
        (Polynomial.evalRingHom (-(branch : ℂ)))
        (gammaPoleCovariantTopResidueValue branch n)
        (MvPolynomial.weightedHomogeneousComponent (bellJetWeight (n + 1))
          (P.weightedTotalDegree (bellJetWeight (n + 1))) P) ≠ 0 := by
  apply meromorphicOrderAt_eq_neg_nat_iff_limit_ne_zero
    (P.weightedTotalDegree (bellJetWeight (n + 1)))
    (meromorphicAt_gammaPoleCovariantPolynomialJetEval branch n P)
  simpa using
    tendsto_pow_weightedTotalDegree_mul_gammaPoleCovariantPolynomialJetEval branch n P

/-- The native Gamma packet obeys the same exact order/noncancellation reflection. -/
theorem meromorphicOrderAt_gammaPolyJetEval_affine_eq_iff
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    meromorphicOrderAt
        (fun x : ℂ => gammaPolyJetEval (n + 1)
          (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) P) 0 =
        ((-((P.weightedTotalDegree (bellJetWeight (n + 1)) : ℕ) : ℤ) : ℤ) : WithTop ℤ) ↔
      MvPolynomial.eval₂
        (Polynomial.evalRingHom (-(branch : ℂ)))
        (gammaPoleCovariantTopResidueValue branch n)
        (MvPolynomial.weightedHomogeneousComponent (bellJetWeight (n + 1))
          (P.weightedTotalDegree (bellJetWeight (n + 1))) P) ≠ 0 := by
  rw [meromorphicOrderAt_gammaPolyJetEval_affine_eq_covariant]
  exact meromorphicOrderAt_gammaPoleCovariantPolynomialJetEval_eq_iff branch n P

end

end GaloisForLFunctions
