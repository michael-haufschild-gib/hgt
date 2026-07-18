import GaloisForLFunctions.HTGeometry.PolynomialTorsionLanguageDefectLimit
import GaloisForLFunctions.HTGeometry.FinitePiProductSummability
import GaloisForLFunctions.HTGeometry.MagnitudeWeightMassPolynomial

/-!
# Gaussian torsion-language tail lock

At the quadratic Taylor scale the dominant ADE face is not confined to a fixed finite
offset window.  Its complete offset lattice is nevertheless absolutely summable: a grouped
weight has only polynomial growth in the offsets, while the exact residual valuation is a
positive Gaussian quadratic form.  This file develops the two analytic exactification tools
which are special to that critical scale:

* exact expansion of a translated quadratic lattice energy;
* domination of a max-polynomial constrained Gaussian by the coordinatewise ambient Gaussian;
* vanishing of the corresponding finite-box tails;
* approximate finite Fourier inversion.  Unlike the finite-face zero theorem, this last result
  retains a uniform error `epsilon`; it is the step which permits the window radius to tend to
  infinity only after torsion recurrence has exposed a chosen Fourier coefficient.

No bounded-confinement assertion is made: offsets of every fixed size remain on the quadratic
face.
-/

open scoped BigOperators

namespace GaloisForLFunctions

open Filter Finset Topology

noncomputable section

/-! ## Exact quadratic offset energy -/

/-- The largest absolute coordinate of an integer lattice point, measured in `ℕ`. -/
def integerLatticeMaxNatAbs {ι : Type*} [Fintype ι] (z : ι → ℤ) : ℕ :=
  Finset.univ.sup fun i => (z i).natAbs

/-- Quadratic energy of an integer offset tuple. -/
def gaussianOffsetEnergy {ι : Type*} [Fintype ι] (z : ι → ℤ) : ℝ :=
  ∑ i, (z i : ℝ) ^ 2

/-- Translating every coordinate by the same real center splits the quadratic energy into its
center, source-sum, and transverse-offset terms. -/
theorem sum_sq_add_eq_center_source_offset
    {ι : Type*} [Fintype ι] (q : ℝ) (z : ι → ℤ) :
    (∑ i, (q + (z i : ℝ)) ^ 2) =
      (Fintype.card ι : ℝ) * q ^ 2 +
        2 * q * (∑ i, (z i : ℝ)) + gaussianOffsetEnergy z := by
  simp only [gaussianOffsetEnergy]
  simp_rw [add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show (∑ i, 2 * q * (z i : ℝ)) =
      2 * q * ∑ i, (z i : ℝ) by
    rw [Finset.mul_sum]]

/-- Exact quadratic expansion for a bounded multiplicity pattern. -/
theorem polynomialPatternPowerValuation_two
    {M D : ℕ} (p : Fin M → Fin (D + 1)) (t : ℝ)
    (hcount : (∑ r, (p r : ℕ)) = D) :
    polynomialPatternPowerValuation 2 p t =
      (D : ℝ) * t ^ 2 +
        2 * t * (polynomialPatternMoment p 1 : ℝ) +
          (polynomialPatternMoment p 2 : ℝ) := by
  rw [polynomialPatternPowerValuation]
  simp_rw [Real.rpow_two, add_sq, mul_add, Finset.sum_add_distrib]
  have hcountR : (∑ x, ((p x : ℕ) : ℝ)) = D := by
    exact_mod_cast hcount
  have hm1 : (∑ x, ((p x : ℕ) : ℝ) * (x : ℝ)) =
      (polynomialPatternMoment p 1 : ℝ) := by
    rw [polynomialPatternMoment]
    push_cast
    simp only [pow_one]
  have hm2 : (∑ x, ((p x : ℕ) : ℝ) * (x : ℝ) ^ 2) =
      (polynomialPatternMoment p 2 : ℝ) := by
    rw [polynomialPatternMoment]
    push_cast
    rfl
  have hfirst : (∑ x, ((p x : ℕ) : ℝ) * t ^ 2) = (D : ℝ) * t ^ 2 := by
    rw [← Finset.sum_mul, hcountR]
  have hmiddle : (∑ x, ((p x : ℕ) : ℝ) * (2 * t * (x : ℝ))) =
      2 * t * (polynomialPatternMoment p 1 : ℝ) := by
    rw [← hm1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  rw [hfirst, hmiddle, hm2]

/-- Equal count and equal source sum make the quadratic valuation difference independent of the
translated center. -/
theorem polynomialPatternPowerValuation_two_sub_of_moment_one_eq
    {M D : ℕ} (p r : Fin M → Fin (D + 1)) (t : ℝ)
    (hpcount : (∑ j, (p j : ℕ)) = D)
    (hrcount : (∑ j, (r j : ℕ)) = D)
    (hmoment : polynomialPatternMoment p 1 = polynomialPatternMoment r 1) :
    polynomialPatternPowerValuation 2 p t -
        polynomialPatternPowerValuation 2 r t =
      (polynomialPatternMoment p 2 : ℝ) -
        (polynomialPatternMoment r 2 : ℝ) := by
  rw [polynomialPatternPowerValuation_two p t hpcount,
    polynomialPatternPowerValuation_two r t hrcount, hmoment]
  ring

/-- At the Gaussian exponent, increasing the source sum produces an eventual linear valuation
gap.  This is the critical-scale replacement for the `beta > 2` source-gap lemma. -/
theorem eventually_polynomialPatternPower_two_gap_of_sourceSum_lt
    {M D : ℕ} (p₀ p : Fin M → Fin (D + 1))
    (hcount₀ : (∑ r, (p₀ r : ℕ)) = D)
    (hcount : (∑ r, (p r : ℕ)) = D)
    (hsource : polynomialPatternSourceSum p₀ < polynomialPatternSourceSum p) :
    ∀ᶠ t : ℝ in atTop,
      t ≤ polynomialPatternPowerValuation 2 p t -
        polynomialPatternPowerValuation 2 p₀ t := by
  have hm1Nat : polynomialPatternMoment p₀ 1 < polynomialPatternMoment p 1 := by
    rw [polynomialPatternMoment_one, polynomialPatternMoment_one]
    simpa [polynomialPatternSourceSum] using hsource
  have hm1 : (1 : ℝ) ≤
      (polynomialPatternMoment p 1 : ℝ) -
        (polynomialPatternMoment p₀ 1 : ℝ) := by
    have hm1cast : (polynomialPatternMoment p₀ 1 : ℝ) + 1 ≤
        (polynomialPatternMoment p 1 : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hm1Nat)
    linarith
  let b : ℝ := (polynomialPatternMoment p 2 : ℝ) -
    (polynomialPatternMoment p₀ 2 : ℝ)
  filter_upwards [eventually_ge_atTop |b|] with t ht
  rw [polynomialPatternPowerValuation_two p t hcount,
    polynomialPatternPowerValuation_two p₀ t hcount₀]
  have ht0 : 0 ≤ t := (abs_nonneg b).trans ht
  have hb : -|b| ≤ b := neg_abs_le b
  dsimp [b] at ht hb ⊢
  nlinarith

/-- On a finite family, the Gaussian source gap is uniform outside the least-source class. -/
theorem eventually_uniform_polynomialPatternPower_two_source_gap
    {M D : ℕ} (S : Finset (Fin M → Fin (D + 1))) (hS : S.Nonempty)
    (hcount : ∀ p ∈ S, (∑ r, (p r : ℕ)) = D)
    (p₀ : Fin M → Fin (D + 1))
    (hp₀ : p₀ ∈ polynomialPatternLeastSourceClass S hS) :
    ∀ᶠ t : ℝ in atTop, ∀ p ∈ S \ polynomialPatternLeastSourceClass S hS,
      t ≤ polynomialPatternPowerValuation 2 p t -
        polynomialPatternPowerValuation 2 p₀ t := by
  let T := S \ polynomialPatternLeastSourceClass S hS
  have hp₀S : p₀ ∈ S := polynomialPatternLeastSourceClass_subset S hS hp₀
  have hp₀source := sourceSum_eq_of_mem_polynomialPatternLeastSourceClass hp₀
  have hgap : ∀ p : ↥T, ∀ᶠ t : ℝ in atTop,
      t ≤ polynomialPatternPowerValuation 2 p.1 t -
        polynomialPatternPowerValuation 2 p₀ t := by
    intro p
    have hpS : p.1 ∈ S := (Finset.mem_sdiff.mp p.2).1
    have hpClass : p.1 ∉ polynomialPatternLeastSourceClass S hS :=
      (Finset.mem_sdiff.mp p.2).2
    have hsource : polynomialPatternSourceSum p₀ <
        polynomialPatternSourceSum p.1 := by
      rw [hp₀source]
      exact minimalSourceSum_lt_of_mem_not_class hS hpS hpClass
    exact eventually_polynomialPatternPower_two_gap_of_sourceSum_lt p₀ p.1
      (hcount p₀ hp₀S) (hcount p.1 hpS) hsource
  have hall : ∀ᶠ t : ℝ in atTop, ∀ p : ↥T,
      t ≤ polynomialPatternPowerValuation 2 p.1 t -
        polynomialPatternPowerValuation 2 p₀ t := eventually_all.mpr hgap
  filter_upwards [hall] with t ht
  intro p hp
  exact ht ⟨p, hp⟩

/-! ## Global Gaussian offset faces -/

/-- Integer offsets represented by the centered finite window `[-R,R]`. -/
def gaussianOffsetInterval (R : ℕ) : Finset ℤ :=
  Finset.Icc (-(R : ℤ)) (R : ℤ)

/-- Signed source sum of a finite multiplicity pattern on integer offsets. -/
def gaussianOffsetSource (a : ℤ →₀ ℕ) : ℤ :=
  a.sum fun r k => r * (k : ℤ)

/-- Quadratic energy of a finite multiplicity pattern on integer offsets. -/
def gaussianOffsetPatternEnergy (a : ℤ →₀ ℕ) : ℤ :=
  a.sum fun r k => r ^ 2 * (k : ℤ)

/-- Degree-`D`, signed-source-`S` Gaussian patterns supported in `[-R,R]`. -/
def gaussianOffsetFace (D : ℕ) (S : ℤ) (R : ℕ) : Finset (ℤ →₀ ℕ) :=
  ((gaussianOffsetInterval R).finsuppAntidiag D).filter fun a =>
    gaussianOffsetSource a = S

@[simp] theorem mem_gaussianOffsetFace
    {D : ℕ} {S : ℤ} {R : ℕ} {a : ℤ →₀ ℕ} :
    a ∈ gaussianOffsetFace D S R ↔
      (∑ r ∈ gaussianOffsetInterval R, a r) = D ∧
      a.support ⊆ gaussianOffsetInterval R ∧ gaussianOffsetSource a = S := by
  simp [gaussianOffsetFace, Finset.mem_finsuppAntidiag, and_assoc]

theorem gaussianOffsetFace_totalCount
    {D : ℕ} {S : ℤ} {R : ℕ} {a : ℤ →₀ ℕ}
    (ha : a ∈ gaussianOffsetFace D S R) :
    a.sum (fun _ k => k) = D := by
  obtain ⟨hcount, hsupp, _hsource⟩ := mem_gaussianOffsetFace.mp ha
  rw [Finsupp.sum_of_support_subset a hsupp (fun _ k => k) (by simp)]
  exact hcount

theorem gaussianOffsetFace_mono
    {D : ℕ} {S : ℤ} {R R' : ℕ} (hRR' : R ≤ R') :
    gaussianOffsetFace D S R ⊆ gaussianOffsetFace D S R' := by
  intro a ha
  obtain ⟨_hcount, hsupp, hsource⟩ := mem_gaussianOffsetFace.mp ha
  have hinterval : gaussianOffsetInterval R ⊆ gaussianOffsetInterval R' := by
    intro z hz
    simp only [gaussianOffsetInterval, Finset.mem_Icc] at hz ⊢
    constructor <;> omega
  have hsupp' : a.support ⊆ gaussianOffsetInterval R' := hsupp.trans hinterval
  have hcount' : (∑ r ∈ gaussianOffsetInterval R', a r) = D := by
    rw [← gaussianOffsetFace_totalCount ha,
      Finsupp.sum_of_support_subset a hsupp' (fun _ k => k) (by simp)]
  exact mem_gaussianOffsetFace.mpr ⟨hcount', hsupp', hsource⟩

/-- Canonical equivalence between a centered window index and its signed integer offset. -/
noncomputable def centeredIndexEquiv (R : ℕ) :
    Fin (2 * R + 1) ≃ ↥(gaussianOffsetInterval R) where
  toFun j := ⟨(j : ℤ) - (R : ℤ), by
    simp only [gaussianOffsetInterval, Finset.mem_Icc]
    have hj := j.isLt
    constructor <;> omega⟩
  invFun z := ⟨Int.toNat (z.1 + (R : ℤ)), by
    have hz := z.2
    simp only [gaussianOffsetInterval, Finset.mem_Icc] at hz
    have hnonneg : 0 ≤ z.1 + (R : ℤ) := by omega
    apply (Int.toNat_lt hnonneg).2
    omega⟩
  left_inv j := by
    apply Fin.ext
    simp only
    have heq : (j : ℤ) - (R : ℤ) + (R : ℤ) = (j : ℤ) := by ring
    rw [heq]
    simp
  right_inv z := by
    apply Subtype.ext
    simp only
    have hz := z.2
    simp only [gaussianOffsetInterval, Finset.mem_Icc] at hz
    have hnonneg : 0 ≤ z.1 + (R : ℤ) := by omega
    rw [Int.toNat_of_nonneg hnonneg]
    omega

/-- Window multiplicities of a global degree-`D` offset pattern. -/
noncomputable def gaussianOffsetPatternWindow
    {D : ℕ} (a : ℤ →₀ ℕ) (hcount : a.sum (fun _ k => k) = D) (R : ℕ) :
    Fin (2 * R + 1) → Fin (D + 1) := fun j =>
  ⟨a ((centeredIndexEquiv R j).1), by
    have hle : a ((centeredIndexEquiv R j).1) ≤ a.sum (fun _ k => k) := by
      classical
      rw [Finsupp.sum]
      by_cases hj : (centeredIndexEquiv R j).1 ∈ a.support
      · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
      · have hz : a ((centeredIndexEquiv R j).1) = 0 := by
          simpa [Finsupp.mem_support_iff] using hj
        simp [hz]
    rw [hcount] at hle
    omega⟩

theorem gaussianOffsetPatternWindow_count
    {D : ℕ} {S : ℤ} {R : ℕ} {a : ℤ →₀ ℕ}
    (ha : a ∈ gaussianOffsetFace D S R) :
    (∑ j, (gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount ha) R j : ℕ)) = D := by
  let hcount := gaussianOffsetFace_totalCount ha
  have hsupp := (mem_gaussianOffsetFace.mp ha).2.1
  change (∑ j : Fin (2 * R + 1), a ((centeredIndexEquiv R j).1)) = D
  calc
    (∑ j : Fin (2 * R + 1), a ((centeredIndexEquiv R j).1)) =
        ∑ z : ↥(gaussianOffsetInterval R), a z.1 :=
      Equiv.sum_comp (centeredIndexEquiv R) (fun z => a z.1)
    _ = ∑ z ∈ gaussianOffsetInterval R, a z := by
      simpa using (Finset.sum_attach (gaussianOffsetInterval R) (fun z => a z))
    _ = a.sum (fun _ k => k) := by
      symm
      exact Finsupp.sum_of_support_subset a hsupp (fun _ k => k) (by simp)
    _ = D := hcount

/-! ## Uniform grouped-weight bounds -/

/-- The translation polynomial of one labelled assignment has degree at most the total jet order
of its differential monomial. -/
theorem natDegree_polynomialPatternAssignmentPoly_le
    {n D K τ M : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {p : Fin M → Fin (D + 1)}
    (m : ↥(polynomialPatternJetGroup n D K τ Q p)) (g : Fin D → Fin M) :
    (polynomialPatternAssignmentPoly m g).natDegree ≤
      jetMonomialOrder n m.1 := by
  rw [polynomialPatternAssignmentPoly]
  calc
    (∏ t : Fin (jetMonomialDegree n m.1),
        (descPochhammer ℂ (flatOrder (fun j => m.1 j.succ) t)).comp
          (Polynomial.X + Polynomial.C
            (((((g (polynomialPatternJetCast m t) : Fin M) : ℕ) : ℤ) -
              (K : ℤ) : ℤ) : ℂ))).natDegree
        ≤ ∑ t : Fin (jetMonomialDegree n m.1),
            ((descPochhammer ℂ (flatOrder (fun j => m.1 j.succ) t)).comp
              (Polynomial.X + Polynomial.C
                (((((g (polynomialPatternJetCast m t) : Fin M) : ℕ) : ℤ) -
                  (K : ℤ) : ℤ) : ℂ))).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ t : Fin (jetMonomialDegree n m.1),
          flatOrder (fun j => m.1 j.succ) t := by
      apply Finset.sum_le_sum
      intro t _ht
      calc
        ((descPochhammer ℂ (flatOrder (fun j => m.1 j.succ) t)).comp
            (Polynomial.X + Polynomial.C
              (((((g (polynomialPatternJetCast m t) : Fin M) : ℕ) : ℤ) -
                (K : ℤ) : ℤ) : ℂ))).natDegree
            ≤ (descPochhammer ℂ (flatOrder (fun j => m.1 j.succ) t)).natDegree *
              (Polynomial.X + Polynomial.C
                (((((g (polynomialPatternJetCast m t) : Fin M) : ℕ) : ℤ) -
                  (K : ℤ) : ℤ) : ℂ)).natDegree := Polynomial.natDegree_comp_le
        _ = flatOrder (fun j => m.1 j.succ) t := by
          rw [descPochhammer_natDegree, Polynomial.natDegree_X_add_C, mul_one]
    _ = jetMonomialOrder n m.1 := by
      simpa [jetMonomialOrder] using
        (flatOrder_sum (fun j => m.1 j.succ))

/-- A common order bound for the active jet group is also a degree bound for its grouped pattern
weight polynomial. -/
theorem natDegree_polynomialPatternWeightPoly_le_of_order_le
    {n D K τ M H : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (p : Fin M → Fin (D + 1))
    (horder : ∀ m : ↥(polynomialPatternJetGroup n D K τ Q p),
      jetMonomialOrder n m.1 ≤ H) :
    (polynomialPatternWeightPoly n D K τ Q p).natDegree ≤ H := by
  classical
  rw [polynomialPatternWeightPoly]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m _hm
  refine (Polynomial.natDegree_mul_le).trans ?_
  have hinner :
      (∑ g ∈ atomPatternAssignments p,
        polynomialPatternAssignmentPoly m g).natDegree ≤ H := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro g _hg
    exact (natDegree_polynomialPatternAssignmentPoly_le m g).trans (horder m)
  simpa using hinner

/-- In particular, the maximal jet order bounds the degree of every grouped pattern weight. -/
theorem natDegree_polynomialPatternWeightPoly_le_maxJetOrder
    {n D K τ M : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (p : Fin M → Fin (D + 1)) :
    (polynomialPatternWeightPoly n D K τ Q p).natDegree ≤
      magnitudeMaxJetOrder n Q := by
  apply natDegree_polynomialPatternWeightPoly_le_of_order_le Q p
  intro m
  exact jetOrder_le_magnitudeMaxJetOrder Q
    (Finset.mem_filter.mp m.2).1

/-- The corresponding integer grouped weight has the same uniform degree bound. -/
theorem natDegree_polynomialPatternWeightPolyInt_le_maxJetOrder
    {n D K τ M : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (c : (Fin (n + 2) →₀ ℕ) → ℤ)
    (hc : ∀ m, MvPolynomial.coeff m Q = (c m : ℂ))
    (p : Fin M → Fin (D + 1)) :
    (polynomialPatternWeightPolyInt n D K τ Q c p).natDegree ≤
      magnitudeMaxJetOrder n Q := by
  have hdeg := natDegree_polynomialPatternWeightPoly_le_maxJetOrder
    (K := K) (τ := τ) Q p
  rw [← map_polynomialPatternWeightPolyInt n D K τ Q c hc p,
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective] at hdeg
  exact hdeg

/-- Any common active-order bound supplies coefficientwise convergence after normalization by
that order. -/
theorem tendsto_polynomialPatternWeightPoly_eval_div_pow_of_order_le
    {n D K τ M H : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (p : Fin M → Fin (D + 1))
    (horder : ∀ m : ↥(polynomialPatternJetGroup n D K τ Q p),
      jetMonomialOrder n m.1 ≤ H) :
    Tendsto (fun q : ℕ =>
      (polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ) /
        (q : ℂ) ^ H) atTop
      (𝓝 ((polynomialPatternWeightPoly n D K τ Q p).coeff H)) := by
  exact tendsto_complexPolynomial_eval_nat_div_pow _
    (natDegree_polynomialPatternWeightPoly_le_of_order_le Q p horder)

/-- The integer-polynomial presentation has the same normalized complex limit. -/
theorem tendsto_polynomialPatternWeightPolyInt_eval_div_pow_of_order_le
    {n D K τ M H : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (c : (Fin (n + 2) →₀ ℕ) → ℤ)
    (hc : ∀ m, MvPolynomial.coeff m Q = (c m : ℂ))
    (p : Fin M → Fin (D + 1))
    (horder : ∀ m : ↥(polynomialPatternJetGroup n D K τ Q p),
      jetMonomialOrder n m.1 ≤ H) :
    Tendsto (fun q : ℕ =>
      (((polynomialPatternWeightPolyInt n D K τ Q c p).eval (q : ℤ) : ℤ) : ℂ) /
        (q : ℂ) ^ H) atTop
      (𝓝 ((polynomialPatternWeightPoly n D K τ Q p).coeff H)) := by
  apply (tendsto_polynomialPatternWeightPoly_eval_div_pow_of_order_le
    Q p horder).congr'
  apply Eventually.of_forall
  intro q
  apply congrArg (fun z : ℂ => z / (q : ℂ) ^ H)
  rw [← map_polynomialPatternWeightPolyInt n D K τ Q c hc p]
  exact (Polynomial.eval_map_apply (p :=
    polynomialPatternWeightPolyInt n D K τ Q c p)
      (Int.castRingHom ℂ) (q : ℤ))

/-- Coefficientwise maximal-order normalization of every grouped pattern weight converges to its
maximal-order coefficient. -/
theorem tendsto_polynomialPatternWeightPoly_eval_div_pow_maxJetOrder
    {n D K τ M : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (p : Fin M → Fin (D + 1)) :
    Tendsto (fun q : ℕ =>
      (polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ) /
        (q : ℂ) ^ magnitudeMaxJetOrder n Q) atTop
      (𝓝 ((polynomialPatternWeightPoly n D K τ Q p).coeff
        (magnitudeMaxJetOrder n Q))) := by
  apply tendsto_polynomialPatternWeightPoly_eval_div_pow_of_order_le Q p
  intro m
  exact jetOrder_le_magnitudeMaxJetOrder Q
    (Finset.mem_filter.mp m.2).1

/-- Coordinates actually used by a bounded multiplicity pattern. -/
def polynomialPatternSupport {M D : ℕ} (p : Fin M → Fin (D + 1)) : Finset (Fin M) :=
  Finset.univ.filter fun r => p r ≠ 0

/-- Largest absolute offset of an active pattern coordinate from the chosen center `K`. -/
def centeredPolynomialPatternRadius {M D : ℕ}
    (K : ℕ) (p : Fin M → Fin (D + 1)) : ℕ :=
  (polynomialPatternSupport p).sup fun r =>
    (((r : ℕ) : ℤ) - (K : ℤ)).natAbs

theorem atomPatternAssignment_mem_polynomialPatternSupport
    {M D : ℕ} {p : Fin M → Fin (D + 1)}
    {g : Fin D → Fin M} (hg : g ∈ atomPatternAssignments p) (t : Fin D) :
    g t ∈ polynomialPatternSupport p := by
  classical
  rw [polynomialPatternSupport, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hzero
  have hkey := mem_atomPatternAssignments.mp hg
  have hpos : key (fun j => (g j : ℕ)) (g t : ℕ) ≠ 0 := by
    rw [key_count_map]
    exact Multiset.count_ne_zero.mpr (by simp)
  apply hpos
  rw [hkey, atomPatternKey_apply]
  simp [hzero, (g t).isLt]

theorem polynomialPatternSupport_card_le_count
    {M D : ℕ} (p : Fin M → Fin (D + 1))
    (hcount : (∑ r, (p r : ℕ)) = D) :
    (polynomialPatternSupport p).card ≤ D := by
  classical
  calc
    (polynomialPatternSupport p).card =
        ∑ _r ∈ polynomialPatternSupport p, 1 := by simp
    _ ≤ ∑ r ∈ polynomialPatternSupport p, (p r : ℕ) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrne : p r ≠ 0 := (Finset.mem_filter.mp hr).2
      have hrneNat : (p r : ℕ) ≠ 0 := by
        intro h
        apply hrne
        apply Fin.ext
        exact h
      omega
    _ ≤ ∑ r : Fin M, (p r : ℕ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro r _hr _hnot
        exact Nat.zero_le _
    _ = D := hcount

/-- The number of labelled assignments of a degree-`D` multiplicity pattern is bounded solely by
`D^D`, independently of the ambient window size. -/
theorem atomPatternAssignments_card_le_pow_count
    {M D : ℕ} (p : Fin M → Fin (D + 1))
    (hcount : (∑ r, (p r : ℕ)) = D) :
    (atomPatternAssignments p).card ≤ D ^ D := by
  classical
  let A := atomPatternAssignments p
  let S := polynomialPatternSupport p
  let encode : ↥A → (Fin D → ↥S) := fun g t =>
    ⟨g.1 t, atomPatternAssignment_mem_polynomialPatternSupport g.2 t⟩
  have hencode : Function.Injective encode := by
    intro g h hgh
    apply Subtype.ext
    funext t
    exact congrArg (fun e : Fin D → ↥S => (e t).1) hgh
  calc
    (atomPatternAssignments p).card = Fintype.card ↥A := by simp [A]
    _ ≤ Fintype.card (Fin D → ↥S) := Fintype.card_le_of_injective encode hencode
    _ = (polynomialPatternSupport p).card ^ D := by simp [S]
    _ ≤ D ^ D := Nat.pow_le_pow_left
      (polynomialPatternSupport_card_le_count p hcount) _

theorem assignment_centered_offset_le_radius
    {M D K : ℕ} {p : Fin M → Fin (D + 1)}
    {g : Fin D → Fin M} (hg : g ∈ atomPatternAssignments p) (t : Fin D) :
    ((((g t : Fin M) : ℕ) : ℤ) - (K : ℤ)).natAbs ≤
      centeredPolynomialPatternRadius K p := by
  exact Finset.le_sup (f := fun r : Fin M =>
    (((r : ℕ) : ℤ) - (K : ℤ)).natAbs)
      (atomPatternAssignment_mem_polynomialPatternSupport hg t)

theorem windowShift_assignment_le_center_add_radius
    {M D q K : ℕ} {p : Fin M → Fin (D + 1)}
    {g : Fin D → Fin M} (hg : g ∈ atomPatternAssignments p)
    (hKq : K ≤ q) (t : Fin D) :
    windowShift q K (g t : ℕ) ≤ q + centeredPolynomialPatternRadius K p := by
  have hoffNat := assignment_centered_offset_le_radius (K := K) hg t
  have hoffInt :
      |((((g t : Fin M) : ℕ) : ℤ) - (K : ℤ))| ≤
        (centeredPolynomialPatternRadius K p : ℤ) := by
    have hcast :
        ((((((g t : Fin M) : ℕ) : ℤ) - (K : ℤ)).natAbs : ℕ) : ℤ) ≤
          (centeredPolynomialPatternRadius K p : ℤ) := by
      exact_mod_cast hoffNat
    rw [Int.natCast_natAbs] at hcast
    exact hcast
  have hupper := (abs_le.mp hoffInt).2
  dsimp [windowShift]
  omega

/-- A labelled assignment whose contributing jet monomial has order at most `H` is bounded by
one common `H`-th power.  The estimate is uniform in the multiplicity pattern and in the window
offsets. -/
theorem norm_windowShift_descFactorial_prod_le
    {n D K τ M q H : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {p : Fin M → Fin (D + 1)}
    (m : ↥(polynomialPatternJetGroup n D K τ Q p))
    (g : Fin D → Fin M) (hKq : K ≤ q) (hq : 1 ≤ q)
    (horder : jetMonomialOrder n m.1 ≤ H) :
    ‖∏ t : Fin (jetMonomialDegree n m.1),
        ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
          (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖ ≤
      (((q + M) ^ H : ℕ) : ℝ) := by
  rw [norm_prod]
  have hfactor : ∀ t : Fin (jetMonomialDegree n m.1),
      ‖((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
          (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖ ≤
        ((((q + M) ^ (flatOrder (fun j => m.1 j.succ) t)) : ℕ) : ℝ) := by
    intro t
    rw [Complex.norm_natCast]
    exact_mod_cast calc
      (windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
          (flatOrder (fun j => m.1 j.succ) t)
          ≤ (windowShift q K (g (polynomialPatternJetCast m t) : ℕ)) ^
              (flatOrder (fun j => m.1 j.succ) t) :=
            Nat.descFactorial_le_pow _ _
      _ ≤ (q + M) ^ (flatOrder (fun j => m.1 j.succ) t) := by
            apply Nat.pow_le_pow_left
            dsimp [windowShift]
            have hglt := (g (polynomialPatternJetCast m t)).isLt
            omega
  calc
    ∏ t, ‖((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
          (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖
        ≤ ∏ t, ((((q + M) ^ (flatOrder (fun j => m.1 j.succ) t)) : ℕ) : ℝ) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun t _ => hfactor t)
    _ = ((((q + M) ^
          (∑ t, flatOrder (fun j => m.1 j.succ) t)) : ℕ) : ℝ) := by
      push_cast
      rw [← Finset.prod_pow_eq_pow_sum]
    _ ≤ (((q + M) ^ H : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega) (by
        rw [flatOrder_sum]
        exact horder)

/-- Once an assignment is restricted to the support of a multiplicity pattern, its factorial
weight is controlled by the centered support radius rather than by the ambient window length.
This is the estimate which remains useful when the window itself grows with the translation
parameter. -/
theorem norm_windowShift_descFactorial_prod_le_centeredRadius
    {n D K τ M q H : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {p : Fin M → Fin (D + 1)}
    (m : ↥(polynomialPatternJetGroup n D K τ Q p))
    (g : Fin D → Fin M) (hg : g ∈ atomPatternAssignments p)
    (hKq : K ≤ q) (hq : 1 ≤ q)
    (horder : jetMonomialOrder n m.1 ≤ H) :
    ‖∏ t : Fin (jetMonomialDegree n m.1),
        ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
          (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖ ≤
      (((q + centeredPolynomialPatternRadius K p) ^ H : ℕ) : ℝ) := by
  rw [norm_prod]
  have hfactor : ∀ t : Fin (jetMonomialDegree n m.1),
      ‖((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
          (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖ ≤
        ((((q + centeredPolynomialPatternRadius K p) ^
          (flatOrder (fun j => m.1 j.succ) t)) : ℕ) : ℝ) := by
    intro t
    rw [Complex.norm_natCast]
    exact_mod_cast calc
      (windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
          (flatOrder (fun j => m.1 j.succ) t)
          ≤ (windowShift q K (g (polynomialPatternJetCast m t) : ℕ)) ^
              (flatOrder (fun j => m.1 j.succ) t) :=
            Nat.descFactorial_le_pow _ _
      _ ≤ (q + centeredPolynomialPatternRadius K p) ^
          (flatOrder (fun j => m.1 j.succ) t) := by
            apply Nat.pow_le_pow_left
            exact windowShift_assignment_le_center_add_radius
              hg hKq (polynomialPatternJetCast m t)
  calc
    ∏ t, ‖((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
          (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖
        ≤ ∏ t, ((((q + centeredPolynomialPatternRadius K p) ^
            (flatOrder (fun j => m.1 j.succ) t)) : ℕ) : ℝ) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun t _ => hfactor t)
    _ = ((((q + centeredPolynomialPatternRadius K p) ^
          (∑ t, flatOrder (fun j => m.1 j.succ) t)) : ℕ) : ℝ) := by
      push_cast
      rw [← Finset.prod_pow_eq_pow_sum]
    _ ≤ (((q + centeredPolynomialPatternRadius K p) ^ H : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega) (by
        rw [flatOrder_sum]
        exact horder)

/-- Every grouped bounded-pattern weight has a polynomial bound which is uniform over the
pattern.  The only window dependence is the explicit cardinal factor `M^D`; no coefficient-level
constant depends on the offsets. -/
theorem norm_eval_polynomialPatternWeightPoly_le
    {n D K τ M q H : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (p : Fin M → Fin (D + 1)) (hKq : K ≤ q) (hq : 1 ≤ q)
    (horder : ∀ m : ↥(polynomialPatternJetGroup n D K τ Q p),
      jetMonomialOrder n m.1 ≤ H) :
    ‖(polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ)‖ ≤
      magnitudeCoefficientMass Q * (((M ^ D : ℕ) : ℝ)) *
        (((q + M) ^ H : ℕ) : ℝ) := by
  classical
  rw [eval_polynomialPatternWeightPoly n D K τ Q p hKq]
  let A : ℝ := (((M ^ D : ℕ) : ℝ))
  let X : ℝ := (((q + M) ^ H : ℕ) : ℝ)
  have hcard : (atomPatternAssignments p).card ≤ M ^ D := by
    calc
      (atomPatternAssignments p).card ≤
          Fintype.card (Fin D → Fin M) := Finset.card_le_univ _
      _ = M ^ D := by simp
  have hinner : ∀ m : ↥(polynomialPatternJetGroup n D K τ Q p),
      ‖∑ g ∈ atomPatternAssignments p,
          ∏ t : Fin (jetMonomialDegree n m.1),
            ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
              (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖ ≤ A * X := by
    intro m
    calc
      ‖∑ g ∈ atomPatternAssignments p,
          ∏ t : Fin (jetMonomialDegree n m.1),
            ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
              (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖
          ≤ ∑ g ∈ atomPatternAssignments p,
              ‖∏ t : Fin (jetMonomialDegree n m.1),
                ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
                  (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _g ∈ atomPatternAssignments p, X := by
        apply Finset.sum_le_sum
        intro g _hg
        exact norm_windowShift_descFactorial_prod_le m g hKq hq (horder m)
      _ = ((atomPatternAssignments p).card : ℝ) * X := by simp
      _ ≤ A * X := by
        apply mul_le_mul_of_nonneg_right _ (by dsimp [X]; positivity)
        dsimp [A]
        exact_mod_cast hcard
  have hcoeff :
      (∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
        ‖MvPolynomial.coeff m.1 Q‖) ≤ magnitudeCoefficientMass Q := by
    calc
      (∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
          ‖MvPolynomial.coeff m.1 Q‖) =
          ∑ m ∈ polynomialPatternJetGroup n D K τ Q p,
            ‖MvPolynomial.coeff m Q‖ :=
        by simpa using
          (Finset.sum_attach (polynomialPatternJetGroup n D K τ Q p)
            (fun m => ‖MvPolynomial.coeff m Q‖))
      _ ≤ ∑ m ∈ Q.support, ‖MvPolynomial.coeff m Q‖ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro m _hm _hnot
          positivity
      _ = magnitudeCoefficientMass Q := by rfl
  calc
    ‖∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
        MvPolynomial.coeff m.1 Q *
          ∑ g ∈ atomPatternAssignments p,
            ∏ t : Fin (jetMonomialDegree n m.1),
              ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
                (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖
        ≤ ∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
            ‖MvPolynomial.coeff m.1 Q *
              ∑ g ∈ atomPatternAssignments p,
                ∏ t : Fin (jetMonomialDegree n m.1),
                  ((windowShift q K
                    (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
                    (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
          ‖MvPolynomial.coeff m.1 Q‖ * (A * X) := by
      apply Finset.sum_le_sum
      intro m _hm
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hinner m) (norm_nonneg _)
    _ = (∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
          ‖MvPolynomial.coeff m.1 Q‖) * (A * X) := by
      rw [Finset.sum_mul]
    _ ≤ magnitudeCoefficientMass Q * (A * X) :=
      mul_le_mul_of_nonneg_right hcoeff (by dsimp [A, X]; positivity)
    _ = magnitudeCoefficientMass Q * (((M ^ D : ℕ) : ℝ)) *
          (((q + M) ^ H : ℕ) : ℝ) := by
      dsimp [A, X]
      ring

/-- The grouped weight of a degree-`D` pattern is bounded using only its centered support radius.
The ambient window cardinality has disappeared: the assignment count is at most `D^D`, because
every labelled atom must land in the at-most-`D` active support positions. -/
theorem norm_eval_polynomialPatternWeightPoly_le_centeredRadius
    {n D K τ M q H : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (p : Fin M → Fin (D + 1))
    (hcount : (∑ r, (p r : ℕ)) = D)
    (hKq : K ≤ q) (hq : 1 ≤ q)
    (horder : ∀ m : ↥(polynomialPatternJetGroup n D K τ Q p),
      jetMonomialOrder n m.1 ≤ H) :
    ‖(polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ)‖ ≤
      magnitudeCoefficientMass Q * (((D ^ D : ℕ) : ℝ)) *
        (((q + centeredPolynomialPatternRadius K p) ^ H : ℕ) : ℝ) := by
  classical
  rw [eval_polynomialPatternWeightPoly n D K τ Q p hKq]
  let A : ℝ := (((D ^ D : ℕ) : ℝ))
  let X : ℝ := (((q + centeredPolynomialPatternRadius K p) ^ H : ℕ) : ℝ)
  have hcard : (atomPatternAssignments p).card ≤ D ^ D :=
    atomPatternAssignments_card_le_pow_count p hcount
  have hinner : ∀ m : ↥(polynomialPatternJetGroup n D K τ Q p),
      ‖∑ g ∈ atomPatternAssignments p,
          ∏ t : Fin (jetMonomialDegree n m.1),
            ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
              (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖ ≤ A * X := by
    intro m
    calc
      ‖∑ g ∈ atomPatternAssignments p,
          ∏ t : Fin (jetMonomialDegree n m.1),
            ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
              (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖
          ≤ ∑ g ∈ atomPatternAssignments p,
              ‖∏ t : Fin (jetMonomialDegree n m.1),
                ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
                  (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _g ∈ atomPatternAssignments p, X := by
        apply Finset.sum_le_sum
        intro g hg
        exact norm_windowShift_descFactorial_prod_le_centeredRadius
          m g hg hKq hq (horder m)
      _ = ((atomPatternAssignments p).card : ℝ) * X := by simp
      _ ≤ A * X := by
        apply mul_le_mul_of_nonneg_right _ (by dsimp [X]; positivity)
        dsimp [A]
        exact_mod_cast hcard
  have hcoeff :
      (∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
        ‖MvPolynomial.coeff m.1 Q‖) ≤ magnitudeCoefficientMass Q := by
    calc
      (∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
          ‖MvPolynomial.coeff m.1 Q‖) =
          ∑ m ∈ polynomialPatternJetGroup n D K τ Q p,
            ‖MvPolynomial.coeff m Q‖ :=
        by simpa using
          (Finset.sum_attach (polynomialPatternJetGroup n D K τ Q p)
            (fun m => ‖MvPolynomial.coeff m Q‖))
      _ ≤ ∑ m ∈ Q.support, ‖MvPolynomial.coeff m Q‖ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro m _hm _hnot
          positivity
      _ = magnitudeCoefficientMass Q := by rfl
  calc
    ‖∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
        MvPolynomial.coeff m.1 Q *
          ∑ g ∈ atomPatternAssignments p,
            ∏ t : Fin (jetMonomialDegree n m.1),
              ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
                (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖
        ≤ ∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
            ‖MvPolynomial.coeff m.1 Q *
              ∑ g ∈ atomPatternAssignments p,
                ∏ t : Fin (jetMonomialDegree n m.1),
                  ((windowShift q K
                    (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
                    (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
          ‖MvPolynomial.coeff m.1 Q‖ * (A * X) := by
      apply Finset.sum_le_sum
      intro m _hm
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hinner m) (norm_nonneg _)
    _ = (∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
          ‖MvPolynomial.coeff m.1 Q‖) * (A * X) := by
      rw [Finset.sum_mul]
    _ ≤ magnitudeCoefficientMass Q * (A * X) :=
      mul_le_mul_of_nonneg_right hcoeff (by dsimp [A, X]; positivity)
    _ = magnitudeCoefficientMass Q * (((D ^ D : ℕ) : ℝ)) *
          (((q + centeredPolynomialPatternRadius K p) ^ H : ℕ) : ℝ) := by
      dsimp [A, X]
      ring

/-- The maximal jet order is a valid common coefficient-level degree bound for every grouped
pattern weight. -/
theorem norm_eval_polynomialPatternWeightPoly_le_maxJetOrder
    {n D K τ M q : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (p : Fin M → Fin (D + 1)) (hKq : K ≤ q) (hq : 1 ≤ q) :
    ‖(polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ)‖ ≤
      magnitudeCoefficientMass Q * (((M ^ D : ℕ) : ℝ)) *
        (((q + M) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ) := by
  apply norm_eval_polynomialPatternWeightPoly_le Q p hKq hq
  intro m
  exact jetOrder_le_magnitudeMaxJetOrder Q
    (Finset.mem_filter.mp m.2).1

/-- If `H` bounds the order of every monomial active in one source group, division by `q^H`
leaves a bound polynomial only in the window size. -/
theorem norm_eval_polynomialPatternWeightPoly_div_pow_le_of_order_le
    {n D K τ M q H : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (p : Fin M → Fin (D + 1)) (hKq : K ≤ q) (hq : 1 ≤ q)
    (horder : ∀ m : ↥(polynomialPatternJetGroup n D K τ Q p),
      jetMonomialOrder n m.1 ≤ H) :
    ‖(polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ) /
        (q : ℂ) ^ H‖ ≤
      magnitudeCoefficientMass Q * (((M + 1) ^ (D + H) : ℕ) : ℝ) := by
  let C : ℝ := magnitudeCoefficientMass Q * (((M ^ D : ℕ) : ℝ))
  let qH : ℝ := (((q ^ H : ℕ) : ℝ))
  let MH : ℝ := ((((M + 1) ^ H : ℕ) : ℝ))
  have hraw : ‖(polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ)‖ ≤
      C * (((q + M) ^ H : ℕ) : ℝ) := by
    simpa only [C, mul_assoc] using
      norm_eval_polynomialPatternWeightPoly_le Q p hKq hq horder
  have hbase : q + M ≤ q * (M + 1) := by
    nlinarith [Nat.zero_le M]
  have hpow : (q + M) ^ H ≤ q ^ H * (M + 1) ^ H := by
    calc
      (q + M) ^ H ≤ (q * (M + 1)) ^ H := Nat.pow_le_pow_left hbase _
      _ = q ^ H * (M + 1) ^ H := by rw [mul_pow]
  have hqHpos : 0 < qH := by
    dsimp [qH]
    positivity
  have hratio : ((((q + M) ^ H : ℕ) : ℝ)) / qH ≤ MH := by
    apply (div_le_iff₀ hqHpos).2
    dsimp [qH, MH]
    exact_mod_cast (by simpa [mul_comm] using hpow)
  have hC : 0 ≤ C := by
    dsimp [C, magnitudeCoefficientMass]
    positivity
  rw [norm_div, norm_pow, Complex.norm_natCast]
  rw [show (q : ℝ) ^ H = qH by
    dsimp [qH]
    push_cast
    rfl]
  change _ / qH ≤ _
  calc
    ‖(polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ)‖ / qH
        ≤ (C * (((q + M) ^ H : ℕ) : ℝ)) / qH :=
      div_le_div_of_nonneg_right hraw hqHpos.le
    _ = C * (((((q + M) ^ H : ℕ) : ℝ)) / qH) := by ring
    _ ≤ C * MH := mul_le_mul_of_nonneg_left hratio hC
    _ ≤ magnitudeCoefficientMass Q *
        (((M + 1) ^ (D + H) : ℕ) : ℝ) := by
      dsimp [C, MH]
      have hMD : M ^ D ≤ (M + 1) ^ D :=
        Nat.pow_le_pow_left (Nat.le_succ M) _
      have hmass : 0 ≤ magnitudeCoefficientMass Q := by
        dsimp [magnitudeCoefficientMass]
        positivity
      have hcast : ((M ^ D : ℕ) : ℝ) ≤ (((M + 1) ^ D : ℕ) : ℝ) := by
        exact_mod_cast hMD
      calc
        magnitudeCoefficientMass Q * ((M ^ D : ℕ) : ℝ) *
            (((M + 1) ^ H : ℕ) : ℝ)
            ≤ magnitudeCoefficientMass Q * (((M + 1) ^ D : ℕ) : ℝ) *
              (((M + 1) ^ H : ℕ) : ℝ) := by
          gcongr
        _ = magnitudeCoefficientMass Q *
            (((M + 1) ^ (D + H) : ℕ) : ℝ) := by
          push_cast
          rw [pow_add]
          ring

/-- After division by the common maximal-order power, every grouped weight is bounded by one
fixed polynomial in the window size.  This is the uniform estimate required before the Gaussian
lattice tail is summed. -/
theorem norm_eval_polynomialPatternWeightPoly_div_pow_le
    {n D K τ M q : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (p : Fin M → Fin (D + 1)) (hKq : K ≤ q) (hq : 1 ≤ q) :
    ‖(polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ) /
        (q : ℂ) ^ magnitudeMaxJetOrder n Q‖ ≤
      magnitudeCoefficientMass Q *
        (((M + 1) ^ (D + magnitudeMaxJetOrder n Q) : ℕ) : ℝ) := by
  apply norm_eval_polynomialPatternWeightPoly_div_pow_le_of_order_le Q p hKq hq
  intro m
  exact jetOrder_le_magnitudeMaxJetOrder Q
    (Finset.mem_filter.mp m.2).1

/-! ## Ambient Gaussian majorant -/

/-- The coordinatewise polynomial-Gaussian majorant supplied by
`summable_fintype_pi_polynomialGaussian`. -/
def gaussianCoordinateMajorant
    {ι : Type*} [Fintype ι] (J : ℕ) (B : ℝ) (z : ι → ℤ) : ℝ :=
  ∏ i, (1 + ((z i).natAbs : ℝ)) ^ J *
    Real.exp (-B * (z i : ℝ) ^ 2)

theorem gaussianCoordinateMajorant_nonneg
    {ι : Type*} [Fintype ι] (J : ℕ) (B : ℝ) (z : ι → ℤ) :
    0 ≤ gaussianCoordinateMajorant J B z := by
  unfold gaussianCoordinateMajorant
  positivity

/-- The maximum-coordinate polynomial weight is bounded by the product of the coordinatewise
weights.  Positivity of the dimension is essential only to choose a coordinate attaining the
finite maximum. -/
theorem one_add_latticeMax_pow_le_prod
    {ι : Type*} [Fintype ι] [Nonempty ι] (J : ℕ) (z : ι → ℤ) :
    (1 + (integerLatticeMaxNatAbs z : ℝ)) ^ J ≤
      ∏ i, (1 + ((z i).natAbs : ℝ)) ^ J := by
  classical
  obtain ⟨i, _hi, hiMax⟩ := Finset.exists_mem_eq_sup
    (s := (Finset.univ : Finset ι)) (f := fun i => (z i).natAbs)
    (Finset.univ_nonempty)
  have hfactor : (1 + (integerLatticeMaxNatAbs z : ℝ)) ^ J =
      (1 + ((z i).natAbs : ℝ)) ^ J := by
    simp only [integerLatticeMaxNatAbs]
    rw [hiMax]
  rw [hfactor]
  calc
    (1 + ((z i).natAbs : ℝ)) ^ J =
        ∏ j ∈ ({i} : Finset ι), (1 + ((z j).natAbs : ℝ)) ^ J := by simp
    _ ≤ ∏ j ∈ (Finset.univ : Finset ι),
        (1 + ((z j).natAbs : ℝ)) ^ J := by
      apply Finset.prod_le_prod_of_subset_of_one_le
      · exact Finset.singleton_subset_iff.mpr (Finset.mem_univ i)
      · intro j _hj
        positivity
      · intro j _hj _hne
        have hnat : (0 : ℝ) ≤ ((z j).natAbs : ℝ) := Nat.cast_nonneg _
        exact one_le_pow₀ (n := J) (by linarith)
    _ = ∏ j, (1 + ((z j).natAbs : ℝ)) ^ J := by rfl

/-- Exact product factorization of the coordinatewise Gaussian. -/
theorem prod_exp_neg_sq
    {ι : Type*} [Fintype ι] (B : ℝ) (z : ι → ℤ) :
    (∏ i, Real.exp (-B * (z i : ℝ) ^ 2)) =
      Real.exp (-B * gaussianOffsetEnergy z) := by
  rw [← Real.exp_sum]
  simp only [gaussianOffsetEnergy]
  congr 1
  rw [← Finset.mul_sum]

/-- A polynomial in the largest offset times the constrained Gaussian energy is bounded by a
constant multiple of the coordinatewise ambient Gaussian. -/
theorem maxPolynomial_gaussian_le_coordinateMajorant
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (J : ℕ) {B : ℝ} (_hB : 0 ≤ B) (Q₀ : ℝ) (z : ι → ℤ) :
    (1 + (integerLatticeMaxNatAbs z : ℝ)) ^ J *
        Real.exp (-B * (gaussianOffsetEnergy z - Q₀)) ≤
      Real.exp (B * Q₀) * gaussianCoordinateMajorant J B z := by
  have hpoly := one_add_latticeMax_pow_le_prod J z
  have hexp : Real.exp (-B * (gaussianOffsetEnergy z - Q₀)) =
      Real.exp (B * Q₀) *
        ∏ i, Real.exp (-B * (z i : ℝ) ^ 2) := by
    rw [prod_exp_neg_sq]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp, gaussianCoordinateMajorant, Finset.prod_mul_distrib]
  have hnonneg : 0 ≤ Real.exp (B * Q₀) *
      ∏ i, Real.exp (-B * (z i : ℝ) ^ 2) := by positivity
  nlinarith

/-- Coordinatewise polynomial-Gaussian weights are summable on every finite integer lattice. -/
theorem summable_gaussianCoordinateMajorant
    (ι : Type) [Fintype ι] (J : ℕ) {B : ℝ} (hB : 0 < B) :
    Summable (gaussianCoordinateMajorant (ι := ι) J B) := by
  change Summable (fun z : ι → ℤ =>
    ∏ i, (1 + ((z i).natAbs : ℝ)) ^ J *
      Real.exp (-B * (z i : ℝ) ^ 2))
  exact summable_fintype_pi_polynomialGaussian
    ι (fun _ => J) (fun _ => B) (fun _ => hB)

/-- The max-polynomial Gaussian itself is summable, by comparison with the ambient product. -/
theorem summable_maxPolynomial_gaussian
    (ι : Type) [Fintype ι] [Nonempty ι]
    (J : ℕ) {B : ℝ} (hB : 0 < B) (Q₀ : ℝ) :
    Summable (fun z : ι → ℤ =>
      (1 + (integerLatticeMaxNatAbs z : ℝ)) ^ J *
        Real.exp (-B * (gaussianOffsetEnergy z - Q₀))) := by
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((summable_gaussianCoordinateMajorant ι J hB).mul_left (Real.exp (B * Q₀)))
  exact maxPolynomial_gaussian_le_coordinateMajorant J hB.le Q₀ z

/-- The ambient product majorant outside growing integer boxes tends to zero. -/
theorem tendsto_gaussianCoordinateMajorant_tsum_outside_box_zero
    (ι : Type) [Fintype ι] (J : ℕ) (B : ℝ) :
    Tendsto (fun R =>
      ∑' z : {z : ι → ℤ // z ∉ integerLatticeBox ι R},
        gaussianCoordinateMajorant J B z.1)
      atTop (nhds 0) := by
  simpa [gaussianCoordinateMajorant] using
    (tendsto_polynomialGaussian_tsum_outside_box_zero
      ι (fun _ => J) (fun _ => B))

/-- The complete max-polynomial Gaussian face has vanishing mass outside growing finite boxes. -/
theorem tendsto_maxPolynomial_gaussian_tsum_outside_box_zero
    (ι : Type) [Fintype ι] [Nonempty ι]
    (J : ℕ) {B : ℝ} (hB : 0 < B) (Q₀ : ℝ) :
    Tendsto (fun R =>
      ∑' z : {z : ι → ℤ // z ∉ integerLatticeBox ι R},
        (1 + (integerLatticeMaxNatAbs z.1 : ℝ)) ^ J *
          Real.exp (-B * (gaussianOffsetEnergy z.1 - Q₀)))
      atTop (nhds 0) := by
  let f : (ι → ℤ) → ℝ := fun z =>
    (1 + (integerLatticeMaxNatAbs z : ℝ)) ^ J *
      Real.exp (-B * (gaussianOffsetEnergy z - Q₀))
  have hsum : Summable f := summable_maxPolynomial_gaussian ι J hB Q₀
  exact (tendsto_tsum_compl_atTop_zero f).comp (integerLatticeBox_tendsto_atTop ι)

/-! ## Approximate finite Fourier inversion -/

/-- Approximate torsion Fourier inversion: if a finite multiplicity face is uniformly bounded by
`epsilon` on the full `(D+1)`-torsion state space, then each individual Fourier coefficient has
norm at most `epsilon`.  This is the quantitative replacement for
`face_fin_weights_eq_zero` needed before sending a Gaussian window radius to infinity. -/
theorem norm_face_fin_weight_le_of_uniform_torsion_bound
    {M D : ℕ} (F : Finset (Fin M → Fin (D + 1)))
    (ell : (Fin M → Fin (D + 1)) → ℂ) {epsilon : ℝ} (_hepsilon : 0 ≤ epsilon)
    (hbound : ∀ s : Fin M → ℂ, (∀ r, s r ^ (D + 1) = 1) →
      ‖∑ p ∈ F, ell p * ∏ r, s r ^ (p r : ℕ)‖ ≤ epsilon) :
    ∀ p ∈ F, ‖ell p‖ ≤ epsilon := by
  classical
  intro p₀ hp₀
  let m := D + 1
  have hm0 : m ≠ 0 := by omega
  set zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / m) with hzetaDef
  have hzeta : IsPrimitiveRoot zeta m := Complex.isPrimitiveRoot_exp m hm0
  have hzeta0 : zeta ≠ 0 := hzeta.ne_zero hm0
  let states : Finset (Fin M → ℕ) :=
    Fintype.piFinset (fun _ : Fin M => Finset.range m)
  let faceValue : (Fin M → ℕ) → ℂ := fun x =>
    ∑ p ∈ F, ell p * ∏ i, zeta ^ ((p i : ℤ) * (x i : ℤ))
  have hstateBound : ∀ x ∈ states, ‖faceValue x‖ ≤ epsilon := by
    intro x hx
    have hxmem : ∀ i, x i ∈ Finset.range m := by
      simpa [states, Fintype.mem_piFinset] using hx
    let s : Fin M → ℂ := fun i => zeta ^ x i
    have hs : ∀ i, s i ^ (D + 1) = 1 := by
      intro i
      dsimp [s, m]
      rw [← pow_mul, mul_comm, pow_mul, hzeta.pow_eq_one, one_pow]
    have hb := hbound s hs
    have heq : faceValue x =
        ∑ p ∈ F, ell p * ∏ i, s i ^ (p i : ℕ) := by
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      dsimp [s]
      rw [← pow_mul, ← zpow_natCast zeta (x i * (p i : ℕ))]
      congr 1
      push_cast
      ring
    rwa [heq]
  have hoff : ∀ p ∈ F, p ≠ p₀ →
      ∏ i, (∑ j ∈ Finset.range m,
        (zeta ^ ((p i : ℤ) - (p₀ i : ℤ))) ^ j) = 0 := by
    intro p hp hne
    obtain ⟨i₀, hi₀⟩ : ∃ i, p i ≠ p₀ i := by
      by_contra hall
      push Not at hall
      exact hne (funext hall)
    refine Finset.prod_eq_zero (Finset.mem_univ i₀)
      (sum_pow_zpow_eq_zero hzeta ?_)
    intro hdvd
    have habs : |(p i₀ : ℤ) - (p₀ i₀ : ℤ)| < (m : ℤ) := by
      rw [abs_lt]
      change -((D : ℤ) + 1) < (p i₀ : ℤ) - (p₀ i₀ : ℤ) ∧
        (p i₀ : ℤ) - (p₀ i₀ : ℤ) < (D : ℤ) + 1
      constructor <;> omega
    have hz := Int.eq_zero_of_abs_lt_dvd hdvd habs
    apply hi₀
    apply Fin.ext
    exact_mod_cast sub_eq_zero.mp hz
  have hdiag :
      ∏ i : Fin M, (∑ j ∈ Finset.range m,
        (zeta ^ ((p₀ i : ℤ) - (p₀ i : ℤ))) ^ j) =
        (m : ℂ) ^ M := by
    simp [Finset.prod_const, m]
  have hfourier :
      ell p₀ * (m : ℂ) ^ M =
        ∑ x ∈ states,
          (∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) * faceValue x := by
    have hrw : ∀ p ∈ F,
        ell p * ∏ i, (∑ j ∈ Finset.range m,
            (zeta ^ ((p i : ℤ) - (p₀ i : ℤ))) ^ j) =
          ∑ x ∈ states,
            (∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) *
              (ell p * ∏ i, zeta ^ ((p i : ℤ) * (x i : ℤ))) := by
      intro p hp
      rw [Finset.prod_univ_sum, Finset.mul_sum]
      apply Finset.sum_congr
      · ext x
        simp only [states, Fintype.mem_piFinset]
      · intro x hx
        have hsplit : ∀ i : Fin M,
            (zeta ^ ((p i : ℤ) - (p₀ i : ℤ))) ^ x i =
              zeta ^ (-((p₀ i : ℤ) * (x i : ℤ))) *
                zeta ^ ((p i : ℤ) * (x i : ℤ)) := by
          intro i
          rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hzeta0]
          congr 1
          ring
        rw [Finset.prod_congr rfl (fun i _ => hsplit i),
          Finset.prod_mul_distrib]
        ring
    calc
      ell p₀ * (m : ℂ) ^ M =
          ∑ p ∈ F, ell p * ∏ i, (∑ j ∈ Finset.range m,
            (zeta ^ ((p i : ℤ) - (p₀ i : ℤ))) ^ j) := by
        rw [Finset.sum_eq_single p₀]
        · rw [hdiag]
        · intro p hp hne
          rw [hoff p hp hne, mul_zero]
        · exact fun h => (h hp₀).elim
      _ = ∑ p ∈ F, ∑ x ∈ states,
          (∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) *
            (ell p * ∏ i, zeta ^ ((p i : ℤ) * (x i : ℤ))) :=
        Finset.sum_congr rfl hrw
      _ = ∑ x ∈ states,
          (∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) * faceValue x := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mul_sum]
  have hcharNorm : ∀ x : Fin M → ℕ, ‖(∏ i : Fin M,
      zeta ^ (-((p₀ i : ℤ) * (x i : ℤ))))‖ = 1 := by
    intro x
    rw [norm_prod]
    have hzetaNorm : ‖zeta‖ = 1 := hzeta.norm'_eq_one hm0
    simp [norm_zpow, hzetaNorm]
  have hrhs :
      ‖∑ x ∈ states,
          (∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) * faceValue x‖ ≤
        (m : ℝ) ^ M * epsilon := by
    calc
      ‖∑ x ∈ states,
          (∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) * faceValue x‖ ≤
          ∑ x ∈ states,
            ‖(∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) * faceValue x‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _x ∈ states, epsilon := by
        apply Finset.sum_le_sum
        intro x hx
        rw [norm_mul, hcharNorm]
        simpa using hstateBound x hx
      _ = (m : ℝ) ^ M * epsilon := by
        rw [Finset.sum_const, nsmul_eq_mul]
        congr 1
        simp [states, m]
  have hmul : ‖ell p₀‖ * (m : ℝ) ^ M ≤ (m : ℝ) ^ M * epsilon := by
    calc
      ‖ell p₀‖ * (m : ℝ) ^ M = ‖ell p₀ * (m : ℂ) ^ M‖ := by simp
      _ = ‖∑ x ∈ states,
          (∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) * faceValue x‖ :=
        congrArg norm hfourier
      _ ≤ (m : ℝ) ^ M * epsilon := hrhs
  have hmpos : 0 < (m : ℝ) ^ M := by positivity
  nlinarith

/-- Torsion-language recurrence transfers an eventual uniform bound on a finite moving face to
the same bound on every limiting Fourier coefficient. -/
theorem norm_face_weight_le_of_torsionLanguageUniversal
    {M D : ℕ} (u : ℕ → ℂ) (hu : TorsionLanguageUniversal u)
    (F : Finset (Fin M → Fin (D + 1)))
    (w : ℕ → (Fin M → Fin (D + 1)) → ℂ)
    (ell : (Fin M → Fin (D + 1)) → ℂ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hw : ∀ p ∈ F, Tendsto (fun q => w q p) atTop (𝓝 (ell p)))
    (hface : ∀ᶠ q : ℕ in atTop,
      ‖∑ p ∈ F, w q p *
        ∏ r : Fin M, u (q + (r : ℕ)) ^ (p r : ℕ)‖ ≤ epsilon) :
    ∀ p ∈ F, ‖ell p‖ ≤ epsilon := by
  apply norm_face_fin_weight_le_of_uniform_torsion_bound F ell hepsilon
  intro s hs
  obtain ⟨q, _hqmono, hqtop, hqword⟩ :=
    hu.exists_strictMono_occurrences (show 0 < D + 1 by omega) s hs
  have hterm : ∀ p ∈ F,
      Tendsto (fun k =>
        w (q k) p * ∏ r : Fin M, u (q k + (r : ℕ)) ^ (p r : ℕ))
        atTop (𝓝 (ell p * ∏ r : Fin M, s r ^ (p r : ℕ))) := by
    intro p hp
    simpa only [hqword] using
      (((hw p hp).comp hqtop).mul tendsto_const_nhds)
  have hsum := tendsto_finsetSum F (fun p hp => hterm p hp)
  exact le_of_tendsto hsum.norm (hqtop.eventually hface)

/-- An exhaustion of finite torsion faces with errors tending to zero cannot retain one fixed
nonzero limiting coefficient.  The window size and the selected representative may vary with
the exhaustion parameter. -/
theorem false_of_torsionLanguageUniversal_approximateFaces
    {D : ℕ} (u : ℕ → ℂ) (hu : TorsionLanguageUniversal u)
    (M : ℕ → ℕ)
    (F : ∀ R, Finset (Fin (M R) → Fin (D + 1)))
    (w : ∀ R, ℕ → (Fin (M R) → Fin (D + 1)) → ℂ)
    (ell : ∀ R, (Fin (M R) → Fin (D + 1)) → ℂ)
    (p₀ : ∀ R, Fin (M R) → Fin (D + 1))
    (epsilon : ℕ → ℝ)
    (hepsilon : ∀ R, 0 ≤ epsilon R)
    (hepsilonZero : Tendsto epsilon atTop (𝓝 0))
    (hp₀ : ∀ R, p₀ R ∈ F R)
    (hw : ∀ R, ∀ p ∈ F R,
      Tendsto (fun q => w R q p) atTop (𝓝 (ell R p)))
    (hface : ∀ R, ∀ᶠ q : ℕ in atTop,
      ‖∑ p ∈ F R, w R q p *
        ∏ r : Fin (M R), u (q + (r : ℕ)) ^ (p r : ℕ)‖ ≤ epsilon R)
    (ell₀ : ℂ) (hell₀ : ∀ R, ell R (p₀ R) = ell₀) (hell₀ne : ell₀ ≠ 0) :
    False := by
  have hbound : ∀ R, ‖ell₀‖ ≤ epsilon R := by
    intro R
    rw [← hell₀ R]
    exact norm_face_weight_le_of_torsionLanguageUniversal
      u hu (F R) (w R) (ell R) (hepsilon R) (hw R) (hface R) (p₀ R) (hp₀ R)
  have hzero : ‖ell₀‖ ≤ 0 :=
    ge_of_tendsto hepsilonZero (Eventually.of_forall hbound)
  exact hell₀ne (norm_eq_zero.mp (le_antisymm hzero (norm_nonneg ell₀)))

/-- **Gaussian tail-lock compiler.**  If every finite-window face has a common nonzero limiting
coefficient and its exterior error is bounded by one fixed polynomially weighted lattice
Gaussian tail, torsion-language universality is impossible. -/
theorem false_of_torsionLanguageUniversal_gaussianTailLock
    (ι : Type) [Fintype ι] [Nonempty ι]
    {D J : ℕ} {B : ℝ} (hB : 0 < B) (Q₀ C : ℝ) (hC : 0 ≤ C)
    (u : ℕ → ℂ) (hu : TorsionLanguageUniversal u)
    (M : ℕ → ℕ)
    (F : ∀ R, Finset (Fin (M R) → Fin (D + 1)))
    (w : ∀ R, ℕ → (Fin (M R) → Fin (D + 1)) → ℂ)
    (ell : ∀ R, (Fin (M R) → Fin (D + 1)) → ℂ)
    (p₀ : ∀ R, Fin (M R) → Fin (D + 1))
    (hp₀ : ∀ R, p₀ R ∈ F R)
    (hw : ∀ R, ∀ p ∈ F R,
      Tendsto (fun q => w R q p) atTop (𝓝 (ell R p)))
    (hface : ∀ R, ∀ᶠ q : ℕ in atTop,
      ‖∑ p ∈ F R, w R q p *
        ∏ r : Fin (M R), u (q + (r : ℕ)) ^ (p r : ℕ)‖ ≤
        C * ∑' z : {z : ι → ℤ // z ∉ integerLatticeBox ι R},
          (1 + (integerLatticeMaxNatAbs z.1 : ℝ)) ^ J *
            Real.exp (-B * (gaussianOffsetEnergy z.1 - Q₀)))
    (ell₀ : ℂ) (hell₀ : ∀ R, ell R (p₀ R) = ell₀) (hell₀ne : ell₀ ≠ 0) :
    False := by
  let epsilon : ℕ → ℝ := fun R =>
    C * ∑' z : {z : ι → ℤ // z ∉ integerLatticeBox ι R},
      (1 + (integerLatticeMaxNatAbs z.1 : ℝ)) ^ J *
        Real.exp (-B * (gaussianOffsetEnergy z.1 - Q₀))
  have hepsilon : ∀ R, 0 ≤ epsilon R := by
    intro R
    exact mul_nonneg hC (tsum_nonneg fun _ => by positivity)
  have hepsilonZero : Tendsto epsilon atTop (𝓝 0) := by
    simpa only [epsilon, mul_zero] using
      (tendsto_maxPolynomial_gaussian_tsum_outside_box_zero
        ι J hB Q₀).const_mul C
  exact false_of_torsionLanguageUniversal_approximateFaces
    u hu M F w ell p₀ epsilon hepsilon hepsilonZero hp₀ hw hface
      ell₀ hell₀ hell₀ne

/-! ## Entire Gaussian phase series -/

/-- Full-support Gaussian coefficients with an arbitrary complex phase. -/
def gaussianPhaseCoeff (B : ℝ) (u : ℕ → ℂ) (n : ℕ) : ℂ :=
  (Real.exp (-(B * (n : ℝ) ^ 2)) : ℂ) * u n

theorem norm_gaussianPhaseCoeff
    (B : ℝ) {u : ℕ → ℂ} (hu : ∀ n, ‖u n‖ = 1) (n : ℕ) :
    ‖gaussianPhaseCoeff B u n‖ = Real.exp (-(B * (n : ℝ) ^ 2)) := by
  rw [gaussianPhaseCoeff, norm_mul, hu, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem gaussianPhaseCoeff_ne_zero
    (B : ℝ) {u : ℕ → ℂ} (hu : ∀ n, ‖u n‖ = 1) (n : ℕ) :
    gaussianPhaseCoeff B u n ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_gaussianPhaseCoeff B hu]
  exact (Real.exp_pos _).ne'

/-- Every unit-phase Gaussian coefficient series has infinite radius of convergence. -/
theorem gaussianPhaseSeries_radius_eq_top
    {B : ℝ} (hB : 0 < B) {u : ℕ → ℂ} (hu : ∀ n, ‖u n‖ = 1) :
    (FormalMultilinearSeries.ofScalars ℂ (gaussianPhaseCoeff B u)).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  let A : ℝ := Real.log ((r : ℝ) + 1) + 1
  have hA : 0 < A := by
    have hr : (1 : ℝ) ≤ (r : ℝ) + 1 := by
      have := NNReal.coe_nonneg r
      linarith
    have hlog : 0 ≤ Real.log ((r : ℝ) + 1) := Real.log_nonneg hr
    dsimp [A]
    linarith
  have hlarge : ∀ᶠ n : ℕ in atTop, A / B ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (A / B)
  apply Real.summable_exp_neg_nat.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hlarge] with n hn
  rw [FormalMultilinearSeries.ofScalars_norm]
  rw [norm_gaussianPhaseCoeff B hu]
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (by positivity))]
  have hr0 : 0 ≤ (r : ℝ) := NNReal.coe_nonneg r
  have hrplus : 0 < (r : ℝ) + 1 := by positivity
  have hrpow : (r : ℝ) ^ n ≤
      Real.exp ((n : ℝ) * Real.log ((r : ℝ) + 1)) := by
    calc
      (r : ℝ) ^ n ≤ ((r : ℝ) + 1) ^ n :=
        pow_le_pow_left₀ hr0 (by linarith) n
      _ = Real.exp (Real.log ((r : ℝ) + 1)) ^ n := by
        rw [Real.exp_log hrplus]
      _ = Real.exp ((n : ℝ) * Real.log ((r : ℝ) + 1)) := by
        rw [Real.exp_nat_mul]
  have hBn : A ≤ (n : ℝ) * B := (div_le_iff₀ hB).mp hn
  have hquadratic : (n : ℝ) * A ≤ B * (n : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hBn (Nat.cast_nonneg n)
    nlinarith
  calc
    Real.exp (-(B * (n : ℝ) ^ 2)) * (r : ℝ) ^ n
        ≤ Real.exp (-(B * (n : ℝ) ^ 2)) *
            Real.exp ((n : ℝ) * Real.log ((r : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hrpow (Real.exp_pos _).le
    _ = Real.exp (-(B * (n : ℝ) ^ 2) +
        (n : ℝ) * Real.log ((r : ℝ) + 1)) := by rw [Real.exp_add]
    _ ≤ Real.exp (-(n : ℝ)) := Real.exp_le_exp.mpr (by
      dsimp [A] at hquadratic
      linarith)

/-- The entire function determined by the Gaussian coefficient series. -/
def gaussianPhaseFunction (B : ℝ) (u : ℕ → ℂ) : ℂ → ℂ :=
  FormalMultilinearSeries.ofScalarsSum (gaussianPhaseCoeff B u)

theorem gaussianPhaseFunction_eq_tsum
    (B : ℝ) (u : ℕ → ℂ) (z : ℂ) :
    gaussianPhaseFunction B u z =
      ∑' n, gaussianPhaseCoeff B u n * z ^ n := by
  simpa [gaussianPhaseFunction, smul_eq_mul] using
    (FormalMultilinearSeries.ofScalars_sum_eq (gaussianPhaseCoeff B u) z)

/-- The Gaussian phase series is analytic on the whole complex plane. -/
theorem analyticOnNhd_gaussianPhaseFunction
    {B : ℝ} (hB : 0 < B) {u : ℕ → ℂ} (hu : ∀ n, ‖u n‖ = 1) :
    AnalyticOnNhd ℂ (gaussianPhaseFunction B u) Set.univ := by
  let p := FormalMultilinearSeries.ofScalars ℂ (gaussianPhaseCoeff B u)
  have hr : p.radius = ⊤ := gaussianPhaseSeries_radius_eq_top hB hu
  have hp : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall (by rw [hr]; simp)
  simpa [gaussianPhaseFunction, p, hr] using hp.analyticOnNhd

theorem contDiff_gaussianPhaseFunction
    {B : ℝ} (hB : 0 < B) {u : ℕ → ℂ} (hu : ∀ n, ‖u n‖ = 1) :
    ContDiff ℂ (⊤ : ℕ∞) (gaussianPhaseFunction B u) :=
  (analyticOnNhd_gaussianPhaseFunction hB hu).contDiff

/-- The Taylor coefficients of the constructed entire function are exactly the prescribed
Gaussian-phase coefficients. -/
theorem taylorPS_gaussianPhaseFunction
    {B : ℝ} (hB : 0 < B) {u : ℕ → ℂ} (hu : ∀ n, ‖u n‖ = 1) (n : ℕ) :
    PowerSeries.coeff n (taylorPS (gaussianPhaseFunction B u)) =
      gaussianPhaseCoeff B u n := by
  let p := FormalMultilinearSeries.ofScalars ℂ (gaussianPhaseCoeff B u)
  have hr : p.radius = ⊤ := gaussianPhaseSeries_radius_eq_top hB hu
  have hp : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall (by rw [hr]; simp)
  have hiter := hp.iteratedFDeriv_eq_sum_of_completeSpace
    (fun _ : Fin n => (1 : ℂ))
  have hiter' : iteratedDeriv n p.sum 0 =
      (n.factorial : ℂ) * gaussianPhaseCoeff B u n := by
    rw [iteratedDeriv_eq_iteratedFDeriv, hiter]
    simp [p, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  change PowerSeries.coeff n (taylorPS p.sum) = gaussianPhaseCoeff B u n
  rw [coeff_taylorPS, hiter']
  exact mul_div_cancel_left₀ (gaussianPhaseCoeff B u n)
    (by exact_mod_cast Nat.factorial_ne_zero n)

/-- The explicit unit-filled universal torsion phase therefore gives an entire Gaussian series
whose Taylor phase is torsion-language universal. -/
theorem exists_entire_gaussian_torsionLanguageUniversal
    (B : ℝ) (hB : 0 < B) :
    ∃ (f : ℂ → ℂ) (u : ℕ → ℂ),
      AnalyticOnNhd ℂ f Set.univ ∧
      (∀ n, PowerSeries.coeff n (taylorPS f) = gaussianPhaseCoeff B u n) ∧
      (∀ n, ‖u n‖ = 1) ∧ TorsionLanguageUniversal u := by
  refine ⟨gaussianPhaseFunction B universalUnitTorsionPhase,
    universalUnitTorsionPhase, ?_, ?_, universalUnitTorsionPhase_norm,
    universalUnitTorsionPhase_torsionLanguageUniversal⟩
  · exact analyticOnNhd_gaussianPhaseFunction hB universalUnitTorsionPhase_norm
  · intro n
    exact taylorPS_gaussianPhaseFunction hB universalUnitTorsionPhase_norm n

end

end GaloisForLFunctions
