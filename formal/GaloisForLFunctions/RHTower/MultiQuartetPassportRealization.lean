import GaloisForLFunctions.RHTower.MultiQuartetEnvelope
import GaloisForLFunctions.RHTower.GradedRealityQuartetRealization
import GaloisForLFunctions.RHTower.SimultaneousFiniteJetFlatness
import GaloisForLFunctions.HTGeometry.ResidueFilledFluxGerm

/-!
# Simultaneous multi-quartet finite-passport realization

For an arbitrary finite list of jet depths this file constructs one entire function

```text
F(w) = ∏_j cosh (w - A_j) cosh (w + A_j) · (1 + ∏_j Q_j(w)^{M_j}),
Q_j(w) = (w² - α_j²)(w² - conj(α_j)²),      α_j = A_j + iπ/2,
```

together with its functional-equation normalization `X(s) = F(-2πi(s-1/2))`.  For pairwise distinct
positive `A_j` the four points `±α_j`, `±conj α_j` are simple zeros of `F`, and under the
normalization they become the quartets `1/4 ± i a_j`, `3/4 ± i a_j` with `a_j = A_j/(2π)`.

`X` is real-even, has no real zero, exact entire order one and no nonzero period, and at every
selected quartet the two partner completed-flux germs agree through the independently prescribed
depth `M_j - 1` while being different germs.
-/

namespace RHTower

open Complex Filter Topology
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

noncomputable section

variable {r : ℕ}

/-! ## The quartet polynomial family -/

/-- The quartet node `α_a = a + iπ/2`. -/
def quartetNode (a : ℝ) : ℂ := (a : ℂ) + ((Real.pi : ℂ) / 2) * I

/-- Its square. -/
def quartetNodeSq (a : ℝ) : ℂ := (quartetNode a) ^ (2 : ℕ)

theorem quartetNodeSq_re (a : ℝ) : (quartetNodeSq a).re = a ^ (2 : ℕ) - Real.pi ^ (2 : ℕ) / 4 := by
  simp only [quartetNodeSq, quartetNode]
  simp [pow_two, Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im]
  ring

theorem quartetNodeSq_im (a : ℝ) : (quartetNodeSq a).im = a * Real.pi := by
  simp only [quartetNodeSq, quartetNode]
  simp [pow_two, Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im]
  ring

theorem quartetNode_ne_zero {a : ℝ} : quartetNode a ≠ 0 := by
  intro hc
  have him := congrArg Complex.im hc
  simp [quartetNode] at him

/-- The real even quartet polynomial with roots `±α_a`, `±conj α_a`. -/
def quartetFactor (a : ℝ) (w : ℂ) : ℂ :=
  (w ^ (2 : ℕ) - quartetNodeSq a) * (w ^ (2 : ℕ) - (starRingEnd ℂ) (quartetNodeSq a))

theorem quartetFactor_neg (a : ℝ) (w : ℂ) : quartetFactor a (-w) = quartetFactor a w := by
  simp only [quartetFactor]
  ring

theorem quartetFactor_conj (a : ℝ) (w : ℂ) :
    quartetFactor a ((starRingEnd ℂ) w) = (starRingEnd ℂ) (quartetFactor a w) := by
  simp only [quartetFactor, map_mul, map_sub, map_pow, Complex.conj_conj]
  ring

theorem quartetFactor_node (a : ℝ) : quartetFactor a (quartetNode a) = 0 := by
  simp only [quartetFactor, quartetNodeSq]
  ring

theorem quartetFactor_neg_node (a : ℝ) : quartetFactor a (-(quartetNode a)) = 0 := by
  rw [quartetFactor_neg, quartetFactor_node]

theorem quartetFactor_conj_node (a : ℝ) :
    quartetFactor a ((starRingEnd ℂ) (quartetNode a)) = 0 := by
  rw [quartetFactor_conj, quartetFactor_node, map_zero]

theorem quartetFactor_neg_conj_node (a : ℝ) :
    quartetFactor a (-((starRingEnd ℂ) (quartetNode a))) = 0 := by
  rw [quartetFactor_neg, quartetFactor_conj_node]

/-- On the imaginary axis every quartet polynomial is a nonnegative real square. -/
theorem quartetFactor_mul_I (a : ℝ) (y : ℝ) :
    quartetFactor a ((y : ℂ) * I)
      = ((Complex.normSq ((y : ℂ) ^ (2 : ℕ) + quartetNodeSq a) : ℝ) : ℂ) := by
  have hsq : ((y : ℂ) * I) ^ (2 : ℕ) = -((y : ℂ) ^ (2 : ℕ)) := by
    linear_combination ((y : ℂ) ^ (2 : ℕ)) * Complex.I_sq
  have hconj : (starRingEnd ℂ) ((y : ℂ) ^ (2 : ℕ) + quartetNodeSq a)
      = (y : ℂ) ^ (2 : ℕ) + (starRingEnd ℂ) (quartetNodeSq a) := by
    simp [map_add, map_pow, Complex.conj_ofReal]
  rw [quartetFactor, hsq,
    show (-((y : ℂ) ^ (2 : ℕ)) - quartetNodeSq a) * (-((y : ℂ) ^ (2 : ℕ))
        - (starRingEnd ℂ) (quartetNodeSq a))
      = ((y : ℂ) ^ (2 : ℕ) + quartetNodeSq a) * (starRingEnd ℂ) ((y : ℂ) ^ (2 : ℕ) + quartetNodeSq a) by
      rw [hconj]; ring,
    Complex.mul_conj]

theorem quartetFactor_mul_I_pos {a : ℝ} (ha : a ≠ 0) (y : ℝ) :
    0 < Complex.normSq ((y : ℂ) ^ (2 : ℕ) + quartetNodeSq a) := by
  refine Complex.normSq_pos.mpr ?_
  intro hc
  have him := congrArg Complex.im hc
  have hy : (((y : ℂ)) ^ (2 : ℕ)).im = 0 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_im]
  simp only [Complex.add_im, Complex.zero_im, quartetNodeSq_im, hy, zero_add] at him
  rcases mul_eq_zero.mp him with h | h
  · exact ha h
  · exact Real.pi_ne_zero h

/-- Distinct positive displacements give disjoint quartets. -/
theorem quartetFactor_ne_zero_of_ne {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    quartetFactor b (quartetNode a) ≠ 0 := by
  have hA : (quartetNode a) ^ (2 : ℕ) = quartetNodeSq a := rfl
  rw [quartetFactor, hA]
  refine mul_ne_zero ?_ ?_
  · intro hc
    have him := congrArg Complex.im (sub_eq_zero.mp hc)
    rw [quartetNodeSq_im, quartetNodeSq_im] at him
    exact hab (mul_right_cancel₀ Real.pi_ne_zero him)
  · intro hc
    have him := congrArg Complex.im (sub_eq_zero.mp hc)
    rw [quartetNodeSq_im, Complex.conj_im, quartetNodeSq_im] at him
    nlinarith [Real.pi_pos]

/-! ## Local envelope orders -/

theorem coshQuartetEnvelope_ne_zero_of_re {a : ℝ} {c : ℂ}
    (h1 : (c - (a : ℂ)).re ≠ 0) (h2 : (c + (a : ℂ)).re ≠ 0) :
    coshQuartetEnvelope a c ≠ 0 :=
  mul_ne_zero (cosh_ne_zero_of_re_ne_zero h1) (cosh_ne_zero_of_re_ne_zero h2)

theorem analyticOrderAt_coshQuartetEnvelope_eq_one {a : ℝ} {c : ℂ}
    (hsub : (c - (a : ℂ)).re ≠ 0)
    (hadd : Complex.cosh (c + (a : ℂ)) = 0)
    (hderiv : Complex.sinh (c + (a : ℂ)) ≠ 0) :
    analyticOrderAt (coshQuartetEnvelope a) c = 1 := by
  have hsplit : coshQuartetEnvelope a
      = (fun z : ℂ => Complex.cosh (z - (a : ℂ))) * (fun z : ℂ => Complex.cosh (z + (a : ℂ))) :=
    rfl
  have hone : analyticOrderAt (fun z : ℂ => Complex.cosh (z - (a : ℂ))) c = 0 :=
    (analyticAt_coshSub a c).analyticOrderAt_eq_zero.mpr (cosh_ne_zero_of_re_ne_zero hsub)
  have htwo : analyticOrderAt (fun z : ℂ => Complex.cosh (z + (a : ℂ))) c = 1 := by
    refine (analyticAt_coshAdd a c).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hadd ?_
    rw [deriv_coshAdd]
    exact hderiv
  rw [hsplit, analyticOrderAt_mul (analyticAt_coshSub a c) (analyticAt_coshAdd a c), hone, htwo,
    zero_add]

/-! ## The construction -/

/-- The simultaneous Hermite-flat product with independently prescribed depths. -/
def flatProduct (A : Fin r → ℝ) (M : Fin r → ℕ) (w : ℂ) : ℂ :=
  ∏ j, (quartetFactor (A j) w) ^ (M j)

/-- The simultaneous flat multiplier. -/
def multiFlatMultiplier (A : Fin r → ℝ) (M : Fin r → ℕ) (w : ℂ) : ℂ := 1 + flatProduct A M w

/-- The realizing entire function. -/
def multiQuartetFn (A : Fin r → ℝ) (M : Fin r → ℕ) (w : ℂ) : ℂ :=
  multiEnvelope A w * multiFlatMultiplier A M w

/-- Its functional-equation normalization. -/
def multiQuartetXi (A : Fin r → ℝ) (M : Fin r → ℕ) (s : ℂ) : ℂ :=
  multiQuartetFn A M (-(2 * (Real.pi : ℂ) * I) * (s - 1 / 2))

theorem flatProduct_neg (A : Fin r → ℝ) (M : Fin r → ℕ) (w : ℂ) :
    flatProduct A M (-w) = flatProduct A M w :=
  Finset.prod_congr rfl fun j _ => by rw [quartetFactor_neg]

theorem flatProduct_conj (A : Fin r → ℝ) (M : Fin r → ℕ) (w : ℂ) :
    flatProduct A M ((starRingEnd ℂ) w) = (starRingEnd ℂ) (flatProduct A M w) := by
  unfold flatProduct
  rw [map_prod]
  exact Finset.prod_congr rfl fun j _ => by rw [quartetFactor_conj, map_pow]

theorem multiFlatMultiplier_neg (A : Fin r → ℝ) (M : Fin r → ℕ) (w : ℂ) :
    multiFlatMultiplier A M (-w) = multiFlatMultiplier A M w := by
  rw [multiFlatMultiplier, multiFlatMultiplier, flatProduct_neg]

theorem multiFlatMultiplier_conj (A : Fin r → ℝ) (M : Fin r → ℕ) (w : ℂ) :
    multiFlatMultiplier A M ((starRingEnd ℂ) w)
      = (starRingEnd ℂ) (multiFlatMultiplier A M w) := by
  rw [multiFlatMultiplier, multiFlatMultiplier, flatProduct_conj, map_add, map_one]

theorem multiQuartetFn_neg (A : Fin r → ℝ) (M : Fin r → ℕ) (w : ℂ) :
    multiQuartetFn A M (-w) = multiQuartetFn A M w := by
  rw [multiQuartetFn, multiQuartetFn, multiEnvelope_neg, multiFlatMultiplier_neg]

theorem multiQuartetFn_conj (A : Fin r → ℝ) (M : Fin r → ℕ) (w : ℂ) :
    multiQuartetFn A M ((starRingEnd ℂ) w) = (starRingEnd ℂ) (multiQuartetFn A M w) := by
  rw [multiQuartetFn, multiQuartetFn, multiEnvelope_conj, multiFlatMultiplier_conj, map_mul]

/-- **Functional equation.** -/
theorem multiQuartetXi_functional_equation (A : Fin r → ℝ) (M : Fin r → ℕ) (s : ℂ) :
    multiQuartetXi A M (1 - s) = multiQuartetXi A M s := by
  rw [multiQuartetXi, multiQuartetXi,
    show -(2 * (Real.pi : ℂ) * I) * ((1 - s) - 1 / 2)
      = -(-(2 * (Real.pi : ℂ) * I) * (s - 1 / 2)) by ring,
    multiQuartetFn_neg]

/-- **Schwarz reality.** -/
theorem multiQuartetXi_conj (A : Fin r → ℝ) (M : Fin r → ℕ) (s : ℂ) :
    multiQuartetXi A M ((starRingEnd ℂ) s) = (starRingEnd ℂ) (multiQuartetXi A M s) := by
  have hw : -(2 * (Real.pi : ℂ) * I) * ((starRingEnd ℂ) s - 1 / 2)
      = -((starRingEnd ℂ) (-(2 * (Real.pi : ℂ) * I) * (s - 1 / 2))) := by
    simp only [map_neg, map_mul, map_sub, map_div₀, map_one, map_ofNat, Complex.conj_I,
      Complex.conj_ofReal]
    ring
  rw [multiQuartetXi, hw, multiQuartetFn_neg, multiQuartetFn_conj, multiQuartetXi]

/-! ## Coordinates of the partner centres -/

/-- The functional-equation partner centre of the `j`-th quartet. -/
def mqFeCentre (a : ℝ) : ℂ := -(quartetNode a)

/-- The Schwarz partner centre of the `j`-th quartet. -/
def mqSchwarzCentre (a : ℝ) : ℂ := -((starRingEnd ℂ) (quartetNode a))

theorem mqSchwarzCentre_eq (a : ℝ) :
    mqSchwarzCentre a = mqFeCentre a + (Real.pi : ℂ) * I := by
  simp only [mqSchwarzCentre, mqFeCentre, quartetNode, map_add, map_mul, map_div₀, map_ofNat,
    Complex.conj_I, Complex.conj_ofReal]
  ring

theorem mqFeCentre_add_self (a : ℝ) :
    mqFeCentre a + (a : ℂ) = -((Real.pi : ℂ) / 2) * I := by
  simp only [mqFeCentre, quartetNode]
  ring

theorem mqSchwarzCentre_add_self (a : ℝ) :
    mqSchwarzCentre a + (a : ℂ) = ((Real.pi : ℂ) / 2) * I := by
  simp only [mqSchwarzCentre, quartetNode, map_add, map_mul, map_div₀, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal]
  ring

theorem mqFeCentre_sub_re (a b : ℝ) : (mqFeCentre a - (b : ℂ)).re = -(a + b) := by
  simp only [mqFeCentre, quartetNode]
  simp [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.mul_re]
  ring

theorem mqFeCentre_add_re (a b : ℝ) : (mqFeCentre a + (b : ℂ)).re = b - a := by
  simp only [mqFeCentre, quartetNode]
  simp [Complex.add_re, Complex.neg_re, Complex.mul_re]
  ring

theorem mqSchwarzCentre_sub_re (a b : ℝ) : (mqSchwarzCentre a - (b : ℂ)).re = -(a + b) := by
  simp only [mqSchwarzCentre, quartetNode, map_add, map_mul, map_div₀, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal]
  simp [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.mul_re]
  ring

theorem mqSchwarzCentre_add_re (a b : ℝ) : (mqSchwarzCentre a + (b : ℂ)).re = b - a := by
  simp only [mqSchwarzCentre, quartetNode, map_add, map_mul, map_div₀, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal]
  simp [Complex.add_re, Complex.neg_re, Complex.mul_re]
  ring

/-! ## Simplicity of the quartet zeros -/

theorem multiEnvelope_split (A : Fin r → ℝ) (j : Fin r) :
    multiEnvelope A = (fun w => coshQuartetEnvelope (A j) w) *
      (fun w => ∏ k ∈ Finset.univ.erase j, coshQuartetEnvelope (A k) w) := by
  funext w
  simp only [Pi.mul_apply, multiEnvelope]
  exact (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)).symm

theorem analyticOrderAt_multiEnvelope_eq_one {A : Fin r → ℝ} {j : Fin r} {c : ℂ}
    (hj : analyticOrderAt (coshQuartetEnvelope (A j)) c = 1)
    (hk : ∀ k ∈ Finset.univ.erase j, coshQuartetEnvelope (A k) c ≠ 0) :
    analyticOrderAt (multiEnvelope A) c = 1 := by
  have hrest : AnalyticAt ℂ (fun w => ∏ k ∈ Finset.univ.erase j,
      coshQuartetEnvelope (A k) w) c :=
    Finset.analyticAt_fun_prod _ fun k _ => coshQuartetEnvelope_analyticAt (A k) c
  have hrestne : (∏ k ∈ Finset.univ.erase j, coshQuartetEnvelope (A k) c) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hk
  rw [multiEnvelope_split A j,
    analyticOrderAt_mul (coshQuartetEnvelope_analyticAt (A j) c) hrest, hj,
    hrest.analyticOrderAt_eq_zero.mpr hrestne, add_zero]

theorem analyticOrderAt_multiEnvelope_mqFeCentre {A : Fin r → ℝ} (hApos : ∀ j, 0 < A j)
    (hAinj : Function.Injective A) (j : Fin r) :
    analyticOrderAt (multiEnvelope A) (mqFeCentre (A j)) = 1 := by
  refine analyticOrderAt_multiEnvelope_eq_one (j := j) ?_ ?_
  · refine analyticOrderAt_coshQuartetEnvelope_eq_one ?_ ?_ ?_
    · rw [mqFeCentre_sub_re]
      have := hApos j
      intro hc
      linarith
    · rw [mqFeCentre_add_self]
      exact cosh_neg_pi_div_two_mul_I
    · rw [mqFeCentre_add_self, sinh_neg_pi_div_two_mul_I]
      simp [Complex.I_ne_zero]
  · intro k hk
    have hne : A k ≠ A j := fun hc => (Finset.mem_erase.mp hk).1 (hAinj hc)
    refine coshQuartetEnvelope_ne_zero_of_re ?_ ?_
    · rw [mqFeCentre_sub_re]
      have h1 := hApos j
      have h2 := hApos k
      intro hc
      linarith
    · rw [mqFeCentre_add_re]
      intro hc
      exact hne (by linarith)

theorem analyticOrderAt_multiEnvelope_mqSchwarzCentre {A : Fin r → ℝ} (hApos : ∀ j, 0 < A j)
    (hAinj : Function.Injective A) (j : Fin r) :
    analyticOrderAt (multiEnvelope A) (mqSchwarzCentre (A j)) = 1 := by
  refine analyticOrderAt_multiEnvelope_eq_one (j := j) ?_ ?_
  · refine analyticOrderAt_coshQuartetEnvelope_eq_one ?_ ?_ ?_
    · rw [mqSchwarzCentre_sub_re]
      have := hApos j
      intro hc
      linarith
    · rw [mqSchwarzCentre_add_self]
      exact cosh_pi_div_two_mul_I
    · rw [mqSchwarzCentre_add_self, sinh_pi_div_two_mul_I]
      exact Complex.I_ne_zero
  · intro k hk
    have hne : A k ≠ A j := fun hc => (Finset.mem_erase.mp hk).1 (hAinj hc)
    refine coshQuartetEnvelope_ne_zero_of_re ?_ ?_
    · rw [mqSchwarzCentre_sub_re]
      have h1 := hApos j
      have h2 := hApos k
      intro hc
      linarith
    · rw [mqSchwarzCentre_add_re]
      intro hc
      exact hne (by linarith)

/-! ## The multiplier is a unit at every quartet centre -/

theorem analyticAt_quartetFactor (a : ℝ) (w : ℂ) : AnalyticAt ℂ (quartetFactor a) w := by
  unfold quartetFactor
  fun_prop

theorem analyticAt_flatProduct (A : Fin r → ℝ) (M : Fin r → ℕ) (w : ℂ) :
    AnalyticAt ℂ (flatProduct A M) w := by
  unfold flatProduct
  exact Finset.analyticAt_fun_prod _ fun j _ => (analyticAt_quartetFactor (A j) w).pow _

theorem analyticAt_multiFlatMultiplier (A : Fin r → ℝ) (M : Fin r → ℕ) (w : ℂ) :
    AnalyticAt ℂ (multiFlatMultiplier A M) w :=
  analyticAt_const.add (analyticAt_flatProduct A M w)

theorem analyticAt_multiQuartetFn (A : Fin r → ℝ) (M : Fin r → ℕ) (w : ℂ) :
    AnalyticAt ℂ (multiQuartetFn A M) w :=
  (multiEnvelope_analyticAt A w).mul (analyticAt_multiFlatMultiplier A M w)

theorem flatProduct_eq_zero_of_root {A : Fin r → ℝ} {M : Fin r → ℕ} {j : Fin r}
    (hM : M j ≠ 0) {w : ℂ} (hw : quartetFactor (A j) w = 0) : flatProduct A M w = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
  rw [hw, zero_pow hM]

theorem multiFlatMultiplier_eq_one_of_root {A : Fin r → ℝ} {M : Fin r → ℕ} {j : Fin r}
    (hM : M j ≠ 0) {w : ℂ} (hw : quartetFactor (A j) w = 0) : multiFlatMultiplier A M w = 1 := by
  rw [multiFlatMultiplier, flatProduct_eq_zero_of_root hM hw, add_zero]

theorem analyticOrderAt_multiFlatMultiplier_of_root {A : Fin r → ℝ} {M : Fin r → ℕ} {j : Fin r}
    (hM : M j ≠ 0) {w : ℂ} (hw : quartetFactor (A j) w = 0) :
    analyticOrderAt (multiFlatMultiplier A M) w = 0 :=
  (analyticAt_multiFlatMultiplier A M w).analyticOrderAt_eq_zero.mpr (by
    rw [multiFlatMultiplier_eq_one_of_root hM hw]; exact one_ne_zero)

theorem multiQuartetFn_eq_mul (A : Fin r → ℝ) (M : Fin r → ℕ) :
    multiQuartetFn A M = multiEnvelope A * multiFlatMultiplier A M := rfl

theorem quartetFactor_mqFeCentre (a : ℝ) : quartetFactor a (mqFeCentre a) = 0 :=
  quartetFactor_neg_node a

theorem quartetFactor_mqSchwarzCentre (a : ℝ) : quartetFactor a (mqSchwarzCentre a) = 0 :=
  quartetFactor_neg_conj_node a

/-- **Every selected quartet point is a simple zero.** -/
theorem analyticOrderAt_multiQuartetFn_mqFeCentre {A : Fin r → ℝ} {M : Fin r → ℕ}
    (hApos : ∀ j, 0 < A j) (hAinj : Function.Injective A) {j : Fin r} (hM : M j ≠ 0) :
    analyticOrderAt (multiQuartetFn A M) (mqFeCentre (A j)) = 1 := by
  rw [multiQuartetFn_eq_mul,
    analyticOrderAt_mul (multiEnvelope_analyticAt A _) (analyticAt_multiFlatMultiplier A M _),
    analyticOrderAt_multiEnvelope_mqFeCentre hApos hAinj j,
    analyticOrderAt_multiFlatMultiplier_of_root hM (quartetFactor_mqFeCentre (A j)), add_zero]

theorem analyticOrderAt_multiQuartetFn_mqSchwarzCentre {A : Fin r → ℝ} {M : Fin r → ℕ}
    (hApos : ∀ j, 0 < A j) (hAinj : Function.Injective A) {j : Fin r} (hM : M j ≠ 0) :
    analyticOrderAt (multiQuartetFn A M) (mqSchwarzCentre (A j)) = 1 := by
  rw [multiQuartetFn_eq_mul,
    analyticOrderAt_mul (multiEnvelope_analyticAt A _) (analyticAt_multiFlatMultiplier A M _),
    analyticOrderAt_multiEnvelope_mqSchwarzCentre hApos hAinj j,
    analyticOrderAt_multiFlatMultiplier_of_root hM (quartetFactor_mqSchwarzCentre (A j)), add_zero]

/-! ## The zero-free real axis -/

theorem flatProduct_mul_I_nonneg (A : Fin r → ℝ) (M : Fin r → ℕ) (y : ℝ) :
    flatProduct A M ((y : ℂ) * I)
      = ((∏ j, (Complex.normSq ((y : ℂ) ^ (2 : ℕ) + quartetNodeSq (A j))) ^ (M j) : ℝ) : ℂ) := by
  unfold flatProduct
  rw [Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun j _ => by
    rw [quartetFactor_mul_I, ← Complex.ofReal_pow]

theorem multiFlatMultiplier_mul_I_ne_zero (A : Fin r → ℝ) (M : Fin r → ℕ) (y : ℝ) :
    multiFlatMultiplier A M ((y : ℂ) * I) ≠ 0 := by
  rw [multiFlatMultiplier, flatProduct_mul_I_nonneg]
  have hnn : (0 : ℝ) ≤ ∏ j, (Complex.normSq ((y : ℂ) ^ (2 : ℕ) + quartetNodeSq (A j))) ^ (M j) :=
    Finset.prod_nonneg fun j _ => pow_nonneg (Complex.normSq_nonneg _) _
  intro hc
  have hre : (1 : ℝ) + ∏ j, (Complex.normSq ((y : ℂ) ^ (2 : ℕ) + quartetNodeSq (A j))) ^ (M j) = 0 := by
    have := congrArg Complex.re hc
    simpa only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.zero_re] using this
  linarith

theorem multiQuartetFn_mul_I_ne_zero {A : Fin r → ℝ} (hA : ∀ j, A j ≠ 0) (M : Fin r → ℕ)
    (y : ℝ) : multiQuartetFn A M ((y : ℂ) * I) ≠ 0 := by
  refine mul_ne_zero ?_ (multiFlatMultiplier_mul_I_ne_zero A M y)
  intro hc
  obtain ⟨j, hj⟩ := multiEnvelope_eq_zero_iff.mp hc
  have hre := coshQuartetEnvelope_zero_re_sq hj
  have hzero : (((y : ℂ) * I).re) = 0 := by simp
  rw [hzero] at hre
  exact hA j (by nlinarith [hre])

/-- **The real axis carries no zero.** -/
theorem multiQuartetXi_ne_zero_of_real {A : Fin r → ℝ} (hA : ∀ j, A j ≠ 0) (M : Fin r → ℕ)
    (t : ℝ) : multiQuartetXi A M (t : ℂ) ≠ 0 := by
  have hcoord : -(2 * (Real.pi : ℂ) * I) * ((t : ℂ) - 1 / 2)
      = ((-(2 * Real.pi * (t - 1 / 2)) : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [multiQuartetXi, hcoord]
  exact multiQuartetFn_mul_I_ne_zero hA M _

/-! ## The multiplier as a polynomial -/

/-- The quartet factor as a genuine polynomial. -/
def quartetFactorPoly (a : ℝ) : Polynomial ℂ :=
  (Polynomial.X ^ (2 : ℕ) - Polynomial.C (quartetNodeSq a)) *
    (Polynomial.X ^ (2 : ℕ) - Polynomial.C ((starRingEnd ℂ) (quartetNodeSq a)))

theorem quartetFactorPoly_eval (a : ℝ) (w : ℂ) :
    (quartetFactorPoly a).eval w = quartetFactor a w := by
  simp [quartetFactorPoly, quartetFactor]

theorem quartetFactorPoly_monic (a : ℝ) : (quartetFactorPoly a).Monic :=
  (Polynomial.monic_X_pow_sub_C _ two_ne_zero).mul
    (Polynomial.monic_X_pow_sub_C _ two_ne_zero)

theorem quartetFactorPoly_natDegree (a : ℝ) : (quartetFactorPoly a).natDegree = 4 := by
  rw [quartetFactorPoly, Polynomial.Monic.natDegree_mul
    (Polynomial.monic_X_pow_sub_C _ two_ne_zero) (Polynomial.monic_X_pow_sub_C _ two_ne_zero),
    Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_X_pow_sub_C]

/-- The flat core as a polynomial. -/
def multiFlatCore (A : Fin r → ℝ) (M : Fin r → ℕ) : Polynomial ℂ :=
  ∏ j, (quartetFactorPoly (A j)) ^ (M j)

/-- The flat multiplier as a polynomial. -/
def multiFlatPoly (A : Fin r → ℝ) (M : Fin r → ℕ) : Polynomial ℂ := 1 + multiFlatCore A M

theorem multiFlatCore_monic (A : Fin r → ℝ) (M : Fin r → ℕ) : (multiFlatCore A M).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun j _ => (quartetFactorPoly_monic (A j)).pow _

theorem multiFlatCore_natDegree (A : Fin r → ℝ) (M : Fin r → ℕ) :
    (multiFlatCore A M).natDegree = ∑ j, M j * 4 := by
  rw [multiFlatCore, Polynomial.natDegree_prod _ _
    (fun j _ => ((quartetFactorPoly_monic (A j)).pow (M j)).ne_zero)]
  exact Finset.sum_congr rfl fun j _ => by
    rw [Polynomial.natDegree_pow, quartetFactorPoly_natDegree]

theorem multiFlatCore_eval (A : Fin r → ℝ) (M : Fin r → ℕ) (w : ℂ) :
    (multiFlatCore A M).eval w = flatProduct A M w := by
  rw [multiFlatCore, flatProduct, Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun j _ => by
    rw [Polynomial.eval_pow, quartetFactorPoly_eval]

theorem multiFlatPoly_eval (A : Fin r → ℝ) (M : Fin r → ℕ) (w : ℂ) :
    (multiFlatPoly A M).eval w = multiFlatMultiplier A M w := by
  rw [multiFlatPoly, Polynomial.eval_add, Polynomial.eval_one, multiFlatCore_eval,
    multiFlatMultiplier]

theorem multiFlatPoly_degree_pos {A : Fin r → ℝ} {M : Fin r → ℕ} (hM : 0 < ∑ j, M j) :
    0 < (multiFlatPoly A M).degree := by
  have hdeg : 0 < (multiFlatCore A M).natDegree := by
    rw [multiFlatCore_natDegree]
    have : ∑ j, M j * 4 = 4 * ∑ j, M j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    omega
  have hcoeff : (multiFlatPoly A M).coeff ((multiFlatCore A M).natDegree) = 1 := by
    rw [multiFlatPoly, Polynomial.coeff_add, Polynomial.coeff_one, if_neg (by omega), zero_add]
    exact (multiFlatCore_monic A M).coeff_natDegree
  have hle : (((multiFlatCore A M).natDegree : ℕ) : WithBot ℕ) ≤ (multiFlatPoly A M).degree :=
    Polynomial.le_degree_of_ne_zero (by rw [hcoeff]; exact one_ne_zero)
  refine lt_of_lt_of_le ?_ hle
  exact_mod_cast hdeg

theorem multiFlatPoly_ne_zero {A : Fin r → ℝ} {M : Fin r → ℕ} (hM : 0 < ∑ j, M j) :
    multiFlatPoly A M ≠ 0 := by
  intro h
  have hpos := multiFlatPoly_degree_pos (A := A) (M := M) hM
  rw [h, Polynomial.degree_zero] at hpos
  exact absurd hpos (by simp)

theorem multiQuartetFn_eq_envelope_mul_poly (A : Fin r → ℝ) (M : Fin r → ℕ) (w : ℂ) :
    multiQuartetFn A M w = multiEnvelope A w * (multiFlatPoly A M).eval w := by
  rw [multiFlatPoly_eval]
  rfl

/-- **No nonzero period.** -/
theorem multiQuartetFn_periodic_iff {A : Fin r → ℝ} {M : Fin r → ℕ} (hr : 0 < r)
    (hM : 0 < ∑ j, M j) (h : ℂ) :
    Function.Periodic (multiQuartetFn A M) h ↔ h = 0 := by
  have hfun : multiQuartetFn A M
      = fun w => multiEnvelope A w * (multiFlatPoly A M).eval w :=
    funext (multiQuartetFn_eq_envelope_mul_poly A M)
  rw [hfun]
  exact multiEnvelope_mul_polynomial_periodic_iff hr (multiFlatPoly A M)
    (multiFlatPoly_degree_pos hM) h

/-- **Exact order one.** -/
theorem multiQuartetFn_order_one_bounds {A : Fin r → ℝ} {M : Fin r → ℕ} (hM : 0 < ∑ j, M j) :
    ∃ Kupper Klower R : ℝ,
      0 < Kupper ∧ 0 < Klower ∧
      (∀ w : ℂ, ‖multiQuartetFn A M w‖ ≤
        Kupper * (1 + ‖w‖) ^ (multiFlatPoly A M).natDegree * Real.exp (2 * r * ‖w‖)) ∧
      ∀ x : ℝ, R ≤ x → Klower * Real.exp (2 * r * x) ≤ ‖multiQuartetFn A M (x : ℂ)‖ := by
  obtain ⟨Ku, Kl, R, hKu, hKl, hupper, hlower⟩ :=
    multiEnvelope_mul_polynomial_order_one_bounds A (multiFlatPoly_ne_zero (A := A) hM)
  refine ⟨Ku, Kl, R, hKu, hKl, fun w => ?_, fun x hx => ?_⟩
  · rw [multiQuartetFn_eq_envelope_mul_poly]
    exact hupper w
  · rw [multiQuartetFn_eq_envelope_mul_poly]
    exact hlower x hx

/-! ## The local Hermite-flat data at a quartet centre -/

/-- The shifted quartet factor: `quartetFactor a (c + x) = x · mqShift a c x` at a root `c`. -/
def mqShift (a : ℝ) (c x : ℂ) : ℂ :=
  4 * c ^ (3 : ℕ) + 6 * c ^ (2 : ℕ) * x + 4 * c * x ^ (2 : ℕ) + x ^ (3 : ℕ)
    - (quartetNodeSq a + (starRingEnd ℂ) (quartetNodeSq a)) * (2 * c + x)

theorem quartetFactor_add (a : ℝ) (c x : ℂ) :
    quartetFactor a (c + x) = x * mqShift a c x + quartetFactor a c := by
  simp only [quartetFactor, mqShift]
  ring

theorem quartetFactor_add_of_root {a : ℝ} {c : ℂ} (hc : quartetFactor a c = 0) (x : ℂ) :
    quartetFactor a (c + x) = x * mqShift a c x := by
  rw [quartetFactor_add, hc, add_zero]

theorem quartetNodeSq_sub_conj_ne_zero {a : ℝ} (ha : a ≠ 0) :
    quartetNodeSq a - (starRingEnd ℂ) (quartetNodeSq a) ≠ 0 := by
  intro hc
  have him := congrArg Complex.im (sub_eq_zero.mp hc)
  rw [quartetNodeSq_im, Complex.conj_im, quartetNodeSq_im] at him
  have hpi := Real.pi_pos
  rcases lt_trichotomy a 0 with h | h | h
  · nlinarith
  · exact ha h
  · nlinarith

theorem mqShift_mqFeCentre_zero (a : ℝ) :
    mqShift a (mqFeCentre a) 0
      = 2 * (mqFeCentre a) * (quartetNodeSq a - (starRingEnd ℂ) (quartetNodeSq a)) := by
  have hc2 : (mqFeCentre a) ^ (2 : ℕ) = quartetNodeSq a := by
    simp only [mqFeCentre, quartetNodeSq]
    ring
  simp only [mqShift]
  linear_combination (4 * (mqFeCentre a)) * hc2

theorem mqShift_mqSchwarzCentre_zero (a : ℝ) :
    mqShift a (mqSchwarzCentre a) 0
      = 2 * (mqSchwarzCentre a) * ((starRingEnd ℂ) (quartetNodeSq a) - quartetNodeSq a) := by
  have hc2 : (mqSchwarzCentre a) ^ (2 : ℕ) = (starRingEnd ℂ) (quartetNodeSq a) := by
    simp only [mqSchwarzCentre, quartetNodeSq, map_pow]
    ring
  simp only [mqShift]
  linear_combination (4 * (mqSchwarzCentre a)) * hc2

theorem mqFeCentre_ne_zero {a : ℝ} : mqFeCentre a ≠ 0 := by
  simpa [mqFeCentre] using quartetNode_ne_zero (a := a)

theorem mqSchwarzCentre_ne_zero {a : ℝ} : mqSchwarzCentre a ≠ 0 := by
  simp only [mqSchwarzCentre, ne_eq, neg_eq_zero]
  intro hc
  exact quartetNode_ne_zero (a := a) (by simpa using congrArg (starRingEnd ℂ) hc)

theorem mqShift_mqFeCentre_zero_ne {a : ℝ} (ha : a ≠ 0) : mqShift a (mqFeCentre a) 0 ≠ 0 := by
  rw [mqShift_mqFeCentre_zero]
  exact mul_ne_zero (mul_ne_zero two_ne_zero mqFeCentre_ne_zero)
    (quartetNodeSq_sub_conj_ne_zero ha)

theorem mqShift_mqSchwarzCentre_zero_ne {a : ℝ} (ha : a ≠ 0) :
    mqShift a (mqSchwarzCentre a) 0 ≠ 0 := by
  rw [mqShift_mqSchwarzCentre_zero]
  refine mul_ne_zero (mul_ne_zero two_ne_zero mqSchwarzCentre_ne_zero) ?_
  intro hc
  exact quartetNodeSq_sub_conj_ne_zero ha (by linear_combination -hc)

/-- The analytic unit of the Hermite-flat factorization at the `j`-th quartet centre. -/
def mqUnit (A : Fin r → ℝ) (M : Fin r → ℕ) (j : Fin r) (c : ℂ) (x : ℂ) : ℂ :=
  (mqShift (A j) c x) ^ (M j) *
    ∏ k ∈ Finset.univ.erase j, (quartetFactor (A k) (c + x)) ^ (M k)

theorem analyticAt_mqUnit (A : Fin r → ℝ) (M : Fin r → ℕ) (j : Fin r) (c : ℂ) :
    AnalyticAt ℂ (mqUnit A M j c) 0 := by
  refine AnalyticAt.mul ?_ ?_
  · refine AnalyticAt.pow ?_ _
    unfold mqShift
    fun_prop
  · refine Finset.analyticAt_fun_prod _ fun k _ => AnalyticAt.pow ?_ _
    exact (analyticAt_quartetFactor (A k) (c + 0)).comp_of_eq
      (analyticAt_const.add analyticAt_id) (by simp)

theorem hermiteFlatFactor_mqUnit {A : Fin r → ℝ} {M : Fin r → ℕ} {j : Fin r} {c : ℂ}
    (hc : quartetFactor (A j) c = 0) :
    hermiteFlatFactor (M j) (mqUnit A M j c) = fun x => multiFlatMultiplier A M (c + x) := by
  funext x
  rw [hermiteFlatFactor, mqUnit, multiFlatMultiplier, flatProduct]
  rw [← Finset.mul_prod_erase Finset.univ (fun k => (quartetFactor (A k) (c + x)) ^ (M k))
    (Finset.mem_univ j)]
  rw [quartetFactor_add_of_root hc, mul_pow]
  ring

theorem mqUnit_zero_mqFeCentre {A : Fin r → ℝ} {M : Fin r → ℕ} (hApos : ∀ j, 0 < A j)
    (hAinj : Function.Injective A) (j : Fin r) :
    mqUnit A M j (mqFeCentre (A j)) 0 ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero _ (mqShift_mqFeCentre_zero_ne (hApos j).ne')) ?_
  refine Finset.prod_ne_zero_iff.mpr fun k hk => pow_ne_zero _ ?_
  have hne : A k ≠ A j := fun hcc => (Finset.mem_erase.mp hk).1 (hAinj hcc)
  rw [add_zero, mqFeCentre, quartetFactor_neg]
  exact quartetFactor_ne_zero_of_ne (hApos j) (hApos k) (Ne.symm hne)

theorem mqUnit_zero_mqSchwarzCentre {A : Fin r → ℝ} {M : Fin r → ℕ} (hApos : ∀ j, 0 < A j)
    (hAinj : Function.Injective A) (j : Fin r) :
    mqUnit A M j (mqSchwarzCentre (A j)) 0 ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero _ (mqShift_mqSchwarzCentre_zero_ne (hApos j).ne')) ?_
  refine Finset.prod_ne_zero_iff.mpr fun k hk => pow_ne_zero _ ?_
  have hne : A k ≠ A j := fun hcc => (Finset.mem_erase.mp hk).1 (hAinj hcc)
  rw [add_zero, mqSchwarzCentre, quartetFactor_neg, quartetFactor_conj]
  simpa using quartetFactor_ne_zero_of_ne (hApos j) (hApos k) (Ne.symm hne)

/-! ## The completed-flux germs at the partner centres -/

/-- The multiplier's flux correction at the `j`-th centre. -/
def mqFlux (A : Fin r → ℝ) (M : Fin r → ℕ) (j : Fin r) (c : ℂ) : ℂ → ℂ :=
  hermiteFlatFluxCorrection (M j) (mqUnit A M j c)

theorem deriv_multiFlatMultiplier_shift (A : Fin r → ℝ) (M : Fin r → ℕ) (c x : ℂ) :
    deriv (fun y : ℂ => multiFlatMultiplier A M (c + y)) x
      = deriv (multiFlatMultiplier A M) (c + x) := by
  have hbase : HasDerivAt (multiFlatMultiplier A M)
      (deriv (multiFlatMultiplier A M) (c + x)) (c + x) :=
    (analyticAt_multiFlatMultiplier A M (c + x)).differentiableAt.hasDerivAt
  have h := hbase.comp x ((hasDerivAt_id x).const_add c)
  simpa [Function.comp_def] using h.deriv

theorem fluxGerm_multiFlatMultiplier_eq {A : Fin r → ℝ} {M : Fin r → ℕ} {j : Fin r} {c : ℂ}
    (hMj : M j ≠ 0) (hc : quartetFactor (A j) c = 0) :
    fluxGerm (multiFlatMultiplier A M) c
      = fun x => -x * deriv (multiFlatMultiplier A M) (c + x)
        / multiFlatMultiplier A M (c + x) := by
  funext x
  by_cases hx : x = 0
  · subst x
    rw [fluxGerm_zero, analyticOrderAt_multiFlatMultiplier_of_root hMj hc]
    simp
  · exact fluxGerm_of_ne_zero _ _ hx

theorem mqFlux_eventuallyEq {A : Fin r → ℝ} {M : Fin r → ℕ} {j : Fin r} {c : ℂ}
    (hMj : 0 < M j) (hc : quartetFactor (A j) c = 0) :
    mqFlux A M j c =ᶠ[𝓝 0] fluxGerm (multiFlatMultiplier A M) c := by
  have h := hermiteFlatFluxCorrection_eventuallyEq_neg_mul_logDeriv (M := M j) hMj
    (analyticAt_mqUnit A M j c)
  rw [fluxGerm_multiFlatMultiplier_eq hMj.ne' hc]
  refine h.trans (Filter.Eventually.of_forall fun x => ?_)
  rw [hermiteFlatFactor_mqUnit hc]
  show -x * deriv (fun y : ℂ => multiFlatMultiplier A M (c + y)) x
      / multiFlatMultiplier A M (c + x)
    = -x * deriv (multiFlatMultiplier A M) (c + x) / multiFlatMultiplier A M (c + x)
  rw [deriv_multiFlatMultiplier_shift]

theorem deriv_multiEnvelope_add_pi_mul_I (A : Fin r → ℝ) (w : ℂ) :
    deriv (multiEnvelope A) (w + (Real.pi : ℂ) * I) = deriv (multiEnvelope A) w := by
  have hfun : (fun z : ℂ => multiEnvelope A (z + (Real.pi : ℂ) * I)) = multiEnvelope A :=
    funext (multiEnvelope_add_pi_mul_I A)
  have hbase : HasDerivAt (multiEnvelope A) (deriv (multiEnvelope A) (w + (Real.pi : ℂ) * I))
      (w + (Real.pi : ℂ) * I) :=
    (multiEnvelope_analyticAt A _).differentiableAt.hasDerivAt
  have hd : HasDerivAt (fun z : ℂ => multiEnvelope A (z + (Real.pi : ℂ) * I))
      (deriv (multiEnvelope A) (w + (Real.pi : ℂ) * I)) w := by
    simpa [Function.comp_def] using
      hbase.comp w ((hasDerivAt_id w).add_const ((Real.pi : ℂ) * I))
  rw [hfun] at hd
  exact hd.deriv.symm

theorem fluxGerm_multiEnvelope_partners_eq {A : Fin r → ℝ} (hApos : ∀ j, 0 < A j)
    (hAinj : Function.Injective A) (j : Fin r) :
    fluxGerm (multiEnvelope A) (mqSchwarzCentre (A j))
      = fluxGerm (multiEnvelope A) (mqFeCentre (A j)) := by
  funext x
  by_cases hx : x = 0
  · subst x
    rw [fluxGerm_zero, fluxGerm_zero,
      analyticOrderAt_multiEnvelope_mqSchwarzCentre hApos hAinj j,
      analyticOrderAt_multiEnvelope_mqFeCentre hApos hAinj j]
  · rw [fluxGerm_of_ne_zero _ _ hx, fluxGerm_of_ne_zero _ _ hx, mqSchwarzCentre_eq,
      show mqFeCentre (A j) + (Real.pi : ℂ) * I + x
        = (mqFeCentre (A j) + x) + (Real.pi : ℂ) * I by ring,
      multiEnvelope_add_pi_mul_I, deriv_multiEnvelope_add_pi_mul_I]

/-- The residue-filled germ at the functional-equation partner centre of the `j`-th quartet. -/
def mqFeGerm (A : Fin r → ℝ) (M : Fin r → ℕ) (j : Fin r) : ℂ → ℂ :=
  fluxGerm (multiQuartetFn A M) (mqFeCentre (A j))

/-- The residue-filled germ at the Schwarz partner centre of the `j`-th quartet. -/
def mqSchwarzGerm (A : Fin r → ℝ) (M : Fin r → ℕ) (j : Fin r) : ℂ → ℂ :=
  fluxGerm (multiQuartetFn A M) (mqSchwarzCentre (A j))

theorem analyticAt_mqFeGerm {A : Fin r → ℝ} {M : Fin r → ℕ} (hApos : ∀ j, 0 < A j)
    (hAinj : Function.Injective A) {j : Fin r} (hMj : M j ≠ 0) :
    AnalyticAt ℂ (mqFeGerm A M j) 0 :=
  fluxGerm_analyticAt_zero (m := 1) (analyticAt_multiQuartetFn A M _)
    (by simpa using analyticOrderAt_multiQuartetFn_mqFeCentre hApos hAinj hMj)

theorem analyticAt_mqSchwarzGerm {A : Fin r → ℝ} {M : Fin r → ℕ} (hApos : ∀ j, 0 < A j)
    (hAinj : Function.Injective A) {j : Fin r} (hMj : M j ≠ 0) :
    AnalyticAt ℂ (mqSchwarzGerm A M j) 0 :=
  fluxGerm_analyticAt_zero (m := 1) (analyticAt_multiQuartetFn A M _)
    (by simpa using analyticOrderAt_multiQuartetFn_mqSchwarzCentre hApos hAinj hMj)

theorem mqGermDiff_eventuallyEq {A : Fin r → ℝ} {M : Fin r → ℕ} (hApos : ∀ j, 0 < A j)
    (hAinj : Function.Injective A) {j : Fin r} (hMj : 0 < M j) :
    mqFeGerm A M j - mqSchwarzGerm A M j =ᶠ[𝓝 0]
      mqFlux A M j (mqFeCentre (A j)) - mqFlux A M j (mqSchwarzCentre (A j)) := by
  have hEc : analyticOrderAt (multiEnvelope A) (mqFeCentre (A j)) = ((1 : ℕ) : ℕ∞) := by
    simpa using analyticOrderAt_multiEnvelope_mqFeCentre hApos hAinj j
  have hEd : analyticOrderAt (multiEnvelope A) (mqSchwarzCentre (A j)) = ((1 : ℕ) : ℕ∞) := by
    simpa using analyticOrderAt_multiEnvelope_mqSchwarzCentre hApos hAinj j
  have hPc : analyticOrderAt (multiFlatMultiplier A M) (mqFeCentre (A j)) = ((0 : ℕ) : ℕ∞) := by
    simpa using analyticOrderAt_multiFlatMultiplier_of_root (M := M) hMj.ne'
      (quartetFactor_mqFeCentre (A j))
  have hPd : analyticOrderAt (multiFlatMultiplier A M) (mqSchwarzCentre (A j))
      = ((0 : ℕ) : ℕ∞) := by
    simpa using analyticOrderAt_multiFlatMultiplier_of_root (M := M) hMj.ne'
      (quartetFactor_mqSchwarzCentre (A j))
  have hc : fluxGerm (multiQuartetFn A M) (mqFeCentre (A j)) =ᶠ[𝓝 0]
      fluxGerm (multiEnvelope A) (mqFeCentre (A j))
        + fluxGerm (multiFlatMultiplier A M) (mqFeCentre (A j)) := by
    rw [multiQuartetFn_eq_mul]
    exact fluxGerm_mul (multiEnvelope_analyticAt A _) (analyticAt_multiFlatMultiplier A M _)
      hEc hPc
  have hd : fluxGerm (multiQuartetFn A M) (mqSchwarzCentre (A j)) =ᶠ[𝓝 0]
      fluxGerm (multiEnvelope A) (mqSchwarzCentre (A j))
        + fluxGerm (multiFlatMultiplier A M) (mqSchwarzCentre (A j)) := by
    rw [multiQuartetFn_eq_mul]
    exact fluxGerm_mul (multiEnvelope_analyticAt A _) (analyticAt_multiFlatMultiplier A M _)
      hEd hPd
  have hmc := mqFlux_eventuallyEq (A := A) (M := M) (j := j) hMj (quartetFactor_mqFeCentre (A j))
  have hmd := mqFlux_eventuallyEq (A := A) (M := M) (j := j) hMj
    (quartetFactor_mqSchwarzCentre (A j))
  have hbase := congrFun (fluxGerm_multiEnvelope_partners_eq hApos hAinj j)
  filter_upwards [hc, hd, hmc, hmd] with x hcx hdx hmcx hmdx
  simp only [Pi.sub_apply, Pi.add_apply] at hcx hdx ⊢
  rw [mqFeGerm, mqSchwarzGerm, hcx, hdx, hmcx, hmdx, hbase x]
  ring

/-- **The two partner germs agree through the prescribed depth.** -/
theorem mqFeGerm_iteratedDeriv_eq_of_lt {A : Fin r → ℝ} {M : Fin r → ℕ} (hApos : ∀ j, 0 < A j)
    (hAinj : Function.Injective A) {j : Fin r} (hMj : 0 < M j) {n : ℕ} (hn : n < M j) :
    iteratedDeriv n (mqFeGerm A M j) 0 = iteratedDeriv n (mqSchwarzGerm A M j) 0 := by
  have hzc : iteratedDeriv n (mqFlux A M j (mqFeCentre (A j))) 0 = 0 :=
    hermiteFlatFluxCorrection_iteratedDeriv_zero hMj (analyticAt_mqUnit A M j _)
      (mqUnit_zero_mqFeCentre hApos hAinj j) hn
  have hzd : iteratedDeriv n (mqFlux A M j (mqSchwarzCentre (A j))) 0 = 0 :=
    hermiteFlatFluxCorrection_iteratedDeriv_zero hMj (analyticAt_mqUnit A M j _)
      (mqUnit_zero_mqSchwarzCentre hApos hAinj j) hn
  have hsplitL : iteratedDeriv n (mqFeGerm A M j - mqSchwarzGerm A M j) 0
      = iteratedDeriv n (mqFeGerm A M j) 0 - iteratedDeriv n (mqSchwarzGerm A M j) 0 :=
    iteratedDeriv_sub (analyticAt_mqFeGerm hApos hAinj hMj.ne').contDiffAt
      (analyticAt_mqSchwarzGerm hApos hAinj hMj.ne').contDiffAt
  have hsplitR : iteratedDeriv n (mqFlux A M j (mqFeCentre (A j))
        - mqFlux A M j (mqSchwarzCentre (A j))) 0
      = iteratedDeriv n (mqFlux A M j (mqFeCentre (A j))) 0
        - iteratedDeriv n (mqFlux A M j (mqSchwarzCentre (A j))) 0 :=
    iteratedDeriv_sub
      (hermiteFlatFluxCorrection_analyticAt_zero hMj (analyticAt_mqUnit A M j _)).contDiffAt
      (hermiteFlatFluxCorrection_analyticAt_zero hMj (analyticAt_mqUnit A M j _)).contDiffAt
  have htrans := (mqGermDiff_eventuallyEq hApos hAinj hMj).iteratedDeriv_eq n
  rw [hsplitL, hsplitR, hzc, hzd, sub_zero] at htrans
  exact sub_eq_zero.mp htrans

/-! ## The two partner germs are different germs -/

theorem leadingCoeff_derivative_eq {p : Polynomial ℂ} (hp : p.natDegree ≠ 0) :
    (Polynomial.derivative p).leadingCoeff = p.leadingCoeff * (p.natDegree : ℂ) := by
  have hone : 1 ≤ p.natDegree := Nat.one_le_iff_ne_zero.mpr hp
  rw [Polynomial.leadingCoeff, Polynomial.natDegree_derivative, Polynomial.coeff_derivative,
    Polynomial.leadingCoeff]
  congr 1
  · congr 1
    omega
  · rw [Nat.cast_sub hone]
    push_cast
    ring

/-- **A shift Wronskian identity forces the shift to vanish.**  If `P'(z)P(z+h) = P'(z+h)P(z)`
identically for a nonconstant polynomial, then `h = 0`. -/
theorem polynomial_wronskian_shift_eq_zero {P : Polynomial ℂ} (hdeg : 0 < P.degree) {h : ℂ}
    (hw : Polynomial.derivative P * (P.comp (Polynomial.X + Polynomial.C h))
        = Polynomial.derivative (P.comp (Polynomial.X + Polynomial.C h)) * P) : h = 0 := by
  have hQm : (Polynomial.X + Polynomial.C h : Polynomial ℂ).Monic := Polynomial.monic_X_add_C h
  have hQnd : (Polynomial.X + Polynomial.C h : Polynomial ℂ).natDegree = 1 :=
    Polynomial.natDegree_X_add_C h
  have hPne : P ≠ 0 := fun hc => by rw [hc, Polynomial.degree_zero] at hdeg; exact absurd hdeg (by simp)
  have hPnd : P.natDegree ≠ 0 := by
    have := Polynomial.natDegree_pos_iff_degree_pos.mpr hdeg
    omega
  set Ap := P.comp (Polynomial.X + Polynomial.C h) with hAp
  have hAnd : Ap.natDegree = P.natDegree := by
    rw [hAp, Polynomial.natDegree_comp, hQnd, mul_one]
  have hAlc : Ap.leadingCoeff = P.leadingCoeff := by
    rw [hAp, Polynomial.leadingCoeff_comp (by rw [hQnd]; norm_num), hQm.leadingCoeff, one_pow,
      mul_one]
  have hlcP : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hPne
  have hAne : Ap ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp (by rw [hAlc]; exact hlcP)
  have hdegeq : Ap.degree = P.degree := by
    rw [Polynomial.degree_eq_natDegree hAne, Polynomial.degree_eq_natDegree hPne, hAnd]
  set Bp := Ap - P with hBp
  have hwB : Polynomial.derivative P * Bp = Polynomial.derivative Bp * P := by
    rw [hBp, mul_sub, Polynomial.derivative_sub, sub_mul, hw]
  by_cases hB0 : Bp = 0
  · have hAeq : Ap = P := by rwa [hBp, sub_eq_zero] at hB0
    refine polynomial_eval_periodic_eq_zero hdeg ?_
    intro z
    have hz := congrArg (fun q => Polynomial.eval z q) hAeq
    simpa [hAp, Polynomial.eval_comp] using hz
  · exfalso
    have hdlt : Bp.degree < P.degree := by
      rw [hBp, ← hdegeq]
      exact Polynomial.degree_sub_lt hdegeq hAne hAlc
    have hBnd : Bp.natDegree < P.natDegree := by
      rw [Polynomial.degree_eq_natDegree hB0, Polynomial.degree_eq_natDegree hPne] at hdlt
      exact_mod_cast hdlt
    have hlcB : Bp.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hB0
    by_cases hBe : Bp.natDegree = 0
    · obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hBe
      have hd0 : Polynomial.derivative Bp = 0 := by rw [← ha, Polynomial.derivative_C]
      rw [hd0, zero_mul] at hwB
      rcases mul_eq_zero.mp hwB with hc | hc
      · exact hPnd (Polynomial.derivative_eq_zero.mp hc)
      · exact hB0 hc
    · have hlc := congrArg Polynomial.leadingCoeff hwB
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul,
        leadingCoeff_derivative_eq hPnd, leadingCoeff_derivative_eq hBe] at hlc
      have hcancel : (P.natDegree : ℂ) * (P.leadingCoeff * Bp.leadingCoeff)
          = (Bp.natDegree : ℂ) * (P.leadingCoeff * Bp.leadingCoeff) := by
        linear_combination hlc
      have hnd : (P.natDegree : ℂ) = (Bp.natDegree : ℂ) :=
        mul_right_cancel₀ (mul_ne_zero hlcP hlcB) hcancel
      have : P.natDegree = Bp.natDegree := by exact_mod_cast hnd
      omega

theorem deriv_multiFlatMultiplier_eq (A : Fin r → ℝ) (M : Fin r → ℕ) (z : ℂ) :
    deriv (multiFlatMultiplier A M) z
      = (Polynomial.derivative (multiFlatPoly A M)).eval z := by
  have hfun : multiFlatMultiplier A M = fun w => (multiFlatPoly A M).eval w :=
    (funext (multiFlatPoly_eval A M)).symm
  rw [hfun, Polynomial.deriv]

/-- **The partner germs are genuinely different germs.**  Equality would make the flat multiplier
a polynomial with the nonzero period `π i`. -/
theorem mqGerms_ne {A : Fin r → ℝ} {M : Fin r → ℕ} (hApos : ∀ j, 0 < A j)
    (hAinj : Function.Injective A) (hMsum : 0 < ∑ j, M j) {j : Fin r} (hMj : 0 < M j) :
    ¬ (mqFeGerm A M j =ᶠ[𝓝 0] mqSchwarzGerm A M j) := by
  intro hgerm
  have hhne : ((Real.pi : ℂ) * I) ≠ 0 := by
    refine mul_ne_zero ?_ Complex.I_ne_zero
    simp [Real.pi_ne_zero]
  refine hhne ?_
  set c := mqFeCentre (A j) with hcdef
  set hsh : ℂ := (Real.pi : ℂ) * I with hshdef
  set Pp := multiFlatPoly A M with hPpdef
  have hdc : mqSchwarzCentre (A j) = c + hsh := mqSchwarzCentre_eq (A j)
  -- the two multiplier flux germs agree near the centre
  have hfluxEq : ∀ᶠ x in 𝓝 (0 : ℂ),
      fluxGerm (multiFlatMultiplier A M) c x
        = fluxGerm (multiFlatMultiplier A M) (mqSchwarzCentre (A j)) x := by
    have hdiff := mqGermDiff_eventuallyEq hApos hAinj hMj
    have hmc := mqFlux_eventuallyEq (A := A) (M := M) (j := j) hMj
      (quartetFactor_mqFeCentre (A j))
    have hmd := mqFlux_eventuallyEq (A := A) (M := M) (j := j) hMj
      (quartetFactor_mqSchwarzCentre (A j))
    filter_upwards [hdiff, hgerm, hmc, hmd] with x hx hgx hmcx hmdx
    simp only [Pi.sub_apply] at hx
    rw [hgx, sub_self] at hx
    rw [← hmcx, ← hmdx]
    exact sub_eq_zero.mp hx.symm
  -- the multiplier does not vanish near either centre
  have hcont : ∀ w : ℂ, ContinuousAt (fun x : ℂ => multiFlatMultiplier A M (w + x)) 0 := by
    intro w
    exact ((analyticAt_multiFlatMultiplier A M (w + 0)).continuousAt).comp_of_eq
      (by fun_prop) (by simp)
  have hnec : ∀ᶠ x in 𝓝 (0 : ℂ), multiFlatMultiplier A M (c + x) ≠ 0 := by
    refine (hcont c).eventually_ne ?_
    rw [add_zero, multiFlatMultiplier_eq_one_of_root hMj.ne' (quartetFactor_mqFeCentre (A j))]
    exact one_ne_zero
  have hned : ∀ᶠ x in 𝓝 (0 : ℂ),
      multiFlatMultiplier A M (mqSchwarzCentre (A j) + x) ≠ 0 := by
    refine (hcont (mqSchwarzCentre (A j))).eventually_ne ?_
    rw [add_zero,
      multiFlatMultiplier_eq_one_of_root hMj.ne' (quartetFactor_mqSchwarzCentre (A j))]
    exact one_ne_zero
  -- the polynomial Wronskian identity, locally
  have hkey : ∀ᶠ x in 𝓝 (0 : ℂ), x ≠ 0 →
      (Polynomial.derivative Pp).eval (c + x) * Pp.eval (c + x + hsh)
        = (Polynomial.derivative Pp).eval (c + x + hsh) * Pp.eval (c + x) := by
    filter_upwards [hfluxEq, hnec, hned] with x heq hxc hxd hx
    rw [fluxGerm_of_ne_zero _ _ hx, fluxGerm_of_ne_zero _ _ hx, hdc] at heq
    rw [hdc] at hxd
    have hsum : c + hsh + x = c + x + hsh := by ring
    rw [hsum] at heq hxd
    rw [← deriv_multiFlatMultiplier_eq, ← deriv_multiFlatMultiplier_eq,
      ← multiFlatPoly_eval, ← multiFlatPoly_eval] at *
    field_simp at heq
    linear_combination -heq
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hkey
  -- infinitely many agreements force the polynomial identity
  have hpolyeq : Polynomial.derivative Pp * (Pp.comp (Polynomial.X + Polynomial.C hsh))
      = Polynomial.derivative (Pp.comp (Polynomial.X + Polynomial.C hsh)) * Pp := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    have hinj : Set.InjOn (fun t : ℝ => c + (t : ℂ)) (Set.Ioo 0 ε) := by
      intro s _ t _ hst
      have := add_left_cancel hst
      exact_mod_cast this
    refine Set.Infinite.mono ?_ ((Set.Ioo_infinite hε).image hinj)
    rintro w ⟨t, ht, rfl⟩
    have hx : ((t : ℂ)) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt ht.1
    have hd : dist ((t : ℂ)) 0 < ε := by
      simpa [Complex.dist_eq, abs_of_pos ht.1] using ht.2
    have h := hball hd hx
    simp only [Set.mem_setOf_eq, Polynomial.eval_mul, Polynomial.derivative_comp,
      Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C, add_zero,
      one_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    exact h
  exact polynomial_wronskian_shift_eq_zero (multiFlatPoly_degree_pos hMsum) hpolyeq

/-! ## The quartets in the normalized coordinate -/

theorem coshQuartetEnvelope_quartetNode (a : ℝ) : coshQuartetEnvelope a (quartetNode a) = 0 := by
  rw [coshQuartetEnvelope,
    show quartetNode a - (a : ℂ) = ((Real.pi : ℂ) / 2) * I by simp only [quartetNode]; ring,
    cosh_pi_div_two_mul_I, zero_mul]

theorem coshQuartetEnvelope_conj_quartetNode (a : ℝ) :
    coshQuartetEnvelope a ((starRingEnd ℂ) (quartetNode a)) = 0 := by
  rw [coshQuartetEnvelope,
    show (starRingEnd ℂ) (quartetNode a) - (a : ℂ) = -((Real.pi : ℂ) / 2) * I by
      simp only [quartetNode, map_add, map_mul, map_div₀, map_ofNat, Complex.conj_I,
        Complex.conj_ofReal]
      ring,
    cosh_neg_pi_div_two_mul_I, zero_mul]

theorem multiQuartetFn_quartetNode (A : Fin r → ℝ) (M : Fin r → ℕ) (j : Fin r) :
    multiQuartetFn A M (quartetNode (A j)) = 0 := by
  rw [multiQuartetFn, multiEnvelope_eq_zero_iff.mpr ⟨j, coshQuartetEnvelope_quartetNode (A j)⟩,
    zero_mul]

theorem multiQuartetFn_conj_quartetNode (A : Fin r → ℝ) (M : Fin r → ℕ) (j : Fin r) :
    multiQuartetFn A M ((starRingEnd ℂ) (quartetNode (A j))) = 0 := by
  rw [multiQuartetFn,
    multiEnvelope_eq_zero_iff.mpr ⟨j, coshQuartetEnvelope_conj_quartetNode (A j)⟩, zero_mul]

theorem multiQuartetFn_mqFeCentre (A : Fin r → ℝ) (M : Fin r → ℕ) (j : Fin r) :
    multiQuartetFn A M (mqFeCentre (A j)) = 0 := by
  rw [mqFeCentre, multiQuartetFn_neg, multiQuartetFn_quartetNode]

theorem multiQuartetFn_mqSchwarzCentre (A : Fin r → ℝ) (M : Fin r → ℕ) (j : Fin r) :
    multiQuartetFn A M (mqSchwarzCentre (A j)) = 0 := by
  rw [mqSchwarzCentre, multiQuartetFn_neg, multiQuartetFn_conj_quartetNode]

/-- **The four quartet points in the critical strip.**  With `A_j = 2π a_j` the quartet is at
`1/4 ± i a_j` and `3/4 ± i a_j`. -/
theorem multiQuartetXi_quartet {A : Fin r → ℝ} {M : Fin r → ℕ} {j : Fin r} {a : ℝ}
    (ha : A j = 2 * Real.pi * a) :
    multiQuartetXi A M (1 / 4 + (a : ℂ) * I) = 0 ∧
      multiQuartetXi A M (3 / 4 - (a : ℂ) * I) = 0 ∧
      multiQuartetXi A M (3 / 4 + (a : ℂ) * I) = 0 ∧
      multiQuartetXi A M (1 / 4 - (a : ℂ) * I) = 0 := by
  have hAj : ((A j : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * (a : ℂ) := by
    rw [ha]; push_cast; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hcoord : -(2 * (Real.pi : ℂ) * I) * ((1 / 4 + (a : ℂ) * I) - 1 / 2)
        = quartetNode (A j) := by
      simp only [quartetNode, hAj]
      linear_combination (-(2 * (Real.pi : ℂ) * (a : ℂ))) * Complex.I_sq
    rw [multiQuartetXi, hcoord, multiQuartetFn_quartetNode]
  · have hcoord : -(2 * (Real.pi : ℂ) * I) * ((3 / 4 - (a : ℂ) * I) - 1 / 2)
        = mqFeCentre (A j) := by
      simp only [mqFeCentre, quartetNode, hAj]
      linear_combination (2 * (Real.pi : ℂ) * (a : ℂ)) * Complex.I_sq
    rw [multiQuartetXi, hcoord, multiQuartetFn_mqFeCentre]
  · have hcoord : -(2 * (Real.pi : ℂ) * I) * ((3 / 4 + (a : ℂ) * I) - 1 / 2)
        = (starRingEnd ℂ) (quartetNode (A j)) := by
      simp only [quartetNode, map_add, map_mul, map_div₀, map_ofNat, Complex.conj_I,
        Complex.conj_ofReal, hAj]
      linear_combination (-(2 * (Real.pi : ℂ) * (a : ℂ))) * Complex.I_sq
    rw [multiQuartetXi, hcoord, multiQuartetFn_conj_quartetNode]
  · have hcoord : -(2 * (Real.pi : ℂ) * I) * ((1 / 4 - (a : ℂ) * I) - 1 / 2)
        = mqSchwarzCentre (A j) := by
      simp only [mqSchwarzCentre, quartetNode, map_add, map_mul, map_div₀, map_ofNat,
        Complex.conj_I, Complex.conj_ofReal, hAj]
      linear_combination (2 * (Real.pi : ℂ) * (a : ℂ)) * Complex.I_sq
    rw [multiQuartetXi, hcoord, multiQuartetFn_mqSchwarzCentre]

/-! ## The germ statement in the normalized coordinate -/

/-- Vanishing of the low-order jet of a germ with an explicit flat factor. -/
theorem iteratedDeriv_eq_zero_of_eventuallyEq_pow_mul {Mp n : ℕ} {f W : ℂ → ℂ}
    (hW : AnalyticAt ℂ W 0) (hf : f =ᶠ[𝓝 0] fun x => x ^ Mp * W x) (hn : n < Mp) :
    iteratedDeriv n f 0 = 0 := by
  have hprod : AnalyticAt ℂ (fun x : ℂ => x ^ Mp * W x) 0 := (analyticAt_id.pow _).mul hW
  rw [hf.iteratedDeriv_eq n]
  by_cases hzero : W =ᶠ[𝓝 0] 0
  · have : (fun x : ℂ => x ^ Mp * W x) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [hzero] with x hx
      simp [hx]
    rw [this.iteratedDeriv_eq n]
    simp
  · have hWord : analyticOrderAt W 0 ≠ ⊤ := by
      rw [Ne, analyticOrderAt_eq_top]
      exact hzero
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hWord
    have hord : analyticOrderAt (fun x : ℂ => x ^ Mp * W x) 0 = ((Mp + k : ℕ) : ℕ∞) := by
      have hsplit : (fun x : ℂ => x ^ Mp * W x) = (id : ℂ → ℂ) ^ Mp * W := rfl
      rw [hsplit, analyticOrderAt_mul (analyticAt_id.pow _) hW, analyticOrderAt_pow analyticAt_id,
        analyticOrderAt_id, hk]
      simp
      rfl
    have h := GaloisForLFunctions.RHTower.GelfondSchneiderProof.analyticOrderAt_eq_nat_imp_iteratedDeriv_eq_zero
      hprod (Mp + k) hord
    have := h.1 n (by omega)
    simpa only [iteratedDeriv_eq_iterate] using this

theorem multiQuartetXi_eq_affine (A : Fin r → ℝ) (M : Fin r → ℕ) :
    multiQuartetXi A M
      = fun s : ℂ => multiQuartetFn A M ((-(2 * (Real.pi : ℂ) * I)) * s + ((Real.pi : ℂ) * I)) := by
  funext s
  rw [multiQuartetXi]
  congr 1
  ring

theorem mqAffineFactor_ne_zero : (-(2 * (Real.pi : ℂ) * I)) ≠ 0 := by
  refine neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero)
  simp [Real.pi_ne_zero]

/-- **The dictionary between the two local coordinates.**  The residue-filled germ of the
normalization at a quartet centre is the germ of the entire realizer at the corresponding centre,
read in the rescaled local coordinate. -/
theorem fluxGerm_multiQuartetXi_of_coord {A : Fin r → ℝ} {M : Fin r → ℕ} {z w : ℂ} {n : ℕ}
    (hzw : (-(2 * (Real.pi : ℂ) * I)) * z + ((Real.pi : ℂ) * I) = w)
    (hord : analyticOrderAt (multiQuartetFn A M) w = n) (x : ℂ) :
    fluxGerm (multiQuartetXi A M) z x
      = fluxGerm (multiQuartetFn A M) w ((-(2 * (Real.pi : ℂ) * I)) * x) := by
  rw [multiQuartetXi_eq_affine]
  subst hzw
  exact fluxGerm_comp_affine mqAffineFactor_ne_zero (analyticAt_multiQuartetFn A M) hord x

theorem mqCoordFe {A : Fin r → ℝ} {j : Fin r} {b : ℝ} (hb : A j = 2 * Real.pi * b) :
    (-(2 * (Real.pi : ℂ) * I)) * (3 / 4 - (b : ℂ) * I) + ((Real.pi : ℂ) * I)
      = mqFeCentre (A j) := by
  have hAj : ((A j : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * (b : ℂ) := by rw [hb]; push_cast; ring
  simp only [mqFeCentre, quartetNode, hAj]
  linear_combination (2 * (Real.pi : ℂ) * (b : ℂ)) * Complex.I_sq

theorem mqCoordSchwarz {A : Fin r → ℝ} {j : Fin r} {b : ℝ} (hb : A j = 2 * Real.pi * b) :
    (-(2 * (Real.pi : ℂ) * I)) * (1 / 4 - (b : ℂ) * I) + ((Real.pi : ℂ) * I)
      = mqSchwarzCentre (A j) := by
  have hAj : ((A j : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * (b : ℂ) := by rw [hb]; push_cast; ring
  simp only [mqSchwarzCentre, quartetNode, map_add, map_mul, map_div₀, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal, hAj]
  linear_combination (2 * (Real.pi : ℂ) * (b : ℂ)) * Complex.I_sq

theorem fluxGerm_multiQuartetXi_fe {A : Fin r → ℝ} {M : Fin r → ℕ} (hApos : ∀ j, 0 < A j)
    (hAinj : Function.Injective A) {j : Fin r} (hMj : M j ≠ 0) {b : ℝ}
    (hb : A j = 2 * Real.pi * b) (x : ℂ) :
    fluxGerm (multiQuartetXi A M) (3 / 4 - (b : ℂ) * I) x
      = mqFeGerm A M j ((-(2 * (Real.pi : ℂ) * I)) * x) :=
  fluxGerm_multiQuartetXi_of_coord (n := 1) (mqCoordFe hb)
    (by simpa using analyticOrderAt_multiQuartetFn_mqFeCentre hApos hAinj hMj) x

theorem fluxGerm_multiQuartetXi_schwarz {A : Fin r → ℝ} {M : Fin r → ℕ} (hApos : ∀ j, 0 < A j)
    (hAinj : Function.Injective A) {j : Fin r} (hMj : M j ≠ 0) {b : ℝ}
    (hb : A j = 2 * Real.pi * b) (x : ℂ) :
    fluxGerm (multiQuartetXi A M) (1 / 4 - (b : ℂ) * I) x
      = mqSchwarzGerm A M j ((-(2 * (Real.pi : ℂ) * I)) * x) :=
  fluxGerm_multiQuartetXi_of_coord (n := 1) (mqCoordSchwarz hb)
    (by simpa using analyticOrderAt_multiQuartetFn_mqSchwarzCentre hApos hAinj hMj) x

theorem analyticAt_fluxGerm_multiQuartetXi_fe {A : Fin r → ℝ} {M : Fin r → ℕ}
    (hApos : ∀ j, 0 < A j) (hAinj : Function.Injective A) {j : Fin r} (hMj : M j ≠ 0) {b : ℝ}
    (hb : A j = 2 * Real.pi * b) :
    AnalyticAt ℂ (fluxGerm (multiQuartetXi A M) (3 / 4 - (b : ℂ) * I)) 0 := by
  refine fluxGerm_analyticAt_zero (m := 1) ?_ ?_
  · rw [multiQuartetXi_eq_affine]
    exact analyticAt_comp_affine (analyticAt_multiQuartetFn A M _)
  · rw [multiQuartetXi_eq_affine]
    refine analyticOrderAt_comp_affine (n := 1) mqAffineFactor_ne_zero
      (analyticAt_multiQuartetFn A M _) ?_
    rw [mqCoordFe hb]
    simpa using analyticOrderAt_multiQuartetFn_mqFeCentre hApos hAinj hMj

theorem analyticAt_fluxGerm_multiQuartetXi_schwarz {A : Fin r → ℝ} {M : Fin r → ℕ}
    (hApos : ∀ j, 0 < A j) (hAinj : Function.Injective A) {j : Fin r} (hMj : M j ≠ 0) {b : ℝ}
    (hb : A j = 2 * Real.pi * b) :
    AnalyticAt ℂ (fluxGerm (multiQuartetXi A M) (1 / 4 - (b : ℂ) * I)) 0 := by
  refine fluxGerm_analyticAt_zero (m := 1) ?_ ?_
  · rw [multiQuartetXi_eq_affine]
    exact analyticAt_comp_affine (analyticAt_multiQuartetFn A M _)
  · rw [multiQuartetXi_eq_affine]
    refine analyticOrderAt_comp_affine (n := 1) mqAffineFactor_ne_zero
      (analyticAt_multiQuartetFn A M _) ?_
    rw [mqCoordSchwarz hb]
    simpa using analyticOrderAt_multiQuartetFn_mqSchwarzCentre hApos hAinj hMj

/-- **The two normalized partner germs agree through the prescribed depth.** -/
theorem mqXi_iteratedDeriv_eq_of_lt {A : Fin r → ℝ} {M : Fin r → ℕ} (hApos : ∀ j, 0 < A j)
    (hAinj : Function.Injective A) {j : Fin r} (hMj : 0 < M j) {b : ℝ}
    (hb : A j = 2 * Real.pi * b) {n : ℕ} (hn : n < M j) :
    iteratedDeriv n (fluxGerm (multiQuartetXi A M) (3 / 4 - (b : ℂ) * I)) 0
      = iteratedDeriv n (fluxGerm (multiQuartetXi A M) (1 / 4 - (b : ℂ) * I)) 0 := by
  set μ : ℂ := -(2 * (Real.pi : ℂ) * I) with hμdef
  have hμ : μ ≠ 0 := mqAffineFactor_ne_zero
  have htend : Filter.Tendsto (fun x : ℂ => μ * x) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun x : ℂ => μ * x) := continuous_const.mul continuous_id
    simpa using hc.tendsto 0
  have hdiffF := mqGermDiff_eventuallyEq hApos hAinj hMj
  have hdiffcomp := hdiffF.comp_tendsto htend
  have hflat : (fun x : ℂ => fluxGerm (multiQuartetXi A M) (3 / 4 - (b : ℂ) * I) x
        - fluxGerm (multiQuartetXi A M) (1 / 4 - (b : ℂ) * I) x)
      =ᶠ[𝓝 0] fun x : ℂ => x ^ (M j) *
        (μ ^ (M j) *
          (hermiteFlatFluxUnit (M j) (mqUnit A M j (mqFeCentre (A j))) (μ * x)
            - hermiteFlatFluxUnit (M j) (mqUnit A M j (mqSchwarzCentre (A j))) (μ * x))) := by
    filter_upwards [hdiffcomp] with x hx
    simp only [Function.comp_apply, Pi.sub_apply] at hx
    rw [fluxGerm_multiQuartetXi_fe hApos hAinj hMj.ne' hb,
      fluxGerm_multiQuartetXi_schwarz hApos hAinj hMj.ne' hb, hx]
    simp only [mqFlux, hermiteFlatFluxCorrection]
    ring
  have hW : AnalyticAt ℂ (fun x : ℂ => μ ^ (M j) *
      (hermiteFlatFluxUnit (M j) (mqUnit A M j (mqFeCentre (A j))) (μ * x)
        - hermiteFlatFluxUnit (M j) (mqUnit A M j (mqSchwarzCentre (A j))) (μ * x))) 0 := by
    refine analyticAt_const.mul (AnalyticAt.sub ?_ ?_)
    · exact (hermiteFlatFluxUnit_analyticAt_zero hMj
        (analyticAt_mqUnit A M j _)).comp_of_eq (analyticAt_const.mul analyticAt_id) (by simp)
    · exact (hermiteFlatFluxUnit_analyticAt_zero hMj
        (analyticAt_mqUnit A M j _)).comp_of_eq (analyticAt_const.mul analyticAt_id) (by simp)
  have hzero := iteratedDeriv_eq_zero_of_eventuallyEq_pow_mul hW hflat hn
  have hsplit : iteratedDeriv n (fun x : ℂ =>
        fluxGerm (multiQuartetXi A M) (3 / 4 - (b : ℂ) * I) x
        - fluxGerm (multiQuartetXi A M) (1 / 4 - (b : ℂ) * I) x) 0
      = iteratedDeriv n (fluxGerm (multiQuartetXi A M) (3 / 4 - (b : ℂ) * I)) 0
        - iteratedDeriv n (fluxGerm (multiQuartetXi A M) (1 / 4 - (b : ℂ) * I)) 0 :=
    iteratedDeriv_sub (analyticAt_fluxGerm_multiQuartetXi_fe hApos hAinj hMj.ne' hb).contDiffAt
      (analyticAt_fluxGerm_multiQuartetXi_schwarz hApos hAinj hMj.ne' hb).contDiffAt
  rw [hsplit] at hzero
  exact sub_eq_zero.mp hzero

/-- **The two normalized partner germs are different germs.** -/
theorem mqXi_germs_ne {A : Fin r → ℝ} {M : Fin r → ℕ} (hApos : ∀ j, 0 < A j)
    (hAinj : Function.Injective A) (hMsum : 0 < ∑ j, M j) {j : Fin r} (hMj : 0 < M j) {b : ℝ}
    (hb : A j = 2 * Real.pi * b) :
    ¬ (fluxGerm (multiQuartetXi A M) (3 / 4 - (b : ℂ) * I)
      =ᶠ[𝓝 0] fluxGerm (multiQuartetXi A M) (1 / 4 - (b : ℂ) * I)) := by
  intro hc
  refine mqGerms_ne hApos hAinj hMsum hMj ?_
  set μ : ℂ := -(2 * (Real.pi : ℂ) * I) with hμdef
  have hμ : μ ≠ 0 := mqAffineFactor_ne_zero
  have htend : Filter.Tendsto (fun y : ℂ => μ⁻¹ * y) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun y : ℂ => μ⁻¹ * y) := continuous_const.mul continuous_id
    simpa using hcont.tendsto 0
  have hcomp := hc.comp_tendsto htend
  filter_upwards [hcomp] with y hy
  simp only [Function.comp_apply] at hy
  rw [fluxGerm_multiQuartetXi_fe hApos hAinj hMj.ne' hb,
    fluxGerm_multiQuartetXi_schwarz hApos hAinj hMj.ne' hb] at hy
  rwa [show μ * (μ⁻¹ * y) = y by field_simp] at hy

/-! ## The capstone -/

/-- **Simultaneous multi-quartet finite-passport realization.**

For pairwise distinct positive displacements `A_j` and arbitrary positive depths `M_j` the entire
function `multiQuartetFn A M` and its normalization `multiQuartetXi A M` realize simultaneously:

* the functional equation `X(1-s) = X(s)` and Schwarz reality;
* no zero on the real axis;
* one off-critical quartet `1/4 ± i a_j`, `3/4 ± i a_j` for every `j`, with `a_j = A_j/(2π)`, each
  point a *simple* zero;
* no nonzero period (and exact order one, `multiQuartetFn_order_one_bounds`);
* at every quartet, identical residue-filled completed-flux Taylor coefficients at the two partner
  centres through the independently prescribed depth `M_j - 1`, while the two germs are different.
-/
theorem simultaneous_multiQuartet_realization {A : Fin r → ℝ} {M : Fin r → ℕ}
    (hr : 0 < r) (hApos : ∀ j, 0 < A j) (hAinj : Function.Injective A) (hM : ∀ j, 0 < M j) :
    (∀ w : ℂ, AnalyticAt ℂ (multiQuartetFn A M) w) ∧
      (∀ s : ℂ, multiQuartetXi A M (1 - s) = multiQuartetXi A M s) ∧
      (∀ s : ℂ, multiQuartetXi A M ((starRingEnd ℂ) s)
        = (starRingEnd ℂ) (multiQuartetXi A M s)) ∧
      (∀ t : ℝ, multiQuartetXi A M (t : ℂ) ≠ 0) ∧
      (∀ h : ℂ, Function.Periodic (multiQuartetFn A M) h ↔ h = 0) ∧
      (∀ j : Fin r, analyticOrderAt (multiQuartetFn A M) (mqFeCentre (A j)) = 1 ∧
        analyticOrderAt (multiQuartetFn A M) (mqSchwarzCentre (A j)) = 1) ∧
      (∀ j : Fin r, ∀ n < M j,
        iteratedDeriv n (mqFeGerm A M j) 0 = iteratedDeriv n (mqSchwarzGerm A M j) 0) ∧
      (∀ j : Fin r, ¬ (mqFeGerm A M j =ᶠ[𝓝 0] mqSchwarzGerm A M j)) ∧
      (∀ (j : Fin r) (b : ℝ), A j = 2 * Real.pi * b →
        (multiQuartetXi A M (1 / 4 + (b : ℂ) * I) = 0 ∧
          multiQuartetXi A M (3 / 4 - (b : ℂ) * I) = 0 ∧
          multiQuartetXi A M (3 / 4 + (b : ℂ) * I) = 0 ∧
          multiQuartetXi A M (1 / 4 - (b : ℂ) * I) = 0) ∧
        (∀ n < M j,
          iteratedDeriv n (fluxGerm (multiQuartetXi A M) (3 / 4 - (b : ℂ) * I)) 0
            = iteratedDeriv n (fluxGerm (multiQuartetXi A M) (1 / 4 - (b : ℂ) * I)) 0) ∧
        ¬ (fluxGerm (multiQuartetXi A M) (3 / 4 - (b : ℂ) * I)
          =ᶠ[𝓝 0] fluxGerm (multiQuartetXi A M) (1 / 4 - (b : ℂ) * I))) := by
  haveI : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  have hMsum : 0 < ∑ j, M j :=
    Finset.sum_pos (fun j _ => hM j) Finset.univ_nonempty
  refine ⟨analyticAt_multiQuartetFn A M, multiQuartetXi_functional_equation A M,
    multiQuartetXi_conj A M,
    multiQuartetXi_ne_zero_of_real (fun j => (hApos j).ne') M,
    multiQuartetFn_periodic_iff hr hMsum,
    fun j => ⟨analyticOrderAt_multiQuartetFn_mqFeCentre hApos hAinj (hM j).ne',
      analyticOrderAt_multiQuartetFn_mqSchwarzCentre hApos hAinj (hM j).ne'⟩,
    fun j n hn => mqFeGerm_iteratedDeriv_eq_of_lt hApos hAinj (hM j) hn,
    fun j => mqGerms_ne hApos hAinj hMsum (hM j),
    fun j b hb => ⟨multiQuartetXi_quartet hb,
      fun n hn => mqXi_iteratedDeriv_eq_of_lt hApos hAinj (hM j) hb hn,
      mqXi_germs_ne hApos hAinj hMsum (hM j) hb⟩⟩

end

end RHTower
