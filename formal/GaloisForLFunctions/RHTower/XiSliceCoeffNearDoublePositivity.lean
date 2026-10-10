import GaloisForLFunctions.RHTower.XiReciprocalSliceNearDoubleDominance
import GaloisForLFunctions.HTGeometry.ElementaryProductPairPerturbation

/-!
# Low-order slice positivity from near-line off-line zeros

The slice coefficients `c_{2j}(t)` of `x ↦ ξ(½+x+it) ξ(½−x+it)` are `Ξ(t)²` times the elementary
symmetric functions `e_j(w)` of the atoms `w_z = (z − t)^{−2}` over the zeros `z` of `Ξ`.
A critical zero gives a positive atom.  An off-line pair `z, z̄` gives a conjugate pair of atoms, and

  `(1 + w y)(1 + w̄ y) = (1 + |w| y)² − 4 β y`,  `|w| = 1/|z − t|²`,  `β = (Im z)²/|z − t|⁴`.

**Theorem** (`xiSliceCoeff_re_pos_of_offLine_nearDouble`).  Let `j ≥ 1`, and let `C₀` be a set
of at least `j` critical zero copies within distance `D` of `t`.  If

  `D² Σ_{off-line z} (Im z)²/|z − t|⁴ ≤ 1/(3j)`,

then `c_{2j}(t) > 0`.  No separation of the off-line zeros from `t` is required.

So a low-order slice sign can fail at `t` only if the off-line zeros carry displacement-weighted
mass `Σ (Im z)²/|z − t|⁴ > 1/(3j D_j²)`, where `D_j` is the distance to the `j`-th nearest
critical zero.  Off-line zeros close to the critical line act as double critical zeros.

**Cone refinement** (`xiSliceCoeff_re_pos_of_exposed_nearDouble`).  A pair inside the visibility
cone of `t` (`|Re z − t| ≥ |Im z|`) has `Re w ≥ 0`, so its factor `1 + 2 Re w y + |w|² y²` has
nonnegative coefficients.  It is kept exactly and costs nothing.  Only the *exposed* off-line
zeros, those with `|Re z − t| < |Im z|`, enter the mass.  With no exposed zeros this is the cone
criterion.  In general a low-order sign fails at `t` only if the exposed zeros carry mass
`> 1/(3j D_j²)`.  A single exposed pair costs at most `2/(Im z)²`, so it is harmless once `j`
critical zeros lie within `|Im z|/√(6j)` of `t`.

**Multiplicity** (`xiSliceCoeff_re_pos_of_exposed_nearDouble_card`).  With `m ≥ j` critical zeros
within `D`, the elementary corner ratio improves to `θ (m − i + 1) e_{i−1} ≤ i e_i`
(`HTGeometry.cornerRatio_elemProd_count`), and the condition becomes
`3j D² Σ_{exposed} ≤ m − j + 1`: each additional critical zero within `D` pays for exposure.

Proof.  Truncate the zero set symmetrically: the critical copies, the upper off-line copies of a
finite set, and their mirrors (`sliceTrunc`).  The truncated product is the real polynomial
`R(−σ²)` with `R = ∏_crit (1 + x y) ∏_pairs ((1 + x y)² − 4β y)`.  The unperturbed product
`P = ∏ (1 + x y)` over the rotated atoms has the corner ratio `e_{j−m} ≤ (jD²)^m e_j` and
`e_j ≥ (jD²)^{−j}`.  The pair perturbation law gives
`[y^j] R ≥ e_j (2 − ∏ (1 + 4jD² β)) ≥ e_j (2 − e^{2/3})`.  Taylor coefficients converge along the
truncations, and the bound passes to the limit.
-/

open Complex Filter Topology Metric Polynomial
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Taylor coefficients of polynomial functions -/

theorem iteratedDeriv_polynomial_eval (Q : ℂ[X]) (n : ℕ) :
    iteratedDeriv n (fun x => Q.eval x) = fun x => (derivative^[n] Q).eval x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    funext x
    exact Polynomial.deriv _

theorem factorial_inv_mul_iteratedDeriv_polynomial_eval (Q : ℂ[X]) (n : ℕ) :
    ((n.factorial : ℂ))⁻¹ * iteratedDeriv n (fun x => Q.eval x) 0 = Q.coeff n := by
  rw [iteratedDeriv_polynomial_eval]
  beta_reduce
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative,
    zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  field_simp

/-- The even Taylor coefficients of `σ ↦ R(−σ²)` for a real polynomial `R`. -/
theorem factorial_inv_mul_iteratedDeriv_eval_neg_sq (R : ℝ[X]) (j : ℕ) :
    (((2 * j).factorial : ℂ))⁻¹ *
        iteratedDeriv (2 * j) (fun σ : ℂ => (R.map (algebraMap ℝ ℂ)).eval (-σ ^ 2)) 0 =
      (-1) ^ j * ((R.coeff j : ℝ) : ℂ) := by
  set Q : ℂ[X] := expand ℂ 2 (R.map (algebraMap ℝ ℂ)) with hQ
  have hfun : (fun σ : ℂ => (R.map (algebraMap ℝ ℂ)).eval (-σ ^ 2)) =
      fun σ => Q.eval (I * σ) := by
    funext σ
    rw [hQ, expand_eval, mul_pow, I_sq, neg_one_mul]
  rw [hfun, iteratedDeriv_comp_const_mul (Q.differentiable.contDiff) I]
  beta_reduce
  rw [mul_zero, mul_left_comm, factorial_inv_mul_iteratedDeriv_polynomial_eval, hQ,
    show 2 * j = j * 2 by ring, coeff_expand_mul (by norm_num), coeff_map, pow_mul', I_sq]
  rfl

/-! ## Locally uniform convergence of the full truncations -/

/-- The finite products over all zero copies converge locally uniformly to `h_t/h_t(0)`. -/
theorem tendstoLocallyUniformlyOn_prod_sliceFactorTerm {t : ℝ} (ht : XiC t ≠ 0) (R : ℝ) :
    TendstoLocallyUniformlyOn (fun (S : Finset XiZeroCopy) σ => ∏ q ∈ S, (1 + sliceFactorTerm t q σ))
      (fun σ => xiHorizontalPair t σ / xiHorizontalPair t 0) atTop (ball (0 : ℂ) R) := by
  have hu : Summable (fun q : XiZeroCopy => R ^ 2 * (1 / ‖xiSpectralPoint q - t‖ ^ 2)) :=
    (summable_inv_sq_norm_xiSpectralPoint_sub (t : ℂ)).mul_left _
  have h := Summable.hasProdLocallyUniformlyOn_one_add (f := fun (q : XiZeroCopy) σ =>
    sliceFactorTerm t q σ) (K := ball (0 : ℂ) R) isOpen_ball hu
    (Eventually.of_forall fun (q : XiZeroCopy) (σ : ℂ) (hσ : σ ∈ ball (0 : ℂ) R) => by
      rw [norm_sliceFactorTerm]
      have hσ' : ‖σ‖ < R := by simpa using hσ
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg σ) hσ'.le 2)
        (by positivity))
    (fun q => by unfold sliceFactorTerm; fun_prop)
  refine TendstoLocallyUniformlyOn.congr_right h fun σ _ => ?_
  have h1 : Tendsto (fun S : Finset XiZeroCopy => ∏ q ∈ S, (1 + sliceFactorTerm t q σ)) atTop
      (𝓝 (∏' q, (1 + sliceFactorTerm t q σ))) :=
    (multipliable_one_add_of_summable ((summable_inv_sq_norm_xiSpectralPoint_sub (t : ℂ)).mul_left
      (‖σ‖ ^ 2) |>.congr fun q => (norm_sliceFactorTerm t q σ).symm)).hasProd
  refine tendsto_nhds_unique h1 ((tendsto_prod_one_sub_sq_div ht σ).congr fun S => ?_)
  refine Finset.prod_congr rfl fun q _ => ?_
  unfold sliceFactorTerm
  ring

/-! ## Symmetric truncations -/

/-- An off-line zero copy in the upper half: `Im z > 0`. -/
def XiCopyUpper (q : XiZeroCopy) : Prop := 0 < (xiSpectralPoint q).im

open scoped Classical in
/-- The critical copies of `S`. -/
def sliceTruncCrit (S : Finset XiZeroCopy) : Finset XiZeroCopy := S.filter XiCopyCritical

open scoped Classical in
/-- The upper off-line copies of `S`. -/
def sliceTruncUp (S : Finset XiZeroCopy) : Finset XiZeroCopy := S.filter XiCopyUpper

open scoped Classical in
/-- The symmetric truncation of `S`: its critical copies, its upper copies, and the mirrors of
its upper copies. -/
def sliceTrunc (S : Finset XiZeroCopy) : Finset XiZeroCopy :=
  sliceTruncCrit S ∪ sliceTruncUp S ∪ (sliceTruncUp S).map xiZeroCopyLineConjEquiv.toEmbedding

theorem mem_sliceTruncCrit {S : Finset XiZeroCopy} {q : XiZeroCopy} :
    q ∈ sliceTruncCrit S ↔ q ∈ S ∧ XiCopyCritical q := by
  unfold sliceTruncCrit; simp

theorem mem_sliceTruncUp {S : Finset XiZeroCopy} {q : XiZeroCopy} :
    q ∈ sliceTruncUp S ↔ q ∈ S ∧ XiCopyUpper q := by
  unfold sliceTruncUp; simp

theorem im_xiSpectralPoint_lineConj (q : XiZeroCopy) :
    (xiSpectralPoint (xiZeroCopyLineConjEquiv q)).im = -(xiSpectralPoint q).im := by
  rw [xiSpectralPoint_lineConj, Complex.conj_im]

open scoped Classical in
/-- Products over a symmetric truncation pair every upper copy with its mirror. -/
theorem prod_sliceTrunc (f : XiZeroCopy → ℂ) (S : Finset XiZeroCopy) :
    ∏ q ∈ sliceTrunc S, f q =
      (∏ q ∈ sliceTruncCrit S, f q) * ∏ q ∈ sliceTruncUp S, (f q * f (xiZeroCopyLineConjEquiv q)) := by
  unfold sliceTrunc
  rw [Finset.prod_union, Finset.prod_union, Finset.prod_map, mul_assoc, ← Finset.prod_mul_distrib]
  · rfl
  · rw [Finset.disjoint_left]
    intro q h1 h2
    have := (mem_sliceTruncCrit.mp h1).2
    have := (mem_sliceTruncUp.mp h2).2
    unfold XiCopyCritical at *; unfold XiCopyUpper at *
    linarith
  · rw [Finset.disjoint_left]
    intro q h1 h2
    obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp h2
    have hup := (mem_sliceTruncUp.mp hr).2
    unfold XiCopyUpper at hup
    simp only [Equiv.coe_toEmbedding] at h1
    have him := im_xiSpectralPoint_lineConj r
    rcases Finset.mem_union.mp h1 with h | h
    · have := (mem_sliceTruncCrit.mp h).2
      unfold XiCopyCritical at this
      linarith
    · have := (mem_sliceTruncUp.mp h).2
      unfold XiCopyUpper at this
      linarith

theorem tendsto_sliceTrunc : Tendsto sliceTrunc atTop atTop := by
  classical
  refine Filter.tendsto_atTop_atTop.mpr fun F =>
    ⟨F ∪ F.map xiZeroCopyLineConjEquiv.symm.toEmbedding, fun S hS r hr => ?_⟩
  unfold sliceTrunc
  simp only [Finset.mem_union, mem_sliceTruncCrit, mem_sliceTruncUp, Finset.mem_map,
    Equiv.coe_toEmbedding]
  have hrS : r ∈ S := hS (Finset.mem_union_left _ hr)
  rcases lt_trichotomy (xiSpectralPoint r).im 0 with h | h | h
  · right
    refine ⟨xiZeroCopyLineConjEquiv.symm r, ⟨hS (Finset.mem_union_right _
      (Finset.mem_map.mpr ⟨r, hr, rfl⟩)), ?_⟩, Equiv.apply_symm_apply _ _⟩
    unfold XiCopyUpper
    have hs := im_xiSpectralPoint_lineConj (xiZeroCopyLineConjEquiv.symm r)
    rw [Equiv.apply_symm_apply] at hs
    linarith
  · exact Or.inl (Or.inl ⟨hrS, h⟩)
  · exact Or.inl (Or.inr ⟨hrS, h⟩)

/-! ## The real polynomial of a symmetric truncation -/

/-- The rotated atom `1/|z − t|²`. -/
def sliceAtom (t : ℝ) (q : XiZeroCopy) : ℝ := 1 / ‖xiSpectralPoint q - t‖ ^ 2

/-- The displacement weight `(Im z)²/|z − t|⁴`. -/
def sliceDefect (t : ℝ) (q : XiZeroCopy) : ℝ :=
  (xiSpectralPoint q).im ^ 2 / ‖xiSpectralPoint q - t‖ ^ 4

/-- `R = ∏_crit (1 + x y) ∏_upper ((1 + x y)² − 4β y)`. -/
def sliceTruncPoly (t : ℝ) (S : Finset XiZeroCopy) : ℝ[X] :=
  (∏ q ∈ sliceTruncCrit S, (1 + C (sliceAtom t q) * X)) *
    ∏ q ∈ sliceTruncUp S, ((1 + C (sliceAtom t q) * X) ^ 2 - C (4 * sliceDefect t q) * X)

/-- **A conjugate pair of slice factors.**  `(1 − σ²/c²)(1 − σ²/c̄²) =
(1 − σ²/|c|²)² + 4σ² (Im c)²/|c|⁴`. -/
theorem pair_sliceFactor_eq {c : ℂ} (hc : c ≠ 0) (σ : ℂ) :
    (1 - σ ^ 2 / c ^ 2) * (1 - σ ^ 2 / (starRingEnd ℂ c) ^ 2) =
      (1 + ((1 / ‖c‖ ^ 2 : ℝ) : ℂ) * (-σ ^ 2)) ^ 2 -
        ((4 * (c.im ^ 2 / ‖c‖ ^ 4) : ℝ) : ℂ) * (-σ ^ 2) := by
  have hcc : starRingEnd ℂ c ≠ 0 := (_root_.map_ne_zero _).mpr hc
  have hN : ((‖c‖ : ℝ) : ℂ) ^ 2 = c * starRingEnd ℂ c := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hIm : ((c.im : ℝ) : ℂ) ^ 2 * (-4) = (c - starRingEnd ℂ c) ^ 2 := by
    rw [Complex.sub_conj]; push_cast; ring_nf; rw [I_sq]; ring
  have hm : ((c.im : ℝ) : ℂ) ^ 2 = -(c - starRingEnd ℂ c) ^ 2 / 4 := by
    linear_combination hIm / (-4)
  push_cast
  rw [show ((‖c‖ : ℝ) : ℂ) ^ 4 = (((‖c‖ : ℝ) : ℂ) ^ 2) ^ 2 by ring, hN, hm]
  field_simp
  ring

theorem one_add_sliceFactorTerm_eq_eval_of_critical {t : ℝ} {q : XiZeroCopy}
    (hq : XiCopyCritical q) (σ : ℂ) :
    1 + sliceFactorTerm t q σ = ((sliceAtom t q : ℝ) : ℂ) * (-σ ^ 2) + 1 := by
  unfold XiCopyCritical at hq
  have hz : xiSpectralPoint q - t = (((xiSpectralPoint q).re - t : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simpa using hq)
  have hn : ‖xiSpectralPoint q - t‖ ^ 2 = ((xiSpectralPoint q).re - t) ^ 2 := by
    rw [hz, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold sliceFactorTerm sliceAtom
  rw [hn, hz]
  push_cast
  ring

/-- **The truncated product is a real polynomial in `−σ²`.** -/
theorem prod_sliceTrunc_eq_eval {t : ℝ} (ht : XiC t ≠ 0) (S : Finset XiZeroCopy) (σ : ℂ) :
    ∏ q ∈ sliceTrunc S, (1 + sliceFactorTerm t q σ) =
      ((sliceTruncPoly t S).map (algebraMap ℝ ℂ)).eval (-σ ^ 2) := by
  rw [prod_sliceTrunc, sliceTruncPoly, Polynomial.map_mul, Polynomial.map_prod,
    Polynomial.map_prod, eval_mul, eval_prod, eval_prod]
  congr 1
  · refine Finset.prod_congr rfl fun q hq => ?_
    rw [one_add_sliceFactorTerm_eq_eval_of_critical (mem_sliceTruncCrit.mp hq).2]
    simp [add_comm]
  · refine Finset.prod_congr rfl fun q _ => ?_
    have hc : xiSpectralPoint q - t ≠ 0 := sub_ne_zero.mpr (xiSpectralPoint_ne_ofReal ht q)
    have hconj : xiSpectralPoint (xiZeroCopyLineConjEquiv q) - t =
        starRingEnd ℂ (xiSpectralPoint q - t) := by
      rw [xiSpectralPoint_lineConj, map_sub, Complex.conj_ofReal]
    have him : (xiSpectralPoint q - t).im = (xiSpectralPoint q).im := by simp
    have e := pair_sliceFactor_eq hc σ
    rw [him] at e
    unfold sliceFactorTerm
    rw [hconj, show ∀ a b : ℂ, (1 + -a) * (1 + -b) = (1 - a) * (1 - b) by intros; ring, e]
    simp [sliceAtom, sliceDefect]

/-! ## Near-double positivity of the low-order slice coefficients -/

theorem exp_two_thirds_lt_two : Real.exp (2 / 3) < 2 := by
  have h := Real.log_two_gt_d9
  calc Real.exp (2 / 3) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr (by norm_num at h ⊢; linarith)
    _ = 2 := Real.exp_log (by norm_num)

/-- **Cone and near-double positivity of the slice coefficients.**  Let `j ≥ 1` and let `C₀` be a
set of `m ≥ j` critical zero copies within distance `D` of `t`.  Call an off-line zero `z`
*exposed at `t`* when `|Re z − t| < |Im z|`, i.e. `z` lies outside the visibility cone of `t`.  If
`3j D² Σ_{exposed} (Im z)²/|z − t|⁴ ≤ m − j + 1`, then `Re c_{2j}(t) > 0`.  Off-line zeros inside
the cone cost nothing, and every additional critical zero within `D` pays for exposure. -/
theorem xiSliceCoeff_re_pos_of_exposed_nearDouble_card {t : ℝ} (ht : XiC t ≠ 0) {j : ℕ}
    (hj : 1 ≤ j) (C₀ : Finset XiZeroCopy) (hC₀ : ∀ q ∈ C₀, XiCopyCritical q) (hk₀ : j ≤ C₀.card)
    {D : ℝ} (hD : ∀ q ∈ C₀, ‖xiSpectralPoint q - t‖ ≤ D)
    (hoff : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, ¬ XiCopyCritical q ∧
        |(xiSpectralPoint q).re - t| < |(xiSpectralPoint q).im|) →
      3 * j * (D ^ 2 * ∑ q ∈ F, (xiSpectralPoint q).im ^ 2 / ‖xiSpectralPoint q - t‖ ^ 4) ≤
        (C₀.card : ℝ) - j + 1) :
    0 < (xiSliceCoeff t (2 * j)).re := by
  classical
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  obtain ⟨q₀, hq₀⟩ : C₀.Nonempty := Finset.card_pos.mp (by omega)
  have hDpos : 0 < D := lt_of_lt_of_le
    (norm_pos_iff.mpr (sub_ne_zero.mpr (xiSpectralPoint_ne_ofReal ht q₀))) (hD q₀ hq₀)
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (D ^ 2)⁻¹ := ⟨_, rfl⟩
  have hθpos : 0 < θ := by rw [hθ]; positivity
  have hjθ : (j : ℝ) / θ = j * D ^ 2 := by rw [hθ]; field_simp
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = (C₀.card : ℝ) - j + 1 := ⟨_, rfl⟩
  have hμ1 : 1 ≤ μ := by
    have : (j : ℝ) ≤ C₀.card := by exact_mod_cast hk₀
    rw [hμ]; linarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = j * D ^ 2 / μ := ⟨_, rfl⟩
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  -- coefficient convergence along the symmetric truncations
  have hconv := tendstoLocallyUniformlyOn_prod_sliceFactorTerm ht 1
  have hd : ∀ᶠ S in atTop, DifferentiableOn ℂ
      (fun σ => ∏ q ∈ S, (1 + sliceFactorTerm t q σ)) (ball 0 1) :=
    Eventually.of_forall fun S =>
      (Differentiable.fun_finsetProd fun q _ => by unfold sliceFactorTerm; fun_prop).differentiableOn
  have hD2 := ((GaloisForLFunctions.tendstoLocallyUniformlyOn_iteratedDeriv isOpen_ball hconv hd
    (2 * j)).1.tendsto_at (mem_ball_self one_pos)).comp tendsto_sliceTrunc
  have hlimval : (((2 * j).factorial : ℂ))⁻¹ *
      iteratedDeriv (2 * j) (fun σ => xiHorizontalPair t σ / xiHorizontalPair t 0) 0 =
        (-1) ^ j * (xiSliceCoeff t (2 * j) / xiHorizontalPair t 0) := by
    have e : (fun σ => xiHorizontalPair t σ / xiHorizontalPair t 0) =
        fun σ => (xiHorizontalPair t 0)⁻¹ * xiHorizontalPair t σ :=
      funext fun σ => by rw [div_eq_inv_mul]
    rw [e, iteratedDeriv_const_mul_field, mul_left_comm,
      factorial_inv_mul_iteratedDeriv_xiHorizontalPair, pow_mul, I_sq]
    ring
  have hlim : Tendsto (fun S => (((sliceTruncPoly t S).coeff j : ℝ) : ℂ)) atTop
      (𝓝 (xiSliceCoeff t (2 * j) / xiHorizontalPair t 0)) := by
    have h3 := (hD2.const_mul ((((2 * j).factorial : ℂ))⁻¹)).const_mul ((-1 : ℂ) ^ j)
    rw [hlimval, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul] at h3
    refine h3.congr fun S => ?_
    simp only [Function.comp_apply]
    have e : (fun σ => ∏ q ∈ sliceTrunc S, (1 + sliceFactorTerm t q σ)) =
        fun σ => ((sliceTruncPoly t S).map (algebraMap ℝ ℂ)).eval (-σ ^ 2) :=
      funext (prod_sliceTrunc_eq_eval ht S)
    rw [e, factorial_inv_mul_iteratedDeriv_eval_neg_sq, ← mul_assoc, ← pow_add, ← two_mul,
      pow_mul, neg_one_sq, one_pow, one_mul]
  -- the uniform lower bound on the truncated coefficients
  have hlow : ∀ᶠ S in atTop, (2 - Real.exp (2 / 3)) * (ρ⁻¹) ^ j ≤
      (sliceTruncPoly t S).coeff j := by
    filter_upwards [eventually_ge_atTop C₀] with S hS
    obtain ⟨Sc, hSc⟩ : ∃ Sc, Sc = sliceTruncCrit S := ⟨_, rfl⟩
    obtain ⟨Su, hSu⟩ : ∃ Su, Su = sliceTruncUp S := ⟨_, rfl⟩
    obtain ⟨So, hSo⟩ : ∃ So, So = Su.filter
        (fun q => |(xiSpectralPoint q).re - t| < |(xiSpectralPoint q).im|) := ⟨_, rfl⟩
    obtain ⟨Si, hSi⟩ : ∃ Si, Si = Su.filter
        (fun q => ¬ |(xiSpectralPoint q).re - t| < |(xiSpectralPoint q).im|) := ⟨_, rfl⟩
    have hatom_nn : ∀ q, 0 ≤ sliceAtom t q := fun q => by unfold sliceAtom; positivity
    have hdef_nn : ∀ q, 0 ≤ sliceDefect t q := fun q => by unfold sliceDefect; positivity
    obtain ⟨pp, hpp⟩ : ∃ pp : XiZeroCopy → ℝ[X], pp = fun q =>
        (1 + C (sliceAtom t q) * X) ^ 2 - C (4 * sliceDefect t q) * X := ⟨_, rfl⟩
    -- pairs inside the cone have nonnegative coefficients
    have hin : ∀ q ∈ Si, ∀ n, 0 ≤ (pp q).coeff n := by
      intro q hq n
      have hcone := (Finset.mem_filter.mp (hSi ▸ hq)).2
      push Not at hcone
      have hpos : 0 < ‖xiSpectralPoint q - t‖ :=
        norm_pos_iff.mpr (sub_ne_zero.mpr (xiSpectralPoint_ne_ofReal ht q))
      have hn2 : ‖xiSpectralPoint q - t‖ ^ 2 =
          ((xiSpectralPoint q).re - t) ^ 2 + (xiSpectralPoint q).im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
        ring
      have hsq : (xiSpectralPoint q).im ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 := by
        rw [← sq_abs ((xiSpectralPoint q).im), ← sq_abs ((xiSpectralPoint q).re - t)]
        exact pow_le_pow_left₀ (abs_nonneg _) hcone 2
      rw [hpp]
      refine coeff_sq_sub_nonneg ?_ n
      unfold sliceDefect sliceAtom
      rw [show ‖xiSpectralPoint q - t‖ ^ 4 = (‖xiSpectralPoint q - t‖ ^ 2) ^ 2 by ring]
      have hN : 0 < ‖xiSpectralPoint q - t‖ ^ 2 := by positivity
      have h2 : (xiSpectralPoint q).im ^ 2 ≤ ‖xiSpectralPoint q - t‖ ^ 2 / 2 := by
        rw [hn2]; linarith
      calc 4 * ((xiSpectralPoint q).im ^ 2 / (‖xiSpectralPoint q - t‖ ^ 2) ^ 2)
          ≤ 4 * ((‖xiSpectralPoint q - t‖ ^ 2 / 2) / (‖xiSpectralPoint q - t‖ ^ 2) ^ 2) := by
            gcongr
        _ = 2 * (1 / ‖xiSpectralPoint q - t‖ ^ 2) := by field_simp; ring
    obtain ⟨B, hB⟩ : ∃ B : ℝ[X], B = ∏ q ∈ Si, pp q := ⟨_, rfl⟩
    have hBnn : ∀ n, 0 ≤ B.coeff n := by rw [hB]; exact polyCoeff_prod_nonneg _ _ hin
    have hB0 : 1 ≤ B.coeff 0 := by
      rw [hB, coeff_zero_prod]
      refine le_of_eq (Finset.prod_eq_one fun q _ => ?_).symm
      simp [hpp, sq]
    -- the rotated critical and exposed atoms
    obtain ⟨L, hL⟩ : ∃ L : List ℝ, L = Sc.toList.map (sliceAtom t) ++
        (So.toList.map (sliceAtom t) ++ So.toList.map (sliceAtom t)) := ⟨_, rfl⟩
    have hLnn : ∀ a ∈ L, 0 ≤ a := by
      intro a ha
      rw [hL] at ha
      simp only [List.mem_append, List.mem_map] at ha
      rcases ha with ⟨q, _, rfl⟩ | ⟨q, _, rfl⟩ | ⟨q, _, rfl⟩ <;> exact hatom_nn q
    have hA : (∏ q ∈ Sc, (1 + C (sliceAtom t q) * X)) = elemProd (Sc.toList.map (sliceAtom t)) := by
      rw [elemProd, List.map_map, Finset.prod_map_toList]
      rfl
    have hU : (∏ q ∈ So, (1 + C (sliceAtom t q) * X) ^ 2) =
        elemProd (So.toList.map (sliceAtom t) ++ So.toList.map (sliceAtom t)) := by
      rw [elemProd_append, elemProd, List.map_map, Finset.prod_map_toList, ← sq,
        Finset.prod_pow]
      rfl
    have hE : (∏ q ∈ Sc, (1 + C (sliceAtom t q) * X)) * ∏ q ∈ So, (1 + C (sliceAtom t q) * X) ^ 2 =
        elemProd L := by
      rw [hA, hU, ← elemProd_append, ← hL]
    have hP : ((∏ q ∈ Sc, (1 + C (sliceAtom t q) * X)) * B) *
        ∏ q ∈ So, (1 + C (sliceAtom t q) * X) ^ 2 = elemProd L * B := by
      rw [← hE]; ring
    -- at least `m` rotated atoms are at least `θ`
    have hcount : C₀.card ≤ (L.filter fun x => decide (θ ≤ x)).length := by
      rw [hL, List.filter_append, List.length_append]
      have hsub : C₀ ⊆ (Sc.toList.filter ((fun x => decide (θ ≤ x)) ∘ sliceAtom t)).toFinset := by
        intro q hq
        rw [List.mem_toFinset, List.mem_filter, Finset.mem_toList, hSc]
        refine ⟨mem_sliceTruncCrit.mpr ⟨hS hq, hC₀ q hq⟩, ?_⟩
        have hpos : 0 < ‖xiSpectralPoint q - t‖ :=
          norm_pos_iff.mpr (sub_ne_zero.mpr (xiSpectralPoint_ne_ofReal ht q))
        have hle : ‖xiSpectralPoint q - t‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hpos.le (hD q hq) 2
        simp only [Function.comp_apply, decide_eq_true_eq, sliceAtom, hθ]
        rw [one_div]
        exact inv_anti₀ (by positivity) hle
      have h1 := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
      rw [List.filter_map, List.length_map] at *
      omega
    have hEnn := coeff_elemProd_nonneg hLnn
    -- the one-step ratio of the unperturbed product
    have hratioE : ∀ i < j, (elemProd L).coeff i ≤ ρ * (elemProd L).coeff (i + 1) := by
      intro i hi
      have h1 := cornerRatio_elemProd_count hθpos.le L hLnn (i + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at h1
      set c := (L.filter fun x => decide (θ ≤ x)).length with hc
      have hcm : (C₀.card : ℝ) ≤ c := by exact_mod_cast hcount
      have hij : ((i : ℝ) + 1) ≤ j := by exact_mod_cast hi
      have hμc : μ ≤ (c : ℝ) - (i + 1 : ℕ) + 1 := by rw [hμ]; push_cast; linarith
      have h2 : θ * μ * (elemProd L).coeff i ≤ (j : ℝ) * (elemProd L).coeff (i + 1) := by
        calc θ * μ * (elemProd L).coeff i
            ≤ θ * ((c : ℝ) - (i + 1 : ℕ) + 1) * (elemProd L).coeff i := by
              gcongr
              exact hEnn i
          _ ≤ ((i + 1 : ℕ) : ℝ) * (elemProd L).coeff (i + 1) := h1
          _ ≤ (j : ℝ) * (elemProd L).coeff (i + 1) := by
              push_cast; exact mul_le_mul_of_nonneg_right hij (hEnn _)
      rw [hρ, hθ] at *
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : (D ^ 2)⁻¹ * μ * (elemProd L).coeff i * D ^ 2 = μ * (elemProd L).coeff i := by
        field_simp
      nlinarith [hEnn i, hEnn (i + 1)]
    have hratioP : ∀ i < j, (elemProd L * B).coeff i ≤ ρ * (elemProd L * B).coeff (i + 1) :=
      coeff_mul_pred_le hEnn hBnn hρpos.le hratioE
    have hρP := coeff_sub_le_pow (elemProd L * B) hρpos.le j hratioP
    -- the unperturbed coefficient
    have hPj : (ρ⁻¹) ^ j ≤ (elemProd L * B).coeff j := by
      have h0 := coeff_sub_le_pow (elemProd L) hρpos.le j hratioE j le_rfl
      rw [Nat.sub_self, coeff_elemProd_zero] at h0
      have hEj : (ρ⁻¹) ^ j ≤ (elemProd L).coeff j := by
        rw [inv_pow, inv_le_iff_one_le_mul₀ (by positivity)]
        linarith
      exact hEj.trans (polyCoeff_le_coeff_mul hEnn hBnn hB0 j)
    -- the exposed mass
    have hup_ne : ∀ q ∈ Su, ¬ XiCopyCritical q := by
      intro q hq hcrit
      have := (mem_sliceTruncUp.mp (hSu ▸ hq)).2
      unfold XiCopyUpper at this; unfold XiCopyCritical at hcrit
      linarith
    have hSo_mem : ∀ q ∈ So, q ∈ Su ∧
        |(xiSpectralPoint q).re - t| < |(xiSpectralPoint q).im| := fun q hq => by
      rw [hSo] at hq; exact Finset.mem_filter.mp hq
    have hsumF : 2 * ρ * (2 * ∑ q ∈ So, sliceDefect t q) ≤ 2 / 3 := by
      have hSoSu : So ⊆ Su := fun q hq => (hSo_mem q hq).1
      have hdisj : Disjoint So (So.map xiZeroCopyLineConjEquiv.toEmbedding) := by
        rw [Finset.disjoint_left]
        intro q hq hq'
        obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp hq'
        have h1 := (mem_sliceTruncUp.mp (hSu ▸ hSoSu hq)).2
        have h2 := (mem_sliceTruncUp.mp (hSu ▸ hSoSu hr)).2
        unfold XiCopyUpper at h1 h2
        simp only [Equiv.coe_toEmbedding] at h1
        rw [im_xiSpectralPoint_lineConj] at h1
        linarith
      have hre_conj : ∀ q, (xiSpectralPoint (xiZeroCopyLineConjEquiv q)).re =
          (xiSpectralPoint q).re := fun q => by
        rw [xiSpectralPoint_lineConj, Complex.conj_re]
      have hoffF := hoff (So ∪ So.map xiZeroCopyLineConjEquiv.toEmbedding) (by
        intro q hq
        rcases Finset.mem_union.mp hq with h | h
        · exact ⟨hup_ne q (hSoSu h), (hSo_mem q h).2⟩
        · obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp h
          simp only [Equiv.coe_toEmbedding]
          refine ⟨fun hcrit => ?_, ?_⟩
          · unfold XiCopyCritical at hcrit
            rw [im_xiSpectralPoint_lineConj, neg_eq_zero] at hcrit
            exact hup_ne r (hSoSu hr) hcrit
          · rw [hre_conj, im_xiSpectralPoint_lineConj, abs_neg]
            exact (hSo_mem r hr).2)
      rw [Finset.sum_union hdisj, Finset.sum_map] at hoffF
      have hsym : ∀ q, (xiSpectralPoint (xiZeroCopyLineConjEquiv q)).im ^ 2 /
          ‖xiSpectralPoint (xiZeroCopyLineConjEquiv q) - t‖ ^ 4 = sliceDefect t q := by
        intro q
        rw [im_xiSpectralPoint_lineConj, xiSpectralPoint_lineConj,
          show starRingEnd ℂ (xiSpectralPoint q) - t = starRingEnd ℂ (xiSpectralPoint q - t) by
            rw [map_sub, Complex.conj_ofReal], Complex.norm_conj, neg_sq]
        rfl
      simp only [Equiv.coe_toEmbedding, hsym] at hoffF
      have e : ∑ q ∈ So, (xiSpectralPoint q).im ^ 2 / ‖xiSpectralPoint q - t‖ ^ 4 =
          ∑ q ∈ So, sliceDefect t q := rfl
      rw [e, ← hμ] at hoffF
      have hμpos : 0 < μ := by linarith
      rw [hρ, show 2 * ((j : ℝ) * D ^ 2 / μ) * (2 * ∑ q ∈ So, sliceDefect t q) =
          (4 * ((j : ℝ) * D ^ 2 * ∑ q ∈ So, sliceDefect t q)) / μ by ring, div_le_iff₀ hμpos]
      nlinarith
    have hProd : ∏ q ∈ So, (1 + 4 * ρ * sliceDefect t q) ≤ Real.exp (2 / 3) := by
      calc ∏ q ∈ So, (1 + 4 * ρ * sliceDefect t q)
          ≤ ∏ q ∈ So, Real.exp (4 * ρ * sliceDefect t q) :=
            Finset.prod_le_prod (fun q _ => by have := hdef_nn q; positivity)
              fun q _ => by linarith [Real.add_one_le_exp (4 * ρ * sliceDefect t q)]
        _ = Real.exp (4 * ρ * ∑ q ∈ So, sliceDefect t q) := by
            rw [← Real.exp_sum, Finset.mul_sum]
        _ ≤ Real.exp (2 / 3) := by
            apply Real.exp_le_exp.mpr
            linarith
    -- the pair perturbation law on the exposed pairs
    have hpert := coeff_mul_prod_pair_ge ((∏ q ∈ Sc, (1 + C (sliceAtom t q) * X)) * B)
      (polyCoeff_mul_nonneg (by rw [hA]; exact coeff_elemProd_nonneg (by
        intro a ha; obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha; exact hatom_nn q)) hBnn)
      So (sliceAtom t) (sliceDefect t) (fun q _ => hatom_nn q) (fun q _ => hdef_nn q) j
      (ρ := ρ) hρpos.le (by
        intro m hm
        rw [hP]
        exact hρP m hm)
    rw [hP] at hpert
    have hR : (sliceTruncPoly t S).coeff j =
        (((∏ q ∈ Sc, (1 + C (sliceAtom t q) * X)) * B) *
          ∏ q ∈ So, ((1 + C (sliceAtom t q) * X) ^ 2 - C (4 * sliceDefect t q) * X)).coeff j := by
      have hsplit := Finset.prod_filter_mul_prod_filter_not Su
        (fun q => |(xiSpectralPoint q).re - t| < |(xiSpectralPoint q).im|) pp
      rw [← hSo, ← hSi] at hsplit
      unfold sliceTruncPoly
      rw [← hSc, ← hSu]
      have e2 : (∏ q ∈ Su, ((1 + C (sliceAtom t q) * X) ^ 2 - C (4 * sliceDefect t q) * X)) =
          ∏ q ∈ Su, pp q := by rw [hpp]
      rw [e2, ← hsplit, hB]
      congr 1
      simp only [hpp]
      ring
    rw [hR]
    refine le_trans ?_ hpert
    have h2 : 0 < 2 - Real.exp (2 / 3) := by linarith [exp_two_thirds_lt_two]
    have h3 : 2 - Real.exp (2 / 3) ≤ 2 - ∏ q ∈ So, (1 + 4 * ρ * sliceDefect t q) := by
      linarith
    calc (2 - Real.exp (2 / 3)) * (ρ⁻¹) ^ j ≤ (2 - Real.exp (2 / 3)) * (elemProd L * B).coeff j :=
          mul_le_mul_of_nonneg_left hPj h2.le
      _ ≤ (elemProd L * B).coeff j * (2 - ∏ q ∈ So, (1 + 4 * ρ * sliceDefect t q)) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left h3 (le_trans (by positivity) hPj)
  -- pass to the limit
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  have hge : (2 - Real.exp (2 / 3)) * (ρ⁻¹) ^ j ≤
      (xiSliceCoeff t (2 * j) / xiHorizontalPair t 0).re :=
    ge_of_tendsto hre (hlow.mono fun S h => by simpa using h)
  have hpos : 0 < (2 - Real.exp (2 / 3)) * (ρ⁻¹) ^ j :=
    mul_pos (by linarith [exp_two_thirds_lt_two]) (by positivity)
  have hh0 := xiHorizontalPair_zero_eq_ofReal (t := t)
  have hreal : (XiC (t : ℂ)).im = 0 := by
    have h := XiC_conj (t : ℂ)
    rw [Complex.conj_ofReal] at h
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  have hre0 : (XiC (t : ℂ)).re ≠ 0 := by
    intro h0
    apply ht
    exact Complex.ext (by simp [h0]) (by simp [hreal])
  have hc0 : 0 < (XiC (t : ℂ)).re ^ 2 := by positivity
  have hsplit : xiSliceCoeff t (2 * j) =
      (((XiC (t : ℂ)).re ^ 2 : ℝ) : ℂ) * (xiSliceCoeff t (2 * j) / xiHorizontalPair t 0) := by
    rw [← hh0, mul_div_cancel₀]
    rw [hh0]
    exact_mod_cast hc0.ne'
  rw [hsplit, Complex.re_ofReal_mul]
  exact mul_pos hc0 (lt_of_lt_of_le hpos hge)

/-- **Cone and near-double positivity, one critical copy per order.**  If `j ≤ |C₀|` critical
copies lie within `D` of `t` and `D² Σ_{exposed} (Im z)²/|z − t|⁴ ≤ 1/(3j)`, then
`Re c_{2j}(t) > 0`. -/
theorem xiSliceCoeff_re_pos_of_exposed_nearDouble {t : ℝ} (ht : XiC t ≠ 0) {j : ℕ} (hj : 1 ≤ j)
    (C₀ : Finset XiZeroCopy) (hC₀ : ∀ q ∈ C₀, XiCopyCritical q) (hk₀ : j ≤ C₀.card) {D : ℝ}
    (hD : ∀ q ∈ C₀, ‖xiSpectralPoint q - t‖ ≤ D)
    (hoff : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, ¬ XiCopyCritical q ∧
        |(xiSpectralPoint q).re - t| < |(xiSpectralPoint q).im|) →
      D ^ 2 * ∑ q ∈ F, (xiSpectralPoint q).im ^ 2 / ‖xiSpectralPoint q - t‖ ^ 4 ≤
        1 / (3 * j)) :
    0 < (xiSliceCoeff t (2 * j)).re := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  refine xiSliceCoeff_re_pos_of_exposed_nearDouble_card ht hj C₀ hC₀ hk₀ hD fun F hF => ?_
  have h1 := hoff F hF
  have hcard : (j : ℝ) ≤ C₀.card := by exact_mod_cast hk₀
  have h2 : 3 * j * (D ^ 2 * ∑ q ∈ F, (xiSpectralPoint q).im ^ 2 /
      ‖xiSpectralPoint q - t‖ ^ 4) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  linarith

/-- **Near-double positivity of the slice coefficients.**  Let `j ≥ 1` and let `C₀` be a set of
at least `j` critical zero copies within distance `D` of `t`.  If
`D² Σ_{off-line} (Im z)²/|z − t|⁴ ≤ 1/(3j)`, then `Re c_{2j}(t) > 0`. -/
theorem xiSliceCoeff_re_pos_of_offLine_nearDouble {t : ℝ} (ht : XiC t ≠ 0) {j : ℕ} (hj : 1 ≤ j)
    (C₀ : Finset XiZeroCopy) (hC₀ : ∀ q ∈ C₀, XiCopyCritical q) (hk₀ : j ≤ C₀.card) {D : ℝ}
    (hD : ∀ q ∈ C₀, ‖xiSpectralPoint q - t‖ ≤ D)
    (hoff : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, ¬ XiCopyCritical q) →
      D ^ 2 * ∑ q ∈ F, (xiSpectralPoint q).im ^ 2 / ‖xiSpectralPoint q - t‖ ^ 4 ≤
        1 / (3 * j)) :
    0 < (xiSliceCoeff t (2 * j)).re :=
  xiSliceCoeff_re_pos_of_exposed_nearDouble ht hj C₀ hC₀ hk₀ hD fun F hF =>
    hoff F fun q hq => (hF q hq).1

end

end RHTower
