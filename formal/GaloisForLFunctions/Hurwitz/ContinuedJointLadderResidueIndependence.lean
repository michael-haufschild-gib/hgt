import GaloisForLFunctions.Hurwitz.PowerOrbitAdditiveSaturation
import GaloisForLFunctions.Hurwitz.ContinuedJointLadderDeformationBridge
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Joint continued-Hurwitz independence from exact monodromy values

The former joint theorem used multiplicative independence of every monomial in the monodromy
scalars.  The actual monodromy geometry has more columns: arbitrarily many branch points can be
looped independently.  A relation of degree `D` can spend one branch column at each translation
difference while `N+1` surviving columns still span the `N`-jet ladder.  Consequently the exact
conditions are only that the scalar values are pairwise distinct and none equals one.
-/

open Complex HurwitzOrbit

namespace HurwitzJointLadder

open HurwitzJointOrbit

noncomputable section

/-- Vandermonde surjectivity for any injectively selected collection of branch points. -/
theorem selected_ladder_matrix_surjective {a s : ℂ} (ha : 0 < a.im)
    {N M : ℕ} (b : Fin (N + 1) → Fin (M + 1)) (hb : Function.Injective b)
    (y : Fin (N + 1) → ℂ) :
    ∃ lam : Fin (N + 1) → ℂ, ∀ k : Fin (N + 1),
      (∑ n : Fin (N + 1),
        ((((b n : ℕ) : ℂ)) + a) ^ (-(s + ((k : ℕ) : ℂ))) * lam n) = y k := by
  have hbase_ne : ∀ n : Fin (N + 1), ((((b n : ℕ) : ℂ)) + a) ≠ 0 := by
    intro n hh
    have him : ((((b n : ℕ) : ℂ)) + a).im = a.im := by simp
    rw [hh] at him
    simp only [Complex.zero_im] at him
    rw [← him] at ha
    exact lt_irrefl 0 ha
  have huinj : Function.Injective
      (fun n : Fin (N + 1) => ((((b n : ℕ) : ℂ)) + a)⁻¹) := by
    intro n₁ n₂ h
    have h2 : ((((b n₁ : ℕ) : ℂ)) + a) = ((((b n₂ : ℕ) : ℂ)) + a) :=
      inv_injective h
    have h3 : (((b n₁ : ℕ) : ℂ)) = (((b n₂ : ℕ) : ℂ)) := by
      have := congrArg (fun w => w - a) h2
      simpa using this
    apply hb
    exact Fin.ext (Nat.cast_injective h3)
  set W : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
    Matrix.of fun k n => ((((b n : ℕ) : ℂ)) + a) ^ (-(s + ((k : ℕ) : ℂ))) with hW
  have hWfact : W = (Matrix.vandermonde
        (fun n : Fin (N + 1) => ((((b n : ℕ) : ℂ)) + a)⁻¹)).transpose
      * Matrix.diagonal
          (fun n : Fin (N + 1) => ((((b n : ℕ) : ℂ)) + a) ^ (-s)) := by
    ext k n
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]
    simp only [Matrix.vandermonde_apply]
    show ((((b n : ℕ) : ℂ)) + a) ^ (-(s + ((k : ℕ) : ℂ))) = _
    have hsplit : -(s + ((k : ℕ) : ℂ)) = (-s) + (-((k : ℕ) : ℂ)) := by ring
    have hk1 : ((((b n : ℕ) : ℂ)) + a) ^ (-(((k : ℕ)) : ℂ)) =
        (((((b n : ℕ) : ℂ)) + a)⁻¹) ^ (k : ℕ) := by
      rw [Complex.cpow_neg, Complex.cpow_natCast, inv_pow]
    rw [hsplit, Complex.cpow_add _ _ (hbase_ne n), hk1]
    ring
  have hdet : W.det ≠ 0 := by
    rw [hWfact, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    apply mul_ne_zero
    · exact (Matrix.det_vandermonde_ne_zero_iff).mpr huinj
    · rw [Finset.prod_ne_zero_iff]
      intro n _
      rw [Ne, Complex.cpow_eq_zero_iff]
      rintro ⟨h1, _⟩
      exact hbase_ne n h1
  have hunit : IsUnit W.det := isUnit_iff_ne_zero.mpr hdet
  refine ⟨W⁻¹.mulVec y, ?_⟩
  intro k
  have hWy : W.mulVec (W⁻¹.mulVec y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv W hunit, Matrix.one_mulVec]
  have hk := congrFun hWy k
  rw [Matrix.mulVec, dotProduct] at hk
  exact hk

/-- At one surviving branch point, consecutive orbit increments span each individual monodromy
label.  Ordinary Vandermonde separation needs only distinct nodes and nontrivial nodes. -/
theorem labelVector_mem_span_survivingIncrementSet
    {ι σ β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] [Fintype β] [DecidableEq β]
    (label : σ → ι) (q : ι → ℂ) (hq : Function.Injective q)
    (hq1 : ∀ j, q j ≠ 1) (W : β → σ → ℂ)
    (S : Finset β) (b : β) (hb : b ∉ S) (j : ι) :
    (fun i => if label i = j then W b i else 0) ∈
      Submodule.span ℂ (survivingIncrementSet
        (fun c m i => W c i * q (label i) ^ m) S) := by
  let e := Fintype.equivFin ι
  let qF : Fin (Fintype.card ι) → ℂ := fun k => q (e.symm k)
  let V := Matrix.vandermonde qF
  have hqF : Function.Injective qF := hq.comp e.symm.injective
  have hdet : V.det ≠ 0 := (Matrix.det_vandermonde_ne_zero_iff).mpr hqF
  have hunit : IsUnit V.det := isUnit_iff_ne_zero.mpr hdet
  let y : Fin (Fintype.card ι) → ℂ := fun k =>
    if e.symm k = j then (q (e.symm k) - 1)⁻¹ else 0
  let lam : Fin (Fintype.card ι) → ℂ := V⁻¹.mulVec y
  have hV : V.mulVec lam = y := by
    dsimp only [lam]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv V hunit, Matrix.one_mulVec]
  let u : β → ℕ → σ → ℂ := fun c m i => W c i * q (label i) ^ m
  let U := Submodule.span ℂ (survivingIncrementSet u S)
  have hgen : ∀ m : Fin (Fintype.card ι), orbitIncrement u b (m : ℕ) ∈ U := by
    intro m
    exact Submodule.subset_span ⟨b, hb, (m : ℕ), rfl⟩
  have hcomb : (∑ m : Fin (Fintype.card ι),
      lam m • orbitIncrement u b (m : ℕ)) ∈ U := by
    exact Submodule.sum_mem U fun m _ => Submodule.smul_mem U (lam m) (hgen m)
  change (fun i => if label i = j then W b i else 0) ∈ U
  convert hcomb using 1
  funext i
  symm
  have hi := congrFun hV (e (label i))
  rw [Matrix.mulVec, dotProduct] at hi
  have hi' : (∑ m : Fin (Fintype.card ι),
      q (label i) ^ (m : ℕ) * lam m) =
      (if label i = j then (q (label i) - 1)⁻¹ else 0) := by
    simpa [V, qF, y] using hi
  simp only [Finset.sum_apply, Pi.smul_apply]
  dsimp only [orbitIncrement, u]
  calc
    (∑ m : Fin (Fintype.card ι),
        lam m *
          (W b i * q (label i) ^ ((m : ℕ) + 1) -
            W b i * q (label i) ^ (m : ℕ))) =
      W b i * (q (label i) - 1) *
        ∑ m : Fin (Fintype.card ι), q (label i) ^ (m : ℕ) * lam m := by
          simp_rw [pow_succ]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m _
          ring
    _ = W b i * (q (label i) - 1) *
        (if label i = j then (q (label i) - 1)⁻¹ else 0) := by rw [hi']
    _ = if label i = j then W b i else 0 := by
      by_cases hij : label i = j
      · rw [if_pos hij, if_pos hij]
        exact mul_div_cancel_right₀ (W b i) (sub_ne_zero.mpr (hq1 (label i)))
      · simp [hij]

/-- After deleting at most `D` of the `N+D+1` branch columns, the remaining consecutive Hurwitz
increments still span every coordinate of the joint `N`-jet rectangle. -/
theorem hurwitz_survivingIncrement_span_eq_top
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℂ) (hq : Function.Injective (fun j => monoScalar (s j)))
    (hq1 : ∀ j, monoScalar (s j) ≠ 1)
    {a : ℂ} (ha : 0 < a.im) (N D : ℕ)
    (S : Finset (Fin (N + D + 1))) (hScard : S.card ≤ D) :
    let W : Fin (N + D + 1) → (ι × Fin (N + 1)) → ℂ := fun b jk =>
      ((((b : ℕ) : ℂ)) + a) ^ (-(s jk.1 + ((jk.2 : ℕ) : ℂ)))
    let u : Fin (N + D + 1) → ℕ → (ι × Fin (N + 1)) → ℂ := fun b m jk =>
      W b jk * monoScalar (s jk.1) ^ m
    Submodule.span ℂ (survivingIncrementSet u S) = ⊤ := by
  dsimp only
  let W : Fin (N + D + 1) → (ι × Fin (N + 1)) → ℂ := fun b jk =>
    ((((b : ℕ) : ℂ)) + a) ^ (-(s jk.1 + ((jk.2 : ℕ) : ℂ)))
  let u : Fin (N + D + 1) → ℕ → (ι × Fin (N + 1)) → ℂ := fun b m jk =>
    W b jk * monoScalar (s jk.1) ^ m
  let R : Finset (Fin (N + D + 1)) := Finset.univ \ S
  have hRcard : N + 1 ≤ R.card := by
    have hcard : R.card = N + D + 1 - S.card := by
      simp [R, Finset.card_sdiff]
    rw [hcard]
    omega
  obtain ⟨T, hTR, hTcard⟩ := Finset.exists_subset_card_eq hRcard
  let eT : Fin (N + 1) ≃ T := (Finset.equivFinOfCardEq hTcard).symm
  let b : Fin (N + 1) → Fin (N + D + 1) := fun n => (eT n).1
  have hb : Function.Injective b := by
    intro n m hnm
    apply eT.injective
    apply Subtype.ext
    exact hnm
  have hbS : ∀ n, b n ∉ S := by
    intro n
    have hnT : (eT n).1 ∈ T := (eT n).2
    have hnR : (eT n).1 ∈ R := hTR hnT
    exact (Finset.mem_sdiff.mp hnR).2
  let U := Submodule.span ℂ (survivingIncrementSet u S)
  have hcoordinate : ∀ p : ι × Fin (N + 1),
      (fun x : ι × Fin (N + 1) => if x = p then 1 else 0) ∈ U := by
    intro p
    obtain ⟨lam, hlam⟩ := selected_ladder_matrix_surjective ha b hb
      (fun k => if k = p.2 then 1 else 0) (s := s p.1)
    have hbranch : ∀ n : Fin (N + 1),
        (fun jk : ι × Fin (N + 1) =>
          if jk.1 = p.1 then W (b n) jk else 0) ∈ U := by
      intro n
      exact labelVector_mem_span_survivingIncrementSet Prod.fst
        (fun j => monoScalar (s j)) hq hq1 W S (b n) (hbS n) p.1
    have hsum : (∑ n : Fin (N + 1), lam n •
        (fun jk : ι × Fin (N + 1) =>
          if jk.1 = p.1 then W (b n) jk else 0)) ∈ U := by
      exact Submodule.sum_mem U fun n _ => Submodule.smul_mem U (lam n) (hbranch n)
    convert hsum using 1
    funext jk
    symm
    simp only [Finset.sum_apply, Pi.smul_apply]
    by_cases hj : jk.1 = p.1
    · simp only [if_pos hj, smul_eq_mul]
      have hk := hlam jk.2
      change (∑ n : Fin (N + 1), W (b n) (p.1, jk.2) * lam n) =
        (if jk.2 = p.2 then 1 else 0) at hk
      have hjkeq : (if jk = p then (1 : ℂ) else 0) =
          (if jk.2 = p.2 then 1 else 0) := by
        simp [Prod.ext_iff, hj]
      rw [hjkeq]
      rw [← hk]
      apply Finset.sum_congr rfl
      intro n _
      rw [show jk = (p.1, jk.2) by exact Prod.ext hj rfl]
      ring
    · have hjp : jk ≠ p := fun h => hj (congrArg Prod.fst h)
      simp [hj, hjp]
  apply top_unique
  intro x _
  change x ∈ U
  have hxrep : x = ∑ p : ι × Fin (N + 1),
      x p • (fun y : ι × Fin (N + 1) => if y = p then 1 else 0) := by
    funext y
    simp
  rw [hxrep]
  exact Submodule.sum_mem U fun p _ => Submodule.smul_mem U (x p) (hcoordinate p)

/-! ## Exact exponent-value conditions -/

/-- Equality of Hurwitz monodromy values is exactly congruence of exponents modulo `ℤ`. -/
theorem monoScalar_eq_monoScalar_iff_integerDifference (s t : ℂ) :
    monoScalar s = monoScalar t ↔ ∃ m : ℤ, s - t = (m : ℂ) := by
  rw [monoScalar, monoScalar, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hp, Complex.I_ne_zero]
    have hcancel : (2 * (Real.pi : ℂ) * Complex.I) * (-(s - t)) =
        (2 * (Real.pi : ℂ) * Complex.I) * (m : ℂ) := by
      linear_combination hm
    have h := mul_left_cancel₀ hpi hcancel
    push_cast
    linear_combination -h
  · rintro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    push_cast at hm ⊢
    linear_combination (-(2 * (Real.pi : ℂ) * Complex.I)) * hm

theorem monoScalar_injective_of_integerDifference
    {ι : Type*} (s : ι → ℂ)
    (hres : ∀ i j : ι, (∃ m : ℤ, s i - s j = (m : ℂ)) → i = j) :
    Function.Injective (fun j => monoScalar (s j)) := by
  intro i j hq
  exact hres i j ((monoScalar_eq_monoScalar_iff_integerDifference (s i) (s j)).mp hq)

theorem monoScalar_ne_one_of_nonintegral {s : ℂ}
    (hs : ∀ m : ℤ, s ≠ (m : ℂ)) : monoScalar s ≠ 1 := by
  intro h
  obtain ⟨m, hm⟩ := (monoScalar_eq_one_iff s).mp h
  exact hs m hm

open HurwitzLadder HurwitzZetaContinuation in
set_option maxHeartbeats 20000000 in
/-- **Joint continued-Hurwitz ladder independence from monodromy-value separation.**

Pairwise distinct nontrivial monodromy scalars suffice.  For a candidate relation of degree `D`,
the proof transports it over `N+D+1` independently looped branch points and applies robust additive
saturation.  No multiplicative independence of scalar monomials is assumed. -/
theorem continued_joint_hurwitz_ladder_independence_of_monoScalar
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ι → ℂ} (hq : Function.Injective (fun j => monoScalar (s j)))
    (hq1 : ∀ j, monoScalar (s j) ≠ 1)
    (N : ℕ) (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ))
    (hrel : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun jk => continuedHzeta (s jk.1 + (jk.2 : ℕ)) a) P = 0) :
    P = 0 := by
  let D := P.totalDegree
  let M := N + D
  have h1 : ∀ a : ℂ, 0 < a.im →
      continuedJointRelA s M P (fun _ _ => 1) a = 0 := by
    intro a ha
    have hg : (fun jk : ι × Fin (N + 1) =>
        continuedDzeta (s jk.1) M (fun _ => 1) (jk.2 : ℕ) a) =
        fun jk => continuedHzeta (s jk.1 + (jk.2 : ℕ)) a := by
      funext jk
      exact continuedDzeta_one (s jk.1) M (jk.2 : ℕ) a
    rw [continuedJointRelA, hg]
    exact hrel a ha
  have hgrid := continuedJointRelA_grid P h1
  have hmap : ∀ a : ℂ, 0 < a.im → MvPolynomial.map (Polynomial.evalRingHom a) P = 0 := by
    intro a ha
    let W : Fin (N + D + 1) → (ι × Fin (N + 1)) → ℂ := fun b jk =>
      ((((b : ℕ) : ℂ)) + a) ^ (-(s jk.1 + ((jk.2 : ℕ) : ℂ)))
    let base : (ι × Fin (N + 1)) → ℂ := fun jk =>
      continuedHzeta (s jk.1 + (jk.2 : ℕ)) a - ∑ b : Fin (N + D + 1), W b jk
    let u : Fin (N + D + 1) → ℕ → (ι × Fin (N + 1)) → ℂ := fun b m jk =>
      W b jk * monoScalar (s jk.1) ^ m
    let Pa : MvPolynomial (ι × Fin (N + 1)) ℂ :=
      MvPolynomial.map (Polynomial.evalRingHom a) P
    have hdz : ∀ (c : ι → Fin (N + D + 1) → ℂ) (jk : ι × Fin (N + 1)),
        continuedDzeta (s jk.1) M (c jk.1) (jk.2 : ℕ) a =
          base jk + ∑ b : Fin (N + D + 1), W b jk * c jk.1 b := by
      intro c jk
      rw [continuedDzeta]
      dsimp only [base, W, M]
      have hterm : ∀ b : Fin (N + D + 1),
          (c jk.1 b - 1) *
              ((((b : ℕ) : ℂ) + a) ^ (-(s jk.1 + (jk.2 : ℕ)))) =
            ((((b : ℕ) : ℂ) + a) ^ (-(s jk.1 + (jk.2 : ℕ)))) * c jk.1 b -
              ((((b : ℕ) : ℂ) + a) ^ (-(s jk.1 + (jk.2 : ℕ)))) := by
        intro b
        ring
      rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_sub_distrib]
      ring
    have hPaDegree : Pa.totalDegree ≤ D := by
      dsimp only [Pa, D]
      unfold MvPolynomial.totalDegree
      exact Finset.sup_mono (MvPolynomial.support_map_subset P (Polynomial.evalRingHom a))
    have hPaGrid : ∀ m : Fin (N + D + 1) → ℕ,
        MvPolynomial.eval (additiveGridPoint base u m) Pa = 0 := by
      intro m
      have hm := hgrid m a ha
      rw [continuedJointRelA, ← MvPolynomial.eval_map] at hm
      have hvalues : (fun jk : ι × Fin (N + 1) =>
          continuedDzeta (s jk.1) M
            (fun b => monoScalar (s jk.1) ^ m b) (jk.2 : ℕ) a) =
          additiveGridPoint base u m := by
        funext jk
        rw [hdz]
        rfl
      rw [hvalues] at hm
      exact hm
    apply additiveGrid_zero_of_robust_increment_span D base u Pa hPaDegree
    · intro S hScard
      exact hurwitz_survivingIncrement_span_eq_top s hq hq1 ha N D S hScard
    · exact hPaGrid
  have hcoeff : ∀ d : (ι × Fin (N + 1)) →₀ ℕ, MvPolynomial.coeff d P = 0 := by
    intro d
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinj : Function.Injective
        (fun t : ℕ => (((t : ℝ) + 1 : ℝ) : ℂ) * Complex.I) := by
      intro t₁ t₂ h
      have him := congrArg Complex.im h
      simp only [Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_one, mul_zero, add_zero] at him
      have ht : (t₁ : ℝ) = (t₂ : ℝ) := by linarith
      exact_mod_cast ht
    have hsub : Set.range (fun t : ℕ => (((t : ℝ) + 1 : ℝ) : ℂ) * Complex.I) ⊆
        {x | Polynomial.IsRoot (MvPolynomial.coeff d P) x} := by
      rintro x ⟨t, rfl⟩
      have him : 0 < ((((t : ℝ) + 1 : ℝ) : ℂ) * Complex.I).im := by
        simp only [Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_one, mul_zero, add_zero]
        positivity
      have hm := hmap _ him
      have hc := congrArg (MvPolynomial.coeff d) hm
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at hc
      exact hc
    exact Set.Infinite.mono hsub (Set.infinite_range_of_injective hinj)
  exact MvPolynomial.ext _ _ (fun d => by rw [hcoeff d, MvPolynomial.coeff_zero])

/-- **Residue-class form.**  Nonintegral exponents in pairwise distinct classes of `ℂ/ℤ` have a
joint algebraically independent continued-Hurwitz shift ladder. -/
theorem continued_joint_hurwitz_ladder_independence_of_integerResidueSeparated
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ι → ℂ} (hnonintegral : ∀ j, ∀ m : ℤ, s j ≠ (m : ℂ))
    (hseparated : ∀ i j, i ≠ j → ∀ m : ℤ, s i - s j ≠ (m : ℂ))
    (N : ℕ) (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ))
    (hrel : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun jk => HurwitzZetaContinuation.continuedHzeta
          (s jk.1 + (jk.2 : ℕ)) a) P = 0) :
    P = 0 := by
  apply continued_joint_hurwitz_ladder_independence_of_monoScalar
    (monoScalar_injective_of_integerDifference s (fun i j hres => ?_))
    (fun j => monoScalar_ne_one_of_nonintegral (hnonintegral j)) N P hrel
  by_contra hij
  obtain ⟨m, hm⟩ := hres
  exact hseparated i j hij m hm

end

end HurwitzJointLadder
