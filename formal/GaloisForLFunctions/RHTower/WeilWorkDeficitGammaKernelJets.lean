import GaloisForLFunctions.RHTower.WeilWorkDeficitGammaSymbol
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

/-!
# Actual reciprocal-Gamma kernel residues and endpoint derivatives

The literal line-two rational factor is decomposed into its distinct
negative-even and positive-odd poles. Lagrange interpolation proves every
lower boundary cancellation, the first derivative jump `1`, and the next
jump `-(2*N+4)^2/2`. These are derivatives of the actual polynomial and
inverse-power pieces, not an assumed endpoint model. Their analytic
inversion and the WP06 spectral-deficit bound remain separate obligations.
-/

noncomputable section
open Complex Polynomial
open scoped BigOperators
namespace RHTower.WeilWorkDeficitGamma

/-- The actual negative-even and positive-odd poles for order `N + 4`. -/
abbrev PoleIndex (N : ℕ) := Fin (N+3) ⊕ Fin (N+3)

def pole (N : ℕ) : PoleIndex N → ℂ
  | Sum.inl j => -2*(j:ℂ)-2
  | Sum.inr j => 2*(j:ℂ)+3

def residue (N : ℕ) (i : PoleIndex N) : ℂ :=
  pole N i * (pole N i-1) /
    ∏ j ∈ Finset.univ.erase i, (pole N i-pole N j)

/-- Right minus left monomial endpoint jet for the actual rational kernel. -/
def boundaryJet (N k : ℕ) : ℂ :=
  ∑ i : PoleIndex N, residue N i *
    ∏ j ∈ Finset.range k, (pole N i-(j:ℂ)-1)

private theorem pole_injective (N : ℕ) : Function.Injective (pole N) := by
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      congr 1
      apply Fin.ext
      have hr := congrArg Complex.re h
      norm_num [pole] at hr
      exact_mod_cast hr
    | inr j =>
      have hr := congrArg Complex.re h
      norm_num [pole] at hr
      have hi : 0 ≤ (i:ℝ) := Nat.cast_nonneg _
      have hj : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
      linarith
  | inr i =>
    cases j with
    | inl j =>
      have hr := congrArg Complex.re h
      norm_num [pole] at hr
      have hi : 0 ≤ (i:ℝ) := Nat.cast_nonneg _
      have hj : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
      linarith
    | inr j =>
      congr 1
      apply Fin.ext
      have hr := congrArg Complex.re h
      norm_num [pole] at hr
      exact_mod_cast hr

private theorem pole_card (N : ℕ) : Fintype.card (PoleIndex N) = 2*N+6 := by
  simp [PoleIndex]
  omega

private theorem pole_product (N : ℕ) (s : ℂ) :
    ∏ i : PoleIndex N, (s-pole N i) = clearingProduct (N+3) s := by
  rw [Fintype.prod_sum_type]
  simp only [pole]
  change (∏ j : Fin (N+3), (fun k : ℕ => s-(-2*(k:ℂ)-2)) j.val) *
    (∏ j : Fin (N+3), (fun k : ℕ => s-(2*(k:ℂ)+3)) j.val) = _
  rw [Fin.prod_univ_eq_prod_range (fun k : ℕ => s-(-2*(k:ℂ)-2)) (N+3),
    Fin.prod_univ_eq_prod_range (fun k : ℕ => s-(2*(k:ℂ)+3)) (N+3),
    ← Finset.prod_mul_distrib]
  unfold clearingProduct
  apply Finset.prod_congr rfl
  intro j hj
  ring

private theorem two_ne_pole (N : ℕ) (t : ℝ) (i : PoleIndex N) :
    2+(t:ℂ)*I ≠ pole N i := by
  intro h
  have hr := congrArg Complex.re h
  cases i with
  | inl j =>
    norm_num [pole] at hr
    have hj : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
    linarith
  | inr j =>
    norm_num [pole] at hr
    have hj : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
    linarith

/-- Every literal residue denominator is nonzero. -/
theorem residue_denominator_ne_zero (N : ℕ) (i : PoleIndex N) :
    (∏ j ∈ Finset.univ.erase i, (pole N i-pole N j)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1 ((pole_injective N h).symm))

private def jetPolynomial (k : ℕ) : Polynomial ℂ :=
  X*(X-C 1)*Lagrange.nodal (Finset.range k) (fun j => (j:ℂ)+1)

private theorem jetPolynomial_monic (k : ℕ) : (jetPolynomial k).Monic :=
  (monic_X.mul (monic_X_sub_C 1)).mul Lagrange.nodal_monic

private theorem jetPolynomial_degree (k : ℕ) : (jetPolynomial k).natDegree = k+2 := by
  rw [jetPolynomial, (monic_X.mul (monic_X_sub_C 1)).natDegree_mul
    Lagrange.nodal_monic, monic_X.natDegree_mul (monic_X_sub_C 1)]
  simp only [natDegree_X, natDegree_X_sub_C, Lagrange.natDegree_nodal, Finset.card_range]
  omega

private theorem jetPolynomial_eval (k : ℕ) (s : ℂ) :
    (jetPolynomial k).eval s = s*(s-1)*∏ j ∈ Finset.range k, (s-(j:ℂ)-1) := by
  simp only [jetPolynomial, eval_mul, eval_X, eval_sub, eval_C, Lagrange.eval_nodal]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  ring

private theorem boundaryJet_eq_coeff (N k : ℕ) (hk : k ≤ 2*N+3) :
    boundaryJet N k = (jetPolynomial k).coeff (2*N+5) := by
  have hd : (jetPolynomial k).degree < (Finset.univ : Finset (PoleIndex N)).card := by
    apply (natDegree_lt_iff_degree_lt (jetPolynomial_monic k).ne_zero).mp
    rw [Finset.card_univ, pole_card, jetPolynomial_degree]
    omega
  have h := Lagrange.coeff_eq_sum (pole_injective N).injOn hd
  rw [Finset.card_univ, pole_card] at h
  have hn : 2*N+6-1 = 2*N+5 := by omega
  rw [hn] at h
  rw [h, boundaryJet]
  apply Finset.sum_congr rfl
  intro i hi
  rw [jetPolynomial_eval, residue]
  ring

/-- Every lower endpoint jet cancels, at the exact order needed for C23. -/
theorem boundaryJet_lower (N : ℕ) (k : Fin (2*N+3)) :
    boundaryJet N k = 0 := by
  rw [boundaryJet_eq_coeff N k (Nat.le_of_lt k.isLt)]
  apply coeff_eq_zero_of_natDegree_lt
  rw [jetPolynomial_degree]
  have := k.isLt
  omega

/-- The first surviving endpoint jet is exactly one, at every Gamma order. -/
theorem boundaryJet_first (N : ℕ) : boundaryJet N (2*N+3) = 1 := by
  rw [boundaryJet_eq_coeff N _ le_rfl]
  have hd : (jetPolynomial (2*N+3)).natDegree = 2*N+5 := by
    rw [jetPolynomial_degree]
  rw [← hd]
  exact (jetPolynomial_monic _).coeff_natDegree

private theorem rationalSymbol_of_ne (N : ℕ) (s : ℂ)
    (hs : ∀ i : PoleIndex N, s ≠ pole N i) :
    s*(s-1)/clearingProduct (N+3) s =
      ∑ i : PoleIndex N, residue N i/(s-pole N i) := by
  let P : Polynomial ℂ := X*(X-C 1)
  have hdeg : P.degree < (Finset.univ : Finset (PoleIndex N)).card := by
    apply (natDegree_lt_iff_degree_lt (monic_X.mul (monic_X_sub_C 1)).ne_zero).mp
    have hp : P.natDegree = 2 := by
      dsimp [P]
      rw [monic_X.natDegree_mul (monic_X_sub_C 1)]
      simp only [natDegree_X, natDegree_X_sub_C]
    rw [Finset.card_univ, pole_card, hp]
    omega
  have hP := Lagrange.eq_interpolate (pole_injective N).injOn hdeg
  have he := congrArg (fun p : Polynomial ℂ => p.eval s) hP
  rw [Lagrange.eval_interpolate_not_at_node _ (fun i _ => hs i),
    Lagrange.eval_nodal, pole_product] at he
  simp only [P, eval_mul, eval_X, eval_sub, eval_C] at he
  have hprod : clearingProduct (N+3) s ≠ 0 := by
    rw [← pole_product]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (hs i))
  rw [he, mul_div_cancel_left₀ _ hprod]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Lagrange.nodalWeight, Finset.prod_inv_distrib, residue, div_eq_mul_inv]
  ring


/-- Partial fractions throughout the literal kernel's pole-free Mellin strip. -/
theorem rationalSymbol_strip (N : ℕ)
    (s : {s : ℂ // -2 < s.re ∧ s.re < 3}) :
    (s:ℂ)*((s:ℂ)-1)/clearingProduct (N+3) s =
      ∑ i : PoleIndex N, residue N i/((s:ℂ)-pole N i) := by
  apply rationalSymbol_of_ne
  intro i hi
  have hr := congrArg Complex.re hi
  cases i with
  | inl j =>
    have hj : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
    norm_num [pole] at hr
    linarith [s.property.1]
  | inr j =>
    have hj : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
    norm_num [pole] at hr
    linarith [s.property.2]

/-- The actual rational factor in the line-two Mellin symbol has these residues. -/
theorem rationalSymbol_two (N : ℕ) (t : ℝ) :
    (2+(t:ℂ)*I)*(1+(t:ℂ)*I)/clearingProduct (N+3) (2+(t:ℂ)*I) =
      ∑ i : PoleIndex N, residue N i/(2+(t:ℂ)*I-pole N i) := by
  have h := rationalSymbol_of_ne N (2+(t:ℂ)*I) (two_ne_pole N t)
  convert h using 1; ring

/-- Polynomial piece of the literal cosine kernel, extended for endpoint differentiation. -/
def kernelInner (N : ℕ) (z : ℂ) : ℂ :=
  -∑ j : Fin (N+3), residue N (Sum.inr j)*z^((2*(j:ℤ)+2):ℤ)

/-- Inverse-power piece of the literal cosine kernel. -/
def kernelOuter (N : ℕ) (z : ℂ) : ℂ :=
  ∑ j : Fin (N+3), residue N (Sum.inl j)*z^((-2*(j:ℤ)-3):ℤ)

private theorem zpow_jet_one (m : ℤ) (k : ℕ) :
    iteratedDeriv k (fun z : ℂ => z^m) 1 =
      ∏ j ∈ Finset.range k, ((m:ℂ)-(j:ℂ)) := by
  simpa only [iteratedDerivWithin_univ, one_zpow, mul_one] using
    iteratedDerivWithin_zpow (𝕜 := ℂ) (s := Set.univ) m k isOpen_univ (Set.mem_univ 1)

private theorem finite_zpow_jet (N k : ℕ) (c : Fin (N+3) → ℂ)
    (m : Fin (N+3) → ℤ) :
    iteratedDeriv k (fun z : ℂ => ∑ j, c j*z^(m j)) 1 =
      ∑ j, c j * ∏ l ∈ Finset.range k, ((m j:ℂ)-(l:ℂ)) := by
  have hc : ∀ j ∈ (Finset.univ : Finset (Fin (N+3))),
      ContDiffAt ℂ k (fun z : ℂ => c j*z^(m j)) 1 := by
    intro j hj
    apply contDiffAt_const.mul
    exact (AnalyticAt.fun_zpow (𝕜 := ℂ) (f := fun z : ℂ => z) (z := (1:ℂ))
      (n := m j) (by fun_prop) (by norm_num)).contDiffAt
  rw [iteratedDeriv_fun_sum hc]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedDeriv_const_mul_field, zpow_jet_one]

/-- Algebraic endpoint jets are the actual derivatives of both kernel pieces. -/
theorem kernel_endpoint_jump (N k : ℕ) :
    iteratedDeriv k (kernelOuter N) 1 - iteratedDeriv k (kernelInner N) 1 =
      boundaryJet N k := by
  unfold kernelOuter kernelInner
  rw [iteratedDeriv_fun_neg, finite_zpow_jet, finite_zpow_jet, sub_neg_eq_add]
  unfold boundaryJet
  rw [Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    congr 1
    apply Finset.prod_congr rfl
    intro l hl
    simp only [pole, Int.cast_sub, Int.cast_mul, Int.cast_neg, Int.cast_ofNat,
      Int.cast_natCast]
    ring
  · apply Finset.sum_congr rfl
    intro j hj
    congr 1
    apply Finset.prod_congr rfl
    intro l hl
    simp only [pole, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    ring

/-- Both literal kernel pieces match in every derivative below the first jump. -/
theorem kernel_endpoint_match (N : ℕ) (k : Fin (2*N+3)) :
    iteratedDeriv k (kernelOuter N) 1 = iteratedDeriv k (kernelInner N) 1 := by
  apply sub_eq_zero.mp
  rw [kernel_endpoint_jump, boundaryJet_lower]

/-- The literal first derivative jump responsible for the integer resonance is one. -/
theorem kernel_endpoint_first (N : ℕ) :
    iteratedDeriv (2*N+3) (kernelOuter N) 1 -
      iteratedDeriv (2*N+3) (kernelInner N) 1 = 1 := by
  rw [kernel_endpoint_jump, boundaryJet_first]


private theorem jetPolynomial_nextCoeff (k : ℕ) :
    (jetPolynomial k).nextCoeff = -(1+(k:ℂ)*((k:ℂ)+1)/2) := by
  induction k with
  | zero =>
    simp only [jetPolynomial, Lagrange.nodal_eq, Finset.range_zero, Finset.prod_empty,
      mul_one, Nat.cast_zero, zero_mul, zero_div, add_zero]
    rw [monic_X.nextCoeff_mul (monic_X_sub_C 1), nextCoeff_X_sub_C]
    simp [Polynomial.nextCoeff]
  | succ k ih =>
    have h : jetPolynomial (k+1) = jetPolynomial k * (X-C ((k:ℂ)+1)) := by
      simp only [jetPolynomial, Lagrange.nodal_eq, Finset.prod_range_succ]
      ring
    rw [h, (jetPolynomial_monic k).nextCoeff_mul (monic_X_sub_C _), ih,
      nextCoeff_X_sub_C]
    push_cast
    ring

private theorem polePolynomial_nextCoeff (N : ℕ) :
    (Lagrange.nodal Finset.univ (pole N)).nextCoeff = -((N:ℂ)+3) := by
  rw [Lagrange.nodal_eq, Monic.nextCoeff_prod _ _ (fun i _ => monic_X_sub_C (pole N i))]
  simp only [nextCoeff_X_sub_C, Finset.sum_neg_distrib]
  congr 1
  rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  have h : (∑ j : Fin (N+3), (pole N (Sum.inl j)+pole N (Sum.inr j))) =
      ∑ _j : Fin (N+3), (1:ℂ) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [pole]
    ring
  rw [h]
  simp

/-- The next literal boundary coefficient grows quadratically with the decay order. -/
theorem boundaryJet_next (N : ℕ) :
    boundaryJet N (2*N+4) = -((2*(N:ℂ)+4)^2)/2 := by
  let P := jetPolynomial (2*N+4)
  let D := Lagrange.nodal Finset.univ (pole N)
  have hPm : P.Monic := jetPolynomial_monic _
  have hDm : D.Monic := Lagrange.nodal_monic
  have hPn : P.natDegree = 2*N+6 := by dsimp [P]; rw [jetPolynomial_degree]
  have hDn : D.natDegree = 2*N+6 := by
    dsimp [D]
    rw [Lagrange.natDegree_nodal, Finset.card_univ, pole_card]
  have hPd : P.degree = (2*N+6:ℕ) := (degree_eq_natDegree hPm.ne_zero).trans (by rw [hPn])
  have hDd : D.degree = (2*N+6:ℕ) := (degree_eq_natDegree hDm.ne_zero).trans (by rw [hDn])
  have hlt : (P-D).degree < (Finset.univ : Finset (PoleIndex N)).card := by
    rw [Finset.card_univ, pole_card, ← hPd]
    exact degree_sub_lt (hPd.trans hDd.symm) hPm.ne_zero (hPm.trans hDm.symm)
  have hc := Lagrange.coeff_eq_sum (pole_injective N).injOn hlt
  rw [Finset.card_univ, pole_card, show 2*N+6-1 = 2*N+5 by omega] at hc
  have hjet : boundaryJet N (2*N+4) = (P-D).coeff (2*N+5) := by
    rw [hc, boundaryJet]
    apply Finset.sum_congr rfl
    intro i hi
    rw [eval_sub, show D.eval (pole N i) = 0 from Lagrange.eval_nodal_at_node (Finset.mem_univ i),
      sub_zero]
    dsimp [P]
    rw [jetPolynomial_eval, residue]
    ring
  have hpnext : P.coeff (2*N+5) = P.nextCoeff := by
    rw [nextCoeff_of_natDegree_pos (by rw [hPn]; omega), hPn, show 2*N+6-1 = 2*N+5 by omega]
  have hdnext : D.coeff (2*N+5) = D.nextCoeff := by
    rw [nextCoeff_of_natDegree_pos (by rw [hDn]; omega), hDn, show 2*N+6-1 = 2*N+5 by omega]
  rw [hjet, coeff_sub, hpnext, hdnext]
  dsimp [P, D]
  rw [jetPolynomial_nextCoeff, polePolynomial_nextCoeff]
  push_cast
  ring

/-- The next derivative jump of the actual kernel retains the full order dependence. -/
theorem kernel_endpoint_next (N : ℕ) :
    iteratedDeriv (2*N+4) (kernelOuter N) 1 -
      iteratedDeriv (2*N+4) (kernelInner N) 1 = -((2*(N:ℂ)+4)^2)/2 := by
  rw [kernel_endpoint_jump, boundaryJet_next]

end RHTower.WeilWorkDeficitGamma
