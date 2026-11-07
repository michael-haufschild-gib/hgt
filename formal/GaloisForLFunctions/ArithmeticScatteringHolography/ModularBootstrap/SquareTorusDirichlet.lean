import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.ScalarChargeCoordinates

/-!
# The scalar Dirichlet series of the square two-torus

Orthogonal momentum and winding charges separate into a primitive direction
and a positive winding scale. Absolute convergence permits this reindexing.
The zero-winding sector cancels the axis removed by the positive-scale choice,
leaving the square of the Epstein series divided by twice `ζ(2s)`.
-/

open Complex RHTower RHTower.HeckeFactorization

namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

noncomputable section

/-- Nonvacuum scalar charges, including zero winding. -/
abbrev NonzeroScalarCharge := {q : (ℤ × ℤ) × (ℤ × ℤ) //
  q.1.1 * q.2.1 + q.1.2 * q.2.2 = 0 ∧ q ≠ ((0, 0), (0, 0))}

/-- Squared momentum plus squared winding. -/
def scalarNorm (q : (ℤ × ℤ) × (ℤ × ℤ)) : ℕ := latNorm q.1 + latNorm q.2

/-- Scalar Dirichlet term, with the vacuum omitted from its domain. -/
def scalarDirichletTerm (s : ℂ) (q : NonzeroScalarCharge) : ℂ :=
  (scalarNorm q.val : ℂ) ^ (-s)

private def primitiveTerm (s : ℂ) (a : D4BMPrimitiveIntegerPair) : ℂ :=
  (latNorm a.pair : ℂ) ^ (-s)

private def halfPlaneTerm (s : ℂ) (t : ℕ × ℤ) : ℂ :=
  (latNorm ((t.1 : ℤ) + 1, t.2) : ℂ) ^ (-s)

private def puncturedTerm (s : ℂ) : ℤ × ℤ → ℂ :=
  {p | p ≠ (0, 0)}.indicator (fun p => (latNorm p : ℂ) ^ (-s))

private theorem summable_puncturedTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (puncturedTerm s) :=
  summable_subtype_iff_indicator.mp (summable_latTerm hs)

private theorem tsum_puncturedTerm (s : ℂ) :
    ∑' p, puncturedTerm s p = ∑' p, latTerm s p := by
  exact (tsum_subtype {p : ℤ × ℤ | p ≠ (0, 0)}
    (fun p => (latNorm p : ℂ) ^ (-s))).symm

private theorem summable_primitiveTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (primitiveTerm s) := by
  let f : D4BMPrimitiveIntegerPair → {p : ℤ × ℤ // p ≠ (0, 0)} :=
    fun a => ⟨a.pair, a.pair_ne_zero⟩
  exact (summable_latTerm hs).comp_injective
    (i := f) (fun a b h => primExt (congrArg Subtype.val h))

private theorem summable_halfPlaneTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (halfPlaneTerm s) := by
  let f : ℕ × ℤ → {p : ℤ × ℤ // p ≠ (0, 0)} := fun t =>
    ⟨((t.1 : ℤ) + 1, t.2), by intro h; have := congrArg Prod.fst h; dsimp at this; omega⟩
  exact (summable_latTerm hs).comp_injective (i := f) (by
    intro a b h
    have h₁ := congrArg (fun p => p.val.1) h
    have h₂ := congrArg (fun p => p.val.2) h
    exact Prod.ext (by dsimp [f] at h₁; omega) h₂)

private theorem puncturedTerm_neg_fst (s : ℂ) (c d : ℤ) :
    puncturedTerm s (-c, d) = puncturedTerm s (c, d) := by
  simp [puncturedTerm, Set.indicator_apply, latNorm, Prod.mk.injEq]

private theorem puncturedTerm_axis_neg (s : ℂ) (d : ℤ) :
    puncturedTerm s (0, -d) = puncturedTerm s (0, d) := by
  simp [puncturedTerm, Set.indicator_apply, latNorm, Prod.mk.injEq]

private theorem puncturedTerm_pos (s : ℂ) (k : ℕ) (d : ℤ) :
    puncturedTerm s ((k : ℤ) + 1, d) = halfPlaneTerm s (k, d) := by
  have h : ((k : ℤ) + 1, d) ≠ (0, 0) := by
    intro h; have := congrArg Prod.fst h; dsimp at this; omega
  simp only [puncturedTerm, Set.indicator_apply, Set.mem_setOf_eq, if_pos h, halfPlaneTerm]

private theorem puncturedTerm_axis_pos (s : ℂ) (k : ℕ) :
    puncturedTerm s (0, (k : ℤ) + 1) = 1 / ((k : ℂ) + 1) ^ (2 * s) := by
  have h : ((0 : ℤ), (k : ℤ) + 1) ≠ (0, 0) := by
    intro h; have := congrArg Prod.snd h; dsimp at this; omega
  have hn : latNorm (0, (k : ℤ) + 1) = (k + 1) ^ 2 := by
    apply Int.ofNat_inj.mp
    rw [latNorm_cast]
    push_cast
    ring
  simp only [puncturedTerm, Set.indicator_apply, Set.mem_setOf_eq, if_pos h,
    hn, natCast_sq_cpow_neg]

/-- Positive and negative winding scales contribute equally; the omitted axis
is twice the ordinary Dirichlet series of `ζ(2s)`. -/
private theorem lattice_halfPlane_split {s : ℂ} (hs : 1 < s.re) :
    ∑' p, latTerm s p =
      2 * (∑' t, halfPlaneTerm s t) + 2 * riemannZeta (2 * s) := by
  have h := summable_puncturedTerm hs
  have ha : Summable (fun d : ℤ => puncturedTerm s (0, d)) := h.prod_factor 0
  have hap : Summable (fun k : ℕ => puncturedTerm s (0, (k : ℤ) + 1)) :=
    ha.comp_injective (fun a b h => by omega)
  have han : Summable (fun k : ℕ => puncturedTerm s (0, -((k : ℤ) + 1))) :=
    ha.comp_injective (fun a b h => by omega)
  have haxis : ∑' d : ℤ, puncturedTerm s (0, d) = 2 * riemannZeta (2 * s) := by
    rw [tsum_of_add_one_of_neg_add_one
      (f := fun d : ℤ => puncturedTerm s (0, d)) hap han]
    simp only [puncturedTerm_axis_neg, puncturedTerm_axis_pos]
    rw [← zeta_eq_tsum_one_div_nat_add_one_cpow (by simp; linarith)]
    simp [puncturedTerm]
    ring
  have hr : Summable (fun c : ℤ => ∑' d : ℤ, puncturedTerm s (c, d)) := h.prod
  have hp : Summable (fun k : ℕ => ∑' d : ℤ, puncturedTerm s ((k : ℤ) + 1, d)) :=
    hr.comp_injective (fun a b h => by omega)
  have hn : Summable (fun k : ℕ => ∑' d : ℤ, puncturedTerm s (-((k : ℤ) + 1), d)) :=
    hr.comp_injective (fun a b h => by omega)
  rw [← tsum_puncturedTerm, h.tsum_prod, tsum_of_add_one_of_neg_add_one
    (f := fun c : ℤ => ∑' d : ℤ, puncturedTerm s (c, d)) hp hn]
  simp only [puncturedTerm_neg_fst, puncturedTerm_pos]
  rw [haxis, ← (summable_halfPlaneTerm hs).tsum_prod]
  ring

/-- Separate zero winding from the uniquely parametrized nonzero-winding sector. -/
def windingSplit :
    {p : ℤ × ℤ // p ≠ (0, 0)} ⊕ ScalarCharge ≃ NonzeroScalarCharge where
  toFun := Sum.elim
    (fun p => ⟨(p.val, (0, 0)), by simp, by
      intro h; exact p.property (congrArg Prod.fst h)⟩)
    (fun q => ⟨q.val, q.property.1, by
      intro h; exact q.property.2 (congrArg Prod.snd h)⟩)
  invFun q := if hw : q.val.2 = (0, 0) then
    Sum.inl ⟨q.val.1, by
      intro h; exact q.property.2 (Prod.ext h hw)⟩
    else Sum.inr ⟨q.val, q.property.1, hw⟩
  left_inv q := by
    cases q with
    | inl p => simp
    | inr q => simp [q.property.2]
  right_inv q := by
    dsimp
    split_ifs with hw
    · exact Subtype.ext (Prod.ext rfl hw.symm)
    · rfl

private def chargeParameterEquiv : (ℕ × ℤ) × D4BMPrimitiveIntegerPair ≃ ScalarCharge :=
  (show (ℕ × ℤ) × D4BMPrimitiveIntegerPair ≃ (ℕ × D4BMPrimitiveIntegerPair) × ℤ from
    { toFun := fun t => ((t.1.1, t.2), t.1.2)
      invFun := fun t => ((t.1.1, t.2), t.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans scalarChargeEquiv

private theorem scalarNorm_parameters (k : ℕ) (a : D4BMPrimitiveIntegerPair) (d : ℤ) :
    scalarNorm (scalarParameters k a d) = latNorm ((k : ℤ) + 1, d) * latNorm a.pair := by
  apply Int.ofNat_inj.mp
  simp only [scalarNorm, Nat.cast_add, Nat.cast_mul, latNorm_cast]
  simpa only [add_assoc] using scalarParameters_energy k a d

private theorem chargeTerm_parameters (s : ℂ) (t : (ℕ × ℤ) × D4BMPrimitiveIntegerPair) :
    (scalarNorm (chargeParameterEquiv t).val : ℂ) ^ (-s) =
      halfPlaneTerm s t.1 * primitiveTerm s t.2 := by
  change (scalarNorm (scalarParameters t.1.1 t.2 t.1.2) : ℂ) ^ (-s) = _
  rw [scalarNorm_parameters, Nat.cast_mul, natCast_mul_natCast_cpow]
  rfl

private theorem summable_windingTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (fun q : ScalarCharge => (scalarNorm q.val : ℂ) ^ (-s)) := by
  apply chargeParameterEquiv.summable_iff.mp
  simp only [Function.comp_def, chargeTerm_parameters]
  exact summable_mul_of_summable_norm
    (summable_halfPlaneTerm hs).norm (summable_primitiveTerm hs).norm

private theorem windingTerm_sum {s : ℂ} (hs : 1 < s.re) :
    ∑' q : ScalarCharge, (scalarNorm q.val : ℂ) ^ (-s) =
      (∑' t, halfPlaneTerm s t) * ∑' a, primitiveTerm s a := by
  rw [← chargeParameterEquiv.tsum_eq
    (fun q : ScalarCharge => (scalarNorm q.val : ℂ) ^ (-s))]
  simp only [chargeTerm_parameters]
  exact (tsum_mul_tsum_of_summable_norm
    (summable_halfPlaneTerm hs).norm (summable_primitiveTerm hs).norm).symm

private theorem zeroWindingTerm_eq (s : ℂ) (p : {p : ℤ × ℤ // p ≠ (0, 0)}) :
    scalarDirichletTerm s (windingSplit (Sum.inl p)) = latTerm s p := by
  change ((latNorm p.val + latNorm (0, 0) : ℕ) : ℂ) ^ (-s) =
    (latNorm p.val : ℂ) ^ (-s)
  rw [show latNorm (0, 0) = 0 from rfl, Nat.add_zero]

private theorem summable_zeroWindingTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p => scalarDirichletTerm s (windingSplit (Sum.inl p))) :=
  (summable_latTerm hs).congr (fun p => (zeroWindingTerm_eq s p).symm)

/-- The scalar Dirichlet series converges absolutely on `Re s > 1`. -/
theorem summable_scalarDirichletTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (scalarDirichletTerm s) := by
  apply windingSplit.summable_iff.mp
  exact Summable.sum (scalarDirichletTerm s ∘ windingSplit)
    (summable_zeroWindingTerm hs) (summable_windingTerm hs)

private theorem scalarDirichlet_zero_winding_split {s : ℂ} (hs : 1 < s.re) :
    ∑' q, scalarDirichletTerm s q = (∑' p, latTerm s p) +
      (∑' t, halfPlaneTerm s t) * ∑' a, primitiveTerm s a := by
  rw [← windingSplit.tsum_eq (scalarDirichletTerm s)]
  have hsum := Summable.tsum_sum (f := scalarDirichletTerm s ∘ windingSplit)
    (summable_zeroWindingTerm hs) (summable_windingTerm hs)
  change (∑' q, (scalarDirichletTerm s ∘ windingSplit) q) = _
  rw [hsum]
  simp only [Function.comp_apply, zeroWindingTerm_eq]
  exact congrArg ((∑' p, latTerm s p) + ·) (windingTerm_sum hs)

/-- The square-torus scalar charge series is the square of the Epstein series
with precisely one zeta factor removed. -/
theorem scalarDirichlet_eq_lattice_square {s : ℂ} (hs : 1 < s.re) :
    ∑' q, scalarDirichletTerm s q = (∑' p, latTerm s p) ^ 2 /
      (2 * riemannZeta (2 * s)) := by
  have hg := latticeSum_eq_zeta_mul_primitive hs
  change (∑' p, latTerm s p) = riemannZeta (2 * s) * ∑' a, primitiveTerm s a at hg
  have hh := lattice_halfPlane_split hs
  have hz : riemannZeta (2 * s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  rw [scalarDirichlet_zero_winding_split hs]
  apply (eq_div_iff (mul_ne_zero (by norm_num) hz)).mpr
  linear_combination (2 * riemannZeta (2 * s) - (∑' p, latTerm s p)) * hg -
    riemannZeta (2 * s) * (∑' a, primitiveTerm s a) * hh

/-- The scalar charge sum has the normalization `2ζ(2s)E(i,s)²`. -/
theorem scalarDirichlet_eq_eisenstein_square {s : ℂ} (hs : 1 < s.re) :
    ∑' q, scalarDirichletTerm s q = 2 * riemannZeta (2 * s) *
      d4BMRawEisensteinPoincareSeries zI ⟨s, hs⟩ ^ 2 := by
  have hz : riemannZeta (2 * s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  rw [scalarDirichlet_eq_lattice_square hs, latticeSum_eq_zeta_mul_primitive hs,
    d4BMRawEisensteinPoincareSeries]
  simp_rw [seed_zI]
  field_simp

end

end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.summable_scalarDirichletTerm
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.scalarDirichlet_eq_lattice_square
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.scalarDirichlet_eq_eisenstein_square
