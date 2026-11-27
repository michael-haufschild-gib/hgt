import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

/-! The coefficient of the identity after multiplication by a character
idempotent is a normalized trace. Its real part is nonnegative on idempotents. -/

noncomputable section
open Polynomial
open scoped Classical

namespace GlobalTheory.GLq

variable {G : Type} [Group G] [Fintype G]

/-- The coefficient at a group element is proportional to the character at its inverse. -/
theorem zOf_coeff (χ : G → ℂ) (x : G) :
    (zOf χ).coeff x = χ 1 / (Fintype.card G : ℂ) * χ x⁻¹ := by
  simp only [zOf, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
    Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Evaluation at the identity pairs a group algebra element with the character. -/
theorem coeff_one_mul_zOf (a : MonoidAlgebra ℂ G) (χ : G → ℂ) :
    (a * zOf χ).coeff 1 = χ 1 / (Fintype.card G : ℂ) * tr a χ := by
  have h : a = ∑ x : G, MonoidAlgebra.single x (a.coeff x) := by
    ext y
    simp [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single]
  conv_lhs => rw [h]
  rw [Finset.sum_mul, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, tr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [MonoidAlgebra.coeff_single_mul_apply, mul_one, zOf_coeff, inv_inv]
  ring

private theorem trace_asAlgebraHom (V : FDRep ℂ G) (a : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ V (Representation.asAlgebraHom (V.ρ : Representation ℂ G V) a) =
      tr a V.character := by
  simp only [tr, Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, FDRep.character]
  rw [Finsupp.sum_fintype _ _ (by simp), map_sum]
  simp

/-- The trace of an idempotent on a genuine representation is the dimension of its image. -/
theorem tr_eq_nat_of_idempotent (a : MonoidAlgebra ℂ G) (ha : a * a = a)
    {χ : G → ℂ} (hχ : IsChar χ) : ∃ m : ℕ, tr a χ = m := by
  obtain ⟨V, hV⟩ := hχ
  let A := Representation.asAlgebraHom (V.ρ : Representation ℂ G V)
  have hproj : IsIdempotentElem (A a) := by
    rw [IsIdempotentElem, ← map_mul, ha]
  rw [← funext hV, ← trace_asAlgebraHom]
  exact ⟨_, (LinearMap.IsIdempotentElem.isProj_range _ hproj).trace⟩

omit [Fintype G] in
/-- The degree of an irreducible character is a positive natural number. -/
theorem irr_degree_pos {χ : G → ℂ} (hχ : IsIrr χ) : ∃ d : ℕ, 0 < d ∧ χ 1 = d := by
  obtain ⟨V, hV, hval⟩ := hχ
  refine ⟨Module.finrank ℂ V, Nat.pos_of_ne_zero fun h => ?_, by rw [← hval, FDRep.char_one]⟩
  letI : CategoryTheory.Simple V := hV
  apply CategoryTheory.Simple.not_isZero V
  rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
  letI : Subsingleton V := Module.finrank_zero_iff.mp h
  ext x
  exact Subsingleton.elim _ _

private theorem re_coeff_one_mul_zOf_nonneg (a : MonoidAlgebra ℂ G) (ha : a * a = a)
    {χ : G → ℂ} (hχ : IsIrr χ) : 0 ≤ ((a * zOf χ).coeff 1).re := by
  obtain ⟨d, _, hd⟩ := irr_degree_pos hχ
  obtain ⟨V, _, hV⟩ := hχ
  obtain ⟨m, hm⟩ := tr_eq_nat_of_idempotent a ha ⟨V, hV⟩
  rw [coeff_one_mul_zOf, hd, hm,
    ← Complex.ofReal_natCast d, ← Complex.ofReal_natCast (Fintype.card G),
    ← Complex.ofReal_natCast m, ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_re]
  positivity

/-- A Harish–Chandra series has nonnegative weight in an idempotent average. -/
theorem wtC_nonneg_of_idempotent {g n : ℕ} [Fact g.Prime] (L : LabelDatum g)
    (a : MonoidAlgebra ℂ (Gn g n)) (ha : a * a = a) (h1 : 0 ≤ (a.coeff 1).re)
    (f : (ZMod g)[X]) : 0 ≤ wtC L a f := by
  refine div_nonneg ?_ h1
  unfold eSerC
  refine finsum_mem_induction (fun b => 0 ≤ ((a * b).coeff 1).re) (by simp) ?_ ?_
  · intro b c hb hc
    rw [mul_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, Complex.add_re]
    exact add_nonneg hb hc
  · exact fun χ hχ => re_coeff_one_mul_zOf_nonneg a ha (show IsIrr χ from hχ.1)

/-- A trace inequality on each irreducible character gives the corresponding
inequality on series weights after division by the two identity coefficients. -/
theorem wtC_le_of_trace_comparison {g n : ℕ} [Fact g.Prime] (L : LabelDatum g)
    (a b : MonoidAlgebra ℂ (Gn g n)) (f : (ZMod g)[X]) (r : ℝ)
    (ha : 0 < (a.coeff 1).re) (hb : 0 < (b.coeff 1).re)
    (htr : ∀ χ, IsIrr χ → r * (tr a χ).re ≤ (tr b χ).re) :
    (r * (a.coeff 1).re / (b.coeff 1).re) * wtC L a f ≤ wtC L b f := by
  have hn : r * ((a * eSerC L n f).coeff 1).re ≤ ((b * eSerC L n f).coeff 1).re := by
    unfold eSerC
    refine finsum_mem_induction
      (fun c => r * ((a * c).coeff 1).re ≤ ((b * c).coeff 1).re) (by simp) ?_ ?_
    · intro c d hc hd
      simp only [mul_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, Complex.add_re]
      exact add_le_add hc hd
    · intro χ hχ
      obtain ⟨d, -, hd⟩ := irr_degree_pos (show IsIrr χ from hχ.1)
      let c : ℝ := (d : ℝ) / (Fintype.card (Gn g n) : ℝ)
      have hcast : χ 1 / (Fintype.card (Gn g n) : ℂ) = Complex.ofReal c := by
        dsimp only [c]
        rw [hd, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast]
      rw [coeff_one_mul_zOf, coeff_one_mul_zOf, hcast, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
        mul_left_comm]
      exact mul_le_mul_of_nonneg_left (htr χ hχ.1) (by positivity)
  rw [wtC, wtC, le_div_iff₀ hb]
  calc
    _ = r * ((a * eSerC L n f).coeff 1).re := by field_simp [ha.ne', hb.ne']
    _ ≤ _ := hn

end GlobalTheory.GLq
