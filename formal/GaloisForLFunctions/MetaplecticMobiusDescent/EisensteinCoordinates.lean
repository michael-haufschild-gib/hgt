/-
Portions adapted from OpenAI’s Eisenstein-coordinate formalization, Apache-2.0.
See LICENSE and NOTICE in this directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.ThePrimaryCubicGaussSumFixesTheSign

/-!
# Eisenstein coordinates, norm, and intrinsic trace

The integral power basis `1,ω` gives unique integer coordinates. Conjugation
and the field norm yield `|a+bω|²=a²-ab+b²` in every complex embedding.
The minimal polynomial gives `Tr(ω)=-1`, hence
`Tr((a+bω)/(1+2ω))=b` for rational coordinates.

Modulo a nonzero rational integer `m`, these coordinates identify the actual
quotient ring as a set with `(ZMod m)²`.
-/

noncomputable section
namespace GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.Coordinates
open GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein
private instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
private theorem hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ K) 3 :=
  IsCyclotomicExtension.zeta_spec 3 ℚ K
private def pb : PowerBasis ℤ O := hζ.integralPowerBasis

private theorem pb_dim : pb.dim = 2 := by
  simp [pb, Nat.totient_prime Nat.prime_three]

private theorem pb_gen : pb.gen = omega := by
  exact hζ.integralPowerBasis_gen

/-- The integral power basis spans every algebraic integer. -/
theorem exists_coordinates (x : O) :
    ∃ a b : ℤ, x = (a : O) + (b : O) * omega := by
  let i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
  let i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩
  let a : ℤ := (pb.basis.repr x) i0
  let b : ℤ := (pb.basis.repr x) i1
  refine ⟨a, b, ?_⟩
  have hsum := pb.basis.sum_repr x
  have huniv : (Finset.univ : Finset (Fin pb.dim)) = {i0, i1} := by
    ext i
    have hi : i.val < 2 := by simpa only [pb_dim] using i.isLt
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases hv with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  rw [huniv] at hsum
  have hne : i0 ≠ i1 := by decide
  have hnot : i0 ∉ ({i1} : Finset (Fin pb.dim)) := by
    simpa only [Finset.mem_singleton] using hne
  rw [Finset.sum_insert hnot, Finset.sum_singleton] at hsum
  simp only [pb.basis_eq_pow] at hsum
  have hi0 : (i0 : ℕ) = 0 := rfl
  have hi1 : (i1 : ℕ) = 1 := rfl
  simpa [a, b, hi0, hi1, pb_gen, smul_eq_mul, mul_comm] using hsum.symm

private def i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
private def i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩

def eval (a b : ℤ) : O := (a : O) + (b : O) * omega

private theorem eval_basis (a b : ℤ) :
    eval a b = a • pb.basis i0 + b • pb.basis i1 := by
  simp [eval, PowerBasis.basis_eq_pow, i0, i1, pb_gen, mul_comm]

/-- Independence of the integral power basis makes coordinates unique. -/
theorem unique_coordinates {a b c d : ℤ}
    (h : eval a b = eval c d) : a = c ∧ b = d := by
  have h0 := congrArg (fun x : O => (pb.basis.repr x) i0) h
  have h1 := congrArg (fun x : O => (pb.basis.repr x) i1) h
  have hne : i0 ≠ i1 := by decide
  rw [eval_basis, eval_basis] at h0 h1
  constructor
  · simpa only [map_add, map_smul, pb.basis.repr_self, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.single_apply, if_pos rfl, if_pos (show True from trivial), if_neg hne.symm,
      smul_eq_mul, mul_one, mul_zero, add_zero] using h0
  · simpa only [map_add, map_smul, pb.basis.repr_self, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.single_apply, if_pos rfl, if_pos (show True from trivial), if_neg hne,
      smul_eq_mul, mul_one, mul_zero, zero_add] using h1

private theorem omega_sq : omega ^ 2 = -omega - 1 := by
  simpa [omega] using IsCyclotomicExtension.Rat.Three.eta_sq hζ

theorem eval_mul (a b c d : ℤ) :
    eval a b * eval c d = eval (a*c-b*d) (a*d+b*c-b*d) := by
  simp only [eval]
  calc
    ((a : O) + (b : O) * omega) * ((c : O) + (d : O) * omega)
      = (a : O) * c + ((a : O) * d + (b : O) * c) * omega +
          ((b : O) * d) * omega ^ 2 := by ring
    _ = ((a*c-b*d : ℤ) : O) + ((a*d+b*c-b*d : ℤ) : O) * omega := by
          rw [omega_sq]
          push_cast
          ring

theorem eval_congr_mod_four {a b c d : ℤ}
    (ha : (a : ZMod 4) = c) (hb : (b : ZMod 4) = d) :
    ∃ z : O, eval a b - eval c d = 4 * z := by
  have ha4 : (4 : ℤ) ∣ a-c := (ZMod.intCast_eq_intCast_iff_dvd_sub c a 4).mp ha.symm
  have hb4 : (4 : ℤ) ∣ b-d := (ZMod.intCast_eq_intCast_iff_dvd_sub d b 4).mp hb.symm
  obtain ⟨u, hu⟩ := ha4
  obtain ⟨v, hv⟩ := hb4
  refine ⟨(u : O) + (v : O) * omega, ?_⟩
  dsimp [eval]
  rw [show a = c + 4*u by omega, show b = d + 4*v by omega]
  push_cast
  ring

private theorem exists_pair (x : O) :
    ∃ p : ℤ × ℤ, eval p.1 p.2 = x := by
  obtain ⟨a, b, h⟩ := exists_coordinates x
  exact ⟨(a, b), h.symm⟩

/-- The unique integer pair representing an Eisenstein integer. -/
def coords (x : O) : ℤ × ℤ := Classical.choose (exists_pair x)

theorem eval_coords (x : O) : eval (coords x).1 (coords x).2 = x :=
  Classical.choose_spec (exists_pair x)

theorem coords_eval (a b : ℤ) : coords (eval a b) = (a, b) := by
  have h := unique_coordinates (eval_coords (eval a b))
  exact Prod.ext h.1 h.2

/-- Integral coordinates identify the Eisenstein lattice with the integer plane. -/
def coordinateEquiv : O ≃ ℤ × ℤ where
  toFun := coords
  invFun z := eval z.1 z.2
  left_inv := eval_coords
  right_inv z := coords_eval z.1 z.2

/-- Multiplication by algebraic conjugation is the positive Eisenstein norm form. -/
theorem eval_mul_conj (a b : ℤ) :
    eval a b * conjO (eval a b) = ((a ^ 2 - a * b + b ^ 2 : ℤ) : O) := by
  have hcube : omega ^ 3 = 1 := omega_primitive.pow_eq_one
  have hsum : omega + omega ^ 2 = -1 := by rw [omega_sq]; ring
  simp only [eval, map_add, map_mul, map_intCast, conjO_omega]
  push_cast
  calc
    ((a : O) + (b : O) * omega) * ((a : O) + (b : O) * omega ^ 2) =
        (a : O) ^ 2 + (a : O) * b * (omega + omega ^ 2) + (b : O) ^ 2 * omega ^ 3 := by ring
    _ = _ := by rw [hcube, hsum]; ring

/-- The integral field norm is the coordinate quadratic form. -/
theorem norm_eval (a b : ℤ) : Algebra.norm ℤ (eval a b) = a ^ 2 - a * b + b ^ 2 := by
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → O))
  rw [norm_int_eq_mul_conjO, eval_mul_conj]

private theorem complex_omega_conj : star (ringComplex omega) = ringComplex omega ^ 2 := by
  let z := ringComplex omega
  have hz3 : z ^ 3 = 1 := by
    change ringComplex omega ^ 3 = 1
    rw [← map_pow, omega_primitive.pow_eq_one, map_one]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hz3
    exact zero_ne_one hz3
  have hznorm : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz3 (by decide)
  apply mul_left_cancel₀ hz0
  calc
    z * star z = 1 := by rw [← starRingEnd_apply, Complex.mul_conj', hznorm]; norm_num
    _ = z * z ^ 2 := by rw [← pow_succ', hz3]

/-- Squared complex modulus agrees with the integral norm form. -/
theorem complex_norm_eval_sq (a b : ℤ) :
    ‖ringComplex (eval a b)‖ ^ 2 = (a : ℝ) ^ 2 - (a : ℝ) * b + (b : ℝ) ^ 2 := by
  have hc : ringComplex (conjO (eval a b)) = star (ringComplex (eval a b)) := by
    simp only [eval, map_add, map_mul, map_intCast, conjO_omega,
      star_add, star_mul, star_intCast, map_pow, complex_omega_conj]
    ring
  have h := congrArg ringComplex (eval_mul_conj a b)
  rw [map_mul, hc, ← starRingEnd_apply, Complex.mul_conj', map_intCast] at h
  exact_mod_cast h

/-- Nonzero Eisenstein integers have strictly positive coordinate norm. -/
theorem coordinate_norm_pos (a b : ℤ) (hc : eval a b ≠ 0) :
    0 < a ^ 2 - a * b + b ^ 2 := by
  have hn : 0 < ‖ringComplex (eval a b)‖ :=
    norm_pos_iff.mpr (fun h => hc (ringComplex_injective (by simpa using h)))
  have hs := sq_pos_of_pos hn
  rw [complex_norm_eval_sq] at hs
  exact_mod_cast hs

private theorem field_finrank : Module.finrank ℚ K = 2 := by
  rw [IsCyclotomicExtension.finrank (n := 3) K
    (Polynomial.cyclotomic.irreducible_rat (by decide))]
  decide

private theorem trace_one : Algebra.trace ℚ K 1 = 2 := by
  have h := Algebra.trace_algebraMap (R := ℚ) (S := K) (1 : ℚ)
  simpa only [map_one, field_finrank, nsmul_eq_mul, Nat.cast_ofNat, mul_one] using h

private theorem trace_omega : Algebra.trace ℚ K (algebraMap O K omega) = -1 := by
  have h := (hζ.powerBasis ℚ).trace_gen_eq_nextCoeff_minpoly
  rw [IsPrimitiveRoot.powerBasis_gen,
    ← Polynomial.cyclotomic_eq_minpoly_rat hζ (by decide)] at h
  have hd : (Polynomial.cyclotomic 3 ℚ).natDegree = 2 := by
    rw [Polynomial.natDegree_cyclotomic]
    decide
  simp only [Polynomial.nextCoeff, hd] at h
  norm_num [Polynomial.cyclotomic_three, Polynomial.coeff_one] at h
  exact h

/-- The field trace on rational Eisenstein coordinates is `2a-b`. -/
theorem trace_rational_coordinates (a b : ℚ) :
    Algebra.trace ℚ K ((a : K) + (b : K) * algebraMap O K omega) = 2 * a - b := by
  have hs (t : ℚ) (x : K) :
      Algebra.trace ℚ K ((t : K) * x) = t * Algebra.trace ℚ K x := by
    simpa [Algebra.smul_def] using (Algebra.trace ℚ K).map_smul t x
  rw [map_add, hs, trace_omega]
  have ha : Algebra.trace ℚ K (a : K) = a * 2 := by
    simpa only [mul_one, trace_one] using hs a 1
  rw [ha]
  ring

/-- Division by the different generator extracts the second coordinate. -/
theorem trace_div_traceLambda (a b : ℚ) :
    Algebra.trace ℚ K
      (((a : K) + (b : K) * algebraMap O K omega) / algebraMap O K traceLambda) = b := by
  let w : K := algebraMap O K omega
  have hrel : w ^ 2 + w + 1 = 0 := by
    have h := congrArg (algebraMap O K) omega_sq
    simp only [map_pow, map_sub, map_neg, map_one] at h
    dsimp [w]
    rw [h]
    ring
  have hd : (1 + 2 * w) ^ 2 = -3 := by linear_combination 4 * hrel
  have hdn : 1 + 2 * w ≠ 0 := by
    intro hz
    rw [hz] at hd
    norm_num at hd
  have heq : ((a : K) + (b : K) * w) / (1 + 2 * w) =
      (((-a + 2 * b) / 3 : ℚ) : K) + (((-2 * a + b) / 3 : ℚ) : K) * w := by
    apply (div_eq_iff hdn).mpr
    push_cast
    field_simp
    linear_combination (4 * (a : K) - 2 * (b : K)) * hrel
  have hden : algebraMap O K traceLambda = 1 + 2 * w := by
    simp only [traceLambda, map_add, map_one, map_mul, map_ofNat, w]
  rw [hden, heq, trace_rational_coordinates]
  ring

/-- Algebraic conjugation sends `(a,b)` to `(a-b,-b)`. -/
theorem conj_eval (a b : ℤ) : conjO (eval a b) = eval (a - b) (-b) := by
  simp only [eval, map_add, map_mul, map_intCast, conjO_omega]
  rw [omega_sq]
  push_cast
  ring

/-- A rational modulus has the square of its rational size as residue cardinality. -/
theorem rational_modulus_card (m : ℕ) :
    Nat.card (O ⧸ Ideal.span {(m : O)}) = m ^ 2 := by
  have hnorm : Algebra.norm ℤ (m : O) = (m : ℤ) ^ 2 := by
    have he : (m : O) = eval (m : ℤ) 0 := by simp only [eval, Int.cast_natCast, Int.cast_zero, zero_mul, add_zero]
    rw [he, norm_eval]
    ring
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    Ideal.absNorm_span_singleton, hnorm]
  simp

private theorem mk_eval_congr_mod (m : ℕ) (a b c d : ℤ)
    (ha : (a : ZMod m) = c) (hb : (b : ZMod m) = d) :
    Ideal.Quotient.mk (Ideal.span {(m : O)})
        (eval a b) =
      Ideal.Quotient.mk (Ideal.span {(m : O)})
        (eval c d) := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  have hda : (m : ℤ) ∣ a - c :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub c a m).mp ha.symm
  have hdb : (m : ℤ) ∣ b - d :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub d b m).mp hb.symm
  obtain ⟨r, hr⟩ := hda
  obtain ⟨s, hs⟩ := hdb
  apply (Ideal.mem_span_singleton).mpr
  refine ⟨eval r s, ?_⟩
  dsimp [eval]
  rw [show a = c + m*r by omega, show b = d + m*s by omega]
  push_cast
  ring

noncomputable def rationalCoordMap (m : ℕ) :
    ZMod m × ZMod m → (O ⧸ Ideal.span {(m : O)}) :=
  fun ab => Ideal.Quotient.mk (Ideal.span {(m : O)})
    (eval (ZMod.cast ab.1) (ZMod.cast ab.2))

theorem rationalCoordMap_surjective (m : ℕ) :
    Function.Surjective (rationalCoordMap m) := by
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, b, hab⟩ := exists_coordinates z
  refine ⟨((a : ZMod m), (b : ZMod m)), ?_⟩
  change Ideal.Quotient.mk (Ideal.span {(m : O)})
      (eval (ZMod.cast (a : ZMod m))
        (ZMod.cast (b : ZMod m))) = _
  rw [hab]
  apply mk_eval_congr_mod
  · exact ZMod.intCast_zmod_cast _
  · exact ZMod.intCast_zmod_cast _

/-- Rational reduction is coordinate reduction in the integral power basis. -/
noncomputable def rationalCoordEquiv (m : ℕ) (hm : m ≠ 0) :
    ZMod m × ZMod m ≃ (O ⧸ Ideal.span {(m : O)}) := by
  letI : NeZero m := ⟨hm⟩
  letI : Finite (O ⧸ Ideal.span {(m : O)}) :=
    (Ideal.span {(m : O)}).finiteQuotientOfFreeOfNeBot
      (fun h => (by exact_mod_cast hm : (m : O) ≠ 0) (Ideal.span_singleton_eq_bot.mp h))
  letI : Fintype (O ⧸ Ideal.span {(m : O)}) := Fintype.ofFinite _
  refine Equiv.ofBijective (rationalCoordMap m) ?_
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · exact rationalCoordMap_surjective m
  · have hq : Fintype.card (O ⧸ Ideal.span {(m : O)}) = m ^ 2 := by
      simpa only [Nat.card_eq_fintype_card] using rational_modulus_card m
    simp [hq, Fintype.card_prod, sq]

end GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.Coordinates

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.Coordinates.coordinateEquiv
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.Coordinates.complex_norm_eval_sq
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.Coordinates.trace_div_traceLambda
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.Coordinates.rationalCoordEquiv
