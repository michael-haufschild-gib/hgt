import GaloisForLFunctions.RHTower.WeilKloostermanHasseDavenport

/-!
# The L-function of a hyperelliptic character sum: extensions

For `f ∈ F[X]` and the quadratic character `χ` of a finite field `F` of odd characteristic, the
weight `w(P) = χ(Res(P, f))` is multiplicative on monic polynomials (`hypW_mul`). When `f` splits
over `F`, its power sums are the character sums over every finite extension:

* **norms** (`quadraticChar_norm`): `χ_E(y) = χ_F(N_{E/F} y)`, from Euler's criterion and
  `N_{E/F} y = y^{(|E|−1)/(|F|−1)}`;
* **the norm of `f(x)`** (`norm_aeval_eq_resultant_pow`): `N_{E/F}(f(x)) = Res(P, f)^{n/d}` for
  `P = minpoly x` of degree `d` and `n = [E : F]`, from `N(x − α) = ((−1)^d P(α))^{n/d}` and
  `Res(P, f) = (−1)^{dm} c^d Π_i P(α_i)` for `f = c Π_i (X − α_i)`;
* **the Hasse–Davenport link** (`extHyp_eq_powerSumW`): grouping `x ∈ E` by minimal polynomial,
  `Σ_{x ∈ E} χ_E(f(x)) = c_n = Σ_{d ∣ n} Σ_{P irreducible, deg P = d} d · w(P)^{n/d}`.
-/

open Polynomial Finset IntermediateField

namespace GaloisForLFunctions.RHTower.Hyperelliptic

open WeilKloosterman

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F]

/-- The weight `w(P) = χ(Res(P, f))`. -/
noncomputable def hypW (f P : F[X]) : ℂ := ((quadraticChar F (resultant P f) : ℤ) : ℂ)

theorem hypW_mul (f : F[X]) {P Q : F[X]} (hP : P.Monic) (hQ : Q.Monic) :
    hypW f (P * Q) = hypW f P * hypW f Q := by
  have h := resultant_mul_left P Q f f.natDegree le_rfl
  rw [← hP.natDegree_mul hQ] at h
  unfold hypW
  rw [h, map_mul]
  push_cast
  ring

theorem hypW_one (f : F[X]) : hypW f 1 = 1 := by
  unfold hypW
  rw [show resultant (1 : F[X]) f = 1 by
    rw [← C_1, resultant, natDegree_C]
    simp]
  simp

variable {E : Type*} [Field E] [Fintype E] [Algebra F E]

omit [Fintype E] in
/-- Integers in `{−1, 0, 1}` with equal images in a field of characteristic `≠ 2` are equal. -/
theorem quadraticChar_values_eq (hE : ringChar E ≠ 2) {a b : ℤ}
    (ha : a = 0 ∨ a = 1 ∨ a = -1) (hb : b = 0 ∨ b = 1 ∨ b = -1) (h : (a : E) = (b : E)) :
    a = b := by
  have h1 := Ring.neg_one_ne_one_of_char_ne_two hE
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first
    | rfl
    | (exfalso; push_cast at h
       first
       | exact one_ne_zero h
       | exact one_ne_zero h.symm
       | exact neg_ne_zero.mpr one_ne_zero h
       | exact neg_ne_zero.mpr one_ne_zero h.symm
       | exact h1 h
       | exact h1 h.symm)

theorem quadraticChar_trichotomy (K : Type*) [Field K] [Fintype K] [DecidableEq K] (y : K) :
    quadraticChar K y = 0 ∨ quadraticChar K y = 1 ∨ quadraticChar K y = -1 := by
  by_cases hy : y = 0
  · left; rw [hy, quadraticChar_zero]
  · right; exact quadraticChar_dichotomy hy

/-- **Quadratic characters and norms**: `χ_E(y) = χ_F(N_{E/F} y)`. -/
theorem quadraticChar_norm (hF : ringChar F ≠ 2) (y : E) :
    quadraticChar E y = quadraticChar F (Algebra.norm F y) := by
  have hE : ringChar E ≠ 2 := by rwa [← Algebra.ringChar_eq F E]
  set q := Fintype.card F
  set n := Module.finrank F E
  have hQ : Fintype.card E = q ^ n := Module.card_eq_pow_finrank
  have hqodd := FiniteField.odd_card_of_char_ne_two hF
  have hq1 : 1 < q := Fintype.one_lt_card
  obtain ⟨a, ha⟩ : q - 1 ∣ Fintype.card E - 1 := by
    rw [hQ]; simpa using Nat.sub_dvd_pow_sub_pow q 1 n
  have hEodd : Fintype.card E % 2 = 1 := FiniteField.odd_card_of_char_ne_two hE
  have hpow : (quadraticChar E y : E) =
      algebraMap F E (quadraticChar F (Algebra.norm F y) : F) := by
    rw [quadraticChar_eq_pow_of_char_ne_two' hE, quadraticChar_eq_pow_of_char_ne_two' hF,
      map_pow, FiniteField.algebraMap_norm_eq_pow, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, ← pow_mul]
    congr 1
    rw [ha, Nat.mul_div_cancel_left _ (by omega)]
    have h2 : Fintype.card F - 1 = 2 * (Fintype.card F / 2) := by omega
    have h3 : Fintype.card E - 1 = 2 * (a * (Fintype.card F / 2)) := by rw [ha, h2]; ring
    have hEpos : 0 < Fintype.card E := Fintype.card_pos
    omega
  rw [map_intCast] at hpow
  exact quadraticChar_values_eq hE (quadraticChar_trichotomy E y)
    (quadraticChar_trichotomy F _) hpow

omit [Fintype F] in
/-- `N_{E/F}(x − α) = ((−1)^d P(α))^{n/d}` for `P = minpoly x` of degree `d`. -/
theorem norm_sub_algebraMap (x : E) (α : F) :
    Algebra.norm F (x - algebraMap F E α) =
      ((-1) ^ (minpoly F x).natDegree * (minpoly F x).eval α) ^
        (Module.finrank F E / (minpoly F x).natDegree) := by
  set y := x - algebraMap F E α
  have hy : IsIntegral F y := .of_finite F y
  have hx : IsIntegral F x := .of_finite F x
  have hmin : minpoly F y = (minpoly F x).comp (X + C α) := minpoly.sub_algebraMap x α
  have hdeg : (minpoly F y).natDegree = (minpoly F x).natDegree := by
    rw [hmin, natDegree_comp]; simp
  rw [Algebra.norm_eq_norm_adjoin F y]
  have hgen : Algebra.norm F (AdjoinSimple.gen F y) =
      (-1) ^ (minpoly F y).natDegree * (minpoly F y).coeff 0 := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (adjoin.powerBasis hy)
    simpa [adjoin.powerBasis, minpoly_gen] using this
  have hcoeff : (minpoly F y).coeff 0 = (minpoly F x).eval α := by
    rw [hmin, coeff_zero_eq_eval_zero, eval_comp]; simp
  have hfin : Module.finrank F⟮y⟯ E = Module.finrank F E / (minpoly F x).natDegree := by
    rw [← Module.finrank_mul_finrank F F⟮y⟯ E, adjoin.finrank hy, hdeg,
      Nat.mul_div_cancel_left _ (minpoly.natDegree_pos hx)]
  rw [hgen, hcoeff, hdeg, hfin]

omit [Fintype F] in
/-- **The norm of `f(x)`** for split `f`: `N_{E/F}(f(x)) = Res(minpoly x, f)^{n/d}`. -/
theorem norm_aeval_eq_resultant_pow {f : F[X]} (hsplit : f.Splits) (x : E) :
    Algebra.norm F (aeval x f) =
      resultant (minpoly F x) f ^ (Module.finrank F E / (minpoly F x).natDegree) := by
  set P := minpoly F x
  set d := P.natDegree
  set n := Module.finrank F E
  have hx : IsIntegral F x := .of_finite F x
  have hdn : d ∣ n := minpoly.degree_dvd hx
  have hroots : Multiset.card f.roots = f.natDegree := splits_iff_card_roots.mp hsplit
  have hf := C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  have hres : resultant P f = (-1) ^ (d * f.natDegree) *
      (f.leadingCoeff ^ d * (f.roots.map P.eval).prod) := by
    rw [resultant_comm, resultant_eq_prod_eval f P d le_rfl hsplit]
  conv_lhs => rw [← hf]
  rw [map_mul, aeval_C, map_mul, Algebra.norm_algebraMap, map_multiset_prod, Multiset.map_map,
    map_multiset_prod, Multiset.map_map]
  have hterm : ∀ α : F, (Algebra.norm F ∘ aeval x ∘ fun a => X - C a) α =
      ((-1) ^ d * P.eval α) ^ (n / d) := by
    intro α
    simp only [Function.comp, map_sub, aeval_X, aeval_C]
    exact norm_sub_algebraMap x α
  rw [Multiset.map_congr rfl fun α _ => hterm α, Multiset.prod_map_pow, Multiset.prod_map_mul,
    Multiset.map_const', Multiset.prod_replicate, hroots, hres]
  obtain ⟨k, hk⟩ := hdn
  have hk' : Module.finrank F E = d * k := hk
  have hd : 0 < d := minpoly.natDegree_pos hx
  rw [hk', show n = d * k from hk, Nat.mul_div_cancel_left k hd]
  ring

/-- **The point-wise link**: `χ_E(f(x)) = w(minpoly x)^{n/d}`. -/
theorem quadraticChar_aeval_eq (hF : ringChar F ≠ 2) {f : F[X]} (hsplit : f.Splits) (x : E) :
    ((quadraticChar E (aeval x f) : ℤ) : ℂ) =
      hypW f (minpoly F x) ^ (Module.finrank F E / (minpoly F x).natDegree) := by
  rw [quadraticChar_norm hF, norm_aeval_eq_resultant_pow hsplit, map_pow, hypW]
  push_cast
  rfl

/-- The character sum `Σ_{x ∈ E} χ_E(f(x))` over a finite extension. -/
noncomputable def extHyp (f : F[X]) : ℂ := ∑ x : E, ((quadraticChar E (aeval x f) : ℤ) : ℂ)

/-- **Hasse–Davenport link**: the character sum over `E` is the power sum `c_n`, `n = [E : F]`. -/
theorem extHyp_eq_powerSumW (hF : ringChar F ≠ 2) {f : F[X]} (hsplit : f.Splits) :
    extHyp (E := E) f = powerSumW (hypW f) (Module.finrank F E) := by
  set n := Module.finrank F E
  have hn : 0 < n := Module.finrank_pos
  set G : F[X] → ℂ := fun P => hypW f P ^ (n / P.natDegree)
  unfold extHyp
  simp_rw [quadraticChar_aeval_eq hF hsplit]
  set t : Finset F[X] := n.divisors.biUnion (irrDeg (F := F))
  have hmaps : ∀ x ∈ (univ : Finset E), minpoly F x ∈ t := by
    intro x _
    have hi : IsIntegral F x := IsIntegral.of_finite F x
    rw [Finset.mem_biUnion]
    refine ⟨(minpoly F x).natDegree, ?_,
      mem_irrDeg.mpr ⟨minpoly.monic hi, rfl, minpoly.irreducible hi⟩⟩
    rw [Nat.mem_divisors]
    exact ⟨minpoly.degree_dvd hi, hn.ne'⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ P ∈ t, (∑ x ∈ univ.filter (fun x : E => minpoly F x = P),
      hypW f (minpoly F x) ^ (n / (minpoly F x).natDegree)) =
      (P.natDegree : ℂ) * hypW f P ^ (n / P.natDegree) := by
    intro P hP
    rw [Finset.mem_biUnion] at hP
    obtain ⟨d, hd, hPd⟩ := hP
    rw [mem_irrDeg] at hPd
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
      Finset.sum_const, card_minpoly_fiber hPd.1 hPd.2.2, hPd.2.1,
      if_pos (Nat.dvd_of_mem_divisors hd), nsmul_eq_mul]
  rw [Finset.sum_congr rfl hfib, Finset.sum_biUnion]
  · unfold powerSumW
    refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun P hP => ?_))
    rw [(mem_irrDeg.mp hP).2.1]
  · intro d _ e _ hde
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro P hPd hPe
    rw [mem_irrDeg] at hPd hPe
    exact hde (hPd.2.1.symm.trans hPe.2.1)

end GaloisForLFunctions.RHTower.Hyperelliptic
