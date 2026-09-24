import GaloisForLFunctions.RHTower.WeilKloostermanLFunction

/-!
# Hasse–Davenport relation for Kloosterman sums

For a finite extension `E/F` of degree `n`, grouping `x ∈ E` by minimal polynomial
(each monic irreducible `P` of degree `d ∣ n` has exactly `d` roots in `E`, `card_minpoly_fiber`),
using `Tr_{E/F}(x) = (n/d)(-nextCoeff P)` and `minpoly(x⁻¹) = P(0)⁻¹ X^d P(1/X)` (`minpoly_inv`),
gives `ψ(Tr(x + a/x)) = λ(P)^{n/d}` and hence `K_E(a) = c_n` (`extKloosterman_eq_klPower`).
With the L-function computation this is the Hasse–Davenport relation `K_E(a) = -(αⁿ + βⁿ)`,
`α + β = -K(a)`, `αβ = q` (`hasseDavenport`): step 3 of the elementary proof of Weil's bound.
-/

open Polynomial Finset IntermediateField

namespace GaloisForLFunctions.RHTower.WeilKloosterman

attribute [local instance] Classical.propDecidable

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

omit [Fintype F] in
/-- An irreducible polynomial whose degree divides `[E:F]` has a root in `E`. -/
theorem exists_root_of_dvd [Finite F] {P : F[X]} (hP : Irreducible P) (hd : P.natDegree ∣ Module.finrank F E) :
    ∃ x : E, aeval x P = 0 := by
  haveI : Fact (Irreducible P) := ⟨hP⟩
  have hne : P ≠ 0 := hP.ne_zero
  have hK : Module.finrank F (AdjoinRoot P) = P.natDegree :=
    (AdjoinRoot.powerBasis hne).finrank.trans (AdjoinRoot.powerBasis_dim hne)
  haveI : Module.Finite F (AdjoinRoot P) := (AdjoinRoot.powerBasis hne).finite
  haveI : Finite (AdjoinRoot P) := Module.finite_of_finite F
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (K := AdjoinRoot P) (L := E) (F := F)
    (hK ▸ hd)
  refine ⟨φ (AdjoinRoot.root P), ?_⟩
  rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]

omit [Fintype F] [Fintype E] in
theorem minpoly_eq_iff_root {P : F[X]} (hPm : P.Monic) (hP : Irreducible P) (x : E) :
    minpoly F x = P ↔ aeval x P = 0 := by
  constructor
  · rintro rfl; exact minpoly.aeval F x
  · intro hx; exact (minpoly.eq_of_irreducible_of_monic hP hx hPm).symm

/-- Fibre sizes of the minimal-polynomial map `E → F[X]`. -/
theorem card_minpoly_fiber {P : F[X]} (hPm : P.Monic) (hP : Irreducible P) :
    (univ.filter (fun x : E => minpoly F x = P)).card =
      if P.natDegree ∣ Module.finrank F E then P.natDegree else 0 := by
  split_ifs with hd
  · obtain ⟨x0, hx0⟩ := exists_root_of_dvd (E := E) hP hd
    have hmin : minpoly F x0 = P := (minpoly_eq_iff_root hPm hP x0).mpr hx0
    have hsplit : (P.map (algebraMap F E)).Splits := by
      rw [← hmin]; exact Normal.splits (IsGalois.to_normal) x0
    have hsep : P.Separable := PerfectField.separable_of_irreducible hP
    have hcard := card_rootSet_eq_natDegree (K := E) hsep hsplit
    rw [← hcard, ← Set.toFinset_card]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
      mem_rootSet_of_ne hP.ne_zero, minpoly_eq_iff_root hPm hP]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    apply hd
    rw [← hx]
    exact minpoly.degree_dvd (IsIntegral.of_finite F x)

/-- Normalized reverse `P(0)⁻¹ · X^{deg P} P(1/X)`. -/
noncomputable def revNorm (P : F[X]) : F[X] := C (P.coeff 0)⁻¹ * P.reverse

omit [Fintype F] in
theorem reverse_natDegree_of_coeff_zero {P : F[X]} (h0 : P.coeff 0 ≠ 0) :
    P.reverse.natDegree = P.natDegree := by
  rw [reverse_natDegree, natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (by simpa using h0),
    Nat.sub_zero]

omit [Fintype F] in
theorem revNorm_monic {P : F[X]} (h0 : P.coeff 0 ≠ 0) : (revNorm P).Monic := by
  unfold revNorm
  rw [Monic, leadingCoeff_mul, leadingCoeff_C, reverse_leadingCoeff,
    trailingCoeff_eq_coeff_zero h0, inv_mul_cancel₀ h0]

omit [Fintype F] in
theorem revNorm_natDegree {P : F[X]} (h0 : P.coeff 0 ≠ 0) :
    (revNorm P).natDegree = P.natDegree := by
  unfold revNorm
  rw [natDegree_C_mul (inv_ne_zero h0), reverse_natDegree_of_coeff_zero h0]

omit [Fintype F] [Fintype E] in
theorem aeval_inv_revNorm {P : F[X]} {x : E} (hx : x ≠ 0) (hP : aeval x P = 0) :
    aeval x⁻¹ (revNorm P) = 0 := by
  letI : Invertible x := invertibleOfNonzero hx
  unfold revNorm
  rw [map_mul, aeval_C, mul_eq_zero]
  right
  rw [aeval_def] at hP ⊢
  have := (eval₂_reverse_eq_zero_iff (algebraMap F E) x P).mpr hP
  simpa [invOf_eq_inv] using this

omit [Fintype F] in
theorem revNorm_nextCoeff {P : F[X]} (h0 : P.coeff 0 ≠ 0) (hd : 1 ≤ P.natDegree) :
    (revNorm P).nextCoeff = P.coeff 1 / P.coeff 0 := by
  rw [nextCoeff, revNorm_natDegree h0, if_neg (by omega)]
  unfold revNorm
  rw [coeff_C_mul, coeff_reverse, revAt_le (by omega)]
  rw [show P.natDegree - (P.natDegree - 1) = 1 by omega, div_eq_inv_mul]

omit [Fintype F] in
/-- The minimal polynomial of `x⁻¹` is the normalized reverse of that of `x`. -/
theorem minpoly_inv {x : E} (hx : x ≠ 0) : minpoly F x⁻¹ = revNorm (minpoly F x) := by
  have hi : ∀ y : E, IsIntegral F y := fun y => IsIntegral.of_finite F y
  have h0x := minpoly.coeff_zero_ne_zero (hi x) hx
  have h0y := minpoly.coeff_zero_ne_zero (hi x⁻¹) (inv_ne_zero hx)
  have hdvd1 : minpoly F x⁻¹ ∣ revNorm (minpoly F x) :=
    minpoly.dvd F x⁻¹ (aeval_inv_revNorm hx (minpoly.aeval F x))
  have hdvd2 : minpoly F x ∣ revNorm (minpoly F x⁻¹) := by
    apply minpoly.dvd F x
    have := aeval_inv_revNorm (inv_ne_zero hx) (minpoly.aeval F x⁻¹)
    rwa [inv_inv] at this
  have hle : (minpoly F x).natDegree ≤ (minpoly F x⁻¹).natDegree := by
    rw [← revNorm_natDegree h0y]
    exact natDegree_le_of_dvd hdvd2 (revNorm_monic h0y).ne_zero
  exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (hi x⁻¹)) (revNorm_monic h0x) hdvd1
    (by rw [revNorm_natDegree h0x]; exact hle)).symm

omit [Fintype F] in
/-- `[E : F⟮x⟯] = [E:F] / deg minpoly(x)`. -/
theorem finrank_adjoin_top (x : E) :
    Module.finrank F⟮x⟯ E = Module.finrank F E / (minpoly F x).natDegree := by
  have hi : IsIntegral F x := IsIntegral.of_finite F x
  have h := Module.finrank_mul_finrank F F⟮x⟯ E
  rw [IntermediateField.adjoin.finrank hi] at h
  have hpos : 0 < (minpoly F x).natDegree := minpoly.natDegree_pos hi
  rw [← h, Nat.mul_div_cancel_left _ hpos]

omit [Fintype F] in
theorem trace_eq_nsmul (x : E) :
    Algebra.trace F E x =
      (Module.finrank F E / (minpoly F x).natDegree) • (-(minpoly F x).nextCoeff) := by
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, finrank_adjoin_top, nsmul_eq_mul]

variable (ψ : AddChar F ℂ) (a : F)

omit [Fintype F] in
/-- **Trace formula.** For `x ≠ 0`, `ψ(Tr(x + a/x)) = λ(minpoly x)^{[E:F]/deg}`. -/
theorem addChar_trace_eq_klW_pow {x : E} (hx : x ≠ 0) :
    ψ (Algebra.trace F E (x + algebraMap F E a * x⁻¹)) =
      klW ψ a (minpoly F x) ^ (Module.finrank F E / (minpoly F x).natDegree) := by
  have hi : IsIntegral F x := IsIntegral.of_finite F x
  set P := minpoly F x
  have h0 : P.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hi hx
  have hd : 1 ≤ P.natDegree := minpoly.natDegree_pos hi
  have hdinv : (minpoly F x⁻¹).natDegree = P.natDegree := by
    rw [minpoly_inv hx, revNorm_natDegree h0]
  have hT1 := trace_eq_nsmul (F := F) x
  have hT2 := trace_eq_nsmul (F := F) x⁻¹
  rw [hdinv, minpoly_inv hx, revNorm_nextCoeff h0 hd] at hT2
  rw [map_add, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, hT1, hT2]
  set k := Module.finrank F E / P.natDegree
  have hsum : (k • (-P.nextCoeff) + a * (k • (-(P.coeff 1 / P.coeff 0)))) =
      k • (-P.nextCoeff - a * (P.coeff 1 / P.coeff 0)) := by
    simp only [nsmul_eq_mul]; ring
  rw [hsum, AddChar.map_nsmul_eq_pow]
  simp only [klW, if_neg h0]

/-- The Kloosterman sum over the extension `E`, with the character `ψ ∘ Tr_{E/F}`. -/
noncomputable def extKloosterman : ℂ :=
  ∑ x : E, if x = 0 then 0 else ψ (Algebra.trace F E (x + algebraMap F E a * x⁻¹))

/-- **Hasse–Davenport link.** The Kloosterman sum over `E` is the power sum `c_n`, `n = [E:F]`. -/
theorem extKloosterman_eq_klPower :
    extKloosterman (E := E) ψ a = klPower ψ a (Module.finrank F E) := by
  set n := Module.finrank F E
  have hn : 0 < n := Module.finrank_pos
  set G : F[X] → ℂ := fun P => klW ψ a P ^ (n / P.natDegree)
  have hpt : ∀ x : E, (if x = 0 then 0 else ψ (Algebra.trace F E (x + algebraMap F E a * x⁻¹))) =
      G (minpoly F x) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      rw [if_pos rfl, minpoly.zero]
      simp only [G, klW, coeff_X_zero, if_true, natDegree_X, Nat.div_one]
      rw [zero_pow hn.ne']
    · rw [if_neg hx, addChar_trace_eq_klW_pow ψ a hx]
  unfold extKloosterman
  simp_rw [hpt]
  set t : Finset F[X] := n.divisors.biUnion (irrDeg (F := F))
  have hmaps : ∀ x ∈ (univ : Finset E), minpoly F x ∈ t := by
    intro x _
    have hi : IsIntegral F x := IsIntegral.of_finite F x
    rw [Finset.mem_biUnion]
    refine ⟨(minpoly F x).natDegree, ?_, mem_irrDeg.mpr ⟨minpoly.monic hi, rfl, minpoly.irreducible hi⟩⟩
    rw [Nat.mem_divisors]
    exact ⟨minpoly.degree_dvd hi, hn.ne'⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ P ∈ t, (∑ x ∈ univ.filter (fun x : E => minpoly F x = P), G (minpoly F x)) =
      (P.natDegree : ℂ) * klW ψ a P ^ (n / P.natDegree) := by
    intro P hP
    rw [Finset.mem_biUnion] at hP
    obtain ⟨d, hd, hPd⟩ := hP
    rw [mem_irrDeg] at hPd
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
      Finset.sum_const, card_minpoly_fiber hPd.1 hPd.2.2, hPd.2.1,
      if_pos (Nat.dvd_of_mem_divisors hd), nsmul_eq_mul]
    simp only [G, hPd.2.1]
  rw [Finset.sum_congr rfl hfib, Finset.sum_biUnion]
  · unfold klPower powerSumW
    refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun P hP => ?_))
    rw [(mem_irrDeg.mp hP).2.1]
  · intro d _ e _ hde
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro P hPd hPe
    rw [mem_irrDeg] at hPd hPe
    exact hde (hPd.2.1.symm.trans hPe.2.1)

omit [Fintype E] [Algebra F E] in
/-- **Hasse–Davenport relation for Kloosterman sums.** There are `α, β ∈ ℂ` with
`α + β = -K(a)`, `αβ = q`, such that for every finite extension `E/F` of degree `n`,
`K_E(a) = -(αⁿ + βⁿ)`. -/
theorem hasseDavenport (hψ : ψ.IsPrimitive) (ha : a ≠ 0) :
    ∃ α β : ℂ, α + β = -kloosterman ψ a ∧ α * β = (Fintype.card F : ℂ) ∧
      ∀ (E : Type*) [Field E] [Fintype E] [Algebra F E],
        extKloosterman (E := E) ψ a = -(α ^ Module.finrank F E + β ^ Module.finrank F E) := by
  obtain ⟨α, β, hs, hp, hc⟩ := klPower_closed_form ψ a hψ ha
  refine ⟨α, β, hs, hp, fun E _ _ _ => ?_⟩
  rw [extKloosterman_eq_klPower, hc _ Module.finrank_pos]

end GaloisForLFunctions.RHTower.WeilKloosterman
