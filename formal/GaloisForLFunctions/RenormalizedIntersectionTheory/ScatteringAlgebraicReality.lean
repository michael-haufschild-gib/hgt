import GaloisForLFunctions.HTGeometry.TwoVariableResultantBridge
import GaloisForLFunctions.Bottcher.RelativeTranscendenceBridge
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.RatFunc.Basic
import GaloisForLFunctions.RHTower.SelbergScatteringPolynomialReality

/-!
# Algebraic scattering transport has two incompatible reality loci

Write a plane polynomial with the transport value as inner variable and the native Casimir
as outer variable. An irreducible correspondence with infinitely many real values both on
`3/16 + t²/4 + it/4` and on the native interval `(1/4, ∞)` is a real horizontal line.

The quadratic Casimir cover has a two-element deck group. Norm descent restricts its factors
to one deck orbit. Two parallel reality lines then force a factor to be invariant under a
nonzero translation, hence independent of the cover coordinate. The spectral edge is sharp:
`(4z - 3/4 - w)² + w = 0` is irreducible, contains every critical Casimir with `w = t²`,
and has real values over real `z` exactly on `(-∞, 1/4]`.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ScatteringAlgebraicReality

/-- Localization and the resultant bound intersections of distinct irreducible plane curves. -/
private theorem finite_first_coords_of_not_associated
    {f g : (ℂ[X])[X]} (hf : Irreducible f) (hg : Irreducible g)
    (hne : ¬ Associated f g) :
    {x : ℂ | ∃ y : ℂ, evalPairHom x y f = 0 ∧ evalPairHom x y g = 0}.Finite := by
  by_cases hd : f.natDegree = 0
  · have he : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hd
    have h0 : f.coeff 0 ≠ 0 := by
      intro h
      apply hf.ne_zero
      rw [he, h, map_zero]
    refine (Polynomial.finite_setOf_isRoot h0).subset ?_
    rintro x ⟨y, hfy, _⟩
    rw [he, evalPairHom_C] at hfy
    exact hfy
  · let E := FractionRing ℂ[X]
    let ι := algebraMap ℂ[X] E
    have hι : Function.Injective ι := IsFractionRing.injective _ _
    have hp := hf.isPrimitive hd
    have hfE : Irreducible (f.map ι) :=
      hp.irreducible_iff_irreducible_map_fraction_map.mp hf
    have hres : f.resultant g ≠ 0 := by
      intro hzero
      have he := congrArg ι hzero
      rw [← Polynomial.resultant_map_map, map_zero] at he
      rw [← Polynomial.natDegree_map_eq_of_injective hι (p := f),
        ← Polynomial.natDegree_map_eq_of_injective hι (p := g)] at he
      have hnot := (Polynomial.resultant_eq_zero_iff.mp he).2
      rcases EuclideanDomain.dvd_or_coprime (f.map ι) (g.map ι) hfE with hdiv | hcop
      · exact hne (hf.associated_of_dvd hg (hp.dvd_of_fraction_map_dvd_fraction_map hdiv))
      · exact hnot hcop
    exact finite_first_coords le_rfl le_rfl (Or.inl hd) hres

private def quadraticRelation (z w : ℂ) : ℂ := (4 * z - 3 / 4 - w) ^ 2 + w

private theorem quadraticRelation_critical (t : ℝ) :
    quadraticRelation (_root_.RHTower.SelbergScatteringPolynomialReality.criticalCasimir t)
      ((t : ℂ) ^ 2) = 0 := by
  have he : 4 * _root_.RHTower.SelbergScatteringPolynomialReality.criticalCasimir (t : ℂ)
      - 3 / 4 - (t : ℂ) ^ 2 = Complex.I * t := by
    simp only [_root_.RHTower.SelbergScatteringPolynomialReality.criticalCasimir]
    ring
  rw [quadraticRelation, he, mul_pow, Complex.I_sq]
  ring

private theorem quadraticRelation_real_iff (x : ℝ) :
    (∃ y : ℝ, quadraticRelation (x : ℂ) y = 0) ↔ x ≤ 1 / 4 := by
  have he (y : ℝ) : quadraticRelation (x : ℂ) y =
      (((y - 4 * x + 5 / 4) ^ 2 + 4 * x - 1 : ℝ) : ℂ) := by
    unfold quadraticRelation
    push_cast
    ring
  constructor
  · rintro ⟨y, hy⟩
    rw [he, Complex.ofReal_eq_zero] at hy
    nlinarith only [sq_nonneg (y - 4 * x + 5 / 4), hy]
  · intro hx
    have hnonneg : 0 ≤ 1 - 4 * x := by linarith only [hx]
    refine ⟨4 * x - 5 / 4 + Real.sqrt (1 - 4 * x), ?_⟩
    rw [he, Complex.ofReal_eq_zero]
    have hs := Real.sq_sqrt hnonneg
    nlinarith only [hs]

/-- The deck norm is even after centering, so it descends through the square map. -/
private theorem exists_quadratic_norm_descent (P : (ℂ[X])[X]) (c : ℂ[X]) :
    ∃ Q : (ℂ[X])[X], P * P.comp (C (2 * c) - X) = Q.comp ((X - C c) ^ 2) := by
  have hd : (C (2 * c) - X).comp (C (2 * c) - X) = X := by
    simp only [sub_comp, C_comp, X_comp]
    ring
  apply Bottcher.exists_comp_square_of_comp_reflection_eq_self c
  rw [mul_comp, comp_assoc, hd, comp_X]
  exact mul_comm _ _

private def quadraticCasimirCover : (ℂ[X])[X] :=
  C (C (1 / 4)) * ((X - C (C (-Complex.I / 2))) ^ 2 + 1)

private theorem exists_casimir_norm_descent (P : (ℂ[X])[X]) :
    ∃ Q : (ℂ[X])[X], P * P.comp (C (2 * C (-Complex.I / 2)) - X) =
      Q.comp quadraticCasimirCover := by
  obtain ⟨Q, hQ⟩ := exists_quadratic_norm_descent P (C (-Complex.I / 2))
  refine ⟨Q.comp (C (C (4 : ℂ)) * X - 1), ?_⟩
  rw [hQ, comp_assoc]
  congr 1
  simp only [sub_comp, mul_comp, C_comp, X_comp, one_comp]
  have hfour : (C (C (4 : ℂ)) : (ℂ[X])[X]) * C (C (1 / 4)) = 1 := by
    rw [← C_mul, ← C_mul]
    norm_num
  rw [quadraticCasimirCover, ← mul_assoc, hfour, one_mul, add_sub_cancel_right]

private theorem quadraticCasimirCover_coeff_two :
    quadraticCasimirCover.coeff 2 = C (1 / 4 : ℂ) := by
  norm_num [quadraticCasimirCover, pow_two, mul_sub, sub_mul, mul_add]

private theorem casimir_comp_injective :
    Function.Injective (fun P : (ℂ[X])[X] => P.comp quadraticCasimirCover) := by
  intro P Q h
  change P.comp quadraticCasimirCover = Q.comp quadraticCasimirCover at h
  have hz : (P - Q).comp quadraticCasimirCover = 0 := by
    rw [sub_comp, h, sub_self]
  rcases Polynomial.comp_eq_zero_iff.mp hz with hz | ⟨_, hconst⟩
  · exact sub_eq_zero.mp hz
  · have h2 := congrArg (fun P : (ℂ[X])[X] => P.coeff 2) hconst
    rw [quadraticCasimirCover_coeff_two] at h2
    norm_num at h2

private theorem quadraticCasimirCover_reflection :
    quadraticCasimirCover.comp (C (2 * C (-Complex.I / 2)) - X) =
      quadraticCasimirCover := by
  have hcenter : (C (2 * C (-Complex.I / 2)) : (ℂ[X])[X]) =
      2 * C (C (-Complex.I / 2)) := by simp only [map_mul, map_ofNat]
  have hs : (C (2 * C (-Complex.I / 2)) - X - C (C (-Complex.I / 2))) ^ 2 =
      ((X : (ℂ[X])[X]) - C (C (-Complex.I / 2))) ^ 2 := by
    rw [hcenter]
    ring
  simp only [quadraticCasimirCover, mul_comp, C_comp, add_comp, pow_comp,
    sub_comp, X_comp, one_comp]
  rw [hs]

private theorem quadratic_norm_factorization (F G R H J : (ℂ[X])[X])
    (hFR : F.comp quadraticCasimirCover = G * R)
    (hH : G * G.comp (C (2 * C (-Complex.I / 2)) - X) = H.comp quadraticCasimirCover)
    (hJ : R * R.comp (C (2 * C (-Complex.I / 2)) - X) = J.comp quadraticCasimirCover) :
    H * J = F ^ 2 := by
  apply casimir_comp_injective
  change (H * J).comp quadraticCasimirCover = (F ^ 2).comp quadraticCasimirCover
  rw [mul_comp, pow_comp, ← hH, ← hJ]
  have he : (G * R).comp (C (2 * C (-Complex.I / 2)) - X) = G * R := by
    rw [← hFR, comp_assoc, quadraticCasimirCover_reflection]
  calc (G * G.comp (C (2 * C (-Complex.I / 2)) - X)) *
        (R * R.comp (C (2 * C (-Complex.I / 2)) - X))
      = (G * R) * (G * R).comp (C (2 * C (-Complex.I / 2)) - X) := by
        rw [mul_comp]
        ring
    _ = (F.comp quadraticCasimirCover) ^ 2 := by rw [he, ← hFR, pow_two]

private theorem swapVars_involutive (P : (ℂ[X])[X]) :
    Bottcher.swapVars (Bottcher.swapVars P) = P := by
  have h := congrArg (fun f => f P) (Bottcher.swapVars_comp_swapVars (K := ℂ))
  exact h

private def swapEquiv : (ℂ[X])[X] ≃+* (ℂ[X])[X] where
  toFun := Bottcher.swapVars
  invFun := Bottcher.swapVars
  left_inv := swapVars_involutive
  right_inv := swapVars_involutive
  map_mul' P Q := map_mul (Bottcher.swapVars (K := ℂ)) P Q
  map_add' P Q := map_add (Bottcher.swapVars (K := ℂ)) P Q

private theorem eval_swap (x y : ℂ) (P : (ℂ[X])[X]) :
    evalPairHom x y (swapEquiv P) = evalPairHom y x P := by
  change Bottcher.evalHom y x (Bottcher.swapVars P) = Bottcher.evalHom x y P
  exact congrArg (fun f => f P) (Bottcher.evalHom_comp_swapVars (K := ℂ) y x)

private theorem finite_second_coords_of_not_associated
    {f g : (ℂ[X])[X]} (hf : Irreducible f) (hg : Irreducible g)
    (hne : ¬ Associated f g) :
    {x : ℂ | ∃ y : ℂ, evalPairHom y x f = 0 ∧ evalPairHom y x g = 0}.Finite := by
  have hf' := (MulEquiv.irreducible_iff swapEquiv).mpr hf
  have hg' := (MulEquiv.irreducible_iff swapEquiv).mpr hg
  have hne' : ¬ Associated (swapEquiv f) (swapEquiv g) := by
    intro h
    apply hne
    simpa using Associated.map swapEquiv.symm h
  have h := finite_first_coords_of_not_associated hf' hg' hne'
  simpa only [eval_swap] using h

/-- The descended norms multiply to F²; primality leaves only one deck orbit of factors. -/
private theorem casimir_factor_orbit {F G R : (ℂ[X])[X]}
    (hF : Irreducible F) (hG : ¬ IsUnit G)
    (hFR : F.comp quadraticCasimirCover = G * R) :
    Associated (F.comp quadraticCasimirCover) G ∨
      Associated (F.comp quadraticCasimirCover)
        (G * G.comp (C (2 * C (-Complex.I / 2)) - X)) := by
  obtain ⟨H, hH⟩ := exists_casimir_norm_descent G
  obtain ⟨J, hJ⟩ := exists_casimir_norm_descent R
  have hHJ := quadratic_norm_factorization F G R H J hFR hH hJ
  have hHnu : ¬ IsUnit H := by
    intro hu
    have hu' := hu.map (Polynomial.compRingHom quadraticCasimirCover)
    change IsUnit (H.comp quadraticCasimirCover) at hu'
    rw [← hH] at hu'
    exact hG (isUnit_of_mul_isUnit_left hu')
  have hHd : H ∣ F ^ 2 := ⟨J, hHJ.symm⟩
  obtain ⟨k, hk, hAssoc⟩ := (dvd_prime_pow hF.prime 2).mp hHd
  interval_cases k
  · exact (hHnu (associated_one_iff_isUnit.mp (by simpa using hAssoc))).elim
  · right
    have hmap := Associated.map (Polynomial.compRingHom quadraticCasimirCover) hAssoc
    change Associated (H.comp quadraticCasimirCover) ((F ^ 1).comp quadraticCasimirCover)
      at hmap
    simpa only [pow_one, ← hH] using hmap.symm
  · left
    obtain ⟨u, hu⟩ := hAssoc
    have hH0 : H ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hHJ
      exact pow_ne_zero 2 hF.ne_zero hHJ.symm
    have hJu : J = (u : (ℂ[X])[X]) :=
      mul_left_cancel₀ hH0 (hHJ.trans hu.symm)
    have hJu' : IsUnit J := by rw [hJu]; exact u.isUnit
    have hprod := hJu'.map (Polynomial.compRingHom quadraticCasimirCover)
    change IsUnit (J.comp quadraticCasimirCover) at hprod
    rw [← hJ] at hprod
    obtain ⟨v, hv⟩ := isUnit_of_mul_isUnit_left hprod
    rw [hFR, ← hv]
    exact ⟨v⁻¹, by simp [mul_assoc]⟩

/-- Leading coefficients remove the unit multiplier; infinitely many translates force constancy. -/
private theorem eq_C_of_associated_shift {P : (ℂ[X])[X]} {a : ℂ[X]}
    (ha : a ≠ 0) (h : Associated P (P.comp (X + C a))) :
    P = C (P.eval 0) := by
  by_cases hP : P = 0
  · simp [hP]
  obtain ⟨u, hu⟩ := h
  obtain ⟨r, _, hr⟩ := Polynomial.isUnit_iff.mp u.isUnit
  rw [← hr] at hu
  have hl := congrArg Polynomial.leadingCoeff hu
  rw [leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_comp (by simp)] at hl
  have hl' : P.leadingCoeff * r = P.leadingCoeff * 1 := by simpa using hl
  have hr1 := mul_left_cancel₀ (leadingCoeff_ne_zero.mpr hP) hl'
  have hs : P.comp (X + C a) = P := by simpa [hr1] using hu.symm
  have hp : Function.Periodic P.eval a := by
    intro z
    have hz := congrArg (Polynomial.eval z) hs
    simpa only [eval_comp, eval_add, eval_X, eval_C] using hz
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Function.Injective (fun n : ℕ => (n : ℂ[X]) * a) := by
    intro m n he
    exact Nat.cast_injective (mul_right_cancel₀ ha he)
  apply (Set.infinite_range_of_injective hi).mono
  rintro z ⟨n, rfl⟩
  simpa only [Set.mem_setOf_eq, eval_C, zero_add, nsmul_eq_mul] using (hp.nsmul n) 0

private def shiftEquiv (a : ℂ) : (ℂ[X])[X] ≃+* (ℂ[X])[X] where
  toFun P := P.comp (X + C (C a))
  invFun P := P.comp (X - C (C a))
  left_inv P := by
    simp only [comp_assoc, add_comp, X_comp, C_comp,
      sub_add_cancel, comp_X]
  right_inv P := by
    simp only [comp_assoc, sub_comp, X_comp, C_comp,
      add_sub_cancel_right, comp_X]
  map_mul' P Q := mul_comp P Q _
  map_add' P Q := add_comp

private theorem eval_shift (x y a : ℂ) (P : (ℂ[X])[X]) :
    evalPairHom x y (shiftEquiv a P) = evalPairHom x (y + a) P := by
  change eval₂ (evalRingHom x) y (P.comp (X + C (C a))) = _
  rw [eval₂_comp]
  simp [evalPairHom]

private def conjugateEquiv : (ℂ[X])[X] ≃+* (ℂ[X])[X] :=
  Polynomial.mapEquiv (Polynomial.mapEquiv Complex.conjAe.toRingEquiv)

private theorem eval_conjugate (x y : ℂ) (P : (ℂ[X])[X]) :
    evalPairHom x y (conjugateEquiv P) =
      (starRingEnd ℂ) (evalPairHom ((starRingEnd ℂ) x) ((starRingEnd ℂ) y) P) := by
  have hinner (p : ℂ[X]) :
      (p.map (starRingEnd ℂ)).eval x = (starRingEnd ℂ) (p.eval ((starRingEnd ℂ) x)) := by
    simpa using Polynomial.eval_map_apply (f := starRingEnd ℂ) (p := p) ((starRingEnd ℂ) x)
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | monomial n a =>
      simp [conjugateEquiv, evalPairHom, map_mul, map_pow]
      exact Or.inl (hinner a)

private def lineRoots (P : (ℂ[X])[X]) (b : ℝ) : Set ℝ :=
  {x | ∃ y : ℝ, evalPairHom (y : ℂ) ((x : ℂ) + Complex.I * b) P = 0}

/-- An infinite real locus forces association with its reflected conjugate. -/
private theorem associated_reflection_of_infinite_line {P : (ℂ[X])[X]}
    (hP : Irreducible P) (b : ℝ) (hline : (lineRoots P b).Infinite) :
    Associated P (shiftEquiv (-2 * Complex.I * b) (conjugateEquiv P)) := by
  by_contra hn
  have hi : Irreducible (shiftEquiv (-2 * Complex.I * b) (conjugateEquiv P)) :=
    (MulEquiv.irreducible_iff _).mpr ((MulEquiv.irreducible_iff _).mpr hP)
  have hf := finite_second_coords_of_not_associated hP hi hn
  have hj : Function.Injective (fun x : ℝ => (x : ℂ) + Complex.I * b) := by
    intro x y h
    exact Complex.ofReal_injective (add_right_cancel h)
  apply hline
  apply (hf.preimage hj.injOn).subset
  rintro x ⟨y, hy⟩
  refine ⟨(y : ℂ), hy, ?_⟩
  rw [eval_shift, eval_conjugate]
  have ht : (starRingEnd ℂ) ((x : ℂ) + Complex.I * b + -2 * Complex.I * b) =
      (x : ℂ) + Complex.I * b := by
    simp only [map_add, map_mul, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [Complex.conj_ofReal, ht, hy, map_zero]

/-- The two reflected conjugates differ by translation by i. -/
private theorem constant_of_two_reality_lines {P : (ℂ[X])[X]} (hP : Irreducible P)
    (hzero : (lineRoots P 0).Infinite) (hhalf : (lineRoots P (-1 / 2)).Infinite) :
    P = C (P.eval 0) := by
  have h0 := associated_reflection_of_infinite_line hP 0 hzero
  have hhalf' := associated_reflection_of_infinite_line hP (-1 / 2) hhalf
  have h0' : Associated P (conjugateEquiv P) := by
    simpa [shiftEquiv] using h0
  have h1 : Associated P (shiftEquiv Complex.I (conjugateEquiv P)) := by
    have he : -2 * Complex.I * ((-1 / 2 : ℝ) : ℂ) = Complex.I := by
      push_cast
      ring
    simpa only [he] using hhalf' 
  have h2 := Associated.map (shiftEquiv Complex.I) h0'
  have h3 := h1.trans h2.symm
  apply eq_C_of_associated_shift (a := C Complex.I) (by simp)
  exact h3

private theorem eval_comp_casimir (y t : ℂ) (F : (ℂ[X])[X]) :
    evalPairHom y t (F.comp quadraticCasimirCover) =
      evalPairHom y (_root_.RHTower.SelbergScatteringPolynomialReality.criticalCasimir t) F := by
  change eval₂ (evalRingHom y) t (F.comp quadraticCasimirCover) = _
  rw [eval₂_comp]
  congr 1
  simp [quadraticCasimirCover, eval₂_sub, eval₂_pow,
    _root_.RHTower.SelbergScatteringPolynomialReality.criticalCasimir]
  ring_nf
  norm_num [Complex.I_sq]
  ring

private def deckEquiv : (ℂ[X])[X] ≃+* (ℂ[X])[X] where
  toFun P := P.comp (C (2 * C (-Complex.I / 2)) - X)
  invFun P := P.comp (C (2 * C (-Complex.I / 2)) - X)
  left_inv P := by simp only [comp_assoc, sub_comp, C_comp, X_comp, sub_sub_cancel, comp_X]
  right_inv P := by simp only [comp_assoc, sub_comp, C_comp, X_comp, sub_sub_cancel, comp_X]
  map_mul' P Q := mul_comp P Q _
  map_add' P Q := add_comp

private theorem eval_deck (y t : ℂ) (P : (ℂ[X])[X]) :
    evalPairHom y t (deckEquiv P) = evalPairHom y (-t - Complex.I) P := by
  change eval₂ (evalRingHom y) t (P.comp (C (2 * C (-Complex.I / 2)) - X)) = _
  rw [eval₂_comp]
  congr 1
  simp
  ring

private theorem lineRoots_mul (P Q : (ℂ[X])[X]) (b : ℝ) :
    lineRoots (P * Q) b = lineRoots P b ∪ lineRoots Q b := by
  ext x
  simp only [lineRoots, Set.mem_setOf_eq, map_mul, mul_eq_zero,
    exists_or, Set.mem_union]

private theorem eval_zero_of_dvd {P Q : (ℂ[X])[X]} (h : P ∣ Q) (y t : ℂ)
    (hz : evalPairHom y t P = 0) : evalPairHom y t Q = 0 := by
  obtain ⟨R, rfl⟩ := h
  rw [map_mul, hz, zero_mul]

private theorem lineRoots_associated {P Q : (ℂ[X])[X]} (h : Associated P Q) (b : ℝ) :
    lineRoots P b = lineRoots Q b := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, eval_zero_of_dvd h.dvd _ _ hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, eval_zero_of_dvd h.symm.dvd _ _ hy⟩

private theorem lineRoots_deck_half (P : (ℂ[X])[X]) :
    lineRoots (deckEquiv P) (-1 / 2) = Neg.neg ⁻¹' lineRoots P (-1 / 2) := by
  ext x
  simp only [lineRoots, Set.mem_preimage, Set.mem_setOf_eq]
  have he : -((x : ℂ) + Complex.I * ((-1 / 2 : ℝ) : ℂ)) - Complex.I =
      ((-x : ℝ) : ℂ) + Complex.I * ((-1 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  simp only [eval_deck, he]

private theorem infinite_line_factor {P G : (ℂ[X])[X]} (b : ℝ)
    (hline : (lineRoots P b).Infinite)
    (horbit : Associated P G ∨ Associated P (G * deckEquiv G)) :
    (lineRoots G b).Infinite ∨ (lineRoots (deckEquiv G) b).Infinite := by
  rcases horbit with h | h
  · exact Or.inl ((lineRoots_associated h b) ▸ hline)
  · rw [lineRoots_associated h b, lineRoots_mul] at hline
    exact Set.infinite_union.mp hline

private theorem infinite_native_factor {P G : (ℂ[X])[X]}
    (hline : (lineRoots P (-1 / 2)).Infinite)
    (horbit : Associated P G ∨ Associated P (G * deckEquiv G)) :
    (lineRoots G (-1 / 2)).Infinite := by
  rcases infinite_line_factor _ hline horbit with h | h
  · exact h
  · rw [lineRoots_deck_half] at h
    by_contra hf
    have hf := not_not.mp hf
    exact h (hf.preimage (neg_injective : Function.Injective (Neg.neg : ℝ → ℝ)).injOn)

/-- Real transport values above the critical Casimir parabola, parametrized by its real height. -/
def criticalRealLocus (F : (ℂ[X])[X]) : Set ℝ :=
  {t | ∃ y : ℝ, evalPairHom (y : ℂ)
    (_root_.RHTower.SelbergScatteringPolynomialReality.criticalCasimir (t : ℂ)) F = 0}

/-- Real transport values above the open native continuous spectrum. -/
def nativeRealLocus (F : (ℂ[X])[X]) : Set ℝ :=
  {x | 1 / 4 < x ∧ ∃ y : ℝ, evalPairHom (y : ℂ) (x : ℂ) F = 0}

private theorem criticalRealLocus_pullback (F : (ℂ[X])[X]) :
    lineRoots (F.comp quadraticCasimirCover) 0 = criticalRealLocus F := by
  ext t
  simp only [lineRoots, criticalRealLocus, Set.mem_setOf_eq,
    Complex.ofReal_zero, mul_zero, add_zero, eval_comp_casimir]

private theorem infinite_native_pullback {F : (ℂ[X])[X]}
    (h : (nativeRealLocus F).Infinite) :
    (lineRoots (F.comp quadraticCasimirCover) (-1 / 2)).Infinite := by
  by_contra hf
  have hf := not_not.mp hf
  apply h
  apply (hf.image (fun t : ℝ => (1 + t ^ 2) / 4)).subset
  rintro x ⟨hx, y, hy⟩
  have hpos : 0 ≤ 4 * x - 1 := by linarith only [hx]
  have hs := Real.sq_sqrt hpos
  refine ⟨Real.sqrt (4 * x - 1), ?_, ?_⟩
  · refine ⟨y, ?_⟩
    rw [eval_comp_casimir]
    have he : _root_.RHTower.SelbergScatteringPolynomialReality.criticalCasimir
        ((Real.sqrt (4 * x - 1) : ℂ) + Complex.I * ((-1 / 2 : ℝ) : ℂ)) = (x : ℂ) := by
      calc
        _ = (((1 + Real.sqrt (4 * x - 1) ^ 2) / 4 : ℝ) : ℂ) := by
          unfold _root_.RHTower.SelbergScatteringPolynomialReality.criticalCasimir
          push_cast
          ring_nf
          norm_num [Complex.I_sq]
          ring
        _ = (x : ℂ) := by congr 1; nlinarith only [hs]
    rw [he]
    exact hy
  · nlinarith only [hs]

/-- The deck map preserves the lifted native line, so a critical factor sees both loci. -/
private theorem exists_common_reality_factor {F : (ℂ[X])[X]} (hF : Irreducible F)
    (hcritical : (criticalRealLocus F).Infinite) (hnative : (nativeRealLocus F).Infinite) :
    ∃ G : (ℂ[X])[X], Irreducible G ∧ G ∣ F.comp quadraticCasimirCover ∧
      (lineRoots G 0).Infinite ∧ (lineRoots G (-1 / 2)).Infinite := by
  have hc : (lineRoots (F.comp quadraticCasimirCover) 0).Infinite := by
    rw [criticalRealLocus_pullback]
    exact hcritical
  have hn := infinite_native_pullback hnative
  have hQ0 : F.comp quadraticCasimirCover ≠ 0 := by
    intro hz
    apply hF.ne_zero
    apply casimir_comp_injective
    simpa using hz
  have hQu : ¬ IsUnit (F.comp quadraticCasimirCover) := by
    intro hu
    obtain ⟨t, y, hy⟩ := hc.nonempty
    have hv := hu.map (evalPairHom (y : ℂ) ((t : ℂ) + Complex.I * (0 : ℝ)))
    rw [hy] at hv
    exact not_isUnit_zero hv
  obtain ⟨G, hG, hGd⟩ := WfDvdMonoid.exists_irreducible_factor hQu hQ0
  obtain ⟨R, hR⟩ := hGd
  have ho := casimir_factor_orbit hF hG.not_isUnit hR
  change Associated (F.comp quadraticCasimirCover) G ∨
    Associated (F.comp quadraticCasimirCover) (G * deckEquiv G) at ho
  have hnG := infinite_native_factor hn ho
  rcases infinite_line_factor 0 hc ho with hcG | hcG
  · exact ⟨G, hG, ⟨R, hR⟩, hcG, hnG⟩
  · have hdeck : deckEquiv (F.comp quadraticCasimirCover) = F.comp quadraticCasimirCover := by
      change (F.comp quadraticCasimirCover).comp
        (C (2 * C (-Complex.I / 2)) - X) = _
      rw [comp_assoc, quadraticCasimirCover_reflection]
    have hnD : (lineRoots (deckEquiv G) (-1 / 2)).Infinite := by
      by_contra hf
      have hf := not_not.mp hf
      have hfin := hf.preimage (neg_injective : Function.Injective (Neg.neg : ℝ → ℝ)).injOn
      have he := lineRoots_deck_half (deckEquiv G)
      have hDD : deckEquiv (deckEquiv G) = G := by
        change deckEquiv.symm (deckEquiv G) = G
        exact deckEquiv.symm_apply_apply G
      rw [hDD] at he
      exact hnG (he.symm ▸ hfin)
    refine ⟨deckEquiv G, (MulEquiv.irreducible_iff deckEquiv).mpr hG,
      ⟨deckEquiv R, ?_⟩, hcG, hnD⟩
    calc F.comp quadraticCasimirCover = deckEquiv (F.comp quadraticCasimirCover) := hdeck.symm
      _ = deckEquiv G * deckEquiv R := by rw [hR, map_mul]

private theorem irreducible_horizontal (c : ℂ) :
    Irreducible (C (X - C c) : (ℂ[X])[X]) := by
  apply (MulEquiv.irreducible_iff swapEquiv).mp
  have he : swapEquiv (C (X - C c)) = X - C (C c) := by
    simp [swapEquiv, Bottcher.swapVars]
  rw [he]
  exact Polynomial.irreducible_X_sub_C _

private theorem criticalCasimir_real_injective :
    Function.Injective (fun t : ℝ =>
      _root_.RHTower.SelbergScatteringPolynomialReality.criticalCasimir (t : ℂ)) := by
  intro x y h
  have hi := congrArg Complex.im h
  simp [_root_.RHTower.SelbergScatteringPolynomialReality.criticalCasimir, ← Complex.ofReal_pow] at hi
  linarith only [hi]

/-- One real value of a constant cover factor yields infinitely many intersections with a horizontal line. -/
private theorem horizontal_of_constant_pullback_factor {F G : (ℂ[X])[X]}
    (hF : Irreducible F) (hGd : G ∣ F.comp quadraticCasimirCover)
    (hGc : G = C (G.eval 0)) (hline : (lineRoots G 0).Infinite) :
    ∃ c : ℝ, Associated F (C (X - C (c : ℂ))) := by
  obtain ⟨t, c, hc⟩ := hline.nonempty
  have hroot : (G.eval 0).eval (c : ℂ) = 0 := by
    rw [hGc, evalPairHom_C] at hc
    exact hc
  refine ⟨c, ?_⟩
  by_contra hn
  have hf := finite_second_coords_of_not_associated hF (irreducible_horizontal (c : ℂ)) hn
  apply (Set.infinite_range_of_injective criticalCasimir_real_injective)
  apply hf.subset
  rintro z ⟨x, rfl⟩
  refine ⟨(c : ℂ), ?_, ?_⟩
  · rw [← eval_comp_casimir]
    apply eval_zero_of_dvd hGd
    rw [hGc, evalPairHom_C]
    exact hroot
  · simp [evalPairHom_C]

/-- Two infinite reality loci force an irreducible correspondence to be a real horizontal line. -/
theorem associated_horizontal_of_infinite_real_loci {F : (ℂ[X])[X]} (hF : Irreducible F)
    (hcritical : (criticalRealLocus F).Infinite) (hnative : (nativeRealLocus F).Infinite) :
    ∃ c : ℝ, Associated F (C (X - C (c : ℂ))) := by
  obtain ⟨G, hG, hd, hc, hn⟩ := exists_common_reality_factor hF hcritical hnative
  exact horizontal_of_constant_pullback_factor hF hd
    (constant_of_two_reality_lines hG hc hn) hc

private def quadraticCoordinateEquiv : (ℂ[X])[X] ≃+* (ℂ[X])[X] where
  toFun P := P.comp (C (C (4 : ℂ)) * X - C (C (3 / 4 : ℂ)) - C X)
  invFun P := P.comp (C (C (1 / 4 : ℂ)) * (X + C (C (3 / 4 : ℂ)) + C X))
  left_inv P := by
    dsimp only
    rw [comp_assoc]
    have he : (C (C (4 : ℂ)) * X - C (C (3 / 4 : ℂ)) - C X).comp
        (C (C (1 / 4 : ℂ)) * (X + C (C (3 / 4 : ℂ)) + C X)) = X := by
      simp only [sub_comp, mul_comp, C_comp, X_comp]
      have h4 : (C (C (4 : ℂ)) : (ℂ[X])[X]) * C (C (1 / 4 : ℂ)) = 1 := by
        rw [← C_mul, ← C_mul]
        norm_num
      rw [← mul_assoc, h4, one_mul]
      ring
    rw [he, comp_X]
  right_inv P := by
    dsimp only
    rw [comp_assoc]
    have he : (C (C (1 / 4 : ℂ)) * (X + C (C (3 / 4 : ℂ)) + C X)).comp
        (C (C (4 : ℂ)) * X - C (C (3 / 4 : ℂ)) - C X) = X := by
      simp only [mul_comp, C_comp, add_comp, X_comp]
      have he' : (C (C (4 : ℂ)) * X - C (C (3 / 4 : ℂ)) - C X +
          C (C (3 / 4 : ℂ)) + C X : (ℂ[X])[X]) = C (C (4 : ℂ)) * X := by ring
      rw [he', ← mul_assoc, ← C_mul, ← C_mul]
      norm_num
    rw [he, comp_X]
  map_mul' P Q := mul_comp P Q _
  map_add' P Q := add_comp

/-- The irreducible quadratic correspondence `(4z - 3/4 - w)² + w = 0`. -/
def quadraticRelationPoly : (ℂ[X])[X] :=
  (C (C (4 : ℂ)) * X - C (C (3 / 4 : ℂ)) - C X) ^ 2 + C X

/-- A triangular change of coordinates identifies this correspondence with a parabola. -/
theorem irreducible_quadraticRelationPoly : Irreducible quadraticRelationPoly := by
  have hi : Irreducible ((X : (ℂ[X])[X]) ^ 2 + C X) := by
    apply (MulEquiv.irreducible_iff swapEquiv).mp
    have he : swapEquiv ((X : (ℂ[X])[X]) ^ 2 + C X) = X - C (-(X ^ 2)) := by
      simp [swapEquiv, Bottcher.swapVars]
      ring
    rw [he]
    exact Polynomial.irreducible_X_sub_C _
  have he : quadraticCoordinateEquiv ((X : (ℂ[X])[X]) ^ 2 + C X) =
      quadraticRelationPoly := by
    change ((X : (ℂ[X])[X]) ^ 2 + C X).comp
      (C (C (4 : ℂ)) * X - C (C (3 / 4 : ℂ)) - C X) = quadraticRelationPoly
    simp only [add_comp, pow_comp, X_comp, C_comp]
    rfl
  rw [← he]
  exact (MulEquiv.irreducible_iff quadraticCoordinateEquiv).mpr hi

private theorem eval_quadraticRelationPoly (y z : ℂ) :
    evalPairHom y z quadraticRelationPoly = quadraticRelation z y := by
  simp [quadraticRelationPoly, quadraticRelation, evalPairHom, eval₂_sub, eval₂_pow]

/-- The only irreducible algebraic transports real infinitely often on both loci are real constants. -/
theorem real_constant_of_infinite_real_loci {F : (ℂ[X])[X]} (hF : Irreducible F)
    (hcritical : (criticalRealLocus F).Infinite) (hnative : (nativeRealLocus F).Infinite) :
    ∃ c : ℝ, ∃ a : ℂ, a ≠ 0 ∧ F = C (C a) * C (X - C (c : ℂ)) := by
  obtain ⟨c, hc⟩ := associated_horizontal_of_infinite_real_loci hF hcritical hnative
  obtain ⟨u, hu⟩ := hc.symm
  obtain ⟨r, hr, hur⟩ := Polynomial.isUnit_iff.mp u.isUnit
  obtain ⟨a, ha, hra⟩ := Polynomial.isUnit_iff.mp hr
  refine ⟨c, a, isUnit_iff_ne_zero.mp ha, ?_⟩
  rw [← hur, ← hra] at hu
  simpa only [mul_comm] using hu.symm

/-- Every critical Casimir has the real transport value `t²` on the quadratic correspondence. -/
theorem quadraticRelationPoly_critical_locus :
    criticalRealLocus quadraticRelationPoly = Set.univ := by
  apply Set.eq_univ_of_forall
  intro t
  refine ⟨t ^ 2, ?_⟩
  rw [eval_quadraticRelationPoly]
  simpa only [Complex.ofReal_pow] using quadraticRelation_critical t

/-- The real base locus of the quadratic correspondence ends exactly at the spectral edge `1/4`. -/
theorem quadraticRelationPoly_real_locus :
    {x : ℝ | ∃ y : ℝ, evalPairHom (y : ℂ) (x : ℂ) quadraticRelationPoly = 0} =
      Set.Iic (1 / 4) := by
  ext x
  simp only [Set.mem_setOf_eq, eval_quadraticRelationPoly, Set.mem_Iic]
  exact quadraticRelation_real_iff x

private theorem quadraticRelationPoly_coeff_two :
    quadraticRelationPoly.coeff 2 = C (16 : ℂ) := by
  norm_num [quadraticRelationPoly, pow_two, mul_sub, sub_mul, mul_add, sub_add]
  have he : (C (C (4 : ℂ)) * X * (C (C (4 : ℂ)) * X) : (ℂ[X])[X]) =
      (C (C (4 : ℂ)) * C (C (4 : ℂ))) * X ^ 2 := by ring
  rw [he, ← C_mul, ← C_mul]
  norm_num

/-- The quadratic correspondence is not any scalar multiple of a horizontal line. -/
theorem quadraticRelationPoly_not_horizontal :
    ¬ ∃ c : ℝ, ∃ a : ℂ,
      quadraticRelationPoly = C (C a) * C (X - C (c : ℂ)) := by
  rintro ⟨c, a, h⟩
  have he := congrArg (fun P : (ℂ[X])[X] => P.coeff 2) h
  rw [quadraticRelationPoly_coeff_two, ← C_mul] at he
  norm_num at he

end GaloisForLFunctions.RenormalizedIntersectionTheory.ScatteringAlgebraicReality
