/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2CarryCocycle

/-!
# Explicit carry classes and cyclic norm quotients

The standard carry cocycle for a finite cyclic Galois extension has kernel exactly the field-norm
image.  It therefore embeds the classical norm quotient into degree-two group cohomology.  When
the quotient is finite, the embedding is an equivalence, giving a literal bar-cocycle model of the
finite local invariant.  A split valuation then reads this carry class as valuation modulo the
extension degree.
-/

open CategoryTheory Representation

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

variable {G A : Type*} [Group G] [AddCommGroup A] [Module ℤ A]

theorem zmod_finEquiv_val (n : ℕ) [NeZero n] (r : Fin n) :
    (ZMod.finEquiv n r).val = (r : ℕ) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- Exactly one standard residue wraps when translated by one around a nonempty cyclic group. -/
theorem sum_cyclicCarry_one (n : ℕ) [NeZero n] (hn : 1 < n) :
    ∑ a : ZMod n, cyclicCarry n a 1 = 1 := by
  have hsum : (∑ a : ZMod n, (a.val + (1 : ZMod n).val)) =
      ∑ a : ZMod n, (n * cyclicCarry n a 1 + (a + 1).val) := by
    apply Finset.sum_congr rfl
    intro a ha
    exact zmod_val_add_split a 1
  have hshift : (∑ a : ZMod n, (a + 1).val) = ∑ a : ZMod n, a.val := by
    apply Fintype.sum_bijective (fun a : ZMod n => a + 1)
    · constructor
      · intro a b hab
        exact add_right_cancel hab
      · intro b
        exact ⟨b - 1, by simp⟩
    · intro a
      rfl
  simp only [Finset.sum_add_distrib] at hsum
  rw [← Finset.mul_sum] at hsum
  rw [hshift] at hsum
  have hone : (1 : ZMod n).val = 1 := by
    letI : Fact (1 < n) := ⟨hn⟩
    exact ZMod.val_one n
  rw [hone] at hsum
  have hcard : Fintype.card (ZMod n) = n := ZMod.card n
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  rw [Finset.card_univ] at hsum
  rw [hcard] at hsum
  have hcancel : n = n * ∑ a : ZMod n, cyclicCarry n a 1 := by
    exact Nat.add_right_cancel (by simpa [add_comm] using hsum)
  have hone_eq : 1 = ∑ a : ZMod n, cyclicCarry n a 1 :=
    Nat.eq_of_mul_eq_mul_left (NeZero.pos n) (by simpa using hcancel)
  exact hone_eq.symm

/-- Partial sum of the orbit of `b` under powers of `g`. -/
def cyclicPartialOrbitSum (rho : G →* Module.End ℤ A) (g : G) (b : A) (m : ℕ) : A :=
  ∑ r ∈ Finset.range m, rho (g ^ r) b

theorem cyclicPartialOrbitSum_zero (rho : G →* Module.End ℤ A) (g : G) (b : A) :
    cyclicPartialOrbitSum rho g b 0 = 0 := by
  simp [cyclicPartialOrbitSum]

theorem cyclicPartialOrbitSum_add (rho : G →* Module.End ℤ A) (g : G) (b : A) (i j : ℕ) :
    cyclicPartialOrbitSum rho g b (i + j) =
      cyclicPartialOrbitSum rho g b i + rho (g ^ i) (cyclicPartialOrbitSum rho g b j) := by
  simp only [cyclicPartialOrbitSum, Finset.sum_range_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [pow_add, map_mul]
  rfl

theorem cyclicPartialOrbitSum_period_mul (rho : G →* Module.End ℤ A) (g : G) (b : A)
    (n c : ℕ) (hgn : g ^ n = 1) :
    cyclicPartialOrbitSum rho g b (n * c) =
      c • cyclicPartialOrbitSum rho g b n := by
  induction c with
  | zero => simp [cyclicPartialOrbitSum_zero]
  | succ c ih =>
      rw [Nat.mul_succ, cyclicPartialOrbitSum_add, ih]
      rw [pow_mul, hgn, one_pow, map_one]
      simp [add_nsmul]

theorem cyclicPartialOrbitSum_split (rho : G →* Module.End ℤ A) (g : G) (b : A)
    (n c r : ℕ) (hgn : g ^ n = 1) :
    cyclicPartialOrbitSum rho g b (n * c + r) =
      c • cyclicPartialOrbitSum rho g b n + cyclicPartialOrbitSum rho g b r := by
  rw [cyclicPartialOrbitSum_add, cyclicPartialOrbitSum_period_mul rho g b n c hgn]
  rw [pow_mul, hgn, one_pow, map_one]
  rfl

/-- Chosen-generator power represented by the standard exponent coordinate. -/
theorem cyclicGaloisGenerator_pow_exponent_val
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (sigma : Gal(L/K)) :
    cyclicGaloisGenerator K L ^ (cyclicGaloisExponent K L sigma).val = sigma := by
  letI : NeZero (Module.finrank K L) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  let e := zmodMulEquivOfGenerator
    (cyclicGaloisGenerator_spec K L) (IsGalois.card_aut_eq_finrank K L)
  calc
    cyclicGaloisGenerator K L ^ (cyclicGaloisExponent K L sigma).val =
        e (Multiplicative.ofAdd
          (((cyclicGaloisExponent K L sigma).val : ℕ) : ZMod (Module.finrank K L))) := by
      rw [← Int.cast_natCast]
      rw [zmodMulEquivOfGenerator_apply_ofAdd_intCast, zpow_natCast]
    _ = e (Multiplicative.ofAdd (cyclicGaloisExponent K L sigma)) := by
      rw [ZMod.natCast_zmod_val]
    _ = sigma := e.apply_symm_apply sigma

/-- Exponent coordinate of a chosen-generator power. -/
theorem cyclicGaloisExponent_generator_pow
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (r : ℕ) :
    cyclicGaloisExponent K L (cyclicGaloisGenerator K L ^ r) =
      (r : ZMod (Module.finrank K L)) := by
  letI : NeZero (Module.finrank K L) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  let e := zmodMulEquivOfGenerator
    (cyclicGaloisGenerator_spec K L) (IsGalois.card_aut_eq_finrank K L)
  apply Multiplicative.ofAdd.injective
  change e.symm (cyclicGaloisGenerator K L ^ r) = Multiplicative.ofAdd (r : ZMod _)
  rw [← zpow_natCast]
  simpa [e, Int.cast_natCast] using
    (zmodMulEquivOfGenerator_symm_apply_zpow
      (cyclicGaloisGenerator_spec K L) (IsGalois.card_aut_eq_finrank K L) (r : ℤ))

/-- Exponent coordinate sends the chosen generator to one. -/
@[simp] theorem cyclicGaloisExponent_generator
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] :
    cyclicGaloisExponent K L (cyclicGaloisGenerator K L) = 1 := by
  simpa using cyclicGaloisExponent_generator_pow K L 1

/-- Exponent coordinates biject the finite cyclic Galois group with its standard residue cycle. -/
theorem cyclicGaloisExponent_bijective
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] :
    Function.Bijective (cyclicGaloisExponent K L) := by
  letI : NeZero (Module.finrank K L) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  constructor
  · intro sigma tau h
    rw [← cyclicGaloisGenerator_pow_exponent_val K L sigma,
      ← cyclicGaloisGenerator_pow_exponent_val K L tau, h]
  · intro r
    refine ⟨cyclicGaloisGenerator K L ^ r.val, ?_⟩
    rw [cyclicGaloisExponent_generator_pow]
    exact ZMod.natCast_zmod_val r

/-- Summing carry against the chosen generator recovers its base parameter. -/
theorem sum_cyclicGaloisCarryFactor_generator
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (hdegree : 1 < Module.finrank K L) (a : Additive Kˣ) :
    (∑ sigma : Gal(L/K), cyclicGaloisCarryFactor K L a
        (sigma, cyclicGaloisGenerator K L)) =
      cyclicGaloisBaseUnitsMap (K := K) (L := L) a := by
  letI : NeZero (Module.finrank K L) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  let x : Rep.ofAlgebraAutOnUnits K L :=
    cyclicGaloisBaseUnitsMap (K := K) (L := L) a
  change (∑ sigma : Gal(L/K),
      cyclicCarry (Module.finrank K L) (cyclicGaloisExponent K L sigma)
          (cyclicGaloisExponent K L (cyclicGaloisGenerator K L)) • x) = x
  rw [cyclicGaloisExponent_generator]
  calc
    (∑ sigma : Gal(L/K),
        cyclicCarry (Module.finrank K L) (cyclicGaloisExponent K L sigma) 1 • x) =
      ∑ r : ZMod (Module.finrank K L), cyclicCarry (Module.finrank K L) r 1 • x := by
        exact Fintype.sum_bijective (cyclicGaloisExponent K L)
          (cyclicGaloisExponent_bijective K L) _ _ (fun _ => rfl)
    _ = (∑ r : ZMod (Module.finrank K L),
        cyclicCarry (Module.finrank K L) r 1) • x := by
      exact Finset.sum_nsmul_assoc Finset.univ _ x
    _ = x := by rw [sum_cyclicCarry_one _ hdegree, one_nsmul]

/-- Summing an inhomogeneous coboundary along the generator edge gives the representation norm. -/
theorem sum_cyclicGaloisCoboundary_generator
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (u : Gal(L/K) → Rep.ofAlgebraAutOnUnits K L) :
    (∑ sigma : Gal(L/K),
      ((Rep.ofAlgebraAutOnUnits K L).ρ sigma
          (u (cyclicGaloisGenerator K L)) -
        u (sigma * cyclicGaloisGenerator K L) + u sigma)) =
      (Rep.ofAlgebraAutOnUnits K L).norm.hom
        (u (cyclicGaloisGenerator K L)) := by
  have hshift : (∑ sigma : Gal(L/K),
      u (sigma * cyclicGaloisGenerator K L)) = ∑ sigma : Gal(L/K), u sigma := by
    exact Fintype.sum_bijective
      (fun sigma : Gal(L/K) => sigma * cyclicGaloisGenerator K L)
      (Group.mulRight_bijective (cyclicGaloisGenerator K L)) _ _ (fun _ => rfl)
  have hnorm : (Rep.ofAlgebraAutOnUnits K L).norm.hom
      (u (cyclicGaloisGenerator K L)) =
      ∑ sigma : Gal(L/K), (Rep.ofAlgebraAutOnUnits K L).ρ sigma
        (u (cyclicGaloisGenerator K L)) := by
    rw [Rep.norm_apply]
    change (∑ sigma : Gal(L/K), (Rep.ofAlgebraAutOnUnits K L).ρ sigma)
        (u (cyclicGaloisGenerator K L)) = _
    exact LinearMap.sum_apply Finset.univ _ _
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← hnorm, hshift]
  abel

/-- Partial orbit sum used as the explicit primitive of a norm carry cocycle. -/
def cyclicGaloisPartialNormCochain
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (b : Rep.ofAlgebraAutOnUnits K L) (sigma : Gal(L/K)) :
    Rep.ofAlgebraAutOnUnits K L :=
  cyclicPartialOrbitSum (Rep.ofAlgebraAutOnUnits K L).ρ
    (cyclicGaloisGenerator K L) b (cyclicGaloisExponent K L sigma).val

/-- Coboundary of the partial orbit sum is carry times the full cyclic orbit sum. -/
theorem cyclicGaloisPartialNormCochain_coboundary
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (b : Rep.ofAlgebraAutOnUnits K L) (sigma tau : Gal(L/K)) :
    (Rep.ofAlgebraAutOnUnits K L).ρ sigma
        (cyclicGaloisPartialNormCochain K L b tau) -
      cyclicGaloisPartialNormCochain K L b (sigma * tau) +
      cyclicGaloisPartialNormCochain K L b sigma =
        cyclicCarry (Module.finrank K L)
            (cyclicGaloisExponent K L sigma) (cyclicGaloisExponent K L tau) •
          cyclicPartialOrbitSum (Rep.ofAlgebraAutOnUnits K L).ρ
            (cyclicGaloisGenerator K L) b (Module.finrank K L) := by
  letI : NeZero (Module.finrank K L) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  let rho := (Rep.ofAlgebraAutOnUnits K L).ρ
  let g := cyclicGaloisGenerator K L
  let i := (cyclicGaloisExponent K L sigma).val
  let j := (cyclicGaloisExponent K L tau).val
  let r := (cyclicGaloisExponent K L (sigma * tau)).val
  let c := cyclicCarry (Module.finrank K L)
    (cyclicGaloisExponent K L sigma) (cyclicGaloisExponent K L tau)
  have hsigma : g ^ i = sigma := cyclicGaloisGenerator_pow_exponent_val K L sigma
  have hexp : cyclicGaloisExponent K L (sigma * tau) =
      cyclicGaloisExponent K L sigma + cyclicGaloisExponent K L tau :=
    cyclicGaloisExponent_mul K L sigma tau
  have hir : i + j = Module.finrank K L * c + r := by
    dsimp [i, j, r, c]
    rw [hexp]
    exact zmod_val_add_split _ _
  have hadd := cyclicPartialOrbitSum_add rho g b i j
  have hsplit := cyclicPartialOrbitSum_split rho g b
    (Module.finrank K L) c r (cyclicGaloisGenerator_pow_finrank K L)
  rw [← hir] at hsplit
  change rho sigma (cyclicPartialOrbitSum rho g b j) -
      cyclicPartialOrbitSum rho g b r + cyclicPartialOrbitSum rho g b i =
        c • cyclicPartialOrbitSum rho g b (Module.finrank K L)
  rw [← hsigma]
  rw [hadd] at hsplit
  calc
    rho (g ^ i) (cyclicPartialOrbitSum rho g b j) -
          cyclicPartialOrbitSum rho g b r + cyclicPartialOrbitSum rho g b i =
        (cyclicPartialOrbitSum rho g b i +
          rho (g ^ i) (cyclicPartialOrbitSum rho g b j)) -
            cyclicPartialOrbitSum rho g b r := by abel
    _ = (c • cyclicPartialOrbitSum rho g b (Module.finrank K L) +
          cyclicPartialOrbitSum rho g b r) - cyclicPartialOrbitSum rho g b r := by
      rw [hsplit]
    _ = c • cyclicPartialOrbitSum rho g b (Module.finrank K L) := by abel

/-- Full partial orbit is Mathlib's representation norm. -/
theorem cyclicGaloisPartialOrbitSum_finrank
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (b : Rep.ofAlgebraAutOnUnits K L) :
    cyclicPartialOrbitSum (Rep.ofAlgebraAutOnUnits K L).ρ
        (cyclicGaloisGenerator K L) b (Module.finrank K L) =
      (Rep.ofAlgebraAutOnUnits K L).norm.hom b := by
  letI : NeZero (Module.finrank K L) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  let f : Fin (Module.finrank K L) → Gal(L/K) :=
    fun r => cyclicGaloisGenerator K L ^ (r : ℕ)
  have hf : Function.Bijective f := by
    constructor
    · intro r s hrs
      apply Fin.ext
      change cyclicGaloisGenerator K L ^ (r : ℕ) =
        cyclicGaloisGenerator K L ^ (s : ℕ) at hrs
      rw [pow_inj_mod, cyclicGaloisGenerator_orderOf K L] at hrs
      simpa [Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt s.isLt] using hrs
    · intro sigma
      refine ⟨⟨(cyclicGaloisExponent K L sigma).val,
        (cyclicGaloisExponent K L sigma).val_lt⟩, ?_⟩
      exact cyclicGaloisGenerator_pow_exponent_val K L sigma
  rw [cyclicPartialOrbitSum, ← Fin.sum_univ_eq_sum_range]
  rw [Rep.norm_apply]
  have hnorm : (Rep.ofAlgebraAutOnUnits K L).ρ.norm b =
      ∑ sigma : Gal(L/K), (Rep.ofAlgebraAutOnUnits K L).ρ sigma b := by
    change (∑ sigma : Gal(L/K), (Rep.ofAlgebraAutOnUnits K L).ρ sigma) b = _
    exact LinearMap.sum_apply Finset.univ _ b
  rw [hnorm]
  change (∑ r : Fin (Module.finrank K L),
      (Rep.ofAlgebraAutOnUnits K L).ρ
        (cyclicGaloisGenerator K L ^ (r : ℕ)) b) =
    ∑ sigma : Gal(L/K), (Rep.ofAlgebraAutOnUnits K L).ρ sigma b
  exact Fintype.sum_bijective f hf _ _ (fun _ => rfl)

/-- Representation norm of a field unit is the embedded field norm in additive notation. -/
theorem cyclicGaloisRepresentationNorm_eq_baseNorm
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (y : Lˣ) :
    (Rep.ofAlgebraAutOnUnits K L).norm.hom
        ((Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)).symm (Additive.ofMul y)) =
      cyclicGaloisBaseUnitsMap (K := K) (L := L)
        (Additive.ofMul (Units.map (Algebra.norm K) y)) := by
  apply Additive.toMul.injective
  apply Units.ext
  exact groupCohomology.norm_ofAlgebraAutOnUnits_eq y

/-- Carry factor of an actual field norm is the coboundary of the explicit partial-orbit cochain. -/
theorem cyclicGaloisCarryFactor_norm_eq_coboundary
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (y : Lˣ) (sigma tau : Gal(L/K)) :
    (Rep.ofAlgebraAutOnUnits K L).ρ sigma
        (cyclicGaloisPartialNormCochain K L
          ((Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)).symm (Additive.ofMul y)) tau) -
      cyclicGaloisPartialNormCochain K L
          ((Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)).symm (Additive.ofMul y)) (sigma * tau) +
      cyclicGaloisPartialNormCochain K L
          ((Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)).symm (Additive.ofMul y)) sigma =
        cyclicGaloisCarryFactor K L
          (Additive.ofMul (Units.map (Algebra.norm K) y)) (sigma, tau) := by
  rw [cyclicGaloisPartialNormCochain_coboundary]
  rw [cyclicGaloisPartialOrbitSum_finrank]
  rw [cyclicGaloisRepresentationNorm_eq_baseNorm]
  rfl

/-- Every field norm has trivial explicit carry class in cyclic degree-two cohomology. -/
theorem cyclicGaloisCarryH2Class_norm_eq_zero
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (y : Lˣ) :
    cyclicGaloisCarryH2Class K L
        (Additive.ofMul (Units.map (Algebra.norm K) y)) = 0 := by
  rw [cyclicGaloisCarryH2Class, groupCohomology.H2π_eq_zero_iff]
  refine ⟨fun sigma => cyclicGaloisPartialNormCochain K L
    ((Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)).symm (Additive.ofMul y)) sigma, ?_⟩
  funext gh
  rcases gh with ⟨sigma, tau⟩
  exact cyclicGaloisCarryFactor_norm_eq_coboundary K L y sigma tau

/-- For every nontrivial finite cyclic Galois extension, the explicit carry class vanishes
exactly on field norms. -/
theorem cyclicGaloisCarryH2Class_eq_zero_iff_exists_norm_of_one_lt
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (hdegree : 1 < Module.finrank K L) (a : Additive Kˣ) :
    cyclicGaloisCarryH2Class K L a = 0 ↔
      ∃ y : Lˣ, Units.map (Algebra.norm K) y = Additive.toMul a := by
  constructor
  · intro ha
    rw [cyclicGaloisCarryH2Class, groupCohomology.H2π_eq_zero_iff] at ha
    rcases ha with ⟨u, hu⟩
    have hsum : (Rep.ofAlgebraAutOnUnits K L).norm.hom
        (u (cyclicGaloisGenerator K L)) =
        cyclicGaloisBaseUnitsMap (K := K) (L := L) a := by
      calc
        (Rep.ofAlgebraAutOnUnits K L).norm.hom
            (u (cyclicGaloisGenerator K L)) =
          ∑ sigma : Gal(L/K),
            ((Rep.ofAlgebraAutOnUnits K L).ρ sigma
                (u (cyclicGaloisGenerator K L)) -
              u (sigma * cyclicGaloisGenerator K L) + u sigma) :=
                (sum_cyclicGaloisCoboundary_generator K L u).symm
        _ = ∑ sigma : Gal(L/K), cyclicGaloisCarryFactor K L a
              (sigma, cyclicGaloisGenerator K L) := by
            apply Finset.sum_congr rfl
            intro sigma hsigma
            exact congrFun hu (sigma, cyclicGaloisGenerator K L)
        _ = cyclicGaloisBaseUnitsMap (K := K) (L := L) a :=
          sum_cyclicGaloisCarryFactor_generator K L hdegree a
    let e := Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)
    let y : Lˣ := Additive.toMul (e (u (cyclicGaloisGenerator K L)))
    have hyinput : e.symm (Additive.ofMul y) = u (cyclicGaloisGenerator K L) := by
      apply e.injective
      simp [y]
    have hyvec := cyclicGaloisRepresentationNorm_eq_baseNorm K L y
    rw [hyinput] at hyvec
    have hbase : cyclicGaloisBaseUnitsMap (K := K) (L := L)
          (Additive.ofMul (Units.map (Algebra.norm K) y)) =
        cyclicGaloisBaseUnitsMap (K := K) (L := L) a :=
      hyvec.symm.trans hsum
    have ha := cyclicGaloisBaseUnitsMap_injective hbase
    exact ⟨y, congrArg Additive.toMul ha⟩
  · rintro ⟨y, hy⟩
    have ha : a = Additive.ofMul (Units.map (Algebra.norm K) y) := by
      apply Additive.toMul.injective
      exact hy.symm
    rw [ha]
    exact cyclicGaloisCarryH2Class_norm_eq_zero K L y

/-- In a nontrivial finite cyclic Galois extension, the carry-class kernel is exactly the
base-field norm image. -/
theorem cyclicGaloisCarryH2Class_eq_zero_iff_mem_normImage_of_one_lt
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (hdegree : 1 < Module.finrank K L) (a : Additive Kˣ) :
    cyclicGaloisCarryH2Class K L a = 0 ↔
      a ∈ cyclicGaloisH2BaseNormImage K L := by
  rw [cyclicGaloisCarryH2Class_eq_zero_iff_exists_norm_of_one_lt K L hdegree a]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Additive.ofMul y, ?_⟩
    apply Additive.toMul.injective
    exact hy
  · rintro ⟨y, hy⟩
    refine ⟨Additive.toMul y, ?_⟩
    exact congrArg Additive.toMul hy

/-- For every finite cyclic Galois extension, including degree one, the explicit carry class
vanishes exactly on field norms. -/
theorem cyclicGaloisCarryH2Class_eq_zero_iff_exists_norm
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (a : Additive Kˣ) :
    cyclicGaloisCarryH2Class K L a = 0 ↔
      ∃ y : Lˣ, Units.map (Algebra.norm K) y = Additive.toMul a := by
  by_cases hdegree : Module.finrank K L = 1
  · constructor
    · intro ha
      refine ⟨Units.map (algebraMap K L) (Additive.toMul a), ?_⟩
      change cyclicGaloisNormUnits K L
          (Units.map (algebraMap K L) (Additive.toMul a)) = Additive.toMul a
      rw [cyclicGaloisNormUnits_algebraMap, hdegree, pow_one]
    · rintro ⟨y, hy⟩
      have ha : a = Additive.ofMul (Units.map (Algebra.norm K) y) := by
        apply Additive.toMul.injective
        exact hy.symm
      rw [ha]
      exact cyclicGaloisCarryH2Class_norm_eq_zero K L y
  · have hdegree' : 1 < Module.finrank K L := by
      have hpos := Module.finrank_pos (R := K) (M := L)
      omega
    exact cyclicGaloisCarryH2Class_eq_zero_iff_exists_norm_of_one_lt
      K L hdegree' a

/-- Unconditional kernel formula: explicit carry classes kill precisely the base-field norm
image in every finite cyclic Galois extension. -/
theorem cyclicGaloisCarryH2Class_eq_zero_iff_mem_normImage
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (a : Additive Kˣ) :
    cyclicGaloisCarryH2Class K L a = 0 ↔
      a ∈ cyclicGaloisH2BaseNormImage K L := by
  rw [cyclicGaloisCarryH2Class_eq_zero_iff_exists_norm K L a]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Additive.ofMul y, ?_⟩
    apply Additive.toMul.injective
    exact hy
  · rintro ⟨y, hy⟩
    refine ⟨Additive.toMul y, ?_⟩
    exact congrArg Additive.toMul hy

/-- Explicit carry classes descend from base units to the field-norm quotient. -/
noncomputable def cyclicGaloisCarryNormQuotientHom
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] :
    Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L →+ cyclicGaloisH2 K L :=
  QuotientAddGroup.lift (cyclicGaloisH2BaseNormImage K L)
    (cyclicGaloisCarryH2ClassHom K L) (by
      intro a ha
      rw [AddMonoidHom.mem_ker]
      rcases ha with ⟨y, rfl⟩
      exact cyclicGaloisCarryH2Class_norm_eq_zero K L (Additive.toMul y))

/-- Quotient computation rule for the explicit carry-class map. -/
@[simp] theorem cyclicGaloisCarryNormQuotientHom_mk
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (a : Additive Kˣ) :
    cyclicGaloisCarryNormQuotientHom K L
        (QuotientAddGroup.mk a) = cyclicGaloisCarryH2Class K L a := rfl

/-- The explicit carry map embeds the field-norm quotient for every finite cyclic Galois
extension. -/
theorem cyclicGaloisCarryNormQuotientHom_injective
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] :
    Function.Injective (cyclicGaloisCarryNormQuotientHom K L) := by
  intro x y hxy
  rw [← sub_eq_zero]
  let z := x - y
  change z = 0
  have hz : cyclicGaloisCarryNormQuotientHom K L z = 0 := by
    change cyclicGaloisCarryNormQuotientHom K L (x - y) = 0
    rw [map_sub, hxy, sub_self]
  revert hz
  induction z using QuotientAddGroup.induction_on with
  | H a =>
      intro hz
      rw [cyclicGaloisCarryNormQuotientHom_mk] at hz
      exact (QuotientAddGroup.eq_zero_iff a).2
        ((cyclicGaloisCarryH2Class_eq_zero_iff_mem_normImage K L a).1 hz)

/-- Whenever the cyclic norm quotient is finite, explicit carry classes give all of degree-two
cohomology, not merely an embedded subgroup. -/
noncomputable def cyclicGaloisCarryNormQuotientEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)] :
    Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ cyclicGaloisH2 K L := by
  let periodic := cyclicGaloisH2BaseNormQuotientEquiv K L
  letI : Finite (cyclicGaloisH2 K L) :=
    Finite.of_injective periodic.symm periodic.symm.injective
  letI := Fintype.ofFinite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)
  letI := Fintype.ofFinite (cyclicGaloisH2 K L)
  apply AddEquiv.ofBijective (cyclicGaloisCarryNormQuotientHom K L)
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨cyclicGaloisCarryNormQuotientHom_injective K L,
    Fintype.card_congr periodic.toEquiv⟩

/-- The finite carry equivalence sends a quotient representative to its literal bar-cocycle
class. -/
@[simp] theorem cyclicGaloisCarryNormQuotientEquiv_mk
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    (a : Additive Kˣ) :
    cyclicGaloisCarryNormQuotientEquiv K L (QuotientAddGroup.mk a) =
      cyclicGaloisCarryH2Class K L a := rfl

/-- If the norm quotient is finite, every cyclic degree-two class has a literal carry-cocycle
representative. -/
theorem cyclicGaloisCarryH2Class_surjective
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)] :
    Function.Surjective (cyclicGaloisCarryH2Class K L) := by
  intro z
  obtain ⟨q, rfl⟩ := (cyclicGaloisCarryNormQuotientEquiv K L).surjective z
  induction q using QuotientAddGroup.induction_on with
  | H a =>
      exact ⟨a, (cyclicGaloisCarryNormQuotientEquiv_mk K L a).symm⟩

/-- Norm-quotient transition transported through literal carry-cocycle coordinates. -/
noncomputable def cyclicGaloisH2CarryNormQuotientTransition
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K M)] :
    cyclicGaloisH2 K L →+ cyclicGaloisH2 K M :=
  (cyclicGaloisCarryNormQuotientEquiv K M).toAddMonoidHom.comp
    ((cyclicGaloisH2BaseNormQuotientTransition K L M).comp
      (cyclicGaloisCarryNormQuotientEquiv K L).symm.toAddMonoidHom)

/-- Carry-normalized tower transition raises the represented base parameter to the relative
degree. -/
@[simp] theorem cyclicGaloisH2CarryNormQuotientTransition_carryClass
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K M)]
    (a : Additive Kˣ) :
    cyclicGaloisH2CarryNormQuotientTransition K L M
        (cyclicGaloisCarryH2Class K L a) =
      cyclicGaloisCarryH2Class K M (Module.finrank L M • a) := by
  change cyclicGaloisCarryNormQuotientEquiv K M
      (cyclicGaloisH2BaseNormQuotientTransition K L M
        ((cyclicGaloisCarryNormQuotientEquiv K L).symm
          (cyclicGaloisCarryH2Class K L a))) = _
  rw [← cyclicGaloisCarryNormQuotientEquiv_mk K L a]
  rw [AddEquiv.symm_apply_apply]
  rw [cyclicGaloisH2BaseNormQuotientTransition_mk]
  exact cyclicGaloisCarryNormQuotientEquiv_mk K M (Module.finrank L M • a)

/-- Carry-normalized transition on an identity tower is the identity. -/
theorem cyclicGaloisH2CarryNormQuotientTransition_self
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)] :
    cyclicGaloisH2CarryNormQuotientTransition K L L = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨a, rfl⟩ := cyclicGaloisCarryH2Class_surjective K L z
  rw [cyclicGaloisH2CarryNormQuotientTransition_carryClass]
  simp

/-- Carry-normalized transitions compose through every finite cyclic tower. -/
theorem cyclicGaloisH2CarryNormQuotientTransition_comp
    (K L M N : Type) [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
    [Algebra L M] [Algebra L N] [Algebra M N]
    [IsScalarTower K L M] [IsScalarTower K L N]
    [IsScalarTower K M N] [IsScalarTower L M N]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K N]
    [FiniteDimensional L M] [FiniteDimensional L N] [FiniteDimensional M N]
    [IsGalois K L] [IsGalois K M] [IsGalois K N]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] [IsCyclic Gal(N/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K M)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K N)] :
    (cyclicGaloisH2CarryNormQuotientTransition K M N).comp
        (cyclicGaloisH2CarryNormQuotientTransition K L M) =
      cyclicGaloisH2CarryNormQuotientTransition K L N := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨a, rfl⟩ := cyclicGaloisCarryH2Class_surjective K L z
  rw [AddMonoidHom.comp_apply]
  rw [cyclicGaloisH2CarryNormQuotientTransition_carryClass]
  rw [cyclicGaloisH2CarryNormQuotientTransition_carryClass]
  rw [cyclicGaloisH2CarryNormQuotientTransition_carryClass]
  rw [← Module.finrank_mul_finrank L M N, ← mul_nsmul]

/-- Periodic-resolution quotient equivalence sends a quotient representative to the abstract
base projection. -/
@[simp] theorem cyclicGaloisH2BaseNormQuotientEquiv_mk
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (a : Additive Kˣ) :
    cyclicGaloisH2BaseNormQuotientEquiv K L (QuotientAddGroup.mk a) =
      cyclicGaloisH2BaseProjection K L a := rfl

/-- On every finite cyclic norm quotient, discrepancy between Mathlib's periodic resolution and
the literal carry cocycle is an automorphism of `H²`. -/
noncomputable def cyclicGaloisH2PeriodicCarryAutomorphism
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)] :
    cyclicGaloisH2 K L ≃+ cyclicGaloisH2 K L :=
  (cyclicGaloisH2BaseNormQuotientEquiv K L).symm.trans
    (cyclicGaloisCarryNormQuotientEquiv K L)

/-- The periodic-to-carry automorphism sends every abstract base projection to its explicit
carry class. -/
@[simp] theorem cyclicGaloisH2PeriodicCarryAutomorphism_baseProjection
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    (a : Additive Kˣ) :
    cyclicGaloisH2PeriodicCarryAutomorphism K L
        (cyclicGaloisH2BaseProjection K L a) =
      cyclicGaloisCarryH2Class K L a := by
  change cyclicGaloisCarryNormQuotientEquiv K L
      ((cyclicGaloisH2BaseNormQuotientEquiv K L).symm
        (cyclicGaloisH2BaseProjection K L a)) = _
  rw [← cyclicGaloisH2BaseNormQuotientEquiv_mk K L a]
  rw [AddEquiv.symm_apply_apply]
  exact cyclicGaloisCarryNormQuotientEquiv_mk K L a

/-- On finite norm quotients, comparison defect is exactly `id - periodicCarryAutomorphism`
applied to the periodic class. -/
theorem cyclicGaloisH2CarryComparisonDefect_eq_id_sub_automorphism
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    (a : Additive Kˣ) :
    cyclicGaloisH2CarryComparisonDefect K L a =
      cyclicGaloisH2BaseProjection K L a -
        cyclicGaloisH2PeriodicCarryAutomorphism K L
          (cyclicGaloisH2BaseProjection K L a) := by
  rw [cyclicGaloisH2CarryComparisonDefect_apply,
    cyclicGaloisH2PeriodicCarryAutomorphism_baseProjection]

/-- Split valuation quotient equivalence evaluates a quotient representative by valuation modulo
the extension degree. -/
@[simp] theorem cyclicGaloisH2BaseNormQuotientSplitValuationEquiv_mk
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ))) (n : ℕ) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hfinrank : Module.finrank K L = n)
    (hval : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) = (tameValHom vL x) ^ n)
    (hzero : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a)
    (a : Additive Kˣ) :
    cyclicGaloisH2BaseNormQuotientSplitValuationEquiv
        K L vK vL n u hu hfinrank hval hzero (QuotientAddGroup.mk a) =
      tameValModNat vK n a := rfl

/-- Literal-cocycle finite local invariant: under split valuation norm classification, explicit
carry classes identify cyclic `H²` with `ℤ/nℤ`. -/
noncomputable def cyclicGaloisCarryH2SplitValuationEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ))) (n : ℕ) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hfinrank : Module.finrank K L = n)
    (hval : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) = (tameValHom vL x) ^ n)
    (hzero : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a) :
    cyclicGaloisH2 K L ≃+ ZMod n := by
  letI : NeZero n := ⟨by rw [← hfinrank]; exact (Module.finrank_pos (R := K) (M := L)).ne'⟩
  let qEquiv := cyclicGaloisH2BaseNormQuotientSplitValuationEquiv
    K L vK vL n u hu hfinrank hval hzero
  letI : Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L) :=
    Finite.of_injective qEquiv qEquiv.injective
  exact (cyclicGaloisCarryNormQuotientEquiv K L).symm.trans qEquiv

/-- Explicit carry parameter is read by the finite local invariant as valuation modulo `n`. -/
@[simp] theorem cyclicGaloisCarryH2SplitValuationEquiv_apply
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ))) (n : ℕ) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hfinrank : Module.finrank K L = n)
    (hval : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) = (tameValHom vL x) ^ n)
    (hzero : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a)
    (a : Additive Kˣ) :
    cyclicGaloisCarryH2SplitValuationEquiv K L vK vL n u hu hfinrank hval hzero
        (cyclicGaloisCarryH2Class K L a) =
      tameValModNat vK n a := by
  letI : NeZero n := ⟨by rw [← hfinrank]; exact (Module.finrank_pos (R := K) (M := L)).ne'⟩
  let qEquiv := cyclicGaloisH2BaseNormQuotientSplitValuationEquiv
    K L vK vL n u hu hfinrank hval hzero
  letI : Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L) :=
    Finite.of_injective qEquiv qEquiv.injective
  change qEquiv ((cyclicGaloisCarryNormQuotientEquiv K L).symm
      (cyclicGaloisCarryH2Class K L a)) = _
  rw [← cyclicGaloisCarryNormQuotientEquiv_mk K L a]
  rw [AddEquiv.symm_apply_apply]
  exact cyclicGaloisH2BaseNormQuotientSplitValuationEquiv_mk
    K L vK vL n u hu hfinrank hval hzero a

end
end GaloisForLFunctions.HTGeometry.ABHN
