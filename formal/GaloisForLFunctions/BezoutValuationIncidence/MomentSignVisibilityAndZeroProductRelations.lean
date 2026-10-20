import GaloisForLFunctions.BezoutValuationIncidence.GaloisInvarianceAndTranslationClosureAtEveryLag
import GaloisForLFunctions.BezoutValuationIncidence.TrapezoidWindowSandwichAtQuadraticOrder
import GaloisForLFunctions.BiScaleUncertainty.CubicSievePhaseRecovery

/-!
# Sign visibility of translated moments and zero-product relations

Averaging `Π_{i<m} s(k + v_i)` over the factorial period keeps exactly the tuples of response
frequencies whose product is one:

`M_m(c; v) = Σ_{ζ ∈ T_N^m, Π ζ_i = 1} Π_i Y(ord ζ_i) ζ_i^{v_i}`.

The multi-characters `v ↦ Π_i ζ_i^{v_i}` of distinct tuples are linearly independent, so the
coefficients of distinct zero-product tuples are read separately by the full array of degree-`m`
moments. Rescaling the Selberg coordinates by `ε(q)` multiplies the coefficient of a tuple by
`Π_i ε(ord ζ_i)`. Hence:

**Sign visibility law.** The degree-`m` translated moments of the rows with coordinates `Y` and
`εY` agree for all shifts iff every zero-product `m`-tuple of active frequencies has
`Π_i ε(ord ζ_i) = 1`.

Every sign pattern is invisible to two-point data, since `ζ₁ ζ₂ = 1` forces equal orders. The
sign of `Y(q)` at an odd order `q ≥ 3` is seen by the third moments through the relation
`ζ · ζ · ζ^{q-2} = 1`. A relative sign between two modes is seen exactly at the least length of a
zero-product relation that uses an odd number of frequencies of one of them.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. Spectral form of the translated moments -/

/-- **Spectral form of the translated moments.** Only zero-product tuples survive the period
average. -/
theorem translatedMoment_eq_spectral (N : ℕ) (c : ℕ → ℝ) {m : ℕ} (v : Fin m → ℕ) :
    (SieveMoments.translatedMoment N c v : ℂ) =
      ∑ ζ ∈ (Fintype.piFinset fun _ : Fin m => responseRoots N).filter (fun ζ => ∏ i, ζ i = 1),
        ∏ i, (selbergMultiplesCoord N c (orderOf (ζ i)) : ℂ) * ζ i ^ v i := by
  classical
  set T := Fintype.piFinset fun _ : Fin m => responseRoots N
  have hprod : ∀ n : ℕ, (∏ i, (sieveSeq N c (n + v i) : ℂ)) =
      ∑ ζ ∈ T, (∏ i, (selbergMultiplesCoord N c (orderOf (ζ i)) : ℂ) * ζ i ^ v i) *
        (∏ i, ζ i) ^ n := by
    intro n
    simp_rw [sieveSeq_eq_sum_responseRoots]
    rw [prod_univ_sum]
    refine sum_congr rfl fun ζ _ => ?_
    rw [← prod_pow, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    rw [pow_add]
    ring
  have hP : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  unfold SieveMoments.translatedMoment
  push_cast
  simp_rw [hprod]
  rw [sum_comm, sum_div, sum_filter]
  refine sum_congr rfl fun ζ hζ => ?_
  rw [← mul_sum]
  split_ifs with h1
  · rw [h1]
    simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
    field_simp
  · have hpow : (∏ i, ζ i) ^ N.factorial = 1 := by
      rw [← prod_pow]
      exact prod_eq_one fun i _ =>
        pow_factorial_eq_one_of_mem_responseRoots ((Fintype.mem_piFinset.mp hζ) i)
    rw [geom_sum_eq h1, hpow, sub_self, zero_div, mul_zero, zero_div]

/-! ## §2. Independence of multi-characters -/

/-- The multi-character `v ↦ Π_i ζ_i^{v_i}` of a tuple of frequencies. -/
def multiCharacter {m : ℕ} (ζ : Fin m → ℂ) : Multiplicative (Fin m → ℕ) →* ℂ where
  toFun v := ∏ i, ζ i ^ (Multiplicative.toAdd v) i
  map_one' := by simp
  map_mul' v w := by
    simp only [toAdd_mul, Pi.add_apply, pow_add, prod_mul_distrib]

theorem multiCharacter_apply {m : ℕ} (ζ : Fin m → ℂ) (v : Fin m → ℕ) :
    multiCharacter ζ (Multiplicative.ofAdd v) = ∏ i, ζ i ^ v i := rfl

theorem multiCharacter_injective {m : ℕ} : Function.Injective (multiCharacter (m := m)) := by
  classical
  intro ζ ξ h
  funext j
  have hj := DFunLike.congr_fun h (Multiplicative.ofAdd (Pi.single j 1))
  rw [multiCharacter_apply, multiCharacter_apply] at hj
  have key : ∀ η : Fin m → ℂ, ∏ i, η i ^ (Pi.single j 1 : Fin m → ℕ) i = η j := by
    intro η
    rw [show (fun i => η i ^ (Pi.single j 1 : Fin m → ℕ) i) = fun i => if i = j then η i else 1 by
      funext i
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]]
    rw [prod_ite_eq']
    simp
  rwa [key, key] at hj

/-- Distinct tuples have independent multi-characters. -/
theorem eq_zero_of_sum_multiCharacter_eq_zero {m : ℕ} (S : Finset (Fin m → ℂ))
    (a : (Fin m → ℂ) → ℂ) (h : ∀ v : Fin m → ℕ, ∑ ζ ∈ S, a ζ * ∏ i, ζ i ^ v i = 0) :
    ∀ ζ ∈ S, a ζ = 0 := by
  have hli : LinearIndependent ℂ fun ζ : Fin m → ℂ =>
      (⇑(multiCharacter ζ) : Multiplicative (Fin m → ℕ) → ℂ) :=
    (linearIndependent_monoidHom (Multiplicative (Fin m → ℕ)) ℂ).comp _ multiCharacter_injective
  refine linearIndependent_iff'.mp hli S a ?_
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  exact h (Multiplicative.toAdd x)

/-! ## §3. The sign visibility law -/

/-- The row with Selberg coordinates `ε(q) Y(q)`. -/
def scaledSelbergRow (N : ℕ) (c : ℕ → ℝ) (ε : ℕ → ℝ) : ℕ → ℝ :=
  RHTower.pmRamanujanResidueCoeff (fun q => ε q * selbergMultiplesCoord N c q) N

theorem selbergMultiplesCoord_scaledSelbergRow {N q : ℕ} (c : ℕ → ℝ) (ε : ℕ → ℝ)
    (hq : q ∈ Icc 1 N) :
    selbergMultiplesCoord N (scaledSelbergRow N c ε) q = ε q * selbergMultiplesCoord N c q :=
  RHTower.pmRamanujanResidueCoeff_multiples _ (mem_Icc.mp hq).1 (mem_Icc.mp hq).2

/-- **Sign visibility law.** The degree-`m` translated moments of `Y` and `εY` agree at every shift
iff every zero-product `m`-tuple of response frequencies has `Π Y (1 - Π ε) = 0`. -/
theorem translatedMoment_scaled_eq_iff (N : ℕ) (c : ℕ → ℝ) (ε : ℕ → ℝ) (m : ℕ) :
    (∀ v : Fin m → ℕ, SieveMoments.translatedMoment N (scaledSelbergRow N c ε) v =
        SieveMoments.translatedMoment N c v) ↔
      ∀ ζ ∈ Fintype.piFinset (fun _ : Fin m => responseRoots N), ∏ i, ζ i = 1 →
        (∏ i, selbergMultiplesCoord N c (orderOf (ζ i))) *
          (1 - ∏ i, ε (orderOf (ζ i))) = 0 := by
  classical
  set S := (Fintype.piFinset fun _ : Fin m => responseRoots N).filter (fun ζ => ∏ i, ζ i = 1)
  have hcoord : ∀ ζ ∈ S, ∀ i, selbergMultiplesCoord N (scaledSelbergRow N c ε) (orderOf (ζ i)) =
      ε (orderOf (ζ i)) * selbergMultiplesCoord N c (orderOf (ζ i)) := fun ζ hζ i =>
    selbergMultiplesCoord_scaledSelbergRow c ε
      (orderOf_mem_Icc_of_mem_responseRoots ((Fintype.mem_piFinset.mp (mem_filter.mp hζ).1) i))
  -- the difference of the two moment arrays, tuple by tuple
  have hdiff : ∀ v : Fin m → ℕ,
      ((SieveMoments.translatedMoment N (scaledSelbergRow N c ε) v -
        SieveMoments.translatedMoment N c v : ℝ) : ℂ) =
      ∑ ζ ∈ S, (((∏ i, selbergMultiplesCoord N c (orderOf (ζ i))) *
        ((∏ i, ε (orderOf (ζ i))) - 1) : ℝ) : ℂ) * ∏ i, ζ i ^ v i := by
    intro v
    rw [Complex.ofReal_sub, translatedMoment_eq_spectral, translatedMoment_eq_spectral,
      ← sum_sub_distrib]
    refine sum_congr rfl fun ζ hζ => ?_
    simp only [hcoord ζ hζ]
    push_cast
    simp only [prod_mul_distrib]
    ring
  constructor
  · intro hall ζ hζ hprod
    have hzero := eq_zero_of_sum_multiCharacter_eq_zero S _ fun v => by
      rw [← hdiff v, hall v, sub_self, Complex.ofReal_zero]
    have h := hzero ζ (mem_filter.mpr ⟨hζ, hprod⟩)
    have h' : (∏ i, selbergMultiplesCoord N c (orderOf (ζ i))) *
        ((∏ i, ε (orderOf (ζ i))) - 1) = 0 := by exact_mod_cast h
    linear_combination -h'
  · intro hall v
    have h := hdiff v
    rw [sum_eq_zero fun ζ hζ => ?_] at h
    · exact sub_eq_zero.mp (by exact_mod_cast h)
    · have hz := hall ζ (mem_filter.mp hζ).1 (mem_filter.mp hζ).2
      have : (∏ i, selbergMultiplesCoord N c (orderOf (ζ i))) *
          ((∏ i, ε (orderOf (ζ i))) - 1) = 0 := by linear_combination -hz
      rw [this, Complex.ofReal_zero, zero_mul]

/-! ## §4. Two-point blindness and odd-order visibility -/

/-- Two-point data are blind to every sign pattern. -/
theorem translatedMoment_two_scaled_eq (N : ℕ) (c : ℕ → ℝ) {ε : ℕ → ℝ}
    (hε : ∀ q, ε q * ε q = 1) (v : Fin 2 → ℕ) :
    SieveMoments.translatedMoment N (scaledSelbergRow N c ε) v =
      SieveMoments.translatedMoment N c v := by
  refine (translatedMoment_scaled_eq_iff N c ε 2).mpr (fun ζ _ hprod => ?_) v
  rw [Fin.prod_univ_two] at hprod ⊢
  have hord : orderOf (ζ 1) = orderOf (ζ 0) := by
    rw [orderOf_eq_orderOf_iff]
    intro n
    have h := congrArg (· ^ n) hprod
    simp only [mul_pow, one_pow] at h
    constructor
    · intro h1
      rwa [h1, mul_one] at h
    · intro h0
      rwa [h0, one_mul] at h
  simp only [Fin.prod_univ_two, hord, hε, sub_self, mul_zero]

/-- **Odd orders are seen at degree three.** If `q ≥ 3` is odd and `Y(q) ≠ 0`, flipping the sign of
the single mode `q` changes some third translated moment. -/
theorem exists_translatedMoment_three_ne_of_odd {N q : ℕ} (hq : q ∈ Icc 3 N) (hodd : Odd q)
    (c : ℕ → ℝ) (hY : selbergMultiplesCoord N c q ≠ 0) :
    ∃ v : Fin 3 → ℕ, SieveMoments.translatedMoment N
        (scaledSelbergRow N c fun r => if r = q then -1 else 1) v ≠
      SieveMoments.translatedMoment N c v := by
  by_contra hall
  push Not at hall
  have hq' := mem_Icc.mp hq
  have hq0 : 0 < q := by omega
  have hζ := Complex.isPrimitiveRoot_exp q hq0.ne'
  set ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑q)
  have hcop : Nat.Coprime (q - 2) q := by
    have hodd2 : Odd (q - 2) := by
      obtain ⟨t, ht⟩ := hodd
      exact ⟨t - 1, by omega⟩
    have h := Nat.coprime_two_right.mpr hodd2
    have hq2 : q = 2 + (q - 2) := by omega
    rw [Nat.Coprime]
    nth_rewrite 2 [hq2]
    rw [Nat.gcd_add_self_right]
    exact h
  have hξ := hζ.pow_of_coprime (q - 2) hcop
  have hqI : q ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, hq'.2⟩
  set τ : Fin 3 → ℂ := ![ζ, ζ, ζ ^ (q - 2)]
  have hτ : τ ∈ Fintype.piFinset (fun _ : Fin 3 => responseRoots N) := by
    refine Fintype.mem_piFinset.mpr fun i => ?_
    fin_cases i
    · exact primitiveRoot_mem_responseRoots hqI hζ
    · exact primitiveRoot_mem_responseRoots hqI hζ
    · exact primitiveRoot_mem_responseRoots hqI hξ
  have hprod : ∏ i, τ i = 1 := by
    rw [Fin.prod_univ_three]
    simp only [τ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [← pow_two, ← pow_add, show 2 + (q - 2) = q by omega, hζ.pow_eq_one]
  have h := (translatedMoment_scaled_eq_iff N c _ 3).mp hall τ hτ hprod
  have hord : ∀ i, orderOf (τ i) = q := by
    intro i
    fin_cases i
    · exact hζ.eq_orderOf.symm
    · exact hζ.eq_orderOf.symm
    · exact hξ.eq_orderOf.symm
  simp only [hord, prod_const, card_univ, Fintype.card_fin, if_true] at h
  have hY3 : selbergMultiplesCoord N c q ^ 3 ≠ 0 := pow_ne_zero 3 hY
  norm_num at h
  exact hY h

end

end GaloisForLFunctions.BezoutValuationIncidence
