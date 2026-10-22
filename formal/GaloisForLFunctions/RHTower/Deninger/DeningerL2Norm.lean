import GaloisForLFunctions.RHTower.Deninger.DeningerL2PlaceSum
import GaloisForLFunctions.RHTower.Deninger.DeningerArchimedeanBaseChange

/-!
# The `L²` place norm and its base change

The `L²` norm of the Kummer function of an algebraic number weights each place by its local degree
over `ℚ`.  At an archimedean place the weight is the multiplicity; at a finite place mathlib's adic
absolute value is the `d`-th power of the one restricting to the standard absolute value on `ℚ`, so
the weighted square is `(log ‖x‖_v)²/d_v`.

Both halves multiply by `[L : K]` under base change — the archimedean one because the fibres of
restriction of complex embeddings have constant size, the finite one by the weighted fibre sum law
— so the norm divided by the absolute degree is an invariant of the algebraic number alone.

* `deningerL2NormSq` : the unnormalized `L²` place norm.
* `deningerL2FinsumBaseChange` : base change for the finite part.
* `deningerL2NormSq_baseChange`, `deningerNormalizedL2_baseChange` : base change for the whole
  norm, and independence of the field of definition after normalizing by the degree.
-/

namespace RHTower

open NumberField Module

section L2Norm

variable {K : Type*} [Field K] [NumberField K]

/-- The unnormalized `L²` place norm: archimedean places weighted by multiplicity, finite places
weighted by the reciprocal of the local degree. -/
noncomputable def deningerL2NormSq (x : K) : ℝ :=
  (∑ v : InfinitePlace K, (v.mult : ℝ) * (Real.log (v x)) ^ (2 : ℕ))
    + ∑ᶠ w : FinitePlace K, (Real.log (w x)) ^ (2 : ℕ) / (deningerPlaceDegree w : ℝ)

/-- The local degree of a finite place is positive. -/
theorem deningerPlaceDegree_pos (w : FinitePlace K) : 0 < deningerPlaceDegree w := by
  haveI : (Ideal.under ℤ w.maximalIdeal.asIdeal).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime (Ideal.under_ne_bot ℤ w.maximalIdeal.ne_bot)
      (Ideal.IsPrime.under ℤ w.maximalIdeal.asIdeal)
  refine Nat.pos_of_ne_zero (Nat.mul_ne_zero ?_ (Ideal.inertiaDeg'_ne_zero _ _))
  exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.maximalIdeal.asIdeal
    (Ideal.under_ne_bot ℤ w.maximalIdeal.ne_bot)

end L2Norm

section BaseChange

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem deningerL2Pow_ne_one {t : ℝ} (ht : 0 < t) (ht1 : t ≠ 1) {n : ℕ} (hn : n ≠ 0) :
    t ^ n ≠ 1 := by
  intro h
  have hlog : (n : ℝ) * Real.log t = 0 := by rw [← Real.log_pow, h, Real.log_one]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hzero := (mul_eq_zero.mp hlog).resolve_left hn'
  refine ht1 ?_
  have hexp := congrArg Real.exp hzero
  rwa [Real.exp_log ht, Real.exp_zero] at hexp

/-- **Base change for the finite part of the `L²` norm.** -/
theorem deningerL2FinsumBaseChange {x : K} (hx : x ≠ 0) :
    ∑ᶠ w : FinitePlace L,
        (Real.log (w (algebraMap K L x))) ^ (2 : ℕ) / (deningerPlaceDegree w : ℝ)
      = (finrank K L : ℝ)
          * ∑ᶠ v : FinitePlace K, (Real.log (v x)) ^ (2 : ℕ) / (deningerPlaceDegree v : ℝ) := by
  classical
  have hxL : algebraMap K L x ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hx
  set SL : Finset (FinitePlace L) := (FinitePlace.hasFiniteMulSupport hxL).toFinset with hSL
  set SK : Finset (FinitePlace K) := (FinitePlace.hasFiniteMulSupport hx).toFinset with hSK
  have hmemSL : ∀ w : FinitePlace L, w ∈ SL ↔ w (algebraMap K L x) ≠ 1 := by
    intro w
    simp [hSL, Function.mulSupport]
  have hmemSK : ∀ v : FinitePlace K, v ∈ SK ↔ v x ≠ 1 := by
    intro v
    simp [hSK, Function.mulSupport]
  have hsubL : Function.support (fun w : FinitePlace L =>
      (Real.log (w (algebraMap K L x))) ^ (2 : ℕ) / (deningerPlaceDegree w : ℝ))
      ⊆ (SL : Set (FinitePlace L)) := by
    intro w hw
    by_contra hwS
    refine hw ?_
    show (Real.log (w (algebraMap K L x))) ^ (2 : ℕ) / (deningerPlaceDegree w : ℝ) = 0
    have hone : w (algebraMap K L x) = 1 := by
      by_contra hne
      exact hwS (Finset.mem_coe.mpr ((hmemSL w).mpr hne))
    rw [hone, Real.log_one]
    simp
  have hsubK : Function.support (fun v : FinitePlace K =>
      (Real.log (v x)) ^ (2 : ℕ) / (deningerPlaceDegree v : ℝ)) ⊆ (SK : Set (FinitePlace K)) := by
    intro v hv
    by_contra hvS
    refine hv ?_
    show (Real.log (v x)) ^ (2 : ℕ) / (deningerPlaceDegree v : ℝ) = 0
    have hone : v x = 1 := by
      by_contra hne
      exact hvS (Finset.mem_coe.mpr ((hmemSK v).mpr hne))
    rw [hone, Real.log_one]
    simp
  have hmaps : ∀ w ∈ SL, deningerRestrictPlace (K := K) w ∈ SK := by
    intro w hw
    refine (hmemSK _).mpr fun hcon => ?_
    have hval := deningerFinitePlace_apply (K := K) w x
    rw [hcon, one_pow] at hval
    exact (hmemSL w).mp hw hval
  have hfib : ∀ v ∈ SK, SL.filter (fun w => deningerRestrictPlace (K := K) w = v)
      = deningerPlacesOver (L := L) v := by
    intro v hv
    ext w
    rw [Finset.mem_filter, deningerMem_placesOver]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    refine (hmemSL w).mpr ?_
    have hval := deningerFinitePlace_apply (K := K) w x
    rw [h] at hval
    rw [hval]
    exact deningerL2Pow_ne_one (FinitePlace.pos_iff.mpr hx) ((hmemSK v).mp hv)
      (deningerLocalDegree_ne_zero (K := K) w)
  rw [finsum_eq_finsetSum_of_support_subset _ hsubL,
    finsum_eq_finsetSum_of_support_subset _ hsubK,
    ← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [hfib v hv, deningerL2FibreSum v x]

/-- **Base change for the `L²` place norm.**  Computing it in an extension multiplies it by the
degree, exactly as for the height. -/
theorem deningerL2NormSq_baseChange {x : K} (hx : x ≠ 0) :
    deningerL2NormSq (algebraMap K L x) = (finrank K L : ℝ) * deningerL2NormSq x := by
  rw [deningerL2NormSq, deningerL2NormSq, mul_add,
    ← deningerArchPlaceSum_baseChange (fun t => (Real.log t) ^ (2 : ℕ)) x,
    ← deningerL2FinsumBaseChange hx]

/-- **The normalized `L²` norm does not depend on the field of definition.** -/
theorem deningerNormalizedL2_baseChange {x : K} (hx : x ≠ 0) :
    deningerL2NormSq (algebraMap K L x) / (finrank ℚ L : ℝ)
      = deningerL2NormSq x / (finrank ℚ K : ℝ) := by
  have htower : finrank ℚ L = finrank ℚ K * finrank K L :=
    (Module.finrank_mul_finrank ℚ K L).symm
  have hK : (finrank ℚ K : ℝ) ≠ 0 := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    positivity
  have hKL : (finrank K L : ℝ) ≠ 0 := by
    have := Module.finrank_pos (R := K) (M := L)
    positivity
  rw [deningerL2NormSq_baseChange hx, htower]
  push_cast
  field_simp

end BaseChange

end RHTower
