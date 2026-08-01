import GaloisForLFunctions.RHTower.DeningerPlaceDegree

/-!
# The weighted fibre sum for the `L²` place norm

The `L²` norm on the place space weights a place by its local degree over `ℚ` and divides the
logarithm of mathlib's adic absolute value by that same degree, because that absolute value is the
`d`-th power of the one restricting to the standard absolute value on `ℚ`.

The resulting summand `(log ‖x‖_w)²/d_w` depends on the place and not only on its value, so the
fibrewise law needs the local degrees themselves: on the fibre over `v` the value contributes
`(d_{w/v})²` and the weight contributes `1/(d_v · d_{w/v})`, leaving `d_{w/v}`, whose fibre sum is
the degree of the extension.

* `deningerRelDegree` : the relative local degree of a place over its restriction.
* `deningerRelDegree_sum` : its fibre sum is `[L : K]`.
* `deningerL2FibreSum` : the weighted fibre sum law.
-/

namespace RHTower

open NumberField IsDedekindDomain Module

section RelDegree

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The relative local degree of a finite place of `L` over its restriction to `K`. -/
noncomputable def deningerRelDegree (w : FinitePlace L) : ℕ :=
  deningerLocalDegree (Ideal.under (𝓞 K) w.maximalIdeal.asIdeal) w.maximalIdeal.asIdeal

/-- **The relative local degrees above a place sum to the degree of the extension.** -/
theorem deningerRelDegree_sum (v : FinitePlace K) :
    ∑ w ∈ deningerPlacesOver (L := L) v, deningerRelDegree (K := K) w = finrank K L := by
  classical
  haveI : v.maximalIdeal.asIdeal.IsMaximal := v.maximalIdeal.isMaximal
  have hinj : ∀ P ∈ (IsDedekindDomain.primesOverFinset v.maximalIdeal.asIdeal (𝓞 L)).attach,
      ∀ Q ∈ (IsDedekindDomain.primesOverFinset v.maximalIdeal.asIdeal (𝓞 L)).attach,
      (FinitePlace.mk (deningerSpectrumOfMem P.2) : FinitePlace L)
          = FinitePlace.mk (deningerSpectrumOfMem Q.2) → P = Q := by
    intro P _ Q _ h
    have hm := congrArg FinitePlace.maximalIdeal h
    rw [FinitePlace.maximalIdeal_mk, FinitePlace.maximalIdeal_mk] at hm
    exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal hm)
  rw [deningerPlacesOver, Finset.sum_image hinj]
  have hterm : ∀ P ∈ (IsDedekindDomain.primesOverFinset v.maximalIdeal.asIdeal (𝓞 L)).attach,
      deningerRelDegree (K := K) (FinitePlace.mk (deningerSpectrumOfMem P.2))
        = deningerLocalDegree v.maximalIdeal.asIdeal P.1 := by
    intro P _
    have hlies := deningerSpectrumOfMem_liesOver (v := v.maximalIdeal) P.2
    have hunder : Ideal.under (𝓞 K) P.1 = v.maximalIdeal.asIdeal :=
      ((Ideal.liesOver_iff _ _).mp hlies).symm
    rw [deningerRelDegree, FinitePlace.maximalIdeal_mk, deningerSpectrumOfMem_asIdeal, hunder]
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_attach _ (fun P => deningerLocalDegree v.maximalIdeal.asIdeal P),
    deningerLocalDegree_sum (L := L) v.maximalIdeal]

/-- The value law in terms of the relative local degree. -/
theorem deningerFinitePlace_apply_relDegree (w : FinitePlace L) (x : K) :
    w (algebraMap K L x) = (deningerRestrictPlace (K := K) w x) ^ deningerRelDegree (K := K) w :=
  deningerFinitePlace_apply w x

/-- **The weighted fibre sum law.**  Summing `(log ‖x‖_w)²/d_w` over the places above `v`
multiplies the corresponding quantity at `v` by `[L : K]`. -/
theorem deningerL2FibreSum (v : FinitePlace K) (x : K) :
    ∑ w ∈ deningerPlacesOver (L := L) v,
        (Real.log (w (algebraMap K L x))) ^ 2 / (deningerPlaceDegree w : ℝ)
      = (finrank K L : ℝ) * ((Real.log (v x)) ^ 2 / (deningerPlaceDegree v : ℝ)) := by
  have hdv : (0 : ℝ) < (deningerPlaceDegree v : ℝ) := by
    have hpos : 0 < deningerPlaceDegree v := by
      haveI : (Ideal.under ℤ v.maximalIdeal.asIdeal).IsMaximal :=
        Ring.DimensionLEOne.maximalOfPrime (Ideal.under_ne_bot ℤ v.maximalIdeal.ne_bot)
          (Ideal.IsPrime.under ℤ v.maximalIdeal.asIdeal)
      refine Nat.pos_of_ne_zero (Nat.mul_ne_zero ?_ (Ideal.inertiaDeg'_ne_zero _ _))
      exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v.maximalIdeal.asIdeal
        (Ideal.under_ne_bot ℤ v.maximalIdeal.ne_bot)
    exact_mod_cast hpos
  have hterm : ∀ w ∈ deningerPlacesOver (L := L) v,
      (Real.log (w (algebraMap K L x))) ^ 2 / (deningerPlaceDegree w : ℝ)
        = (deningerRelDegree (K := K) w : ℝ)
            * ((Real.log (v x)) ^ 2 / (deningerPlaceDegree v : ℝ)) := by
    intro w hw
    have hres : deningerRestrictPlace (K := K) w = v := (deningerMem_placesOver v w).mp hw
    have hval := deningerFinitePlace_apply_relDegree (K := K) w x
    rw [hres] at hval
    have hrpos : 0 < deningerRelDegree (K := K) w := by
      haveI : (Ideal.under (𝓞 K) w.maximalIdeal.asIdeal).IsMaximal :=
        Ring.DimensionLEOne.maximalOfPrime (Ideal.under_ne_bot (𝓞 K) w.maximalIdeal.ne_bot)
          (Ideal.IsPrime.under (𝓞 K) w.maximalIdeal.asIdeal)
      refine Nat.pos_of_ne_zero (Nat.mul_ne_zero ?_ (Ideal.inertiaDeg'_ne_zero _ _))
      exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.maximalIdeal.asIdeal
        (Ideal.under_ne_bot (𝓞 K) w.maximalIdeal.ne_bot)
    have hdeg : (deningerPlaceDegree w : ℝ)
        = (deningerPlaceDegree v : ℝ) * (deningerRelDegree (K := K) w : ℝ) := by
      have h := deningerPlaceDegree_tower (K := K) w
      rw [hres] at h
      rw [h, deningerRelDegree]
      push_cast
      ring
    have hrne : ((deningerRelDegree (K := K) w : ℝ)) ≠ 0 := by
      exact_mod_cast hrpos.ne'
    rw [hval, Real.log_pow, hdeg]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  congr 1
  rw [← Nat.cast_sum, deningerRelDegree_sum v]

end RelDegree

end RHTower
