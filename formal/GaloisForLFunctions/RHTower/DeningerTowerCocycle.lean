import GaloisForLFunctions.RHTower.DeningerTowerTransition

/-!
# The transition maps compose: the tower is a direct system

Restriction of places is transitive — the prime under a prime under a prime is the prime under it,
and composing the structure maps composes the pullbacks of infinite places — and the local degrees
are multiplicative in a tower.  Hence the weighted pullbacks compose: the transition map of a
two-step tower is the composite of the two one-step transition maps.

That is the cocycle condition, so the test spaces of the place spaces of a tower of number fields
form a direct system, with the logarithmic Kummer functions as a compatible family.

* `deningerPlaceRestrict_trans` : restriction of places is transitive.
* `deningerPlaceDegreeOver_tower` : **the local degrees are multiplicative in a tower.**
* `deningerTowerPull_trans` : **the transition maps compose.**
-/

namespace RHTower

open NumberField NumberField.InfinitePlace IsDedekindDomain Module

section RestrictTrans

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

omit [NumberField K] [NumberField L] [NumberField M] in
theorem deningerInfinitePlaceRestrict_trans (w : InfinitePlace M) :
    (w.comap (algebraMap L M)).comap (algebraMap K L) = w.comap (algebraMap K M) := by
  rw [IsScalarTower.algebraMap_eq K L M]
  rfl

theorem deningerRestrictPlace_trans (w : FinitePlace M) :
    deningerRestrictPlace (K := K) (deningerRestrictPlace (K := L) w)
      = deningerRestrictPlace (K := K) w := by
  show FinitePlace.mk
      (deningerUnderSpectrum (K := K) (deningerRestrictPlace (K := L) w).maximalIdeal)
    = FinitePlace.mk (deningerUnderSpectrum (K := K) w.maximalIdeal)
  rw [deningerRestrictPlace_maximalIdeal]
  congr 1
  exact HeightOneSpectrum.ext (Ideal.under_under _)

theorem deningerPlaceRestrict_trans (w : DeningerPlace M) :
    deningerPlaceRestrict K L (deningerPlaceRestrict L M w) = deningerPlaceRestrict K M w := by
  cases w with
  | inl w => exact congrArg Sum.inl (deningerInfinitePlaceRestrict_trans w)
  | inr w => exact congrArg Sum.inr (deningerRestrictPlace_trans w)

end RestrictTrans

section DegreeTower

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

omit [NumberField K] [NumberField L] [NumberField M] in
/-- **The archimedean local degrees are multiplicative in a tower.** -/
theorem deningerArchDegree_tower (w : InfinitePlace M) :
    deningerArchDegreeOver (K := K) w
      = deningerArchDegreeOver (K := L) w
        * deningerArchDegreeOver (K := K) (w.comap (algebraMap L M)) := by
  have hcomap := deningerInfinitePlaceRestrict_trans (K := K) (L := L) w
  have hbase : deningerArchDegreeOver (K := K) w
      * (w.comap (algebraMap K M)).mult = w.mult := deningerArchDegree_mul (K := K) w
  have hstep : deningerArchDegreeOver (K := L) w
      * (w.comap (algebraMap L M)).mult = w.mult := deningerArchDegree_mul (K := L) w
  have hlow : deningerArchDegreeOver (K := K) (w.comap (algebraMap L M))
      * ((w.comap (algebraMap L M)).comap (algebraMap K L)).mult
      = (w.comap (algebraMap L M)).mult := deningerArchDegree_mul (K := K) _
  rw [hcomap] at hlow
  have hpos : 0 < (w.comap (algebraMap K M)).mult := mult_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [hbase, mul_assoc, hlow, hstep]

/-- **The finite local degrees are multiplicative in a tower.** -/
theorem deningerFiniteDegree_tower (w : FinitePlace M) :
    deningerFiniteDegreeOver (K := K) w
      = deningerFiniteDegreeOver (K := K) (deningerRestrictPlace (K := L) w)
        * deningerFiniteDegreeOver (K := L) w := by
  classical
  set Q : Ideal (𝓞 M) := w.maximalIdeal.asIdeal with hQ
  set P : Ideal (𝓞 L) := Q.under (𝓞 L) with hP
  set p : Ideal (𝓞 K) := P.under (𝓞 K) with hp
  have hQbot : Q ≠ ⊥ := w.maximalIdeal.ne_bot
  haveI hQprime : Q.IsPrime := w.maximalIdeal.isPrime
  have hPbot : P ≠ ⊥ := Ideal.under_ne_bot (𝓞 L) hQbot
  have hpbot : p ≠ ⊥ := Ideal.under_ne_bot (𝓞 K) hPbot
  haveI hPprime : P.IsPrime := Ideal.IsPrime.under (𝓞 L) Q
  haveI hpprime : p.IsPrime := Ideal.IsPrime.under (𝓞 K) P
  haveI hPmax : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hPbot hPprime
  haveI hpmax : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hpbot hpprime
  haveI hPover : P.LiesOver p := Ideal.over_under P
  haveI hQover : Q.LiesOver P := Ideal.over_under Q
  have hg0 : Ideal.map (algebraMap (𝓞 L) (𝓞 M)) P ≠ ⊥ := by
    intro hbot
    refine hPbot ?_
    have hinj : Function.Injective (algebraMap (𝓞 L) (𝓞 M)) :=
      RingOfIntegers.algebraMap.injective L M
    exact (Ideal.map_eq_bot_iff_of_injective hinj).mp hbot
  have hfg : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) p ≠ ⊥ := by
    intro hbot
    refine hpbot ?_
    have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 M)) :=
      RingOfIntegers.algebraMap.injective K M
    exact (Ideal.map_eq_bot_iff_of_injective hinj).mp hbot
  have htower : deningerLocalDegree p Q = deningerLocalDegree p P * deningerLocalDegree P Q :=
    deningerLocalDegree_tower hg0 hfg
  have hunder : Q.under (𝓞 K) = p := (Ideal.under_under Q).symm
  show deningerLocalDegree (Q.under (𝓞 K)) Q
    = deningerLocalDegree
        ((deningerRestrictPlace (K := L) w).maximalIdeal.asIdeal.under (𝓞 K))
        (deningerRestrictPlace (K := L) w).maximalIdeal.asIdeal
      * deningerLocalDegree P Q
  rw [deningerRestrictPlace_maximalIdeal, deningerUnderSpectrum_asIdeal, hunder, ← hP, ← hp,
    htower]

/-- **The local degrees of the place space are multiplicative in a tower.** -/
theorem deningerPlaceDegreeOver_tower (w : DeningerPlace M) :
    deningerPlaceDegreeOver K M w
      = deningerPlaceDegreeOver K L (deningerPlaceRestrict L M w)
        * deningerPlaceDegreeOver L M w := by
  cases w with
  | inl w =>
    show deningerArchDegreeOver (K := K) w
      = deningerArchDegreeOver (K := K) (w.comap (algebraMap L M))
        * deningerArchDegreeOver (K := L) w
    rw [deningerArchDegree_tower (K := K) (L := L) w, mul_comm]
  | inr w =>
    show deningerFiniteDegreeOver (K := K) w
      = deningerFiniteDegreeOver (K := K) (deningerRestrictPlace (K := L) w)
        * deningerFiniteDegreeOver (K := L) w
    exact deningerFiniteDegree_tower (K := K) (L := L) w

end DegreeTower

section PullTrans

variable (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

/-- **The transition maps of the tower compose**: pulling a test function from `K` to `L` and then
to `M` is pulling it from `K` to `M`.  So the place test spaces of a tower of number fields form a
direct system. -/
theorem deningerTowerPull_trans (f : DeningerTestSpace (DeningerPlace K)) :
    deningerTowerPull L M (deningerTowerPull K L f) = deningerTowerPull K M f := by
  refine Subtype.ext (funext fun w => ?_)
  show (deningerPlaceDegreeOver L M w : ℝ)
      * ((deningerPlaceDegreeOver K L (deningerPlaceRestrict L M w) : ℝ)
        * (f : DeningerPlace K → ℝ)
          (deningerPlaceRestrict K L (deningerPlaceRestrict L M w)))
    = (deningerPlaceDegreeOver K M w : ℝ)
      * (f : DeningerPlace K → ℝ) (deningerPlaceRestrict K M w)
  rw [deningerPlaceRestrict_trans, deningerPlaceDegreeOver_tower (K := K) (L := L) w,
    Nat.cast_mul, ← mul_assoc, mul_comm ((deningerPlaceDegreeOver L M w : ℝ))]

end PullTrans

end RHTower
