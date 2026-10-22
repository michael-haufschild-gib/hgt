import GaloisForLFunctions.RHTower.Deninger.DeningerFinitePlaceSumBaseChange
import Mathlib.NumberTheory.Height.NumberField

/-!
# Restriction of finite places along a field extension

A finite place of `L` restricts to a finite place of `K`: take the prime under its maximal ideal.
The restricted place computes the same absolute value up to the local degree, and the fibre of the
restriction over a place `v` is exactly the set of primes above `v`.

* `deningerUnderSpectrum`, `deningerRestrictPlace` : the restriction.
* `deningerFinitePlace_apply` : the value law `‖x‖_w = ‖x‖_v ^ (e·f)`.
* `deningerPlacesOver` : the fibre, as a finite set of places of `L`.
* `deningerMem_placesOver` : the fibre is the set of places restricting to `v`.
-/

namespace RHTower

open NumberField IsDedekindDomain Module

section PlaceRestriction

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The height-one prime of the base under a height-one prime of the extension. -/
noncomputable def deningerUnderSpectrum (w : HeightOneSpectrum (𝓞 L)) :
    HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.under (𝓞 K)
  isPrime := Ideal.IsPrime.under (𝓞 K) w.asIdeal
  ne_bot := Ideal.under_ne_bot (𝓞 K) w.ne_bot

omit [NumberField K] [NumberField L] in
@[simp] theorem deningerUnderSpectrum_asIdeal (w : HeightOneSpectrum (𝓞 L)) :
    (deningerUnderSpectrum (K := K) w).asIdeal = w.asIdeal.under (𝓞 K) := rfl

omit [NumberField K] [NumberField L] in
instance deningerUnderSpectrum_liesOver (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (deningerUnderSpectrum (K := K) w).asIdeal :=
  (Ideal.over_under w.asIdeal : w.asIdeal.LiesOver (w.asIdeal.under (𝓞 K)))

/-- The finite place of the base below a finite place of the extension. -/
noncomputable def deningerRestrictPlace (w : FinitePlace L) : FinitePlace K :=
  FinitePlace.mk (deningerUnderSpectrum w.maximalIdeal)

@[simp] theorem deningerRestrictPlace_maximalIdeal (w : FinitePlace L) :
    (deningerRestrictPlace (K := K) w).maximalIdeal = deningerUnderSpectrum w.maximalIdeal :=
  FinitePlace.maximalIdeal_mk _

/-- A finite place is the adic absolute value of its maximal ideal. -/
theorem deningerFinitePlace_eq_adicAbv (w : FinitePlace K) (x : K) :
    w x = HeightOneSpectrum.adicAbv K w.maximalIdeal x := by
  rw [← FinitePlace.norm_embedding_eq w x,
    FinitePlace.norm_embedding (R := 𝓞 K) (v := w.maximalIdeal) x]

/-- **The value law.**  A finite place of `L` evaluated at an element of `K` is the restricted
place raised to the local degree. -/
theorem deningerFinitePlace_apply (w : FinitePlace L) (x : K) :
    w (algebraMap K L x)
      = (deningerRestrictPlace (K := K) w x)
          ^ ((deningerUnderSpectrum (K := K) w.maximalIdeal).asIdeal.ramificationIdx'
                w.maximalIdeal.asIdeal
              * (deningerUnderSpectrum (K := K) w.maximalIdeal).asIdeal.inertiaDeg'
                  w.maximalIdeal.asIdeal) := by
  rw [deningerFinitePlace_eq_adicAbv, deningerFinitePlace_eq_adicAbv,
    deningerRestrictPlace_maximalIdeal,
    deningerAdicAbv_liesOver (deningerUnderSpectrum (K := K) w.maximalIdeal) w.maximalIdeal x]

open scoped Classical in
/-- The fibre of the restriction over a finite place `v` of the base. -/
noncomputable def deningerPlacesOver (v : FinitePlace K) : Finset (FinitePlace L) :=
  (IsDedekindDomain.primesOverFinset v.maximalIdeal.asIdeal (𝓞 L)).attach.image
    (fun P => FinitePlace.mk (deningerSpectrumOfMem P.2))

/-- **The fibre is the set of places restricting to `v`.** -/
theorem deningerMem_placesOver (v : FinitePlace K) (w : FinitePlace L) :
    w ∈ deningerPlacesOver (L := L) v ↔ deningerRestrictPlace (K := K) w = v := by
  haveI : v.maximalIdeal.asIdeal.IsMaximal := v.maximalIdeal.isMaximal
  constructor
  · intro hw
    simp only [deningerPlacesOver, Finset.mem_image] at hw
    obtain ⟨P, -, hP⟩ := hw
    have hlies := deningerSpectrumOfMem_liesOver (v := v.maximalIdeal) P.2
    rw [← hP, deningerRestrictPlace, FinitePlace.maximalIdeal_mk]
    have : (deningerSpectrumOfMem (v := v.maximalIdeal) P.2).asIdeal.under (𝓞 K)
        = v.maximalIdeal.asIdeal := ((Ideal.liesOver_iff _ _).mp hlies).symm
    rw [show deningerUnderSpectrum (deningerSpectrumOfMem (v := v.maximalIdeal) P.2)
        = v.maximalIdeal from HeightOneSpectrum.ext this, FinitePlace.mk_maximalIdeal]
  · intro hw
    simp only [deningerPlacesOver, Finset.mem_image]
    have hmem : w.maximalIdeal.asIdeal
        ∈ IsDedekindDomain.primesOverFinset v.maximalIdeal.asIdeal (𝓞 L) := by
      refine (IsDedekindDomain.mem_primesOverFinset_iff v.maximalIdeal.ne_bot (𝓞 L)).mpr ?_
      refine ⟨w.maximalIdeal.isPrime, ?_⟩
      refine (Ideal.liesOver_iff _ _).mpr ?_
      have := congrArg FinitePlace.maximalIdeal hw
      rw [deningerRestrictPlace_maximalIdeal] at this
      exact (congrArg HeightOneSpectrum.asIdeal this).symm
    exact ⟨⟨w.maximalIdeal.asIdeal, hmem⟩, Finset.mem_attach _ _, FinitePlace.mk_maximalIdeal w⟩

/-- The local degree of a place of `L` over its restriction is nonzero. -/
theorem deningerLocalDegree_ne_zero (w : FinitePlace L) :
    (deningerUnderSpectrum (K := K) w.maximalIdeal).asIdeal.ramificationIdx'
        w.maximalIdeal.asIdeal
      * (deningerUnderSpectrum (K := K) w.maximalIdeal).asIdeal.inertiaDeg'
        w.maximalIdeal.asIdeal ≠ 0 := by
  haveI : (deningerUnderSpectrum (K := K) w.maximalIdeal).asIdeal.IsMaximal :=
    (deningerUnderSpectrum (K := K) w.maximalIdeal).isMaximal
  refine Nat.mul_ne_zero ?_ (Ideal.inertiaDeg'_ne_zero _ _)
  exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.maximalIdeal.asIdeal
    (deningerUnderSpectrum (K := K) w.maximalIdeal).ne_bot

/-- **The fibre sum law for places.**  Summing a homogeneous function of the absolute value over
the places of `L` above `v` multiplies it by `[L : K]`. -/
theorem deningerPlacesOver_sum (F : ℝ → ℝ) (hF : ∀ (n : ℕ) (t : ℝ), F (t ^ n) = n * F t)
    (v : FinitePlace K) (x : K) :
    ∑ w ∈ deningerPlacesOver (L := L) v, F (w (algebraMap K L x))
      = (finrank K L : ℝ) * F (v x) := by
  classical
  haveI : v.maximalIdeal.asIdeal.IsMaximal := v.maximalIdeal.isMaximal
  have hinj : ∀ P ∈ (IsDedekindDomain.primesOverFinset v.maximalIdeal.asIdeal (𝓞 L)).attach,
      ∀ Q ∈ (IsDedekindDomain.primesOverFinset v.maximalIdeal.asIdeal (𝓞 L)).attach,
      (FinitePlace.mk (deningerSpectrumOfMem P.2) : FinitePlace L)
          = FinitePlace.mk (deningerSpectrumOfMem Q.2) → P = Q := by
    intro P _ Q _ h
    have := congrArg FinitePlace.maximalIdeal h
    rw [FinitePlace.maximalIdeal_mk, FinitePlace.maximalIdeal_mk] at this
    exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal this)
  rw [deningerPlacesOver, Finset.sum_image hinj, deningerFinitePlace_eq_adicAbv v x,
    ← deningerFinitePlaceSum_baseChange F hF v.maximalIdeal x]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [deningerFinitePlace_eq_adicAbv, FinitePlace.maximalIdeal_mk]

/-- A positive real different from one has no power equal to one. -/
private theorem deningerPow_ne_one {t : ℝ} (ht : 0 < t) (ht1 : t ≠ 1) {n : ℕ} (hn : n ≠ 0) :
    t ^ n ≠ 1 := by
  intro h
  have hlog : (n : ℝ) * Real.log t = 0 := by rw [← Real.log_pow, h, Real.log_one]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hzero := (mul_eq_zero.mp hlog).resolve_left hn'
  refine ht1 ?_
  have hexp := congrArg Real.exp hzero
  rwa [Real.exp_log ht, Real.exp_zero] at hexp

/-- **The base-change law for the finite part.**  The full sum over the finite places of `L` of a
homogeneous function of the absolute value of an element of `K` is `[L : K]` times the
corresponding sum over the finite places of `K`. -/
theorem deningerFinitePlaceFinsum_baseChange (F : ℝ → ℝ)
    (hF : ∀ (n : ℕ) (t : ℝ), F (t ^ n) = n * F t) (hF1 : F 1 = 0) {x : K} (hx : x ≠ 0) :
    ∑ᶠ w : FinitePlace L, F (w (algebraMap K L x))
      = (finrank K L : ℝ) * ∑ᶠ v : FinitePlace K, F (v x) := by
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
  have hsubL : Function.support (fun w : FinitePlace L => F (w (algebraMap K L x)))
      ⊆ (SL : Set (FinitePlace L)) := by
    intro w hw
    by_contra hwS
    refine hw ?_
    show F (w (algebraMap K L x)) = 0
    have hone : w (algebraMap K L x) = 1 := by
      by_contra hne
      exact hwS (Finset.mem_coe.mpr ((hmemSL w).mpr hne))
    rw [hone, hF1]
  have hsubK : Function.support (fun v : FinitePlace K => F (v x))
      ⊆ (SK : Set (FinitePlace K)) := by
    intro v hv
    by_contra hvS
    refine hv ?_
    show F (v x) = 0
    have hone : v x = 1 := by
      by_contra hne
      exact hvS (Finset.mem_coe.mpr ((hmemSK v).mpr hne))
    rw [hone, hF1]
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
    exact deningerPow_ne_one (FinitePlace.pos_iff.mpr hx) ((hmemSK v).mp hv)
      (deningerLocalDegree_ne_zero (K := K) w)
  rw [finsum_eq_finsetSum_of_support_subset _ hsubL,
    finsum_eq_finsetSum_of_support_subset _ hsubK,
    ← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [hfib v hv, deningerPlacesOver_sum F hF v x]

end PlaceRestriction

end RHTower
