import GaloisForLFunctions.RHTower.DeningerTestPushforward
import GaloisForLFunctions.RHTower.DeningerLocalDegree
import GaloisForLFunctions.RHTower.DeningerArchimedeanBaseChange

/-!
# The transition maps of the tower of place spaces

A place of the extension sits over a place of the base with a local degree: for a finite place it
is `e·f`, for an infinite place it is the ratio of the multiplicities, which is `2` exactly when a
real place becomes complex.  Weighting the pullback of a test function by that degree gives the
transition map of the tower of place spaces, and the fibre sums of the degrees are the degree of
the extension — the fundamental identity for the finite places, a double count of complex
embeddings for the infinite ones.

The logarithmic Kummer functions are compatible with these transition maps: the Kummer function of
an element of the base, computed over the extension, is the weighted pullback of the Kummer
function computed over the base.  So the Kummer functions of a tower of number fields form a
direct system, and the transition maps multiply the mass by the degree, which is why the
normalized mass is the invariant of the tower.

* `deningerArchDegreeOver`, `deningerFiniteDegreeOver` : the local degrees.
* `deningerArchDegree_fibre_sum`, `deningerFiniteDegree_fibre_sum` : **the fibre sums are
  `[L : K]`.**
* `deningerTowerPull` : **the transition map of the tower.**
* `deningerKummerFun_tower` : **the Kummer functions form a direct system.**
* `deningerTowerPull_sum` : **the transition map multiplies the mass by `[L : K]`.**
-/

namespace RHTower

open NumberField NumberField.InfinitePlace IsDedekindDomain Module

section ArchDegree

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The local degree of an infinite place over its restriction: the ratio of the
multiplicities. -/
noncomputable def deningerArchDegreeOver (w : InfinitePlace L) : ℕ :=
  w.mult / (w.comap (algebraMap K L)).mult

omit [NumberField K] [NumberField L] in
theorem deningerArchMult_dvd (w : InfinitePlace L) :
    (w.comap (algebraMap K L)).mult ∣ w.mult := by
  classical
  by_cases hv : (w.comap (algebraMap K L)).IsReal
  · simp [InfinitePlace.mult, hv]
  · have hwc : w.IsComplex :=
      InfinitePlace.IsComplex.of_comap _ (not_isReal_iff_isComplex.mp hv)
    have hw : ¬ w.IsReal := not_isReal_iff_isComplex.mpr hwc
    simp [InfinitePlace.mult, hv, hw]

omit [NumberField K] [NumberField L] in
/-- **The multiplicity of a place of the extension is the local degree times the multiplicity of
its restriction.** -/
theorem deningerArchDegree_mul (w : InfinitePlace L) :
    deningerArchDegreeOver (K := K) w * (w.comap (algebraMap K L)).mult = w.mult :=
  Nat.div_mul_cancel (deningerArchMult_dvd w)

open scoped Classical in
/-- **The multiplicities of the places above an infinite place add up to `[L : K]` times the
multiplicity below**: both sides count the complex embeddings of `L` restricting into the place
below. -/
theorem deningerArchMult_fibre_sum (v : InfinitePlace K) :
    ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace L => w.comap (algebraMap K L) = v), w.mult
      = v.mult * finrank K L := by
  classical
  set T : Finset (InfinitePlace L) :=
    Finset.univ.filter (fun w : InfinitePlace L => w.comap (algebraMap K L) = v) with hT
  set S : Finset (L →+* ℂ) :=
    Finset.univ.filter (fun ψ : L →+* ℂ => (mk ψ).comap (algebraMap K L) = v) with hS
  set U : Finset (K →+* ℂ) := Finset.univ.filter (fun φ : K →+* ℂ => mk φ = v) with hU
  have hmaps1 : ∀ ψ ∈ S, mk ψ ∈ T := by
    intro ψ hψ
    have := (Finset.mem_filter.mp hψ).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩
  have h1 : S.card = ∑ w ∈ T, (S.filter (fun ψ : L →+* ℂ => mk ψ = w)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps1
  have h1' : ∀ w ∈ T, (S.filter (fun ψ : L →+* ℂ => mk ψ = w)).card = w.mult := by
    intro w hw
    have hfilter : S.filter (fun ψ : L →+* ℂ => mk ψ = w)
        = Finset.univ.filter (fun ψ : L →+* ℂ => mk ψ = w) := by
      ext ψ
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨-, hmk⟩
        exact hmk
      · intro hmk
        refine ⟨?_, hmk⟩
        rw [hmk]
        exact (Finset.mem_filter.mp hw).2
    rw [hfilter, card_filter_mk_eq]
  have hmaps2 : ∀ ψ ∈ S, ψ.comp (algebraMap K L) ∈ U := by
    intro ψ hψ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hmk := (Finset.mem_filter.mp hψ).2
    rwa [comap_mk] at hmk
  have h2 : S.card
      = ∑ φ ∈ U, (S.filter (fun ψ : L →+* ℂ => ψ.comp (algebraMap K L) = φ)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps2
  have h2' : ∀ φ ∈ U,
      (S.filter (fun ψ : L →+* ℂ => ψ.comp (algebraMap K L) = φ)).card = finrank K L := by
    intro φ hφ
    have hfilter : S.filter (fun ψ : L →+* ℂ => ψ.comp (algebraMap K L) = φ)
        = Finset.univ.filter (fun ψ : L →+* ℂ => ψ.comp (algebraMap K L) = φ) := by
      ext ψ
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨-, hcomp⟩
        exact hcomp
      · intro hcomp
        refine ⟨?_, hcomp⟩
        rw [comap_mk, hcomp]
        exact (Finset.mem_filter.mp hφ).2
    rw [hfilter]
    exact deningerEmbeddingFibre_card (L := L) φ
  rw [Finset.sum_congr rfl h1'] at h1
  rw [Finset.sum_congr rfl h2', Finset.sum_const, smul_eq_mul] at h2
  have hU' : U.card = v.mult := card_filter_mk_eq v
  rw [hU'] at h2
  rw [← h1, h2]

open scoped Classical in
/-- **The local degrees of the infinite places above a place add up to `[L : K]`.** -/
theorem deningerArchDegree_fibre_sum (v : InfinitePlace K) :
    ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace L => w.comap (algebraMap K L) = v),
        deningerArchDegreeOver (K := K) w = finrank K L := by
  classical
  set T : Finset (InfinitePlace L) :=
    Finset.univ.filter (fun w : InfinitePlace L => w.comap (algebraMap K L) = v) with hT
  have hterm : ∀ w ∈ T, deningerArchDegreeOver (K := K) w * v.mult = w.mult := by
    intro w hw
    have hv : w.comap (algebraMap K L) = v := (Finset.mem_filter.mp hw).2
    have h := deningerArchDegree_mul (K := K) w
    rwa [hv] at h
  have hsum : (∑ w ∈ T, deningerArchDegreeOver (K := K) w) * v.mult = finrank K L * v.mult := by
    rw [Finset.sum_mul, Finset.sum_congr rfl hterm, deningerArchMult_fibre_sum (L := L) v,
      mul_comm]
  exact Nat.eq_of_mul_eq_mul_right mult_pos hsum

end ArchDegree

section FiniteDegree

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The local degree of a finite place over its restriction: `e·f`. -/
noncomputable def deningerFiniteDegreeOver (w : FinitePlace L) : ℕ :=
  deningerLocalDegree (deningerUnderSpectrum (K := K) w.maximalIdeal).asIdeal
    w.maximalIdeal.asIdeal

/-- **The local degrees of the finite places above a place add up to `[L : K]`**, the fundamental
identity. -/
theorem deningerFiniteDegree_fibre_sum (v : FinitePlace K) :
    ∑ w ∈ deningerPlacesOver (L := L) v, deningerFiniteDegreeOver (K := K) w = finrank K L := by
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
  rw [deningerPlacesOver, Finset.sum_image hinj]
  have hterm : ∀ P ∈ (IsDedekindDomain.primesOverFinset v.maximalIdeal.asIdeal (𝓞 L)).attach,
      deningerFiniteDegreeOver (K := K) (FinitePlace.mk (deningerSpectrumOfMem P.2))
        = deningerLocalDegree v.maximalIdeal.asIdeal (P : Ideal (𝓞 L)) := by
    intro P _
    have hlies := deningerSpectrumOfMem_liesOver (v := v.maximalIdeal) P.2
    have hunder : (deningerSpectrumOfMem (v := v.maximalIdeal) P.2).asIdeal.under (𝓞 K)
        = v.maximalIdeal.asIdeal := ((Ideal.liesOver_iff _ _).mp hlies).symm
    rw [deningerFiniteDegreeOver, FinitePlace.maximalIdeal_mk,
      show deningerUnderSpectrum (deningerSpectrumOfMem (v := v.maximalIdeal) P.2)
        = v.maximalIdeal from HeightOneSpectrum.ext hunder]
    rfl
  rw [Finset.sum_congr rfl hterm, Finset.sum_attach _
    (fun P : Ideal (𝓞 L) => deningerLocalDegree v.maximalIdeal.asIdeal P)]
  exact deningerLocalDegree_sum (L := L) v.maximalIdeal

end FiniteDegree

section TowerPull

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The local degree of a place of the extension over its restriction. -/
noncomputable def deningerPlaceDegreeOver : DeningerPlace L → ℕ :=
  Sum.elim (fun w : InfinitePlace L => deningerArchDegreeOver (K := K) w)
    (fun w : FinitePlace L => deningerFiniteDegreeOver (K := K) w)

omit [NumberField K] in
@[simp] theorem deningerPlaceDegreeOver_inl (w : InfinitePlace L) :
    deningerPlaceDegreeOver K L (Sum.inl w : DeningerPlace L)
      = deningerArchDegreeOver (K := K) w := rfl

omit [NumberField K] in
@[simp] theorem deningerPlaceDegreeOver_inr (w : FinitePlace L) :
    deningerPlaceDegreeOver K L (Sum.inr w : DeningerPlace L)
      = deningerFiniteDegreeOver (K := K) w := rfl

/-- **The fibres of the restriction of places are finite.** -/
theorem deningerPlaceRestrict_preimage_finite {S : Set (DeningerPlace K)} (hS : S.Finite) :
    (deningerPlaceRestrict K L ⁻¹' S).Finite := by
  classical
  have hfin : (Sum.inr ⁻¹' S : Set (FinitePlace K)).Finite := hS.preimage Sum.inr_injective.injOn
  have hcover : deningerPlaceRestrict K L ⁻¹' S
      ⊆ Set.range (Sum.inl : InfinitePlace L → DeningerPlace L)
        ∪ Sum.inr '' (⋃ v ∈ (Sum.inr ⁻¹' S : Set (FinitePlace K)),
            (deningerPlacesOver (L := L) v : Set (FinitePlace L))) := by
    rintro (w | w) hw
    · exact Or.inl ⟨w, rfl⟩
    · refine Or.inr ⟨w, ?_, rfl⟩
      have hmem : deningerRestrictPlace (K := K) w ∈ (Sum.inr ⁻¹' S : Set (FinitePlace K)) := hw
      exact Set.mem_biUnion hmem
        (Finset.mem_coe.mpr ((deningerMem_placesOver (L := L) _ w).mpr rfl))
  refine Set.Finite.subset (Set.Finite.union ?_ ?_) hcover
  · exact Set.finite_range _
  · exact Set.Finite.image _ (hfin.biUnion fun v _ => (deningerPlacesOver (L := L) v).finite_toSet)

/-- **The transition map of the tower**, on functions: the pullback along the restriction of
places, weighted by the local degree. -/
noncomputable def deningerTowerPullFun (f : DeningerTestSpace (DeningerPlace K)) :
    DeningerPlace L → ℝ :=
  fun w => (deningerPlaceDegreeOver K L w : ℝ)
    * (f : DeningerPlace K → ℝ) (deningerPlaceRestrict K L w)

theorem deningerTowerPullFun_mem (f : DeningerTestSpace (DeningerPlace K)) :
    deningerTowerPullFun K L f ∈ DeningerTestSpace (DeningerPlace L) := by
  refine ⟨IsLocallyConstant.of_discrete _, ?_⟩
  refine Set.Finite.isCompact (Set.Finite.subset
    (deningerPlaceRestrict_preimage_finite K L (f.2.2.finite_of_discrete)) ?_)
  intro w hw
  by_contra hmem
  refine hw ?_
  show (deningerPlaceDegreeOver K L w : ℝ)
    * (f : DeningerPlace K → ℝ) (deningerPlaceRestrict K L w) = 0
  have hzero : (f : DeningerPlace K → ℝ) (deningerPlaceRestrict K L w) = 0 := by
    by_contra hne
    exact hmem hne
  rw [hzero, mul_zero]

/-- **The transition map of the tower of place spaces.** -/
noncomputable def deningerTowerPull :
    DeningerTestSpace (DeningerPlace K) →ₗ[ℝ] DeningerTestSpace (DeningerPlace L) where
  toFun f := ⟨deningerTowerPullFun K L f, deningerTowerPullFun_mem K L f⟩
  map_add' f g := by
    refine Subtype.ext (funext fun w => ?_)
    show (deningerPlaceDegreeOver K L w : ℝ)
        * ((f : DeningerPlace K → ℝ) (deningerPlaceRestrict K L w)
          + (g : DeningerPlace K → ℝ) (deningerPlaceRestrict K L w))
      = (deningerPlaceDegreeOver K L w : ℝ)
          * (f : DeningerPlace K → ℝ) (deningerPlaceRestrict K L w)
        + (deningerPlaceDegreeOver K L w : ℝ)
          * (g : DeningerPlace K → ℝ) (deningerPlaceRestrict K L w)
    ring
  map_smul' c f := by
    refine Subtype.ext (funext fun w => ?_)
    show (deningerPlaceDegreeOver K L w : ℝ)
        * (c * (f : DeningerPlace K → ℝ) (deningerPlaceRestrict K L w))
      = c * ((deningerPlaceDegreeOver K L w : ℝ)
          * (f : DeningerPlace K → ℝ) (deningerPlaceRestrict K L w))
    ring

theorem deningerTowerPull_apply (f : DeningerTestSpace (DeningerPlace K)) :
    ((deningerTowerPull K L f : DeningerTestSpace (DeningerPlace L)) : DeningerPlace L → ℝ)
      = deningerTowerPullFun K L f := rfl

end TowerPull

section KummerTower

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The logarithmic Kummer functions form a direct system along the tower**: the Kummer function
of an element of the base, computed over the extension, is the weighted pullback of the Kummer
function computed over the base. -/
theorem deningerKummerFun_tower (α : K) (w : DeningerPlace L) :
    deningerKummerFun L (algebraMap K L α) w
      = (deningerPlaceDegreeOver K L w : ℝ)
        * deningerKummerFun K α (deningerPlaceRestrict K L w) := by
  cases w with
  | inl w =>
    show (w.mult : ℝ) * Real.log (w (algebraMap K L α))
      = (deningerArchDegreeOver (K := K) w : ℝ)
        * (((w.comap (algebraMap K L)).mult : ℝ) * Real.log ((w.comap (algebraMap K L)) α))
    have hval : w (algebraMap K L α) = (w.comap (algebraMap K L)) α := rfl
    have hmult : (deningerArchDegreeOver (K := K) w : ℝ)
        * ((w.comap (algebraMap K L)).mult : ℝ) = (w.mult : ℝ) := by
      rw [← Nat.cast_mul, deningerArchDegree_mul]
    rw [hval, ← mul_assoc, hmult]
  | inr w =>
    show Real.log (w (algebraMap K L α))
      = (deningerFiniteDegreeOver (K := K) w : ℝ)
        * Real.log (deningerRestrictPlace (K := K) w α)
    rw [deningerFinitePlace_apply, Real.log_pow]
    rfl

end KummerTower

section TowerMass

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The fibre sum of the local degrees over a place of the base is `[L : K]`. -/
theorem deningerPlaceDegree_fibre_sum (v : DeningerPlace K) :
    ∑ᶠ w ∈ deningerPlaceRestrict K L ⁻¹' {v}, (deningerPlaceDegreeOver K L w : ℝ)
      = (finrank K L : ℝ) := by
  classical
  cases v with
  | inl v =>
    have hbij : Set.BijOn (Sum.inl : InfinitePlace L → DeningerPlace L)
        {w : InfinitePlace L | w.comap (algebraMap K L) = v}
        (deningerPlaceRestrict K L ⁻¹' {Sum.inl v}) := by
      refine ⟨?_, ?_, ?_⟩
      · intro w hw
        have hval : deningerPlaceRestrict K L (Sum.inl w) = Sum.inl v := congrArg Sum.inl hw
        exact hval
      · intro w _ u _ h
        exact Sum.inl_injective h
      · rintro (u | u) hu
        · have hval : deningerPlaceRestrict K L (Sum.inl u) = Sum.inl v := hu
          have hcomap : u.comap (algebraMap K L) = v := Sum.inl_injective hval
          exact ⟨u, hcomap, rfl⟩
        · have hval : deningerPlaceRestrict K L (Sum.inr u) = Sum.inl v := hu
          exact absurd hval (by simp [deningerPlaceRestrict])
    have hfin : {w : InfinitePlace L | w.comap (algebraMap K L) = v}
        = (Finset.univ.filter (fun w : InfinitePlace L => w.comap (algebraMap K L) = v) :
            Finset (InfinitePlace L)) := by
      ext w
      simp
    calc ∑ᶠ w ∈ deningerPlaceRestrict K L ⁻¹' {Sum.inl v},
            (deningerPlaceDegreeOver K L w : ℝ)
        = ∑ᶠ w ∈ {w : InfinitePlace L | w.comap (algebraMap K L) = v},
            (deningerArchDegreeOver (K := K) w : ℝ) :=
          (finsum_mem_eq_of_bijOn Sum.inl hbij fun w _ => rfl).symm
      _ = (finrank K L : ℝ) := by
          rw [hfin, finsum_mem_coe_finset, ← Nat.cast_sum,
            deningerArchDegree_fibre_sum (K := K) (L := L) v]
  | inr v =>
    have hbij : Set.BijOn (Sum.inr : FinitePlace L → DeningerPlace L)
        (deningerPlacesOver (L := L) v : Set (FinitePlace L))
        (deningerPlaceRestrict K L ⁻¹' {Sum.inr v}) := by
      refine ⟨?_, ?_, ?_⟩
      · intro w hw
        have hres : deningerRestrictPlace (K := K) w = v :=
          (deningerMem_placesOver (L := L) v w).mp (Finset.mem_coe.mp hw)
        have hval : deningerPlaceRestrict K L (Sum.inr w) = Sum.inr v := congrArg Sum.inr hres
        exact hval
      · intro w _ u _ h
        exact Sum.inr_injective h
      · rintro (u | u) hu
        · have hval : deningerPlaceRestrict K L (Sum.inl u) = Sum.inr v := hu
          exact absurd hval (by simp [deningerPlaceRestrict])
        · have hval : deningerPlaceRestrict K L (Sum.inr u) = Sum.inr v := hu
          have hres : deningerRestrictPlace (K := K) u = v := Sum.inr_injective hval
          exact ⟨u, Finset.mem_coe.mpr ((deningerMem_placesOver (L := L) v u).mpr hres), rfl⟩
    calc ∑ᶠ w ∈ deningerPlaceRestrict K L ⁻¹' {Sum.inr v},
            (deningerPlaceDegreeOver K L w : ℝ)
        = ∑ᶠ w ∈ (deningerPlacesOver (L := L) v : Set (FinitePlace L)),
            (deningerFiniteDegreeOver (K := K) w : ℝ) :=
          (finsum_mem_eq_of_bijOn Sum.inr hbij fun w _ => rfl).symm
      _ = (finrank K L : ℝ) := by
          rw [finsum_mem_coe_finset, ← Nat.cast_sum,
            deningerFiniteDegree_fibre_sum (K := K) (L := L) v]

/-- **The projection of a transition is the degree**: pushing the weighted pullback of a test
function forward again multiplies it by `[L : K]`. -/
theorem deningerPush_towerPull (f : DeningerTestSpace (DeningerPlace K)) (v : DeningerPlace K) :
    deningerPushFun (deningerPlaceRestrict K L) (deningerTowerPull K L f) v
      = (finrank K L : ℝ) * (f : DeningerPlace K → ℝ) v := by
  have hterm : ∀ w ∈ deningerPlaceRestrict K L ⁻¹' {v},
      ((deningerTowerPull K L f : DeningerTestSpace (DeningerPlace L)) : DeningerPlace L → ℝ) w
        = (deningerPlaceDegreeOver K L w : ℝ) * (f : DeningerPlace K → ℝ) v := by
    intro w hw
    have hwv : deningerPlaceRestrict K L w = v := hw
    show (deningerPlaceDegreeOver K L w : ℝ)
      * (f : DeningerPlace K → ℝ) (deningerPlaceRestrict K L w) = _
    rw [hwv]
  rw [deningerPushFun, finsum_mem_congr rfl hterm, ← finsum_mem_mul,
    deningerPlaceDegree_fibre_sum]

/-- **The transition map multiplies the mass by the degree of the extension.**  So the mass
divided by the absolute degree is the invariant of the tower. -/
theorem deningerTowerPull_sum (f : DeningerTestSpace (DeningerPlace K)) :
    deningerPlaceSum L (deningerTowerPull K L f) = (finrank K L : ℝ) * deningerPlaceSum K f := by
  have hmass := deningerPush_mass (deningerPlaceRestrict K L) (deningerTowerPull K L f)
  rw [deningerPlaceSum_eq_finsum, ← hmass, deningerPlaceSum_eq_finsum]
  have hfun : ∀ v, ((deningerPush (deningerPlaceRestrict K L) (deningerTowerPull K L f) :
        DeningerTestSpace (DeningerPlace K)) : DeningerPlace K → ℝ) v
      = (finrank K L : ℝ) * (f : DeningerPlace K → ℝ) v :=
    deningerPush_towerPull K L f
  rw [finsum_congr hfun, ← mul_finsum]

end TowerMass

end RHTower
