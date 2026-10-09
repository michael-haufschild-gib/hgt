import GaloisForLFunctions.HTGeometry.FinsetCechDatum
import GaloisForLFunctions.HTGeometry.LocalizationAwayDivisibility
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Čech complexes of twisted homogeneous localizations

Let `M = ⊕_i 𝒜_i` be an `ℕ`-graded commutative algebra and `w_i ∈ 𝒜_1` a finite family of linear
forms.  For a finite subset `s` put `w_s = ∏_{i ∈ s} w_i`.  The *degree `-e` part* of the
localization `M[w_s⁻¹]` consists of the fractions `x / w_s^m` with `x ∈ 𝒜_i` and
`i + e = m · #s`; for `e = 0` these are the sections of `𝒪` over `D₊(w_s)` on `Proj M`, and for
general `e` the sections of `𝒪(-e)`.  Restriction along `s ⊆ t` multiplies numerator and
denominator by `w_{t∖s}^m`.

This file builds the corresponding Čech data `twCech 𝒜 w e` together with

* multiplication by a linear form `ℓ ∈ 𝒜_1`, a morphism `twCech (e + 1) → twCech e`
  (the map `𝒪(-e-1) → 𝒪(-e)`);
* the morphism induced by a graded ring map `f : M → M'` carrying `w` to `w'`;

and proves the componentwise exactness of `0 → twCech M (e+1) → twCech M e → twCech M' e → 0`
over every nonempty `s` when `M' = M ⧸ (ℓ)` and `ℓ` is a nonzerodivisor on `M[w_s⁻¹]`: the
middle exactness is the homogeneous projection of `w_s^k x = ℓ z`, surjectivity is the lifting of
homogeneous elements.

* `HTGeometry.twPart`, `HTGeometry.twCech`, `HTGeometry.twMul`, `HTGeometry.twMap`.
* `HTGeometry.twMul_injective`, `HTGeometry.twMap_twMul`, `HTGeometry.twMap_exact`,
  `HTGeometry.twMap_surjective`.
* `HTGeometry.FinsetCechDatum.exactAt_of_bijective`.
-/

namespace HTGeometry

open DirectSum

/-! ## Transport of exactness along an isomorphism of data -/

namespace FinsetCechDatum

variable {T : Type*} [DecidableEq T] [LinearOrder T] {D E : FinsetCechDatum T}

/-- **Exactness transports along a componentwise bijective morphism.** -/
theorem exactAt_of_bijective (φ : Hom D E) (hφ : ∀ s, Function.Bijective (φ.app s)) {p : ℕ}
    (hE : E.ExactAt p) : D.ExactAt p := by
  classical
  intro c hc hdc
  have hc' : E.IsDeg (φ.onCochain c) p := φ.onCochain_isDeg hc
  have hdc' : E.d (φ.onCochain c) = 0 := by rw [φ.d_onCochain, hdc]; funext s; exact map_zero _
  obtain ⟨b, hb, hdb⟩ := hE _ hc' hdc'
  let b' : D.Cochain := fun s => Function.surjInv (hφ s).2 (b s)
  have hb' : φ.onCochain b' = b := funext fun s => Function.surjInv_eq (hφ s).2 (b s)
  refine ⟨b', fun s hs => (hφ s).1 ?_, ?_⟩
  · rw [map_zero]
    exact (congrFun hb' s).trans (hb s hs)
  · funext s
    apply (hφ s).1
    have := congrFun (φ.d_onCochain b') s
    rw [hb', hdb] at this
    exact this.symm

end FinsetCechDatum

universe u

variable {K : Type*} {M : Type u} [CommRing K] [CommRing M] [Algebra K M] (𝒜 : ℕ → Submodule K M)
  [GradedAlgebra 𝒜] {ι : Type*} (w : ι → M)

/-! ## Products of linear forms and fractions -/

/-- The product of the forms indexed by a finite subset. -/
def wProd (s : Finset ι) : M := ∏ i ∈ s, w i

/-- The localization inverting `w_s`. -/
abbrev LocAt (s : Finset ι) := Localization.Away (wProd w s)

variable {𝒜 w}

theorem wProd_mem [DecidableEq ι] (hw : ∀ i, w i ∈ 𝒜 1) (s : Finset ι) : wProd w s ∈ 𝒜 s.card := by
  induction s using Finset.induction_on with
  | empty => exact SetLike.one_mem_graded 𝒜
  | insert a s ha ih =>
    rw [wProd, Finset.prod_insert ha, Finset.card_insert_of_notMem ha, add_comm]
    exact SetLike.mul_mem_graded (hw a) ih

theorem wProd_pow_mem [DecidableEq ι] (hw : ∀ i, w i ∈ 𝒜 1) (s : Finset ι) (m : ℕ) :
    wProd w s ^ m ∈ 𝒜 (m * s.card) := by
  have := SetLike.pow_mem_graded m (wProd_mem hw s)
  rwa [smul_eq_mul] at this

theorem wProd_dvd {s t : Finset ι} (h : s ⊆ t) : wProd w s ∣ wProd w t :=
  Finset.prod_dvd_prod_of_subset _ _ _ h

theorem wProd_sdiff_mul [DecidableEq ι] {s t : Finset ι} (h : s ⊆ t) : wProd w (t \ s) * wProd w s = wProd w t :=
  Finset.prod_sdiff h

variable (w)

/-- The fraction `x / w_s^m`. -/
noncomputable def frac (s : Finset ι) (m : ℕ) (x : M) : LocAt w s :=
  Localization.mk x ⟨wProd w s ^ m, m, rfl⟩

variable {w}

theorem frac_add (s : Finset ι) (m m' : ℕ) (x x' : M) :
    frac w s m x + frac w s m' x' = frac w s (m + m') (wProd w s ^ m * x' + wProd w s ^ m' * x) := by
  rw [frac, frac, frac, Localization.add_mk]
  congr 1
  exact Subtype.ext (by simp [pow_add])

theorem frac_neg (s : Finset ι) (m : ℕ) (x : M) : -frac w s m x = frac w s m (-x) := by
  rw [frac, frac, Localization.neg_mk]

theorem frac_zero (s : Finset ι) (m : ℕ) : frac w s m 0 = 0 := by
  rw [frac, Localization.mk_zero]

theorem frac_mul_pow (s : Finset ι) (m k : ℕ) (x : M) :
    frac w s (m + k) (wProd w s ^ k * x) = frac w s m x := by
  rw [frac, frac, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [pow_add]; ring⟩

theorem algebraMap_mul_frac (s : Finset ι) (m : ℕ) (a x : M) :
    algebraMap M (LocAt w s) a * frac w s m x = frac w s m (a * x) := by
  rw [frac, frac, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul]

/-! ## Twisted parts -/

variable (𝒜 w)

/-- The degree-`-e` fractions over `D₊(w_s)`. -/
def twSet (s : Finset ι) (e : ℕ) : Set (LocAt w s) :=
  {y | ∃ (m i : ℕ) (x : M), x ∈ 𝒜 i ∧ i + e = m * s.card ∧ y = frac w s m x}

/-- **The degree-`-e` part of `M[w_s⁻¹]`**: the sections of `𝒪(-e)` over `D₊(w_s)`. -/
def twPart (s : Finset ι) (e : ℕ) : AddSubgroup (LocAt w s) := AddSubgroup.closure (twSet 𝒜 w s e)

variable {𝒜 w}

omit [GradedAlgebra 𝒜] in
theorem frac_mem_twPart {s : Finset ι} {e m i : ℕ} {x : M} (hx : x ∈ 𝒜 i)
    (hdeg : i + e = m * s.card) : frac w s m x ∈ twPart 𝒜 w s e :=
  AddSubgroup.subset_closure ⟨m, i, x, hx, hdeg, rfl⟩

/-- Over a nonempty subset the degree-`-e` fractions already form a group. -/
noncomputable def twSubgroup [DecidableEq ι] (hw : ∀ i, w i ∈ 𝒜 1) {s : Finset ι} (hs : s.Nonempty) (e : ℕ) :
    AddSubgroup (LocAt w s) where
  carrier := twSet 𝒜 w s e
  zero_mem' := by
    have hcard : 1 ≤ s.card := Finset.card_pos.mpr hs
    refine ⟨e, e * s.card - e, 0, Submodule.zero_mem _, ?_, (frac_zero s e).symm⟩
    have : e ≤ e * s.card := Nat.le_mul_of_pos_right e hcard
    omega
  add_mem' := by
    rintro _ _ ⟨m, i, x, hx, hdeg, rfl⟩ ⟨m', i', x', hx', hdeg', rfl⟩
    refine ⟨m + m', m * s.card + i', _, ?_, ?_, frac_add s m m' x x'⟩
    · refine Submodule.add_mem _ (SetLike.mul_mem_graded (wProd_pow_mem hw s m) hx') ?_
      have : m' * s.card + i = m * s.card + i' := by
        have h1 := hdeg; have h2 := hdeg'
        nlinarith
      rw [← this]
      exact SetLike.mul_mem_graded (wProd_pow_mem hw s m') hx
    · rw [add_mul]
      omega
  neg_mem' := by
    rintro _ ⟨m, i, x, hx, hdeg, rfl⟩
    exact ⟨m, i, -x, Submodule.neg_mem _ hx, hdeg, frac_neg s m x⟩

theorem mem_twPart_iff [DecidableEq ι] (hw : ∀ i, w i ∈ 𝒜 1) {s : Finset ι} (hs : s.Nonempty) {e : ℕ}
    {y : LocAt w s} : y ∈ twPart 𝒜 w s e ↔ y ∈ twSet 𝒜 w s e := by
  constructor
  · intro hy
    exact (AddSubgroup.closure_le (twSubgroup hw hs e)).mpr (fun _ h => h) hy
  · exact fun hy => AddSubgroup.subset_closure hy

/-! ## Restriction -/

section Restriction

variable [DecidableEq ι]

variable (w) in
/-- **Restriction** from `D₊(w_s)` to `D₊(w_t)` for `s ⊆ t`. -/
noncomputable def resLoc {s t : Finset ι} (h : s ⊆ t) : LocAt w s →+* LocAt w t :=
  IsLocalization.Away.lift (wProd w s) (isUnit_algebraMap_of_dvd (wProd_dvd h))

omit [DecidableEq ι] in
theorem resLoc_algebraMap {s t : Finset ι} (h : s ⊆ t) (a : M) :
    resLoc w h (algebraMap M (LocAt w s) a) = algebraMap M (LocAt w t) a :=
  IsLocalization.lift_eq _ a

omit [DecidableEq ι] in
theorem resLoc_comp {s t u : Finset ι} (h₁ : s ⊆ t) (h₂ : t ⊆ u) (y : LocAt w s) :
    resLoc w h₂ (resLoc w h₁ y) = resLoc w (h₁.trans h₂) y := by
  have : (resLoc w h₂).comp (resLoc w h₁) = resLoc w (h₁.trans h₂) :=
    IsLocalization.ringHom_ext (Submonoid.powers (wProd w s)) (by
      ext a
      simp only [RingHom.comp_apply, resLoc_algebraMap])
  exact DFunLike.congr_fun this y

omit [DecidableEq ι] in
theorem resLoc_refl (s : Finset ι) (y : LocAt w s) : resLoc w (Finset.Subset.refl s) y = y := by
  have : resLoc w (Finset.Subset.refl s) = RingHom.id _ :=
    IsLocalization.ringHom_ext (Submonoid.powers (wProd w s)) (by
      ext a
      simp only [RingHom.comp_apply, resLoc_algebraMap, RingHom.id_apply])
  exact DFunLike.congr_fun this y

omit [DecidableEq ι] in
theorem frac_zero_eq (s : Finset ι) (x : M) : frac w s 0 x = algebraMap M (LocAt w s) x := by
  rw [frac, ← Localization.mk_one_eq_algebraMap]
  congr 1
  exact Subtype.ext (pow_zero _)

/-- Restriction of a fraction: numerator and denominator are multiplied by `w_{t∖s}^m`. -/
theorem resLoc_frac {s t : Finset ι} (h : s ⊆ t) (m : ℕ) (x : M) :
    resLoc w h (frac w s m x) = frac w t m (wProd w (t \ s) ^ m * x) := by
  rw [frac, Localization.mk_eq_mk']
  simp only [resLoc, IsLocalization.Away.lift]
  rw [IsLocalization.lift_mk'_spec]
  change algebraMap M (LocAt w t) x
    = algebraMap M (LocAt w t) (wProd w s ^ m) * frac w t m (wProd w (t \ s) ^ m * x)
  rw [algebraMap_mul_frac, ← mul_assoc, ← mul_pow, mul_comm (wProd w s), wProd_sdiff_mul h]
  have := frac_mul_pow (w := w) t 0 m x
  rw [zero_add] at this
  rw [this, frac_zero_eq]

attribute [irreducible] resLoc

theorem resLoc_mem (hw : ∀ i, w i ∈ 𝒜 1) {s t : Finset ι} (h : s ⊆ t) {e : ℕ} {y : LocAt w s}
    (hy : y ∈ twPart 𝒜 w s e) : resLoc w h y ∈ twPart 𝒜 w t e := by
  refine (AddSubgroup.closure_le ((twPart 𝒜 w t e).comap (resLoc w h).toAddMonoidHom)).mpr ?_ hy
  rintro _ ⟨m, i, x, hx, hdeg, rfl⟩
  change resLoc w h (frac w s m x) ∈ twPart 𝒜 w t e
  rw [resLoc_frac]
  refine frac_mem_twPart (SetLike.mul_mem_graded (wProd_pow_mem hw (t \ s) m) hx) ?_
  rw [Finset.card_sdiff_of_subset h]
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (Finset.card_le_card h)
  rw [hc, Nat.add_sub_cancel_left]
  have : m * (s.card + c) = m * s.card + m * c := by ring
  omega

end Restriction

/-! ## The twisted Čech datum -/

section Datum

variable [DecidableEq ι] (hw : ∀ i, w i ∈ 𝒜 1)

variable (𝒜 w) in
/-- **The Čech datum of `𝒪(-e)`** for the cover by the `D₊(w_i)`. -/
noncomputable def twCech (e : ℕ) : FinsetCechDatum ι where
  obj s := twPart 𝒜 w s e
  res h := ((resLoc w h).toAddMonoidHom.comp (twPart 𝒜 w _ e).subtype).codRestrict _
    (fun y => resLoc_mem hw h y.2)
  res_refl s y := Subtype.ext (resLoc_refl s y.1)
  res_res h₁ h₂ y := Subtype.ext (resLoc_comp h₁ h₂ y.1)

/-- The underlying fraction of a section of the twisted datum. -/
def twVal {e : ℕ} {s : Finset ι} (y : (twCech 𝒜 w hw e).obj s) : LocAt w s :=
  (y : twPart 𝒜 w s e).1

theorem twVal_injective {e : ℕ} {s : Finset ι} :
    Function.Injective (twVal (𝒜 := 𝒜) (w := w) hw (e := e) (s := s)) :=
  fun _ _ h => Subtype.ext h

theorem twCech_res_val (e : ℕ) {s t : Finset ι} (h : s ⊆ t) (y : (twCech 𝒜 w hw e).obj s) :
    twVal hw ((twCech 𝒜 w hw e).res h y) = resLoc w h (twVal hw y) := rfl

end Datum

/-! ## Multiplication by a linear form -/

section Mul

variable [DecidableEq ι] (hw : ∀ i, w i ∈ 𝒜 1) {ℓ : M} (hℓ : ℓ ∈ 𝒜 1)

omit [DecidableEq ι] in
include hℓ in
theorem algebraMap_mul_mem_twPart {s : Finset ι} {e : ℕ} {y : LocAt w s}
    (hy : y ∈ twPart 𝒜 w s (e + 1)) : algebraMap M (LocAt w s) ℓ * y ∈ twPart 𝒜 w s e := by
  refine (AddSubgroup.closure_le ((twPart 𝒜 w s e).comap
    (AddMonoidHom.mulLeft (algebraMap M (LocAt w s) ℓ)))).mpr ?_ hy
  rintro _ ⟨m, i, x, hx, hdeg, rfl⟩
  change algebraMap M (LocAt w s) ℓ * frac w s m x ∈ twPart 𝒜 w s e
  rw [algebraMap_mul_frac]
  exact frac_mem_twPart (SetLike.mul_mem_graded hℓ hx) (by omega)

/-- Multiplication by `ℓ` on the twisted parts over one subset. -/
noncomputable def twMulApp (e : ℕ) (s : Finset ι) : twPart 𝒜 w s (e + 1) →+ twPart 𝒜 w s e :=
  ((AddMonoidHom.mulLeft (algebraMap M (LocAt w s) ℓ)).comp
    (twPart 𝒜 w s (e + 1)).subtype).codRestrict _ (fun y => algebraMap_mul_mem_twPart hℓ y.2)

omit [DecidableEq ι] in
theorem twMulApp_coe (e : ℕ) (s : Finset ι) (y : twPart 𝒜 w s (e + 1)) :
    (twMulApp hℓ e s y : LocAt w s) = algebraMap M (LocAt w s) ℓ * y := rfl

/-- **Multiplication by a linear form**, `𝒪(-e-1) → 𝒪(-e)`. -/
noncomputable def twMul (e : ℕ) : (twCech 𝒜 w hw (e + 1)).Hom (twCech 𝒜 w hw e) where
  app s := twMulApp hℓ e s
  comm h y := by
    apply twVal_injective hw
    change resLoc w h (algebraMap M (LocAt w _) ℓ * twVal hw y)
      = algebraMap M (LocAt w _) ℓ * resLoc w h (twVal hw y)
    rw [map_mul, resLoc_algebraMap]

theorem twMul_app_val (e : ℕ) (s : Finset ι) (y : (twCech 𝒜 w hw (e + 1)).obj s) :
    twVal hw ((twMul hw hℓ e).app s y) = algebraMap M (LocAt w s) ℓ * twVal hw y := rfl

/-- **Multiplication by a nonzerodivisor is injective.** -/
theorem twMul_injective (e : ℕ) {s : Finset ι}
    (hreg : algebraMap M (LocAt w s) ℓ ∈ nonZeroDivisors (LocAt w s)) :
    Function.Injective ((twMul hw hℓ e).app s) := by
  intro y y' h
  have h' := congrArg (twVal hw) h
  rw [twMul_app_val, twMul_app_val] at h'
  exact twVal_injective hw ((mul_cancel_left_mem_nonZeroDivisors hreg).mp h')

end Mul

/-! ## Graded ring maps -/

section Map

variable [DecidableEq ι] {M' : Type u} [CommRing M'] [Algebra K M'] {𝒜' : ℕ → Submodule K M'}
  [GradedAlgebra 𝒜'] {w' : ι → M'} (f : M →+* M') (hfw : ∀ i, f (w i) = w' i)

include hfw in
omit [DecidableEq ι] [GradedAlgebra 𝒜'] in
theorem map_wProd (s : Finset ι) : f (wProd w s) = wProd w' s := by
  simp only [wProd, map_prod, hfw]

omit [DecidableEq ι] [GradedAlgebra 𝒜'] in
/-- The map of localizations induced by `f`. -/
noncomputable def locMap (s : Finset ι) : LocAt w s →+* LocAt w' s :=
  IsLocalization.Away.lift (wProd w s) (g := (algebraMap M' (LocAt w' s)).comp f) (by
    rw [RingHom.comp_apply, map_wProd f hfw]
    exact IsLocalization.Away.algebraMap_isUnit _)

omit [DecidableEq ι] [GradedAlgebra 𝒜'] in
theorem locMap_algebraMap (s : Finset ι) (a : M) :
    locMap f hfw s (algebraMap M (LocAt w s) a) = algebraMap M' (LocAt w' s) (f a) :=
  IsLocalization.lift_eq _ a

omit [DecidableEq ι] [GradedAlgebra 𝒜'] in
theorem locMap_frac (s : Finset ι) (m : ℕ) (x : M) :
    locMap f hfw s (frac w s m x) = frac w' s m (f x) := by
  rw [frac, Localization.mk_eq_mk']
  simp only [locMap, IsLocalization.Away.lift]
  rw [IsLocalization.lift_mk'_spec]
  change algebraMap M' (LocAt w' s) (f x)
    = algebraMap M' (LocAt w' s) (f (wProd w s ^ m)) * frac w' s m (f x)
  rw [algebraMap_mul_frac, map_pow, map_wProd f hfw]
  have := frac_mul_pow (w := w') s 0 m (f x)
  rw [zero_add] at this
  rw [this, frac_zero_eq]

omit [DecidableEq ι] [GradedAlgebra 𝒜'] in
theorem locMap_resLoc {s t : Finset ι} (h : s ⊆ t) (y : LocAt w s) :
    locMap f hfw t (resLoc w h y) = resLoc w' h (locMap f hfw s y) := by
  have : (locMap f hfw t).comp (resLoc w h) = (resLoc w' h).comp (locMap f hfw s) :=
    IsLocalization.ringHom_ext (Submonoid.powers (wProd w s)) (by
      ext a
      simp only [RingHom.comp_apply, resLoc_algebraMap, locMap_algebraMap])
  exact DFunLike.congr_fun this y

attribute [irreducible] locMap

variable (hf : ∀ i x, x ∈ 𝒜 i → f x ∈ 𝒜' i)

include hf in
omit [GradedAlgebra 𝒜] [DecidableEq ι] [GradedAlgebra 𝒜'] in
theorem locMap_mem {s : Finset ι} {e : ℕ} {y : LocAt w s} (hy : y ∈ twPart 𝒜 w s e) :
    locMap f hfw s y ∈ twPart 𝒜' w' s e := by
  refine (AddSubgroup.closure_le ((twPart 𝒜' w' s e).comap
    (locMap f hfw s).toAddMonoidHom)).mpr ?_ hy
  rintro _ ⟨m, i, x, hx, hdeg, rfl⟩
  change locMap f hfw s (frac w s m x) ∈ twPart 𝒜' w' s e
  rw [locMap_frac]
  exact frac_mem_twPart (hf i x hx) hdeg

variable (hw : ∀ i, w i ∈ 𝒜 1) (hw' : ∀ i, w' i ∈ 𝒜' 1)

/-- The map of twisted parts over one subset induced by `f`. -/
noncomputable def twMapApp (e : ℕ) (s : Finset ι) : twPart 𝒜 w s e →+ twPart 𝒜' w' s e :=
  ((locMap f hfw s).toAddMonoidHom.comp (twPart 𝒜 w s e).subtype).codRestrict _
    (fun y => locMap_mem f hfw hf y.2)

omit [GradedAlgebra 𝒜] [DecidableEq ι] [GradedAlgebra 𝒜'] in
theorem twMapApp_coe (e : ℕ) (s : Finset ι) (y : twPart 𝒜 w s e) :
    (twMapApp f hfw hf e s y : LocAt w' s) = locMap f hfw s y := rfl

/-- **The morphism of twisted Čech data induced by a graded ring map.** -/
noncomputable def twMap (e : ℕ) : (twCech 𝒜 w hw e).Hom (twCech 𝒜' w' hw' e) where
  app s := twMapApp f hfw hf e s
  comm h y := by
    apply twVal_injective hw'
    change resLoc w' h (locMap f hfw _ (twVal hw y)) = locMap f hfw _ (resLoc w h (twVal hw y))
    exact (locMap_resLoc f hfw h (twVal hw y)).symm

theorem twMap_app_val (e : ℕ) (s : Finset ι) (y : (twCech 𝒜 w hw e).obj s) :
    twVal hw' ((twMap f hfw hf hw hw' e).app s y) = locMap f hfw s (twVal hw y) := rfl

/-- **The composite `𝒪_M(-e-1) → 𝒪_M(-e) → 𝒪_{M'}(-e)` vanishes** when `f` kills `ℓ`. -/
theorem twMap_twMul {ℓ : M} (hℓ : ℓ ∈ 𝒜 1) (hfℓ : f ℓ = 0) (e : ℕ) (s : Finset ι)
    (y : (twCech 𝒜 w hw (e + 1)).obj s) :
    (twMap f hfw hf hw hw' e).app s ((twMul hw hℓ e).app s y) = 0 := by
  apply twVal_injective hw'
  rw [twMap_app_val, twMul_app_val, map_mul, locMap_algebraMap, hfℓ, map_zero, zero_mul]
  rfl

/-- **Middle exactness**: over a nonempty subset, a section of `𝒪_M(-e)` killed in `M'` is `ℓ`
times a section of `𝒪_M(-e-1)`, as soon as the kernel of `f` is generated by `ℓ`. -/
theorem twMap_exact {ℓ : M} (hℓ : ℓ ∈ 𝒜 1) (hker : ∀ x, f x = 0 → ∃ z, x = ℓ * z) (e : ℕ)
    {s : Finset ι} (hs : s.Nonempty) (y : (twCech 𝒜 w hw e).obj s)
    (hy : (twMap f hfw hf hw hw' e).app s y = 0) : ∃ z, (twMul hw hℓ e).app s z = y := by
  obtain ⟨m, i, x, hx, hdeg, hyx⟩ := (mem_twPart_iff hw hs).mp (y : twPart 𝒜 w s e).2
  have hy' : frac w' s m (f x) = 0 := by
    have := congrArg (twVal hw') hy
    rw [twMap_app_val] at this
    change locMap f hfw s (twVal hw y) = 0 at this
    rwa [show twVal hw y = frac w s m x from hyx, locMap_frac] at this
  rw [frac, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hy'
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := hy'
  have hfk : f (wProd w s ^ k * x) = 0 := by
    rw [map_mul, map_pow, map_wProd f hfw]
    exact hk
  obtain ⟨z, hz⟩ := hker _ hfk
  have hmem : wProd w s ^ k * x ∈ 𝒜 (k * s.card + i) :=
    SetLike.mul_mem_graded (wProd_pow_mem hw s k) hx
  by_cases hd : 1 ≤ k * s.card + i
  · set z' : M := (decompose 𝒜 z (k * s.card + i - 1) : M) with hz'
    have hz'mem : z' ∈ 𝒜 (k * s.card + i - 1) := SetLike.coe_mem _
    have hprod : wProd w s ^ k * x = ℓ * z' := by
      rw [← DirectSum.decompose_of_mem_same 𝒜 hmem, hz,
        DirectSum.coe_decompose_mul_of_left_mem_of_le 𝒜 hℓ hd]
    refine ⟨⟨frac w s (m + k) z', frac_mem_twPart hz'mem (by rw [add_mul]; omega)⟩, ?_⟩
    apply twVal_injective hw
    rw [twMul_app_val]
    change algebraMap M (LocAt w s) ℓ * frac w s (m + k) z' = twVal hw y
    rw [show twVal hw y = frac w s m x from hyx, algebraMap_mul_frac, ← hprod, frac_mul_pow]
  · have hzero : wProd w s ^ k * x = 0 := by
      rw [← DirectSum.decompose_of_mem_same 𝒜 hmem, hz,
        DirectSum.coe_decompose_mul_of_left_mem_of_not_le 𝒜 hℓ hd]
    refine ⟨0, ?_⟩
    apply twVal_injective hw
    rw [map_zero]
    change (0 : LocAt w s) = twVal hw y
    rw [show twVal hw y = frac w s m x from hyx, ← frac_mul_pow s m k x, hzero, frac_zero]

/-- **Surjectivity**: over a nonempty subset every section of `𝒪_{M'}(-e)` lifts, as soon as
homogeneous elements lift homogeneously. -/
theorem twMap_surjective (hlift : ∀ i x', x' ∈ 𝒜' i → ∃ x ∈ 𝒜 i, f x = x') (e : ℕ)
    {s : Finset ι} (hs : s.Nonempty) : Function.Surjective ((twMap f hfw hf hw hw' e).app s) := by
  intro y'
  obtain ⟨m, i, x', hx', hdeg, hyx⟩ := (mem_twPart_iff hw' hs).mp (y' : twPart 𝒜' w' s e).2
  obtain ⟨x, hx, rfl⟩ := hlift i x' hx'
  refine ⟨⟨frac w s m x, frac_mem_twPart hx hdeg⟩, twVal_injective hw' ?_⟩
  rw [twMap_app_val]
  change locMap f hfw s (frac w s m x) = twVal hw' y'
  rw [locMap_frac]
  exact hyx.symm

end Map

end HTGeometry
