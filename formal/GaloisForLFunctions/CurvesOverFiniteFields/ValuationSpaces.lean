import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Valuation spaces of a Dedekind domain and their one-step quotients

Let `R` be a Dedekind domain with fraction field `K`. For a finitely supported function
`E : HeightOneSpectrum R →₀ ℤ`, the valuation space `valSpace E` is the `R`-submodule of `K` cut out
by `v(f) ≤ exp(E v)` at every height-one prime `v`, i.e. `ord_v f ≥ −E v`.

* `valSpace_ne_bot`: it contains a nonzero element.
* `exists_valuation_eq_exp_one`: some `s ∈ K` has a simple pole at `v` and no other pole.
* `valSpaceStepEquiv`: raising `E` by one at `v` gives a quotient isomorphic to `R/v` as an
  `R`-module. An element `f` of the larger space with `v(f) = exp(E v + 1)` generates it,
  and `r f` lies in the smaller space exactly when `r ∈ v`.
* `finrank_valSpace_step`: over any field `F` under `R`, the quotient has dimension
  `dim_F (R/v)`.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace GaloisForLFunctions.CurvesOverFiniteFields

/-- In `ℤᵐ⁰`, being below `exp (n + 1)` is being at most `exp n`. -/
theorem lt_exp_add_one_iff {x : WithZero (Multiplicative ℤ)} {n : ℤ} :
    x < exp (n + 1) ↔ x ≤ exp n := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← exp_log hx, exp_lt_exp, exp_le_exp]
    omega

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

variable (K) in
/-- The `R`-submodule of `K` of elements with `v(f) ≤ exp(E v)` at every height-one prime. -/
def valSpace (E : HeightOneSpectrum R →₀ ℤ) : Submodule R K where
  carrier := {f | ∀ v : HeightOneSpectrum R, v.valuation K f ≤ exp (E v)}
  zero_mem' := fun v => by simp
  add_mem' := fun {f g} hf hg v =>
    ((v.valuation K).map_add f g).trans (max_le (hf v) (hg v))
  smul_mem' := fun r f hf v => by
    rw [Algebra.smul_def, map_mul]
    exact (mul_le_of_le_one_left' (v.valuation_le_one r)).trans (hf v)

theorem mem_valSpace {E : HeightOneSpectrum R →₀ ℤ} {f : K} :
    f ∈ valSpace K E ↔ ∀ v : HeightOneSpectrum R, v.valuation K f ≤ exp (E v) := Iff.rfl

theorem valSpace_mono {E E' : HeightOneSpectrum R →₀ ℤ} (h : E ≤ E') :
    valSpace K E ≤ valSpace K E' := fun _ hf v => (hf v).trans (exp_le_exp.mpr (h v))

/-- A nonzero element of every valuation space: a product of powers of uniformizers. -/
theorem valSpace_ne_bot (E : HeightOneSpectrum R →₀ ℤ) : valSpace K E ≠ ⊥ := by
  classical
  choose π hπ using fun v : HeightOneSpectrum R => v.intValuation_exists_uniformizer
  set f : R := ∏ w ∈ E.support, π w ^ (-E w).toNat
  have hπ0 : ∀ w, π w ≠ 0 := fun w h => by
    have := hπ w
    rw [h, map_zero] at this
    exact WithZero.zero_ne_coe this
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (hπ0 w)
  rw [Submodule.ne_bot_iff]
  refine ⟨algebraMap R K f, fun v => ?_, ?_⟩
  · rw [valuation_of_algebraMap]
    by_cases hv : v ∈ E.support
    · have hsplit : f = π v ^ (-E v).toNat * ∏ w ∈ E.support.erase v, π w ^ (-E w).toNat :=
        (Finset.mul_prod_erase _ (fun w => π w ^ (-E w).toNat) hv).symm
      rw [hsplit, map_mul, map_pow, hπ v]
      have h1 := v.intValuation_le_one (∏ w ∈ E.support.erase v, π w ^ (-E w).toNat)
      calc exp (-1 : ℤ) ^ (-E v).toNat * v.intValuation _ ≤ exp (-1 : ℤ) ^ (-E v).toNat * 1 := by
            gcongr
        _ = exp (-((-E v).toNat : ℤ)) := by rw [mul_one, ← exp_nsmul]; simp
        _ ≤ exp (E v) := exp_le_exp.mpr (by omega)
    · rw [Finsupp.notMem_support_iff.mp hv]
      exact (v.intValuation_le_one f).trans (by simp)
  · exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hf0

/-- An element with a simple pole at `v` and no other pole. -/
theorem exists_valuation_eq_exp_one (v : HeightOneSpectrum R) :
    ∃ s : K, v.valuation K s = exp 1 ∧ ∀ w : HeightOneSpectrum R, w ≠ v → w.valuation K s ≤ 1 := by
  obtain ⟨s, hs, hs1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := K) v.ne_bot
    v.isPrime.ne_top
  rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)] at hs
  have hmul : ∀ a ∈ v.asIdeal, ∃ r : R, algebraMap R K r = s * algebraMap R K a := fun a ha => by
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp
      (hs _ ((FractionalIdeal.mem_coeIdeal _).mpr ⟨a, ha, rfl⟩))
    exact ⟨r, hr⟩
  have hw : ∀ w : HeightOneSpectrum R, w ≠ v → w.valuation K s ≤ 1 := by
    intro w hwv
    have hnle : ¬ v.asIdeal ≤ w.asIdeal := fun hle =>
      hwv (HeightOneSpectrum.ext ((v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm))
    obtain ⟨a, hav, haw⟩ := Set.not_subset.mp hnle
    obtain ⟨r, hr⟩ := hmul a hav
    have h1 : w.valuation K (algebraMap R K r) ≤ 1 := w.valuation_le_one r
    rw [hr, map_mul, (valuation_eq_one_iff_notMem w).mpr haw, mul_one] at h1
    exact h1
  have hv1 : 1 < v.valuation K s := by
    refine lt_of_not_ge fun hle => ?_
    apply hs1
    obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one (R := R) K s fun w => by
      by_cases hwv : w = v
      · rw [hwv]; exact hle
      · exact hw w hwv
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨r, hr⟩
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  have hπv : π ∈ v.asIdeal := by
    rw [← v.intValuation_lt_one_iff_mem, hπ, ← exp_zero, exp_lt_exp]; norm_num
  obtain ⟨r, hr⟩ := hmul π hπv
  have h1 : v.valuation K (algebraMap R K r) ≤ 1 := v.valuation_le_one r
  rw [hr, map_mul, valuation_of_algebraMap, hπ] at h1
  refine ⟨s, le_antisymm ?_ ?_, hw⟩
  · have hne : v.valuation K s ≠ 0 := ne_of_gt (lt_trans zero_lt_one hv1)
    rw [← exp_log hne] at h1 ⊢
    rw [← exp_add, ← exp_zero, exp_le_exp] at h1
    exact exp_le_exp.mpr (by omega)
  · have hne : v.valuation K s ≠ 0 := ne_of_gt (lt_trans zero_lt_one hv1)
    rw [← exp_log hne] at hv1 ⊢
    rw [← exp_zero, exp_lt_exp] at hv1
    exact exp_le_exp.mpr (by omega)


section Step

variable (E : HeightOneSpectrum R →₀ ℤ) (v : HeightOneSpectrum R)

theorem valSpace_le_raise : valSpace K E ≤ valSpace K (E + Finsupp.single v 1) :=
  valSpace_mono fun w => by
    classical
    simp only [Finsupp.coe_add, Pi.add_apply]
    have : 0 ≤ Finsupp.single v (1 : ℤ) w := by
      rw [Finsupp.single_apply]; split_ifs <;> norm_num
    omega

/-- The raised space contains an element with exact valuation `exp (E v + 1)` at `v`. -/
theorem exists_mem_raise_valuation_eq :
    ∃ f ∈ valSpace K (E + Finsupp.single v 1), v.valuation K f = exp (E v + 1) := by
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (valSpace_ne_bot (K := K) E)
  obtain ⟨s, hsv, hsw⟩ := exists_valuation_eq_exp_one (K := K) v
  have hgv0 : v.valuation K g ≠ 0 := (Valuation.ne_zero_iff _).mpr hg0
  set m := log (v.valuation K g)
  have hm : m ≤ E v := by
    have := hg v
    rw [← exp_log hgv0, exp_le_exp] at this
    exact this
  set k : ℕ := (E v + 1 - m).toNat
  have hk : (k : ℤ) = E v + 1 - m := by simp only [k]; omega
  refine ⟨s ^ k * g, fun w => ?_, ?_⟩
  · rw [map_mul, map_pow]
    by_cases hwv : w = v
    · subst hwv
      rw [hsv, ← exp_log hgv0, ← exp_nsmul, ← exp_add, exp_le_exp]
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, nsmul_eq_mul, mul_one]
      omega
    · have h1 : w.valuation K s ^ k ≤ 1 := pow_le_one' (hsw w hwv) k
      calc w.valuation K s ^ k * w.valuation K g ≤ 1 * w.valuation K g := by gcongr
        _ = w.valuation K g := one_mul _
        _ ≤ exp (E w) := hg w
        _ = exp ((E + Finsupp.single v 1 : HeightOneSpectrum R →₀ ℤ) w) := by
            classical
            simp [Ne.symm hwv]
  · rw [map_mul, map_pow, hsv, ← exp_log hgv0, ← exp_nsmul, ← exp_add]
    congr 1
    simp only [nsmul_eq_mul, mul_one]
    omega

/-- An element of the raised space with valuation at most `exp (E v)` at `v` lies in the
original space. -/
theorem mem_valSpace_of_mem_raise {f : K} (hf : f ∈ valSpace K (E + Finsupp.single v 1))
    (hfv : v.valuation K f ≤ exp (E v)) : f ∈ valSpace K E := fun w => by
  by_cases hwv : w = v
  · subst hwv; exact hfv
  · classical
    have := hf w
    simpa [Finsupp.single_apply, Ne.symm hwv] using this

/-- Elements of `O_v` are congruent to elements of `R` modulo the maximal ideal. -/
theorem exists_valuation_sub_lt_one {x : K} (hx : v.valuation K x ≤ 1) :
    ∃ r : R, v.valuation K (x - algebraMap R K r) < 1 := by
  have hxmem : x ∈ valuationSubringAtPrime K v := by
    rw [valuationSubringAtPrime_eq_valuationSubring]; exact hx
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl
    (⟨x, hxmem⟩ : valuationSubringAtPrime K v)
  have hb : (b : R) ∉ v.asIdeal := b.2
  have hbK : algebraMap R K b ≠ 0 := by
    intro h
    apply hb
    rw [(IsFractionRing.injective R K) (h.trans (map_zero _).symm)]
    exact v.asIdeal.zero_mem
  have hxab : x = algebraMap R K a / algebraMap R K b := by
    rw [eq_div_iff hbK]
    change IsLocalization.mk' (valuationSubringAtPrime K v) a b = ⟨x, hxmem⟩ at hab
    have hspec := IsLocalization.mk'_spec (valuationSubringAtPrime K v) a b
    rw [hab] at hspec
    have h2 := congrArg (algebraMap (valuationSubringAtPrime K v) K) hspec
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h2
    exact h2
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  have hb' : Ideal.Quotient.mk v.asIdeal b ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective
    ((Ideal.Quotient.mk v.asIdeal b)⁻¹ * Ideal.Quotient.mk v.asIdeal a)
  refine ⟨c, ?_⟩
  have hmem : a - c * b ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc]
    field_simp
    ring
  have h1 : x - algebraMap R K c = algebraMap R K (a - c * b) / algebraMap R K b := by
    rw [hxab, map_sub, map_mul, sub_div, mul_div_cancel_right₀ _ hbK]
  rw [h1, map_div₀, (valuation_eq_one_iff_notMem v).mpr hb, div_one]
  exact (v.valuation_lt_one_iff_mem _).mpr hmem

/-- Every element of the raised space is congruent to an `R`-multiple of a generator. -/
theorem exists_sub_smul_mem_valSpace {f : K} (hf : f ∈ valSpace K (E + Finsupp.single v 1))
    (hfv : v.valuation K f = exp (E v + 1)) {h : K}
    (hh : h ∈ valSpace K (E + Finsupp.single v 1)) :
    ∃ r : R, h - r • f ∈ valSpace K E := by
  have hf0 : f ≠ 0 := by
    intro h0; rw [h0, map_zero] at hfv; exact zero_ne_coe hfv
  have hfv0 : v.valuation K f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf0
  have hx : v.valuation K (h / f) ≤ 1 := by
    rw [map_div₀, hfv, div_le_one₀ (by rw [← hfv]; exact zero_lt_iff.mpr hfv0)]
    simpa [Finsupp.single_apply] using hh v
  obtain ⟨r, hr⟩ := exists_valuation_sub_lt_one v hx
  refine ⟨r, mem_valSpace_of_mem_raise E v (Submodule.sub_mem _ hh (Submodule.smul_mem _ r hf)) ?_⟩
  have heq : h - r • f = f * (h / f - algebraMap R K r) := by
    rw [Algebra.smul_def, mul_sub, mul_div_cancel₀ _ hf0, mul_comm]
  rw [heq, map_mul, hfv, ← lt_exp_add_one_iff]
  calc exp (E v + 1) * v.valuation K (h / f - algebraMap R K r) < exp (E v + 1) * 1 :=
        mul_lt_mul_of_pos_left hr (zero_lt_iff.mpr (coe_ne_zero))
    _ = exp (E v + 1) := mul_one _

variable (F : Type*) [Field F] [Algebra F R] [Algebra F K] [IsScalarTower F R K]

/-- The `F`-subspace underlying a valuation space. -/
abbrev valSpaceF (E : HeightOneSpectrum R →₀ ℤ) : Submodule F K := (valSpace K E).restrictScalars F

/-- **One step**: raising `E` by one at `v` enlarges the valuation space by `dim_F (R/v)`. -/
theorem finrank_valSpace_step :
    Module.finrank F (valSpaceF (K := K) F (E + Finsupp.single v 1) ⧸
      (valSpaceF (K := K) F E).comap (valSpaceF (K := K) F (E + Finsupp.single v 1)).subtype) =
      Module.finrank F (R ⧸ v.asIdeal) := by
  obtain ⟨f, hf, hfv⟩ := exists_mem_raise_valuation_eq (K := K) E v
  set N := valSpaceF (K := K) F (E + Finsupp.single v 1)
  set M := (valSpaceF (K := K) F E).comap N.subtype
  let g : R →ₗ[F] N :=
    { toFun := fun r => ⟨r • f, Submodule.smul_mem _ r hf⟩
      map_add' := fun a b => by ext; simp [add_smul]
      map_smul' := fun c a => by ext; simp [smul_assoc] }
  let φ : R →ₗ[F] N ⧸ M := M.mkQ.comp g
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨⟨h, hh⟩, rfl⟩ := Submodule.mkQ_surjective M y
    obtain ⟨r, hr⟩ := exists_sub_smul_mem_valSpace E v hf hfv hh
    refine ⟨r, ?_⟩
    change M.mkQ (g r) = M.mkQ ⟨h, hh⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    change (g r - ⟨h, hh⟩ : N).1 ∈ valSpace K E
    have : (g r - ⟨h, hh⟩ : N).1 = -(h - r • f) := by simp [g]
    rw [this]
    exact Submodule.neg_mem _ hr
  have hker : LinearMap.ker φ = v.asIdeal.restrictScalars F := by
    ext r
    simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem]
    change M.mkQ (g r) = 0 ↔ r ∈ v.asIdeal
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change r • f ∈ valSpace K E ↔ r ∈ v.asIdeal
    constructor
    · intro hrf
      have h1 := hrf v
      rw [Algebra.smul_def, map_mul, hfv] at h1
      by_contra hc
      rw [(valuation_eq_one_iff_notMem v).mpr hc, one_mul, exp_le_exp] at h1
      omega
    · intro hr
      refine mem_valSpace_of_mem_raise E v (Submodule.smul_mem _ r hf) ?_
      rw [Algebra.smul_def, map_mul, hfv, ← lt_exp_add_one_iff]
      have h1 : v.valuation K (algebraMap R K r) < 1 := (v.valuation_lt_one_iff_mem _).mpr hr
      calc v.valuation K (algebraMap R K r) * exp (E v + 1) < 1 * exp (E v + 1) :=
            mul_lt_mul_of_pos_right h1 (zero_lt_iff.mpr coe_ne_zero)
        _ = exp (E v + 1) := one_mul _
  rw [← (φ.quotKerEquivOfSurjective hsurj).finrank_eq, hker]
  exact (Submodule.Quotient.restrictScalarsEquiv F v.asIdeal).finrank_eq

end Step

end GaloisForLFunctions.CurvesOverFiniteFields
