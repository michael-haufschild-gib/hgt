import Mathlib

/-!
# The cofinal radial Gamma linear relation

The radial multiplier `a_p ↦ p^{-2t} a_p` on all-prime coefficient sequences descends to the
quotient by the summable subspace only as a linear *relation*.  It is single-valued exactly on the
closed half-line `t ≥ 0`, its inverse exactly on `t ≤ 0`, and both exactly at the radial centre.
Every finite-prime truncation induces the diagonal relation at every grade, so the two-sided
descent is invisible at finite stages.
-/

namespace HTGeometry.ConstraintRelativity

open Submodule

/-! ## The fixed summable-subspace target -/

/-- **Card `(CGR.1)`.**  All-prime coefficient sequences. -/
abbrev PrimeSeq : Type := Nat.Primes → ℂ

/-- **Card `(CGR.1)`.**  The summable subspace `ℓ¹(𝒫)`. -/
def summableSubspace : Submodule ℂ PrimeSeq where
  carrier := {a | Summable fun p => ‖a p‖}
  add_mem' := by
    intro a b ha hb
    refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => norm_add_le _ _) ?_
    exact ha.add hb
  zero_mem' := by
    simp only [Set.mem_setOf_eq, Pi.zero_apply, norm_zero]
    exact summable_zero
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, Pi.smul_apply, norm_smul]
    exact ha.mul_left _

theorem mem_summableSubspace {a : PrimeSeq} :
    a ∈ summableSubspace ↔ Summable fun p => ‖a p‖ := Iff.rfl

/-- **Card `(CGR.1)`.**  The fixed quotient target. -/
abbrev GammaTarget : Type := PrimeSeq ⧸ summableSubspace

/-! ## The radial multiplier and its relation -/

/-- **Card `(CGR.2)`.**  The cofinal radial multiplier. -/
noncomputable def radialMul (t : ℝ) : PrimeSeq →ₗ[ℂ] PrimeSeq where
  toFun a p := (((p : ℕ) : ℝ) ^ (-2 * t) : ℝ) • a p
  map_add' a b := by funext p; simp [smul_add]
  map_smul' c a := by funext p; simp; ring

@[simp] theorem radialMul_apply (t : ℝ) (a : PrimeSeq) (p : Nat.Primes) :
    radialMul t a p = (((p : ℕ) : ℝ) ^ (-2 * t) : ℝ) • a p := rfl

theorem norm_radialMul (t : ℝ) (a : PrimeSeq) (p : Nat.Primes) :
    ‖radialMul t a p‖ = ((p : ℕ) : ℝ) ^ (-2 * t) * ‖a p‖ := by
  rw [radialMul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _)]

/-- **Card `(CGR.3)`.**  The canonical quotient relation of a multiplier. -/
noncomputable def gammaRel (C : PrimeSeq →ₗ[ℂ] PrimeSeq) :
    Submodule ℂ (GammaTarget × GammaTarget) :=
  Submodule.map (summableSubspace.mkQ.prodMap summableSubspace.mkQ) (LinearMap.graph C)

theorem mem_gammaRel_iff (C : PrimeSeq →ₗ[ℂ] PrimeSeq) (x y : GammaTarget) :
    (x, y) ∈ gammaRel C ↔ ∃ a : PrimeSeq,
      summableSubspace.mkQ a = x ∧ summableSubspace.mkQ (C a) = y := by
  constructor
  · rintro ⟨⟨a, b⟩, hab, hmap⟩
    refine ⟨a, ?_, ?_⟩
    · exact congrArg Prod.fst hmap
    · have hb : b = C a := hab
      have := congrArg Prod.snd hmap
      simpa [hb] using this
  · rintro ⟨a, hx, hy⟩
    exact ⟨(a, C a), rfl, by simp [hx, hy]⟩

/-- **Lemma A.**  The relation is single-valued exactly when the multiplier preserves the summable
subspace. -/
theorem gammaRel_singleValued_iff (C : PrimeSeq →ₗ[ℂ] PrimeSeq) :
    (∀ x y y' : GammaTarget, (x, y) ∈ gammaRel C → (x, y') ∈ gammaRel C → y = y')
      ↔ ∀ i ∈ summableSubspace, C i ∈ summableSubspace := by
  constructor
  · intro hsv i hi
    have h0 : ((0 : GammaTarget), (0 : GammaTarget)) ∈ gammaRel C :=
      (mem_gammaRel_iff C _ _).2 ⟨0, by simp, by simp⟩
    have hi0 : ((0 : GammaTarget), summableSubspace.mkQ (C i)) ∈ gammaRel C :=
      (mem_gammaRel_iff C _ _).2 ⟨i, (Submodule.Quotient.mk_eq_zero _).2 hi, rfl⟩
    have := hsv 0 0 (summableSubspace.mkQ (C i)) h0 hi0
    exact (Submodule.Quotient.mk_eq_zero _).1 this.symm
  · intro hmap x y y' hy hy'
    obtain ⟨a, hax, hay⟩ := (mem_gammaRel_iff C _ _).1 hy
    obtain ⟨b, hbx, hby⟩ := (mem_gammaRel_iff C _ _).1 hy'
    have hab : a - b ∈ summableSubspace := by
      rw [← Submodule.Quotient.eq]
      show summableSubspace.mkQ a = summableSubspace.mkQ b
      rw [hax, hbx]
    have hC : C (a - b) ∈ summableSubspace := hmap _ hab
    rw [← hay, ← hby]
    show (Submodule.Quotient.mk (C a) : GammaTarget) = Submodule.Quotient.mk (C b)
    rw [Submodule.Quotient.eq, ← map_sub]
    exact hC

/-! ## The exact radial trichotomy -/

/-- **Lemma B.**  The radial multiplier preserves the summable subspace exactly on the closed
half-line `t ≥ 0`. -/
theorem radialMul_mapsTo_iff (t : ℝ) :
    (∀ i ∈ summableSubspace, radialMul t i ∈ summableSubspace) ↔ 0 ≤ t := by
  constructor
  · intro h
    by_contra hcon
    have ht : t < 0 := lt_of_not_ge hcon
    set u : ℝ := -t with hu
    have hupos : 0 < u := by simp only [hu]; linarith
    set b : PrimeSeq := fun p => ((((p : ℕ) : ℝ) ^ (-(2 * u)) * (((p : ℕ) : ℝ))⁻¹ : ℝ) : ℂ)
      with hbdef
    have hppos : ∀ p : Nat.Primes, (0 : ℝ) < ((p : ℕ) : ℝ) := fun p => by
      exact_mod_cast p.2.pos
    have hnormb : ∀ p : Nat.Primes, ‖b p‖ = ((p : ℕ) : ℝ) ^ (-(1 + 2 * u)) := by
      intro p
      have h1 : (((p : ℕ) : ℝ))⁻¹ = ((p : ℕ) : ℝ) ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one]
      rw [hbdef]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      rw [h1, ← Real.rpow_add (hppos p), abs_of_pos (Real.rpow_pos_of_pos (hppos p) _)]
      congr 1
      ring
    have hb : b ∈ summableSubspace := by
      rw [mem_summableSubspace]
      have hsum : Summable fun n : ℕ => ((n : ℝ) ^ (1 + 2 * u))⁻¹ :=
        Real.summable_nat_rpow_inv.2 (by linarith)
      have hsub : Summable fun p : Nat.Primes => (((p : ℕ) : ℝ) ^ (1 + 2 * u))⁻¹ :=
        hsum.subtype _
      refine hsub.congr fun p => ?_
      rw [hnormb p, Real.rpow_neg (hppos p).le]
    have hCb := h b hb
    rw [mem_summableSubspace] at hCb
    refine Nat.Primes.not_summable_one_div (hCb.congr fun p => ?_)
    rw [norm_radialMul, hnormb p, ← Real.rpow_add (hppos p)]
    have hexp : -2 * t + -(1 + 2 * u) = -1 := by simp only [hu]; ring
    rw [hexp, Real.rpow_neg_one, one_div]
  · intro ht i hi
    rw [mem_summableSubspace] at hi ⊢
    refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) hi
    rw [norm_radialMul]
    have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
    have hle : ((p : ℕ) : ℝ) ^ (-2 * t) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
    nlinarith [norm_nonneg (i p)]

/-- **Theorem C.1.**  The forward relation is single-valued exactly on `t ≥ 0`. -/
theorem gammaRel_forward_iff (t : ℝ) :
    (∀ x y y' : GammaTarget, (x, y) ∈ gammaRel (radialMul t) → (x, y') ∈ gammaRel (radialMul t) →
      y = y') ↔ 0 ≤ t :=
  (gammaRel_singleValued_iff (radialMul t)).trans (radialMul_mapsTo_iff t)

/-- **Theorem C.2.**  The inverse relation is single-valued exactly on `t ≤ 0`. -/
theorem gammaRel_inverse_iff (t : ℝ) :
    (∀ x y y' : GammaTarget, (x, y) ∈ gammaRel (radialMul (-t)) →
      (x, y') ∈ gammaRel (radialMul (-t)) → y = y') ↔ t ≤ 0 := by
  rw [gammaRel_forward_iff]
  constructor <;> intro h <;> linarith

/-- **Theorem C.3.**  Both orientations are single-valued exactly at the radial centre. -/
theorem gammaRel_both_iff (t : ℝ) :
    ((∀ x y y' : GammaTarget, (x, y) ∈ gammaRel (radialMul t) →
        (x, y') ∈ gammaRel (radialMul t) → y = y') ∧
      (∀ x y y' : GammaTarget, (x, y) ∈ gammaRel (radialMul (-t)) →
        (x, y') ∈ gammaRel (radialMul (-t)) → y = y')) ↔ t = 0 := by
  rw [gammaRel_forward_iff, gammaRel_inverse_iff]
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · rintro rfl; exact ⟨le_refl 0, le_refl 0⟩

/-- **Theorem C.4.**  At the centre the relation is the diagonal. -/
theorem gammaRel_zero :
    gammaRel (radialMul 0) = LinearMap.graph (LinearMap.id : GammaTarget →ₗ[ℂ] GammaTarget) := by
  ext ⟨x, y⟩
  rw [mem_gammaRel_iff, LinearMap.mem_graph_iff]
  constructor
  · rintro ⟨a, hx, hy⟩
    have h0 : radialMul (0 : ℝ) a = a := by
      funext p
      simp
    rw [h0] at hy
    simp [← hx, ← hy]
  · intro hxy
    obtain ⟨a, ha⟩ := Submodule.mkQ_surjective summableSubspace x
    refine ⟨a, ha, ?_⟩
    have h0 : radialMul (0 : ℝ) a = a := by
      funext p
      simp
    rw [h0, ha]
    simpa using hxy.symm

/-! ## Finite-stage invisibility -/

/-- **Card `(CGR.7)`.**  The finite-prime radial multiplier. -/
noncomputable def finiteRadialMul (t : ℝ) (K : Finset Nat.Primes) : PrimeSeq →ₗ[ℂ] PrimeSeq where
  toFun a p := if p ∈ K then ((((p : ℕ) : ℝ) ^ (-2 * t) : ℝ) : ℂ) * a p else a p
  map_add' a b := by
    funext p
    by_cases hp : p ∈ K <;> simp [hp, mul_add]
  map_smul' c a := by
    funext p
    by_cases hp : p ∈ K
    · simp [hp]; ring
    · simp [hp]

/-- **Theorem D, boxed.**  Every finite-prime truncation induces the diagonal relation, at every
radial grade. -/
theorem gammaRel_finite (t : ℝ) (K : Finset Nat.Primes) :
    gammaRel (finiteRadialMul t K)
      = LinearMap.graph (LinearMap.id : GammaTarget →ₗ[ℂ] GammaTarget) := by
  have hdiff : ∀ a : PrimeSeq, finiteRadialMul t K a - a ∈ summableSubspace := by
    intro a
    rw [mem_summableSubspace]
    refine summable_of_ne_finset_zero (s := K) fun p hp => ?_
    simp [finiteRadialMul, hp]
  have hmk : ∀ a : PrimeSeq,
      summableSubspace.mkQ (finiteRadialMul t K a) = summableSubspace.mkQ a := by
    intro a
    show (Submodule.Quotient.mk (finiteRadialMul t K a) : GammaTarget) = Submodule.Quotient.mk a
    rw [Submodule.Quotient.eq]
    exact hdiff a
  ext ⟨x, y⟩
  rw [mem_gammaRel_iff, LinearMap.mem_graph_iff]
  constructor
  · rintro ⟨a, hx, hy⟩
    rw [hmk a, hx] at hy
    simpa using hy.symm
  · intro hxy
    obtain ⟨a, ha⟩ := Submodule.mkQ_surjective summableSubspace x
    refine ⟨a, ha, ?_⟩
    rw [hmk a, ha]
    simpa using hxy.symm

/-! ## Source coinvariants -/

section Coinvariants

variable {R J : Type*} [AddCommGroup R] [Module ℂ R]

/-- **Corollary E, `(CGR.9)`.**  The source coinvariants. -/
noncomputable def sourceCoinvariants (g : J → (R →ₗ[ℂ] R)) : Submodule ℂ R :=
  ⨆ j, LinearMap.range (g j - LinearMap.id)

/-- **Corollary E.**  A map intertwines the source generators with the diagonal target relation
exactly when it kills every generator defect. -/
theorem intertwiner_iff_vanishes (g : J → (R →ₗ[ℂ] R)) (P : R →ₗ[ℂ] GammaTarget) :
    (∀ j, P ∘ₗ g j = P) ↔ sourceCoinvariants g ≤ LinearMap.ker P := by
  constructor
  · intro h
    refine iSup_le fun j => ?_
    rintro _ ⟨x, rfl⟩
    have := congrArg (fun F => F x) (h j)
    simp only [LinearMap.comp_apply] at this
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_sub, this,
      sub_self]
  · intro h j
    ext x
    have hx : ((g j - LinearMap.id : R →ₗ[ℂ] R) x) ∈ sourceCoinvariants g :=
      le_iSup (fun j => LinearMap.range (g j - (LinearMap.id : R →ₗ[ℂ] R))) j ⟨x, rfl⟩
    have := h hx
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
      sub_eq_zero] at this
    simpa using this

/-- **Corollary E.**  Equivalently, such a map factors through the source coinvariants. -/
theorem exists_factor_iff (g : J → (R →ₗ[ℂ] R)) (P : R →ₗ[ℂ] GammaTarget) :
    (∀ j, P ∘ₗ g j = P) ↔
      ∃ Q : (R ⧸ sourceCoinvariants g) →ₗ[ℂ] GammaTarget, P = Q ∘ₗ (sourceCoinvariants g).mkQ := by
  rw [intertwiner_iff_vanishes]
  constructor
  · intro h
    exact ⟨Submodule.liftQ _ P h, by ext x; simp⟩
  · rintro ⟨Q, rfl⟩
    refine fun x hx => ?_
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero _).2 hx, map_zero]

end Coinvariants

/-! ## Kernel and multivalued defect exchange -/

section Defects

theorem radialMul_add (t s : ℝ) (a : PrimeSeq) :
    radialMul t (radialMul s a) = radialMul (t + s) a := by
  funext p
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hpow : (((p : ℕ) : ℝ) ^ (-2 * t)) * (((p : ℕ) : ℝ) ^ (-2 * s))
      = ((p : ℕ) : ℝ) ^ (-2 * (t + s)) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  simp only [radialMul_apply, smul_smul, hpow]

theorem radialMul_zero (a : PrimeSeq) : radialMul 0 a = a := by
  funext p
  simp

/-- **Card `(CGR.10)`.**  The multivalued part of the relation. -/
noncomputable def mulPart (C : PrimeSeq →ₗ[ℂ] PrimeSeq) : Submodule ℂ GammaTarget :=
  Submodule.map summableSubspace.mkQ (Submodule.map C summableSubspace)

/-- **Card `(CGR.10)`.**  The kernel part of the relation. -/
noncomputable def kerPart (C : PrimeSeq →ₗ[ℂ] PrimeSeq) : Submodule ℂ GammaTarget :=
  Submodule.map summableSubspace.mkQ (Submodule.comap C summableSubspace)

theorem mem_mulPart_iff (C : PrimeSeq →ₗ[ℂ] PrimeSeq) (y : GammaTarget) :
    y ∈ mulPart C ↔ ((0 : GammaTarget), y) ∈ gammaRel C := by
  rw [mem_gammaRel_iff, mulPart]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, (Submodule.Quotient.mk_eq_zero _).2 hi, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨C a, ⟨a, (Submodule.Quotient.mk_eq_zero _).1 ha, rfl⟩, rfl⟩

theorem mem_kerPart_iff (C : PrimeSeq →ₗ[ℂ] PrimeSeq) (x : GammaTarget) :
    x ∈ kerPart C ↔ (x, (0 : GammaTarget)) ∈ gammaRel C := by
  rw [mem_gammaRel_iff, kerPart]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, rfl, (Submodule.Quotient.mk_eq_zero _).2 ha⟩
  · rintro ⟨a, ha, hb⟩
    refine ⟨a, ?_, ha⟩
    show C a ∈ summableSubspace
    exact (Submodule.Quotient.mk_eq_zero _).1 hb

/-- **Card `(CGR.11)`.**  The multivalued defect vanishes exactly on `t ≥ 0`. -/
theorem mulPart_eq_bot_iff (t : ℝ) : mulPart (radialMul t) = ⊥ ↔ 0 ≤ t := by
  rw [← radialMul_mapsTo_iff t]
  constructor
  · intro h i hi
    have hy : summableSubspace.mkQ (radialMul t i) ∈ mulPart (radialMul t) :=
      ⟨radialMul t i, ⟨i, hi, rfl⟩, rfl⟩
    rw [h, Submodule.mem_bot] at hy
    exact (Submodule.Quotient.mk_eq_zero _).1 hy
  · intro h
    refine eq_bot_iff.2 ?_
    rintro y ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).2 (h i hi)

/-- **Card `(CGR.11)`.**  The kernel defect vanishes exactly on `t ≤ 0`. -/
theorem kerPart_eq_bot_iff (t : ℝ) : kerPart (radialMul t) = ⊥ ↔ t ≤ 0 := by
  have hkey : (∀ a : PrimeSeq, radialMul t a ∈ summableSubspace → a ∈ summableSubspace)
      ↔ (∀ i ∈ summableSubspace, radialMul (-t) i ∈ summableSubspace) := by
    constructor
    · intro h i hi
      refine h _ ?_
      rw [radialMul_add, add_neg_cancel, radialMul_zero]
      exact hi
    · intro h a ha
      have := h _ ha
      rwa [radialMul_add, neg_add_cancel, radialMul_zero] at this
  constructor
  · intro h
    have hmaps : ∀ a : PrimeSeq, radialMul t a ∈ summableSubspace → a ∈ summableSubspace := by
      intro a ha
      have hx : summableSubspace.mkQ a ∈ kerPart (radialMul t) := ⟨a, ha, rfl⟩
      rw [h, Submodule.mem_bot] at hx
      exact (Submodule.Quotient.mk_eq_zero _).1 hx
    have := (radialMul_mapsTo_iff (-t)).1 (hkey.1 hmaps)
    linarith
  · intro ht
    have hmaps := hkey.2 ((radialMul_mapsTo_iff (-t)).2 (by linarith))
    refine eq_bot_iff.2 ?_
    rintro x ⟨a, ha, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).2 (hmaps a ha)

/-- **Card `(CGR.12)`.**  Crossing the centre exchanges the kernel defect with the multivalued
defect while preserving the reduced relational carrier. -/
noncomputable def defectExchange (t : ℝ) :
    (GammaTarget ⧸ kerPart (radialMul t)) ≃ₗ[ℂ] (GammaTarget ⧸ mulPart (radialMul t)) := by
  classical
  set C := radialMul t with hC
  refine LinearEquiv.ofBijective
    (Submodule.liftQ (kerPart C)
      (Submodule.liftQ summableSubspace
        ((mulPart C).mkQ ∘ₗ summableSubspace.mkQ ∘ₗ C) ?_) ?_) ⟨?_, ?_⟩
  · rintro i hi
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨C i, ⟨i, hi, rfl⟩, rfl⟩
  · rintro x ⟨a, ha, rfl⟩
    have haI : C a ∈ summableSubspace := ha
    simp only [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.liftQ_apply,
      LinearMap.comp_apply]
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    have hz : (Submodule.Quotient.mk (C a) : GammaTarget) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 haI
    rw [hz]
    exact Submodule.zero_mem _
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro z hz
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      induction x using Submodule.Quotient.induction_on with
      | H a =>
        have hz' : (Submodule.Quotient.mk (summableSubspace.mkQ (C a)) :
            GammaTarget ⧸ mulPart C) = 0 := hz
        obtain ⟨_, ⟨i, hi, rfl⟩, hmk⟩ :=
          (Submodule.Quotient.mk_eq_zero _).1 hz'
        have hdiff : C (a - i) ∈ summableSubspace := by
          rw [map_sub, ← Submodule.Quotient.eq]
          show summableSubspace.mkQ (C a) = summableSubspace.mkQ (C i)
          exact hmk.symm
        have hx : (summableSubspace.mkQ a : GammaTarget) ∈ kerPart C :=
          ⟨a - i, hdiff, by
            show (Submodule.Quotient.mk (a - i) : GammaTarget) = Submodule.Quotient.mk a
            rw [Submodule.Quotient.eq]
            simpa using hi⟩
        rw [Submodule.mem_bot]
        exact (Submodule.Quotient.mk_eq_zero _).2 hx
  · rintro z
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      induction x using Submodule.Quotient.induction_on with
      | H a =>
        refine ⟨Submodule.Quotient.mk (summableSubspace.mkQ (radialMul (-t) a)), ?_⟩
        simp only [Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
        congr 2
        rw [hC, radialMul_add, add_neg_cancel, radialMul_zero]

end Defects

end HTGeometry.ConstraintRelativity
