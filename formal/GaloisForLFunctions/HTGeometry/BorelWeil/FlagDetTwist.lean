import GaloisForLFunctions.HTGeometry.BorelWeil.FlagGlobalSections

/-!
# Twisting the flag cohomology by a power of the determinant

The determinant divides every cell equation, so it becomes invertible in the localization at the
Bruhat cover.  Multiplication by `det^c` is therefore an isomorphism of the localization that raises
the weight by `c` and changes nothing else: it preserves the denominator bounds in each degree of
the Čech complex and commutes with the differential.

Hence `H^p(G/B, L_λ) ≅ H^p(G/B, L_{λ+c})` for every integer weight `λ` and every `c : ℕ`.  Since a
large enough `c` makes any integer weight a natural-number weight, this reduces every statement
about the flag cohomology to the natural-number case — which is what makes the `ρ`-shifted dot
action of Bott's theorem accessible.

## Main results

* `detPoly_dvd_cellDenomPoly`, `isUnit_algebraMap_detPoly`
* `flagSemiInv_mul_detPow`, `denomBounded_mul_detPow` — the two halves of the twist on sections.
* `flagCohomologyTwistEquiv` — `H^p(L_λ) ≃ₗ H^p(L_{λ+c})`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- **The determinant divides every cell equation.**  The top leading minor of `g` permuted by `σ`
is `± det g`. -/
theorem detPoly_dvd_cellDenomPoly (σ : Equiv.Perm (Fin N)) :
    detPoly N k ∣ cellDenomPoly N k σ := by
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h1 : detPoly 0 k = 1 := by
      rw [detPoly_eq_det_genericMatrix, Matrix.det_isEmpty]
    rw [h1]
    exact one_dvd _
  · set j : Fin N := ⟨N - 1, by omega⟩ with hj
    have hjval : (j : ℕ) + 1 = N := by simp only [hj]; omega
    have hmem : minorPolyAt N k σ ((j : ℕ) + 1) ∣ cellDenomPoly N k σ :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    rw [hjval] at hmem
    refine dvd_trans ?_ hmem
    have hval : minorPolyAt N k σ N
        = ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin N × Fin N) k) * detPoly N k := by
      rw [minorPolyAt, truncate_self_commRing, Matrix.det_permute, detPoly_eq_det_genericMatrix]
    exact ⟨((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin N × Fin N) k), by rw [hval]; ring⟩

theorem detPoly_dvd_denomOf {I : Finset (Equiv.Perm (Fin N))} (hI : I.Nonempty) :
    detPoly N k ∣ denomOf N k I := by
  obtain ⟨σ, hσ⟩ := hI
  exact dvd_trans (detPoly_dvd_cellDenomPoly σ) (Finset.dvd_prod_of_mem _ hσ)

theorem isUnit_algebraMap_detPoly :
    IsUnit (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (detPoly N k)) := by
  refine isUnit_of_dvd_unit (map_dvd _ ?_) isUnit_algebraMap_totalDenom
  exact dvd_trans (detPoly_dvd_cellDenomPoly 1)
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ (1 : Equiv.Perm (Fin N))))

theorem algebraMap_detPoly_ne_zero :
    algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (detPoly N k) ≠ 0 := fun h =>
  detPoly_ne_zero (algebraMap_flagLoc_inj (by rw [h, map_zero]))

theorem borelCharZ_add {lam mu : Fin N → ℤ} {B : Matrix (Fin N) (Fin N) k} (hB : IsBorelMat B) :
    borelCharZ (fun i => lam i + mu i) B = borelCharZ lam B * borelCharZ mu B := by
  rw [borelCharZ, borelCharZ, borelCharZ, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => zpow_add₀ (hB.2 i) _ _

theorem borelCharZ_ne_zero {lam : Fin N → ℤ} {B : Matrix (Fin N) (Fin N) k} (hB : IsBorelMat B) :
    borelCharZ lam B ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hB.2 i)

theorem substRight_detPoly (B : Matrix (Fin N) (Fin N) k) :
    substRight B (detPoly N k) = MvPolynomial.C B.det * detPoly N k := by
  refine matEval_injective fun g => ?_
  have hC : matEval g (MvPolynomial.C B.det) = B.det := by simp [matEval]
  rw [matEval_substRight, matEval_detPoly, matEval_mul, matEval_detPoly, hC, Matrix.det_mul]
  ring

/-- The `c`-th power of the determinant is a semi-invariant of the constant weight `c`. -/
theorem algebraMap_detPow_mem_flagSemiInv (c : ℕ) :
    (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (detPoly N k)) ^ c
      ∈ flagSemiInv N k (fun _ : Fin N => (c : ℤ)) := by
  intro B hB
  have hchar : borelCharZ (fun _ : Fin N => (c : ℤ)) B = B.det ^ c := by
    rw [borelCharZ, Matrix.det_of_upperTriangular hB.1, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => zpow_natCast _ _
  rw [hchar, ← _root_.map_pow, substRightAway_algebraMap,
    _root_.map_pow (substRight B) (detPoly N k) c, substRight_detPoly, mul_pow,
    ← _root_.map_pow (MvPolynomial.C : k →+* MvPolynomial (Fin N × Fin N) k) B.det c, map_mul,
    Algebra.smul_def, IsScalarTower.algebraMap_apply k (MvPolynomial (Fin N × Fin N) k)
      (FlagLoc N k)]
  simp only [MvPolynomial.algebraMap_eq]

/-- **The determinant twist on semi-invariants.** -/
theorem flagSemiInv_mul_detPow (c : ℕ) {lam : Fin N → ℤ} {x : FlagLoc N k} :
    x * (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (detPoly N k)) ^ c
        ∈ flagSemiInv N k (fun i => lam i + (c : ℤ))
      ↔ x ∈ flagSemiInv N k lam := by
  constructor
  · intro hx B hB
    have hd := algebraMap_detPow_mem_flagSemiInv (N := N) (k := k) c B hB
    have h := hx B hB
    rw [map_mul, hd, borelCharZ_add hB] at h
    have hc0 : borelCharZ (fun _ : Fin N => (c : ℤ)) B ≠ 0 := borelCharZ_ne_zero hB
    have hgoal : borelCharZ (fun _ : Fin N => (c : ℤ)) B • ((substRightAway hB) x
          * (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (detPoly N k)) ^ c)
        = borelCharZ (fun _ : Fin N => (c : ℤ)) B • ((borelCharZ lam B • x)
          * (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (detPoly N k)) ^ c) := by
      rw [← mul_smul_comm, h, smul_mul_assoc, ← mul_smul,
        mul_comm (borelCharZ lam B) (borelCharZ (fun _ : Fin N => (c : ℤ)) B)]
    exact mul_right_cancel₀ (pow_ne_zero c algebraMap_detPoly_ne_zero)
      (smul_right_injective (FlagLoc N k) hc0 hgoal)
  · intro hx B hB
    have hd := algebraMap_detPow_mem_flagSemiInv (N := N) (k := k) c B hB
    have h := hx B hB
    rw [map_mul, hd, h, smul_mul_smul_comm, borelCharZ_add hB]

/-- **The determinant twist on denominator bounds.** -/
theorem denomBounded_mul_detPow {I : Finset (Equiv.Perm (Fin N))} (hI : I.Nonempty) (c : ℕ)
    {x : FlagLoc N k} :
    x * (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (detPoly N k)) ^ c
        ∈ denomBounded N k I
      ↔ x ∈ denomBounded N k I := by
  obtain ⟨s, hs⟩ := detPoly_dvd_denomOf (k := k) hI
  constructor
  · rintro ⟨m, p, hp⟩
    refine ⟨m + c, p * s ^ c, ?_⟩
    have hkey : (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (denomOf N k I)) ^ (m + c)
        = (algebraMap _ _ (denomOf N k I)) ^ m
          * ((algebraMap _ _ (detPoly N k)) ^ c * (algebraMap _ _ s) ^ c) := by
      rw [pow_add, hs, map_mul, mul_pow, mul_pow]
    rw [hkey, map_mul, _root_.map_pow, ← hp]
    ring
  · rintro ⟨m, p, hp⟩
    refine ⟨m, p * (detPoly N k) ^ c, ?_⟩
    rw [map_mul, _root_.map_pow, ← hp]
    ring

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- Multiplication by a unit of the localization, as a linear equivalence. -/
noncomputable def mulUnit (v : (FlagLoc N k)ˣ) : FlagLoc N k ≃ₗ[k] FlagLoc N k where
  toFun x := x * (v : FlagLoc N k)
  map_add' x y := add_mul x y _
  map_smul' a x := smul_mul_assoc a x _
  invFun x := x * ((v⁻¹ : (FlagLoc N k)ˣ) : FlagLoc N k)
  left_inv x := by simp
  right_inv x := by simp

/-- The unit of the localization given by a power of the determinant. -/
noncomputable def detUnitPow (N : ℕ) (k : Type*) [Field k] [Infinite k] (c : ℕ) :
    (FlagLoc N k)ˣ :=
  isUnit_algebraMap_detPoly.unit ^ c

theorem coe_detUnitPow (c : ℕ) :
    ((detUnitPow N k c : (FlagLoc N k)ˣ) : FlagLoc N k)
      = (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (detPoly N k)) ^ c := by
  rw [detUnitPow, Units.val_pow_eq_pow_val, IsUnit.unit_spec]

/-- The determinant twist on Čech cochains. -/
noncomputable def twistCochains (N : ℕ) (k : Type*) [Field k] [Infinite k] (c : ℕ) :
    (Finset (Equiv.Perm (Fin N)) → FlagLoc N k) ≃ₗ[k]
      (Finset (Equiv.Perm (Fin N)) → FlagLoc N k) :=
  LinearEquiv.piCongrRight fun _ => mulUnit (detUnitPow N k c)

theorem twistCochains_apply (c : ℕ) (ω : Finset (Equiv.Perm (Fin N)) → FlagLoc N k)
    (I : Finset (Equiv.Perm (Fin N))) :
    twistCochains N k c ω I
      = ω I * (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (detPoly N k)) ^ c := by
  have h : twistCochains N k c ω I = ω I * ((detUnitPow N k c : (FlagLoc N k)ˣ) : FlagLoc N k) :=
    rfl
  rw [h, coe_detUnitPow]

theorem twistCochains_eq_zero_iff (c : ℕ) {x : FlagLoc N k} :
    x * (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (detPoly N k)) ^ c = 0
      ↔ x = 0 := by
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero c algebraMap_detPoly_ne_zero)
  · intro h
    rw [h, zero_mul]

/-- The determinant twist on the sections over a nonempty intersection of cells. -/
theorem mem_cellSections_twist {I : Finset (Equiv.Perm (Fin N))} (hI : I.Nonempty) (c : ℕ)
    {lam : Fin N → ℤ} {x : FlagLoc N k} :
    x * (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (detPoly N k)) ^ c
        ∈ cellSections N k I (fun i => lam i + (c : ℤ))
      ↔ x ∈ cellSections N k I lam := by
  rw [cellSections, cellSections, Submodule.mem_inf, Submodule.mem_inf]
  exact and_congr (flagSemiInv_mul_detPow c) (denomBounded_mul_detPow hI c)

theorem isFlagCochain_twist (c : ℕ) {lam : Fin N → ℤ} {p : ℕ}
    {ω : Finset (Equiv.Perm (Fin N)) → FlagLoc N k} :
    IsFlagCochain (fun i => lam i + (c : ℤ)) p (twistCochains N k c ω) ↔ IsFlagCochain lam p ω := by
  classical
  have hempty : ∀ ν : Finset (Equiv.Perm (Fin N)) → FlagLoc N k,
      (∀ J : Finset (Equiv.Perm (Fin N)), J.card ≠ p + 1 → ν J = 0) → ν ∅ = 0 := by
    intro ν h
    exact h ∅ (by rw [Finset.card_empty]; exact (Nat.succ_ne_zero p).symm)
  constructor
  · intro h
    refine ⟨fun I hI => ?_, fun I => ?_⟩
    · have := h.card I hI
      rw [twistCochains_apply, twistCochains_eq_zero_iff] at this
      exact this
    · rcases I.eq_empty_or_nonempty with rfl | hI
      · have hzero : ω ∅ = 0 := by
          refine hempty ω fun J hJ => ?_
          have := h.card J hJ
          rwa [twistCochains_apply, twistCochains_eq_zero_iff] at this
        rw [hzero]
        exact Submodule.zero_mem _
      · refine (mem_cellSections_twist hI c).mp ?_
        have := h.mem I
        rwa [twistCochains_apply] at this
  · intro h
    refine ⟨fun I hI => ?_, fun I => ?_⟩
    · rw [twistCochains_apply, h.card I hI, zero_mul]
    · rcases I.eq_empty_or_nonempty with rfl | hI
      · rw [twistCochains_apply, hempty ω h.card, zero_mul]
        exact Submodule.zero_mem _
      · rw [twistCochains_apply]
        exact (mem_cellSections_twist hI c).mpr (h.mem I)

theorem cechDModule_twist (c : ℕ) (ω : Finset (Equiv.Perm (Fin N)) → FlagLoc N k) :
    cechDModule k (twistCochains N k c ω) = twistCochains N k c (cechDModule k ω) := by
  funext I
  rw [twistCochains_apply, cechDModule, cechDModule, Finset.sum_mul]
  exact Finset.sum_congr rfl fun u _ => by rw [twistCochains_apply, smul_mul_assoc]

theorem cechDModule_twist_symm (c : ℕ) (ω : Finset (Equiv.Perm (Fin N)) → FlagLoc N k) :
    cechDModule k ((twistCochains N k c).symm ω)
      = (twistCochains N k c).symm (cechDModule k ω) := by
  refine (twistCochains N k c).injective ?_
  rw [← cechDModule_twist, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem mem_flagCochains_twist (c : ℕ) {lam : Fin N → ℤ} {p : ℕ}
    {ω : Finset (Equiv.Perm (Fin N)) → FlagLoc N k} :
    twistCochains N k c ω ∈ flagCochains N k (fun i => lam i + (c : ℤ)) p
      ↔ ω ∈ flagCochains N k lam p :=
  isFlagCochain_twist c

theorem mem_flagCocycles_twist (c : ℕ) {lam : Fin N → ℤ} {p : ℕ}
    {ω : Finset (Equiv.Perm (Fin N)) → FlagLoc N k} :
    twistCochains N k c ω ∈ flagCocycles N k (fun i => lam i + (c : ℤ)) p
      ↔ ω ∈ flagCocycles N k lam p := by
  rw [flagCocycles, flagCocycles, Submodule.mem_inf, Submodule.mem_inf]
  refine and_congr (mem_flagCochains_twist c) ?_
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  show cechDModule k (twistCochains N k c ω) = 0 ↔ cechDModule k ω = 0
  rw [cechDModule_twist]
  constructor
  · intro h
    have := congrArg (twistCochains N k c).symm h
    rwa [LinearEquiv.symm_apply_apply, map_zero] at this
  · intro h
    rw [h, map_zero]

theorem mem_flagCoboundaries_twist (c : ℕ) {lam : Fin N → ℤ} {p : ℕ}
    {ω : Finset (Equiv.Perm (Fin N)) → FlagLoc N k} :
    twistCochains N k c ω ∈ flagCoboundaries N k (fun i => lam i + (c : ℤ)) p
      ↔ ω ∈ flagCoboundaries N k lam p := by
  cases p with
  | zero =>
    rw [flagCoboundaries, flagCoboundaries, Submodule.mem_bot, Submodule.mem_bot]
    constructor
    · intro h
      have := congrArg (twistCochains N k c).symm h
      rwa [LinearEquiv.symm_apply_apply, map_zero] at this
    · intro h
      rw [h, map_zero]
  | succ q =>
    rw [flagCoboundaries, flagCoboundaries]
    constructor
    · rintro ⟨ν, hν, hνeq⟩
      refine ⟨(twistCochains N k c).symm ν, (mem_flagCochains_twist c).mp ?_, ?_⟩
      · rwa [LinearEquiv.apply_symm_apply]
      · show cechDModule k ((twistCochains N k c).symm ν) = ω
        rw [cechDModule_twist_symm]
        show (twistCochains N k c).symm (cechDModule k ν) = ω
        rw [show cechDModule k ν = twistCochains N k c ω from hνeq,
          LinearEquiv.symm_apply_apply]
    · rintro ⟨ν, hν, hνeq⟩
      refine ⟨twistCochains N k c ν, (mem_flagCochains_twist c).mpr hν, ?_⟩
      show cechDModule k (twistCochains N k c ν) = twistCochains N k c ω
      rw [cechDModule_twist]
      exact congrArg _ hνeq

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- The determinant twist as an equivalence of Čech cocycle modules. -/
noncomputable def flagCocyclesTwistEquiv (lam : Fin N → ℤ) (p c : ℕ) :
    ↥(flagCocycles N k lam p) ≃ₗ[k] ↥(flagCocycles N k (fun i => lam i + (c : ℤ)) p) where
  toFun z := ⟨twistCochains N k c (z : Finset (Equiv.Perm (Fin N)) → FlagLoc N k),
    (mem_flagCocycles_twist c).mpr z.2⟩
  map_add' z w := Subtype.ext (map_add _ _ _)
  map_smul' a z := Subtype.ext (map_smul _ _ _)
  invFun w := ⟨(twistCochains N k c).symm (w : Finset (Equiv.Perm (Fin N)) → FlagLoc N k), by
    refine (mem_flagCocycles_twist c).mp ?_
    rw [LinearEquiv.apply_symm_apply]
    exact w.2⟩
  left_inv z := Subtype.ext (LinearEquiv.symm_apply_apply _ _)
  right_inv w := Subtype.ext (LinearEquiv.apply_symm_apply _ _)

theorem flagCoboundaries_comap_twist (lam : Fin N → ℤ) (p c : ℕ) :
    Submodule.comap (flagCocyclesTwistEquiv (k := k) lam p c).toLinearMap
        (Submodule.comap (flagCocycles N k (fun i => lam i + (c : ℤ)) p).subtype
          (flagCoboundaries N k (fun i => lam i + (c : ℤ)) p))
      = Submodule.comap (flagCocycles N k lam p).subtype (flagCoboundaries N k lam p) := by
  ext z
  show twistCochains N k c (z : Finset (Equiv.Perm (Fin N)) → FlagLoc N k)
      ∈ flagCoboundaries N k (fun i => lam i + (c : ℤ)) p
    ↔ (z : Finset (Equiv.Perm (Fin N)) → FlagLoc N k) ∈ flagCoboundaries N k lam p
  exact mem_flagCoboundaries_twist c

/-- **The determinant twist on cohomology.**  `H^p(G/B, L_λ) ≅ H^p(G/B, L_{λ+c})`. -/
noncomputable def flagCohomologyTwistEquiv (lam : Fin N → ℤ) (p c : ℕ) :
    flagCohomology N k lam p ≃ₗ[k] flagCohomology N k (fun i => lam i + (c : ℤ)) p :=
  Submodule.Quotient.equiv _ _ (flagCocyclesTwistEquiv lam p c)
    (by
      rw [← flagCoboundaries_comap_twist lam p c]
      exact Submodule.map_comap_eq_of_surjective
        (flagCocyclesTwistEquiv lam p c).surjective _)

/-- **Every integer weight becomes a natural-number weight after a determinant twist.** -/
theorem exists_natCast_twist (lam : Fin N → ℤ) :
    ∃ (c : ℕ) (mu : Fin N → ℕ), ∀ i, lam i + (c : ℤ) = (mu i : ℤ) := by
  classical
  refine ⟨Finset.univ.sup fun i => (-lam i).toNat, fun i => (lam i
    + ((Finset.univ.sup fun j => (-lam j).toNat : ℕ) : ℤ)).toNat, fun i => ?_⟩
  refine (Int.toNat_of_nonneg ?_).symm
  have h1 : (-lam i).toNat ≤ Finset.univ.sup fun j => (-lam j).toNat :=
    Finset.le_sup (f := fun j => (-lam j).toNat) (Finset.mem_univ i)
  have h2 : -lam i ≤ ((Finset.univ.sup fun j => (-lam j).toNat : ℕ) : ℤ) :=
    le_trans (Int.self_le_toNat _) (Int.ofNat_le.mpr h1)
  omega

/-- **Borel–Weil on the flag variety, for an arbitrary integer weight.**  The zeroth cohomology of
`L_λ` on `G/B` is nonzero exactly for dominant `λ`. -/
theorem flagCohomology_zero_nontrivial_iff_int [CharZero k] (lam : Fin N → ℤ) :
    Nontrivial (flagCohomology N k lam 0) ↔ Antitone lam := by
  obtain ⟨c, mu, hmu⟩ := exists_natCast_twist lam
  have hfun : (fun i => lam i + (c : ℤ)) = fun i => (mu i : ℤ) := funext hmu
  have hequiv : flagCohomology N k lam 0 ≃ₗ[k] flagCohomology N k (fun i => (mu i : ℤ)) 0 := by
    rw [← hfun]
    exact flagCohomologyTwistEquiv lam 0 c
  constructor
  · intro h
    haveI : Nontrivial (flagCohomology N k (fun i => (mu i : ℤ)) 0) := hequiv.symm.toEquiv.nontrivial
    have hmono : Antitone mu := flagCohomology_zero_nontrivial_iff.mp this
    intro i j hij
    have h1 : (mu j : ℤ) ≤ (mu i : ℤ) := Int.ofNat_le.mpr (hmono hij)
    have h2 := hmu i
    have h3 := hmu j
    omega
  · intro hlam
    have hmono : Antitone mu := by
      intro i j hij
      have h1 : lam j ≤ lam i := hlam hij
      have h2 := hmu i
      have h3 := hmu j
      omega
    haveI : Nontrivial (flagCohomology N k (fun i => (mu i : ℤ)) 0) :=
      flagCohomology_zero_nontrivial_iff.mpr hmono
    exact hequiv.toEquiv.nontrivial

end GaloisForLFunctions.HTGeometry.BorelWeil
