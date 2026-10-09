import GaloisForLFunctions.HTGeometry.HankelResolutionCohomology
import GaloisForLFunctions.HTGeometry.HankelSecantKernel
import GaloisForLFunctions.HTGeometry.ProjZeroSections

/-!
# The global sections of the Hankel incidence variety

`Γ(Y, 𝒪_Y)` (`Y = Proj B_j`) is the secant ring `K[x_0, …, x_{N-1}]/secantIdealUpTo` of the first
`j + r` moments (for `j = N - r` the Hankel secant ring `A = K[x]/I_r`): the moments `x_n ↦ v_n`
define a ring map `K[x] → Γ(Y, 𝒪_Y)` (through the degree-zero part of `B` and the structure map
`Y → Spec B_0`) which is surjective, because every global section comes from degree zero
(`hankelY_globalSection_surjective`), and whose kernel is the secant ideal: a polynomial is killed
iff it dies on every chart; the Hankel minors die on every chart, and anything dying on the chart
`G(0) ≠ 0` is killed by the atom parametrization.

* `HTGeometry.momentToGlobal` : `K[x] → Γ(Y, 𝒪_Y)`.
* `HTGeometry.ker_momentToGlobal` : its kernel is `secantIdealUpTo`.
* `HTGeometry.momentToGlobal_surjective`.
* `HTGeometry.secantGlobalEquiv` : `K[x]/secantIdealUpTo ≃+* Γ(Y, 𝒪_Y)`.
-/

namespace HTGeometry

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open GaloisForLFunctions.HTGeometry.StableCoordinate.HomogeneousQuotient

universe u

variable {K : Type u} [Field K] {r N : ℕ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

local notation "𝒵" => projGrading K (Fin (r + 1)) (Fin N)

/-! ## Degree zero is the moments -/

theorem momentEmbed_mem (P : MvPolynomial (Fin N) K) : momentEmbed K r N P ∈ 𝒵 0 := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [momentEmbed, MvPolynomial.rename_C]
    exact MvPolynomial.isWeightedHomogeneous_C _ _
  | add p q hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
  | mul_X p n hp =>
    rw [map_mul, momentEmbed_X]
    simpa using SetLike.mul_mem_graded hp (vv_mem (K := K) (r := r) n)

/-- **Degree-zero polynomials are polynomials in the moments.** -/
theorem exists_momentEmbed_eq {a : IncRing K r N} (ha : a ∈ 𝒵 0) :
    ∃ P, momentEmbed K r N P = a := by
  refine MvPolynomial.exists_rename_eq_of_vars_subset_range a Sum.inr Sum.inr_injective ?_
  intro k hk
  rcases k with i | n
  · exfalso
    rw [Finset.mem_coe, MvPolynomial.mem_vars_iff_mem_support] at hk
    obtain ⟨b, hb, hbi⟩ := hk
    have hw := (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp ha
      (MvPolynomial.mem_support_iff.mp hb)
    rw [weight_projWeight] at hw
    have hpos : 0 < b (Sum.inl i) := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hbi)
    have : b (Sum.inl i) ≤ ∑ i', b (Sum.inl i') :=
      Finset.single_le_sum (f := fun i' => b (Sum.inl i')) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    omega
  · exact ⟨n, rfl⟩

variable (K r N) in
/-- **The moments in degree zero of `B_j`.** -/
noncomputable def momentToZero (j : ℕ) : MvPolynomial (Fin N) K →+* quotGrading K r N j 0 where
  toFun P := ⟨Ideal.Quotient.mk _ (momentEmbed K r N P), mk_mem_piece 𝒵 _ (momentEmbed_mem P)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' P Q := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' P Q := Subtype.ext (by simp)

theorem momentToZero_coe (j : ℕ) (P : MvPolynomial (Fin N) K) :
    (momentToZero K r N j P : HankelQuot K r N j) = Ideal.Quotient.mk _ (momentEmbed K r N P) :=
  rfl

theorem momentToZero_surjective (j : ℕ) : Function.Surjective (momentToZero K r N j) := by
  rintro ⟨x, a, ha, rfl⟩
  obtain ⟨P, rfl⟩ := exists_momentEmbed_eq ha
  exact ⟨P, rfl⟩

variable (K r N) in
/-- **The moments as global sections of `𝒪_Y`.** -/
noncomputable def momentToGlobal (j : ℕ) : MvPolynomial (Fin N) K →+* Γ(HankelY K r N j, ⊤) :=
  (zeroToGlobal (quotGrading K r N j)).hom.comp (momentToZero K r N j)

variable (K r N) in
/-- The evaluation charts of `Y`. -/
noncomputable abbrev hankelChart (j : ℕ) (k : Fin (r + 1)) : (HankelY K r N j).Opens :=
  Proj.basicOpen (quotGrading K r N j) (qChart K r N j k)

variable {j : ℕ}

theorem momentToGlobal_restrict (k : Fin (r + 1)) (P : MvPolynomial (Fin N) K) :
    ((HankelY K r N j).presheaf.map (homOfLE (le_top : hankelChart K r N j k ≤ ⊤)).op).hom
        (momentToGlobal K r N j P)
      = (Proj.awayToSection (quotGrading K r N j) (qChart K r N j k)).hom
          (HomogeneousLocalization.fromZeroRingHom _ _ (momentToZero K r N j P)) :=
  zeroToGlobal_restrict _ (qChart_mem (K := K) (r := r) (N := N) j k) one_pos _

theorem fromZero_eq_zero_iff {f : HankelQuot K r N j} (y : quotGrading K r N j 0) :
    HomogeneousLocalization.fromZeroRingHom (quotGrading K r N j) (Submonoid.powers f) y = 0 ↔
      ∃ m : ℕ, f ^ m * (y : HankelQuot K r N j) = 0 := by
  rw [← HomogeneousLocalization.val_injective _ |>.eq_iff, HomogeneousLocalization.val_zero]
  change HomogeneousLocalization.val (HomogeneousLocalization.mk ⟨0, y, 1, _⟩) = 0 ↔ _
  rw [HomogeneousLocalization.val_mk]
  change Localization.mk (y : HankelQuot K r N j) 1 = 0 ↔ _
  rw [Localization.mk_one_eq_algebraMap, IsLocalization.map_eq_zero_iff (Submonoid.powers f)]
  constructor
  · rintro ⟨⟨_, m, rfl⟩, hm⟩
    exact ⟨m, hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨⟨f ^ m, m, rfl⟩, hm⟩

theorem awayToSection_injective (k : Fin (r + 1)) :
    Function.Injective (Proj.awayToSection (quotGrading K r N j)
      (qChart K r N j k)).hom := by
  haveI : IsIso (Proj.awayToSection (quotGrading K r N j) (qChart K r N j k)) := by
    rw [← Proj.basicOpenIsoAway_hom _ _ (qChart_mem (K := K) (r := r) (N := N) j k) one_pos]
    infer_instance
  exact (ConcreteCategory.bijective_of_isIso _).1

/-- **Global sections are determined on the evaluation charts.** -/
theorem globalSection_ext [CharZero K] {σ τ : Γ(HankelY K r N j, ⊤)}
    (h : ∀ k, ((HankelY K r N j).presheaf.map (homOfLE (le_top : hankelChart K r N j k ≤ ⊤)).op).hom σ
      = ((HankelY K r N j).presheaf.map (homOfLE (le_top : hankelChart K r N j k ≤ ⊤)).op).hom τ) :
    σ = τ :=
  TopCat.Sheaf.eq_of_locally_eq' (schemeAbSheaf (HankelY K r N j)) (hankelChart K r N j) ⊤
    (fun _ => homOfLE le_top)
    (le_of_eq (iSup_hankelChart_eq_top (K := K) (r := r) (N := N) j).symm) σ τ h

theorem momentToGlobal_eq_zero_iff_chart (k : Fin (r + 1)) (P : MvPolynomial (Fin N) K) :
    ((HankelY K r N j).presheaf.map (homOfLE (le_top : hankelChart K r N j k ≤ ⊤)).op).hom
        (momentToGlobal K r N j P) = 0 ↔
      ∃ m : ℕ, chartForm K r N (node K k) ^ m * momentEmbed K r N P ∈ hankelIdeal K r N j := by
  rw [momentToGlobal_restrict, ← map_zero (Proj.awayToSection (quotGrading K r N j)
    (qChart K r N j k)).hom, (awayToSection_injective k).eq_iff, fromZero_eq_zero_iff,
    momentToZero_coe]
  simp only [qChart, ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]

/-! ## Surjectivity and the kernel -/

/-- **Every global section of `𝒪_Y` is a polynomial in the moments.** -/
theorem momentToGlobal_surjective [CharZero K] (hj : j + r ≤ N) :
    Function.Surjective (momentToGlobal K r N j) := by
  intro σ
  have h1 := iSup_hankelChart_eq_top (K := K) (r := r) (N := N) j
  have h0 := hankelCech_exactAt (K := K) (r := r) (N := N) j hj 0 0 le_rfl
  obtain ⟨b, hb⟩ := exists_zeroToGlobal_eq (𝒜 := quotGrading K r N j)
    (w := qChart K r N j) (qChart_mem j) h1 h0 σ
  obtain ⟨P, rfl⟩ := momentToZero_surjective (K := K) (r := r) (N := N) j b
  exact ⟨P, hb⟩

/-- **The kernel of the moments on `Y` is the secant ideal of the first `j + r` moments.** -/
theorem ker_momentToGlobal [CharZero K] (hj : j + r ≤ N) :
    RingHom.ker (momentToGlobal K r N j) = secantIdealUpTo K N r j := by
  refine le_antisymm (fun P hP => ?_) (Ideal.span_le.mpr ?_)
  · rw [RingHom.mem_ker] at hP
    obtain ⟨m, hm⟩ := (momentToGlobal_eq_zero_iff_chart 0 P).mp (by rw [hP, map_zero])
    have h0 : node K (0 : Fin (r + 1)) = 0 := by simp [node]
    rw [h0] at hm
    exact mem_secantIdealUpTo_of_chartZero hj hm
  · rintro _ ⟨c, hbound, -, hc, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    refine globalSection_ext fun k => ?_
    rw [map_zero, momentToGlobal_eq_zero_iff_chart]
    exact ⟨1, by rw [pow_one]; exact chartForm_mul_minor_mem _ hbound hc⟩

/-- **`Γ(Y, 𝒪_Y)` is the secant ring of the first `j + r` moments.** -/
noncomputable def secantGlobalEquiv [CharZero K] (hj : j + r ≤ N) :
    MvPolynomial (Fin N) K ⧸ secantIdealUpTo K N r j ≃+* Γ(HankelY K r N j, ⊤) :=
  (Ideal.quotEquivOfEq (ker_momentToGlobal hj).symm).trans
    (RingHom.quotientKerEquivOfSurjective (momentToGlobal_surjective hj))

theorem secantGlobalEquiv_mk [CharZero K] (hj : j + r ≤ N) (P : MvPolynomial (Fin N) K) :
    secantGlobalEquiv hj (Ideal.Quotient.mk _ P) = momentToGlobal K r N j P := rfl

end HTGeometry
