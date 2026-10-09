import GaloisForLFunctions.HTGeometry.HankelResolutionSmooth
import GaloisForLFunctions.HTGeometry.HankelLeadingChart
import GaloisForLFunctions.HTGeometry.HankelMomentTransform
import Mathlib.AlgebraicGeometry.Birational.Birational

/-!
# The resolution of the Hankel secant variety is birational

Let `δ = det (x_{N-2r+1+i+j})_{i,j<r}` be the trailing `r × r` Hankel minor (`2r ≤ N`).  On the chart
`z_0 ≠ 0` of `Y`, the last `r` Hankel equations read `M a = -w` with `M` the Hankel matrix of `δ`, so by
Cramer's rule `δ · a_i` is a polynomial in the moments.  Hence the chart ring `C_0` becomes, after
inverting `δ`, the localization `A_δ` (`A → C_0` is injective: the kernel computation of
`HankelSecantKernel`).  So `π` is an isomorphism from the dense open `{δ ≠ 0}` of the chart onto the
dense open `D(δ)` of `Spec A`: `π` is birational.

* `HTGeometry.bijective_of_away` : the localization comparison.
* `HTGeometry.trailMinor` and `HTGeometry.trailMinor_notMem`.
* `HTGeometry.chartZero_exists_pow_mul_eq` : `δ^n · c` is a moment polynomial for every `c ∈ C_0`.
-/

namespace HTGeometry

/-! ## Comparing two localizations -/

/-- **A map of localizations away from `d` and `β d`** is bijective when `β` is injective and every
element of the target becomes a value of `β` after multiplication by a power of `β d`. -/
theorem bijective_of_away {R S Rd Sg : Type*} [CommRing R] [CommRing S] [CommRing Rd]
    [CommRing Sg] [Algebra R Rd] [Algebra S Sg] (d : R) [IsLocalization.Away d Rd] (β : R →+* S)
    [IsLocalization.Away (β d) Sg] (φ : Rd →+* Sg)
    (hφ : ∀ a, φ (algebraMap R Rd a) = algebraMap S Sg (β a))
    (hinj : Function.Injective β) (hgen : ∀ s, ∃ n a, β d ^ n * s = β a) :
    Function.Bijective φ := by
  have hφmk : ∀ (a : R) (n : ℕ), φ (IsLocalization.mk' Rd a (⟨d ^ n, n, rfl⟩ : Submonoid.powers d))
      * algebraMap S Sg (β d) ^ n = algebraMap S Sg (β a) := by
    intro a n
    rw [← map_pow, ← map_pow, ← hφ, ← hφ, ← map_mul, IsLocalization.mk'_spec]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers d) x
    have h1 := hφmk a n
    rw [hx, zero_mul, eq_comm, IsLocalization.map_eq_zero_iff (Submonoid.powers (β d))] at h1
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := h1
    have h2 : β (d ^ m * a) = 0 := by rw [map_mul, map_pow]; exact hm
    rw [← map_zero β] at h2
    have h3 := hinj h2
    rw [IsLocalization.mk'_eq_zero_iff]
    exact ⟨⟨d ^ m, m, rfl⟩, h3⟩
  · intro y
    obtain ⟨⟨s, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (β d)) y
    obtain ⟨m, a, ha⟩ := hgen s
    refine ⟨IsLocalization.mk' Rd a (⟨d ^ (m + n), m + n, rfl⟩ : Submonoid.powers d), ?_⟩
    have hu : IsUnit (algebraMap S Sg (β d)) := IsLocalization.Away.algebraMap_isUnit (β d)
    have h1 := hφmk a (m + n)
    show _ = IsLocalization.mk' Sg s (⟨β d ^ n, n, rfl⟩ : Submonoid.powers (β d))
    rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul]
    apply (hu.pow m).mul_left_cancel
    rw [← map_pow, ← map_mul, ha, ← h1]
    change _ = _ * (_ * algebraMap S Sg (β d ^ n))
    rw [mul_left_comm, map_pow (algebraMap S Sg) (β d) n, map_pow (algebraMap S Sg) (β d) m,
      ← pow_add]

/-! ## The chart `z_0 ≠ 0` against the trailing minor -/

section ChartZero

open HomogeneousLocalization GaloisForLFunctions.HTGeometry.StableCoordinate.HomogeneousQuotient

variable {K : Type} [Field K] {r N j : ℕ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

local notation "𝒜" => quotGrading K r N j

theorem node_zero : node K (0 : Fin (r + 1)) = 0 := by simp [node]

/-- **The moment shift at `0` is the identity.** -/
theorem momentShift_zero' : momentShift K r N 0 = AlgHom.id K _ := by
  refine MvPolynomial.algHom_ext fun k => ?_
  rcases k with i | n
  · have := momentShift_zv (K := K) (N := N) 0 i
    rw [show (MvPolynomial.X (Sum.inl i) : IncRing K r N) = zv K r N i from rfl, this, map_zero,
      Polynomial.C_0, add_zero, Polynomial.comp_X, gPoly_coeff, dif_pos i.2]
    rfl
  · have := momentShift_vv (K := K) (r := r) 0 n
    rw [show (MvPolynomial.X (Sum.inr n) : IncRing K r N) = vv K r N n from rfl, this, map_zero,
      Polynomial.C_0, sub_zero, momentPair_X_pow]
    rfl

theorem momentShift_node_zero (x : IncRing K r N) : momentShift K r N (node K (0 : Fin (r + 1))) x = x := by
  rw [node_zero, momentShift_zero']
  rfl

variable (K r N j) in
/-- The moments on the chart `z_0 ≠ 0`: `K[x] → C_0`. -/
noncomputable def chartAlpha : MvPolynomial (Fin N) K →+* Away 𝒜 (tChart K r N j (node K (0 : Fin (r + 1)))) :=
  (fromZeroRingHom 𝒜 _).comp (momentToZero K r N j)

theorem chartAlpha_coord (m : ℕ) :
    chartAlpha K r N j (GaloisForLFunctions.HTGeometry.hankelCoord K N m)
      = fromZeroRingHom 𝒜 _ (shiftV K r N j (node K (0 : Fin (r + 1))) m) := by
  rw [chartAlpha, RingHom.comp_apply]
  congr 1
  apply Subtype.ext
  change Ideal.Quotient.mk _ (momentEmbed K r N _) = Ideal.Quotient.mk _ (momentShift K r N _ _)
  rw [momentShift_node_zero, GaloisForLFunctions.HTGeometry.hankelCoord, vAt]
  split_ifs with h
  · rw [momentEmbed_X]
  · rw [map_zero]

theorem chartAlpha_C (c : K) :
    chartAlpha K r N j (MvPolynomial.C c) = fromZeroRingHom 𝒜 _ (algebraMap K (𝒜 0) c) := by
  rw [chartAlpha, RingHom.comp_apply]
  congr 1
  apply Subtype.ext
  simp [momentToZero, momentEmbed]
  rfl

/-- **The kernel of the moments on the chart is the secant ideal.** -/
theorem chartAlpha_eq_zero_iff (hj : j + r ≤ N) (P : MvPolynomial (Fin N) K) :
    chartAlpha K r N j P = 0 ↔ P ∈ secantIdealUpTo K N r j := by
  constructor
  · intro h
    rw [chartAlpha, RingHom.comp_apply, fromZero_eq_zero_iff, momentToZero_coe] at h
    obtain ⟨m, hm⟩ := h
    rw [tChart, ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, node_zero] at hm
    exact mem_secantIdealUpTo_of_chartZero hj hm
  · intro hP
    have hle : secantIdealUpTo K N r j ≤ RingHom.ker (chartAlpha K r N j) := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨c, hbound, -, hc, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, chartAlpha, RingHom.comp_apply, fromZero_eq_zero_iff]
      refine ⟨1, ?_⟩
      rw [momentToZero_coe, pow_one, tChart, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact chartForm_mul_minor_mem _ hbound hc
    exact hle hP

variable (K r N j) in
/-- The trailing Hankel block `(x_{N-2r+1+i+j})_{j,i<r}`. -/
noncomputable def trailMat : Matrix (Fin r) (Fin r) (MvPolynomial (Fin N) K) :=
  Matrix.of fun j' i => GaloisForLFunctions.HTGeometry.hankelCoord K N (j - r + 1 + i + j')

variable (K r N j) in
/-- **The trailing `r × r` Hankel minor.** -/
noncomputable def trailMinor : MvPolynomial (Fin N) K := (trailMat K r N j).det

variable (K r N j) in
/-- The right-hand side `-x_{N-2r+j}`. -/
noncomputable def trailRhs : Fin r → MvPolynomial (Fin N) K :=
  fun j' => -GaloisForLFunctions.HTGeometry.hankelCoord K N (j - r + j')

/-- The last `r` dehomogenized Hankel equations on the chart, as a linear system. -/
theorem trail_system (hrj : r ≤ j) (hj : j + r ≤ N) :
    ((chartAlpha K r N j).mapMatrix (trailMat K r N j)).mulVec
        (fun i => chartPhi K r N j (node K (0 : Fin (r + 1))) (MvPolynomial.X (Sum.inl i)))
      = chartAlpha K r N j ∘ trailRhs K r N j := by
  funext j'
  have hj' := j'.isLt
  have h := fromZero_shiftV_eq (K := K) (r := r) (N := N) hj (node K (0 : Fin (r + 1)))
    (m := j - r + j') (by omega)
  rw [Function.comp_apply, trailRhs, map_neg, chartAlpha_coord, h, neg_neg, Matrix.mulVec,
    dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, trailMat, Matrix.of_apply, chartAlpha_coord,
    mul_comm, chartPhi, MvPolynomial.eval₂Hom_X', Sum.elim_inl]
  congr 3
  omega

/-- **Cramer's rule on the chart**: `δ · a_i` is a moment polynomial. -/
theorem trailMinor_mul_coord (hrj : r ≤ j) (hj : j + r ≤ N) (i : Fin r) :
    chartAlpha K r N j (trailMinor K r N j) * chartPhi K r N j (node K (0 : Fin (r + 1))) (MvPolynomial.X (Sum.inl i))
      = chartAlpha K r N j (((trailMat K r N j).adjugate.mulVec (trailRhs K r N j)) i) := by
  set M := (chartAlpha K r N j).mapMatrix (trailMat K r N j)
  set a := fun i => chartPhi K r N j (node K (0 : Fin (r + 1))) (MvPolynomial.X (Sum.inl i))
  have h1 : M.det • a = M.adjugate.mulVec (chartAlpha K r N j ∘ trailRhs K r N j) := by
    rw [← trail_system hrj hj, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have h2 := congrFun h1 i
  rw [Pi.smul_apply, smul_eq_mul] at h2
  rw [trailMinor, RingHom.map_det, h2, RingHom.map_mulVec]
  congr 2
  exact (RingHom.map_adjugate _ _).symm

/-- **Every element of the chart ring is a moment fraction with denominator a power of `δ`.** -/
theorem chartZero_exists_pow_mul_eq (hrj : r ≤ j) (hj : j + r ≤ N) (c : Away 𝒜 (tChart K r N j (node K (0 : Fin (r + 1))))) :
    ∃ (n : ℕ) (P : MvPolynomial (Fin N) K),
      chartAlpha K r N j (trailMinor K r N j) ^ n * c = chartAlpha K r N j P := by
  obtain ⟨p, rfl⟩ := chartPhi_surjective (K := K) (r := r) (N := N) (by omega) (node K (0 : Fin (r + 1))) c
  induction p using MvPolynomial.induction_on with
  | C k =>
    refine ⟨0, MvPolynomial.C k, ?_⟩
    rw [pow_zero, one_mul, chartAlpha_C, chartPhi, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
  | add p q hp hq =>
    obtain ⟨n₁, P₁, h₁⟩ := hp
    obtain ⟨n₂, P₂, h₂⟩ := hq
    refine ⟨n₁ + n₂, trailMinor K r N j ^ n₂ * P₁ + trailMinor K r N j ^ n₁ * P₂, ?_⟩
    rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow, ← h₁, ← h₂, pow_add]
    ring
  | mul_X p k hp =>
    obtain ⟨n₁, P₁, h₁⟩ := hp
    rcases k with i | n
    · refine ⟨n₁ + 1, P₁ * ((trailMat K r N j).adjugate.mulVec (trailRhs K r N j)) i, ?_⟩
      rw [map_mul, map_mul, ← trailMinor_mul_coord hrj hj i, ← h₁, pow_succ]
      ring
    · refine ⟨n₁, P₁ * GaloisForLFunctions.HTGeometry.hankelCoord K N (j + n), ?_⟩
      rw [map_mul, map_mul, chartAlpha_coord, ← h₁, mul_assoc]
      congr 2
      rw [chartPhi, MvPolynomial.eval₂Hom_X', Sum.elim_inr]

/-- **The trailing minor is the reversal of the leading one** (on the first `j + r` moments). -/
theorem momentRev_hankelLeadMinor (hrj : r ≤ j) :
    GaloisForLFunctions.HTGeometry.momentRev K (j + r)
        (GaloisForLFunctions.HTGeometry.hankelLeadMinor K (j + r) r)
      = trailMinor K r (j + r) j := by
  rw [GaloisForLFunctions.HTGeometry.hankelLeadMinor, AlgEquiv.map_det, trailMinor,
    ← Matrix.det_submatrix_equiv_self Fin.revPerm]
  congr 1
  refine Matrix.ext fun i i' => ?_
  simp only [AlgEquiv.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.submatrix_apply,
    trailMat, Fin.revPerm_apply, Fin.val_rev, GaloisForLFunctions.HTGeometry.hankelCoord]
  have hi := i.isLt
  have hi' := i'.isLt
  rw [dif_pos (by omega), dif_pos (by omega), GaloisForLFunctions.HTGeometry.momentRev_X]
  refine congrArg (MvPolynomial.X (R := K)) (Fin.ext ?_)
  rw [Fin.val_rev]
  simp only
  omega

variable (K r N j) in
/-- Forgetting the free moments: `x_n ↦ x_n` (`n < j + r`), `x_n ↦ 0` (`n ≥ j + r`). -/
noncomputable def forgetFree : MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin (j + r)) K :=
  MvPolynomial.aeval fun n => if h : (n : ℕ) < j + r then MvPolynomial.X ⟨n, h⟩ else 0

theorem forgetFree_coord (hj : j + r ≤ N) {m : ℕ} (hm : m < j + r) :
    forgetFree K r N j (GaloisForLFunctions.HTGeometry.hankelCoord K N m)
      = GaloisForLFunctions.HTGeometry.hankelCoord K (j + r) m := by
  rw [GaloisForLFunctions.HTGeometry.hankelCoord, GaloisForLFunctions.HTGeometry.hankelCoord,
    dif_pos hm]
  split_ifs with h
  · rw [forgetFree, MvPolynomial.aeval_X, dif_pos hm]
  · exact absurd (lt_of_lt_of_le hm hj) h

theorem forgetFree_trailMinor (hrj : r ≤ j) (hj : j + r ≤ N) :
    forgetFree K r N j (trailMinor K r N j) = trailMinor K r (j + r) j := by
  rw [trailMinor, trailMinor, AlgHom.map_det]
  congr 1
  refine Matrix.ext fun i i' => ?_
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, trailMat, trailMat, Matrix.of_apply,
    Matrix.of_apply, forgetFree_coord hj (by have := i.isLt; have := i'.isLt; omega)]

theorem forgetFree_secantIdealUpTo :
    (secantIdealUpTo K N r j).map (forgetFree K r N j)
      ≤ RHTower.finiteHankelSecantIdeal K (j + r) r := by
  rw [secantIdealUpTo, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨c, hb, hmono, hc, rfl⟩, rfl⟩
  have hb' : ∀ i, r + 1 + c i ≤ j + r := fun i => by have := hc i; omega
  have h : forgetFree K r N j (RHTower.finiteHankelMaximalMinorOver K c hb)
      = RHTower.finiteHankelMaximalMinorOver K c hb' := by
    rw [RHTower.finiteHankelMaximalMinorOver, RHTower.finiteHankelMaximalMinorOver, AlgHom.map_det]
    congr 1
    refine Matrix.ext fun i i' => ?_
    have hlt : i.val + c i' < j + r := by have := i.isLt; have := hc i'; omega
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply, forgetFree, MvPolynomial.aeval_X,
      RHTower.finiteHankelIndex, dif_pos hlt]
    rfl
  rw [SetLike.mem_coe, h]
  exact Ideal.subset_span ⟨c, hb', hmono, rfl⟩

/-- **The trailing minor is nonzero in the secant ring.** -/
theorem trailMinor_notMem [CharZero K] (hrj : r ≤ j) (hj : j + r ≤ N) :
    trailMinor K r N j ∉ secantIdealUpTo K N r j := by
  intro h
  have h0 := forgetFree_secantIdealUpTo (Ideal.mem_map_of_mem (forgetFree K r N j) h)
  rw [forgetFree_trailMinor hrj hj] at h0
  have h1 := GaloisForLFunctions.HTGeometry.momentRev_mem_secantIdeal K (j + r) r h0
  rw [← momentRev_hankelLeadMinor hrj, GaloisForLFunctions.HTGeometry.momentRev_momentRev] at h1
  have h2 : GaloisForLFunctions.HTGeometry.hankelChartElem K (j + r) r = 0 := by
    rw [GaloisForLFunctions.HTGeometry.hankelChartElem_eq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h1
  rw [GaloisForLFunctions.HTGeometry.hankelChartElem] at h2
  have h3 := GaloisForLFunctions.HTGeometry.hankelChartHom_injective K (show 2 * r ≤ j + r by omega)
    (h2.trans (map_zero _).symm)
  exact GaloisForLFunctions.HTGeometry.hankelLeadMinor_ne_zero K h3

end ChartZero

/-! ## The isomorphism over the dense open `D(δ)` -/

section Birational

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

variable {K : Type} [Field K] {r N j : ℕ}

local notation "𝒜" => quotGrading K r N j

theorem secantRing_isDomain (hj : j + r ≤ N) : IsDomain (SecantRing K r N j) := by
  haveI := secantIdealUpTo_isPrime (K := K) hj
  exact Ideal.Quotient.isDomain _

/-- `π^#` on global sections. -/
theorem hankelResolution_appTop_apply [CharZero K] (hj : j + r ≤ N) (x : SecantRing K r N j) :
    (hankelResolution K r N hj).appTop ((Scheme.ΓSpecIso (CommRingCat.of (SecantRing K r N j))).inv x)
      = secantGlobalEquiv hj x := by
  have h : (Scheme.ΓSpecIso (CommRingCat.of (SecantRing K r N j))).inv ≫
      (hankelResolution K r N hj).appTop = (secantGlobalIso K r N hj).hom := by
    rw [hankelResolution, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have h' := congrArg (fun φ => φ.hom x) h
  rw [CommRingCat.hom_comp, RingHom.comp_apply] at h'
  exact h'

theorem awayToSection_bijective' {f : HankelQuot K r N j} (hf : f ∈ 𝒜 1) :
    Function.Bijective (Proj.awayToSection 𝒜 f).hom := by
  haveI : IsIso (Proj.awayToSection 𝒜 f) := by
    rw [← Proj.basicOpenIsoAway_hom _ _ hf one_pos]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso _

variable (K r N j) in
/-- The chart `z_0 ≠ 0` of `Y`. -/
noncomputable abbrev chartZeroOpen : (HankelY K r N j).Opens :=
  Proj.basicOpen 𝒜 (tChart K r N j (node K (0 : Fin (r + 1))))

theorem chartZeroOpen_isAffineOpen : IsAffineOpen (chartZeroOpen K r N j) :=
  Proj.isAffineOpen_basicOpen _ _ (tChart_mem _) one_pos

variable (K r N) in
/-- The moments restricted to the chart `z_0 ≠ 0`, from `Γ(Spec A)`. -/
noncomputable def chartBeta [CharZero K] (hj : j + r ≤ N) :
    Γ(Spec (CommRingCat.of (SecantRing K r N j)), ⊤) →+* Γ(HankelY K r N j, chartZeroOpen K r N j) :=
  ((HankelY K r N j).presheaf.map (homOfLE (le_top : chartZeroOpen K r N j ≤ ⊤)).op).hom.comp
    (hankelResolution K r N hj).appTop.hom

theorem chartBeta_apply [CharZero K] (hj : j + r ≤ N) (P : MvPolynomial (Fin N) K) :
    chartBeta K r N hj ((Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk _ P))
      = (Proj.awayToSection 𝒜 (tChart K r N j (node K (0 : Fin (r + 1))))).hom (chartAlpha K r N j P) := by
  rw [chartBeta, RingHom.comp_apply, hankelResolution_appTop_apply, secantGlobalEquiv_mk]
  exact zeroToGlobal_restrict _ (tChart_mem _) one_pos _

theorem chartBeta_injective [CharZero K] (hj : j + r ≤ N) : Function.Injective (chartBeta K r N hj) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ : ∃ y, (Scheme.ΓSpecIso (CommRingCat.of (SecantRing K r N j))).inv y = x :=
    ⟨(Scheme.ΓSpecIso _).hom x, by
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]⟩
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [chartBeta_apply, ← map_zero (Proj.awayToSection 𝒜 _).hom,
    (awayToSection_bijective' (tChart_mem _)).1.eq_iff, chartAlpha_eq_zero_iff hj] at hx
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

variable (K r N j) in
/-- The trailing minor as a global function on `Spec A`. -/
noncomputable def trailSection : Γ(Spec (CommRingCat.of (SecantRing K r N j)), ⊤) :=
  (Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk _ (trailMinor K r N j))

theorem trailSection_ne_zero [CharZero K] (hrj : r ≤ j) (hj : j + r ≤ N) : trailSection K r N j ≠ 0 := by
  intro h
  have h1 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (SecantRing K r N j))).hom.hom h
  rw [trailSection, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero,
    Ideal.Quotient.eq_zero_iff_mem] at h1
  exact trailMinor_notMem hrj hj h1

theorem chartBeta_gen [CharZero K] (hrj : r ≤ j) (hj : j + r ≤ N) (s : Γ(HankelY K r N j, chartZeroOpen K r N j)) :
    ∃ (n : ℕ) (x : Γ(Spec (CommRingCat.of (SecantRing K r N j)), ⊤)),
      chartBeta K r N hj (trailSection K r N j) ^ n * s = chartBeta K r N hj x := by
  obtain ⟨c, rfl⟩ := (awayToSection_bijective' (tChart_mem (K := K) (r := r) (N := N)
    (node K (0 : Fin (r + 1))))).2 s
  obtain ⟨n, P, hP⟩ := chartZero_exists_pow_mul_eq hrj hj c
  refine ⟨n, (Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk _ P), ?_⟩
  rw [trailSection, chartBeta_apply, chartBeta_apply, ← map_pow, ← map_mul, hP]

variable (K r N) in
/-- **The source of the birational isomorphism**: `{δ ≠ 0}` inside the chart `z_0 ≠ 0`. -/
noncomputable abbrev birSource [CharZero K] (hj : j + r ≤ N) : (HankelY K r N j).Opens :=
  (HankelY K r N j).basicOpen (chartBeta K r N hj (trailSection K r N j))

variable (K r N j) in
/-- **The target**: `D(δ) ⊆ Spec A`. -/
noncomputable abbrev birTarget : (Spec (CommRingCat.of (SecantRing K r N j))).Opens :=
  (Spec (CommRingCat.of (SecantRing K r N j))).basicOpen (trailSection K r N j)

theorem birSource_le [CharZero K] (hj : j + r ≤ N) :
    birSource K r N hj ≤ hankelResolution K r N hj ⁻¹ᵁ birTarget K r N j := by
  rw [Scheme.preimage_basicOpen_top, birSource, chartBeta, RingHom.comp_apply, Scheme.basicOpen_res]
  exact inf_le_right

/-- **`π` identifies the sections over `D(δ)` and over `{δ ≠ 0}`.** -/
theorem appLE_bijective [CharZero K] (hrj : r ≤ j) (hj : j + r ≤ N) :
    Function.Bijective ((hankelResolution K r N hj).appLE (birTarget K r N j)
      (birSource K r N hj) (birSource_le _)).hom := by
  haveI := chartZeroOpen_isAffineOpen.isLocalization_basicOpen
    (chartBeta K r N hj (trailSection K r N j))
  refine bijective_of_away (trailSection K r N j) (chartBeta K r N _) _ ?_
    (chartBeta_injective _) (chartBeta_gen hrj hj)
  intro x
  have e1 := congrArg (fun φ => φ.hom x) (Scheme.Hom.map_appLE (hankelResolution K r N hj)
    (birSource_le (K := K) hj)
    (homOfLE ((Spec (CommRingCat.of (SecantRing K r N j))).basicOpen_le (trailSection K r N j))).op)
  rw [CommRingCat.hom_comp, RingHom.comp_apply] at e1
  change _ = ((HankelY K r N j).presheaf.map _).hom (((HankelY K r N j).presheaf.map _).hom
    ((hankelResolution K r N hj).appTop.hom x))
  rw [RingHom.algebraMap_toAlgebra, e1, ← CommRingCat.comp_apply, ← Functor.map_comp,
    Scheme.Hom.appLE, CommRingCat.comp_apply]
  rfl

/-- **`π` restricts to an isomorphism `{δ ≠ 0} ≅ D(δ)`.** -/
theorem resLE_isIso [CharZero K] (hrj : r ≤ j) (hj : j + r ≤ N) :
    IsIso ((hankelResolution K r N hj).resLE (birTarget K r N j) (birSource K r N hj)
      (birSource_le _)) := by
  haveI : IsAffine (birTarget K r N j).toScheme :=
    (isAffineOpen_top (Spec (CommRingCat.of (SecantRing K r N j)))).basicOpen _
  haveI : IsAffine (birSource K r N hj).toScheme :=
    chartZeroOpen_isAffineOpen.basicOpen _
  haveI : IsIso ((hankelResolution K r N hj).appLE (birTarget K r N j)
      (birSource K r N hj) (birSource_le _)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (appLE_bijective hrj hj)
  rw [← MorphismProperty.isomorphisms.iff,
    HasAffineProperty.iff_of_isAffine (P := MorphismProperty.isomorphisms Scheme)]
  refine ⟨inferInstance, ?_⟩
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  infer_instance

/-! ### Density -/

theorem birTarget_dense [CharZero K] (hrj : r ≤ j) (hj : j + r ≤ N) :
    Dense (birTarget K r N j : Set (Spec (CommRingCat.of (SecantRing K r N j)))) := by
  haveI := secantRing_isDomain (K := K) hj
  have hne : birTarget K r N j ≠ ⊥ := by
    rw [Ne, basicOpen_eq_bot_iff]
    exact trailSection_ne_zero hrj hj
  exact (birTarget K r N j).isOpen.dense ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hne)

theorem isDomain_chart (hj : j + r ≤ N) (k : Fin (r + 1)) :
    IsDomain (Away 𝒜 (qChart K r N j k)) :=
  (chartRingEquiv K r N hj (node K k)).symm.toMulEquiv.isDomain _

theorem constantCoeff_incChartEval_chartForm (s : K) :
    MvPolynomial.constantCoeff (incChartEval K r N j (chartForm K r N s)) = 1 := by
  have hcf : chartForm K r N s = ∑ i : Fin (r + 1), zv K r N i * algebraMap K _ (s ^ (i : ℕ)) := by
    rw [chartForm, gPoly, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, map_pow]
  rw [hcf, map_sum, map_sum, Fin.sum_univ_succ]
  simp only [map_mul, incChartEval_zv, chartZ, Fin.cons_zero, Fin.cons_succ,
    MvPolynomial.algebraMap_eq, MvPolynomial.constantCoeff_X, map_one,
    one_mul, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero]

/-- **Every chart meets the chart `z_0 ≠ 0`.** -/
theorem chart_inter_nonempty (hj : j + r ≤ N) (k : Fin (r + 1)) :
    ((hankelChart K r N j k : Set (HankelY K r N j)) ∩ hankelChart K r N j 0).Nonempty := by
  haveI := isDomain_chart (K := K) hj k
  have hpre := Proj.awayι_preimage_basicOpen 𝒜 (qChart_mem (K := K) (r := r) (N := N) j k)
    one_pos (qChart_mem j 0) one_pos
  set x := Away.isLocalizationElem (qChart_mem (K := K) (r := r) (N := N) j k)
    (qChart_mem j 0)
  have hu : qChart K r N j 0 ^ 1 ∈ 𝒜 1 := by rw [pow_one]; exact qChart_mem _ _
  have hx : x ≠ 0 := by
    intro h0
    have h1 : (linFrac (tChart_mem (node K k)) hu : Away 𝒜 (tChart K r N j (node K k))) = 0 := h0
    have h2 := congrArg (chartPsi K r N hj (node K k)) h1
    rw [chartPsi_linFrac, map_zero, pow_one, qChart, chartQuotEval_mk, node_zero,
      chartForm_zero_eq, momentShift_zv_zero] at h2
    have h3 := congrArg MvPolynomial.constantCoeff h2
    rw [constantCoeff_incChartEval_chartForm, map_zero] at h3
    exact one_ne_zero h3
  have hne : Proj.awayι 𝒜 _ (qChart_mem j k) one_pos ⁻¹ᵁ hankelChart K r N j 0 ≠ ⊥ := by
    intro hbot
    rw [hankelChart, hpre] at hbot
    exact hx (isNilpotent_iff_eq_zero.mp ((PrimeSpectrum.basicOpen_eq_bot_iff x).mp hbot))
  obtain ⟨p, hp⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hne
  refine ⟨Proj.awayι 𝒜 _ (qChart_mem j k) one_pos p, ?_, hp⟩
  rw [SetLike.mem_coe, hankelChart, ← Proj.opensRange_awayι 𝒜 _ (qChart_mem j k) one_pos]
  exact ⟨p, rfl⟩

theorem chart_isIrreducible (hj : j + r ≤ N) (k : Fin (r + 1)) :
    IsIrreducible (hankelChart K r N j k : Set (HankelY K r N j)) := by
  haveI := isDomain_chart (K := K) hj k
  rw [hankelChart, ← Proj.opensRange_awayι 𝒜 _ (qChart_mem j k) one_pos,
    Scheme.Hom.coe_opensRange, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _
    (Proj.awayι 𝒜 _ (qChart_mem j k) one_pos).continuous.continuousOn

/-- **The incidence variety is irreducible.** -/
theorem hankelY_irreducibleSpace [CharZero K] (hj : j + r ≤ N) : IrreducibleSpace (HankelY K r N j) := by
  have hcl : closure (hankelChart K r N j 0 : Set (HankelY K r N j)) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    have hy : y ∈ (⨆ k, hankelChart K r N j k) := by
      rw [iSup_hankelChart_eq_top (K := K) (r := r) (N := N) j]
      trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact closure_mono Set.inter_subset_right
      (subset_closure_inter_of_isPreirreducible_of_isOpen (chart_isIrreducible hj k).2
        (hankelChart K r N j 0).isOpen (chart_inter_nonempty hj k) hk)
  rw [irreducibleSpace_def, Set.top_eq_univ, ← hcl]
  exact (chart_isIrreducible hj 0).closure

/-- **The incidence variety is reduced.** -/
theorem hankelY_isReduced [CharZero K] (hj : j + r ≤ N) : IsReduced (HankelY K r N j) := by
  haveI : ∀ k, IsReduced (hankelChart K r N j k).toScheme := fun k => by
    haveI := isDomain_chart (K := K) hj k
    exact isReduced_of_isOpenImmersion
      (Proj.basicOpenIsoSpec 𝒜 _ (qChart_mem j k) one_pos).hom
  let 𝒰 := (HankelY K r N j).openCoverOfIsOpenCover (hankelChart K r N j)
    (iSup_hankelChart_eq_top (K := K) (r := r) (N := N) j)
  haveI : ∀ k, IsReduced (𝒰.X k) := fun k => (inferInstance : IsReduced (hankelChart K r N j k).toScheme)
  exact IsReduced.of_openCover _ 𝒰

/-- **The incidence variety is integral.** -/
theorem hankelY_isIntegral [CharZero K] (hj : j + r ≤ N) : IsIntegral (HankelY K r N j) := by
  haveI := hankelY_isReduced (K := K) hj
  haveI := hankelY_irreducibleSpace (K := K) hj
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem birSource_dense [CharZero K] (hrj : r ≤ j) (hj : j + r ≤ N) :
    Dense (birSource K r N hj : Set (HankelY K r N j)) := by
  haveI := hankelY_isIntegral (K := K) (r := r) (N := N) hj
  have hne : birSource K r N hj ≠ ⊥ := by
    rw [Ne, basicOpen_eq_bot_iff, ← map_zero (chartBeta K r N hj),
      (chartBeta_injective _).eq_iff]
    exact trailSection_ne_zero hrj hj
  exact (birSource K r N _).isOpen.dense ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hne)

/-! ### Birationality -/

variable (K r N) in
/-- **The partial isomorphism** `{δ ≠ 0} ≅ D(δ)` given by `π`. -/
noncomputable def hankelPartialIso [CharZero K] (hrj : r ≤ j) (hj : j + r ≤ N) :
    (HankelY K r N j).PartialIso (Spec (CommRingCat.of (SecantRing K r N j))) where
  source := birSource K r N hj
  dense_source := birSource_dense hrj hj
  target := birTarget K r N j
  dense_target := birTarget_dense hrj hj
  iso := haveI := resLE_isIso (K := K) hrj hj
    asIso ((hankelResolution K r N hj).resLE (birTarget K r N j) (birSource K r N hj)
      (birSource_le _))

/-- **`π : Y → Spec A` is birational.** -/
theorem hankelResolution_birational [CharZero K] (hrj : r ≤ j) (hj : j + r ≤ N) :
    Scheme.BirationalOver (hankelResolution K r N hj) (𝟙 _) :=
  ⟨hankelPartialIso K r N hrj hj, by
    rw [Scheme.PartialIso.IsOver, Category.comp_id]
    exact Scheme.Hom.resLE_comp_ι _ _⟩

end Birational



end HTGeometry
