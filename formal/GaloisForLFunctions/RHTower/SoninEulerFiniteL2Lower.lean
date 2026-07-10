import GaloisForLFunctions.RHTower.SoninEulerQuadraticCorner
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Finite Sonin Euler Calkin `l2` lower bounds

A single narrow exterior shell is asymptotically fixed by the actual even Sonin projection.
Distinct dilations move it into pairwise orthogonal interior shells.  This yields a quantitative
`l2` lower bound, rather than mere linear independence, for finite combinations modulo compact
operators.
-/

noncomputable section

open MeasureTheory Set
open Filter Topology
open scoped InnerProduct InnerProductSpace BigOperators

namespace RHTower

theorem exists_between_forall_fintype
    {ι : Type*} [Fintype ι] [Nonempty ι] (a : ℝ) (u : ι → ℝ)
    (hu : ∀ i, a < u i) :
    ∃ b : ℝ, a < b ∧ ∀ i, b < u i := by
  classical
  let U : Finset ℝ := Finset.univ.image u
  have hUne : U.Nonempty := Finset.univ_nonempty.image u
  let m : ℝ := U.min' hUne
  have ham : a < m := by
    rw [Finset.lt_min'_iff]
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact hu i
  let b : ℝ := (a + m) / 2
  refine ⟨b, by dsimp [b]; linarith, ?_⟩
  intro i
  have hmi : m ≤ u i := Finset.min'_le U (u i)
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  dsimp [b]
  linarith

def finiteScaleShellConstraint {n : ℕ} (r : Fin n → ℝ) : Type :=
  Sum (Fin n) {ij : Fin n × Fin n // r ij.1 < r ij.2}

noncomputable instance {n : ℕ} (r : Fin n → ℝ) :
    Fintype (finiteScaleShellConstraint r) :=
  by
    classical
    unfold finiteScaleShellConstraint
    infer_instance

instance {n : ℕ} [Nonempty (Fin n)] (r : Fin n → ℝ) :
    Nonempty (finiteScaleShellConstraint r) :=
  ⟨Sum.inl (Classical.choice inferInstance)⟩

def finiteScaleShellUpper {n : ℕ} (a : ℝ) (r : Fin n → ℝ) :
    finiteScaleShellConstraint r → ℝ
  | Sum.inl i => r i * a
  | Sum.inr ij => a * r ij.1.2 / r ij.1.1

/-- A finite positive scale family admits one exterior shell whose inward dilates are all inside
the physical cutoff and pairwise disjoint. -/
theorem exists_finiteScale_separatingShellUpper
    {n : ℕ} [Nonempty (Fin n)] (a : ℝ) (ha : 0 < a)
    (r : Fin n → ℝ) (hr : ∀ i, 1 < r i) :
    ∃ b : ℝ, a < b ∧
      (∀ i, b < r i * a) ∧
      (∀ i j, r i < r j → b * r i < a * r j) := by
  have hu : ∀ z : finiteScaleShellConstraint r, a < finiteScaleShellUpper a r z := by
    intro z
    rcases z with i | ij
    · dsimp [finiteScaleShellUpper]
      nlinarith [hr i]
    · rcases ij with ⟨⟨i, j⟩, hij⟩
      dsimp [finiteScaleShellUpper]
      have hri : 0 < r i := zero_lt_one.trans (hr i)
      rw [lt_div_iff₀ hri]
      nlinarith
  obtain ⟨b, hab, hb⟩ := exists_between_forall_fintype a
    (finiteScaleShellUpper a r) hu
  refine ⟨b, hab, ?_, ?_⟩
  · intro i
    exact hb (Sum.inl i)
  · intro i j hij
    have hri : 0 < r i := zero_lt_one.trans (hr i)
    have h := hb (Sum.inr ⟨(i, j), hij⟩)
    dsimp [finiteScaleShellUpper] at h
    rwa [lt_div_iff₀ hri] at h

/-- The normalized inward image of the common exterior shell. -/
def inwardDilatedEvenShell
    (a b r : ℝ) (ha : 0 < a) (hab : a < b) (hr : 0 < r) (m : ℕ) : SoninL2 :=
  dilation r hr (evenShellVector a b ha hab m)

theorem norm_inwardDilatedEvenShell
    (a b r : ℝ) (ha : 0 < a) (hab : a < b) (hr : 0 < r) (m : ℕ) :
    ‖inwardDilatedEvenShell a b r ha hab hr m‖ = 1 := by
  rw [inwardDilatedEvenShell, (dilation r hr).norm_map,
    (evenShellVector_orthonormal a b ha hab).norm_eq_one m]

theorem inner_inwardDilatedEvenShell_eq_zero_of_lt
    {a b p q : ℝ} (ha : 0 < a) (hab : a < b)
    (hp : 0 < p) (hq : 0 < q) (hsep : b * p < a * q) (m : ℕ) :
    inner ℂ (inwardDilatedEvenShell a b p ha hab hp m)
      (inwardDilatedEvenShell a b q ha hab hq m) = 0 := by
  let A : SoninL2 →L[ℂ] SoninL2 :=
    indicatorCutoff (scaledEvenShellBand p a b) (measurableSet_scaledEvenShellBand p a b)
  have hself : A (inwardDilatedEvenShell a b p ha hab hp m) =
      inwardDilatedEvenShell a b p ha hab hp m := by
    dsimp [A, inwardDilatedEvenShell, evenShellVector]
    apply indicatorCutoff_dilation_normalizedIndicator_eq_self
    exact evenShellCell_preimage_subset_scaledEvenShellBand ha hab m
  have hbands : Disjoint (scaledEvenShellBand p a b) (scaledEvenShellBand q a b) :=
    scaledEvenShellBand_disjoint hp hq ha hsep
  have hzero : A (inwardDilatedEvenShell a b q ha hab hq m) = 0 := by
    dsimp [A, inwardDilatedEvenShell, evenShellVector]
    apply indicatorCutoff_dilation_normalizedIndicator_eq_zero
    exact hbands.mono_right
      (evenShellCell_preimage_subset_scaledEvenShellBand ha hab m)
  have hsym := indicatorCutoff_symmetric
    (scaledEvenShellBand p a b) (measurableSet_scaledEvenShellBand p a b)
    (inwardDilatedEvenShell a b p ha hab hp m)
    (inwardDilatedEvenShell a b q ha hab hq m)
  change inner ℂ (A (inwardDilatedEvenShell a b p ha hab hp m))
      (inwardDilatedEvenShell a b q ha hab hq m) =
    inner ℂ (inwardDilatedEvenShell a b p ha hab hp m)
      (A (inwardDilatedEvenShell a b q ha hab hq m)) at hsym
  rw [hself, hzero, inner_zero_right] at hsym
  exact hsym

/-- For a separating common shell, the inward images at distinct scales form an orthonormal
finite family. -/
theorem inwardDilatedEvenShell_orthonormal_scales
    {n : ℕ} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (r : Fin n → ℝ) (hr : ∀ i, 1 < r i) (hinj : Function.Injective r)
    (hsep : ∀ i j, r i < r j → b * r i < a * r j) (m : ℕ) :
    Orthonormal ℂ (fun i =>
      inwardDilatedEvenShell a b (r i) ha hab (zero_lt_one.trans (hr i)) m) := by
  constructor
  · intro i
    exact norm_inwardDilatedEvenShell a b (r i) ha hab
      (zero_lt_one.trans (hr i)) m
  · intro i j hij
    have hrne : r i ≠ r j := fun h => hij (hinj h)
    rcases lt_or_gt_of_ne hrne with hlt | hgt
    · exact inner_inwardDilatedEvenShell_eq_zero_of_lt ha hab
        (zero_lt_one.trans (hr i)) (zero_lt_one.trans (hr j)) (hsep i j hlt) m
    · rw [← inner_conj_symm]
      rw [inner_inwardDilatedEvenShell_eq_zero_of_lt ha hab
        (zero_lt_one.trans (hr j)) (zero_lt_one.trans (hr i)) (hsep j i hgt) m]
      simp

theorem centralPhysicalCutoff_inwardDilatedEvenShell_eq_self
    (a b r : ℝ) (ha : 0 < a) (hab : a < b) (hr : 0 < r)
    (hbr : b < r * a) (m : ℕ) :
    indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
      (inwardDilatedEvenShell a b r ha hab hr m) =
        inwardDilatedEvenShell a b r ha hab hr m := by
  dsimp [inwardDilatedEvenShell, evenShellVector]
  apply indicatorCutoff_dilation_normalizedIndicator_eq_self
  exact (evenShellCell_preimage_subset_scaledEvenShellBand ha hab m).trans
    (by simpa [centralInterval] using
      scaledEvenShellBand_subset_Icc hr ha hbr.le)

theorem inwardDilatedEvenShell_mem_centralPhysicalForbidden
    (a b r : ℝ) (ha : 0 < a) (hab : a < b) (hr : 0 < r)
    (hbr : b < r * a) (m : ℕ) :
    inwardDilatedEvenShell a b r ha hab hr m ∈ centralPhysicalForbidden a := by
  rw [centralPhysicalForbidden]
  apply (physicalForbidden (Set.Icc (-a) a) measurableSet_Icc).starProjection_eq_self_iff.mp
  rw [← indicatorCutoff_eq_physicalForbidden_starProjection]
  simpa [centralInterval] using
    centralPhysicalCutoff_inwardDilatedEvenShell_eq_self a b r ha hab hr hbr m

/-- The actual Sonin lower corner sends the corrected common exterior shell to its normalized
inward image at the chosen scale. -/
theorem centralSoninDilationCorner_commonExteriorShell_tendsto
    (a b r : ℝ) (ha : 0 < a) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) :
    Tendsto (fun m =>
      ‖(crossBoundary (centralSoninProjection a) (dilationSum r hr) :
          SoninL2 →L[ℂ] SoninL2)
          (centralSoninProjection a (evenShellVector a b ha hab m)) -
        inwardDilatedEvenShell a b r ha hab (zero_lt_one.trans hr) m‖)
      atTop (𝓝 0) := by
  let Q : SoninL2 →L[ℂ] SoninL2 := centralSoninProjection a
  let D : SoninL2 →L[ℂ] SoninL2 := dilationSum r hr
  let B : SoninL2 →L[ℂ] SoninL2 := 1 - Q
  let g : ℕ → SoninL2 := evenShellVector a b ha hab
  let e : ℕ → SoninL2 := fun m => Q (g m)
  let v : ℕ → SoninL2 := inwardDilatedEvenShell a b r ha hab (zero_lt_one.trans hr)
  let w : ℕ → SoninL2 := fun m =>
    dilation r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) (g m)
  have hgeNorm : Tendsto (fun m => ‖e m - g m‖) atTop (𝓝 0) := by
    simpa [e, g, Q] using centralSoninProjection_evenShellVector_tendsto_general a b ha hab
  have hge : Tendsto (fun m => e m - g m) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hgeNorm
  have har : a < r * a := by nlinarith
  have hQwNorm : Tendsto (fun m => ‖Q (w m) - w m‖) atTop (𝓝 0) := by
    simpa [Q, w, g] using
      centralSoninProjection_inverseDilatedShell_tendsto a a b r ha ha hab hr har
  have hw : Tendsto (fun m => w m - Q (w m)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    convert hQwNorm using 1
    funext m
    rw [← norm_neg]
    congr 2
    module
  have hfirst : Tendsto (fun m => B (D (e m - g m))) atTop (𝓝 0) := by
    simpa only [map_zero] using (B ∘L D).continuous.continuousAt.tendsto.comp hge
  have hsum : Tendsto (fun m => B (D (e m - g m)) + (w m - Q (w m)))
      atTop (𝓝 0) := by
    simpa only [add_zero] using hfirst.add hw
  have hQe : ∀ m, Q (e m) = e m := by
    intro m
    dsimp [e, Q]
    rw [centralSoninProjection_eq_soninIntersectionProjection]
    apply ((centralPhysicalForbidden a)ᗮ ⊓
      (centralFourierForbidden a)ᗮ).starProjection_eq_self_iff.mpr
    exact ((centralPhysicalForbidden a)ᗮ ⊓
      (centralFourierForbidden a)ᗮ).starProjection_apply_mem _
  have hQv : ∀ m, Q (v m) = 0 := by
    intro m
    exact centralSoninProjection_eq_zero_of_mem_physicalForbidden a
      (inwardDilatedEvenShell_mem_centralPhysicalForbidden
        a b r ha hab (zero_lt_one.trans hr) hbr m)
  have hDg : ∀ m, D (g m) = v m + w m := by
    intro m
    simp [D, g, v, w, inwardDilatedEvenShell]
  have hvec : Tendsto (fun m =>
      (crossBoundary Q D : SoninL2 →L[ℂ] SoninL2) (e m) - v m)
      atTop (𝓝 0) := by
    convert hsum using 1
    funext m
    simp only [crossBoundary, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.sub_apply]
    rw [hQe m]
    have hDe : D (e m) = D (e m - g m) + D (g m) := by
      rw [map_sub, sub_add_cancel]
    rw [hDe, hDg m, map_add, map_add, hQv m]
    dsimp [B]
    module
  exact tendsto_zero_iff_norm_tendsto_zero.mp hvec

/-- The inward shell image, regarded in the even Hilbert carrier. -/
def inwardDilatedEvenShellEven
    (a b r : ℝ) (ha : 0 < a) (hab : a < b) (hr : 0 < r) (m : ℕ) : evenSubspace :=
  (evenDilationUnitary r hr) (evenShellVectorEven a b ha hab m)

@[simp] theorem coe_inwardDilatedEvenShellEven
    (a b r : ℝ) (ha : 0 < a) (hab : a < b) (hr : 0 < r) (m : ℕ) :
    ((inwardDilatedEvenShellEven a b r ha hab hr m : evenSubspace) : SoninL2) =
      inwardDilatedEvenShell a b r ha hab hr m := rfl

theorem inwardDilatedEvenShellEven_orthonormal_scales
    {n : ℕ} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (r : Fin n → ℝ) (hr : ∀ i, 1 < r i) (hinj : Function.Injective r)
    (hsep : ∀ i j, r i < r j → b * r i < a * r j) (m : ℕ) :
    Orthonormal ℂ (fun i =>
      inwardDilatedEvenShellEven a b (r i) ha hab (zero_lt_one.trans (hr i)) m) := by
  exact (inwardDilatedEvenShell_orthonormal_scales a b ha hab r hr hinj hsep m).codRestrict
    evenSubspace (fun i => (inwardDilatedEvenShellEven a b (r i) ha hab
      (zero_lt_one.trans (hr i)) m).2)

/-- The Euclidean norm of a finite complex coefficient family. -/
def finiteCoefficientL2Norm {n : ℕ} (c : Fin n → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖c i‖ ^ 2)

theorem finiteCoefficientL2Norm_nonneg {n : ℕ} (c : Fin n → ℂ) :
    0 ≤ finiteCoefficientL2Norm c :=
  Real.sqrt_nonneg _

theorem norm_sum_smul_orthonormal_eq_finiteCoefficientL2Norm
    {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : Fin n → H) (hv : Orthonormal ℂ v) (c : Fin n → ℂ) :
    ‖∑ i, c i • v i‖ = finiteCoefficientL2Norm c := by
  have hsquare : ‖∑ i, c i • v i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
    simpa [LinearIsometry.toSpanSingleton_apply] using
      hv.orthogonalFamily.norm_sum c Finset.univ
  have hsum : 0 ≤ ∑ i, ‖c i‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsqrt := Real.sq_sqrt hsum
  have hnorm : 0 ≤ ‖∑ i, c i • v i‖ := norm_nonneg _
  have hsqrtnonneg : 0 ≤ Real.sqrt (∑ i, ‖c i‖ ^ 2) := Real.sqrt_nonneg _
  dsimp [finiteCoefficientL2Norm]
  nlinarith

theorem evenCentralSoninDilationCorner_commonExteriorShell_tendsto
    (a b r : ℝ) (ha : 0 < a) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) :
    Tendsto (fun m =>
      ‖evenCentralSoninDilationCorner a r hr
          (evenCentralSoninProjection a (evenShellVectorEven a b ha hab m)) -
        inwardDilatedEvenShellEven a b r ha hab (zero_lt_one.trans hr) m‖)
      atTop (𝓝 0) := by
  change Tendsto (fun m =>
    ‖(crossBoundary (centralSoninProjection a) (dilationSum r hr) :
        SoninL2 →L[ℂ] SoninL2)
        (centralSoninProjection a (evenShellVector a b ha hab m)) -
      inwardDilatedEvenShell a b r ha hab (zero_lt_one.trans hr) m‖)
    atTop (𝓝 0)
  exact centralSoninDilationCorner_commonExteriorShell_tendsto a b r ha hab hr hbr

/-- A finite combination of even Sonin corners sends the one corrected common shell to the
corresponding orthogonal combination of inward shell images. -/
theorem finiteEvenDilationCorners_commonExteriorShell_tendsto
    {n : ℕ} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (r : Fin n → ℝ) (hr : ∀ i, 1 < r i) (c : Fin n → ℂ)
    (hbr : ∀ i, b < r i * a) :
    Tendsto (fun m =>
      ‖finiteEvenDilationCorners a r hr c
          (evenCentralSoninProjection a (evenShellVectorEven a b ha hab m)) -
        ∑ i, c i • inwardDilatedEvenShellEven a b (r i) ha hab
          (zero_lt_one.trans (hr i)) m‖) atTop (𝓝 0) := by
  let f : ℕ → evenSubspace := fun m =>
    evenCentralSoninProjection a (evenShellVectorEven a b ha hab m)
  let v : Fin n → ℕ → evenSubspace := fun i m =>
    inwardDilatedEvenShellEven a b (r i) ha hab (zero_lt_one.trans (hr i)) m
  have hi : ∀ i, Tendsto (fun m =>
      evenCentralSoninDilationCorner a (r i) (hr i) (f m) - v i m)
      atTop (𝓝 0) := by
    intro i
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa [f, v] using
      evenCentralSoninDilationCorner_commonExteriorShell_tendsto
        a b (r i) ha hab (hr i) (hbr i)
  have hsum : Tendsto (fun m =>
      ∑ i, c i • (evenCentralSoninDilationCorner a (r i) (hr i) (f m) - v i m))
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => (hi i).const_smul (c i))
  have hvec : Tendsto (fun m =>
      finiteEvenDilationCorners a r hr c (f m) - ∑ i, c i • v i m)
      atTop (𝓝 0) := by
    convert hsum using 1
    funext m
    dsimp [finiteEvenDilationCorners]
    rw [ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.smul_apply]
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib]
  simpa [f, v] using tendsto_zero_iff_norm_tendsto_zero.mp hvec

/-- The common separating shell gives the finite coefficient `l2` lower bound against every
compact perturbation. -/
theorem finiteCoefficientL2Norm_le_norm_finiteEvenDilationCorners_sub_compact_of_shell
    {n : ℕ} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (r : Fin n → ℝ) (hr : ∀ i, 1 < r i) (hinj : Function.Injective r)
    (c : Fin n → ℂ) (hbr : ∀ i, b < r i * a)
    (hsep : ∀ i j, r i < r j → b * r i < a * r j)
    (K : evenSubspace →L[ℂ] evenSubspace) (hK : IsCompactOperator K) :
    finiteCoefficientL2Norm c ≤ ‖finiteEvenDilationCorners a r hr c - K‖ := by
  let g : ℕ → evenSubspace := evenShellVectorEven a b ha hab
  let f : ℕ → evenSubspace := fun m => evenCentralSoninProjection a (g m)
  let v : ℕ → evenSubspace := fun m =>
    ∑ i, c i • inwardDilatedEvenShellEven a b (r i) ha hab
      (zero_lt_one.trans (hr i)) m
  let T : evenSubspace →L[ℂ] evenSubspace := finiteEvenDilationCorners a r hr c
  have hg : Orthonormal ℂ g := by
    simpa [g] using evenShellVectorEven_orthonormal a b ha hab
  have hf_approx : Tendsto (fun m => ‖f m - g m‖) atTop (𝓝 0) := by
    change Tendsto (fun m =>
      ‖centralSoninProjection a (evenShellVector a b ha hab m) -
        evenShellVector a b ha hab m‖) atTop (𝓝 0)
    exact centralSoninProjection_evenShellVector_tendsto_general a b ha hab
  have hf_weak : ∀ ℓ : evenSubspace →L[ℂ] ℂ,
      Tendsto (fun m => ℓ (f m)) atTop (𝓝 0) :=
    weakly_tendsto_zero_of_norm_sub_tendsto_zero
      (Orthonormal.weakly_tendsto_zero hg) hf_approx
  have hf_bound : ∀ m, ‖f m‖ ≤ 1 := by
    intro m
    calc
      ‖f m‖ ≤ ‖g m‖ := by
        change ‖evenCentralSoninProjection a (g m)‖ ≤ ‖g m‖
        rw [evenCentralSoninProjection_eq_starProjection]
        exact (evenCentralSoninCarrier a).norm_starProjection_apply_le (g m)
      _ = 1 := hg.norm_eq_one m
  have hT_approx : Tendsto (fun m => ‖T (f m) - v m‖) atTop (𝓝 0) := by
    simpa [T, f, g, v] using
      finiteEvenDilationCorners_commonExteriorShell_tendsto
        a b ha hab r hr c hbr
  have hv_norm : ∀ m, ‖v m‖ = finiteCoefficientL2Norm c := by
    intro m
    apply norm_sum_smul_orthonormal_eq_finiteCoefficientL2Norm
    exact inwardDilatedEvenShellEven_orthonormal_scales
      a b ha hab r hr hinj hsep m
  have hKnorm : Tendsto (fun m => ‖K (f m)‖) atTop (𝓝 0) :=
    IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weakly_null
      K hK f 1 hf_bound hf_weak
  have hTvec : Tendsto (fun m => T (f m) - v m) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hT_approx
  have hKvec : Tendsto (fun m => K (f m)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hKnorm
  have hdiff : Tendsto (fun m => (T - K) (f m) - v m) atTop (𝓝 0) := by
    have hsub : Tendsto (fun m => (T (f m) - v m) - K (f m))
        atTop (𝓝 0) := by
      simpa only [sub_zero] using hTvec.sub hKvec
    convert hsub using 1
    funext m
    simp
    module
  have hnorm : Tendsto (fun m => ‖(T - K) (f m)‖)
      atTop (𝓝 (finiteCoefficientL2Norm c)) :=
    tendsto_norm_of_norm_sub_tendsto_zero_of_norm_eq
      (tendsto_zero_iff_norm_tendsto_zero.mp hdiff) hv_norm
  have hle : ∀ m, ‖(T - K) (f m)‖ ≤ ‖T - K‖ := by
    intro m
    calc
      ‖(T - K) (f m)‖ ≤ ‖T - K‖ * ‖f m‖ := (T - K).le_opNorm (f m)
      _ ≤ ‖T - K‖ * 1 :=
        mul_le_mul_of_nonneg_left (hf_bound m) (T - K).opNorm_nonneg
      _ = ‖T - K‖ := mul_one _
  exact le_of_tendsto hnorm (Eventually.of_forall hle)

/-- **Finite `l2` Calkin lower bound.** Distinct even Sonin dilation corners contain the
Euclidean coefficient norm modulo compact operators. -/
theorem finiteCoefficientL2Norm_le_norm_finiteEvenDilationCorners_sub_compact
    {n : ℕ} [Nonempty (Fin n)] (a : ℝ) (ha : 0 < a)
    (r : Fin n → ℝ) (hr : ∀ i, 1 < r i) (hinj : Function.Injective r)
    (c : Fin n → ℂ) (K : evenSubspace →L[ℂ] evenSubspace)
    (hK : IsCompactOperator K) :
    finiteCoefficientL2Norm c ≤ ‖finiteEvenDilationCorners a r hr c - K‖ := by
  obtain ⟨b, hab, hbr, hsep⟩ :=
    exists_finiteScale_separatingShellUpper a ha r hr
  exact finiteCoefficientL2Norm_le_norm_finiteEvenDilationCorners_sub_compact_of_shell
    a b ha hab r hr hinj c hbr hsep K hK

/-- The finite coefficient lower bound, including the empty family. -/
theorem finiteCoefficientL2Norm_le_norm_finiteEvenDilationCorners_sub_compact_all
    {n : ℕ} (a : ℝ) (ha : 0 < a)
    (r : Fin n → ℝ) (hr : ∀ i, 1 < r i) (hinj : Function.Injective r)
    (c : Fin n → ℂ) (K : evenSubspace →L[ℂ] evenSubspace)
    (hK : IsCompactOperator K) :
    finiteCoefficientL2Norm c ≤ ‖finiteEvenDilationCorners a r hr c - K‖ := by
  by_cases hn : n = 0
  · subst n
    have hc0 : finiteCoefficientL2Norm c = 0 := by simp [finiteCoefficientL2Norm]
    rw [hc0]
    exact (finiteEvenDilationCorners a r hr c - K).opNorm_nonneg
  · letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    exact finiteCoefficientL2Norm_le_norm_finiteEvenDilationCorners_sub_compact
      a ha r hr hinj c K hK

/-- The Euclidean coefficient norm after the positive Euler normalization. -/
def finiteEulerCoefficientL2Norm {n : ℕ} (r : Fin n → ℝ) (c : Fin n → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖c i‖ ^ 2 / r i)

theorem finiteCoefficientL2Norm_eulerScaled
    {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 1 < r i) (c : Fin n → ℂ) :
    finiteCoefficientL2Norm
      (fun i => c i * (-((Real.sqrt (r i) : ℂ)⁻¹))) =
        finiteEulerCoefficientL2Norm r c := by
  unfold finiteCoefficientL2Norm finiteEulerCoefficientL2Norm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.2 (zero_lt_one.trans (hr i)))]
  have hs : Real.sqrt (r i) ^ 2 = r i :=
    Real.sq_sqrt (zero_lt_one.trans (hr i)).le
  field_simp [Real.sqrt_ne_zero'.mpr (zero_lt_one.trans (hr i)),
    ne_of_gt (zero_lt_one.trans (hr i))]
  nlinarith

/-- **Finite positive Euler `l2` Calkin lower bound.** The weighted Euclidean coefficient norm
survives every compact perturbation of the finite positive Euler corner combination. -/
theorem finiteEulerCoefficientL2Norm_le_norm_finiteEvenPositiveEulerCorners_sub_compact
    {n : ℕ} (a : ℝ) (ha : 0 < a)
    (r : Fin n → ℝ) (hr : ∀ i, 1 < r i) (hinj : Function.Injective r)
    (c : Fin n → ℂ) (K : evenSubspace →L[ℂ] evenSubspace)
    (hK : IsCompactOperator K) :
    finiteEulerCoefficientL2Norm r c ≤
      ‖finiteEvenPositiveEulerCorners a r hr c - K‖ := by
  rw [finiteEvenPositiveEulerCorners_eq_dilationCorners,
    ← finiteCoefficientL2Norm_eulerScaled r hr c]
  exact finiteCoefficientL2Norm_le_norm_finiteEvenDilationCorners_sub_compact_all
    a ha r hr hinj (fun i => c i * (-((Real.sqrt (r i) : ℂ)⁻¹))) K hK

theorem norm_unitaryPush_le
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (u : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    ‖unitaryPush u T‖ ≤ ‖T‖ := by
  apply (unitaryPush u T).opNorm_le_bound T.opNorm_nonneg
  intro x
  calc
    ‖unitaryPush u T x‖ = ‖T (u.symm x)‖ := u.norm_map _
    _ ≤ ‖T‖ * ‖u.symm x‖ := T.le_opNorm (u.symm x)
    _ = ‖T‖ * ‖x‖ := by rw [u.symm.norm_map]

theorem unitaryPush_symm_unitaryPush
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (u : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    unitaryPush u.symm (unitaryPush u T) = T := by
  ext x
  simp [unitaryPush]

theorem norm_unitaryPush
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (u : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    ‖unitaryPush u T‖ = ‖T‖ := by
  apply le_antisymm (norm_unitaryPush_le u T)
  have h := norm_unitaryPush_le u.symm (unitaryPush u T)
  rwa [unitaryPush_symm_unitaryPush] at h

theorem IsCompactOperator.unitaryPush
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (u : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) (hT : IsCompactOperator T) :
    IsCompactOperator (unitaryPush u T) := by
  have h := (hT.comp_clm (u.symm : K →L[ℂ] H)).clm_comp (u : H →L[ℂ] K)
  simpa [unitaryPush, Function.comp_def] using h

/-- **Concrete source `l2` lower bound.** The weighted Euclidean coefficient norm survives every
compact perturbation of the literal finite positive Euler corner combination on the archimedean
Hardy--Titchmarsh line. -/
theorem finiteEulerCoefficientL2Norm_le_norm_finiteArchimedeanPrimeEulerCorners_sub_compact
    {n : ℕ} (a : ℝ) (ha : 0 < a)
    (r : Fin n → ℝ) (hr : ∀ i, 1 < r i) (hinj : Function.Injective r)
    (c : Fin n → ℂ)
    (K : ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2)
    (hK : IsCompactOperator K) :
    finiteEulerCoefficientL2Norm r c ≤
      ‖finiteArchimedeanPrimeEulerCorners a r hr c - K‖ := by
  let u := archimedeanDualHardyTitchmarshUnitary
  let Kpull : evenSubspace →L[ℂ] evenSubspace := unitaryPush u.symm K
  have hKpull : IsCompactOperator Kpull := by
    exact IsCompactOperator.unitaryPush u.symm K hK
  have hlower :=
    finiteEulerCoefficientL2Norm_le_norm_finiteEvenPositiveEulerCorners_sub_compact
      a ha r hr hinj c Kpull hKpull
  have hpushK : unitaryPush u Kpull = K := by
    dsimp [Kpull, u]
    exact unitaryPush_symm_unitaryPush
      archimedeanDualHardyTitchmarshUnitary.symm K
  have heq : finiteArchimedeanPrimeEulerCorners a r hr c - K =
      unitaryPush u (finiteEvenPositiveEulerCorners a r hr c - Kpull) := by
    rw [finiteArchimedeanPrimeEulerCorners_eq_unitaryPush]
    rw [unitaryPush_sub, hpushK]
  rw [heq, norm_unitaryPush]
  exact hlower

/-- Square root of the reciprocal-scale energy of a finite family. -/
def finiteReciprocalScaleL2Norm {n : ℕ} (r : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, (r i)⁻¹)

theorem finiteEulerCoefficientL2Norm_one
    {n : ℕ} (r : Fin n → ℝ) :
    finiteEulerCoefficientL2Norm r (fun _ => 1) = finiteReciprocalScaleL2Norm r := by
  unfold finiteEulerCoefficientL2Norm finiteReciprocalScaleL2Norm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [div_eq_mul_inv]

/-- Unit coefficients force the reciprocal-scale energy into the concrete source Calkin norm. -/
theorem finiteReciprocalScaleL2Norm_le_norm_finiteArchimedeanPrimeEulerCorners_sub_compact
    {n : ℕ} (a : ℝ) (ha : 0 < a)
    (r : Fin n → ℝ) (hr : ∀ i, 1 < r i) (hinj : Function.Injective r)
    (K : ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2)
    (hK : IsCompactOperator K) :
    finiteReciprocalScaleL2Norm r ≤
      ‖finiteArchimedeanPrimeEulerCorners a r hr (fun _ => 1) - K‖ := by
  rw [← finiteEulerCoefficientL2Norm_one]
  exact finiteEulerCoefficientL2Norm_le_norm_finiteArchimedeanPrimeEulerCorners_sub_compact
    a ha r hr hinj (fun _ => 1) K hK

/-- **Finite-prime source obstruction.** For any injective finite prime family, the square root of
its reciprocal-prime sum is a lower bound against every compact perturbation of the canonical
positive Euler corner sum. -/
theorem finitePrimeReciprocalL2Norm_le_norm_archimedeanEulerCorners_sub_compact
    {n : ℕ} (a : ℝ) (ha : 0 < a) (p : Fin n → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (K : ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2)
    (hK : IsCompactOperator K) :
    finiteReciprocalScaleL2Norm (fun i => (p i : ℝ)) ≤
      ‖finiteArchimedeanPrimeEulerCorners a (fun i => (p i : ℝ))
        (fun i => by
          change (1 : ℝ) < (p i : ℝ)
          exact_mod_cast (hp i).one_lt) (fun _ => 1) - K‖ := by
  have hinjR : Function.Injective (fun i => (p i : ℝ)) := by
    intro i j hij
    apply hinj
    change (p i : ℝ) = (p j : ℝ) at hij
    exact_mod_cast hij
  exact finiteReciprocalScaleL2Norm_le_norm_finiteArchimedeanPrimeEulerCorners_sub_compact
    a ha (fun i => (p i : ℝ)) (fun i => by
      change (1 : ℝ) < (p i : ℝ)
      exact_mod_cast (hp i).one_lt) hinjR K hK

theorem exists_finset_primes_sum_one_div_gt (B : ℝ) :
    ∃ s : Finset Nat.Primes, B < ∑ p ∈ s, (1 / (p : ℝ)) := by
  by_contra h
  apply Nat.Primes.not_summable_one_div
  apply summable_of_sum_le (c := B) (fun p => by positivity)
  intro s
  exact le_of_not_gt fun hs => h ⟨s, hs⟩

/-- Reciprocal-prime energy is arbitrarily large on injective finite prime families. -/
theorem exists_finitePrimeFamily_reciprocalL2Norm_gt (M : ℝ) (hM : 0 ≤ M) :
    ∃ (n : ℕ) (p : Fin n → ℕ),
      (∀ i, (p i).Prime) ∧ Function.Injective p ∧
        M < finiteReciprocalScaleL2Norm (fun i => (p i : ℝ)) := by
  obtain ⟨s, hs⟩ := exists_finset_primes_sum_one_div_gt (M ^ 2)
  let e : Fin s.card ≃ s := s.equivFin.symm
  let p : Fin s.card → ℕ := fun i => (e i : Nat.Primes)
  have hp : ∀ i, (p i).Prime := fun i => (e i).1.prop
  have hinj : Function.Injective p := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    apply Subtype.ext
    exact hij
  have hsum : (∑ i, ((p i : ℝ))⁻¹) = ∑ q ∈ s, (1 / (q : ℝ)) := by
    calc
      (∑ i, ((p i : ℝ))⁻¹) = ∑ i, (1 / ((e i : Nat.Primes) : ℝ)) := by
        simp [p, one_div]
      _ = ∑ q : s, (1 / ((q : Nat.Primes) : ℝ)) := by
        simpa using Equiv.sum_comp e
          (fun q : s => (1 / ((q.1 : Nat.Primes) : ℝ)))
      _ = ∑ q ∈ s, (1 / (q : ℝ)) := by
        simpa using Finset.sum_coe_sort s (fun q : Nat.Primes => (1 / (q : ℝ)))
  refine ⟨s.card, p, hp, hinj, ?_⟩
  rw [finiteReciprocalScaleL2Norm, hsum]
  exact (Real.lt_sqrt hM).2 hs

/-- **All-prime source unboundedness.** Canonical finite positive Euler corner sums have
arbitrarily large norm modulo compacts; in particular they cannot form a bounded all-prime
boundary seam without renormalization or cancellation. -/
theorem exists_finitePrime_archimedeanEulerCorner_norm_gt
    (a M : ℝ) (ha : 0 < a) (hM : 0 ≤ M) :
    ∃ (n : ℕ) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
      (_hinj : Function.Injective p),
      M < ‖finiteArchimedeanPrimeEulerCorners a (fun i => (p i : ℝ))
        (fun i => by
          change (1 : ℝ) < (p i : ℝ)
          exact_mod_cast (hp i).one_lt) (fun _ => 1) - 0‖ := by
  obtain ⟨n, p, hp, hinj, henergy⟩ := exists_finitePrimeFamily_reciprocalL2Norm_gt M hM
  have hlower := finitePrimeReciprocalL2Norm_le_norm_archimedeanEulerCorners_sub_compact
    a ha p hp hinj (0 : ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2)
      isCompactOperator_zero
  exact ⟨n, p, hp, hinj, henergy.trans_le hlower⟩

end RHTower
