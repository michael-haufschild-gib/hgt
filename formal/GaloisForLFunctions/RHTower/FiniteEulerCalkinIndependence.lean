import GaloisForLFunctions.RHTower.HardyTitchmarshEulerConcrete

/-!
# Finite Euler Calkin independence

Distinct dilation scales have linearly independent lower corners modulo compact operators across
the actual common physical/Fourier Sonin projection. The theorem is first proved on ambient
`L²(ℝ)`, then restricted to the actual even Sonin carrier, and finally transported to the literal
positive Euler metric corners on the concrete archimedean Hardy--Titchmarsh line.

The conclusion concerns finite *linear combinations of positive metric corners*. It does not rule
out the nonlinear/product quasi-inner compensation between archimedean and finite-place phase
ratios.
-/

noncomputable section

open MeasureTheory Set
open Filter Topology
open scoped InnerProduct InnerProductSpace

namespace RHTower

/-- The closed even shell pulled inward by the positive scale `r`. -/
def scaledEvenShellBand (r a b : ℝ) : Set ℝ :=
  (fun x : ℝ => r * x) ⁻¹' closedEvenShell a b

theorem measurableSet_scaledEvenShellBand (r a b : ℝ) :
    MeasurableSet (scaledEvenShellBand r a b) :=
  (measurableSet_closedEvenShell a b).preimage (measurable_const_mul r)

theorem scaledEvenShellBand_subset_Icc {r a b : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hba : b ≤ r * a) :
    scaledEvenShellBand r a b ⊆ Set.Icc (-a) a := by
  intro x hx
  have hxabs : |r * x| ≤ b := by
    rcases hx with hx | hx
    · have hxneg : r * x ≤ -a := hx.2
      have hxneg' : r * x < 0 := lt_of_le_of_lt hxneg (neg_lt_zero.mpr ha)
      rw [abs_of_neg hxneg']
      linarith [hx.1]
    · have hxpos : 0 < r * x := lt_of_lt_of_le ha hx.1
      rw [abs_of_pos hxpos]
      exact hx.2
  rw [abs_mul, abs_of_pos hr] at hxabs
  have : |x| ≤ a := by nlinarith
  exact abs_le.mp this

theorem scaledEvenShellBand_disjoint {p q a b : ℝ}
    (hp : 0 < p) (hq : 0 < q) (ha : 0 < a)
    (hsep : b * p < a * q) :
    Disjoint (scaledEvenShellBand p a b) (scaledEvenShellBand q a b) := by
  rw [Set.disjoint_left]
  intro x hxp hxq
  have hpLower : a ≤ p * |x| := by
    rcases hxp with hxp | hxp
    · have hneg : p * x < 0 := lt_of_le_of_lt hxp.2 (neg_lt_zero.mpr ha)
      have : a ≤ -(p * x) := by linarith [hxp.2]
      simpa [abs_mul, abs_of_pos hp, abs_of_neg (show x < 0 by nlinarith)] using this
    · have hx0 : 0 < x := by nlinarith [hxp.1]
      simpa [abs_of_pos hx0] using hxp.1
  have hqUpper : q * |x| ≤ b := by
    rcases hxq with hxq | hxq
    · have hx0 : x < 0 := by nlinarith [hxq.2]
      have : -(q * x) ≤ b := by linarith [hxq.1]
      simpa [abs_of_neg hx0] using this
    · have hx0 : 0 < x := by nlinarith [hxq.1]
      simpa [abs_of_pos hx0] using hxq.2
  nlinarith

theorem evenShellCell_preimage_subset_scaledEvenShellBand
    {r a b : ℝ} (hab : a < b) (n : ℕ) :
    (fun x : ℝ => r * x) ⁻¹' evenShellCell a b n ⊆
      scaledEvenShellBand r a b := by
  intro x hx
  exact evenShellCell_subset_closedEvenShell hab n hx

theorem physicalCutoff_evenShellVector_general
    (a b : ℝ) (hab : a < b) (n : ℕ) :
    indicatorCutoff (Set.Icc (-a) a) measurableSet_Icc
      (evenShellVector a b hab n) = 0 := by
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (Set.Icc (-a) a) measurableSet_Icc
      (evenShellVector a b hab n),
    normalizedIndicator_ae (evenShellCell a b n)
      (measurableSet_evenShellCell a b n)
      (evenShellCell_measure_ne_top hab n),
    Lp.coeFn_zero ℂ 2 volume] with x hcut hshell hzero
  rw [hcut]
  by_cases hxc : x ∈ Set.Icc (-a) a
  · have hxnot : x ∉ evenShellCell a b n := by
      intro hxs
      have hxabs : |x| ≤ a := abs_le.mpr hxc
      have hshell : a < |x| := (lt_shellLeft hab n).trans hxs.1
      exact (not_lt_of_ge hxabs) hshell
    rw [Set.indicator_of_mem hxc]
    change normalizedIndicator (evenShellCell a b n)
      (measurableSet_evenShellCell a b n)
      (evenShellCell_measure_ne_top hab n) x = (0 : SoninL2) x
    rw [hshell, Set.indicator_of_notMem hxnot, hzero]
    simp
  · rw [Set.indicator_of_notMem hxc]
    exact hzero.symm

theorem evenShellVector_mem_centralPhysicalForbidden_orthogonal_general
    (a b : ℝ) (hab : a < b) (n : ℕ) :
    evenShellVector a b hab n ∈ (centralPhysicalForbidden a)ᗮ := by
  change evenShellVector a b hab n ∈
    (physicalForbidden (Set.Icc (-a) a) measurableSet_Icc)ᗮ
  apply (Submodule.starProjection_apply_eq_zero_iff
    (K := physicalForbidden (Set.Icc (-a) a) measurableSet_Icc)).mp
  rw [← indicatorCutoff_eq_physicalForbidden_starProjection]
  exact physicalCutoff_evenShellVector_general a b hab n

theorem centralSoninProjection_evenShellVector_tendsto_general
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto (fun n =>
      ‖centralSoninProjection a (evenShellVector a b hab n) -
        evenShellVector a b hab n‖) atTop (𝓝 0) := by
  let A : Submodule ℂ SoninL2 := centralPhysicalForbidden a
  let B : Submodule ℂ SoninL2 := centralFourierForbidden a
  letI : (Aᗮ ⊓ Bᗮ).HasOrthogonalProjection := by
    dsimp [A, B]
    infer_instance
  have hblock : ‖soninAlternatingBlock A B‖ < 1 := by
    simpa [A, B] using norm_centralSoninAlternatingBlock_lt_one a ha
  have hgA : ∀ n, evenShellVector a b hab n ∈ Aᗮ := by
    intro n
    simpa [A] using
      evenShellVector_mem_centralPhysicalForbidden_orthogonal_general a b hab n
  have hBnull : Tendsto (fun n =>
      ‖B.starProjection (evenShellVector a b hab n)‖) atTop (𝓝 0) := by
    simpa [B, centralFourierForbidden] using
      fourierForbidden_starProjection_evenShellVector_tendsto_zero a b ha hab
  have h := soninIntersectionProjection_tendsto_shell A B hblock
    (evenShellVector a b hab) hgA hBnull
  rw [centralSoninProjection_eq_soninIntersectionProjection]
  simpa [A, B] using h

/-- Physical observer on one inward-scaled shell band. -/
def scaledEvenShellCutoff (r a b : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  indicatorCutoff (scaledEvenShellBand r a b)
    (measurableSet_scaledEvenShellBand r a b)

theorem scaledEvenShellCutoff_target_inward
    {r a b : ℝ} (hr : 0 < r) (hab : a < b) (n : ℕ) :
    scaledEvenShellCutoff r a b
        (dilation r hr (evenShellVector a b hab n)) =
      dilation r hr (evenShellVector a b hab n) := by
  apply indicatorCutoff_dilation_normalizedIndicator_eq_self
  exact evenShellCell_preimage_subset_scaledEvenShellBand hab n

theorem scaledEvenShellCutoff_offtarget_inward
    {p q a b : ℝ} (hp : 0 < p) (hq : 0 < q) (ha : 0 < a) (hab : a < b)
    (hsep : b * p < a * q) (n : ℕ) :
    scaledEvenShellCutoff p a b
        (dilation q hq (evenShellVector a b hab n)) = 0 := by
  apply indicatorCutoff_dilation_normalizedIndicator_eq_zero
  exact (scaledEvenShellBand_disjoint hp hq ha hsep).mono_right
    (evenShellCell_preimage_subset_scaledEvenShellBand hab n)

theorem outward_shell_preimage_disjoint_general
    (a b r : ℝ) (ha : 0 < a) (hab : a < b) (hr : 1 < r) (n : ℕ) :
    Disjoint (Set.Icc (-a) a)
      ((fun x : ℝ => r⁻¹ * x) ⁻¹' evenShellCell a b n) := by
  rw [Set.disjoint_left]
  intro x hxc hxs
  have hxabs : |x| ≤ a := abs_le.mpr hxc
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hinv0 : 0 < r⁻¹ := inv_pos.mpr hr0
  have hscaled_gt : a < |r⁻¹ * x| := (lt_shellLeft hab n).trans hxs.1
  rw [abs_mul, abs_of_pos hinv0] at hscaled_gt
  have : r * a < |x| := by
    have hrne : r ≠ 0 := ne_of_gt hr0
    calc
      r * a < r * (r⁻¹ * |x|) := mul_lt_mul_of_pos_left hscaled_gt hr0
      _ = |x| := by field_simp
  have : a < |x| := by nlinarith
  exact (not_lt_of_ge hxabs) this

theorem scaledEvenShellCutoff_outward
    {p r a b : ℝ} (hp : 0 < p) (hr : 1 < r) (ha : 0 < a) (hab : a < b)
    (hba : b ≤ p * a) (n : ℕ) :
    scaledEvenShellCutoff p a b
        (dilation r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))
          (evenShellVector a b hab n)) = 0 := by
  apply indicatorCutoff_dilation_normalizedIndicator_eq_zero
  exact (outward_shell_preimage_disjoint_general a b r ha hab hr n).mono_left
    (scaledEvenShellBand_subset_Icc hp ha hba)

theorem indicatorCutoff_eq_zero_of_subset_parent
    {c d : Set ℝ} (hc : MeasurableSet c) (hd : MeasurableSet d) (hcd : c ⊆ d)
    (f : SoninL2) (hf : indicatorCutoff d hd f = 0) :
    indicatorCutoff c hc f = 0 := by
  apply Lp.ext
  have hfAE := Lp.eq_zero_iff_ae_eq_zero.mp hf
  filter_upwards [indicatorCutoff_ae c hc f, indicatorCutoff_ae d hd f,
    hfAE, Lp.coeFn_zero ℂ 2 volume] with x hsmall hlarge hzero houtzero
  rw [hsmall]
  by_cases hxc : x ∈ c
  · have hxd : x ∈ d := hcd hxc
    rw [Set.indicator_of_mem hxc]
    have hfx : f x = 0 := by
      rw [hlarge, Set.indicator_of_mem hxd] at hzero
      exact hzero
    rw [hfx]
    exact houtzero.symm
  · rw [Set.indicator_of_notMem hxc]
    exact houtzero.symm

theorem scaledEvenShellCutoff_centralSoninProjection_eq_zero
    {p a b : ℝ} (hp : 0 < p) (ha : 0 < a)
    (hba : b ≤ p * a) (f : SoninL2) :
    scaledEvenShellCutoff p a b (centralSoninProjection a f) = 0 := by
  apply indicatorCutoff_eq_zero_of_subset_parent
    (measurableSet_scaledEvenShellBand p a b) measurableSet_Icc
    (scaledEvenShellBand_subset_Icc hp ha hba)
  rw [indicatorCutoff_eq_physicalForbidden_starProjection]
  change (centralPhysicalForbidden a).starProjection
    (centralSoninProjection a f) = 0
  apply (centralPhysicalForbidden a).starProjection_apply_eq_zero_iff.mpr
  exact ((centralPhysicalForbidden a)ᗮ ⊓
    (centralFourierForbidden a)ᗮ).starProjection_apply_mem f |>.1

theorem norm_scaledEvenShellCutoff_apply_le (p a b : ℝ) (f : SoninL2) :
    ‖scaledEvenShellCutoff p a b f‖ ≤ ‖f‖ := by
  rw [scaledEvenShellCutoff, indicatorCutoff_eq_physicalForbidden_starProjection]
  exact (physicalForbidden (scaledEvenShellBand p a b)
    (measurableSet_scaledEvenShellBand p a b)).norm_starProjection_apply_le f

/-- A fixed positive scaled-shell observation forces the corresponding central Sonin corner to be
noncompact. -/
theorem centralSoninCorner_not_isCompactOperator_of_scaledShell_norm
    {a b p c₀ : ℝ} (ha : 0 < a) (hab : a < b) (hp : 0 < p)
    (hba : b ≤ p * a) (hc₀ : 0 < c₀) (W : SoninL2 →L[ℂ] SoninL2)
    (hW : ∀ n, ‖scaledEvenShellCutoff p a b
      (W (evenShellVector a b hab n))‖ = c₀) :
    ¬ IsCompactOperator
      (crossBoundary (centralSoninProjection a) W : SoninL2 →L[ℂ] SoninL2) := by
  let Q : SoninL2 →L[ℂ] SoninL2 := centralSoninProjection a
  let A : SoninL2 →L[ℂ] SoninL2 := scaledEvenShellCutoff p a b
  let g : ℕ → SoninL2 := evenShellVector a b hab
  let e : ℕ → SoninL2 := fun n => Q (g n)
  have hg : Orthonormal ℂ g := evenShellVector_orthonormal a b ha hab
  have heApprox : Tendsto (fun n => ‖e n - g n‖) atTop (𝓝 0) := by
    simpa [e, g, Q] using
      centralSoninProjection_evenShellVector_tendsto_general a b ha hab
  have heWeak : ∀ ℓ : SoninL2 →L[ℂ] ℂ,
      Tendsto (fun n => ℓ (e n)) atTop (𝓝 0) :=
    weakly_tendsto_zero_of_norm_sub_tendsto_zero
      (Orthonormal.weakly_tendsto_zero hg) heApprox
  have heBound : ∀ n, ‖e n‖ ≤ 1 := by
    intro n
    calc
      ‖e n‖ ≤ ‖g n‖ := (centralSoninCarrier a).norm_starProjection_apply_le (g n)
      _ = 1 := hg.norm_eq_one n
  have hQe : ∀ n, Q (e n) = e n := by
    intro n
    apply (centralSoninCarrier a).starProjection_eq_self_iff.mpr
    exact (centralSoninCarrier a).starProjection_apply_mem (g n)
  have hAQ : ∀ x, A (Q x) = 0 := by
    intro x
    exact scaledEvenShellCutoff_centralSoninProjection_eq_zero hp ha hba x
  have hAContract : ∀ x, ‖A x‖ ≤ ‖x‖ := by
    intro x
    exact norm_scaledEvenShellCutoff_apply_le p a b x
  have hDiff : Tendsto (fun n => ‖A (W (e n)) - A (W (g n))‖) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n => ‖A ∘L W‖ * ‖e n - g n‖) atTop (𝓝 0) := by
      simpa using heApprox.const_mul ‖A ∘L W‖
    apply squeeze_zero (fun n => norm_nonneg _) _ hupper
    intro n
    calc
      ‖A (W (e n)) - A (W (g n))‖ = ‖(A ∘L W) (e n - g n)‖ := by
        rw [map_sub]
        rfl
      _ ≤ ‖A ∘L W‖ * ‖e n - g n‖ := (A ∘L W).le_opNorm _
  have hCross : Tendsto (fun n => ‖A (W (e n))‖) atTop (𝓝 c₀) := by
    apply tendsto_norm_of_norm_sub_tendsto_zero_of_norm_eq hDiff
    intro n
    exact hW n
  have hLower : ∀ᶠ n in atTop, c₀ / 2 ≤ ‖A (W (e n))‖ := by
    have hlt : ∀ᶠ n in atTop, c₀ / 2 < ‖A (W (e n))‖ :=
      (tendsto_order.1 hCross).1 (c₀ / 2) (by linarith)
    exact hlt.mono fun _ hn => hn.le
  simpa [Q] using
    crossBoundary_not_isCompactOperator_of_eventual_shell_sequence
      Q W A e 1 (c₀ / 2) heBound heWeak (by linarith) hQe hAQ hAContract hLower

/-- A finite linear combination of symmetric dilation actions. -/
def finiteDilationCombination {n : ℕ} (r : Fin n → ℝ) (hr : ∀ j, 1 < r j)
    (c : Fin n → ℂ) : SoninL2 →L[ℂ] SoninL2 :=
  ∑ j, c j • dilationSum (r j) (hr j)

theorem scaledEvenShellCutoff_finiteDilationCombination_apply
    {n : ℕ} {a b : ℝ} (r : Fin n → ℝ) (hr : ∀ j, 1 < r j)
    (c : Fin n → ℂ) (k : Fin n) (ha : 0 < a) (hab : a < b)
    (hba : b ≤ r k * a)
    (hsep : ∀ j, j ≠ k → c j ≠ 0 → b * r k < a * r j) (m : ℕ) :
    scaledEvenShellCutoff (r k) a b
        (finiteDilationCombination r hr c (evenShellVector a b hab m)) =
      c k • dilation (r k) (zero_lt_one.trans (hr k))
        (evenShellVector a b hab m) := by
  classical
  let g := evenShellVector a b hab m
  have hk0 : 0 < r k := zero_lt_one.trans (hr k)
  calc
    scaledEvenShellCutoff (r k) a b (finiteDilationCombination r hr c g) =
        ∑ j, scaledEvenShellCutoff (r k) a b ((c j • dilationSum (r j) (hr j)) g) := by
      rw [finiteDilationCombination, ContinuousLinearMap.sum_apply, map_sum]
    _ = c k • dilation (r k) hk0 g := by
      rw [Finset.sum_eq_single k]
      · rw [ContinuousLinearMap.smul_apply, dilationSum_apply, map_smul, map_add,
          scaledEvenShellCutoff_target_inward hk0 hab m,
          scaledEvenShellCutoff_outward hk0 (hr k) ha hab hba m]
        module
      · intro j _ hjk
        by_cases hcj : c j = 0
        · simp [hcj]
        · have hj0 : 0 < r j := zero_lt_one.trans (hr j)
          rw [ContinuousLinearMap.smul_apply, dilationSum_apply, map_smul, map_add,
            scaledEvenShellCutoff_offtarget_inward hk0 hj0 ha hab (hsep j hjk hcj) m,
            scaledEvenShellCutoff_outward hk0 (hr j) ha hab hba m]
          simp
      · simp

theorem norm_scaledEvenShellCutoff_finiteDilationCombination_apply
    {n : ℕ} {a b : ℝ} (r : Fin n → ℝ) (hr : ∀ j, 1 < r j)
    (c : Fin n → ℂ) (k : Fin n) (ha : 0 < a) (hab : a < b)
    (hba : b ≤ r k * a)
    (hsep : ∀ j, j ≠ k → c j ≠ 0 → b * r k < a * r j) (m : ℕ) :
    ‖scaledEvenShellCutoff (r k) a b
        (finiteDilationCombination r hr c (evenShellVector a b hab m))‖ = ‖c k‖ := by
  rw [scaledEvenShellCutoff_finiteDilationCombination_apply r hr c k ha hab hba hsep]
  rw [norm_smul, (dilation (r k) (zero_lt_one.trans (hr k))).norm_map,
    (evenShellVector_orthonormal a b ha hab).norm_eq_one m, mul_one]

theorem exists_finiteSupport_separatingShellUpper
    {n : ℕ} {a : ℝ} (r : Fin n → ℝ) (hr : ∀ j, 1 < r j) (c : Fin n → ℂ)
    (k : Fin n) (ha : 0 < a) (hmin : ∀ j, j ≠ k → c j ≠ 0 → r k < r j) :
    ∃ b : ℝ, a < b ∧ b ≤ r k * a ∧
      ∀ j, j ≠ k → c j ≠ 0 → b * r k < a * r j := by
  classical
  have hk0 : 0 < r k := zero_lt_one.trans (hr k)
  let S : Finset (Fin n) := Finset.univ.filter fun j => c j ≠ 0
  let U : Finset ℝ :=
    insert (r k * a) ((S.erase k).image fun j => a * r j / r k)
  have hUne : U.Nonempty := ⟨r k * a, Finset.mem_insert_self _ _⟩
  let u : ℝ := U.min' hUne
  have hau : a < u := by
    rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · nlinarith [hr k]
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
      have hcj : c j ≠ 0 := (Finset.mem_filter.mp
        (Finset.mem_erase.mp hj).2).2
      rw [lt_div_iff₀ hk0]
      nlinarith [hmin j hjk hcj]
  let b : ℝ := (a + u) / 2
  have hab : a < b := by dsimp [b]; linarith
  have hbu : b < u := by dsimp [b]; linarith
  have hupa : u ≤ r k * a :=
    Finset.min'_le U (r k * a) (Finset.mem_insert_self _ _)
  refine ⟨b, hab, hbu.le.trans hupa, ?_⟩
  intro j hjk hcj
  have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcj⟩
  have hmem : a * r j / r k ∈ U := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hjk, hjS⟩, rfl⟩
  have huj : u ≤ a * r j / r k := Finset.min'_le U _ hmem
  have hbj : b < a * r j / r k := hbu.trans_le huj
  rwa [lt_div_iff₀ hk0] at hbj

/-- **Finite Calkin independence.** Distinct dilation scales have linearly independent lower Sonin
corners modulo compact operators: every nonzero finite coefficient family gives a noncompact
corner. -/
theorem finiteDilationCorners_calkinIndependent
    {n : ℕ} {a : ℝ} (r : Fin n → ℝ) (hr : ∀ j, 1 < r j)
    (hinj : Function.Injective r) (c : Fin n → ℂ) (ha : 0 < a)
    (hc : ∃ j, c j ≠ 0) :
    ¬ IsCompactOperator
      (crossBoundary (centralSoninProjection a) (finiteDilationCombination r hr c) :
        SoninL2 →L[ℂ] SoninL2) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun j => c j ≠ 0
  have hSne : S.Nonempty := by
    obtain ⟨j, hcj⟩ := hc
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcj⟩⟩
  let R : Finset ℝ := S.image r
  have hRne : R.Nonempty := hSne.image r
  let u : ℝ := R.min' hRne
  have huR : u ∈ R := Finset.min'_mem R hRne
  obtain ⟨k, hkS, hku⟩ := Finset.mem_image.mp huR
  have hck : c k ≠ 0 := (Finset.mem_filter.mp hkS).2
  have hmin : ∀ j, j ≠ k → c j ≠ 0 → r k < r j := by
    intro j hjk hcj
    have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcj⟩
    have hrjR : r j ∈ R := Finset.mem_image.mpr ⟨j, hjS, rfl⟩
    have hle : u ≤ r j := Finset.min'_le R _ hrjR
    have hne : u ≠ r j := by
      intro heq
      apply hjk
      apply hinj
      calc
        r j = u := heq.symm
        _ = r k := hku.symm
    rw [hku]
    exact lt_of_le_of_ne hle hne
  obtain ⟨b, hab, hba, hsep⟩ :=
    exists_finiteSupport_separatingShellUpper r hr c k ha hmin
  apply centralSoninCorner_not_isCompactOperator_of_scaledShell_norm
    ha hab (zero_lt_one.trans (hr k)) hba (norm_pos_iff.mpr hck)
    (finiteDilationCombination r hr c)
  intro m
  exact norm_scaledEvenShellCutoff_finiteDilationCombination_apply
    r hr c k ha hab hba hsep m

/-- A finite linear combination of the positive one-scale Euler metrics. -/
def finitePositiveEulerCombination {n : ℕ} (r : Fin n → ℝ) (hr : ∀ j, 1 < r j)
    (c : Fin n → ℂ) : SoninL2 →L[ℂ] SoninL2 :=
  ∑ j, c j • positiveEulerDilationOperator (r j) (hr j)

/-- The constant part of every positive Euler metric disappears at the lower Sonin corner, leaving
exactly its nonzero dilation coefficient. -/
theorem crossBoundary_finitePositiveEulerCombination_eq_dilationCombination
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (hr : ∀ j, 1 < r j) (c : Fin n → ℂ) :
    (crossBoundary (centralSoninProjection a) (finitePositiveEulerCombination r hr c) :
        SoninL2 →L[ℂ] SoninL2) =
      crossBoundary (centralSoninProjection a)
        (finiteDilationCombination r hr
          (fun j => c j * (-((Real.sqrt (r j) : ℂ)⁻¹)))) := by
  classical
  have hsmul (z : ℂ) (T : SoninL2 →L[ℂ] SoninL2) :
      (crossBoundary (centralSoninProjection a) (z • T) :
          SoninL2 →L[ℂ] SoninL2) =
        z • (crossBoundary (centralSoninProjection a) T :
          SoninL2 →L[ℂ] SoninL2) := by
    simp [crossBoundary]
  have hsum (T : Fin n → (SoninL2 →L[ℂ] SoninL2)) :
      (crossBoundary (centralSoninProjection a) (∑ j, T j) :
          SoninL2 →L[ℂ] SoninL2) =
        ∑ j, (crossBoundary (centralSoninProjection a) (T j) :
          SoninL2 →L[ℂ] SoninL2) := by
    classical
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simp [crossBoundary]
    | @insert j s hj ih =>
        simp only [Finset.sum_insert hj]
        rw [crossBoundary_add, ih]
  rw [finitePositiveEulerCombination, finiteDilationCombination]
  rw [hsum, hsum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hsmul, centralPositiveEulerCorner_eq_smul a (r j) (hr j), hsmul]
  module

/-- **Finite Euler Calkin independence.**  Distinct positive Euler metric corners are linearly
independent modulo compact operators. -/
theorem finitePositiveEulerCorners_calkinIndependent
    {n : ℕ} {a : ℝ} (r : Fin n → ℝ) (hr : ∀ j, 1 < r j)
    (hinj : Function.Injective r) (c : Fin n → ℂ) (ha : 0 < a)
    (hc : ∃ j, c j ≠ 0) :
    ¬ IsCompactOperator
      (crossBoundary (centralSoninProjection a) (finitePositiveEulerCombination r hr c) :
        SoninL2 →L[ℂ] SoninL2) := by
  rw [crossBoundary_finitePositiveEulerCombination_eq_dilationCombination]
  apply finiteDilationCorners_calkinIndependent r hr hinj
    (fun j => c j * (-((Real.sqrt (r j) : ℂ)⁻¹))) ha
  obtain ⟨j, hcj⟩ := hc
  refine ⟨j, mul_ne_zero hcj ?_⟩
  have hr0 : 0 < r j := zero_lt_one.trans (hr j)
  simp [Real.sqrt_ne_zero'.mpr hr0]

end RHTower
namespace RHTower

theorem centralSoninProjection_evenProjection_commute (a : ℝ) :
    centralSoninProjection a ∘L evenProjection =
      evenProjection ∘L centralSoninProjection a := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.comp_apply, evenProjection_apply, map_smul, map_add]
  rw [l2Reflection_centralSoninProjection]

/-- The ambient even projection, with its codomain restricted to the actual even carrier. -/
def evenProjectionToEven : SoninL2 →L[ℂ] evenSubspace :=
  evenProjection.codRestrict evenSubspace fun f =>
    (mem_evenSubspace_iff _).mpr (l2Reflection_evenProjection f)

/-- The finite dilation-corner combination on the actual even Sonin carrier. -/
def finiteEvenDilationCorners {n : ℕ} (a : ℝ) (r : Fin n → ℝ)
    (hr : ∀ j, 1 < r j) (c : Fin n → ℂ) : evenSubspace →L[ℂ] evenSubspace :=
  ∑ j, c j • evenCentralSoninDilationCorner a (r j) (hr j)

theorem finiteEvenDilationCorners_coe_apply
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (hr : ∀ j, 1 < r j)
    (c : Fin n → ℂ) (f : evenSubspace) :
    ((finiteEvenDilationCorners a r hr c f : evenSubspace) : SoninL2) =
      (crossBoundary (centralSoninProjection a)
        (finiteDilationCombination r hr c) : SoninL2 →L[ℂ] SoninL2) f := by
  classical
  have hsum (T : Fin n → (SoninL2 →L[ℂ] SoninL2)) :
      (crossBoundary (centralSoninProjection a) (∑ j, T j) :
          SoninL2 →L[ℂ] SoninL2) =
        ∑ j, (crossBoundary (centralSoninProjection a) (T j) :
          SoninL2 →L[ℂ] SoninL2) := by
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simp [crossBoundary]
    | @insert j s hj ih =>
        simp only [Finset.sum_insert hj]
        rw [crossBoundary_add, ih]
  have hsmul (z : ℂ) (T : SoninL2 →L[ℂ] SoninL2) :
      (crossBoundary (centralSoninProjection a) (z • T) :
          SoninL2 →L[ℂ] SoninL2) =
        z • (crossBoundary (centralSoninProjection a) T :
          SoninL2 →L[ℂ] SoninL2) := by
    simp [crossBoundary]
  rw [finiteDilationCombination, hsum]
  change (evenSubspace.subtype : evenSubspace →ₗ[ℂ] SoninL2)
      ((finiteEvenDilationCorners a r hr c) f) = _
  rw [finiteEvenDilationCorners, ContinuousLinearMap.sum_apply, map_sum]
  simp only [ContinuousLinearMap.smul_apply, map_smul]
  rw [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [hsmul, ContinuousLinearMap.smul_apply]
  exact congrArg (fun x : SoninL2 => c j • x)
    (coe_evenCentralSoninDilationCorner_apply a (r j) (hr j) f)

/-- Distinct dilation corners remain Calkin-independent after restriction to the actual even Sonin
carrier. -/
theorem finiteEvenDilationCorners_calkinIndependent
    {n : ℕ} {a : ℝ} (r : Fin n → ℝ) (hr : ∀ j, 1 < r j)
    (hinj : Function.Injective r) (c : Fin n → ℂ) (ha : 0 < a)
    (hc : ∃ j, c j ≠ 0) :
    ¬ IsCompactOperator (finiteEvenDilationCorners a r hr c) := by
  classical
  let W : SoninL2 →L[ℂ] SoninL2 := finiteDilationCombination r hr c
  let E : SoninL2 →L[ℂ] SoninL2 := evenProjection
  let WEven : SoninL2 →L[ℂ] SoninL2 := W ∘L E
  have hnon : ¬ IsCompactOperator
      (crossBoundary (centralSoninProjection a) WEven : SoninL2 →L[ℂ] SoninL2) := by
    let S : Finset (Fin n) := Finset.univ.filter fun j => c j ≠ 0
    have hSne : S.Nonempty := by
      obtain ⟨j, hcj⟩ := hc
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcj⟩⟩
    let R : Finset ℝ := S.image r
    have hRne : R.Nonempty := hSne.image r
    let u : ℝ := R.min' hRne
    have huR : u ∈ R := Finset.min'_mem R hRne
    obtain ⟨k, hkS, hku⟩ := Finset.mem_image.mp huR
    have hck : c k ≠ 0 := (Finset.mem_filter.mp hkS).2
    have hmin : ∀ j, j ≠ k → c j ≠ 0 → r k < r j := by
      intro j hjk hcj
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcj⟩
      have hrjR : r j ∈ R := Finset.mem_image.mpr ⟨j, hjS, rfl⟩
      have hle : u ≤ r j := Finset.min'_le R _ hrjR
      have hne : u ≠ r j := by
        intro heq
        apply hjk
        apply hinj
        calc
          r j = u := heq.symm
          _ = r k := hku.symm
      rw [hku]
      exact lt_of_le_of_ne hle hne
    obtain ⟨b, hab, hba, hsep⟩ :=
      exists_finiteSupport_separatingShellUpper r hr c k ha hmin
    apply centralSoninCorner_not_isCompactOperator_of_scaledShell_norm
      ha hab (zero_lt_one.trans (hr k)) hba (norm_pos_iff.mpr hck) WEven
    intro m
    have heven : evenProjection (evenShellVector a b hab m) =
        evenShellVector a b hab m := by
      rw [evenProjection_apply, l2Reflection_evenShellVector a b hab m]
      module
    simpa [WEven, W, E, heven] using
      norm_scaledEvenShellCutoff_finiteDilationCombination_apply
        r hr c k ha hab hba hsep m
  intro hcompact
  have hextCompact : IsCompactOperator
      (evenSubspace.subtypeL ∘L finiteEvenDilationCorners a r hr c ∘L
        evenProjectionToEven : SoninL2 →L[ℂ] SoninL2) := by
    exact (hcompact.comp_clm evenProjectionToEven).clm_comp evenSubspace.subtypeL
  apply hnon
  have heq :
      (evenSubspace.subtypeL ∘L finiteEvenDilationCorners a r hr c ∘L
        evenProjectionToEven : SoninL2 →L[ℂ] SoninL2) =
      (crossBoundary (centralSoninProjection a) WEven : SoninL2 →L[ℂ] SoninL2) := by
    apply ContinuousLinearMap.ext
    intro f
    change ((finiteEvenDilationCorners a r hr c (evenProjectionToEven f) :
        evenSubspace) : SoninL2) = _
    rw [finiteEvenDilationCorners_coe_apply]
    change (crossBoundary (centralSoninProjection a) W : SoninL2 →L[ℂ] SoninL2)
        (evenProjection f) =
      (crossBoundary (centralSoninProjection a) (W ∘L E) :
        SoninL2 →L[ℂ] SoninL2) f
    have hQE : centralSoninProjection a (E f) =
        E (centralSoninProjection a f) := by
      simpa [E] using
        DFunLike.congr_fun (centralSoninProjection_evenProjection_commute a) f
    simp only [crossBoundary, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply]
    rw [hQE]
  rw [← heq]
  exact hextCompact

/-- A finite linear combination of positive Euler corners on the actual even carrier. -/
def finiteEvenPositiveEulerCorners {n : ℕ} (a : ℝ) (r : Fin n → ℝ)
    (hr : ∀ j, 1 < r j) (c : Fin n → ℂ) : evenSubspace →L[ℂ] evenSubspace :=
  ∑ j, c j • evenCentralPositiveEulerCorner a (r j) (hr j)

theorem finiteEvenPositiveEulerCorners_eq_dilationCorners
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (hr : ∀ j, 1 < r j)
    (c : Fin n → ℂ) :
    finiteEvenPositiveEulerCorners a r hr c =
      finiteEvenDilationCorners a r hr
        (fun j => c j * (-((Real.sqrt (r j) : ℂ)⁻¹))) := by
  classical
  simp only [finiteEvenPositiveEulerCorners, finiteEvenDilationCorners]
  apply Finset.sum_congr rfl
  intro j _
  rw [evenCentralPositiveEulerCorner_eq_smul, smul_smul]

/-- The positive Euler corners are linearly independent modulo compact operators on the actual even
Sonin carrier. -/
theorem finiteEvenPositiveEulerCorners_calkinIndependent
    {n : ℕ} {a : ℝ} (r : Fin n → ℝ) (hr : ∀ j, 1 < r j)
    (hinj : Function.Injective r) (c : Fin n → ℂ) (ha : 0 < a)
    (hc : ∃ j, c j ≠ 0) :
    ¬ IsCompactOperator (finiteEvenPositiveEulerCorners a r hr c) := by
  rw [finiteEvenPositiveEulerCorners_eq_dilationCorners]
  apply finiteEvenDilationCorners_calkinIndependent r hr hinj
    (fun j => c j * (-((Real.sqrt (r j) : ℂ)⁻¹))) ha
  obtain ⟨j, hcj⟩ := hc
  refine ⟨j, mul_ne_zero hcj ?_⟩
  simp [Real.sqrt_ne_zero'.mpr (zero_lt_one.trans (hr j))]

/-- A finite linear combination of the literal positive Euler metric corners on the concrete
archimedean Hardy--Titchmarsh line. -/
def finiteArchimedeanPrimeEulerCorners {n : ℕ} (a : ℝ) (r : Fin n → ℝ)
    (c : Fin n → ℂ) :
    ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  ∑ j, c j • archimedeanPrimeEulerCorner a (r j)

theorem finiteArchimedeanPrimeEulerCorners_eq_unitaryPush
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (hr : ∀ j, 1 < r j)
    (c : Fin n → ℂ) :
    finiteArchimedeanPrimeEulerCorners a r c =
      unitaryPush archimedeanDualHardyTitchmarshUnitary
        (finiteEvenPositiveEulerCorners a r hr c) := by
  classical
  have hterm (j : Fin n) :
      archimedeanPrimeEulerCorner a (r j) =
        unitaryPush archimedeanDualHardyTitchmarshUnitary
          (evenCentralPositiveEulerCorner a (r j) (hr j)) := by
    rw [archimedeanPrimeEulerCorner_eq_sourceCorner (hp := hr j),
      hardyTitchmarshEulerCorner_eq_unitaryPush]
  rw [finiteArchimedeanPrimeEulerCorners, finiteEvenPositiveEulerCorners]
  calc
    ∑ j, c j • archimedeanPrimeEulerCorner a (r j) =
        ∑ j, c j • unitaryPush archimedeanDualHardyTitchmarshUnitary
          (evenCentralPositiveEulerCorner a (r j) (hr j)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hterm j]
    _ = unitaryPush archimedeanDualHardyTitchmarshUnitary
          (∑ j, c j • evenCentralPositiveEulerCorner a (r j) (hr j)) := by
      symm
      induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
      | empty => simp [unitaryPush]
      | @insert j s hj ih =>
          simp only [Finset.sum_insert hj, unitaryPush_add, unitaryPush_smul, ih]

/-- **Concrete source theorem.** Distinct positive Euler metric corners on the archimedean
Hardy--Titchmarsh line are linearly independent in the Calkin quotient. -/
theorem finiteArchimedeanPrimeEulerCorners_calkinIndependent
    {n : ℕ} {a : ℝ} (r : Fin n → ℝ) (hr : ∀ j, 1 < r j)
    (hinj : Function.Injective r) (c : Fin n → ℂ) (ha : 0 < a)
    (hc : ∃ j, c j ≠ 0) :
    ¬ IsCompactOperator (finiteArchimedeanPrimeEulerCorners a r c) := by
  rw [finiteArchimedeanPrimeEulerCorners_eq_unitaryPush]
  intro hcompact
  apply finiteEvenPositiveEulerCorners_calkinIndependent r hr hinj c ha hc
  have hpull := (hcompact.comp_clm
    (archimedeanDualHardyTitchmarshUnitary :
      evenSubspace →L[ℂ] ArchimedeanWeightedL2)).clm_comp
    (archimedeanDualHardyTitchmarshUnitary.symm :
      ArchimedeanWeightedL2 →L[ℂ] evenSubspace)
  simpa [unitaryPush, Function.comp_def] using hpull

end RHTower
