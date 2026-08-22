import GaloisForLFunctions.RHTower.SoninApertureStrict
import GaloisForLFunctions.RHTower.SoninProjectionCalkin
import GaloisForLFunctions.RHTower.BurnolSoninEvenCosineAperture

/-!
# Burnol's Proposition 4.7 for the cosine-invariant and cosine-skew parts

The Sonine space `K_a` is invariant under the cosine transform, so it splits into the `+1` and `-1`
eigenspaces of that involution.  Proposition 4.7 asserts strictness of the aperture filtration on
each half separately.

The mechanism is the same shell obstruction as in `SoninApertureStrict`, symmetrised.  Write
`A_c`, `B_c` for the two forbidden bands and `S_c = A_c ⊔ B_c`, so `K_c = S_cᗮ`.  For `ε = ±1` and
`g` the *even* shell indicator of `a ≤ |x| ≤ b`, the vector `h = g + ε • 𝓕 g` lies in `S_b`, is
even, and satisfies `𝓕 h = ε • h`.  If `h` were in `S_a`, say `h = u + v`, then `g - u = v - ε𝓕g`
would lie in `A_b ⊓ B_b = ⊥`, forcing `g = u ∈ A_a`, which the shell forbids.

The eigen-projection `f ↦ (evenProjection f + ε • 𝓕 (evenProjection f))/2` maps `K_a` into the
`ε`-eigenspace without changing the pairing against `h`, which converts the obstruction into
`K_b ⊓ E_ε < K_a ⊓ E_ε`.  Baire then upgrades strictness to properness of the union exactly as in
the unrestricted case.

## Main results

* `soninFourierEigen` — the `ε`-eigenspace of `𝓕` inside the even carrier
* `centralSoninCarrier_inf_eigen_strictAnti` — strictness at each aperture
* `iSup_centralSoninCarrier_inf_eigen_lt` — **Burnol's Proposition 4.7, eigen-part form**
-/

noncomputable section

open MeasureTheory Set

open scoped InnerProductSpace

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## The two bands are stable under reflection and under the Fourier transform -/

theorem fourierUnitary_fourierUnitary_eq_l2Reflection (f : SoninL2) :
    fourierUnitary (fourierUnitary f) = l2Reflection f := by
  have h := fourierUnitary_symm_eq_reflection_fourier (fourierUnitary f)
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  rw [← l2Reflection_involutive (fourierUnitary (fourierUnitary f)), ← h]

theorem l2Reflection_mem_centralPhysicalForbidden {a : ℝ} {f : SoninL2}
    (hf : f ∈ centralPhysicalForbidden a) : l2Reflection f ∈ centralPhysicalForbidden a := by
  show l2Reflection f ∈ physicalForbidden (Set.Icc (-a) a) measurableSet_Icc
  rw [mem_physicalForbidden_iff]
  have hf' : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Set.Icc (-a) a → (f : ℝ → ℂ) x = 0 := by
    rw [← mem_physicalForbidden_iff]; exact hf
  have hrefl := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving
  filter_upwards [l2Reflection_ae f, hrefl.ae hf'] with x hx hz hout
  rw [hx]
  refine hz fun hmem => hout ?_
  simp only [Set.mem_Icc] at hmem ⊢
  constructor <;> linarith [hmem.1, hmem.2]

theorem l2Reflection_mem_centralFourierForbidden {a : ℝ} {f : SoninL2}
    (hf : f ∈ centralFourierForbidden a) : l2Reflection f ∈ centralFourierForbidden a := by
  rw [centralFourierForbidden, mem_fourierForbidden_iff] at hf ⊢
  rw [fourierUnitary_l2Reflection]
  exact l2Reflection_mem_centralPhysicalForbidden hf

theorem fourierUnitary_mem_centralFourierForbidden {a : ℝ} {f : SoninL2}
    (hf : f ∈ centralPhysicalForbidden a) : fourierUnitary f ∈ centralFourierForbidden a := by
  rw [centralFourierForbidden, mem_fourierForbidden_iff]
  rw [fourierUnitary_fourierUnitary_eq_l2Reflection]
  exact l2Reflection_mem_centralPhysicalForbidden hf

theorem fourierUnitary_mem_centralPhysicalForbidden {a : ℝ} {f : SoninL2}
    (hf : f ∈ centralFourierForbidden a) : fourierUnitary f ∈ centralPhysicalForbidden a := by
  rw [centralFourierForbidden, mem_fourierForbidden_iff] at hf
  exact hf

/-- The sum of the two bands is stable under the Fourier transform. -/
theorem fourierUnitary_mem_sup {a : ℝ} {f : SoninL2}
    (hf : f ∈ centralPhysicalForbidden a ⊔ centralFourierForbidden a) :
    fourierUnitary f ∈ centralPhysicalForbidden a ⊔ centralFourierForbidden a := by
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hf
  rw [← huv, map_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_right (fourierUnitary_mem_centralFourierForbidden hu))
    (Submodule.mem_sup_left (fourierUnitary_mem_centralPhysicalForbidden hv))

/-- The sum of the two bands is stable under reflection. -/
theorem l2Reflection_mem_sup {a : ℝ} {f : SoninL2}
    (hf : f ∈ centralPhysicalForbidden a ⊔ centralFourierForbidden a) :
    l2Reflection f ∈ centralPhysicalForbidden a ⊔ centralFourierForbidden a := by
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hf
  rw [← huv, map_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (l2Reflection_mem_centralPhysicalForbidden hu))
    (Submodule.mem_sup_right (l2Reflection_mem_centralFourierForbidden hv))

theorem evenProjection_mem_sup {a : ℝ} {f : SoninL2}
    (hf : f ∈ centralPhysicalForbidden a ⊔ centralFourierForbidden a) :
    evenProjection f ∈ centralPhysicalForbidden a ⊔ centralFourierForbidden a := by
  rw [evenProjection_apply]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hf (l2Reflection_mem_sup hf))

theorem fourierUnitary_symm_mem_sup {a : ℝ} {f : SoninL2}
    (hf : f ∈ centralPhysicalForbidden a ⊔ centralFourierForbidden a) :
    fourierUnitary.symm f ∈ centralPhysicalForbidden a ⊔ centralFourierForbidden a := by
  rw [fourierUnitary_symm_eq_reflection_fourier]
  exact l2Reflection_mem_sup (fourierUnitary_mem_sup hf)

/-! ## The eigenspaces of the cosine involution -/

/-- The `ε`-eigenspace of the Fourier transform inside the even carrier.  For `ε = 1` this is
Burnol's cosine-invariant part, for `ε = -1` the cosine-skew part. -/
def soninFourierEigen (ε : ℂ) : Submodule ℂ SoninL2 where
  carrier := {f | f ∈ evenSubspace ∧ fourierUnitary f = ε • f}
  zero_mem' := ⟨Submodule.zero_mem _, by simp⟩
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨Submodule.add_mem _ hx hy, by rw [map_add, hx', hy', smul_add]⟩
  smul_mem' := by
    rintro c x ⟨hx, hx'⟩
    exact ⟨Submodule.smul_mem _ _ hx, by rw [map_smul, hx', smul_comm]⟩

theorem mem_soninFourierEigen {ε : ℂ} {f : SoninL2} :
    f ∈ soninFourierEigen ε ↔ f ∈ evenSubspace ∧ fourierUnitary f = ε • f := Iff.rfl

theorem isClosed_soninFourierEigen (ε : ℂ) :
    IsClosed (soninFourierEigen ε : Set SoninL2) := by
  have hset : (soninFourierEigen ε : Set SoninL2)
      = (evenSubspace : Set SoninL2) ∩ {f : SoninL2 | fourierUnitary f = ε • f} := by
    ext f
    exact Iff.rfl
  rw [hset]
  refine IsClosed.inter (isClosed_of_hasOrthogonalProjection _) ?_
  exact isClosed_eq fourierUnitary.continuous (continuous_const_smul ε)

theorem inner_evenProjection_right (x y : SoninL2) :
    ⟪x, evenProjection y⟫_ℂ = ⟪evenProjection x, y⟫_ℂ := by
  simpa using (evenProjection_symmetric x y).symm

/-- The projection onto the `ε`-eigenspace of the cosine involution. -/
def soninEigenProjection (ε : ℂ) (f : SoninL2) : SoninL2 :=
  (2 : ℂ)⁻¹ • (evenProjection f + ε • fourierUnitary (evenProjection f))

theorem soninEigenProjection_mem {ε : ℂ} (hε : ε * ε = 1) (f : SoninL2) :
    soninEigenProjection ε f ∈ soninFourierEigen ε := by
  have hu : evenProjection f ∈ evenSubspace := ⟨f, rfl⟩
  have hFu : fourierUnitary (evenProjection f) ∈ evenSubspace :=
    fourierUnitary_mem_evenSubspace_self hu
  refine ⟨Submodule.smul_mem _ _ (Submodule.add_mem _ hu (Submodule.smul_mem _ _ hFu)), ?_⟩
  have hsq : fourierUnitary (fourierUnitary (evenProjection f)) = evenProjection f := by
    rw [fourierUnitary_fourierUnitary_eq_l2Reflection]
    exact (mem_evenSubspace_iff _).1 hu
  have hkey : ∀ x y : SoninL2, ε • ((2 : ℂ)⁻¹ • (x + ε • y)) = (2 : ℂ)⁻¹ • (y + ε • x) := by
    intro x y
    rw [smul_comm ε ((2 : ℂ)⁻¹), smul_add, smul_smul, hε, one_smul, add_comm]
  rw [soninEigenProjection, map_smul, map_add, map_smul, hsq,
    hkey (evenProjection f) (fourierUnitary (evenProjection f))]

theorem inner_soninEigenProjection {ε : ℂ} (hε : ε * ε = 1) (hεstar : (starRingEnd ℂ) ε = ε)
    (f : SoninL2) {h : SoninL2} (hh : h ∈ soninFourierEigen ε) :
    ⟪h, soninEigenProjection ε f⟫_ℂ = ⟪h, f⟫_ℂ := by
  obtain ⟨hheven, hheig⟩ := hh
  have hsymm : fourierUnitary.symm h = ε • h := by
    have h2 : fourierUnitary.symm (fourierUnitary h) = fourierUnitary.symm (ε • h) :=
      congrArg _ hheig
    rw [LinearIsometryEquiv.symm_apply_apply, map_smul] at h2
    calc fourierUnitary.symm h = (1 : ℂ) • fourierUnitary.symm h := (one_smul _ _).symm
      _ = (ε * ε) • fourierUnitary.symm h := by rw [hε]
      _ = ε • (ε • fourierUnitary.symm h) := by rw [smul_smul]
      _ = ε • h := by rw [← h2]
  have hFu : ⟪h, fourierUnitary (evenProjection f)⟫_ℂ = ε * ⟪h, evenProjection f⟫_ℂ := by
    have hmap := fourierUnitary.inner_map_map (fourierUnitary.symm h) (evenProjection f)
    rw [LinearIsometryEquiv.apply_symm_apply] at hmap
    rw [hmap, hsymm, inner_smul_left, hεstar]
  have hhp : evenProjection h = h := by
    rw [evenProjection_apply, (mem_evenSubspace_iff h).1 hheven]
    module
  have heven : ⟪h, evenProjection f⟫_ℂ = ⟪h, f⟫_ℂ := by
    have hs := evenProjection_symmetric h f
    simpa [hhp] using hs.symm
  rw [soninEigenProjection, inner_smul_right, inner_add_right, inner_smul_right, hFu, heven,
    ← mul_assoc ε ε ⟪h, f⟫_ℂ, hε, one_mul]
  ring

theorem soninEigenProjection_mem_centralSoninCarrier {ε : ℂ} {a : ℝ} {f : SoninL2}
    (hf : f ∈ centralSoninCarrier a) : soninEigenProjection ε f ∈ centralSoninCarrier a := by
  rw [centralSoninCarrier_eq_orthogonal_sup] at hf ⊢
  intro s hs
  have hzero : ∀ t ∈ centralPhysicalForbidden a ⊔ centralFourierForbidden a,
      ⟪evenProjection t, f⟫_ℂ = 0 := fun t ht => hf _ (evenProjection_mem_sup ht)
  have h1 : ⟪s, evenProjection f⟫_ℂ = 0 := by
    rw [inner_evenProjection_right]
    exact hzero s hs
  have h2 : ⟪s, fourierUnitary (evenProjection f)⟫_ℂ = 0 := by
    have hmap := fourierUnitary.inner_map_map (fourierUnitary.symm s) (evenProjection f)
    rw [LinearIsometryEquiv.apply_symm_apply] at hmap
    rw [hmap, inner_evenProjection_right]
    exact hzero _ (fourierUnitary_symm_mem_sup hs)
  rw [soninEigenProjection, inner_smul_right, inner_add_right, inner_smul_right, h1, h2]
  simp

/-! ## The even shell obstruction -/

/-- The symmetric shell `a ≤ |x| ≤ b`. -/
def evenShell (a b : ℝ) : Set ℝ := Set.Icc (-b) b \ Set.Ioo (-a) a

theorem measurableSet_evenShell (a b : ℝ) : MeasurableSet (evenShell a b) :=
  measurableSet_Icc.diff measurableSet_Ioo

theorem neg_mem_evenShell_iff {a b : ℝ} {x : ℝ} : -x ∈ evenShell a b ↔ x ∈ evenShell a b := by
  simp only [evenShell, Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioo, not_and_or, not_lt]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    rcases h3 with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    rcases h3 with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)

/-- The `L²` indicator of the symmetric shell. -/
def evenShellIndicator (a b : ℝ) : SoninL2 :=
  indicatorConstLp 2 (measurableSet_evenShell a b)
    ((measure_mono Set.sdiff_subset).trans_lt measure_Icc_lt_top).ne (1 : ℂ)

theorem evenShellIndicator_coeFn (a b : ℝ) :
    ((evenShellIndicator a b : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      (evenShell a b).indicator fun _ => (1 : ℂ) :=
  indicatorConstLp_coeFn

theorem evenShellIndicator_mem_evenSubspace (a b : ℝ) :
    evenShellIndicator a b ∈ evenSubspace := by
  rw [mem_evenSubspace_iff]
  apply Lp.ext
  have hrefl := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving
  filter_upwards [l2Reflection_ae (evenShellIndicator a b),
    hrefl.ae (evenShellIndicator_coeFn a b), evenShellIndicator_coeFn a b] with x h1 h2 h3
  rw [h1, h2, h3]
  by_cases hx : x ∈ evenShell a b
  · rw [Set.indicator_of_mem (neg_mem_evenShell_iff.2 hx), Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem (fun hc => hx (neg_mem_evenShell_iff.1 hc)),
      Set.indicator_of_notMem hx]

theorem evenShellIndicator_mem_centralPhysicalForbidden (a b : ℝ) :
    evenShellIndicator a b ∈ centralPhysicalForbidden b := by
  show evenShellIndicator a b ∈ physicalForbidden (Set.Icc (-b) b) measurableSet_Icc
  rw [mem_physicalForbidden_iff]
  filter_upwards [evenShellIndicator_coeFn a b] with x hx hout
  rw [hx]
  exact Set.indicator_of_notMem (fun hmem => hout hmem.1) _

theorem evenShellIndicator_notMem_centralPhysicalForbidden {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    evenShellIndicator a b ∉ centralPhysicalForbidden a := by
  intro hmem
  have hmem' : ∀ᵐ x ∂(volume : Measure ℝ),
      x ∉ Set.Icc (-a) a → ((evenShellIndicator a b : SoninL2) : ℝ → ℂ) x = 0 := by
    rw [← mem_physicalForbidden_iff]; exact hmem
  have hbad : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Set.Ioc a b := by
    filter_upwards [evenShellIndicator_coeFn a b, hmem'] with x hx hz hS
    have h1 : x ∈ evenShell a b := by
      refine ⟨⟨by linarith [hS.1, hS.2], hS.2⟩, ?_⟩
      simp only [Set.mem_Ioo, not_and_or, not_lt]
      exact Or.inr (le_of_lt hS.1)
    have h2 : x ∉ Set.Icc (-a) a := fun h => absurd h.2 (not_le.mpr hS.1)
    have hzero := hz h2
    rw [hx, Set.indicator_of_mem h1] at hzero
    exact one_ne_zero hzero
  have hnull : (volume : Measure ℝ) (Set.Ioc a b) = 0 := compl_mem_ae_iff.1 hbad
  rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at hnull
  linarith

/-! ## Strictness on each eigen-part -/

/-- The symmetrised shell vector: it lies in the larger band sum, is an `ε`-eigenvector, and
escapes the smaller band sum. -/
def eigenShellVector (ε : ℂ) (a b : ℝ) : SoninL2 :=
  evenShellIndicator a b + ε • fourierUnitary (evenShellIndicator a b)

theorem eigenShellVector_mem_eigen {ε : ℂ} (hε : ε * ε = 1) (a b : ℝ) :
    eigenShellVector ε a b ∈ soninFourierEigen ε := by
  have hu : evenShellIndicator a b ∈ evenSubspace := evenShellIndicator_mem_evenSubspace a b
  have hFu : fourierUnitary (evenShellIndicator a b) ∈ evenSubspace :=
    fourierUnitary_mem_evenSubspace_self hu
  refine ⟨Submodule.add_mem _ hu (Submodule.smul_mem _ _ hFu), ?_⟩
  have hsq : fourierUnitary (fourierUnitary (evenShellIndicator a b)) = evenShellIndicator a b := by
    rw [fourierUnitary_fourierUnitary_eq_l2Reflection]
    exact (mem_evenSubspace_iff _).1 hu
  rw [eigenShellVector, map_add, map_smul, hsq, smul_add, smul_smul, hε, one_smul, add_comm]

theorem eigenShellVector_mem_sup {ε : ℂ} (a b : ℝ) :
    eigenShellVector ε a b ∈ centralPhysicalForbidden b ⊔ centralFourierForbidden b :=
  Submodule.add_mem _
    (Submodule.mem_sup_left (evenShellIndicator_mem_centralPhysicalForbidden a b))
    (Submodule.smul_mem _ _ (Submodule.mem_sup_right
      (fourierUnitary_mem_centralFourierForbidden
        (evenShellIndicator_mem_centralPhysicalForbidden a b))))

theorem eigenShellVector_notMem_sup {ε : ℂ} {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    eigenShellVector ε a b ∉ centralPhysicalForbidden a ⊔ centralFourierForbidden a := by
  intro hmem
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hmem
  have hg : evenShellIndicator a b ∈ centralPhysicalForbidden b :=
    evenShellIndicator_mem_centralPhysicalForbidden a b
  rw [eigenShellVector] at huv
  set w : SoninL2 := evenShellIndicator a b - u with hw
  have hwA : w ∈ centralPhysicalForbidden b :=
    Submodule.sub_mem _ hg (centralPhysicalForbidden_mono hab.le hu)
  have hwB : w ∈ centralFourierForbidden b := by
    have hrw : w = v - ε • fourierUnitary (evenShellIndicator a b) := by
      rw [hw, sub_eq_sub_iff_add_eq_add, ← huv]
      abel
    rw [hrw]
    exact Submodule.sub_mem _ (centralFourierForbidden_mono hab.le hv)
      (Submodule.smul_mem _ _ (fourierUnitary_mem_centralFourierForbidden hg))
  have hw0 : w = 0 := by
    have hmem2 : w ∈ centralPhysicalForbidden b ⊓ centralFourierForbidden b := ⟨hwA, hwB⟩
    rwa [centralPhysicalForbidden_inf_centralFourierForbidden_eq_bot (le_refl b),
      Submodule.mem_bot] at hmem2
  have hgu : evenShellIndicator a b = u := by
    have := sub_eq_zero.1 hw0
    exact this
  exact evenShellIndicator_notMem_centralPhysicalForbidden ha hab (hgu ▸ hu)

/-- **Strictness of the aperture filtration on each eigen-part.** -/
theorem centralSoninCarrier_inf_eigen_strictAnti {ε : ℂ} (hε : ε * ε = 1)
    (hεstar : (starRingEnd ℂ) ε = ε) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    centralSoninCarrier b ⊓ soninFourierEigen ε < centralSoninCarrier a ⊓ soninFourierEigen ε := by
  refine lt_of_le_of_ne (inf_le_inf_right _ (centralSoninCarrier_antitone hab.le)) ?_
  intro heq
  set h : SoninL2 := eigenShellVector ε a b with hh
  have hhsup : h ∈ centralPhysicalForbidden b ⊔ centralFourierForbidden b :=
    eigenShellVector_mem_sup a b
  have hhnot : h ∉ centralPhysicalForbidden a ⊔ centralFourierForbidden a :=
    eigenShellVector_notMem_sup ha.le hab
  obtain ⟨f, hfK, hfne⟩ : ∃ f : SoninL2, f ∈ centralSoninCarrier a ∧ ⟪f, h⟫_ℂ ≠ 0 := by
    by_contra hcon
    refine hhnot ?_
    have hmem : h ∈ ((centralPhysicalForbidden a ⊔ centralFourierForbidden a)ᗮ)ᗮ := by
      intro u hu
      by_contra hne
      exact hcon ⟨u, by rwa [centralSoninCarrier_eq_orthogonal_sup], hne⟩
    haveI : CompleteSpace
        ((centralPhysicalForbidden a ⊔ centralFourierForbidden a : Submodule ℂ SoninL2)) :=
      (isClosed_centralPhysicalForbidden_sup_centralFourierForbidden a ha).completeSpace_coe
    haveI : (centralPhysicalForbidden a ⊔ centralFourierForbidden a :
        Submodule ℂ SoninL2).HasOrthogonalProjection :=
      Submodule.HasOrthogonalProjection.ofCompleteSpace _
    rwa [Submodule.orthogonal_orthogonal] at hmem
  set f' : SoninL2 := soninEigenProjection ε f with hf'
  have hf'K : f' ∈ centralSoninCarrier a := soninEigenProjection_mem_centralSoninCarrier hfK
  have hf'E : f' ∈ soninFourierEigen ε := soninEigenProjection_mem hε f
  have hf'b : f' ∈ centralSoninCarrier b := by
    have hmem2 : f' ∈ centralSoninCarrier b ⊓ soninFourierEigen ε := by
      rw [heq]; exact ⟨hf'K, hf'E⟩
    exact hmem2.1
  have hzero : ⟪f', h⟫_ℂ = 0 := by
    have := (centralSoninCarrier_eq_orthogonal_sup b) ▸ hf'b
    have hconj : ⟪h, f'⟫_ℂ = 0 := this h hhsup
    rw [← inner_conj_symm, hconj, map_zero]
  have hpair : ⟪h, f'⟫_ℂ = ⟪h, f⟫_ℂ :=
    inner_soninEigenProjection hε hεstar f (eigenShellVector_mem_eigen hε a b)
  apply hfne
  have h1 : ⟪h, f'⟫_ℂ = 0 := by rw [← inner_conj_symm, hzero, map_zero]
  have h2 : ⟪h, f⟫_ℂ = 0 := hpair ▸ h1
  rw [← inner_conj_symm, h2, map_zero]

theorem directed_centralSoninCarrier_inf_eigen (ε : ℂ) (a : ℝ) :
    Directed (· ≤ ·) fun b : Set.Ioi a => centralSoninCarrier (b : ℝ) ⊓ soninFourierEigen ε := by
  rintro ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩
  refine ⟨⟨min b₁ b₂, Set.mem_Ioi.2 (lt_min hb₁ hb₂)⟩, ?_, ?_⟩
  · exact inf_le_inf_right _ (centralSoninCarrier_antitone (min_le_left b₁ b₂))
  · exact inf_le_inf_right _ (centralSoninCarrier_antitone (min_le_right b₁ b₂))

/-- **Burnol's Proposition 4.7 on the eigen-parts.**  For `ε = ±1` the union of the strictly
smaller cosine-`ε` Sonine spaces is a proper subspace of the one at aperture `a`. -/
theorem iSup_centralSoninCarrier_inf_eigen_lt {ε : ℂ} (hε : ε * ε = 1)
    (hεstar : (starRingEnd ℂ) ε = ε) {a : ℝ} (ha : 0 < a) :
    (⨆ b : Set.Ioi a, centralSoninCarrier (b : ℝ) ⊓ soninFourierEigen ε)
      < centralSoninCarrier a ⊓ soninFourierEigen ε := by
  refine lt_of_le_of_ne
    (iSup_le fun b => inf_le_inf_right _ (centralSoninCarrier_antitone (le_of_lt b.2))) ?_
  intro heq
  haveI : Nonempty (Set.Ioi a) := ⟨⟨a + 1, by simp⟩⟩
  haveI hclosed : IsClosed
      ((centralSoninCarrier a ⊓ soninFourierEigen ε : Submodule ℂ SoninL2) : Set SoninL2) := by
    exact (centralSoninCarrier_isClosed a).inter (isClosed_soninFourierEigen ε)
  haveI hcomplete : CompleteSpace (centralSoninCarrier a ⊓ soninFourierEigen ε :
      Submodule ℂ SoninL2) := hclosed.completeSpace_coe
  set stage : ℕ → ℝ := fun n => a + 1 / ((n : ℝ) + 1) with hstage
  have hstage_gt : ∀ n : ℕ, a < stage n := by
    intro n
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    simpa [hstage] using this
  have hcover : ∀ x : (centralSoninCarrier a ⊓ soninFourierEigen ε : Submodule ℂ SoninL2),
      ∃ n : ℕ, (centralSoninCarrier a ⊓ soninFourierEigen ε).subtype x ∈
        centralSoninCarrier (stage n) ⊓ soninFourierEigen ε := by
    intro x
    have hx : (x : SoninL2) ∈
        ⨆ b : Set.Ioi a, centralSoninCarrier (b : ℝ) ⊓ soninFourierEigen ε := by
      rw [heq]; exact x.2
    obtain ⟨b, hb⟩ := (Submodule.mem_iSup_of_directed _
      (directed_centralSoninCarrier_inf_eigen ε a)).1 hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < (b : ℝ) - a by
      have := b.2
      simp only [Set.mem_Ioi] at this
      linarith)
    exact ⟨n, inf_le_inf_right _
      (centralSoninCarrier_antitone (by simp only [hstage]; linarith)) hb⟩
  obtain ⟨N, hN⟩ := shellBaire_exists_stage
    (centralSoninCarrier a ⊓ soninFourierEigen ε).subtype continuous_subtype_val
    (fun n => centralSoninCarrier (stage n) ⊓ soninFourierEigen ε)
    (fun n => (centralSoninCarrier_isClosed (stage n)).inter (isClosed_soninFourierEigen ε))
    hcover
  have hle : centralSoninCarrier a ⊓ soninFourierEigen ε
      ≤ centralSoninCarrier (stage N) ⊓ soninFourierEigen ε := by
    intro x hx
    exact hN ⟨x, hx⟩
  exact absurd (lt_of_lt_of_le
    (centralSoninCarrier_inf_eigen_strictAnti hε hεstar ha (hstage_gt N)) hle) (lt_irrefl _)

/-- **Burnol's Proposition 4.7 for the cosine-invariant part.** -/
theorem iSup_centralSoninCarrier_inf_eigen_one_lt {a : ℝ} (ha : 0 < a) :
    (⨆ b : Set.Ioi a, centralSoninCarrier (b : ℝ) ⊓ soninFourierEigen 1)
      < centralSoninCarrier a ⊓ soninFourierEigen 1 :=
  iSup_centralSoninCarrier_inf_eigen_lt (by norm_num) (by simp) ha

/-- **Burnol's Proposition 4.7 for the cosine-skew part.** -/
theorem iSup_centralSoninCarrier_inf_eigen_neg_one_lt {a : ℝ} (ha : 0 < a) :
    (⨆ b : Set.Ioi a, centralSoninCarrier (b : ℝ) ⊓ soninFourierEigen (-1))
      < centralSoninCarrier a ⊓ soninFourierEigen (-1) :=
  iSup_centralSoninCarrier_inf_eigen_lt (by norm_num) (by simp) ha

end RHTower

end
