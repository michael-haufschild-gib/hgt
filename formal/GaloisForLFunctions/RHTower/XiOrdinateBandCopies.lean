import GaloisForLFunctions.RHTower.XiAdmissibleHeights
import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity
import GaloisForLFunctions.RHTower.CentralReciprocalMoments
import GaloisForLFunctions.RHTower.XiHedenmalmMultiplicityChain

/-!
# Divisor-multiplicity copies in an ordinate band

The divisor mass of the symmetric rectangle of half-height `T` is the total multiplicity of the
`ξ`-zeros with ordinate modulus at most `T`, because every `ξ`-zero lies in the open critical strip.
Grouping the multiplicity copies over the supports in a band therefore produces a `Finset` of copies
whose cardinality is exactly the mass difference across the band.
-/

open Complex Set Metric

noncomputable section

namespace RHTower

/-! ## Zeros and supports of bounded ordinate -/

theorem xiZerosUpTo_finite (T : ℝ) : {u : ℂ | xi u = 0 ∧ |u.im| ≤ T}.Finite := by
  refine (xi_zeros_closedBall_finite 0 (1 + T)).subset ?_
  intro u hu
  refine ⟨?_, hu.1⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  refine le_trans (Complex.norm_le_abs_re_add_abs_im u) ?_
  have hstrip := xi_zero_re_mem_open_unit hu.1
  have hre : |u.re| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hstrip.1, hstrip.2]
  linarith [hu.2]

theorem xiSupportsUpTo_finite (T : ℝ) : {ρ : XiDivisorSupport | |(ρ : ℂ).im| ≤ T}.Finite := by
  refine Set.Finite.of_finite_image (f := fun ρ : XiDivisorSupport => (ρ : ℂ)) ?_ ?_
  · refine (xiZerosUpTo_finite T).subset ?_
    rintro u ⟨ρ, hρ, rfl⟩
    exact ⟨xi_eq_zero_of_mem_divisor_support ρ, hρ⟩
  · intro a _ b _ h
    exact Subtype.ext h

/-- The supports whose ordinate modulus lies in the band `(T₁, T₂]`. -/
def xiSupportsBand (T₁ T₂ : ℝ) : Finset XiDivisorSupport := by
  classical
  exact ((xiSupportsUpTo_finite T₂).toFinset).filter (fun ρ => T₁ < |(ρ : ℂ).im|)

theorem mem_xiSupportsBand {T₁ T₂ : ℝ} {ρ : XiDivisorSupport} :
    ρ ∈ xiSupportsBand T₁ T₂ ↔ T₁ < |(ρ : ℂ).im| ∧ |(ρ : ℂ).im| ≤ T₂ := by
  classical
  rw [xiSupportsBand, Finset.mem_filter, Set.Finite.mem_toFinset]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- The multiplicity copies over a band of supports. -/
def xiCopiesBand (T₁ T₂ : ℝ) : Finset XiZeroCopy :=
  (xiSupportsBand T₁ T₂).biUnion xiZeroCopyFiber

theorem mem_xiCopiesBand {T₁ T₂ : ℝ} {q : XiZeroCopy} :
    q ∈ xiCopiesBand T₁ T₂ ↔ T₁ < |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ T₂ := by
  classical
  rw [xiCopiesBand, Finset.mem_biUnion]
  constructor
  · rintro ⟨ρ, hρ, hq⟩
    rw [mem_xiZeroCopyFiber] at hq
    rw [hq]
    exact mem_xiSupportsBand.mp hρ
  · intro h
    exact ⟨q.1, mem_xiSupportsBand.mpr h, mem_xiZeroCopyFiber.mpr rfl⟩

theorem card_xiCopiesBand (T₁ T₂ : ℝ) :
    (xiCopiesBand T₁ T₂).card = ∑ ρ ∈ xiSupportsBand T₁ T₂, xiSupportMultiplicity ρ := by
  classical
  rw [xiCopiesBand, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [xiZeroCopyFiber, Finset.card_map, Finset.card_univ, Fintype.card_fin,
      xiSupportMultiplicity]
  · intro a _ b _ hab
    exact Finset.disjoint_left.mpr fun q hqa hqb =>
      hab ((mem_xiZeroCopyFiber.mp hqa).symm.trans (mem_xiZeroCopyFiber.mp hqb))

/-! ## The mass is the total multiplicity below a height -/

theorem xiSupportMultiplicity_eq_order (ρ : XiDivisorSupport) :
    (xiSupportMultiplicity ρ : ℤ) = ((analyticOrderAt xi (ρ : ℂ)).toNat : ℤ) := by
  rw [xiSupportMultiplicity, xi_divisor_apply_of_mem (Set.mem_univ ((ρ : ℂ)))]
  simp

theorem mem_symmetricRectangle_of_zero {T : ℝ} (hT : 0 ≤ T) {u : ℂ}
    (hzero : xi u = 0) (him : |u.im| ≤ T) :
    u ∈ Rectangle (((1 - 2 : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) ((2 : ℂ) + (T : ℂ) * I) := by
  have hstrip := xi_zero_re_mem_open_unit hzero
  have hzre : (((1 - 2 : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).re = -1 := by norm_num
  have hzim : (((1 - 2 : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).im = -T := by simp
  have hwre : ((2 : ℂ) + (T : ℂ) * I).re = 2 := by simp
  have hwim : ((2 : ℂ) + (T : ℂ) * I).im = T := by simp
  refine ⟨?_, ?_⟩
  · rw [hzre, hwre, Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)]
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> linarith [hstrip.1, hstrip.2]
  · rw [hzim, hwim, Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T)]
    simp only [Set.mem_preimage, Set.mem_Icc]
    rcases abs_le.mp him with ⟨h1, h2⟩
    exact ⟨h1, h2⟩

theorem xiSymmetricMass_eq_support_sum {T : ℝ} (hT : 0 ≤ T) :
    xiSymmetricMass T
      = ∑ ρ ∈ (xiSupportsUpTo_finite T).toFinset, (xiSupportMultiplicity ρ : ℤ) := by
  classical
  set R : Set ℂ := Rectangle (((1 - 2 : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) ((2 : ℂ) + (T : ℂ) * I)
    with hRdef
  set S : Finset XiDivisorSupport := (xiSupportsUpTo_finite T).toFinset with hSdef
  have hinj : Set.InjOn (fun ρ : XiDivisorSupport => (ρ : ℂ)) ↑S :=
    fun a _ b _ h => Subtype.ext h
  have hsupp : Function.support (fun u : ℂ => (MeromorphicOn.divisor xi R u : ℤ))
      ⊆ ↑(S.image (fun ρ : XiDivisorSupport => (ρ : ℂ))) := by
    intro u hu
    rw [Function.mem_support] at hu
    have humem : u ∈ R := by
      by_contra hmem
      exact hu (xi_divisor_apply_of_notMem hmem)
    have hord : analyticOrderAt xi u ≠ 0 := by
      intro h0
      refine hu ?_
      rw [xi_divisor_apply_of_mem humem, h0]
      rfl
    have hzero : xi u = 0 := by
      by_contra hne
      exact hord (analyticOrderAt_eq_zero.mpr (Or.inr hne))
    have hdivne : (MeromorphicOn.divisor xi Set.univ) u ≠ 0 := by
      rw [xi_divisor_apply_of_mem (Set.mem_univ u)]
      intro h
      refine hord ?_
      have : (analyticOrderAt xi u).toNat = 0 := by exact_mod_cast h
      rw [← ENat.coe_toNat (xi_orderAt_ne_top u), this]
      rfl
    have hρ : u ∈ (MeromorphicOn.divisor xi Set.univ).support := Function.mem_support.mpr hdivne
    have him : |u.im| ≤ T := by
      obtain ⟨-, h2⟩ := humem
      have hzim : (((1 - 2 : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).im = -T := by simp
      have hwim : ((2 : ℂ) + (T : ℂ) * I).im = T := by simp
      rw [hzim, hwim, Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T)] at h2
      simp only [Set.mem_preimage, Set.mem_Icc] at h2
      exact abs_le.mpr h2
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨u, hρ⟩, ?_, rfl⟩)
    rw [hSdef, Set.Finite.mem_toFinset]
    exact him
  rw [xiSymmetricMass, xiRegionOrderSum, ← hRdef,
    finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_image (fun a ha b hb h => hinj (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) h)]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  rw [hSdef, Set.Finite.mem_toFinset] at hρ
  rw [xi_divisor_apply_of_mem
    (mem_symmetricRectangle_of_zero hT (xi_eq_zero_of_mem_divisor_support ρ) hρ),
    xiSupportMultiplicity_eq_order]

/-! ## The band count -/

theorem xiSymmetricMass_diff_eq_card {T₁ T₂ : ℝ} (h₁ : 0 ≤ T₁) (h : T₁ ≤ T₂) :
    xiSymmetricMass T₂ - xiSymmetricMass T₁ = ((xiCopiesBand T₁ T₂).card : ℤ) := by
  classical
  have hsub : (xiSupportsUpTo_finite T₁).toFinset ⊆ (xiSupportsUpTo_finite T₂).toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    have h1 : |((ρ : ℂ)).im| ≤ T₁ := hρ
    show |((ρ : ℂ)).im| ≤ T₂
    linarith
  have hband : xiSupportsBand T₁ T₂
      = (xiSupportsUpTo_finite T₂).toFinset \ (xiSupportsUpTo_finite T₁).toFinset := by
    ext ρ
    rw [mem_xiSupportsBand, Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    constructor
    · intro hρ
      exact ⟨hρ.2, by simpa using not_le.mpr hρ.1⟩
    · intro hρ
      exact ⟨not_le.mp (by simpa using hρ.2), hρ.1⟩
  rw [xiSymmetricMass_eq_support_sum (le_trans h₁ h), xiSymmetricMass_eq_support_sum h₁,
    card_xiCopiesBand, hband]
  push_cast
  rw [Finset.sum_sdiff_eq_sub hsub]

end RHTower
