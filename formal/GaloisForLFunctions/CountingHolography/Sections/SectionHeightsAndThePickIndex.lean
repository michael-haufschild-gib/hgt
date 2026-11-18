import GaloisForLFunctions.CountingHolography.Sections.SmallSectionsOnPrimePairs
import GaloisForLFunctions.CountingHolography.TheIntegerProbesAreNotIntegerValued
import GaloisForLFunctions.HeckeKreinToeplitz.BoundedIndexIsClosedUnderPointwiseLimits
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TheRealProbeKernelCountsTheZerosRightOfTheLine
import GaloisForLFunctions.RenormalizedIntersectionTheory.DistinctScalingClassesAreIndependent

/-!
# The negative index read from rational lattice sections

Subtract the dual logarithmic count from the original count and polarize on
pairs of integer atoms. Their mixed Tate limits give the Hermitian spline
matrix at every horizon. The supremum of its negative indices is also the
index measured by the integer Pick tests.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology ArithmeticScatteringHolography HTGeometry
open ArithmeticCastelnuovoSeveri Zeta23 ExclusionOfTheCriticalState
open HeckeKreinToeplitz RenormalizedIntersectionTheory
open BiScaleUncertainty.ChebyshevGauge (cubicSpline)
open SquareRootThreshold (temperedConfig_zetaZeroConfig)

/-- The signed normalized height before taking the limit along a divisor ray. -/
def rayHeight {N : ℕ} (a : Fin N → ℤ) (m : ℕ) : ℝ :=
  ((splineCount (m • a) : ℝ) - dualCount (m • a)) / (m : ℝ)^2

private def sectionAtom {N : ℕ} (i : Fin N) : Fin N → ℤ := Pi.single i 1

/-- Polarization uses two single divisors and their sum, including when the atoms coincide. -/
def mixedRayHeight {N : ℕ} (i j : Fin N) (m : ℕ) : ℝ :=
  (rayHeight (sectionAtom i + sectionAtom j) m -
    rayHeight (sectionAtom i) m - rayHeight (sectionAtom j) m) / 2

theorem mixedRayHeight_tendsto {N : ℕ} (i j : Fin N) :
    Tendsto (mixedRayHeight i j) atTop (𝓝 (atomGram N i j).re) := by
  have h (a : Fin N → ℤ) : Tendsto (rayHeight a) atTop (𝓝 (integerProbe N a)) :=
    splineCount_sub_dualCount_tateLimit a
  have hm : Tendsto (mixedRayHeight i j) atTop
      (𝓝 ((integerProbe N (sectionAtom i + sectionAtom j) - integerProbe N (sectionAtom i) -
        integerProbe N (sectionAtom j)) / 2)) := by
    unfold mixedRayHeight
    exact (((h (sectionAtom i + sectionAtom j)).sub (h (sectionAtom i))).sub
      (h (sectionAtom j))).div_const 2
  have h₁ (k : Fin N) : integerProbe N (sectionAtom k) = (atomGram N k k).re := integerProbe_single N k
  have h₂ : integerProbe N (sectionAtom i + sectionAtom j) =
      (atomGram N i i).re + (atomGram N j j).re + 2*(atomGram N i j).re := integerProbe_pair N i j
  rw [h₂, h₁, h₁] at hm
  have he (x y z : ℝ) : (x + y + 2*z - x - y) / 2 = z := by ring
  rwa [he] at hm

/-- The matrix specified solely by counts of sections on rational lattices. -/
def sectionMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ((limUnder atTop (mixedRayHeight i j) : ℝ) : ℂ)

theorem sectionMatrix_eq_atomGram (N : ℕ) : sectionMatrix N = atomGram N := by
  ext i j : 1
  change ((limUnder atTop (mixedRayHeight i j) : ℝ) : ℂ) = atomGram N i j
  rw [(mixedRayHeight_tendsto i j).limUnder_eq]
  exact Complex.ext rfl (atomGram_im N i j).symm

private theorem gram_natSlope_eq_atomGram (N : ℕ) :
    gram zetaKernel (fun i : Fin N => natSlope i.val) = atomGram N := by
  rw [gram_zetaKernel_eq_weilGram]
  simp only [scale_natSlope, Nat.cast_add_one]
  rfl

/-- Under RH, the critical ordinates separate every nonzero integer spline. -/
theorem integerProbe_pos_of_rh (hRH : RiemannHypothesis) {N : ℕ} {a : Fin N → ℤ} (ha : a ≠ 0) :
    0 < integerProbe N a := by
  have hne : (fun i => (a i : ℂ)) ≠ 0 := by
    intro h
    apply ha
    funext i
    change a i = 0
    have hi : (a i : ℂ) = 0 := congrFun h i
    exact_mod_cast hi
  unfold integerProbe
  rw [← gram_natSlope_eq_atomGram, funext (zetaKernel_eq_onLine_of_riemannHypothesis hRH)]
  exact hermQuad_gram_onLine_natSlope_pos Fin.val_injective hne

theorem eventually_smallSections_of_rh (hRH : RiemannHypothesis) {N : ℕ} {a : Fin N → ℤ}
    (ha : a ≠ 0) : ∀ᶠ m : ℕ in atTop, ∃ z ∈ smallSections (generator (m • a) : ℝ)
      (radius (m • a)), z ≠ 0 := by
  have hl := (tendsto_splineDegree a).eventually_const_lt (integerProbe_pos_of_rh hRH ha)
  filter_upwards [hl, eventually_ge_atTop 1] with m hm hm1
  apply (exists_nonzero_smallSection (by exact_mod_cast contactGenerator_pos _ _ _)).mpr
  have he := (lt_div_iff₀ (by positivity : 0 < (m : ℝ)^2)).mp hm
  linarith only [he]

/-- The linear independence of distinct scaling classes eliminates all
archimedean slack. Cofinal nonzero sections at the original radius suffice. -/
theorem riemannHypothesis_iff_cofinal_smallSections :
    RiemannHypothesis ↔ ∀ (N : ℕ) (a : Fin N → ℤ), a ≠ 0 →
      ∃ᶠ m : ℕ in atTop, ∃ z ∈ smallSections (generator (m • a) : ℝ)
        (radius (m • a)), z ≠ 0 := by
  constructor
  · exact fun h _ _ ha => (eventually_smallSections_of_rh h ha).frequently
  · intro h
    apply riemannHypothesis_iff_integerProbes.mpr
    intro N a
    by_contra! hq
    have ha : a ≠ 0 := by
      rintro rfl
      have h0 : integerProbe N 0 = 0 := by simpa using integerProbe_smul N 0 (0 : Fin N → ℤ)
      linarith
    have he := (tendsto_splineDegree a).eventually_lt_const hq
    obtain ⟨m,hm,he'⟩ := ((h N a ha).and_eventually he).exists
    have hl := (exists_nonzero_smallSection (by exact_mod_cast contactGenerator_pos _ _ _)).mp hm
    exact (not_lt_of_ge (div_nonneg (sub_nonneg.mpr hl) (sq_nonneg _))) he'

/-- The actual integral modulus fits inside the unmodified radius on
cofinally many multiples of every effective prime pair exactly under RH. -/
theorem riemannHypothesis_iff_prime_modulus_fits :
    RiemannHypothesis ↔ ∀ p : ℕ, p.Prime → ∃ᶠ m : ℕ in atTop,
      Real.log (contactModulus (m • primePair p)) ≤ radius (m • primePair p) := by
  constructor
  · intro h p _
    have ha : primePair p ≠ 0 := by
      intro hz
      have he := congrFun hz 0
      simp only [primePair, Pi.add_apply, Pi.single_apply, Pi.zero_apply, if_true] at he
      split_ifs at he <;> omega
    apply ((eventually_smallSections_of_rh h ha).mono fun m hm => ?_).frequently
    have hp (i : Fin (p+1)) : 0 ≤ (m • primePair p) i := by
      simp only [primePair, Pi.smul_apply, Pi.add_apply, nsmul_eq_mul, Pi.single_apply]
      split_ifs <;> positivity
    have he : (generator (m • primePair p) : ℝ) = contactModulus (m • primePair p) := by
      exact_mod_cast generator_eq_contactModulus _ hp
    rw [← he]
    exact (exists_nonzero_smallSection (by exact_mod_cast contactGenerator_pos _ _ _)).mp hm
  · intro h
    exact riemannHypothesis_iff_prime_modulus_bound.mpr ⟨0, fun p hp => by simpa using h p hp⟩

/-- The matrix at finite multiplicity, before taking a Tate limit. -/
def finiteSectionMatrix (N m : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (mixedRayHeight i j m : ℂ)

theorem finiteSectionMatrix_isHermitian (N m : ℕ) : (finiteSectionMatrix N m).IsHermitian := by
  ext i j : 1
  change (starRingEnd ℂ) ((mixedRayHeight j i m : ℝ) : ℂ) = (mixedRayHeight i j m : ℂ)
  rw [Complex.conj_ofReal]
  congr 1
  unfold mixedRayHeight
  rw [add_comm (sectionAtom j) (sectionAtom i)]
  ring

private theorem finiteSectionMatrix_tendsto {N : ℕ} (i j : Fin N) :
    Tendsto (fun m => finiteSectionMatrix N m i j) atTop (𝓝 (atomGram N i j)) := by
  have he : ((atomGram N i j).re : ℂ) = atomGram N i j :=
    Complex.ext rfl (atomGram_im N i j).symm
  rw [← he]
  exact (Complex.continuous_ofReal.tendsto _).comp (mixedRayHeight_tendsto i j)

/-- Each strictly negative direction persists at sufficiently large finite
multiplicity. No sign or nonsingularity condition is imposed on the nullspace. -/
theorem eventually_le_finiteSectionIndex (N : ℕ) :
    ∀ᶠ m : ℕ in atTop, hermNegIndex (sectionMatrix N) ≤ hermNegIndex (finiteSectionMatrix N m) := by
  rw [sectionMatrix_eq_atomGram]
  exact eventually_le_hermNegIndex (atomGram_isHermitian N) finiteSectionMatrix_tendsto

/-- Under RH, independence on the critical line makes the limiting matrix
strictly positive. Every finite section matrix then has zero negative index
at all sufficiently high multiplicities. -/
theorem eventually_finiteSectionIndex_zero_of_rh (hRH : RiemannHypothesis) (N : ℕ) :
    ∀ᶠ m : ℕ in atTop, hermNegIndex (finiteSectionMatrix N m) = 0 := by
  classical
  have hr : hermPosIndex (atomGram N) = Fintype.card (Fin N) := by
    rw [← gram_natSlope_eq_atomGram]
    exact hermPosIndex_gram_zetaKernel_natSlope_of_riemannHypothesis hRH Fin.val_injective
  have h := eventually_le_hermNegIndex (H := fun m => -finiteSectionMatrix N m)
    (atomGram_isHermitian N).neg (fun i j => (finiteSectionMatrix_tendsto i j).neg)
  simp only [hermNegIndex, neg_neg, hr] at h
  filter_upwards [h] with m hm
  have hF := finiteSectionMatrix_isHermitian N m
  rw [posIndex_eq_card_pos_eigenvalues hF] at hm
  have he : Finset.univ.filter (fun i => 0 < hF.eigenvalues i) = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by simpa only [Finset.card_univ] using hm)
  have hpos (i : Fin N) : 0 < hF.eigenvalues i :=
    (Finset.mem_filter.mp (show i ∈ Finset.univ.filter (fun j => 0 < hF.eigenvalues j) by
      rw [he]; exact Finset.mem_univ _)).2
  rw [negIndex_eq_card_neg_eigenvalues hF]
  simp [fun i => (hpos i).not_gt]

/-- Distinct right zeros, with infinite cardinality allowed, are exactly the
supremal negative index recovered by polarizing the two section counts. -/
theorem rightZeros_encard_eq_sectionIndex :
    (rightZeros zetaZeroConfig).encard = ⨆ N : ℕ, (hermNegIndex (sectionMatrix N) : ℕ∞) := by
  simp only [sectionMatrix_eq_atomGram]
  exact HeckeKreinToeplitz.negIndex_zetaKernel_eq_iSup_integerAtoms

/-- An integer Pick witness of index at least `r` exists exactly up to the
index of the polarized section heights. The two Gram matrices have different entries. -/
theorem integerPick_iff_le_sectionIndex (r : ℕ) :
    (∃ (N : ℕ) (p : Fin N → ℕ), (∀ i, 2 ≤ p i) ∧ r ≤ hermNegIndex (integerPickMatrix p)) ↔
      (r : ℕ∞) ≤ ⨆ N : ℕ, (hermNegIndex (sectionMatrix N) : ℕ∞) := by
  rw [← rightZeros_encard_eq_sectionIndex]
  exact integerProbeIndex_law r

/-- Outside RH one fixed horizon has at least two negative squares at every
sufficiently large finite multiplicity. Thus a cofinal ceiling of one at each
horizon would settle the sign, even without matching indices on null modes. -/
theorem rh_or_eventually_two_finiteSectionIndex :
    RiemannHypothesis ∨ ∃ N : ℕ, ∀ᶠ m : ℕ in atTop, 2 ≤ hermNegIndex (finiteSectionMatrix N m) := by
  by_cases h : RiemannHypothesis
  · exact Or.inl h
  right
  have htwo : (2 : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard := two_le_rightZeros_encard_of_not_RH h
  have hN : ∃ N : ℕ, 2 ≤ hermNegIndex (sectionMatrix N) := by
    by_contra! hn
    have hle : (rightZeros zetaZeroConfig).encard ≤ 1 := by
      rw [rightZeros_encard_eq_sectionIndex]
      apply iSup_le
      intro N
      exact_mod_cast (show hermNegIndex (sectionMatrix N) ≤ 1 by have := hn N; omega)
    exact (by norm_num : ¬ (2 : ℕ∞) ≤ 1) (htwo.trans hle)
  obtain ⟨N, hN⟩ := hN
  exact ⟨N, (eventually_le_finiteSectionIndex N).mono fun _ hm => hN.trans hm⟩

/-- A cofinal ceiling of one negative square on each finite horizon is
necessary and sufficient. All entries here are computed from section counts
before their Tate limits. -/
theorem riemannHypothesis_iff_cofinal_finiteSectionIndex :
    RiemannHypothesis ↔ ∀ N : ℕ, ∃ᶠ m : ℕ in atTop, hermNegIndex (finiteSectionMatrix N m) ≤ 1 := by
  constructor
  · exact fun h N => ((eventually_finiteSectionIndex_zero_of_rh h N).mono fun m hm => by omega).frequently
  · intro h
    rcases rh_or_eventually_two_finiteSectionIndex with hRH | ⟨N,hN⟩
    · exact hRH
    · obtain ⟨m,hm,hm'⟩ := ((h N).and_eventually hN).exists
      omega

/-- With finitely many right zeros, imposing one evaluation per reflected
pair leaves the strictly positive critical Gram. -/
private theorem dim_le_positiveIndex_add_rightCount (N : ℕ) (hf : (rightZeros zetaZeroConfig).Finite) :
    N ≤ hermPosIndex (atomGram N) + hf.toFinset.card := by
  classical
  let R := hf.toFinset
  let x (i : Fin N) := natSlope i.val
  let χ (ρ : ℂ) := zeroChar (starRingEnd ℂ ρ)
  let ω (ρ : ℂ) := starRingEnd ℂ (zetaZeroConfig.Wsummand
    (ArithmeticCastelnuovoSeveri.cx cubicSpline) (ArithmeticCastelnuovoSeveri.cx cubicSpline) ρ)
  let T : (Fin N → ℂ) →ₗ[ℂ] (R → ℂ) := LinearMap.pi (fun ρ : R => charEval (χ ρ) x)
  have hpos : IsPosDefOn (atomGram N) (LinearMap.ker T) := by
    intro c hc hc0
    have hz : zetaKernel = fun u => orbitKernel zetaOnLine cubicSpline u +
        ∑ ρ ∈ R, pairKernel (χ ρ) (ω ρ) u :=
      funext (orbitKernel_eq_onLine_add_pairs temperedConfig_zetaZeroConfig cubicSpline_mem_realTests hf)
    rw [← gram_natSlope_eq_atomGram, hz, hermQuad_gram_add, hermQuad_gram_sum]
    have hterm (ρ : ℂ) (hρ : ρ ∈ R) : hermQuad (gram (pairKernel (χ ρ) (ω ρ)) x) c = 0 := by
      have he : charEval (χ ρ) x c = 0 := congrFun (LinearMap.mem_ker.mp hc) (⟨ρ,hρ⟩ : R)
      rw [hermQuad_gram_pairKernel, he]
      simp
    rw [Finset.sum_eq_zero hterm, add_zero]
    exact hermQuad_gram_onLine_natSlope_pos Fin.val_injective hc0
  have hk : Module.finrank ℂ (LinearMap.ker T) ≤ hermPosIndex (atomGram N) :=
    le_csSup (posIndexSet_bddAbove _) ⟨_,rfl,hpos⟩
  have hr := Submodule.finrank_le (LinearMap.range T)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hr
  have hd := LinearMap.finrank_range_add_finrank_ker T
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hd
  change N ≤ _ + R.card
  omega

/-- Null modes of a finite limiting matrix cannot create more negative
squares than there are distinct right zeros. -/
theorem eventually_finiteSectionIndex_le_rightCount (N : ℕ) (hf : (rightZeros zetaZeroConfig).Finite) :
    ∀ᶠ m : ℕ in atTop, hermNegIndex (finiteSectionMatrix N m) ≤ hf.toFinset.card := by
  have hl := eventually_le_hermNegIndex (H := fun m => -finiteSectionMatrix N m)
    (atomGram_isHermitian N).neg (fun i j => (finiteSectionMatrix_tendsto i j).neg)
  simp only [hermNegIndex, neg_neg] at hl
  have hd := dim_le_positiveIndex_add_rightCount N hf
  filter_upwards [hl] with m hm
  have hi := posIndex_add_negIndex_add_nullIndex (finiteSectionMatrix_isHermitian N m)
  rw [Fintype.card_fin] at hi
  omega

/-- Cofinal index ceilings on the actual finite matrices recover the
entire zero count, including every finite nonzero stratum. -/
theorem rightCount_le_iff_cofinal_finiteSectionIndex (r : ℕ) :
    (rightZeros zetaZeroConfig).encard ≤ (r : ℕ∞) ↔
      ∀ N : ℕ, ∃ᶠ m : ℕ in atTop, hermNegIndex (finiteSectionMatrix N m) ≤ r := by
  constructor
  · intro he N
    have hf := Set.encard_lt_top_iff.mp (he.trans_lt (by simp : (r : ℕ∞) < ⊤))
    have hcard : hf.toFinset.card ≤ r := by
      rw [hf.encard_eq_coe_toFinset_card] at he
      exact_mod_cast he
    exact ((eventually_finiteSectionIndex_le_rightCount N hf).mono fun m hm => hm.trans hcard).frequently
  · intro h
    rw [rightZeros_encard_eq_sectionIndex]
    apply iSup_le
    intro N
    obtain ⟨m,hm,hm'⟩ := ((h N).and_eventually (eventually_le_finiteSectionIndex N)).exists
    exact_mod_cast hm'.trans hm

/-- Any uniform finite ceiling on the section indices already implies
Lindelöf on the critical line. -/
theorem lindelof_of_cofinal_finiteSectionIndex {r : ℕ}
    (h : ∀ N : ℕ, ∃ᶠ m : ℕ in atTop, hermNegIndex (finiteSectionMatrix N m) ≤ r) :
    _root_.RHTower.LindelofSparse.LindelofCriticalLine := by
  apply lindelof_of_negIndex_zetaKernel_lt_top
  rw [negIndex_zetaKernel]
  exact ((rightCount_le_iff_cofinal_finiteSectionIndex r).mpr h).trans_lt (by simp)

#print axioms rightCount_le_iff_cofinal_finiteSectionIndex
#print axioms lindelof_of_cofinal_finiteSectionIndex
#print axioms riemannHypothesis_iff_cofinal_smallSections
#print axioms riemannHypothesis_iff_prime_modulus_fits
#print axioms riemannHypothesis_iff_cofinal_finiteSectionIndex
#print axioms integerPick_iff_le_sectionIndex
#print axioms rh_or_eventually_two_finiteSectionIndex

end GaloisForLFunctions.CountingHolography.Sections
