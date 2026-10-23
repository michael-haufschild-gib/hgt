import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectCountsTheRightZeros
import GaloisForLFunctions.RHTower.EvenLandauPairTest
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionUnrestricted

/-!
# The reflection sectors of the Hodge defect

The reflection `u ↦ −u` of tests (`testNeg`) acts on transforms by `h(z) ↦ h(−z)` and on ordinates
by `γ_ρ ↦ γ_{1−ρ}`. On a configuration symmetric under the functional equation `ρ ↦ 1 − ρ`
(`FESymmetric`) the Weil form splits into the **even** and the **odd** sector
(`testNeg f = f`, resp. `testNeg f = −f`), and the Pontryagin law splits with it
(`sector_pontryagin_law`):

    even defect = #{Re ρ > ½, Im ρ > 0},     odd defect = #{Re ρ > ½, Im ρ ≥ 0}.

* **Upper bound** (`negIndex_sector_le`). For a test of parity `s` the transform satisfies
  `h(−z) = s h(z)`. The conjugate zero `ρ̄` has `γ_{ρ̄} = −conj γ_ρ`, so vanishing at the zeros
  right of the line in the upper half plane kills the pair terms of the lower half plane; at a real
  zero right of the line the pair term is `s m_ρ |h(γ_ρ)|²` (`re_Wsummand_nonneg_of_sector`).
  Real off-line zeros are invisible to even tests.
* **Attainment.** On `ℓ²(Z)` the involution `τ ↦ 1 − τ` (`fesVec`) is the image of `testNeg`
  (`zeroMap_testNeg`) and sends the negative vector `e_ρ − e_{1−ρ̄}` of the pair of `ρ` to minus
  that of `ρ̄`. The vectors `w_ρ = n_ρ − s n_{ρ̄}` are `s`-symmetric, Krein-orthogonal, with
  squares `−4` (`−8` at real zeros); symmetrised approximants by tests have a Gram matrix near a
  negative diagonal.

For `ζ`, which has no real zeros (`zetaZeroConfig_im_ne_zero'`), both sectors carry exactly half
of the Hodge defect (`zeta_even_hodgeDefect_iff`, `zeta_odd_hodgeDefect_iff`): each conjugate pair
of zeros right of the line gives one even and one odd negative square.
-/

open Complex Matrix Finset
open scoped ComplexConjugate lp
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### Reflection of tests -/

/-- The reflected test `u ↦ f(−u)`. -/
def testNeg (f : ℝ → ℂ) : ℝ → ℂ := fun u => f (-u)

theorem paperFT_testNeg (f : ℝ → ℂ) (z : ℂ) : paperFT (testNeg f) z = paperFT f (-z) := by
  unfold paperFT testNeg
  rw [← MeasureTheory.integral_neg_eq_self (fun u : ℝ => f u * cexp (I * -z * u))]
  congr 1
  funext u
  congr 2
  push_cast
  ring

theorem testNeg_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (testNeg f) :=
  hf.comp contDiff_neg

theorem testNeg_hasCompactSupport {f : ℝ → ℂ} (hfc : HasCompactSupport f) :
    HasCompactSupport (testNeg f) :=
  hfc.comp_homeomorph (Homeomorph.neg ℝ)

theorem gammaOf_one_sub_eq (τ : ℂ) : gammaOf (1 - τ) = -gammaOf τ := by
  unfold gammaOf
  ring

theorem gammaOf_conj_eq (σ : ℂ) : gammaOf (conj σ) = -conj (gammaOf σ) := by
  simp only [gammaOf, map_div₀, map_sub, Complex.conj_I, map_one, map_ofNat]
  ring

/-! ### Configurations symmetric under the functional equation -/

/-- A configuration symmetric under `ρ ↦ 1 − ρ` with equal multiplicities. -/
def FESymmetric (Z : ZeroConfig) : Prop :=
  ∀ ρ ∈ Z.carrier, 1 - ρ ∈ Z.carrier ∧ Z.mult (1 - ρ) = Z.mult ρ

theorem FESymmetric.conj_mem {Z : ZeroConfig} (hFE : FESymmetric Z) {ρ : ℂ}
    (hρ : ρ ∈ Z.carrier) : conj ρ ∈ Z.carrier := by
  have h := Z.reflect_mem _ (hFE ρ hρ).1
  have e : reflect (1 - ρ) = conj ρ := by simp [reflect]
  rwa [e] at h

/-- The zeros right of the line seen by the sector of parity `s`: the upper half plane, and for
odd tests also the real axis. -/
def sectorZeros (Z : ZeroConfig) (s : ℂ) : Set ℂ :=
  {σ | σ ∈ rightZeros Z ∧ (0 < σ.im ∨ (s = -1 ∧ σ.im = 0))}

/-- **Sector positivity at the zeros.** If `h_F(−z) = s h_F(z)` with `s = ±1` and `h_F` vanishes
at the zeros of the sector, every Weil summand of `F` has nonnegative real part. -/
theorem re_Wsummand_nonneg_of_sector (Z : ZeroConfig) (hFE : FESymmetric Z) {F : ℝ → ℂ}
    {s : ℂ} (hs : s = 1 ∨ s = -1) (hF : ∀ z, paperFT F (-z) = s * paperFT F z)
    (hvan : ∀ σ ∈ sectorZeros Z s, paperFT F (gammaOf σ) = 0) (τ : Z.carrier) :
    0 ≤ (Z.Wsummand F F τ).re := by
  have hright : ∀ σ ∈ Z.carrier, 1 / 2 < σ.re → 0 ≤ (Z.Wsummand F F σ).re := by
    intro σ hσ hre
    rcases lt_trichotomy σ.im 0 with him | him | him
    · -- the conjugate zero lies in the upper half plane
      have hc : conj σ ∈ sectorZeros Z s :=
        ⟨⟨hFE.conj_mem hσ, by rw [Complex.conj_re]; exact hre⟩,
          Or.inl (by rw [Complex.conj_im]; linarith)⟩
      have h0 := hvan _ hc
      have hz : paperFT F (conj (gammaOf σ)) = 0 := by
        have e : conj (gammaOf σ) = -gammaOf (conj σ) := by rw [gammaOf_conj_eq, neg_neg]
        rw [e, hF, h0, mul_zero]
      simp [ZeroConfig.Wsummand, hz]
    · -- a real zero: `conj γ = −γ`
      have hσr : conj σ = σ := Complex.conj_eq_iff_im.mpr him
      have hγ : conj (gammaOf σ) = -gammaOf σ := by
        have e := gammaOf_conj_eq σ
        rw [hσr] at e
        linear_combination e
      rcases hs with rfl | rfl
      · rw [ZeroConfig.Wsummand, hγ, hF, one_mul, mul_assoc, Complex.mul_conj,
          ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
        exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
      · have h0 := hvan σ ⟨⟨hσ, hre⟩, Or.inr ⟨rfl, him⟩⟩
        simp [ZeroConfig.Wsummand, h0]
    · have h0 := hvan σ ⟨⟨hσ, hre⟩, Or.inl him⟩
      simp [ZeroConfig.Wsummand, h0]
  rcases lt_trichotomy (τ : ℂ).re (1 / 2) with hlt | heq | hgt
  · -- left of the line: the conjugate of the reflected summand
    have hr := Z.reflect_mem _ τ.2
    have hre : 1 / 2 < (reflect (τ : ℂ)).re := by
      simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    have h1 := Wsummand_reflect Z F hr
    have hrr : reflect (reflect (τ : ℂ)) = τ := by simp [reflect]
    rw [hrr] at h1
    rw [h1, Complex.conj_re]
    exact hright _ hr hre
  · -- on the line
    have hγ : conj (gammaOf (τ : ℂ)) = gammaOf τ := Complex.conj_eq_iff_im.mpr (by
      simp [gammaOf, heq])
    rw [ZeroConfig.Wsummand, hγ, mul_assoc, Complex.mul_conj, ← Complex.ofReal_natCast,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
  · exact hright _ τ.2 hgt

/-- **Sector upper bound.** On tests of parity `s` the Weil form has at most as many negative
squares as the sector has zeros. -/
theorem negIndex_sector_le (Z : ZeroConfig) (hZ : TemperedConfig Z) (hFE : FESymmetric Z)
    {s : ℂ} (hs : s = 1 ∨ s = -1) {ι : Type*} [Fintype ι] (f : ι → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfc : ∀ i, HasCompactSupport (f i))
    (hsym : ∀ i, testNeg (f i) = s • f i) :
    (hermNegIndex (zeroGram Z f) : ℕ∞) ≤ (sectorZeros Z s).encard := by
  rcases (sectorZeros Z s).finite_or_infinite with hS | hS
  · haveI := hS.fintype
    rw [hS.encard_eq_coe_toFinset_card, Set.Finite.card_toFinset]
    refine ENat.coe_le_coe.mpr (negIndex_le_card_of_nonneg_on_ker _
      (fun σ : sectorZeros Z s => evalFunctional f (gammaOf σ)) fun x hx => ?_)
    have hcont := fun i => (hf i).continuous
    have hFv : ∀ σ ∈ sectorZeros Z s, paperFT (∑ i, conj (x i) • f i) (gammaOf σ) = 0 := by
      intro σ hσ
      have := hx ⟨σ, hσ⟩
      rw [evalFunctional_eq f hcont hfc] at this
      simpa using this
    have hFs : ∀ z, paperFT (∑ i, conj (x i) • f i) (-z) =
        s * paperFT (∑ i, conj (x i) • f i) z := by
      intro z
      rw [paperFT_sum_smul f hcont hfc, paperFT_sum_smul f hcont hfc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← paperFT_testNeg, hsym i, paperFT_smul]
      ring
    have hFd := contDiff_sum_smul f hf fun i => conj (x i)
    have hFc := hasCompactSupport_sum_smul f hfc fun i => conj (x i)
    rw [hermQuad_zeroGram_of_tempered Z hZ f hf hfc, ZeroConfig.W,
      Complex.re_tsum (summable_Wsummand Z hZ hFd hFc hFd hFc)]
    exact tsum_nonneg fun τ => re_Wsummand_nonneg_of_sector Z hFE hs hFs hFv τ
  · rw [hS.encard_eq]
    exact le_top

/-! ### The functional-equation involution on `ℓ²(Z)` -/

section Involution

variable {Z : ZeroConfig} (hFE : FESymmetric Z)

/-- The involution `τ ↦ 1 − τ` of a symmetric carrier. -/
def fesCarrier (τ : Z.carrier) : Z.carrier := ⟨1 - τ, (hFE τ τ.2).1⟩

theorem fesCarrier_fesCarrier (τ : Z.carrier) : fesCarrier hFE (fesCarrier hFE τ) = τ :=
  Subtype.ext (by simp [fesCarrier])

/-- The involution as a permutation. -/
def fesEquiv : Z.carrier ≃ Z.carrier :=
  ⟨fesCarrier hFE, fesCarrier hFE, fesCarrier_fesCarrier hFE, fesCarrier_fesCarrier hFE⟩

theorem fesEquiv_apply (τ : Z.carrier) : fesEquiv hFE τ = fesCarrier hFE τ := rfl

theorem memℓp_fes (x : ℓ²(Z.carrier, ℂ)) : Memℓp (fun τ => x (fesCarrier hFE τ)) 2 := by
  refine (memℓp_gen_iff (by norm_num)).mpr ?_
  exact (fesEquiv hFE).summable_iff.mpr ((lp.memℓp x).summable (by norm_num))

/-- The involution of the coordinates. -/
def fesVec (x : ℓ²(Z.carrier, ℂ)) : ℓ²(Z.carrier, ℂ) :=
  ⟨fun τ => x (fesCarrier hFE τ), memℓp_fes hFE x⟩

theorem fesVec_apply (x : ℓ²(Z.carrier, ℂ)) (τ : Z.carrier) :
    fesVec hFE x τ = x (fesCarrier hFE τ) := rfl

theorem fesVec_add (x y : ℓ²(Z.carrier, ℂ)) : fesVec hFE (x + y) = fesVec hFE x + fesVec hFE y := by
  ext τ
  simp only [fesVec_apply, lp.coeFn_add, Pi.add_apply]

theorem fesVec_sub (x y : ℓ²(Z.carrier, ℂ)) : fesVec hFE (x - y) = fesVec hFE x - fesVec hFE y := by
  ext τ
  simp only [fesVec_apply, lp.coeFn_sub, Pi.sub_apply]

theorem fesVec_smul (c : ℂ) (x : ℓ²(Z.carrier, ℂ)) : fesVec hFE (c • x) = c • fesVec hFE x := by
  ext τ
  simp only [fesVec_apply, lp.coeFn_smul, Pi.smul_apply]

theorem norm_fesVec (x : ℓ²(Z.carrier, ℂ)) : ‖fesVec hFE x‖ = ‖x‖ := by
  have h2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have h := lp.norm_rpow_eq_tsum h2 (fesVec hFE x)
  have hx := lp.norm_rpow_eq_tsum h2 x
  simp only [fesVec_apply] at h
  have ht := (fesEquiv hFE).tsum_eq (fun τ => ‖x τ‖ ^ (2 : ENNReal).toReal)
  simp only [fesEquiv_apply] at ht
  rw [ht, ← hx] at h
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [← Real.sqrt_sq (norm_nonneg (fesVec hFE x)), h, Real.sqrt_sq (norm_nonneg x)]

theorem fesVec_single [DecidableEq Z.carrier] (a : Z.carrier) :
    fesVec hFE (lp.single 2 a (1 : ℂ)) = lp.single 2 (fesCarrier hFE a) 1 := by
  ext τ
  simp only [fesVec_apply, lp.single_apply, Pi.single_apply]
  by_cases h : τ = fesCarrier hFE a
  · subst h
    simp [fesCarrier_fesCarrier]
  · have h' : fesCarrier hFE τ ≠ a := fun h'' => h (by rw [← h'', fesCarrier_fesCarrier])
    simp [h, h']

/-- The test reflection `u ↦ −u` is the involution `τ ↦ 1 − τ` of the coordinates. -/
theorem zeroMap_testNeg (hZ : TemperedConfig Z) (g : testSpace) :
    zeroMap Z hZ ⟨testNeg g, testNeg_contDiff g.2.1, testNeg_hasCompactSupport g.2.2⟩ =
      fesVec hFE (zeroMap Z hZ g) := by
  ext τ
  rw [zeroMap_apply, fesVec_apply, zeroMap_apply]
  simp only [zeroCoord, fesCarrier, paperFT_testNeg, gammaOf_one_sub_eq, (hFE τ τ.2).2]

end Involution

theorem reflectVec_smul (Z : ZeroConfig) (c : ℂ) (x : ℓ²(Z.carrier, ℂ)) :
    reflectVec Z (c • x) = c • reflectVec Z x := by
  ext τ
  simp only [reflectVec_apply, lp.coeFn_smul, Pi.smul_apply]

/-! ### The sector targets -/

section Targets

variable {Z : ZeroConfig} (hFE : FESymmetric Z) [DecidableEq Z.carrier]

/-- The conjugate zero, as a point of the carrier. -/
def conjCarrier (a : Z.carrier) : Z.carrier := ⟨conj (a : ℂ), hFE.conj_mem a.2⟩

/-- The negative vector `e_ρ − e_{1−ρ̄}` of the pair of `ρ`. -/
def negVec (a : Z.carrier) : ℓ²(Z.carrier, ℂ) :=
  lp.single 2 a (1 : ℂ) - lp.single 2 (reflectCarrier Z a) 1

theorem norm_negVec_le (a : Z.carrier) : ‖negVec a‖ ≤ 2 := by
  refine (norm_sub_le _ _).trans ?_
  rw [lp.norm_single (by norm_num), lp.norm_single (by norm_num), norm_one]
  norm_num

omit [DecidableEq Z.carrier] in
theorem reflectCarrier_ne_of_right {a b : Z.carrier} (ha : 1 / 2 < (a : ℂ).re)
    (hb : 1 / 2 < (b : ℂ).re) : reflectCarrier Z b ≠ a := fun h => by
  have := congrArg (fun t : Z.carrier => (t : ℂ).re) h
  simp only [reflectCarrier, reflect, Complex.sub_re, Complex.one_re, Complex.conj_re] at this
  linarith

/-- **The Krein products of the negative vectors** of zeros right of the line. -/
theorem inner_reflectVec_negVec {a b : Z.carrier} (ha : 1 / 2 < (a : ℂ).re)
    (hb : 1 / 2 < (b : ℂ).re) :
    inner ℂ (reflectVec Z (negVec b)) (negVec a) = if a = b then -2 else 0 := by
  have hRR : reflectCarrier Z b = reflectCarrier Z a ↔ a = b :=
    ⟨fun h => ((reflectEquiv Z).injective h).symm, fun h => h ▸ rfl⟩
  have hba : b = a ↔ a = b := eq_comm
  simp only [negVec, reflectVec_sub, reflectVec_single, reflectCarrier_reflectCarrier,
    inner_sub_left, inner_sub_right, inner_single_single,
    if_neg (reflectCarrier_ne_of_right ha hb), if_neg (Ne.symm (reflectCarrier_ne_of_right hb ha)),
    hRR, hba]
  split_ifs <;> ring

/-- The involution sends the negative vector of `ρ` to minus that of `ρ̄`. -/
theorem fesVec_negVec (a : Z.carrier) : fesVec hFE (negVec a) = -negVec (conjCarrier hFE a) := by
  have h1 : fesCarrier hFE a = reflectCarrier Z (conjCarrier hFE a) :=
    Subtype.ext (by simp [fesCarrier, reflectCarrier, conjCarrier, reflect])
  have h2 : fesCarrier hFE (reflectCarrier Z a) = conjCarrier hFE a :=
    Subtype.ext (by simp [fesCarrier, reflectCarrier, conjCarrier, reflect])
  rw [negVec, fesVec_sub, fesVec_single, fesVec_single, h1, h2, negVec, neg_sub]

/-- The sector target `w_ρ = n_ρ − s n_{ρ̄}`. -/
def sectorVec (s : ℂ) (a : Z.carrier) : ℓ²(Z.carrier, ℂ) :=
  negVec a - s • negVec (conjCarrier hFE a)

omit [DecidableEq Z.carrier] in
theorem conjCarrier_conjCarrier (a : Z.carrier) : conjCarrier hFE (conjCarrier hFE a) = a :=
  Subtype.ext (by simp [conjCarrier])

theorem fesVec_sectorVec {s : ℂ} (hs : s = 1 ∨ s = -1) (a : Z.carrier) :
    fesVec hFE (sectorVec hFE s a) = s • sectorVec hFE s a := by
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  rw [sectorVec, fesVec_sub, fesVec_smul, fesVec_negVec, fesVec_negVec, conjCarrier_conjCarrier,
    smul_sub, smul_neg, smul_smul, hss, one_smul]
  abel

theorem norm_sectorVec_le {s : ℂ} (hs : s = 1 ∨ s = -1) (a : Z.carrier) :
    ‖sectorVec hFE s a‖ ≤ 4 := by
  have h1 : ‖s‖ = 1 := by rcases hs with rfl | rfl <;> simp
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, h1, one_mul]
  linarith [norm_negVec_le a, norm_negVec_le (conjCarrier hFE a)]

/-- **The sector targets are Krein-orthogonal with negative squares**: for zeros of the sector,
`⟨R w_b, w_a⟩ = −4 + 4s[ā = a]` if `a = b`, and `0` otherwise. -/
theorem inner_reflectVec_sectorVec {s : ℂ} (hs : s = 1 ∨ s = -1) {a b : Z.carrier}
    (ha : (a : ℂ) ∈ sectorZeros Z s) (hb : (b : ℂ) ∈ sectorZeros Z s) :
    inner ℂ (reflectVec Z (sectorVec hFE s b)) (sectorVec hFE s a) =
      if a = b then -4 + 4 * s * (if conjCarrier hFE a = a then 1 else 0) else 0 := by
  have hsc : conj s = s := by rcases hs with rfl | rfl <;> simp
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hreA : 1 / 2 < (a : ℂ).re := ha.1.2
  have hreB : 1 / 2 < (b : ℂ).re := hb.1.2
  have hreA' : 1 / 2 < ((conjCarrier hFE a : Z.carrier) : ℂ).re := by
    simpa [conjCarrier] using hreA
  have hreB' : 1 / 2 < ((conjCarrier hFE b : Z.carrier) : ℂ).re := by
    simpa [conjCarrier] using hreB
  -- `ā = b` (or `a = b̄`) inside the sector forces `a = b` real
  have himA : 0 ≤ (a : ℂ).im := by
    rcases ha.2 with h | ⟨_, h⟩ <;> linarith
  have himB : 0 ≤ (b : ℂ).im := by
    rcases hb.2 with h | ⟨_, h⟩ <;> linarith
  have hconj1 : conjCarrier hFE a = b ↔ (a = b ∧ conjCarrier hFE a = a) := by
    constructor
    · intro h
      have him := congrArg (fun t : Z.carrier => (t : ℂ).im) h
      simp only [conjCarrier, Complex.conj_im] at him
      have h0 : (a : ℂ).im = 0 := by linarith
      have hreal : conjCarrier hFE a = a :=
        Subtype.ext (by simp [conjCarrier, Complex.conj_eq_iff_im.mpr h0])
      exact ⟨hreal.symm.trans h, hreal⟩
    · rintro ⟨rfl, h⟩; exact h
  have hconj2 : a = conjCarrier hFE b ↔ (a = b ∧ conjCarrier hFE a = a) := by
    constructor
    · intro h
      have h' : conjCarrier hFE a = b := by rw [h, conjCarrier_conjCarrier]
      exact hconj1.mp h'
    · rintro ⟨rfl, h⟩; exact h.symm
  have hconj3 : conjCarrier hFE a = conjCarrier hFE b ↔ a = b := by
    constructor
    · intro h
      have := congrArg (conjCarrier hFE) h
      rwa [conjCarrier_conjCarrier, conjCarrier_conjCarrier] at this
    · rintro rfl; rfl
  simp only [sectorVec, reflectVec_sub, reflectVec_smul, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, inner_reflectVec_negVec hreA hreB,
    inner_reflectVec_negVec hreA hreB', inner_reflectVec_negVec hreA' hreB,
    inner_reflectVec_negVec hreA' hreB', hconj1, hconj2, hconj3, hsc]
  by_cases hab : a = b
  · subst hab
    by_cases hr : conjCarrier hFE a = a
    · simp only [hr, and_self, if_true]
      linear_combination (-2 : ℂ) * hss
    · simp only [hr, and_false, if_false, if_true]
      linear_combination (-2 : ℂ) * hss
  · simp [hab]

end Targets

/-! ### Attainment in a sector -/

/-- A Gram matrix within `η` of a diagonal with entries `≤ −2`, with `η · n ≤ 1`, has form
`≤ −|x|²`. -/
theorem hermQuad_le_of_near_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ)
    (d : ι → ℝ) (hd : ∀ i, d i ≤ -2) {η : ℝ} (hη : η * Fintype.card ι ≤ 1)
    (hG : ∀ i j, ‖G i j - (if i = j then (d i : ℂ) else 0)‖ ≤ η) (x : ι → ℂ) :
    hermQuad G x ≤ -∑ i, ‖x i‖ ^ 2 := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · simp [hermQuad, dotProduct]
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hG i₀ i₀)
  set D : Matrix ι ι ℂ := diagonal fun i => (d i : ℂ) with hD
  set E : Matrix ι ι ℂ := G - D with hE
  have hsplit : hermQuad G x = hermQuad D x + hermQuad E x := by
    have hGDE : G = D + E := by rw [hE]; abel
    rw [hGDE]
    simp only [hermQuad, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  have hDx : hermQuad D x ≤ -2 * ∑ i, ‖x i‖ ^ 2 := by
    rw [hD, hermQuad_diagonal, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      rw [Complex.normSq_eq_norm_sq]
      exact mul_le_mul_of_nonneg_right (hd i) (by positivity)
  have hEij : ∀ i j, ‖E i j‖ ≤ η := fun i j => by
    have hDij : D i j = if i = j then (d i : ℂ) else 0 := by
      simp only [hD, Matrix.diagonal_apply]
    rw [hE, Matrix.sub_apply, hDij]
    exact hG i j
  have hEx : hermQuad E x ≤ η * (∑ i, ‖x i‖) ^ 2 := by
    calc hermQuad E x ≤ ‖star x ⬝ᵥ E *ᵥ x‖ := Complex.re_le_norm _
      _ ≤ ∑ i, ‖x i‖ * ∑ j, ‖E i j‖ * ‖x j‖ := by
        simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul, norm_star]
        exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
          (Finset.sum_le_sum fun j _ => (norm_mul _ _).le)) (norm_nonneg _)
      _ ≤ ∑ i, ‖x i‖ * ∑ j, η * ‖x j‖ :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hEij i j) (norm_nonneg _)) (norm_nonneg _)
      _ = η * (∑ i, ‖x i‖) ^ 2 := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
        ring
  have hcs : (∑ i, ‖x i‖) ^ 2 ≤ Fintype.card ι * ∑ i, ‖x i‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i => ‖x i‖)
    simpa [Finset.card_univ] using this
  have hX : 0 ≤ ∑ i, ‖x i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h1 : η * (∑ i, ‖x i‖) ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 := by
    calc η * (∑ i, ‖x i‖) ^ 2 ≤ η * (Fintype.card ι * ∑ i, ‖x i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs hη0
      _ = (η * Fintype.card ι) * ∑ i, ‖x i‖ ^ 2 := by ring
      _ ≤ 1 * ∑ i, ‖x i‖ ^ 2 := mul_le_mul_of_nonneg_right hη hX
      _ = ∑ i, ‖x i‖ ^ 2 := one_mul _
  rw [hsplit]
  linarith

/-- **Sector attainment.** For finitely many distinct zeros of the sector of parity `s` there are
compactly supported `C²` tests of parity `s` on which Weil's form has at least that many
negative squares. -/
theorem exists_sector_negIndex_ge (Z : ZeroConfig) (hZ : TemperedConfig Z) (hFE : FESymmetric Z)
    {s : ℂ} (hs : s = 1 ∨ s = -1) {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : ι → ℂ)
    (hρ : Function.Injective ρ) (hS : ∀ i, ρ i ∈ sectorZeros Z s) :
    ∃ f : ι → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
      (∀ i, testNeg (f i) = s • f i) ∧ Fintype.card ι ≤ hermNegIndex (zeroGram Z f) := by
  classical
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hsn : ‖s‖ = 1 := by rcases hs with rfl | rfl <;> simp
  set r : ι → Z.carrier := fun i => ⟨ρ i, (hS i).1.1⟩ with hr
  have hrS : ∀ i, ((r i : Z.carrier) : ℂ) ∈ sectorZeros Z s := hS
  set w : ι → ℓ²(Z.carrier, ℂ) := fun i => sectorVec hFE s (r i) with hw
  -- the diagonal of the target Gram matrix
  set d : ι → ℝ := fun i => -4 - 4 * (if s = -1 ∧ conjCarrier hFE (r i) = r i then 1 else 0)
    with hd
  have hdle : ∀ i, d i ≤ -2 := fun i => by
    simp only [hd]
    split_ifs <;> norm_num
  have hRw : ∀ i j, inner ℂ (reflectVec Z (w j)) (w i) = if i = j then (d i : ℂ) else 0 := by
    intro i j
    rw [hw, inner_reflectVec_sectorVec hFE hs (hrS i) (hrS j)]
    have hrr : r i = r j ↔ i = j := ⟨fun h => hρ (congrArg Subtype.val h), fun h => h ▸ rfl⟩
    by_cases hij : i = j
    · subst hij
      simp only [if_true, hd]
      rcases hs with rfl | rfl
      · have hne : conjCarrier hFE (r i) ≠ r i := fun h => by
          have him := congrArg (fun t : Z.carrier => (t : ℂ).im) h
          simp only [conjCarrier, Complex.conj_im] at him
          rcases (hrS i).2 with h0 | ⟨h1, _⟩
          · linarith
          · norm_num at h1
        simp [hne]
      · by_cases hc : conjCarrier hFE (r i) = r i <;> norm_num [hc]
    · rw [if_neg (fun h => hij (hrr.mp h)), if_neg hij]
  -- approximants, symmetrised to parity `s`
  set k := Fintype.card ι with hk
  set ε : ℝ := 1 / (9 * ((k : ℝ) + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one (by positivity)]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  choose g hg using fun i => exists_zeroMap_near Z hZ (w i) hε0
  set gneg : ι → testSpace := fun i =>
    ⟨testNeg (g i), testNeg_contDiff (g i).2.1, testNeg_hasCompactSupport (g i).2.2⟩
  set gs : ι → testSpace := fun i => (1 / 2 : ℂ) • (g i + s • gneg i) with hgs
  have hTgs : ∀ i, zeroMap Z hZ (gs i) =
      (1 / 2 : ℂ) • (zeroMap Z hZ (g i) + s • fesVec hFE (zeroMap Z hZ (g i))) := fun i => by
    simp only [hgs, map_smul, map_add, gneg, zeroMap_testNeg hFE hZ]
  have hnear : ∀ i, ‖zeroMap Z hZ (gs i) - w i‖ < ε := fun i => by
    have hwsym : w i = (1 / 2 : ℂ) • (w i + s • fesVec hFE (w i)) := by
      rw [hw, fesVec_sectorVec hFE hs, smul_smul, hss, one_smul, ← two_smul ℂ, smul_smul]
      norm_num
    have hdiff : zeroMap Z hZ (gs i) - w i = (1 / 2 : ℂ) •
        ((zeroMap Z hZ (g i) - w i) + s • fesVec hFE (zeroMap Z hZ (g i) - w i)) := by
      rw [hTgs, fesVec_sub, smul_sub]
      conv_lhs => rw [hwsym]
      rw [← smul_sub]
      congr 1
      abel
    rw [hdiff, norm_smul]
    have h1 := hg i
    have h2 : ‖s • fesVec hFE (zeroMap Z hZ (g i) - w i)‖ < ε := by
      rw [norm_smul, hsn, one_mul, norm_fesVec]; exact h1
    have h3 := norm_add_le (zeroMap Z hZ (g i) - w i) (s • fesVec hFE (zeroMap Z hZ (g i) - w i))
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this]
    linarith
  refine ⟨fun i => (gs i : ℝ → ℂ), fun i => (gs i).2.1, fun i => (gs i).2.2, fun i => ?_, ?_⟩
  · -- the symmetrised test has parity `s`
    funext u
    simp only [hgs, gneg, testNeg, Submodule.coe_smul, Submodule.coe_add, Pi.smul_apply,
      Pi.add_apply, smul_eq_mul, neg_neg]
    linear_combination (-(1 / 2 : ℂ) * (g i : ℝ → ℂ) (-u)) * hss
  -- the Gram matrix is near the negative diagonal
  have hentry : ∀ i j, ‖zeroGram Z (fun i => (gs i : ℝ → ℂ)) i j -
      (if i = j then (d i : ℂ) else 0)‖ ≤ 9 * ε := by
    intro i j
    have hGij : zeroGram Z (fun i => (gs i : ℝ → ℂ)) i j =
        inner ℂ (reflectVec Z (zeroMap Z hZ (gs j))) (zeroMap Z hZ (gs i)) :=
      W_eq_inner Z hZ (gs i) (gs j)
    have hdi : zeroMap Z hZ (gs i) = w i + (zeroMap Z hZ (gs i) - w i) := by abel
    have hdj : zeroMap Z hZ (gs j) = w j + (zeroMap Z hZ (gs j) - w j) := by abel
    set ei := zeroMap Z hZ (gs i) - w i
    set ej := zeroMap Z hZ (gs j) - w j
    have hei : ‖ei‖ < ε := hnear i
    have hej : ‖ej‖ < ε := hnear j
    rw [hGij, hdi, hdj, reflectVec_add, inner_add_left, inner_add_right, inner_add_right, hRw i j]
    have h1 := (norm_inner_le_norm (𝕜 := ℂ) (reflectVec Z (w j)) ei).trans_eq
      (by rw [norm_reflectVec])
    have h2 := (norm_inner_le_norm (𝕜 := ℂ) (reflectVec Z ej) (w i)).trans_eq
      (by rw [norm_reflectVec])
    have h3 := (norm_inner_le_norm (𝕜 := ℂ) (reflectVec Z ej) ei).trans_eq
      (by rw [norm_reflectVec])
    have hwi := norm_sectorVec_le hFE hs (r i)
    have hwj := norm_sectorVec_le hFE hs (r j)
    calc ‖(if i = j then (d i : ℂ) else 0) + inner ℂ (reflectVec Z (w j)) ei +
          (inner ℂ (reflectVec Z ej) (w i) + inner ℂ (reflectVec Z ej) ei) -
            (if i = j then (d i : ℂ) else 0)‖
        = ‖inner ℂ (reflectVec Z (w j)) ei + inner ℂ (reflectVec Z ej) (w i) +
            inner ℂ (reflectVec Z ej) ei‖ := by congr 1; ring
      _ ≤ ‖w j‖ * ‖ei‖ + ‖ej‖ * ‖w i‖ + ‖ej‖ * ‖ei‖ :=
        norm_add₃_le.trans (add_le_add (add_le_add h1 h2) h3)
      _ ≤ 4 * ε + ε * 4 + ε * ε := by gcongr
      _ ≤ 9 * ε := by nlinarith
  have hη : 9 * ε * (Fintype.card ι : ℝ) ≤ 1 := by
    rw [← hk, hε]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    rw [show 9 * (1 / (9 * ((k : ℝ) + 1))) * k = k / (k + 1) by field_simp,
      div_le_one (by positivity)]
    linarith
  have hpd : IsPosDefOn (-(zeroGram Z fun i => (gs i : ℝ → ℂ))) ⊤ := fun x _ hx0 => by
    rw [hermQuad_neg]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
    have hpos : 0 < ∑ i, ‖x i‖ ^ 2 :=
      lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2) (Finset.single_le_sum
        (f := fun i => ‖x i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ i))
    linarith [hermQuad_le_of_near_diag _ d hdle hη hentry x]
  have h1 := finrank_le_posIndex hpd
  rw [finrank_top, Module.finrank_fintype_fun_eq_card] at h1
  rw [hermNegIndex]
  exact h1

/-! ### The sector law -/

/-- **The sector Pontryagin law.** On a tempered configuration symmetric under `ρ ↦ 1 − ρ`, Weil's
form has `n` negative squares on some family of `n` compactly supported `C²` tests of parity `s`
iff the sector has at least `n` zeros: the upper-half-plane zeros right of the line for even
tests, and these together with the real ones for odd tests. -/
theorem sector_pontryagin_law (Z : ZeroConfig) (hZ : TemperedConfig Z) (hFE : FESymmetric Z)
    {s : ℂ} (hs : s = 1 ∨ s = -1) (n : ℕ) :
    (∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
      (∀ i, testNeg (f i) = s • f i) ∧ n ≤ hermNegIndex (zeroGram Z f)) ↔
      (n : ℕ∞) ≤ (sectorZeros Z s).encard := by
  classical
  constructor
  · rintro ⟨f, hf, hfc, hsym, hn⟩
    exact (ENat.coe_le_coe.mpr hn).trans (negIndex_sector_le Z hZ hFE hs f hf hfc hsym)
  · intro hn
    obtain ⟨t, hts, htn⟩ := Set.exists_subset_encard_eq hn
    have htf : t.Finite := Set.finite_of_encard_eq_coe htn
    have hcard : htf.toFinset.card = n := by
      have h := htf.encard_eq_coe_toFinset_card
      rw [htn] at h
      exact_mod_cast h.symm
    set e := htf.toFinset.equivFin
    set ρ : Fin n → ℂ := fun i => (e.symm (Fin.cast hcard.symm i) : ℂ)
    have hρ : Function.Injective ρ := fun i j h =>
      Fin.cast_injective _ (e.symm.injective (Subtype.ext h))
    have hS : ∀ i, ρ i ∈ sectorZeros Z s := fun i =>
      hts ((Set.Finite.mem_toFinset htf).mp (e.symm (Fin.cast hcard.symm i)).2)
    obtain ⟨f, hf, hfc, hsym, hge⟩ := exists_sector_negIndex_ge Z hZ hFE hs ρ hρ hS
    exact ⟨f, hf, hfc, hsym, by simpa using hge⟩

/-! ### The zeros of `ζ` -/

theorem fesSymmetric_zetaZeroConfig : FESymmetric zetaZeroConfig := fun _ hρ =>
  ⟨RHTower.one_sub_mem_zetaZeroConfig hρ, RHTower.mult_one_sub_zetaZeroConfig hρ⟩

/-- The nontrivial zeros of `ζ` are not real. -/
theorem zetaZeroConfig_im_ne_zero' : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.im ≠ 0 := by
  intro ρ hρ him
  have h : 0 < ρ.re ∧ ρ.re < 1 := hρ.2
  exact RHTower.riemannZeta_ne_zero_of_abs_im_lt_four h.1 h.2 (by rw [him, abs_zero]; norm_num)
    hρ.1

theorem zeta_sectorZeros_eq (s : ℂ) :
    sectorZeros zetaZeroConfig s = {ρ | ρ ∈ rightZeros zetaZeroConfig ∧ 0 < ρ.im} := by
  ext ρ
  refine ⟨fun ⟨hR, h⟩ => ⟨hR, ?_⟩, fun ⟨hR, h⟩ => ⟨hR, Or.inl h⟩⟩
  rcases h with h | ⟨_, h0⟩
  · exact h
  · exact absurd h0 (zetaZeroConfig_im_ne_zero' ρ hR.1)

/-- **Each reflection sector of `ζ` carries half the Hodge defect.** For parity `s = ±1`, Weil's
form of `ζ` has `n` negative squares on some family of `n` tests of parity `s` iff `ζ` has at least
`n` zeros with `Re ρ > ½` and `Im ρ > 0`. -/
theorem zeta_sector_hodgeDefect_iff {s : ℂ} (hs : s = 1 ∨ s = -1) (n : ℕ) :
    (∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
      (∀ i, testNeg (f i) = s • f i) ∧ n ≤ hermNegIndex (zeroGram zetaZeroConfig f)) ↔
      (n : ℕ∞) ≤ {ρ | ρ ∈ rightZeros zetaZeroConfig ∧ 0 < ρ.im}.encard := by
  rw [sector_pontryagin_law zetaZeroConfig temperedConfig_zetaZeroConfig fesSymmetric_zetaZeroConfig
    hs n, zeta_sectorZeros_eq]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
