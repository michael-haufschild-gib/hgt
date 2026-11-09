import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.TheOddCavitySeesEveryResonance
import GaloisForLFunctions.BlackHoleRingdown.TheOddSectorIsACavity
import GaloisForLFunctions.BlackHoleRingdown.TheWeylUpperBound
import GaloisForLFunctions.BlackHoleRingdown.TheCuspSpectrumIsDiscrete

/-!
# The Maass forms see every resonance in pairs

B109 asks whether the cavity *modes* — the Maass cusp forms — see the resonances of the mirror-even channel.
For two cusp forms `u, v` the pair entry `∫_𝒟 u v̄ E*(s − ½)` is the continuation of their completed
Rankin–Selberg series (`pairing_eq_rankinSelberg`). This module proves **pairwise visibility**: at every
resonance `s = ρ/2`, `Re ρ > 0`, some pair of cuspidal Laplace eigenforms has a nonzero pair entry
(`exists_maass_pair_seeing`).

**Mechanism.** A tent field `G_j` sees the resonance (`exists_tent_seeing`). It is mirror-odd, so its class is the
`L²` sum of its components on the cuspidal eigenbasis (`BlackHoleRingdown.OddSector.hasSum_odd`). The pair entry
`h ↦ ∫_𝒟 G_j h̄ E*` is an inner product with the class of `G_j E*`, which is bounded on `𝒟` because `G_j` vanishes
above height `j + 4` there; so it is continuous on `L²` and some eigenform `v_i` has `∫_𝒟 G_j v̄_i E* ≠ 0`. The
same argument in the other slot, now against the class of `v_i Ē*` (bounded on `𝒟` since `v_i` decays like
`e^{−π Im z}`), gives an eigenform `v_l` with `∫_𝒟 v_l v̄_i E* ≠ 0`.

**B109 for Maass cusp forms.** Enumerating the countable eigenbasis, Baire gives a cuspidal cavity function
`g = Σ_n x_n 2^{−n} v_n/M_n` built from Maass cusp eigenforms whose energy sees every right resonance
(`exists_maass_cavity_seeing_every_right_zero`): the cusp-energy receiver of B109 is complete.
-/

open Complex MeasureTheory Set Filter Topology BoundedContinuousFunction
open scoped MatrixGroups UpperHalfPlane InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.RHTower.DeckPointPair GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
open GaloisForLFunctions.RHTower.SelbergMaassCongruenceTrace (Deck)

/-! ### Scalar horizon data -/

/-- The scalar Maass cusp form of the `i`-th cuspidal eigenvector. -/
def maassForm (i : CuspEigenIndex 0) (z : ℍ) : ℂ := CuspGravity.cuspFn i z 1

theorem maassForm_mem (i : CuspEigenIndex 0) : maassForm i ∈ HeckeCusp.cuspSpace i.1 :=
  HeckeCusp.component_mem_cuspSpace i

theorem inner_smul_ones (a b : ℂ) : ⟪a • onesVec 0, b • onesVec 0⟫_ℂ = starRingEnd ℂ a * b := by
  rw [inner_smul_left, inner_smul_right, WeylUpper.inner_ones_apply]
  simp [onesVec]

theorem inner_cuspFn_smul_ones (i : CuspEigenIndex 0) (z : ℍ) (b : ℂ) :
    ⟪CuspGravity.cuspFn i z, b • onesVec 0⟫_ℂ = b * starRingEnd ℂ (maassForm i z) := by
  rw [inner_smul_right, ← inner_conj_symm, WeylUpper.inner_ones_apply]
  rfl

/-- A continuous scalar function bounded on `𝒟` is square integrable horizon data. -/
theorem memLp_smul_ones {g : ℍ → ℂ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ z ∈ ModularGroup.fd, ‖g z‖ ≤ C) :
    MemLp (fun z => g z • onesVec 0) 2 GaloisForLFunctions.RHTower.MaassCongruenceL2.cellMeasure :=
  MemLp.of_bound (hg.smul continuous_const).aestronglyMeasurable C
    ((ae_restrict_mem ModularGroup.isClosed_fd.measurableSet).mono fun z hz => by
      rw [norm_smul, WeylUpper.norm_onesVec_zero, mul_one]; exact hC z hz)

theorem inner_toDeckL2 {F H : ℍ → DeckSpace 0} (hF : MemLp F 2 GaloisForLFunctions.RHTower.MaassCongruenceL2.cellMeasure)
    (hH : MemLp H 2 GaloisForLFunctions.RHTower.MaassCongruenceL2.cellMeasure) :
    ⟪toDeckL2 F hF, toDeckL2 H hH⟫_ℂ = ∫ z in ModularGroup.fd, ⟪F z, H z⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : ⇑(toDeckL2 F hF) =ᵐ[GaloisForLFunctions.RHTower.MaassCongruenceL2.cellMeasure] F := MemLp.coeFn_toLp _
  have h2 : ⇑(toDeckL2 H hH) =ᵐ[GaloisForLFunctions.RHTower.MaassCongruenceL2.cellMeasure] H := MemLp.coeFn_toLp _
  refine integral_congr_ae ?_
  filter_upwards [h1, h2] with z hz1 hz2
  rw [hz1, hz2]

/-- **Components of an odd datum.** If `⟪w, f⟫ ≠ 0` for a mirror-odd datum `f`, some cuspidal eigenvector `e_i`
has `⟪w, e_i⟫ ≠ 0`. -/
theorem exists_inner_basis_ne_zero {f w : DeckL2 0} (hf : OddSector.mirrorL2 f = -f)
    (h : ⟪w, f⟫_ℂ ≠ 0) : ∃ i, ⟪w, ((cuspEigenBasis 0 i : CuspidalL2 0) : DeckL2 0)⟫_ℂ ≠ 0 := by
  by_contra hno
  push Not at hno
  have hs := (OddSector.hasSum_odd hf).mapL (innerSL ℂ w)
  simp only [innerSL_apply_apply, inner_smul_right, hno, mul_zero] at hs
  exact h (hs.unique hasSum_zero)

theorem inner_ne_zero_symm {x y : DeckL2 0} (h : ⟪x, y⟫_ℂ ≠ 0) : ⟪y, x⟫_ℂ ≠ 0 := by
  rw [← inner_conj_symm]; exact (map_ne_zero _).2 h

/-! ### The odd tent data -/

theorem norm_tentField_le (j : ℕ) (z : ℍ) : ‖(oddCuspField (tent j) z : ℂ)‖ ≤ 1 / 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_oddCuspField_le (tent_le j) z

theorem continuous_tentField (j : ℕ) : Continuous fun z => (oddCuspField (tent j) z : ℂ) :=
  Complex.continuous_ofReal.comp (continuous_oddCuspField (isHeightProfile_tent j))

theorem memLp_tent (j : ℕ) :
    MemLp (fun z => (oddCuspField (tent j) z : ℂ) • onesVec 0) 2 GaloisForLFunctions.RHTower.MaassCongruenceL2.cellMeasure :=
  memLp_smul_ones (continuous_tentField j) fun z _ => norm_tentField_le j z

/-- The tent field `G_j` as horizon data. -/
def tentData (j : ℕ) : DeckL2 0 := toDeckL2 _ (memLp_tent j)

theorem mirrorL2_tentData (j : ℕ) : OddSector.mirrorL2 (tentData j) = -tentData j := by
  have h4 : ⇑(tentData j) =ᵐ[GaloisForLFunctions.RHTower.MaassCongruenceL2.cellMeasure]
      fun z => (oddCuspField (tent j) z : ℂ) • onesVec 0 := MemLp.coeFn_toLp (memLp_tent j)
  have h1 := OddSector.coeFn_mirrorL2 (tentData j)
  have h2 := OddSector.measurePreserving_mirror_fd.quasiMeasurePreserving.ae_eq_comp h4
  have h3 := Lp.coeFn_neg (tentData j)
  apply Lp.ext
  filter_upwards [h1, h2, h3, h4] with z hz1 hz2 hz3 hz4
  rw [hz1, hz2, hz3, Pi.neg_apply, hz4]
  simp only [Function.comp_apply, oddCuspField_mirror (isHeightProfile_tent j), Complex.ofReal_neg,
    neg_smul]

/-! ### The two functionals -/

/-- On `𝒟` the completed Eisenstein function at `s ≠ 1` grows at most polynomially. -/
theorem exists_completed_bound {s : ℂ} (hs : s ≠ 1) :
    ∃ α β a : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ a ∧ ∀ (x Y : ℝ), 1 / 2 ≤ Y →
      ‖EisAuto.completedEisenstein (s - 1 / 2) x Y‖ ≤ α * Y ^ a + β := by
  have hu : s - 1 / 2 ≠ 1 / 2 := fun h => hs (by linear_combination h)
  obtain ⟨α, β, a, hα, hβ, ha, hN⟩ := exists_kernel_bound (K := {s - 1 / 2}) isCompact_singleton
    (fun u hu' => by rw [mem_singleton_iff.1 hu']; exact hu)
  set D := ‖(1 + 2 * (s - 1 / 2)) * (2 * (s - 1 / 2))‖
  refine ⟨α / D, β / D, a, div_nonneg hα (norm_nonneg _), div_nonneg hβ (norm_nonneg _), ha,
    fun x Y hY => ?_⟩
  rw [EisAuto.completedEisenstein, norm_div]
  calc ‖eisensteinNumerator (s - 1 / 2) x Y‖ / D ≤ (α * Y ^ a + β) / D :=
        div_le_div_of_nonneg_right (hN _ (mem_singleton _) x Y hY) (norm_nonneg _)
    _ = α / D * Y ^ a + β / D := by ring

/-- The kernel `G_j E*(s − ½)` of the pair entries against a tent field. -/
def tentKernel (s : ℂ) (j : ℕ) (z : ℍ) : ℂ :=
  (oddCuspField (tent j) z : ℂ) * EisAuto.completedEisenstein (s - 1 / 2) z.re (max z.im (1 / 2))

theorem continuous_tentKernel (s : ℂ) (j : ℕ) : Continuous (tentKernel s j) :=
  (continuous_tentField j).mul (CuspRSC.continuous_completed_max _)

/-- `G_j E*` is bounded on `𝒟`: the tent field vanishes there above height `j + 4`. -/
theorem exists_tentKernel_bound {s : ℂ} (hs : s ≠ 1) (j : ℕ) :
    ∃ C, ∀ z ∈ ModularGroup.fd, ‖tentKernel s j z‖ ≤ C := by
  obtain ⟨α, β, a, hα, hβ, ha, hE⟩ := exists_completed_bound hs
  refine ⟨1 / 2 * (α * ((j : ℝ) + 4) ^ a + β), fun z hz => ?_⟩
  have hz2 : 1 / 2 < z.im := OddCusp.half_lt_im_of_mem_fd hz
  rw [tentKernel, norm_mul, max_eq_left hz2.le]
  by_cases hzh : (j : ℝ) + 4 ≤ z.im
  · rw [oddCuspField_eq_zero_of_high (isHeightProfile_tent j) (b := (j : ℝ) + 4)
      (fun y hy => tent_eq_zero (Or.inr hy))
      (by rw [max_eq_left (by linarith [j.cast_nonneg (α := ℝ)])]; exact hzh)]
    simp only [Complex.ofReal_zero, norm_zero, zero_mul]
    positivity
  · have h2 : z.im ^ a ≤ ((j : ℝ) + 4) ^ a := Real.rpow_le_rpow z.im_pos.le (not_le.1 hzh).le ha
    have hb : ‖EisAuto.completedEisenstein (s - 1 / 2) z.re z.im‖ ≤ α * ((j : ℝ) + 4) ^ a + β :=
      (hE z.re z.im hz2.le).trans (by have := mul_le_mul_of_nonneg_left h2 hα; linarith)
    exact mul_le_mul (norm_tentField_le j z) hb (norm_nonneg _) (by norm_num)

/-- The kernel `v_i Ē*(s − ½)` of the pair entries against an eigenform. -/
def maassKernel (s : ℂ) (i : CuspEigenIndex 0) (z : ℍ) : ℂ :=
  maassForm i z * starRingEnd ℂ (EisAuto.completedEisenstein (s - 1 / 2) z.re (max z.im (1 / 2)))

theorem continuous_maassKernel (s : ℂ) (i : CuspEigenIndex 0) : Continuous (maassKernel s i) :=
  (HeckeCusp.continuous_of_maass (maassForm_mem i).2.1).mul
    (continuous_conj.comp (CuspRSC.continuous_completed_max _))

/-- `v_i Ē*` is bounded on `𝒟`: the cusp form decays like `e^{−π Im z}`. -/
theorem exists_maassKernel_bound {s : ℂ} (hs : s ≠ 1) (i : CuspEigenIndex 0) :
    ∃ C, ∀ z ∈ ModularGroup.fd, ‖maassKernel s i z‖ ≤ C := by
  obtain ⟨α, β, a, hα, hβ, ha, hE⟩ := exists_completed_bound hs
  obtain ⟨M, hM, hv⟩ := exists_envelope_of_mem_cuspSpace (maassForm_mem i)
  obtain ⟨K, hK0, hK⟩ := exists_rpow_mul_exp_le ha Real.pi_pos
  refine ⟨M * (α * K + β), fun z hz => ?_⟩
  have hz2 : 1 / 2 < z.im := OddCusp.half_lt_im_of_mem_fd hz
  rw [maassKernel, norm_mul, Complex.norm_conj, max_eq_left hz2.le]
  have he : Real.exp (-Real.pi * z.im) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, z.im_pos])
  have hk := hK z.im z.im_pos
  calc ‖maassForm i z‖ * ‖EisAuto.completedEisenstein (s - 1 / 2) z.re z.im‖
      ≤ M * Real.exp (-Real.pi * z.im) * (α * z.im ^ a + β) :=
        mul_le_mul (hv z) (hE z.re z.im hz2.le) (norm_nonneg _) (by positivity)
    _ = M * (α * (z.im ^ a * Real.exp (-Real.pi * z.im)) + β * Real.exp (-Real.pi * z.im)) := by ring
    _ ≤ M * (α * K + β * 1) := by gcongr
    _ = M * (α * K + β) := by ring

/-! ### The pair entries as inner products -/

theorem inner_tentData_tentKernel (s : ℂ) (j : ℕ)
    (hk : MemLp (fun z => tentKernel s j z • onesVec 0) 2 GaloisForLFunctions.RHTower.MaassCongruenceL2.cellMeasure) :
    ⟪tentData j, toDeckL2 _ hk⟫_ℂ = tentEnergy s j := by
  rw [tentData, inner_toDeckL2, tentEnergy, pairing]
  refine setIntegral_congr_fun ModularGroup.isClosed_fd.measurableSet fun z hz => ?_
  have hz2 : 1 / 2 < z.im := OddCusp.half_lt_im_of_mem_fd hz
  simp only [inner_smul_ones, tentKernel, pairIntegrand, max_eq_left hz2.le, Complex.conj_ofReal]
  ring

theorem inner_basis_tentKernel (s : ℂ) (j : ℕ) (i : CuspEigenIndex 0)
    (hk : MemLp (fun z => tentKernel s j z • onesVec 0) 2 GaloisForLFunctions.RHTower.MaassCongruenceL2.cellMeasure) :
    ⟪((cuspEigenBasis 0 i : CuspidalL2 0) : DeckL2 0), toDeckL2 _ hk⟫_ℂ =
      pairing s (fun z => (oddCuspField (tent j) z : ℂ)) (maassForm i) := by
  rw [WeylUpper.basis_eq, inner_toDeckL2, pairing]
  refine setIntegral_congr_fun ModularGroup.isClosed_fd.measurableSet fun z hz => ?_
  have hz2 : 1 / 2 < z.im := OddCusp.half_lt_im_of_mem_fd hz
  simp only [inner_cuspFn_smul_ones, tentKernel, pairIntegrand, max_eq_left hz2.le]
  ring

theorem inner_tentData_maassKernel (s : ℂ) (j : ℕ) (i : CuspEigenIndex 0)
    (hk : MemLp (fun z => maassKernel s i z • onesVec 0) 2 GaloisForLFunctions.RHTower.MaassCongruenceL2.cellMeasure) :
    ⟪tentData j, toDeckL2 _ hk⟫_ℂ =
      starRingEnd ℂ (pairing s (fun z => (oddCuspField (tent j) z : ℂ)) (maassForm i)) := by
  rw [tentData, inner_toDeckL2, pairing, ← integral_conj]
  refine setIntegral_congr_fun ModularGroup.isClosed_fd.measurableSet fun z hz => ?_
  have hz2 : 1 / 2 < z.im := OddCusp.half_lt_im_of_mem_fd hz
  simp only [inner_smul_ones, maassKernel, pairIntegrand, max_eq_left hz2.le, Complex.conj_ofReal, map_mul,
    Complex.conj_conj]
  ring

theorem inner_basis_maassKernel (s : ℂ) (i l : CuspEigenIndex 0)
    (hk : MemLp (fun z => maassKernel s i z • onesVec 0) 2 GaloisForLFunctions.RHTower.MaassCongruenceL2.cellMeasure) :
    ⟪((cuspEigenBasis 0 l : CuspidalL2 0) : DeckL2 0), toDeckL2 _ hk⟫_ℂ =
      starRingEnd ℂ (pairing s (maassForm l) (maassForm i)) := by
  rw [WeylUpper.basis_eq, inner_toDeckL2, pairing, ← integral_conj]
  refine setIntegral_congr_fun ModularGroup.isClosed_fd.measurableSet fun z hz => ?_
  have hz2 : 1 / 2 < z.im := OddCusp.half_lt_im_of_mem_fd hz
  simp only [inner_cuspFn_smul_ones, maassKernel, pairIntegrand, max_eq_left hz2.le, map_mul,
    Complex.conj_conj]
  ring

/-! ### Pairwise visibility -/

/-- **Pairwise visibility.** For every zero `ρ` of `ζ` with `Re ρ > 0` there are cuspidal Laplace eigenforms
`v_i, v_l` with `∫_𝒟 v_l v̄_i E*(ρ/2 − ½) ≠ 0`: the continued Rankin–Selberg function of the pair does not vanish
at `ρ/2`. -/
theorem exists_maass_pair_seeing {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hpos : 0 < ρ.re) :
    ∃ i l : CuspEigenIndex 0, pairing (ρ / 2) (maassForm l) (maassForm i) ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_tent_seeing hζ hpos
  have hlt : ρ.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hζ
  have hs1 : ρ / 2 ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  obtain ⟨C₁, hC₁⟩ := exists_tentKernel_bound hs1 j
  have hk₁ := memLp_smul_ones (continuous_tentKernel (ρ / 2) j) hC₁
  have h1 : ⟪toDeckL2 _ hk₁, tentData j⟫_ℂ ≠ 0 :=
    inner_ne_zero_symm (by rw [inner_tentData_tentKernel]; exact hj)
  obtain ⟨i, hi⟩ := exists_inner_basis_ne_zero (mirrorL2_tentData j) h1
  have hi' : pairing (ρ / 2) (fun z => (oddCuspField (tent j) z : ℂ)) (maassForm i) ≠ 0 := by
    rw [← inner_basis_tentKernel _ _ _ hk₁]; exact inner_ne_zero_symm hi
  obtain ⟨C₂, hC₂⟩ := exists_maassKernel_bound hs1 i
  have hk₂ := memLp_smul_ones (continuous_maassKernel (ρ / 2) i) hC₂
  have h2 : ⟪toDeckL2 _ hk₂, tentData j⟫_ℂ ≠ 0 :=
    inner_ne_zero_symm (by rw [inner_tentData_maassKernel]; exact (map_ne_zero _).2 hi')
  obtain ⟨l, hl⟩ := exists_inner_basis_ne_zero (mirrorL2_tentData j) h2
  refine ⟨i, l, fun h0 => inner_ne_zero_symm hl ?_⟩
  rw [inner_basis_maassKernel _ _ _ hk₂, h0, map_zero]

/-! ### B109 for Maass cusp forms -/

theorem countable_cuspEigenIndex : Countable (CuspEigenIndex 0) := by
  have h : (Set.univ : Set (CuspEigenIndex 0)) = ⋃ n : ℕ, {i : CuspEigenIndex 0 | i.1 ≤ (n : ℝ)} := by
    ext i
    simp only [mem_univ, mem_iUnion, mem_setOf_eq, true_iff]
    exact ⟨⌈i.1⌉₊, Nat.le_ceil _⟩
  have hc : (Set.univ : Set (CuspEigenIndex 0)).Countable := by
    rw [h]; exact Set.countable_iUnion fun n => (finite_cuspEigenIndex_le n).countable
  exact Set.countable_univ_iff.1 hc

/-- **B109 for Maass cusp forms.** For an enumeration `v_n` of the cuspidal Laplace eigenforms there are
normalizers `M_n > 0` and one cuspidal cavity function `g = Σ_n x_n 2^{−n} v_n/M_n` whose energy sees every
right resonance. It is a complete receiver: a horocycle rate `y^α` of `|g|²` forces `Re ρ ≤ 2 − 2α` at every
zero `ρ` of `ζ` with `Re ρ > ½`. -/
theorem exists_maass_cavity_seeing_every_right_zero :
    ∃ (v : ℕ → ℍ → ℂ) (lam : ℕ → ℝ) (M : ℕ → ℝ), (∀ n, v n ∈ HeckeCusp.cuspSpace (lam n)) ∧
      (∀ n, 0 < M n) ∧ ∃ x : ℕ →ᵇ ℂ, (∀ y : ℝ, 0 < y → response (cavity (cuspFamily v M) x) y = 0) ∧
        (∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re →
          seedTransform (fun z => ((‖cavity (cuspFamily v M) x z‖ ^ 2 : ℝ) : ℂ)) (ρ / 2) ≠ 0) ∧
        ∀ (α : ℝ) (c : ℂ) (C : ℝ), (∀ y : ℝ, 0 < y → y ≤ 1 →
          ‖response (fun z => ((‖cavity (cuspFamily v M) x z‖ ^ 2 : ℝ) : ℂ)) y - c‖ ≤ C * y ^ α) →
          ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → ρ.re ≤ 2 - 2 * α := by
  haveI := countable_cuspEigenIndex
  haveI : Nonempty (CuspEigenIndex 0) := by haveI := infinite_cuspEigenIndex; infer_instance
  obtain ⟨e, he⟩ := exists_surjective_nat (CuspEigenIndex 0)
  have hv : ∀ n, maassForm (e n) ∈ HeckeCusp.cuspSpace (e n).1 := fun n => maassForm_mem (e n)
  obtain ⟨M, hM, hu, hiff⟩ := cuspFunction_sees_every_right_zero_iff
    (v := fun n => maassForm (e n)) (lam := fun n => (e n).1) hv
  obtain ⟨x, hx⟩ := hiff.2 fun ρ hζ hρ => by
    obtain ⟨i, l, h⟩ := exists_maass_pair_seeing hζ (by linarith)
    obtain ⟨n, rfl⟩ := he l
    obtain ⟨m, rfl⟩ := he i
    exact ⟨n, m, h⟩
  have hMb : ∀ n, 0 < M n ∧ ∀ z : ℍ, ‖maassForm (e n) z‖ ≤ M n * Real.exp (-Real.pi * z.im) := fun n =>
    ⟨hM n, fun z => by
      have := hu.envelope n z
      simp only [cuspFamily, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hM n).le] at this
      rwa [inv_mul_le_iff₀ (hM n)] at this⟩
  exact ⟨fun n => maassForm (e n), fun n => (e n).1, M, hv, hM, x,
    fun y hy => response_cavity_cuspFamily_eq_zero hv hMb x hy, hx,
    fun α c C hrate ρ hζ hρ => re_le_of_cavity_rate hu hx hrate hζ hρ⟩

end GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon
