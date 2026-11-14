import GaloisForLFunctions.CompactHyperbolicSurfaces.WallCrossing
import GaloisForLFunctions.CompactHyperbolicSurfaces.DirichletEnergy

/-!
# Cyclic covers of `Γ(5)\ℍ` with a small eigenvalue

`χ(γ) = θ(γz₀)` is a homomorphism `Γ(5) → ℤ` with `χ(η) = −2`.  For odd `n` the cyclic cover
`Γ_n = {γ ∈ Γ(5) : n ∣ χ(γ)}` is cocompact and free (`isCocompactFree_coverGroup`: `ηᵏ` with
`2k ≡ χ(δ) mod n` moves `δz` into `Γ_n`).  The test function `F(z) = e^{2πiθ(z)/n}` is
`Γ_n`-invariant and unimodular, and it is orthogonal to the constants: `η` normalizes `Γ_n`, so
`ηF` is again a fundamental domain, and `F ∘ η = e^{−4πi/n} F` gives
`∫_F F = e^{−4πi/n} ∫_F F` (`integral_testF_eq_zero`).

Its energy is small: `|F(y) − F(z)| ≤ 2π|θ(y) − θ(z)|/n ≤ 2πL/n` when `u(y, z) ≤ U` (bounded
increments of `θ`), and `≤ 2` always, so
`∬ K_a|F(y) − F(z)|² ≤ |F| (4 tail_a(U) + (2πL/n)²/(a(a − 1)))` (`integral_energy_testL_le`).
Taking `U` with a small tail of `k_a` and then `n` large, `Re⟨F, T_a F⟩ > ‖F‖²/(a(a − 1) + ¼)`,
and `exists_spectralParam_mem_Ioo` gives an eigenvalue `λ ∈ (0, ¼)` of `Γ_n\ℍ`
(`exists_coverGroup_small_eigenvalue`).
-/

open MeasureTheory Set Filter UpperHalfPlane Real
open scoped ENNReal MatrixGroups Pointwise InnerProductSpace ComplexConjugate Topology

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The character `χ` of `Γ(5)` -/

/-- `χ(γ) = θ(γz₀)`, `z₀ = i√3`: the wall homomorphism `wallHom` of `Γ(5)`, additively. -/
def chi (γ : congGroup 5) : ℤ := wallCount 5 zS3 ((γ : SL(2, ℝ)) • zS3)

/-- The cocycle law `θ(γz) = θ(z) + χ(γ)`. -/
theorem wallCount_smul_chi (γ : congGroup 5) (z : ℍ) :
    wallCount 5 zS3 ((γ : SL(2, ℝ)) • z) = wallCount 5 zS3 z + chi γ :=
  wallCount_smul zS3 γ z

theorem chi_mul (γ δ : congGroup 5) : chi (γ * δ) = chi γ + chi δ := by
  rw [chi, Subgroup.coe_mul, mul_smul, wallCount_smul_chi, add_comm]
  rfl

theorem chi_one : chi 1 = 0 := by
  rw [chi, OneMemClass.coe_one, one_smul, wallCount_self]

theorem chi_inv (γ : congGroup 5) : chi γ⁻¹ = -chi γ := by
  have h := chi_mul γ γ⁻¹
  rw [mul_inv_cancel, chi_one] at h
  linarith

theorem chi_pow (γ : congGroup 5) (k : ℕ) : chi (γ ^ k) = k * chi γ := by
  induction k with
  | zero => rw [pow_zero, chi_one]; simp
  | succ k ih => rw [pow_succ, chi_mul, ih]; push_cast; ring

theorem chi_etaG : chi etaG = -2 := wallCount_eta

/-! ### The covers `Γ_n` -/

theorem chi_mk_mul {g g' : SL(2, ℝ)} (hg : g ∈ congGroup 5) (hg' : g' ∈ congGroup 5) :
    chi ⟨g * g', (congGroup 5).mul_mem hg hg'⟩ = chi ⟨g, hg⟩ + chi ⟨g', hg'⟩ :=
  chi_mul ⟨g, hg⟩ ⟨g', hg'⟩

theorem chi_mk_inv {g : SL(2, ℝ)} (hg : g ∈ congGroup 5) :
    chi ⟨g⁻¹, (congGroup 5).inv_mem hg⟩ = -chi ⟨g, hg⟩ :=
  chi_inv ⟨g, hg⟩

/-- **The cyclic covers** `Γ_n = {γ ∈ Γ(5) : n ∣ χ(γ)}`. -/
def coverGroup (n : ℕ) : Subgroup SL(2, ℝ) where
  carrier := {g | ∃ h : g ∈ congGroup 5, (n : ℤ) ∣ chi ⟨g, h⟩}
  one_mem' := ⟨(congGroup 5).one_mem, by
    have h : chi ⟨1, (congGroup 5).one_mem⟩ = 0 := chi_one
    rw [h]
    exact dvd_zero _⟩
  mul_mem' := by
    rintro g g' ⟨hg, hd⟩ ⟨hg', hd'⟩
    refine ⟨(congGroup 5).mul_mem hg hg', ?_⟩
    rw [chi_mk_mul hg hg']
    exact dvd_add hd hd'
  inv_mem' := by
    rintro g ⟨hg, hd⟩
    refine ⟨(congGroup 5).inv_mem hg, ?_⟩
    rw [chi_mk_inv hg]
    exact hd.neg_right

theorem mem_coverGroup {n : ℕ} {g : SL(2, ℝ)} :
    g ∈ coverGroup n ↔ ∃ h : g ∈ congGroup 5, (n : ℤ) ∣ chi ⟨g, h⟩ := Iff.rfl

/-- `Γ(5)` normalizes `Γ_n`. -/
theorem conj_mem_coverGroup {n : ℕ} {g : SL(2, ℝ)} (hg : g ∈ coverGroup n) (δ : congGroup 5) :
    (δ : SL(2, ℝ)) * g * (δ : SL(2, ℝ))⁻¹ ∈ coverGroup n := by
  obtain ⟨hg5, hd⟩ := hg
  refine ⟨(congGroup 5).mul_mem ((congGroup 5).mul_mem δ.2 hg5) ((congGroup 5).inv_mem δ.2), ?_⟩
  rw [chi_mk_mul ((congGroup 5).mul_mem δ.2 hg5) ((congGroup 5).inv_mem δ.2), chi_mk_mul δ.2 hg5,
    chi_mk_inv δ.2,
    show chi ⟨(δ : SL(2, ℝ)), δ.2⟩ + chi ⟨g, hg5⟩ + -chi ⟨(δ : SL(2, ℝ)), δ.2⟩ = chi ⟨g, hg5⟩ by
      ring]
  exact hd

/-- **`Γ_n` is cocompact and free** for odd `n`. -/
theorem isCocompactFree_coverGroup {n : ℕ} (hn : Odd n) : IsCocompactFree (coverGroup n) where
  finite_dist R := by
    refine ((finite_dist_congGroup 5 R).preimage
      (f := fun γ : coverGroup n => (⟨γ, γ.2.1⟩ : congGroup 5)) ?_).subset ?_
    · intro γ _ γ' _ h
      exact Subtype.ext (congrArg (fun x : congGroup 5 => (x : SL(2, ℝ))) h)
    · intro γ hγ
      exact hγ
  exists_compact := by
    obtain ⟨K, hK, hcov⟩ := (isCocompactFree_congGroup (by norm_num : 3 ≤ 5)).exists_compact
    obtain ⟨t, ht⟩ := hn
    have hn' : (n : ℤ) = 2 * t + 1 := by exact_mod_cast ht
    refine ⟨⋃ k ∈ Finset.range n, (fun z => ((etaG ^ k : congGroup 5) : SL(2, ℝ)) • z) '' K,
      (Finset.range n).isCompact_biUnion fun k _ => hK.image (continuous_const_smul _), fun z => ?_⟩
    obtain ⟨δ, hδ⟩ := hcov z
    have hk0 : 0 ≤ chi δ * (t + 1) % n := Int.emod_nonneg _ (by omega)
    have hkn : chi δ * (t + 1) % n < n := Int.emod_lt_of_pos _ (by omega)
    set k : ℕ := (chi δ * (t + 1) % n).toNat with hkdef
    have hk : (k : ℤ) = chi δ * (t + 1) % n := Int.toNat_of_nonneg hk0
    have hdiv : (n : ℤ) ∣ chi (etaG ^ k * δ) := by
      rw [chi_mul, chi_pow, chi_etaG, hk, Int.emod_def]
      exact ⟨2 * (chi δ * (t + 1) / n) - chi δ, by linear_combination chi δ * hn'⟩
    refine ⟨⟨((etaG ^ k * δ : congGroup 5) : SL(2, ℝ)), (etaG ^ k * δ).2, hdiv⟩, ?_⟩
    simp only [Set.mem_iUnion]
    refine ⟨k, Finset.mem_range.mpr (by omega), (δ : SL(2, ℝ)) • z, hδ, ?_⟩
    show ((etaG ^ k : congGroup 5) : SL(2, ℝ)) • (δ : SL(2, ℝ)) • z =
      ((etaG ^ k * δ : congGroup 5) : SL(2, ℝ)) • z
    rw [Subgroup.coe_mul, mul_smul]
  eq_one_of_smul_eq γ z h := by
    have := eq_one_of_smul_eq_congGroup (by norm_num : 3 ≤ 5) ⟨γ, γ.2.1⟩ z h
    exact Subtype.ext (congrArg (fun x : congGroup 5 => (x : SL(2, ℝ))) this)

/-- `Γ_n\ℍ` is a compact quotient. -/
theorem exists_compactQuotient_coverGroup {n : ℕ} (hn : Odd n) :
    ∃ X : CompactQuotient, X.Γ = coverGroup n := by
  have hΓ := isCocompactFree_coverGroup hn
  obtain ⟨F, K, hK, hFK, hF, hfd⟩ := hΓ.exists_isFundamentalDomain
  exact ⟨⟨coverGroup n, hΓ, F, K, hK, hFK, hF, hfd⟩, rfl⟩

/-! ### The test function `e^{2πiθ/n}` -/

/-- `F_n(z) = exp(2πi θ(z)/n)`. -/
def testF (n : ℕ) (z : ℍ) : ℂ :=
  Complex.exp (((2 * π * (wallCount 5 zS3 z : ℝ) / n : ℝ) : ℂ) * Complex.I)

theorem norm_testF (n : ℕ) (z : ℍ) : ‖testF n z‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem measurable_testF (n : ℕ) : Measurable (testF n) := by
  have h1 : Measurable fun z => 2 * π * (wallCount 5 zS3 z : ℝ) / n :=
    ((measurable_wallCount zS3).const_mul (2 * π)).div_const _
  exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp h1).mul_const _)

theorem testF_smul_congGroup (n : ℕ) (γ : congGroup 5) (z : ℍ) :
    testF n ((γ : SL(2, ℝ)) • z) =
      testF n z * Complex.exp (((2 * π * (chi γ : ℝ) / n : ℝ) : ℂ) * Complex.I) := by
  rw [testF, testF, wallCount_smul_chi, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem testF_smul_cover {n : ℕ} (hn0 : n ≠ 0) {g : SL(2, ℝ)} (hg : g ∈ coverGroup n) (z : ℍ) :
    testF n (g • z) = testF n z := by
  obtain ⟨hg5, q, hq⟩ := hg
  have h := testF_smul_congGroup n ⟨g, hg5⟩ z
  rw [hq] at h
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have he : (2 * π * (((n : ℤ) * q : ℤ) : ℝ) / n : ℝ) = q * (2 * π) := by
    rw [div_eq_iff hn]; push_cast; ring
  rw [he] at h
  rw [show g • z = ((⟨g, hg5⟩ : congGroup 5) : SL(2, ℝ)) • z from rfl, h]
  push_cast
  rw [show (q : ℂ) * (2 * π) * Complex.I = q * (2 * π * Complex.I) by ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem testF_smul_eta (n : ℕ) (z : ℍ) :
    testF n (etaSL • z) = testF n z * Complex.exp (((2 * π * (-2 : ℝ) / n : ℝ) : ℂ) * Complex.I) := by
  have h := testF_smul_congGroup n etaG z
  rw [chi_etaG] at h
  exact_mod_cast h

/-- `|F(y) − F(z)| ≤ 2π|θ(y) − θ(z)|/n`. -/
theorem norm_testF_sub_le (n : ℕ) (y z : ℍ) : ‖testF n y - testF n z‖ ≤
    2 * π * |((wallCount 5 zS3 y - wallCount 5 zS3 z : ℤ) : ℝ)| / n := by
  have h : testF n y - testF n z = testF n z * (Complex.exp (Complex.I *
      ((2 * π * ((wallCount 5 zS3 y - wallCount 5 zS3 z : ℤ) : ℝ) / n : ℝ) : ℂ)) - 1) := by
    rw [testF, testF, mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, norm_testF, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos,
    Nat.abs_cast]

theorem norm_testF_sub_le_two (n : ℕ) (y z : ℍ) : ‖testF n y - testF n z‖ ≤ 2 :=
  (norm_sub_le _ _).trans (by rw [norm_testF, norm_testF]; norm_num)

/-! ### The tail of `k_a` -/

/-- The tail mass `∫_{u(i, w) > U} k_a(u(i, w)) dw`. -/
def tailMass (a U : ℝ) : ℝ≥0∞ := ∫⁻ w, (Ioi U).indicator (resKernel a) (pairU I w)

theorem exists_tailMass_le {a : ℝ} (ha : 1 < a) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ m : ℕ, tailMass a m ≤ ε := by
  have hlim : Tendsto (fun m : ℕ => tailMass a m) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := (volume : Measure ℍ))
      (F := fun m : ℕ => fun w => (Ioi (m : ℝ)).indicator (resKernel a) (pairU I w))
      (f := fun _ => 0) (fun w => resKernel a (pairU I w))
      (fun m => ((measurable_resKernel a).indicator measurableSet_Ioi).comp
        (continuous_pairU.comp (continuous_const.prodMk continuous_id)).measurable)
      (fun m => Eventually.of_forall fun w => indicator_le_self _ _ _)
      (lintegral_resKernel_mass_lt_top ha).ne
      (Eventually.of_forall fun w => tendsto_atTop_of_eventually_const (i₀ := ⌈pairU I w⌉₊)
        fun m hm => indicator_of_notMem (by
          simp only [mem_Ioi, not_lt]
          exact (Nat.le_ceil _).trans (by exact_mod_cast hm)) _)
    simpa [tailMass] using this
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.mp hlim) ε hε
  exact ⟨N, hN N le_rfl⟩

theorem dist_le_log_of_pairU_le {y z : ℍ} {U : ℝ} (h : pairU y z ≤ U) :
    dist y z ≤ Real.log (2 + 4 * U) := by
  have hU : 0 ≤ U := (pairU_nonneg y z).trans h
  rw [Real.le_log_iff_exp_le (by linarith)]
  rw [pairU_eq_cosh] at h
  have h2 : Real.exp (dist y z) / 2 ≤ Real.cosh (dist y z) := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos (-dist y z)]
  linarith

/-! ### Unfolding against invariant functions -/

/-- `∫_F K(y, z) h(z) dz = ∫_ℍ k(u(y, z)) h(z) dz` for `Γ`-invariant `h`. -/
theorem CompactQuotient.setLIntegral_autK_mul_invariant (X : CompactQuotient) {k : ℝ → ℝ≥0∞}
    (hk : Measurable k) {h : ℍ → ℝ≥0∞} (hh : Measurable h)
    (hinv : ∀ (γ : X.Γ) (z : ℍ), h ((γ : SL(2, ℝ)) • z) = h z) (y : ℍ) :
    ∫⁻ z in X.F, autK X.Γ k y z * h z = ∫⁻ z, k (pairU y z) * h z := by
  have e1 : ∀ z, autK X.Γ k y z * h z =
      ∑' γ : X.Γ, k (pairU y ((γ : SL(2, ℝ)) • z)) * h ((γ : SL(2, ℝ)) • z) := fun z => by
    rw [autK, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun γ => by rw [hinv]
  have hm : Measurable fun z => k (pairU y z) * h z :=
    (hk.comp (continuous_pairU.comp (continuous_const.prodMk continuous_id)).measurable).mul hh
  calc ∫⁻ z in X.F, autK X.Γ k y z * h z
      = ∫⁻ z in X.F, ∑' γ : X.Γ, k (pairU y ((γ : SL(2, ℝ)) • z)) * h ((γ : SL(2, ℝ)) • z) :=
        lintegral_congr e1
    _ = ∑' γ : X.Γ, ∫⁻ z in X.F, k (pairU y ((γ : SL(2, ℝ)) • z)) * h ((γ : SL(2, ℝ)) • z) :=
        lintegral_tsum fun γ => (hm.comp (measurable_const_smul ((γ : SL(2, ℝ))))).aemeasurable
    _ = ∫⁻ z, k (pairU y z) * h z :=
        (X.isFundamentalDomain.lintegral_eq_tsum'' (fun z => k (pairU y z) * h z)).symm

/-! ### The test vector on a cover -/

namespace CompactQuotient

variable (X : CompactQuotient)

/-- The test vector `F_n ∈ L²(F)`. -/
def testL (n : ℕ) : Lp ℂ 2 X.μ :=
  (MemLp.of_bound (measurable_testF n).aestronglyMeasurable 1
    (Eventually.of_forall fun z => (norm_testF n z).le)).toLp (testF n)

theorem coeFn_testL (n : ℕ) : (X.testL n : ℍ → ℂ) =ᵐ[X.μ] testF n := MemLp.coeFn_toLp _

theorem norm_testL_sq (n : ℕ) : ‖X.testL n‖ ^ 2 = (volume X.F).toReal := by
  rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  calc ∫ z, ‖(X.testL n : ℍ → ℂ) z‖ ^ 2 ∂X.μ = ∫ _z, (1 : ℝ) ∂X.μ := by
        refine integral_congr_ae ?_
        filter_upwards [X.coeFn_testL n] with z hz
        rw [hz, norm_testF, one_pow]
    _ = (volume X.F).toReal := by
        rw [integral_const, smul_eq_mul, mul_one]
        simp only [Measure.real, CompactQuotient.μ, Measure.restrict_apply_univ]

theorem volume_F_ne_zero : volume X.F ≠ 0 := by
  refine X.isFundamentalDomain.measure_ne_zero fun h => ?_
  have := volume_closedBall_pos I one_pos
  rw [h] at this
  simp at this

theorem volume_F_toReal_pos : 0 < (volume X.F).toReal :=
  ENNReal.toReal_pos X.volume_F_ne_zero X.volume_F_lt_top.ne

variable {n : ℕ} (hX : X.Γ = coverGroup n)
include hX

theorem testF_smul_of_eq (hn0 : n ≠ 0) (γ : X.Γ) (z : ℍ) :
    testF n ((γ : SL(2, ℝ)) • z) = testF n z :=
  testF_smul_cover hn0 (hX ▸ γ.2) z

/-- **Orthogonality to the constants.**  `η` normalizes `Γ_n`, so `ηF` is a fundamental domain, and
`F ∘ η = e^{−4πi/n} F` with `e^{−4πi/n} ≠ 1` for `n ≥ 3`. -/
theorem integral_testF_eq_zero (hn3 : 3 ≤ n) : ∫ z in X.F, testF n z = 0 := by
  have hn0 : n ≠ 0 := by omega
  have hmem : ∀ g : SL(2, ℝ), g ∈ X.Γ →
      ((etaG⁻¹ : congGroup 5) : SL(2, ℝ)) * g * ((etaG⁻¹ : congGroup 5) : SL(2, ℝ))⁻¹ ∈ X.Γ ∧
      (etaG : SL(2, ℝ)) * g * (etaG : SL(2, ℝ))⁻¹ ∈ X.Γ := by
    intro g hg
    rw [hX] at hg ⊢
    exact ⟨conj_mem_coverGroup hg etaG⁻¹, conj_mem_coverGroup hg etaG⟩
  let e : X.Γ ≃ X.Γ :=
    { toFun := fun g => ⟨((etaG⁻¹ : congGroup 5) : SL(2, ℝ)) * g * ((etaG⁻¹ : congGroup 5) : SL(2, ℝ))⁻¹,
        (hmem g g.2).1⟩
      invFun := fun g => ⟨(etaG : SL(2, ℝ)) * g * (etaG : SL(2, ℝ))⁻¹, (hmem g g.2).2⟩
      left_inv := fun g => by
        apply Subtype.ext
        simp only [InvMemClass.coe_inv, inv_inv]
        group
      right_inv := fun g => by
        apply Subtype.ext
        simp only [InvMemClass.coe_inv, inv_inv]
        group }
  have hef : ∀ g : X.Γ, Function.Semiconj (MulAction.toPerm etaSL) (fun x : ℍ => e g • x)
      (fun x : ℍ => g • x) := by
    intro g x
    show etaSL • ((e g : SL(2, ℝ)) • x) = (g : SL(2, ℝ)) • etaSL • x
    simp only [e, InvMemClass.coe_inv, inv_inv, ← mul_smul]
    congr 1
    show etaSL * ((etaSL⁻¹ * (g : SL(2, ℝ))) * etaSL) = (g : SL(2, ℝ)) * etaSL
    group
  have ht : IsFundamentalDomain X.Γ ((fun z => etaSL • z) '' X.F) volume :=
    X.isFundamentalDomain.image_of_equiv (MulAction.toPerm etaSL)
      (measurePreserving_smul etaSL⁻¹ volume).quasiMeasurePreserving e hef
  have h1 : ∫ z in X.F, testF n z = ∫ z in (fun z => etaSL • z) '' X.F, testF n z :=
    X.isFundamentalDomain.setIntegral_eq ht fun g z => X.testF_smul_of_eq hX hn0 g z
  have h2 : ∫ z in (fun z => etaSL • z) '' X.F, testF n z = ∫ z in X.F, testF n (etaSL • z) :=
    (measurePreserving_smul etaSL volume).setIntegral_image_emb
      (measurableEmbedding_const_smul etaSL) (testF n) X.F
  set ω : ℂ := Complex.exp (((2 * π * (-2 : ℝ) / n : ℝ) : ℂ) * Complex.I) with hω
  have h3 : ∫ z in X.F, testF n (etaSL • z) = (∫ z in X.F, testF n z) * ω := by
    simp only [testF_smul_eta, hω]
    exact integral_mul_const _ _
  have hω1 : ω ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hω, Complex.exp_ofReal_mul_I_re, Complex.one_re] at hre
    have hn : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    have hlo : -(2 * π) < 2 * π * (-2 : ℝ) / n := by
      rw [lt_div_iff₀ (by linarith)]; nlinarith [Real.pi_pos]
    have hhi : 2 * π * (-2 : ℝ) / n < 2 * π := by
      rw [div_lt_iff₀ (by linarith)]; nlinarith [Real.pi_pos]
    have h0 := (Real.cos_eq_one_iff_of_lt_of_lt hlo hhi).mp hre
    have : 2 * π * (-2 : ℝ) / n < 0 := div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos])
      (by linarith)
    linarith
  have hI : (∫ z in X.F, testF n z) * (1 - ω) = 0 := by
    rw [mul_sub, mul_one, ← h3, ← h2, ← h1, sub_self]
  rcases mul_eq_zero.mp hI with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h).symm hω1

theorem inner_oneL_testL (hn3 : 3 ≤ n) : ⟪X.oneL, X.testL n⟫_ℂ = 0 := by
  rw [MeasureTheory.L2.inner_def]
  calc ∫ z, ⟪(X.oneL : ℍ → ℂ) z, (X.testL n : ℍ → ℂ) z⟫_ℂ ∂X.μ = ∫ z, testF n z ∂X.μ := by
        refine integral_congr_ae ?_
        filter_upwards [X.coeFn_oneL, X.coeFn_testL n] with z h1 h2
        rw [h1, h2]
        simp
    _ = 0 := X.integral_testF_eq_zero hX hn3

/-- **The energy of the test vector.**  With `L` bounding the increments of `θ` over distance
`log(2 + 4U)`, `∬ K_a|F(y) − F(z)|² ≤ |F| (4 tail_a(U) + (2πL/n)²/(a(a − 1)))`. -/
theorem integral_energy_testL_le (hn0 : n ≠ 0) {a : ℝ} (ha : 1 < a) {U : ℝ} {L : ℤ}
    (hL : ∀ y z : ℍ, dist y z ≤ Real.log (2 + 4 * U) →
      |wallCount 5 zS3 y - wallCount 5 zS3 z| ≤ L) :
    ∫ p, X.kerA a p.1 p.2 * ‖(X.testL n : ℍ → ℂ) p.1 - (X.testL n : ℍ → ℂ) p.2‖ ^ 2
        ∂(X.μ.prod X.μ) ≤
      (volume X.F).toReal * (4 * (tailMass a U).toReal + (2 * π * L / n) ^ 2 * (1 / (a * (a - 1)))) := by
  set δ : ℝ := 2 * π * L / n with hδ
  set B : ℝ≥0∞ := 4 * tailMass a U + ENNReal.ofReal (δ ^ 2) * ENNReal.ofReal (1 / (a * (a - 1)))
    with hB
  have htail_fin : tailMass a U ≠ ∞ := by
    refine ne_top_of_le_ne_top (lintegral_resKernel_mass_lt_top ha).ne (lintegral_mono fun w => ?_)
    exact indicator_le_self _ _ _
  -- the pointwise bound
  have hpt : ∀ y z : ℍ, resKernel a (pairU y z) * ‖testF n y - testF n z‖ₑ ^ 2 ≤
      (Ioi U).indicator (resKernel a) (pairU y z) * 4 +
        resKernel a (pairU y z) * ENNReal.ofReal (δ ^ 2) := by
    intro y z
    by_cases hu : U < pairU y z
    · rw [indicator_of_mem (show pairU y z ∈ Ioi U from hu)]
      refine le_add_right ?_
      have h4 : ‖testF n y - testF n z‖ₑ ^ 2 ≤ 4 := by
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
        calc ENNReal.ofReal (‖testF n y - testF n z‖ ^ 2) ≤ ENNReal.ofReal (2 ^ 2) :=
              ENNReal.ofReal_le_ofReal
                (pow_le_pow_left₀ (norm_nonneg _) (norm_testF_sub_le_two n y z) 2)
          _ = 4 := by norm_num
      gcongr
    · rw [indicator_of_notMem (show pairU y z ∉ Ioi U from hu), zero_mul, zero_add]
      have h5 : ‖testF n y - testF n z‖ₑ ^ 2 ≤ ENNReal.ofReal (δ ^ 2) := by
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
        refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
        have hd := hL y z (dist_le_log_of_pairU_le (not_lt.mp hu))
        have hd' : |((wallCount 5 zS3 y - wallCount 5 zS3 z : ℤ) : ℝ)| ≤ L := by exact_mod_cast hd
        have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
        refine (norm_testF_sub_le n y z).trans ?_
        rw [hδ]
        gcongr
      gcongr
  -- the bound for each row
  have hrow : ∀ y : ℍ, ∫⁻ z in X.F, autK X.Γ (resKernel a) y z * ‖testF n y - testF n z‖ₑ ^ 2 ≤ B := by
    intro y
    have hinv : ∀ (γ : X.Γ) (z : ℍ), ‖testF n y - testF n ((γ : SL(2, ℝ)) • z)‖ₑ ^ 2 =
        ‖testF n y - testF n z‖ₑ ^ 2 := fun γ z => by rw [X.testF_smul_of_eq hX hn0]
    have hmh : Measurable fun z => ‖testF n y - testF n z‖ₑ ^ 2 :=
      ((measurable_const.sub (measurable_testF n)).enorm).pow_const 2
    rw [X.setLIntegral_autK_mul_invariant (measurable_resKernel a) hmh hinv y]
    have hm1 : Measurable fun z => (Ioi U).indicator (resKernel a) (pairU y z) :=
      ((measurable_resKernel a).indicator measurableSet_Ioi).comp
        (continuous_pairU.comp (continuous_const.prodMk continuous_id)).measurable
    have hm2 : Measurable fun z => resKernel a (pairU y z) :=
      (measurable_resKernel a).comp
        (continuous_pairU.comp (continuous_const.prodMk continuous_id)).measurable
    have hmk : Measurable fun z => (Ioi U).indicator (resKernel a) (pairU y z) * 4 :=
      hm1.mul_const _
    calc ∫⁻ z, resKernel a (pairU y z) * ‖testF n y - testF n z‖ₑ ^ 2
        ≤ ∫⁻ z, ((Ioi U).indicator (resKernel a) (pairU y z) * 4 +
            resKernel a (pairU y z) * ENNReal.ofReal (δ ^ 2)) := lintegral_mono fun z => hpt y z
      _ = (∫⁻ z, (Ioi U).indicator (resKernel a) (pairU y z) * 4) +
            ∫⁻ z, resKernel a (pairU y z) * ENNReal.ofReal (δ ^ 2) := lintegral_add_left hmk _
      _ = B := by
          rw [lintegral_mul_const _ hm1, lintegral_mul_const _ hm2,
            lintegral_pairU_eq_I ((Ioi U).indicator (resKernel a)) y,
            lintegral_pairU_eq_I (resKernel a) y, lintegral_resKernel_mass ha, hB, tailMass]
          ring
  -- assemble
  have hfst := (Measure.quasiMeasurePreserving_fst (μ := X.μ) (ν := X.μ)).ae_eq (X.coeFn_testL n)
  have hsnd := (Measure.quasiMeasurePreserving_snd (μ := X.μ) (ν := X.μ)).ae_eq (X.coeFn_testL n)
  have hG : (fun p : ℍ × ℍ => X.kerA a p.1 p.2 *
      ‖(X.testL n : ℍ → ℂ) p.1 - (X.testL n : ℍ → ℂ) p.2‖ ^ 2) =ᵐ[X.μ.prod X.μ]
      fun p => X.kerA a p.1 p.2 * ‖testF n p.1 - testF n p.2‖ ^ 2 := by
    filter_upwards [hfst, hsnd] with p h1 h2
    simp only [Function.comp_apply] at h1 h2
    rw [h1, h2]
  have hGm : Measurable fun p : ℍ × ℍ => X.kerA a p.1 p.2 * ‖testF n p.1 - testF n p.2‖ ^ 2 :=
    (X.measurable_kerA a).mul ((((measurable_testF n).comp measurable_fst).sub
      ((measurable_testF n).comp measurable_snd)).norm.pow_const 2)
  rw [integral_congr_ae hG, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun p => mul_nonneg (X.kerA_nonneg a _ _) (sq_nonneg _))
    hGm.aestronglyMeasurable]
  have hle : ∫⁻ p, ENNReal.ofReal (X.kerA a p.1 p.2 * ‖testF n p.1 - testF n p.2‖ ^ 2)
      ∂(X.μ.prod X.μ) ≤ B * volume X.F := by
    calc ∫⁻ p, ENNReal.ofReal (X.kerA a p.1 p.2 * ‖testF n p.1 - testF n p.2‖ ^ 2) ∂(X.μ.prod X.μ)
        ≤ ∫⁻ p, autK X.Γ (resKernel a) p.1 p.2 * ‖testF n p.1 - testF n p.2‖ₑ ^ 2
            ∂(X.μ.prod X.μ) := by
          refine lintegral_mono fun p => ?_
          rw [ENNReal.ofReal_mul (X.kerA_nonneg a _ _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
          gcongr
          exact ENNReal.ofReal_toReal_le
      _ = ∫⁻ y in X.F, ∫⁻ z in X.F, autK X.Γ (resKernel a) y z * ‖testF n y - testF n z‖ₑ ^ 2 :=
          lintegral_prod (fun p : ℍ × ℍ => autK X.Γ (resKernel a) p.1 p.2 *
              ‖testF n p.1 - testF n p.2‖ₑ ^ 2)
            ((measurable_autK (Γ := X.Γ) (measurable_resKernel a)).mul
              ((((measurable_testF n).comp measurable_fst).sub
                ((measurable_testF n).comp measurable_snd)).enorm.pow_const 2)).aemeasurable
      _ ≤ ∫⁻ _y in X.F, B := lintegral_mono fun y => hrow y
      _ = B * volume X.F := by rw [lintegral_const, Measure.restrict_apply_univ]
  have hBfin : B ≠ ∞ := by
    rw [hB]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) htail_fin,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
  have hc : 0 ≤ 1 / (a * (a - 1)) := by
    have : 0 < a * (a - 1) := by nlinarith
    positivity
  calc (∫⁻ p, ENNReal.ofReal (X.kerA a p.1 p.2 * ‖testF n p.1 - testF n p.2‖ ^ 2)
        ∂(X.μ.prod X.μ)).toReal ≤ (B * volume X.F).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hBfin X.volume_F_lt_top.ne) hle
    _ = (volume X.F).toReal * (4 * (tailMass a U).toReal + δ ^ 2 * (1 / (a * (a - 1)))) := by
        rw [ENNReal.toReal_mul, hB, ENNReal.toReal_add (ENNReal.mul_ne_top (by norm_num) htail_fin)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal hc,
          ENNReal.toReal_ofNat]
        ring

end CompactQuotient

/-! ### The small eigenvalue -/

/-- **A cover with a small eigenvalue.**  For every `a > 1` there is an odd `n ≥ 3` such that every
compact quotient by `Γ_n` has a spectral parameter `λ ∈ (0, ¼)`. -/
theorem exists_coverGroup_small_eigenvalue {a : ℝ} (ha : 1 < a) :
    ∃ n : ℕ, Odd n ∧ 3 ≤ n ∧ ∀ X : CompactQuotient, X.Γ = coverGroup n →
      ∃ j : X.SpecIndex ha, 0 < X.spectralParam ha j ∧ X.spectralParam ha j < 1 / 4 := by
  set c := a * (a - 1) with hcdef
  have hc : 0 < c := by simp only [hcdef]; nlinarith
  set κ := 1 / c - 1 / (c + 1 / 4) with hκdef
  have hκ : 0 < κ := by
    simp only [hκdef]
    have : 1 / (c + 1 / 4) < 1 / c := one_div_lt_one_div_of_lt hc (by linarith)
    linarith
  obtain ⟨m, hm⟩ := exists_tailMass_le ha (ε := ENNReal.ofReal (κ / 8))
    (ENNReal.ofReal_pos.mpr (by positivity))
  set U : ℝ := (m : ℝ) with hUdef
  have ht : (tailMass a U).toReal ≤ κ / 8 :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hm).trans_eq (ENNReal.toReal_ofReal (by positivity))
  obtain ⟨L, hL⟩ := exists_abs_wallCount_sub_le_of_dist zS3 (by norm_num : 3 ≤ 5)
    (Real.log (2 + 4 * U))
  set M : ℕ := ⌈(2 * π * L) ^ 2 / (c * κ)⌉₊ + 1 with hMdef
  refine ⟨2 * M + 1, ⟨M, rfl⟩, by omega, fun X hX => ?_⟩
  set n : ℕ := 2 * M + 1 with hndef
  have hn0 : n ≠ 0 := by omega
  have hn3 : 3 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  -- `(2πL/n)²/c < κ`
  have hnbig : (2 * π * L) ^ 2 / (c * κ) < (n : ℝ) ^ 2 := by
    have h1 : (2 * π * L) ^ 2 / (c * κ) < M := by
      rw [hMdef]; push_cast
      linarith [Nat.le_ceil ((2 * π * L) ^ 2 / (c * κ))]
    have h2 : (M : ℝ) ≤ n := by rw [hndef]; push_cast; linarith
    have h3 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      nlinarith
    linarith
  have hδ : (2 * π * L / n) ^ 2 * (1 / c) < κ := by
    rw [div_lt_iff₀ (mul_pos hc hκ)] at hnbig
    rw [div_pow, div_mul_div_comm, mul_one, div_lt_iff₀ (mul_pos (pow_pos hnR 2) hc)]
    linarith
  -- the Rayleigh bound
  have hE := X.integral_energy_testL_le hX hn0 ha hL
  have hid := X.integral_energy ha (X.testL n)
  have hnorm := X.norm_testL_sq n
  have hF := X.volume_F_toReal_pos
  set V := (volume X.F).toReal with hV
  have hR : ‖X.testL n‖ ^ 2 / (c + 1 / 4) < (⟪X.testL n, X.resOp ha (X.testL n)⟫_ℂ).re := by
    rw [hnorm]
    have hκ' : V / (c + 1 / 4) = V / c - V * κ := by
      simp only [hκdef]; ring
    have hlt : V * (2 * (tailMass a U).toReal + (2 * π * L / n) ^ 2 * (1 / c) / 2) < V * κ := by
      refine mul_lt_mul_of_pos_left ?_ hF
      linarith
    rw [hnorm, ← hcdef] at hid
    rw [← hcdef, hid] at hE
    have h1 : 2 * (V / c) - 2 * (⟪X.testL n, X.resOp ha (X.testL n)⟫_ℂ).re ≤
        2 * (V * (2 * (tailMass a U).toReal + (2 * π * L / n) ^ 2 * (1 / c) / 2)) := by
      have e1 : 2 * V / c = 2 * (V / c) := by ring
      have e2 : V * (4 * (tailMass a U).toReal + (2 * π * L / n) ^ 2 * (1 / c)) =
          2 * (V * (2 * (tailMass a U).toReal + (2 * π * L / n) ^ 2 * (1 / c) / 2)) := by ring
      linarith
    rw [hκ']
    linarith
  have hf0 : X.testL n ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_pow two_ne_zero] at hnorm
    linarith
  exact X.exists_spectralParam_mem_Ioo ha hf0 (X.inner_oneL_testL hX hn3) hR

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
