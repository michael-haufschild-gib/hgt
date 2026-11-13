import GaloisForLFunctions.CompactHyperbolicSurfaces.Centralizers
import GaloisForLFunctions.CompactHyperbolicSurfaces.ResolventOperators

/-!
# Orbital integrals over a conjugacy class

For `γ ≠ 1` in a cocompact free group of hyperbolic elements, with primitive root `γ₀`,
`γ₀ = ±σ dil(e^{ℓ₀}) σ⁻¹`:

* the annulus `A = σ · {1 ≤ |z| < e^{ℓ₀}}` meets every orbit of `⟨γ₀⟩` exactly once
  (`tsum_indicator_annulus`);
* the fibres of `δ ↦ δ⁻¹γδ` are the cosets `⟨γ₀⟩δ₁`, so unfolding the fundamental domain gives
  `Σ_{γ' ~ γ} ∫_F k(u(z, γ'z)) = ∫_A k(u(w, γw)) = ℓ₀ ∫_ℝ k(c(1 + t²)) dt`,
  `c = (N − 1)²/(4N)`, `N = e^{ℓ(γ)}` (`tsum_isConj_lintegral`).

`primLen γ`, the least length of a nontrivial element commuting with `γ`, is the length `ℓ₀` of the
primitive root, and both lengths are conjugation invariant.
-/

open MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups ENNReal Pointwise

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry RHTower

noncomputable section

/-! ### Powers and action of a framed element -/

theorem zpow_frame {σ g : SL(2, ℝ)} {ℓ : ℝ}
    (hg : g = σ * dilSL (Real.exp ℓ) (Real.exp_pos _) * σ⁻¹ ∨
      g = -(σ * dilSL (Real.exp ℓ) (Real.exp_pos _) * σ⁻¹)) (k : ℤ) :
    g ^ k = σ * dilSL (Real.exp (k * ℓ)) (Real.exp_pos _) * σ⁻¹ ∨
      g ^ k = -(σ * dilSL (Real.exp (k * ℓ)) (Real.exp_pos _) * σ⁻¹) := by
  have hpow : (σ * dilSL (Real.exp ℓ) (Real.exp_pos _) * σ⁻¹) ^ k =
      σ * dilSL (Real.exp (k * ℓ)) (Real.exp_pos _) * σ⁻¹ := by
    rw [conj_zpow, dilSL_zpow, Real.log_exp]
  rcases hg with rfl | rfl
  · exact Or.inl hpow
  · rw [← neg_one_mul, (Commute.neg_one_left _).mul_zpow, hpow]
    rcases Int.even_or_odd k with he | ho
    · left; rw [he.neg_one_zpow, one_mul]
    · right; rw [ho.neg_one_zpow, neg_one_mul]

theorem smul_frame {σ g : SL(2, ℝ)} {N : ℝ} {hN : 0 < N}
    (hg : g = σ * dilSL N hN * σ⁻¹ ∨ g = -(σ * dilSL N hN * σ⁻¹)) (z : ℍ) :
    g • z = (σ * dilSL N hN * σ⁻¹) • z := by
  rcases hg with rfl | rfl
  · rfl
  · exact neg_smul_SL _ z

theorem hypLen_zpow_frame {σ g : SL(2, ℝ)} {ℓ : ℝ}
    (hg : g = σ * dilSL (Real.exp ℓ) (Real.exp_pos _) * σ⁻¹ ∨
      g = -(σ * dilSL (Real.exp ℓ) (Real.exp_pos _) * σ⁻¹)) (k : ℤ) :
    hypLen (g ^ k) = |k * ℓ| := by
  rw [hypLen_conj_dilSL _ σ (zpow_frame hg k), Real.log_exp]

/-! ### The annulus is an exact fundamental domain for `⟨γ₀⟩` -/

theorem existsUnique_mem_annulus {σ g : SL(2, ℝ)} {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀)
    (hg : g = σ * dilSL (Real.exp ℓ₀) (Real.exp_pos _) * σ⁻¹ ∨
      g = -(σ * dilSL (Real.exp ℓ₀) (Real.exp_pos _) * σ⁻¹)) (w : ℍ) :
    ∃! k : ℤ, (g ^ k) • w ∈ σ • dilAnnulus (Real.exp ℓ₀) := by
  have hmem : ∀ k : ℤ, (g ^ k) • w ∈ σ • dilAnnulus (Real.exp ℓ₀) ↔
      0 ≤ k * ℓ₀ + Real.log ‖((σ⁻¹ • w : ℍ) : ℂ)‖ ∧
        k * ℓ₀ + Real.log ‖((σ⁻¹ • w : ℍ) : ℂ)‖ < ℓ₀ := by
    intro k
    have hv : 0 < ‖((σ⁻¹ • w : ℍ) : ℂ)‖ := norm_pos_iff.mpr (UpperHalfPlane.ne_zero _)
    rw [smul_frame (zpow_frame hg k), Set.mem_smul_set_iff_inv_smul_mem, ← mul_smul,
      show σ⁻¹ * (σ * dilSL (Real.exp (k * ℓ₀)) (Real.exp_pos _) * σ⁻¹) =
        dilSL (Real.exp (k * ℓ₀)) (Real.exp_pos _) * σ⁻¹ by group, mul_smul]
    simp only [dilAnnulus, mem_setOf_eq, coe_dilSL_smul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (k * ℓ₀) * ‖((σ⁻¹ • w : ℍ) : ℂ)‖ =
        Real.exp (k * ℓ₀ + Real.log ‖((σ⁻¹ • w : ℍ) : ℂ)‖) := by
      rw [Real.exp_add, Real.exp_log hv]
    have hl1 : (1 ≤ Real.exp (k * ℓ₀) * ‖((σ⁻¹ • w : ℍ) : ℂ)‖) ↔
        0 ≤ k * ℓ₀ + Real.log ‖((σ⁻¹ • w : ℍ) : ℂ)‖ := by
      rw [he, Real.one_le_exp_iff]
    have hl2 : (Real.exp (k * ℓ₀) * ‖((σ⁻¹ • w : ℍ) : ℂ)‖ < Real.exp ℓ₀) ↔
        k * ℓ₀ + Real.log ‖((σ⁻¹ • w : ℍ) : ℂ)‖ < ℓ₀ := by
      rw [he, Real.exp_lt_exp]
    rw [hl1, hl2]
  set L := Real.log ‖((σ⁻¹ • w : ℍ) : ℂ)‖
  refine ⟨⌈-L / ℓ₀⌉, (hmem _).mpr ⟨?_, ?_⟩, fun k hk => ?_⟩
  · have h := mul_le_mul_of_nonneg_right (Int.le_ceil (-L / ℓ₀)) hℓ₀.le
    rw [div_mul_cancel₀ _ hℓ₀.ne'] at h; linarith
  · have h := mul_lt_mul_of_pos_right (Int.ceil_lt_add_one (-L / ℓ₀)) hℓ₀
    rw [add_mul, div_mul_cancel₀ _ hℓ₀.ne', one_mul] at h; linarith
  · obtain ⟨h1, h2⟩ := (hmem k).mp hk
    symm
    rw [Int.ceil_eq_iff]
    constructor
    · rw [lt_div_iff₀ hℓ₀]; linarith
    · rw [div_le_iff₀ hℓ₀]; linarith

theorem tsum_indicator_annulus {σ g : SL(2, ℝ)} {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀)
    (hg : g = σ * dilSL (Real.exp ℓ₀) (Real.exp_pos _) * σ⁻¹ ∨
      g = -(σ * dilSL (Real.exp ℓ₀) (Real.exp_pos _) * σ⁻¹)) (w : ℍ) :
    ∑' k : ℤ, (σ • dilAnnulus (Real.exp ℓ₀)).indicator (fun _ => (1 : ℝ≥0∞)) ((g ^ k) • w) = 1 := by
  obtain ⟨k₀, hk₀, huniq⟩ := existsUnique_mem_annulus hℓ₀ hg w
  rw [tsum_eq_single k₀ fun k hk => indicator_of_notMem (fun h => hk (huniq k h)) _,
    indicator_of_mem hk₀]

theorem zpow_eq_one_of_frame {σ g : SL(2, ℝ)} {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀)
    (hg : g = σ * dilSL (Real.exp ℓ₀) (Real.exp_pos _) * σ⁻¹ ∨
      g = -(σ * dilSL (Real.exp ℓ₀) (Real.exp_pos _) * σ⁻¹)) {k : ℤ} (hk : g ^ k = 1) : k = 0 := by
  obtain ⟨k₀, hk₀, huniq⟩ := existsUnique_mem_annulus hℓ₀ hg (σ • I)
  have h1 : (g ^ (k₀ + k)) • (σ • I) ∈ σ • dilAnnulus (Real.exp ℓ₀) := by
    rw [zpow_add, hk, mul_one]; exact hk₀
  have := huniq _ h1
  omega

/-! ### Lengths -/

variable {Γ : Subgroup SL(2, ℝ)}

/-- The primitive length: the least length of a nontrivial element commuting with `γ`. -/
def primLen (γ : Γ) : ℝ :=
  sInf {r : ℝ | ∃ δ : Γ, δ ≠ 1 ∧ δ * γ = γ * δ ∧ hypLen (δ : SL(2, ℝ)) = r}

theorem hypLen_conj (c γ : Γ) : hypLen ((c * γ * c⁻¹ : Γ) : SL(2, ℝ)) = hypLen (γ : SL(2, ℝ)) := by
  simp only [hypLen, Subgroup.coe_mul, Subgroup.coe_inv, trSL_conj]

theorem primLen_conj (c γ : Γ) : primLen (c * γ * c⁻¹) = primLen γ := by
  unfold primLen
  congr 1
  ext r
  constructor
  · rintro ⟨δ, hδ1, hδc, rfl⟩
    refine ⟨c⁻¹ * δ * c, fun h => hδ1 ?_, ?_, ?_⟩
    · calc δ = c * (c⁻¹ * δ * c) * c⁻¹ := by group
        _ = 1 := by rw [h]; group
    · have e : c⁻¹ * δ * c * γ = c⁻¹ * (δ * (c * γ * c⁻¹)) * c := by group
      rw [e, hδc]; group
    · simpa using (hypLen_conj c⁻¹ δ)
  · rintro ⟨δ, hδ1, hδc, rfl⟩
    refine ⟨c * δ * c⁻¹, fun h => hδ1 ?_, ?_, hypLen_conj c δ⟩
    · calc δ = c⁻¹ * (c * δ * c⁻¹) * c := by group
        _ = 1 := by rw [h]; group
    · have e : c * δ * c⁻¹ * (c * γ * c⁻¹) = c * (δ * γ) * c⁻¹ := by group
      rw [e, hδc]; group

theorem primLen_eq {γ γ₀ : Γ} {σ : SL(2, ℝ)} {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀)
    (hC : ∀ δ : Γ, δ * γ = γ * δ ↔ ∃ k : ℤ, δ = γ₀ ^ k)
    (hf : (γ₀ : SL(2, ℝ)) = σ * dilSL (Real.exp ℓ₀) (Real.exp_pos _) * σ⁻¹ ∨
      (γ₀ : SL(2, ℝ)) = -(σ * dilSL (Real.exp ℓ₀) (Real.exp_pos _) * σ⁻¹)) :
    primLen γ = ℓ₀ := by
  have hlen : ∀ k : ℤ, hypLen (((γ₀ ^ k : Γ)) : SL(2, ℝ)) = |k| * ℓ₀ := by
    intro k
    rw [Subgroup.coe_zpow, hypLen_zpow_frame hf, abs_mul, abs_of_pos hℓ₀, Int.cast_abs]
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨γ₀, fun h => ?_, (hC γ₀).mpr ⟨1, (zpow_one _).symm⟩, by simpa using hlen 1⟩
    have := zpow_eq_one_of_frame (k := 1) hℓ₀ hf (by rw [zpow_one, h]; rfl)
    omega
  · rintro r ⟨δ, hδ1, hδc, rfl⟩
    obtain ⟨k, rfl⟩ := (hC δ).mp hδc
    have hk : k ≠ 0 := by rintro rfl; exact hδ1 (zpow_zero _)
    rw [hlen]
    have : (1 : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast Int.one_le_abs hk
    nlinarith

/-! ### The class sum -/

namespace CompactQuotient

variable (X : CompactQuotient)

/-- **The orbital integral of a conjugacy class.**  With `N = e^{ℓ(γ)}`,
`Σ_{γ' ~ γ} ∫_F k(u(z, γ'z)) = ℓ₀(γ) ∫_ℝ k((N − 1)²/(4N)·(1 + t²)) dt`. -/
theorem tsum_isConj_lintegral (hhyp : ∀ γ : X.Γ, γ ≠ 1 → 2 < |trSL γ|) (γ : X.Γ) (hγ : γ ≠ 1)
    {k : ℝ → ℝ≥0∞} (hk : Measurable k) :
    ∑' γ' : {γ' : X.Γ // IsConj γ γ'}, ∫⁻ z in X.F, k (pairU z (((γ' : X.Γ) : SL(2, ℝ)) • z)) =
      ENNReal.ofReal (primLen γ) * ∫⁻ t : ℝ,
        k ((Real.exp (hypLen (γ : SL(2, ℝ))) - 1) ^ 2 / (4 * Real.exp (hypLen (γ : SL(2, ℝ)))) *
          (1 + t ^ 2)) := by
  haveI := X.cocompactFree.countable
  obtain ⟨σ, γ₀, ℓ₀, m, hℓ₀, hm, hγm, hC, hf⟩ := exists_primitive_root X.cocompactFree hhyp γ hγ
  set A := σ • dilAnnulus (Real.exp ℓ₀)
  have hAmeas : MeasurableSet A := by
    have : A = (fun w : ℍ => σ⁻¹ • w) ⁻¹' dilAnnulus (Real.exp ℓ₀) := by
      ext w; exact Set.mem_smul_set_iff_inv_smul_mem
    rw [this]
    exact (measurableSet_dilAnnulus _).preimage (continuous_const_smul _).measurable
  -- frame of `γ = γ₀^m`
  have hfγ := zpow_frame hf m
  have hγSL : (γ : SL(2, ℝ)) = (γ₀ : SL(2, ℝ)) ^ (m : ℤ) := by
    rw [hγm, Subgroup.coe_pow, zpow_natCast]
  rw [← hγSL] at hfγ
  simp only [Int.cast_natCast] at hfγ
  have hlenγ : hypLen (γ : SL(2, ℝ)) = m * ℓ₀ := by
    rw [hypLen_conj_dilSL _ σ hfγ, Real.log_exp, abs_of_pos (by positivity)]
  rw [primLen_eq hℓ₀ hC hf, hlenγ]
  -- the right side is the annulus integral
  have hRHS : ∫⁻ w in A, k (pairU w ((γ : SL(2, ℝ)) • w)) =
      ENNReal.ofReal ℓ₀ * ∫⁻ t : ℝ, k ((Real.exp (m * ℓ₀) - 1) ^ 2 / (4 * Real.exp (m * ℓ₀)) *
        (1 + t ^ 2)) := by
    have h := lintegral_smul_annulus_pairU_conj hk (Real.exp_pos ((m : ℝ) * ℓ₀))
      (Real.one_lt_exp_iff.mpr hℓ₀) σ
    rw [Real.log_exp] at h
    rw [← h]
    refine setLIntegral_congr_fun hAmeas fun w _ => ?_
    rw [smul_frame hfγ]
  rw [← hRHS]
  -- unfold the fundamental domain
  have hunf : ∫⁻ w in A, k (pairU w ((γ : SL(2, ℝ)) • w)) =
      ∑' δ : X.Γ, ∫⁻ z in X.F, A.indicator (fun _ => (1 : ℝ≥0∞)) (((δ : X.Γ) : SL(2, ℝ)) • z) *
        k (pairU z ((((δ⁻¹ * γ * δ : X.Γ)) : SL(2, ℝ)) • z)) := by
    rw [← lintegral_indicator hAmeas, X.isFundamentalDomain.lintegral_eq_tsum']
    rw [← (Equiv.inv X.Γ).tsum_eq]
    refine tsum_congr fun δ => setLIntegral_congr_fun X.measurableSet_F fun z _ => ?_
    simp only [Equiv.inv_apply, inv_inv]
    rw [show δ • z = ((δ : X.Γ) : SL(2, ℝ)) • z from rfl]
    by_cases hz : (((δ : X.Γ) : SL(2, ℝ)) • z) ∈ A
    · rw [indicator_of_mem hz, indicator_of_mem hz, one_mul]
      congr 1
      rw [show (((δ⁻¹ * γ * δ : X.Γ)) : SL(2, ℝ)) =
          ((δ : X.Γ) : SL(2, ℝ))⁻¹ * (γ : SL(2, ℝ)) * ((δ : X.Γ) : SL(2, ℝ)) by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv],
        mul_smul, mul_smul, ← pairU_smul ((δ : X.Γ) : SL(2, ℝ)) z, smul_inv_smul]
    · rw [indicator_of_notMem hz, indicator_of_notMem hz, zero_mul]
  rw [hunf]
  -- regroup by the conjugate `δ⁻¹γδ`
  let φ : X.Γ → {γ' : X.Γ // IsConj γ γ'} := fun δ =>
    ⟨δ⁻¹ * γ * δ, isConj_iff.mpr ⟨δ⁻¹, by group⟩⟩
  rw [← (Equiv.sigmaFiberEquiv φ).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun γ' => ?_
  rw [← lintegral_tsum fun δ => ?_]
  swap
  · refine (Measurable.mul ?_ ?_).aemeasurable
    · exact (measurable_const.indicator hAmeas).comp (continuous_const_smul _).measurable
    · exact hk.comp ((continuous_pairU.comp (continuous_id.prodMk
        (continuous_const_smul _))).measurable)
  refine setLIntegral_congr_fun X.measurableSet_F fun z _ => ?_
  -- the fibre over `γ'` is `⟨γ₀⟩δ₁`
  obtain ⟨c, hc⟩ := isConj_iff.mp γ'.2
  obtain ⟨δ₁, rfl⟩ : ∃ d : X.Γ, c = d⁻¹ := ⟨c⁻¹, (inv_inv c).symm⟩
  have hδ₁ : δ₁⁻¹ * γ * δ₁ = γ' := by rw [← hc]; group
  have hfib : ∀ δ : X.Γ, φ δ = γ' ↔ ∃ j : ℤ, δ = γ₀ ^ j * δ₁ := by
    intro δ
    constructor
    · intro h
      have h' : δ⁻¹ * γ * δ = δ₁⁻¹ * γ * δ₁ := by rw [hδ₁]; exact congrArg Subtype.val h
      obtain ⟨j, hj⟩ := (hC (δ * δ₁⁻¹)).mp (by
        calc δ * δ₁⁻¹ * γ = δ * (δ₁⁻¹ * γ * δ₁) * δ₁⁻¹ := by group
          _ = δ * (δ⁻¹ * γ * δ) * δ₁⁻¹ := by rw [← h']
          _ = γ * (δ * δ₁⁻¹) := by group)
      exact ⟨j, by rw [← hj]; group⟩
    · rintro ⟨j, rfl⟩
      apply Subtype.ext
      have hcomm : γ₀ ^ j * γ = γ * γ₀ ^ j := (hC _).mpr ⟨j, rfl⟩
      show (γ₀ ^ j * δ₁)⁻¹ * γ * (γ₀ ^ j * δ₁) = γ'
      calc (γ₀ ^ j * δ₁)⁻¹ * γ * (γ₀ ^ j * δ₁) = δ₁⁻¹ * ((γ₀ ^ j)⁻¹ * (γ * γ₀ ^ j)) * δ₁ := by
            group
        _ = δ₁⁻¹ * γ * δ₁ := by rw [← hcomm]; group
        _ = γ' := hδ₁
  have hinj : Function.Injective fun j : ℤ => γ₀ ^ j * δ₁ := by
    intro j j' h
    have h1 : γ₀ ^ (j - j') = 1 := by
      have := mul_right_cancel h
      rw [zpow_sub, this, mul_inv_cancel]
    have h2 : ((γ₀ : SL(2, ℝ))) ^ (j - j') = 1 := by
      rw [← Subgroup.coe_zpow, h1]; rfl
    have := zpow_eq_one_of_frame hℓ₀ hf h2
    omega
  let e : ℤ ≃ {δ : X.Γ // φ δ = γ'} :=
    Equiv.ofBijective (fun j => ⟨γ₀ ^ j * δ₁, (hfib _).mpr ⟨j, rfl⟩⟩)
      ⟨fun j j' h => hinj (congrArg Subtype.val h), fun ⟨δ, hδ⟩ => by
        obtain ⟨j, hj⟩ := (hfib δ).mp hδ
        exact ⟨j, Subtype.ext hj.symm⟩⟩
  have hconj : ∀ δ : {δ : X.Γ // φ δ = γ'}, ((((δ : X.Γ)⁻¹ * γ * δ : X.Γ)) : SL(2, ℝ)) =
      ((γ' : X.Γ) : SL(2, ℝ)) := fun δ => congrArg (fun x : {γ' : X.Γ // IsConj γ γ'} =>
        ((x : X.Γ) : SL(2, ℝ))) δ.2
  simp only [Equiv.sigmaFiberEquiv_apply]
  simp_rw [hconj]
  rw [ENNReal.tsum_mul_right, ← e.tsum_eq]
  simp only [e, Equiv.ofBijective_apply, Subgroup.coe_mul, mul_smul, Subgroup.coe_zpow]
  rw [tsum_indicator_annulus hℓ₀ hf, one_mul]

end CompactQuotient

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
