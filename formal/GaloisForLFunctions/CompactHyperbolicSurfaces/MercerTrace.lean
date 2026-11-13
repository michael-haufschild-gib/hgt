import GaloisForLFunctions.CompactHyperbolicSurfaces.MercerBound
import GaloisForLFunctions.HTGeometry.CompactOperatorDiscreteSpectrum

/-!
# Mercer's theorem for `P = T_a − T_b` and the trace of `P`

Let `K(z, w) = Σ_γ (k_a − k_b)(u(z, γw))` be the continuous bounded kernel of the positive operator
`P = T_a − T_b`, with eigenvalues `ν_j > 0` on the eigenvectors `e_j`, and let `φ_j = √ν_j ẽ_j` be
the normalized continuous eigenfunctions.

* Bessel gives `Σ_{j ∈ S} |φ_j(w)|² ≤ B` uniformly in `S` and `w`; hence the Mercer series
  `Ψ(z, w) = Σ_j \overline{φ_j(z)} φ_j(w)` converges, and is continuous in `w`
  (`continuous_tsum_mul_of_bounded`).
* The row `K(z, ·)` lies in the closed span of the `e_j` (vectors orthogonal to all `e_j` have
  vanishing transform), so `K(z, ·) = Σ_j ⟨e_j, K(z, ·)⟩ e_j` in `L²`, and by Fatou
  `K(z, ·) = Ψ(z, ·)` almost everywhere.
* Both sides are continuous and `Γ`-invariant, so `K = Ψ` everywhere (`diffKer_eq_mercerKer`);
  on the diagonal `K(z, z) = Σ_j |φ_j(z)|²`.
* Integrating over `F`: `Σ_j ν_j = ∫_F K(z, z) dz` (`hasSum_nu`).
-/

open MeasureTheory Set Filter UpperHalfPlane Real Metric Module.End Topology
open scoped ENNReal MatrixGroups Pointwise InnerProductSpace

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.SchurKernel

noncomputable section

/-- `Σ ‖c_j‖² < ∞` and `Σ ‖g_j‖² < ∞` give a summable product. -/
theorem summable_mul_of_sq {ι : Type*} {c g : ι → ℂ} (hc : Summable fun j => ‖c j‖ ^ 2)
    (hg : Summable fun j => ‖g j‖ ^ 2) : Summable fun j => c j * g j :=
  Summable.of_norm_bounded (hc.add hg) fun j => by
    rw [norm_mul]
    nlinarith [sq_nonneg (‖c j‖ - ‖g j‖), norm_nonneg (c j), norm_nonneg (g j)]

/-- **Pairing a fixed `ℓ²` vector with a bounded continuous family.**  If `Σ ‖c_j‖² < ∞`, the `g_j`
are continuous and `Σ_{j ∈ S} ‖g_j(y)‖² ≤ B` for all finite `S` and all `y`, then
`y ↦ Σ_j c_j g_j(y)` is continuous: by Cauchy–Schwarz the tails are uniformly small. -/
theorem continuous_tsum_mul_of_bounded {ι Y : Type*} [TopologicalSpace Y] {c : ι → ℂ}
    {g : ι → Y → ℂ} (hc : Summable fun j => ‖c j‖ ^ 2) (hg : ∀ j, Continuous (g j)) {B : ℝ}
    (hB : ∀ (S : Finset ι) (y : Y), ∑ j ∈ S, ‖g j y‖ ^ 2 ≤ B) :
    Continuous fun y => ∑' j, c j * g j y := by
  classical
  have hsum : ∀ y, Summable fun j => c j * g j y := fun y =>
    summable_mul_of_sq hc (summable_of_sum_le (fun j => sq_nonneg _) fun S => hB S y)
  refine TendstoUniformly.continuous (F := fun (S : Finset ι) y => ∑ j ∈ S, c j * g j y)
    (p := atTop) ?_ (Frequently.of_forall fun S =>
      continuous_finsetSum _ fun j _ => continuous_const.mul (hg j))
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  set δ := ε ^ 2 / (2 * (|B| + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨S₀, hS₀⟩ := hc.vanishing (Iio_mem_nhds hδ)
  filter_upwards [eventually_ge_atTop S₀] with S hS y
  have htail : ∀ T : Finset ι, S ⊆ T →
      ‖∑ j ∈ T, c j * g j y - ∑ j ∈ S, c j * g j y‖ ^ 2 ≤ δ * |B| := by
    intro T hST
    rw [← Finset.sum_sdiff hST, add_sub_cancel_right]
    have h1 : ∑ j ∈ T \ S, ‖c j‖ ^ 2 < δ :=
      hS₀ (T \ S) (Finset.disjoint_of_subset_right hS Finset.sdiff_disjoint)
    calc ‖∑ j ∈ T \ S, c j * g j y‖ ^ 2 ≤ (∑ j ∈ T \ S, ‖c j‖ * ‖g j y‖) ^ 2 := by
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
      _ ≤ (∑ j ∈ T \ S, ‖c j‖ ^ 2) * ∑ j ∈ T \ S, ‖g j y‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ δ * |B| := mul_le_mul h1.le ((hB _ y).trans (le_abs_self B))
          (Finset.sum_nonneg fun j _ => sq_nonneg _) hδ.le
  have hlim : Tendsto (fun T : Finset ι => ‖∑ j ∈ T, c j * g j y - ∑ j ∈ S, c j * g j y‖ ^ 2)
      atTop (𝓝 (‖∑' j, c j * g j y - ∑ j ∈ S, c j * g j y‖ ^ 2)) :=
    ((Tendsto.sub_const (hsum y).hasSum _).norm).pow 2
  have hle := le_of_tendsto hlim ((eventually_ge_atTop S).mono fun T hT => htail T hT)
  rw [dist_eq_norm]
  have hlt : ‖∑' j, c j * g j y - ∑ j ∈ S, c j * g j y‖ ^ 2 < ε ^ 2 := by
    refine lt_of_le_of_lt hle ?_
    rw [hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    have := sq_pos_of_pos hε
    nlinarith [abs_nonneg B]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt

namespace CompactQuotient

variable (X : CompactQuotient) {a b : ℝ} (ha : 1 < a)

/-- The spectral index set is countable: it injects into (eigenvalues) × ℕ. -/
instance countable_specIndex : Countable (X.SpecIndex ha) := by
  have hc := countable_setOf_hasEigenvalue (𝕜 := ℂ)
    (T := (X.resOp ha : Lp ℂ 2 X.μ →ₗ[ℂ] Lp ℂ 2 X.μ)) (X.isCompactOperator_resOp ha)
    (X.isSymmetric_resOp ha)
  haveI := hc.to_subtype
  refine Function.Injective.countable (f := fun j : X.SpecIndex ha =>
    ((⟨j.1.1, hasEigenvalue_of_hasEigenvector ⟨eigenVec_mem _ j, X.specVec_ne_zero ha j⟩⟩ :
      {μ : ℂ | HasEigenvalue (X.resOp ha : Lp ℂ 2 X.μ →ₗ[ℂ] Lp ℂ 2 X.μ) μ}), (j.2 : ℕ))) ?_
  rintro ⟨⟨μ, hμ⟩, k⟩ ⟨⟨μ', hμ'⟩, k'⟩ h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  obtain ⟨rfl, hk⟩ := h
  exact Sigma.ext rfl (heq_of_eq (Fin.ext hk))

/-! ### The normalized continuous eigenfunctions -/

/-- `φ_j = √ν_j ẽ_j`. -/
def normRep (j : X.SpecIndex ha) (w : ℍ) : ℂ :=
  ((Real.sqrt (X.nu ha (b := b) j) : ℝ) : ℂ) * X.specRep ha (b := b) j w

theorem norm_normRep_sq (hab : a < b) (j : X.SpecIndex ha) (w : ℍ) :
    ‖X.normRep ha (b := b) j w‖ ^ 2 = X.nu ha (b := b) j * ‖X.specRep ha (b := b) j w‖ ^ 2 := by
  rw [normRep, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt (X.nu_pos ha hab j).le]

theorem continuous_normRep (hab : a < b) (j : X.SpecIndex ha) :
    Continuous (X.normRep ha (b := b) j) :=
  continuous_const.mul (X.continuous_specRep ha hab j)

theorem normRep_smul (hab : a < b) (j : X.SpecIndex ha) (γ : X.Γ) (w : ℍ) :
    X.normRep ha (b := b) j ((γ : SL(2, ℝ)) • w) = X.normRep ha (b := b) j w := by
  rw [normRep, normRep, X.specRep_smul ha hab]

theorem exists_sum_normRep_le (hab : a < b) : ∃ B : ℝ, ∀ (S : Finset (X.SpecIndex ha)) (w : ℍ),
    ∑ j ∈ S, ‖X.normRep ha (b := b) j w‖ ^ 2 ≤ B := by
  obtain ⟨B, hB⟩ := X.exists_sum_nu_specRep_le ha hab
  exact ⟨B, fun S w => by simpa only [X.norm_normRep_sq ha hab] using hB S w⟩

theorem summable_normRep_sq (hab : a < b) (w : ℍ) :
    Summable fun j => ‖X.normRep ha (b := b) j w‖ ^ 2 := by
  obtain ⟨B, hB⟩ := X.exists_sum_normRep_le ha hab
  exact summable_of_sum_le (fun j => sq_nonneg _) fun S => hB S w

/-- `∫_F |φ_j|² = ν_j`. -/
theorem lintegral_normRep_sq (hab : a < b) (j : X.SpecIndex ha) :
    ∫⁻ w, ‖X.normRep ha (b := b) j w‖ₑ ^ 2 ∂X.μ = ENNReal.ofReal (X.nu ha (b := b) j) := by
  have hae : ∀ᵐ w ∂X.μ, X.normRep ha (b := b) j w =
      ((((Real.sqrt (X.nu ha (b := b) j) : ℝ) : ℂ) • X.specVec ha j : Lp ℂ 2 X.μ) : ℍ → ℂ) w := by
    filter_upwards [X.ae_eq_specRep ha hab j,
      Lp.coeFn_smul (((Real.sqrt (X.nu ha (b := b) j) : ℝ) : ℂ)) (X.specVec ha j)] with w h1 h2
    rw [h2, Pi.smul_apply, smul_eq_mul, h1, normRep]
  calc ∫⁻ w, ‖X.normRep ha (b := b) j w‖ₑ ^ 2 ∂X.μ
      = ∫⁻ w, ‖((((Real.sqrt (X.nu ha (b := b) j) : ℝ) : ℂ) • X.specVec ha j :
          Lp ℂ 2 X.μ) : ℍ → ℂ) w‖ₑ ^ 2 ∂X.μ :=
        lintegral_congr_ae (by filter_upwards [hae] with w hw; rw [hw])
    _ = ‖(((Real.sqrt (X.nu ha (b := b) j) : ℝ) : ℂ) • X.specVec ha j : Lp ℂ 2 X.μ)‖ₑ ^ 2 := by
        rw [Lp.enorm_def, eLpNorm_two_sq]
    _ = ENNReal.ofReal (X.nu ha (b := b) j) := by
        rw [← ofReal_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _),
          (orthonormal_eigenVec (X.isSymmetric_resOp ha)).1 j, mul_one,
          ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (X.nu_pos ha hab j).le]

/-! ### The Mercer series -/

/-- `Ψ(z, w) = Σ_j \overline{φ_j(z)} φ_j(w)`. -/
def mercerKer (z w : ℍ) : ℂ :=
  ∑' j, starRingEnd ℂ (X.normRep ha (b := b) j z) * X.normRep ha (b := b) j w

/-- The partial sums of the Mercer series. -/
def mercerPartial (S : Finset (X.SpecIndex ha)) (z w : ℍ) : ℂ :=
  ∑ j ∈ S, starRingEnd ℂ (X.normRep ha (b := b) j z) * X.normRep ha (b := b) j w

theorem summable_mercer (hab : a < b) (z w : ℍ) :
    Summable fun j => starRingEnd ℂ (X.normRep ha (b := b) j z) * X.normRep ha (b := b) j w :=
  summable_mul_of_sq (by simpa only [RCLike.norm_conj] using X.summable_normRep_sq ha hab z)
    (X.summable_normRep_sq ha hab w)

theorem tendsto_mercerPartial (hab : a < b) (z w : ℍ) :
    Tendsto (fun S => X.mercerPartial ha (b := b) S z w) atTop
      (𝓝 (X.mercerKer ha (b := b) z w)) :=
  (X.summable_mercer ha hab z w).hasSum

theorem continuous_mercerKer_right (hab : a < b) (z : ℍ) :
    Continuous (X.mercerKer ha (b := b) z) := by
  obtain ⟨B, hB⟩ := X.exists_sum_normRep_le ha hab
  show Continuous fun w =>
    ∑' j, starRingEnd ℂ (X.normRep ha (b := b) j z) * X.normRep ha (b := b) j w
  exact continuous_tsum_mul_of_bounded
    (by simpa only [RCLike.norm_conj] using X.summable_normRep_sq ha hab z)
    (X.continuous_normRep ha hab) hB

theorem mercerKer_smul_right (hab : a < b) (z : ℍ) (γ : X.Γ) (w : ℍ) :
    X.mercerKer ha (b := b) z ((γ : SL(2, ℝ)) • w) = X.mercerKer ha (b := b) z w := by
  simp only [mercerKer, X.normRep_smul ha hab]

/-! ### The rows of `K` and their eigen-expansion -/

include ha in
theorem memLp_kerRow (hab : a < b) (z : ℍ) :
    MemLp (fun w => ((X.diffKer a b z w : ℝ) : ℂ)) 2 X.μ := by
  obtain ⟨B, -, hB⟩ := X.exists_diffKer_le ha hab
  refine MemLp.of_bound (Complex.continuous_ofReal.comp ((X.continuous_diffKer ha hab).comp
    (continuous_const.prodMk continuous_id))).aestronglyMeasurable B
    (Eventually.of_forall fun w => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (X.diffKer_nonneg hab _ _)]
  exact hB z w

/-- The row `K(z, ·)` as an `L²` vector. -/
def kerVec (hab : a < b) (z : ℍ) : Lp ℂ 2 X.μ := (X.memLp_kerRow ha hab z).toLp _

theorem coeFn_kerVec (hab : a < b) (z : ℍ) :
    (X.kerVec ha hab z : ℍ → ℂ) =ᵐ[X.μ] fun w => ((X.diffKer a b z w : ℝ) : ℂ) :=
  MemLp.coeFn_toLp _

theorem inner_kerVec_left (hab : a < b) (z : ℍ) (f : Lp ℂ 2 X.μ) :
    ⟪X.kerVec ha hab z, f⟫_ℂ = X.kerApply (a := a) (b := b) f z := by
  rw [L2.inner_def, kerApply]
  refine integral_congr_ae ?_
  filter_upwards [X.coeFn_kerVec ha hab z] with w hw
  rw [hw, RCLike.inner_apply', Complex.conj_ofReal]

theorem kerApply_specVec (hab : a < b) (j : X.SpecIndex ha) (z : ℍ) :
    X.kerApply (a := a) (b := b) (X.specVec ha j) z =
      ((X.nu ha (b := b) j : ℝ) : ℂ) * X.specRep ha (b := b) j z := by
  have hν : ((X.nu ha (b := b) j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (X.nu_pos ha hab j).ne'
  rw [specRep, ← mul_assoc, mul_inv_cancel₀ hν, one_mul]

/-- `⟨e_j, K(z, ·)⟩ = √ν_j \overline{φ_j(z)}`. -/
theorem inner_specVec_kerVec (hab : a < b) (j : X.SpecIndex ha) (z : ℍ) :
    ⟪X.specVec ha j, X.kerVec ha hab z⟫_ℂ =
      ((Real.sqrt (X.nu ha (b := b) j) : ℝ) : ℂ) * starRingEnd ℂ (X.normRep ha (b := b) j z) := by
  rw [← inner_conj_symm, X.inner_kerVec_left ha hab, X.kerApply_specVec ha hab, normRep]
  simp only [map_mul, Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (X.nu_pos ha hab j).le]

/-- **Completeness for the rows.**  `K(z, ·) = Σ_j ⟨e_j, K(z, ·)⟩ e_j` in `L²`: extend the `e_j` to
a Hilbert basis; the added vectors are orthogonal to every `e_j`, hence to `K(z, ·)`. -/
theorem hasSum_kerVec (hab : a < b) (z : ℍ) :
    HasSum (fun j => ⟪X.specVec ha j, X.kerVec ha hab z⟫_ℂ • X.specVec ha j)
      (X.kerVec ha hab z) := by
  have hon := orthonormal_eigenVec (X.isSymmetric_resOp ha)
  obtain ⟨W, bas, hsub, hbas⟩ := hon.toSubtypeRange.exists_hilbertBasis_extension
  have hrepr := bas.hasSum_repr (X.kerVec ha hab z)
  simp only [HilbertBasis.repr_apply_apply, hbas] at hrepr
  have hinj : Function.Injective fun j : X.SpecIndex ha =>
      (⟨X.specVec ha j, hsub (Set.mem_range_self j)⟩ : W) := fun j j' h =>
    hon.linearIndependent.injective (congrArg Subtype.val h)
  refine (hinj.hasSum_iff (f := fun i : W => ⟪(i : Lp ℂ 2 X.μ), X.kerVec ha hab z⟫_ℂ •
    (i : Lp ℂ 2 X.μ)) fun i hi => ?_).mpr hrepr
  have horth : ∀ j, ⟪X.specVec ha j, (i : Lp ℂ 2 X.μ)⟫_ℂ = 0 := by
    intro j
    have hne : (⟨X.specVec ha j, hsub (Set.mem_range_self j)⟩ : W) ≠ i := fun h => hi ⟨j, h⟩
    simpa [hbas] using bas.orthonormal.2 hne
  show ⟪(i : Lp ℂ 2 X.μ), X.kerVec ha hab z⟫_ℂ • (i : Lp ℂ 2 X.μ) = 0
  rw [← inner_conj_symm, X.inner_kerVec_left ha hab,
    X.kerApply_eq_zero_of_orthogonal ha hab horth, map_zero, zero_smul]

/-- **Mercer, almost everywhere.**  `K(z, w) = Ψ(z, w)` for almost every `w` (Fatou along the
partial sums, whose `L²` distance to the row tends to zero). -/
theorem ae_eq_mercerKer (hab : a < b) (z : ℍ) :
    ∀ᵐ w ∂X.μ, ((X.diffKer a b z w : ℝ) : ℂ) = X.mercerKer ha (b := b) z w := by
  have hsmul : ∀ᵐ w ∂X.μ, ∀ j, ((⟪X.specVec ha j, X.kerVec ha hab z⟫_ℂ • X.specVec ha j :
      Lp ℂ 2 X.μ) : ℍ → ℂ) w =
        starRingEnd ℂ (X.normRep ha (b := b) j z) * X.normRep ha (b := b) j w := by
    rw [ae_all_iff]
    intro j
    filter_upwards [Lp.coeFn_smul (⟪X.specVec ha j, X.kerVec ha hab z⟫_ℂ) (X.specVec ha j),
      X.ae_eq_specRep ha hab j] with w h1 h3
    rw [h1, Pi.smul_apply, smul_eq_mul, h3, X.inner_specVec_kerVec ha hab]
    simp only [normRep]
    ring
  have hcoe : ∀ S : Finset (X.SpecIndex ha), ∀ᵐ w ∂X.μ,
      ((X.kerVec ha hab z - ∑ j ∈ S, ⟪X.specVec ha j, X.kerVec ha hab z⟫_ℂ • X.specVec ha j :
        Lp ℂ 2 X.μ) : ℍ → ℂ) w =
        ((X.diffKer a b z w : ℝ) : ℂ) - X.mercerPartial ha (b := b) S z w := by
    intro S
    filter_upwards [Lp.coeFn_sub (X.kerVec ha hab z)
        (∑ j ∈ S, ⟪X.specVec ha j, X.kerVec ha hab z⟫_ℂ • X.specVec ha j),
      X.coeFn_kerVec ha hab z,
      Lp.coeFn_fun_finsetSum S (fun j => ⟪X.specVec ha j, X.kerVec ha hab z⟫_ℂ • X.specVec ha j),
      hsmul] with w h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3, mercerPartial]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => h4 j)
  have hL : ∀ S : Finset (X.SpecIndex ha),
      ∫⁻ w, ‖((X.diffKer a b z w : ℝ) : ℂ) - X.mercerPartial ha (b := b) S z w‖ₑ ^ 2 ∂X.μ =
        ‖X.kerVec ha hab z -
          ∑ j ∈ S, ⟪X.specVec ha j, X.kerVec ha hab z⟫_ℂ • X.specVec ha j‖ₑ ^ 2 := by
    intro S
    rw [Lp.enorm_def, eLpNorm_two_sq]
    refine lintegral_congr_ae ?_
    filter_upwards [hcoe S] with w hw
    rw [hw]
  have hint : Tendsto (fun S : Finset (X.SpecIndex ha) =>
      ∫⁻ w, ‖((X.diffKer a b z w : ℝ) : ℂ) - X.mercerPartial ha (b := b) S z w‖ₑ ^ 2 ∂X.μ)
      atTop (𝓝 0) := by
    simp_rw [hL]
    have hP : Tendsto (fun S : Finset (X.SpecIndex ha) =>
        ∑ j ∈ S, ⟪X.specVec ha j, X.kerVec ha hab z⟫_ℂ • X.specVec ha j) atTop
        (𝓝 (X.kerVec ha hab z)) := X.hasSum_kerVec ha hab z
    have h := ENNReal.Tendsto.pow (n := 2) (hP.const_sub (X.kerVec ha hab z)).enorm
    simpa only [sub_self, enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] using h
  have hcont : ∀ S : Finset (X.SpecIndex ha),
      Continuous fun w => ((X.diffKer a b z w : ℝ) : ℂ) - X.mercerPartial ha (b := b) S z w :=
    fun S => (Complex.continuous_ofReal.comp ((X.continuous_diffKer ha hab).comp
      (continuous_const.prodMk continuous_id))).sub
      (continuous_finsetSum _ fun j _ => continuous_const.mul (X.continuous_normRep ha hab j))
  have hfatou := lintegral_liminf_le (μ := X.μ) (u := (atTop : Filter (Finset (X.SpecIndex ha))))
    fun S => (hcont S).enorm.measurable.pow_const 2
  have hpt : ∀ w, liminf (fun S : Finset (X.SpecIndex ha) =>
      ‖((X.diffKer a b z w : ℝ) : ℂ) - X.mercerPartial ha (b := b) S z w‖ₑ ^ 2) atTop =
      ‖((X.diffKer a b z w : ℝ) : ℂ) - X.mercerKer ha (b := b) z w‖ₑ ^ 2 := fun w =>
    (ENNReal.Tendsto.pow (((X.tendsto_mercerPartial ha hab z w).const_sub _).enorm)).liminf_eq
  simp only [hpt, hint.liminf_eq] at hfatou
  have h0 : ∫⁻ w, ‖((X.diffKer a b z w : ℝ) : ℂ) - X.mercerKer ha (b := b) z w‖ₑ ^ 2 ∂X.μ = 0 :=
    le_antisymm hfatou bot_le
  have hmeas : Measurable fun w =>
      ‖((X.diffKer a b z w : ℝ) : ℂ) - X.mercerKer ha (b := b) z w‖ₑ ^ 2 :=
    ((Complex.continuous_ofReal.comp ((X.continuous_diffKer ha hab).comp
      (continuous_const.prodMk continuous_id))).sub
      (X.continuous_mercerKer_right ha hab z)).enorm.measurable.pow_const 2
  filter_upwards [(lintegral_eq_zero_iff hmeas).mp h0] with w hw
  have h : ‖((X.diffKer a b z w : ℝ) : ℂ) - X.mercerKer ha (b := b) z w‖ₑ ^ 2 = 0 := hw
  rwa [pow_eq_zero_iff two_ne_zero, enorm_eq_zero, sub_eq_zero] at h

/-- **Mercer's theorem.**  `K(z, w) = Σ_j \overline{φ_j(z)} φ_j(w)` for all `z, w`. -/
theorem diffKer_eq_mercerKer (hab : a < b) (z w : ℍ) :
    ((X.diffKer a b z w : ℝ) : ℂ) = X.mercerKer ha (b := b) z w := by
  have h := X.eq_zero_of_ae_eq_zero
    (g := fun w => ((X.diffKer a b z w : ℝ) : ℂ) - X.mercerKer ha (b := b) z w)
    ((Complex.continuous_ofReal.comp ((X.continuous_diffKer ha hab).comp
      (continuous_const.prodMk continuous_id))).sub (X.continuous_mercerKer_right ha hab z))
    (fun γ w => by simp only [X.diffKer_smul_right ha hab, X.mercerKer_smul_right ha hab])
    (by
      filter_upwards [X.ae_eq_mercerKer ha hab z] with w hw
      show ((X.diffKer a b z w : ℝ) : ℂ) - X.mercerKer ha (b := b) z w = 0
      rw [hw, sub_self])
  exact sub_eq_zero.mp (congrFun h w)

/-- **The diagonal.**  `K(z, z) = Σ_j |φ_j(z)|²`. -/
theorem diffKer_self_eq_tsum (hab : a < b) (z : ℍ) :
    X.diffKer a b z z = ∑' j, ‖X.normRep ha (b := b) j z‖ ^ 2 := by
  have h := X.diffKer_eq_mercerKer ha hab z z
  have h2 : ∀ j, starRingEnd ℂ (X.normRep ha (b := b) j z) * X.normRep ha (b := b) j z =
      ((‖X.normRep ha (b := b) j z‖ ^ 2 : ℝ) : ℂ) := fun j => by
    rw [Complex.conj_mul']; push_cast; rfl
  rw [mercerKer, tsum_congr h2, ← Complex.ofReal_tsum] at h
  exact_mod_cast h

/-- **The trace of `P = T_a − T_b`.**  `Σ_j ν_j = ∫_F K(z, z) dz`. -/
theorem hasSum_nu (hab : a < b) :
    HasSum (fun j => X.nu ha (b := b) j) (∫ z, X.diffKer a b z z ∂X.μ) := by
  have hdiag : ∀ z, ∑' j, ‖X.normRep ha (b := b) j z‖ₑ ^ 2 =
      ENNReal.ofReal (X.diffKer a b z z) := by
    intro z
    rw [X.diffKer_self_eq_tsum ha hab z, ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _)
      (X.summable_normRep_sq ha hab z)]
    refine tsum_congr fun j => ?_
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  have htot : ∑' j, ENNReal.ofReal (X.nu ha (b := b) j) =
      ∫⁻ z, ENNReal.ofReal (X.diffKer a b z z) ∂X.μ := by
    simp_rw [← X.lintegral_normRep_sq ha hab, ← hdiag]
    exact (lintegral_tsum fun j =>
      ((X.continuous_normRep ha hab j).enorm.measurable.pow_const 2).aemeasurable).symm
  have hcont : Continuous fun z => X.diffKer a b z z :=
    (X.continuous_diffKer ha hab).comp (continuous_id.prodMk continuous_id)
  obtain ⟨B, -, hB⟩ := X.exists_diffKer_le ha hab
  have hfin : ∫⁻ z, ENNReal.ofReal (X.diffKer a b z z) ∂X.μ < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hB z z)) ?_
    rw [lintegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hsum : Summable fun j => X.nu ha (b := b) j := by
    have := ENNReal.summable_toReal (htot ▸ hfin.ne)
    simpa only [ENNReal.toReal_ofReal (X.nu_pos ha hab _).le] using this
  have hval : ∑' j, X.nu ha (b := b) j = ∫ z, X.diffKer a b z z ∂X.μ := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => X.diffKer_nonneg hab z z)
      hcont.aestronglyMeasurable, ← htot, ENNReal.tsum_toReal_eq fun _ => ENNReal.ofReal_ne_top]
    exact tsum_congr fun j => (ENNReal.toReal_ofReal (X.nu_pos ha hab j).le).symm
  rw [← hval]
  exact hsum.hasSum

end CompactQuotient

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
