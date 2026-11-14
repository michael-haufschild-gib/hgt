import GaloisForLFunctions.CompactHyperbolicSurfaces.BergmanKernel
import GaloisForLFunctions.CompactHyperbolicSurfaces.ResolventOperators
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact
import GaloisForLFunctions.HTGeometry.FiniteRankDeterminant

/-!
# Bergman projections of a compact surface

For `j ≥ 0` and the even weight `m = 2(j + 2)`, the automorphic Bergman kernel of `X = Γ\ℍ` is

  `K(z, w) = c Σ_γ h(z, γw)^m ε_γ(w)^m`,  `c = (2j + 3)/4π`   (`bergAut`).

* The series converges absolutely, `|h(z, γw)^m ε_γ(w)^m| = (1 + u(z, γw))^{−(j+2)}`; `K` is
  bounded, continuous, hermitian (`bergAut_swap`), and `K(γz, w) = ε_γ(z)^m K(z, w)`
  (`bergAut_smul_left`).
* **Idempotency** (`integral_bergAut_mul`): `∫_F K(z, y) K(y, w) dμ(y) = K(z, w)`.  Indeed
  `K(z, y) K(y, w) = c Σ_γ Ψ(γy)` with `Ψ(y) = h(z, y)^m K(y, w)`, which unfolds to `c ∫_ℍ Ψ`, and
  the reproducing identity `∫_ℍ h(z, y)^m h(y, δw)^m = c⁻¹ h(z, δw)^m` gives `c ∫_ℍ Ψ = K(z, w)`.
* The Schur operator `P` of `K` on `L²(F)` is therefore an idempotent Hilbert–Schmidt operator,
  hence compact with finite-dimensional range, and its trace is that dimension
  (`exists_opTrace_eq_nat`).  By the composition trace formula,
  `tr P = tr P² = ∫_F ∫_F K(z, y) K(y, z) = ∫_F K(y, y)`: **the diagonal integral of `K` is a
  natural number** (`exists_nat_integral_bergAut_diag`).
-/

open MeasureTheory Set Filter UpperHalfPlane Metric
open scoped ENNReal MatrixGroups ComplexConjugate Real

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.SchurKernel

noncomputable section

/-- The Borel structure of `ℍ` is countably generated. -/
instance : MeasurableSpace.CountablyGenerated ℍ :=
  MeasurableSpace.CountablyGenerated.comap UpperHalfPlane.coe

instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩

/-- **Trace of a compact idempotent.**  An idempotent compact operator maps into its
eigenspace for `1`, which is finite-dimensional, and acts there as the identity: its trace is the
dimension of that eigenspace. -/
theorem exists_opTrace_eq_nat {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {P : E →L[ℂ] E} (hidem : P ∘L P = P) (hc : IsCompactOperator P) :
    ∃ n : ℕ, ContinuousLinearMap.opTrace P = n := by
  set V := Module.End.eigenspace (P : E →ₗ[ℂ] E) 1
  haveI : FiniteDimensional ℂ V := ContinuousLinearMap.finite_dimensional_eigenspace hc 1 one_ne_zero
  have hmem : ∀ x, P x ∈ V := fun x => Module.End.mem_eigenspace_iff.mpr (by
    rw [one_smul]; exact congrArg (fun T : E →L[ℂ] E => T x) hidem)
  refine ⟨Module.finrank ℂ V, ?_⟩
  rw [opTrace_eq_trace_restrict hmem]
  have hid : (P : E →ₗ[ℂ] E).restrict (fun x _ => hmem x) = LinearMap.id := by
    ext ⟨v, hv⟩
    have h := Module.End.mem_eigenspace_iff.mp hv
    rw [one_smul] at h
    simp only [LinearMap.restrict_apply, LinearMap.id_apply]
    exact h
  rw [hid, LinearMap.trace_id]

/-! ### The summands -/

/-- The summand `h(z, γw)^m ε_γ(w)^m`, `m = 2(j + 2)`. -/
def bergTerm (j : ℕ) (γ : SL(2, ℝ)) (z w : ℍ) : ℂ :=
  bergK z (γ • w : ℍ) ^ (2 * (j + 2)) * autF γ w ^ (2 * (j + 2))

/-- The Bergman constant `c = (2j + 3)/4π`. -/
def bergC (j : ℕ) : ℝ := (2 * j + 3) / (4 * π)

theorem norm_bergTerm (j : ℕ) (γ : SL(2, ℝ)) (z w : ℍ) :
    ‖bergTerm j γ z w‖ = ((1 + pairU z (γ • w)) ^ (j + 2))⁻¹ := by
  rw [bergTerm, norm_mul, norm_bergK_pow_two_mul, norm_pow, norm_autF, one_pow, mul_one]

theorem inv_pow_eq_rpow (j : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    ((1 + u) ^ (j + 2))⁻¹ = (1 + u) ^ (-((j : ℝ) + 2)) := by
  rw [Real.rpow_neg (by linarith), show (j : ℝ) + 2 = ((j + 2 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]

theorem continuous_bergK : Continuous fun p : ℍ × ℍ => bergK p.1 p.2 := by
  unfold bergK
  refine Continuous.div ?_ ?_ fun p => sub_conj_ne_zero p.1.im_pos p.2.im_pos
  · refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
    exact Real.continuous_sqrt.comp ((Complex.continuous_im.comp (continuous_coe.comp
      continuous_fst)).mul (Complex.continuous_im.comp (continuous_coe.comp continuous_snd)))
  · exact (continuous_coe.comp continuous_fst).sub
      (Complex.continuous_conj.comp (continuous_coe.comp continuous_snd))

theorem continuous_autF (γ : SL(2, ℝ)) : Continuous fun w : ℍ => autF γ w := by
  have hj : Continuous fun w : ℍ => jF γ w := by unfold jF; fun_prop
  refine hj.div (Complex.continuous_ofReal.comp hj.norm) fun w => ?_
  exact_mod_cast norm_ne_zero_iff.mpr (jF_ne_zero γ w)

theorem continuous_bergTerm (j : ℕ) (γ : SL(2, ℝ)) :
    Continuous fun p : ℍ × ℍ => bergTerm j γ p.1 p.2 :=
  ((continuous_bergK.comp (continuous_fst.prodMk ((continuous_const_smul γ).comp
    continuous_snd))).pow _).mul (((continuous_autF γ).comp continuous_snd).pow _)

/-- `\overline{h(z, γw)^m ε_γ(w)^m} = h(w, γ⁻¹z)^m ε_{γ⁻¹}(z)^m`. -/
theorem conj_bergTerm (j : ℕ) (γ : SL(2, ℝ)) (z w : ℍ) :
    conj (bergTerm j γ z w) = bergTerm j γ⁻¹ w z := by
  have h := bergK_smul γ w (γ⁻¹ • z)
  rw [smul_inv_smul] at h
  have hinv : autF γ⁻¹ z = conj (autF γ (γ⁻¹ • z : ℍ)) := by
    have h1 := autF_mul γ γ⁻¹ z
    rw [mul_inv_cancel, autF_one] at h1
    have h2 := conj_autF_mul_self γ (γ⁻¹ • z)
    linear_combination (-conj (autF γ (γ⁻¹ • z : ℍ))) * h1 - autF γ⁻¹ z * h2
  have hw := conj_autF_mul_self γ w
  rw [bergTerm, bergTerm, map_mul, map_pow, map_pow, ← bergK_swap, h, hinv]
  rw [show (bergK w (γ⁻¹ • z : ℍ) * autF γ w * conj (autF γ (γ⁻¹ • z : ℍ))) ^ (2 * (j + 2)) *
      conj (autF γ w) ^ (2 * (j + 2)) = bergK w (γ⁻¹ • z : ℍ) ^ (2 * (j + 2)) *
      conj (autF γ (γ⁻¹ • z : ℍ)) ^ (2 * (j + 2)) * (conj (autF γ w) * autF γ w) ^ (2 * (j + 2))
      by ring, hw, one_pow, mul_one]

/-- `h(γy, γδw)^m ε_{γδ}(w)^m = ε_γ(y)^m h(y, δw)^m ε_δ(w)^m`. -/
theorem bergTerm_mul_smul (j : ℕ) (γ δ : SL(2, ℝ)) (y w : ℍ) :
    bergTerm j (γ * δ) (γ • y) w = autF γ y ^ (2 * (j + 2)) * bergTerm j δ y w := by
  have hc := conj_autF_mul_self γ (δ • w)
  rw [bergTerm, bergTerm, mul_smul, bergK_smul, autF_mul]
  rw [show (bergK y (δ • w : ℍ) * autF γ y * conj (autF γ (δ • w : ℍ))) ^ (2 * (j + 2)) *
      (autF γ (δ • w : ℍ) * autF δ w) ^ (2 * (j + 2)) = autF γ y ^ (2 * (j + 2)) *
      (bergK y (δ • w : ℍ) ^ (2 * (j + 2)) * autF δ w ^ (2 * (j + 2))) *
      (conj (autF γ (δ • w : ℍ)) * autF γ (δ • w : ℍ)) ^ (2 * (j + 2)) by ring, hc, one_pow,
    mul_one]

namespace CompactQuotient

variable (X : CompactQuotient) (j : ℕ)

theorem summable_norm_bergTerm (z w : ℍ) :
    Summable fun γ : X.Γ => ‖bergTerm j γ z w‖ := by
  refine (X.cocompactFree.summable_rpow (σ := (j : ℝ) + 2) (by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)])
    z w).congr fun γ => ?_
  rw [norm_bergTerm, inv_pow_eq_rpow j (pairU_nonneg _ _)]

theorem summable_bergTerm (z w : ℍ) : Summable fun γ : X.Γ => bergTerm j γ z w :=
  (X.summable_norm_bergTerm j z w).of_norm

/-- `Σ_γ |h(z, γw)^m ε_γ(w)^m| ≤ M` uniformly in `z, w`. -/
theorem exists_tsum_norm_bergTerm_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z w : ℍ, ∑' γ : X.Γ, ‖bergTerm j γ z w‖ ≤ M := by
  obtain ⟨M, hM, hle⟩ := X.cocompactFree.exists_tsum_rpow_le (σ := (j : ℝ) + 2)
    (by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)])
  refine ⟨M.toReal, ENNReal.toReal_nonneg, fun z w => ?_⟩
  rw [← ENNReal.ofReal_le_iff_le_toReal hM.ne, ENNReal.ofReal_tsum_of_nonneg
    (fun γ => norm_nonneg _) (X.summable_norm_bergTerm j z w)]
  refine le_trans (le_of_eq (tsum_congr fun γ => ?_)) (hle z w)
  rw [norm_bergTerm, inv_pow_eq_rpow j (pairU_nonneg _ _)]

/-- A uniform bound for `Σ_γ |h(z, γw)^m ε_γ(w)^m|`. -/
def bergBound : ℝ := (X.exists_tsum_norm_bergTerm_le j).choose

theorem bergBound_nonneg : 0 ≤ X.bergBound j := (X.exists_tsum_norm_bergTerm_le j).choose_spec.1

theorem tsum_norm_bergTerm_le (z w : ℍ) : ∑' γ : X.Γ, ‖bergTerm j γ z w‖ ≤ X.bergBound j :=
  (X.exists_tsum_norm_bergTerm_le j).choose_spec.2 z w

/-- **The automorphic Bergman kernel** `K(z, w) = c Σ_γ h(z, γw)^m ε_γ(w)^m`. -/
def bergAut (z w : ℍ) : ℂ := (bergC j : ℂ) * ∑' γ : X.Γ, bergTerm j γ z w

theorem bergC_pos : 0 < bergC j := by unfold bergC; positivity

theorem norm_bergAut_le (z w : ℍ) : ‖X.bergAut j z w‖ ≤ bergC j * X.bergBound j := by
  rw [bergAut, norm_mul, Complex.norm_real, Real.norm_of_nonneg (bergC_pos j).le]
  exact mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm (X.summable_norm_bergTerm j z w)).trans
    (X.tsum_norm_bergTerm_le j z w)) (bergC_pos j).le

theorem continuous_bergAut : Continuous fun p : ℍ × ℍ => X.bergAut j p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨z₀, w₀⟩
  set s : Set (ℍ × ℍ) := closedBall z₀ 1 ×ˢ closedBall w₀ 1
  have hs : s ∈ nhds (z₀, w₀) :=
    prod_mem_nhds (closedBall_mem_nhds _ one_pos) (closedBall_mem_nhds _ one_pos)
  set c : ℝ := Real.exp (-(2 * 1)) / 4
  have hc : 0 < c := by positivity
  show ContinuousAt (fun p : ℍ × ℍ => (bergC j : ℂ) * ∑' γ : X.Γ, bergTerm j γ p.1 p.2) (z₀, w₀)
  refine continuousAt_const.mul ?_
  refine ContinuousOn.continuousAt ?_ hs
  refine continuousOn_tsum (u := fun γ : X.Γ => (c ^ (j + 2))⁻¹ * ‖bergTerm j γ z₀ w₀‖)
    (fun γ => (continuous_bergTerm j γ).continuousOn)
    ((X.summable_norm_bergTerm j z₀ w₀).mul_left _) (fun γ p hp => ?_)
  have hcomp := one_add_pairU_ge (show dist p.1 z₀ ≤ 1 from hp.1) (show dist p.2 w₀ ≤ 1 from hp.2)
    (γ : SL(2, ℝ))
  have h0 : 0 < 1 + pairU z₀ ((γ : SL(2, ℝ)) • w₀) := by
    have := pairU_nonneg z₀ ((γ : SL(2, ℝ)) • w₀); linarith
  rw [norm_bergTerm, norm_bergTerm, ← mul_inv, ← mul_pow]
  exact inv_anti₀ (pow_pos (mul_pos hc h0) _) (pow_le_pow_left₀ (mul_pos hc h0).le hcomp _)

theorem measurable_bergAut : Measurable (Function.uncurry (X.bergAut j)) :=
  (X.continuous_bergAut j).measurable

/-- **Hermitian symmetry.**  `K(w, z) = \overline{K(z, w)}`. -/
theorem bergAut_swap (z w : ℍ) : X.bergAut j w z = conj (X.bergAut j z w) := by
  rw [bergAut, bergAut, map_mul, Complex.conj_ofReal, Complex.conj_tsum]
  congr 1
  simp_rw [conj_bergTerm]
  exact ((Equiv.inv X.Γ).tsum_eq (fun γ : X.Γ => bergTerm j (γ : SL(2, ℝ)) w z)).symm.trans
    (tsum_congr fun γ => by simp only [Equiv.inv_apply, InvMemClass.coe_inv])

/-- **Automorphy.**  `K(γy, w) = ε_γ(y)^m K(y, w)`. -/
theorem bergAut_smul_left (γ : X.Γ) (y w : ℍ) :
    X.bergAut j ((γ : SL(2, ℝ)) • y) w = autF γ y ^ (2 * (j + 2)) * X.bergAut j y w := by
  rw [bergAut, bergAut, ← (Equiv.mulLeft γ).tsum_eq]
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, bergTerm_mul_smul]
  rw [tsum_mul_left]
  ring

/-! ### Idempotency -/

theorem tsum_enorm_bergTerm_le (y w : ℍ) :
    ∑' δ : X.Γ, ‖bergTerm j δ y w‖ₑ ≤ ENNReal.ofReal (X.bergBound j) := by
  simp_rw [← ofReal_norm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun δ => norm_nonneg _) (X.summable_norm_bergTerm j y w)]
  exact ENNReal.ofReal_le_ofReal (X.tsum_norm_bergTerm_le j y w)

theorem continuous_bergK_pow (z : ℍ) : Continuous fun y : ℍ => bergK z y ^ (2 * (j + 2)) :=
  (continuous_bergK.comp (continuous_const.prodMk continuous_id)).pow _

/-- `∫_ℍ |h(z, y)|^m dμ(y) < ∞`. -/
theorem lintegral_enorm_bergK_pow_lt_top (z : ℍ) :
    ∫⁻ y : ℍ, ‖bergK z y ^ (2 * (j + 2))‖ₑ < ∞ := by
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_))
    (lintegral_one_add_pairU_pow_lt_top j z)
  rw [← ofReal_norm, norm_bergK_pow_two_mul]

theorem bergC_mul_mass : (bergC j : ℂ) * ((4 * π / ((2 * j + 2 : ℕ) + 1) : ℝ) : ℂ) = 1 := by
  have h : bergC j * (4 * π / ((2 * j + 2 : ℕ) + 1)) = 1 := by
    have hπ := Real.pi_pos.ne'
    unfold bergC
    push_cast
    field_simp
    ring
  exact_mod_cast h

/-- `∫_ℍ h(z, y)^m K(y, w) dμ(y) = Σ_δ h(z, δw)^m ε_δ(w)^m`: the reproducing identity, summed. -/
theorem integral_bergK_pow_mul_bergAut (z w : ℍ) :
    ∫ y : ℍ, bergK z y ^ (2 * (j + 2)) * X.bergAut j y w = ∑' δ : X.Γ, bergTerm j δ z w := by
  have hexp : ∀ y : ℍ, bergK z y ^ (2 * (j + 2)) * X.bergAut j y w =
      (bergC j : ℂ) * ∑' δ : X.Γ, bergK z y ^ (2 * (j + 2)) * bergTerm j δ y w := by
    intro y; rw [bergAut, tsum_mul_left]; ring
  have hmeas : ∀ δ : X.Γ, AEStronglyMeasurable
      (fun y : ℍ => bergK z y ^ (2 * (j + 2)) * bergTerm j δ y w) volume := fun δ =>
    ((continuous_bergK_pow j z).mul ((continuous_bergTerm j δ).comp
      (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  have hsum : ∑' δ : X.Γ, ∫⁻ y : ℍ, ‖bergK z y ^ (2 * (j + 2)) * bergTerm j δ y w‖ₑ ≠ ∞ := by
    refine ne_of_lt ?_
    rw [← lintegral_tsum fun δ => (hmeas δ).enorm]
    calc ∫⁻ y : ℍ, ∑' δ : X.Γ, ‖bergK z y ^ (2 * (j + 2)) * bergTerm j δ y w‖ₑ
        ≤ ∫⁻ y : ℍ, ‖bergK z y ^ (2 * (j + 2))‖ₑ * ENNReal.ofReal (X.bergBound j) := by
          refine lintegral_mono fun y => ?_
          simp_rw [enorm_mul]
          rw [ENNReal.tsum_mul_left]
          gcongr
          exact X.tsum_enorm_bergTerm_le j y w
      _ = (∫⁻ y : ℍ, ‖bergK z y ^ (2 * (j + 2))‖ₑ) * ENNReal.ofReal (X.bergBound j) :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ < ∞ := ENNReal.mul_lt_top (lintegral_enorm_bergK_pow_lt_top j z) ENNReal.ofReal_lt_top
  simp_rw [hexp]
  rw [integral_const_mul, integral_tsum hmeas hsum]
  have hm : 2 * j + 2 + 2 = 2 * (j + 2) := by ring
  have hterm : ∀ δ : X.Γ, ∫ y : ℍ, bergK z y ^ (2 * (j + 2)) * bergTerm j δ y w =
      ((4 * π / ((2 * j + 2 : ℕ) + 1) : ℝ) : ℂ) * bergTerm j δ z w := by
    intro δ
    have h := integral_bergK_pow (2 * j + 2) z ((δ : SL(2, ℝ)) • w)
    rw [hm] at h
    simp only [bergTerm, ← mul_assoc]
    rw [integral_mul_const, h]
  simp_rw [hterm]
  rw [tsum_mul_left, ← mul_assoc, bergC_mul_mass j, one_mul]

/-- **Idempotency.**  `∫_F K(z, y) K(y, w) dμ(y) = K(z, w)`. -/
theorem integral_bergAut_mul (z w : ℍ) :
    ∫ y in X.F, X.bergAut j z y * X.bergAut j y w = X.bergAut j z w := by
  have hK : Continuous fun y : ℍ => X.bergAut j y w :=
    (X.continuous_bergAut j).comp₂ continuous_id continuous_const
  have hΨc' : Continuous fun y : ℍ => bergK z y ^ (2 * (j + 2)) * X.bergAut j y w :=
    (continuous_bergK_pow j z).mul hK
  set Ψ : ℍ → ℂ := fun y => bergK z y ^ (2 * (j + 2)) * X.bergAut j y w with hΨdef
  have hΨc : Continuous Ψ := hΨc'
  -- `K(z, y) K(y, w) = c Σ_γ Ψ(γy)`
  have hpt : ∀ y : ℍ, X.bergAut j z y * X.bergAut j y w =
      (bergC j : ℂ) * ∑' γ : X.Γ, Ψ ((γ : SL(2, ℝ)) • y) := by
    intro y
    rw [bergAut, mul_assoc, ← tsum_mul_right]
    congr 1
    refine tsum_congr fun γ => ?_
    simp only [Ψ, bergTerm]
    rw [X.bergAut_smul_left j γ y w]
    ring
  simp_rw [hpt]
  -- `Ψ` is integrable on `ℍ`
  have hΨlint : ∫⁻ y, ‖Ψ y‖ₑ < ∞ := by
    calc ∫⁻ y, ‖Ψ y‖ₑ ≤ ∫⁻ y : ℍ, ‖bergK z y ^ (2 * (j + 2))‖ₑ *
          ENNReal.ofReal (bergC j * X.bergBound j) := by
          refine lintegral_mono fun y => ?_
          simp only [Ψ, enorm_mul]
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (X.norm_bergAut_le j y w)
      _ = (∫⁻ y : ℍ, ‖bergK z y ^ (2 * (j + 2))‖ₑ) * ENNReal.ofReal (bergC j * X.bergBound j) :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ < ∞ := ENNReal.mul_lt_top (lintegral_enorm_bergK_pow_lt_top j z) ENNReal.ofReal_lt_top
  have hΨint : Integrable Ψ := ⟨hΨc.aestronglyMeasurable, hΨlint⟩
  have hsum : ∑' γ : X.Γ, ∫⁻ y in X.F, ‖Ψ (γ • y)‖ₑ ≠ ∞ := by
    rw [← X.isFundamentalDomain.lintegral_eq_tsum'' (fun y => ‖Ψ y‖ₑ)]
    exact hΨlint.ne
  rw [integral_const_mul, integral_tsum (f := fun (γ : X.Γ) (y : ℍ) => Ψ ((γ : SL(2, ℝ)) • y))
    (fun γ => (hΨc.comp (continuous_const_smul _)).aestronglyMeasurable) hsum]
  -- unfold the fundamental domain
  have hunf : ∑' γ : X.Γ, ∫ y in X.F, Ψ ((γ : SL(2, ℝ)) • y) = ∫ y, Ψ y := by
    rw [X.isFundamentalDomain.integral_eq_tsum' Ψ hΨint, ← (Equiv.inv X.Γ).tsum_eq]
    refine tsum_congr fun γ => ?_
    simp only [Equiv.inv_apply]
    rfl
  rw [hunf, hΨdef, X.integral_bergK_pow_mul_bergAut j z w, bergAut]

/-! ### The projection and its trace -/

theorem lintegral_enorm_le_of_le {f : ℍ → ℂ} {B : ℝ} (hB : 0 ≤ B) (hf : ∀ z, ‖f z‖ ≤ B) :
    ∫⁻ z, ‖f z‖ₑ ∂X.μ ≤ ((B * (volume X.F).toReal).toNNReal : ℝ≥0∞) := by
  calc ∫⁻ z, ‖f z‖ₑ ∂X.μ ≤ ∫⁻ _z, ENNReal.ofReal B ∂X.μ := lintegral_mono fun z => by
        rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hf z)
    _ = ENNReal.ofReal B * volume X.F := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    _ = ((B * (volume X.F).toReal).toNNReal : ℝ≥0∞) := by
        show _ = ENNReal.ofReal (B * (volume X.F).toReal)
        rw [ENNReal.ofReal_mul hB, ENNReal.ofReal_toReal X.volume_F_lt_top.ne]

/-- The Bergman kernel as a Schur kernel on `L²(F)`. -/
def bergKer : SchurKernel X.μ where
  toFun := X.bergAut j
  measurable := X.measurable_bergAut j
  bound := (bergC j * X.bergBound j * (volume X.F).toReal).toNNReal
  row y := X.lintegral_enorm_le_of_le (mul_nonneg (bergC_pos j).le (X.bergBound_nonneg j))
    fun z => X.norm_bergAut_le j y z
  col z := X.lintegral_enorm_le_of_le (mul_nonneg (bergC_pos j).le (X.bergBound_nonneg j))
    fun y => X.norm_bergAut_le j y z

theorem lintegral_sq_bergKer_lt_top :
    ∫⁻ y, ∫⁻ z, ‖(X.bergKer j).toFun y z‖ₑ ^ 2 ∂X.μ ∂X.μ < ∞ := by
  have hpt : ∀ y z : ℍ, ‖(X.bergKer j).toFun y z‖ₑ ^ 2 ≤
      ENNReal.ofReal (bergC j * X.bergBound j) ^ 2 := fun y z => by
    refine pow_le_pow_left₀ bot_le ?_ 2
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (X.norm_bergAut_le j y z)
  calc ∫⁻ y, ∫⁻ z, ‖(X.bergKer j).toFun y z‖ₑ ^ 2 ∂X.μ ∂X.μ
      ≤ ∫⁻ _y, ∫⁻ _z, ENNReal.ofReal (bergC j * X.bergBound j) ^ 2 ∂X.μ ∂X.μ :=
        lintegral_mono fun y => lintegral_mono fun z => hpt y z
    _ = ENNReal.ofReal (bergC j * X.bergBound j) ^ 2 * volume X.F * volume X.F := by
        simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
        X.volume_F_lt_top) X.volume_F_lt_top

/-- `P² = P`. -/
theorem bergKer_op_comp_self : (X.bergKer j).op ∘L (X.bergKer j).op = (X.bergKer j).op := by
  rw [← comp_op]
  exact op_eq_of_ae (Eventually.of_forall fun y => Eventually.of_forall fun z => by
    rw [comp_toFun]
    exact X.integral_bergAut_mul j y z)

theorem isCompactOperator_bergKer_op : IsCompactOperator (X.bergKer j).op :=
  ((X.bergKer j).isHilbertSchmidt_op (X.lintegral_sq_bergKer_lt_top j)).isCompactOperator

/-- **The diagonal integral of the Bergman kernel is a natural number**: it is the trace of the
compact idempotent `P`, `tr P = tr P² = ∫_F ∫_F K(z, y) K(y, z) = ∫_F K(y, y)`. -/
theorem exists_nat_integral_bergAut_diag : ∃ n : ℕ, ∫ y in X.F, X.bergAut j y y = n := by
  obtain ⟨n, hn⟩ := exists_opTrace_eq_nat (X.bergKer_op_comp_self j)
    (X.isCompactOperator_bergKer_op j)
  refine ⟨n, ?_⟩
  rw [← hn, ← X.bergKer_op_comp_self j, opTrace_comp_op _ _ (X.lintegral_sq_bergKer_lt_top j)
    (X.lintegral_sq_bergKer_lt_top j)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show X.bergAut j y y = ∫ z, X.bergAut j z y * X.bergAut j y z ∂X.μ
  simp_rw [mul_comm (X.bergAut j _ y)]
  exact (X.integral_bergAut_mul j y y).symm

end CompactQuotient

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
