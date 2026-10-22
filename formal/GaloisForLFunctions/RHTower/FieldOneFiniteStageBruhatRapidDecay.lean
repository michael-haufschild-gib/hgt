import GaloisForLFunctions.RHTower.FieldOneFiniteStageBruhatPeriodization
import GaloisForLFunctions.RHTower.FieldOneFiniteStageModuleOneFundamentalDomain
import GaloisForLFunctions.RHTower.CCM.CCMRationalPeriodicWeightedPoisson

/-!
# Uniform rapid decay of finite-stage Bruhat periodization

This file proves the large-module half of Connes--Marcolli Lemma 2.29 on the
literal semilocal carrier.  One integer denominator confines the compact
finite support uniformly under every element of the norm-one torus `K_S`.
The contributing rational `S`-units then inject into the punctured integer
lattice.  Existing arbitrary-order Schwartz seminorm bounds give one decay
constant over the whole compact fundamental domain.

Consequently every finite-stage Bruhat--Schwartz tensor periodization decays
faster than every prescribed power of the module, uniformly in `K_S`.  No
asymptotic hypothesis, endpoint cancellation, spectral premise, or numerical
computation occurs.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

def fieldOneFiniteStageBruhatLogRayIdele
    (S : Finset (HeightOneSpectrum ℤ))
    (b : (v : ↥S) → (v.1.adicCompletion ℚ)ˣ)
    (t : ℝ) : FieldOneFiniteStageIdele S :=
  (Units.mk0 (Real.exp t) (Real.exp_ne_zero t), b)

@[simp]
theorem fieldOneFiniteStageBruhatPeriodization_zero
    (S : Finset (HeightOneSpectrum ℤ))
    (u : FieldOneFiniteStageIdele S) :
    fieldOneFiniteStageBruhatPeriodization S 0 u = 0 := by
  simp [fieldOneFiniteStageBruhatPeriodization,
    fieldOneFiniteStageBruhatOrbit]

theorem fieldOneFiniteStageBruhatPeriodization_add
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S) :
    fieldOneFiniteStageBruhatPeriodization S (x + y) u =
      fieldOneFiniteStageBruhatPeriodization S x u +
        fieldOneFiniteStageBruhatPeriodization S y u := by
  rw [fieldOneFiniteStageBruhatPeriodization,
    fieldOneFiniteStageBruhatPeriodization,
    fieldOneFiniteStageBruhatPeriodization]
  have hx := summable_norm_iff.mp
    (fieldOneFiniteStageBruhatOrbit_summable S x u)
  have hy := summable_norm_iff.mp
    (fieldOneFiniteStageBruhatOrbit_summable S y u)
  rw [← hx.tsum_add hy]
  apply tsum_congr
  intro q
  simp [fieldOneFiniteStageBruhatOrbit]

/-- One support denominator works uniformly under every norm-one local-unit
translation in the compact finite-stage fundamental domain. -/
theorem fieldOneFiniteStageFiniteBruhat_exists_uniformNormOneIntegerDenominator
    (S : Finset (HeightOneSpectrum ℤ))
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    ∃ d : ℤ, d ≠ 0 ∧
      ∀ (k : FieldOneFiniteStageNormOneTorus S)
        (q : fieldOneSUnitSubgroup S),
      phi.1 (fun v =>
        algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
          ((k v).1 : v.1.adicCompletion ℚ)) ≠ 0 →
      algebraMap ℤ ℚ d * (q.1 : ℚ) ∈ (algebraMap ℤ ℚ).range := by
  obtain ⟨d, hd, hden⟩ :=
    fieldOneFiniteStageFinite_isCompact_exists_commonIntegerDenominator S phi.2
  refine ⟨d, hd, fun k q hq => ?_⟩
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ
  intro v
  have hlocalMem :
      algebraMap ℚ (v.adicCompletion ℚ)
          (algebraMap ℤ ℚ d * (q.1 : ℚ)) ∈
        v.adicCompletionIntegers ℚ := by
    by_cases hv : v ∈ S
    · let w : ↥S := ⟨v, hv⟩
      let x : FieldOneFiniteStageFinitePart S := fun z =>
        algebraMap ℚ (z.1.adicCompletion ℚ) (q.1 : ℚ) *
          ((k z).1 : z.1.adicCompletion ℚ)
      have hxSupp : x ∈ tsupport
          (phi.1 : FieldOneFiniteStageFinitePart S → ℂ) := by
        apply subset_tsupport
        exact hq
      have hx := hden hxSupp w
      have hkinv : (((k w).1⁻¹ : (v.adicCompletion ℚ)ˣ) :
          v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        apply Valued.toNormedField.norm_le_one_iff.mp
        have hkNorm := (k w).2
        change ‖((((k w).1 : (v.adicCompletion ℚ)ˣ) :
          v.adicCompletion ℚ))‖ = 1 at hkNorm
        rw [Units.val_inv_eq_inv_val, norm_inv, hkNorm, inv_one]
      have hmul := mul_mem hx hkinv
      change algebraMap ℤ (v.adicCompletion ℚ) d *
          (algebraMap ℚ (v.adicCompletion ℚ) (q.1 : ℚ) *
            (((k w).1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) *
          (((k w).1⁻¹ : (v.adicCompletion ℚ)ˣ) :
            v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ at hmul
      have hcancel :
          (((k w).1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) *
            (((k w).1⁻¹ : (v.adicCompletion ℚ)ˣ) :
              v.adicCompletion ℚ) = 1 := by
        change (((k w).1 * (k w).1⁻¹ : (v.adicCompletion ℚ)ˣ) :
          v.adicCompletion ℚ) = 1
        simp
      simpa [mul_assoc, hcancel, map_mul] using hmul
    · have hqnorm := fieldOneSUnit_localNorm_one_of_not_mem S q hv
      have hqint :
          algebraMap ℚ (v.adicCompletion ℚ) (q.1 : ℚ) ∈
            v.adicCompletionIntegers ℚ := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        simpa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using hqnorm.le
      rw [map_mul]
      exact mul_mem
        (coe_mem_adicCompletionIntegers (K := ℚ) v d) hqint
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hlocalMem
  change Valued.v
      (algebraMap ℚ (v.adicCompletion ℚ)
        (algebraMap ℤ ℚ d * (q.1 : ℚ))) ≤ 1 at hlocalMem
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
    (v := v) (algebraMap ℤ ℚ d * (q.1 : ℚ))]
  exact hlocalMem

private theorem fieldOneFiniteStageBruhatPureTensor_norm_tsum_logRay_large_bound_of_denominator
    (S : Finset (HeightOneSpectrum ℤ))
    (f : SchwartzMap ℝ ℂ)
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (b : (v : ↥S) → (v.1.adicCompletion ℚ)ˣ)
    (B : ℝ) (hB : ∀ x, ‖phi.1 x‖ ≤ B)
    (d : ℤ) (hd : d ≠ 0)
    (hden : ∀ q : fieldOneSUnitSubgroup S,
      phi.1 (fun v =>
        algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
          (b v : v.1.adicCompletion ℚ)) ≠ 0 →
      algebraMap ℤ ℚ d * (q.1 : ℚ) ∈ (algebraMap ℤ ℚ).range)
    (N : ℕ) :
    ∀ t : ℝ,
    (∑' q : fieldOneSUnitSubgroup S,
      ‖fieldOneFiniteStageBruhatPureTensorOrbit S f phi
        (fieldOneFiniteStageBruhatLogRayIdele S b t) q‖) ≤
      (B * ccmRationalArchimedeanDecayConstant f N *
          ((d * d : ℤ) : ℝ) ^ ccmRationalArchimedeanDecayExponent N) /
        Real.exp t ^ ccmRationalArchimedeanDecayExponent N := by
  classical
  let D : ℤ := d * d
  have hD : 0 < D := mul_self_pos.mpr hd
  have hD0 : D ≠ 0 := hD.ne'
  let P : Set (fieldOneSUnitSubgroup S) :=
    {q | phi.1 (fun v =>
      algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
        (b v : v.1.adicCompletion ℚ)) ≠ 0}
  have hdenD (q : P) :
      algebraMap ℤ ℚ D * (q.1.1 : ℚ) ∈ (algebraMap ℤ ℚ).range := by
    obtain ⟨z, hz⟩ := hden q.1 q.2
    refine ⟨d * z, ?_⟩
    change ((d * z : ℤ) : ℚ) = (D : ℚ) * (q.1.1 : ℚ)
    push_cast
    dsimp [D]
    change (z : ℚ) = (d : ℚ) * (q.1.1 : ℚ) at hz
    calc
      (d : ℚ) * (z : ℚ) = (d : ℚ) * ((d : ℚ) * (q.1.1 : ℚ)) :=
        congrArg (fun x : ℚ => (d : ℚ) * x) hz
      _ = (((d * d : ℤ) : ℚ)) * (q.1.1 : ℚ) := by push_cast; ring
  choose n hn using hdenD
  have hnInjective : Function.Injective n := by
    intro q r hqr
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast hD0
    apply mul_left_cancel₀ hDQ
    calc
      (D : ℚ) * (q.1.1 : ℚ) = (n q : ℚ) := (hn q).symm
      _ = (n r : ℚ) := by rw [hqr]
      _ = (D : ℚ) * (r.1.1 : ℚ) := hn r
  have hn_ne_zero (q : P) : n q ≠ 0 := by
    intro hn0
    have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast hD0
    have hq0 : (q.1.1 : ℚ) = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hDQ
      have h := hn q
      rw [hn0] at h
      simpa using h.symm
    exact Units.ne_zero q.1.1 hq0
  let w : P → ℂ := fun q => phi.1 (fun v =>
    algebraMap ℚ (v.1.adicCompletion ℚ) (q.1.1 : ℚ) *
      (b v : v.1.adicCompletion ℚ))
  let v : ℤ → ℂ := Function.extend n w 0
  have hB0 : 0 ≤ B := (norm_nonneg (phi.1 0)).trans (hB 0)
  have hv : ∀ z, ‖v z‖ ≤ B := by
    intro z
    by_cases hz : ∃ q, n q = z
    · rcases hz with ⟨q, rfl⟩
      rw [show v (n q) = w q from hnInjective.extend_apply w 0 q]
      exact hB _
    · change ‖Function.extend n w 0 z‖ ≤ B
      rw [Function.extend_apply' (f := n) w (0 : ℤ → ℂ) z hz]
      simpa using hB0
  have hv0 : v 0 = 0 := by
    change Function.extend n w 0 0 = 0
    apply Function.extend_apply' (f := n) w (0 : ℤ → ℂ) 0
    intro hz
    rcases hz with ⟨q, hq⟩
    exact hn_ne_zero q hq
  have htraceNorm (t : ℝ) :
      (∑' q : fieldOneSUnitSubgroup S,
        ‖fieldOneFiniteStageBruhatPureTensorOrbit S f phi
          (fieldOneFiniteStageBruhatLogRayIdele S b t) q‖) =
        ∑' z : ℤ, ‖v z * f ((Real.exp t / (D : ℝ)) * (z : ℝ))‖ := by
    let F : fieldOneSUnitSubgroup S → ℂ := fun q =>
      fieldOneFiniteStageBruhatPureTensorOrbit S f phi
        (fieldOneFiniteStageBruhatLogRayIdele S b t) q
    have hsupport : Function.support F ⊆ P := by
      intro q hq
      by_contra hnot
      have hphi : phi.1 (fun z =>
          algebraMap ℚ (z.1.adicCompletion ℚ) (q.1 : ℚ) *
            (b z : z.1.adicCompletion ℚ)) = 0 := by
        simpa [P] using hnot
      apply hq
      change fieldOneFiniteStageBruhatPureTensorOrbit S f phi
        (fieldOneFiniteStageBruhatLogRayIdele S b t) q = 0
      change f (Real.exp t * (((q.1 : ℚ) : ℝ))) *
        phi.1 (fun z =>
          algebraMap ℚ (z.1.adicCompletion ℚ) (q.1 : ℚ) *
            (b z : z.1.adicCompletion ℚ)) = 0
      rw [hphi, mul_zero]
    have hsupportNorm : Function.support (fun q => ‖F q‖) ⊆ P := by
      intro q hq
      apply hsupport
      intro hFq
      exact hq (by simp [hFq])
    change (∑' q, ‖F q‖) = _
    rw [(tsum_subtype_eq_of_support_subset hsupportNorm).symm]
    let G : ℤ → ℝ := fun z => ‖v z * f ((Real.exp t / (D : ℝ)) * (z : ℝ))‖
    have hGsupport : Function.support G ⊆ Set.range n := by
      intro z hz
      by_contra hnot
      have hvz : v z = 0 := by
        exact Function.extend_apply' (f := n) w (0 : ℤ → ℂ) z hnot
      exact hz (by simp [G, hvz])
    calc
      (∑' q : P, ‖F q.1‖) = ∑' q : P, G (n q) := by
        apply tsum_congr
        intro q
        have hnReal : (n q : ℝ) = (D : ℝ) * ((q.1.1 : ℚ) : ℝ) := by
          exact_mod_cast hn q
        change
          ‖f (Real.exp t * (((q.1.1 : ℚ) : ℝ))) * w q‖ =
            ‖v (n q) * f ((Real.exp t / (D : ℝ)) * (n q : ℝ))‖
        rw [show v (n q) = w q from hnInjective.extend_apply w 0 q]
        rw [mul_comm]
        congr 2
        rw [hnReal]
        have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD0
        field_simp
      _ = ∑' z : ℤ, G z := hnInjective.tsum_eq hGsupport
      _ = ∑' z : ℤ,
          ‖v z * f ((Real.exp t / (D : ℝ)) * (z : ℝ))‖ := rfl
  let p := ccmRationalArchimedeanDecayExponent N
  intro t
  have ha : 0 < Real.exp t / (D : ℝ) := div_pos (Real.exp_pos t) (by exact_mod_cast hD)
  rw [htraceNorm]
  have hlarge := ccmRationalBoundedWeightedLatticeTrace_norm_tsum_large_bound
    v B hv f (by rw [hv0, zero_mul]) N ha
  calc
    (∑' z : ℤ, ‖v z * f ((Real.exp t / (D : ℝ)) * (z : ℝ))‖) ≤
        B * ccmRationalArchimedeanDecayConstant f N /
          (Real.exp t / (D : ℝ)) ^ p := hlarge
    _ = (B * ccmRationalArchimedeanDecayConstant f N *
          ((d * d : ℤ) : ℝ) ^ ccmRationalArchimedeanDecayExponent N) /
        Real.exp t ^ ccmRationalArchimedeanDecayExponent N := by
      dsimp [p, D]
      rw [div_pow]
      field_simp

private theorem fieldOneFiniteStageBruhatPureTensor_logRay_large_bound_of_denominator
    (S : Finset (HeightOneSpectrum ℤ))
    (f : SchwartzMap ℝ ℂ)
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (b : (v : ↥S) → (v.1.adicCompletion ℚ)ˣ)
    (B : ℝ) (hB : ∀ x, ‖phi.1 x‖ ≤ B)
    (d : ℤ) (hd : d ≠ 0)
    (hden : ∀ q : fieldOneSUnitSubgroup S,
      phi.1 (fun v =>
        algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
          (b v : v.1.adicCompletion ℚ)) ≠ 0 →
      algebraMap ℤ ℚ d * (q.1 : ℚ) ∈ (algebraMap ℤ ℚ).range)
    (N : ℕ) :
    ∀ t : ℝ,
    ‖fieldOneFiniteStageBruhatPeriodization S (f ⊗ₜ[ℂ] phi)
        (fieldOneFiniteStageBruhatLogRayIdele S b t)‖ ≤
      (B * ccmRationalArchimedeanDecayConstant f N *
          ((d * d : ℤ) : ℝ) ^ ccmRationalArchimedeanDecayExponent N) /
        Real.exp t ^ ccmRationalArchimedeanDecayExponent N := by
  intro t
  rw [fieldOneFiniteStageBruhatPeriodization]
  exact (norm_tsum_le_tsum_norm
    (fieldOneFiniteStageBruhatPureTensorOrbit_summable S f phi
      (fieldOneFiniteStageBruhatLogRayIdele S b t))).trans
    (fieldOneFiniteStageBruhatPureTensor_norm_tsum_logRay_large_bound_of_denominator
      S f phi b B hB d hd hden N t)

theorem fieldOneFiniteStageBruhatPureTensor_norm_tsum_logRay_exists_large_bound
    (S : Finset (HeightOneSpectrum ℤ))
    (f : SchwartzMap ℝ ℂ)
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (b : (v : ↥S) → (v.1.adicCompletion ℚ)ˣ)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      (∑' q : fieldOneSUnitSubgroup S,
        ‖fieldOneFiniteStageBruhatPureTensorOrbit S f phi
          (fieldOneFiniteStageBruhatLogRayIdele S b t) q‖) ≤
        C / Real.exp t ^ ccmRationalArchimedeanDecayExponent N := by
  obtain ⟨B, hB⟩ := fieldOneFiniteStageFiniteBruhat_exists_norm_bound S phi
  let u0 : FieldOneFiniteStageIdele S := (1, b)
  obtain ⟨d, hd, hden⟩ :=
    fieldOneFiniteStageFiniteBruhatMulRight_exists_integerDenominator S phi u0
  let C := B * ccmRationalArchimedeanDecayConstant f N *
    ((d * d : ℤ) : ℝ) ^ ccmRationalArchimedeanDecayExponent N
  have hB0 : 0 ≤ B := (norm_nonneg (phi.1 0)).trans (hB 0)
  have hdd : 0 ≤ ((d * d : ℤ) : ℝ) := by exact_mod_cast (mul_self_nonneg d)
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg hB0 (ccmRationalArchimedeanDecayConstant_nonneg f N))
    (pow_nonneg hdd _)
  refine ⟨C, hC, fun t => ?_⟩
  exact fieldOneFiniteStageBruhatPureTensor_norm_tsum_logRay_large_bound_of_denominator
    S f phi b B hB d hd (by simpa [u0] using hden) N t

theorem fieldOneFiniteStageBruhatPureTensor_logRay_exists_large_bound
    (S : Finset (HeightOneSpectrum ℤ))
    (f : SchwartzMap ℝ ℂ)
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (b : (v : ↥S) → (v.1.adicCompletion ℚ)ˣ)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖fieldOneFiniteStageBruhatPeriodization S (f ⊗ₜ[ℂ] phi)
          (fieldOneFiniteStageBruhatLogRayIdele S b t)‖ ≤
        C / Real.exp t ^ ccmRationalArchimedeanDecayExponent N := by
  obtain ⟨C, hC, hbound⟩ :=
    fieldOneFiniteStageBruhatPureTensor_norm_tsum_logRay_exists_large_bound
      S f phi b N
  refine ⟨C, hC, fun t => ?_⟩
  rw [fieldOneFiniteStageBruhatPeriodization]
  exact (norm_tsum_le_tsum_norm
    (fieldOneFiniteStageBruhatPureTensorOrbit_summable S f phi
      (fieldOneFiniteStageBruhatLogRayIdele S b t))).trans (hbound t)

/-- A single arbitrary-power bound holds over the whole compact norm-one
fundamental domain. -/
theorem fieldOneFiniteStageBruhatPureTensor_norm_tsum_uniform_exists_large_bound
    (S : Finset (HeightOneSpectrum ℤ))
    (f : SchwartzMap ℝ ℂ)
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k : FieldOneFiniteStageNormOneTorus S) (t : ℝ),
      (∑' q : fieldOneSUnitSubgroup S,
        ‖fieldOneFiniteStageBruhatPureTensorOrbit S f phi
          (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t) q‖) ≤
        C / Real.exp t ^ ccmRationalArchimedeanDecayExponent N := by
  obtain ⟨B, hB⟩ := fieldOneFiniteStageFiniteBruhat_exists_norm_bound S phi
  obtain ⟨d, hd, hden⟩ := fieldOneFiniteStageFiniteBruhat_exists_uniformNormOneIntegerDenominator S phi
  let C := B * ccmRationalArchimedeanDecayConstant f N *
    ((d * d : ℤ) : ℝ) ^ ccmRationalArchimedeanDecayExponent N
  have hB0 : 0 ≤ B := (norm_nonneg (phi.1 0)).trans (hB 0)
  have hdd : 0 ≤ ((d * d : ℤ) : ℝ) := by exact_mod_cast (mul_self_nonneg d)
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg hB0 (ccmRationalArchimedeanDecayConstant_nonneg f N))
    (pow_nonneg hdd _)
  refine ⟨C, hC, fun k t => ?_⟩
  exact fieldOneFiniteStageBruhatPureTensor_norm_tsum_logRay_large_bound_of_denominator
    S f phi (fun v => (k v).1) B hB d hd (hden k) N t

/-- A single arbitrary-power bound holds over the whole compact norm-one
fundamental domain. -/
theorem fieldOneFiniteStageBruhatPureTensor_uniform_exists_large_bound
    (S : Finset (HeightOneSpectrum ℤ))
    (f : SchwartzMap ℝ ℂ)
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k : FieldOneFiniteStageNormOneTorus S) (t : ℝ),
      ‖fieldOneFiniteStageBruhatPeriodization S (f ⊗ₜ[ℂ] phi)
          (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t)‖ ≤
        C / Real.exp t ^ ccmRationalArchimedeanDecayExponent N := by
  obtain ⟨C, hC, hbound⟩ :=
    fieldOneFiniteStageBruhatPureTensor_norm_tsum_uniform_exists_large_bound
      S f phi N
  refine ⟨C, hC, fun k t => ?_⟩
  rw [fieldOneFiniteStageBruhatPeriodization]
  exact (norm_tsum_le_tsum_norm
    (fieldOneFiniteStageBruhatPureTensorOrbit_summable S f phi
      (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t))).trans
    (hbound k t)

theorem fieldOneFiniteStageBruhatPureTensor_logRay_rapidDecay
    (S : Finset (HeightOneSpectrum ℤ))
    (f : SchwartzMap ℝ ℂ)
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (b : (v : ↥S) → (v.1.adicCompletion ℚ)ˣ)
    (a : ℝ) :
    (fun t : ℝ =>
      fieldOneFiniteStageBruhatPeriodization S (f ⊗ₜ[ℂ] phi)
        (fieldOneFiniteStageBruhatLogRayIdele S b t)) =O[Filter.atTop]
      (fun t : ℝ => Real.exp t ^ (-a)) := by
  let N : ℕ := ⌈max a 0⌉₊
  let p : ℕ := ccmRationalArchimedeanDecayExponent N
  obtain ⟨C, hC, hbound⟩ :=
    fieldOneFiniteStageBruhatPureTensor_logRay_exists_large_bound S f phi b N
  have hap : a ≤ (p : ℝ) := by
    have hceil : max a 0 ≤ (N : ℝ) := Nat.le_ceil _
    have hNp : (N : ℝ) ≤ (p : ℝ) := by
      have hnat : N ≤ ccmRationalArchimedeanDecayExponent N := by
        simp [ccmRationalArchimedeanDecayExponent]
        omega
      exact_mod_cast hnat
    exact (le_max_left a 0).trans (hceil.trans hNp)
  refine (Asymptotics.IsBigOWith.of_bound (c := C) ?_).isBigO
  refine (Filter.eventually_ge_atTop (0 : ℝ)).mono ?_
  intro t ht
  have hx : 1 ≤ Real.exp t := Real.one_le_exp ht
  have hrpow : Real.exp t ^ (-(p : ℝ)) ≤ Real.exp t ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg hap)
  have hrewrite : C / Real.exp t ^ p =
      C * Real.exp t ^ (-(p : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_natCast,
      ← Real.rpow_neg (Real.exp_pos t).le]
  rw [show ‖Real.exp t ^ (-a)‖ = Real.exp t ^ (-a) by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Real.exp_pos t).le _)]]
  exact (hbound t).trans_eq hrewrite |>.trans
    (mul_le_mul_of_nonneg_left hrpow hC)

theorem fieldOneFiniteStageBruhatTensor_logRay_rapidDecay
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (b : (v : ↥S) → (v.1.adicCompletion ℚ)ˣ)
    (a : ℝ) :
    (fun t : ℝ =>
      fieldOneFiniteStageBruhatPeriodization S x
        (fieldOneFiniteStageBruhatLogRayIdele S b t)) =O[Filter.atTop]
      (fun t : ℝ => Real.exp t ^ (-a)) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      simpa using (Asymptotics.isBigO_zero
        (fun t : ℝ => Real.exp t ^ (-a)) Filter.atTop)
  | tmul f phi =>
      exact fieldOneFiniteStageBruhatPureTensor_logRay_rapidDecay S f phi b a
  | add x y hx hy =>
      have hxy := hx.add hy
      apply hxy.congr'
      · exact Filter.Eventually.of_forall fun t =>
          (fieldOneFiniteStageBruhatPeriodization_add S x y (fieldOneFiniteStageBruhatLogRayIdele S b t)).symm
      · exact Filter.EventuallyEq.rfl

/-- Uniform rapid decay of the absolute orbit sum over the literal compact
norm-one fundamental domain. -/
theorem fieldOneFiniteStageBruhatTensor_norm_tsum_uniform_rapidDecay
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k : FieldOneFiniteStageNormOneTorus S) (t : ℝ), 0 ≤ t →
      (∑' q : fieldOneSUnitSubgroup S,
        ‖fieldOneFiniteStageBruhatOrbit S x
          (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t) q‖) ≤
        C * Real.exp t ^ (-a) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      refine ⟨0, le_rfl, fun k t ht => ?_⟩
      simp [fieldOneFiniteStageBruhatOrbit]
  | tmul f phi =>
      let N : ℕ := ⌈max a 0⌉₊
      let p : ℕ := ccmRationalArchimedeanDecayExponent N
      obtain ⟨C, hC, hbound⟩ :=
        fieldOneFiniteStageBruhatPureTensor_norm_tsum_uniform_exists_large_bound
          S f phi N
      have hap : a ≤ (p : ℝ) := by
        have hceil : max a 0 ≤ (N : ℝ) := Nat.le_ceil _
        have hNp : (N : ℝ) ≤ (p : ℝ) := by
          have hnat : N ≤ ccmRationalArchimedeanDecayExponent N := by
            simp [ccmRationalArchimedeanDecayExponent]
            omega
          exact_mod_cast hnat
        exact (le_max_left a 0).trans (hceil.trans hNp)
      refine ⟨C, hC, fun k t ht => ?_⟩
      have hx : 1 ≤ Real.exp t := Real.one_le_exp ht
      have hrpow : Real.exp t ^ (-(p : ℝ)) ≤ Real.exp t ^ (-a) :=
        Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg hap)
      have hrewrite : C / Real.exp t ^ p =
          C * Real.exp t ^ (-(p : ℝ)) := by
        rw [div_eq_mul_inv, ← Real.rpow_natCast,
          ← Real.rpow_neg (Real.exp_pos t).le]
      simpa only [fieldOneFiniteStageBruhatOrbit_tmul] using
        (hbound k t).trans_eq hrewrite |>.trans
          (mul_le_mul_of_nonneg_left hrpow hC)
  | add x y hx hy =>
      obtain ⟨Cx, hCx, hxbound⟩ := hx
      obtain ⟨Cy, hCy, hybound⟩ := hy
      refine ⟨Cx + Cy, add_nonneg hCx hCy, fun k t ht => ?_⟩
      let u := fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t
      have hsx := fieldOneFiniteStageBruhatOrbit_summable S x u
      have hsy := fieldOneFiniteStageBruhatOrbit_summable S y u
      have hsxy := fieldOneFiniteStageBruhatOrbit_summable S (x + y) u
      calc
        (∑' q, ‖fieldOneFiniteStageBruhatOrbit S (x + y) u q‖) ≤
            ∑' q, (‖fieldOneFiniteStageBruhatOrbit S x u q‖ +
              ‖fieldOneFiniteStageBruhatOrbit S y u q‖) := by
          apply hsxy.tsum_le_tsum
          · intro q
            simpa [fieldOneFiniteStageBruhatOrbit] using
              norm_add_le (fieldOneFiniteStageBruhatOrbit S x u q)
                (fieldOneFiniteStageBruhatOrbit S y u q)
          · exact hsx.add hsy
        _ = (∑' q, ‖fieldOneFiniteStageBruhatOrbit S x u q‖) +
              ∑' q, ‖fieldOneFiniteStageBruhatOrbit S y u q‖ :=
          hsx.tsum_add hsy
        _ ≤ Cx * Real.exp t ^ (-a) + Cy * Real.exp t ^ (-a) :=
          add_le_add (hxbound k t ht) (hybound k t ht)
        _ = (Cx + Cy) * Real.exp t ^ (-a) := by ring

/-- Uniform rapid decay over the literal compact norm-one fundamental
domain.  This is the full large-module assertion of Connes--Marcolli
Lemma 2.29, with no angular parameter hidden in the constant. -/
theorem fieldOneFiniteStageBruhatTensor_uniform_rapidDecay
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k : FieldOneFiniteStageNormOneTorus S) (t : ℝ), 0 ≤ t →
      ‖fieldOneFiniteStageBruhatPeriodization S x
          (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t)‖ ≤
        C * Real.exp t ^ (-a) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      refine ⟨0, le_rfl, fun k t ht => ?_⟩
      simp
  | tmul f phi =>
      let N : ℕ := ⌈max a 0⌉₊
      let p : ℕ := ccmRationalArchimedeanDecayExponent N
      obtain ⟨C, hC, hbound⟩ :=
        fieldOneFiniteStageBruhatPureTensor_uniform_exists_large_bound S f phi N
      have hap : a ≤ (p : ℝ) := by
        have hceil : max a 0 ≤ (N : ℝ) := Nat.le_ceil _
        have hNp : (N : ℝ) ≤ (p : ℝ) := by
          have hnat : N ≤ ccmRationalArchimedeanDecayExponent N := by
            simp [ccmRationalArchimedeanDecayExponent]
            omega
          exact_mod_cast hnat
        exact (le_max_left a 0).trans (hceil.trans hNp)
      refine ⟨C, hC, fun k t ht => ?_⟩
      have hx : 1 ≤ Real.exp t := Real.one_le_exp ht
      have hrpow : Real.exp t ^ (-(p : ℝ)) ≤ Real.exp t ^ (-a) :=
        Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg hap)
      have hrewrite : C / Real.exp t ^ p =
          C * Real.exp t ^ (-(p : ℝ)) := by
        rw [div_eq_mul_inv, ← Real.rpow_natCast,
          ← Real.rpow_neg (Real.exp_pos t).le]
      exact (hbound k t).trans_eq hrewrite |>.trans
        (mul_le_mul_of_nonneg_left hrpow hC)
  | add x y hx hy =>
      obtain ⟨Cx, hCx, hxbound⟩ := hx
      obtain ⟨Cy, hCy, hybound⟩ := hy
      refine ⟨Cx + Cy, add_nonneg hCx hCy, fun k t ht => ?_⟩
      rw [fieldOneFiniteStageBruhatPeriodization_add]
      calc
        ‖fieldOneFiniteStageBruhatPeriodization S x
              (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t) +
            fieldOneFiniteStageBruhatPeriodization S y
              (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t)‖ ≤
            ‖fieldOneFiniteStageBruhatPeriodization S x
              (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t)‖ +
            ‖fieldOneFiniteStageBruhatPeriodization S y
              (fieldOneFiniteStageBruhatLogRayIdele S (fun v => (k v).1) t)‖ := norm_add_le _ _
        _ ≤ Cx * Real.exp t ^ (-a) + Cy * Real.exp t ^ (-a) :=
          add_le_add (hxbound k t ht) (hybound k t ht)
        _ = (Cx + Cy) * Real.exp t ^ (-a) := by ring

end

end GaloisForLFunctions.RHTower
