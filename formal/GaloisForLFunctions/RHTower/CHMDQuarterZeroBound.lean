import GaloisForLFunctions.RHTower.CHMDBoundStateInertia
import GaloisForLFunctions.RHTower.ZetaZeroCountUpperBound

/-!
# The quarter-strip Birman–Schwinger bound

The defect functional `f ↦ f̂(γ_ρ) − f̂(γ̄_ρ)` of a zero `ρ` changes sign under the reflection
`ρ ↦ 1 − ρ̄` and, for real tests, is conjugated under `ρ ↦ ρ̄`. Every off-line zero is obtained
from a zero in the closed upper-right quarter `{Re ρ > 1/2, Im ρ ≥ 0}` of the strip by at most one
conjugation and one reflection, so for real tests the defect functionals of the quarter zeros
control all of them. The dimension count of the Birman–Schwinger bound therefore only pays for the
quarter zeros: every orthonormal family of primitive bound states of the arithmetic resolvent
above `1/2` has at most `2 · #(quarter zeros)` members. Since the quarter zeros and their
reflections are disjoint subsets of the off-line zeros, this is at most `#(off-line zeros)`, and it
is `#(off-line zeros)/2` when no off-line zero is real.
-/

open MeasureTheory Set Filter Topology Zeta23
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump

/-! ## Symmetries of the defect functional -/

theorem reflect_re (ρ : ℂ) : (reflect ρ).re = 1 - ρ.re := by
  simp [reflect]

theorem reflect_im (ρ : ℂ) : (reflect ρ).im = ρ.im := by
  simp [reflect]

theorem reflect_reflect (ρ : ℂ) : reflect (reflect ρ) = ρ := by
  simp [reflect]

theorem gammaOf_conj (ρ : ℂ) : gammaOf (conj ρ) = -(conj (gammaOf ρ)) := by
  unfold gammaOf
  rw [map_div₀, map_sub, Complex.conj_I, div_neg, neg_neg, map_div₀, map_one, map_ofNat]

/-- The defect functional changes sign under reflection. -/
theorem zeroDefect_reflect (f : ℝ → ℂ) (ρ : ℂ) : zeroDefect f (reflect ρ) = -zeroDefect f ρ := by
  unfold zeroDefect
  rw [CHMDGrowthCollapse.gammaOf_reflect, Complex.conj_conj]
  ring

/-- For real tests the defect functional is conjugated under conjugation of the zero. -/
theorem zeroDefect_conj_ofReal (v : ℝ → ℝ) (ρ : ℂ) :
    zeroDefect (fun u => (v u : ℂ)) (conj ρ) = conj (zeroDefect (fun u => (v u : ℂ)) ρ) := by
  unfold zeroDefect
  rw [gammaOf_conj, map_neg, Complex.conj_conj, map_sub, conj_paperFT_ofReal, conj_paperFT_ofReal,
    Complex.conj_conj]

/-! ## Quarter zeros -/

/-- The off-line zeros in the closed upper-right quarter of the strip. -/
def quarterZeros : Set ℂ := {ρ | ρ ∈ zetaZeroConfig.carrier ∧ 1 / 2 < ρ.re ∧ 0 ≤ ρ.im}

theorem quarterZeros_subset_offLine : quarterZeros ⊆ offLineZeros := fun _ h => ⟨h.1, h.2.1.ne'⟩

/-- Every off-line zero is a quarter zero up to conjugation and reflection. -/
theorem exists_quarter_of_offLine {ρ : ℂ} (hρ : ρ ∈ offLineZeros) :
    ∃ σ ∈ quarterZeros, ρ = σ ∨ ρ = conj σ ∨ ρ = reflect σ ∨ ρ = reflect (conj σ) := by
  obtain ⟨hc, hre⟩ := hρ
  rcases lt_or_gt_of_ne hre with hlt | hgt
  · rcases le_or_gt 0 ρ.im with him | him
    · refine ⟨reflect ρ, ⟨zetaZeroConfig.reflect_mem ρ hc, ?_, ?_⟩,
        Or.inr (Or.inr (Or.inl (reflect_reflect ρ).symm))⟩
      · rw [reflect_re]; linarith
      · rw [reflect_im]; exact him
    · refine ⟨conj (reflect ρ), ⟨conj_mem_zetaCarrier (zetaZeroConfig.reflect_mem ρ hc), ?_, ?_⟩,
        Or.inr (Or.inr (Or.inr ?_))⟩
      · rw [Complex.conj_re, reflect_re]; linarith
      · rw [Complex.conj_im, reflect_im]; linarith
      · rw [Complex.conj_conj, reflect_reflect]
  · rcases le_or_gt 0 ρ.im with him | him
    · exact ⟨ρ, ⟨hc, hgt, him⟩, Or.inl rfl⟩
    · refine ⟨conj ρ, ⟨conj_mem_zetaCarrier hc, ?_, ?_⟩, Or.inr (Or.inl ?_)⟩
      · rw [Complex.conj_re]; exact hgt
      · rw [Complex.conj_im]; linarith
      · rw [Complex.conj_conj]

/-- For a real test, vanishing of the defects at the quarter zeros forces vanishing at every
off-line zero. -/
theorem zeroDefect_ofReal_eq_zero_of_quarter (v : ℝ → ℝ)
    (hq : ∀ σ ∈ quarterZeros, zeroDefect (fun u => (v u : ℂ)) σ = 0) {ρ : ℂ}
    (hρ : ρ ∈ offLineZeros) : zeroDefect (fun u => (v u : ℂ)) ρ = 0 := by
  obtain ⟨σ, hσ, h | h | h | h⟩ := exists_quarter_of_offLine hρ
  · rw [h]; exact hq σ hσ
  · rw [h, zeroDefect_conj_ofReal, hq σ hσ, map_zero]
  · rw [h, zeroDefect_reflect, hq σ hσ, neg_zero]
  · rw [h, zeroDefect_reflect, zeroDefect_conj_ofReal, hq σ hσ, map_zero, neg_zero]

open Classical in
/-- The quarter zeros as a finset. -/
def quarterFinset (hfin : offLineZeros.Finite) : Finset ℂ :=
  (hfin.subset quarterZeros_subset_offLine).toFinset

theorem mem_quarterFinset (hfin : offLineZeros.Finite) {ρ : ℂ} :
    ρ ∈ quarterFinset hfin ↔ ρ ∈ quarterZeros := by
  classical
  unfold quarterFinset
  exact Set.Finite.mem_toFinset _

theorem card_quarterFinset (hfin : offLineZeros.Finite) :
    (quarterFinset hfin).card = quarterZeros.ncard := by
  classical
  unfold quarterFinset
  exact (Set.ncard_eq_toFinset_card _ _).symm

/-- The quarter zeros and their reflections are disjoint off-line zeros. -/
theorem two_mul_ncard_quarterZeros_le (hfin : offLineZeros.Finite) :
    2 * quarterZeros.ncard ≤ offLineZeros.ncard := by
  have hsub : quarterZeros ∪ reflect '' quarterZeros ⊆ offLineZeros := by
    rintro ρ (hρ | ⟨σ, hσ, rfl⟩)
    · exact quarterZeros_subset_offLine hρ
    · refine ⟨zetaZeroConfig.reflect_mem σ hσ.1, ?_⟩
      rw [reflect_re]
      linarith [hσ.2.1]
  have hdisj : Disjoint quarterZeros (reflect '' quarterZeros) := by
    rw [Set.disjoint_left]
    rintro ρ hρ ⟨σ, hσ, rfl⟩
    have h1 := hρ.2.1
    rw [reflect_re] at h1
    linarith [hσ.2.1]
  have hinj : Function.Injective reflect := by
    intro x y hxy
    rw [← reflect_reflect x, hxy, reflect_reflect]
  have h := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_union_eq hdisj (hfin.subset quarterZeros_subset_offLine)
    ((hfin.subset quarterZeros_subset_offLine).image _), Set.ncard_image_of_injective _ hinj] at h
  omega

/-! ## The quarter-strip count -/

/-- **Quarter-strip Birman–Schwinger count.** A negative-definite family of `k` real compact tests
for the Weil form needs `k ≤ 2 · #(quarter zeros)`. -/
theorem card_le_two_mul_quarter_of_negative_definite (hfin : offLineZeros.Finite) {k : ℕ}
    (q : Fin k → SourceGraph) (hq : ∀ i, q i ∈ compactTests)
    (hneg : ∀ c : Fin k → ℝ, c ≠ 0 → weilForm (∑ i, c i • q i) < 0) :
    k ≤ 2 * quarterZeros.ncard := by
  classical
  have hv : ∀ i, ∃ (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v),
      q i = compactLift v hv hvc := hq
  choose v hv hvc hqv using hv
  set T := quarterFinset hfin with hT
  let a : Fin k → T → ℂ := fun i ρ => zeroDefect (fun x => (phiDoobTest (v i) x : ℂ)) (ρ : ℂ)
  let L : (Fin k → ℝ) →ₗ[ℝ] (T → ℂ) :=
    { toFun := fun c ρ => ∑ i, (c i : ℂ) * a i ρ
      map_add' := fun c d => by
        funext ρ
        simp only [Pi.add_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        funext ρ
        simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
          Finset.smul_sum, Complex.real_smul, mul_assoc] }
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    by_contra hc0
    have hmem : (∑ i, c i • q i) ∈ compactTests :=
      Submodule.sum_mem _ fun i _ => compactTests.smul_mem _ (hq i)
    obtain ⟨w, hw, hwc, hqw⟩ := hmem
    have hW := weilForm_compactLift w hw hwc
    rw [← hqw] at hW
    have h2 : (compactLift w hw hwc).val.fst = ∑ i, c i • (q i).val.fst := by
      rw [← hqw]
      show sourceMap (∑ i, c i • q i) = ∑ i, c i • sourceMap (q i)
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
    have h1 : ((compactLift w hw hwc).val.fst : ℝ → ℝ) =ᵐ[massMeasure] w :=
      compactLift_source_ae w hw hwc
    rw [h2] at h1
    have h3 := Lp_coeFn_sum_smul Finset.univ c fun i => (q i).val.fst
    have h4 : ∀ i, ((q i).val.fst : ℝ → ℝ) =ᵐ[massMeasure] v i := fun i => by
      rw [hqv i]
      exact compactLift_source_ae _ _ _
    have h4' : ∀ᵐ x ∂massMeasure, ∀ i, (q i).val.fst x = v i x := ae_all_iff.mpr h4
    have h5 : w =ᵐ[massMeasure] fun x => ∑ i, c i * v i x := by
      filter_upwards [h1, h3, h4'] with x hx1 hx3 hx4
      rw [← hx1, hx3]
      exact Finset.sum_congr rfl fun i _ => by rw [hx4 i]
    have h6 := volume_absolutelyContinuous_mass.ae_eq h5
    have hae : (fun x => (phiDoobTest w x : ℂ)) =ᵐ[volume]
        fun x => ∑ i, (c i : ℂ) * (phiDoobTest (v i) x : ℂ) := by
      filter_upwards [h6] with x hx
      simp only [phiDoobTest, hx]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hFT : ∀ z, paperFT (fun x => (phiDoobTest w x : ℂ)) z =
        ∑ i, (c i : ℂ) * paperFT (fun x => (phiDoobTest (v i) x : ℂ)) z := by
      intro z
      rw [← paperFT_sum_mul c (fun i x => (phiDoobTest (v i) x : ℂ))
        (fun i => (contDiff_phiDoobTest_ofReal (hv i)).continuous)
        (fun i => hasCompactSupport_phiDoobTest_ofReal (hvc i)) z]
      simp only [paperFT_def]
      exact integral_congr_ae (hae.mul (ae_eq_refl _))
    have hdefq : ∀ ρ ∈ quarterZeros, zeroDefect (fun x => (phiDoobTest w x : ℂ)) ρ = 0 := by
      intro ρ hρ
      have hρT : ρ ∈ T := (mem_quarterFinset hfin).mpr hρ
      have hL : L c ⟨ρ, hρT⟩ = 0 := by rw [hc]; rfl
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, a] at hL
      unfold zeroDefect at hL ⊢
      rw [hFT, hFT, ← Finset.sum_sub_distrib, ← hL]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hdef : ∀ ρ ∈ offLineFinset hfin, zeroDefect (fun x => (phiDoobTest w x : ℂ)) ρ = 0 := by
      intro ρ hρ
      rw [mem_offLineFinset] at hρ
      exact zeroDefect_ofReal_eq_zero_of_quarter (phiDoobTest w) hdefq ⟨ρ.2, hρ⟩
    have hbound := re_W_add_defect_nonneg hfin (contDiff_phiDoobTest_ofReal hw)
      (hasCompactSupport_phiDoobTest_ofReal hwc)
    have hzero : ∑ ρ ∈ offLineFinset hfin, defectWeight (fun x => (phiDoobTest w x : ℂ)) ρ = 0 :=
      Finset.sum_eq_zero fun ρ hρ => by
        unfold defectWeight
        rw [hdef ρ hρ, norm_zero]
        ring
    rw [hzero, add_zero] at hbound
    have hneg' := hneg c hc0
    linarith
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fin_fun, Module.finrank_pi_fintype, Finset.sum_const,
    Complex.finrank_real_complex, Finset.card_univ, Fintype.card_coe, card_quarterFinset,
    smul_eq_mul] at h
  linarith

/-- **Primitive bound states are paid for by quarter zeros.** If only finitely many nontrivial
zeros lie off the critical line, every orthonormal family of primitive eigenvectors of the
arithmetic resolvent with eigenvalues above `1/2` has at most `2 · #(quarter zeros)` members, hence
at most `#(off-line zeros)`. -/
theorem orthonormal_primitive_bound_states_le_two_mul_quarter (hfin : offLineZeros.Finite) {k : ℕ}
    {e : Fin k → MassSpace} (he : Orthonormal ℝ e) {μ : Fin k → ℝ} (hμ : ∀ i, 1 / 2 < μ i)
    (hprim : ∀ i, ⟪e i, oneL⟫_ℝ = 0) (heig : ∀ i, resolvent (e i) = μ i • e i) :
    k ≤ 2 * quarterZeros.ncard := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · omega
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => μ i * (2 * μ i - 1))
    Finset.univ_nonempty
  have hδ : 0 < μ i₀ * (2 * μ i₀ - 1) := mul_pos (by linarith [hμ i₀]) (by linarith [hμ i₀])
  have hneg := weilForm_rieszLift_sum_le he hprim heig (fun i => hi₀ i (Finset.mem_univ i))
  obtain ⟨q, hq, hqneg⟩ := exists_compactTests_negative_definite (fun i => rieszLift (e i)) hδ hneg
  exact card_le_two_mul_quarter_of_negative_definite hfin q hq hqneg

theorem orthonormal_primitive_bound_states_le_offLine (hfin : offLineZeros.Finite) {k : ℕ}
    {e : Fin k → MassSpace} (he : Orthonormal ℝ e) {μ : Fin k → ℝ} (hμ : ∀ i, 1 / 2 < μ i)
    (hprim : ∀ i, ⟪e i, oneL⟫_ℝ = 0) (heig : ∀ i, resolvent (e i) = μ i • e i) :
    k ≤ offLineZeros.ncard :=
  (orthonormal_primitive_bound_states_le_two_mul_quarter hfin he hμ hprim heig).trans
    (two_mul_ncard_quarterZeros_le hfin)

end RHTower.CHMDPolar
