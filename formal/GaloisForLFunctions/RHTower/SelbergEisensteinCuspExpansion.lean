import GaloisForLFunctions.RHTower.SelbergEisensteinCuspFourier
import GaloisForLFunctions.RHTower.SelbergEisensteinContinuation

open Complex UpperHalfPlane Metric Filter Topology
open scoped MatrixGroups FourierTransform

/-!
# The continued `Γ(N)` Eisenstein series at every cusp

For `Re s > 1`, summing the row slices of `E_∞(σz, s)` (the `c = 0` rows give `count₀ y^s`, `slice0σ`; the `n = 0`
Fourier terms of the rows `c ≠ 0` give the scattering term, `ctermσ_eq`, `tsum_weight_eq_Dσ`) yields the Fourier
expansion at the cusp `σ∞`:
`E_∞(σz, s) = count₀ y^s + N^{-s} (y/N)^{1-s} φ_{∞,σ∞}(s) + E^*_σ(z, s)` (`poincare_smul_expansion`).
Both sides of this identity are holomorphic on the punctured half-plane `{Re s > 1/2, s ≠ 1}`, which is preconnected
(`isPreconnected_punctured`): the left side through the continuation `E = y^s + constTerm + E^*` at `∞`
(`differentiableAt_Econt`), the right side term by term (`differentiableAt_Ecusp`). The identity theorem extends the
expansion to the whole punctured half-plane (`Econt_smul_eq`).
-/

namespace GaloisForLFunctions.RHTower.SelbergEisensteinCuspExpansion
open GaloisForLFunctions.RHTower.SelbergPoincareKernel GaloisForLFunctions.RHTower.SelbergEisensteinCusp
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspRows GaloisForLFunctions.RHTower.SelbergPoincareFourier
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspSlice GaloisForLFunctions.RHTower.SelbergEisensteinCuspConstant
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspCount GaloisForLFunctions.RHTower.SelbergEisensteinCuspFourier
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspScattering GaloisForLFunctions.RHTower.SelbergEisensteinScatteringEntry
  GaloisForLFunctions.RHTower.SelbergPoincareContinuation GaloisForLFunctions.RHTower.SelbergPoincare
  GaloisForLFunctions.RHTower.SelbergEisensteinStar GaloisForLFunctions.RHTower.SelbergEisensteinContinuation

/-- The punctured half-plane `{Re s > 1/2, s ≠ 1}` is preconnected. -/
theorem isPreconnected_punctured : IsPreconnected {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} := by
  set A1 := {s : ℂ | 1 < s.re}
  set A2 := {s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | 0 < s.im}
  set A3 := {s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | s.im < 0}
  set A4 := {s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | s.re < 1}
  have hU : {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} = ((A1 ∪ A2) ∪ A3) ∪ A4 := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, A1, A2, A3, A4]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_trichotomy s.re 1 with h | h | h
      · right; exact ⟨h1, h⟩
      · rcases lt_trichotomy s.im 0 with h' | h' | h'
        · left; right; exact ⟨h1, h'⟩
        · exact absurd (Complex.ext (by simpa using h) (by simpa using h')) h2
        · left; left; right; exact ⟨h1, h'⟩
      · left; left; left; exact h
    · rintro (((h | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, h'⟩)
      · refine ⟨by linarith, fun h1 => ?_⟩; rw [h1] at h; simp at h
      · refine ⟨h, fun h1 => ?_⟩; rename_i h2; rw [h1] at h2; simp at h2
      · refine ⟨h, fun h1 => ?_⟩; rename_i h2; rw [h1] at h2; simp at h2
      · refine ⟨h, fun h1 => ?_⟩; rw [h1] at h'; simp at h'
  rw [hU]
  have c1 : IsPreconnected A1 := (convex_halfSpace_re_gt 1).isPreconnected
  have c2 : IsPreconnected A2 := ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have c3 : IsPreconnected A3 := ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have c4 : IsPreconnected A4 := ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have m1 : (3 / 4 + Complex.I) ∈ A2 := ⟨by norm_num, by norm_num⟩
  have m2 : (3 / 4 + Complex.I) ∈ A4 := ⟨by norm_num, by norm_num⟩
  have m3 : (2 - Complex.I) ∈ A1 := by show 1 < (2 - Complex.I).re; norm_num
  have m4 : (2 - Complex.I) ∈ A3 := ⟨by norm_num, by norm_num⟩
  have m5 : (2 + Complex.I) ∈ A1 := by show 1 < (2 + Complex.I).re; norm_num
  have m6 : (2 + Complex.I) ∈ A2 := ⟨by norm_num, by norm_num⟩
  refine IsPreconnected.union (3 / 4 + Complex.I) (Set.mem_union_left _ (Set.mem_union_right _ m1)) m2 ?_ c4
  refine IsPreconnected.union (2 - Complex.I) (Set.mem_union_left _ m3) m4 ?_ c3
  exact IsPreconnected.union (2 + Complex.I) m5 m6 c1 c2

theorem isOpen_punctured : IsOpen {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} :=
  (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne

variable (N : ℕ) [NeZero N] (σ : SL(2, ℤ))

theorem summable_indicatorσ {s : ℂ} (hs : 1 < s.re) (z : ℍ) :
    Summable ((rowMul σ '' adm N).indicator (esum s z)) := by
  have h : Summable (fun q => esum s z (botσ N σ q)) :=
    (summable_termQ N 0 hs (σ • z)).of_norm.congr (fun q => termQ_smul N σ s z q)
  rw [← (botσ_injective N σ).summable_iff (f := (rowMul σ '' adm N).indicator (esum s z))]
  · refine h.congr fun q => ?_
    rw [Function.comp_apply, Set.indicator_of_mem (by rw [← range_botσ N σ]; exact ⟨q, rfl⟩)]
  · intro x hx
    rw [range_botσ] at hx
    exact Set.indicator_of_notMem hx _

omit [NeZero N] in
theorem slice0σ (s : ℂ) (z : ℍ) :
    ∑' d : ℤ, (rowMul σ '' adm N).indicator (esum s z) (0, d) = ((z.im : ℝ) : ℂ) ^ s * (count0 N σ : ℂ) := by
  classical
  have h : HasSum (fun d : ℤ => (rowMul σ '' adm N).indicator (esum s z) (0, d))
      (∑ d ∈ ({1, -1} : Finset ℤ), (rowMul σ '' adm N).indicator (esum s z) (0, d)) := by
    refine hasSum_sum_of_ne_finset_zero (fun d hd => ?_)
    have hm : ((0 : ℤ), d) ∉ rowMul σ '' adm N := by
      intro hm
      rcases mem_zero N σ hm with h | h <;> simp [h] at hd
    exact Set.indicator_of_notMem hm _
  rw [h.tsum_eq]
  have h2 : ∀ d ∈ ({1, -1} : Finset ℤ), (rowMul σ '' adm N).indicator (esum s z) (0, d) =
      if ((0 : ℤ), d) ∈ rowMul σ '' adm N then ((z.im : ℝ) : ℂ) ^ s else 0 := by
    intro d hd
    have hd' : d = 1 ∨ d = -1 := by simpa using hd
    rw [Set.indicator_apply]
    split_ifs
    · unfold esum; rcases hd' with rfl | rfl <;> simp
    · rfl
  rw [Finset.sum_congr rfl h2, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    count0]
  ring

omit [NeZero N] in
theorem ksumσ_zero (c : ℤ) : ksumσ N σ c 0 = (countσ N σ c : ℂ) := by
  classical
  unfold ksumσ countσ
  rw [Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro r _
  rw [Set.indicator_apply]
  split_ifs <;> simp [kphase, phase]

/-- The constant-term contribution of the row `c` at `σ∞`. -/
noncomputable def ctermσ (s : ℂ) (z : ℍ) (c : ℤ) : ℂ :=
  if c = 0 then 0 else
    cexp (-s * (Real.log ((c : ℝ) ^ 2) : ℂ)) * cexp (-s * (Real.log N : ℂ)) *
      (𝓕 (ker 0 (z.im / N) s) 0 * ksumσ N σ c 0)

omit [NeZero N] in
theorem slice_split (s : ℂ) (z : ℍ) {c : ℤ} (hc : c ≠ 0)
    (hsum : Summable (fun k : ℤ => etermσ N σ s z (c, k))) :
    cexp (-s * (Real.log ((c : ℝ) ^ 2) : ℂ)) * cexp (-s * (Real.log N : ℂ)) *
        ∑' n : ℤ, 𝓕 (ker 0 (z.im / N) s) n * cexp (2 * Real.pi * Complex.I * n * z.re / N) * ksumσ N σ c n =
      ctermσ N σ s z c + ∑' k, etermσ N σ s z (c, k) := by
  unfold ctermσ
  simp only [if_neg hc]
  have hs : Summable (fun k : ℤ => 𝓕 (ker 0 (z.im / N) s) k * cexp (2 * Real.pi * Complex.I * k * z.re / N) *
      ksumσ N σ c k) := by
    have h2 := hsum.mul_left (cexp (-s * (Real.log ((c : ℝ) ^ 2) : ℂ)) * cexp (-s * (Real.log N : ℂ)))⁻¹
    refine (h2.add (summable_of_ne_finset_zero (s := {0})
      (f := fun k : ℤ => if k = 0 then 𝓕 (ker 0 (z.im / N) s) 0 * ksumσ N σ c 0 else 0)
      (fun k hk => by simp at hk; simp [hk]))).congr (fun k => ?_)
    by_cases hk : k = 0
    · subst hk; simp [etermσ]
    · simp only [etermσ, hc, hk, or_self, if_false, add_zero]
      field_simp
  rw [hs.tsum_eq_add_tsum_ite 0, mul_add]
  congr 1
  · simp
  · rw [← tsum_mul_left]
    apply tsum_congr; intro k
    by_cases hk : k = 0
    · simp [hk, etermσ]
    · simp only [etermσ, hc, hk, or_self, if_false]

omit [NeZero N] in
theorem ctermσ_eq (s : ℂ) (z : ℍ) (c : ℤ) :
    ctermσ N σ s z c = (((c : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * (countσ N σ c : ℂ) *
      (cexp (-s * (Real.log N : ℂ)) * 𝓕 (ker 0 (z.im / N) s) 0) := by
  unfold ctermσ
  by_cases hc : c = 0
  · subst hc; simp [countσ_zero]
  · rw [if_neg hc, ksumσ_zero, cpow_neg_eq_exp hc]; ring

theorem fourier_ker0_zero (s : ℂ) (z : ℍ) :
    𝓕 (ker 0 (z.im / N) s) 0 = (((z.im / N : ℝ)) : ℂ) ^ (1 - s) * ∫ t, ker 0 1 s t := by
  have hy : 0 < z.im / N := div_pos z.im_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
  rw [← integral_ker0_scale hy s]
  simp [Real.fourier_eq]

/-- **Fourier expansion of `E_∞` at the cusp `σ∞`** (`Re s > 1`):
`E_∞(σz, s) = count₀ y^s + N^{-s} (y/N)^{1-s} φ_{∞,σ∞}(s) + E^*_σ(z, s)`. -/
theorem poincare_smul_expansion {s : ℂ} (hs : 1 < s.re) (z : ℍ) :
    poincare N 0 s (σ • z) = ((z.im : ℝ) : ℂ) ^ s * (count0 N σ : ℂ) +
      cexp (-s * (Real.log N : ℂ)) * (((z.im / N : ℝ)) : ℂ) ^ (1 - s) * phiσ N σ s + Estarσ N σ s z := by
  have hsum := summable_indicatorσ N σ hs z
  have hse := summable_etermσ N σ (s := s) (by linarith) z
  rw [poincare_smul_eq, range_botσ, Summable.tsum_prod hsum]
  have hrow : ∀ c : ℤ, ∑' d : ℤ, (rowMul σ '' adm N).indicator (esum s z) (c, d) =
      (if c = 0 then ((z.im : ℝ) : ℂ) ^ s * (count0 N σ : ℂ) else 0) + ctermσ N σ s z c +
        ∑' k, etermσ N σ s z (c, k) := by
    intro c
    by_cases hc : c = 0
    · subst hc
      rw [slice0σ, if_pos rfl]
      have h1 : ctermσ N σ s z 0 = 0 := by simp [ctermσ]
      have h2 : ∀ k, etermσ N σ s z (0, k) = 0 := fun k => by simp [etermσ]
      simp [h1, h2]
    · rw [if_neg hc, zero_add, sliceσ N σ hc (by linarith) z (hsum.prod_factor c),
        slice_split N σ s z hc (hse.prod_factor c)]
  simp_rw [hrow]
  have hc : Summable (ctermσ N σ s z) := by
    rw [show ctermσ N σ s z = _ from funext (ctermσ_eq N σ s z)]
    refine Summable.mul_right _ (Summable.of_norm_bounded (summable_weight N σ hs) (fun c => ?_))
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_nonneg (by positivity) (by simp; linarith)]
    simp
  rw [Summable.tsum_add (((hasSum_ite_eq 0 _).summable).add hc) hse.prod,
    Summable.tsum_add (hasSum_ite_eq 0 _).summable hc, tsum_ite_eq, ← Summable.tsum_prod hse]
  congr 2
  rw [show ctermσ N σ s z = _ from funext (ctermσ_eq N σ s z), tsum_mul_right, tsum_weight_eq_Dσ N σ hs, fourier_ker0_zero, phiσ]
  ring

/-- The continued Eisenstein series `E_∞(w, s) = Im(w)^s + constTerm(s, w) + E^*(w, s)` (`N ≥ 3`). -/
noncomputable def Econt (s : ℂ) (w : ℍ) : ℂ := (w.im : ℂ) ^ s + constTerm N s w + Estar N s w

/-- The continued expansion at `σ∞`. -/
noncomputable def Ecusp (s : ℂ) (z : ℍ) : ℂ :=
  ((z.im : ℝ) : ℂ) ^ s * (count0 N σ : ℂ) +
    cexp (-s * (Real.log N : ℂ)) * (((z.im / N : ℝ)) : ℂ) ^ (1 - s) * phiσ N σ s + Estarσ N σ s z

theorem differentiableAt_Econt (w : ℍ) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (fun s => Econt N s w) s := by
  unfold Econt
  have hw : ((w.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast w.im_pos.ne'
  exact ((differentiableAt_id.const_cpow (Or.inl hw)).add (differentiableAt_constTerm N w hs hs1)).add
    (differentiableAt_Estar N w hs)

theorem differentiableAt_Ecusp (z : ℍ) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (fun s => Ecusp N σ s z) s := by
  unfold Ecusp
  have hy : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast z.im_pos.ne'
  have hyN : (((z.im / N : ℝ)) : ℂ) ≠ 0 := by
    have : 0 < z.im / N := div_pos z.im_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
    exact_mod_cast this.ne'
  refine (((differentiableAt_id.const_cpow (Or.inl hy)).mul_const _).add ?_).add
    (differentiableAt_Estarσ N σ z hs)
  exact (((differentiable_exp_neg_mul _).differentiableAt).mul
    ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id |>.const_cpow (Or.inl hyN))).mul
    (differentiableAt_phiσ N σ hs hs1)

/-- **The continued `Γ(N)` Eisenstein series at the cusp `σ∞`** (`N ≥ 3`, `Re s > 1/2`, `s ≠ 1`):
`E_∞(σz, s) = count₀ y^s + N^{-s} (y/N)^{1-s} φ_{∞,σ∞}(s) + E^*_σ(z, s)`, every term holomorphic in `s`. -/
theorem Econt_smul_eq (hN : 3 ≤ N) (z : ℍ) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    Econt N s (σ • z) = Ecusp N σ s z := by
  set U := {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1}
  have hf : AnalyticOnNhd ℂ (fun s => Econt N s (σ • z)) U :=
    DifferentiableOn.analyticOnNhd (fun s hs => (differentiableAt_Econt N (σ • z) hs.1 hs.2).differentiableWithinAt)
      isOpen_punctured
  have hg : AnalyticOnNhd ℂ (fun s => Ecusp N σ s z) U :=
    DifferentiableOn.analyticOnNhd (fun s hs => (differentiableAt_Ecusp N σ z hs.1 hs.2).differentiableWithinAt)
      isOpen_punctured
  have h2 : (2 : ℂ) ∈ U := ⟨by norm_num, by norm_num⟩
  have hev : (fun s => Econt N s (σ • z)) =ᶠ[𝓝 2] (fun s => Ecusp N σ s z) := by
    have : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [this] with s hs'
    simp only [Econt, Ecusp]
    rw [← eisenstein_eq N hN hs' (σ • z), poincare_smul_expansion N σ hs' z]
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_punctured h2 hev ⟨hs, hs1⟩

end GaloisForLFunctions.RHTower.SelbergEisensteinCuspExpansion
