import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TwoVerticalLinesWeighTheZerosOfAFunctionOfOrderOne
import GaloisForLFunctions.SquareRootThreshold.WindowedWeilFormSliceTransfer
import Zeta23.ZetaReflect

/-!
# The zeros of a function of order one with a reflection form a tempered configuration

Let `E` be entire with `E(2) ≠ 0`, all zeros in `0 ≤ Re s ≤ 1`, and the orders of its zeros
invariant under `ρ ↦ 1 − ρ̄`. Its zeros with their orders are a zero configuration
(`zerosConfig`): Weil's form of `E` and the index law of a tempered configuration apply to it.

* `analyticOrderAt_reflect_of_dual`: the invariance of the orders follows from a functional
  equation `E(1 − s) = W Ẽ(s)` with `Ẽ(s̄) = conj E(s)`.
* `hasSum_zerosConfig`: a sum over the zeros counted by copies is the sum over the distinct zeros
  with their multiplicities.
* `temperedConfig_zerosConfig`: for `E` of order one, `Σ_ρ m_ρ/(1 + |γ_ρ|²) < ∞`.
* `W_zerosConfig_eq`: Weil's form of the configuration is the sum of the transform of `f ⋆ g̃`
  over the zeros.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.EntireZeroDivisor
open Zeta23 Zeta23.WeilEF
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

variable {E : ℂ → ℂ}

/-! ### Orders -/

/-- **Orders under the reflection.** If `E(1 − s) = W Ẽ(s)` and `Ẽ(s̄) = conj E(s)`, the order
of `E` at `1 − ρ̄` is its order at `ρ`. -/
theorem analyticOrderAt_reflect_of_dual {E' : ℂ → ℂ} {W : ℂ} (hW : W ≠ 0)
    (hE' : Differentiable ℂ E') (hFE : ∀ s, E (1 - s) = W * E' s)
    (hconj : ∀ s, E' (conj s) = conj (E s)) (ρ : ℂ) :
    analyticOrderAt E (reflect ρ) = analyticOrderAt E ρ := by
  have hg : AnalyticAt ℂ (fun z : ℂ => 1 - z) (conj ρ) := analyticAt_const.sub analyticAt_id
  have hg' : deriv (fun z : ℂ => 1 - z) (conj ρ) ≠ 0 := by
    have : deriv (fun z : ℂ => 1 - z) (conj ρ) = -1 := by
      rw [deriv_const_sub]
      simp
    rw [this]
    simp
  have hev : (E ∘ fun z : ℂ => 1 - z) =ᶠ[𝓝 (conj ρ)] ((fun _ => W) * E') :=
    Eventually.of_forall fun z => hFE z
  have hE'an : AnalyticAt ℂ E' (conj ρ) := hE'.analyticAt _
  have hWan : AnalyticAt ℂ (fun _ : ℂ => W) (conj ρ) := analyticAt_const
  have hcong : (fun z => conj (E (conj z))) =ᶠ[𝓝 (conj ρ)] E' :=
    Eventually.of_forall fun z => by
      have := hconj (conj z)
      rw [Complex.conj_conj] at this
      exact this.symm
  calc analyticOrderAt E (reflect ρ)
      = analyticOrderAt E ((fun z : ℂ => 1 - z) (conj ρ)) := rfl
    _ = analyticOrderAt (E ∘ fun z : ℂ => 1 - z) (conj ρ) :=
        (analyticOrderAt_comp_of_deriv_ne_zero hg hg').symm
    _ = analyticOrderAt ((fun _ => W) * E') (conj ρ) := analyticOrderAt_congr hev
    _ = analyticOrderAt E' (conj ρ) := by
        rw [analyticOrderAt_mul hWan hE'an, hWan.analyticOrderAt_eq_zero.mpr hW, zero_add]
    _ = analyticOrderAt (fun z => conj (E (conj z))) (conj ρ) :=
        (analyticOrderAt_congr hcong).symm
    _ = analyticOrderAt E ρ := Zeta23.analyticOrderAt_conj_conj E ρ

theorem analyticOrderAt_ne_top_of_ne_zero (hE : Differentiable ℂ E) {a : ℂ} (ha : E a ≠ 0)
    (z : ℂ) : analyticOrderAt E z ≠ ⊤ := by
  have hA : AnalyticOnNhd ℂ E univ := hE.differentiableOn.analyticOnNhd isOpen_univ
  exact hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ a) (mem_univ z)
    (by rw [(hA a (mem_univ a)).analyticOrderAt_eq_zero.mpr ha]; exact ENat.zero_ne_top)

theorem one_le_toNat_analyticOrderAt (hE : Differentiable ℂ E) {a : ℂ} (ha : E a ≠ 0) {ρ : ℂ}
    (hρ : E ρ = 0) : 1 ≤ (analyticOrderAt E ρ).toNat := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_ne_top_of_ne_zero hE ha ρ)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact ((hE.analyticAt ρ).analyticOrderAt_eq_zero.mp (by simpa using hn.symm)) hρ
  rw [← hn, ENat.toNat_coe]
  omega

/-- A zero of an entire function that is not identically zero is a point of its divisor. -/
theorem mem_support_divisor_of_zero (hE : Differentiable ℂ E) {a : ℂ} (ha : E a ≠ 0) {w : ℂ}
    (hw : E w = 0) : w ∈ (MeromorphicOn.divisor E univ).support := by
  have hA : AnalyticOnNhd ℂ E univ := hE.differentiableOn.analyticOnNhd isOpen_univ
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_ne_top_of_ne_zero hE ha w)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact ((hE.analyticAt w).analyticOrderAt_eq_zero.mp (by simpa using hn.symm)) hw
  have hdiv : (MeromorphicOn.divisor E univ) w = (n : ℤ) := by
    rw [divisor_univ_eq_analyticOrder hA, ← hn]
    rfl
  rw [Function.mem_support, hdiv]
  exact_mod_cast hn0

/-- A point of the divisor of an entire function is a zero. -/
theorem apply_zeroSupport (hE : Differentiable ℂ E) (w : ZeroSupport E) : E (w : ℂ) = 0 := by
  have hA : AnalyticOnNhd ℂ E univ := hE.differentiableOn.analyticOnNhd isOpen_univ
  by_contra h
  have hord : analyticOrderAt E (w : ℂ) = 0 := (hA _ (mem_univ _)).analyticOrderAt_eq_zero.mpr h
  apply w.2
  change (MeromorphicOn.divisor E univ) (w : ℂ) = 0
  rw [divisor_univ_eq_analyticOrder hA, hord]
  rfl

/-! ### The configuration -/

/-- **The zeros of `E` with their orders**, for an entire `E` with `E(2) ≠ 0`, zeros in the
closed strip, and orders invariant under `ρ ↦ 1 − ρ̄`. -/
def zerosConfig (E : ℂ → ℂ) (hE : Differentiable ℂ E) (h2 : E 2 ≠ 0)
    (hstrip : ∀ s, E s = 0 → 0 ≤ s.re ∧ s.re ≤ 1)
    (hrefl : ∀ ρ, analyticOrderAt E (reflect ρ) = analyticOrderAt E ρ) : ZeroConfig where
  carrier := {ρ | E ρ = 0}
  mult := fun ρ => (analyticOrderAt E ρ).toNat
  one_le_mult := fun _ hρ => one_le_toNat_analyticOrderAt hE h2 hρ
  strip := fun ρ hρ => hstrip ρ hρ
  reflect_mem := fun ρ hρ => by
    by_contra h
    have h' : E (reflect ρ) ≠ 0 := h
    have h0 : analyticOrderAt E (reflect ρ) = 0 :=
      (hE.analyticAt _).analyticOrderAt_eq_zero.mpr h'
    rw [hrefl ρ] at h0
    exact ((hE.analyticAt ρ).analyticOrderAt_eq_zero.mp h0) hρ
  mult_reflect := fun ρ _ => by
    show (analyticOrderAt E (reflect ρ)).toNat = (analyticOrderAt E ρ).toNat
    rw [hrefl ρ]
  finite_window := fun T₁ T₂ => by
    have hA : AnalyticOnNhd ℂ E univ := hE.differentiableOn.analyticOnNhd isOpen_univ
    have hfin := (finite_zeroSupport_ball hA (1 + (|T₁| + |T₂|))).image
      (fun w : ZeroSupport E => (w : ℂ))
    refine hfin.subset ?_
    rintro ρ ⟨hρ, h1, h1'⟩
    refine ⟨⟨ρ, mem_support_divisor_of_zero hE h2 hρ⟩, ?_, rfl⟩
    show ‖ρ‖ ≤ 1 + (|T₁| + |T₂|)
    obtain ⟨hs0, hs1⟩ := hstrip ρ hρ
    have hre : |ρ.re| ≤ 1 := abs_le.mpr ⟨by linarith, hs1⟩
    have him : |ρ.im| ≤ |T₁| + |T₂| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le T₁, abs_nonneg T₂]
      · linarith [le_abs_self T₂, abs_nonneg T₁]
    exact (Complex.norm_le_abs_re_add_abs_im ρ).trans (add_le_add hre him)

section Sums

variable (hE : Differentiable ℂ E) (h2 : E 2 ≠ 0)
  (hstrip : ∀ s, E s = 0 → 0 ≤ s.re ∧ s.re ≤ 1)
  (hrefl : ∀ ρ, analyticOrderAt E (reflect ρ) = analyticOrderAt E ρ)

include hE h2 in
/-- The multiplicity of a point of the divisor of `z ↦ E(z + 2)` is the order of `E` there. -/
theorem toNat_divisor_shift (w : ℂ) :
    ((MeromorphicOn.divisor (fun z => E (z + 2)) univ) w).toNat =
      (analyticOrderAt E (w + 2)).toNat := by
  have hgd : Differentiable ℂ (fun z => E (z + 2)) := hE.comp (differentiable_id.add_const 2)
  have hg : AnalyticOnNhd ℂ (fun z => E (z + 2)) univ :=
    hgd.differentiableOn.analyticOnNhd isOpen_univ
  have hord : analyticOrderAt (fun z => E (z + 2)) w = analyticOrderAt E (w + 2) := by
    have h1 : AnalyticAt ℂ (fun z : ℂ => z + 2) w := analyticAt_id.add analyticAt_const
    have h2' : deriv (fun z : ℂ => z + 2) w ≠ 0 := by
      rw [deriv_add_const]
      simp
    exact analyticOrderAt_comp_of_deriv_ne_zero (f := E) h1 h2'
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_ne_top_of_ne_zero hE h2 (w + 2))
  rw [divisor_univ_eq_analyticOrder hg, hord, ← hn]
  simp

/-- The distinct zeros of `z ↦ E(z + 2)` and the zeros of `E`. -/
def zeroSupportEquiv :
    ZeroSupport (fun z => E (z + 2)) ≃ (zerosConfig E hE h2 hstrip hrefl).carrier where
  toFun w := ⟨(w : ℂ) + 2, apply_zeroSupport (hE.comp (differentiable_id.add_const 2)) w⟩
  invFun ρ := ⟨(ρ : ℂ) - 2,
    mem_support_divisor_of_zero (E := fun z => E (z + 2)) (a := 0)
      (hE.comp (differentiable_id.add_const 2)) (by simpa using h2)
      (by
        show E ((ρ : ℂ) - 2 + 2) = 0
        rw [sub_add_cancel]
        exact ρ.2)⟩
  left_inv w := Subtype.ext (add_sub_cancel_right _ _)
  right_inv ρ := Subtype.ext (sub_add_cancel _ _)

/-- **Copies and multiplicities.** A sum over the zeros of `E` counted by copies is the sum over
the distinct zeros with their multiplicities. -/
theorem hasSum_zerosConfig {α : Type*} [NormedAddCommGroup α] (F : ℂ → α) {S : α}
    (h : HasSum (fun q : ZeroCopy (fun z => E (z + 2)) => F (zeroOf E q)) S) :
    HasSum (fun ρ : (zerosConfig E hE h2 hstrip hrefl).carrier =>
      (zerosConfig E hE h2 hstrip hrefl).mult ρ • F ρ) S := by
  have h1 : HasSum (fun w : ZeroSupport (fun z => E (z + 2)) =>
      ((MeromorphicOn.divisor (fun z => E (z + 2)) univ) (w : ℂ)).toNat • F ((w : ℂ) + 2)) S := by
    refine h.sigma fun w => ?_
    have hs := hasSum_fintype (fun c : Fin ((MeromorphicOn.divisor (fun z => E (z + 2)) univ)
      (w : ℂ)).toNat => F (zeroOf E ⟨w, c⟩))
    have hc : ∑ c : Fin ((MeromorphicOn.divisor (fun z => E (z + 2)) univ) (w : ℂ)).toNat,
        F (zeroOf E ⟨w, c⟩) =
        ((MeromorphicOn.divisor (fun z => E (z + 2)) univ) (w : ℂ)).toNat • F ((w : ℂ) + 2) := by
      show ∑ _c : Fin ((MeromorphicOn.divisor (fun z => E (z + 2)) univ) (w : ℂ)).toNat,
        F ((w : ℂ) + 2) = _
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← hc]
    exact hs
  refine ((zeroSupportEquiv hE h2 hstrip hrefl).hasSum_iff).mp ?_
  refine h1.congr_fun fun w => ?_
  show (analyticOrderAt E ((w : ℂ) + 2)).toNat • F ((w : ℂ) + 2) = _
  rw [toNat_divisor_shift hE h2]

/-- **The zeros of a function of order one are a tempered configuration.** -/
theorem temperedConfig_zerosConfig {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ s : ℂ, ‖E s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖))) :
    SquareRootThreshold.TemperedConfig (zerosConfig E hE h2 hstrip hrefl) := by
  obtain ⟨hne2, hsum, -⟩ := exists_hasSum_logDeriv hE hC hbound h2
  have hcmp : Summable (fun q : ZeroCopy (fun z => E (z + 2)) =>
      1 / (1 + Complex.normSq (gammaOf (zeroOf E q)))) := by
    refine Summable.of_nonneg_of_le (fun q => div_nonneg zero_le_one
      (by linarith [Complex.normSq_nonneg (gammaOf (zeroOf E q))])) (fun q => ?_)
      (hsum.mul_left (9 / 2))
    have hb : 0 < ‖zeroOf E q - 2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hne2 q))
    have hγ : Complex.normSq (gammaOf (zeroOf E q)) = ‖zeroOf E q - 1 / 2‖ ^ 2 := by
      rw [gammaOf, Complex.normSq_div, Complex.normSq_I, div_one, Complex.normSq_eq_norm_sq]
    have htri : ‖zeroOf E q - 2‖ ≤ ‖zeroOf E q - 1 / 2‖ + 3 / 2 := by
      calc ‖zeroOf E q - 2‖ = ‖(zeroOf E q - 1 / 2) - ((3 / 2 : ℝ) : ℂ)‖ := by
            congr 1
            push_cast
            ring
        _ ≤ ‖zeroOf E q - 1 / 2‖ + ‖((3 / 2 : ℝ) : ℂ)‖ := norm_sub_le _ _
        _ = ‖zeroOf E q - 1 / 2‖ + 3 / 2 := by
            rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
    have ha := norm_nonneg (zeroOf E q - 1 / 2)
    have hsq : ‖zeroOf E q - 2‖ ^ 2 ≤ (‖zeroOf E q - 1 / 2‖ + 3 / 2) ^ 2 :=
      pow_le_pow_left₀ hb.le htri 2
    rw [hγ, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (7 * ‖zeroOf E q - 1 / 2‖ - 3)]
  have h := hasSum_zerosConfig hE h2 hstrip hrefl
    (fun ρ => 1 / (1 + Complex.normSq (gammaOf ρ))) hcmp.hasSum
  unfold SquareRootThreshold.TemperedConfig
  refine h.summable.congr fun ρ => ?_
  rw [nsmul_eq_mul, mul_one_div]

/-- **Weil's form of the configuration is the sum over the zeros of the transform of
`f ⋆ g̃`.** -/
theorem W_zerosConfig_eq {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) {S : ℂ}
    (h : HasSum (fun q : ZeroCopy (fun z => E (z + 2)) =>
      Hfn (EF.weilTest f g) (zeroOf E q)) S) :
    (zerosConfig E hE h2 hstrip hrefl).W f g = S := by
  have h1 := hasSum_zerosConfig hE h2 hstrip hrefl (fun ρ => Hfn (EF.weilTest f g) ρ) h
  rw [ZeroConfig.W, ← h1.tsum_eq]
  refine tsum_congr fun ρ => ?_
  rw [ZeroConfig.Wsummand, nsmul_eq_mul, mul_assoc]
  congr 1
  show _ = paperFT (EF.weilTest f g) (gammaOf ρ)
  rw [EF.paperFT_weilTest hf hg hfc hgc]

end Sums

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
