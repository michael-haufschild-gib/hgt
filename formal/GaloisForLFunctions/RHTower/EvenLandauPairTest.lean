import GaloisForLFunctions.RHTower.LandauPairTest

/-!
# Even tests at the Landau pair

`EvenHodgeIndexAtLevel Z a` is Weil positivity at level `a` restricted to even tests.

**Symmetrization.** Let `g(u) = f(-u)`.
* The zero set of ζ is invariant under `ρ ↦ 1 - ρ` and `ρ ↦ ρ̄`, so `W(g, g) = W(f, f)` and
  `W(g, f) = conj W(f, g)`.
* Hence `Re W(f + g, f + g) = 2 Re W(f, f) + 2 Re W(f, g)`.

**The cross term.** For the Landau test of an off-line pair `{ρ₀, ρ₁ = 1 - ρ̄₀}`, the divided
kernel vanishes at every zero outside the pair, including the mirrored points `ρ̄₀, ρ̄₁`. So every
summand of `W(f, g)` carries a cutoff-tail factor.

Consequently the pair inequality holds under even positivity alone, with the node errors enlarged
by `C_N ε B_w/(1+2t₀)²` and one extra window sum (`pairLandau_inequality_even`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

noncomputable section

/-- Weil positivity at level `a` on even, `C²`, pole-free tests supported in `[-a, a]`. -/
def EvenHodgeIndexAtLevel (Z : ZeroConfig) (a : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → (∀ u, f (-u) = f u) → tsupport f ⊆ Icc (-a) a →
    paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 → 0 ≤ (Z.W f f).re

theorem EvenHodgeIndexAtLevel.of_hodgeIndexAtLevel {Z : ZeroConfig} {a : ℝ}
    (h : HodgeIndexAtLevel Z a) : EvenHodgeIndexAtLevel Z a :=
  fun f hf _ hsupp h1 h2 => h f hf hsupp h1 h2

/-! ## Reflection of tests -/

theorem paperFT_comp_neg (f : ℝ → ℂ) (z : ℂ) :
    paperFT (fun u => f (-u)) z = paperFT f (-z) := by
  unfold paperFT
  rw [← integral_neg_eq_self]
  congr 1
  funext u
  simp only [neg_neg, ofReal_neg]
  ring_nf

theorem integrable_mul_cexp_of_continuous_compact {f : ℝ → ℂ} (hf : Continuous f)
    (hcpt : HasCompactSupport f) (z : ℂ) :
    Integrable (fun u : ℝ => f u * Complex.exp (I * z * u)) :=
  (hf.mul (by fun_prop)).integrable_of_hasCompactSupport (hcpt.mul_right)

theorem paperFT_add_of_continuous {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (z : ℂ) :
    paperFT (f + g) z = paperFT f z + paperFT g z := by
  unfold paperFT
  rw [← integral_add (integrable_mul_cexp_of_continuous_compact hf hfc z)
    (integrable_mul_cexp_of_continuous_compact hg hgc z)]
  congr 1
  funext u
  simp only [Pi.add_apply]
  ring

/-! ## Symmetries of the zeros of ζ -/

theorem gammaOf_conj (ρ : ℂ) : gammaOf (conj ρ) = -conj (gammaOf ρ) := by
  simp only [gammaOf, map_div₀, map_sub, map_one, Complex.conj_I]
  rw [div_neg, neg_neg]
  congr 1
  rw [map_ofNat]

theorem gammaOf_one_sub (ρ : ℂ) : gammaOf (1 - ρ) = -gammaOf ρ := by
  simp only [gammaOf]
  rw [← neg_div]
  congr 1
  ring

theorem isNontrivialZero_conj {ρ : ℂ} (h : IsNontrivialZero ρ) : IsNontrivialZero (conj ρ) := by
  have hne : ρ ≠ 1 := by
    intro h1
    have := h.2.2
    rw [h1, Complex.one_re] at this
    exact lt_irrefl _ this
  refine ⟨?_, ?_, ?_⟩
  · rw [riemannZeta_conj hne, h.1, map_zero]
  · rw [Complex.conj_re]; exact h.2.1
  · rw [Complex.conj_re]; exact h.2.2

theorem zeroMult_conj {ρ : ℂ} (h : IsNontrivialZero ρ) : zeroMult (conj ρ) = zeroMult ρ := by
  have hne : ρ ≠ 1 := by
    intro h1
    have := h.2.2
    rw [h1, Complex.one_re] at this
    exact lt_irrefl _ this
  unfold zeroMult
  rw [analyticOrderAt_zeta_conj hne]

theorem conj_mem_zetaZeroConfig {ρ : ℂ} (h : ρ ∈ zetaZeroConfig.carrier) :
    conj ρ ∈ zetaZeroConfig.carrier :=
  isNontrivialZero_conj h

theorem mult_conj_zetaZeroConfig {ρ : ℂ} (h : ρ ∈ zetaZeroConfig.carrier) :
    zetaZeroConfig.mult (conj ρ) = zetaZeroConfig.mult ρ :=
  zeroMult_conj h

theorem one_sub_eq_reflect_conj (ρ : ℂ) : 1 - ρ = Zeta23.reflect (conj ρ) := by
  simp [Zeta23.reflect]

theorem one_sub_mem_zetaZeroConfig {ρ : ℂ} (h : ρ ∈ zetaZeroConfig.carrier) :
    1 - ρ ∈ zetaZeroConfig.carrier := by
  rw [one_sub_eq_reflect_conj]
  exact zetaZeroConfig.reflect_mem _ (conj_mem_zetaZeroConfig h)

theorem mult_one_sub_zetaZeroConfig {ρ : ℂ} (h : ρ ∈ zetaZeroConfig.carrier) :
    zetaZeroConfig.mult (1 - ρ) = zetaZeroConfig.mult ρ := by
  rw [one_sub_eq_reflect_conj, zetaZeroConfig.mult_reflect _ (conj_mem_zetaZeroConfig h),
    mult_conj_zetaZeroConfig h]

/-- `ρ ↦ 1 - ρ` on the zeros of ζ. -/
def zetaCarrierOneSub : zetaZeroConfig.carrier ≃ zetaZeroConfig.carrier where
  toFun ρ := ⟨1 - ρ, one_sub_mem_zetaZeroConfig ρ.2⟩
  invFun ρ := ⟨1 - ρ, one_sub_mem_zetaZeroConfig ρ.2⟩
  left_inv ρ := by ext; simp
  right_inv ρ := by ext; simp

/-- `ρ ↦ 1 - ρ̄` on the zeros of ζ. -/
def zetaCarrierReflect : zetaZeroConfig.carrier ≃ zetaZeroConfig.carrier where
  toFun ρ := ⟨Zeta23.reflect ρ, zetaZeroConfig.reflect_mem _ ρ.2⟩
  invFun ρ := ⟨Zeta23.reflect ρ, zetaZeroConfig.reflect_mem _ ρ.2⟩
  left_inv ρ := by ext; simp [Zeta23.reflect]
  right_inv ρ := by ext; simp [Zeta23.reflect]

/-! ## Symmetrization of a test -/

theorem support_comp_neg_subset_Icc {f : ℝ → ℂ} {a : ℝ} (hf : tsupport f ⊆ Icc (-a) a) :
    Function.support (fun u => f (-u)) ⊆ Icc (-a) a := by
  intro u hu
  have h := hf (subset_tsupport f hu)
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

theorem tsupport_add_comp_neg_subset {f : ℝ → ℂ} {a : ℝ} (hf : tsupport f ⊆ Icc (-a) a) :
    tsupport (f + fun u => f (-u)) ⊆ Icc (-a) a := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  rcases Function.support_add f (fun u => f (-u)) hu with h | h
  · exact hf (subset_tsupport f h)
  · exact support_comp_neg_subset_Icc hf h

theorem hasCompactSupport_comp_neg_of_Icc {f : ℝ → ℂ} {a : ℝ} (hf : tsupport f ⊆ Icc (-a) a) :
    HasCompactSupport (fun u => f (-u)) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
    (closure_minimal (support_comp_neg_subset_Icc hf) isClosed_Icc)

theorem Wsummand_comp_neg_comp_neg (f : ℝ → ℂ) (ρ : zetaZeroConfig.carrier) :
    zetaZeroConfig.Wsummand (fun u => f (-u)) (fun u => f (-u)) ρ =
      zetaZeroConfig.Wsummand f f (zetaCarrierOneSub ρ) := by
  simp only [ZeroConfig.Wsummand, zetaCarrierOneSub, Equiv.coe_fn_mk,
    mult_one_sub_zetaZeroConfig ρ.2, paperFT_comp_neg, gammaOf_one_sub, map_neg]

theorem Wsummand_comp_neg_left (f : ℝ → ℂ) (ρ : zetaZeroConfig.carrier) :
    zetaZeroConfig.Wsummand (fun u => f (-u)) f ρ =
      conj (zetaZeroConfig.Wsummand f (fun u => f (-u)) (zetaCarrierReflect ρ)) := by
  simp only [ZeroConfig.Wsummand, zetaCarrierReflect, Equiv.coe_fn_mk,
    zetaZeroConfig.mult_reflect _ ρ.2, paperFT_comp_neg, gammaOf_reflect', map_mul,
    Complex.conj_conj, map_natCast]
  ring

theorem W_comp_neg_comp_neg (f : ℝ → ℂ) :
    zetaZeroConfig.W (fun u => f (-u)) (fun u => f (-u)) = zetaZeroConfig.W f f := by
  unfold ZeroConfig.W
  simp_rw [Wsummand_comp_neg_comp_neg]
  exact zetaCarrierOneSub.tsum_eq (fun ρ => zetaZeroConfig.Wsummand f f ρ)

theorem W_comp_neg_left (f : ℝ → ℂ) :
    zetaZeroConfig.W (fun u => f (-u)) f = conj (zetaZeroConfig.W f (fun u => f (-u))) := by
  unfold ZeroConfig.W
  simp_rw [Wsummand_comp_neg_left]
  rw [Complex.conj_tsum]
  exact zetaCarrierReflect.tsum_eq (fun ρ => conj (zetaZeroConfig.Wsummand f (fun u => f (-u)) ρ))

/-- **Symmetrization.** For a continuous compactly supported test `f` with absolutely summable
diagonal and cross Weil series, `Re W(f + f(-·)) = 2 Re W(f, f) + 2 Re W(f, f(-·))`. -/
theorem re_W_add_comp_neg {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {a : ℝ} (hsupp : tsupport f ⊆ Icc (-a) a)
    (hff : Summable (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f f ρ))
    (hfg : Summable (fun ρ : zetaZeroConfig.carrier =>
      zetaZeroConfig.Wsummand f (fun u => f (-u)) ρ)) :
    (zetaZeroConfig.W (f + fun u => f (-u)) (f + fun u => f (-u))).re =
      2 * (zetaZeroConfig.W f f).re + 2 * (zetaZeroConfig.W f (fun u => f (-u))).re := by
  set g : ℝ → ℂ := fun u => f (-u) with hg_def
  have hgc : Continuous g := hf.comp continuous_neg
  have hgcpt : HasCompactSupport g := hasCompactSupport_comp_neg_of_Icc hsupp
  have hadd : ∀ z, paperFT (f + g) z = paperFT f z + paperFT g z := fun z =>
    paperFT_add_of_continuous hf hgc hfc hgcpt z
  have hsplit : ∀ ρ : zetaZeroConfig.carrier, zetaZeroConfig.Wsummand (f + g) (f + g) ρ =
      zetaZeroConfig.Wsummand f f ρ + zetaZeroConfig.Wsummand f g ρ +
        zetaZeroConfig.Wsummand g f ρ + zetaZeroConfig.Wsummand g g ρ := fun ρ => by
    simp only [ZeroConfig.Wsummand, hadd, map_add]
    ring
  have hgg : Summable (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand g g ρ) := by
    have e : (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand g g ρ) =
        (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f f ρ) ∘ zetaCarrierOneSub :=
      funext fun ρ => Wsummand_comp_neg_comp_neg f ρ
    rw [e]
    exact zetaCarrierOneSub.summable_iff.2 hff
  have hgf : Summable (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand g f ρ) := by
    have h1 : Summable ((fun ρ : zetaZeroConfig.carrier =>
        zetaZeroConfig.Wsummand f (fun u => f (-u)) ρ) ∘ zetaCarrierReflect) :=
      zetaCarrierReflect.summable_iff.2 hfg
    have e : (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand g f ρ) =
        fun ρ => conj (((fun ρ : zetaZeroConfig.carrier =>
          zetaZeroConfig.Wsummand f (fun u => f (-u)) ρ) ∘ zetaCarrierReflect) ρ) :=
      funext fun ρ => Wsummand_comp_neg_left f ρ
    rw [e]
    exact Complex.summable_conj.2 h1
  have hW : zetaZeroConfig.W (f + g) (f + g) = zetaZeroConfig.W f f + zetaZeroConfig.W f g +
      zetaZeroConfig.W g f + zetaZeroConfig.W g g := by
    unfold ZeroConfig.W
    simp_rw [hsplit]
    rw [(((hff.add hfg).add hgf)).tsum_add hgg, ((hff.add hfg)).tsum_add hgf, hff.tsum_add hfg]
  rw [hW, hg_def, W_comp_neg_comp_neg, W_comp_neg_left]
  simp only [add_re, conj_re]
  ring

/-! ## The cross term -/

/-- `1/(D₋²D₊²) ≤ (1/(1+t₀))(1/D₋³ + 1/D₊³)` with `D_± = 1 + |x ∓ t₀|`. -/
theorem inv_sq_mul_inv_sq_le_window {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (x : ℝ) :
    1 / ((1 + |x - t₀|) ^ 2 * (1 + |x + t₀|) ^ 2) ≤
      1 / (1 + t₀) * (1 / (1 + |x - t₀|) ^ 3 + 1 / (1 + |x + t₀|) ^ 3) := by
  set D₁ := 1 + |x - t₀| with hD₁
  set D₂ := 1 + |x + t₀| with hD₂
  have h1 : 1 ≤ D₁ := by rw [hD₁]; linarith [abs_nonneg (x - t₀)]
  have h2 : 1 ≤ D₂ := by rw [hD₂]; linarith [abs_nonneg (x + t₀)]
  have hsum : 2 + 2 * t₀ ≤ D₁ + D₂ := by
    have := abs_sub_abs_le_abs_sub (x + t₀) (x - t₀)
    have h3 : |x + t₀ - (x - t₀)| = 2 * t₀ := by
      rw [show x + t₀ - (x - t₀) = 2 * t₀ by ring, abs_of_nonneg (by linarith)]
    have h4 := abs_sub (x + t₀) (x - t₀)
    rw [hD₁, hD₂]
    linarith
  have ht1 : 0 < 1 + t₀ := by linarith
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have hnn : 0 ≤ 1 / (1 + t₀) * (1 / D₁ ^ 3) := by positivity
  have hnn' : 0 ≤ 1 / (1 + t₀) * (1 / D₂ ^ 3) := by positivity
  have key : ∀ {P Q : ℝ}, 0 < P → P ≤ Q → 1 + t₀ ≤ Q →
      1 / (P ^ 2 * Q ^ 2) ≤ 1 / (1 + t₀) * (1 / P ^ 3) := by
    intro P Q hP hPQ hQ
    have hQ0 : 0 < Q := lt_of_lt_of_le hP hPQ
    have hk : P / Q ^ 2 ≤ 1 / (1 + t₀) := by
      rw [div_le_div_iff₀ (by positivity) ht1, one_mul, sq]
      calc P * (1 + t₀) ≤ Q * Q := by nlinarith
        _ = Q * Q := rfl
    calc 1 / (P ^ 2 * Q ^ 2) = 1 / P ^ 3 * (P / Q ^ 2) := by field_simp
      _ ≤ 1 / P ^ 3 * (1 / (1 + t₀)) := mul_le_mul_of_nonneg_left hk (by positivity)
      _ = 1 / (1 + t₀) * (1 / P ^ 3) := by ring
  rcases le_total D₁ D₂ with h | h
  · have := key hD₁0 h (by linarith)
    linarith
  · have := key hD₂0 h (by linarith)
    rw [mul_comm (D₂ ^ 2)] at this
    linarith

/-- **The cross term of a test concentrated at height `t₀`.** Suppose `|f̂(γ_ρ)| ≤ S/(1+|γ-t₀|)²`
at every zero and `≤ E/(1+|γ-t₀|)²` at every zero outside a set `P` of zeros at height `t₀ > 0`.
Then `W(f, f(-·))` converges absolutely and `|W(f, f(-·))| ≤ S E (48 A₀ log(t₀+3))/(1+t₀)`. -/
theorem norm_W_comp_neg_le {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {f : ℝ → ℂ} {t₀ S E : ℝ} (ht₀ : 0 < t₀) (hS0 : 0 ≤ S) (hE0 : 0 ≤ E) (P : ℂ → Prop)
    (hP : ∀ ρ ∈ zetaZeroConfig.carrier, P ρ → ρ.im = t₀)
    (hS : ∀ ρ ∈ zetaZeroConfig.carrier, ‖paperFT f (gammaOf ρ)‖ ≤ S / (1 + |ρ.im - t₀|) ^ 2)
    (hE : ∀ ρ ∈ zetaZeroConfig.carrier, ¬ P ρ →
      ‖paperFT f (gammaOf ρ)‖ ≤ E / (1 + |ρ.im - t₀|) ^ 2) :
    Summable (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f (fun u => f (-u)) ρ) ∧
      ‖zetaZeroConfig.W f (fun u => f (-u))‖ ≤
        S * E * (1 / (1 + t₀)) * (24 * A₀ * Real.log (t₀ + 3) + 24 * A₀ * Real.log (t₀ + 3)) := by
  obtain ⟨hs₁, hl₁⟩ := window_tsum_le zetaZeroConfig hA₀ hloc t₀
  obtain ⟨hs₂, hl₂⟩ := window_tsum_le zetaZeroConfig hA₀ hloc (-t₀)
  rw [abs_neg, abs_of_pos ht₀] at hl₂
  rw [abs_of_pos ht₀] at hl₁
  have hconjF : ∀ ρ : ℂ, paperFT (fun u => f (-u)) ((starRingEnd ℂ) (gammaOf ρ)) =
      paperFT f (gammaOf ((starRingEnd ℂ) ρ)) := fun ρ => by
    rw [paperFT_comp_neg, gammaOf_conj]
  -- the pointwise product bound
  have hprod : ∀ ρ ∈ zetaZeroConfig.carrier, ‖paperFT f (gammaOf ρ)‖ *
      ‖paperFT f (gammaOf ((starRingEnd ℂ) ρ))‖ ≤
        S * E * (1 / ((1 + |ρ.im - t₀|) ^ 2 * (1 + |ρ.im + t₀|) ^ 2)) := by
    intro ρ hρ
    have hc := conj_mem_zetaZeroConfig hρ
    have hcim : ((starRingEnd ℂ) ρ).im = -ρ.im := Complex.conj_im ρ
    have habs : |((starRingEnd ℂ) ρ).im - t₀| = |ρ.im + t₀| := by
      rw [hcim, show -ρ.im - t₀ = -(ρ.im + t₀) by ring, abs_neg]
    have hD₁ : 0 < (1 + |ρ.im - t₀|) ^ 2 := by positivity
    have hD₂ : 0 < (1 + |ρ.im + t₀|) ^ 2 := by positivity
    have e : S * E * (1 / ((1 + |ρ.im - t₀|) ^ 2 * (1 + |ρ.im + t₀|) ^ 2)) =
        (S / (1 + |ρ.im - t₀|) ^ 2) * (E / (1 + |ρ.im + t₀|) ^ 2) := by
      field_simp
    have e' : S * E * (1 / ((1 + |ρ.im - t₀|) ^ 2 * (1 + |ρ.im + t₀|) ^ 2)) =
        (E / (1 + |ρ.im - t₀|) ^ 2) * (S / (1 + |ρ.im + t₀|) ^ 2) := by
      field_simp
    by_cases hPρ : P ρ
    · have him := hP ρ hρ hPρ
      have hnP : ¬ P ((starRingEnd ℂ) ρ) := fun h' => by
        have := hP _ hc h'
        rw [hcim] at this
        linarith
      have h2 := hE _ hc hnP
      rw [habs] at h2
      rw [e]
      exact mul_le_mul (hS ρ hρ) h2 (norm_nonneg _) (by positivity)
    · have h1 := hE ρ hρ hPρ
      have h2 := hS _ hc
      rw [habs] at h2
      rw [e']
      exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  set B : zetaZeroConfig.carrier → ℝ := fun ρ => S * E * (1 / (1 + t₀)) *
    ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - t₀|) ^ 3 +
      (zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - -t₀|) ^ 3) with hB
  have hbound : ∀ ρ : zetaZeroConfig.carrier,
      ‖zetaZeroConfig.Wsummand f (fun u => f (-u)) ρ‖ ≤ B ρ := by
    intro ρ
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    have hnorm : ‖zetaZeroConfig.Wsummand f (fun u => f (-u)) ρ‖ = (zetaZeroConfig.mult ρ : ℝ) *
        (‖paperFT f (gammaOf ρ)‖ * ‖paperFT f (gammaOf ((starRingEnd ℂ) (ρ : ℂ)))‖) := by
      simp only [ZeroConfig.Wsummand, hconjF, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
      ring
    rw [hnorm]
    have h1 := hprod ρ ρ.2
    have h2 := inv_sq_mul_inv_sq_le_window ht₀.le (ρ : ℂ).im
    have h3 : S * E * (1 / ((1 + |(ρ : ℂ).im - t₀|) ^ 2 * (1 + |(ρ : ℂ).im + t₀|) ^ 2)) ≤
        S * E * (1 / (1 + t₀) * (1 / (1 + |(ρ : ℂ).im - t₀|) ^ 3 +
          1 / (1 + |(ρ : ℂ).im + t₀|) ^ 3)) :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg hS0 hE0)
    have e : (ρ : ℂ).im - -t₀ = (ρ : ℂ).im + t₀ := by ring
    calc (zetaZeroConfig.mult ρ : ℝ) *
          (‖paperFT f (gammaOf ρ)‖ * ‖paperFT f (gammaOf ((starRingEnd ℂ) (ρ : ℂ)))‖)
        ≤ (zetaZeroConfig.mult ρ : ℝ) * (S * E * (1 / (1 + t₀) *
            (1 / (1 + |(ρ : ℂ).im - t₀|) ^ 3 + 1 / (1 + |(ρ : ℂ).im + t₀|) ^ 3))) :=
          mul_le_mul_of_nonneg_left (h1.trans h3) hm
      _ = B ρ := by rw [hB]; simp only [e]; ring
  have hBs : Summable B := by
    have := (hs₁.add hs₂).mul_left (S * E * (1 / (1 + t₀)))
    exact this
  have hsum : Summable (fun ρ : zetaZeroConfig.carrier =>
      zetaZeroConfig.Wsummand f (fun u => f (-u)) ρ) := Summable.of_norm_bounded hBs hbound
  refine ⟨hsum, ?_⟩
  calc ‖zetaZeroConfig.W f (fun u => f (-u))‖
      ≤ ∑' ρ, B ρ := by
        unfold ZeroConfig.W
        exact tsum_of_norm_bounded hBs.hasSum hbound
    _ = S * E * (1 / (1 + t₀)) *
        (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - t₀|) ^ 3 +
          ∑' ρ : zetaZeroConfig.carrier,
            (zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - -t₀|) ^ 3) := by
        rw [hB, tsum_mul_left, hs₁.tsum_add hs₂]
    _ ≤ _ := by
        have hc0 : 0 ≤ S * E * (1 / (1 + t₀)) := by
          have : 0 < 1 + t₀ := by linarith
          positivity
        exact mul_le_mul_of_nonneg_left (add_le_add hl₁ hl₂) hc0

/-! ## The even pair inequality -/

theorem pair_node_arith_even {x₀ x₁ y₀ y₁ e lam M R c CN : ℝ} (hM : 2 ≤ M) (hR : 0 ≤ R)
    (he0 : 0 ≤ e) (hc : 0 ≤ c) (hCN : 0 ≤ CN) (hy₀ : y₀ ≤ e) (hy₁ : y₁ ≤ e) (hy₀0 : 0 ≤ y₀)
    (hy₁0 : 0 ≤ y₁) (hx₀ : lam ≤ x₀) (hx₁ : lam ≤ x₁) (hlam : 0 ≤ lam)
    (hmain : 0 ≤ M * (-(x₀ * x₁) + x₀ * y₁ + y₀ * x₁ + y₀ * y₁) + e ^ 2 * R +
      (x₀ + y₀ + x₁ + y₁ + CN * e) * e * c) :
    lam ≤ e * (1 + c / 2) * (3 + (R + (2 + CN) * c) / 2) := by
  have hx₀0 : 0 ≤ x₀ := le_trans hlam hx₀
  have hx₁0 : 0 ≤ x₁ := le_trans hlam hx₁
  set e' := e * (1 + c / 2) with he'
  have hk : 1 ≤ (1 + c / 2) ^ 2 := one_le_pow₀ (by linarith)
  have hk0 : 0 < (1 + c / 2) ^ 2 := by positivity
  set R' := (R + (2 + CN) * c) / (1 + c / 2) ^ 2 with hR'
  have hR'0 : 0 ≤ R' := div_nonneg (by positivity) hk0.le
  have hR'le : R' ≤ R + (2 + CN) * c := div_le_self (by positivity) hk
  have hy'₀ : y₀ + e * c / 2 ≤ e' := by rw [he']; nlinarith
  have hy'₁ : y₁ + e * c / 2 ≤ e' := by rw [he']; nlinarith
  have he'2 : e' ^ 2 * R' = e ^ 2 * (R + (2 + CN) * c) := by
    rw [he', hR']; field_simp
  have hmain' : 0 ≤ M * (-(x₀ * x₁) + x₀ * (y₁ + e * c / 2) + (y₀ + e * c / 2) * x₁ +
      (y₀ + e * c / 2) * (y₁ + e * c / 2)) + e' ^ 2 * R' := by
    rw [he'2]
    have h1 : (x₀ + x₁) * e * c ≤ M * ((e * c / 2) * (x₀ + x₁)) := by
      have : 0 ≤ (e * c / 2) * (x₀ + x₁) := by positivity
      nlinarith
    have h2 : 0 ≤ M * ((y₀ + e * c / 2) * (y₁ + e * c / 2) - y₀ * y₁) := by
      have : 0 ≤ (y₀ + e * c / 2) * (y₁ + e * c / 2) - y₀ * y₁ := by
        have : 0 ≤ e * c / 2 := by positivity
        nlinarith
      exact mul_nonneg (by linarith) this
    have h3 : (y₀ + y₁ + CN * e) * e * c ≤ (2 + CN) * c * e ^ 2 := by
      have hec : 0 ≤ e * c := mul_nonneg he0 hc
      have : y₀ + y₁ + CN * e ≤ (2 + CN) * e := by linarith
      nlinarith
    nlinarith
  have h := pair_node_arith hM hR'0 (by positivity) hy'₀ hy'₁ (by positivity) hx₀ hx₁ hlam hmain'
  calc lam ≤ e' * (3 + R' / 2) := h
    _ ≤ e' * (3 + (R + (2 + CN) * c) / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = _ := by rw [he']

/-- **Even positivity bounds the diagonal from below.** If `f` is a `C²` pole-free test in
`[-a, a]` whose transform at the zeros satisfies the bounds of `norm_W_comp_neg_le`, then even
positivity at level `a` gives `Re W(f, f) ≥ -S E (48 A₀ log(t₀+3))/(1+t₀)`. -/
theorem neg_le_re_W_of_evenHodge {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {a : ℝ}
    (hH : EvenHodgeIndexAtLevel zetaZeroConfig a) {f : ℝ → ℂ} (hf2 : ContDiff ℝ 2 f)
    (hfsupp : tsupport f ⊆ Icc (-a) a) (hp1 : paperFT f (I / 2) = 0)
    (hp2 : paperFT f (-(I / 2)) = 0)
    (hff : Summable (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f f ρ))
    {t₀ S E : ℝ} (ht₀ : 0 < t₀) (hS0 : 0 ≤ S) (hE0 : 0 ≤ E) (P : ℂ → Prop)
    (hP : ∀ ρ ∈ zetaZeroConfig.carrier, P ρ → ρ.im = t₀)
    (hS : ∀ ρ ∈ zetaZeroConfig.carrier, ‖paperFT f (gammaOf ρ)‖ ≤ S / (1 + |ρ.im - t₀|) ^ 2)
    (hE : ∀ ρ ∈ zetaZeroConfig.carrier, ¬ P ρ →
      ‖paperFT f (gammaOf ρ)‖ ≤ E / (1 + |ρ.im - t₀|) ^ 2) :
    -(S * E * (1 / (1 + t₀)) * (24 * A₀ * Real.log (t₀ + 3) + 24 * A₀ * Real.log (t₀ + 3))) ≤
      (zetaZeroConfig.W f f).re := by
  have hfcpt : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hfsupp
  have hgc : Continuous (fun u => f (-u)) := hf2.continuous.comp continuous_neg
  have hgcpt := hasCompactSupport_comp_neg_of_Icc hfsupp
  have hfe : ∀ z, paperFT (f + fun u => f (-u)) z = paperFT f z + paperFT f (-z) := fun z => by
    rw [paperFT_add_of_continuous hf2.continuous hgc hfcpt hgcpt, paperFT_comp_neg]
  have hpos := hH (f + fun u => f (-u)) (hf2.add (hf2.comp contDiff_neg))
    (fun u => by simp only [Pi.add_apply, neg_neg]; ring) (tsupport_add_comp_neg_subset hfsupp)
    (by rw [hfe, hp1, hp2, add_zero])
    (by rw [hfe, hp2, neg_neg, hp1, add_zero])
  obtain ⟨hfg, hcross⟩ := norm_W_comp_neg_le hA₀ hloc ht₀ hS0 hE0 P hP hS hE
  have hsym := re_W_add_comp_neg hf2.continuous hfcpt hfsupp hff hfg
  have hre := Complex.re_le_norm (zetaZeroConfig.W f (fun u => f (-u)))
  linarith

theorem even_pair_constant_le {CN A₀ L t₀ : ℝ} (hCN : 1 ≤ CN) (hA₀ : 1 ≤ A₀) (hL : 0 ≤ L)
    (ht₀ : 0 ≤ t₀) (hLt : L = Real.log (t₀ + 3) := by rfl) :
    (1 + CN * (1 / (1 + t₀)) * (24 * A₀ * L + 24 * A₀ * L) / 2) *
      (3 + (CN ^ 2 * (24 * A₀ * L) + (2 + CN) * (CN * (1 / (1 + t₀)) *
        (24 * A₀ * L + 24 * A₀ * L))) / 2) ≤
      49 * CN ^ 3 * A₀ ^ 2 * (147 + 12 * L) := by
  have ht1 : 0 < 1 + t₀ := by linarith
  have hLle : L ≤ 2 * (1 + t₀) := by
    rw [hLt]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < t₀ + 3 by linarith)
    linarith
  have hq : L * (1 / (1 + t₀)) ≤ 2 := by
    rw [mul_one_div, div_le_iff₀ ht1]; linarith
  set c := CN * (1 / (1 + t₀)) * (24 * A₀ * L + 24 * A₀ * L) with hc_def
  have hc : c ≤ 96 * CN * A₀ := by
    have e : c = 48 * CN * A₀ * (L * (1 / (1 + t₀))) := by rw [hc_def]; ring
    rw [e]
    have : 0 ≤ 48 * CN * A₀ := by positivity
    nlinarith
  have hc0 : 0 ≤ c := by rw [hc_def]; positivity
  have h1 : 1 + c / 2 ≤ 49 * CN * A₀ := by nlinarith
  have h2 : 3 + (CN ^ 2 * (24 * A₀ * L) + (2 + CN) * c) / 2 ≤ CN ^ 2 * A₀ * (147 + 12 * L) := by
    have h3 : (2 + CN) * c ≤ 3 * CN * (96 * CN * A₀) := by
      have : 2 + CN ≤ 3 * CN := by linarith
      exact mul_le_mul this hc hc0 (by positivity)
    have h4 : 3 ≤ 3 * (CN ^ 2 * A₀) := by
      have : 1 ≤ CN ^ 2 * A₀ := by nlinarith
      linarith
    nlinarith
  calc (1 + c / 2) * (3 + (CN ^ 2 * (24 * A₀ * L) + (2 + CN) * c) / 2)
      ≤ (49 * CN * A₀) * (CN ^ 2 * A₀ * (147 + 12 * L)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 49 * CN ^ 3 * A₀ ^ 2 * (147 + 12 * L) := by ring

/-- **The pair inequality under even positivity.** As `pairLandau_inequality`, with the level-`a`
Hodge index replaced by its restriction to even tests and `t₀ > 0`: if the node values satisfy
`|X_j| ≥ λ ≥ 0`, then `λ ≤ ε B_w (1+t₀)² · 49 N³ A₀² (147 + 12 log(t₀+3))`. -/
theorem pairLandau_inequality_even {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier)
    (hoff : ρ₀.re ≠ 1 / 2) (ht₀ : 0 < ρ₀.im) {h : ℝ → ℂ} (hh : SuperExpDecay h)
    (hprod : ∀ z, (z - gammaOf ρ₀) ^ zetaZeroConfig.mult ρ₀ *
      (z - (starRingEnd ℂ) (gammaOf ρ₀)) ^ zetaZeroConfig.mult ρ₀ * paperFT h z =
        paperFT (tiltedPhi θ) z)
    {U w s a : ℝ} (hw : 0 < w) (hw4 : 4 * w ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1)
    (ha : U + w + s ≤ a) (hH : EvenHodgeIndexAtLevel zetaZeroConfig a) {lam : ℝ} (hlam : 0 ≤ lam)
    (hX₀ : lam ≤ ‖paperFT h (gammaOf ρ₀)‖ *
      ‖paperFT (scaledBumpPolarFree w ρ₀.im) (gammaOf ρ₀)‖)
    (hX₁ : lam ≤ ‖paperFT h ((starRingEnd ℂ) (gammaOf ρ₀))‖ *
      ‖paperFT (scaledBumpPolarFree w ρ₀.im) ((starRingEnd ℂ) (gammaOf ρ₀))‖) :
    lam ≤ expTail h (1 / 2) U * (scaledBumpConst w * (1 + ρ₀.im) ^ 2) *
      (49 * (1 + 4 / (s * |ρ₀.re - 1 / 2|)) ^ 3 * A₀ ^ 2 * (147 + 12 * Real.log (ρ₀.im + 3))) := by
  have hnt : IsNontrivialZero ρ₀ := hρ₀
  set t₀ := ρ₀.im with ht₀def
  set γ₀ := gammaOf ρ₀ with hγ₀def
  set γ₁ := (starRingEnd ℂ) γ₀ with hγ₁def
  set ρ₁ := Zeta23.reflect ρ₀ with hρ₁def
  have h₁ : ρ₁ ∈ zetaZeroConfig.carrier := zetaZeroConfig.reflect_mem ρ₀ hρ₀
  have hγ₁ρ : gammaOf ρ₁ = γ₁ := by rw [hρ₁def, gammaOf_reflect']
  have hne : ρ₀ ≠ ρ₁ := by
    intro h; have := congrArg Complex.re h
    simp [hρ₁def, Zeta23.reflect] at this; exact hoff (by linarith)
  have hγ₀im : γ₀.im = 1 / 2 - ρ₀.re := WeilEF.gammaOf_im ρ₀
  have hγ₀re : γ₀.re = t₀ := WeilEF.gammaOf_re ρ₀
  have him : γ₀.im ≠ 0 := by rw [hγ₀im]; intro h; exact hoff (by linarith)
  have him2 : |γ₀.im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt ⟨hnt.2.1, hnt.2.2⟩).le
  have him2' : |γ₁.im| ≤ 1 / 2 := by rw [hγ₁def, Complex.conj_im, abs_neg]; exact him2
  have hγ₁re : γ₁.re = t₀ := by rw [hγ₁def, Complex.conj_re]; exact hγ₀re
  have habsim : |γ₀.im| = |ρ₀.re - 1 / 2| := by rw [hγ₀im, abs_sub_comm]
  -- node values
  set κ := scaledBumpPolarFree w t₀ with hκ
  set X₀ := paperFT h γ₀ * paperFT κ γ₀ with hX₀def
  set X₁ := paperFT h γ₁ * paperFT κ γ₁ with hX₁def
  set Y₀ := paperFT (cutoffTail U h) γ₀ * paperFT κ γ₀ with hY₀def
  set Y₁ := paperFT (cutoffTail U h) γ₁ * paperFT κ γ₁ with hY₁def
  set Q := X₀ * (starRingEnd ℂ) X₁ with hQdef
  set v := pairPhase Q with hvdef
  have hv : ‖v‖ = 1 := norm_pairPhase Q
  set c₁ := pairC₁ γ₀ s v
  set c₂ := pairC₂ γ₀ s v
  set f := pairLandauTest h U w t₀ c₁ c₂ s with hfdef
  have hf : ∀ z, paperFT f z = nodeSymbol c₁ c₂ s z *
      ((paperFT h z - paperFT (cutoffTail U h) z) * paperFT κ z) :=
    fun z => paperFT_pairLandauTest hh U hw t₀ c₁ c₂ s z
  have hfγ₀ : paperFT f γ₀ = X₀ - Y₀ := by
    rw [hf, nodeSymbol_pairC_γ₀]; ring
  have hfγ₁ : paperFT f γ₁ = v * (X₁ - Y₁) := by
    rw [hf, hγ₁def, nodeSymbol_pairC_γ₁ him hs]; ring
  -- Hodge positivity
  have hpolar := paperFT_pairLandauTest_polar hh U hw t₀ c₁ c₂ s
  -- bounds on the strip
  set ε := expTail h (1 / 2) U with hε
  set G := expTail h (1 / 2) (-1) with hG
  set Bw := scaledBumpConst w * (1 + t₀) ^ 2 with hBw
  set CN := 1 + 4 / (s * |ρ₀.re - 1 / 2|) with hCN
  have hε0 : 0 ≤ ε := expTail_nonneg _ _ _
  have hG0 : 0 ≤ G := expTail_nonneg _ _ _
  have hBw0 : 0 ≤ Bw := by have := scaledBumpConst_nonneg hw; positivity
  have hCN1 : 1 ≤ CN := by
    have : 0 ≤ 4 / (s * |ρ₀.re - 1 / 2|) := by positivity
    linarith
  have hN : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖nodeSymbol c₁ c₂ s z‖ ≤ CN := by
    intro z hz
    have := norm_nodeSymbol_pairC_le him him2 hs hs1 hv hz
    rwa [habsim] at this
  have hκb : ∀ z : ℂ, |z.im| ≤ 1 / 2 →
      ‖paperFT κ z‖ ≤ Bw / (1 + |z.re - t₀|) ^ 2 := by
    intro z hz
    have := norm_paperFT_scaledBumpPolarFree_le hw hw4 t₀ hz
    rw [abs_of_nonneg ht₀.le] at this
    rw [hBw]; exact this
  have htail : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖paperFT (cutoffTail U h) z‖ ≤ ε :=
    fun z hz => norm_paperFT_cutoffTail_le hh hz
  have hhb : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖paperFT h z‖ ≤ G :=
    fun z hz => norm_paperFT_le_expTail_half hh hz
  -- the pointwise bound for `f̂`
  have hfb : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ∀ E : ℝ, ‖paperFT h z‖ ≤ E - ε →
      ‖paperFT f z‖ ≤ CN * E * Bw / (1 + |z.re - t₀|) ^ 2 := by
    intro z hz E hE
    rw [hf, norm_mul, norm_mul]
    have h1 := hN z hz
    have h2 : ‖paperFT h z - paperFT (cutoffTail U h) z‖ ≤ E :=
      (norm_sub_le _ _).trans (by linarith [htail z hz])
    have h3 := hκb z hz
    have hE0 : 0 ≤ E := le_trans (norm_nonneg _) h2
    calc ‖nodeSymbol c₁ c₂ s z‖ * (‖paperFT h z - paperFT (cutoffTail U h) z‖ * ‖paperFT κ z‖)
        ≤ CN * (E * (Bw / (1 + |z.re - t₀|) ^ 2)) := by gcongr
      _ = CN * E * Bw / (1 + |z.re - t₀|) ^ 2 := by ring
  have hzero_pts : ∀ ρ ∈ zetaZeroConfig.carrier,
      |(gammaOf ρ).im| ≤ 1 / 2 ∧ |((starRingEnd ℂ) (gammaOf ρ)).im| ≤ 1 / 2 ∧
      (gammaOf ρ).re = ρ.im ∧ ((starRingEnd ℂ) (gammaOf ρ)).re = ρ.im := by
    intro ρ hρ
    have h : IsNontrivialZero ρ := hρ
    have hIm := (WeilEF.abs_gammaOf_im_lt ⟨h.2.1, h.2.2⟩).le
    exact ⟨hIm, by rw [Complex.conj_im, abs_neg]; exact hIm, WeilEF.gammaOf_re ρ,
      by rw [Complex.conj_re, WeilEF.gammaOf_re]⟩
  have hsq4 : ∀ D : ℝ, 1 ≤ D → ∀ A : ℝ, 0 ≤ A → A / D ^ 2 * (A / D ^ 2) ≤ A ^ 2 / D ^ 3 := by
    intro D hD A hA
    rw [div_mul_div_comm, ← sq, ← pow_add]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_right₀ hD (by norm_num)
  have hall : ∀ ρ ∈ zetaZeroConfig.carrier, ‖paperFT f (gammaOf ρ)‖ *
      ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖ ≤
        (CN * (G + ε) * Bw) ^ 2 / (1 + |ρ.im - t₀|) ^ 3 := by
    intro ρ hρ
    obtain ⟨hi1, hi2, hr1, hr2⟩ := hzero_pts ρ hρ
    have b1 := hfb _ hi1 (G + ε) (by linarith [hhb _ hi1])
    have b2 := hfb _ hi2 (G + ε) (by linarith [hhb _ hi2])
    rw [hr1] at b1; rw [hr2] at b2
    have hD : 1 ≤ 1 + |ρ.im - t₀| := by linarith [abs_nonneg (ρ.im - t₀)]
    calc ‖paperFT f (gammaOf ρ)‖ * ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖
        ≤ (CN * (G + ε) * Bw / (1 + |ρ.im - t₀|) ^ 2) *
            (CN * (G + ε) * Bw / (1 + |ρ.im - t₀|) ^ 2) :=
          mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
      _ ≤ (CN * (G + ε) * Bw) ^ 2 / (1 + |ρ.im - t₀|) ^ 3 := hsq4 _ hD _ (by positivity)
  have hother : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ ρ₁ → ‖paperFT f (gammaOf ρ)‖ *
      ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ (CN * ε * Bw) ^ 2 / (1 + |ρ.im - t₀|) ^ 3 := by
    intro ρ hρ h0 h1
    obtain ⟨hi1, hi2, hr1, hr2⟩ := hzero_pts ρ hρ
    have hz1 : paperFT h (gammaOf ρ) = 0 :=
      paperFT_divided_eq_zero_of_zero hθ0 hθ hprod hρ h0 h1
    have hrefl := zetaZeroConfig.reflect_mem ρ hρ
    have hz2 : paperFT h ((starRingEnd ℂ) (gammaOf ρ)) = 0 := by
      rw [← gammaOf_reflect']
      refine paperFT_divided_eq_zero_of_zero hθ0 hθ hprod hrefl ?_ ?_
      · intro h; apply h1; rw [hρ₁def, ← h, reflect_reflect]
      · intro h; apply h0
        have := congrArg Zeta23.reflect h
        rwa [reflect_reflect, reflect_reflect] at this
    have b1 := hfb _ hi1 ε (by rw [hz1, norm_zero]; linarith)
    have b2 := hfb _ hi2 ε (by rw [hz2, norm_zero]; linarith)
    rw [hr1] at b1; rw [hr2] at b2
    have hD : 1 ≤ 1 + |ρ.im - t₀| := by linarith [abs_nonneg (ρ.im - t₀)]
    calc ‖paperFT f (gammaOf ρ)‖ * ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖
        ≤ (CN * ε * Bw / (1 + |ρ.im - t₀|) ^ 2) * (CN * ε * Bw / (1 + |ρ.im - t₀|) ^ 2) :=
          mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
      _ ≤ (CN * ε * Bw) ^ 2 / (1 + |ρ.im - t₀|) ^ 3 := hsq4 _ hD _ (by positivity)
  have hsplit := re_W_le_pair_add_window hA₀ hloc hρ₀ h₁ hne hγ₁ρ (by positivity) hall hother
  rw [hγ₁ρ, hfγ₀, hfγ₁, abs_of_nonneg ht₀.le] at hsplit
  -- the node block
  have hQv : X₀ * (starRingEnd ℂ) X₁ * (starRingEnd ℂ) v = -(‖X₀ * (starRingEnd ℂ) X₁‖ : ℂ) :=
    mul_conj_pairPhase Q
  have hblock := OffLinePairData.re_node_block_le (Y₀ := Y₀) (Y₁ := Y₁) hv hQv
  have hY₀ : ‖Y₀‖ ≤ ε * Bw := by
    rw [hY₀def, norm_mul]
    have := hκb γ₀ him2; rw [hγ₀re, sub_self, abs_zero, add_zero, one_pow, div_one] at this
    exact mul_le_mul (htail γ₀ him2) this (norm_nonneg _) hε0
  have hY₁ : ‖Y₁‖ ≤ ε * Bw := by
    rw [hY₁def, norm_mul]
    have := hκb γ₁ him2'; rw [hγ₁re, sub_self, abs_zero, add_zero, one_pow, div_one] at this
    exact mul_le_mul (htail γ₁ him2') this (norm_nonneg _) hε0
  have hm1 : (1 : ℝ) ≤ zetaZeroConfig.mult ρ₀ := by
    exact_mod_cast zetaZeroConfig.one_le_mult ρ₀ hρ₀
  have hmr : zetaZeroConfig.mult ρ₁ = zetaZeroConfig.mult ρ₀ := zetaZeroConfig.mult_reflect ρ₀ hρ₀
  rw [hmr] at hsplit
  set M := (zetaZeroConfig.mult ρ₀ : ℝ) + zetaZeroConfig.mult ρ₀ with hMdef
  have hM2 : 2 ≤ M := by rw [hMdef]; linarith
  set R := CN ^ 2 * (24 * A₀ * Real.log (t₀ + 3)) with hR
  have hlog0 : 0 ≤ Real.log (t₀ + 3) := Real.log_nonneg (by linarith)
  have hR0 : 0 ≤ R := by have : 0 ≤ A₀ := by linarith
                         positivity
  -- the diagonal series converges absolutely
  obtain ⟨hws₁, -⟩ := window_tsum_le zetaZeroConfig hA₀ hloc t₀
  have hff : Summable (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f f ρ) := by
    refine Summable.of_norm_bounded (hws₁.mul_left ((CN * (G + ε) * Bw) ^ 2)) fun ρ => ?_
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    simp only [ZeroConfig.Wsummand, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
    have := hall ρ ρ.2
    calc (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ *
          ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖
        ≤ (zetaZeroConfig.mult ρ : ℝ) * ((CN * (G + ε) * Bw) ^ 2 / (1 + |(ρ : ℂ).im - t₀|) ^ 3) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left this hm
      _ = _ := by ring
  -- the cross term
  have hρ₁im : ρ₁.im = t₀ := by simp [hρ₁def, Zeta23.reflect, ht₀def]
  set S := ‖X₀‖ + ‖Y₀‖ + ‖X₁‖ + ‖Y₁‖ + CN * ε * Bw with hS
  have hsmall : ∀ ρ ∈ zetaZeroConfig.carrier, ¬ (ρ = ρ₀ ∨ ρ = ρ₁) →
      ‖paperFT f (gammaOf ρ)‖ ≤ CN * ε * Bw / (1 + |ρ.im - t₀|) ^ 2 := by
    intro ρ hρ hP
    push Not at hP
    obtain ⟨hi1, -, hr1, -⟩ := hzero_pts ρ hρ
    have hz1 : paperFT h (gammaOf ρ) = 0 :=
      paperFT_divided_eq_zero_of_zero hθ0 hθ hprod hρ hP.1 hP.2
    have b1 := hfb _ hi1 ε (by rw [hz1, norm_zero]; linarith)
    rw [hr1] at b1
    exact b1
  have hlarge : ∀ ρ ∈ zetaZeroConfig.carrier,
      ‖paperFT f (gammaOf ρ)‖ ≤ S / (1 + |ρ.im - t₀|) ^ 2 := by
    intro ρ hρ
    have hS0 : 0 ≤ S := by positivity
    by_cases h0 : ρ = ρ₀
    · have hz : ρ.im - t₀ = 0 := by rw [h0, ht₀def]; ring
      rw [hz, abs_zero, add_zero, one_pow, div_one, h0, ← hγ₀def, hfγ₀]
      have := norm_sub_le X₀ Y₀
      have : 0 ≤ ‖X₁‖ + ‖Y₁‖ + CN * ε * Bw := by positivity
      linarith
    by_cases h1 : ρ = ρ₁
    · rw [h1, hρ₁im, sub_self, abs_zero, add_zero, one_pow, div_one, hγ₁ρ, hfγ₁, norm_mul, hv,
        one_mul]
      have := norm_sub_le X₁ Y₁
      have : 0 ≤ ‖X₀‖ + ‖Y₀‖ + CN * ε * Bw := by positivity
      linarith
    · refine (hsmall ρ hρ (by tauto)).trans ?_
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 0 ≤ ‖X₀‖ + ‖Y₀‖ + ‖X₁‖ + ‖Y₁‖ := by positivity
      linarith
  have hposW := neg_le_re_W_of_evenHodge hA₀ hloc hH
    (contDiff_pairLandauTest hh.1 U hw t₀ c₁ c₂ s) (tsupport_pairLandauTest hw t₀ c₁ c₂ hs.le ha)
    hpolar.1 hpolar.2 hff ht₀ (by positivity) (by positivity) (fun ρ => ρ = ρ₀ ∨ ρ = ρ₁)
    (fun ρ _ hP => by
      rcases hP with h | h
      · rw [h]
      · rw [h, hρ₁im]) hlarge hsmall
  set c := CN * (1 / (1 + t₀)) * (24 * A₀ * Real.log (t₀ + 3) + 24 * A₀ * Real.log (t₀ + 3))
    with hc
  have hcross' : S * (CN * ε * Bw) * (1 / (1 + t₀)) *
      (24 * A₀ * Real.log (t₀ + 3) + 24 * A₀ * Real.log (t₀ + 3)) =
      (‖X₀‖ + ‖Y₀‖ + ‖X₁‖ + ‖Y₁‖ + CN * (ε * Bw)) * (ε * Bw) * c := by
    rw [hS, hc]; ring
  have hmain : 0 ≤ M * (-(‖X₀‖ * ‖X₁‖) + ‖X₀‖ * ‖Y₁‖ + ‖Y₀‖ * ‖X₁‖ + ‖Y₀‖ * ‖Y₁‖) +
      (ε * Bw) ^ 2 * R + (‖X₀‖ + ‖Y₀‖ + ‖X₁‖ + ‖Y₁‖ + CN * (ε * Bw)) * (ε * Bw) * c := by
    have h1 := mul_le_mul_of_nonneg_left hblock (by linarith : (0 : ℝ) ≤ M)
    have e : (CN * ε * Bw) ^ 2 * (24 * A₀ * Real.log (t₀ + 3)) = (ε * Bw) ^ 2 * R := by
      rw [hR]; ring
    rw [e] at hsplit
    have hre : ((X₀ - Y₀) * (starRingEnd ℂ) (v * (X₁ - Y₁))).re =
        (paperFT f γ₀ * (starRingEnd ℂ) (paperFT f γ₁)).re := by rw [hfγ₀, hfγ₁]
    linarith only [h1, hsplit, hre, hposW, hcross']
  have hx₀ : lam ≤ ‖X₀‖ := by rw [hX₀def, norm_mul]; exact hX₀
  have hx₁ : lam ≤ ‖X₁‖ := by rw [hX₁def, norm_mul]; exact hX₁
  have ht1 : 0 < 1 + t₀ := by linarith only [ht₀]
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact mul_nonneg (mul_nonneg (zero_le_one.trans hCN1) (one_div_nonneg.2 ht1.le))
      (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hA₀)) hlog0)
        (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hA₀)) hlog0))
  have he0 : 0 ≤ ε * Bw := mul_nonneg hε0 hBw0
  have harith := pair_node_arith_even hM2 hR0 he0 hc0 (zero_le_one.trans hCN1) hY₀ hY₁
    (norm_nonneg _) (norm_nonneg _) hx₀ hx₁ hlam hmain
  refine harith.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (even_pair_constant_le hCN1 hA₀ hlog0 ht₀.le) he0


end

end RHTower
