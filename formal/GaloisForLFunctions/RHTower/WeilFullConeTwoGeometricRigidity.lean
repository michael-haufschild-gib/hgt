import GaloisForLFunctions.RHTower.RiemannKernelFloquetBlockTests
import GaloisForLFunctions.RHTower.WeilFullConeThreeHalvesLacunaryRigidity

/-!
# Weil-cone rigidity on two geometric progressions with a common ratio

**Theorem** (`eq_vonMangoldt_of_weilPositiveFull_of_two_geometric`). Let `b ≥ 4`, `c ≥ 2`, and let
`log c / log b` have fractional part in `(1/6, 1/4)`. A full-cone Weil-positive weight system equal
to `Λ` off `{b^(q+1)} ∪ {c b^q}` equals `Λ`. The deviations on the two progressions are arbitrary up
to the universal box. Instance: `{4^(q+1)} ∪ {21·4^q}`, whose consecutive ratios alternate between
`21/16` and `64/21` (`eq_vonMangoldt_of_weilPositiveFull_of_four_twentyOne`).

**Mechanism.** In logarithmic coordinates the support lies on the lattice `ℓℤ` (`ℓ = log b`) and
its translate `α + ℓℤ` (`α = log c`). With `P = 1/ℓ`, the three Floquet blocks at offsets
`−2, 0, 1` have vertices `1, e^{2πiPα}, e^{−4πiPα}`, whose triangle contains `0` exactly when the
three sines `sin 2πPα`, `−sin 6πPα`, `sin 4πPα` are positive (`floquetVertex_crosses_pos`). This is
the fractional-part condition. For each point of the support the transform is prescribed exactly:
- a shifted point `c b^{q₀}` is isolated by the moment
  `x(t) = s e^{−2πit(α+q₀ℓ)} conj Ψ_α(t) / max(|Ψ_α(t)|², 1/4)` (`cosetMoment`), for which
  `xΨ_α = s e^{−2πit(α+q₀ℓ)}` on a period;
- a base point `b^{q₀}` is isolated by the mass `u(t) = 1 + 2s cos(2πtq₀ℓ)` (`latticeMass`).

The pairing then collapses to `2sP v(n₀)` for both signs of `s` (`floquet_pairing_single`), so
`v(n₀) = 0`. All three blocks fit inside the zero-free window `|ξ| ≤ 1633/1000` once `b ≥ 4`.

Unlike contraction arguments on lacunary sets, which need a minimal logarithmic gap, the
annihilation is exact: it uses only the lattice structure and the zero-free window.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate Convolution FourierTransform
open Zeta23

namespace RHTower

noncomputable section

/-! ## Two geometric progressions: the vertex triangle -/

theorem spectralChar_neg_left (a γ : ℝ) : spectralChar (-a) γ = spectralChar a (-γ) := by
  unfold spectralChar; congr 2; push_cast; ring

theorem planarCross_spectralChar (a b γ : ℝ) :
    planarCross (spectralChar a γ) (spectralChar b γ) = Real.sin (2 * π * (b - a) * γ) := by
  unfold planarCross
  rw [conj_spectralChar, ← spectralChar_neg_left, ← spectralChar_add_left]
  unfold spectralChar
  rw [Complex.exp_ofReal_mul_I_im]
  congr 1; ring

theorem floquetVertex_crosses_pos {P α : ℝ} {m : ℕ} (hlo : (m : ℝ) + 1 / 6 < P * α)
    (hhi : P * α < m + 1 / 4) :
    0 < planarCross (floquetVertex P α 0) (floquetVertex P α 1) ∧
      0 < planarCross (floquetVertex P α 1) (floquetVertex P α (-2)) ∧
        0 < planarCross (floquetVertex P α (-2)) (floquetVertex P α 0) := by
  unfold floquetVertex
  simp only [planarCross_spectralChar]
  push_cast
  set f := P * α - m with hf
  have hf1 : 1 / 6 < f := by rw [hf]; linarith
  have hf2 : f < 1 / 4 := by rw [hf]; linarith
  have hπ := Real.pi_pos
  refine ⟨?_, ?_, ?_⟩
  · have e : 2 * π * (1 * P - 0 * P) * α = 2 * π * f + (m : ℕ) * (2 * π) := by rw [hf]; ring
    rw [e, Real.sin_add_nat_mul_two_pi]
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  · have e : 2 * π * (-2 * P - 1 * P) * α = -(6 * π * f + ((3 * m : ℕ) : ℝ) * (2 * π)) := by
      rw [hf]; push_cast; ring
    rw [e, Real.sin_neg, Real.sin_add_nat_mul_two_pi]
    have e2 : 6 * π * f = (6 * π * f - π) + π := by ring
    rw [e2, Real.sin_add_pi]
    have : 0 < Real.sin (6 * π * f - π) :=
      Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)
    linarith
  · have e : 2 * π * (0 * P - -2 * P) * α = 4 * π * f + ((2 * m : ℕ) : ℝ) * (2 * π) := by
      rw [hf]; push_cast; ring
    rw [e, Real.sin_add_nat_mul_two_pi]
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)

theorem floquetVertex_one_re_pos {P α : ℝ} {m : ℕ} (hlo : (m : ℝ) + 1 / 6 < P * α)
    (hhi : P * α < m + 1 / 4) : 0 < (spectralChar P α).re := by
  unfold spectralChar
  rw [Complex.exp_ofReal_mul_I_re]
  set f := P * α - m with hf
  have e : 2 * π * P * α = 2 * π * f + (m : ℕ) * (2 * π) := by rw [hf]; ring
  rw [e, Real.cos_add_nat_mul_two_pi]
  have hπ := Real.pi_pos
  refine Real.cos_pos_of_mem_Ioo ⟨by nlinarith, by nlinarith⟩

/-! ## The target isolating a point of the shifted coset -/

theorem norm_div_max_normSq_le (z : ℂ) : ‖z‖ / max (Complex.normSq z) (1 / 4) ≤ 2 := by
  have hn : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
  have h0 := norm_nonneg z
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) (le_max_right _ _))]
  rcases le_total (1 / 4) (Complex.normSq z) with h | h
  · rw [max_eq_left h, hn]
    rw [hn] at h
    nlinarith
  · rw [max_eq_right h]
    rw [hn] at h
    nlinarith

/-- The moment `x(t) = s e(t, −(α + q₀ℓ)) conj Ψ(t) / max(|Ψ(t)|², 1/4)`, `Ψ` the fiber phase. -/
def cosetMoment (δ P α ℓ s : ℝ) (q₀ : ℤ) (t : ℝ) : ℂ :=
  (s : ℂ) * spectralChar t (-(α + q₀ * ℓ)) * conj (fiberPhase δ P α t) /
    ((max (Complex.normSq (fiberPhase δ P α t)) (1 / 4) : ℝ) : ℂ)

theorem continuous_cosetMoment (δ P α ℓ s : ℝ) (q₀ : ℤ) :
    Continuous (cosetMoment δ P α ℓ s q₀) := by
  have hΨ := (contDiff_fiberPhase δ P α).continuous
  unfold cosetMoment
  refine Continuous.div ((continuous_const.mul (continuous_spectralChar.comp
    (continuous_id.prodMk continuous_const))).mul (continuous_conj.comp hΨ))
    (Complex.continuous_ofReal.comp ((Complex.continuous_normSq.comp hΨ).max continuous_const))
    fun t => ?_
  refine Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le (by norm_num) (le_max_right _ _)).ne'

theorem norm_cosetMoment_le (δ P α ℓ s : ℝ) (q₀ : ℤ) (t : ℝ) :
    ‖cosetMoment δ P α ℓ s q₀ t‖ ≤ 2 * |s| := by
  unfold cosetMoment
  have hm : 0 < max (Complex.normSq (fiberPhase δ P α t)) (1 / 4) :=
    lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  rw [norm_div, norm_mul, norm_mul, Complex.norm_real, norm_spectralChar, Complex.norm_conj,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hm, mul_one, mul_div_assoc]
  have := norm_div_max_normSq_le (fiberPhase δ P α t)
  have hs := abs_nonneg s
  nlinarith

theorem cosetMoment_eq_on {δ P α ℓ s : ℝ} {q₀ : ℤ} {t : ℝ}
    (ht : 1 / 4 < Complex.normSq (fiberPhase δ P α t)) :
    cosetMoment δ P α ℓ s q₀ t = (s : ℂ) * spectralChar t (-(α + q₀ * ℓ)) *
      conj (fiberPhase δ P α t) / (Complex.normSq (fiberPhase δ P α t) : ℂ) := by
  unfold cosetMoment; rw [max_eq_left ht.le]

theorem contDiffAt_cosetMoment {δ P α ℓ s : ℝ} (q₀ : ℤ) (hδ : 0 < δ) (hP : 4 * δ ≤ P)
    (hre : 0 ≤ (spectralChar P α).re) {t : ℝ} (ht : t ∈ Ioo (-(2 * δ)) (P + 2 * δ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (cosetMoment δ P α ℓ s q₀) t := by
  have hΨ := contDiff_fiberPhase δ P α
  have hN : ContDiff ℝ (⊤ : ℕ∞) fun t => Complex.normSq (fiberPhase δ P α t) := by
    have : (fun t => Complex.normSq (fiberPhase δ P α t)) =
        fun t => (fiberPhase δ P α t).re * (fiberPhase δ P α t).re +
          (fiberPhase δ P α t).im * (fiberPhase δ P α t).im := by
      funext t; rw [Complex.normSq_apply]
    rw [this]
    have hr := Complex.reCLM.contDiff.comp hΨ
    have hi := Complex.imCLM.contDiff.comp hΨ
    exact (hr.mul hr).add (hi.mul hi)
  have hge : 1 / 2 ≤ Complex.normSq (fiberPhase δ P α t) :=
    normSq_fiberPhase_ge hδ hP hre ht.1.le ht.2.le
  have hev : ∀ᶠ s' in 𝓝 t, 1 / 4 < Complex.normSq (fiberPhase δ P α s') :=
    (hN.continuous.tendsto t).eventually (Ioi_mem_nhds (by linarith))
  refine ContDiffAt.congr_of_eventuallyEq ?_ (hev.mono fun s' hs' => cosetMoment_eq_on hs')
  have hnum : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => (s : ℂ) * spectralChar t (-(α + q₀ * ℓ)) *
      conj (fiberPhase δ P α t) :=
    (contDiff_const.mul (contDiff_spectralChar_left _)).mul (Complex.conjCLE.contDiff.comp hΨ)
  have hden : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => (Complex.normSq (fiberPhase δ P α t) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp hN
  have hm := hnum.contDiffAt (x := t) |>.mul
    (hden.contDiffAt.inv (Complex.ofReal_ne_zero.mpr (by linarith)))
  exact hm.congr_of_eventuallyEq (Eventually.of_forall fun _ => div_eq_mul_inv _ _)

theorem spectralChar_zero_left (z : ℝ) : spectralChar 0 z = 1 := by simp [spectralChar]

theorem spectralChar_mul_neg_left (a z : ℝ) : spectralChar a z * spectralChar (-a) z = 1 := by
  rw [← spectralChar_add_left, add_neg_cancel, spectralChar_zero_left]

theorem cosetMoment_add_period {δ P ℓ α s : ℝ} (q₀ : ℤ) (hδ : 0 < δ) (hP : 4 * δ ≤ P)
    (hPl : P * ℓ = 1) {t : ℝ} (h0 : -δ ≤ t) (h1 : t ≤ δ) :
    cosetMoment δ P α ℓ s q₀ (t + P) = cosetMoment δ P α ℓ s q₀ t := by
  unfold cosetMoment
  rw [fiberPhase_add_period hδ hP h0 h1, Complex.normSq_mul, map_mul, conj_spectralChar]
  have hn : Complex.normSq (spectralChar (-P) α) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_spectralChar]; norm_num
  rw [hn, one_mul, spectralChar_add_left]
  have hl : spectralChar P (-(α + q₀ * ℓ)) = spectralChar P (-α) := by
    rw [show -(α + q₀ * ℓ) = -α + ((-q₀ : ℤ) : ℝ) * ℓ by push_cast; ring, spectralChar_add]
    have := spectralChar_int_lattice hPl 1 (-q₀)
    rw [Int.cast_one, one_mul] at this
    rw [this, mul_one]
  rw [hl]
  have hm : spectralChar P (-α) * spectralChar (-P) (-α) = 1 := spectralChar_mul_neg_left P (-α)
  congr 1
  linear_combination (s : ℂ) * spectralChar t (-(α + q₀ * ℓ)) * conj (fiberPhase δ P α t) * hm

theorem cosetMoment_mul_fiberPhase {δ P ℓ α s : ℝ} (q₀ : ℤ) (hδ : 0 < δ) (hP : 4 * δ ≤ P)
    (hre : 0 ≤ (spectralChar P α).re) {ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ P) :
    cosetMoment δ P α ℓ s q₀ ξ * fiberPhase δ P α ξ = s * spectralChar ξ (-(α + q₀ * ℓ)) := by
  have hge : 1 / 2 ≤ Complex.normSq (fiberPhase δ P α ξ) :=
    normSq_fiberPhase_ge hδ hP hre (by linarith) (by linarith)
  rw [cosetMoment_eq_on (by linarith)]
  have hne : (Complex.normSq (fiberPhase δ P α ξ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by linarith)
  rw [Complex.normSq_eq_conj_mul_self] at hne ⊢
  rw [div_mul_eq_mul_div, mul_assoc ((s : ℂ) * spectralChar ξ (-(α + q₀ * ℓ))), mul_div_assoc,
    div_self hne, mul_one]

/-- For the coset target, the transform on the base lattice is `P` at `0` and vanishes elsewhere. -/
theorem floquetTransform_coset_base {δ P ℓ α s : ℝ} (q₀ : ℤ) (hδ : 0 < δ) (hP : 4 * δ ≤ P)
    (hPl : P * ℓ = 1) (hA : floquetArea P α ≠ 0)
    (hpos : ∀ i t, 0 < floquetWeight P α ((fun _ => (1 : ℝ)) t) (cosetMoment δ P α ℓ s q₀ t) i)
    (q : ℤ) :
    floquetTransform δ P α (fun _ => 1) (cosetMoment δ P α ℓ s q₀) (q * ℓ) =
      if q = 0 then (P : ℂ) else 0 := by
  rw [floquetTransform_lattice_zero hδ hP hPl hA continuous_const (continuous_cosetMoment _ _ _ _ _ _)
    (fun t ht => ⟨rfl, cosetMoment_add_period q₀ hδ hP hPl ht.1 ht.2⟩) hpos q]
  simp only [Complex.ofReal_one, one_mul]
  exact integral_spectralChar_period hPl q

/-- For the coset target, the transform on the shifted lattice isolates `α + q₀ℓ`. -/
theorem floquetTransform_coset_shift {δ P ℓ α s : ℝ} (q₀ : ℤ) (hδ : 0 < δ) (hP : 4 * δ ≤ P)
    (hPl : P * ℓ = 1) (hA : floquetArea P α ≠ 0) (hre : 0 ≤ (spectralChar P α).re)
    (hpos : ∀ i t, 0 < floquetWeight P α ((fun _ => (1 : ℝ)) t) (cosetMoment δ P α ℓ s q₀ t) i)
    (q : ℤ) :
    floquetTransform δ P α (fun _ => 1) (cosetMoment δ P α ℓ s q₀) (α + q * ℓ) =
      if q = q₀ then (s : ℂ) * P else 0 := by
  rw [floquetTransform_lattice_alpha hδ hP hPl hA continuous_const
    (continuous_cosetMoment _ _ _ _ _ _)
    (fun t ht => ⟨rfl, cosetMoment_add_period q₀ hδ hP hPl ht.1 ht.2⟩) hpos q]
  have hP0 : 0 ≤ P := by linarith
  have e : ∫ ξ in (0 : ℝ)..P, cosetMoment δ P α ℓ s q₀ ξ * spectralChar ξ (α + q * ℓ) *
      fiberPhase δ P α ξ = ∫ ξ in (0 : ℝ)..P, (s : ℂ) * spectralChar ξ (((q - q₀ : ℤ) : ℝ) * ℓ) := by
    refine intervalIntegral.integral_congr fun ξ hξ => ?_
    rw [Set.uIcc_of_le hP0] at hξ
    have h := cosetMoment_mul_fiberPhase (s := s) (ℓ := ℓ) q₀ hδ hP hre hξ.1 hξ.2
    have e2 : spectralChar ξ (-(α + q₀ * ℓ)) * spectralChar ξ (α + q * ℓ) =
        spectralChar ξ (((q - q₀ : ℤ) : ℝ) * ℓ) := by
      rw [← spectralChar_add]; congr 1; push_cast; ring
    rw [mul_right_comm, h, mul_assoc, e2]
  rw [e, intervalIntegral.integral_const_mul, integral_spectralChar_period hPl]
  by_cases hq : q = q₀
  · subst hq; simp
  · have : q - q₀ ≠ 0 := sub_ne_zero.mpr hq
    simp [this, hq]

/-! ## The target isolating a point of the base lattice -/

/-- The mass `u(t) = 1 + 2s cos(2π t q₀ ℓ)`. -/
def latticeMass (ℓ s : ℝ) (q₀ : ℤ) (t : ℝ) : ℝ := 1 + 2 * s * Real.cos (2 * π * t * (q₀ * ℓ))

theorem contDiff_latticeMass (ℓ s : ℝ) (q₀ : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (latticeMass ℓ s q₀) :=
  contDiff_const.add (contDiff_const.mul (Real.contDiff_cos.comp
    ((contDiff_const.mul contDiff_id).mul contDiff_const)))

theorem latticeMass_add_period {P ℓ s : ℝ} (hPl : P * ℓ = 1) (q₀ : ℤ) (t : ℝ) :
    latticeMass ℓ s q₀ (t + P) = latticeMass ℓ s q₀ t := by
  unfold latticeMass
  have e : 2 * π * (t + P) * (q₀ * ℓ) = 2 * π * t * (q₀ * ℓ) + q₀ * (2 * π) := by
    have : P * (q₀ * ℓ) = q₀ * (P * ℓ) := by ring
    rw [hPl] at this
    linear_combination 2 * π * this
  rw [e, Real.cos_add_int_mul_two_pi]

theorem ofReal_latticeMass (ℓ s : ℝ) (q₀ : ℤ) (ξ : ℝ) :
    (latticeMass ℓ s q₀ ξ : ℂ) = 1 + s * (spectralChar ξ (q₀ * ℓ) + spectralChar ξ (-(q₀ * ℓ))) := by
  unfold latticeMass spectralChar
  push_cast
  rw [Complex.cos, show (2 : ℂ) * π * ξ * -(q₀ * ℓ) * I = -((2 : ℂ) * π * ξ * (q₀ * ℓ)) * I by ring]
  ring

theorem floquetTransform_latticeMass_base {δ P ℓ α s : ℝ} (q₀ : ℤ) (hδ : 0 < δ) (hP : 4 * δ ≤ P)
    (hPl : P * ℓ = 1) (hA : floquetArea P α ≠ 0)
    (hpos : ∀ i t, 0 < floquetWeight P α (latticeMass ℓ s q₀ t) ((fun _ => (0 : ℂ)) t) i)
    (q : ℤ) :
    floquetTransform δ P α (latticeMass ℓ s q₀) (fun _ => 0) (q * ℓ) =
      (if q = 0 then (P : ℂ) else 0) +
        s * ((if q + q₀ = 0 then (P : ℂ) else 0) + (if q - q₀ = 0 then (P : ℂ) else 0)) := by
  rw [floquetTransform_lattice_zero hδ hP hPl hA (contDiff_latticeMass ℓ s q₀).continuous
    continuous_const (fun t _ => ⟨latticeMass_add_period hPl q₀ t, rfl⟩) hpos q]
  have e : ∀ ξ, (latticeMass ℓ s q₀ ξ : ℂ) * spectralChar ξ (q * ℓ) =
      spectralChar ξ (q * ℓ) + s * (spectralChar ξ (((q + q₀ : ℤ) : ℝ) * ℓ) +
        spectralChar ξ (((q - q₀ : ℤ) : ℝ) * ℓ)) := by
    intro ξ
    rw [ofReal_latticeMass]
    have e1 : spectralChar ξ (q₀ * ℓ) * spectralChar ξ (q * ℓ) =
        spectralChar ξ (((q + q₀ : ℤ) : ℝ) * ℓ) := by
      rw [← spectralChar_add]; congr 1; push_cast; ring
    have e2 : spectralChar ξ (-(q₀ * ℓ)) * spectralChar ξ (q * ℓ) =
        spectralChar ξ (((q - q₀ : ℤ) : ℝ) * ℓ) := by
      rw [← spectralChar_add]; congr 1; push_cast; ring
    linear_combination (s : ℂ) * (e1 + e2)
  simp_rw [e]
  have hc : ∀ z : ℝ, Continuous fun ξ : ℝ => spectralChar ξ z := fun z =>
    continuous_spectralChar.comp (continuous_id.prodMk continuous_const)
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add, integral_spectralChar_period hPl,
    integral_spectralChar_period hPl, integral_spectralChar_period hPl]
  · exact (hc _).intervalIntegrable _ _
  · exact (hc _).intervalIntegrable _ _
  · exact (hc _).intervalIntegrable _ _
  · exact (((hc _).add (hc _)).const_mul _).intervalIntegrable _ _

theorem floquetTransform_latticeMass_shift {δ P ℓ α s : ℝ} (q₀ : ℤ) (hδ : 0 < δ) (hP : 4 * δ ≤ P)
    (hPl : P * ℓ = 1) (hA : floquetArea P α ≠ 0)
    (hpos : ∀ i t, 0 < floquetWeight P α (latticeMass ℓ s q₀ t) ((fun _ => (0 : ℂ)) t) i)
    (q : ℤ) : floquetTransform δ P α (latticeMass ℓ s q₀) (fun _ => 0) (α + q * ℓ) = 0 := by
  rw [floquetTransform_lattice_alpha hδ hP hPl hA (contDiff_latticeMass ℓ s q₀).continuous
    continuous_const (fun t _ => ⟨latticeMass_add_period hPl q₀ t, rfl⟩) hpos q]
  simp

/-! ## Rigidity on two geometric progressions -/

/-- Summability over a union of two geometric progressions. -/
theorem summable_normDeficit_two_geometric {lam : ℕ → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ n : ℕ, |normDeficit lam n| ≤ B * (1 + |Real.log n|)) {b c : ℕ} (hb : 4 ≤ b)
    (hc : 2 ≤ c)
    (hv : ∀ n, normDeficit lam n ≠ 0 → (∃ q : ℕ, n = b ^ (q + 1)) ∨ (∃ q : ℕ, n = c * b ^ q)) :
    Summable fun n : ℕ => |normDeficit lam n| * ((1 + |Real.log n|) ^ 3)⁻¹ := by
  set g : ℕ → ℝ := fun n => B * ((1 + |Real.log n|) ^ 2)⁻¹ with hg
  set S₁ := Set.range fun q : ℕ => b ^ (q + 1)
  set S₂ := Set.range fun q : ℕ => c * b ^ q
  have hlog1 : (1 : ℝ) ≤ Real.log b := by
    have : Real.log 4 ≤ Real.log b := Real.log_le_log (by norm_num) (by exact_mod_cast hb)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have := Real.log_two_gt_d9
    linarith
  have hq2 : Summable fun q : ℕ => B * (1 / ((q + 1 : ℕ) : ℝ) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two)
    exact (this.mul_left B).congr fun q => by push_cast; ring
  have hgle : ∀ q : ℕ, ∀ y : ℝ, (q + 1 : ℝ) ≤ 1 + |y| → B * ((1 + |y|) ^ 2)⁻¹ ≤
      B * (1 / ((q + 1 : ℕ) : ℝ) ^ 2) := by
    intro q y hy
    refine mul_le_mul_of_nonneg_left ?_ hB0
    rw [one_div]
    push_cast
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hy 2)
  have hs1 : Summable (S₁.indicator g) := by
    have hinj : Function.Injective fun q : ℕ => b ^ (q + 1) :=
      (Nat.pow_right_injective (by omega)).comp (add_left_injective 1)
    rw [← hinj.summable_iff (fun n hn => Set.indicator_of_notMem hn _)]
    refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) hq2
    · simp only [Function.comp, Set.indicator_of_mem (Set.mem_range_self q), hg]; positivity
    · simp only [Function.comp, Set.indicator_of_mem (Set.mem_range_self q), hg]
      refine hgle q _ ?_
      rw [Nat.cast_pow, Real.log_pow, abs_of_nonneg (by positivity)]
      push_cast; nlinarith
  have hs2 : Summable (S₂.indicator g) := by
    have hinj : Function.Injective fun q : ℕ => c * b ^ q :=
      fun q q' h => Nat.pow_right_injective (by omega) (Nat.eq_of_mul_eq_mul_left (by omega) h)
    rw [← hinj.summable_iff (fun n hn => Set.indicator_of_notMem hn _)]
    refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) hq2
    · simp only [Function.comp, Set.indicator_of_mem (Set.mem_range_self q), hg]; positivity
    · simp only [Function.comp, Set.indicator_of_mem (Set.mem_range_self q), hg]
      refine hgle q _ ?_
      have hc0 : (0 : ℝ) ≤ Real.log c := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ c))
      push_cast
      rw [Real.log_mul (by exact_mod_cast (by omega : c ≠ 0)) (by positivity), Real.log_pow,
        abs_of_nonneg (by positivity)]
      nlinarith
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hs1.add hs2)
  have h1 : 0 ≤ S₁.indicator g n := Set.indicator_nonneg (fun _ _ => by positivity) n
  have h2 : 0 ≤ S₂.indicator g n := Set.indicator_nonneg (fun _ _ => by positivity) n
  by_cases hvn : normDeficit lam n = 0
  · rw [hvn, abs_zero, zero_mul]; positivity
  have hbound : |normDeficit lam n| * ((1 + |Real.log n|) ^ 3)⁻¹ ≤ g n := by
    have hl : 0 < 1 + |Real.log n| := by positivity
    rw [hg, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    calc |normDeficit lam n| ≤ B * (1 + |Real.log n|) := hB n
      _ = B * ((1 + |Real.log n|) ^ 2)⁻¹ * (1 + |Real.log n|) ^ 3 := by field_simp
  rcases hv n hvn with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · rw [Set.indicator_of_mem (Set.mem_range_self q)]; linarith
  · rw [Set.indicator_of_mem (Set.mem_range_self q) g]; linarith

/-- A real number that is `≥ 0` after multiplication by a positive `c` and by `−c` vanishes. -/
theorem eq_zero_of_signed_nonneg {v c : ℝ} (hc : 0 < c) (h1 : 0 ≤ c * v) (h2 : 0 ≤ -c * v) :
    v = 0 := by
  have h3 : c * v = 0 := le_antisymm (by linarith) h1
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd h hc.ne'
  · exact h

/-- The three-block pairing collapses to a single atom when the transform vanishes at every other
point of the support. -/
theorem floquet_pairing_single {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {A : ℝ}
    (hAbox : ∀ n, |normDeficit lam n| ≤ A * (1 + |Real.log n|)) {k : ℕ}
    (hZ : Summable fun n : ℕ => |normDeficit lam n| * ((1 + |Real.log n|) ^ k)⁻¹)
    {δ P α : ℝ} (hδ : 0 < δ) (hP : 0 < P) (hwin : 2 * P + δ < 1633 / 1000)
    {u : ℝ → ℝ} {x : ℝ → ℂ}
    (hsm : ∀ t ∈ Ioo (-(2 * δ)) (P + 2 * δ), ContDiffAt ℝ (⊤ : ℕ∞) u t ∧
      ContDiffAt ℝ (⊤ : ℕ∞) x t)
    (hpos : ∀ i t, 0 < floquetWeight P α (u t) (x t) i) {n₀ : ℕ} {s : ℝ}
    (h0 : floquetTransform δ P α u x (Real.log n₀) = (s : ℂ) * P)
    (hoff : ∀ n, n ≠ n₀ → normDeficit lam n ≠ 0 → floquetTransform δ P α u x (Real.log n) = 0) :
    0 ≤ 2 * s * P * normDeficit lam n₀ := by
  have h := floquet_pairing_nonneg hW hAbox hZ hδ hP hwin hsm hpos
  rw [tsum_eq_single n₀] at h
  · simp only [floquetTransform_neg, h0, map_mul, Complex.conj_ofReal] at h
    have e : ((normDeficit lam n₀ : ℝ) : ℂ) * ((s : ℂ) * P + (s : ℂ) * P) =
        ((2 * s * P * normDeficit lam n₀ : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.ofReal_re] at h
    exact h
  · intro n hn
    by_cases hvn : normDeficit lam n = 0
    · rw [hvn]; simp
    · rw [floquetTransform_neg, hoff n hn hvn]; simp

/-- The data of two geometric progressions `{b^(q+1)} ∪ {c b^q}` in logarithmic coordinates. -/
structure TwoGeometricData (b c : ℕ) (P ℓ α δ cm : ℝ) : Prop where
  hδ : 0 < δ
  h4 : 4 * δ ≤ P
  hP : 0 < P
  hPl : P * ℓ = 1
  hwin : 2 * P + δ < 1633 / 1000
  hArea : 0 < floquetArea P α
  hre : 0 ≤ (spectralChar P α).re
  hcm : 0 < cm
  hcall : ∀ j : Fin 3, cm ≤ ![planarCross (floquetVertex P α 0) (floquetVertex P α 1),
    planarCross (floquetVertex P α 1) (floquetVertex P α (-2)),
    planarCross (floquetVertex P α (-2)) (floquetVertex P α 0)] j
  hlogb : ∀ q : ℕ, Real.log ((b ^ (q + 1) : ℕ) : ℝ) = (((q + 1 : ℕ) : ℤ) : ℝ) * ℓ
  hlogc : ∀ q : ℕ, Real.log ((c * b ^ q : ℕ) : ℝ) = α + (((q : ℕ) : ℤ) : ℝ) * ℓ

/-- **The shifted coset points are rigid.** -/
theorem normDeficit_coset_eq_zero {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {B : ℝ}
    (hB : ∀ n : ℕ, |normDeficit lam n| ≤ B * (1 + |Real.log n|))
    (hZ : Summable fun n : ℕ => |normDeficit lam n| * ((1 + |Real.log n|) ^ 3)⁻¹)
    {b c : ℕ} {P ℓ α δ cm : ℝ} (hd : TwoGeometricData b c P ℓ α δ cm)
    (hv : ∀ n, normDeficit lam n ≠ 0 → (∃ q : ℕ, n = b ^ (q + 1)) ∨ (∃ q : ℕ, n = c * b ^ q))
    (q₀ : ℕ) : normDeficit lam (c * b ^ q₀) = 0 := by
  have hside : ∀ σ : ℝ, |σ| = 1 → 0 ≤ 2 * (σ * (cm / 8)) * P * normDeficit lam (c * b ^ q₀) := by
    intro σ hσ
    set s := σ * (cm / 8) with hs
    have hsabs : |s| = cm / 8 := by rw [hs, abs_mul, hσ, one_mul, abs_of_pos (by linarith [hd.hcm])]
    have hpos : ∀ i t, 0 < floquetWeight P α ((fun _ => (1 : ℝ)) t)
        (cosetMoment δ P α ℓ s (q₀ : ℤ) t) i := by
      intro i t
      have hge := floquetWeight_ge hd.hArea 1 (cosetMoment δ P α ℓ s (q₀ : ℤ) t) i hd.hcall
        (by norm_num)
      have hx := norm_cosetMoment_le δ P α ℓ s (q₀ : ℤ) t
      rw [hsabs] at hx
      refine lt_of_lt_of_le (div_pos ?_ hd.hArea) hge
      have := hd.hcm
      linarith
    have hsm : ∀ t ∈ Ioo (-(2 * δ)) (P + 2 * δ), ContDiffAt ℝ (⊤ : ℕ∞) (fun _ => (1 : ℝ)) t ∧
        ContDiffAt ℝ (⊤ : ℕ∞) (cosetMoment δ P α ℓ s (q₀ : ℤ)) t :=
      fun t ht => ⟨contDiffAt_const, contDiffAt_cosetMoment _ hd.hδ hd.h4 hd.hre ht⟩
    refine floquet_pairing_single hW hB hZ hd.hδ hd.hP hd.hwin hsm hpos ?_ ?_
    · rw [hd.hlogc, floquetTransform_coset_shift (q₀ : ℤ) hd.hδ hd.h4 hd.hPl hd.hArea.ne' hd.hre
        hpos]
      simp
    · intro n hn hvn
      rcases hv n hvn with ⟨q, rfl⟩ | ⟨q, rfl⟩
      · rw [hd.hlogb, floquetTransform_coset_base (q₀ : ℤ) hd.hδ hd.h4 hd.hPl hd.hArea.ne' hpos,
          if_neg (by omega)]
      · rw [hd.hlogc, floquetTransform_coset_shift (q₀ : ℤ) hd.hδ hd.h4 hd.hPl hd.hArea.ne' hd.hre
          hpos]
        have : (q : ℤ) ≠ q₀ := fun h => hn (by rw [Int.natCast_inj.mp h])
        rw [if_neg this]
  have h1 := hside 1 (by norm_num)
  have h2 := hside (-1) (by norm_num)
  have hc : 0 < cm / 4 * P := mul_pos (by linarith [hd.hcm]) hd.hP
  refine eq_zero_of_signed_nonneg hc ?_ ?_
  · have e : 2 * (1 * (cm / 8)) * P * normDeficit lam (c * b ^ q₀) =
        cm / 4 * P * normDeficit lam (c * b ^ q₀) := by ring
    linarith
  · have e : 2 * (-1 * (cm / 8)) * P * normDeficit lam (c * b ^ q₀) =
        -(cm / 4 * P) * normDeficit lam (c * b ^ q₀) := by ring
    linarith

theorem one_half_le_latticeMass {ℓ s : ℝ} (hs : |s| = 1 / 4) (q₀ : ℤ) (t : ℝ) :
    1 / 2 ≤ latticeMass ℓ s q₀ t := by
  unfold latticeMass
  have hcos := abs_le.mp (Real.abs_cos_le_one (2 * π * t * (q₀ * ℓ)))
  have hsl := abs_le.mp (le_of_eq hs)
  have : |2 * s * Real.cos (2 * π * t * (q₀ * ℓ))| ≤ 1 / 2 := by
    rw [abs_mul, abs_mul, hs, abs_two]
    have := Real.abs_cos_le_one (2 * π * t * (q₀ * ℓ))
    nlinarith
  linarith [neg_abs_le (2 * s * Real.cos (2 * π * t * (q₀ * ℓ)))]

/-- **The base lattice points are rigid.** -/
theorem normDeficit_base_eq_zero {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {B : ℝ}
    (hB : ∀ n : ℕ, |normDeficit lam n| ≤ B * (1 + |Real.log n|))
    (hZ : Summable fun n : ℕ => |normDeficit lam n| * ((1 + |Real.log n|) ^ 3)⁻¹)
    {b c : ℕ} {P ℓ α δ cm : ℝ} (hd : TwoGeometricData b c P ℓ α δ cm)
    (hv : ∀ n, normDeficit lam n ≠ 0 → (∃ q : ℕ, n = b ^ (q + 1)) ∨ (∃ q : ℕ, n = c * b ^ q))
    (q₀ : ℕ) : normDeficit lam (b ^ (q₀ + 1)) = 0 := by
  set q₁ : ℤ := ((q₀ + 1 : ℕ) : ℤ) with hq₁
  have hside : ∀ σ : ℝ, |σ| = 1 → 0 ≤ 2 * (σ / 4) * P * normDeficit lam (b ^ (q₀ + 1)) := by
    intro σ hσ
    set s := σ / 4 with hs
    have hsabs : |s| = 1 / 4 := by rw [hs, abs_div, hσ]; norm_num
    have hpos : ∀ i t, 0 < floquetWeight P α (latticeMass ℓ s q₁ t) ((fun _ => (0 : ℂ)) t) i := by
      intro i t
      have hu := one_half_le_latticeMass (ℓ := ℓ) hsabs q₁ t
      have hge := floquetWeight_ge hd.hArea (latticeMass ℓ s q₁ t) 0 i hd.hcall (by linarith)
      refine lt_of_lt_of_le ?_ hge
      rw [norm_zero, mul_zero, sub_zero]
      exact div_pos (mul_pos (by linarith) hd.hcm) hd.hArea
    have hsm : ∀ t ∈ Ioo (-(2 * δ)) (P + 2 * δ), ContDiffAt ℝ (⊤ : ℕ∞) (latticeMass ℓ s q₁) t ∧
        ContDiffAt ℝ (⊤ : ℕ∞) (fun _ => (0 : ℂ)) t :=
      fun t _ => ⟨(contDiff_latticeMass ℓ s q₁).contDiffAt, contDiffAt_const⟩
    refine floquet_pairing_single hW hB hZ hd.hδ hd.hP hd.hwin hsm hpos ?_ ?_
    · rw [hd.hlogb, floquetTransform_latticeMass_base q₁ hd.hδ hd.h4 hd.hPl hd.hArea.ne' hpos,
        if_neg (by omega), if_neg (by omega), if_pos (by rw [hq₁]; ring)]
      ring
    · intro n hn hvn
      rcases hv n hvn with ⟨q, rfl⟩ | ⟨q, rfl⟩
      · have h3 : ((q + 1 : ℕ) : ℤ) - q₁ ≠ 0 := by
          intro h
          apply hn
          have : q = q₀ := by omega
          rw [this]
        rw [hd.hlogb, floquetTransform_latticeMass_base q₁ hd.hδ hd.h4 hd.hPl hd.hArea.ne' hpos,
          if_neg (by omega), if_neg (by omega), if_neg h3]
        ring
      · rw [hd.hlogc, floquetTransform_latticeMass_shift q₁ hd.hδ hd.h4 hd.hPl hd.hArea.ne' hpos]
  have h1 := hside 1 (by norm_num)
  have h2 := hside (-1) (by norm_num)
  have hc : 0 < P / 2 := by linarith [hd.hP]
  refine eq_zero_of_signed_nonneg hc ?_ ?_
  · have e : 2 * (1 / 4) * P * normDeficit lam (b ^ (q₀ + 1)) =
        P / 2 * normDeficit lam (b ^ (q₀ + 1)) := by ring
    linarith
  · have e : 2 * (-1 / 4) * P * normDeficit lam (b ^ (q₀ + 1)) =
        -(P / 2) * normDeficit lam (b ^ (q₀ + 1)) := by ring
    linarith

/-- The lattice data for `b ≥ 4` and `log c / log b` with fractional part in `(1/6, 1/4)`. -/
theorem exists_twoGeometricData {b c m : ℕ} (hb : 4 ≤ b) (hc : 2 ≤ c)
    (hlo : ((m : ℝ) + 1 / 6) * Real.log b < Real.log c)
    (hhi : Real.log c < ((m : ℝ) + 1 / 4) * Real.log b) :
    ∃ cm : ℝ, TwoGeometricData b c (Real.log b)⁻¹ (Real.log b) (Real.log c)
      ((Real.log b)⁻¹ / 8) cm := by
  set ℓ := Real.log b with hℓdef
  have hlog4 : (1302 : ℝ) / 1000 < Real.log 4 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [this]; have := Real.log_two_gt_d9; linarith
  have hℓ : (1302 : ℝ) / 1000 < ℓ :=
    lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) (by exact_mod_cast hb))
  have hℓ0 : 0 < ℓ := by linarith
  set P := ℓ⁻¹ with hPdef
  have hP0 : 0 < P := inv_pos.mpr hℓ0
  have hPl : P * ℓ = 1 := inv_mul_cancel₀ hℓ0.ne'
  have hPlt : P < 1000 / 1302 := by
    rw [hPdef, inv_lt_comm₀ hℓ0 (by norm_num : (0 : ℝ) < 1000 / 1302)]; norm_num; linarith
  set α := Real.log c with hαdef
  have hr1 : (m : ℝ) + 1 / 6 < P * α := by
    rw [hPdef, inv_mul_eq_div, lt_div_iff₀ hℓ0]; linarith
  have hr2 : P * α < m + 1 / 4 := by
    rw [hPdef, inv_mul_eq_div, div_lt_iff₀ hℓ0]; linarith
  obtain ⟨hC1, hC2, hC3⟩ := floquetVertex_crosses_pos hr1 hr2
  refine ⟨min (planarCross (floquetVertex P α 0) (floquetVertex P α 1))
    (min (planarCross (floquetVertex P α 1) (floquetVertex P α (-2)))
      (planarCross (floquetVertex P α (-2)) (floquetVertex P α 0))), ?_⟩
  refine
    { hδ := by positivity
      h4 := by linarith
      hP := hP0
      hPl := hPl
      hwin := by linarith
      hArea := by unfold floquetArea; linarith
      hre := (floquetVertex_one_re_pos hr1 hr2).le
      hcm := lt_min hC1 (lt_min hC2 hC3)
      hcall := ?_
      hlogb := fun q => by push_cast; rw [Real.log_pow]; push_cast; ring
      hlogc := fun q => by
        push_cast
        rw [Real.log_mul (by exact_mod_cast (by omega : c ≠ 0)) (by positivity), Real.log_pow] }
  intro j
  fin_cases j
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

/-- **Weil-cone rigidity on two geometric progressions with a common ratio.** Let `b ≥ 4`, `c ≥ 2`,
and let `log c / log b` have fractional part in `(1/6, 1/4)`. A full-cone Weil-positive `lam` equal
to `Λ` off `{b^(q+1) : q ≥ 0} ∪ {c b^q : q ≥ 0}` equals `Λ`. The proof uses exact annihilating
radical tests built fiber by fiber over the lattice `(log b)ℤ` (Floquet decomposition) from three
blocks inside the zero-free window. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_two_geometric {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {b c m : ℕ} (hb : 4 ≤ b) (hc : 2 ≤ c)
    (hlo : ((m : ℝ) + 1 / 6) * Real.log b < Real.log c)
    (hhi : Real.log c < ((m : ℝ) + 1 / 4) * Real.log b)
    (hsupp : ∀ n, 2 ≤ n → (∀ q : ℕ, n ≠ b ^ (q + 1)) → (∀ q : ℕ, n ≠ c * b ^ q) →
      lam n = ArithmeticFunction.vonMangoldt n) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  obtain ⟨cm, hd⟩ := exists_twoGeometricData hb hc hlo hhi
  obtain ⟨B, hB0, hB⟩ := exists_abs_normDeficit_le_log hW
  have hv : ∀ n, normDeficit lam n ≠ 0 →
      (∃ q : ℕ, n = b ^ (q + 1)) ∨ (∃ q : ℕ, n = c * b ^ q) := by
    intro n hn
    by_contra hcon
    push Not at hcon
    apply hn
    simp only [normDeficit]
    split_ifs with h2
    · rw [hsupp n h2 (fun q hq => hcon.1 q hq) (fun q hq => hcon.2 q hq), sub_self, zero_div]
    · rfl
  have hZ := summable_normDeficit_two_geometric hB0 hB hb hc hv
  intro n hn
  have hvn : normDeficit lam n = 0 := by
    by_contra hne
    rcases hv n hne with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · exact hne (normDeficit_base_eq_zero hW hB hZ hd hv q)
    · exact hne (normDeficit_coset_eq_zero hW hB hZ hd hv q)
  simp only [normDeficit, if_pos hn] at hvn
  have hsq : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))).ne'
  rw [div_eq_zero_iff, sub_eq_zero] at hvn
  rcases hvn with hvn | hvn
  · exact hvn.symm
  · exact absurd hvn hsq

/-- **Instance: `{4^(q+1)} ∪ {21·4^q}`.** Consecutive ratios alternate between `21/16` and
`64/21`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_four_twentyOne {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam)
    (hsupp : ∀ n, 2 ≤ n → (∀ q : ℕ, n ≠ 4 ^ (q + 1)) → (∀ q : ℕ, n ≠ 21 * 4 ^ q) →
      lam n = ArithmeticFunction.vonMangoldt n) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  refine eq_vonMangoldt_of_weilPositiveFull_of_two_geometric hW (b := 4) (c := 21) (m := 2)
    le_rfl (by norm_num) ?_ ?_ hsupp
  · -- `4^13 < 21^6`
    have h : Real.log ((4 : ℝ) ^ 13) < Real.log ((21 : ℝ) ^ 6) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h ⊢
    linarith
  · -- `21^4 < 4^9`
    have h : Real.log ((21 : ℝ) ^ 4) < Real.log ((4 : ℝ) ^ 9) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h ⊢
    linarith

end

end RHTower
