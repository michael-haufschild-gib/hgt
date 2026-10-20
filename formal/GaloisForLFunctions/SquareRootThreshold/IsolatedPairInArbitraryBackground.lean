import GaloisForLFunctions.SquareRootThreshold.LatticeGroundEnergyStepLaw

/-!
# An isolated off-line pair in an arbitrary on-line background

The isolated-pair law places the visibility of one off-line pair in an on-line *lattice* at an
aperture of order `log(δL)/(2δ)`. With the two-bump lag-structure law the background can be
arbitrary.

**Setting.** `Z` is any tempered configuration whose zeros are all on the critical line, except one
simple reflected pair `½ ± δ + iγ₀`. Fix a `C²` bump `β` supported in `[−w, w]` and measure the
**local on-line mass** that it sees at height `γ₀`:

`M = Σ_{ρ on the line} m_ρ |h_β(γ_ρ − γ₀)|²`  (`onLineMass`).

**Visibility** (`isolatedPair_visible`). Let `Q = h_β(−iδ) · conj h_β(iδ)`. If

`|Q| · (sinh(δv) − 1) > M`,

then `Z` is visible at aperture `v/2 + w`, by a two-bump test modulated to height `γ₀`.

The mechanism: modulated to height `γ₀`, the pair contributes to the smeared lag structure
`e^{iγ₀v}(Q e^{δv} + Q̄ e^{−δv})`, which grows like `e^{δv}`, while every on-line zero contributes a
positive multiple of a unimodular phase, so the whole background is bounded by its mass at lag `0`
(`onLine_summand`). The general form for any bump `b` is `isolatedPair_lagStructure_gt`. The aperture of visibility is therefore
`≈ (1/2δ) log(M/|Q|)`: logarithmic in the local zero count, whatever the arrangement of the
on-line zeros. For a background of `ζ`-density this is `≍ (1/2δ) log log T`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- The point `½ + s + iγ₀`. -/
def heightPoint (s γ₀ : ℝ) : ℂ := ⟨1 / 2 + s, γ₀⟩

theorem gammaOf_heightPoint (s γ₀ : ℝ) : gammaOf (heightPoint s γ₀) = (γ₀ : ℂ) - I * s := by
  have hI : I * I = -1 := Complex.I_mul_I
  rw [gammaOf, div_eq_iff Complex.I_ne_zero, heightPoint, Complex.mk_eq_add_mul_I]
  push_cast
  linear_combination (s : ℂ) * hI

/-- The local on-line mass seen by the bump `β` at height `γ₀`. -/
def onLineMass (Z : ZeroConfig) (β : ℝ → ℂ) (γ₀ : ℝ) : ℝ :=
  ∑' ρ : Z.carrier, if (ρ : ℂ).re = 1 / 2 then
    (Z.mult ρ : ℝ) * ‖paperFT β (gammaOf ρ - γ₀)‖ ^ 2 else 0

/-- The bump modulated to height `γ₀`. -/
def modBump (β : ℝ → ℂ) (γ₀ : ℝ) : ℝ → ℂ := fun u => cexp (-(I * γ₀ * u)) * β u

theorem contDiff_modBump {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β) (γ₀ : ℝ) :
    ContDiff ℝ 2 (modBump β γ₀) := by
  have he : ContDiff ℝ 2 fun u : ℝ => cexp (-(I * γ₀ * u)) := by
    have : ContDiff ℝ 2 fun u : ℝ => -(I * (γ₀ : ℂ) * (u : ℂ)) :=
      (contDiff_const.mul Complex.ofRealCLM.contDiff).neg
    exact Complex.contDiff_exp.comp this
  exact he.mul hβ

theorem paperFT_weilTest_modBump {β : ℝ → ℂ} (hβ : Continuous β) (hβc : HasCompactSupport β)
    (γ₀ : ℝ) (z : ℂ) :
    paperFT (EF.weilTest (modBump β γ₀) (modBump β γ₀)) z =
      paperFT β (z - γ₀) * conj (paperFT β (conj z - γ₀)) := by
  have hc : Continuous (modBump β γ₀) := (by fun_prop : Continuous fun u : ℝ =>
    cexp (-(I * γ₀ * u))).mul hβ
  have hcs : HasCompactSupport (modBump β γ₀) := hβc.mul_left
  rw [EF.paperFT_weilTest hc hc hcs hcs]
  unfold modBump
  rw [paperFT_modulate, paperFT_modulate]

/-- For an on-line zero the ordinate is real. -/
theorem gammaOf_eq_ofReal_of_re {ρ : ℂ} (h : ρ.re = 1 / 2) : gammaOf ρ = ((ρ.im : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [re_gammaOf]; simp
  · rw [im_gammaOf, h]; simp

/-- An on-line summand of a lag structure is a positive multiple of a phase. -/
theorem onLine_summand {b : ℝ → ℂ} (hb : Continuous b) (hbc : HasCompactSupport b)
    (m : ℕ) (g v : ℝ) :
    let T : ℝ → ℂ := fun v => (m : ℂ) * paperFT (EF.weilTest b b) (g : ℂ) * cexp (I * (g : ℂ) * v)
    T v + conj (T (-v)) = 2 * T v ∧ ‖T v‖ = m * ‖paperFT b g‖ ^ 2 ∧
      T 0 = ((m * ‖paperFT b g‖ ^ 2 : ℝ) : ℂ) := by
  intro T
  have hH : paperFT (EF.weilTest b b) (g : ℂ) = ((‖paperFT b g‖ ^ 2 : ℝ) : ℂ) := by
    rw [EF.paperFT_weilTest hb hb hbc hbc, Complex.conj_ofReal, Complex.mul_conj']
    push_cast; ring
  simp only [T, hH]
  refine ⟨?_, ?_, ?_⟩
  · rw [map_mul, map_mul, map_natCast, Complex.conj_ofReal, ← Complex.exp_conj]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring_nf
  · rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _),
      show I * (g : ℂ) * (v : ℂ) = ((g * v : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  · simp

/-- The pair's lag contribution: `S_p(v) + conj S_p(−v) = 2e^{iγ₀v}(Q e^{δv} + Q̄ e^{−δv})`. -/
theorem pair_lag_identity (Q : ℂ) (γ₀ δ v : ℝ) :
    (Q * cexp (I * ((γ₀ : ℂ) - I * δ) * v) + conj Q * cexp (I * ((γ₀ : ℂ) - I * (-δ : ℝ)) * v)) +
      conj (Q * cexp (I * ((γ₀ : ℂ) - I * δ) * ((-v : ℝ) : ℂ)) +
        conj Q * cexp (I * ((γ₀ : ℂ) - I * (-δ : ℝ)) * ((-v : ℝ) : ℂ))) =
      2 * cexp (I * γ₀ * v) *
        (Q * (Real.exp (δ * v) : ℂ) + conj Q * (Real.exp (-(δ * v)) : ℂ)) := by
  have hI : I * I = -1 := Complex.I_mul_I
  have e1 : cexp (I * ((γ₀ : ℂ) - I * δ) * v) = cexp (I * γ₀ * v) * (Real.exp (δ * v) : ℂ) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast
    linear_combination (-(δ : ℂ) * v) * hI
  have e2 : cexp (I * ((γ₀ : ℂ) - I * (-δ : ℝ)) * v) =
      cexp (I * γ₀ * v) * (Real.exp (-(δ * v)) : ℂ) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast
    linear_combination ((δ : ℂ) * v) * hI
  have e3 : conj (cexp (I * ((γ₀ : ℂ) - I * δ) * ((-v : ℝ) : ℂ))) =
      cexp (I * γ₀ * v) * (Real.exp (-(δ * v)) : ℂ) := by
    rw [← Complex.exp_conj, Complex.ofReal_exp, ← Complex.exp_add]; congr 1
    simp only [map_mul, map_sub, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    linear_combination ((δ : ℂ) * v) * hI
  have e4 : conj (cexp (I * ((γ₀ : ℂ) - I * (-δ : ℝ)) * ((-v : ℝ) : ℂ))) =
      cexp (I * γ₀ * v) * (Real.exp (δ * v) : ℂ) := by
    rw [← Complex.exp_conj, Complex.ofReal_exp, ← Complex.exp_add]; congr 1
    simp only [map_mul, map_sub, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    linear_combination (-(δ : ℂ) * v) * hI
  rw [map_add, map_mul, map_mul, e3, e4, e1, e2, Complex.conj_conj]
  ring

/-- The pair weight `Q_b = h_b(γ₀ − iδ) · conj h_b(γ₀ + iδ)`. -/
def pairWeight (b : ℝ → ℂ) (δ γ₀ : ℝ) : ℂ :=
  paperFT b ((γ₀ : ℂ) - I * δ) * conj (paperFT b ((γ₀ : ℂ) + I * δ))

/-- The two pair summands of a lag structure. -/
theorem pair_summand {b : ℝ → ℂ} (hb : Continuous b) (hbc : HasCompactSupport b)
    (γ₀ δ : ℝ) (v : ℝ) :
    paperFT (EF.weilTest b b) (gammaOf (heightPoint δ γ₀)) *
        cexp (I * gammaOf (heightPoint δ γ₀) * v) =
      pairWeight b δ γ₀ * cexp (I * ((γ₀ : ℂ) - I * δ) * v) ∧
    paperFT (EF.weilTest b b) (gammaOf (heightPoint (-δ) γ₀)) *
        cexp (I * gammaOf (heightPoint (-δ) γ₀) * v) =
      conj (pairWeight b δ γ₀) * cexp (I * ((γ₀ : ℂ) - I * (-δ : ℝ)) * v) := by
  rw [gammaOf_heightPoint, gammaOf_heightPoint, EF.paperFT_weilTest hb hb hbc hbc,
    EF.paperFT_weilTest hb hb hbc hbc, pairWeight]
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_conj]
  constructor
  · congr 3; ring_nf
  · rw [mul_comm (paperFT b _) (conj _)]
    congr 2
    · congr 2; push_cast; ring
    · congr 1; push_cast; ring

/-- The on-line mass seen by a bump `b`: `Σ_{on-line} m_ρ |h_b(γ_ρ)|²`. -/
def onLineMassOf (Z : ZeroConfig) (b : ℝ → ℂ) : ℝ :=
  ∑' ρ : Z.carrier, if (ρ : ℂ).re = 1 / 2 then (Z.mult ρ : ℝ) * ‖paperFT b (gammaOf ρ)‖ ^ 2 else 0

/-- **The lag structure of an isolated pair.** If all zeros of a tempered configuration are on the
critical line except one simple pair `½ ± δ + iγ₀`, then for every bump `b` and every `v ≥ 0` with
`|Q_b| (sinh(δv) − 1) > M_b` the two-point minor fails: `2 Re S_b(0) < |S_b(v) + conj S_b(−v)|`. -/
theorem isolatedPair_lagStructure_gt (Z : ZeroConfig) (hZ : TemperedConfig Z) {δ γ₀ : ℝ}
    (hδ : 0 < δ)
    (hp : heightPoint δ γ₀ ∈ Z.carrier) (hm : heightPoint (-δ) γ₀ ∈ Z.carrier)
    (hmp : Z.mult (heightPoint δ γ₀) = 1) (hmm : Z.mult (heightPoint (-δ) γ₀) = 1)
    (hon : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 ∨ ρ = heightPoint δ γ₀ ∨ ρ = heightPoint (-δ) γ₀)
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {v : ℝ}
    (hvis : onLineMassOf Z b < ‖pairWeight b δ γ₀‖ * (Real.sinh (δ * v) - 1)) :
    2 * (lagStructure Z b 0).re < ‖lagStructure Z b v + conj (lagStructure Z b (-v))‖ := by
  classical
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  set F : ℝ → Z.carrier → ℂ := fun v ρ => (Z.mult ρ : ℂ) *
    paperFT (EF.weilTest (b) (b)) (gammaOf ρ) * cexp (I * gammaOf ρ * v)
    with hF
  have hFs : ∀ v, Summable (F v) := fun v => summable_lagStructure Z hZ hb hbs v
  set pp : Z.carrier := ⟨heightPoint δ γ₀, hp⟩ with hpp
  set pm : Z.carrier := ⟨heightPoint (-δ) γ₀, hm⟩ with hpm
  have hre_pp : (pp : ℂ).re ≠ 1 / 2 := by simp [hpp, heightPoint]; linarith
  have hre_pm : (pm : ℂ).re ≠ 1 / 2 := by simp [hpm, heightPoint]; linarith
  have hne : pm ≠ pp := fun h => by
    have := congrArg (fun x : Z.carrier => (x : ℂ).re) h
    simp [hpp, hpm, heightPoint] at this
    linarith
  -- the on-line remainder
  set R : ℝ → Z.carrier → ℂ := fun v ρ => if (ρ : ℂ).re = 1 / 2 then F v ρ else 0 with hR
  have hRs : ∀ v, Summable (R v) := fun v => Summable.of_norm_bounded (hFs v).norm fun ρ => by
    simp only [hR]; split_ifs <;> simp
  have hpt : ∀ v ρ, F v ρ = (if ρ = pp then F v pp else 0) + (if ρ = pm then F v pm else 0) +
      R v ρ := by
    intro v ρ
    rcases hon ρ.1 ρ.2 with h | h | h
    · have h1 : ρ ≠ pp := fun e => hre_pp (e ▸ h)
      have h2 : ρ ≠ pm := fun e => hre_pm (e ▸ h)
      simp [hR, h, h1, h2]
    · have h1 : ρ = pp := Subtype.ext h
      subst h1
      rw [if_pos rfl, if_neg hne.symm, show R v pp = 0 from if_neg hre_pp, add_zero, add_zero]
    · have h2 : ρ = pm := Subtype.ext h
      subst h2
      rw [if_neg hne, if_pos rfl, show R v pm = 0 from if_neg hre_pm, zero_add, add_zero]
  have hsplit : ∀ v, lagStructure Z (b) v = F v pp + F v pm + ∑' ρ, R v ρ := by
    intro v
    rw [lagStructure, show (∑' ρ : Z.carrier, (Z.mult ρ : ℂ) *
      paperFT (EF.weilTest (b) (b)) (gammaOf ρ) *
        cexp (I * gammaOf ρ * v)) = ∑' ρ, F v ρ from rfl, tsum_congr (hpt v)]
    have hs1 : Summable fun ρ : Z.carrier => if ρ = pp then F v pp else 0 :=
      summable_of_ne_finset_zero (s := {pp}) fun ρ hρ => by
        rw [Finset.mem_singleton] at hρ; simp [hρ]
    have hs2 : Summable fun ρ : Z.carrier => if ρ = pm then F v pm else 0 :=
      summable_of_ne_finset_zero (s := {pm}) fun ρ hρ => by
        rw [Finset.mem_singleton] at hρ; simp [hρ]
    rw [Summable.tsum_add (hs1.add hs2) (hRs v), Summable.tsum_add hs1 hs2, tsum_ite_eq,
      tsum_ite_eq]
  -- on-line terms
  set R₀ : Z.carrier → ℝ := fun ρ => if (ρ : ℂ).re = 1 / 2 then
    (Z.mult ρ : ℝ) * ‖paperFT b (gammaOf ρ)‖ ^ 2 else 0 with hR₀
  have hon_term : ∀ v ρ, R v ρ + conj (R (-v) ρ) = 2 * R v ρ ∧ ‖R v ρ‖ = R₀ ρ ∧
      R 0 ρ = (R₀ ρ : ℂ) := by
    intro v ρ
    by_cases h : (ρ : ℂ).re = 1 / 2
    · have hg := gammaOf_eq_ofReal_of_re h
      obtain ⟨h1, h2, h3⟩ := onLine_summand hb.continuous hbc (Z.mult ρ) (ρ : ℂ).im v
      simp only [hR, hR₀, if_pos h, hF, hg]
      exact ⟨h1, h2, h3⟩
    · simp only [hR, hR₀, if_neg h]
      simp
  have hR₀s : Summable R₀ := by
    refine Summable.of_norm_bounded (hRs 0).norm fun ρ => ?_
    rw [← (hon_term 0 ρ).2.1, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hM : onLineMassOf Z b = ∑' ρ, R₀ ρ := rfl
  have hconj : Summable fun ρ => conj (R (-v) ρ) :=
    ((hRs (-v)).map (starRingEnd ℂ).toAddMonoidHom Complex.continuous_conj)
  have hX_on : ‖(∑' ρ, R v ρ) + conj (∑' ρ, R (-v) ρ)‖ ≤ 2 * onLineMassOf Z b := by
    rw [Complex.conj_tsum, ← Summable.tsum_add (hRs v) hconj,
      tsum_congr fun ρ => (hon_term v ρ).1]
    have hn : Summable fun ρ => ‖2 * R v ρ‖ := ((hRs v).mul_left 2).norm
    refine (norm_tsum_le_tsum_norm hn).trans ?_
    rw [hM, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun ρ => ?_) hn (hR₀s.mul_left 2)
    rw [norm_mul, Complex.norm_ofNat, (hon_term v ρ).2.1]
  have hS0_on : (∑' ρ, R 0 ρ).re = onLineMassOf Z b := by
    rw [Complex.re_tsum (hRs 0), hM]
    exact tsum_congr fun ρ => by rw [(hon_term 0 ρ).2.2, Complex.ofReal_re]
  -- the pair
  set Q : ℂ := pairWeight b δ γ₀ with hQ
  have hFpp : ∀ v, F v pp = Q * cexp (I * ((γ₀ : ℂ) - I * δ) * v) := by
    intro v
    simp only [hF, hpp, hmp, Nat.cast_one, one_mul]
    exact (pair_summand hb.continuous hbc γ₀ δ v).1
  have hFpm : ∀ v, F v pm = conj Q * cexp (I * ((γ₀ : ℂ) - I * (-δ : ℝ)) * v) := by
    intro v
    simp only [hF, hpm, hmm, Nat.cast_one, one_mul]
    exact (pair_summand hb.continuous hbc γ₀ δ v).2
  have hX : lagStructure Z (b) v + conj (lagStructure Z (b) (-v)) =
      2 * cexp (I * γ₀ * v) * (Q * (Real.exp (δ * v) : ℂ) + conj Q * (Real.exp (-(δ * v)) : ℂ)) +
        ((∑' ρ, R v ρ) + conj (∑' ρ, R (-v) ρ)) := by
    rw [hsplit, hsplit, hFpp, hFpp, hFpm, hFpm, ← pair_lag_identity Q γ₀ δ v]
    simp only [map_add]
    push_cast
    ring
  have hS0 : (lagStructure Z (b) 0).re = 2 * Q.re + onLineMassOf Z b := by
    rw [hsplit, hFpp, hFpm, Complex.add_re, Complex.add_re, hS0_on]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, Complex.conj_re]
    ring
  clear_value Q
  have hE : ‖cexp (I * γ₀ * v)‖ = 1 := by
    rw [show I * (γ₀ : ℂ) * (v : ℂ) = ((γ₀ * v : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hnorm : ∀ Y : ℂ, ‖2 * cexp (I * γ₀ * v) * Y‖ = 2 * ‖Y‖ := fun Y => by
    rw [norm_mul, norm_mul, Complex.norm_two, hE, mul_one]
  have hpair : 4 * ‖Q‖ * Real.sinh (δ * v) ≤ ‖2 * cexp (I * γ₀ * v) *
      (Q * (Real.exp (δ * v) : ℂ) + conj Q * (Real.exp (-(δ * v)) : ℂ))‖ := by
    rw [hnorm]
    have h1 := norm_sub_norm_le (Q * (Real.exp (δ * v) : ℂ))
      (-(conj Q * (Real.exp (-(δ * v)) : ℂ)))
    rw [norm_neg, sub_neg_eq_add, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.exp_pos _)] at h1
    rw [Real.sinh_eq]
    linarith
  rw [hX, hS0]
  have hre : Q.re ≤ ‖Q‖ := Complex.re_le_norm Q
  have hsplitn := norm_sub_norm_le (2 * cexp (I * γ₀ * v) *
      (Q * (Real.exp (δ * v) : ℂ) + conj Q * (Real.exp (-(δ * v)) : ℂ)))
    (-((∑' ρ, R v ρ) + conj (∑' ρ, R (-v) ρ)))
  rw [norm_neg, sub_neg_eq_add] at hsplitn
  nlinarith

/-- **Isolated pair in an arbitrary on-line background.** If all zeros of a tempered configuration
are on the critical line except one simple pair `½ ± δ + iγ₀`, and
`|h_β(−iδ)| |h_β(iδ)| (sinh(δv) − 1) > M`, `M` the local on-line mass at height `γ₀`, then the
configuration is visible at aperture `v/2 + w`. -/
theorem isolatedPair_visible (Z : ZeroConfig) (hZ : TemperedConfig Z) {δ γ₀ : ℝ} (hδ : 0 < δ)
    (hp : heightPoint δ γ₀ ∈ Z.carrier) (hm : heightPoint (-δ) γ₀ ∈ Z.carrier)
    (hmp : Z.mult (heightPoint δ γ₀) = 1) (hmm : Z.mult (heightPoint (-δ) γ₀) = 1)
    (hon : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 ∨ ρ = heightPoint δ γ₀ ∨ ρ = heightPoint (-δ) γ₀)
    {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β) {w : ℝ} (hβs : ∀ u, β u ≠ 0 → |u| ≤ w) {v : ℝ}
    (hv : 0 ≤ v)
    (hvis : onLineMass Z β γ₀ <
      ‖paperFT β (-(I * δ))‖ * ‖paperFT β (I * δ)‖ * (Real.sinh (δ * v) - 1)) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-(v / 2 + w)) (v / 2 + w) ∧
      (Z.W f f).re < 0 := by
  have hβc : HasCompactSupport β := hasCompactSupport_of_support_subset_abs hβs
  have hb := contDiff_modBump hβ γ₀
  have hbs : ∀ u, modBump β γ₀ u ≠ 0 → |u| ≤ w := fun u hu => hβs u (right_ne_zero_of_mul hu)
  have hmod : ∀ z : ℂ, paperFT (modBump β γ₀) z = paperFT β (z - γ₀) := fun z => by
    unfold modBump; exact paperFT_modulate β γ₀ z
  have hM : onLineMassOf Z (modBump β γ₀) = onLineMass Z β γ₀ := by
    unfold onLineMassOf onLineMass
    exact tsum_congr fun ρ => by rw [hmod]
  have hQ : ‖pairWeight (modBump β γ₀) δ γ₀‖ = ‖paperFT β (-(I * δ))‖ * ‖paperFT β (I * δ)‖ := by
    rw [pairWeight, hmod, hmod, norm_mul, Complex.norm_conj]
    congr 2 <;> ring_nf
  refine exists_visible_of_lagStructure Z hZ hb hbs hv ?_
  exact isolatedPair_lagStructure_gt Z hZ hδ hp hm hmp hmm hon hb hbs (by rw [hM, hQ]; exact hvis)

end GaloisForLFunctions.SquareRootThreshold
