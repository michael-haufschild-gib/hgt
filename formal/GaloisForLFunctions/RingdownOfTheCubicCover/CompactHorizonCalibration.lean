import GaloisForLFunctions.CompactHyperbolicSurfaces.SelbergZeta
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.MayerResonanceCharacterization

/-!
# Compact Hyperbolic Quotient Calibration: Absence of Continuous Cusp Scattering

On any compact hyperbolic quotient `X = Γ\ℍ` (`CompactQuotient`) whose non-trivial elements are
hyperbolic (`|tr γ| > 2`), there is no cusp and no continuous Eisenstein scattering channel. This
module proves unconditionally the resulting calibration laws and contrasts them directly with the
cuspidal modular horizon `PSL₂(ℤ)\ℍ`:

1. **Zero non-real off-line zeros (`selbergZeta_zero_re_eq_half_or_im_eq_zero`)**:
   Every zero of `Z_Γ(s)` in `Re s > 0` satisfies either `Re s = 1/2` or `Im s = 0`. Equivalently,
   every non-real zero of `Z_Γ(s)` lies unconditionally on the critical line `Re s = 1/2`.
   By contrast, on the cuspidal modular horizon `PSL₂(ℤ)\ℍ`, every Mayer scattering resonance has
   `Im s ≠ 0` (`im_ne_zero_of_isMayerScatteringResonance`).

2. **Exact parametrization of real off-line zeros (`selbergZeta_offline_zero_iff_exceptional_eigenvalue`)**:
   Zeros of `Z_Γ(s)` in `1/2 < Re s < 1` correspond strictly to real exceptional discrete Laplace
   eigenvalues `0 < λ_j < 1/4` via `s = 1/2 + √(1/4 - λ_j)`.

3. **Finiteness of all off-line zeros (`finite_offline_selbergZeta_zeros`)**:
   The entire off-line zero set `{s : ℂ | 1/2 < Re s ∧ Z_Γ(s) = 0}` is finite.

4. **Spectral-gap equivalence (`selbergZeta_no_offline_zeros_iff_spectralGap_quarter`)**:
   The open strip `1/2 < Re s < 1` is zero-free for `Z_Γ` if and only if every positive discrete
   Laplace eigenvalue satisfies `λ_j ≥ 1/4`.

5. **Discrete spectral packet ringdown (`compact_spectral_packet_decay`)**:
   Every finite superposition of orthogonal compact modes above `λ_min > 0` decays unconditionally
   as `O(e^{-γ(λ_min) τ})` with `γ(λ_min) = 1/2` iff `λ_min ≥ 1/4`, with no continuous-spectrum
   tail or zeta-zero obstruction.
-/

noncomputable section

open Complex Finset Set Filter
open scoped BigOperators MatrixGroups Topology

namespace GaloisForLFunctions.RingdownOfTheCubicCover

open CompactHyperbolicSurfaces
open CompactHyperbolicSurfaces.CompactQuotient
open RenormalizedIntersectionTheory.MayerScattering

/-! ## Algebraic Dispersion Lemmas for `λ + s(s - 1) = 0` -/

/-- Any complex root of `l + s(s - 1) = 0` with `l ∈ ℝ` lies either on `Re s = 1/2` or on `ℝ`. -/
theorem lam_add_mul_sub_one_eq_zero_re_or_im {l : ℝ} {s : ℂ}
    (h : (l : ℂ) + s * (s - 1) = 0) :
    s.re = 1 / 2 ∨ s.im = 0 := by
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.sub_im, Complex.one_im,
    Complex.sub_re, Complex.one_re, zero_add, Complex.zero_im] at him
  have hprod : s.im * (2 * s.re - 1) = 0 := by linarith
  rcases mul_eq_zero.mp hprod with him0 | hre
  · exact Or.inr him0
  · exact Or.inl (by linarith)

/-- Any root of `l + s(s - 1) = 0` (`l ∈ ℝ`) in `Re s > 1/2` satisfies `l < 1/4` and
`s = 1/2 + √(1/4 - l)`. -/
theorem lam_add_mul_sub_one_eq_zero_of_half_lt_re {l : ℝ} {s : ℂ}
    (hsre : 1 / 2 < s.re) (h : (l : ℂ) + s * (s - 1) = 0) :
    l < 1 / 4 ∧ s = ((1 / 2 + Real.sqrt (1 / 4 - l) : ℝ) : ℂ) := by
  have him0 : s.im = 0 :=
    (lam_add_mul_sub_one_eq_zero_re_or_im h).resolve_left (by linarith)
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im, Complex.zero_re, him0, mul_zero, sub_zero] at hre
  have hl_eq : 1 / 4 - l = (s.re - 1 / 2) ^ 2 := by nlinarith
  have hl_lt : l < 1 / 4 := by
    have hpos : 0 < (s.re - 1 / 2) ^ 2 := sq_pos_of_pos (by linarith)
    linarith
  have hsqrt : Real.sqrt (1 / 4 - l) = s.re - 1 / 2 := by
    rw [hl_eq, Real.sqrt_sq (by linarith)]
  refine ⟨hl_lt, ?_⟩
  apply Complex.ext
  · simp only [Complex.ofReal_re]; linarith [hsqrt]
  · simp [him0]

/-- Exact characterization of roots of `l + s(s - 1) = 0` (`l ≥ 0`) inside `1/2 < Re s < 1`. -/
theorem lam_add_mul_sub_one_eq_zero_offline_iff {l : ℝ} {s : ℂ} :
    (1 / 2 < s.re ∧ s.re < 1 ∧ (l : ℂ) + s * (s - 1) = 0) ↔
      (0 < l ∧ l < 1 / 4 ∧ s = ((1 / 2 + Real.sqrt (1 / 4 - l) : ℝ) : ℂ)) := by
  constructor
  · rintro ⟨h12, h1, h⟩
    obtain ⟨hllt, hs_eq⟩ := lam_add_mul_sub_one_eq_zero_of_half_lt_re h12 h
    have him0 : s.im = 0 := by rw [hs_eq]; simp
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, Complex.zero_re, him0, mul_zero, sub_zero] at hre
    have hlpos : 0 < l := by nlinarith
    exact ⟨hlpos, hllt, hs_eq⟩
  · rintro ⟨hl0, hllt, rfl⟩
    set r : ℝ := Real.sqrt (1 / 4 - l)
    have hr_pos : 0 < r := Real.sqrt_pos.mpr (by linarith)
    have hr_sq : r ^ 2 = 1 / 4 - l := Real.sq_sqrt (by linarith)
    have hr_lt : r < 1 / 2 := by nlinarith
    refine ⟨by simp; linarith, by simp; linarith, ?_⟩
    have hreal : l + (1 / 2 + r) * (1 / 2 + r - 1) = 0 := by nlinarith
    exact_mod_cast hreal

/-! ## Selberg Zeta Calibration on Compact Hyperbolic Surfaces -/

section CompactSurface

variable (X : CompactQuotient) (hhyp : ∀ γ : X.Γ, γ ≠ 1 → 2 < |trSL γ|) {a : ℝ} (ha : 1 < a)

include hhyp in
/-- **Zero non-real off-line zeros on compact quotients**: every zero of `Z_Γ(s)` satisfies
`Re s = 1/2` or `Im s = 0`. -/
theorem selbergZeta_zero_re_eq_half_or_im_eq_zero {s : ℂ}
    (hs : X.selbergZeta ha s = 0) :
    s.re = 1 / 2 ∨ s.im = 0 := by
  obtain ⟨j, hj⟩ := (X.selbergZeta_eq_zero_iff hhyp ha s).mp hs
  exact lam_add_mul_sub_one_eq_zero_re_or_im hj

include hhyp in
/-- Every non-real zero of the compact-quotient Selberg zeta function lies on `Re s = 1/2`. -/
theorem selbergZeta_nonreal_zero_re_eq_half {s : ℂ}
    (hs : X.selbergZeta ha s = 0) (him : s.im ≠ 0) :
    s.re = 1 / 2 :=
  (selbergZeta_zero_re_eq_half_or_im_eq_zero X hhyp ha hs).resolve_right him

include hhyp in
/-- Off-line zeros of `Z_Γ(s)` in `1/2 < Re s < 1` correspond strictly to exceptional eigenvalues
`0 < λ_j < 1/4` via `s = 1/2 + √(1/4 - λ_j)`. -/
theorem selbergZeta_offline_zero_iff_exceptional_eigenvalue (s : ℂ) :
    (1 / 2 < s.re ∧ s.re < 1 ∧ X.selbergZeta ha s = 0) ↔
      ∃ j : X.SpecIndex ha,
        0 < X.spectralParam ha j ∧
        X.spectralParam ha j < 1 / 4 ∧
        s = ((1 / 2 + Real.sqrt (1 / 4 - X.spectralParam ha j) : ℝ) : ℂ) := by
  rw [X.selbergZeta_eq_zero_iff hhyp ha s]
  constructor
  · rintro ⟨h12, h1, j, hj⟩
    exact ⟨j, (lam_add_mul_sub_one_eq_zero_offline_iff.mp ⟨h12, h1, hj⟩)⟩
  · rintro ⟨j, hj0, hjlt, hs_eq⟩
    obtain ⟨h12, h1, hj⟩ := lam_add_mul_sub_one_eq_zero_offline_iff.mpr ⟨hj0, hjlt, hs_eq⟩
    exact ⟨h12, h1, j, hj⟩

include hhyp in
/-- The set of all off-line zeros `{s : ℂ | 1/2 < Re s ∧ Z_Γ(s) = 0}` on a compact hyperbolic
quotient is unconditionally finite. -/
theorem finite_offline_selbergZeta_zeros :
    {s : ℂ | 1 / 2 < s.re ∧ X.selbergZeta ha s = 0}.Finite := by
  refine ((X.finite_lam_lt ha (1 / 4)).image
    (fun j : X.SpecIndex ha =>
      ((1 / 2 + Real.sqrt (1 / 4 - X.spectralParam ha j) : ℝ) : ℂ))).subset ?_
  rintro s ⟨hsre, hz⟩
  obtain ⟨j, hj⟩ := (X.selbergZeta_eq_zero_iff hhyp ha s).mp hz
  obtain ⟨hjlt, hs_eq⟩ := lam_add_mul_sub_one_eq_zero_of_half_lt_re hsre hj
  exact ⟨j, hjlt, hs_eq.symm⟩

include hhyp in
/-- The strip `1/2 < Re s < 1` is zero-free for `Z_Γ(s)` if and only if every positive discrete
Laplace eigenvalue satisfies `λ_j ≥ 1/4`. -/
theorem selbergZeta_no_offline_zeros_iff_spectralGap_quarter :
    (∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → X.selbergZeta ha s ≠ 0) ↔
      ∀ j : X.SpecIndex ha, X.spectralParam ha j = 0 ∨ 1 / 4 ≤ X.spectralParam ha j := by
  constructor
  · intro hno j
    rcases eq_or_lt_of_le (X.spectralParam_nonneg ha j) with hj0 | hjpos
    · exact Or.inl hj0.symm
    · refine Or.inr (le_of_not_gt fun hjlt => ?_)
      set s : ℂ := ((1 / 2 + Real.sqrt (1 / 4 - X.spectralParam ha j) : ℝ) : ℂ)
      obtain ⟨h12, h1, hz⟩ :=
        (selbergZeta_offline_zero_iff_exceptional_eigenvalue X hhyp ha s).mpr
          ⟨j, hjpos, hjlt, rfl⟩
      exact hno s h12 h1 hz
  · intro hgap s h12 h1 hz
    obtain ⟨j, hjpos, hjlt, -⟩ :=
      (selbergZeta_offline_zero_iff_exceptional_eigenvalue X hhyp ha s).mp ⟨h12, h1, hz⟩
    rcases hgap j with hj0 | hjge <;> linarith

end CompactSurface

/-! ## Discrete Spectral Packet Ringdown Without a Cusp -/

/-- Wave-equation decay exponent `s(λ)` solving `s(1 - s) = λ` on the decaying branch (`Re s ≤ 1/2`
for `0 < λ < 1/4`, `Re s = 1/2` for `λ ≥ 1/4`). -/
def compactModeExponent (lam : ℝ) : ℂ :=
  if lam < 1 / 4 then
    ((1 / 2 - Real.sqrt (1 / 4 - lam) : ℝ) : ℂ)
  else
    (1 / 2 : ℂ) + I * (Real.sqrt (lam - 1 / 4) : ℂ)

/-- Real exponential decay rate `γ(λ) = Re(s(λ))` of a compact hyperbolic mode with eigenvalue `λ`. -/
def compactDecayRate (lam : ℝ) : ℝ :=
  if lam < 1 / 4 then 1 / 2 - Real.sqrt (1 / 4 - lam) else 1 / 2

/-- Dispersion identity `s(λ)(1 - s(λ)) = λ` for every `λ ∈ ℝ`. -/
theorem compactModeExponent_dispersion (lam : ℝ) :
    compactModeExponent lam * (1 - compactModeExponent lam) = (lam : ℂ) := by
  unfold compactModeExponent
  split_ifs with hlt
  · have hsq : Real.sqrt (1 / 4 - lam) ^ 2 = 1 / 4 - lam := Real.sq_sqrt (by linarith)
    have hreal : (1 / 2 - Real.sqrt (1 / 4 - lam)) *
        (1 - (1 / 2 - Real.sqrt (1 / 4 - lam))) = lam := by nlinarith
    exact_mod_cast hreal
  · have hge : 1 / 4 ≤ lam := not_lt.mp hlt
    have hsq : (Real.sqrt (lam - 1 / 4) : ℂ) ^ 2 = ((lam - 1 / 4 : ℝ) : ℂ) := by
      norm_cast
      exact Real.sq_sqrt (by linarith)
    calc ((1 / 2 : ℂ) + I * (Real.sqrt (lam - 1 / 4) : ℂ)) *
          (1 - ((1 / 2 : ℂ) + I * (Real.sqrt (lam - 1 / 4) : ℂ)))
        = 1 / 4 - I ^ 2 * (Real.sqrt (lam - 1 / 4) : ℂ) ^ 2 := by ring
      _ = (lam : ℂ) := by rw [Complex.I_sq, hsq]; push_cast; ring

theorem compactModeExponent_re (lam : ℝ) :
    (compactModeExponent lam).re = compactDecayRate lam := by
  unfold compactModeExponent compactDecayRate
  split_ifs <;> simp

theorem compactDecayRate_pos {lam : ℝ} (hlam : 0 < lam) :
    0 < compactDecayRate lam := by
  unfold compactDecayRate
  split_ifs with hlt
  · have hsq : Real.sqrt (1 / 4 - lam) ^ 2 = 1 / 4 - lam := Real.sq_sqrt (by linarith)
    have hnn : 0 ≤ Real.sqrt (1 / 4 - lam) := Real.sqrt_nonneg _
    nlinarith
  · norm_num

theorem compactDecayRate_eq_half_iff {lam : ℝ} :
    compactDecayRate lam = 1 / 2 ↔ 1 / 4 ≤ lam := by
  unfold compactDecayRate
  split_ifs with hlt
  · constructor
    · intro h
      have hpos : 0 < Real.sqrt (1 / 4 - lam) := Real.sqrt_pos.mpr (by linarith)
      linarith
    · intro hge; linarith
  · exact ⟨fun _ => not_lt.mp hlt, fun _ => rfl⟩

theorem compactDecayRate_mono {lam₁ lam₂ : ℝ} (hle : lam₁ ≤ lam₂) :
    compactDecayRate lam₁ ≤ compactDecayRate lam₂ := by
  unfold compactDecayRate
  split_ifs with hlt₁ hlt₂
  · have hs : Real.sqrt (1 / 4 - lam₂) ≤ Real.sqrt (1 / 4 - lam₁) :=
      Real.sqrt_le_sqrt (by linarith)
    linarith
  · have hnn : 0 ≤ Real.sqrt (1 / 4 - lam₁) := Real.sqrt_nonneg _
    linarith
  · linarith
  · exact le_rfl

/-- Quantitative ringdown of any finite spectral packet orthogonal to constants (`λ_i ≥ λ_min > 0`)
on a compact hyperbolic quotient. -/
theorem compact_spectral_packet_decay {ι : Type*} (S : Finset ι) (c : ι → ℂ) (lam : ι → ℝ)
    {lam_min : ℝ} (_hmin : 0 < lam_min) (hlam : ∀ i ∈ S, lam_min ≤ lam i)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖∑ i ∈ S, c i * cexp (-compactModeExponent (lam i) * (τ : ℂ))‖ ≤
      (∑ i ∈ S, ‖c i‖) * Real.exp (-compactDecayRate lam_min * τ) := by
  calc ‖∑ i ∈ S, c i * cexp (-compactModeExponent (lam i) * (τ : ℂ))‖
      ≤ ∑ i ∈ S, ‖c i * cexp (-compactModeExponent (lam i) * (τ : ℂ))‖ := norm_sum_le S _
    _ ≤ ∑ i ∈ S, ‖c i‖ * Real.exp (-compactDecayRate lam_min * τ) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_mul, Complex.norm_exp]
        have hre : (-compactModeExponent (lam i) * (τ : ℂ)).re =
            -compactDecayRate (lam i) * τ := by
          simp [compactModeExponent_re]
        rw [hre]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
        have hm := compactDecayRate_mono (hlam i hi)
        nlinarith
    _ = (∑ i ∈ S, ‖c i‖) * Real.exp (-compactDecayRate lam_min * τ) := by
        rw [Finset.sum_mul]

/-- **Compact vs Cuspidal Horizon Dichotomy**:
On any compact hyperbolic surface `X`, every non-real Selberg zero lies on `Re s = 1/2` and only
finitely many off-line zeros exist (all real). On the cuspidal modular horizon `PSL₂(ℤ)\ℍ`, every
Mayer scattering resonance in `0 < Re s < 1/2` is strictly non-real (`Im s ≠ 0`), generated purely
by the continuous Eisenstein scattering channel `ζ(2s) = 0`. -/
theorem compact_vs_cuspidal_horizon_dichotomy
    (X : CompactQuotient) (hhyp : ∀ γ : X.Γ, γ ≠ 1 → 2 < |trSL γ|) {a : ℝ} (ha : 1 < a) :
    ((∀ s : ℂ, X.selbergZeta ha s = 0 → s.im ≠ 0 → s.re = 1 / 2) ∧
      {s : ℂ | 1 / 2 < s.re ∧ X.selbergZeta ha s = 0}.Finite) ∧
    (∀ s : ℂ, IsMayerScatteringResonance s →
      s.im ≠ 0 ∧ riemannZeta (2 * s) = 0) := by
  refine ⟨⟨fun s hs him => selbergZeta_nonreal_zero_re_eq_half X hhyp ha hs him,
      finite_offline_selbergZeta_zeros X hhyp ha⟩,
    fun s hs => ⟨im_ne_zero_of_isMayerScatteringResonance hs,
      (isMayerScatteringResonance_iff_zeta_zero hs.1 hs.2.1).mp hs⟩⟩

end GaloisForLFunctions.RingdownOfTheCubicCover

end
