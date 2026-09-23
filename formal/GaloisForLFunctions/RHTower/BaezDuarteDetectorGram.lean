import GaloisForLFunctions.RHTower.BaezDuarteTargetPairing
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardHardyNonexpansive

/-!
# The detector Gram is the Cauchy kernel of the centered zeros

`BaezDuarteL2Carrier` attaches to each point `s` with `Re s < ½` a detector vector in the carrier whose
inner product with `F` is the Mellin integral `∫₁^∞ F(u)u^{s-1}du`.  Two detectors pair explicitly:

`⟪bdDetector s₁, bdDetector s₂⟫ = ∫₁^∞ u^{s₁ + conj s₂ - 2} du = 1/(1 - s₁ - conj s₂)`,

so at `s_i = 1 - ρ_i` — the detectors that see a zeta zero — the Gram matrix of the detectors is

`⟪·,·⟫ = 1/(ρ_i + conj ρ_j - 1) = 1/((ρ_i - ½) + conj (ρ_j - ½))`,

which is **exactly** `RHTower.rightHalfPlaneHardyCauchyGram` evaluated at the centered zeros
`w_i = ρ_i - ½`.  The corpus already studies that matrix (hermitian, positive semidefinite, nonexpansive);
this file identifies it as the object controlling the Nyman--Beurling floor.

With that, the one-zero floor of `BaezDuarteL2Carrier` becomes a many-zero floor.  If `e` is any
orthonormal family inside the span of finitely many detectors at zeros, then Bessel's inequality gives

`∑_i ‖⟪e_i, bdTarget⟫‖² ≤ ‖bdTarget − G‖²`

for every `G` in the closed span of the Báez-Duarte generators, because every detector — and hence every
combination of detectors — annihilates that span.  The right-hand side is the squared Báez-Duarte
distance and the left-hand side is the squared norm of the projection of the target onto the detector
span, i.e. `v* G⁻¹ v` with `v_i = 1/ρ_i` and `G` the Cauchy matrix above.  That is the Hilbert-space
skeleton of the Burnol-type lower bound `liminf d_N² log N ≥ ∑_ρ m_ρ²/|ρ|²`: the arithmetic input is only
the location of the zeros, and everything else is the geometry of the Cauchy kernel.
-/

open MeasureTheory Set Complex
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- Conjugation passes through a real positive base in a complex power. -/
theorem conj_ofReal_cpow_baezDuarteDetectorGram {u : ℝ} (hu : 0 < u) (z : ℂ) :
    (starRingEnd ℂ) ((u : ℂ) ^ z) = (u : ℂ) ^ ((starRingEnd ℂ) z) := by
  have harg : ((u : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hu.le]
    exact ne_of_lt Real.pi_pos
  have h := Complex.conj_cpow (u : ℂ) ((starRingEnd ℂ) z) harg
  rw [Complex.conj_ofReal, RingHomInvPair.comp_apply_eq] at h
  exact h.symm

/-- **The detector Gram entry.**  Two Mellin detectors pair as a Cauchy kernel. -/
theorem inner_bdDetector_bdDetector {s₁ s₂ : ℂ} (hs₁ : s₁.re < 1 / 2) (hs₂ : s₂.re < 1 / 2) :
    inner ℂ (bdDetector hs₁) (bdDetector hs₂)
      = 1 / (1 - s₁ - (starRingEnd ℂ) s₂) := by
  have hre : (s₁ + (starRingEnd ℂ) s₂ - 2).re < -1 := by
    rw [Complex.sub_re, Complex.add_re, Complex.conj_re]
    norm_num
    linarith
  rw [MeasureTheory.L2.inner_def]
  have hcongr : ∀ᵐ u ∂bdMeasure,
      inner ℂ ((bdDetector hs₁ : ℝ → ℂ) u) ((bdDetector hs₂ : ℝ → ℂ) u)
        = (u : ℂ) ^ (s₁ + (starRingEnd ℂ) s₂ - 2) := by
    filter_upwards [(memLp_bdDetectorFun hs₁).coeFn_toLp, (memLp_bdDetectorFun hs₂).coeFn_toLp,
      ae_restrict_mem measurableSet_Ioi] with u hu1 hu2 hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu)
    have hune : ((u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu0)
    rw [bdDetector, bdDetector, hu1, hu2, RCLike.inner_apply, bdDetectorFun, bdDetectorFun,
      Complex.conj_conj, conj_ofReal_cpow_baezDuarteDetectorGram hu0, ← Complex.cpow_add _ _ hune]
    congr 1
    rw [map_sub, map_one]
    ring
  rw [integral_congr_ae hcongr, integral_Ioi_cpow_of_lt hre one_pos, Complex.ofReal_one,
    Complex.one_cpow]
  rw [show (s₁ + (starRingEnd ℂ) s₂ - 2 + 1) = ((s₁ + (starRingEnd ℂ) s₂) - 1) from by ring,
    show (1 : ℂ) - s₁ - (starRingEnd ℂ) s₂ = -((s₁ + (starRingEnd ℂ) s₂) - 1) from by ring,
    div_neg, neg_div]

/-- The detector Gram at two zeros, in centered coordinates: the Cauchy kernel of `ρ - ½`. -/
theorem inner_bdDetector_bdDetector_zeros {ρ₁ ρ₂ : ℂ} (hρ₁ : 1 / 2 < ρ₁.re)
    (hρ₂ : 1 / 2 < ρ₂.re) :
    inner ℂ (bdDetector (one_sub_re_lt hρ₁)) (bdDetector (one_sub_re_lt hρ₂))
      = 1 / ((ρ₁ - 1 / 2) + (starRingEnd ℂ) (ρ₂ - 1 / 2)) := by
  rw [inner_bdDetector_bdDetector]
  congr 1
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    norm_num [Complex.ext_iff]
  simp only [map_sub, map_one, hhalf]
  ring

/-- **The bridge.**  The detector Gram matrix is the corpus's half-plane Hardy Cauchy Gram evaluated at
the centered zeros. -/
theorem inner_bdDetector_eq_rightHalfPlaneHardyCauchyGram {n : ℕ} (ρ : Fin n → ℂ)
    (hρ : ∀ j, 1 / 2 < (ρ j).re) (i j : Fin n) :
    inner ℂ (bdDetector (one_sub_re_lt (hρ i))) (bdDetector (one_sub_re_lt (hρ j)))
      = rightHalfPlaneHardyCauchyGram (fun k => ρ k - 1 / 2) i j := by
  rw [inner_bdDetector_bdDetector_zeros (hρ i) (hρ j), rightHalfPlaneHardyCauchyGram,
    starRingEnd_apply]

/-- **The Cauchy kernel of any right half-plane point family is a Gram matrix.**  For `Re w > 0` the
detector at `s = ½ − w` is a genuine vector of the carrier, and the corpus's Cauchy Gram is literally the
matrix of their inner products.  In particular `rightHalfPlaneHardyCauchyGram_posSemidef` is the statement
that a Gram matrix is positive semidefinite — the corpus proves it by an explicit boundary integral, and
this identification gives the structural reason. -/
theorem inner_bdDetector_eq_cauchyGram {n : ℕ} (w : Fin n → ℂ) (hw : ∀ i, 0 < (w i).re)
    (i j : Fin n) :
    inner ℂ (bdDetector (s := 1 / 2 - w i) (by
        rw [Complex.sub_re]
        have := hw i
        norm_num
        linarith))
      (bdDetector (s := 1 / 2 - w j) (by
        rw [Complex.sub_re]
        have := hw j
        norm_num
        linarith))
      = rightHalfPlaneHardyCauchyGram w i j := by
  rw [inner_bdDetector_bdDetector, rightHalfPlaneHardyCauchyGram, starRingEnd_apply]
  congr 1
  have hhalf : star (1 / 2 : ℂ) = 1 / 2 := by
    norm_num [Complex.ext_iff]
  rw [star_sub, hhalf]
  ring

/-! ## The many-zero floor -/

/-- A finite combination of detectors at zeros annihilates the closed span of the generators. -/
theorem inner_combination_bdDetector_eq_zero {n : ℕ} (ρ : Fin n → ℂ)
    (hρ : ∀ j, 1 / 2 < (ρ j).re) (hρ1 : ∀ j, (ρ j).re < 1)
    (hzero : ∀ j, riemannZeta (ρ j) = 0) (a : Fin n → ℂ) {G : BDCarrier}
    (hG : G ∈ (Submodule.span ℂ (Set.range (fun i : bdIndex => bdGen i.1))).topologicalClosure) :
    inner ℂ (∑ j, a j • bdDetector (one_sub_re_lt (hρ j))) G = 0 := by
  rw [sum_inner]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [inner_smul_left]
  have hker := GaloisForLFunctions.HTGeometry.continuousLinearMap_eq_zero_on_closedSpan
    (innerSL ℂ (bdDetector (one_sub_re_lt (hρ j)))) (fun i : bdIndex => bdGen i.1)
    (fun i => inner_bdDetector_bdGen_eq_zero (hρ j) (hρ1 j) (hzero j) i) hG
  have h0 : inner ℂ (bdDetector (one_sub_re_lt (hρ j))) G = 0 := hker
  rw [h0, mul_zero]

/-- **The many-zero Nyman--Beurling floor.**  For any orthonormal family built from detectors at zeta
zeros, the squared Báez-Duarte distance is at least the total squared pairing with the target.  This is
Bessel's inequality applied inside the detector span, and the constants involved are the Cauchy Gram
matrix `1/((ρ_i - ½) + conj(ρ_j - ½))` together with the target components `⟪detector, bdTarget⟫ = 1/ρ_i`.
-/
theorem bdTarget_dist_floor_orthonormal {n : ℕ} {k : Type*} [Fintype k] (ρ : Fin n → ℂ)
    (hρ : ∀ j, 1 / 2 < (ρ j).re) (hρ1 : ∀ j, (ρ j).re < 1)
    (hzero : ∀ j, riemannZeta (ρ j) = 0) (a : k → Fin n → ℂ)
    (he : Orthonormal ℂ (fun i : k => ∑ j, a i j • bdDetector (one_sub_re_lt (hρ j))))
    {G : BDCarrier}
    (hG : G ∈ (Submodule.span ℂ (Set.range (fun i : bdIndex => bdGen i.1))).topologicalClosure) :
    ∑ i : k, ‖inner ℂ (∑ j, a i j • bdDetector (one_sub_re_lt (hρ j))) bdTarget‖ ^ (2 : ℕ)
      ≤ ‖bdTarget - G‖ ^ (2 : ℕ) := by
  classical
  have hshift : ∀ i : k,
      inner ℂ (∑ j, a i j • bdDetector (one_sub_re_lt (hρ j))) (bdTarget - G)
        = inner ℂ (∑ j, a i j • bdDetector (one_sub_re_lt (hρ j))) bdTarget := by
    intro i
    rw [inner_sub_right, inner_combination_bdDetector_eq_zero ρ hρ hρ1 hzero (a i) hG, sub_zero]
  have hbessel := he.sum_inner_products_le (s := (Finset.univ : Finset k)) (bdTarget - G)
  calc ∑ i : k, ‖inner ℂ (∑ j, a i j • bdDetector (one_sub_re_lt (hρ j))) bdTarget‖ ^ (2 : ℕ)
      = ∑ i : k, ‖inner ℂ (∑ j, a i j • bdDetector (one_sub_re_lt (hρ j))) (bdTarget - G)‖ ^ (2 : ℕ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hshift i]
    _ ≤ ‖bdTarget - G‖ ^ (2 : ℕ) := hbessel

end RHTower

end
