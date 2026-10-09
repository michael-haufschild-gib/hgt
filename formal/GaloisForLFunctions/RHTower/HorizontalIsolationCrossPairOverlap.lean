import GaloisForLFunctions.RHTower.HorizontallyIsolatedSimpleZeros

/-!
# Cross-pair overlaps of the sampled Weil vectors

For two off-line zeros `p = ½ + ε_p + iγ_p` and `q = ½ + ε_q + iγ_q` with `Δ = γ_q − γ_p`, the
sampled real and imaginary vectors are `g_p(k) = Re φ̂(γ_p − iε_p − τ_k)/√c` and
`h_q(k) = Im φ̂(γ_q − iε_q − τ_k)/√c`.  On the full sampling grid their overlaps are window
integrals (`hasSum_re_mul_re_cross_grid`, `hasSum_re_mul_im_cross_grid`):

  `Σ_k g_p g_q = L ∫ φ² cosh(ε_p u) cosh(ε_q u) cos(Δu) / c`,
  `Σ_k g_p h_q = L ∫ φ² cosh(ε_p u) sinh(ε_q u) sin(Δu) / c`,

with `c = aL² = L ∫ φ²`.

The imaginary part is the transform of a sinh window: `Im φ̂(w − iε) = (−i φ sinh(ε·))^(w)`
(`paperFT_sinh_eq_im`).  The frequency shift `Δ` is a modulation `e^{iΔu}` of the window
(`paperFT_add_ofReal`).  The polarised sampling Parseval identity
(`hasSum_re_mul_re_paperFT_grid`) then applies with the real window `φ cosh(ε_p ·)`.
`inner_blockReVec_blockReVec_eq_grid` and `inner_blockImVec_blockReVec_eq_grid` identify the
truncated block inner products with `c⁻¹` times the first `d` terms of those series.
-/

open Complex MeasureTheory
open scoped RealInnerProductSpace

namespace RHTower

noncomputable section

/-- The odd shift difference of a window transform:
`(φ̂(w − iε) − φ̂(w + iε))/2 = (φ sinh(ε·))^(w)`. -/
theorem paperFT_sinh_diff {φ : ℝ → ℝ} {L : ℝ} (hc : Continuous φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) (w ε : ℝ) :
    (Zeta23.paperFT (fun u => (φ u : ℂ)) ((w : ℂ) - ε * I)
        - Zeta23.paperFT (fun u => (φ u : ℂ)) ((w : ℂ) + ε * I)) / 2
      = Zeta23.paperFT (fun u => ((φ u * Real.sinh (ε * u) : ℝ) : ℂ)) (w : ℂ) := by
  simp only [Zeta23.paperFT]
  have i1 := integrable_ofReal_mul_cexp hc hsupp ((w : ℂ) - ε * I)
  have i2 := integrable_ofReal_mul_cexp hc hsupp ((w : ℂ) + ε * I)
  rw [← integral_sub i1 i2, ← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  have e1 : I * ((w : ℂ) - ε * I) * u = I * w * u + (ε * u : ℝ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  have e2 : I * ((w : ℂ) + ε * I) * u = I * w * u + (-(ε * u) : ℝ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [e1, e2, Complex.exp_add, Complex.exp_add]
  have hsinh : ((Real.sinh (ε * u) : ℝ) : ℂ) =
      (cexp ((ε * u : ℝ) : ℂ) - cexp ((-(ε * u) : ℝ) : ℂ)) / 2 := by
    rw [Complex.ofReal_sinh, Complex.sinh]; push_cast; ring_nf
  push_cast
  rw [show ((Real.sinh (ε * u)) : ℂ) = Complex.sinh ((ε : ℂ) * u) by push_cast; rfl] at hsinh
  rw [hsinh]
  push_cast
  ring

/-- **The imaginary part is a sinh-window transform.**
`(−i φ sinh(ε·))^(w) = Im φ̂(w − iε)` for real `w, ε`. -/
theorem paperFT_sinh_eq_im (Q : Zeta23.Params) (T : ℝ) (hc : Continuous (Q.phi T))
    (hsupp : ∀ u, Q.L T / 2 ≤ |u| → Q.phi T u = 0) (hconj : Zeta23.ZeroSide.PhiHatConj T Q)
    (w ε : ℝ) :
    Zeta23.paperFT (fun u => -I * ((Q.phi T u * Real.sinh (ε * u) : ℝ) : ℂ)) (w : ℂ)
      = ((Q.phiHat T ((w : ℂ) - ε * I)).im : ℂ) := by
  have hlin : Zeta23.paperFT (fun u => -I * ((Q.phi T u * Real.sinh (ε * u) : ℝ) : ℂ)) (w : ℂ)
      = -I * Zeta23.paperFT (fun u => ((Q.phi T u * Real.sinh (ε * u) : ℝ) : ℂ)) (w : ℂ) := by
    simp only [Zeta23.paperFT]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    ring
  rw [hlin, ← paperFT_sinh_diff hc hsupp w ε]
  have hconj' : Q.phiHat T ((w : ℂ) + ε * I) = starRingEnd ℂ (Q.phiHat T ((w : ℂ) - ε * I)) := by
    rw [← hconj]; congr 1; simp [Complex.conj_ofReal]
  change -I * ((Q.phiHat T ((w : ℂ) - ε * I) - Q.phiHat T ((w : ℂ) + ε * I)) / 2) = _
  rw [hconj']
  apply Complex.ext <;> simp

/-- **Cross overlap of real parts on the full grid.**  With `w_j = γ − τ_j`,
`Σ_j Re φ̂(w_j − iε_p) Re φ̂(w_j + Δ − iε_q) / c = L ∫ φ² cosh(ε_p u) cosh(ε_q u) cos(Δu) / c`. -/
theorem hasSum_re_mul_re_cross_grid (Q : Zeta23.Params) (T : ℝ) (hL : 0 < Q.L T)
    (hc : Continuous (Q.phi T)) (hsupp : ∀ u, Q.L T / 2 ≤ |u| → Q.phi T u = 0)
    (hconj : Zeta23.ZeroSide.PhiHatConj T Q) (γ Δ εp εq : ℝ) :
    HasSum (fun j : ℤ =>
        (Q.phiHat T ((((γ - (T + j * (2 * Real.pi / Q.L T))) : ℝ) : ℂ) - εp * I)).re
          * (Q.phiHat T ((((γ - (T + j * (2 * Real.pi / Q.L T)) + Δ) : ℝ) : ℂ) - εq * I)).re)
      (Q.L T * ∫ u in (-(Q.L T / 2))..(Q.L T / 2),
        Q.phi T u ^ 2 * Real.cosh (εp * u) * Real.cosh (εq * u) * Real.cos (Δ * u)) := by
  set L := Q.L T with hLdef
  set φ := Q.phi T with hφ
  set a : ℝ → ℝ := fun u => φ u * Real.cosh (εp * u) with ha
  have hac : Continuous a := by simp only [ha]; exact hc.mul (by fun_prop)
  have has : ∀ u, L / 2 ≤ |u| → a u = 0 := fun u hu => by
    simp only [ha]; rw [show φ u = 0 from hsupp u hu, zero_mul]
  set b : ℝ → ℂ := fun u => ((φ u * Real.cosh (εq * u) : ℝ) : ℂ) * cexp (I * Δ * u) with hb
  have hbc : Continuous b := by simp only [hb]; fun_prop
  have hbs : ∀ u, L / 2 ≤ |u| → b u = 0 := fun u hu => by
    simp only [hb]; rw [show φ u = 0 from hsupp u hu, zero_mul, Complex.ofReal_zero, zero_mul]
  have hbre : ∀ u, (b u).re = φ u * Real.cosh (εq * u) * Real.cos (Δ * u) := fun u => by
    simp only [hb]
    rw [show I * (Δ : ℂ) * (u : ℂ) = ((Δ * u : ℝ) : ℂ) * I by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  set w : ℤ → ℝ := fun j => γ - (T + j * (2 * Real.pi / L)) with hw
  have hagrid : ∀ j : ℤ, Zeta23.paperFT (fun u => (a u : ℂ)) ((w j : ℝ) : ℂ)
      = ((Q.phiHat T (((w j : ℝ) : ℂ) - εp * I)).re : ℂ) :=
    fun j => paperFT_cosh_eq_re Q T hc hsupp hconj (w j) εp
  have hbgrid : ∀ j : ℤ, Zeta23.paperFT b ((w j : ℝ) : ℂ)
      = ((Q.phiHat T ((((w j + Δ) : ℝ) : ℂ) - εq * I)).re : ℂ) := by
    intro j
    rw [← paperFT_cosh_eq_re Q T hc hsupp hconj (w j + Δ) εq]
    rw [show (((w j + Δ) : ℝ) : ℂ) = ((w j : ℝ) : ℂ) + (Δ : ℝ) by push_cast; ring,
      paperFT_add_ofReal]
  have hreal' : ∀ j : ℤ, (Zeta23.paperFT (fun u => (a u : ℂ)) ((w j : ℝ) : ℂ)).im = 0 := by
    intro j; rw [hagrid j, Complex.ofReal_im]
  have h := hasSum_re_mul_re_paperFT_grid hL hac hbc has hbs γ T hreal'
  have hint : (∫ u in (-(L / 2))..(L / 2), a u * (b u).re) =
      ∫ u in (-(L / 2))..(L / 2),
        φ u ^ 2 * Real.cosh (εp * u) * Real.cosh (εq * u) * Real.cos (Δ * u) := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [ha, hbre]; ring
  rw [hint] at h
  refine h.congr_fun fun j => ?_
  rw [hagrid j, hbgrid j, Complex.ofReal_re, Complex.ofReal_re]

/-- **Cross overlap of a real part with an imaginary part on the full grid.**
`Σ_j Re φ̂(w_j − iε_p) Im φ̂(w_j + Δ − iε_q) = L ∫ φ² cosh(ε_p u) sinh(ε_q u) sin(Δu)`. -/
theorem hasSum_re_mul_im_cross_grid (Q : Zeta23.Params) (T : ℝ) (hL : 0 < Q.L T)
    (hc : Continuous (Q.phi T)) (hsupp : ∀ u, Q.L T / 2 ≤ |u| → Q.phi T u = 0)
    (hconj : Zeta23.ZeroSide.PhiHatConj T Q) (γ Δ εp εq : ℝ) :
    HasSum (fun j : ℤ =>
        (Q.phiHat T ((((γ - (T + j * (2 * Real.pi / Q.L T))) : ℝ) : ℂ) - εp * I)).re
          * (Q.phiHat T ((((γ - (T + j * (2 * Real.pi / Q.L T)) + Δ) : ℝ) : ℂ) - εq * I)).im)
      (Q.L T * ∫ u in (-(Q.L T / 2))..(Q.L T / 2),
        Q.phi T u ^ 2 * Real.cosh (εp * u) * Real.sinh (εq * u) * Real.sin (Δ * u)) := by
  set L := Q.L T with hLdef
  set φ := Q.phi T with hφ
  set a : ℝ → ℝ := fun u => φ u * Real.cosh (εp * u) with ha
  have hac : Continuous a := by simp only [ha]; exact hc.mul (by fun_prop)
  have has : ∀ u, L / 2 ≤ |u| → a u = 0 := fun u hu => by
    simp only [ha]; rw [show φ u = 0 from hsupp u hu, zero_mul]
  set b : ℝ → ℂ := fun u =>
    -I * ((φ u * Real.sinh (εq * u) : ℝ) : ℂ) * cexp (I * Δ * u) with hb
  have hbc : Continuous b := by simp only [hb]; fun_prop
  have hbs : ∀ u, L / 2 ≤ |u| → b u = 0 := fun u hu => by
    simp only [hb]; rw [show φ u = 0 from hsupp u hu, zero_mul, Complex.ofReal_zero, mul_zero,
      zero_mul]
  have hbre : ∀ u, (b u).re = φ u * Real.sinh (εq * u) * Real.sin (Δ * u) := fun u => by
    simp only [hb]
    rw [show I * (Δ : ℂ) * (u : ℂ) = ((Δ * u : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I]
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  set w : ℤ → ℝ := fun j => γ - (T + j * (2 * Real.pi / L)) with hw
  have hagrid : ∀ j : ℤ, Zeta23.paperFT (fun u => (a u : ℂ)) ((w j : ℝ) : ℂ)
      = ((Q.phiHat T (((w j : ℝ) : ℂ) - εp * I)).re : ℂ) :=
    fun j => paperFT_cosh_eq_re Q T hc hsupp hconj (w j) εp
  have hbgrid : ∀ j : ℤ, Zeta23.paperFT b ((w j : ℝ) : ℂ)
      = ((Q.phiHat T ((((w j + Δ) : ℝ) : ℂ) - εq * I)).im : ℂ) := by
    intro j
    rw [← paperFT_sinh_eq_im Q T hc hsupp hconj (w j + Δ) εq]
    rw [show (((w j + Δ) : ℝ) : ℂ) = ((w j : ℝ) : ℂ) + (Δ : ℝ) by push_cast; ring,
      paperFT_add_ofReal]
  have hreal' : ∀ j : ℤ, (Zeta23.paperFT (fun u => (a u : ℂ)) ((w j : ℝ) : ℂ)).im = 0 := by
    intro j; rw [hagrid j, Complex.ofReal_im]
  have h := hasSum_re_mul_re_paperFT_grid hL hac hbc has hbs γ T hreal'
  have hint : (∫ u in (-(L / 2))..(L / 2), a u * (b u).re) =
      ∫ u in (-(L / 2))..(L / 2),
        φ u ^ 2 * Real.cosh (εp * u) * Real.sinh (εq * u) * Real.sin (Δ * u) := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [ha, hbre]; ring
  rw [hint] at h
  refine h.congr_fun fun j => ?_
  rw [hagrid j, hbgrid j, Complex.ofReal_re, Complex.ofReal_re]

/-! ## The block vectors -/

open Zeta23 Zeta23.ZeroSide

variable {Z : ZeroConfig} {T : ℝ} {P : Params}

/-- The sampled vector of a zero `ρ = ½ + ε + iγ` evaluates `φ̂(γ − iε − τ_k)`. -/
theorem blockData_v_eq (hconj : PhiHatConj T P) (ρ : ZI Z T) (k : Fin (P.d T)) :
    (blockData Z T P hconj).v ρ k =
      P.phiHat T ((((ρ : ℂ).im : ℝ) : ℂ) - (((ρ : ℂ).re - 1 / 2 : ℝ) : ℂ) * I - P.tau T k) := by
  simp only [blockData, mkData_v, evalVec, gammaOf_eq_im_sub]

/-- **Truncated real–real cross overlap.** -/
theorem inner_blockReVec_blockReVec (hconj : PhiHatConj T P) (c : ℝ) (p q : ZI Z T) :
    ⟪blockReVec (blockData Z T P hconj) c q, blockReVec (blockData Z T P hconj) c p⟫ =
      ∑ k : Fin (P.d T),
        (P.phiHat T ((((p : ℂ).im : ℝ) : ℂ) - (((p : ℂ).re - 1 / 2 : ℝ) : ℂ) * I
            - P.tau T k)).re / Real.sqrt c
          * ((P.phiHat T ((((q : ℂ).im : ℝ) : ℂ) - (((q : ℂ).re - 1 / 2 : ℝ) : ℂ) * I
            - P.tau T k)).re / Real.sqrt c) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, blockReVec_apply,
    blockData_v_eq]

/-- **Truncated imaginary–real cross overlap.** -/
theorem inner_blockImVec_blockReVec (hconj : PhiHatConj T P) (c : ℝ) (p q : ZI Z T) :
    ⟪blockImVec (blockData Z T P hconj) c q, blockReVec (blockData Z T P hconj) c p⟫ =
      ∑ k : Fin (P.d T),
        (P.phiHat T ((((p : ℂ).im : ℝ) : ℂ) - (((p : ℂ).re - 1 / 2 : ℝ) : ℂ) * I
            - P.tau T k)).re / Real.sqrt c
          * ((P.phiHat T ((((q : ℂ).im : ℝ) : ℂ) - (((q : ℂ).re - 1 / 2 : ℝ) : ℂ) * I
            - P.tau T k)).im / Real.sqrt c) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, blockReVec_apply,
    blockImVec_apply, blockData_v_eq]

/-- The grid point `γ_p − τ_k` in the form `w_k + Δ` used by the full-grid identities. -/
theorem grid_point_eq (P : Params) (T γp γq : ℝ) (k : Fin (P.d T)) :
    (((γq : ℝ) : ℂ) - P.tau T k) =
      ((((γp - (T + ((k : ℕ) : ℤ) * (2 * Real.pi / P.L T))) + (γq - γp) : ℝ)) : ℂ) := by
  simp only [Params.tau, Params.hgrid]
  push_cast
  ring

/-- **Truncated overlaps are partial sums of the full-grid series.**  With `γ = Im p`,
`Δ = Im q − Im p`, `ε_p = Re p − ½`, `ε_q = Re q − ½` and `c > 0`, the block inner products are
`c⁻¹ Σ_{k<d}` of the summands of `hasSum_re_mul_re_cross_grid` and `hasSum_re_mul_im_cross_grid`
at `j = k`. -/
theorem inner_blockReVec_blockReVec_eq_grid (hconj : PhiHatConj T P) {c : ℝ} (hc : 0 < c)
    (p q : ZI Z T) :
    ⟪blockReVec (blockData Z T P hconj) c q, blockReVec (blockData Z T P hconj) c p⟫ =
      (∑ k : Fin (P.d T),
        (P.phiHat T (((((p : ℂ).im - (T + ((k : ℕ) : ℤ) * (2 * Real.pi / P.L T))) : ℝ) : ℂ)
            - (((p : ℂ).re - 1 / 2 : ℝ) : ℂ) * I)).re
          * (P.phiHat T (((((p : ℂ).im - (T + ((k : ℕ) : ℤ) * (2 * Real.pi / P.L T))
              + ((q : ℂ).im - (p : ℂ).im)) : ℝ) : ℂ)
            - (((q : ℂ).re - 1 / 2 : ℝ) : ℂ) * I)).re) / c := by
  rw [inner_blockReVec_blockReVec, Finset.sum_div]
  have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 : ((((p : ℂ).im : ℝ) : ℂ) - (((p : ℂ).re - 1 / 2 : ℝ) : ℂ) * I - P.tau T k) =
      (((((p : ℂ).im - (T + ((k : ℕ) : ℤ) * (2 * Real.pi / P.L T))) : ℝ) : ℂ)
        - (((p : ℂ).re - 1 / 2 : ℝ) : ℂ) * I) := by
    simp only [Params.tau, Params.hgrid]; push_cast; ring
  have e2 : ((((q : ℂ).im : ℝ) : ℂ) - (((q : ℂ).re - 1 / 2 : ℝ) : ℂ) * I - P.tau T k) =
      (((((p : ℂ).im - (T + ((k : ℕ) : ℤ) * (2 * Real.pi / P.L T))
          + ((q : ℂ).im - (p : ℂ).im)) : ℝ) : ℂ) - (((q : ℂ).re - 1 / 2 : ℝ) : ℂ) * I) := by
    simp only [Params.tau, Params.hgrid]; push_cast; ring
  rw [e1, e2, div_mul_div_comm, hsq]

/-- The imaginary–real version of `inner_blockReVec_blockReVec_eq_grid`. -/
theorem inner_blockImVec_blockReVec_eq_grid (hconj : PhiHatConj T P) {c : ℝ} (hc : 0 < c)
    (p q : ZI Z T) :
    ⟪blockImVec (blockData Z T P hconj) c q, blockReVec (blockData Z T P hconj) c p⟫ =
      (∑ k : Fin (P.d T),
        (P.phiHat T (((((p : ℂ).im - (T + ((k : ℕ) : ℤ) * (2 * Real.pi / P.L T))) : ℝ) : ℂ)
            - (((p : ℂ).re - 1 / 2 : ℝ) : ℂ) * I)).re
          * (P.phiHat T (((((p : ℂ).im - (T + ((k : ℕ) : ℤ) * (2 * Real.pi / P.L T))
              + ((q : ℂ).im - (p : ℂ).im)) : ℝ) : ℂ)
            - (((q : ℂ).re - 1 / 2 : ℝ) : ℂ) * I)).im) / c := by
  rw [inner_blockImVec_blockReVec, Finset.sum_div]
  have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 : ((((p : ℂ).im : ℝ) : ℂ) - (((p : ℂ).re - 1 / 2 : ℝ) : ℂ) * I - P.tau T k) =
      (((((p : ℂ).im - (T + ((k : ℕ) : ℤ) * (2 * Real.pi / P.L T))) : ℝ) : ℂ)
        - (((p : ℂ).re - 1 / 2 : ℝ) : ℂ) * I) := by
    simp only [Params.tau, Params.hgrid]; push_cast; ring
  have e2 : ((((q : ℂ).im : ℝ) : ℂ) - (((q : ℂ).re - 1 / 2 : ℝ) : ℂ) * I - P.tau T k) =
      (((((p : ℂ).im - (T + ((k : ℕ) : ℤ) * (2 * Real.pi / P.L T))
          + ((q : ℂ).im - (p : ℂ).im)) : ℝ) : ℂ) - (((q : ℂ).re - 1 / 2 : ℝ) : ℂ) * I) := by
    simp only [Params.tau, Params.hgrid]; push_cast; ring
  rw [e1, e2, div_mul_div_comm, hsq]

end

end RHTower
