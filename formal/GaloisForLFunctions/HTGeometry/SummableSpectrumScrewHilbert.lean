import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewValue

/-!
# The Hilbert screw of a summable-spectrum frequency family

Weighting each torus coordinate by `sqrt (a i / 2)` and recording its displacement from
the neutral phase embeds the product torus isometrically-in-square into `ℓ²`. The squared
Hilbert distance of two phases is exactly the phase-defect energy of their difference, so
the screw line becomes a curve whose squared chord length depends only on the time
difference: the classical screw property.

Consequently the relation hull is a compact connected monothetic group in the intrinsic
Hilbert metric, and the value and parity laws are its geometric radius laws.
-/

open Complex Filter Set Topology
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I : Type*} {a : I → ℝ}

/-! ## Multiplicativity of the circle coordinate -/

theorem screwCoord_add (x y : UnitAddCircle) :
    screwCoord (x + y) = screwCoord x * screwCoord y := by
  simp [screwCoord, fourier_apply, smul_add, AddCircle.toCircle_add]

theorem screwCoord_ne_zero (x : UnitAddCircle) : screwCoord x ≠ 0 := by
  intro h
  have := screwCoord_norm x
  rw [h] at this
  simp at this

theorem screwCoord_sub (x y : UnitAddCircle) :
    screwCoord (x - y) = screwCoord x * (starRingEnd ℂ) (screwCoord y) := by
  have hmul : screwCoord (x - y) * screwCoord y = screwCoord x := by
    rw [← screwCoord_add, sub_add_cancel]
  have hunit : screwCoord y * (starRingEnd ℂ) (screwCoord y) = 1 := by
    rw [Complex.mul_conj]
    have hns : Complex.normSq (screwCoord y) = 1 := by
      rw [Complex.normSq_eq_norm_sq, screwCoord_norm]; norm_num
    rw [hns]
    norm_num
  calc screwCoord (x - y)
      = screwCoord (x - y) * (screwCoord y * (starRingEnd ℂ) (screwCoord y)) := by
        rw [hunit, mul_one]
    _ = screwCoord (x - y) * screwCoord y * (starRingEnd ℂ) (screwCoord y) := by ring
    _ = screwCoord x * (starRingEnd ℂ) (screwCoord y) := by rw [hmul]

/-- A unit-modulus coordinate equal to one comes from the neutral phase. -/
theorem eq_zero_of_screwCoord_re_eq_one {x : UnitAddCircle}
    (hx : (screwCoord x).re = 1) : x = 0 := by
  have hnorm : ‖screwCoord x‖ = 1 := screwCoord_norm x
  have hsq : (screwCoord x).re ^ 2 + (screwCoord x).im ^ 2 = 1 := by
    have hns : Complex.normSq (screwCoord x) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hnorm]; norm_num
    simpa [Complex.normSq_apply, sq] using hns
  have him : (screwCoord x).im = 0 := by
    have h2 : (screwCoord x).im ^ 2 = 0 := by rw [hx] at hsq; nlinarith [hsq]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  have hval : screwCoord x = 1 := by
    apply Complex.ext <;> simp [hx, him]
  have hcirc : AddCircle.toCircle (T := (1 : ℝ)) x =
      AddCircle.toCircle (T := (1 : ℝ)) (0 : UnitAddCircle) := by
    apply Subtype.ext
    have h1 : ((AddCircle.toCircle (T := (1 : ℝ)) x : Circle) : ℂ) = 1 := by
      rw [← hval, screwCoord, fourier_apply, one_smul]
    have h2 : ((AddCircle.toCircle (T := (1 : ℝ)) (0 : UnitAddCircle) : Circle) : ℂ) = 1 := by
      have := screwCoord_zero
      rw [screwCoord, fourier_apply, one_smul] at this
      exact this
    rw [h1, h2]
  exact AddCircle.injective_toCircle one_ne_zero hcirc

/-! ## The Hilbert screw embedding -/

/-- Weighted displacement of a phase from the neutral phase. -/
def screwEmbedFun (a : I → ℝ) (z : I → UnitAddCircle) : I → ℂ :=
  fun i => (Real.sqrt (a i / 2) : ℂ) * (1 - screwCoord (z i))

/-- **Screw identity, coordinatewise.** The squared Hilbert gap of two phases in one
coordinate is the phase-defect energy of their difference in that coordinate. -/
theorem sq_norm_screwEmbedFun_sub (hpos : ∀ i, 0 ≤ a i) (z w : I → UnitAddCircle) (i : I) :
    ‖screwEmbedFun a z i - screwEmbedFun a w i‖ ^ 2 =
      a i * (1 - (screwCoord ((z - w) i)).re) := by
  set s : ℝ := Real.sqrt (a i / 2) with hs
  have hs2 : s ^ 2 = a i / 2 := Real.sq_sqrt (by linarith [hpos i])
  set zeta : ℂ := screwCoord (z i) with hzeta
  set xi : ℂ := screwCoord (w i) with hxi
  have hdiff : screwEmbedFun a z i - screwEmbedFun a w i = (s : ℂ) * (xi - zeta) := by
    simp only [screwEmbedFun, hzeta, hxi, hs]
    ring
  have hzn : zeta.re ^ 2 + zeta.im ^ 2 = 1 := by
    have hns : Complex.normSq zeta = 1 := by
      rw [Complex.normSq_eq_norm_sq, hzeta, screwCoord_norm]; norm_num
    simpa [Complex.normSq_apply, sq] using hns
  have hxn : xi.re ^ 2 + xi.im ^ 2 = 1 := by
    have hns : Complex.normSq xi = 1 := by
      rw [Complex.normSq_eq_norm_sq, hxi, screwCoord_norm]; norm_num
    simpa [Complex.normSq_apply, sq] using hns
  have hcoord : (screwCoord ((z - w) i)).re = zeta.re * xi.re + zeta.im * xi.im := by
    have : (z - w) i = z i - w i := rfl
    rw [this, screwCoord_sub, ← hzeta, ← hxi]
    simp [Complex.mul_re]
  rw [hdiff, hcoord]
  have hnormsq : ‖(s : ℂ) * (xi - zeta)‖ ^ 2 = s ^ 2 * ((xi - zeta).re ^ 2 + (xi - zeta).im ^ 2) := by
    rw [norm_mul, mul_pow]
    congr 1
    · simp [Complex.norm_real, sq_abs]
    · have hns : Complex.normSq (xi - zeta) = (xi - zeta).re ^ 2 + (xi - zeta).im ^ 2 := by
        simp [Complex.normSq_apply, sq]
      rw [← hns, Complex.normSq_eq_norm_sq]
  rw [hnormsq, hs2]
  simp only [Complex.sub_re, Complex.sub_im]
  nlinarith [hzn, hxn]

theorem screwEmbedFun_zero (a : I → ℝ) : screwEmbedFun a (0 : I → UnitAddCircle) = 0 := by
  funext i
  simp [screwEmbedFun]

theorem sq_norm_screwEmbedFun (hpos : ∀ i, 0 ≤ a i) (z : I → UnitAddCircle) (i : I) :
    ‖screwEmbedFun a z i‖ ^ 2 = a i * (1 - (screwCoord (z i)).re) := by
  have h := sq_norm_screwEmbedFun_sub hpos z (0 : I → UnitAddCircle) i
  rw [screwEmbedFun_zero] at h
  simpa using h

theorem memLp_screwEmbedFun (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a)
    (z : I → UnitAddCircle) : Memℓp (screwEmbedFun a z) 2 := by
  refine memℓp_gen ?_
  have hp : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [hp]
  refine Summable.congr (screwValue_summable hpos hsum z) fun i => ?_
  rw [show ‖screwEmbedFun a z i‖ ^ (2 : ℝ) = ‖screwEmbedFun a z i‖ ^ (2 : ℕ) by
    rw [← Real.rpow_natCast]; norm_num]
  exact (sq_norm_screwEmbedFun hpos z i).symm

/-- The Hilbert screw embedding of the product torus. -/
def screwEmbed (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a) (z : I → UnitAddCircle) :
    lp (fun _ : I => ℂ) 2 :=
  ⟨screwEmbedFun a z, memLp_screwEmbedFun hpos hsum z⟩

@[simp]
theorem screwEmbed_coe (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a) (z : I → UnitAddCircle) :
    (screwEmbed hpos hsum z : I → ℂ) = screwEmbedFun a z := rfl

/-- **Hilbert screw law.** The squared Hilbert distance of two phases is the phase-defect
energy of their difference. -/
theorem sq_norm_screwEmbed_sub (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a)
    (z w : I → UnitAddCircle) :
    ‖screwEmbed hpos hsum z - screwEmbed hpos hsum w‖ ^ 2 = screwValue a (z - w) := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hrpow := lp.norm_rpow_eq_tsum hp (screwEmbed hpos hsum z - screwEmbed hpos hsum w)
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2] at hrpow
  rw [show ‖screwEmbed hpos hsum z - screwEmbed hpos hsum w‖ ^ (2 : ℕ) =
      ‖screwEmbed hpos hsum z - screwEmbed hpos hsum w‖ ^ (2 : ℝ) by
    rw [← Real.rpow_natCast]; norm_num]
  rw [hrpow, screwValue]
  refine tsum_congr fun i => ?_
  have hsubcoe : ((screwEmbed hpos hsum z - screwEmbed hpos hsum w : lp (fun _ : I => ℂ) 2) :
      I → ℂ) i = screwEmbedFun a z i - screwEmbedFun a w i := by
    rw [lp.coeFn_sub]
    rfl
  rw [hsubcoe]
  rw [show ‖screwEmbedFun a z i - screwEmbedFun a w i‖ ^ (2 : ℝ) =
      ‖screwEmbedFun a z i - screwEmbedFun a w i‖ ^ (2 : ℕ) by
    rw [← Real.rpow_natCast]; norm_num]
  exact sq_norm_screwEmbedFun_sub hpos z w i

/-- **Screw property of the line.** Along the screw line the squared Hilbert chord
depends only on the time difference, and equals the screw series there. -/
theorem sq_norm_screwEmbed_screwPhase_sub (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a)
    (omega : I → ℝ) (t u : ℝ) :
    ‖screwEmbed hpos hsum (screwPhase omega t) -
        screwEmbed hpos hsum (screwPhase omega u)‖ ^ 2 =
      screwSeries a omega (t - u) := by
  rw [sq_norm_screwEmbed_sub, screwSeries_eq_screwValue]
  congr 1
  have hneg : screwPhase omega (-u) = -screwPhase omega u := map_neg (screwLineHom omega) u
  have hsub : screwPhase omega t - screwPhase omega u = screwPhase omega (t - u) := by
    rw [sub_eq_add_neg, ← hneg, ← screwPhase_add, ← sub_eq_add_neg]
  rw [hsub]

/-- With strictly positive weights the Hilbert screw embedding is injective. -/
theorem screwEmbed_injective (hpos : ∀ i, 0 < a i) (hsum : Summable a) :
    Function.Injective (screwEmbed (fun i => (hpos i).le) hsum) := by
  intro z w hzw
  have hzero : screwValue a (z - w) = 0 := by
    have := sq_norm_screwEmbed_sub (fun i => (hpos i).le) hsum z w
    rw [hzw, sub_self, norm_zero] at this
    simpa using this.symm
  have hterms : ∀ i, a i * (1 - (screwCoord ((z - w) i)).re) = 0 := by
    intro i
    have hnn := screwValue_term_nonneg (fun i => (hpos i).le) (z - w)
    have hsummable := screwValue_summable (fun i => (hpos i).le) hsum (z - w)
    have hle := hsummable.le_tsum i (fun j _ => hnn j)
    rw [← screwValue, hzero] at hle
    exact le_antisymm hle (hnn i)
  funext i
  have hre : (screwCoord ((z - w) i)).re = 1 := by
    have h := hterms i
    have ha := hpos i
    nlinarith [h, ha]
  have hz0 : (z - w) i = 0 := eq_zero_of_screwCoord_re_eq_one hre
  have : z i - w i = 0 := hz0
  linear_combination (norm := abel) this

end

end GaloisForLFunctions.HTGeometry
