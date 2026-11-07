import GaloisForLFunctions.BlackHoleRingdown.TheCuspChannel
import GaloisForLFunctions.HTGeometry.ModularFundamentalDomainVolume
import GaloisForLFunctions.HTGeometry.PeterssonInnerProductLevelOne
import GaloisForLFunctions.HTGeometry.HolomorphicPoincareSeries
import GaloisForLFunctions.RHTower.EisensteinHoroballBound

/-!
# The cusp forms of the modular horizon exist

The mirror `ι z = -z̄` normalizes `SL₂(ℤ)` (`mirror_smul`) and maps every closed horocycle to itself. So a
modular function that is odd under `ι` has zero mean on every closed horocycle
(`horocycle_mean_eq_zero_of_odd`): **the odd sector of the horizon is cuspidal**. It is orthogonal to the
constants and to the Eisenstein channel, so it carries no resonance and no zero of `ξ`.

Odd smooth modular functions supported in the cusp exist. Let `ψ_k` be a bump supported in
`(2 + 2k, 3 + 2k)` and `G_k(w) = ψ_k(Im w) sin(2π Re w)`. Put `F_k(z) = G_k(γ z)` for any `γ ∈ SL₂(ℤ)` with
`Im γz > ½`. This does not depend on `γ`: a matrix with `c ≠ 0` maps heights above `½` below `2`
(`im_smul_le_inv`), where `G_k` vanishes, and a matrix with `c = 0` is a translation. The `F_k` are vectors of
the cuspidal form domain of the corpus spectral theorem, nonzero and pairwise orthogonal.

So the cuspidal eigenbasis is infinite (`infinite_cuspEigenIndex`), there are infinitely many distinct
cuspidal Laplace eigenvalues at level one (`infinite_cuspEigenvalues`), and **Maass cusp forms for `SL₂(ℤ)`
exist** (`exists_maassCuspForm`). On the modular black hole the cusp channel rings forever in infinitely many
tones, each undamped at the rate of the boundary condition (`infinite_undamped_tones`). The input is the
discreteness of the cuspidal spectrum, which the corpus proves by compactness; no Weyl law is used.
-/

open Complex MeasureTheory Set Filter Topology
open scoped MatrixGroups UpperHalfPlane InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.DeckPointPair
  MaassFiniteDeckDirichlet SelbergMaassCongruenceTrace

namespace OddCusp

/-! ### The mirror of the upper half-plane -/

/-- The mirror `z ↦ -z̄` of the upper half-plane. -/
def mirror (z : ℍ) : ℍ := ⟨-(starRingEnd ℂ) (z : ℂ), by simpa using z.im_pos⟩

@[simp] theorem coe_mirror (z : ℍ) : (mirror z : ℂ) = -(starRingEnd ℂ) (z : ℂ) := rfl

theorem mirror_im (z : ℍ) : (mirror z).im = z.im := by
  show (-(starRingEnd ℂ) (z : ℂ)).im = (z : ℂ).im
  simp

/-- The conjugate of a modular matrix by the mirror. -/
def mirrorSL (g : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨Matrix.of ![![g 0 0, -g 0 1], ![-g 1 0, g 1 1]], by
    have h := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    linear_combination h⟩

@[simp] theorem mirrorSL_00 (g : SL(2, ℤ)) : mirrorSL g 0 0 = g 0 0 := rfl
@[simp] theorem mirrorSL_01 (g : SL(2, ℤ)) : mirrorSL g 0 1 = -g 0 1 := rfl
@[simp] theorem mirrorSL_10 (g : SL(2, ℤ)) : mirrorSL g 1 0 = -g 1 0 := rfl
@[simp] theorem mirrorSL_11 (g : SL(2, ℤ)) : mirrorSL g 1 1 = g 1 1 := rfl

/-- **The mirror normalizes the modular group**: `ι (g z) = g' (ι z)`. -/
theorem mirror_smul (g : SL(2, ℤ)) (z : ℍ) : mirror (g • z) = mirrorSL g • mirror z := by
  apply UpperHalfPlane.ext
  rw [coe_mirror, UpperHalfPlane.coe_specialLinearGroup_apply,
    UpperHalfPlane.coe_specialLinearGroup_apply, coe_mirror]
  simp only [mirrorSL_00, mirrorSL_01, mirrorSL_10, mirrorSL_11, algebraMap_int_eq, eq_intCast,
    map_div₀, map_add, map_mul, Complex.conj_ofReal, Int.cast_neg, Complex.ofReal_neg]
  ring

/-! ### Heights above `½` meet only translates -/

/-- A matrix with `c ≠ 0` maps height `y` to height at most `1/y`. -/
theorem im_smul_le_inv {g : SL(2, ℤ)} (hc : g 1 0 ≠ 0) (z : ℍ) : (g • z).im ≤ 1 / z.im := by
  have hy := z.im_pos
  rw [ModularGroup.im_smul_eq_div_normSq, _root_.RHTower.denom_SL2Z]
  have hc1 : (1 : ℝ) ≤ ((g 1 0 : ℤ) : ℝ) ^ 2 := by
    have h1 : (1 : ℤ) ≤ (g 1 0) ^ 2 := by
      have := Int.one_le_abs hc
      nlinarith [sq_abs (g 1 0), abs_nonneg (g 1 0)]
    exact_mod_cast h1
  set w : ℂ := ((g 1 0 : ℤ) : ℂ) * (z : ℂ) + ((g 1 1 : ℤ) : ℂ) with hw
  have him : w.im = ((g 1 0 : ℤ) : ℝ) * z.im := by rw [hw]; simp
  have hn : z.im ^ 2 ≤ Complex.normSq w := by
    rw [Complex.normSq_apply, him]
    nlinarith [mul_self_nonneg w.re, mul_le_mul_of_nonneg_right hc1 (sq_nonneg z.im)]
  have hpos : 0 < Complex.normSq w := lt_of_lt_of_le (by positivity) hn
  rw [div_le_div_iff₀ hpos hy]
  nlinarith

theorem im_lt_two_of_ne_zero {g : SL(2, ℤ)} (hc : g 1 0 ≠ 0) {w : ℍ} (hw : 1 / 2 < w.im) :
    (g • w).im < 2 := by
  have h := im_smul_le_inv hc w
  have h2 : 1 / w.im < 2 := by
    rw [div_lt_iff₀ w.im_pos]
    linarith
  linarith

/-- A matrix with `c = 0` is a translation. -/
theorem exists_int_of_bottom_zero {g : SL(2, ℤ)} (hc : g 1 0 = 0) (w : ℍ) :
    ∃ n : ℤ, ((g • w : ℍ) : ℂ) = (w : ℂ) + n := by
  have hdet : g 0 0 * g 1 1 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at h
    exact h
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨-, h1⟩ | ⟨-, h1⟩
  · obtain ⟨n, hn⟩ := GaloisForLFunctions.HTGeometry.coe_smul_eq_coe_smul_add_int_of_bottomRow_eq g 1
      (by simp [hc]) (by simp [h1]) w
    exact ⟨n, by rw [hn, one_smul]⟩
  · obtain ⟨n, hn⟩ := GaloisForLFunctions.HTGeometry.coe_smul_eq_coe_smul_add_int_of_bottomRow_eq g (-1)
      (by simp [hc]) (by simp [h1]) w
    exact ⟨n, by rw [hn, ModularGroup.SL_neg_smul, one_smul]⟩

theorem half_lt_im_of_mem_fd {z : ℍ} (hz : z ∈ ModularGroup.fd) : 1 / 2 < z.im := by
  have h1 : 1 ≤ z.re * z.re + z.im * z.im := by
    have := hz.1
    rw [Complex.normSq_apply] at this
    exact this
  have hre : z.re * z.re ≤ 1 / 4 := by
    have := abs_le.mp hz.2
    nlinarith
  nlinarith [z.im_pos]

theorem mem_fd_of_cusp {z : ℍ} (h1 : 2 < z.im) (h2 : |z.re| < 1 / 2) : z ∈ ModularGroup.fd := by
  constructor
  · rw [Complex.normSq_apply]
    change 1 ≤ z.re * z.re + z.im * z.im
    nlinarith [mul_self_nonneg z.re]
  · exact h2.le

/-! ### The odd cusp profile -/

/-- The height bump of index `k`: smooth, with values in `[0, 1]`, supported in `(2 + 2k, 3 + 2k)`. -/
def heightBump (k : ℕ) : ContDiffBump ((5 / 2 : ℝ) + 2 * k) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

theorem heightBump_eq_zero {k : ℕ} {y : ℝ} (hy : y ≤ 2 + 2 * k ∨ 3 + 2 * k ≤ y) :
    heightBump k y = 0 := by
  refine (heightBump k).zero_of_le_dist ?_
  show (1 / 2 : ℝ) ≤ dist y (5 / 2 + 2 * k)
  rw [Real.dist_eq]
  rcases hy with hy | hy
  · rw [abs_of_neg (by linarith)]
    linarith
  · rw [abs_of_pos (by linarith)]
    linarith

theorem heightBump_center (k : ℕ) : heightBump k ((5 / 2 : ℝ) + 2 * k) = 1 :=
  (heightBump k).one_of_mem_closedBall (Metric.mem_closedBall_self (heightBump k).rIn_pos.le)

theorem contDiff_heightBump (k : ℕ) : ContDiff ℝ 1 (heightBump k) := by
  simpa using (heightBump k).contDiff (n := 1)

/-- Two bumps of different index have disjoint supports. -/
theorem heightBump_mul_eq_zero {j k : ℕ} (hjk : j ≠ k) (y : ℝ) :
    heightBump j y * heightBump k y = 0 := by
  by_contra h
  have hj : heightBump j y ≠ 0 := left_ne_zero_of_mul h
  have hk : heightBump k y ≠ 0 := right_ne_zero_of_mul h
  have hj1 : 2 + 2 * (j : ℝ) < y := by
    by_contra h'
    exact hj (heightBump_eq_zero (Or.inl (not_lt.mp h')))
  have hj2 : y < 3 + 2 * (j : ℝ) := by
    by_contra h'
    exact hj (heightBump_eq_zero (Or.inr (not_lt.mp h')))
  have hk1 : 2 + 2 * (k : ℝ) < y := by
    by_contra h'
    exact hk (heightBump_eq_zero (Or.inl (not_lt.mp h')))
  have hk2 : y < 3 + 2 * (k : ℝ) := by
    by_contra h'
    exact hk (heightBump_eq_zero (Or.inr (not_lt.mp h')))
  rcases Nat.lt_or_gt_of_ne hjk with h | h
  · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
    linarith
  · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast h
    linarith

/-- The odd cusp profile `G_k(w) = ψ_k(Im w) sin(2π Re w)`. -/
def oddProfile (k : ℕ) (w : ℂ) : ℝ := heightBump k w.im * Real.sin (2 * Real.pi * w.re)

theorem oddProfile_eq_zero_of_im_le {k : ℕ} {w : ℂ} (hw : w.im ≤ 2) : oddProfile k w = 0 := by
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  rw [oddProfile, heightBump_eq_zero (Or.inl (by linarith)), zero_mul]

theorem oddProfile_add_int (k : ℕ) (w : ℂ) (n : ℤ) : oddProfile k (w + n) = oddProfile k w := by
  simp only [oddProfile, Complex.add_im, Complex.intCast_im, add_zero, Complex.add_re,
    Complex.intCast_re]
  rw [show 2 * Real.pi * (w.re + n) = 2 * Real.pi * w.re + n * (2 * Real.pi) by ring,
    Real.sin_add_int_mul_two_pi]

theorem oddProfile_mirror (k : ℕ) (w : ℂ) :
    oddProfile k (-(starRingEnd ℂ) w) = -oddProfile k w := by
  simp only [oddProfile, Complex.neg_im, Complex.conj_im, neg_neg, Complex.neg_re, Complex.conj_re,
    mul_neg, Real.sin_neg]

theorem abs_oddProfile_le (k : ℕ) (w : ℂ) : |oddProfile k w| ≤ 1 := by
  rw [oddProfile, abs_mul]
  have h1 : |heightBump k w.im| ≤ 1 := by
    rw [abs_of_nonneg (heightBump k).nonneg]
    exact (heightBump k).le_one
  exact mul_le_one₀ h1 (abs_nonneg _) (Real.abs_sin_le_one _)

theorem contDiff_oddProfile (k : ℕ) : ContDiff ℝ 1 (oddProfile k) :=
  ((contDiff_heightBump k).comp Complex.imCLM.contDiff).mul
    (Real.contDiff_sin.comp (contDiff_const.mul Complex.reCLM.contDiff))

/-- **Well defined.** If `Im w > ½` and `Im g w > ½`, the profile takes the same value at `w` and at `g w`. -/
theorem oddProfile_smul_eq {k : ℕ} (g : SL(2, ℤ)) {w : ℍ} (hw : 1 / 2 < w.im)
    (hgw : 1 / 2 < (g • w).im) : oddProfile k (g • w : ℍ) = oddProfile k w := by
  by_cases hc : g 1 0 = 0
  · obtain ⟨n, hn⟩ := exists_int_of_bottom_zero hc w
    rw [hn, oddProfile_add_int]
  · have h1 : (g • w).im < 2 := im_lt_two_of_ne_zero hc hw
    have hinv : (g⁻¹) 1 0 = -g 1 0 := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
      rfl
    have hc' : (g⁻¹) 1 0 ≠ 0 := by
      rw [hinv]
      exact neg_ne_zero.mpr hc
    have h2 : w.im < 2 := by
      have := im_lt_two_of_ne_zero hc' hgw
      rwa [inv_smul_smul] at this
    rw [oddProfile_eq_zero_of_im_le (by exact h1.le), oddProfile_eq_zero_of_im_le (by exact h2.le)]

/-! ### The odd cusp field -/

/-- A matrix moving `z` into the fundamental domain. -/
def reduceSL (z : ℍ) : SL(2, ℤ) := (ModularGroup.exists_smul_mem_fd z).choose

theorem reduceSL_mem (z : ℍ) : reduceSL z • z ∈ ModularGroup.fd :=
  (ModularGroup.exists_smul_mem_fd z).choose_spec

/-- **The odd cusp field** `F_k(z) = G_k(γ z)`, for any `γ` with `Im γz > ½`. -/
def oddField (k : ℕ) (z : ℍ) : ℝ := oddProfile k (reduceSL z • z : ℍ)

theorem oddField_eq (k : ℕ) {z : ℍ} (g : SL(2, ℤ)) (hg : 1 / 2 < (g • z).im) :
    oddField k z = oddProfile k (g • z : ℍ) := by
  have e : (reduceSL z * g⁻¹) • g • z = reduceSL z • z := by
    rw [smul_smul, inv_mul_cancel_right]
  have hr : 1 / 2 < ((reduceSL z * g⁻¹) • g • z).im := by
    rw [e]
    exact half_lt_im_of_mem_fd (reduceSL_mem z)
  rw [oddField, ← e, oddProfile_smul_eq _ hg hr]

theorem oddField_of_half_lt (k : ℕ) {z : ℍ} (hz : 1 / 2 < z.im) : oddField k z = oddProfile k z := by
  rw [oddField_eq k 1 (by rwa [one_smul]), one_smul]

theorem oddField_smul (k : ℕ) (A : SL(2, ℤ)) (z : ℍ) : oddField k (A • z) = oddField k z := by
  have e : (reduceSL z * A⁻¹) • A • z = reduceSL z • z := by
    rw [smul_smul, inv_mul_cancel_right]
  rw [oddField_eq k (reduceSL z * A⁻¹) (by rw [e]; exact half_lt_im_of_mem_fd (reduceSL_mem z)), e]
  rfl

theorem oddField_mirror (k : ℕ) (z : ℍ) : oddField k (mirror z) = -oddField k z := by
  have e : mirrorSL (reduceSL z) • mirror z = mirror (reduceSL z • z) := (mirror_smul _ _).symm
  rw [oddField_eq k (mirrorSL (reduceSL z))
    (by rw [e, mirror_im]; exact half_lt_im_of_mem_fd (reduceSL_mem z)), e, coe_mirror,
    oddProfile_mirror]
  rfl

/-! ### The odd sector is cuspidal -/

/-- The point `x + iy` of the upper half-plane. -/
def cuspPoint (x y : ℝ) (hy : 0 < y) : ℍ := ⟨⟨x, y⟩, hy⟩

theorem cuspPoint_add_one (x y : ℝ) (hy : 0 < y) :
    cuspPoint (x + 1) y hy = ModularGroup.T • cuspPoint x y hy := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]
  exact Complex.ext (by simp [cuspPoint]; ring) (by simp [cuspPoint])

theorem cuspPoint_neg (x y : ℝ) (hy : 0 < y) : cuspPoint (-x) y hy = mirror (cuspPoint x y hy) := by
  apply UpperHalfPlane.ext
  exact Complex.ext (by simp [cuspPoint]) (by simp [cuspPoint])

/-- A `1`-periodic odd function has zero integral over every period. -/
theorem integral_period_eq_zero_of_odd {f : ℝ → ℂ} (hper : Function.Periodic f 1)
    (hodd : ∀ x, f (-x) = -f x) (a : ℝ) : ∫ x in a..a + 1, f x = 0 := by
  have h1 : ∫ x in a..a + 1, f x = ∫ x in (0 : ℝ)..0 + 1, f x := hper.intervalIntegral_add_eq a 0
  have h2 : ∫ x in (-1 : ℝ)..(-1) + 1, f x = ∫ x in (0 : ℝ)..0 + 1, f x :=
    hper.intervalIntegral_add_eq (-1) 0
  have h3 : ∫ x in (0 : ℝ)..1, f (-x) = ∫ x in (-1 : ℝ)..(-0), f x := intervalIntegral.integral_comp_neg f
  have h4 : ∫ x in (0 : ℝ)..1, f (-x) = -∫ x in (0 : ℝ)..1, f x := by
    simp only [hodd, intervalIntegral.integral_neg]
  rw [h1, zero_add]
  rw [neg_zero] at h3
  rw [show (-1 : ℝ) + 1 = 0 by norm_num, zero_add] at h2
  have h5 : ∫ x in (0 : ℝ)..1, f x = -∫ x in (0 : ℝ)..1, f x := by
    rw [← h4, h3, h2]
  linear_combination h5 / 2

/-- **The odd sector is cuspidal.** A modular function odd under the mirror has zero mean on every
closed horocycle. -/
theorem horocycle_mean_eq_zero_of_odd {f : ℍ → ℂ} (hinv : ∀ (A : SL(2, ℤ)) (z : ℍ), f (A • z) = f z)
    (hodd : ∀ z, f (mirror z) = -f z) {y : ℝ} (hy : 0 < y) (a : ℝ) :
    ∫ x in a..a + 1, f (cuspPoint x y hy) = 0 := by
  refine integral_period_eq_zero_of_odd (f := fun x => f (cuspPoint x y hy)) (fun x => ?_)
    (fun x => ?_) a
  · show f (cuspPoint (x + 1) y hy) = f (cuspPoint x y hy)
    rw [cuspPoint_add_one, hinv]
  · show f (cuspPoint (-x) y hy) = -f (cuspPoint x y hy)
    rw [cuspPoint_neg, hodd]

/-! ### The field as a vector of the level-one deck -/

/-- The odd cusp field as a vector of the level-one deck. -/
def oddVec (k : ℕ) (z : ℍ) : DeckSpace 0 := (oddField k z : ℂ) • onesVec 0

/-- The profile in the chart, as a deck vector. -/
def oddE (k : ℕ) (ζ : ℂ) : DeckSpace 0 := (oddProfile k ζ : ℂ) • onesVec 0

theorem oddVec_of_half_lt (k : ℕ) {z : ℍ} (hz : 1 / 2 < z.im) : oddVec k z = oddE k z := by
  rw [oddVec, oddField_of_half_lt k hz]
  rfl

theorem oddVec_of_mem_fd (k : ℕ) {z : ℍ} (hz : z ∈ ModularGroup.fd) : oddVec k z = oddE k z :=
  oddVec_of_half_lt k (half_lt_im_of_mem_fd hz)

theorem regular_onesVec (g : Deck 0) : GaloisForLFunctions.HTGeometry.finiteRegularUnitary g (onesVec 0) =
    onesVec 0 := by
  ext q
  rw [GaloisForLFunctions.HTGeometry.finiteRegularUnitary_apply]
  rfl

theorem onesVec_ne_zero : onesVec 0 ≠ 0 := by
  intro h
  have := congrArg (fun v : DeckSpace 0 => v (QuotientGroup.mk 1 : Deck 0)) h
  simp [onesVec] at this

theorem deckEquivariant_oddVec (k : ℕ) : deckEquivariant 0 (oddVec k) := by
  intro A z
  rw [oddVec, oddVec, oddField_smul, map_smul, regular_onesVec]

theorem contDiff_complexSmul : ContDiff ℝ 1 fun w : ℂ => w • onesVec 0 :=
  (contDiff_id.smul contDiff_const : ContDiff ℂ 1 fun w : ℂ => id w • onesVec 0).restrict_scalars ℝ

theorem contDiff_oddE (k : ℕ) : ContDiff ℝ 1 (oddE k) :=
  contDiff_complexSmul.comp (Complex.ofRealCLM.contDiff.comp (contDiff_oddProfile k))

theorem continuous_oddE_coe (k : ℕ) : Continuous fun z : ℍ => oddE k z :=
  (contDiff_oddE k).continuous.comp UpperHalfPlane.continuous_coe

/-- The Möbius map of `g` in the complex chart. -/
def mob (g : SL(2, ℤ)) (ζ : ℂ) : ℂ :=
  ((g 0 0 : ℂ) * ζ + (g 0 1 : ℂ)) * ((g 1 0 : ℂ) * ζ + (g 1 1 : ℂ))⁻¹

theorem mob_eq (g : SL(2, ℤ)) {ζ : ℂ} (hζ : 0 < ζ.im) :
    mob g ζ = ((g • UpperHalfPlane.ofComplex ζ : ℍ) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hζ]
  simp [mob, div_eq_mul_inv]

theorem mob_den_ne_zero (g : SL(2, ℤ)) {ζ : ℂ} (hζ : 0 < ζ.im) :
    (g 1 0 : ℂ) * ζ + (g 1 1 : ℂ) ≠ 0 := by
  have h := UpperHalfPlane.denom_ne_zero
    (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g))
    (UpperHalfPlane.ofComplex ζ)
  rw [_root_.RHTower.denom_SL2Z, UpperHalfPlane.ofComplex_apply_of_im_pos hζ] at h
  exact h

theorem contDiffAt_mob (g : SL(2, ℤ)) {ζ : ℂ} (hζ : 0 < ζ.im) : ContDiffAt ℝ 1 (mob g) ζ := by
  unfold mob
  exact ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const).mul
    (((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const).inv (mob_den_ne_zero g hζ))

/-- Near every point the field is the profile composed with one Möbius map. -/
theorem chartFun_oddVec_eventuallyEq (k : ℕ) {ζ₀ : ℂ} (hζ₀ : 0 < ζ₀.im) :
    chartFun (oddVec k) =ᶠ[𝓝 ζ₀] oddE k ∘ mob (reduceSL (UpperHalfPlane.ofComplex ζ₀)) := by
  set g := reduceSL (UpperHalfPlane.ofComplex ζ₀)
  have hg : 1 / 2 < (mob g ζ₀).im := by
    rw [mob_eq g hζ₀]
    exact half_lt_im_of_mem_fd (reduceSL_mem _)
  have hcont : ContinuousAt (fun ζ => (mob g ζ).im) ζ₀ :=
    Complex.continuous_im.continuousAt.comp (contDiffAt_mob g hζ₀).continuousAt
  filter_upwards [continuousAt_const.eventually_lt hcont hg,
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hζ₀] with ζ h1 h2
  have h2' : 0 < ζ.im := h2
  have h1' : 1 / 2 < (g • UpperHalfPlane.ofComplex ζ).im := by
    show 1 / 2 < ((g • UpperHalfPlane.ofComplex ζ : ℍ) : ℂ).im
    rw [← mob_eq g h2']
    exact h1
  show (oddField k (UpperHalfPlane.ofComplex ζ) : ℂ) • onesVec 0 =
    (oddProfile k (mob g ζ) : ℂ) • onesVec 0
  rw [oddField_eq k g h1', ← mob_eq g h2']

theorem isChartC1_oddVec (k : ℕ) : IsChartC1 (oddVec k) := by
  unfold IsChartC1
  intro ζ hζ
  exact (((contDiff_oddE k).contDiffAt.comp ζ (contDiffAt_mob _ hζ)).congr_of_eventuallyEq
    (chartFun_oddVec_eventuallyEq k hζ)).contDiffWithinAt

/-! ### Square integrability -/

/-- A function equal on the modular cell to a bounded continuous one is square integrable there. -/
theorem memLp_of_eqOn_fd {F Φ : ℍ → DeckSpace 0} (hΦ : Continuous Φ) {C : ℝ} (hC : ∀ z, ‖Φ z‖ ≤ C)
    (h : ∀ z ∈ ModularGroup.fd, F z = Φ z) : MemLp F 2 MaassCongruenceL2.cellMeasure := by
  refine (memLp_congr_ae ?_).mpr (MemLp.of_bound hΦ.aestronglyMeasurable C (Eventually.of_forall hC))
  exact (ae_restrict_iff' GaloisForLFunctions.HTGeometry.measurableSet_fd).mpr (Eventually.of_forall h)

theorem memLp_oddVec (k : ℕ) : MemLp (oddVec k) 2 MaassCongruenceL2.cellMeasure := by
  refine memLp_of_eqOn_fd (continuous_oddE_coe k) (C := ‖onesVec 0‖) (fun z => ?_)
    fun z hz => oddVec_of_mem_fd k hz
  rw [oddE, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (abs_oddProfile_le k z)

/-- The derivative of the field along a horocycle, in the chart. -/
theorem fderiv_one_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℂ → F} {ζ : ℂ}
    {L : F} (hf : DifferentiableAt ℝ f ζ) (h : HasDerivAt (fun q : ℝ => f ⟨q, ζ.im⟩) L ζ.re) :
    fderiv ℝ f ζ 1 = L :=
  (hf.hasFDerivAt.comp_hasDerivAt_of_eq ζ.re (hasDerivAt_mk_re ζ.re ζ.im) (Complex.eta ζ).symm).unique h

/-- The derivative of the field in the height, in the chart. -/
theorem fderiv_I_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℂ → F} {ζ : ℂ}
    {L : F} (hf : DifferentiableAt ℝ f ζ) (h : HasDerivAt (fun q : ℝ => f ⟨ζ.re, q⟩) L ζ.im) :
    fderiv ℝ f ζ Complex.I = L :=
  (hf.hasFDerivAt.comp_hasDerivAt_of_eq ζ.im (hasDerivAt_mk_im ζ.re ζ.im) (Complex.eta ζ).symm).unique h

theorem hasDerivAt_oddE_re (k : ℕ) (x y : ℝ) :
    HasDerivAt (fun q : ℝ => oddE k ⟨q, y⟩)
      (((heightBump k y * (Real.cos (2 * Real.pi * x) * (2 * Real.pi)) : ℝ) : ℂ) • onesVec 0) x := by
  have h1 : HasDerivAt (fun q : ℝ => 2 * Real.pi * q) (2 * Real.pi) x := by
    simpa using (hasDerivAt_id x).const_mul (2 * Real.pi)
  exact ((h1.sin.const_mul (heightBump k y)).ofReal_comp).smul_const (onesVec 0)

theorem hasDerivAt_oddE_im (k : ℕ) (x y : ℝ) :
    HasDerivAt (fun q : ℝ => oddE k ⟨x, q⟩)
      (((deriv (heightBump k) y * Real.sin (2 * Real.pi * x) : ℝ) : ℂ) • onesVec 0) y := by
  have h1 : HasDerivAt (heightBump k) (deriv (heightBump k) y) y :=
    ((contDiff_heightBump k).differentiable one_ne_zero y).hasDerivAt
  exact ((h1.mul_const (Real.sin (2 * Real.pi * x))).ofReal_comp).smul_const (onesVec 0)

/-- Above height `½` the field is the profile in the chart. -/
theorem chartFun_oddVec_eq_oddE (k : ℕ) {ζ : ℂ} (hζ : 1 / 2 < ζ.im) :
    chartFun (oddVec k) =ᶠ[𝓝 ζ] oddE k := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hζ] with w hw
  have hw' : 1 / 2 < w.im := hw
  have hw0 : 0 < w.im := by linarith
  have e : ((UpperHalfPlane.ofComplex w : ℍ) : ℂ) = w := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw0]
  have him : 1 / 2 < (UpperHalfPlane.ofComplex w).im := by
    show 1 / 2 < ((UpperHalfPlane.ofComplex w : ℍ) : ℂ).im
    rw [e]
    exact hw'
  show oddVec k (UpperHalfPlane.ofComplex w) = oddE k w
  rw [oddVec_of_half_lt k him, e]

theorem hypGradX_oddVec (k : ℕ) {z : ℍ} (hz : 1 / 2 < z.im) :
    hypGradX (oddVec k) z = ((z.im * (heightBump k z.im *
      (Real.cos (2 * Real.pi * z.re) * (2 * Real.pi))) : ℝ) : ℂ) • onesVec 0 := by
  have hE := chartFun_oddVec_eq_oddE k (show 1 / 2 < (z : ℂ).im from hz)
  have hd := fderiv_one_eq ((contDiff_oddE k).differentiable one_ne_zero (z : ℂ))
    (hasDerivAt_oddE_re k (z : ℂ).re (z : ℂ).im)
  rw [hypGradX, chartDeriv, hE.fderiv_eq, hd, smul_smul, ← Complex.ofReal_mul]
  rfl

theorem hypGradY_oddVec (k : ℕ) {z : ℍ} (hz : 1 / 2 < z.im) :
    hypGradY (oddVec k) z = ((z.im * (deriv (heightBump k) z.im *
      Real.sin (2 * Real.pi * z.re)) : ℝ) : ℂ) • onesVec 0 := by
  have hE := chartFun_oddVec_eq_oddE k (show 1 / 2 < (z : ℂ).im from hz)
  have hd := fderiv_I_eq ((contDiff_oddE k).differentiable one_ne_zero (z : ℂ))
    (hasDerivAt_oddE_im k (z : ℂ).re (z : ℂ).im)
  rw [hypGradY, chartDeriv, hE.fderiv_eq, hd, smul_smul, ← Complex.ofReal_mul]
  rfl

theorem exists_bound_mul {φ : ℝ → ℝ} (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    ∃ C, ∀ y : ℝ, |y * φ y| ≤ C := by
  obtain ⟨C, hC⟩ := Continuous.bounded_above_of_compact_support (f := (fun y : ℝ => y) * φ)
    (continuous_id.mul hφ) hs.mul_left
  exact ⟨C, fun y => by simpa using hC y⟩

theorem memLp_hypGradX_oddVec (k : ℕ) : MemLp (hypGradX (oddVec k)) 2 MaassCongruenceL2.cellMeasure := by
  obtain ⟨C, hC⟩ := exists_bound_mul (heightBump k).continuous (heightBump k).hasCompactSupport
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  refine memLp_of_eqOn_fd (Φ := fun z : ℍ => ((z.im * (heightBump k z.im *
      (Real.cos (2 * Real.pi * z.re) * (2 * Real.pi))) : ℝ) : ℂ) • onesVec 0)
    ((Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_im.mul
      (((heightBump k).continuous.comp UpperHalfPlane.continuous_im).mul
        ((Real.continuous_cos.comp (continuous_const.mul UpperHalfPlane.continuous_re)).mul
          continuous_const)))).smul continuous_const)
    (C := C * (2 * Real.pi) * ‖onesVec 0‖) (fun z => ?_)
    fun z hz => hypGradX_oddVec k (half_lt_im_of_mem_fd hz)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have e : z.im * (heightBump k z.im * (Real.cos (2 * Real.pi * z.re) * (2 * Real.pi))) =
      z.im * heightBump k z.im * Real.cos (2 * Real.pi * z.re) * (2 * Real.pi) := by ring
  rw [e, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  calc |z.im * heightBump k z.im| * |Real.cos (2 * Real.pi * z.re)| * (2 * Real.pi) * ‖onesVec 0‖
      ≤ C * 1 * (2 * Real.pi) * ‖onesVec 0‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul (hC _) (Real.abs_cos_le_one _) (abs_nonneg _) hC0) (by positivity))
          (norm_nonneg _)
    _ = C * (2 * Real.pi) * ‖onesVec 0‖ := by ring

theorem memLp_hypGradY_oddVec (k : ℕ) : MemLp (hypGradY (oddVec k)) 2 MaassCongruenceL2.cellMeasure := by
  have hd := (contDiff_heightBump k).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := exists_bound_mul hd (heightBump k).hasCompactSupport.deriv
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  refine memLp_of_eqOn_fd (Φ := fun z : ℍ => ((z.im * (deriv (heightBump k) z.im *
      Real.sin (2 * Real.pi * z.re)) : ℝ) : ℂ) • onesVec 0)
    ((Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_im.mul
      ((hd.comp UpperHalfPlane.continuous_im).mul
        (Real.continuous_sin.comp (continuous_const.mul UpperHalfPlane.continuous_re))))).smul
      continuous_const)
    (C := C * ‖onesVec 0‖) (fun z => ?_) fun z hz => hypGradY_oddVec k (half_lt_im_of_mem_fd hz)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have e : z.im * (deriv (heightBump k) z.im * Real.sin (2 * Real.pi * z.re)) =
      z.im * deriv (heightBump k) z.im * Real.sin (2 * Real.pi * z.re) := by ring
  rw [e, abs_mul]
  calc |z.im * deriv (heightBump k) z.im| * |Real.sin (2 * Real.pi * z.re)| * ‖onesVec 0‖
      ≤ C * 1 * ‖onesVec 0‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (Real.abs_sin_le_one _) (abs_nonneg _) hC0)
          (norm_nonneg _)
    _ = C * ‖onesVec 0‖ := by ring

/-! ### Vectors of the cuspidal form domain -/

theorem levelCuspZero_oddVec (k : ℕ) : levelCuspZero 0 (oddVec k) := by
  intro q y hy a
  have hval : ∀ x : ℝ, oddVec k (UpperHalfPlane.ofComplex (SelbergMaassMean.point x y)) q =
      (oddField k (cuspPoint x y hy) : ℂ) := by
    intro x
    rw [chart_point, UpperHalfPlane.ofComplex_apply_of_im_pos (show (0 : ℝ) < (⟨x, y⟩ : ℂ).im from hy)]
    show ((oddField k (cuspPoint x y hy) : ℂ) • onesVec 0) q = _
    simp [onesVec]
  simp only [hval]
  rw [show a + (((0 : ℕ) + 1 : ℕ) : ℝ) = a + 1 by norm_num]
  exact horocycle_mean_eq_zero_of_odd (f := fun z => (oddField k z : ℂ))
    (fun A z => by simp only [oddField_smul]) (fun z => by simp only [oddField_mirror, Complex.ofReal_neg])
    hy a

/-- The odd cusp field in the form pre-domain. -/
def oddPre (k : ℕ) : formPreDomain 0 :=
  ⟨oddVec k, isChartC1_oddVec k, deckEquivariant_oddVec k, memLp_oddVec k, memLp_hypGradX_oddVec k,
    memLp_hypGradY_oddVec k⟩

/-- The odd cusp field in the cusp-zero pre-domain. -/
def oddCusp (k : ℕ) : cuspidalFormPreDomain 0 := ⟨oddVec k, (oddPre k).property, levelCuspZero_oddVec k⟩

/-- The odd cusp field as a cuspidal `L²` vector. -/
def oddL2 (k : ℕ) : CuspidalL2 0 := cuspidalFormInclusionClosure 0 (toCuspidalFormDomain 0 (oddCusp k))

theorem coe_oddL2 (k : ℕ) : (oddL2 k : DeckL2 0) = toDeckL2 (oddVec k) (memLp_oddVec k) := rfl

/-- A point of the cusp where the field of index `k` is the unit vector. -/
def oddPeak (k : ℕ) : ℍ := ⟨⟨1 / 4, 5 / 2 + 2 * k⟩, by show (0 : ℝ) < 5 / 2 + 2 * k; positivity⟩

theorem oddProfile_oddPeak (k : ℕ) : oddProfile k (oddPeak k) = 1 := by
  show heightBump k (5 / 2 + 2 * k) * Real.sin (2 * Real.pi * (1 / 4)) = 1
  rw [heightBump_center, show 2 * Real.pi * (1 / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two,
    one_mul]

theorem toDeckL2_oddVec_ne_zero (k : ℕ) : toDeckL2 (oddVec k) (memLp_oddVec k) ≠ 0 := by
  intro h0
  have h2 : (⇑(toDeckL2 (oddVec k) (memLp_oddVec k)) : ℍ → DeckSpace 0) =ᵐ[MaassCongruenceL2.cellMeasure] 0 := by
    rw [h0]
    exact Lp.coeFn_zero _ _ _
  have hae : oddVec k =ᵐ[MaassCongruenceL2.cellMeasure] 0 := (memLp_oddVec k).coeFn_toLp.symm.trans h2
  set V : Set ℍ := {z | 2 < z.im ∧ |z.re| < 1 / 2}
  have hVo : IsOpen V := (isOpen_lt continuous_const UpperHalfPlane.continuous_im).inter
    (isOpen_lt (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const)
  have hVfd : V ⊆ ModularGroup.fd := fun z hz => mem_fd_of_cusp hz.1 hz.2
  have hV : oddVec k =ᵐ[volume.restrict V] 0 := ae_restrict_of_ae_restrict_of_subset hVfd hae
  have hc : ContinuousOn (oddVec k) V :=
    (continuous_oddE_coe k).continuousOn.congr fun z hz => oddVec_of_half_lt k (by linarith [hz.1])
  have heq := Measure.eqOn_open_of_ae_eq hV hVo hc continuousOn_const
  have hpk : oddPeak k ∈ V := by
    refine ⟨?_, ?_⟩
    · show (2 : ℝ) < 5 / 2 + 2 * k
      have : (0 : ℝ) ≤ k := k.cast_nonneg
      linarith
    · show |(1 / 4 : ℝ)| < 1 / 2
      rw [abs_of_pos (by norm_num)]
      norm_num
  have h1 := heq hpk
  rw [oddVec_of_half_lt k (by linarith [hpk.1]), oddE, oddProfile_oddPeak] at h1
  exact onesVec_ne_zero (by simpa using h1)

theorem oddL2_ne_zero (k : ℕ) : oddL2 k ≠ 0 := fun h =>
  toDeckL2_oddVec_ne_zero k (by rw [← coe_oddL2, h]; rfl)

/-- **Different indices are orthogonal**: their supports on the modular cell are disjoint. -/
theorem inner_oddL2 {j k : ℕ} (hjk : j ≠ k) : ⟪oddL2 j, oddL2 k⟫_ℂ = 0 := by
  rw [Submodule.coe_inner, coe_oddL2, coe_oddL2, MeasureTheory.L2.inner_def]
  simp only [toDeckL2]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [(memLp_oddVec j).coeFn_toLp, (memLp_oddVec k).coeFn_toLp,
    ae_restrict_mem GaloisForLFunctions.HTGeometry.measurableSet_fd] with z h1 h2 hz
  rw [h1, h2, oddVec_of_mem_fd j hz, oddVec_of_mem_fd k hz, oddE, oddE, inner_smul_left,
    inner_smul_right]
  have h0 : oddProfile j z * oddProfile k z = 0 := by
    unfold oddProfile
    calc _ = (heightBump j (z : ℂ).im * heightBump k (z : ℂ).im) *
          (Real.sin (2 * Real.pi * (z : ℂ).re) * Real.sin (2 * Real.pi * (z : ℂ).re)) := by ring
      _ = 0 := by rw [heightBump_mul_eq_zero hjk, zero_mul]
  rcases mul_eq_zero.mp h0 with h | h <;> simp [h]

end OddCusp

open OddCusp

/-! ### The cusp forms exist -/

/-- **The level-one cuspidal eigenbasis is infinite.** -/
theorem infinite_cuspEigenIndex : Infinite (CuspEigenIndex 0) := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  haveI := hfin
  set b := cuspEigenBasis 0
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range b)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
  have htop : Submodule.span ℂ (Set.range b) = ⊤ := by
    have h := b.dense_span
    rwa [(Submodule.span ℂ (Set.range b)).closed_of_finiteDimensional.submodule_topologicalClosure_eq]
      at h
  have hli : LinearIndependent ℂ oddL2 :=
    linearIndependent_of_ne_zero_of_inner_eq_zero oddL2_ne_zero fun j k hjk => inner_oddL2 hjk
  have hli' : LinearIndependent ℂ (fun k => (⟨oddL2 k, by rw [htop]; exact Submodule.mem_top⟩ :
      Submodule.span ℂ (Set.range b))) :=
    LinearIndependent.of_comp (Submodule.span ℂ (Set.range b)).subtype hli
  exact (not_finite_iff_infinite.mpr (inferInstance : Infinite ℕ)) hli'.finite

/-- **Infinitely many distinct cuspidal Laplace eigenvalues at level one.** Each eigenvalue has a
finite-dimensional eigenspace, so an infinite basis needs infinitely many of them. -/
theorem infinite_cuspEigenvalues : (Set.range (Sigma.fst : CuspEigenIndex 0 → ℝ)).Infinite := by
  intro hfin
  have hfib : ∀ l ∈ Set.range (Sigma.fst : CuspEigenIndex 0 → ℝ),
      (Sigma.fst ⁻¹' {l} : Set (CuspEigenIndex 0)).Finite := by
    intro l _
    refine (Set.finite_range fun x : Fin (Module.finrank ℂ (eigenClassSpace 0 l)) =>
      (⟨l, x⟩ : CuspEigenIndex 0)).subset ?_
    rintro ⟨l', x⟩ hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨x, rfl⟩
  have h := hfin.preimage' hfib
  rw [Set.preimage_range] at h
  exact (Set.infinite_univ_iff.mpr infinite_cuspEigenIndex) h

/-- **The modular black hole rings forever in infinitely many tones.** There are infinitely many
cuspidal eigenvalues, each at least `¼`, and each element of the basis is a nonzero cusp form whose two
branches solve the modular wave equation, undamped beyond the rate of the boundary condition. -/
theorem infinite_undamped_tones :
    (Set.range (Sigma.fst : CuspEigenIndex 0 → ℝ)).Infinite ∧
      ∀ i : CuspEigenIndex 0, 1 / 4 ≤ i.1 ∧ ∃ (U : ℍ → DeckSpace 0) (hU : IsCuspLaplaceEigen 0 i.1 U),
        toDeckL2 U hU.memLp ≠ 0 ∧ (∀ q : Deck 0, IsModularWave (cuspMode U q (cuspFrequency i.1))) ∧
          ∀ q : Deck 0, IsModularWave (cuspMode U q (-cuspFrequency i.1)) := by
  refine ⟨infinite_cuspEigenvalues, fun i => ⟨one_quarter_le_cuspEigenBasis i, ?_⟩⟩
  obtain ⟨U, hU, hb, h1, h2, -⟩ := exists_cuspEigenBasis_modes i
  refine ⟨U, hU, ?_, h1, h2⟩
  rw [← hb]
  intro h0
  have h1' := (cuspEigenBasis 0).orthonormal.1 i
  rw [show (cuspEigenBasis 0 i : CuspidalL2 0) = 0 from Subtype.ext h0, norm_zero] at h1'
  exact zero_ne_one h1'

/-- **Maass cusp forms for `SL₂(ℤ)` exist.** -/
theorem exists_maassCuspForm :
    ∃ (lam : ℝ) (U : ℍ → DeckSpace 0) (hU : IsCuspLaplaceEigen 0 lam U),
      toDeckL2 U hU.memLp ≠ 0 ∧ 1 / 4 ≤ lam := by
  obtain ⟨i⟩ : Nonempty (CuspEigenIndex 0) := infinite_cuspEigenIndex.nonempty
  obtain ⟨hq, U, hU, h0, -, -⟩ := infinite_undamped_tones.2 i
  exact ⟨i.1, U, hU, h0, hq⟩

end GaloisForLFunctions.BlackHoleRingdown
