import GaloisForLFunctions.BlackHoleRingdown.TheWeylKernel
import GaloisForLFunctions.BlackHoleRingdown.TheOddSectorIsACavity
import GaloisForLFunctions.RHTower.RepPointPairTopEigen

/-!
# A Weyl lower bound for the cusp spectrum of the modular horizon

**The count.** There are `C, c > 0` with `N(Λ) ≥ cΛ` for `Λ ≥ C` (`weyl_lower_bound`), where `N(Λ)`
counts the level-one cusp forms of eigenvalue at most `Λ` with multiplicity. Already the mirror-odd
sector gives this many.

**The mechanism.** Place `18n²` Euclidean discs of radius `1/(40n)` on a grid in the interior of the
modular cell, with their mirror images. Each odd pair of indicators is cuspidal (the odd sector is a
cavity). For the narrow kernel `φ_R`, `R ≍ n⁻²`, the point-pair operator acts on a disc as the local
convolution, since a matrix moving an interior point within the kernel range of another one acts
trivially (`smul_eq_self_of_pairU`). On the inner half of each disc the convolution of the indicator
is the mass `m` of the kernel. So the quadratic form is at least `m/16` times the norm on the span of
the `18n²` test vectors (`form_ge_on_span`), and by min–max at least `18n²` basis vectors have kernel
eigenvalue `≥ m/16`. A kernel eigenvalue `κ` and the Laplace eigenvalue `λ` satisfy `λ|κ| ≤ ‖Dφ‖₁ ≤ A`,
so these basis vectors have `λ ≤ 16A/m ≲ n²` (`count_ge_grid`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped MatrixGroups UpperHalfPlane InnerProductSpace ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.DeckPointPair
  MaassFiniteDeckDirichlet SelbergMaassCongruenceTrace OddCusp OddSector
open GaloisForLFunctions.HTGeometry (pairU)

namespace WeylBound

/-! ### The working region of the cell -/

/-- The region `1/10 ≤ |Re z| ≤ 2/5`, `6/5 ≤ Im z ≤ 9/5`, deep inside the modular cell. -/
def region : Set ℍ := {z | 1 / 10 ≤ |z.re| ∧ |z.re| ≤ 2 / 5 ∧ 6 / 5 ≤ z.im ∧ z.im ≤ 9 / 5}

theorem abs_re_sub_le (z w : ℍ) : |z.re - w.re| ≤ dist (z : ℂ) (w : ℂ) := by
  rw [Complex.dist_eq]
  have := Complex.abs_re_le_norm ((z : ℂ) - w)
  simpa using this

theorem abs_im_sub_le (z w : ℍ) : |z.im - w.im| ≤ dist (z : ℂ) (w : ℂ) := by
  rw [Complex.dist_eq]
  have := Complex.abs_im_le_norm ((z : ℂ) - w)
  simpa using this

/-- Points within `1/20` of the region lie in the open modular cell. -/
theorem mem_fdo_of_near {z w : ℍ} (hz : z ∈ region) (hd : dist (z : ℂ) (w : ℂ) ≤ 1 / 20) :
    w ∈ ModularGroup.fdo := by
  obtain ⟨-, h2, h3, -⟩ := hz
  have hre := abs_re_sub_le z w
  have him := abs_im_sub_le z w
  rw [abs_le] at hre him
  constructor
  · rw [Complex.normSq_apply]
    change 1 < w.re * w.re + w.im * w.im
    nlinarith [mul_self_nonneg w.re]
  · rw [abs_lt]
    rw [abs_le] at h2
    constructor <;> linarith

/-- A small `u(z, w)` forces `|z - w|² ≤ 32 u`-closeness for heights at most `2`. -/
theorem dist_sq_le_of_pairU {z w : ℍ} {R : ℝ} (hR : R ≤ 1 / 32) (hz : z.im ≤ 2)
    (hu : pairU z w ≤ R) : dist (z : ℂ) (w : ℂ) ^ 2 ≤ 32 * R := by
  have ha := z.im_pos
  have hb := w.im_pos
  have hR0 : 0 ≤ R := le_trans (by unfold pairU; positivity) hu
  have hd : dist (z : ℂ) (w : ℂ) ^ 2 ≤ 4 * R * z.im * w.im := by
    unfold pairU at hu
    rw [div_le_iff₀ (by positivity)] at hu
    linarith
  have him := abs_im_sub_le z w
  have hsq : (z.im - w.im) ^ 2 ≤ dist (z : ℂ) (w : ℂ) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) him 2
  have h8 : 4 * R * z.im * w.im ≤ z.im * w.im / 8 := by nlinarith [mul_pos ha hb]
  have hwb : w.im < 2 * z.im := by nlinarith
  calc dist (z : ℂ) (w : ℂ) ^ 2 ≤ 4 * R * z.im * w.im := hd
    _ ≤ 4 * R * 2 * 4 := by
        have : z.im * w.im ≤ 2 * 4 := by nlinarith
        nlinarith
    _ = 32 * R := by ring

theorem deckRho_zero_apply (g : SL(2, ℤ)) (v : DeckSpace 0) : deckRho 0 g v = v := by
  ext q
  rw [deckRho_apply, Subsingleton.elim (q * _) q]

theorem one_ne_neg_one_SL : (1 : SL(2, ℤ)) ≠ -1 := by
  intro h
  have := congrArg (fun g : SL(2, ℤ) => g 0 0) h
  simp at this

/-- **A matrix moving a point of the region within the kernel range of another acts trivially.** -/
theorem smul_eq_self_of_pairU {z z' : ℍ} (hz : z ∈ region) (hz' : z' ∈ region) {B : SL(2, ℤ)}
    {R : ℝ} (hR : R ≤ 1 / 12800) (hu : pairU z (B • z') ≤ R) : B = 1 ∨ B = -1 := by
  have hd := dist_sq_le_of_pairU (by linarith) (by linarith [hz.2.2.2]) hu
  have hd' : dist (z : ℂ) ((B • z' : ℍ) : ℂ) ≤ 1 / 20 := by
    have h1 : dist (z : ℂ) ((B • z' : ℍ) : ℂ) ^ 2 ≤ (1 / 20) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ dist_nonneg (by norm_num) (by norm_num)).1 h1
  have hB : B • z' ∈ ModularGroup.fdo := mem_fdo_of_near hz hd'
  have hz'o : z' ∈ ModularGroup.fdo := mem_fdo_of_near hz' (by simp)
  exact ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo hz'o hB

/-- **The kernel acts locally on data supported in the region.** -/
theorem ppApply_eq_local {φ : ℝ → ℝ} {R : ℝ} (hR : R ≤ 1 / 12800) (hφR : KernelSupport φ R)
    {F : ℍ → DeckSpace 0} (hF : ∀ z', z' ∉ region → F z' = 0) {z : ℍ} (hz : z ∈ region) :
    ppApply φ F z = ∫ z' in ModularGroup.fd, ((φ (pairU z z') : ℝ) : ℂ) • F z' := by
  unfold ppApply
  have hzero : ∀ B ∉ ({1, -1} : Finset SL(2, ℤ)), ppTerm φ F z B = 0 := by
    intro B hB
    unfold ppTerm
    refine integral_eq_zero_of_ae (Eventually.of_forall fun z' => ?_)
    show ((φ (pairU z (B • z')) : ℝ) : ℂ) • deckRho 0 B (F z') = 0
    by_cases hz' : z' ∈ region
    · have hlt : R < pairU z (B • z') := by
        by_contra hle
        push Not at hle
        rcases smul_eq_self_of_pairU hz hz' hR hle with h | h <;> simp [h] at hB
      rw [hφR _ hlt]
      simp
    · simp [hF z' hz']
  rw [tsum_eq_sum hzero, Finset.sum_pair one_ne_neg_one_SL]
  have h1 : ppTerm φ F z 1 = ∫ z' in ModularGroup.fd, ((φ (pairU z z') : ℝ) : ℂ) • F z' := by
    unfold ppTerm
    simp [deckRho_zero_apply]
  have h2 : ppTerm φ F z (-1) = ∫ z' in ModularGroup.fd, ((φ (pairU z z') : ℝ) : ℂ) • F z' := by
    unfold ppTerm
    refine integral_congr_ae (Eventually.of_forall fun z' => ?_)
    simp only [ModularGroup.SL_neg_smul, one_smul, deckRho_zero_apply]
  rw [h1, h2, ← two_smul ℂ, smul_smul]
  norm_num

/-! ### Volumes of discs in the region -/

theorem volume_le_of_im_ge_one {s : Set ℍ} (hs : ∀ w ∈ s, 1 ≤ w.im) :
    (volume : Measure ℍ) s ≤ volume (UpperHalfPlane.coe '' s) := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  calc ∫⁻ z : ℂ in UpperHalfPlane.coe '' s, ((1 / ‖z.im‖₊) ^ 2 : ℝ≥0)
      ≤ ∫⁻ z : ℂ in UpperHalfPlane.coe '' s, (1 : ℝ≥0∞) := by
        refine setLIntegral_mono measurable_const fun z hz => ?_
        obtain ⟨w, hw, rfl⟩ := hz
        have h1 : (1 : ℝ) ≤ (w : ℂ).im := hs w hw
        have h2 : ((1 / ‖(w : ℂ).im‖₊) ^ 2 : ℝ≥0) ≤ 1 := by
          rw [← NNReal.coe_le_coe]
          push_cast
          rw [Real.norm_eq_abs, abs_of_pos (by linarith), div_pow, one_pow, div_le_iff₀ (by positivity)]
          nlinarith
        exact_mod_cast h2
    _ = volume (UpperHalfPlane.coe '' s) := by rw [setLIntegral_const, one_mul]

/-- The preimage in `ℍ` of a closed Euclidean disc. -/
def ball (c : ℂ) (r : ℝ) : Set ℍ := UpperHalfPlane.coe ⁻¹' Metric.closedBall c r

theorem measurableSet_ball (c : ℂ) (r : ℝ) : MeasurableSet (ball c r) :=
  (Metric.isClosed_closedBall.preimage UpperHalfPlane.continuous_coe).measurableSet

theorem image_ball {c : ℂ} {r : ℝ} (h : r < c.im) :
    UpperHalfPlane.coe '' ball c r = Metric.closedBall c r := by
  refine Set.image_preimage_eq_of_subset fun z hz => ?_
  have him := Complex.abs_im_le_norm (z - c)
  rw [Metric.mem_closedBall, Complex.dist_eq] at hz
  simp only [Complex.sub_im] at him
  have hpos : 0 < z.im := by rw [abs_le] at him; linarith
  exact ⟨⟨z, hpos⟩, rfl⟩

theorem im_bounds_ball {c : ℂ} {r : ℝ} {w : ℍ} (hw : w ∈ ball c r) :
    c.im - r ≤ w.im ∧ w.im ≤ c.im + r := by
  have him := Complex.abs_im_le_norm ((w : ℂ) - c)
  have hw' : ‖(w : ℂ) - c‖ ≤ r := by
    have := hw
    change (w : ℂ) ∈ Metric.closedBall c r at this
    rwa [Metric.mem_closedBall, Complex.dist_eq] at this
  simp only [Complex.sub_im] at him
  rw [abs_le] at him
  exact ⟨by change c.im - r ≤ (w : ℂ).im; linarith, by change (w : ℂ).im ≤ c.im + r; linarith⟩

theorem volume_ball_le {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (h1 : 1 + r ≤ c.im) :
    (volume : Measure ℍ) (ball c r) ≤ ENNReal.ofReal (Real.pi * r ^ 2) := by
  refine (volume_le_of_im_ge_one fun w hw => by linarith [(im_bounds_ball hw).1]).trans ?_
  rw [image_ball (by linarith), Complex.volume_closedBall, ← ENNReal.ofReal_pow hr,
    ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity), mul_comm]

theorem volume_ball_ge {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (h1 : r < c.im) (h2 : c.im + r ≤ 2) :
    ENNReal.ofReal (Real.pi * r ^ 2 / 4) ≤ (volume : Measure ℍ) (ball c r) := by
  refine le_trans ?_ (volume_ge_of_im_le fun w hw => by linarith [(im_bounds_ball hw).2])
  rw [image_ball h1, Complex.volume_closedBall, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_coe_nnreal,
    NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity),
    show (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4) by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp,
    ← ENNReal.ofReal_mul (by norm_num)]
  exact le_of_eq (by congr 1; ring)

/-! ### The test discs -/

variable {n : ℕ}

/-- The centre of the test disc of index `(i, j)`. -/
def center (n : ℕ) (k : Fin (3 * n) × Fin (6 * n)) : ℂ :=
  ⟨1 / 10 + ((k.1 : ℝ) + 1 / 2) / (10 * n), 6 / 5 + ((k.2 : ℝ) + 1 / 2) / (10 * n)⟩

/-- The radius of a test disc. -/
def radius (n : ℕ) : ℝ := 1 / (40 * n)

/-- The test disc and its mirror image. -/
def discP (n : ℕ) (k : Fin (3 * n) × Fin (6 * n)) : Set ℍ := ball (center n k) (radius n)
def discM (n : ℕ) (k : Fin (3 * n) × Fin (6 * n)) : Set ℍ :=
  ball (-(starRingEnd ℂ) (center n k)) (radius n)

/-- The inner discs, of half the radius. -/
def innerP (n : ℕ) (k : Fin (3 * n) × Fin (6 * n)) : Set ℍ := ball (center n k) (radius n / 2)
def innerM (n : ℕ) (k : Fin (3 * n) × Fin (6 * n)) : Set ℍ :=
  ball (-(starRingEnd ℂ) (center n k)) (radius n / 2)

theorem re_bounds_ball {c : ℂ} {r : ℝ} {w : ℍ} (hw : w ∈ ball c r) :
    c.re - r ≤ w.re ∧ w.re ≤ c.re + r := by
  have hre := Complex.abs_re_le_norm ((w : ℂ) - c)
  have hw' : ‖(w : ℂ) - c‖ ≤ r := by
    have := hw
    change (w : ℂ) ∈ Metric.closedBall c r at this
    rwa [Metric.mem_closedBall, Complex.dist_eq] at this
  simp only [Complex.sub_re] at hre
  rw [abs_le] at hre
  exact ⟨by change c.re - r ≤ (w : ℂ).re; linarith, by change (w : ℂ).re ≤ c.re + r; linarith⟩

theorem mirror_region {w : ℍ} (hw : w ∈ region) : mirror w ∈ region := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  have e1 : (mirror w).re = -w.re := by
    show (-(starRingEnd ℂ) (w : ℂ)).re = -(w : ℂ).re
    simp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [e1, abs_neg, mirror_im] <;> assumption

theorem dist_mirror (z w : ℍ) : dist ((mirror z : ℍ) : ℂ) ((mirror w : ℍ) : ℂ) = dist (z : ℂ) (w : ℂ) := by
  rw [coe_mirror, coe_mirror, dist_neg_neg, Complex.dist_conj_conj]

theorem mem_discM_iff {k : Fin (3 * n) × Fin (6 * n)} {w : ℍ} : w ∈ discM n k ↔ mirror w ∈ discP n k := by
  change (w : ℂ) ∈ Metric.closedBall _ _ ↔ ((mirror w : ℍ) : ℂ) ∈ Metric.closedBall _ _
  rw [coe_mirror, Metric.mem_closedBall, Metric.mem_closedBall, Complex.dist_eq, Complex.dist_eq]
  rw [show -(starRingEnd ℂ) (w : ℂ) - center n k = -(starRingEnd ℂ) ((w : ℂ) - -(starRingEnd ℂ) (center n k)) by
    simp; ring]
  rw [norm_neg, Complex.norm_conj]

section Geometry

variable (hn : 1 ≤ n)
include hn

theorem n_pos : (0 : ℝ) < n := by exact_mod_cast hn

theorem center_re_bounds (k : Fin (3 * n) × Fin (6 * n)) :
    1 / 10 + 1 / (20 * n) ≤ (center n k).re ∧ (center n k).re ≤ 2 / 5 - 1 / (20 * n) := by
  have hn' := n_pos hn
  have hk : (k.1 : ℝ) + 1 ≤ 3 * n := by
    have := k.1.2
    have : (k.1 : ℕ) + 1 ≤ 3 * n := this
    exact_mod_cast this
  have hk0 : (0 : ℝ) ≤ k.1 := Nat.cast_nonneg _
  simp only [center]
  constructor
  · rw [show (1 : ℝ) / (20 * n) = (0 + 1 / 2) / (10 * n) by field_simp; ring]
    gcongr
  · have : ((k.1 : ℝ) + 1 / 2) / (10 * n) ≤ 3 / 10 - 1 / (20 * n) := by
      rw [div_le_iff₀ (by positivity)]
      field_simp
      nlinarith
    linarith

theorem center_im_bounds (k : Fin (3 * n) × Fin (6 * n)) :
    6 / 5 + 1 / (20 * n) ≤ (center n k).im ∧ (center n k).im ≤ 9 / 5 - 1 / (20 * n) := by
  have hn' := n_pos hn
  have hk : (k.2 : ℝ) + 1 ≤ 6 * n := by
    have := k.2.2
    have : (k.2 : ℕ) + 1 ≤ 6 * n := this
    exact_mod_cast this
  have hk0 : (0 : ℝ) ≤ k.2 := Nat.cast_nonneg _
  simp only [center]
  constructor
  · rw [show (1 : ℝ) / (20 * n) = (0 + 1 / 2) / (10 * n) by field_simp; ring]
    gcongr
  · have : ((k.2 : ℝ) + 1 / 2) / (10 * n) ≤ 3 / 5 - 1 / (20 * n) := by
      rw [div_le_iff₀ (by positivity)]
      field_simp
      nlinarith
    linarith

theorem radius_pos : 0 < radius n := by unfold radius; have := n_pos hn; positivity

theorem two_radius_eq : 2 * radius n = 1 / (20 * n) := by unfold radius; field_simp; ring

theorem discP_subset (k : Fin (3 * n) × Fin (6 * n)) : discP n k ⊆ region := by
  intro w hw
  obtain ⟨h1, h2⟩ := re_bounds_ball hw
  obtain ⟨h3, h4⟩ := im_bounds_ball hw
  obtain ⟨c1, c2⟩ := center_re_bounds hn k
  obtain ⟨c3, c4⟩ := center_im_bounds hn k
  have hr : radius n ≤ 1 / (20 * n) := by
    have := two_radius_eq hn
    have := radius_pos hn
    linarith
  have hre0 : 0 ≤ w.re := by
    have := n_pos hn
    have h20 : 0 < 1 / (20 * (n : ℝ)) := by positivity
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [abs_of_nonneg hre0]; linarith
  · rw [abs_of_nonneg hre0]; linarith
  · linarith
  · linarith

theorem discM_subset (k : Fin (3 * n) × Fin (6 * n)) : discM n k ⊆ region := by
  intro w hw
  have h := mirror_region (discP_subset hn k (mem_discM_iff.1 hw))
  rwa [mirror_mirror] at h

end Geometry

/-! ### Separation of the discs -/

section Separation

variable (hn : 1 ≤ n)
include hn

/-- The grid index of a point near a test disc. -/
theorem floor_eq_of_near {k : Fin (3 * n) × Fin (6 * n)} {z w : ℍ} (hz : z ∈ discP n k)
    (hd : dist (z : ℂ) (w : ℂ) ≤ 1 / (80 * n)) :
    ⌊(w.re - 1 / 10) * (10 * n)⌋₊ = k.1 ∧ ⌊(w.im - 6 / 5) * (10 * n)⌋₊ = k.2 := by
  have hn' := n_pos hn
  obtain ⟨h1, h2⟩ := re_bounds_ball hz
  obtain ⟨h3, h4⟩ := im_bounds_ball hz
  have hre := abs_re_sub_le z w
  have him := abs_im_sub_le z w
  rw [abs_le] at hre him
  have hr : radius n = 1 / (40 * n) := rfl
  simp only [center, hr] at h1 h2 h3 h4
  have hk1 : (0 : ℝ) ≤ k.1 := Nat.cast_nonneg _
  have hk2 : (0 : ℝ) ≤ k.2 := Nat.cast_nonneg _
  have e1 : (w.re - 1 / 10) * (10 * n) ≥ (k.1 : ℝ) + 1 / 8 := by
    have : w.re ≥ 1 / 10 + ((k.1 : ℝ) + 1 / 2) / (10 * n) - 1 / (40 * n) - 1 / (80 * n) := by linarith
    have e : (1 / 10 + ((k.1 : ℝ) + 1 / 2) / (10 * n) - 1 / (40 * n) - 1 / (80 * n) - 1 / 10) * (10 * n) =
        (k.1 : ℝ) + 1 / 8 := by field_simp; ring
    nlinarith
  have e2 : (w.re - 1 / 10) * (10 * n) ≤ (k.1 : ℝ) + 7 / 8 := by
    have : w.re ≤ 1 / 10 + ((k.1 : ℝ) + 1 / 2) / (10 * n) + 1 / (40 * n) + 1 / (80 * n) := by linarith
    have e : (1 / 10 + ((k.1 : ℝ) + 1 / 2) / (10 * n) + 1 / (40 * n) + 1 / (80 * n) - 1 / 10) * (10 * n) =
        (k.1 : ℝ) + 7 / 8 := by field_simp; ring
    nlinarith
  have e3 : (w.im - 6 / 5) * (10 * n) ≥ (k.2 : ℝ) + 1 / 8 := by
    have : w.im ≥ 6 / 5 + ((k.2 : ℝ) + 1 / 2) / (10 * n) - 1 / (40 * n) - 1 / (80 * n) := by linarith
    have e : (6 / 5 + ((k.2 : ℝ) + 1 / 2) / (10 * n) - 1 / (40 * n) - 1 / (80 * n) - 6 / 5) * (10 * n) =
        (k.2 : ℝ) + 1 / 8 := by field_simp; ring
    nlinarith
  have e4 : (w.im - 6 / 5) * (10 * n) ≤ (k.2 : ℝ) + 7 / 8 := by
    have : w.im ≤ 6 / 5 + ((k.2 : ℝ) + 1 / 2) / (10 * n) + 1 / (40 * n) + 1 / (80 * n) := by linarith
    have e : (6 / 5 + ((k.2 : ℝ) + 1 / 2) / (10 * n) + 1 / (40 * n) + 1 / (80 * n) - 6 / 5) * (10 * n) =
        (k.2 : ℝ) + 7 / 8 := by field_simp; ring
    nlinarith
  constructor
  · rw [Nat.floor_eq_iff (by linarith)]
    constructor <;> linarith
  · rw [Nat.floor_eq_iff (by linarith)]
    constructor <;> linarith

/-- Two test discs whose points come within `1/(80n)` of each other are the same disc. -/
theorem eq_of_near {k l : Fin (3 * n) × Fin (6 * n)} {z w : ℍ} (hz : z ∈ discP n k) (hw : w ∈ discP n l)
    (hd : dist (z : ℂ) (w : ℂ) ≤ 1 / (80 * n)) : k = l := by
  obtain ⟨a1, a2⟩ := floor_eq_of_near hn hz hd
  obtain ⟨b1, b2⟩ := floor_eq_of_near hn hw (by rw [dist_self]; have := n_pos hn; positivity)
  exact Prod.ext (Fin.ext (a1.symm.trans b1)) (Fin.ext (a2.symm.trans b2))

/-- A point of a positive disc is far from every negative disc. -/
theorem far_discM {k l : Fin (3 * n) × Fin (6 * n)} {z w : ℍ} (hz : z ∈ discP n k) (hw : w ∈ discM n l) :
    1 / 5 ≤ dist (z : ℂ) (w : ℂ) := by
  have h1 := (discP_subset hn k hz).1
  have h2 := (discM_subset hn l hw).1
  have hzre : 0 ≤ z.re := by
    have := re_bounds_ball hz
    have := center_re_bounds hn k
    have := radius_pos hn
    have : radius n ≤ 1 / (20 * n) := by have := two_radius_eq hn; linarith
    linarith
  have hwre : w.re ≤ 0 := by
    have hm := mem_discM_iff.1 hw
    have := re_bounds_ball hm
    have := center_re_bounds hn l
    have : radius n ≤ 1 / (20 * n) := by have := two_radius_eq hn; have := radius_pos hn; linarith
    have e : (mirror w).re = -w.re := by
      show (-(starRingEnd ℂ) (w : ℂ)).re = -(w : ℂ).re
      simp
    linarith
  rw [abs_of_nonneg hzre] at h1
  rw [abs_of_nonpos hwre] at h2
  have := abs_re_sub_le z w
  rw [abs_of_nonneg (by linarith)] at this
  linarith

/-- The kernel range of `R = 1/(204800 n²)`. -/
def kernelRadius (n : ℕ) : ℝ := 1 / (204800 * (n : ℝ) ^ 2)

theorem kernelRadius_pos : 0 < kernelRadius n := by unfold kernelRadius; have := n_pos hn; positivity

theorem kernelRadius_le : kernelRadius n ≤ 1 / 204800 := by
  unfold kernelRadius
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem dist_le_of_kernel {z w : ℍ} (hz : z ∈ region) (hu : pairU z w ≤ kernelRadius n) :
    dist (z : ℂ) (w : ℂ) ≤ 1 / (80 * n) := by
  have hR := kernelRadius_le hn
  have h := dist_sq_le_of_pairU (by linarith) (by linarith [hz.2.2.2]) hu
  have hn' := n_pos hn
  have e : 32 * kernelRadius n = (1 / (80 * n)) ^ 2 := by unfold kernelRadius; field_simp; ring
  rw [e] at h
  exact (pow_le_pow_iff_left₀ dist_nonneg (by positivity) (by norm_num)).1 h

/-- The disc pair of index `k`. -/
def pairSet (n : ℕ) (k : Fin (3 * n) × Fin (6 * n)) : Set ℍ := discP n k ∪ discM n k

theorem pairSet_subset (k : Fin (3 * n) × Fin (6 * n)) : pairSet n k ⊆ region :=
  Set.union_subset (discP_subset hn k) (discM_subset hn k)

/-- **Different pairs are beyond the kernel range of each other.** -/
theorem kernel_lt_of_ne {k l : Fin (3 * n) × Fin (6 * n)} (hkl : k ≠ l) {z w : ℍ} (hz : z ∈ pairSet n k)
    (hw : w ∈ pairSet n l) : kernelRadius n < pairU z w := by
  by_contra hle
  push Not at hle
  have hd := dist_le_of_kernel hn (pairSet_subset hn k hz) hle
  have hn' := n_pos hn
  have hsmall : 1 / (80 * (n : ℝ)) < 1 / 5 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  rcases hz with hz | hz <;> rcases hw with hw | hw
  · exact hkl (eq_of_near hn hz hw hd)
  · linarith [far_discM hn hz hw]
  · have := far_discM hn hw hz
    rw [dist_comm] at this
    linarith
  · have hd' : dist ((mirror z : ℍ) : ℂ) ((mirror w : ℍ) : ℂ) ≤ 1 / (80 * n) := by
      rw [dist_mirror]
      exact hd
    exact hkl (eq_of_near hn (mem_discM_iff.1 hz) (mem_discM_iff.1 hw) hd')

/-- A positive disc is beyond the kernel range of its own negative disc. -/
theorem kernel_lt_PM {k : Fin (3 * n) × Fin (6 * n)} {z w : ℍ} (hz : z ∈ discP n k) (hw : w ∈ discM n k) :
    kernelRadius n < pairU z w := by
  by_contra hle
  push Not at hle
  have hd := dist_le_of_kernel hn (discP_subset hn k hz) hle
  have hn' := n_pos hn
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsmall : 1 / (80 * (n : ℝ)) < 1 / 5 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  linarith [far_discM hn hz hw]

theorem kernel_lt_MP {k : Fin (3 * n) × Fin (6 * n)} {z w : ℍ} (hz : z ∈ discM n k) (hw : w ∈ discP n k) :
    kernelRadius n < pairU z w := by
  rw [GaloisForLFunctions.HTGeometry.pairU_comm]
  exact kernel_lt_PM hn hw hz

/-- The kernel range of an inner disc stays in its disc. -/
theorem mem_discP_of_inner {k : Fin (3 * n) × Fin (6 * n)} {z w : ℍ} (hz : z ∈ innerP n k)
    (hu : pairU z w ≤ kernelRadius n) : w ∈ discP n k := by
  have hzP : z ∈ discP n k := by
    change (z : ℂ) ∈ Metric.closedBall _ _ at hz ⊢
    exact Metric.closedBall_subset_closedBall (by have := radius_pos hn; linarith) hz
  have hd := dist_le_of_kernel hn (discP_subset hn k hzP) hu
  change (w : ℂ) ∈ Metric.closedBall _ _
  change (z : ℂ) ∈ Metric.closedBall _ _ at hz
  rw [Metric.mem_closedBall] at hz ⊢
  have hr : radius n / 2 = 1 / (80 * n) := by unfold radius; field_simp; ring
  calc dist (w : ℂ) (center n k) ≤ dist (w : ℂ) (z : ℂ) + dist (z : ℂ) (center n k) := dist_triangle _ _ _
    _ ≤ 1 / (80 * n) + radius n / 2 := by rw [dist_comm]; exact add_le_add hd hz
    _ = radius n := by rw [hr]; unfold radius; field_simp; ring

theorem mem_discM_of_inner {k : Fin (3 * n) × Fin (6 * n)} {z w : ℍ} (hz : z ∈ innerM n k)
    (hu : pairU z w ≤ kernelRadius n) : w ∈ discM n k := by
  have hz' : mirror z ∈ innerP n k := by
    change ((mirror z : ℍ) : ℂ) ∈ Metric.closedBall _ _
    change (z : ℂ) ∈ Metric.closedBall _ _ at hz
    rw [coe_mirror, Metric.mem_closedBall, Complex.dist_eq]
    rw [Metric.mem_closedBall, Complex.dist_eq] at hz
    rw [show -(starRingEnd ℂ) (z : ℂ) - center n k = -(starRingEnd ℂ) ((z : ℂ) - -(starRingEnd ℂ) (center n k)) by
      simp; ring, norm_neg, Complex.norm_conj]
    exact hz
  have hu' : pairU (mirror z) (mirror w) ≤ kernelRadius n := by
    have e : pairU (mirror z) (mirror w) = pairU z w := by
      unfold pairU
      rw [mirror_im, mirror_im, dist_mirror]
    rw [e]; exact hu
  exact mem_discM_iff.2 (mem_discP_of_inner hn hz' hu')

end Separation

/-! ### The test vectors -/

/-- The odd indicator of the disc pair `k`. -/
def testFun (n : ℕ) (k : Fin (3 * n) × Fin (6 * n)) (z : ℍ) : ℝ :=
  (discP n k).indicator 1 z - (discM n k).indicator 1 z

/-- The test field: the odd indicator times the deck unit vector. -/
def testField (n : ℕ) (k : Fin (3 * n) × Fin (6 * n)) (z : ℍ) : DeckSpace 0 :=
  ((testFun n k z : ℝ) : ℂ) • onesVec 0

theorem measurableSet_discP (n : ℕ) (k : Fin (3 * n) × Fin (6 * n)) : MeasurableSet (discP n k) :=
  measurableSet_ball _ _
theorem measurableSet_discM (n : ℕ) (k : Fin (3 * n) × Fin (6 * n)) : MeasurableSet (discM n k) :=
  measurableSet_ball _ _

section Vectors

variable (hn : 1 ≤ n)
include hn

theorem disjoint_PM (k : Fin (3 * n) × Fin (6 * n)) : Disjoint (discP n k) (discM n k) := by
  rw [Set.disjoint_left]
  intro z hzP hzM
  have := far_discM hn hzP hzM
  simp at this
  linarith

theorem testFun_of_P {k : Fin (3 * n) × Fin (6 * n)} {z : ℍ} (hz : z ∈ discP n k) : testFun n k z = 1 := by
  have hM : z ∉ discM n k := Set.disjoint_left.1 (disjoint_PM hn k) hz
  simp [testFun, Set.indicator_of_mem hz, Set.indicator_of_notMem hM]

theorem testFun_of_M {k : Fin (3 * n) × Fin (6 * n)} {z : ℍ} (hz : z ∈ discM n k) : testFun n k z = -1 := by
  have hP : z ∉ discP n k := fun h => Set.disjoint_left.1 (disjoint_PM hn k) h hz
  simp [testFun, Set.indicator_of_mem hz, Set.indicator_of_notMem hP]

omit hn in
theorem testFun_of_not {k : Fin (3 * n) × Fin (6 * n)} {z : ℍ} (hz : z ∉ pairSet n k) : testFun n k z = 0 := by
  simp only [pairSet, Set.mem_union, not_or] at hz
  simp [testFun, Set.indicator_of_notMem hz.1, Set.indicator_of_notMem hz.2]

theorem abs_testFun_le (k : Fin (3 * n) × Fin (6 * n)) (z : ℍ) : |testFun n k z| ≤ 1 := by
  by_cases hP : z ∈ discP n k
  · rw [testFun_of_P hn hP]; norm_num
  · by_cases hM : z ∈ discM n k
    · rw [testFun_of_M hn hM]; norm_num
    · rw [testFun_of_not (by simp [pairSet, hP, hM])]; norm_num

omit hn in
theorem testFun_mirror (k : Fin (3 * n) × Fin (6 * n)) (z : ℍ) : testFun n k (mirror z) = -testFun n k z := by
  have h1 : (discP n k).indicator (1 : ℍ → ℝ) (mirror z) = (discM n k).indicator 1 z := by
    by_cases h : z ∈ discM n k
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (mem_discM_iff.1 h)]
      rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (mem_discM_iff.2 h'))]
  have h2 : (discM n k).indicator (1 : ℍ → ℝ) (mirror z) = (discP n k).indicator 1 z := by
    by_cases h : z ∈ discP n k
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (mem_discM_iff.2 (by rwa [mirror_mirror]))]
      rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (by
        have := mem_discM_iff.1 h'; rwa [mirror_mirror] at this))]
  simp only [testFun, h1, h2]
  ring

omit hn in
theorem measurable_testFun (k : Fin (3 * n) × Fin (6 * n)) : Measurable (testFun n k) :=
  (measurable_one.indicator (measurableSet_discP n k)).sub (measurable_one.indicator (measurableSet_discM n k))

theorem memLp_testField (k : Fin (3 * n) × Fin (6 * n)) :
    MemLp (testField n k) 2 MaassCongruenceL2.cellMeasure := by
  refine MemLp.of_bound ((Complex.measurable_ofReal.comp (measurable_testFun k)).smul_const
    (onesVec 0)).aestronglyMeasurable ‖onesVec 0‖ (Eventually.of_forall fun z => ?_)
  rw [testField, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (abs_testFun_le hn k z)

theorem testField_of_not {k : Fin (3 * n) × Fin (6 * n)} {z : ℍ} (hz : z ∉ region) : testField n k z = 0 := by
  rw [testField, testFun_of_not (fun h => hz (pairSet_subset hn k h))]
  simp

theorem mirrorL2_testField (k : Fin (3 * n) × Fin (6 * n)) :
    mirrorL2 (toDeckL2 (testField n k) (memLp_testField hn k)) =
      -toDeckL2 (testField n k) (memLp_testField hn k) := by
  apply Lp.ext
  have h1 := coeFn_mirrorL2 (toDeckL2 (testField n k) (memLp_testField hn k))
  have h4 : ⇑(toDeckL2 (testField n k) (memLp_testField hn k)) =ᵐ[MaassCongruenceL2.cellMeasure]
      testField n k := MemLp.coeFn_toLp _
  have h2 := measurePreserving_mirror_fd.quasiMeasurePreserving.ae_eq_comp h4
  filter_upwards [h1, h2, Lp.coeFn_neg (toDeckL2 (testField n k) (memLp_testField hn k)), h4]
    with z hz1 hz2 hz3 hz4
  rw [hz1, hz2, hz3, Pi.neg_apply, hz4]
  simp [testField, testFun_mirror k z]

/-- **The test vector**: cuspidal because it is odd. -/
def testVec (k : Fin (3 * n) × Fin (6 * n)) : CuspidalL2 0 :=
  ⟨toDeckL2 (testField n k) (memLp_testField hn k), mem_cuspidalL2Closure_of_odd (mirrorL2_testField hn k)⟩

end Vectors

/-! ### The kernel on the test vectors -/

/-- The narrow kernel at resolution `n`. -/
def kernelAt (n : ℕ) (hn : 1 ≤ n) : SmoothProfile := narrowProfile (kernelRadius n) (kernelRadius_pos hn)

/-- The convolution of a test function with the kernel. -/
def conv (n : ℕ) (hn : 1 ≤ n) (k : Fin (3 * n) × Fin (6 * n)) (z : ℍ) : ℝ :=
  ∫ z' in ModularGroup.fd, (kernelAt n hn).toFun (pairU z z') * testFun n k z'

/-- The real mass of the kernel. -/
def mass (n : ℕ) (hn : 1 ≤ n) : ℝ := ∫ w : ℍ, (kernelAt n hn).toFun (pairU UpperHalfPlane.I w)

theorem mem_fd_of_fdo {z : ℍ} (hz : z ∈ ModularGroup.fdo) : z ∈ ModularGroup.fd :=
  ⟨hz.1.le, hz.2.le⟩

theorem card_deck_zero : Fintype.card (Deck 0) = 1 :=
  Fintype.card_eq_one_iff.mpr ⟨QuotientGroup.mk 1, fun _ => Subsingleton.elim _ _⟩

theorem inner_ones : ⟪onesVec 0, onesVec 0⟫_ℂ = 1 := by
  rw [PiLp.inner_apply]
  simp [onesVec, card_deck_zero]

theorem inner_smul_ones (a b : ℝ) :
    ⟪((a : ℝ) : ℂ) • onesVec 0, ((b : ℝ) : ℂ) • onesVec 0⟫_ℂ = ((a * b : ℝ) : ℂ) := by
  rw [inner_smul_left, inner_smul_right, inner_ones, Complex.conj_ofReal]
  push_cast
  ring

section Kernel

variable (hn : 1 ≤ n)
include hn

theorem kernelRadius_le_small : kernelRadius n ≤ 1 / 12800 := by
  have := kernelRadius_le hn
  linarith

theorem ppApply_testField {k : Fin (3 * n) × Fin (6 * n)} {z : ℍ} (hz : z ∈ region) :
    ppApply (kernelAt n hn).toFun (testField n k) z = ((conv n hn k z : ℝ) : ℂ) • onesVec 0 := by
  rw [ppApply_eq_local (kernelRadius_le_small hn) (kernelAt n hn).kernelSupport
    (fun z' hz' => testField_of_not hn hz') hz]
  have e : ∀ z', (((kernelAt n hn).toFun (pairU z z') : ℝ) : ℂ) • testField n k z' =
      (((kernelAt n hn).toFun (pairU z z') * testFun n k z' : ℝ) : ℂ) • onesVec 0 := by
    intro z'
    rw [testField, smul_smul, Complex.ofReal_mul]
  simp_rw [e]
  rw [integral_smul_const, integral_complex_ofReal]
  rfl

theorem conv_eq_zero_of_ne {k l : Fin (3 * n) × Fin (6 * n)} (hkl : k ≠ l) {z : ℍ}
    (hz : z ∈ pairSet n k) : conv n hn l z = 0 := by
  unfold conv
  refine integral_eq_zero_of_ae (Eventually.of_forall fun z' => ?_)
  show (kernelAt n hn).toFun (pairU z z') * testFun n l z' = 0
  by_cases hz' : z' ∈ pairSet n l
  · rw [(kernelAt n hn).kernelSupport _ (kernel_lt_of_ne hn hkl hz hz'), zero_mul]
  · rw [testFun_of_not hz', mul_zero]

theorem conv_nonneg_of_P {k : Fin (3 * n) × Fin (6 * n)} {z : ℍ} (hz : z ∈ discP n k) :
    0 ≤ conv n hn k z := by
  unfold conv
  refine integral_nonneg fun z' => ?_
  show (0 : ℝ) ≤ (kernelAt n hn).toFun (pairU z z') * testFun n k z'
  by_cases hM : z' ∈ discM n k
  · rw [(kernelAt n hn).kernelSupport _ (kernel_lt_PM hn hz hM), zero_mul]
  · have h0 : 0 ≤ testFun n k z' := by
      by_cases hP : z' ∈ discP n k
      · rw [testFun_of_P hn hP]; norm_num
      · rw [testFun_of_not (by simp [pairSet, hP, hM])]
    exact mul_nonneg (narrow_nonneg _ _ _) h0

theorem conv_nonpos_of_M {k : Fin (3 * n) × Fin (6 * n)} {z : ℍ} (hz : z ∈ discM n k) :
    conv n hn k z ≤ 0 := by
  unfold conv
  refine integral_nonpos fun z' => ?_
  show (kernelAt n hn).toFun (pairU z z') * testFun n k z' ≤ 0
  by_cases hP : z' ∈ discP n k
  · rw [(kernelAt n hn).kernelSupport _ (kernel_lt_MP hn hz hP), zero_mul]
  · have h0 : testFun n k z' ≤ 0 := by
      by_cases hM : z' ∈ discM n k
      · rw [testFun_of_M hn hM]; norm_num
      · rw [testFun_of_not (by simp [pairSet, hP, hM])]
    exact mul_nonpos_of_nonneg_of_nonpos (narrow_nonneg _ _ _) h0

theorem discP_subset_fd (k : Fin (3 * n) × Fin (6 * n)) : discP n k ⊆ ModularGroup.fd := fun w hw =>
  mem_fd_of_fdo (mem_fdo_of_near (discP_subset hn k hw) (by rw [dist_self]; norm_num))

theorem discM_subset_fd (k : Fin (3 * n) × Fin (6 * n)) : discM n k ⊆ ModularGroup.fd := fun w hw =>
  mem_fd_of_fdo (mem_fdo_of_near (discM_subset hn k hw) (by rw [dist_self]; norm_num))

theorem conv_of_innerP {k : Fin (3 * n) × Fin (6 * n)} {z : ℍ} (hz : z ∈ innerP n k) :
    conv n hn k z = mass n hn := by
  unfold conv mass
  have e : ∀ z', (kernelAt n hn).toFun (pairU z z') * testFun n k z' = (kernelAt n hn).toFun (pairU z z') := by
    intro z'
    by_cases hu : pairU z z' ≤ kernelRadius n
    · rw [testFun_of_P hn (mem_discP_of_inner hn hz hu), mul_one]
    · rw [(kernelAt n hn).kernelSupport _ (not_le.mp hu)]
      simp
  simp_rw [e]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z' hz' => ?_]
  · exact RepPointPair.integral_pairU_eq _ z
  · by_contra hne
    have hu : pairU z z' ≤ kernelRadius n := by
      by_contra hlt
      exact hne ((kernelAt n hn).kernelSupport _ (not_le.mp hlt))
    exact hz' (discP_subset_fd hn k (mem_discP_of_inner hn hz hu))

theorem conv_of_innerM {k : Fin (3 * n) × Fin (6 * n)} {z : ℍ} (hz : z ∈ innerM n k) :
    conv n hn k z = -mass n hn := by
  unfold conv mass
  have e : ∀ z', (kernelAt n hn).toFun (pairU z z') * testFun n k z' = -(kernelAt n hn).toFun (pairU z z') := by
    intro z'
    by_cases hu : pairU z z' ≤ kernelRadius n
    · rw [testFun_of_M hn (mem_discM_of_inner hn hz hu), mul_neg_one]
    · rw [(kernelAt n hn).kernelSupport _ (not_le.mp hu)]
      simp
  simp_rw [e]
  rw [integral_neg, setIntegral_eq_integral_of_forall_compl_eq_zero fun z' hz' => ?_]
  · rw [RepPointPair.integral_pairU_eq _ z]
  · by_contra hne
    have hu : pairU z z' ≤ kernelRadius n := by
      by_contra hlt
      exact hne ((kernelAt n hn).kernelSupport _ (not_le.mp hlt))
    exact hz' (discM_subset_fd hn k (mem_discM_of_inner hn hz hu))

theorem mass_eq : mass n hn = (ppKernelMass (kernelAt n hn).toFun).toReal := by
  unfold mass ppKernelMass
  have hm : AEStronglyMeasurable (fun w : ℍ => (kernelAt n hn).toFun (pairU UpperHalfPlane.I w)) volume :=
    ((kernelAt n hn).contDiff_two.continuous.comp (continuous_pairU_right _)).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[volume] fun w : ℍ => (kernelAt n hn).toFun (pairU UpperHalfPlane.I w) :=
    Eventually.of_forall fun w => narrow_nonneg (kernelRadius n) (kernelRadius_pos hn) _
  rw [integral_eq_lintegral_of_nonneg_ae hnn hm]
  congr 1
  refine lintegral_congr fun w => ?_
  have h : (0 : ℝ) ≤ (kernelAt n hn).toFun (pairU UpperHalfPlane.I w) :=
    narrow_nonneg (kernelRadius n) (kernelRadius_pos hn) _
  rw [abs_of_nonneg h]

theorem mass_ge : Real.pi * kernelRadius n / 8 ≤ mass n hn := by
  rw [mass_eq hn]
  have hR := kernelRadius_le hn
  have h := narrow_mass_ge (kernelRadius_pos hn) (by linarith)
  have hfin : ppKernelMass (kernelAt n hn).toFun ≠ ⊤ :=
    (kernelMass_lt_top (kernelAt n hn).pp.radius_nonneg (kernelAt n hn).pp.abs_le
      (kernelAt n hn).pp.support).ne
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 h

theorem mass_pos : 0 < mass n hn := by
  have hpos : 0 < Real.pi * kernelRadius n / 8 := by have := kernelRadius_pos hn; positivity
  exact lt_of_lt_of_le hpos (mass_ge hn)

/-! ### The quadratic form on the test vectors -/

theorem inner_integrand_ae (k l : Fin (3 * n) × Fin (6 * n)) :
    (fun z => ⟪(toDeckL2 (testField n k) (memLp_testField hn k) : ℍ → DeckSpace 0) z,
      ((kernelAt n hn).pp.op 0 (toDeckL2 (testField n l) (memLp_testField hn l)) : ℍ → DeckSpace 0) z⟫_ℂ)
      =ᵐ[MaassCongruenceL2.cellMeasure] fun z => ((testFun n k z * conv n hn l z : ℝ) : ℂ) := by
  have h1 : ⇑(toDeckL2 (testField n k) (memLp_testField hn k)) =ᵐ[MaassCongruenceL2.cellMeasure]
      testField n k := MemLp.coeFn_toLp _
  have h2 := (kernelAt n hn).pp.op_coeFn (toDeckL2 (testField n l) (memLp_testField hn l))
  have h3 : ⇑(toDeckL2 (testField n l) (memLp_testField hn l)) =ᵐ[MaassCongruenceL2.cellMeasure]
      testField n l := MemLp.coeFn_toLp _
  rw [ppApply_congr_ae _ h3] at h2
  filter_upwards [h1, h2] with z hz1 hz2
  rw [hz1, hz2]
  by_cases hz : z ∈ region
  · rw [SmoothProfile.pp_toFun, ppApply_testField hn hz, testField, inner_smul_ones]
  · rw [testField_of_not hn hz, inner_zero_left, testFun_of_not (fun h => hz (pairSet_subset hn k h)),
      zero_mul, Complex.ofReal_zero]

theorem inner_testVec_op (k l : Fin (3 * n) × Fin (6 * n)) :
    ⟪(testVec hn k : CuspidalL2 0), (kernelAt n hn).pp.cuspOp 0 (testVec hn l)⟫_ℂ =
      ((∫ z in ModularGroup.fd, testFun n k z * conv n hn l z : ℝ) : ℂ) := by
  rw [Submodule.coe_inner, PairProfile.coe_cuspOp, MeasureTheory.L2.inner_def, ← integral_complex_ofReal]
  exact integral_congr_ae (inner_integrand_ae hn k l)

theorem integrable_testFun_conv (k l : Fin (3 * n) × Fin (6 * n)) :
    Integrable (fun z => testFun n k z * conv n hn l z) MaassCongruenceL2.cellMeasure := by
  have hint := MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
    (toDeckL2 (testField n k) (memLp_testField hn k))
    ((kernelAt n hn).pp.op 0 (toDeckL2 (testField n l) (memLp_testField hn l)))
  have := (hint.congr (inner_integrand_ae hn k l)).re
  simpa using this

theorem inner_testVec (k l : Fin (3 * n) × Fin (6 * n)) :
    ⟪(testVec hn k : CuspidalL2 0), testVec hn l⟫_ℂ =
      ((∫ z in ModularGroup.fd, testFun n k z * testFun n l z : ℝ) : ℂ) := by
  rw [Submodule.coe_inner, MeasureTheory.L2.inner_def, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_testField hn k), MemLp.coeFn_toLp (memLp_testField hn l)]
    with z hz1 hz2
  change ⟪(toDeckL2 (testField n k) (memLp_testField hn k) : ℍ → DeckSpace 0) z,
    (toDeckL2 (testField n l) (memLp_testField hn l) : ℍ → DeckSpace 0) z⟫_ℂ = _
  rw [toDeckL2, toDeckL2, hz1, hz2, testField, testField, inner_smul_ones]

theorem testFun_mul_eq_zero {k l : Fin (3 * n) × Fin (6 * n)} (hkl : k ≠ l) (z : ℍ) :
    testFun n k z * testFun n l z = 0 := by
  by_cases hk : z ∈ pairSet n k
  · by_cases hl : z ∈ pairSet n l
    · exfalso
      have := kernel_lt_of_ne hn hkl hk hl
      have h0 : pairU z z = 0 := by unfold pairU; simp
      have := kernelRadius_pos hn
      linarith
    · rw [testFun_of_not hl, mul_zero]
  · rw [testFun_of_not hk, zero_mul]

/-- The radius of the inner discs, `1/(80n)`. -/
theorem half_radius_eq : radius n / 2 = 1 / (80 * n) := by
  unfold radius; have := n_pos hn; field_simp; ring

/-- **The form on one test vector.** -/
theorem form_ge_testVec (k : Fin (3 * n) × Fin (6 * n)) :
    mass n hn / 16 * ‖(testVec hn k : CuspidalL2 0)‖ ^ 2 ≤
      (⟪(testVec hn k : CuspidalL2 0), (kernelAt n hn).pp.cuspOp 0 (testVec hn k)⟫_ℂ).re := by
  have hm := (mass_pos hn).le
  have hρ := radius_pos hn
  have hc := center_im_bounds hn k
  have hcre : (-(starRingEnd ℂ) (center n k)).im = (center n k).im := by simp
  have hn' := n_pos hn
  have h20 : radius n ≤ 1 / (20 * n) := by have := two_radius_eq hn; linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h20' : (1 : ℝ) / (20 * n) ≤ 1 / 20 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- the norm
  have hnorm : ‖(testVec hn k : CuspidalL2 0)‖ ^ 2 ≤ 2 * (Real.pi * radius n ^ 2) := by
    have h := inner_testVec hn k k
    have hre : ‖(testVec hn k : CuspidalL2 0)‖ ^ 2 = ∫ z in ModularGroup.fd, testFun n k z * testFun n k z := by
      have e := congrArg Complex.re h
      rw [Complex.ofReal_re] at e
      rw [← e]
      have := @inner_self_eq_norm_sq ℂ (CuspidalL2 0) _ _ _ (testVec hn k)
      simpa using this.symm
    rw [hre]
    have hpt : ∀ z, testFun n k z * testFun n k z ≤
        (discP n k).indicator 1 z + (discM n k).indicator 1 z := by
      intro z
      by_cases hP : z ∈ discP n k
      · rw [testFun_of_P hn hP, Set.indicator_of_mem hP,
          Set.indicator_of_notMem (Set.disjoint_left.1 (disjoint_PM hn k) hP)]; norm_num
      · by_cases hM : z ∈ discM n k
        · rw [testFun_of_M hn hM, Set.indicator_of_mem hM, Set.indicator_of_notMem hP]; norm_num
        · rw [testFun_of_not (by simp [pairSet, hP, hM]), Set.indicator_of_notMem hP,
            Set.indicator_of_notMem hM]; norm_num
    have hiP : Integrable ((discP n k).indicator (1 : ℍ → ℝ)) MaassCongruenceL2.cellMeasure :=
      (integrable_const 1).indicator (measurableSet_discP n k)
    have hiM : Integrable ((discM n k).indicator (1 : ℍ → ℝ)) MaassCongruenceL2.cellMeasure :=
      (integrable_const 1).indicator (measurableSet_discM n k)
    have hsq : Integrable (fun z => testFun n k z * testFun n k z) MaassCongruenceL2.cellMeasure := by
      refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun z => ?_) -- bounded
      · exact ((measurable_testFun k).mul (measurable_testFun k)).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_one₀ (abs_testFun_le hn k z) (abs_nonneg _) (abs_testFun_le hn k z)
    calc ∫ z in ModularGroup.fd, testFun n k z * testFun n k z
        ≤ ∫ z in ModularGroup.fd, ((discP n k).indicator 1 z + (discM n k).indicator 1 z) :=
          integral_mono hsq (hiP.add hiM) hpt
      _ = (volume (discP n k)).toReal + (volume (discM n k)).toReal := by
          rw [integral_add hiP hiM, integral_indicator_one (measurableSet_discP n k),
            integral_indicator_one (measurableSet_discM n k), measureReal_def, measureReal_def]
          simp only [MaassCongruenceL2.cellMeasure]
          rw [Measure.restrict_apply (measurableSet_discP n k),
            Measure.restrict_apply (measurableSet_discM n k), Set.inter_eq_left.2 (discP_subset_fd hn k),
            Set.inter_eq_left.2 (discM_subset_fd hn k)]
      _ ≤ Real.pi * radius n ^ 2 + Real.pi * radius n ^ 2 := by
          gcongr
          · exact ENNReal.toReal_le_of_le_ofReal (by positivity)
              (volume_ball_le hρ.le (by linarith [hc.1]))
          · exact ENNReal.toReal_le_of_le_ofReal (by positivity)
              (volume_ball_le hρ.le (by rw [hcre]; linarith [hc.1]))
      _ = 2 * (Real.pi * radius n ^ 2) := by ring
  -- the form
  have hform : 2 * (mass n hn * (Real.pi * (radius n / 2) ^ 2 / 4)) ≤
      (⟪(testVec hn k : CuspidalL2 0), (kernelAt n hn).pp.cuspOp 0 (testVec hn k)⟫_ℂ).re := by
    rw [inner_testVec_op hn k k, Complex.ofReal_re]
    have hpt : ∀ z, mass n hn * ((innerP n k).indicator 1 z + (innerM n k).indicator 1 z) ≤
        testFun n k z * conv n hn k z := by
      intro z
      have hiPP : innerP n k ⊆ discP n k := fun w hw => by
        change (w : ℂ) ∈ Metric.closedBall _ _ at hw ⊢
        exact Metric.closedBall_subset_closedBall (by linarith) hw
      have hiMM : innerM n k ⊆ discM n k := fun w hw => by
        change (w : ℂ) ∈ Metric.closedBall _ _ at hw ⊢
        exact Metric.closedBall_subset_closedBall (by linarith) hw
      by_cases hP : z ∈ discP n k
      · have hMn : z ∉ innerM n k := fun h => Set.disjoint_left.1 (disjoint_PM hn k) hP (hiMM h)
        rw [testFun_of_P hn hP, one_mul, Set.indicator_of_notMem hMn, add_zero]
        by_cases hi : z ∈ innerP n k
        · rw [Set.indicator_of_mem hi, conv_of_innerP hn hi]; simp
        · rw [Set.indicator_of_notMem hi, mul_zero]; exact conv_nonneg_of_P hn hP
      · have hPn : z ∉ innerP n k := fun h => hP (hiPP h)
        rw [Set.indicator_of_notMem hPn, zero_add]
        by_cases hM : z ∈ discM n k
        · rw [testFun_of_M hn hM]
          by_cases hi : z ∈ innerM n k
          · rw [Set.indicator_of_mem hi, conv_of_innerM hn hi]; simp
          · rw [Set.indicator_of_notMem hi, mul_zero]; linarith [conv_nonpos_of_M hn hM]
        · have hMn : z ∉ innerM n k := fun h => hM (hiMM h)
          rw [Set.indicator_of_notMem hMn, testFun_of_not (by simp [pairSet, hP, hM])]; simp
    have hiP : Integrable ((innerP n k).indicator (1 : ℍ → ℝ)) MaassCongruenceL2.cellMeasure :=
      (integrable_const 1).indicator (measurableSet_ball _ _)
    have hiM : Integrable ((innerM n k).indicator (1 : ℍ → ℝ)) MaassCongruenceL2.cellMeasure :=
      (integrable_const 1).indicator (measurableSet_ball _ _)
    have hsubP : innerP n k ⊆ ModularGroup.fd := fun w hw => discP_subset_fd hn k (by
      change (w : ℂ) ∈ Metric.closedBall _ _ at hw ⊢
      exact Metric.closedBall_subset_closedBall (by linarith) hw)
    have hsubM : innerM n k ⊆ ModularGroup.fd := fun w hw => discM_subset_fd hn k (by
      change (w : ℂ) ∈ Metric.closedBall _ _ at hw ⊢
      exact Metric.closedBall_subset_closedBall (by linarith) hw)
    calc 2 * (mass n hn * (Real.pi * (radius n / 2) ^ 2 / 4))
        ≤ mass n hn * ((volume (innerP n k)).toReal + (volume (innerM n k)).toReal) := by
          have hb1 : Real.pi * (radius n / 2) ^ 2 / 4 ≤ (volume (innerP n k)).toReal :=
            (ENNReal.ofReal_le_iff_le_toReal
              (measure_ne_top_of_subset hsubP GaloisForLFunctions.HTGeometry.volume_fd_ne_top)).1
              (volume_ball_ge (by linarith) (by linarith [hc.1]) (by linarith [hc.2]))
          have hb2 : Real.pi * (radius n / 2) ^ 2 / 4 ≤ (volume (innerM n k)).toReal :=
            (ENNReal.ofReal_le_iff_le_toReal
              (measure_ne_top_of_subset hsubM GaloisForLFunctions.HTGeometry.volume_fd_ne_top)).1
              (volume_ball_ge (by linarith) (by rw [hcre]; linarith [hc.1]) (by rw [hcre]; linarith [hc.2]))
          nlinarith
      _ = ∫ z in ModularGroup.fd, mass n hn * ((innerP n k).indicator 1 z + (innerM n k).indicator 1 z) := by
          have hmP : MeasurableSet (innerP n k) := measurableSet_ball _ _
          have hmM : MeasurableSet (innerM n k) := measurableSet_ball _ _
          rw [integral_const_mul, integral_add hiP hiM, integral_indicator_one hmP,
            integral_indicator_one hmM, measureReal_def, measureReal_def]
          simp only [MaassCongruenceL2.cellMeasure]
          rw [Measure.restrict_apply hmP, Measure.restrict_apply hmM, Set.inter_eq_left.2 hsubP,
            Set.inter_eq_left.2 hsubM]
      _ ≤ ∫ z in ModularGroup.fd, testFun n k z * conv n hn k z :=
          integral_mono ((hiP.add hiM).const_mul _) (integrable_testFun_conv hn k k) hpt
  have hr : (radius n / 2) ^ 2 = radius n ^ 2 / 4 := by ring
  rw [hr] at hform
  nlinarith

end Kernel

/-! ### The span of the test vectors -/

/-- **The form on a span of mutually orthogonal, kernel-orthogonal vectors.** -/
theorem form_ge_on_span {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι]
    (T : E →L[ℂ] E) (v : ι → E) (hoff : ∀ k l, k ≠ l → ⟪v k, T (v l)⟫_ℂ = 0)
    (horth : ∀ k l, k ≠ l → ⟪v k, v l⟫_ℂ = 0) {c : ℝ}
    (hdiag : ∀ k, c * ‖v k‖ ^ 2 ≤ (⟪v k, T (v k)⟫_ℂ).re) :
    ∀ f ∈ Submodule.span ℂ (Set.range v), c * ‖f‖ ^ 2 ≤ (⟪f, T f⟫_ℂ).re := by
  classical
  intro f hf
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hf
  have hT : ⟪∑ k, a k • v k, T (∑ l, a l • v l)⟫_ℂ =
      ∑ k, ((‖a k‖ ^ 2 : ℝ) : ℂ) * ⟪v k, T (v k)⟫_ℂ := by
    simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_left, inner_smul_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [hoff l k hl]) (by simp)]
    push_cast
    rw [← Complex.mul_conj']
    ring
  have hN : ⟪∑ k, a k • v k, ∑ l, a l • v l⟫_ℂ = ∑ k, ((‖a k‖ ^ 2 : ℝ) : ℂ) * ⟪v k, v k⟫_ℂ := by
    simp only [inner_sum, sum_inner, inner_smul_left, inner_smul_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [horth l k hl]) (by simp)]
    push_cast
    rw [← Complex.mul_conj']
    ring
  have hnorm : ‖∑ k, a k • v k‖ ^ 2 = ∑ k, ‖a k‖ ^ 2 * ‖v k‖ ^ 2 := by
    have h1 := @inner_self_eq_norm_sq ℂ E _ _ _ (∑ k, a k • v k)
    have h1' : (⟪∑ k, a k • v k, ∑ k, a k • v k⟫_ℂ).re = ‖∑ k, a k • v k‖ ^ 2 := by simpa using h1
    rw [← h1', hN, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h2 := @inner_self_eq_norm_sq ℂ E _ _ _ (v k)
    have h2' : (⟪v k, v k⟫_ℂ).re = ‖v k‖ ^ 2 := by simpa using h2
    rw [Complex.re_ofReal_mul, h2']
  rw [hT, Complex.re_sum, hnorm, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Complex.re_ofReal_mul]
  have := hdiag k
  nlinarith [sq_nonneg ‖a k‖]

/-! ### The count -/

theorem cuspCount_mono {Λ Λ' : ℝ} (h : Λ ≤ Λ') : cuspCount Λ ≤ cuspCount Λ' := by
  unfold cuspCount
  refine Finset.card_le_card fun i hi => ?_
  rw [Set.Finite.mem_toFinset] at hi ⊢
  exact le_trans hi h

theorem card_grid (n : ℕ) : Fintype.card (Fin (3 * n) × Fin (6 * n)) = 18 * n ^ 2 := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

theorem testVec_ne_zero (hn : 1 ≤ n) (k : Fin (3 * n) × Fin (6 * n)) : testVec hn k ≠ 0 := by
  intro h0
  have h := inner_testVec hn k k
  rw [h0, inner_zero_left] at h
  have hint : ∫ z in ModularGroup.fd, testFun n k z * testFun n k z = 0 := by
    exact_mod_cast h.symm
  have hρ := radius_pos hn
  have hc := center_im_bounds hn k
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr40 : radius n ≤ 1 / 40 := by
    unfold radius
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hpos20 : 0 ≤ 1 / (20 * (n : ℝ)) := by positivity
  have hsubP : innerP n k ⊆ ModularGroup.fd := fun w hw => discP_subset_fd hn k (by
    change (w : ℂ) ∈ Metric.closedBall _ _ at hw ⊢
    exact Metric.closedBall_subset_closedBall (by linarith) hw)
  have hmP : MeasurableSet (innerP n k) := measurableSet_ball _ _
  have hpt : ∀ z, (innerP n k).indicator (1 : ℍ → ℝ) z ≤ testFun n k z * testFun n k z := by
    intro z
    by_cases hi : z ∈ innerP n k
    · have hP : z ∈ discP n k := by
        change (z : ℂ) ∈ Metric.closedBall _ _ at hi ⊢
        exact Metric.closedBall_subset_closedBall (by linarith) hi
      rw [Set.indicator_of_mem hi, testFun_of_P hn hP]
      norm_num
    · rw [Set.indicator_of_notMem hi]
      exact mul_self_nonneg _
  have hsq : Integrable (fun z => testFun n k z * testFun n k z) MaassCongruenceL2.cellMeasure := by
    refine Integrable.of_bound ((measurable_testFun k).mul (measurable_testFun k)).aestronglyMeasurable 1
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_one₀ (abs_testFun_le hn k z) (abs_nonneg _) (abs_testFun_le hn k z)
  have hle := integral_mono ((integrable_const 1).indicator hmP) hsq hpt
  rw [hint, integral_indicator_one hmP, measureReal_def] at hle
  simp only [MaassCongruenceL2.cellMeasure] at hle
  rw [Measure.restrict_apply hmP, Set.inter_eq_left.2 hsubP] at hle
  have hb : Real.pi * (radius n / 2) ^ 2 / 4 ≤ (volume (innerP n k)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal
      (measure_ne_top_of_subset hsubP GaloisForLFunctions.HTGeometry.volume_fd_ne_top)).1
      (volume_ball_ge (by linarith) (by linarith [hc.1]) (by linarith [hc.2]))
  have : 0 < Real.pi * (radius n / 2) ^ 2 / 4 := by positivity
  linarith

/-- **At least `18n²` cusp forms have eigenvalue at most `Cn²`.** -/
theorem count_ge_grid : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → 18 * n ^ 2 ≤ cuspCount (C * n ^ 2) := by
  obtain ⟨A, hA0, hA⟩ := exists_narrow_lap_mass_le
  refine ⟨128 * 204800 * A / Real.pi, by positivity, fun n hn => ?_⟩
  set P := kernelAt n hn
  set T : CuspidalL2 0 →L[ℂ] CuspidalL2 0 := P.pp.cuspOp 0
  have hTs : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := P.pp.cuspOp_isSymmetric
  choose κ hκ hκb using fun i => exists_kernelEigenvalue P i
  have hm := mass_pos hn
  set c₀ := mass n hn / 16 with hc₀def
  have hc₀ : 0 < c₀ := by positivity
  have hAP : (ppKernelMass (radialLap P.toFun)).toReal ≤ A :=
    hA (kernelRadius n) (kernelRadius_pos hn) (by linarith [kernelRadius_le hn])
  set Λ := A / c₀
  have hS : ∀ i, c₀ ≤ κ i → i ∈ (finite_cuspEigenIndex_le Λ).toFinset := by
    intro i hi
    rw [Set.Finite.mem_toFinset]
    show i.1 ≤ A / c₀
    have hq := one_quarter_le_cuspEigenBasis i
    have hκpos : 0 < κ i := lt_of_lt_of_le hc₀ hi
    have h1 := hκb i
    rw [abs_of_pos hκpos] at h1
    rw [le_div_iff₀ hc₀]
    nlinarith
  have hoff : ∀ k l, k ≠ l → ⟪testVec hn k, T (testVec hn l)⟫_ℂ = 0 := by
    intro k l hkl
    rw [inner_testVec_op hn k l]
    have : ∫ z in ModularGroup.fd, testFun n k z * conv n hn l z = 0 := by
      refine integral_eq_zero_of_ae (Eventually.of_forall fun z => ?_)
      show testFun n k z * conv n hn l z = 0
      by_cases hz : z ∈ pairSet n k
      · rw [conv_eq_zero_of_ne hn hkl hz, mul_zero]
      · rw [testFun_of_not hz, zero_mul]
    rw [this, Complex.ofReal_zero]
  have horth : ∀ k l, k ≠ l → ⟪testVec hn k, testVec hn l⟫_ℂ = 0 := by
    intro k l hkl
    rw [inner_testVec hn k l]
    have : ∫ z in ModularGroup.fd, testFun n k z * testFun n l z = 0 :=
      integral_eq_zero_of_ae (Eventually.of_forall fun z => testFun_mul_eq_zero hn hkl z)
    rw [this, Complex.ofReal_zero]
  set V := Submodule.span ℂ (Set.range (testVec hn))
  haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hV := form_ge_on_span T (testVec hn) hoff horth (form_ge_testVec hn)
  have hli : LinearIndependent ℂ (testVec hn) :=
    linearIndependent_of_ne_zero_of_inner_eq_zero (testVec_ne_zero hn) fun k l hkl => horth k l hkl
  have hrank : Module.finrank ℂ V = 18 * n ^ 2 := by
    rw [finrank_span_eq_card hli, card_grid]
  have hmm := finrank_le_card_of_form_ge (cuspEigenBasis 0) T hTs κ hκ
    (finite_cuspEigenIndex_le Λ).toFinset hS V hV
  rw [hrank] at hmm
  refine hmm.trans (cuspCount_mono ?_)
  -- `Λ = 16A/m ≤ 128A/(πR) = Cn²`
  have hmg := mass_ge hn
  have hR : kernelRadius n = 1 / (204800 * (n : ℝ) ^ 2) := rfl
  have hn' := n_pos hn
  have hpi := Real.pi_pos
  show A / c₀ ≤ 128 * 204800 * A / Real.pi * n ^ 2
  rw [hc₀def, div_div_eq_mul_div, div_le_iff₀ hm]
  have hmR : Real.pi * (1 / (204800 * (n : ℝ) ^ 2)) / 8 ≤ mass n hn := by rw [← hR]; exact hmg
  have key : A * 16 ≤ 128 * 204800 * A / Real.pi * n ^ 2 * (Real.pi * (1 / (204800 * (n : ℝ) ^ 2)) / 8) := by
    have e : 128 * 204800 * A / Real.pi * n ^ 2 * (Real.pi * (1 / (204800 * (n : ℝ) ^ 2)) / 8) = 16 * A := by
      field_simp
      try ring
    linarith [e]
  calc A * 16 ≤ 128 * 204800 * A / Real.pi * n ^ 2 * (Real.pi * (1 / (204800 * (n : ℝ) ^ 2)) / 8) := key
    _ ≤ 128 * 204800 * A / Real.pi * n ^ 2 * mass n hn := by gcongr

/-- **A Weyl lower bound for the cusp spectrum of the modular horizon**: the number of cusp forms of
eigenvalue at most `Λ`, with multiplicity, is at least a fixed multiple of `Λ` for large `Λ`. -/
theorem weyl_lower_bound : ∃ c > 0, ∃ Λ₀ : ℝ, ∀ Λ ≥ Λ₀, c * Λ ≤ cuspCount Λ := by
  obtain ⟨C, hC0, hC⟩ := count_ge_grid
  set C' := max C 1 with hC'def
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hC'C : C ≤ C' := le_max_left _ _
  refine ⟨9 / (2 * C'), by positivity, 4 * C', fun Λ hΛ => ?_⟩
  have hC'pos : 0 < C' := by linarith
  set x := Real.sqrt (Λ / C') with hxdef
  have hΛ0 : 0 ≤ Λ := by linarith
  have hx2 : 2 ≤ x := by
    rw [hxdef, show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by rw [le_div_iff₀ hC'pos]; linarith)
  have hxsq : x ^ 2 = Λ / C' := Real.sq_sqrt (by positivity)
  set m := ⌊x⌋₊ with hmdef
  have hm1 : 1 ≤ m := Nat.le_floor (by norm_num; linarith)
  have hmx : (m : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxm : x < m + 1 := Nat.lt_floor_add_one x
  have h1 : C' * (m : ℝ) ^ 2 ≤ Λ := by
    have : (m : ℝ) ^ 2 ≤ x ^ 2 := by gcongr
    rw [hxsq, le_div_iff₀ hC'pos] at this
    linarith
  have h2 : x / 2 ≤ m := by linarith
  have h3 : 9 / (2 * C') * Λ ≤ 18 * (m : ℝ) ^ 2 := by
    have hx4 : Λ / C' / 4 ≤ (m : ℝ) ^ 2 := by
      have : (x / 2) ^ 2 ≤ (m : ℝ) ^ 2 := by gcongr
      rw [div_pow, hxsq] at this
      linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    rw [div_div, div_le_iff₀ (by positivity)] at hx4
    nlinarith
  have h4 := hC m hm1
  have h4' : (18 * (m : ℝ) ^ 2) ≤ (cuspCount (C * (m : ℝ) ^ 2) : ℝ) := by exact_mod_cast h4
  have hle : C * (m : ℝ) ^ 2 ≤ Λ := le_trans (mul_le_mul_of_nonneg_right hC'C (by positivity)) h1
  have h5 : (cuspCount (C * (m : ℝ) ^ 2) : ℝ) ≤ cuspCount Λ := by exact_mod_cast cuspCount_mono hle
  linarith

end WeylBound

end GaloisForLFunctions.BlackHoleRingdown
