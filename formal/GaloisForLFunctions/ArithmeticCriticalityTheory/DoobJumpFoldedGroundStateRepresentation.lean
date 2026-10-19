import GaloisForLFunctions.ArithmeticCriticalityTheory.GroundStateRepresentationAlgebra
import GaloisForLFunctions.RHTower.WeilPhiDoobArchimedeanJumpAndHalfLineFolding
import GaloisForLFunctions.RHTower.WeilPhiDoobReflectedKillingPotentialAndDisjointSupportDiagonal

/-!
# Folded ground-state representation of one Doob shift jump

For an odd Doob test `v = ω u` (`ω` odd, `u` even, continuous, compactly supported) and a shift
`t ≥ 0`, the full-line Doob jump `∫ Φ(x)Φ(x+t)(v(x) − v(x+t))² dx` is folded onto the half line and
each piece is expanded with the ground-state identities. The result is exact:

    ∫_ℝ Φ(x)Φ(x+t)(v(x) − v(x+t))² dx
      = 2∫_{x>0} Φ(x)Φ(x+t) ω(x)ω(x+t) (u(x) − u(x+t))² dx
        + ∫_{0<x<t} Φ(x)Φ(t−x) ω(x)ω(t−x) (u(x) + u(t−x))² dx
        + 2∫_{x>0} u(x)² ω(x) · Φ(x)[Φ(x+t)(ω(x) − ω(x+t)) + Φ(x−t)(ω(x) − ω(|x−t|))] dx.

The last bracket is the folded (Neumann) single-shift generator: on `(0,∞)` it is the two-sided
generator applied to the even reflection `|ω|`. Its difference from the two-sided generator of the
odd function `ω` is the reflected collar `2Φ(x)Φ(t−x) ω(t−x)⁺`. The first two terms are nonnegative
when `ω` is positive on `(0,∞)`.
-/

open MeasureTheory Set Filter Topology
open RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The folded (Neumann) single-shift generator at shift `t`, evaluated at `x`. -/
def foldedShiftGenerator (ω : ℝ → ℝ) (t x : ℝ) : ℝ :=
  riemannKernelReal x * (riemannKernelReal (x + t) * (ω x - ω (x + t)) +
    riemannKernelReal (x - t) * (ω x - ω |x - t|))

/-- The two-sided (Dirichlet) single-shift generator at shift `t`, evaluated at `x`. -/
def twoSidedShiftGenerator (ω : ℝ → ℝ) (t x : ℝ) : ℝ :=
  riemannKernelReal x * (riemannKernelReal (x + t) * (ω x - ω (x + t)) +
    riemannKernelReal (x - t) * (ω x - ω (x - t)))

/-- Same-side ground-state jump `Φ(x)Φ(x+t) ω(x)ω(x+t) (u(x) − u(x+t))²`. -/
def sameSideGroundJump (ω u : ℝ → ℝ) (t x : ℝ) : ℝ :=
  riemannKernelReal x * riemannKernelReal (x + t) * ω x * ω (x + t) * (u x - u (x + t)) ^ 2

/-- Reflected ground-state jump `Φ(x)Φ(t−x) ω(x)ω(t−x) (u(x) + u(t−x))²` on the collar `0 < x < t`. -/
def reflectedGroundJump (ω u : ℝ → ℝ) (t x : ℝ) : ℝ :=
  riemannKernelReal x * riemannKernelReal (t - x) * ω x * ω (t - x) * (u x + u (t - x)) ^ 2

theorem riemannKernelReal_neg' (x : ℝ) : riemannKernelReal (-x) = riemannKernelReal x := by
  simp [riemannKernelReal]

theorem riemannKernelReal_abs' (x : ℝ) : riemannKernelReal |x| = riemannKernelReal x := by
  simp [riemannKernelReal]

theorem odd_apply_zero {ω : ℝ → ℝ} (hodd : ∀ x, ω (-x) = -ω x) : ω 0 = 0 := by
  have h := hodd 0
  rw [neg_zero] at h
  linarith

/-- The two generators differ by the reflected collar `2Φ(x)Φ(t−x) ω(t−x)⁺`. -/
theorem twoSidedShiftGenerator_eq_folded_add_collar {ω : ℝ → ℝ} (hodd : ∀ x, ω (-x) = -ω x)
    (hpos : ∀ x, 0 < x → 0 < ω x) {t x : ℝ} (hx : 0 < x) :
    twoSidedShiftGenerator ω t x =
      foldedShiftGenerator ω t x +
        2 * riemannKernelReal x * riemannKernelReal (t - x) * max (ω (t - x)) 0 := by
  unfold twoSidedShiftGenerator foldedShiftGenerator
  rcases lt_trichotomy x t with h | h | h
  · have habs : |x - t| = t - x := by
      rw [abs_of_neg (by linarith)]
      ring
    have hneg : ω (x - t) = -ω (t - x) := by
      rw [show x - t = -(t - x) by ring, hodd]
    have hΦ : riemannKernelReal (x - t) = riemannKernelReal (t - x) := by
      rw [show x - t = -(t - x) by ring, riemannKernelReal_neg']
    rw [habs, hneg, hΦ, max_eq_left (hpos _ (by linarith)).le]
    ring
  · subst h
    rw [sub_self, abs_zero, odd_apply_zero hodd, max_self]
    ring
  · have habs : |x - t| = x - t := abs_of_pos (by linarith)
    have hle : ω (t - x) ≤ 0 := by
      rw [show t - x = -(x - t) by ring, hodd]
      linarith [hpos _ (by linarith : 0 < x - t)]
    rw [habs, max_eq_right hle]
    ring

theorem sameSideGroundJump_nonneg {ω u : ℝ → ℝ} (hpos : ∀ x, 0 < x → 0 ≤ ω x) {t x : ℝ}
    (ht : 0 ≤ t) (hx : 0 < x) : 0 ≤ sameSideGroundJump ω u t x := by
  unfold sameSideGroundJump
  have h1 := riemannKernelReal_pos x
  have h2 := riemannKernelReal_pos (x + t)
  have h3 := hpos x hx
  have h4 := hpos (x + t) (by linarith)
  positivity

theorem reflectedGroundJump_nonneg {ω u : ℝ → ℝ} (hpos : ∀ x, 0 < x → 0 ≤ ω x) {t x : ℝ}
    (hx : 0 < x) (hxt : x < t) : 0 ≤ reflectedGroundJump ω u t x := by
  unfold reflectedGroundJump
  have h1 := riemannKernelReal_pos x
  have h2 := riemannKernelReal_pos (t - x)
  have h3 := hpos x hx
  have h4 := hpos (t - x) (by linarith)
  positivity

theorem hasCompactSupport_sq {u : ℝ → ℝ} (huc : HasCompactSupport u) :
    HasCompactSupport fun x => u x ^ 2 := by
  rw [hasCompactSupport_iff_eventuallyEq] at huc ⊢
  filter_upwards [huc] with x hx
  simp [hx]

/-- A continuous function times the square of a continuous compactly supported function is
integrable on every set. -/
theorem integrableOn_continuous_mul_sq {g u : ℝ → ℝ} (hg : Continuous g) (hu : Continuous u)
    (huc : HasCompactSupport u) (s : Set ℝ) : IntegrableOn (fun x => g x * u x ^ 2) s :=
  ((hg.mul (hu.pow 2)).integrable_of_hasCompactSupport
    (hasCompactSupport_sq huc).mul_left).integrableOn

theorem continuous_shift {u : ℝ → ℝ} (hu : Continuous u) (t : ℝ) :
    Continuous fun x => u (x + t) :=
  hu.comp (continuous_id.add continuous_const)

theorem hasCompactSupport_shift {u : ℝ → ℝ} (huc : HasCompactSupport u) (t : ℝ) :
    HasCompactSupport fun x => u (x + t) :=
  huc.comp_homeomorph (Homeomorph.addRight t)

/-- **Folded ground-state representation of one shift jump.** -/
theorem integral_phiDoobArchShiftJump_groundState {ω u : ℝ → ℝ} (hω : Continuous ω)
    (hodd : ∀ x, ω (-x) = -ω x) (hu : Continuous u) (huc : HasCompactSupport u)
    (heven : ∀ x, u (-x) = u x) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : ℝ, phiDoobArchShiftJump (fun y => ω y * u y) t x) =
      2 * (∫ x in Ioi (0 : ℝ), sameSideGroundJump ω u t x) +
        (∫ x in Ioo (0 : ℝ) t, reflectedGroundJump ω u t x) +
        2 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * ω x * foldedShiftGenerator ω t x := by
  set v : ℝ → ℝ := fun y => ω y * u y with hv_def
  have hv : Continuous v := hω.mul hu
  have hvc : HasCompactSupport v := huc.mul_left
  have hvodd : ∀ x, v (-x) = -v x := by
    intro x
    simp only [hv_def, hodd x, heven x]
    ring
  rw [integral_phiDoobArchShiftJump_eq_halfLine_of_odd hv hvc hvodd ht]
  -- the pieces
  set Φ := riemannKernelReal with hΦ_def
  set a : ℝ → ℝ := fun x => Φ x * Φ (x + t) * (ω x - ω (x + t)) * ω x * u x ^ 2 with ha_def
  set b : ℝ → ℝ := fun y => Φ (y - t) * Φ y * (ω (y - t) - ω y) * ω y * u y ^ 2 with hb_def
  set c : ℝ → ℝ := fun x => Φ x * Φ (t - x) * (ω x - ω (t - x)) * ω x * u x ^ 2 with hc_def
  set d : ℝ → ℝ := fun x => Φ x * Φ (x - t) * (ω x - ω |x - t|) * ω x * u x ^ 2 with hd_def
  have hΦc : Continuous Φ := continuous_riemannKernelReal
  -- integrability of the pieces
  have hint_same : IntegrableOn (sameSideGroundJump ω u t) (Ioi 0) := by
    have : sameSideGroundJump ω u t =
        fun x => (Φ x * Φ (x + t) * ω x * ω (x + t)) * (u x - u (x + t)) ^ 2 := by
      funext x; simp only [sameSideGroundJump]
    rw [this]
    exact integrableOn_continuous_mul_sq
      (((hΦc.mul (hΦc.comp (continuous_id.add continuous_const))).mul hω).mul
        (hω.comp (continuous_id.add continuous_const)))
      (hu.sub (continuous_shift hu t)) (huc.sub (hasCompactSupport_shift huc t)) _
  have hint_a : IntegrableOn a (Ioi 0) :=
    integrableOn_continuous_mul_sq
      (((hΦc.mul (hΦc.comp (continuous_id.add continuous_const))).mul
        (hω.sub (hω.comp (continuous_id.add continuous_const)))).mul hω) hu huc _
  have hint_bshift : IntegrableOn (fun x => b (x + t)) (Ioi 0) := by
    have : (fun x => b (x + t)) =
        fun x => (Φ (x + t - t) * Φ (x + t) * (ω (x + t - t) - ω (x + t)) * ω (x + t)) *
          u (x + t) ^ 2 := by
      funext x; simp only [hb_def]
    rw [this]
    exact integrableOn_continuous_mul_sq
      (((hΦc.comp ((continuous_id.add continuous_const).sub continuous_const)).mul
        (hΦc.comp (continuous_id.add continuous_const))).mul
        ((hω.comp ((continuous_id.add continuous_const).sub continuous_const)).sub
          (hω.comp (continuous_id.add continuous_const))) |>.mul
        (hω.comp (continuous_id.add continuous_const)))
      (continuous_shift hu t) (hasCompactSupport_shift huc t) _
  have hint_b : IntegrableOn b (Ioi t) :=
    integrableOn_continuous_mul_sq
      (((hΦc.comp (continuous_id.sub continuous_const)).mul hΦc).mul
        ((hω.comp (continuous_id.sub continuous_const)).sub hω) |>.mul hω) hu huc _
  have hint_d : IntegrableOn d (Ioi 0) :=
    integrableOn_continuous_mul_sq
      (((hΦc.mul (hΦc.comp (continuous_id.sub continuous_const))).mul
        (hω.sub (hω.comp (continuous_abs.comp (continuous_id.sub continuous_const))))).mul hω)
      hu huc _
  have hc_cont : Continuous c :=
    ((((hΦc.mul (hΦc.comp (continuous_const.sub continuous_id))).mul
      (hω.sub (hω.comp (continuous_const.sub continuous_id)))).mul hω).mul (hu.pow 2))
  have hint_c : IntegrableOn c (Ioo 0 t) :=
    (hc_cont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hint_refl : IntegrableOn (reflectedGroundJump ω u t) (Ioo 0 t) := by
    have hcont : Continuous (reflectedGroundJump ω u t) := by
      unfold reflectedGroundJump
      exact ((((hΦc.mul (hΦc.comp (continuous_const.sub continuous_id))).mul hω).mul
        (hω.comp (continuous_const.sub continuous_id))).mul
        ((hu.add (hu.comp (continuous_const.sub continuous_id))).pow 2))
    exact (hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  -- same-side expansion
  have hsame : (∫ x in Ioi (0 : ℝ), phiDoobArchShiftJump v t x) =
      (∫ x in Ioi (0 : ℝ), sameSideGroundJump ω u t x) +
        (∫ x in Ioi (0 : ℝ), a x) + ∫ x in Ioi (0 : ℝ), -b (x + t) := by
    rw [← integral_add hint_same hint_a, ← integral_add (hint_same.add hint_a) hint_bshift.neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [phiDoobArchShiftJump, hv_def, sameSideGroundJump, ha_def, hb_def, Pi.add_apply,
      Pi.neg_apply, hΦ_def, add_sub_cancel_right]
    ring
  -- the shifted piece
  have hshift : (∫ x in Ioi (0 : ℝ), -b (x + t)) = -∫ y in Ioi t, b y := by
    rw [integral_neg]
    congr 1
    have hmp : MeasurePreserving (fun x : ℝ => x + t) volume volume :=
      measurePreserving_add_right volume t
    have hemb : MeasurableEmbedding (fun x : ℝ => x + t) :=
      (Homeomorph.addRight t).measurableEmbedding
    have hpre : (fun x : ℝ => x + t) ⁻¹' Ioi t = Ioi (0 : ℝ) := by
      ext x
      simp
    have htr := hmp.setIntegral_preimage_emb hemb b (Ioi t)
    rw [hpre] at htr
    exact htr
  -- reflected expansion
  have hrefl : (∫ x in Ioo (0 : ℝ) t,
      riemannKernelReal x * riemannKernelReal (t - x) * (v x + v (t - x)) ^ 2) =
      (∫ x in Ioo (0 : ℝ) t, reflectedGroundJump ω u t x) + 2 * ∫ x in Ioo (0 : ℝ) t, c x := by
    have hcr : IntegrableOn (fun x => c (t - x)) (Ioo 0 t) := by
      have : Continuous fun x => c (t - x) := hc_cont.comp (continuous_const.sub continuous_id)
      exact (this.integrableOn_Icc).mono_set Ioo_subset_Icc_self
    have hsplit : (∫ x in Ioo (0 : ℝ) t,
        riemannKernelReal x * riemannKernelReal (t - x) * (v x + v (t - x)) ^ 2) =
        (∫ x in Ioo (0 : ℝ) t, reflectedGroundJump ω u t x) +
          (∫ x in Ioo (0 : ℝ) t, c x) + ∫ x in Ioo (0 : ℝ) t, c (t - x) := by
      rw [← integral_add hint_refl hint_c, ← integral_add (hint_refl.add hint_c) hcr]
      refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
      simp only [hv_def, reflectedGroundJump, hc_def, Pi.add_apply, hΦ_def, sub_sub_cancel]
      ring
    rw [hsplit, setIntegral_Ioo_reflect_self c t]
    ring
  -- the potential: split `Ioi 0 = Ioo 0 t ∪ Ioi t`
  have hpot : (∫ x in Ioi (0 : ℝ), u x ^ 2 * ω x * foldedShiftGenerator ω t x) =
      (∫ x in Ioi (0 : ℝ), a x) + ((∫ x in Ioo (0 : ℝ) t, c x) - ∫ y in Ioi t, b y) := by
    have had : (∫ x in Ioi (0 : ℝ), u x ^ 2 * ω x * foldedShiftGenerator ω t x) =
        (∫ x in Ioi (0 : ℝ), a x) + ∫ x in Ioi (0 : ℝ), d x := by
      rw [← integral_add hint_a hint_d]
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      simp only [foldedShiftGenerator, ha_def, hd_def, Pi.add_apply, hΦ_def]
      ring
    have hd_split : (∫ x in Ioi (0 : ℝ), d x) =
        (∫ x in Ioo (0 : ℝ) t, d x) + ∫ x in Ioi t, d x := by
      rw [← Ioc_union_Ioi_eq_Ioi ht,
        setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          (hint_d.mono_set Ioc_subset_Ioi_self) (hint_d.mono_set (Ioi_subset_Ioi ht)),
        integral_Ioc_eq_integral_Ioo]
    have hdc : (∫ x in Ioo (0 : ℝ) t, d x) = ∫ x in Ioo (0 : ℝ) t, c x := by
      refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      simp only [hd_def, hc_def, hΦ_def]
      have habs : |x - t| = t - x := by
        rw [abs_of_neg (by linarith [hx.2])]
        ring
      rw [habs, show x - t = -(t - x) by ring, riemannKernelReal_neg']
    have hdb : (∫ x in Ioi t, d x) = -∫ y in Ioi t, b y := by
      rw [← integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      simp only [hd_def, hb_def, hΦ_def, Pi.neg_apply]
      rw [abs_of_pos (by linarith [mem_Ioi.mp hx])]
      ring
    rw [had, hd_split, hdc, hdb]
    ring
  rw [hsame, hshift, hrefl, hpot]
  ring

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
