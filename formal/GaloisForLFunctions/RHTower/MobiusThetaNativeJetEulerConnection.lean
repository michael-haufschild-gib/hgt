import GaloisForLFunctions.RHTower.MobiusThetaNativeSecondCollar
import GaloisForLFunctions.RHTower.Deninger.DeningerMobiusConnection

/-!
# Original internal-jet Euler connection on both collars

Raising an original internal theta jet produces its physical logarithmic factor,
the complete von Mangoldt dilation current, and the unchanged finite-prefix term.
The existing exchanged source has the opposite raising sign. Successive admitted
native jets prove absolute convergence of the logarithmic series at every depth.

Each complete all-integer Euler current has a summable scalar pairing against every
Schwartz test at zero damping, using the source-produced zero mass and first moment.
This is admission of the series of pairings. It does not exchange that series with
an integral of its pointwise sum, identify it with a damping-limit derivative, or
identify either construction with the fixed Gamma/BV reader.
-/

set_option autoImplicit false
open Complex MeasureTheory ArithmeticFunction
open scoped SchwartzMap
noncomputable section
namespace RHTower

private def rayTerm (h : SchwartzMap ℝ ℂ) (x : ℝ) (n : ℕ) : ℂ :=
  ((moebius n : ℤ) : ℂ) * deningerLogPull h ((n : ℝ) * x)

private theorem rayTerm_raise (h g : SchwartzMap ℝ ℂ) (c : ℂ)
    (hg : ∀ t : ℝ, g t = c * (t : ℂ) * h t) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    rayTerm g x n = c * ((Real.log x : ℂ) * rayTerm h x n +
      (Real.log (n : ℝ) : ℂ) * rayTerm h x n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [rayTerm]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [rayTerm, deningerLogPull_apply, hg]
  dsimp only [rayTerm, deningerLogPull]
  rw [Real.log_mul hnR.ne' hx.ne']
  push_cast
  ring

private theorem rayLog_summable (h g : DeningerExpSchwartz) {c : ℂ} (hc : c ≠ 0)
    (hg : ∀ t : ℝ, (g : SchwartzMap ℝ ℂ) t = c * (t : ℂ) * (h : SchwartzMap ℝ ℂ) t)
    {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => (Real.log (n : ℝ) : ℂ) * rayTerm h x n) := by
  have hs := deningerMobiusRay_summable h.property hx
  have ht := deningerMobiusRay_summable g.property hx
  have hr : Summable (fun n : ℕ => c * ((Real.log (n : ℝ) : ℂ) * rayTerm h x n)) := by
    apply (ht.sub (hs.mul_left (c * (Real.log x : ℂ)))).congr
    intro n
    change rayTerm g x n - (c * (Real.log x : ℂ)) * rayTerm h x n = _
    rw [rayTerm_raise h g c hg hx n]
    ring
  exact (summable_mul_left_iff hc).mp hr

private theorem rayLog_tsum_eq (h : DeningerExpSchwartz) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, (Real.log (n : ℝ) : ℂ) * rayTerm h x n) =
      -(∑' r : ℕ, (vonMangoldt r : ℂ) * deningerMobiusPreimage h ((r : ℝ) * x)) := by
  rw [deningerMobius_connection h.property hx, deningerMobiusDerivative, ← tsum_neg]
  apply tsum_congr
  intro n
  dsimp only [rayTerm]
  push_cast
  ring

private theorem rayTail_raise (h g : DeningerExpSchwartz) {c : ℂ} (hc : c ≠ 0)
    (hg : ∀ t : ℝ, (g : SchwartzMap ℝ ℂ) t = c * (t : ℂ) * (h : SchwartzMap ℝ ℂ) t)
    (p : ℕ) {x : ℝ} (hx : 0 < x) :
    (∑' j : ℕ, rayTerm g x (p + j)) =
      c * ((Real.log x : ℂ) * (∑' j : ℕ, rayTerm h x (p + j)) -
        (∑' r : ℕ, (vonMangoldt r : ℂ) * deningerMobiusPreimage h ((r : ℝ) * x)) -
        ∑ n ∈ Finset.range p, (Real.log (n : ℝ) : ℂ) * rayTerm h x n) := by
  have hs := deningerMobiusRay_summable h.property hx
  have hl := rayLog_summable h g hc hg hx
  have hst : Summable (fun j : ℕ => rayTerm h x (p + j)) := by
    simpa only [Nat.add_comm, rayTerm] using (_root_.summable_nat_add_iff p).2 hs
  have hlt : Summable (fun j : ℕ =>
      (Real.log ((p + j : ℕ) : ℝ) : ℂ) * rayTerm h x (p + j)) := by
    simpa only [Nat.add_comm] using (_root_.summable_nat_add_iff p).2 hl
  have hsplit : (∑' j : ℕ, (Real.log ((p + j : ℕ) : ℝ) : ℂ) * rayTerm h x (p + j)) =
      (∑' n : ℕ, (Real.log (n : ℝ) : ℂ) * rayTerm h x n) -
        ∑ n ∈ Finset.range p, (Real.log (n : ℝ) : ℂ) * rayTerm h x n := by
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm]
    simpa only [Nat.add_comm] using hl.sum_add_tsum_nat_add p
  calc
    _ = ∑' j : ℕ, c * ((Real.log x : ℂ) * rayTerm h x (p + j) +
        (Real.log ((p + j : ℕ) : ℝ) : ℂ) * rayTerm h x (p + j)) :=
      tsum_congr fun j => rayTerm_raise h g c hg hx (p + j)
    _ = _ := by
      rw [tsum_mul_left, (hst.mul_left (Real.log x : ℂ)).tsum_add hlt,
        tsum_mul_left, hsplit, rayLog_tsum_eq h hx]
      ring

/-- Raising the original internal jet keeps the native depth in the logarithmic factor. -/
theorem mobiusThetaNativeCollarSource_succ (k : ℕ) (m : ℕ+) (t : ℝ) :
    mobiusThetaNativeCollarSource (k + 1) m t =
      (I * (m : ℂ)) * (t : ℂ) * mobiusThetaNativeCollarSource k m t := by
  rw [mobiusThetaNativeCollarSource_apply, mobiusThetaNativeCollarSource_apply, pow_succ]
  push_cast
  ring

/-- The full original Euler current before deleting the finite prime prefix. -/
def mobiusThetaNativeEulerCurrent (k : ℕ) (m : ℕ+) (x : ℝ) : ℂ :=
  ∑' r : ℕ, (vonMangoldt r : ℂ) *
    deningerMobiusPreimage (mobiusThetaNativeCollarSource k m) ((r : ℝ) * x)

/-- The original finite-prefix logarithmic contribution. -/
def mobiusThetaNativeLogPrefix (k p : ℕ) (m : ℕ+) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range p, (Real.log (n : ℝ) : ℂ) *
    (((moebius n : ℤ) : ℂ) *
      deningerLogPull (mobiusThetaNativeCollarSource k m) ((n : ℝ) * x))

/-- The original complete logarithmic source is absolutely admitted at every positive depth. -/
theorem summable_norm_mobiusThetaNativeLogRay (k : ℕ) (m : ℕ+) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => ‖(Real.log (n : ℝ) : ℂ) *
      (((moebius n : ℤ) : ℂ) *
        deningerLogPull (mobiusThetaNativeCollarSource k m) ((n : ℝ) * x))‖) := by
  have hc : I * (m : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast m.ne_zero)
  exact (rayLog_summable
    ⟨_, mobiusThetaNativeCollarSource_mem_deningerExpSchwartz k m⟩
    ⟨_, mobiusThetaNativeCollarSource_mem_deningerExpSchwartz (k + 1) m⟩
    hc (mobiusThetaNativeCollarSource_succ k m) hx).norm

/-- Full jet-raising connection, retaining the original cutoff and every Euler term. -/
theorem mobiusThetaNativeCollarTail_succ_euler (k p : ℕ) (m : ℕ+)
    {x : ℝ} (hx : 0 < x) :
    mobiusThetaNativeCollarTail (k + 1) p m x =
      (I * (m : ℂ)) * ((Real.log x : ℂ) * mobiusThetaNativeCollarTail k p m x -
        mobiusThetaNativeEulerCurrent k m x - mobiusThetaNativeLogPrefix k p m x) := by
  have hc : I * (m : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast m.ne_zero)
  simpa only [mobiusThetaNativeCollarTail, abs_of_pos hx, mobiusThetaNativeEulerCurrent,
    mobiusThetaNativeLogPrefix, rayTerm] using
    rayTail_raise
      ⟨_, mobiusThetaNativeCollarSource_mem_deningerExpSchwartz k m⟩
      ⟨_, mobiusThetaNativeCollarSource_mem_deningerExpSchwartz (k + 1) m⟩
      hc (mobiusThetaNativeCollarSource_succ k m) p hx

private abbrev exchanged (k : ℕ) (m : ℕ+) : DeningerExpSchwartz :=
  DeningerMeyerSource.toSource (mobiusThetaNativeSecondCollarSource k m)

/-- Jet raising reverses sign on the actual exchanged source. -/
theorem mobiusThetaNativeSecondCollarSource_succ (k : ℕ) (m : ℕ+) (t : ℝ) :
    (exchanged (k + 1) m : SchwartzMap ℝ ℂ) t =
      (-(I * (m : ℂ))) * (t : ℂ) * (exchanged k m : SchwartzMap ℝ ℂ) t := by
  change (Real.exp (-t) : ℂ) * mobiusThetaNativeCollarSource (k + 1) m (-t) =
    (-(I * (m : ℂ))) * (t : ℂ) *
      ((Real.exp (-t) : ℂ) * mobiusThetaNativeCollarSource k m (-t))
  rw [mobiusThetaNativeCollarSource_succ]
  push_cast
  ring

/-- The whole Euler current of the unchanged second collar. -/
def mobiusThetaNativeSecondEulerCurrent (k : ℕ) (m : ℕ+) (x : ℝ) : ℂ :=
  ∑' r : ℕ, (vonMangoldt r : ℂ) *
    deningerMobiusPreimage (exchanged k m) ((r : ℝ) * x)

/-- The logarithmic finite prefix on the actual exchanged collar. -/
def mobiusThetaNativeSecondLogPrefix (k p : ℕ) (m : ℕ+) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range p, (Real.log (n : ℝ) : ℂ) *
    (((moebius n : ℤ) : ℂ) * deningerLogPull (exchanged k m) ((n : ℝ) * x))

/-- Absolute admission of the full second logarithmic source at every positive depth. -/
theorem summable_norm_mobiusThetaNativeSecondLogRay
    (k : ℕ) (m : ℕ+) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => ‖(Real.log (n : ℝ) : ℂ) *
      (((moebius n : ℤ) : ℂ) * deningerLogPull (exchanged k m) ((n : ℝ) * x))‖) := by
  have hc : -(I * (m : ℂ)) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero I_ne_zero (by exact_mod_cast m.ne_zero))
  exact (rayLog_summable (exchanged k m) (exchanged (k + 1) m)
    hc (mobiusThetaNativeSecondCollarSource_succ k m) hx).norm

/-- The second complete source has the opposite jet-raising connection, with its entire prefix. -/
theorem mobiusThetaNativeSecondCollarTail_succ_euler (k p : ℕ) (m : ℕ+)
    {x : ℝ} (hx : 0 < x) :
    mobiusThetaNativeSecondCollarTail (k + 1) p m x =
      (-(I * (m : ℂ))) *
        ((Real.log x : ℂ) * mobiusThetaNativeSecondCollarTail k p m x -
          mobiusThetaNativeSecondEulerCurrent k m x -
            mobiusThetaNativeSecondLogPrefix k p m x) := by
  have hc : -(I * (m : ℂ)) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero I_ne_zero (by exact_mod_cast m.ne_zero))
  simpa only [mobiusThetaNativeSecondCollarTail, deningerAdiabaticEvenLogPullDilation,
    abs_of_pos hx, mobiusThetaNativeSecondEulerCurrent,
    mobiusThetaNativeSecondLogPrefix, rayTerm] using
    rayTail_raise (exchanged k m) (exchanged (k + 1) m)
      hc (mobiusThetaNativeSecondCollarSource_succ k m) p hx

private theorem schwartz_lip_zero (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖φ x - φ 0‖ ≤ (SchwartzMap.seminorm ℝ 0 1 φ) * |x| := by
  have hd : ∀ t : ℝ, ‖deriv φ t‖ ≤ SchwartzMap.seminorm ℝ 0 1 φ := by
    intro t
    simpa only [pow_zero, one_mul, iteratedDeriv_one] using φ.le_seminorm' ℝ 0 1 t
  simpa only [sub_zero, Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t (_ : t ∈ (Set.univ : Set ℝ)) => φ.differentiableAt)
      (fun t _ => hd t) convex_univ (Set.mem_univ (0 : ℝ)) (Set.mem_univ x)

private theorem source_causal_summable (h : DeningerExpSchwartz) (φ : SchwartzMap ℝ ℂ) :
    Summable (deningerCausalTerm (deningerMobiusPreimage h) φ) := by
  have hmoment : IntegrableOn
      (fun y : ℝ => (y : ℂ) * deningerMobiusPreimage h y) (Set.Ioi 0) := by
    simpa only [pow_one] using deningerMobiusPreimagePow_integrableOn h.property 1
  apply (deningerCausal_summable_iff (schwartz_lip_zero φ) φ.continuous
    (deningerMobiusPreimage_integrableOn h.property) hmoment).mpr
  rw [deningerMobiusPreimage_mass_eq_zero h.property, zero_mul]

/-- Every Schwartz test admits the original complete Euler current at zero damping. -/
theorem mobiusThetaNativeEulerCurrent_schwartz_pairing_summable
    (k : ℕ) (m : ℕ+) (φ : SchwartzMap ℝ ℂ) :
    Summable (deningerCausalTerm
      (deningerMobiusPreimage (mobiusThetaNativeCollarSource k m)) φ) :=
  source_causal_summable
    ⟨_, mobiusThetaNativeCollarSource_mem_deningerExpSchwartz k m⟩ φ

/-- The same endpoint admission holds for the unchanged exchanged source. -/
theorem mobiusThetaNativeSecondEulerCurrent_schwartz_pairing_summable
    (k : ℕ) (m : ℕ+) (φ : SchwartzMap ℝ ℂ) :
    Summable (deningerCausalTerm (deningerMobiusPreimage (exchanged k m)) φ) :=
  source_causal_summable (exchanged k m) φ

end RHTower
