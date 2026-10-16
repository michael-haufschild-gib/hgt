import GaloisForLFunctions.RHTower.CHMDSinglePrimeWindow

/-!
# Sign law of the prime cross terms on the one-signed odd cone

For an odd test `v` that is nonnegative on the right half-line and supported in `(−L/2, L/2)`,
the cross term of the prime power `n` pairs the points `x` and `x + log n`; when `L ≤ 2 log n`
these lie on opposite sides of the origin, so `v(x) v(x + log n) ≤ 0` and the cross term is
nonpositive. On the window `L ≤ 2 log 2` this holds for every prime power at once, so the whole
explicit-weight prime series is nonpositive and the Doob energy dominates the archimedean Lévy
form of `Θv`. Since `Λ_∞(|f|) ≤ Λ_∞(f)` (the jump energy can only decrease under `f ↦ |f|`), the
energy also dominates the Lévy form of the nonnegative even test `Θ|v|`:

`E(v) ≥ Λ_∞(Θv) ≥ Λ_∞(Θ|v|)` for odd `v ≥ 0` on `[0,∞)` with `supp v ⊆ (−log 2, log 2)`.

On this cone the primes `2` and `3` are active, yet positivity of the arithmetic energy follows from
a prime-free statement about nonnegative even tests of support length up to `2 log 2`.
-/

open MeasureTheory Set Filter Topology Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph

/-! ## The sign of a cross term on the one-signed odd cone -/

/-- On the one-signed odd cone, the cross term of `n` is nonpositive once `L ≤ 2 log n`. -/
theorem phiDoobPrimeCross_nonpos_of_odd_oneSigned {v : ℝ → ℝ} (hodd : ∀ x, v (-x) = -v x)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ v x) {L : ℝ} (hsupp : ∀ x ∉ Ioo (-(L / 2)) (L / 2), v x = 0)
    {n : ℕ} (hn : L ≤ 2 * Real.log n) (x : ℝ) : phiDoobPrimeCross v n x ≤ 0 := by
  unfold phiDoobPrimeCross
  by_cases hx : x ∈ Ioo (-(L / 2)) (L / 2)
  · by_cases hx' : x + Real.log n ∈ Ioo (-(L / 2)) (L / 2)
    · have hv1 : v x ≤ 0 := by
        have h := hpos (-x) (by linarith [hx'.2])
        rw [hodd] at h
        linarith
      have hv2 : 0 ≤ v (x + Real.log n) := hpos _ (by linarith [hx.1])
      have h1 : 2 * vonMangoldtAtom n * riemannKernelReal x * riemannKernelReal (x + Real.log n) *
          v x ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inl ⟨mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
          (vonMangoldtAtom_nonneg n)) (riemannKernelReal_pos x).le)
          (riemannKernelReal_pos _).le, hv1⟩)
      exact mul_nonpos_iff.mpr (Or.inr ⟨h1, hv2⟩)
    · rw [hsupp _ hx']
      simp
  · rw [hsupp x hx]
    simp

theorem integral_phiDoobPrimeCross_nonpos_of_odd_oneSigned {v : ℝ → ℝ}
    (hodd : ∀ x, v (-x) = -v x) (hpos : ∀ x, 0 ≤ x → 0 ≤ v x) {L : ℝ}
    (hsupp : ∀ x ∉ Ioo (-(L / 2)) (L / 2), v x = 0) {n : ℕ} (hn : L ≤ 2 * Real.log n) :
    ∫ x, phiDoobPrimeCross v n x ≤ 0 :=
  integral_nonpos fun x => phiDoobPrimeCross_nonpos_of_odd_oneSigned hodd hpos hsupp hn x

/-- On the window `L ≤ 2 log 2` every prime cross term is nonpositive on the one-signed odd cone. -/
theorem tsum_cross_nonpos_of_odd_oneSigned {v : ℝ → ℝ} (hodd : ∀ x, v (-x) = -v x)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ v x) {L : ℝ} (hsupp : ∀ x ∉ Ioo (-(L / 2)) (L / 2), v x = 0)
    (hL : L ≤ 2 * Real.log 2) :
    ∑' n : ℕ, ∫ x, phiDoobPrimeCross v n x ≤ 0 := by
  refine tsum_nonpos fun n => ?_
  rcases lt_or_ge n 2 with hn | hn
  · have h : (fun x => phiDoobPrimeCross v n x) = fun _ => 0 :=
      funext (phiDoobPrimeCross_eq_zero_of_lt_two v hn)
    rw [h, integral_zero]
  · apply integral_phiDoobPrimeCross_nonpos_of_odd_oneSigned hodd hpos hsupp
    calc L ≤ 2 * Real.log 2 := hL
      _ ≤ 2 * Real.log n := by
        have h2 : Real.log 2 ≤ Real.log n :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hn)
        linarith

/-- **Prime help on the one-signed odd cone.** With support in `(−log 2, log 2)` the Doob energy
dominates the archimedean Lévy form of `Θv`. -/
theorem levy_le_sourceEnergy_of_odd_oneSigned (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x) (hpos : ∀ x, 0 ≤ x → 0 ≤ v x)
    {L : ℝ} (hsupp : ∀ x ∉ Ioo (-(L / 2)) (L / 2), v x = 0) (hL : L ≤ 2 * Real.log 2) :
    weilLevyForm (phiDoobTest v) ≤ sourceEnergy (compactLift v hv hvc) := by
  rw [sourceEnergy_compactLift_eq_levy_sub_tsum_cross]
  linarith [tsum_cross_nonpos_of_odd_oneSigned hodd hpos hsupp hL]

/-! ## The diamagnetic bound `Λ_∞(|f|) ≤ Λ_∞(f)` -/

theorem sq_abs_sub_abs_le (a b : ℝ) : (|a| - |b|) ^ 2 ≤ (a - b) ^ 2 := by
  have h := abs_abs_sub_abs_le_abs_sub a b
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rwa [sq_abs, sq_abs] at h2

theorem integral_sq_abs_sub_le {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : ℝ) :
    (∫ u, (|f u| - |f (u + x)|) ^ 2) ≤ ∫ u, (f u - f (u + x)) ^ 2 := by
  have hcs : HasCompactSupport fun u => f u - f (u + x) :=
    hfc.sub (hfc.comp_homeomorph (Homeomorph.addRight x))
  have hc : Continuous fun u => f u - f (u + x) :=
    hf.sub (hf.comp (continuous_id.add continuous_const))
  have hint : Integrable fun u => (f u - f (u + x)) ^ 2 := by
    have e : (fun u => (f u - f (u + x)) ^ 2) =
        (fun u => f u - f (u + x)) * (fun u => f u - f (u + x)) := by
      funext u
      simp [pow_two]
    rw [e]
    exact (hc.mul hc).integrable_of_hasCompactSupport hcs.mul_left
  exact integral_mono_of_nonneg (Eventually.of_forall fun u => sq_nonneg _) hint
    (Eventually.of_forall fun u => sq_abs_sub_abs_le _ _)

theorem jumpEnergy_abs_le {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    NonnegativeCone.jumpEnergy (fun u => |f u|) ≤ NonnegativeCone.jumpEnergy f := by
  unfold NonnegativeCone.jumpEnergy
  refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (integral_sq_abs_sub_le hf hfc x) (archLevyDensity_pos hx).le

/-- **Diamagnetic bound**: the Lévy form can only decrease under `f ↦ |f|`. -/
theorem weilLevyForm_abs_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    weilLevyForm (fun u => |f u|) ≤ weilLevyForm f := by
  unfold weilLevyForm
  have h1 : (∫ u, |f u| ^ 2) = ∫ u, f u ^ 2 := by
    congr 1
    funext u
    exact sq_abs _
  rw [h1]
  have h2 := ENNReal.toReal_mono (NonnegativeCone.jumpEnergy_ne_top_of_smooth hf hfc)
    (jumpEnergy_abs_le hf.continuous hfc)
  linarith

theorem abs_phiDoobTest (v : ℝ → ℝ) (x : ℝ) :
    |phiDoobTest v x| = phiDoobTest (fun y => |v y|) x := by
  unfold phiDoobTest
  rw [abs_mul, abs_of_pos (riemannKernelReal_pos x)]

/-- **Prime-free lower bound on the one-signed odd cone.** For odd `v ≥ 0` on `[0,∞)` supported in
`(−log 2, log 2)`, the arithmetic Doob energy dominates the archimedean Lévy form of the
nonnegative even test `Θ|v|`. -/
theorem levy_abs_le_sourceEnergy_of_odd_oneSigned (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x) (hpos : ∀ x, 0 ≤ x → 0 ≤ v x)
    {L : ℝ} (hsupp : ∀ x ∉ Ioo (-(L / 2)) (L / 2), v x = 0) (hL : L ≤ 2 * Real.log 2) :
    weilLevyForm (phiDoobTest fun y => |v y|) ≤ sourceEnergy (compactLift v hv hvc) := by
  have h1 := levy_le_sourceEnergy_of_odd_oneSigned v hv hvc hodd hpos hsupp hL
  have h2 := weilLevyForm_abs_le (contDiff_phiDoobTest hv) (hasCompactSupport_phiDoobTest hvc)
  have h3 : (fun u => |phiDoobTest v u|) = phiDoobTest fun y => |v y| := funext (abs_phiDoobTest v)
  rw [h3] at h2
  exact h2.trans h1

/-- On the one-signed odd cone with support in `(−log 2, log 2)`, nonnegativity of the Lévy form
of the even test `Θ|v|` gives nonnegative arithmetic energy, with both primes `2` and `3` active. -/
theorem sourceEnergy_nonneg_of_levy_abs_nonneg (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x) (hpos : ∀ x, 0 ≤ x → 0 ≤ v x)
    {L : ℝ} (hsupp : ∀ x ∉ Ioo (-(L / 2)) (L / 2), v x = 0) (hL : L ≤ 2 * Real.log 2)
    (hlevy : 0 ≤ weilLevyForm (phiDoobTest fun y => |v y|)) :
    0 ≤ sourceEnergy (compactLift v hv hvc) :=
  hlevy.trans (levy_abs_le_sourceEnergy_of_odd_oneSigned v hv hvc hodd hpos hsupp hL)

end RHTower.CHMDPolar
