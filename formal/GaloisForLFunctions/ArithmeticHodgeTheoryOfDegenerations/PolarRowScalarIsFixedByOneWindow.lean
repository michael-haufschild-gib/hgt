import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# One window identifies a scalar row profile

A nonvanishing bounded test pairing identifies the coefficient of an approximate
scalar line. Quantitative stability upgrades weak identification to strong convergence.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- A single nonvanishing test pairing identifies a scalar profile, with an explicit stable
bound in the ambient Hilbert norm. -/
theorem norm_sub_smul_le_of_scalar_approximation {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (x v h : V) {a : ℝ} (ha : 0 < a)
    (hpair : a ≤ ⟪v, h⟫) (s t : ℝ) :
    ‖x - s • v‖ ≤ ‖x - t • v‖ * (1 + ‖v‖ * ‖h‖ / a) +
      (‖v‖ / a) * |⟪x, h⟫ - s * ⟪v, h⟫| := by
  let e := x - t • v
  have he : x - s • v = e + (t - s) • v := by dsimp only [e]; module
  have hdecomp : (t - s) * ⟪v, h⟫ =
      (⟪x, h⟫ - s * ⟪v, h⟫) - ⟪e, h⟫ := by
    dsimp only [e]
    rw [inner_sub_left, real_inner_smul_left]
    ring
  have hcoeff : |t - s| ≤ (|⟪x, h⟫ - s * ⟪v, h⟫| + ‖e‖ * ‖h‖) / a := by
    apply (le_div_iff₀ ha).mpr
    calc
      |t - s| * a ≤ |t - s| * ⟪v, h⟫ := mul_le_mul_of_nonneg_left hpair (abs_nonneg _)
      _ = |(t - s) * ⟪v, h⟫| := by rw [abs_mul, abs_of_pos (ha.trans_le hpair)]
      _ = |(⟪x, h⟫ - s * ⟪v, h⟫) - ⟪e, h⟫| := by rw [hdecomp]
      _ ≤ |⟪x, h⟫ - s * ⟪v, h⟫| + ‖e‖ * ‖h‖ :=
        (abs_sub _ _).trans (add_le_add le_rfl (abs_real_inner_le_norm e h))
  calc
    _ ≤ ‖e‖ + |t - s| * ‖v‖ := by
      rw [he]
      simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le e ((t-s) • v)
    _ ≤ ‖e‖ + ((|⟪x, h⟫ - s * ⟪v, h⟫| + ‖e‖ * ‖h‖) / a) * ‖v‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _))
    _ = _ := by dsimp only [e]; ring

/-- Approximation by a scalar line becomes strong convergence once a single nonvanishing
bounded test pairing has the required limit. The Hilbert spaces may vary with the horizon. -/
theorem tendsto_norm_sub_smul_of_scalar_line_approximation
    {V : ℕ → Type*} [∀ N, NormedAddCommGroup (V N)] [∀ N, InnerProductSpace ℝ (V N)]
    (x v h : (N : ℕ) → V N) {a B C s : ℝ} (ha : 0 < a) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hv : ∀ᶠ N in Filter.atTop, ‖v N‖ ≤ B)
    (hh : ∀ᶠ N in Filter.atTop, ‖h N‖ ≤ C)
    (hp : ∀ᶠ N in Filter.atTop, a ≤ ⟪v N, h N⟫)
    (happrox : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in Filter.atTop,
      ∃ t : ℝ, ‖x N - t • v N‖ ≤ ε)
    (hweak : Filter.Tendsto (fun N => ⟪x N, h N⟫ - s * ⟪v N, h N⟫)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N => ‖x N - s • v N‖) Filter.atTop (nhds 0) := by
  let D := 1 + B * C / a
  let E := B / a
  have hD : 0 < D := by dsimp only [D]; positivity
  have hE : 0 ≤ E := div_nonneg hB ha.le
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Filter.Eventually.of_forall fun N => hb.trans_le (norm_nonneg _)
  · intro ε hε
    have hweakAbs : Filter.Tendsto (fun N => |⟪x N, h N⟫ - s * ⟪v N, h N⟫|)
        Filter.atTop (nhds 0) := by simpa only [abs_zero] using hweak.abs
    filter_upwards [hv, hh, hp, happrox (ε / (2 * D)) (by positivity),
      hweakAbs.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / (2 * (E + 1))))]
      with N hvN hhN hpN happroxN hweakN
    obtain ⟨t, ht⟩ := happroxN
    have hd : 1 + ‖v N‖ * ‖h N‖ / a ≤ D :=
      add_le_add le_rfl (div_le_div_of_nonneg_right
        (mul_le_mul hvN hhN (norm_nonneg _) hB) ha.le)
    have he : ‖v N‖ / a ≤ E := div_le_div_of_nonneg_right hvN ha.le
    have hfirst : ‖x N - t • v N‖ * (1 + ‖v N‖ * ‖h N‖ / a) ≤ ε / 2 := by
      calc
        _ ≤ (ε / (2 * D)) * D := mul_le_mul ht hd (by positivity) (by positivity)
        _ = ε / 2 := by field_simp [hD.ne']
    have hsecond : (‖v N‖ / a) * |⟪x N, h N⟫ - s * ⟪v N, h N⟫| < ε / 2 := by
      have hsmall : E * (ε / (2 * (E + 1))) < ε / 2 := by
        rw [← mul_div_assoc]
        apply (div_lt_iff₀ (by positivity : 0 < 2 * (E + 1))).mpr
        nlinarith only [hε]
      calc
        _ ≤ E * (ε / (2 * (E + 1))) :=
          mul_le_mul he hweakN.le (abs_nonneg _) hE
        _ < ε / 2 := hsmall
    have hb := norm_sub_smul_le_of_scalar_approximation (x N) (v N) (h N) ha hpN s t
    linarith only [hb, hfirst, hsecond]

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
