import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheAbelEscapeAtomsOfZetaAreItsDominantZeros
import GaloisForLFunctions.SelbergClass.DegreeOne.AbelianBoundaryLimit

/-!
# A summatory power asymptotic excludes nonreal boundary residues

A power asymptotic becomes a convergent bounded profile on logarithmic
coordinates. The nonresonant Abelian theorem then makes every nonreal
boundary residue of the summatory Mellin pairing vanish.
-/

noncomputable section

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open TransHorizonIncidenceMechanics (complexMellinPairing complexMellinCell norm_complexMellinCell_le)
open SelbergClass.DegreeOne

/-- A normalized summatory limit supplies an exact power bound. -/
theorem exists_power_bound_of_normalized_tendsto {f : ℕ → ℝ} (hf0 : f 0 = 0)
    {θ L : ℝ} (hf : Tendsto (fun N : ℕ => (N : ℝ) ^ (-θ) * f N) atTop (𝓝 L)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |f N| ≤ C * (N : ℝ) ^ θ := by
  obtain ⟨B, hB⟩ := hf.abs.bddAbove_range
  refine ⟨|B|, abs_nonneg _, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [hf0, abs_zero]
    positivity
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hb := (hB ⟨N, rfl⟩).trans (le_abs_self B)
  change |(N : ℝ) ^ (-θ) * f N| ≤ |B| at hb
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hNp _)] at hb
  have hm := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hNp.le θ)
  rw [← mul_assoc, ← Real.rpow_add hNp, add_neg_cancel, Real.rpow_zero, one_mul] at hm
  simpa only [mul_comm] using hm

/-- A strict exponent gap makes the summatory Mellin majorant summable. -/
theorem summable_mellin_majorant_of_power_bound
    {f : ℕ → ℝ} (hf0 : f 0 = 0) {C θ σ : ℝ}
    (hbound : ∀ N : ℕ, |f N| ≤ C * (N : ℝ) ^ θ) (hgap : θ < σ) :
    Summable fun n : ℕ => |f n| * (n : ℝ) ^ (-σ - 1) := by
  apply ((Real.summable_nat_rpow.mpr
    (show θ - σ - 1 < -1 by linarith only [hgap])).mul_left C).of_nonneg_of_le
      (fun n => by positivity)
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [hf0, abs_zero, zero_mul]
    have hC : 0 ≤ C := by simpa only [Nat.cast_one, Real.one_rpow, mul_one] using
      (abs_nonneg (f 1)).trans (hbound 1)
    positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ (C * (n : ℝ) ^ θ) * (n : ℝ) ^ (-σ - 1) :=
      mul_le_mul_of_nonneg_right (hbound n) (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hn0]; congr 2; ring

/-- Pointwise power growth gives holomorphy throughout the corresponding
open Mellin half-plane, including exponents below one half. -/
theorem differentiableOn_complexMellinPairing_of_power_bound
    {f : ℕ → ℝ} (hf0 : f 0 = 0) {C θ : ℝ} (hθ : 0 ≤ θ)
    (hbound : ∀ N : ℕ, |f N| ≤ C * (N : ℝ) ^ θ) :
    DifferentiableOn ℂ (complexMellinPairing f) {s : ℂ | θ < s.re} := by
  intro s₀ hs₀
  change θ < s₀.re at hs₀
  let b := (θ + s₀.re) / 2
  have hb : θ < b := by dsimp only [b]; linarith only [hs₀]
  have hbs : b < s₀.re := by dsimp only [b]; linarith only [hs₀]
  have hb0 : 0 < b := hθ.trans_lt hb
  let R := ‖s₀‖ + 1
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  let U : Set ℂ := {s | b < s.re} ∩ {s | ‖s‖ < R}
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_norm continuous_const)
  have hsU : s₀ ∈ U := by
    change b < s₀.re ∧ ‖s₀‖ < ‖s₀‖ + 1
    exact ⟨hbs, lt_add_one _⟩
  have hsum := (summable_mellin_majorant_of_power_bound hf0 hbound hb).mul_left R
  have hdiff : DifferentiableOn ℂ (complexMellinPairing f) U := by
    apply Complex.differentiableOn_tsum_of_summable_norm
      (F := fun n s => (f n : ℂ) * complexMellinCell s n) hsum ?_ hU ?_
    · intro n s hs
      change b < s.re ∧ ‖s‖ < R at hs
      have hsne : -s ≠ 0 := neg_ne_zero.mpr fun hz => by
        have hh : b < s.re := hs.1
        rw [hz, Complex.zero_re] at hh
        exact (not_lt_of_ge hb0.le) hh
      exact ((differentiableAt_const _).mul
        ((differentiableAt_id.neg.const_cpow (Or.inr hsne)).sub
          (differentiableAt_id.neg.const_cpow (Or.inr hsne)))).differentiableWithinAt
    · intro n s hs
      change b < s.re ∧ ‖s‖ < R at hs
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [hf0]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ |f n| * (‖s‖ * (n : ℝ) ^ (-s.re - 1)) :=
          mul_le_mul_of_nonneg_left (norm_complexMellinCell_le (hb0.trans hs.1) hn)
            (abs_nonneg _)
        _ ≤ |f n| * (R * (n : ℝ) ^ (-b - 1)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact mul_le_mul hs.2.le
            (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
              (by linarith only [hs.1])) (by positivity) hR
        _ = _ := by ring
  exact (hdiff.differentiableAt (hU.mem_nhds hsU)).differentiableWithinAt

/-- Replacing the discrete cutoff by its logarithmic staircase preserves
its leading power coefficient. -/
theorem tendsto_stepLaplaceIntegrand_of_power_asymptotic
    {f : ℕ → ℝ} {θ L : ℝ}
    (hf : Tendsto (fun N : ℕ => (N : ℝ) ^ (-θ) * f N) atTop (𝓝 L)) :
    Tendsto (stepLaplaceIntegrand f (θ : ℂ)) atTop (𝓝 (L : ℂ)) := by
  have hfloor : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop (N : ℝ)] with x hx
    exact Nat.le_floor hx
  have hr := (tendsto_nat_floor_div_atTop :
    Tendsto (fun x : ℝ => (⌊x⌋₊ : ℝ) / x) atTop (𝓝 1))
  have hp : Tendsto (fun x : ℝ => ((⌊x⌋₊ : ℝ) / x) ^ θ) atTop (𝓝 1) := by
    have hc : ContinuousAt (fun x : ℝ => x ^ θ) 1 :=
      Real.continuousAt_rpow_const 1 θ (Or.inl one_ne_zero)
    have hh := hc.tendsto.comp hr
    rw [Real.one_rpow] at hh
    exact hh.congr fun _ => rfl
  have h := (hf.comp hfloor).mul hp
  rw [mul_one] at h
  have hx : Tendsto (fun x : ℝ => x ^ (-θ) * f ⌊x⌋₊) atTop (𝓝 L) := by
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    change ((⌊x⌋₊ : ℝ) ^ (-θ) * f ⌊x⌋₊) * ((⌊x⌋₊ : ℝ) / x) ^ θ =
      x ^ (-θ) * f ⌊x⌋₊
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hn : 0 < (⌊x⌋₊ : ℝ) := by
      have hn1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hx)
      exact_mod_cast (Nat.zero_lt_one.trans_le hn1)
    rw [Real.div_rpow hn.le hx0.le, div_eq_mul_inv, ← Real.rpow_neg hx0.le]
    calc
      _ = ((⌊x⌋₊ : ℝ) ^ (-θ) * (⌊x⌋₊ : ℝ) ^ θ) *
          (x ^ (-θ) * f ⌊x⌋₊) := by ring
      _ = _ := by rw [← Real.rpow_add hn, neg_add_cancel, Real.rpow_zero, one_mul]
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp (hx.comp Real.tendsto_exp_atTop)
  refine hc.congr fun u => ?_
  simp only [Function.comp_apply, stepLaplaceIntegrand, Complex.ofReal_mul]
  congr 1
  rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- Convergent normalized summatory data has no nonreal residue on the
boundary line of its Mellin transform. -/
theorem tendsto_mul_complexMellinPairing_at_nonreal_boundary
    {f : ℕ → ℝ} (hf0 : f 0 = 0) {θ L τ : ℝ} (hθ : 0 ≤ θ) (hτ : τ ≠ 0)
    (hf : Tendsto (fun N : ℕ => (N : ℝ) ^ (-θ) * f N) atTop (𝓝 L)) :
    Tendsto (fun ε : ℝ => (ε : ℂ) *
      complexMellinPairing f (((θ + ε : ℝ) : ℂ) + (τ : ℂ) * I))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_power_bound_of_normalized_tendsto hf0 hf
  let r := stepLaplaceIntegrand f (θ : ℂ)
  have hr : AEStronglyMeasurable r (volume.restrict (Ioi 0)) :=
    (measurable_stepLaplaceIntegrand f (θ : ℂ)).aestronglyMeasurable
  have hb : ∀ u, 0 < u → ‖r u‖ ≤ C := by
    intro u hu
    rw [norm_stepLaplaceIntegrand, ofReal_re]
    have hn := Real.rpow_le_rpow (Nat.cast_nonneg ⌊Real.exp u⌋₊)
      (Nat.floor_le (Real.exp_pos u).le) hθ
    have hh := mul_le_mul_of_nonneg_left ((hbound _).trans
      (mul_le_mul_of_nonneg_left hn hC)) (Real.exp_pos (-(θ * u))).le
    have he : Real.exp (-(θ * u)) * (C * (Real.exp u) ^ θ) = C := by
      rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp, mul_left_comm,
        ← Real.exp_add, show -(θ * u) + u * θ = 0 by ring, Real.exp_zero, mul_one]
    exact hh.trans_eq he
  have hlim := tendsto_stepLaplaceIntegrand_of_power_asymptotic hf
  have heps : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hab := tendsto_abelIntegral_off hr hb hlim 0
    (show ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε from self_mem_nhdsWithin)
    heps (τ := fun _ : ℝ => τ) tendsto_const_nhds hτ
  have hz : Tendsto (fun ε : ℝ => (ε : ℂ) *
      abelIntegral r 0 ((ε : ℂ) + (τ : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply hab.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hε)]
  have hs : Tendsto (fun ε : ℝ => ((θ + ε : ℝ) : ℂ) + (τ : ℂ) * I)
      (𝓝[>] 0) (𝓝 ((θ : ℂ) + (τ : ℂ) * I)) := by
    have hh :=
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp (heps.const_add θ)).add_const
        ((τ : ℂ) * I))
    rw [add_zero] at hh
    exact hh.congr fun _ => rfl
  have hm := hs.mul hz
  rw [mul_zero] at hm
  apply hm.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  let s : ℂ := ((θ + ε : ℝ) : ℂ) + (τ : ℂ) * I
  have hsre : s.re = θ + ε := by simp [s]
  have hs0 : 0 < s.re := by rw [hsre]; linarith only [hθ, hε0]
  have hsum := summable_mellin_majorant_of_power_bound hf0 hbound
    (show θ < s.re by rw [hsre]; linarith only [hε0])
  have hi : abelIntegral r 0 ((ε : ℂ) + (τ : ℂ) * I) = complexMellinPairing f s / s := by
    have he : (fun u => r u * abelKernel 0 ((ε : ℂ) + (τ : ℂ) * I) u) =
        stepLaplaceIntegrand f s := by
      funext u
      simp only [r, stepLaplaceIntegrand, abelKernel, ofReal_zero, mul_zero, neg_zero,
        Complex.cpow_zero, one_mul]
      rw [mul_right_comm, ← Complex.exp_add]
      congr 2
      dsimp only [s]
      push_cast
      ring
    rw [abelIntegral, he, ← integral_Ici_eq_integral_Ioi]
    calc
      _ = ∫ u, stepLaplaceIntegrand f s u := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
        intro u hu
        exact stepLaplaceIntegrand_of_neg hf0 s (not_le.mp hu)
      _ = _ := integral_stepLaplaceIntegrand hf0 hs0 hsum
  rw [hi]
  have hsne : s ≠ 0 := fun h => by rw [h, zero_re] at hs0; exact lt_irrefl 0 hs0
  change s * ((ε : ℂ) * (complexMellinPairing f s / s)) =
    (ε : ℂ) * complexMellinPairing f s
  field_simp [hsne]

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
