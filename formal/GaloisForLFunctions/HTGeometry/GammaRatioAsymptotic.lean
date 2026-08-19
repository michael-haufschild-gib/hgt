/-
# The Gamma ratio is asymptotically a power

Wendel's inequality traps `Γ(x+a)/Γ(x)` between `x/(x+a)^{1-a}` and `x^a`, and both bounds are
`x^a(1+o(1))`, so the ratio is `x^a(1+o(1))` for `0 ≤ a ≤ 1`.  The functional equation then extends
this to every nonnegative shift by peeling off whole units.

Main results:
* `tendsto_Gamma_add_div_rpow_unit` — the ratio law for a shift in `[0,1]`.
* `tendsto_Gamma_add_div_rpow_nat` — the ratio law for a shift in `[0,1] + ℕ`.
* `tendsto_Gamma_add_div_rpow` — **the ratio law for every nonnegative shift**.
-/
import GaloisForLFunctions.HTGeometry.GammaWendelInequality

open Filter Topology Real

namespace GaloisForLFunctions.HTGeometry

/-- **The Gamma ratio law for a shift in `[0,1]`.** -/
theorem tendsto_Gamma_add_div_rpow_unit {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Tendsto (fun x : ℝ => Real.Gamma (x + a) / (Real.Gamma x * x ^ a)) atTop (nhds 1) := by
  have hupper : ∀ᶠ x : ℝ in atTop,
      Real.Gamma (x + a) / (Real.Gamma x * x ^ a) ≤ 1 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hGx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
    have hpow : (0 : ℝ) < x ^ a := Real.rpow_pos_of_pos hx a
    rw [div_le_one (by positivity)]
    exact Gamma_add_le hx ha0 ha1
  have hlower : ∀ᶠ x : ℝ in atTop,
      (x / (x + a)) ^ (1 - a) ≤ Real.Gamma (x + a) / (Real.Gamma x * x ^ a) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hxa : (0 : ℝ) < x + a := by linarith
    have hGx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
    have hpow : (0 : ℝ) < x ^ a := Real.rpow_pos_of_pos hx a
    have hwendel := le_Gamma_add hx ha0 ha1
    have hxa' : (0 : ℝ) < (x + a) ^ (1 - a) := Real.rpow_pos_of_pos hxa _
    rw [le_div_iff₀ (by positivity)]
    have hkey : Real.Gamma x * x ≤ Real.Gamma (x + a) * (x + a) ^ (1 - a) := hwendel
    have hsplit : (x / (x + a)) ^ (1 - a) * (Real.Gamma x * x ^ a)
        = (Real.Gamma x * x) / ((x + a) ^ (1 - a)) := by
      rw [Real.div_rpow hx.le hxa.le]
      have hx1 : x ^ (1 - a) * x ^ a = x := by
        rw [← Real.rpow_add hx]
        simp
      field_simp
      nlinarith [hx1, hxa'.le, hGx.le]
    rw [hsplit, div_le_iff₀ hxa']
    calc Real.Gamma x * x ≤ Real.Gamma (x + a) * (x + a) ^ (1 - a) := hkey
      _ = Real.Gamma (x + a) * (x + a) ^ (1 - a) := rfl
  have hsq : Tendsto (fun x : ℝ => (x / (x + a)) ^ (1 - a)) atTop (nhds 1) := by
    have hratio : Tendsto (fun x : ℝ => x / (x + a)) atTop (nhds 1) := by
      have := Filter.Tendsto.div_atTop (f := fun _ : ℝ => a) tendsto_const_nhds tendsto_id
      have hrw : ∀ᶠ x : ℝ in atTop, x / (x + a) = (1 + a / x)⁻¹ := by
        filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (-a)] with x hx hxa
        have hxa' : x + a ≠ 0 := by intro h; linarith
        field_simp
      refine Filter.Tendsto.congr' (Filter.EventuallyEq.symm hrw) ?_
      have hlim : Tendsto (fun x : ℝ => 1 + a / x) atTop (nhds 1) := by
        simpa using tendsto_const_nhds.add this
      simpa using hlim.inv₀ one_ne_zero
    have hcomp := (Real.continuousAt_rpow_const 1 (1 - a) (Or.inl one_ne_zero)).tendsto.comp hratio
    have hone : (1 : ℝ) ^ (1 - a) = 1 := Real.one_rpow _
    rw [hone] at hcomp
    exact hcomp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hsq tendsto_const_nhds hlower hupper

/-- **The Gamma ratio law for every nonnegative shift.** -/
theorem tendsto_Gamma_add_div_rpow_nat {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∀ n : ℕ, Tendsto
      (fun x : ℝ => Real.Gamma (x + (a + n)) / (Real.Gamma x * x ^ (a + (n : ℝ)))) atTop
      (nhds 1) := by
  intro n
  induction n with
  | zero => simpa using tendsto_Gamma_add_div_rpow_unit ha0 ha1
  | succ m ih =>
      have hstep : ∀ᶠ x : ℝ in atTop,
          Real.Gamma (x + (a + ((m : ℝ) + 1)))
              / (Real.Gamma x * x ^ (a + ((m : ℝ) + 1)))
            = (Real.Gamma (x + (a + (m : ℝ))) / (Real.Gamma x * x ^ (a + (m : ℝ))))
              * ((x + (a + (m : ℝ))) / x) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ),
          eventually_gt_atTop (-(a + (m : ℝ)))] with x hx hxm
        have hxam : (0 : ℝ) < x + (a + (m : ℝ)) := by linarith
        have hGx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
        have hshift : Real.Gamma (x + (a + ((m : ℝ) + 1)))
            = (x + (a + (m : ℝ))) * Real.Gamma (x + (a + (m : ℝ))) := by
          have harg : x + (a + ((m : ℝ) + 1)) = (x + (a + (m : ℝ))) + 1 := by ring
          rw [harg, Real.Gamma_add_one hxam.ne']
        have hpow : x ^ (a + ((m : ℝ) + 1)) = x ^ (a + (m : ℝ)) * x := by
          have : a + ((m : ℝ) + 1) = (a + (m : ℝ)) + 1 := by ring
          rw [this, Real.rpow_add hx, Real.rpow_one]
        rw [hshift, hpow]
        have hpx : (0 : ℝ) < x ^ (a + (m : ℝ)) := Real.rpow_pos_of_pos hx _
        field_simp
      have hratio : Tendsto (fun x : ℝ => (x + (a + (m : ℝ))) / x) atTop (nhds 1) := by
        have hrw : ∀ᶠ x : ℝ in atTop, (x + (a + (m : ℝ))) / x = 1 + (a + (m : ℝ)) / x := by
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
          field_simp
        refine Filter.Tendsto.congr' (Filter.EventuallyEq.symm hrw) ?_
        have := Filter.Tendsto.div_atTop
          (f := fun _ : ℝ => a + (m : ℝ)) tendsto_const_nhds tendsto_id
        simpa using tendsto_const_nhds.add this
      have hcast : a + (((m + 1 : ℕ) : ℝ)) = a + ((m : ℝ) + 1) := by push_cast; ring
      refine Filter.Tendsto.congr' (Filter.EventuallyEq.symm hstep) ?_ |>.congr ?_
      · simpa using ih.mul hratio
      · intro x
        rw [hcast]

/-- **The Gamma ratio law for every nonnegative shift**: `Γ(x+a) ∼ Γ(x)·x^a` as `x → ∞`. -/
theorem tendsto_Gamma_add_div_rpow {a : ℝ} (ha0 : 0 ≤ a) :
    Tendsto (fun x : ℝ => Real.Gamma (x + a) / (Real.Gamma x * x ^ a)) atTop (nhds 1) := by
  set n : ℕ := ⌊a⌋₊ with hn
  have hnle : (n : ℝ) ≤ a := Nat.floor_le ha0
  have hlt : a < (n : ℝ) + 1 := Nat.lt_floor_add_one a
  set r : ℝ := a - (n : ℝ) with hr
  have hr0 : 0 ≤ r := by simp only [hr]; linarith
  have hr1 : r ≤ 1 := by simp only [hr]; linarith
  have hsum : r + (n : ℝ) = a := by simp only [hr]; ring
  have h := tendsto_Gamma_add_div_rpow_nat hr0 hr1 n
  refine h.congr fun x => ?_
  rw [hsum]

end GaloisForLFunctions.HTGeometry
