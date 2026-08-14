import GaloisForLFunctions.HTGeometry.FlatVolterraDecay
import GaloisForLFunctions.HTGeometry.CoerciveResolutionBound
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The flat primitive flux system decays exponentially

The localized value equation and the backward flux tail form a closed pair of block inequalities

`f n ≤ A₀ y n / n + C₀ e^{-δ n}`,   `y n ≤ D₀ ∑_{m ≥ n} f m + C₁ e^{-δ n}`.

Substituting the first into the second turns the pair into a single backward Volterra inequality
for the flux, whose flat solution decays at every rate below the source rate; feeding that back
into the value equation gives the same decay for the value.  No adjoint, no normality and no group
bound for the nonnormal prime transport is used: the only operator input is the coercive lower
bound of the terminal Gamma block.
-/

open Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The geometric tail of the exponential source. -/
theorem tsum_exp_shift {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (∑' k : ℕ, Real.exp (-δ * ((n : ℝ) + k)))
      = Real.exp (-δ * n) / (1 - Real.exp (-δ)) := by
  have hlt : Real.exp (-δ) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hval : ∀ k : ℕ, Real.exp (-δ * ((n : ℝ) + k))
      = Real.exp (-δ * n) * (Real.exp (-δ)) ^ k := by
    intro k
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [tsum_congr hval, tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hlt]
  ring

/-- **The coupled flat flux system decays at every rate below the source rate.** -/
theorem flat_flux_exponential_decay {F Y : ℕ → ℝ} {A₀ C₀ D₀ C₁ δ δ' : ℝ}
    (hA₀ : 0 ≤ A₀) (hC₀ : 0 ≤ C₀) (hD₀ : 0 ≤ D₀) (hC₁ : 0 ≤ C₁)
    (hδ : 0 < δ) (hδ' : 0 < δ') (hlt : δ' < δ)
    (hF0 : ∀ n, 0 ≤ F n) (hY0 : ∀ n, 0 ≤ Y n)
    (hFflat : SuperpolynomiallyFlat F) (hYflat : SuperpolynomiallyFlat Y)
    (hvalue : ∀ᶠ n : ℕ in atTop, F n ≤ A₀ * (Y n / n) + C₀ * Real.exp (-δ * n))
    (hflux : ∀ᶠ n : ℕ in atTop,
      Y n ≤ D₀ * (∑' k : ℕ, F (n + k)) + C₁ * Real.exp (-δ * n)) :
    ∃ C' : ℝ, (∀ᶠ n : ℕ in atTop, Y n ≤ C' * Real.exp (-δ' * n)) ∧
      (∀ᶠ n : ℕ in atTop, F n ≤ C' * Real.exp (-δ' * n)) := by
  have hgeo : Real.exp (-δ) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hgeopos : (0:ℝ) < 1 - Real.exp (-δ) := by linarith
  -- the value equation makes the flux tail a Volterra tail
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hvalue
  have htail : ∀ n : ℕ, n₀ ≤ n →
      (∑' k : ℕ, F (n + k))
        ≤ A₀ * volterraTail Y n + C₀ * (Real.exp (-δ * n) / (1 - Real.exp (-δ))) := by
    intro n hn
    have hsumF : Summable fun k : ℕ => F (n + k) := summable_shifted_of_flat hF0 hFflat n
    have hsumY : Summable fun k : ℕ => volterraTerm Y (n + k) :=
      summable_shifted_volterraTerm hY0 hYflat n
    have hsumE : Summable fun k : ℕ => Real.exp (-δ * ((n : ℝ) + k)) := by
      have hbase : Summable fun k : ℕ => (Real.exp (-δ)) ^ k :=
        summable_geometric_of_lt_one (Real.exp_pos _).le hgeo
      refine (hbase.mul_left (Real.exp (-δ * n))).congr fun k => ?_
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    have hmajor : Summable fun k : ℕ =>
        A₀ * volterraTerm Y (n + k) + C₀ * Real.exp (-δ * ((n : ℝ) + k)) :=
      (hsumY.mul_left A₀).add (hsumE.mul_left C₀)
    have hterm : ∀ k : ℕ, F (n + k)
        ≤ A₀ * volterraTerm Y (n + k) + C₀ * Real.exp (-δ * ((n : ℝ) + k)) := by
      intro k
      have hk := hn₀ (n + k) (le_trans hn (Nat.le_add_right n k))
      have hcast : ((n + k : ℕ) : ℝ) = (n : ℝ) + k := by push_cast; ring
      rw [volterraTerm, hcast]
      rw [hcast] at hk
      exact hk
    have hle := Summable.tsum_le_tsum hterm hsumF hmajor
    rw [Summable.tsum_add (hsumY.mul_left A₀) (hsumE.mul_left C₀), tsum_mul_left, tsum_mul_left,
      tsum_exp_shift hδ n, ← volterraTail] at hle
    exact hle
  -- the Volterra inequality for the flux
  have hvolt : ∀ᶠ n : ℕ in atTop,
      Y n ≤ (D₀ * A₀) * volterraTail Y n
        + (D₀ * C₀ / (1 - Real.exp (-δ)) + C₁) * Real.exp (-δ * n) := by
    filter_upwards [hflux, eventually_ge_atTop n₀] with n hf hn
    have ht := htail n hn
    have hstep : D₀ * (∑' k : ℕ, F (n + k))
        ≤ D₀ * (A₀ * volterraTail Y n + C₀ * (Real.exp (-δ * n) / (1 - Real.exp (-δ)))) :=
      mul_le_mul_of_nonneg_left ht hD₀
    have hexpand : D₀ * (A₀ * volterraTail Y n
          + C₀ * (Real.exp (-δ * n) / (1 - Real.exp (-δ))))
        = (D₀ * A₀) * volterraTail Y n
          + (D₀ * C₀ / (1 - Real.exp (-δ))) * Real.exp (-δ * n) := by
      field_simp
    rw [hexpand] at hstep
    linarith
  obtain ⟨K, hK⟩ := flat_volterra_decay_of_tail (q := Y) (A := D₀ * A₀)
    (C := D₀ * C₀ / (1 - Real.exp (-δ)) + C₁) (by positivity)
    (by positivity) hδ' hlt hY0 hYflat hvolt
  -- feeding the flux decay back into the value equation
  refine ⟨max K (A₀ * K + C₀), ?_, ?_⟩
  · filter_upwards [hK] with n hn
    have hexp : (0:ℝ) < Real.exp (-δ' * n) := Real.exp_pos _
    have hmax : K ≤ max K (A₀ * K + C₀) := le_max_left _ _
    nlinarith [hn, hexp, hmax]
  · filter_upwards [hvalue, hK, eventually_ge_atTop 1] with n hv hy hn
    have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hexp : (0:ℝ) < Real.exp (-δ' * n) := Real.exp_pos _
    have hdiv : Y n / n ≤ K * Real.exp (-δ' * n) := by
      have hYn : Y n ≤ K * Real.exp (-δ' * n) := hy
      have hpos : (0:ℝ) < (n:ℝ) := by linarith
      rw [div_le_iff₀ hpos]
      nlinarith [hY0 n, hYn, hn1, hexp]
    have hsrc : Real.exp (-δ * n) ≤ Real.exp (-δ' * n) := by
      apply Real.exp_le_exp.mpr
      have hnn : (0:ℝ) ≤ (n:ℝ) := by linarith
      nlinarith
    have hmax : A₀ * K + C₀ ≤ max K (A₀ * K + C₀) := le_max_right _ _
    nlinarith [hv, hdiv, hsrc, hexp, hA₀, hC₀, hmax]

/-! ## The zero-charge backward tail -/

/-- **`(12)`: a flux with no terminal charge is the backward integral of its source.** -/
theorem terminal_flux_eq_neg_integral {Y g : ℝ → ℝ} {L : ℝ}
    (hderiv : ∀ t ∈ Set.Ioi L, HasDerivAt Y (g t) t)
    (hcont : ContinuousWithinAt Y (Set.Ici L) L)
    (hint : MeasureTheory.IntegrableOn g (Set.Ioi L) MeasureTheory.volume)
    (hlim : Tendsto Y atTop (𝓝 0)) :
    Y L = -∫ t in Set.Ioi L, g t := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [h]
  ring

/-! ## The exponential envelope -/

/-- The exponential block envelope of a sequence. -/
noncomputable def expEnvelope (μ : ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' m : ℕ, Real.exp (-μ * |(n : ℝ) - m|) * a m

/-- Every block is dominated by its own envelope. -/
theorem le_expEnvelope {a : ℕ → ℝ} {μ : ℝ} (n : ℕ) (ha0 : ∀ m, 0 ≤ a m)
    (hsum : Summable fun m : ℕ => Real.exp (-μ * |(n : ℝ) - m|) * a m) :
    a n ≤ expEnvelope μ a n := by
  have hterm : a n = Real.exp (-μ * |(n : ℝ) - n|) * a n := by
    rw [sub_self, abs_zero, mul_zero, Real.exp_zero, one_mul]
  rw [expEnvelope, hterm]
  exact Summable.le_tsum hsum n fun m _ => mul_nonneg (Real.exp_pos _).le (ha0 m)

/-- **`(8)`, `(22)`: the envelope of an exponentially small sequence is exponentially small at the
same rate**, provided the envelope rate is strictly larger. -/
theorem expEnvelope_le_of_exp_decay {a : ℕ → ℝ} {μ δ' C : ℝ} (hC : 0 ≤ C) (hδ' : 0 < δ')
    (hμ : δ' < μ) (ha0 : ∀ m, 0 ≤ a m) (ha : ∀ m, a m ≤ C * Real.exp (-δ' * m)) (n : ℕ) :
    expEnvelope μ a n ≤ (2 * C / (1 - Real.exp (-(μ - δ')))) * Real.exp (-δ' * n) := by
  have hε : 0 < μ - δ' := by linarith
  have hgeo : Real.exp (-(μ - δ')) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hgeopos : (0:ℝ) < 1 - Real.exp (-(μ - δ')) := by linarith
  set r : ℝ := Real.exp (-(μ - δ')) with hrdef
  have hr0 : (0:ℝ) ≤ r := (Real.exp_pos _).le
  set S : ℝ := C * Real.exp (-δ' * n) with hSdef
  have hS0 : 0 ≤ S := by positivity
  set f : ℕ → ℝ := fun m => Real.exp (-μ * |(n : ℝ) - m|) * a m with hfdef
  have hf0 : ∀ m, 0 ≤ f m := fun m => mul_nonneg (Real.exp_pos _).le (ha0 m)
  -- the two pointwise majorants
  have hleft : ∀ m : ℕ, m ≤ n → f m ≤ S * r ^ (n - m) := by
    intro m hm
    have hmR : (m : ℝ) ≤ n := by exact_mod_cast hm
    have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := by
      push_cast [Nat.cast_sub hm]
      ring
    have habs : |(n : ℝ) - m| = ((n - m : ℕ) : ℝ) := by
      rw [hcast, abs_of_nonneg (by linarith)]
    have hval : S * r ^ (n - m) = C * Real.exp (-μ * ((n - m : ℕ) : ℝ) + -δ' * (m : ℝ)) := by
      rw [hSdef, hrdef, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      congr 1
      rw [hcast]
      ring
    show Real.exp (-μ * |(n : ℝ) - m|) * a m ≤ S * r ^ (n - m)
    rw [habs, hval]
    have hstep := mul_le_mul_of_nonneg_left (ha m)
      (Real.exp_pos (-μ * ((n - m : ℕ) : ℝ))).le
    refine le_trans hstep (le_of_eq ?_)
    rw [Real.exp_add]
    ring
  have hright : ∀ k : ℕ, f (n + 1 + k) ≤ S * r ^ (k + 1) := by
    intro k
    have hcast2 : ((n + 1 + k : ℕ) : ℝ) = (n : ℝ) + ((k : ℝ) + 1) := by push_cast; ring
    have habs : |(n : ℝ) - ((n + 1 + k : ℕ) : ℝ)| = (k : ℝ) + 1 := by
      rw [hcast2, show (n : ℝ) - ((n : ℝ) + ((k : ℝ) + 1)) = -((k : ℝ) + 1) by ring, abs_neg,
        abs_of_nonneg (by positivity)]
    have hval : S * r ^ (k + 1)
        = C * Real.exp (-δ' * (n : ℝ) + -(μ - δ') * ((k : ℝ) + 1)) := by
      rw [hSdef, hrdef, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      congr 1
      push_cast
      ring
    show Real.exp (-μ * |(n : ℝ) - ((n + 1 + k : ℕ) : ℝ)|) * a (n + 1 + k) ≤ S * r ^ (k + 1)
    rw [habs, hval]
    have hbound := ha (n + 1 + k)
    rw [hcast2] at hbound
    have hstep := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (-μ * ((k : ℝ) + 1))).le
    refine le_trans hstep ?_
    have hcombine : Real.exp (-μ * ((k : ℝ) + 1))
        * (C * Real.exp (-δ' * ((n : ℝ) + ((k : ℝ) + 1))))
        = C * Real.exp (-δ' * (n : ℝ) + -(μ + δ') * ((k : ℝ) + 1)) := by
      rw [← mul_assoc, mul_comm (Real.exp (-μ * ((k : ℝ) + 1))) C, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [hcombine]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
    nlinarith [hδ'.le, (by positivity : (0:ℝ) ≤ (k : ℝ) + 1)]
  -- summability
  have hgeosum : Summable fun k : ℕ => S * r ^ k :=
    (summable_geometric_of_lt_one hr0 hgeo).mul_left S
  have hgeosum1 : Summable fun k : ℕ => S * r ^ (k + 1) := by
    refine ((summable_geometric_of_lt_one hr0 hgeo).mul_left (S * r)).congr fun k => ?_
    rw [pow_succ]
    ring
  have hsumshift : Summable fun k : ℕ => f (n + 1 + k) := by
    exact Summable.of_nonneg_of_le (fun k => hf0 _) (fun k => hright k) hgeosum1
  have hsum : Summable f := by
    have h := (summable_nat_add_iff (n + 1)).mp (hsumshift.congr fun k => by
      rw [Nat.add_comm (n + 1) k])
    exact h
  -- the split and the two bounds
  have hsplit : (∑ m ∈ Finset.range (n + 1), f m) + ∑' k : ℕ, f (k + (n + 1)) = ∑' m : ℕ, f m :=
    hsum.sum_add_tsum_nat_add (n + 1)
  have hpart1 : (∑ m ∈ Finset.range (n + 1), f m) ≤ S / (1 - r) := by
    have hle : (∑ m ∈ Finset.range (n + 1), f m)
        ≤ ∑ m ∈ Finset.range (n + 1), S * r ^ (n - m) := by
      refine Finset.sum_le_sum fun m hm => ?_
      exact hleft m (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hm)
    have hreflect : (∑ m ∈ Finset.range (n + 1), S * r ^ (n - m))
        = ∑ j ∈ Finset.range (n + 1), S * r ^ j := by
      have h := Finset.sum_range_reflect (fun j => S * r ^ j) (n + 1)
      simpa using h
    have hgeo' : (∑ j ∈ Finset.range (n + 1), S * r ^ j) ≤ ∑' j : ℕ, S * r ^ j :=
      Summable.sum_le_tsum _ (fun j _ => by positivity) hgeosum
    have hval : (∑' j : ℕ, S * r ^ j) = S / (1 - r) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hgeo]
      ring
    rw [hreflect] at hle
    rw [hval] at hgeo'
    linarith
  have hpart2 : (∑' k : ℕ, f (k + (n + 1))) ≤ S / (1 - r) := by
    have hcongr : (∑' k : ℕ, f (k + (n + 1))) = ∑' k : ℕ, f (n + 1 + k) := by
      refine tsum_congr fun k => ?_
      rw [Nat.add_comm k (n + 1)]
    rw [hcongr]
    have hle := Summable.tsum_le_tsum hright hsumshift hgeosum1
    refine le_trans hle ?_
    have hval : (∑' k : ℕ, S * r ^ (k + 1)) = S * r / (1 - r) := by
      have hshift : ∀ k : ℕ, S * r ^ (k + 1) = (S * r) * r ^ k := by
        intro k
        rw [pow_succ]
        ring
      rw [tsum_congr hshift, tsum_mul_left, tsum_geometric_of_lt_one hr0 hgeo]
      ring
    rw [hval, div_le_div_iff₀ hgeopos hgeopos]
    nlinarith [hS0, hgeopos, mul_nonneg hS0 (sq_nonneg (1 - r))]
  rw [expEnvelope, ← hsplit]
  have hfinal : S / (1 - r) + S / (1 - r)
      = (2 * C / (1 - r)) * Real.exp (-δ' * n) := by
    rw [hSdef]
    field_simp
    ring
  linarith [hpart1, hpart2, hfinal]

end RHTower