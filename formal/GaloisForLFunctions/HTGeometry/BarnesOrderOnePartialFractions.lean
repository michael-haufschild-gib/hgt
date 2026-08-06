import GaloisForLFunctions.HTGeometry.BarnesLadderDecomposition
import GaloisForLFunctions.HTGeometry.BarnesPoleAvoidance
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-!
# The order-one reflected Barnes source is a cotangent

With a single structural direction the Barnes cone product is the genus-one Weierstrass product over
the ray `ℕ w`, and its logarithmic derivative is the partial-fraction series

```text
Ψ(z) = ∑_{m ≥ 1} (1/(m w + z) - 1/(m w)).
```

Reflecting at the period and subtracting cancels the constant terms and pairs the two rays:

```text
Ψ(z) - Ψ(w - z) = ∑_{m ≥ 1} (1/(m w + z) - 1/((m+1) w - z)),
```

which is the Mittag-Leffler expansion of the cotangent up to one telescoping term.  Against the
classical expansion

```text
π cot(π x) = 1/x + ∑_{m ≥ 1} (1/(x - m) + 1/(x + m))
```

at `x = z/w` the difference of the two summands telescopes, so

```text
Ψ(z) - Ψ(w - z) = (π/w) cot(π z / w) - 1/z + 1/(w - z).
```

This is the order-one boundary `S_1(z; w) = 2 sin(π z / w)` of the multiple sine hierarchy, in the
form the differential descent consumes: the reflected source differs from the period cotangent by a
rational function.
-/

open Filter Set Topology Complex
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-! ### A telescoping series -/

/-- A summable telescoping series sums to its first term. -/
theorem tsum_telescope {f : ℕ → ℂ} (hs : Summable fun n => f n - f (n + 1))
    (h0 : Filter.Tendsto f Filter.atTop (nhds 0)) :
    ∑' n, (f n - f (n + 1)) = f 0 := by
  have hHas : HasSum (fun n => f n - f (n + 1)) (f 0) := by
    rw [hs.hasSum_iff_tendsto_nat]
    simp only [Finset.sum_range_sub' f]
    simpa using (tendsto_const_nhds (x := f 0) (f := Filter.atTop (α := ℕ))).sub h0
  exact hHas.tsum_eq

/-- The inverse of a sequence whose norm tends to infinity tends to zero. -/
theorem tendsto_inv_of_tendsto_norm_atTop {f : ℕ → ℂ}
    (h : Filter.Tendsto (fun n => ‖f n‖) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => (f n)⁻¹) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_inv]
  exact h.inv_tendsto_atTop

/-! ### The order-one atom -/

/-- The order-one Barnes atom: the genus-one elementary term of the ray `ℕ w`. -/
def orderOneAtom (w z : ℂ) (m : ℕ) : ℂ :=
  if m = 0 then 0 else 1 / ((m : ℂ) * w + z) - 1 / ((m : ℂ) * w)

theorem conePeriod_const (w : ℂ) (n : Fin 1 → ℕ) :
    conePeriod (fun _ : Fin 1 => w) n = (n default : ℂ) * w := by
  unfold conePeriod
  exact Fintype.sum_unique fun i => (n i : ℂ) * w

theorem barnesAtom_const_eq_orderOneAtom (w : ℂ) (hw : w ≠ 0) {z : ℂ}
    (hz : ∀ k : ℤ, z ≠ (k : ℂ) * w) (m : ℕ) :
    barnesAtom (fun _ : Fin 1 => w) (fun _ => m) z = orderOneAtom w z m := by
  by_cases hm : m = 0
  · subst hm
    have hzero : (fun _ : Fin 1 => (0 : ℕ)) = 0 := rfl
    rw [barnesAtom, if_pos hzero, orderOneAtom, if_pos rfl]
  · have hn : (fun _ : Fin 1 => m) ≠ 0 := fun h => hm (congrFun h default)
    have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have hmw : (m : ℂ) * w ≠ 0 := mul_ne_zero hmC hw
    have hpole : (m : ℂ) * w + z ≠ 0 := by
      intro h
      refine hz (-(m : ℤ)) ?_
      push_cast
      linear_combination h
    rw [barnesAtom, if_neg hn, conePeriod_const, Fintype.card_unique, pow_one,
      orderOneAtom, if_neg hm]
    field_simp
    ring

/-! ### The order-one source is the atom series -/

theorem summable_orderOneAtom (w : ℂ) (hw : 0 < w.im) (hw0 : w ≠ 0) {z : ℂ}
    (hz : ∀ k : ℤ, z ≠ (k : ℂ) * w) :
    Summable (orderOneAtom w z) := by
  have hbase : Summable fun n : Fin 1 → ℕ => barnesAtom (fun _ : Fin 1 => w) n z :=
    summable_barnesAtom (fun _ : Fin 1 => w) (fun _ => hw) z
  have hshift := (Equiv.summable_iff (f := fun n : Fin 1 → ℕ => barnesAtom (fun _ : Fin 1 => w) n z)
    (Equiv.funUnique (Fin 1) ℕ).symm).mpr hbase
  refine hshift.congr fun m => ?_
  exact barnesAtom_const_eq_orderOneAtom w hw0 hz m

theorem logDeriv_barnesConeProduct_const_eq_tsum (w : ℂ) (hw : 0 < w.im) (hw0 : w ≠ 0) {z : ℂ}
    (hz : ∀ k : ℤ, z ≠ (k : ℂ) * w) :
    logDeriv (barnesConeProduct (fun _ : Fin 1 => w)) z = ∑' m : ℕ, orderOneAtom w z m := by
  have hpole : ∀ n : Fin 1 → ℕ, n ≠ 0 → conePeriod (fun _ : Fin 1 => w) n + z ≠ 0 := by
    intro n hn hcon
    have hnd : n default ≠ 0 := by
      intro h
      exact hn (funext fun i => by rw [Unique.eq_default i, h]; rfl)
    rw [conePeriod_const] at hcon
    refine hz (-(n default : ℤ)) ?_
    push_cast
    linear_combination hcon
  rw [logDeriv_barnesConeProduct_eq_tsum_barnesAtom (fun _ : Fin 1 => w) (fun _ => hw) hpole,
    ← (Equiv.funUnique (Fin 1) ℕ).symm.tsum_eq
      (fun n : Fin 1 → ℕ => barnesAtom (fun _ : Fin 1 => w) n z)]
  exact tsum_congr fun m => barnesAtom_const_eq_orderOneAtom w hw0 hz m

/-! ### The reflected order-one source -/

/-- **The order-one reflected source is the period cotangent up to a rational function.** -/
theorem barnesSource_orderOne_reflect_eq_cot (w : ℂ) (hw : 0 < w.im) {z : ℂ}
    (hz : ∀ k : ℤ, z ≠ (k : ℂ) * w) :
    logDeriv (barnesConeProduct (fun _ : Fin 1 => w)) z
        - logDeriv (barnesConeProduct (fun _ : Fin 1 => w)) (w - z)
      = ((Real.pi : ℂ) / w) * Complex.cot ((Real.pi : ℂ) * z / w) - 1 / z + 1 / (w - z) := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  have hz' : ∀ k : ℤ, w - z ≠ (k : ℂ) * w := by
    intro k hcon
    refine hz (1 - k) ?_
    push_cast
    linear_combination -hcon
  -- the two atom series
  have hsz := summable_orderOneAtom w hw hw0 hz
  have hsr := summable_orderOneAtom w hw hw0 hz'
  set d : ℕ → ℂ := fun m => orderOneAtom w z m - orderOneAtom w (w - z) m with hd
  have hdsum : Summable d := hsz.sub hsr
  have hsource : logDeriv (barnesConeProduct (fun _ : Fin 1 => w)) z
      - logDeriv (barnesConeProduct (fun _ : Fin 1 => w)) (w - z) = ∑' m : ℕ, d m := by
    rw [logDeriv_barnesConeProduct_const_eq_tsum w hw hw0 hz,
      logDeriv_barnesConeProduct_const_eq_tsum w hw hw0 hz',
      ← hsz.tsum_sub hsr]
  -- drop the zeroth term
  have hzero : d 0 = 0 := by
    simp [hd, orderOneAtom]
  have hshift : ∑' m : ℕ, d m = ∑' n : ℕ, d (n + 1) := by
    rw [hdsum.tsum_eq_zero_add, hzero, zero_add]
  -- the classical cotangent series
  have hx : z / w ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨k, hk⟩
    refine hz k ?_
    field_simp at hk
    linear_combination -hk
  set c : ℕ → ℂ := fun n => 1 / (z - ((n : ℂ) + 1) * w) + 1 / (z + ((n : ℂ) + 1) * w) with hc
  have hcterm : ∀ n : ℕ, c n = (1 / w) * cotTerm (z / w) n := by
    intro n
    rw [hc]
    have h1 : z / w - ((n : ℂ) + 1) ≠ 0 := by
      intro hcon
      refine hz (n + 1) ?_
      field_simp at hcon
      push_cast
      linear_combination hcon
    have h2 : z / w + ((n : ℂ) + 1) ≠ 0 := by
      intro hcon
      refine hz (-(n + 1)) ?_
      field_simp at hcon
      push_cast
      linear_combination hcon
    show 1 / (z - ((n : ℂ) + 1) * w) + 1 / (z + ((n : ℂ) + 1) * w)
      = (1 / w) * (1 / (z / w - ((n : ℂ) + 1)) + 1 / (z / w + ((n : ℂ) + 1)))
    field_simp
  have hcsum : Summable c := by
    refine ((summable_cotTerm hx).mul_left (1 / w)).congr fun n => (hcterm n).symm
  have hctsum : ∑' n : ℕ, c n
      = ((Real.pi : ℂ) / w) * Complex.cot ((Real.pi : ℂ) * z / w) - 1 / z := by
    rw [tsum_congr hcterm, tsum_mul_left, ← cot_series_rep' hx]
    have harg : (Real.pi : ℂ) * (z / w) = (Real.pi : ℂ) * z / w := by ring
    rw [harg]
    have hzne : z ≠ 0 := by
      intro h
      exact hz 0 (by rw [h]; ring)
    field_simp
  -- the telescoping remainder
  set t : ℕ → ℂ := fun n => 1 / (((n : ℂ) + 1) * w - z) with ht
  have hkey : ∀ n : ℕ, d (n + 1) - c n = t n - t (n + 1) := by
    intro n
    have hdval : d (n + 1)
        = 1 / (((n : ℂ) + 1) * w + z) - 1 / (((n : ℂ) + 1) * w + w - z) := by
      rw [hd]
      simp only [orderOneAtom, if_neg (Nat.succ_ne_zero n)]
      push_cast
      ring
    have hcval : c n = 1 / (z - ((n : ℂ) + 1) * w) + 1 / (z + ((n : ℂ) + 1) * w) := rfl
    have htval : t n = 1 / (((n : ℂ) + 1) * w - z) := rfl
    have ht1val : t (n + 1) = 1 / (((n : ℂ) + 1 + 1) * w - z) := by
      simp only [ht]
      push_cast
      ring_nf
    have hflip : (1 : ℂ) / (z - ((n : ℂ) + 1) * w) = -(1 / (((n : ℂ) + 1) * w - z)) := by
      rw [show z - ((n : ℂ) + 1) * w = -(((n : ℂ) + 1) * w - z) by ring, one_div, inv_neg,
        one_div]
    rw [hdval, hcval, htval, ht1val, hflip]
    ring
  have hdshift : Summable fun n : ℕ => d (n + 1) := (summable_nat_add_iff 1).mpr hdsum
  have htsum : Summable fun n : ℕ => t n - t (n + 1) :=
    (hdshift.sub hcsum).congr hkey
  have htend : Filter.Tendsto t Filter.atTop (nhds 0) := by
    have hnorm : Filter.Tendsto (fun n : ℕ => ‖((n : ℂ) + 1) * w - z‖)
        Filter.atTop Filter.atTop := by
      have hbound : ∀ n : ℕ, ((n : ℝ) + 1) * ‖w‖ - ‖z‖ ≤ ‖((n : ℂ) + 1) * w - z‖ := by
        intro n
        have h1 : ‖((n : ℂ) + 1) * w‖ - ‖z‖ ≤ ‖((n : ℂ) + 1) * w - z‖ :=
          norm_sub_norm_le _ _
        have h2 : ‖((n : ℂ) + 1) * w‖ = ((n : ℝ) + 1) * ‖w‖ := by
          rw [norm_mul]
          congr 1
          rw [show ((n : ℂ) + 1) = ((((n : ℕ) + 1 : ℕ)) : ℂ) by push_cast; ring,
            Complex.norm_natCast]
          push_cast
          ring
        rw [← h2]
        exact h1
      refine Filter.tendsto_atTop_mono hbound ?_
      have hwpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw0
      have hlin : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) * ‖w‖)
          Filter.atTop Filter.atTop := by
        refine Filter.Tendsto.atTop_mul_const hwpos ?_
        exact Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      exact Filter.tendsto_atTop_add_const_right _ (-‖z‖) hlin
    have := tendsto_inv_of_tendsto_norm_atTop hnorm
    refine this.congr fun n => ?_
    simp only [ht, one_div]
  have htel : ∑' n : ℕ, (t n - t (n + 1)) = t 0 := tsum_telescope htsum htend
  have ht0 : t 0 = 1 / (w - z) := by
    rw [ht]
    norm_num
  have hfinal : ∑' n : ℕ, d (n + 1) - ∑' n : ℕ, c n = 1 / (w - z) := by
    rw [← hdshift.tsum_sub hcsum, tsum_congr hkey, htel, ht0]
  rw [hsource, hshift]
  have := hfinal
  rw [hctsum] at this
  linear_combination this

end

end GaloisForLFunctions.HTGeometry
