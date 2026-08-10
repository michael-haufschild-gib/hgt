import GaloisForLFunctions.HTGeometry.NewtonSlopeTransform

/-!
# The minimal Newton slope exists

For a polynomial over `K⟦t⟧` whose special fibre is `X ^ d` and which is not `X ^ d` itself, the
Newton polygon has a smallest positive slope, and it is attained.  Written as `p / q` in the form
supplied here — `p` the order of a minimising coefficient and `q` its horizontal distance to the
leading vertex — the two defining properties of that slope are exactly the hypotheses of the slope
substitution: every coefficient is divisible by the corresponding power of the variable after
expansion, and at the minimising index the divisibility is sharp, so the edge polynomial has a
second nonzero term besides its leading one.

No rational arithmetic survives into the statement: the minimum is selected in `ℚ` and immediately
cross-multiplied back to `ℕ`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial PowerSeries

variable {K : Type} [Field K]

/-- Divisibility by a power of the variable is a lower bound on the order. -/
theorem X_pow_dvd_of_le_order {n : ℕ} {φ : PowerSeries K} (h : (n : ℕ∞) ≤ φ.order) :
    (PowerSeries.X : PowerSeries K) ^ n ∣ φ := by
  refine PowerSeries.X_pow_dvd_iff.2 fun m hm => ?_
  refine PowerSeries.coeff_of_lt_order m (lt_of_lt_of_le ?_ h)
  exact_mod_cast hm

/-- The order of an expansion, as a natural number. -/
theorem order_expand_toNat {q : ℕ} (hq : q ≠ 0) {φ : PowerSeries K} (hφ : φ ≠ 0) :
    (PowerSeries.expand q hq φ).order = ((q * φ.order.toNat : ℕ) : ℕ∞) := by
  have hne : φ.order ≠ ⊤ := by
    rw [Ne, PowerSeries.order_eq_top]
    exact hφ
  have hcast : φ.order = ((φ.order.toNat : ℕ) : ℕ∞) := (ENat.coe_toNat hne).symm
  rw [PowerSeries.order_expand]
  conv_lhs => rw [hcast]
  push_cast
  rw [nsmul_eq_mul]

/-- An expansion of a nonzero series is nonzero. -/
theorem expand_ne_zero {q : ℕ} (hq : q ≠ 0) {φ : PowerSeries K} (hφ : φ ≠ 0) :
    PowerSeries.expand q hq φ ≠ 0 := by
  intro hcon
  have hord : (PowerSeries.expand q hq φ).order = ((q * φ.order.toNat : ℕ) : ℕ∞) :=
    order_expand_toNat hq hφ
  rw [hcon, PowerSeries.order_zero] at hord
  exact (ENat.coe_ne_top _) hord.symm

/-- **The minimal Newton slope.**  A polynomial of degree `d` whose special fibre is `X ^ d` and
which has some vanishing coefficient below the top has a slope `p / q` with `p, q ≥ 1` such that
every coefficient clears the corresponding power after expansion by `q`, with equality at one
index. -/
theorem exists_newton_slope {f : (PowerSeries K)[X]} {d : ℕ}
    (hfib : ∀ i < d, PowerSeries.constantCoeff (f.coeff i) = 0)
    (hne : ∃ i, i < d ∧ f.coeff i ≠ 0) :
    ∃ (p q : ℕ) (hq : q ≠ 0), 0 < p ∧
      (∀ i ≤ d, (PowerSeries.X : PowerSeries K) ^ (p * (d - i)) ∣
        PowerSeries.expand q hq (f.coeff i)) ∧
      ∃ i₀, i₀ < d ∧
        PowerSeries.coeff (p * (d - i₀)) (PowerSeries.expand q hq (f.coeff i₀)) ≠ 0 := by
  classical
  set S : Finset ℕ := (Finset.range d).filter (fun i => f.coeff i ≠ 0) with hSdef
  have hSne : S.Nonempty := by
    obtain ⟨i, hi, hci⟩ := hne
    exact ⟨i, by rw [hSdef, Finset.mem_filter, Finset.mem_range]; exact ⟨hi, hci⟩⟩
  obtain ⟨i₀, hi₀S, hmin⟩ := Finset.exists_min_image S
    (fun i => ((f.coeff i).order.toNat : ℚ) / ((d - i : ℕ) : ℚ)) hSne
  have hmem := Finset.mem_filter.1 (by rwa [hSdef] at hi₀S)
  have hi₀d : i₀ < d := Finset.mem_range.1 hmem.1
  have hci₀ : f.coeff i₀ ≠ 0 := hmem.2
  refine ⟨(f.coeff i₀).order.toNat, d - i₀, by omega, ?_, ?_, i₀, hi₀d, ?_⟩
  · -- the minimal order is positive because the special fibre kills the constant term
    have h1 : (1 : ℕ∞) ≤ (f.coeff i₀).order :=
      PowerSeries.one_le_order_iff_constCoeff_eq_zero.2 (hfib i₀ hi₀d)
    have hne' : (f.coeff i₀).order ≠ ⊤ := by
      rw [Ne, PowerSeries.order_eq_top]; exact hci₀
    rw [← ENat.coe_toNat hne'] at h1
    exact_mod_cast h1
  · intro i hi
    rcases Nat.lt_or_ge i d with hid | hid
    · by_cases hci : f.coeff i = 0
      · rw [hci, map_zero]
        exact dvd_zero _
      · have hiS : i ∈ S := by
          rw [hSdef, Finset.mem_filter, Finset.mem_range]
          exact ⟨hid, hci⟩
        have hle := hmin i hiS
        have hqpos : (0 : ℚ) < ((d - i₀ : ℕ) : ℚ) := by
          have : 0 < d - i₀ := by omega
          exact_mod_cast this
        have hipos : (0 : ℚ) < ((d - i : ℕ) : ℚ) := by
          have : 0 < d - i := by omega
          exact_mod_cast this
        rw [div_le_div_iff₀ hqpos hipos] at hle
        have hcross : (f.coeff i₀).order.toNat * (d - i) ≤ (f.coeff i).order.toNat * (d - i₀) := by
          exact_mod_cast hle
        refine X_pow_dvd_of_le_order ?_
        rw [order_expand_toNat (by omega) hci]
        have : (f.coeff i₀).order.toNat * (d - i) ≤ (d - i₀) * (f.coeff i).order.toNat := by
          rw [Nat.mul_comm (d - i₀)]
          exact hcross
        exact_mod_cast this
    · have hieq : d - i = 0 := by omega
      rw [hieq, Nat.mul_zero, pow_zero]
      exact one_dvd _
  · -- at the minimising index the divisibility is sharp
    have hsharp : (PowerSeries.expand (d - i₀) (by omega) (f.coeff i₀)).order
        = (((d - i₀) * (f.coeff i₀).order.toNat : ℕ) : ℕ∞) :=
      order_expand_toNat (by omega) hci₀
    have hidx : (f.coeff i₀).order.toNat * (d - i₀)
        = (PowerSeries.expand (d - i₀) (by omega) (f.coeff i₀)).order.toNat := by
      rw [hsharp, ENat.toNat_coe, Nat.mul_comm]
    rw [hidx]
    exact PowerSeries.coeff_order (expand_ne_zero (by omega) hci₀)

end GaloisForLFunctions.HTGeometry
