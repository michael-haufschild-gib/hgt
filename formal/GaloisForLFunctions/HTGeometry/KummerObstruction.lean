/-
# Kummer obstruction I — roots force divisibility of zero orders; root rigidity

Generic complex-analytic base layer for the MWM lane
(docs/drafts/rh-monodromy-weight-mismatch/, Arc A).  An analytic `n`-th root of a function
forces every vanishing order to be divisible by `n` (`root_orders_dvd`), and is rigid: on a
preconnected open set it is determined by its value at a single point where the base function
does not vanish (`pow_root_unique`) — proved derivative-free via the geometric-sum
factorisation `(∑ g₁^j g₂^{n-1-j}) (g₁ - g₂) = g₁^n - g₂^n` and the identity theorem.
Also records the convex simply-connectedness discharge used by the downstream root-existence
arguments.  All ambient names verified against this toolchain (/tmp/mwm_a0_probe.lean,
2026-07-03).
-/
import Mathlib

namespace RHTower

open Complex Filter Set

/-- A nonempty convex subset of `ℂ` is simply connected. -/
theorem isSimplyConnected_of_convex {s : Set ℂ} (hs : Convex ℝ s) (hne : s.Nonempty) :
    IsSimplyConnected s := by
  haveI : ContractibleSpace s := hs.contractibleSpace hne
  exact SimplyConnectedSpace.ofContractible _

/-- **Roots force divisibility.**  If `g` is analytic on an open set `U` with `g ^ n = f`
pointwise on `U`, then the analytic vanishing order of `f` at every point of `U` is divisible
by `n`. -/
theorem root_orders_dvd {f g : ℂ → ℂ} {U : Set ℂ} {n : ℕ} (hU : IsOpen U)
    (hg : AnalyticOnNhd ℂ g U) (hpow : ∀ s ∈ U, g s ^ n = f s) {z₀ : ℂ} (hz : z₀ ∈ U) :
    (n : ℕ∞) ∣ analyticOrderAt f z₀ := by
  have hev : (g ^ n) =ᶠ[nhds z₀] f := by
    filter_upwards [hU.mem_nhds hz] with s hs
    exact hpow s hs
  have h1 : analyticOrderAt f z₀ = n • analyticOrderAt g z₀ :=
    (analyticOrderAt_congr hev).symm.trans (analyticOrderAt_pow (hg z₀ hz) n)
  rw [h1, nsmul_eq_mul]
  exact dvd_mul_right (n : ℕ∞) (analyticOrderAt g z₀)

/-- **Root rigidity.**  Two analytic `n`-th roots (`0 < n`) of the same function on a
preconnected open set that agree at one point where the function does not vanish agree
everywhere. -/
theorem pow_root_unique {f g₁ g₂ : ℂ → ℂ} {U : Set ℂ} {n : ℕ} (hn : 0 < n)
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (h₁ : AnalyticOnNhd ℂ g₁ U) (h₂ : AnalyticOnNhd ℂ g₂ U)
    (hp₁ : ∀ s ∈ U, g₁ s ^ n = f s) (hp₂ : ∀ s ∈ U, g₂ s ^ n = f s)
    {z₀ : ℂ} (hz : z₀ ∈ U) (hf0 : f z₀ ≠ 0) (hpt : g₁ z₀ = g₂ z₀) :
    Set.EqOn g₁ g₂ U := by
  have hg₂0 : g₂ z₀ ≠ 0 := fun h0 => hf0 (by rw [← hp₂ z₀ hz, h0, zero_pow hn.ne'])
  have hqan : AnalyticAt ℂ (fun s => ∑ j ∈ Finset.range n, g₁ s ^ j * g₂ s ^ (n - 1 - j)) z₀ :=
    Finset.analyticAt_fun_sum _ (fun j _ => ((h₁ z₀ hz).pow j).mul ((h₂ z₀ hz).pow (n - 1 - j)))
  have hqz : (∑ j ∈ Finset.range n, g₁ z₀ ^ j * g₂ z₀ ^ (n - 1 - j)) =
      (n : ℂ) * g₂ z₀ ^ (n - 1) := by
    rw [hpt]
    have hterm : ∀ j ∈ Finset.range n, g₂ z₀ ^ j * g₂ z₀ ^ (n - 1 - j) = g₂ z₀ ^ (n - 1) := by
      intro j hj
      have hjn := Finset.mem_range.mp hj
      rw [← pow_add]
      congr 1
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hq0 : (∑ j ∈ Finset.range n, g₁ z₀ ^ j * g₂ z₀ ^ (n - 1 - j)) ≠ 0 := by
    rw [hqz]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') (pow_ne_zero _ hg₂0)
  have hev : g₁ =ᶠ[nhds z₀] g₂ := by
    filter_upwards [hqan.continuousAt.eventually_ne hq0, hU.mem_nhds hz] with s hqs hs
    have hfac : (∑ j ∈ Finset.range n, g₁ s ^ j * g₂ s ^ (n - 1 - j)) * (g₁ s - g₂ s) = 0 := by
      rw [geom_sum₂_mul, hp₁ s hs, hp₂ s hs, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h hqs
    · exact sub_eq_zero.mp h
  exact h₁.eqOn_of_preconnected_of_eventuallyEq h₂ hUc hz hev

/-- Divisibility descends along the coercion `ℕ → ℕ∞` when the divisor is nonzero. -/
theorem natCast_dvd_natCast_of_enat {a b : ℕ} (ha : a ≠ 0) (h : (a : ℕ∞) ∣ (b : ℕ∞)) :
    a ∣ b := by
  obtain ⟨c, hc⟩ := h
  have hcne : c ≠ ⊤ := by
    intro hct
    rw [hct, ENat.mul_top (by exact_mod_cast ha)] at hc
    exact (by simp : ((b : ℕ∞)) ≠ ⊤) hc
  refine ⟨c.toNat, ?_⟩
  have h1 : ((b : ℕ∞)) = ((a * c.toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_mul, ENat.coe_toNat hcne]
    exact hc
  exact_mod_cast h1

end RHTower
