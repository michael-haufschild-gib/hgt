import GaloisForLFunctions.RHTower.CalogeroVirialCollapse

/-!
# The pair-kernel dichotomy for Lyapunov observables

A pairwise dynamics of the zeros, `ẋ_j = Σ_{k≠j} F(x_j - x_k)` with `F` odd, moves an observable
`Σ_j G(x_j)` at the rate

```text
  d/dτ Σ_j G(x_j) = (1/2) Σ_{j≠k} (G'(x_j) - G'(x_k)) · F(x_j - x_k) .
```

The rate is `≤ 0` for *every* finite configuration exactly when the two-point condition
`(g x - g y)·F(x - y) ≤ 0` holds for `g = G'`, since two-point configurations already test it.
This file classifies the weights `g` that satisfy it.

* If `F < 0` on `(0,∞)` — a purely attractive long-range kernel, the de Bruijn--Newman case — the
  condition says exactly that `g` is monotone, i.e. that `G` is convex.  A convex function bounded
  above on `ℝ` is constant, so no *bounded* observable of this form has a sign.
* If `F` is negative on one interval of `(0,∞)` and positive on another, the condition forces `g`
  to be constant, so `G` is affine and `Σ_j G(x_j)` is conserved rather than monotone.

Together: **no pairwise zero dynamics admits a bounded nonconstant Lyapunov observable of the form
`Σ_j G(x_j)`.**  The obstruction is not special to the kernel `1/u`; it is a property of the
two-point sign condition itself.  The second case needs no irrationality and no regularity of `g`:
a sign interval of length `β - α` makes `g` monotone under every shift `t` beyond
`αβ/(β-α)`, and two intervals of opposite sign make `g` both nondecreasing and nonincreasing under
all large shifts.
-/

namespace RHTower

/-- The two-point sign condition: `Σ_j G(x_j)` has rate `≤ 0` along the `F`-dynamics for every
finite configuration exactly when `g = G'` satisfies this. -/
def SignedWeight (F g : ℝ → ℝ) : Prop := ∀ x y : ℝ, (g x - g y) * F (x - y) ≤ 0

/-- **Attractive kernel: the signed weights are the monotone ones.** -/
theorem monotone_of_signedWeight_neg {F g : ℝ → ℝ} (hF : ∀ u : ℝ, 0 < u → F u < 0)
    (hg : SignedWeight F g) : Monotone g := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with h | h
  · rw [h]
  · have hpos : 0 < y - x := sub_pos.mpr h
    have hFneg : F (y - x) < 0 := hF _ hpos
    have := hg y x
    nlinarith

/-- A single sign interval propagates monotonicity to every large shift. -/
theorem le_shift_of_interval {g : ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (h : ∀ z : ℝ, ∀ s : ℝ, α < s → s < β → g z ≤ g (z + s))
    {t : ℝ} (ht : α * β / (β - α) < t) (x : ℝ) : g x ≤ g (x + t) := by
  have hβ : 0 < β := lt_trans hα hαβ
  have hd : 0 < β - α := sub_pos.mpr hαβ
  have htpos : 0 < t := by
    have : 0 < α * β / (β - α) := by positivity
    linarith
  have hwidth : 1 < t / α - t / β := by
    rw [div_sub_div _ _ (ne_of_gt hα) (ne_of_gt hβ), lt_div_iff₀ (by positivity)]
    rw [div_lt_iff₀ hd] at ht
    nlinarith
  set k : ℕ := ⌊t / β⌋₊ + 1 with hk
  have hkfloor : t / β < (k : ℝ) := by
    rw [hk]; push_cast; exact Nat.lt_floor_add_one (t / β)
  have hkle : (k : ℝ) ≤ t / β + 1 := by
    rw [hk]; push_cast
    have := Nat.floor_le (a := t / β) (by positivity)
    linarith
  have hkup : (k : ℝ) < t / α := by linarith
  have hkpos : 0 < (k : ℝ) := lt_of_le_of_lt (le_of_lt (by positivity : (0:ℝ) < t / β)) hkfloor
  set s : ℝ := t / (k : ℝ) with hs
  have hsα : α < s := by
    rw [hs, lt_div_iff₀ hkpos]
    rw [lt_div_iff₀ hα] at hkup
    linarith
  have hsβ : s < β := by
    rw [hs, div_lt_iff₀ hkpos]
    rw [div_lt_iff₀ hβ] at hkfloor
    linarith
  have step : ∀ n : ℕ, g x ≤ g (x + (n : ℝ) * s) := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      have := h (x + (m : ℝ) * s) s hsα hsβ
      have hrw : x + (m : ℝ) * s + s = x + ((m : ℝ) + 1) * s := by ring
      rw [hrw] at this
      push_cast
      linarith
  have hks : (k : ℝ) * s = t := by
    rw [hs]; field_simp
  have := step k
  rwa [hks] at this

/-- **Sign-changing kernel: only the constants have a sign.** -/
theorem eq_const_of_signedWeight_signChange {F g : ℝ → ℝ} {α₁ β₁ α₂ β₂ : ℝ}
    (h1 : 0 < α₁) (h1' : α₁ < β₁) (hneg : ∀ u : ℝ, α₁ < u → u < β₁ → F u < 0)
    (h2 : 0 < α₂) (h2' : α₂ < β₂) (hpos : ∀ u : ℝ, α₂ < u → u < β₂ → 0 < F u)
    (hg : SignedWeight F g) (a b : ℝ) : g a = g b := by
  have hup : ∀ z : ℝ, ∀ s : ℝ, α₁ < s → s < β₁ → g z ≤ g (z + s) := by
    intro z s hs1 hs2
    have hFneg : F s < 0 := hneg s hs1 hs2
    have hrw : z + s - z = s := by ring
    have := hg (z + s) z
    rw [hrw] at this
    nlinarith
  have hdown : ∀ z : ℝ, ∀ s : ℝ, α₂ < s → s < β₂ → (fun w => -g w) z ≤ (fun w => -g w) (z + s) := by
    intro z s hs1 hs2
    have hFpos : 0 < F s := hpos s hs1 hs2
    have hrw : z + s - z = s := by ring
    have := hg (z + s) z
    rw [hrw] at this
    show -g z ≤ -g (z + s)
    nlinarith
  set T : ℝ := max (α₁ * β₁ / (β₁ - α₁)) (α₂ * β₂ / (β₂ - α₂)) with hT
  have hflat : ∀ z : ℝ, ∀ t : ℝ, T < t → g (z + t) = g z := by
    intro z t hts
    have ht1 : α₁ * β₁ / (β₁ - α₁) < t := lt_of_le_of_lt (le_max_left _ _) hts
    have ht2 : α₂ * β₂ / (β₂ - α₂) < t := lt_of_le_of_lt (le_max_right _ _) hts
    have hle := le_shift_of_interval h1 h1' hup ht1 z
    have hge := le_shift_of_interval h2 h2' hdown ht2 z
    have hge' : -g z ≤ -g (z + t) := hge
    linarith
  have hca : T < (max a b + T + 1) - a := by
    have hle : a ≤ max a b := le_max_left a b
    linarith
  have hcb : T < (max a b + T + 1) - b := by
    have hle : b ≤ max a b := le_max_right a b
    linarith
  have ha := hflat a ((max a b + T + 1) - a) hca
  have hb := hflat b ((max a b + T + 1) - b) hcb
  have hra : a + ((max a b + T + 1) - a) = max a b + T + 1 := by ring
  have hrb : b + ((max a b + T + 1) - b) = max a b + T + 1 := by ring
  rw [hra] at ha
  rw [hrb] at hb
  rw [← ha, ← hb]



/-! ### The two-point condition is necessary and sufficient -/

/-- Symmetrised rate of the observable `Σ_j G(x_j)` along the `F`-dynamics. -/
theorem two_mul_pairRate {ι : Type*} (S : Finset ι) (x : ι → ℝ) (F g : ℝ → ℝ)
    (hodd : ∀ u : ℝ, F (-u) = -F u) :
    2 * ∑ j ∈ S, g (x j) * ∑ k ∈ S, F (x j - x k)
      = ∑ j ∈ S, ∑ k ∈ S, (g (x j) - g (x k)) * F (x j - x k) := by
  have hswap : (∑ j ∈ S, ∑ k ∈ S, g (x k) * F (x k - x j))
      = ∑ j ∈ S, ∑ k ∈ S, g (x j) * F (x j - x k) := Finset.sum_comm
  have hpair : ∀ j k : ι,
      g (x j) * F (x j - x k) + g (x k) * F (x k - x j)
        = (g (x j) - g (x k)) * F (x j - x k) := by
    intro j k
    have h := hodd (x j - x k)
    rw [show -(x j - x k) = x k - x j by ring] at h
    rw [h]; ring
  calc 2 * ∑ j ∈ S, g (x j) * ∑ k ∈ S, F (x j - x k)
      = 2 * ∑ j ∈ S, ∑ k ∈ S, g (x j) * F (x j - x k) := by
        simp only [Finset.mul_sum]
    _ = (∑ j ∈ S, ∑ k ∈ S, g (x j) * F (x j - x k))
          + ∑ j ∈ S, ∑ k ∈ S, g (x k) * F (x k - x j) := by
        rw [hswap]; ring
    _ = ∑ j ∈ S, ∑ k ∈ S, (g (x j) * F (x j - x k) + g (x k) * F (x k - x j)) := by
        simp only [Finset.sum_add_distrib]
    _ = _ := Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hpair j k

/-- **Sufficiency.**  A signed weight makes the rate nonpositive for every configuration. -/
theorem pairRate_nonpos {ι : Type*} (S : Finset ι) (x : ι → ℝ) {F g : ℝ → ℝ}
    (hodd : ∀ u : ℝ, F (-u) = -F u) (hg : SignedWeight F g) :
    ∑ j ∈ S, g (x j) * ∑ k ∈ S, F (x j - x k) ≤ 0 := by
  have h := two_mul_pairRate S x F g hodd
  have hnn : ∑ j ∈ S, ∑ k ∈ S, (g (x j) - g (x k)) * F (x j - x k) ≤ 0 := by
    refine Finset.sum_nonpos fun j _ => Finset.sum_nonpos fun k _ => ?_
    have := hg (x j) (x k)
    linarith
  linarith

/-- **Necessity.**  A two-point configuration realises the two-point condition exactly. -/
theorem pairRate_two (F g : ℝ → ℝ) (hodd : ∀ u : ℝ, F (-u) = -F u) (p q : ℝ) :
    ∑ j ∈ (Finset.univ : Finset (Fin 2)),
        g (![p, q] j) * ∑ k ∈ (Finset.univ : Finset (Fin 2)), F (![p, q] j - ![p, q] k)
      = (g p - g q) * F (p - q) := by
  have hF0 : F 0 = 0 := by
    have h := hodd 0
    rw [neg_zero] at h
    linarith
  have hqp : F (q - p) = -F (p - q) := by
    have h := hodd (p - q)
    rw [show -(p - q) = q - p by ring] at h
    exact h
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_self, hF0, hqp]
  ring

/-! ### The complete no-go -/

/-- **Attractive kernel: no bounded nonconstant Lyapunov observable.**  If `G` is differentiable,
its derivative is a signed weight for a purely attractive kernel, and `G` is bounded above, then
`G` is constant. -/
theorem eq_const_of_signedWeight_deriv_of_le {F G : ℝ → ℝ}
    (hF : ∀ u : ℝ, 0 < u → F u < 0) (hdiff : Differentiable ℝ G)
    (hg : SignedWeight F (deriv G)) {M : ℝ} (hM : ∀ y, G y ≤ M) (a b : ℝ) : G a = G b := by
  have hmono : Monotone (deriv G) := monotone_of_signedWeight_neg hF hg
  have hconv : ConvexOn ℝ Set.univ G :=
    MonotoneOn.convexOn_of_deriv convex_univ hdiff.continuous.continuousOn
      hdiff.differentiableOn (fun u _ v _ huv => hmono huv)
  exact eq_of_convexOn_univ_of_le hconv hM a b

/-- **Sign-changing kernel: the observable is conserved, not monotone.**  Its weight is constant,
so `G` is affine and `Σ_j G(x_j)` is a conserved quantity. -/
theorem eq_const_deriv_of_signChange {F G : ℝ → ℝ} {α₁ β₁ α₂ β₂ : ℝ}
    (h1 : 0 < α₁) (h1' : α₁ < β₁) (hneg : ∀ u : ℝ, α₁ < u → u < β₁ → F u < 0)
    (h2 : 0 < α₂) (h2' : α₂ < β₂) (hpos : ∀ u : ℝ, α₂ < u → u < β₂ → 0 < F u)
    (hg : SignedWeight F (deriv G)) (a b : ℝ) : deriv G a = deriv G b :=
  eq_const_of_signedWeight_signChange h1 h1' hneg h2 h2' hpos hg a b

end RHTower
