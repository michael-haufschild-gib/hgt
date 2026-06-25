/-
# Hurwitz N=2 spine — the `z = log x` substitution glue

The descent runs in the coordinate `z = log x` (`x = a + n`), where the exponent filtration
(`ExponentFiltration.coeffs_zero_of_exp_periodic_combo`) applies: the singular term `x^{-(s+k)}` becomes
`exp(-(s+k)·z)` and the regular part `R(x) = R(e^z)` becomes `2πi`-periodic. This file supplies the two
substitution facts that bridge the Hurwitz-zeta local expansion to the exp-form the filtration consumes.

* `comp_exp_periodic` — `R(e^z)` is `2πi`-periodic (`e^{z+2πi} = e^z`).
* `cexp_cpow_strip` — on the strip `Im z ∈ (-π, π]`, `(e^z)^w = e^{w·z}` (so `x^{-(s+k)} = e^{-(s+k)z}`).
-/
import GaloisForLFunctions.Hurwitz.ExponentFiltration

open Complex

namespace HurwitzSpine

/-- **The regular part is `2πi`-periodic in `z = log x`.** `R(e^{z+2πi}) = R(e^z)` since `e^{2πi} = 1`.
This is the `H` (periodic) input of `coeffs_zero_of_exp_periodic_combo`. -/
theorem comp_exp_periodic (R : ℂ → ℂ) (z : ℂ) :
    R (Complex.exp (z + 2 * (Real.pi : ℂ) * Complex.I)) = R (Complex.exp z) := by
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- **Singular term in `z = log x`.** On the strip `Im z ∈ (-π, π]`, `(e^z)^w = e^{w·z}`; applied with
`z = log x` and `w = -(s+k)`, the Hurwitz singular term `x^{-(s+k)}` is `e^{-(s+k)·log x}`, the
exponential the filtration separates. -/
theorem cexp_cpow_strip {z : ℂ} (h1 : -Real.pi < z.im) (h2 : z.im ≤ Real.pi) (w : ℂ) :
    (Complex.exp z) ^ w = Complex.exp (w * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero z), Complex.log_exp h1 h2, mul_comm]

/-- **Exponent filtration on a `2πi`-invariant open region.** The Hurwitz relation holds only on a left
half-plane in `z = log x` (`x → 0`), not all `z`; this is the region version of
`coeffs_zero_of_exp_periodic_combo`. The shift `z ↦ z + 2πi` stays in the region (`2πi`-invariance) and
fixes the periodic `H`, so the shift-difference is a pure exponential combination vanishing on the open
region; `expLin_eq_zero_on_open` collapses it, and `β_k ∉ ℤ` removes the scalar. -/
theorem coeffs_zero_of_exp_periodic_combo_on_open {K : ℕ} {β : Fin K → ℂ}
    (hβ : Function.Injective β)
    (hβint : ∀ k, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * β k) ≠ 1) {c : Fin K → ℂ}
    {H : ℂ → ℂ} {U : Set ℂ} (hUo : IsOpen U) (hUne : U.Nonempty)
    (hUinv : ∀ z ∈ U, z + 2 * (Real.pi : ℂ) * Complex.I ∈ U)
    (hper : ∀ z, H (z + 2 * (Real.pi : ℂ) * Complex.I) = H z)
    (h : ∀ z ∈ U, ∑ k, c k * Complex.exp (β k * z) + H z = 0) : c = 0 := by
  have hexp : ∀ (k : Fin K) (z : ℂ), Complex.exp (β k * (z + 2 * (Real.pi : ℂ) * Complex.I))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * β k) * Complex.exp (β k * z) := by
    intro k z
    rw [show β k * (z + 2 * (Real.pi : ℂ) * Complex.I)
          = β k * z + 2 * (Real.pi : ℂ) * Complex.I * β k from by ring, Complex.exp_add]
    ring
  have hdiff : ∀ z ∈ U, ∑ k, (c k * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * β k) - 1))
      * Complex.exp (β k * z) = 0 := by
    intro z hz
    have h1 := h (z + 2 * (Real.pi : ℂ) * Complex.I) (hUinv z hz)
    rw [hper z] at h1
    have h2 := h z hz
    have key : ∑ k, c k * Complex.exp (β k * (z + 2 * (Real.pi : ℂ) * Complex.I))
        = ∑ k, c k * Complex.exp (β k * z) := by linear_combination h1 - h2
    rw [show (0 : ℂ) = (∑ k, c k * Complex.exp (β k * (z + 2 * (Real.pi : ℂ) * Complex.I)))
          - ∑ k, c k * Complex.exp (β k * z) from by rw [key]; ring,
        ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by rw [hexp k z]; ring)
  have hcd : (fun k => c k * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * β k) - 1)) = 0 :=
    HurwitzExp.expLin_eq_zero_on_open hβ hUo hUne hdiff
  funext k
  have := congrFun hcd k
  exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (hβint k))

/-- **Shift-eigenspace separation (the periodic-coefficient filtration core).** In `z = log x` the N=2
relation splits by *monodromy eigenvalue* of the shift `S : f ↦ f(·+2πi)`: the doubly-singular quadratic
block `Φ` (all exponents `-(2s+w)`, `w∈{0..4}`, share eigenvalue `λq = e^{-4πis}` since `e^{-2πiw}=1`),
the singular linear+cross block `Ψ` (exponents `-(s+k)`, share `λl = e^{-2πis}`), and the regular block
`Θ` (eigenvalue `1`). The three eigenvalues are distinct exactly when `2s ∉ ℤ` and `s ∉ ℤ`. Evaluating
the relation at `z, z+2πi, z+4πi` is a `3×3` Vandermonde in `(Φ,Ψ,Θ)` with nodes `(λq,λl,1)`; the
nonzero determinant `(λq-λl)(λq-1)(λl-1)` forces each block to vanish *separately*. **This is the step
that decouples the cross-terms:** the quadratic block carries NO Hurwitz tails, so killing it (next
filtration) sets every `q_{ij}=0`, which annihilates the cross-terms inside `Ψ` and leaves the linear
block clean. -/
theorem shift_eigenspace_separation {U : Set ℂ} {Φ Ψ Θ : ℂ → ℂ} {lq ll : ℂ}
    (hUinv : ∀ z ∈ U, z + 2 * (Real.pi : ℂ) * Complex.I ∈ U)
    (hΦ : ∀ z ∈ U, Φ (z + 2 * (Real.pi : ℂ) * Complex.I) = lq * Φ z)
    (hΨ : ∀ z ∈ U, Ψ (z + 2 * (Real.pi : ℂ) * Complex.I) = ll * Ψ z)
    (hΘ : ∀ z ∈ U, Θ (z + 2 * (Real.pi : ℂ) * Complex.I) = Θ z)
    (hql : lq ≠ ll) (hq1 : lq ≠ 1) (hl1 : ll ≠ 1)
    (h : ∀ z ∈ U, Φ z + Ψ z + Θ z = 0) :
    ∀ z ∈ U, Φ z = 0 ∧ Ψ z = 0 ∧ Θ z = 0 := by
  intro z hz
  have hz1 : z + 2 * (Real.pi : ℂ) * Complex.I ∈ U := hUinv z hz
  have hz2 : (z + 2 * (Real.pi : ℂ) * Complex.I) + 2 * (Real.pi : ℂ) * Complex.I ∈ U := hUinv _ hz1
  -- The three scalar equations in (Φ z, Ψ z, Θ z), nodes (lq, ll, 1).
  have e1 : Φ z + Ψ z + Θ z = 0 := h z hz
  have e2 : lq * Φ z + ll * Ψ z + Θ z = 0 := by
    have := h _ hz1; rw [hΦ z hz, hΨ z hz, hΘ z hz] at this; linear_combination this
  have e3 : lq ^ 2 * Φ z + ll ^ 2 * Ψ z + Θ z = 0 := by
    have h3 := h _ hz2
    rw [hΦ _ hz1, hΨ _ hz1, hΘ _ hz1, hΦ z hz, hΨ z hz, hΘ z hz] at h3
    linear_combination h3
  -- Vandermonde elimination.
  have hΨ0 : Ψ z = 0 := by
    have hv : (ll - 1) * (ll - lq) * Ψ z = 0 := by
      linear_combination lq * e1 - (1 + lq) * e2 + e3
    rcases mul_eq_zero.mp hv with hk | hk
    · rcases mul_eq_zero.mp hk with h' | h'
      · exact absurd (sub_eq_zero.mp h') hl1
      · exact absurd (sub_eq_zero.mp h') (fun hc => hql hc.symm)
    · exact hk
  have hΦ0 : Φ z = 0 := by
    have hv : (lq - 1) * Φ z = 0 := by linear_combination e2 - e1 - (ll - 1) * hΨ0
    exact (mul_eq_zero.mp hv).resolve_left (sub_ne_zero.mpr hq1)
  refine ⟨hΦ0, hΨ0, ?_⟩
  linear_combination e1 - hΦ0 - hΨ0

/-- **Hurwitz linear-block close.** After the quadratic filtration zeroes every `q_{ij}` (so the
cross-terms vanish), the surviving singular part is the pure linear block `∑_k l_k·x^{-(s+k)}` plus a
regular `2πi`-periodic remainder. In `z = log x` this is `∑_k l_k·e^{-(s+k)z} + H(z) = 0` on the region,
with exponents `β_k = -(s+k)` distinct and `e^{2πiβ_k} = e^{-2πis} ≠ 1` exactly when `s ∉ ℤ`. So
`coeffs_zero_of_exp_periodic_combo_on_open` forces every `l_k = 0` (and then the regular part `= 0`
forces the constant). This is the final, cleanest descent step. -/
theorem hurwitz_linear_vanish {K : ℕ} {s : ℂ} (hs : ∀ n : ℤ, (n : ℂ) ≠ s)
    {c : Fin K → ℂ} {H : ℂ → ℂ} {U : Set ℂ} (hUo : IsOpen U) (hUne : U.Nonempty)
    (hUinv : ∀ z ∈ U, z + 2 * (Real.pi : ℂ) * Complex.I ∈ U)
    (hper : ∀ z, H (z + 2 * (Real.pi : ℂ) * Complex.I) = H z)
    (h : ∀ z ∈ U, ∑ k : Fin K, c k * Complex.exp (-(s + (k : ℂ)) * z) + H z = 0) : c = 0 := by
  refine coeffs_zero_of_exp_periodic_combo_on_open (β := fun k => -(s + (k : ℂ))) ?_ ?_ hUo hUne
    hUinv hper h
  · intro k1 k2 hk
    simp only [neg_inj, add_right_inj] at hk
    exact Fin.ext (by exact_mod_cast hk)
  · intro k hcon
    rw [Complex.exp_eq_one_iff] at hcon
    obtain ⟨n, hn⟩ := hcon
    apply hs (-(n + (k : ℤ)))
    have hpiI : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hcancel : -(s + (k : ℂ)) = (n : ℂ) := by
      have h2 : (2 * (Real.pi : ℂ) * Complex.I) * (-(s + (k : ℂ)))
          = (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by linear_combination hn
      exact mul_left_cancel₀ hpiI h2
    push_cast
    linear_combination hcancel

/-- **Quadratic-filtration leading coefficient (the Laurent peel).** Once `shift_eigenspace_separation`
gives the quadratic block `∑_{w≤W} A_w(x)·x^{-w} = 0` (here written multiplied through by `x^W`, so
`∑_w A_w(x)·x^{W-w} = 0`, no negative powers), let `x → 0`: every `w < W` term carries `x^{W-w}` with
`W-w ≥ 1` and dies, leaving the top coefficient `A_W(0)`. So `A_W(0) = 0`. Applied at `x = a+n` for every
large `n`, this gives `A_W(-n) = 0` for all `n`; since `A_W` is a fixed rational function (`A_W = ∑_{i+j=W}
q_{ij}`), `DescentAlgebra.eq_zero_of_eventually_neg_nat_roots` forces `A_W ≡ 0`, then the relation drops
to degree `W-1` and the peel repeats — the downward induction that zeroes every quadratic coefficient. -/
theorem quadratic_filtration_top {W : ℕ} {A : Fin (W + 1) → ℂ → ℂ} {l : Filter ℂ} [l.NeBot]
    (hid : Filter.Tendsto (fun x : ℂ => x) l (nhds 0))
    (hA : ∀ w : Fin (W + 1), Filter.Tendsto (A w) l (nhds (A w 0)))
    (h : ∀ᶠ x in l, ∑ w : Fin (W + 1), A w x * x ^ (W - (w : ℕ)) = 0) :
    A (Fin.last W) 0 = 0 := by
  have hterm : ∀ w : Fin (W + 1), Filter.Tendsto (fun x => A w x * x ^ (W - (w : ℕ))) l
      (nhds (if w = Fin.last W then A (Fin.last W) 0 else 0)) := by
    intro w
    by_cases hw : w = Fin.last W
    · subst hw
      simp only [if_pos rfl, Fin.val_last, Nat.sub_self, pow_zero, mul_one]
      exact hA _
    · rw [if_neg hw]
      have hlt : (w : ℕ) < W := by
        have hwlt := w.isLt
        have hne : (w : ℕ) ≠ W := fun hc => hw (Fin.ext (by rw [Fin.val_last]; exact hc))
        omega
      have hpow : Filter.Tendsto (fun x : ℂ => x ^ (W - (w : ℕ))) l (nhds 0) := by
        have hp := hid.pow (W - (w : ℕ))
        rwa [zero_pow (by omega : W - (w : ℕ) ≠ 0)] at hp
      have := (hA w).mul hpow
      rwa [mul_zero] at this
  have hsum := tendsto_finset_sum Finset.univ (fun w _ => hterm w)
  rw [Finset.sum_ite_eq' Finset.univ (Fin.last W) (fun _ => A (Fin.last W) 0)] at hsum
  simp only [Finset.mem_univ, if_true] at hsum
  have hzero : Filter.Tendsto (fun x => ∑ w : Fin (W + 1), A w x * x ^ (W - (w : ℕ))) l (nhds 0) :=
    tendsto_const_nhds.congr' (h.mono fun x hx => hx.symm)
  exact tendsto_nhds_unique hsum hzero

end HurwitzSpine
