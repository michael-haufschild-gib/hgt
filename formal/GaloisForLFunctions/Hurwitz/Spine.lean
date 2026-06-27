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
import GaloisForLFunctions.Hurwitz.DescentAlgebra

open Complex HurwitzDescent

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

/-- **Integer-shift collapse of the monodromy eigenvalue.** `e^{2πi·(-(a+w))} = e^{2πi·(-a)}` for
`w : ℕ`, since `e^{-2πiw} = 1`. This supplies the `hβ` (common eigenvalue) of `block_shift_eigen` for
both Hurwitz blocks: quadratic exponents `-(2s+w)` give `a = 2s`, eigenvalue `e^{2πi(-2s)} = e^{-4πis}`;
linear exponents `-(s+k)` give `a = s`, eigenvalue `e^{-2πis}`. -/
theorem exp_two_pi_I_neg_add_nat (a : ℂ) (w : ℕ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-(a + (w : ℂ))))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-a)) := by
  have hw : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-(w : ℂ))) = 1 := by
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (-(w : ℂ))
          = -((w : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) from by ring,
        Complex.exp_neg, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow, inv_one]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (-(a + (w : ℂ)))
        = 2 * (Real.pi : ℂ) * Complex.I * (-a) + 2 * (Real.pi : ℂ) * Complex.I * (-(w : ℂ))
        from by ring, Complex.exp_add, hw, mul_one]

/-- **A block with integer-spaced exponents and periodic coefficients is a shift-eigenvector.** This is
the bridge that produces the `hΦ`/`hΨ` hypotheses of `shift_eigenspace_separation` from the actual
Hurwitz blocks. The quadratic block `Φ(z) = ∑_w A_w(e^z)·e^{-(2s+w)z}` has exponents `β_w = -(2s+w)`
that are all congruent mod `1` (differ by integers `w`), so `e^{2πiβ_w} = e^{-4πis} =: λ` for every `w`
(the `e^{-2πiw}=1` collapse), and the coefficients `A_w(e^z)` are `2πi`-periodic — hence
`Φ(z+2πi) = λ·Φ(z)`. Same for the linear block with `λ = e^{-2πis}`. -/
theorem block_shift_eigen {K : ℕ} {β : Fin K → ℂ} {lam : ℂ} {c : Fin K → ℂ → ℂ}
    (hβ : ∀ k, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * β k) = lam)
    (hc : ∀ k z, c k (z + 2 * (Real.pi : ℂ) * Complex.I) = c k z) (z : ℂ) :
    (∑ k, c k (z + 2 * (Real.pi : ℂ) * Complex.I)
        * Complex.exp (β k * (z + 2 * (Real.pi : ℂ) * Complex.I)))
      = lam * ∑ k, c k z * Complex.exp (β k * z) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hc k z, show β k * (z + 2 * (Real.pi : ℂ) * Complex.I)
        = β k * z + 2 * (Real.pi : ℂ) * Complex.I * β k from by ring, Complex.exp_add, hβ k]
  ring

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
      simp only [Fin.val_last, Nat.sub_self, pow_zero, mul_one]
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
  have hsum := tendsto_finsetSum Finset.univ (fun w _ => hterm w)
  rw [Finset.sum_ite_eq' Finset.univ (Fin.last W) (fun _ => A (Fin.last W) 0)] at hsum
  simp only [Finset.mem_univ, if_true] at hsum
  have hzero : Filter.Tendsto (fun x => ∑ w : Fin (W + 1), A w x * x ^ (W - (w : ℕ))) l (nhds 0) :=
    tendsto_const_nhds.congr' (h.mono fun x hx => hx.symm)
  exact tendsto_nhds_unique hsum hzero

/-- **The block coefficient `tendsto` along a `0`-filter.** `x ↦ p(−n+x) → p(−n)`. -/
private theorem evalShift_tendsto {l : Filter ℂ} (hid : Filter.Tendsto (fun x : ℂ => x) l (nhds 0))
    (p : Polynomial ℂ) (n : ℕ) :
    Filter.Tendsto (fun x => p.eval (-(n : ℂ) + x)) l (nhds (p.eval (-(n : ℂ)))) := by
  have hin : Filter.Tendsto (fun x : ℂ => -(n : ℂ) + x) l (nhds (-(n : ℂ))) := by
    simpa using (tendsto_const_nhds (x := -(n : ℂ)) (f := l)).add hid
  exact (p.continuous.tendsto _).comp hin

/-- **Downward filtration: every quadratic-block coefficient vanishes.** Given (for all large `n`) the
peeled relation `∑_{w≤W} A_w(−n+x)·x^{W−w} = 0` near `x=0` with `A_w ∈ ℂ[a]` fixed polynomials, *all*
`A_w = 0`. Induction on `W`: `quadratic_filtration_top` extracts the top `A_W(−n) = 0` for every `n`, so
`A_W = 0` by `eq_zero_of_eventually_neg_nat_roots`; dropping it and cancelling one `x` gives the degree-`W−1`
relation, and the induction closes. This is the engine that converts "the block vanishes" into "the rational
coefficients vanish" — used for both the quadratic block (kills `q_{ij}`) and the linear block. -/
theorem quad_coeffs_vanish {l : Filter ℂ} [l.NeBot]
    (hid : Filter.Tendsto (fun x : ℂ => x) l (nhds 0)) (hne : ∀ᶠ x in l, x ≠ 0) :
    ∀ (W : ℕ) (A : ℕ → Polynomial ℂ) (N : ℕ),
      (∀ n, N ≤ n → ∀ᶠ x in l,
        ∑ w ∈ Finset.range (W + 1), (A w).eval (-(n : ℂ) + x) * x ^ (W - w) = 0) →
      ∀ w, w ≤ W → A w = 0 := by
  intro W
  induction W with
  | zero =>
    intro A N hrel w hw
    obtain rfl : w = 0 := Nat.le_zero.mp hw
    apply eq_zero_of_eventually_neg_nat_roots (N := N)
    intro n hn
    have hr := hrel n hn
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_self,
      pow_zero, mul_one] at hr
    have hz : Filter.Tendsto (fun x => (A 0).eval (-(n : ℂ) + x)) l (nhds 0) :=
      tendsto_const_nhds.congr' (hr.mono fun x hx => hx.symm)
    exact tendsto_nhds_unique (evalShift_tendsto hid (A 0) n) hz
  | succ W ih =>
    intro A N hrel w hw
    -- top coefficient A (W+1) vanishes
    have htop : A (W + 1) = 0 := by
      apply eq_zero_of_eventually_neg_nat_roots (N := N)
      intro n hn
      have htend : ∀ k : Fin (W + 2),
          Filter.Tendsto (fun x => (A (k : ℕ)).eval (-(n : ℂ) + x)) l
            (nhds ((fun x => (A (k : ℕ)).eval (-(n : ℂ) + x)) 0)) := by
        intro k
        simp only [add_zero]
        exact evalShift_tendsto hid (A k) n
      have hfin : ∀ᶠ x in l,
          ∑ k : Fin (W + 2), (fun x => (A (k : ℕ)).eval (-(n : ℂ) + x)) x * x ^ (W + 1 - (k : ℕ)) = 0 := by
        refine (hrel n hn).mono fun x hx => ?_
        rw [Fin.sum_univ_eq_sum_range (fun k => (A k).eval (-(n : ℂ) + x) * x ^ (W + 1 - k)) (W + 2)]
        exact hx
      have hq := quadratic_filtration_top (W := W + 1)
        (A := fun k => fun x => (A (k : ℕ)).eval (-(n : ℂ) + x)) hid htend hfin
      simpa [Polynomial.IsRoot, Fin.val_last] using hq
    -- reduce: drop the top, cancel one x
    have hreduced : ∀ n, N ≤ n → ∀ᶠ x in l,
        ∑ k ∈ Finset.range (W + 1), (A k).eval (-(n : ℂ) + x) * x ^ (W - k) = 0 := by
      intro n hn
      filter_upwards [hrel n hn, hne] with x hx hx0
      rw [Finset.sum_range_succ, htop] at hx
      simp only [Polynomial.eval_zero, zero_mul, add_zero] at hx
      have hfactor : ∑ k ∈ Finset.range (W + 1), (A k).eval (-(n : ℂ) + x) * x ^ (W + 1 - k)
          = x * ∑ k ∈ Finset.range (W + 1), (A k).eval (-(n : ℂ) + x) * x ^ (W - k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hkW : k ≤ W := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [show W + 1 - k = (W - k) + 1 from by omega, pow_succ]
        ring
      rw [hfactor] at hx
      exact (mul_eq_zero.mp hx).resolve_left hx0
    rcases Nat.lt_or_ge w (W + 1) with hlt | hge
    · exact ih A N hreduced w (Nat.lt_succ_iff.mp hlt)
    · obtain rfl : w = W + 1 := le_antisymm hw hge
      exact htop

/-- **Conversion bridge `z`-form → `x`-form (`x = e^z`).** The shift-eigenspace separation outputs a
block identity that holds for all `z` in the left half-plane `{Re z < B}`; `quad_coeffs_vanish` instead
consumes the relation in the local coordinate `x = e^z → 0`. Since `x ↦ log x` inverts `exp` and
`Re(log x) = log‖x‖ < B` exactly when `‖x‖ < e^B`, a `z`-form vanishing on the half-plane transfers to an
`x`-form vanishing on the punctured disk `{0 < ‖x‖ < e^B}`, hence eventually along `𝓝[≠] 0` — the filter
`quad_coeffs_vanish` runs on. -/
theorem rel_x_of_rel_exp {B : ℝ} {rel : ℂ → ℂ}
    (h : ∀ z : ℂ, z.re < B → rel (Complex.exp z) = 0) :
    ∀ᶠ x in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, rel x = 0 := by
  rw [Filter.eventually_iff, mem_nhdsWithin]
  refine ⟨Metric.ball 0 (Real.exp B), Metric.isOpen_ball,
    Metric.mem_ball_self (Real.exp_pos B), ?_⟩
  rintro x ⟨hxball, hx0⟩
  have hxne : x ≠ 0 := hx0
  have hlt : ‖x‖ < Real.exp B := by simpa [Complex.dist_eq] using hxball
  show rel x = 0
  rw [← Complex.exp_log hxne]
  apply h
  rw [Complex.log_re]
  calc Real.log ‖x‖ < Real.log (Real.exp B) :=
        Real.log_lt_log (norm_pos_iff.mpr hxne) hlt
    _ = B := Real.log_exp B

/-- **Single-block descent — the descent machine end-to-end on one block.** A block of the form
`∑_{w≤W} A_w(−n+e^z)·e^{−(2s+w)z}` (the post-separation quadratic block, with shifted exponent base `2s`;
the linear block is the `s` case) vanishing on the half-plane `{Re z < B n}` for every large `n` forces
*every* polynomial coefficient `A_w = 0`. Proof: the common factor `e^{(W+2s)z}` converts the block
identity into `∑_w A_w(−n+x)·x^{W−w} = 0` (`x = e^z`), `rel_x_of_rel_exp` moves it to `𝓝[≠]0`, and
`quad_coeffs_vanish` runs the downward induction. This packages `block_shift_eigen` →
`shift_eigenspace_separation` → `rel_x_of_rel_exp` → `quad_coeffs_vanish` into one reusable step. -/
theorem block_descent {s : ℂ} {A : ℕ → Polynomial ℂ} {W N : ℕ} {Bregion : ℕ → ℝ}
    (hblock : ∀ n, N ≤ n → ∀ z : ℂ, z.re < Bregion n →
        ∑ w ∈ Finset.range (W + 1), (A w).eval (-(n : ℂ) + Complex.exp z)
          * Complex.exp (-(2 * s + (w : ℂ)) * z) = 0) :
    ∀ w, w ≤ W → A w = 0 := by
  haveI : (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ).NeBot := Module.punctured_nhds_neBot ℝ ℂ 0
  have hid : Filter.Tendsto (fun x : ℂ => x) (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds 0) :=
    (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
  have hne : ∀ᶠ x in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx using hx
  refine quad_coeffs_vanish hid hne W A N ?_
  intro n hn
  apply rel_x_of_rel_exp (B := Bregion n)
  intro z hz
  have hb := hblock n hn z hz
  have hconv : ∑ w ∈ Finset.range (W + 1), (A w).eval (-(n : ℂ) + Complex.exp z)
        * Complex.exp z ^ (W - w)
      = Complex.exp (((W : ℂ) + 2 * s) * z)
        * ∑ w ∈ Finset.range (W + 1), (A w).eval (-(n : ℂ) + Complex.exp z)
          * Complex.exp (-(2 * s + (w : ℂ)) * z) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w hw => ?_)
    have hwW : w ≤ W := Nat.lt_succ_iff.mp (Finset.mem_range.mp hw)
    rw [← Complex.exp_nat_mul, Nat.cast_sub hwW, ← mul_assoc,
      mul_comm (Complex.exp (((W : ℂ) + 2 * s) * z)) ((A w).eval (-(n : ℂ) + Complex.exp z)),
      mul_assoc, ← Complex.exp_add]
    ring_nf
  rw [hconv, hb, mul_zero]

end HurwitzSpine
