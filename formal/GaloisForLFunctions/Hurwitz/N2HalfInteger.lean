/-
# Hurwitz N=2 — the half-integer block split

When `s ∉ ℤ` but `2s ∈ ℤ`, the three-block separation used by
`N2Final.hurwitz_n2_unconditional` degenerates: the quadratic block and the
regular block have the same monodromy eigenvalue `1`, while the middle block has
eigenvalue `-1`.  This file proves the exact order-two split, the Laurent
separation of the invariant residual, and the combined N=2 theorem with no
`2s ∉ ℤ` hypothesis:

* the odd/eigenvalue-`-1` block `Ψ` vanishes;
* the invariant part satisfies `Φ + Θ = 0`;
* integer-pole Laurent dominance separates `Φ` from the regular block `Θ`.
-/
import GaloisForLFunctions.Hurwitz.N2Main
import GaloisForLFunctions.Hurwitz.N2Final
import GaloisForLFunctions.Hurwitz.MonodromyScalar

open Complex Filter Topology HurwitzEncoding HurwitzSpine HurwitzN2Tail

namespace HurwitzN2HalfInteger

/-- **Order-two eigenspace split.**  If `Φ` and `Θ` are shift-invariant while
`Ψ` changes sign, then a relation `Φ + Ψ + Θ = 0` forces `Ψ = 0` and leaves the
invariant residue `Φ + Θ = 0`. -/
theorem shift_eigenspace_separation_order_two {U : Set ℂ} {Φ Ψ Θ : ℂ → ℂ}
    (hUinv : ∀ z ∈ U, z + 2 * (Real.pi : ℂ) * Complex.I ∈ U)
    (hΦ : ∀ z ∈ U, Φ (z + 2 * (Real.pi : ℂ) * Complex.I) = Φ z)
    (hΨ : ∀ z ∈ U, Ψ (z + 2 * (Real.pi : ℂ) * Complex.I) = -Ψ z)
    (hΘ : ∀ z ∈ U, Θ (z + 2 * (Real.pi : ℂ) * Complex.I) = Θ z)
    (h : ∀ z ∈ U, Φ z + Ψ z + Θ z = 0) :
    ∀ z ∈ U, Ψ z = 0 ∧ Φ z + Θ z = 0 := by
  intro z hz
  have hz1 : z + 2 * (Real.pi : ℂ) * Complex.I ∈ U := hUinv z hz
  have e0 : Φ z + Ψ z + Θ z = 0 := h z hz
  have e1 : Φ z - Ψ z + Θ z = 0 := by
    have hshift := h _ hz1
    rw [hΦ z hz, hΨ z hz, hΘ z hz] at hshift
    linear_combination hshift
  have hΨ0 : Ψ z = 0 := by
    have htwo : (2 : ℂ) * Ψ z = 0 := by
      linear_combination e0 - e1
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  refine ⟨hΨ0, ?_⟩
  linear_combination e0 - hΨ0

/-- `2s ∈ ℤ` makes the quadratic block eigenvalue equal to `1`. -/
theorem quadratic_eigenvalue_eq_one_of_two_mul_int {s : ℂ}
    (h2s : ∃ m : ℤ, 2 * s = (m : ℂ)) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-(2 * s))) = 1 := by
  rw [Complex.exp_eq_one_iff]
  obtain ⟨m, hm⟩ := h2s
  refine ⟨-m, ?_⟩
  push_cast
  linear_combination (-(2 * (Real.pi : ℂ) * Complex.I)) * hm

/-- `s ∉ ℤ` and `2s ∈ ℤ` make the middle block eigenvalue equal to `-1`. -/
theorem linear_eigenvalue_eq_neg_one_of_half_integer {s : ℂ}
    (hs : ∀ m : ℤ, s ≠ (m : ℂ)) (h2s : ∃ m : ℤ, 2 * s = (m : ℂ)) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-s)) = -1 := by
  simpa [HurwitzOrbit.monoScalar, mul_assoc] using HurwitzOrbit.monoScalar_eq_neg_one hs h2s

/-- **Half-integer N=2 block split.**  In the order-two branch (`s ∉ ℤ`, `2s ∈ ℤ`), the full relation
splits into the vanishing of the sign-changing block `Ψ` and the invariant residual relation `Φ + Θ = 0`.
This is the exact replacement for `N2Main.n2_blocks_vanish` at the degenerate monodromy scalar. -/
theorem n2_blocks_order_two_split (s : ℂ) (n : ℕ) (hs : ∀ k : ℤ, s ≠ (k : ℂ))
    (h2s : ∃ k : ℤ, 2 * s = (k : ℂ))
    (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ)
    (R : Fin 3 → ℂ → ℂ) (hRper : ∀ k z, R k (z + 2 * (Real.pi : ℂ) * Complex.I) = R k z)
    {B : ℝ} {z0 : ℂ} (h0re : z0.re < B) (h0im1 : -Real.pi < z0.im) (h0im2 : z0.im < Real.pi)
    (hanalytic : AnalyticOnNhd ℂ
      (fun z => HurwitzN2Main.PhiB s n q z + HurwitzN2Main.PsiB s n q l R z
        + HurwitzN2Main.ThetaB s n q l cc R z) {z : ℂ | z.re < B})
    (hrel_split : ∀ z : ℂ, z.re < B → -Real.pi < z.im → z.im < Real.pi →
      HurwitzN2Main.PhiB s n q z + HurwitzN2Main.PsiB s n q l R z
        + HurwitzN2Main.ThetaB s n q l cc R z = 0) :
    (∀ z : ℂ, z.re < B → HurwitzN2Main.PsiB s n q l R z = 0)
      ∧ (∀ z : ℂ, z.re < B →
        HurwitzN2Main.PhiB s n q z + HurwitzN2Main.ThetaB s n q l cc R z = 0) := by
  have hg0 : ∀ z : ℂ, z.re < B →
      HurwitzN2Main.PhiB s n q z + HurwitzN2Main.PsiB s n q l R z
        + HurwitzN2Main.ThetaB s n q l cc R z = 0 :=
    fun z hz => split_extend hanalytic hrel_split h0re h0im1 h0im2 hz
  have hΦ : ∀ z ∈ {z : ℂ | z.re < B},
      HurwitzN2Main.PhiB s n q (z + 2 * (Real.pi : ℂ) * Complex.I)
        = HurwitzN2Main.PhiB s n q z := by
    intro z hz
    have h := phi_block_eigen (s := s)
      (A := fun w z => (HurwitzN2Descent.Aq q w).eval (-(n : ℂ) + Complex.exp z))
      (fun w z => coeff_periodic (HurwitzN2Descent.Aq q w) n z) z
    have hlam : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (2 * s))) = 1 := by
      convert quadratic_eigenvalue_eq_one_of_two_mul_int h2s using 2
      ring
    have hlam' : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-(2 * s))) = 1 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (-(2 * s))
          = -(2 * (Real.pi : ℂ) * Complex.I * (2 * s)) by ring, hlam]
    rw [hlam', one_mul] at h
    simpa [HurwitzN2Main.PhiB] using h
  have hΨ : ∀ z ∈ {z : ℂ | z.re < B},
      HurwitzN2Main.PsiB s n q l R (z + 2 * (Real.pi : ℂ) * Complex.I)
        = -HurwitzN2Main.PsiB s n q l R z := by
    intro z hz
    have h := psi_block_eigen (s := s)
      (q := fun i j z => (q i j).eval (-(n : ℂ) + Complex.exp z))
      (l := fun k z => (l k).eval (-(n : ℂ) + Complex.exp z)) (R := R)
      (fun i j z => coeff_periodic (q i j) n z) (fun k z => coeff_periodic (l k) n z)
      hRper z
    have hlam : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * s)) = -1 := by
      convert linear_eigenvalue_eq_neg_one_of_half_integer hs h2s using 2
      ring
    have hlam' : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-s)) = -1 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (-s)
          = -(2 * (Real.pi : ℂ) * Complex.I * s) by ring, hlam]
    rw [hlam'] at h
    simpa [HurwitzN2Main.PsiB] using h
  have hΘ : ∀ z ∈ {z : ℂ | z.re < B},
      HurwitzN2Main.ThetaB s n q l cc R (z + 2 * (Real.pi : ℂ) * Complex.I)
        = HurwitzN2Main.ThetaB s n q l cc R z := fun z _ =>
    theta_block_eigen (q := fun i j z => (q i j).eval (-(n : ℂ) + Complex.exp z))
      (l := fun k z => (l k).eval (-(n : ℂ) + Complex.exp z))
      (cc := fun z => cc.eval (-(n : ℂ) + Complex.exp z)) (R := R)
      (fun i j z => coeff_periodic (q i j) n z) (fun k z => coeff_periodic (l k) n z)
      (fun z => coeff_periodic cc n z) hRper z
  have hsep := shift_eigenspace_separation_order_two
    (fun z (hz : z.re < B) => halfplane_invariant (B := B) (z := z) hz)
    hΦ hΨ hΘ (fun z hz => hg0 z hz)
  exact ⟨fun z hz => (hsep z hz).1, fun z hz => (hsep z hz).2⟩

end HurwitzN2HalfInteger

namespace HurwitzN2HalfInteger

/-- Laurent-top extraction with a regular tail: if the filtered polynomial block plus
`T(x) x^(r+W)` vanishes near `0`, with `r > 0` and `T` continuous at `0`, then the top coefficient
still vanishes. -/
theorem quadratic_filtration_top_with_tail {W r : ℕ} {A : Fin (W + 1) → ℂ → ℂ} {T : ℂ → ℂ}
    {l : Filter ℂ} [l.NeBot] (hr : 0 < r)
    (hid : Filter.Tendsto (fun x : ℂ => x) l (nhds 0))
    (hA : ∀ w : Fin (W + 1), Filter.Tendsto (A w) l (nhds (A w 0)))
    (hT : Filter.Tendsto T l (nhds (T 0)))
    (h : ∀ᶠ x in l, (∑ w : Fin (W + 1), A w x * x ^ (W - (w : ℕ))) + T x * x ^ (r + W) = 0) :
    A (Fin.last W) 0 = 0 := by
  let pure : ℂ → ℂ := fun x => ∑ w : Fin (W + 1), A w x * x ^ (W - (w : ℕ))
  have hpure_top : Filter.Tendsto pure l (nhds (A (Fin.last W) 0)) := by
    have hterm : ∀ w : Fin (W + 1),
        Filter.Tendsto (fun x => A w x * x ^ (W - (w : ℕ))) l
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
    simpa [pure] using hsum
  have htail_zero : Filter.Tendsto (fun x : ℂ => T x * x ^ (r + W)) l (nhds 0) := by
    have hpow := hid.pow (r + W)
    have hnonzero : r + W ≠ 0 := by omega
    rw [zero_pow hnonzero] at hpow
    simpa [mul_zero] using hT.mul hpow
  have hpure_zero : Filter.Tendsto pure l (nhds 0) := by
    have htail_neg : Filter.Tendsto (fun x : ℂ => -(T x * x ^ (r + W))) l (nhds 0) := by
      simpa using htail_zero.neg
    refine htail_neg.congr' ?_
    filter_upwards [h] with x hx
    dsimp [pure]
    exact neg_eq_of_add_eq_zero_right (by rw [add_comm]; exact hx)
  exact tendsto_nhds_unique hpure_top hpure_zero

/-- Local copy of the polynomial-shift continuity helper used by the tail-aware descent. -/
private theorem evalShift_tendsto_local {l : Filter ℂ}
    (hid : Filter.Tendsto (fun x : ℂ => x) l (nhds 0)) (p : Polynomial ℂ) (n : ℕ) :
    Filter.Tendsto (fun x => p.eval (-(n : ℂ) + x)) l (nhds (p.eval (-(n : ℂ)))) := by
  have hin : Filter.Tendsto (fun x : ℂ => -(n : ℂ) + x) l (nhds (-(n : ℂ))) := by
    simpa using (tendsto_const_nhds (x := -(n : ℂ)) (f := l)).add hid
  exact (p.continuous.tendsto _).comp hin

/-- Downward Laurent filtration with a regular tail.  The tail carries a strictly positive extra power
`x^r`, so it never contributes to any of the Laurent coefficients peeled from the polynomial block. -/
theorem quad_coeffs_vanish_with_tail {l : Filter ℂ} [l.NeBot]
    (hid : Filter.Tendsto (fun x : ℂ => x) l (nhds 0)) (hne : ∀ᶠ x in l, x ≠ 0) :
    ∀ (W r : ℕ), 0 < r → ∀ (A : ℕ → Polynomial ℂ) (T : ℕ → ℂ → ℂ) (N : ℕ),
      (∀ n, Filter.Tendsto (T n) l (nhds (T n 0))) →
      (∀ n, N ≤ n → ∀ᶠ x in l,
        (∑ w ∈ Finset.range (W + 1), (A w).eval (-(n : ℂ) + x) * x ^ (W - w))
          + T n x * x ^ (r + W) = 0) →
      ∀ w, w ≤ W → A w = 0 := by
  intro W
  induction W with
  | zero =>
      intro r hr A T N hT hrel w hw
      obtain rfl : w = 0 := Nat.le_zero.mp hw
      apply HurwitzDescent.eq_zero_of_eventually_neg_nat_roots (N := N)
      intro n hn
      have hA : ∀ k : Fin (0 + 1),
          Filter.Tendsto (fun x => (A (k : ℕ)).eval (-(n : ℂ) + x)) l
            (nhds ((fun x => (A (k : ℕ)).eval (-(n : ℂ) + x)) 0)) := by
        intro k
        simp only [add_zero]
        exact evalShift_tendsto_local hid (A k) n
      have htop := quadratic_filtration_top_with_tail (W := 0) (r := r)
        (A := fun k => fun x => (A (k : ℕ)).eval (-(n : ℂ) + x)) (T := T n)
        hr hid hA (hT n) ?_
      · simpa [Polynomial.IsRoot, Fin.val_last] using htop
      · filter_upwards [hrel n hn] with x hx
        simpa using hx
  | succ W ih =>
      intro r hr A T N hT hrel w hw
      have htop : A (W + 1) = 0 := by
        apply HurwitzDescent.eq_zero_of_eventually_neg_nat_roots (N := N)
        intro n hn
        have hA : ∀ k : Fin (W + 2),
            Filter.Tendsto (fun x => (A (k : ℕ)).eval (-(n : ℂ) + x)) l
              (nhds ((fun x => (A (k : ℕ)).eval (-(n : ℂ) + x)) 0)) := by
          intro k
          simp only [add_zero]
          exact evalShift_tendsto_local hid (A k) n
        have hfin : ∀ᶠ x in l,
            (∑ k : Fin (W + 2), (fun x => (A (k : ℕ)).eval (-(n : ℂ) + x)) x
                * x ^ (W + 1 - (k : ℕ))) + T n x * x ^ (r + (W + 1)) = 0 := by
          refine (hrel n hn).mono fun x hx => ?_
          rw [Fin.sum_univ_eq_sum_range
            (fun k => (A k).eval (-(n : ℂ) + x) * x ^ (W + 1 - k)) (W + 2)]
          exact hx
        have hq := quadratic_filtration_top_with_tail (W := W + 1) (r := r)
          (A := fun k => fun x => (A (k : ℕ)).eval (-(n : ℂ) + x)) (T := T n)
          hr hid hA (hT n) hfin
        simpa [Polynomial.IsRoot, Fin.val_last] using hq
      have hreduced : ∀ n, N ≤ n → ∀ᶠ x in l,
          (∑ k ∈ Finset.range (W + 1), (A k).eval (-(n : ℂ) + x) * x ^ (W - k))
            + T n x * x ^ (r + W) = 0 := by
        intro n hn
        filter_upwards [hrel n hn, hne] with x hx hx0
        rw [Finset.sum_range_succ, htop] at hx
        simp only [Polynomial.eval_zero, zero_mul, add_zero] at hx
        have hfactor :
            (∑ k ∈ Finset.range (W + 1), (A k).eval (-(n : ℂ) + x) * x ^ (W + 1 - k))
                + T n x * x ^ (r + (W + 1)) =
              x * ((∑ k ∈ Finset.range (W + 1), (A k).eval (-(n : ℂ) + x) * x ^ (W - k))
                + T n x * x ^ (r + W)) := by
          rw [mul_add, Finset.mul_sum]
          congr 1
          · refine Finset.sum_congr rfl (fun k hk => ?_)
            have hkW : k ≤ W := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            rw [show W + 1 - k = (W - k) + 1 from by omega, pow_succ]
            ring
          · rw [show r + (W + 1) = (r + W) + 1 by omega, pow_succ]
            ring
        rw [hfactor] at hx
        exact (mul_eq_zero.mp hx).resolve_left hx0
      rcases Nat.lt_or_ge w (W + 1) with hlt | hge
      · exact ih r hr A T N hT hreduced w (Nat.lt_succ_iff.mp hlt)
      · obtain rfl : w = W + 1 := le_antisymm hw hge
        exact htop

end HurwitzN2HalfInteger

namespace HurwitzN2HalfInteger

/-- The regular `Θ` block written in the local coordinate `x = exp z`. -/
noncomputable def thetaX (s : ℂ) (n : ℕ) (q : Fin 3 → Fin 3 → Polynomial ℂ)
    (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ) (x : ℂ) : ℂ :=
  (∑ i : Fin 3, ∑ j : Fin 3, (q i j).eval (-(n : ℂ) + x)
      * (tailFactored s (i : ℕ) n x * tailFactored s (j : ℕ) n x))
    + (∑ k : Fin 3, (l k).eval (-(n : ℂ) + x) * tailFactored s (k : ℕ) n x)
    + cc.eval (-(n : ℂ) + x)

/-- The regular `Θ` block is continuous at `x = 0`. -/
theorem thetaX_continuousAt {s : ℂ} (hs1 : 1 < s.re) (n : ℕ)
    (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ) :
    ContinuousAt (thetaX s n q l cc) 0 := by
  unfold thetaX
  have htail : ∀ k : Fin 3, ContinuousAt (fun x : ℂ => tailFactored s (k : ℕ) n x) 0 :=
    fun k => ((tailFactored_analytic hs1 (k : ℕ) n).continuousOn).continuousAt
      (IsOpen.mem_nhds (isOpen_lt continuous_norm continuous_const) (by norm_num))
  have hpoly : ∀ p : Polynomial ℂ, ContinuousAt (fun x : ℂ => p.eval (-(n : ℂ) + x)) 0 :=
    fun p => ((Polynomial.continuous p).comp (by fun_prop)).continuousAt
  fun_prop (disch := first | exact htail _ | exact hpoly _)

/-- In the half-integer branch, once the order-two split has reduced the invariant part to
`Φ + Θ = 0`, Laurent dominance separates the integer-pole quadratic block from the regular `Θ` block and
forces every quadratic weight coefficient `A_w` to vanish. -/
theorem quadratic_coeffs_vanish_of_order_two_residual {s : ℂ} (hs1 : 1 < s.re)
    {m : ℕ} (hmpos : 0 < m) (hm : 2 * s = (m : ℂ))
    (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ)
    {N : ℕ} {Bregion : ℕ → ℝ}
    (hres : ∀ n, N ≤ n → ∀ z : ℂ, z.re < Bregion n →
      HurwitzN2Main.PhiB s n q z + HurwitzN2Main.ThetaB s n q l cc
        (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0) :
    ∀ w, w ≤ 4 → HurwitzN2Descent.Aq q w = 0 := by
  haveI : (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ).NeBot := Module.punctured_nhds_neBot ℝ ℂ 0
  have hid : Filter.Tendsto (fun x : ℂ => x) (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds 0) :=
    (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
  have hne : ∀ᶠ x in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx using hx
  refine quad_coeffs_vanish_with_tail hid hne 4 m hmpos (HurwitzN2Descent.Aq q)
    (fun n => thetaX s n q l cc) N ?_ ?_
  · intro n
    exact (thetaX_continuousAt hs1 n q l cc).tendsto.mono_left nhdsWithin_le_nhds
  · intro n hn
    apply HurwitzSpine.rel_x_of_rel_exp (B := Bregion n)
    intro z hz
    have hr := hres n hn z hz
    have hconv :
        (∑ w ∈ Finset.range (4 + 1), (HurwitzN2Descent.Aq q w).eval (-(n : ℂ) + Complex.exp z)
            * Complex.exp z ^ (4 - w)) =
          Complex.exp (((4 : ℂ) + 2 * s) * z) * HurwitzN2Main.PhiB s n q z := by
      rw [HurwitzN2Main.PhiB, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun w hw => ?_)
      have hwW : w ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hw)
      rw [← Complex.exp_nat_mul, Nat.cast_sub hwW, ← mul_assoc,
        mul_comm (Complex.exp (((4 : ℂ) + 2 * s) * z))
          ((HurwitzN2Descent.Aq q w).eval (-(n : ℂ) + Complex.exp z)),
        mul_assoc, ← Complex.exp_add]
      ring_nf
    have htheta : thetaX s n q l cc (Complex.exp z) =
        HurwitzN2Main.ThetaB s n q l cc
          (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z := by
      rfl
    have hpow : Complex.exp z ^ (m + 4) = Complex.exp (((m + 4 : ℕ) : ℂ) * z) := by
      rw [Complex.exp_nat_mul]
    have hmexp : Complex.exp (((m + 4 : ℕ) : ℂ) * z)
        = Complex.exp (((4 : ℂ) + 2 * s) * z) := by
      congr 1
      rw [hm]
      push_cast
      ring
    change
      (∑ w ∈ Finset.range (4 + 1), (HurwitzN2Descent.Aq q w).eval (-(n : ℂ) + Complex.exp z)
          * Complex.exp z ^ (4 - w))
        + thetaX s n q l cc (Complex.exp z) * Complex.exp z ^ (m + 4) = 0
    rw [hconv, htheta, hpow, hmexp]
    linear_combination Complex.exp (((4 : ℂ) + 2 * s) * z) * hr

/-- Triangular coefficient read-off for the half-integer residual branch. -/
theorem n2_quad_coeffs_order_two_residual {s : ℂ} (hs1 : 1 < s.re)
    {m : ℕ} (hmpos : 0 < m) (hm : 2 * s = (m : ℂ))
    (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ)
    {N : ℕ} {Bregion : ℕ → ℝ}
    (hres : ∀ n, N ≤ n → ∀ z : ℂ, z.re < Bregion n →
      HurwitzN2Main.PhiB s n q z + HurwitzN2Main.ThetaB s n q l cc
        (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0) :
    q 0 0 = 0 ∧ q 2 2 = 0 ∧ q 0 2 + q 1 1 + q 2 0 = 0 := by
  have hAq : ∀ w, w ≤ 4 → HurwitzN2Descent.Aq q w = 0 :=
    quadratic_coeffs_vanish_of_order_two_residual hs1 hmpos hm q l cc hres
  obtain ⟨h0, h4, h2⟩ := weight_filter_eval q
  refine ⟨?_, ?_, ?_⟩
  · rw [← h0]; exact hAq 0 (by norm_num)
  · rw [← h4]; exact hAq 4 (by norm_num)
  · rw [← h2]; exact hAq 2 (by norm_num)

end HurwitzN2HalfInteger

namespace HurwitzN2HalfInteger

/-- **Hurwitz N=2 half-integer branch, unconditional with a natural pole-order witness.**  This is the
missing companion to `HurwitzN2Final.hurwitz_n2_unconditional`: instead of assuming `2s ∉ ℤ`, it assumes
`2s = m` for a positive natural number `m`.  The order-two split kills `Ψ`; Laurent dominance of the
integer-pole residual `Φ + Θ` kills the quadratic block; the already-proved survivor and linear descents
then close the relation. -/
theorem hurwitz_n2_half_integer_unconditional_nat {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, (k : ℂ) ≠ s) {m : ℕ} (hmpos : 0 < m) (hm : 2 * s = (m : ℂ))
    (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ) {N : ℕ}
    (hrel : ∀ n, N ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
      (∑ i : Fin 3, ∑ j : Fin 3, (q i j).eval (-(n : ℂ) + Complex.exp z) *
          ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin 3, (l k).eval (-(n : ℂ) + Complex.exp z) *
            (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) :
    q 0 0 = 0 ∧ q 2 2 = 0 ∧ q 1 1 = 0 ∧ q 0 2 + q 2 0 = 0
      ∧ l 2 = 0 ∧ l 0 = 0 ∧ l 1 = 0 ∧ cc = 0 := by
  have hlog : -1 < -Real.log 2 := by have := Real.log_two_lt_d9; linarith
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have h2sInt : ∃ k : ℤ, 2 * s = (k : ℂ) := ⟨m, by simpa using hm⟩
  have hblocks : ∀ n, N ≤ n →
      (∀ z : ℂ, z.re < -Real.log 2 →
          HurwitzN2Main.PsiB s n q l (fun k z => tailFactored s (k:ℕ) n (Complex.exp z)) z = 0)
      ∧ (∀ z : ℂ, z.re < -Real.log 2 →
          HurwitzN2Main.PhiB s n q z + HurwitzN2Main.ThetaB s n q l cc
            (fun k z => tailFactored s (k:ℕ) n (Complex.exp z)) z = 0) := by
    intro n hn
    set R : Fin 3 → ℂ → ℂ := fun k z => tailFactored s (k:ℕ) n (Complex.exp z) with hRdef
    have hRper : ∀ k z, R k (z + 2*(Real.pi:ℂ)*Complex.I) = R k z :=
      fun k z => tailFactored_periodic s (k:ℕ) n z
    have hsplit : ∀ z:ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
        HurwitzN2Main.PhiB s n q z + HurwitzN2Main.PsiB s n q l R z
          + HurwitzN2Main.ThetaB s n q l cc R z = 0 := by
      intro z hz hz1 hz2
      rw [HurwitzN2Main.PhiB_eq_products, HurwitzN2Main.PsiB, HurwitzN2Main.ThetaB]
      have hcoll := relation_collect (s:=s) (fun i j => (q i j).eval (-(n:ℂ)+Complex.exp z))
        (fun k => (l k).eval (-(n:ℂ)+Complex.exp z)) (cc.eval (-(n:ℂ)+Complex.exp z)) z (fun k => R k z)
      have hr := hrel n hn z hz hz1 hz2
      linear_combination hr - hcoll
    exact n2_blocks_order_two_split s n (fun k => (hsZ k).symm) h2sInt q l cc R hRper
      (z0 := -1) (B := -Real.log 2)
      (by simpa using hlog) (by simpa using hpi) (by simpa using hpi)
      (HurwitzN2BlockAnalytic.blockSum_analytic hs1 n q l cc) hsplit
  have hAqfun : ∀ w, w ≤ 4 → HurwitzN2Descent.Aq q w = 0 :=
    quadratic_coeffs_vanish_of_order_two_residual hs1 hmpos hm q l cc
      (fun n hn z hz => (hblocks n hn).2 z hz)
  obtain ⟨hq00, hq22, hsurv⟩ :=
    n2_quad_coeffs_order_two_residual hs1 hmpos hm q l cc
      (fun n hn z hz => (hblocks n hn).2 z hz)
  have hA1 : q 0 1 + q 1 0 = 0 := by rw [← HurwitzN2Final.Aq_one]; exact hAqfun 1 (by norm_num)
  have hA3 : q 1 2 + q 2 1 = 0 := by rw [← HurwitzN2Final.Aq_three]; exact hAqfun 3 (by norm_num)
  have hrow : ∀ᶠ n : ℕ in Filter.atTop,
      (q 0 2 + q 2 0).eval (-(n:ℂ)) * HurwitzZetaShift.hzeta s (-(n:ℂ)) + (l 2).eval (-(n:ℂ)) = 0 := by
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    exact HurwitzN2Final.row_extract hs1 n q l hq22 hA3 (hblocks n hn).1
  obtain ⟨hQ, hl2⟩ := HurwitzN2DensityShadow.survivor_killed hs1 (fun k => (hsZ k).symm) hrow
  have hq11 : q 1 1 = 0 := by linear_combination hsurv - hQ
  have hlin : ∀ k, k ≤ 2 →
      (fun m : ℕ => if m = 0 then l 0 else if m = 1 then l 1 else l 2) k = 0 := by
    apply HurwitzN2Descent.lin_descent (s:=s)
      (fun m : ℕ => if m = 0 then l 0 else if m = 1 then l 1 else l 2) (N:=N)
      (Bregion := fun _ => -Real.log 2)
    intro n hn z hz
    have hPsi0 := (hblocks n hn).1 z hz
    rw [HurwitzN2Final.psiB_pure n q l hq00 hq22 hq11 hA1 hA3 hQ z] at hPsi0
    rw [← hPsi0, ← Fin.sum_univ_eq_sum_range
      (fun m : ℕ => (if m = 0 then l 0 else if m = 1 then l 1 else l 2).eval (-(n:ℂ)+Complex.exp z)
        * Complex.exp (-(s+(m:ℂ))*z)) 3]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hidx : (if (i : ℕ) = 0 then l 0 else if (i : ℕ) = 1 then l 1 else l 2) = l i := by
      fin_cases i <;> rfl
    rw [hidx]
  have hl0 : l 0 = 0 := by have := hlin 0 (by norm_num); simpa using this
  have hl1 : l 1 = 0 := by have := hlin 1 (by norm_num); simpa using this
  have hcc : cc = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem
      (f := fun m : ℕ => -((N:ℂ)) + (1:ℂ) / ((m + 3 : ℕ) : ℂ))
    · intro a b hab
      simp only [add_right_inj] at hab
      rw [one_div, one_div, inv_inj] at hab
      have := Nat.cast_injective (R := ℂ) hab
      omega
    · intro m0
      have hx : ((m0 + 3 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hxr : ((m0 + 3 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hez : Complex.exp (Complex.log ((1:ℂ) / ((m0 + 3 : ℕ) : ℂ)))
          = (1:ℂ) / ((m0 + 3 : ℕ) : ℂ) := Complex.exp_log (div_ne_zero one_ne_zero hx)
      have hzre : (Complex.log ((1:ℂ) / ((m0 + 3 : ℕ) : ℂ))).re < -Real.log 2 := by
        rw [Complex.log_re, norm_div, norm_one, Complex.norm_natCast]
        rw [Real.log_div one_ne_zero hxr, Real.log_one, zero_sub]
        have h2 : Real.log 2 < Real.log ((m0 + 3 : ℕ) : ℝ) :=
          Real.log_lt_log (by norm_num) (by exact_mod_cast (show 2 < m0 + 3 by omega))
        linarith
      have hθ := (hblocks N le_rfl).2 _ hzre
      have hPhi0 : HurwitzN2Main.PhiB s N q (Complex.log ((1:ℂ) / ((m0 + 3 : ℕ) : ℂ))) = 0 := by
        rw [HurwitzN2Main.PhiB]
        apply Finset.sum_eq_zero
        intro w hw
        have hwle : w ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hw)
        rw [hAqfun w hwle, Polynomial.eval_zero, zero_mul]
      rw [hPhi0, zero_add, HurwitzN2Final.thetaB_const N q l cc hq00 hq22 hq11 hA1 hA3 hQ hl0 hl1 hl2,
        hez] at hθ
      simpa [Set.mem_setOf_eq, Polynomial.IsRoot] using hθ
  exact ⟨hq00, hq22, hq11, hQ, hl2, hl0, hl1, hcc⟩

end HurwitzN2HalfInteger

namespace HurwitzN2HalfInteger

/-- If `Re(s)>1` and `2s` is an integer, then that integer is represented by a positive natural number. -/
theorem exists_pos_nat_two_mul_eq_int {s : ℂ} (hs1 : 1 < s.re)
    (h2s : ∃ k : ℤ, 2 * s = (k : ℂ)) : ∃ m : ℕ, 0 < m ∧ 2 * s = (m : ℂ) := by
  obtain ⟨k, hk⟩ := h2s
  have hre := congrArg Complex.re hk
  simp at hre
  have hkgtR : (0 : ℝ) < k := by nlinarith [hs1, hre]
  have hkgt0 : (0 : ℤ) < k := by exact_mod_cast hkgtR
  refine ⟨k.toNat, ?_, ?_⟩
  · have hktoZ : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (le_of_lt hkgt0)
    have hposZ : (0 : ℤ) < (k.toNat : ℤ) := by rwa [hktoZ]
    exact_mod_cast hposZ
  · have hktoZ : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (le_of_lt hkgt0)
    have hkcastC : ((k.toNat : ℕ) : ℂ) = (k : ℂ) := by exact_mod_cast hktoZ
    rw [hkcastC]
    exact hk

/-- **Hurwitz N=2 half-integer branch, unconditional.**  This discharges the branch excluded from the
previous generic theorem: `s ∉ ℤ`, `2s ∈ ℤ`, `Re(s)>1`. -/
theorem hurwitz_n2_half_integer_unconditional {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, (k : ℂ) ≠ s) (h2s : ∃ k : ℤ, 2 * s = (k : ℂ))
    (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ) {N : ℕ}
    (hrel : ∀ n, N ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
      (∑ i : Fin 3, ∑ j : Fin 3, (q i j).eval (-(n : ℂ) + Complex.exp z) *
          ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin 3, (l k).eval (-(n : ℂ) + Complex.exp z) *
            (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) :
    q 0 0 = 0 ∧ q 2 2 = 0 ∧ q 1 1 = 0 ∧ q 0 2 + q 2 0 = 0
      ∧ l 2 = 0 ∧ l 0 = 0 ∧ l 1 = 0 ∧ cc = 0 := by
  obtain ⟨m, hmpos, hm⟩ := exists_pos_nat_two_mul_eq_int hs1 h2s
  exact hurwitz_n2_half_integer_unconditional_nat hs1 hsZ hmpos hm q l cc hrel

end HurwitzN2HalfInteger

namespace HurwitzN2HalfInteger

/-- **Hurwitz N=2 density-shadow theorem with no `2s ∉ ℤ` hypothesis.**  This combines the old generic
branch (`2s ∉ ℤ`) with the half-integer branch proved in this file. -/
theorem hurwitz_n2_unconditional_all_noninteger {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, (k : ℂ) ≠ s)
    (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ) {N : ℕ}
    (hrel : ∀ n, N ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
      (∑ i : Fin 3, ∑ j : Fin 3, (q i j).eval (-(n : ℂ) + Complex.exp z) *
          ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin 3, (l k).eval (-(n : ℂ) + Complex.exp z) *
            (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) :
    q 0 0 = 0 ∧ q 2 2 = 0 ∧ q 1 1 = 0 ∧ q 0 2 + q 2 0 = 0
      ∧ l 2 = 0 ∧ l 0 = 0 ∧ l 1 = 0 ∧ cc = 0 := by
  by_cases h2s : ∃ k : ℤ, 2 * s = (k : ℂ)
  · exact hurwitz_n2_half_integer_unconditional hs1 hsZ h2s q l cc hrel
  · exact HurwitzN2Final.hurwitz_n2_unconditional hs1 hsZ
      (fun k hk => h2s ⟨k, hk.symm⟩) q l cc hrel

end HurwitzN2HalfInteger
