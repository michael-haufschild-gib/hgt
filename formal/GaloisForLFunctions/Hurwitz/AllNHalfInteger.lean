/-
# Hurwitz all-N — the half-integer quadratic block

The generic all-`N` quadratic block theorem assumes `2s ∉ ℤ` so the three
monodromy eigenspaces split.  This file proves the formerly excluded order-two branch:
when `s ∉ ℤ` but `2s ∈ ℤ`, the middle block is odd under the period shift while
the quadratic and regular blocks are invariant.  The invariant residual
`Φ_N + Θ_N = 0` is then separated by the same tail-aware Laurent descent used in
the `N = 2` proof.
-/
import GaloisForLFunctions.Hurwitz.AllNQuadFilt
import GaloisForLFunctions.Hurwitz.N2HalfInteger

open Complex Filter Topology HurwitzEncoding HurwitzSpine HurwitzN2Tail
open HurwitzAllNQuadFilt

namespace HurwitzAllNHalfInteger

variable {N : ℕ}

/-- **All-`N` half-integer block split.**  In the order-two branch
(`s ∉ ℤ`, `2s ∈ ℤ`), the sign-changing block `Ψ_N` vanishes and the invariant
residual satisfies `Φ_N + Θ_N = 0`. -/
theorem allN_blocks_order_two_split (s : ℂ) (n : ℕ) (hs : ∀ k : ℤ, s ≠ (k : ℂ))
    (h2s : ∃ k : ℤ, 2 * s = (k : ℂ))
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ)
    (R : Fin (N + 1) → ℂ → ℂ)
    (hRper : ∀ k z, R k (z + 2 * (Real.pi : ℂ) * Complex.I) = R k z)
    {B : ℝ} {z0 : ℂ} (h0re : z0.re < B) (h0im1 : -Real.pi < z0.im)
    (h0im2 : z0.im < Real.pi)
    (hanalytic : AnalyticOnNhd ℂ
      (fun z => PhiN s n q z + PsiN s n q l R z + ThetaN s n q l cc R z)
      {z : ℂ | z.re < B})
    (hrel_split : ∀ z : ℂ, z.re < B → -Real.pi < z.im → z.im < Real.pi →
      PhiN s n q z + PsiN s n q l R z + ThetaN s n q l cc R z = 0) :
    (∀ z : ℂ, z.re < B → PsiN s n q l R z = 0)
      ∧ (∀ z : ℂ, z.re < B → PhiN s n q z + ThetaN s n q l cc R z = 0) := by
  have hg0 : ∀ z : ℂ, z.re < B →
      PhiN s n q z + PsiN s n q l R z + ThetaN s n q l cc R z = 0 :=
    fun z hz => split_extend hanalytic hrel_split h0re h0im1 h0im2 hz
  have hΦ : ∀ z ∈ {z : ℂ | z.re < B},
      PhiN s n q (z + 2 * (Real.pi : ℂ) * Complex.I) = PhiN s n q z := by
    intro z hz
    have h := phiN_block_eigen (N := N) (s := s)
      (Q := fun i j z => (q i j).eval (-(n : ℂ) + Complex.exp z))
      (fun i j z => coeff_periodic (q i j) n z) z
    rw [HurwitzN2HalfInteger.quadratic_eigenvalue_eq_one_of_two_mul_int h2s, one_mul] at h
    simpa [PhiN] using h
  have hΨ : ∀ z ∈ {z : ℂ | z.re < B},
      PsiN s n q l R (z + 2 * (Real.pi : ℂ) * Complex.I) = -PsiN s n q l R z := by
    intro z hz
    have h := psiN_block_eigen (N := N) (s := s)
      (q := fun i j z => (q i j).eval (-(n : ℂ) + Complex.exp z))
      (l := fun k z => (l k).eval (-(n : ℂ) + Complex.exp z)) (R := R)
      (fun i j z => coeff_periodic (q i j) n z) (fun k z => coeff_periodic (l k) n z)
      hRper z
    rw [HurwitzN2HalfInteger.linear_eigenvalue_eq_neg_one_of_half_integer hs h2s] at h
    simpa [PsiN] using h
  have hΘ : ∀ z ∈ {z : ℂ | z.re < B},
      ThetaN s n q l cc R (z + 2 * (Real.pi : ℂ) * Complex.I)
        = ThetaN s n q l cc R z := fun z _ =>
    thetaN_block_eigen (N := N)
      (q := fun i j z => (q i j).eval (-(n : ℂ) + Complex.exp z))
      (l := fun k z => (l k).eval (-(n : ℂ) + Complex.exp z))
      (cc := fun z => cc.eval (-(n : ℂ) + Complex.exp z)) (R := R)
      (fun i j z => coeff_periodic (q i j) n z) (fun k z => coeff_periodic (l k) n z)
      (fun z => coeff_periodic cc n z) hRper z
  have hsep := HurwitzN2HalfInteger.shift_eigenspace_separation_order_two
    (fun z (hz : z.re < B) => halfplane_invariant (B := B) (z := z) hz)
    hΦ hΨ hΘ (fun z hz => hg0 z hz)
  exact ⟨fun z hz => (hsep z hz).1, fun z hz => (hsep z hz).2⟩

/-- The regular all-`N` `Θ` block in the local coordinate `x = exp z`. -/
noncomputable def thetaNX (s : ℂ) (n : ℕ)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ) (x : ℂ) : ℂ :=
  (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + x)
      * (tailFactored s (i : ℕ) n x * tailFactored s (j : ℕ) n x))
    + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + x) * tailFactored s (k : ℕ) n x)
    + cc.eval (-(n : ℂ) + x)

/-- The local regular block is continuous at `x = 0`. -/
theorem thetaNX_continuousAt {s : ℂ} (hs1 : 1 < s.re) (n : ℕ)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ) :
    ContinuousAt (thetaNX (N := N) s n q l cc) 0 := by
  unfold thetaNX
  have htail : ∀ k : Fin (N + 1),
      ContinuousAt (fun x : ℂ => tailFactored s (k : ℕ) n x) 0 :=
    fun k => ((tailFactored_analytic hs1 (k : ℕ) n).continuousOn).continuousAt
      (IsOpen.mem_nhds (isOpen_lt continuous_norm continuous_const) (by norm_num))
  have hpoly : ∀ p : Polynomial ℂ,
      ContinuousAt (fun x : ℂ => p.eval (-(n : ℂ) + x)) 0 :=
    fun p => ((Polynomial.continuous p).comp (by fun_prop)).continuousAt
  fun_prop (disch := first | exact htail _ | exact hpoly _)

/-- In the half-integer branch, Laurent dominance separates the invariant
residual `Φ_N + Θ_N = 0` and forces every all-`N` quadratic weight coefficient
to vanish. -/
theorem allN_quadratic_coeffs_vanish_of_order_two_residual {s : ℂ} (hs1 : 1 < s.re)
    {m : ℕ} (hmpos : 0 < m) (hm : 2 * s = (m : ℂ))
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ)
    {M : ℕ} {Bregion : ℕ → ℝ}
    (hres : ∀ n, M ≤ n → ∀ z : ℂ, z.re < Bregion n →
      PhiN s n q z + ThetaN s n q l cc
        (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0) :
    ∀ w, w ≤ 2 * N → AqN q w = 0 := by
  haveI : (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ).NeBot := Module.punctured_nhds_neBot ℝ ℂ 0
  have hid : Filter.Tendsto (fun x : ℂ => x) (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds 0) :=
    (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
  have hne : ∀ᶠ x in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx using hx
  refine HurwitzN2HalfInteger.quad_coeffs_vanish_with_tail hid hne (2 * N) m hmpos
    (AqN q) (fun n => thetaNX (N := N) s n q l cc) M ?_ ?_
  · intro n
    exact (thetaNX_continuousAt (N := N) hs1 n q l cc).tendsto.mono_left nhdsWithin_le_nhds
  · intro n hn
    apply HurwitzSpine.rel_x_of_rel_exp (B := Bregion n)
    intro z hz
    have hr := hres n hn z hz
    have hphi_weight :
        PhiN s n q z =
          ∑ w ∈ Finset.range (2 * N + 1), (AqN q w).eval (-(n : ℂ) + Complex.exp z)
            * Complex.exp (-(2 * s + (w : ℂ)) * z) := by
      unfold PhiN
      have hev : ∀ w, (AqN q w).eval (-(n : ℂ) + Complex.exp z)
          = ∑ ij ∈ Finset.univ.filter
              (fun ij : Fin (N + 1) × Fin (N + 1) =>
                (ij.1 : ℕ) + (ij.2 : ℕ) = w),
            (q ij.1 ij.2).eval (-(n : ℂ) + Complex.exp z) := by
        intro w
        rw [AqN, Polynomial.eval_finsetSum]
      rw [phiN_regroup (N := N) s (fun i j => (q i j).eval (-(n : ℂ) + Complex.exp z)) z]
      simp_rw [hev]
    have hconv :
        (∑ w ∈ Finset.range (2 * N + 1), (AqN q w).eval (-(n : ℂ) + Complex.exp z)
            * Complex.exp z ^ (2 * N - w))
          = Complex.exp ((((2 * N : ℕ) : ℂ) + 2 * s) * z) * PhiN s n q z := by
      rw [hphi_weight, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun w hw => ?_)
      have hwW : w ≤ 2 * N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hw)
      rw [← Complex.exp_nat_mul, Nat.cast_sub hwW, ← mul_assoc,
        mul_comm (Complex.exp ((((2 * N : ℕ) : ℂ) + 2 * s) * z))
          ((AqN q w).eval (-(n : ℂ) + Complex.exp z)),
        mul_assoc, ← Complex.exp_add]
      ring_nf
    have htheta : thetaNX (N := N) s n q l cc (Complex.exp z) =
        ThetaN s n q l cc (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z := by
      rfl
    have hpow : Complex.exp z ^ (m + 2 * N)
        = Complex.exp (((m + 2 * N : ℕ) : ℂ) * z) := by
      rw [Complex.exp_nat_mul]
    have hmexp : Complex.exp (((m + 2 * N : ℕ) : ℂ) * z)
        = Complex.exp ((((2 * N : ℕ) : ℂ) + 2 * s) * z) := by
      congr 1
      rw [hm]
      push_cast
      ring
    change
      (∑ w ∈ Finset.range (2 * N + 1), (AqN q w).eval (-(n : ℂ) + Complex.exp z)
          * Complex.exp z ^ (2 * N - w))
        + thetaNX (N := N) s n q l cc (Complex.exp z) * Complex.exp z ^ (m + 2 * N) = 0
    rw [hconv, htheta, hpow, hmexp]
    linear_combination Complex.exp ((((2 * N : ℕ) : ℂ) + 2 * s) * z) * hr

/-- All-`N` quadratic-block vanishing in the half-integer branch, with the pole
order represented by a positive natural number. -/
theorem allN_quad_vanish_half_integer_nat {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, (k : ℂ) ≠ s) {m : ℕ} (hmpos : 0 < m) (hm : 2 * s = (m : ℂ))
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ) {M : ℕ}
    (hrel : ∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im →
      z.im < Real.pi →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) :
    ∀ w, w ≤ 2 * N → AqN q w = 0 := by
  have hlog : -1 < -Real.log 2 := by have := Real.log_two_lt_d9; linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2sInt : ∃ k : ℤ, 2 * s = (k : ℂ) := ⟨m, by simpa using hm⟩
  have hblocks : ∀ n, M ≤ n →
      (∀ z : ℂ, z.re < -Real.log 2 →
          PsiN s n q l (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0)
        ∧ (∀ z : ℂ, z.re < -Real.log 2 →
          PhiN s n q z + ThetaN s n q l cc
            (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0) := by
    intro n hn
    set R : Fin (N + 1) → ℂ → ℂ := fun k z => tailFactored s (k : ℕ) n (Complex.exp z) with hRdef
    have hRper : ∀ k z, R k (z + 2 * (Real.pi : ℂ) * Complex.I) = R k z :=
      fun k z => tailFactored_periodic s (k : ℕ) n z
    have hsplit : ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
        PhiN s n q z + PsiN s n q l R z + ThetaN s n q l cc R z = 0 := by
      intro z hz hz1 hz2
      rw [PhiN, PsiN, ThetaN]
      have hcoll := relation_collectN (s := s) (N := N)
        (fun i j => (q i j).eval (-(n : ℂ) + Complex.exp z))
        (fun k => (l k).eval (-(n : ℂ) + Complex.exp z)) (cc.eval (-(n : ℂ) + Complex.exp z))
        z (fun k => R k z)
      have hr := hrel n hn z hz hz1 hz2
      linear_combination hr - hcoll
    exact allN_blocks_order_two_split (N := N) s n (fun k => (hsZ k).symm) h2sInt q l cc R hRper
      (z0 := -1) (B := -Real.log 2)
      (by simpa using hlog) (by simpa using hpi) (by simpa using hpi)
      (allN_blockSum_analytic (N := N) hs1 n q l cc) hsplit
  exact allN_quadratic_coeffs_vanish_of_order_two_residual (N := N) hs1 hmpos hm q l cc
    (fun n hn z hz => (hblocks n hn).2 z hz)

/-- All-`N` quadratic-block vanishing in the half-integer branch. -/
theorem allN_quad_vanish_half_integer {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, (k : ℂ) ≠ s) (h2s : ∃ k : ℤ, 2 * s = (k : ℂ))
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ) {M : ℕ}
    (hrel : ∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im →
      z.im < Real.pi →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) :
    ∀ w, w ≤ 2 * N → AqN q w = 0 := by
  obtain ⟨m, hmpos, hm⟩ := HurwitzN2HalfInteger.exists_pos_nat_two_mul_eq_int hs1 h2s
  exact allN_quad_vanish_half_integer_nat (N := N) hs1 hsZ hmpos hm q l cc hrel

/-- **All-`N` quadratic-block theorem with no `2s ∉ ℤ` side condition.** -/
theorem allN_quad_vanish_genuine_all_noninteger {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, (k : ℂ) ≠ s)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ) {M : ℕ}
    (hrel : ∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im →
      z.im < Real.pi →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) :
    ∀ w, w ≤ 2 * N → AqN q w = 0 := by
  by_cases h2s : ∃ k : ℤ, 2 * s = (k : ℂ)
  · exact allN_quad_vanish_half_integer (N := N) hs1 hsZ h2s q l cc hrel
  · exact allN_quad_vanish_genuine (N := N) (s := s) (M := M) hs1 hsZ
      (fun k hk => h2s ⟨k, hk.symm⟩) q l cc hrel

end HurwitzAllNHalfInteger
