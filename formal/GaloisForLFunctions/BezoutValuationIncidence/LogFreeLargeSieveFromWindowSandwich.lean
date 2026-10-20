import GaloisForLFunctions.BezoutValuationIncidence.TrapezoidWindowSandwichAtQuadraticOrder
import GaloisForLFunctions.RHTower.Sieve.SieveBoundSharp

/-!
# A log-free large sieve with unit main coefficient from the window sandwich

The window sandwich bounds the dual large-sieve sums over the response frequencies, the roots of
unity of order at most `Q`:

`Σ_{A<k≤A+K} |Σ_{ζ ∈ T} a(ζ) ζ^k|² ≤ (K + 2Q² - 1) Σ |a(ζ)|²`.

The duality principle carries the same constant to the primal sums, which are the Farey-point
values of a trigonometric polynomial:

`Σ_{q ≤ Q} Σ_{(a,q) = 1} |Σ_{n < N} x(n) e(a n / q)|² ≤ (N + 2Q² - 1) Σ |x(n)|²`.

The main term has coefficient one and there is no logarithm; the classical Montgomery–Vaughan
constant `N + Q² - 1` is reached up to the factor two on `Q²`. Fed into Montgomery's combinatorial
sieve inequality this gives `|A| Σ_{p ∈ P} (p - ω_p)/ω_p ≤ N + 2Q² - 1` for any `A ⊆ [0, N)`
occupying `ω_p` classes modulo `p`, in place of the constants `N + Q²(1 + log(Q²/2 + 1))` and
`Q² + 4πN` available from the separated-frequency large sieve.
-/

open Finset RHTower.Sieve
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. The duality principle -/

/-- **Duality.** A bound on the dual sums `Σ_k |Σ_ζ a(ζ) ζ^k|²` transfers, with the same constant, to
the primal sums `Σ_ζ |Σ_k x(k) ζ^k|²`. -/
theorem sum_norm_sq_primal_le_of_dual {T : Finset ℂ} {W : Finset ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hdual : ∀ a : ℂ → ℂ, ∑ k ∈ W, ‖∑ ζ ∈ T, a ζ * ζ ^ k‖ ^ 2 ≤ C * ∑ ζ ∈ T, ‖a ζ‖ ^ 2)
    (x : ℕ → ℂ) :
    ∑ ζ ∈ T, ‖∑ k ∈ W, x k * ζ ^ k‖ ^ 2 ≤ C * ∑ k ∈ W, ‖x k‖ ^ 2 := by
  set y : ℂ → ℂ := fun ζ => ∑ k ∈ W, x k * ζ ^ k with hy
  set S := ∑ ζ ∈ T, ‖y ζ‖ ^ 2 with hS
  set a : ℂ → ℂ := fun ζ => conj (y ζ) with ha
  set z : ℕ → ℂ := fun k => ∑ ζ ∈ T, a ζ * ζ ^ k with hz
  set X := ∑ k ∈ W, ‖x k‖ ^ 2 with hX
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hX0 : 0 ≤ X := sum_nonneg fun _ _ => sq_nonneg _
  have haS : ∑ ζ ∈ T, ‖a ζ‖ ^ 2 = S := sum_congr rfl fun ζ _ => by rw [ha, Complex.norm_conj]
  have hZ : ∑ k ∈ W, ‖z k‖ ^ 2 ≤ C * S := haS ▸ hdual a
  -- `S = Σ_k x(k) z(k)`
  have hSz : (S : ℂ) = ∑ k ∈ W, x k * z k := by
    rw [hS, Complex.ofReal_sum]
    have h1 : ∀ ζ ∈ T, ((‖y ζ‖ ^ 2 : ℝ) : ℂ) = ∑ k ∈ W, conj (y ζ) * (x k * ζ ^ k) := by
      intro ζ _
      rw [← mul_sum, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rw [sum_congr rfl h1, sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [hz, mul_sum]
    exact sum_congr rfl fun ζ _ => by rw [ha]; ring
  have hle : S ≤ ∑ k ∈ W, ‖x k‖ * ‖z k‖ := by
    have h := norm_sum_le W fun k => x k * z k
    rw [← hSz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0] at h
    exact h.trans_eq (sum_congr rfl fun k _ => norm_mul _ _)
  have hcs := sum_mul_sq_le_sq_mul_sq W (fun k => ‖x k‖) (fun k => ‖z k‖)
  have hsq : S ^ 2 ≤ X * (C * S) :=
    (pow_le_pow_left₀ hS0 hle 2).trans (hcs.trans (mul_le_mul_of_nonneg_left hZ hX0))
  rcases hS0.lt_or_eq with hpos | hzero
  · nlinarith
  · rw [← hzero]
    exact mul_nonneg hC hX0

/-! ## §2. The primal large sieve over the response frequencies -/

/-- **Log-free large sieve.** For frequencies among the roots of unity of order at most `Q` and any
window of length `K`, `Σ_ζ |Σ_k x(k) ζ^k|² ≤ (K + 2Q² - 1) Σ |x(k)|²`. -/
theorem largeSieve_responseRoots {Q : ℕ} (hQ : 2 ≤ Q) {T : Finset ℂ} (hT : T ⊆ responseRoots Q)
    (A K : ℕ) (x : ℕ → ℂ) :
    ∑ ζ ∈ T, ‖∑ k ∈ Icc (A + 1) (A + K), x k * ζ ^ k‖ ^ 2 ≤
      ((K : ℝ) + 2 * (Q : ℝ) ^ 2 - 1) * ∑ k ∈ Icc (A + 1) (A + K), ‖x k‖ ^ 2 := by
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hC : (0 : ℝ) ≤ (K : ℝ) + 2 * (Q : ℝ) ^ 2 - 1 := by
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  refine sum_norm_sq_primal_le_of_dual hC (fun a => ?_) x
  have h := (abs_le.mp (abs_window_sum_norm_sq_sub_le hQ hT a A K)).2
  linarith

/-! ## §3. Farey points -/

theorem circleFreq_natCast (n : ℕ) : circleFreq (n : ℝ) = 1 := by
  rw [circleFreq]
  convert Complex.exp_int_mul_two_pi_mul_I (n : ℤ) using 2
  push_cast
  ring

/-- **Log-free large sieve at the proper Farey points, for a set of integers.** -/
theorem largeSieve_set_properFarey_logFree (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (A : Finset ℕ)
    (hA : A ⊆ range N) :
    ∑ p ∈ properFareySet Q, ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((p.1 : ℝ) / (p.2 : ℝ)))‖ ^ 2 ≤
      ((N : ℝ) + 2 * (Q : ℝ) ^ 2 - 1) * (A.card : ℝ) := by
  classical
  set f : ℕ × ℕ → ℂ := fun p => circleFreq ((p.1 : ℝ) / (p.2 : ℝ)) with hf
  -- proper Farey points are response frequencies of order at most `Q`
  have hmem : ∀ p ∈ properFareySet Q, f p ∈ responseRoots Q := by
    intro p hp
    obtain ⟨⟨_, _⟩, ⟨hq1, hqQ⟩, _, _⟩ := mem_fareySet.mp (mem_properFareySet.mp hp).1
    refine mem_biUnion.mpr ⟨p.2, mem_Icc.mpr ⟨hq1, hqQ⟩, ?_⟩
    rw [Polynomial.mem_nthRootsFinset (by omega) 1, hf, circleFreq_pow]
    have hq0 : (p.2 : ℝ) ≠ 0 := by exact_mod_cast (show p.2 ≠ 0 by omega)
    rw [mul_div_cancel₀ _ hq0, circleFreq_natCast]
  -- distinct proper Farey points are distinct frequencies
  have hinj : ∀ p ∈ properFareySet Q, ∀ r ∈ properFareySet Q, f p = f r → p = r := by
    intro p hp r hr hpr
    by_contra hne
    have hsep := fareySet_sep p (mem_properFareySet.mp hp).1 r (mem_properFareySet.mp hr).1 hne
    have hchord := four_mul_toIntDist_le_norm_sub ((p.1 : ℝ) / (p.2 : ℝ)) ((r.1 : ℝ) / (r.2 : ℝ))
    have hfp : ‖f p‖ = 1 := norm_circleFreq _
    simp only [hf] at hpr hfp
    rw [← hpr, conj_mul_self_of_norm_eq_one hfp, sub_self, norm_zero] at hchord
    have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
    have : (0 : ℝ) < 1 / (Q : ℝ) ^ (2 : ℕ) := by positivity
    linarith
  -- shift the set into the window `[1, N]`
  set A' := A.map (addRightEmbedding 1) with hA'
  have hA'sub : A' ⊆ Icc (0 + 1) (0 + N) := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := mem_map.mp hk
    have := mem_range.mp (hA hn)
    simp only [addRightEmbedding_apply, mem_Icc]
    omega
  set x : ℕ → ℂ := fun k => if k ∈ A' then 1 else 0 with hx
  have hval : ∀ ζ : ℂ, ‖ζ‖ = 1 →
      ‖∑ n ∈ A, ζ ^ n‖ = ‖∑ k ∈ Icc (0 + 1) (0 + N), x k * ζ ^ k‖ := by
    intro ζ hζ
    have h1 : ∑ k ∈ Icc (0 + 1) (0 + N), x k * ζ ^ k = ζ * ∑ n ∈ A, ζ ^ n := by
      rw [mul_sum]
      simp only [hx, ite_mul, one_mul, zero_mul]
      rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hA'sub, hA', sum_map]
      exact sum_congr rfl fun n _ => by rw [addRightEmbedding_apply, pow_succ, mul_comm]
    rw [h1, norm_mul, hζ, one_mul]
  have hX : ∑ k ∈ Icc (0 + 1) (0 + N), ‖x k‖ ^ 2 = (A.card : ℝ) := by
    simp only [hx, apply_ite (fun z : ℂ => ‖z‖ ^ 2), norm_one, one_pow, norm_zero,
      zero_pow two_ne_zero]
    rw [sum_ite_mem, inter_eq_right.mpr hA'sub, sum_const, nsmul_eq_mul, mul_one, hA', card_map]
  have hls := largeSieve_responseRoots hQ (T := (properFareySet Q).image f)
    (fun ζ hζ => by
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hζ
      exact hmem p hp) 0 N x
  rw [hX, sum_image hinj] at hls
  refine le_of_eq_of_le (sum_congr rfl fun p _ => ?_) hls
  have hfp : ‖f p‖ = 1 := norm_circleFreq _
  rw [← hval (f p) hfp]
  simp only [hf, circleFreq_pow]

/-! ## §4. Montgomery's sieve with the log-free constant -/

/-- **Montgomery's sieve inequality with constant `N + 2Q² - 1`.** -/
theorem montgomery_sieve_logFree (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (A : Finset ℕ)
    (hA : A ⊆ range N) (hAne : A.Nonempty) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q) :
    (A.card : ℝ) * ∑ p ∈ P,
        ((p : ℝ) - ((occupiedClasses p A).card : ℝ)) / ((occupiedClasses p A).card : ℝ) ≤
      (N : ℝ) + 2 * (Q : ℝ) ^ 2 - 1 := by
  classical
  have hlow : ∀ p ∈ P,
      (A.card : ℝ) ^ (2 : ℕ) *
          (((p : ℝ) - ((occupiedClasses p A).card : ℝ)) / ((occupiedClasses p A).card : ℝ)) ≤
        ∑ x ∈ (properFareySet Q).filter (fun x => x.2 = p),
          ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((x.1 : ℝ) / (x.2 : ℝ)))‖ ^ (2 : ℕ) := by
    intro p hp
    obtain ⟨hprime, hpQ⟩ := hP p hp
    have hc : (0 : ℝ) < ((occupiedClasses p A).card : ℝ) := by
      exact_mod_cast occupiedClasses_card_pos hprime.pos hAne
    have hmont := occupied_mul_sum_nonzero_ge hprime.pos A
    rw [← sum_fareySet_fibre_eq hprime hpQ A, ← properFareySet_fibre_prime hprime (Q := Q)] at hmont
    rw [mul_div_assoc', div_le_iff₀ hc]
    linarith [hmont, mul_comm ((occupiedClasses p A).card : ℝ)
      (∑ x ∈ (properFareySet Q).filter (fun x => x.2 = p),
        ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((x.1 : ℝ) / (x.2 : ℝ)))‖ ^ (2 : ℕ))]
  have hdisj : (↑P : Set ℕ).PairwiseDisjoint
      (fun p => (properFareySet Q).filter (fun x => x.2 = p)) := by
    intro p _ p' _ hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro x hx hx'
    rw [mem_filter] at hx hx'
    exact hne (hx.2.symm.trans hx'.2)
  have hsub : P.biUnion (fun p => (properFareySet Q).filter (fun x => x.2 = p)) ⊆
      properFareySet Q := by
    intro x hx
    obtain ⟨p, _, hxp⟩ := mem_biUnion.mp hx
    exact (mem_filter.mp hxp).1
  have hfibres : ∑ p ∈ P, ∑ x ∈ (properFareySet Q).filter (fun x => x.2 = p),
        ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((x.1 : ℝ) / (x.2 : ℝ)))‖ ^ (2 : ℕ) ≤
      ∑ x ∈ properFareySet Q,
        ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((x.1 : ℝ) / (x.2 : ℝ)))‖ ^ (2 : ℕ) := by
    rw [← sum_biUnion hdisj]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  have hbig := largeSieve_set_properFarey_logFree N hQ A hA
  have hcardpos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast card_pos.mpr hAne
  have hchain : (A.card : ℝ) ^ (2 : ℕ) * ∑ p ∈ P,
      ((p : ℝ) - ((occupiedClasses p A).card : ℝ)) / ((occupiedClasses p A).card : ℝ) ≤
      ((N : ℝ) + 2 * (Q : ℝ) ^ 2 - 1) * (A.card : ℝ) := by
    rw [mul_sum]
    exact (sum_le_sum hlow).trans (hfibres.trans hbig)
  refine le_of_mul_le_mul_right ?_ hcardpos
  calc ((A.card : ℝ) * ∑ p ∈ P,
        ((p : ℝ) - ((occupiedClasses p A).card : ℝ)) / ((occupiedClasses p A).card : ℝ)) *
        (A.card : ℝ)
      = (A.card : ℝ) ^ (2 : ℕ) * ∑ p ∈ P,
          ((p : ℝ) - ((occupiedClasses p A).card : ℝ)) / ((occupiedClasses p A).card : ℝ) := by
        ring
    _ ≤ _ := hchain

/-- **The sieve bound with the log-free constant.** A set in `[0, N)` omitting at least `w_p` classes
modulo each prime `p ∈ P` has at most `(N + 2Q² - 1)/L` elements, `L ≤ Σ_p w_p/(p - w_p)`. -/
theorem card_le_of_sieve_logFree (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (A : Finset ℕ)
    (hA : A ⊆ range N) (hAne : A.Nonempty) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q)
    (w : ℕ → ℝ) (hwp : ∀ p ∈ P, w p < (p : ℝ))
    (hocc : ∀ p ∈ P, ((occupiedClasses p A).card : ℝ) + w p ≤ (p : ℝ))
    {L : ℝ} (hL : 0 < L) (hLle : L ≤ ∑ p ∈ P, w p / ((p : ℝ) - w p)) :
    (A.card : ℝ) ≤ ((N : ℝ) + 2 * (Q : ℝ) ^ 2 - 1) / L := by
  have hbase := montgomery_sieve_logFree N hQ A hA hAne P hP
  have hcard : (0 : ℝ) ≤ (A.card : ℝ) := by positivity
  have hmono : ∑ p ∈ P, w p / ((p : ℝ) - w p) ≤
      ∑ p ∈ P, ((p : ℝ) - ((occupiedClasses p A).card : ℝ)) /
        ((occupiedClasses p A).card : ℝ) := by
    refine sum_le_sum fun p hp => ?_
    obtain ⟨hprime, _⟩ := hP p hp
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have hcpos : (0 : ℝ) < ((occupiedClasses p A).card : ℝ) := by
      exact_mod_cast occupiedClasses_card_pos hprime.pos hAne
    exact deficiency_ge hppos hcpos (hwp p hp) (hocc p hp)
  rw [le_div_iff₀ hL]
  exact (mul_le_mul_of_nonneg_left hLle hcard).trans
    ((mul_le_mul_of_nonneg_left hmono hcard).trans hbase)

end

end GaloisForLFunctions.BezoutValuationIncidence
