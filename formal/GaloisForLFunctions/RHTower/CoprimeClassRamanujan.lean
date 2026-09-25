import GaloisForLFunctions.RHTower.CoprimeClassCount

open Complex ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

/-!
# A Ramanujan bound for exponential sums over a coprime residue class

For `(gcd(n',N), b) = 1` and `n ≠ 0`: `|Σ_{r mod n'N, r ≡ b (N), (r,n')=1} e(nr/(n'N))| ≤ n²` uniformly in `n'`
(`norm_class_sum_le`). Möbius inversion of `(r,n') = 1` leaves, for each `e | n'` with `(e,N) = 1`, one residue
class mod `eN` (Chinese remainder theorem), i.e. a geometric sum of length `n'/e` in `e(n/(n'/e))`, of size
`n'/e` if `(n'/e) | n` and `0` otherwise (`norm_geom_le`, `norm_inner_le`); classes with `(e,N) > 1` are empty. The
surviving terms are divisors of `n`, whose sum is at most `n²` (`sum_divisor_ite_le`). These are the Ramanujan-type
sums in the Fourier coefficients of the `Γ(N)` Eisenstein series at every cusp.
-/

namespace GaloisForLFunctions.RHTower.CoprimeClassRamanujan
open GaloisForLFunctions.RHTower.CoprimeClassCount

/-- The additive character `r ↦ e(nr/Q)`. -/
noncomputable def ph (n : ℤ) (Q : ℕ) (r : ℕ) : ℂ := cexp (2 * Real.pi * I * n * r / Q)

theorem norm_geom_le {M : ℕ} (hM : 0 < M) (n : ℤ) :
    ‖∑ k ∈ range M, ph n M k‖ ≤ if (M : ℤ) ∣ n then (M : ℝ) else 0 := by
  set w := cexp (2 * Real.pi * I * n / M)
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hk : ∀ k : ℕ, ph n M k = w ^ k := by
    intro k; unfold ph; rw [← Complex.exp_nat_mul]; congr 1; ring
  simp_rw [hk]
  have hw1 : ‖w‖ = 1 := by
    rw [Complex.norm_exp]; simp
  split_ifs with hd
  · refine (norm_sum_le _ _).trans ?_
    simp [norm_pow, hw1]
  · have hne : w ≠ 1 := by
      intro h
      obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
      apply hd
      refine ⟨k, ?_⟩
      have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
      have : (n : ℂ) = k * M := by
        field_simp at hk
        linear_combination hk
      exact_mod_cast (show (n : ℂ) = ((M * k : ℤ) : ℂ) by push_cast; rw [this]; ring)
    rw [geom_sum_eq hne]
    have hwM : w ^ M = 1 := by
      rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
      exact ⟨n, by field_simp⟩
    simp [hwM]

theorem sum_filter_reindex {x L M : ℕ} (hL : 0 < L) (hx : x < L) (f : ℕ → ℂ) :
    ∑ r ∈ (range (M * L)).filter (fun r => r ≡ x [MOD L]), f r = ∑ k ∈ range M, f (x + L * k) := by
  refine Finset.sum_nbij' (fun r => r / L) (fun k => x + L * k) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [mem_filter, mem_range] at hr ⊢
    exact (Nat.div_lt_iff_lt_mul hL).mpr hr.1
  · intro k hk
    simp only [mem_filter, mem_range] at hk ⊢
    refine ⟨by nlinarith, ?_⟩
    simp [Nat.ModEq, Nat.add_mul_mod_self_left]
  · intro r hr
    simp only [mem_filter, mem_range] at hr
    have h1 : r % L = x := by rw [hr.2]; exact Nat.mod_eq_of_lt hx
    have := Nat.mod_add_div r L
    omega
  · intro k _
    rw [Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt hx, zero_add]
  · intro r hr
    simp only [mem_filter, mem_range] at hr
    have h1 : r % L = x := by rw [hr.2]; exact Nat.mod_eq_of_lt hx
    have := Nat.mod_add_div r L
    congr 1; omega

theorem norm_inner_le {n' N e : ℕ} (hn' : 0 < n') (hN : 0 < N) (he : e ∣ n') (hco : e.Coprime N) (b : ℕ) (n : ℤ) :
    ‖∑ r ∈ (range (n' * N)).filter (fun r => r ≡ b [MOD N] ∧ e ∣ r), ph n (n' * N) r‖ ≤
      if ((n' / e : ℕ) : ℤ) ∣ n then ((n' / e : ℕ) : ℝ) else 0 := by
  have he0 : 0 < e := Nat.pos_of_dvd_of_pos he hn'
  obtain ⟨x, hx0, hxb⟩ := Nat.chineseRemainder hco 0 b
  set L := e * N
  have hL : 0 < L := Nat.mul_pos he0 hN
  have hiff : ∀ r, (r ≡ b [MOD N] ∧ e ∣ r) ↔ r ≡ x % L [MOD L] := by
    intro r
    rw [← Nat.modEq_and_modEq_iff_modEq_mul hco, ← Nat.modEq_zero_iff_dvd]
    have hxL : x % L ≡ x [MOD e * N] := Nat.mod_modEq x L
    have hxe : x % L ≡ x [MOD e] := Nat.ModEq.of_mul_right N hxL
    have hxN : x % L ≡ x [MOD N] := Nat.ModEq.of_mul_left e hxL
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(h2.trans hx0.symm).trans hxe.symm, (h1.trans hxb.symm).trans hxN.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨(h2.trans hxN).trans hxb, (h1.trans hxe).trans hx0⟩
  set M := n' / e
  have hn'M : n' = e * M := (Nat.mul_div_cancel' he).symm
  have hM : 0 < M := Nat.div_pos (Nat.le_of_dvd hn' he) he0
  have hK : n' * N = M * L := by rw [hn'M]; ring
  simp_rw [hiff]
  rw [hK, sum_filter_reindex hL (Nat.mod_lt x hL)]
  have hsplit : ∀ k, ph n (M * L) (x % L + L * k) = ph n (M * L) (x % L) * ph n M k := by
    intro k
    unfold ph
    rw [← Complex.exp_add]
    congr 1
    have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    push_cast
    field_simp
  simp_rw [hsplit]
  rw [← Finset.mul_sum, norm_mul]
  have h1 : ‖ph n (M * L) (x % L)‖ = 1 := by
    unfold ph
    rw [show 2 * (Real.pi : ℂ) * I * n * ((x % L : ℕ) : ℂ) / ((M * L : ℕ) : ℂ) =
      ((2 * Real.pi * n * (x % L : ℕ) / (M * L : ℕ) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  rw [h1, one_mul]
  exact norm_geom_le hM n

theorem sum_divisor_ite_le (n' : ℕ) {n : ℤ} (hn : n ≠ 0) :
    ∑ f ∈ n'.divisors, (if (f : ℤ) ∣ n then (f : ℝ) else 0) ≤ (n.natAbs : ℝ) ^ 2 := by
  rw [← Finset.sum_filter]
  have hsub : n'.divisors.filter (fun f : ℕ => (f : ℤ) ∣ n) ⊆ n.natAbs.divisors := by
    intro f hf
    simp only [mem_filter] at hf
    exact Nat.mem_divisors.mpr ⟨Int.natCast_dvd.mp hf.2, Int.natAbs_ne_zero.mpr hn⟩
  calc ∑ f ∈ n'.divisors.filter (fun f : ℕ => (f : ℤ) ∣ n), (f : ℝ)
      ≤ ∑ f ∈ n.natAbs.divisors, (f : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ ∑ _f ∈ n.natAbs.divisors, (n.natAbs : ℝ) :=
        Finset.sum_le_sum (fun f hf => by exact_mod_cast Nat.divisor_le hf)
    _ = n.natAbs.divisors.card * (n.natAbs : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n.natAbs : ℝ) * n.natAbs := by
        gcongr; exact_mod_cast Nat.card_divisors_le_self _
    _ = (n.natAbs : ℝ) ^ 2 := by ring

/-- **A Ramanujan bound for a coprime residue class**: if `(gcd(n',N), b) = 1` and `n ≠ 0`, then
`|Σ_{r mod n'N, r ≡ b (N), (r,n')=1} e(nr/(n'N))| ≤ n²`, uniformly in `n'`. -/
theorem norm_class_sum_le {n' N : ℕ} (hn' : 0 < n') (hN : 0 < N) {b : ℕ} (hb : (n'.gcd N).Coprime b)
    {n : ℤ} (hn : n ≠ 0) :
    ‖∑ r ∈ (range (n' * N)).filter (fun r => r ≡ b [MOD N] ∧ n'.Coprime r), ph n (n' * N) r‖ ≤
      (n.natAbs : ℝ) ^ 2 := by
  classical
  rw [Finset.sum_filter]
  have h1 : ∀ r ∈ range (n' * N), (if r ≡ b [MOD N] ∧ n'.Coprime r then ph n (n' * N) r else 0) =
      ∑ e ∈ n'.divisors, if r ≡ b [MOD N] ∧ e ∣ r then (μ e : ℂ) * ph n (n' * N) r else 0 := by
    intro r _
    by_cases hr : r ≡ b [MOD N]
    · simp only [hr, true_and]
      have hc := coprime_indicator hn' r
      have hc' : (if n'.Coprime r then (1 : ℂ) else 0) = ∑ e ∈ n'.divisors, if e ∣ r then (μ e : ℂ) else 0 := by
        have := congrArg (fun t : ℤ => (t : ℂ)) hc
        push_cast at this
        exact this
      calc (if n'.Coprime r then ph n (n' * N) r else 0)
          = (if n'.Coprime r then (1 : ℂ) else 0) * ph n (n' * N) r := by split_ifs <;> simp
        _ = _ := by rw [hc', Finset.sum_mul]; apply Finset.sum_congr rfl; intro e _; split_ifs <;> simp
    · simp [hr]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∀ e ∈ n'.divisors, (∑ r ∈ range (n' * N), if r ≡ b [MOD N] ∧ e ∣ r then (μ e : ℂ) * ph n (n' * N) r else 0)
      = (μ e : ℂ) * ∑ r ∈ (range (n' * N)).filter (fun r => r ≡ b [MOD N] ∧ e ∣ r), ph n (n' * N) r := by
    intro e _
    rw [← Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_congr rfl h2]
  refine (norm_sum_le _ _).trans ?_
  have h3 : ∀ e ∈ n'.divisors, ‖(μ e : ℂ) * ∑ r ∈ (range (n' * N)).filter (fun r => r ≡ b [MOD N] ∧ e ∣ r),
      ph n (n' * N) r‖ ≤ if ((n' / e : ℕ) : ℤ) ∣ n then ((n' / e : ℕ) : ℝ) else 0 := by
    intro e he
    have hen : e ∣ n' := Nat.dvd_of_mem_divisors he
    rw [norm_mul]
    have hμ : ‖(μ e : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    by_cases hco : e.Coprime N
    · calc ‖(μ e : ℂ)‖ * _ ≤ 1 * (if ((n' / e : ℕ) : ℤ) ∣ n then ((n' / e : ℕ) : ℝ) else 0) :=
            mul_le_mul hμ (norm_inner_le hn' hN hen hco b n) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    · have h0 : (range (n' * N)).filter (fun r => r ≡ b [MOD N] ∧ e ∣ r) = ∅ :=
        Finset.card_eq_zero.mp (card_crt_zero hen hco hb)
      rw [h0, Finset.sum_empty, norm_zero, mul_zero]
      split_ifs <;> positivity
  refine (Finset.sum_le_sum h3).trans ?_
  rw [Nat.sum_div_divisors n' (fun f => if (f : ℤ) ∣ n then (f : ℝ) else 0)]
  exact sum_divisor_ite_le n' hn

end GaloisForLFunctions.RHTower.CoprimeClassRamanujan
