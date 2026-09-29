import GaloisForLFunctions.RHTower.MobiusHilbertExponentLaw
import GaloisForLFunctions.RHTower.MobiusCubicGammaNorm

/-!
# The mean-square Mertens exponent law

Let `M(k) = Σ_{n ≤ k} μ(n)` and `Θ = sup {Re ρ : ζ(ρ) = 0}`.  For `c ≥ 1` off the boundary
`c = 2Θ + 1`,

`Σ_{k ≤ X} M(k)² = O(X^c)`  ⟺  `2Θ + 1 < c`

(`exists_sum_sq_shiftedMertens_le_rpow_iff`).

* `⇐`: Littlewood's bound `M(k) ≪ k^{Θ+ε}` (`mobiusMertens_subpower_zetaZeroAbscissa`).
* `⇒`: the Abel form of the finite Möbius–Laplace pencil and Cauchy–Schwarz give
  `E_N(r) ≤ 2Γ(r) M(N)² (2N)^{-r} + 2Γ(r+1) Σ_{k<N} M(k+1)² (k+1)^{-(r+1)}`
  (`finiteMobiusGammaHankelEnergy_le_mertens`).  Abel summation bounds the sum uniformly when
  `r > c - 1`, and a cutoff `N` with small `M(N)` exists in every dyadic block.  The energies are
  therefore bounded along infinitely many cutoffs, and the closed-half-plane criterion excludes
  zeros with `Re ρ ≥ r/2`.

Every Möbius energy that controls the Mertens mean square is thus a receiver: its growth exponent
detects `Θ` and nothing else.
-/

open MeasureTheory Set Filter Finset

noncomputable section

namespace RHTower

/-- The shifted Mertens sum vanishes at `0`. -/
theorem shiftedMertensReal_zero : shiftedMertensReal 0 = 0 := by
  simp [shiftedMertensReal]

/-- Weighted Cauchy–Schwarz: `(Σ a_k w_k)² ≤ (Σ a_k² w_k)(Σ w_k)` for `w ≥ 0`. -/
theorem sq_sum_mul_le_sum_sq_mul_mul_sum (s : Finset ℕ) (a w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k) :
    (∑ k ∈ s, a k * w k) ^ 2 ≤ (∑ k ∈ s, a k ^ 2 * w k) * ∑ k ∈ s, w k := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun k => a k * Real.sqrt (w k))
    (fun k => Real.sqrt (w k))
  have e1 : ∀ k, a k * Real.sqrt (w k) * Real.sqrt (w k) = a k * w k := fun k => by
    rw [mul_assoc, Real.mul_self_sqrt (hw k)]
  have e2 : ∀ k, (a k * Real.sqrt (w k)) ^ 2 = a k ^ 2 * w k := fun k => by
    rw [mul_pow, Real.sq_sqrt (hw k)]
  have e3 : ∀ k, Real.sqrt (w k) ^ 2 = w k := fun k => Real.sq_sqrt (hw k)
  simp only [e1, e2, e3] at h
  exact h

/-- Pointwise Abel–Cauchy–Schwarz bound for the Möbius–Laplace pencil. -/
theorem sq_finiteMobiusLaplacePencil_le (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    finiteMobiusLaplacePencil N x ^ 2 ≤
      2 * (shiftedMertensReal N ^ 2 * Real.exp (-x) ^ (2 * N)) +
        2 * (x * ∑ k ∈ range N, shiftedMertensReal (k + 1) ^ 2 * Real.exp (-x) ^ (k + 1)) := by
  rw [finiteMobiusLaplacePencil_eq_abel]
  set q : ℝ := Real.exp (-x) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h1q : 1 - q ≤ x := by have := Real.add_one_le_exp (-x); rw [hq]; linarith
  have h1q0 : 0 ≤ 1 - q := by linarith
  have hw : ∀ k : ℕ, 0 ≤ q ^ k := fun k => pow_nonneg hq0 k
  have hcs := sq_sum_mul_le_sum_sq_mul_mul_sum (range N) shiftedMertensReal (fun k => q ^ k) hw
  have hgeom : (1 - q) * ∑ k ∈ range N, q ^ k ≤ 1 := by
    rw [mul_comm, geom_sum_mul_neg]; linarith [pow_nonneg hq0 N]
  have hS0 : 0 ≤ ∑ k ∈ range N, shiftedMertensReal k ^ 2 * q ^ k :=
    Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (hw k)
  have hshift : ∑ k ∈ range N, shiftedMertensReal k ^ 2 * q ^ k ≤
      ∑ k ∈ range N, shiftedMertensReal (k + 1) ^ 2 * q ^ (k + 1) := by
    rcases N with _ | n
    · simp
    · rw [Finset.sum_range_succ', shiftedMertensReal_zero, Finset.sum_range_succ]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero]
      exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (hw _))
  have hsecond : ((1 - q) * ∑ k ∈ range N, shiftedMertensReal k * q ^ k) ^ 2 ≤
      x * ∑ k ∈ range N, shiftedMertensReal (k + 1) ^ 2 * q ^ (k + 1) := by
    calc ((1 - q) * ∑ k ∈ range N, shiftedMertensReal k * q ^ k) ^ 2
        = (1 - q) ^ 2 * (∑ k ∈ range N, shiftedMertensReal k * q ^ k) ^ 2 := by ring
      _ ≤ (1 - q) ^ 2 * ((∑ k ∈ range N, shiftedMertensReal k ^ 2 * q ^ k) *
            ∑ k ∈ range N, q ^ k) := mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = (1 - q) * (∑ k ∈ range N, shiftedMertensReal k ^ 2 * q ^ k) *
            ((1 - q) * ∑ k ∈ range N, q ^ k) := by ring
      _ ≤ (1 - q) * (∑ k ∈ range N, shiftedMertensReal k ^ 2 * q ^ k) * 1 :=
          mul_le_mul_of_nonneg_left hgeom (mul_nonneg h1q0 hS0)
      _ ≤ x * ∑ k ∈ range N, shiftedMertensReal (k + 1) ^ 2 * q ^ (k + 1) := by
          rw [mul_one]; exact mul_le_mul h1q hshift hS0 hx
  have hfirst : (shiftedMertensReal N * q ^ N) ^ 2 = shiftedMertensReal N ^ 2 * q ^ (2 * N) := by
    rw [mul_pow, ← pow_mul, mul_comm N 2]
  nlinarith [sq_nonneg (shiftedMertensReal N * q ^ N -
    (1 - q) * ∑ k ∈ range N, shiftedMertensReal k * q ^ k)]

/-- **Energy bound in terms of the Mertens function.** -/
theorem finiteMobiusGammaHankelEnergy_le_mertens {N : ℕ} (hN : 1 ≤ N) {r : ℝ} (hr : 0 < r) :
    finiteMobiusGammaHankelEnergy N r ≤
      2 * shiftedMertensReal N ^ 2 * ((1 / (2 * N : ℝ)) ^ r * Real.Gamma r) +
        2 * ∑ k ∈ range N, shiftedMertensReal (k + 1) ^ 2 *
          ((1 / ((k : ℝ) + 1)) ^ (r + 1) * Real.Gamma (r + 1)) := by
  have hN0 : (0 : ℝ) < 2 * N := by positivity
  set g : ℝ → ℝ := fun x =>
    2 * shiftedMertensReal N ^ 2 * (x ^ (r - 1) * Real.exp (-((2 * N : ℝ) * x))) +
      ∑ k ∈ range N, 2 * shiftedMertensReal (k + 1) ^ 2 *
        (x ^ ((r + 1) - 1) * Real.exp (-(((k : ℝ) + 1) * x))) with hg
  have hint1 : IntegrableOn (fun x : ℝ => x ^ (r - 1) * Real.exp (-((2 * N : ℝ) * x))) (Ioi 0) :=
    CubicGamma.integrableOn_rpow_mul_exp hr hN0
  have hint2 : ∀ k ∈ range N, IntegrableOn
      (fun x : ℝ => 2 * shiftedMertensReal (k + 1) ^ 2 *
        (x ^ ((r + 1) - 1) * Real.exp (-(((k : ℝ) + 1) * x)))) (Ioi 0) := fun k _ =>
    (CubicGamma.integrableOn_rpow_mul_exp (by linarith) (by positivity)).const_mul _
  have hgi : IntegrableOn g (Ioi 0) :=
    (hint1.const_mul _).add (integrable_finsetSum _ hint2)
  rw [← integral_finiteMobiusLaplacePencil_sq N hr]
  calc (∫ x in Ioi (0 : ℝ), x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2)
      ≤ ∫ x in Ioi (0 : ℝ), g x := by
        refine integral_mono_of_nonneg ?_ hgi ?_
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          exact mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (sq_nonneg _)
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          have hx0 : 0 < x := hx
          have hp := sq_finiteMobiusLaplacePencil_le N hx0.le
          have hxr : 0 ≤ x ^ (r - 1) := Real.rpow_nonneg hx0.le _
          have he2 : Real.exp (-x) ^ (2 * N) = Real.exp (-((2 * N : ℝ) * x)) := by
            rw [← Real.exp_nat_mul]; push_cast; ring_nf
          have hek : ∀ k : ℕ, Real.exp (-x) ^ (k + 1) = Real.exp (-(((k : ℝ) + 1) * x)) :=
            fun k => by rw [← Real.exp_nat_mul]; push_cast; ring_nf
          have hxpow : x ^ (r - 1) * x = x ^ ((r + 1) - 1) := by
            rw [show (r + 1) - 1 = (r - 1) + 1 by ring, Real.rpow_add_one hx0.ne']
          calc x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2
              ≤ x ^ (r - 1) * (2 * (shiftedMertensReal N ^ 2 * Real.exp (-x) ^ (2 * N)) +
                  2 * (x * ∑ k ∈ range N, shiftedMertensReal (k + 1) ^ 2 *
                    Real.exp (-x) ^ (k + 1))) := mul_le_mul_of_nonneg_left hp hxr
            _ = g x := by
                rw [hg]
                simp only [he2, hek, mul_add, Finset.mul_sum]
                congr 1
                · ring
                · exact Finset.sum_congr rfl fun k _ => by rw [← hxpow]; ring
    _ = _ := by
        rw [hg, integral_add (hint1.const_mul _) (integrable_finsetSum _ hint2),
          integral_finsetSum _ hint2, integral_const_mul,
          Real.integral_rpow_mul_exp_neg_mul_Ioi hr hN0]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith)
          (by positivity)]
        ring

/-- `u^{-p} - (u+1)^{-p} ≤ p u^{-p-1}` for `u ≥ 1`, `p ≥ 1`. -/
theorem rpow_neg_sub_rpow_neg_succ_le {u p : ℝ} (hu : 1 ≤ u) (hp : 1 ≤ p) :
    u ^ (-p) - (u + 1) ^ (-p) ≤ p * u ^ (-p - 1) := by
  have hu0 : 0 < u := by linarith
  have hs : -1 ≤ -(1 / (u + 1)) := by
    rw [neg_le_neg_iff, div_le_one (by linarith)]; linarith
  have hb := one_add_mul_self_le_rpow_one_add hs hp
  have hfrac : 1 + -(1 / (u + 1)) = u / (u + 1) := by field_simp; ring
  rw [hfrac] at hb
  have hsplit : (u + 1) ^ (-p) = u ^ (-p) * (u / (u + 1)) ^ p := by
    rw [Real.div_rpow hu0.le (by linarith), Real.rpow_neg (by linarith), Real.rpow_neg hu0.le]
    field_simp
  have hup : 0 ≤ u ^ (-p) := Real.rpow_nonneg hu0.le _
  have hpow : u ^ (-p - 1) = u ^ (-p) / u := by
    rw [Real.rpow_sub hu0, Real.rpow_one]
  rw [hsplit, hpow]
  have h1 : u ^ (-p) - u ^ (-p) * (u / (u + 1)) ^ p ≤ u ^ (-p) * (p * (1 / (u + 1))) := by
    nlinarith [mul_le_mul_of_nonneg_left hb hup]
  calc u ^ (-p) - u ^ (-p) * (u / (u + 1)) ^ p ≤ u ^ (-p) * (p * (1 / (u + 1))) := h1
    _ ≤ u ^ (-p) * (p * (1 / u)) := by
        apply mul_le_mul_of_nonneg_left _ hup
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact one_div_le_one_div_of_le hu0 (by linarith)
    _ = p * (u ^ (-p) / u) := by field_simp

/-- **Abel summation against the mean-square bound.**  If
`Σ_{k ≤ X} M(k)² ≤ C(X+1)^c` for all `X`, `1 ≤ p` and `c < p`, the weighted sums
`Σ_{k<N} M(k+1)² (k+1)^{-p}` are bounded uniformly in `N`. -/
theorem exists_forall_sum_sq_mertens_rpow_neg_le {C c p : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hp : 1 ≤ p) (hcp : c < p)
    (hS : ∀ X : ℕ, ∑ k ∈ range (X + 1), shiftedMertensReal k ^ 2 ≤ C * ((X : ℝ) + 1) ^ c) :
    ∃ B : ℝ, ∀ N : ℕ,
      ∑ k ∈ range N, shiftedMertensReal (k + 1) ^ 2 * ((k : ℝ) + 1) ^ (-p) ≤ B := by
  have hsum : Summable fun i : ℕ => ((i : ℝ) + 1) ^ (c - p - 1) := by
    have h := (Real.summable_nat_rpow (p := c - p - 1)).mpr (by linarith)
    have h' := (summable_nat_add_iff 1).mpr h
    exact h'.congr fun i => by push_cast; ring_nf
  set T : ℝ := ∑' i : ℕ, ((i : ℝ) + 1) ^ (c - p - 1) with hT
  have hT0 : 0 ≤ T := tsum_nonneg fun i => Real.rpow_nonneg (by positivity) _
  refine ⟨C * 2 ^ c + p * C * 2 ^ c * T, fun N => ?_⟩
  set a : ℕ → ℝ := fun k => shiftedMertensReal (k + 1) ^ 2 with ha
  set w : ℕ → ℝ := fun k => ((k : ℝ) + 1) ^ (-p) with hw
  set G : ℕ → ℝ := fun m => ∑ j ∈ range m, a j with hG
  have hG0 : ∀ m, 0 ≤ G m := fun m => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hGle : ∀ m, G m ≤ C * ((m : ℝ) + 1) ^ c := by
    intro m
    have h := hS m
    rw [Finset.sum_range_succ', shiftedMertensReal_zero] at h
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at h
    exact h
  have hby := Finset.sum_range_by_parts w a N
  simp only [smul_eq_mul] at hby
  change ∑ k ∈ range N, a k * w k ≤ _
  rw [show ∑ k ∈ range N, a k * w k = ∑ i ∈ range N, w i * a i from
    Finset.sum_congr rfl fun i _ => mul_comm _ _, hby]
  -- the boundary term
  have hbd : w (N - 1) * ∑ i ∈ range N, a i ≤ C * 2 ^ c := by
    rcases N with _ | n
    · simp; positivity
    · simp only [Nat.add_sub_cancel]
      change w n * G (n + 1) ≤ _
      have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      calc w n * G (n + 1) ≤ ((n : ℝ) + 1) ^ (-p) * (C * (((n + 1 : ℕ) : ℝ) + 1) ^ c) :=
            mul_le_mul_of_nonneg_left (hGle _) (Real.rpow_nonneg (by positivity) _)
        _ ≤ ((n : ℝ) + 1) ^ (-p) * (C * (2 * ((n : ℝ) + 1)) ^ c) := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
            apply mul_le_mul_of_nonneg_left _ hC
            apply Real.rpow_le_rpow (by positivity) _ hc
            push_cast; linarith
        _ = C * 2 ^ c * ((n : ℝ) + 1) ^ (c - p) := by
            rw [Real.mul_rpow (by norm_num) (by positivity), Real.rpow_sub (by positivity),
              Real.rpow_neg (by positivity)]
            field_simp
        _ ≤ C * 2 ^ c * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
        _ = C * 2 ^ c := mul_one _
  -- the interior terms
  have hint : -∑ i ∈ range (N - 1), (w (i + 1) - w i) * ∑ j ∈ range (i + 1), a j ≤
      p * C * 2 ^ c * T := by
    rw [← Finset.sum_neg_distrib]
    have hterm : ∀ i ∈ range (N - 1), -((w (i + 1) - w i) * ∑ j ∈ range (i + 1), a j) ≤
        p * C * 2 ^ c * ((i : ℝ) + 1) ^ (c - p - 1) := by
      intro i _
      have hi1 : (1 : ℝ) ≤ (i : ℝ) + 1 := by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
      have hdiff := rpow_neg_sub_rpow_neg_succ_le hi1 hp
      have hwdiff : -(w (i + 1) - w i) ≤ p * ((i : ℝ) + 1) ^ (-p - 1) := by
        simp only [hw]; push_cast
        linarith
      have hwnn : 0 ≤ -(w (i + 1) - w i) := by
        simp only [hw]; push_cast
        have : ((i : ℝ) + 1 + 1) ^ (-p) ≤ ((i : ℝ) + 1) ^ (-p) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
        linarith
      have hGi : ∑ j ∈ range (i + 1), a j ≤ C * 2 ^ c * ((i : ℝ) + 1) ^ c := by
        refine (hGle (i + 1)).trans ?_
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hC
        rw [← Real.mul_rpow (by norm_num) (by positivity)]
        apply Real.rpow_le_rpow (by positivity) _ hc
        push_cast; linarith
      calc -((w (i + 1) - w i) * ∑ j ∈ range (i + 1), a j)
          = -(w (i + 1) - w i) * ∑ j ∈ range (i + 1), a j := by ring
        _ ≤ (p * ((i : ℝ) + 1) ^ (-p - 1)) * (C * 2 ^ c * ((i : ℝ) + 1) ^ c) :=
            mul_le_mul hwdiff hGi (hG0 _) (by positivity)
        _ = p * C * 2 ^ c * ((i : ℝ) + 1) ^ (c - p - 1) := by
            rw [show c - p - 1 = (-p - 1) + c by ring, Real.rpow_add (by positivity)]
            ring
    calc ∑ i ∈ range (N - 1), -((w (i + 1) - w i) * ∑ j ∈ range (i + 1), a j)
        ≤ ∑ i ∈ range (N - 1), p * C * 2 ^ c * ((i : ℝ) + 1) ^ (c - p - 1) :=
          Finset.sum_le_sum hterm
      _ = p * C * 2 ^ c * ∑ i ∈ range (N - 1), ((i : ℝ) + 1) ^ (c - p - 1) := by
          rw [Finset.mul_sum]
      _ ≤ p * C * 2 ^ c * T := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hsum.sum_le_tsum _ fun i _ => Real.rpow_nonneg (by positivity) _
  linarith

/-- **Bounded energies along infinitely many cutoffs.**  Under the mean-square bound, for every
`r > c - 1` the finite energies `E_N(r)` are bounded for infinitely many `N`. -/
theorem exists_frequently_energy_le_of_sum_sq_mertens {C c r : ℝ} (hC : 0 ≤ C) (hc : 1 ≤ c)
    (hr : 0 < r) (hcr : c - 1 < r)
    (hS : ∀ X : ℕ, ∑ k ∈ range (X + 1), shiftedMertensReal k ^ 2 ≤ C * ((X : ℝ) + 1) ^ c) :
    ∃ B : ℝ, ∃ᶠ N in atTop, finiteMobiusGammaHankelEnergy N r ≤ B := by
  obtain ⟨B₁, hB₁⟩ := exists_forall_sum_sq_mertens_rpow_neg_le hC (by linarith)
    (show 1 ≤ r + 1 by linarith) (by linarith) hS
  have hΓ : 0 < Real.Gamma r := Real.Gamma_pos_of_pos hr
  have hΓ1 : 0 < Real.Gamma (r + 1) := Real.Gamma_pos_of_pos (by linarith)
  refine ⟨2 * (C * 3 ^ c) * (2 ^ (-r) * Real.Gamma r) + 2 * (Real.Gamma (r + 1) * B₁),
    Filter.frequently_atTop.mpr fun X₀ => ?_⟩
  set X : ℕ := max X₀ 1 with hX
  have hX1 : 1 ≤ X := le_max_right _ _
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX1
  -- a cutoff with small Mertens value in `(X, 2X]`
  have hne : (Finset.Ioc X (2 * X)).Nonempty := ⟨2 * X, by simp; omega⟩
  have hsumle : ∑ n ∈ Finset.Ioc X (2 * X), shiftedMertensReal n ^ 2 ≤
      ∑ n ∈ Finset.Ioc X (2 * X), C * ((2 * X : ℝ) + 1) ^ c / X := by
    rw [Finset.sum_const, Nat.card_Ioc, show 2 * X - X = X by omega, nsmul_eq_mul]
    calc ∑ n ∈ Finset.Ioc X (2 * X), shiftedMertensReal n ^ 2
        ≤ ∑ n ∈ range (2 * X + 1), shiftedMertensReal n ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn; simp at hn ⊢; omega
          · intro n _ _; exact sq_nonneg _
      _ ≤ C * (((2 * X : ℕ) : ℝ) + 1) ^ c := hS _
      _ = (X : ℝ) * (C * ((2 * X : ℝ) + 1) ^ c / X) := by push_cast; field_simp
  obtain ⟨N, hN, hNle⟩ := Finset.exists_le_of_sum_le hne hsumle
  have hNX : X < N := (Finset.mem_Ioc.mp hN).1
  have hN1 : 1 ≤ N := by omega
  refine ⟨N, by omega, ?_⟩
  refine (finiteMobiusGammaHankelEnergy_le_mertens hN1 hr).trans ?_
  have hsum : ∑ k ∈ range N, shiftedMertensReal (k + 1) ^ 2 *
      ((1 / ((k : ℝ) + 1)) ^ (r + 1) * Real.Gamma (r + 1)) ≤ Real.Gamma (r + 1) * B₁ := by
    calc ∑ k ∈ range N, shiftedMertensReal (k + 1) ^ 2 *
          ((1 / ((k : ℝ) + 1)) ^ (r + 1) * Real.Gamma (r + 1))
        = Real.Gamma (r + 1) * ∑ k ∈ range N, shiftedMertensReal (k + 1) ^ 2 *
            ((k : ℝ) + 1) ^ (-(r + 1)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
          ring
      _ ≤ Real.Gamma (r + 1) * B₁ := mul_le_mul_of_nonneg_left (hB₁ N) hΓ1.le
  have hfirst : 2 * shiftedMertensReal N ^ 2 * ((1 / (2 * N : ℝ)) ^ r * Real.Gamma r) ≤
      2 * (C * 3 ^ c) * (2 ^ (-r) * Real.Gamma r) := by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hXN : (X : ℝ) < N := by exact_mod_cast hNX
    have h2X : (2 * X : ℝ) + 1 ≤ 3 * X := by linarith [(show (1 : ℝ) ≤ X by exact_mod_cast hX1)]
    have hM : shiftedMertensReal N ^ 2 ≤ C * 3 ^ c * (X : ℝ) ^ (c - 1) := by
      refine hNle.trans ?_
      calc C * ((2 * X : ℝ) + 1) ^ c / X ≤ C * (3 * X) ^ c / X := by
            apply div_le_div_of_nonneg_right _ hX0.le
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (by positivity) h2X (by linarith)) hC
        _ = C * 3 ^ c * (X : ℝ) ^ (c - 1) := by
            rw [Real.mul_rpow (by norm_num) hX0.le, Real.rpow_sub_one hX0.ne']
            field_simp
    have hpow : (1 / (2 * N : ℝ)) ^ r ≤ 2 ^ (-r) * (X : ℝ) ^ (-r) := by
      rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
        Real.mul_rpow (by norm_num) hN0.le]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_nonpos hX0 hXN.le (by linarith)
    have hXc : (X : ℝ) ^ (c - 1) * (X : ℝ) ^ (-r) ≤ 1 := by
      rw [← Real.rpow_add hX0]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hX1) (by linarith)
    calc 2 * shiftedMertensReal N ^ 2 * ((1 / (2 * N : ℝ)) ^ r * Real.Gamma r)
        ≤ 2 * (C * 3 ^ c * (X : ℝ) ^ (c - 1)) * ((2 ^ (-r) * (X : ℝ) ^ (-r)) * Real.Gamma r) := by
          gcongr
      _ = 2 * (C * 3 ^ c) * (2 ^ (-r) * Real.Gamma r) *
            ((X : ℝ) ^ (c - 1) * (X : ℝ) ^ (-r)) := by ring
      _ ≤ 2 * (C * 3 ^ c) * (2 ^ (-r) * Real.Gamma r) * 1 :=
          mul_le_mul_of_nonneg_left hXc (by positivity)
      _ = _ := mul_one _
  linarith

/-- **The Mertens mean square bounds the zero abscissa.**  If
`Σ_{k ≤ X} M(k)² ≤ C(X+1)^c` for all `X`, with `c ≥ 1`, then every zeta zero has
`Re ρ ≤ (c-1)/2`. -/
theorem zetaZeroAbscissa_le_of_sum_sq_shiftedMertens_le {C c : ℝ} (hc : 1 ≤ c)
    (hS : ∀ X : ℕ, ∑ k ∈ range (X + 1), shiftedMertensReal k ^ 2 ≤ C * ((X : ℝ) + 1) ^ c) :
    zetaZeroAbscissa ≤ (c - 1) / 2 := by
  have hC : 0 ≤ C := by
    have h := hS 0
    simp [shiftedMertensReal_zero] at h
    exact h
  apply le_of_forall_gt_imp_ge_of_dense
  intro σ hσ
  rcases le_or_gt 1 σ with h1 | h1
  · exact zetaZeroAbscissa_le_one.trans h1
  have hσ0 : 0 < σ := by linarith
  obtain ⟨B, hB⟩ := exists_frequently_energy_le_of_sum_sq_mertens hC hc (by linarith : 0 < 2 * σ)
    (by linarith) hS
  have hmem := memLp_mobiusLaplaceLogMellinLineSource_of_frequently_energy_le hσ0 hB
  apply csSup_le zetaZeroReSet_nonempty
  rintro x ⟨ρ, hρ, rfl⟩
  by_contra hcon
  rw [not_le] at hcon
  have hρ1 : ρ ≠ 1 := fun h => riemannZeta_one_ne_zero (h ▸ hρ)
  exact riemannZeta_ne_zero_of_memLp_mobiusLaplaceLogMellinLineSource_closed hσ0 h1 hmem
    hcon.le hρ1 hρ

/-- **The zero abscissa bounds the Mertens mean square** (Littlewood). -/
theorem exists_sum_sq_shiftedMertens_le_of_lt {c : ℝ} (hc : 2 * zetaZeroAbscissa + 1 < c) :
    ∃ C : ℝ, ∀ X : ℕ, ∑ k ∈ range (X + 1), shiftedMertensReal k ^ 2 ≤ C * ((X : ℝ) + 1) ^ c := by
  set ε : ℝ := (c - 2 * zetaZeroAbscissa - 1) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨C₁, hC₁, hM⟩ := mobiusMertens_subpower_zetaZeroAbscissa ε hε0
  refine ⟨C₁ ^ 2, fun X => ?_⟩
  have hX1 : (1 : ℝ) ≤ (X : ℝ) + 1 := by linarith [(Nat.cast_nonneg X : (0 : ℝ) ≤ X)]
  have hterm : ∀ k ∈ range (X + 1), shiftedMertensReal k ^ 2 ≤
      C₁ ^ 2 * ((X : ℝ) + 1) ^ (c - 1) := by
    intro k hk
    have hkX : (k : ℝ) + 1 ≤ (X : ℝ) + 1 := by
      have := Finset.mem_range.mp hk
      have : (k : ℝ) ≤ X := by exact_mod_cast Nat.lt_succ_iff.mp this
      linarith
    have hMk := hM k
    rw [norm_mobiusMertensPartialSum_eq_abs_shiftedMertensReal] at hMk
    have h0 : 0 ≤ ((k : ℝ) + 1) ^ (zetaZeroAbscissa + ε) := Real.rpow_nonneg (by positivity) _
    calc shiftedMertensReal k ^ 2 = |shiftedMertensReal k| ^ 2 := (sq_abs _).symm
      _ ≤ (C₁ * ((k : ℝ) + 1) ^ (zetaZeroAbscissa + ε)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hMk 2
      _ = C₁ ^ 2 * ((k : ℝ) + 1) ^ (2 * (zetaZeroAbscissa + ε)) := by
          have e : (((k : ℝ) + 1) ^ (zetaZeroAbscissa + ε)) ^ 2 =
              ((k : ℝ) + 1) ^ (2 * (zetaZeroAbscissa + ε)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; ring_nf
          rw [mul_pow, e]
      _ ≤ C₁ ^ 2 * ((X : ℝ) + 1) ^ (c - 1) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          calc ((k : ℝ) + 1) ^ (2 * (zetaZeroAbscissa + ε))
              ≤ ((X : ℝ) + 1) ^ (2 * (zetaZeroAbscissa + ε)) :=
                Real.rpow_le_rpow (by positivity) hkX
                  (by linarith [half_le_zetaZeroAbscissa])
            _ ≤ ((X : ℝ) + 1) ^ (c - 1) :=
                Real.rpow_le_rpow_of_exponent_le hX1 (by rw [hε]; linarith)
  calc ∑ k ∈ range (X + 1), shiftedMertensReal k ^ 2
      ≤ ∑ _k ∈ range (X + 1), C₁ ^ 2 * ((X : ℝ) + 1) ^ (c - 1) := Finset.sum_le_sum hterm
    _ = C₁ ^ 2 * ((X : ℝ) + 1) ^ c := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        rw [show c = (c - 1) + 1 by ring, Real.rpow_add_one (by positivity), sub_add_cancel]
        ring

/-- **Mean-square Mertens exponent law.**  For `c ≥ 1` off the boundary `c = 2Θ + 1`,
`Σ_{k ≤ X} M(k)² = O(X^c)` holds exactly when `2Θ + 1 < c`. -/
theorem exists_sum_sq_shiftedMertens_le_rpow_iff {c : ℝ} (hc : 1 ≤ c)
    (hne : c ≠ 2 * zetaZeroAbscissa + 1) :
    (∃ C : ℝ, ∀ X : ℕ, ∑ k ∈ range (X + 1), shiftedMertensReal k ^ 2 ≤
      C * ((X : ℝ) + 1) ^ c) ↔ 2 * zetaZeroAbscissa + 1 < c := by
  constructor
  · rintro ⟨C, hS⟩
    have h := zetaZeroAbscissa_le_of_sum_sq_shiftedMertens_le hc hS
    exact lt_of_le_of_ne (by linarith) (fun h' => hne h'.symm)
  · exact exists_sum_sq_shiftedMertens_le_of_lt

end RHTower
