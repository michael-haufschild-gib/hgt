/-
Bohr coefficient uniqueness for Dirichlet character series on the central line.

The mean-value (Bohr) inner product `M_y[·] = lim_{T→∞} T⁻¹∫₀ᵀ · dy` is orthogonal on the
almost-periodic characters `y ↦ exp(i·λ·y)`: `M_y[exp(i·λ·y)] = 1` if `λ = 0` and `0`
otherwise (Kronecker–Weyl, `RHTower.Weyl.trig_time_average`).  Applied to an absolutely
summable character series in the frequencies `log n`, this extracts individual coefficients,
the exponential (cleaner) analogue of the sine-series orthogonality of `OverlapRigidity`.

* `char_avg_finsum` — for a finite index set `s`, coefficients `C n i` with
  `∑ₙ ∑ᵢ ‖C n i‖ < ∞` and real frequencies `F n i`, the Cesàro average over `[0,T]` of the
  double character series `∑ₙ ∑ᵢ C n i · exp(i·F n i·y)` converges to
  `∑ₙ ∑ᵢ (if F n i = 0 then C n i else 0)`.  Interchange of window integral and the `n`-sum
  (`‖exp(iθy)‖ = 1`, dominated convergence), then term-by-term Weyl averaging.
* `char_avg_tendsto` — the single-character specialisation over `ℕ`.
* `char_series_coeff_zero` — if `∑ ‖b n‖ < ∞`, `b 0 = 0` and `∑ₙ b n · exp(i·y·log n) = 0`
  for every real `y`, then `b m = 0` for all `m ≥ 1`.  Averaging against `exp(−i·y·log m)`
  isolates the diagonal `log n = log m`; injectivity of `log` on positive integers and
  `b 0 = 0` collapse it to `b m`, while the vanishing series forces it to `0`.
* `conductor_datum_finite_support` — reflection payoff.  Let `∑ aₙ n^{−s}` converge
  absolutely at some `σ₀ < 1/2` and satisfy, on the overlap strip, a functional equation with
  a finite conductor datum, `L(s) = (∑_{j∈J} c_j Q_j^{1−2s})·L(1−s)`.  Then `a m = 0` for
  every `m ≥ 1` with `m ∤ Q_j²` for all `j`: the surviving coefficients lie in
  `⋃_j divisors(Q_j²)`, a finite set, so the series is a Dirichlet polynomial.  Evaluating at
  `s = ½ + iy` and setting `bₙ = aₙ n^{−½}` turns the equation into an equality of central-line
  character series; the two Cesàro averages agree, the left isolating `b m` and the right
  supported on frequencies `log(Q_j²/n)` — a `−log m` component of which requires `m ∣ Q_j²`
  (log-injectivity and `mn = Q_j²`), absent by hypothesis, so `b m = 0` and hence `a m = 0`.
* `conductor_datum_pairing` — the coefficient recursion behind that support statement.  Under the
  same absolute convergence and finite-conductor functional equation, the central-line Bohr average
  gives, for every `m ≥ 1`, `aₘ m^{−½} = ∑_{j∈J} (if m ∣ Q_j² then c_j·a_{Q_j²/m}·(Q_j²/m)^{−½}
  else 0)`.  The right Cesàro diagonal keeps the surviving frequencies `log m + log n − 2 log Q_j =
  0`, i.e. `mn = Q_j²`, pairing `m` with the cofactor `Q_j²/m` whenever `m ∣ Q_j²`; the `n = 0` term
  drops by `b 0 = 0`.  `conductor_datum_finite_support` is the case where every divisibility fails.
* `conductor_datum_pairing_coeff` — the same identity solved for `aₘ`, clearing `m^{−½}` via
  `m^{½}·m^{−½} = 1`: `aₘ = m^{½} · ∑_{j∈J} (if m ∣ Q_j² then c_j·a_{Q_j²/m}·(Q_j²/m)^{−½} else 0)`.
-/
import Mathlib
import GaloisForLFunctions.RHTower.WeylEquidistribution

open MeasureTheory intervalIntegral Filter Topology Complex

noncomputable section
namespace RHTower

private theorem norm_char_eq_one (θ y : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I * (y : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have : ((θ : ℂ) * Complex.I * (y : ℂ)).re = 0 := by simp
  rw [this, Real.exp_zero]

theorem char_avg_finsum {ι : Type*} (s : Finset ι) (C : ℕ → ι → ℂ) (F : ℕ → ι → ℝ)
    (hsum : Summable fun n => ∑ i ∈ s, ‖C n i‖) :
    Tendsto (fun T : ℝ => (↑T)⁻¹ * ∫ y in (0:ℝ)..T,
        ∑' n : ℕ, ∑ i ∈ s, C n i * Complex.exp ((F n i : ℂ) * Complex.I * (y : ℂ)))
      atTop (𝓝 (∑' n : ℕ, ∑ i ∈ s, if F n i = 0 then C n i else 0)) := by
  set fterm : ℕ → ℝ → ℂ :=
    fun n y => ∑ i ∈ s, C n i * Complex.exp ((F n i : ℂ) * Complex.I * (y : ℂ)) with hfterm
  have hcont : ∀ n : ℕ, Continuous (fterm n) := by
    intro n; rw [hfterm]; fun_prop
  have hbound : ∀ n : ℕ, ∀ y : ℝ, ‖fterm n y‖ ≤ ∑ i ∈ s, ‖C n i‖ := by
    intro n y
    rw [hfterm]
    refine le_trans (norm_sum_le _ _) ?_
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul, norm_char_eq_one, mul_one]
  have hInterchange : ∀ T : ℝ, 0 ≤ T →
      (∑' n : ℕ, ∫ y in Set.Ioc (0:ℝ) T, fterm n y)
        = ∫ y in Set.Ioc (0:ℝ) T, ∑' n : ℕ, fterm n y := by
    intro T hT
    refine MeasureTheory.integral_tsum_of_summable_integral_norm (fun n => ?_) ?_
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
        ((hcont n).intervalIntegrable 0 T)
    · have hIocVol : volume.real (Set.Ioc (0:ℝ) T) = T := by
        rw [Real.volume_real_Ioc, sub_zero, max_eq_left hT]
      refine Summable.of_nonneg_of_le
        (fun n => integral_nonneg fun y => norm_nonneg _) (fun n => ?_) (hsum.mul_right T)
      calc (∫ y in Set.Ioc (0:ℝ) T, ‖fterm n y‖)
          ≤ ‖∫ y in Set.Ioc (0:ℝ) T, ‖fterm n y‖‖ := le_abs_self _ |>.trans (le_of_eq (Real.norm_eq_abs _).symm)
        _ ≤ (∑ i ∈ s, ‖C n i‖) * volume.real (Set.Ioc (0:ℝ) T) :=
            norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top (fun y _ => by
              rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hbound n y)
        _ = (∑ i ∈ s, ‖C n i‖) * T := by rw [hIocVol]
  have key : ∀ T : ℝ, 0 ≤ T →
      (↑T)⁻¹ * ∫ y in (0:ℝ)..T, ∑' n : ℕ, fterm n y
        = ∑' n : ℕ, (↑T)⁻¹ * ∫ y in (0:ℝ)..T, fterm n y := by
    intro T hT
    rw [integral_of_le hT, ← hInterchange T hT, ← tsum_mul_left]
    apply tsum_congr; intro n
    rw [integral_of_le hT]
  have hlim : Tendsto (fun T : ℝ => ∑' n : ℕ, (↑T)⁻¹ * ∫ y in (0:ℝ)..T, fterm n y) atTop
      (𝓝 (∑' n : ℕ, ∑ i ∈ s, if F n i = 0 then C n i else 0)) := by
    apply tendsto_tsum_of_dominated_convergence hsum
    · intro n
      have hrw : (fun T : ℝ => (↑T)⁻¹ * ∫ y in (0:ℝ)..T, fterm n y)
          = fun T : ℝ => ∑ i ∈ s, C n i *
              ((↑T)⁻¹ * ∫ y in (0:ℝ)..T, Complex.exp ((F n i : ℂ) * Complex.I * (y : ℂ))) := by
        funext T
        rw [hfterm, intervalIntegral.integral_finsetSum
            (fun i _ => ((by fun_prop : Continuous (fun y : ℝ =>
              C n i * Complex.exp ((F n i : ℂ) * Complex.I * (y : ℂ)))).intervalIntegrable 0 T))]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        rw [intervalIntegral.integral_const_mul]; ring
      rw [hrw]
      exact tendsto_finsetSum s (fun i _ => RHTower.Weyl.char_term_time_average_tendsto (F n) (C n) i)
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
      intro n
      rw [norm_mul]
      have hI : ‖∫ y in (0:ℝ)..T, fterm n y‖ ≤ (∑ i ∈ s, ‖C n i‖) * |T - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun y _ => hbound n y
      rw [sub_zero, abs_of_pos hT] at hI
      have hTinv : ‖((T:ℝ) : ℂ)⁻¹‖ = T⁻¹ := by
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
      rw [hTinv]
      calc T⁻¹ * ‖∫ y in (0:ℝ)..T, fterm n y‖
          ≤ T⁻¹ * ((∑ i ∈ s, ‖C n i‖) * T) := by gcongr
        _ = ∑ i ∈ s, ‖C n i‖ := by
            rw [mul_comm (∑ i ∈ s, ‖C n i‖) T, ← mul_assoc, inv_mul_cancel₀ hT.ne', one_mul]
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
  rw [key T hT]

theorem char_avg_tendsto {c : ℕ → ℂ} (hc : Summable fun n => ‖c n‖) (ν : ℕ → ℝ) :
    Tendsto (fun T : ℝ => (↑T)⁻¹ * ∫ y in (0:ℝ)..T,
        ∑' n : ℕ, c n * Complex.exp ((ν n : ℂ) * Complex.I * (y : ℂ)))
      atTop (𝓝 (∑' n : ℕ, if ν n = 0 then c n else 0)) := by
  have h := char_avg_finsum (Finset.univ : Finset Unit) (fun n _ => c n) (fun n _ => ν n)
    (by simpa using hc)
  simpa using h

private theorem log_eq_imp_zero {m n : ℕ} (hm : 1 ≤ m) (hne : n ≠ m)
    (heq : Real.log (n : ℝ) = Real.log (m : ℝ)) : n = 0 := by
  by_contra hn0
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hmpos : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hcast : (n : ℝ) = (m : ℝ) := by
    rw [← Real.exp_log hnpos, ← Real.exp_log hmpos, heq]
  exact hne (by exact_mod_cast hcast)

theorem char_series_coeff_zero {b : ℕ → ℂ} (hsum : Summable fun n => ‖b n‖) (hb0 : b 0 = 0)
    (hvan : ∀ y : ℝ, ∑' n : ℕ, b n * Complex.exp ((Real.log n : ℂ) * Complex.I * (y : ℂ)) = 0) :
    ∀ m, 1 ≤ m → b m = 0 := by
  intro m hm
  have havg := char_avg_tendsto hsum (fun n => Real.log n - Real.log m)
  have hzero : Tendsto (fun T : ℝ => (↑T)⁻¹ * ∫ y in (0:ℝ)..T,
      ∑' n : ℕ, b n *
        Complex.exp (((Real.log n - Real.log m : ℝ) : ℂ) * Complex.I * (y : ℂ)))
      atTop (𝓝 0) := by
    have hInt : ∀ y : ℝ, (∑' n : ℕ, b n *
        Complex.exp (((Real.log n - Real.log m : ℝ) : ℂ) * Complex.I * (y : ℂ))) = 0 := by
      intro y
      have hterm : ∀ n : ℕ,
          b n * Complex.exp (((Real.log n - Real.log m : ℝ) : ℂ) * Complex.I * (y : ℂ))
            = Complex.exp (((-(Real.log m) : ℝ) : ℂ) * Complex.I * (y : ℂ)) *
              (b n * Complex.exp ((Real.log n : ℂ) * Complex.I * (y : ℂ))) := by
        intro n
        rw [show ((Real.log n - Real.log m : ℝ) : ℂ) * Complex.I * (y : ℂ)
              = (Real.log n : ℂ) * Complex.I * (y : ℂ)
                + ((-(Real.log m) : ℝ) : ℂ) * Complex.I * (y : ℂ) by push_cast; ring,
          Complex.exp_add]
        ring
      rw [tsum_congr hterm, tsum_mul_left, hvan y, mul_zero]
    have hfun : (fun T : ℝ => (↑T)⁻¹ * ∫ y in (0:ℝ)..T,
        ∑' n : ℕ, b n *
          Complex.exp (((Real.log n - Real.log m : ℝ) : ℂ) * Complex.I * (y : ℂ)))
        = fun _ : ℝ => (0 : ℂ) := by
      funext T
      rw [show (fun y : ℝ => ∑' n : ℕ, b n *
          Complex.exp (((Real.log n - Real.log m : ℝ) : ℂ) * Complex.I * (y : ℂ)))
            = fun _ => (0:ℂ) from funext hInt, intervalIntegral.integral_zero, mul_zero]
    rw [hfun]; exact tendsto_const_nhds
  have hdiag : (∑' n : ℕ, if Real.log n - Real.log m = 0 then b n else 0) = 0 :=
    tendsto_nhds_unique havg hzero
  have hcollapse : (∑' n : ℕ, if Real.log n - Real.log m = 0 then b n else 0) = b m := by
    have hpt : ∀ n : ℕ, (if Real.log n - Real.log m = 0 then b n else 0)
        = (if n = m then b m else 0) := by
      intro n
      by_cases hnm : n = m
      · subst hnm; rw [if_pos (sub_self _), if_pos rfl]
      · rw [if_neg hnm]
        by_cases hlog : Real.log n - Real.log m = 0
        · rw [if_pos hlog]
          have : n = 0 := log_eq_imp_zero hm hnm (sub_eq_zero.mp hlog)
          rw [this, hb0]
        · rw [if_neg hlog]
    rw [tsum_congr hpt, tsum_eq_single m (fun n hn => if_neg hn), if_pos rfl]
  rw [hcollapse] at hdiag
  exact hdiag

private theorem term_eq_char_plus (a : ℕ → ℂ) (y : ℝ) (n : ℕ) :
    LSeries.term a ((1/2 : ℂ) + ↑y * Complex.I) n
      = (a n * (n : ℂ) ^ (-(1/2 : ℂ))) * Complex.exp (((-Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero]
    simp only [Nat.cast_zero]
    rw [Complex.zero_cpow (by norm_num : -(1/2 : ℂ) ≠ 0)]; ring
  · rw [LSeries.term_of_ne_zero hn]
    have hn0 : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn
    have hlog : Complex.log ((n : ℕ) : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (by positivity)]
    have hcpow : ∀ w : ℂ, ((n : ℕ) : ℂ) ^ w = Complex.exp (((Real.log n : ℝ) : ℂ) * w) := by
      intro w; rw [Complex.cpow_def_of_ne_zero hn0, hlog]
    rw [hcpow, hcpow, div_eq_mul_inv, ← Complex.exp_neg, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring

private theorem term_eq_char_minus (a : ℕ → ℂ) (y : ℝ) (n : ℕ) :
    LSeries.term a ((1/2 : ℂ) - ↑y * Complex.I) n
      = (a n * (n : ℂ) ^ (-(1/2 : ℂ))) * Complex.exp (((Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero]
    simp only [Nat.cast_zero]
    rw [Complex.zero_cpow (by norm_num : -(1/2 : ℂ) ≠ 0)]; ring
  · rw [LSeries.term_of_ne_zero hn]
    have hn0 : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn
    have hlog : Complex.log ((n : ℕ) : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (by positivity)]
    have hcpow : ∀ w : ℂ, ((n : ℕ) : ℂ) ^ w = Complex.exp (((Real.log n : ℝ) : ℂ) * w) := by
      intro w; rw [Complex.cpow_def_of_ne_zero hn0, hlog]
    rw [hcpow, hcpow, div_eq_mul_inv, ← Complex.exp_neg, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring

private theorem qpow_eq_char (Q : ℕ) (hQ : 1 ≤ Q) (y : ℝ) :
    (Q : ℂ) ^ ((1 : ℂ) - 2 * ((1/2 : ℂ) + ↑y * Complex.I))
      = Complex.exp (((-(2 * Real.log Q) : ℝ) : ℂ) * Complex.I * (y : ℂ)) := by
  have hQ0 : ((Q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hlog : Complex.log ((Q : ℕ) : ℂ) = ((Real.log Q : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast Q, ← Complex.ofReal_log (by positivity)]
  rw [Complex.cpow_def_of_ne_zero hQ0, hlog]
  congr 1
  push_cast; ring

private theorem diag_collapse_sub {bb : ℕ → ℂ} (hbb0 : bb 0 = 0) {m : ℕ} (hm : 1 ≤ m) :
    (∑' n : ℕ, if Real.log (m : ℝ) - Real.log (n : ℝ) = 0 then bb n else 0) = bb m := by
  have hpt : ∀ n : ℕ, (if Real.log (m : ℝ) - Real.log (n : ℝ) = 0 then bb n else 0)
      = (if n = m then bb m else 0) := by
    intro n
    by_cases hnm : n = m
    · subst hnm; rw [if_pos (sub_self _), if_pos rfl]
    · rw [if_neg hnm]
      by_cases hlog : Real.log (m : ℝ) - Real.log (n : ℝ) = 0
      · rw [if_pos hlog]
        have hn0 : n = 0 := log_eq_imp_zero hm hnm (sub_eq_zero.mp hlog).symm
        rw [hn0, hbb0]
      · rw [if_neg hlog]
  rw [tsum_congr hpt, tsum_eq_single m (fun n hn => if_neg hn), if_pos rfl]

private theorem freq_ne_of_not_dvd {m : ℕ} (hm : 1 ≤ m) {Q : ℕ} (hQ : 1 ≤ Q)
    (hnd : ¬ m ∣ Q ^ 2) (n : ℕ) :
    Real.log (m : ℝ) + Real.log (n : ℝ) - 2 * Real.log (Q : ℝ) ≠ 0 := by
  intro h
  apply hnd
  have hmpos : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hQpos : (0:ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hlogQ2 : 2 * Real.log (Q : ℝ) = Real.log ((Q : ℝ) ^ 2) := by
    rw [Real.log_pow]; push_cast; ring
  rcases eq_or_ne n 0 with rfl | hn
  · have hlogm : Real.log (m : ℝ) = Real.log ((Q : ℝ) ^ 2) := by
      rw [← hlogQ2]; simp only [Nat.cast_zero, Real.log_zero, add_zero] at h; linarith
    have hQ2pos : (0:ℝ) < (Q : ℝ) ^ 2 := pow_pos hQpos 2
    have hcast : (m : ℝ) = (Q : ℝ) ^ 2 := by
      rw [← Real.exp_log hmpos, ← Real.exp_log hQ2pos, hlogm]
    have hmn : m = Q ^ 2 := by exact_mod_cast hcast
    exact ⟨1, by rw [hmn, mul_one]⟩
  · have hnpos : (0:ℝ) < (n : ℝ) := by
      have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      exact_mod_cast this
    have hlogmn : Real.log (m : ℝ) + Real.log (n : ℝ) = Real.log (((m * n : ℕ)) : ℝ) := by
      push_cast; rw [Real.log_mul hmpos.ne' hnpos.ne']
    have hEq : Real.log (((m * n : ℕ)) : ℝ) = Real.log ((Q : ℝ) ^ 2) := by
      rw [← hlogmn, ← hlogQ2]; linarith
    have hmn_pos : 0 < m * n := Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hn)
    have hmnpos : (0:ℝ) < (((m * n : ℕ)) : ℝ) := by exact_mod_cast hmn_pos
    have hQ2pos : (0:ℝ) < (Q : ℝ) ^ 2 := pow_pos hQpos 2
    have hcast : (((m * n : ℕ)) : ℝ) = (Q : ℝ) ^ 2 := by
      rw [← Real.exp_log hmnpos, ← Real.exp_log hQ2pos, hEq]
    have hmn : m * n = Q ^ 2 := by exact_mod_cast hcast
    exact ⟨n, hmn.symm⟩

theorem conductor_datum_finite_support {ι : Type*} {a : ℕ → ℂ} {σ₀ : ℝ} (hσ : σ₀ < 1/2)
    (hsum : LSeriesSummable a σ₀) (J : Finset ι) (c : ι → ℂ) (Q : ι → ℕ)
    (hQ : ∀ j ∈ J, 1 ≤ Q j)
    (hFE : ∀ s : ℂ, σ₀ < s.re → s.re < 1 - σ₀ →
      LSeries a s = (∑ j ∈ J, c j * (Q j : ℂ) ^ ((1 : ℂ) - 2 * s)) * LSeries a (1 - s)) :
    ∀ m : ℕ, 1 ≤ m → (∀ j ∈ J, ¬ (m ∣ (Q j) ^ 2)) → a m = 0 := by
  intro m hm hdiv
  have hb_sum : Summable fun n : ℕ => ‖a n * (n : ℂ) ^ (-(1/2 : ℂ))‖ := by
    have hhalf : LSeriesSummable a (((1:ℝ)/2 : ℝ) : ℂ) :=
      hsum.of_re_le_re (by rw [Complex.ofReal_re, Complex.ofReal_re]; linarith)
    have hnorm : Summable fun n => ‖LSeries.term a (((1:ℝ)/2 : ℝ) : ℂ) n‖ :=
      summable_norm_iff.mpr hhalf
    refine hnorm.congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [LSeries.term_zero, norm_zero, Nat.cast_zero]
      rw [Complex.zero_cpow (by norm_num : -(1/2 : ℂ) ≠ 0), mul_zero, norm_zero]
    · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
      rw [LSeries.norm_term_eq, if_neg hn, norm_mul,
        Complex.norm_natCast_cpow_of_pos hn0, Complex.ofReal_re,
        show (-(1/2 : ℂ)).re = -((1:ℝ)/2) by simp,
        Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hb0 : (fun n : ℕ => a n * (n : ℂ) ^ (-(1/2 : ℂ))) 0 = 0 := by
    simp only [Nat.cast_zero]
    rw [Complex.zero_cpow (by norm_num : -(1/2 : ℂ) ≠ 0), mul_zero]
  have hL1 : ∀ y : ℝ, LSeries a ((1/2 : ℂ) + ↑y * Complex.I)
      = ∑' n : ℕ, (a n * (n : ℂ) ^ (-(1/2 : ℂ)))
          * Complex.exp (((-Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ)) := by
    intro y
    rw [show LSeries a ((1/2 : ℂ) + ↑y * Complex.I)
        = ∑' n : ℕ, LSeries.term a ((1/2 : ℂ) + ↑y * Complex.I) n from rfl]
    exact tsum_congr (fun n => term_eq_char_plus a y n)
  have hL2 : ∀ y : ℝ, LSeries a ((1/2 : ℂ) - ↑y * Complex.I)
      = ∑' n : ℕ, (a n * (n : ℂ) ^ (-(1/2 : ℂ)))
          * Complex.exp (((Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ)) := by
    intro y
    rw [show LSeries a ((1/2 : ℂ) - ↑y * Complex.I)
        = ∑' n : ℕ, LSeries.term a ((1/2 : ℂ) - ↑y * Complex.I) n from rfl]
    exact tsum_congr (fun n => term_eq_char_minus a y n)
  -- integrand equality: fL(y) = fR(y)
  have hInteg : ∀ y : ℝ,
      (∑' n : ℕ, (a n * (n : ℂ) ^ (-(1/2 : ℂ)))
          * Complex.exp (((Real.log m - Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ)))
        = ∑' n : ℕ, ∑ j ∈ J, (c j * (a n * (n : ℂ) ^ (-(1/2 : ℂ))))
            * Complex.exp (((Real.log m + Real.log n - 2 * Real.log (Q j) : ℝ) : ℂ)
                * Complex.I * (y : ℂ)) := by
    intro y
    have hre : ((1/2 : ℂ) + ↑y * Complex.I).re = 1/2 := by simp
    have hfey := hFE ((1/2 : ℂ) + ↑y * Complex.I) (by rw [hre]; linarith) (by rw [hre]; linarith)
    rw [show (1 : ℂ) - ((1/2 : ℂ) + ↑y * Complex.I) = (1/2 : ℂ) - ↑y * Complex.I by ring] at hfey
    have hD : (∑ j ∈ J, c j * (Q j : ℂ) ^ ((1 : ℂ) - 2 * ((1/2 : ℂ) + ↑y * Complex.I)))
        = ∑ j ∈ J, c j
            * Complex.exp (((-(2 * Real.log (Q j)) : ℝ) : ℂ) * Complex.I * (y : ℂ)) := by
      apply Finset.sum_congr rfl; intro j hj
      rw [qpow_eq_char (Q j) (hQ j hj) y]
    have hDshift : Complex.exp (((Real.log m : ℝ) : ℂ) * Complex.I * (y : ℂ))
        * (∑ j ∈ J, c j
            * Complex.exp (((-(2 * Real.log (Q j)) : ℝ) : ℂ) * Complex.I * (y : ℂ)))
        = ∑ j ∈ J, c j
            * Complex.exp (((Real.log m - 2 * Real.log (Q j) : ℝ) : ℂ) * Complex.I * (y : ℂ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j hj
      rw [show ((Real.log m - 2 * Real.log (Q j) : ℝ) : ℂ) * Complex.I * (y : ℂ)
            = ((Real.log m : ℝ) : ℂ) * Complex.I * (y : ℂ)
              + ((-(2 * Real.log (Q j)) : ℝ) : ℂ) * Complex.I * (y : ℂ) by push_cast; ring,
        Complex.exp_add]
      ring
    -- common middle value
    have hMidL : (∑' n : ℕ, (a n * (n : ℂ) ^ (-(1/2 : ℂ)))
          * Complex.exp (((Real.log m - Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ)))
        = (∑ j ∈ J, c j
            * Complex.exp (((Real.log m - 2 * Real.log (Q j) : ℝ) : ℂ) * Complex.I * (y : ℂ)))
          * LSeries a ((1/2 : ℂ) - ↑y * Complex.I) := by
      have step1 : (∑' n : ℕ, (a n * (n : ℂ) ^ (-(1/2 : ℂ)))
            * Complex.exp (((Real.log m - Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ)))
          = Complex.exp (((Real.log m : ℝ) : ℂ) * Complex.I * (y : ℂ))
            * LSeries a ((1/2 : ℂ) + ↑y * Complex.I) := by
        rw [hL1 y, ← tsum_mul_left]
        apply tsum_congr; intro n
        rw [show ((Real.log m - Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ)
              = ((Real.log m : ℝ) : ℂ) * Complex.I * (y : ℂ)
                + ((-Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ) by push_cast; ring,
          Complex.exp_add]
        ring
      rw [step1, hfey, hD, ← mul_assoc, hDshift]
    have hMidR : (∑' n : ℕ, ∑ j ∈ J, (c j * (a n * (n : ℂ) ^ (-(1/2 : ℂ))))
          * Complex.exp (((Real.log m + Real.log n - 2 * Real.log (Q j) : ℝ) : ℂ)
              * Complex.I * (y : ℂ)))
        = (∑ j ∈ J, c j
            * Complex.exp (((Real.log m - 2 * Real.log (Q j) : ℝ) : ℂ) * Complex.I * (y : ℂ)))
          * LSeries a ((1/2 : ℂ) - ↑y * Complex.I) := by
      have step : (∑' n : ℕ, ∑ j ∈ J, (c j * (a n * (n : ℂ) ^ (-(1/2 : ℂ))))
            * Complex.exp (((Real.log m + Real.log n - 2 * Real.log (Q j) : ℝ) : ℂ)
                * Complex.I * (y : ℂ)))
          = (∑ j ∈ J, c j
              * Complex.exp (((Real.log m - 2 * Real.log (Q j) : ℝ) : ℂ) * Complex.I * (y : ℂ)))
            * ∑' n : ℕ, (a n * (n : ℂ) ^ (-(1/2 : ℂ)))
                * Complex.exp (((Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ)) := by
        rw [← tsum_mul_left]
        apply tsum_congr; intro n
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro j hj
        rw [show ((Real.log m + Real.log n - 2 * Real.log (Q j) : ℝ) : ℂ) * Complex.I * (y : ℂ)
              = ((Real.log m - 2 * Real.log (Q j) : ℝ) : ℂ) * Complex.I * (y : ℂ)
                + ((Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ) by push_cast; ring,
          Complex.exp_add]
        ring
      rw [step, hL2 y]
    rw [hMidL, hMidR]
  -- the two Cesàro-average limits
  have havgL := char_avg_tendsto hb_sum (fun n => Real.log m - Real.log n)
  have hCsum : Summable fun n : ℕ => ∑ j ∈ J, ‖c j * (a n * (n : ℂ) ^ (-(1/2 : ℂ)))‖ := by
    have hrw : (fun n : ℕ => ∑ j ∈ J, ‖c j * (a n * (n : ℂ) ^ (-(1/2 : ℂ)))‖)
        = fun n => (∑ j ∈ J, ‖c j‖) * ‖a n * (n : ℂ) ^ (-(1/2 : ℂ))‖ := by
      funext n; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j hj; rw [norm_mul]
    rw [hrw]; exact hb_sum.mul_left _
  have havgR := char_avg_finsum J (fun n j => c j * (a n * (n : ℂ) ^ (-(1/2 : ℂ))))
    (fun n j => Real.log m + Real.log n - 2 * Real.log (Q j)) hCsum
  -- diagonal values
  have hLdiag := diag_collapse_sub (bb := fun n : ℕ => a n * (n : ℂ) ^ (-(1/2 : ℂ))) hb0 hm
  have hRdiag : (∑' n : ℕ, ∑ j ∈ J,
      if Real.log m + Real.log n - 2 * Real.log (Q j) = 0
        then c j * (a n * (n : ℂ) ^ (-(1/2 : ℂ))) else 0) = 0 := by
    have hzero : (fun n : ℕ => ∑ j ∈ J,
        if Real.log m + Real.log n - 2 * Real.log (Q j) = 0
          then c j * (a n * (n : ℂ) ^ (-(1/2 : ℂ))) else 0) = fun _ => (0:ℂ) := by
      funext n
      apply Finset.sum_eq_zero; intro j hj
      exact if_neg (freq_ne_of_not_dvd hm (hQ j hj) (hdiv j hj) n)
    rw [hzero, tsum_zero]
  -- combine
  have hbm : a m * (m : ℂ) ^ (-(1/2 : ℂ)) = 0 := by
    have hfun : (fun T : ℝ => (↑T)⁻¹ * ∫ y in (0:ℝ)..T,
          ∑' n : ℕ, (a n * (n : ℂ) ^ (-(1/2 : ℂ)))
            * Complex.exp (((Real.log m - Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ)))
        = (fun T : ℝ => (↑T)⁻¹ * ∫ y in (0:ℝ)..T,
          ∑' n : ℕ, ∑ j ∈ J, (c j * (a n * (n : ℂ) ^ (-(1/2 : ℂ))))
            * Complex.exp (((Real.log m + Real.log n - 2 * Real.log (Q j) : ℝ) : ℂ)
                * Complex.I * (y : ℂ))) := by
      funext T; congr 1; exact intervalIntegral.integral_congr (fun y _ => hInteg y)
    rw [hfun] at havgL
    have huniq := tendsto_nhds_unique havgL havgR
    rw [hLdiag, hRdiag] at huniq
    exact huniq
  have hmne : ((m : ℂ) ^ (-(1/2 : ℂ))) ≠ 0 := by
    rw [← norm_ne_zero_iff, Complex.norm_natCast_cpow_of_pos (by omega : 0 < m)]
    exact (Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < m)) _).ne'
  exact (mul_eq_zero.mp hbm).resolve_right hmne

private theorem freq_zero_iff_mul {m : ℕ} (hm : 1 ≤ m) {Q : ℕ} (hQ : 1 ≤ Q)
    {n : ℕ} (hn : 1 ≤ n) :
    Real.log (m : ℝ) + Real.log (n : ℝ) - 2 * Real.log (Q : ℝ) = 0 ↔ m * n = Q ^ 2 := by
  have hmpos : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hQpos : (0:ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hlogQ2 : 2 * Real.log (Q : ℝ) = Real.log ((Q : ℝ) ^ 2) := by
    rw [Real.log_pow]; push_cast; ring
  have hlogmn : Real.log (m : ℝ) + Real.log (n : ℝ) = Real.log (((m * n : ℕ)) : ℝ) := by
    push_cast; rw [Real.log_mul hmpos.ne' hnpos.ne']
  constructor
  · intro h
    have hEq : Real.log (((m * n : ℕ)) : ℝ) = Real.log ((Q : ℝ) ^ 2) := by
      rw [← hlogmn, ← hlogQ2]; linarith
    have hmn_pos : 0 < m * n := Nat.mul_pos (by omega) (by omega)
    have hmnpos : (0:ℝ) < (((m * n : ℕ)) : ℝ) := by exact_mod_cast hmn_pos
    have hQ2pos : (0:ℝ) < (Q : ℝ) ^ 2 := pow_pos hQpos 2
    have hcast : (((m * n : ℕ)) : ℝ) = (Q : ℝ) ^ 2 := by
      rw [← Real.exp_log hmnpos, ← Real.exp_log hQ2pos, hEq]
    exact_mod_cast hcast
  · intro h
    have hcast : (((m * n : ℕ)) : ℝ) = (Q : ℝ) ^ 2 := by exact_mod_cast h
    have hlogeq : Real.log (((m * n : ℕ)) : ℝ) = Real.log ((Q : ℝ) ^ 2) := by rw [hcast]
    linarith [hlogmn, hlogQ2, hlogeq]

private theorem diag_collapse_add {bb : ℕ → ℂ} (hbb0 : bb 0 = 0) {m : ℕ} (hm : 1 ≤ m)
    {Q : ℕ} (hQ : 1 ≤ Q) (c : ℂ) :
    (∑' n : ℕ, if Real.log (m : ℝ) + Real.log (n : ℝ) - 2 * Real.log (Q : ℝ) = 0
        then c * bb n else 0)
      = if m ∣ Q ^ 2 then c * bb (Q ^ 2 / m) else 0 := by
  by_cases hdvd : m ∣ Q ^ 2
  · rw [if_pos hdvd]
    obtain ⟨k, hk⟩ := hdvd
    have hkval : Q ^ 2 / m = k := by rw [hk]; exact Nat.mul_div_cancel_left k (by omega)
    have hkpos : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · rw [hk0, mul_zero] at hk
        have : 1 ≤ Q ^ 2 := Nat.one_le_pow 2 Q (by omega)
        omega
      · exact hk0
    have hpt : ∀ n : ℕ, (if Real.log (m : ℝ) + Real.log (n : ℝ) - 2 * Real.log (Q : ℝ) = 0
          then c * bb n else 0) = (if n = k then c * bb k else 0) := by
      intro n
      by_cases hnk : n = k
      · subst hnk
        rw [if_pos ((freq_zero_iff_mul hm hQ hkpos).mpr hk.symm), if_pos rfl]
      · rw [if_neg hnk]
        rcases Nat.eq_zero_or_pos n with hn0 | hn0
        · subst hn0
          by_cases hf : Real.log (m : ℝ) + Real.log ((0:ℕ) : ℝ) - 2 * Real.log (Q : ℝ) = 0
          · rw [if_pos hf, hbb0, mul_zero]
          · rw [if_neg hf]
        · by_cases hf : Real.log (m : ℝ) + Real.log (n : ℝ) - 2 * Real.log (Q : ℝ) = 0
          · exfalso
            have hmn : m * n = Q ^ 2 := (freq_zero_iff_mul hm hQ hn0).mp hf
            have : m * n = m * k := by rw [hmn, hk]
            exact hnk (Nat.eq_of_mul_eq_mul_left (by omega) this)
          · rw [if_neg hf]
    rw [hkval, tsum_congr hpt, tsum_eq_single k (fun n hn => if_neg hn), if_pos rfl]
  · rw [if_neg hdvd]
    have hz : (fun n : ℕ => if Real.log (m : ℝ) + Real.log (n : ℝ) - 2 * Real.log (Q : ℝ) = 0
          then c * bb n else 0) = fun _ => (0:ℂ) := by
      funext n; exact if_neg (freq_ne_of_not_dvd hm hQ hdvd n)
    rw [hz, tsum_zero]

/-- Reflection coefficient pairing.  Under the hypotheses of `conductor_datum_finite_support` -- an
absolutely convergent `∑ aₙ n^{−s}` at some `σ₀ < 1/2` obeying, on the overlap strip, the
finite-conductor functional equation `L(s) = (∑_{j∈J} c_j Q_j^{1−2s})·L(1−s)` -- the central-line
Bohr average yields, for every `m ≥ 1`, the exact coefficient relation
`aₘ·m^{−½} = ∑_{j∈J} (if m ∣ Q_j² then c_j·a_{Q_j²/m}·(Q_j²/m)^{−½} else 0)`.
Evaluating at `s = ½ + iy` turns the equation into an equality of character series in the
frequencies `log n`; the two Cesàro averages agree, the left isolating `b m := aₘ m^{−½}` and the
right, after swapping the `n`-sum with the finite `j`-sum, collapsing each diagonal
`log m + log n − 2 log Q_j = 0`.  For `n ≥ 1` that frequency vanishes iff `m·n = Q_j²`
(`exp∘log`), pairing `m` with the cofactor `Q_j²/m` exactly when `m ∣ Q_j²`; the `n = 0` term drops
by `b 0 = 0`.  `conductor_datum_finite_support` is the special case where every divisibility fails. -/
theorem conductor_datum_pairing {ι : Type*} {a : ℕ → ℂ} {σ₀ : ℝ} (hσ : σ₀ < 1/2)
    (hsum : LSeriesSummable a σ₀) (J : Finset ι) (c : ι → ℂ) (Q : ι → ℕ)
    (hQ : ∀ j ∈ J, 1 ≤ Q j)
    (hFE : ∀ s : ℂ, σ₀ < s.re → s.re < 1 - σ₀ →
      LSeries a s = (∑ j ∈ J, c j * (Q j : ℂ) ^ ((1 : ℂ) - 2 * s)) * LSeries a (1 - s)) :
    ∀ m : ℕ, 1 ≤ m →
      a m * (m : ℂ) ^ (-(1/2 : ℂ))
        = ∑ j ∈ J, if m ∣ (Q j) ^ 2
            then c j * (a ((Q j) ^ 2 / m) * (((Q j) ^ 2 / m : ℕ) : ℂ) ^ (-(1/2 : ℂ))) else 0 := by
  intro m hm
  have hb_sum : Summable fun n : ℕ => ‖a n * (n : ℂ) ^ (-(1/2 : ℂ))‖ := by
    have hhalf : LSeriesSummable a (((1:ℝ)/2 : ℝ) : ℂ) :=
      hsum.of_re_le_re (by rw [Complex.ofReal_re, Complex.ofReal_re]; linarith)
    have hnorm : Summable fun n => ‖LSeries.term a (((1:ℝ)/2 : ℝ) : ℂ) n‖ :=
      summable_norm_iff.mpr hhalf
    refine hnorm.congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [LSeries.term_zero, norm_zero, Nat.cast_zero]
      rw [Complex.zero_cpow (by norm_num : -(1/2 : ℂ) ≠ 0), mul_zero, norm_zero]
    · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
      rw [LSeries.norm_term_eq, if_neg hn, norm_mul,
        Complex.norm_natCast_cpow_of_pos hn0, Complex.ofReal_re,
        show (-(1/2 : ℂ)).re = -((1:ℝ)/2) by simp,
        Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hb0 : (fun n : ℕ => a n * (n : ℂ) ^ (-(1/2 : ℂ))) 0 = 0 := by
    simp only [Nat.cast_zero]
    rw [Complex.zero_cpow (by norm_num : -(1/2 : ℂ) ≠ 0), mul_zero]
  have hL1 : ∀ y : ℝ, LSeries a ((1/2 : ℂ) + ↑y * Complex.I)
      = ∑' n : ℕ, (a n * (n : ℂ) ^ (-(1/2 : ℂ)))
          * Complex.exp (((-Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ)) := by
    intro y
    rw [show LSeries a ((1/2 : ℂ) + ↑y * Complex.I)
        = ∑' n : ℕ, LSeries.term a ((1/2 : ℂ) + ↑y * Complex.I) n from rfl]
    exact tsum_congr (fun n => term_eq_char_plus a y n)
  have hL2 : ∀ y : ℝ, LSeries a ((1/2 : ℂ) - ↑y * Complex.I)
      = ∑' n : ℕ, (a n * (n : ℂ) ^ (-(1/2 : ℂ)))
          * Complex.exp (((Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ)) := by
    intro y
    rw [show LSeries a ((1/2 : ℂ) - ↑y * Complex.I)
        = ∑' n : ℕ, LSeries.term a ((1/2 : ℂ) - ↑y * Complex.I) n from rfl]
    exact tsum_congr (fun n => term_eq_char_minus a y n)
  -- integrand equality: fL(y) = fR(y)
  have hInteg : ∀ y : ℝ,
      (∑' n : ℕ, (a n * (n : ℂ) ^ (-(1/2 : ℂ)))
          * Complex.exp (((Real.log m - Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ)))
        = ∑' n : ℕ, ∑ j ∈ J, (c j * (a n * (n : ℂ) ^ (-(1/2 : ℂ))))
            * Complex.exp (((Real.log m + Real.log n - 2 * Real.log (Q j) : ℝ) : ℂ)
                * Complex.I * (y : ℂ)) := by
    intro y
    have hre : ((1/2 : ℂ) + ↑y * Complex.I).re = 1/2 := by simp
    have hfey := hFE ((1/2 : ℂ) + ↑y * Complex.I) (by rw [hre]; linarith) (by rw [hre]; linarith)
    rw [show (1 : ℂ) - ((1/2 : ℂ) + ↑y * Complex.I) = (1/2 : ℂ) - ↑y * Complex.I by ring] at hfey
    have hD : (∑ j ∈ J, c j * (Q j : ℂ) ^ ((1 : ℂ) - 2 * ((1/2 : ℂ) + ↑y * Complex.I)))
        = ∑ j ∈ J, c j
            * Complex.exp (((-(2 * Real.log (Q j)) : ℝ) : ℂ) * Complex.I * (y : ℂ)) := by
      apply Finset.sum_congr rfl; intro j hj
      rw [qpow_eq_char (Q j) (hQ j hj) y]
    have hDshift : Complex.exp (((Real.log m : ℝ) : ℂ) * Complex.I * (y : ℂ))
        * (∑ j ∈ J, c j
            * Complex.exp (((-(2 * Real.log (Q j)) : ℝ) : ℂ) * Complex.I * (y : ℂ)))
        = ∑ j ∈ J, c j
            * Complex.exp (((Real.log m - 2 * Real.log (Q j) : ℝ) : ℂ) * Complex.I * (y : ℂ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j hj
      rw [show ((Real.log m - 2 * Real.log (Q j) : ℝ) : ℂ) * Complex.I * (y : ℂ)
            = ((Real.log m : ℝ) : ℂ) * Complex.I * (y : ℂ)
              + ((-(2 * Real.log (Q j)) : ℝ) : ℂ) * Complex.I * (y : ℂ) by push_cast; ring,
        Complex.exp_add]
      ring
    -- common middle value
    have hMidL : (∑' n : ℕ, (a n * (n : ℂ) ^ (-(1/2 : ℂ)))
          * Complex.exp (((Real.log m - Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ)))
        = (∑ j ∈ J, c j
            * Complex.exp (((Real.log m - 2 * Real.log (Q j) : ℝ) : ℂ) * Complex.I * (y : ℂ)))
          * LSeries a ((1/2 : ℂ) - ↑y * Complex.I) := by
      have step1 : (∑' n : ℕ, (a n * (n : ℂ) ^ (-(1/2 : ℂ)))
            * Complex.exp (((Real.log m - Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ)))
          = Complex.exp (((Real.log m : ℝ) : ℂ) * Complex.I * (y : ℂ))
            * LSeries a ((1/2 : ℂ) + ↑y * Complex.I) := by
        rw [hL1 y, ← tsum_mul_left]
        apply tsum_congr; intro n
        rw [show ((Real.log m - Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ)
              = ((Real.log m : ℝ) : ℂ) * Complex.I * (y : ℂ)
                + ((-Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ) by push_cast; ring,
          Complex.exp_add]
        ring
      rw [step1, hfey, hD, ← mul_assoc, hDshift]
    have hMidR : (∑' n : ℕ, ∑ j ∈ J, (c j * (a n * (n : ℂ) ^ (-(1/2 : ℂ))))
          * Complex.exp (((Real.log m + Real.log n - 2 * Real.log (Q j) : ℝ) : ℂ)
              * Complex.I * (y : ℂ)))
        = (∑ j ∈ J, c j
            * Complex.exp (((Real.log m - 2 * Real.log (Q j) : ℝ) : ℂ) * Complex.I * (y : ℂ)))
          * LSeries a ((1/2 : ℂ) - ↑y * Complex.I) := by
      have step : (∑' n : ℕ, ∑ j ∈ J, (c j * (a n * (n : ℂ) ^ (-(1/2 : ℂ))))
            * Complex.exp (((Real.log m + Real.log n - 2 * Real.log (Q j) : ℝ) : ℂ)
                * Complex.I * (y : ℂ)))
          = (∑ j ∈ J, c j
              * Complex.exp (((Real.log m - 2 * Real.log (Q j) : ℝ) : ℂ) * Complex.I * (y : ℂ)))
            * ∑' n : ℕ, (a n * (n : ℂ) ^ (-(1/2 : ℂ)))
                * Complex.exp (((Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ)) := by
        rw [← tsum_mul_left]
        apply tsum_congr; intro n
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro j hj
        rw [show ((Real.log m + Real.log n - 2 * Real.log (Q j) : ℝ) : ℂ) * Complex.I * (y : ℂ)
              = ((Real.log m - 2 * Real.log (Q j) : ℝ) : ℂ) * Complex.I * (y : ℂ)
                + ((Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ) by push_cast; ring,
          Complex.exp_add]
        ring
      rw [step, hL2 y]
    rw [hMidL, hMidR]
  -- the two Cesàro-average limits
  have havgL := char_avg_tendsto hb_sum (fun n => Real.log m - Real.log n)
  have hCsum : Summable fun n : ℕ => ∑ j ∈ J, ‖c j * (a n * (n : ℂ) ^ (-(1/2 : ℂ)))‖ := by
    have hrw : (fun n : ℕ => ∑ j ∈ J, ‖c j * (a n * (n : ℂ) ^ (-(1/2 : ℂ)))‖)
        = fun n => (∑ j ∈ J, ‖c j‖) * ‖a n * (n : ℂ) ^ (-(1/2 : ℂ))‖ := by
      funext n; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j hj; rw [norm_mul]
    rw [hrw]; exact hb_sum.mul_left _
  have havgR := char_avg_finsum J (fun n j => c j * (a n * (n : ℂ) ^ (-(1/2 : ℂ))))
    (fun n j => Real.log m + Real.log n - 2 * Real.log (Q j)) hCsum
  -- diagonal values
  have hLdiag := diag_collapse_sub (bb := fun n : ℕ => a n * (n : ℂ) ^ (-(1/2 : ℂ))) hb0 hm
  have hRdiag : (∑' n : ℕ, ∑ j ∈ J,
      if Real.log m + Real.log n - 2 * Real.log (Q j) = 0
        then c j * (a n * (n : ℂ) ^ (-(1/2 : ℂ))) else 0)
      = ∑ j ∈ J, if m ∣ (Q j) ^ 2
          then c j * (a ((Q j) ^ 2 / m) * (((Q j) ^ 2 / m : ℕ) : ℂ) ^ (-(1/2 : ℂ))) else 0 := by
    have hf : ∀ j ∈ J, Summable (fun n : ℕ =>
        if Real.log m + Real.log n - 2 * Real.log (Q j) = 0
          then c j * (a n * (n : ℂ) ^ (-(1/2 : ℂ))) else 0) := by
      intro j _
      refine Summable.of_norm_bounded (hb_sum.mul_left ‖c j‖) (fun n => ?_)
      by_cases hcond : Real.log m + Real.log n - 2 * Real.log (Q j) = 0
      · exact le_of_eq (by rw [if_pos hcond, norm_mul])
      · rw [if_neg hcond, norm_zero]; positivity
    rw [Summable.tsum_finsetSum hf]
    apply Finset.sum_congr rfl
    intro j hj
    exact diag_collapse_add (bb := fun n : ℕ => a n * (n : ℂ) ^ (-(1/2 : ℂ)))
      hb0 hm (hQ j hj) (c j)
  have hbm : a m * (m : ℂ) ^ (-(1/2 : ℂ))
      = ∑ j ∈ J, if m ∣ (Q j) ^ 2
          then c j * (a ((Q j) ^ 2 / m) * (((Q j) ^ 2 / m : ℕ) : ℂ) ^ (-(1/2 : ℂ))) else 0 := by
    have hfun : (fun T : ℝ => (↑T)⁻¹ * ∫ y in (0:ℝ)..T,
          ∑' n : ℕ, (a n * (n : ℂ) ^ (-(1/2 : ℂ)))
            * Complex.exp (((Real.log m - Real.log n : ℝ) : ℂ) * Complex.I * (y : ℂ)))
        = (fun T : ℝ => (↑T)⁻¹ * ∫ y in (0:ℝ)..T,
          ∑' n : ℕ, ∑ j ∈ J, (c j * (a n * (n : ℂ) ^ (-(1/2 : ℂ))))
            * Complex.exp (((Real.log m + Real.log n - 2 * Real.log (Q j) : ℝ) : ℂ)
                * Complex.I * (y : ℂ))) := by
      funext T; congr 1; exact intervalIntegral.integral_congr (fun y _ => hInteg y)
    rw [hfun] at havgL
    have huniq := tendsto_nhds_unique havgL havgR
    rw [hLdiag, hRdiag] at huniq
    exact huniq
  exact hbm

/-- The reflection coefficient pairing solved for `aₘ`.  Clearing the `m^{−½}` factor in
`conductor_datum_pairing` via `m^{½}·m^{−½} = 1` gives, for every `m ≥ 1`,
`aₘ = m^{½} · ∑_{j∈J} (if m ∣ Q_j² then c_j·a_{Q_j²/m}·(Q_j²/m)^{−½} else 0)`. -/
theorem conductor_datum_pairing_coeff {ι : Type*} {a : ℕ → ℂ} {σ₀ : ℝ} (hσ : σ₀ < 1/2)
    (hsum : LSeriesSummable a σ₀) (J : Finset ι) (c : ι → ℂ) (Q : ι → ℕ)
    (hQ : ∀ j ∈ J, 1 ≤ Q j)
    (hFE : ∀ s : ℂ, σ₀ < s.re → s.re < 1 - σ₀ →
      LSeries a s = (∑ j ∈ J, c j * (Q j : ℂ) ^ ((1 : ℂ) - 2 * s)) * LSeries a (1 - s)) :
    ∀ m : ℕ, 1 ≤ m →
      a m = (m : ℂ) ^ (1/2 : ℂ) * ∑ j ∈ J, if m ∣ (Q j) ^ 2
          then c j * (a ((Q j) ^ 2 / m) * (((Q j) ^ 2 / m : ℕ) : ℂ) ^ (-(1/2 : ℂ))) else 0 := by
  intro m hm
  have hpair := conductor_datum_pairing hσ hsum J c Q hQ hFE m hm
  have hmne : ((m : ℂ)) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hid : (m : ℂ) ^ (1/2 : ℂ) * (m : ℂ) ^ (-(1/2 : ℂ)) = 1 := by
    rw [← Complex.cpow_add _ _ hmne, show (1/2 : ℂ) + -(1/2 : ℂ) = 0 by ring, Complex.cpow_zero]
  calc a m = a m * ((m : ℂ) ^ (1/2 : ℂ) * (m : ℂ) ^ (-(1/2 : ℂ))) := by rw [hid, mul_one]
    _ = (m : ℂ) ^ (1/2 : ℂ) * (a m * (m : ℂ) ^ (-(1/2 : ℂ))) := by ring
    _ = (m : ℂ) ^ (1/2 : ℂ) * ∑ j ∈ J, if m ∣ (Q j) ^ 2
          then c j * (a ((Q j) ^ 2 / m) * (((Q j) ^ 2 / m : ℕ) : ℂ) ^ (-(1/2 : ℂ))) else 0 := by
        rw [hpair]

end RHTower
