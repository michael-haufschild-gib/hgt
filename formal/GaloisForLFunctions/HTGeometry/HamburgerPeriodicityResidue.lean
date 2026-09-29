import Mathlib

/-!
# The residue-periodicity step of Hamburger's theorem

The partial-fraction series `L(t) = Σ_{n≥1} a_n t/(π(n² + t²))` is meromorphic, with a simple pole at
each `t = i n₀` (`n₀ ≥ 1`) of residue `a_{n₀}/(2π)` (`tendsto_sub_mul_hamburgerSeries`). The only
hypothesis is `Σ‖a_n‖/n² < ∞`. The tail near `i n₀` is controlled by the separation
`‖m² + t²‖ ≥ (|m − n₀| − ½)(m + n₀ − ½)` (`norm_sq_add_sq_ge`).

If `L(t + i) − L(t) = c/(t + i) − c/t` near `i n₀`, comparing the residues at `i(n₀+1)` and `i n₀`
gives `a_{n₀+1} = a_{n₀}` (`coeff_succ_eq_of_hamburgerSeries_periodic`). Since `L` is continuous
at `0` with `L(0) = 0`, the pole of `c/t` fixes `a₁ = −2πc`. The identity is only needed on the
open right half-plane, where the dual theta series converges: residues on the imaginary axis are
limits from the right, so every coefficient equals `−2πc`
(`coeff_eq_of_hamburgerSeries_periodic_re_pos`). In Hamburger's
characterization of `ζ` by its functional equation, this is the step that forces the Dirichlet
coefficients to be constant, after the Laplace transform has turned the dual theta series into an
`i`-periodic function.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The Hamburger partial-fraction series `L(t) = Σ_{n ≥ 1} a_n t / (π(n² + t²))`. -/
def hamburgerSeries (a : ℕ → ℂ) (t : ℂ) : ℂ :=
  ∑' n : ℕ, a (n + 1) * t / ((Real.pi : ℂ) * (((n + 1 : ℕ) : ℂ) ^ 2 + t ^ 2))

/-- Lower bound for `|m² + t²|` near `t = i n₀` when `m ≠ n₀`. -/
theorem norm_sq_add_sq_ge {m n₀ : ℕ} (hm : m ≠ n₀) {t : ℂ}
    (ht : ‖t - (n₀ : ℂ) * I‖ ≤ 1 / 2) :
    (|(m : ℝ) - n₀| - 1 / 2) * (((m : ℝ) + n₀) - 1 / 2) ≤ ‖((m : ℂ)) ^ 2 + t ^ 2‖ := by
  set η := t - (n₀ : ℂ) * I with hη
  have hfac : ((m : ℂ)) ^ 2 + t ^ 2 = ((m : ℂ) + t * I) * ((m : ℂ) - t * I) := by
    linear_combination t ^ 2 * I_sq
  rw [hfac, norm_mul]
  have ht' : t = (n₀ : ℂ) * I + η := by rw [hη]; ring
  have h1 : ‖(m : ℂ) + t * I‖ ≥ |(m : ℝ) - n₀| - 1 / 2 := by
    rw [ht']
    have : (m : ℂ) + ((n₀ : ℂ) * I + η) * I = ((m : ℝ) - n₀ : ℝ) + η * I := by
      push_cast; linear_combination (n₀ : ℂ) * I_sq
    rw [this]
    have hηI : ‖η * I‖ = ‖η‖ := by rw [norm_mul, norm_I, mul_one]
    have htri : ‖(((m : ℝ) - n₀ : ℝ) : ℂ)‖ ≤ ‖(((m : ℝ) - n₀ : ℝ) : ℂ) + η * I‖ + ‖η * I‖ := by
      have := norm_sub_le ((((m : ℝ) - n₀ : ℝ) : ℂ) + η * I) (η * I)
      simpa using this
    calc ‖(((m : ℝ) - n₀ : ℝ) : ℂ) + η * I‖ ≥ ‖(((m : ℝ) - n₀ : ℝ) : ℂ)‖ - ‖η * I‖ := by linarith
      _ ≥ |(m : ℝ) - n₀| - 1 / 2 := by rw [Complex.norm_real, Real.norm_eq_abs, hηI]; linarith
  have h2 : ‖(m : ℂ) - t * I‖ ≥ ((m : ℝ) + n₀) - 1 / 2 := by
    rw [ht']
    have : (m : ℂ) - ((n₀ : ℂ) * I + η) * I = ((m : ℝ) + n₀ : ℝ) - η * I := by
      push_cast; linear_combination -(n₀ : ℂ) * I_sq
    rw [this]
    have hηI : ‖η * I‖ = ‖η‖ := by rw [norm_mul, norm_I, mul_one]
    have := norm_sub_norm_le (((m : ℝ) + n₀ : ℝ) : ℂ) (η * I)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), hηI] at this
    linarith
  have hmn : (1 : ℝ) ≤ |(m : ℝ) - n₀| := by
    have : (m : ℤ) ≠ n₀ := by exact_mod_cast hm
    have h := Int.one_le_abs (sub_ne_zero.mpr this)
    have : |((m : ℤ) - n₀ : ℤ)| = |(m : ℝ) - n₀| := by push_cast; rfl
    exact_mod_cast (this ▸ (by exact_mod_cast h : (1 : ℝ) ≤ |((m : ℤ) - n₀ : ℤ)|))
  have hpos1 : 0 ≤ |(m : ℝ) - n₀| - 1 / 2 := by linarith
  have hpos2 : 0 ≤ ((m : ℝ) + n₀) - 1 / 2 := by
    have : (1 : ℝ) ≤ (m : ℝ) + n₀ := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; have : n₀ ≠ 0 := fun h' => hm h'.symm; simp; exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
      · have : (1 : ℝ) ≤ m := by exact_mod_cast h
        have : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
        linarith
    linarith
  exact mul_le_mul h1 h2 hpos2 (norm_nonneg _)

theorem sq_div_four_le_sep {m n₀ : ℕ} (hm : 2 * n₀ + 2 ≤ m) :
    (m : ℝ) ^ 2 / 4 ≤ (|(m : ℝ) - n₀| - 1 / 2) * (((m : ℝ) + n₀) - 1 / 2) := by
  have hm' : (2 * n₀ + 2 : ℝ) ≤ m := by exact_mod_cast hm
  have hn : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  rw [abs_of_nonneg (by linarith)]
  nlinarith

/-- The `n₀`-th residue of the Hamburger series: `(t − i n₀) L(t) → a_{n₀}/(2π)` as `t → i n₀`. -/
theorem tendsto_sub_mul_hamburgerSeries {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) {n₀ : ℕ} (hn₀ : 1 ≤ n₀) :
    Tendsto (fun t => (t - (n₀ : ℂ) * I) * hamburgerSeries a t) (𝓝[≠] ((n₀ : ℂ) * I))
      (𝓝 (a n₀ / (2 * Real.pi))) := by
  -- split off the term n + 1 = n₀
  set k := n₀ - 1 with hk
  have hkn : k + 1 = n₀ := by omega
  set term : ℕ → ℂ → ℂ := fun n t =>
    a (n + 1) * t / ((Real.pi : ℂ) * (((n + 1 : ℕ) : ℂ) ^ 2 + t ^ 2)) with hterm
  set R : ℂ → ℂ := fun t => ∑' n : ℕ, if n = k then 0 else term n t with hR
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set K : ℝ := 2 * (n₀ + 1) * (2 * n₀ + 2) ^ 2 / Real.pi with hK
  have hKpos : 0 ≤ K := by positivity
  have hbound : ∀ n : ℕ, ∀ t ∈ Metric.closedBall ((n₀ : ℂ) * I) (1 / 2),
      ‖(if n = k then 0 else term n t)‖ ≤ K * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    intro n t ht
    split_ifs with h1
    · simp; positivity
    have hne : n + 1 ≠ n₀ := by omega
    rw [Metric.mem_closedBall, dist_eq_norm] at ht
    have hsep := norm_sq_add_sq_ge hne ht
    have htn : ‖t‖ ≤ n₀ + 1 := by
      have := norm_add_le (t - (n₀ : ℂ) * I) ((n₀ : ℂ) * I)
      simp only [sub_add_cancel] at this
      have h3 : ‖(n₀ : ℂ) * I‖ = n₀ := by rw [norm_mul, norm_I, mul_one]; simp
      linarith
    have hm1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    -- lower bound for the denominator: ≥ (n+1)² / (2n₀+2)²
    have hden : ((n + 1 : ℕ) : ℝ) ^ 2 / (2 * (2 * n₀ + 2) ^ 2) ≤ ‖(((n + 1 : ℕ) : ℂ)) ^ 2 + t ^ 2‖ := by
      refine le_trans ?_ hsep
      have hmn : (1 : ℝ) ≤ |((n + 1 : ℕ) : ℝ) - n₀| := by
        have : ((n + 1 : ℕ) : ℤ) ≠ n₀ := by exact_mod_cast hne
        have h := Int.one_le_abs (sub_ne_zero.mpr this)
        have e : ((|(((n + 1 : ℕ) : ℤ) - n₀)| : ℤ) : ℝ) = |((n + 1 : ℕ) : ℝ) - n₀| := by push_cast; rfl
        rw [← e]; exact_mod_cast h
      have hn0 : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
      by_cases hbig : 2 * n₀ + 2 ≤ n + 1
      · have := sq_div_four_le_sep hbig
        have hd : ((n + 1 : ℕ) : ℝ) ^ 2 / (2 * (2 * n₀ + 2) ^ 2) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 / 4 := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
          nlinarith
        linarith
      · have hsmall : ((n + 1 : ℕ) : ℝ) ≤ 2 * n₀ + 2 := by
          push Not at hbig; exact_mod_cast hbig.le
        have h1' : ((n + 1 : ℕ) : ℝ) ^ 2 / (2 * (2 * n₀ + 2) ^ 2) ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]
          have := pow_le_pow_left₀ (by positivity) hsmall 2
          linarith
        have h2' : (1 : ℝ) / 2 * 1 ≤ (|((n + 1 : ℕ) : ℝ) - n₀| - 1 / 2) *
            (((n + 1 : ℕ) : ℝ) + n₀ - 1 / 2) := by
          apply mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
        linarith
    have hden_pos : 0 < ‖(((n + 1 : ℕ) : ℂ)) ^ 2 + t ^ 2‖ := lt_of_lt_of_le (by positivity) hden
    simp only [hterm]
    rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [div_le_iff₀ (mul_pos Real.pi_pos hden_pos)]
    calc ‖a (n + 1)‖ * ‖t‖ ≤ ‖a (n + 1)‖ * (n₀ + 1) := mul_le_mul_of_nonneg_left htn (norm_nonneg _)
      _ = K * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) *
            (Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 / (2 * (2 * n₀ + 2) ^ 2))) := by
          rw [hK]; field_simp
      _ ≤ K * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) *
            (Real.pi * ‖(((n + 1 : ℕ) : ℂ)) ^ 2 + t ^ 2‖) := by gcongr
  have hsumK : Summable fun n : ℕ => K * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) := ha.mul_left K
  -- continuity of the tail on the ball
  have hRcont : ContinuousOn R (Metric.closedBall ((n₀ : ℂ) * I) (1 / 2)) := by
    refine continuousOn_tsum (fun n => ?_) hsumK (fun n t ht => hbound n t ht)
    split_ifs with h1
    · exact continuousOn_const
    · have hne : n + 1 ≠ n₀ := by omega
      refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => ?_
      rw [Metric.mem_closedBall, dist_eq_norm] at ht
      have hsep := norm_sq_add_sq_ge hne ht
      have hmn : (1 : ℝ) ≤ |((n + 1 : ℕ) : ℝ) - n₀| := by
        have : ((n + 1 : ℕ) : ℤ) ≠ n₀ := by exact_mod_cast hne
        have h := Int.one_le_abs (sub_ne_zero.mpr this)
        have e : ((|(((n + 1 : ℕ) : ℤ) - n₀)| : ℤ) : ℝ) = |((n + 1 : ℕ) : ℝ) - n₀| := by push_cast; rfl
        rw [← e]; exact_mod_cast h
      have hn0 : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
      have hpos : 0 < (|((n + 1 : ℕ) : ℝ) - n₀| - 1 / 2) * (((n + 1 : ℕ) : ℝ) + n₀ - 1 / 2) := by
        have hm1' : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
        apply mul_pos (by linarith) (by linarith)
      intro h0
      have : ‖(((n + 1 : ℕ) : ℂ)) ^ 2 + t ^ 2‖ = 0 := by
        have := mul_eq_zero.mp h0
        rcases this with h | h
        · exact absurd h hπ
        · rw [h, norm_zero]
      linarith
  have hball : Metric.closedBall ((n₀ : ℂ) * I) (1 / 2) ∈ 𝓝 ((n₀ : ℂ) * I) :=
    Metric.closedBall_mem_nhds _ (by norm_num)
  have hRlim : Tendsto R (𝓝[≠] ((n₀ : ℂ) * I)) (𝓝 (R ((n₀ : ℂ) * I))) :=
    ((hRcont.continuousAt hball).tendsto).mono_left nhdsWithin_le_nhds
  -- the main term
  have hmain : Tendsto (fun t => (t - (n₀ : ℂ) * I) * term k t) (𝓝[≠] ((n₀ : ℂ) * I))
      (𝓝 (a n₀ / (2 * Real.pi))) := by
    have hlim : Tendsto (fun t : ℂ => a n₀ * t / ((Real.pi : ℂ) * (t + (n₀ : ℂ) * I)))
        (𝓝 ((n₀ : ℂ) * I)) (𝓝 (a n₀ / (2 * Real.pi))) := by
      have hn0 : (n₀ : ℂ) ≠ 0 := by exact_mod_cast (by omega : n₀ ≠ 0)
      have hc : ContinuousAt (fun t : ℂ => a n₀ * t / ((Real.pi : ℂ) * (t + (n₀ : ℂ) * I)))
          ((n₀ : ℂ) * I) := by
        refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
        refine mul_ne_zero hπ ?_
        intro h
        have : (2 : ℂ) * ((n₀ : ℂ) * I) = 0 := by linear_combination h
        simp [hn0, I_ne_zero] at this
      convert hc.tendsto using 1
      have hn0' : (n₀ : ℂ) * I ≠ 0 := mul_ne_zero hn0 I_ne_zero
      field_simp
      ring_nf
    have hnear : ∀ᶠ t in 𝓝[≠] ((n₀ : ℂ) * I), t ∈ Metric.ball ((n₀ : ℂ) * I) (1 / 2) :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds _ (by norm_num))
    refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin, hnear] with t ht hball
    have ht' : t - (n₀ : ℂ) * I ≠ 0 := sub_ne_zero.mpr ht
    simp only [hterm, hkn]
    have hfac : ((n₀ : ℕ) : ℂ) ^ 2 + t ^ 2 = (t - (n₀ : ℂ) * I) * (t + (n₀ : ℂ) * I) := by
      linear_combination (n₀ : ℂ) ^ 2 * I_sq
    rw [hfac]
    have ht'' : t + (n₀ : ℂ) * I ≠ 0 := by
      intro h
      rw [Metric.mem_ball, dist_eq_norm] at hball
      have e : t - (n₀ : ℂ) * I = -(2 * ((n₀ : ℂ) * I)) := by linear_combination h
      rw [e, norm_neg, norm_mul, norm_mul, norm_I, mul_one] at hball
      have hn0 : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
      simp at hball
      linarith
    field_simp
  have hsplit : ∀ᶠ t in 𝓝[≠] ((n₀ : ℂ) * I),
      (t - (n₀ : ℂ) * I) * hamburgerSeries a t =
        (t - (n₀ : ℂ) * I) * term k t + (t - (n₀ : ℂ) * I) * R t := by
    have hnear : ∀ᶠ t in 𝓝[≠] ((n₀ : ℂ) * I), t ∈ Metric.closedBall ((n₀ : ℂ) * I) (1 / 2) :=
      nhdsWithin_le_nhds hball
    filter_upwards [hnear] with t ht
    have hsumR : Summable fun n => (if n = k then 0 else term n t) :=
      Summable.of_norm_bounded hsumK (fun n => hbound n t ht)
    have hsumT : Summable fun n => term n t := by
      have hEq : (fun n => term n t) =
          fun n => (if n = k then 0 else term n t) + (if n = k then term k t else 0) := by
        funext n; split_ifs with h <;> simp [h]
      rw [hEq]
      exact hsumR.add (summable_of_ne_finset_zero (s := {k}) (fun n hn => by
        simp at hn; simp [hn]))
    have := hsumT.tsum_eq_add_tsum_ite k
    simp only [hamburgerSeries]
    change (t - (n₀ : ℂ) * I) * ∑' n, term n t = _
    rw [this, mul_add]
  refine (Tendsto.congr' (EventuallyEq.symm hsplit) ?_)
  have hzero : Tendsto (fun t => (t - (n₀ : ℂ) * I) * R t) (𝓝[≠] ((n₀ : ℂ) * I)) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℂ => t - (n₀ : ℂ) * I) (𝓝[≠] ((n₀ : ℂ) * I)) (𝓝 0) := by
      have hc : Tendsto (fun t : ℂ => t - (n₀ : ℂ) * I) (𝓝 ((n₀ : ℂ) * I))
          (𝓝 ((n₀ : ℂ) * I - (n₀ : ℂ) * I)) :=
        (continuous_id.sub continuous_const).tendsto ((n₀ : ℂ) * I)
      rw [sub_self] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    simpa using h1.mul hRlim
  simpa using hmain.add hzero

/-- **Hamburger's periodicity step.**  If `L(t + i) − L(t) = c/(t + i) − c/t` on a punctured
neighbourhood of `i n₀` (`n₀ ≥ 1`), then `a_{n₀+1} = a_{n₀}`: compare the residues at `i(n₀+1)`
and `i n₀`. -/
theorem coeff_succ_eq_of_hamburgerSeries_periodic {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) {n₀ : ℕ} (hn₀ : 1 ≤ n₀)
    (c : ℂ) (hper : ∀ᶠ t in 𝓝[≠] ((n₀ : ℂ) * I),
      hamburgerSeries a (t + I) - hamburgerSeries a t = c / (t + I) - c / t) :
    a (n₀ + 1) = a n₀ := by
  have hA := tendsto_sub_mul_hamburgerSeries ha hn₀
  have hB := tendsto_sub_mul_hamburgerSeries ha (n₀ := n₀ + 1) (by omega)
  -- transport hB along t ↦ t + I
  have hshift : Tendsto (fun t : ℂ => t + I) (𝓝[≠] ((n₀ : ℂ) * I))
      (𝓝[≠] (((n₀ + 1 : ℕ) : ℂ) * I)) := by
    have hc : Tendsto (fun t : ℂ => t + I) (𝓝 ((n₀ : ℂ) * I)) (𝓝 (((n₀ + 1 : ℕ) : ℂ) * I)) := by
      have := (continuous_id.add continuous_const).tendsto ((n₀ : ℂ) * I) (f := fun t : ℂ => t + I)
      convert this using 2
      push_cast; ring_nf
    refine tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
    intro h
    apply ht
    push_cast at h
    linear_combination h
  have hB' : Tendsto (fun t => ((t + I) - ((n₀ + 1 : ℕ) : ℂ) * I) * hamburgerSeries a (t + I))
      (𝓝[≠] ((n₀ : ℂ) * I)) (𝓝 (a (n₀ + 1) / (2 * Real.pi))) := hB.comp hshift
  have hB'' : Tendsto (fun t => (t - (n₀ : ℂ) * I) * hamburgerSeries a (t + I))
      (𝓝[≠] ((n₀ : ℂ) * I)) (𝓝 (a (n₀ + 1) / (2 * Real.pi))) := by
    refine hB'.congr' (Filter.Eventually.of_forall fun t => ?_)
    congr 1
    push_cast; ring_nf
  -- the right-hand side times (t - i n₀) tends to 0
  have hn0 : (n₀ : ℂ) ≠ 0 := by exact_mod_cast (by omega : n₀ ≠ 0)
  have hR : Tendsto (fun t => (t - (n₀ : ℂ) * I) * (c / (t + I) - c / t))
      (𝓝[≠] ((n₀ : ℂ) * I)) (𝓝 0) := by
    have h1 : (n₀ : ℂ) * I + I ≠ 0 := by
      intro h
      have : ((n₀ : ℂ) + 1) * I = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · have : ((n₀ + 1 : ℕ) : ℂ) = 0 := by push_cast; exact h'
        exact absurd (by exact_mod_cast this) (Nat.succ_ne_zero n₀)
      · exact I_ne_zero h'
    have h2 : (n₀ : ℂ) * I ≠ 0 := mul_ne_zero hn0 I_ne_zero
    have hc : ContinuousAt (fun t => (t - (n₀ : ℂ) * I) * (c / (t + I) - c / t)) ((n₀ : ℂ) * I) := by
      refine ContinuousAt.mul (by fun_prop) (ContinuousAt.sub ?_ ?_)
      · exact continuousAt_const.div (by fun_prop) h1
      · exact continuousAt_const.div continuousAt_id h2
    have := hc.tendsto
    simp only [sub_self, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hdiff : Tendsto (fun t => (t - (n₀ : ℂ) * I) * hamburgerSeries a (t + I) -
      (t - (n₀ : ℂ) * I) * hamburgerSeries a t) (𝓝[≠] ((n₀ : ℂ) * I))
      (𝓝 (a (n₀ + 1) / (2 * Real.pi) - a n₀ / (2 * Real.pi))) := hB''.sub hA
  have hdiff0 : Tendsto (fun t => (t - (n₀ : ℂ) * I) * hamburgerSeries a (t + I) -
      (t - (n₀ : ℂ) * I) * hamburgerSeries a t) (𝓝[≠] ((n₀ : ℂ) * I)) (𝓝 0) := by
    refine hR.congr' ?_
    filter_upwards [hper] with t ht
    rw [← mul_sub, ht]
  have huniq := tendsto_nhds_unique hdiff hdiff0
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have : a (n₀ + 1) - a n₀ = 0 := by
    have h := huniq
    rw [← sub_div] at h
    exact (div_eq_zero_iff.mp h).resolve_right hπ
  exact sub_eq_zero.mp this

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

/-- The Hamburger series is continuous at `0`, where it vanishes. -/
theorem tendsto_hamburgerSeries_zero {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) :
    Tendsto (hamburgerSeries a) (𝓝 0) (𝓝 0) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hbound : ∀ n : ℕ, ∀ t ∈ Metric.closedBall (0 : ℂ) (1 / 2),
      ‖a (n + 1) * t / ((Real.pi : ℂ) * (((n + 1 : ℕ) : ℂ) ^ 2 + t ^ 2))‖ ≤
        (1 / Real.pi) * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    intro n t ht
    rw [Metric.mem_closedBall, dist_zero_right] at ht
    have hm : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hden : ((n + 1 : ℕ) : ℝ) ^ 2 / 2 ≤ ‖(((n + 1 : ℕ) : ℂ)) ^ 2 + t ^ 2‖ := by
      have h1 : ‖(((n + 1 : ℕ) : ℂ)) ^ 2‖ = ((n + 1 : ℕ) : ℝ) ^ 2 := by
        rw [norm_pow, Complex.norm_natCast]
      have h2 : ‖t ^ 2‖ ≤ 1 / 4 := by
        rw [norm_pow]; nlinarith [norm_nonneg t]
      have := norm_sub_le ((((n + 1 : ℕ) : ℂ)) ^ 2 + t ^ 2) (t ^ 2)
      simp only [add_sub_cancel_right] at this
      rw [h1] at this
      nlinarith
    have hdpos : 0 < ‖(((n + 1 : ℕ) : ℂ)) ^ 2 + t ^ 2‖ := lt_of_lt_of_le (by positivity) hden
    rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      div_le_iff₀ (mul_pos Real.pi_pos hdpos)]
    calc ‖a (n + 1)‖ * ‖t‖ ≤ ‖a (n + 1)‖ * (1 / 2) := mul_le_mul_of_nonneg_left ht (norm_nonneg _)
      _ = 1 / Real.pi * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) *
            (Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 / 2)) := by field_simp
      _ ≤ 1 / Real.pi * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) *
            (Real.pi * ‖(((n + 1 : ℕ) : ℂ)) ^ 2 + t ^ 2‖) := by gcongr
  have hcont : ContinuousOn (hamburgerSeries a) (Metric.closedBall (0 : ℂ) (1 / 2)) := by
    refine continuousOn_tsum (fun n => ?_) (ha.mul_left (1 / Real.pi)) hbound
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => ?_
    rw [Metric.mem_closedBall, dist_zero_right] at ht
    refine mul_ne_zero hπ fun h => ?_
    have hm : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have h1 : ‖(((n + 1 : ℕ) : ℂ)) ^ 2‖ = ((n + 1 : ℕ) : ℝ) ^ 2 := by
      rw [norm_pow, Complex.norm_natCast]
    have h2 : ‖t ^ 2‖ ≤ 1 / 4 := by rw [norm_pow]; nlinarith [norm_nonneg t]
    have : (((n + 1 : ℕ) : ℂ)) ^ 2 = -(t ^ 2) := by linear_combination h
    rw [this, norm_neg] at h1
    nlinarith
  have hval : hamburgerSeries a 0 = 0 := by simp [hamburgerSeries]
  have := (hcont.continuousAt (Metric.closedBall_mem_nhds _ (by norm_num))).tendsto
  rwa [hval] at this

/-- The pole of `t ↦ L(t + i)` at `t = 0`: `t · L(t + i) → a₁/(2π)`. -/
theorem tendsto_mul_hamburgerSeries_add_I {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) :
    Tendsto (fun t => t * hamburgerSeries a (t + I)) (𝓝[≠] 0) (𝓝 (a 1 / (2 * Real.pi))) := by
  have hB := tendsto_sub_mul_hamburgerSeries ha (n₀ := 1) le_rfl
  have hshift : Tendsto (fun t : ℂ => t + I) (𝓝[≠] 0) (𝓝[≠] (((1 : ℕ) : ℂ) * I)) := by
    have hc : Tendsto (fun t : ℂ => t + I) (𝓝 0) (𝓝 (((1 : ℕ) : ℂ) * I)) := by
      have := (continuous_id.add continuous_const).tendsto (0 : ℂ) (f := fun t : ℂ => t + I)
      convert this using 2
      simp
    refine tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
    intro h
    apply ht
    simp at h
    linear_combination h
  refine (hB.comp hshift).congr' (Filter.Eventually.of_forall fun t => ?_)
  simp

/-- **The odd-sign residue identity at `t = 0`.**  If `L(t + i) − L(t) = c/(t + i) − c/t` on a
punctured neighbourhood of `0`, then `a₁/(2π) = −c`. -/
theorem coeff_one_eq_of_periodic_at_zero {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) (c : ℂ)
    (hper : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      hamburgerSeries a (t + I) - hamburgerSeries a t = c / (t + I) - c / t) :
    a 1 / (2 * Real.pi) = -c := by
  have h1 := tendsto_mul_hamburgerSeries_add_I ha
  have h2 : Tendsto (fun t => t * hamburgerSeries a t) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have hz : Tendsto (fun t : ℂ => t) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hL : Tendsto (hamburgerSeries a) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
      (tendsto_hamburgerSeries_zero ha).mono_left nhdsWithin_le_nhds
    simpa using hz.mul hL
  have h3 : Tendsto (fun t => t * (c / (t + I) - c / t)) (𝓝[≠] (0 : ℂ)) (𝓝 (-c)) := by
    have hc : Tendsto (fun t : ℂ => t * (c / (t + I)) - c) (𝓝 (0 : ℂ)) (𝓝 (0 * (c / (0 + I)) - c)) := by
      have hI : (0 : ℂ) + I ≠ 0 := by simp
      exact ((continuous_id.tendsto 0).mul ((continuous_const.tendsto 0).div
        ((continuous_id.add continuous_const).tendsto 0) hI)).sub tendsto_const_nhds
    simp only [zero_mul, zero_sub] at hc
    refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht
    field_simp
  have h4 : Tendsto (fun t => t * hamburgerSeries a (t + I) - t * hamburgerSeries a t)
      (𝓝[≠] (0 : ℂ)) (𝓝 (a 1 / (2 * Real.pi) - 0)) := h1.sub h2
  rw [sub_zero] at h4
  have h5 : Tendsto (fun t => t * hamburgerSeries a (t + I) - t * hamburgerSeries a t)
      (𝓝[≠] (0 : ℂ)) (𝓝 (-c)) := by
    refine h3.congr' ?_
    filter_upwards [hper] with t ht
    rw [← mul_sub, ht]
  exact tendsto_nhds_unique h4 h5

/-- Every point of the imaginary axis is a limit of the open right half-plane. -/
theorem nhdsWithin_re_pos_neBot (y : ℝ) : (𝓝[{t : ℂ | 0 < t.re}] ((y : ℂ) * I)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Complex.closure_setOf_lt_re]
  simp

theorem nhdsWithin_re_pos_le_punctured (y : ℝ) :
    𝓝[{t : ℂ | 0 < t.re}] ((y : ℂ) * I) ≤ 𝓝[≠] ((y : ℂ) * I) := by
  refine nhdsWithin_mono _ fun t ht => ?_
  simp only [Set.mem_setOf_eq] at ht
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  rintro rfl
  simp at ht

/-- **Hamburger's periodicity step from the right half-plane.**  If
`L(t + i) − L(t) = c/(t + i) − c/t` for `Re t > 0`, then every coefficient equals `−2πc`.
Residues at `i n₀` are computed as limits from the right half-plane: at `n₀ = 0` the pole of
`c/t` gives `a₁ = −2πc`, and at `n₀ ≥ 1` the right-hand side is regular, so `a_{n₀+1} = a_{n₀}`. -/
theorem coeff_eq_of_hamburgerSeries_periodic_re_pos {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) (c : ℂ)
    (hper : ∀ t : ℂ, 0 < t.re →
      hamburgerSeries a (t + I) - hamburgerSeries a t = c / (t + I) - c / t) (n : ℕ) :
    a (n + 1) = -(2 * Real.pi * c) := by
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hev : ∀ y : ℝ, ∀ᶠ t in 𝓝[{t : ℂ | 0 < t.re}] ((y : ℂ) * I),
      hamburgerSeries a (t + I) - hamburgerSeries a t = c / (t + I) - c / t := by
    intro y
    filter_upwards [self_mem_nhdsWithin] with t ht using hper t ht
  induction n with
  | zero =>
    haveI := nhdsWithin_re_pos_neBot 0
    have hle := nhdsWithin_re_pos_le_punctured 0
    simp only [ofReal_zero, zero_mul] at hle this
    have h1 := (tendsto_mul_hamburgerSeries_add_I ha).mono_left hle
    have h2 : Tendsto (fun t => t * hamburgerSeries a t) (𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ)) (𝓝 0) := by
      have hz : Tendsto (fun t : ℂ => t) (𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hL : Tendsto (hamburgerSeries a) (𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ)) (𝓝 0) :=
        (tendsto_hamburgerSeries_zero ha).mono_left nhdsWithin_le_nhds
      simpa using hz.mul hL
    have h3 : Tendsto (fun t => t * (c / (t + I) - c / t)) (𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ))
        (𝓝 (-c)) := by
      have hc : Tendsto (fun t : ℂ => t * (c / (t + I)) - c) (𝓝 (0 : ℂ))
          (𝓝 (0 * (c / (0 + I)) - c)) := by
        have hI : (0 : ℂ) + I ≠ 0 := by simp
        exact ((continuous_id.tendsto 0).mul ((continuous_const.tendsto 0).div
          ((continuous_id.add continuous_const).tendsto 0) hI)).sub tendsto_const_nhds
      simp only [zero_mul, zero_sub] at hc
      refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by
        rintro rfl
        simp at ht
      field_simp
    have h4 := h1.sub h2
    rw [sub_zero] at h4
    have h5 : Tendsto (fun t => t * hamburgerSeries a (t + I) - t * hamburgerSeries a t)
        (𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ)) (𝓝 (-c)) := by
      have h0 := hev 0
      simp only [ofReal_zero, zero_mul] at h0
      refine h3.congr' ?_
      filter_upwards [h0] with t ht
      rw [← mul_sub, ht]
    have huniq := tendsto_nhds_unique h4 h5
    rw [div_eq_iff hπ] at huniq
    rw [huniq]
    ring
  | succ n ih =>
    rw [← ih]
    set n₀ := n + 1 with hn₀def
    have hn₀ : 1 ≤ n₀ := by omega
    haveI := nhdsWithin_re_pos_neBot (n₀ : ℝ)
    have hle := nhdsWithin_re_pos_le_punctured (n₀ : ℝ)
    simp only [ofReal_natCast] at hle this
    have hA := (tendsto_sub_mul_hamburgerSeries ha hn₀).mono_left hle
    have hB := tendsto_sub_mul_hamburgerSeries ha (n₀ := n₀ + 1) (by omega)
    have hshift : Tendsto (fun t : ℂ => t + I) (𝓝[≠] ((n₀ : ℂ) * I))
        (𝓝[≠] (((n₀ + 1 : ℕ) : ℂ) * I)) := by
      have hc : Tendsto (fun t : ℂ => t + I) (𝓝 ((n₀ : ℂ) * I)) (𝓝 (((n₀ + 1 : ℕ) : ℂ) * I)) := by
        have := (continuous_id.add continuous_const).tendsto ((n₀ : ℂ) * I) (f := fun t : ℂ => t + I)
        convert this using 2
        push_cast; ring_nf
      refine tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
      intro h
      apply ht
      push_cast at h
      linear_combination h
    have hB'' : Tendsto (fun t => (t - (n₀ : ℂ) * I) * hamburgerSeries a (t + I))
        (𝓝[{t : ℂ | 0 < t.re}] ((n₀ : ℂ) * I)) (𝓝 (a (n₀ + 1) / (2 * Real.pi))) := by
      refine ((hB.comp hshift).mono_left hle).congr' (Filter.Eventually.of_forall fun t => ?_)
      simp only [Function.comp]
      congr 1
      push_cast; ring_nf
    have hn0 : (n₀ : ℂ) ≠ 0 := by exact_mod_cast (by omega : n₀ ≠ 0)
    have hR : Tendsto (fun t => (t - (n₀ : ℂ) * I) * (c / (t + I) - c / t))
        (𝓝[{t : ℂ | 0 < t.re}] ((n₀ : ℂ) * I)) (𝓝 0) := by
      have h1 : (n₀ : ℂ) * I + I ≠ 0 := by
        intro h
        have : ((n₀ : ℂ) + 1) * I = 0 := by linear_combination h
        rcases mul_eq_zero.mp this with h' | h'
        · have : ((n₀ + 1 : ℕ) : ℂ) = 0 := by push_cast; exact h'
          exact absurd (by exact_mod_cast this) (Nat.succ_ne_zero n₀)
        · exact I_ne_zero h'
      have h2 : (n₀ : ℂ) * I ≠ 0 := mul_ne_zero hn0 I_ne_zero
      have hc : ContinuousAt (fun t => (t - (n₀ : ℂ) * I) * (c / (t + I) - c / t))
          ((n₀ : ℂ) * I) := by
        refine ContinuousAt.mul (by fun_prop) (ContinuousAt.sub ?_ ?_)
        · exact continuousAt_const.div (by fun_prop) h1
        · exact continuousAt_const.div continuousAt_id h2
      have := hc.tendsto
      simp only [sub_self, zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hdiff := hB''.sub hA
    have hdiff0 : Tendsto (fun t => (t - (n₀ : ℂ) * I) * hamburgerSeries a (t + I) -
        (t - (n₀ : ℂ) * I) * hamburgerSeries a t) (𝓝[{t : ℂ | 0 < t.re}] ((n₀ : ℂ) * I))
        (𝓝 0) := by
      have h0 := hev (n₀ : ℝ)
      simp only [ofReal_natCast] at h0
      refine hR.congr' ?_
      filter_upwards [h0] with t ht
      rw [← mul_sub, ht]
    have huniq := tendsto_nhds_unique hdiff hdiff0
    rw [← sub_div] at huniq
    exact sub_eq_zero.mp ((div_eq_zero_iff.mp huniq).resolve_right hπ)

end GaloisForLFunctions.HTGeometry
